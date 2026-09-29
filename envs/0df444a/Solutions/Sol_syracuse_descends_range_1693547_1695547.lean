-- Prove2me | solution 1 for syracuse_descends_range_1693547_1695547
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:24:33.713683+00:00
-- url     : https://prove2.me/submissions/bd1ed69f-a646-467c-8835-ff551ef4ec1a

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


theorem B1810469 : Blo 1693547 1810469 := bbase (se 4 (by rfl) ⟨169731, by rfl⟩ : syracuseStep 1810469 = 339463) (by norm_num)
theorem B8257589 : Blo 1693547 8257589 := bbase (se 5 (by rfl) ⟨387074, by rfl⟩ : syracuseStep 8257589 = 774149) (by norm_num)
theorem B2859077 : Blo 1693547 2859077 := bbase (se 4 (by rfl) ⟨268038, by rfl⟩ : syracuseStep 2859077 = 536077) (by norm_num)
theorem B47644757 : Blo 1693547 47644757 := bbase (se 8 (by rfl) ⟨279168, by rfl⟩ : syracuseStep 47644757 = 558337) (by norm_num)
theorem B1810597 : Blo 1693547 1810597 := bbase (se 4 (by rfl) ⟨169743, by rfl⟩ : syracuseStep 1810597 = 339487) (by norm_num)
theorem B2859205 : Blo 1693547 2859205 := bbase (se 4 (by rfl) ⟨268050, by rfl⟩ : syracuseStep 2859205 = 536101) (by norm_num)
theorem B3531005 : Blo 1693547 3531005 := bbase (se 3 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 3531005 = 1324127) (by norm_num)
theorem B2859293 : Blo 1693547 2859293 := bbase (se 3 (by rfl) ⟨536117, by rfl⟩ : syracuseStep 2859293 = 1072235) (by norm_num)
theorem B3350813 : Blo 1693547 3350813 := bbase (se 3 (by rfl) ⟨628277, by rfl⟩ : syracuseStep 3350813 = 1256555) (by norm_num)
theorem B15892789 : Blo 1693547 15892789 := bbase (se 5 (by rfl) ⟨744974, by rfl⟩ : syracuseStep 15892789 = 1489949) (by norm_num)
theorem B3719485 : Blo 1693547 3719485 := bbase (se 3 (by rfl) ⟨697403, by rfl⟩ : syracuseStep 3719485 = 1394807) (by norm_num)
theorem B5431637 : Blo 1693547 5431637 := bbase (se 10 (by rfl) ⟨7956, by rfl⟩ : syracuseStep 5431637 = 15913) (by norm_num)
theorem B8577413 : Blo 1693547 8577413 := bbase (se 4 (by rfl) ⟨804132, by rfl⟩ : syracuseStep 8577413 = 1608265) (by norm_num)
theorem B2859421 : Blo 1693547 2859421 := bbase (se 3 (by rfl) ⟨536141, by rfl⟩ : syracuseStep 2859421 = 1072283) (by norm_num)
theorem B5718437 : Blo 1693547 5718437 := bbase (se 4 (by rfl) ⟨536103, by rfl⟩ : syracuseStep 5718437 = 1072207) (by norm_num)
theorem B4071845 : Blo 1693547 4071845 := bbase (se 4 (by rfl) ⟨381735, by rfl⟩ : syracuseStep 4071845 = 763471) (by norm_num)
theorem B7242149 : Blo 1693547 7242149 := bbase (se 4 (by rfl) ⟨678951, by rfl⟩ : syracuseStep 7242149 = 1357903) (by norm_num)
theorem B2859509 : Blo 1693547 2859509 := bbase (se 5 (by rfl) ⟨134039, by rfl⟩ : syracuseStep 2859509 = 268079) (by norm_num)
theorem B3670525 : Blo 1693547 3670525 := bbase (se 3 (by rfl) ⟨688223, by rfl⟩ : syracuseStep 3670525 = 1376447) (by norm_num)
theorem B4071989 : Blo 1693547 4071989 := bbase (se 5 (by rfl) ⟨190874, by rfl⟩ : syracuseStep 4071989 = 381749) (by norm_num)
theorem B1720913 : Blo 1693547 1720913 := bbase (se 2 (by rfl) ⟨645342, by rfl⟩ : syracuseStep 1720913 = 1290685) (by norm_num)
theorem B7340645 : Blo 1693547 7340645 := bbase (se 4 (by rfl) ⟨688185, by rfl⟩ : syracuseStep 7340645 = 1376371) (by norm_num)
theorem B2859637 : Blo 1693547 2859637 := bbase (se 5 (by rfl) ⟨134045, by rfl⟩ : syracuseStep 2859637 = 268091) (by norm_num)
theorem B7832213 : Blo 1693547 7832213 := bbase (se 6 (by rfl) ⟨183567, by rfl⟩ : syracuseStep 7832213 = 367135) (by norm_num)
theorem B9159317 : Blo 1693547 9159317 := bbase (se 6 (by rfl) ⟨214671, by rfl⟩ : syracuseStep 9159317 = 429343) (by norm_num)
theorem B2859725 : Blo 1693547 2859725 := bbase (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) (by norm_num)
theorem B16286453 : Blo 1693547 16286453 := bbase (se 5 (by rfl) ⟨763427, by rfl⟩ : syracuseStep 16286453 = 1526855) (by norm_num)
theorem B2540333 : Blo 1693547 2540333 := bbase (se 3 (by rfl) ⟨476312, by rfl⟩ : syracuseStep 2540333 = 952625) (by norm_num)
theorem B2540357 : Blo 1693547 2540357 := bbase (se 4 (by rfl) ⟨238158, by rfl⟩ : syracuseStep 2540357 = 476317) (by norm_num)
theorem B2859853 : Blo 1693547 2859853 := bbase (se 3 (by rfl) ⟨536222, by rfl⟩ : syracuseStep 2859853 = 1072445) (by norm_num)
theorem B5718869 : Blo 1693547 5718869 := bbase (se 9 (by rfl) ⟨16754, by rfl⟩ : syracuseStep 5718869 = 33509) (by norm_num)
theorem B23192405 : Blo 1693547 23192405 := bbase (se 9 (by rfl) ⟨67946, by rfl⟩ : syracuseStep 23192405 = 135893) (by norm_num)
theorem B2540381 : Blo 1693547 2540381 := bbase (se 3 (by rfl) ⟨476321, by rfl⟩ : syracuseStep 2540381 = 952643) (by norm_num)
theorem B2540405 : Blo 1693547 2540405 := bbase (se 5 (by rfl) ⟨119081, by rfl⟩ : syracuseStep 2540405 = 238163) (by norm_num)
theorem B3433349 : Blo 1693547 3433349 := bbase (se 4 (by rfl) ⟨321876, by rfl⟩ : syracuseStep 3433349 = 643753) (by norm_num)
theorem B2540429 : Blo 1693547 2540429 := bbase (se 3 (by rfl) ⟨476330, by rfl⟩ : syracuseStep 2540429 = 952661) (by norm_num)
theorem B2540453 : Blo 1693547 2540453 := bbase (se 4 (by rfl) ⟨238167, by rfl⟩ : syracuseStep 2540453 = 476335) (by norm_num)
theorem B2859941 : Blo 1693547 2859941 := bbase (se 4 (by rfl) ⟨268119, by rfl⟩ : syracuseStep 2859941 = 536239) (by norm_num)
theorem B2540477 : Blo 1693547 2540477 := bbase (se 3 (by rfl) ⟨476339, by rfl⟩ : syracuseStep 2540477 = 952679) (by norm_num)
theorem B2540501 : Blo 1693547 2540501 := bbase (se 7 (by rfl) ⟨29771, by rfl⟩ : syracuseStep 2540501 = 59543) (by norm_num)
theorem B2540525 : Blo 1693547 2540525 := bbase (se 3 (by rfl) ⟨476348, by rfl⟩ : syracuseStep 2540525 = 952697) (by norm_num)
theorem B2540549 : Blo 1693547 2540549 := bbase (se 4 (by rfl) ⟨238176, by rfl⟩ : syracuseStep 2540549 = 476353) (by norm_num)
theorem B4826117 : Blo 1693547 4826117 := bbase (se 4 (by rfl) ⟨452448, by rfl⟩ : syracuseStep 4826117 = 904897) (by norm_num)
theorem B2540573 : Blo 1693547 2540573 := bbase (se 3 (by rfl) ⟨476357, by rfl⟩ : syracuseStep 2540573 = 952715) (by norm_num)
theorem B2860069 : Blo 1693547 2860069 := bbase (se 4 (by rfl) ⟨268131, by rfl⟩ : syracuseStep 2860069 = 536263) (by norm_num)
theorem B2540597 : Blo 1693547 2540597 := bbase (se 5 (by rfl) ⟨119090, by rfl⟩ : syracuseStep 2540597 = 238181) (by norm_num)
theorem B2540621 : Blo 1693547 2540621 := bbase (se 3 (by rfl) ⟨476366, by rfl⟩ : syracuseStep 2540621 = 952733) (by norm_num)
theorem B2540645 : Blo 1693547 2540645 := bbase (se 4 (by rfl) ⟨238185, by rfl⟩ : syracuseStep 2540645 = 476371) (by norm_num)
theorem B6431845 : Blo 1693547 6431845 := bbase (se 4 (by rfl) ⟨602985, by rfl⟩ : syracuseStep 6431845 = 1205971) (by norm_num)
theorem B3261541 : Blo 1693547 3261541 := bbase (se 4 (by rfl) ⟨305769, by rfl⟩ : syracuseStep 3261541 = 611539) (by norm_num)
theorem B2540669 : Blo 1693547 2540669 := bbase (se 3 (by rfl) ⟨476375, by rfl⟩ : syracuseStep 2540669 = 952751) (by norm_num)
theorem B2860157 : Blo 1693547 2860157 := bbase (se 3 (by rfl) ⟨536279, by rfl⟩ : syracuseStep 2860157 = 1072559) (by norm_num)
theorem B2540693 : Blo 1693547 2540693 := bbase (se 6 (by rfl) ⟨59547, by rfl⟩ : syracuseStep 2540693 = 119095) (by norm_num)
theorem B2540717 : Blo 1693547 2540717 := bbase (se 3 (by rfl) ⟨476384, by rfl⟩ : syracuseStep 2540717 = 952769) (by norm_num)
theorem B2540741 : Blo 1693547 2540741 := bbase (se 4 (by rfl) ⟨238194, by rfl⟩ : syracuseStep 2540741 = 476389) (by norm_num)
theorem B3810509 : Blo 1693547 3810509 := bbase (se 3 (by rfl) ⟨714470, by rfl⟩ : syracuseStep 3810509 = 1428941) (by norm_num)
theorem B9651413 : Blo 1693547 9651413 := bbase (se 7 (by rfl) ⟨113102, by rfl⟩ : syracuseStep 9651413 = 226205) (by norm_num)
theorem B2540765 : Blo 1693547 2540765 := bbase (se 3 (by rfl) ⟨476393, by rfl⟩ : syracuseStep 2540765 = 952787) (by norm_num)
theorem B2540789 : Blo 1693547 2540789 := bbase (se 5 (by rfl) ⟨119099, by rfl⟩ : syracuseStep 2540789 = 238199) (by norm_num)
theorem B2860285 : Blo 1693547 2860285 := bbase (se 3 (by rfl) ⟨536303, by rfl⟩ : syracuseStep 2860285 = 1072607) (by norm_num)
theorem B5719301 : Blo 1693547 5719301 := bbase (se 4 (by rfl) ⟨536184, by rfl⟩ : syracuseStep 5719301 = 1072369) (by norm_num)
theorem B2540813 : Blo 1693547 2540813 := bbase (se 3 (by rfl) ⟨476402, by rfl⟩ : syracuseStep 2540813 = 952805) (by norm_num)
theorem B3810581 : Blo 1693547 3810581 := bbase (se 6 (by rfl) ⟨89310, by rfl⟩ : syracuseStep 3810581 = 178621) (by norm_num)
theorem B2540837 : Blo 1693547 2540837 := bbase (se 4 (by rfl) ⟨238203, by rfl⟩ : syracuseStep 2540837 = 476407) (by norm_num)
theorem B2540861 : Blo 1693547 2540861 := bbase (se 3 (by rfl) ⟨476411, by rfl⟩ : syracuseStep 2540861 = 952823) (by norm_num)
theorem B2540885 : Blo 1693547 2540885 := bbase (se 12 (by rfl) ⟨930, by rfl⟩ : syracuseStep 2540885 = 1861) (by norm_num)
theorem B2860373 : Blo 1693547 2860373 := bbase (se 12 (by rfl) ⟨1047, by rfl⟩ : syracuseStep 2860373 = 2095) (by norm_num)
theorem B3810653 : Blo 1693547 3810653 := bbase (se 3 (by rfl) ⟨714497, by rfl⟩ : syracuseStep 3810653 = 1428995) (by norm_num)
theorem B2540909 : Blo 1693547 2540909 := bbase (se 3 (by rfl) ⟨476420, by rfl⟩ : syracuseStep 2540909 = 952841) (by norm_num)
theorem B2540933 : Blo 1693547 2540933 := bbase (se 4 (by rfl) ⟨238212, by rfl⟩ : syracuseStep 2540933 = 476425) (by norm_num)
theorem B6432149 : Blo 1693547 6432149 := bbase (se 6 (by rfl) ⟨150753, by rfl⟩ : syracuseStep 6432149 = 301507) (by norm_num)
theorem B2540957 : Blo 1693547 2540957 := bbase (se 3 (by rfl) ⟨476429, by rfl⟩ : syracuseStep 2540957 = 952859) (by norm_num)
theorem B3810725 : Blo 1693547 3810725 := bbase (se 4 (by rfl) ⟨357255, by rfl⟩ : syracuseStep 3810725 = 714511) (by norm_num)
theorem B7333301 : Blo 1693547 7333301 := bbase (se 5 (by rfl) ⟨343748, by rfl⟩ : syracuseStep 7333301 = 687497) (by norm_num)
theorem B2540981 : Blo 1693547 2540981 := bbase (se 5 (by rfl) ⟨119108, by rfl⟩ : syracuseStep 2540981 = 238217) (by norm_num)
theorem B2541005 : Blo 1693547 2541005 := bbase (se 3 (by rfl) ⟨476438, by rfl⟩ : syracuseStep 2541005 = 952877) (by norm_num)
theorem B2860501 : Blo 1693547 2860501 := bbase (se 7 (by rfl) ⟨33521, by rfl⟩ : syracuseStep 2860501 = 67043) (by norm_num)
theorem B2541029 : Blo 1693547 2541029 := bbase (se 4 (by rfl) ⟨238221, by rfl⟩ : syracuseStep 2541029 = 476443) (by norm_num)
theorem B3810797 : Blo 1693547 3810797 := bbase (se 3 (by rfl) ⟨714524, by rfl⟩ : syracuseStep 3810797 = 1429049) (by norm_num)
theorem B2541053 : Blo 1693547 2541053 := bbase (se 3 (by rfl) ⟨476447, by rfl⟩ : syracuseStep 2541053 = 952895) (by norm_num)
theorem B4580869 : Blo 1693547 4580869 := bbase (se 4 (by rfl) ⟨429456, by rfl⟩ : syracuseStep 4580869 = 858913) (by norm_num)
theorem B2541077 : Blo 1693547 2541077 := bbase (se 6 (by rfl) ⟨59556, by rfl⟩ : syracuseStep 2541077 = 119113) (by norm_num)
theorem B2541101 : Blo 1693547 2541101 := bbase (se 3 (by rfl) ⟨476456, by rfl⟩ : syracuseStep 2541101 = 952913) (by norm_num)
theorem B2860589 : Blo 1693547 2860589 := bbase (se 3 (by rfl) ⟨536360, by rfl⟩ : syracuseStep 2860589 = 1072721) (by norm_num)
theorem B3810869 : Blo 1693547 3810869 := bbase (se 5 (by rfl) ⟨178634, by rfl⟩ : syracuseStep 3810869 = 357269) (by norm_num)
theorem B2541125 : Blo 1693547 2541125 := bbase (se 4 (by rfl) ⟨238230, by rfl⟩ : syracuseStep 2541125 = 476461) (by norm_num)
theorem B2541149 : Blo 1693547 2541149 := bbase (se 3 (by rfl) ⟨476465, by rfl⟩ : syracuseStep 2541149 = 952931) (by norm_num)
theorem B2541173 : Blo 1693547 2541173 := bbase (se 5 (by rfl) ⟨119117, by rfl⟩ : syracuseStep 2541173 = 238235) (by norm_num)
theorem B3810941 : Blo 1693547 3810941 := bbase (se 3 (by rfl) ⟨714551, by rfl⟩ : syracuseStep 3810941 = 1429103) (by norm_num)
theorem B2541197 : Blo 1693547 2541197 := bbase (se 3 (by rfl) ⟨476474, by rfl⟩ : syracuseStep 2541197 = 952949) (by norm_num)
theorem B8578709 : Blo 1693547 8578709 := bbase (se 6 (by rfl) ⟨201063, by rfl⟩ : syracuseStep 8578709 = 402127) (by norm_num)
theorem B2541221 : Blo 1693547 2541221 := bbase (se 4 (by rfl) ⟨238239, by rfl⟩ : syracuseStep 2541221 = 476479) (by norm_num)
theorem B2860717 : Blo 1693547 2860717 := bbase (se 3 (by rfl) ⟨536384, by rfl⟩ : syracuseStep 2860717 = 1072769) (by norm_num)
theorem B5719733 : Blo 1693547 5719733 := bbase (se 5 (by rfl) ⟨268112, by rfl⟩ : syracuseStep 5719733 = 536225) (by norm_num)
theorem B2541245 : Blo 1693547 2541245 := bbase (se 3 (by rfl) ⟨476483, by rfl⟩ : syracuseStep 2541245 = 952967) (by norm_num)
theorem B3811013 : Blo 1693547 3811013 := bbase (se 4 (by rfl) ⟨357282, by rfl⟩ : syracuseStep 3811013 = 714565) (by norm_num)
theorem B2541269 : Blo 1693547 2541269 := bbase (se 7 (by rfl) ⟨29780, by rfl⟩ : syracuseStep 2541269 = 59561) (by norm_num)
theorem B2541293 : Blo 1693547 2541293 := bbase (se 3 (by rfl) ⟨476492, by rfl⟩ : syracuseStep 2541293 = 952985) (by norm_num)
theorem B2713333 : Blo 1693547 2713333 := bbase (se 5 (by rfl) ⟨127187, by rfl⟩ : syracuseStep 2713333 = 254375) (by norm_num)
theorem B2541317 : Blo 1693547 2541317 := bbase (se 4 (by rfl) ⟨238248, by rfl⟩ : syracuseStep 2541317 = 476497) (by norm_num)
theorem B2860805 : Blo 1693547 2860805 := bbase (se 4 (by rfl) ⟨268200, by rfl⟩ : syracuseStep 2860805 = 536401) (by norm_num)
theorem B3811085 : Blo 1693547 3811085 := bbase (se 3 (by rfl) ⟨714578, by rfl⟩ : syracuseStep 3811085 = 1429157) (by norm_num)
theorem B2541341 : Blo 1693547 2541341 := bbase (se 3 (by rfl) ⟨476501, by rfl⟩ : syracuseStep 2541341 = 953003) (by norm_num)
theorem B2541365 : Blo 1693547 2541365 := bbase (se 5 (by rfl) ⟨119126, by rfl⟩ : syracuseStep 2541365 = 238253) (by norm_num)
theorem B2541389 : Blo 1693547 2541389 := bbase (se 3 (by rfl) ⟨476510, by rfl⟩ : syracuseStep 2541389 = 953021) (by norm_num)
theorem B3811157 : Blo 1693547 3811157 := bbase (se 9 (by rfl) ⟨11165, by rfl⟩ : syracuseStep 3811157 = 22331) (by norm_num)
theorem B2713429 : Blo 1693547 2713429 := bbase (se 9 (by rfl) ⟨7949, by rfl⟩ : syracuseStep 2713429 = 15899) (by norm_num)
theorem B2541413 : Blo 1693547 2541413 := bbase (se 4 (by rfl) ⟨238257, by rfl⟩ : syracuseStep 2541413 = 476515) (by norm_num)
theorem B2541437 : Blo 1693547 2541437 := bbase (se 3 (by rfl) ⟨476519, by rfl⟩ : syracuseStep 2541437 = 953039) (by norm_num)
theorem B2860933 : Blo 1693547 2860933 := bbase (se 4 (by rfl) ⟨268212, by rfl⟩ : syracuseStep 2860933 = 536425) (by norm_num)
theorem B2541461 : Blo 1693547 2541461 := bbase (se 6 (by rfl) ⟨59565, by rfl⟩ : syracuseStep 2541461 = 119131) (by norm_num)
theorem B3811229 : Blo 1693547 3811229 := bbase (se 3 (by rfl) ⟨714605, by rfl⟩ : syracuseStep 3811229 = 1429211) (by norm_num)
theorem B2541485 : Blo 1693547 2541485 := bbase (se 3 (by rfl) ⟨476528, by rfl⟩ : syracuseStep 2541485 = 953057) (by norm_num)
theorem B2541509 : Blo 1693547 2541509 := bbase (se 4 (by rfl) ⟨238266, by rfl⟩ : syracuseStep 2541509 = 476533) (by norm_num)
theorem B10856405 : Blo 1693547 10856405 := bbase (se 7 (by rfl) ⟨127223, by rfl⟩ : syracuseStep 10856405 = 254447) (by norm_num)
theorem B2541533 : Blo 1693547 2541533 := bbase (se 3 (by rfl) ⟨476537, by rfl⟩ : syracuseStep 2541533 = 953075) (by norm_num)
theorem B2861021 : Blo 1693547 2861021 := bbase (se 3 (by rfl) ⟨536441, by rfl⟩ : syracuseStep 2861021 = 1072883) (by norm_num)
theorem B3811301 : Blo 1693547 3811301 := bbase (se 4 (by rfl) ⟨357309, by rfl⟩ : syracuseStep 3811301 = 714619) (by norm_num)
theorem B2713589 : Blo 1693547 2713589 := bbase (se 5 (by rfl) ⟨127199, by rfl⟩ : syracuseStep 2713589 = 254399) (by norm_num)
theorem B2541557 : Blo 1693547 2541557 := bbase (se 5 (by rfl) ⟨119135, by rfl⟩ : syracuseStep 2541557 = 238271) (by norm_num)
theorem B2541581 : Blo 1693547 2541581 := bbase (se 3 (by rfl) ⟨476546, by rfl⟩ : syracuseStep 2541581 = 953093) (by norm_num)
theorem B2541605 : Blo 1693547 2541605 := bbase (se 4 (by rfl) ⟨238275, by rfl⟩ : syracuseStep 2541605 = 476551) (by norm_num)
theorem B3811373 : Blo 1693547 3811373 := bbase (se 3 (by rfl) ⟨714632, by rfl⟩ : syracuseStep 3811373 = 1429265) (by norm_num)
theorem B2541629 : Blo 1693547 2541629 := bbase (se 3 (by rfl) ⟨476555, by rfl⟩ : syracuseStep 2541629 = 953111) (by norm_num)
theorem B3434581 : Blo 1693547 3434581 := bbase (se 8 (by rfl) ⟨20124, by rfl⟩ : syracuseStep 3434581 = 40249) (by norm_num)
theorem B2541653 : Blo 1693547 2541653 := bbase (se 8 (by rfl) ⟨14892, by rfl⟩ : syracuseStep 2541653 = 29785) (by norm_num)
theorem B2861149 : Blo 1693547 2861149 := bbase (se 3 (by rfl) ⟨536465, by rfl⟩ : syracuseStep 2861149 = 1072931) (by norm_num)
theorem B5720165 : Blo 1693547 5720165 := bbase (se 4 (by rfl) ⟨536265, by rfl⟩ : syracuseStep 5720165 = 1072531) (by norm_num)
theorem B2541677 : Blo 1693547 2541677 := bbase (se 3 (by rfl) ⟨476564, by rfl⟩ : syracuseStep 2541677 = 953129) (by norm_num)
theorem B3811445 : Blo 1693547 3811445 := bbase (se 5 (by rfl) ⟨178661, by rfl⟩ : syracuseStep 3811445 = 357323) (by norm_num)
theorem B2541701 : Blo 1693547 2541701 := bbase (se 4 (by rfl) ⟨238284, by rfl⟩ : syracuseStep 2541701 = 476569) (by norm_num)
theorem B2541725 : Blo 1693547 2541725 := bbase (se 3 (by rfl) ⟨476573, by rfl⟩ : syracuseStep 2541725 = 953147) (by norm_num)
theorem B2541749 : Blo 1693547 2541749 := bbase (se 5 (by rfl) ⟨119144, by rfl⟩ : syracuseStep 2541749 = 238289) (by norm_num)
theorem B2861237 : Blo 1693547 2861237 := bbase (se 5 (by rfl) ⟨134120, by rfl⟩ : syracuseStep 2861237 = 268241) (by norm_num)
theorem B3811517 : Blo 1693547 3811517 := bbase (se 3 (by rfl) ⟨714659, by rfl⟩ : syracuseStep 3811517 = 1429319) (by norm_num)
theorem B2541773 : Blo 1693547 2541773 := bbase (se 3 (by rfl) ⟨476582, by rfl⟩ : syracuseStep 2541773 = 953165) (by norm_num)
theorem B2541797 : Blo 1693547 2541797 := bbase (se 4 (by rfl) ⟨238293, by rfl⟩ : syracuseStep 2541797 = 476587) (by norm_num)
theorem B3262693 : Blo 1693547 3262693 := bbase (se 4 (by rfl) ⟨305877, by rfl⟩ : syracuseStep 3262693 = 611755) (by norm_num)
theorem B2541821 : Blo 1693547 2541821 := bbase (se 3 (by rfl) ⟨476591, by rfl⟩ : syracuseStep 2541821 = 953183) (by norm_num)
theorem B3811589 : Blo 1693547 3811589 := bbase (se 4 (by rfl) ⟨357336, by rfl⟩ : syracuseStep 3811589 = 714673) (by norm_num)
theorem B2541845 : Blo 1693547 2541845 := bbase (se 6 (by rfl) ⟨59574, by rfl⟩ : syracuseStep 2541845 = 119149) (by norm_num)
theorem B2541869 : Blo 1693547 2541869 := bbase (se 3 (by rfl) ⟨476600, by rfl⟩ : syracuseStep 2541869 = 953201) (by norm_num)
theorem B2173241 : Blo 1693547 2173241 := bbase (se 2 (by rfl) ⟨814965, by rfl⟩ : syracuseStep 2173241 = 1629931) (by norm_num)
theorem B2541893 : Blo 1693547 2541893 := bbase (se 4 (by rfl) ⟨238302, by rfl⟩ : syracuseStep 2541893 = 476605) (by norm_num)
theorem B3811661 : Blo 1693547 3811661 := bbase (se 3 (by rfl) ⟨714686, by rfl⟩ : syracuseStep 3811661 = 1429373) (by norm_num)
theorem B2541917 : Blo 1693547 2541917 := bbase (se 3 (by rfl) ⟨476609, by rfl⟩ : syracuseStep 2541917 = 953219) (by norm_num)
theorem B2541941 : Blo 1693547 2541941 := bbase (se 5 (by rfl) ⟨119153, by rfl⟩ : syracuseStep 2541941 = 238307) (by norm_num)
theorem B2541965 : Blo 1693547 2541965 := bbase (se 3 (by rfl) ⟨476618, by rfl⟩ : syracuseStep 2541965 = 953237) (by norm_num)
theorem B3811733 : Blo 1693547 3811733 := bbase (se 6 (by rfl) ⟨89337, by rfl⟩ : syracuseStep 3811733 = 178675) (by norm_num)
theorem B2541989 : Blo 1693547 2541989 := bbase (se 4 (by rfl) ⟨238311, by rfl⟩ : syracuseStep 2541989 = 476623) (by norm_num)
theorem B2542013 : Blo 1693547 2542013 := bbase (se 3 (by rfl) ⟨476627, by rfl⟩ : syracuseStep 2542013 = 953255) (by norm_num)
theorem B6867413 : Blo 1693547 6867413 := bbase (se 7 (by rfl) ⟨80477, by rfl⟩ : syracuseStep 6867413 = 160955) (by norm_num)
theorem B2542037 : Blo 1693547 2542037 := bbase (se 7 (by rfl) ⟨29789, by rfl⟩ : syracuseStep 2542037 = 59579) (by norm_num)
theorem B3811805 : Blo 1693547 3811805 := bbase (se 3 (by rfl) ⟨714713, by rfl⟩ : syracuseStep 3811805 = 1429427) (by norm_num)
theorem B2542061 : Blo 1693547 2542061 := bbase (se 3 (by rfl) ⟨476636, by rfl⟩ : syracuseStep 2542061 = 953273) (by norm_num)
theorem B4286965 : Blo 1693547 4286965 := bbase (se 5 (by rfl) ⟨200951, by rfl⟩ : syracuseStep 4286965 = 401903) (by norm_num)
theorem B2542085 : Blo 1693547 2542085 := bbase (se 4 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 2542085 = 476641) (by norm_num)
theorem B5720597 : Blo 1693547 5720597 := bbase (se 6 (by rfl) ⟨134076, by rfl⟩ : syracuseStep 5720597 = 268153) (by norm_num)
theorem B2542109 : Blo 1693547 2542109 := bbase (se 3 (by rfl) ⟨476645, by rfl⟩ : syracuseStep 2542109 = 953291) (by norm_num)
theorem B3811877 : Blo 1693547 3811877 := bbase (se 4 (by rfl) ⟨357363, by rfl⟩ : syracuseStep 3811877 = 714727) (by norm_num)
theorem B2542133 : Blo 1693547 2542133 := bbase (se 5 (by rfl) ⟨119162, by rfl⟩ : syracuseStep 2542133 = 238325) (by norm_num)
theorem B4827701 : Blo 1693547 4827701 := bbase (se 5 (by rfl) ⟨226298, by rfl⟩ : syracuseStep 4827701 = 452597) (by norm_num)
theorem B2542157 : Blo 1693547 2542157 := bbase (se 3 (by rfl) ⟨476654, by rfl⟩ : syracuseStep 2542157 = 953309) (by norm_num)
theorem B16280149 : Blo 1693547 16280149 := bbase (se 8 (by rfl) ⟨95391, by rfl⟩ : syracuseStep 16280149 = 190783) (by norm_num)
theorem B4287077 : Blo 1693547 4287077 := bbase (se 4 (by rfl) ⟨401913, by rfl⟩ : syracuseStep 4287077 = 803827) (by norm_num)
theorem B2542181 : Blo 1693547 2542181 := bbase (se 4 (by rfl) ⟨238329, by rfl⟩ : syracuseStep 2542181 = 476659) (by norm_num)
theorem B3811949 : Blo 1693547 3811949 := bbase (se 3 (by rfl) ⟨714740, by rfl⟩ : syracuseStep 3811949 = 1429481) (by norm_num)
theorem B2542205 : Blo 1693547 2542205 := bbase (se 3 (by rfl) ⟨476663, by rfl⟩ : syracuseStep 2542205 = 953327) (by norm_num)
theorem B2542229 : Blo 1693547 2542229 := bbase (se 6 (by rfl) ⟨59583, by rfl⟩ : syracuseStep 2542229 = 119167) (by norm_num)
theorem B6965909 : Blo 1693547 6965909 := bbase (se 6 (by rfl) ⟨163263, by rfl⟩ : syracuseStep 6965909 = 326527) (by norm_num)
theorem B2542253 : Blo 1693547 2542253 := bbase (se 3 (by rfl) ⟨476672, by rfl⟩ : syracuseStep 2542253 = 953345) (by norm_num)
theorem B3812021 : Blo 1693547 3812021 := bbase (se 5 (by rfl) ⟨178688, by rfl⟩ : syracuseStep 3812021 = 357377) (by norm_num)
theorem B2542277 : Blo 1693547 2542277 := bbase (se 4 (by rfl) ⟨238338, by rfl⟩ : syracuseStep 2542277 = 476677) (by norm_num)
theorem B2542301 : Blo 1693547 2542301 := bbase (se 3 (by rfl) ⟨476681, by rfl⟩ : syracuseStep 2542301 = 953363) (by norm_num)
theorem B2542325 : Blo 1693547 2542325 := bbase (se 5 (by rfl) ⟨119171, by rfl⟩ : syracuseStep 2542325 = 238343) (by norm_num)
theorem B3812093 : Blo 1693547 3812093 := bbase (se 3 (by rfl) ⟨714767, by rfl⟩ : syracuseStep 3812093 = 1429535) (by norm_num)
theorem B2575109 : Blo 1693547 2575109 := bbase (se 4 (by rfl) ⟨241416, by rfl⟩ : syracuseStep 2575109 = 482833) (by norm_num)
theorem B2542349 : Blo 1693547 2542349 := bbase (se 3 (by rfl) ⟨476690, by rfl⟩ : syracuseStep 2542349 = 953381) (by norm_num)
theorem B7236373 : Blo 1693547 7236373 := bbase (se 6 (by rfl) ⟨169602, by rfl⟩ : syracuseStep 7236373 = 339205) (by norm_num)
theorem B4287269 : Blo 1693547 4287269 := bbase (se 4 (by rfl) ⟨401931, by rfl⟩ : syracuseStep 4287269 = 803863) (by norm_num)
theorem B2542373 : Blo 1693547 2542373 := bbase (se 4 (by rfl) ⟨238347, by rfl⟩ : syracuseStep 2542373 = 476695) (by norm_num)
theorem B2542397 : Blo 1693547 2542397 := bbase (se 3 (by rfl) ⟨476699, by rfl⟩ : syracuseStep 2542397 = 953399) (by norm_num)
theorem B3812165 : Blo 1693547 3812165 := bbase (se 4 (by rfl) ⟨357390, by rfl⟩ : syracuseStep 3812165 = 714781) (by norm_num)
theorem B2542421 : Blo 1693547 2542421 := bbase (se 9 (by rfl) ⟨7448, by rfl⟩ : syracuseStep 2542421 = 14897) (by norm_num)
theorem B2542445 : Blo 1693547 2542445 := bbase (se 3 (by rfl) ⟨476708, by rfl⟩ : syracuseStep 2542445 = 953417) (by norm_num)
theorem B2542469 : Blo 1693547 2542469 := bbase (se 4 (by rfl) ⟨238356, by rfl⟩ : syracuseStep 2542469 = 476713) (by norm_num)
theorem B3812237 : Blo 1693547 3812237 := bbase (se 3 (by rfl) ⟨714794, by rfl⟩ : syracuseStep 3812237 = 1429589) (by norm_num)
theorem B2542493 : Blo 1693547 2542493 := bbase (se 3 (by rfl) ⟨476717, by rfl⟩ : syracuseStep 2542493 = 953435) (by norm_num)
theorem B8580005 : Blo 1693547 8580005 := bbase (se 4 (by rfl) ⟨804375, by rfl⟩ : syracuseStep 8580005 = 1608751) (by norm_num)
theorem B2542517 : Blo 1693547 2542517 := bbase (se 5 (by rfl) ⟨119180, by rfl⟩ : syracuseStep 2542517 = 238361) (by norm_num)
theorem B5721029 : Blo 1693547 5721029 := bbase (se 4 (by rfl) ⟨536346, by rfl⟩ : syracuseStep 5721029 = 1072693) (by norm_num)
theorem B2542541 : Blo 1693547 2542541 := bbase (se 3 (by rfl) ⟨476726, by rfl⟩ : syracuseStep 2542541 = 953453) (by norm_num)
theorem B3812309 : Blo 1693547 3812309 := bbase (se 7 (by rfl) ⟨44675, by rfl⟩ : syracuseStep 3812309 = 89351) (by norm_num)
theorem B2542565 : Blo 1693547 2542565 := bbase (se 4 (by rfl) ⟨238365, by rfl⟩ : syracuseStep 2542565 = 476731) (by norm_num)
theorem B2542589 : Blo 1693547 2542589 := bbase (se 3 (by rfl) ⟨476735, by rfl⟩ : syracuseStep 2542589 = 953471) (by norm_num)
theorem B2542613 : Blo 1693547 2542613 := bbase (se 6 (by rfl) ⟨59592, by rfl⟩ : syracuseStep 2542613 = 119185) (by norm_num)
theorem B3812381 : Blo 1693547 3812381 := bbase (se 3 (by rfl) ⟨714821, by rfl⟩ : syracuseStep 3812381 = 1429643) (by norm_num)
theorem B2542637 : Blo 1693547 2542637 := bbase (se 3 (by rfl) ⟨476744, by rfl⟩ : syracuseStep 2542637 = 953489) (by norm_num)
theorem B2542661 : Blo 1693547 2542661 := bbase (se 4 (by rfl) ⟨238374, by rfl⟩ : syracuseStep 2542661 = 476749) (by norm_num)
theorem B2034769 : Blo 1693547 2034769 := bbase (se 2 (by rfl) ⟨763038, by rfl⟩ : syracuseStep 2034769 = 1526077) (by norm_num)
theorem B2714717 : Blo 1693547 2714717 := bbase (se 3 (by rfl) ⟨509009, by rfl⟩ : syracuseStep 2714717 = 1018019) (by norm_num)
theorem B2542685 : Blo 1693547 2542685 := bbase (se 3 (by rfl) ⟨476753, by rfl⟩ : syracuseStep 2542685 = 953507) (by norm_num)
theorem B3812453 : Blo 1693547 3812453 := bbase (se 4 (by rfl) ⟨357417, by rfl⟩ : syracuseStep 3812453 = 714835) (by norm_num)
theorem B2542709 : Blo 1693547 2542709 := bbase (se 5 (by rfl) ⟨119189, by rfl⟩ : syracuseStep 2542709 = 238379) (by norm_num)
theorem B4287613 : Blo 1693547 4287613 := bbase (se 3 (by rfl) ⟨803927, by rfl⟩ : syracuseStep 4287613 = 1607855) (by norm_num)
theorem B2542733 : Blo 1693547 2542733 := bbase (se 3 (by rfl) ⟨476762, by rfl⟩ : syracuseStep 2542733 = 953525) (by norm_num)
theorem B12217493 : Blo 1693547 12217493 := bbase (se 6 (by rfl) ⟨286347, by rfl⟩ : syracuseStep 12217493 = 572695) (by norm_num)
theorem B2542757 : Blo 1693547 2542757 := bbase (se 4 (by rfl) ⟨238383, by rfl⟩ : syracuseStep 2542757 = 476767) (by norm_num)
theorem B3812525 : Blo 1693547 3812525 := bbase (se 3 (by rfl) ⟨714848, by rfl⟩ : syracuseStep 3812525 = 1429697) (by norm_num)
theorem B2034865 : Blo 1693547 2034865 := bbase (se 2 (by rfl) ⟨763074, by rfl⟩ : syracuseStep 2034865 = 1526149) (by norm_num)
theorem B5426357 : Blo 1693547 5426357 := bbase (se 5 (by rfl) ⟨254360, by rfl⟩ : syracuseStep 5426357 = 508721) (by norm_num)
theorem B2542781 : Blo 1693547 2542781 := bbase (se 3 (by rfl) ⟨476771, by rfl⟩ : syracuseStep 2542781 = 953543) (by norm_num)
theorem B2542805 : Blo 1693547 2542805 := bbase (se 7 (by rfl) ⟨29798, by rfl⟩ : syracuseStep 2542805 = 59597) (by norm_num)
theorem B4287725 : Blo 1693547 4287725 := bbase (se 3 (by rfl) ⟨803948, by rfl⟩ : syracuseStep 4287725 = 1607897) (by norm_num)
theorem B2542829 : Blo 1693547 2542829 := bbase (se 3 (by rfl) ⟨476780, by rfl⟩ : syracuseStep 2542829 = 953561) (by norm_num)
theorem B3812597 : Blo 1693547 3812597 := bbase (se 5 (by rfl) ⟨178715, by rfl⟩ : syracuseStep 3812597 = 357431) (by norm_num)
theorem B2542853 : Blo 1693547 2542853 := bbase (se 4 (by rfl) ⟨238392, by rfl⟩ : syracuseStep 2542853 = 476785) (by norm_num)
theorem B2542877 : Blo 1693547 2542877 := bbase (se 3 (by rfl) ⟨476789, by rfl⟩ : syracuseStep 2542877 = 953579) (by norm_num)
theorem B2542901 : Blo 1693547 2542901 := bbase (se 5 (by rfl) ⟨119198, by rfl⟩ : syracuseStep 2542901 = 238397) (by norm_num)
theorem B3812669 : Blo 1693547 3812669 := bbase (se 3 (by rfl) ⟨714875, by rfl⟩ : syracuseStep 3812669 = 1429751) (by norm_num)
theorem B2542925 : Blo 1693547 2542925 := bbase (se 3 (by rfl) ⟨476798, by rfl⟩ : syracuseStep 2542925 = 953597) (by norm_num)
theorem B2542949 : Blo 1693547 2542949 := bbase (se 4 (by rfl) ⟨238401, by rfl⟩ : syracuseStep 2542949 = 476803) (by norm_num)
theorem B5721461 : Blo 1693547 5721461 := bbase (se 5 (by rfl) ⟨268193, by rfl⟩ : syracuseStep 5721461 = 536387) (by norm_num)
theorem B2542973 : Blo 1693547 2542973 := bbase (se 3 (by rfl) ⟨476807, by rfl⟩ : syracuseStep 2542973 = 953615) (by norm_num)
theorem B3812741 : Blo 1693547 3812741 := bbase (se 4 (by rfl) ⟨357444, by rfl⟩ : syracuseStep 3812741 = 714889) (by norm_num)
theorem B2542997 : Blo 1693547 2542997 := bbase (se 6 (by rfl) ⟨59601, by rfl⟩ : syracuseStep 2542997 = 119203) (by norm_num)
theorem B4287917 : Blo 1693547 4287917 := bbase (se 3 (by rfl) ⟨803984, by rfl⟩ : syracuseStep 4287917 = 1607969) (by norm_num)
theorem B2543021 : Blo 1693547 2543021 := bbase (se 3 (by rfl) ⟨476816, by rfl⟩ : syracuseStep 2543021 = 953633) (by norm_num)
theorem B2411965 : Blo 1693547 2411965 := bbase (se 3 (by rfl) ⟨452243, by rfl⟩ : syracuseStep 2411965 = 904487) (by norm_num)
theorem B2543045 : Blo 1693547 2543045 := bbase (se 4 (by rfl) ⟨238410, by rfl⟩ : syracuseStep 2543045 = 476821) (by norm_num)
theorem B3812813 : Blo 1693547 3812813 := bbase (se 3 (by rfl) ⟨714902, by rfl⟩ : syracuseStep 3812813 = 1429805) (by norm_num)
theorem B6434261 : Blo 1693547 6434261 := bbase (se 7 (by rfl) ⟨75401, by rfl⟩ : syracuseStep 6434261 = 150803) (by norm_num)
theorem B2543069 : Blo 1693547 2543069 := bbase (se 3 (by rfl) ⟨476825, by rfl⟩ : syracuseStep 2543069 = 953651) (by norm_num)
theorem B2543093 : Blo 1693547 2543093 := bbase (se 5 (by rfl) ⟨119207, by rfl⟩ : syracuseStep 2543093 = 238415) (by norm_num)
theorem B2543117 : Blo 1693547 2543117 := bbase (se 3 (by rfl) ⟨476834, by rfl⟩ : syracuseStep 2543117 = 953669) (by norm_num)
theorem B3812885 : Blo 1693547 3812885 := bbase (se 6 (by rfl) ⟨89364, by rfl⟩ : syracuseStep 3812885 = 178729) (by norm_num)
theorem B2543141 : Blo 1693547 2543141 := bbase (se 4 (by rfl) ⟨238419, by rfl⟩ : syracuseStep 2543141 = 476839) (by norm_num)
theorem B2543165 : Blo 1693547 2543165 := bbase (se 3 (by rfl) ⟨476843, by rfl⟩ : syracuseStep 2543165 = 953687) (by norm_num)
theorem B2543189 : Blo 1693547 2543189 := bbase (se 8 (by rfl) ⟨14901, by rfl⟩ : syracuseStep 2543189 = 29803) (by norm_num)
theorem B3812957 : Blo 1693547 3812957 := bbase (se 3 (by rfl) ⟨714929, by rfl⟩ : syracuseStep 3812957 = 1429859) (by norm_num)
theorem B2715229 : Blo 1693547 2715229 := bbase (se 3 (by rfl) ⟨509105, by rfl⟩ : syracuseStep 2715229 = 1018211) (by norm_num)
theorem B2543213 : Blo 1693547 2543213 := bbase (se 3 (by rfl) ⟨476852, by rfl⟩ : syracuseStep 2543213 = 953705) (by norm_num)
theorem B2543237 : Blo 1693547 2543237 := bbase (se 4 (by rfl) ⟨238428, by rfl⟩ : syracuseStep 2543237 = 476857) (by norm_num)
theorem B2543261 : Blo 1693547 2543261 := bbase (se 3 (by rfl) ⟨476861, by rfl⟩ : syracuseStep 2543261 = 953723) (by norm_num)
theorem B3813029 : Blo 1693547 3813029 := bbase (se 4 (by rfl) ⟨357471, by rfl⟩ : syracuseStep 3813029 = 714943) (by norm_num)
theorem B2092721 : Blo 1693547 2092721 := bbase (se 2 (by rfl) ⟨784770, by rfl⟩ : syracuseStep 2092721 = 1569541) (by norm_num)
theorem B2543285 : Blo 1693547 2543285 := bbase (se 5 (by rfl) ⟨119216, by rfl⟩ : syracuseStep 2543285 = 238433) (by norm_num)
theorem B2543309 : Blo 1693547 2543309 := bbase (se 3 (by rfl) ⟨476870, by rfl⟩ : syracuseStep 2543309 = 953741) (by norm_num)
theorem B3813101 : Blo 1693547 3813101 := bbase (se 3 (by rfl) ⟨714956, by rfl⟩ : syracuseStep 3813101 = 1429913) (by norm_num)
theorem B6434549 : Blo 1693547 6434549 := bbase (se 5 (by rfl) ⟨301619, by rfl⟩ : syracuseStep 6434549 = 603239) (by norm_num)
theorem B8138501 : Blo 1693547 8138501 := bbase (se 4 (by rfl) ⟨762984, by rfl⟩ : syracuseStep 8138501 = 1525969) (by norm_num)
theorem B4288261 : Blo 1693547 4288261 := bbase (se 4 (by rfl) ⟨402024, by rfl⟩ : syracuseStep 4288261 = 804049) (by norm_num)
theorem B3436301 : Blo 1693547 3436301 := bbase (se 3 (by rfl) ⟨644306, by rfl⟩ : syracuseStep 3436301 = 1288613) (by norm_num)
theorem B5721893 : Blo 1693547 5721893 := bbase (se 4 (by rfl) ⟨536427, by rfl⟩ : syracuseStep 5721893 = 1072855) (by norm_num)
theorem B3813173 : Blo 1693547 3813173 := bbase (se 5 (by rfl) ⟨178742, by rfl⟩ : syracuseStep 3813173 = 357485) (by norm_num)
theorem B5959477 : Blo 1693547 5959477 := bbase (se 5 (by rfl) ⟨279350, by rfl⟩ : syracuseStep 5959477 = 558701) (by norm_num)
theorem B11587445 : Blo 1693547 11587445 := bbase (se 5 (by rfl) ⟨543161, by rfl⟩ : syracuseStep 11587445 = 1086323) (by norm_num)
theorem B4288373 : Blo 1693547 4288373 := bbase (se 5 (by rfl) ⟨201017, by rfl⟩ : syracuseStep 4288373 = 402035) (by norm_num)
theorem B7729013 : Blo 1693547 7729013 := bbase (se 5 (by rfl) ⟨362297, by rfl⟩ : syracuseStep 7729013 = 724595) (by norm_num)
theorem B3813245 : Blo 1693547 3813245 := bbase (se 3 (by rfl) ⟨714983, by rfl⟩ : syracuseStep 3813245 = 1429967) (by norm_num)
theorem B3215285 : Blo 1693547 3215285 := bbase (se 5 (by rfl) ⟨150716, by rfl⟩ : syracuseStep 3215285 = 301433) (by norm_num)
theorem B12873653 : Blo 1693547 12873653 := bbase (se 5 (by rfl) ⟨603452, by rfl⟩ : syracuseStep 12873653 = 1206905) (by norm_num)
theorem B2035649 : Blo 1693547 2035649 := bbase (se 2 (by rfl) ⟨763368, by rfl⟩ : syracuseStep 2035649 = 1526737) (by norm_num)
theorem B3813317 : Blo 1693547 3813317 := bbase (se 4 (by rfl) ⟨357498, by rfl⟩ : syracuseStep 3813317 = 714997) (by norm_num)
theorem B9646037 : Blo 1693547 9646037 := bbase (se 7 (by rfl) ⟨113039, by rfl⟩ : syracuseStep 9646037 = 226079) (by norm_num)
theorem B2289677 : Blo 1693547 2289677 := bbase (se 3 (by rfl) ⟨429314, by rfl⟩ : syracuseStep 2289677 = 858629) (by norm_num)
theorem B3813389 : Blo 1693547 3813389 := bbase (se 3 (by rfl) ⟨715010, by rfl⟩ : syracuseStep 3813389 = 1430021) (by norm_num)
theorem B4288565 : Blo 1693547 4288565 := bbase (se 5 (by rfl) ⟨201026, by rfl⟩ : syracuseStep 4288565 = 402053) (by norm_num)
theorem B5427269 : Blo 1693547 5427269 := bbase (se 4 (by rfl) ⟨508806, by rfl⟩ : syracuseStep 5427269 = 1017613) (by norm_num)
theorem B3813461 : Blo 1693547 3813461 := bbase (se 8 (by rfl) ⟨22344, by rfl⟩ : syracuseStep 3813461 = 44689) (by norm_num)
theorem B3969181 : Blo 1693547 3969181 := bbase (se 3 (by rfl) ⟨744221, by rfl⟩ : syracuseStep 3969181 = 1488443) (by norm_num)
theorem B3813533 : Blo 1693547 3813533 := bbase (se 3 (by rfl) ⟨715037, by rfl⟩ : syracuseStep 3813533 = 1430075) (by norm_num)
theorem B8581301 : Blo 1693547 8581301 := bbase (se 5 (by rfl) ⟨402248, by rfl⟩ : syracuseStep 8581301 = 804497) (by norm_num)
theorem B2412757 : Blo 1693547 2412757 := bbase (se 7 (by rfl) ⟨28274, by rfl⟩ : syracuseStep 2412757 = 56549) (by norm_num)
theorem B5722325 : Blo 1693547 5722325 := bbase (se 7 (by rfl) ⟨67058, by rfl⟩ : syracuseStep 5722325 = 134117) (by norm_num)
theorem B3813605 : Blo 1693547 3813605 := bbase (se 4 (by rfl) ⟨357525, by rfl⟩ : syracuseStep 3813605 = 715051) (by norm_num)
theorem B4346093 : Blo 1693547 4346093 := bbase (se 3 (by rfl) ⟨814892, by rfl⟩ : syracuseStep 4346093 = 1629785) (by norm_num)
theorem B2035957 : Blo 1693547 2035957 := bbase (se 5 (by rfl) ⟨95435, by rfl⟩ : syracuseStep 2035957 = 190871) (by norm_num)
theorem B3813677 : Blo 1693547 3813677 := bbase (se 3 (by rfl) ⟨715064, by rfl⟩ : syracuseStep 3813677 = 1430129) (by norm_num)
theorem B3617093 : Blo 1693547 3617093 := bbase (se 4 (by rfl) ⟨339102, by rfl⟩ : syracuseStep 3617093 = 678205) (by norm_num)
theorem B12865877 : Blo 1693547 12865877 := bbase (se 10 (by rfl) ⟨18846, by rfl⟩ : syracuseStep 12865877 = 37693) (by norm_num)
theorem B3813749 : Blo 1693547 3813749 := bbase (se 5 (by rfl) ⟨178769, by rfl⟩ : syracuseStep 3813749 = 357539) (by norm_num)
theorem B4288909 : Blo 1693547 4288909 := bbase (se 3 (by rfl) ⟨804170, by rfl⟩ : syracuseStep 4288909 = 1608341) (by norm_num)
theorem B8253845 : Blo 1693547 8253845 := bbase (se 6 (by rfl) ⟨193449, by rfl⟩ : syracuseStep 8253845 = 386899) (by norm_num)
theorem B3813821 : Blo 1693547 3813821 := bbase (se 3 (by rfl) ⟨715091, by rfl⟩ : syracuseStep 3813821 = 1430183) (by norm_num)
theorem B7336421 : Blo 1693547 7336421 := bbase (se 4 (by rfl) ⟨687789, by rfl⟩ : syracuseStep 7336421 = 1375579) (by norm_num)
theorem B4289021 : Blo 1693547 4289021 := bbase (se 3 (by rfl) ⟨804191, by rfl⟩ : syracuseStep 4289021 = 1608383) (by norm_num)
theorem B3813893 : Blo 1693547 3813893 := bbase (se 4 (by rfl) ⟨357552, by rfl⟩ : syracuseStep 3813893 = 715105) (by norm_num)
theorem B2413093 : Blo 1693547 2413093 := bbase (se 4 (by rfl) ⟨226227, by rfl⟩ : syracuseStep 2413093 = 452455) (by norm_num)
theorem B3813965 : Blo 1693547 3813965 := bbase (se 3 (by rfl) ⟨715118, by rfl⟩ : syracuseStep 3813965 = 1430237) (by norm_num)
theorem B1905241 : Blo 1693547 1905241 := bbase (se 2 (by rfl) ⟨714465, by rfl⟩ : syracuseStep 1905241 = 1428931) (by norm_num)
theorem B1716833 : Blo 1693547 1716833 := bbase (se 2 (by rfl) ⟨643812, by rfl⟩ : syracuseStep 1716833 = 1287625) (by norm_num)
theorem B2036345 : Blo 1693547 2036345 := bbase (se 2 (by rfl) ⟨763629, by rfl⟩ : syracuseStep 2036345 = 1527259) (by norm_num)
theorem B1905277 : Blo 1693547 1905277 := bbase (se 3 (by rfl) ⟨357239, by rfl⟩ : syracuseStep 1905277 = 714479) (by norm_num)
theorem B3814037 : Blo 1693547 3814037 := bbase (se 6 (by rfl) ⟨89391, by rfl⟩ : syracuseStep 3814037 = 178783) (by norm_num)
theorem B1905313 : Blo 1693547 1905313 := bbase (se 2 (by rfl) ⟨714492, by rfl⟩ : syracuseStep 1905313 = 1428985) (by norm_num)
theorem B3216037 : Blo 1693547 3216037 := bbase (se 4 (by rfl) ⟨301503, by rfl⟩ : syracuseStep 3216037 = 603007) (by norm_num)
theorem B3617453 : Blo 1693547 3617453 := bbase (se 3 (by rfl) ⟨678272, by rfl⟩ : syracuseStep 3617453 = 1356545) (by norm_num)
theorem B4289213 : Blo 1693547 4289213 := bbase (se 3 (by rfl) ⟨804227, by rfl⟩ : syracuseStep 4289213 = 1608455) (by norm_num)
theorem B1905349 : Blo 1693547 1905349 := bbase (se 4 (by rfl) ⟨178626, by rfl⟩ : syracuseStep 1905349 = 357253) (by norm_num)
theorem B6869717 : Blo 1693547 6869717 := bbase (se 7 (by rfl) ⟨80504, by rfl⟩ : syracuseStep 6869717 = 161009) (by norm_num)
theorem B3814109 : Blo 1693547 3814109 := bbase (se 3 (by rfl) ⟨715145, by rfl⟩ : syracuseStep 3814109 = 1430291) (by norm_num)
theorem B1905385 : Blo 1693547 1905385 := bbase (se 2 (by rfl) ⟨714519, by rfl⟩ : syracuseStep 1905385 = 1429039) (by norm_num)
theorem B3863285 : Blo 1693547 3863285 := bbase (se 5 (by rfl) ⟨181091, by rfl⟩ : syracuseStep 3863285 = 362183) (by norm_num)
theorem B2413309 : Blo 1693547 2413309 := bbase (se 3 (by rfl) ⟨452495, by rfl⟩ : syracuseStep 2413309 = 904991) (by norm_num)
theorem B1905421 : Blo 1693547 1905421 := bbase (se 3 (by rfl) ⟨357266, by rfl⟩ : syracuseStep 1905421 = 714533) (by norm_num)
theorem B3814181 : Blo 1693547 3814181 := bbase (se 4 (by rfl) ⟨357579, by rfl⟩ : syracuseStep 3814181 = 715159) (by norm_num)
theorem B1905457 : Blo 1693547 1905457 := bbase (se 2 (by rfl) ⟨714546, by rfl⟩ : syracuseStep 1905457 = 1429093) (by norm_num)
theorem B3216181 : Blo 1693547 3216181 := bbase (se 5 (by rfl) ⟨150758, by rfl⟩ : syracuseStep 3216181 = 301517) (by norm_num)
theorem B1905493 : Blo 1693547 1905493 := bbase (se 9 (by rfl) ⟨5582, by rfl⟩ : syracuseStep 1905493 = 11165) (by norm_num)
theorem B3814253 : Blo 1693547 3814253 := bbase (se 3 (by rfl) ⟨715172, by rfl⟩ : syracuseStep 3814253 = 1430345) (by norm_num)
theorem B1905529 : Blo 1693547 1905529 := bbase (se 2 (by rfl) ⟨714573, by rfl⟩ : syracuseStep 1905529 = 1429147) (by norm_num)
theorem B6435733 : Blo 1693547 6435733 := bbase (se 6 (by rfl) ⟨150837, by rfl⟩ : syracuseStep 6435733 = 301675) (by norm_num)
theorem B1905565 : Blo 1693547 1905565 := bbase (se 3 (by rfl) ⟨357293, by rfl⟩ : syracuseStep 1905565 = 714587) (by norm_num)
theorem B3814325 : Blo 1693547 3814325 := bbase (se 5 (by rfl) ⟨178796, by rfl⟩ : syracuseStep 3814325 = 357593) (by norm_num)
theorem B1905601 : Blo 1693547 1905601 := bbase (se 2 (by rfl) ⟨714600, by rfl⟩ : syracuseStep 1905601 = 1429201) (by norm_num)
theorem B3216341 : Blo 1693547 3216341 := bbase (se 7 (by rfl) ⟨37691, by rfl⟩ : syracuseStep 3216341 = 75383) (by norm_num)
theorem B2036701 : Blo 1693547 2036701 := bbase (se 3 (by rfl) ⟨381881, by rfl⟩ : syracuseStep 2036701 = 763763) (by norm_num)
theorem B1905637 : Blo 1693547 1905637 := bbase (se 4 (by rfl) ⟨178653, by rfl⟩ : syracuseStep 1905637 = 357307) (by norm_num)
theorem B1741805 : Blo 1693547 1741805 := bbase (se 3 (by rfl) ⟨326588, by rfl⟩ : syracuseStep 1741805 = 653177) (by norm_num)
theorem B3814397 : Blo 1693547 3814397 := bbase (se 3 (by rfl) ⟨715199, by rfl⟩ : syracuseStep 3814397 = 1430399) (by norm_num)
theorem B1905673 : Blo 1693547 1905673 := bbase (se 2 (by rfl) ⟨714627, by rfl⟩ : syracuseStep 1905673 = 1429255) (by norm_num)
theorem B4289557 : Blo 1693547 4289557 := bbase (se 6 (by rfl) ⟨100536, by rfl⟩ : syracuseStep 4289557 = 201073) (by norm_num)
theorem B1905709 : Blo 1693547 1905709 := bbase (se 3 (by rfl) ⟨357320, by rfl⟩ : syracuseStep 1905709 = 714641) (by norm_num)
theorem B3814469 : Blo 1693547 3814469 := bbase (se 4 (by rfl) ⟨357606, by rfl⟩ : syracuseStep 3814469 = 715213) (by norm_num)
theorem B1905745 : Blo 1693547 1905745 := bbase (se 2 (by rfl) ⟨714654, by rfl⟩ : syracuseStep 1905745 = 1429309) (by norm_num)
theorem B3216485 : Blo 1693547 3216485 := bbase (se 4 (by rfl) ⟨301545, by rfl⟩ : syracuseStep 3216485 = 603091) (by norm_num)
theorem B1741937 : Blo 1693547 1741937 := bbase (se 2 (by rfl) ⟨653226, by rfl⟩ : syracuseStep 1741937 = 1306453) (by norm_num)
theorem B9647221 : Blo 1693547 9647221 := bbase (se 5 (by rfl) ⟨452213, by rfl⟩ : syracuseStep 9647221 = 904427) (by norm_num)
theorem B1905781 : Blo 1693547 1905781 := bbase (se 5 (by rfl) ⟨89333, by rfl⟩ : syracuseStep 1905781 = 178667) (by norm_num)
theorem B2413685 : Blo 1693547 2413685 := bbase (se 5 (by rfl) ⟨113141, by rfl⟩ : syracuseStep 2413685 = 226283) (by norm_num)
theorem B4289669 : Blo 1693547 4289669 := bbase (se 4 (by rfl) ⟨402156, by rfl⟩ : syracuseStep 4289669 = 804313) (by norm_num)
theorem B3814541 : Blo 1693547 3814541 := bbase (se 3 (by rfl) ⟨715226, by rfl⟩ : syracuseStep 3814541 = 1430453) (by norm_num)
theorem B1905817 : Blo 1693547 1905817 := bbase (se 2 (by rfl) ⟨714681, by rfl⟩ : syracuseStep 1905817 = 1429363) (by norm_num)
theorem B2143417 : Blo 1693547 2143417 := bbase (se 2 (by rfl) ⟨803781, by rfl⟩ : syracuseStep 2143417 = 1607563) (by norm_num)
theorem B1905853 : Blo 1693547 1905853 := bbase (se 3 (by rfl) ⟨357347, by rfl⟩ : syracuseStep 1905853 = 714695) (by norm_num)
theorem B6436037 : Blo 1693547 6436037 := bbase (se 4 (by rfl) ⟨603378, by rfl⟩ : syracuseStep 6436037 = 1206757) (by norm_num)
theorem B1717453 : Blo 1693547 1717453 := bbase (se 3 (by rfl) ⟨322022, by rfl⟩ : syracuseStep 1717453 = 644045) (by norm_num)
theorem B3814613 : Blo 1693547 3814613 := bbase (se 7 (by rfl) ⟨44702, by rfl⟩ : syracuseStep 3814613 = 89405) (by norm_num)
theorem B1905889 : Blo 1693547 1905889 := bbase (se 2 (by rfl) ⟨714708, by rfl⟩ : syracuseStep 1905889 = 1429417) (by norm_num)
theorem B1905925 : Blo 1693547 1905925 := bbase (se 4 (by rfl) ⟨178680, by rfl⟩ : syracuseStep 1905925 = 357361) (by norm_num)
theorem B7730437 : Blo 1693547 7730437 := bbase (se 4 (by rfl) ⟨724728, by rfl⟩ : syracuseStep 7730437 = 1449457) (by norm_num)
theorem B27866389 : Blo 1693547 27866389 := bbase (se 6 (by rfl) ⟨653118, by rfl⟩ : syracuseStep 27866389 = 1306237) (by norm_num)
theorem B2143513 : Blo 1693547 2143513 := bbase (se 2 (by rfl) ⟨803817, by rfl⟩ : syracuseStep 2143513 = 1607635) (by norm_num)
theorem B3814685 : Blo 1693547 3814685 := bbase (se 3 (by rfl) ⟨715253, by rfl⟩ : syracuseStep 3814685 = 1430507) (by norm_num)
theorem B1905961 : Blo 1693547 1905961 := bbase (se 2 (by rfl) ⟨714735, by rfl⟩ : syracuseStep 1905961 = 1429471) (by norm_num)
theorem B4289861 : Blo 1693547 4289861 := bbase (se 4 (by rfl) ⟨402174, by rfl⟩ : syracuseStep 4289861 = 804349) (by norm_num)
theorem B1905997 : Blo 1693547 1905997 := bbase (se 3 (by rfl) ⟨357374, by rfl⟩ : syracuseStep 1905997 = 714749) (by norm_num)
theorem B3814757 : Blo 1693547 3814757 := bbase (se 4 (by rfl) ⟨357633, by rfl⟩ : syracuseStep 3814757 = 715267) (by norm_num)
theorem B1906033 : Blo 1693547 1906033 := bbase (se 2 (by rfl) ⟨714762, by rfl⟩ : syracuseStep 1906033 = 1429525) (by norm_num)
theorem B3216773 : Blo 1693547 3216773 := bbase (se 4 (by rfl) ⟨301572, by rfl⟩ : syracuseStep 3216773 = 603145) (by norm_num)
theorem B5428613 : Blo 1693547 5428613 := bbase (se 4 (by rfl) ⟨508932, by rfl⟩ : syracuseStep 5428613 = 1017865) (by norm_num)
theorem B1906069 : Blo 1693547 1906069 := bbase (se 6 (by rfl) ⟨44673, by rfl⟩ : syracuseStep 1906069 = 89347) (by norm_num)
theorem B3814829 : Blo 1693547 3814829 := bbase (se 3 (by rfl) ⟨715280, by rfl⟩ : syracuseStep 3814829 = 1430561) (by norm_num)
theorem B1906105 : Blo 1693547 1906105 := bbase (se 2 (by rfl) ⟨714789, by rfl⟩ : syracuseStep 1906105 = 1429579) (by norm_num)
theorem B2143685 : Blo 1693547 2143685 := bbase (se 4 (by rfl) ⟨200970, by rfl⟩ : syracuseStep 2143685 = 401941) (by norm_num)
theorem B8582597 : Blo 1693547 8582597 := bbase (se 4 (by rfl) ⟨804618, by rfl⟩ : syracuseStep 8582597 = 1609237) (by norm_num)
theorem B1906141 : Blo 1693547 1906141 := bbase (se 3 (by rfl) ⟨357401, by rfl⟩ : syracuseStep 1906141 = 714803) (by norm_num)
theorem B3814901 : Blo 1693547 3814901 := bbase (se 5 (by rfl) ⟨178823, by rfl⟩ : syracuseStep 3814901 = 357647) (by norm_num)
theorem B2143741 : Blo 1693547 2143741 := bbase (se 3 (by rfl) ⟨401951, by rfl⟩ : syracuseStep 2143741 = 803903) (by norm_num)
theorem B1906177 : Blo 1693547 1906177 := bbase (se 2 (by rfl) ⟨714816, by rfl⟩ : syracuseStep 1906177 = 1429633) (by norm_num)
theorem B2291213 : Blo 1693547 2291213 := bbase (se 3 (by rfl) ⟨429602, by rfl⟩ : syracuseStep 2291213 = 859205) (by norm_num)
theorem B1717777 : Blo 1693547 1717777 := bbase (se 2 (by rfl) ⟨644166, by rfl⟩ : syracuseStep 1717777 = 1288333) (by norm_num)
theorem B5879317 : Blo 1693547 5879317 := bbase (se 6 (by rfl) ⟨137796, by rfl⟩ : syracuseStep 5879317 = 275593) (by norm_num)
theorem B3216925 : Blo 1693547 3216925 := bbase (se 3 (by rfl) ⟨603173, by rfl⟩ : syracuseStep 3216925 = 1206347) (by norm_num)
theorem B3618341 : Blo 1693547 3618341 := bbase (se 4 (by rfl) ⟨339219, by rfl⟩ : syracuseStep 3618341 = 678439) (by norm_num)
theorem B1906213 : Blo 1693547 1906213 := bbase (se 4 (by rfl) ⟨178707, by rfl⟩ : syracuseStep 1906213 = 357415) (by norm_num)
theorem B13923893 : Blo 1693547 13923893 := bbase (se 5 (by rfl) ⟨652682, by rfl⟩ : syracuseStep 13923893 = 1305365) (by norm_num)
theorem B3814973 : Blo 1693547 3814973 := bbase (se 3 (by rfl) ⟨715307, by rfl⟩ : syracuseStep 3814973 = 1430615) (by norm_num)
theorem B1906249 : Blo 1693547 1906249 := bbase (se 2 (by rfl) ⟨714843, by rfl⟩ : syracuseStep 1906249 = 1429687) (by norm_num)
theorem B2143837 : Blo 1693547 2143837 := bbase (se 3 (by rfl) ⟨401969, by rfl⟩ : syracuseStep 2143837 = 803939) (by norm_num)
theorem B1906285 : Blo 1693547 1906285 := bbase (se 3 (by rfl) ⟨357428, by rfl⟩ : syracuseStep 1906285 = 714857) (by norm_num)
theorem B1906321 : Blo 1693547 1906321 := bbase (se 2 (by rfl) ⟨714870, by rfl⟩ : syracuseStep 1906321 = 1429741) (by norm_num)
theorem B4290205 : Blo 1693547 4290205 := bbase (se 3 (by rfl) ⟨804413, by rfl⟩ : syracuseStep 4290205 = 1608827) (by norm_num)
theorem B1906357 : Blo 1693547 1906357 := bbase (se 5 (by rfl) ⟨89360, by rfl⟩ : syracuseStep 1906357 = 178721) (by norm_num)
theorem B7239365 : Blo 1693547 7239365 := bbase (se 4 (by rfl) ⟨678690, by rfl⟩ : syracuseStep 7239365 = 1357381) (by norm_num)
theorem B1906393 : Blo 1693547 1906393 := bbase (se 2 (by rfl) ⟨714897, by rfl⟩ : syracuseStep 1906393 = 1429795) (by norm_num)
theorem B10860277 : Blo 1693547 10860277 := bbase (se 5 (by rfl) ⟨509075, by rfl⟩ : syracuseStep 10860277 = 1018151) (by norm_num)
theorem B1906429 : Blo 1693547 1906429 := bbase (se 3 (by rfl) ⟨357455, by rfl⟩ : syracuseStep 1906429 = 714911) (by norm_num)
theorem B2144009 : Blo 1693547 2144009 := bbase (se 2 (by rfl) ⟨804003, by rfl⟩ : syracuseStep 2144009 = 1608007) (by norm_num)
theorem B4290317 : Blo 1693547 4290317 := bbase (se 3 (by rfl) ⟨804434, by rfl⟩ : syracuseStep 4290317 = 1608869) (by norm_num)
theorem B3618589 : Blo 1693547 3618589 := bbase (se 3 (by rfl) ⟨678485, by rfl⟩ : syracuseStep 3618589 = 1356971) (by norm_num)
theorem B1906465 : Blo 1693547 1906465 := bbase (se 2 (by rfl) ⟨714924, by rfl⟩ : syracuseStep 1906465 = 1429849) (by norm_num)
theorem B2144065 : Blo 1693547 2144065 := bbase (se 2 (by rfl) ⟨804024, by rfl⟩ : syracuseStep 2144065 = 1608049) (by norm_num)
theorem B1906501 : Blo 1693547 1906501 := bbase (se 4 (by rfl) ⟨178734, by rfl⟩ : syracuseStep 1906501 = 357469) (by norm_num)
theorem B3217229 : Blo 1693547 3217229 := bbase (se 3 (by rfl) ⟨603230, by rfl⟩ : syracuseStep 3217229 = 1206461) (by norm_num)
theorem B8574821 : Blo 1693547 8574821 := bbase (se 4 (by rfl) ⟨803889, by rfl⟩ : syracuseStep 8574821 = 1607779) (by norm_num)
theorem B1906537 : Blo 1693547 1906537 := bbase (se 2 (by rfl) ⟨714951, by rfl⟩ : syracuseStep 1906537 = 1429903) (by norm_num)
theorem B5715845 : Blo 1693547 5715845 := bbase (se 4 (by rfl) ⟨535860, by rfl⟩ : syracuseStep 5715845 = 1071721) (by norm_num)
theorem B1906573 : Blo 1693547 1906573 := bbase (se 3 (by rfl) ⟨357482, by rfl⟩ : syracuseStep 1906573 = 714965) (by norm_num)
theorem B2144161 : Blo 1693547 2144161 := bbase (se 2 (by rfl) ⟨804060, by rfl⟩ : syracuseStep 2144161 = 1608121) (by norm_num)
theorem B3717029 : Blo 1693547 3717029 := bbase (se 4 (by rfl) ⟨348471, by rfl⟩ : syracuseStep 3717029 = 696943) (by norm_num)
theorem B1906609 : Blo 1693547 1906609 := bbase (se 2 (by rfl) ⟨714978, by rfl⟩ : syracuseStep 1906609 = 1429957) (by norm_num)
theorem B4290509 : Blo 1693547 4290509 := bbase (se 3 (by rfl) ⟨804470, by rfl⟩ : syracuseStep 4290509 = 1608941) (by norm_num)
theorem B1906645 : Blo 1693547 1906645 := bbase (se 7 (by rfl) ⟨22343, by rfl⟩ : syracuseStep 1906645 = 44687) (by norm_num)
theorem B5150693 : Blo 1693547 5150693 := bbase (se 4 (by rfl) ⟨482877, by rfl⟩ : syracuseStep 5150693 = 965755) (by norm_num)
theorem B1906681 : Blo 1693547 1906681 := bbase (se 2 (by rfl) ⟨715005, by rfl⟩ : syracuseStep 1906681 = 1430011) (by norm_num)
theorem B21714965 : Blo 1693547 21714965 := bbase (se 6 (by rfl) ⟨508944, by rfl⟩ : syracuseStep 21714965 = 1017889) (by norm_num)
theorem B1906717 : Blo 1693547 1906717 := bbase (se 3 (by rfl) ⟨357509, by rfl⟩ : syracuseStep 1906717 = 715019) (by norm_num)
theorem B1718329 : Blo 1693547 1718329 := bbase (se 2 (by rfl) ⟨644373, by rfl⟩ : syracuseStep 1718329 = 1288747) (by norm_num)
theorem B1906753 : Blo 1693547 1906753 := bbase (se 2 (by rfl) ⟨715032, by rfl⟩ : syracuseStep 1906753 = 1430065) (by norm_num)
theorem B1718345 : Blo 1693547 1718345 := bbase (se 2 (by rfl) ⟨644379, by rfl⟩ : syracuseStep 1718345 = 1288759) (by norm_num)
theorem B4069453 : Blo 1693547 4069453 := bbase (se 3 (by rfl) ⟨763022, by rfl⟩ : syracuseStep 4069453 = 1526045) (by norm_num)
theorem B2144333 : Blo 1693547 2144333 := bbase (se 3 (by rfl) ⟨402062, by rfl⟩ : syracuseStep 2144333 = 804125) (by norm_num)
theorem B1906789 : Blo 1693547 1906789 := bbase (se 4 (by rfl) ⟨178761, by rfl⟩ : syracuseStep 1906789 = 357523) (by norm_num)
theorem B1931369 : Blo 1693547 1931369 := bbase (se 2 (by rfl) ⟨724263, by rfl⟩ : syracuseStep 1931369 = 1448527) (by norm_num)
theorem B2144389 : Blo 1693547 2144389 := bbase (se 4 (by rfl) ⟨201036, by rfl⟩ : syracuseStep 2144389 = 402073) (by norm_num)
theorem B1906825 : Blo 1693547 1906825 := bbase (se 2 (by rfl) ⟨715059, by rfl⟩ : syracuseStep 1906825 = 1430119) (by norm_num)
theorem B3668125 : Blo 1693547 3668125 := bbase (se 3 (by rfl) ⟨687773, by rfl⟩ : syracuseStep 3668125 = 1375547) (by norm_num)
theorem B1906861 : Blo 1693547 1906861 := bbase (se 3 (by rfl) ⟨357536, by rfl⟩ : syracuseStep 1906861 = 715073) (by norm_num)
theorem B6109381 : Blo 1693547 6109381 := bbase (se 4 (by rfl) ⟨572754, by rfl⟩ : syracuseStep 6109381 = 1145509) (by norm_num)
theorem B1906897 : Blo 1693547 1906897 := bbase (se 2 (by rfl) ⟨715086, by rfl⟩ : syracuseStep 1906897 = 1430173) (by norm_num)
theorem B2144485 : Blo 1693547 2144485 := bbase (se 4 (by rfl) ⟨201045, by rfl⟩ : syracuseStep 2144485 = 402091) (by norm_num)
theorem B1906933 : Blo 1693547 1906933 := bbase (se 5 (by rfl) ⟨89387, by rfl⟩ : syracuseStep 1906933 = 178775) (by norm_num)
theorem B3619093 : Blo 1693547 3619093 := bbase (se 6 (by rfl) ⟨84822, by rfl⟩ : syracuseStep 3619093 = 169645) (by norm_num)
theorem B1906969 : Blo 1693547 1906969 := bbase (se 2 (by rfl) ⟨715113, by rfl⟩ : syracuseStep 1906969 = 1430227) (by norm_num)
theorem B4290853 : Blo 1693547 4290853 := bbase (se 4 (by rfl) ⟨402267, by rfl⟩ : syracuseStep 4290853 = 804535) (by norm_num)
theorem B5716277 : Blo 1693547 5716277 := bbase (se 5 (by rfl) ⟨267950, by rfl⟩ : syracuseStep 5716277 = 535901) (by norm_num)
theorem B1907005 : Blo 1693547 1907005 := bbase (se 3 (by rfl) ⟨357563, by rfl⟩ : syracuseStep 1907005 = 715127) (by norm_num)
theorem B2611525 : Blo 1693547 2611525 := bbase (se 4 (by rfl) ⟨244830, by rfl⟩ : syracuseStep 2611525 = 489661) (by norm_num)
theorem B1907041 : Blo 1693547 1907041 := bbase (se 2 (by rfl) ⟨715140, by rfl⟩ : syracuseStep 1907041 = 1430281) (by norm_num)
theorem B1907077 : Blo 1693547 1907077 := bbase (se 4 (by rfl) ⟨178788, by rfl⟩ : syracuseStep 1907077 = 357577) (by norm_num)
theorem B2144657 : Blo 1693547 2144657 := bbase (se 2 (by rfl) ⟨804246, by rfl⟩ : syracuseStep 2144657 = 1608493) (by norm_num)
theorem B4290965 : Blo 1693547 4290965 := bbase (se 6 (by rfl) ⟨100569, by rfl⟩ : syracuseStep 4290965 = 201139) (by norm_num)
theorem B1907113 : Blo 1693547 1907113 := bbase (se 2 (by rfl) ⟨715167, by rfl⟩ : syracuseStep 1907113 = 1430335) (by norm_num)
theorem B2144713 : Blo 1693547 2144713 := bbase (se 2 (by rfl) ⟨804267, by rfl⟩ : syracuseStep 2144713 = 1608535) (by norm_num)
theorem B1907149 : Blo 1693547 1907149 := bbase (se 3 (by rfl) ⟨357590, by rfl⟩ : syracuseStep 1907149 = 715181) (by norm_num)
theorem B4823509 : Blo 1693547 4823509 := bbase (se 7 (by rfl) ⟨56525, by rfl⟩ : syracuseStep 4823509 = 113051) (by norm_num)
theorem B1907185 : Blo 1693547 1907185 := bbase (se 2 (by rfl) ⟨715194, by rfl⟩ : syracuseStep 1907185 = 1430389) (by norm_num)
theorem B1808897 : Blo 1693547 1808897 := bbase (se 2 (by rfl) ⟨678336, by rfl⟩ : syracuseStep 1808897 = 1356673) (by norm_num)
theorem B1907221 : Blo 1693547 1907221 := bbase (se 6 (by rfl) ⟨44700, by rfl⟩ : syracuseStep 1907221 = 89401) (by norm_num)
theorem B2144809 : Blo 1693547 2144809 := bbase (se 2 (by rfl) ⟨804303, by rfl⟩ : syracuseStep 2144809 = 1608607) (by norm_num)
theorem B1907257 : Blo 1693547 1907257 := bbase (se 2 (by rfl) ⟨715221, by rfl⟩ : syracuseStep 1907257 = 1430443) (by norm_num)
theorem B3217981 : Blo 1693547 3217981 := bbase (se 3 (by rfl) ⟨603371, by rfl⟩ : syracuseStep 3217981 = 1206743) (by norm_num)
theorem B4291157 : Blo 1693547 4291157 := bbase (se 8 (by rfl) ⟨25143, by rfl⟩ : syracuseStep 4291157 = 50287) (by norm_num)
theorem B1907293 : Blo 1693547 1907293 := bbase (se 3 (by rfl) ⟨357617, by rfl⟩ : syracuseStep 1907293 = 715235) (by norm_num)
theorem B1907329 : Blo 1693547 1907329 := bbase (se 2 (by rfl) ⟨715248, by rfl⟩ : syracuseStep 1907329 = 1430497) (by norm_num)
theorem B3054229 : Blo 1693547 3054229 := bbase (se 6 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 3054229 = 143167) (by norm_num)
theorem B1907365 : Blo 1693547 1907365 := bbase (se 4 (by rfl) ⟨178815, by rfl⟩ : syracuseStep 1907365 = 357631) (by norm_num)
theorem B7240373 : Blo 1693547 7240373 := bbase (se 5 (by rfl) ⟨339392, by rfl⟩ : syracuseStep 7240373 = 678785) (by norm_num)
theorem B6273733 : Blo 1693547 6273733 := bbase (se 4 (by rfl) ⟨588162, by rfl⟩ : syracuseStep 6273733 = 1176325) (by norm_num)
theorem B1907401 : Blo 1693547 1907401 := bbase (se 2 (by rfl) ⟨715275, by rfl⟩ : syracuseStep 1907401 = 1430551) (by norm_num)
theorem B3218125 : Blo 1693547 3218125 := bbase (se 3 (by rfl) ⟨603398, by rfl⟩ : syracuseStep 3218125 = 1206797) (by norm_num)
theorem B2144981 : Blo 1693547 2144981 := bbase (se 7 (by rfl) ⟨25136, by rfl⟩ : syracuseStep 2144981 = 50273) (by norm_num)
theorem B5716709 : Blo 1693547 5716709 := bbase (se 4 (by rfl) ⟨535941, by rfl⟩ : syracuseStep 5716709 = 1071883) (by norm_num)
theorem B1907437 : Blo 1693547 1907437 := bbase (se 3 (by rfl) ⟨357644, by rfl⟩ : syracuseStep 1907437 = 715289) (by norm_num)
theorem B1809145 : Blo 1693547 1809145 := bbase (se 2 (by rfl) ⟨678429, by rfl⟩ : syracuseStep 1809145 = 1356859) (by norm_num)
theorem B2145037 : Blo 1693547 2145037 := bbase (se 3 (by rfl) ⟨402194, by rfl⟩ : syracuseStep 2145037 = 804389) (by norm_num)
theorem B1907473 : Blo 1693547 1907473 := bbase (se 2 (by rfl) ⟨715302, by rfl⟩ : syracuseStep 1907473 = 1430605) (by norm_num)
theorem B5151509 : Blo 1693547 5151509 := bbase (se 6 (by rfl) ⟨120738, by rfl⟩ : syracuseStep 5151509 = 241477) (by norm_num)
theorem B5430037 : Blo 1693547 5430037 := bbase (se 6 (by rfl) ⟨127266, by rfl⟩ : syracuseStep 5430037 = 254533) (by norm_num)
theorem B2145133 : Blo 1693547 2145133 := bbase (se 3 (by rfl) ⟨402212, by rfl⟩ : syracuseStep 2145133 = 804425) (by norm_num)
theorem B3218285 : Blo 1693547 3218285 := bbase (se 3 (by rfl) ⟨603428, by rfl⟩ : syracuseStep 3218285 = 1206857) (by norm_num)
theorem B4291501 : Blo 1693547 4291501 := bbase (se 3 (by rfl) ⟨804656, by rfl⟩ : syracuseStep 4291501 = 1609313) (by norm_num)
theorem B2857909 : Blo 1693547 2857909 := bbase (se 5 (by rfl) ⟨133964, by rfl⟩ : syracuseStep 2857909 = 267929) (by norm_num)
theorem B3218429 : Blo 1693547 3218429 := bbase (se 3 (by rfl) ⟨603455, by rfl⟩ : syracuseStep 3218429 = 1206911) (by norm_num)
theorem B2857997 : Blo 1693547 2857997 := bbase (se 3 (by rfl) ⟨535874, by rfl⟩ : syracuseStep 2857997 = 1071749) (by norm_num)
theorem B2145305 : Blo 1693547 2145305 := bbase (se 2 (by rfl) ⟨804489, by rfl⟩ : syracuseStep 2145305 = 1608979) (by norm_num)
theorem B1932317 : Blo 1693547 1932317 := bbase (se 3 (by rfl) ⟨362309, by rfl⟩ : syracuseStep 1932317 = 724619) (by norm_num)
theorem B4291613 : Blo 1693547 4291613 := bbase (se 3 (by rfl) ⟨804677, by rfl⟩ : syracuseStep 4291613 = 1609355) (by norm_num)
theorem B9649205 : Blo 1693547 9649205 := bbase (se 5 (by rfl) ⟨452306, by rfl⟩ : syracuseStep 9649205 = 904613) (by norm_num)
theorem B2145361 : Blo 1693547 2145361 := bbase (se 2 (by rfl) ⟨804510, by rfl⟩ : syracuseStep 2145361 = 1609021) (by norm_num)
theorem B2899037 : Blo 1693547 2899037 := bbase (se 3 (by rfl) ⟨543569, by rfl⟩ : syracuseStep 2899037 = 1087139) (by norm_num)
theorem B3054685 : Blo 1693547 3054685 := bbase (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) (by norm_num)
theorem B8576117 : Blo 1693547 8576117 := bbase (se 5 (by rfl) ⟨402005, by rfl⟩ : syracuseStep 8576117 = 804011) (by norm_num)
theorem B4127861 : Blo 1693547 4127861 := bbase (se 5 (by rfl) ⟨193493, by rfl⟩ : syracuseStep 4127861 = 386987) (by norm_num)
theorem B2858125 : Blo 1693547 2858125 := bbase (se 3 (by rfl) ⟨535898, by rfl⟩ : syracuseStep 2858125 = 1071797) (by norm_num)
theorem B3619981 : Blo 1693547 3619981 := bbase (se 3 (by rfl) ⟨678746, by rfl⟩ : syracuseStep 3619981 = 1357493) (by norm_num)
theorem B5717141 : Blo 1693547 5717141 := bbase (se 6 (by rfl) ⟨133995, by rfl⟩ : syracuseStep 5717141 = 267991) (by norm_num)
theorem B2145457 : Blo 1693547 2145457 := bbase (se 2 (by rfl) ⟨804546, by rfl⟩ : syracuseStep 2145457 = 1609093) (by norm_num)
theorem B1809589 : Blo 1693547 1809589 := bbase (se 5 (by rfl) ⟨84824, by rfl⟩ : syracuseStep 1809589 = 169649) (by norm_num)
theorem B4291805 : Blo 1693547 4291805 := bbase (se 3 (by rfl) ⟨804713, by rfl⟩ : syracuseStep 4291805 = 1609427) (by norm_num)
theorem B2858213 : Blo 1693547 2858213 := bbase (se 4 (by rfl) ⟨267957, by rfl⟩ : syracuseStep 2858213 = 535915) (by norm_num)
theorem B1809649 : Blo 1693547 1809649 := bbase (se 2 (by rfl) ⟨678618, by rfl⟩ : syracuseStep 1809649 = 1357237) (by norm_num)
theorem B3218717 : Blo 1693547 3218717 := bbase (se 3 (by rfl) ⟨603509, by rfl⟩ : syracuseStep 3218717 = 1207019) (by norm_num)
theorem B8142133 : Blo 1693547 8142133 := bbase (se 5 (by rfl) ⟨381662, by rfl⟩ : syracuseStep 8142133 = 763325) (by norm_num)
theorem B2145629 : Blo 1693547 2145629 := bbase (se 3 (by rfl) ⟨402305, by rfl⟩ : syracuseStep 2145629 = 804611) (by norm_num)
theorem B2858341 : Blo 1693547 2858341 := bbase (se 4 (by rfl) ⟨267969, by rfl⟩ : syracuseStep 2858341 = 535939) (by norm_num)
theorem B2145685 : Blo 1693547 2145685 := bbase (se 6 (by rfl) ⟨50289, by rfl⟩ : syracuseStep 2145685 = 100579) (by norm_num)
theorem B3218869 : Blo 1693547 3218869 := bbase (se 5 (by rfl) ⟨150884, by rfl⟩ : syracuseStep 3218869 = 301769) (by norm_num)
theorem B2858429 : Blo 1693547 2858429 := bbase (se 3 (by rfl) ⟨535955, by rfl⟩ : syracuseStep 2858429 = 1071911) (by norm_num)
theorem B3259877 : Blo 1693547 3259877 := bbase (se 4 (by rfl) ⟨305613, by rfl⟩ : syracuseStep 3259877 = 611227) (by norm_num)
theorem B2145781 : Blo 1693547 2145781 := bbase (se 5 (by rfl) ⟨100583, by rfl⟩ : syracuseStep 2145781 = 201167) (by norm_num)
theorem B4824613 : Blo 1693547 4824613 := bbase (se 4 (by rfl) ⟨452307, by rfl⟩ : syracuseStep 4824613 = 904615) (by norm_num)
theorem B1809965 : Blo 1693547 1809965 := bbase (se 3 (by rfl) ⟨339368, by rfl⟩ : syracuseStep 1809965 = 678737) (by norm_num)
theorem B2858557 : Blo 1693547 2858557 := bbase (se 3 (by rfl) ⟨535979, by rfl⟩ : syracuseStep 2858557 = 1071959) (by norm_num)
theorem B5717573 : Blo 1693547 5717573 := bbase (se 4 (by rfl) ⟨536022, by rfl⟩ : syracuseStep 5717573 = 1072045) (by norm_num)
theorem B1834573 : Blo 1693547 1834573 := bbase (se 3 (by rfl) ⟨343982, by rfl⟩ : syracuseStep 1834573 = 687965) (by norm_num)
theorem B3620477 : Blo 1693547 3620477 := bbase (se 3 (by rfl) ⟨678839, by rfl⟩ : syracuseStep 3620477 = 1357679) (by norm_num)
theorem B2858645 : Blo 1693547 2858645 := bbase (se 6 (by rfl) ⟨66999, by rfl⟩ : syracuseStep 2858645 = 133999) (by norm_num)
theorem B6430373 : Blo 1693547 6430373 := bbase (se 4 (by rfl) ⟨602847, by rfl⟩ : syracuseStep 6430373 = 1205695) (by norm_num)
theorem B14474933 : Blo 1693547 14474933 := bbase (se 5 (by rfl) ⟨678512, by rfl⟩ : syracuseStep 14474933 = 1357025) (by norm_num)
theorem B2858773 : Blo 1693547 2858773 := bbase (se 6 (by rfl) ⟨67002, by rfl⟩ : syracuseStep 2858773 = 134005) (by norm_num)
theorem B2858861 : Blo 1693547 2858861 := bbase (se 3 (by rfl) ⟨536036, by rfl⟩ : syracuseStep 2858861 = 1072073) (by norm_num)
theorem B10305397 : Blo 1693547 10305397 := bbase (se 5 (by rfl) ⟨483065, by rfl⟩ : syracuseStep 10305397 = 966131) (by norm_num)
theorem B1933193 : Blo 1693547 1933193 := bbase (se 2 (by rfl) ⟨724947, by rfl⟩ : syracuseStep 1933193 = 1449895) (by norm_num)
theorem B3915661 : Blo 1693547 3915661 := bbase (se 3 (by rfl) ⟨734186, by rfl⟩ : syracuseStep 3915661 = 1468373) (by norm_num)
theorem B6430661 : Blo 1693547 6430661 := bbase (se 4 (by rfl) ⟨602874, by rfl⟩ : syracuseStep 6430661 = 1205749) (by norm_num)
theorem B1810409 : Blo 1693547 1810409 := bbase (se 2 (by rfl) ⟨678903, by rfl⟩ : syracuseStep 1810409 = 1357807) (by norm_num)
theorem B2858989 : Blo 1693547 2858989 := bbase (se 3 (by rfl) ⟨536060, by rfl⟩ : syracuseStep 2858989 = 1072121) (by norm_num)
theorem B5718005 : Blo 1693547 5718005 := bbase (se 5 (by rfl) ⟨268031, by rfl⟩ : syracuseStep 5718005 = 536063) (by norm_num)
theorem B2859043 : Blo 1693547 2859043 := bstep (se 1 (by rfl) ⟨2144282, by rfl⟩ : syracuseStep 2859043 = 4288565) B4288565
theorem B5505059 : Blo 1693547 5505059 := bstep (se 1 (by rfl) ⟨4128794, by rfl⟩ : syracuseStep 5505059 = 8257589) B8257589
theorem B2859185 : Blo 1693547 2859185 := bstep (se 2 (by rfl) ⟨1072194, by rfl⟩ : syracuseStep 2859185 = 2144389) B2144389
theorem B5718221 : Blo 1693547 5718221 := bstep (se 3 (by rfl) ⟨1072166, by rfl⟩ : syracuseStep 5718221 = 2144333) B2144333
theorem B4890833 : Blo 1693547 4890833 := bstep (se 2 (by rfl) ⟨1834062, by rfl⟩ : syracuseStep 4890833 = 3668125) B3668125
theorem B8577251 : Blo 1693547 8577251 := bstep (se 1 (by rfl) ⟨6432938, by rfl⟩ : syracuseStep 8577251 = 12865877) B12865877
theorem B5718275 : Blo 1693547 5718275 := bstep (se 1 (by rfl) ⟨4288706, by rfl⟩ : syracuseStep 5718275 = 8577413) B8577413
theorem B2859313 : Blo 1693547 2859313 := bstep (se 2 (by rfl) ⟨1072242, by rfl⟩ : syracuseStep 2859313 = 2144485) B2144485
theorem B4350257 : Blo 1693547 4350257 := bstep (se 2 (by rfl) ⟨1631346, by rfl⟩ : syracuseStep 4350257 = 3262693) B3262693
theorem B20611381 : Blo 1693547 20611381 := bstep (se 5 (by rfl) ⟨966158, by rfl⟩ : syracuseStep 20611381 = 1932317) B1932317
theorem B35742005 : Blo 1693547 35742005 := bstep (se 5 (by rfl) ⟨1675406, by rfl⟩ : syracuseStep 35742005 = 3350813) B3350813
theorem B4890947 : Blo 1693547 4890947 := bstep (se 1 (by rfl) ⟨3668210, by rfl⟩ : syracuseStep 4890947 = 7336421) B7336421
theorem B2859347 : Blo 1693547 2859347 := bstep (se 1 (by rfl) ⟨2144510, by rfl⟩ : syracuseStep 2859347 = 4289021) B4289021
theorem B4825457 : Blo 1693547 4825457 := bstep (se 2 (by rfl) ⟨1809546, by rfl⟩ : syracuseStep 4825457 = 3619093) B3619093
theorem B32579981 : Blo 1693547 32579981 := bstep (se 3 (by rfl) ⟨6108746, by rfl⟩ : syracuseStep 32579981 = 12217493) B12217493
theorem B3482033 : Blo 1693547 3482033 := bstep (se 2 (by rfl) ⟨1305762, by rfl⟩ : syracuseStep 3482033 = 2611525) B2611525
theorem B18317765 : Blo 1693547 18317765 := bstep (se 4 (by rfl) ⟨1717290, by rfl⟩ : syracuseStep 18317765 = 3434581) B3434581
theorem B2859475 : Blo 1693547 2859475 := bstep (se 1 (by rfl) ⟨2144606, by rfl⟩ : syracuseStep 2859475 = 4289213) B4289213
theorem B4579811 : Blo 1693547 4579811 := bstep (se 1 (by rfl) ⟨3434858, by rfl⟩ : syracuseStep 4579811 = 6869717) B6869717
theorem B5718545 : Blo 1693547 5718545 := bstep (se 2 (by rfl) ⟨2144454, by rfl⟩ : syracuseStep 5718545 = 4288909) B4288909
theorem B2859617 : Blo 1693547 2859617 := bstep (se 2 (by rfl) ⟨1072356, by rfl⟩ : syracuseStep 2859617 = 2144713) B2144713
theorem B6431345 : Blo 1693547 6431345 := bstep (se 2 (by rfl) ⟨2411754, by rfl⟩ : syracuseStep 6431345 = 4823509) B4823509
theorem B2859745 : Blo 1693547 2859745 := bstep (se 2 (by rfl) ⟨1072404, by rfl⟩ : syracuseStep 2859745 = 2144809) B2144809
theorem B2859779 : Blo 1693547 2859779 := bstep (se 1 (by rfl) ⟨2144834, by rfl⟩ : syracuseStep 2859779 = 4289669) B4289669
theorem B2540321 : Blo 1693547 2540321 := bstep (se 2 (by rfl) ⟨952620, by rfl⟩ : syracuseStep 2540321 = 1905241) B1905241
theorem B2540339 : Blo 1693547 2540339 := bstep (se 1 (by rfl) ⟨1905254, by rfl⟩ : syracuseStep 2540339 = 3810509) B3810509
theorem B21168965 : Blo 1693547 21168965 := bstep (se 4 (by rfl) ⟨1984590, by rfl⟩ : syracuseStep 21168965 = 3969181) B3969181
theorem B2540369 : Blo 1693547 2540369 := bstep (se 2 (by rfl) ⟨952638, by rfl⟩ : syracuseStep 2540369 = 1905277) B1905277
theorem B2540387 : Blo 1693547 2540387 := bstep (se 1 (by rfl) ⟨1905290, by rfl⟩ : syracuseStep 2540387 = 3810581) B3810581
theorem B2540417 : Blo 1693547 2540417 := bstep (se 2 (by rfl) ⟨952656, by rfl⟩ : syracuseStep 2540417 = 1905313) B1905313
theorem B2859907 : Blo 1693547 2859907 := bstep (se 1 (by rfl) ⟨2144930, by rfl⟩ : syracuseStep 2859907 = 4289861) B4289861
theorem B14484365 : Blo 1693547 14484365 := bstep (se 3 (by rfl) ⟨2715818, by rfl⟩ : syracuseStep 14484365 = 5431637) B5431637
theorem B2540435 : Blo 1693547 2540435 := bstep (se 1 (by rfl) ⟨1905326, by rfl⟩ : syracuseStep 2540435 = 3810653) B3810653
theorem B2540465 : Blo 1693547 2540465 := bstep (se 2 (by rfl) ⟨952674, by rfl⟩ : syracuseStep 2540465 = 1905349) B1905349
theorem B8364977 : Blo 1693547 8364977 := bstep (se 2 (by rfl) ⟨3136866, by rfl⟩ : syracuseStep 8364977 = 6273733) B6273733
theorem B2540483 : Blo 1693547 2540483 := bstep (se 1 (by rfl) ⟨1905362, by rfl⟩ : syracuseStep 2540483 = 3810725) B3810725
theorem B2540513 : Blo 1693547 2540513 := bstep (se 2 (by rfl) ⟨952692, by rfl⟩ : syracuseStep 2540513 = 1905385) B1905385
theorem B2540531 : Blo 1693547 2540531 := bstep (se 1 (by rfl) ⟨1905398, by rfl⟩ : syracuseStep 2540531 = 3810797) B3810797
theorem B8578061 : Blo 1693547 8578061 := bstep (se 3 (by rfl) ⟨1608386, by rfl⟩ : syracuseStep 8578061 = 3216773) B3216773
theorem B2540561 : Blo 1693547 2540561 := bstep (se 2 (by rfl) ⟨952710, by rfl⟩ : syracuseStep 2540561 = 1905421) B1905421
theorem B2860049 : Blo 1693547 2860049 := bstep (se 2 (by rfl) ⟨1072518, by rfl⟩ : syracuseStep 2860049 = 2145037) B2145037
theorem B2540579 : Blo 1693547 2540579 := bstep (se 1 (by rfl) ⟨1905434, by rfl⟩ : syracuseStep 2540579 = 3810869) B3810869
theorem B9282595 : Blo 1693547 9282595 := bstep (se 1 (by rfl) ⟨6961946, by rfl⟩ : syracuseStep 9282595 = 13923893) B13923893
theorem B5719085 : Blo 1693547 5719085 := bstep (se 3 (by rfl) ⟨1072328, by rfl⟩ : syracuseStep 5719085 = 2144657) B2144657
theorem B2540609 : Blo 1693547 2540609 := bstep (se 2 (by rfl) ⟨952728, by rfl⟩ : syracuseStep 2540609 = 1905457) B1905457
theorem B2540627 : Blo 1693547 2540627 := bstep (se 1 (by rfl) ⟨1905470, by rfl⟩ : syracuseStep 2540627 = 3810941) B3810941
theorem B5719139 : Blo 1693547 5719139 := bstep (se 1 (by rfl) ⟨4289354, by rfl⟩ : syracuseStep 5719139 = 8578709) B8578709
theorem B2540657 : Blo 1693547 2540657 := bstep (se 2 (by rfl) ⟨952746, by rfl⟩ : syracuseStep 2540657 = 1905493) B1905493
theorem B2540675 : Blo 1693547 2540675 := bstep (se 1 (by rfl) ⟨1905506, by rfl⟩ : syracuseStep 2540675 = 3811013) B3811013
theorem B4826243 : Blo 1693547 4826243 := bstep (se 1 (by rfl) ⟨3619682, by rfl⟩ : syracuseStep 4826243 = 7239365) B7239365
theorem B2860177 : Blo 1693547 2860177 := bstep (se 2 (by rfl) ⟨1072566, by rfl⟩ : syracuseStep 2860177 = 2145133) B2145133
theorem B2540705 : Blo 1693547 2540705 := bstep (se 2 (by rfl) ⟨952764, by rfl⟩ : syracuseStep 2540705 = 1905529) B1905529
theorem B2540723 : Blo 1693547 2540723 := bstep (se 1 (by rfl) ⟨1905542, by rfl⟩ : syracuseStep 2540723 = 3811085) B3811085
theorem B2860211 : Blo 1693547 2860211 := bstep (se 1 (by rfl) ⟨2145158, by rfl⟩ : syracuseStep 2860211 = 4290317) B4290317
theorem B18580661 : Blo 1693547 18580661 := bstep (se 5 (by rfl) ⟨870968, by rfl⟩ : syracuseStep 18580661 = 1741937) B1741937
theorem B2540753 : Blo 1693547 2540753 := bstep (se 2 (by rfl) ⟨952782, by rfl⟩ : syracuseStep 2540753 = 1905565) B1905565
theorem B2540771 : Blo 1693547 2540771 := bstep (se 1 (by rfl) ⟨1905578, by rfl⟩ : syracuseStep 2540771 = 3811157) B3811157
theorem B3810545 : Blo 1693547 3810545 := bstep (se 2 (by rfl) ⟨1428954, by rfl⟩ : syracuseStep 3810545 = 2857909) B2857909
theorem B2540801 : Blo 1693547 2540801 := bstep (se 2 (by rfl) ⟨952800, by rfl⟩ : syracuseStep 2540801 = 1905601) B1905601
theorem B3810563 : Blo 1693547 3810563 := bstep (se 1 (by rfl) ⟨2857922, by rfl⟩ : syracuseStep 3810563 = 5715845) B5715845
theorem B8693005 : Blo 1693547 8693005 := bstep (se 3 (by rfl) ⟨1629938, by rfl⟩ : syracuseStep 8693005 = 3259877) B3259877
theorem B2540819 : Blo 1693547 2540819 := bstep (se 1 (by rfl) ⟨1905614, by rfl⟩ : syracuseStep 2540819 = 3811229) B3811229
theorem B2540849 : Blo 1693547 2540849 := bstep (se 2 (by rfl) ⟨952818, by rfl⟩ : syracuseStep 2540849 = 1905637) B1905637
theorem B2860339 : Blo 1693547 2860339 := bstep (se 1 (by rfl) ⟨2145254, by rfl⟩ : syracuseStep 2860339 = 4290509) B4290509
theorem B3433795 : Blo 1693547 3433795 := bstep (se 1 (by rfl) ⟨2575346, by rfl⟩ : syracuseStep 3433795 = 5150693) B5150693
theorem B2540867 : Blo 1693547 2540867 := bstep (se 1 (by rfl) ⟨1905650, by rfl⟩ : syracuseStep 2540867 = 3811301) B3811301
theorem B2540897 : Blo 1693547 2540897 := bstep (se 2 (by rfl) ⟨952836, by rfl⟩ : syracuseStep 2540897 = 1905673) B1905673
theorem B14476643 : Blo 1693547 14476643 := bstep (se 1 (by rfl) ⟨10857482, by rfl⟩ : syracuseStep 14476643 = 21714965) B21714965
theorem B5719409 : Blo 1693547 5719409 := bstep (se 2 (by rfl) ⟨2144778, by rfl⟩ : syracuseStep 5719409 = 4289557) B4289557
theorem B2540915 : Blo 1693547 2540915 := bstep (se 1 (by rfl) ⟨1905686, by rfl⟩ : syracuseStep 2540915 = 3811373) B3811373
theorem B2540945 : Blo 1693547 2540945 := bstep (se 2 (by rfl) ⟨952854, by rfl⟩ : syracuseStep 2540945 = 1905709) B1905709
theorem B2540963 : Blo 1693547 2540963 := bstep (se 1 (by rfl) ⟨1905722, by rfl⟩ : syracuseStep 2540963 = 3811445) B3811445
theorem B2713025 : Blo 1693547 2713025 := bstep (se 2 (by rfl) ⟨1017384, by rfl⟩ : syracuseStep 2713025 = 2034769) B2034769
theorem B2540993 : Blo 1693547 2540993 := bstep (se 2 (by rfl) ⟨952872, by rfl⟩ : syracuseStep 2540993 = 1905745) B1905745
theorem B2860481 : Blo 1693547 2860481 := bstep (se 2 (by rfl) ⟨1072680, by rfl⟩ : syracuseStep 2860481 = 2145361) B2145361
theorem B4826573 : Blo 1693547 4826573 := bstep (se 3 (by rfl) ⟨904982, by rfl⟩ : syracuseStep 4826573 = 1809965) B1809965
theorem B4072913 : Blo 1693547 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B2541011 : Blo 1693547 2541011 := bstep (se 1 (by rfl) ⟨1905758, by rfl⟩ : syracuseStep 2541011 = 3811517) B3811517
theorem B12862961 : Blo 1693547 12862961 := bstep (se 2 (by rfl) ⟨4823610, by rfl⟩ : syracuseStep 12862961 = 9647221) B9647221
theorem B2541041 : Blo 1693547 2541041 := bstep (se 2 (by rfl) ⟨952890, by rfl⟩ : syracuseStep 2541041 = 1905781) B1905781
theorem B2541059 : Blo 1693547 2541059 := bstep (se 1 (by rfl) ⟨1905794, by rfl⟩ : syracuseStep 2541059 = 3811589) B3811589
theorem B3810833 : Blo 1693547 3810833 := bstep (se 2 (by rfl) ⟨1429062, by rfl⟩ : syracuseStep 3810833 = 2858125) B2858125
theorem B4826641 : Blo 1693547 4826641 := bstep (se 2 (by rfl) ⟨1809990, by rfl⟩ : syracuseStep 4826641 = 3619981) B3619981
theorem B2541089 : Blo 1693547 2541089 := bstep (se 2 (by rfl) ⟨952908, by rfl⟩ : syracuseStep 2541089 = 1905817) B1905817
theorem B3810851 : Blo 1693547 3810851 := bstep (se 1 (by rfl) ⟨2858138, by rfl⟩ : syracuseStep 3810851 = 5716277) B5716277
theorem B4589101 : Blo 1693547 4589101 := bstep (se 3 (by rfl) ⟨860456, by rfl⟩ : syracuseStep 4589101 = 1720913) B1720913
theorem B2541107 : Blo 1693547 2541107 := bstep (se 1 (by rfl) ⟨1905830, by rfl⟩ : syracuseStep 2541107 = 3811661) B3811661
theorem B2860609 : Blo 1693547 2860609 := bstep (se 2 (by rfl) ⟨1072728, by rfl⟩ : syracuseStep 2860609 = 2145457) B2145457
theorem B2541137 : Blo 1693547 2541137 := bstep (se 2 (by rfl) ⟨952926, by rfl⟩ : syracuseStep 2541137 = 1905853) B1905853
theorem B2541155 : Blo 1693547 2541155 := bstep (se 1 (by rfl) ⟨1905866, by rfl⟩ : syracuseStep 2541155 = 3811733) B3811733
theorem B2860643 : Blo 1693547 2860643 := bstep (se 1 (by rfl) ⟨2145482, by rfl⟩ : syracuseStep 2860643 = 4290965) B4290965
theorem B2541185 : Blo 1693547 2541185 := bstep (se 2 (by rfl) ⟨952944, by rfl⟩ : syracuseStep 2541185 = 1905889) B1905889
theorem B2541203 : Blo 1693547 2541203 := bstep (se 1 (by rfl) ⟨1905902, by rfl⟩ : syracuseStep 2541203 = 3811805) B3811805
theorem B2541233 : Blo 1693547 2541233 := bstep (se 2 (by rfl) ⟨952962, by rfl⟩ : syracuseStep 2541233 = 1905925) B1905925
theorem B10307249 : Blo 1693547 10307249 := bstep (se 2 (by rfl) ⟨3865218, by rfl⟩ : syracuseStep 10307249 = 7730437) B7730437
theorem B2541251 : Blo 1693547 2541251 := bstep (se 1 (by rfl) ⟨1905938, by rfl⟩ : syracuseStep 2541251 = 3811877) B3811877
theorem B2541281 : Blo 1693547 2541281 := bstep (se 2 (by rfl) ⟨952980, by rfl⟩ : syracuseStep 2541281 = 1905961) B1905961
theorem B2860771 : Blo 1693547 2860771 := bstep (se 1 (by rfl) ⟨2145578, by rfl⟩ : syracuseStep 2860771 = 4291157) B4291157
theorem B10856177 : Blo 1693547 10856177 := bstep (se 2 (by rfl) ⟨4071066, by rfl⟩ : syracuseStep 10856177 = 8142133) B8142133
theorem B2541299 : Blo 1693547 2541299 := bstep (se 1 (by rfl) ⟨1905974, by rfl⟩ : syracuseStep 2541299 = 3811949) B3811949
theorem B2541329 : Blo 1693547 2541329 := bstep (se 2 (by rfl) ⟨952998, by rfl⟩ : syracuseStep 2541329 = 1905997) B1905997
theorem B2541347 : Blo 1693547 2541347 := bstep (se 1 (by rfl) ⟨1906010, by rfl⟩ : syracuseStep 2541347 = 3812021) B3812021
theorem B4826915 : Blo 1693547 4826915 := bstep (se 1 (by rfl) ⟨3620186, by rfl⟩ : syracuseStep 4826915 = 7240373) B7240373
theorem B5580589 : Blo 1693547 5580589 := bstep (se 3 (by rfl) ⟨1046360, by rfl⟩ : syracuseStep 5580589 = 2092721) B2092721
theorem B3811121 : Blo 1693547 3811121 := bstep (se 2 (by rfl) ⟨1429170, by rfl⟩ : syracuseStep 3811121 = 2858341) B2858341
theorem B2541377 : Blo 1693547 2541377 := bstep (se 2 (by rfl) ⟨953016, by rfl⟩ : syracuseStep 2541377 = 1906033) B1906033
theorem B3811139 : Blo 1693547 3811139 := bstep (se 1 (by rfl) ⟨2858354, by rfl⟩ : syracuseStep 3811139 = 5716709) B5716709
theorem B2541395 : Blo 1693547 2541395 := bstep (se 1 (by rfl) ⟨1906046, by rfl⟩ : syracuseStep 2541395 = 3812093) B3812093
theorem B3434339 : Blo 1693547 3434339 := bstep (se 1 (by rfl) ⟨2575754, by rfl⟩ : syracuseStep 3434339 = 5151509) B5151509
theorem B2541425 : Blo 1693547 2541425 := bstep (se 2 (by rfl) ⟨953034, by rfl⟩ : syracuseStep 2541425 = 1906069) B1906069
theorem B2860913 : Blo 1693547 2860913 := bstep (se 2 (by rfl) ⟨1072842, by rfl⟩ : syracuseStep 2860913 = 2145685) B2145685
theorem B2541443 : Blo 1693547 2541443 := bstep (se 1 (by rfl) ⟨1906082, by rfl⟩ : syracuseStep 2541443 = 3812165) B3812165
theorem B5719949 : Blo 1693547 5719949 := bstep (se 3 (by rfl) ⟨1072490, by rfl⟩ : syracuseStep 5719949 = 2144981) B2144981
theorem B2541473 : Blo 1693547 2541473 := bstep (se 2 (by rfl) ⟨953052, by rfl⟩ : syracuseStep 2541473 = 1906105) B1906105
theorem B2541491 : Blo 1693547 2541491 := bstep (se 1 (by rfl) ⟨1906118, by rfl⟩ : syracuseStep 2541491 = 3812237) B3812237
theorem B5720003 : Blo 1693547 5720003 := bstep (se 1 (by rfl) ⟨4290002, by rfl⟩ : syracuseStep 5720003 = 8580005) B8580005
theorem B2541521 : Blo 1693547 2541521 := bstep (se 2 (by rfl) ⟨953070, by rfl⟩ : syracuseStep 2541521 = 1906141) B1906141
theorem B2541539 : Blo 1693547 2541539 := bstep (se 1 (by rfl) ⟨1906154, by rfl⟩ : syracuseStep 2541539 = 3812309) B3812309
theorem B2861041 : Blo 1693547 2861041 := bstep (se 2 (by rfl) ⟨1072890, by rfl⟩ : syracuseStep 2861041 = 2145781) B2145781
theorem B2541569 : Blo 1693547 2541569 := bstep (se 2 (by rfl) ⟨953088, by rfl⟩ : syracuseStep 2541569 = 1906177) B1906177
theorem B6866957 : Blo 1693547 6866957 := bstep (se 3 (by rfl) ⟨1287554, by rfl⟩ : syracuseStep 6866957 = 2575109) B2575109
theorem B2541587 : Blo 1693547 2541587 := bstep (se 1 (by rfl) ⟨1906190, by rfl⟩ : syracuseStep 2541587 = 3812381) B3812381
theorem B2861075 : Blo 1693547 2861075 := bstep (se 1 (by rfl) ⟨2145806, by rfl⟩ : syracuseStep 2861075 = 4291613) B4291613
theorem B6432803 : Blo 1693547 6432803 := bstep (se 1 (by rfl) ⟨4824602, by rfl⟩ : syracuseStep 6432803 = 9649205) B9649205
theorem B6432817 : Blo 1693547 6432817 := bstep (se 2 (by rfl) ⟨2412306, by rfl⟩ : syracuseStep 6432817 = 4824613) B4824613
theorem B2541617 : Blo 1693547 2541617 := bstep (se 2 (by rfl) ⟨953106, by rfl⟩ : syracuseStep 2541617 = 1906213) B1906213
theorem B2541635 : Blo 1693547 2541635 := bstep (se 1 (by rfl) ⟨1906226, by rfl⟩ : syracuseStep 2541635 = 3812453) B3812453
theorem B3811409 : Blo 1693547 3811409 := bstep (se 2 (by rfl) ⟨1429278, by rfl⟩ : syracuseStep 3811409 = 2858557) B2858557
theorem B2541665 : Blo 1693547 2541665 := bstep (se 2 (by rfl) ⟨953124, by rfl⟩ : syracuseStep 2541665 = 1906249) B1906249
theorem B3811427 : Blo 1693547 3811427 := bstep (se 1 (by rfl) ⟨2858570, by rfl⟩ : syracuseStep 3811427 = 5717141) B5717141
theorem B2541683 : Blo 1693547 2541683 := bstep (se 1 (by rfl) ⟨1906262, by rfl⟩ : syracuseStep 2541683 = 3812525) B3812525
theorem B2541713 : Blo 1693547 2541713 := bstep (se 2 (by rfl) ⟨953142, by rfl⟩ : syracuseStep 2541713 = 1906285) B1906285
theorem B2861203 : Blo 1693547 2861203 := bstep (se 1 (by rfl) ⟨2145902, by rfl⟩ : syracuseStep 2861203 = 4291805) B4291805
theorem B2541731 : Blo 1693547 2541731 := bstep (se 1 (by rfl) ⟨1906298, by rfl⟩ : syracuseStep 2541731 = 3812597) B3812597
theorem B2541761 : Blo 1693547 2541761 := bstep (se 2 (by rfl) ⟨953160, by rfl⟩ : syracuseStep 2541761 = 1906321) B1906321
theorem B5720273 : Blo 1693547 5720273 := bstep (se 2 (by rfl) ⟨2145102, by rfl⟩ : syracuseStep 5720273 = 4290205) B4290205
theorem B2541779 : Blo 1693547 2541779 := bstep (se 1 (by rfl) ⟨1906334, by rfl⟩ : syracuseStep 2541779 = 3812669) B3812669
theorem B2541809 : Blo 1693547 2541809 := bstep (se 2 (by rfl) ⟨953178, by rfl⟩ : syracuseStep 2541809 = 1906357) B1906357
theorem B2541827 : Blo 1693547 2541827 := bstep (se 1 (by rfl) ⟨1906370, by rfl⟩ : syracuseStep 2541827 = 3812741) B3812741
theorem B2541857 : Blo 1693547 2541857 := bstep (se 2 (by rfl) ⟨953196, by rfl⟩ : syracuseStep 2541857 = 1906393) B1906393
theorem B2541875 : Blo 1693547 2541875 := bstep (se 1 (by rfl) ⟨1906406, by rfl⟩ : syracuseStep 2541875 = 3812813) B3812813
theorem B2541905 : Blo 1693547 2541905 := bstep (se 2 (by rfl) ⟨953214, by rfl⟩ : syracuseStep 2541905 = 1906429) B1906429
theorem B2541923 : Blo 1693547 2541923 := bstep (se 1 (by rfl) ⟨1906442, by rfl⟩ : syracuseStep 2541923 = 3812885) B3812885
theorem B5155181 : Blo 1693547 5155181 := bstep (se 3 (by rfl) ⟨966596, by rfl⟩ : syracuseStep 5155181 = 1933193) B1933193
theorem B3811697 : Blo 1693547 3811697 := bstep (se 2 (by rfl) ⟨1429386, by rfl⟩ : syracuseStep 3811697 = 2858773) B2858773
theorem B3811715 : Blo 1693547 3811715 := bstep (se 1 (by rfl) ⟨2858786, by rfl⟩ : syracuseStep 3811715 = 5717573) B5717573
theorem B2541953 : Blo 1693547 2541953 := bstep (se 2 (by rfl) ⟨953232, by rfl⟩ : syracuseStep 2541953 = 1906465) B1906465
theorem B2541971 : Blo 1693547 2541971 := bstep (se 1 (by rfl) ⟨1906478, by rfl⟩ : syracuseStep 2541971 = 3812957) B3812957
theorem B2542001 : Blo 1693547 2542001 := bstep (se 2 (by rfl) ⟨953250, by rfl⟩ : syracuseStep 2542001 = 1906501) B1906501
theorem B4286915 : Blo 1693547 4286915 := bstep (se 1 (by rfl) ⟨3215186, by rfl⟩ : syracuseStep 4286915 = 6430373) B6430373
theorem B2542019 : Blo 1693547 2542019 := bstep (se 1 (by rfl) ⟨1906514, by rfl⟩ : syracuseStep 2542019 = 3813029) B3813029
theorem B2542049 : Blo 1693547 2542049 := bstep (se 2 (by rfl) ⟨953268, by rfl⟩ : syracuseStep 2542049 = 1906537) B1906537
theorem B13740529 : Blo 1693547 13740529 := bstep (se 2 (by rfl) ⟨5152698, by rfl⟩ : syracuseStep 13740529 = 10305397) B10305397
theorem B2542067 : Blo 1693547 2542067 := bstep (se 1 (by rfl) ⟨1906550, by rfl⟩ : syracuseStep 2542067 = 3813101) B3813101
theorem B5425667 : Blo 1693547 5425667 := bstep (se 1 (by rfl) ⟨4069250, by rfl⟩ : syracuseStep 5425667 = 8138501) B8138501
theorem B5220881 : Blo 1693547 5220881 := bstep (se 2 (by rfl) ⟨1957830, by rfl⟩ : syracuseStep 5220881 = 3915661) B3915661
theorem B2542097 : Blo 1693547 2542097 := bstep (se 2 (by rfl) ⟨953286, by rfl⟩ : syracuseStep 2542097 = 1906573) B1906573
theorem B2542115 : Blo 1693547 2542115 := bstep (se 1 (by rfl) ⟨1906586, by rfl⟩ : syracuseStep 2542115 = 3813173) B3813173
theorem B2542145 : Blo 1693547 2542145 := bstep (se 2 (by rfl) ⟨953304, by rfl⟩ : syracuseStep 2542145 = 1906609) B1906609
theorem B2542163 : Blo 1693547 2542163 := bstep (se 1 (by rfl) ⟨1906622, by rfl⟩ : syracuseStep 2542163 = 3813245) B3813245
theorem B4827757 : Blo 1693547 4827757 := bstep (se 3 (by rfl) ⟨905204, by rfl⟩ : syracuseStep 4827757 = 1810409) B1810409
theorem B2542193 : Blo 1693547 2542193 := bstep (se 2 (by rfl) ⟨953322, by rfl⟩ : syracuseStep 2542193 = 1906645) B1906645
theorem B4287107 : Blo 1693547 4287107 := bstep (se 1 (by rfl) ⟨3215330, by rfl⟩ : syracuseStep 4287107 = 6430661) B6430661
theorem B2542211 : Blo 1693547 2542211 := bstep (se 1 (by rfl) ⟨1906658, by rfl⟩ : syracuseStep 2542211 = 3813317) B3813317
theorem B3811985 : Blo 1693547 3811985 := bstep (se 2 (by rfl) ⟨1429494, by rfl⟩ : syracuseStep 3811985 = 2858989) B2858989
theorem B2542241 : Blo 1693547 2542241 := bstep (se 2 (by rfl) ⟨953340, by rfl⟩ : syracuseStep 2542241 = 1906681) B1906681
theorem B3812003 : Blo 1693547 3812003 := bstep (se 1 (by rfl) ⟨2859002, by rfl⟩ : syracuseStep 3812003 = 5718005) B5718005
theorem B2542259 : Blo 1693547 2542259 := bstep (se 1 (by rfl) ⟨1906694, by rfl⟩ : syracuseStep 2542259 = 3813389) B3813389
theorem B2542289 : Blo 1693547 2542289 := bstep (se 2 (by rfl) ⟨953358, by rfl⟩ : syracuseStep 2542289 = 1906717) B1906717
theorem B31763171 : Blo 1693547 31763171 := bstep (se 1 (by rfl) ⟨23822378, by rfl⟩ : syracuseStep 31763171 = 47644757) B47644757
theorem B2542307 : Blo 1693547 2542307 := bstep (se 1 (by rfl) ⟨1906730, by rfl⟩ : syracuseStep 2542307 = 3813461) B3813461
theorem B5720813 : Blo 1693547 5720813 := bstep (se 3 (by rfl) ⟨1072652, by rfl⟩ : syracuseStep 5720813 = 2145305) B2145305
theorem B2542337 : Blo 1693547 2542337 := bstep (se 2 (by rfl) ⟨953376, by rfl⟩ : syracuseStep 2542337 = 1906753) B1906753
theorem B9161477 : Blo 1693547 9161477 := bstep (se 4 (by rfl) ⟨858888, by rfl⟩ : syracuseStep 9161477 = 1717777) B1717777
theorem B4827917 : Blo 1693547 4827917 := bstep (se 3 (by rfl) ⟨905234, by rfl⟩ : syracuseStep 4827917 = 1810469) B1810469
theorem B5425937 : Blo 1693547 5425937 := bstep (se 2 (by rfl) ⟨2034726, by rfl⟩ : syracuseStep 5425937 = 4069453) B4069453
theorem B2542355 : Blo 1693547 2542355 := bstep (se 1 (by rfl) ⟨1906766, by rfl⟩ : syracuseStep 2542355 = 3813533) B3813533
theorem B5720867 : Blo 1693547 5720867 := bstep (se 1 (by rfl) ⟨4290650, by rfl⟩ : syracuseStep 5720867 = 8581301) B8581301
theorem B2542385 : Blo 1693547 2542385 := bstep (se 2 (by rfl) ⟨953394, by rfl⟩ : syracuseStep 2542385 = 1906789) B1906789
theorem B24423221 : Blo 1693547 24423221 := bstep (se 5 (by rfl) ⟨1144838, by rfl⟩ : syracuseStep 24423221 = 2289677) B2289677
theorem B2542403 : Blo 1693547 2542403 := bstep (se 1 (by rfl) ⟨1906802, by rfl⟩ : syracuseStep 2542403 = 3813605) B3813605
theorem B2354003 : Blo 1693547 2354003 := bstep (se 1 (by rfl) ⟨1765502, by rfl⟩ : syracuseStep 2354003 = 3531005) B3531005
theorem B2542433 : Blo 1693547 2542433 := bstep (se 2 (by rfl) ⟨953412, by rfl⟩ : syracuseStep 2542433 = 1906825) B1906825
theorem B4582253 : Blo 1693547 4582253 := bstep (se 3 (by rfl) ⟨859172, by rfl⟩ : syracuseStep 4582253 = 1718345) B1718345
theorem B2542451 : Blo 1693547 2542451 := bstep (se 1 (by rfl) ⟨1906838, by rfl⟩ : syracuseStep 2542451 = 3813677) B3813677
theorem B2542481 : Blo 1693547 2542481 := bstep (se 2 (by rfl) ⟨953430, by rfl⟩ : syracuseStep 2542481 = 1906861) B1906861
theorem B2542499 : Blo 1693547 2542499 := bstep (se 1 (by rfl) ⟨1906874, by rfl⟩ : syracuseStep 2542499 = 3813749) B3813749
theorem B3812273 : Blo 1693547 3812273 := bstep (se 2 (by rfl) ⟨1429602, by rfl⟩ : syracuseStep 3812273 = 2859205) B2859205
theorem B8145841 : Blo 1693547 8145841 := bstep (se 2 (by rfl) ⟨3054690, by rfl⟩ : syracuseStep 8145841 = 6109381) B6109381
theorem B2542529 : Blo 1693547 2542529 := bstep (se 2 (by rfl) ⟨953448, by rfl⟩ : syracuseStep 2542529 = 1906897) B1906897
theorem B3812291 : Blo 1693547 3812291 := bstep (se 1 (by rfl) ⟨2859218, by rfl⟩ : syracuseStep 3812291 = 5718437) B5718437
theorem B2714563 : Blo 1693547 2714563 := bstep (se 1 (by rfl) ⟨2035922, by rfl⟩ : syracuseStep 2714563 = 4071845) B4071845
theorem B4828099 : Blo 1693547 4828099 := bstep (se 1 (by rfl) ⟨3621074, by rfl⟩ : syracuseStep 4828099 = 7242149) B7242149
theorem B2542547 : Blo 1693547 2542547 := bstep (se 1 (by rfl) ⟨1906910, by rfl⟩ : syracuseStep 2542547 = 3813821) B3813821
theorem B2714609 : Blo 1693547 2714609 := bstep (se 2 (by rfl) ⟨1017978, by rfl⟩ : syracuseStep 2714609 = 2035957) B2035957
theorem B2542577 : Blo 1693547 2542577 := bstep (se 2 (by rfl) ⟨953466, by rfl⟩ : syracuseStep 2542577 = 1906933) B1906933
theorem B2542595 : Blo 1693547 2542595 := bstep (se 1 (by rfl) ⟨1906946, by rfl⟩ : syracuseStep 2542595 = 3813893) B3813893
theorem B2542625 : Blo 1693547 2542625 := bstep (se 2 (by rfl) ⟨953484, by rfl⟩ : syracuseStep 2542625 = 1906969) B1906969
theorem B5721137 : Blo 1693547 5721137 := bstep (se 2 (by rfl) ⟨2145426, by rfl⟩ : syracuseStep 5721137 = 4290853) B4290853
theorem B2542643 : Blo 1693547 2542643 := bstep (se 1 (by rfl) ⟨1906982, by rfl⟩ : syracuseStep 2542643 = 3813965) B3813965
theorem B4893763 : Blo 1693547 4893763 := bstep (se 1 (by rfl) ⟨3670322, by rfl⟩ : syracuseStep 4893763 = 7340645) B7340645
theorem B4959313 : Blo 1693547 4959313 := bstep (se 2 (by rfl) ⟨1859742, by rfl⟩ : syracuseStep 4959313 = 3719485) B3719485
theorem B2542673 : Blo 1693547 2542673 := bstep (se 2 (by rfl) ⟨953502, by rfl⟩ : syracuseStep 2542673 = 1907005) B1907005
theorem B5221475 : Blo 1693547 5221475 := bstep (se 1 (by rfl) ⟨3916106, by rfl⟩ : syracuseStep 5221475 = 7832213) B7832213
theorem B6106211 : Blo 1693547 6106211 := bstep (se 1 (by rfl) ⟨4579658, by rfl⟩ : syracuseStep 6106211 = 9159317) B9159317
theorem B2542691 : Blo 1693547 2542691 := bstep (se 1 (by rfl) ⟨1907018, by rfl⟩ : syracuseStep 2542691 = 3814037) B3814037
theorem B2411635 : Blo 1693547 2411635 := bstep (se 1 (by rfl) ⟨1808726, by rfl⟩ : syracuseStep 2411635 = 3617453) B3617453
theorem B2542721 : Blo 1693547 2542721 := bstep (se 2 (by rfl) ⟨953520, by rfl⟩ : syracuseStep 2542721 = 1907041) B1907041
theorem B14470285 : Blo 1693547 14470285 := bstep (se 3 (by rfl) ⟨2713178, by rfl⟩ : syracuseStep 14470285 = 5426357) B5426357
theorem B2542739 : Blo 1693547 2542739 := bstep (se 1 (by rfl) ⟨1907054, by rfl⟩ : syracuseStep 2542739 = 3814109) B3814109
theorem B2575523 : Blo 1693547 2575523 := bstep (se 1 (by rfl) ⟨1931642, by rfl⟩ : syracuseStep 2575523 = 3863285) B3863285
theorem B10857635 : Blo 1693547 10857635 := bstep (se 1 (by rfl) ⟨8143226, by rfl⟩ : syracuseStep 10857635 = 16286453) B16286453
theorem B2542769 : Blo 1693547 2542769 := bstep (se 2 (by rfl) ⟨953538, by rfl⟩ : syracuseStep 2542769 = 1907077) B1907077
theorem B2542787 : Blo 1693547 2542787 := bstep (se 1 (by rfl) ⟨1907090, by rfl⟩ : syracuseStep 2542787 = 3814181) B3814181
theorem B3812561 : Blo 1693547 3812561 := bstep (se 2 (by rfl) ⟨1429710, by rfl⟩ : syracuseStep 3812561 = 2859421) B2859421
theorem B2542817 : Blo 1693547 2542817 := bstep (se 2 (by rfl) ⟨953556, by rfl⟩ : syracuseStep 2542817 = 1907113) B1907113
theorem B3812579 : Blo 1693547 3812579 := bstep (se 1 (by rfl) ⟨2859434, by rfl⟩ : syracuseStep 3812579 = 5718869) B5718869
theorem B15461603 : Blo 1693547 15461603 := bstep (se 1 (by rfl) ⟨11596202, by rfl⟩ : syracuseStep 15461603 = 23192405) B23192405
theorem B2542835 : Blo 1693547 2542835 := bstep (se 1 (by rfl) ⟨1907126, by rfl⟩ : syracuseStep 2542835 = 3814253) B3814253
theorem B2288899 : Blo 1693547 2288899 := bstep (se 1 (by rfl) ⟨1716674, by rfl⟩ : syracuseStep 2288899 = 3433349) B3433349
theorem B2542865 : Blo 1693547 2542865 := bstep (se 2 (by rfl) ⟨953574, by rfl⟩ : syracuseStep 2542865 = 1907149) B1907149
theorem B2542883 : Blo 1693547 2542883 := bstep (se 1 (by rfl) ⟨1907162, by rfl⟩ : syracuseStep 2542883 = 3814325) B3814325
theorem B2542913 : Blo 1693547 2542913 := bstep (se 2 (by rfl) ⟨953592, by rfl⟩ : syracuseStep 2542913 = 1907185) B1907185
theorem B4894033 : Blo 1693547 4894033 := bstep (se 2 (by rfl) ⟨1835262, by rfl⟩ : syracuseStep 4894033 = 3670525) B3670525
theorem B2542931 : Blo 1693547 2542931 := bstep (se 1 (by rfl) ⟨1907198, by rfl⟩ : syracuseStep 2542931 = 3814397) B3814397
theorem B2542961 : Blo 1693547 2542961 := bstep (se 2 (by rfl) ⟨953610, by rfl⟩ : syracuseStep 2542961 = 1907221) B1907221
theorem B2542979 : Blo 1693547 2542979 := bstep (se 1 (by rfl) ⟨1907234, by rfl⟩ : syracuseStep 2542979 = 3814469) B3814469
theorem B2543009 : Blo 1693547 2543009 := bstep (se 2 (by rfl) ⟨953628, by rfl⟩ : syracuseStep 2543009 = 1907257) B1907257
theorem B2543027 : Blo 1693547 2543027 := bstep (se 1 (by rfl) ⟨1907270, by rfl⟩ : syracuseStep 2543027 = 3814541) B3814541
theorem B16289221 : Blo 1693547 16289221 := bstep (se 4 (by rfl) ⟨1527114, by rfl⟩ : syracuseStep 16289221 = 3054229) B3054229
theorem B2543057 : Blo 1693547 2543057 := bstep (se 2 (by rfl) ⟨953646, by rfl⟩ : syracuseStep 2543057 = 1907293) B1907293
theorem B6434275 : Blo 1693547 6434275 := bstep (se 1 (by rfl) ⟨4825706, by rfl⟩ : syracuseStep 6434275 = 9651413) B9651413
theorem B2543075 : Blo 1693547 2543075 := bstep (se 1 (by rfl) ⟨1907306, by rfl⟩ : syracuseStep 2543075 = 3814613) B3814613
theorem B5795309 : Blo 1693547 5795309 := bstep (se 3 (by rfl) ⟨1086620, by rfl⟩ : syracuseStep 5795309 = 2173241) B2173241
theorem B3812849 : Blo 1693547 3812849 := bstep (se 2 (by rfl) ⟨1429818, by rfl⟩ : syracuseStep 3812849 = 2859637) B2859637
theorem B2543105 : Blo 1693547 2543105 := bstep (se 2 (by rfl) ⟨953664, by rfl⟩ : syracuseStep 2543105 = 1907329) B1907329
theorem B3812867 : Blo 1693547 3812867 := bstep (se 1 (by rfl) ⟨2859650, by rfl⟩ : syracuseStep 3812867 = 5719301) B5719301
theorem B9645581 : Blo 1693547 9645581 := bstep (se 3 (by rfl) ⟨1808546, by rfl⟩ : syracuseStep 9645581 = 3617093) B3617093
theorem B2543123 : Blo 1693547 2543123 := bstep (se 1 (by rfl) ⟨1907342, by rfl⟩ : syracuseStep 2543123 = 3814685) B3814685
theorem B4288049 : Blo 1693547 4288049 := bstep (se 2 (by rfl) ⟨1608018, by rfl⟩ : syracuseStep 4288049 = 3216037) B3216037
theorem B2543153 : Blo 1693547 2543153 := bstep (se 2 (by rfl) ⟨953682, by rfl⟩ : syracuseStep 2543153 = 1907365) B1907365
theorem B2543171 : Blo 1693547 2543171 := bstep (se 1 (by rfl) ⟨1907378, by rfl⟩ : syracuseStep 2543171 = 3814757) B3814757
theorem B5721677 : Blo 1693547 5721677 := bstep (se 3 (by rfl) ⟨1072814, by rfl⟩ : syracuseStep 5721677 = 2145629) B2145629
theorem B2543201 : Blo 1693547 2543201 := bstep (se 2 (by rfl) ⟨953700, by rfl⟩ : syracuseStep 2543201 = 1907401) B1907401
theorem B4288099 : Blo 1693547 4288099 := bstep (se 1 (by rfl) ⟨3216074, by rfl⟩ : syracuseStep 4288099 = 6432149) B6432149
theorem B2543219 : Blo 1693547 2543219 := bstep (se 1 (by rfl) ⟨1907414, by rfl⟩ : syracuseStep 2543219 = 3814829) B3814829
theorem B5721731 : Blo 1693547 5721731 := bstep (se 1 (by rfl) ⟨4291298, by rfl⟩ : syracuseStep 5721731 = 8582597) B8582597
theorem B2543249 : Blo 1693547 2543249 := bstep (se 2 (by rfl) ⟨953718, by rfl⟩ : syracuseStep 2543249 = 1907437) B1907437
theorem B2412193 : Blo 1693547 2412193 := bstep (se 2 (by rfl) ⟨904572, by rfl⟩ : syracuseStep 2412193 = 1809145) B1809145
theorem B2543267 : Blo 1693547 2543267 := bstep (se 1 (by rfl) ⟨1907450, by rfl⟩ : syracuseStep 2543267 = 3814901) B3814901
theorem B2543297 : Blo 1693547 2543297 := bstep (se 2 (by rfl) ⟨953736, by rfl⟩ : syracuseStep 2543297 = 1907473) B1907473
theorem B2412227 : Blo 1693547 2412227 := bstep (se 1 (by rfl) ⟨1809170, by rfl⟩ : syracuseStep 2412227 = 3618341) B3618341
theorem B2543315 : Blo 1693547 2543315 := bstep (se 1 (by rfl) ⟨1907486, by rfl⟩ : syracuseStep 2543315 = 3814973) B3814973
theorem B4288241 : Blo 1693547 4288241 := bstep (se 2 (by rfl) ⟨1608090, by rfl⟩ : syracuseStep 4288241 = 3216181) B3216181
theorem B3813137 : Blo 1693547 3813137 := bstep (se 2 (by rfl) ⟨1429926, by rfl⟩ : syracuseStep 3813137 = 2859853) B2859853
theorem B3813155 : Blo 1693547 3813155 := bstep (se 1 (by rfl) ⟨2859866, by rfl⟩ : syracuseStep 3813155 = 5719733) B5719733
theorem B8580977 : Blo 1693547 8580977 := bstep (se 2 (by rfl) ⟨3217866, by rfl⟩ : syracuseStep 8580977 = 6435733) B6435733
theorem B5722001 : Blo 1693547 5722001 := bstep (se 2 (by rfl) ⟨2145750, by rfl⟩ : syracuseStep 5722001 = 4291501) B4291501
theorem B2715601 : Blo 1693547 2715601 := bstep (se 2 (by rfl) ⟨1018350, by rfl⟩ : syracuseStep 2715601 = 2036701) B2036701
theorem B7237603 : Blo 1693547 7237603 := bstep (se 1 (by rfl) ⟨5428202, by rfl⟩ : syracuseStep 7237603 = 10856405) B10856405
theorem B3813425 : Blo 1693547 3813425 := bstep (se 2 (by rfl) ⟨1430034, by rfl⟩ : syracuseStep 3813425 = 2860069) B2860069
theorem B3813443 : Blo 1693547 3813443 := bstep (se 1 (by rfl) ⟨2860082, by rfl⟩ : syracuseStep 3813443 = 5720165) B5720165
theorem B10858637 : Blo 1693547 10858637 := bstep (se 3 (by rfl) ⟨2035994, by rfl⟩ : syracuseStep 10858637 = 4071989) B4071989
theorem B2412785 : Blo 1693547 2412785 := bstep (se 2 (by rfl) ⟨904794, by rfl⟩ : syracuseStep 2412785 = 1809589) B1809589
theorem B2289937 : Blo 1693547 2289937 := bstep (se 2 (by rfl) ⟨858726, by rfl⟩ : syracuseStep 2289937 = 1717453) B1717453
theorem B2412865 : Blo 1693547 2412865 := bstep (se 2 (by rfl) ⟨904824, by rfl⟩ : syracuseStep 2412865 = 1809649) B1809649
theorem B3813713 : Blo 1693547 3813713 := bstep (se 2 (by rfl) ⟨1430142, by rfl⟩ : syracuseStep 3813713 = 2860285) B2860285
theorem B3813731 : Blo 1693547 3813731 := bstep (se 1 (by rfl) ⟨2860298, by rfl⟩ : syracuseStep 3813731 = 5720597) B5720597
theorem B37155185 : Blo 1693547 37155185 := bstep (se 2 (by rfl) ⟨13933194, by rfl⟩ : syracuseStep 37155185 = 27866389) B27866389
theorem B14471621 : Blo 1693547 14471621 := bstep (se 4 (by rfl) ⟨1356714, by rfl⟩ : syracuseStep 14471621 = 2713429) B2713429
theorem B3215953 : Blo 1693547 3215953 := bstep (se 2 (by rfl) ⟨1205982, by rfl⟩ : syracuseStep 3215953 = 2411965) B2411965
theorem B3814001 : Blo 1693547 3814001 := bstep (se 2 (by rfl) ⟨1430250, by rfl⟩ : syracuseStep 3814001 = 2860501) B2860501
theorem B3814019 : Blo 1693547 3814019 := bstep (se 1 (by rfl) ⟨2860514, by rfl⟩ : syracuseStep 3814019 = 5721029) B5721029
theorem B6107825 : Blo 1693547 6107825 := bstep (se 2 (by rfl) ⟨2290434, by rfl⟩ : syracuseStep 6107825 = 4580869) B4580869
theorem B1905331 : Blo 1693547 1905331 := bstep (se 1 (by rfl) ⟨1428998, by rfl⟩ : syracuseStep 1905331 = 2857997) B2857997
theorem B9163469 : Blo 1693547 9163469 := bstep (se 3 (by rfl) ⟨1718150, by rfl⟩ : syracuseStep 9163469 = 3436301) B3436301
theorem B4289233 : Blo 1693547 4289233 := bstep (se 2 (by rfl) ⟨1608462, by rfl⟩ : syracuseStep 4289233 = 3216925) B3216925
theorem B2446097 : Blo 1693547 2446097 := bstep (se 2 (by rfl) ⟨917286, by rfl⟩ : syracuseStep 2446097 = 1834573) B1834573
theorem B1905475 : Blo 1693547 1905475 := bstep (se 1 (by rfl) ⟨1429106, by rfl⟩ : syracuseStep 1905475 = 2858213) B2858213
theorem B3814289 : Blo 1693547 3814289 := bstep (se 2 (by rfl) ⟨1430358, by rfl⟩ : syracuseStep 3814289 = 2860717) B2860717
theorem B3814307 : Blo 1693547 3814307 := bstep (se 1 (by rfl) ⟨2860730, by rfl⟩ : syracuseStep 3814307 = 5721461) B5721461
theorem B1905619 : Blo 1693547 1905619 := bstep (se 1 (by rfl) ⟨1429214, by rfl⟩ : syracuseStep 1905619 = 2858429) B2858429
theorem B4289507 : Blo 1693547 4289507 := bstep (se 1 (by rfl) ⟨3217130, by rfl⟩ : syracuseStep 4289507 = 6434261) B6434261
theorem B3617777 : Blo 1693547 3617777 := bstep (se 2 (by rfl) ⟨1356666, by rfl⟩ : syracuseStep 3617777 = 2713333) B2713333
theorem B14480369 : Blo 1693547 14480369 := bstep (se 2 (by rfl) ⟨5430138, by rfl⟩ : syracuseStep 14480369 = 10860277) B10860277
theorem B2413651 : Blo 1693547 2413651 := bstep (se 1 (by rfl) ⟨1810238, by rfl⟩ : syracuseStep 2413651 = 3620477) B3620477
theorem B1905763 : Blo 1693547 1905763 := bstep (se 1 (by rfl) ⟨1429322, by rfl⟩ : syracuseStep 1905763 = 2858645) B2858645
theorem B4289699 : Blo 1693547 4289699 := bstep (se 1 (by rfl) ⟨3217274, by rfl⟩ : syracuseStep 4289699 = 6434549) B6434549
theorem B5428397 : Blo 1693547 5428397 := bstep (se 3 (by rfl) ⟨1017824, by rfl⟩ : syracuseStep 5428397 = 2035649) B2035649
theorem B3814577 : Blo 1693547 3814577 := bstep (se 2 (by rfl) ⟨1430466, by rfl⟩ : syracuseStep 3814577 = 2860933) B2860933
theorem B3814595 : Blo 1693547 3814595 := bstep (se 1 (by rfl) ⟨2860946, by rfl⟩ : syracuseStep 3814595 = 5721893) B5721893
theorem B1905907 : Blo 1693547 1905907 := bstep (se 1 (by rfl) ⟨1429430, by rfl⟩ : syracuseStep 1905907 = 2858861) B2858861
theorem B2143523 : Blo 1693547 2143523 := bstep (se 1 (by rfl) ⟨1607642, by rfl⟩ : syracuseStep 2143523 = 3215285) B3215285
theorem B8582435 : Blo 1693547 8582435 := bstep (se 1 (by rfl) ⟨6436826, by rfl⟩ : syracuseStep 8582435 = 12873653) B12873653
theorem B3618179 : Blo 1693547 3618179 := bstep (se 1 (by rfl) ⟨2713634, by rfl⟩ : syracuseStep 3618179 = 5427269) B5427269
theorem B1906051 : Blo 1693547 1906051 := bstep (se 1 (by rfl) ⟨1429538, by rfl⟩ : syracuseStep 1906051 = 2859077) B2859077
theorem B2291105 : Blo 1693547 2291105 := bstep (se 2 (by rfl) ⟨859164, by rfl⟩ : syracuseStep 2291105 = 1718329) B1718329
theorem B3814865 : Blo 1693547 3814865 := bstep (se 2 (by rfl) ⟨1430574, by rfl⟩ : syracuseStep 3814865 = 2861149) B2861149
theorem B3814883 : Blo 1693547 3814883 := bstep (se 1 (by rfl) ⟨2861162, by rfl⟩ : syracuseStep 3814883 = 5722325) B5722325
theorem B1906195 : Blo 1693547 1906195 := bstep (se 1 (by rfl) ⟨1429646, by rfl⟩ : syracuseStep 1906195 = 2859293) B2859293
theorem B2414129 : Blo 1693547 2414129 := bstep (se 2 (by rfl) ⟨905298, by rfl⟩ : syracuseStep 2414129 = 1810597) B1810597
theorem B7730765 : Blo 1693547 7730765 := bstep (se 3 (by rfl) ⟨1449518, by rfl⟩ : syracuseStep 7730765 = 2899037) B2899037
theorem B5502563 : Blo 1693547 5502563 := bstep (se 1 (by rfl) ⟨4126922, by rfl⟩ : syracuseStep 5502563 = 8253845) B8253845
theorem B5150317 : Blo 1693547 5150317 := bstep (se 3 (by rfl) ⟨965684, by rfl⟩ : syracuseStep 5150317 = 1931369) B1931369
theorem B3217009 : Blo 1693547 3217009 := bstep (se 2 (by rfl) ⟨1206378, by rfl⟩ : syracuseStep 3217009 = 2412757) B2412757
theorem B6436493 : Blo 1693547 6436493 := bstep (se 3 (by rfl) ⟨1206842, by rfl⟩ : syracuseStep 6436493 = 2413685) B2413685
theorem B1906339 : Blo 1693547 1906339 := bstep (se 1 (by rfl) ⟨1429754, by rfl⟩ : syracuseStep 1906339 = 2859509) B2859509
theorem B21190385 : Blo 1693547 21190385 := bstep (se 2 (by rfl) ⟨7946394, by rfl⟩ : syracuseStep 21190385 = 15892789) B15892789
theorem B1906483 : Blo 1693547 1906483 := bstep (se 1 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 1906483 = 2859725) B2859725
theorem B1693555 : Blo 1693547 1693555 := bstep (se 1 (by rfl) ⟨1270166, by rfl⟩ : syracuseStep 1693555 = 2540333) B2540333
theorem B1693571 : Blo 1693547 1693571 := bstep (se 1 (by rfl) ⟨1270178, by rfl⟩ : syracuseStep 1693571 = 2540357) B2540357
theorem B1693587 : Blo 1693547 1693587 := bstep (se 1 (by rfl) ⟨1270190, by rfl⟩ : syracuseStep 1693587 = 2540381) B2540381
theorem B1693603 : Blo 1693547 1693603 := bstep (se 1 (by rfl) ⟨1270202, by rfl⟩ : syracuseStep 1693603 = 2540405) B2540405
theorem B1693619 : Blo 1693547 1693619 := bstep (se 1 (by rfl) ⟨1270214, by rfl⟩ : syracuseStep 1693619 = 2540429) B2540429
theorem B1693635 : Blo 1693547 1693635 := bstep (se 1 (by rfl) ⟨1270226, by rfl⟩ : syracuseStep 1693635 = 2540453) B2540453
theorem B1906627 : Blo 1693547 1906627 := bstep (se 1 (by rfl) ⟨1429970, by rfl⟩ : syracuseStep 1906627 = 2859941) B2859941
theorem B11589581 : Blo 1693547 11589581 := bstep (se 3 (by rfl) ⟨2173046, by rfl⟩ : syracuseStep 11589581 = 4346093) B4346093
theorem B1693651 : Blo 1693547 1693651 := bstep (se 1 (by rfl) ⟨1270238, by rfl⟩ : syracuseStep 1693651 = 2540477) B2540477
theorem B1693667 : Blo 1693547 1693667 := bstep (se 1 (by rfl) ⟨1270250, by rfl⟩ : syracuseStep 1693667 = 2540501) B2540501
theorem B2144227 : Blo 1693547 2144227 := bstep (se 1 (by rfl) ⟨1608170, by rfl⟩ : syracuseStep 2144227 = 3216341) B3216341
theorem B5715953 : Blo 1693547 5715953 := bstep (se 2 (by rfl) ⟨2143482, by rfl⟩ : syracuseStep 5715953 = 4286965) B4286965
theorem B1693683 : Blo 1693547 1693683 := bstep (se 1 (by rfl) ⟨1270262, by rfl⟩ : syracuseStep 1693683 = 2540525) B2540525
theorem B1693699 : Blo 1693547 1693699 := bstep (se 1 (by rfl) ⟨1270274, by rfl⟩ : syracuseStep 1693699 = 2540549) B2540549
theorem B3217411 : Blo 1693547 3217411 := bstep (se 1 (by rfl) ⟨2413058, by rfl⟩ : syracuseStep 3217411 = 4826117) B4826117
theorem B1693715 : Blo 1693547 1693715 := bstep (se 1 (by rfl) ⟨1270286, by rfl⟩ : syracuseStep 1693715 = 2540573) B2540573
theorem B1693731 : Blo 1693547 1693731 := bstep (se 1 (by rfl) ⟨1270298, by rfl⟩ : syracuseStep 1693731 = 2540597) B2540597
theorem B3217457 : Blo 1693547 3217457 := bstep (se 2 (by rfl) ⟨1206546, by rfl⟩ : syracuseStep 3217457 = 2413093) B2413093
theorem B1693747 : Blo 1693547 1693747 := bstep (se 1 (by rfl) ⟨1270310, by rfl⟩ : syracuseStep 1693747 = 2540621) B2540621
theorem B1693763 : Blo 1693547 1693763 := bstep (se 1 (by rfl) ⟨1270322, by rfl⟩ : syracuseStep 1693763 = 2540645) B2540645
theorem B2144323 : Blo 1693547 2144323 := bstep (se 1 (by rfl) ⟨1608242, by rfl⟩ : syracuseStep 2144323 = 3216485) B3216485
theorem B4290641 : Blo 1693547 4290641 := bstep (se 2 (by rfl) ⟨1608990, by rfl⟩ : syracuseStep 4290641 = 3217981) B3217981
theorem B8583245 : Blo 1693547 8583245 := bstep (se 3 (by rfl) ⟨1609358, by rfl⟩ : syracuseStep 8583245 = 3218717) B3218717
theorem B1693779 : Blo 1693547 1693779 := bstep (se 1 (by rfl) ⟨1270334, by rfl⟩ : syracuseStep 1693779 = 2540669) B2540669
theorem B1906771 : Blo 1693547 1906771 := bstep (se 1 (by rfl) ⟨1430078, by rfl⟩ : syracuseStep 1906771 = 2860157) B2860157
theorem B1693795 : Blo 1693547 1693795 := bstep (se 1 (by rfl) ⟨1270346, by rfl⟩ : syracuseStep 1693795 = 2540693) B2540693
theorem B21706865 : Blo 1693547 21706865 := bstep (se 2 (by rfl) ⟨8140074, by rfl⟩ : syracuseStep 21706865 = 16280149) B16280149
theorem B1693811 : Blo 1693547 1693811 := bstep (se 1 (by rfl) ⟨1270358, by rfl⟩ : syracuseStep 1693811 = 2540717) B2540717
theorem B1693827 : Blo 1693547 1693827 := bstep (se 1 (by rfl) ⟨1270370, by rfl⟩ : syracuseStep 1693827 = 2540741) B2540741
theorem B4290691 : Blo 1693547 4290691 := bstep (se 1 (by rfl) ⟨3218018, by rfl⟩ : syracuseStep 4290691 = 6436037) B6436037
theorem B1693843 : Blo 1693547 1693843 := bstep (se 1 (by rfl) ⟨1270382, by rfl⟩ : syracuseStep 1693843 = 2540765) B2540765
theorem B1693859 : Blo 1693547 1693859 := bstep (se 1 (by rfl) ⟨1270394, by rfl⟩ : syracuseStep 1693859 = 2540789) B2540789
theorem B1693875 : Blo 1693547 1693875 := bstep (se 1 (by rfl) ⟨1270406, by rfl⟩ : syracuseStep 1693875 = 2540813) B2540813
theorem B1693891 : Blo 1693547 1693891 := bstep (se 1 (by rfl) ⟨1270418, by rfl⟩ : syracuseStep 1693891 = 2540837) B2540837
theorem B1693907 : Blo 1693547 1693907 := bstep (se 1 (by rfl) ⟨1270430, by rfl⟩ : syracuseStep 1693907 = 2540861) B2540861
theorem B1693923 : Blo 1693547 1693923 := bstep (se 1 (by rfl) ⟨1270442, by rfl⟩ : syracuseStep 1693923 = 2540885) B2540885
theorem B1906915 : Blo 1693547 1906915 := bstep (se 1 (by rfl) ⟨1430186, by rfl⟩ : syracuseStep 1906915 = 2860373) B2860373
theorem B1693939 : Blo 1693547 1693939 := bstep (se 1 (by rfl) ⟨1270454, by rfl⟩ : syracuseStep 1693939 = 2540909) B2540909
theorem B1693955 : Blo 1693547 1693955 := bstep (se 1 (by rfl) ⟨1270466, by rfl⟩ : syracuseStep 1693955 = 2540933) B2540933
theorem B3619075 : Blo 1693547 3619075 := bstep (se 1 (by rfl) ⟨2714306, by rfl⟩ : syracuseStep 3619075 = 5428613) B5428613
theorem B10852613 : Blo 1693547 10852613 := bstep (se 4 (by rfl) ⟨1017432, by rfl⟩ : syracuseStep 10852613 = 2034865) B2034865
theorem B4290833 : Blo 1693547 4290833 := bstep (se 2 (by rfl) ⟨1609062, by rfl⟩ : syracuseStep 4290833 = 3218125) B3218125
theorem B1693971 : Blo 1693547 1693971 := bstep (se 1 (by rfl) ⟨1270478, by rfl⟩ : syracuseStep 1693971 = 2540957) B2540957
theorem B4888867 : Blo 1693547 4888867 := bstep (se 1 (by rfl) ⟨3666650, by rfl⟩ : syracuseStep 4888867 = 7333301) B7333301
theorem B1693987 : Blo 1693547 1693987 := bstep (se 1 (by rfl) ⟨1270490, by rfl⟩ : syracuseStep 1693987 = 2540981) B2540981
theorem B1694003 : Blo 1693547 1694003 := bstep (se 1 (by rfl) ⟨1270502, by rfl⟩ : syracuseStep 1694003 = 2541005) B2541005
theorem B1694019 : Blo 1693547 1694019 := bstep (se 1 (by rfl) ⟨1270514, by rfl⟩ : syracuseStep 1694019 = 2541029) B2541029
theorem B3217745 : Blo 1693547 3217745 := bstep (se 2 (by rfl) ⟨1206654, by rfl⟩ : syracuseStep 3217745 = 2413309) B2413309
theorem B1694035 : Blo 1693547 1694035 := bstep (se 1 (by rfl) ⟨1270526, by rfl⟩ : syracuseStep 1694035 = 2541053) B2541053
theorem B1694051 : Blo 1693547 1694051 := bstep (se 1 (by rfl) ⟨1270538, by rfl⟩ : syracuseStep 1694051 = 2541077) B2541077
theorem B9648497 : Blo 1693547 9648497 := bstep (se 2 (by rfl) ⟨3618186, by rfl⟩ : syracuseStep 9648497 = 7236373) B7236373
theorem B7240049 : Blo 1693547 7240049 := bstep (se 2 (by rfl) ⟨2715018, by rfl⟩ : syracuseStep 7240049 = 5430037) B5430037
theorem B1694067 : Blo 1693547 1694067 := bstep (se 1 (by rfl) ⟨1270550, by rfl⟩ : syracuseStep 1694067 = 2541101) B2541101
theorem B1907059 : Blo 1693547 1907059 := bstep (se 1 (by rfl) ⟨1430294, by rfl⟩ : syracuseStep 1907059 = 2860589) B2860589
theorem B1694083 : Blo 1693547 1694083 := bstep (se 1 (by rfl) ⟨1270562, by rfl⟩ : syracuseStep 1694083 = 2541125) B2541125
theorem B1694099 : Blo 1693547 1694099 := bstep (se 1 (by rfl) ⟨1270574, by rfl⟩ : syracuseStep 1694099 = 2541149) B2541149
theorem B1694115 : Blo 1693547 1694115 := bstep (se 1 (by rfl) ⟨1270586, by rfl⟩ : syracuseStep 1694115 = 2541173) B2541173
theorem B1694131 : Blo 1693547 1694131 := bstep (se 1 (by rfl) ⟨1270598, by rfl⟩ : syracuseStep 1694131 = 2541197) B2541197
theorem B1694147 : Blo 1693547 1694147 := bstep (se 1 (by rfl) ⟨1270610, by rfl⟩ : syracuseStep 1694147 = 2541221) B2541221
theorem B1694163 : Blo 1693547 1694163 := bstep (se 1 (by rfl) ⟨1270622, by rfl⟩ : syracuseStep 1694163 = 2541245) B2541245
theorem B1694179 : Blo 1693547 1694179 := bstep (se 1 (by rfl) ⟨1270634, by rfl⟩ : syracuseStep 1694179 = 2541269) B2541269
theorem B1694195 : Blo 1693547 1694195 := bstep (se 1 (by rfl) ⟨1270646, by rfl⟩ : syracuseStep 1694195 = 2541293) B2541293
theorem B1694211 : Blo 1693547 1694211 := bstep (se 1 (by rfl) ⟨1270658, by rfl⟩ : syracuseStep 1694211 = 2541317) B2541317
theorem B1907203 : Blo 1693547 1907203 := bstep (se 1 (by rfl) ⟨1430402, by rfl⟩ : syracuseStep 1907203 = 2860805) B2860805
theorem B5716493 : Blo 1693547 5716493 := bstep (se 3 (by rfl) ⟨1071842, by rfl⟩ : syracuseStep 5716493 = 2143685) B2143685
theorem B1694227 : Blo 1693547 1694227 := bstep (se 1 (by rfl) ⟨1270670, by rfl⟩ : syracuseStep 1694227 = 2541341) B2541341
theorem B1694243 : Blo 1693547 1694243 := bstep (se 1 (by rfl) ⟨1270682, by rfl⟩ : syracuseStep 1694243 = 2541365) B2541365
theorem B1694259 : Blo 1693547 1694259 := bstep (se 1 (by rfl) ⟨1270694, by rfl⟩ : syracuseStep 1694259 = 2541389) B2541389
theorem B2144819 : Blo 1693547 2144819 := bstep (se 1 (by rfl) ⟨1608614, by rfl⟩ : syracuseStep 2144819 = 3217229) B3217229
theorem B5716547 : Blo 1693547 5716547 := bstep (se 1 (by rfl) ⟨4287410, by rfl⟩ : syracuseStep 5716547 = 8574821) B8574821
theorem B1694275 : Blo 1693547 1694275 := bstep (se 1 (by rfl) ⟨1270706, by rfl⟩ : syracuseStep 1694275 = 2541413) B2541413
theorem B1694291 : Blo 1693547 1694291 := bstep (se 1 (by rfl) ⟨1270718, by rfl⟩ : syracuseStep 1694291 = 2541437) B2541437
theorem B1694307 : Blo 1693547 1694307 := bstep (se 1 (by rfl) ⟨1270730, by rfl⟩ : syracuseStep 1694307 = 2541461) B2541461
theorem B1694323 : Blo 1693547 1694323 := bstep (se 1 (by rfl) ⟨1270742, by rfl⟩ : syracuseStep 1694323 = 2541485) B2541485
theorem B1694339 : Blo 1693547 1694339 := bstep (se 1 (by rfl) ⟨1270754, by rfl⟩ : syracuseStep 1694339 = 2541509) B2541509
theorem B1694355 : Blo 1693547 1694355 := bstep (se 1 (by rfl) ⟨1270766, by rfl⟩ : syracuseStep 1694355 = 2541533) B2541533
theorem B1907347 : Blo 1693547 1907347 := bstep (se 1 (by rfl) ⟨1430510, by rfl⟩ : syracuseStep 1907347 = 2861021) B2861021
theorem B1809059 : Blo 1693547 1809059 := bstep (se 1 (by rfl) ⟨1356794, by rfl⟩ : syracuseStep 1809059 = 2713589) B2713589
theorem B1694371 : Blo 1693547 1694371 := bstep (se 1 (by rfl) ⟨1270778, by rfl⟩ : syracuseStep 1694371 = 2541557) B2541557
theorem B4823725 : Blo 1693547 4823725 := bstep (se 3 (by rfl) ⟨904448, by rfl⟩ : syracuseStep 4823725 = 1808897) B1808897
theorem B1694387 : Blo 1693547 1694387 := bstep (se 1 (by rfl) ⟨1270790, by rfl⟩ : syracuseStep 1694387 = 2541581) B2541581
theorem B1694403 : Blo 1693547 1694403 := bstep (se 1 (by rfl) ⟨1270802, by rfl⟩ : syracuseStep 1694403 = 2541605) B2541605
theorem B6109901 : Blo 1693547 6109901 := bstep (se 3 (by rfl) ⟨1145606, by rfl⟩ : syracuseStep 6109901 = 2291213) B2291213
theorem B1694419 : Blo 1693547 1694419 := bstep (se 1 (by rfl) ⟨1270814, by rfl⟩ : syracuseStep 1694419 = 2541629) B2541629
theorem B1694435 : Blo 1693547 1694435 := bstep (se 1 (by rfl) ⟨1270826, by rfl⟩ : syracuseStep 1694435 = 2541653) B2541653
theorem B1694451 : Blo 1693547 1694451 := bstep (se 1 (by rfl) ⟨1270838, by rfl⟩ : syracuseStep 1694451 = 2541677) B2541677
theorem B1694467 : Blo 1693547 1694467 := bstep (se 1 (by rfl) ⟨1270850, by rfl⟩ : syracuseStep 1694467 = 2541701) B2541701
theorem B1694483 : Blo 1693547 1694483 := bstep (se 1 (by rfl) ⟨1270862, by rfl⟩ : syracuseStep 1694483 = 2541725) B2541725
theorem B1694499 : Blo 1693547 1694499 := bstep (se 1 (by rfl) ⟨1270874, by rfl⟩ : syracuseStep 1694499 = 2541749) B2541749
theorem B1907491 : Blo 1693547 1907491 := bstep (se 1 (by rfl) ⟨1430618, by rfl⟩ : syracuseStep 1907491 = 2861237) B2861237
theorem B8575793 : Blo 1693547 8575793 := bstep (se 2 (by rfl) ⟨3215922, by rfl⟩ : syracuseStep 8575793 = 6431845) B6431845
theorem B4348721 : Blo 1693547 4348721 := bstep (se 2 (by rfl) ⟨1630770, by rfl⟩ : syracuseStep 4348721 = 3261541) B3261541
theorem B1694515 : Blo 1693547 1694515 := bstep (se 1 (by rfl) ⟨1270886, by rfl⟩ : syracuseStep 1694515 = 2541773) B2541773
theorem B1694531 : Blo 1693547 1694531 := bstep (se 1 (by rfl) ⟨1270898, by rfl⟩ : syracuseStep 1694531 = 2541797) B2541797
theorem B5716817 : Blo 1693547 5716817 := bstep (se 2 (by rfl) ⟨2143806, by rfl⟩ : syracuseStep 5716817 = 4287613) B4287613
theorem B1694547 : Blo 1693547 1694547 := bstep (se 1 (by rfl) ⟨1270910, by rfl⟩ : syracuseStep 1694547 = 2541821) B2541821
theorem B1694563 : Blo 1693547 1694563 := bstep (se 1 (by rfl) ⟨1270922, by rfl⟩ : syracuseStep 1694563 = 2541845) B2541845
theorem B1694579 : Blo 1693547 1694579 := bstep (se 1 (by rfl) ⟨1270934, by rfl⟩ : syracuseStep 1694579 = 2541869) B2541869
theorem B1694595 : Blo 1693547 1694595 := bstep (se 1 (by rfl) ⟨1270946, by rfl⟩ : syracuseStep 1694595 = 2541893) B2541893
theorem B1694611 : Blo 1693547 1694611 := bstep (se 1 (by rfl) ⟨1270958, by rfl⟩ : syracuseStep 1694611 = 2541917) B2541917
theorem B2857889 : Blo 1693547 2857889 := bstep (se 2 (by rfl) ⟨1071708, by rfl⟩ : syracuseStep 2857889 = 2143417) B2143417
theorem B1694627 : Blo 1693547 1694627 := bstep (se 1 (by rfl) ⟨1270970, by rfl⟩ : syracuseStep 1694627 = 2541941) B2541941
theorem B4578221 : Blo 1693547 4578221 := bstep (se 3 (by rfl) ⟨858416, by rfl⟩ : syracuseStep 4578221 = 1716833) B1716833
theorem B1694643 : Blo 1693547 1694643 := bstep (se 1 (by rfl) ⟨1270982, by rfl⟩ : syracuseStep 1694643 = 2541965) B2541965
theorem B1694659 : Blo 1693547 1694659 := bstep (se 1 (by rfl) ⟨1270994, by rfl⟩ : syracuseStep 1694659 = 2541989) B2541989
theorem B31783877 : Blo 1693547 31783877 := bstep (se 4 (by rfl) ⟨2979738, by rfl⟩ : syracuseStep 31783877 = 5959477) B5959477
theorem B1694675 : Blo 1693547 1694675 := bstep (se 1 (by rfl) ⟨1271006, by rfl⟩ : syracuseStep 1694675 = 2542013) B2542013
theorem B4578275 : Blo 1693547 4578275 := bstep (se 1 (by rfl) ⟨3433706, by rfl⟩ : syracuseStep 4578275 = 6867413) B6867413
theorem B1694691 : Blo 1693547 1694691 := bstep (se 1 (by rfl) ⟨1271018, by rfl⟩ : syracuseStep 1694691 = 2542037) B2542037
theorem B5430253 : Blo 1693547 5430253 := bstep (se 3 (by rfl) ⟨1018172, by rfl⟩ : syracuseStep 5430253 = 2036345) B2036345
theorem B1694707 : Blo 1693547 1694707 := bstep (se 1 (by rfl) ⟨1271030, by rfl⟩ : syracuseStep 1694707 = 2542061) B2542061
theorem B1694723 : Blo 1693547 1694723 := bstep (se 1 (by rfl) ⟨1271042, by rfl⟩ : syracuseStep 1694723 = 2542085) B2542085
theorem B1694739 : Blo 1693547 1694739 := bstep (se 1 (by rfl) ⟨1271054, by rfl⟩ : syracuseStep 1694739 = 2542109) B2542109
theorem B2858017 : Blo 1693547 2858017 := bstep (se 2 (by rfl) ⟨1071756, by rfl⟩ : syracuseStep 2858017 = 2143513) B2143513
theorem B1694755 : Blo 1693547 1694755 := bstep (se 1 (by rfl) ⟨1271066, by rfl⟩ : syracuseStep 1694755 = 2542133) B2542133
theorem B3218467 : Blo 1693547 3218467 := bstep (se 1 (by rfl) ⟨2413850, by rfl⟩ : syracuseStep 3218467 = 4827701) B4827701
theorem B1694771 : Blo 1693547 1694771 := bstep (se 1 (by rfl) ⟨1271078, by rfl⟩ : syracuseStep 1694771 = 2542157) B2542157
theorem B2858051 : Blo 1693547 2858051 := bstep (se 1 (by rfl) ⟨2143538, by rfl⟩ : syracuseStep 2858051 = 4287077) B4287077
theorem B1694787 : Blo 1693547 1694787 := bstep (se 1 (by rfl) ⟨1271090, by rfl⟩ : syracuseStep 1694787 = 2542181) B2542181
theorem B1694803 : Blo 1693547 1694803 := bstep (se 1 (by rfl) ⟨1271102, by rfl⟩ : syracuseStep 1694803 = 2542205) B2542205
theorem B1694819 : Blo 1693547 1694819 := bstep (se 1 (by rfl) ⟨1271114, by rfl⟩ : syracuseStep 1694819 = 2542229) B2542229
theorem B4643939 : Blo 1693547 4643939 := bstep (se 1 (by rfl) ⟨3482954, by rfl⟩ : syracuseStep 4643939 = 6965909) B6965909
theorem B1694835 : Blo 1693547 1694835 := bstep (se 1 (by rfl) ⟨1271126, by rfl⟩ : syracuseStep 1694835 = 2542253) B2542253
theorem B1694851 : Blo 1693547 1694851 := bstep (se 1 (by rfl) ⟨1271138, by rfl⟩ : syracuseStep 1694851 = 2542277) B2542277
theorem B1694867 : Blo 1693547 1694867 := bstep (se 1 (by rfl) ⟨1271150, by rfl⟩ : syracuseStep 1694867 = 2542301) B2542301
theorem B1694883 : Blo 1693547 1694883 := bstep (se 1 (by rfl) ⟨1271162, by rfl⟩ : syracuseStep 1694883 = 2542325) B2542325
theorem B1694899 : Blo 1693547 1694899 := bstep (se 1 (by rfl) ⟨1271174, by rfl⟩ : syracuseStep 1694899 = 2542349) B2542349
theorem B2858179 : Blo 1693547 2858179 := bstep (se 1 (by rfl) ⟨2143634, by rfl⟩ : syracuseStep 2858179 = 4287269) B4287269
theorem B1694915 : Blo 1693547 1694915 := bstep (se 1 (by rfl) ⟨1271186, by rfl⟩ : syracuseStep 1694915 = 2542373) B2542373
theorem B1694931 : Blo 1693547 1694931 := bstep (se 1 (by rfl) ⟨1271198, by rfl⟩ : syracuseStep 1694931 = 2542397) B2542397
theorem B1694947 : Blo 1693547 1694947 := bstep (se 1 (by rfl) ⟨1271210, by rfl⟩ : syracuseStep 1694947 = 2542421) B2542421
theorem B4291825 : Blo 1693547 4291825 := bstep (se 2 (by rfl) ⟨1609434, by rfl⟩ : syracuseStep 4291825 = 3218869) B3218869
theorem B1694963 : Blo 1693547 1694963 := bstep (se 1 (by rfl) ⟨1271222, by rfl⟩ : syracuseStep 1694963 = 2542445) B2542445
theorem B2145523 : Blo 1693547 2145523 := bstep (se 1 (by rfl) ⟨1609142, by rfl⟩ : syracuseStep 2145523 = 3218285) B3218285
theorem B1694979 : Blo 1693547 1694979 := bstep (se 1 (by rfl) ⟨1271234, by rfl⟩ : syracuseStep 1694979 = 2542469) B2542469
theorem B1694995 : Blo 1693547 1694995 := bstep (se 1 (by rfl) ⟨1271246, by rfl⟩ : syracuseStep 1694995 = 2542493) B2542493
theorem B1695011 : Blo 1693547 1695011 := bstep (se 1 (by rfl) ⟨1271258, by rfl⟩ : syracuseStep 1695011 = 2542517) B2542517
theorem B1695027 : Blo 1693547 1695027 := bstep (se 1 (by rfl) ⟨1271270, by rfl⟩ : syracuseStep 1695027 = 2542541) B2542541
theorem B1695043 : Blo 1693547 1695043 := bstep (se 1 (by rfl) ⟨1271282, by rfl⟩ : syracuseStep 1695043 = 2542565) B2542565
theorem B2858321 : Blo 1693547 2858321 := bstep (se 2 (by rfl) ⟨1071870, by rfl⟩ : syracuseStep 2858321 = 2143741) B2143741
theorem B1695059 : Blo 1693547 1695059 := bstep (se 1 (by rfl) ⟨1271294, by rfl⟩ : syracuseStep 1695059 = 2542589) B2542589
theorem B2145619 : Blo 1693547 2145619 := bstep (se 1 (by rfl) ⟨1609214, by rfl⟩ : syracuseStep 2145619 = 3218429) B3218429
theorem B1695075 : Blo 1693547 1695075 := bstep (se 1 (by rfl) ⟨1271306, by rfl⟩ : syracuseStep 1695075 = 2542613) B2542613
theorem B5717357 : Blo 1693547 5717357 := bstep (se 3 (by rfl) ⟨1072004, by rfl⟩ : syracuseStep 5717357 = 2144009) B2144009
theorem B7839089 : Blo 1693547 7839089 := bstep (se 2 (by rfl) ⟨2939658, by rfl⟩ : syracuseStep 7839089 = 5879317) B5879317
theorem B1695091 : Blo 1693547 1695091 := bstep (se 1 (by rfl) ⟨1271318, by rfl⟩ : syracuseStep 1695091 = 2542637) B2542637
theorem B1695107 : Blo 1693547 1695107 := bstep (se 1 (by rfl) ⟨1271330, by rfl⟩ : syracuseStep 1695107 = 2542661) B2542661
theorem B1809811 : Blo 1693547 1809811 := bstep (se 1 (by rfl) ⟨1357358, by rfl⟩ : syracuseStep 1809811 = 2714717) B2714717
theorem B1695123 : Blo 1693547 1695123 := bstep (se 1 (by rfl) ⟨1271342, by rfl⟩ : syracuseStep 1695123 = 2542685) B2542685
theorem B5717411 : Blo 1693547 5717411 := bstep (se 1 (by rfl) ⟨4288058, by rfl⟩ : syracuseStep 5717411 = 8576117) B8576117
theorem B2751907 : Blo 1693547 2751907 := bstep (se 1 (by rfl) ⟨2063930, by rfl⟩ : syracuseStep 2751907 = 4127861) B4127861
theorem B1695139 : Blo 1693547 1695139 := bstep (se 1 (by rfl) ⟨1271354, by rfl⟩ : syracuseStep 1695139 = 2542709) B2542709
theorem B1695155 : Blo 1693547 1695155 := bstep (se 1 (by rfl) ⟨1271366, by rfl⟩ : syracuseStep 1695155 = 2542733) B2542733
theorem B1695171 : Blo 1693547 1695171 := bstep (se 1 (by rfl) ⟨1271378, by rfl⟩ : syracuseStep 1695171 = 2542757) B2542757
theorem B2858449 : Blo 1693547 2858449 := bstep (se 2 (by rfl) ⟨1071918, by rfl⟩ : syracuseStep 2858449 = 2143837) B2143837
theorem B3620305 : Blo 1693547 3620305 := bstep (se 2 (by rfl) ⟨1357614, by rfl⟩ : syracuseStep 3620305 = 2715229) B2715229
theorem B1695187 : Blo 1693547 1695187 := bstep (se 1 (by rfl) ⟨1271390, by rfl⟩ : syracuseStep 1695187 = 2542781) B2542781
theorem B1695203 : Blo 1693547 1695203 := bstep (se 1 (by rfl) ⟨1271402, by rfl⟩ : syracuseStep 1695203 = 2542805) B2542805
theorem B2858483 : Blo 1693547 2858483 := bstep (se 1 (by rfl) ⟨2143862, by rfl⟩ : syracuseStep 2858483 = 4287725) B4287725
theorem B1695219 : Blo 1693547 1695219 := bstep (se 1 (by rfl) ⟨1271414, by rfl⟩ : syracuseStep 1695219 = 2542829) B2542829
theorem B1695235 : Blo 1693547 1695235 := bstep (se 1 (by rfl) ⟨1271426, by rfl⟩ : syracuseStep 1695235 = 2542853) B2542853
theorem B1695251 : Blo 1693547 1695251 := bstep (se 1 (by rfl) ⟨1271438, by rfl⟩ : syracuseStep 1695251 = 2542877) B2542877
theorem B1695267 : Blo 1693547 1695267 := bstep (se 1 (by rfl) ⟨1271450, by rfl⟩ : syracuseStep 1695267 = 2542901) B2542901
theorem B1695283 : Blo 1693547 1695283 := bstep (se 1 (by rfl) ⟨1271462, by rfl⟩ : syracuseStep 1695283 = 2542925) B2542925
theorem B1695299 : Blo 1693547 1695299 := bstep (se 1 (by rfl) ⟨1271474, by rfl⟩ : syracuseStep 1695299 = 2542949) B2542949
theorem B1695315 : Blo 1693547 1695315 := bstep (se 1 (by rfl) ⟨1271486, by rfl⟩ : syracuseStep 1695315 = 2542973) B2542973
theorem B1695331 : Blo 1693547 1695331 := bstep (se 1 (by rfl) ⟨1271498, by rfl⟩ : syracuseStep 1695331 = 2542997) B2542997
theorem B2858611 : Blo 1693547 2858611 := bstep (se 1 (by rfl) ⟨2143958, by rfl⟩ : syracuseStep 2858611 = 4287917) B4287917
theorem B1695347 : Blo 1693547 1695347 := bstep (se 1 (by rfl) ⟨1271510, by rfl⟩ : syracuseStep 1695347 = 2543021) B2543021
theorem B1695363 : Blo 1693547 1695363 := bstep (se 1 (by rfl) ⟨1271522, by rfl⟩ : syracuseStep 1695363 = 2543045) B2543045
theorem B1695379 : Blo 1693547 1695379 := bstep (se 1 (by rfl) ⟨1271534, by rfl⟩ : syracuseStep 1695379 = 2543069) B2543069
theorem B1695395 : Blo 1693547 1695395 := bstep (se 1 (by rfl) ⟨1271546, by rfl⟩ : syracuseStep 1695395 = 2543093) B2543093
theorem B5717681 : Blo 1693547 5717681 := bstep (se 2 (by rfl) ⟨2144130, by rfl⟩ : syracuseStep 5717681 = 4288261) B4288261
theorem B1695411 : Blo 1693547 1695411 := bstep (se 1 (by rfl) ⟨1271558, by rfl⟩ : syracuseStep 1695411 = 2543117) B2543117
theorem B1695427 : Blo 1693547 1695427 := bstep (se 1 (by rfl) ⟨1271570, by rfl⟩ : syracuseStep 1695427 = 2543141) B2543141
theorem B4824785 : Blo 1693547 4824785 := bstep (se 2 (by rfl) ⟨1809294, by rfl⟩ : syracuseStep 4824785 = 3618589) B3618589
theorem B1695443 : Blo 1693547 1695443 := bstep (se 1 (by rfl) ⟨1271582, by rfl⟩ : syracuseStep 1695443 = 2543165) B2543165
theorem B1695459 : Blo 1693547 1695459 := bstep (se 1 (by rfl) ⟨1271594, by rfl⟩ : syracuseStep 1695459 = 2543189) B2543189
theorem B1695475 : Blo 1693547 1695475 := bstep (se 1 (by rfl) ⟨1271606, by rfl⟩ : syracuseStep 1695475 = 2543213) B2543213
theorem B2858753 : Blo 1693547 2858753 := bstep (se 2 (by rfl) ⟨1072032, by rfl⟩ : syracuseStep 2858753 = 2144065) B2144065
theorem B1695491 : Blo 1693547 1695491 := bstep (se 1 (by rfl) ⟨1271618, by rfl⟩ : syracuseStep 1695491 = 2543237) B2543237
theorem B9912077 : Blo 1693547 9912077 := bstep (se 3 (by rfl) ⟨1858514, by rfl⟩ : syracuseStep 9912077 = 3717029) B3717029
theorem B1695507 : Blo 1693547 1695507 := bstep (se 1 (by rfl) ⟨1271630, by rfl⟩ : syracuseStep 1695507 = 2543261) B2543261
theorem B9649955 : Blo 1693547 9649955 := bstep (se 1 (by rfl) ⟨7237466, by rfl⟩ : syracuseStep 9649955 = 14474933) B14474933
theorem B1695523 : Blo 1693547 1695523 := bstep (se 1 (by rfl) ⟨1271642, by rfl⟩ : syracuseStep 1695523 = 2543285) B2543285
theorem B1695539 : Blo 1693547 1695539 := bstep (se 1 (by rfl) ⟨1271654, by rfl⟩ : syracuseStep 1695539 = 2543309) B2543309
theorem B18579253 : Blo 1693547 18579253 := bstep (se 5 (by rfl) ⟨870902, by rfl⟩ : syracuseStep 18579253 = 1741805) B1741805
theorem B2858881 : Blo 1693547 2858881 := bstep (se 2 (by rfl) ⟨1072080, by rfl⟩ : syracuseStep 2858881 = 2144161) B2144161
theorem B7724963 : Blo 1693547 7724963 := bstep (se 1 (by rfl) ⟨5793722, by rfl⟩ : syracuseStep 7724963 = 11587445) B11587445
theorem B2858915 : Blo 1693547 2858915 := bstep (se 1 (by rfl) ⟨2144186, by rfl⟩ : syracuseStep 2858915 = 4288373) B4288373
theorem B5152675 : Blo 1693547 5152675 := bstep (se 1 (by rfl) ⟨3864506, by rfl⟩ : syracuseStep 5152675 = 7729013) B7729013
theorem B6430691 : Blo 1693547 6430691 := bstep (se 1 (by rfl) ⟨4823018, by rfl⟩ : syracuseStep 6430691 = 9646037) B9646037
theorem B3670039 : Blo 1693547 3670039 := bstep (se 1 (by rfl) ⟨2752529, by rfl⟩ : syracuseStep 3670039 = 5505059) B5505059
theorem B8577089 : Blo 1693547 8577089 := bstep (se 2 (by rfl) ⟨3216408, by rfl⟩ : syracuseStep 8577089 = 6432817) B6432817
theorem B2859097 : Blo 1693547 2859097 := bstep (se 2 (by rfl) ⟨1072161, by rfl⟩ : syracuseStep 2859097 = 2144323) B2144323
theorem B3260555 : Blo 1693547 3260555 := bstep (se 1 (by rfl) ⟨2445416, by rfl⟩ : syracuseStep 3260555 = 4890833) B4890833
theorem B5718167 : Blo 1693547 5718167 := bstep (se 1 (by rfl) ⟨4288625, by rfl⟩ : syracuseStep 5718167 = 8577251) B8577251
theorem B4825433 : Blo 1693547 4825433 := bstep (se 2 (by rfl) ⟨1809537, by rfl⟩ : syracuseStep 4825433 = 3619075) B3619075
theorem B4071883 : Blo 1693547 4071883 := bstep (se 1 (by rfl) ⟨3053912, by rfl⟩ : syracuseStep 4071883 = 6107825) B6107825
theorem B2859671 : Blo 1693547 2859671 := bstep (se 1 (by rfl) ⟨2144753, by rfl⟩ : syracuseStep 2859671 = 4289507) B4289507
theorem B5718707 : Blo 1693547 5718707 := bstep (se 1 (by rfl) ⟨4289030, by rfl⟩ : syracuseStep 5718707 = 8578061) B8578061
theorem B2859799 : Blo 1693547 2859799 := bstep (se 1 (by rfl) ⟨2144849, by rfl⟩ : syracuseStep 2859799 = 4289699) B4289699
theorem B12387107 : Blo 1693547 12387107 := bstep (se 1 (by rfl) ⟨9290330, by rfl⟩ : syracuseStep 12387107 = 18580661) B18580661
theorem B2540363 : Blo 1693547 2540363 := bstep (se 1 (by rfl) ⟨1905272, by rfl⟩ : syracuseStep 2540363 = 3810545) B3810545
theorem B2540375 : Blo 1693547 2540375 := bstep (se 1 (by rfl) ⟨1905281, by rfl⟩ : syracuseStep 2540375 = 3810563) B3810563
theorem B25109365 : Blo 1693547 25109365 := bstep (se 5 (by rfl) ⟨1177001, by rfl⟩ : syracuseStep 25109365 = 2354003) B2354003
theorem B6431633 : Blo 1693547 6431633 := bstep (se 2 (by rfl) ⟨2411862, by rfl⟩ : syracuseStep 6431633 = 4823725) B4823725
theorem B9651095 : Blo 1693547 9651095 := bstep (se 1 (by rfl) ⟨7238321, by rfl⟩ : syracuseStep 9651095 = 14476643) B14476643
theorem B2540441 : Blo 1693547 2540441 := bstep (se 2 (by rfl) ⟨952665, by rfl⟩ : syracuseStep 2540441 = 1905331) B1905331
theorem B5718977 : Blo 1693547 5718977 := bstep (se 2 (by rfl) ⟨2144616, by rfl⟩ : syracuseStep 5718977 = 4289233) B4289233
theorem B2540555 : Blo 1693547 2540555 := bstep (se 1 (by rfl) ⟨1905416, by rfl⟩ : syracuseStep 2540555 = 3810833) B3810833
theorem B2540567 : Blo 1693547 2540567 := bstep (se 1 (by rfl) ⟨1905425, by rfl⟩ : syracuseStep 2540567 = 3810851) B3810851
theorem B5153843 : Blo 1693547 5153843 := bstep (se 1 (by rfl) ⟨3865382, by rfl⟩ : syracuseStep 5153843 = 7730765) B7730765
theorem B2540633 : Blo 1693547 2540633 := bstep (se 2 (by rfl) ⟨952737, by rfl⟩ : syracuseStep 2540633 = 1905475) B1905475
theorem B7234733 : Blo 1693547 7234733 := bstep (se 3 (by rfl) ⟨1356512, by rfl⟩ : syracuseStep 7234733 = 2713025) B2713025
theorem B2540747 : Blo 1693547 2540747 := bstep (se 1 (by rfl) ⟨1905560, by rfl⟩ : syracuseStep 2540747 = 3811121) B3811121
theorem B2540759 : Blo 1693547 2540759 := bstep (se 1 (by rfl) ⟨1905569, by rfl⟩ : syracuseStep 2540759 = 3811139) B3811139
theorem B2540825 : Blo 1693547 2540825 := bstep (se 2 (by rfl) ⟨952809, by rfl⟩ : syracuseStep 2540825 = 1905619) B1905619
theorem B7726387 : Blo 1693547 7726387 := bstep (se 1 (by rfl) ⟨5794790, by rfl⟩ : syracuseStep 7726387 = 11589581) B11589581
theorem B3810635 : Blo 1693547 3810635 := bstep (se 1 (by rfl) ⟨2857976, by rfl⟩ : syracuseStep 3810635 = 5715953) B5715953
theorem B3810689 : Blo 1693547 3810689 := bstep (se 2 (by rfl) ⟨1429008, by rfl⟩ : syracuseStep 3810689 = 2858017) B2858017
theorem B2540939 : Blo 1693547 2540939 := bstep (se 1 (by rfl) ⟨1905704, by rfl⟩ : syracuseStep 2540939 = 3811409) B3811409
theorem B2860427 : Blo 1693547 2860427 := bstep (se 1 (by rfl) ⟨2145320, by rfl⟩ : syracuseStep 2860427 = 4290641) B4290641
theorem B2540951 : Blo 1693547 2540951 := bstep (se 1 (by rfl) ⟨1905713, by rfl⟩ : syracuseStep 2540951 = 3811427) B3811427
theorem B2541017 : Blo 1693547 2541017 := bstep (se 2 (by rfl) ⟨952881, by rfl⟩ : syracuseStep 2541017 = 1905763) B1905763
theorem B5719517 : Blo 1693547 5719517 := bstep (se 3 (by rfl) ⟨1072409, by rfl⟩ : syracuseStep 5719517 = 2144819) B2144819
theorem B7235075 : Blo 1693547 7235075 := bstep (se 1 (by rfl) ⟨5426306, by rfl⟩ : syracuseStep 7235075 = 10852613) B10852613
theorem B2860555 : Blo 1693547 2860555 := bstep (se 1 (by rfl) ⟨2145416, by rfl⟩ : syracuseStep 2860555 = 4290833) B4290833
theorem B19293713 : Blo 1693547 19293713 := bstep (se 2 (by rfl) ⟨7235142, by rfl⟩ : syracuseStep 19293713 = 14470285) B14470285
theorem B2541131 : Blo 1693547 2541131 := bstep (se 1 (by rfl) ⟨1905848, by rfl⟩ : syracuseStep 2541131 = 3811697) B3811697
theorem B6432331 : Blo 1693547 6432331 := bstep (se 1 (by rfl) ⟨4824248, by rfl⟩ : syracuseStep 6432331 = 9648497) B9648497
theorem B4826699 : Blo 1693547 4826699 := bstep (se 1 (by rfl) ⟨3620024, by rfl⟩ : syracuseStep 4826699 = 7240049) B7240049
theorem B2541143 : Blo 1693547 2541143 := bstep (se 1 (by rfl) ⟨1905857, by rfl⟩ : syracuseStep 2541143 = 3811715) B3811715
theorem B3810905 : Blo 1693547 3810905 := bstep (se 2 (by rfl) ⟨1429089, by rfl⟩ : syracuseStep 3810905 = 2858179) B2858179
theorem B2541209 : Blo 1693547 2541209 := bstep (se 2 (by rfl) ⟨952953, by rfl⟩ : syracuseStep 2541209 = 1905907) B1905907
theorem B2860697 : Blo 1693547 2860697 := bstep (se 2 (by rfl) ⟨1072761, by rfl⟩ : syracuseStep 2860697 = 2145523) B2145523
theorem B3810995 : Blo 1693547 3810995 := bstep (se 1 (by rfl) ⟨2858246, by rfl⟩ : syracuseStep 3810995 = 5716493) B5716493
theorem B3811031 : Blo 1693547 3811031 := bstep (se 1 (by rfl) ⟨2858273, by rfl⟩ : syracuseStep 3811031 = 5716547) B5716547
theorem B2541323 : Blo 1693547 2541323 := bstep (se 1 (by rfl) ⟨1905992, by rfl⟩ : syracuseStep 2541323 = 3811985) B3811985
theorem B2541335 : Blo 1693547 2541335 := bstep (se 1 (by rfl) ⟨1906001, by rfl⟩ : syracuseStep 2541335 = 3812003) B3812003
theorem B2860825 : Blo 1693547 2860825 := bstep (se 2 (by rfl) ⟨1072809, by rfl⟩ : syracuseStep 2860825 = 2145619) B2145619
theorem B4073267 : Blo 1693547 4073267 := bstep (se 1 (by rfl) ⟨3054950, by rfl⟩ : syracuseStep 4073267 = 6109901) B6109901
theorem B2541401 : Blo 1693547 2541401 := bstep (se 2 (by rfl) ⟨953025, by rfl⟩ : syracuseStep 2541401 = 1906051) B1906051
theorem B6432605 : Blo 1693547 6432605 := bstep (se 3 (by rfl) ⟨1206113, by rfl⟩ : syracuseStep 6432605 = 2412227) B2412227
theorem B3811211 : Blo 1693547 3811211 := bstep (se 1 (by rfl) ⟨2858408, by rfl⟩ : syracuseStep 3811211 = 5716817) B5716817
theorem B21718961 : Blo 1693547 21718961 := bstep (se 2 (by rfl) ⟨8144610, by rfl⟩ : syracuseStep 21718961 = 16289221) B16289221
theorem B3811265 : Blo 1693547 3811265 := bstep (se 2 (by rfl) ⟨1429224, by rfl⟩ : syracuseStep 3811265 = 2858449) B2858449
theorem B2541515 : Blo 1693547 2541515 := bstep (se 1 (by rfl) ⟨1906136, by rfl⟩ : syracuseStep 2541515 = 3812273) B3812273
theorem B2541527 : Blo 1693547 2541527 := bstep (se 1 (by rfl) ⟨1906145, by rfl⟩ : syracuseStep 2541527 = 3812291) B3812291
theorem B8579033 : Blo 1693547 8579033 := bstep (se 2 (by rfl) ⟨3217137, by rfl⟩ : syracuseStep 8579033 = 6434275) B6434275
theorem B2541593 : Blo 1693547 2541593 := bstep (se 2 (by rfl) ⟨953097, by rfl⟩ : syracuseStep 2541593 = 1906195) B1906195
theorem B6522925 : Blo 1693547 6522925 := bstep (se 3 (by rfl) ⟨1223048, by rfl⟩ : syracuseStep 6522925 = 2446097) B2446097
theorem B2541707 : Blo 1693547 2541707 := bstep (se 1 (by rfl) ⟨1906280, by rfl⟩ : syracuseStep 2541707 = 3812561) B3812561
theorem B6867089 : Blo 1693547 6867089 := bstep (se 2 (by rfl) ⟨2575158, by rfl⟩ : syracuseStep 6867089 = 5150317) B5150317
theorem B2541719 : Blo 1693547 2541719 := bstep (se 1 (by rfl) ⟨1906289, by rfl⟩ : syracuseStep 2541719 = 3812579) B3812579
theorem B10307735 : Blo 1693547 10307735 := bstep (se 1 (by rfl) ⟨7730801, by rfl⟩ : syracuseStep 10307735 = 15461603) B15461603
theorem B3811481 : Blo 1693547 3811481 := bstep (se 2 (by rfl) ⟨1429305, by rfl⟩ : syracuseStep 3811481 = 2858611) B2858611
theorem B2541785 : Blo 1693547 2541785 := bstep (se 2 (by rfl) ⟨953169, by rfl⟩ : syracuseStep 2541785 = 1906339) B1906339
theorem B3811571 : Blo 1693547 3811571 := bstep (se 1 (by rfl) ⟨2858678, by rfl⟩ : syracuseStep 3811571 = 5717357) B5717357
theorem B3811607 : Blo 1693547 3811607 := bstep (se 1 (by rfl) ⟨2858705, by rfl⟩ : syracuseStep 3811607 = 5717411) B5717411
theorem B2541899 : Blo 1693547 2541899 := bstep (se 1 (by rfl) ⟨1906424, by rfl⟩ : syracuseStep 2541899 = 3812849) B3812849
theorem B2541911 : Blo 1693547 2541911 := bstep (se 1 (by rfl) ⟨1906433, by rfl⟩ : syracuseStep 2541911 = 3812867) B3812867
theorem B7440785 : Blo 1693547 7440785 := bstep (se 2 (by rfl) ⟨2790294, by rfl⟩ : syracuseStep 7440785 = 5580589) B5580589
theorem B2541977 : Blo 1693547 2541977 := bstep (se 2 (by rfl) ⟨953241, by rfl⟩ : syracuseStep 2541977 = 1906483) B1906483
theorem B3811787 : Blo 1693547 3811787 := bstep (se 1 (by rfl) ⟨2858840, by rfl⟩ : syracuseStep 3811787 = 5717681) B5717681
theorem B3811841 : Blo 1693547 3811841 := bstep (se 2 (by rfl) ⟨1429440, by rfl⟩ : syracuseStep 3811841 = 2858881) B2858881
theorem B2542091 : Blo 1693547 2542091 := bstep (se 1 (by rfl) ⟨1906568, by rfl⟩ : syracuseStep 2542091 = 3813137) B3813137
theorem B6433303 : Blo 1693547 6433303 := bstep (se 1 (by rfl) ⟨4824977, by rfl⟩ : syracuseStep 6433303 = 9649955) B9649955
theorem B2542103 : Blo 1693547 2542103 := bstep (se 1 (by rfl) ⟨1906577, by rfl⟩ : syracuseStep 2542103 = 3813155) B3813155
theorem B5720651 : Blo 1693547 5720651 := bstep (se 1 (by rfl) ⟨4290488, by rfl⟩ : syracuseStep 5720651 = 8580977) B8580977
theorem B2542169 : Blo 1693547 2542169 := bstep (se 2 (by rfl) ⟨953313, by rfl⟩ : syracuseStep 2542169 = 1906627) B1906627
theorem B4287127 : Blo 1693547 4287127 := bstep (se 1 (by rfl) ⟨3215345, by rfl⟩ : syracuseStep 4287127 = 6430691) B6430691
theorem B2542283 : Blo 1693547 2542283 := bstep (se 1 (by rfl) ⟨1906712, by rfl⟩ : syracuseStep 2542283 = 3813425) B3813425
theorem B2542295 : Blo 1693547 2542295 := bstep (se 1 (by rfl) ⟨1906721, by rfl⟩ : syracuseStep 2542295 = 3813443) B3813443
theorem B3812057 : Blo 1693547 3812057 := bstep (se 2 (by rfl) ⟨1429521, by rfl⟩ : syracuseStep 3812057 = 2859043) B2859043
theorem B2542361 : Blo 1693547 2542361 := bstep (se 2 (by rfl) ⟨953385, by rfl⟩ : syracuseStep 2542361 = 1906771) B1906771
theorem B3812147 : Blo 1693547 3812147 := bstep (se 1 (by rfl) ⟨2859110, by rfl⟩ : syracuseStep 3812147 = 5718221) B5718221
theorem B3812183 : Blo 1693547 3812183 := bstep (se 1 (by rfl) ⟨2859137, by rfl⟩ : syracuseStep 3812183 = 5718275) B5718275
theorem B5720921 : Blo 1693547 5720921 := bstep (se 2 (by rfl) ⟨2145345, by rfl⟩ : syracuseStep 5720921 = 4290691) B4290691
theorem B2542475 : Blo 1693547 2542475 := bstep (se 1 (by rfl) ⟨1906856, by rfl⟩ : syracuseStep 2542475 = 3813713) B3813713
theorem B2542487 : Blo 1693547 2542487 := bstep (se 1 (by rfl) ⟨1906865, by rfl⟩ : syracuseStep 2542487 = 3813731) B3813731
theorem B21719987 : Blo 1693547 21719987 := bstep (se 1 (by rfl) ⟨16289990, by rfl⟩ : syracuseStep 21719987 = 32579981) B32579981
theorem B2542553 : Blo 1693547 2542553 := bstep (se 2 (by rfl) ⟨953457, by rfl⟩ : syracuseStep 2542553 = 1906915) B1906915
theorem B3812363 : Blo 1693547 3812363 := bstep (se 1 (by rfl) ⟨2859272, by rfl⟩ : syracuseStep 3812363 = 5718545) B5718545
theorem B3812417 : Blo 1693547 3812417 := bstep (se 2 (by rfl) ⟨1429656, by rfl⟩ : syracuseStep 3812417 = 2859313) B2859313
theorem B4287563 : Blo 1693547 4287563 := bstep (se 1 (by rfl) ⟨3215672, by rfl⟩ : syracuseStep 4287563 = 6431345) B6431345
theorem B2542667 : Blo 1693547 2542667 := bstep (se 1 (by rfl) ⟨1907000, by rfl⟩ : syracuseStep 2542667 = 3814001) B3814001
theorem B2542679 : Blo 1693547 2542679 := bstep (se 1 (by rfl) ⟨1907009, by rfl⟩ : syracuseStep 2542679 = 3814019) B3814019
theorem B6868061 : Blo 1693547 6868061 := bstep (se 3 (by rfl) ⟨1287761, by rfl⟩ : syracuseStep 6868061 = 2575523) B2575523
theorem B2542745 : Blo 1693547 2542745 := bstep (se 2 (by rfl) ⟨953529, by rfl⟩ : syracuseStep 2542745 = 1907059) B1907059
theorem B46402741 : Blo 1693547 46402741 := bstep (se 5 (by rfl) ⟨2175128, by rfl⟩ : syracuseStep 46402741 = 4350257) B4350257
theorem B2542859 : Blo 1693547 2542859 := bstep (se 1 (by rfl) ⟨1907144, by rfl⟩ : syracuseStep 2542859 = 3814289) B3814289
theorem B2542871 : Blo 1693547 2542871 := bstep (se 1 (by rfl) ⟨1907153, by rfl⟩ : syracuseStep 2542871 = 3814307) B3814307
theorem B3812633 : Blo 1693547 3812633 := bstep (se 2 (by rfl) ⟨1429737, by rfl⟩ : syracuseStep 3812633 = 2859475) B2859475
theorem B6434093 : Blo 1693547 6434093 := bstep (se 3 (by rfl) ⟨1206392, by rfl⟩ : syracuseStep 6434093 = 2412785) B2412785
theorem B18320705 : Blo 1693547 18320705 := bstep (se 2 (by rfl) ⟨6870264, by rfl⟩ : syracuseStep 18320705 = 13740529) B13740529
theorem B2411851 : Blo 1693547 2411851 := bstep (se 1 (by rfl) ⟨1808888, by rfl⟩ : syracuseStep 2411851 = 3617777) B3617777
theorem B9653579 : Blo 1693547 9653579 := bstep (se 1 (by rfl) ⟨7240184, by rfl⟩ : syracuseStep 9653579 = 14480369) B14480369
theorem B2542937 : Blo 1693547 2542937 := bstep (se 2 (by rfl) ⟨953601, by rfl⟩ : syracuseStep 2542937 = 1907203) B1907203
theorem B3812723 : Blo 1693547 3812723 := bstep (se 1 (by rfl) ⟨2859542, by rfl⟩ : syracuseStep 3812723 = 5719085) B5719085
theorem B52170101 : Blo 1693547 52170101 := bstep (se 5 (by rfl) ⟨2445473, by rfl⟩ : syracuseStep 52170101 = 4890947) B4890947
theorem B3812759 : Blo 1693547 3812759 := bstep (se 1 (by rfl) ⟨2859569, by rfl⟩ : syracuseStep 3812759 = 5719139) B5719139
theorem B4287937 : Blo 1693547 4287937 := bstep (se 2 (by rfl) ⟨1607976, by rfl⟩ : syracuseStep 4287937 = 3215953) B3215953
theorem B2543051 : Blo 1693547 2543051 := bstep (se 1 (by rfl) ⟨1907288, by rfl⟩ : syracuseStep 2543051 = 3814577) B3814577
theorem B2543063 : Blo 1693547 2543063 := bstep (se 1 (by rfl) ⟨1907297, by rfl⟩ : syracuseStep 2543063 = 3814595) B3814595
theorem B5721623 : Blo 1693547 5721623 := bstep (se 1 (by rfl) ⟨4291217, by rfl⟩ : syracuseStep 5721623 = 8582435) B8582435
theorem B2543129 : Blo 1693547 2543129 := bstep (se 2 (by rfl) ⟨953673, by rfl⟩ : syracuseStep 2543129 = 1907347) B1907347
theorem B8580653 : Blo 1693547 8580653 := bstep (se 3 (by rfl) ⟨1608872, by rfl⟩ : syracuseStep 8580653 = 3217745) B3217745
theorem B3812939 : Blo 1693547 3812939 := bstep (se 1 (by rfl) ⟨2859704, by rfl⟩ : syracuseStep 3812939 = 5719409) B5719409
theorem B2412119 : Blo 1693547 2412119 := bstep (se 1 (by rfl) ⟨1809089, by rfl⟩ : syracuseStep 2412119 = 3618179) B3618179
theorem B3812993 : Blo 1693547 3812993 := bstep (se 2 (by rfl) ⟨1429872, by rfl⟩ : syracuseStep 3812993 = 2859745) B2859745
theorem B2715275 : Blo 1693547 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B2543243 : Blo 1693547 2543243 := bstep (se 1 (by rfl) ⟨1907432, by rfl⟩ : syracuseStep 2543243 = 3814865) B3814865
theorem B2543255 : Blo 1693547 2543255 := bstep (se 1 (by rfl) ⟨1907441, by rfl⟩ : syracuseStep 2543255 = 3814883) B3814883
theorem B2543321 : Blo 1693547 2543321 := bstep (se 2 (by rfl) ⟨953745, by rfl⟩ : syracuseStep 2543321 = 1907491) B1907491
theorem B7237451 : Blo 1693547 7237451 := bstep (se 1 (by rfl) ⟨5428088, by rfl⟩ : syracuseStep 7237451 = 10856177) B10856177
theorem B14126923 : Blo 1693547 14126923 := bstep (se 1 (by rfl) ⟨10595192, by rfl⟩ : syracuseStep 14126923 = 21190385) B21190385
theorem B3813209 : Blo 1693547 3813209 := bstep (se 2 (by rfl) ⟨1429953, by rfl⟩ : syracuseStep 3813209 = 2859907) B2859907
theorem B2289559 : Blo 1693547 2289559 := bstep (se 1 (by rfl) ⟨1717169, by rfl⟩ : syracuseStep 2289559 = 3434339) B3434339
theorem B3813299 : Blo 1693547 3813299 := bstep (se 1 (by rfl) ⟨2859974, by rfl⟩ : syracuseStep 3813299 = 5719949) B5719949
theorem B3813335 : Blo 1693547 3813335 := bstep (se 1 (by rfl) ⟨2860001, by rfl⟩ : syracuseStep 3813335 = 5720003) B5720003
theorem B4288535 : Blo 1693547 4288535 := bstep (se 1 (by rfl) ⟨3216401, by rfl⟩ : syracuseStep 4288535 = 6432803) B6432803
theorem B5722163 : Blo 1693547 5722163 := bstep (se 1 (by rfl) ⟨4291622, by rfl⟩ : syracuseStep 5722163 = 8583245) B8583245
theorem B14471243 : Blo 1693547 14471243 := bstep (se 1 (by rfl) ⟨10853432, by rfl⟩ : syracuseStep 14471243 = 21706865) B21706865
theorem B6525017 : Blo 1693547 6525017 := bstep (se 2 (by rfl) ⟨2446881, by rfl⟩ : syracuseStep 6525017 = 4893763) B4893763
theorem B3813515 : Blo 1693547 3813515 := bstep (se 1 (by rfl) ⟨2860136, by rfl⟩ : syracuseStep 3813515 = 5720273) B5720273
theorem B3215513 : Blo 1693547 3215513 := bstep (se 2 (by rfl) ⟨1205817, by rfl⟩ : syracuseStep 3215513 = 2411635) B2411635
theorem B3813569 : Blo 1693547 3813569 := bstep (se 2 (by rfl) ⟨1430088, by rfl⟩ : syracuseStep 3813569 = 2860177) B2860177
theorem B3436787 : Blo 1693547 3436787 := bstep (se 1 (by rfl) ⟨2577590, by rfl⟩ : syracuseStep 3436787 = 5155181) B5155181
theorem B5722433 : Blo 1693547 5722433 := bstep (se 2 (by rfl) ⟨2145912, by rfl⟩ : syracuseStep 5722433 = 4291825) B4291825
theorem B3617111 : Blo 1693547 3617111 := bstep (se 1 (by rfl) ⟨2712833, by rfl⟩ : syracuseStep 3617111 = 5425667) B5425667
theorem B3051865 : Blo 1693547 3051865 := bstep (se 2 (by rfl) ⟨1144449, by rfl⟩ : syracuseStep 3051865 = 2288899) B2288899
theorem B18313573 : Blo 1693547 18313573 := bstep (se 4 (by rfl) ⟨1716897, by rfl⟩ : syracuseStep 18313573 = 3433795) B3433795
theorem B19296629 : Blo 1693547 19296629 := bstep (se 5 (by rfl) ⟨904529, by rfl⟩ : syracuseStep 19296629 = 1809059) B1809059
theorem B3813785 : Blo 1693547 3813785 := bstep (se 2 (by rfl) ⟨1430169, by rfl⟩ : syracuseStep 3813785 = 2860339) B2860339
theorem B6525377 : Blo 1693547 6525377 := bstep (se 2 (by rfl) ⟨2447016, by rfl⟩ : syracuseStep 6525377 = 4894033) B4894033
theorem B3813875 : Blo 1693547 3813875 := bstep (se 1 (by rfl) ⟨2860406, by rfl⟩ : syracuseStep 3813875 = 5720813) B5720813
theorem B6107651 : Blo 1693547 6107651 := bstep (se 1 (by rfl) ⟨4580738, by rfl⟩ : syracuseStep 6107651 = 9161477) B9161477
theorem B3617291 : Blo 1693547 3617291 := bstep (se 1 (by rfl) ⟨2712968, by rfl⟩ : syracuseStep 3617291 = 5425937) B5425937
theorem B3813911 : Blo 1693547 3813911 := bstep (se 1 (by rfl) ⟨2860433, by rfl⟩ : syracuseStep 3813911 = 5720867) B5720867
theorem B2413081 : Blo 1693547 2413081 := bstep (se 2 (by rfl) ⟨904905, by rfl⟩ : syracuseStep 2413081 = 1809811) B1809811
theorem B16282147 : Blo 1693547 16282147 := bstep (se 1 (by rfl) ⟨12211610, by rfl⟩ : syracuseStep 16282147 = 24423221) B24423221
theorem B1905259 : Blo 1693547 1905259 := bstep (se 1 (by rfl) ⟨1428944, by rfl⟩ : syracuseStep 1905259 = 2857889) B2857889
theorem B3052147 : Blo 1693547 3052147 := bstep (se 1 (by rfl) ⟨2289110, by rfl⟩ : syracuseStep 3052147 = 4578221) B4578221
theorem B21189251 : Blo 1693547 21189251 := bstep (se 1 (by rfl) ⟨15891938, by rfl⟩ : syracuseStep 21189251 = 31783877) B31783877
theorem B3052183 : Blo 1693547 3052183 := bstep (se 1 (by rfl) ⟨2289137, by rfl⟩ : syracuseStep 3052183 = 4578275) B4578275
theorem B6435521 : Blo 1693547 6435521 := bstep (se 2 (by rfl) ⟨2413320, by rfl⟩ : syracuseStep 6435521 = 4826641) B4826641
theorem B3814091 : Blo 1693547 3814091 := bstep (se 1 (by rfl) ⟨2860568, by rfl⟩ : syracuseStep 3814091 = 5721137) B5721137
theorem B1905367 : Blo 1693547 1905367 := bstep (se 1 (by rfl) ⟨1429025, by rfl⟩ : syracuseStep 1905367 = 2858051) B2858051
theorem B3814145 : Blo 1693547 3814145 := bstep (se 2 (by rfl) ⟨1430304, by rfl⟩ : syracuseStep 3814145 = 2860609) B2860609
theorem B7238423 : Blo 1693547 7238423 := bstep (se 1 (by rfl) ⟨5428817, by rfl⟩ : syracuseStep 7238423 = 10857635) B10857635
theorem B4289345 : Blo 1693547 4289345 := bstep (se 2 (by rfl) ⟨1608504, by rfl⟩ : syracuseStep 4289345 = 3217009) B3217009
theorem B3216257 : Blo 1693547 3216257 := bstep (se 2 (by rfl) ⟨1206096, by rfl⟩ : syracuseStep 3216257 = 2412193) B2412193
theorem B1905547 : Blo 1693547 1905547 := bstep (se 1 (by rfl) ⟨1429160, by rfl⟩ : syracuseStep 1905547 = 2858321) B2858321
theorem B3814361 : Blo 1693547 3814361 := bstep (se 2 (by rfl) ⟨1430385, by rfl⟩ : syracuseStep 3814361 = 2860771) B2860771
theorem B3863539 : Blo 1693547 3863539 := bstep (se 1 (by rfl) ⟨2897654, by rfl⟩ : syracuseStep 3863539 = 5795309) B5795309
theorem B1905655 : Blo 1693547 1905655 := bstep (se 1 (by rfl) ⟨1429241, by rfl⟩ : syracuseStep 1905655 = 2858483) B2858483
theorem B3814451 : Blo 1693547 3814451 := bstep (se 1 (by rfl) ⟨2860838, by rfl⟩ : syracuseStep 3814451 = 5721677) B5721677
theorem B3814487 : Blo 1693547 3814487 := bstep (se 1 (by rfl) ⟨2860865, by rfl⟩ : syracuseStep 3814487 = 5721731) B5721731
theorem B3216523 : Blo 1693547 3216523 := bstep (se 1 (by rfl) ⟨2412392, by rfl⟩ : syracuseStep 3216523 = 4824785) B4824785
theorem B1905835 : Blo 1693547 1905835 := bstep (se 1 (by rfl) ⟨1429376, by rfl⟩ : syracuseStep 1905835 = 2858753) B2858753
theorem B6608051 : Blo 1693547 6608051 := bstep (se 1 (by rfl) ⟨4956038, by rfl⟩ : syracuseStep 6608051 = 9912077) B9912077
theorem B6870233 : Blo 1693547 6870233 := bstep (se 2 (by rfl) ⟨2576337, by rfl⟩ : syracuseStep 6870233 = 5152675) B5152675
theorem B3814667 : Blo 1693547 3814667 := bstep (se 1 (by rfl) ⟨2861000, by rfl⟩ : syracuseStep 3814667 = 5722001) B5722001
theorem B5149975 : Blo 1693547 5149975 := bstep (se 1 (by rfl) ⟨3862481, by rfl⟩ : syracuseStep 5149975 = 7724963) B7724963
theorem B1905943 : Blo 1693547 1905943 := bstep (se 1 (by rfl) ⟨1429457, by rfl⟩ : syracuseStep 1905943 = 2858915) B2858915
theorem B3814721 : Blo 1693547 3814721 := bstep (se 2 (by rfl) ⟨1430520, by rfl⟩ : syracuseStep 3814721 = 2861041) B2861041
theorem B4289881 : Blo 1693547 4289881 := bstep (se 2 (by rfl) ⟨1608705, by rfl⟩ : syracuseStep 4289881 = 3217411) B3217411
theorem B7239091 : Blo 1693547 7239091 := bstep (se 1 (by rfl) ⟨5429318, by rfl⟩ : syracuseStep 7239091 = 10858637) B10858637
theorem B1906123 : Blo 1693547 1906123 := bstep (se 1 (by rfl) ⟨1429592, by rfl⟩ : syracuseStep 1906123 = 2859185) B2859185
theorem B3814937 : Blo 1693547 3814937 := bstep (se 2 (by rfl) ⟨1430601, by rfl⟩ : syracuseStep 3814937 = 2861203) B2861203
theorem B23828003 : Blo 1693547 23828003 := bstep (se 1 (by rfl) ⟨17871002, by rfl⟩ : syracuseStep 23828003 = 35742005) B35742005
theorem B1906231 : Blo 1693547 1906231 := bstep (se 1 (by rfl) ⟨1429673, by rfl⟩ : syracuseStep 1906231 = 2859347) B2859347
theorem B24475205 : Blo 1693547 24475205 := bstep (se 4 (by rfl) ⟨2294550, by rfl⟩ : syracuseStep 24475205 = 4589101) B4589101
theorem B3216971 : Blo 1693547 3216971 := bstep (se 1 (by rfl) ⟨2412728, by rfl⟩ : syracuseStep 3216971 = 4825457) B4825457
theorem B24770123 : Blo 1693547 24770123 := bstep (se 1 (by rfl) ⟨18577592, by rfl⟩ : syracuseStep 24770123 = 37155185) B37155185
theorem B12383837 : Blo 1693547 12383837 := bstep (se 3 (by rfl) ⟨2321969, by rfl⟩ : syracuseStep 12383837 = 4643939) B4643939
theorem B9647747 : Blo 1693547 9647747 := bstep (se 1 (by rfl) ⟨7235810, by rfl⟩ : syracuseStep 9647747 = 14471621) B14471621
theorem B12211843 : Blo 1693547 12211843 := bstep (se 1 (by rfl) ⟨9158882, by rfl⟩ : syracuseStep 12211843 = 18317765) B18317765
theorem B3053207 : Blo 1693547 3053207 := bstep (se 1 (by rfl) ⟨2289905, by rfl⟩ : syracuseStep 3053207 = 4579811) B4579811
theorem B3053249 : Blo 1693547 3053249 := bstep (se 2 (by rfl) ⟨1144968, by rfl⟩ : syracuseStep 3053249 = 2289937) B2289937
theorem B6518489 : Blo 1693547 6518489 := bstep (se 2 (by rfl) ⟨2444433, by rfl⟩ : syracuseStep 6518489 = 4888867) B4888867
theorem B1906411 : Blo 1693547 1906411 := bstep (se 1 (by rfl) ⟨1429808, by rfl⟩ : syracuseStep 1906411 = 2859617) B2859617
theorem B27481841 : Blo 1693547 27481841 := bstep (se 2 (by rfl) ⟨10305690, by rfl⟩ : syracuseStep 27481841 = 20611381) B20611381
theorem B3217153 : Blo 1693547 3217153 := bstep (se 2 (by rfl) ⟨1206432, by rfl⟩ : syracuseStep 3217153 = 2412865) B2412865
theorem B26449669 : Blo 1693547 26449669 := bstep (se 4 (by rfl) ⟨2479656, by rfl⟩ : syracuseStep 26449669 = 4959313) B4959313
theorem B6108979 : Blo 1693547 6108979 := bstep (se 1 (by rfl) ⟨4581734, by rfl⟩ : syracuseStep 6108979 = 9163469) B9163469
theorem B1906519 : Blo 1693547 1906519 := bstep (se 1 (by rfl) ⟨1429889, by rfl⟩ : syracuseStep 1906519 = 2859779) B2859779
theorem B1693547 : Blo 1693547 1693547 := bstep (se 1 (by rfl) ⟨1270160, by rfl⟩ : syracuseStep 1693547 = 2540321) B2540321
theorem B1693559 : Blo 1693547 1693559 := bstep (se 1 (by rfl) ⟨1270169, by rfl⟩ : syracuseStep 1693559 = 2540339) B2540339
theorem B14112643 : Blo 1693547 14112643 := bstep (se 1 (by rfl) ⟨10584482, by rfl⟩ : syracuseStep 14112643 = 21168965) B21168965
theorem B1693579 : Blo 1693547 1693579 := bstep (se 1 (by rfl) ⟨1270184, by rfl⟩ : syracuseStep 1693579 = 2540369) B2540369
theorem B1693591 : Blo 1693547 1693591 := bstep (se 1 (by rfl) ⟨1270193, by rfl⟩ : syracuseStep 1693591 = 2540387) B2540387
theorem B1693611 : Blo 1693547 1693611 := bstep (se 1 (by rfl) ⟨1270208, by rfl⟩ : syracuseStep 1693611 = 2540417) B2540417
theorem B9656243 : Blo 1693547 9656243 := bstep (se 1 (by rfl) ⟨7242182, by rfl⟩ : syracuseStep 9656243 = 14484365) B14484365
theorem B1693623 : Blo 1693547 1693623 := bstep (se 1 (by rfl) ⟨1270217, by rfl⟩ : syracuseStep 1693623 = 2540435) B2540435
theorem B1693643 : Blo 1693547 1693643 := bstep (se 1 (by rfl) ⟨1270232, by rfl⟩ : syracuseStep 1693643 = 2540465) B2540465
theorem B5576651 : Blo 1693547 5576651 := bstep (se 1 (by rfl) ⟨4182488, by rfl⟩ : syracuseStep 5576651 = 8364977) B8364977
theorem B1693655 : Blo 1693547 1693655 := bstep (se 1 (by rfl) ⟨1270241, by rfl⟩ : syracuseStep 1693655 = 2540483) B2540483
theorem B1693675 : Blo 1693547 1693675 := bstep (se 1 (by rfl) ⟨1270256, by rfl⟩ : syracuseStep 1693675 = 2540513) B2540513
theorem B1693687 : Blo 1693547 1693687 := bstep (se 1 (by rfl) ⟨1270265, by rfl⟩ : syracuseStep 1693687 = 2540531) B2540531
theorem B1693707 : Blo 1693547 1693707 := bstep (se 1 (by rfl) ⟨1270280, by rfl⟩ : syracuseStep 1693707 = 2540561) B2540561
theorem B1906699 : Blo 1693547 1906699 := bstep (se 1 (by rfl) ⟨1430024, by rfl⟩ : syracuseStep 1906699 = 2860049) B2860049
theorem B1693719 : Blo 1693547 1693719 := bstep (se 1 (by rfl) ⟨1270289, by rfl⟩ : syracuseStep 1693719 = 2540579) B2540579
theorem B1693739 : Blo 1693547 1693739 := bstep (se 1 (by rfl) ⟨1270304, by rfl⟩ : syracuseStep 1693739 = 2540609) B2540609
theorem B1693751 : Blo 1693547 1693751 := bstep (se 1 (by rfl) ⟨1270313, by rfl⟩ : syracuseStep 1693751 = 2540627) B2540627
theorem B1693771 : Blo 1693547 1693771 := bstep (se 1 (by rfl) ⟨1270328, by rfl⟩ : syracuseStep 1693771 = 2540657) B2540657
theorem B1693783 : Blo 1693547 1693783 := bstep (se 1 (by rfl) ⟨1270337, by rfl⟩ : syracuseStep 1693783 = 2540675) B2540675
theorem B3217495 : Blo 1693547 3217495 := bstep (se 1 (by rfl) ⟨2413121, by rfl⟩ : syracuseStep 3217495 = 4826243) B4826243
theorem B5716061 : Blo 1693547 5716061 := bstep (se 3 (by rfl) ⟨1071761, by rfl⟩ : syracuseStep 5716061 = 2143523) B2143523
theorem B1693803 : Blo 1693547 1693803 := bstep (se 1 (by rfl) ⟨1270352, by rfl⟩ : syracuseStep 1693803 = 2540705) B2540705
theorem B3618931 : Blo 1693547 3618931 := bstep (se 1 (by rfl) ⟨2714198, by rfl⟩ : syracuseStep 3618931 = 5428397) B5428397
theorem B1693815 : Blo 1693547 1693815 := bstep (se 1 (by rfl) ⟨1270361, by rfl⟩ : syracuseStep 1693815 = 2540723) B2540723
theorem B1906807 : Blo 1693547 1906807 := bstep (se 1 (by rfl) ⟨1430105, by rfl⟩ : syracuseStep 1906807 = 2860211) B2860211
theorem B1693835 : Blo 1693547 1693835 := bstep (se 1 (by rfl) ⟨1270376, by rfl⟩ : syracuseStep 1693835 = 2540753) B2540753
theorem B6437009 : Blo 1693547 6437009 := bstep (se 2 (by rfl) ⟨2413878, by rfl⟩ : syracuseStep 6437009 = 4827757) B4827757
theorem B1693847 : Blo 1693547 1693847 := bstep (se 1 (by rfl) ⟨1270385, by rfl⟩ : syracuseStep 1693847 = 2540771) B2540771
theorem B1693867 : Blo 1693547 1693867 := bstep (se 1 (by rfl) ⟨1270400, by rfl⟩ : syracuseStep 1693867 = 2540801) B2540801
theorem B1693879 : Blo 1693547 1693879 := bstep (se 1 (by rfl) ⟨1270409, by rfl⟩ : syracuseStep 1693879 = 2540819) B2540819
theorem B1693899 : Blo 1693547 1693899 := bstep (se 1 (by rfl) ⟨1270424, by rfl⟩ : syracuseStep 1693899 = 2540849) B2540849
theorem B1693911 : Blo 1693547 1693911 := bstep (se 1 (by rfl) ⟨1270433, by rfl⟩ : syracuseStep 1693911 = 2540867) B2540867
theorem B1693931 : Blo 1693547 1693931 := bstep (se 1 (by rfl) ⟨1270448, by rfl⟩ : syracuseStep 1693931 = 2540897) B2540897
theorem B1693943 : Blo 1693547 1693943 := bstep (se 1 (by rfl) ⟨1270457, by rfl⟩ : syracuseStep 1693943 = 2540915) B2540915
theorem B1693963 : Blo 1693547 1693963 := bstep (se 1 (by rfl) ⟨1270472, by rfl⟩ : syracuseStep 1693963 = 2540945) B2540945
theorem B1693975 : Blo 1693547 1693975 := bstep (se 1 (by rfl) ⟨1270481, by rfl⟩ : syracuseStep 1693975 = 2540963) B2540963
theorem B1693995 : Blo 1693547 1693995 := bstep (se 1 (by rfl) ⟨1270496, by rfl⟩ : syracuseStep 1693995 = 2540993) B2540993
theorem B1906987 : Blo 1693547 1906987 := bstep (se 1 (by rfl) ⟨1430240, by rfl⟩ : syracuseStep 1906987 = 2860481) B2860481
theorem B3217715 : Blo 1693547 3217715 := bstep (se 1 (by rfl) ⟨2413286, by rfl⟩ : syracuseStep 3217715 = 4826573) B4826573
theorem B1694007 : Blo 1693547 1694007 := bstep (se 1 (by rfl) ⟨1270505, by rfl⟩ : syracuseStep 1694007 = 2541011) B2541011
theorem B8575307 : Blo 1693547 8575307 := bstep (se 1 (by rfl) ⟨6431480, by rfl⟩ : syracuseStep 8575307 = 12862961) B12862961
theorem B1694027 : Blo 1693547 1694027 := bstep (se 1 (by rfl) ⟨1270520, by rfl⟩ : syracuseStep 1694027 = 2541041) B2541041
theorem B1694039 : Blo 1693547 1694039 := bstep (se 1 (by rfl) ⟨1270529, by rfl⟩ : syracuseStep 1694039 = 2541059) B2541059
theorem B1694059 : Blo 1693547 1694059 := bstep (se 1 (by rfl) ⟨1270544, by rfl⟩ : syracuseStep 1694059 = 2541089) B2541089
theorem B1694071 : Blo 1693547 1694071 := bstep (se 1 (by rfl) ⟨1270553, by rfl⟩ : syracuseStep 1694071 = 2541107) B2541107
theorem B1694091 : Blo 1693547 1694091 := bstep (se 1 (by rfl) ⟨1270568, by rfl⟩ : syracuseStep 1694091 = 2541137) B2541137
theorem B1694103 : Blo 1693547 1694103 := bstep (se 1 (by rfl) ⟨1270577, by rfl⟩ : syracuseStep 1694103 = 2541155) B2541155
theorem B3668375 : Blo 1693547 3668375 := bstep (se 1 (by rfl) ⟨2751281, by rfl⟩ : syracuseStep 3668375 = 5502563) B5502563
theorem B1907095 : Blo 1693547 1907095 := bstep (se 1 (by rfl) ⟨1430321, by rfl⟩ : syracuseStep 1907095 = 2860643) B2860643
theorem B1694123 : Blo 1693547 1694123 := bstep (se 1 (by rfl) ⟨1270592, by rfl⟩ : syracuseStep 1694123 = 2541185) B2541185
theorem B6109613 : Blo 1693547 6109613 := bstep (se 3 (by rfl) ⟨1145552, by rfl⟩ : syracuseStep 6109613 = 2291105) B2291105
theorem B4290995 : Blo 1693547 4290995 := bstep (se 1 (by rfl) ⟨3218246, by rfl⟩ : syracuseStep 4290995 = 6436493) B6436493
theorem B1694135 : Blo 1693547 1694135 := bstep (se 1 (by rfl) ⟨1270601, by rfl⟩ : syracuseStep 1694135 = 2541203) B2541203
theorem B1694155 : Blo 1693547 1694155 := bstep (se 1 (by rfl) ⟨1270616, by rfl⟩ : syracuseStep 1694155 = 2541233) B2541233
theorem B6871499 : Blo 1693547 6871499 := bstep (se 1 (by rfl) ⟨5153624, by rfl⟩ : syracuseStep 6871499 = 10307249) B10307249
theorem B1694167 : Blo 1693547 1694167 := bstep (se 1 (by rfl) ⟨1270625, by rfl⟩ : syracuseStep 1694167 = 2541251) B2541251
theorem B1694187 : Blo 1693547 1694187 := bstep (se 1 (by rfl) ⟨1270640, by rfl⟩ : syracuseStep 1694187 = 2541281) B2541281
theorem B1694199 : Blo 1693547 1694199 := bstep (se 1 (by rfl) ⟨1270649, by rfl⟩ : syracuseStep 1694199 = 2541299) B2541299
theorem B1694219 : Blo 1693547 1694219 := bstep (se 1 (by rfl) ⟨1270664, by rfl⟩ : syracuseStep 1694219 = 2541329) B2541329
theorem B1694231 : Blo 1693547 1694231 := bstep (se 1 (by rfl) ⟨1270673, by rfl⟩ : syracuseStep 1694231 = 2541347) B2541347
theorem B3217943 : Blo 1693547 3217943 := bstep (se 1 (by rfl) ⟨2413457, by rfl⟩ : syracuseStep 3217943 = 4826915) B4826915
theorem B1694251 : Blo 1693547 1694251 := bstep (se 1 (by rfl) ⟨1270688, by rfl⟩ : syracuseStep 1694251 = 2541377) B2541377
theorem B1694263 : Blo 1693547 1694263 := bstep (se 1 (by rfl) ⟨1270697, by rfl⟩ : syracuseStep 1694263 = 2541395) B2541395
theorem B10861121 : Blo 1693547 10861121 := bstep (se 2 (by rfl) ⟨4072920, by rfl⟩ : syracuseStep 10861121 = 8145841) B8145841
theorem B1694283 : Blo 1693547 1694283 := bstep (se 1 (by rfl) ⟨1270712, by rfl⟩ : syracuseStep 1694283 = 2541425) B2541425
theorem B1907275 : Blo 1693547 1907275 := bstep (se 1 (by rfl) ⟨1430456, by rfl⟩ : syracuseStep 1907275 = 2860913) B2860913
theorem B1694295 : Blo 1693547 1694295 := bstep (se 1 (by rfl) ⟨1270721, by rfl⟩ : syracuseStep 1694295 = 2541443) B2541443
theorem B3619417 : Blo 1693547 3619417 := bstep (se 2 (by rfl) ⟨1357281, by rfl⟩ : syracuseStep 3619417 = 2714563) B2714563
theorem B6437465 : Blo 1693547 6437465 := bstep (se 2 (by rfl) ⟨2414049, by rfl⟩ : syracuseStep 6437465 = 4828099) B4828099
theorem B1694315 : Blo 1693547 1694315 := bstep (se 1 (by rfl) ⟨1270736, by rfl⟩ : syracuseStep 1694315 = 2541473) B2541473
theorem B1694327 : Blo 1693547 1694327 := bstep (se 1 (by rfl) ⟨1270745, by rfl⟩ : syracuseStep 1694327 = 2541491) B2541491
theorem B1694347 : Blo 1693547 1694347 := bstep (se 1 (by rfl) ⟨1270760, by rfl⟩ : syracuseStep 1694347 = 2541521) B2541521
theorem B7240337 : Blo 1693547 7240337 := bstep (se 2 (by rfl) ⟨2715126, by rfl⟩ : syracuseStep 7240337 = 5430253) B5430253
theorem B1694359 : Blo 1693547 1694359 := bstep (se 1 (by rfl) ⟨1270769, by rfl⟩ : syracuseStep 1694359 = 2541539) B2541539
theorem B1694379 : Blo 1693547 1694379 := bstep (se 1 (by rfl) ⟨1270784, by rfl⟩ : syracuseStep 1694379 = 2541569) B2541569
theorem B4577971 : Blo 1693547 4577971 := bstep (se 1 (by rfl) ⟨3433478, by rfl⟩ : syracuseStep 4577971 = 6866957) B6866957
theorem B1694391 : Blo 1693547 1694391 := bstep (se 1 (by rfl) ⟨1270793, by rfl⟩ : syracuseStep 1694391 = 2541587) B2541587
theorem B1907383 : Blo 1693547 1907383 := bstep (se 1 (by rfl) ⟨1430537, by rfl⟩ : syracuseStep 1907383 = 2861075) B2861075
theorem B1694411 : Blo 1693547 1694411 := bstep (se 1 (by rfl) ⟨1270808, by rfl⟩ : syracuseStep 1694411 = 2541617) B2541617
theorem B2144971 : Blo 1693547 2144971 := bstep (se 1 (by rfl) ⟨1608728, by rfl⟩ : syracuseStep 2144971 = 3217457) B3217457
theorem B1694423 : Blo 1693547 1694423 := bstep (se 1 (by rfl) ⟨1270817, by rfl⟩ : syracuseStep 1694423 = 2541635) B2541635
theorem B12376793 : Blo 1693547 12376793 := bstep (se 2 (by rfl) ⟨4641297, by rfl⟩ : syracuseStep 12376793 = 9282595) B9282595
theorem B4291289 : Blo 1693547 4291289 := bstep (se 2 (by rfl) ⟨1609233, by rfl⟩ : syracuseStep 4291289 = 3218467) B3218467
theorem B1694443 : Blo 1693547 1694443 := bstep (se 1 (by rfl) ⟨1270832, by rfl⟩ : syracuseStep 1694443 = 2541665) B2541665
theorem B1694455 : Blo 1693547 1694455 := bstep (se 1 (by rfl) ⟨1270841, by rfl⟩ : syracuseStep 1694455 = 2541683) B2541683
theorem B1694475 : Blo 1693547 1694475 := bstep (se 1 (by rfl) ⟨1270856, by rfl⟩ : syracuseStep 1694475 = 2541713) B2541713
theorem B1694487 : Blo 1693547 1694487 := bstep (se 1 (by rfl) ⟨1270865, by rfl⟩ : syracuseStep 1694487 = 2541731) B2541731
theorem B3218201 : Blo 1693547 3218201 := bstep (se 2 (by rfl) ⟨1206825, by rfl⟩ : syracuseStep 3218201 = 2413651) B2413651
theorem B1694507 : Blo 1693547 1694507 := bstep (se 1 (by rfl) ⟨1270880, by rfl⟩ : syracuseStep 1694507 = 2541761) B2541761
theorem B6437677 : Blo 1693547 6437677 := bstep (se 3 (by rfl) ⟨1207064, by rfl⟩ : syracuseStep 6437677 = 2414129) B2414129
theorem B1694519 : Blo 1693547 1694519 := bstep (se 1 (by rfl) ⟨1270889, by rfl⟩ : syracuseStep 1694519 = 2541779) B2541779
theorem B1694539 : Blo 1693547 1694539 := bstep (se 1 (by rfl) ⟨1270904, by rfl⟩ : syracuseStep 1694539 = 2541809) B2541809
theorem B1694551 : Blo 1693547 1694551 := bstep (se 1 (by rfl) ⟨1270913, by rfl⟩ : syracuseStep 1694551 = 2541827) B2541827
theorem B1694571 : Blo 1693547 1694571 := bstep (se 1 (by rfl) ⟨1270928, by rfl⟩ : syracuseStep 1694571 = 2541857) B2541857
theorem B1694583 : Blo 1693547 1694583 := bstep (se 1 (by rfl) ⟨1270937, by rfl⟩ : syracuseStep 1694583 = 2541875) B2541875
theorem B1694603 : Blo 1693547 1694603 := bstep (se 1 (by rfl) ⟨1270952, by rfl⟩ : syracuseStep 1694603 = 2541905) B2541905
theorem B1694615 : Blo 1693547 1694615 := bstep (se 1 (by rfl) ⟨1270961, by rfl⟩ : syracuseStep 1694615 = 2541923) B2541923
theorem B1694635 : Blo 1693547 1694635 := bstep (se 1 (by rfl) ⟨1270976, by rfl⟩ : syracuseStep 1694635 = 2541953) B2541953
theorem B1694647 : Blo 1693547 1694647 := bstep (se 1 (by rfl) ⟨1270985, by rfl⟩ : syracuseStep 1694647 = 2541971) B2541971
theorem B1694667 : Blo 1693547 1694667 := bstep (se 1 (by rfl) ⟨1271000, by rfl⟩ : syracuseStep 1694667 = 2542001) B2542001
theorem B2857943 : Blo 1693547 2857943 := bstep (se 1 (by rfl) ⟨2143457, by rfl⟩ : syracuseStep 2857943 = 4286915) B4286915
theorem B1694679 : Blo 1693547 1694679 := bstep (se 1 (by rfl) ⟨1271009, by rfl⟩ : syracuseStep 1694679 = 2542019) B2542019
theorem B1694699 : Blo 1693547 1694699 := bstep (se 1 (by rfl) ⟨1271024, by rfl⟩ : syracuseStep 1694699 = 2542049) B2542049
theorem B1694711 : Blo 1693547 1694711 := bstep (se 1 (by rfl) ⟨1271033, by rfl⟩ : syracuseStep 1694711 = 2542067) B2542067
theorem B3480587 : Blo 1693547 3480587 := bstep (se 1 (by rfl) ⟨2610440, by rfl⟩ : syracuseStep 3480587 = 5220881) B5220881
theorem B1694731 : Blo 1693547 1694731 := bstep (se 1 (by rfl) ⟨1271048, by rfl⟩ : syracuseStep 1694731 = 2542097) B2542097
theorem B11590673 : Blo 1693547 11590673 := bstep (se 2 (by rfl) ⟨4346502, by rfl⟩ : syracuseStep 11590673 = 8693005) B8693005
theorem B1694743 : Blo 1693547 1694743 := bstep (se 1 (by rfl) ⟨1271057, by rfl⟩ : syracuseStep 1694743 = 2542115) B2542115
theorem B1694763 : Blo 1693547 1694763 := bstep (se 1 (by rfl) ⟨1271072, by rfl⟩ : syracuseStep 1694763 = 2542145) B2542145
theorem B1694775 : Blo 1693547 1694775 := bstep (se 1 (by rfl) ⟨1271081, by rfl⟩ : syracuseStep 1694775 = 2542163) B2542163
theorem B1694795 : Blo 1693547 1694795 := bstep (se 1 (by rfl) ⟨1271096, by rfl⟩ : syracuseStep 1694795 = 2542193) B2542193
theorem B2858071 : Blo 1693547 2858071 := bstep (se 1 (by rfl) ⟨2143553, by rfl⟩ : syracuseStep 2858071 = 4287107) B4287107
theorem B1694807 : Blo 1693547 1694807 := bstep (se 1 (by rfl) ⟨1271105, by rfl⟩ : syracuseStep 1694807 = 2542211) B2542211
theorem B1694827 : Blo 1693547 1694827 := bstep (se 1 (by rfl) ⟨1271120, by rfl⟩ : syracuseStep 1694827 = 2542241) B2542241
theorem B1694839 : Blo 1693547 1694839 := bstep (se 1 (by rfl) ⟨1271129, by rfl⟩ : syracuseStep 1694839 = 2542259) B2542259
theorem B1694859 : Blo 1693547 1694859 := bstep (se 1 (by rfl) ⟨1271144, by rfl⟩ : syracuseStep 1694859 = 2542289) B2542289
theorem B21175447 : Blo 1693547 21175447 := bstep (se 1 (by rfl) ⟨15881585, by rfl⟩ : syracuseStep 21175447 = 31763171) B31763171
theorem B1694871 : Blo 1693547 1694871 := bstep (se 1 (by rfl) ⟨1271153, by rfl⟩ : syracuseStep 1694871 = 2542307) B2542307
theorem B1694891 : Blo 1693547 1694891 := bstep (se 1 (by rfl) ⟨1271168, by rfl⟩ : syracuseStep 1694891 = 2542337) B2542337
theorem B3218611 : Blo 1693547 3218611 := bstep (se 1 (by rfl) ⟨2413958, by rfl⟩ : syracuseStep 3218611 = 4827917) B4827917
theorem B37141685 : Blo 1693547 37141685 := bstep (se 5 (by rfl) ⟨1741016, by rfl⟩ : syracuseStep 37141685 = 3482033) B3482033
theorem B1694903 : Blo 1693547 1694903 := bstep (se 1 (by rfl) ⟨1271177, by rfl⟩ : syracuseStep 1694903 = 2542355) B2542355
theorem B5717195 : Blo 1693547 5717195 := bstep (se 1 (by rfl) ⟨4287896, by rfl⟩ : syracuseStep 5717195 = 8575793) B8575793
theorem B2899147 : Blo 1693547 2899147 := bstep (se 1 (by rfl) ⟨2174360, by rfl⟩ : syracuseStep 2899147 = 4348721) B4348721
theorem B1694923 : Blo 1693547 1694923 := bstep (se 1 (by rfl) ⟨1271192, by rfl⟩ : syracuseStep 1694923 = 2542385) B2542385
theorem B1694935 : Blo 1693547 1694935 := bstep (se 1 (by rfl) ⟨1271201, by rfl⟩ : syracuseStep 1694935 = 2542403) B2542403
theorem B3669209 : Blo 1693547 3669209 := bstep (se 2 (by rfl) ⟨1375953, by rfl⟩ : syracuseStep 3669209 = 2751907) B2751907
theorem B1694955 : Blo 1693547 1694955 := bstep (se 1 (by rfl) ⟨1271216, by rfl⟩ : syracuseStep 1694955 = 2542433) B2542433
theorem B3054835 : Blo 1693547 3054835 := bstep (se 1 (by rfl) ⟨2291126, by rfl⟩ : syracuseStep 3054835 = 4582253) B4582253
theorem B1694967 : Blo 1693547 1694967 := bstep (se 1 (by rfl) ⟨1271225, by rfl⟩ : syracuseStep 1694967 = 2542451) B2542451
theorem B1694987 : Blo 1693547 1694987 := bstep (se 1 (by rfl) ⟨1271240, by rfl⟩ : syracuseStep 1694987 = 2542481) B2542481
theorem B1694999 : Blo 1693547 1694999 := bstep (se 1 (by rfl) ⟨1271249, by rfl⟩ : syracuseStep 1694999 = 2542499) B2542499
theorem B1695019 : Blo 1693547 1695019 := bstep (se 1 (by rfl) ⟨1271264, by rfl⟩ : syracuseStep 1695019 = 2542529) B2542529
theorem B1695031 : Blo 1693547 1695031 := bstep (se 1 (by rfl) ⟨1271273, by rfl⟩ : syracuseStep 1695031 = 2542547) B2542547
theorem B1809739 : Blo 1693547 1809739 := bstep (se 1 (by rfl) ⟨1357304, by rfl⟩ : syracuseStep 1809739 = 2714609) B2714609
theorem B1695051 : Blo 1693547 1695051 := bstep (se 1 (by rfl) ⟨1271288, by rfl⟩ : syracuseStep 1695051 = 2542577) B2542577
theorem B1695063 : Blo 1693547 1695063 := bstep (se 1 (by rfl) ⟨1271297, by rfl⟩ : syracuseStep 1695063 = 2542595) B2542595
theorem B1695083 : Blo 1693547 1695083 := bstep (se 1 (by rfl) ⟨1271312, by rfl⟩ : syracuseStep 1695083 = 2542625) B2542625
theorem B1695095 : Blo 1693547 1695095 := bstep (se 1 (by rfl) ⟨1271321, by rfl⟩ : syracuseStep 1695095 = 2542643) B2542643
theorem B1695115 : Blo 1693547 1695115 := bstep (se 1 (by rfl) ⟨1271336, by rfl⟩ : syracuseStep 1695115 = 2542673) B2542673
theorem B3480983 : Blo 1693547 3480983 := bstep (se 1 (by rfl) ⟨2610737, by rfl⟩ : syracuseStep 3480983 = 5221475) B5221475
theorem B4070807 : Blo 1693547 4070807 := bstep (se 1 (by rfl) ⟨3053105, by rfl⟩ : syracuseStep 4070807 = 6106211) B6106211
theorem B1695127 : Blo 1693547 1695127 := bstep (se 1 (by rfl) ⟨1271345, by rfl⟩ : syracuseStep 1695127 = 2542691) B2542691
theorem B1695147 : Blo 1693547 1695147 := bstep (se 1 (by rfl) ⟨1271360, by rfl⟩ : syracuseStep 1695147 = 2542721) B2542721
theorem B1695159 : Blo 1693547 1695159 := bstep (se 1 (by rfl) ⟨1271369, by rfl⟩ : syracuseStep 1695159 = 2542739) B2542739
theorem B1695179 : Blo 1693547 1695179 := bstep (se 1 (by rfl) ⟨1271384, by rfl⟩ : syracuseStep 1695179 = 2542769) B2542769
theorem B1695191 : Blo 1693547 1695191 := bstep (se 1 (by rfl) ⟨1271393, by rfl⟩ : syracuseStep 1695191 = 2542787) B2542787
theorem B5717465 : Blo 1693547 5717465 := bstep (se 2 (by rfl) ⟨2144049, by rfl⟩ : syracuseStep 5717465 = 4288099) B4288099
theorem B1695211 : Blo 1693547 1695211 := bstep (se 1 (by rfl) ⟨1271408, by rfl⟩ : syracuseStep 1695211 = 2542817) B2542817
theorem B1695223 : Blo 1693547 1695223 := bstep (se 1 (by rfl) ⟨1271417, by rfl⟩ : syracuseStep 1695223 = 2542835) B2542835
theorem B1695243 : Blo 1693547 1695243 := bstep (se 1 (by rfl) ⟨1271432, by rfl⟩ : syracuseStep 1695243 = 2542865) B2542865
theorem B1695255 : Blo 1693547 1695255 := bstep (se 1 (by rfl) ⟨1271441, by rfl⟩ : syracuseStep 1695255 = 2542883) B2542883
theorem B1695275 : Blo 1693547 1695275 := bstep (se 1 (by rfl) ⟨1271456, by rfl⟩ : syracuseStep 1695275 = 2542913) B2542913
theorem B1695287 : Blo 1693547 1695287 := bstep (se 1 (by rfl) ⟨1271465, by rfl⟩ : syracuseStep 1695287 = 2542931) B2542931
theorem B1695307 : Blo 1693547 1695307 := bstep (se 1 (by rfl) ⟨1271480, by rfl⟩ : syracuseStep 1695307 = 2542961) B2542961
theorem B5226059 : Blo 1693547 5226059 := bstep (se 1 (by rfl) ⟨3919544, by rfl⟩ : syracuseStep 5226059 = 7839089) B7839089
theorem B1695319 : Blo 1693547 1695319 := bstep (se 1 (by rfl) ⟨1271489, by rfl⟩ : syracuseStep 1695319 = 2542979) B2542979
theorem B1695339 : Blo 1693547 1695339 := bstep (se 1 (by rfl) ⟨1271504, by rfl⟩ : syracuseStep 1695339 = 2543009) B2543009
theorem B1695351 : Blo 1693547 1695351 := bstep (se 1 (by rfl) ⟨1271513, by rfl⟩ : syracuseStep 1695351 = 2543027) B2543027
theorem B1695371 : Blo 1693547 1695371 := bstep (se 1 (by rfl) ⟨1271528, by rfl⟩ : syracuseStep 1695371 = 2543057) B2543057
theorem B1695383 : Blo 1693547 1695383 := bstep (se 1 (by rfl) ⟨1271537, by rfl⟩ : syracuseStep 1695383 = 2543075) B2543075
theorem B1695403 : Blo 1693547 1695403 := bstep (se 1 (by rfl) ⟨1271552, by rfl⟩ : syracuseStep 1695403 = 2543105) B2543105
theorem B6430387 : Blo 1693547 6430387 := bstep (se 1 (by rfl) ⟨4822790, by rfl⟩ : syracuseStep 6430387 = 9645581) B9645581
theorem B1695415 : Blo 1693547 1695415 := bstep (se 1 (by rfl) ⟨1271561, by rfl⟩ : syracuseStep 1695415 = 2543123) B2543123
theorem B2858699 : Blo 1693547 2858699 := bstep (se 1 (by rfl) ⟨2144024, by rfl⟩ : syracuseStep 2858699 = 4288049) B4288049
theorem B1695435 : Blo 1693547 1695435 := bstep (se 1 (by rfl) ⟨1271576, by rfl⟩ : syracuseStep 1695435 = 2543153) B2543153
theorem B1695447 : Blo 1693547 1695447 := bstep (se 1 (by rfl) ⟨1271585, by rfl⟩ : syracuseStep 1695447 = 2543171) B2543171
theorem B1695467 : Blo 1693547 1695467 := bstep (se 1 (by rfl) ⟨1271600, by rfl⟩ : syracuseStep 1695467 = 2543201) B2543201
theorem B24772337 : Blo 1693547 24772337 := bstep (se 2 (by rfl) ⟨9289626, by rfl⟩ : syracuseStep 24772337 = 18579253) B18579253
theorem B1695479 : Blo 1693547 1695479 := bstep (se 1 (by rfl) ⟨1271609, by rfl⟩ : syracuseStep 1695479 = 2543219) B2543219
theorem B19308293 : Blo 1693547 19308293 := bstep (se 4 (by rfl) ⟨1810152, by rfl⟩ : syracuseStep 19308293 = 3620305) B3620305
theorem B1695499 : Blo 1693547 1695499 := bstep (se 1 (by rfl) ⟨1271624, by rfl⟩ : syracuseStep 1695499 = 2543249) B2543249
theorem B1695511 : Blo 1693547 1695511 := bstep (se 1 (by rfl) ⟨1271633, by rfl⟩ : syracuseStep 1695511 = 2543267) B2543267
theorem B1695531 : Blo 1693547 1695531 := bstep (se 1 (by rfl) ⟨1271648, by rfl⟩ : syracuseStep 1695531 = 2543297) B2543297
theorem B1695543 : Blo 1693547 1695543 := bstep (se 1 (by rfl) ⟨1271657, by rfl⟩ : syracuseStep 1695543 = 2543315) B2543315
theorem B2858827 : Blo 1693547 2858827 := bstep (se 1 (by rfl) ⟨2144120, by rfl⟩ : syracuseStep 2858827 = 4288241) B4288241
theorem B3620801 : Blo 1693547 3620801 := bstep (se 2 (by rfl) ⟨1357800, by rfl⟩ : syracuseStep 3620801 = 2715601) B2715601
theorem B2858969 : Blo 1693547 2858969 := bstep (se 2 (by rfl) ⟨1072113, by rfl⟩ : syracuseStep 2858969 = 2144227) B2144227
theorem B9650137 : Blo 1693547 9650137 := bstep (se 2 (by rfl) ⟨3618801, by rfl⟩ : syracuseStep 9650137 = 7237603) B7237603
theorem B2859023 : Blo 1693547 2859023 := bstep (se 1 (by rfl) ⟨2144267, by rfl⟩ : syracuseStep 2859023 = 4288535) B4288535
theorem B5718059 : Blo 1693547 5718059 := bstep (se 1 (by rfl) ⟨4288544, by rfl⟩ : syracuseStep 5718059 = 8577089) B8577089
theorem B30908461 : Blo 1693547 30908461 := bstep (se 3 (by rfl) ⟨5795336, by rfl⟩ : syracuseStep 30908461 = 11590673) B11590673
theorem B12869765 : Blo 1693547 12869765 := bstep (se 4 (by rfl) ⟨1206540, by rfl⟩ : syracuseStep 12869765 = 2413081) B2413081
theorem B4825241 : Blo 1693547 4825241 := bstep (se 2 (by rfl) ⟨1809465, by rfl⟩ : syracuseStep 4825241 = 3618931) B3618931
theorem B4350251 : Blo 1693547 4350251 := bstep (se 1 (by rfl) ⟨3262688, by rfl⟩ : syracuseStep 4350251 = 6525377) B6525377
theorem B4071767 : Blo 1693547 4071767 := bstep (se 1 (by rfl) ⟨3053825, by rfl⟩ : syracuseStep 4071767 = 6107651) B6107651
theorem B8258071 : Blo 1693547 8258071 := bstep (se 1 (by rfl) ⟨6193553, by rfl⟩ : syracuseStep 8258071 = 12387107) B12387107
theorem B2859563 : Blo 1693547 2859563 := bstep (se 1 (by rfl) ⟨2144672, by rfl⟩ : syracuseStep 2859563 = 4289345) B4289345
theorem B8577737 : Blo 1693547 8577737 := bstep (se 2 (by rfl) ⟨3216651, by rfl⟩ : syracuseStep 8577737 = 6433303) B6433303
theorem B21709529 : Blo 1693547 21709529 := bstep (se 2 (by rfl) ⟨8141073, by rfl⟩ : syracuseStep 21709529 = 16282147) B16282147
theorem B4825889 : Blo 1693547 4825889 := bstep (se 2 (by rfl) ⟨1809708, by rfl⟩ : syracuseStep 4825889 = 3619417) B3619417
theorem B2540345 : Blo 1693547 2540345 := bstep (se 2 (by rfl) ⟨952629, by rfl⟩ : syracuseStep 2540345 = 1905259) B1905259
theorem B4580155 : Blo 1693547 4580155 := bstep (se 1 (by rfl) ⟨3435116, by rfl⟩ : syracuseStep 4580155 = 6870233) B6870233
theorem B2540423 : Blo 1693547 2540423 := bstep (se 1 (by rfl) ⟨1905317, by rfl⟩ : syracuseStep 2540423 = 3810635) B3810635
theorem B6103961 : Blo 1693547 6103961 := bstep (se 2 (by rfl) ⟨2288985, by rfl⟩ : syracuseStep 6103961 = 4577971) B4577971
theorem B2540459 : Blo 1693547 2540459 := bstep (se 1 (by rfl) ⟨1905344, by rfl⟩ : syracuseStep 2540459 = 3810689) B3810689
theorem B69600181 : Blo 1693547 69600181 := bstep (se 5 (by rfl) ⟨3262508, by rfl⟩ : syracuseStep 69600181 = 6525017) B6525017
theorem B2859961 : Blo 1693547 2859961 := bstep (se 2 (by rfl) ⟨1072485, by rfl⟩ : syracuseStep 2859961 = 2144971) B2144971
theorem B2540489 : Blo 1693547 2540489 := bstep (se 2 (by rfl) ⟨952683, by rfl⟩ : syracuseStep 2540489 = 1905367) B1905367
theorem B12862475 : Blo 1693547 12862475 := bstep (se 1 (by rfl) ⟨9646856, by rfl⟩ : syracuseStep 12862475 = 19293713) B19293713
theorem B15885335 : Blo 1693547 15885335 := bstep (se 1 (by rfl) ⟨11914001, by rfl⟩ : syracuseStep 15885335 = 23828003) B23828003
theorem B2540603 : Blo 1693547 2540603 := bstep (se 1 (by rfl) ⟨1905452, by rfl⟩ : syracuseStep 2540603 = 3810905) B3810905
theorem B9782333 : Blo 1693547 9782333 := bstep (se 3 (by rfl) ⟨1834187, by rfl⟩ : syracuseStep 9782333 = 3668375) B3668375
theorem B6431831 : Blo 1693547 6431831 := bstep (se 1 (by rfl) ⟨4823873, by rfl⟩ : syracuseStep 6431831 = 9647747) B9647747
theorem B2540663 : Blo 1693547 2540663 := bstep (se 1 (by rfl) ⟨1905497, by rfl⟩ : syracuseStep 2540663 = 3810995) B3810995
theorem B2540687 : Blo 1693547 2540687 := bstep (se 1 (by rfl) ⟨1905515, by rfl⟩ : syracuseStep 2540687 = 3811031) B3811031
theorem B2540729 : Blo 1693547 2540729 := bstep (se 2 (by rfl) ⟨952773, by rfl⟩ : syracuseStep 2540729 = 1905547) B1905547
theorem B2540807 : Blo 1693547 2540807 := bstep (se 1 (by rfl) ⟨1905605, by rfl⟩ : syracuseStep 2540807 = 3811211) B3811211
theorem B2540843 : Blo 1693547 2540843 := bstep (se 1 (by rfl) ⟨1905632, by rfl⟩ : syracuseStep 2540843 = 3811265) B3811265
theorem B5719355 : Blo 1693547 5719355 := bstep (se 1 (by rfl) ⟨4289516, by rfl⟩ : syracuseStep 5719355 = 8579033) B8579033
theorem B2540873 : Blo 1693547 2540873 := bstep (se 2 (by rfl) ⟨952827, by rfl⟩ : syracuseStep 2540873 = 1905655) B1905655
theorem B3810707 : Blo 1693547 3810707 := bstep (se 1 (by rfl) ⟨2858030, by rfl⟩ : syracuseStep 3810707 = 5716061) B5716061
theorem B2540987 : Blo 1693547 2540987 := bstep (se 1 (by rfl) ⟨1905740, by rfl⟩ : syracuseStep 2540987 = 3811481) B3811481
theorem B3810761 : Blo 1693547 3810761 := bstep (se 2 (by rfl) ⟨1429035, by rfl⟩ : syracuseStep 3810761 = 2858071) B2858071
theorem B2541047 : Blo 1693547 2541047 := bstep (se 1 (by rfl) ⟨1905785, by rfl⟩ : syracuseStep 2541047 = 3811571) B3811571
theorem B2541071 : Blo 1693547 2541071 := bstep (se 1 (by rfl) ⟨1905803, by rfl⟩ : syracuseStep 2541071 = 3811607) B3811607
theorem B13936157 : Blo 1693547 13936157 := bstep (se 3 (by rfl) ⟨2613029, by rfl⟩ : syracuseStep 13936157 = 5226059) B5226059
theorem B2541113 : Blo 1693547 2541113 := bstep (se 2 (by rfl) ⟨952917, by rfl⟩ : syracuseStep 2541113 = 1905835) B1905835
theorem B6432317 : Blo 1693547 6432317 := bstep (se 3 (by rfl) ⟨1206059, by rfl⟩ : syracuseStep 6432317 = 2412119) B2412119
theorem B4073075 : Blo 1693547 4073075 := bstep (se 1 (by rfl) ⟨3054806, by rfl⟩ : syracuseStep 4073075 = 6109613) B6109613
theorem B2860663 : Blo 1693547 2860663 := bstep (se 1 (by rfl) ⟨2145497, by rfl⟩ : syracuseStep 2860663 = 4290995) B4290995
theorem B2541191 : Blo 1693547 2541191 := bstep (se 1 (by rfl) ⟨1905893, by rfl⟩ : syracuseStep 2541191 = 3811787) B3811787
theorem B4580999 : Blo 1693547 4580999 := bstep (se 1 (by rfl) ⟨3435749, by rfl⟩ : syracuseStep 4580999 = 6871499) B6871499
theorem B4073113 : Blo 1693547 4073113 := bstep (se 2 (by rfl) ⟨1527417, by rfl⟩ : syracuseStep 4073113 = 3054835) B3054835
theorem B2541227 : Blo 1693547 2541227 := bstep (se 1 (by rfl) ⟨1905920, by rfl⟩ : syracuseStep 2541227 = 3811841) B3811841
theorem B6866633 : Blo 1693547 6866633 := bstep (se 2 (by rfl) ⟨2574987, by rfl⟩ : syracuseStep 6866633 = 5149975) B5149975
theorem B2541257 : Blo 1693547 2541257 := bstep (se 2 (by rfl) ⟨952971, by rfl⟩ : syracuseStep 2541257 = 1905943) B1905943
theorem B4826891 : Blo 1693547 4826891 := bstep (se 1 (by rfl) ⟨3620168, by rfl⟩ : syracuseStep 4826891 = 7240337) B7240337
theorem B5719841 : Blo 1693547 5719841 := bstep (se 2 (by rfl) ⟨2144940, by rfl⟩ : syracuseStep 5719841 = 4289881) B4289881
theorem B8251195 : Blo 1693547 8251195 := bstep (se 1 (by rfl) ⟨6188396, by rfl⟩ : syracuseStep 8251195 = 12376793) B12376793
theorem B2541371 : Blo 1693547 2541371 := bstep (se 1 (by rfl) ⟨1906028, by rfl⟩ : syracuseStep 2541371 = 3812057) B3812057
theorem B2860859 : Blo 1693547 2860859 := bstep (se 1 (by rfl) ⟨2145644, by rfl⟩ : syracuseStep 2860859 = 4291289) B4291289
theorem B2541431 : Blo 1693547 2541431 := bstep (se 1 (by rfl) ⟨1906073, by rfl⟩ : syracuseStep 2541431 = 3812147) B3812147
theorem B2541455 : Blo 1693547 2541455 := bstep (se 1 (by rfl) ⟨1906091, by rfl⟩ : syracuseStep 2541455 = 3812183) B3812183
theorem B9652121 : Blo 1693547 9652121 := bstep (se 2 (by rfl) ⟨3619545, by rfl⟩ : syracuseStep 9652121 = 7239091) B7239091
theorem B2541497 : Blo 1693547 2541497 := bstep (se 2 (by rfl) ⟨953061, by rfl⟩ : syracuseStep 2541497 = 1906123) B1906123
theorem B2320391 : Blo 1693547 2320391 := bstep (se 1 (by rfl) ⟨1740293, by rfl⟩ : syracuseStep 2320391 = 3480587) B3480587
theorem B2541575 : Blo 1693547 2541575 := bstep (se 1 (by rfl) ⟨1906181, by rfl⟩ : syracuseStep 2541575 = 3812363) B3812363
theorem B2541611 : Blo 1693547 2541611 := bstep (se 1 (by rfl) ⟨1906208, by rfl⟩ : syracuseStep 2541611 = 3812417) B3812417
theorem B19302461 : Blo 1693547 19302461 := bstep (se 3 (by rfl) ⟨3619211, by rfl⟩ : syracuseStep 19302461 = 7238423) B7238423
theorem B2541641 : Blo 1693547 2541641 := bstep (se 2 (by rfl) ⟨953115, by rfl⟩ : syracuseStep 2541641 = 1906231) B1906231
theorem B3811463 : Blo 1693547 3811463 := bstep (se 1 (by rfl) ⟨2858597, by rfl⟩ : syracuseStep 3811463 = 5717195) B5717195
theorem B2541755 : Blo 1693547 2541755 := bstep (se 1 (by rfl) ⟨1906316, by rfl⟩ : syracuseStep 2541755 = 3812633) B3812633
theorem B2541815 : Blo 1693547 2541815 := bstep (se 1 (by rfl) ⟨1906361, by rfl⟩ : syracuseStep 2541815 = 3812723) B3812723
theorem B2320655 : Blo 1693547 2320655 := bstep (se 1 (by rfl) ⟨1740491, by rfl⟩ : syracuseStep 2320655 = 3480983) B3480983
theorem B2713871 : Blo 1693547 2713871 := bstep (se 1 (by rfl) ⟨2035403, by rfl⟩ : syracuseStep 2713871 = 4070807) B4070807
theorem B2541839 : Blo 1693547 2541839 := bstep (se 1 (by rfl) ⟨1906379, by rfl⟩ : syracuseStep 2541839 = 3812759) B3812759
theorem B2541881 : Blo 1693547 2541881 := bstep (se 2 (by rfl) ⟨953205, by rfl⟩ : syracuseStep 2541881 = 1906411) B1906411
theorem B3811643 : Blo 1693547 3811643 := bstep (se 1 (by rfl) ⟨2858732, by rfl⟩ : syracuseStep 3811643 = 5717465) B5717465
theorem B5720435 : Blo 1693547 5720435 := bstep (se 1 (by rfl) ⟨4290326, by rfl⟩ : syracuseStep 5720435 = 8580653) B8580653
theorem B2541959 : Blo 1693547 2541959 := bstep (se 1 (by rfl) ⟨1906469, by rfl⟩ : syracuseStep 2541959 = 3812939) B3812939
theorem B8145305 : Blo 1693547 8145305 := bstep (se 2 (by rfl) ⟨3054489, by rfl⟩ : syracuseStep 8145305 = 6108979) B6108979
theorem B2541995 : Blo 1693547 2541995 := bstep (se 1 (by rfl) ⟨1906496, by rfl⟩ : syracuseStep 2541995 = 3812993) B3812993
theorem B3811769 : Blo 1693547 3811769 := bstep (se 2 (by rfl) ⟨1429413, by rfl⟩ : syracuseStep 3811769 = 2858827) B2858827
theorem B18835897 : Blo 1693547 18835897 := bstep (se 2 (by rfl) ⟨7063461, by rfl⟩ : syracuseStep 18835897 = 14126923) B14126923
theorem B2542025 : Blo 1693547 2542025 := bstep (se 2 (by rfl) ⟨953259, by rfl⟩ : syracuseStep 2542025 = 1906519) B1906519
theorem B12872195 : Blo 1693547 12872195 := bstep (se 1 (by rfl) ⟨9654146, by rfl⟩ : syracuseStep 12872195 = 19308293) B19308293
theorem B2542139 : Blo 1693547 2542139 := bstep (se 1 (by rfl) ⟨1906604, by rfl⟩ : syracuseStep 2542139 = 3813209) B3813209
theorem B2542199 : Blo 1693547 2542199 := bstep (se 1 (by rfl) ⟨1906649, by rfl⟩ : syracuseStep 2542199 = 3813299) B3813299
theorem B2542223 : Blo 1693547 2542223 := bstep (se 1 (by rfl) ⟨1906667, by rfl⟩ : syracuseStep 2542223 = 3813335) B3813335
theorem B2542265 : Blo 1693547 2542265 := bstep (se 2 (by rfl) ⟨953349, by rfl⟩ : syracuseStep 2542265 = 1906699) B1906699
theorem B4893385 : Blo 1693547 4893385 := bstep (se 2 (by rfl) ⟨1835019, by rfl⟩ : syracuseStep 4893385 = 3670039) B3670039
theorem B2173703 : Blo 1693547 2173703 := bstep (se 1 (by rfl) ⟨1630277, by rfl⟩ : syracuseStep 2173703 = 3260555) B3260555
theorem B2542343 : Blo 1693547 2542343 := bstep (se 1 (by rfl) ⟨1906757, by rfl⟩ : syracuseStep 2542343 = 3813515) B3813515
theorem B3812111 : Blo 1693547 3812111 := bstep (se 1 (by rfl) ⟨2859083, by rfl⟩ : syracuseStep 3812111 = 5718167) B5718167
theorem B3812129 : Blo 1693547 3812129 := bstep (se 2 (by rfl) ⟨1429548, by rfl⟩ : syracuseStep 3812129 = 2859097) B2859097
theorem B2542379 : Blo 1693547 2542379 := bstep (se 1 (by rfl) ⟨1906784, by rfl⟩ : syracuseStep 2542379 = 3813569) B3813569
theorem B2542409 : Blo 1693547 2542409 := bstep (se 2 (by rfl) ⟨953403, by rfl⟩ : syracuseStep 2542409 = 1906807) B1906807
theorem B2411407 : Blo 1693547 2411407 := bstep (se 1 (by rfl) ⟨1808555, by rfl⟩ : syracuseStep 2411407 = 3617111) B3617111
theorem B12864419 : Blo 1693547 12864419 := bstep (se 1 (by rfl) ⟨9648314, by rfl⟩ : syracuseStep 12864419 = 19296629) B19296629
theorem B2542523 : Blo 1693547 2542523 := bstep (se 1 (by rfl) ⟨1906892, by rfl⟩ : syracuseStep 2542523 = 3813785) B3813785
theorem B2542583 : Blo 1693547 2542583 := bstep (se 1 (by rfl) ⟨1906937, by rfl⟩ : syracuseStep 2542583 = 3813875) B3813875
theorem B2411527 : Blo 1693547 2411527 := bstep (se 1 (by rfl) ⟨1808645, by rfl⟩ : syracuseStep 2411527 = 3617291) B3617291
theorem B2542607 : Blo 1693547 2542607 := bstep (se 1 (by rfl) ⟨1906955, by rfl⟩ : syracuseStep 2542607 = 3813911) B3813911
theorem B2542649 : Blo 1693547 2542649 := bstep (se 2 (by rfl) ⟨953493, by rfl⟩ : syracuseStep 2542649 = 1906987) B1906987
theorem B14126167 : Blo 1693547 14126167 := bstep (se 1 (by rfl) ⟨10594625, by rfl⟩ : syracuseStep 14126167 = 21189251) B21189251
theorem B3812471 : Blo 1693547 3812471 := bstep (se 1 (by rfl) ⟨2859353, by rfl⟩ : syracuseStep 3812471 = 5718707) B5718707
theorem B2542727 : Blo 1693547 2542727 := bstep (se 1 (by rfl) ⟨1907045, by rfl⟩ : syracuseStep 2542727 = 3814091) B3814091
theorem B2542763 : Blo 1693547 2542763 := bstep (se 1 (by rfl) ⟨1907072, by rfl⟩ : syracuseStep 2542763 = 3814145) B3814145
theorem B2542793 : Blo 1693547 2542793 := bstep (se 2 (by rfl) ⟨953547, by rfl⟩ : syracuseStep 2542793 = 1907095) B1907095
theorem B4287755 : Blo 1693547 4287755 := bstep (se 1 (by rfl) ⟨3215816, by rfl⟩ : syracuseStep 4287755 = 6431633) B6431633
theorem B6434063 : Blo 1693547 6434063 := bstep (se 1 (by rfl) ⟨4825547, by rfl⟩ : syracuseStep 6434063 = 9651095) B9651095
theorem B3812651 : Blo 1693547 3812651 := bstep (se 1 (by rfl) ⟨2859488, by rfl⟩ : syracuseStep 3812651 = 5718977) B5718977
theorem B2542907 : Blo 1693547 2542907 := bstep (se 1 (by rfl) ⟨1907180, by rfl⟩ : syracuseStep 2542907 = 3814361) B3814361
theorem B3435895 : Blo 1693547 3435895 := bstep (se 1 (by rfl) ⟨2576921, by rfl⟩ : syracuseStep 3435895 = 5153843) B5153843
theorem B2542967 : Blo 1693547 2542967 := bstep (se 1 (by rfl) ⟨1907225, by rfl⟩ : syracuseStep 2542967 = 3814451) B3814451
theorem B2542991 : Blo 1693547 2542991 := bstep (se 1 (by rfl) ⟨1907243, by rfl⟩ : syracuseStep 2542991 = 3814487) B3814487
theorem B2543033 : Blo 1693547 2543033 := bstep (se 2 (by rfl) ⟨953637, by rfl⟩ : syracuseStep 2543033 = 1907275) B1907275
theorem B2543111 : Blo 1693547 2543111 := bstep (se 1 (by rfl) ⟨1907333, by rfl⟩ : syracuseStep 2543111 = 3814667) B3814667
theorem B2543147 : Blo 1693547 2543147 := bstep (se 1 (by rfl) ⟨1907360, by rfl⟩ : syracuseStep 2543147 = 3814721) B3814721
theorem B2543177 : Blo 1693547 2543177 := bstep (se 2 (by rfl) ⟨953691, by rfl⟩ : syracuseStep 2543177 = 1907383) B1907383
theorem B3813011 : Blo 1693547 3813011 := bstep (se 1 (by rfl) ⟨2859758, by rfl⟩ : syracuseStep 3813011 = 5719517) B5719517
theorem B2543291 : Blo 1693547 2543291 := bstep (se 1 (by rfl) ⟨1907468, by rfl⟩ : syracuseStep 2543291 = 3814937) B3814937
theorem B3813065 : Blo 1693547 3813065 := bstep (se 2 (by rfl) ⟨1429899, by rfl⟩ : syracuseStep 3813065 = 2859799) B2859799
theorem B2035471 : Blo 1693547 2035471 := bstep (se 1 (by rfl) ⟨1526603, by rfl⟩ : syracuseStep 2035471 = 3053207) B3053207
theorem B2035499 : Blo 1693547 2035499 := bstep (se 1 (by rfl) ⟨1526624, by rfl⟩ : syracuseStep 2035499 = 3053249) B3053249
theorem B18321227 : Blo 1693547 18321227 := bstep (se 1 (by rfl) ⟨13740920, by rfl⟩ : syracuseStep 18321227 = 27481841) B27481841
theorem B4288403 : Blo 1693547 4288403 := bstep (se 1 (by rfl) ⟨3216302, by rfl⟩ : syracuseStep 4288403 = 6432605) B6432605
theorem B14479307 : Blo 1693547 14479307 := bstep (se 1 (by rfl) ⟨10859480, by rfl⟩ : syracuseStep 14479307 = 21718961) B21718961
theorem B4288697 : Blo 1693547 4288697 := bstep (se 2 (by rfl) ⟨1608261, by rfl⟩ : syracuseStep 4288697 = 3216523) B3216523
theorem B28233929 : Blo 1693547 28233929 := bstep (se 2 (by rfl) ⟨10587723, by rfl⟩ : syracuseStep 28233929 = 21175447) B21175447
theorem B61870321 : Blo 1693547 61870321 := bstep (se 2 (by rfl) ⟨23201370, by rfl⟩ : syracuseStep 61870321 = 46402741) B46402741
theorem B4960523 : Blo 1693547 4960523 := bstep (se 1 (by rfl) ⟨3720392, by rfl⟩ : syracuseStep 4960523 = 7440785) B7440785
theorem B3813767 : Blo 1693547 3813767 := bstep (se 1 (by rfl) ⟨2860325, by rfl⟩ : syracuseStep 3813767 = 5720651) B5720651
theorem B10301849 : Blo 1693547 10301849 := bstep (se 2 (by rfl) ⟨3863193, by rfl⟩ : syracuseStep 10301849 = 7726387) B7726387
theorem B3215801 : Blo 1693547 3215801 := bstep (se 2 (by rfl) ⟨1205925, by rfl⟩ : syracuseStep 3215801 = 2411851) B2411851
theorem B2412985 : Blo 1693547 2412985 := bstep (se 2 (by rfl) ⟨904869, by rfl⟩ : syracuseStep 2412985 = 1809739) B1809739
theorem B3813947 : Blo 1693547 3813947 := bstep (se 1 (by rfl) ⟨2860460, by rfl⟩ : syracuseStep 3813947 = 5720921) B5720921
theorem B14479991 : Blo 1693547 14479991 := bstep (se 1 (by rfl) ⟨10859993, by rfl⟩ : syracuseStep 14479991 = 21719987) B21719987
theorem B1905295 : Blo 1693547 1905295 := bstep (se 1 (by rfl) ⟨1428971, by rfl⟩ : syracuseStep 1905295 = 2857943) B2857943
theorem B3814073 : Blo 1693547 3814073 := bstep (se 2 (by rfl) ⟨1430277, by rfl⟩ : syracuseStep 3814073 = 2860555) B2860555
theorem B24761123 : Blo 1693547 24761123 := bstep (se 1 (by rfl) ⟨18570842, by rfl⟩ : syracuseStep 24761123 = 37141685) B37141685
theorem B2446139 : Blo 1693547 2446139 := bstep (se 1 (by rfl) ⟨1834604, by rfl⟩ : syracuseStep 2446139 = 3669209) B3669209
theorem B16282457 : Blo 1693547 16282457 := bstep (se 2 (by rfl) ⟨6105921, by rfl⟩ : syracuseStep 16282457 = 12211843) B12211843
theorem B4289395 : Blo 1693547 4289395 := bstep (se 1 (by rfl) ⟨3217046, by rfl⟩ : syracuseStep 4289395 = 6434093) B6434093
theorem B6435719 : Blo 1693547 6435719 := bstep (se 1 (by rfl) ⟨4826789, by rfl⟩ : syracuseStep 6435719 = 9653579) B9653579
theorem B8573849 : Blo 1693547 8573849 := bstep (se 2 (by rfl) ⟨3215193, by rfl⟩ : syracuseStep 8573849 = 6430387) B6430387
theorem B34780067 : Blo 1693547 34780067 := bstep (se 1 (by rfl) ⟨26085050, by rfl⟩ : syracuseStep 34780067 = 52170101) B52170101
theorem B4289537 : Blo 1693547 4289537 := bstep (se 2 (by rfl) ⟨1608576, by rfl⟩ : syracuseStep 4289537 = 3217153) B3217153
theorem B3814415 : Blo 1693547 3814415 := bstep (se 1 (by rfl) ⟨2860811, by rfl⟩ : syracuseStep 3814415 = 5721623) B5721623
theorem B3814433 : Blo 1693547 3814433 := bstep (se 2 (by rfl) ⟨1430412, by rfl⟩ : syracuseStep 3814433 = 2860825) B2860825
theorem B1905799 : Blo 1693547 1905799 := bstep (se 1 (by rfl) ⟨1429349, by rfl⟩ : syracuseStep 1905799 = 2858699) B2858699
theorem B9655469 : Blo 1693547 9655469 := bstep (se 3 (by rfl) ⟨1810400, by rfl⟩ : syracuseStep 9655469 = 3620801) B3620801
theorem B3052745 : Blo 1693547 3052745 := bstep (se 2 (by rfl) ⟨1144779, by rfl⟩ : syracuseStep 3052745 = 2289559) B2289559
theorem B12866849 : Blo 1693547 12866849 := bstep (se 2 (by rfl) ⟨4825068, by rfl⟩ : syracuseStep 12866849 = 9650137) B9650137
theorem B1905979 : Blo 1693547 1905979 := bstep (se 1 (by rfl) ⟨1429484, by rfl⟩ : syracuseStep 1905979 = 2858969) B2858969
theorem B3814775 : Blo 1693547 3814775 := bstep (se 1 (by rfl) ⟨2861081, by rfl⟩ : syracuseStep 3814775 = 5722163) B5722163
theorem B9647495 : Blo 1693547 9647495 := bstep (se 1 (by rfl) ⟨7235621, by rfl⟩ : syracuseStep 9647495 = 14471243) B14471243
theorem B8697233 : Blo 1693547 8697233 := bstep (se 2 (by rfl) ⟨3261462, by rfl⟩ : syracuseStep 8697233 = 6522925) B6522925
theorem B2143675 : Blo 1693547 2143675 := bstep (se 1 (by rfl) ⟨1607756, by rfl⟩ : syracuseStep 2143675 = 3215513) B3215513
theorem B4289993 : Blo 1693547 4289993 := bstep (se 2 (by rfl) ⟨1608747, by rfl⟩ : syracuseStep 4289993 = 3217495) B3217495
theorem B3814955 : Blo 1693547 3814955 := bstep (se 1 (by rfl) ⟨2861216, by rfl⟩ : syracuseStep 3814955 = 5722433) B5722433
theorem B1906447 : Blo 1693547 1906447 := bstep (se 1 (by rfl) ⟨1429835, by rfl⟩ : syracuseStep 1906447 = 2859671) B2859671
theorem B4069153 : Blo 1693547 4069153 := bstep (se 2 (by rfl) ⟨1525932, by rfl⟩ : syracuseStep 4069153 = 3051865) B3051865
theorem B4290347 : Blo 1693547 4290347 := bstep (se 1 (by rfl) ⟨3217760, by rfl⟩ : syracuseStep 4290347 = 6435521) B6435521
theorem B24418097 : Blo 1693547 24418097 := bstep (se 2 (by rfl) ⟨9156786, by rfl⟩ : syracuseStep 24418097 = 18313573) B18313573
theorem B1693575 : Blo 1693547 1693575 := bstep (se 1 (by rfl) ⟨1270181, by rfl⟩ : syracuseStep 1693575 = 2540363) B2540363
theorem B1693583 : Blo 1693547 1693583 := bstep (se 1 (by rfl) ⟨1270187, by rfl⟩ : syracuseStep 1693583 = 2540375) B2540375
theorem B2144171 : Blo 1693547 2144171 := bstep (se 1 (by rfl) ⟨1608128, by rfl⟩ : syracuseStep 2144171 = 3216257) B3216257
theorem B5429177 : Blo 1693547 5429177 := bstep (se 2 (by rfl) ⟨2035941, by rfl⟩ : syracuseStep 5429177 = 4071883) B4071883
theorem B1693627 : Blo 1693547 1693627 := bstep (se 1 (by rfl) ⟨1270220, by rfl⟩ : syracuseStep 1693627 = 2540441) B2540441
theorem B9164765 : Blo 1693547 9164765 := bstep (se 3 (by rfl) ⟨1718393, by rfl⟩ : syracuseStep 9164765 = 3436787) B3436787
theorem B1693703 : Blo 1693547 1693703 := bstep (se 1 (by rfl) ⟨1270277, by rfl⟩ : syracuseStep 1693703 = 2540555) B2540555
theorem B1693711 : Blo 1693547 1693711 := bstep (se 1 (by rfl) ⟨1270283, by rfl⟩ : syracuseStep 1693711 = 2540567) B2540567
theorem B1693755 : Blo 1693547 1693755 := bstep (se 1 (by rfl) ⟨1270316, by rfl⟩ : syracuseStep 1693755 = 2540633) B2540633
theorem B4823155 : Blo 1693547 4823155 := bstep (se 1 (by rfl) ⟨3617366, by rfl⟩ : syracuseStep 4823155 = 7234733) B7234733
theorem B4405367 : Blo 1693547 4405367 := bstep (se 1 (by rfl) ⟨3304025, by rfl⟩ : syracuseStep 4405367 = 6608051) B6608051
theorem B1693831 : Blo 1693547 1693831 := bstep (se 1 (by rfl) ⟨1270373, by rfl⟩ : syracuseStep 1693831 = 2540747) B2540747
theorem B1693839 : Blo 1693547 1693839 := bstep (se 1 (by rfl) ⟨1270379, by rfl⟩ : syracuseStep 1693839 = 2540759) B2540759
theorem B4069529 : Blo 1693547 4069529 := bstep (se 2 (by rfl) ⟨1526073, by rfl⟩ : syracuseStep 4069529 = 3052147) B3052147
theorem B1693883 : Blo 1693547 1693883 := bstep (se 1 (by rfl) ⟨1270412, by rfl⟩ : syracuseStep 1693883 = 2540825) B2540825
theorem B5716169 : Blo 1693547 5716169 := bstep (se 2 (by rfl) ⟨2143563, by rfl⟩ : syracuseStep 5716169 = 4287127) B4287127
theorem B4069577 : Blo 1693547 4069577 := bstep (se 2 (by rfl) ⟨1526091, by rfl⟩ : syracuseStep 4069577 = 3052183) B3052183
theorem B12867821 : Blo 1693547 12867821 := bstep (se 3 (by rfl) ⟨2412716, by rfl⟩ : syracuseStep 12867821 = 4825433) B4825433
theorem B1693959 : Blo 1693547 1693959 := bstep (se 1 (by rfl) ⟨1270469, by rfl⟩ : syracuseStep 1693959 = 2540939) B2540939
theorem B1906951 : Blo 1693547 1906951 := bstep (se 1 (by rfl) ⟨1430213, by rfl⟩ : syracuseStep 1906951 = 2860427) B2860427
theorem B1693967 : Blo 1693547 1693967 := bstep (se 1 (by rfl) ⟨1270475, by rfl⟩ : syracuseStep 1693967 = 2540951) B2540951
theorem B1694011 : Blo 1693547 1694011 := bstep (se 1 (by rfl) ⟨1270508, by rfl⟩ : syracuseStep 1694011 = 2541017) B2541017
theorem B4823383 : Blo 1693547 4823383 := bstep (se 1 (by rfl) ⟨3617537, by rfl⟩ : syracuseStep 4823383 = 7235075) B7235075
theorem B16316803 : Blo 1693547 16316803 := bstep (se 1 (by rfl) ⟨12237602, by rfl⟩ : syracuseStep 16316803 = 24475205) B24475205
theorem B1694087 : Blo 1693547 1694087 := bstep (se 1 (by rfl) ⟨1270565, by rfl⟩ : syracuseStep 1694087 = 2541131) B2541131
theorem B2144647 : Blo 1693547 2144647 := bstep (se 1 (by rfl) ⟨1608485, by rfl⟩ : syracuseStep 2144647 = 3216971) B3216971
theorem B3217799 : Blo 1693547 3217799 := bstep (se 1 (by rfl) ⟨2413349, by rfl⟩ : syracuseStep 3217799 = 4826699) B4826699
theorem B16513415 : Blo 1693547 16513415 := bstep (se 1 (by rfl) ⟨12385061, by rfl⟩ : syracuseStep 16513415 = 24770123) B24770123
theorem B1694095 : Blo 1693547 1694095 := bstep (se 1 (by rfl) ⟨1270571, by rfl⟩ : syracuseStep 1694095 = 2541143) B2541143
theorem B8583569 : Blo 1693547 8583569 := bstep (se 2 (by rfl) ⟨3218838, by rfl⟩ : syracuseStep 8583569 = 6437677) B6437677
theorem B8255891 : Blo 1693547 8255891 := bstep (se 1 (by rfl) ⟨6191918, by rfl⟩ : syracuseStep 8255891 = 12383837) B12383837
theorem B1694139 : Blo 1693547 1694139 := bstep (se 1 (by rfl) ⟨1270604, by rfl⟩ : syracuseStep 1694139 = 2541209) B2541209
theorem B1907131 : Blo 1693547 1907131 := bstep (se 1 (by rfl) ⟨1430348, by rfl⟩ : syracuseStep 1907131 = 2860697) B2860697
theorem B33479153 : Blo 1693547 33479153 := bstep (se 2 (by rfl) ⟨12554682, by rfl⟩ : syracuseStep 33479153 = 25109365) B25109365
theorem B1694215 : Blo 1693547 1694215 := bstep (se 1 (by rfl) ⟨1270661, by rfl⟩ : syracuseStep 1694215 = 2541323) B2541323
theorem B1694223 : Blo 1693547 1694223 := bstep (se 1 (by rfl) ⟨1270667, by rfl⟩ : syracuseStep 1694223 = 2541335) B2541335
theorem B1694267 : Blo 1693547 1694267 := bstep (se 1 (by rfl) ⟨1270700, by rfl⟩ : syracuseStep 1694267 = 2541401) B2541401
theorem B6437495 : Blo 1693547 6437495 := bstep (se 1 (by rfl) ⟨4828121, by rfl⟩ : syracuseStep 6437495 = 9656243) B9656243
theorem B3717767 : Blo 1693547 3717767 := bstep (se 1 (by rfl) ⟨2788325, by rfl⟩ : syracuseStep 3717767 = 5576651) B5576651
theorem B1694343 : Blo 1693547 1694343 := bstep (se 1 (by rfl) ⟨1270757, by rfl⟩ : syracuseStep 1694343 = 2541515) B2541515
theorem B1694351 : Blo 1693547 1694351 := bstep (se 1 (by rfl) ⟨1270763, by rfl⟩ : syracuseStep 1694351 = 2541527) B2541527
theorem B5151385 : Blo 1693547 5151385 := bstep (se 2 (by rfl) ⟨1931769, by rfl⟩ : syracuseStep 5151385 = 3863539) B3863539
theorem B1694395 : Blo 1693547 1694395 := bstep (se 1 (by rfl) ⟨1270796, by rfl⟩ : syracuseStep 1694395 = 2541593) B2541593
theorem B1694471 : Blo 1693547 1694471 := bstep (se 1 (by rfl) ⟨1270853, by rfl⟩ : syracuseStep 1694471 = 2541707) B2541707
theorem B4578059 : Blo 1693547 4578059 := bstep (se 1 (by rfl) ⟨3433544, by rfl⟩ : syracuseStep 4578059 = 6867089) B6867089
theorem B4291339 : Blo 1693547 4291339 := bstep (se 1 (by rfl) ⟨3218504, by rfl⟩ : syracuseStep 4291339 = 6437009) B6437009
theorem B1694479 : Blo 1693547 1694479 := bstep (se 1 (by rfl) ⟨1270859, by rfl⟩ : syracuseStep 1694479 = 2541719) B2541719
theorem B6871823 : Blo 1693547 6871823 := bstep (se 1 (by rfl) ⟨5153867, by rfl⟩ : syracuseStep 6871823 = 10307735) B10307735
theorem B1694523 : Blo 1693547 1694523 := bstep (se 1 (by rfl) ⟨1270892, by rfl⟩ : syracuseStep 1694523 = 2541785) B2541785
theorem B2145143 : Blo 1693547 2145143 := bstep (se 1 (by rfl) ⟨1608857, by rfl⟩ : syracuseStep 2145143 = 3217715) B3217715
theorem B5716871 : Blo 1693547 5716871 := bstep (se 1 (by rfl) ⟨4287653, by rfl⟩ : syracuseStep 5716871 = 8575307) B8575307
theorem B1694599 : Blo 1693547 1694599 := bstep (se 1 (by rfl) ⟨1270949, by rfl⟩ : syracuseStep 1694599 = 2541899) B2541899
theorem B1694607 : Blo 1693547 1694607 := bstep (se 1 (by rfl) ⟨1270955, by rfl⟩ : syracuseStep 1694607 = 2541911) B2541911
theorem B4291481 : Blo 1693547 4291481 := bstep (se 2 (by rfl) ⟨1609305, by rfl⟩ : syracuseStep 4291481 = 3218611) B3218611
theorem B3865529 : Blo 1693547 3865529 := bstep (se 2 (by rfl) ⟨1449573, by rfl⟩ : syracuseStep 3865529 = 2899147) B2899147
theorem B1694651 : Blo 1693547 1694651 := bstep (se 1 (by rfl) ⟨1270988, by rfl⟩ : syracuseStep 1694651 = 2541977) B2541977
theorem B1694727 : Blo 1693547 1694727 := bstep (se 1 (by rfl) ⟨1271045, by rfl⟩ : syracuseStep 1694727 = 2542091) B2542091
theorem B1694735 : Blo 1693547 1694735 := bstep (se 1 (by rfl) ⟨1271051, by rfl⟩ : syracuseStep 1694735 = 2542103) B2542103
theorem B2145295 : Blo 1693547 2145295 := bstep (se 1 (by rfl) ⟨1608971, by rfl⟩ : syracuseStep 2145295 = 3217943) B3217943
theorem B7240747 : Blo 1693547 7240747 := bstep (se 1 (by rfl) ⟨5430560, by rfl⟩ : syracuseStep 7240747 = 10861121) B10861121
theorem B1694779 : Blo 1693547 1694779 := bstep (se 1 (by rfl) ⟨1271084, by rfl⟩ : syracuseStep 1694779 = 2542169) B2542169
theorem B4291643 : Blo 1693547 4291643 := bstep (se 1 (by rfl) ⟨3218732, by rfl⟩ : syracuseStep 4291643 = 6437465) B6437465
theorem B1694855 : Blo 1693547 1694855 := bstep (se 1 (by rfl) ⟨1271141, by rfl⟩ : syracuseStep 1694855 = 2542283) B2542283
theorem B1694863 : Blo 1693547 1694863 := bstep (se 1 (by rfl) ⟨1271147, by rfl⟩ : syracuseStep 1694863 = 2542295) B2542295
theorem B1694907 : Blo 1693547 1694907 := bstep (se 1 (by rfl) ⟨1271180, by rfl⟩ : syracuseStep 1694907 = 2542361) B2542361
theorem B2145467 : Blo 1693547 2145467 := bstep (se 1 (by rfl) ⟨1609100, by rfl⟩ : syracuseStep 2145467 = 3218201) B3218201
theorem B17382637 : Blo 1693547 17382637 := bstep (se 3 (by rfl) ⟨3259244, by rfl⟩ : syracuseStep 17382637 = 6518489) B6518489
theorem B5717249 : Blo 1693547 5717249 := bstep (se 2 (by rfl) ⟨2143968, by rfl⟩ : syracuseStep 5717249 = 4287937) B4287937
theorem B1694983 : Blo 1693547 1694983 := bstep (se 1 (by rfl) ⟨1271237, by rfl⟩ : syracuseStep 1694983 = 2542475) B2542475
theorem B1694991 : Blo 1693547 1694991 := bstep (se 1 (by rfl) ⟨1271243, by rfl⟩ : syracuseStep 1694991 = 2542487) B2542487
theorem B1695035 : Blo 1693547 1695035 := bstep (se 1 (by rfl) ⟨1271276, by rfl⟩ : syracuseStep 1695035 = 2542553) B2542553
theorem B2858375 : Blo 1693547 2858375 := bstep (se 1 (by rfl) ⟨2143781, by rfl⟩ : syracuseStep 2858375 = 4287563) B4287563
theorem B1695111 : Blo 1693547 1695111 := bstep (se 1 (by rfl) ⟨1271333, by rfl⟩ : syracuseStep 1695111 = 2542667) B2542667
theorem B1695119 : Blo 1693547 1695119 := bstep (se 1 (by rfl) ⟨1271339, by rfl⟩ : syracuseStep 1695119 = 2542679) B2542679
theorem B4578707 : Blo 1693547 4578707 := bstep (se 1 (by rfl) ⟨3434030, by rfl⟩ : syracuseStep 4578707 = 6868061) B6868061
theorem B8576441 : Blo 1693547 8576441 := bstep (se 2 (by rfl) ⟨3216165, by rfl⟩ : syracuseStep 8576441 = 6432331) B6432331
theorem B1695163 : Blo 1693547 1695163 := bstep (se 1 (by rfl) ⟨1271372, by rfl⟩ : syracuseStep 1695163 = 2542745) B2542745
theorem B10862045 : Blo 1693547 10862045 := bstep (se 3 (by rfl) ⟨2036633, by rfl⟩ : syracuseStep 10862045 = 4073267) B4073267
theorem B1695239 : Blo 1693547 1695239 := bstep (se 1 (by rfl) ⟨1271429, by rfl⟩ : syracuseStep 1695239 = 2542859) B2542859
theorem B1695247 : Blo 1693547 1695247 := bstep (se 1 (by rfl) ⟨1271435, by rfl⟩ : syracuseStep 1695247 = 2542871) B2542871
theorem B12213803 : Blo 1693547 12213803 := bstep (se 1 (by rfl) ⟨9160352, by rfl⟩ : syracuseStep 12213803 = 18320705) B18320705
theorem B1695291 : Blo 1693547 1695291 := bstep (se 1 (by rfl) ⟨1271468, by rfl⟩ : syracuseStep 1695291 = 2542937) B2542937
theorem B1695367 : Blo 1693547 1695367 := bstep (se 1 (by rfl) ⟨1271525, by rfl⟩ : syracuseStep 1695367 = 2543051) B2543051
theorem B1695375 : Blo 1693547 1695375 := bstep (se 1 (by rfl) ⟨1271531, by rfl⟩ : syracuseStep 1695375 = 2543063) B2543063
theorem B35266225 : Blo 1693547 35266225 := bstep (se 2 (by rfl) ⟨13224834, by rfl⟩ : syracuseStep 35266225 = 26449669) B26449669
theorem B1695419 : Blo 1693547 1695419 := bstep (se 1 (by rfl) ⟨1271564, by rfl⟩ : syracuseStep 1695419 = 2543129) B2543129
theorem B1810183 : Blo 1693547 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B1695495 : Blo 1693547 1695495 := bstep (se 1 (by rfl) ⟨1271621, by rfl⟩ : syracuseStep 1695495 = 2543243) B2543243
theorem B1695503 : Blo 1693547 1695503 := bstep (se 1 (by rfl) ⟨1271627, by rfl⟩ : syracuseStep 1695503 = 2543255) B2543255
theorem B1695547 : Blo 1693547 1695547 := bstep (se 1 (by rfl) ⟨1271660, by rfl⟩ : syracuseStep 1695547 = 2543321) B2543321
theorem B16514891 : Blo 1693547 16514891 := bstep (se 1 (by rfl) ⟨12386168, by rfl⟩ : syracuseStep 16514891 = 24772337) B24772337
theorem B18816857 : Blo 1693547 18816857 := bstep (se 2 (by rfl) ⟨7056321, by rfl⟩ : syracuseStep 18816857 = 14112643) B14112643
theorem B4824967 : Blo 1693547 4824967 := bstep (se 1 (by rfl) ⟨3618725, by rfl⟩ : syracuseStep 4824967 = 7237451) B7237451
theorem B42360893 : Blo 1693547 42360893 := bstep (se 3 (by rfl) ⟨7942667, by rfl⟩ : syracuseStep 42360893 = 15885335) B15885335
theorem B2859131 : Blo 1693547 2859131 := bstep (se 1 (by rfl) ⟨2144348, by rfl⟩ : syracuseStep 2859131 = 4288697) B4288697
theorem B6430873 : Blo 1693547 6430873 := bstep (se 2 (by rfl) ⟨2411577, by rfl⟩ : syracuseStep 6430873 = 4823155) B4823155
theorem B2900167 : Blo 1693547 2900167 := bstep (se 1 (by rfl) ⟨2175125, by rfl⟩ : syracuseStep 2900167 = 4350251) B4350251
theorem B82493761 : Blo 1693547 82493761 := bstep (se 2 (by rfl) ⟨30935160, by rfl⟩ : syracuseStep 82493761 = 61870321) B61870321
theorem B6431177 : Blo 1693547 6431177 := bstep (se 2 (by rfl) ⟨2411691, by rfl⟩ : syracuseStep 6431177 = 4823383) B4823383
theorem B5718491 : Blo 1693547 5718491 := bstep (se 1 (by rfl) ⟨4288868, by rfl⟩ : syracuseStep 5718491 = 8577737) B8577737
theorem B2859529 : Blo 1693547 2859529 := bstep (se 2 (by rfl) ⟨1072323, by rfl⟩ : syracuseStep 2859529 = 2144647) B2144647
theorem B16507415 : Blo 1693547 16507415 := bstep (se 1 (by rfl) ⟨12380561, by rfl⟩ : syracuseStep 16507415 = 24761123) B24761123
theorem B10854971 : Blo 1693547 10854971 := bstep (se 1 (by rfl) ⟨8141228, by rfl⟩ : syracuseStep 10854971 = 16282457) B16282457
theorem B2859691 : Blo 1693547 2859691 := bstep (se 1 (by rfl) ⟨2144768, by rfl⟩ : syracuseStep 2859691 = 4289537) B4289537
theorem B11010761 : Blo 1693547 11010761 := bstep (se 2 (by rfl) ⟨4129035, by rfl⟩ : syracuseStep 11010761 = 8258071) B8258071
theorem B6521555 : Blo 1693547 6521555 := bstep (se 1 (by rfl) ⟨4891166, by rfl⟩ : syracuseStep 6521555 = 9782333) B9782333
theorem B2540393 : Blo 1693547 2540393 := bstep (se 2 (by rfl) ⟨952647, by rfl⟩ : syracuseStep 2540393 = 1905295) B1905295
theorem B8577899 : Blo 1693547 8577899 := bstep (se 1 (by rfl) ⟨6433424, by rfl⟩ : syracuseStep 8577899 = 12866849) B12866849
theorem B6431663 : Blo 1693547 6431663 := bstep (se 1 (by rfl) ⟨4823747, by rfl⟩ : syracuseStep 6431663 = 9647495) B9647495
theorem B2540471 : Blo 1693547 2540471 := bstep (se 1 (by rfl) ⟨1905353, by rfl⟩ : syracuseStep 2540471 = 3810707) B3810707
theorem B2540507 : Blo 1693547 2540507 := bstep (se 1 (by rfl) ⟨1905380, by rfl⟩ : syracuseStep 2540507 = 3810761) B3810761
theorem B2859995 : Blo 1693547 2859995 := bstep (se 1 (by rfl) ⟨2144996, by rfl⟩ : syracuseStep 2859995 = 4289993) B4289993
theorem B9290771 : Blo 1693547 9290771 := bstep (se 1 (by rfl) ⟨6968078, by rfl⟩ : syracuseStep 9290771 = 13936157) B13936157
theorem B5719193 : Blo 1693547 5719193 := bstep (se 2 (by rfl) ⟨2144697, by rfl⟩ : syracuseStep 5719193 = 4289395) B4289395
theorem B2860231 : Blo 1693547 2860231 := bstep (se 1 (by rfl) ⟨2145173, by rfl⟩ : syracuseStep 2860231 = 4290347) B4290347
theorem B16278731 : Blo 1693547 16278731 := bstep (se 1 (by rfl) ⟨12209048, by rfl⟩ : syracuseStep 16278731 = 24418097) B24418097
theorem B92800241 : Blo 1693547 92800241 := bstep (se 2 (by rfl) ⟨34800090, by rfl⟩ : syracuseStep 92800241 = 69600181) B69600181
theorem B2860393 : Blo 1693547 2860393 := bstep (se 2 (by rfl) ⟨1072647, by rfl⟩ : syracuseStep 2860393 = 2145295) B2145295
theorem B2540975 : Blo 1693547 2540975 := bstep (se 1 (by rfl) ⟨1905731, by rfl⟩ : syracuseStep 2540975 = 3811463) B3811463
theorem B2713019 : Blo 1693547 2713019 := bstep (se 1 (by rfl) ⟨2034764, by rfl⟩ : syracuseStep 2713019 = 4069529) B4069529
theorem B18834889 : Blo 1693547 18834889 := bstep (se 2 (by rfl) ⟨7063083, by rfl⟩ : syracuseStep 18834889 = 14126167) B14126167
theorem B3810779 : Blo 1693547 3810779 := bstep (se 1 (by rfl) ⟨2858084, by rfl⟩ : syracuseStep 3810779 = 5716169) B5716169
theorem B2713051 : Blo 1693547 2713051 := bstep (se 1 (by rfl) ⟨2034788, by rfl⟩ : syracuseStep 2713051 = 4069577) B4069577
theorem B8578547 : Blo 1693547 8578547 := bstep (se 1 (by rfl) ⟨6433910, by rfl⟩ : syracuseStep 8578547 = 12867821) B12867821
theorem B2541065 : Blo 1693547 2541065 := bstep (se 2 (by rfl) ⟨952899, by rfl⟩ : syracuseStep 2541065 = 1905799) B1905799
theorem B2541095 : Blo 1693547 2541095 := bstep (se 1 (by rfl) ⟨1905821, by rfl⟩ : syracuseStep 2541095 = 3811643) B3811643
theorem B2541179 : Blo 1693547 2541179 := bstep (se 1 (by rfl) ⟨1905884, by rfl⟩ : syracuseStep 2541179 = 3811769) B3811769
theorem B23176849 : Blo 1693547 23176849 := bstep (se 2 (by rfl) ⟨8691318, by rfl⟩ : syracuseStep 23176849 = 17382637) B17382637
theorem B2541305 : Blo 1693547 2541305 := bstep (se 2 (by rfl) ⟨952989, by rfl⟩ : syracuseStep 2541305 = 1905979) B1905979
theorem B4581193 : Blo 1693547 4581193 := bstep (se 2 (by rfl) ⟨1717947, by rfl⟩ : syracuseStep 4581193 = 3435895) B3435895
theorem B2541407 : Blo 1693547 2541407 := bstep (se 1 (by rfl) ⟨1906055, by rfl⟩ : syracuseStep 2541407 = 3812111) B3812111
theorem B4581215 : Blo 1693547 4581215 := bstep (se 1 (by rfl) ⟨3435911, by rfl⟩ : syracuseStep 4581215 = 6871823) B6871823
theorem B2541419 : Blo 1693547 2541419 := bstep (se 1 (by rfl) ⟨1906064, by rfl⟩ : syracuseStep 2541419 = 3812129) B3812129
theorem B18311021 : Blo 1693547 18311021 := bstep (se 3 (by rfl) ⟨3433316, by rfl⟩ : syracuseStep 18311021 = 6866633) B6866633
theorem B3811247 : Blo 1693547 3811247 := bstep (se 1 (by rfl) ⟨2858435, by rfl⟩ : syracuseStep 3811247 = 5716871) B5716871
theorem B2860987 : Blo 1693547 2860987 := bstep (se 1 (by rfl) ⟨2145740, by rfl⟩ : syracuseStep 2860987 = 4291481) B4291481
theorem B12871709 : Blo 1693547 12871709 := bstep (se 3 (by rfl) ⟨2413445, by rfl⟩ : syracuseStep 12871709 = 4826891) B4826891
theorem B2861095 : Blo 1693547 2861095 := bstep (se 1 (by rfl) ⟨2145821, by rfl⟩ : syracuseStep 2861095 = 4291643) B4291643
theorem B2541647 : Blo 1693547 2541647 := bstep (se 1 (by rfl) ⟨1906235, by rfl⟩ : syracuseStep 2541647 = 3812471) B3812471
theorem B6523037 : Blo 1693547 6523037 := bstep (se 3 (by rfl) ⟨1223069, by rfl⟩ : syracuseStep 6523037 = 2446139) B2446139
theorem B3811499 : Blo 1693547 3811499 := bstep (se 1 (by rfl) ⟨2858624, by rfl⟩ : syracuseStep 3811499 = 5717249) B5717249
theorem B2541767 : Blo 1693547 2541767 := bstep (se 1 (by rfl) ⟨1906325, by rfl⟩ : syracuseStep 2541767 = 3812651) B3812651
theorem B5720381 : Blo 1693547 5720381 := bstep (se 3 (by rfl) ⟨1072571, by rfl⟩ : syracuseStep 5720381 = 2145143) B2145143
theorem B2713961 : Blo 1693547 2713961 := bstep (se 2 (by rfl) ⟨1017735, by rfl⟩ : syracuseStep 2713961 = 2035471) B2035471
theorem B2541929 : Blo 1693547 2541929 := bstep (se 2 (by rfl) ⟨953223, by rfl⟩ : syracuseStep 2541929 = 1906447) B1906447
theorem B5425537 : Blo 1693547 5425537 := bstep (se 2 (by rfl) ⟨2034576, by rfl⟩ : syracuseStep 5425537 = 4069153) B4069153
theorem B2542007 : Blo 1693547 2542007 := bstep (se 1 (by rfl) ⟨1906505, by rfl⟩ : syracuseStep 2542007 = 3813011) B3813011
theorem B2542043 : Blo 1693547 2542043 := bstep (se 1 (by rfl) ⟨1906532, by rfl⟩ : syracuseStep 2542043 = 3813065) B3813065
theorem B6433289 : Blo 1693547 6433289 := bstep (se 2 (by rfl) ⟨2412483, by rfl⟩ : syracuseStep 6433289 = 4824967) B4824967
theorem B12544571 : Blo 1693547 12544571 := bstep (se 1 (by rfl) ⟨9408428, by rfl⟩ : syracuseStep 12544571 = 18816857) B18816857
theorem B9652871 : Blo 1693547 9652871 := bstep (se 1 (by rfl) ⟨7239653, by rfl⟩ : syracuseStep 9652871 = 14479307) B14479307
theorem B6187709 : Blo 1693547 6187709 := bstep (se 3 (by rfl) ⟨1160195, by rfl⟩ : syracuseStep 6187709 = 2320391) B2320391
theorem B3812039 : Blo 1693547 3812039 := bstep (se 1 (by rfl) ⟨2859029, by rfl⟩ : syracuseStep 3812039 = 5718059) B5718059
theorem B8579843 : Blo 1693547 8579843 := bstep (se 1 (by rfl) ⟨6434882, by rfl⟩ : syracuseStep 8579843 = 12869765) B12869765
theorem B2542511 : Blo 1693547 2542511 := bstep (se 1 (by rfl) ⟨1906883, by rfl⟩ : syracuseStep 2542511 = 3813767) B3813767
theorem B6867899 : Blo 1693547 6867899 := bstep (se 1 (by rfl) ⟨5150924, by rfl⟩ : syracuseStep 6867899 = 10301849) B10301849
theorem B2542601 : Blo 1693547 2542601 := bstep (se 2 (by rfl) ⟨953475, by rfl⟩ : syracuseStep 2542601 = 1906951) B1906951
theorem B2542631 : Blo 1693547 2542631 := bstep (se 1 (by rfl) ⟨1906973, by rfl⟩ : syracuseStep 2542631 = 3813947) B3813947
theorem B9653327 : Blo 1693547 9653327 := bstep (se 1 (by rfl) ⟨7239995, by rfl⟩ : syracuseStep 9653327 = 14479991) B14479991
theorem B21711989 : Blo 1693547 21711989 := bstep (se 5 (by rfl) ⟨1017749, by rfl⟩ : syracuseStep 21711989 = 2035499) B2035499
theorem B2542715 : Blo 1693547 2542715 := bstep (se 1 (by rfl) ⟨1907036, by rfl⟩ : syracuseStep 2542715 = 3814073) B3814073
theorem B5721245 : Blo 1693547 5721245 := bstep (se 3 (by rfl) ⟨1072733, by rfl⟩ : syracuseStep 5721245 = 2145467) B2145467
theorem B2542841 : Blo 1693547 2542841 := bstep (se 2 (by rfl) ⟨953565, by rfl⟩ : syracuseStep 2542841 = 1907131) B1907131
theorem B23186711 : Blo 1693547 23186711 := bstep (se 1 (by rfl) ⟨17390033, by rfl⟩ : syracuseStep 23186711 = 34780067) B34780067
theorem B2542943 : Blo 1693547 2542943 := bstep (se 1 (by rfl) ⟨1907207, by rfl⟩ : syracuseStep 2542943 = 3814415) B3814415
theorem B2542955 : Blo 1693547 2542955 := bstep (se 1 (by rfl) ⟨1907216, by rfl⟩ : syracuseStep 2542955 = 3814433) B3814433
theorem B6188413 : Blo 1693547 6188413 := bstep (se 3 (by rfl) ⟨1160327, by rfl⟩ : syracuseStep 6188413 = 2320655) B2320655
theorem B7236989 : Blo 1693547 7236989 := bstep (se 3 (by rfl) ⟨1356935, by rfl⟩ : syracuseStep 7236989 = 2713871) B2713871
theorem B4287887 : Blo 1693547 4287887 := bstep (se 1 (by rfl) ⟨3215915, by rfl⟩ : syracuseStep 4287887 = 6431831) B6431831
theorem B2035163 : Blo 1693547 2035163 := bstep (se 1 (by rfl) ⟨1526372, by rfl⟩ : syracuseStep 2035163 = 3052745) B3052745
theorem B6868513 : Blo 1693547 6868513 := bstep (se 2 (by rfl) ⟨2575692, by rfl⟩ : syracuseStep 6868513 = 5151385) B5151385
theorem B3812903 : Blo 1693547 3812903 := bstep (se 1 (by rfl) ⟨2859677, by rfl⟩ : syracuseStep 3812903 = 5719355) B5719355
theorem B10858045 : Blo 1693547 10858045 := bstep (se 3 (by rfl) ⟨2035883, by rfl⟩ : syracuseStep 10858045 = 4071767) B4071767
theorem B2543183 : Blo 1693547 2543183 := bstep (se 1 (by rfl) ⟨1907387, by rfl⟩ : syracuseStep 2543183 = 3814775) B3814775
theorem B6524513 : Blo 1693547 6524513 := bstep (se 2 (by rfl) ⟨2446692, by rfl⟩ : syracuseStep 6524513 = 4893385) B4893385
theorem B5721785 : Blo 1693547 5721785 := bstep (se 2 (by rfl) ⟨2145669, by rfl⟩ : syracuseStep 5721785 = 4291339) B4291339
theorem B2543303 : Blo 1693547 2543303 := bstep (se 1 (by rfl) ⟨1907477, by rfl⟩ : syracuseStep 2543303 = 3814955) B3814955
theorem B4288211 : Blo 1693547 4288211 := bstep (se 1 (by rfl) ⟨3216158, by rfl⟩ : syracuseStep 4288211 = 6432317) B6432317
theorem B12209885 : Blo 1693547 12209885 := bstep (se 3 (by rfl) ⟨2289353, by rfl⟩ : syracuseStep 12209885 = 4578707) B4578707
theorem B22015709 : Blo 1693547 22015709 := bstep (se 3 (by rfl) ⟨4127945, by rfl⟩ : syracuseStep 22015709 = 8255891) B8255891
theorem B2715383 : Blo 1693547 2715383 := bstep (se 1 (by rfl) ⟨2036537, by rfl⟩ : syracuseStep 2715383 = 4073075) B4073075
theorem B3215209 : Blo 1693547 3215209 := bstep (se 2 (by rfl) ⟨1205703, by rfl⟩ : syracuseStep 3215209 = 2411407) B2411407
theorem B3813227 : Blo 1693547 3813227 := bstep (se 1 (by rfl) ⟨2859920, by rfl⟩ : syracuseStep 3813227 = 5719841) B5719841
theorem B3813281 : Blo 1693547 3813281 := bstep (se 2 (by rfl) ⟨1429980, by rfl⟩ : syracuseStep 3813281 = 2859961) B2859961
theorem B6434747 : Blo 1693547 6434747 := bstep (se 1 (by rfl) ⟨4826060, by rfl⟩ : syracuseStep 6434747 = 9652121) B9652121
theorem B3215369 : Blo 1693547 3215369 := bstep (se 2 (by rfl) ⟨1205763, by rfl⟩ : syracuseStep 3215369 = 2411527) B2411527
theorem B9654329 : Blo 1693547 9654329 := bstep (se 2 (by rfl) ⟨3620373, by rfl⟩ : syracuseStep 9654329 = 7240747) B7240747
theorem B2936911 : Blo 1693547 2936911 := bstep (se 1 (by rfl) ⟨2202683, by rfl⟩ : syracuseStep 2936911 = 4405367) B4405367
theorem B3813623 : Blo 1693547 3813623 := bstep (se 1 (by rfl) ⟨2860217, by rfl⟩ : syracuseStep 3813623 = 5720435) B5720435
theorem B5722379 : Blo 1693547 5722379 := bstep (se 1 (by rfl) ⟨4291784, by rfl⟩ : syracuseStep 5722379 = 8583569) B8583569
theorem B22319435 : Blo 1693547 22319435 := bstep (se 1 (by rfl) ⟨16739576, by rfl⟩ : syracuseStep 22319435 = 33479153) B33479153
theorem B8581463 : Blo 1693547 8581463 := bstep (se 1 (by rfl) ⟨6436097, by rfl⟩ : syracuseStep 8581463 = 12872195) B12872195
theorem B2478511 : Blo 1693547 2478511 := bstep (se 1 (by rfl) ⟨1858883, by rfl⟩ : syracuseStep 2478511 = 3717767) B3717767
theorem B3052039 : Blo 1693547 3052039 := bstep (se 1 (by rfl) ⟨2289029, by rfl⟩ : syracuseStep 3052039 = 4578059) B4578059
theorem B2577019 : Blo 1693547 2577019 := bstep (se 1 (by rfl) ⟨1932764, by rfl⟩ : syracuseStep 2577019 = 3865529) B3865529
theorem B5796541 : Blo 1693547 5796541 := bstep (se 3 (by rfl) ⟨1086851, by rfl⟩ : syracuseStep 5796541 = 2173703) B2173703
theorem B3814217 : Blo 1693547 3814217 := bstep (se 2 (by rfl) ⟨1430331, by rfl⟩ : syracuseStep 3814217 = 2860663) B2860663
theorem B4289375 : Blo 1693547 4289375 := bstep (se 1 (by rfl) ⟨3217031, by rfl⟩ : syracuseStep 4289375 = 6434063) B6434063
theorem B1905583 : Blo 1693547 1905583 := bstep (se 1 (by rfl) ⟨1429187, by rfl⟩ : syracuseStep 1905583 = 2858375) B2858375
theorem B2413577 : Blo 1693547 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B1906015 : Blo 1693547 1906015 := bstep (se 1 (by rfl) ⟨1429511, by rfl⟩ : syracuseStep 1906015 = 2859023) B2859023
theorem B41211281 : Blo 1693547 41211281 := bstep (se 2 (by rfl) ⟨15454230, by rfl⟩ : syracuseStep 41211281 = 30908461) B30908461
theorem B3216827 : Blo 1693547 3216827 := bstep (se 1 (by rfl) ⟨2412620, by rfl⟩ : syracuseStep 3216827 = 4825241) B4825241
theorem B18822619 : Blo 1693547 18822619 := bstep (se 1 (by rfl) ⟨14116964, by rfl⟩ : syracuseStep 18822619 = 28233929) B28233929
theorem B3307015 : Blo 1693547 3307015 := bstep (se 1 (by rfl) ⟨2480261, by rfl⟩ : syracuseStep 3307015 = 4960523) B4960523
theorem B1906375 : Blo 1693547 1906375 := bstep (se 1 (by rfl) ⟨1429781, by rfl⟩ : syracuseStep 1906375 = 2859563) B2859563
theorem B14473019 : Blo 1693547 14473019 := bstep (se 1 (by rfl) ⟨10854764, by rfl⟩ : syracuseStep 14473019 = 21709529) B21709529
theorem B21755737 : Blo 1693547 21755737 := bstep (se 2 (by rfl) ⟨8158401, by rfl⟩ : syracuseStep 21755737 = 16316803) B16316803
theorem B3217259 : Blo 1693547 3217259 := bstep (se 1 (by rfl) ⟨2412944, by rfl⟩ : syracuseStep 3217259 = 4825889) B4825889
theorem B1693563 : Blo 1693547 1693563 := bstep (se 1 (by rfl) ⟨1270172, by rfl⟩ : syracuseStep 1693563 = 2540345) B2540345
theorem B3217313 : Blo 1693547 3217313 := bstep (se 2 (by rfl) ⟨1206492, by rfl⟩ : syracuseStep 3217313 = 2412985) B2412985
theorem B25114529 : Blo 1693547 25114529 := bstep (se 2 (by rfl) ⟨9417948, by rfl⟩ : syracuseStep 25114529 = 18835897) B18835897
theorem B1693615 : Blo 1693547 1693615 := bstep (se 1 (by rfl) ⟨1270211, by rfl⟩ : syracuseStep 1693615 = 2540423) B2540423
theorem B4290479 : Blo 1693547 4290479 := bstep (se 1 (by rfl) ⟨3217859, by rfl⟩ : syracuseStep 4290479 = 6435719) B6435719
theorem B5715899 : Blo 1693547 5715899 := bstep (se 1 (by rfl) ⟨4286924, by rfl⟩ : syracuseStep 5715899 = 8573849) B8573849
theorem B4069307 : Blo 1693547 4069307 := bstep (se 1 (by rfl) ⟨3051980, by rfl⟩ : syracuseStep 4069307 = 6103961) B6103961
theorem B1693639 : Blo 1693547 1693639 := bstep (se 1 (by rfl) ⟨1270229, by rfl⟩ : syracuseStep 1693639 = 2540459) B2540459
theorem B1693659 : Blo 1693547 1693659 := bstep (se 1 (by rfl) ⟨1270244, by rfl⟩ : syracuseStep 1693659 = 2540489) B2540489
theorem B8574983 : Blo 1693547 8574983 := bstep (se 1 (by rfl) ⟨6431237, by rfl⟩ : syracuseStep 8574983 = 12862475) B12862475
theorem B1693735 : Blo 1693547 1693735 := bstep (se 1 (by rfl) ⟨1270301, by rfl⟩ : syracuseStep 1693735 = 2540603) B2540603
theorem B1693775 : Blo 1693547 1693775 := bstep (se 1 (by rfl) ⟨1270331, by rfl⟩ : syracuseStep 1693775 = 2540663) B2540663
theorem B1693791 : Blo 1693547 1693791 := bstep (se 1 (by rfl) ⟨1270343, by rfl⟩ : syracuseStep 1693791 = 2540687) B2540687
theorem B6436979 : Blo 1693547 6436979 := bstep (se 1 (by rfl) ⟨4827734, by rfl⟩ : syracuseStep 6436979 = 9655469) B9655469
theorem B1693819 : Blo 1693547 1693819 := bstep (se 1 (by rfl) ⟨1270364, by rfl⟩ : syracuseStep 1693819 = 2540729) B2540729
theorem B1693871 : Blo 1693547 1693871 := bstep (se 1 (by rfl) ⟨1270403, by rfl⟩ : syracuseStep 1693871 = 2540807) B2540807
theorem B1693895 : Blo 1693547 1693895 := bstep (se 1 (by rfl) ⟨1270421, by rfl⟩ : syracuseStep 1693895 = 2540843) B2540843
theorem B1693915 : Blo 1693547 1693915 := bstep (se 1 (by rfl) ⟨1270436, by rfl⟩ : syracuseStep 1693915 = 2540873) B2540873
theorem B5798155 : Blo 1693547 5798155 := bstep (se 1 (by rfl) ⟨4348616, by rfl⟩ : syracuseStep 5798155 = 8697233) B8697233
theorem B1693991 : Blo 1693547 1693991 := bstep (se 1 (by rfl) ⟨1270493, by rfl⟩ : syracuseStep 1693991 = 2540987) B2540987
theorem B1694031 : Blo 1693547 1694031 := bstep (se 1 (by rfl) ⟨1270523, by rfl⟩ : syracuseStep 1694031 = 2541047) B2541047
theorem B1694047 : Blo 1693547 1694047 := bstep (se 1 (by rfl) ⟨1270535, by rfl⟩ : syracuseStep 1694047 = 2541071) B2541071
theorem B1694075 : Blo 1693547 1694075 := bstep (se 1 (by rfl) ⟨1270556, by rfl⟩ : syracuseStep 1694075 = 2541113) B2541113
theorem B1694127 : Blo 1693547 1694127 := bstep (se 1 (by rfl) ⟨1270595, by rfl⟩ : syracuseStep 1694127 = 2541191) B2541191
theorem B3053999 : Blo 1693547 3053999 := bstep (se 1 (by rfl) ⟨2290499, by rfl⟩ : syracuseStep 3053999 = 4580999) B4580999
theorem B1694151 : Blo 1693547 1694151 := bstep (se 1 (by rfl) ⟨1270613, by rfl⟩ : syracuseStep 1694151 = 2541227) B2541227
theorem B1694171 : Blo 1693547 1694171 := bstep (se 1 (by rfl) ⟨1270628, by rfl⟩ : syracuseStep 1694171 = 2541257) B2541257
theorem B8575469 : Blo 1693547 8575469 := bstep (se 3 (by rfl) ⟨1607900, by rfl⟩ : syracuseStep 8575469 = 3215801) B3215801
theorem B1694247 : Blo 1693547 1694247 := bstep (se 1 (by rfl) ⟨1270685, by rfl⟩ : syracuseStep 1694247 = 2541371) B2541371
theorem B1907239 : Blo 1693547 1907239 := bstep (se 1 (by rfl) ⟨1430429, by rfl⟩ : syracuseStep 1907239 = 2860859) B2860859
theorem B1694287 : Blo 1693547 1694287 := bstep (se 1 (by rfl) ⟨1270715, by rfl⟩ : syracuseStep 1694287 = 2541431) B2541431
theorem B1694303 : Blo 1693547 1694303 := bstep (se 1 (by rfl) ⟨1270727, by rfl⟩ : syracuseStep 1694303 = 2541455) B2541455
theorem B1694331 : Blo 1693547 1694331 := bstep (se 1 (by rfl) ⟨1270748, by rfl⟩ : syracuseStep 1694331 = 2541497) B2541497
theorem B3619451 : Blo 1693547 3619451 := bstep (se 1 (by rfl) ⟨2714588, by rfl⟩ : syracuseStep 3619451 = 5429177) B5429177
theorem B6109843 : Blo 1693547 6109843 := bstep (se 1 (by rfl) ⟨4582382, by rfl⟩ : syracuseStep 6109843 = 9164765) B9164765
theorem B1694383 : Blo 1693547 1694383 := bstep (se 1 (by rfl) ⟨1270787, by rfl⟩ : syracuseStep 1694383 = 2541575) B2541575
theorem B1694407 : Blo 1693547 1694407 := bstep (se 1 (by rfl) ⟨1270805, by rfl⟩ : syracuseStep 1694407 = 2541611) B2541611
theorem B12868307 : Blo 1693547 12868307 := bstep (se 1 (by rfl) ⟨9651230, by rfl⟩ : syracuseStep 12868307 = 19302461) B19302461
theorem B1694427 : Blo 1693547 1694427 := bstep (se 1 (by rfl) ⟨1270820, by rfl⟩ : syracuseStep 1694427 = 2541641) B2541641
theorem B1694503 : Blo 1693547 1694503 := bstep (se 1 (by rfl) ⟨1270877, by rfl⟩ : syracuseStep 1694503 = 2541755) B2541755
theorem B1694543 : Blo 1693547 1694543 := bstep (se 1 (by rfl) ⟨1270907, by rfl⟩ : syracuseStep 1694543 = 2541815) B2541815
theorem B1694559 : Blo 1693547 1694559 := bstep (se 1 (by rfl) ⟨1270919, by rfl⟩ : syracuseStep 1694559 = 2541839) B2541839
theorem B1694587 : Blo 1693547 1694587 := bstep (se 1 (by rfl) ⟨1270940, by rfl⟩ : syracuseStep 1694587 = 2541881) B2541881
theorem B1694639 : Blo 1693547 1694639 := bstep (se 1 (by rfl) ⟨1270979, by rfl⟩ : syracuseStep 1694639 = 2541959) B2541959
theorem B2145199 : Blo 1693547 2145199 := bstep (se 1 (by rfl) ⟨1608899, by rfl⟩ : syracuseStep 2145199 = 3217799) B3217799
theorem B11008943 : Blo 1693547 11008943 := bstep (se 1 (by rfl) ⟨8256707, by rfl⟩ : syracuseStep 11008943 = 16513415) B16513415
theorem B5430203 : Blo 1693547 5430203 := bstep (se 1 (by rfl) ⟨4072652, by rfl⟩ : syracuseStep 5430203 = 8145305) B8145305
theorem B1694663 : Blo 1693547 1694663 := bstep (se 1 (by rfl) ⟨1270997, by rfl⟩ : syracuseStep 1694663 = 2541995) B2541995
theorem B1694683 : Blo 1693547 1694683 := bstep (se 1 (by rfl) ⟨1271012, by rfl⟩ : syracuseStep 1694683 = 2542025) B2542025
theorem B24427493 : Blo 1693547 24427493 := bstep (se 4 (by rfl) ⟨2290077, by rfl⟩ : syracuseStep 24427493 = 4580155) B4580155
theorem B1694759 : Blo 1693547 1694759 := bstep (se 1 (by rfl) ⟨1271069, by rfl⟩ : syracuseStep 1694759 = 2542139) B2542139
theorem B1694799 : Blo 1693547 1694799 := bstep (se 1 (by rfl) ⟨1271099, by rfl⟩ : syracuseStep 1694799 = 2542199) B2542199
theorem B4291663 : Blo 1693547 4291663 := bstep (se 1 (by rfl) ⟨3218747, by rfl⟩ : syracuseStep 4291663 = 6437495) B6437495
theorem B1694815 : Blo 1693547 1694815 := bstep (se 1 (by rfl) ⟨1271111, by rfl⟩ : syracuseStep 1694815 = 2542223) B2542223
theorem B1694843 : Blo 1693547 1694843 := bstep (se 1 (by rfl) ⟨1271132, by rfl⟩ : syracuseStep 1694843 = 2542265) B2542265
theorem B1694895 : Blo 1693547 1694895 := bstep (se 1 (by rfl) ⟨1271171, by rfl⟩ : syracuseStep 1694895 = 2542343) B2542343
theorem B1694919 : Blo 1693547 1694919 := bstep (se 1 (by rfl) ⟨1271189, by rfl⟩ : syracuseStep 1694919 = 2542379) B2542379
theorem B1694939 : Blo 1693547 1694939 := bstep (se 1 (by rfl) ⟨1271204, by rfl⟩ : syracuseStep 1694939 = 2542409) B2542409
theorem B2858233 : Blo 1693547 2858233 := bstep (se 2 (by rfl) ⟨1071837, by rfl⟩ : syracuseStep 2858233 = 2143675) B2143675
theorem B8576279 : Blo 1693547 8576279 := bstep (se 1 (by rfl) ⟨6432209, by rfl⟩ : syracuseStep 8576279 = 12864419) B12864419
theorem B1695015 : Blo 1693547 1695015 := bstep (se 1 (by rfl) ⟨1271261, by rfl⟩ : syracuseStep 1695015 = 2542523) B2542523
theorem B1695055 : Blo 1693547 1695055 := bstep (se 1 (by rfl) ⟨1271291, by rfl⟩ : syracuseStep 1695055 = 2542583) B2542583
theorem B1695071 : Blo 1693547 1695071 := bstep (se 1 (by rfl) ⟨1271303, by rfl⟩ : syracuseStep 1695071 = 2542607) B2542607
theorem B1695099 : Blo 1693547 1695099 := bstep (se 1 (by rfl) ⟨1271324, by rfl⟩ : syracuseStep 1695099 = 2542649) B2542649
theorem B1695151 : Blo 1693547 1695151 := bstep (se 1 (by rfl) ⟨1271363, by rfl⟩ : syracuseStep 1695151 = 2542727) B2542727
theorem B1695175 : Blo 1693547 1695175 := bstep (se 1 (by rfl) ⟨1271381, by rfl⟩ : syracuseStep 1695175 = 2542763) B2542763
theorem B1695195 : Blo 1693547 1695195 := bstep (se 1 (by rfl) ⟨1271396, by rfl⟩ : syracuseStep 1695195 = 2542793) B2542793
theorem B2858503 : Blo 1693547 2858503 := bstep (se 1 (by rfl) ⟨2143877, by rfl⟩ : syracuseStep 2858503 = 4287755) B4287755
theorem B5430817 : Blo 1693547 5430817 := bstep (se 2 (by rfl) ⟨2036556, by rfl⟩ : syracuseStep 5430817 = 4073113) B4073113
theorem B1695271 : Blo 1693547 1695271 := bstep (se 1 (by rfl) ⟨1271453, by rfl⟩ : syracuseStep 1695271 = 2542907) B2542907
theorem B47021633 : Blo 1693547 47021633 := bstep (se 2 (by rfl) ⟨17633112, by rfl⟩ : syracuseStep 47021633 = 35266225) B35266225
theorem B1695311 : Blo 1693547 1695311 := bstep (se 1 (by rfl) ⟨1271483, by rfl⟩ : syracuseStep 1695311 = 2542967) B2542967
theorem B1695327 : Blo 1693547 1695327 := bstep (se 1 (by rfl) ⟨1271495, by rfl⟩ : syracuseStep 1695327 = 2542991) B2542991
theorem B5717627 : Blo 1693547 5717627 := bstep (se 1 (by rfl) ⟨4288220, by rfl⟩ : syracuseStep 5717627 = 8576441) B8576441
theorem B1695355 : Blo 1693547 1695355 := bstep (se 1 (by rfl) ⟨1271516, by rfl⟩ : syracuseStep 1695355 = 2543033) B2543033
theorem B7241363 : Blo 1693547 7241363 := bstep (se 1 (by rfl) ⟨5431022, by rfl⟩ : syracuseStep 7241363 = 10862045) B10862045
theorem B1695407 : Blo 1693547 1695407 := bstep (se 1 (by rfl) ⟨1271555, by rfl⟩ : syracuseStep 1695407 = 2543111) B2543111
theorem B8142535 : Blo 1693547 8142535 := bstep (se 1 (by rfl) ⟨6106901, by rfl⟩ : syracuseStep 8142535 = 12213803) B12213803
theorem B1695431 : Blo 1693547 1695431 := bstep (se 1 (by rfl) ⟨1271573, by rfl⟩ : syracuseStep 1695431 = 2543147) B2543147
theorem B1695451 : Blo 1693547 1695451 := bstep (se 1 (by rfl) ⟨1271588, by rfl⟩ : syracuseStep 1695451 = 2543177) B2543177
theorem B11001593 : Blo 1693547 11001593 := bstep (se 2 (by rfl) ⟨4125597, by rfl⟩ : syracuseStep 11001593 = 8251195) B8251195
theorem B5717789 : Blo 1693547 5717789 := bstep (se 3 (by rfl) ⟨1072085, by rfl⟩ : syracuseStep 5717789 = 2144171) B2144171
theorem B1695527 : Blo 1693547 1695527 := bstep (se 1 (by rfl) ⟨1271645, by rfl⟩ : syracuseStep 1695527 = 2543291) B2543291
theorem B12214151 : Blo 1693547 12214151 := bstep (se 1 (by rfl) ⟨9160613, by rfl⟩ : syracuseStep 12214151 = 18321227) B18321227
theorem B11009927 : Blo 1693547 11009927 := bstep (se 1 (by rfl) ⟨8257445, by rfl⟩ : syracuseStep 11009927 = 16514891) B16514891
theorem B2858935 : Blo 1693547 2858935 := bstep (se 1 (by rfl) ⟨2144201, by rfl⟩ : syracuseStep 2858935 = 4288403) B4288403
theorem B3915881 : Blo 1693547 3915881 := bstep (se 2 (by rfl) ⟨1468455, by rfl⟩ : syracuseStep 3915881 = 2936911) B2936911
theorem B7340507 : Blo 1693547 7340507 := bstep (se 1 (by rfl) ⟨5505380, by rfl⟩ : syracuseStep 7340507 = 11010761) B11010761
theorem B7234049 : Blo 1693547 7234049 := bstep (se 2 (by rfl) ⟨2712768, by rfl⟩ : syracuseStep 7234049 = 5425537) B5425537
theorem B2859583 : Blo 1693547 2859583 := bstep (se 1 (by rfl) ⟨2144687, by rfl⟩ : syracuseStep 2859583 = 4289375) B4289375
theorem B5718599 : Blo 1693547 5718599 := bstep (se 1 (by rfl) ⟨4288949, by rfl⟩ : syracuseStep 5718599 = 8577899) B8577899
theorem B6193847 : Blo 1693547 6193847 := bstep (se 1 (by rfl) ⟨4645385, by rfl⟩ : syracuseStep 6193847 = 9290771) B9290771
theorem B61866827 : Blo 1693547 61866827 := bstep (se 1 (by rfl) ⟨46400120, by rfl⟩ : syracuseStep 61866827 = 92800241) B92800241
theorem B2540519 : Blo 1693547 2540519 := bstep (se 1 (by rfl) ⟨1905389, by rfl⟩ : syracuseStep 2540519 = 3810779) B3810779
theorem B5719031 : Blo 1693547 5719031 := bstep (se 1 (by rfl) ⟨4289273, by rfl⟩ : syracuseStep 5719031 = 8578547) B8578547
theorem B15467557 : Blo 1693547 15467557 := bstep (se 4 (by rfl) ⟨1450083, by rfl⟩ : syracuseStep 15467557 = 2900167) B2900167
theorem B7234717 : Blo 1693547 7234717 := bstep (se 3 (by rfl) ⟨1356509, by rfl⟩ : syracuseStep 7234717 = 2713019) B2713019
theorem B2540777 : Blo 1693547 2540777 := bstep (se 2 (by rfl) ⟨952791, by rfl⟩ : syracuseStep 2540777 = 1905583) B1905583
theorem B2860265 : Blo 1693547 2860265 := bstep (se 2 (by rfl) ⟨1072599, by rfl⟩ : syracuseStep 2860265 = 2145199) B2145199
theorem B12207347 : Blo 1693547 12207347 := bstep (se 1 (by rfl) ⟨9155510, by rfl⟩ : syracuseStep 12207347 = 18311021) B18311021
theorem B2540831 : Blo 1693547 2540831 := bstep (se 1 (by rfl) ⟨1905623, by rfl⟩ : syracuseStep 2540831 = 3811247) B3811247
theorem B2860319 : Blo 1693547 2860319 := bstep (se 1 (by rfl) ⟨2145239, by rfl⟩ : syracuseStep 2860319 = 4290479) B4290479
theorem B3810599 : Blo 1693547 3810599 := bstep (se 1 (by rfl) ⟨2857949, by rfl⟩ : syracuseStep 3810599 = 5715899) B5715899
theorem B2712871 : Blo 1693547 2712871 := bstep (se 1 (by rfl) ⟨2034653, by rfl⟩ : syracuseStep 2712871 = 4069307) B4069307
theorem B2540999 : Blo 1693547 2540999 := bstep (se 1 (by rfl) ⟨1905749, by rfl⟩ : syracuseStep 2540999 = 3811499) B3811499
theorem B9651869 : Blo 1693547 9651869 := bstep (se 3 (by rfl) ⟨1809725, by rfl⟩ : syracuseStep 9651869 = 3619451) B3619451
theorem B3810977 : Blo 1693547 3810977 := bstep (se 2 (by rfl) ⟨1429116, by rfl⟩ : syracuseStep 3810977 = 2858233) B2858233
theorem B2541353 : Blo 1693547 2541353 := bstep (se 2 (by rfl) ⟨953007, by rfl⟩ : syracuseStep 2541353 = 1906015) B1906015
theorem B2541359 : Blo 1693547 2541359 := bstep (se 1 (by rfl) ⟨1906019, by rfl⟩ : syracuseStep 2541359 = 3812039) B3812039
theorem B8578871 : Blo 1693547 8578871 := bstep (se 1 (by rfl) ⟨6434153, by rfl⟩ : syracuseStep 8578871 = 12868307) B12868307
theorem B16500557 : Blo 1693547 16500557 := bstep (se 3 (by rfl) ⟨3093854, by rfl⟩ : syracuseStep 16500557 = 6187709) B6187709
theorem B8251217 : Blo 1693547 8251217 := bstep (se 2 (by rfl) ⟨3094206, by rfl⟩ : syracuseStep 8251217 = 6188413) B6188413
theorem B5719895 : Blo 1693547 5719895 := bstep (se 1 (by rfl) ⟨4289921, by rfl⟩ : syracuseStep 5719895 = 8579843) B8579843
theorem B3811337 : Blo 1693547 3811337 := bstep (se 2 (by rfl) ⟨1429251, by rfl⟩ : syracuseStep 3811337 = 2858503) B2858503
theorem B4409353 : Blo 1693547 4409353 := bstep (se 2 (by rfl) ⟨1653507, by rfl⟩ : syracuseStep 4409353 = 3307015) B3307015
theorem B14477393 : Blo 1693547 14477393 := bstep (se 2 (by rfl) ⟨5429022, by rfl⟩ : syracuseStep 14477393 = 10858045) B10858045
theorem B30902465 : Blo 1693547 30902465 := bstep (se 2 (by rfl) ⟨11588424, by rfl⟩ : syracuseStep 30902465 = 23176849) B23176849
theorem B10856713 : Blo 1693547 10856713 := bstep (se 2 (by rfl) ⟨4071267, by rfl⟩ : syracuseStep 10856713 = 8142535) B8142535
theorem B2541833 : Blo 1693547 2541833 := bstep (se 2 (by rfl) ⟨953187, by rfl⟩ : syracuseStep 2541833 = 1906375) B1906375
theorem B8579357 : Blo 1693547 8579357 := bstep (se 3 (by rfl) ⟨1608629, by rfl⟩ : syracuseStep 8579357 = 3217259) B3217259
theorem B2541935 : Blo 1693547 2541935 := bstep (se 1 (by rfl) ⟨1906451, by rfl⟩ : syracuseStep 2541935 = 3812903) B3812903
theorem B3811751 : Blo 1693547 3811751 := bstep (se 1 (by rfl) ⟨2858813, by rfl⟩ : syracuseStep 3811751 = 5717627) B5717627
theorem B4827575 : Blo 1693547 4827575 := bstep (se 1 (by rfl) ⟨3620681, by rfl⟩ : syracuseStep 4827575 = 7241363) B7241363
theorem B4286945 : Blo 1693547 4286945 := bstep (se 2 (by rfl) ⟨1607604, by rfl⟩ : syracuseStep 4286945 = 3215209) B3215209
theorem B7334395 : Blo 1693547 7334395 := bstep (se 1 (by rfl) ⟨5500796, by rfl⟩ : syracuseStep 7334395 = 11001593) B11001593
theorem B3811859 : Blo 1693547 3811859 := bstep (se 1 (by rfl) ⟨2858894, by rfl⟩ : syracuseStep 3811859 = 5717789) B5717789
theorem B2542151 : Blo 1693547 2542151 := bstep (se 1 (by rfl) ⟨1906613, by rfl⟩ : syracuseStep 2542151 = 3813227) B3813227
theorem B3811913 : Blo 1693547 3811913 := bstep (se 2 (by rfl) ⟨1429467, by rfl⟩ : syracuseStep 3811913 = 2858935) B2858935
theorem B2542187 : Blo 1693547 2542187 := bstep (se 1 (by rfl) ⟨1906640, by rfl⟩ : syracuseStep 2542187 = 3813281) B3813281
theorem B28240595 : Blo 1693547 28240595 := bstep (se 1 (by rfl) ⟨21180446, by rfl⟩ : syracuseStep 28240595 = 42360893) B42360893
theorem B2542415 : Blo 1693547 2542415 := bstep (se 1 (by rfl) ⟨1906811, by rfl⟩ : syracuseStep 2542415 = 3813623) B3813623
theorem B14879623 : Blo 1693547 14879623 := bstep (se 1 (by rfl) ⟨11159717, by rfl⟩ : syracuseStep 14879623 = 22319435) B22319435
theorem B5720975 : Blo 1693547 5720975 := bstep (se 1 (by rfl) ⟨4290731, by rfl⟩ : syracuseStep 5720975 = 8581463) B8581463
theorem B4287451 : Blo 1693547 4287451 := bstep (se 1 (by rfl) ⟨3215588, by rfl⟩ : syracuseStep 4287451 = 6431177) B6431177
theorem B3812327 : Blo 1693547 3812327 := bstep (se 1 (by rfl) ⟨2859245, by rfl⟩ : syracuseStep 3812327 = 5718491) B5718491
theorem B11004943 : Blo 1693547 11004943 := bstep (se 1 (by rfl) ⟨8253707, by rfl⟩ : syracuseStep 11004943 = 16507415) B16507415
theorem B7236647 : Blo 1693547 7236647 := bstep (se 1 (by rfl) ⟨5427485, by rfl⟩ : syracuseStep 7236647 = 10854971) B10854971
theorem B2542811 : Blo 1693547 2542811 := bstep (se 1 (by rfl) ⟨1907108, by rfl⟩ : syracuseStep 2542811 = 3814217) B3814217
theorem B3304681 : Blo 1693547 3304681 := bstep (se 2 (by rfl) ⟨1239255, by rfl⟩ : syracuseStep 3304681 = 2478511) B2478511
theorem B4287775 : Blo 1693547 4287775 := bstep (se 1 (by rfl) ⟨3215831, by rfl⟩ : syracuseStep 4287775 = 6431663) B6431663
theorem B3812705 : Blo 1693547 3812705 := bstep (se 2 (by rfl) ⟨1429764, by rfl⟩ : syracuseStep 3812705 = 2859529) B2859529
theorem B2542985 : Blo 1693547 2542985 := bstep (se 2 (by rfl) ⟨953619, by rfl⟩ : syracuseStep 2542985 = 1907239) B1907239
theorem B3812795 : Blo 1693547 3812795 := bstep (se 1 (by rfl) ⟨2859596, by rfl⟩ : syracuseStep 3812795 = 5719193) B5719193
theorem B3436025 : Blo 1693547 3436025 := bstep (se 2 (by rfl) ⟨1288509, by rfl⟩ : syracuseStep 3436025 = 2577019) B2577019
theorem B8146457 : Blo 1693547 8146457 := bstep (se 2 (by rfl) ⟨3054921, by rfl⟩ : syracuseStep 8146457 = 6109843) B6109843
theorem B3812921 : Blo 1693547 3812921 := bstep (se 2 (by rfl) ⟨1429845, by rfl⟩ : syracuseStep 3812921 = 2859691) B2859691
theorem B5427101 : Blo 1693547 5427101 := bstep (se 3 (by rfl) ⟨1017581, by rfl⟩ : syracuseStep 5427101 = 2035163) B2035163
theorem B8581139 : Blo 1693547 8581139 := bstep (se 1 (by rfl) ⟨6435854, by rfl⟩ : syracuseStep 8581139 = 12871709) B12871709
theorem B5722217 : Blo 1693547 5722217 := bstep (se 2 (by rfl) ⟨2145831, by rfl⟩ : syracuseStep 5722217 = 4291663) B4291663
theorem B3813587 : Blo 1693547 3813587 := bstep (se 1 (by rfl) ⟨2860190, by rfl⟩ : syracuseStep 3813587 = 5720381) B5720381
theorem B3813641 : Blo 1693547 3813641 := bstep (se 2 (by rfl) ⟨1430115, by rfl⟩ : syracuseStep 3813641 = 2860231) B2860231
theorem B2035999 : Blo 1693547 2035999 := bstep (se 1 (by rfl) ⟨1526999, by rfl⟩ : syracuseStep 2035999 = 3053999) B3053999
theorem B4288859 : Blo 1693547 4288859 := bstep (se 1 (by rfl) ⟨3216644, by rfl⟩ : syracuseStep 4288859 = 6433289) B6433289
theorem B6435247 : Blo 1693547 6435247 := bstep (se 1 (by rfl) ⟨4826435, by rfl⟩ : syracuseStep 6435247 = 9652871) B9652871
theorem B3813857 : Blo 1693547 3813857 := bstep (se 2 (by rfl) ⟨1430196, by rfl⟩ : syracuseStep 3813857 = 2860393) B2860393
theorem B25113185 : Blo 1693547 25113185 := bstep (se 2 (by rfl) ⟨9417444, by rfl⟩ : syracuseStep 25113185 = 18834889) B18834889
theorem B3617401 : Blo 1693547 3617401 := bstep (se 2 (by rfl) ⟨1356525, by rfl⟩ : syracuseStep 3617401 = 2713051) B2713051
theorem B25096825 : Blo 1693547 25096825 := bstep (se 2 (by rfl) ⟨9411309, by rfl⟩ : syracuseStep 25096825 = 18822619) B18822619
theorem B6435551 : Blo 1693547 6435551 := bstep (se 1 (by rfl) ⟨4826663, by rfl⟩ : syracuseStep 6435551 = 9653327) B9653327
theorem B3814163 : Blo 1693547 3814163 := bstep (se 1 (by rfl) ⟨2860622, by rfl⟩ : syracuseStep 3814163 = 5721245) B5721245
theorem B31347755 : Blo 1693547 31347755 := bstep (se 1 (by rfl) ⟨23510816, by rfl⟩ : syracuseStep 31347755 = 47021633) B47021633
theorem B6108257 : Blo 1693547 6108257 := bstep (se 2 (by rfl) ⟨2290596, by rfl⟩ : syracuseStep 6108257 = 4581193) B4581193
theorem B3814523 : Blo 1693547 3814523 := bstep (se 1 (by rfl) ⟨2860892, by rfl⟩ : syracuseStep 3814523 = 5721785) B5721785
theorem B8139923 : Blo 1693547 8139923 := bstep (se 1 (by rfl) ⟨6104942, by rfl⟩ : syracuseStep 8139923 = 12209885) B12209885
theorem B14677139 : Blo 1693547 14677139 := bstep (se 1 (by rfl) ⟨11007854, by rfl⟩ : syracuseStep 14677139 = 22015709) B22015709
theorem B3814649 : Blo 1693547 3814649 := bstep (se 2 (by rfl) ⟨1430493, by rfl⟩ : syracuseStep 3814649 = 2860987) B2860987
theorem B4289831 : Blo 1693547 4289831 := bstep (se 1 (by rfl) ⟨3217373, by rfl⟩ : syracuseStep 4289831 = 6434747) B6434747
theorem B2143579 : Blo 1693547 2143579 := bstep (se 1 (by rfl) ⟨1607684, by rfl⟩ : syracuseStep 2143579 = 3215369) B3215369
theorem B6436205 : Blo 1693547 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B6436219 : Blo 1693547 6436219 := bstep (se 1 (by rfl) ⟨4827164, by rfl⟩ : syracuseStep 6436219 = 9654329) B9654329
theorem B3814793 : Blo 1693547 3814793 := bstep (se 2 (by rfl) ⟨1430547, by rfl⟩ : syracuseStep 3814793 = 2861095) B2861095
theorem B1906087 : Blo 1693547 1906087 := bstep (se 1 (by rfl) ⟨1429565, by rfl⟩ : syracuseStep 1906087 = 2859131) B2859131
theorem B3814919 : Blo 1693547 3814919 := bstep (se 1 (by rfl) ⟨2861189, by rfl⟩ : syracuseStep 3814919 = 5722379) B5722379
theorem B8574497 : Blo 1693547 8574497 := bstep (se 2 (by rfl) ⟨3215436, by rfl⟩ : syracuseStep 8574497 = 6430873) B6430873
theorem B7730873 : Blo 1693547 7730873 := bstep (se 2 (by rfl) ⟨2899077, by rfl⟩ : syracuseStep 7730873 = 5798155) B5798155
theorem B109991681 : Blo 1693547 109991681 := bstep (se 2 (by rfl) ⟨41246880, by rfl⟩ : syracuseStep 109991681 = 82493761) B82493761
theorem B4347703 : Blo 1693547 4347703 := bstep (se 1 (by rfl) ⟨3260777, by rfl⟩ : syracuseStep 4347703 = 6521555) B6521555
theorem B1693595 : Blo 1693547 1693595 := bstep (se 1 (by rfl) ⟨1270196, by rfl⟩ : syracuseStep 1693595 = 2540393) B2540393
theorem B1693647 : Blo 1693547 1693647 := bstep (se 1 (by rfl) ⟨1270235, by rfl⟩ : syracuseStep 1693647 = 2540471) B2540471
theorem B1693671 : Blo 1693547 1693671 := bstep (se 1 (by rfl) ⟨1270253, by rfl⟩ : syracuseStep 1693671 = 2540507) B2540507
theorem B1906663 : Blo 1693547 1906663 := bstep (se 1 (by rfl) ⟨1429997, by rfl⟩ : syracuseStep 1906663 = 2859995) B2859995
theorem B4069385 : Blo 1693547 4069385 := bstep (se 2 (by rfl) ⟨1526019, by rfl⟩ : syracuseStep 4069385 = 3052039) B3052039
theorem B10852487 : Blo 1693547 10852487 := bstep (se 1 (by rfl) ⟨8139365, by rfl⟩ : syracuseStep 10852487 = 16278731) B16278731
theorem B27474187 : Blo 1693547 27474187 := bstep (se 1 (by rfl) ⟨20605640, by rfl⟩ : syracuseStep 27474187 = 41211281) B41211281
theorem B1693983 : Blo 1693547 1693983 := bstep (se 1 (by rfl) ⟨1270487, by rfl⟩ : syracuseStep 1693983 = 2540975) B2540975
theorem B2144551 : Blo 1693547 2144551 := bstep (se 1 (by rfl) ⟨1608413, by rfl⟩ : syracuseStep 2144551 = 3216827) B3216827
theorem B30914885 : Blo 1693547 30914885 := bstep (se 4 (by rfl) ⟨2898270, by rfl⟩ : syracuseStep 30914885 = 5796541) B5796541
theorem B1694043 : Blo 1693547 1694043 := bstep (se 1 (by rfl) ⟨1270532, by rfl⟩ : syracuseStep 1694043 = 2541065) B2541065
theorem B1694063 : Blo 1693547 1694063 := bstep (se 1 (by rfl) ⟨1270547, by rfl⟩ : syracuseStep 1694063 = 2541095) B2541095
theorem B1694119 : Blo 1693547 1694119 := bstep (se 1 (by rfl) ⟨1270589, by rfl⟩ : syracuseStep 1694119 = 2541179) B2541179
theorem B1694203 : Blo 1693547 1694203 := bstep (se 1 (by rfl) ⟨1270652, by rfl⟩ : syracuseStep 1694203 = 2541305) B2541305
theorem B9648679 : Blo 1693547 9648679 := bstep (se 1 (by rfl) ⟨7236509, by rfl⟩ : syracuseStep 9648679 = 14473019) B14473019
theorem B1694271 : Blo 1693547 1694271 := bstep (se 1 (by rfl) ⟨1270703, by rfl⟩ : syracuseStep 1694271 = 2541407) B2541407
theorem B3054143 : Blo 1693547 3054143 := bstep (se 1 (by rfl) ⟨2290607, by rfl⟩ : syracuseStep 3054143 = 4581215) B4581215
theorem B1694279 : Blo 1693547 1694279 := bstep (se 1 (by rfl) ⟨1270709, by rfl⟩ : syracuseStep 1694279 = 2541419) B2541419
theorem B2144875 : Blo 1693547 2144875 := bstep (se 1 (by rfl) ⟨1608656, by rfl⟩ : syracuseStep 2144875 = 3217313) B3217313
theorem B16743019 : Blo 1693547 16743019 := bstep (se 1 (by rfl) ⟨12557264, by rfl⟩ : syracuseStep 16743019 = 25114529) B25114529
theorem B5716655 : Blo 1693547 5716655 := bstep (se 1 (by rfl) ⟨4287491, by rfl⟩ : syracuseStep 5716655 = 8574983) B8574983
theorem B1694431 : Blo 1693547 1694431 := bstep (se 1 (by rfl) ⟨1270823, by rfl⟩ : syracuseStep 1694431 = 2541647) B2541647
theorem B4291319 : Blo 1693547 4291319 := bstep (se 1 (by rfl) ⟨3218489, by rfl⟩ : syracuseStep 4291319 = 6436979) B6436979
theorem B4348691 : Blo 1693547 4348691 := bstep (se 1 (by rfl) ⟨3261518, by rfl⟩ : syracuseStep 4348691 = 6523037) B6523037
theorem B1694511 : Blo 1693547 1694511 := bstep (se 1 (by rfl) ⟨1270883, by rfl⟩ : syracuseStep 1694511 = 2541767) B2541767
theorem B1809307 : Blo 1693547 1809307 := bstep (se 1 (by rfl) ⟨1356980, by rfl⟩ : syracuseStep 1809307 = 2713961) B2713961
theorem B1694619 : Blo 1693547 1694619 := bstep (se 1 (by rfl) ⟨1270964, by rfl⟩ : syracuseStep 1694619 = 2541929) B2541929
theorem B1694671 : Blo 1693547 1694671 := bstep (se 1 (by rfl) ⟨1271003, by rfl⟩ : syracuseStep 1694671 = 2542007) B2542007
theorem B1694695 : Blo 1693547 1694695 := bstep (se 1 (by rfl) ⟨1271021, by rfl⟩ : syracuseStep 1694695 = 2542043) B2542043
theorem B5716979 : Blo 1693547 5716979 := bstep (se 1 (by rfl) ⟨4287734, by rfl⟩ : syracuseStep 5716979 = 8575469) B8575469
theorem B8363047 : Blo 1693547 8363047 := bstep (se 1 (by rfl) ⟨6272285, by rfl⟩ : syracuseStep 8363047 = 12544571) B12544571
theorem B1695007 : Blo 1693547 1695007 := bstep (se 1 (by rfl) ⟨1271255, by rfl⟩ : syracuseStep 1695007 = 2542511) B2542511
theorem B7339295 : Blo 1693547 7339295 := bstep (se 1 (by rfl) ⟨5504471, by rfl⟩ : syracuseStep 7339295 = 11008943) B11008943
theorem B4578599 : Blo 1693547 4578599 := bstep (se 1 (by rfl) ⟨3433949, by rfl⟩ : syracuseStep 4578599 = 6867899) B6867899
theorem B3620135 : Blo 1693547 3620135 := bstep (se 1 (by rfl) ⟨2715101, by rfl⟩ : syracuseStep 3620135 = 5430203) B5430203
theorem B7241021 : Blo 1693547 7241021 := bstep (se 3 (by rfl) ⟨1357691, by rfl⟩ : syracuseStep 7241021 = 2715383) B2715383
theorem B16284995 : Blo 1693547 16284995 := bstep (se 1 (by rfl) ⟨12213746, by rfl⟩ : syracuseStep 16284995 = 24427493) B24427493
theorem B1695067 : Blo 1693547 1695067 := bstep (se 1 (by rfl) ⟨1271300, by rfl⟩ : syracuseStep 1695067 = 2542601) B2542601
theorem B1695087 : Blo 1693547 1695087 := bstep (se 1 (by rfl) ⟨1271315, by rfl⟩ : syracuseStep 1695087 = 2542631) B2542631
theorem B9158017 : Blo 1693547 9158017 := bstep (se 2 (by rfl) ⟨3434256, by rfl⟩ : syracuseStep 9158017 = 6868513) B6868513
theorem B7241089 : Blo 1693547 7241089 := bstep (se 2 (by rfl) ⟨2715408, by rfl⟩ : syracuseStep 7241089 = 5430817) B5430817
theorem B14474659 : Blo 1693547 14474659 := bstep (se 1 (by rfl) ⟨10855994, by rfl⟩ : syracuseStep 14474659 = 21711989) B21711989
theorem B1695143 : Blo 1693547 1695143 := bstep (se 1 (by rfl) ⟨1271357, by rfl⟩ : syracuseStep 1695143 = 2542715) B2542715
theorem B1695227 : Blo 1693547 1695227 := bstep (se 1 (by rfl) ⟨1271420, by rfl⟩ : syracuseStep 1695227 = 2542841) B2542841
theorem B5717519 : Blo 1693547 5717519 := bstep (se 1 (by rfl) ⟨4288139, by rfl⟩ : syracuseStep 5717519 = 8576279) B8576279
theorem B15457807 : Blo 1693547 15457807 := bstep (se 1 (by rfl) ⟨11593355, by rfl⟩ : syracuseStep 15457807 = 23186711) B23186711
theorem B1695295 : Blo 1693547 1695295 := bstep (se 1 (by rfl) ⟨1271471, by rfl⟩ : syracuseStep 1695295 = 2542943) B2542943
theorem B1695303 : Blo 1693547 1695303 := bstep (se 1 (by rfl) ⟨1271477, by rfl⟩ : syracuseStep 1695303 = 2542955) B2542955
theorem B4824659 : Blo 1693547 4824659 := bstep (se 1 (by rfl) ⟨3618494, by rfl⟩ : syracuseStep 4824659 = 7236989) B7236989
theorem B2858591 : Blo 1693547 2858591 := bstep (se 1 (by rfl) ⟨2143943, by rfl⟩ : syracuseStep 2858591 = 4287887) B4287887
theorem B1695455 : Blo 1693547 1695455 := bstep (se 1 (by rfl) ⟨1271591, by rfl⟩ : syracuseStep 1695455 = 2543183) B2543183
theorem B4349675 : Blo 1693547 4349675 := bstep (se 1 (by rfl) ⟨3262256, by rfl⟩ : syracuseStep 4349675 = 6524513) B6524513
theorem B29007649 : Blo 1693547 29007649 := bstep (se 2 (by rfl) ⟨10877868, by rfl⟩ : syracuseStep 29007649 = 21755737) B21755737
theorem B1695535 : Blo 1693547 1695535 := bstep (se 1 (by rfl) ⟨1271651, by rfl⟩ : syracuseStep 1695535 = 2543303) B2543303
theorem B2858807 : Blo 1693547 2858807 := bstep (se 1 (by rfl) ⟨2144105, by rfl⟩ : syracuseStep 2858807 = 4288211) B4288211
theorem B8142767 : Blo 1693547 8142767 := bstep (se 1 (by rfl) ⟨6107075, by rfl⟩ : syracuseStep 8142767 = 12214151) B12214151
theorem B7339951 : Blo 1693547 7339951 := bstep (se 1 (by rfl) ⟨5504963, by rfl⟩ : syracuseStep 7339951 = 11009927) B11009927
theorem B2859239 : Blo 1693547 2859239 := bstep (se 1 (by rfl) ⟨2144429, by rfl⟩ : syracuseStep 2859239 = 4288859) B4288859
theorem B14475617 : Blo 1693547 14475617 := bstep (se 2 (by rfl) ⟨5428356, by rfl⟩ : syracuseStep 14475617 = 10856713) B10856713
theorem B2859401 : Blo 1693547 2859401 := bstep (se 2 (by rfl) ⟨1072275, by rfl⟩ : syracuseStep 2859401 = 2144551) B2144551
theorem B4129231 : Blo 1693547 4129231 := bstep (se 1 (by rfl) ⟨3096923, by rfl⟩ : syracuseStep 4129231 = 6193847) B6193847
theorem B20898503 : Blo 1693547 20898503 := bstep (se 1 (by rfl) ⟨15673877, by rfl⟩ : syracuseStep 20898503 = 31347755) B31347755
theorem B19571453 : Blo 1693547 19571453 := bstep (se 3 (by rfl) ⟨3669647, by rfl⟩ : syracuseStep 19571453 = 7339295) B7339295
theorem B2859833 : Blo 1693547 2859833 := bstep (se 2 (by rfl) ⟨1072437, by rfl⟩ : syracuseStep 2859833 = 2144875) B2144875
theorem B22324025 : Blo 1693547 22324025 := bstep (se 2 (by rfl) ⟨8371509, by rfl⟩ : syracuseStep 22324025 = 16743019) B16743019
theorem B2540399 : Blo 1693547 2540399 := bstep (se 1 (by rfl) ⟨1905299, by rfl⟩ : syracuseStep 2540399 = 3810599) B3810599
theorem B2859887 : Blo 1693547 2859887 := bstep (se 1 (by rfl) ⟨2144915, by rfl⟩ : syracuseStep 2859887 = 4289831) B4289831
theorem B2540651 : Blo 1693547 2540651 := bstep (se 1 (by rfl) ⟨1905488, by rfl⟩ : syracuseStep 2540651 = 3810977) B3810977
theorem B5153915 : Blo 1693547 5153915 := bstep (se 1 (by rfl) ⟨3865436, by rfl⟩ : syracuseStep 5153915 = 7730873) B7730873
theorem B73327787 : Blo 1693547 73327787 := bstep (se 1 (by rfl) ⟨54995840, by rfl⟩ : syracuseStep 73327787 = 109991681) B109991681
theorem B5719247 : Blo 1693547 5719247 := bstep (se 1 (by rfl) ⟨4289435, by rfl⟩ : syracuseStep 5719247 = 8578871) B8578871
theorem B2712923 : Blo 1693547 2712923 := bstep (se 1 (by rfl) ⟨2034692, by rfl⟩ : syracuseStep 2712923 = 4069385) B4069385
theorem B2540891 : Blo 1693547 2540891 := bstep (se 1 (by rfl) ⟨1905668, by rfl⟩ : syracuseStep 2540891 = 3811337) B3811337
theorem B14673257 : Blo 1693547 14673257 := bstep (se 2 (by rfl) ⟨5502471, by rfl⟩ : syracuseStep 14673257 = 11004943) B11004943
theorem B11150729 : Blo 1693547 11150729 := bstep (se 2 (by rfl) ⟨4181523, by rfl⟩ : syracuseStep 11150729 = 8363047) B8363047
theorem B9651595 : Blo 1693547 9651595 := bstep (se 1 (by rfl) ⟨7238696, by rfl⟩ : syracuseStep 9651595 = 14477393) B14477393
theorem B7234991 : Blo 1693547 7234991 := bstep (se 1 (by rfl) ⟨5426243, by rfl⟩ : syracuseStep 7234991 = 10852487) B10852487
theorem B8144381 : Blo 1693547 8144381 := bstep (se 3 (by rfl) ⟨1527071, by rfl⟩ : syracuseStep 8144381 = 3054143) B3054143
theorem B5719571 : Blo 1693547 5719571 := bstep (se 1 (by rfl) ⟨4289678, by rfl⟩ : syracuseStep 5719571 = 8579357) B8579357
theorem B14468645 : Blo 1693547 14468645 := bstep (se 4 (by rfl) ⟨1356435, by rfl⟩ : syracuseStep 14468645 = 2712871) B2712871
theorem B2541167 : Blo 1693547 2541167 := bstep (se 1 (by rfl) ⟨1905875, by rfl⟩ : syracuseStep 2541167 = 3811751) B3811751
theorem B2541239 : Blo 1693547 2541239 := bstep (se 1 (by rfl) ⟨1905929, by rfl⟩ : syracuseStep 2541239 = 3811859) B3811859
theorem B2541275 : Blo 1693547 2541275 := bstep (se 1 (by rfl) ⟨1905956, by rfl⟩ : syracuseStep 2541275 = 3811913) B3811913
theorem B3811103 : Blo 1693547 3811103 := bstep (se 1 (by rfl) ⟨2858327, by rfl⟩ : syracuseStep 3811103 = 5716655) B5716655
theorem B18827063 : Blo 1693547 18827063 := bstep (se 1 (by rfl) ⟨14120297, by rfl⟩ : syracuseStep 18827063 = 28240595) B28240595
theorem B2860879 : Blo 1693547 2860879 := bstep (se 1 (by rfl) ⟨2145659, by rfl⟩ : syracuseStep 2860879 = 4291319) B4291319
theorem B2541449 : Blo 1693547 2541449 := bstep (se 2 (by rfl) ⟨953043, by rfl⟩ : syracuseStep 2541449 = 1906087) B1906087
theorem B2541551 : Blo 1693547 2541551 := bstep (se 1 (by rfl) ⟨1906163, by rfl⟩ : syracuseStep 2541551 = 3812327) B3812327
theorem B3811319 : Blo 1693547 3811319 := bstep (se 1 (by rfl) ⟨2858489, by rfl⟩ : syracuseStep 3811319 = 5716979) B5716979
theorem B4827347 : Blo 1693547 4827347 := bstep (se 1 (by rfl) ⟨3620510, by rfl⟩ : syracuseStep 4827347 = 7241021) B7241021
theorem B10856663 : Blo 1693547 10856663 := bstep (se 1 (by rfl) ⟨8142497, by rfl⟩ : syracuseStep 10856663 = 16284995) B16284995
theorem B2541803 : Blo 1693547 2541803 := bstep (se 1 (by rfl) ⟨1906352, by rfl⟩ : syracuseStep 2541803 = 3812705) B3812705
theorem B2541863 : Blo 1693547 2541863 := bstep (se 1 (by rfl) ⟨1906397, by rfl⟩ : syracuseStep 2541863 = 3812795) B3812795
theorem B3811679 : Blo 1693547 3811679 := bstep (se 1 (by rfl) ⟨2858759, by rfl⟩ : syracuseStep 3811679 = 5717519) B5717519
theorem B2541947 : Blo 1693547 2541947 := bstep (se 1 (by rfl) ⟨1906460, by rfl⟩ : syracuseStep 2541947 = 3812921) B3812921
theorem B38676865 : Blo 1693547 38676865 := bstep (se 2 (by rfl) ⟨14503824, by rfl⟩ : syracuseStep 38676865 = 29007649) B29007649
theorem B2542217 : Blo 1693547 2542217 := bstep (se 2 (by rfl) ⟨953331, by rfl⟩ : syracuseStep 2542217 = 1906663) B1906663
theorem B5720759 : Blo 1693547 5720759 := bstep (se 1 (by rfl) ⟨4290569, by rfl⟩ : syracuseStep 5720759 = 8581139) B8581139
theorem B2542391 : Blo 1693547 2542391 := bstep (se 1 (by rfl) ⟨1906793, by rfl⟩ : syracuseStep 2542391 = 3813587) B3813587
theorem B2542427 : Blo 1693547 2542427 := bstep (se 1 (by rfl) ⟨1906820, by rfl⟩ : syracuseStep 2542427 = 3813641) B3813641
theorem B16288685 : Blo 1693547 16288685 := bstep (se 3 (by rfl) ⟨3054128, by rfl⟩ : syracuseStep 16288685 = 6108257) B6108257
theorem B4893671 : Blo 1693547 4893671 := bstep (se 1 (by rfl) ⟨3670253, by rfl⟩ : syracuseStep 4893671 = 7340507) B7340507
theorem B2542571 : Blo 1693547 2542571 := bstep (se 1 (by rfl) ⟨1906928, by rfl⟩ : syracuseStep 2542571 = 3813857) B3813857
theorem B3812399 : Blo 1693547 3812399 := bstep (se 1 (by rfl) ⟨2859299, by rfl⟩ : syracuseStep 3812399 = 5718599) B5718599
theorem B2542775 : Blo 1693547 2542775 := bstep (se 1 (by rfl) ⟨1907081, by rfl⟩ : syracuseStep 2542775 = 3814163) B3814163
theorem B8580329 : Blo 1693547 8580329 := bstep (se 2 (by rfl) ⟨3217623, by rfl⟩ : syracuseStep 8580329 = 6435247) B6435247
theorem B3812687 : Blo 1693547 3812687 := bstep (se 1 (by rfl) ⟨2859515, by rfl⟩ : syracuseStep 3812687 = 5719031) B5719031
theorem B12864905 : Blo 1693547 12864905 := bstep (se 2 (by rfl) ⟨4824339, by rfl⟩ : syracuseStep 12864905 = 9648679) B9648679
theorem B3812777 : Blo 1693547 3812777 := bstep (se 2 (by rfl) ⟨1429791, by rfl⟩ : syracuseStep 3812777 = 2859583) B2859583
theorem B2543015 : Blo 1693547 2543015 := bstep (se 1 (by rfl) ⟨1907261, by rfl⟩ : syracuseStep 2543015 = 3814523) B3814523
theorem B5426615 : Blo 1693547 5426615 := bstep (se 1 (by rfl) ⟨4069961, by rfl⟩ : syracuseStep 5426615 = 8139923) B8139923
theorem B9784759 : Blo 1693547 9784759 := bstep (se 1 (by rfl) ⟨7338569, by rfl⟩ : syracuseStep 9784759 = 14677139) B14677139
theorem B8138231 : Blo 1693547 8138231 := bstep (se 1 (by rfl) ⟨6103673, by rfl⟩ : syracuseStep 8138231 = 12207347) B12207347
theorem B2543099 : Blo 1693547 2543099 := bstep (se 1 (by rfl) ⟨1907324, by rfl⟩ : syracuseStep 2543099 = 3814649) B3814649
theorem B2543195 : Blo 1693547 2543195 := bstep (se 1 (by rfl) ⟨1907396, by rfl⟩ : syracuseStep 2543195 = 3814793) B3814793
theorem B2543279 : Blo 1693547 2543279 := bstep (se 1 (by rfl) ⟨1907459, by rfl⟩ : syracuseStep 2543279 = 3814919) B3814919
theorem B6434579 : Blo 1693547 6434579 := bstep (se 1 (by rfl) ⟨4825934, by rfl⟩ : syracuseStep 6434579 = 9651869) B9651869
theorem B17624965 : Blo 1693547 17624965 := bstep (se 4 (by rfl) ⟨1652340, by rfl⟩ : syracuseStep 17624965 = 3304681) B3304681
theorem B5500811 : Blo 1693547 5500811 := bstep (se 1 (by rfl) ⟨4125608, by rfl⟩ : syracuseStep 5500811 = 8251217) B8251217
theorem B3813263 : Blo 1693547 3813263 := bstep (se 1 (by rfl) ⟨2859947, by rfl⟩ : syracuseStep 3813263 = 5719895) B5719895
theorem B9162733 : Blo 1693547 9162733 := bstep (se 3 (by rfl) ⟨1718012, by rfl⟩ : syracuseStep 9162733 = 3436025) B3436025
theorem B20623409 : Blo 1693547 20623409 := bstep (se 2 (by rfl) ⟨7733778, by rfl⟩ : syracuseStep 20623409 = 15467557) B15467557
theorem B10858661 : Blo 1693547 10858661 := bstep (se 4 (by rfl) ⟨1017999, by rfl⟩ : syracuseStep 10858661 = 2035999) B2035999
theorem B9646289 : Blo 1693547 9646289 := bstep (se 2 (by rfl) ⟨3617358, by rfl⟩ : syracuseStep 9646289 = 7234717) B7234717
theorem B8581625 : Blo 1693547 8581625 := bstep (se 2 (by rfl) ⟨3218109, by rfl⟩ : syracuseStep 8581625 = 6436219) B6436219
theorem B12210689 : Blo 1693547 12210689 := bstep (se 2 (by rfl) ⟨4579008, by rfl⟩ : syracuseStep 12210689 = 9158017) B9158017
theorem B9654785 : Blo 1693547 9654785 := bstep (se 2 (by rfl) ⟨3620544, by rfl⟩ : syracuseStep 9654785 = 7241089) B7241089
theorem B3813983 : Blo 1693547 3813983 := bstep (se 1 (by rfl) ⟨2860487, by rfl⟩ : syracuseStep 3813983 = 5720975) B5720975
theorem B3052399 : Blo 1693547 3052399 := bstep (se 1 (by rfl) ⟨2289299, by rfl⟩ : syracuseStep 3052399 = 4578599) B4578599
theorem B2413423 : Blo 1693547 2413423 := bstep (se 1 (by rfl) ⟨1810067, by rfl⟩ : syracuseStep 2413423 = 3620135) B3620135
theorem B3216439 : Blo 1693547 3216439 := bstep (se 1 (by rfl) ⟨2412329, by rfl⟩ : syracuseStep 3216439 = 4824659) B4824659
theorem B1905727 : Blo 1693547 1905727 := bstep (se 1 (by rfl) ⟨1429295, by rfl⟩ : syracuseStep 1905727 = 2858591) B2858591
theorem B5796937 : Blo 1693547 5796937 := bstep (se 2 (by rfl) ⟨2173851, by rfl⟩ : syracuseStep 5796937 = 4347703) B4347703
theorem B14472269 : Blo 1693547 14472269 := bstep (se 3 (by rfl) ⟨2713550, by rfl⟩ : syracuseStep 14472269 = 5427101) B5427101
theorem B1905871 : Blo 1693547 1905871 := bstep (se 1 (by rfl) ⟨1429403, by rfl⟩ : syracuseStep 1905871 = 2858807) B2858807
theorem B9786601 : Blo 1693547 9786601 := bstep (se 2 (by rfl) ⟨3669975, by rfl⟩ : syracuseStep 9786601 = 7339951) B7339951
theorem B5428511 : Blo 1693547 5428511 := bstep (se 1 (by rfl) ⟨4071383, by rfl⟩ : syracuseStep 5428511 = 8142767) B8142767
theorem B5879137 : Blo 1693547 5879137 := bstep (se 2 (by rfl) ⟨2204676, by rfl⟩ : syracuseStep 5879137 = 4409353) B4409353
theorem B2610587 : Blo 1693547 2610587 := bstep (se 1 (by rfl) ⟨1957940, by rfl⟩ : syracuseStep 2610587 = 3915881) B3915881
theorem B3814811 : Blo 1693547 3814811 := bstep (se 1 (by rfl) ⟨2861108, by rfl⟩ : syracuseStep 3814811 = 5722217) B5722217
theorem B36632249 : Blo 1693547 36632249 := bstep (se 2 (by rfl) ⟨13737093, by rfl⟩ : syracuseStep 36632249 = 27474187) B27474187
theorem B16742123 : Blo 1693547 16742123 := bstep (se 1 (by rfl) ⟨12556592, by rfl⟩ : syracuseStep 16742123 = 25113185) B25113185
theorem B4290367 : Blo 1693547 4290367 := bstep (se 1 (by rfl) ⟨3217775, by rfl⟩ : syracuseStep 4290367 = 6435551) B6435551
theorem B41244551 : Blo 1693547 41244551 := bstep (se 1 (by rfl) ⟨30933413, by rfl⟩ : syracuseStep 41244551 = 61866827) B61866827
theorem B1693679 : Blo 1693547 1693679 := bstep (se 1 (by rfl) ⟨1270259, by rfl⟩ : syracuseStep 1693679 = 2540519) B2540519
theorem B1693851 : Blo 1693547 1693851 := bstep (se 1 (by rfl) ⟨1270388, by rfl⟩ : syracuseStep 1693851 = 2540777) B2540777
theorem B1906843 : Blo 1693547 1906843 := bstep (se 1 (by rfl) ⟨1430132, by rfl⟩ : syracuseStep 1906843 = 2860265) B2860265
theorem B4823201 : Blo 1693547 4823201 := bstep (se 2 (by rfl) ⟨1808700, by rfl⟩ : syracuseStep 4823201 = 3617401) B3617401
theorem B33462433 : Blo 1693547 33462433 := bstep (se 2 (by rfl) ⟨12548412, by rfl⟩ : syracuseStep 33462433 = 25096825) B25096825
theorem B1693887 : Blo 1693547 1693887 := bstep (se 1 (by rfl) ⟨1270415, by rfl⟩ : syracuseStep 1693887 = 2540831) B2540831
theorem B1906879 : Blo 1693547 1906879 := bstep (se 1 (by rfl) ⟨1430159, by rfl⟩ : syracuseStep 1906879 = 2860319) B2860319
theorem B4290803 : Blo 1693547 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B1693999 : Blo 1693547 1693999 := bstep (se 1 (by rfl) ⟨1270499, by rfl⟩ : syracuseStep 1693999 = 2540999) B2540999
theorem B5716331 : Blo 1693547 5716331 := bstep (se 1 (by rfl) ⟨4287248, by rfl⟩ : syracuseStep 5716331 = 8574497) B8574497
theorem B19839497 : Blo 1693547 19839497 := bstep (se 2 (by rfl) ⟨7439811, by rfl⟩ : syracuseStep 19839497 = 14879623) B14879623
theorem B1694235 : Blo 1693547 1694235 := bstep (se 1 (by rfl) ⟨1270676, by rfl⟩ : syracuseStep 1694235 = 2541353) B2541353
theorem B1694239 : Blo 1693547 1694239 := bstep (se 1 (by rfl) ⟨1270679, by rfl⟩ : syracuseStep 1694239 = 2541359) B2541359
theorem B11000371 : Blo 1693547 11000371 := bstep (se 1 (by rfl) ⟨8250278, by rfl⟩ : syracuseStep 11000371 = 16500557) B16500557
theorem B5716601 : Blo 1693547 5716601 := bstep (se 2 (by rfl) ⟨2143725, by rfl⟩ : syracuseStep 5716601 = 4287451) B4287451
theorem B19290797 : Blo 1693547 19290797 := bstep (se 3 (by rfl) ⟨3617024, by rfl⟩ : syracuseStep 19290797 = 7234049) B7234049
theorem B20601643 : Blo 1693547 20601643 := bstep (se 1 (by rfl) ⟨15451232, by rfl⟩ : syracuseStep 20601643 = 30902465) B30902465
theorem B1694555 : Blo 1693547 1694555 := bstep (se 1 (by rfl) ⟨1270916, by rfl⟩ : syracuseStep 1694555 = 2541833) B2541833
theorem B20609923 : Blo 1693547 20609923 := bstep (se 1 (by rfl) ⟨15457442, by rfl⟩ : syracuseStep 20609923 = 30914885) B30914885
theorem B1694623 : Blo 1693547 1694623 := bstep (se 1 (by rfl) ⟨1270967, by rfl⟩ : syracuseStep 1694623 = 2541935) B2541935
theorem B3218383 : Blo 1693547 3218383 := bstep (se 1 (by rfl) ⟨2413787, by rfl⟩ : syracuseStep 3218383 = 4827575) B4827575
theorem B2857963 : Blo 1693547 2857963 := bstep (se 1 (by rfl) ⟨2143472, by rfl⟩ : syracuseStep 2857963 = 4286945) B4286945
theorem B5717033 : Blo 1693547 5717033 := bstep (se 2 (by rfl) ⟨2143887, by rfl⟩ : syracuseStep 5717033 = 4287775) B4287775
theorem B1694767 : Blo 1693547 1694767 := bstep (se 1 (by rfl) ⟨1271075, by rfl⟩ : syracuseStep 1694767 = 2542151) B2542151
theorem B1694791 : Blo 1693547 1694791 := bstep (se 1 (by rfl) ⟨1271093, by rfl⟩ : syracuseStep 1694791 = 2542187) B2542187
theorem B2858105 : Blo 1693547 2858105 := bstep (se 2 (by rfl) ⟨1071789, by rfl⟩ : syracuseStep 2858105 = 2143579) B2143579
theorem B2899127 : Blo 1693547 2899127 := bstep (se 1 (by rfl) ⟨2174345, by rfl⟩ : syracuseStep 2899127 = 4348691) B4348691
theorem B19299545 : Blo 1693547 19299545 := bstep (se 2 (by rfl) ⟨7237329, by rfl⟩ : syracuseStep 19299545 = 14474659) B14474659
theorem B1694943 : Blo 1693547 1694943 := bstep (se 1 (by rfl) ⟨1271207, by rfl⟩ : syracuseStep 1694943 = 2542415) B2542415
theorem B20610409 : Blo 1693547 20610409 := bstep (se 2 (by rfl) ⟨7728903, by rfl⟩ : syracuseStep 20610409 = 15457807) B15457807
theorem B4824431 : Blo 1693547 4824431 := bstep (se 1 (by rfl) ⟨3618323, by rfl⟩ : syracuseStep 4824431 = 7236647) B7236647
theorem B9649637 : Blo 1693547 9649637 := bstep (se 4 (by rfl) ⟨904653, by rfl⟩ : syracuseStep 9649637 = 1809307) B1809307
theorem B1695207 : Blo 1693547 1695207 := bstep (se 1 (by rfl) ⟨1271405, by rfl⟩ : syracuseStep 1695207 = 2542811) B2542811
theorem B1695323 : Blo 1693547 1695323 := bstep (se 1 (by rfl) ⟨1271492, by rfl⟩ : syracuseStep 1695323 = 2542985) B2542985
theorem B5430971 : Blo 1693547 5430971 := bstep (se 1 (by rfl) ⟨4073228, by rfl⟩ : syracuseStep 5430971 = 8146457) B8146457
theorem B2899783 : Blo 1693547 2899783 := bstep (se 1 (by rfl) ⟨2174837, by rfl⟩ : syracuseStep 2899783 = 4349675) B4349675
theorem B39116773 : Blo 1693547 39116773 := bstep (se 4 (by rfl) ⟨3667197, by rfl⟩ : syracuseStep 39116773 = 7334395) B7334395
theorem B6430859 : Blo 1693547 6430859 := bstep (se 1 (by rfl) ⟨4823144, by rfl⟩ : syracuseStep 6430859 = 9646289) B9646289
theorem B9650411 : Blo 1693547 9650411 := bstep (se 1 (by rfl) ⟨7237808, by rfl⟩ : syracuseStep 9650411 = 14475617) B14475617
theorem B30916997 : Blo 1693547 30916997 := bstep (se 4 (by rfl) ⟨2898468, by rfl⟩ : syracuseStep 30916997 = 5796937) B5796937
theorem B51569153 : Blo 1693547 51569153 := bstep (se 2 (by rfl) ⟨19338432, by rfl⟩ : syracuseStep 51569153 = 38676865) B38676865
theorem B5505641 : Blo 1693547 5505641 := bstep (se 2 (by rfl) ⟨2064615, by rfl⟩ : syracuseStep 5505641 = 4129231) B4129231
theorem B9782171 : Blo 1693547 9782171 := bstep (se 1 (by rfl) ⟨7336628, by rfl⟩ : syracuseStep 9782171 = 14673257) B14673257
theorem B27468857 : Blo 1693547 27468857 := bstep (se 2 (by rfl) ⟨10300821, by rfl⟩ : syracuseStep 27468857 = 20601643) B20601643
theorem B24421499 : Blo 1693547 24421499 := bstep (se 1 (by rfl) ⟨18316124, by rfl⟩ : syracuseStep 24421499 = 36632249) B36632249
theorem B2540735 : Blo 1693547 2540735 := bstep (se 1 (by rfl) ⟨1905551, by rfl⟩ : syracuseStep 2540735 = 3811103) B3811103
theorem B12551375 : Blo 1693547 12551375 := bstep (se 1 (by rfl) ⟨9413531, by rfl⟩ : syracuseStep 12551375 = 18827063) B18827063
theorem B3810617 : Blo 1693547 3810617 := bstep (se 2 (by rfl) ⟨1428981, by rfl⟩ : syracuseStep 3810617 = 2857963) B2857963
theorem B2540879 : Blo 1693547 2540879 := bstep (se 1 (by rfl) ⟨1905659, by rfl⟩ : syracuseStep 2540879 = 3811319) B3811319
theorem B52905325 : Blo 1693547 52905325 := bstep (se 3 (by rfl) ⟨9919748, by rfl⟩ : syracuseStep 52905325 = 19839497) B19839497
theorem B2540969 : Blo 1693547 2540969 := bstep (se 2 (by rfl) ⟨952863, by rfl⟩ : syracuseStep 2540969 = 1905727) B1905727
theorem B2860535 : Blo 1693547 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B2541119 : Blo 1693547 2541119 := bstep (se 1 (by rfl) ⟨1905839, by rfl⟩ : syracuseStep 2541119 = 3811679) B3811679
theorem B3810887 : Blo 1693547 3810887 := bstep (se 1 (by rfl) ⟨2858165, by rfl⟩ : syracuseStep 3810887 = 5716331) B5716331
theorem B2541161 : Blo 1693547 2541161 := bstep (se 2 (by rfl) ⟨952935, by rfl⟩ : syracuseStep 2541161 = 1905871) B1905871
theorem B3811067 : Blo 1693547 3811067 := bstep (se 1 (by rfl) ⟨2858300, by rfl⟩ : syracuseStep 3811067 = 5716601) B5716601
theorem B3262447 : Blo 1693547 3262447 := bstep (se 1 (by rfl) ⟨2446835, by rfl⟩ : syracuseStep 3262447 = 4893671) B4893671
theorem B3811355 : Blo 1693547 3811355 := bstep (se 1 (by rfl) ⟨2858516, by rfl⟩ : syracuseStep 3811355 = 5717033) B5717033
theorem B2541599 : Blo 1693547 2541599 := bstep (se 1 (by rfl) ⟨1906199, by rfl⟩ : syracuseStep 2541599 = 3812399) B3812399
theorem B5720219 : Blo 1693547 5720219 := bstep (se 1 (by rfl) ⟨4290164, by rfl⟩ : syracuseStep 5720219 = 8580329) B8580329
theorem B2541791 : Blo 1693547 2541791 := bstep (se 1 (by rfl) ⟨1906343, by rfl⟩ : syracuseStep 2541791 = 3812687) B3812687
theorem B2541851 : Blo 1693547 2541851 := bstep (se 1 (by rfl) ⟨1906388, by rfl⟩ : syracuseStep 2541851 = 3812777) B3812777
theorem B6433091 : Blo 1693547 6433091 := bstep (se 1 (by rfl) ⟨4824818, by rfl⟩ : syracuseStep 6433091 = 9649637) B9649637
theorem B5425487 : Blo 1693547 5425487 := bstep (se 1 (by rfl) ⟨4069115, by rfl⟩ : syracuseStep 5425487 = 8138231) B8138231
theorem B5720489 : Blo 1693547 5720489 := bstep (se 2 (by rfl) ⟨2145183, by rfl⟩ : syracuseStep 5720489 = 4290367) B4290367
theorem B2542175 : Blo 1693547 2542175 := bstep (se 1 (by rfl) ⟨1906631, by rfl⟩ : syracuseStep 2542175 = 3813263) B3813263
theorem B12216977 : Blo 1693547 12216977 := bstep (se 2 (by rfl) ⟨4581366, by rfl⟩ : syracuseStep 12216977 = 9162733) B9162733
theorem B13748939 : Blo 1693547 13748939 := bstep (se 1 (by rfl) ⟨10311704, by rfl⟩ : syracuseStep 13748939 = 20623409) B20623409
theorem B2542457 : Blo 1693547 2542457 := bstep (se 2 (by rfl) ⟨953421, by rfl⟩ : syracuseStep 2542457 = 1906843) B1906843
theorem B44616577 : Blo 1693547 44616577 := bstep (se 2 (by rfl) ⟨16731216, by rfl⟩ : syracuseStep 44616577 = 33462433) B33462433
theorem B2542505 : Blo 1693547 2542505 := bstep (se 2 (by rfl) ⟨953439, by rfl⟩ : syracuseStep 2542505 = 1906879) B1906879
theorem B5721083 : Blo 1693547 5721083 := bstep (se 1 (by rfl) ⟨4290812, by rfl⟩ : syracuseStep 5721083 = 8581625) B8581625
theorem B2542655 : Blo 1693547 2542655 := bstep (se 1 (by rfl) ⟨1906991, by rfl⟩ : syracuseStep 2542655 = 3813983) B3813983
theorem B14667161 : Blo 1693547 14667161 := bstep (se 2 (by rfl) ⟨5500185, by rfl⟩ : syracuseStep 14667161 = 11000371) B11000371
theorem B3435943 : Blo 1693547 3435943 := bstep (se 1 (by rfl) ⟨2576957, by rfl⟩ : syracuseStep 3435943 = 5153915) B5153915
theorem B48885191 : Blo 1693547 48885191 := bstep (se 1 (by rfl) ⟨36663893, by rfl⟩ : syracuseStep 48885191 = 73327787) B73327787
theorem B3812831 : Blo 1693547 3812831 := bstep (se 1 (by rfl) ⟨2859623, by rfl⟩ : syracuseStep 3812831 = 5719247) B5719247
theorem B7433819 : Blo 1693547 7433819 := bstep (se 1 (by rfl) ⟨5575364, by rfl⟩ : syracuseStep 7433819 = 11150729) B11150729
theorem B1740391 : Blo 1693547 1740391 := bstep (se 1 (by rfl) ⟨1305293, by rfl⟩ : syracuseStep 1740391 = 2610587) B2610587
theorem B2543207 : Blo 1693547 2543207 := bstep (se 1 (by rfl) ⟨1907405, by rfl⟩ : syracuseStep 2543207 = 3814811) B3814811
theorem B3813047 : Blo 1693547 3813047 := bstep (se 1 (by rfl) ⟨2859785, by rfl⟩ : syracuseStep 3813047 = 5719571) B5719571
theorem B9645763 : Blo 1693547 9645763 := bstep (se 1 (by rfl) ⟨7234322, by rfl⟩ : syracuseStep 9645763 = 14468645) B14468645
theorem B11161415 : Blo 1693547 11161415 := bstep (se 1 (by rfl) ⟨8371061, by rfl⟩ : syracuseStep 11161415 = 16742123) B16742123
theorem B27479897 : Blo 1693547 27479897 := bstep (se 2 (by rfl) ⟨10304961, by rfl⟩ : syracuseStep 27479897 = 20609923) B20609923
theorem B52195205 : Blo 1693547 52195205 := bstep (se 4 (by rfl) ⟨4893300, by rfl⟩ : syracuseStep 52195205 = 9786601) B9786601
theorem B27496367 : Blo 1693547 27496367 := bstep (se 1 (by rfl) ⟨20622275, by rfl⟩ : syracuseStep 27496367 = 41244551) B41244551
theorem B4288585 : Blo 1693547 4288585 := bstep (se 2 (by rfl) ⟨1608219, by rfl⟩ : syracuseStep 4288585 = 3216439) B3216439
theorem B3215467 : Blo 1693547 3215467 := bstep (se 1 (by rfl) ⟨2411600, by rfl⟩ : syracuseStep 3215467 = 4823201) B4823201
theorem B7237775 : Blo 1693547 7237775 := bstep (se 1 (by rfl) ⟨5428331, by rfl⟩ : syracuseStep 7237775 = 10856663) B10856663
theorem B3813839 : Blo 1693547 3813839 := bstep (se 1 (by rfl) ⟨2860379, by rfl⟩ : syracuseStep 3813839 = 5720759) B5720759
theorem B27480545 : Blo 1693547 27480545 := bstep (se 2 (by rfl) ⟨10305204, by rfl⟩ : syracuseStep 27480545 = 20610409) B20610409
theorem B13046345 : Blo 1693547 13046345 := bstep (se 2 (by rfl) ⟨4892379, by rfl⟩ : syracuseStep 13046345 = 9784759) B9784759
theorem B10859123 : Blo 1693547 10859123 := bstep (se 1 (by rfl) ⟨8144342, by rfl⟩ : syracuseStep 10859123 = 16288685) B16288685
theorem B1905403 : Blo 1693547 1905403 := bstep (se 1 (by rfl) ⟨1429052, by rfl⟩ : syracuseStep 1905403 = 2858105) B2858105
theorem B12866363 : Blo 1693547 12866363 := bstep (se 1 (by rfl) ⟨9649772, by rfl⟩ : syracuseStep 12866363 = 19299545) B19299545
theorem B3216287 : Blo 1693547 3216287 := bstep (se 1 (by rfl) ⟨2412215, by rfl⟩ : syracuseStep 3216287 = 4824431) B4824431
theorem B3617743 : Blo 1693547 3617743 := bstep (se 1 (by rfl) ⟨2713307, by rfl⟩ : syracuseStep 3617743 = 5426615) B5426615
theorem B3814505 : Blo 1693547 3814505 := bstep (se 2 (by rfl) ⟨1430439, by rfl⟩ : syracuseStep 3814505 = 2860879) B2860879
theorem B23499953 : Blo 1693547 23499953 := bstep (se 2 (by rfl) ⟨8812482, by rfl⟩ : syracuseStep 23499953 = 17624965) B17624965
theorem B4289719 : Blo 1693547 4289719 := bstep (se 1 (by rfl) ⟨3217289, by rfl⟩ : syracuseStep 4289719 = 6434579) B6434579
theorem B3667207 : Blo 1693547 3667207 := bstep (se 1 (by rfl) ⟨2750405, by rfl⟩ : syracuseStep 3667207 = 5500811) B5500811
theorem B52155697 : Blo 1693547 52155697 := bstep (se 2 (by rfl) ⟨19558386, by rfl⟩ : syracuseStep 52155697 = 39116773) B39116773
theorem B7239107 : Blo 1693547 7239107 := bstep (se 1 (by rfl) ⟨5429330, by rfl⟩ : syracuseStep 7239107 = 10858661) B10858661
theorem B1906159 : Blo 1693547 1906159 := bstep (se 1 (by rfl) ⟨1429619, by rfl⟩ : syracuseStep 1906159 = 2859239) B2859239
theorem B1906267 : Blo 1693547 1906267 := bstep (se 1 (by rfl) ⟨1429700, by rfl⟩ : syracuseStep 1906267 = 2859401) B2859401
theorem B8140459 : Blo 1693547 8140459 := bstep (se 1 (by rfl) ⟨6105344, by rfl⟩ : syracuseStep 8140459 = 12210689) B12210689
theorem B6436523 : Blo 1693547 6436523 := bstep (se 1 (by rfl) ⟨4827392, by rfl⟩ : syracuseStep 6436523 = 9654785) B9654785
theorem B13932335 : Blo 1693547 13932335 := bstep (se 1 (by rfl) ⟨10449251, by rfl⟩ : syracuseStep 13932335 = 20898503) B20898503
theorem B13047635 : Blo 1693547 13047635 := bstep (se 1 (by rfl) ⟨9785726, by rfl⟩ : syracuseStep 13047635 = 19571453) B19571453
theorem B1906555 : Blo 1693547 1906555 := bstep (se 1 (by rfl) ⟨1429916, by rfl⟩ : syracuseStep 1906555 = 2859833) B2859833
theorem B1693599 : Blo 1693547 1693599 := bstep (se 1 (by rfl) ⟨1270199, by rfl⟩ : syracuseStep 1693599 = 2540399) B2540399
theorem B1906591 : Blo 1693547 1906591 := bstep (se 1 (by rfl) ⟨1429943, by rfl⟩ : syracuseStep 1906591 = 2859887) B2859887
theorem B9648179 : Blo 1693547 9648179 := bstep (se 1 (by rfl) ⟨7236134, by rfl⟩ : syracuseStep 9648179 = 14472269) B14472269
theorem B1693767 : Blo 1693547 1693767 := bstep (se 1 (by rfl) ⟨1270325, by rfl⟩ : syracuseStep 1693767 = 2540651) B2540651
theorem B3619007 : Blo 1693547 3619007 := bstep (se 1 (by rfl) ⟨2714255, by rfl⟩ : syracuseStep 3619007 = 5428511) B5428511
theorem B1808615 : Blo 1693547 1808615 := bstep (se 1 (by rfl) ⟨1356461, by rfl⟩ : syracuseStep 1808615 = 2712923) B2712923
theorem B1693927 : Blo 1693547 1693927 := bstep (se 1 (by rfl) ⟨1270445, by rfl⟩ : syracuseStep 1693927 = 2540891) B2540891
theorem B4823327 : Blo 1693547 4823327 := bstep (se 1 (by rfl) ⟨3617495, by rfl⟩ : syracuseStep 4823327 = 7234991) B7234991
theorem B5429587 : Blo 1693547 5429587 := bstep (se 1 (by rfl) ⟨4072190, by rfl⟩ : syracuseStep 5429587 = 8144381) B8144381
theorem B1694111 : Blo 1693547 1694111 := bstep (se 1 (by rfl) ⟨1270583, by rfl⟩ : syracuseStep 1694111 = 2541167) B2541167
theorem B1694159 : Blo 1693547 1694159 := bstep (se 1 (by rfl) ⟨1270619, by rfl⟩ : syracuseStep 1694159 = 2541239) B2541239
theorem B1694183 : Blo 1693547 1694183 := bstep (se 1 (by rfl) ⟨1270637, by rfl⟩ : syracuseStep 1694183 = 2541275) B2541275
theorem B4069865 : Blo 1693547 4069865 := bstep (se 2 (by rfl) ⟨1526199, by rfl⟩ : syracuseStep 4069865 = 3052399) B3052399
theorem B3217897 : Blo 1693547 3217897 := bstep (se 2 (by rfl) ⟨1206711, by rfl⟩ : syracuseStep 3217897 = 2413423) B2413423
theorem B1694299 : Blo 1693547 1694299 := bstep (se 1 (by rfl) ⟨1270724, by rfl⟩ : syracuseStep 1694299 = 2541449) B2541449
theorem B4291177 : Blo 1693547 4291177 := bstep (se 2 (by rfl) ⟨1609191, by rfl⟩ : syracuseStep 4291177 = 3218383) B3218383
theorem B1694367 : Blo 1693547 1694367 := bstep (se 1 (by rfl) ⟨1270775, by rfl⟩ : syracuseStep 1694367 = 2541551) B2541551
theorem B3218231 : Blo 1693547 3218231 := bstep (se 1 (by rfl) ⟨2413673, by rfl⟩ : syracuseStep 3218231 = 4827347) B4827347
theorem B1694535 : Blo 1693547 1694535 := bstep (se 1 (by rfl) ⟨1270901, by rfl⟩ : syracuseStep 1694535 = 2541803) B2541803
theorem B1694575 : Blo 1693547 1694575 := bstep (se 1 (by rfl) ⟨1270931, by rfl⟩ : syracuseStep 1694575 = 2541863) B2541863
theorem B1694631 : Blo 1693547 1694631 := bstep (se 1 (by rfl) ⟨1270973, by rfl⟩ : syracuseStep 1694631 = 2541947) B2541947
theorem B1694811 : Blo 1693547 1694811 := bstep (se 1 (by rfl) ⟨1271108, by rfl⟩ : syracuseStep 1694811 = 2542217) B2542217
theorem B12860531 : Blo 1693547 12860531 := bstep (se 1 (by rfl) ⟨9645398, by rfl⟩ : syracuseStep 12860531 = 19290797) B19290797
theorem B7838849 : Blo 1693547 7838849 := bstep (se 2 (by rfl) ⟨2939568, by rfl⟩ : syracuseStep 7838849 = 5879137) B5879137
theorem B12868793 : Blo 1693547 12868793 := bstep (se 2 (by rfl) ⟨4825797, by rfl⟩ : syracuseStep 12868793 = 9651595) B9651595
theorem B1694927 : Blo 1693547 1694927 := bstep (se 1 (by rfl) ⟨1271195, by rfl⟩ : syracuseStep 1694927 = 2542391) B2542391
theorem B1694951 : Blo 1693547 1694951 := bstep (se 1 (by rfl) ⟨1271213, by rfl⟩ : syracuseStep 1694951 = 2542427) B2542427
theorem B1695047 : Blo 1693547 1695047 := bstep (se 1 (by rfl) ⟨1271285, by rfl⟩ : syracuseStep 1695047 = 2542571) B2542571
theorem B1932751 : Blo 1693547 1932751 := bstep (se 1 (by rfl) ⟨1449563, by rfl⟩ : syracuseStep 1932751 = 2899127) B2899127
theorem B1695183 : Blo 1693547 1695183 := bstep (se 1 (by rfl) ⟨1271387, by rfl⟩ : syracuseStep 1695183 = 2542775) B2542775
theorem B59530733 : Blo 1693547 59530733 := bstep (se 3 (by rfl) ⟨11162012, by rfl⟩ : syracuseStep 59530733 = 22324025) B22324025
theorem B8576603 : Blo 1693547 8576603 := bstep (se 1 (by rfl) ⟨6432452, by rfl⟩ : syracuseStep 8576603 = 12864905) B12864905
theorem B1695343 : Blo 1693547 1695343 := bstep (se 1 (by rfl) ⟨1271507, by rfl⟩ : syracuseStep 1695343 = 2543015) B2543015
theorem B1695399 : Blo 1693547 1695399 := bstep (se 1 (by rfl) ⟨1271549, by rfl⟩ : syracuseStep 1695399 = 2543099) B2543099
theorem B1695463 : Blo 1693547 1695463 := bstep (se 1 (by rfl) ⟨1271597, by rfl⟩ : syracuseStep 1695463 = 2543195) B2543195
theorem B3866377 : Blo 1693547 3866377 := bstep (se 2 (by rfl) ⟨1449891, by rfl⟩ : syracuseStep 3866377 = 2899783) B2899783
theorem B1695519 : Blo 1693547 1695519 := bstep (se 1 (by rfl) ⟨1271639, by rfl⟩ : syracuseStep 1695519 = 2543279) B2543279
theorem B3620647 : Blo 1693547 3620647 := bstep (se 1 (by rfl) ⟨2715485, by rfl⟩ : syracuseStep 3620647 = 5430971) B5430971
theorem B5718113 : Blo 1693547 5718113 := bstep (se 2 (by rfl) ⟨2144292, by rfl⟩ : syracuseStep 5718113 = 4288585) B4288585
theorem B4825183 : Blo 1693547 4825183 := bstep (se 1 (by rfl) ⟨3618887, by rfl⟩ : syracuseStep 4825183 = 7237775) B7237775
theorem B20611331 : Blo 1693547 20611331 := bstep (se 1 (by rfl) ⟨15458498, by rfl⟩ : syracuseStep 20611331 = 30916997) B30916997
theorem B3670427 : Blo 1693547 3670427 := bstep (se 1 (by rfl) ⟨2752820, by rfl⟩ : syracuseStep 3670427 = 5505641) B5505641
theorem B8577575 : Blo 1693547 8577575 := bstep (se 1 (by rfl) ⟨6433181, by rfl⟩ : syracuseStep 8577575 = 12866363) B12866363
theorem B6521447 : Blo 1693547 6521447 := bstep (se 1 (by rfl) ⟨4891085, by rfl⟩ : syracuseStep 6521447 = 9782171) B9782171
theorem B2540411 : Blo 1693547 2540411 := bstep (se 1 (by rfl) ⟨1905308, by rfl⟩ : syracuseStep 2540411 = 3810617) B3810617
theorem B4826071 : Blo 1693547 4826071 := bstep (se 1 (by rfl) ⟨3619553, by rfl⟩ : syracuseStep 4826071 = 7239107) B7239107
theorem B2540537 : Blo 1693547 2540537 := bstep (se 2 (by rfl) ⟨952701, by rfl⟩ : syracuseStep 2540537 = 1905403) B1905403
theorem B2540591 : Blo 1693547 2540591 := bstep (se 1 (by rfl) ⟨1905443, by rfl⟩ : syracuseStep 2540591 = 3810887) B3810887
theorem B2540711 : Blo 1693547 2540711 := bstep (se 1 (by rfl) ⟨1905533, by rfl⟩ : syracuseStep 2540711 = 3811067) B3811067
theorem B2540903 : Blo 1693547 2540903 := bstep (se 1 (by rfl) ⟨1905677, by rfl⟩ : syracuseStep 2540903 = 3811355) B3811355
theorem B6432119 : Blo 1693547 6432119 := bstep (se 1 (by rfl) ⟨4824089, by rfl⟩ : syracuseStep 6432119 = 9648179) B9648179
theorem B5719625 : Blo 1693547 5719625 := bstep (se 2 (by rfl) ⟨2144859, by rfl⟩ : syracuseStep 5719625 = 4289719) B4289719
theorem B8144651 : Blo 1693547 8144651 := bstep (se 1 (by rfl) ⟨6108488, by rfl⟩ : syracuseStep 8144651 = 12216977) B12216977
theorem B4581257 : Blo 1693547 4581257 := bstep (se 2 (by rfl) ⟨1717971, by rfl⟩ : syracuseStep 4581257 = 3435943) B3435943
theorem B2541545 : Blo 1693547 2541545 := bstep (se 2 (by rfl) ⟨953079, by rfl⟩ : syracuseStep 2541545 = 1906159) B1906159
theorem B2541689 : Blo 1693547 2541689 := bstep (se 2 (by rfl) ⟨953133, by rfl⟩ : syracuseStep 2541689 = 1906267) B1906267
theorem B8579195 : Blo 1693547 8579195 := bstep (se 1 (by rfl) ⟨6434396, by rfl⟩ : syracuseStep 8579195 = 12868793) B12868793
theorem B37152893 : Blo 1693547 37152893 := bstep (se 3 (by rfl) ⟨6966167, by rfl⟩ : syracuseStep 37152893 = 13932335) B13932335
theorem B37128341 : Blo 1693547 37128341 := bstep (se 6 (by rfl) ⟨870195, by rfl⟩ : syracuseStep 37128341 = 1740391) B1740391
theorem B29763773 : Blo 1693547 29763773 := bstep (se 3 (by rfl) ⟨5580707, by rfl⟩ : syracuseStep 29763773 = 11161415) B11161415
theorem B32590127 : Blo 1693547 32590127 := bstep (se 1 (by rfl) ⟨24442595, by rfl⟩ : syracuseStep 32590127 = 48885191) B48885191
theorem B2541887 : Blo 1693547 2541887 := bstep (se 1 (by rfl) ⟨1906415, by rfl⟩ : syracuseStep 2541887 = 3812831) B3812831
theorem B5155169 : Blo 1693547 5155169 := bstep (se 2 (by rfl) ⟨1933188, by rfl⟩ : syracuseStep 5155169 = 3866377) B3866377
theorem B4827529 : Blo 1693547 4827529 := bstep (se 2 (by rfl) ⟨1810323, by rfl⟩ : syracuseStep 4827529 = 3620647) B3620647
theorem B10308005 : Blo 1693547 10308005 := bstep (se 4 (by rfl) ⟨966375, by rfl⟩ : syracuseStep 10308005 = 1932751) B1932751
theorem B2542031 : Blo 1693547 2542031 := bstep (se 1 (by rfl) ⟨1906523, by rfl⟩ : syracuseStep 2542031 = 3813047) B3813047
theorem B2542073 : Blo 1693547 2542073 := bstep (se 2 (by rfl) ⟨953277, by rfl⟩ : syracuseStep 2542073 = 1906555) B1906555
theorem B2542121 : Blo 1693547 2542121 := bstep (se 2 (by rfl) ⟨953295, by rfl⟩ : syracuseStep 2542121 = 1906591) B1906591
theorem B18319931 : Blo 1693547 18319931 := bstep (se 1 (by rfl) ⟨13739948, by rfl⟩ : syracuseStep 18319931 = 27479897) B27479897
theorem B4287239 : Blo 1693547 4287239 := bstep (se 1 (by rfl) ⟨3215429, by rfl⟩ : syracuseStep 4287239 = 6430859) B6430859
theorem B4287289 : Blo 1693547 4287289 := bstep (se 2 (by rfl) ⟨1607733, by rfl⟩ : syracuseStep 4287289 = 3215467) B3215467
theorem B6433607 : Blo 1693547 6433607 := bstep (se 1 (by rfl) ⟨4825205, by rfl⟩ : syracuseStep 6433607 = 9650411) B9650411
theorem B2542559 : Blo 1693547 2542559 := bstep (se 1 (by rfl) ⟨1906919, by rfl⟩ : syracuseStep 2542559 = 3813839) B3813839
theorem B18320363 : Blo 1693547 18320363 := bstep (se 1 (by rfl) ⟨13740272, by rfl⟩ : syracuseStep 18320363 = 27480545) B27480545
theorem B18312571 : Blo 1693547 18312571 := bstep (se 1 (by rfl) ⟨13734428, by rfl⟩ : syracuseStep 18312571 = 27468857) B27468857
theorem B2543003 : Blo 1693547 2543003 := bstep (se 1 (by rfl) ⟨1907252, by rfl⟩ : syracuseStep 2543003 = 3814505) B3814505
theorem B16280999 : Blo 1693547 16280999 := bstep (se 1 (by rfl) ⟨12210749, by rfl⟩ : syracuseStep 16280999 = 24421499) B24421499
theorem B15666635 : Blo 1693547 15666635 := bstep (se 1 (by rfl) ⟨11749976, by rfl⟩ : syracuseStep 15666635 = 23499953) B23499953
theorem B8367583 : Blo 1693547 8367583 := bstep (se 1 (by rfl) ⟨6275687, by rfl⟩ : syracuseStep 8367583 = 12551375) B12551375
theorem B5721569 : Blo 1693547 5721569 := bstep (se 2 (by rfl) ⟨2145588, by rfl⟩ : syracuseStep 5721569 = 4291177) B4291177
theorem B39112429 : Blo 1693547 39112429 := bstep (se 3 (by rfl) ⟨7333580, by rfl⟩ : syracuseStep 39112429 = 14667161) B14667161
theorem B3813479 : Blo 1693547 3813479 := bstep (se 1 (by rfl) ⟨2860109, by rfl⟩ : syracuseStep 3813479 = 5720219) B5720219
theorem B2412671 : Blo 1693547 2412671 := bstep (se 1 (by rfl) ⟨1809503, by rfl⟩ : syracuseStep 2412671 = 3619007) B3619007
theorem B3215551 : Blo 1693547 3215551 := bstep (se 1 (by rfl) ⟨2411663, by rfl⟩ : syracuseStep 3215551 = 4823327) B4823327
theorem B4288727 : Blo 1693547 4288727 := bstep (se 1 (by rfl) ⟨3216545, by rfl⟩ : syracuseStep 4288727 = 6433091) B6433091
theorem B3616991 : Blo 1693547 3616991 := bstep (se 1 (by rfl) ⟨2712743, by rfl⟩ : syracuseStep 3616991 = 5425487) B5425487
theorem B3813659 : Blo 1693547 3813659 := bstep (se 1 (by rfl) ⟨2860244, by rfl⟩ : syracuseStep 3813659 = 5720489) B5720489
theorem B3814055 : Blo 1693547 3814055 := bstep (se 1 (by rfl) ⟨2860541, by rfl⟩ : syracuseStep 3814055 = 5721083) B5721083
theorem B8573687 : Blo 1693547 8573687 := bstep (se 1 (by rfl) ⟨6430265, by rfl⟩ : syracuseStep 8573687 = 12860531) B12860531
theorem B8581949 : Blo 1693547 8581949 := bstep (se 3 (by rfl) ⟨1609115, by rfl⟩ : syracuseStep 8581949 = 3218231) B3218231
theorem B39687155 : Blo 1693547 39687155 := bstep (se 1 (by rfl) ⟨29765366, by rfl⟩ : syracuseStep 39687155 = 59530733) B59530733
theorem B34796803 : Blo 1693547 34796803 := bstep (se 1 (by rfl) ⟨26097602, by rfl⟩ : syracuseStep 34796803 = 52195205) B52195205
theorem B18330911 : Blo 1693547 18330911 := bstep (se 1 (by rfl) ⟨13748183, by rfl⟩ : syracuseStep 18330911 = 27496367) B27496367
theorem B34379435 : Blo 1693547 34379435 := bstep (se 1 (by rfl) ⟨25784576, by rfl⟩ : syracuseStep 34379435 = 51569153) B51569153
theorem B20903597 : Blo 1693547 20903597 := bstep (se 3 (by rfl) ⟨3919424, by rfl⟩ : syracuseStep 20903597 = 7838849) B7838849
theorem B8697563 : Blo 1693547 8697563 := bstep (se 1 (by rfl) ⟨6523172, by rfl⟩ : syracuseStep 8697563 = 13046345) B13046345
theorem B7239415 : Blo 1693547 7239415 := bstep (se 1 (by rfl) ⟨5429561, by rfl⟩ : syracuseStep 7239415 = 10859123) B10859123
theorem B7239449 : Blo 1693547 7239449 := bstep (se 2 (by rfl) ⟨2714793, by rfl⟩ : syracuseStep 7239449 = 5429587) B5429587
theorem B4822973 : Blo 1693547 4822973 := bstep (se 3 (by rfl) ⟨904307, by rfl⟩ : syracuseStep 4822973 = 1808615) B1808615
theorem B4290529 : Blo 1693547 4290529 := bstep (se 2 (by rfl) ⟨1608948, by rfl⟩ : syracuseStep 4290529 = 3217897) B3217897
theorem B1693823 : Blo 1693547 1693823 := bstep (se 1 (by rfl) ⟨1270367, by rfl⟩ : syracuseStep 1693823 = 2540735) B2540735
theorem B1693919 : Blo 1693547 1693919 := bstep (se 1 (by rfl) ⟨1270439, by rfl⟩ : syracuseStep 1693919 = 2540879) B2540879
theorem B1693979 : Blo 1693547 1693979 := bstep (se 1 (by rfl) ⟨1270484, by rfl⟩ : syracuseStep 1693979 = 2540969) B2540969
theorem B1907023 : Blo 1693547 1907023 := bstep (se 1 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 1907023 = 2860535) B2860535
theorem B1694079 : Blo 1693547 1694079 := bstep (se 1 (by rfl) ⟨1270559, by rfl⟩ : syracuseStep 1694079 = 2541119) B2541119
theorem B1694107 : Blo 1693547 1694107 := bstep (se 1 (by rfl) ⟨1270580, by rfl⟩ : syracuseStep 1694107 = 2541161) B2541161
theorem B4291015 : Blo 1693547 4291015 := bstep (se 1 (by rfl) ⟨3218261, by rfl⟩ : syracuseStep 4291015 = 6436523) B6436523
theorem B59488769 : Blo 1693547 59488769 := bstep (se 2 (by rfl) ⟨22308288, by rfl⟩ : syracuseStep 59488769 = 44616577) B44616577
theorem B8698423 : Blo 1693547 8698423 := bstep (se 1 (by rfl) ⟨6523817, by rfl⟩ : syracuseStep 8698423 = 13047635) B13047635
theorem B4823657 : Blo 1693547 4823657 := bstep (se 2 (by rfl) ⟨1808871, by rfl⟩ : syracuseStep 4823657 = 3617743) B3617743
theorem B10852973 : Blo 1693547 10852973 := bstep (se 3 (by rfl) ⟨2034932, by rfl⟩ : syracuseStep 10852973 = 4069865) B4069865
theorem B1694399 : Blo 1693547 1694399 := bstep (se 1 (by rfl) ⟨1270799, by rfl⟩ : syracuseStep 1694399 = 2541599) B2541599
theorem B1694527 : Blo 1693547 1694527 := bstep (se 1 (by rfl) ⟨1270895, by rfl⟩ : syracuseStep 1694527 = 2541791) B2541791
theorem B1694567 : Blo 1693547 1694567 := bstep (se 1 (by rfl) ⟨1270925, by rfl⟩ : syracuseStep 1694567 = 2541851) B2541851
theorem B4889609 : Blo 1693547 4889609 := bstep (se 2 (by rfl) ⟨1833603, by rfl⟩ : syracuseStep 4889609 = 3667207) B3667207
theorem B1694783 : Blo 1693547 1694783 := bstep (se 1 (by rfl) ⟨1271087, by rfl⟩ : syracuseStep 1694783 = 2542175) B2542175
theorem B69540929 : Blo 1693547 69540929 := bstep (se 2 (by rfl) ⟨26077848, by rfl⟩ : syracuseStep 69540929 = 52155697) B52155697
theorem B9165959 : Blo 1693547 9165959 := bstep (se 1 (by rfl) ⟨6874469, by rfl⟩ : syracuseStep 9165959 = 13748939) B13748939
theorem B70540433 : Blo 1693547 70540433 := bstep (se 2 (by rfl) ⟨26452662, by rfl⟩ : syracuseStep 70540433 = 52905325) B52905325
theorem B1694971 : Blo 1693547 1694971 := bstep (se 1 (by rfl) ⟨1271228, by rfl⟩ : syracuseStep 1694971 = 2542457) B2542457
theorem B1695003 : Blo 1693547 1695003 := bstep (se 1 (by rfl) ⟨1271252, by rfl⟩ : syracuseStep 1695003 = 2542505) B2542505
theorem B1695103 : Blo 1693547 1695103 := bstep (se 1 (by rfl) ⟨1271327, by rfl⟩ : syracuseStep 1695103 = 2542655) B2542655
theorem B10853945 : Blo 1693547 10853945 := bstep (se 2 (by rfl) ⟨4070229, by rfl⟩ : syracuseStep 10853945 = 8140459) B8140459
theorem B12861017 : Blo 1693547 12861017 := bstep (se 2 (by rfl) ⟨4822881, by rfl⟩ : syracuseStep 12861017 = 9645763) B9645763
theorem B4955879 : Blo 1693547 4955879 := bstep (se 1 (by rfl) ⟨3716909, by rfl⟩ : syracuseStep 4955879 = 7433819) B7433819
theorem B5717735 : Blo 1693547 5717735 := bstep (se 1 (by rfl) ⟨4288301, by rfl⟩ : syracuseStep 5717735 = 8576603) B8576603
theorem B1695471 : Blo 1693547 1695471 := bstep (se 1 (by rfl) ⟨1271603, by rfl⟩ : syracuseStep 1695471 = 2543207) B2543207
theorem B8576765 : Blo 1693547 8576765 := bstep (se 3 (by rfl) ⟨1608143, by rfl⟩ : syracuseStep 8576765 = 3216287) B3216287
theorem B17399717 : Blo 1693547 17399717 := bstep (se 4 (by rfl) ⟨1631223, by rfl⟩ : syracuseStep 17399717 = 3262447) B3262447
theorem B2859151 : Blo 1693547 2859151 := bstep (se 1 (by rfl) ⟨2144363, by rfl⟩ : syracuseStep 2859151 = 4288727) B4288727
theorem B5718383 : Blo 1693547 5718383 := bstep (se 1 (by rfl) ⟨4288787, by rfl⟩ : syracuseStep 5718383 = 8577575) B8577575
theorem B13747117 : Blo 1693547 13747117 := bstep (se 3 (by rfl) ⟨2577584, by rfl⟩ : syracuseStep 13747117 = 5155169) B5155169
theorem B13935731 : Blo 1693547 13935731 := bstep (se 1 (by rfl) ⟨10451798, by rfl⟩ : syracuseStep 13935731 = 20903597) B20903597
theorem B4826299 : Blo 1693547 4826299 := bstep (se 1 (by rfl) ⟨3619724, by rfl⟩ : syracuseStep 4826299 = 7239449) B7239449
theorem B5719463 : Blo 1693547 5719463 := bstep (se 1 (by rfl) ⟨4289597, by rfl⟩ : syracuseStep 5719463 = 8579195) B8579195
theorem B19842515 : Blo 1693547 19842515 := bstep (se 1 (by rfl) ⟨14881886, by rfl⟩ : syracuseStep 19842515 = 29763773) B29763773
theorem B21726751 : Blo 1693547 21726751 := bstep (se 1 (by rfl) ⟨16295063, by rfl⟩ : syracuseStep 21726751 = 32590127) B32590127
theorem B39659179 : Blo 1693547 39659179 := bstep (se 1 (by rfl) ⟨29744384, by rfl⟩ : syracuseStep 39659179 = 59488769) B59488769
theorem B7235315 : Blo 1693547 7235315 := bstep (se 1 (by rfl) ⟨5426486, by rfl⟩ : syracuseStep 7235315 = 10852973) B10852973
theorem B91678493 : Blo 1693547 91678493 := bstep (se 3 (by rfl) ⟨17189717, by rfl⟩ : syracuseStep 91678493 = 34379435) B34379435
theorem B97667045 : Blo 1693547 97667045 := bstep (se 4 (by rfl) ⟨9156285, by rfl⟩ : syracuseStep 97667045 = 18312571) B18312571
theorem B46360619 : Blo 1693547 46360619 := bstep (se 1 (by rfl) ⟨34770464, by rfl⟩ : syracuseStep 46360619 = 69540929) B69540929
theorem B9652553 : Blo 1693547 9652553 := bstep (se 2 (by rfl) ⟨3619707, by rfl⟩ : syracuseStep 9652553 = 7239415) B7239415
theorem B12216685 : Blo 1693547 12216685 := bstep (se 3 (by rfl) ⟨2290628, by rfl⟩ : syracuseStep 12216685 = 4581257) B4581257
theorem B7235963 : Blo 1693547 7235963 := bstep (se 1 (by rfl) ⟨5426972, by rfl⟩ : syracuseStep 7235963 = 10853945) B10853945
theorem B3303919 : Blo 1693547 3303919 := bstep (se 1 (by rfl) ⟨2477939, by rfl⟩ : syracuseStep 3303919 = 4955879) B4955879
theorem B3811823 : Blo 1693547 3811823 := bstep (se 1 (by rfl) ⟨2858867, by rfl⟩ : syracuseStep 3811823 = 5717735) B5717735
theorem B5720705 : Blo 1693547 5720705 := bstep (se 2 (by rfl) ⟨2145264, by rfl⟩ : syracuseStep 5720705 = 4290529) B4290529
theorem B3812075 : Blo 1693547 3812075 := bstep (se 1 (by rfl) ⟨2859056, by rfl⟩ : syracuseStep 3812075 = 5718113) B5718113
theorem B2542319 : Blo 1693547 2542319 := bstep (se 1 (by rfl) ⟨1906739, by rfl⟩ : syracuseStep 2542319 = 3813479) B3813479
theorem B6433577 : Blo 1693547 6433577 := bstep (se 2 (by rfl) ⟨2412591, by rfl⟩ : syracuseStep 6433577 = 4825183) B4825183
theorem B2411327 : Blo 1693547 2411327 := bstep (se 1 (by rfl) ⟨1808495, by rfl⟩ : syracuseStep 2411327 = 3616991) B3616991
theorem B13740887 : Blo 1693547 13740887 := bstep (se 1 (by rfl) ⟨10305665, by rfl⟩ : syracuseStep 13740887 = 20611331) B20611331
theorem B2542439 : Blo 1693547 2542439 := bstep (se 1 (by rfl) ⟨1906829, by rfl⟩ : syracuseStep 2542439 = 3813659) B3813659
theorem B4287401 : Blo 1693547 4287401 := bstep (se 2 (by rfl) ⟨1607775, by rfl⟩ : syracuseStep 4287401 = 3215551) B3215551
theorem B6433789 : Blo 1693547 6433789 := bstep (se 3 (by rfl) ⟨1206335, by rfl⟩ : syracuseStep 6433789 = 2412671) B2412671
theorem B2542697 : Blo 1693547 2542697 := bstep (se 2 (by rfl) ⟨953511, by rfl⟩ : syracuseStep 2542697 = 1907023) B1907023
theorem B2542703 : Blo 1693547 2542703 := bstep (se 1 (by rfl) ⟨1907027, by rfl⟩ : syracuseStep 2542703 = 3814055) B3814055
theorem B5721299 : Blo 1693547 5721299 := bstep (se 1 (by rfl) ⟨4290974, by rfl⟩ : syracuseStep 5721299 = 8581949) B8581949
theorem B5721353 : Blo 1693547 5721353 := bstep (se 2 (by rfl) ⟨2145507, by rfl⟩ : syracuseStep 5721353 = 4291015) B4291015
theorem B4288079 : Blo 1693547 4288079 := bstep (se 1 (by rfl) ⟨3216059, by rfl⟩ : syracuseStep 4288079 = 6432119) B6432119
theorem B3813083 : Blo 1693547 3813083 := bstep (se 1 (by rfl) ⟨2859812, by rfl⟩ : syracuseStep 3813083 = 5719625) B5719625
theorem B6434761 : Blo 1693547 6434761 := bstep (se 2 (by rfl) ⟨2413035, by rfl⟩ : syracuseStep 6434761 = 4826071) B4826071
theorem B3215315 : Blo 1693547 3215315 := bstep (se 1 (by rfl) ⟨2411486, by rfl⟩ : syracuseStep 3215315 = 4822973) B4822973
theorem B24768595 : Blo 1693547 24768595 := bstep (se 1 (by rfl) ⟨18576446, by rfl⟩ : syracuseStep 24768595 = 37152893) B37152893
theorem B24752227 : Blo 1693547 24752227 := bstep (se 1 (by rfl) ⟨18564170, by rfl⟩ : syracuseStep 24752227 = 37128341) B37128341
theorem B46395737 : Blo 1693547 46395737 := bstep (se 2 (by rfl) ⟨17398401, by rfl⟩ : syracuseStep 46395737 = 34796803) B34796803
theorem B3215771 : Blo 1693547 3215771 := bstep (se 1 (by rfl) ⟨2411828, by rfl⟩ : syracuseStep 3215771 = 4823657) B4823657
theorem B4289071 : Blo 1693547 4289071 := bstep (se 1 (by rfl) ⟨3216803, by rfl⟩ : syracuseStep 4289071 = 6433607) B6433607
theorem B47026955 : Blo 1693547 47026955 := bstep (se 1 (by rfl) ⟨35270216, by rfl⟩ : syracuseStep 47026955 = 70540433) B70540433
theorem B3814379 : Blo 1693547 3814379 := bstep (se 1 (by rfl) ⟨2860784, by rfl⟩ : syracuseStep 3814379 = 5721569) B5721569
theorem B8574011 : Blo 1693547 8574011 := bstep (se 1 (by rfl) ⟨6430508, by rfl⟩ : syracuseStep 8574011 = 12861017) B12861017
theorem B4347631 : Blo 1693547 4347631 := bstep (se 1 (by rfl) ⟨3260723, by rfl⟩ : syracuseStep 4347631 = 6521447) B6521447
theorem B5715791 : Blo 1693547 5715791 := bstep (se 1 (by rfl) ⟨4286843, by rfl⟩ : syracuseStep 5715791 = 8573687) B8573687
theorem B6436705 : Blo 1693547 6436705 := bstep (se 2 (by rfl) ⟨2413764, by rfl⟩ : syracuseStep 6436705 = 4827529) B4827529
theorem B1693607 : Blo 1693547 1693607 := bstep (se 1 (by rfl) ⟨1270205, by rfl⟩ : syracuseStep 1693607 = 2540411) B2540411
theorem B26458103 : Blo 1693547 26458103 := bstep (se 1 (by rfl) ⟨19843577, by rfl⟩ : syracuseStep 26458103 = 39687155) B39687155
theorem B1693691 : Blo 1693547 1693691 := bstep (se 1 (by rfl) ⟨1270268, by rfl⟩ : syracuseStep 1693691 = 2540537) B2540537
theorem B1693727 : Blo 1693547 1693727 := bstep (se 1 (by rfl) ⟨1270295, by rfl⟩ : syracuseStep 1693727 = 2540591) B2540591
theorem B11597897 : Blo 1693547 11597897 := bstep (se 2 (by rfl) ⟨4349211, by rfl⟩ : syracuseStep 11597897 = 8698423) B8698423
theorem B1693807 : Blo 1693547 1693807 := bstep (se 1 (by rfl) ⟨1270355, by rfl⟩ : syracuseStep 1693807 = 2540711) B2540711
theorem B12220607 : Blo 1693547 12220607 := bstep (se 1 (by rfl) ⟨9165455, by rfl⟩ : syracuseStep 12220607 = 18330911) B18330911
theorem B1693935 : Blo 1693547 1693935 := bstep (se 1 (by rfl) ⟨1270451, by rfl⟩ : syracuseStep 1693935 = 2540903) B2540903
theorem B9787805 : Blo 1693547 9787805 := bstep (se 3 (by rfl) ⟨1835213, by rfl⟩ : syracuseStep 9787805 = 3670427) B3670427
theorem B5716385 : Blo 1693547 5716385 := bstep (se 2 (by rfl) ⟨2143644, by rfl⟩ : syracuseStep 5716385 = 4287289) B4287289
theorem B5798375 : Blo 1693547 5798375 := bstep (se 1 (by rfl) ⟨4348781, by rfl⟩ : syracuseStep 5798375 = 8697563) B8697563
theorem B5429767 : Blo 1693547 5429767 := bstep (se 1 (by rfl) ⟨4072325, by rfl⟩ : syracuseStep 5429767 = 8144651) B8144651
theorem B41777693 : Blo 1693547 41777693 := bstep (se 3 (by rfl) ⟨7833317, by rfl⟩ : syracuseStep 41777693 = 15666635) B15666635
theorem B1694363 : Blo 1693547 1694363 := bstep (se 1 (by rfl) ⟨1270772, by rfl⟩ : syracuseStep 1694363 = 2541545) B2541545
theorem B1694459 : Blo 1693547 1694459 := bstep (se 1 (by rfl) ⟨1270844, by rfl⟩ : syracuseStep 1694459 = 2541689) B2541689
theorem B1694591 : Blo 1693547 1694591 := bstep (se 1 (by rfl) ⟨1270943, by rfl⟩ : syracuseStep 1694591 = 2541887) B2541887
theorem B6872003 : Blo 1693547 6872003 := bstep (se 1 (by rfl) ⟨5154002, by rfl⟩ : syracuseStep 6872003 = 10308005) B10308005
theorem B1694687 : Blo 1693547 1694687 := bstep (se 1 (by rfl) ⟨1271015, by rfl⟩ : syracuseStep 1694687 = 2542031) B2542031
theorem B1694715 : Blo 1693547 1694715 := bstep (se 1 (by rfl) ⟨1271036, by rfl⟩ : syracuseStep 1694715 = 2542073) B2542073
theorem B1694747 : Blo 1693547 1694747 := bstep (se 1 (by rfl) ⟨1271060, by rfl⟩ : syracuseStep 1694747 = 2542121) B2542121
theorem B12213287 : Blo 1693547 12213287 := bstep (se 1 (by rfl) ⟨9159965, by rfl⟩ : syracuseStep 12213287 = 18319931) B18319931
theorem B2858159 : Blo 1693547 2858159 := bstep (se 1 (by rfl) ⟨2143619, by rfl⟩ : syracuseStep 2858159 = 4287239) B4287239
theorem B11156777 : Blo 1693547 11156777 := bstep (se 2 (by rfl) ⟨4183791, by rfl⟩ : syracuseStep 11156777 = 8367583) B8367583
theorem B1695039 : Blo 1693547 1695039 := bstep (se 1 (by rfl) ⟨1271279, by rfl⟩ : syracuseStep 1695039 = 2542559) B2542559
theorem B12213575 : Blo 1693547 12213575 := bstep (se 1 (by rfl) ⟨9160181, by rfl⟩ : syracuseStep 12213575 = 18320363) B18320363
theorem B3259739 : Blo 1693547 3259739 := bstep (se 1 (by rfl) ⟨2444804, by rfl⟩ : syracuseStep 3259739 = 4889609) B4889609
theorem B6110639 : Blo 1693547 6110639 := bstep (se 1 (by rfl) ⟨4582979, by rfl⟩ : syracuseStep 6110639 = 9165959) B9165959
theorem B1695335 : Blo 1693547 1695335 := bstep (se 1 (by rfl) ⟨1271501, by rfl⟩ : syracuseStep 1695335 = 2543003) B2543003
theorem B10853999 : Blo 1693547 10853999 := bstep (se 1 (by rfl) ⟨8140499, by rfl⟩ : syracuseStep 10853999 = 16280999) B16280999
theorem B52149905 : Blo 1693547 52149905 := bstep (se 2 (by rfl) ⟨19556214, by rfl⟩ : syracuseStep 52149905 = 39112429) B39112429
theorem B5717843 : Blo 1693547 5717843 := bstep (se 1 (by rfl) ⟨4288382, by rfl⟩ : syracuseStep 5717843 = 8576765) B8576765
theorem B11599811 : Blo 1693547 11599811 := bstep (se 1 (by rfl) ⟨8699858, by rfl⟩ : syracuseStep 11599811 = 17399717) B17399717
theorem B31351303 : Blo 1693547 31351303 := bstep (se 1 (by rfl) ⟨23513477, by rfl⟩ : syracuseStep 31351303 = 47026955) B47026955
theorem B5718761 : Blo 1693547 5718761 := bstep (se 2 (by rfl) ⟨2144535, by rfl⟩ : syracuseStep 5718761 = 4289071) B4289071
theorem B3810527 : Blo 1693547 3810527 := bstep (se 1 (by rfl) ⟨2857895, by rfl⟩ : syracuseStep 3810527 = 5715791) B5715791
theorem B65111363 : Blo 1693547 65111363 := bstep (se 1 (by rfl) ⟨48833522, by rfl⟩ : syracuseStep 65111363 = 97667045) B97667045
theorem B17638735 : Blo 1693547 17638735 := bstep (se 1 (by rfl) ⟨13229051, by rfl⟩ : syracuseStep 17638735 = 26458103) B26458103
theorem B8578385 : Blo 1693547 8578385 := bstep (se 2 (by rfl) ⟨3216894, by rfl⟩ : syracuseStep 8578385 = 6433789) B6433789
theorem B3810923 : Blo 1693547 3810923 := bstep (se 1 (by rfl) ⟨2858192, by rfl⟩ : syracuseStep 3810923 = 5716385) B5716385
theorem B2541215 : Blo 1693547 2541215 := bstep (se 1 (by rfl) ⟨1905911, by rfl⟩ : syracuseStep 2541215 = 3811823) B3811823
theorem B2541383 : Blo 1693547 2541383 := bstep (se 1 (by rfl) ⟨1906037, by rfl⟩ : syracuseStep 2541383 = 3812075) B3812075
theorem B4581335 : Blo 1693547 4581335 := bstep (se 1 (by rfl) ⟨3436001, by rfl⟩ : syracuseStep 4581335 = 6872003) B6872003
theorem B28969001 : Blo 1693547 28969001 := bstep (se 2 (by rfl) ⟨10863375, by rfl⟩ : syracuseStep 28969001 = 21726751) B21726751
theorem B244475981 : Blo 1693547 244475981 := bstep (se 3 (by rfl) ⟨45839246, by rfl⟩ : syracuseStep 244475981 = 91678493) B91678493
theorem B2173159 : Blo 1693547 2173159 := bstep (se 1 (by rfl) ⟨1629869, by rfl⟩ : syracuseStep 2173159 = 3259739) B3259739
theorem B4073759 : Blo 1693547 4073759 := bstep (se 1 (by rfl) ⟨3055319, by rfl⟩ : syracuseStep 4073759 = 6110639) B6110639
theorem B7235999 : Blo 1693547 7235999 := bstep (se 1 (by rfl) ⟨5426999, by rfl⟩ : syracuseStep 7235999 = 10853999) B10853999
theorem B2542055 : Blo 1693547 2542055 := bstep (se 1 (by rfl) ⟨1906541, by rfl⟩ : syracuseStep 2542055 = 3813083) B3813083
theorem B3811895 : Blo 1693547 3811895 := bstep (se 1 (by rfl) ⟨2858921, by rfl⟩ : syracuseStep 3811895 = 5717843) B5717843
theorem B8579681 : Blo 1693547 8579681 := bstep (se 2 (by rfl) ⟨3217380, by rfl⟩ : syracuseStep 8579681 = 6434761) B6434761
theorem B3812201 : Blo 1693547 3812201 := bstep (se 2 (by rfl) ⟨1429575, by rfl⟩ : syracuseStep 3812201 = 2859151) B2859151
theorem B3812255 : Blo 1693547 3812255 := bstep (se 1 (by rfl) ⟨2859191, by rfl⟩ : syracuseStep 3812255 = 5718383) B5718383
theorem B37161949 : Blo 1693547 37161949 := bstep (se 3 (by rfl) ⟨6967865, by rfl⟩ : syracuseStep 37161949 = 13935731) B13935731
theorem B132099173 : Blo 1693547 132099173 := bstep (se 4 (by rfl) ⟨12384297, by rfl⟩ : syracuseStep 132099173 = 24768595) B24768595
theorem B16288913 : Blo 1693547 16288913 := bstep (se 2 (by rfl) ⟨6108342, by rfl⟩ : syracuseStep 16288913 = 12216685) B12216685
theorem B2542919 : Blo 1693547 2542919 := bstep (se 1 (by rfl) ⟨1907189, by rfl⟩ : syracuseStep 2542919 = 3814379) B3814379
theorem B3812975 : Blo 1693547 3812975 := bstep (se 1 (by rfl) ⟨2859731, by rfl⟩ : syracuseStep 3812975 = 5719463) B5719463
theorem B18329489 : Blo 1693547 18329489 := bstep (se 2 (by rfl) ⟨6873558, by rfl⟩ : syracuseStep 18329489 = 13747117) B13747117
theorem B8147071 : Blo 1693547 8147071 := bstep (se 1 (by rfl) ⟨6110303, by rfl⟩ : syracuseStep 8147071 = 12220607) B12220607
theorem B6435035 : Blo 1693547 6435035 := bstep (se 1 (by rfl) ⟨4826276, by rfl⟩ : syracuseStep 6435035 = 9652553) B9652553
theorem B6435065 : Blo 1693547 6435065 := bstep (se 2 (by rfl) ⟨2413149, by rfl⟩ : syracuseStep 6435065 = 4826299) B4826299
theorem B6525203 : Blo 1693547 6525203 := bstep (se 1 (by rfl) ⟨4893902, by rfl⟩ : syracuseStep 6525203 = 9787805) B9787805
theorem B3813803 : Blo 1693547 3813803 := bstep (se 1 (by rfl) ⟨2860352, by rfl⟩ : syracuseStep 3813803 = 5720705) B5720705
theorem B4289051 : Blo 1693547 4289051 := bstep (se 1 (by rfl) ⟨3216788, by rfl⟩ : syracuseStep 4289051 = 6433577) B6433577
theorem B1905439 : Blo 1693547 1905439 := bstep (se 1 (by rfl) ⟨1429079, by rfl⟩ : syracuseStep 1905439 = 2858159) B2858159
theorem B3814199 : Blo 1693547 3814199 := bstep (se 1 (by rfl) ⟨2860649, by rfl⟩ : syracuseStep 3814199 = 5721299) B5721299
theorem B3814235 : Blo 1693547 3814235 := bstep (se 1 (by rfl) ⟨2860676, by rfl⟩ : syracuseStep 3814235 = 5721353) B5721353
theorem B5796841 : Blo 1693547 5796841 := bstep (se 2 (by rfl) ⟨2173815, by rfl⟩ : syracuseStep 5796841 = 4347631) B4347631
theorem B8582273 : Blo 1693547 8582273 := bstep (se 2 (by rfl) ⟨3218352, by rfl⟩ : syracuseStep 8582273 = 6436705) B6436705
theorem B8574173 : Blo 1693547 8574173 := bstep (se 3 (by rfl) ⟨1607657, by rfl⟩ : syracuseStep 8574173 = 3215315) B3215315
theorem B33002969 : Blo 1693547 33002969 := bstep (se 2 (by rfl) ⟨12376113, by rfl⟩ : syracuseStep 33002969 = 24752227) B24752227
theorem B30930491 : Blo 1693547 30930491 := bstep (se 1 (by rfl) ⟨23197868, by rfl⟩ : syracuseStep 30930491 = 46395737) B46395737
theorem B2143847 : Blo 1693547 2143847 := bstep (se 1 (by rfl) ⟨1607885, by rfl⟩ : syracuseStep 2143847 = 3215771) B3215771
theorem B7239689 : Blo 1693547 7239689 := bstep (se 2 (by rfl) ⟨2714883, by rfl⟩ : syracuseStep 7239689 = 5429767) B5429767
theorem B5716007 : Blo 1693547 5716007 := bstep (se 1 (by rfl) ⟨4287005, by rfl⟩ : syracuseStep 5716007 = 8574011) B8574011
theorem B13228343 : Blo 1693547 13228343 := bstep (se 1 (by rfl) ⟨9921257, by rfl⟩ : syracuseStep 13228343 = 19842515) B19842515
theorem B4823543 : Blo 1693547 4823543 := bstep (se 1 (by rfl) ⟨3617657, by rfl⟩ : syracuseStep 4823543 = 7235315) B7235315
theorem B30907079 : Blo 1693547 30907079 := bstep (se 1 (by rfl) ⟨23180309, by rfl⟩ : syracuseStep 30907079 = 46360619) B46360619
theorem B7731931 : Blo 1693547 7731931 := bstep (se 1 (by rfl) ⟨5798948, by rfl⟩ : syracuseStep 7731931 = 11597897) B11597897
theorem B4823975 : Blo 1693547 4823975 := bstep (se 1 (by rfl) ⟨3617981, by rfl⟩ : syracuseStep 4823975 = 7235963) B7235963
theorem B3865583 : Blo 1693547 3865583 := bstep (se 1 (by rfl) ⟨2899187, by rfl⟩ : syracuseStep 3865583 = 5798375) B5798375
theorem B27851795 : Blo 1693547 27851795 := bstep (se 1 (by rfl) ⟨20888846, by rfl⟩ : syracuseStep 27851795 = 41777693) B41777693
theorem B1694879 : Blo 1693547 1694879 := bstep (se 1 (by rfl) ⟨1271159, by rfl⟩ : syracuseStep 1694879 = 2542319) B2542319
theorem B1694959 : Blo 1693547 1694959 := bstep (se 1 (by rfl) ⟨1271219, by rfl⟩ : syracuseStep 1694959 = 2542439) B2542439
theorem B2858267 : Blo 1693547 2858267 := bstep (se 1 (by rfl) ⟨2143700, by rfl⟩ : syracuseStep 2858267 = 4287401) B4287401
theorem B8142191 : Blo 1693547 8142191 := bstep (se 1 (by rfl) ⟨6106643, by rfl⟩ : syracuseStep 8142191 = 12213287) B12213287
theorem B1695131 : Blo 1693547 1695131 := bstep (se 1 (by rfl) ⟨1271348, by rfl⟩ : syracuseStep 1695131 = 2542697) B2542697
theorem B1695135 : Blo 1693547 1695135 := bstep (se 1 (by rfl) ⟨1271351, by rfl⟩ : syracuseStep 1695135 = 2542703) B2542703
theorem B6430205 : Blo 1693547 6430205 := bstep (se 3 (by rfl) ⟨1205663, by rfl⟩ : syracuseStep 6430205 = 2411327) B2411327
theorem B7437851 : Blo 1693547 7437851 := bstep (se 1 (by rfl) ⟨5578388, by rfl⟩ : syracuseStep 7437851 = 11156777) B11156777
theorem B8142383 : Blo 1693547 8142383 := bstep (se 1 (by rfl) ⟨6106787, by rfl⟩ : syracuseStep 8142383 = 12213575) B12213575
theorem B52878905 : Blo 1693547 52878905 := bstep (se 2 (by rfl) ⟨19829589, by rfl⟩ : syracuseStep 52878905 = 39659179) B39659179
theorem B36642365 : Blo 1693547 36642365 := bstep (se 3 (by rfl) ⟨6870443, by rfl⟩ : syracuseStep 36642365 = 13740887) B13740887
theorem B2858719 : Blo 1693547 2858719 := bstep (se 1 (by rfl) ⟨2144039, by rfl⟩ : syracuseStep 2858719 = 4288079) B4288079
theorem B34766603 : Blo 1693547 34766603 := bstep (se 1 (by rfl) ⟨26074952, by rfl⟩ : syracuseStep 34766603 = 52149905) B52149905
theorem B17620901 : Blo 1693547 17620901 := bstep (se 4 (by rfl) ⟨1651959, by rfl⟩ : syracuseStep 17620901 = 3303919) B3303919
theorem B7733207 : Blo 1693547 7733207 := bstep (se 1 (by rfl) ⟨5799905, by rfl⟩ : syracuseStep 7733207 = 11599811) B11599811
theorem B167206949 : Blo 1693547 167206949 := bstep (se 4 (by rfl) ⟨15675651, by rfl⟩ : syracuseStep 167206949 = 31351303) B31351303
theorem B10862761 : Blo 1693547 10862761 := bstep (se 2 (by rfl) ⟨4073535, by rfl⟩ : syracuseStep 10862761 = 8147071) B8147071
theorem B2859367 : Blo 1693547 2859367 := bstep (se 1 (by rfl) ⟨2144525, by rfl⟩ : syracuseStep 2859367 = 4289051) B4289051
theorem B2540351 : Blo 1693547 2540351 := bstep (se 1 (by rfl) ⟨1905263, by rfl⟩ : syracuseStep 2540351 = 3810527) B3810527
theorem B5718923 : Blo 1693547 5718923 := bstep (se 1 (by rfl) ⟨4289192, by rfl⟩ : syracuseStep 5718923 = 8578385) B8578385
theorem B20620327 : Blo 1693547 20620327 := bstep (se 1 (by rfl) ⟨15465245, by rfl⟩ : syracuseStep 20620327 = 30930491) B30930491
theorem B2540585 : Blo 1693547 2540585 := bstep (se 2 (by rfl) ⟨952719, by rfl⟩ : syracuseStep 2540585 = 1905439) B1905439
theorem B2540615 : Blo 1693547 2540615 := bstep (se 1 (by rfl) ⟨1905461, by rfl⟩ : syracuseStep 2540615 = 3810923) B3810923
theorem B88007917 : Blo 1693547 88007917 := bstep (se 3 (by rfl) ⟨16501484, by rfl⟩ : syracuseStep 88007917 = 33002969) B33002969
theorem B4826459 : Blo 1693547 4826459 := bstep (se 1 (by rfl) ⟨3619844, by rfl⟩ : syracuseStep 4826459 = 7239689) B7239689
theorem B3810671 : Blo 1693547 3810671 := bstep (se 1 (by rfl) ⟨2858003, by rfl⟩ : syracuseStep 3810671 = 5716007) B5716007
theorem B2541263 : Blo 1693547 2541263 := bstep (se 1 (by rfl) ⟨1905947, by rfl⟩ : syracuseStep 2541263 = 3811895) B3811895
theorem B5719787 : Blo 1693547 5719787 := bstep (se 1 (by rfl) ⟨4289840, by rfl⟩ : syracuseStep 5719787 = 8579681) B8579681
theorem B20604719 : Blo 1693547 20604719 := bstep (se 1 (by rfl) ⟨15453539, by rfl⟩ : syracuseStep 20604719 = 30907079) B30907079
theorem B2541467 : Blo 1693547 2541467 := bstep (se 1 (by rfl) ⟨1906100, by rfl⟩ : syracuseStep 2541467 = 3812201) B3812201
theorem B2541503 : Blo 1693547 2541503 := bstep (se 1 (by rfl) ⟨1906127, by rfl⟩ : syracuseStep 2541503 = 3812255) B3812255
theorem B88066115 : Blo 1693547 88066115 := bstep (se 1 (by rfl) ⟨66049586, by rfl⟩ : syracuseStep 88066115 = 132099173) B132099173
theorem B3811625 : Blo 1693547 3811625 := bstep (se 2 (by rfl) ⟨1429359, by rfl⟩ : syracuseStep 3811625 = 2858719) B2858719
theorem B4286803 : Blo 1693547 4286803 := bstep (se 1 (by rfl) ⟨3215102, by rfl⟩ : syracuseStep 4286803 = 6430205) B6430205
theorem B4958567 : Blo 1693547 4958567 := bstep (se 1 (by rfl) ⟨3718925, by rfl⟩ : syracuseStep 4958567 = 7437851) B7437851
theorem B35252603 : Blo 1693547 35252603 := bstep (se 1 (by rfl) ⟨26439452, by rfl⟩ : syracuseStep 35252603 = 52878905) B52878905
theorem B2541983 : Blo 1693547 2541983 := bstep (se 1 (by rfl) ⟨1906487, by rfl⟩ : syracuseStep 2541983 = 3812975) B3812975
theorem B12863933 : Blo 1693547 12863933 := bstep (se 3 (by rfl) ⟨2411987, by rfl⟩ : syracuseStep 12863933 = 4823975) B4823975
theorem B23177735 : Blo 1693547 23177735 := bstep (se 1 (by rfl) ⟨17383301, by rfl⟩ : syracuseStep 23177735 = 34766603) B34766603
theorem B10308221 : Blo 1693547 10308221 := bstep (se 3 (by rfl) ⟨1932791, by rfl⟩ : syracuseStep 10308221 = 3865583) B3865583
theorem B5155471 : Blo 1693547 5155471 := bstep (se 1 (by rfl) ⟨3866603, by rfl⟩ : syracuseStep 5155471 = 7733207) B7733207
theorem B69602165 : Blo 1693547 69602165 := bstep (se 5 (by rfl) ⟨3262601, by rfl⟩ : syracuseStep 69602165 = 6525203) B6525203
theorem B2542535 : Blo 1693547 2542535 := bstep (se 1 (by rfl) ⟨1906901, by rfl⟩ : syracuseStep 2542535 = 3813803) B3813803
theorem B3812507 : Blo 1693547 3812507 := bstep (se 1 (by rfl) ⟨2859380, by rfl⟩ : syracuseStep 3812507 = 5718761) B5718761
theorem B2542799 : Blo 1693547 2542799 := bstep (se 1 (by rfl) ⟨1907099, by rfl⟩ : syracuseStep 2542799 = 3814199) B3814199
theorem B2542823 : Blo 1693547 2542823 := bstep (se 1 (by rfl) ⟨1907117, by rfl⟩ : syracuseStep 2542823 = 3814235) B3814235
theorem B5721515 : Blo 1693547 5721515 := bstep (se 1 (by rfl) ⟨4291136, by rfl⟩ : syracuseStep 5721515 = 8582273) B8582273
theorem B10309241 : Blo 1693547 10309241 := bstep (se 2 (by rfl) ⟨3865965, by rfl⟩ : syracuseStep 10309241 = 7731931) B7731931
theorem B49549265 : Blo 1693547 49549265 := bstep (se 2 (by rfl) ⟨18580974, by rfl⟩ : syracuseStep 49549265 = 37161949) B37161949
theorem B7729121 : Blo 1693547 7729121 := bstep (se 2 (by rfl) ⟨2898420, by rfl⟩ : syracuseStep 7729121 = 5796841) B5796841
theorem B19312667 : Blo 1693547 19312667 := bstep (se 1 (by rfl) ⟨14484500, by rfl⟩ : syracuseStep 19312667 = 28969001) B28969001
theorem B162983987 : Blo 1693547 162983987 := bstep (se 1 (by rfl) ⟨122237990, by rfl⟩ : syracuseStep 162983987 = 244475981) B244475981
theorem B2715839 : Blo 1693547 2715839 := bstep (se 1 (by rfl) ⟨2036879, by rfl⟩ : syracuseStep 2715839 = 4073759) B4073759
theorem B8818895 : Blo 1693547 8818895 := bstep (se 1 (by rfl) ⟨6614171, by rfl⟩ : syracuseStep 8818895 = 13228343) B13228343
theorem B3215695 : Blo 1693547 3215695 := bstep (se 1 (by rfl) ⟨2411771, by rfl⟩ : syracuseStep 3215695 = 4823543) B4823543
theorem B18567863 : Blo 1693547 18567863 := bstep (se 1 (by rfl) ⟨13925897, by rfl⟩ : syracuseStep 18567863 = 27851795) B27851795
theorem B10859275 : Blo 1693547 10859275 := bstep (se 1 (by rfl) ⟨8144456, by rfl⟩ : syracuseStep 10859275 = 16288913) B16288913
theorem B1905511 : Blo 1693547 1905511 := bstep (se 1 (by rfl) ⟨1429133, by rfl⟩ : syracuseStep 1905511 = 2858267) B2858267
theorem B5428127 : Blo 1693547 5428127 := bstep (se 1 (by rfl) ⟨4071095, by rfl⟩ : syracuseStep 5428127 = 8142191) B8142191
theorem B5428255 : Blo 1693547 5428255 := bstep (se 1 (by rfl) ⟨4071191, by rfl⟩ : syracuseStep 5428255 = 8142383) B8142383
theorem B12219659 : Blo 1693547 12219659 := bstep (se 1 (by rfl) ⟨9164744, by rfl⟩ : syracuseStep 12219659 = 18329489) B18329489
theorem B4290023 : Blo 1693547 4290023 := bstep (se 1 (by rfl) ⟨3217517, by rfl⟩ : syracuseStep 4290023 = 6435035) B6435035
theorem B4290043 : Blo 1693547 4290043 := bstep (se 1 (by rfl) ⟨3217532, by rfl⟩ : syracuseStep 4290043 = 6435065) B6435065
theorem B2897545 : Blo 1693547 2897545 := bstep (se 2 (by rfl) ⟨1086579, by rfl⟩ : syracuseStep 2897545 = 2173159) B2173159
theorem B5716115 : Blo 1693547 5716115 := bstep (se 1 (by rfl) ⟨4287086, by rfl⟩ : syracuseStep 5716115 = 8574173) B8574173
theorem B43407575 : Blo 1693547 43407575 := bstep (se 1 (by rfl) ⟨32555681, by rfl⟩ : syracuseStep 43407575 = 65111363) B65111363
theorem B1694143 : Blo 1693547 1694143 := bstep (se 1 (by rfl) ⟨1270607, by rfl⟩ : syracuseStep 1694143 = 2541215) B2541215
theorem B1694255 : Blo 1693547 1694255 := bstep (se 1 (by rfl) ⟨1270691, by rfl⟩ : syracuseStep 1694255 = 2541383) B2541383
theorem B3054223 : Blo 1693547 3054223 := bstep (se 1 (by rfl) ⟨2290667, by rfl⟩ : syracuseStep 3054223 = 4581335) B4581335
theorem B5716925 : Blo 1693547 5716925 := bstep (se 3 (by rfl) ⟨1071923, by rfl⟩ : syracuseStep 5716925 = 2143847) B2143847
theorem B4823999 : Blo 1693547 4823999 := bstep (se 1 (by rfl) ⟨3617999, by rfl⟩ : syracuseStep 4823999 = 7235999) B7235999
theorem B1694703 : Blo 1693547 1694703 := bstep (se 1 (by rfl) ⟨1271027, by rfl⟩ : syracuseStep 1694703 = 2542055) B2542055
theorem B23518313 : Blo 1693547 23518313 := bstep (se 2 (by rfl) ⟨8819367, by rfl⟩ : syracuseStep 23518313 = 17638735) B17638735
theorem B1695279 : Blo 1693547 1695279 := bstep (se 1 (by rfl) ⟨1271459, by rfl⟩ : syracuseStep 1695279 = 2542919) B2542919
theorem B24428243 : Blo 1693547 24428243 := bstep (se 1 (by rfl) ⟨18321182, by rfl⟩ : syracuseStep 24428243 = 36642365) B36642365
theorem B11747267 : Blo 1693547 11747267 := bstep (se 1 (by rfl) ⟨8810450, by rfl⟩ : syracuseStep 11747267 = 17620901) B17620901
theorem B1810559 : Blo 1693547 1810559 := bstep (se 1 (by rfl) ⟨1357919, by rfl⟩ : syracuseStep 1810559 = 2715839) B2715839
theorem B14483681 : Blo 1693547 14483681 := bstep (se 2 (by rfl) ⟨5431380, by rfl⟩ : syracuseStep 14483681 = 10862761) B10862761
theorem B12378575 : Blo 1693547 12378575 := bstep (se 1 (by rfl) ⟨9283931, by rfl⟩ : syracuseStep 12378575 = 18567863) B18567863
theorem B4072297 : Blo 1693547 4072297 := bstep (se 2 (by rfl) ⟨1527111, by rfl⟩ : syracuseStep 4072297 = 3054223) B3054223
theorem B2540447 : Blo 1693547 2540447 := bstep (se 1 (by rfl) ⟨1905335, by rfl⟩ : syracuseStep 2540447 = 3810671) B3810671
theorem B2860015 : Blo 1693547 2860015 := bstep (se 1 (by rfl) ⟨2145011, by rfl⟩ : syracuseStep 2860015 = 4290023) B4290023
theorem B2540681 : Blo 1693547 2540681 := bstep (se 2 (by rfl) ⟨952755, by rfl⟩ : syracuseStep 2540681 = 1905511) B1905511
theorem B27493769 : Blo 1693547 27493769 := bstep (se 2 (by rfl) ⟨10310163, by rfl⟩ : syracuseStep 27493769 = 20620327) B20620327
theorem B3810743 : Blo 1693547 3810743 := bstep (se 1 (by rfl) ⟨2858057, by rfl⟩ : syracuseStep 3810743 = 5716115) B5716115
theorem B2541083 : Blo 1693547 2541083 := bstep (se 1 (by rfl) ⟨1905812, by rfl⟩ : syracuseStep 2541083 = 3811625) B3811625
theorem B117343889 : Blo 1693547 117343889 := bstep (se 2 (by rfl) ⟨44003958, by rfl⟩ : syracuseStep 117343889 = 88007917) B88007917
theorem B15451823 : Blo 1693547 15451823 := bstep (se 1 (by rfl) ⟨11588867, by rfl⟩ : syracuseStep 15451823 = 23177735) B23177735
theorem B46401443 : Blo 1693547 46401443 := bstep (se 1 (by rfl) ⟨34801082, by rfl⟩ : syracuseStep 46401443 = 69602165) B69602165
theorem B3811283 : Blo 1693547 3811283 := bstep (se 1 (by rfl) ⟨2858462, by rfl⟩ : syracuseStep 3811283 = 5716925) B5716925
theorem B5720057 : Blo 1693547 5720057 := bstep (se 2 (by rfl) ⟨2145021, by rfl⟩ : syracuseStep 5720057 = 4290043) B4290043
theorem B2541671 : Blo 1693547 2541671 := bstep (se 1 (by rfl) ⟨1906253, by rfl⟩ : syracuseStep 2541671 = 3812507) B3812507
theorem B33032843 : Blo 1693547 33032843 := bstep (se 1 (by rfl) ⟨24774632, by rfl⟩ : syracuseStep 33032843 = 49549265) B49549265
theorem B111471299 : Blo 1693547 111471299 := bstep (se 1 (by rfl) ⟨83603474, by rfl⟩ : syracuseStep 111471299 = 167206949) B167206949
theorem B4287593 : Blo 1693547 4287593 := bstep (se 2 (by rfl) ⟨1607847, by rfl⟩ : syracuseStep 4287593 = 3215695) B3215695
theorem B3812489 : Blo 1693547 3812489 := bstep (se 2 (by rfl) ⟨1429683, by rfl⟩ : syracuseStep 3812489 = 2859367) B2859367
theorem B3812615 : Blo 1693547 3812615 := bstep (se 1 (by rfl) ⟨2859461, by rfl⟩ : syracuseStep 3812615 = 5718923) B5718923
theorem B27495845 : Blo 1693547 27495845 := bstep (se 4 (by rfl) ⟨2577735, by rfl⟩ : syracuseStep 27495845 = 5155471) B5155471
theorem B8146439 : Blo 1693547 8146439 := bstep (se 1 (by rfl) ⟨6109829, by rfl⟩ : syracuseStep 8146439 = 12219659) B12219659
theorem B14479033 : Blo 1693547 14479033 := bstep (se 2 (by rfl) ⟨5429637, by rfl⟩ : syracuseStep 14479033 = 10859275) B10859275
theorem B3813191 : Blo 1693547 3813191 := bstep (se 1 (by rfl) ⟨2859893, by rfl⟩ : syracuseStep 3813191 = 5719787) B5719787
theorem B7237673 : Blo 1693547 7237673 := bstep (se 2 (by rfl) ⟨2714127, by rfl⟩ : syracuseStep 7237673 = 5428255) B5428255
theorem B28938383 : Blo 1693547 28938383 := bstep (se 1 (by rfl) ⟨21703787, by rfl⟩ : syracuseStep 28938383 = 43407575) B43407575
theorem B3305711 : Blo 1693547 3305711 := bstep (se 1 (by rfl) ⟨2479283, by rfl⟩ : syracuseStep 3305711 = 4958567) B4958567
theorem B3215999 : Blo 1693547 3215999 := bstep (se 1 (by rfl) ⟨2411999, by rfl⟩ : syracuseStep 3215999 = 4823999) B4823999
theorem B3863393 : Blo 1693547 3863393 := bstep (se 2 (by rfl) ⟨1448772, by rfl⟩ : syracuseStep 3863393 = 2897545) B2897545
theorem B3814343 : Blo 1693547 3814343 := bstep (se 1 (by rfl) ⟨2860757, by rfl⟩ : syracuseStep 3814343 = 5721515) B5721515
theorem B12875111 : Blo 1693547 12875111 := bstep (se 1 (by rfl) ⟨9656333, by rfl⟩ : syracuseStep 12875111 = 19312667) B19312667
theorem B108655991 : Blo 1693547 108655991 := bstep (se 1 (by rfl) ⟨81491993, by rfl⟩ : syracuseStep 108655991 = 162983987) B162983987
theorem B5715737 : Blo 1693547 5715737 := bstep (se 2 (by rfl) ⟨2143401, by rfl⟩ : syracuseStep 5715737 = 4286803) B4286803
theorem B23517053 : Blo 1693547 23517053 := bstep (se 3 (by rfl) ⟨4409447, by rfl⟩ : syracuseStep 23517053 = 8818895) B8818895
theorem B1693567 : Blo 1693547 1693567 := bstep (se 1 (by rfl) ⟨1270175, by rfl⟩ : syracuseStep 1693567 = 2540351) B2540351
theorem B3618751 : Blo 1693547 3618751 := bstep (se 1 (by rfl) ⟨2714063, by rfl⟩ : syracuseStep 3618751 = 5428127) B5428127
theorem B1693723 : Blo 1693547 1693723 := bstep (se 1 (by rfl) ⟨1270292, by rfl⟩ : syracuseStep 1693723 = 2540585) B2540585
theorem B1693743 : Blo 1693547 1693743 := bstep (se 1 (by rfl) ⟨1270307, by rfl⟩ : syracuseStep 1693743 = 2540615) B2540615
theorem B3217639 : Blo 1693547 3217639 := bstep (se 1 (by rfl) ⟨2413229, by rfl⟩ : syracuseStep 3217639 = 4826459) B4826459
theorem B1694175 : Blo 1693547 1694175 := bstep (se 1 (by rfl) ⟨1270631, by rfl⟩ : syracuseStep 1694175 = 2541263) B2541263
theorem B13736479 : Blo 1693547 13736479 := bstep (se 1 (by rfl) ⟨10302359, by rfl⟩ : syracuseStep 13736479 = 20604719) B20604719
theorem B1694311 : Blo 1693547 1694311 := bstep (se 1 (by rfl) ⟨1270733, by rfl⟩ : syracuseStep 1694311 = 2541467) B2541467
theorem B1694335 : Blo 1693547 1694335 := bstep (se 1 (by rfl) ⟨1270751, by rfl⟩ : syracuseStep 1694335 = 2541503) B2541503
theorem B58710743 : Blo 1693547 58710743 := bstep (se 1 (by rfl) ⟨44033057, by rfl⟩ : syracuseStep 58710743 = 88066115) B88066115
theorem B23501735 : Blo 1693547 23501735 := bstep (se 1 (by rfl) ⟨17626301, by rfl⟩ : syracuseStep 23501735 = 35252603) B35252603
theorem B1694655 : Blo 1693547 1694655 := bstep (se 1 (by rfl) ⟨1270991, by rfl⟩ : syracuseStep 1694655 = 2541983) B2541983
theorem B8575955 : Blo 1693547 8575955 := bstep (se 1 (by rfl) ⟨6431966, by rfl⟩ : syracuseStep 8575955 = 12863933) B12863933
theorem B27491309 : Blo 1693547 27491309 := bstep (se 3 (by rfl) ⟨5154620, by rfl⟩ : syracuseStep 27491309 = 10309241) B10309241
theorem B6872147 : Blo 1693547 6872147 := bstep (se 1 (by rfl) ⟨5154110, by rfl⟩ : syracuseStep 6872147 = 10308221) B10308221
theorem B1695023 : Blo 1693547 1695023 := bstep (se 1 (by rfl) ⟨1271267, by rfl⟩ : syracuseStep 1695023 = 2542535) B2542535
theorem B15678875 : Blo 1693547 15678875 := bstep (se 1 (by rfl) ⟨11759156, by rfl⟩ : syracuseStep 15678875 = 23518313) B23518313
theorem B1695199 : Blo 1693547 1695199 := bstep (se 1 (by rfl) ⟨1271399, by rfl⟩ : syracuseStep 1695199 = 2542799) B2542799
theorem B1695215 : Blo 1693547 1695215 := bstep (se 1 (by rfl) ⟨1271411, by rfl⟩ : syracuseStep 1695215 = 2542823) B2542823
theorem B16285495 : Blo 1693547 16285495 := bstep (se 1 (by rfl) ⟨12214121, by rfl⟩ : syracuseStep 16285495 = 24428243) B24428243
theorem B7831511 : Blo 1693547 7831511 := bstep (se 1 (by rfl) ⟨5873633, by rfl⟩ : syracuseStep 7831511 = 11747267) B11747267
theorem B5152747 : Blo 1693547 5152747 := bstep (se 1 (by rfl) ⟨3864560, by rfl⟩ : syracuseStep 5152747 = 7729121) B7729121
theorem B4825115 : Blo 1693547 4825115 := bstep (se 1 (by rfl) ⟨3618836, by rfl⟩ : syracuseStep 4825115 = 7237673) B7237673
theorem B19292255 : Blo 1693547 19292255 := bstep (se 1 (by rfl) ⟨14469191, by rfl⟩ : syracuseStep 19292255 = 28938383) B28938383
theorem B8815229 : Blo 1693547 8815229 := bstep (se 3 (by rfl) ⟨1652855, by rfl⟩ : syracuseStep 8815229 = 3305711) B3305711
theorem B2540495 : Blo 1693547 2540495 := bstep (se 1 (by rfl) ⟨1905371, by rfl⟩ : syracuseStep 2540495 = 3810743) B3810743
theorem B3810491 : Blo 1693547 3810491 := bstep (se 1 (by rfl) ⟨2857868, by rfl⟩ : syracuseStep 3810491 = 5715737) B5715737
theorem B30934295 : Blo 1693547 30934295 := bstep (se 1 (by rfl) ⟨23200721, by rfl⟩ : syracuseStep 30934295 = 46401443) B46401443
theorem B2540855 : Blo 1693547 2540855 := bstep (se 1 (by rfl) ⟨1905641, by rfl⟩ : syracuseStep 2540855 = 3811283) B3811283
theorem B22021895 : Blo 1693547 22021895 := bstep (se 1 (by rfl) ⟨16516421, by rfl⟩ : syracuseStep 22021895 = 33032843) B33032843
theorem B18327539 : Blo 1693547 18327539 := bstep (se 1 (by rfl) ⟨13745654, by rfl⟩ : syracuseStep 18327539 = 27491309) B27491309
theorem B4581431 : Blo 1693547 4581431 := bstep (se 1 (by rfl) ⟨3436073, by rfl⟩ : syracuseStep 4581431 = 6872147) B6872147
theorem B2541659 : Blo 1693547 2541659 := bstep (se 1 (by rfl) ⟨1906244, by rfl⟩ : syracuseStep 2541659 = 3812489) B3812489
theorem B2541743 : Blo 1693547 2541743 := bstep (se 1 (by rfl) ⟨1906307, by rfl⟩ : syracuseStep 2541743 = 3812615) B3812615
theorem B2542127 : Blo 1693547 2542127 := bstep (se 1 (by rfl) ⟨1906595, by rfl⟩ : syracuseStep 2542127 = 3813191) B3813191
theorem B5221007 : Blo 1693547 5221007 := bstep (se 1 (by rfl) ⟨3915755, by rfl⟩ : syracuseStep 5221007 = 7831511) B7831511
theorem B8252383 : Blo 1693547 8252383 := bstep (se 1 (by rfl) ⟨6189287, by rfl⟩ : syracuseStep 8252383 = 12378575) B12378575
theorem B4828157 : Blo 1693547 4828157 := bstep (se 3 (by rfl) ⟨905279, by rfl⟩ : syracuseStep 4828157 = 1810559) B1810559
theorem B2575595 : Blo 1693547 2575595 := bstep (se 1 (by rfl) ⟨1931696, by rfl⟩ : syracuseStep 2575595 = 3863393) B3863393
theorem B2542895 : Blo 1693547 2542895 := bstep (se 1 (by rfl) ⟨1907171, by rfl⟩ : syracuseStep 2542895 = 3814343) B3814343
theorem B72437327 : Blo 1693547 72437327 := bstep (se 1 (by rfl) ⟨54327995, by rfl⟩ : syracuseStep 72437327 = 108655991) B108655991
theorem B18329179 : Blo 1693547 18329179 := bstep (se 1 (by rfl) ⟨13746884, by rfl⟩ : syracuseStep 18329179 = 27493769) B27493769
theorem B78229259 : Blo 1693547 78229259 := bstep (se 1 (by rfl) ⟨58671944, by rfl⟩ : syracuseStep 78229259 = 117343889) B117343889
theorem B10301215 : Blo 1693547 10301215 := bstep (se 1 (by rfl) ⟨7725911, by rfl⟩ : syracuseStep 10301215 = 15451823) B15451823
theorem B3813353 : Blo 1693547 3813353 := bstep (se 2 (by rfl) ⟨1430007, by rfl⟩ : syracuseStep 3813353 = 2860015) B2860015
theorem B3813371 : Blo 1693547 3813371 := bstep (se 1 (by rfl) ⟨2860028, by rfl⟩ : syracuseStep 3813371 = 5720057) B5720057
theorem B74314199 : Blo 1693547 74314199 := bstep (se 1 (by rfl) ⟨55735649, by rfl⟩ : syracuseStep 74314199 = 111471299) B111471299
theorem B15667823 : Blo 1693547 15667823 := bstep (se 1 (by rfl) ⟨11750867, by rfl⟩ : syracuseStep 15667823 = 23501735) B23501735
theorem B19305377 : Blo 1693547 19305377 := bstep (se 2 (by rfl) ⟨7239516, by rfl⟩ : syracuseStep 19305377 = 14479033) B14479033
theorem B18330563 : Blo 1693547 18330563 := bstep (se 1 (by rfl) ⟨13747922, by rfl⟩ : syracuseStep 18330563 = 27495845) B27495845
theorem B21713993 : Blo 1693547 21713993 := bstep (se 2 (by rfl) ⟨8142747, by rfl⟩ : syracuseStep 21713993 = 16285495) B16285495
theorem B6870329 : Blo 1693547 6870329 := bstep (se 2 (by rfl) ⟨2576373, by rfl⟩ : syracuseStep 6870329 = 5152747) B5152747
theorem B9655787 : Blo 1693547 9655787 := bstep (se 1 (by rfl) ⟨7241840, by rfl⟩ : syracuseStep 9655787 = 14483681) B14483681
theorem B4290185 : Blo 1693547 4290185 := bstep (se 2 (by rfl) ⟨1608819, by rfl⟩ : syracuseStep 4290185 = 3217639) B3217639
theorem B2143999 : Blo 1693547 2143999 := bstep (se 1 (by rfl) ⟨1607999, by rfl⟩ : syracuseStep 2143999 = 3215999) B3215999
theorem B1693631 : Blo 1693547 1693631 := bstep (se 1 (by rfl) ⟨1270223, by rfl⟩ : syracuseStep 1693631 = 2540447) B2540447
theorem B18315305 : Blo 1693547 18315305 := bstep (se 2 (by rfl) ⟨6868239, by rfl⟩ : syracuseStep 18315305 = 13736479) B13736479
theorem B1693787 : Blo 1693547 1693787 := bstep (se 1 (by rfl) ⟨1270340, by rfl⟩ : syracuseStep 1693787 = 2540681) B2540681
theorem B8583407 : Blo 1693547 8583407 := bstep (se 1 (by rfl) ⟨6437555, by rfl⟩ : syracuseStep 8583407 = 12875111) B12875111
theorem B1694055 : Blo 1693547 1694055 := bstep (se 1 (by rfl) ⟨1270541, by rfl⟩ : syracuseStep 1694055 = 2541083) B2541083
theorem B5429729 : Blo 1693547 5429729 := bstep (se 2 (by rfl) ⟨2036148, by rfl⟩ : syracuseStep 5429729 = 4072297) B4072297
theorem B15678035 : Blo 1693547 15678035 := bstep (se 1 (by rfl) ⟨11758526, by rfl⟩ : syracuseStep 15678035 = 23517053) B23517053
theorem B1694447 : Blo 1693547 1694447 := bstep (se 1 (by rfl) ⟨1270835, by rfl⟩ : syracuseStep 1694447 = 2541671) B2541671
theorem B39140495 : Blo 1693547 39140495 := bstep (se 1 (by rfl) ⟨29355371, by rfl⟩ : syracuseStep 39140495 = 58710743) B58710743
theorem B5717303 : Blo 1693547 5717303 := bstep (se 1 (by rfl) ⟨4287977, by rfl⟩ : syracuseStep 5717303 = 8575955) B8575955
theorem B2858395 : Blo 1693547 2858395 := bstep (se 1 (by rfl) ⟨2143796, by rfl⟩ : syracuseStep 2858395 = 4287593) B4287593
theorem B10452583 : Blo 1693547 10452583 := bstep (se 1 (by rfl) ⟨7839437, by rfl⟩ : syracuseStep 10452583 = 15678875) B15678875
theorem B5430959 : Blo 1693547 5430959 := bstep (se 1 (by rfl) ⟨4073219, by rfl⟩ : syracuseStep 5430959 = 8146439) B8146439
theorem B4825001 : Blo 1693547 4825001 := bstep (se 2 (by rfl) ⟨1809375, by rfl⟩ : syracuseStep 4825001 = 3618751) B3618751
theorem B12861503 : Blo 1693547 12861503 := bstep (se 1 (by rfl) ⟨9646127, by rfl⟩ : syracuseStep 12861503 = 19292255) B19292255
theorem B10445215 : Blo 1693547 10445215 := bstep (se 1 (by rfl) ⟨7833911, by rfl⟩ : syracuseStep 10445215 = 15667823) B15667823
theorem B55747109 : Blo 1693547 55747109 := bstep (se 4 (by rfl) ⟨5226291, by rfl⟩ : syracuseStep 55747109 = 10452583) B10452583
theorem B12870251 : Blo 1693547 12870251 := bstep (se 1 (by rfl) ⟨9652688, by rfl⟩ : syracuseStep 12870251 = 19305377) B19305377
theorem B14475995 : Blo 1693547 14475995 := bstep (se 1 (by rfl) ⟨10856996, by rfl⟩ : syracuseStep 14475995 = 21713993) B21713993
theorem B2540327 : Blo 1693547 2540327 := bstep (se 1 (by rfl) ⟨1905245, by rfl⟩ : syracuseStep 2540327 = 3810491) B3810491
theorem B4580219 : Blo 1693547 4580219 := bstep (se 1 (by rfl) ⟨3435164, by rfl⟩ : syracuseStep 4580219 = 6870329) B6870329
theorem B2860123 : Blo 1693547 2860123 := bstep (se 1 (by rfl) ⟨2145092, by rfl⟩ : syracuseStep 2860123 = 4290185) B4290185
theorem B14681263 : Blo 1693547 14681263 := bstep (se 1 (by rfl) ⟨11010947, by rfl⟩ : syracuseStep 14681263 = 22021895) B22021895
theorem B11003177 : Blo 1693547 11003177 := bstep (se 2 (by rfl) ⟨4126191, by rfl⟩ : syracuseStep 11003177 = 8252383) B8252383
theorem B3811193 : Blo 1693547 3811193 := bstep (se 2 (by rfl) ⟨1429197, by rfl⟩ : syracuseStep 3811193 = 2858395) B2858395
theorem B26093663 : Blo 1693547 26093663 := bstep (se 1 (by rfl) ⟨19570247, by rfl⟩ : syracuseStep 26093663 = 39140495) B39140495
theorem B24438905 : Blo 1693547 24438905 := bstep (se 2 (by rfl) ⟨9164589, by rfl⟩ : syracuseStep 24438905 = 18329179) B18329179
theorem B3811535 : Blo 1693547 3811535 := bstep (se 1 (by rfl) ⟨2858651, by rfl⟩ : syracuseStep 3811535 = 5717303) B5717303
theorem B52152839 : Blo 1693547 52152839 := bstep (se 1 (by rfl) ⟨39114629, by rfl⟩ : syracuseStep 52152839 = 78229259) B78229259
theorem B2542235 : Blo 1693547 2542235 := bstep (se 1 (by rfl) ⟨1906676, by rfl⟩ : syracuseStep 2542235 = 3813353) B3813353
theorem B2542247 : Blo 1693547 2542247 := bstep (se 1 (by rfl) ⟨1906685, by rfl⟩ : syracuseStep 2542247 = 3813371) B3813371
theorem B5876819 : Blo 1693547 5876819 := bstep (se 1 (by rfl) ⟨4407614, by rfl⟩ : syracuseStep 5876819 = 8815229) B8815229
theorem B6868253 : Blo 1693547 6868253 := bstep (se 3 (by rfl) ⟨1287797, by rfl⟩ : syracuseStep 6868253 = 2575595) B2575595
theorem B20622863 : Blo 1693547 20622863 := bstep (se 1 (by rfl) ⟨15467147, by rfl⟩ : syracuseStep 20622863 = 30934295) B30934295
theorem B12218359 : Blo 1693547 12218359 := bstep (se 1 (by rfl) ⟨9163769, by rfl⟩ : syracuseStep 12218359 = 18327539) B18327539
theorem B12210203 : Blo 1693547 12210203 := bstep (se 1 (by rfl) ⟨9157652, by rfl⟩ : syracuseStep 12210203 = 18315305) B18315305
theorem B5722271 : Blo 1693547 5722271 := bstep (se 1 (by rfl) ⟨4291703, by rfl⟩ : syracuseStep 5722271 = 8583407) B8583407
theorem B13734953 : Blo 1693547 13734953 := bstep (se 2 (by rfl) ⟨5150607, by rfl⟩ : syracuseStep 13734953 = 10301215) B10301215
theorem B3216667 : Blo 1693547 3216667 := bstep (se 1 (by rfl) ⟨2412500, by rfl⟩ : syracuseStep 3216667 = 4825001) B4825001
theorem B3216743 : Blo 1693547 3216743 := bstep (se 1 (by rfl) ⟨2412557, by rfl⟩ : syracuseStep 3216743 = 4825115) B4825115
theorem B49542799 : Blo 1693547 49542799 := bstep (se 1 (by rfl) ⟨37157099, by rfl⟩ : syracuseStep 49542799 = 74314199) B74314199
theorem B1693663 : Blo 1693547 1693663 := bstep (se 1 (by rfl) ⟨1270247, by rfl⟩ : syracuseStep 1693663 = 2540495) B2540495
theorem B1693903 : Blo 1693547 1693903 := bstep (se 1 (by rfl) ⟨1270427, by rfl⟩ : syracuseStep 1693903 = 2540855) B2540855
theorem B6437191 : Blo 1693547 6437191 := bstep (se 1 (by rfl) ⟨4827893, by rfl⟩ : syracuseStep 6437191 = 9655787) B9655787
theorem B3054287 : Blo 1693547 3054287 := bstep (se 1 (by rfl) ⟨2290715, by rfl⟩ : syracuseStep 3054287 = 4581431) B4581431
theorem B1694439 : Blo 1693547 1694439 := bstep (se 1 (by rfl) ⟨1270829, by rfl⟩ : syracuseStep 1694439 = 2541659) B2541659
theorem B1694495 : Blo 1693547 1694495 := bstep (se 1 (by rfl) ⟨1270871, by rfl⟩ : syracuseStep 1694495 = 2541743) B2541743
theorem B3619819 : Blo 1693547 3619819 := bstep (se 1 (by rfl) ⟨2714864, by rfl⟩ : syracuseStep 3619819 = 5429729) B5429729
theorem B1694751 : Blo 1693547 1694751 := bstep (se 1 (by rfl) ⟨1271063, by rfl⟩ : syracuseStep 1694751 = 2542127) B2542127
theorem B10452023 : Blo 1693547 10452023 := bstep (se 1 (by rfl) ⟨7839017, by rfl⟩ : syracuseStep 10452023 = 15678035) B15678035
theorem B3480671 : Blo 1693547 3480671 := bstep (se 1 (by rfl) ⟨2610503, by rfl⟩ : syracuseStep 3480671 = 5221007) B5221007
theorem B3218771 : Blo 1693547 3218771 := bstep (se 1 (by rfl) ⟨2414078, by rfl⟩ : syracuseStep 3218771 = 4828157) B4828157
theorem B1695263 : Blo 1693547 1695263 := bstep (se 1 (by rfl) ⟨1271447, by rfl⟩ : syracuseStep 1695263 = 2542895) B2542895
theorem B2858665 : Blo 1693547 2858665 := bstep (se 2 (by rfl) ⟨1071999, by rfl⟩ : syracuseStep 2858665 = 2143999) B2143999
theorem B48291551 : Blo 1693547 48291551 := bstep (se 1 (by rfl) ⟨36218663, by rfl⟩ : syracuseStep 48291551 = 72437327) B72437327
theorem B3620639 : Blo 1693547 3620639 := bstep (se 1 (by rfl) ⟨2715479, by rfl⟩ : syracuseStep 3620639 = 5430959) B5430959
theorem B48881501 : Blo 1693547 48881501 := bstep (se 3 (by rfl) ⟨9165281, by rfl⟩ : syracuseStep 48881501 = 18330563) B18330563
theorem B9281789 : Blo 1693547 9281789 := bstep (se 3 (by rfl) ⟨1740335, by rfl⟩ : syracuseStep 9281789 = 3480671) B3480671
theorem B9650663 : Blo 1693547 9650663 := bstep (se 1 (by rfl) ⟨7237997, by rfl⟩ : syracuseStep 9650663 = 14475995) B14475995
theorem B13926953 : Blo 1693547 13926953 := bstep (se 2 (by rfl) ⟨5222607, by rfl⟩ : syracuseStep 13926953 = 10445215) B10445215
theorem B2540795 : Blo 1693547 2540795 := bstep (se 1 (by rfl) ⟨1905596, by rfl⟩ : syracuseStep 2540795 = 3811193) B3811193
theorem B4826425 : Blo 1693547 4826425 := bstep (se 2 (by rfl) ⟨1809909, by rfl⟩ : syracuseStep 4826425 = 3619819) B3619819
theorem B54994301 : Blo 1693547 54994301 := bstep (se 3 (by rfl) ⟨10311431, by rfl⟩ : syracuseStep 54994301 = 20622863) B20622863
theorem B2541023 : Blo 1693547 2541023 := bstep (se 1 (by rfl) ⟨1905767, by rfl⟩ : syracuseStep 2541023 = 3811535) B3811535
theorem B34768559 : Blo 1693547 34768559 := bstep (se 1 (by rfl) ⟨26076419, by rfl⟩ : syracuseStep 34768559 = 52152839) B52152839
theorem B8144765 : Blo 1693547 8144765 := bstep (se 3 (by rfl) ⟨1527143, by rfl⟩ : syracuseStep 8144765 = 3054287) B3054287
theorem B3917879 : Blo 1693547 3917879 := bstep (se 1 (by rfl) ⟨2938409, by rfl⟩ : syracuseStep 3917879 = 5876819) B5876819
theorem B3811553 : Blo 1693547 3811553 := bstep (se 2 (by rfl) ⟨1429332, by rfl⟩ : syracuseStep 3811553 = 2858665) B2858665
theorem B8580167 : Blo 1693547 8580167 := bstep (se 1 (by rfl) ⟨6435125, by rfl⟩ : syracuseStep 8580167 = 12870251) B12870251
theorem B7335451 : Blo 1693547 7335451 := bstep (se 1 (by rfl) ⟨5501588, by rfl⟩ : syracuseStep 7335451 = 11003177) B11003177
theorem B17395775 : Blo 1693547 17395775 := bstep (se 1 (by rfl) ⟨13046831, by rfl⟩ : syracuseStep 17395775 = 26093663) B26093663
theorem B3813497 : Blo 1693547 3813497 := bstep (se 2 (by rfl) ⟨1430061, by rfl⟩ : syracuseStep 3813497 = 2860123) B2860123
theorem B19575017 : Blo 1693547 19575017 := bstep (se 2 (by rfl) ⟨7340631, by rfl⟩ : syracuseStep 19575017 = 14681263) B14681263
theorem B4288889 : Blo 1693547 4288889 := bstep (se 2 (by rfl) ⟨1608333, by rfl⟩ : syracuseStep 4288889 = 3216667) B3216667
theorem B6968015 : Blo 1693547 6968015 := bstep (se 1 (by rfl) ⟨5226011, by rfl⟩ : syracuseStep 6968015 = 10452023) B10452023
theorem B9655037 : Blo 1693547 9655037 := bstep (se 3 (by rfl) ⟨1810319, by rfl⟩ : syracuseStep 9655037 = 3620639) B3620639
theorem B66057065 : Blo 1693547 66057065 := bstep (se 2 (by rfl) ⟨24771399, by rfl⟩ : syracuseStep 66057065 = 49542799) B49542799
theorem B16291145 : Blo 1693547 16291145 := bstep (se 2 (by rfl) ⟨6109179, by rfl⟩ : syracuseStep 16291145 = 12218359) B12218359
theorem B8140135 : Blo 1693547 8140135 := bstep (se 1 (by rfl) ⟨6105101, by rfl⟩ : syracuseStep 8140135 = 12210203) B12210203
theorem B8574335 : Blo 1693547 8574335 := bstep (se 1 (by rfl) ⟨6430751, by rfl⟩ : syracuseStep 8574335 = 12861503) B12861503
theorem B3814847 : Blo 1693547 3814847 := bstep (se 1 (by rfl) ⟨2861135, by rfl⟩ : syracuseStep 3814847 = 5722271) B5722271
theorem B37164739 : Blo 1693547 37164739 := bstep (se 1 (by rfl) ⟨27873554, by rfl⟩ : syracuseStep 37164739 = 55747109) B55747109
theorem B8582921 : Blo 1693547 8582921 := bstep (se 2 (by rfl) ⟨3218595, by rfl⟩ : syracuseStep 8582921 = 6437191) B6437191
theorem B1693551 : Blo 1693547 1693551 := bstep (se 1 (by rfl) ⟨1270163, by rfl⟩ : syracuseStep 1693551 = 2540327) B2540327
theorem B9156635 : Blo 1693547 9156635 := bstep (se 1 (by rfl) ⟨6867476, by rfl⟩ : syracuseStep 9156635 = 13734953) B13734953
theorem B18315341 : Blo 1693547 18315341 := bstep (se 3 (by rfl) ⟨3434126, by rfl⟩ : syracuseStep 18315341 = 6868253) B6868253
theorem B2144495 : Blo 1693547 2144495 := bstep (se 1 (by rfl) ⟨1608371, by rfl⟩ : syracuseStep 2144495 = 3216743) B3216743
theorem B16292603 : Blo 1693547 16292603 := bstep (se 1 (by rfl) ⟨12219452, by rfl⟩ : syracuseStep 16292603 = 24438905) B24438905
theorem B1694823 : Blo 1693547 1694823 := bstep (se 1 (by rfl) ⟨1271117, by rfl⟩ : syracuseStep 1694823 = 2542235) B2542235
theorem B1694831 : Blo 1693547 1694831 := bstep (se 1 (by rfl) ⟨1271123, by rfl⟩ : syracuseStep 1694831 = 2542247) B2542247
theorem B2145847 : Blo 1693547 2145847 := bstep (se 1 (by rfl) ⟨1609385, by rfl⟩ : syracuseStep 2145847 = 3218771) B3218771
theorem B12213917 : Blo 1693547 12213917 := bstep (se 3 (by rfl) ⟨2290109, by rfl⟩ : syracuseStep 12213917 = 4580219) B4580219
theorem B32194367 : Blo 1693547 32194367 := bstep (se 1 (by rfl) ⟨24145775, by rfl⟩ : syracuseStep 32194367 = 48291551) B48291551
theorem B32587667 : Blo 1693547 32587667 := bstep (se 1 (by rfl) ⟨24440750, by rfl⟩ : syracuseStep 32587667 = 48881501) B48881501
theorem B13050011 : Blo 1693547 13050011 := bstep (se 1 (by rfl) ⟨9787508, by rfl⟩ : syracuseStep 13050011 = 19575017) B19575017
theorem B2859259 : Blo 1693547 2859259 := bstep (se 1 (by rfl) ⟨2144444, by rfl⟩ : syracuseStep 2859259 = 4288889) B4288889
theorem B4645343 : Blo 1693547 4645343 := bstep (se 1 (by rfl) ⟨3484007, by rfl⟩ : syracuseStep 4645343 = 6968015) B6968015
theorem B5718653 : Blo 1693547 5718653 := bstep (se 3 (by rfl) ⟨1072247, by rfl⟩ : syracuseStep 5718653 = 2144495) B2144495
theorem B6104423 : Blo 1693547 6104423 := bstep (se 1 (by rfl) ⟨4578317, by rfl⟩ : syracuseStep 6104423 = 9156635) B9156635
theorem B2541035 : Blo 1693547 2541035 := bstep (se 1 (by rfl) ⟨1905776, by rfl⟩ : syracuseStep 2541035 = 3811553) B3811553
theorem B5720111 : Blo 1693547 5720111 := bstep (se 1 (by rfl) ⟨4290083, by rfl⟩ : syracuseStep 5720111 = 8580167) B8580167
theorem B2861129 : Blo 1693547 2861129 := bstep (se 2 (by rfl) ⟨1072923, by rfl⟩ : syracuseStep 2861129 = 2145847) B2145847
theorem B2542331 : Blo 1693547 2542331 := bstep (se 1 (by rfl) ⟨1906748, by rfl⟩ : syracuseStep 2542331 = 3813497) B3813497
theorem B6187859 : Blo 1693547 6187859 := bstep (se 1 (by rfl) ⟨4640894, by rfl⟩ : syracuseStep 6187859 = 9281789) B9281789
theorem B6433775 : Blo 1693547 6433775 := bstep (se 1 (by rfl) ⟨4825331, by rfl⟩ : syracuseStep 6433775 = 9650663) B9650663
theorem B9284635 : Blo 1693547 9284635 := bstep (se 1 (by rfl) ⟨6963476, by rfl⟩ : syracuseStep 9284635 = 13926953) B13926953
theorem B36662867 : Blo 1693547 36662867 := bstep (se 1 (by rfl) ⟨27497150, by rfl⟩ : syracuseStep 36662867 = 54994301) B54994301
theorem B2543231 : Blo 1693547 2543231 := bstep (se 1 (by rfl) ⟨1907423, by rfl⟩ : syracuseStep 2543231 = 3814847) B3814847
theorem B5721947 : Blo 1693547 5721947 := bstep (se 1 (by rfl) ⟨4291460, by rfl⟩ : syracuseStep 5721947 = 8582921) B8582921
theorem B12210227 : Blo 1693547 12210227 := bstep (se 1 (by rfl) ⟨9157670, by rfl⟩ : syracuseStep 12210227 = 18315341) B18315341
theorem B6435233 : Blo 1693547 6435233 := bstep (se 2 (by rfl) ⟨2413212, by rfl⟩ : syracuseStep 6435233 = 4826425) B4826425
theorem B43446941 : Blo 1693547 43446941 := bstep (se 3 (by rfl) ⟨8146301, by rfl⟩ : syracuseStep 43446941 = 16292603) B16292603
theorem B11597183 : Blo 1693547 11597183 := bstep (se 1 (by rfl) ⟨8697887, by rfl⟩ : syracuseStep 11597183 = 17395775) B17395775
theorem B6436691 : Blo 1693547 6436691 := bstep (se 1 (by rfl) ⟨4827518, by rfl⟩ : syracuseStep 6436691 = 9655037) B9655037
theorem B44038043 : Blo 1693547 44038043 := bstep (se 1 (by rfl) ⟨33028532, by rfl⟩ : syracuseStep 44038043 = 66057065) B66057065
theorem B1693863 : Blo 1693547 1693863 := bstep (se 1 (by rfl) ⟨1270397, by rfl⟩ : syracuseStep 1693863 = 2540795) B2540795
theorem B10860763 : Blo 1693547 10860763 := bstep (se 1 (by rfl) ⟨8145572, by rfl⟩ : syracuseStep 10860763 = 16291145) B16291145
theorem B5716223 : Blo 1693547 5716223 := bstep (se 1 (by rfl) ⟨4287167, by rfl⟩ : syracuseStep 5716223 = 8574335) B8574335
theorem B1694015 : Blo 1693547 1694015 := bstep (se 1 (by rfl) ⟨1270511, by rfl⟩ : syracuseStep 1694015 = 2541023) B2541023
theorem B5429843 : Blo 1693547 5429843 := bstep (se 1 (by rfl) ⟨4072382, by rfl⟩ : syracuseStep 5429843 = 8144765) B8144765
theorem B2611919 : Blo 1693547 2611919 := bstep (se 1 (by rfl) ⟨1958939, by rfl⟩ : syracuseStep 2611919 = 3917879) B3917879
theorem B92716157 : Blo 1693547 92716157 := bstep (se 3 (by rfl) ⟨17384279, by rfl⟩ : syracuseStep 92716157 = 34768559) B34768559
theorem B10853513 : Blo 1693547 10853513 := bstep (se 2 (by rfl) ⟨4070067, by rfl⟩ : syracuseStep 10853513 = 8140135) B8140135
theorem B9780601 : Blo 1693547 9780601 := bstep (se 2 (by rfl) ⟨3667725, by rfl⟩ : syracuseStep 9780601 = 7335451) B7335451
theorem B49552985 : Blo 1693547 49552985 := bstep (se 2 (by rfl) ⟨18582369, by rfl⟩ : syracuseStep 49552985 = 37164739) B37164739
theorem B8142611 : Blo 1693547 8142611 := bstep (se 1 (by rfl) ⟨6106958, by rfl⟩ : syracuseStep 8142611 = 12213917) B12213917
theorem B21462911 : Blo 1693547 21462911 := bstep (se 1 (by rfl) ⟨16097183, by rfl⟩ : syracuseStep 21462911 = 32194367) B32194367
theorem B21725111 : Blo 1693547 21725111 := bstep (se 1 (by rfl) ⟨16293833, by rfl⟩ : syracuseStep 21725111 = 32587667) B32587667
theorem B8700007 : Blo 1693547 8700007 := bstep (se 1 (by rfl) ⟨6525005, by rfl⟩ : syracuseStep 8700007 = 13050011) B13050011
theorem B3096895 : Blo 1693547 3096895 := bstep (se 1 (by rfl) ⟨2322671, by rfl⟩ : syracuseStep 3096895 = 4645343) B4645343
theorem B3810815 : Blo 1693547 3810815 := bstep (se 1 (by rfl) ⟨2858111, by rfl⟩ : syracuseStep 3810815 = 5716223) B5716223
theorem B61810771 : Blo 1693547 61810771 := bstep (se 1 (by rfl) ⟨46358078, by rfl⟩ : syracuseStep 61810771 = 92716157) B92716157
theorem B7235675 : Blo 1693547 7235675 := bstep (se 1 (by rfl) ⟨5426756, by rfl⟩ : syracuseStep 7235675 = 10853513) B10853513
theorem B3812345 : Blo 1693547 3812345 := bstep (se 2 (by rfl) ⟨1429629, by rfl⟩ : syracuseStep 3812345 = 2859259) B2859259
theorem B3812435 : Blo 1693547 3812435 := bstep (se 1 (by rfl) ⟨2859326, by rfl⟩ : syracuseStep 3812435 = 5718653) B5718653
theorem B3813407 : Blo 1693547 3813407 := bstep (se 1 (by rfl) ⟨2860055, by rfl⟩ : syracuseStep 3813407 = 5720111) B5720111
theorem B1741279 : Blo 1693547 1741279 := bstep (se 1 (by rfl) ⟨1305959, by rfl⟩ : syracuseStep 1741279 = 2611919) B2611919
theorem B4125239 : Blo 1693547 4125239 := bstep (se 1 (by rfl) ⟨3093929, by rfl⟩ : syracuseStep 4125239 = 6187859) B6187859
theorem B4289183 : Blo 1693547 4289183 := bstep (se 1 (by rfl) ⟨3216887, by rfl⟩ : syracuseStep 4289183 = 6433775) B6433775
theorem B21713629 : Blo 1693547 21713629 := bstep (se 3 (by rfl) ⟨4071305, by rfl⟩ : syracuseStep 21713629 = 8142611) B8142611
theorem B24441911 : Blo 1693547 24441911 := bstep (se 1 (by rfl) ⟨18331433, by rfl⟩ : syracuseStep 24441911 = 36662867) B36662867
theorem B33035323 : Blo 1693547 33035323 := bstep (se 1 (by rfl) ⟨24776492, by rfl⟩ : syracuseStep 33035323 = 49552985) B49552985
theorem B3814631 : Blo 1693547 3814631 := bstep (se 1 (by rfl) ⟨2860973, by rfl⟩ : syracuseStep 3814631 = 5721947) B5721947
theorem B14308607 : Blo 1693547 14308607 := bstep (se 1 (by rfl) ⟨10731455, by rfl⟩ : syracuseStep 14308607 = 21462911) B21462911
theorem B8140151 : Blo 1693547 8140151 := bstep (se 1 (by rfl) ⟨6105113, by rfl⟩ : syracuseStep 8140151 = 12210227) B12210227
theorem B49518053 : Blo 1693547 49518053 := bstep (se 4 (by rfl) ⟨4642317, by rfl⟩ : syracuseStep 49518053 = 9284635) B9284635
theorem B4290155 : Blo 1693547 4290155 := bstep (se 1 (by rfl) ⟨3217616, by rfl⟩ : syracuseStep 4290155 = 6435233) B6435233
theorem B14481017 : Blo 1693547 14481017 := bstep (se 2 (by rfl) ⟨5430381, by rfl⟩ : syracuseStep 14481017 = 10860763) B10860763
theorem B28964627 : Blo 1693547 28964627 := bstep (se 1 (by rfl) ⟨21723470, by rfl⟩ : syracuseStep 28964627 = 43446941) B43446941
theorem B4069615 : Blo 1693547 4069615 := bstep (se 1 (by rfl) ⟨3052211, by rfl⟩ : syracuseStep 4069615 = 6104423) B6104423
theorem B7731455 : Blo 1693547 7731455 := bstep (se 1 (by rfl) ⟨5798591, by rfl⟩ : syracuseStep 7731455 = 11597183) B11597183
theorem B1694023 : Blo 1693547 1694023 := bstep (se 1 (by rfl) ⟨1270517, by rfl⟩ : syracuseStep 1694023 = 2541035) B2541035
theorem B4291127 : Blo 1693547 4291127 := bstep (se 1 (by rfl) ⟨3218345, by rfl⟩ : syracuseStep 4291127 = 6436691) B6436691
theorem B29358695 : Blo 1693547 29358695 := bstep (se 1 (by rfl) ⟨22019021, by rfl⟩ : syracuseStep 29358695 = 44038043) B44038043
theorem B1907419 : Blo 1693547 1907419 := bstep (se 1 (by rfl) ⟨1430564, by rfl⟩ : syracuseStep 1907419 = 2861129) B2861129
theorem B3619895 : Blo 1693547 3619895 := bstep (se 1 (by rfl) ⟨2714921, by rfl⟩ : syracuseStep 3619895 = 5429843) B5429843
theorem B13040801 : Blo 1693547 13040801 := bstep (se 2 (by rfl) ⟨4890300, by rfl⟩ : syracuseStep 13040801 = 9780601) B9780601
theorem B1694887 : Blo 1693547 1694887 := bstep (se 1 (by rfl) ⟨1271165, by rfl⟩ : syracuseStep 1694887 = 2542331) B2542331
theorem B1695487 : Blo 1693547 1695487 := bstep (se 1 (by rfl) ⟨1271615, by rfl⟩ : syracuseStep 1695487 = 2543231) B2543231
theorem B14483407 : Blo 1693547 14483407 := bstep (se 1 (by rfl) ⟨10862555, by rfl⟩ : syracuseStep 14483407 = 21725111) B21725111
theorem B11600009 : Blo 1693547 11600009 := bstep (se 2 (by rfl) ⟨4350003, by rfl⟩ : syracuseStep 11600009 = 8700007) B8700007
theorem B4129193 : Blo 1693547 4129193 := bstep (se 2 (by rfl) ⟨1548447, by rfl⟩ : syracuseStep 4129193 = 3096895) B3096895
theorem B2859455 : Blo 1693547 2859455 := bstep (se 1 (by rfl) ⟨2144591, by rfl⟩ : syracuseStep 2859455 = 4289183) B4289183
theorem B16294607 : Blo 1693547 16294607 := bstep (se 1 (by rfl) ⟨12220955, by rfl⟩ : syracuseStep 16294607 = 24441911) B24441911
theorem B28951505 : Blo 1693547 28951505 := bstep (se 2 (by rfl) ⟨10856814, by rfl⟩ : syracuseStep 28951505 = 21713629) B21713629
theorem B2540543 : Blo 1693547 2540543 := bstep (se 1 (by rfl) ⟨1905407, by rfl⟩ : syracuseStep 2540543 = 3810815) B3810815
theorem B2860103 : Blo 1693547 2860103 := bstep (se 1 (by rfl) ⟨2145077, by rfl⟩ : syracuseStep 2860103 = 4290155) B4290155
theorem B19309751 : Blo 1693547 19309751 := bstep (se 1 (by rfl) ⟨14482313, by rfl⟩ : syracuseStep 19309751 = 28964627) B28964627
theorem B2860751 : Blo 1693547 2860751 := bstep (se 1 (by rfl) ⟨2145563, by rfl⟩ : syracuseStep 2860751 = 4291127) B4291127
theorem B19572463 : Blo 1693547 19572463 := bstep (se 1 (by rfl) ⟨14679347, by rfl⟩ : syracuseStep 19572463 = 29358695) B29358695
theorem B2541563 : Blo 1693547 2541563 := bstep (se 1 (by rfl) ⟨1906172, by rfl⟩ : syracuseStep 2541563 = 3812345) B3812345
theorem B2541623 : Blo 1693547 2541623 := bstep (se 1 (by rfl) ⟨1906217, by rfl⟩ : syracuseStep 2541623 = 3812435) B3812435
theorem B8693867 : Blo 1693547 8693867 := bstep (se 1 (by rfl) ⟨6520400, by rfl⟩ : syracuseStep 8693867 = 13040801) B13040801
theorem B19311209 : Blo 1693547 19311209 := bstep (se 2 (by rfl) ⟨7241703, by rfl⟩ : syracuseStep 19311209 = 14483407) B14483407
theorem B2542271 : Blo 1693547 2542271 := bstep (se 1 (by rfl) ⟨1906703, by rfl⟩ : syracuseStep 2542271 = 3813407) B3813407
theorem B82414361 : Blo 1693547 82414361 := bstep (se 2 (by rfl) ⟨30905385, by rfl⟩ : syracuseStep 82414361 = 61810771) B61810771
theorem B9653053 : Blo 1693547 9653053 := bstep (se 3 (by rfl) ⟨1809947, by rfl⟩ : syracuseStep 9653053 = 3619895) B3619895
theorem B5426153 : Blo 1693547 5426153 := bstep (se 2 (by rfl) ⟨2034807, by rfl⟩ : syracuseStep 5426153 = 4069615) B4069615
theorem B2321705 : Blo 1693547 2321705 := bstep (se 2 (by rfl) ⟨870639, by rfl⟩ : syracuseStep 2321705 = 1741279) B1741279
theorem B2543087 : Blo 1693547 2543087 := bstep (se 1 (by rfl) ⟨1907315, by rfl⟩ : syracuseStep 2543087 = 3814631) B3814631
theorem B5426767 : Blo 1693547 5426767 := bstep (se 1 (by rfl) ⟨4070075, by rfl⟩ : syracuseStep 5426767 = 8140151) B8140151
theorem B2543225 : Blo 1693547 2543225 := bstep (se 2 (by rfl) ⟨953709, by rfl⟩ : syracuseStep 2543225 = 1907419) B1907419
theorem B9654011 : Blo 1693547 9654011 := bstep (se 1 (by rfl) ⟨7240508, by rfl⟩ : syracuseStep 9654011 = 14481017) B14481017
theorem B2750159 : Blo 1693547 2750159 := bstep (se 1 (by rfl) ⟨2062619, by rfl⟩ : syracuseStep 2750159 = 4125239) B4125239
theorem B38156285 : Blo 1693547 38156285 := bstep (se 3 (by rfl) ⟨7154303, by rfl⟩ : syracuseStep 38156285 = 14308607) B14308607
theorem B33012035 : Blo 1693547 33012035 := bstep (se 1 (by rfl) ⟨24759026, by rfl⟩ : syracuseStep 33012035 = 49518053) B49518053
theorem B4823783 : Blo 1693547 4823783 := bstep (se 1 (by rfl) ⟨3617837, by rfl⟩ : syracuseStep 4823783 = 7235675) B7235675
theorem B44047097 : Blo 1693547 44047097 := bstep (se 2 (by rfl) ⟨16517661, by rfl⟩ : syracuseStep 44047097 = 33035323) B33035323
theorem B82468853 : Blo 1693547 82468853 := bstep (se 5 (by rfl) ⟨3865727, by rfl⟩ : syracuseStep 82468853 = 7731455) B7731455
theorem B7733339 : Blo 1693547 7733339 := bstep (se 1 (by rfl) ⟨5800004, by rfl⟩ : syracuseStep 7733339 = 11600009) B11600009
theorem B2752795 : Blo 1693547 2752795 := bstep (se 1 (by rfl) ⟨2064596, by rfl⟩ : syracuseStep 2752795 = 4129193) B4129193
theorem B28942757 : Blo 1693547 28942757 := bstep (se 4 (by rfl) ⟨2713383, by rfl⟩ : syracuseStep 28942757 = 5426767) B5426767
theorem B10863071 : Blo 1693547 10863071 := bstep (se 1 (by rfl) ⟨8147303, by rfl⟩ : syracuseStep 10863071 = 16294607) B16294607
theorem B19301003 : Blo 1693547 19301003 := bstep (se 1 (by rfl) ⟨14475752, by rfl⟩ : syracuseStep 19301003 = 28951505) B28951505
theorem B12870737 : Blo 1693547 12870737 := bstep (se 2 (by rfl) ⟨4826526, by rfl⟩ : syracuseStep 12870737 = 9653053) B9653053
theorem B25437523 : Blo 1693547 25437523 := bstep (se 1 (by rfl) ⟨19078142, by rfl⟩ : syracuseStep 25437523 = 38156285) B38156285
theorem B54979235 : Blo 1693547 54979235 := bstep (se 1 (by rfl) ⟨41234426, by rfl⟩ : syracuseStep 54979235 = 82468853) B82468853
theorem B12873167 : Blo 1693547 12873167 := bstep (se 1 (by rfl) ⟨9654875, by rfl⟩ : syracuseStep 12873167 = 19309751) B19309751
theorem B5795911 : Blo 1693547 5795911 := bstep (se 1 (by rfl) ⟨4346933, by rfl⟩ : syracuseStep 5795911 = 8693867) B8693867
theorem B22008023 : Blo 1693547 22008023 := bstep (se 1 (by rfl) ⟨16506017, by rfl⟩ : syracuseStep 22008023 = 33012035) B33012035
theorem B12874139 : Blo 1693547 12874139 := bstep (se 1 (by rfl) ⟨9655604, by rfl⟩ : syracuseStep 12874139 = 19311209) B19311209
theorem B3215855 : Blo 1693547 3215855 := bstep (se 1 (by rfl) ⟨2411891, by rfl⟩ : syracuseStep 3215855 = 4823783) B4823783
theorem B29364731 : Blo 1693547 29364731 := bstep (se 1 (by rfl) ⟨22023548, by rfl⟩ : syracuseStep 29364731 = 44047097) B44047097
theorem B3617435 : Blo 1693547 3617435 := bstep (se 1 (by rfl) ⟨2713076, by rfl⟩ : syracuseStep 3617435 = 5426153) B5426153
theorem B26096617 : Blo 1693547 26096617 := bstep (se 2 (by rfl) ⟨9786231, by rfl⟩ : syracuseStep 26096617 = 19572463) B19572463
theorem B6436007 : Blo 1693547 6436007 := bstep (se 1 (by rfl) ⟨4827005, by rfl⟩ : syracuseStep 6436007 = 9654011) B9654011
theorem B1906303 : Blo 1693547 1906303 := bstep (se 1 (by rfl) ⟨1429727, by rfl⟩ : syracuseStep 1906303 = 2859455) B2859455
theorem B1693695 : Blo 1693547 1693695 := bstep (se 1 (by rfl) ⟨1270271, by rfl⟩ : syracuseStep 1693695 = 2540543) B2540543
theorem B1906735 : Blo 1693547 1906735 := bstep (se 1 (by rfl) ⟨1430051, by rfl⟩ : syracuseStep 1906735 = 2860103) B2860103
theorem B6191213 : Blo 1693547 6191213 := bstep (se 3 (by rfl) ⟨1160852, by rfl⟩ : syracuseStep 6191213 = 2321705) B2321705
theorem B1833439 : Blo 1693547 1833439 := bstep (se 1 (by rfl) ⟨1375079, by rfl⟩ : syracuseStep 1833439 = 2750159) B2750159
theorem B1907167 : Blo 1693547 1907167 := bstep (se 1 (by rfl) ⟨1430375, by rfl⟩ : syracuseStep 1907167 = 2860751) B2860751
theorem B1694375 : Blo 1693547 1694375 := bstep (se 1 (by rfl) ⟨1270781, by rfl⟩ : syracuseStep 1694375 = 2541563) B2541563
theorem B1694415 : Blo 1693547 1694415 := bstep (se 1 (by rfl) ⟨1270811, by rfl⟩ : syracuseStep 1694415 = 2541623) B2541623
theorem B1694847 : Blo 1693547 1694847 := bstep (se 1 (by rfl) ⟨1271135, by rfl⟩ : syracuseStep 1694847 = 2542271) B2542271
theorem B54942907 : Blo 1693547 54942907 := bstep (se 1 (by rfl) ⟨41207180, by rfl⟩ : syracuseStep 54942907 = 82414361) B82414361
theorem B1695391 : Blo 1693547 1695391 := bstep (se 1 (by rfl) ⟨1271543, by rfl⟩ : syracuseStep 1695391 = 2543087) B2543087
theorem B1695483 : Blo 1693547 1695483 := bstep (se 1 (by rfl) ⟨1271612, by rfl⟩ : syracuseStep 1695483 = 2543225) B2543225
theorem B14672015 : Blo 1693547 14672015 := bstep (se 1 (by rfl) ⟨11004011, by rfl⟩ : syracuseStep 14672015 = 22008023) B22008023
theorem B7242047 : Blo 1693547 7242047 := bstep (se 1 (by rfl) ⟨5431535, by rfl⟩ : syracuseStep 7242047 = 10863071) B10863071
theorem B14681573 : Blo 1693547 14681573 := bstep (se 4 (by rfl) ⟨1376397, by rfl⟩ : syracuseStep 14681573 = 2752795) B2752795
theorem B36652823 : Blo 1693547 36652823 := bstep (se 1 (by rfl) ⟨27489617, by rfl⟩ : syracuseStep 36652823 = 54979235) B54979235
theorem B33916697 : Blo 1693547 33916697 := bstep (se 2 (by rfl) ⟨12718761, by rfl⟩ : syracuseStep 33916697 = 25437523) B25437523
theorem B2541737 : Blo 1693547 2541737 := bstep (se 2 (by rfl) ⟨953151, by rfl⟩ : syracuseStep 2541737 = 1906303) B1906303
theorem B5155559 : Blo 1693547 5155559 := bstep (se 1 (by rfl) ⟨3866669, by rfl⟩ : syracuseStep 5155559 = 7733339) B7733339
theorem B2542313 : Blo 1693547 2542313 := bstep (se 2 (by rfl) ⟨953367, by rfl⟩ : syracuseStep 2542313 = 1906735) B1906735
theorem B7727881 : Blo 1693547 7727881 := bstep (se 2 (by rfl) ⟨2897955, by rfl⟩ : syracuseStep 7727881 = 5795911) B5795911
theorem B19295171 : Blo 1693547 19295171 := bstep (se 1 (by rfl) ⟨14471378, by rfl⟩ : syracuseStep 19295171 = 28942757) B28942757
theorem B16509901 : Blo 1693547 16509901 := bstep (se 3 (by rfl) ⟨3095606, by rfl⟩ : syracuseStep 16509901 = 6191213) B6191213
theorem B2411623 : Blo 1693547 2411623 := bstep (se 1 (by rfl) ⟨1808717, by rfl⟩ : syracuseStep 2411623 = 3617435) B3617435
theorem B2444585 : Blo 1693547 2444585 := bstep (se 2 (by rfl) ⟨916719, by rfl⟩ : syracuseStep 2444585 = 1833439) B1833439
theorem B2542889 : Blo 1693547 2542889 := bstep (se 2 (by rfl) ⟨953583, by rfl⟩ : syracuseStep 2542889 = 1907167) B1907167
theorem B8580491 : Blo 1693547 8580491 := bstep (se 1 (by rfl) ⟨6435368, by rfl⟩ : syracuseStep 8580491 = 12870737) B12870737
theorem B34795489 : Blo 1693547 34795489 := bstep (se 2 (by rfl) ⟨13048308, by rfl⟩ : syracuseStep 34795489 = 26096617) B26096617
theorem B73257209 : Blo 1693547 73257209 := bstep (se 2 (by rfl) ⟨27471453, by rfl⟩ : syracuseStep 73257209 = 54942907) B54942907
theorem B8582111 : Blo 1693547 8582111 := bstep (se 1 (by rfl) ⟨6436583, by rfl⟩ : syracuseStep 8582111 = 12873167) B12873167
theorem B8582759 : Blo 1693547 8582759 := bstep (se 1 (by rfl) ⟨6437069, by rfl⟩ : syracuseStep 8582759 = 12874139) B12874139
theorem B2143903 : Blo 1693547 2143903 := bstep (se 1 (by rfl) ⟨1607927, by rfl⟩ : syracuseStep 2143903 = 3215855) B3215855
theorem B19576487 : Blo 1693547 19576487 := bstep (se 1 (by rfl) ⟨14682365, by rfl⟩ : syracuseStep 19576487 = 29364731) B29364731
theorem B12867335 : Blo 1693547 12867335 := bstep (se 1 (by rfl) ⟨9650501, by rfl⟩ : syracuseStep 12867335 = 19301003) B19301003
theorem B4290671 : Blo 1693547 4290671 := bstep (se 1 (by rfl) ⟨3218003, by rfl⟩ : syracuseStep 4290671 = 6436007) B6436007
theorem B9781343 : Blo 1693547 9781343 := bstep (se 1 (by rfl) ⟨7336007, by rfl⟩ : syracuseStep 9781343 = 14672015) B14672015
theorem B12861989 : Blo 1693547 12861989 := bstep (se 4 (by rfl) ⟨1205811, by rfl⟩ : syracuseStep 12861989 = 2411623) B2411623
theorem B13050991 : Blo 1693547 13050991 := bstep (se 1 (by rfl) ⟨9788243, by rfl⟩ : syracuseStep 13050991 = 19576487) B19576487
theorem B8578223 : Blo 1693547 8578223 := bstep (se 1 (by rfl) ⟨6433667, by rfl⟩ : syracuseStep 8578223 = 12867335) B12867335
theorem B22611131 : Blo 1693547 22611131 := bstep (se 1 (by rfl) ⟨16958348, by rfl⟩ : syracuseStep 22611131 = 33916697) B33916697
theorem B22013201 : Blo 1693547 22013201 := bstep (se 2 (by rfl) ⟨8254950, by rfl⟩ : syracuseStep 22013201 = 16509901) B16509901
theorem B2860447 : Blo 1693547 2860447 := bstep (se 1 (by rfl) ⟨2145335, by rfl⟩ : syracuseStep 2860447 = 4290671) B4290671
theorem B12863447 : Blo 1693547 12863447 := bstep (se 1 (by rfl) ⟨9647585, by rfl⟩ : syracuseStep 12863447 = 19295171) B19295171
theorem B5720327 : Blo 1693547 5720327 := bstep (se 1 (by rfl) ⟨4290245, by rfl⟩ : syracuseStep 5720327 = 8580491) B8580491
theorem B46393985 : Blo 1693547 46393985 := bstep (se 2 (by rfl) ⟨17397744, by rfl⟩ : syracuseStep 46393985 = 34795489) B34795489
theorem B4828031 : Blo 1693547 4828031 := bstep (se 1 (by rfl) ⟨3621023, by rfl⟩ : syracuseStep 4828031 = 7242047) B7242047
theorem B5721407 : Blo 1693547 5721407 := bstep (se 1 (by rfl) ⟨4291055, by rfl⟩ : syracuseStep 5721407 = 8582111) B8582111
theorem B5721839 : Blo 1693547 5721839 := bstep (se 1 (by rfl) ⟨4291379, by rfl⟩ : syracuseStep 5721839 = 8582759) B8582759
theorem B3437039 : Blo 1693547 3437039 := bstep (se 1 (by rfl) ⟨2577779, by rfl⟩ : syracuseStep 3437039 = 5155559) B5155559
theorem B48838139 : Blo 1693547 48838139 := bstep (se 1 (by rfl) ⟨36628604, by rfl⟩ : syracuseStep 48838139 = 73257209) B73257209
theorem B6518893 : Blo 1693547 6518893 := bstep (se 3 (by rfl) ⟨1222292, by rfl⟩ : syracuseStep 6518893 = 2444585) B2444585
theorem B9787715 : Blo 1693547 9787715 := bstep (se 1 (by rfl) ⟨7340786, by rfl⟩ : syracuseStep 9787715 = 14681573) B14681573
theorem B10303841 : Blo 1693547 10303841 := bstep (se 2 (by rfl) ⟨3863940, by rfl⟩ : syracuseStep 10303841 = 7727881) B7727881
theorem B24435215 : Blo 1693547 24435215 := bstep (se 1 (by rfl) ⟨18326411, by rfl⟩ : syracuseStep 24435215 = 36652823) B36652823
theorem B1694491 : Blo 1693547 1694491 := bstep (se 1 (by rfl) ⟨1270868, by rfl⟩ : syracuseStep 1694491 = 2541737) B2541737
theorem B1694875 : Blo 1693547 1694875 := bstep (se 1 (by rfl) ⟨1271156, by rfl⟩ : syracuseStep 1694875 = 2542313) B2542313
theorem B1695259 : Blo 1693547 1695259 := bstep (se 1 (by rfl) ⟨1271444, by rfl⟩ : syracuseStep 1695259 = 2542889) B2542889
theorem B2858537 : Blo 1693547 2858537 := bstep (se 2 (by rfl) ⟨1071951, by rfl⟩ : syracuseStep 2858537 = 2143903) B2143903
theorem B6520895 : Blo 1693547 6520895 := bstep (se 1 (by rfl) ⟨4890671, by rfl⟩ : syracuseStep 6520895 = 9781343) B9781343
theorem B8691857 : Blo 1693547 8691857 := bstep (se 2 (by rfl) ⟨3259446, by rfl⟩ : syracuseStep 8691857 = 6518893) B6518893
theorem B5718815 : Blo 1693547 5718815 := bstep (se 1 (by rfl) ⟨4289111, by rfl⟩ : syracuseStep 5718815 = 8578223) B8578223
theorem B15074087 : Blo 1693547 15074087 := bstep (se 1 (by rfl) ⟨11305565, by rfl⟩ : syracuseStep 15074087 = 22611131) B22611131
theorem B17401321 : Blo 1693547 17401321 := bstep (se 2 (by rfl) ⟨6525495, by rfl⟩ : syracuseStep 17401321 = 13050991) B13050991
theorem B123717293 : Blo 1693547 123717293 := bstep (se 3 (by rfl) ⟨23196992, by rfl⟩ : syracuseStep 123717293 = 46393985) B46393985
theorem B14675467 : Blo 1693547 14675467 := bstep (se 1 (by rfl) ⟨11006600, by rfl⟩ : syracuseStep 14675467 = 22013201) B22013201
theorem B32558759 : Blo 1693547 32558759 := bstep (se 1 (by rfl) ⟨24419069, by rfl⟩ : syracuseStep 32558759 = 48838139) B48838139
theorem B3813551 : Blo 1693547 3813551 := bstep (se 1 (by rfl) ⟨2860163, by rfl⟩ : syracuseStep 3813551 = 5720327) B5720327
theorem B6525143 : Blo 1693547 6525143 := bstep (se 1 (by rfl) ⟨4893857, by rfl⟩ : syracuseStep 6525143 = 9787715) B9787715
theorem B6869227 : Blo 1693547 6869227 := bstep (se 1 (by rfl) ⟨5151920, by rfl⟩ : syracuseStep 6869227 = 10303841) B10303841
theorem B16290143 : Blo 1693547 16290143 := bstep (se 1 (by rfl) ⟨12217607, by rfl⟩ : syracuseStep 16290143 = 24435215) B24435215
theorem B3813929 : Blo 1693547 3813929 := bstep (se 2 (by rfl) ⟨1430223, by rfl⟩ : syracuseStep 3813929 = 2860447) B2860447
theorem B3814271 : Blo 1693547 3814271 := bstep (se 1 (by rfl) ⟨2860703, by rfl⟩ : syracuseStep 3814271 = 5721407) B5721407
theorem B1905691 : Blo 1693547 1905691 := bstep (se 1 (by rfl) ⟨1429268, by rfl⟩ : syracuseStep 1905691 = 2858537) B2858537
theorem B3814559 : Blo 1693547 3814559 := bstep (se 1 (by rfl) ⟨2860919, by rfl⟩ : syracuseStep 3814559 = 5721839) B5721839
theorem B8574659 : Blo 1693547 8574659 := bstep (se 1 (by rfl) ⟨6430994, by rfl⟩ : syracuseStep 8574659 = 12861989) B12861989
theorem B9165437 : Blo 1693547 9165437 := bstep (se 3 (by rfl) ⟨1718519, by rfl⟩ : syracuseStep 9165437 = 3437039) B3437039
theorem B8575631 : Blo 1693547 8575631 := bstep (se 1 (by rfl) ⟨6431723, by rfl⟩ : syracuseStep 8575631 = 12863447) B12863447
theorem B3218687 : Blo 1693547 3218687 := bstep (se 1 (by rfl) ⟨2414015, by rfl⟩ : syracuseStep 3218687 = 4828031) B4828031
theorem B4350095 : Blo 1693547 4350095 := bstep (se 1 (by rfl) ⟨3262571, by rfl⟩ : syracuseStep 4350095 = 6525143) B6525143
theorem B9158969 : Blo 1693547 9158969 := bstep (se 2 (by rfl) ⟨3434613, by rfl⟩ : syracuseStep 9158969 = 6869227) B6869227
theorem B82478195 : Blo 1693547 82478195 := bstep (se 1 (by rfl) ⟨61858646, by rfl⟩ : syracuseStep 82478195 = 123717293) B123717293
theorem B2540921 : Blo 1693547 2540921 := bstep (se 2 (by rfl) ⟨952845, by rfl⟩ : syracuseStep 2540921 = 1905691) B1905691
theorem B23201761 : Blo 1693547 23201761 := bstep (se 2 (by rfl) ⟨8700660, by rfl⟩ : syracuseStep 23201761 = 17401321) B17401321
theorem B5794571 : Blo 1693547 5794571 := bstep (se 1 (by rfl) ⟨4345928, by rfl⟩ : syracuseStep 5794571 = 8691857) B8691857
theorem B2542367 : Blo 1693547 2542367 := bstep (se 1 (by rfl) ⟨1906775, by rfl⟩ : syracuseStep 2542367 = 3813551) B3813551
theorem B2542619 : Blo 1693547 2542619 := bstep (se 1 (by rfl) ⟨1906964, by rfl⟩ : syracuseStep 2542619 = 3813929) B3813929
theorem B3812543 : Blo 1693547 3812543 := bstep (se 1 (by rfl) ⟨2859407, by rfl⟩ : syracuseStep 3812543 = 5718815) B5718815
theorem B2542847 : Blo 1693547 2542847 := bstep (se 1 (by rfl) ⟨1907135, by rfl⟩ : syracuseStep 2542847 = 3814271) B3814271
theorem B2543039 : Blo 1693547 2543039 := bstep (se 1 (by rfl) ⟨1907279, by rfl⟩ : syracuseStep 2543039 = 3814559) B3814559
theorem B19567289 : Blo 1693547 19567289 := bstep (se 2 (by rfl) ⟨7337733, by rfl⟩ : syracuseStep 19567289 = 14675467) B14675467
theorem B21705839 : Blo 1693547 21705839 := bstep (se 1 (by rfl) ⟨16279379, by rfl⟩ : syracuseStep 21705839 = 32558759) B32558759
theorem B4347263 : Blo 1693547 4347263 := bstep (se 1 (by rfl) ⟨3260447, by rfl⟩ : syracuseStep 4347263 = 6520895) B6520895
theorem B10860095 : Blo 1693547 10860095 := bstep (se 1 (by rfl) ⟨8145071, by rfl⟩ : syracuseStep 10860095 = 16290143) B16290143
theorem B5716439 : Blo 1693547 5716439 := bstep (se 1 (by rfl) ⟨4287329, by rfl⟩ : syracuseStep 5716439 = 8574659) B8574659
theorem B6110291 : Blo 1693547 6110291 := bstep (se 1 (by rfl) ⟨4582718, by rfl⟩ : syracuseStep 6110291 = 9165437) B9165437
theorem B5717087 : Blo 1693547 5717087 := bstep (se 1 (by rfl) ⟨4287815, by rfl⟩ : syracuseStep 5717087 = 8575631) B8575631
theorem B40197565 : Blo 1693547 40197565 := bstep (se 3 (by rfl) ⟨7537043, by rfl⟩ : syracuseStep 40197565 = 15074087) B15074087
theorem B2145791 : Blo 1693547 2145791 := bstep (se 1 (by rfl) ⟨1609343, by rfl⟩ : syracuseStep 2145791 = 3218687) B3218687
theorem B2900063 : Blo 1693547 2900063 := bstep (se 1 (by rfl) ⟨2175047, by rfl⟩ : syracuseStep 2900063 = 4350095) B4350095
theorem B54985463 : Blo 1693547 54985463 := bstep (se 1 (by rfl) ⟨41239097, by rfl⟩ : syracuseStep 54985463 = 82478195) B82478195
theorem B28960253 : Blo 1693547 28960253 := bstep (se 3 (by rfl) ⟨5430047, by rfl⟩ : syracuseStep 28960253 = 10860095) B10860095
theorem B3810959 : Blo 1693547 3810959 := bstep (se 1 (by rfl) ⟨2858219, by rfl⟩ : syracuseStep 3810959 = 5716439) B5716439
theorem B4073527 : Blo 1693547 4073527 := bstep (se 1 (by rfl) ⟨3055145, by rfl⟩ : syracuseStep 4073527 = 6110291) B6110291
theorem B3811391 : Blo 1693547 3811391 := bstep (se 1 (by rfl) ⟨2858543, by rfl⟩ : syracuseStep 3811391 = 5717087) B5717087
theorem B2541695 : Blo 1693547 2541695 := bstep (se 1 (by rfl) ⟨1906271, by rfl⟩ : syracuseStep 2541695 = 3812543) B3812543
theorem B214387013 : Blo 1693547 214387013 := bstep (se 4 (by rfl) ⟨20098782, by rfl⟩ : syracuseStep 214387013 = 40197565) B40197565
theorem B30935681 : Blo 1693547 30935681 := bstep (se 2 (by rfl) ⟨11600880, by rfl⟩ : syracuseStep 30935681 = 23201761) B23201761
theorem B6105979 : Blo 1693547 6105979 := bstep (se 1 (by rfl) ⟨4579484, by rfl⟩ : syracuseStep 6105979 = 9158969) B9158969
theorem B14470559 : Blo 1693547 14470559 := bstep (se 1 (by rfl) ⟨10852919, by rfl⟩ : syracuseStep 14470559 = 21705839) B21705839
theorem B5722109 : Blo 1693547 5722109 := bstep (se 3 (by rfl) ⟨1072895, by rfl⟩ : syracuseStep 5722109 = 2145791) B2145791
theorem B52179437 : Blo 1693547 52179437 := bstep (se 3 (by rfl) ⟨9783644, by rfl⟩ : syracuseStep 52179437 = 19567289) B19567289
theorem B3863047 : Blo 1693547 3863047 := bstep (se 1 (by rfl) ⟨2897285, by rfl⟩ : syracuseStep 3863047 = 5794571) B5794571
theorem B1693947 : Blo 1693547 1693947 := bstep (se 1 (by rfl) ⟨1270460, by rfl⟩ : syracuseStep 1693947 = 2540921) B2540921
theorem B2898175 : Blo 1693547 2898175 := bstep (se 1 (by rfl) ⟨2173631, by rfl⟩ : syracuseStep 2898175 = 4347263) B4347263
theorem B1694911 : Blo 1693547 1694911 := bstep (se 1 (by rfl) ⟨1271183, by rfl⟩ : syracuseStep 1694911 = 2542367) B2542367
theorem B1695079 : Blo 1693547 1695079 := bstep (se 1 (by rfl) ⟨1271309, by rfl⟩ : syracuseStep 1695079 = 2542619) B2542619
theorem B1695231 : Blo 1693547 1695231 := bstep (se 1 (by rfl) ⟨1271423, by rfl⟩ : syracuseStep 1695231 = 2542847) B2542847
theorem B1695359 : Blo 1693547 1695359 := bstep (se 1 (by rfl) ⟨1271519, by rfl⟩ : syracuseStep 1695359 = 2543039) B2543039
theorem B5431369 : Blo 1693547 5431369 := bstep (se 2 (by rfl) ⟨2036763, by rfl⟩ : syracuseStep 5431369 = 4073527) B4073527
theorem B7733501 : Blo 1693547 7733501 := bstep (se 3 (by rfl) ⟨1450031, by rfl⟩ : syracuseStep 7733501 = 2900063) B2900063
theorem B2540639 : Blo 1693547 2540639 := bstep (se 1 (by rfl) ⟨1905479, by rfl⟩ : syracuseStep 2540639 = 3810959) B3810959
theorem B2540927 : Blo 1693547 2540927 := bstep (se 1 (by rfl) ⟨1905695, by rfl⟩ : syracuseStep 2540927 = 3811391) B3811391
theorem B139145165 : Blo 1693547 139145165 := bstep (se 3 (by rfl) ⟨26089718, by rfl⟩ : syracuseStep 139145165 = 52179437) B52179437
theorem B20623787 : Blo 1693547 20623787 := bstep (se 1 (by rfl) ⟨15467840, by rfl⟩ : syracuseStep 20623787 = 30935681) B30935681
theorem B9647039 : Blo 1693547 9647039 := bstep (se 1 (by rfl) ⟨7235279, by rfl⟩ : syracuseStep 9647039 = 14470559) B14470559
theorem B3814739 : Blo 1693547 3814739 := bstep (se 1 (by rfl) ⟨2861054, by rfl⟩ : syracuseStep 3814739 = 5722109) B5722109
theorem B3864233 : Blo 1693547 3864233 := bstep (se 2 (by rfl) ⟨1449087, by rfl⟩ : syracuseStep 3864233 = 2898175) B2898175
theorem B36656975 : Blo 1693547 36656975 := bstep (se 1 (by rfl) ⟨27492731, by rfl⟩ : syracuseStep 36656975 = 54985463) B54985463
theorem B5150729 : Blo 1693547 5150729 := bstep (se 2 (by rfl) ⟨1931523, by rfl⟩ : syracuseStep 5150729 = 3863047) B3863047
theorem B19306835 : Blo 1693547 19306835 := bstep (se 1 (by rfl) ⟨14480126, by rfl⟩ : syracuseStep 19306835 = 28960253) B28960253
theorem B8141305 : Blo 1693547 8141305 := bstep (se 2 (by rfl) ⟨3052989, by rfl⟩ : syracuseStep 8141305 = 6105979) B6105979
theorem B1694463 : Blo 1693547 1694463 := bstep (se 1 (by rfl) ⟨1270847, by rfl⟩ : syracuseStep 1694463 = 2541695) B2541695
theorem B142924675 : Blo 1693547 142924675 := bstep (se 1 (by rfl) ⟨107193506, by rfl⟩ : syracuseStep 142924675 = 214387013) B214387013
theorem B7241825 : Blo 1693547 7241825 := bstep (se 2 (by rfl) ⟨2715684, by rfl⟩ : syracuseStep 7241825 = 5431369) B5431369
theorem B6431359 : Blo 1693547 6431359 := bstep (se 1 (by rfl) ⟨4823519, by rfl⟩ : syracuseStep 6431359 = 9647039) B9647039
theorem B10855073 : Blo 1693547 10855073 := bstep (se 2 (by rfl) ⟨4070652, by rfl⟩ : syracuseStep 10855073 = 8141305) B8141305
theorem B24437983 : Blo 1693547 24437983 := bstep (se 1 (by rfl) ⟨18328487, by rfl⟩ : syracuseStep 24437983 = 36656975) B36656975
theorem B12871223 : Blo 1693547 12871223 := bstep (se 1 (by rfl) ⟨9653417, by rfl⟩ : syracuseStep 12871223 = 19306835) B19306835
theorem B5155667 : Blo 1693547 5155667 := bstep (se 1 (by rfl) ⟨3866750, by rfl⟩ : syracuseStep 5155667 = 7733501) B7733501
theorem B13749191 : Blo 1693547 13749191 := bstep (se 1 (by rfl) ⟨10311893, by rfl⟩ : syracuseStep 13749191 = 20623787) B20623787
theorem B2543159 : Blo 1693547 2543159 := bstep (se 1 (by rfl) ⟨1907369, by rfl⟩ : syracuseStep 2543159 = 3814739) B3814739
theorem B190566233 : Blo 1693547 190566233 := bstep (se 2 (by rfl) ⟨71462337, by rfl⟩ : syracuseStep 190566233 = 142924675) B142924675
theorem B92763443 : Blo 1693547 92763443 := bstep (se 1 (by rfl) ⟨69572582, by rfl⟩ : syracuseStep 92763443 = 139145165) B139145165
theorem B13735277 : Blo 1693547 13735277 := bstep (se 3 (by rfl) ⟨2575364, by rfl⟩ : syracuseStep 13735277 = 5150729) B5150729
theorem B1693759 : Blo 1693547 1693759 := bstep (se 1 (by rfl) ⟨1270319, by rfl⟩ : syracuseStep 1693759 = 2540639) B2540639
theorem B1693951 : Blo 1693547 1693951 := bstep (se 1 (by rfl) ⟨1270463, by rfl⟩ : syracuseStep 1693951 = 2540927) B2540927
theorem B10304621 : Blo 1693547 10304621 := bstep (se 3 (by rfl) ⟨1932116, by rfl⟩ : syracuseStep 10304621 = 3864233) B3864233
theorem B61842295 : Blo 1693547 61842295 := bstep (se 1 (by rfl) ⟨46381721, by rfl⟩ : syracuseStep 61842295 = 92763443) B92763443
theorem B127044155 : Blo 1693547 127044155 := bstep (se 1 (by rfl) ⟨95283116, by rfl⟩ : syracuseStep 127044155 = 190566233) B190566233
theorem B4827883 : Blo 1693547 4827883 := bstep (se 1 (by rfl) ⟨3620912, by rfl⟩ : syracuseStep 4827883 = 7241825) B7241825
theorem B7236715 : Blo 1693547 7236715 := bstep (se 1 (by rfl) ⟨5427536, by rfl⟩ : syracuseStep 7236715 = 10855073) B10855073
theorem B8580815 : Blo 1693547 8580815 := bstep (se 1 (by rfl) ⟨6435611, by rfl⟩ : syracuseStep 8580815 = 12871223) B12871223
theorem B32583977 : Blo 1693547 32583977 := bstep (se 2 (by rfl) ⟨12218991, by rfl⟩ : syracuseStep 32583977 = 24437983) B24437983
theorem B3437111 : Blo 1693547 3437111 := bstep (se 1 (by rfl) ⟨2577833, by rfl⟩ : syracuseStep 3437111 = 5155667) B5155667
theorem B6869747 : Blo 1693547 6869747 := bstep (se 1 (by rfl) ⟨5152310, by rfl⟩ : syracuseStep 6869747 = 10304621) B10304621
theorem B8575145 : Blo 1693547 8575145 := bstep (se 2 (by rfl) ⟨3215679, by rfl⟩ : syracuseStep 8575145 = 6431359) B6431359
theorem B9156851 : Blo 1693547 9156851 := bstep (se 1 (by rfl) ⟨6867638, by rfl⟩ : syracuseStep 9156851 = 13735277) B13735277
theorem B9166127 : Blo 1693547 9166127 := bstep (se 1 (by rfl) ⟨6874595, by rfl⟩ : syracuseStep 9166127 = 13749191) B13749191
theorem B1695439 : Blo 1693547 1695439 := bstep (se 1 (by rfl) ⟨1271579, by rfl⟩ : syracuseStep 1695439 = 2543159) B2543159
theorem B4579831 : Blo 1693547 4579831 := bstep (se 1 (by rfl) ⟨3434873, by rfl⟩ : syracuseStep 4579831 = 6869747) B6869747
theorem B6104567 : Blo 1693547 6104567 := bstep (se 1 (by rfl) ⟨4578425, by rfl⟩ : syracuseStep 6104567 = 9156851) B9156851
theorem B5720543 : Blo 1693547 5720543 := bstep (se 1 (by rfl) ⟨4290407, by rfl⟩ : syracuseStep 5720543 = 8580815) B8580815
theorem B82456393 : Blo 1693547 82456393 := bstep (se 2 (by rfl) ⟨30921147, by rfl⟩ : syracuseStep 82456393 = 61842295) B61842295
theorem B21722651 : Blo 1693547 21722651 := bstep (se 1 (by rfl) ⟨16291988, by rfl⟩ : syracuseStep 21722651 = 32583977) B32583977
theorem B24443005 : Blo 1693547 24443005 := bstep (se 3 (by rfl) ⟨4583063, by rfl⟩ : syracuseStep 24443005 = 9166127) B9166127
theorem B6437177 : Blo 1693547 6437177 := bstep (se 2 (by rfl) ⟨2413941, by rfl⟩ : syracuseStep 6437177 = 4827883) B4827883
theorem B5716763 : Blo 1693547 5716763 := bstep (se 1 (by rfl) ⟨4287572, by rfl⟩ : syracuseStep 5716763 = 8575145) B8575145
theorem B9648953 : Blo 1693547 9648953 := bstep (se 2 (by rfl) ⟨3618357, by rfl⟩ : syracuseStep 9648953 = 7236715) B7236715
theorem B9165629 : Blo 1693547 9165629 := bstep (se 3 (by rfl) ⟨1718555, by rfl⟩ : syracuseStep 9165629 = 3437111) B3437111
theorem B84696103 : Blo 1693547 84696103 := bstep (se 1 (by rfl) ⟨63522077, by rfl⟩ : syracuseStep 84696103 = 127044155) B127044155
theorem B112928137 : Blo 1693547 112928137 := bstep (se 2 (by rfl) ⟨42348051, by rfl⟩ : syracuseStep 112928137 = 84696103) B84696103
theorem B3811175 : Blo 1693547 3811175 := bstep (se 1 (by rfl) ⟨2858381, by rfl⟩ : syracuseStep 3811175 = 5716763) B5716763
theorem B6432635 : Blo 1693547 6432635 := bstep (se 1 (by rfl) ⟨4824476, by rfl⟩ : syracuseStep 6432635 = 9648953) B9648953
theorem B32590673 : Blo 1693547 32590673 := bstep (se 2 (by rfl) ⟨12221502, by rfl⟩ : syracuseStep 32590673 = 24443005) B24443005
theorem B6106441 : Blo 1693547 6106441 := bstep (se 2 (by rfl) ⟨2289915, by rfl⟩ : syracuseStep 6106441 = 4579831) B4579831
theorem B3813695 : Blo 1693547 3813695 := bstep (se 1 (by rfl) ⟨2860271, by rfl⟩ : syracuseStep 3813695 = 5720543) B5720543
theorem B109941857 : Blo 1693547 109941857 := bstep (se 2 (by rfl) ⟨41228196, by rfl⟩ : syracuseStep 109941857 = 82456393) B82456393
theorem B4069711 : Blo 1693547 4069711 := bstep (se 1 (by rfl) ⟨3052283, by rfl⟩ : syracuseStep 4069711 = 6104567) B6104567
theorem B14481767 : Blo 1693547 14481767 := bstep (se 1 (by rfl) ⟨10861325, by rfl⟩ : syracuseStep 14481767 = 21722651) B21722651
theorem B4291451 : Blo 1693547 4291451 := bstep (se 1 (by rfl) ⟨3218588, by rfl⟩ : syracuseStep 4291451 = 6437177) B6437177
theorem B6110419 : Blo 1693547 6110419 := bstep (se 1 (by rfl) ⟨4582814, by rfl⟩ : syracuseStep 6110419 = 9165629) B9165629
theorem B73294571 : Blo 1693547 73294571 := bstep (se 1 (by rfl) ⟨54970928, by rfl⟩ : syracuseStep 73294571 = 109941857) B109941857
theorem B2540783 : Blo 1693547 2540783 := bstep (se 1 (by rfl) ⟨1905587, by rfl⟩ : syracuseStep 2540783 = 3811175) B3811175
theorem B21727115 : Blo 1693547 21727115 := bstep (se 1 (by rfl) ⟨16295336, by rfl⟩ : syracuseStep 21727115 = 32590673) B32590673
theorem B2860967 : Blo 1693547 2860967 := bstep (se 1 (by rfl) ⟨2145725, by rfl⟩ : syracuseStep 2860967 = 4291451) B4291451
theorem B2542463 : Blo 1693547 2542463 := bstep (se 1 (by rfl) ⟨1906847, by rfl⟩ : syracuseStep 2542463 = 3813695) B3813695
theorem B5426281 : Blo 1693547 5426281 := bstep (se 2 (by rfl) ⟨2034855, by rfl⟩ : syracuseStep 5426281 = 4069711) B4069711
theorem B4288423 : Blo 1693547 4288423 := bstep (se 1 (by rfl) ⟨3216317, by rfl⟩ : syracuseStep 4288423 = 6432635) B6432635
theorem B9654511 : Blo 1693547 9654511 := bstep (se 1 (by rfl) ⟨7240883, by rfl⟩ : syracuseStep 9654511 = 14481767) B14481767
theorem B8147225 : Blo 1693547 8147225 := bstep (se 2 (by rfl) ⟨3055209, by rfl⟩ : syracuseStep 8147225 = 6110419) B6110419
theorem B2409133589 : Blo 1693547 2409133589 := bstep (se 6 (by rfl) ⟨56464068, by rfl⟩ : syracuseStep 2409133589 = 112928137) B112928137
theorem B8141921 : Blo 1693547 8141921 := bstep (se 2 (by rfl) ⟨3053220, by rfl⟩ : syracuseStep 8141921 = 6106441) B6106441
theorem B5431483 : Blo 1693547 5431483 := bstep (se 1 (by rfl) ⟨4073612, by rfl⟩ : syracuseStep 5431483 = 8147225) B8147225
theorem B14484743 : Blo 1693547 14484743 := bstep (se 1 (by rfl) ⟨10863557, by rfl⟩ : syracuseStep 14484743 = 21727115) B21727115
theorem B7235041 : Blo 1693547 7235041 := bstep (se 2 (by rfl) ⟨2713140, by rfl⟩ : syracuseStep 7235041 = 5426281) B5426281
theorem B12872681 : Blo 1693547 12872681 := bstep (se 2 (by rfl) ⟨4827255, by rfl⟩ : syracuseStep 12872681 = 9654511) B9654511
theorem B5427947 : Blo 1693547 5427947 := bstep (se 1 (by rfl) ⟨4070960, by rfl⟩ : syracuseStep 5427947 = 8141921) B8141921
theorem B48863047 : Blo 1693547 48863047 := bstep (se 1 (by rfl) ⟨36647285, by rfl⟩ : syracuseStep 48863047 = 73294571) B73294571
theorem B1693855 : Blo 1693547 1693855 := bstep (se 1 (by rfl) ⟨1270391, by rfl⟩ : syracuseStep 1693855 = 2540783) B2540783
theorem B1606089059 : Blo 1693547 1606089059 := bstep (se 1 (by rfl) ⟨1204566794, by rfl⟩ : syracuseStep 1606089059 = 2409133589) B2409133589
theorem B1907311 : Blo 1693547 1907311 := bstep (se 1 (by rfl) ⟨1430483, by rfl⟩ : syracuseStep 1907311 = 2860967) B2860967
theorem B1694975 : Blo 1693547 1694975 := bstep (se 1 (by rfl) ⟨1271231, by rfl⟩ : syracuseStep 1694975 = 2542463) B2542463
theorem B5717897 : Blo 1693547 5717897 := bstep (se 2 (by rfl) ⟨2144211, by rfl⟩ : syracuseStep 5717897 = 4288423) B4288423
theorem B7241977 : Blo 1693547 7241977 := bstep (se 2 (by rfl) ⟨2715741, by rfl⟩ : syracuseStep 7241977 = 5431483) B5431483
theorem B3811931 : Blo 1693547 3811931 := bstep (se 1 (by rfl) ⟨2858948, by rfl⟩ : syracuseStep 3811931 = 5717897) B5717897
theorem B2543081 : Blo 1693547 2543081 := bstep (se 2 (by rfl) ⟨953655, by rfl⟩ : syracuseStep 2543081 = 1907311) B1907311
theorem B9646721 : Blo 1693547 9646721 := bstep (se 2 (by rfl) ⟨3617520, by rfl⟩ : syracuseStep 9646721 = 7235041) B7235041
theorem B8581787 : Blo 1693547 8581787 := bstep (se 1 (by rfl) ⟨6436340, by rfl⟩ : syracuseStep 8581787 = 12872681) B12872681
theorem B3618631 : Blo 1693547 3618631 := bstep (se 1 (by rfl) ⟨2713973, by rfl⟩ : syracuseStep 3618631 = 5427947) B5427947
theorem B9656495 : Blo 1693547 9656495 := bstep (se 1 (by rfl) ⟨7242371, by rfl⟩ : syracuseStep 9656495 = 14484743) B14484743
theorem B1070726039 : Blo 1693547 1070726039 := bstep (se 1 (by rfl) ⟨803044529, by rfl⟩ : syracuseStep 1070726039 = 1606089059) B1606089059
theorem B65150729 : Blo 1693547 65150729 := bstep (se 2 (by rfl) ⟨24431523, by rfl⟩ : syracuseStep 65150729 = 48863047) B48863047
theorem B6431147 : Blo 1693547 6431147 := bstep (se 1 (by rfl) ⟨4823360, by rfl⟩ : syracuseStep 6431147 = 9646721) B9646721
theorem B2541287 : Blo 1693547 2541287 := bstep (se 1 (by rfl) ⟨1905965, by rfl⟩ : syracuseStep 2541287 = 3811931) B3811931
theorem B5721191 : Blo 1693547 5721191 := bstep (se 1 (by rfl) ⟨4290893, by rfl⟩ : syracuseStep 5721191 = 8581787) B8581787
theorem B9655969 : Blo 1693547 9655969 := bstep (se 2 (by rfl) ⟨3620988, by rfl⟩ : syracuseStep 9655969 = 7241977) B7241977
theorem B6437663 : Blo 1693547 6437663 := bstep (se 1 (by rfl) ⟨4828247, by rfl⟩ : syracuseStep 6437663 = 9656495) B9656495
theorem B713817359 : Blo 1693547 713817359 := bstep (se 1 (by rfl) ⟨535363019, by rfl⟩ : syracuseStep 713817359 = 1070726039) B1070726039
theorem B1695387 : Blo 1693547 1695387 := bstep (se 1 (by rfl) ⟨1271540, by rfl⟩ : syracuseStep 1695387 = 2543081) B2543081
theorem B4824841 : Blo 1693547 4824841 := bstep (se 2 (by rfl) ⟨1809315, by rfl⟩ : syracuseStep 4824841 = 3618631) B3618631
theorem B43433819 : Blo 1693547 43433819 := bstep (se 1 (by rfl) ⟨32575364, by rfl⟩ : syracuseStep 43433819 = 65150729) B65150729
theorem B6433121 : Blo 1693547 6433121 := bstep (se 2 (by rfl) ⟨2412420, by rfl⟩ : syracuseStep 6433121 = 4824841) B4824841
theorem B4287431 : Blo 1693547 4287431 := bstep (se 1 (by rfl) ⟨3215573, by rfl⟩ : syracuseStep 4287431 = 6431147) B6431147
theorem B3814127 : Blo 1693547 3814127 := bstep (se 1 (by rfl) ⟨2860595, by rfl⟩ : syracuseStep 3814127 = 5721191) B5721191
theorem B475878239 : Blo 1693547 475878239 := bstep (se 1 (by rfl) ⟨356908679, by rfl⟩ : syracuseStep 475878239 = 713817359) B713817359
theorem B12874625 : Blo 1693547 12874625 := bstep (se 2 (by rfl) ⟨4827984, by rfl⟩ : syracuseStep 12874625 = 9655969) B9655969
theorem B28955879 : Blo 1693547 28955879 := bstep (se 1 (by rfl) ⟨21716909, by rfl⟩ : syracuseStep 28955879 = 43433819) B43433819
theorem B1694191 : Blo 1693547 1694191 := bstep (se 1 (by rfl) ⟨1270643, by rfl⟩ : syracuseStep 1694191 = 2541287) B2541287
theorem B4291775 : Blo 1693547 4291775 := bstep (se 1 (by rfl) ⟨3218831, by rfl⟩ : syracuseStep 4291775 = 6437663) B6437663
theorem B317252159 : Blo 1693547 317252159 := bstep (se 1 (by rfl) ⟨237939119, by rfl⟩ : syracuseStep 317252159 = 475878239) B475878239
theorem B2861183 : Blo 1693547 2861183 := bstep (se 1 (by rfl) ⟨2145887, by rfl⟩ : syracuseStep 2861183 = 4291775) B4291775
theorem B2542751 : Blo 1693547 2542751 := bstep (se 1 (by rfl) ⟨1907063, by rfl⟩ : syracuseStep 2542751 = 3814127) B3814127
theorem B19303919 : Blo 1693547 19303919 := bstep (se 1 (by rfl) ⟨14477939, by rfl⟩ : syracuseStep 19303919 = 28955879) B28955879
theorem B4288747 : Blo 1693547 4288747 := bstep (se 1 (by rfl) ⟨3216560, by rfl⟩ : syracuseStep 4288747 = 6433121) B6433121
theorem B8583083 : Blo 1693547 8583083 := bstep (se 1 (by rfl) ⟨6437312, by rfl⟩ : syracuseStep 8583083 = 12874625) B12874625
theorem B2858287 : Blo 1693547 2858287 := bstep (se 1 (by rfl) ⟨2143715, by rfl⟩ : syracuseStep 2858287 = 4287431) B4287431
theorem B5718329 : Blo 1693547 5718329 := bstep (se 2 (by rfl) ⟨2144373, by rfl⟩ : syracuseStep 5718329 = 4288747) B4288747
theorem B211501439 : Blo 1693547 211501439 := bstep (se 1 (by rfl) ⟨158626079, by rfl⟩ : syracuseStep 211501439 = 317252159) B317252159
theorem B3811049 : Blo 1693547 3811049 := bstep (se 2 (by rfl) ⟨1429143, by rfl⟩ : syracuseStep 3811049 = 2858287) B2858287
theorem B5722055 : Blo 1693547 5722055 := bstep (se 1 (by rfl) ⟨4291541, by rfl⟩ : syracuseStep 5722055 = 8583083) B8583083
theorem B1907455 : Blo 1693547 1907455 := bstep (se 1 (by rfl) ⟨1430591, by rfl⟩ : syracuseStep 1907455 = 2861183) B2861183
theorem B1695167 : Blo 1693547 1695167 := bstep (se 1 (by rfl) ⟨1271375, by rfl⟩ : syracuseStep 1695167 = 2542751) B2542751
theorem B12869279 : Blo 1693547 12869279 := bstep (se 1 (by rfl) ⟨9651959, by rfl⟩ : syracuseStep 12869279 = 19303919) B19303919
theorem B141000959 : Blo 1693547 141000959 := bstep (se 1 (by rfl) ⟨105750719, by rfl⟩ : syracuseStep 141000959 = 211501439) B211501439
theorem B2540699 : Blo 1693547 2540699 := bstep (se 1 (by rfl) ⟨1905524, by rfl⟩ : syracuseStep 2540699 = 3811049) B3811049
theorem B8579519 : Blo 1693547 8579519 := bstep (se 1 (by rfl) ⟨6434639, by rfl⟩ : syracuseStep 8579519 = 12869279) B12869279
theorem B3812219 : Blo 1693547 3812219 := bstep (se 1 (by rfl) ⟨2859164, by rfl⟩ : syracuseStep 3812219 = 5718329) B5718329
theorem B2543273 : Blo 1693547 2543273 := bstep (se 2 (by rfl) ⟨953727, by rfl⟩ : syracuseStep 2543273 = 1907455) B1907455
theorem B3814703 : Blo 1693547 3814703 := bstep (se 1 (by rfl) ⟨2861027, by rfl⟩ : syracuseStep 3814703 = 5722055) B5722055
theorem B5719679 : Blo 1693547 5719679 := bstep (se 1 (by rfl) ⟨4289759, by rfl⟩ : syracuseStep 5719679 = 8579519) B8579519
theorem B2541479 : Blo 1693547 2541479 := bstep (se 1 (by rfl) ⟨1906109, by rfl⟩ : syracuseStep 2541479 = 3812219) B3812219
theorem B2543135 : Blo 1693547 2543135 := bstep (se 1 (by rfl) ⟨1907351, by rfl⟩ : syracuseStep 2543135 = 3814703) B3814703
theorem B376002557 : Blo 1693547 376002557 := bstep (se 3 (by rfl) ⟨70500479, by rfl⟩ : syracuseStep 376002557 = 141000959) B141000959
theorem B1693799 : Blo 1693547 1693799 := bstep (se 1 (by rfl) ⟨1270349, by rfl⟩ : syracuseStep 1693799 = 2540699) B2540699
theorem B1695515 : Blo 1693547 1695515 := bstep (se 1 (by rfl) ⟨1271636, by rfl⟩ : syracuseStep 1695515 = 2543273) B2543273
theorem B250668371 : Blo 1693547 250668371 := bstep (se 1 (by rfl) ⟨188001278, by rfl⟩ : syracuseStep 250668371 = 376002557) B376002557
theorem B3813119 : Blo 1693547 3813119 := bstep (se 1 (by rfl) ⟨2859839, by rfl⟩ : syracuseStep 3813119 = 5719679) B5719679
theorem B1694319 : Blo 1693547 1694319 := bstep (se 1 (by rfl) ⟨1270739, by rfl⟩ : syracuseStep 1694319 = 2541479) B2541479
theorem B1695423 : Blo 1693547 1695423 := bstep (se 1 (by rfl) ⟨1271567, by rfl⟩ : syracuseStep 1695423 = 2543135) B2543135
theorem B2542079 : Blo 1693547 2542079 := bstep (se 1 (by rfl) ⟨1906559, by rfl⟩ : syracuseStep 2542079 = 3813119) B3813119
theorem B167112247 : Blo 1693547 167112247 := bstep (se 1 (by rfl) ⟨125334185, by rfl⟩ : syracuseStep 167112247 = 250668371) B250668371
theorem B222816329 : Blo 1693547 222816329 := bstep (se 2 (by rfl) ⟨83556123, by rfl⟩ : syracuseStep 222816329 = 167112247) B167112247
theorem B1694719 : Blo 1693547 1694719 := bstep (se 1 (by rfl) ⟨1271039, by rfl⟩ : syracuseStep 1694719 = 2542079) B2542079
theorem B148544219 : Blo 1693547 148544219 := bstep (se 1 (by rfl) ⟨111408164, by rfl⟩ : syracuseStep 148544219 = 222816329) B222816329
theorem B99029479 : Blo 1693547 99029479 := bstep (se 1 (by rfl) ⟨74272109, by rfl⟩ : syracuseStep 99029479 = 148544219) B148544219
theorem B132039305 : Blo 1693547 132039305 := bstep (se 2 (by rfl) ⟨49514739, by rfl⟩ : syracuseStep 132039305 = 99029479) B99029479
theorem B88026203 : Blo 1693547 88026203 := bstep (se 1 (by rfl) ⟨66019652, by rfl⟩ : syracuseStep 88026203 = 132039305) B132039305
theorem B234736541 : Blo 1693547 234736541 := bstep (se 3 (by rfl) ⟨44013101, by rfl⟩ : syracuseStep 234736541 = 88026203) B88026203
theorem B156491027 : Blo 1693547 156491027 := bstep (se 1 (by rfl) ⟨117368270, by rfl⟩ : syracuseStep 156491027 = 234736541) B234736541
theorem B104327351 : Blo 1693547 104327351 := bstep (se 1 (by rfl) ⟨78245513, by rfl⟩ : syracuseStep 104327351 = 156491027) B156491027
theorem B69551567 : Blo 1693547 69551567 := bstep (se 1 (by rfl) ⟨52163675, by rfl⟩ : syracuseStep 69551567 = 104327351) B104327351
theorem B46367711 : Blo 1693547 46367711 := bstep (se 1 (by rfl) ⟨34775783, by rfl⟩ : syracuseStep 46367711 = 69551567) B69551567
theorem B30911807 : Blo 1693547 30911807 := bstep (se 1 (by rfl) ⟨23183855, by rfl⟩ : syracuseStep 30911807 = 46367711) B46367711
theorem B20607871 : Blo 1693547 20607871 := bstep (se 1 (by rfl) ⟨15455903, by rfl⟩ : syracuseStep 20607871 = 30911807) B30911807
theorem B27477161 : Blo 1693547 27477161 := bstep (se 2 (by rfl) ⟨10303935, by rfl⟩ : syracuseStep 27477161 = 20607871) B20607871
theorem B18318107 : Blo 1693547 18318107 := bstep (se 1 (by rfl) ⟨13738580, by rfl⟩ : syracuseStep 18318107 = 27477161) B27477161
theorem B48848285 : Blo 1693547 48848285 := bstep (se 3 (by rfl) ⟨9159053, by rfl⟩ : syracuseStep 48848285 = 18318107) B18318107
theorem B32565523 : Blo 1693547 32565523 := bstep (se 1 (by rfl) ⟨24424142, by rfl⟩ : syracuseStep 32565523 = 48848285) B48848285
theorem B43420697 : Blo 1693547 43420697 := bstep (se 2 (by rfl) ⟨16282761, by rfl⟩ : syracuseStep 43420697 = 32565523) B32565523
theorem B28947131 : Blo 1693547 28947131 := bstep (se 1 (by rfl) ⟨21710348, by rfl⟩ : syracuseStep 28947131 = 43420697) B43420697
theorem B19298087 : Blo 1693547 19298087 := bstep (se 1 (by rfl) ⟨14473565, by rfl⟩ : syracuseStep 19298087 = 28947131) B28947131
theorem B12865391 : Blo 1693547 12865391 := bstep (se 1 (by rfl) ⟨9649043, by rfl⟩ : syracuseStep 12865391 = 19298087) B19298087
theorem B8576927 : Blo 1693547 8576927 := bstep (se 1 (by rfl) ⟨6432695, by rfl⟩ : syracuseStep 8576927 = 12865391) B12865391
theorem B5717951 : Blo 1693547 5717951 := bstep (se 1 (by rfl) ⟨4288463, by rfl⟩ : syracuseStep 5717951 = 8576927) B8576927
theorem B3811967 : Blo 1693547 3811967 := bstep (se 1 (by rfl) ⟨2858975, by rfl⟩ : syracuseStep 3811967 = 5717951) B5717951
theorem B2541311 : Blo 1693547 2541311 := bstep (se 1 (by rfl) ⟨1905983, by rfl⟩ : syracuseStep 2541311 = 3811967) B3811967
theorem B1694207 : Blo 1693547 1694207 := bstep (se 1 (by rfl) ⟨1270655, by rfl⟩ : syracuseStep 1694207 = 2541311) B2541311

theorem C0 (j : ℕ) (h1 : 423386 ≤ j) (h2 : j ≤ 423886) : Blo 1693547 (4 * j + 3) := by
  interval_cases j
  · exact B1693547
  · exact B1693551
  · exact B1693555
  · exact B1693559
  · exact B1693563
  · exact B1693567
  · exact B1693571
  · exact B1693575
  · exact B1693579
  · exact B1693583
  · exact B1693587
  · exact B1693591
  · exact B1693595
  · exact B1693599
  · exact B1693603
  · exact B1693607
  · exact B1693611
  · exact B1693615
  · exact B1693619
  · exact B1693623
  · exact B1693627
  · exact B1693631
  · exact B1693635
  · exact B1693639
  · exact B1693643
  · exact B1693647
  · exact B1693651
  · exact B1693655
  · exact B1693659
  · exact B1693663
  · exact B1693667
  · exact B1693671
  · exact B1693675
  · exact B1693679
  · exact B1693683
  · exact B1693687
  · exact B1693691
  · exact B1693695
  · exact B1693699
  · exact B1693703
  · exact B1693707
  · exact B1693711
  · exact B1693715
  · exact B1693719
  · exact B1693723
  · exact B1693727
  · exact B1693731
  · exact B1693735
  · exact B1693739
  · exact B1693743
  · exact B1693747
  · exact B1693751
  · exact B1693755
  · exact B1693759
  · exact B1693763
  · exact B1693767
  · exact B1693771
  · exact B1693775
  · exact B1693779
  · exact B1693783
  · exact B1693787
  · exact B1693791
  · exact B1693795
  · exact B1693799
  · exact B1693803
  · exact B1693807
  · exact B1693811
  · exact B1693815
  · exact B1693819
  · exact B1693823
  · exact B1693827
  · exact B1693831
  · exact B1693835
  · exact B1693839
  · exact B1693843
  · exact B1693847
  · exact B1693851
  · exact B1693855
  · exact B1693859
  · exact B1693863
  · exact B1693867
  · exact B1693871
  · exact B1693875
  · exact B1693879
  · exact B1693883
  · exact B1693887
  · exact B1693891
  · exact B1693895
  · exact B1693899
  · exact B1693903
  · exact B1693907
  · exact B1693911
  · exact B1693915
  · exact B1693919
  · exact B1693923
  · exact B1693927
  · exact B1693931
  · exact B1693935
  · exact B1693939
  · exact B1693943
  · exact B1693947
  · exact B1693951
  · exact B1693955
  · exact B1693959
  · exact B1693963
  · exact B1693967
  · exact B1693971
  · exact B1693975
  · exact B1693979
  · exact B1693983
  · exact B1693987
  · exact B1693991
  · exact B1693995
  · exact B1693999
  · exact B1694003
  · exact B1694007
  · exact B1694011
  · exact B1694015
  · exact B1694019
  · exact B1694023
  · exact B1694027
  · exact B1694031
  · exact B1694035
  · exact B1694039
  · exact B1694043
  · exact B1694047
  · exact B1694051
  · exact B1694055
  · exact B1694059
  · exact B1694063
  · exact B1694067
  · exact B1694071
  · exact B1694075
  · exact B1694079
  · exact B1694083
  · exact B1694087
  · exact B1694091
  · exact B1694095
  · exact B1694099
  · exact B1694103
  · exact B1694107
  · exact B1694111
  · exact B1694115
  · exact B1694119
  · exact B1694123
  · exact B1694127
  · exact B1694131
  · exact B1694135
  · exact B1694139
  · exact B1694143
  · exact B1694147
  · exact B1694151
  · exact B1694155
  · exact B1694159
  · exact B1694163
  · exact B1694167
  · exact B1694171
  · exact B1694175
  · exact B1694179
  · exact B1694183
  · exact B1694187
  · exact B1694191
  · exact B1694195
  · exact B1694199
  · exact B1694203
  · exact B1694207
  · exact B1694211
  · exact B1694215
  · exact B1694219
  · exact B1694223
  · exact B1694227
  · exact B1694231
  · exact B1694235
  · exact B1694239
  · exact B1694243
  · exact B1694247
  · exact B1694251
  · exact B1694255
  · exact B1694259
  · exact B1694263
  · exact B1694267
  · exact B1694271
  · exact B1694275
  · exact B1694279
  · exact B1694283
  · exact B1694287
  · exact B1694291
  · exact B1694295
  · exact B1694299
  · exact B1694303
  · exact B1694307
  · exact B1694311
  · exact B1694315
  · exact B1694319
  · exact B1694323
  · exact B1694327
  · exact B1694331
  · exact B1694335
  · exact B1694339
  · exact B1694343
  · exact B1694347
  · exact B1694351
  · exact B1694355
  · exact B1694359
  · exact B1694363
  · exact B1694367
  · exact B1694371
  · exact B1694375
  · exact B1694379
  · exact B1694383
  · exact B1694387
  · exact B1694391
  · exact B1694395
  · exact B1694399
  · exact B1694403
  · exact B1694407
  · exact B1694411
  · exact B1694415
  · exact B1694419
  · exact B1694423
  · exact B1694427
  · exact B1694431
  · exact B1694435
  · exact B1694439
  · exact B1694443
  · exact B1694447
  · exact B1694451
  · exact B1694455
  · exact B1694459
  · exact B1694463
  · exact B1694467
  · exact B1694471
  · exact B1694475
  · exact B1694479
  · exact B1694483
  · exact B1694487
  · exact B1694491
  · exact B1694495
  · exact B1694499
  · exact B1694503
  · exact B1694507
  · exact B1694511
  · exact B1694515
  · exact B1694519
  · exact B1694523
  · exact B1694527
  · exact B1694531
  · exact B1694535
  · exact B1694539
  · exact B1694543
  · exact B1694547
  · exact B1694551
  · exact B1694555
  · exact B1694559
  · exact B1694563
  · exact B1694567
  · exact B1694571
  · exact B1694575
  · exact B1694579
  · exact B1694583
  · exact B1694587
  · exact B1694591
  · exact B1694595
  · exact B1694599
  · exact B1694603
  · exact B1694607
  · exact B1694611
  · exact B1694615
  · exact B1694619
  · exact B1694623
  · exact B1694627
  · exact B1694631
  · exact B1694635
  · exact B1694639
  · exact B1694643
  · exact B1694647
  · exact B1694651
  · exact B1694655
  · exact B1694659
  · exact B1694663
  · exact B1694667
  · exact B1694671
  · exact B1694675
  · exact B1694679
  · exact B1694683
  · exact B1694687
  · exact B1694691
  · exact B1694695
  · exact B1694699
  · exact B1694703
  · exact B1694707
  · exact B1694711
  · exact B1694715
  · exact B1694719
  · exact B1694723
  · exact B1694727
  · exact B1694731
  · exact B1694735
  · exact B1694739
  · exact B1694743
  · exact B1694747
  · exact B1694751
  · exact B1694755
  · exact B1694759
  · exact B1694763
  · exact B1694767
  · exact B1694771
  · exact B1694775
  · exact B1694779
  · exact B1694783
  · exact B1694787
  · exact B1694791
  · exact B1694795
  · exact B1694799
  · exact B1694803
  · exact B1694807
  · exact B1694811
  · exact B1694815
  · exact B1694819
  · exact B1694823
  · exact B1694827
  · exact B1694831
  · exact B1694835
  · exact B1694839
  · exact B1694843
  · exact B1694847
  · exact B1694851
  · exact B1694855
  · exact B1694859
  · exact B1694863
  · exact B1694867
  · exact B1694871
  · exact B1694875
  · exact B1694879
  · exact B1694883
  · exact B1694887
  · exact B1694891
  · exact B1694895
  · exact B1694899
  · exact B1694903
  · exact B1694907
  · exact B1694911
  · exact B1694915
  · exact B1694919
  · exact B1694923
  · exact B1694927
  · exact B1694931
  · exact B1694935
  · exact B1694939
  · exact B1694943
  · exact B1694947
  · exact B1694951
  · exact B1694955
  · exact B1694959
  · exact B1694963
  · exact B1694967
  · exact B1694971
  · exact B1694975
  · exact B1694979
  · exact B1694983
  · exact B1694987
  · exact B1694991
  · exact B1694995
  · exact B1694999
  · exact B1695003
  · exact B1695007
  · exact B1695011
  · exact B1695015
  · exact B1695019
  · exact B1695023
  · exact B1695027
  · exact B1695031
  · exact B1695035
  · exact B1695039
  · exact B1695043
  · exact B1695047
  · exact B1695051
  · exact B1695055
  · exact B1695059
  · exact B1695063
  · exact B1695067
  · exact B1695071
  · exact B1695075
  · exact B1695079
  · exact B1695083
  · exact B1695087
  · exact B1695091
  · exact B1695095
  · exact B1695099
  · exact B1695103
  · exact B1695107
  · exact B1695111
  · exact B1695115
  · exact B1695119
  · exact B1695123
  · exact B1695127
  · exact B1695131
  · exact B1695135
  · exact B1695139
  · exact B1695143
  · exact B1695147
  · exact B1695151
  · exact B1695155
  · exact B1695159
  · exact B1695163
  · exact B1695167
  · exact B1695171
  · exact B1695175
  · exact B1695179
  · exact B1695183
  · exact B1695187
  · exact B1695191
  · exact B1695195
  · exact B1695199
  · exact B1695203
  · exact B1695207
  · exact B1695211
  · exact B1695215
  · exact B1695219
  · exact B1695223
  · exact B1695227
  · exact B1695231
  · exact B1695235
  · exact B1695239
  · exact B1695243
  · exact B1695247
  · exact B1695251
  · exact B1695255
  · exact B1695259
  · exact B1695263
  · exact B1695267
  · exact B1695271
  · exact B1695275
  · exact B1695279
  · exact B1695283
  · exact B1695287
  · exact B1695291
  · exact B1695295
  · exact B1695299
  · exact B1695303
  · exact B1695307
  · exact B1695311
  · exact B1695315
  · exact B1695319
  · exact B1695323
  · exact B1695327
  · exact B1695331
  · exact B1695335
  · exact B1695339
  · exact B1695343
  · exact B1695347
  · exact B1695351
  · exact B1695355
  · exact B1695359
  · exact B1695363
  · exact B1695367
  · exact B1695371
  · exact B1695375
  · exact B1695379
  · exact B1695383
  · exact B1695387
  · exact B1695391
  · exact B1695395
  · exact B1695399
  · exact B1695403
  · exact B1695407
  · exact B1695411
  · exact B1695415
  · exact B1695419
  · exact B1695423
  · exact B1695427
  · exact B1695431
  · exact B1695435
  · exact B1695439
  · exact B1695443
  · exact B1695447
  · exact B1695451
  · exact B1695455
  · exact B1695459
  · exact B1695463
  · exact B1695467
  · exact B1695471
  · exact B1695475
  · exact B1695479
  · exact B1695483
  · exact B1695487
  · exact B1695491
  · exact B1695495
  · exact B1695499
  · exact B1695503
  · exact B1695507
  · exact B1695511
  · exact B1695515
  · exact B1695519
  · exact B1695523
  · exact B1695527
  · exact B1695531
  · exact B1695535
  · exact B1695539
  · exact B1695543
  · exact B1695547

theorem solution (m : ℕ) (hlo : 1693547 ≤ m) (hhi : m ≤ 1695547) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 423386 ≤ j := by omega
    have hj2 : j ≤ 423886 := by omega
    have hb : Blo 1693547 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
