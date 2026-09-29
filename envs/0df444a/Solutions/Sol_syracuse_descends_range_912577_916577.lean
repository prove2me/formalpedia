-- Prove2me | solution 1 for syracuse_descends_range_912577_916577
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:51.370114+00:00
-- url     : https://prove2.me/submissions/1cc30a47-f173-4fe0-8d53-4f5501477087

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


theorem B3080213 : Blo 912577 3080213 := bbase (se 6 (by rfl) ⟨72192, by rfl⟩ : syracuseStep 3080213 = 144385) (by norm_num)
theorem B1540181 : Blo 912577 1540181 := bbase (se 8 (by rfl) ⟨9024, by rfl⟩ : syracuseStep 1540181 = 18049) (by norm_num)
theorem B1736797 : Blo 912577 1736797 := bbase (se 3 (by rfl) ⟨325649, by rfl⟩ : syracuseStep 1736797 = 651299) (by norm_num)
theorem B1540309 : Blo 912577 1540309 := bbase (se 7 (by rfl) ⟨18050, by rfl⟩ : syracuseStep 1540309 = 36101) (by norm_num)
theorem B1736957 : Blo 912577 1736957 := bbase (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) (by norm_num)
theorem B1540397 : Blo 912577 1540397 := bbase (se 3 (by rfl) ⟨288824, by rfl⟩ : syracuseStep 1540397 = 577649) (by norm_num)
theorem B1737101 : Blo 912577 1737101 := bbase (se 3 (by rfl) ⟨325706, by rfl⟩ : syracuseStep 1737101 = 651413) (by norm_num)
theorem B1540525 : Blo 912577 1540525 := bbase (se 3 (by rfl) ⟨288848, by rfl⟩ : syracuseStep 1540525 = 577697) (by norm_num)
theorem B4620725 : Blo 912577 4620725 := bbase (se 5 (by rfl) ⟨216596, by rfl⟩ : syracuseStep 4620725 = 433193) (by norm_num)
theorem B3080645 : Blo 912577 3080645 := bbase (se 4 (by rfl) ⟨288810, by rfl⟩ : syracuseStep 3080645 = 577621) (by norm_num)
theorem B8028629 : Blo 912577 8028629 := bbase (se 7 (by rfl) ⟨94085, by rfl⟩ : syracuseStep 8028629 = 188171) (by norm_num)
theorem B1671637 : Blo 912577 1671637 := bbase (se 7 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 1671637 = 39179) (by norm_num)
theorem B1540613 : Blo 912577 1540613 := bbase (se 4 (by rfl) ⟨144432, by rfl⟩ : syracuseStep 1540613 = 288865) (by norm_num)
theorem B1540741 : Blo 912577 1540741 := bbase (se 4 (by rfl) ⟨144444, by rfl⟩ : syracuseStep 1540741 = 288889) (by norm_num)
theorem B1737389 : Blo 912577 1737389 := bbase (se 3 (by rfl) ⟨325760, by rfl⟩ : syracuseStep 1737389 = 651521) (by norm_num)
theorem B1540829 : Blo 912577 1540829 := bbase (se 3 (by rfl) ⟨288905, by rfl⟩ : syracuseStep 1540829 = 577811) (by norm_num)
theorem B6259477 : Blo 912577 6259477 := bbase (se 6 (by rfl) ⟨146706, by rfl⟩ : syracuseStep 6259477 = 293413) (by norm_num)
theorem B1737541 : Blo 912577 1737541 := bbase (se 4 (by rfl) ⟨162894, by rfl⟩ : syracuseStep 1737541 = 325789) (by norm_num)
theorem B1540957 : Blo 912577 1540957 := bbase (se 3 (by rfl) ⟨288929, by rfl⟩ : syracuseStep 1540957 = 577859) (by norm_num)
theorem B3081077 : Blo 912577 3081077 := bbase (se 5 (by rfl) ⟨144425, by rfl⟩ : syracuseStep 3081077 = 288851) (by norm_num)
theorem B1541045 : Blo 912577 1541045 := bbase (se 5 (by rfl) ⟨72236, by rfl⟩ : syracuseStep 1541045 = 144473) (by norm_num)
theorem B1541173 : Blo 912577 1541173 := bbase (se 5 (by rfl) ⟨72242, by rfl⟩ : syracuseStep 1541173 = 144485) (by norm_num)
theorem B3343445 : Blo 912577 3343445 := bbase (se 8 (by rfl) ⟨19590, by rfl⟩ : syracuseStep 3343445 = 39181) (by norm_num)
theorem B1737845 : Blo 912577 1737845 := bbase (se 5 (by rfl) ⟨81461, by rfl⟩ : syracuseStep 1737845 = 162923) (by norm_num)
theorem B5866613 : Blo 912577 5866613 := bbase (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) (by norm_num)
theorem B1541261 : Blo 912577 1541261 := bbase (se 3 (by rfl) ⟨288986, by rfl⟩ : syracuseStep 1541261 = 577973) (by norm_num)
theorem B1541389 : Blo 912577 1541389 := bbase (se 3 (by rfl) ⟨289010, by rfl⟩ : syracuseStep 1541389 = 578021) (by norm_num)
theorem B3081509 : Blo 912577 3081509 := bbase (se 4 (by rfl) ⟨288891, by rfl⟩ : syracuseStep 3081509 = 577783) (by norm_num)
theorem B5276981 : Blo 912577 5276981 := bbase (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) (by norm_num)
theorem B1541477 : Blo 912577 1541477 := bbase (se 4 (by rfl) ⟨144513, by rfl⟩ : syracuseStep 1541477 = 289027) (by norm_num)
theorem B4294085 : Blo 912577 4294085 := bbase (se 4 (by rfl) ⟨402570, by rfl⟩ : syracuseStep 4294085 = 805141) (by norm_num)
theorem B1541605 : Blo 912577 1541605 := bbase (se 4 (by rfl) ⟨144525, by rfl⟩ : syracuseStep 1541605 = 289051) (by norm_num)
theorem B6948341 : Blo 912577 6948341 := bbase (se 5 (by rfl) ⟨325703, by rfl⟩ : syracuseStep 6948341 = 651407) (by norm_num)
theorem B1541693 : Blo 912577 1541693 := bbase (se 3 (by rfl) ⟨289067, by rfl⟩ : syracuseStep 1541693 = 578135) (by norm_num)
theorem B3901061 : Blo 912577 3901061 := bbase (se 4 (by rfl) ⟨365724, by rfl⟩ : syracuseStep 3901061 = 731449) (by norm_num)
theorem B1541821 : Blo 912577 1541821 := bbase (se 3 (by rfl) ⟨289091, by rfl⟩ : syracuseStep 1541821 = 578183) (by norm_num)
theorem B4622021 : Blo 912577 4622021 := bbase (se 4 (by rfl) ⟨433314, by rfl⟩ : syracuseStep 4622021 = 866629) (by norm_num)
theorem B3081941 : Blo 912577 3081941 := bbase (se 7 (by rfl) ⟨36116, by rfl⟩ : syracuseStep 3081941 = 72233) (by norm_num)
theorem B1541909 : Blo 912577 1541909 := bbase (se 6 (by rfl) ⟨36138, by rfl⟩ : syracuseStep 1541909 = 72277) (by norm_num)
theorem B1738597 : Blo 912577 1738597 := bbase (se 4 (by rfl) ⟨162993, by rfl⟩ : syracuseStep 1738597 = 325987) (by norm_num)
theorem B1542037 : Blo 912577 1542037 := bbase (se 6 (by rfl) ⟨36141, by rfl⟩ : syracuseStep 1542037 = 72283) (by norm_num)
theorem B1542125 : Blo 912577 1542125 := bbase (se 3 (by rfl) ⟨289148, by rfl⟩ : syracuseStep 1542125 = 578297) (by norm_num)
theorem B1738741 : Blo 912577 1738741 := bbase (se 5 (by rfl) ⟨81503, by rfl⟩ : syracuseStep 1738741 = 163007) (by norm_num)
theorem B3475493 : Blo 912577 3475493 := bbase (se 4 (by rfl) ⟨325827, by rfl⟩ : syracuseStep 3475493 = 651655) (by norm_num)
theorem B1542253 : Blo 912577 1542253 := bbase (se 3 (by rfl) ⟨289172, by rfl⟩ : syracuseStep 1542253 = 578345) (by norm_num)
theorem B3082373 : Blo 912577 3082373 := bbase (se 4 (by rfl) ⟨288972, by rfl⟩ : syracuseStep 3082373 = 577945) (by norm_num)
theorem B1738901 : Blo 912577 1738901 := bbase (se 6 (by rfl) ⟨40755, by rfl⟩ : syracuseStep 1738901 = 81511) (by norm_num)
theorem B1542341 : Blo 912577 1542341 := bbase (se 4 (by rfl) ⟨144594, by rfl⟩ : syracuseStep 1542341 = 289189) (by norm_num)
theorem B1739045 : Blo 912577 1739045 := bbase (se 4 (by rfl) ⟨163035, by rfl⟩ : syracuseStep 1739045 = 326071) (by norm_num)
theorem B1542469 : Blo 912577 1542469 := bbase (se 4 (by rfl) ⟨144606, by rfl⟩ : syracuseStep 1542469 = 289213) (by norm_num)
theorem B3475781 : Blo 912577 3475781 := bbase (se 4 (by rfl) ⟨325854, by rfl⟩ : syracuseStep 3475781 = 651709) (by norm_num)
theorem B4393349 : Blo 912577 4393349 := bbase (se 4 (by rfl) ⟨411876, by rfl⟩ : syracuseStep 4393349 = 823753) (by norm_num)
theorem B1542557 : Blo 912577 1542557 := bbase (se 3 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 1542557 = 578459) (by norm_num)
theorem B1542685 : Blo 912577 1542685 := bbase (se 3 (by rfl) ⟨289253, by rfl⟩ : syracuseStep 1542685 = 578507) (by norm_num)
theorem B3082805 : Blo 912577 3082805 := bbase (se 5 (by rfl) ⟨144506, by rfl⟩ : syracuseStep 3082805 = 289013) (by norm_num)
theorem B1739333 : Blo 912577 1739333 := bbase (se 4 (by rfl) ⟨163062, by rfl⟩ : syracuseStep 1739333 = 326125) (by norm_num)
theorem B3902053 : Blo 912577 3902053 := bbase (se 4 (by rfl) ⟨365817, by rfl⟩ : syracuseStep 3902053 = 731635) (by norm_num)
theorem B1542773 : Blo 912577 1542773 := bbase (se 5 (by rfl) ⟨72317, by rfl⟩ : syracuseStep 1542773 = 144635) (by norm_num)
theorem B5638805 : Blo 912577 5638805 := bbase (se 6 (by rfl) ⟨132159, by rfl⟩ : syracuseStep 5638805 = 264319) (by norm_num)
theorem B1739485 : Blo 912577 1739485 := bbase (se 3 (by rfl) ⟨326153, by rfl⟩ : syracuseStep 1739485 = 652307) (by norm_num)
theorem B1542901 : Blo 912577 1542901 := bbase (se 5 (by rfl) ⟨72323, by rfl⟩ : syracuseStep 1542901 = 144647) (by norm_num)
theorem B2198269 : Blo 912577 2198269 := bbase (se 3 (by rfl) ⟨412175, by rfl⟩ : syracuseStep 2198269 = 824351) (by norm_num)
theorem B1542989 : Blo 912577 1542989 := bbase (se 3 (by rfl) ⟨289310, by rfl⟩ : syracuseStep 1542989 = 578621) (by norm_num)
theorem B1543117 : Blo 912577 1543117 := bbase (se 3 (by rfl) ⟨289334, by rfl⟩ : syracuseStep 1543117 = 578669) (by norm_num)
theorem B4623317 : Blo 912577 4623317 := bbase (se 7 (by rfl) ⟨54179, by rfl⟩ : syracuseStep 4623317 = 108359) (by norm_num)
theorem B3083237 : Blo 912577 3083237 := bbase (se 4 (by rfl) ⟨289053, by rfl⟩ : syracuseStep 3083237 = 578107) (by norm_num)
theorem B1739789 : Blo 912577 1739789 := bbase (se 3 (by rfl) ⟨326210, by rfl⟩ : syracuseStep 1739789 = 652421) (by norm_num)
theorem B1543205 : Blo 912577 1543205 := bbase (se 4 (by rfl) ⟨144675, by rfl⟩ : syracuseStep 1543205 = 289351) (by norm_num)
theorem B1543333 : Blo 912577 1543333 := bbase (se 4 (by rfl) ⟨144687, by rfl⟩ : syracuseStep 1543333 = 289375) (by norm_num)
theorem B11144405 : Blo 912577 11144405 := bbase (se 7 (by rfl) ⟨130598, by rfl⟩ : syracuseStep 11144405 = 261197) (by norm_num)
theorem B1543421 : Blo 912577 1543421 := bbase (se 3 (by rfl) ⟨289391, by rfl⟩ : syracuseStep 1543421 = 578783) (by norm_num)
theorem B7048565 : Blo 912577 7048565 := bbase (se 5 (by rfl) ⟨330401, by rfl⟩ : syracuseStep 7048565 = 660803) (by norm_num)
theorem B1543549 : Blo 912577 1543549 := bbase (se 3 (by rfl) ⟨289415, by rfl⟩ : syracuseStep 1543549 = 578831) (by norm_num)
theorem B3083669 : Blo 912577 3083669 := bbase (se 6 (by rfl) ⟨72273, by rfl⟩ : syracuseStep 3083669 = 144547) (by norm_num)
theorem B1543637 : Blo 912577 1543637 := bbase (se 7 (by rfl) ⟨18089, by rfl⟩ : syracuseStep 1543637 = 36179) (by norm_num)
theorem B3476965 : Blo 912577 3476965 := bbase (se 4 (by rfl) ⟨325965, by rfl⟩ : syracuseStep 3476965 = 651931) (by norm_num)
theorem B5213717 : Blo 912577 5213717 := bbase (se 6 (by rfl) ⟨122196, by rfl⟩ : syracuseStep 5213717 = 244393) (by norm_num)
theorem B1543765 : Blo 912577 1543765 := bbase (se 8 (by rfl) ⟨9045, by rfl⟩ : syracuseStep 1543765 = 18091) (by norm_num)
theorem B1543853 : Blo 912577 1543853 := bbase (se 3 (by rfl) ⟨289472, by rfl⟩ : syracuseStep 1543853 = 578945) (by norm_num)
theorem B3477269 : Blo 912577 3477269 := bbase (se 6 (by rfl) ⟨81498, by rfl⟩ : syracuseStep 3477269 = 162997) (by norm_num)
theorem B1543981 : Blo 912577 1543981 := bbase (se 3 (by rfl) ⟨289496, by rfl⟩ : syracuseStep 1543981 = 578993) (by norm_num)
theorem B3084101 : Blo 912577 3084101 := bbase (se 4 (by rfl) ⟨289134, by rfl⟩ : syracuseStep 3084101 = 578269) (by norm_num)
theorem B1544069 : Blo 912577 1544069 := bbase (se 4 (by rfl) ⟨144756, by rfl⟩ : syracuseStep 1544069 = 289513) (by norm_num)
theorem B6688757 : Blo 912577 6688757 := bbase (se 5 (by rfl) ⟨313535, by rfl⟩ : syracuseStep 6688757 = 627071) (by norm_num)
theorem B1544197 : Blo 912577 1544197 := bbase (se 4 (by rfl) ⟨144768, by rfl⟩ : syracuseStep 1544197 = 289537) (by norm_num)
theorem B1544285 : Blo 912577 1544285 := bbase (se 3 (by rfl) ⟨289553, by rfl⟩ : syracuseStep 1544285 = 579107) (by norm_num)
theorem B2199653 : Blo 912577 2199653 := bbase (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) (by norm_num)
theorem B1544413 : Blo 912577 1544413 := bbase (se 3 (by rfl) ⟨289577, by rfl⟩ : syracuseStep 1544413 = 579155) (by norm_num)
theorem B4624613 : Blo 912577 4624613 := bbase (se 4 (by rfl) ⟨433557, by rfl⟩ : syracuseStep 4624613 = 867115) (by norm_num)
theorem B3084533 : Blo 912577 3084533 := bbase (se 5 (by rfl) ⟨144587, by rfl⟩ : syracuseStep 3084533 = 289175) (by norm_num)
theorem B2199845 : Blo 912577 2199845 := bbase (se 4 (by rfl) ⟨206235, by rfl⟩ : syracuseStep 2199845 = 412471) (by norm_num)
theorem B1544501 : Blo 912577 1544501 := bbase (se 5 (by rfl) ⟨72398, by rfl⟩ : syracuseStep 1544501 = 144797) (by norm_num)
theorem B3379589 : Blo 912577 3379589 := bbase (se 4 (by rfl) ⟨316836, by rfl⟩ : syracuseStep 3379589 = 633673) (by norm_num)
theorem B1544629 : Blo 912577 1544629 := bbase (se 5 (by rfl) ⟨72404, by rfl⟩ : syracuseStep 1544629 = 144809) (by norm_num)
theorem B1544717 : Blo 912577 1544717 := bbase (se 3 (by rfl) ⟨289634, by rfl⟩ : syracuseStep 1544717 = 579269) (by norm_num)
theorem B1544845 : Blo 912577 1544845 := bbase (se 3 (by rfl) ⟨289658, by rfl⟩ : syracuseStep 1544845 = 579317) (by norm_num)
theorem B3084965 : Blo 912577 3084965 := bbase (se 4 (by rfl) ⟨289215, by rfl⟩ : syracuseStep 3084965 = 578431) (by norm_num)
theorem B5214901 : Blo 912577 5214901 := bbase (se 5 (by rfl) ⟨244448, by rfl⟩ : syracuseStep 5214901 = 488897) (by norm_num)
theorem B1544933 : Blo 912577 1544933 := bbase (se 4 (by rfl) ⟨144837, by rfl⟩ : syracuseStep 1544933 = 289675) (by norm_num)
theorem B1545061 : Blo 912577 1545061 := bbase (se 4 (by rfl) ⟨144849, by rfl⟩ : syracuseStep 1545061 = 289699) (by norm_num)
theorem B2003837 : Blo 912577 2003837 := bbase (se 3 (by rfl) ⟨375719, by rfl⟩ : syracuseStep 2003837 = 751439) (by norm_num)
theorem B1545149 : Blo 912577 1545149 := bbase (se 3 (by rfl) ⟨289715, by rfl⟩ : syracuseStep 1545149 = 579431) (by norm_num)
theorem B988157 : Blo 912577 988157 := bbase (se 3 (by rfl) ⟨185279, by rfl⟩ : syracuseStep 988157 = 370559) (by norm_num)
theorem B1545277 : Blo 912577 1545277 := bbase (se 3 (by rfl) ⟨289739, by rfl⟩ : syracuseStep 1545277 = 579479) (by norm_num)
theorem B3085397 : Blo 912577 3085397 := bbase (se 8 (by rfl) ⟨18078, by rfl⟩ : syracuseStep 3085397 = 36157) (by norm_num)
theorem B1545365 : Blo 912577 1545365 := bbase (se 6 (by rfl) ⟨36219, by rfl⟩ : syracuseStep 1545365 = 72439) (by norm_num)
theorem B1742029 : Blo 912577 1742029 := bbase (se 3 (by rfl) ⟨326630, by rfl⟩ : syracuseStep 1742029 = 653261) (by norm_num)
theorem B1545493 : Blo 912577 1545493 := bbase (se 6 (by rfl) ⟨36222, by rfl⟩ : syracuseStep 1545493 = 72445) (by norm_num)
theorem B1545581 : Blo 912577 1545581 := bbase (se 3 (by rfl) ⟨289796, by rfl⟩ : syracuseStep 1545581 = 579593) (by norm_num)
theorem B7804309 : Blo 912577 7804309 := bbase (se 6 (by rfl) ⟨182913, by rfl⟩ : syracuseStep 7804309 = 365827) (by norm_num)
theorem B1545709 : Blo 912577 1545709 := bbase (se 3 (by rfl) ⟨289820, by rfl⟩ : syracuseStep 1545709 = 579641) (by norm_num)
theorem B4625909 : Blo 912577 4625909 := bbase (se 5 (by rfl) ⟨216839, by rfl⟩ : syracuseStep 4625909 = 433679) (by norm_num)
theorem B3085829 : Blo 912577 3085829 := bbase (se 4 (by rfl) ⟨289296, by rfl⟩ : syracuseStep 3085829 = 578593) (by norm_num)
theorem B1545797 : Blo 912577 1545797 := bbase (se 4 (by rfl) ⟨144918, by rfl⟩ : syracuseStep 1545797 = 289837) (by norm_num)
theorem B1545925 : Blo 912577 1545925 := bbase (se 4 (by rfl) ⟨144930, by rfl⟩ : syracuseStep 1545925 = 289861) (by norm_num)
theorem B1546013 : Blo 912577 1546013 := bbase (se 3 (by rfl) ⟨289877, by rfl⟩ : syracuseStep 1546013 = 579755) (by norm_num)
theorem B2201413 : Blo 912577 2201413 := bbase (se 4 (by rfl) ⟨206382, by rfl⟩ : syracuseStep 2201413 = 412765) (by norm_num)
theorem B3479381 : Blo 912577 3479381 := bbase (se 9 (by rfl) ⟨10193, by rfl⟩ : syracuseStep 3479381 = 20387) (by norm_num)
theorem B1546141 : Blo 912577 1546141 := bbase (se 3 (by rfl) ⟨289901, by rfl⟩ : syracuseStep 1546141 = 579803) (by norm_num)
theorem B3086261 : Blo 912577 3086261 := bbase (se 5 (by rfl) ⟨144668, by rfl⟩ : syracuseStep 3086261 = 289337) (by norm_num)
theorem B1546229 : Blo 912577 1546229 := bbase (se 5 (by rfl) ⟨72479, by rfl⟩ : syracuseStep 1546229 = 144959) (by norm_num)
theorem B1644565 : Blo 912577 1644565 := bbase (se 6 (by rfl) ⟨38544, by rfl⟩ : syracuseStep 1644565 = 77089) (by norm_num)
theorem B3708965 : Blo 912577 3708965 := bbase (se 4 (by rfl) ⟨347715, by rfl⟩ : syracuseStep 3708965 = 695431) (by norm_num)
theorem B12064853 : Blo 912577 12064853 := bbase (se 8 (by rfl) ⟨70692, by rfl⟩ : syracuseStep 12064853 = 141385) (by norm_num)
theorem B1546357 : Blo 912577 1546357 := bbase (se 5 (by rfl) ⟨72485, by rfl⟩ : syracuseStep 1546357 = 144971) (by norm_num)
theorem B3479669 : Blo 912577 3479669 := bbase (se 5 (by rfl) ⟨163109, by rfl⟩ : syracuseStep 3479669 = 326219) (by norm_num)
theorem B3709093 : Blo 912577 3709093 := bbase (se 4 (by rfl) ⟨347727, by rfl⟩ : syracuseStep 3709093 = 695455) (by norm_num)
theorem B1054909 : Blo 912577 1054909 := bbase (se 3 (by rfl) ⟨197795, by rfl⟩ : syracuseStep 1054909 = 395591) (by norm_num)
theorem B1546445 : Blo 912577 1546445 := bbase (se 3 (by rfl) ⟨289958, by rfl⟩ : syracuseStep 1546445 = 579917) (by norm_num)
theorem B1546573 : Blo 912577 1546573 := bbase (se 3 (by rfl) ⟨289982, by rfl⟩ : syracuseStep 1546573 = 579965) (by norm_num)
theorem B3086693 : Blo 912577 3086693 := bbase (se 4 (by rfl) ⟨289377, by rfl⟩ : syracuseStep 3086693 = 578755) (by norm_num)
theorem B1546661 : Blo 912577 1546661 := bbase (se 4 (by rfl) ⟨144999, by rfl⟩ : syracuseStep 1546661 = 289999) (by norm_num)
theorem B2202029 : Blo 912577 2202029 := bbase (se 3 (by rfl) ⟨412880, by rfl⟩ : syracuseStep 2202029 = 825761) (by norm_num)
theorem B5216885 : Blo 912577 5216885 := bbase (se 5 (by rfl) ⟨244541, by rfl⟩ : syracuseStep 5216885 = 489083) (by norm_num)
theorem B5872277 : Blo 912577 5872277 := bbase (se 6 (by rfl) ⟨137631, by rfl⟩ : syracuseStep 5872277 = 275263) (by norm_num)
theorem B4627205 : Blo 912577 4627205 := bbase (se 4 (by rfl) ⟨433800, by rfl⟩ : syracuseStep 4627205 = 867601) (by norm_num)
theorem B3087125 : Blo 912577 3087125 := bbase (se 6 (by rfl) ⟨72354, by rfl⟩ : syracuseStep 3087125 = 144709) (by norm_num)
theorem B1645357 : Blo 912577 1645357 := bbase (se 3 (by rfl) ⟨308504, by rfl⟩ : syracuseStep 1645357 = 617009) (by norm_num)
theorem B1645373 : Blo 912577 1645373 := bbase (se 3 (by rfl) ⟨308507, by rfl⟩ : syracuseStep 1645373 = 617015) (by norm_num)
theorem B1645589 : Blo 912577 1645589 := bbase (se 6 (by rfl) ⟨38568, by rfl⟩ : syracuseStep 1645589 = 77137) (by norm_num)
theorem B1645733 : Blo 912577 1645733 := bbase (se 4 (by rfl) ⟨154287, by rfl⟩ : syracuseStep 1645733 = 308575) (by norm_num)
theorem B4168901 : Blo 912577 4168901 := bbase (se 4 (by rfl) ⟨390834, by rfl⟩ : syracuseStep 4168901 = 781669) (by norm_num)
theorem B3087557 : Blo 912577 3087557 := bbase (se 4 (by rfl) ⟨289458, by rfl⟩ : syracuseStep 3087557 = 578917) (by norm_num)
theorem B7806293 : Blo 912577 7806293 := bbase (se 11 (by rfl) ⟨5717, by rfl⟩ : syracuseStep 7806293 = 11435) (by norm_num)
theorem B3907061 : Blo 912577 3907061 := bbase (se 5 (by rfl) ⟨183143, by rfl⟩ : syracuseStep 3907061 = 366287) (by norm_num)
theorem B3087989 : Blo 912577 3087989 := bbase (se 5 (by rfl) ⟨144749, by rfl⟩ : syracuseStep 3087989 = 289499) (by norm_num)
theorem B3907349 : Blo 912577 3907349 := bbase (se 6 (by rfl) ⟨91578, by rfl⟩ : syracuseStep 3907349 = 183157) (by norm_num)
theorem B1646453 : Blo 912577 1646453 := bbase (se 5 (by rfl) ⟨77177, by rfl⟩ : syracuseStep 1646453 = 154355) (by norm_num)
theorem B1056629 : Blo 912577 1056629 := bbase (se 5 (by rfl) ⟨49529, by rfl⟩ : syracuseStep 1056629 = 99059) (by norm_num)
theorem B1154989 : Blo 912577 1154989 := bbase (se 3 (by rfl) ⟨216560, by rfl⟩ : syracuseStep 1154989 = 433121) (by norm_num)
theorem B925705 : Blo 912577 925705 := bbase (se 2 (by rfl) ⟨347139, by rfl⟩ : syracuseStep 925705 = 694279) (by norm_num)
theorem B4628501 : Blo 912577 4628501 := bbase (se 6 (by rfl) ⟨108480, by rfl⟩ : syracuseStep 4628501 = 216961) (by norm_num)
theorem B3088421 : Blo 912577 3088421 := bbase (se 4 (by rfl) ⟨289539, by rfl⟩ : syracuseStep 3088421 = 579079) (by norm_num)
theorem B1155161 : Blo 912577 1155161 := bbase (se 2 (by rfl) ⟨433185, by rfl⟩ : syracuseStep 1155161 = 866371) (by norm_num)
theorem B1155217 : Blo 912577 1155217 := bbase (se 2 (by rfl) ⟨433206, by rfl⟩ : syracuseStep 1155217 = 866413) (by norm_num)
theorem B1646741 : Blo 912577 1646741 := bbase (se 6 (by rfl) ⟨38595, by rfl⟩ : syracuseStep 1646741 = 77191) (by norm_num)
theorem B8331445 : Blo 912577 8331445 := bbase (se 5 (by rfl) ⟨390536, by rfl⟩ : syracuseStep 8331445 = 781073) (by norm_num)
theorem B1155313 : Blo 912577 1155313 := bbase (se 2 (by rfl) ⟨433242, by rfl⟩ : syracuseStep 1155313 = 866485) (by norm_num)
theorem B926041 : Blo 912577 926041 := bbase (se 2 (by rfl) ⟨347265, by rfl⟩ : syracuseStep 926041 = 694531) (by norm_num)
theorem B1155485 : Blo 912577 1155485 := bbase (se 3 (by rfl) ⟨216653, by rfl⟩ : syracuseStep 1155485 = 433307) (by norm_num)
theorem B1155541 : Blo 912577 1155541 := bbase (se 7 (by rfl) ⟨13541, by rfl⟩ : syracuseStep 1155541 = 27083) (by norm_num)
theorem B3088853 : Blo 912577 3088853 := bbase (se 7 (by rfl) ⟨36197, by rfl⟩ : syracuseStep 3088853 = 72395) (by norm_num)
theorem B3908101 : Blo 912577 3908101 := bbase (se 4 (by rfl) ⟨366384, by rfl⟩ : syracuseStep 3908101 = 732769) (by norm_num)
theorem B1155637 : Blo 912577 1155637 := bbase (se 5 (by rfl) ⟨54170, by rfl⟩ : syracuseStep 1155637 = 108341) (by norm_num)
theorem B926357 : Blo 912577 926357 := bbase (se 6 (by rfl) ⟨21711, by rfl⟩ : syracuseStep 926357 = 43423) (by norm_num)
theorem B11870869 : Blo 912577 11870869 := bbase (se 6 (by rfl) ⟨278223, by rfl⟩ : syracuseStep 11870869 = 556447) (by norm_num)
theorem B926389 : Blo 912577 926389 := bbase (se 5 (by rfl) ⟨43424, by rfl⟩ : syracuseStep 926389 = 86849) (by norm_num)
theorem B1155809 : Blo 912577 1155809 := bbase (se 2 (by rfl) ⟨433428, by rfl⟩ : syracuseStep 1155809 = 866857) (by norm_num)
theorem B1057517 : Blo 912577 1057517 := bbase (se 3 (by rfl) ⟨198284, by rfl⟩ : syracuseStep 1057517 = 396569) (by norm_num)
theorem B5219093 : Blo 912577 5219093 := bbase (se 6 (by rfl) ⟨122322, by rfl⟩ : syracuseStep 5219093 = 244645) (by norm_num)
theorem B1155865 : Blo 912577 1155865 := bbase (se 2 (by rfl) ⟨433449, by rfl⟩ : syracuseStep 1155865 = 866899) (by norm_num)
theorem B1155961 : Blo 912577 1155961 := bbase (se 2 (by rfl) ⟨433485, by rfl⟩ : syracuseStep 1155961 = 866971) (by norm_num)
theorem B1254269 : Blo 912577 1254269 := bbase (se 3 (by rfl) ⟨235175, by rfl⟩ : syracuseStep 1254269 = 470351) (by norm_num)
theorem B3089285 : Blo 912577 3089285 := bbase (se 4 (by rfl) ⟨289620, by rfl⟩ : syracuseStep 3089285 = 579241) (by norm_num)
theorem B1156133 : Blo 912577 1156133 := bbase (se 4 (by rfl) ⟨108387, by rfl⟩ : syracuseStep 1156133 = 216775) (by norm_num)
theorem B6956117 : Blo 912577 6956117 := bbase (se 8 (by rfl) ⟨40758, by rfl⟩ : syracuseStep 6956117 = 81517) (by norm_num)
theorem B1156189 : Blo 912577 1156189 := bbase (se 3 (by rfl) ⟨216785, by rfl⟩ : syracuseStep 1156189 = 433571) (by norm_num)
theorem B1156285 : Blo 912577 1156285 := bbase (se 3 (by rfl) ⟨216803, by rfl⟩ : syracuseStep 1156285 = 433607) (by norm_num)
theorem B3122405 : Blo 912577 3122405 := bbase (se 4 (by rfl) ⟨292725, by rfl⟩ : syracuseStep 3122405 = 585451) (by norm_num)
theorem B3908837 : Blo 912577 3908837 := bbase (se 4 (by rfl) ⟨366453, by rfl⟩ : syracuseStep 3908837 = 732907) (by norm_num)
theorem B1254637 : Blo 912577 1254637 := bbase (se 3 (by rfl) ⟨235244, by rfl⟩ : syracuseStep 1254637 = 470489) (by norm_num)
theorem B4629797 : Blo 912577 4629797 := bbase (se 4 (by rfl) ⟨434043, by rfl⟩ : syracuseStep 4629797 = 868087) (by norm_num)
theorem B3089717 : Blo 912577 3089717 := bbase (se 5 (by rfl) ⟨144830, by rfl⟩ : syracuseStep 3089717 = 289661) (by norm_num)
theorem B1156457 : Blo 912577 1156457 := bbase (se 2 (by rfl) ⟨433671, by rfl⟩ : syracuseStep 1156457 = 867343) (by norm_num)
theorem B1156513 : Blo 912577 1156513 := bbase (se 2 (by rfl) ⟨433692, by rfl⟩ : syracuseStep 1156513 = 867385) (by norm_num)
theorem B927217 : Blo 912577 927217 := bbase (se 2 (by rfl) ⟨347706, by rfl⟩ : syracuseStep 927217 = 695413) (by norm_num)
theorem B1156609 : Blo 912577 1156609 := bbase (se 2 (by rfl) ⟨433728, by rfl⟩ : syracuseStep 1156609 = 867457) (by norm_num)
theorem B1156781 : Blo 912577 1156781 := bbase (se 3 (by rfl) ⟨216896, by rfl⟩ : syracuseStep 1156781 = 433793) (by norm_num)
theorem B2926309 : Blo 912577 2926309 := bbase (se 4 (by rfl) ⟨274341, by rfl⟩ : syracuseStep 2926309 = 548683) (by norm_num)
theorem B1156837 : Blo 912577 1156837 := bbase (se 4 (by rfl) ⟨108453, by rfl⟩ : syracuseStep 1156837 = 216907) (by norm_num)
theorem B3090149 : Blo 912577 3090149 := bbase (se 4 (by rfl) ⟨289701, by rfl⟩ : syracuseStep 3090149 = 579403) (by norm_num)
theorem B1156933 : Blo 912577 1156933 := bbase (se 4 (by rfl) ⟨108462, by rfl⟩ : syracuseStep 1156933 = 216925) (by norm_num)
theorem B3123173 : Blo 912577 3123173 := bbase (se 4 (by rfl) ⟨292797, by rfl⟩ : syracuseStep 3123173 = 585595) (by norm_num)
theorem B1157105 : Blo 912577 1157105 := bbase (se 2 (by rfl) ⟨433914, by rfl⟩ : syracuseStep 1157105 = 867829) (by norm_num)
theorem B1157161 : Blo 912577 1157161 := bbase (se 2 (by rfl) ⟨433935, by rfl⟩ : syracuseStep 1157161 = 867871) (by norm_num)
theorem B1157257 : Blo 912577 1157257 := bbase (se 2 (by rfl) ⟨433971, by rfl⟩ : syracuseStep 1157257 = 867943) (by norm_num)
theorem B3090581 : Blo 912577 3090581 := bbase (se 6 (by rfl) ⟨72435, by rfl⟩ : syracuseStep 3090581 = 144871) (by norm_num)
theorem B1976557 : Blo 912577 1976557 := bbase (se 3 (by rfl) ⟨370604, by rfl⟩ : syracuseStep 1976557 = 741209) (by norm_num)
theorem B1157429 : Blo 912577 1157429 := bbase (se 5 (by rfl) ⟨54254, by rfl⟩ : syracuseStep 1157429 = 108509) (by norm_num)
theorem B1157485 : Blo 912577 1157485 := bbase (se 3 (by rfl) ⟨217028, by rfl⟩ : syracuseStep 1157485 = 434057) (by norm_num)
theorem B1157581 : Blo 912577 1157581 := bbase (se 3 (by rfl) ⟨217046, by rfl⟩ : syracuseStep 1157581 = 434093) (by norm_num)
theorem B4631093 : Blo 912577 4631093 := bbase (se 5 (by rfl) ⟨217082, by rfl⟩ : syracuseStep 4631093 = 434165) (by norm_num)
theorem B3091013 : Blo 912577 3091013 := bbase (se 4 (by rfl) ⟨289782, by rfl⟩ : syracuseStep 3091013 = 579565) (by norm_num)
theorem B1026661 : Blo 912577 1026661 := bbase (se 4 (by rfl) ⟨96249, by rfl⟩ : syracuseStep 1026661 = 192499) (by norm_num)
theorem B1157753 : Blo 912577 1157753 := bbase (se 2 (by rfl) ⟨434157, by rfl⟩ : syracuseStep 1157753 = 868315) (by norm_num)
theorem B1026697 : Blo 912577 1026697 := bbase (se 2 (by rfl) ⟨385011, by rfl⟩ : syracuseStep 1026697 = 770023) (by norm_num)
theorem B1026733 : Blo 912577 1026733 := bbase (se 3 (by rfl) ⟨192512, by rfl⟩ : syracuseStep 1026733 = 385025) (by norm_num)
theorem B1157809 : Blo 912577 1157809 := bbase (se 2 (by rfl) ⟨434178, by rfl⟩ : syracuseStep 1157809 = 868357) (by norm_num)
theorem B928433 : Blo 912577 928433 := bbase (se 2 (by rfl) ⟨348162, by rfl⟩ : syracuseStep 928433 = 696325) (by norm_num)
theorem B1026769 : Blo 912577 1026769 := bbase (se 2 (by rfl) ⟨385038, by rfl⟩ : syracuseStep 1026769 = 770077) (by norm_num)
theorem B3517141 : Blo 912577 3517141 := bbase (se 7 (by rfl) ⟨41216, by rfl⟩ : syracuseStep 3517141 = 82433) (by norm_num)
theorem B1026805 : Blo 912577 1026805 := bbase (se 5 (by rfl) ⟨48131, by rfl⟩ : syracuseStep 1026805 = 96263) (by norm_num)
theorem B1157905 : Blo 912577 1157905 := bbase (se 2 (by rfl) ⟨434214, by rfl⟩ : syracuseStep 1157905 = 868429) (by norm_num)
theorem B1026841 : Blo 912577 1026841 := bbase (se 2 (by rfl) ⟨385065, by rfl⟩ : syracuseStep 1026841 = 770131) (by norm_num)
theorem B1026877 : Blo 912577 1026877 := bbase (se 3 (by rfl) ⟨192539, by rfl⟩ : syracuseStep 1026877 = 385079) (by norm_num)
theorem B1026913 : Blo 912577 1026913 := bbase (se 2 (by rfl) ⟨385092, by rfl⟩ : syracuseStep 1026913 = 770185) (by norm_num)
theorem B1026949 : Blo 912577 1026949 := bbase (se 4 (by rfl) ⟨96276, by rfl⟩ : syracuseStep 1026949 = 192553) (by norm_num)
theorem B1026985 : Blo 912577 1026985 := bbase (se 2 (by rfl) ⟨385119, by rfl⟩ : syracuseStep 1026985 = 770239) (by norm_num)
theorem B1158077 : Blo 912577 1158077 := bbase (se 3 (by rfl) ⟨217139, by rfl⟩ : syracuseStep 1158077 = 434279) (by norm_num)
theorem B2599877 : Blo 912577 2599877 := bbase (se 4 (by rfl) ⟨243738, by rfl⟩ : syracuseStep 2599877 = 487477) (by norm_num)
theorem B1027021 : Blo 912577 1027021 := bbase (se 3 (by rfl) ⟨192566, by rfl⟩ : syracuseStep 1027021 = 385133) (by norm_num)
theorem B1027057 : Blo 912577 1027057 := bbase (se 2 (by rfl) ⟨385146, by rfl⟩ : syracuseStep 1027057 = 770293) (by norm_num)
theorem B2501621 : Blo 912577 2501621 := bbase (se 5 (by rfl) ⟨117263, by rfl⟩ : syracuseStep 2501621 = 234527) (by norm_num)
theorem B1158133 : Blo 912577 1158133 := bbase (se 5 (by rfl) ⟨54287, by rfl⟩ : syracuseStep 1158133 = 108575) (by norm_num)
theorem B3091445 : Blo 912577 3091445 := bbase (se 5 (by rfl) ⟨144911, by rfl⟩ : syracuseStep 3091445 = 289823) (by norm_num)
theorem B1027093 : Blo 912577 1027093 := bbase (se 6 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 1027093 = 48145) (by norm_num)
theorem B1027129 : Blo 912577 1027129 := bbase (se 2 (by rfl) ⟨385173, by rfl⟩ : syracuseStep 1027129 = 770347) (by norm_num)
theorem B1158229 : Blo 912577 1158229 := bbase (se 8 (by rfl) ⟨6786, by rfl⟩ : syracuseStep 1158229 = 13573) (by norm_num)
theorem B1027165 : Blo 912577 1027165 := bbase (se 3 (by rfl) ⟨192593, by rfl⟩ : syracuseStep 1027165 = 385187) (by norm_num)
theorem B1027201 : Blo 912577 1027201 := bbase (se 2 (by rfl) ⟨385200, by rfl⟩ : syracuseStep 1027201 = 770401) (by norm_num)
theorem B1027237 : Blo 912577 1027237 := bbase (se 4 (by rfl) ⟨96303, by rfl⟩ : syracuseStep 1027237 = 192607) (by norm_num)
theorem B1027273 : Blo 912577 1027273 := bbase (se 2 (by rfl) ⟨385227, by rfl⟩ : syracuseStep 1027273 = 770455) (by norm_num)
theorem B1027309 : Blo 912577 1027309 := bbase (se 3 (by rfl) ⟨192620, by rfl⟩ : syracuseStep 1027309 = 385241) (by norm_num)
theorem B4402421 : Blo 912577 4402421 := bbase (se 5 (by rfl) ⟨206363, by rfl⟩ : syracuseStep 4402421 = 412727) (by norm_num)
theorem B929017 : Blo 912577 929017 := bbase (se 2 (by rfl) ⟨348381, by rfl⟩ : syracuseStep 929017 = 696763) (by norm_num)
theorem B1158401 : Blo 912577 1158401 := bbase (se 2 (by rfl) ⟨434400, by rfl⟩ : syracuseStep 1158401 = 868801) (by norm_num)
theorem B1027345 : Blo 912577 1027345 := bbase (se 2 (by rfl) ⟨385254, by rfl⟩ : syracuseStep 1027345 = 770509) (by norm_num)
theorem B1027381 : Blo 912577 1027381 := bbase (se 5 (by rfl) ⟨48158, by rfl⟩ : syracuseStep 1027381 = 96317) (by norm_num)
theorem B1158457 : Blo 912577 1158457 := bbase (se 2 (by rfl) ⟨434421, by rfl⟩ : syracuseStep 1158457 = 868843) (by norm_num)
theorem B1027417 : Blo 912577 1027417 := bbase (se 2 (by rfl) ⟨385281, by rfl⟩ : syracuseStep 1027417 = 770563) (by norm_num)
theorem B1027453 : Blo 912577 1027453 := bbase (se 3 (by rfl) ⟨192647, by rfl⟩ : syracuseStep 1027453 = 385295) (by norm_num)
theorem B1158553 : Blo 912577 1158553 := bbase (se 2 (by rfl) ⟨434457, by rfl⟩ : syracuseStep 1158553 = 868915) (by norm_num)
theorem B1027489 : Blo 912577 1027489 := bbase (se 2 (by rfl) ⟨385308, by rfl⟩ : syracuseStep 1027489 = 770617) (by norm_num)
theorem B3091877 : Blo 912577 3091877 := bbase (se 4 (by rfl) ⟨289863, by rfl⟩ : syracuseStep 3091877 = 579727) (by norm_num)
theorem B3517877 : Blo 912577 3517877 := bbase (se 5 (by rfl) ⟨164900, by rfl⟩ : syracuseStep 3517877 = 329801) (by norm_num)
theorem B4402613 : Blo 912577 4402613 := bbase (se 5 (by rfl) ⟨206372, by rfl⟩ : syracuseStep 4402613 = 412745) (by norm_num)
theorem B1027525 : Blo 912577 1027525 := bbase (se 4 (by rfl) ⟨96330, by rfl⟩ : syracuseStep 1027525 = 192661) (by norm_num)
theorem B1027561 : Blo 912577 1027561 := bbase (se 2 (by rfl) ⟨385335, by rfl⟩ : syracuseStep 1027561 = 770671) (by norm_num)
theorem B1027597 : Blo 912577 1027597 := bbase (se 3 (by rfl) ⟨192674, by rfl⟩ : syracuseStep 1027597 = 385349) (by norm_num)
theorem B1027633 : Blo 912577 1027633 := bbase (se 2 (by rfl) ⟨385362, by rfl⟩ : syracuseStep 1027633 = 770725) (by norm_num)
theorem B1158725 : Blo 912577 1158725 := bbase (se 4 (by rfl) ⟨108630, by rfl⟩ : syracuseStep 1158725 = 217261) (by norm_num)
theorem B1027669 : Blo 912577 1027669 := bbase (se 8 (by rfl) ⟨6021, by rfl⟩ : syracuseStep 1027669 = 12043) (by norm_num)
theorem B1977941 : Blo 912577 1977941 := bbase (se 8 (by rfl) ⟨11589, by rfl⟩ : syracuseStep 1977941 = 23179) (by norm_num)
theorem B2600549 : Blo 912577 2600549 := bbase (se 4 (by rfl) ⟨243801, by rfl⟩ : syracuseStep 2600549 = 487603) (by norm_num)
theorem B1027705 : Blo 912577 1027705 := bbase (se 2 (by rfl) ⟨385389, by rfl⟩ : syracuseStep 1027705 = 770779) (by norm_num)
theorem B1158781 : Blo 912577 1158781 := bbase (se 3 (by rfl) ⟨217271, by rfl⟩ : syracuseStep 1158781 = 434543) (by norm_num)
theorem B1027741 : Blo 912577 1027741 := bbase (se 3 (by rfl) ⟨192701, by rfl⟩ : syracuseStep 1027741 = 385403) (by norm_num)
theorem B1027777 : Blo 912577 1027777 := bbase (se 2 (by rfl) ⟨385416, by rfl⟩ : syracuseStep 1027777 = 770833) (by norm_num)
theorem B1158877 : Blo 912577 1158877 := bbase (se 3 (by rfl) ⟨217289, by rfl⟩ : syracuseStep 1158877 = 434579) (by norm_num)
theorem B1027813 : Blo 912577 1027813 := bbase (se 4 (by rfl) ⟨96357, by rfl⟩ : syracuseStep 1027813 = 192715) (by norm_num)
theorem B8793845 : Blo 912577 8793845 := bbase (se 5 (by rfl) ⟨412211, by rfl⟩ : syracuseStep 8793845 = 824423) (by norm_num)
theorem B1027849 : Blo 912577 1027849 := bbase (se 2 (by rfl) ⟨385443, by rfl⟩ : syracuseStep 1027849 = 770887) (by norm_num)
theorem B1027885 : Blo 912577 1027885 := bbase (se 3 (by rfl) ⟨192728, by rfl⟩ : syracuseStep 1027885 = 385457) (by norm_num)
theorem B4402997 : Blo 912577 4402997 := bbase (se 5 (by rfl) ⟨206390, by rfl⟩ : syracuseStep 4402997 = 412781) (by norm_num)
theorem B4632389 : Blo 912577 4632389 := bbase (se 4 (by rfl) ⟨434286, by rfl⟩ : syracuseStep 4632389 = 868573) (by norm_num)
theorem B1027921 : Blo 912577 1027921 := bbase (se 2 (by rfl) ⟨385470, by rfl⟩ : syracuseStep 1027921 = 770941) (by norm_num)
theorem B3092309 : Blo 912577 3092309 := bbase (se 9 (by rfl) ⟨9059, by rfl⟩ : syracuseStep 3092309 = 18119) (by norm_num)
theorem B3518309 : Blo 912577 3518309 := bbase (se 4 (by rfl) ⟨329841, by rfl⟩ : syracuseStep 3518309 = 659683) (by norm_num)
theorem B1027957 : Blo 912577 1027957 := bbase (se 5 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 1027957 = 96371) (by norm_num)
theorem B1159049 : Blo 912577 1159049 := bbase (se 2 (by rfl) ⟨434643, by rfl⟩ : syracuseStep 1159049 = 869287) (by norm_num)
theorem B1027993 : Blo 912577 1027993 := bbase (se 2 (by rfl) ⟨385497, by rfl⟩ : syracuseStep 1027993 = 770995) (by norm_num)
theorem B1028029 : Blo 912577 1028029 := bbase (se 3 (by rfl) ⟨192755, by rfl⟩ : syracuseStep 1028029 = 385511) (by norm_num)
theorem B1159105 : Blo 912577 1159105 := bbase (se 2 (by rfl) ⟨434664, by rfl⟩ : syracuseStep 1159105 = 869329) (by norm_num)
theorem B3715013 : Blo 912577 3715013 := bbase (se 4 (by rfl) ⟨348282, by rfl⟩ : syracuseStep 3715013 = 696565) (by norm_num)
theorem B1028065 : Blo 912577 1028065 := bbase (se 2 (by rfl) ⟨385524, by rfl⟩ : syracuseStep 1028065 = 771049) (by norm_num)
theorem B1028101 : Blo 912577 1028101 := bbase (se 4 (by rfl) ⟨96384, by rfl⟩ : syracuseStep 1028101 = 192769) (by norm_num)
theorem B2600981 : Blo 912577 2600981 := bbase (se 6 (by rfl) ⟨60960, by rfl⟩ : syracuseStep 2600981 = 121921) (by norm_num)
theorem B1159201 : Blo 912577 1159201 := bbase (se 2 (by rfl) ⟨434700, by rfl⟩ : syracuseStep 1159201 = 869401) (by norm_num)
theorem B1028137 : Blo 912577 1028137 := bbase (se 2 (by rfl) ⟨385551, by rfl⟩ : syracuseStep 1028137 = 771103) (by norm_num)
theorem B1028173 : Blo 912577 1028173 := bbase (se 3 (by rfl) ⟨192782, by rfl⟩ : syracuseStep 1028173 = 385565) (by norm_num)
theorem B1028209 : Blo 912577 1028209 := bbase (se 2 (by rfl) ⟨385578, by rfl⟩ : syracuseStep 1028209 = 771157) (by norm_num)
theorem B1028245 : Blo 912577 1028245 := bbase (se 6 (by rfl) ⟨24099, by rfl⟩ : syracuseStep 1028245 = 48199) (by norm_num)
theorem B1028281 : Blo 912577 1028281 := bbase (se 2 (by rfl) ⟨385605, by rfl⟩ : syracuseStep 1028281 = 771211) (by norm_num)
theorem B1159373 : Blo 912577 1159373 := bbase (se 3 (by rfl) ⟨217382, by rfl⟩ : syracuseStep 1159373 = 434765) (by norm_num)
theorem B1028317 : Blo 912577 1028317 := bbase (se 3 (by rfl) ⟨192809, by rfl⟩ : syracuseStep 1028317 = 385619) (by norm_num)
theorem B1028353 : Blo 912577 1028353 := bbase (se 2 (by rfl) ⟨385632, by rfl⟩ : syracuseStep 1028353 = 771265) (by norm_num)
theorem B1159429 : Blo 912577 1159429 := bbase (se 4 (by rfl) ⟨108696, by rfl⟩ : syracuseStep 1159429 = 217393) (by norm_num)
theorem B3092741 : Blo 912577 3092741 := bbase (se 4 (by rfl) ⟨289944, by rfl⟩ : syracuseStep 3092741 = 579889) (by norm_num)
theorem B1028389 : Blo 912577 1028389 := bbase (se 4 (by rfl) ⟨96411, by rfl⟩ : syracuseStep 1028389 = 192823) (by norm_num)
theorem B1028425 : Blo 912577 1028425 := bbase (se 2 (by rfl) ⟨385659, by rfl⟩ : syracuseStep 1028425 = 771319) (by norm_num)
theorem B1651037 : Blo 912577 1651037 := bbase (se 3 (by rfl) ⟨309569, by rfl⟩ : syracuseStep 1651037 = 619139) (by norm_num)
theorem B1159525 : Blo 912577 1159525 := bbase (se 4 (by rfl) ⟨108705, by rfl⟩ : syracuseStep 1159525 = 217411) (by norm_num)
theorem B1028461 : Blo 912577 1028461 := bbase (se 3 (by rfl) ⟨192836, by rfl⟩ : syracuseStep 1028461 = 385673) (by norm_num)
theorem B1028497 : Blo 912577 1028497 := bbase (se 2 (by rfl) ⟨385686, by rfl⟩ : syracuseStep 1028497 = 771373) (by norm_num)
theorem B1028533 : Blo 912577 1028533 := bbase (se 5 (by rfl) ⟨48212, by rfl⟩ : syracuseStep 1028533 = 96425) (by norm_num)
theorem B3912133 : Blo 912577 3912133 := bbase (se 4 (by rfl) ⟨366762, by rfl⟩ : syracuseStep 3912133 = 733525) (by norm_num)
theorem B1028569 : Blo 912577 1028569 := bbase (se 2 (by rfl) ⟨385713, by rfl⟩ : syracuseStep 1028569 = 771427) (by norm_num)
theorem B1028605 : Blo 912577 1028605 := bbase (se 3 (by rfl) ⟨192863, by rfl⟩ : syracuseStep 1028605 = 385727) (by norm_num)
theorem B1159697 : Blo 912577 1159697 := bbase (se 2 (by rfl) ⟨434886, by rfl⟩ : syracuseStep 1159697 = 869773) (by norm_num)
theorem B1028641 : Blo 912577 1028641 := bbase (se 2 (by rfl) ⟨385740, by rfl⟩ : syracuseStep 1028641 = 771481) (by norm_num)
theorem B1028677 : Blo 912577 1028677 := bbase (se 4 (by rfl) ⟨96438, by rfl⟩ : syracuseStep 1028677 = 192877) (by norm_num)
theorem B1159753 : Blo 912577 1159753 := bbase (se 2 (by rfl) ⟨434907, by rfl⟩ : syracuseStep 1159753 = 869815) (by norm_num)
theorem B1028713 : Blo 912577 1028713 := bbase (se 2 (by rfl) ⟨385767, by rfl⟩ : syracuseStep 1028713 = 771535) (by norm_num)
theorem B1487477 : Blo 912577 1487477 := bbase (se 5 (by rfl) ⟨69725, by rfl⟩ : syracuseStep 1487477 = 139451) (by norm_num)
theorem B1028749 : Blo 912577 1028749 := bbase (se 3 (by rfl) ⟨192890, by rfl⟩ : syracuseStep 1028749 = 385781) (by norm_num)
theorem B1159849 : Blo 912577 1159849 := bbase (se 2 (by rfl) ⟨434943, by rfl⟩ : syracuseStep 1159849 = 869887) (by norm_num)
theorem B1028785 : Blo 912577 1028785 := bbase (se 2 (by rfl) ⟨385794, by rfl⟩ : syracuseStep 1028785 = 771589) (by norm_num)
theorem B3093173 : Blo 912577 3093173 := bbase (se 5 (by rfl) ⟨144992, by rfl⟩ : syracuseStep 3093173 = 289985) (by norm_num)
theorem B1389269 : Blo 912577 1389269 := bbase (se 7 (by rfl) ⟨16280, by rfl⟩ : syracuseStep 1389269 = 32561) (by norm_num)
theorem B1028821 : Blo 912577 1028821 := bbase (se 7 (by rfl) ⟨12056, by rfl⟩ : syracuseStep 1028821 = 24113) (by norm_num)
theorem B1028857 : Blo 912577 1028857 := bbase (se 2 (by rfl) ⟨385821, by rfl⟩ : syracuseStep 1028857 = 771643) (by norm_num)
theorem B2601733 : Blo 912577 2601733 := bbase (se 4 (by rfl) ⟨243912, by rfl⟩ : syracuseStep 2601733 = 487825) (by norm_num)
theorem B1028893 : Blo 912577 1028893 := bbase (se 3 (by rfl) ⟨192917, by rfl⟩ : syracuseStep 1028893 = 385835) (by norm_num)
theorem B1028929 : Blo 912577 1028929 := bbase (se 2 (by rfl) ⟨385848, by rfl⟩ : syracuseStep 1028929 = 771697) (by norm_num)
theorem B1160021 : Blo 912577 1160021 := bbase (se 9 (by rfl) ⟨3398, by rfl⟩ : syracuseStep 1160021 = 6797) (by norm_num)
theorem B1028965 : Blo 912577 1028965 := bbase (se 4 (by rfl) ⟨96465, by rfl⟩ : syracuseStep 1028965 = 192931) (by norm_num)
theorem B1029001 : Blo 912577 1029001 := bbase (se 2 (by rfl) ⟨385875, by rfl⟩ : syracuseStep 1029001 = 771751) (by norm_num)
theorem B1029037 : Blo 912577 1029037 := bbase (se 3 (by rfl) ⟨192944, by rfl⟩ : syracuseStep 1029037 = 385889) (by norm_num)
theorem B1029073 : Blo 912577 1029073 := bbase (se 2 (by rfl) ⟨385902, by rfl⟩ : syracuseStep 1029073 = 771805) (by norm_num)
theorem B1029109 : Blo 912577 1029109 := bbase (se 5 (by rfl) ⟨48239, by rfl⟩ : syracuseStep 1029109 = 96479) (by norm_num)
theorem B1029145 : Blo 912577 1029145 := bbase (se 2 (by rfl) ⟨385929, by rfl⟩ : syracuseStep 1029145 = 771859) (by norm_num)
theorem B7025717 : Blo 912577 7025717 := bbase (se 5 (by rfl) ⟨329330, by rfl⟩ : syracuseStep 7025717 = 658661) (by norm_num)
theorem B1029181 : Blo 912577 1029181 := bbase (se 3 (by rfl) ⟨192971, by rfl⟩ : syracuseStep 1029181 = 385943) (by norm_num)
theorem B4633685 : Blo 912577 4633685 := bbase (se 8 (by rfl) ⟨27150, by rfl⟩ : syracuseStep 4633685 = 54301) (by norm_num)
theorem B1029217 : Blo 912577 1029217 := bbase (se 2 (by rfl) ⟨385956, by rfl⟩ : syracuseStep 1029217 = 771913) (by norm_num)
theorem B1029253 : Blo 912577 1029253 := bbase (se 4 (by rfl) ⟨96492, by rfl⟩ : syracuseStep 1029253 = 192985) (by norm_num)
theorem B1389725 : Blo 912577 1389725 := bbase (se 3 (by rfl) ⟨260573, by rfl⟩ : syracuseStep 1389725 = 521147) (by norm_num)
theorem B1029289 : Blo 912577 1029289 := bbase (se 2 (by rfl) ⟨385983, by rfl⟩ : syracuseStep 1029289 = 771967) (by norm_num)
theorem B1029325 : Blo 912577 1029325 := bbase (se 3 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 1029325 = 385997) (by norm_num)
theorem B1029361 : Blo 912577 1029361 := bbase (se 2 (by rfl) ⟨386010, by rfl⟩ : syracuseStep 1029361 = 772021) (by norm_num)
theorem B9385237 : Blo 912577 9385237 := bbase (se 6 (by rfl) ⟨219966, by rfl⟩ : syracuseStep 9385237 = 439933) (by norm_num)
theorem B1029397 : Blo 912577 1029397 := bbase (se 6 (by rfl) ⟨24126, by rfl⟩ : syracuseStep 1029397 = 48253) (by norm_num)
theorem B1029433 : Blo 912577 1029433 := bbase (se 2 (by rfl) ⟨386037, by rfl⟩ : syracuseStep 1029433 = 772075) (by norm_num)
theorem B1029469 : Blo 912577 1029469 := bbase (se 3 (by rfl) ⟨193025, by rfl⟩ : syracuseStep 1029469 = 386051) (by norm_num)
theorem B1029505 : Blo 912577 1029505 := bbase (se 2 (by rfl) ⟨386064, by rfl⟩ : syracuseStep 1029505 = 772129) (by norm_num)
theorem B1029541 : Blo 912577 1029541 := bbase (se 4 (by rfl) ⟨96519, by rfl⟩ : syracuseStep 1029541 = 193039) (by norm_num)
theorem B1029577 : Blo 912577 1029577 := bbase (se 2 (by rfl) ⟨386091, by rfl⟩ : syracuseStep 1029577 = 772183) (by norm_num)
theorem B1029613 : Blo 912577 1029613 := bbase (se 3 (by rfl) ⟨193052, by rfl⟩ : syracuseStep 1029613 = 386105) (by norm_num)
theorem B1029649 : Blo 912577 1029649 := bbase (se 2 (by rfl) ⟨386118, by rfl⟩ : syracuseStep 1029649 = 772237) (by norm_num)
theorem B1029685 : Blo 912577 1029685 := bbase (se 5 (by rfl) ⟨48266, by rfl⟩ : syracuseStep 1029685 = 96533) (by norm_num)
theorem B1029721 : Blo 912577 1029721 := bbase (se 2 (by rfl) ⟨386145, by rfl⟩ : syracuseStep 1029721 = 772291) (by norm_num)
theorem B1029757 : Blo 912577 1029757 := bbase (se 3 (by rfl) ⟨193079, by rfl⟩ : syracuseStep 1029757 = 386159) (by norm_num)
theorem B1029793 : Blo 912577 1029793 := bbase (se 2 (by rfl) ⟨386172, by rfl⟩ : syracuseStep 1029793 = 772345) (by norm_num)
theorem B1029829 : Blo 912577 1029829 := bbase (se 4 (by rfl) ⟨96546, by rfl⟩ : syracuseStep 1029829 = 193093) (by norm_num)
theorem B1029865 : Blo 912577 1029865 := bbase (se 2 (by rfl) ⟨386199, by rfl⟩ : syracuseStep 1029865 = 772399) (by norm_num)
theorem B1029901 : Blo 912577 1029901 := bbase (se 3 (by rfl) ⟨193106, by rfl⟩ : syracuseStep 1029901 = 386213) (by norm_num)
theorem B1029937 : Blo 912577 1029937 := bbase (se 2 (by rfl) ⟨386226, by rfl⟩ : syracuseStep 1029937 = 772453) (by norm_num)
theorem B1029973 : Blo 912577 1029973 := bbase (se 9 (by rfl) ⟨3017, by rfl⟩ : syracuseStep 1029973 = 6035) (by norm_num)
theorem B1030009 : Blo 912577 1030009 := bbase (se 2 (by rfl) ⟨386253, by rfl⟩ : syracuseStep 1030009 = 772507) (by norm_num)
theorem B1030045 : Blo 912577 1030045 := bbase (se 3 (by rfl) ⟨193133, by rfl⟩ : syracuseStep 1030045 = 386267) (by norm_num)
theorem B1030081 : Blo 912577 1030081 := bbase (se 2 (by rfl) ⟨386280, by rfl⟩ : syracuseStep 1030081 = 772561) (by norm_num)
theorem B1030117 : Blo 912577 1030117 := bbase (se 4 (by rfl) ⟨96573, by rfl⟩ : syracuseStep 1030117 = 193147) (by norm_num)
theorem B1030153 : Blo 912577 1030153 := bbase (se 2 (by rfl) ⟨386307, by rfl⟩ : syracuseStep 1030153 = 772615) (by norm_num)
theorem B1030189 : Blo 912577 1030189 := bbase (se 3 (by rfl) ⟨193160, by rfl⟩ : syracuseStep 1030189 = 386321) (by norm_num)
theorem B2472005 : Blo 912577 2472005 := bbase (se 4 (by rfl) ⟨231750, by rfl⟩ : syracuseStep 2472005 = 463501) (by norm_num)
theorem B1030225 : Blo 912577 1030225 := bbase (se 2 (by rfl) ⟨386334, by rfl⟩ : syracuseStep 1030225 = 772669) (by norm_num)
theorem B16660565 : Blo 912577 16660565 := bbase (se 8 (by rfl) ⟨97620, by rfl⟩ : syracuseStep 16660565 = 195241) (by norm_num)
theorem B1030261 : Blo 912577 1030261 := bbase (se 5 (by rfl) ⟨48293, by rfl⟩ : syracuseStep 1030261 = 96587) (by norm_num)
theorem B1030297 : Blo 912577 1030297 := bbase (se 2 (by rfl) ⟨386361, by rfl⟩ : syracuseStep 1030297 = 772723) (by norm_num)
theorem B2472101 : Blo 912577 2472101 := bbase (se 4 (by rfl) ⟨231759, by rfl⟩ : syracuseStep 2472101 = 463519) (by norm_num)
theorem B1030333 : Blo 912577 1030333 := bbase (se 3 (by rfl) ⟨193187, by rfl⟩ : syracuseStep 1030333 = 386375) (by norm_num)
theorem B1030369 : Blo 912577 1030369 := bbase (se 2 (by rfl) ⟨386388, by rfl⟩ : syracuseStep 1030369 = 772777) (by norm_num)
theorem B1128701 : Blo 912577 1128701 := bbase (se 3 (by rfl) ⟨211631, by rfl⟩ : syracuseStep 1128701 = 423263) (by norm_num)
theorem B1030405 : Blo 912577 1030405 := bbase (se 4 (by rfl) ⟨96600, by rfl⟩ : syracuseStep 1030405 = 193201) (by norm_num)
theorem B1030441 : Blo 912577 1030441 := bbase (se 2 (by rfl) ⟨386415, by rfl⟩ : syracuseStep 1030441 = 772831) (by norm_num)
theorem B1030477 : Blo 912577 1030477 := bbase (se 3 (by rfl) ⟨193214, by rfl⟩ : syracuseStep 1030477 = 386429) (by norm_num)
theorem B4634981 : Blo 912577 4634981 := bbase (se 4 (by rfl) ⟨434529, by rfl⟩ : syracuseStep 4634981 = 869059) (by norm_num)
theorem B1030513 : Blo 912577 1030513 := bbase (se 2 (by rfl) ⟨386442, by rfl⟩ : syracuseStep 1030513 = 772885) (by norm_num)
theorem B1030549 : Blo 912577 1030549 := bbase (se 6 (by rfl) ⟨24153, by rfl⟩ : syracuseStep 1030549 = 48307) (by norm_num)
theorem B1030585 : Blo 912577 1030585 := bbase (se 2 (by rfl) ⟨386469, by rfl⟩ : syracuseStep 1030585 = 772939) (by norm_num)
theorem B1030621 : Blo 912577 1030621 := bbase (se 3 (by rfl) ⟨193241, by rfl⟩ : syracuseStep 1030621 = 386483) (by norm_num)
theorem B3291637 : Blo 912577 3291637 := bbase (se 5 (by rfl) ⟨154295, by rfl⟩ : syracuseStep 3291637 = 308591) (by norm_num)
theorem B1030657 : Blo 912577 1030657 := bbase (se 2 (by rfl) ⟨386496, by rfl⟩ : syracuseStep 1030657 = 772993) (by norm_num)
theorem B1391141 : Blo 912577 1391141 := bbase (se 4 (by rfl) ⟨130419, by rfl⟩ : syracuseStep 1391141 = 260839) (by norm_num)
theorem B1030693 : Blo 912577 1030693 := bbase (se 4 (by rfl) ⟨96627, by rfl⟩ : syracuseStep 1030693 = 193255) (by norm_num)
theorem B1030729 : Blo 912577 1030729 := bbase (se 2 (by rfl) ⟨386523, by rfl⟩ : syracuseStep 1030729 = 773047) (by norm_num)
theorem B1030765 : Blo 912577 1030765 := bbase (se 3 (by rfl) ⟨193268, by rfl⟩ : syracuseStep 1030765 = 386537) (by norm_num)
theorem B1030801 : Blo 912577 1030801 := bbase (se 2 (by rfl) ⟨386550, by rfl⟩ : syracuseStep 1030801 = 773101) (by norm_num)
theorem B1030837 : Blo 912577 1030837 := bbase (se 5 (by rfl) ⟨48320, by rfl⟩ : syracuseStep 1030837 = 96641) (by norm_num)
theorem B1030873 : Blo 912577 1030873 := bbase (se 2 (by rfl) ⟨386577, by rfl⟩ : syracuseStep 1030873 = 773155) (by norm_num)
theorem B1030909 : Blo 912577 1030909 := bbase (se 3 (by rfl) ⟨193295, by rfl⟩ : syracuseStep 1030909 = 386591) (by norm_num)
theorem B2931461 : Blo 912577 2931461 := bbase (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) (by norm_num)
theorem B1030945 : Blo 912577 1030945 := bbase (se 2 (by rfl) ⟨386604, by rfl⟩ : syracuseStep 1030945 = 773209) (by norm_num)
theorem B1030981 : Blo 912577 1030981 := bbase (se 4 (by rfl) ⟨96654, by rfl⟩ : syracuseStep 1030981 = 193309) (by norm_num)
theorem B1031017 : Blo 912577 1031017 := bbase (se 2 (by rfl) ⟨386631, by rfl⟩ : syracuseStep 1031017 = 773263) (by norm_num)
theorem B1031053 : Blo 912577 1031053 := bbase (se 3 (by rfl) ⟨193322, by rfl⟩ : syracuseStep 1031053 = 386645) (by norm_num)
theorem B1096597 : Blo 912577 1096597 := bbase (se 6 (by rfl) ⟨25701, by rfl⟩ : syracuseStep 1096597 = 51403) (by norm_num)
theorem B1031089 : Blo 912577 1031089 := bbase (se 2 (by rfl) ⟨386658, by rfl⟩ : syracuseStep 1031089 = 773317) (by norm_num)
theorem B3292085 : Blo 912577 3292085 := bbase (se 5 (by rfl) ⟨154316, by rfl⟩ : syracuseStep 3292085 = 308633) (by norm_num)
theorem B1391573 : Blo 912577 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B1031125 : Blo 912577 1031125 := bbase (se 7 (by rfl) ⟨12083, by rfl⟩ : syracuseStep 1031125 = 24167) (by norm_num)
theorem B1850573 : Blo 912577 1850573 := bbase (se 3 (by rfl) ⟨346982, by rfl⟩ : syracuseStep 1850573 = 693965) (by norm_num)
theorem B3915125 : Blo 912577 3915125 := bbase (se 5 (by rfl) ⟨183521, by rfl⟩ : syracuseStep 3915125 = 367043) (by norm_num)
theorem B6766037 : Blo 912577 6766037 := bbase (se 7 (by rfl) ⟨79289, by rfl⟩ : syracuseStep 6766037 = 158579) (by norm_num)
theorem B2604581 : Blo 912577 2604581 := bbase (se 4 (by rfl) ⟨244179, by rfl⟩ : syracuseStep 2604581 = 488359) (by norm_num)
theorem B4636277 : Blo 912577 4636277 := bbase (se 5 (by rfl) ⟨217325, by rfl⟩ : syracuseStep 4636277 = 434651) (by norm_num)
theorem B2932357 : Blo 912577 2932357 := bbase (se 4 (by rfl) ⟨274908, by rfl⟩ : syracuseStep 2932357 = 549817) (by norm_num)
theorem B1949437 : Blo 912577 1949437 := bbase (se 3 (by rfl) ⟨365519, by rfl⟩ : syracuseStep 1949437 = 731039) (by norm_num)
theorem B1097597 : Blo 912577 1097597 := bbase (se 3 (by rfl) ⟨205799, by rfl⟩ : syracuseStep 1097597 = 411599) (by norm_num)
theorem B2310029 : Blo 912577 2310029 := bbase (se 3 (by rfl) ⟨433130, by rfl⟩ : syracuseStep 2310029 = 866261) (by norm_num)
theorem B1097669 : Blo 912577 1097669 := bbase (se 4 (by rfl) ⟨102906, by rfl⟩ : syracuseStep 1097669 = 205813) (by norm_num)
theorem B2932757 : Blo 912577 2932757 := bbase (se 6 (by rfl) ⟨68736, by rfl⟩ : syracuseStep 2932757 = 137473) (by norm_num)
theorem B2310221 : Blo 912577 2310221 := bbase (se 3 (by rfl) ⟨433166, by rfl⟩ : syracuseStep 2310221 = 866333) (by norm_num)
theorem B1949933 : Blo 912577 1949933 := bbase (se 3 (by rfl) ⟨365612, by rfl⟩ : syracuseStep 1949933 = 731225) (by norm_num)
theorem B1097977 : Blo 912577 1097977 := bbase (se 2 (by rfl) ⟨411741, by rfl⟩ : syracuseStep 1097977 = 823483) (by norm_num)
theorem B1392893 : Blo 912577 1392893 := bbase (se 3 (by rfl) ⟨261167, by rfl⟩ : syracuseStep 1392893 = 522335) (by norm_num)
theorem B1098145 : Blo 912577 1098145 := bbase (se 2 (by rfl) ⟨411804, by rfl⟩ : syracuseStep 1098145 = 823609) (by norm_num)
theorem B2310565 : Blo 912577 2310565 := bbase (se 4 (by rfl) ⟨216615, by rfl⟩ : syracuseStep 2310565 = 433231) (by norm_num)
theorem B2113997 : Blo 912577 2113997 := bbase (se 3 (by rfl) ⟨396374, by rfl⟩ : syracuseStep 2113997 = 792749) (by norm_num)
theorem B1098193 : Blo 912577 1098193 := bbase (se 2 (by rfl) ⟨411822, by rfl⟩ : syracuseStep 1098193 = 823645) (by norm_num)
theorem B11715029 : Blo 912577 11715029 := bbase (se 7 (by rfl) ⟨137285, by rfl⟩ : syracuseStep 11715029 = 274571) (by norm_num)
theorem B2310677 : Blo 912577 2310677 := bbase (se 6 (by rfl) ⟨54156, by rfl⟩ : syracuseStep 2310677 = 108313) (by norm_num)
theorem B1098289 : Blo 912577 1098289 := bbase (se 2 (by rfl) ⟨411858, by rfl⟩ : syracuseStep 1098289 = 823717) (by norm_num)
theorem B2605765 : Blo 912577 2605765 := bbase (se 4 (by rfl) ⟨244290, by rfl⟩ : syracuseStep 2605765 = 488581) (by norm_num)
theorem B2310869 : Blo 912577 2310869 := bbase (se 7 (by rfl) ⟨27080, by rfl⟩ : syracuseStep 2310869 = 54161) (by norm_num)
theorem B1393453 : Blo 912577 1393453 := bbase (se 3 (by rfl) ⟨261272, by rfl⟩ : syracuseStep 1393453 = 522545) (by norm_num)
theorem B2605925 : Blo 912577 2605925 := bbase (se 4 (by rfl) ⟨244305, by rfl⟩ : syracuseStep 2605925 = 488611) (by norm_num)
theorem B2474869 : Blo 912577 2474869 := bbase (se 5 (by rfl) ⟨116009, by rfl⟩ : syracuseStep 2474869 = 232019) (by norm_num)
theorem B4637573 : Blo 912577 4637573 := bbase (se 4 (by rfl) ⟨434772, by rfl⟩ : syracuseStep 4637573 = 869545) (by norm_num)
theorem B2311213 : Blo 912577 2311213 := bbase (se 3 (by rfl) ⟨433352, by rfl⟩ : syracuseStep 2311213 = 866705) (by norm_num)
theorem B1950797 : Blo 912577 1950797 := bbase (se 3 (by rfl) ⟨365774, by rfl⟩ : syracuseStep 1950797 = 731549) (by norm_num)
theorem B2606165 : Blo 912577 2606165 := bbase (se 8 (by rfl) ⟨15270, by rfl⟩ : syracuseStep 2606165 = 30541) (by norm_num)
theorem B1098865 : Blo 912577 1098865 := bbase (se 2 (by rfl) ⟨412074, by rfl⟩ : syracuseStep 1098865 = 824149) (by norm_num)
theorem B2311325 : Blo 912577 2311325 := bbase (se 3 (by rfl) ⟨433373, by rfl⟩ : syracuseStep 2311325 = 866747) (by norm_num)
theorem B1950941 : Blo 912577 1950941 := bbase (se 3 (by rfl) ⟨365801, by rfl⟩ : syracuseStep 1950941 = 731603) (by norm_num)
theorem B2606357 : Blo 912577 2606357 := bbase (se 6 (by rfl) ⟨61086, by rfl⟩ : syracuseStep 2606357 = 122173) (by norm_num)
theorem B2311517 : Blo 912577 2311517 := bbase (se 3 (by rfl) ⟨433409, by rfl⟩ : syracuseStep 2311517 = 866819) (by norm_num)
theorem B1852877 : Blo 912577 1852877 := bbase (se 3 (by rfl) ⟨347414, by rfl⟩ : syracuseStep 1852877 = 694829) (by norm_num)
theorem B2311861 : Blo 912577 2311861 := bbase (se 5 (by rfl) ⟨108368, by rfl⟩ : syracuseStep 2311861 = 216737) (by norm_num)
theorem B2311973 : Blo 912577 2311973 := bbase (se 4 (by rfl) ⟨216747, by rfl⟩ : syracuseStep 2311973 = 433495) (by norm_num)
theorem B8898389 : Blo 912577 8898389 := bbase (se 9 (by rfl) ⟨26069, by rfl⟩ : syracuseStep 8898389 = 52139) (by norm_num)
theorem B4179845 : Blo 912577 4179845 := bbase (se 4 (by rfl) ⟨391860, by rfl⟩ : syracuseStep 4179845 = 783721) (by norm_num)
theorem B1951685 : Blo 912577 1951685 := bbase (se 4 (by rfl) ⟨182970, by rfl⟩ : syracuseStep 1951685 = 365941) (by norm_num)
theorem B2312165 : Blo 912577 2312165 := bbase (se 4 (by rfl) ⟨216765, by rfl⟩ : syracuseStep 2312165 = 433531) (by norm_num)
theorem B1099865 : Blo 912577 1099865 := bbase (se 2 (by rfl) ⟨412449, by rfl⟩ : syracuseStep 1099865 = 824899) (by norm_num)
theorem B1099913 : Blo 912577 1099913 := bbase (se 2 (by rfl) ⟨412467, by rfl⟩ : syracuseStep 1099913 = 824935) (by norm_num)
theorem B4638869 : Blo 912577 4638869 := bbase (se 6 (by rfl) ⟨108723, by rfl⟩ : syracuseStep 4638869 = 217447) (by norm_num)
theorem B2607349 : Blo 912577 2607349 := bbase (se 5 (by rfl) ⟨122219, by rfl⟩ : syracuseStep 2607349 = 244439) (by norm_num)
theorem B2345213 : Blo 912577 2345213 := bbase (se 3 (by rfl) ⟨439727, by rfl⟩ : syracuseStep 2345213 = 879455) (by norm_num)
theorem B6932789 : Blo 912577 6932789 := bbase (se 5 (by rfl) ⟨324974, by rfl⟩ : syracuseStep 6932789 = 649949) (by norm_num)
theorem B8898869 : Blo 912577 8898869 := bbase (se 5 (by rfl) ⟨417134, by rfl⟩ : syracuseStep 8898869 = 834269) (by norm_num)
theorem B2312509 : Blo 912577 2312509 := bbase (se 3 (by rfl) ⟨433595, by rfl⟩ : syracuseStep 2312509 = 867191) (by norm_num)
theorem B3754309 : Blo 912577 3754309 := bbase (se 4 (by rfl) ⟨351966, by rfl⟩ : syracuseStep 3754309 = 703933) (by norm_num)
theorem B2312621 : Blo 912577 2312621 := bbase (se 3 (by rfl) ⟨433616, by rfl⟩ : syracuseStep 2312621 = 867233) (by norm_num)
theorem B5556757 : Blo 912577 5556757 := bbase (se 6 (by rfl) ⟨130236, by rfl⟩ : syracuseStep 5556757 = 260473) (by norm_num)
theorem B3525205 : Blo 912577 3525205 := bbase (se 8 (by rfl) ⟨20655, by rfl⟩ : syracuseStep 3525205 = 41311) (by norm_num)
theorem B2312813 : Blo 912577 2312813 := bbase (se 3 (by rfl) ⟨433652, by rfl⟩ : syracuseStep 2312813 = 867305) (by norm_num)
theorem B1100461 : Blo 912577 1100461 := bbase (se 3 (by rfl) ⟨206336, by rfl⟩ : syracuseStep 1100461 = 412673) (by norm_num)
theorem B1952437 : Blo 912577 1952437 := bbase (se 5 (by rfl) ⟨91520, by rfl⟩ : syracuseStep 1952437 = 183041) (by norm_num)
theorem B1952581 : Blo 912577 1952581 := bbase (se 4 (by rfl) ⟨183054, by rfl⟩ : syracuseStep 1952581 = 366109) (by norm_num)
theorem B2313157 : Blo 912577 2313157 := bbase (se 4 (by rfl) ⟨216858, by rfl⟩ : syracuseStep 2313157 = 433717) (by norm_num)
theorem B2313269 : Blo 912577 2313269 := bbase (se 5 (by rfl) ⟨108434, by rfl⟩ : syracuseStep 2313269 = 216869) (by norm_num)
theorem B3132533 : Blo 912577 3132533 := bbase (se 5 (by rfl) ⟨146837, by rfl⟩ : syracuseStep 3132533 = 293675) (by norm_num)
theorem B1100941 : Blo 912577 1100941 := bbase (se 3 (by rfl) ⟨206426, by rfl⟩ : syracuseStep 1100941 = 412853) (by norm_num)
theorem B7818389 : Blo 912577 7818389 := bbase (se 6 (by rfl) ⟨183243, by rfl⟩ : syracuseStep 7818389 = 366487) (by norm_num)
theorem B1952957 : Blo 912577 1952957 := bbase (se 3 (by rfl) ⟨366179, by rfl⟩ : syracuseStep 1952957 = 732359) (by norm_num)
theorem B2313461 : Blo 912577 2313461 := bbase (se 5 (by rfl) ⟨108443, by rfl⟩ : syracuseStep 2313461 = 216887) (by norm_num)
theorem B2608453 : Blo 912577 2608453 := bbase (se 4 (by rfl) ⟨244542, by rfl⟩ : syracuseStep 2608453 = 489085) (by norm_num)
theorem B2542949 : Blo 912577 2542949 := bbase (se 4 (by rfl) ⟨238401, by rfl⟩ : syracuseStep 2542949 = 476803) (by norm_num)
theorem B4640165 : Blo 912577 4640165 := bbase (se 4 (by rfl) ⟨435015, by rfl⟩ : syracuseStep 4640165 = 870031) (by norm_num)
theorem B1461797 : Blo 912577 1461797 := bbase (se 4 (by rfl) ⟨137043, by rfl⟩ : syracuseStep 1461797 = 274087) (by norm_num)
theorem B1953325 : Blo 912577 1953325 := bbase (se 3 (by rfl) ⟨366248, by rfl⟩ : syracuseStep 1953325 = 732497) (by norm_num)
theorem B2313805 : Blo 912577 2313805 := bbase (se 3 (by rfl) ⟨433838, by rfl⟩ : syracuseStep 2313805 = 867677) (by norm_num)
theorem B8343125 : Blo 912577 8343125 := bbase (se 8 (by rfl) ⟨48885, by rfl⟩ : syracuseStep 8343125 = 97771) (by norm_num)
theorem B2313917 : Blo 912577 2313917 := bbase (se 3 (by rfl) ⟨433859, by rfl⟩ : syracuseStep 2313917 = 867719) (by norm_num)
theorem B1461989 : Blo 912577 1461989 := bbase (se 4 (by rfl) ⟨137061, by rfl⟩ : syracuseStep 1461989 = 274123) (by norm_num)
theorem B3952421 : Blo 912577 3952421 := bbase (se 4 (by rfl) ⟨370539, by rfl⟩ : syracuseStep 3952421 = 741079) (by norm_num)
theorem B2314109 : Blo 912577 2314109 := bbase (se 3 (by rfl) ⟨433895, by rfl⟩ : syracuseStep 2314109 = 867791) (by norm_num)
theorem B2314453 : Blo 912577 2314453 := bbase (se 7 (by rfl) ⟨27122, by rfl⟩ : syracuseStep 2314453 = 54245) (by norm_num)
theorem B2314565 : Blo 912577 2314565 := bbase (se 4 (by rfl) ⟨216990, by rfl⟩ : syracuseStep 2314565 = 433981) (by norm_num)
theorem B2085197 : Blo 912577 2085197 := bbase (se 3 (by rfl) ⟨390974, by rfl⟩ : syracuseStep 2085197 = 781949) (by norm_num)
theorem B2347429 : Blo 912577 2347429 := bbase (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) (by norm_num)
theorem B2314757 : Blo 912577 2314757 := bbase (se 4 (by rfl) ⟨217008, by rfl⟩ : syracuseStep 2314757 = 434017) (by norm_num)
theorem B1561141 : Blo 912577 1561141 := bbase (se 5 (by rfl) ⟨73178, by rfl⟩ : syracuseStep 1561141 = 146357) (by norm_num)
theorem B10408661 : Blo 912577 10408661 := bbase (se 7 (by rfl) ⟨121976, by rfl⟩ : syracuseStep 10408661 = 243953) (by norm_num)
theorem B3756773 : Blo 912577 3756773 := bbase (se 4 (by rfl) ⟨352197, by rfl⟩ : syracuseStep 3756773 = 704395) (by norm_num)
theorem B2609957 : Blo 912577 2609957 := bbase (se 4 (by rfl) ⟨244683, by rfl⟩ : syracuseStep 2609957 = 489367) (by norm_num)
theorem B2315101 : Blo 912577 2315101 := bbase (se 3 (by rfl) ⟨434081, by rfl⟩ : syracuseStep 2315101 = 868163) (by norm_num)
theorem B1856405 : Blo 912577 1856405 := bbase (se 6 (by rfl) ⟨43509, by rfl⟩ : syracuseStep 1856405 = 87019) (by norm_num)
theorem B1299397 : Blo 912577 1299397 := bbase (se 4 (by rfl) ⟨121818, by rfl⟩ : syracuseStep 1299397 = 243637) (by norm_num)
theorem B2315213 : Blo 912577 2315213 := bbase (se 3 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 2315213 = 868205) (by norm_num)
theorem B1561613 : Blo 912577 1561613 := bbase (se 3 (by rfl) ⟨292802, by rfl⟩ : syracuseStep 1561613 = 585605) (by norm_num)
theorem B1954829 : Blo 912577 1954829 := bbase (se 3 (by rfl) ⟨366530, by rfl⟩ : syracuseStep 1954829 = 733061) (by norm_num)
theorem B1234013 : Blo 912577 1234013 := bbase (se 3 (by rfl) ⟨231377, by rfl⟩ : syracuseStep 1234013 = 462755) (by norm_num)
theorem B1463437 : Blo 912577 1463437 := bbase (se 3 (by rfl) ⟨274394, by rfl⟩ : syracuseStep 1463437 = 548789) (by norm_num)
theorem B2315405 : Blo 912577 2315405 := bbase (se 3 (by rfl) ⟨434138, by rfl⟩ : syracuseStep 2315405 = 868277) (by norm_num)
theorem B1954973 : Blo 912577 1954973 := bbase (se 3 (by rfl) ⟨366557, by rfl⟩ : syracuseStep 1954973 = 733115) (by norm_num)
theorem B2053349 : Blo 912577 2053349 := bbase (se 4 (by rfl) ⟨192501, by rfl⟩ : syracuseStep 2053349 = 385003) (by norm_num)
theorem B2053421 : Blo 912577 2053421 := bbase (se 3 (by rfl) ⟨385016, by rfl⟩ : syracuseStep 2053421 = 770033) (by norm_num)
theorem B5854517 : Blo 912577 5854517 := bbase (se 5 (by rfl) ⟨274430, by rfl⟩ : syracuseStep 5854517 = 548861) (by norm_num)
theorem B1299773 : Blo 912577 1299773 := bbase (se 3 (by rfl) ⟨243707, by rfl⟩ : syracuseStep 1299773 = 487415) (by norm_num)
theorem B2053493 : Blo 912577 2053493 := bbase (se 5 (by rfl) ⟨96257, by rfl⟩ : syracuseStep 2053493 = 192515) (by norm_num)
theorem B2053565 : Blo 912577 2053565 := bbase (se 3 (by rfl) ⟨385043, by rfl⟩ : syracuseStep 2053565 = 770087) (by norm_num)
theorem B2315749 : Blo 912577 2315749 := bbase (se 4 (by rfl) ⟨217101, by rfl⟩ : syracuseStep 2315749 = 434203) (by norm_num)
theorem B2053637 : Blo 912577 2053637 := bbase (se 4 (by rfl) ⟨192528, by rfl⟩ : syracuseStep 2053637 = 385057) (by norm_num)
theorem B1955333 : Blo 912577 1955333 := bbase (se 4 (by rfl) ⟨183312, by rfl⟩ : syracuseStep 1955333 = 366625) (by norm_num)
theorem B2053709 : Blo 912577 2053709 := bbase (se 3 (by rfl) ⟨385070, by rfl⟩ : syracuseStep 2053709 = 770141) (by norm_num)
theorem B2315861 : Blo 912577 2315861 := bbase (se 8 (by rfl) ⟨13569, by rfl⟩ : syracuseStep 2315861 = 27139) (by norm_num)
theorem B2053781 : Blo 912577 2053781 := bbase (se 6 (by rfl) ⟨48135, by rfl⟩ : syracuseStep 2053781 = 96271) (by norm_num)
theorem B1234645 : Blo 912577 1234645 := bbase (se 7 (by rfl) ⟨14468, by rfl⟩ : syracuseStep 1234645 = 28937) (by norm_num)
theorem B2053853 : Blo 912577 2053853 := bbase (se 3 (by rfl) ⟨385097, by rfl⟩ : syracuseStep 2053853 = 770195) (by norm_num)
theorem B7034645 : Blo 912577 7034645 := bbase (se 6 (by rfl) ⟨164874, by rfl⟩ : syracuseStep 7034645 = 329749) (by norm_num)
theorem B2316053 : Blo 912577 2316053 := bbase (se 6 (by rfl) ⟨54282, by rfl⟩ : syracuseStep 2316053 = 108565) (by norm_num)
theorem B2053925 : Blo 912577 2053925 := bbase (se 4 (by rfl) ⟨192555, by rfl⟩ : syracuseStep 2053925 = 385111) (by norm_num)
theorem B2053997 : Blo 912577 2053997 := bbase (se 3 (by rfl) ⟨385124, by rfl⟩ : syracuseStep 2053997 = 770249) (by norm_num)
theorem B2054069 : Blo 912577 2054069 := bbase (se 5 (by rfl) ⟨96284, by rfl⟩ : syracuseStep 2054069 = 192569) (by norm_num)
theorem B2054141 : Blo 912577 2054141 := bbase (se 3 (by rfl) ⟨385151, by rfl⟩ : syracuseStep 2054141 = 770303) (by norm_num)
theorem B2054213 : Blo 912577 2054213 := bbase (se 4 (by rfl) ⟨192582, by rfl⟩ : syracuseStep 2054213 = 385165) (by norm_num)
theorem B2316397 : Blo 912577 2316397 := bbase (se 3 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 2316397 = 868649) (by norm_num)
theorem B2054285 : Blo 912577 2054285 := bbase (se 3 (by rfl) ⟨385178, by rfl⟩ : syracuseStep 2054285 = 770357) (by norm_num)
theorem B2054357 : Blo 912577 2054357 := bbase (se 7 (by rfl) ⟨24074, by rfl⟩ : syracuseStep 2054357 = 48149) (by norm_num)
theorem B2316509 : Blo 912577 2316509 := bbase (se 3 (by rfl) ⟨434345, by rfl⟩ : syracuseStep 2316509 = 868691) (by norm_num)
theorem B2054429 : Blo 912577 2054429 := bbase (se 3 (by rfl) ⟨385205, by rfl⟩ : syracuseStep 2054429 = 770411) (by norm_num)
theorem B2054501 : Blo 912577 2054501 := bbase (se 4 (by rfl) ⟨192609, by rfl⟩ : syracuseStep 2054501 = 385219) (by norm_num)
theorem B1956221 : Blo 912577 1956221 := bbase (se 3 (by rfl) ⟨366791, by rfl⟩ : syracuseStep 1956221 = 733583) (by norm_num)
theorem B2316701 : Blo 912577 2316701 := bbase (se 3 (by rfl) ⟨434381, by rfl⟩ : syracuseStep 2316701 = 868763) (by norm_num)
theorem B2054573 : Blo 912577 2054573 := bbase (se 3 (by rfl) ⟨385232, by rfl⟩ : syracuseStep 2054573 = 770465) (by norm_num)
theorem B2054645 : Blo 912577 2054645 := bbase (se 5 (by rfl) ⟨96311, by rfl⟩ : syracuseStep 2054645 = 192623) (by norm_num)
theorem B1464821 : Blo 912577 1464821 := bbase (se 5 (by rfl) ⟨68663, by rfl⟩ : syracuseStep 1464821 = 137327) (by norm_num)
theorem B2054717 : Blo 912577 2054717 := bbase (se 3 (by rfl) ⟨385259, by rfl⟩ : syracuseStep 2054717 = 770519) (by norm_num)
theorem B9394805 : Blo 912577 9394805 := bbase (se 5 (by rfl) ⟨440381, by rfl⟩ : syracuseStep 9394805 = 880763) (by norm_num)
theorem B1956469 : Blo 912577 1956469 := bbase (se 5 (by rfl) ⟨91709, by rfl⟩ : syracuseStep 1956469 = 183419) (by norm_num)
theorem B2054789 : Blo 912577 2054789 := bbase (se 4 (by rfl) ⟨192636, by rfl⟩ : syracuseStep 2054789 = 385273) (by norm_num)
theorem B1465013 : Blo 912577 1465013 := bbase (se 5 (by rfl) ⟨68672, by rfl⟩ : syracuseStep 1465013 = 137345) (by norm_num)
theorem B2054861 : Blo 912577 2054861 := bbase (se 3 (by rfl) ⟨385286, by rfl⟩ : syracuseStep 2054861 = 770573) (by norm_num)
theorem B1301197 : Blo 912577 1301197 := bbase (se 3 (by rfl) ⟨243974, by rfl⟩ : syracuseStep 1301197 = 487949) (by norm_num)
theorem B2317045 : Blo 912577 2317045 := bbase (se 5 (by rfl) ⟨108611, by rfl⟩ : syracuseStep 2317045 = 217223) (by norm_num)
theorem B2054933 : Blo 912577 2054933 := bbase (se 6 (by rfl) ⟨48162, by rfl⟩ : syracuseStep 2054933 = 96325) (by norm_num)
theorem B2055005 : Blo 912577 2055005 := bbase (se 3 (by rfl) ⟨385313, by rfl⟩ : syracuseStep 2055005 = 770627) (by norm_num)
theorem B2317157 : Blo 912577 2317157 := bbase (se 4 (by rfl) ⟨217233, by rfl⟩ : syracuseStep 2317157 = 434467) (by norm_num)
theorem B2055077 : Blo 912577 2055077 := bbase (se 4 (by rfl) ⟨192663, by rfl⟩ : syracuseStep 2055077 = 385327) (by norm_num)
theorem B2055149 : Blo 912577 2055149 := bbase (se 3 (by rfl) ⟨385340, by rfl⟩ : syracuseStep 2055149 = 770681) (by norm_num)
theorem B2317349 : Blo 912577 2317349 := bbase (se 4 (by rfl) ⟨217251, by rfl⟩ : syracuseStep 2317349 = 434503) (by norm_num)
theorem B3300389 : Blo 912577 3300389 := bbase (se 4 (by rfl) ⟨309411, by rfl⟩ : syracuseStep 3300389 = 618823) (by norm_num)
theorem B2055221 : Blo 912577 2055221 := bbase (se 5 (by rfl) ⟨96338, by rfl⟩ : syracuseStep 2055221 = 192677) (by norm_num)
theorem B1956973 : Blo 912577 1956973 := bbase (se 3 (by rfl) ⟨366932, by rfl⟩ : syracuseStep 1956973 = 733865) (by norm_num)
theorem B2055293 : Blo 912577 2055293 := bbase (se 3 (by rfl) ⟨385367, by rfl⟩ : syracuseStep 2055293 = 770735) (by norm_num)
theorem B3300517 : Blo 912577 3300517 := bbase (se 4 (by rfl) ⟨309423, by rfl⟩ : syracuseStep 3300517 = 618847) (by norm_num)
theorem B2055365 : Blo 912577 2055365 := bbase (se 4 (by rfl) ⟨192690, by rfl⟩ : syracuseStep 2055365 = 385381) (by norm_num)
theorem B2055437 : Blo 912577 2055437 := bbase (se 3 (by rfl) ⟨385394, by rfl⟩ : syracuseStep 2055437 = 770789) (by norm_num)
theorem B1301789 : Blo 912577 1301789 := bbase (se 3 (by rfl) ⟨244085, by rfl⟩ : syracuseStep 1301789 = 488171) (by norm_num)
theorem B2055509 : Blo 912577 2055509 := bbase (se 11 (by rfl) ⟨1505, by rfl⟩ : syracuseStep 2055509 = 3011) (by norm_num)
theorem B1301869 : Blo 912577 1301869 := bbase (se 3 (by rfl) ⟨244100, by rfl⟩ : syracuseStep 1301869 = 488201) (by norm_num)
theorem B2317693 : Blo 912577 2317693 := bbase (se 3 (by rfl) ⟨434567, by rfl⟩ : syracuseStep 2317693 = 869135) (by norm_num)
theorem B2055581 : Blo 912577 2055581 := bbase (se 3 (by rfl) ⟨385421, by rfl⟩ : syracuseStep 2055581 = 770843) (by norm_num)
theorem B1236397 : Blo 912577 1236397 := bbase (se 3 (by rfl) ⟨231824, by rfl⟩ : syracuseStep 1236397 = 463649) (by norm_num)
theorem B2055653 : Blo 912577 2055653 := bbase (se 4 (by rfl) ⟨192717, by rfl⟩ : syracuseStep 2055653 = 385435) (by norm_num)
theorem B1301989 : Blo 912577 1301989 := bbase (se 4 (by rfl) ⟨122061, by rfl⟩ : syracuseStep 1301989 = 244123) (by norm_num)
theorem B2317805 : Blo 912577 2317805 := bbase (se 3 (by rfl) ⟨434588, by rfl⟩ : syracuseStep 2317805 = 869177) (by norm_num)
theorem B2055725 : Blo 912577 2055725 := bbase (se 3 (by rfl) ⟨385448, by rfl⟩ : syracuseStep 2055725 = 770897) (by norm_num)
theorem B1564213 : Blo 912577 1564213 := bbase (se 5 (by rfl) ⟨73322, by rfl⟩ : syracuseStep 1564213 = 146645) (by norm_num)
theorem B1302085 : Blo 912577 1302085 := bbase (se 4 (by rfl) ⟨122070, by rfl⟩ : syracuseStep 1302085 = 244141) (by norm_num)
theorem B2055797 : Blo 912577 2055797 := bbase (se 5 (by rfl) ⟨96365, by rfl⟩ : syracuseStep 2055797 = 192731) (by norm_num)
theorem B2317997 : Blo 912577 2317997 := bbase (se 3 (by rfl) ⟨434624, by rfl⟩ : syracuseStep 2317997 = 869249) (by norm_num)
theorem B2088629 : Blo 912577 2088629 := bbase (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) (by norm_num)
theorem B2055869 : Blo 912577 2055869 := bbase (se 3 (by rfl) ⟨385475, by rfl⟩ : syracuseStep 2055869 = 770951) (by norm_num)
theorem B2055941 : Blo 912577 2055941 := bbase (se 4 (by rfl) ⟨192744, by rfl⟩ : syracuseStep 2055941 = 385489) (by norm_num)
theorem B2056013 : Blo 912577 2056013 := bbase (se 3 (by rfl) ⟨385502, by rfl⟩ : syracuseStep 2056013 = 771005) (by norm_num)
theorem B2088821 : Blo 912577 2088821 := bbase (se 5 (by rfl) ⟨97913, by rfl⟩ : syracuseStep 2088821 = 195827) (by norm_num)
theorem B2056085 : Blo 912577 2056085 := bbase (se 6 (by rfl) ⟨48189, by rfl⟩ : syracuseStep 2056085 = 96379) (by norm_num)
theorem B974749 : Blo 912577 974749 := bbase (se 3 (by rfl) ⟨182765, by rfl⟩ : syracuseStep 974749 = 365531) (by norm_num)
theorem B2056157 : Blo 912577 2056157 := bbase (se 3 (by rfl) ⟨385529, by rfl⟩ : syracuseStep 2056157 = 771059) (by norm_num)
theorem B1466333 : Blo 912577 1466333 := bbase (se 3 (by rfl) ⟨274937, by rfl⟩ : syracuseStep 1466333 = 549875) (by norm_num)
theorem B2318341 : Blo 912577 2318341 := bbase (se 4 (by rfl) ⟨217344, by rfl⟩ : syracuseStep 2318341 = 434689) (by norm_num)
theorem B2056229 : Blo 912577 2056229 := bbase (se 4 (by rfl) ⟨192771, by rfl⟩ : syracuseStep 2056229 = 385543) (by norm_num)
theorem B1302581 : Blo 912577 1302581 := bbase (se 5 (by rfl) ⟨61058, by rfl⟩ : syracuseStep 1302581 = 122117) (by norm_num)
theorem B1171513 : Blo 912577 1171513 := bbase (se 2 (by rfl) ⟨439317, by rfl⟩ : syracuseStep 1171513 = 878635) (by norm_num)
theorem B1466429 : Blo 912577 1466429 := bbase (se 3 (by rfl) ⟨274955, by rfl⟩ : syracuseStep 1466429 = 549911) (by norm_num)
theorem B3465301 : Blo 912577 3465301 := bbase (se 8 (by rfl) ⟨20304, by rfl⟩ : syracuseStep 3465301 = 40609) (by norm_num)
theorem B1466461 : Blo 912577 1466461 := bbase (se 3 (by rfl) ⟨274961, by rfl⟩ : syracuseStep 1466461 = 549923) (by norm_num)
theorem B2056301 : Blo 912577 2056301 := bbase (se 3 (by rfl) ⟨385556, by rfl⟩ : syracuseStep 2056301 = 771113) (by norm_num)
theorem B2318453 : Blo 912577 2318453 := bbase (se 5 (by rfl) ⟨108677, by rfl⟩ : syracuseStep 2318453 = 217355) (by norm_num)
theorem B2056373 : Blo 912577 2056373 := bbase (se 5 (by rfl) ⟨96392, by rfl⟩ : syracuseStep 2056373 = 192785) (by norm_num)
theorem B2056445 : Blo 912577 2056445 := bbase (se 3 (by rfl) ⟨385583, by rfl⟩ : syracuseStep 2056445 = 771167) (by norm_num)
theorem B975125 : Blo 912577 975125 := bbase (se 6 (by rfl) ⟨22854, by rfl⟩ : syracuseStep 975125 = 45709) (by norm_num)
theorem B2318645 : Blo 912577 2318645 := bbase (se 5 (by rfl) ⟨108686, by rfl⟩ : syracuseStep 2318645 = 217373) (by norm_num)
theorem B2056517 : Blo 912577 2056517 := bbase (se 4 (by rfl) ⟨192798, by rfl⟩ : syracuseStep 2056517 = 385597) (by norm_num)
theorem B1040725 : Blo 912577 1040725 := bbase (se 10 (by rfl) ⟨1524, by rfl⟩ : syracuseStep 1040725 = 3049) (by norm_num)
theorem B975197 : Blo 912577 975197 := bbase (se 3 (by rfl) ⟨182849, by rfl⟩ : syracuseStep 975197 = 365699) (by norm_num)
theorem B3465605 : Blo 912577 3465605 := bbase (se 4 (by rfl) ⟨324900, by rfl⟩ : syracuseStep 3465605 = 649801) (by norm_num)
theorem B2056589 : Blo 912577 2056589 := bbase (se 3 (by rfl) ⟨385610, by rfl⟩ : syracuseStep 2056589 = 771221) (by norm_num)
theorem B2056661 : Blo 912577 2056661 := bbase (se 7 (by rfl) ⟨24101, by rfl⟩ : syracuseStep 2056661 = 48203) (by norm_num)
theorem B975385 : Blo 912577 975385 := bbase (se 2 (by rfl) ⟨365769, by rfl⟩ : syracuseStep 975385 = 731539) (by norm_num)
theorem B2056733 : Blo 912577 2056733 := bbase (se 3 (by rfl) ⟨385637, by rfl⟩ : syracuseStep 2056733 = 771275) (by norm_num)
theorem B1237565 : Blo 912577 1237565 := bbase (se 3 (by rfl) ⟨232043, by rfl⟩ : syracuseStep 1237565 = 464087) (by norm_num)
theorem B1303133 : Blo 912577 1303133 := bbase (se 3 (by rfl) ⟨244337, by rfl⟩ : syracuseStep 1303133 = 488675) (by norm_num)
theorem B2056805 : Blo 912577 2056805 := bbase (se 4 (by rfl) ⟨192825, by rfl⟩ : syracuseStep 2056805 = 385651) (by norm_num)
theorem B2318989 : Blo 912577 2318989 := bbase (se 3 (by rfl) ⟨434810, by rfl⟩ : syracuseStep 2318989 = 869621) (by norm_num)
theorem B2056877 : Blo 912577 2056877 := bbase (se 3 (by rfl) ⟨385664, by rfl⟩ : syracuseStep 2056877 = 771329) (by norm_num)
theorem B975569 : Blo 912577 975569 := bbase (se 2 (by rfl) ⟨365838, by rfl⟩ : syracuseStep 975569 = 731677) (by norm_num)
theorem B2056949 : Blo 912577 2056949 := bbase (se 5 (by rfl) ⟨96419, by rfl⟩ : syracuseStep 2056949 = 192839) (by norm_num)
theorem B2319101 : Blo 912577 2319101 := bbase (se 3 (by rfl) ⟨434831, by rfl⟩ : syracuseStep 2319101 = 869663) (by norm_num)
theorem B1237781 : Blo 912577 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B1368869 : Blo 912577 1368869 := bbase (se 4 (by rfl) ⟨128331, by rfl⟩ : syracuseStep 1368869 = 256663) (by norm_num)
theorem B1368893 : Blo 912577 1368893 := bbase (se 3 (by rfl) ⟨256667, by rfl⟩ : syracuseStep 1368893 = 513335) (by norm_num)
theorem B2057021 : Blo 912577 2057021 := bbase (se 3 (by rfl) ⟨385691, by rfl⟩ : syracuseStep 2057021 = 771383) (by norm_num)
theorem B1368917 : Blo 912577 1368917 := bbase (se 9 (by rfl) ⟨4010, by rfl⟩ : syracuseStep 1368917 = 8021) (by norm_num)
theorem B1368941 : Blo 912577 1368941 := bbase (se 3 (by rfl) ⟨256676, by rfl⟩ : syracuseStep 1368941 = 513353) (by norm_num)
theorem B1368965 : Blo 912577 1368965 := bbase (se 4 (by rfl) ⟨128340, by rfl⟩ : syracuseStep 1368965 = 256681) (by norm_num)
theorem B2057093 : Blo 912577 2057093 := bbase (se 4 (by rfl) ⟨192852, by rfl⟩ : syracuseStep 2057093 = 385705) (by norm_num)
theorem B1368989 : Blo 912577 1368989 := bbase (se 3 (by rfl) ⟨256685, by rfl⟩ : syracuseStep 1368989 = 513371) (by norm_num)
theorem B1369013 : Blo 912577 1369013 := bbase (se 5 (by rfl) ⟨64172, by rfl⟩ : syracuseStep 1369013 = 128345) (by norm_num)
theorem B2319293 : Blo 912577 2319293 := bbase (se 3 (by rfl) ⟨434867, by rfl⟩ : syracuseStep 2319293 = 869735) (by norm_num)
theorem B1369037 : Blo 912577 1369037 := bbase (se 3 (by rfl) ⟨256694, by rfl⟩ : syracuseStep 1369037 = 513389) (by norm_num)
theorem B2057165 : Blo 912577 2057165 := bbase (se 3 (by rfl) ⟨385718, by rfl⟩ : syracuseStep 2057165 = 771437) (by norm_num)
theorem B1369061 : Blo 912577 1369061 := bbase (se 4 (by rfl) ⟨128349, by rfl⟩ : syracuseStep 1369061 = 256699) (by norm_num)
theorem B1270765 : Blo 912577 1270765 := bbase (se 3 (by rfl) ⟨238268, by rfl⟩ : syracuseStep 1270765 = 476537) (by norm_num)
theorem B1369085 : Blo 912577 1369085 := bbase (se 3 (by rfl) ⟨256703, by rfl⟩ : syracuseStep 1369085 = 513407) (by norm_num)
theorem B1369109 : Blo 912577 1369109 := bbase (se 6 (by rfl) ⟨32088, by rfl⟩ : syracuseStep 1369109 = 64177) (by norm_num)
theorem B2057237 : Blo 912577 2057237 := bbase (se 6 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 2057237 = 96433) (by norm_num)
theorem B1369133 : Blo 912577 1369133 := bbase (se 3 (by rfl) ⟨256712, by rfl⟩ : syracuseStep 1369133 = 513425) (by norm_num)
theorem B1369157 : Blo 912577 1369157 := bbase (se 4 (by rfl) ⟨128358, by rfl⟩ : syracuseStep 1369157 = 256717) (by norm_num)
theorem B1369181 : Blo 912577 1369181 := bbase (se 3 (by rfl) ⟨256721, by rfl⟩ : syracuseStep 1369181 = 513443) (by norm_num)
theorem B2057309 : Blo 912577 2057309 := bbase (se 3 (by rfl) ⟨385745, by rfl⟩ : syracuseStep 2057309 = 771491) (by norm_num)
theorem B1369205 : Blo 912577 1369205 := bbase (se 5 (by rfl) ⟨64181, by rfl⟩ : syracuseStep 1369205 = 128363) (by norm_num)
theorem B1369229 : Blo 912577 1369229 := bbase (se 3 (by rfl) ⟨256730, by rfl⟩ : syracuseStep 1369229 = 513461) (by norm_num)
theorem B1369253 : Blo 912577 1369253 := bbase (se 4 (by rfl) ⟨128367, by rfl⟩ : syracuseStep 1369253 = 256735) (by norm_num)
theorem B2057381 : Blo 912577 2057381 := bbase (se 4 (by rfl) ⟨192879, by rfl⟩ : syracuseStep 2057381 = 385759) (by norm_num)
theorem B1369277 : Blo 912577 1369277 := bbase (se 3 (by rfl) ⟨256739, by rfl⟩ : syracuseStep 1369277 = 513479) (by norm_num)
theorem B1238213 : Blo 912577 1238213 := bbase (se 4 (by rfl) ⟨116082, by rfl⟩ : syracuseStep 1238213 = 232165) (by norm_num)
theorem B1369301 : Blo 912577 1369301 := bbase (se 7 (by rfl) ⟨16046, by rfl⟩ : syracuseStep 1369301 = 32093) (by norm_num)
theorem B1369325 : Blo 912577 1369325 := bbase (se 3 (by rfl) ⟨256748, by rfl⟩ : syracuseStep 1369325 = 513497) (by norm_num)
theorem B2057453 : Blo 912577 2057453 := bbase (se 3 (by rfl) ⟨385772, by rfl⟩ : syracuseStep 2057453 = 771545) (by norm_num)
theorem B1369349 : Blo 912577 1369349 := bbase (se 4 (by rfl) ⟨128376, by rfl⟩ : syracuseStep 1369349 = 256753) (by norm_num)
theorem B2319637 : Blo 912577 2319637 := bbase (se 6 (by rfl) ⟨54366, by rfl⟩ : syracuseStep 2319637 = 108733) (by norm_num)
theorem B1369373 : Blo 912577 1369373 := bbase (se 3 (by rfl) ⟨256757, by rfl⟩ : syracuseStep 1369373 = 513515) (by norm_num)
theorem B1369397 : Blo 912577 1369397 := bbase (se 5 (by rfl) ⟨64190, by rfl⟩ : syracuseStep 1369397 = 128381) (by norm_num)
theorem B2057525 : Blo 912577 2057525 := bbase (se 5 (by rfl) ⟨96446, by rfl⟩ : syracuseStep 2057525 = 192893) (by norm_num)
theorem B1369421 : Blo 912577 1369421 := bbase (se 3 (by rfl) ⟨256766, by rfl⟩ : syracuseStep 1369421 = 513533) (by norm_num)
theorem B1303885 : Blo 912577 1303885 := bbase (se 3 (by rfl) ⟨244478, by rfl⟩ : syracuseStep 1303885 = 488957) (by norm_num)
theorem B1369445 : Blo 912577 1369445 := bbase (se 4 (by rfl) ⟨128385, by rfl⟩ : syracuseStep 1369445 = 256771) (by norm_num)
theorem B1369469 : Blo 912577 1369469 := bbase (se 3 (by rfl) ⟨256775, by rfl⟩ : syracuseStep 1369469 = 513551) (by norm_num)
theorem B2057597 : Blo 912577 2057597 := bbase (se 3 (by rfl) ⟨385799, by rfl⟩ : syracuseStep 2057597 = 771599) (by norm_num)
theorem B2319749 : Blo 912577 2319749 := bbase (se 4 (by rfl) ⟨217476, by rfl⟩ : syracuseStep 2319749 = 434953) (by norm_num)
theorem B1369493 : Blo 912577 1369493 := bbase (se 6 (by rfl) ⟨32097, by rfl⟩ : syracuseStep 1369493 = 64195) (by norm_num)
theorem B1369517 : Blo 912577 1369517 := bbase (se 3 (by rfl) ⟨256784, by rfl⟩ : syracuseStep 1369517 = 513569) (by norm_num)
theorem B976321 : Blo 912577 976321 := bbase (se 2 (by rfl) ⟨366120, by rfl⟩ : syracuseStep 976321 = 732241) (by norm_num)
theorem B1369541 : Blo 912577 1369541 := bbase (se 4 (by rfl) ⟨128394, by rfl⟩ : syracuseStep 1369541 = 256789) (by norm_num)
theorem B2057669 : Blo 912577 2057669 := bbase (se 4 (by rfl) ⟨192906, by rfl⟩ : syracuseStep 2057669 = 385813) (by norm_num)
theorem B1369565 : Blo 912577 1369565 := bbase (se 3 (by rfl) ⟨256793, by rfl⟩ : syracuseStep 1369565 = 513587) (by norm_num)
theorem B1369589 : Blo 912577 1369589 := bbase (se 5 (by rfl) ⟨64199, by rfl⟩ : syracuseStep 1369589 = 128399) (by norm_num)
theorem B976393 : Blo 912577 976393 := bbase (se 2 (by rfl) ⟨366147, by rfl⟩ : syracuseStep 976393 = 732295) (by norm_num)
theorem B1369613 : Blo 912577 1369613 := bbase (se 3 (by rfl) ⟨256802, by rfl⟩ : syracuseStep 1369613 = 513605) (by norm_num)
theorem B2057741 : Blo 912577 2057741 := bbase (se 3 (by rfl) ⟨385826, by rfl⟩ : syracuseStep 2057741 = 771653) (by norm_num)
theorem B1369637 : Blo 912577 1369637 := bbase (se 4 (by rfl) ⟨128403, by rfl⟩ : syracuseStep 1369637 = 256807) (by norm_num)
theorem B1173037 : Blo 912577 1173037 := bbase (se 3 (by rfl) ⟨219944, by rfl⟩ : syracuseStep 1173037 = 439889) (by norm_num)
theorem B1369661 : Blo 912577 1369661 := bbase (se 3 (by rfl) ⟨256811, by rfl⟩ : syracuseStep 1369661 = 513623) (by norm_num)
theorem B1467973 : Blo 912577 1467973 := bbase (se 4 (by rfl) ⟨137622, by rfl⟩ : syracuseStep 1467973 = 275245) (by norm_num)
theorem B2319941 : Blo 912577 2319941 := bbase (se 4 (by rfl) ⟨217494, by rfl⟩ : syracuseStep 2319941 = 434989) (by norm_num)
theorem B1369685 : Blo 912577 1369685 := bbase (se 8 (by rfl) ⟨8025, by rfl⟩ : syracuseStep 1369685 = 16051) (by norm_num)
theorem B2057813 : Blo 912577 2057813 := bbase (se 8 (by rfl) ⟨12057, by rfl⟩ : syracuseStep 2057813 = 24115) (by norm_num)
theorem B1369709 : Blo 912577 1369709 := bbase (se 3 (by rfl) ⟨256820, by rfl⟩ : syracuseStep 1369709 = 513641) (by norm_num)
theorem B1369733 : Blo 912577 1369733 := bbase (se 4 (by rfl) ⟨128412, by rfl⟩ : syracuseStep 1369733 = 256825) (by norm_num)
theorem B1369757 : Blo 912577 1369757 := bbase (se 3 (by rfl) ⟨256829, by rfl⟩ : syracuseStep 1369757 = 513659) (by norm_num)
theorem B2057885 : Blo 912577 2057885 := bbase (se 3 (by rfl) ⟨385853, by rfl⟩ : syracuseStep 2057885 = 771707) (by norm_num)
theorem B1369781 : Blo 912577 1369781 := bbase (se 5 (by rfl) ⟨64208, by rfl⟩ : syracuseStep 1369781 = 128417) (by norm_num)
theorem B976573 : Blo 912577 976573 := bbase (se 3 (by rfl) ⟨183107, by rfl⟩ : syracuseStep 976573 = 366215) (by norm_num)
theorem B1369805 : Blo 912577 1369805 := bbase (se 3 (by rfl) ⟨256838, by rfl⟩ : syracuseStep 1369805 = 513677) (by norm_num)
theorem B1369829 : Blo 912577 1369829 := bbase (se 4 (by rfl) ⟨128421, by rfl⟩ : syracuseStep 1369829 = 256843) (by norm_num)
theorem B2057957 : Blo 912577 2057957 := bbase (se 4 (by rfl) ⟨192933, by rfl⟩ : syracuseStep 2057957 = 385867) (by norm_num)
theorem B1369853 : Blo 912577 1369853 := bbase (se 3 (by rfl) ⟨256847, by rfl⟩ : syracuseStep 1369853 = 513695) (by norm_num)
theorem B1369877 : Blo 912577 1369877 := bbase (se 6 (by rfl) ⟨32106, by rfl⟩ : syracuseStep 1369877 = 64213) (by norm_num)
theorem B1369901 : Blo 912577 1369901 := bbase (se 3 (by rfl) ⟨256856, by rfl⟩ : syracuseStep 1369901 = 513713) (by norm_num)
theorem B2058029 : Blo 912577 2058029 := bbase (se 3 (by rfl) ⟨385880, by rfl⟩ : syracuseStep 2058029 = 771761) (by norm_num)
theorem B1369925 : Blo 912577 1369925 := bbase (se 4 (by rfl) ⟨128430, by rfl⟩ : syracuseStep 1369925 = 256861) (by norm_num)
theorem B1369949 : Blo 912577 1369949 := bbase (se 3 (by rfl) ⟨256865, by rfl⟩ : syracuseStep 1369949 = 513731) (by norm_num)
theorem B1369973 : Blo 912577 1369973 := bbase (se 5 (by rfl) ⟨64217, by rfl⟩ : syracuseStep 1369973 = 128435) (by norm_num)
theorem B2058101 : Blo 912577 2058101 := bbase (se 5 (by rfl) ⟨96473, by rfl⟩ : syracuseStep 2058101 = 192947) (by norm_num)
theorem B1369997 : Blo 912577 1369997 := bbase (se 3 (by rfl) ⟨256874, by rfl⟩ : syracuseStep 1369997 = 513749) (by norm_num)
theorem B6940565 : Blo 912577 6940565 := bbase (se 6 (by rfl) ⟨162669, by rfl⟩ : syracuseStep 6940565 = 325339) (by norm_num)
theorem B1370021 : Blo 912577 1370021 := bbase (se 4 (by rfl) ⟨128439, by rfl⟩ : syracuseStep 1370021 = 256879) (by norm_num)
theorem B4515749 : Blo 912577 4515749 := bbase (se 4 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 4515749 = 846703) (by norm_num)
theorem B1370045 : Blo 912577 1370045 := bbase (se 3 (by rfl) ⟨256883, by rfl⟩ : syracuseStep 1370045 = 513767) (by norm_num)
theorem B2058173 : Blo 912577 2058173 := bbase (se 3 (by rfl) ⟨385907, by rfl⟩ : syracuseStep 2058173 = 771815) (by norm_num)
theorem B1370069 : Blo 912577 1370069 := bbase (se 7 (by rfl) ⟨16055, by rfl⟩ : syracuseStep 1370069 = 32111) (by norm_num)
theorem B1370093 : Blo 912577 1370093 := bbase (se 3 (by rfl) ⟨256892, by rfl⟩ : syracuseStep 1370093 = 513785) (by norm_num)
theorem B1370117 : Blo 912577 1370117 := bbase (se 4 (by rfl) ⟨128448, by rfl⟩ : syracuseStep 1370117 = 256897) (by norm_num)
theorem B2058245 : Blo 912577 2058245 := bbase (se 4 (by rfl) ⟨192960, by rfl⟩ : syracuseStep 2058245 = 385921) (by norm_num)
theorem B8775701 : Blo 912577 8775701 := bbase (se 6 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 8775701 = 411361) (by norm_num)
theorem B1042453 : Blo 912577 1042453 := bbase (se 6 (by rfl) ⟨24432, by rfl⟩ : syracuseStep 1042453 = 48865) (by norm_num)
theorem B1370141 : Blo 912577 1370141 := bbase (se 3 (by rfl) ⟨256901, by rfl⟩ : syracuseStep 1370141 = 513803) (by norm_num)
theorem B1370165 : Blo 912577 1370165 := bbase (se 5 (by rfl) ⟨64226, by rfl⟩ : syracuseStep 1370165 = 128453) (by norm_num)
theorem B1370189 : Blo 912577 1370189 := bbase (se 3 (by rfl) ⟨256910, by rfl⟩ : syracuseStep 1370189 = 513821) (by norm_num)
theorem B2058317 : Blo 912577 2058317 := bbase (se 3 (by rfl) ⟨385934, by rfl⟩ : syracuseStep 2058317 = 771869) (by norm_num)
theorem B1370213 : Blo 912577 1370213 := bbase (se 4 (by rfl) ⟨128457, by rfl⟩ : syracuseStep 1370213 = 256915) (by norm_num)
theorem B1304677 : Blo 912577 1304677 := bbase (se 4 (by rfl) ⟨122313, by rfl⟩ : syracuseStep 1304677 = 244627) (by norm_num)
theorem B977017 : Blo 912577 977017 := bbase (se 2 (by rfl) ⟨366381, by rfl⟩ : syracuseStep 977017 = 732763) (by norm_num)
theorem B1370237 : Blo 912577 1370237 := bbase (se 3 (by rfl) ⟨256919, by rfl⟩ : syracuseStep 1370237 = 513839) (by norm_num)
theorem B1370261 : Blo 912577 1370261 := bbase (se 6 (by rfl) ⟨32115, by rfl⟩ : syracuseStep 1370261 = 64231) (by norm_num)
theorem B2058389 : Blo 912577 2058389 := bbase (se 6 (by rfl) ⟨48243, by rfl⟩ : syracuseStep 2058389 = 96487) (by norm_num)
theorem B1370285 : Blo 912577 1370285 := bbase (se 3 (by rfl) ⟨256928, by rfl⟩ : syracuseStep 1370285 = 513857) (by norm_num)
theorem B1370309 : Blo 912577 1370309 := bbase (se 4 (by rfl) ⟨128466, by rfl⟩ : syracuseStep 1370309 = 256933) (by norm_num)
theorem B1370333 : Blo 912577 1370333 := bbase (se 3 (by rfl) ⟨256937, by rfl⟩ : syracuseStep 1370333 = 513875) (by norm_num)
theorem B2058461 : Blo 912577 2058461 := bbase (se 3 (by rfl) ⟨385961, by rfl⟩ : syracuseStep 2058461 = 771923) (by norm_num)
theorem B1370357 : Blo 912577 1370357 := bbase (se 5 (by rfl) ⟨64235, by rfl⟩ : syracuseStep 1370357 = 128471) (by norm_num)
theorem B977141 : Blo 912577 977141 := bbase (se 5 (by rfl) ⟨45803, by rfl⟩ : syracuseStep 977141 = 91607) (by norm_num)
theorem B1566965 : Blo 912577 1566965 := bbase (se 5 (by rfl) ⟨73451, by rfl⟩ : syracuseStep 1566965 = 146903) (by norm_num)
theorem B1370381 : Blo 912577 1370381 := bbase (se 3 (by rfl) ⟨256946, by rfl⟩ : syracuseStep 1370381 = 513893) (by norm_num)
theorem B1370405 : Blo 912577 1370405 := bbase (se 4 (by rfl) ⟨128475, by rfl⟩ : syracuseStep 1370405 = 256951) (by norm_num)
theorem B2058533 : Blo 912577 2058533 := bbase (se 4 (by rfl) ⟨192987, by rfl⟩ : syracuseStep 2058533 = 385975) (by norm_num)
theorem B1370429 : Blo 912577 1370429 := bbase (se 3 (by rfl) ⟨256955, by rfl⟩ : syracuseStep 1370429 = 513911) (by norm_num)
theorem B1370453 : Blo 912577 1370453 := bbase (se 10 (by rfl) ⟨2007, by rfl⟩ : syracuseStep 1370453 = 4015) (by norm_num)
theorem B1370477 : Blo 912577 1370477 := bbase (se 3 (by rfl) ⟨256964, by rfl⟩ : syracuseStep 1370477 = 513929) (by norm_num)
theorem B2058605 : Blo 912577 2058605 := bbase (se 3 (by rfl) ⟨385988, by rfl⟩ : syracuseStep 2058605 = 771977) (by norm_num)
theorem B1370501 : Blo 912577 1370501 := bbase (se 4 (by rfl) ⟨128484, by rfl⟩ : syracuseStep 1370501 = 256969) (by norm_num)
theorem B14281109 : Blo 912577 14281109 := bbase (se 6 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 14281109 = 669427) (by norm_num)
theorem B1370525 : Blo 912577 1370525 := bbase (se 3 (by rfl) ⟨256973, by rfl⟩ : syracuseStep 1370525 = 513947) (by norm_num)
theorem B1370549 : Blo 912577 1370549 := bbase (se 5 (by rfl) ⟨64244, by rfl⟩ : syracuseStep 1370549 = 128489) (by norm_num)
theorem B2058677 : Blo 912577 2058677 := bbase (se 5 (by rfl) ⟨96500, by rfl⟩ : syracuseStep 2058677 = 193001) (by norm_num)
theorem B1305013 : Blo 912577 1305013 := bbase (se 5 (by rfl) ⟨61172, by rfl⟩ : syracuseStep 1305013 = 122345) (by norm_num)
theorem B3467717 : Blo 912577 3467717 := bbase (se 4 (by rfl) ⟨325098, by rfl⟩ : syracuseStep 3467717 = 650197) (by norm_num)
theorem B1370573 : Blo 912577 1370573 := bbase (se 3 (by rfl) ⟨256982, by rfl⟩ : syracuseStep 1370573 = 513965) (by norm_num)
theorem B1370597 : Blo 912577 1370597 := bbase (se 4 (by rfl) ⟨128493, by rfl⟩ : syracuseStep 1370597 = 256987) (by norm_num)
theorem B977393 : Blo 912577 977393 := bbase (se 2 (by rfl) ⟨366522, by rfl⟩ : syracuseStep 977393 = 733045) (by norm_num)
theorem B1370621 : Blo 912577 1370621 := bbase (se 3 (by rfl) ⟨256991, by rfl⟩ : syracuseStep 1370621 = 513983) (by norm_num)
theorem B2058749 : Blo 912577 2058749 := bbase (se 3 (by rfl) ⟨386015, by rfl⟩ : syracuseStep 2058749 = 772031) (by norm_num)
theorem B1370645 : Blo 912577 1370645 := bbase (se 6 (by rfl) ⟨32124, by rfl⟩ : syracuseStep 1370645 = 64249) (by norm_num)
theorem B1370669 : Blo 912577 1370669 := bbase (se 3 (by rfl) ⟨257000, by rfl⟩ : syracuseStep 1370669 = 514001) (by norm_num)
theorem B1370693 : Blo 912577 1370693 := bbase (se 4 (by rfl) ⟨128502, by rfl⟩ : syracuseStep 1370693 = 257005) (by norm_num)
theorem B2058821 : Blo 912577 2058821 := bbase (se 4 (by rfl) ⟨193014, by rfl⟩ : syracuseStep 2058821 = 386029) (by norm_num)
theorem B1370717 : Blo 912577 1370717 := bbase (se 3 (by rfl) ⟨257009, by rfl⟩ : syracuseStep 1370717 = 514019) (by norm_num)
theorem B1567333 : Blo 912577 1567333 := bbase (se 4 (by rfl) ⟨146937, by rfl⟩ : syracuseStep 1567333 = 293875) (by norm_num)
theorem B1370741 : Blo 912577 1370741 := bbase (se 5 (by rfl) ⟨64253, by rfl⟩ : syracuseStep 1370741 = 128507) (by norm_num)
theorem B1370765 : Blo 912577 1370765 := bbase (se 3 (by rfl) ⟨257018, by rfl⟩ : syracuseStep 1370765 = 514037) (by norm_num)
theorem B2058893 : Blo 912577 2058893 := bbase (se 3 (by rfl) ⟨386042, by rfl⟩ : syracuseStep 2058893 = 772085) (by norm_num)
theorem B1370789 : Blo 912577 1370789 := bbase (se 4 (by rfl) ⟨128511, by rfl⟩ : syracuseStep 1370789 = 257023) (by norm_num)
theorem B1370813 : Blo 912577 1370813 := bbase (se 3 (by rfl) ⟨257027, by rfl⟩ : syracuseStep 1370813 = 514055) (by norm_num)
theorem B1370837 : Blo 912577 1370837 := bbase (se 7 (by rfl) ⟨16064, by rfl⟩ : syracuseStep 1370837 = 32129) (by norm_num)
theorem B2058965 : Blo 912577 2058965 := bbase (se 7 (by rfl) ⟨24128, by rfl⟩ : syracuseStep 2058965 = 48257) (by norm_num)
theorem B3468005 : Blo 912577 3468005 := bbase (se 4 (by rfl) ⟨325125, by rfl⟩ : syracuseStep 3468005 = 650251) (by norm_num)
theorem B1370861 : Blo 912577 1370861 := bbase (se 3 (by rfl) ⟨257036, by rfl⟩ : syracuseStep 1370861 = 514073) (by norm_num)
theorem B1370885 : Blo 912577 1370885 := bbase (se 4 (by rfl) ⟨128520, by rfl⟩ : syracuseStep 1370885 = 257041) (by norm_num)
theorem B1370909 : Blo 912577 1370909 := bbase (se 3 (by rfl) ⟨257045, by rfl⟩ : syracuseStep 1370909 = 514091) (by norm_num)
theorem B2059037 : Blo 912577 2059037 := bbase (se 3 (by rfl) ⟨386069, by rfl⟩ : syracuseStep 2059037 = 772139) (by norm_num)
theorem B1370933 : Blo 912577 1370933 := bbase (se 5 (by rfl) ⟨64262, by rfl⟩ : syracuseStep 1370933 = 128525) (by norm_num)
theorem B1370957 : Blo 912577 1370957 := bbase (se 3 (by rfl) ⟨257054, by rfl⟩ : syracuseStep 1370957 = 514109) (by norm_num)
theorem B1370981 : Blo 912577 1370981 := bbase (se 4 (by rfl) ⟨128529, by rfl⟩ : syracuseStep 1370981 = 257059) (by norm_num)
theorem B2059109 : Blo 912577 2059109 := bbase (se 4 (by rfl) ⟨193041, by rfl⟩ : syracuseStep 2059109 = 386083) (by norm_num)
theorem B1371005 : Blo 912577 1371005 := bbase (se 3 (by rfl) ⟨257063, by rfl⟩ : syracuseStep 1371005 = 514127) (by norm_num)
theorem B1371029 : Blo 912577 1371029 := bbase (se 6 (by rfl) ⟨32133, by rfl⟩ : syracuseStep 1371029 = 64267) (by norm_num)
theorem B1371053 : Blo 912577 1371053 := bbase (se 3 (by rfl) ⟨257072, by rfl⟩ : syracuseStep 1371053 = 514145) (by norm_num)
theorem B2059181 : Blo 912577 2059181 := bbase (se 3 (by rfl) ⟨386096, by rfl⟩ : syracuseStep 2059181 = 772193) (by norm_num)
theorem B977837 : Blo 912577 977837 := bbase (se 3 (by rfl) ⟨183344, by rfl⟩ : syracuseStep 977837 = 366689) (by norm_num)
theorem B1043389 : Blo 912577 1043389 := bbase (se 3 (by rfl) ⟨195635, by rfl⟩ : syracuseStep 1043389 = 391271) (by norm_num)
theorem B1371077 : Blo 912577 1371077 := bbase (se 4 (by rfl) ⟨128538, by rfl⟩ : syracuseStep 1371077 = 257077) (by norm_num)
theorem B3959765 : Blo 912577 3959765 := bbase (se 7 (by rfl) ⟨46403, by rfl⟩ : syracuseStep 3959765 = 92807) (by norm_num)
theorem B1371101 : Blo 912577 1371101 := bbase (se 3 (by rfl) ⟨257081, by rfl⟩ : syracuseStep 1371101 = 514163) (by norm_num)
theorem B1371125 : Blo 912577 1371125 := bbase (se 5 (by rfl) ⟨64271, by rfl⟩ : syracuseStep 1371125 = 128543) (by norm_num)
theorem B2059253 : Blo 912577 2059253 := bbase (se 5 (by rfl) ⟨96527, by rfl⟩ : syracuseStep 2059253 = 193055) (by norm_num)
theorem B1371149 : Blo 912577 1371149 := bbase (se 3 (by rfl) ⟨257090, by rfl⟩ : syracuseStep 1371149 = 514181) (by norm_num)
theorem B7826453 : Blo 912577 7826453 := bbase (se 6 (by rfl) ⟨183432, by rfl⟩ : syracuseStep 7826453 = 366865) (by norm_num)
theorem B1371173 : Blo 912577 1371173 := bbase (se 4 (by rfl) ⟨128547, by rfl⟩ : syracuseStep 1371173 = 257095) (by norm_num)
theorem B1371197 : Blo 912577 1371197 := bbase (se 3 (by rfl) ⟨257099, by rfl⟩ : syracuseStep 1371197 = 514199) (by norm_num)
theorem B2059325 : Blo 912577 2059325 := bbase (se 3 (by rfl) ⟨386123, by rfl⟩ : syracuseStep 2059325 = 772247) (by norm_num)
theorem B1371221 : Blo 912577 1371221 := bbase (se 8 (by rfl) ⟨8034, by rfl⟩ : syracuseStep 1371221 = 16069) (by norm_num)
theorem B1371245 : Blo 912577 1371245 := bbase (se 3 (by rfl) ⟨257108, by rfl⟩ : syracuseStep 1371245 = 514217) (by norm_num)
theorem B1371269 : Blo 912577 1371269 := bbase (se 4 (by rfl) ⟨128556, by rfl⟩ : syracuseStep 1371269 = 257113) (by norm_num)
theorem B2059397 : Blo 912577 2059397 := bbase (se 4 (by rfl) ⟨193068, by rfl⟩ : syracuseStep 2059397 = 386137) (by norm_num)
theorem B1371293 : Blo 912577 1371293 := bbase (se 3 (by rfl) ⟨257117, by rfl⟩ : syracuseStep 1371293 = 514235) (by norm_num)
theorem B978085 : Blo 912577 978085 := bbase (se 4 (by rfl) ⟨91695, by rfl⟩ : syracuseStep 978085 = 183391) (by norm_num)
theorem B1371317 : Blo 912577 1371317 := bbase (se 5 (by rfl) ⟨64280, by rfl⟩ : syracuseStep 1371317 = 128561) (by norm_num)
theorem B1371341 : Blo 912577 1371341 := bbase (se 3 (by rfl) ⟨257126, by rfl⟩ : syracuseStep 1371341 = 514253) (by norm_num)
theorem B2059469 : Blo 912577 2059469 := bbase (se 3 (by rfl) ⟨386150, by rfl⟩ : syracuseStep 2059469 = 772301) (by norm_num)
theorem B1371365 : Blo 912577 1371365 := bbase (se 4 (by rfl) ⟨128565, by rfl⟩ : syracuseStep 1371365 = 257131) (by norm_num)
theorem B1371389 : Blo 912577 1371389 := bbase (se 3 (by rfl) ⟨257135, by rfl⟩ : syracuseStep 1371389 = 514271) (by norm_num)
theorem B1371413 : Blo 912577 1371413 := bbase (se 6 (by rfl) ⟨32142, by rfl⟩ : syracuseStep 1371413 = 64285) (by norm_num)
theorem B2059541 : Blo 912577 2059541 := bbase (se 6 (by rfl) ⟨48270, by rfl⟩ : syracuseStep 2059541 = 96541) (by norm_num)
theorem B1371437 : Blo 912577 1371437 := bbase (se 3 (by rfl) ⟨257144, by rfl⟩ : syracuseStep 1371437 = 514289) (by norm_num)
theorem B1371461 : Blo 912577 1371461 := bbase (se 4 (by rfl) ⟨128574, by rfl⟩ : syracuseStep 1371461 = 257149) (by norm_num)
theorem B1371485 : Blo 912577 1371485 := bbase (se 3 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 1371485 = 514307) (by norm_num)
theorem B2059613 : Blo 912577 2059613 := bbase (se 3 (by rfl) ⟨386177, by rfl⟩ : syracuseStep 2059613 = 772355) (by norm_num)
theorem B1371509 : Blo 912577 1371509 := bbase (se 5 (by rfl) ⟨64289, by rfl⟩ : syracuseStep 1371509 = 128579) (by norm_num)
theorem B1371533 : Blo 912577 1371533 := bbase (se 3 (by rfl) ⟨257162, by rfl⟩ : syracuseStep 1371533 = 514325) (by norm_num)
theorem B1371557 : Blo 912577 1371557 := bbase (se 4 (by rfl) ⟨128583, by rfl⟩ : syracuseStep 1371557 = 257167) (by norm_num)
theorem B2059685 : Blo 912577 2059685 := bbase (se 4 (by rfl) ⟨193095, by rfl⟩ : syracuseStep 2059685 = 386191) (by norm_num)
theorem B1371581 : Blo 912577 1371581 := bbase (se 3 (by rfl) ⟨257171, by rfl⟩ : syracuseStep 1371581 = 514343) (by norm_num)
theorem B1371605 : Blo 912577 1371605 := bbase (se 7 (by rfl) ⟨16073, by rfl⟩ : syracuseStep 1371605 = 32147) (by norm_num)
theorem B1371629 : Blo 912577 1371629 := bbase (se 3 (by rfl) ⟨257180, by rfl⟩ : syracuseStep 1371629 = 514361) (by norm_num)
theorem B2059757 : Blo 912577 2059757 := bbase (se 3 (by rfl) ⟨386204, by rfl⟩ : syracuseStep 2059757 = 772409) (by norm_num)
theorem B1371653 : Blo 912577 1371653 := bbase (se 4 (by rfl) ⟨128592, by rfl⟩ : syracuseStep 1371653 = 257185) (by norm_num)
theorem B1371677 : Blo 912577 1371677 := bbase (se 3 (by rfl) ⟨257189, by rfl⟩ : syracuseStep 1371677 = 514379) (by norm_num)
theorem B1175089 : Blo 912577 1175089 := bbase (se 2 (by rfl) ⟨440658, by rfl⟩ : syracuseStep 1175089 = 881317) (by norm_num)
theorem B1371701 : Blo 912577 1371701 := bbase (se 5 (by rfl) ⟨64298, by rfl⟩ : syracuseStep 1371701 = 128597) (by norm_num)
theorem B2059829 : Blo 912577 2059829 := bbase (se 5 (by rfl) ⟨96554, by rfl⟩ : syracuseStep 2059829 = 193109) (by norm_num)
theorem B1371725 : Blo 912577 1371725 := bbase (se 3 (by rfl) ⟨257198, by rfl⟩ : syracuseStep 1371725 = 514397) (by norm_num)
theorem B978529 : Blo 912577 978529 := bbase (se 2 (by rfl) ⟨366948, by rfl⟩ : syracuseStep 978529 = 733897) (by norm_num)
theorem B1371749 : Blo 912577 1371749 := bbase (se 4 (by rfl) ⟨128601, by rfl⟩ : syracuseStep 1371749 = 257203) (by norm_num)
theorem B1371773 : Blo 912577 1371773 := bbase (se 3 (by rfl) ⟨257207, by rfl⟩ : syracuseStep 1371773 = 514415) (by norm_num)
theorem B2059901 : Blo 912577 2059901 := bbase (se 3 (by rfl) ⟨386231, by rfl⟩ : syracuseStep 2059901 = 772463) (by norm_num)
theorem B5205653 : Blo 912577 5205653 := bbase (se 6 (by rfl) ⟨122007, by rfl⟩ : syracuseStep 5205653 = 244015) (by norm_num)
theorem B1371797 : Blo 912577 1371797 := bbase (se 6 (by rfl) ⟨32151, by rfl⟩ : syracuseStep 1371797 = 64303) (by norm_num)
theorem B978589 : Blo 912577 978589 := bbase (se 3 (by rfl) ⟨183485, by rfl⟩ : syracuseStep 978589 = 366971) (by norm_num)
theorem B1371821 : Blo 912577 1371821 := bbase (se 3 (by rfl) ⟨257216, by rfl⟩ : syracuseStep 1371821 = 514433) (by norm_num)
theorem B1044149 : Blo 912577 1044149 := bbase (se 5 (by rfl) ⟨48944, by rfl⟩ : syracuseStep 1044149 = 97889) (by norm_num)
theorem B1175233 : Blo 912577 1175233 := bbase (se 2 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 1175233 = 881425) (by norm_num)
theorem B1371845 : Blo 912577 1371845 := bbase (se 4 (by rfl) ⟨128610, by rfl⟩ : syracuseStep 1371845 = 257221) (by norm_num)
theorem B2059973 : Blo 912577 2059973 := bbase (se 4 (by rfl) ⟨193122, by rfl⟩ : syracuseStep 2059973 = 386245) (by norm_num)
theorem B2223821 : Blo 912577 2223821 := bbase (se 3 (by rfl) ⟨416966, by rfl⟩ : syracuseStep 2223821 = 833933) (by norm_num)
theorem B1371869 : Blo 912577 1371869 := bbase (se 3 (by rfl) ⟨257225, by rfl⟩ : syracuseStep 1371869 = 514451) (by norm_num)
theorem B6582005 : Blo 912577 6582005 := bbase (se 5 (by rfl) ⟨308531, by rfl⟩ : syracuseStep 6582005 = 617063) (by norm_num)
theorem B1371893 : Blo 912577 1371893 := bbase (se 5 (by rfl) ⟨64307, by rfl⟩ : syracuseStep 1371893 = 128615) (by norm_num)
theorem B1371917 : Blo 912577 1371917 := bbase (se 3 (by rfl) ⟨257234, by rfl⟩ : syracuseStep 1371917 = 514469) (by norm_num)
theorem B2060045 : Blo 912577 2060045 := bbase (se 3 (by rfl) ⟨386258, by rfl⟩ : syracuseStep 2060045 = 772517) (by norm_num)
theorem B1568533 : Blo 912577 1568533 := bbase (se 6 (by rfl) ⟨36762, by rfl⟩ : syracuseStep 1568533 = 73525) (by norm_num)
theorem B1371941 : Blo 912577 1371941 := bbase (se 4 (by rfl) ⟨128619, by rfl⟩ : syracuseStep 1371941 = 257239) (by norm_num)
theorem B1371965 : Blo 912577 1371965 := bbase (se 3 (by rfl) ⟨257243, by rfl⟩ : syracuseStep 1371965 = 514487) (by norm_num)
theorem B1371989 : Blo 912577 1371989 := bbase (se 9 (by rfl) ⟨4019, by rfl⟩ : syracuseStep 1371989 = 8039) (by norm_num)
theorem B2060117 : Blo 912577 2060117 := bbase (se 9 (by rfl) ⟨6035, by rfl⟩ : syracuseStep 2060117 = 12071) (by norm_num)
theorem B1372013 : Blo 912577 1372013 := bbase (se 3 (by rfl) ⟨257252, by rfl⟩ : syracuseStep 1372013 = 514505) (by norm_num)
theorem B3469189 : Blo 912577 3469189 := bbase (se 4 (by rfl) ⟨325236, by rfl⟩ : syracuseStep 3469189 = 650473) (by norm_num)
theorem B1372037 : Blo 912577 1372037 := bbase (se 4 (by rfl) ⟨128628, by rfl⟩ : syracuseStep 1372037 = 257257) (by norm_num)
theorem B1372061 : Blo 912577 1372061 := bbase (se 3 (by rfl) ⟨257261, by rfl⟩ : syracuseStep 1372061 = 514523) (by norm_num)
theorem B2060189 : Blo 912577 2060189 := bbase (se 3 (by rfl) ⟨386285, by rfl⟩ : syracuseStep 2060189 = 772571) (by norm_num)
theorem B1372085 : Blo 912577 1372085 := bbase (se 5 (by rfl) ⟨64316, by rfl⟩ : syracuseStep 1372085 = 128633) (by norm_num)
theorem B1372109 : Blo 912577 1372109 := bbase (se 3 (by rfl) ⟨257270, by rfl⟩ : syracuseStep 1372109 = 514541) (by norm_num)
theorem B4386773 : Blo 912577 4386773 := bbase (se 7 (by rfl) ⟨51407, by rfl⟩ : syracuseStep 4386773 = 102815) (by norm_num)
theorem B1372133 : Blo 912577 1372133 := bbase (se 4 (by rfl) ⟨128637, by rfl⟩ : syracuseStep 1372133 = 257275) (by norm_num)
theorem B2060261 : Blo 912577 2060261 := bbase (se 4 (by rfl) ⟨193149, by rfl⟩ : syracuseStep 2060261 = 386299) (by norm_num)
theorem B1372157 : Blo 912577 1372157 := bbase (se 3 (by rfl) ⟨257279, by rfl⟩ : syracuseStep 1372157 = 514559) (by norm_num)
theorem B1372181 : Blo 912577 1372181 := bbase (se 6 (by rfl) ⟨32160, by rfl⟩ : syracuseStep 1372181 = 64321) (by norm_num)
theorem B1372205 : Blo 912577 1372205 := bbase (se 3 (by rfl) ⟨257288, by rfl⟩ : syracuseStep 1372205 = 514577) (by norm_num)
theorem B2060333 : Blo 912577 2060333 := bbase (se 3 (by rfl) ⟨386312, by rfl⟩ : syracuseStep 2060333 = 772625) (by norm_num)
theorem B1372229 : Blo 912577 1372229 := bbase (se 4 (by rfl) ⟨128646, by rfl⟩ : syracuseStep 1372229 = 257293) (by norm_num)
theorem B1372253 : Blo 912577 1372253 := bbase (se 3 (by rfl) ⟨257297, by rfl⟩ : syracuseStep 1372253 = 514595) (by norm_num)
theorem B1372277 : Blo 912577 1372277 := bbase (se 5 (by rfl) ⟨64325, by rfl⟩ : syracuseStep 1372277 = 128651) (by norm_num)
theorem B2060405 : Blo 912577 2060405 := bbase (se 5 (by rfl) ⟨96581, by rfl⟩ : syracuseStep 2060405 = 193163) (by norm_num)
theorem B1372301 : Blo 912577 1372301 := bbase (se 3 (by rfl) ⟨257306, by rfl⟩ : syracuseStep 1372301 = 514613) (by norm_num)
theorem B1732765 : Blo 912577 1732765 := bbase (se 3 (by rfl) ⟨324893, by rfl⟩ : syracuseStep 1732765 = 649787) (by norm_num)
theorem B1372325 : Blo 912577 1372325 := bbase (se 4 (by rfl) ⟨128655, by rfl⟩ : syracuseStep 1372325 = 257311) (by norm_num)
theorem B3469493 : Blo 912577 3469493 := bbase (se 5 (by rfl) ⟨162632, by rfl⟩ : syracuseStep 3469493 = 325265) (by norm_num)
theorem B1372349 : Blo 912577 1372349 := bbase (se 3 (by rfl) ⟨257315, by rfl⟩ : syracuseStep 1372349 = 514631) (by norm_num)
theorem B2060477 : Blo 912577 2060477 := bbase (se 3 (by rfl) ⟨386339, by rfl⟩ : syracuseStep 2060477 = 772679) (by norm_num)
theorem B1372373 : Blo 912577 1372373 := bbase (se 7 (by rfl) ⟨16082, by rfl⟩ : syracuseStep 1372373 = 32165) (by norm_num)
theorem B1372397 : Blo 912577 1372397 := bbase (se 3 (by rfl) ⟨257324, by rfl⟩ : syracuseStep 1372397 = 514649) (by norm_num)
theorem B1372421 : Blo 912577 1372421 := bbase (se 4 (by rfl) ⟨128664, by rfl⟩ : syracuseStep 1372421 = 257329) (by norm_num)
theorem B2060549 : Blo 912577 2060549 := bbase (se 4 (by rfl) ⟨193176, by rfl⟩ : syracuseStep 2060549 = 386353) (by norm_num)
theorem B1372445 : Blo 912577 1372445 := bbase (se 3 (by rfl) ⟨257333, by rfl⟩ : syracuseStep 1372445 = 514667) (by norm_num)
theorem B1732909 : Blo 912577 1732909 := bbase (se 3 (by rfl) ⟨324920, by rfl⟩ : syracuseStep 1732909 = 649841) (by norm_num)
theorem B1372469 : Blo 912577 1372469 := bbase (se 5 (by rfl) ⟨64334, by rfl⟩ : syracuseStep 1372469 = 128669) (by norm_num)
theorem B1372493 : Blo 912577 1372493 := bbase (se 3 (by rfl) ⟨257342, by rfl⟩ : syracuseStep 1372493 = 514685) (by norm_num)
theorem B2060621 : Blo 912577 2060621 := bbase (se 3 (by rfl) ⟨386366, by rfl⟩ : syracuseStep 2060621 = 772733) (by norm_num)
theorem B5566805 : Blo 912577 5566805 := bbase (se 10 (by rfl) ⟨8154, by rfl⟩ : syracuseStep 5566805 = 16309) (by norm_num)
theorem B1372517 : Blo 912577 1372517 := bbase (se 4 (by rfl) ⟨128673, by rfl⟩ : syracuseStep 1372517 = 257347) (by norm_num)
theorem B1372541 : Blo 912577 1372541 := bbase (se 3 (by rfl) ⟨257351, by rfl⟩ : syracuseStep 1372541 = 514703) (by norm_num)
theorem B2781589 : Blo 912577 2781589 := bbase (se 6 (by rfl) ⟨65193, by rfl⟩ : syracuseStep 2781589 = 130387) (by norm_num)
theorem B1372565 : Blo 912577 1372565 := bbase (se 6 (by rfl) ⟨32169, by rfl⟩ : syracuseStep 1372565 = 64339) (by norm_num)
theorem B2060693 : Blo 912577 2060693 := bbase (se 6 (by rfl) ⟨48297, by rfl⟩ : syracuseStep 2060693 = 96595) (by norm_num)
theorem B1372589 : Blo 912577 1372589 := bbase (se 3 (by rfl) ⟨257360, by rfl⟩ : syracuseStep 1372589 = 514721) (by norm_num)
theorem B1372613 : Blo 912577 1372613 := bbase (se 4 (by rfl) ⟨128682, by rfl⟩ : syracuseStep 1372613 = 257365) (by norm_num)
theorem B1733069 : Blo 912577 1733069 := bbase (se 3 (by rfl) ⟨324950, by rfl⟩ : syracuseStep 1733069 = 649901) (by norm_num)
theorem B1372637 : Blo 912577 1372637 := bbase (se 3 (by rfl) ⟨257369, by rfl⟩ : syracuseStep 1372637 = 514739) (by norm_num)
theorem B2060765 : Blo 912577 2060765 := bbase (se 3 (by rfl) ⟨386393, by rfl⟩ : syracuseStep 2060765 = 772787) (by norm_num)
theorem B1372661 : Blo 912577 1372661 := bbase (se 5 (by rfl) ⟨64343, by rfl⟩ : syracuseStep 1372661 = 128687) (by norm_num)
theorem B1372685 : Blo 912577 1372685 := bbase (se 3 (by rfl) ⟨257378, by rfl⟩ : syracuseStep 1372685 = 514757) (by norm_num)
theorem B1372709 : Blo 912577 1372709 := bbase (se 4 (by rfl) ⟨128691, by rfl⟩ : syracuseStep 1372709 = 257383) (by norm_num)
theorem B2060837 : Blo 912577 2060837 := bbase (se 4 (by rfl) ⟨193203, by rfl⟩ : syracuseStep 2060837 = 386407) (by norm_num)
theorem B1372733 : Blo 912577 1372733 := bbase (se 3 (by rfl) ⟨257387, by rfl⟩ : syracuseStep 1372733 = 514775) (by norm_num)
theorem B1372757 : Blo 912577 1372757 := bbase (se 8 (by rfl) ⟨8043, by rfl⟩ : syracuseStep 1372757 = 16087) (by norm_num)
theorem B1733213 : Blo 912577 1733213 := bbase (se 3 (by rfl) ⟨324977, by rfl⟩ : syracuseStep 1733213 = 649955) (by norm_num)
theorem B1372781 : Blo 912577 1372781 := bbase (se 3 (by rfl) ⟨257396, by rfl⟩ : syracuseStep 1372781 = 514793) (by norm_num)
theorem B2060909 : Blo 912577 2060909 := bbase (se 3 (by rfl) ⟨386420, by rfl⟩ : syracuseStep 2060909 = 772841) (by norm_num)
theorem B1372805 : Blo 912577 1372805 := bbase (se 4 (by rfl) ⟨128700, by rfl⟩ : syracuseStep 1372805 = 257401) (by norm_num)
theorem B1372829 : Blo 912577 1372829 := bbase (se 3 (by rfl) ⟨257405, by rfl⟩ : syracuseStep 1372829 = 514811) (by norm_num)
theorem B1372853 : Blo 912577 1372853 := bbase (se 5 (by rfl) ⟨64352, by rfl⟩ : syracuseStep 1372853 = 128705) (by norm_num)
theorem B2060981 : Blo 912577 2060981 := bbase (se 5 (by rfl) ⟨96608, by rfl⟩ : syracuseStep 2060981 = 193217) (by norm_num)
theorem B1045181 : Blo 912577 1045181 := bbase (se 3 (by rfl) ⟨195971, by rfl⟩ : syracuseStep 1045181 = 391943) (by norm_num)
theorem B1372877 : Blo 912577 1372877 := bbase (se 3 (by rfl) ⟨257414, by rfl⟩ : syracuseStep 1372877 = 514829) (by norm_num)
theorem B7533269 : Blo 912577 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B1372901 : Blo 912577 1372901 := bbase (se 4 (by rfl) ⟨128709, by rfl⟩ : syracuseStep 1372901 = 257419) (by norm_num)
theorem B1372925 : Blo 912577 1372925 := bbase (se 3 (by rfl) ⟨257423, by rfl⟩ : syracuseStep 1372925 = 514847) (by norm_num)
theorem B2061053 : Blo 912577 2061053 := bbase (se 3 (by rfl) ⟨386447, by rfl⟩ : syracuseStep 2061053 = 772895) (by norm_num)
theorem B1372949 : Blo 912577 1372949 := bbase (se 6 (by rfl) ⟨32178, by rfl⟩ : syracuseStep 1372949 = 64357) (by norm_num)
theorem B1372973 : Blo 912577 1372973 := bbase (se 3 (by rfl) ⟨257432, by rfl⟩ : syracuseStep 1372973 = 514865) (by norm_num)
theorem B1372997 : Blo 912577 1372997 := bbase (se 4 (by rfl) ⟨128718, by rfl⟩ : syracuseStep 1372997 = 257437) (by norm_num)
theorem B2061125 : Blo 912577 2061125 := bbase (se 4 (by rfl) ⟨193230, by rfl⟩ : syracuseStep 2061125 = 386461) (by norm_num)
theorem B4944725 : Blo 912577 4944725 := bbase (se 9 (by rfl) ⟨14486, by rfl⟩ : syracuseStep 4944725 = 28973) (by norm_num)
theorem B1373021 : Blo 912577 1373021 := bbase (se 3 (by rfl) ⟨257441, by rfl⟩ : syracuseStep 1373021 = 514883) (by norm_num)
theorem B1373045 : Blo 912577 1373045 := bbase (se 5 (by rfl) ⟨64361, by rfl⟩ : syracuseStep 1373045 = 128723) (by norm_num)
theorem B1733501 : Blo 912577 1733501 := bbase (se 3 (by rfl) ⟨325031, by rfl⟩ : syracuseStep 1733501 = 650063) (by norm_num)
theorem B1373069 : Blo 912577 1373069 := bbase (se 3 (by rfl) ⟨257450, by rfl⟩ : syracuseStep 1373069 = 514901) (by norm_num)
theorem B2061197 : Blo 912577 2061197 := bbase (se 3 (by rfl) ⟨386474, by rfl⟩ : syracuseStep 2061197 = 772949) (by norm_num)
theorem B1373093 : Blo 912577 1373093 := bbase (se 4 (by rfl) ⟨128727, by rfl⟩ : syracuseStep 1373093 = 257455) (by norm_num)
theorem B1373117 : Blo 912577 1373117 := bbase (se 3 (by rfl) ⟨257459, by rfl⟩ : syracuseStep 1373117 = 514919) (by norm_num)
theorem B1373141 : Blo 912577 1373141 := bbase (se 7 (by rfl) ⟨16091, by rfl⟩ : syracuseStep 1373141 = 32183) (by norm_num)
theorem B2061269 : Blo 912577 2061269 := bbase (se 7 (by rfl) ⟨24155, by rfl⟩ : syracuseStep 2061269 = 48311) (by norm_num)
theorem B1373165 : Blo 912577 1373165 := bbase (se 3 (by rfl) ⟨257468, by rfl⟩ : syracuseStep 1373165 = 514937) (by norm_num)
theorem B1373189 : Blo 912577 1373189 := bbase (se 4 (by rfl) ⟨128736, by rfl⟩ : syracuseStep 1373189 = 257473) (by norm_num)
theorem B1733653 : Blo 912577 1733653 := bbase (se 6 (by rfl) ⟨40632, by rfl⟩ : syracuseStep 1733653 = 81265) (by norm_num)
theorem B1373213 : Blo 912577 1373213 := bbase (se 3 (by rfl) ⟨257477, by rfl⟩ : syracuseStep 1373213 = 514955) (by norm_num)
theorem B2061341 : Blo 912577 2061341 := bbase (se 3 (by rfl) ⟨386501, by rfl⟩ : syracuseStep 2061341 = 773003) (by norm_num)
theorem B1373237 : Blo 912577 1373237 := bbase (se 5 (by rfl) ⟨64370, by rfl⟩ : syracuseStep 1373237 = 128741) (by norm_num)
theorem B1373261 : Blo 912577 1373261 := bbase (se 3 (by rfl) ⟨257486, by rfl⟩ : syracuseStep 1373261 = 514973) (by norm_num)
theorem B1373285 : Blo 912577 1373285 := bbase (se 4 (by rfl) ⟨128745, by rfl⟩ : syracuseStep 1373285 = 257491) (by norm_num)
theorem B2061413 : Blo 912577 2061413 := bbase (se 4 (by rfl) ⟨193257, by rfl⟩ : syracuseStep 2061413 = 386515) (by norm_num)
theorem B1373309 : Blo 912577 1373309 := bbase (se 3 (by rfl) ⟨257495, by rfl⟩ : syracuseStep 1373309 = 514991) (by norm_num)
theorem B1373333 : Blo 912577 1373333 := bbase (se 6 (by rfl) ⟨32187, by rfl⟩ : syracuseStep 1373333 = 64375) (by norm_num)
theorem B1373357 : Blo 912577 1373357 := bbase (se 3 (by rfl) ⟨257504, by rfl⟩ : syracuseStep 1373357 = 515009) (by norm_num)
theorem B2061485 : Blo 912577 2061485 := bbase (se 3 (by rfl) ⟨386528, by rfl⟩ : syracuseStep 2061485 = 773057) (by norm_num)
theorem B1373381 : Blo 912577 1373381 := bbase (se 4 (by rfl) ⟨128754, by rfl⟩ : syracuseStep 1373381 = 257509) (by norm_num)
theorem B1373405 : Blo 912577 1373405 := bbase (se 3 (by rfl) ⟨257513, by rfl⟩ : syracuseStep 1373405 = 515027) (by norm_num)
theorem B1373429 : Blo 912577 1373429 := bbase (se 5 (by rfl) ⟨64379, by rfl⟩ : syracuseStep 1373429 = 128759) (by norm_num)
theorem B2061557 : Blo 912577 2061557 := bbase (se 5 (by rfl) ⟨96635, by rfl⟩ : syracuseStep 2061557 = 193271) (by norm_num)
theorem B1373453 : Blo 912577 1373453 := bbase (se 3 (by rfl) ⟨257522, by rfl⟩ : syracuseStep 1373453 = 515045) (by norm_num)
theorem B1373477 : Blo 912577 1373477 := bbase (se 4 (by rfl) ⟨128763, by rfl⟩ : syracuseStep 1373477 = 257527) (by norm_num)
theorem B1373501 : Blo 912577 1373501 := bbase (se 3 (by rfl) ⟨257531, by rfl⟩ : syracuseStep 1373501 = 515063) (by norm_num)
theorem B2061629 : Blo 912577 2061629 := bbase (se 3 (by rfl) ⟨386555, by rfl⟩ : syracuseStep 2061629 = 773111) (by norm_num)
theorem B1733957 : Blo 912577 1733957 := bbase (se 4 (by rfl) ⟨162558, by rfl⟩ : syracuseStep 1733957 = 325117) (by norm_num)
theorem B17593685 : Blo 912577 17593685 := bbase (se 13 (by rfl) ⟨3221, by rfl⟩ : syracuseStep 17593685 = 6443) (by norm_num)
theorem B1373525 : Blo 912577 1373525 := bbase (se 13 (by rfl) ⟨251, by rfl⟩ : syracuseStep 1373525 = 503) (by norm_num)
theorem B1373549 : Blo 912577 1373549 := bbase (se 3 (by rfl) ⟨257540, by rfl⟩ : syracuseStep 1373549 = 515081) (by norm_num)
theorem B1373573 : Blo 912577 1373573 := bbase (se 4 (by rfl) ⟨128772, by rfl⟩ : syracuseStep 1373573 = 257545) (by norm_num)
theorem B2061701 : Blo 912577 2061701 := bbase (se 4 (by rfl) ⟨193284, by rfl⟩ : syracuseStep 2061701 = 386569) (by norm_num)
theorem B1373597 : Blo 912577 1373597 := bbase (se 3 (by rfl) ⟨257549, by rfl⟩ : syracuseStep 1373597 = 515099) (by norm_num)
theorem B1373621 : Blo 912577 1373621 := bbase (se 5 (by rfl) ⟨64388, by rfl⟩ : syracuseStep 1373621 = 128777) (by norm_num)
theorem B1373645 : Blo 912577 1373645 := bbase (se 3 (by rfl) ⟨257558, by rfl⟩ : syracuseStep 1373645 = 515117) (by norm_num)
theorem B2061773 : Blo 912577 2061773 := bbase (se 3 (by rfl) ⟨386582, by rfl⟩ : syracuseStep 2061773 = 773165) (by norm_num)
theorem B1373669 : Blo 912577 1373669 := bbase (se 4 (by rfl) ⟨128781, by rfl⟩ : syracuseStep 1373669 = 257563) (by norm_num)
theorem B1373693 : Blo 912577 1373693 := bbase (se 3 (by rfl) ⟨257567, by rfl⟩ : syracuseStep 1373693 = 515135) (by norm_num)
theorem B1373717 : Blo 912577 1373717 := bbase (se 6 (by rfl) ⟨32196, by rfl⟩ : syracuseStep 1373717 = 64393) (by norm_num)
theorem B2061845 : Blo 912577 2061845 := bbase (se 6 (by rfl) ⟨48324, by rfl⟩ : syracuseStep 2061845 = 96649) (by norm_num)
theorem B1373741 : Blo 912577 1373741 := bbase (se 3 (by rfl) ⟨257576, by rfl⟩ : syracuseStep 1373741 = 515153) (by norm_num)
theorem B1373765 : Blo 912577 1373765 := bbase (se 4 (by rfl) ⟨128790, by rfl⟩ : syracuseStep 1373765 = 257581) (by norm_num)
theorem B1373789 : Blo 912577 1373789 := bbase (se 3 (by rfl) ⟨257585, by rfl⟩ : syracuseStep 1373789 = 515171) (by norm_num)
theorem B2061917 : Blo 912577 2061917 := bbase (se 3 (by rfl) ⟨386609, by rfl⟩ : syracuseStep 2061917 = 773219) (by norm_num)
theorem B1373813 : Blo 912577 1373813 := bbase (se 5 (by rfl) ⟨64397, by rfl⟩ : syracuseStep 1373813 = 128795) (by norm_num)
theorem B1373837 : Blo 912577 1373837 := bbase (se 3 (by rfl) ⟨257594, by rfl⟩ : syracuseStep 1373837 = 515189) (by norm_num)
theorem B3176101 : Blo 912577 3176101 := bbase (se 4 (by rfl) ⟨297759, by rfl⟩ : syracuseStep 3176101 = 595519) (by norm_num)
theorem B1373861 : Blo 912577 1373861 := bbase (se 4 (by rfl) ⟨128799, by rfl⟩ : syracuseStep 1373861 = 257599) (by norm_num)
theorem B2061989 : Blo 912577 2061989 := bbase (se 4 (by rfl) ⟨193311, by rfl⟩ : syracuseStep 2061989 = 386623) (by norm_num)
theorem B1373885 : Blo 912577 1373885 := bbase (se 3 (by rfl) ⟨257603, by rfl⟩ : syracuseStep 1373885 = 515207) (by norm_num)
theorem B1373909 : Blo 912577 1373909 := bbase (se 7 (by rfl) ⟨16100, by rfl⟩ : syracuseStep 1373909 = 32201) (by norm_num)
theorem B1373933 : Blo 912577 1373933 := bbase (se 3 (by rfl) ⟨257612, by rfl⟩ : syracuseStep 1373933 = 515225) (by norm_num)
theorem B2062061 : Blo 912577 2062061 := bbase (se 3 (by rfl) ⟨386636, by rfl⟩ : syracuseStep 2062061 = 773273) (by norm_num)
theorem B1373957 : Blo 912577 1373957 := bbase (se 4 (by rfl) ⟨128808, by rfl⟩ : syracuseStep 1373957 = 257617) (by norm_num)
theorem B1373981 : Blo 912577 1373981 := bbase (se 3 (by rfl) ⟨257621, by rfl⟩ : syracuseStep 1373981 = 515243) (by norm_num)
theorem B1374005 : Blo 912577 1374005 := bbase (se 5 (by rfl) ⟨64406, by rfl⟩ : syracuseStep 1374005 = 128813) (by norm_num)
theorem B2062133 : Blo 912577 2062133 := bbase (se 5 (by rfl) ⟨96662, by rfl⟩ : syracuseStep 2062133 = 193325) (by norm_num)
theorem B1374029 : Blo 912577 1374029 := bbase (se 3 (by rfl) ⟨257630, by rfl⟩ : syracuseStep 1374029 = 515261) (by norm_num)
theorem B3700565 : Blo 912577 3700565 := bbase (se 9 (by rfl) ⟨10841, by rfl⟩ : syracuseStep 3700565 = 21683) (by norm_num)
theorem B1374053 : Blo 912577 1374053 := bbase (se 4 (by rfl) ⟨128817, by rfl⟩ : syracuseStep 1374053 = 257635) (by norm_num)
theorem B1374077 : Blo 912577 1374077 := bbase (se 3 (by rfl) ⟨257639, by rfl⟩ : syracuseStep 1374077 = 515279) (by norm_num)
theorem B2062205 : Blo 912577 2062205 := bbase (se 3 (by rfl) ⟨386663, by rfl⟩ : syracuseStep 2062205 = 773327) (by norm_num)
theorem B1374101 : Blo 912577 1374101 := bbase (se 6 (by rfl) ⟨32205, by rfl⟩ : syracuseStep 1374101 = 64411) (by norm_num)
theorem B1374125 : Blo 912577 1374125 := bbase (se 3 (by rfl) ⟨257648, by rfl⟩ : syracuseStep 1374125 = 515297) (by norm_num)
theorem B1374149 : Blo 912577 1374149 := bbase (se 4 (by rfl) ⟨128826, by rfl⟩ : syracuseStep 1374149 = 257653) (by norm_num)
theorem B2062277 : Blo 912577 2062277 := bbase (se 4 (by rfl) ⟨193338, by rfl⟩ : syracuseStep 2062277 = 386677) (by norm_num)
theorem B1374173 : Blo 912577 1374173 := bbase (se 3 (by rfl) ⟨257657, by rfl⟩ : syracuseStep 1374173 = 515315) (by norm_num)
theorem B1374197 : Blo 912577 1374197 := bbase (se 5 (by rfl) ⟨64415, by rfl⟩ : syracuseStep 1374197 = 128831) (by norm_num)
theorem B1374221 : Blo 912577 1374221 := bbase (se 3 (by rfl) ⟨257666, by rfl⟩ : syracuseStep 1374221 = 515333) (by norm_num)
theorem B1374245 : Blo 912577 1374245 := bbase (se 4 (by rfl) ⟨128835, by rfl⟩ : syracuseStep 1374245 = 257671) (by norm_num)
theorem B1734709 : Blo 912577 1734709 := bbase (se 5 (by rfl) ⟨81314, by rfl⟩ : syracuseStep 1734709 = 162629) (by norm_num)
theorem B1374269 : Blo 912577 1374269 := bbase (se 3 (by rfl) ⟨257675, by rfl⟩ : syracuseStep 1374269 = 515351) (by norm_num)
theorem B2193493 : Blo 912577 2193493 := bbase (se 8 (by rfl) ⟨12852, by rfl⟩ : syracuseStep 2193493 = 25705) (by norm_num)
theorem B1374293 : Blo 912577 1374293 := bbase (se 8 (by rfl) ⟨8052, by rfl⟩ : syracuseStep 1374293 = 16105) (by norm_num)
theorem B1374317 : Blo 912577 1374317 := bbase (se 3 (by rfl) ⟨257684, by rfl⟩ : syracuseStep 1374317 = 515369) (by norm_num)
theorem B1374341 : Blo 912577 1374341 := bbase (se 4 (by rfl) ⟨128844, by rfl⟩ : syracuseStep 1374341 = 257689) (by norm_num)
theorem B1374365 : Blo 912577 1374365 := bbase (se 3 (by rfl) ⟨257693, by rfl⟩ : syracuseStep 1374365 = 515387) (by norm_num)
theorem B1374389 : Blo 912577 1374389 := bbase (se 5 (by rfl) ⟨64424, by rfl⟩ : syracuseStep 1374389 = 128849) (by norm_num)
theorem B1734853 : Blo 912577 1734853 := bbase (se 4 (by rfl) ⟨162642, by rfl⟩ : syracuseStep 1734853 = 325285) (by norm_num)
theorem B1374413 : Blo 912577 1374413 := bbase (se 3 (by rfl) ⟨257702, by rfl⟩ : syracuseStep 1374413 = 515405) (by norm_num)
theorem B1374437 : Blo 912577 1374437 := bbase (se 4 (by rfl) ⟨128853, by rfl⟩ : syracuseStep 1374437 = 257707) (by norm_num)
theorem B3471605 : Blo 912577 3471605 := bbase (se 5 (by rfl) ⟨162731, by rfl⟩ : syracuseStep 3471605 = 325463) (by norm_num)
theorem B1374461 : Blo 912577 1374461 := bbase (se 3 (by rfl) ⟨257711, by rfl⟩ : syracuseStep 1374461 = 515423) (by norm_num)
theorem B1374485 : Blo 912577 1374485 := bbase (se 6 (by rfl) ⟨32214, by rfl⟩ : syracuseStep 1374485 = 64429) (by norm_num)
theorem B2226469 : Blo 912577 2226469 := bbase (se 4 (by rfl) ⟨208731, by rfl⟩ : syracuseStep 2226469 = 417463) (by norm_num)
theorem B1374509 : Blo 912577 1374509 := bbase (se 3 (by rfl) ⟨257720, by rfl⟩ : syracuseStep 1374509 = 515441) (by norm_num)
theorem B1374533 : Blo 912577 1374533 := bbase (se 4 (by rfl) ⟨128862, by rfl⟩ : syracuseStep 1374533 = 257725) (by norm_num)
theorem B2783573 : Blo 912577 2783573 := bbase (se 10 (by rfl) ⟨4077, by rfl⟩ : syracuseStep 2783573 = 8155) (by norm_num)
theorem B1374557 : Blo 912577 1374557 := bbase (se 3 (by rfl) ⟨257729, by rfl⟩ : syracuseStep 1374557 = 515459) (by norm_num)
theorem B1735013 : Blo 912577 1735013 := bbase (se 4 (by rfl) ⟨162657, by rfl⟩ : syracuseStep 1735013 = 325315) (by norm_num)
theorem B1374581 : Blo 912577 1374581 := bbase (se 5 (by rfl) ⟨64433, by rfl⟩ : syracuseStep 1374581 = 128867) (by norm_num)
theorem B1374605 : Blo 912577 1374605 := bbase (se 3 (by rfl) ⟨257738, by rfl⟩ : syracuseStep 1374605 = 515477) (by norm_num)
theorem B1374629 : Blo 912577 1374629 := bbase (se 4 (by rfl) ⟨128871, by rfl⟩ : syracuseStep 1374629 = 257743) (by norm_num)
theorem B1374653 : Blo 912577 1374653 := bbase (se 3 (by rfl) ⟨257747, by rfl⟩ : syracuseStep 1374653 = 515495) (by norm_num)
theorem B1374677 : Blo 912577 1374677 := bbase (se 7 (by rfl) ⟨16109, by rfl⟩ : syracuseStep 1374677 = 32219) (by norm_num)
theorem B1374701 : Blo 912577 1374701 := bbase (se 3 (by rfl) ⟨257756, by rfl⟩ : syracuseStep 1374701 = 515513) (by norm_num)
theorem B1735157 : Blo 912577 1735157 := bbase (se 5 (by rfl) ⟨81335, by rfl⟩ : syracuseStep 1735157 = 162671) (by norm_num)
theorem B1374725 : Blo 912577 1374725 := bbase (se 4 (by rfl) ⟨128880, by rfl⟩ : syracuseStep 1374725 = 257761) (by norm_num)
theorem B3471893 : Blo 912577 3471893 := bbase (se 6 (by rfl) ⟨81372, by rfl⟩ : syracuseStep 3471893 = 162745) (by norm_num)
theorem B4946453 : Blo 912577 4946453 := bbase (se 6 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 4946453 = 231865) (by norm_num)
theorem B1374749 : Blo 912577 1374749 := bbase (se 3 (by rfl) ⟨257765, by rfl⟩ : syracuseStep 1374749 = 515531) (by norm_num)
theorem B1374773 : Blo 912577 1374773 := bbase (se 5 (by rfl) ⟨64442, by rfl⟩ : syracuseStep 1374773 = 128885) (by norm_num)
theorem B1374797 : Blo 912577 1374797 := bbase (se 3 (by rfl) ⟨257774, by rfl⟩ : syracuseStep 1374797 = 515549) (by norm_num)
theorem B2226781 : Blo 912577 2226781 := bbase (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) (by norm_num)
theorem B1374821 : Blo 912577 1374821 := bbase (se 4 (by rfl) ⟨128889, by rfl⟩ : syracuseStep 1374821 = 257779) (by norm_num)
theorem B1374845 : Blo 912577 1374845 := bbase (se 3 (by rfl) ⟨257783, by rfl⟩ : syracuseStep 1374845 = 515567) (by norm_num)
theorem B4455125 : Blo 912577 4455125 := bbase (se 7 (by rfl) ⟨52208, by rfl⟩ : syracuseStep 4455125 = 104417) (by norm_num)
theorem B1735445 : Blo 912577 1735445 := bbase (se 6 (by rfl) ⟨40674, by rfl⟩ : syracuseStep 1735445 = 81349) (by norm_num)
theorem B1735597 : Blo 912577 1735597 := bbase (se 3 (by rfl) ⟨325424, by rfl⟩ : syracuseStep 1735597 = 650849) (by norm_num)
theorem B2194445 : Blo 912577 2194445 := bbase (se 3 (by rfl) ⟨411458, by rfl⟩ : syracuseStep 2194445 = 822917) (by norm_num)
theorem B2194501 : Blo 912577 2194501 := bbase (se 4 (by rfl) ⟨205734, by rfl⟩ : syracuseStep 2194501 = 411469) (by norm_num)
theorem B1735901 : Blo 912577 1735901 := bbase (se 3 (by rfl) ⟨325481, by rfl⟩ : syracuseStep 1735901 = 650963) (by norm_num)
theorem B4947317 : Blo 912577 4947317 := bbase (se 5 (by rfl) ⟨231905, by rfl⟩ : syracuseStep 4947317 = 463811) (by norm_num)
theorem B2194877 : Blo 912577 2194877 := bbase (se 3 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 2194877 = 823079) (by norm_num)
theorem B2195117 : Blo 912577 2195117 := bbase (se 3 (by rfl) ⟨411584, by rfl⟩ : syracuseStep 2195117 = 823169) (by norm_num)
theorem B3473077 : Blo 912577 3473077 := bbase (se 5 (by rfl) ⟨162800, by rfl⟩ : syracuseStep 3473077 = 325601) (by norm_num)
theorem B3899285 : Blo 912577 3899285 := bbase (se 6 (by rfl) ⟨91389, by rfl⟩ : syracuseStep 3899285 = 182779) (by norm_num)
theorem B1736653 : Blo 912577 1736653 := bbase (se 3 (by rfl) ⟨325622, by rfl⟩ : syracuseStep 1736653 = 651245) (by norm_num)
theorem B3473381 : Blo 912577 3473381 := bbase (se 4 (by rfl) ⟨325629, by rfl⟩ : syracuseStep 3473381 = 651259) (by norm_num)
theorem B1540093 : Blo 912577 1540093 := bbase (se 3 (by rfl) ⟨288767, by rfl⟩ : syracuseStep 1540093 = 577535) (by norm_num)
theorem B1540147 : Blo 912577 1540147 := bstep (se 1 (by rfl) ⟨1155110, by rfl⟩ : syracuseStep 1540147 = 2310221) B2310221
theorem B4620401 : Blo 912577 4620401 := bstep (se 2 (by rfl) ⟨1732650, by rfl⟩ : syracuseStep 4620401 = 3465301) B3465301
theorem B3473549 : Blo 912577 3473549 := bstep (se 3 (by rfl) ⟨651290, by rfl⟩ : syracuseStep 3473549 = 1302581) B1302581
theorem B1540289 : Blo 912577 1540289 := bstep (se 2 (by rfl) ⟨577608, by rfl⟩ : syracuseStep 1540289 = 1155217) B1155217
theorem B3080429 : Blo 912577 3080429 := bstep (se 3 (by rfl) ⟨577580, by rfl⟩ : syracuseStep 3080429 = 1155161) B1155161
theorem B11108593 : Blo 912577 11108593 := bstep (se 2 (by rfl) ⟨4165722, by rfl⟩ : syracuseStep 11108593 = 8331445) B8331445
theorem B3080483 : Blo 912577 3080483 := bstep (se 1 (by rfl) ⟨2310362, by rfl⟩ : syracuseStep 3080483 = 4620725) B4620725
theorem B1540417 : Blo 912577 1540417 := bstep (se 2 (by rfl) ⟨577656, by rfl⟩ : syracuseStep 1540417 = 1155313) B1155313
theorem B1540451 : Blo 912577 1540451 := bstep (se 1 (by rfl) ⟨1155338, by rfl⟩ : syracuseStep 1540451 = 2310677) B2310677
theorem B4391309 : Blo 912577 4391309 := bstep (se 3 (by rfl) ⟨823370, by rfl⟩ : syracuseStep 4391309 = 1646741) B1646741
theorem B1540579 : Blo 912577 1540579 := bstep (se 1 (by rfl) ⟨1155434, by rfl⟩ : syracuseStep 1540579 = 2310869) B2310869
theorem B3080753 : Blo 912577 3080753 := bstep (se 2 (by rfl) ⟨1155282, by rfl⟩ : syracuseStep 3080753 = 2310565) B2310565
theorem B1737283 : Blo 912577 1737283 := bstep (se 1 (by rfl) ⟨1302962, by rfl⟩ : syracuseStep 1737283 = 2605925) B2605925
theorem B1540721 : Blo 912577 1540721 := bstep (se 2 (by rfl) ⟨577770, by rfl⟩ : syracuseStep 1540721 = 1155541) B1155541
theorem B2228849 : Blo 912577 2228849 := bstep (se 2 (by rfl) ⟨835818, by rfl⟩ : syracuseStep 2228849 = 1671637) B1671637
theorem B5210801 : Blo 912577 5210801 := bstep (se 2 (by rfl) ⟨1954050, by rfl⟩ : syracuseStep 5210801 = 3908101) B3908101
theorem B1737443 : Blo 912577 1737443 := bstep (se 1 (by rfl) ⟨1303082, by rfl⟩ : syracuseStep 1737443 = 2606165) B2606165
theorem B2228963 : Blo 912577 2228963 := bstep (se 1 (by rfl) ⟨1671722, by rfl⟩ : syracuseStep 2228963 = 3343445) B3343445
theorem B1540849 : Blo 912577 1540849 := bstep (se 2 (by rfl) ⟨577818, by rfl⟩ : syracuseStep 1540849 = 1155637) B1155637
theorem B5866253 : Blo 912577 5866253 := bstep (se 3 (by rfl) ⟨1099922, by rfl⟩ : syracuseStep 5866253 = 2199845) B2199845
theorem B1540883 : Blo 912577 1540883 := bstep (se 1 (by rfl) ⟨1155662, by rfl⟩ : syracuseStep 1540883 = 2311325) B2311325
theorem B15827825 : Blo 912577 15827825 := bstep (se 2 (by rfl) ⟨5935434, by rfl⟩ : syracuseStep 15827825 = 11870869) B11870869
theorem B1541011 : Blo 912577 1541011 := bstep (se 1 (by rfl) ⟨1155758, by rfl⟩ : syracuseStep 1541011 = 2311517) B2311517
theorem B3474353 : Blo 912577 3474353 := bstep (se 2 (by rfl) ⟨1302882, by rfl⟩ : syracuseStep 3474353 = 2605765) B2605765
theorem B1541153 : Blo 912577 1541153 := bstep (se 2 (by rfl) ⟨577932, by rfl⟩ : syracuseStep 1541153 = 1155865) B1155865
theorem B3081293 : Blo 912577 3081293 := bstep (se 3 (by rfl) ⟨577742, by rfl⟩ : syracuseStep 3081293 = 1155485) B1155485
theorem B3081347 : Blo 912577 3081347 := bstep (se 1 (by rfl) ⟨2311010, by rfl⟩ : syracuseStep 3081347 = 4622021) B4622021
theorem B1541281 : Blo 912577 1541281 := bstep (se 2 (by rfl) ⟨577980, by rfl⟩ : syracuseStep 1541281 = 1155961) B1155961
theorem B1541315 : Blo 912577 1541315 := bstep (se 1 (by rfl) ⟨1155986, by rfl⟩ : syracuseStep 1541315 = 2311973) B2311973
theorem B5637325 : Blo 912577 5637325 := bstep (se 3 (by rfl) ⟨1056998, by rfl⟩ : syracuseStep 5637325 = 2113997) B2113997
theorem B5932259 : Blo 912577 5932259 := bstep (se 1 (by rfl) ⟨4449194, by rfl⟩ : syracuseStep 5932259 = 8898389) B8898389
theorem B2786563 : Blo 912577 2786563 := bstep (se 1 (by rfl) ⟨2089922, by rfl⟩ : syracuseStep 2786563 = 4179845) B4179845
theorem B1541443 : Blo 912577 1541443 := bstep (se 1 (by rfl) ⟨1156082, by rfl⟩ : syracuseStep 1541443 = 2312165) B2312165
theorem B3081617 : Blo 912577 3081617 := bstep (se 2 (by rfl) ⟨1155606, by rfl⟩ : syracuseStep 3081617 = 2311213) B2311213
theorem B1541585 : Blo 912577 1541585 := bstep (se 2 (by rfl) ⟨578094, by rfl⟩ : syracuseStep 1541585 = 1156189) B1156189
theorem B4621859 : Blo 912577 4621859 := bstep (se 1 (by rfl) ⟨3466394, by rfl⟩ : syracuseStep 4621859 = 6932789) B6932789
theorem B3475021 : Blo 912577 3475021 := bstep (se 3 (by rfl) ⟨651566, by rfl⟩ : syracuseStep 3475021 = 1303133) B1303133
theorem B1541713 : Blo 912577 1541713 := bstep (se 2 (by rfl) ⟨578142, by rfl⟩ : syracuseStep 1541713 = 1156285) B1156285
theorem B1541747 : Blo 912577 1541747 := bstep (se 1 (by rfl) ⟨1156310, by rfl⟩ : syracuseStep 1541747 = 2312621) B2312621
theorem B1672849 : Blo 912577 1672849 := bstep (se 2 (by rfl) ⟨627318, by rfl⟩ : syracuseStep 1672849 = 1254637) B1254637
theorem B1541875 : Blo 912577 1541875 := bstep (se 1 (by rfl) ⟨1156406, by rfl⟩ : syracuseStep 1541875 = 2312813) B2312813
theorem B1738513 : Blo 912577 1738513 := bstep (se 2 (by rfl) ⟨651942, by rfl⟩ : syracuseStep 1738513 = 1303885) B1303885
theorem B2787149 : Blo 912577 2787149 := bstep (se 3 (by rfl) ⟨522590, by rfl⟩ : syracuseStep 2787149 = 1045181) B1045181
theorem B1542017 : Blo 912577 1542017 := bstep (se 2 (by rfl) ⟨578256, by rfl⟩ : syracuseStep 1542017 = 1156513) B1156513
theorem B3704717 : Blo 912577 3704717 := bstep (se 3 (by rfl) ⟨694634, by rfl⟩ : syracuseStep 3704717 = 1389269) B1389269
theorem B3082157 : Blo 912577 3082157 := bstep (se 3 (by rfl) ⟨577904, by rfl⟩ : syracuseStep 3082157 = 1155809) B1155809
theorem B3082211 : Blo 912577 3082211 := bstep (se 1 (by rfl) ⟨2311658, by rfl⟩ : syracuseStep 3082211 = 4623317) B4623317
theorem B1542145 : Blo 912577 1542145 := bstep (se 2 (by rfl) ⟨578304, by rfl⟩ : syracuseStep 1542145 = 1156609) B1156609
theorem B1542179 : Blo 912577 1542179 := bstep (se 1 (by rfl) ⟨1156634, by rfl⟩ : syracuseStep 1542179 = 2313269) B2313269
theorem B5212259 : Blo 912577 5212259 := bstep (se 1 (by rfl) ⟨3909194, by rfl⟩ : syracuseStep 5212259 = 7818389) B7818389
theorem B1542307 : Blo 912577 1542307 := bstep (se 1 (by rfl) ⟨1156730, by rfl⟩ : syracuseStep 1542307 = 2313461) B2313461
theorem B3082481 : Blo 912577 3082481 := bstep (se 2 (by rfl) ⟨1155930, by rfl⟩ : syracuseStep 3082481 = 2311861) B2311861
theorem B3901745 : Blo 912577 3901745 := bstep (se 2 (by rfl) ⟨1463154, by rfl⟩ : syracuseStep 3901745 = 2926309) B2926309
theorem B1542449 : Blo 912577 1542449 := bstep (se 2 (by rfl) ⟨578418, by rfl⟩ : syracuseStep 1542449 = 1156837) B1156837
theorem B4622669 : Blo 912577 4622669 := bstep (se 3 (by rfl) ⟨866750, by rfl⟩ : syracuseStep 4622669 = 1733501) B1733501
theorem B5343565 : Blo 912577 5343565 := bstep (se 3 (by rfl) ⟨1001918, by rfl⟩ : syracuseStep 5343565 = 2003837) B2003837
theorem B3344717 : Blo 912577 3344717 := bstep (se 3 (by rfl) ⟨627134, by rfl⟩ : syracuseStep 3344717 = 1254269) B1254269
theorem B3475811 : Blo 912577 3475811 := bstep (se 1 (by rfl) ⟨2606858, by rfl⟩ : syracuseStep 3475811 = 5213717) B5213717
theorem B1542577 : Blo 912577 1542577 := bstep (se 2 (by rfl) ⟨578466, by rfl⟩ : syracuseStep 1542577 = 1156933) B1156933
theorem B1542611 : Blo 912577 1542611 := bstep (se 1 (by rfl) ⟨1156958, by rfl⟩ : syracuseStep 1542611 = 2313917) B2313917
theorem B1542739 : Blo 912577 1542739 := bstep (se 1 (by rfl) ⟨1157054, by rfl⟩ : syracuseStep 1542739 = 2314109) B2314109
theorem B4164301 : Blo 912577 4164301 := bstep (se 3 (by rfl) ⟨780806, by rfl⟩ : syracuseStep 4164301 = 1561613) B1561613
theorem B1542881 : Blo 912577 1542881 := bstep (se 2 (by rfl) ⟨578580, by rfl⟩ : syracuseStep 1542881 = 1157161) B1157161
theorem B3083021 : Blo 912577 3083021 := bstep (se 3 (by rfl) ⟨578066, by rfl⟩ : syracuseStep 3083021 = 1156133) B1156133
theorem B1739569 : Blo 912577 1739569 := bstep (se 2 (by rfl) ⟨652338, by rfl⟩ : syracuseStep 1739569 = 1304677) B1304677
theorem B3083075 : Blo 912577 3083075 := bstep (se 1 (by rfl) ⟨2312306, by rfl⟩ : syracuseStep 3083075 = 4624613) B4624613
theorem B1543009 : Blo 912577 1543009 := bstep (se 2 (by rfl) ⟨578628, by rfl⟩ : syracuseStep 1543009 = 1157257) B1157257
theorem B1543043 : Blo 912577 1543043 := bstep (se 1 (by rfl) ⟨1157282, by rfl⟩ : syracuseStep 1543043 = 2314565) B2314565
theorem B3476465 : Blo 912577 3476465 := bstep (se 2 (by rfl) ⟨1303674, by rfl⟩ : syracuseStep 3476465 = 2607349) B2607349
theorem B1543171 : Blo 912577 1543171 := bstep (se 1 (by rfl) ⟨1157378, by rfl⟩ : syracuseStep 1543171 = 2314757) B2314757
theorem B5213261 : Blo 912577 5213261 := bstep (se 3 (by rfl) ⟨977486, by rfl⟩ : syracuseStep 5213261 = 1954973) B1954973
theorem B3083345 : Blo 912577 3083345 := bstep (se 2 (by rfl) ⟨1156254, by rfl⟩ : syracuseStep 3083345 = 2312509) B2312509
theorem B1543313 : Blo 912577 1543313 := bstep (se 2 (by rfl) ⟨578742, by rfl⟩ : syracuseStep 1543313 = 1157485) B1157485
theorem B1739971 : Blo 912577 1739971 := bstep (se 1 (by rfl) ⟨1304978, by rfl⟩ : syracuseStep 1739971 = 2609957) B2609957
theorem B8359109 : Blo 912577 8359109 := bstep (se 4 (by rfl) ⟨783666, by rfl⟩ : syracuseStep 8359109 = 1567333) B1567333
theorem B1740017 : Blo 912577 1740017 := bstep (se 2 (by rfl) ⟨652506, by rfl⟩ : syracuseStep 1740017 = 1305013) B1305013
theorem B1543441 : Blo 912577 1543441 := bstep (se 2 (by rfl) ⟨578790, by rfl⟩ : syracuseStep 1543441 = 1157581) B1157581
theorem B1543475 : Blo 912577 1543475 := bstep (se 1 (by rfl) ⟨1157606, by rfl⟩ : syracuseStep 1543475 = 2315213) B2315213
theorem B7409009 : Blo 912577 7409009 := bstep (se 2 (by rfl) ⟨2778378, by rfl⟩ : syracuseStep 7409009 = 5556757) B5556757
theorem B6950285 : Blo 912577 6950285 := bstep (se 3 (by rfl) ⟨1303178, by rfl⟩ : syracuseStep 6950285 = 2606357) B2606357
theorem B1543603 : Blo 912577 1543603 := bstep (se 1 (by rfl) ⟨1157702, by rfl⟩ : syracuseStep 1543603 = 2315405) B2315405
theorem B3903011 : Blo 912577 3903011 := bstep (se 1 (by rfl) ⟨2927258, by rfl⟩ : syracuseStep 3903011 = 5854517) B5854517
theorem B1543745 : Blo 912577 1543745 := bstep (se 2 (by rfl) ⟨578904, by rfl⟩ : syracuseStep 1543745 = 1157809) B1157809
theorem B3083885 : Blo 912577 3083885 := bstep (se 3 (by rfl) ⟨578228, by rfl⟩ : syracuseStep 3083885 = 1156457) B1156457
theorem B4689521 : Blo 912577 4689521 := bstep (se 2 (by rfl) ⟨1758570, by rfl⟩ : syracuseStep 4689521 = 3517141) B3517141
theorem B3083939 : Blo 912577 3083939 := bstep (se 1 (by rfl) ⟨2312954, by rfl⟩ : syracuseStep 3083939 = 4625909) B4625909
theorem B1543873 : Blo 912577 1543873 := bstep (se 2 (by rfl) ⟨578952, by rfl⟩ : syracuseStep 1543873 = 1157905) B1157905
theorem B1543907 : Blo 912577 1543907 := bstep (se 1 (by rfl) ⟨1157930, by rfl⟩ : syracuseStep 1543907 = 2315861) B2315861
theorem B1544035 : Blo 912577 1544035 := bstep (se 1 (by rfl) ⟨1158026, by rfl⟩ : syracuseStep 1544035 = 2316053) B2316053
theorem B3084209 : Blo 912577 3084209 := bstep (se 2 (by rfl) ⟨1156578, by rfl⟩ : syracuseStep 3084209 = 2313157) B2313157
theorem B1544177 : Blo 912577 1544177 := bstep (se 2 (by rfl) ⟨579066, by rfl⟩ : syracuseStep 1544177 = 1158133) B1158133
theorem B1544305 : Blo 912577 1544305 := bstep (se 2 (by rfl) ⟨579114, by rfl⟩ : syracuseStep 1544305 = 1158229) B1158229
theorem B1544339 : Blo 912577 1544339 := bstep (se 1 (by rfl) ⟨1158254, by rfl⟩ : syracuseStep 1544339 = 2316509) B2316509
theorem B1544467 : Blo 912577 1544467 := bstep (se 1 (by rfl) ⟨1158350, by rfl⟩ : syracuseStep 1544467 = 2316701) B2316701
theorem B1544609 : Blo 912577 1544609 := bstep (se 2 (by rfl) ⟨579228, by rfl⟩ : syracuseStep 1544609 = 1158457) B1158457
theorem B6263203 : Blo 912577 6263203 := bstep (se 1 (by rfl) ⟨4697402, by rfl⟩ : syracuseStep 6263203 = 9394805) B9394805
theorem B3477923 : Blo 912577 3477923 := bstep (se 1 (by rfl) ⟨2608442, by rfl⟩ : syracuseStep 3477923 = 5216885) B5216885
theorem B3477937 : Blo 912577 3477937 := bstep (se 2 (by rfl) ⟨1304226, by rfl⟩ : syracuseStep 3477937 = 2608453) B2608453
theorem B3084749 : Blo 912577 3084749 := bstep (se 3 (by rfl) ⟨578390, by rfl⟩ : syracuseStep 3084749 = 1156781) B1156781
theorem B3084803 : Blo 912577 3084803 := bstep (se 1 (by rfl) ⟨2313602, by rfl⟩ : syracuseStep 3084803 = 4627205) B4627205
theorem B1544737 : Blo 912577 1544737 := bstep (se 2 (by rfl) ⟨579276, by rfl⟩ : syracuseStep 1544737 = 1158553) B1158553
theorem B1544771 : Blo 912577 1544771 := bstep (se 1 (by rfl) ⟨1158578, by rfl⟩ : syracuseStep 1544771 = 2317157) B2317157
theorem B1544899 : Blo 912577 1544899 := bstep (se 1 (by rfl) ⟨1158674, by rfl⟩ : syracuseStep 1544899 = 2317349) B2317349
theorem B2200259 : Blo 912577 2200259 := bstep (se 1 (by rfl) ⟨1650194, by rfl⟩ : syracuseStep 2200259 = 3300389) B3300389
theorem B3085073 : Blo 912577 3085073 := bstep (se 2 (by rfl) ⟨1156902, by rfl⟩ : syracuseStep 3085073 = 2313805) B2313805
theorem B1545041 : Blo 912577 1545041 := bstep (se 2 (by rfl) ⟨579390, by rfl⟩ : syracuseStep 1545041 = 1158781) B1158781
theorem B1545169 : Blo 912577 1545169 := bstep (se 2 (by rfl) ⟨579438, by rfl⟩ : syracuseStep 1545169 = 1158877) B1158877
theorem B1545203 : Blo 912577 1545203 := bstep (se 1 (by rfl) ⟨1158902, by rfl⟩ : syracuseStep 1545203 = 2317805) B2317805
theorem B1545331 : Blo 912577 1545331 := bstep (se 1 (by rfl) ⟨1158998, by rfl⟩ : syracuseStep 1545331 = 2317997) B2317997
theorem B4625585 : Blo 912577 4625585 := bstep (se 2 (by rfl) ⟨1734594, by rfl⟩ : syracuseStep 4625585 = 3469189) B3469189
theorem B1545473 : Blo 912577 1545473 := bstep (se 2 (by rfl) ⟨579552, by rfl⟩ : syracuseStep 1545473 = 1159105) B1159105
theorem B3085613 : Blo 912577 3085613 := bstep (se 3 (by rfl) ⟨578552, by rfl⟩ : syracuseStep 3085613 = 1157105) B1157105
theorem B3085667 : Blo 912577 3085667 := bstep (se 1 (by rfl) ⟨2314250, by rfl⟩ : syracuseStep 3085667 = 4628501) B4628501
theorem B1545601 : Blo 912577 1545601 := bstep (se 2 (by rfl) ⟨579600, by rfl⟩ : syracuseStep 1545601 = 1159201) B1159201
theorem B1545635 : Blo 912577 1545635 := bstep (se 1 (by rfl) ⟨1159226, by rfl⟩ : syracuseStep 1545635 = 2318453) B2318453
theorem B6592013 : Blo 912577 6592013 := bstep (se 3 (by rfl) ⟨1236002, by rfl⟩ : syracuseStep 6592013 = 2472005) B2472005
theorem B1545763 : Blo 912577 1545763 := bstep (se 1 (by rfl) ⟨1159322, by rfl⟩ : syracuseStep 1545763 = 2318645) B2318645
theorem B3085937 : Blo 912577 3085937 := bstep (se 2 (by rfl) ⟨1157226, by rfl⟩ : syracuseStep 3085937 = 2314453) B2314453
theorem B1545905 : Blo 912577 1545905 := bstep (se 2 (by rfl) ⟨579714, by rfl⟩ : syracuseStep 1545905 = 1159429) B1159429
theorem B1546033 : Blo 912577 1546033 := bstep (se 2 (by rfl) ⟨579762, by rfl⟩ : syracuseStep 1546033 = 1159525) B1159525
theorem B1546067 : Blo 912577 1546067 := bstep (se 1 (by rfl) ⟨1159550, by rfl⟩ : syracuseStep 1546067 = 2319101) B2319101
theorem B3479395 : Blo 912577 3479395 := bstep (se 1 (by rfl) ⟨2609546, by rfl⟩ : syracuseStep 3479395 = 5219093) B5219093
theorem B3708785 : Blo 912577 3708785 := bstep (se 2 (by rfl) ⟨1390794, by rfl⟩ : syracuseStep 3708785 = 2781589) B2781589
theorem B5216177 : Blo 912577 5216177 := bstep (se 2 (by rfl) ⟨1956066, by rfl⟩ : syracuseStep 5216177 = 3912133) B3912133
theorem B1546195 : Blo 912577 1546195 := bstep (se 1 (by rfl) ⟨1159646, by rfl⟩ : syracuseStep 1546195 = 2319293) B2319293
theorem B5871685 : Blo 912577 5871685 := bstep (se 4 (by rfl) ⟨550470, by rfl⟩ : syracuseStep 5871685 = 1100941) B1100941
theorem B1546337 : Blo 912577 1546337 := bstep (se 2 (by rfl) ⟨579876, by rfl⟩ : syracuseStep 1546337 = 1159753) B1159753
theorem B23730317 : Blo 912577 23730317 := bstep (se 3 (by rfl) ⟨4449434, by rfl⟩ : syracuseStep 23730317 = 8898869) B8898869
theorem B3086477 : Blo 912577 3086477 := bstep (se 3 (by rfl) ⟨578714, by rfl⟩ : syracuseStep 3086477 = 1157429) B1157429
theorem B3086531 : Blo 912577 3086531 := bstep (se 1 (by rfl) ⟨2314898, by rfl⟩ : syracuseStep 3086531 = 4629797) B4629797
theorem B1546465 : Blo 912577 1546465 := bstep (se 2 (by rfl) ⟨579924, by rfl⟩ : syracuseStep 1546465 = 1159849) B1159849
theorem B6953201 : Blo 912577 6953201 := bstep (se 2 (by rfl) ⟨2607450, by rfl⟩ : syracuseStep 6953201 = 5214901) B5214901
theorem B1546499 : Blo 912577 1546499 := bstep (se 1 (by rfl) ⟨1159874, by rfl⟩ : syracuseStep 1546499 = 2319749) B2319749
theorem B1546627 : Blo 912577 1546627 := bstep (se 1 (by rfl) ⟨1159970, by rfl⟩ : syracuseStep 1546627 = 2319941) B2319941
theorem B3086801 : Blo 912577 3086801 := bstep (se 2 (by rfl) ⟨1157550, by rfl⟩ : syracuseStep 3086801 = 2315101) B2315101
theorem B4627043 : Blo 912577 4627043 := bstep (se 1 (by rfl) ⟨3470282, by rfl⟩ : syracuseStep 4627043 = 6940565) B6940565
theorem B3709709 : Blo 912577 3709709 := bstep (se 3 (by rfl) ⟨695570, by rfl⟩ : syracuseStep 3709709 = 1391141) B1391141
theorem B3087341 : Blo 912577 3087341 := bstep (se 3 (by rfl) ⟨578876, by rfl⟩ : syracuseStep 3087341 = 1157753) B1157753
theorem B3087395 : Blo 912577 3087395 := bstep (se 1 (by rfl) ⟨2315546, by rfl⟩ : syracuseStep 3087395 = 4631093) B4631093
theorem B3906701 : Blo 912577 3906701 := bstep (se 3 (by rfl) ⟨732506, by rfl⟩ : syracuseStep 3906701 = 1465013) B1465013
theorem B3087665 : Blo 912577 3087665 := bstep (se 2 (by rfl) ⟨1157874, by rfl⟩ : syracuseStep 3087665 = 2315749) B2315749
theorem B5217635 : Blo 912577 5217635 := bstep (se 1 (by rfl) ⟨3913226, by rfl⟩ : syracuseStep 5217635 = 7826453) B7826453
theorem B4627853 : Blo 912577 4627853 := bstep (se 3 (by rfl) ⟨867722, by rfl⟩ : syracuseStep 4627853 = 1735445) B1735445
theorem B1318627 : Blo 912577 1318627 := bstep (se 1 (by rfl) ⟨988970, by rfl⟩ : syracuseStep 1318627 = 1977941) B1977941
theorem B1482547 : Blo 912577 1482547 := bstep (se 1 (by rfl) ⟨1111910, by rfl⟩ : syracuseStep 1482547 = 2223821) B2223821
theorem B11280181 : Blo 912577 11280181 := bstep (se 5 (by rfl) ⟨528758, by rfl⟩ : syracuseStep 11280181 = 1057517) B1057517
theorem B3088205 : Blo 912577 3088205 := bstep (se 3 (by rfl) ⟨579038, by rfl⟩ : syracuseStep 3088205 = 1158077) B1158077
theorem B3088259 : Blo 912577 3088259 := bstep (se 1 (by rfl) ⟨2316194, by rfl⟩ : syracuseStep 3088259 = 4632389) B4632389
theorem B3710861 : Blo 912577 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B2924515 : Blo 912577 2924515 := bstep (se 1 (by rfl) ⟨2193386, by rfl⟩ : syracuseStep 2924515 = 4386773) B4386773
theorem B2924657 : Blo 912577 2924657 := bstep (se 2 (by rfl) ⟨1096746, by rfl⟩ : syracuseStep 2924657 = 2193493) B2193493
theorem B3088529 : Blo 912577 3088529 := bstep (se 2 (by rfl) ⟨1158198, by rfl⟩ : syracuseStep 3088529 = 2316397) B2316397
theorem B3711203 : Blo 912577 3711203 := bstep (se 1 (by rfl) ⟨2783402, by rfl⟩ : syracuseStep 3711203 = 5566805) B5566805
theorem B1155379 : Blo 912577 1155379 := bstep (se 1 (by rfl) ⟨866534, by rfl⟩ : syracuseStep 1155379 = 1733069) B1733069
theorem B1155475 : Blo 912577 1155475 := bstep (se 1 (by rfl) ⟨866606, by rfl⟩ : syracuseStep 1155475 = 1733213) B1733213
theorem B991651 : Blo 912577 991651 := bstep (se 1 (by rfl) ⟨743738, by rfl⟩ : syracuseStep 991651 = 1487477) B1487477
theorem B5022179 : Blo 912577 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B3089069 : Blo 912577 3089069 := bstep (se 3 (by rfl) ⟨579200, by rfl⟩ : syracuseStep 3089069 = 1158401) B1158401
theorem B3089123 : Blo 912577 3089123 := bstep (se 1 (by rfl) ⟨2316842, by rfl⟩ : syracuseStep 3089123 = 4633685) B4633685
theorem B926483 : Blo 912577 926483 := bstep (se 1 (by rfl) ⟨694862, by rfl⟩ : syracuseStep 926483 = 1389725) B1389725
theorem B1155971 : Blo 912577 1155971 := bstep (se 1 (by rfl) ⟨866978, by rfl⟩ : syracuseStep 1155971 = 1733957) B1733957
theorem B3089393 : Blo 912577 3089393 := bstep (se 2 (by rfl) ⟨1158522, by rfl⟩ : syracuseStep 3089393 = 2317045) B2317045
theorem B9381005 : Blo 912577 9381005 := bstep (se 3 (by rfl) ⟨1758938, by rfl⟩ : syracuseStep 9381005 = 3517877) B3517877
theorem B2467043 : Blo 912577 2467043 := bstep (se 1 (by rfl) ⟨1850282, by rfl⟩ : syracuseStep 2467043 = 3700565) B3700565
theorem B10396997 : Blo 912577 10396997 := bstep (se 4 (by rfl) ⟨974718, by rfl⟩ : syracuseStep 10396997 = 1949437) B1949437
theorem B2926001 : Blo 912577 2926001 := bstep (se 2 (by rfl) ⟨1097250, by rfl⟩ : syracuseStep 2926001 = 2194501) B2194501
theorem B1648067 : Blo 912577 1648067 := bstep (se 1 (by rfl) ⟨1236050, by rfl⟩ : syracuseStep 1648067 = 2472101) B2472101
theorem B3089933 : Blo 912577 3089933 := bstep (se 3 (by rfl) ⟨579362, by rfl⟩ : syracuseStep 3089933 = 1158725) B1158725
theorem B4400689 : Blo 912577 4400689 := bstep (se 2 (by rfl) ⟨1650258, by rfl⟩ : syracuseStep 4400689 = 3300517) B3300517
theorem B1156675 : Blo 912577 1156675 := bstep (se 1 (by rfl) ⟨867506, by rfl⟩ : syracuseStep 1156675 = 1735013) B1735013
theorem B3089987 : Blo 912577 3089987 := bstep (se 1 (by rfl) ⟨2317490, by rfl⟩ : syracuseStep 3089987 = 4634981) B4634981
theorem B1156771 : Blo 912577 1156771 := bstep (se 1 (by rfl) ⟨867578, by rfl⟩ : syracuseStep 1156771 = 1735157) B1735157
theorem B3090257 : Blo 912577 3090257 := bstep (se 2 (by rfl) ⟨1158846, by rfl⟩ : syracuseStep 3090257 = 2317693) B2317693
theorem B1648529 : Blo 912577 1648529 := bstep (se 2 (by rfl) ⟨618198, by rfl⟩ : syracuseStep 1648529 = 1236397) B1236397
theorem B1157267 : Blo 912577 1157267 := bstep (se 1 (by rfl) ⟨867950, by rfl⟩ : syracuseStep 1157267 = 1735901) B1735901
theorem B3909809 : Blo 912577 3909809 := bstep (se 2 (by rfl) ⟨1466178, by rfl⟩ : syracuseStep 3909809 = 2932357) B2932357
theorem B4630769 : Blo 912577 4630769 := bstep (se 2 (by rfl) ⟨1736538, by rfl⟩ : syracuseStep 4630769 = 3473077) B3473077
theorem B2926925 : Blo 912577 2926925 := bstep (se 3 (by rfl) ⟨548798, by rfl⟩ : syracuseStep 2926925 = 1097597) B1097597
theorem B3090797 : Blo 912577 3090797 := bstep (se 3 (by rfl) ⟨579524, by rfl⟩ : syracuseStep 3090797 = 1159049) B1159049
theorem B3090851 : Blo 912577 3090851 := bstep (se 1 (by rfl) ⟨2318138, by rfl⟩ : syracuseStep 3090851 = 4636277) B4636277
theorem B2927117 : Blo 912577 2927117 := bstep (se 3 (by rfl) ⟨548834, by rfl⟩ : syracuseStep 2927117 = 1097669) B1097669
theorem B2599523 : Blo 912577 2599523 := bstep (se 1 (by rfl) ⟨1949642, by rfl⟩ : syracuseStep 2599523 = 3899285) B3899285
theorem B17836685 : Blo 912577 17836685 := bstep (se 3 (by rfl) ⟨3344378, by rfl⟩ : syracuseStep 17836685 = 6688757) B6688757
theorem B3091121 : Blo 912577 3091121 := bstep (se 2 (by rfl) ⟨1159170, by rfl⟩ : syracuseStep 3091121 = 2318341) B2318341
theorem B1026787 : Blo 912577 1026787 := bstep (se 1 (by rfl) ⟨770090, by rfl⟩ : syracuseStep 1026787 = 1540181) B1540181
theorem B3910477 : Blo 912577 3910477 := bstep (se 3 (by rfl) ⟨733214, by rfl⟩ : syracuseStep 3910477 = 1466429) B1466429
theorem B1157971 : Blo 912577 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B928595 : Blo 912577 928595 := bstep (se 1 (by rfl) ⟨696446, by rfl⟩ : syracuseStep 928595 = 1392893) B1392893
theorem B1026931 : Blo 912577 1026931 := bstep (se 1 (by rfl) ⟨770198, by rfl⟩ : syracuseStep 1026931 = 1540397) B1540397
theorem B1158067 : Blo 912577 1158067 := bstep (se 1 (by rfl) ⟨868550, by rfl⟩ : syracuseStep 1158067 = 1737101) B1737101
theorem B7810019 : Blo 912577 7810019 := bstep (se 1 (by rfl) ⟨5857514, by rfl⟩ : syracuseStep 7810019 = 11715029) B11715029
theorem B5352419 : Blo 912577 5352419 := bstep (se 1 (by rfl) ⟨4014314, by rfl⟩ : syracuseStep 5352419 = 8028629) B8028629
theorem B1027075 : Blo 912577 1027075 := bstep (se 1 (by rfl) ⟨770306, by rfl⟩ : syracuseStep 1027075 = 1540613) B1540613
theorem B1387633 : Blo 912577 1387633 := bstep (se 2 (by rfl) ⟨520362, by rfl⟩ : syracuseStep 1387633 = 1040725) B1040725
theorem B1027219 : Blo 912577 1027219 := bstep (se 1 (by rfl) ⟨770414, by rfl⟩ : syracuseStep 1027219 = 1540829) B1540829
theorem B3091661 : Blo 912577 3091661 := bstep (se 3 (by rfl) ⟨579686, by rfl⟩ : syracuseStep 3091661 = 1159373) B1159373
theorem B3091715 : Blo 912577 3091715 := bstep (se 1 (by rfl) ⟨2318786, by rfl⟩ : syracuseStep 3091715 = 4637573) B4637573
theorem B1027363 : Blo 912577 1027363 := bstep (se 1 (by rfl) ⟨770522, by rfl⟩ : syracuseStep 1027363 = 1541045) B1541045
theorem B2600333 : Blo 912577 2600333 := bstep (se 3 (by rfl) ⟨487562, by rfl⟩ : syracuseStep 2600333 = 975125) B975125
theorem B1158563 : Blo 912577 1158563 := bstep (se 1 (by rfl) ⟨868922, by rfl⟩ : syracuseStep 1158563 = 1737845) B1737845
theorem B3911075 : Blo 912577 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B1027507 : Blo 912577 1027507 := bstep (se 1 (by rfl) ⟨770630, by rfl⟩ : syracuseStep 1027507 = 1541261) B1541261
theorem B3091985 : Blo 912577 3091985 := bstep (se 2 (by rfl) ⟨1159494, by rfl⟩ : syracuseStep 3091985 = 2318989) B2318989
theorem B3517987 : Blo 912577 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B1027651 : Blo 912577 1027651 := bstep (se 1 (by rfl) ⟨770738, by rfl⟩ : syracuseStep 1027651 = 1541477) B1541477
theorem B2600525 : Blo 912577 2600525 := bstep (se 3 (by rfl) ⟨487598, by rfl⟩ : syracuseStep 2600525 = 975197) B975197
theorem B4402765 : Blo 912577 4402765 := bstep (se 3 (by rfl) ⟨825518, by rfl⟩ : syracuseStep 4402765 = 1651037) B1651037
theorem B4632227 : Blo 912577 4632227 := bstep (se 1 (by rfl) ⟨3474170, by rfl⟩ : syracuseStep 4632227 = 6948341) B6948341
theorem B1027795 : Blo 912577 1027795 := bstep (se 1 (by rfl) ⟨770846, by rfl⟩ : syracuseStep 1027795 = 1541693) B1541693
theorem B1027939 : Blo 912577 1027939 := bstep (se 1 (by rfl) ⟨770954, by rfl⟩ : syracuseStep 1027939 = 1541909) B1541909
theorem B1028083 : Blo 912577 1028083 := bstep (se 1 (by rfl) ⟨771062, by rfl⟩ : syracuseStep 1028083 = 1542125) B1542125
theorem B3092525 : Blo 912577 3092525 := bstep (se 3 (by rfl) ⟨579848, by rfl⟩ : syracuseStep 3092525 = 1159697) B1159697
theorem B1159267 : Blo 912577 1159267 := bstep (se 1 (by rfl) ⟨869450, by rfl⟩ : syracuseStep 1159267 = 1738901) B1738901
theorem B3092579 : Blo 912577 3092579 := bstep (se 1 (by rfl) ⟨2319434, by rfl⟩ : syracuseStep 3092579 = 4638869) B4638869
theorem B1028227 : Blo 912577 1028227 := bstep (se 1 (by rfl) ⟨771170, by rfl⟩ : syracuseStep 1028227 = 1542341) B1542341
theorem B1159363 : Blo 912577 1159363 := bstep (se 1 (by rfl) ⟨869522, by rfl⟩ : syracuseStep 1159363 = 1739045) B1739045
theorem B2928899 : Blo 912577 2928899 := bstep (se 1 (by rfl) ⟨2196674, by rfl⟩ : syracuseStep 2928899 = 4393349) B4393349
theorem B1028371 : Blo 912577 1028371 := bstep (se 1 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 1028371 = 1542557) B1542557
theorem B3092849 : Blo 912577 3092849 := bstep (se 2 (by rfl) ⟨1159818, by rfl⟩ : syracuseStep 3092849 = 2319637) B2319637
theorem B2470285 : Blo 912577 2470285 := bstep (se 3 (by rfl) ⟨463178, by rfl⟩ : syracuseStep 2470285 = 926357) B926357
theorem B1028515 : Blo 912577 1028515 := bstep (se 1 (by rfl) ⟨771386, by rfl⟩ : syracuseStep 1028515 = 1542773) B1542773
theorem B4633037 : Blo 912577 4633037 := bstep (se 3 (by rfl) ⟨868694, by rfl⟩ : syracuseStep 4633037 = 1737389) B1737389
theorem B2601517 : Blo 912577 2601517 := bstep (se 3 (by rfl) ⟨487784, by rfl⟩ : syracuseStep 2601517 = 975569) B975569
theorem B1028659 : Blo 912577 1028659 := bstep (se 1 (by rfl) ⟨771494, by rfl⟩ : syracuseStep 1028659 = 1542989) B1542989
theorem B1159859 : Blo 912577 1159859 := bstep (se 1 (by rfl) ⟨869894, by rfl⟩ : syracuseStep 1159859 = 1739789) B1739789
theorem B1028803 : Blo 912577 1028803 := bstep (se 1 (by rfl) ⟨771602, by rfl⟩ : syracuseStep 1028803 = 1543205) B1543205
theorem B1028947 : Blo 912577 1028947 := bstep (se 1 (by rfl) ⟨771710, by rfl⟩ : syracuseStep 1028947 = 1543421) B1543421
theorem B3093389 : Blo 912577 3093389 := bstep (se 3 (by rfl) ⟨580010, by rfl⟩ : syracuseStep 3093389 = 1160021) B1160021
theorem B4699043 : Blo 912577 4699043 := bstep (se 1 (by rfl) ⟨3524282, by rfl⟩ : syracuseStep 4699043 = 7048565) B7048565
theorem B3093443 : Blo 912577 3093443 := bstep (se 1 (by rfl) ⟨2320082, by rfl⟩ : syracuseStep 3093443 = 4640165) B4640165
theorem B1029091 : Blo 912577 1029091 := bstep (se 1 (by rfl) ⟨771818, by rfl⟩ : syracuseStep 1029091 = 1543637) B1543637
theorem B1029235 : Blo 912577 1029235 := bstep (se 1 (by rfl) ⟨771926, by rfl⟩ : syracuseStep 1029235 = 1543853) B1543853
theorem B2634947 : Blo 912577 2634947 := bstep (se 1 (by rfl) ⟨1976210, by rfl⟩ : syracuseStep 2634947 = 3952421) B3952421
theorem B1029379 : Blo 912577 1029379 := bstep (se 1 (by rfl) ⟨772034, by rfl⟩ : syracuseStep 1029379 = 1544069) B1544069
theorem B2635085 : Blo 912577 2635085 := bstep (se 3 (by rfl) ⟨494078, by rfl⟩ : syracuseStep 2635085 = 988157) B988157
theorem B1029523 : Blo 912577 1029523 := bstep (se 1 (by rfl) ⟨772142, by rfl⟩ : syracuseStep 1029523 = 1544285) B1544285
theorem B1029667 : Blo 912577 1029667 := bstep (se 1 (by rfl) ⟨772250, by rfl⟩ : syracuseStep 1029667 = 1544501) B1544501
theorem B3290701 : Blo 912577 3290701 := bstep (se 3 (by rfl) ⟨617006, by rfl⟩ : syracuseStep 3290701 = 1234013) B1234013
theorem B2635409 : Blo 912577 2635409 := bstep (se 2 (by rfl) ⟨988278, by rfl⟩ : syracuseStep 2635409 = 1976557) B1976557
theorem B1029811 : Blo 912577 1029811 := bstep (se 1 (by rfl) ⟨772358, by rfl⟩ : syracuseStep 1029811 = 1544717) B1544717
theorem B2504515 : Blo 912577 2504515 := bstep (se 1 (by rfl) ⟨1878386, by rfl⟩ : syracuseStep 2504515 = 3756773) B3756773
theorem B1029955 : Blo 912577 1029955 := bstep (se 1 (by rfl) ⟨772466, by rfl⟩ : syracuseStep 1029955 = 1544933) B1544933
theorem B1030099 : Blo 912577 1030099 := bstep (se 1 (by rfl) ⟨772574, by rfl⟩ : syracuseStep 1030099 = 1545149) B1545149
theorem B1030243 : Blo 912577 1030243 := bstep (se 1 (by rfl) ⟨772682, by rfl⟩ : syracuseStep 1030243 = 1545365) B1545365
theorem B4700273 : Blo 912577 4700273 := bstep (se 2 (by rfl) ⟨1762602, by rfl⟩ : syracuseStep 4700273 = 3525205) B3525205
theorem B2603249 : Blo 912577 2603249 := bstep (se 2 (by rfl) ⟨976218, by rfl⟩ : syracuseStep 2603249 = 1952437) B1952437
theorem B1030387 : Blo 912577 1030387 := bstep (se 1 (by rfl) ⟨772790, by rfl⟩ : syracuseStep 1030387 = 1545581) B1545581
theorem B2931025 : Blo 912577 2931025 := bstep (se 2 (by rfl) ⟨1099134, by rfl⟩ : syracuseStep 2931025 = 2198269) B2198269
theorem B1030531 : Blo 912577 1030531 := bstep (se 1 (by rfl) ⟨772898, by rfl⟩ : syracuseStep 1030531 = 1545797) B1545797
theorem B2603441 : Blo 912577 2603441 := bstep (se 2 (by rfl) ⟨976290, by rfl⟩ : syracuseStep 2603441 = 1952581) B1952581
theorem B11450893 : Blo 912577 11450893 := bstep (se 3 (by rfl) ⟨2147042, by rfl⟩ : syracuseStep 11450893 = 4294085) B4294085
theorem B1030675 : Blo 912577 1030675 := bstep (se 1 (by rfl) ⟨773006, by rfl⟩ : syracuseStep 1030675 = 1546013) B1546013
theorem B1391185 : Blo 912577 1391185 := bstep (se 2 (by rfl) ⟨521694, by rfl⟩ : syracuseStep 1391185 = 1043389) B1043389
theorem B1030819 : Blo 912577 1030819 := bstep (se 1 (by rfl) ⟨773114, by rfl⟩ : syracuseStep 1030819 = 1546229) B1546229
theorem B2472643 : Blo 912577 2472643 := bstep (se 1 (by rfl) ⟨1854482, by rfl⟩ : syracuseStep 2472643 = 3708965) B3708965
theorem B8043235 : Blo 912577 8043235 := bstep (se 1 (by rfl) ⟨6032426, by rfl⟩ : syracuseStep 8043235 = 12064853) B12064853
theorem B1030963 : Blo 912577 1030963 := bstep (se 1 (by rfl) ⟨773222, by rfl⟩ : syracuseStep 1030963 = 1546445) B1546445
theorem B1031107 : Blo 912577 1031107 := bstep (se 1 (by rfl) ⟨773330, by rfl⟩ : syracuseStep 1031107 = 1546661) B1546661
theorem B10402829 : Blo 912577 10402829 := bstep (se 3 (by rfl) ⟨1950530, by rfl⟩ : syracuseStep 10402829 = 3901061) B3901061
theorem B3914851 : Blo 912577 3914851 := bstep (se 1 (by rfl) ⟨2936138, by rfl⟩ : syracuseStep 3914851 = 5872277) B5872277
theorem B1096915 : Blo 912577 1096915 := bstep (se 1 (by rfl) ⟨822686, by rfl⟩ : syracuseStep 1096915 = 1645373) B1645373
theorem B4635953 : Blo 912577 4635953 := bstep (se 2 (by rfl) ⟨1738482, by rfl⟩ : syracuseStep 4635953 = 3476965) B3476965
theorem B1097059 : Blo 912577 1097059 := bstep (se 1 (by rfl) ⟨822794, by rfl⟩ : syracuseStep 1097059 = 1645589) B1645589
theorem B18759053 : Blo 912577 18759053 := bstep (se 3 (by rfl) ⟨3517322, by rfl⟩ : syracuseStep 18759053 = 7034645) B7034645
theorem B2604433 : Blo 912577 2604433 := bstep (se 2 (by rfl) ⟨976662, by rfl⟩ : syracuseStep 2604433 = 1953325) B1953325
theorem B1097155 : Blo 912577 1097155 := bstep (se 1 (by rfl) ⟨822866, by rfl⟩ : syracuseStep 1097155 = 1645733) B1645733
theorem B5848517 : Blo 912577 5848517 := bstep (se 4 (by rfl) ⟨548298, by rfl⟩ : syracuseStep 5848517 = 1096597) B1096597
theorem B2604707 : Blo 912577 2604707 := bstep (se 1 (by rfl) ⟨1953530, by rfl⟩ : syracuseStep 2604707 = 3907061) B3907061
theorem B1392419 : Blo 912577 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B2604899 : Blo 912577 2604899 := bstep (se 1 (by rfl) ⟨1953674, by rfl⟩ : syracuseStep 2604899 = 3907349) B3907349
theorem B1097635 : Blo 912577 1097635 := bstep (se 1 (by rfl) ⟨823226, by rfl⟩ : syracuseStep 1097635 = 1646453) B1646453
theorem B1392547 : Blo 912577 1392547 := bstep (se 1 (by rfl) ⟨1044410, by rfl⟩ : syracuseStep 1392547 = 2088821) B2088821
theorem B2310353 : Blo 912577 2310353 := bstep (se 2 (by rfl) ⟨866382, by rfl⟩ : syracuseStep 2310353 = 1732765) B1732765
theorem B2932973 : Blo 912577 2932973 := bstep (se 3 (by rfl) ⟨549932, by rfl⟩ : syracuseStep 2932973 = 1099865) B1099865
theorem B2310403 : Blo 912577 2310403 := bstep (se 1 (by rfl) ⟨1732802, by rfl⟩ : syracuseStep 2310403 = 3465605) B3465605
theorem B2933101 : Blo 912577 2933101 := bstep (se 3 (by rfl) ⟨549956, by rfl⟩ : syracuseStep 2933101 = 1099913) B1099913
theorem B2310545 : Blo 912577 2310545 := bstep (se 2 (by rfl) ⟨866454, by rfl⟩ : syracuseStep 2310545 = 1732909) B1732909
theorem B3129905 : Blo 912577 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B2605709 : Blo 912577 2605709 := bstep (se 3 (by rfl) ⟨488570, by rfl⟩ : syracuseStep 2605709 = 977141) B977141
theorem B4178573 : Blo 912577 4178573 := bstep (se 3 (by rfl) ⟨783482, by rfl⟩ : syracuseStep 4178573 = 1566965) B1566965
theorem B4637411 : Blo 912577 4637411 := bstep (se 1 (by rfl) ⟨3478058, by rfl⟩ : syracuseStep 4637411 = 6956117) B6956117
theorem B2081521 : Blo 912577 2081521 := bstep (se 2 (by rfl) ⟨780570, by rfl⟩ : syracuseStep 2081521 = 1561141) B1561141
theorem B2081603 : Blo 912577 2081603 := bstep (se 1 (by rfl) ⟨1561202, by rfl⟩ : syracuseStep 2081603 = 3122405) B3122405
theorem B2605891 : Blo 912577 2605891 := bstep (se 1 (by rfl) ⟨1954418, by rfl⟩ : syracuseStep 2605891 = 3908837) B3908837
theorem B9290821 : Blo 912577 9290821 := bstep (se 4 (by rfl) ⟨871014, by rfl⟩ : syracuseStep 9290821 = 1742029) B1742029
theorem B2606381 : Blo 912577 2606381 := bstep (se 3 (by rfl) ⟨488696, by rfl⟩ : syracuseStep 2606381 = 977393) B977393
theorem B2082115 : Blo 912577 2082115 := bstep (se 1 (by rfl) ⟨1561586, by rfl⟩ : syracuseStep 2082115 = 3123173) B3123173
theorem B5850467 : Blo 912577 5850467 := bstep (se 1 (by rfl) ⟨4387850, by rfl⟩ : syracuseStep 5850467 = 8775701) B8775701
theorem B2311537 : Blo 912577 2311537 := bstep (se 2 (by rfl) ⟨866826, by rfl⟩ : syracuseStep 2311537 = 1733653) B1733653
theorem B4638221 : Blo 912577 4638221 := bstep (se 3 (by rfl) ⟨869666, by rfl⟩ : syracuseStep 4638221 = 1739333) B1739333
theorem B1951249 : Blo 912577 1951249 := bstep (se 2 (by rfl) ⟨731718, by rfl⟩ : syracuseStep 1951249 = 1463437) B1463437
theorem B9520739 : Blo 912577 9520739 := bstep (se 1 (by rfl) ⟨7140554, by rfl⟩ : syracuseStep 9520739 = 14281109) B14281109
theorem B2311811 : Blo 912577 2311811 := bstep (se 1 (by rfl) ⟨1733858, by rfl⟩ : syracuseStep 2311811 = 3467717) B3467717
theorem B2475821 : Blo 912577 2475821 := bstep (se 3 (by rfl) ⟨464216, by rfl⟩ : syracuseStep 2475821 = 928433) B928433
theorem B2312003 : Blo 912577 2312003 := bstep (se 1 (by rfl) ⟨1734002, by rfl⟩ : syracuseStep 2312003 = 3468005) B3468005
theorem B10405745 : Blo 912577 10405745 := bstep (se 2 (by rfl) ⟨3902154, by rfl⟩ : syracuseStep 10405745 = 7804309) B7804309
theorem B2639843 : Blo 912577 2639843 := bstep (se 1 (by rfl) ⟨1979882, by rfl⟩ : syracuseStep 2639843 = 3959765) B3959765
theorem B2934947 : Blo 912577 2934947 := bstep (se 1 (by rfl) ⟨2201210, by rfl⟩ : syracuseStep 2934947 = 4402421) B4402421
theorem B2935075 : Blo 912577 2935075 := bstep (se 1 (by rfl) ⟨2201306, by rfl⟩ : syracuseStep 2935075 = 4402613) B4402613
theorem B2935217 : Blo 912577 2935217 := bstep (se 2 (by rfl) ⟨1100706, by rfl⟩ : syracuseStep 2935217 = 2201413) B2201413
theorem B2607565 : Blo 912577 2607565 := bstep (se 3 (by rfl) ⟨488918, by rfl⟩ : syracuseStep 2607565 = 977837) B977837
theorem B2935331 : Blo 912577 2935331 := bstep (se 1 (by rfl) ⟨2201498, by rfl⟩ : syracuseStep 2935331 = 4402997) B4402997
theorem B2345539 : Blo 912577 2345539 := bstep (se 1 (by rfl) ⟨1759154, by rfl⟩ : syracuseStep 2345539 = 3518309) B3518309
theorem B2476675 : Blo 912577 2476675 := bstep (se 1 (by rfl) ⟨1857506, by rfl⟩ : syracuseStep 2476675 = 3715013) B3715013
theorem B2312945 : Blo 912577 2312945 := bstep (se 2 (by rfl) ⟨867354, by rfl⟩ : syracuseStep 2312945 = 1734709) B1734709
theorem B2312995 : Blo 912577 2312995 := bstep (se 1 (by rfl) ⟨1734746, by rfl⟩ : syracuseStep 2312995 = 3469493) B3469493
theorem B2313137 : Blo 912577 2313137 := bstep (se 2 (by rfl) ⟨867426, by rfl⟩ : syracuseStep 2313137 = 1734853) B1734853
theorem B2968625 : Blo 912577 2968625 := bstep (se 2 (by rfl) ⟨1113234, by rfl⟩ : syracuseStep 2968625 = 2226469) B2226469
theorem B3296483 : Blo 912577 3296483 := bstep (se 1 (by rfl) ⟨2472362, by rfl⟩ : syracuseStep 3296483 = 4944725) B4944725
theorem B2969041 : Blo 912577 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B2608625 : Blo 912577 2608625 := bstep (se 2 (by rfl) ⟨978234, by rfl⟩ : syracuseStep 2608625 = 1956469) B1956469
theorem B5853005 : Blo 912577 5853005 := bstep (se 3 (by rfl) ⟨1097438, by rfl⟩ : syracuseStep 5853005 = 2194877) B2194877
theorem B2314129 : Blo 912577 2314129 := bstep (se 2 (by rfl) ⟨867798, by rfl⟩ : syracuseStep 2314129 = 1735597) B1735597
theorem B2609297 : Blo 912577 2609297 := bstep (se 2 (by rfl) ⟨978486, by rfl⟩ : syracuseStep 2609297 = 1956973) B1956973
theorem B2314403 : Blo 912577 2314403 := bstep (se 1 (by rfl) ⟨1735802, by rfl⟩ : syracuseStep 2314403 = 3471605) B3471605
theorem B1855715 : Blo 912577 1855715 := bstep (se 1 (by rfl) ⟨1391786, by rfl⟩ : syracuseStep 1855715 = 2783573) B2783573
theorem B2314595 : Blo 912577 2314595 := bstep (se 1 (by rfl) ⟨1735946, by rfl⟩ : syracuseStep 2314595 = 3471893) B3471893
theorem B3297635 : Blo 912577 3297635 := bstep (se 1 (by rfl) ⟨2473226, by rfl⟩ : syracuseStep 3297635 = 4946453) B4946453
theorem B2970083 : Blo 912577 2970083 := bstep (se 1 (by rfl) ⟨2227562, by rfl⟩ : syracuseStep 2970083 = 4455125) B4455125
theorem B1954307 : Blo 912577 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B1462963 : Blo 912577 1462963 := bstep (se 1 (by rfl) ⟨1097222, by rfl⟩ : syracuseStep 1462963 = 2194445) B2194445
theorem B2085617 : Blo 912577 2085617 := bstep (se 2 (by rfl) ⟨782106, by rfl⟩ : syracuseStep 2085617 = 1564213) B1564213
theorem B1233715 : Blo 912577 1233715 := bstep (se 1 (by rfl) ⟨925286, by rfl⟩ : syracuseStep 1233715 = 1850573) B1850573
theorem B3298211 : Blo 912577 3298211 := bstep (se 1 (by rfl) ⟨2473658, by rfl⟩ : syracuseStep 3298211 = 4947317) B4947317
theorem B2610083 : Blo 912577 2610083 := bstep (se 1 (by rfl) ⟨1957562, by rfl⟩ : syracuseStep 2610083 = 3915125) B3915125
theorem B4510691 : Blo 912577 4510691 := bstep (se 1 (by rfl) ⟨3383018, by rfl⟩ : syracuseStep 4510691 = 6766037) B6766037
theorem B1463411 : Blo 912577 1463411 := bstep (se 1 (by rfl) ⟨1097558, by rfl⟩ : syracuseStep 1463411 = 2195117) B2195117
theorem B1299665 : Blo 912577 1299665 := bstep (se 2 (by rfl) ⟨487374, by rfl⟩ : syracuseStep 1299665 = 974749) B974749
theorem B2315537 : Blo 912577 2315537 := bstep (se 2 (by rfl) ⟨868326, by rfl⟩ : syracuseStep 2315537 = 1736653) B1736653
theorem B2315587 : Blo 912577 2315587 := bstep (se 1 (by rfl) ⟨1736690, by rfl⟩ : syracuseStep 2315587 = 3473381) B3473381
theorem B2053457 : Blo 912577 2053457 := bstep (se 2 (by rfl) ⟨770046, by rfl⟩ : syracuseStep 2053457 = 1540093) B1540093
theorem B1234273 : Blo 912577 1234273 := bstep (se 2 (by rfl) ⟨462852, by rfl⟩ : syracuseStep 1234273 = 925705) B925705
theorem B2053475 : Blo 912577 2053475 := bstep (se 1 (by rfl) ⟨1540106, by rfl⟩ : syracuseStep 2053475 = 3080213) B3080213
theorem B1955171 : Blo 912577 1955171 := bstep (se 1 (by rfl) ⟨1466378, by rfl⟩ : syracuseStep 1955171 = 2932757) B2932757
theorem B1562017 : Blo 912577 1562017 := bstep (se 2 (by rfl) ⟨585756, by rfl⟩ : syracuseStep 1562017 = 1171513) B1171513
theorem B5559749 : Blo 912577 5559749 := bstep (se 4 (by rfl) ⟨521226, by rfl⟩ : syracuseStep 5559749 = 1042453) B1042453
theorem B2315729 : Blo 912577 2315729 := bstep (se 2 (by rfl) ⟨868398, by rfl⟩ : syracuseStep 2315729 = 1736797) B1736797
theorem B1955281 : Blo 912577 1955281 := bstep (se 2 (by rfl) ⟨733230, by rfl⟩ : syracuseStep 1955281 = 1466461) B1466461
theorem B2053745 : Blo 912577 2053745 := bstep (se 2 (by rfl) ⟨770154, by rfl⟩ : syracuseStep 2053745 = 1540309) B1540309
theorem B2053763 : Blo 912577 2053763 := bstep (se 1 (by rfl) ⟨1540322, by rfl⟩ : syracuseStep 2053763 = 3080645) B3080645
theorem B1463969 : Blo 912577 1463969 := bstep (se 2 (by rfl) ⟨548988, by rfl⟩ : syracuseStep 1463969 = 1097977) B1097977
theorem B1234721 : Blo 912577 1234721 := bstep (se 2 (by rfl) ⟨463020, by rfl⟩ : syracuseStep 1234721 = 926041) B926041
theorem B1464193 : Blo 912577 1464193 := bstep (se 2 (by rfl) ⟨549072, by rfl⟩ : syracuseStep 1464193 = 1098145) B1098145
theorem B2054033 : Blo 912577 2054033 := bstep (se 2 (by rfl) ⟨770262, by rfl⟩ : syracuseStep 2054033 = 1540525) B1540525
theorem B2054051 : Blo 912577 2054051 := bstep (se 1 (by rfl) ⟨1540538, by rfl⟩ : syracuseStep 2054051 = 3081077) B3081077
theorem B1464257 : Blo 912577 1464257 := bstep (se 2 (by rfl) ⟨549096, by rfl⟩ : syracuseStep 1464257 = 1098193) B1098193
theorem B5199821 : Blo 912577 5199821 := bstep (se 3 (by rfl) ⟨974966, by rfl⟩ : syracuseStep 5199821 = 1949933) B1949933
theorem B1300531 : Blo 912577 1300531 := bstep (se 1 (by rfl) ⟨975398, by rfl⟩ : syracuseStep 1300531 = 1950797) B1950797
theorem B1464385 : Blo 912577 1464385 := bstep (se 2 (by rfl) ⟨549144, by rfl⟩ : syracuseStep 1464385 = 1098289) B1098289
theorem B1300627 : Blo 912577 1300627 := bstep (se 1 (by rfl) ⟨975470, by rfl⟩ : syracuseStep 1300627 = 1950941) B1950941
theorem B2054321 : Blo 912577 2054321 := bstep (se 2 (by rfl) ⟨770370, by rfl⟩ : syracuseStep 2054321 = 1540741) B1540741
theorem B2054339 : Blo 912577 2054339 := bstep (se 1 (by rfl) ⟨1540754, by rfl⟩ : syracuseStep 2054339 = 3081509) B3081509
theorem B5560525 : Blo 912577 5560525 := bstep (se 3 (by rfl) ⟨1042598, by rfl⟩ : syracuseStep 5560525 = 2085197) B2085197
theorem B1235251 : Blo 912577 1235251 := bstep (se 1 (by rfl) ⟨926438, by rfl⟩ : syracuseStep 1235251 = 1852877) B1852877
theorem B5626181 : Blo 912577 5626181 := bstep (se 4 (by rfl) ⟨527454, by rfl⟩ : syracuseStep 5626181 = 1054909) B1054909
theorem B8345969 : Blo 912577 8345969 := bstep (se 2 (by rfl) ⟨3129738, by rfl⟩ : syracuseStep 8345969 = 6259477) B6259477
theorem B1857937 : Blo 912577 1857937 := bstep (se 2 (by rfl) ⟨696726, by rfl⟩ : syracuseStep 1857937 = 1393453) B1393453
theorem B2316721 : Blo 912577 2316721 := bstep (se 2 (by rfl) ⟨868770, by rfl⟩ : syracuseStep 2316721 = 1737541) B1737541
theorem B2054609 : Blo 912577 2054609 := bstep (se 2 (by rfl) ⟨770478, by rfl⟩ : syracuseStep 2054609 = 1540957) B1540957
theorem B2054627 : Blo 912577 2054627 := bstep (se 1 (by rfl) ⟨1540970, by rfl⟩ : syracuseStep 2054627 = 3081941) B3081941
theorem B3299825 : Blo 912577 3299825 := bstep (se 2 (by rfl) ⟨1237434, by rfl⟩ : syracuseStep 3299825 = 2474869) B2474869
theorem B1301123 : Blo 912577 1301123 := bstep (se 1 (by rfl) ⟨975842, by rfl⟩ : syracuseStep 1301123 = 1951685) B1951685
theorem B1694353 : Blo 912577 1694353 := bstep (se 2 (by rfl) ⟨635382, by rfl⟩ : syracuseStep 1694353 = 1270765) B1270765
theorem B2316995 : Blo 912577 2316995 := bstep (se 1 (by rfl) ⟨1737746, by rfl⟩ : syracuseStep 2316995 = 3475493) B3475493
theorem B2054897 : Blo 912577 2054897 := bstep (se 2 (by rfl) ⟨770586, by rfl⟩ : syracuseStep 2054897 = 1541173) B1541173
theorem B2054915 : Blo 912577 2054915 := bstep (se 1 (by rfl) ⟨1541186, by rfl⟩ : syracuseStep 2054915 = 3082373) B3082373
theorem B3300173 : Blo 912577 3300173 := bstep (se 3 (by rfl) ⟨618782, by rfl⟩ : syracuseStep 3300173 = 1237565) B1237565
theorem B1563475 : Blo 912577 1563475 := bstep (se 1 (by rfl) ⟨1172606, by rfl⟩ : syracuseStep 1563475 = 2345213) B2345213
theorem B2317187 : Blo 912577 2317187 := bstep (se 1 (by rfl) ⟨1737890, by rfl⟩ : syracuseStep 2317187 = 3475781) B3475781
theorem B2055185 : Blo 912577 2055185 := bstep (se 2 (by rfl) ⟨770694, by rfl⟩ : syracuseStep 2055185 = 1541389) B1541389
theorem B2055203 : Blo 912577 2055203 := bstep (se 1 (by rfl) ⟨1541402, by rfl⟩ : syracuseStep 2055203 = 3082805) B3082805
theorem B3759203 : Blo 912577 3759203 := bstep (se 1 (by rfl) ⟨2819402, by rfl⟩ : syracuseStep 3759203 = 5638805) B5638805
theorem B1301761 : Blo 912577 1301761 := bstep (se 2 (by rfl) ⟨488160, by rfl⟩ : syracuseStep 1301761 = 976321) B976321
theorem B2055473 : Blo 912577 2055473 := bstep (se 2 (by rfl) ⟨770802, by rfl⟩ : syracuseStep 2055473 = 1541605) B1541605
theorem B2055491 : Blo 912577 2055491 := bstep (se 1 (by rfl) ⟨1541618, by rfl⟩ : syracuseStep 2055491 = 3083237) B3083237
theorem B3300749 : Blo 912577 3300749 := bstep (se 3 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 3300749 = 1237781) B1237781
theorem B1564049 : Blo 912577 1564049 := bstep (se 2 (by rfl) ⟨586518, by rfl⟩ : syracuseStep 1564049 = 1173037) B1173037
theorem B2088355 : Blo 912577 2088355 := bstep (se 1 (by rfl) ⟨1566266, by rfl⟩ : syracuseStep 2088355 = 3132533) B3132533
theorem B1957297 : Blo 912577 1957297 := bstep (se 2 (by rfl) ⟨733986, by rfl⟩ : syracuseStep 1957297 = 1467973) B1467973
theorem B2055761 : Blo 912577 2055761 := bstep (se 2 (by rfl) ⟨770910, by rfl⟩ : syracuseStep 2055761 = 1541821) B1541821
theorem B1302097 : Blo 912577 1302097 := bstep (se 2 (by rfl) ⟨488286, by rfl⟩ : syracuseStep 1302097 = 976573) B976573
theorem B2055779 : Blo 912577 2055779 := bstep (se 1 (by rfl) ⟨1541834, by rfl⟩ : syracuseStep 2055779 = 3083669) B3083669
theorem B974531 : Blo 912577 974531 := bstep (se 1 (by rfl) ⟨730898, by rfl⟩ : syracuseStep 974531 = 1461797) B1461797
theorem B5562083 : Blo 912577 5562083 := bstep (se 1 (by rfl) ⟨4171562, by rfl⟩ : syracuseStep 5562083 = 8343125) B8343125
theorem B2318129 : Blo 912577 2318129 := bstep (se 2 (by rfl) ⟨869298, by rfl⟩ : syracuseStep 2318129 = 1738597) B1738597
theorem B2318179 : Blo 912577 2318179 := bstep (se 1 (by rfl) ⟨1738634, by rfl⟩ : syracuseStep 2318179 = 3477269) B3477269
theorem B2056049 : Blo 912577 2056049 := bstep (se 2 (by rfl) ⟨771018, by rfl⟩ : syracuseStep 2056049 = 1542037) B1542037
theorem B2056067 : Blo 912577 2056067 := bstep (se 1 (by rfl) ⟨1542050, by rfl⟩ : syracuseStep 2056067 = 3084101) B3084101
theorem B2318321 : Blo 912577 2318321 := bstep (se 2 (by rfl) ⟨869370, by rfl⟩ : syracuseStep 2318321 = 1738741) B1738741
theorem B1466435 : Blo 912577 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B5202053 : Blo 912577 5202053 := bstep (se 4 (by rfl) ⟨487692, by rfl⟩ : syracuseStep 5202053 = 975385) B975385
theorem B18735245 : Blo 912577 18735245 := bstep (se 3 (by rfl) ⟨3512858, by rfl⟩ : syracuseStep 18735245 = 7025717) B7025717
theorem B2056337 : Blo 912577 2056337 := bstep (se 2 (by rfl) ⟨771126, by rfl⟩ : syracuseStep 2056337 = 1542253) B1542253
theorem B1302689 : Blo 912577 1302689 := bstep (se 2 (by rfl) ⟨488508, by rfl⟩ : syracuseStep 1302689 = 977017) B977017
theorem B2056355 : Blo 912577 2056355 := bstep (se 1 (by rfl) ⟨1542266, by rfl⟩ : syracuseStep 2056355 = 3084533) B3084533
theorem B2253059 : Blo 912577 2253059 := bstep (se 1 (by rfl) ⟨1689794, by rfl⟩ : syracuseStep 2253059 = 3379589) B3379589
theorem B5005745 : Blo 912577 5005745 := bstep (se 2 (by rfl) ⟨1877154, by rfl⟩ : syracuseStep 5005745 = 3754309) B3754309
theorem B2056625 : Blo 912577 2056625 := bstep (se 2 (by rfl) ⟨771234, by rfl⟩ : syracuseStep 2056625 = 1542469) B1542469
theorem B2056643 : Blo 912577 2056643 := bstep (se 1 (by rfl) ⟨1542482, by rfl⟩ : syracuseStep 2056643 = 3084965) B3084965
theorem B6939107 : Blo 912577 6939107 := bstep (se 1 (by rfl) ⟨5204330, by rfl⟩ : syracuseStep 6939107 = 10408661) B10408661
theorem B3301901 : Blo 912577 3301901 := bstep (se 3 (by rfl) ⟨619106, by rfl⟩ : syracuseStep 3301901 = 1238213) B1238213
theorem B1237603 : Blo 912577 1237603 := bstep (se 1 (by rfl) ⟨928202, by rfl⟩ : syracuseStep 1237603 = 1856405) B1856405
theorem B1303219 : Blo 912577 1303219 := bstep (se 1 (by rfl) ⟨977414, by rfl⟩ : syracuseStep 1303219 = 1954829) B1954829
theorem B2056913 : Blo 912577 2056913 := bstep (se 2 (by rfl) ⟨771342, by rfl⟩ : syracuseStep 2056913 = 1542685) B1542685
theorem B2056931 : Blo 912577 2056931 := bstep (se 1 (by rfl) ⟨1542698, by rfl⟩ : syracuseStep 2056931 = 3085397) B3085397
theorem B1368881 : Blo 912577 1368881 := bstep (se 2 (by rfl) ⟨513330, by rfl⟩ : syracuseStep 1368881 = 1026661) B1026661
theorem B5202737 : Blo 912577 5202737 := bstep (se 2 (by rfl) ⟨1951026, by rfl⟩ : syracuseStep 5202737 = 3902053) B3902053
theorem B1368899 : Blo 912577 1368899 := bstep (se 1 (by rfl) ⟨1026674, by rfl⟩ : syracuseStep 1368899 = 2053349) B2053349
theorem B3466061 : Blo 912577 3466061 := bstep (se 3 (by rfl) ⟨649886, by rfl⟩ : syracuseStep 3466061 = 1299773) B1299773
theorem B1368929 : Blo 912577 1368929 := bstep (se 2 (by rfl) ⟨513348, by rfl⟩ : syracuseStep 1368929 = 1026697) B1026697
theorem B1368947 : Blo 912577 1368947 := bstep (se 1 (by rfl) ⟨1026710, by rfl⟩ : syracuseStep 1368947 = 2053421) B2053421
theorem B1368977 : Blo 912577 1368977 := bstep (se 2 (by rfl) ⟨513366, by rfl⟩ : syracuseStep 1368977 = 1026733) B1026733
theorem B1467281 : Blo 912577 1467281 := bstep (se 2 (by rfl) ⟨550230, by rfl⟩ : syracuseStep 1467281 = 1100461) B1100461
theorem B1368995 : Blo 912577 1368995 := bstep (se 1 (by rfl) ⟨1026746, by rfl⟩ : syracuseStep 1368995 = 2053493) B2053493
theorem B1369025 : Blo 912577 1369025 := bstep (se 2 (by rfl) ⟨513384, by rfl⟩ : syracuseStep 1369025 = 1026769) B1026769
theorem B4940741 : Blo 912577 4940741 := bstep (se 4 (by rfl) ⟨463194, by rfl⟩ : syracuseStep 4940741 = 926389) B926389
theorem B2319313 : Blo 912577 2319313 := bstep (se 2 (by rfl) ⟨869742, by rfl⟩ : syracuseStep 2319313 = 1739485) B1739485
theorem B1369043 : Blo 912577 1369043 := bstep (se 1 (by rfl) ⟨1026782, by rfl⟩ : syracuseStep 1369043 = 2053565) B2053565
theorem B1369073 : Blo 912577 1369073 := bstep (se 2 (by rfl) ⟨513402, by rfl⟩ : syracuseStep 1369073 = 1026805) B1026805
theorem B2057201 : Blo 912577 2057201 := bstep (se 2 (by rfl) ⟨771450, by rfl⟩ : syracuseStep 2057201 = 1542901) B1542901
theorem B1369091 : Blo 912577 1369091 := bstep (se 1 (by rfl) ⟨1026818, by rfl⟩ : syracuseStep 1369091 = 2053637) B2053637
theorem B2057219 : Blo 912577 2057219 := bstep (se 1 (by rfl) ⟨1542914, by rfl⟩ : syracuseStep 2057219 = 3085829) B3085829
theorem B1303555 : Blo 912577 1303555 := bstep (se 1 (by rfl) ⟨977666, by rfl⟩ : syracuseStep 1303555 = 1955333) B1955333
theorem B1369121 : Blo 912577 1369121 := bstep (se 2 (by rfl) ⟨513420, by rfl⟩ : syracuseStep 1369121 = 1026841) B1026841
theorem B1369139 : Blo 912577 1369139 := bstep (se 1 (by rfl) ⟨1026854, by rfl⟩ : syracuseStep 1369139 = 2053709) B2053709
theorem B27124789 : Blo 912577 27124789 := bstep (se 5 (by rfl) ⟨1271474, by rfl⟩ : syracuseStep 27124789 = 2542949) B2542949
theorem B1369169 : Blo 912577 1369169 := bstep (se 2 (by rfl) ⟨513438, by rfl⟩ : syracuseStep 1369169 = 1026877) B1026877
theorem B1369187 : Blo 912577 1369187 := bstep (se 1 (by rfl) ⟨1026890, by rfl⟩ : syracuseStep 1369187 = 2053781) B2053781
theorem B1369217 : Blo 912577 1369217 := bstep (se 2 (by rfl) ⟨513456, by rfl⟩ : syracuseStep 1369217 = 1026913) B1026913
theorem B1369235 : Blo 912577 1369235 := bstep (se 1 (by rfl) ⟨1026926, by rfl⟩ : syracuseStep 1369235 = 2053853) B2053853
theorem B1369265 : Blo 912577 1369265 := bstep (se 2 (by rfl) ⟨513474, by rfl⟩ : syracuseStep 1369265 = 1026949) B1026949
theorem B1369283 : Blo 912577 1369283 := bstep (se 1 (by rfl) ⟨1026962, by rfl⟩ : syracuseStep 1369283 = 2053925) B2053925
theorem B1369313 : Blo 912577 1369313 := bstep (se 2 (by rfl) ⟨513492, by rfl⟩ : syracuseStep 1369313 = 1026985) B1026985
theorem B2319587 : Blo 912577 2319587 := bstep (se 1 (by rfl) ⟨1739690, by rfl⟩ : syracuseStep 2319587 = 3479381) B3479381
theorem B1369331 : Blo 912577 1369331 := bstep (se 1 (by rfl) ⟨1026998, by rfl⟩ : syracuseStep 1369331 = 2053997) B2053997
theorem B1369361 : Blo 912577 1369361 := bstep (se 2 (by rfl) ⟨513510, by rfl⟩ : syracuseStep 1369361 = 1027021) B1027021
theorem B2057489 : Blo 912577 2057489 := bstep (se 2 (by rfl) ⟨771558, by rfl⟩ : syracuseStep 2057489 = 1543117) B1543117
theorem B1369379 : Blo 912577 1369379 := bstep (se 1 (by rfl) ⟨1027034, by rfl⟩ : syracuseStep 1369379 = 2054069) B2054069
theorem B2057507 : Blo 912577 2057507 := bstep (se 1 (by rfl) ⟨1543130, by rfl⟩ : syracuseStep 2057507 = 3086261) B3086261
theorem B1369409 : Blo 912577 1369409 := bstep (se 2 (by rfl) ⟨513528, by rfl⟩ : syracuseStep 1369409 = 1027057) B1027057
theorem B1369427 : Blo 912577 1369427 := bstep (se 1 (by rfl) ⟨1027070, by rfl⟩ : syracuseStep 1369427 = 2054141) B2054141
theorem B1369457 : Blo 912577 1369457 := bstep (se 2 (by rfl) ⟨513546, by rfl⟩ : syracuseStep 1369457 = 1027093) B1027093
theorem B1369475 : Blo 912577 1369475 := bstep (se 1 (by rfl) ⟨1027106, by rfl⟩ : syracuseStep 1369475 = 2054213) B2054213
theorem B1369505 : Blo 912577 1369505 := bstep (se 2 (by rfl) ⟨513564, by rfl⟩ : syracuseStep 1369505 = 1027129) B1027129
theorem B2319779 : Blo 912577 2319779 := bstep (se 1 (by rfl) ⟨1739834, by rfl⟩ : syracuseStep 2319779 = 3479669) B3479669
theorem B1369523 : Blo 912577 1369523 := bstep (se 1 (by rfl) ⟨1027142, by rfl⟩ : syracuseStep 1369523 = 2054285) B2054285
theorem B1369553 : Blo 912577 1369553 := bstep (se 2 (by rfl) ⟨513582, by rfl⟩ : syracuseStep 1369553 = 1027165) B1027165
theorem B1369571 : Blo 912577 1369571 := bstep (se 1 (by rfl) ⟨1027178, by rfl⟩ : syracuseStep 1369571 = 2054357) B2054357
theorem B1369601 : Blo 912577 1369601 := bstep (se 2 (by rfl) ⟨513600, by rfl⟩ : syracuseStep 1369601 = 1027201) B1027201
theorem B1369619 : Blo 912577 1369619 := bstep (se 1 (by rfl) ⟨1027214, by rfl⟩ : syracuseStep 1369619 = 2054429) B2054429
theorem B1369649 : Blo 912577 1369649 := bstep (se 2 (by rfl) ⟨513618, by rfl⟩ : syracuseStep 1369649 = 1027237) B1027237
theorem B2057777 : Blo 912577 2057777 := bstep (se 2 (by rfl) ⟨771666, by rfl⟩ : syracuseStep 2057777 = 1543333) B1543333
theorem B1304113 : Blo 912577 1304113 := bstep (se 2 (by rfl) ⟨489042, by rfl⟩ : syracuseStep 1304113 = 978085) B978085
theorem B1369667 : Blo 912577 1369667 := bstep (se 1 (by rfl) ⟨1027250, by rfl⟩ : syracuseStep 1369667 = 2054501) B2054501
theorem B2057795 : Blo 912577 2057795 := bstep (se 1 (by rfl) ⟨1543346, by rfl⟩ : syracuseStep 2057795 = 3086693) B3086693
theorem B1304147 : Blo 912577 1304147 := bstep (se 1 (by rfl) ⟨978110, by rfl⟩ : syracuseStep 1304147 = 1956221) B1956221
theorem B1369697 : Blo 912577 1369697 := bstep (se 2 (by rfl) ⟨513636, by rfl⟩ : syracuseStep 1369697 = 1027273) B1027273
theorem B1369715 : Blo 912577 1369715 := bstep (se 1 (by rfl) ⟨1027286, by rfl⟩ : syracuseStep 1369715 = 2054573) B2054573
theorem B1468019 : Blo 912577 1468019 := bstep (se 1 (by rfl) ⟨1101014, by rfl⟩ : syracuseStep 1468019 = 2202029) B2202029
theorem B1369745 : Blo 912577 1369745 := bstep (se 2 (by rfl) ⟨513654, by rfl⟩ : syracuseStep 1369745 = 1027309) B1027309
theorem B1238689 : Blo 912577 1238689 := bstep (se 2 (by rfl) ⟨464508, by rfl⟩ : syracuseStep 1238689 = 929017) B929017
theorem B1369763 : Blo 912577 1369763 := bstep (se 1 (by rfl) ⟨1027322, by rfl⟩ : syracuseStep 1369763 = 2054645) B2054645
theorem B976547 : Blo 912577 976547 := bstep (se 1 (by rfl) ⟨732410, by rfl⟩ : syracuseStep 976547 = 1464821) B1464821
theorem B1369793 : Blo 912577 1369793 := bstep (se 2 (by rfl) ⟨513672, by rfl⟩ : syracuseStep 1369793 = 1027345) B1027345
theorem B1369811 : Blo 912577 1369811 := bstep (se 1 (by rfl) ⟨1027358, by rfl⟩ : syracuseStep 1369811 = 2054717) B2054717
theorem B1369841 : Blo 912577 1369841 := bstep (se 2 (by rfl) ⟨513690, by rfl⟩ : syracuseStep 1369841 = 1027381) B1027381
theorem B1369859 : Blo 912577 1369859 := bstep (se 1 (by rfl) ⟨1027394, by rfl⟩ : syracuseStep 1369859 = 2054789) B2054789
theorem B1369889 : Blo 912577 1369889 := bstep (se 2 (by rfl) ⟨513708, by rfl⟩ : syracuseStep 1369889 = 1027417) B1027417
theorem B1369907 : Blo 912577 1369907 := bstep (se 1 (by rfl) ⟨1027430, by rfl⟩ : syracuseStep 1369907 = 2054861) B2054861
theorem B1369937 : Blo 912577 1369937 := bstep (se 2 (by rfl) ⟨513726, by rfl⟩ : syracuseStep 1369937 = 1027453) B1027453
theorem B2058065 : Blo 912577 2058065 := bstep (se 2 (by rfl) ⟨771774, by rfl⟩ : syracuseStep 2058065 = 1543549) B1543549
theorem B1369955 : Blo 912577 1369955 := bstep (se 1 (by rfl) ⟨1027466, by rfl⟩ : syracuseStep 1369955 = 2054933) B2054933
theorem B2058083 : Blo 912577 2058083 := bstep (se 1 (by rfl) ⟨1543562, by rfl⟩ : syracuseStep 2058083 = 3087125) B3087125
theorem B1369985 : Blo 912577 1369985 := bstep (se 2 (by rfl) ⟨513744, by rfl⟩ : syracuseStep 1369985 = 1027489) B1027489
theorem B1370003 : Blo 912577 1370003 := bstep (se 1 (by rfl) ⟨1027502, by rfl⟩ : syracuseStep 1370003 = 2055005) B2055005
theorem B1370033 : Blo 912577 1370033 := bstep (se 2 (by rfl) ⟨513762, by rfl⟩ : syracuseStep 1370033 = 1027525) B1027525
theorem B1370051 : Blo 912577 1370051 := bstep (se 1 (by rfl) ⟨1027538, by rfl⟩ : syracuseStep 1370051 = 2055077) B2055077
theorem B1370081 : Blo 912577 1370081 := bstep (se 2 (by rfl) ⟨513780, by rfl⟩ : syracuseStep 1370081 = 1027561) B1027561
theorem B1370099 : Blo 912577 1370099 := bstep (se 1 (by rfl) ⟨1027574, by rfl⟩ : syracuseStep 1370099 = 2055149) B2055149
theorem B1370129 : Blo 912577 1370129 := bstep (se 2 (by rfl) ⟨513798, by rfl⟩ : syracuseStep 1370129 = 1027597) B1027597
theorem B1370147 : Blo 912577 1370147 := bstep (se 1 (by rfl) ⟨1027610, by rfl⟩ : syracuseStep 1370147 = 2055221) B2055221
theorem B1370177 : Blo 912577 1370177 := bstep (se 2 (by rfl) ⟨513816, by rfl⟩ : syracuseStep 1370177 = 1027633) B1027633
theorem B1566785 : Blo 912577 1566785 := bstep (se 2 (by rfl) ⟨587544, by rfl⟩ : syracuseStep 1566785 = 1175089) B1175089
theorem B1370195 : Blo 912577 1370195 := bstep (se 1 (by rfl) ⟨1027646, by rfl⟩ : syracuseStep 1370195 = 2055293) B2055293
theorem B1370225 : Blo 912577 1370225 := bstep (se 2 (by rfl) ⟨513834, by rfl⟩ : syracuseStep 1370225 = 1027669) B1027669
theorem B2058353 : Blo 912577 2058353 := bstep (se 2 (by rfl) ⟨771882, by rfl⟩ : syracuseStep 2058353 = 1543765) B1543765
theorem B1304705 : Blo 912577 1304705 := bstep (se 2 (by rfl) ⟨489264, by rfl⟩ : syracuseStep 1304705 = 978529) B978529
theorem B1370243 : Blo 912577 1370243 := bstep (se 1 (by rfl) ⟨1027682, by rfl⟩ : syracuseStep 1370243 = 2055365) B2055365
theorem B2779267 : Blo 912577 2779267 := bstep (se 1 (by rfl) ⟨2084450, by rfl⟩ : syracuseStep 2779267 = 4168901) B4168901
theorem B2058371 : Blo 912577 2058371 := bstep (se 1 (by rfl) ⟨1543778, by rfl⟩ : syracuseStep 2058371 = 3087557) B3087557
theorem B1370273 : Blo 912577 1370273 := bstep (se 2 (by rfl) ⟨513852, by rfl⟩ : syracuseStep 1370273 = 1027705) B1027705
theorem B1370291 : Blo 912577 1370291 := bstep (se 1 (by rfl) ⟨1027718, by rfl⟩ : syracuseStep 1370291 = 2055437) B2055437
theorem B1370321 : Blo 912577 1370321 := bstep (se 2 (by rfl) ⟨513870, by rfl⟩ : syracuseStep 1370321 = 1027741) B1027741
theorem B1304785 : Blo 912577 1304785 := bstep (se 2 (by rfl) ⟨489294, by rfl⟩ : syracuseStep 1304785 = 978589) B978589
theorem B1370339 : Blo 912577 1370339 := bstep (se 1 (by rfl) ⟨1027754, by rfl⟩ : syracuseStep 1370339 = 2055509) B2055509
theorem B5204195 : Blo 912577 5204195 := bstep (se 1 (by rfl) ⟨3903146, by rfl⟩ : syracuseStep 5204195 = 7806293) B7806293
theorem B1370369 : Blo 912577 1370369 := bstep (se 2 (by rfl) ⟨513888, by rfl⟩ : syracuseStep 1370369 = 1027777) B1027777
theorem B1566977 : Blo 912577 1566977 := bstep (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) B1175233
theorem B1370387 : Blo 912577 1370387 := bstep (se 1 (by rfl) ⟨1027790, by rfl⟩ : syracuseStep 1370387 = 2055581) B2055581
theorem B1370417 : Blo 912577 1370417 := bstep (se 2 (by rfl) ⟨513906, by rfl⟩ : syracuseStep 1370417 = 1027813) B1027813
theorem B1370435 : Blo 912577 1370435 := bstep (se 1 (by rfl) ⟨1027826, by rfl⟩ : syracuseStep 1370435 = 2055653) B2055653
theorem B1370465 : Blo 912577 1370465 := bstep (se 2 (by rfl) ⟨513924, by rfl⟩ : syracuseStep 1370465 = 1027849) B1027849
theorem B2091377 : Blo 912577 2091377 := bstep (se 2 (by rfl) ⟨784266, by rfl⟩ : syracuseStep 2091377 = 1568533) B1568533
theorem B1370483 : Blo 912577 1370483 := bstep (se 1 (by rfl) ⟨1027862, by rfl⟩ : syracuseStep 1370483 = 2055725) B2055725
theorem B1370513 : Blo 912577 1370513 := bstep (se 2 (by rfl) ⟨513942, by rfl⟩ : syracuseStep 1370513 = 1027885) B1027885
theorem B2058641 : Blo 912577 2058641 := bstep (se 2 (by rfl) ⟨771990, by rfl⟩ : syracuseStep 2058641 = 1543981) B1543981
theorem B1370531 : Blo 912577 1370531 := bstep (se 1 (by rfl) ⟨1027898, by rfl⟩ : syracuseStep 1370531 = 2055797) B2055797
theorem B2058659 : Blo 912577 2058659 := bstep (se 1 (by rfl) ⟨1543994, by rfl⟩ : syracuseStep 2058659 = 3087989) B3087989
theorem B1370561 : Blo 912577 1370561 := bstep (se 2 (by rfl) ⟨513960, by rfl⟩ : syracuseStep 1370561 = 1027921) B1027921
theorem B1370579 : Blo 912577 1370579 := bstep (se 1 (by rfl) ⟨1027934, by rfl⟩ : syracuseStep 1370579 = 2055869) B2055869
theorem B1370609 : Blo 912577 1370609 := bstep (se 2 (by rfl) ⟨513978, by rfl⟩ : syracuseStep 1370609 = 1027957) B1027957
theorem B1370627 : Blo 912577 1370627 := bstep (se 1 (by rfl) ⟨1027970, by rfl⟩ : syracuseStep 1370627 = 2055941) B2055941
theorem B1370657 : Blo 912577 1370657 := bstep (se 2 (by rfl) ⟨513996, by rfl⟩ : syracuseStep 1370657 = 1027993) B1027993
theorem B1370675 : Blo 912577 1370675 := bstep (se 1 (by rfl) ⟨1028006, by rfl⟩ : syracuseStep 1370675 = 2056013) B2056013
theorem B1370705 : Blo 912577 1370705 := bstep (se 2 (by rfl) ⟨514014, by rfl⟩ : syracuseStep 1370705 = 1028029) B1028029
theorem B1370723 : Blo 912577 1370723 := bstep (se 1 (by rfl) ⟨1028042, by rfl⟩ : syracuseStep 1370723 = 2056085) B2056085
theorem B1370753 : Blo 912577 1370753 := bstep (se 2 (by rfl) ⟨514032, by rfl⟩ : syracuseStep 1370753 = 1028065) B1028065
theorem B1370771 : Blo 912577 1370771 := bstep (se 1 (by rfl) ⟨1028078, by rfl⟩ : syracuseStep 1370771 = 2056157) B2056157
theorem B977555 : Blo 912577 977555 := bstep (se 1 (by rfl) ⟨733166, by rfl⟩ : syracuseStep 977555 = 1466333) B1466333
theorem B1370801 : Blo 912577 1370801 := bstep (se 2 (by rfl) ⟨514050, by rfl⟩ : syracuseStep 1370801 = 1028101) B1028101
theorem B2058929 : Blo 912577 2058929 := bstep (se 2 (by rfl) ⟨772098, by rfl⟩ : syracuseStep 2058929 = 1544197) B1544197
theorem B1370819 : Blo 912577 1370819 := bstep (se 1 (by rfl) ⟨1028114, by rfl⟩ : syracuseStep 1370819 = 2056229) B2056229
theorem B2058947 : Blo 912577 2058947 := bstep (se 1 (by rfl) ⟨1544210, by rfl⟩ : syracuseStep 2058947 = 3088421) B3088421
theorem B1370849 : Blo 912577 1370849 := bstep (se 2 (by rfl) ⟨514068, by rfl⟩ : syracuseStep 1370849 = 1028137) B1028137
theorem B1370867 : Blo 912577 1370867 := bstep (se 1 (by rfl) ⟨1028150, by rfl⟩ : syracuseStep 1370867 = 2056301) B2056301
theorem B1370897 : Blo 912577 1370897 := bstep (se 2 (by rfl) ⟨514086, by rfl⟩ : syracuseStep 1370897 = 1028173) B1028173
theorem B1370915 : Blo 912577 1370915 := bstep (se 1 (by rfl) ⟨1028186, by rfl⟩ : syracuseStep 1370915 = 2056373) B2056373
theorem B1370945 : Blo 912577 1370945 := bstep (se 2 (by rfl) ⟨514104, by rfl⟩ : syracuseStep 1370945 = 1028209) B1028209
theorem B1370963 : Blo 912577 1370963 := bstep (se 1 (by rfl) ⟨1028222, by rfl⟩ : syracuseStep 1370963 = 2056445) B2056445
theorem B1370993 : Blo 912577 1370993 := bstep (se 2 (by rfl) ⟨514122, by rfl⟩ : syracuseStep 1370993 = 1028245) B1028245
theorem B1371011 : Blo 912577 1371011 := bstep (se 1 (by rfl) ⟨1028258, by rfl⟩ : syracuseStep 1371011 = 2056517) B2056517
theorem B1371041 : Blo 912577 1371041 := bstep (se 2 (by rfl) ⟨514140, by rfl⟩ : syracuseStep 1371041 = 1028281) B1028281
theorem B1371059 : Blo 912577 1371059 := bstep (se 1 (by rfl) ⟨1028294, by rfl⟩ : syracuseStep 1371059 = 2056589) B2056589
theorem B1371089 : Blo 912577 1371089 := bstep (se 2 (by rfl) ⟨514158, by rfl⟩ : syracuseStep 1371089 = 1028317) B1028317
theorem B2059217 : Blo 912577 2059217 := bstep (se 2 (by rfl) ⟨772206, by rfl⟩ : syracuseStep 2059217 = 1544413) B1544413
theorem B1371107 : Blo 912577 1371107 := bstep (se 1 (by rfl) ⟨1028330, by rfl⟩ : syracuseStep 1371107 = 2056661) B2056661
theorem B2059235 : Blo 912577 2059235 := bstep (se 1 (by rfl) ⟨1544426, by rfl⟩ : syracuseStep 2059235 = 3088853) B3088853
theorem B1371137 : Blo 912577 1371137 := bstep (se 2 (by rfl) ⟨514176, by rfl⟩ : syracuseStep 1371137 = 1028353) B1028353
theorem B1371155 : Blo 912577 1371155 := bstep (se 1 (by rfl) ⟨1028366, by rfl⟩ : syracuseStep 1371155 = 2056733) B2056733
theorem B1371185 : Blo 912577 1371185 := bstep (se 2 (by rfl) ⟨514194, by rfl⟩ : syracuseStep 1371185 = 1028389) B1028389
theorem B1371203 : Blo 912577 1371203 := bstep (se 1 (by rfl) ⟨1028402, by rfl⟩ : syracuseStep 1371203 = 2056805) B2056805
theorem B1371233 : Blo 912577 1371233 := bstep (se 2 (by rfl) ⟨514212, by rfl⟩ : syracuseStep 1371233 = 1028425) B1028425
theorem B1371251 : Blo 912577 1371251 := bstep (se 1 (by rfl) ⟨1028438, by rfl⟩ : syracuseStep 1371251 = 2056877) B2056877
theorem B1371281 : Blo 912577 1371281 := bstep (se 2 (by rfl) ⟨514230, by rfl⟩ : syracuseStep 1371281 = 1028461) B1028461
theorem B1371299 : Blo 912577 1371299 := bstep (se 1 (by rfl) ⟨1028474, by rfl⟩ : syracuseStep 1371299 = 2056949) B2056949
theorem B1371329 : Blo 912577 1371329 := bstep (se 2 (by rfl) ⟨514248, by rfl⟩ : syracuseStep 1371329 = 1028497) B1028497
theorem B912579 : Blo 912577 912579 := bstep (se 1 (by rfl) ⟨684434, by rfl⟩ : syracuseStep 912579 = 1368869) B1368869
theorem B912595 : Blo 912577 912595 := bstep (se 1 (by rfl) ⟨684446, by rfl⟩ : syracuseStep 912595 = 1368893) B1368893
theorem B1371347 : Blo 912577 1371347 := bstep (se 1 (by rfl) ⟨1028510, by rfl⟩ : syracuseStep 1371347 = 2057021) B2057021
theorem B912611 : Blo 912577 912611 := bstep (se 1 (by rfl) ⟨684458, by rfl⟩ : syracuseStep 912611 = 1368917) B1368917
theorem B1371377 : Blo 912577 1371377 := bstep (se 2 (by rfl) ⟨514266, by rfl⟩ : syracuseStep 1371377 = 1028533) B1028533
theorem B2059505 : Blo 912577 2059505 := bstep (se 2 (by rfl) ⟨772314, by rfl⟩ : syracuseStep 2059505 = 1544629) B1544629
theorem B912627 : Blo 912577 912627 := bstep (se 1 (by rfl) ⟨684470, by rfl⟩ : syracuseStep 912627 = 1368941) B1368941
theorem B912643 : Blo 912577 912643 := bstep (se 1 (by rfl) ⟨684482, by rfl⟩ : syracuseStep 912643 = 1368965) B1368965
theorem B1371395 : Blo 912577 1371395 := bstep (se 1 (by rfl) ⟨1028546, by rfl⟩ : syracuseStep 1371395 = 2057093) B2057093
theorem B5860613 : Blo 912577 5860613 := bstep (se 4 (by rfl) ⟨549432, by rfl⟩ : syracuseStep 5860613 = 1098865) B1098865
theorem B2059523 : Blo 912577 2059523 := bstep (se 1 (by rfl) ⟨1544642, by rfl⟩ : syracuseStep 2059523 = 3089285) B3089285
theorem B912659 : Blo 912577 912659 := bstep (se 1 (by rfl) ⟨684494, by rfl⟩ : syracuseStep 912659 = 1368989) B1368989
theorem B1371425 : Blo 912577 1371425 := bstep (se 2 (by rfl) ⟨514284, by rfl⟩ : syracuseStep 1371425 = 1028569) B1028569
theorem B912675 : Blo 912577 912675 := bstep (se 1 (by rfl) ⟨684506, by rfl⟩ : syracuseStep 912675 = 1369013) B1369013
theorem B912691 : Blo 912577 912691 := bstep (se 1 (by rfl) ⟨684518, by rfl⟩ : syracuseStep 912691 = 1369037) B1369037
theorem B1371443 : Blo 912577 1371443 := bstep (se 1 (by rfl) ⟨1028582, by rfl⟩ : syracuseStep 1371443 = 2057165) B2057165
theorem B912707 : Blo 912577 912707 := bstep (se 1 (by rfl) ⟨684530, by rfl⟩ : syracuseStep 912707 = 1369061) B1369061
theorem B3009869 : Blo 912577 3009869 := bstep (se 3 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 3009869 = 1128701) B1128701
theorem B1371473 : Blo 912577 1371473 := bstep (se 2 (by rfl) ⟨514302, by rfl⟩ : syracuseStep 1371473 = 1028605) B1028605
theorem B912723 : Blo 912577 912723 := bstep (se 1 (by rfl) ⟨684542, by rfl⟩ : syracuseStep 912723 = 1369085) B1369085
theorem B912739 : Blo 912577 912739 := bstep (se 1 (by rfl) ⟨684554, by rfl⟩ : syracuseStep 912739 = 1369109) B1369109
theorem B1371491 : Blo 912577 1371491 := bstep (se 1 (by rfl) ⟨1028618, by rfl⟩ : syracuseStep 1371491 = 2057237) B2057237
theorem B912755 : Blo 912577 912755 := bstep (se 1 (by rfl) ⟨684566, by rfl⟩ : syracuseStep 912755 = 1369133) B1369133
theorem B1371521 : Blo 912577 1371521 := bstep (se 2 (by rfl) ⟨514320, by rfl⟩ : syracuseStep 1371521 = 1028641) B1028641
theorem B912771 : Blo 912577 912771 := bstep (se 1 (by rfl) ⟨684578, by rfl⟩ : syracuseStep 912771 = 1369157) B1369157
theorem B912787 : Blo 912577 912787 := bstep (se 1 (by rfl) ⟨684590, by rfl⟩ : syracuseStep 912787 = 1369181) B1369181
theorem B1371539 : Blo 912577 1371539 := bstep (se 1 (by rfl) ⟨1028654, by rfl⟩ : syracuseStep 1371539 = 2057309) B2057309
theorem B912803 : Blo 912577 912803 := bstep (se 1 (by rfl) ⟨684602, by rfl⟩ : syracuseStep 912803 = 1369205) B1369205
theorem B1371569 : Blo 912577 1371569 := bstep (se 2 (by rfl) ⟨514338, by rfl⟩ : syracuseStep 1371569 = 1028677) B1028677
theorem B912819 : Blo 912577 912819 := bstep (se 1 (by rfl) ⟨684614, by rfl⟩ : syracuseStep 912819 = 1369229) B1369229
theorem B912835 : Blo 912577 912835 := bstep (se 1 (by rfl) ⟨684626, by rfl⟩ : syracuseStep 912835 = 1369253) B1369253
theorem B1371587 : Blo 912577 1371587 := bstep (se 1 (by rfl) ⟨1028690, by rfl⟩ : syracuseStep 1371587 = 2057381) B2057381
theorem B912851 : Blo 912577 912851 := bstep (se 1 (by rfl) ⟨684638, by rfl⟩ : syracuseStep 912851 = 1369277) B1369277
theorem B1371617 : Blo 912577 1371617 := bstep (se 2 (by rfl) ⟨514356, by rfl⟩ : syracuseStep 1371617 = 1028713) B1028713
theorem B912867 : Blo 912577 912867 := bstep (se 1 (by rfl) ⟨684650, by rfl⟩ : syracuseStep 912867 = 1369301) B1369301
theorem B912883 : Blo 912577 912883 := bstep (se 1 (by rfl) ⟨684662, by rfl⟩ : syracuseStep 912883 = 1369325) B1369325
theorem B1371635 : Blo 912577 1371635 := bstep (se 1 (by rfl) ⟨1028726, by rfl⟩ : syracuseStep 1371635 = 2057453) B2057453
theorem B912899 : Blo 912577 912899 := bstep (se 1 (by rfl) ⟨684674, by rfl⟩ : syracuseStep 912899 = 1369349) B1369349
theorem B1371665 : Blo 912577 1371665 := bstep (se 2 (by rfl) ⟨514374, by rfl⟩ : syracuseStep 1371665 = 1028749) B1028749
theorem B2059793 : Blo 912577 2059793 := bstep (se 2 (by rfl) ⟨772422, by rfl⟩ : syracuseStep 2059793 = 1544845) B1544845
theorem B912915 : Blo 912577 912915 := bstep (se 1 (by rfl) ⟨684686, by rfl⟩ : syracuseStep 912915 = 1369373) B1369373
theorem B912931 : Blo 912577 912931 := bstep (se 1 (by rfl) ⟨684698, by rfl⟩ : syracuseStep 912931 = 1369397) B1369397
theorem B1371683 : Blo 912577 1371683 := bstep (se 1 (by rfl) ⟨1028762, by rfl⟩ : syracuseStep 1371683 = 2057525) B2057525
theorem B2059811 : Blo 912577 2059811 := bstep (se 1 (by rfl) ⟨1544858, by rfl⟩ : syracuseStep 2059811 = 3089717) B3089717
theorem B912947 : Blo 912577 912947 := bstep (se 1 (by rfl) ⟨684710, by rfl⟩ : syracuseStep 912947 = 1369421) B1369421
theorem B1371713 : Blo 912577 1371713 := bstep (se 2 (by rfl) ⟨514392, by rfl⟩ : syracuseStep 1371713 = 1028785) B1028785
theorem B912963 : Blo 912577 912963 := bstep (se 1 (by rfl) ⟨684722, by rfl⟩ : syracuseStep 912963 = 1369445) B1369445
theorem B912979 : Blo 912577 912979 := bstep (se 1 (by rfl) ⟨684734, by rfl⟩ : syracuseStep 912979 = 1369469) B1369469
theorem B1371731 : Blo 912577 1371731 := bstep (se 1 (by rfl) ⟨1028798, by rfl⟩ : syracuseStep 1371731 = 2057597) B2057597
theorem B912995 : Blo 912577 912995 := bstep (se 1 (by rfl) ⟨684746, by rfl⟩ : syracuseStep 912995 = 1369493) B1369493
theorem B1371761 : Blo 912577 1371761 := bstep (se 2 (by rfl) ⟨514410, by rfl⟩ : syracuseStep 1371761 = 1028821) B1028821
theorem B913011 : Blo 912577 913011 := bstep (se 1 (by rfl) ⟨684758, by rfl⟩ : syracuseStep 913011 = 1369517) B1369517
theorem B913027 : Blo 912577 913027 := bstep (se 1 (by rfl) ⟨684770, by rfl⟩ : syracuseStep 913027 = 1369541) B1369541
theorem B1371779 : Blo 912577 1371779 := bstep (se 1 (by rfl) ⟨1028834, by rfl⟩ : syracuseStep 1371779 = 2057669) B2057669
theorem B913043 : Blo 912577 913043 := bstep (se 1 (by rfl) ⟨684782, by rfl⟩ : syracuseStep 913043 = 1369565) B1369565
theorem B1371809 : Blo 912577 1371809 := bstep (se 2 (by rfl) ⟨514428, by rfl⟩ : syracuseStep 1371809 = 1028857) B1028857
theorem B913059 : Blo 912577 913059 := bstep (se 1 (by rfl) ⟨684794, by rfl⟩ : syracuseStep 913059 = 1369589) B1369589
theorem B3468977 : Blo 912577 3468977 := bstep (se 2 (by rfl) ⟨1300866, by rfl⟩ : syracuseStep 3468977 = 2601733) B2601733
theorem B913075 : Blo 912577 913075 := bstep (se 1 (by rfl) ⟨684806, by rfl⟩ : syracuseStep 913075 = 1369613) B1369613
theorem B1371827 : Blo 912577 1371827 := bstep (se 1 (by rfl) ⟨1028870, by rfl⟩ : syracuseStep 1371827 = 2057741) B2057741
theorem B913091 : Blo 912577 913091 := bstep (se 1 (by rfl) ⟨684818, by rfl⟩ : syracuseStep 913091 = 1369637) B1369637
theorem B1371857 : Blo 912577 1371857 := bstep (se 2 (by rfl) ⟨514446, by rfl⟩ : syracuseStep 1371857 = 1028893) B1028893
theorem B913107 : Blo 912577 913107 := bstep (se 1 (by rfl) ⟨684830, by rfl⟩ : syracuseStep 913107 = 1369661) B1369661
theorem B913123 : Blo 912577 913123 := bstep (se 1 (by rfl) ⟨684842, by rfl⟩ : syracuseStep 913123 = 1369685) B1369685
theorem B1371875 : Blo 912577 1371875 := bstep (se 1 (by rfl) ⟨1028906, by rfl⟩ : syracuseStep 1371875 = 2057813) B2057813
theorem B913139 : Blo 912577 913139 := bstep (se 1 (by rfl) ⟨684854, by rfl⟩ : syracuseStep 913139 = 1369709) B1369709
theorem B1371905 : Blo 912577 1371905 := bstep (se 2 (by rfl) ⟨514464, by rfl⟩ : syracuseStep 1371905 = 1028929) B1028929
theorem B913155 : Blo 912577 913155 := bstep (se 1 (by rfl) ⟨684866, by rfl⟩ : syracuseStep 913155 = 1369733) B1369733
theorem B913171 : Blo 912577 913171 := bstep (se 1 (by rfl) ⟨684878, by rfl⟩ : syracuseStep 913171 = 1369757) B1369757
theorem B1371923 : Blo 912577 1371923 := bstep (se 1 (by rfl) ⟨1028942, by rfl⟩ : syracuseStep 1371923 = 2057885) B2057885
theorem B913187 : Blo 912577 913187 := bstep (se 1 (by rfl) ⟨684890, by rfl⟩ : syracuseStep 913187 = 1369781) B1369781
theorem B1371953 : Blo 912577 1371953 := bstep (se 2 (by rfl) ⟨514482, by rfl⟩ : syracuseStep 1371953 = 1028965) B1028965
theorem B2060081 : Blo 912577 2060081 := bstep (se 2 (by rfl) ⟨772530, by rfl⟩ : syracuseStep 2060081 = 1545061) B1545061
theorem B913203 : Blo 912577 913203 := bstep (se 1 (by rfl) ⟨684902, by rfl⟩ : syracuseStep 913203 = 1369805) B1369805
theorem B2060099 : Blo 912577 2060099 := bstep (se 1 (by rfl) ⟨1545074, by rfl⟩ : syracuseStep 2060099 = 3090149) B3090149
theorem B913219 : Blo 912577 913219 := bstep (se 1 (by rfl) ⟨684914, by rfl⟩ : syracuseStep 913219 = 1369829) B1369829
theorem B1371971 : Blo 912577 1371971 := bstep (se 1 (by rfl) ⟨1028978, by rfl⟩ : syracuseStep 1371971 = 2057957) B2057957
theorem B913235 : Blo 912577 913235 := bstep (se 1 (by rfl) ⟨684926, by rfl⟩ : syracuseStep 913235 = 1369853) B1369853
theorem B1372001 : Blo 912577 1372001 := bstep (se 2 (by rfl) ⟨514500, by rfl⟩ : syracuseStep 1372001 = 1029001) B1029001
theorem B913251 : Blo 912577 913251 := bstep (se 1 (by rfl) ⟨684938, by rfl⟩ : syracuseStep 913251 = 1369877) B1369877
theorem B913267 : Blo 912577 913267 := bstep (se 1 (by rfl) ⟨684950, by rfl⟩ : syracuseStep 913267 = 1369901) B1369901
theorem B1372019 : Blo 912577 1372019 := bstep (se 1 (by rfl) ⟨1029014, by rfl⟩ : syracuseStep 1372019 = 2058029) B2058029
theorem B913283 : Blo 912577 913283 := bstep (se 1 (by rfl) ⟨684962, by rfl⟩ : syracuseStep 913283 = 1369925) B1369925
theorem B1372049 : Blo 912577 1372049 := bstep (se 2 (by rfl) ⟨514518, by rfl⟩ : syracuseStep 1372049 = 1029037) B1029037
theorem B913299 : Blo 912577 913299 := bstep (se 1 (by rfl) ⟨684974, by rfl⟩ : syracuseStep 913299 = 1369949) B1369949
theorem B913315 : Blo 912577 913315 := bstep (se 1 (by rfl) ⟨684986, by rfl⟩ : syracuseStep 913315 = 1369973) B1369973
theorem B1372067 : Blo 912577 1372067 := bstep (se 1 (by rfl) ⟨1029050, by rfl⟩ : syracuseStep 1372067 = 2058101) B2058101
theorem B1732529 : Blo 912577 1732529 := bstep (se 2 (by rfl) ⟨649698, by rfl⟩ : syracuseStep 1732529 = 1299397) B1299397
theorem B913331 : Blo 912577 913331 := bstep (se 1 (by rfl) ⟨684998, by rfl⟩ : syracuseStep 913331 = 1369997) B1369997
theorem B1372097 : Blo 912577 1372097 := bstep (se 2 (by rfl) ⟨514536, by rfl⟩ : syracuseStep 1372097 = 1029073) B1029073
theorem B913347 : Blo 912577 913347 := bstep (se 1 (by rfl) ⟨685010, by rfl⟩ : syracuseStep 913347 = 1370021) B1370021
theorem B3010499 : Blo 912577 3010499 := bstep (se 1 (by rfl) ⟨2257874, by rfl⟩ : syracuseStep 3010499 = 4515749) B4515749
theorem B913363 : Blo 912577 913363 := bstep (se 1 (by rfl) ⟨685022, by rfl⟩ : syracuseStep 913363 = 1370045) B1370045
theorem B1372115 : Blo 912577 1372115 := bstep (se 1 (by rfl) ⟨1029086, by rfl⟩ : syracuseStep 1372115 = 2058173) B2058173
theorem B913379 : Blo 912577 913379 := bstep (se 1 (by rfl) ⟨685034, by rfl⟩ : syracuseStep 913379 = 1370069) B1370069
theorem B1372145 : Blo 912577 1372145 := bstep (se 2 (by rfl) ⟨514554, by rfl⟩ : syracuseStep 1372145 = 1029109) B1029109
theorem B913395 : Blo 912577 913395 := bstep (se 1 (by rfl) ⟨685046, by rfl⟩ : syracuseStep 913395 = 1370093) B1370093
theorem B913411 : Blo 912577 913411 := bstep (se 1 (by rfl) ⟨685058, by rfl⟩ : syracuseStep 913411 = 1370117) B1370117
theorem B1372163 : Blo 912577 1372163 := bstep (se 1 (by rfl) ⟨1029122, by rfl⟩ : syracuseStep 1372163 = 2058245) B2058245
theorem B913427 : Blo 912577 913427 := bstep (se 1 (by rfl) ⟨685070, by rfl⟩ : syracuseStep 913427 = 1370141) B1370141
theorem B1372193 : Blo 912577 1372193 := bstep (se 2 (by rfl) ⟨514572, by rfl⟩ : syracuseStep 1372193 = 1029145) B1029145
theorem B913443 : Blo 912577 913443 := bstep (se 1 (by rfl) ⟨685082, by rfl⟩ : syracuseStep 913443 = 1370165) B1370165
theorem B913459 : Blo 912577 913459 := bstep (se 1 (by rfl) ⟨685094, by rfl⟩ : syracuseStep 913459 = 1370189) B1370189
theorem B1372211 : Blo 912577 1372211 := bstep (se 1 (by rfl) ⟨1029158, by rfl⟩ : syracuseStep 1372211 = 2058317) B2058317
theorem B913475 : Blo 912577 913475 := bstep (se 1 (by rfl) ⟨685106, by rfl⟩ : syracuseStep 913475 = 1370213) B1370213
theorem B1372241 : Blo 912577 1372241 := bstep (se 2 (by rfl) ⟨514590, by rfl⟩ : syracuseStep 1372241 = 1029181) B1029181
theorem B2060369 : Blo 912577 2060369 := bstep (se 2 (by rfl) ⟨772638, by rfl⟩ : syracuseStep 2060369 = 1545277) B1545277
theorem B913491 : Blo 912577 913491 := bstep (se 1 (by rfl) ⟨685118, by rfl⟩ : syracuseStep 913491 = 1370237) B1370237
theorem B913507 : Blo 912577 913507 := bstep (se 1 (by rfl) ⟨685130, by rfl⟩ : syracuseStep 913507 = 1370261) B1370261
theorem B1372259 : Blo 912577 1372259 := bstep (se 1 (by rfl) ⟨1029194, by rfl⟩ : syracuseStep 1372259 = 2058389) B2058389
theorem B2060387 : Blo 912577 2060387 := bstep (se 1 (by rfl) ⟨1545290, by rfl⟩ : syracuseStep 2060387 = 3090581) B3090581
theorem B913523 : Blo 912577 913523 := bstep (se 1 (by rfl) ⟨685142, by rfl⟩ : syracuseStep 913523 = 1370285) B1370285
theorem B1372289 : Blo 912577 1372289 := bstep (se 2 (by rfl) ⟨514608, by rfl⟩ : syracuseStep 1372289 = 1029217) B1029217
theorem B913539 : Blo 912577 913539 := bstep (se 1 (by rfl) ⟨685154, by rfl⟩ : syracuseStep 913539 = 1370309) B1370309
theorem B913555 : Blo 912577 913555 := bstep (se 1 (by rfl) ⟨685166, by rfl⟩ : syracuseStep 913555 = 1370333) B1370333
theorem B1372307 : Blo 912577 1372307 := bstep (se 1 (by rfl) ⟨1029230, by rfl⟩ : syracuseStep 1372307 = 2058461) B2058461
theorem B913571 : Blo 912577 913571 := bstep (se 1 (by rfl) ⟨685178, by rfl⟩ : syracuseStep 913571 = 1370357) B1370357
theorem B1372337 : Blo 912577 1372337 := bstep (se 2 (by rfl) ⟨514626, by rfl⟩ : syracuseStep 1372337 = 1029253) B1029253
theorem B913587 : Blo 912577 913587 := bstep (se 1 (by rfl) ⟨685190, by rfl⟩ : syracuseStep 913587 = 1370381) B1370381
theorem B913603 : Blo 912577 913603 := bstep (se 1 (by rfl) ⟨685202, by rfl⟩ : syracuseStep 913603 = 1370405) B1370405
theorem B1372355 : Blo 912577 1372355 := bstep (se 1 (by rfl) ⟨1029266, by rfl⟩ : syracuseStep 1372355 = 2058533) B2058533
theorem B913619 : Blo 912577 913619 := bstep (se 1 (by rfl) ⟨685214, by rfl⟩ : syracuseStep 913619 = 1370429) B1370429
theorem B1372385 : Blo 912577 1372385 := bstep (se 2 (by rfl) ⟨514644, by rfl⟩ : syracuseStep 1372385 = 1029289) B1029289
theorem B913635 : Blo 912577 913635 := bstep (se 1 (by rfl) ⟨685226, by rfl⟩ : syracuseStep 913635 = 1370453) B1370453
theorem B913651 : Blo 912577 913651 := bstep (se 1 (by rfl) ⟨685238, by rfl⟩ : syracuseStep 913651 = 1370477) B1370477
theorem B1372403 : Blo 912577 1372403 := bstep (se 1 (by rfl) ⟨1029302, by rfl⟩ : syracuseStep 1372403 = 2058605) B2058605
theorem B913667 : Blo 912577 913667 := bstep (se 1 (by rfl) ⟨685250, by rfl⟩ : syracuseStep 913667 = 1370501) B1370501
theorem B1372433 : Blo 912577 1372433 := bstep (se 2 (by rfl) ⟨514662, by rfl⟩ : syracuseStep 1372433 = 1029325) B1029325
theorem B913683 : Blo 912577 913683 := bstep (se 1 (by rfl) ⟨685262, by rfl⟩ : syracuseStep 913683 = 1370525) B1370525
theorem B913699 : Blo 912577 913699 := bstep (se 1 (by rfl) ⟨685274, by rfl⟩ : syracuseStep 913699 = 1370549) B1370549
theorem B1372451 : Blo 912577 1372451 := bstep (se 1 (by rfl) ⟨1029338, by rfl⟩ : syracuseStep 1372451 = 2058677) B2058677
theorem B913715 : Blo 912577 913715 := bstep (se 1 (by rfl) ⟨685286, by rfl⟩ : syracuseStep 913715 = 1370573) B1370573
theorem B1372481 : Blo 912577 1372481 := bstep (se 2 (by rfl) ⟨514680, by rfl⟩ : syracuseStep 1372481 = 1029361) B1029361
theorem B913731 : Blo 912577 913731 := bstep (se 1 (by rfl) ⟨685298, by rfl⟩ : syracuseStep 913731 = 1370597) B1370597
theorem B913747 : Blo 912577 913747 := bstep (se 1 (by rfl) ⟨685310, by rfl⟩ : syracuseStep 913747 = 1370621) B1370621
theorem B1372499 : Blo 912577 1372499 := bstep (se 1 (by rfl) ⟨1029374, by rfl⟩ : syracuseStep 1372499 = 2058749) B2058749
theorem B913763 : Blo 912577 913763 := bstep (se 1 (by rfl) ⟨685322, by rfl⟩ : syracuseStep 913763 = 1370645) B1370645
theorem B12513649 : Blo 912577 12513649 := bstep (se 2 (by rfl) ⟨4692618, by rfl⟩ : syracuseStep 12513649 = 9385237) B9385237
theorem B1372529 : Blo 912577 1372529 := bstep (se 2 (by rfl) ⟨514698, by rfl⟩ : syracuseStep 1372529 = 1029397) B1029397
theorem B913779 : Blo 912577 913779 := bstep (se 1 (by rfl) ⟨685334, by rfl⟩ : syracuseStep 913779 = 1370669) B1370669
theorem B2060657 : Blo 912577 2060657 := bstep (se 2 (by rfl) ⟨772746, by rfl⟩ : syracuseStep 2060657 = 1545493) B1545493
theorem B913795 : Blo 912577 913795 := bstep (se 1 (by rfl) ⟨685346, by rfl⟩ : syracuseStep 913795 = 1370693) B1370693
theorem B1372547 : Blo 912577 1372547 := bstep (se 1 (by rfl) ⟨1029410, by rfl⟩ : syracuseStep 1372547 = 2058821) B2058821
theorem B2060675 : Blo 912577 2060675 := bstep (se 1 (by rfl) ⟨1545506, by rfl⟩ : syracuseStep 2060675 = 3091013) B3091013
theorem B913811 : Blo 912577 913811 := bstep (se 1 (by rfl) ⟨685358, by rfl⟩ : syracuseStep 913811 = 1370717) B1370717
theorem B1372577 : Blo 912577 1372577 := bstep (se 2 (by rfl) ⟨514716, by rfl⟩ : syracuseStep 1372577 = 1029433) B1029433
theorem B913827 : Blo 912577 913827 := bstep (se 1 (by rfl) ⟨685370, by rfl⟩ : syracuseStep 913827 = 1370741) B1370741
theorem B913843 : Blo 912577 913843 := bstep (se 1 (by rfl) ⟨685382, by rfl⟩ : syracuseStep 913843 = 1370765) B1370765
theorem B1372595 : Blo 912577 1372595 := bstep (se 1 (by rfl) ⟨1029446, by rfl⟩ : syracuseStep 1372595 = 2058893) B2058893
theorem B913859 : Blo 912577 913859 := bstep (se 1 (by rfl) ⟨685394, by rfl⟩ : syracuseStep 913859 = 1370789) B1370789
theorem B1372625 : Blo 912577 1372625 := bstep (se 2 (by rfl) ⟨514734, by rfl⟩ : syracuseStep 1372625 = 1029469) B1029469
theorem B913875 : Blo 912577 913875 := bstep (se 1 (by rfl) ⟨685406, by rfl⟩ : syracuseStep 913875 = 1370813) B1370813
theorem B913891 : Blo 912577 913891 := bstep (se 1 (by rfl) ⟨685418, by rfl⟩ : syracuseStep 913891 = 1370837) B1370837
theorem B1372643 : Blo 912577 1372643 := bstep (se 1 (by rfl) ⟨1029482, by rfl⟩ : syracuseStep 1372643 = 2058965) B2058965
theorem B913907 : Blo 912577 913907 := bstep (se 1 (by rfl) ⟨685430, by rfl⟩ : syracuseStep 913907 = 1370861) B1370861
theorem B1372673 : Blo 912577 1372673 := bstep (se 2 (by rfl) ⟨514752, by rfl⟩ : syracuseStep 1372673 = 1029505) B1029505
theorem B913923 : Blo 912577 913923 := bstep (se 1 (by rfl) ⟨685442, by rfl⟩ : syracuseStep 913923 = 1370885) B1370885
theorem B913939 : Blo 912577 913939 := bstep (se 1 (by rfl) ⟨685454, by rfl⟩ : syracuseStep 913939 = 1370909) B1370909
theorem B1372691 : Blo 912577 1372691 := bstep (se 1 (by rfl) ⟨1029518, by rfl⟩ : syracuseStep 1372691 = 2059037) B2059037
theorem B913955 : Blo 912577 913955 := bstep (se 1 (by rfl) ⟨685466, by rfl⟩ : syracuseStep 913955 = 1370933) B1370933
theorem B1372721 : Blo 912577 1372721 := bstep (se 2 (by rfl) ⟨514770, by rfl⟩ : syracuseStep 1372721 = 1029541) B1029541
theorem B913971 : Blo 912577 913971 := bstep (se 1 (by rfl) ⟨685478, by rfl⟩ : syracuseStep 913971 = 1370957) B1370957
theorem B913987 : Blo 912577 913987 := bstep (se 1 (by rfl) ⟨685490, by rfl⟩ : syracuseStep 913987 = 1370981) B1370981
theorem B1372739 : Blo 912577 1372739 := bstep (se 1 (by rfl) ⟨1029554, by rfl⟩ : syracuseStep 1372739 = 2059109) B2059109
theorem B914003 : Blo 912577 914003 := bstep (se 1 (by rfl) ⟨685502, by rfl⟩ : syracuseStep 914003 = 1371005) B1371005
theorem B1372769 : Blo 912577 1372769 := bstep (se 2 (by rfl) ⟨514788, by rfl⟩ : syracuseStep 1372769 = 1029577) B1029577
theorem B914019 : Blo 912577 914019 := bstep (se 1 (by rfl) ⟨685514, by rfl⟩ : syracuseStep 914019 = 1371029) B1371029
theorem B914035 : Blo 912577 914035 := bstep (se 1 (by rfl) ⟨685526, by rfl⟩ : syracuseStep 914035 = 1371053) B1371053
theorem B1372787 : Blo 912577 1372787 := bstep (se 1 (by rfl) ⟨1029590, by rfl⟩ : syracuseStep 1372787 = 2059181) B2059181
theorem B1733251 : Blo 912577 1733251 := bstep (se 1 (by rfl) ⟨1299938, by rfl⟩ : syracuseStep 1733251 = 2599877) B2599877
theorem B914051 : Blo 912577 914051 := bstep (se 1 (by rfl) ⟨685538, by rfl⟩ : syracuseStep 914051 = 1371077) B1371077
theorem B1372817 : Blo 912577 1372817 := bstep (se 2 (by rfl) ⟨514806, by rfl⟩ : syracuseStep 1372817 = 1029613) B1029613
theorem B2060945 : Blo 912577 2060945 := bstep (se 2 (by rfl) ⟨772854, by rfl⟩ : syracuseStep 2060945 = 1545709) B1545709
theorem B914067 : Blo 912577 914067 := bstep (se 1 (by rfl) ⟨685550, by rfl⟩ : syracuseStep 914067 = 1371101) B1371101
theorem B1667747 : Blo 912577 1667747 := bstep (se 1 (by rfl) ⟨1250810, by rfl⟩ : syracuseStep 1667747 = 2501621) B2501621
theorem B914083 : Blo 912577 914083 := bstep (se 1 (by rfl) ⟨685562, by rfl⟩ : syracuseStep 914083 = 1371125) B1371125
theorem B1372835 : Blo 912577 1372835 := bstep (se 1 (by rfl) ⟨1029626, by rfl⟩ : syracuseStep 1372835 = 2059253) B2059253
theorem B2060963 : Blo 912577 2060963 := bstep (se 1 (by rfl) ⟨1545722, by rfl⟩ : syracuseStep 2060963 = 3091445) B3091445
theorem B914099 : Blo 912577 914099 := bstep (se 1 (by rfl) ⟨685574, by rfl⟩ : syracuseStep 914099 = 1371149) B1371149
theorem B1372865 : Blo 912577 1372865 := bstep (se 2 (by rfl) ⟨514824, by rfl⟩ : syracuseStep 1372865 = 1029649) B1029649
theorem B914115 : Blo 912577 914115 := bstep (se 1 (by rfl) ⟨685586, by rfl⟩ : syracuseStep 914115 = 1371173) B1371173
theorem B914131 : Blo 912577 914131 := bstep (se 1 (by rfl) ⟨685598, by rfl⟩ : syracuseStep 914131 = 1371197) B1371197
theorem B1372883 : Blo 912577 1372883 := bstep (se 1 (by rfl) ⟨1029662, by rfl⟩ : syracuseStep 1372883 = 2059325) B2059325
theorem B914147 : Blo 912577 914147 := bstep (se 1 (by rfl) ⟨685610, by rfl⟩ : syracuseStep 914147 = 1371221) B1371221
theorem B1372913 : Blo 912577 1372913 := bstep (se 2 (by rfl) ⟨514842, by rfl⟩ : syracuseStep 1372913 = 1029685) B1029685
theorem B914163 : Blo 912577 914163 := bstep (se 1 (by rfl) ⟨685622, by rfl⟩ : syracuseStep 914163 = 1371245) B1371245
theorem B914179 : Blo 912577 914179 := bstep (se 1 (by rfl) ⟨685634, by rfl⟩ : syracuseStep 914179 = 1371269) B1371269
theorem B1372931 : Blo 912577 1372931 := bstep (se 1 (by rfl) ⟨1029698, by rfl⟩ : syracuseStep 1372931 = 2059397) B2059397
theorem B914195 : Blo 912577 914195 := bstep (se 1 (by rfl) ⟨685646, by rfl⟩ : syracuseStep 914195 = 1371293) B1371293
theorem B1372961 : Blo 912577 1372961 := bstep (se 2 (by rfl) ⟨514860, by rfl⟩ : syracuseStep 1372961 = 1029721) B1029721
theorem B914211 : Blo 912577 914211 := bstep (se 1 (by rfl) ⟨685658, by rfl⟩ : syracuseStep 914211 = 1371317) B1371317
theorem B914227 : Blo 912577 914227 := bstep (se 1 (by rfl) ⟨685670, by rfl⟩ : syracuseStep 914227 = 1371341) B1371341
theorem B1372979 : Blo 912577 1372979 := bstep (se 1 (by rfl) ⟨1029734, by rfl⟩ : syracuseStep 1372979 = 2059469) B2059469
theorem B914243 : Blo 912577 914243 := bstep (se 1 (by rfl) ⟨685682, by rfl⟩ : syracuseStep 914243 = 1371365) B1371365
theorem B1373009 : Blo 912577 1373009 := bstep (se 2 (by rfl) ⟨514878, by rfl⟩ : syracuseStep 1373009 = 1029757) B1029757
theorem B914259 : Blo 912577 914259 := bstep (se 1 (by rfl) ⟨685694, by rfl⟩ : syracuseStep 914259 = 1371389) B1371389
theorem B914275 : Blo 912577 914275 := bstep (se 1 (by rfl) ⟨685706, by rfl⟩ : syracuseStep 914275 = 1371413) B1371413
theorem B1373027 : Blo 912577 1373027 := bstep (se 1 (by rfl) ⟨1029770, by rfl⟩ : syracuseStep 1373027 = 2059541) B2059541
theorem B914291 : Blo 912577 914291 := bstep (se 1 (by rfl) ⟨685718, by rfl⟩ : syracuseStep 914291 = 1371437) B1371437
theorem B1373057 : Blo 912577 1373057 := bstep (se 2 (by rfl) ⟨514896, by rfl⟩ : syracuseStep 1373057 = 1029793) B1029793
theorem B914307 : Blo 912577 914307 := bstep (se 1 (by rfl) ⟨685730, by rfl⟩ : syracuseStep 914307 = 1371461) B1371461
theorem B914323 : Blo 912577 914323 := bstep (se 1 (by rfl) ⟨685742, by rfl⟩ : syracuseStep 914323 = 1371485) B1371485
theorem B1373075 : Blo 912577 1373075 := bstep (se 1 (by rfl) ⟨1029806, by rfl⟩ : syracuseStep 1373075 = 2059613) B2059613
theorem B914339 : Blo 912577 914339 := bstep (se 1 (by rfl) ⟨685754, by rfl⟩ : syracuseStep 914339 = 1371509) B1371509
theorem B1373105 : Blo 912577 1373105 := bstep (se 2 (by rfl) ⟨514914, by rfl⟩ : syracuseStep 1373105 = 1029829) B1029829
theorem B2061233 : Blo 912577 2061233 := bstep (se 2 (by rfl) ⟨772962, by rfl⟩ : syracuseStep 2061233 = 1545925) B1545925
theorem B914355 : Blo 912577 914355 := bstep (se 1 (by rfl) ⟨685766, by rfl⟩ : syracuseStep 914355 = 1371533) B1371533
theorem B914371 : Blo 912577 914371 := bstep (se 1 (by rfl) ⟨685778, by rfl⟩ : syracuseStep 914371 = 1371557) B1371557
theorem B1373123 : Blo 912577 1373123 := bstep (se 1 (by rfl) ⟨1029842, by rfl⟩ : syracuseStep 1373123 = 2059685) B2059685
theorem B2061251 : Blo 912577 2061251 := bstep (se 1 (by rfl) ⟨1545938, by rfl⟩ : syracuseStep 2061251 = 3091877) B3091877
theorem B914387 : Blo 912577 914387 := bstep (se 1 (by rfl) ⟨685790, by rfl⟩ : syracuseStep 914387 = 1371581) B1371581
theorem B1373153 : Blo 912577 1373153 := bstep (se 2 (by rfl) ⟨514932, by rfl⟩ : syracuseStep 1373153 = 1029865) B1029865
theorem B914403 : Blo 912577 914403 := bstep (se 1 (by rfl) ⟨685802, by rfl⟩ : syracuseStep 914403 = 1371605) B1371605
theorem B914419 : Blo 912577 914419 := bstep (se 1 (by rfl) ⟨685814, by rfl⟩ : syracuseStep 914419 = 1371629) B1371629
theorem B1373171 : Blo 912577 1373171 := bstep (se 1 (by rfl) ⟨1029878, by rfl⟩ : syracuseStep 1373171 = 2059757) B2059757
theorem B914435 : Blo 912577 914435 := bstep (se 1 (by rfl) ⟨685826, by rfl⟩ : syracuseStep 914435 = 1371653) B1371653
theorem B1373201 : Blo 912577 1373201 := bstep (se 2 (by rfl) ⟨514950, by rfl⟩ : syracuseStep 1373201 = 1029901) B1029901
theorem B914451 : Blo 912577 914451 := bstep (se 1 (by rfl) ⟨685838, by rfl⟩ : syracuseStep 914451 = 1371677) B1371677
theorem B914467 : Blo 912577 914467 := bstep (se 1 (by rfl) ⟨685850, by rfl⟩ : syracuseStep 914467 = 1371701) B1371701
theorem B1373219 : Blo 912577 1373219 := bstep (se 1 (by rfl) ⟨1029914, by rfl⟩ : syracuseStep 1373219 = 2059829) B2059829
theorem B914483 : Blo 912577 914483 := bstep (se 1 (by rfl) ⟨685862, by rfl⟩ : syracuseStep 914483 = 1371725) B1371725
theorem B1373249 : Blo 912577 1373249 := bstep (se 2 (by rfl) ⟨514968, by rfl⟩ : syracuseStep 1373249 = 1029937) B1029937
theorem B1733699 : Blo 912577 1733699 := bstep (se 1 (by rfl) ⟨1300274, by rfl⟩ : syracuseStep 1733699 = 2600549) B2600549
theorem B914499 : Blo 912577 914499 := bstep (se 1 (by rfl) ⟨685874, by rfl⟩ : syracuseStep 914499 = 1371749) B1371749
theorem B914515 : Blo 912577 914515 := bstep (se 1 (by rfl) ⟨685886, by rfl⟩ : syracuseStep 914515 = 1371773) B1371773
theorem B1373267 : Blo 912577 1373267 := bstep (se 1 (by rfl) ⟨1029950, by rfl⟩ : syracuseStep 1373267 = 2059901) B2059901
theorem B3470435 : Blo 912577 3470435 := bstep (se 1 (by rfl) ⟨2602826, by rfl⟩ : syracuseStep 3470435 = 5205653) B5205653
theorem B914531 : Blo 912577 914531 := bstep (se 1 (by rfl) ⟨685898, by rfl⟩ : syracuseStep 914531 = 1371797) B1371797
theorem B1373297 : Blo 912577 1373297 := bstep (se 2 (by rfl) ⟨514986, by rfl⟩ : syracuseStep 1373297 = 1029973) B1029973
theorem B914547 : Blo 912577 914547 := bstep (se 1 (by rfl) ⟨685910, by rfl⟩ : syracuseStep 914547 = 1371821) B1371821
theorem B914563 : Blo 912577 914563 := bstep (se 1 (by rfl) ⟨685922, by rfl⟩ : syracuseStep 914563 = 1371845) B1371845
theorem B1373315 : Blo 912577 1373315 := bstep (se 1 (by rfl) ⟨1029986, by rfl⟩ : syracuseStep 1373315 = 2059973) B2059973
theorem B914579 : Blo 912577 914579 := bstep (se 1 (by rfl) ⟨685934, by rfl⟩ : syracuseStep 914579 = 1371869) B1371869
theorem B1373345 : Blo 912577 1373345 := bstep (se 2 (by rfl) ⟨515004, by rfl⟩ : syracuseStep 1373345 = 1030009) B1030009
theorem B4388003 : Blo 912577 4388003 := bstep (se 1 (by rfl) ⟨3291002, by rfl⟩ : syracuseStep 4388003 = 6582005) B6582005
theorem B914595 : Blo 912577 914595 := bstep (se 1 (by rfl) ⟨685946, by rfl⟩ : syracuseStep 914595 = 1371893) B1371893
theorem B5862563 : Blo 912577 5862563 := bstep (se 1 (by rfl) ⟨4396922, by rfl⟩ : syracuseStep 5862563 = 8793845) B8793845
theorem B914611 : Blo 912577 914611 := bstep (se 1 (by rfl) ⟨685958, by rfl⟩ : syracuseStep 914611 = 1371917) B1371917
theorem B1373363 : Blo 912577 1373363 := bstep (se 1 (by rfl) ⟨1030022, by rfl⟩ : syracuseStep 1373363 = 2060045) B2060045
theorem B914627 : Blo 912577 914627 := bstep (se 1 (by rfl) ⟨685970, by rfl⟩ : syracuseStep 914627 = 1371941) B1371941
theorem B1373393 : Blo 912577 1373393 := bstep (se 2 (by rfl) ⟨515022, by rfl⟩ : syracuseStep 1373393 = 1030045) B1030045
theorem B2061521 : Blo 912577 2061521 := bstep (se 2 (by rfl) ⟨773070, by rfl⟩ : syracuseStep 2061521 = 1546141) B1546141
theorem B914643 : Blo 912577 914643 := bstep (se 1 (by rfl) ⟨685982, by rfl⟩ : syracuseStep 914643 = 1371965) B1371965
theorem B914659 : Blo 912577 914659 := bstep (se 1 (by rfl) ⟨685994, by rfl⟩ : syracuseStep 914659 = 1371989) B1371989
theorem B1373411 : Blo 912577 1373411 := bstep (se 1 (by rfl) ⟨1030058, by rfl⟩ : syracuseStep 1373411 = 2060117) B2060117
theorem B2061539 : Blo 912577 2061539 := bstep (se 1 (by rfl) ⟨1546154, by rfl⟩ : syracuseStep 2061539 = 3092309) B3092309
theorem B914675 : Blo 912577 914675 := bstep (se 1 (by rfl) ⟨686006, by rfl⟩ : syracuseStep 914675 = 1372013) B1372013
theorem B1373441 : Blo 912577 1373441 := bstep (se 2 (by rfl) ⟨515040, by rfl⟩ : syracuseStep 1373441 = 1030081) B1030081
theorem B914691 : Blo 912577 914691 := bstep (se 1 (by rfl) ⟨686018, by rfl⟩ : syracuseStep 914691 = 1372037) B1372037
theorem B4945157 : Blo 912577 4945157 := bstep (se 4 (by rfl) ⟨463608, by rfl⟩ : syracuseStep 4945157 = 927217) B927217
theorem B914707 : Blo 912577 914707 := bstep (se 1 (by rfl) ⟨686030, by rfl⟩ : syracuseStep 914707 = 1372061) B1372061
theorem B1373459 : Blo 912577 1373459 := bstep (se 1 (by rfl) ⟨1030094, by rfl⟩ : syracuseStep 1373459 = 2060189) B2060189
theorem B914723 : Blo 912577 914723 := bstep (se 1 (by rfl) ⟨686042, by rfl⟩ : syracuseStep 914723 = 1372085) B1372085
theorem B1373489 : Blo 912577 1373489 := bstep (se 2 (by rfl) ⟨515058, by rfl⟩ : syracuseStep 1373489 = 1030117) B1030117
theorem B914739 : Blo 912577 914739 := bstep (se 1 (by rfl) ⟨686054, by rfl⟩ : syracuseStep 914739 = 1372109) B1372109
theorem B914755 : Blo 912577 914755 := bstep (se 1 (by rfl) ⟨686066, by rfl⟩ : syracuseStep 914755 = 1372133) B1372133
theorem B1373507 : Blo 912577 1373507 := bstep (se 1 (by rfl) ⟨1030130, by rfl⟩ : syracuseStep 1373507 = 2060261) B2060261
theorem B914771 : Blo 912577 914771 := bstep (se 1 (by rfl) ⟨686078, by rfl⟩ : syracuseStep 914771 = 1372157) B1372157
theorem B1373537 : Blo 912577 1373537 := bstep (se 2 (by rfl) ⟨515076, by rfl⟩ : syracuseStep 1373537 = 1030153) B1030153
theorem B1733987 : Blo 912577 1733987 := bstep (se 1 (by rfl) ⟨1300490, by rfl⟩ : syracuseStep 1733987 = 2600981) B2600981
theorem B914787 : Blo 912577 914787 := bstep (se 1 (by rfl) ⟨686090, by rfl⟩ : syracuseStep 914787 = 1372181) B1372181
theorem B2192753 : Blo 912577 2192753 := bstep (se 2 (by rfl) ⟨822282, by rfl⟩ : syracuseStep 2192753 = 1644565) B1644565
theorem B914803 : Blo 912577 914803 := bstep (se 1 (by rfl) ⟨686102, by rfl⟩ : syracuseStep 914803 = 1372205) B1372205
theorem B1373555 : Blo 912577 1373555 := bstep (se 1 (by rfl) ⟨1030166, by rfl⟩ : syracuseStep 1373555 = 2060333) B2060333
theorem B914819 : Blo 912577 914819 := bstep (se 1 (by rfl) ⟨686114, by rfl⟩ : syracuseStep 914819 = 1372229) B1372229
theorem B5207429 : Blo 912577 5207429 := bstep (se 4 (by rfl) ⟨488196, by rfl⟩ : syracuseStep 5207429 = 976393) B976393
theorem B1373585 : Blo 912577 1373585 := bstep (se 2 (by rfl) ⟨515094, by rfl⟩ : syracuseStep 1373585 = 1030189) B1030189
theorem B914835 : Blo 912577 914835 := bstep (se 1 (by rfl) ⟨686126, by rfl⟩ : syracuseStep 914835 = 1372253) B1372253
theorem B914851 : Blo 912577 914851 := bstep (se 1 (by rfl) ⟨686138, by rfl⟩ : syracuseStep 914851 = 1372277) B1372277
theorem B1373603 : Blo 912577 1373603 := bstep (se 1 (by rfl) ⟨1030202, by rfl⟩ : syracuseStep 1373603 = 2060405) B2060405
theorem B914867 : Blo 912577 914867 := bstep (se 1 (by rfl) ⟨686150, by rfl⟩ : syracuseStep 914867 = 1372301) B1372301
theorem B1373633 : Blo 912577 1373633 := bstep (se 2 (by rfl) ⟨515112, by rfl⟩ : syracuseStep 1373633 = 1030225) B1030225
theorem B914883 : Blo 912577 914883 := bstep (se 1 (by rfl) ⟨686162, by rfl⟩ : syracuseStep 914883 = 1372325) B1372325
theorem B914899 : Blo 912577 914899 := bstep (se 1 (by rfl) ⟨686174, by rfl⟩ : syracuseStep 914899 = 1372349) B1372349
theorem B1373651 : Blo 912577 1373651 := bstep (se 1 (by rfl) ⟨1030238, by rfl⟩ : syracuseStep 1373651 = 2060477) B2060477
theorem B914915 : Blo 912577 914915 := bstep (se 1 (by rfl) ⟨686186, by rfl⟩ : syracuseStep 914915 = 1372373) B1372373
theorem B1373681 : Blo 912577 1373681 := bstep (se 2 (by rfl) ⟨515130, by rfl⟩ : syracuseStep 1373681 = 1030261) B1030261
theorem B2061809 : Blo 912577 2061809 := bstep (se 2 (by rfl) ⟨773178, by rfl⟩ : syracuseStep 2061809 = 1546357) B1546357
theorem B914931 : Blo 912577 914931 := bstep (se 1 (by rfl) ⟨686198, by rfl⟩ : syracuseStep 914931 = 1372397) B1372397
theorem B914947 : Blo 912577 914947 := bstep (se 1 (by rfl) ⟨686210, by rfl⟩ : syracuseStep 914947 = 1372421) B1372421
theorem B1373699 : Blo 912577 1373699 := bstep (se 1 (by rfl) ⟨1030274, by rfl⟩ : syracuseStep 1373699 = 2060549) B2060549
theorem B2061827 : Blo 912577 2061827 := bstep (se 1 (by rfl) ⟨1546370, by rfl⟩ : syracuseStep 2061827 = 3092741) B3092741
theorem B914963 : Blo 912577 914963 := bstep (se 1 (by rfl) ⟨686222, by rfl⟩ : syracuseStep 914963 = 1372445) B1372445
theorem B1373729 : Blo 912577 1373729 := bstep (se 2 (by rfl) ⟨515148, by rfl⟩ : syracuseStep 1373729 = 1030297) B1030297
theorem B914979 : Blo 912577 914979 := bstep (se 1 (by rfl) ⟨686234, by rfl⟩ : syracuseStep 914979 = 1372469) B1372469
theorem B4945457 : Blo 912577 4945457 := bstep (se 2 (by rfl) ⟨1854546, by rfl⟩ : syracuseStep 4945457 = 3709093) B3709093
theorem B914995 : Blo 912577 914995 := bstep (se 1 (by rfl) ⟨686246, by rfl⟩ : syracuseStep 914995 = 1372493) B1372493
theorem B1373747 : Blo 912577 1373747 := bstep (se 1 (by rfl) ⟨1030310, by rfl⟩ : syracuseStep 1373747 = 2060621) B2060621
theorem B915011 : Blo 912577 915011 := bstep (se 1 (by rfl) ⟨686258, by rfl⟩ : syracuseStep 915011 = 1372517) B1372517
theorem B1373777 : Blo 912577 1373777 := bstep (se 2 (by rfl) ⟨515166, by rfl⟩ : syracuseStep 1373777 = 1030333) B1030333
theorem B915027 : Blo 912577 915027 := bstep (se 1 (by rfl) ⟨686270, by rfl⟩ : syracuseStep 915027 = 1372541) B1372541
theorem B915043 : Blo 912577 915043 := bstep (se 1 (by rfl) ⟨686282, by rfl⟩ : syracuseStep 915043 = 1372565) B1372565
theorem B1373795 : Blo 912577 1373795 := bstep (se 1 (by rfl) ⟨1030346, by rfl⟩ : syracuseStep 1373795 = 2060693) B2060693
theorem B915059 : Blo 912577 915059 := bstep (se 1 (by rfl) ⟨686294, by rfl⟩ : syracuseStep 915059 = 1372589) B1372589
theorem B1373825 : Blo 912577 1373825 := bstep (se 2 (by rfl) ⟨515184, by rfl⟩ : syracuseStep 1373825 = 1030369) B1030369
theorem B915075 : Blo 912577 915075 := bstep (se 1 (by rfl) ⟨686306, by rfl⟩ : syracuseStep 915075 = 1372613) B1372613
theorem B915091 : Blo 912577 915091 := bstep (se 1 (by rfl) ⟨686318, by rfl⟩ : syracuseStep 915091 = 1372637) B1372637
theorem B1373843 : Blo 912577 1373843 := bstep (se 1 (by rfl) ⟨1030382, by rfl⟩ : syracuseStep 1373843 = 2060765) B2060765
theorem B915107 : Blo 912577 915107 := bstep (se 1 (by rfl) ⟨686330, by rfl⟩ : syracuseStep 915107 = 1372661) B1372661
theorem B1373873 : Blo 912577 1373873 := bstep (se 2 (by rfl) ⟨515202, by rfl⟩ : syracuseStep 1373873 = 1030405) B1030405
theorem B915123 : Blo 912577 915123 := bstep (se 1 (by rfl) ⟨686342, by rfl⟩ : syracuseStep 915123 = 1372685) B1372685
theorem B915139 : Blo 912577 915139 := bstep (se 1 (by rfl) ⟨686354, by rfl⟩ : syracuseStep 915139 = 1372709) B1372709
theorem B6944453 : Blo 912577 6944453 := bstep (se 4 (by rfl) ⟨651042, by rfl⟩ : syracuseStep 6944453 = 1302085) B1302085
theorem B1373891 : Blo 912577 1373891 := bstep (se 1 (by rfl) ⟨1030418, by rfl⟩ : syracuseStep 1373891 = 2060837) B2060837
theorem B915155 : Blo 912577 915155 := bstep (se 1 (by rfl) ⟨686366, by rfl⟩ : syracuseStep 915155 = 1372733) B1372733
theorem B1373921 : Blo 912577 1373921 := bstep (se 2 (by rfl) ⟨515220, by rfl⟩ : syracuseStep 1373921 = 1030441) B1030441
theorem B915171 : Blo 912577 915171 := bstep (se 1 (by rfl) ⟨686378, by rfl⟩ : syracuseStep 915171 = 1372757) B1372757
theorem B915187 : Blo 912577 915187 := bstep (se 1 (by rfl) ⟨686390, by rfl⟩ : syracuseStep 915187 = 1372781) B1372781
theorem B1373939 : Blo 912577 1373939 := bstep (se 1 (by rfl) ⟨1030454, by rfl⟩ : syracuseStep 1373939 = 2060909) B2060909
theorem B915203 : Blo 912577 915203 := bstep (se 1 (by rfl) ⟨686402, by rfl⟩ : syracuseStep 915203 = 1372805) B1372805
theorem B1373969 : Blo 912577 1373969 := bstep (se 2 (by rfl) ⟨515238, by rfl⟩ : syracuseStep 1373969 = 1030477) B1030477
theorem B2062097 : Blo 912577 2062097 := bstep (se 2 (by rfl) ⟨773286, by rfl⟩ : syracuseStep 2062097 = 1546573) B1546573
theorem B915219 : Blo 912577 915219 := bstep (se 1 (by rfl) ⟨686414, by rfl⟩ : syracuseStep 915219 = 1372829) B1372829
theorem B915235 : Blo 912577 915235 := bstep (se 1 (by rfl) ⟨686426, by rfl⟩ : syracuseStep 915235 = 1372853) B1372853
theorem B1373987 : Blo 912577 1373987 := bstep (se 1 (by rfl) ⟨1030490, by rfl⟩ : syracuseStep 1373987 = 2060981) B2060981
theorem B2062115 : Blo 912577 2062115 := bstep (se 1 (by rfl) ⟨1546586, by rfl⟩ : syracuseStep 2062115 = 3093173) B3093173
theorem B915251 : Blo 912577 915251 := bstep (se 1 (by rfl) ⟨686438, by rfl⟩ : syracuseStep 915251 = 1372877) B1372877
theorem B1374017 : Blo 912577 1374017 := bstep (se 2 (by rfl) ⟨515256, by rfl⟩ : syracuseStep 1374017 = 1030513) B1030513
theorem B915267 : Blo 912577 915267 := bstep (se 1 (by rfl) ⟨686450, by rfl⟩ : syracuseStep 915267 = 1372901) B1372901
theorem B5207885 : Blo 912577 5207885 := bstep (se 3 (by rfl) ⟨976478, by rfl⟩ : syracuseStep 5207885 = 1952957) B1952957
theorem B915283 : Blo 912577 915283 := bstep (se 1 (by rfl) ⟨686462, by rfl⟩ : syracuseStep 915283 = 1372925) B1372925
theorem B1374035 : Blo 912577 1374035 := bstep (se 1 (by rfl) ⟨1030526, by rfl⟩ : syracuseStep 1374035 = 2061053) B2061053
theorem B915299 : Blo 912577 915299 := bstep (se 1 (by rfl) ⟨686474, by rfl⟩ : syracuseStep 915299 = 1372949) B1372949
theorem B1374065 : Blo 912577 1374065 := bstep (se 2 (by rfl) ⟨515274, by rfl⟩ : syracuseStep 1374065 = 1030549) B1030549
theorem B915315 : Blo 912577 915315 := bstep (se 1 (by rfl) ⟨686486, by rfl⟩ : syracuseStep 915315 = 1372973) B1372973
theorem B915331 : Blo 912577 915331 := bstep (se 1 (by rfl) ⟨686498, by rfl⟩ : syracuseStep 915331 = 1372997) B1372997
theorem B1374083 : Blo 912577 1374083 := bstep (se 1 (by rfl) ⟨1030562, by rfl⟩ : syracuseStep 1374083 = 2061125) B2061125
theorem B29718413 : Blo 912577 29718413 := bstep (se 3 (by rfl) ⟨5572202, by rfl⟩ : syracuseStep 29718413 = 11144405) B11144405
theorem B915347 : Blo 912577 915347 := bstep (se 1 (by rfl) ⟨686510, by rfl⟩ : syracuseStep 915347 = 1373021) B1373021
theorem B1374113 : Blo 912577 1374113 := bstep (se 2 (by rfl) ⟨515292, by rfl⟩ : syracuseStep 1374113 = 1030585) B1030585
theorem B915363 : Blo 912577 915363 := bstep (se 1 (by rfl) ⟨686522, by rfl⟩ : syracuseStep 915363 = 1373045) B1373045
theorem B915379 : Blo 912577 915379 := bstep (se 1 (by rfl) ⟨686534, by rfl⟩ : syracuseStep 915379 = 1373069) B1373069
theorem B1374131 : Blo 912577 1374131 := bstep (se 1 (by rfl) ⟨1030598, by rfl⟩ : syracuseStep 1374131 = 2061197) B2061197
theorem B915395 : Blo 912577 915395 := bstep (se 1 (by rfl) ⟨686546, by rfl⟩ : syracuseStep 915395 = 1373093) B1373093
theorem B1374161 : Blo 912577 1374161 := bstep (se 2 (by rfl) ⟨515310, by rfl⟩ : syracuseStep 1374161 = 1030621) B1030621
theorem B915411 : Blo 912577 915411 := bstep (se 1 (by rfl) ⟨686558, by rfl⟩ : syracuseStep 915411 = 1373117) B1373117
theorem B915427 : Blo 912577 915427 := bstep (se 1 (by rfl) ⟨686570, by rfl⟩ : syracuseStep 915427 = 1373141) B1373141
theorem B1374179 : Blo 912577 1374179 := bstep (se 1 (by rfl) ⟨1030634, by rfl⟩ : syracuseStep 1374179 = 2061269) B2061269
theorem B4388849 : Blo 912577 4388849 := bstep (se 2 (by rfl) ⟨1645818, by rfl⟩ : syracuseStep 4388849 = 3291637) B3291637
theorem B915443 : Blo 912577 915443 := bstep (se 1 (by rfl) ⟨686582, by rfl⟩ : syracuseStep 915443 = 1373165) B1373165
theorem B1374209 : Blo 912577 1374209 := bstep (se 2 (by rfl) ⟨515328, by rfl⟩ : syracuseStep 1374209 = 1030657) B1030657
theorem B915459 : Blo 912577 915459 := bstep (se 1 (by rfl) ⟨686594, by rfl⟩ : syracuseStep 915459 = 1373189) B1373189
theorem B915475 : Blo 912577 915475 := bstep (se 1 (by rfl) ⟨686606, by rfl⟩ : syracuseStep 915475 = 1373213) B1373213
theorem B1374227 : Blo 912577 1374227 := bstep (se 1 (by rfl) ⟨1030670, by rfl⟩ : syracuseStep 1374227 = 2061341) B2061341
theorem B915491 : Blo 912577 915491 := bstep (se 1 (by rfl) ⟨686618, by rfl⟩ : syracuseStep 915491 = 1373237) B1373237
theorem B1374257 : Blo 912577 1374257 := bstep (se 2 (by rfl) ⟨515346, by rfl⟩ : syracuseStep 1374257 = 1030693) B1030693
theorem B915507 : Blo 912577 915507 := bstep (se 1 (by rfl) ⟨686630, by rfl⟩ : syracuseStep 915507 = 1373261) B1373261
theorem B915523 : Blo 912577 915523 := bstep (se 1 (by rfl) ⟨686642, by rfl⟩ : syracuseStep 915523 = 1373285) B1373285
theorem B1374275 : Blo 912577 1374275 := bstep (se 1 (by rfl) ⟨1030706, by rfl⟩ : syracuseStep 1374275 = 2061413) B2061413
theorem B3471437 : Blo 912577 3471437 := bstep (se 3 (by rfl) ⟨650894, by rfl⟩ : syracuseStep 3471437 = 1301789) B1301789
theorem B915539 : Blo 912577 915539 := bstep (se 1 (by rfl) ⟨686654, by rfl⟩ : syracuseStep 915539 = 1373309) B1373309
theorem B1374305 : Blo 912577 1374305 := bstep (se 2 (by rfl) ⟨515364, by rfl⟩ : syracuseStep 1374305 = 1030729) B1030729
theorem B915555 : Blo 912577 915555 := bstep (se 1 (by rfl) ⟨686666, by rfl⟩ : syracuseStep 915555 = 1373333) B1373333
theorem B915571 : Blo 912577 915571 := bstep (se 1 (by rfl) ⟨686678, by rfl⟩ : syracuseStep 915571 = 1373357) B1373357
theorem B1374323 : Blo 912577 1374323 := bstep (se 1 (by rfl) ⟨1030742, by rfl⟩ : syracuseStep 1374323 = 2061485) B2061485
theorem B915587 : Blo 912577 915587 := bstep (se 1 (by rfl) ⟨686690, by rfl⟩ : syracuseStep 915587 = 1373381) B1373381
theorem B1374353 : Blo 912577 1374353 := bstep (se 2 (by rfl) ⟨515382, by rfl⟩ : syracuseStep 1374353 = 1030765) B1030765
theorem B915603 : Blo 912577 915603 := bstep (se 1 (by rfl) ⟨686702, by rfl⟩ : syracuseStep 915603 = 1373405) B1373405
theorem B915619 : Blo 912577 915619 := bstep (se 1 (by rfl) ⟨686714, by rfl⟩ : syracuseStep 915619 = 1373429) B1373429
theorem B1374371 : Blo 912577 1374371 := bstep (se 1 (by rfl) ⟨1030778, by rfl⟩ : syracuseStep 1374371 = 2061557) B2061557
theorem B915635 : Blo 912577 915635 := bstep (se 1 (by rfl) ⟨686726, by rfl⟩ : syracuseStep 915635 = 1373453) B1373453
theorem B1374401 : Blo 912577 1374401 := bstep (se 2 (by rfl) ⟨515400, by rfl⟩ : syracuseStep 1374401 = 1030801) B1030801
theorem B915651 : Blo 912577 915651 := bstep (se 1 (by rfl) ⟨686738, by rfl⟩ : syracuseStep 915651 = 1373477) B1373477
theorem B16939205 : Blo 912577 16939205 := bstep (se 4 (by rfl) ⟨1588050, by rfl⟩ : syracuseStep 16939205 = 3176101) B3176101
theorem B915667 : Blo 912577 915667 := bstep (se 1 (by rfl) ⟨686750, by rfl⟩ : syracuseStep 915667 = 1373501) B1373501
theorem B1374419 : Blo 912577 1374419 := bstep (se 1 (by rfl) ⟨1030814, by rfl⟩ : syracuseStep 1374419 = 2061629) B2061629
theorem B11729123 : Blo 912577 11729123 := bstep (se 1 (by rfl) ⟨8796842, by rfl⟩ : syracuseStep 11729123 = 17593685) B17593685
theorem B915683 : Blo 912577 915683 := bstep (se 1 (by rfl) ⟨686762, by rfl⟩ : syracuseStep 915683 = 1373525) B1373525
theorem B1374449 : Blo 912577 1374449 := bstep (se 2 (by rfl) ⟨515418, by rfl⟩ : syracuseStep 1374449 = 1030837) B1030837
theorem B915699 : Blo 912577 915699 := bstep (se 1 (by rfl) ⟨686774, by rfl⟩ : syracuseStep 915699 = 1373549) B1373549
theorem B915715 : Blo 912577 915715 := bstep (se 1 (by rfl) ⟨686786, by rfl⟩ : syracuseStep 915715 = 1373573) B1373573
theorem B1374467 : Blo 912577 1374467 := bstep (se 1 (by rfl) ⟨1030850, by rfl⟩ : syracuseStep 1374467 = 2061701) B2061701
theorem B1734929 : Blo 912577 1734929 := bstep (se 2 (by rfl) ⟨650598, by rfl⟩ : syracuseStep 1734929 = 1301197) B1301197
theorem B915731 : Blo 912577 915731 := bstep (se 1 (by rfl) ⟨686798, by rfl⟩ : syracuseStep 915731 = 1373597) B1373597
theorem B1374497 : Blo 912577 1374497 := bstep (se 2 (by rfl) ⟨515436, by rfl⟩ : syracuseStep 1374497 = 1030873) B1030873
theorem B915747 : Blo 912577 915747 := bstep (se 1 (by rfl) ⟨686810, by rfl⟩ : syracuseStep 915747 = 1373621) B1373621
theorem B915763 : Blo 912577 915763 := bstep (se 1 (by rfl) ⟨686822, by rfl⟩ : syracuseStep 915763 = 1373645) B1373645
theorem B1374515 : Blo 912577 1374515 := bstep (se 1 (by rfl) ⟨1030886, by rfl⟩ : syracuseStep 1374515 = 2061773) B2061773
theorem B915779 : Blo 912577 915779 := bstep (se 1 (by rfl) ⟨686834, by rfl⟩ : syracuseStep 915779 = 1373669) B1373669
theorem B1374545 : Blo 912577 1374545 := bstep (se 2 (by rfl) ⟨515454, by rfl⟩ : syracuseStep 1374545 = 1030909) B1030909
theorem B915795 : Blo 912577 915795 := bstep (se 1 (by rfl) ⟨686846, by rfl⟩ : syracuseStep 915795 = 1373693) B1373693
theorem B915811 : Blo 912577 915811 := bstep (se 1 (by rfl) ⟨686858, by rfl⟩ : syracuseStep 915811 = 1373717) B1373717
theorem B1374563 : Blo 912577 1374563 := bstep (se 1 (by rfl) ⟨1030922, by rfl⟩ : syracuseStep 1374563 = 2061845) B2061845
theorem B915827 : Blo 912577 915827 := bstep (se 1 (by rfl) ⟨686870, by rfl⟩ : syracuseStep 915827 = 1373741) B1373741
theorem B1374593 : Blo 912577 1374593 := bstep (se 2 (by rfl) ⟨515472, by rfl⟩ : syracuseStep 1374593 = 1030945) B1030945
theorem B915843 : Blo 912577 915843 := bstep (se 1 (by rfl) ⟨686882, by rfl⟩ : syracuseStep 915843 = 1373765) B1373765
theorem B2193809 : Blo 912577 2193809 := bstep (se 2 (by rfl) ⟨822678, by rfl⟩ : syracuseStep 2193809 = 1645357) B1645357
theorem B915859 : Blo 912577 915859 := bstep (se 1 (by rfl) ⟨686894, by rfl⟩ : syracuseStep 915859 = 1373789) B1373789
theorem B1374611 : Blo 912577 1374611 := bstep (se 1 (by rfl) ⟨1030958, by rfl⟩ : syracuseStep 1374611 = 2061917) B2061917
theorem B915875 : Blo 912577 915875 := bstep (se 1 (by rfl) ⟨686906, by rfl⟩ : syracuseStep 915875 = 1373813) B1373813
theorem B1374641 : Blo 912577 1374641 := bstep (se 2 (by rfl) ⟨515490, by rfl⟩ : syracuseStep 1374641 = 1030981) B1030981
theorem B915891 : Blo 912577 915891 := bstep (se 1 (by rfl) ⟨686918, by rfl⟩ : syracuseStep 915891 = 1373837) B1373837
theorem B915907 : Blo 912577 915907 := bstep (se 1 (by rfl) ⟨686930, by rfl⟩ : syracuseStep 915907 = 1373861) B1373861
theorem B1374659 : Blo 912577 1374659 := bstep (se 1 (by rfl) ⟨1030994, by rfl⟩ : syracuseStep 1374659 = 2061989) B2061989
theorem B6584773 : Blo 912577 6584773 := bstep (se 4 (by rfl) ⟨617322, by rfl⟩ : syracuseStep 6584773 = 1234645) B1234645
theorem B915923 : Blo 912577 915923 := bstep (se 1 (by rfl) ⟨686942, by rfl⟩ : syracuseStep 915923 = 1373885) B1373885
theorem B1374689 : Blo 912577 1374689 := bstep (se 2 (by rfl) ⟨515508, by rfl⟩ : syracuseStep 1374689 = 1031017) B1031017
theorem B915939 : Blo 912577 915939 := bstep (se 1 (by rfl) ⟨686954, by rfl⟩ : syracuseStep 915939 = 1373909) B1373909
theorem B915955 : Blo 912577 915955 := bstep (se 1 (by rfl) ⟨686966, by rfl⟩ : syracuseStep 915955 = 1373933) B1373933
theorem B1374707 : Blo 912577 1374707 := bstep (se 1 (by rfl) ⟨1031030, by rfl⟩ : syracuseStep 1374707 = 2062061) B2062061
theorem B915971 : Blo 912577 915971 := bstep (se 1 (by rfl) ⟨686978, by rfl⟩ : syracuseStep 915971 = 1373957) B1373957
theorem B1374737 : Blo 912577 1374737 := bstep (se 2 (by rfl) ⟨515526, by rfl⟩ : syracuseStep 1374737 = 1031053) B1031053
theorem B915987 : Blo 912577 915987 := bstep (se 1 (by rfl) ⟨686990, by rfl⟩ : syracuseStep 915987 = 1373981) B1373981
theorem B916003 : Blo 912577 916003 := bstep (se 1 (by rfl) ⟨687002, by rfl⟩ : syracuseStep 916003 = 1374005) B1374005
theorem B1374755 : Blo 912577 1374755 := bstep (se 1 (by rfl) ⟨1031066, by rfl⟩ : syracuseStep 1374755 = 2062133) B2062133
theorem B916019 : Blo 912577 916019 := bstep (se 1 (by rfl) ⟨687014, by rfl⟩ : syracuseStep 916019 = 1374029) B1374029
theorem B1374785 : Blo 912577 1374785 := bstep (se 2 (by rfl) ⟨515544, by rfl⟩ : syracuseStep 1374785 = 1031089) B1031089
theorem B916035 : Blo 912577 916035 := bstep (se 1 (by rfl) ⟨687026, by rfl⟩ : syracuseStep 916035 = 1374053) B1374053
theorem B916051 : Blo 912577 916051 := bstep (se 1 (by rfl) ⟨687038, by rfl⟩ : syracuseStep 916051 = 1374077) B1374077
theorem B1374803 : Blo 912577 1374803 := bstep (se 1 (by rfl) ⟨1031102, by rfl⟩ : syracuseStep 1374803 = 2062205) B2062205
theorem B916067 : Blo 912577 916067 := bstep (se 1 (by rfl) ⟨687050, by rfl⟩ : syracuseStep 916067 = 1374101) B1374101
theorem B1374833 : Blo 912577 1374833 := bstep (se 2 (by rfl) ⟨515562, by rfl⟩ : syracuseStep 1374833 = 1031125) B1031125
theorem B916083 : Blo 912577 916083 := bstep (se 1 (by rfl) ⟨687062, by rfl⟩ : syracuseStep 916083 = 1374125) B1374125
theorem B916099 : Blo 912577 916099 := bstep (se 1 (by rfl) ⟨687074, by rfl⟩ : syracuseStep 916099 = 1374149) B1374149
theorem B1374851 : Blo 912577 1374851 := bstep (se 1 (by rfl) ⟨1031138, by rfl⟩ : syracuseStep 1374851 = 2062277) B2062277
theorem B916115 : Blo 912577 916115 := bstep (se 1 (by rfl) ⟨687086, by rfl⟩ : syracuseStep 916115 = 1374173) B1374173
theorem B916131 : Blo 912577 916131 := bstep (se 1 (by rfl) ⟨687098, by rfl⟩ : syracuseStep 916131 = 1374197) B1374197
theorem B916147 : Blo 912577 916147 := bstep (se 1 (by rfl) ⟨687110, by rfl⟩ : syracuseStep 916147 = 1374221) B1374221
theorem B916163 : Blo 912577 916163 := bstep (se 1 (by rfl) ⟨687122, by rfl⟩ : syracuseStep 916163 = 1374245) B1374245
theorem B916179 : Blo 912577 916179 := bstep (se 1 (by rfl) ⟨687134, by rfl⟩ : syracuseStep 916179 = 1374269) B1374269
theorem B11107043 : Blo 912577 11107043 := bstep (se 1 (by rfl) ⟨8330282, by rfl⟩ : syracuseStep 11107043 = 16660565) B16660565
theorem B916195 : Blo 912577 916195 := bstep (se 1 (by rfl) ⟨687146, by rfl⟩ : syracuseStep 916195 = 1374293) B1374293
theorem B916211 : Blo 912577 916211 := bstep (se 1 (by rfl) ⟨687158, by rfl⟩ : syracuseStep 916211 = 1374317) B1374317
theorem B916227 : Blo 912577 916227 := bstep (se 1 (by rfl) ⟨687170, by rfl⟩ : syracuseStep 916227 = 1374341) B1374341
theorem B916243 : Blo 912577 916243 := bstep (se 1 (by rfl) ⟨687182, by rfl⟩ : syracuseStep 916243 = 1374365) B1374365
theorem B916259 : Blo 912577 916259 := bstep (se 1 (by rfl) ⟨687194, by rfl⟩ : syracuseStep 916259 = 1374389) B1374389
theorem B916275 : Blo 912577 916275 := bstep (se 1 (by rfl) ⟨687206, by rfl⟩ : syracuseStep 916275 = 1374413) B1374413
theorem B916291 : Blo 912577 916291 := bstep (se 1 (by rfl) ⟨687218, by rfl⟩ : syracuseStep 916291 = 1374437) B1374437
theorem B916307 : Blo 912577 916307 := bstep (se 1 (by rfl) ⟨687230, by rfl⟩ : syracuseStep 916307 = 1374461) B1374461
theorem B916323 : Blo 912577 916323 := bstep (se 1 (by rfl) ⟨687242, by rfl⟩ : syracuseStep 916323 = 1374485) B1374485
theorem B916339 : Blo 912577 916339 := bstep (se 1 (by rfl) ⟨687254, by rfl⟩ : syracuseStep 916339 = 1374509) B1374509
theorem B916355 : Blo 912577 916355 := bstep (se 1 (by rfl) ⟨687266, by rfl⟩ : syracuseStep 916355 = 1374533) B1374533
theorem B916371 : Blo 912577 916371 := bstep (se 1 (by rfl) ⟨687278, by rfl⟩ : syracuseStep 916371 = 1374557) B1374557
theorem B916387 : Blo 912577 916387 := bstep (se 1 (by rfl) ⟨687290, by rfl⟩ : syracuseStep 916387 = 1374581) B1374581
theorem B916403 : Blo 912577 916403 := bstep (se 1 (by rfl) ⟨687302, by rfl⟩ : syracuseStep 916403 = 1374605) B1374605
theorem B916419 : Blo 912577 916419 := bstep (se 1 (by rfl) ⟨687314, by rfl⟩ : syracuseStep 916419 = 1374629) B1374629
theorem B916435 : Blo 912577 916435 := bstep (se 1 (by rfl) ⟨687326, by rfl⟩ : syracuseStep 916435 = 1374653) B1374653
theorem B916451 : Blo 912577 916451 := bstep (se 1 (by rfl) ⟨687338, by rfl⟩ : syracuseStep 916451 = 1374677) B1374677
theorem B916467 : Blo 912577 916467 := bstep (se 1 (by rfl) ⟨687350, by rfl⟩ : syracuseStep 916467 = 1374701) B1374701
theorem B916483 : Blo 912577 916483 := bstep (se 1 (by rfl) ⟨687362, by rfl⟩ : syracuseStep 916483 = 1374725) B1374725
theorem B916499 : Blo 912577 916499 := bstep (se 1 (by rfl) ⟨687374, by rfl⟩ : syracuseStep 916499 = 1374749) B1374749
theorem B916515 : Blo 912577 916515 := bstep (se 1 (by rfl) ⟨687386, by rfl⟩ : syracuseStep 916515 = 1374773) B1374773
theorem B916531 : Blo 912577 916531 := bstep (se 1 (by rfl) ⟨687398, by rfl⟩ : syracuseStep 916531 = 1374797) B1374797
theorem B916547 : Blo 912577 916547 := bstep (se 1 (by rfl) ⟨687410, by rfl⟩ : syracuseStep 916547 = 1374821) B1374821
theorem B916563 : Blo 912577 916563 := bstep (se 1 (by rfl) ⟨687422, by rfl⟩ : syracuseStep 916563 = 1374845) B1374845
theorem B2784397 : Blo 912577 2784397 := bstep (se 3 (by rfl) ⟨522074, by rfl⟩ : syracuseStep 2784397 = 1044149) B1044149
theorem B1735825 : Blo 912577 1735825 := bstep (se 2 (by rfl) ⟨650934, by rfl⟩ : syracuseStep 1735825 = 1301869) B1301869
theorem B3898637 : Blo 912577 3898637 := bstep (se 3 (by rfl) ⟨730994, by rfl⟩ : syracuseStep 3898637 = 1461989) B1461989
theorem B2194723 : Blo 912577 2194723 := bstep (se 1 (by rfl) ⟨1646042, by rfl⟩ : syracuseStep 2194723 = 3292085) B3292085
theorem B1735985 : Blo 912577 1735985 := bstep (se 2 (by rfl) ⟨650994, by rfl⟩ : syracuseStep 1735985 = 1301989) B1301989
theorem B2817677 : Blo 912577 2817677 := bstep (se 3 (by rfl) ⟨528314, by rfl⟩ : syracuseStep 2817677 = 1056629) B1056629
theorem B1736387 : Blo 912577 1736387 := bstep (se 1 (by rfl) ⟨1302290, by rfl⟩ : syracuseStep 1736387 = 2604581) B2604581
theorem B1539985 : Blo 912577 1539985 := bstep (se 2 (by rfl) ⟨577494, by rfl⟩ : syracuseStep 1539985 = 1154989) B1154989
theorem B1540019 : Blo 912577 1540019 := bstep (se 1 (by rfl) ⟨1155014, by rfl⟩ : syracuseStep 1540019 = 2310029) B2310029
theorem B3080267 : Blo 912577 3080267 := bstep (se 1 (by rfl) ⟨2310200, by rfl⟩ : syracuseStep 3080267 = 4620401) B4620401
theorem B1540235 : Blo 912577 1540235 := bstep (se 1 (by rfl) ⟨1155176, by rfl⟩ : syracuseStep 1540235 = 2310353) B2310353
theorem B1540363 : Blo 912577 1540363 := bstep (se 1 (by rfl) ⟨1155272, by rfl⟩ : syracuseStep 1540363 = 2310545) B2310545
theorem B3080537 : Blo 912577 3080537 := bstep (se 2 (by rfl) ⟨1155201, by rfl⟩ : syracuseStep 3080537 = 2310403) B2310403
theorem B1540505 : Blo 912577 1540505 := bstep (se 2 (by rfl) ⟨577689, by rfl⟩ : syracuseStep 1540505 = 1155379) B1155379
theorem B3473837 : Blo 912577 3473837 := bstep (se 3 (by rfl) ⟨651344, by rfl⟩ : syracuseStep 3473837 = 1302689) B1302689
theorem B1737139 : Blo 912577 1737139 := bstep (se 1 (by rfl) ⟨1302854, by rfl⟩ : syracuseStep 1737139 = 2605709) B2605709
theorem B2785715 : Blo 912577 2785715 := bstep (se 1 (by rfl) ⟨2089286, by rfl⟩ : syracuseStep 2785715 = 4178573) B4178573
theorem B3473867 : Blo 912577 3473867 := bstep (se 1 (by rfl) ⟨2605400, by rfl⟩ : syracuseStep 3473867 = 5210801) B5210801
theorem B1540633 : Blo 912577 1540633 := bstep (se 2 (by rfl) ⟨577737, by rfl⟩ : syracuseStep 1540633 = 1155475) B1155475
theorem B10551883 : Blo 912577 10551883 := bstep (se 1 (by rfl) ⟨7913912, by rfl⟩ : syracuseStep 10551883 = 15827825) B15827825
theorem B4948573 : Blo 912577 4948573 := bstep (se 3 (by rfl) ⟨927857, by rfl⟩ : syracuseStep 4948573 = 1855715) B1855715
theorem B1737587 : Blo 912577 1737587 := bstep (se 1 (by rfl) ⟨1303190, by rfl⟩ : syracuseStep 1737587 = 2606381) B2606381
theorem B3900311 : Blo 912577 3900311 := bstep (se 1 (by rfl) ⟨2925233, by rfl⟩ : syracuseStep 3900311 = 5850467) B5850467
theorem B1737625 : Blo 912577 1737625 := bstep (se 2 (by rfl) ⟨651609, by rfl⟩ : syracuseStep 1737625 = 1303219) B1303219
theorem B3081239 : Blo 912577 3081239 := bstep (se 1 (by rfl) ⟨2310929, by rfl⟩ : syracuseStep 3081239 = 4621859) B4621859
theorem B1541207 : Blo 912577 1541207 := bstep (se 1 (by rfl) ⟨1155905, by rfl⟩ : syracuseStep 1541207 = 2311811) B2311811
theorem B3474521 : Blo 912577 3474521 := bstep (se 2 (by rfl) ⟨1302945, by rfl⟩ : syracuseStep 3474521 = 2605891) B2605891
theorem B50136245 : Blo 912577 50136245 := bstep (se 5 (by rfl) ⟨2350136, by rfl⟩ : syracuseStep 50136245 = 4700273) B4700273
theorem B1541335 : Blo 912577 1541335 := bstep (se 1 (by rfl) ⟨1156001, by rfl⟩ : syracuseStep 1541335 = 2312003) B2312003
theorem B59245829 : Blo 912577 59245829 := bstep (se 4 (by rfl) ⟨5554296, by rfl⟩ : syracuseStep 59245829 = 11108593) B11108593
theorem B1738073 : Blo 912577 1738073 := bstep (se 2 (by rfl) ⟨651777, by rfl⟩ : syracuseStep 1738073 = 1303555) B1303555
theorem B5211485 : Blo 912577 5211485 := bstep (se 3 (by rfl) ⟨977153, by rfl⟩ : syracuseStep 5211485 = 1954307) B1954307
theorem B3474839 : Blo 912577 3474839 := bstep (se 1 (by rfl) ⟨2606129, by rfl⟩ : syracuseStep 3474839 = 5212259) B5212259
theorem B12387761 : Blo 912577 12387761 := bstep (se 2 (by rfl) ⟨4645410, by rfl⟩ : syracuseStep 12387761 = 9290821) B9290821
theorem B3081779 : Blo 912577 3081779 := bstep (se 1 (by rfl) ⟨2311334, by rfl⟩ : syracuseStep 3081779 = 4622669) B4622669
theorem B2229811 : Blo 912577 2229811 := bstep (se 1 (by rfl) ⟨1672358, by rfl⟩ : syracuseStep 2229811 = 3344717) B3344717
theorem B3082049 : Blo 912577 3082049 := bstep (se 2 (by rfl) ⟨1155768, by rfl⟩ : syracuseStep 3082049 = 2311537) B2311537
theorem B1541963 : Blo 912577 1541963 := bstep (se 1 (by rfl) ⟨1156472, by rfl⟩ : syracuseStep 1541963 = 2312945) B2312945
theorem B1542091 : Blo 912577 1542091 := bstep (se 1 (by rfl) ⟨1156568, by rfl⟩ : syracuseStep 1542091 = 2313137) B2313137
theorem B3475507 : Blo 912577 3475507 := bstep (se 1 (by rfl) ⟨2606630, by rfl⟩ : syracuseStep 3475507 = 5213261) B5213261
theorem B5867585 : Blo 912577 5867585 := bstep (se 2 (by rfl) ⟨2200344, by rfl⟩ : syracuseStep 5867585 = 4400689) B4400689
theorem B1738817 : Blo 912577 1738817 := bstep (se 2 (by rfl) ⟨652056, by rfl⟩ : syracuseStep 1738817 = 1304113) B1304113
theorem B1542233 : Blo 912577 1542233 := bstep (se 2 (by rfl) ⟨578337, by rfl⟩ : syracuseStep 1542233 = 1156675) B1156675
theorem B5572739 : Blo 912577 5572739 := bstep (se 1 (by rfl) ⟨4179554, by rfl⟩ : syracuseStep 5572739 = 8359109) B8359109
theorem B2197655 : Blo 912577 2197655 := bstep (se 1 (by rfl) ⟨1648241, by rfl⟩ : syracuseStep 2197655 = 3296483) B3296483
theorem B2230465 : Blo 912577 2230465 := bstep (se 2 (by rfl) ⟨836424, by rfl⟩ : syracuseStep 2230465 = 1672849) B1672849
theorem B1542361 : Blo 912577 1542361 := bstep (se 2 (by rfl) ⟨578385, by rfl⟩ : syracuseStep 1542361 = 1156771) B1156771
theorem B1739083 : Blo 912577 1739083 := bstep (se 1 (by rfl) ⟨1304312, by rfl⟩ : syracuseStep 1739083 = 2608625) B2608625
theorem B3082589 : Blo 912577 3082589 := bstep (se 3 (by rfl) ⟨577985, by rfl⟩ : syracuseStep 3082589 = 1155971) B1155971
theorem B3902003 : Blo 912577 3902003 := bstep (se 1 (by rfl) ⟨2926502, by rfl⟩ : syracuseStep 3902003 = 5853005) B5853005
theorem B16714421 : Blo 912577 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B1739531 : Blo 912577 1739531 := bstep (se 1 (by rfl) ⟨1304648, by rfl⟩ : syracuseStep 1739531 = 2609297) B2609297
theorem B1542935 : Blo 912577 1542935 := bstep (se 1 (by rfl) ⟨1157201, by rfl⟩ : syracuseStep 1542935 = 2314403) B2314403
theorem B3705689 : Blo 912577 3705689 := bstep (se 2 (by rfl) ⟨1389633, by rfl⟩ : syracuseStep 3705689 = 2779267) B2779267
theorem B1543063 : Blo 912577 1543063 := bstep (se 1 (by rfl) ⟨1157297, by rfl⟩ : syracuseStep 1543063 = 2314595) B2314595
theorem B2198423 : Blo 912577 2198423 := bstep (se 1 (by rfl) ⟨1648817, by rfl⟩ : syracuseStep 2198423 = 3297635) B3297635
theorem B1739713 : Blo 912577 1739713 := bstep (se 2 (by rfl) ⟨652392, by rfl⟩ : syracuseStep 1739713 = 1304785) B1304785
theorem B3476753 : Blo 912577 3476753 := bstep (se 2 (by rfl) ⟨1303782, by rfl⟩ : syracuseStep 3476753 = 2607565) B2607565
theorem B2198807 : Blo 912577 2198807 := bstep (se 1 (by rfl) ⟨1649105, by rfl⟩ : syracuseStep 2198807 = 3298211) B3298211
theorem B1740055 : Blo 912577 1740055 := bstep (se 1 (by rfl) ⟨1305041, by rfl⟩ : syracuseStep 1740055 = 2610083) B2610083
theorem B13208933 : Blo 912577 13208933 := bstep (se 4 (by rfl) ⟨1238337, by rfl⟩ : syracuseStep 13208933 = 2476675) B2476675
theorem B3083723 : Blo 912577 3083723 := bstep (se 1 (by rfl) ⟨2312792, by rfl⟩ : syracuseStep 3083723 = 4625585) B4625585
theorem B1543691 : Blo 912577 1543691 := bstep (se 1 (by rfl) ⟨1157768, by rfl⟩ : syracuseStep 1543691 = 2315537) B2315537
theorem B4623965 : Blo 912577 4623965 := bstep (se 3 (by rfl) ⟨866993, by rfl⟩ : syracuseStep 4623965 = 1733987) B1733987
theorem B3706499 : Blo 912577 3706499 := bstep (se 1 (by rfl) ⟨2779874, by rfl⟩ : syracuseStep 3706499 = 5559749) B5559749
theorem B1543819 : Blo 912577 1543819 := bstep (se 1 (by rfl) ⟨1157864, by rfl⟩ : syracuseStep 1543819 = 2315729) B2315729
theorem B4394675 : Blo 912577 4394675 := bstep (se 1 (by rfl) ⟨3296006, by rfl⟩ : syracuseStep 4394675 = 6592013) B6592013
theorem B3083993 : Blo 912577 3083993 := bstep (se 2 (by rfl) ⟨1156497, by rfl⟩ : syracuseStep 3083993 = 2312995) B2312995
theorem B5213969 : Blo 912577 5213969 := bstep (se 2 (by rfl) ⟨1955238, by rfl⟩ : syracuseStep 5213969 = 3910477) B3910477
theorem B1543961 : Blo 912577 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B7802669 : Blo 912577 7802669 := bstep (se 3 (by rfl) ⟨1463000, by rfl⟩ : syracuseStep 7802669 = 2926001) B2926001
theorem B4394845 : Blo 912577 4394845 := bstep (se 3 (by rfl) ⟨824033, by rfl⟩ : syracuseStep 4394845 = 1648067) B1648067
theorem B1544089 : Blo 912577 1544089 := bstep (se 2 (by rfl) ⟨579033, by rfl⟩ : syracuseStep 1544089 = 1158067) B1158067
theorem B3477451 : Blo 912577 3477451 := bstep (se 1 (by rfl) ⟨2608088, by rfl⟩ : syracuseStep 3477451 = 5216177) B5216177
theorem B3477725 : Blo 912577 3477725 := bstep (se 3 (by rfl) ⟨652073, by rfl⟩ : syracuseStep 3477725 = 1304147) B1304147
theorem B2199883 : Blo 912577 2199883 := bstep (se 1 (by rfl) ⟨1649912, by rfl⟩ : syracuseStep 2199883 = 3299825) B3299825
theorem B3084695 : Blo 912577 3084695 := bstep (se 1 (by rfl) ⟨2313521, by rfl⟩ : syracuseStep 3084695 = 4627043) B4627043
theorem B1544663 : Blo 912577 1544663 := bstep (se 1 (by rfl) ⟨1158497, by rfl⟩ : syracuseStep 1544663 = 2316995) B2316995
theorem B2200115 : Blo 912577 2200115 := bstep (se 1 (by rfl) ⟨1650086, by rfl⟩ : syracuseStep 2200115 = 3300173) B3300173
theorem B1544791 : Blo 912577 1544791 := bstep (se 1 (by rfl) ⟨1158593, by rfl⟩ : syracuseStep 1544791 = 2317187) B2317187
theorem B4690649 : Blo 912577 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B5870353 : Blo 912577 5870353 := bstep (se 2 (by rfl) ⟨2201382, by rfl⟩ : syracuseStep 5870353 = 4402765) B4402765
theorem B3478423 : Blo 912577 3478423 := bstep (se 1 (by rfl) ⟨2608817, by rfl⟩ : syracuseStep 3478423 = 5217635) B5217635
theorem B3085235 : Blo 912577 3085235 := bstep (se 1 (by rfl) ⟨2313926, by rfl⟩ : syracuseStep 3085235 = 4627853) B4627853
theorem B2200499 : Blo 912577 2200499 := bstep (se 1 (by rfl) ⟨1650374, by rfl⟩ : syracuseStep 2200499 = 3300749) B3300749
theorem B3708055 : Blo 912577 3708055 := bstep (se 1 (by rfl) ⟨2781041, by rfl⟩ : syracuseStep 3708055 = 5562083) B5562083
theorem B3904685 : Blo 912577 3904685 := bstep (se 3 (by rfl) ⟨732128, by rfl⟩ : syracuseStep 3904685 = 1464257) B1464257
theorem B3085505 : Blo 912577 3085505 := bstep (se 2 (by rfl) ⟨1157064, by rfl⟩ : syracuseStep 3085505 = 2314129) B2314129
theorem B1545419 : Blo 912577 1545419 := bstep (se 1 (by rfl) ⟨1159064, by rfl⟩ : syracuseStep 1545419 = 2318129) B2318129
theorem B1545547 : Blo 912577 1545547 := bstep (se 1 (by rfl) ⟨1159160, by rfl⟩ : syracuseStep 1545547 = 2318321) B2318321
theorem B12490163 : Blo 912577 12490163 := bstep (se 1 (by rfl) ⟨9367622, by rfl⟩ : syracuseStep 12490163 = 18735245) B18735245
theorem B1545689 : Blo 912577 1545689 := bstep (se 2 (by rfl) ⟨579633, by rfl⟩ : syracuseStep 1545689 = 1159267) B1159267
theorem B1545817 : Blo 912577 1545817 := bstep (se 2 (by rfl) ⟨579681, by rfl⟩ : syracuseStep 1545817 = 1159363) B1159363
theorem B4626071 : Blo 912577 4626071 := bstep (se 1 (by rfl) ⟨3469553, by rfl⟩ : syracuseStep 4626071 = 6939107) B6939107
theorem B3348119 : Blo 912577 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B3479213 : Blo 912577 3479213 := bstep (se 3 (by rfl) ⟨652352, by rfl⟩ : syracuseStep 3479213 = 1304705) B1304705
theorem B2201267 : Blo 912577 2201267 := bstep (se 1 (by rfl) ⟨1650950, by rfl⟩ : syracuseStep 2201267 = 3301901) B3301901
theorem B3086045 : Blo 912577 3086045 := bstep (se 3 (by rfl) ⟨578633, by rfl⟩ : syracuseStep 3086045 = 1157267) B1157267
theorem B10426157 : Blo 912577 10426157 := bstep (se 3 (by rfl) ⟨1954904, by rfl⟩ : syracuseStep 10426157 = 3909809) B3909809
theorem B16684865 : Blo 912577 16684865 := bstep (se 2 (by rfl) ⟨6256824, by rfl⟩ : syracuseStep 16684865 = 12513649) B12513649
theorem B1644695 : Blo 912577 1644695 := bstep (se 1 (by rfl) ⟨1233521, by rfl⟩ : syracuseStep 1644695 = 2467043) B2467043
theorem B1546391 : Blo 912577 1546391 := bstep (se 1 (by rfl) ⟨1159793, by rfl⟩ : syracuseStep 1546391 = 2319587) B2319587
theorem B1546519 : Blo 912577 1546519 := bstep (se 1 (by rfl) ⟨1159889, by rfl⟩ : syracuseStep 1546519 = 2319779) B2319779
theorem B5577005 : Blo 912577 5577005 := bstep (se 3 (by rfl) ⟨1045688, by rfl⟩ : syracuseStep 5577005 = 2091377) B2091377
theorem B1644953 : Blo 912577 1644953 := bstep (se 2 (by rfl) ⟨616857, by rfl⟩ : syracuseStep 1644953 = 1233715) B1233715
theorem B7805645 : Blo 912577 7805645 := bstep (se 3 (by rfl) ⟨1463558, by rfl⟩ : syracuseStep 7805645 = 2927117) B2927117
theorem B3087179 : Blo 912577 3087179 := bstep (se 1 (by rfl) ⟨2315384, by rfl⟩ : syracuseStep 3087179 = 4630769) B4630769
theorem B3087449 : Blo 912577 3087449 := bstep (se 2 (by rfl) ⟨1157793, by rfl⟩ : syracuseStep 3087449 = 2315587) B2315587
theorem B1645697 : Blo 912577 1645697 := bstep (se 2 (by rfl) ⟨617136, by rfl⟩ : syracuseStep 1645697 = 1234273) B1234273
theorem B2006579 : Blo 912577 2006579 := bstep (se 1 (by rfl) ⟨1504934, by rfl⟩ : syracuseStep 2006579 = 3009869) B3009869
theorem B3088151 : Blo 912577 3088151 := bstep (se 1 (by rfl) ⟨2316113, by rfl⟩ : syracuseStep 3088151 = 4632227) B4632227
theorem B2006999 : Blo 912577 2006999 := bstep (se 1 (by rfl) ⟨1505249, by rfl⟩ : syracuseStep 2006999 = 3010499) B3010499
theorem B7414033 : Blo 912577 7414033 := bstep (se 2 (by rfl) ⟨2780262, by rfl⟩ : syracuseStep 7414033 = 5560525) B5560525
theorem B3088691 : Blo 912577 3088691 := bstep (se 1 (by rfl) ⟨2316518, by rfl⟩ : syracuseStep 3088691 = 4633037) B4633037
theorem B1647001 : Blo 912577 1647001 := bstep (se 2 (by rfl) ⟨617625, by rfl⟩ : syracuseStep 1647001 = 1235251) B1235251
theorem B3908033 : Blo 912577 3908033 := bstep (se 2 (by rfl) ⟨1465512, by rfl⟩ : syracuseStep 3908033 = 2931025) B2931025
theorem B3088961 : Blo 912577 3088961 := bstep (se 2 (by rfl) ⟨1158360, by rfl⟩ : syracuseStep 3088961 = 2316721) B2316721
theorem B1155799 : Blo 912577 1155799 := bstep (se 1 (by rfl) ⟨866849, by rfl⟩ : syracuseStep 1155799 = 1733699) B1733699
theorem B2925335 : Blo 912577 2925335 := bstep (se 1 (by rfl) ⟨2194001, by rfl⟩ : syracuseStep 2925335 = 4388003) B4388003
theorem B3908375 : Blo 912577 3908375 := bstep (se 1 (by rfl) ⟨2931281, by rfl⟩ : syracuseStep 3908375 = 5862563) B5862563
theorem B4170797 : Blo 912577 4170797 := bstep (se 3 (by rfl) ⟨782024, by rfl⟩ : syracuseStep 4170797 = 1564049) B1564049
theorem B3089501 : Blo 912577 3089501 := bstep (se 3 (by rfl) ⟨579281, by rfl⟩ : syracuseStep 3089501 = 1158563) B1158563
theorem B4629635 : Blo 912577 4629635 := bstep (se 1 (by rfl) ⟨3472226, by rfl⟩ : syracuseStep 4629635 = 6944453) B6944453
theorem B2925899 : Blo 912577 2925899 := bstep (se 1 (by rfl) ⟨2194424, by rfl⟩ : syracuseStep 2925899 = 4388849) B4388849
theorem B5219801 : Blo 912577 5219801 := bstep (se 2 (by rfl) ⟨1957425, by rfl⟩ : syracuseStep 5219801 = 3914851) B3914851
theorem B1156619 : Blo 912577 1156619 := bstep (se 1 (by rfl) ⟨867464, by rfl⟩ : syracuseStep 1156619 = 1734929) B1734929
theorem B3712529 : Blo 912577 3712529 := bstep (se 2 (by rfl) ⟨1392198, by rfl⟩ : syracuseStep 3712529 = 2784397) B2784397
theorem B7513805 : Blo 912577 7513805 := bstep (se 3 (by rfl) ⟨1408838, by rfl⟩ : syracuseStep 7513805 = 2817677) B2817677
theorem B2926297 : Blo 912577 2926297 := bstep (se 2 (by rfl) ⟨1097361, by rfl⟩ : syracuseStep 2926297 = 2194723) B2194723
theorem B2598749 : Blo 912577 2598749 := bstep (se 3 (by rfl) ⟨487265, by rfl⟩ : syracuseStep 2598749 = 974531) B974531
theorem B2599091 : Blo 912577 2599091 := bstep (se 1 (by rfl) ⟨1949318, by rfl⟩ : syracuseStep 2599091 = 3898637) B3898637
theorem B1157323 : Blo 912577 1157323 := bstep (se 1 (by rfl) ⟨867992, by rfl⟩ : syracuseStep 1157323 = 1735985) B1735985
theorem B3090635 : Blo 912577 3090635 := bstep (se 1 (by rfl) ⟨2317976, by rfl⟩ : syracuseStep 3090635 = 4635953) B4635953
theorem B1976729 : Blo 912577 1976729 := bstep (se 2 (by rfl) ⟨741273, by rfl⟩ : syracuseStep 1976729 = 1482547) B1482547
theorem B1157591 : Blo 912577 1157591 := bstep (se 1 (by rfl) ⟨868193, by rfl⟩ : syracuseStep 1157591 = 1736387) B1736387
theorem B3090905 : Blo 912577 3090905 := bstep (se 2 (by rfl) ⟨1159089, by rfl⟩ : syracuseStep 3090905 = 2318179) B2318179
theorem B928279 : Blo 912577 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B1026679 : Blo 912577 1026679 := bstep (se 1 (by rfl) ⟨770009, by rfl⟩ : syracuseStep 1026679 = 1540019) B1540019
theorem B1026859 : Blo 912577 1026859 := bstep (se 1 (by rfl) ⟨770144, by rfl⟩ : syracuseStep 1026859 = 1540289) B1540289
theorem B3910493 : Blo 912577 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B1026967 : Blo 912577 1026967 := bstep (se 1 (by rfl) ⟨770225, by rfl⟩ : syracuseStep 1026967 = 1540451) B1540451
theorem B2927539 : Blo 912577 2927539 := bstep (se 1 (by rfl) ⟨2195654, by rfl⟩ : syracuseStep 2927539 = 4391309) B4391309
theorem B1027147 : Blo 912577 1027147 := bstep (se 1 (by rfl) ⟨770360, by rfl⟩ : syracuseStep 1027147 = 1540721) B1540721
theorem B1485899 : Blo 912577 1485899 := bstep (se 1 (by rfl) ⟨1114424, by rfl⟩ : syracuseStep 1485899 = 2228849) B2228849
theorem B3910801 : Blo 912577 3910801 := bstep (se 2 (by rfl) ⟨1466550, by rfl⟩ : syracuseStep 3910801 = 2933101) B2933101
theorem B1158295 : Blo 912577 1158295 := bstep (se 1 (by rfl) ⟨868721, by rfl⟩ : syracuseStep 1158295 = 1737443) B1737443
theorem B3091607 : Blo 912577 3091607 := bstep (se 1 (by rfl) ⟨2318705, by rfl⟩ : syracuseStep 3091607 = 4637411) B4637411
theorem B3910835 : Blo 912577 3910835 := bstep (se 1 (by rfl) ⟨2933126, by rfl⟩ : syracuseStep 3910835 = 5866253) B5866253
theorem B1027255 : Blo 912577 1027255 := bstep (se 1 (by rfl) ⟨770441, by rfl⟩ : syracuseStep 1027255 = 1540883) B1540883
theorem B1387735 : Blo 912577 1387735 := bstep (se 1 (by rfl) ⟨1040801, by rfl⟩ : syracuseStep 1387735 = 2081603) B2081603
theorem B1322201 : Blo 912577 1322201 := bstep (se 2 (by rfl) ⟨495825, by rfl⟩ : syracuseStep 1322201 = 991651) B991651
theorem B1027435 : Blo 912577 1027435 := bstep (se 1 (by rfl) ⟨770576, by rfl⟩ : syracuseStep 1027435 = 1541153) B1541153
theorem B1027543 : Blo 912577 1027543 := bstep (se 1 (by rfl) ⟨770657, by rfl⟩ : syracuseStep 1027543 = 1541315) B1541315
theorem B1650137 : Blo 912577 1650137 := bstep (se 2 (by rfl) ⟨618801, by rfl⟩ : syracuseStep 1650137 = 1237603) B1237603
theorem B1027723 : Blo 912577 1027723 := bstep (se 1 (by rfl) ⟨770792, by rfl⟩ : syracuseStep 1027723 = 1541585) B1541585
theorem B3092147 : Blo 912577 3092147 := bstep (se 1 (by rfl) ⟨2319110, by rfl⟩ : syracuseStep 3092147 = 4638221) B4638221
theorem B1027831 : Blo 912577 1027831 := bstep (se 1 (by rfl) ⟨770873, by rfl⟩ : syracuseStep 1027831 = 1541747) B1541747
theorem B1650547 : Blo 912577 1650547 := bstep (se 1 (by rfl) ⟨1237910, by rfl⟩ : syracuseStep 1650547 = 2475821) B2475821
theorem B1028011 : Blo 912577 1028011 := bstep (se 1 (by rfl) ⟨771008, by rfl⟩ : syracuseStep 1028011 = 1542017) B1542017
theorem B2469811 : Blo 912577 2469811 := bstep (se 1 (by rfl) ⟨1852358, by rfl⟩ : syracuseStep 2469811 = 3704717) B3704717
theorem B3092417 : Blo 912577 3092417 := bstep (se 2 (by rfl) ⟨1159656, by rfl⟩ : syracuseStep 3092417 = 2319313) B2319313
theorem B1028119 : Blo 912577 1028119 := bstep (se 1 (by rfl) ⟨771089, by rfl⟩ : syracuseStep 1028119 = 1542179) B1542179
theorem B2601163 : Blo 912577 2601163 := bstep (se 1 (by rfl) ⟨1950872, by rfl⟩ : syracuseStep 2601163 = 3901745) B3901745
theorem B1028299 : Blo 912577 1028299 := bstep (se 1 (by rfl) ⟨771224, by rfl⟩ : syracuseStep 1028299 = 1542449) B1542449
theorem B7516433 : Blo 912577 7516433 := bstep (se 2 (by rfl) ⟨2818662, by rfl⟩ : syracuseStep 7516433 = 5637325) B5637325
theorem B1028407 : Blo 912577 1028407 := bstep (se 1 (by rfl) ⟨771305, by rfl⟩ : syracuseStep 1028407 = 1542611) B1542611
theorem B3715417 : Blo 912577 3715417 := bstep (se 2 (by rfl) ⟨1393281, by rfl⟩ : syracuseStep 3715417 = 2786563) B2786563
theorem B3092957 : Blo 912577 3092957 := bstep (se 3 (by rfl) ⟨579929, by rfl⟩ : syracuseStep 3092957 = 1159859) B1159859
theorem B1028587 : Blo 912577 1028587 := bstep (se 1 (by rfl) ⟨771440, by rfl⟩ : syracuseStep 1028587 = 1542881) B1542881
theorem B1028695 : Blo 912577 1028695 := bstep (se 1 (by rfl) ⟨771521, by rfl⟩ : syracuseStep 1028695 = 1543043) B1543043
theorem B5943901 : Blo 912577 5943901 := bstep (se 3 (by rfl) ⟨1114481, by rfl⟩ : syracuseStep 5943901 = 2228963) B2228963
theorem B2601665 : Blo 912577 2601665 := bstep (se 2 (by rfl) ⟨975624, by rfl⟩ : syracuseStep 2601665 = 1951249) B1951249
theorem B1979083 : Blo 912577 1979083 := bstep (se 1 (by rfl) ⟨1484312, by rfl⟩ : syracuseStep 1979083 = 2968625) B2968625
theorem B1028875 : Blo 912577 1028875 := bstep (se 1 (by rfl) ⟨771656, by rfl⟩ : syracuseStep 1028875 = 1543313) B1543313
theorem B4633361 : Blo 912577 4633361 := bstep (se 2 (by rfl) ⟨1737510, by rfl⟩ : syracuseStep 4633361 = 3475021) B3475021
theorem B1160011 : Blo 912577 1160011 := bstep (se 1 (by rfl) ⟨870008, by rfl⟩ : syracuseStep 1160011 = 1740017) B1740017
theorem B1028983 : Blo 912577 1028983 := bstep (se 1 (by rfl) ⟨771737, by rfl⟩ : syracuseStep 1028983 = 1543475) B1543475
theorem B1651585 : Blo 912577 1651585 := bstep (se 2 (by rfl) ⟨619344, by rfl⟩ : syracuseStep 1651585 = 1238689) B1238689
theorem B4633523 : Blo 912577 4633523 := bstep (se 1 (by rfl) ⟨3475142, by rfl⟩ : syracuseStep 4633523 = 6950285) B6950285
theorem B2602007 : Blo 912577 2602007 := bstep (se 1 (by rfl) ⟨1951505, by rfl⟩ : syracuseStep 2602007 = 3903011) B3903011
theorem B1029163 : Blo 912577 1029163 := bstep (se 1 (by rfl) ⟨771872, by rfl⟩ : syracuseStep 1029163 = 1543745) B1543745
theorem B3912749 : Blo 912577 3912749 := bstep (se 3 (by rfl) ⟨733640, by rfl⟩ : syracuseStep 3912749 = 1467281) B1467281
theorem B3126347 : Blo 912577 3126347 := bstep (se 1 (by rfl) ⟨2344760, by rfl⟩ : syracuseStep 3126347 = 4689521) B4689521
theorem B1029271 : Blo 912577 1029271 := bstep (se 1 (by rfl) ⟨771953, by rfl⟩ : syracuseStep 1029271 = 1543907) B1543907
theorem B1029451 : Blo 912577 1029451 := bstep (se 1 (by rfl) ⟨772088, by rfl⟩ : syracuseStep 1029451 = 1544177) B1544177
theorem B1029559 : Blo 912577 1029559 := bstep (se 1 (by rfl) ⟨772169, by rfl⟩ : syracuseStep 1029559 = 1544339) B1544339
theorem B1029739 : Blo 912577 1029739 := bstep (se 1 (by rfl) ⟨772304, by rfl⟩ : syracuseStep 1029739 = 1544609) B1544609
theorem B1980055 : Blo 912577 1980055 := bstep (se 1 (by rfl) ⟨1485041, by rfl⟩ : syracuseStep 1980055 = 2970083) B2970083
theorem B1029847 : Blo 912577 1029847 := bstep (se 1 (by rfl) ⟨772385, by rfl⟩ : syracuseStep 1029847 = 1544771) B1544771
theorem B3913433 : Blo 912577 3913433 := bstep (se 2 (by rfl) ⟨1467537, by rfl⟩ : syracuseStep 3913433 = 2935075) B2935075
theorem B7124753 : Blo 912577 7124753 := bstep (se 2 (by rfl) ⟨2671782, by rfl⟩ : syracuseStep 7124753 = 5343565) B5343565
theorem B1390411 : Blo 912577 1390411 := bstep (se 1 (by rfl) ⟨1042808, by rfl⟩ : syracuseStep 1390411 = 2085617) B2085617
theorem B1030027 : Blo 912577 1030027 := bstep (se 1 (by rfl) ⟨772520, by rfl⟩ : syracuseStep 1030027 = 1545041) B1545041
theorem B1030135 : Blo 912577 1030135 := bstep (se 1 (by rfl) ⟨772601, by rfl⟩ : syracuseStep 1030135 = 1545203) B1545203
theorem B3127385 : Blo 912577 3127385 := bstep (se 2 (by rfl) ⟨1172769, by rfl⟩ : syracuseStep 3127385 = 2345539) B2345539
theorem B1030315 : Blo 912577 1030315 := bstep (se 1 (by rfl) ⟨772736, by rfl⟩ : syracuseStep 1030315 = 1545473) B1545473
theorem B5552401 : Blo 912577 5552401 := bstep (se 2 (by rfl) ⟨2082150, by rfl⟩ : syracuseStep 5552401 = 4164301) B4164301
theorem B1030423 : Blo 912577 1030423 := bstep (se 1 (by rfl) ⟨772817, by rfl⟩ : syracuseStep 1030423 = 1545635) B1545635
theorem B1030603 : Blo 912577 1030603 := bstep (se 1 (by rfl) ⟨772952, by rfl⟩ : syracuseStep 1030603 = 1545905) B1545905
theorem B1030711 : Blo 912577 1030711 := bstep (se 1 (by rfl) ⟨773033, by rfl⟩ : syracuseStep 1030711 = 1546067) B1546067
theorem B1030891 : Blo 912577 1030891 := bstep (se 1 (by rfl) ⟨773168, by rfl⟩ : syracuseStep 1030891 = 1546337) B1546337
theorem B1850177 : Blo 912577 1850177 := bstep (se 2 (by rfl) ⟨693816, by rfl⟩ : syracuseStep 1850177 = 1387633) B1387633
theorem B4635467 : Blo 912577 4635467 := bstep (se 1 (by rfl) ⟨3476600, by rfl⟩ : syracuseStep 4635467 = 6953201) B6953201
theorem B1030999 : Blo 912577 1030999 := bstep (se 1 (by rfl) ⟨773249, by rfl⟩ : syracuseStep 1030999 = 1546499) B1546499
theorem B3750787 : Blo 912577 3750787 := bstep (se 1 (by rfl) ⟨2813090, by rfl⟩ : syracuseStep 3750787 = 5626181) B5626181
theorem B2604125 : Blo 912577 2604125 := bstep (se 3 (by rfl) ⟨488273, by rfl⟩ : syracuseStep 2604125 = 976547) B976547
theorem B2473139 : Blo 912577 2473139 := bstep (se 1 (by rfl) ⟨1854854, by rfl⟩ : syracuseStep 2473139 = 3709709) B3709709
theorem B171589013 : Blo 912577 171589013 := bstep (se 6 (by rfl) ⟨4021617, by rfl⟩ : syracuseStep 171589013 = 8043235) B8043235
theorem B3292589 : Blo 912577 3292589 := bstep (se 3 (by rfl) ⟨617360, by rfl⟩ : syracuseStep 3292589 = 1234721) B1234721
theorem B2604467 : Blo 912577 2604467 := bstep (se 1 (by rfl) ⟨1953350, by rfl⟩ : syracuseStep 2604467 = 3906701) B3906701
theorem B2473907 : Blo 912577 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B1949771 : Blo 912577 1949771 := bstep (se 1 (by rfl) ⟨1462328, by rfl⟩ : syracuseStep 1949771 = 2924657) B2924657
theorem B2474135 : Blo 912577 2474135 := bstep (se 1 (by rfl) ⟨1855601, by rfl⟩ : syracuseStep 2474135 = 3711203) B3711203
theorem B3293713 : Blo 912577 3293713 := bstep (se 2 (by rfl) ⟨1235142, by rfl⟩ : syracuseStep 3293713 = 2470285) B2470285
theorem B2310707 : Blo 912577 2310707 := bstep (se 1 (by rfl) ⟨1733030, by rfl⟩ : syracuseStep 2310707 = 3466061) B3466061
theorem B4637249 : Blo 912577 4637249 := bstep (se 2 (by rfl) ⟨1738968, by rfl⟩ : syracuseStep 4637249 = 3477937) B3477937
theorem B3293827 : Blo 912577 3293827 := bstep (se 1 (by rfl) ⟨2470370, by rfl⟩ : syracuseStep 3293827 = 4940741) B4940741
theorem B2311001 : Blo 912577 2311001 := bstep (se 2 (by rfl) ⟨866625, by rfl⟩ : syracuseStep 2311001 = 1733251) B1733251
theorem B6931331 : Blo 912577 6931331 := bstep (se 1 (by rfl) ⟨5198498, by rfl⟩ : syracuseStep 6931331 = 10396997) B10396997
theorem B1950617 : Blo 912577 1950617 := bstep (se 2 (by rfl) ⟨731481, by rfl⟩ : syracuseStep 1950617 = 1462963) B1462963
theorem B5850157 : Blo 912577 5850157 := bstep (se 3 (by rfl) ⟨1096904, by rfl⟩ : syracuseStep 5850157 = 2193809) B2193809
theorem B1099019 : Blo 912577 1099019 := bstep (se 1 (by rfl) ⟨824264, by rfl⟩ : syracuseStep 1099019 = 1648529) B1648529
theorem B1951283 : Blo 912577 1951283 := bstep (se 1 (by rfl) ⟨1463462, by rfl⟩ : syracuseStep 1951283 = 2926925) B2926925
theorem B2606813 : Blo 912577 2606813 := bstep (se 3 (by rfl) ⟨488777, by rfl⟩ : syracuseStep 2606813 = 977555) B977555
theorem B2082689 : Blo 912577 2082689 := bstep (se 2 (by rfl) ⟨781008, by rfl⟩ : syracuseStep 2082689 = 1562017) B1562017
theorem B2607041 : Blo 912577 2607041 := bstep (se 2 (by rfl) ⟨977640, by rfl⟩ : syracuseStep 2607041 = 1955281) B1955281
theorem B2476253 : Blo 912577 2476253 := bstep (se 3 (by rfl) ⟨464297, by rfl⟩ : syracuseStep 2476253 = 928595) B928595
theorem B2607383 : Blo 912577 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B2312651 : Blo 912577 2312651 := bstep (se 1 (by rfl) ⟨1734488, by rfl⟩ : syracuseStep 2312651 = 3468977) B3468977
theorem B4639193 : Blo 912577 4639193 := bstep (se 2 (by rfl) ⟨1739697, by rfl⟩ : syracuseStep 4639193 = 3479395) B3479395
theorem B1952257 : Blo 912577 1952257 := bstep (se 2 (by rfl) ⟨732096, by rfl⟩ : syracuseStep 1952257 = 1464193) B1464193
theorem B1952513 : Blo 912577 1952513 := bstep (se 2 (by rfl) ⟨732192, by rfl⟩ : syracuseStep 1952513 = 1464385) B1464385
theorem B1952599 : Blo 912577 1952599 := bstep (se 1 (by rfl) ⟨1464449, by rfl⟩ : syracuseStep 1952599 = 2928899) B2928899
theorem B9882485 : Blo 912577 9882485 := bstep (se 5 (by rfl) ⟨463241, by rfl⟩ : syracuseStep 9882485 = 926483) B926483
theorem B2477249 : Blo 912577 2477249 := bstep (se 2 (by rfl) ⟨928968, by rfl⟩ : syracuseStep 2477249 = 1857937) B1857937
theorem B3132695 : Blo 912577 3132695 := bstep (se 1 (by rfl) ⟨2349521, by rfl⟩ : syracuseStep 3132695 = 4699043) B4699043
theorem B2313623 : Blo 912577 2313623 := bstep (se 1 (by rfl) ⟨1735217, by rfl⟩ : syracuseStep 2313623 = 3470435) B3470435
theorem B1854913 : Blo 912577 1854913 := bstep (se 2 (by rfl) ⟨695592, by rfl⟩ : syracuseStep 1854913 = 1391185) B1391185
theorem B1756631 : Blo 912577 1756631 := bstep (se 1 (by rfl) ⟨1317473, by rfl⟩ : syracuseStep 1756631 = 2634947) B2634947
theorem B3296771 : Blo 912577 3296771 := bstep (se 1 (by rfl) ⟨2472578, by rfl⟩ : syracuseStep 3296771 = 4945157) B4945157
theorem B1756723 : Blo 912577 1756723 := bstep (se 1 (by rfl) ⟨1317542, by rfl⟩ : syracuseStep 1756723 = 2635085) B2635085
theorem B1461835 : Blo 912577 1461835 := bstep (se 1 (by rfl) ⟨1096376, by rfl⟩ : syracuseStep 1461835 = 2192753) B2192753
theorem B3296857 : Blo 912577 3296857 := bstep (se 2 (by rfl) ⟨1236321, by rfl⟩ : syracuseStep 3296857 = 2472643) B2472643
theorem B3296971 : Blo 912577 3296971 := bstep (se 1 (by rfl) ⟨2472728, by rfl⟩ : syracuseStep 3296971 = 4945457) B4945457
theorem B50024141 : Blo 912577 50024141 := bstep (se 3 (by rfl) ⟨9379526, by rfl⟩ : syracuseStep 50024141 = 18759053) B18759053
theorem B1756939 : Blo 912577 1756939 := bstep (se 1 (by rfl) ⟨1317704, by rfl⟩ : syracuseStep 1756939 = 2635409) B2635409
theorem B2084633 : Blo 912577 2084633 := bstep (se 2 (by rfl) ⟨781737, by rfl⟩ : syracuseStep 2084633 = 1563475) B1563475
theorem B19812275 : Blo 912577 19812275 := bstep (se 1 (by rfl) ⟨14859206, by rfl⟩ : syracuseStep 19812275 = 29718413) B29718413
theorem B2314291 : Blo 912577 2314291 := bstep (se 1 (by rfl) ⟨1735718, by rfl⟩ : syracuseStep 2314291 = 3471437) B3471437
theorem B11292803 : Blo 912577 11292803 := bstep (se 1 (by rfl) ⟨8469602, by rfl⟩ : syracuseStep 11292803 = 16939205) B16939205
theorem B7819415 : Blo 912577 7819415 := bstep (se 1 (by rfl) ⟨5864561, by rfl⟩ : syracuseStep 7819415 = 11729123) B11729123
theorem B2314433 : Blo 912577 2314433 := bstep (se 2 (by rfl) ⟨867912, by rfl⟩ : syracuseStep 2314433 = 1735825) B1735825
theorem B6934733 : Blo 912577 6934733 := bstep (se 3 (by rfl) ⟨1300262, by rfl⟩ : syracuseStep 6934733 = 2600525) B2600525
theorem B1462553 : Blo 912577 1462553 := bstep (se 2 (by rfl) ⟨548457, by rfl⟩ : syracuseStep 1462553 = 1096915) B1096915
theorem B1462745 : Blo 912577 1462745 := bstep (se 2 (by rfl) ⟨548529, by rfl⟩ : syracuseStep 1462745 = 1097059) B1097059
theorem B2609729 : Blo 912577 2609729 := bstep (se 2 (by rfl) ⟨978648, by rfl⟩ : syracuseStep 2609729 = 1957297) B1957297
theorem B1462873 : Blo 912577 1462873 := bstep (se 2 (by rfl) ⟨548577, by rfl⟩ : syracuseStep 1462873 = 1097155) B1097155
theorem B6935219 : Blo 912577 6935219 := bstep (se 1 (by rfl) ⟨5201414, by rfl⟩ : syracuseStep 6935219 = 10402829) B10402829
theorem B1758169 : Blo 912577 1758169 := bstep (se 2 (by rfl) ⟨659313, by rfl⟩ : syracuseStep 1758169 = 1318627) B1318627
theorem B2053313 : Blo 912577 2053313 := bstep (se 2 (by rfl) ⟨769992, by rfl⟩ : syracuseStep 2053313 = 1539985) B1539985
theorem B1856729 : Blo 912577 1856729 := bstep (se 2 (by rfl) ⟨696273, by rfl⟩ : syracuseStep 1856729 = 1392547) B1392547
theorem B1463513 : Blo 912577 1463513 := bstep (se 2 (by rfl) ⟨548817, by rfl⟩ : syracuseStep 1463513 = 1097635) B1097635
theorem B2053529 : Blo 912577 2053529 := bstep (se 2 (by rfl) ⟨770073, by rfl⟩ : syracuseStep 2053529 = 1540147) B1540147
theorem B2315699 : Blo 912577 2315699 := bstep (se 1 (by rfl) ⟨1736774, by rfl⟩ : syracuseStep 2315699 = 3473549) B3473549
theorem B2053619 : Blo 912577 2053619 := bstep (se 1 (by rfl) ⟨1540214, by rfl⟩ : syracuseStep 2053619 = 3080429) B3080429
theorem B1955315 : Blo 912577 1955315 := bstep (se 1 (by rfl) ⟨1466486, by rfl⟩ : syracuseStep 1955315 = 2932973) B2932973
theorem B2053655 : Blo 912577 2053655 := bstep (se 1 (by rfl) ⟨1540241, by rfl⟩ : syracuseStep 2053655 = 3080483) B3080483
theorem B2053835 : Blo 912577 2053835 := bstep (se 1 (by rfl) ⟨1540376, by rfl⟩ : syracuseStep 2053835 = 3080753) B3080753
theorem B2086603 : Blo 912577 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B2053889 : Blo 912577 2053889 := bstep (se 2 (by rfl) ⟨770208, by rfl⟩ : syracuseStep 2053889 = 1540417) B1540417
theorem B2316235 : Blo 912577 2316235 := bstep (se 1 (by rfl) ⟨1737176, by rfl⟩ : syracuseStep 2316235 = 3474353) B3474353
theorem B2054105 : Blo 912577 2054105 := bstep (se 2 (by rfl) ⟨770289, by rfl⟩ : syracuseStep 2054105 = 1540579) B1540579
theorem B2054195 : Blo 912577 2054195 := bstep (se 1 (by rfl) ⟨1540646, by rfl⟩ : syracuseStep 2054195 = 3081293) B3081293
theorem B2054231 : Blo 912577 2054231 := bstep (se 1 (by rfl) ⟨1540673, by rfl⟩ : syracuseStep 2054231 = 3081347) B3081347
theorem B2316377 : Blo 912577 2316377 := bstep (se 2 (by rfl) ⟨868641, by rfl⟩ : syracuseStep 2316377 = 1737283) B1737283
theorem B6936677 : Blo 912577 6936677 := bstep (se 4 (by rfl) ⟨650313, by rfl⟩ : syracuseStep 6936677 = 1300627) B1300627
theorem B3954839 : Blo 912577 3954839 := bstep (se 1 (by rfl) ⟨2966129, by rfl⟩ : syracuseStep 3954839 = 5932259) B5932259
theorem B2054411 : Blo 912577 2054411 := bstep (se 1 (by rfl) ⟨1540808, by rfl⟩ : syracuseStep 2054411 = 3081617) B3081617
theorem B2054465 : Blo 912577 2054465 := bstep (se 2 (by rfl) ⟨770424, by rfl⟩ : syracuseStep 2054465 = 1540849) B1540849
theorem B6347159 : Blo 912577 6347159 := bstep (se 1 (by rfl) ⟨4760369, by rfl⟩ : syracuseStep 6347159 = 9520739) B9520739
theorem B2054681 : Blo 912577 2054681 := bstep (se 2 (by rfl) ⟨770505, by rfl⟩ : syracuseStep 2054681 = 1541011) B1541011
theorem B6937163 : Blo 912577 6937163 := bstep (se 1 (by rfl) ⟨5202872, by rfl⟩ : syracuseStep 6937163 = 10405745) B10405745
theorem B2054771 : Blo 912577 2054771 := bstep (se 1 (by rfl) ⟨1541078, by rfl⟩ : syracuseStep 2054771 = 3082157) B3082157
theorem B2054807 : Blo 912577 2054807 := bstep (se 1 (by rfl) ⟨1541105, by rfl⟩ : syracuseStep 2054807 = 3082211) B3082211
theorem B1759895 : Blo 912577 1759895 := bstep (se 1 (by rfl) ⟨1319921, by rfl⟩ : syracuseStep 1759895 = 2639843) B2639843
theorem B36166385 : Blo 912577 36166385 := bstep (se 2 (by rfl) ⟨13562394, by rfl⟩ : syracuseStep 36166385 = 27124789) B27124789
theorem B1956631 : Blo 912577 1956631 := bstep (se 1 (by rfl) ⟨1467473, by rfl⟩ : syracuseStep 1956631 = 2934947) B2934947
theorem B2054987 : Blo 912577 2054987 := bstep (se 1 (by rfl) ⟨1541240, by rfl⟩ : syracuseStep 2054987 = 3082481) B3082481
theorem B2055041 : Blo 912577 2055041 := bstep (se 2 (by rfl) ⟨770640, by rfl⟩ : syracuseStep 2055041 = 1541281) B1541281
theorem B2317207 : Blo 912577 2317207 := bstep (se 1 (by rfl) ⟨1737905, by rfl⟩ : syracuseStep 2317207 = 3475811) B3475811
theorem B1956811 : Blo 912577 1956811 := bstep (se 1 (by rfl) ⟨1467608, by rfl⟩ : syracuseStep 1956811 = 2935217) B2935217
theorem B1956887 : Blo 912577 1956887 := bstep (se 1 (by rfl) ⟨1467665, by rfl⟩ : syracuseStep 1956887 = 2935331) B2935331
theorem B2776153 : Blo 912577 2776153 := bstep (se 2 (by rfl) ⟨1041057, by rfl⟩ : syracuseStep 2776153 = 2082115) B2082115
theorem B2055257 : Blo 912577 2055257 := bstep (se 2 (by rfl) ⟨770721, by rfl⟩ : syracuseStep 2055257 = 1541443) B1541443
theorem B4447325 : Blo 912577 4447325 := bstep (se 3 (by rfl) ⟨833873, by rfl⟩ : syracuseStep 4447325 = 1667747) B1667747
theorem B2055347 : Blo 912577 2055347 := bstep (se 1 (by rfl) ⟨1541510, by rfl⟩ : syracuseStep 2055347 = 3083021) B3083021
theorem B2055383 : Blo 912577 2055383 := bstep (se 1 (by rfl) ⟨1541537, by rfl⟩ : syracuseStep 2055383 = 3083075) B3083075
theorem B2317643 : Blo 912577 2317643 := bstep (se 1 (by rfl) ⟨1738232, by rfl⟩ : syracuseStep 2317643 = 3476465) B3476465
theorem B2055563 : Blo 912577 2055563 := bstep (se 1 (by rfl) ⟨1541672, by rfl⟩ : syracuseStep 2055563 = 3083345) B3083345
theorem B2055617 : Blo 912577 2055617 := bstep (se 2 (by rfl) ⟨770856, by rfl⟩ : syracuseStep 2055617 = 1541713) B1541713
theorem B2055833 : Blo 912577 2055833 := bstep (se 2 (by rfl) ⟨770937, by rfl⟩ : syracuseStep 2055833 = 1541875) B1541875
theorem B2318017 : Blo 912577 2318017 := bstep (se 2 (by rfl) ⟨869256, by rfl⟩ : syracuseStep 2318017 = 1738513) B1738513
theorem B2055923 : Blo 912577 2055923 := bstep (se 1 (by rfl) ⟨1541942, by rfl⟩ : syracuseStep 2055923 = 3083885) B3083885
theorem B2055959 : Blo 912577 2055959 := bstep (se 1 (by rfl) ⟨1541969, by rfl⟩ : syracuseStep 2055959 = 3083939) B3083939
theorem B2056139 : Blo 912577 2056139 := bstep (se 1 (by rfl) ⟨1542104, by rfl⟩ : syracuseStep 2056139 = 3084209) B3084209
theorem B2056193 : Blo 912577 2056193 := bstep (se 2 (by rfl) ⟨771072, by rfl⟩ : syracuseStep 2056193 = 1542145) B1542145
theorem B2056409 : Blo 912577 2056409 := bstep (se 2 (by rfl) ⟨771153, by rfl⟩ : syracuseStep 2056409 = 1542307) B1542307
theorem B2318615 : Blo 912577 2318615 := bstep (se 1 (by rfl) ⟨1738961, by rfl⟩ : syracuseStep 2318615 = 3477923) B3477923
theorem B2056499 : Blo 912577 2056499 := bstep (se 1 (by rfl) ⟨1542374, by rfl⟩ : syracuseStep 2056499 = 3084749) B3084749
theorem B2056535 : Blo 912577 2056535 := bstep (se 1 (by rfl) ⟨1542401, by rfl⟩ : syracuseStep 2056535 = 3084803) B3084803
theorem B1466839 : Blo 912577 1466839 := bstep (se 1 (by rfl) ⟨1100129, by rfl⟩ : syracuseStep 1466839 = 2200259) B2200259
theorem B2056715 : Blo 912577 2056715 := bstep (se 1 (by rfl) ⟨1542536, by rfl⟩ : syracuseStep 2056715 = 3085073) B3085073
theorem B3465773 : Blo 912577 3465773 := bstep (se 3 (by rfl) ⟨649832, by rfl⟩ : syracuseStep 3465773 = 1299665) B1299665
theorem B2056769 : Blo 912577 2056769 := bstep (se 2 (by rfl) ⟨771288, by rfl⟩ : syracuseStep 2056769 = 1542577) B1542577
theorem B3007127 : Blo 912577 3007127 := bstep (se 1 (by rfl) ⟨2255345, by rfl⟩ : syracuseStep 3007127 = 4510691) B4510691
theorem B975607 : Blo 912577 975607 := bstep (se 1 (by rfl) ⟨731705, by rfl⟩ : syracuseStep 975607 = 1463411) B1463411
theorem B2056985 : Blo 912577 2056985 := bstep (se 2 (by rfl) ⟨771369, by rfl⟩ : syracuseStep 2056985 = 1542739) B1542739
theorem B2057075 : Blo 912577 2057075 := bstep (se 1 (by rfl) ⟨1542806, by rfl⟩ : syracuseStep 2057075 = 3085613) B3085613
theorem B1368971 : Blo 912577 1368971 := bstep (se 1 (by rfl) ⟨1026728, by rfl⟩ : syracuseStep 1368971 = 2053457) B2053457
theorem B1368983 : Blo 912577 1368983 := bstep (se 1 (by rfl) ⟨1026737, by rfl⟩ : syracuseStep 1368983 = 2053475) B2053475
theorem B2057111 : Blo 912577 2057111 := bstep (se 1 (by rfl) ⟨1542833, by rfl⟩ : syracuseStep 2057111 = 3085667) B3085667
theorem B1303447 : Blo 912577 1303447 := bstep (se 1 (by rfl) ⟨977585, by rfl⟩ : syracuseStep 1303447 = 1955171) B1955171
theorem B1369049 : Blo 912577 1369049 := bstep (se 2 (by rfl) ⟨513393, by rfl⟩ : syracuseStep 1369049 = 1026787) B1026787
theorem B2319425 : Blo 912577 2319425 := bstep (se 2 (by rfl) ⟨869784, by rfl⟩ : syracuseStep 2319425 = 1739569) B1739569
theorem B1369163 : Blo 912577 1369163 := bstep (se 1 (by rfl) ⟨1026872, by rfl⟩ : syracuseStep 1369163 = 2053745) B2053745
theorem B2057291 : Blo 912577 2057291 := bstep (se 1 (by rfl) ⟨1542968, by rfl⟩ : syracuseStep 2057291 = 3085937) B3085937
theorem B1369175 : Blo 912577 1369175 := bstep (se 1 (by rfl) ⟨1026881, by rfl⟩ : syracuseStep 1369175 = 2053763) B2053763
theorem B975979 : Blo 912577 975979 := bstep (se 1 (by rfl) ⟨731984, by rfl⟩ : syracuseStep 975979 = 1463969) B1463969
theorem B2057345 : Blo 912577 2057345 := bstep (se 2 (by rfl) ⟨771504, by rfl⟩ : syracuseStep 2057345 = 1543009) B1543009
theorem B1369241 : Blo 912577 1369241 := bstep (se 2 (by rfl) ⟨513465, by rfl⟩ : syracuseStep 1369241 = 1026931) B1026931
theorem B11101445 : Blo 912577 11101445 := bstep (se 4 (by rfl) ⟨1040760, by rfl⟩ : syracuseStep 11101445 = 2081521) B2081521
theorem B1369355 : Blo 912577 1369355 := bstep (se 1 (by rfl) ⟨1027016, by rfl⟩ : syracuseStep 1369355 = 2054033) B2054033
theorem B1369367 : Blo 912577 1369367 := bstep (se 1 (by rfl) ⟨1027025, by rfl⟩ : syracuseStep 1369367 = 2054051) B2054051
theorem B3466547 : Blo 912577 3466547 := bstep (se 1 (by rfl) ⟨2599910, by rfl⟩ : syracuseStep 3466547 = 5199821) B5199821
theorem B1369433 : Blo 912577 1369433 := bstep (se 2 (by rfl) ⟨513537, by rfl⟩ : syracuseStep 1369433 = 1027075) B1027075
theorem B2057561 : Blo 912577 2057561 := bstep (se 2 (by rfl) ⟨771585, by rfl⟩ : syracuseStep 2057561 = 1543171) B1543171
theorem B15820211 : Blo 912577 15820211 := bstep (se 1 (by rfl) ⟨11865158, by rfl⟩ : syracuseStep 15820211 = 23730317) B23730317
theorem B2057651 : Blo 912577 2057651 := bstep (se 1 (by rfl) ⟨1543238, by rfl⟩ : syracuseStep 2057651 = 3086477) B3086477
theorem B1369547 : Blo 912577 1369547 := bstep (se 1 (by rfl) ⟨1027160, by rfl⟩ : syracuseStep 1369547 = 2054321) B2054321
theorem B1369559 : Blo 912577 1369559 := bstep (se 1 (by rfl) ⟨1027169, by rfl⟩ : syracuseStep 1369559 = 2054339) B2054339
theorem B2057687 : Blo 912577 2057687 := bstep (se 1 (by rfl) ⟨1543265, by rfl⟩ : syracuseStep 2057687 = 3086531) B3086531
theorem B1369625 : Blo 912577 1369625 := bstep (se 2 (by rfl) ⟨513609, by rfl⟩ : syracuseStep 1369625 = 1027219) B1027219
theorem B5563979 : Blo 912577 5563979 := bstep (se 1 (by rfl) ⟨4172984, by rfl⟩ : syracuseStep 5563979 = 8345969) B8345969
theorem B2319961 : Blo 912577 2319961 := bstep (se 2 (by rfl) ⟨869985, by rfl⟩ : syracuseStep 2319961 = 1739971) B1739971
theorem B1369739 : Blo 912577 1369739 := bstep (se 1 (by rfl) ⟨1027304, by rfl⟩ : syracuseStep 1369739 = 2054609) B2054609
theorem B2057867 : Blo 912577 2057867 := bstep (se 1 (by rfl) ⟨1543400, by rfl⟩ : syracuseStep 2057867 = 3086801) B3086801
theorem B1369751 : Blo 912577 1369751 := bstep (se 1 (by rfl) ⟨1027313, by rfl⟩ : syracuseStep 1369751 = 2054627) B2054627
theorem B2057921 : Blo 912577 2057921 := bstep (se 2 (by rfl) ⟨771720, by rfl⟩ : syracuseStep 2057921 = 1543441) B1543441
theorem B1369817 : Blo 912577 1369817 := bstep (se 2 (by rfl) ⟨513681, by rfl⟩ : syracuseStep 1369817 = 1027363) B1027363
theorem B1369931 : Blo 912577 1369931 := bstep (se 1 (by rfl) ⟨1027448, by rfl⟩ : syracuseStep 1369931 = 2054897) B2054897
theorem B1369943 : Blo 912577 1369943 := bstep (se 1 (by rfl) ⟨1027457, by rfl⟩ : syracuseStep 1369943 = 2054915) B2054915
theorem B1370009 : Blo 912577 1370009 := bstep (se 2 (by rfl) ⟨513753, by rfl⟩ : syracuseStep 1370009 = 1027507) B1027507
theorem B2058137 : Blo 912577 2058137 := bstep (se 2 (by rfl) ⟨771801, by rfl⟩ : syracuseStep 2058137 = 1543603) B1543603
theorem B3958721 : Blo 912577 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B2058227 : Blo 912577 2058227 := bstep (se 1 (by rfl) ⟨1543670, by rfl⟩ : syracuseStep 2058227 = 3087341) B3087341
theorem B1370123 : Blo 912577 1370123 := bstep (se 1 (by rfl) ⟨1027592, by rfl⟩ : syracuseStep 1370123 = 2055185) B2055185
theorem B1370135 : Blo 912577 1370135 := bstep (se 1 (by rfl) ⟨1027601, by rfl⟩ : syracuseStep 1370135 = 2055203) B2055203
theorem B2058263 : Blo 912577 2058263 := bstep (se 1 (by rfl) ⟨1543697, by rfl⟩ : syracuseStep 2058263 = 3087395) B3087395
theorem B1370201 : Blo 912577 1370201 := bstep (se 2 (by rfl) ⟨513825, by rfl⟩ : syracuseStep 1370201 = 1027651) B1027651
theorem B1370315 : Blo 912577 1370315 := bstep (se 1 (by rfl) ⟨1027736, by rfl⟩ : syracuseStep 1370315 = 2055473) B2055473
theorem B2058443 : Blo 912577 2058443 := bstep (se 1 (by rfl) ⟨1543832, by rfl⟩ : syracuseStep 2058443 = 3087665) B3087665
theorem B7432397 : Blo 912577 7432397 := bstep (se 3 (by rfl) ⟨1393574, by rfl⟩ : syracuseStep 7432397 = 2787149) B2787149
theorem B1370327 : Blo 912577 1370327 := bstep (se 1 (by rfl) ⟨1027745, by rfl⟩ : syracuseStep 1370327 = 2055491) B2055491
theorem B2058497 : Blo 912577 2058497 := bstep (se 2 (by rfl) ⟨771936, by rfl⟩ : syracuseStep 2058497 = 1543873) B1543873
theorem B1370393 : Blo 912577 1370393 := bstep (se 2 (by rfl) ⟨513897, by rfl⟩ : syracuseStep 1370393 = 1027795) B1027795
theorem B9890093 : Blo 912577 9890093 := bstep (se 3 (by rfl) ⟨1854392, by rfl⟩ : syracuseStep 9890093 = 3708785) B3708785
theorem B1370507 : Blo 912577 1370507 := bstep (se 1 (by rfl) ⟨1027880, by rfl⟩ : syracuseStep 1370507 = 2055761) B2055761
theorem B1370519 : Blo 912577 1370519 := bstep (se 1 (by rfl) ⟨1027889, by rfl⟩ : syracuseStep 1370519 = 2055779) B2055779
theorem B1370585 : Blo 912577 1370585 := bstep (se 2 (by rfl) ⟨513969, by rfl⟩ : syracuseStep 1370585 = 1027939) B1027939
theorem B2058713 : Blo 912577 2058713 := bstep (se 2 (by rfl) ⟨772017, by rfl⟩ : syracuseStep 2058713 = 1544035) B1544035
theorem B2058803 : Blo 912577 2058803 := bstep (se 1 (by rfl) ⟨1544102, by rfl⟩ : syracuseStep 2058803 = 3088205) B3088205
theorem B1370699 : Blo 912577 1370699 := bstep (se 1 (by rfl) ⟨1028024, by rfl⟩ : syracuseStep 1370699 = 2056049) B2056049
theorem B1370711 : Blo 912577 1370711 := bstep (se 1 (by rfl) ⟨1028033, by rfl⟩ : syracuseStep 1370711 = 2056067) B2056067
theorem B2058839 : Blo 912577 2058839 := bstep (se 1 (by rfl) ⟨1544129, by rfl⟩ : syracuseStep 2058839 = 3088259) B3088259
theorem B1370777 : Blo 912577 1370777 := bstep (se 2 (by rfl) ⟨514041, by rfl⟩ : syracuseStep 1370777 = 1028083) B1028083
theorem B3468035 : Blo 912577 3468035 := bstep (se 1 (by rfl) ⟨2601026, by rfl⟩ : syracuseStep 3468035 = 5202053) B5202053
theorem B1370891 : Blo 912577 1370891 := bstep (se 1 (by rfl) ⟨1028168, by rfl⟩ : syracuseStep 1370891 = 2056337) B2056337
theorem B2059019 : Blo 912577 2059019 := bstep (se 1 (by rfl) ⟨1544264, by rfl⟩ : syracuseStep 2059019 = 3088529) B3088529
theorem B1370903 : Blo 912577 1370903 := bstep (se 1 (by rfl) ⟨1028177, by rfl⟩ : syracuseStep 1370903 = 2056355) B2056355
theorem B2059073 : Blo 912577 2059073 := bstep (se 2 (by rfl) ⟨772152, by rfl⟩ : syracuseStep 2059073 = 1544305) B1544305
theorem B1502039 : Blo 912577 1502039 := bstep (se 1 (by rfl) ⟨1126529, by rfl⟩ : syracuseStep 1502039 = 2253059) B2253059
theorem B1370969 : Blo 912577 1370969 := bstep (se 2 (by rfl) ⟨514113, by rfl⟩ : syracuseStep 1370969 = 1028227) B1028227
theorem B3337163 : Blo 912577 3337163 := bstep (se 1 (by rfl) ⟨2502872, by rfl⟩ : syracuseStep 3337163 = 5005745) B5005745
theorem B1371083 : Blo 912577 1371083 := bstep (se 1 (by rfl) ⟨1028312, by rfl⟩ : syracuseStep 1371083 = 2056625) B2056625
theorem B1371095 : Blo 912577 1371095 := bstep (se 1 (by rfl) ⟨1028321, by rfl⟩ : syracuseStep 1371095 = 2056643) B2056643
theorem B1371161 : Blo 912577 1371161 := bstep (se 2 (by rfl) ⟨514185, by rfl⟩ : syracuseStep 1371161 = 1028371) B1028371
theorem B2059289 : Blo 912577 2059289 := bstep (se 2 (by rfl) ⟨772233, by rfl⟩ : syracuseStep 2059289 = 1544467) B1544467
theorem B2059379 : Blo 912577 2059379 := bstep (se 1 (by rfl) ⟨1544534, by rfl⟩ : syracuseStep 2059379 = 3089069) B3089069
theorem B1371275 : Blo 912577 1371275 := bstep (se 1 (by rfl) ⟨1028456, by rfl⟩ : syracuseStep 1371275 = 2056913) B2056913
theorem B1371287 : Blo 912577 1371287 := bstep (se 1 (by rfl) ⟨1028465, by rfl⟩ : syracuseStep 1371287 = 2056931) B2056931
theorem B2059415 : Blo 912577 2059415 := bstep (se 1 (by rfl) ⟨1544561, by rfl⟩ : syracuseStep 2059415 = 3089123) B3089123
theorem B912587 : Blo 912577 912587 := bstep (se 1 (by rfl) ⟨684440, by rfl⟩ : syracuseStep 912587 = 1368881) B1368881
theorem B3468491 : Blo 912577 3468491 := bstep (se 1 (by rfl) ⟨2601368, by rfl⟩ : syracuseStep 3468491 = 5202737) B5202737
theorem B912599 : Blo 912577 912599 := bstep (se 1 (by rfl) ⟨684449, by rfl⟩ : syracuseStep 912599 = 1368899) B1368899
theorem B1371353 : Blo 912577 1371353 := bstep (se 2 (by rfl) ⟨514257, by rfl⟩ : syracuseStep 1371353 = 1028515) B1028515
theorem B8350937 : Blo 912577 8350937 := bstep (se 2 (by rfl) ⟨3131601, by rfl⟩ : syracuseStep 8350937 = 6263203) B6263203
theorem B912619 : Blo 912577 912619 := bstep (se 1 (by rfl) ⟨684464, by rfl⟩ : syracuseStep 912619 = 1368929) B1368929
theorem B912631 : Blo 912577 912631 := bstep (se 1 (by rfl) ⟨684473, by rfl⟩ : syracuseStep 912631 = 1368947) B1368947
theorem B912651 : Blo 912577 912651 := bstep (se 1 (by rfl) ⟨684488, by rfl⟩ : syracuseStep 912651 = 1368977) B1368977
theorem B912663 : Blo 912577 912663 := bstep (se 1 (by rfl) ⟨684497, by rfl⟩ : syracuseStep 912663 = 1368995) B1368995
theorem B912683 : Blo 912577 912683 := bstep (se 1 (by rfl) ⟨684512, by rfl⟩ : syracuseStep 912683 = 1369025) B1369025
theorem B912695 : Blo 912577 912695 := bstep (se 1 (by rfl) ⟨684521, by rfl⟩ : syracuseStep 912695 = 1369043) B1369043
theorem B912715 : Blo 912577 912715 := bstep (se 1 (by rfl) ⟨684536, by rfl⟩ : syracuseStep 912715 = 1369073) B1369073
theorem B1371467 : Blo 912577 1371467 := bstep (se 1 (by rfl) ⟨1028600, by rfl⟩ : syracuseStep 1371467 = 2057201) B2057201
theorem B2059595 : Blo 912577 2059595 := bstep (se 1 (by rfl) ⟨1544696, by rfl⟩ : syracuseStep 2059595 = 3089393) B3089393
theorem B912727 : Blo 912577 912727 := bstep (se 1 (by rfl) ⟨684545, by rfl⟩ : syracuseStep 912727 = 1369091) B1369091
theorem B1371479 : Blo 912577 1371479 := bstep (se 1 (by rfl) ⟨1028609, by rfl⟩ : syracuseStep 1371479 = 2057219) B2057219
theorem B912747 : Blo 912577 912747 := bstep (se 1 (by rfl) ⟨684560, by rfl⟩ : syracuseStep 912747 = 1369121) B1369121
theorem B912759 : Blo 912577 912759 := bstep (se 1 (by rfl) ⟨684569, by rfl⟩ : syracuseStep 912759 = 1369139) B1369139
theorem B2059649 : Blo 912577 2059649 := bstep (se 2 (by rfl) ⟨772368, by rfl⟩ : syracuseStep 2059649 = 1544737) B1544737
theorem B912779 : Blo 912577 912779 := bstep (se 1 (by rfl) ⟨684584, by rfl⟩ : syracuseStep 912779 = 1369169) B1369169
theorem B3468689 : Blo 912577 3468689 := bstep (se 2 (by rfl) ⟨1300758, by rfl⟩ : syracuseStep 3468689 = 2601517) B2601517
theorem B912791 : Blo 912577 912791 := bstep (se 1 (by rfl) ⟨684593, by rfl⟩ : syracuseStep 912791 = 1369187) B1369187
theorem B1371545 : Blo 912577 1371545 := bstep (se 2 (by rfl) ⟨514329, by rfl⟩ : syracuseStep 1371545 = 1028659) B1028659
theorem B912811 : Blo 912577 912811 := bstep (se 1 (by rfl) ⟨684608, by rfl⟩ : syracuseStep 912811 = 1369217) B1369217
theorem B6254003 : Blo 912577 6254003 := bstep (se 1 (by rfl) ⟨4690502, by rfl⟩ : syracuseStep 6254003 = 9381005) B9381005
theorem B912823 : Blo 912577 912823 := bstep (se 1 (by rfl) ⟨684617, by rfl⟩ : syracuseStep 912823 = 1369235) B1369235
theorem B912843 : Blo 912577 912843 := bstep (se 1 (by rfl) ⟨684632, by rfl⟩ : syracuseStep 912843 = 1369265) B1369265
theorem B912855 : Blo 912577 912855 := bstep (se 1 (by rfl) ⟨684641, by rfl⟩ : syracuseStep 912855 = 1369283) B1369283
theorem B912875 : Blo 912577 912875 := bstep (se 1 (by rfl) ⟨684656, by rfl⟩ : syracuseStep 912875 = 1369313) B1369313
theorem B912887 : Blo 912577 912887 := bstep (se 1 (by rfl) ⟨684665, by rfl⟩ : syracuseStep 912887 = 1369331) B1369331
theorem B912907 : Blo 912577 912907 := bstep (se 1 (by rfl) ⟨684680, by rfl⟩ : syracuseStep 912907 = 1369361) B1369361
theorem B1371659 : Blo 912577 1371659 := bstep (se 1 (by rfl) ⟨1028744, by rfl⟩ : syracuseStep 1371659 = 2057489) B2057489
theorem B912919 : Blo 912577 912919 := bstep (se 1 (by rfl) ⟨684689, by rfl⟩ : syracuseStep 912919 = 1369379) B1369379
theorem B1371671 : Blo 912577 1371671 := bstep (se 1 (by rfl) ⟨1028753, by rfl⟩ : syracuseStep 1371671 = 2057507) B2057507
theorem B912939 : Blo 912577 912939 := bstep (se 1 (by rfl) ⟨684704, by rfl⟩ : syracuseStep 912939 = 1369409) B1369409
theorem B912951 : Blo 912577 912951 := bstep (se 1 (by rfl) ⟨684713, by rfl⟩ : syracuseStep 912951 = 1369427) B1369427
theorem B912971 : Blo 912577 912971 := bstep (se 1 (by rfl) ⟨684728, by rfl⟩ : syracuseStep 912971 = 1369457) B1369457
theorem B912983 : Blo 912577 912983 := bstep (se 1 (by rfl) ⟨684737, by rfl⟩ : syracuseStep 912983 = 1369475) B1369475
theorem B1371737 : Blo 912577 1371737 := bstep (se 2 (by rfl) ⟨514401, by rfl⟩ : syracuseStep 1371737 = 1028803) B1028803
theorem B2059865 : Blo 912577 2059865 := bstep (se 2 (by rfl) ⟨772449, by rfl⟩ : syracuseStep 2059865 = 1544899) B1544899
theorem B913003 : Blo 912577 913003 := bstep (se 1 (by rfl) ⟨684752, by rfl⟩ : syracuseStep 913003 = 1369505) B1369505
theorem B913015 : Blo 912577 913015 := bstep (se 1 (by rfl) ⟨684761, by rfl⟩ : syracuseStep 913015 = 1369523) B1369523
theorem B913035 : Blo 912577 913035 := bstep (se 1 (by rfl) ⟨684776, by rfl⟩ : syracuseStep 913035 = 1369553) B1369553
theorem B913047 : Blo 912577 913047 := bstep (se 1 (by rfl) ⟨684785, by rfl⟩ : syracuseStep 913047 = 1369571) B1369571
theorem B913067 : Blo 912577 913067 := bstep (se 1 (by rfl) ⟨684800, by rfl⟩ : syracuseStep 913067 = 1369601) B1369601
theorem B2059955 : Blo 912577 2059955 := bstep (se 1 (by rfl) ⟨1544966, by rfl⟩ : syracuseStep 2059955 = 3089933) B3089933
theorem B913079 : Blo 912577 913079 := bstep (se 1 (by rfl) ⟨684809, by rfl⟩ : syracuseStep 913079 = 1369619) B1369619
theorem B913099 : Blo 912577 913099 := bstep (se 1 (by rfl) ⟨684824, by rfl⟩ : syracuseStep 913099 = 1369649) B1369649
theorem B1371851 : Blo 912577 1371851 := bstep (se 1 (by rfl) ⟨1028888, by rfl⟩ : syracuseStep 1371851 = 2057777) B2057777
theorem B913111 : Blo 912577 913111 := bstep (se 1 (by rfl) ⟨684833, by rfl⟩ : syracuseStep 913111 = 1369667) B1369667
theorem B1371863 : Blo 912577 1371863 := bstep (se 1 (by rfl) ⟨1028897, by rfl⟩ : syracuseStep 1371863 = 2057795) B2057795
theorem B2059991 : Blo 912577 2059991 := bstep (se 1 (by rfl) ⟨1544993, by rfl⟩ : syracuseStep 2059991 = 3089987) B3089987
theorem B913131 : Blo 912577 913131 := bstep (se 1 (by rfl) ⟨684848, by rfl⟩ : syracuseStep 913131 = 1369697) B1369697
theorem B913143 : Blo 912577 913143 := bstep (se 1 (by rfl) ⟨684857, by rfl⟩ : syracuseStep 913143 = 1369715) B1369715
theorem B978679 : Blo 912577 978679 := bstep (se 1 (by rfl) ⟨734009, by rfl⟩ : syracuseStep 978679 = 1468019) B1468019
theorem B913163 : Blo 912577 913163 := bstep (se 1 (by rfl) ⟨684872, by rfl⟩ : syracuseStep 913163 = 1369745) B1369745
theorem B913175 : Blo 912577 913175 := bstep (se 1 (by rfl) ⟨684881, by rfl⟩ : syracuseStep 913175 = 1369763) B1369763
theorem B1371929 : Blo 912577 1371929 := bstep (se 2 (by rfl) ⟨514473, by rfl⟩ : syracuseStep 1371929 = 1028947) B1028947
theorem B913195 : Blo 912577 913195 := bstep (se 1 (by rfl) ⟨684896, by rfl⟩ : syracuseStep 913195 = 1369793) B1369793
theorem B6942509 : Blo 912577 6942509 := bstep (se 3 (by rfl) ⟨1301720, by rfl⟩ : syracuseStep 6942509 = 2603441) B2603441
theorem B913207 : Blo 912577 913207 := bstep (se 1 (by rfl) ⟨684905, by rfl⟩ : syracuseStep 913207 = 1369811) B1369811
theorem B913227 : Blo 912577 913227 := bstep (se 1 (by rfl) ⟨684920, by rfl⟩ : syracuseStep 913227 = 1369841) B1369841
theorem B913239 : Blo 912577 913239 := bstep (se 1 (by rfl) ⟨684929, by rfl⟩ : syracuseStep 913239 = 1369859) B1369859
theorem B913259 : Blo 912577 913259 := bstep (se 1 (by rfl) ⟨684944, by rfl⟩ : syracuseStep 913259 = 1369889) B1369889
theorem B913271 : Blo 912577 913271 := bstep (se 1 (by rfl) ⟨684953, by rfl⟩ : syracuseStep 913271 = 1369907) B1369907
theorem B913291 : Blo 912577 913291 := bstep (se 1 (by rfl) ⟨684968, by rfl⟩ : syracuseStep 913291 = 1369937) B1369937
theorem B1372043 : Blo 912577 1372043 := bstep (se 1 (by rfl) ⟨1029032, by rfl⟩ : syracuseStep 1372043 = 2058065) B2058065
theorem B2060171 : Blo 912577 2060171 := bstep (se 1 (by rfl) ⟨1545128, by rfl⟩ : syracuseStep 2060171 = 3090257) B3090257
theorem B913303 : Blo 912577 913303 := bstep (se 1 (by rfl) ⟨684977, by rfl⟩ : syracuseStep 913303 = 1369955) B1369955
theorem B1372055 : Blo 912577 1372055 := bstep (se 1 (by rfl) ⟨1029041, by rfl⟩ : syracuseStep 1372055 = 2058083) B2058083
theorem B913323 : Blo 912577 913323 := bstep (se 1 (by rfl) ⟨684992, by rfl⟩ : syracuseStep 913323 = 1369985) B1369985
theorem B913335 : Blo 912577 913335 := bstep (se 1 (by rfl) ⟨685001, by rfl⟩ : syracuseStep 913335 = 1370003) B1370003
theorem B2060225 : Blo 912577 2060225 := bstep (se 2 (by rfl) ⟨772584, by rfl⟩ : syracuseStep 2060225 = 1545169) B1545169
theorem B913355 : Blo 912577 913355 := bstep (se 1 (by rfl) ⟨685016, by rfl⟩ : syracuseStep 913355 = 1370033) B1370033
theorem B913367 : Blo 912577 913367 := bstep (se 1 (by rfl) ⟨685025, by rfl⟩ : syracuseStep 913367 = 1370051) B1370051
theorem B1372121 : Blo 912577 1372121 := bstep (se 2 (by rfl) ⟨514545, by rfl⟩ : syracuseStep 1372121 = 1029091) B1029091
theorem B913387 : Blo 912577 913387 := bstep (se 1 (by rfl) ⟨685040, by rfl⟩ : syracuseStep 913387 = 1370081) B1370081
theorem B913399 : Blo 912577 913399 := bstep (se 1 (by rfl) ⟨685049, by rfl⟩ : syracuseStep 913399 = 1370099) B1370099
theorem B913419 : Blo 912577 913419 := bstep (se 1 (by rfl) ⟨685064, by rfl⟩ : syracuseStep 913419 = 1370129) B1370129
theorem B913431 : Blo 912577 913431 := bstep (se 1 (by rfl) ⟨685073, by rfl⟩ : syracuseStep 913431 = 1370147) B1370147
theorem B913451 : Blo 912577 913451 := bstep (se 1 (by rfl) ⟨685088, by rfl⟩ : syracuseStep 913451 = 1370177) B1370177
theorem B1044523 : Blo 912577 1044523 := bstep (se 1 (by rfl) ⟨783392, by rfl⟩ : syracuseStep 1044523 = 1566785) B1566785
theorem B913463 : Blo 912577 913463 := bstep (se 1 (by rfl) ⟨685097, by rfl⟩ : syracuseStep 913463 = 1370195) B1370195
theorem B913483 : Blo 912577 913483 := bstep (se 1 (by rfl) ⟨685112, by rfl⟩ : syracuseStep 913483 = 1370225) B1370225
theorem B1372235 : Blo 912577 1372235 := bstep (se 1 (by rfl) ⟨1029176, by rfl⟩ : syracuseStep 1372235 = 2058353) B2058353
theorem B913495 : Blo 912577 913495 := bstep (se 1 (by rfl) ⟨685121, by rfl⟩ : syracuseStep 913495 = 1370243) B1370243
theorem B1372247 : Blo 912577 1372247 := bstep (se 1 (by rfl) ⟨1029185, by rfl⟩ : syracuseStep 1372247 = 2058371) B2058371
theorem B913515 : Blo 912577 913515 := bstep (se 1 (by rfl) ⟨685136, by rfl⟩ : syracuseStep 913515 = 1370273) B1370273
theorem B913527 : Blo 912577 913527 := bstep (se 1 (by rfl) ⟨685145, by rfl⟩ : syracuseStep 913527 = 1370291) B1370291
theorem B913547 : Blo 912577 913547 := bstep (se 1 (by rfl) ⟨685160, by rfl⟩ : syracuseStep 913547 = 1370321) B1370321
theorem B913559 : Blo 912577 913559 := bstep (se 1 (by rfl) ⟨685169, by rfl⟩ : syracuseStep 913559 = 1370339) B1370339
theorem B3469463 : Blo 912577 3469463 := bstep (se 1 (by rfl) ⟨2602097, by rfl⟩ : syracuseStep 3469463 = 5204195) B5204195
theorem B1372313 : Blo 912577 1372313 := bstep (se 2 (by rfl) ⟨514617, by rfl⟩ : syracuseStep 1372313 = 1029235) B1029235
theorem B2060441 : Blo 912577 2060441 := bstep (se 2 (by rfl) ⟨772665, by rfl⟩ : syracuseStep 2060441 = 1545331) B1545331
theorem B913579 : Blo 912577 913579 := bstep (se 1 (by rfl) ⟨685184, by rfl⟩ : syracuseStep 913579 = 1370369) B1370369
theorem B913591 : Blo 912577 913591 := bstep (se 1 (by rfl) ⟨685193, by rfl⟩ : syracuseStep 913591 = 1370387) B1370387
theorem B913611 : Blo 912577 913611 := bstep (se 1 (by rfl) ⟨685208, by rfl⟩ : syracuseStep 913611 = 1370417) B1370417
theorem B913623 : Blo 912577 913623 := bstep (se 1 (by rfl) ⟨685217, by rfl⟩ : syracuseStep 913623 = 1370435) B1370435
theorem B913643 : Blo 912577 913643 := bstep (se 1 (by rfl) ⟨685232, by rfl⟩ : syracuseStep 913643 = 1370465) B1370465
theorem B2060531 : Blo 912577 2060531 := bstep (se 1 (by rfl) ⟨1545398, by rfl⟩ : syracuseStep 2060531 = 3090797) B3090797
theorem B913655 : Blo 912577 913655 := bstep (se 1 (by rfl) ⟨685241, by rfl⟩ : syracuseStep 913655 = 1370483) B1370483
theorem B913675 : Blo 912577 913675 := bstep (se 1 (by rfl) ⟨685256, by rfl⟩ : syracuseStep 913675 = 1370513) B1370513
theorem B1372427 : Blo 912577 1372427 := bstep (se 1 (by rfl) ⟨1029320, by rfl⟩ : syracuseStep 1372427 = 2058641) B2058641
theorem B913687 : Blo 912577 913687 := bstep (se 1 (by rfl) ⟨685265, by rfl⟩ : syracuseStep 913687 = 1370531) B1370531
theorem B1372439 : Blo 912577 1372439 := bstep (se 1 (by rfl) ⟨1029329, by rfl⟩ : syracuseStep 1372439 = 2058659) B2058659
theorem B2060567 : Blo 912577 2060567 := bstep (se 1 (by rfl) ⟨1545425, by rfl⟩ : syracuseStep 2060567 = 3090851) B3090851
theorem B913707 : Blo 912577 913707 := bstep (se 1 (by rfl) ⟨685280, by rfl⟩ : syracuseStep 913707 = 1370561) B1370561
theorem B913719 : Blo 912577 913719 := bstep (se 1 (by rfl) ⟨685289, by rfl⟩ : syracuseStep 913719 = 1370579) B1370579
theorem B913739 : Blo 912577 913739 := bstep (se 1 (by rfl) ⟨685304, by rfl⟩ : syracuseStep 913739 = 1370609) B1370609
theorem B913751 : Blo 912577 913751 := bstep (se 1 (by rfl) ⟨685313, by rfl⟩ : syracuseStep 913751 = 1370627) B1370627
theorem B1372505 : Blo 912577 1372505 := bstep (se 2 (by rfl) ⟨514689, by rfl⟩ : syracuseStep 1372505 = 1029379) B1029379
theorem B3469661 : Blo 912577 3469661 := bstep (se 3 (by rfl) ⟨650561, by rfl⟩ : syracuseStep 3469661 = 1301123) B1301123
theorem B913771 : Blo 912577 913771 := bstep (se 1 (by rfl) ⟨685328, by rfl⟩ : syracuseStep 913771 = 1370657) B1370657
theorem B913783 : Blo 912577 913783 := bstep (se 1 (by rfl) ⟨685337, by rfl⟩ : syracuseStep 913783 = 1370675) B1370675
theorem B913803 : Blo 912577 913803 := bstep (se 1 (by rfl) ⟨685352, by rfl⟩ : syracuseStep 913803 = 1370705) B1370705
theorem B1733015 : Blo 912577 1733015 := bstep (se 1 (by rfl) ⟨1299761, by rfl⟩ : syracuseStep 1733015 = 2599523) B2599523
theorem B913815 : Blo 912577 913815 := bstep (se 1 (by rfl) ⟨685361, by rfl⟩ : syracuseStep 913815 = 1370723) B1370723
theorem B913835 : Blo 912577 913835 := bstep (se 1 (by rfl) ⟨685376, by rfl⟩ : syracuseStep 913835 = 1370753) B1370753
theorem B11891123 : Blo 912577 11891123 := bstep (se 1 (by rfl) ⟨8918342, by rfl⟩ : syracuseStep 11891123 = 17836685) B17836685
theorem B913847 : Blo 912577 913847 := bstep (se 1 (by rfl) ⟨685385, by rfl⟩ : syracuseStep 913847 = 1370771) B1370771
theorem B913867 : Blo 912577 913867 := bstep (se 1 (by rfl) ⟨685400, by rfl⟩ : syracuseStep 913867 = 1370801) B1370801
theorem B1372619 : Blo 912577 1372619 := bstep (se 1 (by rfl) ⟨1029464, by rfl⟩ : syracuseStep 1372619 = 2058929) B2058929
theorem B2060747 : Blo 912577 2060747 := bstep (se 1 (by rfl) ⟨1545560, by rfl⟩ : syracuseStep 2060747 = 3091121) B3091121
theorem B913879 : Blo 912577 913879 := bstep (se 1 (by rfl) ⟨685409, by rfl⟩ : syracuseStep 913879 = 1370819) B1370819
theorem B1372631 : Blo 912577 1372631 := bstep (se 1 (by rfl) ⟨1029473, by rfl⟩ : syracuseStep 1372631 = 2058947) B2058947
theorem B913899 : Blo 912577 913899 := bstep (se 1 (by rfl) ⟨685424, by rfl⟩ : syracuseStep 913899 = 1370849) B1370849
theorem B913911 : Blo 912577 913911 := bstep (se 1 (by rfl) ⟨685433, by rfl⟩ : syracuseStep 913911 = 1370867) B1370867
theorem B2060801 : Blo 912577 2060801 := bstep (se 2 (by rfl) ⟨772800, by rfl⟩ : syracuseStep 2060801 = 1545601) B1545601
theorem B913931 : Blo 912577 913931 := bstep (se 1 (by rfl) ⟨685448, by rfl⟩ : syracuseStep 913931 = 1370897) B1370897
theorem B913943 : Blo 912577 913943 := bstep (se 1 (by rfl) ⟨685457, by rfl⟩ : syracuseStep 913943 = 1370915) B1370915
theorem B1372697 : Blo 912577 1372697 := bstep (se 2 (by rfl) ⟨514761, by rfl⟩ : syracuseStep 1372697 = 1029523) B1029523
theorem B913963 : Blo 912577 913963 := bstep (se 1 (by rfl) ⟨685472, by rfl⟩ : syracuseStep 913963 = 1370945) B1370945
theorem B913975 : Blo 912577 913975 := bstep (se 1 (by rfl) ⟨685481, by rfl⟩ : syracuseStep 913975 = 1370963) B1370963
theorem B913995 : Blo 912577 913995 := bstep (se 1 (by rfl) ⟨685496, by rfl⟩ : syracuseStep 913995 = 1370993) B1370993
theorem B914007 : Blo 912577 914007 := bstep (se 1 (by rfl) ⟨685505, by rfl⟩ : syracuseStep 914007 = 1371011) B1371011
theorem B914027 : Blo 912577 914027 := bstep (se 1 (by rfl) ⟨685520, by rfl⟩ : syracuseStep 914027 = 1371041) B1371041
theorem B914039 : Blo 912577 914039 := bstep (se 1 (by rfl) ⟨685529, by rfl⟩ : syracuseStep 914039 = 1371059) B1371059
theorem B914059 : Blo 912577 914059 := bstep (se 1 (by rfl) ⟨685544, by rfl⟩ : syracuseStep 914059 = 1371089) B1371089
theorem B1372811 : Blo 912577 1372811 := bstep (se 1 (by rfl) ⟨1029608, by rfl⟩ : syracuseStep 1372811 = 2059217) B2059217
theorem B914071 : Blo 912577 914071 := bstep (se 1 (by rfl) ⟨685553, by rfl⟩ : syracuseStep 914071 = 1371107) B1371107
theorem B5206679 : Blo 912577 5206679 := bstep (se 1 (by rfl) ⟨3905009, by rfl⟩ : syracuseStep 5206679 = 7810019) B7810019
theorem B3568279 : Blo 912577 3568279 := bstep (se 1 (by rfl) ⟨2676209, by rfl⟩ : syracuseStep 3568279 = 5352419) B5352419
theorem B1372823 : Blo 912577 1372823 := bstep (se 1 (by rfl) ⟨1029617, by rfl⟩ : syracuseStep 1372823 = 2059235) B2059235
theorem B914091 : Blo 912577 914091 := bstep (se 1 (by rfl) ⟨685568, by rfl⟩ : syracuseStep 914091 = 1371137) B1371137
theorem B914103 : Blo 912577 914103 := bstep (se 1 (by rfl) ⟨685577, by rfl⟩ : syracuseStep 914103 = 1371155) B1371155
theorem B914123 : Blo 912577 914123 := bstep (se 1 (by rfl) ⟨685592, by rfl⟩ : syracuseStep 914123 = 1371185) B1371185
theorem B914135 : Blo 912577 914135 := bstep (se 1 (by rfl) ⟨685601, by rfl⟩ : syracuseStep 914135 = 1371203) B1371203
theorem B1372889 : Blo 912577 1372889 := bstep (se 2 (by rfl) ⟨514833, by rfl⟩ : syracuseStep 1372889 = 1029667) B1029667
theorem B2061017 : Blo 912577 2061017 := bstep (se 2 (by rfl) ⟨772881, by rfl⟩ : syracuseStep 2061017 = 1545763) B1545763
theorem B914155 : Blo 912577 914155 := bstep (se 1 (by rfl) ⟨685616, by rfl⟩ : syracuseStep 914155 = 1371233) B1371233
theorem B914167 : Blo 912577 914167 := bstep (se 1 (by rfl) ⟨685625, by rfl⟩ : syracuseStep 914167 = 1371251) B1371251
theorem B914187 : Blo 912577 914187 := bstep (se 1 (by rfl) ⟨685640, by rfl⟩ : syracuseStep 914187 = 1371281) B1371281
theorem B4387601 : Blo 912577 4387601 := bstep (se 2 (by rfl) ⟨1645350, by rfl⟩ : syracuseStep 4387601 = 3290701) B3290701
theorem B914199 : Blo 912577 914199 := bstep (se 1 (by rfl) ⟨685649, by rfl⟩ : syracuseStep 914199 = 1371299) B1371299
theorem B914219 : Blo 912577 914219 := bstep (se 1 (by rfl) ⟨685664, by rfl⟩ : syracuseStep 914219 = 1371329) B1371329
theorem B2061107 : Blo 912577 2061107 := bstep (se 1 (by rfl) ⟨1545830, by rfl⟩ : syracuseStep 2061107 = 3091661) B3091661
theorem B914231 : Blo 912577 914231 := bstep (se 1 (by rfl) ⟨685673, by rfl⟩ : syracuseStep 914231 = 1371347) B1371347
theorem B914251 : Blo 912577 914251 := bstep (se 1 (by rfl) ⟨685688, by rfl⟩ : syracuseStep 914251 = 1371377) B1371377
theorem B1373003 : Blo 912577 1373003 := bstep (se 1 (by rfl) ⟨1029752, by rfl⟩ : syracuseStep 1373003 = 2059505) B2059505
theorem B914263 : Blo 912577 914263 := bstep (se 1 (by rfl) ⟨685697, by rfl⟩ : syracuseStep 914263 = 1371395) B1371395
theorem B1373015 : Blo 912577 1373015 := bstep (se 1 (by rfl) ⟨1029761, by rfl⟩ : syracuseStep 1373015 = 2059523) B2059523
theorem B2061143 : Blo 912577 2061143 := bstep (se 1 (by rfl) ⟨1545857, by rfl⟩ : syracuseStep 2061143 = 3091715) B3091715
theorem B914283 : Blo 912577 914283 := bstep (se 1 (by rfl) ⟨685712, by rfl⟩ : syracuseStep 914283 = 1371425) B1371425
theorem B914295 : Blo 912577 914295 := bstep (se 1 (by rfl) ⟨685721, by rfl⟩ : syracuseStep 914295 = 1371443) B1371443
theorem B914315 : Blo 912577 914315 := bstep (se 1 (by rfl) ⟨685736, by rfl⟩ : syracuseStep 914315 = 1371473) B1371473
theorem B914327 : Blo 912577 914327 := bstep (se 1 (by rfl) ⟨685745, by rfl⟩ : syracuseStep 914327 = 1371491) B1371491
theorem B1373081 : Blo 912577 1373081 := bstep (se 2 (by rfl) ⟨514905, by rfl⟩ : syracuseStep 1373081 = 1029811) B1029811
theorem B914347 : Blo 912577 914347 := bstep (se 1 (by rfl) ⟨685760, by rfl⟩ : syracuseStep 914347 = 1371521) B1371521
theorem B1733555 : Blo 912577 1733555 := bstep (se 1 (by rfl) ⟨1300166, by rfl⟩ : syracuseStep 1733555 = 2600333) B2600333
theorem B914359 : Blo 912577 914359 := bstep (se 1 (by rfl) ⟨685769, by rfl⟩ : syracuseStep 914359 = 1371539) B1371539
theorem B914379 : Blo 912577 914379 := bstep (se 1 (by rfl) ⟨685784, by rfl⟩ : syracuseStep 914379 = 1371569) B1371569
theorem B914391 : Blo 912577 914391 := bstep (se 1 (by rfl) ⟨685793, by rfl⟩ : syracuseStep 914391 = 1371587) B1371587
theorem B914411 : Blo 912577 914411 := bstep (se 1 (by rfl) ⟨685808, by rfl⟩ : syracuseStep 914411 = 1371617) B1371617
theorem B914423 : Blo 912577 914423 := bstep (se 1 (by rfl) ⟨685817, by rfl⟩ : syracuseStep 914423 = 1371635) B1371635
theorem B914443 : Blo 912577 914443 := bstep (se 1 (by rfl) ⟨685832, by rfl⟩ : syracuseStep 914443 = 1371665) B1371665
theorem B1373195 : Blo 912577 1373195 := bstep (se 1 (by rfl) ⟨1029896, by rfl⟩ : syracuseStep 1373195 = 2059793) B2059793
theorem B2061323 : Blo 912577 2061323 := bstep (se 1 (by rfl) ⟨1545992, by rfl⟩ : syracuseStep 2061323 = 3091985) B3091985
theorem B914455 : Blo 912577 914455 := bstep (se 1 (by rfl) ⟨685841, by rfl⟩ : syracuseStep 914455 = 1371683) B1371683
theorem B1373207 : Blo 912577 1373207 := bstep (se 1 (by rfl) ⟨1029905, by rfl⟩ : syracuseStep 1373207 = 2059811) B2059811
theorem B914475 : Blo 912577 914475 := bstep (se 1 (by rfl) ⟨685856, by rfl⟩ : syracuseStep 914475 = 1371713) B1371713
theorem B914487 : Blo 912577 914487 := bstep (se 1 (by rfl) ⟨685865, by rfl⟩ : syracuseStep 914487 = 1371731) B1371731
theorem B2061377 : Blo 912577 2061377 := bstep (se 2 (by rfl) ⟨773016, by rfl⟩ : syracuseStep 2061377 = 1546033) B1546033
theorem B914507 : Blo 912577 914507 := bstep (se 1 (by rfl) ⟨685880, by rfl⟩ : syracuseStep 914507 = 1371761) B1371761
theorem B914519 : Blo 912577 914519 := bstep (se 1 (by rfl) ⟨685889, by rfl⟩ : syracuseStep 914519 = 1371779) B1371779
theorem B3339353 : Blo 912577 3339353 := bstep (se 2 (by rfl) ⟨1252257, by rfl⟩ : syracuseStep 3339353 = 2504515) B2504515
theorem B1373273 : Blo 912577 1373273 := bstep (se 2 (by rfl) ⟨514977, by rfl⟩ : syracuseStep 1373273 = 1029955) B1029955
theorem B914539 : Blo 912577 914539 := bstep (se 1 (by rfl) ⟨685904, by rfl⟩ : syracuseStep 914539 = 1371809) B1371809
theorem B914551 : Blo 912577 914551 := bstep (se 1 (by rfl) ⟨685913, by rfl⟩ : syracuseStep 914551 = 1371827) B1371827
theorem B914571 : Blo 912577 914571 := bstep (se 1 (by rfl) ⟨685928, by rfl⟩ : syracuseStep 914571 = 1371857) B1371857
theorem B914583 : Blo 912577 914583 := bstep (se 1 (by rfl) ⟨685937, by rfl⟩ : syracuseStep 914583 = 1371875) B1371875
theorem B914603 : Blo 912577 914603 := bstep (se 1 (by rfl) ⟨685952, by rfl⟩ : syracuseStep 914603 = 1371905) B1371905
theorem B914615 : Blo 912577 914615 := bstep (se 1 (by rfl) ⟨685961, by rfl⟩ : syracuseStep 914615 = 1371923) B1371923
theorem B914635 : Blo 912577 914635 := bstep (se 1 (by rfl) ⟨685976, by rfl⟩ : syracuseStep 914635 = 1371953) B1371953
theorem B1373387 : Blo 912577 1373387 := bstep (se 1 (by rfl) ⟨1030040, by rfl⟩ : syracuseStep 1373387 = 2060081) B2060081
theorem B914647 : Blo 912577 914647 := bstep (se 1 (by rfl) ⟨685985, by rfl⟩ : syracuseStep 914647 = 1371971) B1371971
theorem B1373399 : Blo 912577 1373399 := bstep (se 1 (by rfl) ⟨1030049, by rfl⟩ : syracuseStep 1373399 = 2060099) B2060099
theorem B914667 : Blo 912577 914667 := bstep (se 1 (by rfl) ⟨686000, by rfl⟩ : syracuseStep 914667 = 1372001) B1372001
theorem B914679 : Blo 912577 914679 := bstep (se 1 (by rfl) ⟨686009, by rfl⟩ : syracuseStep 914679 = 1372019) B1372019
theorem B914699 : Blo 912577 914699 := bstep (se 1 (by rfl) ⟨686024, by rfl⟩ : syracuseStep 914699 = 1372049) B1372049
theorem B914711 : Blo 912577 914711 := bstep (se 1 (by rfl) ⟨686033, by rfl⟩ : syracuseStep 914711 = 1372067) B1372067
theorem B1373465 : Blo 912577 1373465 := bstep (se 2 (by rfl) ⟨515049, by rfl⟩ : syracuseStep 1373465 = 1030099) B1030099
theorem B2061593 : Blo 912577 2061593 := bstep (se 2 (by rfl) ⟨773097, by rfl⟩ : syracuseStep 2061593 = 1546195) B1546195
theorem B914731 : Blo 912577 914731 := bstep (se 1 (by rfl) ⟨686048, by rfl⟩ : syracuseStep 914731 = 1372097) B1372097
theorem B914743 : Blo 912577 914743 := bstep (se 1 (by rfl) ⟨686057, by rfl⟩ : syracuseStep 914743 = 1372115) B1372115
theorem B914763 : Blo 912577 914763 := bstep (se 1 (by rfl) ⟨686072, by rfl⟩ : syracuseStep 914763 = 1372145) B1372145
theorem B914775 : Blo 912577 914775 := bstep (se 1 (by rfl) ⟨686081, by rfl⟩ : syracuseStep 914775 = 1372163) B1372163
theorem B914795 : Blo 912577 914795 := bstep (se 1 (by rfl) ⟨686096, by rfl⟩ : syracuseStep 914795 = 1372193) B1372193
theorem B2061683 : Blo 912577 2061683 := bstep (se 1 (by rfl) ⟨1546262, by rfl⟩ : syracuseStep 2061683 = 3092525) B3092525
theorem B914807 : Blo 912577 914807 := bstep (se 1 (by rfl) ⟨686105, by rfl⟩ : syracuseStep 914807 = 1372211) B1372211
theorem B914827 : Blo 912577 914827 := bstep (se 1 (by rfl) ⟨686120, by rfl⟩ : syracuseStep 914827 = 1372241) B1372241
theorem B1373579 : Blo 912577 1373579 := bstep (se 1 (by rfl) ⟨1030184, by rfl⟩ : syracuseStep 1373579 = 2060369) B2060369
theorem B914839 : Blo 912577 914839 := bstep (se 1 (by rfl) ⟨686129, by rfl⟩ : syracuseStep 914839 = 1372259) B1372259
theorem B1373591 : Blo 912577 1373591 := bstep (se 1 (by rfl) ⟨1030193, by rfl⟩ : syracuseStep 1373591 = 2060387) B2060387
theorem B1734041 : Blo 912577 1734041 := bstep (se 2 (by rfl) ⟨650265, by rfl⟩ : syracuseStep 1734041 = 1300531) B1300531
theorem B2061719 : Blo 912577 2061719 := bstep (se 1 (by rfl) ⟨1546289, by rfl⟩ : syracuseStep 2061719 = 3092579) B3092579
theorem B914859 : Blo 912577 914859 := bstep (se 1 (by rfl) ⟨686144, by rfl⟩ : syracuseStep 914859 = 1372289) B1372289
theorem B7828913 : Blo 912577 7828913 := bstep (se 2 (by rfl) ⟨2935842, by rfl⟩ : syracuseStep 7828913 = 5871685) B5871685
theorem B914871 : Blo 912577 914871 := bstep (se 1 (by rfl) ⟨686153, by rfl⟩ : syracuseStep 914871 = 1372307) B1372307
theorem B914891 : Blo 912577 914891 := bstep (se 1 (by rfl) ⟨686168, by rfl⟩ : syracuseStep 914891 = 1372337) B1372337
theorem B914903 : Blo 912577 914903 := bstep (se 1 (by rfl) ⟨686177, by rfl⟩ : syracuseStep 914903 = 1372355) B1372355
theorem B1373657 : Blo 912577 1373657 := bstep (se 2 (by rfl) ⟨515121, by rfl⟩ : syracuseStep 1373657 = 1030243) B1030243
theorem B914923 : Blo 912577 914923 := bstep (se 1 (by rfl) ⟨686192, by rfl⟩ : syracuseStep 914923 = 1372385) B1372385
theorem B914935 : Blo 912577 914935 := bstep (se 1 (by rfl) ⟨686201, by rfl⟩ : syracuseStep 914935 = 1372403) B1372403
theorem B914955 : Blo 912577 914955 := bstep (se 1 (by rfl) ⟨686216, by rfl⟩ : syracuseStep 914955 = 1372433) B1372433
theorem B914967 : Blo 912577 914967 := bstep (se 1 (by rfl) ⟨686225, by rfl⟩ : syracuseStep 914967 = 1372451) B1372451
theorem B914987 : Blo 912577 914987 := bstep (se 1 (by rfl) ⟨686240, by rfl⟩ : syracuseStep 914987 = 1372481) B1372481
theorem B914999 : Blo 912577 914999 := bstep (se 1 (by rfl) ⟨686249, by rfl⟩ : syracuseStep 914999 = 1372499) B1372499
theorem B915019 : Blo 912577 915019 := bstep (se 1 (by rfl) ⟨686264, by rfl⟩ : syracuseStep 915019 = 1372529) B1372529
theorem B1373771 : Blo 912577 1373771 := bstep (se 1 (by rfl) ⟨1030328, by rfl⟩ : syracuseStep 1373771 = 2060657) B2060657
theorem B2061899 : Blo 912577 2061899 := bstep (se 1 (by rfl) ⟨1546424, by rfl⟩ : syracuseStep 2061899 = 3092849) B3092849
theorem B915031 : Blo 912577 915031 := bstep (se 1 (by rfl) ⟨686273, by rfl⟩ : syracuseStep 915031 = 1372547) B1372547
theorem B1373783 : Blo 912577 1373783 := bstep (se 1 (by rfl) ⟨1030337, by rfl⟩ : syracuseStep 1373783 = 2060675) B2060675
theorem B10024541 : Blo 912577 10024541 := bstep (se 3 (by rfl) ⟨1879601, by rfl⟩ : syracuseStep 10024541 = 3759203) B3759203
theorem B915051 : Blo 912577 915051 := bstep (se 1 (by rfl) ⟨686288, by rfl⟩ : syracuseStep 915051 = 1372577) B1372577
theorem B915063 : Blo 912577 915063 := bstep (se 1 (by rfl) ⟨686297, by rfl⟩ : syracuseStep 915063 = 1372595) B1372595
theorem B2061953 : Blo 912577 2061953 := bstep (se 2 (by rfl) ⟨773232, by rfl⟩ : syracuseStep 2061953 = 1546465) B1546465
theorem B915083 : Blo 912577 915083 := bstep (se 1 (by rfl) ⟨686312, by rfl⟩ : syracuseStep 915083 = 1372625) B1372625
theorem B915095 : Blo 912577 915095 := bstep (se 1 (by rfl) ⟨686321, by rfl⟩ : syracuseStep 915095 = 1372643) B1372643
theorem B1373849 : Blo 912577 1373849 := bstep (se 2 (by rfl) ⟨515193, by rfl⟩ : syracuseStep 1373849 = 1030387) B1030387
theorem B915115 : Blo 912577 915115 := bstep (se 1 (by rfl) ⟨686336, by rfl⟩ : syracuseStep 915115 = 1372673) B1372673
theorem B915127 : Blo 912577 915127 := bstep (se 1 (by rfl) ⟨686345, by rfl⟩ : syracuseStep 915127 = 1372691) B1372691
theorem B915147 : Blo 912577 915147 := bstep (se 1 (by rfl) ⟨686360, by rfl⟩ : syracuseStep 915147 = 1372721) B1372721
theorem B915159 : Blo 912577 915159 := bstep (se 1 (by rfl) ⟨686369, by rfl⟩ : syracuseStep 915159 = 1372739) B1372739
theorem B915179 : Blo 912577 915179 := bstep (se 1 (by rfl) ⟨686384, by rfl⟩ : syracuseStep 915179 = 1372769) B1372769
theorem B915191 : Blo 912577 915191 := bstep (se 1 (by rfl) ⟨686393, by rfl⟩ : syracuseStep 915191 = 1372787) B1372787
theorem B915211 : Blo 912577 915211 := bstep (se 1 (by rfl) ⟨686408, by rfl⟩ : syracuseStep 915211 = 1372817) B1372817
theorem B1373963 : Blo 912577 1373963 := bstep (se 1 (by rfl) ⟨1030472, by rfl⟩ : syracuseStep 1373963 = 2060945) B2060945
theorem B915223 : Blo 912577 915223 := bstep (se 1 (by rfl) ⟨686417, by rfl⟩ : syracuseStep 915223 = 1372835) B1372835
theorem B1373975 : Blo 912577 1373975 := bstep (se 1 (by rfl) ⟨1030481, by rfl⟩ : syracuseStep 1373975 = 2060963) B2060963
theorem B915243 : Blo 912577 915243 := bstep (se 1 (by rfl) ⟨686432, by rfl⟩ : syracuseStep 915243 = 1372865) B1372865
theorem B915255 : Blo 912577 915255 := bstep (se 1 (by rfl) ⟨686441, by rfl⟩ : syracuseStep 915255 = 1372883) B1372883
theorem B915275 : Blo 912577 915275 := bstep (se 1 (by rfl) ⟨686456, by rfl⟩ : syracuseStep 915275 = 1372913) B1372913
theorem B915287 : Blo 912577 915287 := bstep (se 1 (by rfl) ⟨686465, by rfl⟩ : syracuseStep 915287 = 1372931) B1372931
theorem B1374041 : Blo 912577 1374041 := bstep (se 2 (by rfl) ⟨515265, by rfl⟩ : syracuseStep 1374041 = 1030531) B1030531
theorem B2062169 : Blo 912577 2062169 := bstep (se 2 (by rfl) ⟨773313, by rfl⟩ : syracuseStep 2062169 = 1546627) B1546627
theorem B915307 : Blo 912577 915307 := bstep (se 1 (by rfl) ⟨686480, by rfl⟩ : syracuseStep 915307 = 1372961) B1372961
theorem B915319 : Blo 912577 915319 := bstep (se 1 (by rfl) ⟨686489, by rfl⟩ : syracuseStep 915319 = 1372979) B1372979
theorem B915339 : Blo 912577 915339 := bstep (se 1 (by rfl) ⟨686504, by rfl⟩ : syracuseStep 915339 = 1373009) B1373009
theorem B915351 : Blo 912577 915351 := bstep (se 1 (by rfl) ⟨686513, by rfl⟩ : syracuseStep 915351 = 1373027) B1373027
theorem B915371 : Blo 912577 915371 := bstep (se 1 (by rfl) ⟨686528, by rfl⟩ : syracuseStep 915371 = 1373057) B1373057
theorem B8779697 : Blo 912577 8779697 := bstep (se 2 (by rfl) ⟨3292386, by rfl⟩ : syracuseStep 8779697 = 6584773) B6584773
theorem B2062259 : Blo 912577 2062259 := bstep (se 1 (by rfl) ⟨1546694, by rfl⟩ : syracuseStep 2062259 = 3093389) B3093389
theorem B915383 : Blo 912577 915383 := bstep (se 1 (by rfl) ⟨686537, by rfl⟩ : syracuseStep 915383 = 1373075) B1373075
theorem B915403 : Blo 912577 915403 := bstep (se 1 (by rfl) ⟨686552, by rfl⟩ : syracuseStep 915403 = 1373105) B1373105
theorem B1374155 : Blo 912577 1374155 := bstep (se 1 (by rfl) ⟨1030616, by rfl⟩ : syracuseStep 1374155 = 2061233) B2061233
theorem B915415 : Blo 912577 915415 := bstep (se 1 (by rfl) ⟨686561, by rfl⟩ : syracuseStep 915415 = 1373123) B1373123
theorem B1374167 : Blo 912577 1374167 := bstep (se 1 (by rfl) ⟨1030625, by rfl⟩ : syracuseStep 1374167 = 2061251) B2061251
theorem B2062295 : Blo 912577 2062295 := bstep (se 1 (by rfl) ⟨1546721, by rfl⟩ : syracuseStep 2062295 = 3093443) B3093443
theorem B915435 : Blo 912577 915435 := bstep (se 1 (by rfl) ⟨686576, by rfl⟩ : syracuseStep 915435 = 1373153) B1373153
theorem B915447 : Blo 912577 915447 := bstep (se 1 (by rfl) ⟨686585, by rfl⟩ : syracuseStep 915447 = 1373171) B1373171
theorem B915467 : Blo 912577 915467 := bstep (se 1 (by rfl) ⟨686600, by rfl⟩ : syracuseStep 915467 = 1373201) B1373201
theorem B15628301 : Blo 912577 15628301 := bstep (se 3 (by rfl) ⟨2930306, by rfl⟩ : syracuseStep 15628301 = 5860613) B5860613
theorem B15267857 : Blo 912577 15267857 := bstep (se 2 (by rfl) ⟨5725446, by rfl⟩ : syracuseStep 15267857 = 11450893) B11450893
theorem B915479 : Blo 912577 915479 := bstep (se 1 (by rfl) ⟨686609, by rfl⟩ : syracuseStep 915479 = 1373219) B1373219
theorem B1374233 : Blo 912577 1374233 := bstep (se 2 (by rfl) ⟨515337, by rfl⟩ : syracuseStep 1374233 = 1030675) B1030675
theorem B915499 : Blo 912577 915499 := bstep (se 1 (by rfl) ⟨686624, by rfl⟩ : syracuseStep 915499 = 1373249) B1373249
theorem B915511 : Blo 912577 915511 := bstep (se 1 (by rfl) ⟨686633, by rfl⟩ : syracuseStep 915511 = 1373267) B1373267
theorem B915531 : Blo 912577 915531 := bstep (se 1 (by rfl) ⟨686648, by rfl⟩ : syracuseStep 915531 = 1373297) B1373297
theorem B915543 : Blo 912577 915543 := bstep (se 1 (by rfl) ⟨686657, by rfl⟩ : syracuseStep 915543 = 1373315) B1373315
theorem B915563 : Blo 912577 915563 := bstep (se 1 (by rfl) ⟨686672, by rfl⟩ : syracuseStep 915563 = 1373345) B1373345
theorem B915575 : Blo 912577 915575 := bstep (se 1 (by rfl) ⟨686681, by rfl⟩ : syracuseStep 915575 = 1373363) B1373363
theorem B915595 : Blo 912577 915595 := bstep (se 1 (by rfl) ⟨686696, by rfl⟩ : syracuseStep 915595 = 1373393) B1373393
theorem B1374347 : Blo 912577 1374347 := bstep (se 1 (by rfl) ⟨1030760, by rfl⟩ : syracuseStep 1374347 = 2061521) B2061521
theorem B915607 : Blo 912577 915607 := bstep (se 1 (by rfl) ⟨686705, by rfl⟩ : syracuseStep 915607 = 1373411) B1373411
theorem B1374359 : Blo 912577 1374359 := bstep (se 1 (by rfl) ⟨1030769, by rfl⟩ : syracuseStep 1374359 = 2061539) B2061539
theorem B915627 : Blo 912577 915627 := bstep (se 1 (by rfl) ⟨686720, by rfl⟩ : syracuseStep 915627 = 1373441) B1373441
theorem B915639 : Blo 912577 915639 := bstep (se 1 (by rfl) ⟨686729, by rfl⟩ : syracuseStep 915639 = 1373459) B1373459
theorem B2259137 : Blo 912577 2259137 := bstep (se 2 (by rfl) ⟨847176, by rfl⟩ : syracuseStep 2259137 = 1694353) B1694353
theorem B915659 : Blo 912577 915659 := bstep (se 1 (by rfl) ⟨686744, by rfl⟩ : syracuseStep 915659 = 1373489) B1373489
theorem B915671 : Blo 912577 915671 := bstep (se 1 (by rfl) ⟨686753, by rfl⟩ : syracuseStep 915671 = 1373507) B1373507
theorem B1374425 : Blo 912577 1374425 := bstep (se 2 (by rfl) ⟨515409, by rfl⟩ : syracuseStep 1374425 = 1030819) B1030819
theorem B915691 : Blo 912577 915691 := bstep (se 1 (by rfl) ⟨686768, by rfl⟩ : syracuseStep 915691 = 1373537) B1373537
theorem B915703 : Blo 912577 915703 := bstep (se 1 (by rfl) ⟨686777, by rfl⟩ : syracuseStep 915703 = 1373555) B1373555
theorem B3471619 : Blo 912577 3471619 := bstep (se 1 (by rfl) ⟨2603714, by rfl⟩ : syracuseStep 3471619 = 5207429) B5207429
theorem B915723 : Blo 912577 915723 := bstep (se 1 (by rfl) ⟨686792, by rfl⟩ : syracuseStep 915723 = 1373585) B1373585
theorem B915735 : Blo 912577 915735 := bstep (se 1 (by rfl) ⟨686801, by rfl⟩ : syracuseStep 915735 = 1373603) B1373603
theorem B915755 : Blo 912577 915755 := bstep (se 1 (by rfl) ⟨686816, by rfl⟩ : syracuseStep 915755 = 1373633) B1373633
theorem B19757357 : Blo 912577 19757357 := bstep (se 3 (by rfl) ⟨3704504, by rfl⟩ : syracuseStep 19757357 = 7409009) B7409009
theorem B915767 : Blo 912577 915767 := bstep (se 1 (by rfl) ⟨686825, by rfl⟩ : syracuseStep 915767 = 1373651) B1373651
theorem B915787 : Blo 912577 915787 := bstep (se 1 (by rfl) ⟨686840, by rfl⟩ : syracuseStep 915787 = 1373681) B1373681
theorem B1374539 : Blo 912577 1374539 := bstep (se 1 (by rfl) ⟨1030904, by rfl⟩ : syracuseStep 1374539 = 2061809) B2061809
theorem B915799 : Blo 912577 915799 := bstep (se 1 (by rfl) ⟨686849, by rfl⟩ : syracuseStep 915799 = 1373699) B1373699
theorem B1374551 : Blo 912577 1374551 := bstep (se 1 (by rfl) ⟨1030913, by rfl⟩ : syracuseStep 1374551 = 2061827) B2061827
theorem B915819 : Blo 912577 915819 := bstep (se 1 (by rfl) ⟨686864, by rfl⟩ : syracuseStep 915819 = 1373729) B1373729
theorem B915831 : Blo 912577 915831 := bstep (se 1 (by rfl) ⟨686873, by rfl⟩ : syracuseStep 915831 = 1373747) B1373747
theorem B915851 : Blo 912577 915851 := bstep (se 1 (by rfl) ⟨686888, by rfl⟩ : syracuseStep 915851 = 1373777) B1373777
theorem B915863 : Blo 912577 915863 := bstep (se 1 (by rfl) ⟨686897, by rfl⟩ : syracuseStep 915863 = 1373795) B1373795
theorem B1374617 : Blo 912577 1374617 := bstep (se 2 (by rfl) ⟨515481, by rfl⟩ : syracuseStep 1374617 = 1030963) B1030963
theorem B915883 : Blo 912577 915883 := bstep (se 1 (by rfl) ⟨686912, by rfl⟩ : syracuseStep 915883 = 1373825) B1373825
theorem B915895 : Blo 912577 915895 := bstep (se 1 (by rfl) ⟨686921, by rfl⟩ : syracuseStep 915895 = 1373843) B1373843
theorem B915915 : Blo 912577 915915 := bstep (se 1 (by rfl) ⟨686936, by rfl⟩ : syracuseStep 915915 = 1373873) B1373873
theorem B915927 : Blo 912577 915927 := bstep (se 1 (by rfl) ⟨686945, by rfl⟩ : syracuseStep 915927 = 1373891) B1373891
theorem B915947 : Blo 912577 915947 := bstep (se 1 (by rfl) ⟨686960, by rfl⟩ : syracuseStep 915947 = 1373921) B1373921
theorem B915959 : Blo 912577 915959 := bstep (se 1 (by rfl) ⟨686969, by rfl⟩ : syracuseStep 915959 = 1373939) B1373939
theorem B915979 : Blo 912577 915979 := bstep (se 1 (by rfl) ⟨686984, by rfl⟩ : syracuseStep 915979 = 1373969) B1373969
theorem B1374731 : Blo 912577 1374731 := bstep (se 1 (by rfl) ⟨1031048, by rfl⟩ : syracuseStep 1374731 = 2062097) B2062097
theorem B915991 : Blo 912577 915991 := bstep (se 1 (by rfl) ⟨686993, by rfl⟩ : syracuseStep 915991 = 1373987) B1373987
theorem B1374743 : Blo 912577 1374743 := bstep (se 1 (by rfl) ⟨1031057, by rfl⟩ : syracuseStep 1374743 = 2062115) B2062115
theorem B916011 : Blo 912577 916011 := bstep (se 1 (by rfl) ⟨687008, by rfl⟩ : syracuseStep 916011 = 1374017) B1374017
theorem B3471923 : Blo 912577 3471923 := bstep (se 1 (by rfl) ⟨2603942, by rfl⟩ : syracuseStep 3471923 = 5207885) B5207885
theorem B916023 : Blo 912577 916023 := bstep (se 1 (by rfl) ⟨687017, by rfl⟩ : syracuseStep 916023 = 1374035) B1374035
theorem B916043 : Blo 912577 916043 := bstep (se 1 (by rfl) ⟨687032, by rfl⟩ : syracuseStep 916043 = 1374065) B1374065
theorem B916055 : Blo 912577 916055 := bstep (se 1 (by rfl) ⟨687041, by rfl⟩ : syracuseStep 916055 = 1374083) B1374083
theorem B1374809 : Blo 912577 1374809 := bstep (se 2 (by rfl) ⟨515553, by rfl⟩ : syracuseStep 1374809 = 1031107) B1031107
theorem B916075 : Blo 912577 916075 := bstep (se 1 (by rfl) ⟨687056, by rfl⟩ : syracuseStep 916075 = 1374113) B1374113
theorem B916087 : Blo 912577 916087 := bstep (se 1 (by rfl) ⟨687065, by rfl⟩ : syracuseStep 916087 = 1374131) B1374131
theorem B916107 : Blo 912577 916107 := bstep (se 1 (by rfl) ⟨687080, by rfl⟩ : syracuseStep 916107 = 1374161) B1374161
theorem B916119 : Blo 912577 916119 := bstep (se 1 (by rfl) ⟨687089, by rfl⟩ : syracuseStep 916119 = 1374179) B1374179
theorem B916139 : Blo 912577 916139 := bstep (se 1 (by rfl) ⟨687104, by rfl⟩ : syracuseStep 916139 = 1374209) B1374209
theorem B916151 : Blo 912577 916151 := bstep (se 1 (by rfl) ⟨687113, by rfl⟩ : syracuseStep 916151 = 1374227) B1374227
theorem B916171 : Blo 912577 916171 := bstep (se 1 (by rfl) ⟨687128, by rfl⟩ : syracuseStep 916171 = 1374257) B1374257
theorem B916183 : Blo 912577 916183 := bstep (se 1 (by rfl) ⟨687137, by rfl⟩ : syracuseStep 916183 = 1374275) B1374275
theorem B916203 : Blo 912577 916203 := bstep (se 1 (by rfl) ⟨687152, by rfl⟩ : syracuseStep 916203 = 1374305) B1374305
theorem B916215 : Blo 912577 916215 := bstep (se 1 (by rfl) ⟨687161, by rfl⟩ : syracuseStep 916215 = 1374323) B1374323
theorem B916235 : Blo 912577 916235 := bstep (se 1 (by rfl) ⟨687176, by rfl⟩ : syracuseStep 916235 = 1374353) B1374353
theorem B916247 : Blo 912577 916247 := bstep (se 1 (by rfl) ⟨687185, by rfl⟩ : syracuseStep 916247 = 1374371) B1374371
theorem B916267 : Blo 912577 916267 := bstep (se 1 (by rfl) ⟨687200, by rfl⟩ : syracuseStep 916267 = 1374401) B1374401
theorem B916279 : Blo 912577 916279 := bstep (se 1 (by rfl) ⟨687209, by rfl⟩ : syracuseStep 916279 = 1374419) B1374419
theorem B1735499 : Blo 912577 1735499 := bstep (se 1 (by rfl) ⟨1301624, by rfl⟩ : syracuseStep 1735499 = 2603249) B2603249
theorem B916299 : Blo 912577 916299 := bstep (se 1 (by rfl) ⟨687224, by rfl⟩ : syracuseStep 916299 = 1374449) B1374449
theorem B916311 : Blo 912577 916311 := bstep (se 1 (by rfl) ⟨687233, by rfl⟩ : syracuseStep 916311 = 1374467) B1374467
theorem B916331 : Blo 912577 916331 := bstep (se 1 (by rfl) ⟨687248, by rfl⟩ : syracuseStep 916331 = 1374497) B1374497
theorem B916343 : Blo 912577 916343 := bstep (se 1 (by rfl) ⟨687257, by rfl⟩ : syracuseStep 916343 = 1374515) B1374515
theorem B916363 : Blo 912577 916363 := bstep (se 1 (by rfl) ⟨687272, by rfl⟩ : syracuseStep 916363 = 1374545) B1374545
theorem B916375 : Blo 912577 916375 := bstep (se 1 (by rfl) ⟨687281, by rfl⟩ : syracuseStep 916375 = 1374563) B1374563
theorem B916395 : Blo 912577 916395 := bstep (se 1 (by rfl) ⟨687296, by rfl⟩ : syracuseStep 916395 = 1374593) B1374593
theorem B916407 : Blo 912577 916407 := bstep (se 1 (by rfl) ⟨687305, by rfl⟩ : syracuseStep 916407 = 1374611) B1374611
theorem B916427 : Blo 912577 916427 := bstep (se 1 (by rfl) ⟨687320, by rfl⟩ : syracuseStep 916427 = 1374641) B1374641
theorem B916439 : Blo 912577 916439 := bstep (se 1 (by rfl) ⟨687329, by rfl⟩ : syracuseStep 916439 = 1374659) B1374659
theorem B916459 : Blo 912577 916459 := bstep (se 1 (by rfl) ⟨687344, by rfl⟩ : syracuseStep 916459 = 1374689) B1374689
theorem B916471 : Blo 912577 916471 := bstep (se 1 (by rfl) ⟨687353, by rfl⟩ : syracuseStep 916471 = 1374707) B1374707
theorem B1735681 : Blo 912577 1735681 := bstep (se 2 (by rfl) ⟨650880, by rfl⟩ : syracuseStep 1735681 = 1301761) B1301761
theorem B916491 : Blo 912577 916491 := bstep (se 1 (by rfl) ⟨687368, by rfl⟩ : syracuseStep 916491 = 1374737) B1374737
theorem B916503 : Blo 912577 916503 := bstep (se 1 (by rfl) ⟨687377, by rfl⟩ : syracuseStep 916503 = 1374755) B1374755
theorem B916523 : Blo 912577 916523 := bstep (se 1 (by rfl) ⟨687392, by rfl⟩ : syracuseStep 916523 = 1374785) B1374785
theorem B916535 : Blo 912577 916535 := bstep (se 1 (by rfl) ⟨687401, by rfl⟩ : syracuseStep 916535 = 1374803) B1374803
theorem B916555 : Blo 912577 916555 := bstep (se 1 (by rfl) ⟨687416, by rfl⟩ : syracuseStep 916555 = 1374833) B1374833
theorem B916567 : Blo 912577 916567 := bstep (se 1 (by rfl) ⟨687425, by rfl⟩ : syracuseStep 916567 = 1374851) B1374851
theorem B7404695 : Blo 912577 7404695 := bstep (se 1 (by rfl) ⟨5553521, by rfl⟩ : syracuseStep 7404695 = 11107043) B11107043
theorem B3472577 : Blo 912577 3472577 := bstep (se 2 (by rfl) ⟨1302216, by rfl⟩ : syracuseStep 3472577 = 2604433) B2604433
theorem B2784473 : Blo 912577 2784473 := bstep (se 2 (by rfl) ⟨1044177, by rfl⟩ : syracuseStep 2784473 = 2088355) B2088355
theorem B1736129 : Blo 912577 1736129 := bstep (se 2 (by rfl) ⟨651048, by rfl⟩ : syracuseStep 1736129 = 1302097) B1302097
theorem B6946397 : Blo 912577 6946397 := bstep (se 3 (by rfl) ⟨1302449, by rfl⟩ : syracuseStep 6946397 = 2604899) B2604899
theorem B3899011 : Blo 912577 3899011 := bstep (se 1 (by rfl) ⟨2924258, by rfl⟩ : syracuseStep 3899011 = 5848517) B5848517
theorem B15040241 : Blo 912577 15040241 := bstep (se 2 (by rfl) ⟨5640090, by rfl⟩ : syracuseStep 15040241 = 11280181) B11280181
theorem B1736471 : Blo 912577 1736471 := bstep (se 1 (by rfl) ⟨1302353, by rfl⟩ : syracuseStep 1736471 = 2604707) B2604707
theorem B4620077 : Blo 912577 4620077 := bstep (se 3 (by rfl) ⟨866264, by rfl⟩ : syracuseStep 4620077 = 1732529) B1732529
theorem B3899353 : Blo 912577 3899353 := bstep (se 2 (by rfl) ⟨1462257, by rfl⟩ : syracuseStep 3899353 = 2924515) B2924515
theorem B5570789 : Blo 912577 5570789 := bstep (se 4 (by rfl) ⟨522261, by rfl⟩ : syracuseStep 5570789 = 1044523) B1044523
theorem B1540471 : Blo 912577 1540471 := bstep (se 1 (by rfl) ⟨1155353, by rfl⟩ : syracuseStep 1540471 = 2310707) B2310707
theorem B2196001 : Blo 912577 2196001 := bstep (se 2 (by rfl) ⟨823500, by rfl⟩ : syracuseStep 2196001 = 1647001) B1647001
theorem B1540667 : Blo 912577 1540667 := bstep (se 1 (by rfl) ⟨1155500, by rfl⟩ : syracuseStep 1540667 = 2311001) B2311001
theorem B4620887 : Blo 912577 4620887 := bstep (se 1 (by rfl) ⟨3465665, by rfl⟩ : syracuseStep 4620887 = 6931331) B6931331
theorem B4391617 : Blo 912577 4391617 := bstep (se 2 (by rfl) ⟨1646856, by rfl⟩ : syracuseStep 4391617 = 3293713) B3293713
theorem B33424163 : Blo 912577 33424163 := bstep (se 1 (by rfl) ⟨25068122, by rfl⟩ : syracuseStep 33424163 = 50136245) B50136245
theorem B3474323 : Blo 912577 3474323 := bstep (se 1 (by rfl) ⟨2605742, by rfl⟩ : syracuseStep 3474323 = 5211485) B5211485
theorem B1541065 : Blo 912577 1541065 := bstep (se 2 (by rfl) ⟨577899, by rfl⟩ : syracuseStep 1541065 = 1155799) B1155799
theorem B8258507 : Blo 912577 8258507 := bstep (se 1 (by rfl) ⟨6193880, by rfl⟩ : syracuseStep 8258507 = 12387761) B12387761
theorem B4621373 : Blo 912577 4621373 := bstep (se 3 (by rfl) ⟨866507, by rfl⟩ : syracuseStep 4621373 = 1733015) B1733015
theorem B1737875 : Blo 912577 1737875 := bstep (se 1 (by rfl) ⟨1303406, by rfl⟩ : syracuseStep 1737875 = 2606813) B2606813
theorem B1737929 : Blo 912577 1737929 := bstep (se 2 (by rfl) ⟨651723, by rfl⟩ : syracuseStep 1737929 = 1303447) B1303447
theorem B1738027 : Blo 912577 1738027 := bstep (se 1 (by rfl) ⟨1303520, by rfl⟩ : syracuseStep 1738027 = 2607041) B2607041
theorem B7800209 : Blo 912577 7800209 := bstep (se 2 (by rfl) ⟨2925078, by rfl⟩ : syracuseStep 7800209 = 5850157) B5850157
theorem B1738255 : Blo 912577 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B1541767 : Blo 912577 1541767 := bstep (se 1 (by rfl) ⟨1156325, by rfl⟩ : syracuseStep 1541767 = 2312651) B2312651
theorem B11142947 : Blo 912577 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B6588323 : Blo 912577 6588323 := bstep (se 1 (by rfl) ⟨4941242, by rfl⟩ : syracuseStep 6588323 = 9882485) B9882485
theorem B7800893 : Blo 912577 7800893 := bstep (se 3 (by rfl) ⟨1462667, by rfl⟩ : syracuseStep 7800893 = 2925335) B2925335
theorem B1542415 : Blo 912577 1542415 := bstep (se 1 (by rfl) ⟨1156811, by rfl⟩ : syracuseStep 1542415 = 2313623) B2313623
theorem B3901729 : Blo 912577 3901729 := bstep (se 2 (by rfl) ⟨1463148, by rfl⟩ : syracuseStep 3901729 = 2926297) B2926297
theorem B2197847 : Blo 912577 2197847 := bstep (se 1 (by rfl) ⟨1648385, by rfl⟩ : syracuseStep 2197847 = 3296771) B3296771
theorem B3082643 : Blo 912577 3082643 := bstep (se 1 (by rfl) ⟨2311982, by rfl⟩ : syracuseStep 3082643 = 4623965) B4623965
theorem B3475979 : Blo 912577 3475979 := bstep (se 1 (by rfl) ⟨2606984, by rfl⟩ : syracuseStep 3475979 = 5213969) B5213969
theorem B13208183 : Blo 912577 13208183 := bstep (se 1 (by rfl) ⟨9906137, by rfl⟩ : syracuseStep 13208183 = 19812275) B19812275
theorem B5212943 : Blo 912577 5212943 := bstep (se 1 (by rfl) ⟨3909707, by rfl⟩ : syracuseStep 5212943 = 7819415) B7819415
theorem B4950821 : Blo 912577 4950821 := bstep (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) B928279
theorem B1542955 : Blo 912577 1542955 := bstep (se 1 (by rfl) ⟨1157216, by rfl⟩ : syracuseStep 1542955 = 2314433) B2314433
theorem B4623155 : Blo 912577 4623155 := bstep (se 1 (by rfl) ⟨3467366, by rfl⟩ : syracuseStep 4623155 = 6934733) B6934733
theorem B1543097 : Blo 912577 1543097 := bstep (se 2 (by rfl) ⟨578661, by rfl⟩ : syracuseStep 1543097 = 1157323) B1157323
theorem B1739819 : Blo 912577 1739819 := bstep (se 1 (by rfl) ⟨1304864, by rfl⟩ : syracuseStep 1739819 = 2609729) B2609729
theorem B4623479 : Blo 912577 4623479 := bstep (se 1 (by rfl) ⟨3467609, by rfl⟩ : syracuseStep 4623479 = 6935219) B6935219
theorem B4951277 : Blo 912577 4951277 := bstep (se 3 (by rfl) ⟨928364, by rfl⟩ : syracuseStep 4951277 = 1856729) B1856729
theorem B17567077 : Blo 912577 17567077 := bstep (se 4 (by rfl) ⟨1646913, by rfl⟩ : syracuseStep 17567077 = 3293827) B3293827
theorem B1543799 : Blo 912577 1543799 := bstep (se 1 (by rfl) ⟨1157849, by rfl⟩ : syracuseStep 1543799 = 2315699) B2315699
theorem B8326775 : Blo 912577 8326775 := bstep (se 1 (by rfl) ⟨6245081, by rfl⟩ : syracuseStep 8326775 = 12490163) B12490163
theorem B10555109 : Blo 912577 10555109 := bstep (se 4 (by rfl) ⟨989541, by rfl⟩ : syracuseStep 10555109 = 1979083) B1979083
theorem B3084047 : Blo 912577 3084047 := bstep (se 1 (by rfl) ⟨2313035, by rfl⟩ : syracuseStep 3084047 = 4626071) B4626071
theorem B2232079 : Blo 912577 2232079 := bstep (se 1 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 2232079 = 3348119) B3348119
theorem B6950771 : Blo 912577 6950771 := bstep (se 1 (by rfl) ⟨5213078, by rfl⟩ : syracuseStep 6950771 = 10426157) B10426157
theorem B3903385 : Blo 912577 3903385 := bstep (se 2 (by rfl) ⟨1463769, by rfl⟩ : syracuseStep 3903385 = 2927539) B2927539
theorem B3084317 : Blo 912577 3084317 := bstep (se 3 (by rfl) ⟨578309, by rfl⟩ : syracuseStep 3084317 = 1156619) B1156619
theorem B1544251 : Blo 912577 1544251 := bstep (se 1 (by rfl) ⟨1158188, by rfl⟩ : syracuseStep 1544251 = 2316377) B2316377
theorem B4624451 : Blo 912577 4624451 := bstep (se 1 (by rfl) ⟨3468338, by rfl⟩ : syracuseStep 4624451 = 6936677) B6936677
theorem B5214401 : Blo 912577 5214401 := bstep (se 2 (by rfl) ⟨1955400, by rfl⟩ : syracuseStep 5214401 = 3910801) B3910801
theorem B1544393 : Blo 912577 1544393 := bstep (se 2 (by rfl) ⟨579147, by rfl⟩ : syracuseStep 1544393 = 1158295) B1158295
theorem B4231439 : Blo 912577 4231439 := bstep (se 1 (by rfl) ⟨3173579, by rfl⟩ : syracuseStep 4231439 = 6347159) B6347159
theorem B4624775 : Blo 912577 4624775 := bstep (se 1 (by rfl) ⟨3468581, by rfl⟩ : syracuseStep 4624775 = 6937163) B6937163
theorem B5870045 : Blo 912577 5870045 := bstep (se 3 (by rfl) ⟨1100633, by rfl⟩ : syracuseStep 5870045 = 2201267) B2201267
theorem B4395809 : Blo 912577 4395809 := bstep (se 2 (by rfl) ⟨1648428, by rfl⟩ : syracuseStep 4395809 = 3296857) B3296857
theorem B1545095 : Blo 912577 1545095 := bstep (se 1 (by rfl) ⟨1158821, by rfl⟩ : syracuseStep 1545095 = 2317643) B2317643
theorem B4395961 : Blo 912577 4395961 := bstep (se 2 (by rfl) ⟨1648485, by rfl⟩ : syracuseStep 4395961 = 3296971) B3296971
theorem B3085721 : Blo 912577 3085721 := bstep (se 2 (by rfl) ⟨1157145, by rfl⟩ : syracuseStep 3085721 = 2314291) B2314291
theorem B1545743 : Blo 912577 1545743 := bstep (se 1 (by rfl) ⟨1159307, by rfl⟩ : syracuseStep 1545743 = 2318615) B2318615
theorem B2004751 : Blo 912577 2004751 := bstep (se 1 (by rfl) ⟨1503563, by rfl⟩ : syracuseStep 2004751 = 3007127) B3007127
theorem B4953889 : Blo 912577 4953889 := bstep (se 2 (by rfl) ⟨1857708, by rfl⟩ : syracuseStep 4953889 = 3715417) B3715417
theorem B1546283 : Blo 912577 1546283 := bstep (se 1 (by rfl) ⟨1159712, by rfl⟩ : syracuseStep 1546283 = 2319425) B2319425
theorem B3086423 : Blo 912577 3086423 := bstep (se 1 (by rfl) ⟨2314817, by rfl⟩ : syracuseStep 3086423 = 4629635) B4629635
theorem B4757705 : Blo 912577 4757705 := bstep (se 2 (by rfl) ⟨1784139, by rfl⟩ : syracuseStep 4757705 = 3568279) B3568279
theorem B106928437 : Blo 912577 106928437 := bstep (se 5 (by rfl) ⟨5012270, by rfl⟩ : syracuseStep 106928437 = 10024541) B10024541
theorem B3479867 : Blo 912577 3479867 := bstep (se 1 (by rfl) ⟨2609900, by rfl⟩ : syracuseStep 3479867 = 5219801) B5219801
theorem B3709319 : Blo 912577 3709319 := bstep (se 1 (by rfl) ⟨2781989, by rfl⟩ : syracuseStep 3709319 = 5563979) B5563979
theorem B1546681 : Blo 912577 1546681 := bstep (se 2 (by rfl) ⟨580005, by rfl⟩ : syracuseStep 1546681 = 1160011) B1160011
theorem B2202113 : Blo 912577 2202113 := bstep (se 2 (by rfl) ⟨825792, by rfl⟩ : syracuseStep 2202113 = 1651585) B1651585
theorem B3086909 : Blo 912577 3086909 := bstep (se 3 (by rfl) ⟨578795, by rfl⟩ : syracuseStep 3086909 = 1157591) B1157591
theorem B4954931 : Blo 912577 4954931 := bstep (se 1 (by rfl) ⟨3716198, by rfl⟩ : syracuseStep 4954931 = 7432397) B7432397
theorem B6593395 : Blo 912577 6593395 := bstep (se 1 (by rfl) ⟨4945046, by rfl⟩ : syracuseStep 6593395 = 9890093) B9890093
theorem B96443693 : Blo 912577 96443693 := bstep (se 3 (by rfl) ⟨18083192, by rfl⟩ : syracuseStep 96443693 = 36166385) B36166385
theorem B990599 : Blo 912577 990599 := bstep (se 1 (by rfl) ⟨742949, by rfl⟩ : syracuseStep 990599 = 1485899) B1485899
theorem B4169335 : Blo 912577 4169335 := bstep (se 1 (by rfl) ⟨3127001, by rfl⟩ : syracuseStep 4169335 = 6254003) B6254003
theorem B4628339 : Blo 912577 4628339 := bstep (se 1 (by rfl) ⟨3471254, by rfl⟩ : syracuseStep 4628339 = 6942509) B6942509
theorem B3088313 : Blo 912577 3088313 := bstep (se 2 (by rfl) ⟨1158117, by rfl⟩ : syracuseStep 3088313 = 2316235) B2316235
theorem B4628825 : Blo 912577 4628825 := bstep (se 2 (by rfl) ⟨1735809, by rfl⟩ : syracuseStep 4628825 = 3471619) B3471619
theorem B2925067 : Blo 912577 2925067 := bstep (se 1 (by rfl) ⟨2193800, by rfl⟩ : syracuseStep 2925067 = 4387601) B4387601
theorem B3088907 : Blo 912577 3088907 := bstep (se 1 (by rfl) ⟨2316680, by rfl⟩ : syracuseStep 3088907 = 4633361) B4633361
theorem B1155703 : Blo 912577 1155703 := bstep (se 1 (by rfl) ⟨866777, by rfl⟩ : syracuseStep 1155703 = 1733555) B1733555
theorem B3089015 : Blo 912577 3089015 := bstep (se 1 (by rfl) ⟨2316761, by rfl⟩ : syracuseStep 3089015 = 4633523) B4633523
theorem B10560293 : Blo 912577 10560293 := bstep (se 4 (by rfl) ⟨990027, by rfl⟩ : syracuseStep 10560293 = 1980055) B1980055
theorem B1156027 : Blo 912577 1156027 := bstep (se 1 (by rfl) ⟨867020, by rfl⟩ : syracuseStep 1156027 = 1734041) B1734041
theorem B5219275 : Blo 912577 5219275 := bstep (se 1 (by rfl) ⟨3914456, by rfl⟩ : syracuseStep 5219275 = 7828913) B7828913
theorem B3089609 : Blo 912577 3089609 := bstep (se 2 (by rfl) ⟨1158603, by rfl⟩ : syracuseStep 3089609 = 2317207) B2317207
theorem B4400365 : Blo 912577 4400365 := bstep (se 3 (by rfl) ⟨825068, by rfl⟩ : syracuseStep 4400365 = 1650137) B1650137
theorem B7415525 : Blo 912577 7415525 := bstep (se 4 (by rfl) ⟨695205, by rfl⟩ : syracuseStep 7415525 = 1390411) B1390411
theorem B26388341 : Blo 912577 26388341 := bstep (se 5 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 26388341 = 2473907) B2473907
theorem B1156999 : Blo 912577 1156999 := bstep (se 1 (by rfl) ⟨867749, by rfl⟩ : syracuseStep 1156999 = 1735499) B1735499
theorem B3090311 : Blo 912577 3090311 := bstep (se 1 (by rfl) ⟨2317733, by rfl⟩ : syracuseStep 3090311 = 4635467) B4635467
theorem B1648759 : Blo 912577 1648759 := bstep (se 1 (by rfl) ⟨1236569, by rfl⟩ : syracuseStep 1648759 = 2473139) B2473139
theorem B3090689 : Blo 912577 3090689 := bstep (se 2 (by rfl) ⟨1159008, by rfl⟩ : syracuseStep 3090689 = 2318017) B2318017
theorem B1157419 : Blo 912577 1157419 := bstep (se 1 (by rfl) ⟨868064, by rfl⟩ : syracuseStep 1157419 = 1736129) B1736129
theorem B4630931 : Blo 912577 4630931 := bstep (se 1 (by rfl) ⟨3473198, by rfl⟩ : syracuseStep 4630931 = 6946397) B6946397
theorem B1157647 : Blo 912577 1157647 := bstep (se 1 (by rfl) ⟨868235, by rfl⟩ : syracuseStep 1157647 = 1736471) B1736471
theorem B1026823 : Blo 912577 1026823 := bstep (se 1 (by rfl) ⟨770117, by rfl⟩ : syracuseStep 1026823 = 1540235) B1540235
theorem B1649423 : Blo 912577 1649423 := bstep (se 1 (by rfl) ⟨1237067, by rfl⟩ : syracuseStep 1649423 = 2474135) B2474135
theorem B1027003 : Blo 912577 1027003 := bstep (se 1 (by rfl) ⟨770252, by rfl⟩ : syracuseStep 1027003 = 1540505) B1540505
theorem B3091499 : Blo 912577 3091499 := bstep (se 1 (by rfl) ⟨2318624, by rfl⟩ : syracuseStep 3091499 = 4637249) B4637249
theorem B1158391 : Blo 912577 1158391 := bstep (se 1 (by rfl) ⟨868793, by rfl⟩ : syracuseStep 1158391 = 1737587) B1737587
theorem B2600207 : Blo 912577 2600207 := bstep (se 1 (by rfl) ⟨1950155, by rfl⟩ : syracuseStep 2600207 = 3900311) B3900311
theorem B1027471 : Blo 912577 1027471 := bstep (se 1 (by rfl) ⟨770603, by rfl⟩ : syracuseStep 1027471 = 1541207) B1541207
theorem B14069177 : Blo 912577 14069177 := bstep (se 2 (by rfl) ⟨5275941, by rfl⟩ : syracuseStep 14069177 = 10551883) B10551883
theorem B6598097 : Blo 912577 6598097 := bstep (se 2 (by rfl) ⟨2474286, by rfl⟩ : syracuseStep 6598097 = 4948573) B4948573
theorem B39497219 : Blo 912577 39497219 := bstep (se 1 (by rfl) ⟨29622914, by rfl⟩ : syracuseStep 39497219 = 59245829) B59245829
theorem B1158715 : Blo 912577 1158715 := bstep (se 1 (by rfl) ⟨869036, by rfl⟩ : syracuseStep 1158715 = 1738073) B1738073
theorem B1027975 : Blo 912577 1027975 := bstep (se 1 (by rfl) ⟨770981, by rfl⟩ : syracuseStep 1027975 = 1541963) B1541963
theorem B1388459 : Blo 912577 1388459 := bstep (se 1 (by rfl) ⟨1041344, by rfl⟩ : syracuseStep 1388459 = 2082689) B2082689
theorem B3911723 : Blo 912577 3911723 := bstep (se 1 (by rfl) ⟨2933792, by rfl⟩ : syracuseStep 3911723 = 5867585) B5867585
theorem B1159211 : Blo 912577 1159211 := bstep (se 1 (by rfl) ⟨869408, by rfl⟩ : syracuseStep 1159211 = 1738817) B1738817
theorem B1028155 : Blo 912577 1028155 := bstep (se 1 (by rfl) ⟨771116, by rfl⟩ : syracuseStep 1028155 = 1542233) B1542233
theorem B3715159 : Blo 912577 3715159 := bstep (se 1 (by rfl) ⟨2786369, by rfl⟩ : syracuseStep 3715159 = 5572739) B5572739
theorem B1650835 : Blo 912577 1650835 := bstep (se 1 (by rfl) ⟨1238126, by rfl⟩ : syracuseStep 1650835 = 2476253) B2476253
theorem B3092795 : Blo 912577 3092795 := bstep (se 1 (by rfl) ⟨2319596, by rfl⟩ : syracuseStep 3092795 = 4639193) B4639193
theorem B2601335 : Blo 912577 2601335 := bstep (se 1 (by rfl) ⟨1951001, by rfl⟩ : syracuseStep 2601335 = 3902003) B3902003
theorem B1159687 : Blo 912577 1159687 := bstep (se 1 (by rfl) ⟨869765, by rfl⟩ : syracuseStep 1159687 = 1739531) B1739531
theorem B1028623 : Blo 912577 1028623 := bstep (se 1 (by rfl) ⟨771467, by rfl⟩ : syracuseStep 1028623 = 1542935) B1542935
theorem B2470459 : Blo 912577 2470459 := bstep (se 1 (by rfl) ⟨1852844, by rfl⟩ : syracuseStep 2470459 = 3705689) B3705689
theorem B3093281 : Blo 912577 3093281 := bstep (se 2 (by rfl) ⟨1159980, by rfl⟩ : syracuseStep 3093281 = 2319961) B2319961
theorem B1651499 : Blo 912577 1651499 := bstep (se 1 (by rfl) ⟨1238624, by rfl⟩ : syracuseStep 1651499 = 2477249) B2477249
theorem B15610805 : Blo 912577 15610805 := bstep (se 5 (by rfl) ⟨731756, by rfl⟩ : syracuseStep 15610805 = 1463513) B1463513
theorem B1029127 : Blo 912577 1029127 := bstep (se 1 (by rfl) ⟨771845, by rfl⟩ : syracuseStep 1029127 = 1543691) B1543691
theorem B2470999 : Blo 912577 2470999 := bstep (se 1 (by rfl) ⟨1853249, by rfl⟩ : syracuseStep 2470999 = 3706499) B3706499
theorem B2929783 : Blo 912577 2929783 := bstep (se 1 (by rfl) ⟨2197337, by rfl⟩ : syracuseStep 2929783 = 4394675) B4394675
theorem B1389755 : Blo 912577 1389755 := bstep (se 1 (by rfl) ⟨1042316, by rfl⟩ : syracuseStep 1389755 = 2084633) B2084633
theorem B1029307 : Blo 912577 1029307 := bstep (se 1 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 1029307 = 1543961) B1543961
theorem B4634009 : Blo 912577 4634009 := bstep (se 2 (by rfl) ⟨1737753, by rfl⟩ : syracuseStep 4634009 = 3475507) B3475507
theorem B1029775 : Blo 912577 1029775 := bstep (se 1 (by rfl) ⟨772331, by rfl⟩ : syracuseStep 1029775 = 1544663) B1544663
theorem B3127099 : Blo 912577 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B2603009 : Blo 912577 2603009 := bstep (se 2 (by rfl) ⟨976128, by rfl⟩ : syracuseStep 2603009 = 1952257) B1952257
theorem B2930717 : Blo 912577 2930717 := bstep (se 3 (by rfl) ⟨549509, by rfl⟩ : syracuseStep 2930717 = 1099019) B1099019
theorem B2603123 : Blo 912577 2603123 := bstep (se 1 (by rfl) ⟨1952342, by rfl⟩ : syracuseStep 2603123 = 3904685) B3904685
theorem B1030279 : Blo 912577 1030279 := bstep (se 1 (by rfl) ⟨772709, by rfl⟩ : syracuseStep 1030279 = 1545419) B1545419
theorem B1030459 : Blo 912577 1030459 := bstep (se 1 (by rfl) ⟨772844, by rfl⟩ : syracuseStep 1030459 = 1545689) B1545689
theorem B2603465 : Blo 912577 2603465 := bstep (se 2 (by rfl) ⟨976299, by rfl⟩ : syracuseStep 2603465 = 1952599) B1952599
theorem B11123243 : Blo 912577 11123243 := bstep (se 1 (by rfl) ⟨8342432, by rfl⟩ : syracuseStep 11123243 = 16684865) B16684865
theorem B1096463 : Blo 912577 1096463 := bstep (se 1 (by rfl) ⟨822347, by rfl⟩ : syracuseStep 1096463 = 1644695) B1644695
theorem B1030927 : Blo 912577 1030927 := bstep (se 1 (by rfl) ⟨773195, by rfl⟩ : syracuseStep 1030927 = 1546391) B1546391
theorem B3718003 : Blo 912577 3718003 := bstep (se 1 (by rfl) ⟨2788502, by rfl⟩ : syracuseStep 3718003 = 5577005) B5577005
theorem B17546165 : Blo 912577 17546165 := bstep (se 5 (by rfl) ⟨822476, by rfl⟩ : syracuseStep 17546165 = 1644953) B1644953
theorem B21085109 : Blo 912577 21085109 := bstep (se 5 (by rfl) ⟨988364, by rfl⟩ : syracuseStep 21085109 = 1976729) B1976729
theorem B2473217 : Blo 912577 2473217 := bstep (se 2 (by rfl) ⟨927456, by rfl⟩ : syracuseStep 2473217 = 1854913) B1854913
theorem B2342297 : Blo 912577 2342297 := bstep (se 2 (by rfl) ⟨878361, by rfl⟩ : syracuseStep 2342297 = 1756723) B1756723
theorem B1949113 : Blo 912577 1949113 := bstep (se 2 (by rfl) ⟨730917, by rfl⟩ : syracuseStep 1949113 = 1461835) B1461835
theorem B2342585 : Blo 912577 2342585 := bstep (se 2 (by rfl) ⟨878469, by rfl⟩ : syracuseStep 2342585 = 1756939) B1756939
theorem B3293081 : Blo 912577 3293081 := bstep (se 2 (by rfl) ⟨1234905, by rfl⟩ : syracuseStep 3293081 = 2469811) B2469811
theorem B4636601 : Blo 912577 4636601 := bstep (se 2 (by rfl) ⟨1738725, by rfl⟩ : syracuseStep 4636601 = 3477451) B3477451
theorem B40714285 : Blo 912577 40714285 := bstep (se 3 (by rfl) ⟨7633928, by rfl⟩ : syracuseStep 40714285 = 15267857) B15267857
theorem B2605355 : Blo 912577 2605355 := bstep (se 1 (by rfl) ⟨1954016, by rfl⟩ : syracuseStep 2605355 = 3908033) B3908033
theorem B2310515 : Blo 912577 2310515 := bstep (se 1 (by rfl) ⟨1732886, by rfl⟩ : syracuseStep 2310515 = 3465773) B3465773
theorem B2933177 : Blo 912577 2933177 := bstep (se 2 (by rfl) ⟨1099941, by rfl⟩ : syracuseStep 2933177 = 2199883) B2199883
theorem B2605583 : Blo 912577 2605583 := bstep (se 1 (by rfl) ⟨1954187, by rfl⟩ : syracuseStep 2605583 = 3908375) B3908375
theorem B1950497 : Blo 912577 1950497 := bstep (se 2 (by rfl) ⟨731436, by rfl⟩ : syracuseStep 1950497 = 1462873) B1462873
theorem B2311031 : Blo 912577 2311031 := bstep (se 1 (by rfl) ⟨1733273, by rfl⟩ : syracuseStep 2311031 = 3466547) B3466547
theorem B1950599 : Blo 912577 1950599 := bstep (se 1 (by rfl) ⟨1462949, by rfl⟩ : syracuseStep 1950599 = 2925899) B2925899
theorem B2475019 : Blo 912577 2475019 := bstep (se 1 (by rfl) ⟨1856264, by rfl⟩ : syracuseStep 2475019 = 3712529) B3712529
theorem B4637897 : Blo 912577 4637897 := bstep (se 2 (by rfl) ⟨1739211, by rfl⟩ : syracuseStep 4637897 = 3478423) B3478423
theorem B2344225 : Blo 912577 2344225 := bstep (se 2 (by rfl) ⟨879084, by rfl⟩ : syracuseStep 2344225 = 1758169) B1758169
theorem B2639147 : Blo 912577 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B2312023 : Blo 912577 2312023 := bstep (se 1 (by rfl) ⟨1734017, by rfl⟩ : syracuseStep 2312023 = 3468035) B3468035
theorem B1001359 : Blo 912577 1001359 := bstep (se 1 (by rfl) ⟨751019, by rfl⟩ : syracuseStep 1001359 = 1502039) B1502039
theorem B2606995 : Blo 912577 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B2607223 : Blo 912577 2607223 := bstep (se 1 (by rfl) ⟨1955417, by rfl⟩ : syracuseStep 2607223 = 3910835) B3910835
theorem B2312327 : Blo 912577 2312327 := bstep (se 1 (by rfl) ⟨1734245, by rfl⟩ : syracuseStep 2312327 = 3468491) B3468491
theorem B2312459 : Blo 912577 2312459 := bstep (se 1 (by rfl) ⟨1734344, by rfl⟩ : syracuseStep 2312459 = 3468689) B3468689
theorem B2312975 : Blo 912577 2312975 := bstep (se 1 (by rfl) ⟨1734731, by rfl⟩ : syracuseStep 2312975 = 3469463) B3469463
theorem B2313107 : Blo 912577 2313107 := bstep (se 1 (by rfl) ⟨1734830, by rfl⟩ : syracuseStep 2313107 = 3469661) B3469661
theorem B3525869 : Blo 912577 3525869 := bstep (se 3 (by rfl) ⟨661100, by rfl⟩ : syracuseStep 3525869 = 1322201) B1322201
theorem B2608499 : Blo 912577 2608499 := bstep (se 1 (by rfl) ⟨1956374, by rfl⟩ : syracuseStep 2608499 = 3912749) B3912749
theorem B2084231 : Blo 912577 2084231 := bstep (se 1 (by rfl) ⟨1563173, by rfl⟩ : syracuseStep 2084231 = 3126347) B3126347
theorem B2608841 : Blo 912577 2608841 := bstep (se 2 (by rfl) ⟨978315, by rfl⟩ : syracuseStep 2608841 = 1956631) B1956631
theorem B11128549 : Blo 912577 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B2608955 : Blo 912577 2608955 := bstep (se 1 (by rfl) ⟨1956716, by rfl⟩ : syracuseStep 2608955 = 3913433) B3913433
theorem B5001049 : Blo 912577 5001049 := bstep (se 2 (by rfl) ⟨1875393, by rfl⟩ : syracuseStep 5001049 = 3750787) B3750787
theorem B2609081 : Blo 912577 2609081 := bstep (se 2 (by rfl) ⟨978405, by rfl⟩ : syracuseStep 2609081 = 1956811) B1956811
theorem B5853131 : Blo 912577 5853131 := bstep (se 1 (by rfl) ⟨4389848, by rfl⟩ : syracuseStep 5853131 = 8779697) B8779697
theorem B2314241 : Blo 912577 2314241 := bstep (se 2 (by rfl) ⟨867840, by rfl⟩ : syracuseStep 2314241 = 1735681) B1735681
theorem B2084923 : Blo 912577 2084923 := bstep (se 1 (by rfl) ⟨1563692, by rfl⟩ : syracuseStep 2084923 = 3127385) B3127385
theorem B2314615 : Blo 912577 2314615 := bstep (se 1 (by rfl) ⟨1735961, by rfl⟩ : syracuseStep 2314615 = 3471923) B3471923
theorem B1233451 : Blo 912577 1233451 := bstep (se 1 (by rfl) ⟨925088, by rfl⟩ : syracuseStep 1233451 = 1850177) B1850177
theorem B8802917 : Blo 912577 8802917 := bstep (se 4 (by rfl) ⟨825273, by rfl⟩ : syracuseStep 8802917 = 1650547) B1650547
theorem B4936463 : Blo 912577 4936463 := bstep (se 1 (by rfl) ⟨3702347, by rfl⟩ : syracuseStep 4936463 = 7404695) B7404695
theorem B2315051 : Blo 912577 2315051 := bstep (se 1 (by rfl) ⟨1736288, by rfl⟩ : syracuseStep 2315051 = 3472577) B3472577
theorem B1856315 : Blo 912577 1856315 := bstep (se 1 (by rfl) ⟨1392236, by rfl⟩ : syracuseStep 1856315 = 2784473) B2784473
theorem B5198681 : Blo 912577 5198681 := bstep (se 2 (by rfl) ⟨1949505, by rfl⟩ : syracuseStep 5198681 = 3899011) B3899011
theorem B5199137 : Blo 912577 5199137 := bstep (se 2 (by rfl) ⟨1949676, by rfl⟩ : syracuseStep 5199137 = 3899353) B3899353
theorem B2053511 : Blo 912577 2053511 := bstep (se 1 (by rfl) ⟨1540133, by rfl⟩ : syracuseStep 2053511 = 3080267) B3080267
theorem B5199389 : Blo 912577 5199389 := bstep (se 3 (by rfl) ⟨974885, by rfl⟩ : syracuseStep 5199389 = 1949771) B1949771
theorem B2053691 : Blo 912577 2053691 := bstep (se 1 (by rfl) ⟨1540268, by rfl⟩ : syracuseStep 2053691 = 3080537) B3080537
theorem B2315891 : Blo 912577 2315891 := bstep (se 1 (by rfl) ⟨1736918, by rfl⟩ : syracuseStep 2315891 = 3473837) B3473837
theorem B1857143 : Blo 912577 1857143 := bstep (se 1 (by rfl) ⟨1392857, by rfl⟩ : syracuseStep 1857143 = 2785715) B2785715
theorem B2315911 : Blo 912577 2315911 := bstep (se 1 (by rfl) ⟨1736933, by rfl⟩ : syracuseStep 2315911 = 3473867) B3473867
theorem B2053817 : Blo 912577 2053817 := bstep (se 2 (by rfl) ⟨770181, by rfl⟩ : syracuseStep 2053817 = 1540363) B1540363
theorem B9885377 : Blo 912577 9885377 := bstep (se 2 (by rfl) ⟨3707016, by rfl⟩ : syracuseStep 9885377 = 7414033) B7414033
theorem B2316185 : Blo 912577 2316185 := bstep (se 2 (by rfl) ⟨868569, by rfl⟩ : syracuseStep 2316185 = 1737139) B1737139
theorem B1300411 : Blo 912577 1300411 := bstep (se 1 (by rfl) ⟨975308, by rfl⟩ : syracuseStep 1300411 = 1950617) B1950617
theorem B2054159 : Blo 912577 2054159 := bstep (se 1 (by rfl) ⟨1540619, by rfl⟩ : syracuseStep 2054159 = 3081239) B3081239
theorem B2054177 : Blo 912577 2054177 := bstep (se 2 (by rfl) ⟨770316, by rfl⟩ : syracuseStep 2054177 = 1540633) B1540633
theorem B20043821 : Blo 912577 20043821 := bstep (se 3 (by rfl) ⟨3758216, by rfl⟩ : syracuseStep 20043821 = 7516433) B7516433
theorem B2316347 : Blo 912577 2316347 := bstep (se 1 (by rfl) ⟨1737260, by rfl⟩ : syracuseStep 2316347 = 3474521) B3474521
theorem B2316559 : Blo 912577 2316559 := bstep (se 1 (by rfl) ⟨1737419, by rfl⟩ : syracuseStep 2316559 = 3474839) B3474839
theorem B2054519 : Blo 912577 2054519 := bstep (se 1 (by rfl) ⟨1540889, by rfl⟩ : syracuseStep 2054519 = 3081779) B3081779
theorem B1300855 : Blo 912577 1300855 := bstep (se 1 (by rfl) ⟨975641, by rfl⟩ : syracuseStep 1300855 = 1951283) B1951283
theorem B47569301 : Blo 912577 47569301 := bstep (se 6 (by rfl) ⟨1114905, by rfl⟩ : syracuseStep 47569301 = 2229811) B2229811
theorem B2316833 : Blo 912577 2316833 := bstep (se 2 (by rfl) ⟨868812, by rfl⟩ : syracuseStep 2316833 = 1737625) B1737625
theorem B2054699 : Blo 912577 2054699 := bstep (se 1 (by rfl) ⟨1541024, by rfl⟩ : syracuseStep 2054699 = 3082049) B3082049
theorem B1465103 : Blo 912577 1465103 := bstep (se 1 (by rfl) ⟨1098827, by rfl⟩ : syracuseStep 1465103 = 2197655) B2197655
theorem B2055059 : Blo 912577 2055059 := bstep (se 1 (by rfl) ⟨1541294, by rfl⟩ : syracuseStep 2055059 = 3082589) B3082589
theorem B2055113 : Blo 912577 2055113 := bstep (se 2 (by rfl) ⟨770667, by rfl⟩ : syracuseStep 2055113 = 1541335) B1541335
theorem B1301675 : Blo 912577 1301675 := bstep (se 1 (by rfl) ⟨976256, by rfl⟩ : syracuseStep 1301675 = 1952513) B1952513
theorem B1465615 : Blo 912577 1465615 := bstep (se 1 (by rfl) ⟨1099211, by rfl⟩ : syracuseStep 1465615 = 2198423) B2198423
theorem B2317835 : Blo 912577 2317835 := bstep (se 1 (by rfl) ⟨1738376, by rfl⟩ : syracuseStep 2317835 = 3476753) B3476753
theorem B1465871 : Blo 912577 1465871 := bstep (se 1 (by rfl) ⟨1099403, by rfl⟩ : syracuseStep 1465871 = 2198807) B2198807
theorem B8805955 : Blo 912577 8805955 := bstep (se 1 (by rfl) ⟨6604466, by rfl⟩ : syracuseStep 8805955 = 13208933) B13208933
theorem B2055815 : Blo 912577 2055815 := bstep (se 1 (by rfl) ⟨1541861, by rfl⟩ : syracuseStep 2055815 = 3083723) B3083723
theorem B7823141 : Blo 912577 7823141 := bstep (se 4 (by rfl) ⟨733419, by rfl⟩ : syracuseStep 7823141 = 1466839) B1466839
theorem B33349427 : Blo 912577 33349427 := bstep (se 1 (by rfl) ⟨25012070, by rfl⟩ : syracuseStep 33349427 = 50024141) B50024141
theorem B2055995 : Blo 912577 2055995 := bstep (se 1 (by rfl) ⟨1541996, by rfl⟩ : syracuseStep 2055995 = 3083993) B3083993
theorem B5201779 : Blo 912577 5201779 := bstep (se 1 (by rfl) ⟨3901334, by rfl⟩ : syracuseStep 5201779 = 7802669) B7802669
theorem B2056121 : Blo 912577 2056121 := bstep (se 2 (by rfl) ⟨771045, by rfl⟩ : syracuseStep 2056121 = 1542091) B1542091
theorem B7528535 : Blo 912577 7528535 := bstep (se 1 (by rfl) ⟨5646401, by rfl⟩ : syracuseStep 7528535 = 11292803) B11292803
theorem B2318483 : Blo 912577 2318483 := bstep (se 1 (by rfl) ⟨1738862, by rfl⟩ : syracuseStep 2318483 = 3477725) B3477725
theorem B975035 : Blo 912577 975035 := bstep (se 1 (by rfl) ⟨731276, by rfl⟩ : syracuseStep 975035 = 1462553) B1462553
theorem B8904941 : Blo 912577 8904941 := bstep (se 3 (by rfl) ⟨1669676, by rfl⟩ : syracuseStep 8904941 = 3339353) B3339353
theorem B2973953 : Blo 912577 2973953 := bstep (se 2 (by rfl) ⟨1115232, by rfl⟩ : syracuseStep 2973953 = 2230465) B2230465
theorem B2056463 : Blo 912577 2056463 := bstep (se 1 (by rfl) ⟨1542347, by rfl⟩ : syracuseStep 2056463 = 3084695) B3084695
theorem B2056481 : Blo 912577 2056481 := bstep (se 2 (by rfl) ⟨771180, by rfl⟩ : syracuseStep 2056481 = 1542361) B1542361
theorem B975163 : Blo 912577 975163 := bstep (se 1 (by rfl) ⟨731372, by rfl⟩ : syracuseStep 975163 = 1462745) B1462745
theorem B1466743 : Blo 912577 1466743 := bstep (se 1 (by rfl) ⟨1100057, by rfl⟩ : syracuseStep 1466743 = 2200115) B2200115
theorem B2318777 : Blo 912577 2318777 := bstep (se 2 (by rfl) ⟨869541, by rfl⟩ : syracuseStep 2318777 = 1739083) B1739083
theorem B2056823 : Blo 912577 2056823 := bstep (se 1 (by rfl) ⟨1542617, by rfl⟩ : syracuseStep 2056823 = 3085235) B3085235
theorem B1466999 : Blo 912577 1466999 := bstep (se 1 (by rfl) ⟨1100249, by rfl⟩ : syracuseStep 1466999 = 2200499) B2200499
theorem B1368875 : Blo 912577 1368875 := bstep (se 1 (by rfl) ⟨1026656, by rfl⟩ : syracuseStep 1368875 = 2053313) B2053313
theorem B2057003 : Blo 912577 2057003 := bstep (se 1 (by rfl) ⟨1542752, by rfl⟩ : syracuseStep 2057003 = 3085505) B3085505
theorem B1368905 : Blo 912577 1368905 := bstep (se 2 (by rfl) ⟨513339, by rfl⟩ : syracuseStep 1368905 = 1026679) B1026679
theorem B1369019 : Blo 912577 1369019 := bstep (se 1 (by rfl) ⟨1026764, by rfl⟩ : syracuseStep 1369019 = 2053529) B2053529
theorem B1369079 : Blo 912577 1369079 := bstep (se 1 (by rfl) ⟨1026809, by rfl⟩ : syracuseStep 1369079 = 2053619) B2053619
theorem B1303543 : Blo 912577 1303543 := bstep (se 1 (by rfl) ⟨977657, by rfl⟩ : syracuseStep 1303543 = 1955315) B1955315
theorem B1369103 : Blo 912577 1369103 := bstep (se 1 (by rfl) ⟨1026827, by rfl⟩ : syracuseStep 1369103 = 2053655) B2053655
theorem B1369145 : Blo 912577 1369145 := bstep (se 2 (by rfl) ⟨513429, by rfl⟩ : syracuseStep 1369145 = 1026859) B1026859
theorem B2319475 : Blo 912577 2319475 := bstep (se 1 (by rfl) ⟨1739606, by rfl⟩ : syracuseStep 2319475 = 3479213) B3479213
theorem B1369223 : Blo 912577 1369223 := bstep (se 1 (by rfl) ⟨1026917, by rfl⟩ : syracuseStep 1369223 = 2053835) B2053835
theorem B2057363 : Blo 912577 2057363 := bstep (se 1 (by rfl) ⟨1543022, by rfl⟩ : syracuseStep 2057363 = 3086045) B3086045
theorem B1369259 : Blo 912577 1369259 := bstep (se 1 (by rfl) ⟨1026944, by rfl⟩ : syracuseStep 1369259 = 2053889) B2053889
theorem B1369289 : Blo 912577 1369289 := bstep (se 2 (by rfl) ⟨513483, by rfl⟩ : syracuseStep 1369289 = 1026967) B1026967
theorem B2057417 : Blo 912577 2057417 := bstep (se 2 (by rfl) ⟨771531, by rfl⟩ : syracuseStep 2057417 = 1543063) B1543063
theorem B2319617 : Blo 912577 2319617 := bstep (se 2 (by rfl) ⟨869856, by rfl⟩ : syracuseStep 2319617 = 1739713) B1739713
theorem B5203237 : Blo 912577 5203237 := bstep (se 4 (by rfl) ⟨487803, by rfl⟩ : syracuseStep 5203237 = 975607) B975607
theorem B1369403 : Blo 912577 1369403 := bstep (se 1 (by rfl) ⟨1027052, by rfl⟩ : syracuseStep 1369403 = 2054105) B2054105
theorem B1369463 : Blo 912577 1369463 := bstep (se 1 (by rfl) ⟨1027097, by rfl⟩ : syracuseStep 1369463 = 2054195) B2054195
theorem B1369487 : Blo 912577 1369487 := bstep (se 1 (by rfl) ⟨1027115, by rfl⟩ : syracuseStep 1369487 = 2054231) B2054231
theorem B1369529 : Blo 912577 1369529 := bstep (se 2 (by rfl) ⟨513573, by rfl⟩ : syracuseStep 1369529 = 1027147) B1027147
theorem B1369607 : Blo 912577 1369607 := bstep (se 1 (by rfl) ⟨1027205, by rfl⟩ : syracuseStep 1369607 = 2054411) B2054411
theorem B1369643 : Blo 912577 1369643 := bstep (se 1 (by rfl) ⟨1027232, by rfl⟩ : syracuseStep 1369643 = 2054465) B2054465
theorem B1369673 : Blo 912577 1369673 := bstep (se 2 (by rfl) ⟨513627, by rfl⟩ : syracuseStep 1369673 = 1027255) B1027255
theorem B1369787 : Blo 912577 1369787 := bstep (se 1 (by rfl) ⟨1027340, by rfl⟩ : syracuseStep 1369787 = 2054681) B2054681
theorem B2320073 : Blo 912577 2320073 := bstep (se 2 (by rfl) ⟨870027, by rfl⟩ : syracuseStep 2320073 = 1740055) B1740055
theorem B1369847 : Blo 912577 1369847 := bstep (se 1 (by rfl) ⟨1027385, by rfl⟩ : syracuseStep 1369847 = 2054771) B2054771
theorem B1369871 : Blo 912577 1369871 := bstep (se 1 (by rfl) ⟨1027403, by rfl⟩ : syracuseStep 1369871 = 2054807) B2054807
theorem B1173263 : Blo 912577 1173263 := bstep (se 1 (by rfl) ⟨879947, by rfl⟩ : syracuseStep 1173263 = 1759895) B1759895
theorem B5203763 : Blo 912577 5203763 := bstep (se 1 (by rfl) ⟨3902822, by rfl⟩ : syracuseStep 5203763 = 7805645) B7805645
theorem B1369913 : Blo 912577 1369913 := bstep (se 2 (by rfl) ⟨513717, by rfl⟩ : syracuseStep 1369913 = 1027435) B1027435
theorem B1369991 : Blo 912577 1369991 := bstep (se 1 (by rfl) ⟨1027493, by rfl⟩ : syracuseStep 1369991 = 2054987) B2054987
theorem B2058119 : Blo 912577 2058119 := bstep (se 1 (by rfl) ⟨1543589, by rfl⟩ : syracuseStep 2058119 = 3087179) B3087179
theorem B1370027 : Blo 912577 1370027 := bstep (se 1 (by rfl) ⟨1027520, by rfl⟩ : syracuseStep 1370027 = 2055041) B2055041
theorem B1370057 : Blo 912577 1370057 := bstep (se 2 (by rfl) ⟨513771, by rfl⟩ : syracuseStep 1370057 = 1027543) B1027543
theorem B1304591 : Blo 912577 1304591 := bstep (se 1 (by rfl) ⟨978443, by rfl⟩ : syracuseStep 1304591 = 1956887) B1956887
theorem B18999341 : Blo 912577 18999341 := bstep (se 3 (by rfl) ⟨3562376, by rfl⟩ : syracuseStep 18999341 = 7124753) B7124753
theorem B1370171 : Blo 912577 1370171 := bstep (se 1 (by rfl) ⟨1027628, by rfl⟩ : syracuseStep 1370171 = 2055257) B2055257
theorem B2058299 : Blo 912577 2058299 := bstep (se 1 (by rfl) ⟨1543724, by rfl⟩ : syracuseStep 2058299 = 3087449) B3087449
theorem B1370231 : Blo 912577 1370231 := bstep (se 1 (by rfl) ⟨1027673, by rfl⟩ : syracuseStep 1370231 = 2055347) B2055347
theorem B1370255 : Blo 912577 1370255 := bstep (se 1 (by rfl) ⟨1027691, by rfl⟩ : syracuseStep 1370255 = 2055383) B2055383
theorem B1370297 : Blo 912577 1370297 := bstep (se 2 (by rfl) ⟨513861, by rfl⟩ : syracuseStep 1370297 = 1027723) B1027723
theorem B2058425 : Blo 912577 2058425 := bstep (se 2 (by rfl) ⟨771909, by rfl⟩ : syracuseStep 2058425 = 1543819) B1543819
theorem B1370375 : Blo 912577 1370375 := bstep (se 1 (by rfl) ⟨1027781, by rfl⟩ : syracuseStep 1370375 = 2055563) B2055563
theorem B1370411 : Blo 912577 1370411 := bstep (se 1 (by rfl) ⟨1027808, by rfl⟩ : syracuseStep 1370411 = 2055617) B2055617
theorem B1370441 : Blo 912577 1370441 := bstep (se 2 (by rfl) ⟨513915, by rfl⟩ : syracuseStep 1370441 = 1027831) B1027831
theorem B1304905 : Blo 912577 1304905 := bstep (se 2 (by rfl) ⟨489339, by rfl⟩ : syracuseStep 1304905 = 978679) B978679
theorem B1337719 : Blo 912577 1337719 := bstep (se 1 (by rfl) ⟨1003289, by rfl⟩ : syracuseStep 1337719 = 2006579) B2006579
theorem B1370555 : Blo 912577 1370555 := bstep (se 1 (by rfl) ⟨1027916, by rfl⟩ : syracuseStep 1370555 = 2055833) B2055833
theorem B5859793 : Blo 912577 5859793 := bstep (se 2 (by rfl) ⟨2197422, by rfl⟩ : syracuseStep 5859793 = 4394845) B4394845
theorem B1370615 : Blo 912577 1370615 := bstep (se 1 (by rfl) ⟨1027961, by rfl⟩ : syracuseStep 1370615 = 2055923) B2055923
theorem B1370639 : Blo 912577 1370639 := bstep (se 1 (by rfl) ⟨1027979, by rfl⟩ : syracuseStep 1370639 = 2055959) B2055959
theorem B2058767 : Blo 912577 2058767 := bstep (se 1 (by rfl) ⟨1544075, by rfl⟩ : syracuseStep 2058767 = 3088151) B3088151
theorem B2058785 : Blo 912577 2058785 := bstep (se 2 (by rfl) ⟨772044, by rfl⟩ : syracuseStep 2058785 = 1544089) B1544089
theorem B1370681 : Blo 912577 1370681 := bstep (se 2 (by rfl) ⟨514005, by rfl⟩ : syracuseStep 1370681 = 1028011) B1028011
theorem B1370759 : Blo 912577 1370759 := bstep (se 1 (by rfl) ⟨1028069, by rfl⟩ : syracuseStep 1370759 = 2056139) B2056139
theorem B1337999 : Blo 912577 1337999 := bstep (se 1 (by rfl) ⟨1003499, by rfl⟩ : syracuseStep 1337999 = 2006999) B2006999
theorem B1370795 : Blo 912577 1370795 := bstep (se 1 (by rfl) ⟨1028096, by rfl⟩ : syracuseStep 1370795 = 2056193) B2056193
theorem B1370825 : Blo 912577 1370825 := bstep (se 2 (by rfl) ⟨514059, by rfl⟩ : syracuseStep 1370825 = 1028119) B1028119
theorem B1370939 : Blo 912577 1370939 := bstep (se 1 (by rfl) ⟨1028204, by rfl⟩ : syracuseStep 1370939 = 2056409) B2056409
theorem B1370999 : Blo 912577 1370999 := bstep (se 1 (by rfl) ⟨1028249, by rfl⟩ : syracuseStep 1370999 = 2056499) B2056499
theorem B2059127 : Blo 912577 2059127 := bstep (se 1 (by rfl) ⟨1544345, by rfl⟩ : syracuseStep 2059127 = 3088691) B3088691
theorem B1371023 : Blo 912577 1371023 := bstep (se 1 (by rfl) ⟨1028267, by rfl⟩ : syracuseStep 1371023 = 2056535) B2056535
theorem B3468217 : Blo 912577 3468217 := bstep (se 2 (by rfl) ⟨1300581, by rfl⟩ : syracuseStep 3468217 = 2601163) B2601163
theorem B1371065 : Blo 912577 1371065 := bstep (se 2 (by rfl) ⟨514149, by rfl⟩ : syracuseStep 1371065 = 1028299) B1028299
theorem B1371143 : Blo 912577 1371143 := bstep (se 1 (by rfl) ⟨1028357, by rfl⟩ : syracuseStep 1371143 = 2056715) B2056715
theorem B1371179 : Blo 912577 1371179 := bstep (se 1 (by rfl) ⟨1028384, by rfl⟩ : syracuseStep 1371179 = 2056769) B2056769
theorem B2059307 : Blo 912577 2059307 := bstep (se 1 (by rfl) ⟨1544480, by rfl⟩ : syracuseStep 2059307 = 3088961) B3088961
theorem B10546237 : Blo 912577 10546237 := bstep (se 3 (by rfl) ⟨1977419, by rfl⟩ : syracuseStep 10546237 = 3954839) B3954839
theorem B1371209 : Blo 912577 1371209 := bstep (se 2 (by rfl) ⟨514203, by rfl⟩ : syracuseStep 1371209 = 1028407) B1028407
theorem B1371323 : Blo 912577 1371323 := bstep (se 1 (by rfl) ⟨1028492, by rfl⟩ : syracuseStep 1371323 = 2056985) B2056985
theorem B5205221 : Blo 912577 5205221 := bstep (se 4 (by rfl) ⟨487989, by rfl⟩ : syracuseStep 5205221 = 975979) B975979
theorem B1371383 : Blo 912577 1371383 := bstep (se 1 (by rfl) ⟨1028537, by rfl⟩ : syracuseStep 1371383 = 2057075) B2057075
theorem B912647 : Blo 912577 912647 := bstep (se 1 (by rfl) ⟨684485, by rfl⟩ : syracuseStep 912647 = 1368971) B1368971
theorem B912655 : Blo 912577 912655 := bstep (se 1 (by rfl) ⟨684491, by rfl⟩ : syracuseStep 912655 = 1368983) B1368983
theorem B1371407 : Blo 912577 1371407 := bstep (se 1 (by rfl) ⟨1028555, by rfl⟩ : syracuseStep 1371407 = 2057111) B2057111
theorem B1371449 : Blo 912577 1371449 := bstep (se 2 (by rfl) ⟨514293, by rfl⟩ : syracuseStep 1371449 = 1028587) B1028587
theorem B912699 : Blo 912577 912699 := bstep (se 1 (by rfl) ⟨684524, by rfl⟩ : syracuseStep 912699 = 1369049) B1369049
theorem B2780531 : Blo 912577 2780531 := bstep (se 1 (by rfl) ⟨2085398, by rfl⟩ : syracuseStep 2780531 = 4170797) B4170797
theorem B912775 : Blo 912577 912775 := bstep (se 1 (by rfl) ⟨684581, by rfl⟩ : syracuseStep 912775 = 1369163) B1369163
theorem B1371527 : Blo 912577 1371527 := bstep (se 1 (by rfl) ⟨1028645, by rfl⟩ : syracuseStep 1371527 = 2057291) B2057291
theorem B912783 : Blo 912577 912783 := bstep (se 1 (by rfl) ⟨684587, by rfl⟩ : syracuseStep 912783 = 1369175) B1369175
theorem B2059667 : Blo 912577 2059667 := bstep (se 1 (by rfl) ⟨1544750, by rfl⟩ : syracuseStep 2059667 = 3089501) B3089501
theorem B1371563 : Blo 912577 1371563 := bstep (se 1 (by rfl) ⟨1028672, by rfl⟩ : syracuseStep 1371563 = 2057345) B2057345
theorem B912827 : Blo 912577 912827 := bstep (se 1 (by rfl) ⟨684620, by rfl⟩ : syracuseStep 912827 = 1369241) B1369241
theorem B1371593 : Blo 912577 1371593 := bstep (se 2 (by rfl) ⟨514347, by rfl⟩ : syracuseStep 1371593 = 1028695) B1028695
theorem B2059721 : Blo 912577 2059721 := bstep (se 2 (by rfl) ⟨772395, by rfl⟩ : syracuseStep 2059721 = 1544791) B1544791
theorem B7925201 : Blo 912577 7925201 := bstep (se 2 (by rfl) ⟨2971950, by rfl⟩ : syracuseStep 7925201 = 5943901) B5943901
theorem B7400963 : Blo 912577 7400963 := bstep (se 1 (by rfl) ⟨5550722, by rfl⟩ : syracuseStep 7400963 = 11101445) B11101445
theorem B912903 : Blo 912577 912903 := bstep (se 1 (by rfl) ⟨684677, by rfl⟩ : syracuseStep 912903 = 1369355) B1369355
theorem B912911 : Blo 912577 912911 := bstep (se 1 (by rfl) ⟨684683, by rfl⟩ : syracuseStep 912911 = 1369367) B1369367
theorem B912955 : Blo 912577 912955 := bstep (se 1 (by rfl) ⟨684716, by rfl⟩ : syracuseStep 912955 = 1369433) B1369433
theorem B1371707 : Blo 912577 1371707 := bstep (se 1 (by rfl) ⟨1028780, by rfl⟩ : syracuseStep 1371707 = 2057561) B2057561
theorem B10546807 : Blo 912577 10546807 := bstep (se 1 (by rfl) ⟨7910105, by rfl⟩ : syracuseStep 10546807 = 15820211) B15820211
theorem B1371767 : Blo 912577 1371767 := bstep (se 1 (by rfl) ⟨1028825, by rfl⟩ : syracuseStep 1371767 = 2057651) B2057651
theorem B913031 : Blo 912577 913031 := bstep (se 1 (by rfl) ⟨684773, by rfl⟩ : syracuseStep 913031 = 1369547) B1369547
theorem B913039 : Blo 912577 913039 := bstep (se 1 (by rfl) ⟨684779, by rfl⟩ : syracuseStep 913039 = 1369559) B1369559
theorem B1371791 : Blo 912577 1371791 := bstep (se 1 (by rfl) ⟨1028843, by rfl⟩ : syracuseStep 1371791 = 2057687) B2057687
theorem B1371833 : Blo 912577 1371833 := bstep (se 2 (by rfl) ⟨514437, by rfl⟩ : syracuseStep 1371833 = 1028875) B1028875
theorem B913083 : Blo 912577 913083 := bstep (se 1 (by rfl) ⟨684812, by rfl⟩ : syracuseStep 913083 = 1369625) B1369625
theorem B7827137 : Blo 912577 7827137 := bstep (se 2 (by rfl) ⟨2935176, by rfl⟩ : syracuseStep 7827137 = 5870353) B5870353
theorem B913159 : Blo 912577 913159 := bstep (se 1 (by rfl) ⟨684869, by rfl⟩ : syracuseStep 913159 = 1369739) B1369739
theorem B1371911 : Blo 912577 1371911 := bstep (se 1 (by rfl) ⟨1028933, by rfl⟩ : syracuseStep 1371911 = 2057867) B2057867
theorem B913167 : Blo 912577 913167 := bstep (se 1 (by rfl) ⟨684875, by rfl⟩ : syracuseStep 913167 = 1369751) B1369751
theorem B7401253 : Blo 912577 7401253 := bstep (se 4 (by rfl) ⟨693867, by rfl⟩ : syracuseStep 7401253 = 1387735) B1387735
theorem B1371947 : Blo 912577 1371947 := bstep (se 1 (by rfl) ⟨1028960, by rfl⟩ : syracuseStep 1371947 = 2057921) B2057921
theorem B5009203 : Blo 912577 5009203 := bstep (se 1 (by rfl) ⟨3756902, by rfl⟩ : syracuseStep 5009203 = 7513805) B7513805
theorem B913211 : Blo 912577 913211 := bstep (se 1 (by rfl) ⟨684908, by rfl⟩ : syracuseStep 913211 = 1369817) B1369817
theorem B1371977 : Blo 912577 1371977 := bstep (se 2 (by rfl) ⟨514491, by rfl⟩ : syracuseStep 1371977 = 1028983) B1028983
theorem B913287 : Blo 912577 913287 := bstep (se 1 (by rfl) ⟨684965, by rfl⟩ : syracuseStep 913287 = 1369931) B1369931
theorem B913295 : Blo 912577 913295 := bstep (se 1 (by rfl) ⟨684971, by rfl⟩ : syracuseStep 913295 = 1369943) B1369943
theorem B1732499 : Blo 912577 1732499 := bstep (se 1 (by rfl) ⟨1299374, by rfl⟩ : syracuseStep 1732499 = 2598749) B2598749
theorem B913339 : Blo 912577 913339 := bstep (se 1 (by rfl) ⟨685004, by rfl⟩ : syracuseStep 913339 = 1370009) B1370009
theorem B1372091 : Blo 912577 1372091 := bstep (se 1 (by rfl) ⟨1029068, by rfl⟩ : syracuseStep 1372091 = 2058137) B2058137
theorem B1372151 : Blo 912577 1372151 := bstep (se 1 (by rfl) ⟨1029113, by rfl⟩ : syracuseStep 1372151 = 2058227) B2058227
theorem B913415 : Blo 912577 913415 := bstep (se 1 (by rfl) ⟨685061, by rfl⟩ : syracuseStep 913415 = 1370123) B1370123
theorem B913423 : Blo 912577 913423 := bstep (se 1 (by rfl) ⟨685067, by rfl⟩ : syracuseStep 913423 = 1370135) B1370135
theorem B1372175 : Blo 912577 1372175 := bstep (se 1 (by rfl) ⟨1029131, by rfl⟩ : syracuseStep 1372175 = 2058263) B2058263
theorem B1372217 : Blo 912577 1372217 := bstep (se 2 (by rfl) ⟨514581, by rfl⟩ : syracuseStep 1372217 = 1029163) B1029163
theorem B913467 : Blo 912577 913467 := bstep (se 1 (by rfl) ⟨685100, by rfl⟩ : syracuseStep 913467 = 1370201) B1370201
theorem B1732727 : Blo 912577 1732727 := bstep (se 1 (by rfl) ⟨1299545, by rfl⟩ : syracuseStep 1732727 = 2599091) B2599091
theorem B913543 : Blo 912577 913543 := bstep (se 1 (by rfl) ⟨685157, by rfl⟩ : syracuseStep 913543 = 1370315) B1370315
theorem B1372295 : Blo 912577 1372295 := bstep (se 1 (by rfl) ⟨1029221, by rfl⟩ : syracuseStep 1372295 = 2058443) B2058443
theorem B2060423 : Blo 912577 2060423 := bstep (se 1 (by rfl) ⟨1545317, by rfl⟩ : syracuseStep 2060423 = 3090635) B3090635
theorem B913551 : Blo 912577 913551 := bstep (se 1 (by rfl) ⟨685163, by rfl⟩ : syracuseStep 913551 = 1370327) B1370327
theorem B1372331 : Blo 912577 1372331 := bstep (se 1 (by rfl) ⟨1029248, by rfl⟩ : syracuseStep 1372331 = 2058497) B2058497
theorem B913595 : Blo 912577 913595 := bstep (se 1 (by rfl) ⟨685196, by rfl⟩ : syracuseStep 913595 = 1370393) B1370393
theorem B4944073 : Blo 912577 4944073 := bstep (se 2 (by rfl) ⟨1854027, by rfl⟩ : syracuseStep 4944073 = 3708055) B3708055
theorem B1372361 : Blo 912577 1372361 := bstep (se 2 (by rfl) ⟨514635, by rfl⟩ : syracuseStep 1372361 = 1029271) B1029271
theorem B913671 : Blo 912577 913671 := bstep (se 1 (by rfl) ⟨685253, by rfl⟩ : syracuseStep 913671 = 1370507) B1370507
theorem B913679 : Blo 912577 913679 := bstep (se 1 (by rfl) ⟨685259, by rfl⟩ : syracuseStep 913679 = 1370519) B1370519
theorem B913723 : Blo 912577 913723 := bstep (se 1 (by rfl) ⟨685292, by rfl⟩ : syracuseStep 913723 = 1370585) B1370585
theorem B1372475 : Blo 912577 1372475 := bstep (se 1 (by rfl) ⟨1029356, by rfl⟩ : syracuseStep 1372475 = 2058713) B2058713
theorem B2060603 : Blo 912577 2060603 := bstep (se 1 (by rfl) ⟨1545452, by rfl⟩ : syracuseStep 2060603 = 3090905) B3090905
theorem B1372535 : Blo 912577 1372535 := bstep (se 1 (by rfl) ⟨1029401, by rfl⟩ : syracuseStep 1372535 = 2058803) B2058803
theorem B913799 : Blo 912577 913799 := bstep (se 1 (by rfl) ⟨685349, by rfl⟩ : syracuseStep 913799 = 1370699) B1370699
theorem B913807 : Blo 912577 913807 := bstep (se 1 (by rfl) ⟨685355, by rfl⟩ : syracuseStep 913807 = 1370711) B1370711
theorem B1372559 : Blo 912577 1372559 := bstep (se 1 (by rfl) ⟨1029419, by rfl⟩ : syracuseStep 1372559 = 2058839) B2058839
theorem B1372601 : Blo 912577 1372601 := bstep (se 2 (by rfl) ⟨514725, by rfl⟩ : syracuseStep 1372601 = 1029451) B1029451
theorem B2060729 : Blo 912577 2060729 := bstep (se 2 (by rfl) ⟨772773, by rfl⟩ : syracuseStep 2060729 = 1545547) B1545547
theorem B913851 : Blo 912577 913851 := bstep (se 1 (by rfl) ⟨685388, by rfl⟩ : syracuseStep 913851 = 1370777) B1370777
theorem B913927 : Blo 912577 913927 := bstep (se 1 (by rfl) ⟨685445, by rfl⟩ : syracuseStep 913927 = 1370891) B1370891
theorem B1372679 : Blo 912577 1372679 := bstep (se 1 (by rfl) ⟨1029509, by rfl⟩ : syracuseStep 1372679 = 2059019) B2059019
theorem B913935 : Blo 912577 913935 := bstep (se 1 (by rfl) ⟨685451, by rfl⟩ : syracuseStep 913935 = 1370903) B1370903
theorem B1372715 : Blo 912577 1372715 := bstep (se 1 (by rfl) ⟨1029536, by rfl⟩ : syracuseStep 1372715 = 2059073) B2059073
theorem B913979 : Blo 912577 913979 := bstep (se 1 (by rfl) ⟨685484, by rfl⟩ : syracuseStep 913979 = 1370969) B1370969
theorem B1372745 : Blo 912577 1372745 := bstep (se 2 (by rfl) ⟨514779, by rfl⟩ : syracuseStep 1372745 = 1029559) B1029559
theorem B2224775 : Blo 912577 2224775 := bstep (se 1 (by rfl) ⟨1668581, by rfl⟩ : syracuseStep 2224775 = 3337163) B3337163
theorem B914055 : Blo 912577 914055 := bstep (se 1 (by rfl) ⟨685541, by rfl⟩ : syracuseStep 914055 = 1371083) B1371083
theorem B914063 : Blo 912577 914063 := bstep (se 1 (by rfl) ⟨685547, by rfl⟩ : syracuseStep 914063 = 1371095) B1371095
theorem B914107 : Blo 912577 914107 := bstep (se 1 (by rfl) ⟨685580, by rfl⟩ : syracuseStep 914107 = 1371161) B1371161
theorem B1372859 : Blo 912577 1372859 := bstep (se 1 (by rfl) ⟨1029644, by rfl⟩ : syracuseStep 1372859 = 2059289) B2059289
theorem B1372919 : Blo 912577 1372919 := bstep (se 1 (by rfl) ⟨1029689, by rfl⟩ : syracuseStep 1372919 = 2059379) B2059379
theorem B914183 : Blo 912577 914183 := bstep (se 1 (by rfl) ⟨685637, by rfl⟩ : syracuseStep 914183 = 1371275) B1371275
theorem B1372943 : Blo 912577 1372943 := bstep (se 1 (by rfl) ⟨1029707, by rfl⟩ : syracuseStep 1372943 = 2059415) B2059415
theorem B914191 : Blo 912577 914191 := bstep (se 1 (by rfl) ⟨685643, by rfl⟩ : syracuseStep 914191 = 1371287) B1371287
theorem B2061071 : Blo 912577 2061071 := bstep (se 1 (by rfl) ⟨1545803, by rfl⟩ : syracuseStep 2061071 = 3091607) B3091607
theorem B2061089 : Blo 912577 2061089 := bstep (se 2 (by rfl) ⟨772908, by rfl⟩ : syracuseStep 2061089 = 1545817) B1545817
theorem B1372985 : Blo 912577 1372985 := bstep (se 2 (by rfl) ⟨514869, by rfl⟩ : syracuseStep 1372985 = 1029739) B1029739
theorem B914235 : Blo 912577 914235 := bstep (se 1 (by rfl) ⟨685676, by rfl⟩ : syracuseStep 914235 = 1371353) B1371353
theorem B5567291 : Blo 912577 5567291 := bstep (se 1 (by rfl) ⟨4175468, by rfl⟩ : syracuseStep 5567291 = 8350937) B8350937
theorem B914311 : Blo 912577 914311 := bstep (se 1 (by rfl) ⟨685733, by rfl⟩ : syracuseStep 914311 = 1371467) B1371467
theorem B1373063 : Blo 912577 1373063 := bstep (se 1 (by rfl) ⟨1029797, by rfl⟩ : syracuseStep 1373063 = 2059595) B2059595
theorem B914319 : Blo 912577 914319 := bstep (se 1 (by rfl) ⟨685739, by rfl⟩ : syracuseStep 914319 = 1371479) B1371479
theorem B1373099 : Blo 912577 1373099 := bstep (se 1 (by rfl) ⟨1029824, by rfl⟩ : syracuseStep 1373099 = 2059649) B2059649
theorem B914363 : Blo 912577 914363 := bstep (se 1 (by rfl) ⟨685772, by rfl⟩ : syracuseStep 914363 = 1371545) B1371545
theorem B1373129 : Blo 912577 1373129 := bstep (se 2 (by rfl) ⟨514923, by rfl⟩ : syracuseStep 1373129 = 1029847) B1029847
theorem B914439 : Blo 912577 914439 := bstep (se 1 (by rfl) ⟨685829, by rfl⟩ : syracuseStep 914439 = 1371659) B1371659
theorem B914447 : Blo 912577 914447 := bstep (se 1 (by rfl) ⟨685835, by rfl⟩ : syracuseStep 914447 = 1371671) B1371671
theorem B914491 : Blo 912577 914491 := bstep (se 1 (by rfl) ⟨685868, by rfl⟩ : syracuseStep 914491 = 1371737) B1371737
theorem B1373243 : Blo 912577 1373243 := bstep (se 1 (by rfl) ⟨1029932, by rfl⟩ : syracuseStep 1373243 = 2059865) B2059865
theorem B1373303 : Blo 912577 1373303 := bstep (se 1 (by rfl) ⟨1029977, by rfl⟩ : syracuseStep 1373303 = 2059955) B2059955
theorem B2061431 : Blo 912577 2061431 := bstep (se 1 (by rfl) ⟨1546073, by rfl⟩ : syracuseStep 2061431 = 3092147) B3092147
theorem B914567 : Blo 912577 914567 := bstep (se 1 (by rfl) ⟨685925, by rfl⟩ : syracuseStep 914567 = 1371851) B1371851
theorem B914575 : Blo 912577 914575 := bstep (se 1 (by rfl) ⟨685931, by rfl⟩ : syracuseStep 914575 = 1371863) B1371863
theorem B1373327 : Blo 912577 1373327 := bstep (se 1 (by rfl) ⟨1029995, by rfl⟩ : syracuseStep 1373327 = 2059991) B2059991
theorem B1373369 : Blo 912577 1373369 := bstep (se 2 (by rfl) ⟨515013, by rfl⟩ : syracuseStep 1373369 = 1030027) B1030027
theorem B914619 : Blo 912577 914619 := bstep (se 1 (by rfl) ⟨685964, by rfl⟩ : syracuseStep 914619 = 1371929) B1371929
theorem B914695 : Blo 912577 914695 := bstep (se 1 (by rfl) ⟨686021, by rfl⟩ : syracuseStep 914695 = 1372043) B1372043
theorem B1373447 : Blo 912577 1373447 := bstep (se 1 (by rfl) ⟨1030085, by rfl⟩ : syracuseStep 1373447 = 2060171) B2060171
theorem B914703 : Blo 912577 914703 := bstep (se 1 (by rfl) ⟨686027, by rfl⟩ : syracuseStep 914703 = 1372055) B1372055
theorem B1373483 : Blo 912577 1373483 := bstep (se 1 (by rfl) ⟨1030112, by rfl⟩ : syracuseStep 1373483 = 2060225) B2060225
theorem B2061611 : Blo 912577 2061611 := bstep (se 1 (by rfl) ⟨1546208, by rfl⟩ : syracuseStep 2061611 = 3092417) B3092417
theorem B914747 : Blo 912577 914747 := bstep (se 1 (by rfl) ⟨686060, by rfl⟩ : syracuseStep 914747 = 1372121) B1372121
theorem B1373513 : Blo 912577 1373513 := bstep (se 2 (by rfl) ⟨515067, by rfl⟩ : syracuseStep 1373513 = 1030135) B1030135
theorem B914823 : Blo 912577 914823 := bstep (se 1 (by rfl) ⟨686117, by rfl⟩ : syracuseStep 914823 = 1372235) B1372235
theorem B914831 : Blo 912577 914831 := bstep (se 1 (by rfl) ⟨686123, by rfl⟩ : syracuseStep 914831 = 1372247) B1372247
theorem B914875 : Blo 912577 914875 := bstep (se 1 (by rfl) ⟨686156, by rfl⟩ : syracuseStep 914875 = 1372313) B1372313
theorem B1373627 : Blo 912577 1373627 := bstep (se 1 (by rfl) ⟨1030220, by rfl⟩ : syracuseStep 1373627 = 2060441) B2060441
theorem B1373687 : Blo 912577 1373687 := bstep (se 1 (by rfl) ⟨1030265, by rfl⟩ : syracuseStep 1373687 = 2060531) B2060531
theorem B914951 : Blo 912577 914951 := bstep (se 1 (by rfl) ⟨686213, by rfl⟩ : syracuseStep 914951 = 1372427) B1372427
theorem B914959 : Blo 912577 914959 := bstep (se 1 (by rfl) ⟨686219, by rfl⟩ : syracuseStep 914959 = 1372439) B1372439
theorem B1373711 : Blo 912577 1373711 := bstep (se 1 (by rfl) ⟨1030283, by rfl⟩ : syracuseStep 1373711 = 2060567) B2060567
theorem B1373753 : Blo 912577 1373753 := bstep (se 2 (by rfl) ⟨515157, by rfl⟩ : syracuseStep 1373753 = 1030315) B1030315
theorem B915003 : Blo 912577 915003 := bstep (se 1 (by rfl) ⟨686252, by rfl⟩ : syracuseStep 915003 = 1372505) B1372505
theorem B11859533 : Blo 912577 11859533 := bstep (se 3 (by rfl) ⟨2223662, by rfl⟩ : syracuseStep 11859533 = 4447325) B4447325
theorem B7927415 : Blo 912577 7927415 := bstep (se 1 (by rfl) ⟨5945561, by rfl⟩ : syracuseStep 7927415 = 11891123) B11891123
theorem B915079 : Blo 912577 915079 := bstep (se 1 (by rfl) ⟨686309, by rfl⟩ : syracuseStep 915079 = 1372619) B1372619
theorem B1373831 : Blo 912577 1373831 := bstep (se 1 (by rfl) ⟨1030373, by rfl⟩ : syracuseStep 1373831 = 2060747) B2060747
theorem B915087 : Blo 912577 915087 := bstep (se 1 (by rfl) ⟨686315, by rfl⟩ : syracuseStep 915087 = 1372631) B1372631
theorem B2061971 : Blo 912577 2061971 := bstep (se 1 (by rfl) ⟨1546478, by rfl⟩ : syracuseStep 2061971 = 3092957) B3092957
theorem B1373867 : Blo 912577 1373867 := bstep (se 1 (by rfl) ⟨1030400, by rfl⟩ : syracuseStep 1373867 = 2060801) B2060801
theorem B4388525 : Blo 912577 4388525 := bstep (se 3 (by rfl) ⟨822848, by rfl⟩ : syracuseStep 4388525 = 1645697) B1645697
theorem B915131 : Blo 912577 915131 := bstep (se 1 (by rfl) ⟨686348, by rfl⟩ : syracuseStep 915131 = 1372697) B1372697
theorem B7403201 : Blo 912577 7403201 := bstep (se 2 (by rfl) ⟨2776200, by rfl⟩ : syracuseStep 7403201 = 5552401) B5552401
theorem B1373897 : Blo 912577 1373897 := bstep (se 2 (by rfl) ⟨515211, by rfl⟩ : syracuseStep 1373897 = 1030423) B1030423
theorem B2062025 : Blo 912577 2062025 := bstep (se 2 (by rfl) ⟨773259, by rfl⟩ : syracuseStep 2062025 = 1546519) B1546519
theorem B915207 : Blo 912577 915207 := bstep (se 1 (by rfl) ⟨686405, by rfl⟩ : syracuseStep 915207 = 1372811) B1372811
theorem B3471119 : Blo 912577 3471119 := bstep (se 1 (by rfl) ⟨2603339, by rfl⟩ : syracuseStep 3471119 = 5206679) B5206679
theorem B915215 : Blo 912577 915215 := bstep (se 1 (by rfl) ⟨686411, by rfl⟩ : syracuseStep 915215 = 1372823) B1372823
theorem B1734443 : Blo 912577 1734443 := bstep (se 1 (by rfl) ⟨1300832, by rfl⟩ : syracuseStep 1734443 = 2601665) B2601665
theorem B915259 : Blo 912577 915259 := bstep (se 1 (by rfl) ⟨686444, by rfl⟩ : syracuseStep 915259 = 1372889) B1372889
theorem B1374011 : Blo 912577 1374011 := bstep (se 1 (by rfl) ⟨1030508, by rfl⟩ : syracuseStep 1374011 = 2061017) B2061017
theorem B1374071 : Blo 912577 1374071 := bstep (se 1 (by rfl) ⟨1030553, by rfl⟩ : syracuseStep 1374071 = 2061107) B2061107
theorem B915335 : Blo 912577 915335 := bstep (se 1 (by rfl) ⟨686501, by rfl⟩ : syracuseStep 915335 = 1373003) B1373003
theorem B915343 : Blo 912577 915343 := bstep (se 1 (by rfl) ⟨686507, by rfl⟩ : syracuseStep 915343 = 1373015) B1373015
theorem B1374095 : Blo 912577 1374095 := bstep (se 1 (by rfl) ⟨1030571, by rfl⟩ : syracuseStep 1374095 = 2061143) B2061143
theorem B1374137 : Blo 912577 1374137 := bstep (se 2 (by rfl) ⟨515301, by rfl⟩ : syracuseStep 1374137 = 1030603) B1030603
theorem B915387 : Blo 912577 915387 := bstep (se 1 (by rfl) ⟨686540, by rfl⟩ : syracuseStep 915387 = 1373081) B1373081
theorem B915463 : Blo 912577 915463 := bstep (se 1 (by rfl) ⟨686597, by rfl⟩ : syracuseStep 915463 = 1373195) B1373195
theorem B1374215 : Blo 912577 1374215 := bstep (se 1 (by rfl) ⟨1030661, by rfl⟩ : syracuseStep 1374215 = 2061323) B2061323
theorem B1734671 : Blo 912577 1734671 := bstep (se 1 (by rfl) ⟨1301003, by rfl⟩ : syracuseStep 1734671 = 2602007) B2602007
theorem B915471 : Blo 912577 915471 := bstep (se 1 (by rfl) ⟨686603, by rfl⟩ : syracuseStep 915471 = 1373207) B1373207
theorem B1374251 : Blo 912577 1374251 := bstep (se 1 (by rfl) ⟨1030688, by rfl⟩ : syracuseStep 1374251 = 2061377) B2061377
theorem B915515 : Blo 912577 915515 := bstep (se 1 (by rfl) ⟨686636, by rfl⟩ : syracuseStep 915515 = 1373273) B1373273
theorem B8353853 : Blo 912577 8353853 := bstep (se 3 (by rfl) ⟨1566347, by rfl⟩ : syracuseStep 8353853 = 3132695) B3132695
theorem B1374281 : Blo 912577 1374281 := bstep (se 2 (by rfl) ⟨515355, by rfl⟩ : syracuseStep 1374281 = 1030711) B1030711
theorem B915591 : Blo 912577 915591 := bstep (se 1 (by rfl) ⟨686693, by rfl⟩ : syracuseStep 915591 = 1373387) B1373387
theorem B915599 : Blo 912577 915599 := bstep (se 1 (by rfl) ⟨686699, by rfl⟩ : syracuseStep 915599 = 1373399) B1373399
theorem B915643 : Blo 912577 915643 := bstep (se 1 (by rfl) ⟨686732, by rfl⟩ : syracuseStep 915643 = 1373465) B1373465
theorem B1374395 : Blo 912577 1374395 := bstep (se 1 (by rfl) ⟨1030796, by rfl⟩ : syracuseStep 1374395 = 2061593) B2061593
theorem B1374455 : Blo 912577 1374455 := bstep (se 1 (by rfl) ⟨1030841, by rfl⟩ : syracuseStep 1374455 = 2061683) B2061683
theorem B915719 : Blo 912577 915719 := bstep (se 1 (by rfl) ⟨686789, by rfl⟩ : syracuseStep 915719 = 1373579) B1373579
theorem B915727 : Blo 912577 915727 := bstep (se 1 (by rfl) ⟨686795, by rfl⟩ : syracuseStep 915727 = 1373591) B1373591
theorem B1374479 : Blo 912577 1374479 := bstep (se 1 (by rfl) ⟨1030859, by rfl⟩ : syracuseStep 1374479 = 2061719) B2061719
theorem B1374521 : Blo 912577 1374521 := bstep (se 2 (by rfl) ⟨515445, by rfl⟩ : syracuseStep 1374521 = 1030891) B1030891
theorem B915771 : Blo 912577 915771 := bstep (se 1 (by rfl) ⟨686828, by rfl⟩ : syracuseStep 915771 = 1373657) B1373657
theorem B915847 : Blo 912577 915847 := bstep (se 1 (by rfl) ⟨686885, by rfl⟩ : syracuseStep 915847 = 1373771) B1373771
theorem B1374599 : Blo 912577 1374599 := bstep (se 1 (by rfl) ⟨1030949, by rfl⟩ : syracuseStep 1374599 = 2061899) B2061899
theorem B915855 : Blo 912577 915855 := bstep (se 1 (by rfl) ⟨686891, by rfl⟩ : syracuseStep 915855 = 1373783) B1373783
theorem B1374635 : Blo 912577 1374635 := bstep (se 1 (by rfl) ⟨1030976, by rfl⟩ : syracuseStep 1374635 = 2061953) B2061953
theorem B915899 : Blo 912577 915899 := bstep (se 1 (by rfl) ⟨686924, by rfl⟩ : syracuseStep 915899 = 1373849) B1373849
theorem B1374665 : Blo 912577 1374665 := bstep (se 2 (by rfl) ⟨515499, by rfl⟩ : syracuseStep 1374665 = 1030999) B1030999
theorem B8780237 : Blo 912577 8780237 := bstep (se 3 (by rfl) ⟨1646294, by rfl⟩ : syracuseStep 8780237 = 3292589) B3292589
theorem B915975 : Blo 912577 915975 := bstep (se 1 (by rfl) ⟨686981, by rfl⟩ : syracuseStep 915975 = 1373963) B1373963
theorem B915983 : Blo 912577 915983 := bstep (se 1 (by rfl) ⟨686987, by rfl⟩ : syracuseStep 915983 = 1373975) B1373975
theorem B916027 : Blo 912577 916027 := bstep (se 1 (by rfl) ⟨687020, by rfl⟩ : syracuseStep 916027 = 1374041) B1374041
theorem B1374779 : Blo 912577 1374779 := bstep (se 1 (by rfl) ⟨1031084, by rfl⟩ : syracuseStep 1374779 = 2062169) B2062169
theorem B4684349 : Blo 912577 4684349 := bstep (se 3 (by rfl) ⟨878315, by rfl⟩ : syracuseStep 4684349 = 1756631) B1756631
theorem B1374839 : Blo 912577 1374839 := bstep (se 1 (by rfl) ⟨1031129, by rfl⟩ : syracuseStep 1374839 = 2062259) B2062259
theorem B916103 : Blo 912577 916103 := bstep (se 1 (by rfl) ⟨687077, by rfl⟩ : syracuseStep 916103 = 1374155) B1374155
theorem B916111 : Blo 912577 916111 := bstep (se 1 (by rfl) ⟨687083, by rfl⟩ : syracuseStep 916111 = 1374167) B1374167
theorem B1374863 : Blo 912577 1374863 := bstep (se 1 (by rfl) ⟨1031147, by rfl⟩ : syracuseStep 1374863 = 2062295) B2062295
theorem B10418867 : Blo 912577 10418867 := bstep (se 1 (by rfl) ⟨7814150, by rfl⟩ : syracuseStep 10418867 = 15628301) B15628301
theorem B916155 : Blo 912577 916155 := bstep (se 1 (by rfl) ⟨687116, by rfl⟩ : syracuseStep 916155 = 1374233) B1374233
theorem B916231 : Blo 912577 916231 := bstep (se 1 (by rfl) ⟨687173, by rfl⟩ : syracuseStep 916231 = 1374347) B1374347
theorem B916239 : Blo 912577 916239 := bstep (se 1 (by rfl) ⟨687179, by rfl⟩ : syracuseStep 916239 = 1374359) B1374359
theorem B3701537 : Blo 912577 3701537 := bstep (se 2 (by rfl) ⟨1388076, by rfl⟩ : syracuseStep 3701537 = 2776153) B2776153
theorem B1506091 : Blo 912577 1506091 := bstep (se 1 (by rfl) ⟨1129568, by rfl⟩ : syracuseStep 1506091 = 2259137) B2259137
theorem B916283 : Blo 912577 916283 := bstep (se 1 (by rfl) ⟨687212, by rfl⟩ : syracuseStep 916283 = 1374425) B1374425
theorem B13171571 : Blo 912577 13171571 := bstep (se 1 (by rfl) ⟨9878678, by rfl⟩ : syracuseStep 13171571 = 19757357) B19757357
theorem B916359 : Blo 912577 916359 := bstep (se 1 (by rfl) ⟨687269, by rfl⟩ : syracuseStep 916359 = 1374539) B1374539
theorem B916367 : Blo 912577 916367 := bstep (se 1 (by rfl) ⟨687275, by rfl⟩ : syracuseStep 916367 = 1374551) B1374551
theorem B916411 : Blo 912577 916411 := bstep (se 1 (by rfl) ⟨687308, by rfl⟩ : syracuseStep 916411 = 1374617) B1374617
theorem B916487 : Blo 912577 916487 := bstep (se 1 (by rfl) ⟨687365, by rfl⟩ : syracuseStep 916487 = 1374731) B1374731
theorem B916495 : Blo 912577 916495 := bstep (se 1 (by rfl) ⟨687371, by rfl⟩ : syracuseStep 916495 = 1374743) B1374743
theorem B916539 : Blo 912577 916539 := bstep (se 1 (by rfl) ⟨687404, by rfl⟩ : syracuseStep 916539 = 1374809) B1374809
theorem B1736083 : Blo 912577 1736083 := bstep (se 1 (by rfl) ⟨1302062, by rfl⟩ : syracuseStep 1736083 = 2604125) B2604125
theorem B114392675 : Blo 912577 114392675 := bstep (se 1 (by rfl) ⟨85794506, by rfl⟩ : syracuseStep 114392675 = 171589013) B171589013
theorem B1736311 : Blo 912577 1736311 := bstep (se 1 (by rfl) ⟨1302233, by rfl⟩ : syracuseStep 1736311 = 2604467) B2604467
theorem B10026827 : Blo 912577 10026827 := bstep (se 1 (by rfl) ⟨7520120, by rfl⟩ : syracuseStep 10026827 = 15040241) B15040241
theorem B3080051 : Blo 912577 3080051 := bstep (se 1 (by rfl) ⟨2310038, by rfl⟩ : syracuseStep 3080051 = 4620077) B4620077
theorem B1736903 : Blo 912577 1736903 := bstep (se 1 (by rfl) ⟨1302677, by rfl⟩ : syracuseStep 1736903 = 2605355) B2605355
theorem B1540343 : Blo 912577 1540343 := bstep (se 1 (by rfl) ⟨1155257, by rfl⟩ : syracuseStep 1540343 = 2310515) B2310515
theorem B1737055 : Blo 912577 1737055 := bstep (se 1 (by rfl) ⟨1302791, by rfl⟩ : syracuseStep 1737055 = 2605583) B2605583
theorem B3080591 : Blo 912577 3080591 := bstep (se 1 (by rfl) ⟨2310443, by rfl⟩ : syracuseStep 3080591 = 4620887) B4620887
theorem B22282775 : Blo 912577 22282775 := bstep (se 1 (by rfl) ⟨16712081, by rfl⟩ : syracuseStep 22282775 = 33424163) B33424163
theorem B1540687 : Blo 912577 1540687 := bstep (se 1 (by rfl) ⟨1155515, by rfl⟩ : syracuseStep 1540687 = 2311031) B2311031
theorem B5505671 : Blo 912577 5505671 := bstep (se 1 (by rfl) ⟨4129253, by rfl⟩ : syracuseStep 5505671 = 8258507) B8258507
theorem B7930541 : Blo 912577 7930541 := bstep (se 3 (by rfl) ⟨1486976, by rfl⟩ : syracuseStep 7930541 = 2973953) B2973953
theorem B3900089 : Blo 912577 3900089 := bstep (se 2 (by rfl) ⟨1462533, by rfl⟩ : syracuseStep 3900089 = 2925067) B2925067
theorem B3080915 : Blo 912577 3080915 := bstep (se 1 (by rfl) ⟨2310686, by rfl⟩ : syracuseStep 3080915 = 4621373) B4621373
theorem B1540937 : Blo 912577 1540937 := bstep (se 2 (by rfl) ⟨577851, by rfl⟩ : syracuseStep 1540937 = 1155703) B1155703
theorem B1541369 : Blo 912577 1541369 := bstep (se 2 (by rfl) ⟨578013, by rfl⟩ : syracuseStep 1541369 = 1156027) B1156027
theorem B4392215 : Blo 912577 4392215 := bstep (se 1 (by rfl) ⟨3294161, by rfl⟩ : syracuseStep 4392215 = 6588323) B6588323
theorem B1541551 : Blo 912577 1541551 := bstep (se 1 (by rfl) ⟨1156163, by rfl⟩ : syracuseStep 1541551 = 2312327) B2312327
theorem B1541639 : Blo 912577 1541639 := bstep (se 1 (by rfl) ⟨1156229, by rfl⟩ : syracuseStep 1541639 = 2312459) B2312459
theorem B5867153 : Blo 912577 5867153 := bstep (se 2 (by rfl) ⟨2200182, by rfl⟩ : syracuseStep 5867153 = 4400365) B4400365
theorem B5932733 : Blo 912577 5932733 := bstep (se 3 (by rfl) ⟨1112387, by rfl⟩ : syracuseStep 5932733 = 2224775) B2224775
theorem B1541983 : Blo 912577 1541983 := bstep (se 1 (by rfl) ⟨1156487, by rfl⟩ : syracuseStep 1541983 = 2312975) B2312975
theorem B3475295 : Blo 912577 3475295 := bstep (se 1 (by rfl) ⟨2606471, by rfl⟩ : syracuseStep 3475295 = 5212943) B5212943
theorem B3082103 : Blo 912577 3082103 := bstep (se 1 (by rfl) ⟨2311577, by rfl⟩ : syracuseStep 3082103 = 4623155) B4623155
theorem B1542071 : Blo 912577 1542071 := bstep (se 1 (by rfl) ⟨1156553, by rfl⟩ : syracuseStep 1542071 = 2313107) B2313107
theorem B3082319 : Blo 912577 3082319 := bstep (se 1 (by rfl) ⟨2311739, by rfl⟩ : syracuseStep 3082319 = 4623479) B4623479
theorem B4950173 : Blo 912577 4950173 := bstep (se 3 (by rfl) ⟨928157, by rfl⟩ : syracuseStep 4950173 = 1856315) B1856315
theorem B1738999 : Blo 912577 1738999 := bstep (se 1 (by rfl) ⟨1304249, by rfl⟩ : syracuseStep 1738999 = 2608499) B2608499
theorem B3082697 : Blo 912577 3082697 := bstep (se 2 (by rfl) ⟨1156011, by rfl⟩ : syracuseStep 3082697 = 2312023) B2312023
theorem B1739227 : Blo 912577 1739227 := bstep (se 1 (by rfl) ⟨1304420, by rfl⟩ : syracuseStep 1739227 = 2608841) B2608841
theorem B1542665 : Blo 912577 1542665 := bstep (se 2 (by rfl) ⟨578499, by rfl⟩ : syracuseStep 1542665 = 1156999) B1156999
theorem B3475993 : Blo 912577 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B1739303 : Blo 912577 1739303 := bstep (se 1 (by rfl) ⟨1304477, by rfl⟩ : syracuseStep 1739303 = 2608955) B2608955
theorem B1739387 : Blo 912577 1739387 := bstep (se 1 (by rfl) ⟨1304540, by rfl⟩ : syracuseStep 1739387 = 2609081) B2609081
theorem B3902087 : Blo 912577 3902087 := bstep (se 1 (by rfl) ⟨2926565, by rfl⟩ : syracuseStep 3902087 = 5853131) B5853131
theorem B1542827 : Blo 912577 1542827 := bstep (se 1 (by rfl) ⟨1157120, by rfl⟩ : syracuseStep 1542827 = 2314241) B2314241
theorem B3082967 : Blo 912577 3082967 := bstep (se 1 (by rfl) ⟨2312225, by rfl⟩ : syracuseStep 3082967 = 4624451) B4624451
theorem B3476267 : Blo 912577 3476267 := bstep (se 1 (by rfl) ⟨2607200, by rfl⟩ : syracuseStep 3476267 = 5214401) B5214401
theorem B2198345 : Blo 912577 2198345 := bstep (se 2 (by rfl) ⟨824379, by rfl⟩ : syracuseStep 2198345 = 1648759) B1648759
theorem B3476297 : Blo 912577 3476297 := bstep (se 2 (by rfl) ⟨1303611, by rfl⟩ : syracuseStep 3476297 = 2607223) B2607223
theorem B2820959 : Blo 912577 2820959 := bstep (se 1 (by rfl) ⟨2115719, by rfl⟩ : syracuseStep 2820959 = 4231439) B4231439
theorem B3083183 : Blo 912577 3083183 := bstep (se 1 (by rfl) ⟨2312387, by rfl⟩ : syracuseStep 3083183 = 4624775) B4624775
theorem B1543225 : Blo 912577 1543225 := bstep (se 2 (by rfl) ⟨578709, by rfl⟩ : syracuseStep 1543225 = 1157419) B1157419
theorem B5868611 : Blo 912577 5868611 := bstep (se 1 (by rfl) ⟨4401458, by rfl⟩ : syracuseStep 5868611 = 8802917) B8802917
theorem B1739873 : Blo 912577 1739873 := bstep (se 2 (by rfl) ⟨652452, by rfl⟩ : syracuseStep 1739873 = 1304905) B1304905
theorem B3706013 : Blo 912577 3706013 := bstep (se 3 (by rfl) ⟨694877, by rfl⟩ : syracuseStep 3706013 = 1389755) B1389755
theorem B1543367 : Blo 912577 1543367 := bstep (se 1 (by rfl) ⟨1157525, by rfl⟩ : syracuseStep 1543367 = 2315051) B2315051
theorem B1543529 : Blo 912577 1543529 := bstep (se 2 (by rfl) ⟨578823, by rfl⟩ : syracuseStep 1543529 = 1157647) B1157647
theorem B1543927 : Blo 912577 1543927 := bstep (se 1 (by rfl) ⟨1157945, by rfl⟩ : syracuseStep 1543927 = 2315891) B2315891
theorem B6590251 : Blo 912577 6590251 := bstep (se 1 (by rfl) ⟨4942688, by rfl⟩ : syracuseStep 6590251 = 9885377) B9885377
theorem B4624289 : Blo 912577 4624289 := bstep (se 2 (by rfl) ⟨1734108, by rfl⟩ : syracuseStep 4624289 = 3468217) B3468217
theorem B1544123 : Blo 912577 1544123 := bstep (se 1 (by rfl) ⟨1158092, by rfl⟩ : syracuseStep 1544123 = 2316185) B2316185
theorem B1544231 : Blo 912577 1544231 := bstep (se 1 (by rfl) ⟨1158173, by rfl⟩ : syracuseStep 1544231 = 2316347) B2316347
theorem B14061649 : Blo 912577 14061649 := bstep (se 2 (by rfl) ⟨5273118, by rfl⟩ : syracuseStep 14061649 = 10546237) B10546237
theorem B1544521 : Blo 912577 1544521 := bstep (se 2 (by rfl) ⟨579195, by rfl⟩ : syracuseStep 1544521 = 1158391) B1158391
theorem B1544555 : Blo 912577 1544555 := bstep (se 1 (by rfl) ⟨1158416, by rfl⟩ : syracuseStep 1544555 = 2316833) B2316833
theorem B1544953 : Blo 912577 1544953 := bstep (se 2 (by rfl) ⟨579357, by rfl⟩ : syracuseStep 1544953 = 1158715) B1158715
theorem B14062409 : Blo 912577 14062409 := bstep (se 2 (by rfl) ⟨5273403, by rfl⟩ : syracuseStep 14062409 = 10546807) B10546807
theorem B64295795 : Blo 912577 64295795 := bstep (se 1 (by rfl) ⟨48221846, by rfl⟩ : syracuseStep 64295795 = 96443693) B96443693
theorem B1545223 : Blo 912577 1545223 := bstep (se 1 (by rfl) ⟨1158917, by rfl⟩ : syracuseStep 1545223 = 2317835) B2317835
theorem B9868337 : Blo 912577 9868337 := bstep (se 2 (by rfl) ⟨3700626, by rfl⟩ : syracuseStep 9868337 = 7401253) B7401253
theorem B5215427 : Blo 912577 5215427 := bstep (se 1 (by rfl) ⟨3911570, by rfl⟩ : syracuseStep 5215427 = 7823141) B7823141
theorem B3085559 : Blo 912577 3085559 := bstep (se 1 (by rfl) ⟨2314169, by rfl⟩ : syracuseStep 3085559 = 4628339) B4628339
theorem B6952229 : Blo 912577 6952229 := bstep (se 4 (by rfl) ⟨651771, by rfl⟩ : syracuseStep 6952229 = 1303543) B1303543
theorem B3478909 : Blo 912577 3478909 := bstep (se 3 (by rfl) ⟨652295, by rfl⟩ : syracuseStep 3478909 = 1304591) B1304591
theorem B5019023 : Blo 912577 5019023 := bstep (se 1 (by rfl) ⟨3764267, by rfl⟩ : syracuseStep 5019023 = 7528535) B7528535
theorem B1545655 : Blo 912577 1545655 := bstep (se 1 (by rfl) ⟨1159241, by rfl⟩ : syracuseStep 1545655 = 2318483) B2318483
theorem B4953545 : Blo 912577 4953545 := bstep (se 2 (by rfl) ⟨1857579, by rfl⟩ : syracuseStep 4953545 = 3715159) B3715159
theorem B53450189 : Blo 912577 53450189 := bstep (se 3 (by rfl) ⟨10021910, by rfl⟩ : syracuseStep 53450189 = 20043821) B20043821
theorem B5936627 : Blo 912577 5936627 := bstep (se 1 (by rfl) ⟨4452470, by rfl⟩ : syracuseStep 5936627 = 8904941) B8904941
theorem B2201113 : Blo 912577 2201113 := bstep (se 2 (by rfl) ⟨825417, by rfl⟩ : syracuseStep 2201113 = 1650835) B1650835
theorem B3085883 : Blo 912577 3085883 := bstep (se 1 (by rfl) ⟨2314412, by rfl⟩ : syracuseStep 3085883 = 4628825) B4628825
theorem B6592097 : Blo 912577 6592097 := bstep (se 2 (by rfl) ⟨2472036, by rfl⟩ : syracuseStep 6592097 = 4944073) B4944073
theorem B1545851 : Blo 912577 1545851 := bstep (se 1 (by rfl) ⟨1159388, by rfl⟩ : syracuseStep 1545851 = 2318777) B2318777
theorem B3086153 : Blo 912577 3086153 := bstep (se 2 (by rfl) ⟨1157307, by rfl⟩ : syracuseStep 3086153 = 2314615) B2314615
theorem B1546249 : Blo 912577 1546249 := bstep (se 2 (by rfl) ⟨579843, by rfl⟩ : syracuseStep 1546249 = 1159687) B1159687
theorem B1546411 : Blo 912577 1546411 := bstep (se 1 (by rfl) ⟨1159808, by rfl⟩ : syracuseStep 1546411 = 2319617) B2319617
theorem B1546715 : Blo 912577 1546715 := bstep (se 1 (by rfl) ⟨1160036, by rfl⟩ : syracuseStep 1546715 = 2320073) B2320073
theorem B5872301 : Blo 912577 5872301 := bstep (se 3 (by rfl) ⟨1101056, by rfl⟩ : syracuseStep 5872301 = 2202113) B2202113
theorem B3906377 : Blo 912577 3906377 := bstep (se 2 (by rfl) ⟨1464891, by rfl⟩ : syracuseStep 3906377 = 2929783) B2929783
theorem B12491597 : Blo 912577 12491597 := bstep (se 3 (by rfl) ⟨2342174, by rfl⟩ : syracuseStep 12491597 = 4684349) B4684349
theorem B3087287 : Blo 912577 3087287 := bstep (se 1 (by rfl) ⟨2315465, by rfl⟩ : syracuseStep 3087287 = 4630931) B4630931
theorem B2923901 : Blo 912577 2923901 := bstep (se 3 (by rfl) ⟨548231, by rfl⟩ : syracuseStep 2923901 = 1096463) B1096463
theorem B4398461 : Blo 912577 4398461 := bstep (se 3 (by rfl) ⟨824711, by rfl⟩ : syracuseStep 4398461 = 1649423) B1649423
theorem B3087881 : Blo 912577 3087881 := bstep (se 2 (by rfl) ⟨1157955, by rfl⟩ : syracuseStep 3087881 = 2315911) B2315911
theorem B9379451 : Blo 912577 9379451 := bstep (se 1 (by rfl) ⟨7034588, by rfl⟩ : syracuseStep 9379451 = 14069177) B14069177
theorem B5283467 : Blo 912577 5283467 := bstep (se 1 (by rfl) ⟨3962600, by rfl⟩ : syracuseStep 5283467 = 7925201) B7925201
theorem B4398731 : Blo 912577 4398731 := bstep (se 1 (by rfl) ⟨3299048, by rfl⟩ : syracuseStep 4398731 = 6598097) B6598097
theorem B4169465 : Blo 912577 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B5218091 : Blo 912577 5218091 := bstep (se 1 (by rfl) ⟨3913568, by rfl⟩ : syracuseStep 5218091 = 7827137) B7827137
theorem B1154999 : Blo 912577 1154999 := bstep (se 1 (by rfl) ⟨866249, by rfl⟩ : syracuseStep 1154999 = 1732499) B1732499
theorem B1155151 : Blo 912577 1155151 := bstep (se 1 (by rfl) ⟨866363, by rfl⟩ : syracuseStep 1155151 = 1732727) B1732727
theorem B3088745 : Blo 912577 3088745 := bstep (se 2 (by rfl) ⟨1158279, by rfl⟩ : syracuseStep 3088745 = 2316559) B2316559
theorem B3711527 : Blo 912577 3711527 := bstep (se 1 (by rfl) ⟨2783645, by rfl⟩ : syracuseStep 3711527 = 5567291) B5567291
theorem B3089339 : Blo 912577 3089339 := bstep (se 1 (by rfl) ⟨2317004, by rfl⟩ : syracuseStep 3089339 = 4634009) B4634009
theorem B7906355 : Blo 912577 7906355 := bstep (se 1 (by rfl) ⟨5929766, by rfl⟩ : syracuseStep 7906355 = 11859533) B11859533
theorem B2008121 : Blo 912577 2008121 := bstep (se 2 (by rfl) ⟨753045, by rfl⟩ : syracuseStep 2008121 = 1506091) B1506091
theorem B5284943 : Blo 912577 5284943 := bstep (se 1 (by rfl) ⟨3963707, by rfl⟩ : syracuseStep 5284943 = 7927415) B7927415
theorem B2925683 : Blo 912577 2925683 := bstep (se 1 (by rfl) ⟨2194262, by rfl⟩ : syracuseStep 2925683 = 4388525) B4388525
theorem B8791193 : Blo 912577 8791193 := bstep (se 2 (by rfl) ⟨3296697, by rfl⟩ : syracuseStep 8791193 = 6593395) B6593395
theorem B4957337 : Blo 912577 4957337 := bstep (se 2 (by rfl) ⟨1859001, by rfl⟩ : syracuseStep 4957337 = 3718003) B3718003
theorem B1156295 : Blo 912577 1156295 := bstep (se 1 (by rfl) ⟨867221, by rfl⟩ : syracuseStep 1156295 = 1734443) B1734443
theorem B1156447 : Blo 912577 1156447 := bstep (se 1 (by rfl) ⟨867335, by rfl⟩ : syracuseStep 1156447 = 1734671) B1734671
theorem B3908989 : Blo 912577 3908989 := bstep (se 3 (by rfl) ⟨732935, by rfl⟩ : syracuseStep 3908989 = 1465871) B1465871
theorem B11904421 : Blo 912577 11904421 := bstep (se 4 (by rfl) ⟨1116039, by rfl⟩ : syracuseStep 11904421 = 2232079) B2232079
theorem B7415495 : Blo 912577 7415495 := bstep (se 1 (by rfl) ⟨5561621, by rfl⟩ : syracuseStep 7415495 = 11123243) B11123243
theorem B2467691 : Blo 912577 2467691 := bstep (se 1 (by rfl) ⟨1850768, by rfl⟩ : syracuseStep 2467691 = 3701537) B3701537
theorem B2598817 : Blo 912577 2598817 := bstep (se 2 (by rfl) ⟨974556, by rfl⟩ : syracuseStep 2598817 = 1949113) B1949113
theorem B11741273 : Blo 912577 11741273 := bstep (se 2 (by rfl) ⟨4402977, by rfl⟩ : syracuseStep 11741273 = 8805955) B8805955
theorem B1648811 : Blo 912577 1648811 := bstep (se 1 (by rfl) ⟨1236608, by rfl⟩ : syracuseStep 1648811 = 2473217) B2473217
theorem B76261783 : Blo 912577 76261783 := bstep (se 1 (by rfl) ⟨57196337, by rfl⟩ : syracuseStep 76261783 = 114392675) B114392675
theorem B3091067 : Blo 912577 3091067 := bstep (se 1 (by rfl) ⟨2318300, by rfl⟩ : syracuseStep 3091067 = 4636601) B4636601
theorem B3091229 : Blo 912577 3091229 := bstep (se 3 (by rfl) ⟨579605, by rfl⟩ : syracuseStep 3091229 = 1159211) B1159211
theorem B11119589 : Blo 912577 11119589 := bstep (se 4 (by rfl) ⟨1042461, by rfl⟩ : syracuseStep 11119589 = 2084923) B2084923
theorem B1027111 : Blo 912577 1027111 := bstep (se 1 (by rfl) ⟨770333, by rfl⟩ : syracuseStep 1027111 = 1540667) B1540667
theorem B2600093 : Blo 912577 2600093 := bstep (se 3 (by rfl) ⟨487517, by rfl⟩ : syracuseStep 2600093 = 975035) B975035
theorem B14855437 : Blo 912577 14855437 := bstep (se 3 (by rfl) ⟨2785394, by rfl⟩ : syracuseStep 14855437 = 5570789) B5570789
theorem B2928001 : Blo 912577 2928001 := bstep (se 2 (by rfl) ⟨1098000, by rfl⟩ : syracuseStep 2928001 = 2196001) B2196001
theorem B1158619 : Blo 912577 1158619 := bstep (se 1 (by rfl) ⟨868964, by rfl⟩ : syracuseStep 1158619 = 1737929) B1737929
theorem B3091931 : Blo 912577 3091931 := bstep (se 1 (by rfl) ⟨2318948, by rfl⟩ : syracuseStep 3091931 = 4637897) B4637897
theorem B6959033 : Blo 912577 6959033 := bstep (se 2 (by rfl) ⟨2609637, by rfl⟩ : syracuseStep 6959033 = 5219275) B5219275
theorem B3092633 : Blo 912577 3092633 := bstep (se 2 (by rfl) ⟨1159737, by rfl⟩ : syracuseStep 3092633 = 2319475) B2319475
theorem B3125633 : Blo 912577 3125633 := bstep (se 2 (by rfl) ⟨1172112, by rfl⟩ : syracuseStep 3125633 = 2344225) B2344225
theorem B1028731 : Blo 912577 1028731 := bstep (se 1 (by rfl) ⟨771548, by rfl⟩ : syracuseStep 1028731 = 1543097) B1543097
theorem B1389487 : Blo 912577 1389487 := bstep (se 1 (by rfl) ⟨1042115, by rfl⟩ : syracuseStep 1389487 = 2084231) B2084231
theorem B5551183 : Blo 912577 5551183 := bstep (se 1 (by rfl) ⟨4163387, by rfl⟩ : syracuseStep 5551183 = 8326775) B8326775
theorem B1029199 : Blo 912577 1029199 := bstep (se 1 (by rfl) ⟨771899, by rfl⟩ : syracuseStep 1029199 = 1543799) B1543799
theorem B4633847 : Blo 912577 4633847 := bstep (se 1 (by rfl) ⟨3475385, by rfl⟩ : syracuseStep 4633847 = 6950771) B6950771
theorem B1029595 : Blo 912577 1029595 := bstep (se 1 (by rfl) ⟨772196, by rfl⟩ : syracuseStep 1029595 = 1544393) B1544393
theorem B3913363 : Blo 912577 3913363 := bstep (se 1 (by rfl) ⟨2935022, by rfl⟩ : syracuseStep 3913363 = 5870045) B5870045
theorem B4634333 : Blo 912577 4634333 := bstep (se 3 (by rfl) ⟨868937, by rfl⟩ : syracuseStep 4634333 = 1737875) B1737875
theorem B1783625 : Blo 912577 1783625 := bstep (se 2 (by rfl) ⟨668859, by rfl⟩ : syracuseStep 1783625 = 1337719) B1337719
theorem B3290975 : Blo 912577 3290975 := bstep (se 1 (by rfl) ⟨2468231, by rfl⟩ : syracuseStep 3290975 = 4936463) B4936463
theorem B2930539 : Blo 912577 2930539 := bstep (se 1 (by rfl) ⟨2197904, by rfl⟩ : syracuseStep 2930539 = 4395809) B4395809
theorem B1030063 : Blo 912577 1030063 := bstep (se 1 (by rfl) ⟨772547, by rfl⟩ : syracuseStep 1030063 = 1545095) B1545095
theorem B7813057 : Blo 912577 7813057 := bstep (se 2 (by rfl) ⟨2929896, by rfl⟩ : syracuseStep 7813057 = 5859793) B5859793
theorem B1030495 : Blo 912577 1030495 := bstep (se 1 (by rfl) ⟨772871, by rfl⟩ : syracuseStep 1030495 = 1545743) B1545743
theorem B1030855 : Blo 912577 1030855 := bstep (se 1 (by rfl) ⟨773141, by rfl⟩ : syracuseStep 1030855 = 1546283) B1546283
theorem B10566389 : Blo 912577 10566389 := bstep (se 5 (by rfl) ⟨495299, by rfl⟩ : syracuseStep 10566389 = 990599) B990599
theorem B3128701 : Blo 912577 3128701 := bstep (se 3 (by rfl) ⟨586631, by rfl⟩ : syracuseStep 3128701 = 1173263) B1173263
theorem B6668065 : Blo 912577 6668065 := bstep (se 2 (by rfl) ⟨2500524, by rfl⟩ : syracuseStep 6668065 = 5001049) B5001049
theorem B22232951 : Blo 912577 22232951 := bstep (se 1 (by rfl) ⟨16674713, by rfl⟩ : syracuseStep 22232951 = 33349427) B33349427
theorem B3293945 : Blo 912577 3293945 := bstep (se 2 (by rfl) ⟨1235229, by rfl⟩ : syracuseStep 3293945 = 2470459) B2470459
theorem B12666227 : Blo 912577 12666227 := bstep (se 1 (by rfl) ⟨9499670, by rfl⟩ : syracuseStep 12666227 = 18999341) B18999341
theorem B3294665 : Blo 912577 3294665 := bstep (se 2 (by rfl) ⟨1235499, by rfl⟩ : syracuseStep 3294665 = 2470999) B2470999
theorem B1853687 : Blo 912577 1853687 := bstep (se 1 (by rfl) ⟨1390265, by rfl⟩ : syracuseStep 1853687 = 2780531) B2780531
theorem B4933975 : Blo 912577 4933975 := bstep (se 1 (by rfl) ⟨3700481, by rfl⟩ : syracuseStep 4933975 = 7400963) B7400963
theorem B26331479 : Blo 912577 26331479 := bstep (se 1 (by rfl) ⟨19748609, by rfl⟩ : syracuseStep 26331479 = 39497219) B39497219
theorem B2673001 : Blo 912577 2673001 := bstep (se 2 (by rfl) ⟨1002375, by rfl⟩ : syracuseStep 2673001 = 2004751) B2004751
theorem B6605185 : Blo 912577 6605185 := bstep (se 2 (by rfl) ⟨2476944, by rfl⟩ : syracuseStep 6605185 = 4953889) B4953889
theorem B2607815 : Blo 912577 2607815 := bstep (se 1 (by rfl) ⟨1955861, by rfl⟩ : syracuseStep 2607815 = 3911723) B3911723
theorem B4639517 : Blo 912577 4639517 := bstep (se 3 (by rfl) ⟨869909, by rfl⟩ : syracuseStep 4639517 = 1739819) B1739819
theorem B1100999 : Blo 912577 1100999 := bstep (se 1 (by rfl) ⟨825749, by rfl⟩ : syracuseStep 1100999 = 1651499) B1651499
theorem B10407203 : Blo 912577 10407203 := bstep (se 1 (by rfl) ⟨7805402, by rfl⟩ : syracuseStep 10407203 = 15610805) B15610805
theorem B4935467 : Blo 912577 4935467 := bstep (se 1 (by rfl) ⟨3701600, by rfl⟩ : syracuseStep 4935467 = 7403201) B7403201
theorem B2314079 : Blo 912577 2314079 := bstep (se 1 (by rfl) ⟨1735559, by rfl⟩ : syracuseStep 2314079 = 3471119) B3471119
theorem B1953811 : Blo 912577 1953811 := bstep (se 1 (by rfl) ⟨1465358, by rfl⟩ : syracuseStep 1953811 = 2930717) B2930717
theorem B5853491 : Blo 912577 5853491 := bstep (se 1 (by rfl) ⟨4390118, by rfl⟩ : syracuseStep 5853491 = 8780237) B8780237
theorem B1954153 : Blo 912577 1954153 := bstep (se 2 (by rfl) ⟨732807, by rfl⟩ : syracuseStep 1954153 = 1465615) B1465615
theorem B2314777 : Blo 912577 2314777 := bstep (se 2 (by rfl) ⟨868041, by rfl⟩ : syracuseStep 2314777 = 1736083) B1736083
theorem B5559113 : Blo 912577 5559113 := bstep (se 2 (by rfl) ⟨2084667, by rfl⟩ : syracuseStep 5559113 = 4169335) B4169335
theorem B2315081 : Blo 912577 2315081 := bstep (se 2 (by rfl) ⟨868155, by rfl⟩ : syracuseStep 2315081 = 1736311) B1736311
theorem B1561531 : Blo 912577 1561531 := bstep (se 1 (by rfl) ⟨1171148, by rfl⟩ : syracuseStep 1561531 = 2342297) B2342297
theorem B1561723 : Blo 912577 1561723 := bstep (se 1 (by rfl) ⟨1171292, by rfl⟩ : syracuseStep 1561723 = 2342585) B2342585
theorem B6935705 : Blo 912577 6935705 := bstep (se 2 (by rfl) ⟨2600889, by rfl⟩ : syracuseStep 6935705 = 5201779) B5201779
theorem B2053367 : Blo 912577 2053367 := bstep (se 1 (by rfl) ⟨1540025, by rfl⟩ : syracuseStep 2053367 = 3080051) B3080051
theorem B54285713 : Blo 912577 54285713 := bstep (se 2 (by rfl) ⟨20357142, by rfl⟩ : syracuseStep 54285713 = 40714285) B40714285
theorem B1300217 : Blo 912577 1300217 := bstep (se 2 (by rfl) ⟨487581, by rfl⟩ : syracuseStep 1300217 = 975163) B975163
theorem B1955657 : Blo 912577 1955657 := bstep (se 2 (by rfl) ⟨733371, by rfl⟩ : syracuseStep 1955657 = 1466743) B1466743
theorem B2053961 : Blo 912577 2053961 := bstep (se 2 (by rfl) ⟨770235, by rfl⟩ : syracuseStep 2053961 = 1540471) B1540471
theorem B1300331 : Blo 912577 1300331 := bstep (se 1 (by rfl) ⟨975248, by rfl⟩ : syracuseStep 1300331 = 1950497) B1950497
theorem B2316215 : Blo 912577 2316215 := bstep (se 1 (by rfl) ⟨1737161, by rfl⟩ : syracuseStep 2316215 = 3474323) B3474323
theorem B5855489 : Blo 912577 5855489 := bstep (se 2 (by rfl) ⟨2195808, by rfl⟩ : syracuseStep 5855489 = 4391617) B4391617
theorem B5200139 : Blo 912577 5200139 := bstep (se 1 (by rfl) ⟨3900104, by rfl⟩ : syracuseStep 5200139 = 7800209) B7800209
theorem B7821805 : Blo 912577 7821805 := bstep (se 3 (by rfl) ⟨1466588, by rfl⟩ : syracuseStep 7821805 = 2933177) B2933177
theorem B7428631 : Blo 912577 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B2054753 : Blo 912577 2054753 := bstep (se 2 (by rfl) ⟨770532, by rfl⟩ : syracuseStep 2054753 = 1541065) B1541065
theorem B5200595 : Blo 912577 5200595 := bstep (se 1 (by rfl) ⟨3900446, by rfl⟩ : syracuseStep 5200595 = 7800893) B7800893
theorem B1465231 : Blo 912577 1465231 := bstep (se 1 (by rfl) ⟨1098923, by rfl⟩ : syracuseStep 1465231 = 2197847) B2197847
theorem B2055095 : Blo 912577 2055095 := bstep (se 1 (by rfl) ⟨1541321, by rfl⟩ : syracuseStep 2055095 = 3082643) B3082643
theorem B2317319 : Blo 912577 2317319 := bstep (se 1 (by rfl) ⟨1737989, by rfl⟩ : syracuseStep 2317319 = 3475979) B3475979
theorem B6937649 : Blo 912577 6937649 := bstep (se 2 (by rfl) ⟨2601618, by rfl⟩ : syracuseStep 6937649 = 5203237) B5203237
theorem B2317369 : Blo 912577 2317369 := bstep (se 2 (by rfl) ⟨869013, by rfl⟩ : syracuseStep 2317369 = 1738027) B1738027
theorem B8805455 : Blo 912577 8805455 := bstep (se 1 (by rfl) ⟨6604091, by rfl⟩ : syracuseStep 8805455 = 13208183) B13208183
theorem B2317673 : Blo 912577 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B3300851 : Blo 912577 3300851 := bstep (se 1 (by rfl) ⟨2475638, by rfl⟩ : syracuseStep 3300851 = 4951277) B4951277
theorem B2055689 : Blo 912577 2055689 := bstep (se 2 (by rfl) ⟨770883, by rfl⟩ : syracuseStep 2055689 = 1541767) B1541767
theorem B5201597 : Blo 912577 5201597 := bstep (se 3 (by rfl) ⟨975299, by rfl⟩ : syracuseStep 5201597 = 1950599) B1950599
theorem B7036739 : Blo 912577 7036739 := bstep (se 1 (by rfl) ⟨5277554, by rfl⟩ : syracuseStep 7036739 = 10555109) B10555109
theorem B2056031 : Blo 912577 2056031 := bstep (se 1 (by rfl) ⟨1542023, by rfl⟩ : syracuseStep 2056031 = 3084047) B3084047
theorem B1335145 : Blo 912577 1335145 := bstep (se 2 (by rfl) ⟨500679, by rfl⟩ : syracuseStep 1335145 = 1001359) B1001359
theorem B2056211 : Blo 912577 2056211 := bstep (se 1 (by rfl) ⟨1542158, by rfl⟩ : syracuseStep 2056211 = 3084317) B3084317
theorem B6578405 : Blo 912577 6578405 := bstep (se 4 (by rfl) ⟨616725, by rfl⟩ : syracuseStep 6578405 = 1233451) B1233451
theorem B2056553 : Blo 912577 2056553 := bstep (se 2 (by rfl) ⟨771207, by rfl⟩ : syracuseStep 2056553 = 1542415) B1542415
theorem B5202305 : Blo 912577 5202305 := bstep (se 2 (by rfl) ⟨1950864, by rfl⟩ : syracuseStep 5202305 = 3901729) B3901729
theorem B3465787 : Blo 912577 3465787 := bstep (se 1 (by rfl) ⟨2599340, by rfl⟩ : syracuseStep 3465787 = 5198681) B5198681
theorem B7037725 : Blo 912577 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B3466091 : Blo 912577 3466091 := bstep (se 1 (by rfl) ⟨2599568, by rfl⟩ : syracuseStep 3466091 = 5199137) B5199137
theorem B1369007 : Blo 912577 1369007 := bstep (se 1 (by rfl) ⟨1026755, by rfl⟩ : syracuseStep 1369007 = 2053511) B2053511
theorem B2057147 : Blo 912577 2057147 := bstep (se 1 (by rfl) ⟨1542860, by rfl⟩ : syracuseStep 2057147 = 3085721) B3085721
theorem B1369097 : Blo 912577 1369097 := bstep (se 2 (by rfl) ⟨513411, by rfl⟩ : syracuseStep 1369097 = 1026823) B1026823
theorem B3466259 : Blo 912577 3466259 := bstep (se 1 (by rfl) ⟨2599694, by rfl⟩ : syracuseStep 3466259 = 5199389) B5199389
theorem B1369127 : Blo 912577 1369127 := bstep (se 1 (by rfl) ⟨1026845, by rfl⟩ : syracuseStep 1369127 = 2053691) B2053691
theorem B2057273 : Blo 912577 2057273 := bstep (se 2 (by rfl) ⟨771477, by rfl⟩ : syracuseStep 2057273 = 1542955) B1542955
theorem B1238095 : Blo 912577 1238095 := bstep (se 1 (by rfl) ⟨928571, by rfl⟩ : syracuseStep 1238095 = 1857143) B1857143
theorem B1369211 : Blo 912577 1369211 := bstep (se 1 (by rfl) ⟨1026908, by rfl⟩ : syracuseStep 1369211 = 2053817) B2053817
theorem B1369337 : Blo 912577 1369337 := bstep (se 2 (by rfl) ⟨513501, by rfl⟩ : syracuseStep 1369337 = 1027003) B1027003
theorem B1369439 : Blo 912577 1369439 := bstep (se 1 (by rfl) ⟨1027079, by rfl⟩ : syracuseStep 1369439 = 2054159) B2054159
theorem B1369451 : Blo 912577 1369451 := bstep (se 1 (by rfl) ⟨1027088, by rfl⟩ : syracuseStep 1369451 = 2054177) B2054177
theorem B2057615 : Blo 912577 2057615 := bstep (se 1 (by rfl) ⟨1543211, by rfl⟩ : syracuseStep 2057615 = 3086423) B3086423
theorem B3171803 : Blo 912577 3171803 := bstep (se 1 (by rfl) ⟨2378852, by rfl⟩ : syracuseStep 3171803 = 4757705) B4757705
theorem B2319911 : Blo 912577 2319911 := bstep (se 1 (by rfl) ⟨1739933, by rfl⟩ : syracuseStep 2319911 = 3479867) B3479867
theorem B1369679 : Blo 912577 1369679 := bstep (se 1 (by rfl) ⟨1027259, by rfl⟩ : syracuseStep 1369679 = 2054519) B2054519
theorem B31712867 : Blo 912577 31712867 := bstep (se 1 (by rfl) ⟨23784650, by rfl⟩ : syracuseStep 31712867 = 47569301) B47569301
theorem B1369799 : Blo 912577 1369799 := bstep (se 1 (by rfl) ⟨1027349, by rfl⟩ : syracuseStep 1369799 = 2054699) B2054699
theorem B2057939 : Blo 912577 2057939 := bstep (se 1 (by rfl) ⟨1543454, by rfl⟩ : syracuseStep 2057939 = 3086909) B3086909
theorem B23422769 : Blo 912577 23422769 := bstep (se 2 (by rfl) ⟨8783538, by rfl⟩ : syracuseStep 23422769 = 17567077) B17567077
theorem B976735 : Blo 912577 976735 := bstep (se 1 (by rfl) ⟨732551, by rfl⟩ : syracuseStep 976735 = 1465103) B1465103
theorem B1369961 : Blo 912577 1369961 := bstep (se 2 (by rfl) ⟨513735, by rfl⟩ : syracuseStep 1369961 = 1027471) B1027471
theorem B3303287 : Blo 912577 3303287 := bstep (se 1 (by rfl) ⟨2477465, by rfl⟩ : syracuseStep 3303287 = 4954931) B4954931
theorem B1370039 : Blo 912577 1370039 := bstep (se 1 (by rfl) ⟨1027529, by rfl⟩ : syracuseStep 1370039 = 2055059) B2055059
theorem B1370075 : Blo 912577 1370075 := bstep (se 1 (by rfl) ⟨1027556, by rfl⟩ : syracuseStep 1370075 = 2055113) B2055113
theorem B14838065 : Blo 912577 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B6678937 : Blo 912577 6678937 := bstep (se 2 (by rfl) ⟨2504601, by rfl⟩ : syracuseStep 6678937 = 5009203) B5009203
theorem B1370543 : Blo 912577 1370543 := bstep (se 1 (by rfl) ⟨1027907, by rfl⟩ : syracuseStep 1370543 = 2055815) B2055815
theorem B1370633 : Blo 912577 1370633 := bstep (se 2 (by rfl) ⟨513987, by rfl⟩ : syracuseStep 1370633 = 1027975) B1027975
theorem B5204513 : Blo 912577 5204513 := bstep (se 2 (by rfl) ⟨1951692, by rfl⟩ : syracuseStep 5204513 = 3903385) B3903385
theorem B1370663 : Blo 912577 1370663 := bstep (se 1 (by rfl) ⟨1027997, by rfl⟩ : syracuseStep 1370663 = 2055995) B2055995
theorem B1370747 : Blo 912577 1370747 := bstep (se 1 (by rfl) ⟨1028060, by rfl⟩ : syracuseStep 1370747 = 2056121) B2056121
theorem B2058875 : Blo 912577 2058875 := bstep (se 1 (by rfl) ⟨1544156, by rfl⟩ : syracuseStep 2058875 = 3088313) B3088313
theorem B13200101 : Blo 912577 13200101 := bstep (se 4 (by rfl) ⟨1237509, by rfl⟩ : syracuseStep 13200101 = 2475019) B2475019
theorem B1370873 : Blo 912577 1370873 := bstep (se 2 (by rfl) ⟨514077, by rfl⟩ : syracuseStep 1370873 = 1028155) B1028155
theorem B2059001 : Blo 912577 2059001 := bstep (se 2 (by rfl) ⟨772125, by rfl⟩ : syracuseStep 2059001 = 1544251) B1544251
theorem B1370975 : Blo 912577 1370975 := bstep (se 1 (by rfl) ⟨1028231, by rfl⟩ : syracuseStep 1370975 = 2056463) B2056463
theorem B1370987 : Blo 912577 1370987 := bstep (se 1 (by rfl) ⟨1028240, by rfl⟩ : syracuseStep 1370987 = 2056481) B2056481
theorem B2059271 : Blo 912577 2059271 := bstep (se 1 (by rfl) ⟨1544453, by rfl⟩ : syracuseStep 2059271 = 3088907) B3088907
theorem B1371215 : Blo 912577 1371215 := bstep (se 1 (by rfl) ⟨1028411, by rfl⟩ : syracuseStep 1371215 = 2056823) B2056823
theorem B2059343 : Blo 912577 2059343 := bstep (se 1 (by rfl) ⟨1544507, by rfl⟩ : syracuseStep 2059343 = 3089015) B3089015
theorem B977999 : Blo 912577 977999 := bstep (se 1 (by rfl) ⟨733499, by rfl⟩ : syracuseStep 977999 = 1466999) B1466999
theorem B7040195 : Blo 912577 7040195 := bstep (se 1 (by rfl) ⟨5280146, by rfl⟩ : syracuseStep 7040195 = 10560293) B10560293
theorem B912583 : Blo 912577 912583 := bstep (se 1 (by rfl) ⟨684437, by rfl⟩ : syracuseStep 912583 = 1368875) B1368875
theorem B1371335 : Blo 912577 1371335 := bstep (se 1 (by rfl) ⟨1028501, by rfl⟩ : syracuseStep 1371335 = 2057003) B2057003
theorem B912603 : Blo 912577 912603 := bstep (se 1 (by rfl) ⟨684452, by rfl⟩ : syracuseStep 912603 = 1368905) B1368905
theorem B912679 : Blo 912577 912679 := bstep (se 1 (by rfl) ⟨684509, by rfl⟩ : syracuseStep 912679 = 1369019) B1369019
theorem B912719 : Blo 912577 912719 := bstep (se 1 (by rfl) ⟨684539, by rfl⟩ : syracuseStep 912719 = 1369079) B1369079
theorem B912735 : Blo 912577 912735 := bstep (se 1 (by rfl) ⟨684551, by rfl⟩ : syracuseStep 912735 = 1369103) B1369103
theorem B1371497 : Blo 912577 1371497 := bstep (se 2 (by rfl) ⟨514311, by rfl⟩ : syracuseStep 1371497 = 1028623) B1028623
theorem B912763 : Blo 912577 912763 := bstep (se 1 (by rfl) ⟨684572, by rfl⟩ : syracuseStep 912763 = 1369145) B1369145
theorem B912815 : Blo 912577 912815 := bstep (se 1 (by rfl) ⟨684611, by rfl⟩ : syracuseStep 912815 = 1369223) B1369223
theorem B1371575 : Blo 912577 1371575 := bstep (se 1 (by rfl) ⟨1028681, by rfl⟩ : syracuseStep 1371575 = 2057363) B2057363
theorem B912839 : Blo 912577 912839 := bstep (se 1 (by rfl) ⟨684629, by rfl⟩ : syracuseStep 912839 = 1369259) B1369259
theorem B912859 : Blo 912577 912859 := bstep (se 1 (by rfl) ⟨684644, by rfl⟩ : syracuseStep 912859 = 1369289) B1369289
theorem B1371611 : Blo 912577 1371611 := bstep (se 1 (by rfl) ⟨1028708, by rfl⟩ : syracuseStep 1371611 = 2057417) B2057417
theorem B2059739 : Blo 912577 2059739 := bstep (se 1 (by rfl) ⟨1544804, by rfl⟩ : syracuseStep 2059739 = 3089609) B3089609
theorem B912935 : Blo 912577 912935 := bstep (se 1 (by rfl) ⟨684701, by rfl⟩ : syracuseStep 912935 = 1369403) B1369403
theorem B912975 : Blo 912577 912975 := bstep (se 1 (by rfl) ⟨684731, by rfl⟩ : syracuseStep 912975 = 1369463) B1369463
theorem B912991 : Blo 912577 912991 := bstep (se 1 (by rfl) ⟨684743, by rfl⟩ : syracuseStep 912991 = 1369487) B1369487
theorem B913019 : Blo 912577 913019 := bstep (se 1 (by rfl) ⟨684764, by rfl⟩ : syracuseStep 913019 = 1369529) B1369529
theorem B913071 : Blo 912577 913071 := bstep (se 1 (by rfl) ⟨684803, by rfl⟩ : syracuseStep 913071 = 1369607) B1369607
theorem B9891517 : Blo 912577 9891517 := bstep (se 3 (by rfl) ⟨1854659, by rfl⟩ : syracuseStep 9891517 = 3709319) B3709319
theorem B913095 : Blo 912577 913095 := bstep (se 1 (by rfl) ⟨684821, by rfl⟩ : syracuseStep 913095 = 1369643) B1369643
theorem B913115 : Blo 912577 913115 := bstep (se 1 (by rfl) ⟨684836, by rfl⟩ : syracuseStep 913115 = 1369673) B1369673
theorem B913191 : Blo 912577 913191 := bstep (se 1 (by rfl) ⟨684893, by rfl⟩ : syracuseStep 913191 = 1369787) B1369787
theorem B4943683 : Blo 912577 4943683 := bstep (se 1 (by rfl) ⟨3707762, by rfl⟩ : syracuseStep 4943683 = 7415525) B7415525
theorem B913231 : Blo 912577 913231 := bstep (se 1 (by rfl) ⟨684923, by rfl⟩ : syracuseStep 913231 = 1369847) B1369847
theorem B913247 : Blo 912577 913247 := bstep (se 1 (by rfl) ⟨684935, by rfl⟩ : syracuseStep 913247 = 1369871) B1369871
theorem B3469175 : Blo 912577 3469175 := bstep (se 1 (by rfl) ⟨2601881, by rfl⟩ : syracuseStep 3469175 = 5203763) B5203763
theorem B913275 : Blo 912577 913275 := bstep (se 1 (by rfl) ⟨684956, by rfl⟩ : syracuseStep 913275 = 1369913) B1369913
theorem B5861281 : Blo 912577 5861281 := bstep (se 2 (by rfl) ⟨2197980, by rfl⟩ : syracuseStep 5861281 = 4395961) B4395961
theorem B17592227 : Blo 912577 17592227 := bstep (se 1 (by rfl) ⟨13194170, by rfl⟩ : syracuseStep 17592227 = 26388341) B26388341
theorem B913327 : Blo 912577 913327 := bstep (se 1 (by rfl) ⟨684995, by rfl⟩ : syracuseStep 913327 = 1369991) B1369991
theorem B1372079 : Blo 912577 1372079 := bstep (se 1 (by rfl) ⟨1029059, by rfl⟩ : syracuseStep 1372079 = 2058119) B2058119
theorem B2060207 : Blo 912577 2060207 := bstep (se 1 (by rfl) ⟨1545155, by rfl⟩ : syracuseStep 2060207 = 3090311) B3090311
theorem B913351 : Blo 912577 913351 := bstep (se 1 (by rfl) ⟨685013, by rfl⟩ : syracuseStep 913351 = 1370027) B1370027
theorem B913371 : Blo 912577 913371 := bstep (se 1 (by rfl) ⟨685028, by rfl⟩ : syracuseStep 913371 = 1370057) B1370057
theorem B1372169 : Blo 912577 1372169 := bstep (se 2 (by rfl) ⟨514563, by rfl⟩ : syracuseStep 1372169 = 1029127) B1029127
theorem B913447 : Blo 912577 913447 := bstep (se 1 (by rfl) ⟨685085, by rfl⟩ : syracuseStep 913447 = 1370171) B1370171
theorem B1372199 : Blo 912577 1372199 := bstep (se 1 (by rfl) ⟨1029149, by rfl⟩ : syracuseStep 1372199 = 2058299) B2058299
theorem B913487 : Blo 912577 913487 := bstep (se 1 (by rfl) ⟨685115, by rfl⟩ : syracuseStep 913487 = 1370231) B1370231
theorem B913503 : Blo 912577 913503 := bstep (se 1 (by rfl) ⟨685127, by rfl⟩ : syracuseStep 913503 = 1370255) B1370255
theorem B913531 : Blo 912577 913531 := bstep (se 1 (by rfl) ⟨685148, by rfl⟩ : syracuseStep 913531 = 1370297) B1370297
theorem B1372283 : Blo 912577 1372283 := bstep (se 1 (by rfl) ⟨1029212, by rfl⟩ : syracuseStep 1372283 = 2058425) B2058425
theorem B2060459 : Blo 912577 2060459 := bstep (se 1 (by rfl) ⟨1545344, by rfl⟩ : syracuseStep 2060459 = 3090689) B3090689
theorem B913583 : Blo 912577 913583 := bstep (se 1 (by rfl) ⟨685187, by rfl⟩ : syracuseStep 913583 = 1370375) B1370375
theorem B913607 : Blo 912577 913607 := bstep (se 1 (by rfl) ⟨685205, by rfl⟩ : syracuseStep 913607 = 1370411) B1370411
theorem B913627 : Blo 912577 913627 := bstep (se 1 (by rfl) ⟨685220, by rfl⟩ : syracuseStep 913627 = 1370441) B1370441
theorem B1372409 : Blo 912577 1372409 := bstep (se 2 (by rfl) ⟨514653, by rfl⟩ : syracuseStep 1372409 = 1029307) B1029307
theorem B913703 : Blo 912577 913703 := bstep (se 1 (by rfl) ⟨685277, by rfl⟩ : syracuseStep 913703 = 1370555) B1370555
theorem B913743 : Blo 912577 913743 := bstep (se 1 (by rfl) ⟨685307, by rfl⟩ : syracuseStep 913743 = 1370615) B1370615
theorem B913759 : Blo 912577 913759 := bstep (se 1 (by rfl) ⟨685319, by rfl⟩ : syracuseStep 913759 = 1370639) B1370639
theorem B1372511 : Blo 912577 1372511 := bstep (se 1 (by rfl) ⟨1029383, by rfl⟩ : syracuseStep 1372511 = 2058767) B2058767
theorem B1372523 : Blo 912577 1372523 := bstep (se 1 (by rfl) ⟨1029392, by rfl⟩ : syracuseStep 1372523 = 2058785) B2058785
theorem B913787 : Blo 912577 913787 := bstep (se 1 (by rfl) ⟨685340, by rfl⟩ : syracuseStep 913787 = 1370681) B1370681
theorem B3567997 : Blo 912577 3567997 := bstep (se 3 (by rfl) ⟨668999, by rfl⟩ : syracuseStep 3567997 = 1337999) B1337999
theorem B913839 : Blo 912577 913839 := bstep (se 1 (by rfl) ⟨685379, by rfl⟩ : syracuseStep 913839 = 1370759) B1370759
theorem B913863 : Blo 912577 913863 := bstep (se 1 (by rfl) ⟨685397, by rfl⟩ : syracuseStep 913863 = 1370795) B1370795
theorem B913883 : Blo 912577 913883 := bstep (se 1 (by rfl) ⟨685412, by rfl⟩ : syracuseStep 913883 = 1370825) B1370825
theorem B913959 : Blo 912577 913959 := bstep (se 1 (by rfl) ⟨685469, by rfl⟩ : syracuseStep 913959 = 1370939) B1370939
theorem B913999 : Blo 912577 913999 := bstep (se 1 (by rfl) ⟨685499, by rfl⟩ : syracuseStep 913999 = 1370999) B1370999
theorem B1372751 : Blo 912577 1372751 := bstep (se 1 (by rfl) ⟨1029563, by rfl⟩ : syracuseStep 1372751 = 2059127) B2059127
theorem B914015 : Blo 912577 914015 := bstep (se 1 (by rfl) ⟨685511, by rfl⟩ : syracuseStep 914015 = 1371023) B1371023
theorem B914043 : Blo 912577 914043 := bstep (se 1 (by rfl) ⟨685532, by rfl⟩ : syracuseStep 914043 = 1371065) B1371065
theorem B914095 : Blo 912577 914095 := bstep (se 1 (by rfl) ⟨685571, by rfl⟩ : syracuseStep 914095 = 1371143) B1371143
theorem B914119 : Blo 912577 914119 := bstep (se 1 (by rfl) ⟨685589, by rfl⟩ : syracuseStep 914119 = 1371179) B1371179
theorem B1372871 : Blo 912577 1372871 := bstep (se 1 (by rfl) ⟨1029653, by rfl⟩ : syracuseStep 1372871 = 2059307) B2059307
theorem B2060999 : Blo 912577 2060999 := bstep (se 1 (by rfl) ⟨1545749, by rfl⟩ : syracuseStep 2060999 = 3091499) B3091499
theorem B914139 : Blo 912577 914139 := bstep (se 1 (by rfl) ⟨685604, by rfl⟩ : syracuseStep 914139 = 1371209) B1371209
theorem B13202189 : Blo 912577 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B914215 : Blo 912577 914215 := bstep (se 1 (by rfl) ⟨685661, by rfl⟩ : syracuseStep 914215 = 1371323) B1371323
theorem B3470147 : Blo 912577 3470147 := bstep (se 1 (by rfl) ⟨2602610, by rfl⟩ : syracuseStep 3470147 = 5205221) B5205221
theorem B914255 : Blo 912577 914255 := bstep (se 1 (by rfl) ⟨685691, by rfl⟩ : syracuseStep 914255 = 1371383) B1371383
theorem B1733471 : Blo 912577 1733471 := bstep (se 1 (by rfl) ⟨1300103, by rfl⟩ : syracuseStep 1733471 = 2600207) B2600207
theorem B914271 : Blo 912577 914271 := bstep (se 1 (by rfl) ⟨685703, by rfl⟩ : syracuseStep 914271 = 1371407) B1371407
theorem B1373033 : Blo 912577 1373033 := bstep (se 2 (by rfl) ⟨514887, by rfl⟩ : syracuseStep 1373033 = 1029775) B1029775
theorem B914299 : Blo 912577 914299 := bstep (se 1 (by rfl) ⟨685724, by rfl⟩ : syracuseStep 914299 = 1371449) B1371449
theorem B914351 : Blo 912577 914351 := bstep (se 1 (by rfl) ⟨685763, by rfl⟩ : syracuseStep 914351 = 1371527) B1371527
theorem B1373111 : Blo 912577 1373111 := bstep (se 1 (by rfl) ⟨1029833, by rfl⟩ : syracuseStep 1373111 = 2059667) B2059667
theorem B914375 : Blo 912577 914375 := bstep (se 1 (by rfl) ⟨685781, by rfl⟩ : syracuseStep 914375 = 1371563) B1371563
theorem B914395 : Blo 912577 914395 := bstep (se 1 (by rfl) ⟨685796, by rfl⟩ : syracuseStep 914395 = 1371593) B1371593
theorem B1373147 : Blo 912577 1373147 := bstep (se 1 (by rfl) ⟨1029860, by rfl⟩ : syracuseStep 1373147 = 2059721) B2059721
theorem B914471 : Blo 912577 914471 := bstep (se 1 (by rfl) ⟨685853, by rfl⟩ : syracuseStep 914471 = 1371707) B1371707
theorem B914511 : Blo 912577 914511 := bstep (se 1 (by rfl) ⟨685883, by rfl⟩ : syracuseStep 914511 = 1371767) B1371767
theorem B914527 : Blo 912577 914527 := bstep (se 1 (by rfl) ⟨685895, by rfl⟩ : syracuseStep 914527 = 1371791) B1371791
theorem B914555 : Blo 912577 914555 := bstep (se 1 (by rfl) ⟨685916, by rfl⟩ : syracuseStep 914555 = 1371833) B1371833
theorem B914607 : Blo 912577 914607 := bstep (se 1 (by rfl) ⟨685955, by rfl⟩ : syracuseStep 914607 = 1371911) B1371911
theorem B914631 : Blo 912577 914631 := bstep (se 1 (by rfl) ⟨685973, by rfl⟩ : syracuseStep 914631 = 1371947) B1371947
theorem B914651 : Blo 912577 914651 := bstep (se 1 (by rfl) ⟨685988, by rfl⟩ : syracuseStep 914651 = 1371977) B1371977
theorem B1733881 : Blo 912577 1733881 := bstep (se 2 (by rfl) ⟨650205, by rfl⟩ : syracuseStep 1733881 = 1300411) B1300411
theorem B914727 : Blo 912577 914727 := bstep (se 1 (by rfl) ⟨686045, by rfl⟩ : syracuseStep 914727 = 1372091) B1372091
theorem B914767 : Blo 912577 914767 := bstep (se 1 (by rfl) ⟨686075, by rfl⟩ : syracuseStep 914767 = 1372151) B1372151
theorem B914783 : Blo 912577 914783 := bstep (se 1 (by rfl) ⟨686087, by rfl⟩ : syracuseStep 914783 = 1372175) B1372175
theorem B914811 : Blo 912577 914811 := bstep (se 1 (by rfl) ⟨686108, by rfl⟩ : syracuseStep 914811 = 1372217) B1372217
theorem B914863 : Blo 912577 914863 := bstep (se 1 (by rfl) ⟨686147, by rfl⟩ : syracuseStep 914863 = 1372295) B1372295
theorem B1373615 : Blo 912577 1373615 := bstep (se 1 (by rfl) ⟨1030211, by rfl⟩ : syracuseStep 1373615 = 2060423) B2060423
theorem B914887 : Blo 912577 914887 := bstep (se 1 (by rfl) ⟨686165, by rfl⟩ : syracuseStep 914887 = 1372331) B1372331
theorem B914907 : Blo 912577 914907 := bstep (se 1 (by rfl) ⟨686180, by rfl⟩ : syracuseStep 914907 = 1372361) B1372361
theorem B1373705 : Blo 912577 1373705 := bstep (se 2 (by rfl) ⟨515139, by rfl⟩ : syracuseStep 1373705 = 1030279) B1030279
theorem B914983 : Blo 912577 914983 := bstep (se 1 (by rfl) ⟨686237, by rfl⟩ : syracuseStep 914983 = 1372475) B1372475
theorem B1373735 : Blo 912577 1373735 := bstep (se 1 (by rfl) ⟨1030301, by rfl⟩ : syracuseStep 1373735 = 2060603) B2060603
theorem B2061863 : Blo 912577 2061863 := bstep (se 1 (by rfl) ⟨1546397, by rfl⟩ : syracuseStep 2061863 = 3092795) B3092795
theorem B1734223 : Blo 912577 1734223 := bstep (se 1 (by rfl) ⟨1300667, by rfl⟩ : syracuseStep 1734223 = 2601335) B2601335
theorem B915023 : Blo 912577 915023 := bstep (se 1 (by rfl) ⟨686267, by rfl⟩ : syracuseStep 915023 = 1372535) B1372535
theorem B915039 : Blo 912577 915039 := bstep (se 1 (by rfl) ⟨686279, by rfl⟩ : syracuseStep 915039 = 1372559) B1372559
theorem B915067 : Blo 912577 915067 := bstep (se 1 (by rfl) ⟨686300, by rfl⟩ : syracuseStep 915067 = 1372601) B1372601
theorem B1373819 : Blo 912577 1373819 := bstep (se 1 (by rfl) ⟨1030364, by rfl⟩ : syracuseStep 1373819 = 2060729) B2060729
theorem B915119 : Blo 912577 915119 := bstep (se 1 (by rfl) ⟨686339, by rfl⟩ : syracuseStep 915119 = 1372679) B1372679
theorem B915143 : Blo 912577 915143 := bstep (se 1 (by rfl) ⟨686357, by rfl⟩ : syracuseStep 915143 = 1372715) B1372715
theorem B915163 : Blo 912577 915163 := bstep (se 1 (by rfl) ⟨686372, by rfl⟩ : syracuseStep 915163 = 1372745) B1372745
theorem B142571249 : Blo 912577 142571249 := bstep (se 2 (by rfl) ⟨53464218, by rfl⟩ : syracuseStep 142571249 = 106928437) B106928437
theorem B1373945 : Blo 912577 1373945 := bstep (se 2 (by rfl) ⟨515229, by rfl⟩ : syracuseStep 1373945 = 1030459) B1030459
theorem B3471133 : Blo 912577 3471133 := bstep (se 3 (by rfl) ⟨650837, by rfl⟩ : syracuseStep 3471133 = 1301675) B1301675
theorem B915239 : Blo 912577 915239 := bstep (se 1 (by rfl) ⟨686429, by rfl⟩ : syracuseStep 915239 = 1372859) B1372859
theorem B1734473 : Blo 912577 1734473 := bstep (se 2 (by rfl) ⟨650427, by rfl⟩ : syracuseStep 1734473 = 1300855) B1300855
theorem B915279 : Blo 912577 915279 := bstep (se 1 (by rfl) ⟨686459, by rfl⟩ : syracuseStep 915279 = 1372919) B1372919
theorem B915295 : Blo 912577 915295 := bstep (se 1 (by rfl) ⟨686471, by rfl⟩ : syracuseStep 915295 = 1372943) B1372943
theorem B1374047 : Blo 912577 1374047 := bstep (se 1 (by rfl) ⟨1030535, by rfl⟩ : syracuseStep 1374047 = 2061071) B2061071
theorem B1374059 : Blo 912577 1374059 := bstep (se 1 (by rfl) ⟨1030544, by rfl⟩ : syracuseStep 1374059 = 2061089) B2061089
theorem B2062187 : Blo 912577 2062187 := bstep (se 1 (by rfl) ⟨1546640, by rfl⟩ : syracuseStep 2062187 = 3093281) B3093281
theorem B915323 : Blo 912577 915323 := bstep (se 1 (by rfl) ⟨686492, by rfl⟩ : syracuseStep 915323 = 1372985) B1372985
theorem B2062241 : Blo 912577 2062241 := bstep (se 2 (by rfl) ⟨773340, by rfl⟩ : syracuseStep 2062241 = 1546681) B1546681
theorem B915375 : Blo 912577 915375 := bstep (se 1 (by rfl) ⟨686531, by rfl⟩ : syracuseStep 915375 = 1373063) B1373063
theorem B915399 : Blo 912577 915399 := bstep (se 1 (by rfl) ⟨686549, by rfl⟩ : syracuseStep 915399 = 1373099) B1373099
theorem B9402317 : Blo 912577 9402317 := bstep (se 3 (by rfl) ⟨1762934, by rfl⟩ : syracuseStep 9402317 = 3525869) B3525869
theorem B915419 : Blo 912577 915419 := bstep (se 1 (by rfl) ⟨686564, by rfl⟩ : syracuseStep 915419 = 1373129) B1373129
theorem B915495 : Blo 912577 915495 := bstep (se 1 (by rfl) ⟨686621, by rfl⟩ : syracuseStep 915495 = 1373243) B1373243
theorem B915535 : Blo 912577 915535 := bstep (se 1 (by rfl) ⟨686651, by rfl⟩ : syracuseStep 915535 = 1373303) B1373303
theorem B1374287 : Blo 912577 1374287 := bstep (se 1 (by rfl) ⟨1030715, by rfl⟩ : syracuseStep 1374287 = 2061431) B2061431
theorem B915551 : Blo 912577 915551 := bstep (se 1 (by rfl) ⟨686663, by rfl⟩ : syracuseStep 915551 = 1373327) B1373327
theorem B915579 : Blo 912577 915579 := bstep (se 1 (by rfl) ⟨686684, by rfl⟩ : syracuseStep 915579 = 1373369) B1373369
theorem B915631 : Blo 912577 915631 := bstep (se 1 (by rfl) ⟨686723, by rfl⟩ : syracuseStep 915631 = 1373447) B1373447
theorem B915655 : Blo 912577 915655 := bstep (se 1 (by rfl) ⟨686741, by rfl⟩ : syracuseStep 915655 = 1373483) B1373483
theorem B1374407 : Blo 912577 1374407 := bstep (se 1 (by rfl) ⟨1030805, by rfl⟩ : syracuseStep 1374407 = 2061611) B2061611
theorem B915675 : Blo 912577 915675 := bstep (se 1 (by rfl) ⟨686756, by rfl⟩ : syracuseStep 915675 = 1373513) B1373513
theorem B915751 : Blo 912577 915751 := bstep (se 1 (by rfl) ⟨686813, by rfl⟩ : syracuseStep 915751 = 1373627) B1373627
theorem B915791 : Blo 912577 915791 := bstep (se 1 (by rfl) ⟨686843, by rfl⟩ : syracuseStep 915791 = 1373687) B1373687
theorem B915807 : Blo 912577 915807 := bstep (se 1 (by rfl) ⟨686855, by rfl⟩ : syracuseStep 915807 = 1373711) B1373711
theorem B1374569 : Blo 912577 1374569 := bstep (se 2 (by rfl) ⟨515463, by rfl⟩ : syracuseStep 1374569 = 1030927) B1030927
theorem B915835 : Blo 912577 915835 := bstep (se 1 (by rfl) ⟨686876, by rfl⟩ : syracuseStep 915835 = 1373753) B1373753
theorem B915887 : Blo 912577 915887 := bstep (se 1 (by rfl) ⟨686915, by rfl⟩ : syracuseStep 915887 = 1373831) B1373831
theorem B1374647 : Blo 912577 1374647 := bstep (se 1 (by rfl) ⟨1030985, by rfl⟩ : syracuseStep 1374647 = 2061971) B2061971
theorem B915911 : Blo 912577 915911 := bstep (se 1 (by rfl) ⟨686933, by rfl⟩ : syracuseStep 915911 = 1373867) B1373867
theorem B915931 : Blo 912577 915931 := bstep (se 1 (by rfl) ⟨686948, by rfl⟩ : syracuseStep 915931 = 1373897) B1373897
theorem B1374683 : Blo 912577 1374683 := bstep (se 1 (by rfl) ⟨1031012, by rfl⟩ : syracuseStep 1374683 = 2062025) B2062025
theorem B916007 : Blo 912577 916007 := bstep (se 1 (by rfl) ⟨687005, by rfl⟩ : syracuseStep 916007 = 1374011) B1374011
theorem B916047 : Blo 912577 916047 := bstep (se 1 (by rfl) ⟨687035, by rfl⟩ : syracuseStep 916047 = 1374071) B1374071
theorem B916063 : Blo 912577 916063 := bstep (se 1 (by rfl) ⟨687047, by rfl⟩ : syracuseStep 916063 = 1374095) B1374095
theorem B916091 : Blo 912577 916091 := bstep (se 1 (by rfl) ⟨687068, by rfl⟩ : syracuseStep 916091 = 1374137) B1374137
theorem B1735339 : Blo 912577 1735339 := bstep (se 1 (by rfl) ⟨1301504, by rfl⟩ : syracuseStep 1735339 = 2603009) B2603009
theorem B916143 : Blo 912577 916143 := bstep (se 1 (by rfl) ⟨687107, by rfl⟩ : syracuseStep 916143 = 1374215) B1374215
theorem B916167 : Blo 912577 916167 := bstep (se 1 (by rfl) ⟨687125, by rfl⟩ : syracuseStep 916167 = 1374251) B1374251
theorem B5569235 : Blo 912577 5569235 := bstep (se 1 (by rfl) ⟨4176926, by rfl⟩ : syracuseStep 5569235 = 8353853) B8353853
theorem B916187 : Blo 912577 916187 := bstep (se 1 (by rfl) ⟨687140, by rfl⟩ : syracuseStep 916187 = 1374281) B1374281
theorem B1735415 : Blo 912577 1735415 := bstep (se 1 (by rfl) ⟨1301561, by rfl⟩ : syracuseStep 1735415 = 2603123) B2603123
theorem B916263 : Blo 912577 916263 := bstep (se 1 (by rfl) ⟨687197, by rfl⟩ : syracuseStep 916263 = 1374395) B1374395
theorem B916303 : Blo 912577 916303 := bstep (se 1 (by rfl) ⟨687227, by rfl⟩ : syracuseStep 916303 = 1374455) B1374455
theorem B916319 : Blo 912577 916319 := bstep (se 1 (by rfl) ⟨687239, by rfl⟩ : syracuseStep 916319 = 1374479) B1374479
theorem B916347 : Blo 912577 916347 := bstep (se 1 (by rfl) ⟨687260, by rfl⟩ : syracuseStep 916347 = 1374521) B1374521
theorem B916399 : Blo 912577 916399 := bstep (se 1 (by rfl) ⟨687299, by rfl⟩ : syracuseStep 916399 = 1374599) B1374599
theorem B916423 : Blo 912577 916423 := bstep (se 1 (by rfl) ⟨687317, by rfl⟩ : syracuseStep 916423 = 1374635) B1374635
theorem B1735643 : Blo 912577 1735643 := bstep (se 1 (by rfl) ⟨1301732, by rfl⟩ : syracuseStep 1735643 = 2603465) B2603465
theorem B916443 : Blo 912577 916443 := bstep (se 1 (by rfl) ⟨687332, by rfl⟩ : syracuseStep 916443 = 1374665) B1374665
theorem B916519 : Blo 912577 916519 := bstep (se 1 (by rfl) ⟨687389, by rfl⟩ : syracuseStep 916519 = 1374779) B1374779
theorem B916559 : Blo 912577 916559 := bstep (se 1 (by rfl) ⟨687419, by rfl⟩ : syracuseStep 916559 = 1374839) B1374839
theorem B916575 : Blo 912577 916575 := bstep (se 1 (by rfl) ⟨687431, by rfl⟩ : syracuseStep 916575 = 1374863) B1374863
theorem B6945911 : Blo 912577 6945911 := bstep (se 1 (by rfl) ⟨5209433, by rfl⟩ : syracuseStep 6945911 = 10418867) B10418867
theorem B8781047 : Blo 912577 8781047 := bstep (se 1 (by rfl) ⟨6585785, by rfl⟩ : syracuseStep 8781047 = 13171571) B13171571
theorem B11697443 : Blo 912577 11697443 := bstep (se 1 (by rfl) ⟨8773082, by rfl⟩ : syracuseStep 11697443 = 17546165) B17546165
theorem B14056739 : Blo 912577 14056739 := bstep (se 1 (by rfl) ⟨10542554, by rfl⟩ : syracuseStep 14056739 = 21085109) B21085109
theorem B3702557 : Blo 912577 3702557 := bstep (se 3 (by rfl) ⟨694229, by rfl⟩ : syracuseStep 3702557 = 1388459) B1388459
theorem B6684551 : Blo 912577 6684551 := bstep (se 1 (by rfl) ⟨5013413, by rfl⟩ : syracuseStep 6684551 = 10026827) B10026827
theorem B2195387 : Blo 912577 2195387 := bstep (se 1 (by rfl) ⟨1646540, by rfl⟩ : syracuseStep 2195387 = 3293081) B3293081
theorem B10420325 : Blo 912577 10420325 := bstep (se 4 (by rfl) ⟨976905, by rfl⟩ : syracuseStep 10420325 = 1953811) B1953811
theorem B1540201 : Blo 912577 1540201 := bstep (se 2 (by rfl) ⟨577575, by rfl⟩ : syracuseStep 1540201 = 1155151) B1155151
theorem B3670447 : Blo 912577 3670447 := bstep (se 1 (by rfl) ⟨2752835, by rfl⟩ : syracuseStep 3670447 = 5505671) B5505671
theorem B2195963 : Blo 912577 2195963 := bstep (se 1 (by rfl) ⟨1646972, by rfl⟩ : syracuseStep 2195963 = 3293945) B3293945
theorem B4621049 : Blo 912577 4621049 := bstep (se 2 (by rfl) ⟨1732893, by rfl⟩ : syracuseStep 4621049 = 3465787) B3465787
theorem B2196443 : Blo 912577 2196443 := bstep (se 1 (by rfl) ⟨1647332, by rfl⟩ : syracuseStep 2196443 = 3294665) B3294665
theorem B1541929 : Blo 912577 1541929 := bstep (se 2 (by rfl) ⟨578223, by rfl⟩ : syracuseStep 1541929 = 1156447) B1156447
theorem B5211985 : Blo 912577 5211985 := bstep (se 2 (by rfl) ⟨1954494, by rfl⟩ : syracuseStep 5211985 = 3908989) B3908989
theorem B1542719 : Blo 912577 1542719 := bstep (se 1 (by rfl) ⟨1157039, by rfl⟩ : syracuseStep 1542719 = 2314079) B2314079
theorem B3082859 : Blo 912577 3082859 := bstep (se 1 (by rfl) ⟨2312144, by rfl⟩ : syracuseStep 3082859 = 4624289) B4624289
theorem B3902327 : Blo 912577 3902327 := bstep (se 1 (by rfl) ⟨2926745, by rfl⟩ : syracuseStep 3902327 = 5853491) B5853491
theorem B3083453 : Blo 912577 3083453 := bstep (se 3 (by rfl) ⟨578147, by rfl⟩ : syracuseStep 3083453 = 1156295) B1156295
theorem B101682377 : Blo 912577 101682377 := bstep (se 2 (by rfl) ⟨38130891, by rfl⟩ : syracuseStep 101682377 = 76261783) B76261783
theorem B9374939 : Blo 912577 9374939 := bstep (se 1 (by rfl) ⟨7031204, by rfl⟩ : syracuseStep 9374939 = 14062409) B14062409
theorem B3706075 : Blo 912577 3706075 := bstep (se 1 (by rfl) ⟨2779556, by rfl⟩ : syracuseStep 3706075 = 5559113) B5559113
theorem B1543387 : Blo 912577 1543387 := bstep (se 1 (by rfl) ⟨1157540, by rfl⟩ : syracuseStep 1543387 = 2315081) B2315081
theorem B42863863 : Blo 912577 42863863 := bstep (se 1 (by rfl) ⟨32147897, by rfl⟩ : syracuseStep 42863863 = 64295795) B64295795
theorem B4623803 : Blo 912577 4623803 := bstep (se 1 (by rfl) ⟨3467852, by rfl⟩ : syracuseStep 4623803 = 6935705) B6935705
theorem B3476951 : Blo 912577 3476951 := bstep (se 1 (by rfl) ⟨2607713, by rfl⟩ : syracuseStep 3476951 = 5215427) B5215427
theorem B4394731 : Blo 912577 4394731 := bstep (se 1 (by rfl) ⟨3296048, by rfl⟩ : syracuseStep 4394731 = 6592097) B6592097
theorem B8458141 : Blo 912577 8458141 := bstep (se 3 (by rfl) ⟨1585901, by rfl⟩ : syracuseStep 8458141 = 3171803) B3171803
theorem B1544143 : Blo 912577 1544143 := bstep (se 1 (by rfl) ⟨1158107, by rfl⟩ : syracuseStep 1544143 = 2316215) B2316215
theorem B3903659 : Blo 912577 3903659 := bstep (se 1 (by rfl) ⟨2927744, by rfl⟩ : syracuseStep 3903659 = 5855489) B5855489
theorem B3904001 : Blo 912577 3904001 := bstep (se 2 (by rfl) ⟨1464000, by rfl⟩ : syracuseStep 3904001 = 2928001) B2928001
theorem B8327731 : Blo 912577 8327731 := bstep (se 1 (by rfl) ⟨6245798, by rfl⟩ : syracuseStep 8327731 = 12491597) B12491597
theorem B1544825 : Blo 912577 1544825 := bstep (se 2 (by rfl) ⟨579309, by rfl⟩ : syracuseStep 1544825 = 1158619) B1158619
theorem B1544879 : Blo 912577 1544879 := bstep (se 1 (by rfl) ⟨1158659, by rfl⟩ : syracuseStep 1544879 = 2317319) B2317319
theorem B4625099 : Blo 912577 4625099 := bstep (se 1 (by rfl) ⟨3468824, by rfl⟩ : syracuseStep 4625099 = 6937649) B6937649
theorem B5870303 : Blo 912577 5870303 := bstep (se 1 (by rfl) ⟨4402727, by rfl⟩ : syracuseStep 5870303 = 8805455) B8805455
theorem B4625261 : Blo 912577 4625261 := bstep (se 3 (by rfl) ⟨867236, by rfl⟩ : syracuseStep 4625261 = 1734473) B1734473
theorem B4756333 : Blo 912577 4756333 := bstep (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) B1783625
theorem B1545115 : Blo 912577 1545115 := bstep (se 1 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 1545115 = 2317673) B2317673
theorem B2200567 : Blo 912577 2200567 := bstep (se 1 (by rfl) ⟨1650425, by rfl⟩ : syracuseStep 2200567 = 3300851) B3300851
theorem B8787001 : Blo 912577 8787001 := bstep (se 2 (by rfl) ⟨3295125, by rfl⟩ : syracuseStep 8787001 = 6590251) B6590251
theorem B6591577 : Blo 912577 6591577 := bstep (se 2 (by rfl) ⟨2471841, by rfl⟩ : syracuseStep 6591577 = 4943683) B4943683
theorem B3478727 : Blo 912577 3478727 := bstep (se 1 (by rfl) ⟨2609045, by rfl⟩ : syracuseStep 3478727 = 5218091) B5218091
theorem B4691159 : Blo 912577 4691159 := bstep (se 1 (by rfl) ⟨3518369, by rfl⟩ : syracuseStep 4691159 = 7036739) B7036739
theorem B18748865 : Blo 912577 18748865 := bstep (se 2 (by rfl) ⟨7030824, by rfl⟩ : syracuseStep 18748865 = 14061649) B14061649
theorem B4757329 : Blo 912577 4757329 := bstep (se 2 (by rfl) ⟨1783998, by rfl⟩ : syracuseStep 4757329 = 3567997) B3567997
theorem B8329189 : Blo 912577 8329189 := bstep (se 4 (by rfl) ⟨780861, by rfl⟩ : syracuseStep 8329189 = 1561723) B1561723
theorem B3086369 : Blo 912577 3086369 := bstep (se 2 (by rfl) ⟨1157388, by rfl⟩ : syracuseStep 3086369 = 2314777) B2314777
theorem B1546607 : Blo 912577 1546607 := bstep (se 1 (by rfl) ⟨1159955, by rfl⟩ : syracuseStep 1546607 = 2319911) B2319911
theorem B21141911 : Blo 912577 21141911 := bstep (se 1 (by rfl) ⟨15856433, by rfl⟩ : syracuseStep 21141911 = 31712867) B31712867
theorem B1645127 : Blo 912577 1645127 := bstep (se 1 (by rfl) ⟨1233845, by rfl⟩ : syracuseStep 1645127 = 2467691) B2467691
theorem B2202191 : Blo 912577 2202191 := bstep (se 1 (by rfl) ⟨1651643, by rfl⟩ : syracuseStep 2202191 = 3303287) B3303287
theorem B6954173 : Blo 912577 6954173 := bstep (se 3 (by rfl) ⟨1303907, by rfl⟩ : syracuseStep 6954173 = 2607815) B2607815
theorem B63282485 : Blo 912577 63282485 := bstep (se 5 (by rfl) ⟨2966366, by rfl⟩ : syracuseStep 63282485 = 5932733) B5932733
theorem B7413059 : Blo 912577 7413059 := bstep (se 1 (by rfl) ⟨5559794, by rfl⟩ : syracuseStep 7413059 = 11119589) B11119589
theorem B4693463 : Blo 912577 4693463 := bstep (se 1 (by rfl) ⟨3520097, by rfl⟩ : syracuseStep 4693463 = 7040195) B7040195
theorem B5217817 : Blo 912577 5217817 := bstep (se 2 (by rfl) ⟨1956681, by rfl⟩ : syracuseStep 5217817 = 3913363) B3913363
theorem B4628177 : Blo 912577 4628177 := bstep (se 2 (by rfl) ⟨1735566, by rfl⟩ : syracuseStep 4628177 = 3471133) B3471133
theorem B3907385 : Blo 912577 3907385 := bstep (se 2 (by rfl) ⟨1465269, by rfl⟩ : syracuseStep 3907385 = 2930539) B2930539
theorem B11739269 : Blo 912577 11739269 := bstep (se 4 (by rfl) ⟨1100556, by rfl⟩ : syracuseStep 11739269 = 2201113) B2201113
theorem B1155647 : Blo 912577 1155647 := bstep (se 1 (by rfl) ⟨866735, by rfl⟩ : syracuseStep 1155647 = 1733471) B1733471
theorem B10429073 : Blo 912577 10429073 := bstep (se 2 (by rfl) ⟨3910902, by rfl⟩ : syracuseStep 10429073 = 7821805) B7821805
theorem B9904841 : Blo 912577 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B3089231 : Blo 912577 3089231 := bstep (se 1 (by rfl) ⟨2316923, by rfl⟩ : syracuseStep 3089231 = 4633847) B4633847
theorem B3089555 : Blo 912577 3089555 := bstep (se 1 (by rfl) ⟨2317166, by rfl⟩ : syracuseStep 3089555 = 4634333) B4634333
theorem B6268211 : Blo 912577 6268211 := bstep (se 1 (by rfl) ⟨4701158, by rfl⟩ : syracuseStep 6268211 = 9402317) B9402317
theorem B3089825 : Blo 912577 3089825 := bstep (se 2 (by rfl) ⟨1158684, by rfl⟩ : syracuseStep 3089825 = 2317369) B2317369
theorem B35563013 : Blo 912577 35563013 := bstep (se 4 (by rfl) ⟨3334032, by rfl⟩ : syracuseStep 35563013 = 6668065) B6668065
theorem B3712823 : Blo 912577 3712823 := bstep (se 1 (by rfl) ⟨2784617, by rfl⟩ : syracuseStep 3712823 = 5569235) B5569235
theorem B1156943 : Blo 912577 1156943 := bstep (se 1 (by rfl) ⟨867707, by rfl⟩ : syracuseStep 1156943 = 1735415) B1735415
theorem B4171601 : Blo 912577 4171601 := bstep (se 2 (by rfl) ⟨1564350, by rfl⟩ : syracuseStep 4171601 = 3128701) B3128701
theorem B1157095 : Blo 912577 1157095 := bstep (se 1 (by rfl) ⟨867821, by rfl⟩ : syracuseStep 1157095 = 1735643) B1735643
theorem B9873485 : Blo 912577 9873485 := bstep (se 3 (by rfl) ⟨1851278, by rfl⟩ : syracuseStep 9873485 = 3702557) B3702557
theorem B4630607 : Blo 912577 4630607 := bstep (se 1 (by rfl) ⟨3472955, by rfl⟩ : syracuseStep 4630607 = 6945911) B6945911
theorem B1780193 : Blo 912577 1780193 := bstep (se 2 (by rfl) ⟨667572, by rfl⟩ : syracuseStep 1780193 = 1335145) B1335145
theorem B14821967 : Blo 912577 14821967 := bstep (se 1 (by rfl) ⟨11116475, by rfl⟩ : syracuseStep 14821967 = 22232951) B22232951
theorem B1026895 : Blo 912577 1026895 := bstep (se 1 (by rfl) ⟨770171, by rfl⟩ : syracuseStep 1026895 = 1540343) B1540343
theorem B14855183 : Blo 912577 14855183 := bstep (se 1 (by rfl) ⟨11141387, by rfl⟩ : syracuseStep 14855183 = 22282775) B22282775
theorem B5287027 : Blo 912577 5287027 := bstep (se 1 (by rfl) ⟨3965270, by rfl⟩ : syracuseStep 5287027 = 7930541) B7930541
theorem B2600059 : Blo 912577 2600059 := bstep (se 1 (by rfl) ⟨1950044, by rfl⟩ : syracuseStep 2600059 = 3900089) B3900089
theorem B4631741 : Blo 912577 4631741 := bstep (se 3 (by rfl) ⟨868451, by rfl⟩ : syracuseStep 4631741 = 1736903) B1736903
theorem B1027291 : Blo 912577 1027291 := bstep (se 1 (by rfl) ⟨770468, by rfl⟩ : syracuseStep 1027291 = 1540937) B1540937
theorem B10431989 : Blo 912577 10431989 := bstep (se 5 (by rfl) ⟨488999, by rfl⟩ : syracuseStep 10431989 = 977999) B977999
theorem B1027579 : Blo 912577 1027579 := bstep (se 1 (by rfl) ⟨770684, by rfl⟩ : syracuseStep 1027579 = 1541369) B1541369
theorem B2928143 : Blo 912577 2928143 := bstep (se 1 (by rfl) ⟨2196107, by rfl⟩ : syracuseStep 2928143 = 4392215) B4392215
theorem B1027759 : Blo 912577 1027759 := bstep (se 1 (by rfl) ⟨770819, by rfl⟩ : syracuseStep 1027759 = 1541639) B1541639
theorem B9383633 : Blo 912577 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B3911435 : Blo 912577 3911435 := bstep (se 1 (by rfl) ⟨2933576, by rfl⟩ : syracuseStep 3911435 = 5867153) B5867153
theorem B1028047 : Blo 912577 1028047 := bstep (se 1 (by rfl) ⟨771035, by rfl⟩ : syracuseStep 1028047 = 1542071) B1542071
theorem B1650793 : Blo 912577 1650793 := bstep (se 2 (by rfl) ⟨619047, by rfl⟩ : syracuseStep 1650793 = 1238095) B1238095
theorem B1028443 : Blo 912577 1028443 := bstep (se 1 (by rfl) ⟨771332, by rfl⟩ : syracuseStep 1028443 = 1542665) B1542665
theorem B1159535 : Blo 912577 1159535 := bstep (se 1 (by rfl) ⟨869651, by rfl⟩ : syracuseStep 1159535 = 1739303) B1739303
theorem B1159591 : Blo 912577 1159591 := bstep (se 1 (by rfl) ⟨869693, by rfl⟩ : syracuseStep 1159591 = 1739387) B1739387
theorem B2601391 : Blo 912577 2601391 := bstep (se 1 (by rfl) ⟨1951043, by rfl⟩ : syracuseStep 2601391 = 3902087) B3902087
theorem B1028551 : Blo 912577 1028551 := bstep (se 1 (by rfl) ⟨771413, by rfl⟩ : syracuseStep 1028551 = 1542827) B1542827
theorem B3093011 : Blo 912577 3093011 := bstep (se 1 (by rfl) ⟨2319758, by rfl⟩ : syracuseStep 3093011 = 4639517) B4639517
theorem B15872561 : Blo 912577 15872561 := bstep (se 2 (by rfl) ⟨5952210, by rfl⟩ : syracuseStep 15872561 = 11904421) B11904421
theorem B1880639 : Blo 912577 1880639 := bstep (se 1 (by rfl) ⟨1410479, by rfl⟩ : syracuseStep 1880639 = 2820959) B2820959
theorem B3912407 : Blo 912577 3912407 := bstep (se 1 (by rfl) ⟨2934305, by rfl⟩ : syracuseStep 3912407 = 5868611) B5868611
theorem B1159915 : Blo 912577 1159915 := bstep (se 1 (by rfl) ⟨869936, by rfl⟩ : syracuseStep 1159915 = 1739873) B1739873
theorem B2470675 : Blo 912577 2470675 := bstep (se 1 (by rfl) ⟨1853006, by rfl⟩ : syracuseStep 2470675 = 3706013) B3706013
theorem B1028911 : Blo 912577 1028911 := bstep (se 1 (by rfl) ⟨771683, by rfl⟩ : syracuseStep 1028911 = 1543367) B1543367
theorem B1029019 : Blo 912577 1029019 := bstep (se 1 (by rfl) ⟨771764, by rfl⟩ : syracuseStep 1029019 = 1543529) B1543529
theorem B3290311 : Blo 912577 3290311 := bstep (se 1 (by rfl) ⟨2467733, by rfl⟩ : syracuseStep 3290311 = 4935467) B4935467
theorem B1029415 : Blo 912577 1029415 := bstep (se 1 (by rfl) ⟨772061, by rfl⟩ : syracuseStep 1029415 = 1544123) B1544123
theorem B1029487 : Blo 912577 1029487 := bstep (se 1 (by rfl) ⟨772115, by rfl⟩ : syracuseStep 1029487 = 1544231) B1544231
theorem B1029703 : Blo 912577 1029703 := bstep (se 1 (by rfl) ⟨772277, by rfl⟩ : syracuseStep 1029703 = 1544555) B1544555
theorem B4634657 : Blo 912577 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B4634819 : Blo 912577 4634819 := bstep (se 1 (by rfl) ⟨3476114, by rfl⟩ : syracuseStep 4634819 = 6952229) B6952229
theorem B36190475 : Blo 912577 36190475 := bstep (se 1 (by rfl) ⟨27142856, by rfl⟩ : syracuseStep 36190475 = 54285713) B54285713
theorem B35633459 : Blo 912577 35633459 := bstep (se 1 (by rfl) ⟨26725094, by rfl⟩ : syracuseStep 35633459 = 53450189) B53450189
theorem B13384061 : Blo 912577 13384061 := bstep (se 3 (by rfl) ⟨2509511, by rfl⟩ : syracuseStep 13384061 = 5019023) B5019023
theorem B1030567 : Blo 912577 1030567 := bstep (se 1 (by rfl) ⟨772925, by rfl⟩ : syracuseStep 1030567 = 1545851) B1545851
theorem B33340085 : Blo 912577 33340085 := bstep (se 5 (by rfl) ⟨1562816, by rfl⟩ : syracuseStep 33340085 = 3125633) B3125633
theorem B1031143 : Blo 912577 1031143 := bstep (se 1 (by rfl) ⟨773357, by rfl⟩ : syracuseStep 1031143 = 1546715) B1546715
theorem B19807249 : Blo 912577 19807249 := bstep (se 2 (by rfl) ⟨7427718, by rfl⟩ : syracuseStep 19807249 = 14855437) B14855437
theorem B3914867 : Blo 912577 3914867 := bstep (se 1 (by rfl) ⟨2936150, by rfl⟩ : syracuseStep 3914867 = 5872301) B5872301
theorem B2604251 : Blo 912577 2604251 := bstep (se 1 (by rfl) ⟨1953188, by rfl⟩ : syracuseStep 2604251 = 3906377) B3906377
theorem B13188689 : Blo 912577 13188689 := bstep (se 2 (by rfl) ⟨4945758, by rfl⟩ : syracuseStep 13188689 = 9891517) B9891517
theorem B1949267 : Blo 912577 1949267 := bstep (se 1 (by rfl) ⟨1461950, by rfl⟩ : syracuseStep 1949267 = 2923901) B2923901
theorem B2932307 : Blo 912577 2932307 := bstep (se 1 (by rfl) ⟨2199230, by rfl⟩ : syracuseStep 2932307 = 4398461) B4398461
theorem B3522311 : Blo 912577 3522311 := bstep (se 1 (by rfl) ⟨2641733, by rfl⟩ : syracuseStep 3522311 = 5283467) B5283467
theorem B2932487 : Blo 912577 2932487 := bstep (se 1 (by rfl) ⟨2199365, by rfl⟩ : syracuseStep 2932487 = 4398731) B4398731
theorem B7815041 : Blo 912577 7815041 := bstep (se 2 (by rfl) ⟨2930640, by rfl⟩ : syracuseStep 7815041 = 5861281) B5861281
theorem B2474351 : Blo 912577 2474351 := bstep (se 1 (by rfl) ⟨1855763, by rfl⟩ : syracuseStep 2474351 = 3711527) B3711527
theorem B29606309 : Blo 912577 29606309 := bstep (se 4 (by rfl) ⟨2775591, by rfl⟩ : syracuseStep 29606309 = 5551183) B5551183
theorem B2605537 : Blo 912577 2605537 := bstep (se 2 (by rfl) ⟨977076, by rfl⟩ : syracuseStep 2605537 = 1954153) B1954153
theorem B2310727 : Blo 912577 2310727 := bstep (se 1 (by rfl) ⟨1733045, by rfl⟩ : syracuseStep 2310727 = 3466091) B3466091
theorem B2310839 : Blo 912577 2310839 := bstep (se 1 (by rfl) ⟨1733129, by rfl⟩ : syracuseStep 2310839 = 3466259) B3466259
theorem B3523295 : Blo 912577 3523295 := bstep (se 1 (by rfl) ⟨2642471, by rfl⟩ : syracuseStep 3523295 = 5284943) B5284943
theorem B1950455 : Blo 912577 1950455 := bstep (se 1 (by rfl) ⟨1462841, by rfl⟩ : syracuseStep 1950455 = 2925683) B2925683
theorem B15615179 : Blo 912577 15615179 := bstep (se 1 (by rfl) ⟨11711384, by rfl⟩ : syracuseStep 15615179 = 23422769) B23422769
theorem B1852649 : Blo 912577 1852649 := bstep (se 2 (by rfl) ⟨694743, by rfl⟩ : syracuseStep 1852649 = 1389487) B1389487
theorem B2082041 : Blo 912577 2082041 := bstep (se 2 (by rfl) ⟨780765, by rfl⟩ : syracuseStep 2082041 = 1561531) B1561531
theorem B1099207 : Blo 912577 1099207 := bstep (se 1 (by rfl) ⟨824405, by rfl⟩ : syracuseStep 1099207 = 1648811) B1648811
theorem B2311841 : Blo 912577 2311841 := bstep (se 2 (by rfl) ⟨866940, by rfl⟩ : syracuseStep 2311841 = 1733881) B1733881
theorem B8800067 : Blo 912577 8800067 := bstep (se 1 (by rfl) ⟨6600050, by rfl⟩ : syracuseStep 8800067 = 13200101) B13200101
theorem B4638545 : Blo 912577 4638545 := bstep (se 2 (by rfl) ⟨1739454, by rfl⟩ : syracuseStep 4638545 = 3478909) B3478909
theorem B2312297 : Blo 912577 2312297 := bstep (se 2 (by rfl) ⟨867111, by rfl⟩ : syracuseStep 2312297 = 1734223) B1734223
theorem B2312783 : Blo 912577 2312783 := bstep (se 1 (by rfl) ⟨1734587, by rfl⟩ : syracuseStep 2312783 = 3469175) B3469175
theorem B4639355 : Blo 912577 4639355 := bstep (se 1 (by rfl) ⟨3479516, by rfl⟩ : syracuseStep 4639355 = 6959033) B6959033
theorem B8801459 : Blo 912577 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B2935997 : Blo 912577 2935997 := bstep (se 3 (by rfl) ⟨550499, by rfl⟩ : syracuseStep 2935997 = 1100999) B1100999
theorem B2313431 : Blo 912577 2313431 := bstep (se 1 (by rfl) ⟨1735073, by rfl⟩ : syracuseStep 2313431 = 3470147) B3470147
theorem B23449013 : Blo 912577 23449013 := bstep (se 5 (by rfl) ⟨1099172, by rfl⟩ : syracuseStep 23449013 = 2198345) B2198345
theorem B2313785 : Blo 912577 2313785 := bstep (se 2 (by rfl) ⟨867669, by rfl⟩ : syracuseStep 2313785 = 1735339) B1735339
theorem B95047499 : Blo 912577 95047499 := bstep (se 1 (by rfl) ⟨71285624, by rfl⟩ : syracuseStep 95047499 = 142571249) B142571249
theorem B1953641 : Blo 912577 1953641 := bstep (se 2 (by rfl) ⟨732615, by rfl⟩ : syracuseStep 1953641 = 1465231) B1465231
theorem B5854031 : Blo 912577 5854031 := bstep (se 1 (by rfl) ⟨4390523, by rfl⟩ : syracuseStep 5854031 = 8781047) B8781047
theorem B1463591 : Blo 912577 1463591 := bstep (se 1 (by rfl) ⟨1097693, by rfl⟩ : syracuseStep 1463591 = 2195387) B2195387
theorem B2053727 : Blo 912577 2053727 := bstep (se 1 (by rfl) ⟨1540295, by rfl⟩ : syracuseStep 2053727 = 3080591) B3080591
theorem B2316073 : Blo 912577 2316073 := bstep (se 2 (by rfl) ⟨868527, by rfl⟩ : syracuseStep 2316073 = 1737055) B1737055
theorem B2053943 : Blo 912577 2053943 := bstep (se 1 (by rfl) ⟨1540457, by rfl⟩ : syracuseStep 2053943 = 3080915) B3080915
theorem B21419957 : Blo 912577 21419957 := bstep (se 5 (by rfl) ⟨1004060, by rfl⟩ : syracuseStep 21419957 = 2008121) B2008121
theorem B2054249 : Blo 912577 2054249 := bstep (se 2 (by rfl) ⟨770343, by rfl⟩ : syracuseStep 2054249 = 1540687) B1540687
theorem B2316863 : Blo 912577 2316863 := bstep (se 1 (by rfl) ⟨1737647, by rfl⟩ : syracuseStep 2316863 = 3475295) B3475295
theorem B2054735 : Blo 912577 2054735 := bstep (se 1 (by rfl) ⟨1541051, by rfl⟩ : syracuseStep 2054735 = 3082103) B3082103
theorem B2054879 : Blo 912577 2054879 := bstep (se 1 (by rfl) ⟨1541159, by rfl⟩ : syracuseStep 2054879 = 3082319) B3082319
theorem B3300115 : Blo 912577 3300115 := bstep (se 1 (by rfl) ⟨2475086, by rfl⟩ : syracuseStep 3300115 = 4950173) B4950173
theorem B1235791 : Blo 912577 1235791 := bstep (se 1 (by rfl) ⟨926843, by rfl⟩ : syracuseStep 1235791 = 1853687) B1853687
theorem B17554319 : Blo 912577 17554319 := bstep (se 1 (by rfl) ⟨13165739, by rfl⟩ : syracuseStep 17554319 = 26331479) B26331479
theorem B2055131 : Blo 912577 2055131 := bstep (se 1 (by rfl) ⟨1541348, by rfl⟩ : syracuseStep 2055131 = 3082697) B3082697
theorem B2055311 : Blo 912577 2055311 := bstep (se 1 (by rfl) ⟨1541483, by rfl⟩ : syracuseStep 2055311 = 3082967) B3082967
theorem B2317511 : Blo 912577 2317511 := bstep (se 1 (by rfl) ⟨1738133, by rfl⟩ : syracuseStep 2317511 = 3476267) B3476267
theorem B2317531 : Blo 912577 2317531 := bstep (se 1 (by rfl) ⟨1738148, by rfl⟩ : syracuseStep 2317531 = 3476297) B3476297
theorem B2055401 : Blo 912577 2055401 := bstep (se 2 (by rfl) ⟨770775, by rfl⟩ : syracuseStep 2055401 = 1541551) B1541551
theorem B2055455 : Blo 912577 2055455 := bstep (se 1 (by rfl) ⟨1541591, by rfl⟩ : syracuseStep 2055455 = 3083183) B3083183
theorem B6938135 : Blo 912577 6938135 := bstep (se 1 (by rfl) ⟨5203601, by rfl⟩ : syracuseStep 6938135 = 10407203) B10407203
theorem B2055977 : Blo 912577 2055977 := bstep (se 2 (by rfl) ⟨770991, by rfl⟩ : syracuseStep 2055977 = 1541983) B1541983
theorem B1302313 : Blo 912577 1302313 := bstep (se 2 (by rfl) ⟨488367, by rfl⟩ : syracuseStep 1302313 = 976735) B976735
theorem B3465089 : Blo 912577 3465089 := bstep (se 2 (by rfl) ⟨1299408, by rfl⟩ : syracuseStep 3465089 = 2598817) B2598817
theorem B2318665 : Blo 912577 2318665 := bstep (se 2 (by rfl) ⟨869499, by rfl⟩ : syracuseStep 2318665 = 1738999) B1738999
theorem B6578633 : Blo 912577 6578633 := bstep (se 2 (by rfl) ⟨2466987, by rfl⟩ : syracuseStep 6578633 = 4933975) B4933975
theorem B3564001 : Blo 912577 3564001 := bstep (se 2 (by rfl) ⟨1336500, by rfl⟩ : syracuseStep 3564001 = 2673001) B2673001
theorem B8806913 : Blo 912577 8806913 := bstep (se 2 (by rfl) ⟨3302592, by rfl⟩ : syracuseStep 8806913 = 6605185) B6605185
theorem B8905249 : Blo 912577 8905249 := bstep (se 2 (by rfl) ⟨3339468, by rfl⟩ : syracuseStep 8905249 = 6678937) B6678937
theorem B2318969 : Blo 912577 2318969 := bstep (se 2 (by rfl) ⟨869613, by rfl⟩ : syracuseStep 2318969 = 1739227) B1739227
theorem B6578891 : Blo 912577 6578891 := bstep (se 1 (by rfl) ⟨4934168, by rfl⟩ : syracuseStep 6578891 = 9868337) B9868337
theorem B1368911 : Blo 912577 1368911 := bstep (se 1 (by rfl) ⟨1026683, by rfl⟩ : syracuseStep 1368911 = 2053367) B2053367
theorem B2057039 : Blo 912577 2057039 := bstep (se 1 (by rfl) ⟨1542779, by rfl⟩ : syracuseStep 2057039 = 3085559) B3085559
theorem B3302363 : Blo 912577 3302363 := bstep (se 1 (by rfl) ⟨2476772, by rfl⟩ : syracuseStep 3302363 = 4953545) B4953545
theorem B33776605 : Blo 912577 33776605 := bstep (se 3 (by rfl) ⟨6333113, by rfl⟩ : syracuseStep 33776605 = 12666227) B12666227
theorem B3957751 : Blo 912577 3957751 := bstep (se 1 (by rfl) ⟨2968313, by rfl⟩ : syracuseStep 3957751 = 5936627) B5936627
theorem B2057255 : Blo 912577 2057255 := bstep (se 1 (by rfl) ⟨1542941, by rfl⟩ : syracuseStep 2057255 = 3085883) B3085883
theorem B1369307 : Blo 912577 1369307 := bstep (se 1 (by rfl) ⟨1026980, by rfl⟩ : syracuseStep 1369307 = 2053961) B2053961
theorem B2057435 : Blo 912577 2057435 := bstep (se 1 (by rfl) ⟨1543076, by rfl⟩ : syracuseStep 2057435 = 3086153) B3086153
theorem B1303771 : Blo 912577 1303771 := bstep (se 1 (by rfl) ⟨977828, by rfl⟩ : syracuseStep 1303771 = 1955657) B1955657
theorem B1369481 : Blo 912577 1369481 := bstep (se 2 (by rfl) ⟨513555, by rfl⟩ : syracuseStep 1369481 = 1027111) B1027111
theorem B2057633 : Blo 912577 2057633 := bstep (se 2 (by rfl) ⟨771612, by rfl⟩ : syracuseStep 2057633 = 1543225) B1543225
theorem B3466759 : Blo 912577 3466759 := bstep (se 1 (by rfl) ⟨2600069, by rfl⟩ : syracuseStep 3466759 = 5200139) B5200139
theorem B1369835 : Blo 912577 1369835 := bstep (se 1 (by rfl) ⟨1027376, by rfl⟩ : syracuseStep 1369835 = 2054753) B2054753
theorem B3467063 : Blo 912577 3467063 := bstep (se 1 (by rfl) ⟨2600297, by rfl⟩ : syracuseStep 3467063 = 5200595) B5200595
theorem B1370063 : Blo 912577 1370063 := bstep (se 1 (by rfl) ⟨1027547, by rfl⟩ : syracuseStep 1370063 = 2055095) B2055095
theorem B2058191 : Blo 912577 2058191 := bstep (se 1 (by rfl) ⟨1543643, by rfl⟩ : syracuseStep 2058191 = 3087287) B3087287
theorem B3467245 : Blo 912577 3467245 := bstep (se 3 (by rfl) ⟨650108, by rfl⟩ : syracuseStep 3467245 = 1300217) B1300217
theorem B3467549 : Blo 912577 3467549 := bstep (se 3 (by rfl) ⟨650165, by rfl⟩ : syracuseStep 3467549 = 1300331) B1300331
theorem B2058569 : Blo 912577 2058569 := bstep (se 2 (by rfl) ⟨771963, by rfl⟩ : syracuseStep 2058569 = 1543927) B1543927
theorem B1370459 : Blo 912577 1370459 := bstep (se 1 (by rfl) ⟨1027844, by rfl⟩ : syracuseStep 1370459 = 2055689) B2055689
theorem B2058587 : Blo 912577 2058587 := bstep (se 1 (by rfl) ⟨1543940, by rfl⟩ : syracuseStep 2058587 = 3087881) B3087881
theorem B6252967 : Blo 912577 6252967 := bstep (se 1 (by rfl) ⟨4689725, by rfl⟩ : syracuseStep 6252967 = 9379451) B9379451
theorem B3467731 : Blo 912577 3467731 := bstep (se 1 (by rfl) ⟨2600798, by rfl⟩ : syracuseStep 3467731 = 5201597) B5201597
theorem B2779643 : Blo 912577 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B1370687 : Blo 912577 1370687 := bstep (se 1 (by rfl) ⟨1028015, by rfl⟩ : syracuseStep 1370687 = 2056031) B2056031
theorem B1370807 : Blo 912577 1370807 := bstep (se 1 (by rfl) ⟨1028105, by rfl⟩ : syracuseStep 1370807 = 2056211) B2056211
theorem B4385603 : Blo 912577 4385603 := bstep (se 1 (by rfl) ⟨3289202, by rfl⟩ : syracuseStep 4385603 = 6578405) B6578405
theorem B1371035 : Blo 912577 1371035 := bstep (se 1 (by rfl) ⟨1028276, by rfl⟩ : syracuseStep 1371035 = 2056553) B2056553
theorem B2059163 : Blo 912577 2059163 := bstep (se 1 (by rfl) ⟨1544372, by rfl⟩ : syracuseStep 2059163 = 3088745) B3088745
theorem B3468203 : Blo 912577 3468203 := bstep (se 1 (by rfl) ⟨2601152, by rfl⟩ : syracuseStep 3468203 = 5202305) B5202305
theorem B2059361 : Blo 912577 2059361 := bstep (se 2 (by rfl) ⟨772260, by rfl⟩ : syracuseStep 2059361 = 1544521) B1544521
theorem B912671 : Blo 912577 912671 := bstep (se 1 (by rfl) ⟨684503, by rfl⟩ : syracuseStep 912671 = 1369007) B1369007
theorem B1371431 : Blo 912577 1371431 := bstep (se 1 (by rfl) ⟨1028573, by rfl⟩ : syracuseStep 1371431 = 2057147) B2057147
theorem B2059559 : Blo 912577 2059559 := bstep (se 1 (by rfl) ⟨1544669, by rfl⟩ : syracuseStep 2059559 = 3089339) B3089339
theorem B912731 : Blo 912577 912731 := bstep (se 1 (by rfl) ⟨684548, by rfl⟩ : syracuseStep 912731 = 1369097) B1369097
theorem B912751 : Blo 912577 912751 := bstep (se 1 (by rfl) ⟨684563, by rfl⟩ : syracuseStep 912751 = 1369127) B1369127
theorem B5270903 : Blo 912577 5270903 := bstep (se 1 (by rfl) ⟨3953177, by rfl⟩ : syracuseStep 5270903 = 7906355) B7906355
theorem B1371515 : Blo 912577 1371515 := bstep (se 1 (by rfl) ⟨1028636, by rfl⟩ : syracuseStep 1371515 = 2057273) B2057273
theorem B912807 : Blo 912577 912807 := bstep (se 1 (by rfl) ⟨684605, by rfl⟩ : syracuseStep 912807 = 1369211) B1369211
theorem B5860795 : Blo 912577 5860795 := bstep (se 1 (by rfl) ⟨4395596, by rfl⟩ : syracuseStep 5860795 = 8791193) B8791193
theorem B3304891 : Blo 912577 3304891 := bstep (se 1 (by rfl) ⟨2478668, by rfl⟩ : syracuseStep 3304891 = 4957337) B4957337
theorem B1371641 : Blo 912577 1371641 := bstep (se 2 (by rfl) ⟨514365, by rfl⟩ : syracuseStep 1371641 = 1028731) B1028731
theorem B912891 : Blo 912577 912891 := bstep (se 1 (by rfl) ⟨684668, by rfl⟩ : syracuseStep 912891 = 1369337) B1369337
theorem B912959 : Blo 912577 912959 := bstep (se 1 (by rfl) ⟨684719, by rfl⟩ : syracuseStep 912959 = 1369439) B1369439
theorem B912967 : Blo 912577 912967 := bstep (se 1 (by rfl) ⟨684725, by rfl⟩ : syracuseStep 912967 = 1369451) B1369451
theorem B1371743 : Blo 912577 1371743 := bstep (se 1 (by rfl) ⟨1028807, by rfl⟩ : syracuseStep 1371743 = 2057615) B2057615
theorem B2059937 : Blo 912577 2059937 := bstep (se 2 (by rfl) ⟨772476, by rfl⟩ : syracuseStep 2059937 = 1544953) B1544953
theorem B913119 : Blo 912577 913119 := bstep (se 1 (by rfl) ⟨684839, by rfl⟩ : syracuseStep 913119 = 1369679) B1369679
theorem B913199 : Blo 912577 913199 := bstep (se 1 (by rfl) ⟨684899, by rfl⟩ : syracuseStep 913199 = 1369799) B1369799
theorem B4943663 : Blo 912577 4943663 := bstep (se 1 (by rfl) ⟨3707747, by rfl⟩ : syracuseStep 4943663 = 7415495) B7415495
theorem B1371959 : Blo 912577 1371959 := bstep (se 1 (by rfl) ⟨1028969, by rfl⟩ : syracuseStep 1371959 = 2057939) B2057939
theorem B913307 : Blo 912577 913307 := bstep (se 1 (by rfl) ⟨684980, by rfl⟩ : syracuseStep 913307 = 1369961) B1369961
theorem B913359 : Blo 912577 913359 := bstep (se 1 (by rfl) ⟨685019, by rfl⟩ : syracuseStep 913359 = 1370039) B1370039
theorem B913383 : Blo 912577 913383 := bstep (se 1 (by rfl) ⟨685037, by rfl⟩ : syracuseStep 913383 = 1370075) B1370075
theorem B2060297 : Blo 912577 2060297 := bstep (se 2 (by rfl) ⟨772611, by rfl⟩ : syracuseStep 2060297 = 1545223) B1545223
theorem B7827515 : Blo 912577 7827515 := bstep (se 1 (by rfl) ⟨5870636, by rfl⟩ : syracuseStep 7827515 = 11741273) B11741273
theorem B1372265 : Blo 912577 1372265 := bstep (se 2 (by rfl) ⟨514599, by rfl⟩ : syracuseStep 1372265 = 1029199) B1029199
theorem B9892043 : Blo 912577 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B913695 : Blo 912577 913695 := bstep (se 1 (by rfl) ⟨685271, by rfl⟩ : syracuseStep 913695 = 1370543) B1370543
theorem B913755 : Blo 912577 913755 := bstep (se 1 (by rfl) ⟨685316, by rfl⟩ : syracuseStep 913755 = 1370633) B1370633
theorem B3469675 : Blo 912577 3469675 := bstep (se 1 (by rfl) ⟨2602256, by rfl⟩ : syracuseStep 3469675 = 5204513) B5204513
theorem B913775 : Blo 912577 913775 := bstep (se 1 (by rfl) ⟨685331, by rfl⟩ : syracuseStep 913775 = 1370663) B1370663
theorem B913831 : Blo 912577 913831 := bstep (se 1 (by rfl) ⟨685373, by rfl⟩ : syracuseStep 913831 = 1370747) B1370747
theorem B1372583 : Blo 912577 1372583 := bstep (se 1 (by rfl) ⟨1029437, by rfl⟩ : syracuseStep 1372583 = 2058875) B2058875
theorem B2060711 : Blo 912577 2060711 := bstep (se 1 (by rfl) ⟨1545533, by rfl⟩ : syracuseStep 2060711 = 3091067) B3091067
theorem B913915 : Blo 912577 913915 := bstep (se 1 (by rfl) ⟨685436, by rfl⟩ : syracuseStep 913915 = 1370873) B1370873
theorem B1372667 : Blo 912577 1372667 := bstep (se 1 (by rfl) ⟨1029500, by rfl⟩ : syracuseStep 1372667 = 2059001) B2059001
theorem B2060819 : Blo 912577 2060819 := bstep (se 1 (by rfl) ⟨1545614, by rfl⟩ : syracuseStep 2060819 = 3091229) B3091229
theorem B913983 : Blo 912577 913983 := bstep (se 1 (by rfl) ⟨685487, by rfl⟩ : syracuseStep 913983 = 1370975) B1370975
theorem B913991 : Blo 912577 913991 := bstep (se 1 (by rfl) ⟨685493, by rfl⟩ : syracuseStep 913991 = 1370987) B1370987
theorem B2060873 : Blo 912577 2060873 := bstep (se 2 (by rfl) ⟨772827, by rfl⟩ : syracuseStep 2060873 = 1545655) B1545655
theorem B1372793 : Blo 912577 1372793 := bstep (se 2 (by rfl) ⟨514797, by rfl⟩ : syracuseStep 1372793 = 1029595) B1029595
theorem B1372847 : Blo 912577 1372847 := bstep (se 1 (by rfl) ⟨1029635, by rfl⟩ : syracuseStep 1372847 = 2059271) B2059271
theorem B914143 : Blo 912577 914143 := bstep (se 1 (by rfl) ⟨685607, by rfl⟩ : syracuseStep 914143 = 1371215) B1371215
theorem B1372895 : Blo 912577 1372895 := bstep (se 1 (by rfl) ⟨1029671, by rfl⟩ : syracuseStep 1372895 = 2059343) B2059343
theorem B1733395 : Blo 912577 1733395 := bstep (se 1 (by rfl) ⟨1300046, by rfl⟩ : syracuseStep 1733395 = 2600093) B2600093
theorem B914223 : Blo 912577 914223 := bstep (se 1 (by rfl) ⟨685667, by rfl⟩ : syracuseStep 914223 = 1371335) B1371335
theorem B914331 : Blo 912577 914331 := bstep (se 1 (by rfl) ⟨685748, by rfl⟩ : syracuseStep 914331 = 1371497) B1371497
theorem B914383 : Blo 912577 914383 := bstep (se 1 (by rfl) ⟨685787, by rfl⟩ : syracuseStep 914383 = 1371575) B1371575
theorem B914407 : Blo 912577 914407 := bstep (se 1 (by rfl) ⟨685805, by rfl⟩ : syracuseStep 914407 = 1371611) B1371611
theorem B1373159 : Blo 912577 1373159 := bstep (se 1 (by rfl) ⟨1029869, by rfl⟩ : syracuseStep 1373159 = 2059739) B2059739
theorem B2061287 : Blo 912577 2061287 := bstep (se 1 (by rfl) ⟨1545965, by rfl⟩ : syracuseStep 2061287 = 3091931) B3091931
theorem B1373417 : Blo 912577 1373417 := bstep (se 2 (by rfl) ⟨515031, by rfl⟩ : syracuseStep 1373417 = 1030063) B1030063
theorem B10417409 : Blo 912577 10417409 := bstep (se 2 (by rfl) ⟨3906528, by rfl⟩ : syracuseStep 10417409 = 7813057) B7813057
theorem B11728151 : Blo 912577 11728151 := bstep (se 1 (by rfl) ⟨8796113, by rfl⟩ : syracuseStep 11728151 = 17592227) B17592227
theorem B914719 : Blo 912577 914719 := bstep (se 1 (by rfl) ⟨686039, by rfl⟩ : syracuseStep 914719 = 1372079) B1372079
theorem B1373471 : Blo 912577 1373471 := bstep (se 1 (by rfl) ⟨1030103, by rfl⟩ : syracuseStep 1373471 = 2060207) B2060207
theorem B914779 : Blo 912577 914779 := bstep (se 1 (by rfl) ⟨686084, by rfl⟩ : syracuseStep 914779 = 1372169) B1372169
theorem B2061665 : Blo 912577 2061665 := bstep (se 2 (by rfl) ⟨773124, by rfl⟩ : syracuseStep 2061665 = 1546249) B1546249
theorem B914799 : Blo 912577 914799 := bstep (se 1 (by rfl) ⟨686099, by rfl⟩ : syracuseStep 914799 = 1372199) B1372199
theorem B914855 : Blo 912577 914855 := bstep (se 1 (by rfl) ⟨686141, by rfl⟩ : syracuseStep 914855 = 1372283) B1372283
theorem B2061755 : Blo 912577 2061755 := bstep (se 1 (by rfl) ⟨1546316, by rfl⟩ : syracuseStep 2061755 = 3092633) B3092633
theorem B1373639 : Blo 912577 1373639 := bstep (se 1 (by rfl) ⟨1030229, by rfl⟩ : syracuseStep 1373639 = 2060459) B2060459
theorem B914939 : Blo 912577 914939 := bstep (se 1 (by rfl) ⟨686204, by rfl⟩ : syracuseStep 914939 = 1372409) B1372409
theorem B2061881 : Blo 912577 2061881 := bstep (se 2 (by rfl) ⟨773205, by rfl⟩ : syracuseStep 2061881 = 1546411) B1546411
theorem B915007 : Blo 912577 915007 := bstep (se 1 (by rfl) ⟨686255, by rfl⟩ : syracuseStep 915007 = 1372511) B1372511
theorem B915015 : Blo 912577 915015 := bstep (se 1 (by rfl) ⟨686261, by rfl⟩ : syracuseStep 915015 = 1372523) B1372523
theorem B915167 : Blo 912577 915167 := bstep (se 1 (by rfl) ⟨686375, by rfl⟩ : syracuseStep 915167 = 1372751) B1372751
theorem B1373993 : Blo 912577 1373993 := bstep (se 2 (by rfl) ⟨515247, by rfl⟩ : syracuseStep 1373993 = 1030495) B1030495
theorem B915247 : Blo 912577 915247 := bstep (se 1 (by rfl) ⟨686435, by rfl⟩ : syracuseStep 915247 = 1372871) B1372871
theorem B1373999 : Blo 912577 1373999 := bstep (se 1 (by rfl) ⟨1030499, by rfl⟩ : syracuseStep 1373999 = 2060999) B2060999
theorem B915355 : Blo 912577 915355 := bstep (se 1 (by rfl) ⟨686516, by rfl⟩ : syracuseStep 915355 = 1373033) B1373033
theorem B915407 : Blo 912577 915407 := bstep (se 1 (by rfl) ⟨686555, by rfl⟩ : syracuseStep 915407 = 1373111) B1373111
theorem B915431 : Blo 912577 915431 := bstep (se 1 (by rfl) ⟨686573, by rfl⟩ : syracuseStep 915431 = 1373147) B1373147
theorem B1374473 : Blo 912577 1374473 := bstep (se 2 (by rfl) ⟨515427, by rfl⟩ : syracuseStep 1374473 = 1030855) B1030855
theorem B915743 : Blo 912577 915743 := bstep (se 1 (by rfl) ⟨686807, by rfl⟩ : syracuseStep 915743 = 1373615) B1373615
theorem B915803 : Blo 912577 915803 := bstep (se 1 (by rfl) ⟨686852, by rfl⟩ : syracuseStep 915803 = 1373705) B1373705
theorem B915823 : Blo 912577 915823 := bstep (se 1 (by rfl) ⟨686867, by rfl⟩ : syracuseStep 915823 = 1373735) B1373735
theorem B1374575 : Blo 912577 1374575 := bstep (se 1 (by rfl) ⟨1030931, by rfl⟩ : syracuseStep 1374575 = 2061863) B2061863
theorem B915879 : Blo 912577 915879 := bstep (se 1 (by rfl) ⟨686909, by rfl⟩ : syracuseStep 915879 = 1373819) B1373819
theorem B915963 : Blo 912577 915963 := bstep (se 1 (by rfl) ⟨686972, by rfl⟩ : syracuseStep 915963 = 1373945) B1373945
theorem B2193983 : Blo 912577 2193983 := bstep (se 1 (by rfl) ⟨1645487, by rfl⟩ : syracuseStep 2193983 = 3290975) B3290975
theorem B916031 : Blo 912577 916031 := bstep (se 1 (by rfl) ⟨687023, by rfl⟩ : syracuseStep 916031 = 1374047) B1374047
theorem B916039 : Blo 912577 916039 := bstep (se 1 (by rfl) ⟨687029, by rfl⟩ : syracuseStep 916039 = 1374059) B1374059
theorem B1374791 : Blo 912577 1374791 := bstep (se 1 (by rfl) ⟨1031093, by rfl⟩ : syracuseStep 1374791 = 2062187) B2062187
theorem B1374827 : Blo 912577 1374827 := bstep (se 1 (by rfl) ⟨1031120, by rfl⟩ : syracuseStep 1374827 = 2062241) B2062241
theorem B916191 : Blo 912577 916191 := bstep (se 1 (by rfl) ⟨687143, by rfl⟩ : syracuseStep 916191 = 1374287) B1374287
theorem B916271 : Blo 912577 916271 := bstep (se 1 (by rfl) ⟨687203, by rfl⟩ : syracuseStep 916271 = 1374407) B1374407
theorem B916379 : Blo 912577 916379 := bstep (se 1 (by rfl) ⟨687284, by rfl⟩ : syracuseStep 916379 = 1374569) B1374569
theorem B916431 : Blo 912577 916431 := bstep (se 1 (by rfl) ⟨687323, by rfl⟩ : syracuseStep 916431 = 1374647) B1374647
theorem B916455 : Blo 912577 916455 := bstep (se 1 (by rfl) ⟨687341, by rfl⟩ : syracuseStep 916455 = 1374683) B1374683
theorem B7044259 : Blo 912577 7044259 := bstep (se 1 (by rfl) ⟨5283194, by rfl⟩ : syracuseStep 7044259 = 10566389) B10566389
theorem B7798295 : Blo 912577 7798295 := bstep (se 1 (by rfl) ⟨5848721, by rfl⟩ : syracuseStep 7798295 = 11697443) B11697443
theorem B9371159 : Blo 912577 9371159 := bstep (se 1 (by rfl) ⟨7028369, by rfl⟩ : syracuseStep 9371159 = 14056739) B14056739
theorem B3079997 : Blo 912577 3079997 := bstep (se 3 (by rfl) ⟨577499, by rfl⟩ : syracuseStep 3079997 = 1154999) B1154999
theorem B4456367 : Blo 912577 4456367 := bstep (se 1 (by rfl) ⟨3342275, by rfl⟩ : syracuseStep 4456367 = 6684551) B6684551
theorem B6946883 : Blo 912577 6946883 := bstep (se 1 (by rfl) ⟨5210162, by rfl⟩ : syracuseStep 6946883 = 10420325) B10420325
theorem B1540559 : Blo 912577 1540559 := bstep (se 1 (by rfl) ⟨1155419, by rfl⟩ : syracuseStep 1540559 = 2310839) B2310839
theorem B3080699 : Blo 912577 3080699 := bstep (se 1 (by rfl) ⟨2310524, by rfl⟩ : syracuseStep 3080699 = 4621049) B4621049
theorem B4752001 : Blo 912577 4752001 := bstep (se 2 (by rfl) ⟨1782000, by rfl⟩ : syracuseStep 4752001 = 3564001) B3564001
theorem B3474049 : Blo 912577 3474049 := bstep (se 2 (by rfl) ⟨1302768, by rfl⟩ : syracuseStep 3474049 = 2605537) B2605537
theorem B3080969 : Blo 912577 3080969 := bstep (se 2 (by rfl) ⟨1155363, by rfl⟩ : syracuseStep 3080969 = 2310727) B2310727
theorem B1541227 : Blo 912577 1541227 := bstep (se 1 (by rfl) ⟨1155920, by rfl⟩ : syracuseStep 1541227 = 2311841) B2311841
theorem B5866711 : Blo 912577 5866711 := bstep (se 1 (by rfl) ⟨4400033, by rfl⟩ : syracuseStep 5866711 = 8800067) B8800067
theorem B5277001 : Blo 912577 5277001 := bstep (se 2 (by rfl) ⟨1978875, by rfl⟩ : syracuseStep 5277001 = 3957751) B3957751
theorem B1541531 : Blo 912577 1541531 := bstep (se 1 (by rfl) ⟨1156148, by rfl⟩ : syracuseStep 1541531 = 2312297) B2312297
theorem B3081725 : Blo 912577 3081725 := bstep (se 3 (by rfl) ⟨577823, by rfl⟩ : syracuseStep 3081725 = 1155647) B1155647
theorem B1738361 : Blo 912577 1738361 := bstep (se 2 (by rfl) ⟨651885, by rfl⟩ : syracuseStep 1738361 = 1303771) B1303771
theorem B1541855 : Blo 912577 1541855 := bstep (se 1 (by rfl) ⟨1156391, by rfl⟩ : syracuseStep 1541855 = 2312783) B2312783
theorem B4622345 : Blo 912577 4622345 := bstep (se 2 (by rfl) ⟨1733379, by rfl⟩ : syracuseStep 4622345 = 3466759) B3466759
theorem B5867639 : Blo 912577 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B1542287 : Blo 912577 1542287 := bstep (se 1 (by rfl) ⟨1156715, by rfl⟩ : syracuseStep 1542287 = 2313431) B2313431
theorem B15632675 : Blo 912577 15632675 := bstep (se 1 (by rfl) ⟨11724506, by rfl⟩ : syracuseStep 15632675 = 23449013) B23449013
theorem B3082535 : Blo 912577 3082535 := bstep (se 1 (by rfl) ⟨2311901, by rfl⟩ : syracuseStep 3082535 = 4623803) B4623803
theorem B1542523 : Blo 912577 1542523 := bstep (se 1 (by rfl) ⟨1156892, by rfl⟩ : syracuseStep 1542523 = 2313785) B2313785
theorem B6949313 : Blo 912577 6949313 := bstep (se 2 (by rfl) ⟨2605992, by rfl⟩ : syracuseStep 6949313 = 5211985) B5211985
theorem B1542793 : Blo 912577 1542793 := bstep (se 2 (by rfl) ⟨578547, by rfl⟩ : syracuseStep 1542793 = 1157095) B1157095
theorem B4622993 : Blo 912577 4622993 := bstep (se 2 (by rfl) ⟨1733622, by rfl⟩ : syracuseStep 4622993 = 3467245) B3467245
theorem B3083399 : Blo 912577 3083399 := bstep (se 1 (by rfl) ⟨2312549, by rfl⟩ : syracuseStep 3083399 = 4625099) B4625099
theorem B3902687 : Blo 912577 3902687 := bstep (se 1 (by rfl) ⟨2927015, by rfl⟩ : syracuseStep 3902687 = 5854031) B5854031
theorem B3083507 : Blo 912577 3083507 := bstep (se 1 (by rfl) ⟨2312630, by rfl⟩ : syracuseStep 3083507 = 4625261) B4625261
theorem B4623641 : Blo 912577 4623641 := bstep (se 2 (by rfl) ⟨1733865, by rfl⟩ : syracuseStep 4623641 = 3467731) B3467731
theorem B7049369 : Blo 912577 7049369 := bstep (se 2 (by rfl) ⟨2643513, by rfl⟩ : syracuseStep 7049369 = 5287027) B5287027
theorem B14094607 : Blo 912577 14094607 := bstep (se 1 (by rfl) ⟨10570955, by rfl⟩ : syracuseStep 14094607 = 21141911) B21141911
theorem B57151817 : Blo 912577 57151817 := bstep (se 2 (by rfl) ⟨21431931, by rfl⟩ : syracuseStep 57151817 = 42863863) B42863863
theorem B1544575 : Blo 912577 1544575 := bstep (se 1 (by rfl) ⟨1158431, by rfl⟩ : syracuseStep 1544575 = 2316863) B2316863
theorem B11702879 : Blo 912577 11702879 := bstep (se 1 (by rfl) ⟨8777159, by rfl⟩ : syracuseStep 11702879 = 17554319) B17554319
theorem B1545007 : Blo 912577 1545007 := bstep (se 1 (by rfl) ⟨1158755, by rfl⟩ : syracuseStep 1545007 = 2317511) B2317511
theorem B3085181 : Blo 912577 3085181 := bstep (se 3 (by rfl) ⟨578471, by rfl⟩ : syracuseStep 3085181 = 1156943) B1156943
theorem B4625423 : Blo 912577 4625423 := bstep (se 1 (by rfl) ⟨3469067, by rfl⟩ : syracuseStep 4625423 = 6938135) B6938135
theorem B3085451 : Blo 912577 3085451 := bstep (se 1 (by rfl) ⟨2314088, by rfl⟩ : syracuseStep 3085451 = 4628177) B4628177
theorem B11277521 : Blo 912577 11277521 := bstep (se 2 (by rfl) ⟨4229070, by rfl⟩ : syracuseStep 11277521 = 8458141) B8458141
theorem B2201057 : Blo 912577 2201057 := bstep (se 2 (by rfl) ⟨825396, by rfl⟩ : syracuseStep 2201057 = 1650793) B1650793
theorem B5871275 : Blo 912577 5871275 := bstep (se 1 (by rfl) ⟨4403456, by rfl⟩ : syracuseStep 5871275 = 8806913) B8806913
theorem B1545979 : Blo 912577 1545979 := bstep (se 1 (by rfl) ⟨1159484, by rfl⟩ : syracuseStep 1545979 = 2318969) B2318969
theorem B6952715 : Blo 912577 6952715 := bstep (se 1 (by rfl) ⟨5214536, by rfl⟩ : syracuseStep 6952715 = 10429073) B10429073
theorem B4626233 : Blo 912577 4626233 := bstep (se 2 (by rfl) ⟨1734837, by rfl⟩ : syracuseStep 4626233 = 3469675) B3469675
theorem B1546121 : Blo 912577 1546121 := bstep (se 2 (by rfl) ⟨579795, by rfl⟩ : syracuseStep 1546121 = 1159591) B1159591
theorem B2201575 : Blo 912577 2201575 := bstep (se 1 (by rfl) ⟨1651181, by rfl⟩ : syracuseStep 2201575 = 3302363) B3302363
theorem B1546553 : Blo 912577 1546553 := bstep (se 2 (by rfl) ⟨579957, by rfl⟩ : syracuseStep 1546553 = 1159915) B1159915
theorem B7412381 : Blo 912577 7412381 := bstep (se 3 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 7412381 = 2779643) B2779643
theorem B3087071 : Blo 912577 3087071 := bstep (se 1 (by rfl) ⟨2315303, by rfl⟩ : syracuseStep 3087071 = 4630607) B4630607
theorem B8788769 : Blo 912577 8788769 := bstep (se 2 (by rfl) ⟨3295788, by rfl⟩ : syracuseStep 8788769 = 6591577) B6591577
theorem B1186795 : Blo 912577 1186795 := bstep (se 1 (by rfl) ⟨890096, by rfl⟩ : syracuseStep 1186795 = 1780193) B1780193
theorem B2923735 : Blo 912577 2923735 := bstep (se 1 (by rfl) ⟨2192801, by rfl⟩ : syracuseStep 2923735 = 4385603) B4385603
theorem B9903455 : Blo 912577 9903455 := bstep (se 1 (by rfl) ⟨7427591, by rfl⟩ : syracuseStep 9903455 = 14855183) B14855183
theorem B3087827 : Blo 912577 3087827 := bstep (se 1 (by rfl) ⟨2315870, by rfl⟩ : syracuseStep 3087827 = 4631741) B4631741
theorem B3513935 : Blo 912577 3513935 := bstep (se 1 (by rfl) ⟨2635451, by rfl⟩ : syracuseStep 3513935 = 5270903) B5270903
theorem B6954659 : Blo 912577 6954659 := bstep (se 1 (by rfl) ⟨5215994, by rfl⟩ : syracuseStep 6954659 = 10431989) B10431989
theorem B3088097 : Blo 912577 3088097 := bstep (se 2 (by rfl) ⟨1158036, by rfl⟩ : syracuseStep 3088097 = 2316073) B2316073
theorem B5218343 : Blo 912577 5218343 := bstep (se 1 (by rfl) ⟨3913757, by rfl⟩ : syracuseStep 5218343 = 7827515) B7827515
theorem B6594695 : Blo 912577 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B1253759 : Blo 912577 1253759 := bstep (se 1 (by rfl) ⟨940319, by rfl⟩ : syracuseStep 1253759 = 1880639) B1880639
theorem B19768157 : Blo 912577 19768157 := bstep (se 3 (by rfl) ⟨3706529, by rfl⟩ : syracuseStep 19768157 = 7413059) B7413059
theorem B4400153 : Blo 912577 4400153 := bstep (se 2 (by rfl) ⟨1650057, by rfl⟩ : syracuseStep 4400153 = 3300115) B3300115
theorem B1647721 : Blo 912577 1647721 := bstep (se 2 (by rfl) ⟨617895, by rfl⟩ : syracuseStep 1647721 = 1235791) B1235791
theorem B3089771 : Blo 912577 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B3089879 : Blo 912577 3089879 := bstep (se 1 (by rfl) ⟨2317409, by rfl⟩ : syracuseStep 3089879 = 4634819) B4634819
theorem B24126983 : Blo 912577 24126983 := bstep (se 1 (by rfl) ⟨18095237, by rfl⟩ : syracuseStep 24126983 = 36190475) B36190475
theorem B8922707 : Blo 912577 8922707 := bstep (se 1 (by rfl) ⟨6692030, by rfl⟩ : syracuseStep 8922707 = 13384061) B13384061
theorem B3090041 : Blo 912577 3090041 := bstep (se 2 (by rfl) ⟨1158765, by rfl⟩ : syracuseStep 3090041 = 2317531) B2317531
theorem B22226723 : Blo 912577 22226723 := bstep (se 1 (by rfl) ⟨16670042, by rfl⟩ : syracuseStep 22226723 = 33340085) B33340085
theorem B6957089 : Blo 912577 6957089 := bstep (se 2 (by rfl) ⟨2608908, by rfl⟩ : syracuseStep 6957089 = 5217817) B5217817
theorem B8792459 : Blo 912577 8792459 := bstep (se 1 (by rfl) ⟨6594344, by rfl⟩ : syracuseStep 8792459 = 13188689) B13188689
theorem B1649567 : Blo 912577 1649567 := bstep (se 1 (by rfl) ⟨1237175, by rfl⟩ : syracuseStep 1649567 = 2474351) B2474351
theorem B19737539 : Blo 912577 19737539 := bstep (se 1 (by rfl) ⟨14803154, by rfl⟩ : syracuseStep 19737539 = 29606309) B29606309
theorem B3091553 : Blo 912577 3091553 := bstep (se 2 (by rfl) ⟨1159332, by rfl⟩ : syracuseStep 3091553 = 2318665) B2318665
theorem B4893929 : Blo 912577 4893929 := bstep (se 2 (by rfl) ⟨1835223, by rfl⟩ : syracuseStep 4893929 = 3670447) B3670447
theorem B11873665 : Blo 912577 11873665 := bstep (se 2 (by rfl) ⟨4452624, by rfl⟩ : syracuseStep 11873665 = 8905249) B8905249
theorem B1388027 : Blo 912577 1388027 := bstep (se 1 (by rfl) ⟨1041020, by rfl⟩ : syracuseStep 1388027 = 2082041) B2082041
theorem B3092093 : Blo 912577 3092093 := bstep (se 3 (by rfl) ⟨579767, by rfl⟩ : syracuseStep 3092093 = 1159535) B1159535
theorem B3092363 : Blo 912577 3092363 := bstep (se 1 (by rfl) ⟨2319272, by rfl⟩ : syracuseStep 3092363 = 4638545) B4638545
theorem B1028479 : Blo 912577 1028479 := bstep (se 1 (by rfl) ⟨771359, by rfl⟩ : syracuseStep 1028479 = 1542719) B1542719
theorem B3092903 : Blo 912577 3092903 := bstep (se 1 (by rfl) ⟨2319677, by rfl⟩ : syracuseStep 3092903 = 4639355) B4639355
theorem B2601551 : Blo 912577 2601551 := bstep (se 1 (by rfl) ⟨1951163, by rfl⟩ : syracuseStep 2601551 = 3902327) B3902327
theorem B2602439 : Blo 912577 2602439 := bstep (se 1 (by rfl) ⟨1951829, by rfl⟩ : syracuseStep 2602439 = 3903659) B3903659
theorem B2602667 : Blo 912577 2602667 := bstep (se 1 (by rfl) ⟨1952000, by rfl⟩ : syracuseStep 2602667 = 3904001) B3904001
theorem B1029883 : Blo 912577 1029883 := bstep (se 1 (by rfl) ⟨772412, by rfl⟩ : syracuseStep 1029883 = 1544825) B1544825
theorem B1029919 : Blo 912577 1029919 := bstep (se 1 (by rfl) ⟨772439, by rfl⟩ : syracuseStep 1029919 = 1544879) B1544879
theorem B3913535 : Blo 912577 3913535 := bstep (se 1 (by rfl) ⟨2935151, by rfl⟩ : syracuseStep 3913535 = 5870303) B5870303
theorem B8337289 : Blo 912577 8337289 := bstep (se 2 (by rfl) ⟨3126483, by rfl⟩ : syracuseStep 8337289 = 6252967) B6252967
theorem B3127439 : Blo 912577 3127439 := bstep (se 1 (by rfl) ⟨2345579, by rfl⟩ : syracuseStep 3127439 = 4691159) B4691159
theorem B1031071 : Blo 912577 1031071 := bstep (se 1 (by rfl) ⟨773303, by rfl⟩ : syracuseStep 1031071 = 1546607) B1546607
theorem B1096751 : Blo 912577 1096751 := bstep (se 1 (by rfl) ⟨822563, by rfl⟩ : syracuseStep 1096751 = 1645127) B1645127
theorem B7814393 : Blo 912577 7814393 := bstep (se 2 (by rfl) ⟨2930397, by rfl⟩ : syracuseStep 7814393 = 5860795) B5860795
theorem B4406521 : Blo 912577 4406521 := bstep (se 2 (by rfl) ⟨1652445, by rfl⟩ : syracuseStep 4406521 = 3304891) B3304891
theorem B4636115 : Blo 912577 4636115 := bstep (se 1 (by rfl) ⟨3477086, by rfl⟩ : syracuseStep 4636115 = 6954173) B6954173
theorem B42188323 : Blo 912577 42188323 := bstep (se 1 (by rfl) ⟨31641242, by rfl⟩ : syracuseStep 42188323 = 63282485) B63282485
theorem B3128975 : Blo 912577 3128975 := bstep (se 1 (by rfl) ⟨2346731, by rfl⟩ : syracuseStep 3128975 = 4693463) B4693463
theorem B180141893 : Blo 912577 180141893 := bstep (se 4 (by rfl) ⟨16888302, by rfl⟩ : syracuseStep 180141893 = 33776605) B33776605
theorem B2604923 : Blo 912577 2604923 := bstep (se 1 (by rfl) ⟨1953692, by rfl⟩ : syracuseStep 2604923 = 3907385) B3907385
theorem B2310059 : Blo 912577 2310059 := bstep (se 1 (by rfl) ⟨1732544, by rfl⟩ : syracuseStep 2310059 = 3465089) B3465089
theorem B6603227 : Blo 912577 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B4178807 : Blo 912577 4178807 := bstep (se 1 (by rfl) ⟨3134105, by rfl⟩ : syracuseStep 4178807 = 6268211) B6268211
theorem B23708675 : Blo 912577 23708675 := bstep (se 1 (by rfl) ⟨17781506, by rfl⟩ : syracuseStep 23708675 = 35563013) B35563013
theorem B2311193 : Blo 912577 2311193 := bstep (se 2 (by rfl) ⟨866697, by rfl⟩ : syracuseStep 2311193 = 1733395) B1733395
theorem B3294233 : Blo 912577 3294233 := bstep (se 2 (by rfl) ⟨1235337, by rfl⟩ : syracuseStep 3294233 = 2470675) B2470675
theorem B6341777 : Blo 912577 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B2311375 : Blo 912577 2311375 := bstep (se 1 (by rfl) ⟨1733531, by rfl⟩ : syracuseStep 2311375 = 3467063) B3467063
theorem B2475215 : Blo 912577 2475215 := bstep (se 1 (by rfl) ⟨1856411, by rfl⟩ : syracuseStep 2475215 = 3712823) B3712823
theorem B2934089 : Blo 912577 2934089 := bstep (se 2 (by rfl) ⟨1100283, by rfl⟩ : syracuseStep 2934089 = 2200567) B2200567
theorem B11716001 : Blo 912577 11716001 := bstep (se 2 (by rfl) ⟨4393500, by rfl⟩ : syracuseStep 11716001 = 8787001) B8787001
theorem B2311699 : Blo 912577 2311699 := bstep (se 1 (by rfl) ⟨1733774, by rfl⟩ : syracuseStep 2311699 = 3467549) B3467549
theorem B9881311 : Blo 912577 9881311 := bstep (se 1 (by rfl) ⟨7410983, by rfl⟩ : syracuseStep 9881311 = 14821967) B14821967
theorem B2312135 : Blo 912577 2312135 := bstep (se 1 (by rfl) ⟨1734101, by rfl⟩ : syracuseStep 2312135 = 3468203) B3468203
theorem B1952095 : Blo 912577 1952095 := bstep (se 1 (by rfl) ⟨1464071, by rfl⟩ : syracuseStep 1952095 = 2928143) B2928143
theorem B6343105 : Blo 912577 6343105 := bstep (se 2 (by rfl) ⟨2378664, by rfl⟩ : syracuseStep 6343105 = 4757329) B4757329
theorem B2607623 : Blo 912577 2607623 := bstep (se 1 (by rfl) ⟨1955717, by rfl⟩ : syracuseStep 2607623 = 3911435) B3911435
theorem B3295775 : Blo 912577 3295775 := bstep (se 1 (by rfl) ⟨2471831, by rfl⟩ : syracuseStep 3295775 = 4943663) B4943663
theorem B2608271 : Blo 912577 2608271 := bstep (se 1 (by rfl) ⟨1956203, by rfl⟩ : syracuseStep 2608271 = 3912407) B3912407
theorem B7818767 : Blo 912577 7818767 := bstep (se 1 (by rfl) ⟨5864075, by rfl⟩ : syracuseStep 7818767 = 11728151) B11728151
theorem B9392345 : Blo 912577 9392345 := bstep (se 2 (by rfl) ⟨3522129, by rfl⟩ : syracuseStep 9392345 = 7044259) B7044259
theorem B1462655 : Blo 912577 1462655 := bstep (se 1 (by rfl) ⟨1096991, by rfl⟩ : syracuseStep 1462655 = 2193983) B2193983
theorem B2609911 : Blo 912577 2609911 := bstep (se 1 (by rfl) ⟨1957433, by rfl⟩ : syracuseStep 2609911 = 3914867) B3914867
theorem B5198863 : Blo 912577 5198863 := bstep (se 1 (by rfl) ⟨3899147, by rfl⟩ : syracuseStep 5198863 = 7798295) B7798295
theorem B6247439 : Blo 912577 6247439 := bstep (se 1 (by rfl) ⟨4685579, by rfl⟩ : syracuseStep 6247439 = 9371159) B9371159
theorem B1299511 : Blo 912577 1299511 := bstep (se 1 (by rfl) ⟨974633, by rfl⟩ : syracuseStep 1299511 = 1949267) B1949267
theorem B1954871 : Blo 912577 1954871 := bstep (se 1 (by rfl) ⟨1466153, by rfl⟩ : syracuseStep 1954871 = 2932307) B2932307
theorem B2348207 : Blo 912577 2348207 := bstep (se 1 (by rfl) ⟨1761155, by rfl⟩ : syracuseStep 2348207 = 3522311) B3522311
theorem B1954991 : Blo 912577 1954991 := bstep (se 1 (by rfl) ⟨1466243, by rfl⟩ : syracuseStep 1954991 = 2932487) B2932487
theorem B2053331 : Blo 912577 2053331 := bstep (se 1 (by rfl) ⟨1539998, by rfl⟩ : syracuseStep 2053331 = 3079997) B3079997
theorem B2970911 : Blo 912577 2970911 := bstep (se 1 (by rfl) ⟨2228183, by rfl⟩ : syracuseStep 2970911 = 4456367) B4456367
theorem B2053601 : Blo 912577 2053601 := bstep (se 2 (by rfl) ⟨770100, by rfl⟩ : syracuseStep 2053601 = 1540201) B1540201
theorem B1463975 : Blo 912577 1463975 := bstep (se 1 (by rfl) ⟨1097981, by rfl⟩ : syracuseStep 1463975 = 2195963) B2195963
theorem B1300303 : Blo 912577 1300303 := bstep (se 1 (by rfl) ⟨975227, by rfl⟩ : syracuseStep 1300303 = 1950455) B1950455
theorem B10410119 : Blo 912577 10410119 := bstep (se 1 (by rfl) ⟨7807589, by rfl⟩ : syracuseStep 10410119 = 15615179) B15615179
theorem B1235099 : Blo 912577 1235099 := bstep (se 1 (by rfl) ⟨926324, by rfl⟩ : syracuseStep 1235099 = 1852649) B1852649
theorem B2055239 : Blo 912577 2055239 := bstep (se 1 (by rfl) ⟨1541429, by rfl⟩ : syracuseStep 2055239 = 3082859) B3082859
theorem B9395453 : Blo 912577 9395453 := bstep (se 3 (by rfl) ⟨1761647, by rfl⟩ : syracuseStep 9395453 = 3523295) B3523295
theorem B1465609 : Blo 912577 1465609 := bstep (se 2 (by rfl) ⟨549603, by rfl⟩ : syracuseStep 1465609 = 1099207) B1099207
theorem B2055635 : Blo 912577 2055635 := bstep (se 1 (by rfl) ⟨1541726, by rfl⟩ : syracuseStep 2055635 = 3083453) B3083453
theorem B1957331 : Blo 912577 1957331 := bstep (se 1 (by rfl) ⟨1467998, by rfl⟩ : syracuseStep 1957331 = 2935997) B2935997
theorem B67788251 : Blo 912577 67788251 := bstep (se 1 (by rfl) ⟨50841188, by rfl⟩ : syracuseStep 67788251 = 101682377) B101682377
theorem B6249959 : Blo 912577 6249959 := bstep (se 1 (by rfl) ⟨4687469, by rfl⟩ : syracuseStep 6249959 = 9374939) B9374939
theorem B2317967 : Blo 912577 2317967 := bstep (se 1 (by rfl) ⟨1738475, by rfl⟩ : syracuseStep 2317967 = 3476951) B3476951
theorem B2055905 : Blo 912577 2055905 := bstep (se 2 (by rfl) ⟨770964, by rfl⟩ : syracuseStep 2055905 = 1541929) B1541929
theorem B63364999 : Blo 912577 63364999 := bstep (se 1 (by rfl) ⟨47523749, by rfl⟩ : syracuseStep 63364999 = 95047499) B95047499
theorem B1302427 : Blo 912577 1302427 := bstep (se 1 (by rfl) ⟨976820, by rfl⟩ : syracuseStep 1302427 = 1953641) B1953641
theorem B5857181 : Blo 912577 5857181 := bstep (se 3 (by rfl) ⟨1098221, by rfl⟩ : syracuseStep 5857181 = 2196443) B2196443
theorem B2319151 : Blo 912577 2319151 := bstep (se 1 (by rfl) ⟨1739363, by rfl⟩ : syracuseStep 2319151 = 3478727) B3478727
theorem B975727 : Blo 912577 975727 := bstep (se 1 (by rfl) ⟨731795, by rfl⟩ : syracuseStep 975727 = 1463591) B1463591
theorem B1369151 : Blo 912577 1369151 := bstep (se 1 (by rfl) ⟨1026863, by rfl⟩ : syracuseStep 1369151 = 2053727) B2053727
theorem B1369193 : Blo 912577 1369193 := bstep (se 2 (by rfl) ⟨513447, by rfl⟩ : syracuseStep 1369193 = 1026895) B1026895
theorem B49996973 : Blo 912577 49996973 := bstep (se 3 (by rfl) ⟨9374432, by rfl⟩ : syracuseStep 49996973 = 18748865) B18748865
theorem B1369295 : Blo 912577 1369295 := bstep (se 1 (by rfl) ⟨1026971, by rfl⟩ : syracuseStep 1369295 = 2053943) B2053943
theorem B14279971 : Blo 912577 14279971 := bstep (se 1 (by rfl) ⟨10709978, by rfl⟩ : syracuseStep 14279971 = 21419957) B21419957
theorem B2057579 : Blo 912577 2057579 := bstep (se 1 (by rfl) ⟨1543184, by rfl⟩ : syracuseStep 2057579 = 3086369) B3086369
theorem B1369499 : Blo 912577 1369499 := bstep (se 1 (by rfl) ⟨1027124, by rfl⟩ : syracuseStep 1369499 = 2054249) B2054249
theorem B3466745 : Blo 912577 3466745 := bstep (se 2 (by rfl) ⟨1300029, by rfl⟩ : syracuseStep 3466745 = 2600059) B2600059
theorem B1369721 : Blo 912577 1369721 := bstep (se 2 (by rfl) ⟨513645, by rfl⟩ : syracuseStep 1369721 = 1027291) B1027291
theorem B4941433 : Blo 912577 4941433 := bstep (se 2 (by rfl) ⟨1853037, by rfl⟩ : syracuseStep 4941433 = 3706075) B3706075
theorem B2057849 : Blo 912577 2057849 := bstep (se 2 (by rfl) ⟨771693, by rfl⟩ : syracuseStep 2057849 = 1543387) B1543387
theorem B1369823 : Blo 912577 1369823 := bstep (se 1 (by rfl) ⟨1027367, by rfl⟩ : syracuseStep 1369823 = 2054735) B2054735
theorem B1468127 : Blo 912577 1468127 := bstep (se 1 (by rfl) ⟨1101095, by rfl⟩ : syracuseStep 1468127 = 2202191) B2202191
theorem B1369919 : Blo 912577 1369919 := bstep (se 1 (by rfl) ⟨1027439, by rfl⟩ : syracuseStep 1369919 = 2054879) B2054879
theorem B1370087 : Blo 912577 1370087 := bstep (se 1 (by rfl) ⟨1027565, by rfl⟩ : syracuseStep 1370087 = 2055131) B2055131
theorem B1370105 : Blo 912577 1370105 := bstep (se 2 (by rfl) ⟨513789, by rfl⟩ : syracuseStep 1370105 = 1027579) B1027579
theorem B1370207 : Blo 912577 1370207 := bstep (se 1 (by rfl) ⟨1027655, by rfl⟩ : syracuseStep 1370207 = 2055311) B2055311
theorem B1370267 : Blo 912577 1370267 := bstep (se 1 (by rfl) ⟨1027700, by rfl⟩ : syracuseStep 1370267 = 2055401) B2055401
theorem B1370303 : Blo 912577 1370303 := bstep (se 1 (by rfl) ⟨1027727, by rfl⟩ : syracuseStep 1370303 = 2055455) B2055455
theorem B1370345 : Blo 912577 1370345 := bstep (se 2 (by rfl) ⟨513879, by rfl⟩ : syracuseStep 1370345 = 1027759) B1027759
theorem B5859641 : Blo 912577 5859641 := bstep (se 2 (by rfl) ⟨2197365, by rfl⟩ : syracuseStep 5859641 = 4394731) B4394731
theorem B1370651 : Blo 912577 1370651 := bstep (se 1 (by rfl) ⟨1027988, by rfl⟩ : syracuseStep 1370651 = 2055977) B2055977
theorem B1370729 : Blo 912577 1370729 := bstep (se 2 (by rfl) ⟨514023, by rfl⟩ : syracuseStep 1370729 = 1028047) B1028047
theorem B2058857 : Blo 912577 2058857 := bstep (se 2 (by rfl) ⟨772071, by rfl⟩ : syracuseStep 2058857 = 1544143) B1544143
theorem B7826179 : Blo 912577 7826179 := bstep (se 1 (by rfl) ⟨5869634, by rfl⟩ : syracuseStep 7826179 = 11739269) B11739269
theorem B4385755 : Blo 912577 4385755 := bstep (se 1 (by rfl) ⟨3289316, by rfl⟩ : syracuseStep 4385755 = 6578633) B6578633
theorem B1371257 : Blo 912577 1371257 := bstep (se 2 (by rfl) ⟨514221, by rfl⟩ : syracuseStep 1371257 = 1028443) B1028443
theorem B4385927 : Blo 912577 4385927 := bstep (se 1 (by rfl) ⟨3289445, by rfl⟩ : syracuseStep 4385927 = 6578891) B6578891
theorem B912607 : Blo 912577 912607 := bstep (se 1 (by rfl) ⟨684455, by rfl⟩ : syracuseStep 912607 = 1368911) B1368911
theorem B1371359 : Blo 912577 1371359 := bstep (se 1 (by rfl) ⟨1028519, by rfl⟩ : syracuseStep 1371359 = 2057039) B2057039
theorem B2059487 : Blo 912577 2059487 := bstep (se 1 (by rfl) ⟨1544615, by rfl⟩ : syracuseStep 2059487 = 3089231) B3089231
theorem B3468521 : Blo 912577 3468521 := bstep (se 2 (by rfl) ⟨1300695, by rfl⟩ : syracuseStep 3468521 = 2601391) B2601391
theorem B1371401 : Blo 912577 1371401 := bstep (se 2 (by rfl) ⟨514275, by rfl⟩ : syracuseStep 1371401 = 1028551) B1028551
theorem B1371503 : Blo 912577 1371503 := bstep (se 1 (by rfl) ⟨1028627, by rfl⟩ : syracuseStep 1371503 = 2057255) B2057255
theorem B11103641 : Blo 912577 11103641 := bstep (se 2 (by rfl) ⟨4163865, by rfl⟩ : syracuseStep 11103641 = 8327731) B8327731
theorem B2059703 : Blo 912577 2059703 := bstep (se 1 (by rfl) ⟨1544777, by rfl⟩ : syracuseStep 2059703 = 3089555) B3089555
theorem B912871 : Blo 912577 912871 := bstep (se 1 (by rfl) ⟨684653, by rfl⟩ : syracuseStep 912871 = 1369307) B1369307
theorem B1371623 : Blo 912577 1371623 := bstep (se 1 (by rfl) ⟨1028717, by rfl⟩ : syracuseStep 1371623 = 2057435) B2057435
theorem B912987 : Blo 912577 912987 := bstep (se 1 (by rfl) ⟨684740, by rfl⟩ : syracuseStep 912987 = 1369481) B1369481
theorem B1371755 : Blo 912577 1371755 := bstep (se 1 (by rfl) ⟨1028816, by rfl⟩ : syracuseStep 1371755 = 2057633) B2057633
theorem B2059883 : Blo 912577 2059883 := bstep (se 1 (by rfl) ⟨1544912, by rfl⟩ : syracuseStep 2059883 = 3089825) B3089825
theorem B1371881 : Blo 912577 1371881 := bstep (se 2 (by rfl) ⟨514455, by rfl⟩ : syracuseStep 1371881 = 1028911) B1028911
theorem B913223 : Blo 912577 913223 := bstep (se 1 (by rfl) ⟨684917, by rfl⟩ : syracuseStep 913223 = 1369835) B1369835
theorem B1372025 : Blo 912577 1372025 := bstep (se 2 (by rfl) ⟨514509, by rfl⟩ : syracuseStep 1372025 = 1029019) B1029019
theorem B2060153 : Blo 912577 2060153 := bstep (se 2 (by rfl) ⟨772557, by rfl⟩ : syracuseStep 2060153 = 1545115) B1545115
theorem B2781067 : Blo 912577 2781067 := bstep (se 1 (by rfl) ⟨2085800, by rfl⟩ : syracuseStep 2781067 = 4171601) B4171601
theorem B913375 : Blo 912577 913375 := bstep (se 1 (by rfl) ⟨685031, by rfl⟩ : syracuseStep 913375 = 1370063) B1370063
theorem B1372127 : Blo 912577 1372127 := bstep (se 1 (by rfl) ⟨1029095, by rfl⟩ : syracuseStep 1372127 = 2058191) B2058191
theorem B6582323 : Blo 912577 6582323 := bstep (se 1 (by rfl) ⟨4936742, by rfl⟩ : syracuseStep 6582323 = 9873485) B9873485
theorem B1372379 : Blo 912577 1372379 := bstep (se 1 (by rfl) ⟨1029284, by rfl⟩ : syracuseStep 1372379 = 2058569) B2058569
theorem B913639 : Blo 912577 913639 := bstep (se 1 (by rfl) ⟨685229, by rfl⟩ : syracuseStep 913639 = 1370459) B1370459
theorem B1372391 : Blo 912577 1372391 := bstep (se 1 (by rfl) ⟨1029293, by rfl⟩ : syracuseStep 1372391 = 2058587) B2058587
theorem B4387081 : Blo 912577 4387081 := bstep (se 2 (by rfl) ⟨1645155, by rfl⟩ : syracuseStep 4387081 = 3290311) B3290311
theorem B913791 : Blo 912577 913791 := bstep (se 1 (by rfl) ⟨685343, by rfl⟩ : syracuseStep 913791 = 1370687) B1370687
theorem B1372553 : Blo 912577 1372553 := bstep (se 2 (by rfl) ⟨514707, by rfl⟩ : syracuseStep 1372553 = 1029415) B1029415
theorem B913871 : Blo 912577 913871 := bstep (se 1 (by rfl) ⟨685403, by rfl⟩ : syracuseStep 913871 = 1370807) B1370807
theorem B1372649 : Blo 912577 1372649 := bstep (se 2 (by rfl) ⟨514743, by rfl⟩ : syracuseStep 1372649 = 1029487) B1029487
theorem B914023 : Blo 912577 914023 := bstep (se 1 (by rfl) ⟨685517, by rfl⟩ : syracuseStep 914023 = 1371035) B1371035
theorem B1372775 : Blo 912577 1372775 := bstep (se 1 (by rfl) ⟨1029581, by rfl⟩ : syracuseStep 1372775 = 2059163) B2059163
theorem B1372907 : Blo 912577 1372907 := bstep (se 1 (by rfl) ⟨1029680, by rfl⟩ : syracuseStep 1372907 = 2059361) B2059361
theorem B1372937 : Blo 912577 1372937 := bstep (se 2 (by rfl) ⟨514851, by rfl⟩ : syracuseStep 1372937 = 1029703) B1029703
theorem B914287 : Blo 912577 914287 := bstep (se 1 (by rfl) ⟨685715, by rfl⟩ : syracuseStep 914287 = 1371431) B1371431
theorem B1373039 : Blo 912577 1373039 := bstep (se 1 (by rfl) ⟨1029779, by rfl⟩ : syracuseStep 1373039 = 2059559) B2059559
theorem B914343 : Blo 912577 914343 := bstep (se 1 (by rfl) ⟨685757, by rfl⟩ : syracuseStep 914343 = 1371515) B1371515
theorem B914427 : Blo 912577 914427 := bstep (se 1 (by rfl) ⟨685820, by rfl⟩ : syracuseStep 914427 = 1371641) B1371641
theorem B914495 : Blo 912577 914495 := bstep (se 1 (by rfl) ⟨685871, by rfl⟩ : syracuseStep 914495 = 1371743) B1371743
theorem B1373291 : Blo 912577 1373291 := bstep (se 1 (by rfl) ⟨1029968, by rfl⟩ : syracuseStep 1373291 = 2059937) B2059937
theorem B6255755 : Blo 912577 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B914639 : Blo 912577 914639 := bstep (se 1 (by rfl) ⟨685979, by rfl⟩ : syracuseStep 914639 = 1371959) B1371959
theorem B11105585 : Blo 912577 11105585 := bstep (se 2 (by rfl) ⟨4164594, by rfl⟩ : syracuseStep 11105585 = 8329189) B8329189
theorem B1373531 : Blo 912577 1373531 := bstep (se 1 (by rfl) ⟨1030148, by rfl⟩ : syracuseStep 1373531 = 2060297) B2060297
theorem B914843 : Blo 912577 914843 := bstep (se 1 (by rfl) ⟨686132, by rfl⟩ : syracuseStep 914843 = 1372265) B1372265
theorem B915055 : Blo 912577 915055 := bstep (se 1 (by rfl) ⟨686291, by rfl⟩ : syracuseStep 915055 = 1372583) B1372583
theorem B1373807 : Blo 912577 1373807 := bstep (se 1 (by rfl) ⟨1030355, by rfl⟩ : syracuseStep 1373807 = 2060711) B2060711
theorem B915111 : Blo 912577 915111 := bstep (se 1 (by rfl) ⟨686333, by rfl⟩ : syracuseStep 915111 = 1372667) B1372667
theorem B1373879 : Blo 912577 1373879 := bstep (se 1 (by rfl) ⟨1030409, by rfl⟩ : syracuseStep 1373879 = 2060819) B2060819
theorem B2062007 : Blo 912577 2062007 := bstep (se 1 (by rfl) ⟨1546505, by rfl⟩ : syracuseStep 2062007 = 3093011) B3093011
theorem B10581707 : Blo 912577 10581707 := bstep (se 1 (by rfl) ⟨7936280, by rfl⟩ : syracuseStep 10581707 = 15872561) B15872561
theorem B1373915 : Blo 912577 1373915 := bstep (se 1 (by rfl) ⟨1030436, by rfl⟩ : syracuseStep 1373915 = 2060873) B2060873
theorem B915195 : Blo 912577 915195 := bstep (se 1 (by rfl) ⟨686396, by rfl⟩ : syracuseStep 915195 = 1372793) B1372793
theorem B915231 : Blo 912577 915231 := bstep (se 1 (by rfl) ⟨686423, by rfl⟩ : syracuseStep 915231 = 1372847) B1372847
theorem B915263 : Blo 912577 915263 := bstep (se 1 (by rfl) ⟨686447, by rfl⟩ : syracuseStep 915263 = 1372895) B1372895
theorem B1374089 : Blo 912577 1374089 := bstep (se 2 (by rfl) ⟨515283, by rfl⟩ : syracuseStep 1374089 = 1030567) B1030567
theorem B915439 : Blo 912577 915439 := bstep (se 1 (by rfl) ⟨686579, by rfl⟩ : syracuseStep 915439 = 1373159) B1373159
theorem B1374191 : Blo 912577 1374191 := bstep (se 1 (by rfl) ⟨1030643, by rfl⟩ : syracuseStep 1374191 = 2061287) B2061287
theorem B915611 : Blo 912577 915611 := bstep (se 1 (by rfl) ⟨686708, by rfl⟩ : syracuseStep 915611 = 1373417) B1373417
theorem B6944939 : Blo 912577 6944939 := bstep (se 1 (by rfl) ⟨5208704, by rfl⟩ : syracuseStep 6944939 = 10417409) B10417409
theorem B915647 : Blo 912577 915647 := bstep (se 1 (by rfl) ⟨686735, by rfl⟩ : syracuseStep 915647 = 1373471) B1373471
theorem B1374443 : Blo 912577 1374443 := bstep (se 1 (by rfl) ⟨1030832, by rfl⟩ : syracuseStep 1374443 = 2061665) B2061665
theorem B1374503 : Blo 912577 1374503 := bstep (se 1 (by rfl) ⟨1030877, by rfl⟩ : syracuseStep 1374503 = 2061755) B2061755
theorem B915759 : Blo 912577 915759 := bstep (se 1 (by rfl) ⟨686819, by rfl⟩ : syracuseStep 915759 = 1373639) B1373639
theorem B1374587 : Blo 912577 1374587 := bstep (se 1 (by rfl) ⟨1030940, by rfl⟩ : syracuseStep 1374587 = 2061881) B2061881
theorem B915995 : Blo 912577 915995 := bstep (se 1 (by rfl) ⟨686996, by rfl⟩ : syracuseStep 915995 = 1373993) B1373993
theorem B915999 : Blo 912577 915999 := bstep (se 1 (by rfl) ⟨686999, by rfl⟩ : syracuseStep 915999 = 1373999) B1373999
theorem B1374857 : Blo 912577 1374857 := bstep (se 2 (by rfl) ⟨515571, by rfl⟩ : syracuseStep 1374857 = 1031143) B1031143
theorem B26409665 : Blo 912577 26409665 := bstep (se 2 (by rfl) ⟨9903624, by rfl⟩ : syracuseStep 26409665 = 19807249) B19807249
theorem B916315 : Blo 912577 916315 := bstep (se 1 (by rfl) ⟨687236, by rfl⟩ : syracuseStep 916315 = 1374473) B1374473
theorem B23755639 : Blo 912577 23755639 := bstep (se 1 (by rfl) ⟨17816729, by rfl⟩ : syracuseStep 23755639 = 35633459) B35633459
theorem B916383 : Blo 912577 916383 := bstep (se 1 (by rfl) ⟨687287, by rfl⟩ : syracuseStep 916383 = 1374575) B1374575
theorem B916527 : Blo 912577 916527 := bstep (se 1 (by rfl) ⟨687395, by rfl⟩ : syracuseStep 916527 = 1374791) B1374791
theorem B916551 : Blo 912577 916551 := bstep (se 1 (by rfl) ⟨687413, by rfl⟩ : syracuseStep 916551 = 1374827) B1374827
theorem B1736167 : Blo 912577 1736167 := bstep (se 1 (by rfl) ⟨1302125, by rfl⟩ : syracuseStep 1736167 = 2604251) B2604251
theorem B1736417 : Blo 912577 1736417 := bstep (se 2 (by rfl) ⟨651156, by rfl⟩ : syracuseStep 1736417 = 1302313) B1302313
theorem B5210027 : Blo 912577 5210027 := bstep (se 1 (by rfl) ⟨3907520, by rfl⟩ : syracuseStep 5210027 = 7815041) B7815041
theorem B2785871 : Blo 912577 2785871 := bstep (se 1 (by rfl) ⟨2089403, by rfl⟩ : syracuseStep 2785871 = 4178807) B4178807
theorem B1540795 : Blo 912577 1540795 := bstep (se 1 (by rfl) ⟨1155596, by rfl⟩ : syracuseStep 1540795 = 2311193) B2311193
theorem B2196155 : Blo 912577 2196155 := bstep (se 1 (by rfl) ⟨1647116, by rfl⟩ : syracuseStep 2196155 = 3294233) B3294233
theorem B4227851 : Blo 912577 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B3900413 : Blo 912577 3900413 := bstep (se 3 (by rfl) ⟨731327, by rfl⟩ : syracuseStep 3900413 = 1462655) B1462655
theorem B3343357 : Blo 912577 3343357 := bstep (se 3 (by rfl) ⟨626879, by rfl⟩ : syracuseStep 3343357 = 1253759) B1253759
theorem B1541423 : Blo 912577 1541423 := bstep (se 1 (by rfl) ⟨1156067, by rfl⟩ : syracuseStep 1541423 = 2312135) B2312135
theorem B3081563 : Blo 912577 3081563 := bstep (se 1 (by rfl) ⟨2311172, by rfl⟩ : syracuseStep 3081563 = 4622345) B4622345
theorem B10421783 : Blo 912577 10421783 := bstep (se 1 (by rfl) ⟨7816337, by rfl⟩ : syracuseStep 10421783 = 15632675) B15632675
theorem B3081833 : Blo 912577 3081833 := bstep (se 2 (by rfl) ⟨1155687, by rfl⟩ : syracuseStep 3081833 = 2311375) B2311375
theorem B1738415 : Blo 912577 1738415 := bstep (se 1 (by rfl) ⟨1303811, by rfl⟩ : syracuseStep 1738415 = 2607623) B2607623
theorem B19039961 : Blo 912577 19039961 := bstep (se 2 (by rfl) ⟨7139985, by rfl⟩ : syracuseStep 19039961 = 14279971) B14279971
theorem B3081995 : Blo 912577 3081995 := bstep (se 1 (by rfl) ⟨2311496, by rfl⟩ : syracuseStep 3081995 = 4622993) B4622993
theorem B3082265 : Blo 912577 3082265 := bstep (se 2 (by rfl) ⟨1155849, by rfl⟩ : syracuseStep 3082265 = 2311699) B2311699
theorem B1738847 : Blo 912577 1738847 := bstep (se 1 (by rfl) ⟨1304135, by rfl⟩ : syracuseStep 1738847 = 2608271) B2608271
theorem B6588577 : Blo 912577 6588577 := bstep (se 2 (by rfl) ⟨2470716, by rfl⟩ : syracuseStep 6588577 = 4941433) B4941433
theorem B3082427 : Blo 912577 3082427 := bstep (se 1 (by rfl) ⟨2311820, by rfl⟩ : syracuseStep 3082427 = 4623641) B4623641
theorem B13175081 : Blo 912577 13175081 := bstep (se 2 (by rfl) ⟨4940655, by rfl⟩ : syracuseStep 13175081 = 9881311) B9881311
theorem B5212511 : Blo 912577 5212511 := bstep (se 1 (by rfl) ⟨3909383, by rfl⟩ : syracuseStep 5212511 = 7818767) B7818767
theorem B6261563 : Blo 912577 6261563 := bstep (se 1 (by rfl) ⟨4696172, by rfl⟩ : syracuseStep 6261563 = 9392345) B9392345
theorem B7801919 : Blo 912577 7801919 := bstep (se 1 (by rfl) ⟨5851439, by rfl⟩ : syracuseStep 7801919 = 11702879) B11702879
theorem B8457473 : Blo 912577 8457473 := bstep (se 2 (by rfl) ⟨3171552, by rfl⟩ : syracuseStep 8457473 = 6343105) B6343105
theorem B4164959 : Blo 912577 4164959 := bstep (se 1 (by rfl) ⟨3123719, by rfl⟩ : syracuseStep 4164959 = 6247439) B6247439
theorem B3083615 : Blo 912577 3083615 := bstep (se 1 (by rfl) ⟨2312711, by rfl⟩ : syracuseStep 3083615 = 4625423) B4625423
theorem B3084155 : Blo 912577 3084155 := bstep (se 1 (by rfl) ⟨2313116, by rfl⟩ : syracuseStep 3084155 = 4626233) B4626233
theorem B15831553 : Blo 912577 15831553 := bstep (se 2 (by rfl) ⟨5936832, by rfl⟩ : syracuseStep 15831553 = 11873665) B11873665
theorem B6263635 : Blo 912577 6263635 := bstep (se 1 (by rfl) ⟨4697726, by rfl⟩ : syracuseStep 6263635 = 9395453) B9395453
theorem B45192167 : Blo 912577 45192167 := bstep (se 1 (by rfl) ⟨33894125, by rfl⟩ : syracuseStep 45192167 = 67788251) B67788251
theorem B4166639 : Blo 912577 4166639 := bstep (se 1 (by rfl) ⟨3124979, by rfl⟩ : syracuseStep 4166639 = 6249959) B6249959
theorem B1545311 : Blo 912577 1545311 := bstep (se 1 (by rfl) ⟨1158983, by rfl⟩ : syracuseStep 1545311 = 2317967) B2317967
theorem B3708089 : Blo 912577 3708089 := bstep (se 2 (by rfl) ⟨1390533, by rfl⟩ : syracuseStep 3708089 = 2781067) B2781067
theorem B6329573 : Blo 912577 6329573 := bstep (se 4 (by rfl) ⟨593397, by rfl⟩ : syracuseStep 6329573 = 1186795) B1186795
theorem B3904787 : Blo 912577 3904787 := bstep (se 1 (by rfl) ⟨2928590, by rfl⟩ : syracuseStep 3904787 = 5857181) B5857181
theorem B3478895 : Blo 912577 3478895 := bstep (se 1 (by rfl) ⟨2609171, by rfl⟩ : syracuseStep 3478895 = 5218343) B5218343
theorem B4396463 : Blo 912577 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B8787845 : Blo 912577 8787845 := bstep (se 4 (by rfl) ⟨823860, by rfl⟩ : syracuseStep 8787845 = 1647721) B1647721
theorem B13178771 : Blo 912577 13178771 := bstep (se 1 (by rfl) ⟨9884078, by rfl⟩ : syracuseStep 13178771 = 19768157) B19768157
theorem B3479881 : Blo 912577 3479881 := bstep (se 2 (by rfl) ⟨1304955, by rfl⟩ : syracuseStep 3479881 = 2609911) B2609911
theorem B14817815 : Blo 912577 14817815 := bstep (se 1 (by rfl) ⟨11113361, by rfl⟩ : syracuseStep 14817815 = 22226723) B22226723
theorem B8788733 : Blo 912577 8788733 := bstep (se 3 (by rfl) ⟨1647887, by rfl⟩ : syracuseStep 8788733 = 3295775) B3295775
theorem B3906427 : Blo 912577 3906427 := bstep (se 1 (by rfl) ⟨2929820, by rfl⟩ : syracuseStep 3906427 = 5859641) B5859641
theorem B2923951 : Blo 912577 2923951 := bstep (se 1 (by rfl) ⟨2192963, by rfl⟩ : syracuseStep 2923951 = 4385927) B4385927
theorem B925351 : Blo 912577 925351 := bstep (se 1 (by rfl) ⟨694013, by rfl⟩ : syracuseStep 925351 = 1388027) B1388027
theorem B11116385 : Blo 912577 11116385 := bstep (se 2 (by rfl) ⟨4168644, by rfl⟩ : syracuseStep 11116385 = 8337289) B8337289
theorem B2924669 : Blo 912577 2924669 := bstep (se 3 (by rfl) ⟨548375, by rfl⟩ : syracuseStep 2924669 = 1096751) B1096751
theorem B4170503 : Blo 912577 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B7054471 : Blo 912577 7054471 := bstep (se 1 (by rfl) ⟨5290853, by rfl⟩ : syracuseStep 7054471 = 10581707) B10581707
theorem B5219549 : Blo 912577 5219549 := bstep (se 3 (by rfl) ⟨978665, by rfl⟩ : syracuseStep 5219549 = 1957331) B1957331
theorem B4629959 : Blo 912577 4629959 := bstep (se 1 (by rfl) ⟨3472469, by rfl⟩ : syracuseStep 4629959 = 6944939) B6944939
theorem B5875361 : Blo 912577 5875361 := bstep (se 2 (by rfl) ⟨2203260, by rfl⟩ : syracuseStep 5875361 = 4406521) B4406521
theorem B17606443 : Blo 912577 17606443 := bstep (se 1 (by rfl) ⟨13204832, by rfl⟩ : syracuseStep 17606443 = 26409665) B26409665
theorem B4630445 : Blo 912577 4630445 := bstep (se 3 (by rfl) ⟨868208, by rfl⟩ : syracuseStep 4630445 = 1736417) B1736417
theorem B3090743 : Blo 912577 3090743 := bstep (se 1 (by rfl) ⟨2318057, by rfl⟩ : syracuseStep 3090743 = 4636115) B4636115
theorem B84486665 : Blo 912577 84486665 := bstep (se 2 (by rfl) ⟨31682499, by rfl⟩ : syracuseStep 84486665 = 63364999) B63364999
theorem B4631255 : Blo 912577 4631255 := bstep (se 1 (by rfl) ⟨3473441, by rfl⟩ : syracuseStep 4631255 = 6946883) B6946883
theorem B1027039 : Blo 912577 1027039 := bstep (se 1 (by rfl) ⟨770279, by rfl⟩ : syracuseStep 1027039 = 1540559) B1540559
theorem B4402151 : Blo 912577 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B15805783 : Blo 912577 15805783 := bstep (se 1 (by rfl) ⟨11854337, by rfl⟩ : syracuseStep 15805783 = 23708675) B23708675
theorem B1650143 : Blo 912577 1650143 := bstep (se 1 (by rfl) ⟨1237607, by rfl⟩ : syracuseStep 1650143 = 2475215) B2475215
theorem B6336001 : Blo 912577 6336001 := bstep (se 2 (by rfl) ⟨2376000, by rfl⟩ : syracuseStep 6336001 = 4752001) B4752001
theorem B4632065 : Blo 912577 4632065 := bstep (se 2 (by rfl) ⟨1737024, by rfl⟩ : syracuseStep 4632065 = 3474049) B3474049
theorem B1027687 : Blo 912577 1027687 := bstep (se 1 (by rfl) ⟨770765, by rfl⟩ : syracuseStep 1027687 = 1541531) B1541531
theorem B7810667 : Blo 912577 7810667 := bstep (se 1 (by rfl) ⟨5858000, by rfl⟩ : syracuseStep 7810667 = 11716001) B11716001
theorem B3092201 : Blo 912577 3092201 := bstep (se 2 (by rfl) ⟨1159575, by rfl⟩ : syracuseStep 3092201 = 2319151) B2319151
theorem B1027903 : Blo 912577 1027903 := bstep (se 1 (by rfl) ⟨770927, by rfl⟩ : syracuseStep 1027903 = 1541855) B1541855
theorem B3911759 : Blo 912577 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B1028191 : Blo 912577 1028191 := bstep (se 1 (by rfl) ⟨771143, by rfl⟩ : syracuseStep 1028191 = 1542287) B1542287
theorem B4632875 : Blo 912577 4632875 := bstep (se 1 (by rfl) ⟨3474656, by rfl⟩ : syracuseStep 4632875 = 6949313) B6949313
theorem B2601791 : Blo 912577 2601791 := bstep (se 1 (by rfl) ⟨1951343, by rfl⟩ : syracuseStep 2601791 = 3902687) B3902687
theorem B4699579 : Blo 912577 4699579 := bstep (se 1 (by rfl) ⟨3524684, by rfl⟩ : syracuseStep 4699579 = 7049369) B7049369
theorem B2602793 : Blo 912577 2602793 := bstep (se 2 (by rfl) ⟨976047, by rfl⟩ : syracuseStep 2602793 = 1952095) B1952095
theorem B7518347 : Blo 912577 7518347 := bstep (se 1 (by rfl) ⟨5638760, by rfl⟩ : syracuseStep 7518347 = 11277521) B11277521
theorem B1980607 : Blo 912577 1980607 := bstep (se 1 (by rfl) ⟨1485455, by rfl⟩ : syracuseStep 1980607 = 2970911) B2970911
theorem B10434905 : Blo 912577 10434905 := bstep (se 2 (by rfl) ⟨3913089, by rfl⟩ : syracuseStep 10434905 = 7826179) B7826179
theorem B3914183 : Blo 912577 3914183 := bstep (se 1 (by rfl) ⟨2935637, by rfl⟩ : syracuseStep 3914183 = 5871275) B5871275
theorem B4635143 : Blo 912577 4635143 := bstep (se 1 (by rfl) ⟨3476357, by rfl⟩ : syracuseStep 4635143 = 6952715) B6952715
theorem B1030747 : Blo 912577 1030747 := bstep (se 1 (by rfl) ⟨773060, by rfl⟩ : syracuseStep 1030747 = 1546121) B1546121
theorem B5847673 : Blo 912577 5847673 := bstep (se 2 (by rfl) ⟨2192877, by rfl⟩ : syracuseStep 5847673 = 4385755) B4385755
theorem B1031035 : Blo 912577 1031035 := bstep (se 1 (by rfl) ⟨773276, by rfl⟩ : syracuseStep 1031035 = 1546553) B1546553
theorem B4635629 : Blo 912577 4635629 := bstep (se 3 (by rfl) ⟨869180, by rfl⟩ : syracuseStep 4635629 = 1738361) B1738361
theorem B6602303 : Blo 912577 6602303 := bstep (se 1 (by rfl) ⟨4951727, by rfl⟩ : syracuseStep 6602303 = 9903455) B9903455
theorem B2342623 : Blo 912577 2342623 := bstep (se 1 (by rfl) ⟨1756967, by rfl⟩ : syracuseStep 2342623 = 3513935) B3513935
theorem B4636439 : Blo 912577 4636439 := bstep (se 1 (by rfl) ⟨3477329, by rfl⟩ : syracuseStep 4636439 = 6954659) B6954659
theorem B5849441 : Blo 912577 5849441 := bstep (se 2 (by rfl) ⟨2193540, by rfl⟩ : syracuseStep 5849441 = 4387081) B4387081
theorem B18792809 : Blo 912577 18792809 := bstep (se 2 (by rfl) ⟨7047303, by rfl⟩ : syracuseStep 18792809 = 14094607) B14094607
theorem B3293597 : Blo 912577 3293597 := bstep (se 3 (by rfl) ⟨617549, by rfl⟩ : syracuseStep 3293597 = 1235099) B1235099
theorem B2933435 : Blo 912577 2933435 := bstep (se 1 (by rfl) ⟨2200076, by rfl⟩ : syracuseStep 2933435 = 4400153) B4400153
theorem B2311163 : Blo 912577 2311163 := bstep (se 1 (by rfl) ⟨1733372, by rfl⟩ : syracuseStep 2311163 = 3466745) B3466745
theorem B5948471 : Blo 912577 5948471 := bstep (se 1 (by rfl) ⟨4461353, by rfl⟩ : syracuseStep 5948471 = 8922707) B8922707
theorem B6931817 : Blo 912577 6931817 := bstep (se 2 (by rfl) ⟨2599431, by rfl⟩ : syracuseStep 6931817 = 5198863) B5198863
theorem B4638059 : Blo 912577 4638059 := bstep (se 1 (by rfl) ⟨3478544, by rfl⟩ : syracuseStep 4638059 = 6957089) B6957089
theorem B1099711 : Blo 912577 1099711 := bstep (se 1 (by rfl) ⟨824783, by rfl⟩ : syracuseStep 1099711 = 1649567) B1649567
theorem B13158359 : Blo 912577 13158359 := bstep (se 1 (by rfl) ⟨9868769, by rfl⟩ : syracuseStep 13158359 = 19737539) B19737539
theorem B2312347 : Blo 912577 2312347 := bstep (se 1 (by rfl) ⟨1734260, by rfl⟩ : syracuseStep 2312347 = 3468521) B3468521
theorem B3262619 : Blo 912577 3262619 := bstep (se 1 (by rfl) ⟨2446964, by rfl⟩ : syracuseStep 3262619 = 4893929) B4893929
theorem B2935433 : Blo 912577 2935433 := bstep (se 2 (by rfl) ⟨1100787, by rfl⟩ : syracuseStep 2935433 = 2201575) B2201575
theorem B31674185 : Blo 912577 31674185 := bstep (se 2 (by rfl) ⟨11877819, by rfl⟩ : syracuseStep 31674185 = 23755639) B23755639
theorem B2609023 : Blo 912577 2609023 := bstep (se 1 (by rfl) ⟨1956767, by rfl⟩ : syracuseStep 2609023 = 3913535) B3913535
theorem B2084959 : Blo 912577 2084959 := bstep (se 1 (by rfl) ⟨1563719, by rfl⟩ : syracuseStep 2084959 = 3127439) B3127439
theorem B1954145 : Blo 912577 1954145 := bstep (se 2 (by rfl) ⟨732804, by rfl⟩ : syracuseStep 1954145 = 1465609) B1465609
theorem B2314889 : Blo 912577 2314889 := bstep (se 2 (by rfl) ⟨868083, by rfl⟩ : syracuseStep 2314889 = 1736167) B1736167
theorem B56251097 : Blo 912577 56251097 := bstep (se 2 (by rfl) ⟨21094161, by rfl⟩ : syracuseStep 56251097 = 42188323) B42188323
theorem B2085983 : Blo 912577 2085983 := bstep (se 1 (by rfl) ⟨1564487, by rfl⟩ : syracuseStep 2085983 = 3128975) B3128975
theorem B17552861 : Blo 912577 17552861 := bstep (se 3 (by rfl) ⟨3291161, by rfl⟩ : syracuseStep 17552861 = 6582323) B6582323
theorem B2053799 : Blo 912577 2053799 := bstep (se 1 (by rfl) ⟨1540349, by rfl⟩ : syracuseStep 2053799 = 3080699) B3080699
theorem B2053979 : Blo 912577 2053979 := bstep (se 1 (by rfl) ⟨1540484, by rfl⟩ : syracuseStep 2053979 = 3080969) B3080969
theorem B1956059 : Blo 912577 1956059 := bstep (se 1 (by rfl) ⟨1467044, by rfl⟩ : syracuseStep 1956059 = 2934089) B2934089
theorem B2054483 : Blo 912577 2054483 := bstep (se 1 (by rfl) ⟨1540862, by rfl⟩ : syracuseStep 2054483 = 3081725) B3081725
theorem B1300969 : Blo 912577 1300969 := bstep (se 2 (by rfl) ⟨487863, by rfl⟩ : syracuseStep 1300969 = 975727) B975727
theorem B2054969 : Blo 912577 2054969 := bstep (se 2 (by rfl) ⟨770613, by rfl⟩ : syracuseStep 2054969 = 1541227) B1541227
theorem B2055023 : Blo 912577 2055023 := bstep (se 1 (by rfl) ⟨1541267, by rfl⟩ : syracuseStep 2055023 = 3082535) B3082535
theorem B7036001 : Blo 912577 7036001 := bstep (se 2 (by rfl) ⟨2638500, by rfl⟩ : syracuseStep 7036001 = 5277001) B5277001
theorem B2055599 : Blo 912577 2055599 := bstep (se 1 (by rfl) ⟨1541699, by rfl⟩ : syracuseStep 2055599 = 3083399) B3083399
theorem B2055671 : Blo 912577 2055671 := bstep (se 1 (by rfl) ⟨1541753, by rfl⟩ : syracuseStep 2055671 = 3083507) B3083507
theorem B38101211 : Blo 912577 38101211 := bstep (se 1 (by rfl) ⟨28575908, by rfl⟩ : syracuseStep 38101211 = 57151817) B57151817
theorem B133325261 : Blo 912577 133325261 := bstep (se 3 (by rfl) ⟨24998486, by rfl⟩ : syracuseStep 133325261 = 49996973) B49996973
theorem B2056697 : Blo 912577 2056697 := bstep (se 2 (by rfl) ⟨771261, by rfl⟩ : syracuseStep 2056697 = 1542523) B1542523
theorem B2056787 : Blo 912577 2056787 := bstep (se 1 (by rfl) ⟨1542590, by rfl⟩ : syracuseStep 2056787 = 3085181) B3085181
theorem B1303247 : Blo 912577 1303247 := bstep (se 1 (by rfl) ⟨977435, by rfl⟩ : syracuseStep 1303247 = 1954871) B1954871
theorem B2056967 : Blo 912577 2056967 := bstep (se 1 (by rfl) ⟨1542725, by rfl⟩ : syracuseStep 2056967 = 3085451) B3085451
theorem B1565471 : Blo 912577 1565471 := bstep (se 1 (by rfl) ⟨1174103, by rfl⟩ : syracuseStep 1565471 = 2348207) B2348207
theorem B1303327 : Blo 912577 1303327 := bstep (se 1 (by rfl) ⟨977495, by rfl⟩ : syracuseStep 1303327 = 1954991) B1954991
theorem B1368887 : Blo 912577 1368887 := bstep (se 1 (by rfl) ⟨1026665, by rfl⟩ : syracuseStep 1368887 = 2053331) B2053331
theorem B2057057 : Blo 912577 2057057 := bstep (se 2 (by rfl) ⟨771396, by rfl⟩ : syracuseStep 2057057 = 1542793) B1542793
theorem B1369067 : Blo 912577 1369067 := bstep (se 1 (by rfl) ⟨1026800, by rfl⟩ : syracuseStep 1369067 = 2053601) B2053601
theorem B1467371 : Blo 912577 1467371 := bstep (se 1 (by rfl) ⟨1100528, by rfl⟩ : syracuseStep 1467371 = 2201057) B2201057
theorem B975983 : Blo 912577 975983 := bstep (se 1 (by rfl) ⟨731987, by rfl⟩ : syracuseStep 975983 = 1463975) B1463975
theorem B6940079 : Blo 912577 6940079 := bstep (se 1 (by rfl) ⟨5205059, by rfl⟩ : syracuseStep 6940079 = 10410119) B10410119
theorem B4941587 : Blo 912577 4941587 := bstep (se 1 (by rfl) ⟨3706190, by rfl⟩ : syracuseStep 4941587 = 7412381) B7412381
theorem B2058047 : Blo 912577 2058047 := bstep (se 1 (by rfl) ⟨1543535, by rfl⟩ : syracuseStep 2058047 = 3087071) B3087071
theorem B5859179 : Blo 912577 5859179 := bstep (se 1 (by rfl) ⟨4394384, by rfl⟩ : syracuseStep 5859179 = 8788769) B8788769
theorem B1370159 : Blo 912577 1370159 := bstep (se 1 (by rfl) ⟨1027619, by rfl⟩ : syracuseStep 1370159 = 2055239) B2055239
theorem B1370423 : Blo 912577 1370423 := bstep (se 1 (by rfl) ⟨1027817, by rfl⟩ : syracuseStep 1370423 = 2055635) B2055635
theorem B2058551 : Blo 912577 2058551 := bstep (se 1 (by rfl) ⟨1543913, by rfl⟩ : syracuseStep 2058551 = 3087827) B3087827
theorem B1370603 : Blo 912577 1370603 := bstep (se 1 (by rfl) ⟨1027952, by rfl⟩ : syracuseStep 1370603 = 2055905) B2055905
theorem B2058731 : Blo 912577 2058731 := bstep (se 1 (by rfl) ⟨1544048, by rfl⟩ : syracuseStep 2058731 = 3088097) B3088097
theorem B1371305 : Blo 912577 1371305 := bstep (se 2 (by rfl) ⟨514239, by rfl⟩ : syracuseStep 1371305 = 1028479) B1028479
theorem B2059433 : Blo 912577 2059433 := bstep (se 2 (by rfl) ⟨772287, by rfl⟩ : syracuseStep 2059433 = 1544575) B1544575
theorem B912767 : Blo 912577 912767 := bstep (se 1 (by rfl) ⟨684575, by rfl⟩ : syracuseStep 912767 = 1369151) B1369151
theorem B912795 : Blo 912577 912795 := bstep (se 1 (by rfl) ⟨684596, by rfl⟩ : syracuseStep 912795 = 1369193) B1369193
theorem B912863 : Blo 912577 912863 := bstep (se 1 (by rfl) ⟨684647, by rfl⟩ : syracuseStep 912863 = 1369295) B1369295
theorem B1371719 : Blo 912577 1371719 := bstep (se 1 (by rfl) ⟨1028789, by rfl⟩ : syracuseStep 1371719 = 2057579) B2057579
theorem B2059847 : Blo 912577 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B912999 : Blo 912577 912999 := bstep (se 1 (by rfl) ⟨684749, by rfl⟩ : syracuseStep 912999 = 1369499) B1369499
theorem B2059919 : Blo 912577 2059919 := bstep (se 1 (by rfl) ⟨1544939, by rfl⟩ : syracuseStep 2059919 = 3089879) B3089879
theorem B16084655 : Blo 912577 16084655 := bstep (se 1 (by rfl) ⟨12063491, by rfl⟩ : syracuseStep 16084655 = 24126983) B24126983
theorem B2060009 : Blo 912577 2060009 := bstep (se 2 (by rfl) ⟨772503, by rfl⟩ : syracuseStep 2060009 = 1545007) B1545007
theorem B913147 : Blo 912577 913147 := bstep (se 1 (by rfl) ⟨684860, by rfl⟩ : syracuseStep 913147 = 1369721) B1369721
theorem B1371899 : Blo 912577 1371899 := bstep (se 1 (by rfl) ⟨1028924, by rfl⟩ : syracuseStep 1371899 = 2057849) B2057849
theorem B2060027 : Blo 912577 2060027 := bstep (se 1 (by rfl) ⟨1545020, by rfl⟩ : syracuseStep 2060027 = 3090041) B3090041
theorem B31289125 : Blo 912577 31289125 := bstep (se 4 (by rfl) ⟨2933355, by rfl⟩ : syracuseStep 31289125 = 5866711) B5866711
theorem B913215 : Blo 912577 913215 := bstep (se 1 (by rfl) ⟨684911, by rfl⟩ : syracuseStep 913215 = 1369823) B1369823
theorem B978751 : Blo 912577 978751 := bstep (se 1 (by rfl) ⟨734063, by rfl⟩ : syracuseStep 978751 = 1468127) B1468127
theorem B913279 : Blo 912577 913279 := bstep (se 1 (by rfl) ⟨684959, by rfl⟩ : syracuseStep 913279 = 1369919) B1369919
theorem B913391 : Blo 912577 913391 := bstep (se 1 (by rfl) ⟨685043, by rfl⟩ : syracuseStep 913391 = 1370087) B1370087
theorem B913403 : Blo 912577 913403 := bstep (se 1 (by rfl) ⟨685052, by rfl⟩ : syracuseStep 913403 = 1370105) B1370105
theorem B913471 : Blo 912577 913471 := bstep (se 1 (by rfl) ⟨685103, by rfl⟩ : syracuseStep 913471 = 1370207) B1370207
theorem B1732681 : Blo 912577 1732681 := bstep (se 2 (by rfl) ⟨649755, by rfl⟩ : syracuseStep 1732681 = 1299511) B1299511
theorem B913511 : Blo 912577 913511 := bstep (se 1 (by rfl) ⟨685133, by rfl⟩ : syracuseStep 913511 = 1370267) B1370267
theorem B913535 : Blo 912577 913535 := bstep (se 1 (by rfl) ⟨685151, by rfl⟩ : syracuseStep 913535 = 1370303) B1370303
theorem B913563 : Blo 912577 913563 := bstep (se 1 (by rfl) ⟨685172, by rfl⟩ : syracuseStep 913563 = 1370345) B1370345
theorem B5861639 : Blo 912577 5861639 := bstep (se 1 (by rfl) ⟨4396229, by rfl⟩ : syracuseStep 5861639 = 8792459) B8792459
theorem B913767 : Blo 912577 913767 := bstep (se 1 (by rfl) ⟨685325, by rfl⟩ : syracuseStep 913767 = 1370651) B1370651
theorem B913819 : Blo 912577 913819 := bstep (se 1 (by rfl) ⟨685364, by rfl⟩ : syracuseStep 913819 = 1370729) B1370729
theorem B1372571 : Blo 912577 1372571 := bstep (se 1 (by rfl) ⟨1029428, by rfl⟩ : syracuseStep 1372571 = 2058857) B2058857
theorem B2061035 : Blo 912577 2061035 := bstep (se 1 (by rfl) ⟨1545776, by rfl⟩ : syracuseStep 2061035 = 3091553) B3091553
theorem B914171 : Blo 912577 914171 := bstep (se 1 (by rfl) ⟨685628, by rfl⟩ : syracuseStep 914171 = 1371257) B1371257
theorem B914239 : Blo 912577 914239 := bstep (se 1 (by rfl) ⟨685679, by rfl⟩ : syracuseStep 914239 = 1371359) B1371359
theorem B1372991 : Blo 912577 1372991 := bstep (se 1 (by rfl) ⟨1029743, by rfl⟩ : syracuseStep 1372991 = 2059487) B2059487
theorem B914267 : Blo 912577 914267 := bstep (se 1 (by rfl) ⟨685700, by rfl⟩ : syracuseStep 914267 = 1371401) B1371401
theorem B914335 : Blo 912577 914335 := bstep (se 1 (by rfl) ⟨685751, by rfl⟩ : syracuseStep 914335 = 1371503) B1371503
theorem B7402427 : Blo 912577 7402427 := bstep (se 1 (by rfl) ⟨5551820, by rfl⟩ : syracuseStep 7402427 = 11103641) B11103641
theorem B1373135 : Blo 912577 1373135 := bstep (se 1 (by rfl) ⟨1029851, by rfl⟩ : syracuseStep 1373135 = 2059703) B2059703
theorem B914415 : Blo 912577 914415 := bstep (se 1 (by rfl) ⟨685811, by rfl⟩ : syracuseStep 914415 = 1371623) B1371623
theorem B1373177 : Blo 912577 1373177 := bstep (se 2 (by rfl) ⟨514941, by rfl⟩ : syracuseStep 1373177 = 1029883) B1029883
theorem B2061305 : Blo 912577 2061305 := bstep (se 2 (by rfl) ⟨772989, by rfl⟩ : syracuseStep 2061305 = 1545979) B1545979
theorem B1373225 : Blo 912577 1373225 := bstep (se 2 (by rfl) ⟨514959, by rfl⟩ : syracuseStep 1373225 = 1029919) B1029919
theorem B914503 : Blo 912577 914503 := bstep (se 1 (by rfl) ⟨685877, by rfl⟩ : syracuseStep 914503 = 1371755) B1371755
theorem B1373255 : Blo 912577 1373255 := bstep (se 1 (by rfl) ⟨1029941, by rfl⟩ : syracuseStep 1373255 = 2059883) B2059883
theorem B2061395 : Blo 912577 2061395 := bstep (se 1 (by rfl) ⟨1546046, by rfl⟩ : syracuseStep 2061395 = 3092093) B3092093
theorem B1733737 : Blo 912577 1733737 := bstep (se 2 (by rfl) ⟨650151, by rfl⟩ : syracuseStep 1733737 = 1300303) B1300303
theorem B914587 : Blo 912577 914587 := bstep (se 1 (by rfl) ⟨685940, by rfl⟩ : syracuseStep 914587 = 1371881) B1371881
theorem B914683 : Blo 912577 914683 := bstep (se 1 (by rfl) ⟨686012, by rfl⟩ : syracuseStep 914683 = 1372025) B1372025
theorem B1373435 : Blo 912577 1373435 := bstep (se 1 (by rfl) ⟨1030076, by rfl⟩ : syracuseStep 1373435 = 2060153) B2060153
theorem B2061575 : Blo 912577 2061575 := bstep (se 1 (by rfl) ⟨1546181, by rfl⟩ : syracuseStep 2061575 = 3092363) B3092363
theorem B914751 : Blo 912577 914751 := bstep (se 1 (by rfl) ⟨686063, by rfl⟩ : syracuseStep 914751 = 1372127) B1372127
theorem B914919 : Blo 912577 914919 := bstep (se 1 (by rfl) ⟨686189, by rfl⟩ : syracuseStep 914919 = 1372379) B1372379
theorem B914927 : Blo 912577 914927 := bstep (se 1 (by rfl) ⟨686195, by rfl⟩ : syracuseStep 914927 = 1372391) B1372391
theorem B915035 : Blo 912577 915035 := bstep (se 1 (by rfl) ⟨686276, by rfl⟩ : syracuseStep 915035 = 1372553) B1372553
theorem B2061935 : Blo 912577 2061935 := bstep (se 1 (by rfl) ⟨1546451, by rfl⟩ : syracuseStep 2061935 = 3092903) B3092903
theorem B915099 : Blo 912577 915099 := bstep (se 1 (by rfl) ⟨686324, by rfl⟩ : syracuseStep 915099 = 1372649) B1372649
theorem B1734367 : Blo 912577 1734367 := bstep (se 1 (by rfl) ⟨1300775, by rfl⟩ : syracuseStep 1734367 = 2601551) B2601551
theorem B915183 : Blo 912577 915183 := bstep (se 1 (by rfl) ⟨686387, by rfl⟩ : syracuseStep 915183 = 1372775) B1372775
theorem B915271 : Blo 912577 915271 := bstep (se 1 (by rfl) ⟨686453, by rfl⟩ : syracuseStep 915271 = 1372907) B1372907
theorem B915291 : Blo 912577 915291 := bstep (se 1 (by rfl) ⟨686468, by rfl⟩ : syracuseStep 915291 = 1372937) B1372937
theorem B915359 : Blo 912577 915359 := bstep (se 1 (by rfl) ⟨686519, by rfl⟩ : syracuseStep 915359 = 1373039) B1373039
theorem B915527 : Blo 912577 915527 := bstep (se 1 (by rfl) ⟨686645, by rfl⟩ : syracuseStep 915527 = 1373291) B1373291
theorem B7403723 : Blo 912577 7403723 := bstep (se 1 (by rfl) ⟨5552792, by rfl⟩ : syracuseStep 7403723 = 11105585) B11105585
theorem B915687 : Blo 912577 915687 := bstep (se 1 (by rfl) ⟨686765, by rfl⟩ : syracuseStep 915687 = 1373531) B1373531
theorem B1734959 : Blo 912577 1734959 := bstep (se 1 (by rfl) ⟨1301219, by rfl⟩ : syracuseStep 1734959 = 2602439) B2602439
theorem B915871 : Blo 912577 915871 := bstep (se 1 (by rfl) ⟨686903, by rfl⟩ : syracuseStep 915871 = 1373807) B1373807
theorem B1735111 : Blo 912577 1735111 := bstep (se 1 (by rfl) ⟨1301333, by rfl⟩ : syracuseStep 1735111 = 2602667) B2602667
theorem B915919 : Blo 912577 915919 := bstep (se 1 (by rfl) ⟨686939, by rfl⟩ : syracuseStep 915919 = 1373879) B1373879
theorem B1374671 : Blo 912577 1374671 := bstep (se 1 (by rfl) ⟨1031003, by rfl⟩ : syracuseStep 1374671 = 2062007) B2062007
theorem B915943 : Blo 912577 915943 := bstep (se 1 (by rfl) ⟨686957, by rfl⟩ : syracuseStep 915943 = 1373915) B1373915
theorem B1374761 : Blo 912577 1374761 := bstep (se 2 (by rfl) ⟨515535, by rfl⟩ : syracuseStep 1374761 = 1031071) B1031071
theorem B916059 : Blo 912577 916059 := bstep (se 1 (by rfl) ⟨687044, by rfl⟩ : syracuseStep 916059 = 1374089) B1374089
theorem B916127 : Blo 912577 916127 := bstep (se 1 (by rfl) ⟨687095, by rfl⟩ : syracuseStep 916127 = 1374191) B1374191
theorem B916295 : Blo 912577 916295 := bstep (se 1 (by rfl) ⟨687221, by rfl⟩ : syracuseStep 916295 = 1374443) B1374443
theorem B916335 : Blo 912577 916335 := bstep (se 1 (by rfl) ⟨687251, by rfl⟩ : syracuseStep 916335 = 1374503) B1374503
theorem B916391 : Blo 912577 916391 := bstep (se 1 (by rfl) ⟨687293, by rfl⟩ : syracuseStep 916391 = 1374587) B1374587
theorem B3898313 : Blo 912577 3898313 := bstep (se 2 (by rfl) ⟨1461867, by rfl⟩ : syracuseStep 3898313 = 2923735) B2923735
theorem B916571 : Blo 912577 916571 := bstep (se 1 (by rfl) ⟨687428, by rfl⟩ : syracuseStep 916571 = 1374857) B1374857
theorem B5209595 : Blo 912577 5209595 := bstep (se 1 (by rfl) ⟨3907196, by rfl⟩ : syracuseStep 5209595 = 7814393) B7814393
theorem B1736569 : Blo 912577 1736569 := bstep (se 2 (by rfl) ⟨651213, by rfl⟩ : syracuseStep 1736569 = 1302427) B1302427
theorem B120094595 : Blo 912577 120094595 := bstep (se 1 (by rfl) ⟨90070946, by rfl⟩ : syracuseStep 120094595 = 180141893) B180141893
theorem B1736615 : Blo 912577 1736615 := bstep (se 1 (by rfl) ⟨1302461, by rfl⟩ : syracuseStep 1736615 = 2604923) B2604923
theorem B1540039 : Blo 912577 1540039 := bstep (se 1 (by rfl) ⟨1155029, by rfl⟩ : syracuseStep 1540039 = 2310059) B2310059
theorem B3473351 : Blo 912577 3473351 := bstep (se 1 (by rfl) ⟨2605013, by rfl⟩ : syracuseStep 3473351 = 5210027) B5210027
theorem B3899627 : Blo 912577 3899627 := bstep (se 1 (by rfl) ⟨2924720, by rfl⟩ : syracuseStep 3899627 = 5849441) B5849441
theorem B2195731 : Blo 912577 2195731 := bstep (se 1 (by rfl) ⟨1646798, by rfl⟩ : syracuseStep 2195731 = 3293597) B3293597
theorem B2818567 : Blo 912577 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B1540775 : Blo 912577 1540775 := bstep (se 1 (by rfl) ⟨1155581, by rfl⟩ : syracuseStep 1540775 = 2311163) B2311163
theorem B3965647 : Blo 912577 3965647 := bstep (se 1 (by rfl) ⟨2974235, by rfl⟩ : syracuseStep 3965647 = 5948471) B5948471
theorem B4621211 : Blo 912577 4621211 := bstep (se 1 (by rfl) ⟨3465908, by rfl⟩ : syracuseStep 4621211 = 6931817) B6931817
theorem B5211053 : Blo 912577 5211053 := bstep (se 3 (by rfl) ⟨977072, by rfl⟩ : syracuseStep 5211053 = 1954145) B1954145
theorem B6947855 : Blo 912577 6947855 := bstep (se 1 (by rfl) ⟨5210891, by rfl⟩ : syracuseStep 6947855 = 10421783) B10421783
theorem B1737769 : Blo 912577 1737769 := bstep (se 2 (by rfl) ⟨651663, by rfl⟩ : syracuseStep 1737769 = 1303327) B1303327
theorem B4457809 : Blo 912577 4457809 := bstep (se 2 (by rfl) ⟨1671678, by rfl⟩ : syracuseStep 4457809 = 3343357) B3343357
theorem B8783387 : Blo 912577 8783387 := bstep (se 1 (by rfl) ⟨6587540, by rfl⟩ : syracuseStep 8783387 = 13175081) B13175081
theorem B3475007 : Blo 912577 3475007 := bstep (se 1 (by rfl) ⟨2606255, by rfl⟩ : syracuseStep 3475007 = 5212511) B5212511
theorem B3475325 : Blo 912577 3475325 := bstep (se 3 (by rfl) ⟨651623, by rfl⟩ : syracuseStep 3475325 = 1303247) B1303247
theorem B3083129 : Blo 912577 3083129 := bstep (se 2 (by rfl) ⟨1156173, by rfl⟩ : syracuseStep 3083129 = 2312347) B2312347
theorem B8784769 : Blo 912577 8784769 := bstep (se 2 (by rfl) ⟨3294288, by rfl⟩ : syracuseStep 8784769 = 6588577) B6588577
theorem B1543259 : Blo 912577 1543259 := bstep (se 1 (by rfl) ⟨1157444, by rfl⟩ : syracuseStep 1543259 = 2314889) B2314889
theorem B11701907 : Blo 912577 11701907 := bstep (se 1 (by rfl) ⟨8776430, by rfl⟩ : syracuseStep 11701907 = 17552861) B17552861
theorem B8785847 : Blo 912577 8785847 := bstep (se 1 (by rfl) ⟨6589385, by rfl⟩ : syracuseStep 8785847 = 13178771) B13178771
theorem B21074377 : Blo 912577 21074377 := bstep (se 2 (by rfl) ⟨7902891, by rfl⟩ : syracuseStep 21074377 = 15805783) B15805783
theorem B49975957 : Blo 912577 49975957 := bstep (se 6 (by rfl) ⟨1171311, by rfl⟩ : syracuseStep 49975957 = 2342623) B2342623
theorem B13177565 : Blo 912577 13177565 := bstep (se 3 (by rfl) ⟨2470793, by rfl⟩ : syracuseStep 13177565 = 4941587) B4941587
theorem B4690667 : Blo 912577 4690667 := bstep (se 1 (by rfl) ⟨3518000, by rfl⟩ : syracuseStep 4690667 = 7036001) B7036001
theorem B41718833 : Blo 912577 41718833 := bstep (se 2 (by rfl) ⟨15644562, by rfl⟩ : syracuseStep 41718833 = 31289125) B31289125
theorem B3478697 : Blo 912577 3478697 := bstep (se 2 (by rfl) ⟨1304511, by rfl⟩ : syracuseStep 3478697 = 2609023) B2609023
theorem B7410923 : Blo 912577 7410923 := bstep (se 1 (by rfl) ⟨5558192, by rfl⟩ : syracuseStep 7410923 = 11116385) B11116385
theorem B25400807 : Blo 912577 25400807 := bstep (se 1 (by rfl) ⟨19050605, by rfl⟩ : syracuseStep 25400807 = 38101211) B38101211
theorem B21108737 : Blo 912577 21108737 := bstep (se 2 (by rfl) ⟨7915776, by rfl⟩ : syracuseStep 21108737 = 15831553) B15831553
theorem B37623845 : Blo 912577 37623845 := bstep (se 4 (by rfl) ⟨3527235, by rfl⟩ : syracuseStep 37623845 = 7054471) B7054471
theorem B4626557 : Blo 912577 4626557 := bstep (se 3 (by rfl) ⟨867479, by rfl⟩ : syracuseStep 4626557 = 1734959) B1734959
theorem B3479699 : Blo 912577 3479699 := bstep (se 1 (by rfl) ⟨2609774, by rfl⟩ : syracuseStep 3479699 = 5219549) B5219549
theorem B4626719 : Blo 912577 4626719 := bstep (se 1 (by rfl) ⟨3470039, by rfl⟩ : syracuseStep 4626719 = 6940079) B6940079
theorem B3086639 : Blo 912577 3086639 := bstep (se 1 (by rfl) ⟨2314979, by rfl⟩ : syracuseStep 3086639 = 4629959) B4629959
theorem B3906119 : Blo 912577 3906119 := bstep (se 1 (by rfl) ⟨2929589, by rfl⟩ : syracuseStep 3906119 = 5859179) B5859179
theorem B3086963 : Blo 912577 3086963 := bstep (se 1 (by rfl) ⟨2315222, by rfl⟩ : syracuseStep 3086963 = 4630445) B4630445
theorem B3087503 : Blo 912577 3087503 := bstep (se 1 (by rfl) ⟨2315627, by rfl⟩ : syracuseStep 3087503 = 4631255) B4631255
theorem B6266105 : Blo 912577 6266105 := bstep (se 2 (by rfl) ⟨2349789, by rfl⟩ : syracuseStep 6266105 = 4699579) B4699579
theorem B3088043 : Blo 912577 3088043 := bstep (se 1 (by rfl) ⟨2316032, by rfl⟩ : syracuseStep 3088043 = 4632065) B4632065
theorem B10723103 : Blo 912577 10723103 := bstep (se 1 (by rfl) ⟨8042327, by rfl⟩ : syracuseStep 10723103 = 16084655) B16084655
theorem B33792005 : Blo 912577 33792005 := bstep (se 4 (by rfl) ⟨3168000, by rfl⟩ : syracuseStep 33792005 = 6336001) B6336001
theorem B3907759 : Blo 912577 3907759 := bstep (se 1 (by rfl) ⟨2930819, by rfl⟩ : syracuseStep 3907759 = 5861639) B5861639
theorem B3088583 : Blo 912577 3088583 := bstep (se 1 (by rfl) ⟨2316437, by rfl⟩ : syracuseStep 3088583 = 4632875) B4632875
theorem B22553261 : Blo 912577 22553261 := bstep (se 3 (by rfl) ⟨4228736, by rfl⟩ : syracuseStep 22553261 = 8457473) B8457473
theorem B4400381 : Blo 912577 4400381 := bstep (se 3 (by rfl) ⟨825071, by rfl⟩ : syracuseStep 4400381 = 1650143) B1650143
theorem B6956603 : Blo 912577 6956603 := bstep (se 1 (by rfl) ⟨5217452, by rfl⟩ : syracuseStep 6956603 = 10434905) B10434905
theorem B3090095 : Blo 912577 3090095 := bstep (se 1 (by rfl) ⟨2317571, by rfl⟩ : syracuseStep 3090095 = 4635143) B4635143
theorem B2598875 : Blo 912577 2598875 := bstep (se 1 (by rfl) ⟨1949156, by rfl⟩ : syracuseStep 2598875 = 3898313) B3898313
theorem B3090419 : Blo 912577 3090419 := bstep (se 1 (by rfl) ⟨2317814, by rfl⟩ : syracuseStep 3090419 = 4635629) B4635629
theorem B4401535 : Blo 912577 4401535 := bstep (se 1 (by rfl) ⟨3301151, by rfl⟩ : syracuseStep 4401535 = 6602303) B6602303
theorem B3090959 : Blo 912577 3090959 := bstep (se 1 (by rfl) ⟨2318219, by rfl⟩ : syracuseStep 3090959 = 4636439) B4636439
theorem B80063063 : Blo 912577 80063063 := bstep (se 1 (by rfl) ⟨60047297, by rfl⟩ : syracuseStep 80063063 = 120094595) B120094595
theorem B1157743 : Blo 912577 1157743 := bstep (se 1 (by rfl) ⟨868307, by rfl⟩ : syracuseStep 1157743 = 1736615) B1736615
theorem B12528539 : Blo 912577 12528539 := bstep (se 1 (by rfl) ⟨9396404, by rfl⟩ : syracuseStep 12528539 = 18792809) B18792809
theorem B11119781 : Blo 912577 11119781 := bstep (se 4 (by rfl) ⟨1042479, by rfl⟩ : syracuseStep 11119781 = 2084959) B2084959
theorem B2600275 : Blo 912577 2600275 := bstep (se 1 (by rfl) ⟨1950206, by rfl⟩ : syracuseStep 2600275 = 3900413) B3900413
theorem B1027615 : Blo 912577 1027615 := bstep (se 1 (by rfl) ⟨770711, by rfl⟩ : syracuseStep 1027615 = 1541423) B1541423
theorem B3092039 : Blo 912577 3092039 := bstep (se 1 (by rfl) ⟨2319029, by rfl⟩ : syracuseStep 3092039 = 4638059) B4638059
theorem B1158943 : Blo 912577 1158943 := bstep (se 1 (by rfl) ⟨869207, by rfl⟩ : syracuseStep 1158943 = 1738415) B1738415
theorem B12693307 : Blo 912577 12693307 := bstep (se 1 (by rfl) ⟨9519980, by rfl⟩ : syracuseStep 12693307 = 19039961) B19039961
theorem B4174375 : Blo 912577 4174375 := bstep (se 1 (by rfl) ⟨3130781, by rfl⟩ : syracuseStep 4174375 = 6261563) B6261563
theorem B4174589 : Blo 912577 4174589 := bstep (se 3 (by rfl) ⟨782735, by rfl⟩ : syracuseStep 4174589 = 1565471) B1565471
theorem B23475257 : Blo 912577 23475257 := bstep (se 2 (by rfl) ⟨8803221, by rfl⟩ : syracuseStep 23475257 = 17606443) B17606443
theorem B21116123 : Blo 912577 21116123 := bstep (se 1 (by rfl) ⟨15837092, by rfl⟩ : syracuseStep 21116123 = 31674185) B31674185
theorem B2602621 : Blo 912577 2602621 := bstep (se 3 (by rfl) ⟨487991, by rfl⟩ : syracuseStep 2602621 = 975983) B975983
theorem B37500731 : Blo 912577 37500731 := bstep (se 1 (by rfl) ⟨28125548, by rfl⟩ : syracuseStep 37500731 = 56251097) B56251097
theorem B30128111 : Blo 912577 30128111 := bstep (se 1 (by rfl) ⟨22596083, by rfl⟩ : syracuseStep 30128111 = 45192167) B45192167
theorem B1390655 : Blo 912577 1390655 := bstep (se 1 (by rfl) ⟨1042991, by rfl⟩ : syracuseStep 1390655 = 2085983) B2085983
theorem B1030207 : Blo 912577 1030207 := bstep (se 1 (by rfl) ⟨772655, by rfl⟩ : syracuseStep 1030207 = 1545311) B1545311
theorem B2472059 : Blo 912577 2472059 := bstep (se 1 (by rfl) ⟨1854044, by rfl⟩ : syracuseStep 2472059 = 3708089) B3708089
theorem B2603191 : Blo 912577 2603191 := bstep (se 1 (by rfl) ⟨1952393, by rfl⟩ : syracuseStep 2603191 = 3904787) B3904787
theorem B2930975 : Blo 912577 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B9878543 : Blo 912577 9878543 := bstep (se 1 (by rfl) ⟨7408907, by rfl⟩ : syracuseStep 9878543 = 14817815) B14817815
theorem B1949779 : Blo 912577 1949779 := bstep (se 1 (by rfl) ⟨1462334, by rfl⟩ : syracuseStep 1949779 = 2924669) B2924669
theorem B2310241 : Blo 912577 2310241 := bstep (se 2 (by rfl) ⟨866340, by rfl⟩ : syracuseStep 2310241 = 1732681) B1732681
theorem B4636925 : Blo 912577 4636925 := bstep (se 3 (by rfl) ⟨869423, by rfl⟩ : syracuseStep 4636925 = 1738847) B1738847
theorem B88883507 : Blo 912577 88883507 := bstep (se 1 (by rfl) ⟨66662630, by rfl⟩ : syracuseStep 88883507 = 133325261) B133325261
theorem B8700317 : Blo 912577 8700317 := bstep (se 3 (by rfl) ⟨1631309, by rfl⟩ : syracuseStep 8700317 = 3262619) B3262619
theorem B3916907 : Blo 912577 3916907 := bstep (se 1 (by rfl) ⟨2937680, by rfl⟩ : syracuseStep 3916907 = 5875361) B5875361
theorem B10437821 : Blo 912577 10437821 := bstep (se 3 (by rfl) ⟨1957091, by rfl⟩ : syracuseStep 10437821 = 3914183) B3914183
theorem B2311649 : Blo 912577 2311649 := bstep (se 2 (by rfl) ⟨866868, by rfl⟩ : syracuseStep 2311649 = 1733737) B1733737
theorem B2934767 : Blo 912577 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B2312489 : Blo 912577 2312489 := bstep (se 2 (by rfl) ⟨867183, by rfl⟩ : syracuseStep 2312489 = 1734367) B1734367
theorem B2607839 : Blo 912577 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B2640809 : Blo 912577 2640809 := bstep (se 2 (by rfl) ⟨990303, by rfl⟩ : syracuseStep 2640809 = 1980607) B1980607
theorem B4639841 : Blo 912577 4639841 := bstep (se 2 (by rfl) ⟨1739940, by rfl⟩ : syracuseStep 4639841 = 3479881) B3479881
theorem B2313481 : Blo 912577 2313481 := bstep (se 2 (by rfl) ⟨867555, by rfl⟩ : syracuseStep 2313481 = 1735111) B1735111
theorem B4934951 : Blo 912577 4934951 := bstep (se 1 (by rfl) ⟨3701213, by rfl⟩ : syracuseStep 4934951 = 7402427) B7402427
theorem B4935205 : Blo 912577 4935205 := bstep (se 4 (by rfl) ⟨462675, by rfl⟩ : syracuseStep 4935205 = 925351) B925351
theorem B4935815 : Blo 912577 4935815 := bstep (se 1 (by rfl) ⟨3701861, by rfl⟩ : syracuseStep 4935815 = 7403723) B7403723
theorem B2315425 : Blo 912577 2315425 := bstep (se 2 (by rfl) ⟨868284, by rfl⟩ : syracuseStep 2315425 = 1736569) B1736569
theorem B2053385 : Blo 912577 2053385 := bstep (se 2 (by rfl) ⟨770019, by rfl⟩ : syracuseStep 2053385 = 1540039) B1540039
theorem B2315567 : Blo 912577 2315567 := bstep (se 1 (by rfl) ⟨1736675, by rfl⟩ : syracuseStep 2315567 = 3473351) B3473351
theorem B1464103 : Blo 912577 1464103 := bstep (se 1 (by rfl) ⟨1098077, by rfl⟩ : syracuseStep 1464103 = 2196155) B2196155
theorem B1955623 : Blo 912577 1955623 := bstep (se 1 (by rfl) ⟨1466717, by rfl⟩ : syracuseStep 1955623 = 2933435) B2933435
theorem B2054375 : Blo 912577 2054375 := bstep (se 1 (by rfl) ⟨1540781, by rfl⟩ : syracuseStep 2054375 = 3081563) B3081563
theorem B2054393 : Blo 912577 2054393 := bstep (se 2 (by rfl) ⟨770397, by rfl⟩ : syracuseStep 2054393 = 1540795) B1540795
theorem B2054555 : Blo 912577 2054555 := bstep (se 1 (by rfl) ⟨1540916, by rfl⟩ : syracuseStep 2054555 = 3081833) B3081833
theorem B2054663 : Blo 912577 2054663 := bstep (se 1 (by rfl) ⟨1540997, by rfl⟩ : syracuseStep 2054663 = 3081995) B3081995
theorem B8772239 : Blo 912577 8772239 := bstep (se 1 (by rfl) ⟨6579179, by rfl⟩ : syracuseStep 8772239 = 13158359) B13158359
theorem B2054843 : Blo 912577 2054843 := bstep (se 1 (by rfl) ⟨1541132, by rfl⟩ : syracuseStep 2054843 = 3082265) B3082265
theorem B2054951 : Blo 912577 2054951 := bstep (se 1 (by rfl) ⟨1541213, by rfl⟩ : syracuseStep 2054951 = 3082427) B3082427
theorem B7428989 : Blo 912577 7428989 := bstep (se 3 (by rfl) ⟨1392935, by rfl⟩ : syracuseStep 7428989 = 2785871) B2785871
theorem B1956955 : Blo 912577 1956955 := bstep (se 1 (by rfl) ⟨1467716, by rfl⟩ : syracuseStep 1956955 = 2935433) B2935433
theorem B5201279 : Blo 912577 5201279 := bstep (se 1 (by rfl) ⟨3900959, by rfl⟩ : syracuseStep 5201279 = 7801919) B7801919
theorem B2776639 : Blo 912577 2776639 := bstep (se 1 (by rfl) ⟨2082479, by rfl⟩ : syracuseStep 2776639 = 4164959) B4164959
theorem B2055743 : Blo 912577 2055743 := bstep (se 1 (by rfl) ⟨1541807, by rfl⟩ : syracuseStep 2055743 = 3083615) B3083615
theorem B2056103 : Blo 912577 2056103 := bstep (se 1 (by rfl) ⟨1542077, by rfl⟩ : syracuseStep 2056103 = 3084155) B3084155
theorem B1466281 : Blo 912577 1466281 := bstep (se 2 (by rfl) ⟨549855, by rfl⟩ : syracuseStep 1466281 = 1099711) B1099711
theorem B2777759 : Blo 912577 2777759 := bstep (se 1 (by rfl) ⟨2083319, by rfl⟩ : syracuseStep 2777759 = 4166639) B4166639
theorem B4219715 : Blo 912577 4219715 := bstep (se 1 (by rfl) ⟨3164786, by rfl⟩ : syracuseStep 4219715 = 6329573) B6329573
theorem B2319263 : Blo 912577 2319263 := bstep (se 1 (by rfl) ⟨1739447, by rfl⟩ : syracuseStep 2319263 = 3478895) B3478895
theorem B1369199 : Blo 912577 1369199 := bstep (se 1 (by rfl) ⟨1026899, by rfl⟩ : syracuseStep 1369199 = 2053799) B2053799
theorem B1369319 : Blo 912577 1369319 := bstep (se 1 (by rfl) ⟨1026989, by rfl⟩ : syracuseStep 1369319 = 2053979) B2053979
theorem B5858563 : Blo 912577 5858563 := bstep (se 1 (by rfl) ⟨4393922, by rfl⟩ : syracuseStep 5858563 = 8787845) B8787845
theorem B1369385 : Blo 912577 1369385 := bstep (se 2 (by rfl) ⟨513519, by rfl⟩ : syracuseStep 1369385 = 1027039) B1027039
theorem B1304039 : Blo 912577 1304039 := bstep (se 1 (by rfl) ⟨978029, by rfl⟩ : syracuseStep 1304039 = 1956059) B1956059
theorem B1369655 : Blo 912577 1369655 := bstep (se 1 (by rfl) ⟨1027241, by rfl⟩ : syracuseStep 1369655 = 2054483) B2054483
theorem B5859155 : Blo 912577 5859155 := bstep (se 1 (by rfl) ⟨4394366, by rfl⟩ : syracuseStep 5859155 = 8788733) B8788733
theorem B1369979 : Blo 912577 1369979 := bstep (se 1 (by rfl) ⟨1027484, by rfl⟩ : syracuseStep 1369979 = 2054969) B2054969
theorem B1370015 : Blo 912577 1370015 := bstep (se 1 (by rfl) ⟨1027511, by rfl⟩ : syracuseStep 1370015 = 2055023) B2055023
theorem B1370249 : Blo 912577 1370249 := bstep (se 2 (by rfl) ⟨513843, by rfl⟩ : syracuseStep 1370249 = 1027687) B1027687
theorem B1370399 : Blo 912577 1370399 := bstep (se 1 (by rfl) ⟨1027799, by rfl⟩ : syracuseStep 1370399 = 2055599) B2055599
theorem B1370447 : Blo 912577 1370447 := bstep (se 1 (by rfl) ⟨1027835, by rfl⟩ : syracuseStep 1370447 = 2055671) B2055671
theorem B1370537 : Blo 912577 1370537 := bstep (se 2 (by rfl) ⟨513951, by rfl⟩ : syracuseStep 1370537 = 1027903) B1027903
theorem B1305001 : Blo 912577 1305001 := bstep (se 2 (by rfl) ⟨489375, by rfl⟩ : syracuseStep 1305001 = 978751) B978751
theorem B1370921 : Blo 912577 1370921 := bstep (se 2 (by rfl) ⟨514095, by rfl⟩ : syracuseStep 1370921 = 1028191) B1028191
theorem B1371131 : Blo 912577 1371131 := bstep (se 1 (by rfl) ⟨1028348, by rfl⟩ : syracuseStep 1371131 = 2056697) B2056697
theorem B1371191 : Blo 912577 1371191 := bstep (se 1 (by rfl) ⟨1028393, by rfl⟩ : syracuseStep 1371191 = 2056787) B2056787
theorem B1371311 : Blo 912577 1371311 := bstep (se 1 (by rfl) ⟨1028483, by rfl⟩ : syracuseStep 1371311 = 2056967) B2056967
theorem B2780335 : Blo 912577 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B912591 : Blo 912577 912591 := bstep (se 1 (by rfl) ⟨684443, by rfl⟩ : syracuseStep 912591 = 1368887) B1368887
theorem B1371371 : Blo 912577 1371371 := bstep (se 1 (by rfl) ⟨1028528, by rfl⟩ : syracuseStep 1371371 = 2057057) B2057057
theorem B912711 : Blo 912577 912711 := bstep (se 1 (by rfl) ⟨684533, by rfl⟩ : syracuseStep 912711 = 1369067) B1369067
theorem B978247 : Blo 912577 978247 := bstep (se 1 (by rfl) ⟨733685, by rfl⟩ : syracuseStep 978247 = 1467371) B1467371
theorem B8351513 : Blo 912577 8351513 := bstep (se 2 (by rfl) ⟨3131817, by rfl⟩ : syracuseStep 8351513 = 6263635) B6263635
theorem B1372031 : Blo 912577 1372031 := bstep (se 1 (by rfl) ⟨1029023, by rfl⟩ : syracuseStep 1372031 = 2058047) B2058047
theorem B913439 : Blo 912577 913439 := bstep (se 1 (by rfl) ⟨685079, by rfl⟩ : syracuseStep 913439 = 1370159) B1370159
theorem B913615 : Blo 912577 913615 := bstep (se 1 (by rfl) ⟨685211, by rfl⟩ : syracuseStep 913615 = 1370423) B1370423
theorem B1372367 : Blo 912577 1372367 := bstep (se 1 (by rfl) ⟨1029275, by rfl⟩ : syracuseStep 1372367 = 2058551) B2058551
theorem B2060495 : Blo 912577 2060495 := bstep (se 1 (by rfl) ⟨1545371, by rfl⟩ : syracuseStep 2060495 = 3090743) B3090743
theorem B913735 : Blo 912577 913735 := bstep (se 1 (by rfl) ⟨685301, by rfl⟩ : syracuseStep 913735 = 1370603) B1370603
theorem B1372487 : Blo 912577 1372487 := bstep (se 1 (by rfl) ⟨1029365, by rfl⟩ : syracuseStep 1372487 = 2058731) B2058731
theorem B56324443 : Blo 912577 56324443 := bstep (se 1 (by rfl) ⟨42243332, by rfl⟩ : syracuseStep 56324443 = 84486665) B84486665
theorem B914203 : Blo 912577 914203 := bstep (se 1 (by rfl) ⟨685652, by rfl⟩ : syracuseStep 914203 = 1371305) B1371305
theorem B1372955 : Blo 912577 1372955 := bstep (se 1 (by rfl) ⟨1029716, by rfl⟩ : syracuseStep 1372955 = 2059433) B2059433
theorem B914479 : Blo 912577 914479 := bstep (se 1 (by rfl) ⟨685859, by rfl⟩ : syracuseStep 914479 = 1371719) B1371719
theorem B1373231 : Blo 912577 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B5207111 : Blo 912577 5207111 := bstep (se 1 (by rfl) ⟨3905333, by rfl⟩ : syracuseStep 5207111 = 7810667) B7810667
theorem B1373279 : Blo 912577 1373279 := bstep (se 1 (by rfl) ⟨1029959, by rfl⟩ : syracuseStep 1373279 = 2059919) B2059919
theorem B1373339 : Blo 912577 1373339 := bstep (se 1 (by rfl) ⟨1030004, by rfl⟩ : syracuseStep 1373339 = 2060009) B2060009
theorem B2061467 : Blo 912577 2061467 := bstep (se 1 (by rfl) ⟨1546100, by rfl⟩ : syracuseStep 2061467 = 3092201) B3092201
theorem B914599 : Blo 912577 914599 := bstep (se 1 (by rfl) ⟨685949, by rfl⟩ : syracuseStep 914599 = 1371899) B1371899
theorem B1373351 : Blo 912577 1373351 := bstep (se 1 (by rfl) ⟨1030013, by rfl⟩ : syracuseStep 1373351 = 2060027) B2060027
theorem B915047 : Blo 912577 915047 := bstep (se 1 (by rfl) ⟨686285, by rfl⟩ : syracuseStep 915047 = 1372571) B1372571
theorem B1374023 : Blo 912577 1374023 := bstep (se 1 (by rfl) ⟨1030517, by rfl⟩ : syracuseStep 1374023 = 2061035) B2061035
theorem B1734527 : Blo 912577 1734527 := bstep (se 1 (by rfl) ⟨1300895, by rfl⟩ : syracuseStep 1734527 = 2601791) B2601791
theorem B915327 : Blo 912577 915327 := bstep (se 1 (by rfl) ⟨686495, by rfl⟩ : syracuseStep 915327 = 1372991) B1372991
theorem B915423 : Blo 912577 915423 := bstep (se 1 (by rfl) ⟨686567, by rfl⟩ : syracuseStep 915423 = 1373135) B1373135
theorem B1734625 : Blo 912577 1734625 := bstep (se 2 (by rfl) ⟨650484, by rfl⟩ : syracuseStep 1734625 = 1300969) B1300969
theorem B915451 : Blo 912577 915451 := bstep (se 1 (by rfl) ⟨686588, by rfl⟩ : syracuseStep 915451 = 1373177) B1373177
theorem B1374203 : Blo 912577 1374203 := bstep (se 1 (by rfl) ⟨1030652, by rfl⟩ : syracuseStep 1374203 = 2061305) B2061305
theorem B915483 : Blo 912577 915483 := bstep (se 1 (by rfl) ⟨686612, by rfl⟩ : syracuseStep 915483 = 1373225) B1373225
theorem B915503 : Blo 912577 915503 := bstep (se 1 (by rfl) ⟨686627, by rfl⟩ : syracuseStep 915503 = 1373255) B1373255
theorem B1374263 : Blo 912577 1374263 := bstep (se 1 (by rfl) ⟨1030697, by rfl⟩ : syracuseStep 1374263 = 2061395) B2061395
theorem B1374329 : Blo 912577 1374329 := bstep (se 2 (by rfl) ⟨515373, by rfl⟩ : syracuseStep 1374329 = 1030747) B1030747
theorem B7796897 : Blo 912577 7796897 := bstep (se 2 (by rfl) ⟨2923836, by rfl⟩ : syracuseStep 7796897 = 5847673) B5847673
theorem B915623 : Blo 912577 915623 := bstep (se 1 (by rfl) ⟨686717, by rfl⟩ : syracuseStep 915623 = 1373435) B1373435
theorem B1374383 : Blo 912577 1374383 := bstep (se 1 (by rfl) ⟨1030787, by rfl⟩ : syracuseStep 1374383 = 2061575) B2061575
theorem B1374623 : Blo 912577 1374623 := bstep (se 1 (by rfl) ⟨1030967, by rfl⟩ : syracuseStep 1374623 = 2061935) B2061935
theorem B5208569 : Blo 912577 5208569 := bstep (se 2 (by rfl) ⟨1953213, by rfl⟩ : syracuseStep 5208569 = 3906427) B3906427
theorem B1374713 : Blo 912577 1374713 := bstep (se 2 (by rfl) ⟨515517, by rfl⟩ : syracuseStep 1374713 = 1031035) B1031035
theorem B1735195 : Blo 912577 1735195 := bstep (se 1 (by rfl) ⟨1301396, by rfl⟩ : syracuseStep 1735195 = 2602793) B2602793
theorem B5012231 : Blo 912577 5012231 := bstep (se 1 (by rfl) ⟨3759173, by rfl⟩ : syracuseStep 5012231 = 7518347) B7518347
theorem B916447 : Blo 912577 916447 := bstep (se 1 (by rfl) ⟨687335, by rfl⟩ : syracuseStep 916447 = 1374671) B1374671
theorem B916507 : Blo 912577 916507 := bstep (se 1 (by rfl) ⟨687380, by rfl⟩ : syracuseStep 916507 = 1374761) B1374761
theorem B3898601 : Blo 912577 3898601 := bstep (se 2 (by rfl) ⟨1461975, by rfl⟩ : syracuseStep 3898601 = 2923951) B2923951
theorem B3473063 : Blo 912577 3473063 := bstep (se 1 (by rfl) ⟨2604797, by rfl⟩ : syracuseStep 3473063 = 5209595) B5209595
theorem B3080321 : Blo 912577 3080321 := bstep (se 2 (by rfl) ⟨1155120, by rfl⟩ : syracuseStep 3080321 = 2310241) B2310241
theorem B5210345 : Blo 912577 5210345 := bstep (se 2 (by rfl) ⟨1953879, by rfl⟩ : syracuseStep 5210345 = 3907759) B3907759
theorem B5800211 : Blo 912577 5800211 := bstep (se 1 (by rfl) ⟨4350158, by rfl⟩ : syracuseStep 5800211 = 8700317) B8700317
theorem B3080807 : Blo 912577 3080807 := bstep (se 1 (by rfl) ⟨2310605, by rfl⟩ : syracuseStep 3080807 = 4621211) B4621211
theorem B3474035 : Blo 912577 3474035 := bstep (se 1 (by rfl) ⟨2605526, by rfl⟩ : syracuseStep 3474035 = 5211053) B5211053
theorem B1541099 : Blo 912577 1541099 := bstep (se 1 (by rfl) ⟨1155824, by rfl⟩ : syracuseStep 1541099 = 2311649) B2311649
theorem B1541659 : Blo 912577 1541659 := bstep (se 1 (by rfl) ⟨1156244, by rfl⟩ : syracuseStep 1541659 = 2312489) B2312489
theorem B1738559 : Blo 912577 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B7801271 : Blo 912577 7801271 := bstep (se 1 (by rfl) ⟨5850953, by rfl⟩ : syracuseStep 7801271 = 11701907) B11701907
theorem B8785043 : Blo 912577 8785043 := bstep (se 1 (by rfl) ⟨6588782, by rfl⟩ : syracuseStep 8785043 = 13177565) B13177565
theorem B5868713 : Blo 912577 5868713 := bstep (se 2 (by rfl) ⟨2200767, by rfl⟩ : syracuseStep 5868713 = 4401535) B4401535
theorem B1543657 : Blo 912577 1543657 := bstep (se 2 (by rfl) ⟨578871, by rfl⟩ : syracuseStep 1543657 = 1157743) B1157743
theorem B1543711 : Blo 912577 1543711 := bstep (se 1 (by rfl) ⟨1157783, by rfl⟩ : syracuseStep 1543711 = 2315567) B2315567
theorem B3477437 : Blo 912577 3477437 := bstep (se 3 (by rfl) ⟨652019, by rfl⟩ : syracuseStep 3477437 = 1304039) B1304039
theorem B3084371 : Blo 912577 3084371 := bstep (se 1 (by rfl) ⟨2313278, by rfl⟩ : syracuseStep 3084371 = 4626557) B4626557
theorem B3084479 : Blo 912577 3084479 := bstep (se 1 (by rfl) ⟨2313359, by rfl⟩ : syracuseStep 3084479 = 4626719) B4626719
theorem B3084641 : Blo 912577 3084641 := bstep (se 2 (by rfl) ⟨1156740, by rfl⟩ : syracuseStep 3084641 = 2313481) B2313481
theorem B4952659 : Blo 912577 4952659 := bstep (se 1 (by rfl) ⟨3714494, by rfl⟩ : syracuseStep 4952659 = 7428989) B7428989
theorem B1545257 : Blo 912577 1545257 := bstep (se 2 (by rfl) ⟨579471, by rfl⟩ : syracuseStep 1545257 = 1158943) B1158943
theorem B7148735 : Blo 912577 7148735 := bstep (se 1 (by rfl) ⟨5361551, by rfl⟩ : syracuseStep 7148735 = 10723103) B10723103
theorem B3708413 : Blo 912577 3708413 := bstep (se 3 (by rfl) ⟨695327, by rfl⟩ : syracuseStep 3708413 = 1390655) B1390655
theorem B1546175 : Blo 912577 1546175 := bstep (se 1 (by rfl) ⟨1159631, by rfl⟩ : syracuseStep 1546175 = 2319263) B2319263
theorem B3906103 : Blo 912577 3906103 := bstep (se 1 (by rfl) ⟨2929577, by rfl⟩ : syracuseStep 3906103 = 5859155) B5859155
theorem B3087233 : Blo 912577 3087233 := bstep (se 2 (by rfl) ⟨1157712, by rfl⟩ : syracuseStep 3087233 = 2315425) B2315425
theorem B5217317 : Blo 912577 5217317 := bstep (se 4 (by rfl) ⟨489123, by rfl⟩ : syracuseStep 5217317 = 978247) B978247
theorem B1156351 : Blo 912577 1156351 := bstep (se 1 (by rfl) ⟨867263, by rfl⟩ : syracuseStep 1156351 = 1734527) B1734527
theorem B1648039 : Blo 912577 1648039 := bstep (se 1 (by rfl) ⟨1236029, by rfl⟩ : syracuseStep 1648039 = 2472059) B2472059
theorem B2599067 : Blo 912577 2599067 := bstep (se 1 (by rfl) ⟨1949300, by rfl⟩ : syracuseStep 2599067 = 3898601) B3898601
theorem B2599705 : Blo 912577 2599705 := bstep (se 2 (by rfl) ⟨974889, by rfl⟩ : syracuseStep 2599705 = 1949779) B1949779
theorem B2599751 : Blo 912577 2599751 := bstep (se 1 (by rfl) ⟨1949813, by rfl⟩ : syracuseStep 2599751 = 3899627) B3899627
theorem B3091283 : Blo 912577 3091283 := bstep (se 1 (by rfl) ⟨2318462, by rfl⟩ : syracuseStep 3091283 = 4636925) B4636925
theorem B59255671 : Blo 912577 59255671 := bstep (se 1 (by rfl) ⟨44441753, by rfl⟩ : syracuseStep 59255671 = 88883507) B88883507
theorem B1027183 : Blo 912577 1027183 := bstep (se 1 (by rfl) ⟨770387, by rfl⟩ : syracuseStep 1027183 = 1540775) B1540775
theorem B4631903 : Blo 912577 4631903 := bstep (se 1 (by rfl) ⟨3473927, by rfl⟩ : syracuseStep 4631903 = 6947855) B6947855
theorem B6958547 : Blo 912577 6958547 := bstep (se 1 (by rfl) ⟨5218910, by rfl⟩ : syracuseStep 6958547 = 10437821) B10437821
theorem B5287529 : Blo 912577 5287529 := bstep (se 2 (by rfl) ⟨1982823, by rfl⟩ : syracuseStep 5287529 = 3965647) B3965647
theorem B11710565 : Blo 912577 11710565 := bstep (se 4 (by rfl) ⟨1097865, by rfl⟩ : syracuseStep 11710565 = 2195731) B2195731
theorem B7811417 : Blo 912577 7811417 := bstep (se 2 (by rfl) ⟨2929281, by rfl⟩ : syracuseStep 7811417 = 5858563) B5858563
theorem B5943745 : Blo 912577 5943745 := bstep (se 2 (by rfl) ⟨2228904, by rfl⟩ : syracuseStep 5943745 = 4457809) B4457809
theorem B1028839 : Blo 912577 1028839 := bstep (se 1 (by rfl) ⟨771629, by rfl⟩ : syracuseStep 1028839 = 1543259) B1543259
theorem B3093227 : Blo 912577 3093227 := bstep (se 1 (by rfl) ⟨2319920, by rfl⟩ : syracuseStep 3093227 = 4639841) B4639841
theorem B3289967 : Blo 912577 3289967 := bstep (se 1 (by rfl) ⟨2467475, by rfl⟩ : syracuseStep 3289967 = 4934951) B4934951
theorem B6960005 : Blo 912577 6960005 := bstep (se 4 (by rfl) ⟨652500, by rfl⟩ : syracuseStep 6960005 = 1305001) B1305001
theorem B3290543 : Blo 912577 3290543 := bstep (se 1 (by rfl) ⟨2467907, by rfl⟩ : syracuseStep 3290543 = 4935815) B4935815
theorem B11713025 : Blo 912577 11713025 := bstep (se 2 (by rfl) ⟨4392384, by rfl⟩ : syracuseStep 11713025 = 8784769) B8784769
theorem B14072491 : Blo 912577 14072491 := bstep (se 1 (by rfl) ⟨10554368, by rfl⟩ : syracuseStep 14072491 = 21108737) B21108737
theorem B25082563 : Blo 912577 25082563 := bstep (se 1 (by rfl) ⟨18811922, by rfl⟩ : syracuseStep 25082563 = 37623845) B37623845
theorem B2604079 : Blo 912577 2604079 := bstep (se 1 (by rfl) ⟨1953059, by rfl⟩ : syracuseStep 2604079 = 3906119) B3906119
theorem B5848159 : Blo 912577 5848159 := bstep (se 1 (by rfl) ⟨4386119, by rfl⟩ : syracuseStep 5848159 = 8772239) B8772239
theorem B4177403 : Blo 912577 4177403 := bstep (se 1 (by rfl) ⟨3133052, by rfl⟩ : syracuseStep 4177403 = 6266105) B6266105
theorem B16924409 : Blo 912577 16924409 := bstep (se 2 (by rfl) ⟨6346653, by rfl⟩ : syracuseStep 16924409 = 12693307) B12693307
theorem B22528003 : Blo 912577 22528003 := bstep (se 1 (by rfl) ⟨16896002, by rfl⟩ : syracuseStep 22528003 = 33792005) B33792005
theorem B1851839 : Blo 912577 1851839 := bstep (se 1 (by rfl) ⟨1388879, by rfl⟩ : syracuseStep 1851839 = 2777759) B2777759
theorem B28099169 : Blo 912577 28099169 := bstep (se 2 (by rfl) ⟨10537188, by rfl⟩ : syracuseStep 28099169 = 21074377) B21074377
theorem B2933587 : Blo 912577 2933587 := bstep (se 1 (by rfl) ⟨2200190, by rfl⟩ : syracuseStep 2933587 = 4400381) B4400381
theorem B66634609 : Blo 912577 66634609 := bstep (se 2 (by rfl) ⟨24987978, by rfl⟩ : syracuseStep 66634609 = 49975957) B49975957
theorem B14828453 : Blo 912577 14828453 := bstep (se 4 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 14828453 = 2780335) B2780335
theorem B4637735 : Blo 912577 4637735 := bstep (se 1 (by rfl) ⟨3478301, by rfl⟩ : syracuseStep 4637735 = 6956603) B6956603
theorem B1952137 : Blo 912577 1952137 := bstep (se 2 (by rfl) ⟨732051, by rfl⟩ : syracuseStep 1952137 = 1464103) B1464103
theorem B2607497 : Blo 912577 2607497 := bstep (se 2 (by rfl) ⟨977811, by rfl⟩ : syracuseStep 2607497 = 1955623) B1955623
theorem B2312833 : Blo 912577 2312833 := bstep (se 2 (by rfl) ⟨867312, by rfl⟩ : syracuseStep 2312833 = 1734625) B1734625
theorem B53463797 : Blo 912577 53463797 := bstep (se 5 (by rfl) ⟨2506115, by rfl⟩ : syracuseStep 53463797 = 5012231) B5012231
theorem B2313593 : Blo 912577 2313593 := bstep (se 2 (by rfl) ⟨867597, by rfl⟩ : syracuseStep 2313593 = 1735195) B1735195
theorem B15650171 : Blo 912577 15650171 := bstep (se 1 (by rfl) ⟨11737628, by rfl⟩ : syracuseStep 15650171 = 23475257) B23475257
theorem B14077415 : Blo 912577 14077415 := bstep (se 1 (by rfl) ⟨10558061, by rfl⟩ : syracuseStep 14077415 = 21116123) B21116123
theorem B5197931 : Blo 912577 5197931 := bstep (se 1 (by rfl) ⟨3898448, by rfl⟩ : syracuseStep 5197931 = 7796897) B7796897
theorem B2609273 : Blo 912577 2609273 := bstep (se 2 (by rfl) ⟨978477, by rfl⟩ : syracuseStep 2609273 = 1956955) B1956955
theorem B1953983 : Blo 912577 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B7820165 : Blo 912577 7820165 := bstep (se 4 (by rfl) ⟨733140, by rfl⟩ : syracuseStep 7820165 = 1466281) B1466281
theorem B2315375 : Blo 912577 2315375 := bstep (se 1 (by rfl) ⟨1736531, by rfl⟩ : syracuseStep 2315375 = 3473063) B3473063
theorem B3758089 : Blo 912577 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B2611271 : Blo 912577 2611271 := bstep (se 1 (by rfl) ⟨1958453, by rfl⟩ : syracuseStep 2611271 = 3916907) B3916907
theorem B5855591 : Blo 912577 5855591 := bstep (se 1 (by rfl) ⟨4391693, by rfl⟩ : syracuseStep 5855591 = 8783387) B8783387
theorem B2316671 : Blo 912577 2316671 := bstep (se 1 (by rfl) ⟨1737503, by rfl⟩ : syracuseStep 2316671 = 3475007) B3475007
theorem B2316883 : Blo 912577 2316883 := bstep (se 1 (by rfl) ⟨1737662, by rfl⟩ : syracuseStep 2316883 = 3475325) B3475325
theorem B1956511 : Blo 912577 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B2317025 : Blo 912577 2317025 := bstep (se 2 (by rfl) ⟨868884, by rfl⟩ : syracuseStep 2317025 = 1737769) B1737769
theorem B2055419 : Blo 912577 2055419 := bstep (se 1 (by rfl) ⟨1541564, by rfl⟩ : syracuseStep 2055419 = 3083129) B3083129
theorem B12508445 : Blo 912577 12508445 := bstep (se 3 (by rfl) ⟨2345333, by rfl⟩ : syracuseStep 12508445 = 4690667) B4690667
theorem B11132237 : Blo 912577 11132237 := bstep (se 3 (by rfl) ⟨2087294, by rfl⟩ : syracuseStep 11132237 = 4174589) B4174589
theorem B5857231 : Blo 912577 5857231 := bstep (se 1 (by rfl) ⟨4392923, by rfl⟩ : syracuseStep 5857231 = 8785847) B8785847
theorem B27812555 : Blo 912577 27812555 := bstep (se 1 (by rfl) ⟨20859416, by rfl⟩ : syracuseStep 27812555 = 41718833) B41718833
theorem B2319131 : Blo 912577 2319131 := bstep (se 1 (by rfl) ⟨1739348, by rfl⟩ : syracuseStep 2319131 = 3478697) B3478697
theorem B4940615 : Blo 912577 4940615 := bstep (se 1 (by rfl) ⟨3705461, by rfl⟩ : syracuseStep 4940615 = 7410923) B7410923
theorem B1368923 : Blo 912577 1368923 := bstep (se 1 (by rfl) ⟨1026692, by rfl⟩ : syracuseStep 1368923 = 2053385) B2053385
theorem B16933871 : Blo 912577 16933871 := bstep (se 1 (by rfl) ⟨12700403, by rfl⟩ : syracuseStep 16933871 = 25400807) B25400807
theorem B2319799 : Blo 912577 2319799 := bstep (se 1 (by rfl) ⟨1739849, by rfl⟩ : syracuseStep 2319799 = 3479699) B3479699
theorem B1369583 : Blo 912577 1369583 := bstep (se 1 (by rfl) ⟨1027187, by rfl⟩ : syracuseStep 1369583 = 2054375) B2054375
theorem B1369595 : Blo 912577 1369595 := bstep (se 1 (by rfl) ⟨1027196, by rfl⟩ : syracuseStep 1369595 = 2054393) B2054393
theorem B2057759 : Blo 912577 2057759 := bstep (se 1 (by rfl) ⟨1543319, by rfl⟩ : syracuseStep 2057759 = 3086639) B3086639
theorem B1369703 : Blo 912577 1369703 := bstep (se 1 (by rfl) ⟨1027277, by rfl⟩ : syracuseStep 1369703 = 2054555) B2054555
theorem B1369775 : Blo 912577 1369775 := bstep (se 1 (by rfl) ⟨1027331, by rfl⟩ : syracuseStep 1369775 = 2054663) B2054663
theorem B2057975 : Blo 912577 2057975 := bstep (se 1 (by rfl) ⟨1543481, by rfl⟩ : syracuseStep 2057975 = 3086963) B3086963
theorem B3467033 : Blo 912577 3467033 := bstep (se 2 (by rfl) ⟨1300137, by rfl⟩ : syracuseStep 3467033 = 2600275) B2600275
theorem B1369895 : Blo 912577 1369895 := bstep (se 1 (by rfl) ⟨1027421, by rfl⟩ : syracuseStep 1369895 = 2054843) B2054843
theorem B1369967 : Blo 912577 1369967 := bstep (se 1 (by rfl) ⟨1027475, by rfl⟩ : syracuseStep 1369967 = 2054951) B2054951
theorem B1370153 : Blo 912577 1370153 := bstep (se 2 (by rfl) ⟨513807, by rfl⟩ : syracuseStep 1370153 = 1027615) B1027615
theorem B6580273 : Blo 912577 6580273 := bstep (se 2 (by rfl) ⟨2467602, by rfl⟩ : syracuseStep 6580273 = 4935205) B4935205
theorem B2058335 : Blo 912577 2058335 := bstep (se 1 (by rfl) ⟨1543751, by rfl⟩ : syracuseStep 2058335 = 3087503) B3087503
theorem B3467519 : Blo 912577 3467519 := bstep (se 1 (by rfl) ⟨2600639, by rfl⟩ : syracuseStep 3467519 = 5201279) B5201279
theorem B1370495 : Blo 912577 1370495 := bstep (se 1 (by rfl) ⟨1027871, by rfl⟩ : syracuseStep 1370495 = 2055743) B2055743
theorem B2058695 : Blo 912577 2058695 := bstep (se 1 (by rfl) ⟨1544021, by rfl⟩ : syracuseStep 2058695 = 3088043) B3088043
theorem B1370735 : Blo 912577 1370735 := bstep (se 1 (by rfl) ⟨1028051, by rfl⟩ : syracuseStep 1370735 = 2056103) B2056103
theorem B2059055 : Blo 912577 2059055 := bstep (se 1 (by rfl) ⟨1544291, by rfl⟩ : syracuseStep 2059055 = 3088583) B3088583
theorem B15035507 : Blo 912577 15035507 := bstep (se 1 (by rfl) ⟨11276630, by rfl⟩ : syracuseStep 15035507 = 22553261) B22553261
theorem B75099257 : Blo 912577 75099257 := bstep (se 2 (by rfl) ⟨28162221, by rfl⟩ : syracuseStep 75099257 = 56324443) B56324443
theorem B2813143 : Blo 912577 2813143 := bstep (se 1 (by rfl) ⟨2109857, by rfl⟩ : syracuseStep 2813143 = 4219715) B4219715
theorem B5565833 : Blo 912577 5565833 := bstep (se 2 (by rfl) ⟨2087187, by rfl⟩ : syracuseStep 5565833 = 4174375) B4174375
theorem B912799 : Blo 912577 912799 := bstep (se 1 (by rfl) ⟨684599, by rfl⟩ : syracuseStep 912799 = 1369199) B1369199
theorem B912879 : Blo 912577 912879 := bstep (se 1 (by rfl) ⟨684659, by rfl⟩ : syracuseStep 912879 = 1369319) B1369319
theorem B912923 : Blo 912577 912923 := bstep (se 1 (by rfl) ⟨684692, by rfl⟩ : syracuseStep 912923 = 1369385) B1369385
theorem B913103 : Blo 912577 913103 := bstep (se 1 (by rfl) ⟨684827, by rfl⟩ : syracuseStep 913103 = 1369655) B1369655
theorem B2060063 : Blo 912577 2060063 := bstep (se 1 (by rfl) ⟨1545047, by rfl⟩ : syracuseStep 2060063 = 3090095) B3090095
theorem B913319 : Blo 912577 913319 := bstep (se 1 (by rfl) ⟨684989, by rfl⟩ : syracuseStep 913319 = 1369979) B1369979
theorem B913343 : Blo 912577 913343 := bstep (se 1 (by rfl) ⟨685007, by rfl⟩ : syracuseStep 913343 = 1370015) B1370015
theorem B1732583 : Blo 912577 1732583 := bstep (se 1 (by rfl) ⟨1299437, by rfl⟩ : syracuseStep 1732583 = 2598875) B2598875
theorem B2060279 : Blo 912577 2060279 := bstep (se 1 (by rfl) ⟨1545209, by rfl⟩ : syracuseStep 2060279 = 3090419) B3090419
theorem B913499 : Blo 912577 913499 := bstep (se 1 (by rfl) ⟨685124, by rfl⟩ : syracuseStep 913499 = 1370249) B1370249
theorem B913599 : Blo 912577 913599 := bstep (se 1 (by rfl) ⟨685199, by rfl⟩ : syracuseStep 913599 = 1370399) B1370399
theorem B913631 : Blo 912577 913631 := bstep (se 1 (by rfl) ⟨685223, by rfl⟩ : syracuseStep 913631 = 1370447) B1370447
theorem B913691 : Blo 912577 913691 := bstep (se 1 (by rfl) ⟨685268, by rfl⟩ : syracuseStep 913691 = 1370537) B1370537
theorem B2060639 : Blo 912577 2060639 := bstep (se 1 (by rfl) ⟨1545479, by rfl⟩ : syracuseStep 2060639 = 3090959) B3090959
theorem B53375375 : Blo 912577 53375375 := bstep (se 1 (by rfl) ⟨40031531, by rfl⟩ : syracuseStep 53375375 = 80063063) B80063063
theorem B913947 : Blo 912577 913947 := bstep (se 1 (by rfl) ⟨685460, by rfl⟩ : syracuseStep 913947 = 1370921) B1370921
theorem B8352359 : Blo 912577 8352359 := bstep (se 1 (by rfl) ⟨6264269, by rfl⟩ : syracuseStep 8352359 = 12528539) B12528539
theorem B914087 : Blo 912577 914087 := bstep (se 1 (by rfl) ⟨685565, by rfl⟩ : syracuseStep 914087 = 1371131) B1371131
theorem B914127 : Blo 912577 914127 := bstep (se 1 (by rfl) ⟨685595, by rfl⟩ : syracuseStep 914127 = 1371191) B1371191
theorem B914207 : Blo 912577 914207 := bstep (se 1 (by rfl) ⟨685655, by rfl⟩ : syracuseStep 914207 = 1371311) B1371311
theorem B914247 : Blo 912577 914247 := bstep (se 1 (by rfl) ⟨685685, by rfl⟩ : syracuseStep 914247 = 1371371) B1371371
theorem B3470161 : Blo 912577 3470161 := bstep (se 2 (by rfl) ⟨1301310, by rfl⟩ : syracuseStep 3470161 = 2602621) B2602621
theorem B2061359 : Blo 912577 2061359 := bstep (se 1 (by rfl) ⟨1546019, by rfl⟩ : syracuseStep 2061359 = 3092039) B3092039
theorem B7042157 : Blo 912577 7042157 := bstep (se 3 (by rfl) ⟨1320404, by rfl⟩ : syracuseStep 7042157 = 2640809) B2640809
theorem B5567675 : Blo 912577 5567675 := bstep (se 1 (by rfl) ⟨4175756, by rfl⟩ : syracuseStep 5567675 = 8351513) B8351513
theorem B914687 : Blo 912577 914687 := bstep (se 1 (by rfl) ⟨686015, by rfl⟩ : syracuseStep 914687 = 1372031) B1372031
theorem B1373609 : Blo 912577 1373609 := bstep (se 2 (by rfl) ⟨515103, by rfl⟩ : syracuseStep 1373609 = 1030207) B1030207
theorem B914911 : Blo 912577 914911 := bstep (se 1 (by rfl) ⟨686183, by rfl⟩ : syracuseStep 914911 = 1372367) B1372367
theorem B1373663 : Blo 912577 1373663 := bstep (se 1 (by rfl) ⟨1030247, by rfl⟩ : syracuseStep 1373663 = 2060495) B2060495
theorem B914991 : Blo 912577 914991 := bstep (se 1 (by rfl) ⟨686243, by rfl⟩ : syracuseStep 914991 = 1372487) B1372487
theorem B3470921 : Blo 912577 3470921 := bstep (se 2 (by rfl) ⟨1301595, by rfl⟩ : syracuseStep 3470921 = 2603191) B2603191
theorem B29652749 : Blo 912577 29652749 := bstep (se 3 (by rfl) ⟨5559890, by rfl⟩ : syracuseStep 29652749 = 11119781) B11119781
theorem B915303 : Blo 912577 915303 := bstep (se 1 (by rfl) ⟨686477, by rfl⟩ : syracuseStep 915303 = 1372955) B1372955
theorem B915487 : Blo 912577 915487 := bstep (se 1 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 915487 = 1373231) B1373231
theorem B3471407 : Blo 912577 3471407 := bstep (se 1 (by rfl) ⟨2603555, by rfl⟩ : syracuseStep 3471407 = 5207111) B5207111
theorem B915519 : Blo 912577 915519 := bstep (se 1 (by rfl) ⟨686639, by rfl⟩ : syracuseStep 915519 = 1373279) B1373279
theorem B915559 : Blo 912577 915559 := bstep (se 1 (by rfl) ⟨686669, by rfl⟩ : syracuseStep 915559 = 1373339) B1373339
theorem B1374311 : Blo 912577 1374311 := bstep (se 1 (by rfl) ⟨1030733, by rfl⟩ : syracuseStep 1374311 = 2061467) B2061467
theorem B915567 : Blo 912577 915567 := bstep (se 1 (by rfl) ⟨686675, by rfl⟩ : syracuseStep 915567 = 1373351) B1373351
theorem B25000487 : Blo 912577 25000487 := bstep (se 1 (by rfl) ⟨18750365, by rfl⟩ : syracuseStep 25000487 = 37500731) B37500731
theorem B916015 : Blo 912577 916015 := bstep (se 1 (by rfl) ⟨687011, by rfl⟩ : syracuseStep 916015 = 1374023) B1374023
theorem B20085407 : Blo 912577 20085407 := bstep (se 1 (by rfl) ⟨15064055, by rfl⟩ : syracuseStep 20085407 = 30128111) B30128111
theorem B916135 : Blo 912577 916135 := bstep (se 1 (by rfl) ⟨687101, by rfl⟩ : syracuseStep 916135 = 1374203) B1374203
theorem B916175 : Blo 912577 916175 := bstep (se 1 (by rfl) ⟨687131, by rfl⟩ : syracuseStep 916175 = 1374263) B1374263
theorem B916219 : Blo 912577 916219 := bstep (se 1 (by rfl) ⟨687164, by rfl⟩ : syracuseStep 916219 = 1374329) B1374329
theorem B916255 : Blo 912577 916255 := bstep (se 1 (by rfl) ⟨687191, by rfl⟩ : syracuseStep 916255 = 1374383) B1374383
theorem B916415 : Blo 912577 916415 := bstep (se 1 (by rfl) ⟨687311, by rfl⟩ : syracuseStep 916415 = 1374623) B1374623
theorem B3472379 : Blo 912577 3472379 := bstep (se 1 (by rfl) ⟨2604284, by rfl⟩ : syracuseStep 3472379 = 5208569) B5208569
theorem B916475 : Blo 912577 916475 := bstep (se 1 (by rfl) ⟨687356, by rfl⟩ : syracuseStep 916475 = 1374713) B1374713
theorem B6585695 : Blo 912577 6585695 := bstep (se 1 (by rfl) ⟨4939271, by rfl⟩ : syracuseStep 6585695 = 9878543) B9878543
theorem B3702185 : Blo 912577 3702185 := bstep (se 2 (by rfl) ⟨1388319, by rfl⟩ : syracuseStep 3702185 = 2776639) B2776639
theorem B3473563 : Blo 912577 3473563 := bstep (se 1 (by rfl) ⟨2605172, by rfl⟩ : syracuseStep 3473563 = 5210345) B5210345
theorem B3866807 : Blo 912577 3866807 := bstep (se 1 (by rfl) ⟨2900105, by rfl⟩ : syracuseStep 3866807 = 5800211) B5800211
theorem B1738331 : Blo 912577 1738331 := bstep (se 1 (by rfl) ⟨1303748, by rfl⟩ : syracuseStep 1738331 = 2607497) B2607497
theorem B1541801 : Blo 912577 1541801 := bstep (se 2 (by rfl) ⟨578175, by rfl⟩ : syracuseStep 1541801 = 1156351) B1156351
theorem B2197385 : Blo 912577 2197385 := bstep (se 2 (by rfl) ⟨824019, by rfl⟩ : syracuseStep 2197385 = 1648039) B1648039
theorem B1542395 : Blo 912577 1542395 := bstep (se 1 (by rfl) ⟨1156796, by rfl⟩ : syracuseStep 1542395 = 2313593) B2313593
theorem B45156989 : Blo 912577 45156989 := bstep (se 3 (by rfl) ⟨8466935, by rfl⟩ : syracuseStep 45156989 = 16933871) B16933871
theorem B14847133 : Blo 912577 14847133 := bstep (se 3 (by rfl) ⟨2783837, by rfl⟩ : syracuseStep 14847133 = 5567675) B5567675
theorem B5213443 : Blo 912577 5213443 := bstep (se 1 (by rfl) ⟨3910082, by rfl⟩ : syracuseStep 5213443 = 7820165) B7820165
theorem B1543583 : Blo 912577 1543583 := bstep (se 1 (by rfl) ⟨1157687, by rfl⟩ : syracuseStep 1543583 = 2315375) B2315375
theorem B3083777 : Blo 912577 3083777 := bstep (se 2 (by rfl) ⟨1156416, by rfl⟩ : syracuseStep 3083777 = 2312833) B2312833
theorem B79007561 : Blo 912577 79007561 := bstep (se 2 (by rfl) ⟨29627835, by rfl⟩ : syracuseStep 79007561 = 59255671) B59255671
theorem B1740847 : Blo 912577 1740847 := bstep (se 1 (by rfl) ⟨1305635, by rfl⟩ : syracuseStep 1740847 = 2611271) B2611271
theorem B3903727 : Blo 912577 3903727 := bstep (se 1 (by rfl) ⟨2927795, by rfl⟩ : syracuseStep 3903727 = 5855591) B5855591
theorem B1544447 : Blo 912577 1544447 := bstep (se 1 (by rfl) ⟨1158335, by rfl⟩ : syracuseStep 1544447 = 2316671) B2316671
theorem B1544683 : Blo 912577 1544683 := bstep (se 1 (by rfl) ⟨1158512, by rfl⟩ : syracuseStep 1544683 = 2317025) B2317025
theorem B3478211 : Blo 912577 3478211 := bstep (se 1 (by rfl) ⟨2608658, by rfl⟩ : syracuseStep 3478211 = 5217317) B5217317
theorem B1546087 : Blo 912577 1546087 := bstep (se 1 (by rfl) ⟨1159565, by rfl⟩ : syracuseStep 1546087 = 2319131) B2319131
theorem B4626881 : Blo 912577 4626881 := bstep (se 2 (by rfl) ⟨1735080, by rfl⟩ : syracuseStep 4626881 = 3470161) B3470161
theorem B3087935 : Blo 912577 3087935 := bstep (se 1 (by rfl) ⟨2315951, by rfl⟩ : syracuseStep 3087935 = 4631903) B4631903
theorem B3710555 : Blo 912577 3710555 := bstep (se 1 (by rfl) ⟨2782916, by rfl⟩ : syracuseStep 3710555 = 5565833) B5565833
theorem B1155055 : Blo 912577 1155055 := bstep (se 1 (by rfl) ⟨866291, by rfl⟩ : syracuseStep 1155055 = 1732583) B1732583
theorem B7807043 : Blo 912577 7807043 := bstep (se 1 (by rfl) ⟨5855282, by rfl⟩ : syracuseStep 7807043 = 11710565) B11710565
theorem B4694771 : Blo 912577 4694771 := bstep (se 1 (by rfl) ⟨3521078, by rfl⟩ : syracuseStep 4694771 = 7042157) B7042157
theorem B3089177 : Blo 912577 3089177 := bstep (se 2 (by rfl) ⟨1158441, by rfl⟩ : syracuseStep 3089177 = 2316883) B2316883
theorem B19768499 : Blo 912577 19768499 := bstep (se 1 (by rfl) ⟨14826374, by rfl⟩ : syracuseStep 19768499 = 29652749) B29652749
theorem B14100077 : Blo 912577 14100077 := bstep (se 3 (by rfl) ⟨2643764, by rfl⟩ : syracuseStep 14100077 = 5287529) B5287529
theorem B7808683 : Blo 912577 7808683 := bstep (se 1 (by rfl) ⟨5856512, by rfl⟩ : syracuseStep 7808683 = 11713025) B11713025
theorem B2468123 : Blo 912577 2468123 := bstep (se 1 (by rfl) ⟨1851092, by rfl⟩ : syracuseStep 2468123 = 3702185) B3702185
theorem B11282939 : Blo 912577 11282939 := bstep (se 1 (by rfl) ⟨8462204, by rfl⟩ : syracuseStep 11282939 = 16924409) B16924409
theorem B7809641 : Blo 912577 7809641 := bstep (se 2 (by rfl) ⟨2928615, by rfl⟩ : syracuseStep 7809641 = 5857231) B5857231
theorem B6958061 : Blo 912577 6958061 := bstep (se 3 (by rfl) ⟨1304636, by rfl⟩ : syracuseStep 6958061 = 2609273) B2609273
theorem B1027399 : Blo 912577 1027399 := bstep (se 1 (by rfl) ⟨770549, by rfl⟩ : syracuseStep 1027399 = 1541099) B1541099
theorem B3091823 : Blo 912577 3091823 := bstep (se 1 (by rfl) ⟨2318867, by rfl⟩ : syracuseStep 3091823 = 4637735) B4637735
theorem B88846145 : Blo 912577 88846145 := bstep (se 2 (by rfl) ⟨33317304, by rfl⟩ : syracuseStep 88846145 = 66634609) B66634609
theorem B1159039 : Blo 912577 1159039 := bstep (se 1 (by rfl) ⟨869279, by rfl⟩ : syracuseStep 1159039 = 1738559) B1738559
theorem B3093065 : Blo 912577 3093065 := bstep (se 2 (by rfl) ⟨1159899, by rfl⟩ : syracuseStep 3093065 = 2319799) B2319799
theorem B3912475 : Blo 912577 3912475 := bstep (se 1 (by rfl) ⟨2934356, by rfl⟩ : syracuseStep 3912475 = 5868713) B5868713
theorem B10433447 : Blo 912577 10433447 := bstep (se 1 (by rfl) ⟨7825085, by rfl⟩ : syracuseStep 10433447 = 15650171) B15650171
theorem B31699973 : Blo 912577 31699973 := bstep (se 4 (by rfl) ⟨2971872, by rfl⟩ : syracuseStep 31699973 = 5943745) B5943745
theorem B2602849 : Blo 912577 2602849 := bstep (se 2 (by rfl) ⟨976068, by rfl⟩ : syracuseStep 2602849 = 1952137) B1952137
theorem B1030171 : Blo 912577 1030171 := bstep (se 1 (by rfl) ⟨772628, by rfl⟩ : syracuseStep 1030171 = 1545257) B1545257
theorem B4765823 : Blo 912577 4765823 := bstep (se 1 (by rfl) ⟨3574367, by rfl⟩ : syracuseStep 4765823 = 7148735) B7148735
theorem B2472275 : Blo 912577 2472275 := bstep (se 1 (by rfl) ⟨1854206, by rfl⟩ : syracuseStep 2472275 = 3708413) B3708413
theorem B1030783 : Blo 912577 1030783 := bstep (se 1 (by rfl) ⟨773087, by rfl⟩ : syracuseStep 1030783 = 1546175) B1546175
theorem B3750857 : Blo 912577 3750857 := bstep (se 2 (by rfl) ⟨1406571, by rfl⟩ : syracuseStep 3750857 = 2813143) B2813143
theorem B15645797 : Blo 912577 15645797 := bstep (se 4 (by rfl) ⟨1466793, by rfl⟩ : syracuseStep 15645797 = 2933587) B2933587
theorem B8338963 : Blo 912577 8338963 := bstep (se 1 (by rfl) ⟨6254222, by rfl⟩ : syracuseStep 8338963 = 12508445) B12508445
theorem B7421491 : Blo 912577 7421491 := bstep (se 1 (by rfl) ⟨5566118, by rfl⟩ : syracuseStep 7421491 = 11132237) B11132237
theorem B6930845 : Blo 912577 6930845 := bstep (se 3 (by rfl) ⟨1299533, by rfl⟩ : syracuseStep 6930845 = 2599067) B2599067
theorem B3293743 : Blo 912577 3293743 := bstep (se 1 (by rfl) ⟨2470307, by rfl⟩ : syracuseStep 3293743 = 4940615) B4940615
theorem B6603545 : Blo 912577 6603545 := bstep (se 2 (by rfl) ⟨2476329, by rfl⟩ : syracuseStep 6603545 = 4952659) B4952659
theorem B2311355 : Blo 912577 2311355 := bstep (se 1 (by rfl) ⟨1733516, by rfl⟩ : syracuseStep 2311355 = 3467033) B3467033
theorem B2311679 : Blo 912577 2311679 := bstep (se 1 (by rfl) ⟨1733759, by rfl⟩ : syracuseStep 2311679 = 3467519) B3467519
theorem B4639031 : Blo 912577 4639031 := bstep (se 1 (by rfl) ⟨3479273, by rfl⟩ : syracuseStep 4639031 = 6958547) B6958547
theorem B4640003 : Blo 912577 4640003 := bstep (se 1 (by rfl) ⟨3480002, by rfl⟩ : syracuseStep 4640003 = 6960005) B6960005
theorem B2608681 : Blo 912577 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B18763321 : Blo 912577 18763321 := bstep (se 2 (by rfl) ⟨7036245, by rfl⟩ : syracuseStep 18763321 = 14072491) B14072491
theorem B33443417 : Blo 912577 33443417 := bstep (se 2 (by rfl) ⟨12541281, by rfl⟩ : syracuseStep 33443417 = 25082563) B25082563
theorem B2313947 : Blo 912577 2313947 := bstep (se 1 (by rfl) ⟨1735460, by rfl⟩ : syracuseStep 2313947 = 3470921) B3470921
theorem B37539773 : Blo 912577 37539773 := bstep (se 3 (by rfl) ⟨7038707, by rfl⟩ : syracuseStep 37539773 = 14077415) B14077415
theorem B2314271 : Blo 912577 2314271 := bstep (se 1 (by rfl) ⟨1735703, by rfl⟩ : syracuseStep 2314271 = 3471407) B3471407
theorem B16666991 : Blo 912577 16666991 := bstep (se 1 (by rfl) ⟨12500243, by rfl⟩ : syracuseStep 16666991 = 25000487) B25000487
theorem B13390271 : Blo 912577 13390271 := bstep (se 1 (by rfl) ⟨10042703, by rfl⟩ : syracuseStep 13390271 = 20085407) B20085407
theorem B2314919 : Blo 912577 2314919 := bstep (se 1 (by rfl) ⟨1736189, by rfl⟩ : syracuseStep 2314919 = 3472379) B3472379
theorem B30037337 : Blo 912577 30037337 := bstep (se 2 (by rfl) ⟨11264001, by rfl⟩ : syracuseStep 30037337 = 22528003) B22528003
theorem B2053547 : Blo 912577 2053547 := bstep (se 1 (by rfl) ⟨1540160, by rfl⟩ : syracuseStep 2053547 = 3080321) B3080321
theorem B1234559 : Blo 912577 1234559 := bstep (se 1 (by rfl) ⟨925919, by rfl⟩ : syracuseStep 1234559 = 1851839) B1851839
theorem B18732779 : Blo 912577 18732779 := bstep (se 1 (by rfl) ⟨14049584, by rfl⟩ : syracuseStep 18732779 = 28099169) B28099169
theorem B2053871 : Blo 912577 2053871 := bstep (se 1 (by rfl) ⟨1540403, by rfl⟩ : syracuseStep 2053871 = 3080807) B3080807
theorem B2316023 : Blo 912577 2316023 := bstep (se 1 (by rfl) ⟨1737017, by rfl⟩ : syracuseStep 2316023 = 3474035) B3474035
theorem B9885635 : Blo 912577 9885635 := bstep (se 1 (by rfl) ⟨7414226, by rfl⟩ : syracuseStep 9885635 = 14828453) B14828453
theorem B5200847 : Blo 912577 5200847 := bstep (se 1 (by rfl) ⟨3900635, by rfl⟩ : syracuseStep 5200847 = 7801271) B7801271
theorem B35642531 : Blo 912577 35642531 := bstep (se 1 (by rfl) ⟨26731898, by rfl⟩ : syracuseStep 35642531 = 53463797) B53463797
theorem B2055545 : Blo 912577 2055545 := bstep (se 2 (by rfl) ⟨770829, by rfl⟩ : syracuseStep 2055545 = 1541659) B1541659
theorem B5856695 : Blo 912577 5856695 := bstep (se 1 (by rfl) ⟨4392521, by rfl⟩ : syracuseStep 5856695 = 8785043) B8785043
theorem B2318291 : Blo 912577 2318291 := bstep (se 1 (by rfl) ⟨1738718, by rfl⟩ : syracuseStep 2318291 = 3477437) B3477437
theorem B2056247 : Blo 912577 2056247 := bstep (se 1 (by rfl) ⟨1542185, by rfl⟩ : syracuseStep 2056247 = 3084371) B3084371
theorem B8773697 : Blo 912577 8773697 := bstep (se 2 (by rfl) ⟨3290136, by rfl⟩ : syracuseStep 8773697 = 6580273) B6580273
theorem B3465287 : Blo 912577 3465287 := bstep (se 1 (by rfl) ⟨2598965, by rfl⟩ : syracuseStep 3465287 = 5197931) B5197931
theorem B2056319 : Blo 912577 2056319 := bstep (se 1 (by rfl) ⟨1542239, by rfl⟩ : syracuseStep 2056319 = 3084479) B3084479
theorem B1302655 : Blo 912577 1302655 := bstep (se 1 (by rfl) ⟨976991, by rfl⟩ : syracuseStep 1302655 = 1953983) B1953983
theorem B2056427 : Blo 912577 2056427 := bstep (se 1 (by rfl) ⟨1542320, by rfl⟩ : syracuseStep 2056427 = 3084641) B3084641
theorem B3466273 : Blo 912577 3466273 := bstep (se 2 (by rfl) ⟨1299852, by rfl⟩ : syracuseStep 3466273 = 2599705) B2599705
theorem B1369577 : Blo 912577 1369577 := bstep (se 2 (by rfl) ⟨513591, by rfl⟩ : syracuseStep 1369577 = 1027183) B1027183
theorem B2058155 : Blo 912577 2058155 := bstep (se 1 (by rfl) ⟨1543616, by rfl⟩ : syracuseStep 2058155 = 3087233) B3087233
theorem B2058209 : Blo 912577 2058209 := bstep (se 2 (by rfl) ⟨771828, by rfl⟩ : syracuseStep 2058209 = 1543657) B1543657
theorem B2058281 : Blo 912577 2058281 := bstep (se 2 (by rfl) ⟨771855, by rfl⟩ : syracuseStep 2058281 = 1543711) B1543711
theorem B1370279 : Blo 912577 1370279 := bstep (se 1 (by rfl) ⟨1027709, by rfl⟩ : syracuseStep 1370279 = 2055419) B2055419
theorem B18541703 : Blo 912577 18541703 := bstep (se 1 (by rfl) ⟨13906277, by rfl⟩ : syracuseStep 18541703 = 27812555) B27812555
theorem B912615 : Blo 912577 912615 := bstep (se 1 (by rfl) ⟨684461, by rfl⟩ : syracuseStep 912615 = 1368923) B1368923
theorem B1371785 : Blo 912577 1371785 := bstep (se 2 (by rfl) ⟨514419, by rfl⟩ : syracuseStep 1371785 = 1028839) B1028839
theorem B913055 : Blo 912577 913055 := bstep (se 1 (by rfl) ⟨684791, by rfl⟩ : syracuseStep 913055 = 1369583) B1369583
theorem B913063 : Blo 912577 913063 := bstep (se 1 (by rfl) ⟨684797, by rfl⟩ : syracuseStep 913063 = 1369595) B1369595
theorem B1371839 : Blo 912577 1371839 := bstep (se 1 (by rfl) ⟨1028879, by rfl⟩ : syracuseStep 1371839 = 2057759) B2057759
theorem B913135 : Blo 912577 913135 := bstep (se 1 (by rfl) ⟨684851, by rfl⟩ : syracuseStep 913135 = 1369703) B1369703
theorem B913183 : Blo 912577 913183 := bstep (se 1 (by rfl) ⟨684887, by rfl⟩ : syracuseStep 913183 = 1369775) B1369775
theorem B1371983 : Blo 912577 1371983 := bstep (se 1 (by rfl) ⟨1028987, by rfl⟩ : syracuseStep 1371983 = 2057975) B2057975
theorem B913263 : Blo 912577 913263 := bstep (se 1 (by rfl) ⟨684947, by rfl⟩ : syracuseStep 913263 = 1369895) B1369895
theorem B913311 : Blo 912577 913311 := bstep (se 1 (by rfl) ⟨684983, by rfl⟩ : syracuseStep 913311 = 1369967) B1369967
theorem B913435 : Blo 912577 913435 := bstep (se 1 (by rfl) ⟨685076, by rfl⟩ : syracuseStep 913435 = 1370153) B1370153
theorem B1372223 : Blo 912577 1372223 := bstep (se 1 (by rfl) ⟨1029167, by rfl⟩ : syracuseStep 1372223 = 2058335) B2058335
theorem B913663 : Blo 912577 913663 := bstep (se 1 (by rfl) ⟨685247, by rfl⟩ : syracuseStep 913663 = 1370495) B1370495
theorem B1372463 : Blo 912577 1372463 := bstep (se 1 (by rfl) ⟨1029347, by rfl⟩ : syracuseStep 1372463 = 2058695) B2058695
theorem B913823 : Blo 912577 913823 := bstep (se 1 (by rfl) ⟨685367, by rfl⟩ : syracuseStep 913823 = 1370735) B1370735
theorem B1372703 : Blo 912577 1372703 := bstep (se 1 (by rfl) ⟨1029527, by rfl⟩ : syracuseStep 1372703 = 2059055) B2059055
theorem B1733167 : Blo 912577 1733167 := bstep (se 1 (by rfl) ⟨1299875, by rfl⟩ : syracuseStep 1733167 = 2599751) B2599751
theorem B2060855 : Blo 912577 2060855 := bstep (se 1 (by rfl) ⟨1545641, by rfl⟩ : syracuseStep 2060855 = 3091283) B3091283
theorem B10023671 : Blo 912577 10023671 := bstep (se 1 (by rfl) ⟨7517753, by rfl⟩ : syracuseStep 10023671 = 15035507) B15035507
theorem B50066171 : Blo 912577 50066171 := bstep (se 1 (by rfl) ⟨37549628, by rfl⟩ : syracuseStep 50066171 = 75099257) B75099257
theorem B1373375 : Blo 912577 1373375 := bstep (se 1 (by rfl) ⟨1030031, by rfl⟩ : syracuseStep 1373375 = 2060063) B2060063
theorem B1373519 : Blo 912577 1373519 := bstep (se 1 (by rfl) ⟨1030139, by rfl⟩ : syracuseStep 1373519 = 2060279) B2060279
theorem B5010785 : Blo 912577 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B5207611 : Blo 912577 5207611 := bstep (se 1 (by rfl) ⟨3905708, by rfl⟩ : syracuseStep 5207611 = 7811417) B7811417
theorem B1373759 : Blo 912577 1373759 := bstep (se 1 (by rfl) ⟨1030319, by rfl⟩ : syracuseStep 1373759 = 2060639) B2060639
theorem B35583583 : Blo 912577 35583583 := bstep (se 1 (by rfl) ⟨26687687, by rfl⟩ : syracuseStep 35583583 = 53375375) B53375375
theorem B5568239 : Blo 912577 5568239 := bstep (se 1 (by rfl) ⟨4176179, by rfl⟩ : syracuseStep 5568239 = 8352359) B8352359
theorem B2062151 : Blo 912577 2062151 := bstep (se 1 (by rfl) ⟨1546613, by rfl⟩ : syracuseStep 2062151 = 3093227) B3093227
theorem B2193311 : Blo 912577 2193311 := bstep (se 1 (by rfl) ⟨1644983, by rfl⟩ : syracuseStep 2193311 = 3289967) B3289967
theorem B1374239 : Blo 912577 1374239 := bstep (se 1 (by rfl) ⟨1030679, by rfl⟩ : syracuseStep 1374239 = 2061359) B2061359
theorem B5208137 : Blo 912577 5208137 := bstep (se 2 (by rfl) ⟨1953051, by rfl⟩ : syracuseStep 5208137 = 3906103) B3906103
theorem B915739 : Blo 912577 915739 := bstep (se 1 (by rfl) ⟨686804, by rfl⟩ : syracuseStep 915739 = 1373609) B1373609
theorem B2193695 : Blo 912577 2193695 := bstep (se 1 (by rfl) ⟨1645271, by rfl⟩ : syracuseStep 2193695 = 3290543) B3290543
theorem B915775 : Blo 912577 915775 := bstep (se 1 (by rfl) ⟨686831, by rfl⟩ : syracuseStep 915775 = 1373663) B1373663
theorem B3472105 : Blo 912577 3472105 := bstep (se 2 (by rfl) ⟨1302039, by rfl⟩ : syracuseStep 3472105 = 2604079) B2604079
theorem B916207 : Blo 912577 916207 := bstep (se 1 (by rfl) ⟨687155, by rfl⟩ : syracuseStep 916207 = 1374311) B1374311
theorem B7797545 : Blo 912577 7797545 := bstep (se 2 (by rfl) ⟨2924079, by rfl⟩ : syracuseStep 7797545 = 5848159) B5848159
theorem B4390463 : Blo 912577 4390463 := bstep (se 1 (by rfl) ⟨3292847, by rfl⟩ : syracuseStep 4390463 = 6585695) B6585695
theorem B2784935 : Blo 912577 2784935 := bstep (se 1 (by rfl) ⟨2088701, by rfl⟩ : syracuseStep 2784935 = 4177403) B4177403
theorem B1736873 : Blo 912577 1736873 := bstep (se 2 (by rfl) ⟨651327, by rfl⟩ : syracuseStep 1736873 = 1302655) B1302655
theorem B23396525 : Blo 912577 23396525 := bstep (se 3 (by rfl) ⟨4386848, by rfl⟩ : syracuseStep 23396525 = 8773697) B8773697
theorem B4620563 : Blo 912577 4620563 := bstep (se 1 (by rfl) ⟨3465422, by rfl⟩ : syracuseStep 4620563 = 6930845) B6930845
theorem B4391657 : Blo 912577 4391657 := bstep (se 2 (by rfl) ⟨1646871, by rfl⟩ : syracuseStep 4391657 = 3293743) B3293743
theorem B1540903 : Blo 912577 1540903 := bstep (se 1 (by rfl) ⟨1155677, by rfl⟩ : syracuseStep 1540903 = 2311355) B2311355
theorem B1541119 : Blo 912577 1541119 := bstep (se 1 (by rfl) ⟨1155839, by rfl⟩ : syracuseStep 1541119 = 2311679) B2311679
theorem B4621697 : Blo 912577 4621697 := bstep (se 2 (by rfl) ⟨1733136, by rfl⟩ : syracuseStep 4621697 = 3466273) B3466273
theorem B1542631 : Blo 912577 1542631 := bstep (se 1 (by rfl) ⟨1156973, by rfl⟩ : syracuseStep 1542631 = 2313947) B2313947
theorem B1542847 : Blo 912577 1542847 := bstep (se 1 (by rfl) ⟨1157135, by rfl⟩ : syracuseStep 1542847 = 2314271) B2314271
theorem B11111327 : Blo 912577 11111327 := bstep (se 1 (by rfl) ⟨8333495, by rfl⟩ : syracuseStep 11111327 = 16666991) B16666991
theorem B1543279 : Blo 912577 1543279 := bstep (se 1 (by rfl) ⟨1157459, by rfl⟩ : syracuseStep 1543279 = 2314919) B2314919
theorem B20024891 : Blo 912577 20024891 := bstep (se 1 (by rfl) ⟨15018668, by rfl⟩ : syracuseStep 20024891 = 30037337) B30037337
theorem B12488519 : Blo 912577 12488519 := bstep (se 1 (by rfl) ⟨9366389, by rfl⟩ : syracuseStep 12488519 = 18732779) B18732779
theorem B1544015 : Blo 912577 1544015 := bstep (se 1 (by rfl) ⟨1158011, by rfl⟩ : syracuseStep 1544015 = 2316023) B2316023
theorem B6590423 : Blo 912577 6590423 := bstep (se 1 (by rfl) ⟨4942817, by rfl⟩ : syracuseStep 6590423 = 9885635) B9885635
theorem B19796177 : Blo 912577 19796177 := bstep (se 2 (by rfl) ⟨7423566, by rfl⟩ : syracuseStep 19796177 = 14847133) B14847133
theorem B3084587 : Blo 912577 3084587 := bstep (se 1 (by rfl) ⟨2313440, by rfl⟩ : syracuseStep 3084587 = 4626881) B4626881
theorem B6951257 : Blo 912577 6951257 := bstep (se 2 (by rfl) ⟨2606721, by rfl⟩ : syracuseStep 6951257 = 5213443) B5213443
theorem B3478241 : Blo 912577 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B23761687 : Blo 912577 23761687 := bstep (se 1 (by rfl) ⟨17821265, by rfl⟩ : syracuseStep 23761687 = 35642531) B35642531
theorem B3904463 : Blo 912577 3904463 := bstep (se 1 (by rfl) ⟨2928347, by rfl⟩ : syracuseStep 3904463 = 5856695) B5856695
theorem B1545385 : Blo 912577 1545385 := bstep (se 2 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 1545385 = 1159039) B1159039
theorem B1545527 : Blo 912577 1545527 := bstep (se 1 (by rfl) ⟨1159145, by rfl⟩ : syracuseStep 1545527 = 2318291) B2318291
theorem B13178999 : Blo 912577 13178999 := bstep (se 1 (by rfl) ⟨9884249, by rfl⟩ : syracuseStep 13178999 = 19768499) B19768499
theorem B5216633 : Blo 912577 5216633 := bstep (se 2 (by rfl) ⟨1956237, by rfl⟩ : syracuseStep 5216633 = 3912475) B3912475
theorem B1645415 : Blo 912577 1645415 := bstep (se 1 (by rfl) ⟨1234061, by rfl⟩ : syracuseStep 1645415 = 2468123) B2468123
theorem B12361135 : Blo 912577 12361135 := bstep (se 1 (by rfl) ⟨9270851, by rfl⟩ : syracuseStep 12361135 = 18541703) B18541703
theorem B6955631 : Blo 912577 6955631 := bstep (se 1 (by rfl) ⟨5216723, by rfl⟩ : syracuseStep 6955631 = 10433447) B10433447
theorem B4629473 : Blo 912577 4629473 := bstep (se 2 (by rfl) ⟨1736052, by rfl⟩ : syracuseStep 4629473 = 3472105) B3472105
theorem B3712159 : Blo 912577 3712159 := bstep (se 1 (by rfl) ⟨2784119, by rfl⟩ : syracuseStep 3712159 = 5568239) B5568239
theorem B11707901 : Blo 912577 11707901 := bstep (se 3 (by rfl) ⟨2195231, by rfl⟩ : syracuseStep 11707901 = 4390463) B4390463
theorem B1648183 : Blo 912577 1648183 := bstep (se 1 (by rfl) ⟨1236137, by rfl⟩ : syracuseStep 1648183 = 2472275) B2472275
theorem B2500571 : Blo 912577 2500571 := bstep (se 1 (by rfl) ⟨1875428, by rfl⟩ : syracuseStep 2500571 = 3750857) B3750857
theorem B11118617 : Blo 912577 11118617 := bstep (se 2 (by rfl) ⟨4169481, by rfl⟩ : syracuseStep 11118617 = 8338963) B8338963
theorem B10430531 : Blo 912577 10430531 := bstep (se 1 (by rfl) ⟨7822898, by rfl⟩ : syracuseStep 10430531 = 15645797) B15645797
theorem B4631417 : Blo 912577 4631417 := bstep (se 2 (by rfl) ⟨1736781, by rfl⟩ : syracuseStep 4631417 = 3473563) B3473563
theorem B4402363 : Blo 912577 4402363 := bstep (se 1 (by rfl) ⟨3301772, by rfl⟩ : syracuseStep 4402363 = 6603545) B6603545
theorem B1158887 : Blo 912577 1158887 := bstep (se 1 (by rfl) ⟨869165, by rfl⟩ : syracuseStep 1158887 = 1738331) B1738331
theorem B1027867 : Blo 912577 1027867 := bstep (se 1 (by rfl) ⟨770900, by rfl⟩ : syracuseStep 1027867 = 1541801) B1541801
theorem B1028263 : Blo 912577 1028263 := bstep (se 1 (by rfl) ⟨771197, by rfl⟩ : syracuseStep 1028263 = 1542395) B1542395
theorem B3092687 : Blo 912577 3092687 := bstep (se 1 (by rfl) ⟨2319515, by rfl⟩ : syracuseStep 3092687 = 4639031) B4639031
theorem B3093335 : Blo 912577 3093335 := bstep (se 1 (by rfl) ⟨2320001, by rfl⟩ : syracuseStep 3093335 = 4640003) B4640003
theorem B1029055 : Blo 912577 1029055 := bstep (se 1 (by rfl) ⟨771791, by rfl⟩ : syracuseStep 1029055 = 1543583) B1543583
theorem B22295611 : Blo 912577 22295611 := bstep (se 1 (by rfl) ⟨16721708, by rfl⟩ : syracuseStep 22295611 = 33443417) B33443417
theorem B52671707 : Blo 912577 52671707 := bstep (se 1 (by rfl) ⟨39503780, by rfl⟩ : syracuseStep 52671707 = 79007561) B79007561
theorem B1029631 : Blo 912577 1029631 := bstep (se 1 (by rfl) ⟨772223, by rfl⟩ : syracuseStep 1029631 = 1544447) B1544447
theorem B8926847 : Blo 912577 8926847 := bstep (se 1 (by rfl) ⟨6695135, by rfl⟩ : syracuseStep 8926847 = 13390271) B13390271
theorem B3292157 : Blo 912577 3292157 := bstep (se 3 (by rfl) ⟨617279, by rfl⟩ : syracuseStep 3292157 = 1234559) B1234559
theorem B25017761 : Blo 912577 25017761 := bstep (se 2 (by rfl) ⟨9381660, by rfl⟩ : syracuseStep 25017761 = 18763321) B18763321
theorem B2473703 : Blo 912577 2473703 := bstep (se 1 (by rfl) ⟨1855277, by rfl⟩ : syracuseStep 2473703 = 3710555) B3710555
theorem B2310191 : Blo 912577 2310191 := bstep (se 1 (by rfl) ⟨1732643, by rfl⟩ : syracuseStep 2310191 = 3465287) B3465287
theorem B3129847 : Blo 912577 3129847 := bstep (se 1 (by rfl) ⟨2347385, by rfl⟩ : syracuseStep 3129847 = 4694771) B4694771
theorem B2310889 : Blo 912577 2310889 := bstep (se 2 (by rfl) ⟨866583, by rfl⟩ : syracuseStep 2310889 = 1733167) B1733167
theorem B7521959 : Blo 912577 7521959 := bstep (se 1 (by rfl) ⟨5641469, by rfl⟩ : syracuseStep 7521959 = 11282939) B11282939
theorem B4638707 : Blo 912577 4638707 := bstep (se 1 (by rfl) ⟨3479030, by rfl⟩ : syracuseStep 4638707 = 6958061) B6958061
theorem B59230763 : Blo 912577 59230763 := bstep (se 1 (by rfl) ⟨44423072, by rfl⟩ : syracuseStep 59230763 = 88846145) B88846145
theorem B33377447 : Blo 912577 33377447 := bstep (se 1 (by rfl) ⟨25033085, by rfl⟩ : syracuseStep 33377447 = 50066171) B50066171
theorem B1462207 : Blo 912577 1462207 := bstep (se 1 (by rfl) ⟨1096655, by rfl⟩ : syracuseStep 1462207 = 2193311) B2193311
theorem B1462463 : Blo 912577 1462463 := bstep (se 1 (by rfl) ⟨1096847, by rfl⟩ : syracuseStep 1462463 = 2193695) B2193695
theorem B5198363 : Blo 912577 5198363 := bstep (se 1 (by rfl) ⟨3898772, by rfl⟩ : syracuseStep 5198363 = 7797545) B7797545
theorem B1856623 : Blo 912577 1856623 := bstep (se 1 (by rfl) ⟨1392467, by rfl⟩ : syracuseStep 1856623 = 2784935) B2784935
theorem B2577871 : Blo 912577 2577871 := bstep (se 1 (by rfl) ⟨1933403, by rfl⟩ : syracuseStep 2577871 = 3866807) B3866807
theorem B1464923 : Blo 912577 1464923 := bstep (se 1 (by rfl) ⟨1098692, by rfl⟩ : syracuseStep 1464923 = 2197385) B2197385
theorem B30104659 : Blo 912577 30104659 := bstep (se 1 (by rfl) ⟨22578494, by rfl⟩ : syracuseStep 30104659 = 45156989) B45156989
theorem B10411577 : Blo 912577 10411577 := bstep (se 2 (by rfl) ⟨3904341, by rfl⟩ : syracuseStep 10411577 = 7808683) B7808683
theorem B2055851 : Blo 912577 2055851 := bstep (se 1 (by rfl) ⟨1541888, by rfl⟩ : syracuseStep 2055851 = 3083777) B3083777
theorem B25026515 : Blo 912577 25026515 := bstep (se 1 (by rfl) ⟨18769886, by rfl⟩ : syracuseStep 25026515 = 37539773) B37539773
theorem B2318807 : Blo 912577 2318807 := bstep (se 1 (by rfl) ⟨1739105, by rfl⟩ : syracuseStep 2318807 = 3478211) B3478211
theorem B1369031 : Blo 912577 1369031 := bstep (se 1 (by rfl) ⟨1026773, by rfl⟩ : syracuseStep 1369031 = 2053547) B2053547
theorem B1369247 : Blo 912577 1369247 := bstep (se 1 (by rfl) ⟨1026935, by rfl⟩ : syracuseStep 1369247 = 2053871) B2053871
theorem B1369865 : Blo 912577 1369865 := bstep (se 2 (by rfl) ⟨513699, by rfl⟩ : syracuseStep 1369865 = 1027399) B1027399
theorem B3467231 : Blo 912577 3467231 := bstep (se 1 (by rfl) ⟨2600423, by rfl⟩ : syracuseStep 3467231 = 5200847) B5200847
theorem B1370363 : Blo 912577 1370363 := bstep (se 1 (by rfl) ⟨1027772, by rfl⟩ : syracuseStep 1370363 = 2055545) B2055545
theorem B2058623 : Blo 912577 2058623 := bstep (se 1 (by rfl) ⟨1543967, by rfl⟩ : syracuseStep 2058623 = 3087935) B3087935
theorem B1370831 : Blo 912577 1370831 := bstep (se 1 (by rfl) ⟨1028123, by rfl⟩ : syracuseStep 1370831 = 2056247) B2056247
theorem B5204695 : Blo 912577 5204695 := bstep (se 1 (by rfl) ⟨3903521, by rfl⟩ : syracuseStep 5204695 = 7807043) B7807043
theorem B2321129 : Blo 912577 2321129 := bstep (se 2 (by rfl) ⟨870423, by rfl⟩ : syracuseStep 2321129 = 1740847) B1740847
theorem B1370879 : Blo 912577 1370879 := bstep (se 1 (by rfl) ⟨1028159, by rfl⟩ : syracuseStep 1370879 = 2056319) B2056319
theorem B1370951 : Blo 912577 1370951 := bstep (se 1 (by rfl) ⟨1028213, by rfl⟩ : syracuseStep 1370951 = 2056427) B2056427
theorem B5204969 : Blo 912577 5204969 := bstep (se 2 (by rfl) ⟨1951863, by rfl⟩ : syracuseStep 5204969 = 3903727) B3903727
theorem B2059451 : Blo 912577 2059451 := bstep (se 1 (by rfl) ⟨1544588, by rfl⟩ : syracuseStep 2059451 = 3089177) B3089177
theorem B2059577 : Blo 912577 2059577 := bstep (se 2 (by rfl) ⟨772341, by rfl⟩ : syracuseStep 2059577 = 1544683) B1544683
theorem B913051 : Blo 912577 913051 := bstep (se 1 (by rfl) ⟨684788, by rfl⟩ : syracuseStep 913051 = 1369577) B1369577
theorem B9400051 : Blo 912577 9400051 := bstep (se 1 (by rfl) ⟨7050038, by rfl⟩ : syracuseStep 9400051 = 14100077) B14100077
theorem B1372103 : Blo 912577 1372103 := bstep (se 1 (by rfl) ⟨1029077, by rfl⟩ : syracuseStep 1372103 = 2058155) B2058155
theorem B1372139 : Blo 912577 1372139 := bstep (se 1 (by rfl) ⟨1029104, by rfl⟩ : syracuseStep 1372139 = 2058209) B2058209
theorem B1372187 : Blo 912577 1372187 := bstep (se 1 (by rfl) ⟨1029140, by rfl⟩ : syracuseStep 1372187 = 2058281) B2058281
theorem B913519 : Blo 912577 913519 := bstep (se 1 (by rfl) ⟨685139, by rfl⟩ : syracuseStep 913519 = 1370279) B1370279
theorem B5206427 : Blo 912577 5206427 := bstep (se 1 (by rfl) ⟨3904820, by rfl⟩ : syracuseStep 5206427 = 7809641) B7809641
theorem B6943481 : Blo 912577 6943481 := bstep (se 2 (by rfl) ⟨2603805, by rfl⟩ : syracuseStep 6943481 = 5207611) B5207611
theorem B47444777 : Blo 912577 47444777 := bstep (se 2 (by rfl) ⟨17791791, by rfl⟩ : syracuseStep 47444777 = 35583583) B35583583
theorem B2061215 : Blo 912577 2061215 := bstep (se 1 (by rfl) ⟨1545911, by rfl⟩ : syracuseStep 2061215 = 3091823) B3091823
theorem B914523 : Blo 912577 914523 := bstep (se 1 (by rfl) ⟨685892, by rfl⟩ : syracuseStep 914523 = 1371785) B1371785
theorem B914559 : Blo 912577 914559 := bstep (se 1 (by rfl) ⟨685919, by rfl⟩ : syracuseStep 914559 = 1371839) B1371839
theorem B3470465 : Blo 912577 3470465 := bstep (se 2 (by rfl) ⟨1301424, by rfl⟩ : syracuseStep 3470465 = 2602849) B2602849
theorem B2061449 : Blo 912577 2061449 := bstep (se 2 (by rfl) ⟨773043, by rfl⟩ : syracuseStep 2061449 = 1546087) B1546087
theorem B914655 : Blo 912577 914655 := bstep (se 1 (by rfl) ⟨685991, by rfl⟩ : syracuseStep 914655 = 1371983) B1371983
theorem B1373561 : Blo 912577 1373561 := bstep (se 2 (by rfl) ⟨515085, by rfl⟩ : syracuseStep 1373561 = 1030171) B1030171
theorem B914815 : Blo 912577 914815 := bstep (se 1 (by rfl) ⟨686111, by rfl⟩ : syracuseStep 914815 = 1372223) B1372223
theorem B914975 : Blo 912577 914975 := bstep (se 1 (by rfl) ⟨686231, by rfl⟩ : syracuseStep 914975 = 1372463) B1372463
theorem B915135 : Blo 912577 915135 := bstep (se 1 (by rfl) ⟨686351, by rfl⟩ : syracuseStep 915135 = 1372703) B1372703
theorem B1373903 : Blo 912577 1373903 := bstep (se 1 (by rfl) ⟨1030427, by rfl⟩ : syracuseStep 1373903 = 2060855) B2060855
theorem B2062043 : Blo 912577 2062043 := bstep (se 1 (by rfl) ⟨1546532, by rfl⟩ : syracuseStep 2062043 = 3093065) B3093065
theorem B6682447 : Blo 912577 6682447 := bstep (se 1 (by rfl) ⟨5011835, by rfl⟩ : syracuseStep 6682447 = 10023671) B10023671
theorem B21133315 : Blo 912577 21133315 := bstep (se 1 (by rfl) ⟨15849986, by rfl⟩ : syracuseStep 21133315 = 31699973) B31699973
theorem B915583 : Blo 912577 915583 := bstep (se 1 (by rfl) ⟨686687, by rfl⟩ : syracuseStep 915583 = 1373375) B1373375
theorem B1374377 : Blo 912577 1374377 := bstep (se 2 (by rfl) ⟨515391, by rfl⟩ : syracuseStep 1374377 = 1030783) B1030783
theorem B915679 : Blo 912577 915679 := bstep (se 1 (by rfl) ⟨686759, by rfl⟩ : syracuseStep 915679 = 1373519) B1373519
theorem B3340523 : Blo 912577 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B915839 : Blo 912577 915839 := bstep (se 1 (by rfl) ⟨686879, by rfl⟩ : syracuseStep 915839 = 1373759) B1373759
theorem B1374767 : Blo 912577 1374767 := bstep (se 1 (by rfl) ⟨1031075, by rfl⟩ : syracuseStep 1374767 = 2062151) B2062151
theorem B916159 : Blo 912577 916159 := bstep (se 1 (by rfl) ⟨687119, by rfl⟩ : syracuseStep 916159 = 1374239) B1374239
theorem B3472091 : Blo 912577 3472091 := bstep (se 1 (by rfl) ⟨2604068, by rfl⟩ : syracuseStep 3472091 = 5208137) B5208137
theorem B3177215 : Blo 912577 3177215 := bstep (se 1 (by rfl) ⟨2382911, by rfl⟩ : syracuseStep 3177215 = 4765823) B4765823
theorem B9895321 : Blo 912577 9895321 := bstep (se 2 (by rfl) ⟨3710745, by rfl⟩ : syracuseStep 9895321 = 7421491) B7421491
theorem B1540073 : Blo 912577 1540073 := bstep (se 2 (by rfl) ⟨577527, by rfl⟩ : syracuseStep 1540073 = 1155055) B1155055
theorem B1540127 : Blo 912577 1540127 := bstep (se 1 (by rfl) ⟨1155095, by rfl⟩ : syracuseStep 1540127 = 2310191) B2310191
theorem B15597683 : Blo 912577 15597683 := bstep (se 1 (by rfl) ⟨11698262, by rfl⟩ : syracuseStep 15597683 = 23396525) B23396525
theorem B3080375 : Blo 912577 3080375 := bstep (se 1 (by rfl) ⟨2310281, by rfl⟩ : syracuseStep 3080375 = 4620563) B4620563
theorem B52789805 : Blo 912577 52789805 := bstep (se 3 (by rfl) ⟨9898088, by rfl⟩ : syracuseStep 52789805 = 19796177) B19796177
theorem B3081131 : Blo 912577 3081131 := bstep (se 1 (by rfl) ⟨2310848, by rfl⟩ : syracuseStep 3081131 = 4621697) B4621697
theorem B3081185 : Blo 912577 3081185 := bstep (se 2 (by rfl) ⟨1155444, by rfl⟩ : syracuseStep 3081185 = 2310889) B2310889
theorem B5014639 : Blo 912577 5014639 := bstep (se 1 (by rfl) ⟨3760979, by rfl⟩ : syracuseStep 5014639 = 7521959) B7521959
theorem B39487175 : Blo 912577 39487175 := bstep (se 1 (by rfl) ⟨29615381, by rfl⟩ : syracuseStep 39487175 = 59230763) B59230763
theorem B7407551 : Blo 912577 7407551 := bstep (se 1 (by rfl) ⟨5555663, by rfl⟩ : syracuseStep 7407551 = 11111327) B11111327
theorem B2197577 : Blo 912577 2197577 := bstep (se 2 (by rfl) ⟨824091, by rfl⟩ : syracuseStep 2197577 = 1648183) B1648183
theorem B8325679 : Blo 912577 8325679 := bstep (se 1 (by rfl) ⟨6244259, by rfl⟩ : syracuseStep 8325679 = 12488519) B12488519
theorem B4393615 : Blo 912577 4393615 := bstep (se 1 (by rfl) ⟨3295211, by rfl⟩ : syracuseStep 4393615 = 6590423) B6590423
theorem B8785999 : Blo 912577 8785999 := bstep (se 1 (by rfl) ⟨6589499, by rfl⟩ : syracuseStep 8785999 = 13178999) B13178999
theorem B5869817 : Blo 912577 5869817 := bstep (se 2 (by rfl) ⟨2201181, by rfl⟩ : syracuseStep 5869817 = 4402363) B4402363
theorem B3477755 : Blo 912577 3477755 := bstep (se 1 (by rfl) ⟨2608316, by rfl⟩ : syracuseStep 3477755 = 5216633) B5216633
theorem B16684343 : Blo 912577 16684343 := bstep (se 1 (by rfl) ⟨12513257, by rfl⟩ : syracuseStep 16684343 = 25026515) B25026515
theorem B1545871 : Blo 912577 1545871 := bstep (se 1 (by rfl) ⟨1159403, by rfl⟩ : syracuseStep 1545871 = 2318807) B2318807
theorem B3086315 : Blo 912577 3086315 := bstep (se 1 (by rfl) ⟨2314736, by rfl⟩ : syracuseStep 3086315 = 4629473) B4629473
theorem B19798181 : Blo 912577 19798181 := bstep (se 4 (by rfl) ⟨1856079, by rfl⟩ : syracuseStep 19798181 = 3712159) B3712159
theorem B7805267 : Blo 912577 7805267 := bstep (se 1 (by rfl) ⟨5853950, by rfl⟩ : syracuseStep 7805267 = 11707901) B11707901
theorem B7412411 : Blo 912577 7412411 := bstep (se 1 (by rfl) ⟨5559308, by rfl⟩ : syracuseStep 7412411 = 11118617) B11118617
theorem B6953687 : Blo 912577 6953687 := bstep (se 1 (by rfl) ⟨5215265, by rfl⟩ : syracuseStep 6953687 = 10430531) B10430531
theorem B29727481 : Blo 912577 29727481 := bstep (se 2 (by rfl) ⟨11147805, by rfl⟩ : syracuseStep 29727481 = 22295611) B22295611
theorem B3906461 : Blo 912577 3906461 := bstep (se 3 (by rfl) ⟨732461, by rfl⟩ : syracuseStep 3906461 = 1464923) B1464923
theorem B1547419 : Blo 912577 1547419 := bstep (se 1 (by rfl) ⟨1160564, by rfl⟩ : syracuseStep 1547419 = 2321129) B2321129
theorem B3087611 : Blo 912577 3087611 := bstep (se 1 (by rfl) ⟨2315708, by rfl⟩ : syracuseStep 3087611 = 4631417) B4631417
theorem B89006525 : Blo 912577 89006525 := bstep (se 3 (by rfl) ⟨16688723, by rfl⟩ : syracuseStep 89006525 = 33377447) B33377447
theorem B4628987 : Blo 912577 4628987 := bstep (se 1 (by rfl) ⟨3471740, by rfl⟩ : syracuseStep 4628987 = 6943481) B6943481
theorem B31629851 : Blo 912577 31629851 := bstep (se 1 (by rfl) ⟨23722388, by rfl⟩ : syracuseStep 31629851 = 47444777) B47444777
theorem B3090365 : Blo 912577 3090365 := bstep (se 3 (by rfl) ⟨579443, by rfl⟩ : syracuseStep 3090365 = 1158887) B1158887
theorem B1649135 : Blo 912577 1649135 := bstep (se 1 (by rfl) ⟨1236851, by rfl⟩ : syracuseStep 1649135 = 2473703) B2473703
theorem B1026715 : Blo 912577 1026715 := bstep (se 1 (by rfl) ⟨770036, by rfl⟩ : syracuseStep 1026715 = 1540073) B1540073
theorem B1157915 : Blo 912577 1157915 := bstep (se 1 (by rfl) ⟨868436, by rfl⟩ : syracuseStep 1157915 = 1736873) B1736873
theorem B2927771 : Blo 912577 2927771 := bstep (se 1 (by rfl) ⟨2195828, by rfl⟩ : syracuseStep 2927771 = 4391657) B4391657
theorem B3092471 : Blo 912577 3092471 := bstep (se 1 (by rfl) ⟨2319353, by rfl⟩ : syracuseStep 3092471 = 4638707) B4638707
theorem B13349927 : Blo 912577 13349927 := bstep (se 1 (by rfl) ⟨10012445, by rfl⟩ : syracuseStep 13349927 = 20024891) B20024891
theorem B1029343 : Blo 912577 1029343 := bstep (se 1 (by rfl) ⟨772007, by rfl⟩ : syracuseStep 1029343 = 1544015) B1544015
theorem B16692517 : Blo 912577 16692517 := bstep (se 4 (by rfl) ⟨1564923, by rfl⟩ : syracuseStep 16692517 = 3129847) B3129847
theorem B4634171 : Blo 912577 4634171 := bstep (se 1 (by rfl) ⟨3475628, by rfl⟩ : syracuseStep 4634171 = 6951257) B6951257
theorem B2602975 : Blo 912577 2602975 := bstep (se 1 (by rfl) ⟨1952231, by rfl⟩ : syracuseStep 2602975 = 3904463) B3904463
theorem B1030351 : Blo 912577 1030351 := bstep (se 1 (by rfl) ⟨772763, by rfl⟩ : syracuseStep 1030351 = 1545527) B1545527
theorem B1096943 : Blo 912577 1096943 := bstep (se 1 (by rfl) ⟨822707, by rfl⟩ : syracuseStep 1096943 = 1645415) B1645415
theorem B12533401 : Blo 912577 12533401 := bstep (se 2 (by rfl) ⟨4700025, by rfl⟩ : syracuseStep 12533401 = 9400051) B9400051
theorem B1949609 : Blo 912577 1949609 := bstep (se 2 (by rfl) ⟨731103, by rfl⟩ : syracuseStep 1949609 = 1462207) B1462207
theorem B4637087 : Blo 912577 4637087 := bstep (se 1 (by rfl) ⟨3477815, by rfl⟩ : syracuseStep 4637087 = 6955631) B6955631
theorem B2311487 : Blo 912577 2311487 := bstep (se 1 (by rfl) ⟨1733615, by rfl⟩ : syracuseStep 2311487 = 3467231) B3467231
theorem B2475497 : Blo 912577 2475497 := bstep (se 2 (by rfl) ⟨928311, by rfl⟩ : syracuseStep 2475497 = 1856623) B1856623
theorem B2313643 : Blo 912577 2313643 := bstep (se 1 (by rfl) ⟨1735232, by rfl⟩ : syracuseStep 2313643 = 3470465) B3470465
theorem B35114471 : Blo 912577 35114471 := bstep (se 1 (by rfl) ⟨26335853, by rfl⟩ : syracuseStep 35114471 = 52671707) B52671707
theorem B5951231 : Blo 912577 5951231 := bstep (se 1 (by rfl) ⟨4463423, by rfl⟩ : syracuseStep 5951231 = 8926847) B8926847
theorem B2314727 : Blo 912577 2314727 := bstep (se 1 (by rfl) ⟨1736045, by rfl⟩ : syracuseStep 2314727 = 3472091) B3472091
theorem B2118143 : Blo 912577 2118143 := bstep (se 1 (by rfl) ⟨1588607, by rfl⟩ : syracuseStep 2118143 = 3177215) B3177215
theorem B13193761 : Blo 912577 13193761 := bstep (se 2 (by rfl) ⟨4947660, by rfl⟩ : syracuseStep 13193761 = 9895321) B9895321
theorem B2054537 : Blo 912577 2054537 := bstep (se 2 (by rfl) ⟨770451, by rfl⟩ : syracuseStep 2054537 = 1540903) B1540903
theorem B2054825 : Blo 912577 2054825 := bstep (se 2 (by rfl) ⟨770559, by rfl⟩ : syracuseStep 2054825 = 1541119) B1541119
theorem B974975 : Blo 912577 974975 := bstep (se 1 (by rfl) ⟨731231, by rfl⟩ : syracuseStep 974975 = 1462463) B1462463
theorem B2056391 : Blo 912577 2056391 := bstep (se 1 (by rfl) ⟨1542293, by rfl⟩ : syracuseStep 2056391 = 3084587) B3084587
theorem B3465575 : Blo 912577 3465575 := bstep (se 1 (by rfl) ⟨2599181, by rfl⟩ : syracuseStep 3465575 = 5198363) B5198363
theorem B2318827 : Blo 912577 2318827 := bstep (se 1 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 2318827 = 3478241) B3478241
theorem B2056841 : Blo 912577 2056841 := bstep (se 2 (by rfl) ⟨771315, by rfl⟩ : syracuseStep 2056841 = 1542631) B1542631
theorem B2057129 : Blo 912577 2057129 := bstep (se 2 (by rfl) ⟨771423, by rfl⟩ : syracuseStep 2057129 = 1542847) B1542847
theorem B6939593 : Blo 912577 6939593 := bstep (se 2 (by rfl) ⟨2602347, by rfl⟩ : syracuseStep 6939593 = 5204695) B5204695
theorem B2057705 : Blo 912577 2057705 := bstep (se 2 (by rfl) ⟨771639, by rfl⟩ : syracuseStep 2057705 = 1543279) B1543279
theorem B1370489 : Blo 912577 1370489 := bstep (se 2 (by rfl) ⟨513933, by rfl⟩ : syracuseStep 1370489 = 1027867) B1027867
theorem B6941051 : Blo 912577 6941051 := bstep (se 1 (by rfl) ⟨5205788, by rfl⟩ : syracuseStep 6941051 = 10411577) B10411577
theorem B1370567 : Blo 912577 1370567 := bstep (se 1 (by rfl) ⟨1027925, by rfl⟩ : syracuseStep 1370567 = 2055851) B2055851
theorem B1371017 : Blo 912577 1371017 := bstep (se 2 (by rfl) ⟨514131, by rfl⟩ : syracuseStep 1371017 = 1028263) B1028263
theorem B8908061 : Blo 912577 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B912687 : Blo 912577 912687 := bstep (se 1 (by rfl) ⟨684515, by rfl⟩ : syracuseStep 912687 = 1369031) B1369031
theorem B912831 : Blo 912577 912831 := bstep (se 1 (by rfl) ⟨684623, by rfl⟩ : syracuseStep 912831 = 1369247) B1369247
theorem B31682249 : Blo 912577 31682249 := bstep (se 2 (by rfl) ⟨11880843, by rfl⟩ : syracuseStep 31682249 = 23761687) B23761687
theorem B913243 : Blo 912577 913243 := bstep (se 1 (by rfl) ⟨684932, by rfl⟩ : syracuseStep 913243 = 1369865) B1369865
theorem B1372073 : Blo 912577 1372073 := bstep (se 2 (by rfl) ⟨514527, by rfl⟩ : syracuseStep 1372073 = 1029055) B1029055
theorem B1667047 : Blo 912577 1667047 := bstep (se 1 (by rfl) ⟨1250285, by rfl⟩ : syracuseStep 1667047 = 2500571) B2500571
theorem B913575 : Blo 912577 913575 := bstep (se 1 (by rfl) ⟨685181, by rfl⟩ : syracuseStep 913575 = 1370363) B1370363
theorem B2060513 : Blo 912577 2060513 := bstep (se 2 (by rfl) ⟨772692, by rfl⟩ : syracuseStep 2060513 = 1545385) B1545385
theorem B1372415 : Blo 912577 1372415 := bstep (se 1 (by rfl) ⟨1029311, by rfl⟩ : syracuseStep 1372415 = 2058623) B2058623
theorem B913887 : Blo 912577 913887 := bstep (se 1 (by rfl) ⟨685415, by rfl⟩ : syracuseStep 913887 = 1370831) B1370831
theorem B913919 : Blo 912577 913919 := bstep (se 1 (by rfl) ⟨685439, by rfl⟩ : syracuseStep 913919 = 1370879) B1370879
theorem B913967 : Blo 912577 913967 := bstep (se 1 (by rfl) ⟨685475, by rfl⟩ : syracuseStep 913967 = 1370951) B1370951
theorem B3437161 : Blo 912577 3437161 := bstep (se 2 (by rfl) ⟨1288935, by rfl⟩ : syracuseStep 3437161 = 2577871) B2577871
theorem B3469979 : Blo 912577 3469979 := bstep (se 1 (by rfl) ⟨2602484, by rfl⟩ : syracuseStep 3469979 = 5204969) B5204969
theorem B1372841 : Blo 912577 1372841 := bstep (se 2 (by rfl) ⟨514815, by rfl⟩ : syracuseStep 1372841 = 1029631) B1029631
theorem B1372967 : Blo 912577 1372967 := bstep (se 1 (by rfl) ⟨1029725, by rfl⟩ : syracuseStep 1372967 = 2059451) B2059451
theorem B1373051 : Blo 912577 1373051 := bstep (se 1 (by rfl) ⟨1029788, by rfl⟩ : syracuseStep 1373051 = 2059577) B2059577
theorem B8909929 : Blo 912577 8909929 := bstep (se 2 (by rfl) ⟨3341223, by rfl⟩ : syracuseStep 8909929 = 6682447) B6682447
theorem B914735 : Blo 912577 914735 := bstep (se 1 (by rfl) ⟨686051, by rfl⟩ : syracuseStep 914735 = 1372103) B1372103
theorem B914759 : Blo 912577 914759 := bstep (se 1 (by rfl) ⟨686069, by rfl⟩ : syracuseStep 914759 = 1372139) B1372139
theorem B28177753 : Blo 912577 28177753 := bstep (se 2 (by rfl) ⟨10566657, by rfl⟩ : syracuseStep 28177753 = 21133315) B21133315
theorem B914791 : Blo 912577 914791 := bstep (se 1 (by rfl) ⟨686093, by rfl⟩ : syracuseStep 914791 = 1372187) B1372187
theorem B2061791 : Blo 912577 2061791 := bstep (se 1 (by rfl) ⟨1546343, by rfl⟩ : syracuseStep 2061791 = 3092687) B3092687
theorem B3470951 : Blo 912577 3470951 := bstep (se 1 (by rfl) ⟨2603213, by rfl⟩ : syracuseStep 3470951 = 5206427) B5206427
theorem B2062223 : Blo 912577 2062223 := bstep (se 1 (by rfl) ⟨1546667, by rfl⟩ : syracuseStep 2062223 = 3093335) B3093335
theorem B1374143 : Blo 912577 1374143 := bstep (se 1 (by rfl) ⟨1030607, by rfl⟩ : syracuseStep 1374143 = 2061215) B2061215
theorem B1374299 : Blo 912577 1374299 := bstep (se 1 (by rfl) ⟨1030724, by rfl⟩ : syracuseStep 1374299 = 2061449) B2061449
theorem B915707 : Blo 912577 915707 := bstep (se 1 (by rfl) ⟨686780, by rfl⟩ : syracuseStep 915707 = 1373561) B1373561
theorem B915935 : Blo 912577 915935 := bstep (se 1 (by rfl) ⟨686951, by rfl⟩ : syracuseStep 915935 = 1373903) B1373903
theorem B1374695 : Blo 912577 1374695 := bstep (se 1 (by rfl) ⟨1031021, by rfl⟩ : syracuseStep 1374695 = 2062043) B2062043
theorem B40139545 : Blo 912577 40139545 := bstep (se 2 (by rfl) ⟨15052329, by rfl⟩ : syracuseStep 40139545 = 30104659) B30104659
theorem B916251 : Blo 912577 916251 := bstep (se 1 (by rfl) ⟨687188, by rfl⟩ : syracuseStep 916251 = 1374377) B1374377
theorem B916511 : Blo 912577 916511 := bstep (se 1 (by rfl) ⟨687383, by rfl⟩ : syracuseStep 916511 = 1374767) B1374767
theorem B16481513 : Blo 912577 16481513 := bstep (se 2 (by rfl) ⟨6180567, by rfl⟩ : syracuseStep 16481513 = 12361135) B12361135
theorem B2194771 : Blo 912577 2194771 := bstep (se 1 (by rfl) ⟨1646078, by rfl⟩ : syracuseStep 2194771 = 3292157) B3292157
theorem B16678507 : Blo 912577 16678507 := bstep (se 1 (by rfl) ⟨12508880, by rfl⟩ : syracuseStep 16678507 = 25017761) B25017761
theorem B35193203 : Blo 912577 35193203 := bstep (se 1 (by rfl) ⟨26394902, by rfl⟩ : syracuseStep 35193203 = 52789805) B52789805
theorem B1540991 : Blo 912577 1540991 := bstep (se 1 (by rfl) ⟨1155743, by rfl⟩ : syracuseStep 1540991 = 2311487) B2311487
theorem B3967487 : Blo 912577 3967487 := bstep (se 1 (by rfl) ⟨2975615, by rfl⟩ : syracuseStep 3967487 = 5951231) B5951231
theorem B1543151 : Blo 912577 1543151 := bstep (se 1 (by rfl) ⟨1157363, by rfl⟩ : syracuseStep 1543151 = 2314727) B2314727
theorem B1412095 : Blo 912577 1412095 := bstep (se 1 (by rfl) ⟨1059071, by rfl⟩ : syracuseStep 1412095 = 2118143) B2118143
theorem B3084857 : Blo 912577 3084857 := bstep (se 2 (by rfl) ⟨1156821, by rfl⟩ : syracuseStep 3084857 = 2313643) B2313643
theorem B3085991 : Blo 912577 3085991 := bstep (se 1 (by rfl) ⟨2314493, by rfl⟩ : syracuseStep 3085991 = 4628987) B4628987
theorem B26744741 : Blo 912577 26744741 := bstep (se 4 (by rfl) ⟨2507319, by rfl⟩ : syracuseStep 26744741 = 5014639) B5014639
theorem B4626395 : Blo 912577 4626395 := bstep (se 1 (by rfl) ⟨3469796, by rfl⟩ : syracuseStep 4626395 = 6939593) B6939593
theorem B4627367 : Blo 912577 4627367 := bstep (se 1 (by rfl) ⟨3470525, by rfl⟩ : syracuseStep 4627367 = 6941051) B6941051
theorem B22256689 : Blo 912577 22256689 := bstep (se 2 (by rfl) ⟨8346258, by rfl⟩ : syracuseStep 22256689 = 16692517) B16692517
theorem B3087773 : Blo 912577 3087773 := bstep (se 3 (by rfl) ⟨578957, by rfl⟩ : syracuseStep 3087773 = 1157915) B1157915
theorem B43950701 : Blo 912577 43950701 := bstep (se 3 (by rfl) ⟨8240756, by rfl⟩ : syracuseStep 43950701 = 16481513) B16481513
theorem B2925181 : Blo 912577 2925181 := bstep (se 3 (by rfl) ⟨548471, by rfl⟩ : syracuseStep 2925181 = 1096943) B1096943
theorem B53519393 : Blo 912577 53519393 := bstep (se 2 (by rfl) ⟨20069772, by rfl⟩ : syracuseStep 53519393 = 40139545) B40139545
theorem B3089447 : Blo 912577 3089447 := bstep (se 1 (by rfl) ⟨2317085, by rfl⟩ : syracuseStep 3089447 = 4634171) B4634171
theorem B2926361 : Blo 912577 2926361 := bstep (se 2 (by rfl) ⟨1097385, by rfl⟩ : syracuseStep 2926361 = 2194771) B2194771
theorem B1026751 : Blo 912577 1026751 := bstep (se 1 (by rfl) ⟨770063, by rfl⟩ : syracuseStep 1026751 = 1540127) B1540127
theorem B10398455 : Blo 912577 10398455 := bstep (se 1 (by rfl) ⟨7798841, by rfl⟩ : syracuseStep 10398455 = 15597683) B15597683
theorem B3091391 : Blo 912577 3091391 := bstep (se 1 (by rfl) ⟨2318543, by rfl⟩ : syracuseStep 3091391 = 4637087) B4637087
theorem B2599933 : Blo 912577 2599933 := bstep (se 3 (by rfl) ⟨487487, by rfl⟩ : syracuseStep 2599933 = 974975) B974975
theorem B3091769 : Blo 912577 3091769 := bstep (se 2 (by rfl) ⟨1159413, by rfl⟩ : syracuseStep 3091769 = 2318827) B2318827
theorem B1650331 : Blo 912577 1650331 := bstep (se 1 (by rfl) ⟨1237748, by rfl⟩ : syracuseStep 1650331 = 2475497) B2475497
theorem B26324783 : Blo 912577 26324783 := bstep (se 1 (by rfl) ⟨19743587, by rfl⟩ : syracuseStep 26324783 = 39487175) B39487175
theorem B23409647 : Blo 912577 23409647 := bstep (se 1 (by rfl) ⟨17557235, by rfl⟩ : syracuseStep 23409647 = 35114471) B35114471
theorem B3913211 : Blo 912577 3913211 := bstep (se 1 (by rfl) ⟨2934908, by rfl⟩ : syracuseStep 3913211 = 5869817) B5869817
theorem B18331525 : Blo 912577 18331525 := bstep (se 4 (by rfl) ⟨1718580, by rfl⟩ : syracuseStep 18331525 = 3437161) B3437161
theorem B11122895 : Blo 912577 11122895 := bstep (se 1 (by rfl) ⟨8342171, by rfl⟩ : syracuseStep 11122895 = 16684343) B16684343
theorem B4635791 : Blo 912577 4635791 := bstep (se 1 (by rfl) ⟨3476843, by rfl⟩ : syracuseStep 4635791 = 6953687) B6953687
theorem B2604307 : Blo 912577 2604307 := bstep (se 1 (by rfl) ⟨1953230, by rfl⟩ : syracuseStep 2604307 = 3906461) B3906461
theorem B11714665 : Blo 912577 11714665 := bstep (se 2 (by rfl) ⟨4392999, by rfl⟩ : syracuseStep 11714665 = 8785999) B8785999
theorem B2310383 : Blo 912577 2310383 := bstep (se 1 (by rfl) ⟨1732787, by rfl⟩ : syracuseStep 2310383 = 3465575) B3465575
theorem B21086567 : Blo 912577 21086567 := bstep (se 1 (by rfl) ⟨15814925, by rfl⟩ : syracuseStep 21086567 = 31629851) B31629851
theorem B11879905 : Blo 912577 11879905 := bstep (se 2 (by rfl) ⟨4454964, by rfl⟩ : syracuseStep 11879905 = 8909929) B8909929
theorem B1099423 : Blo 912577 1099423 := bstep (se 1 (by rfl) ⟨824567, by rfl⟩ : syracuseStep 1099423 = 1649135) B1649135
theorem B37570337 : Blo 912577 37570337 := bstep (se 2 (by rfl) ⟨14088876, by rfl⟩ : syracuseStep 37570337 = 28177753) B28177753
theorem B1951847 : Blo 912577 1951847 := bstep (se 1 (by rfl) ⟨1463885, by rfl⟩ : syracuseStep 1951847 = 2927771) B2927771
theorem B21121499 : Blo 912577 21121499 := bstep (se 1 (by rfl) ⟨15841124, by rfl⟩ : syracuseStep 21121499 = 31682249) B31682249
theorem B2313319 : Blo 912577 2313319 := bstep (se 1 (by rfl) ⟨1734989, by rfl⟩ : syracuseStep 2313319 = 3469979) B3469979
theorem B8899951 : Blo 912577 8899951 := bstep (se 1 (by rfl) ⟨6674963, by rfl⟩ : syracuseStep 8899951 = 13349927) B13349927
theorem B39636641 : Blo 912577 39636641 := bstep (se 2 (by rfl) ⟨14863740, by rfl⟩ : syracuseStep 39636641 = 29727481) B29727481
theorem B2313967 : Blo 912577 2313967 := bstep (se 1 (by rfl) ⟨1735475, by rfl⟩ : syracuseStep 2313967 = 3470951) B3470951
theorem B22238009 : Blo 912577 22238009 := bstep (se 2 (by rfl) ⟨8339253, by rfl⟩ : syracuseStep 22238009 = 16678507) B16678507
theorem B1299739 : Blo 912577 1299739 := bstep (se 1 (by rfl) ⟨974804, by rfl⟩ : syracuseStep 1299739 = 1949609) B1949609
theorem B2053583 : Blo 912577 2053583 := bstep (se 1 (by rfl) ⟨1540187, by rfl⟩ : syracuseStep 2053583 = 3080375) B3080375
theorem B2054087 : Blo 912577 2054087 := bstep (se 1 (by rfl) ⟨1540565, by rfl⟩ : syracuseStep 2054087 = 3081131) B3081131
theorem B2054123 : Blo 912577 2054123 := bstep (se 1 (by rfl) ⟨1540592, by rfl⟩ : syracuseStep 2054123 = 3081185) B3081185
theorem B4938367 : Blo 912577 4938367 := bstep (se 1 (by rfl) ⟨3703775, by rfl⟩ : syracuseStep 4938367 = 7407551) B7407551
theorem B1465051 : Blo 912577 1465051 := bstep (se 1 (by rfl) ⟨1098788, by rfl⟩ : syracuseStep 1465051 = 2197577) B2197577
theorem B2318503 : Blo 912577 2318503 := bstep (se 1 (by rfl) ⟨1738877, by rfl⟩ : syracuseStep 2318503 = 3477755) B3477755
theorem B11100905 : Blo 912577 11100905 := bstep (se 2 (by rfl) ⟨4162839, by rfl⟩ : syracuseStep 11100905 = 8325679) B8325679
theorem B5858153 : Blo 912577 5858153 := bstep (se 2 (by rfl) ⟨2196807, by rfl⟩ : syracuseStep 5858153 = 4393615) B4393615
theorem B1368953 : Blo 912577 1368953 := bstep (se 2 (by rfl) ⟨513357, by rfl⟩ : syracuseStep 1368953 = 1026715) B1026715
theorem B2057543 : Blo 912577 2057543 := bstep (se 1 (by rfl) ⟨1543157, by rfl⟩ : syracuseStep 2057543 = 3086315) B3086315
theorem B13198787 : Blo 912577 13198787 := bstep (se 1 (by rfl) ⟨9899090, by rfl⟩ : syracuseStep 13198787 = 19798181) B19798181
theorem B5203511 : Blo 912577 5203511 := bstep (se 1 (by rfl) ⟨3902633, by rfl⟩ : syracuseStep 5203511 = 7805267) B7805267
theorem B1369691 : Blo 912577 1369691 := bstep (se 1 (by rfl) ⟨1027268, by rfl⟩ : syracuseStep 1369691 = 2054537) B2054537
theorem B1369883 : Blo 912577 1369883 := bstep (se 1 (by rfl) ⟨1027412, by rfl⟩ : syracuseStep 1369883 = 2054825) B2054825
theorem B4941607 : Blo 912577 4941607 := bstep (se 1 (by rfl) ⟨3706205, by rfl⟩ : syracuseStep 4941607 = 7412411) B7412411
theorem B2058407 : Blo 912577 2058407 := bstep (se 1 (by rfl) ⟨1543805, by rfl⟩ : syracuseStep 2058407 = 3087611) B3087611
theorem B2222729 : Blo 912577 2222729 := bstep (se 2 (by rfl) ⟨833523, by rfl⟩ : syracuseStep 2222729 = 1667047) B1667047
theorem B1370927 : Blo 912577 1370927 := bstep (se 1 (by rfl) ⟨1028195, by rfl⟩ : syracuseStep 1370927 = 2056391) B2056391
theorem B59337683 : Blo 912577 59337683 := bstep (se 1 (by rfl) ⟨44503262, by rfl⟩ : syracuseStep 59337683 = 89006525) B89006525
theorem B1371227 : Blo 912577 1371227 := bstep (se 1 (by rfl) ⟨1028420, by rfl⟩ : syracuseStep 1371227 = 2056841) B2056841
theorem B1371419 : Blo 912577 1371419 := bstep (se 1 (by rfl) ⟨1028564, by rfl⟩ : syracuseStep 1371419 = 2057129) B2057129
theorem B17591681 : Blo 912577 17591681 := bstep (se 2 (by rfl) ⟨6596880, by rfl⟩ : syracuseStep 17591681 = 13193761) B13193761
theorem B1371803 : Blo 912577 1371803 := bstep (se 1 (by rfl) ⟨1028852, by rfl⟩ : syracuseStep 1371803 = 2057705) B2057705
theorem B2060243 : Blo 912577 2060243 := bstep (se 1 (by rfl) ⟨1545182, by rfl⟩ : syracuseStep 2060243 = 3090365) B3090365
theorem B913659 : Blo 912577 913659 := bstep (se 1 (by rfl) ⟨685244, by rfl⟩ : syracuseStep 913659 = 1370489) B1370489
theorem B1372457 : Blo 912577 1372457 := bstep (se 2 (by rfl) ⟨514671, by rfl⟩ : syracuseStep 1372457 = 1029343) B1029343
theorem B913711 : Blo 912577 913711 := bstep (se 1 (by rfl) ⟨685283, by rfl⟩ : syracuseStep 913711 = 1370567) B1370567
theorem B914011 : Blo 912577 914011 := bstep (se 1 (by rfl) ⟨685508, by rfl⟩ : syracuseStep 914011 = 1371017) B1371017
theorem B2061161 : Blo 912577 2061161 := bstep (se 2 (by rfl) ⟨772935, by rfl⟩ : syracuseStep 2061161 = 1545871) B1545871
theorem B914715 : Blo 912577 914715 := bstep (se 1 (by rfl) ⟨686036, by rfl⟩ : syracuseStep 914715 = 1372073) B1372073
theorem B3470633 : Blo 912577 3470633 := bstep (se 2 (by rfl) ⟨1301487, by rfl⟩ : syracuseStep 3470633 = 2602975) B2602975
theorem B2061647 : Blo 912577 2061647 := bstep (se 1 (by rfl) ⟨1546235, by rfl⟩ : syracuseStep 2061647 = 3092471) B3092471
theorem B1373675 : Blo 912577 1373675 := bstep (se 1 (by rfl) ⟨1030256, by rfl⟩ : syracuseStep 1373675 = 2060513) B2060513
theorem B914943 : Blo 912577 914943 := bstep (se 1 (by rfl) ⟨686207, by rfl⟩ : syracuseStep 914943 = 1372415) B1372415
theorem B1373801 : Blo 912577 1373801 := bstep (se 2 (by rfl) ⟨515175, by rfl⟩ : syracuseStep 1373801 = 1030351) B1030351
theorem B915227 : Blo 912577 915227 := bstep (se 1 (by rfl) ⟨686420, by rfl⟩ : syracuseStep 915227 = 1372841) B1372841
theorem B915311 : Blo 912577 915311 := bstep (se 1 (by rfl) ⟨686483, by rfl⟩ : syracuseStep 915311 = 1372967) B1372967
theorem B915367 : Blo 912577 915367 := bstep (se 1 (by rfl) ⟨686525, by rfl⟩ : syracuseStep 915367 = 1373051) B1373051
theorem B23754829 : Blo 912577 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B1374527 : Blo 912577 1374527 := bstep (se 1 (by rfl) ⟨1030895, by rfl⟩ : syracuseStep 1374527 = 2061791) B2061791
theorem B1374815 : Blo 912577 1374815 := bstep (se 1 (by rfl) ⟨1031111, by rfl⟩ : syracuseStep 1374815 = 2062223) B2062223
theorem B916095 : Blo 912577 916095 := bstep (se 1 (by rfl) ⟨687071, by rfl⟩ : syracuseStep 916095 = 1374143) B1374143
theorem B916199 : Blo 912577 916199 := bstep (se 1 (by rfl) ⟨687149, by rfl⟩ : syracuseStep 916199 = 1374299) B1374299
theorem B2063225 : Blo 912577 2063225 := bstep (se 2 (by rfl) ⟨773709, by rfl⟩ : syracuseStep 2063225 = 1547419) B1547419
theorem B916463 : Blo 912577 916463 := bstep (se 1 (by rfl) ⟨687347, by rfl⟩ : syracuseStep 916463 = 1374695) B1374695
theorem B16711201 : Blo 912577 16711201 := bstep (se 2 (by rfl) ⟨6266700, by rfl⟩ : syracuseStep 16711201 = 12533401) B12533401
theorem B1540255 : Blo 912577 1540255 := bstep (se 1 (by rfl) ⟨1155191, by rfl⟩ : syracuseStep 1540255 = 2310383) B2310383
theorem B14057711 : Blo 912577 14057711 := bstep (se 1 (by rfl) ⟨10543283, by rfl⟩ : syracuseStep 14057711 = 21086567) B21086567
theorem B23462135 : Blo 912577 23462135 := bstep (se 1 (by rfl) ⟨17596601, by rfl⟩ : syracuseStep 23462135 = 35193203) B35193203
theorem B3900241 : Blo 912577 3900241 := bstep (se 2 (by rfl) ⟨1462590, by rfl⟩ : syracuseStep 3900241 = 2925181) B2925181
theorem B6588809 : Blo 912577 6588809 := bstep (se 2 (by rfl) ⟨2470803, by rfl⟩ : syracuseStep 6588809 = 4941607) B4941607
theorem B17829827 : Blo 912577 17829827 := bstep (se 1 (by rfl) ⟨13372370, by rfl⟩ : syracuseStep 17829827 = 26744741) B26744741
theorem B3084263 : Blo 912577 3084263 := bstep (se 1 (by rfl) ⟨2313197, by rfl⟩ : syracuseStep 3084263 = 4626395) B4626395
theorem B3084425 : Blo 912577 3084425 := bstep (se 2 (by rfl) ⟨1156659, by rfl⟩ : syracuseStep 3084425 = 2313319) B2313319
theorem B11866601 : Blo 912577 11866601 := bstep (se 2 (by rfl) ⟨4449975, by rfl⟩ : syracuseStep 11866601 = 8899951) B8899951
theorem B3084911 : Blo 912577 3084911 := bstep (se 1 (by rfl) ⟨2313683, by rfl⟩ : syracuseStep 3084911 = 4627367) B4627367
theorem B2200441 : Blo 912577 2200441 := bstep (se 2 (by rfl) ⟨825165, by rfl⟩ : syracuseStep 2200441 = 1650331) B1650331
theorem B3085289 : Blo 912577 3085289 := bstep (se 2 (by rfl) ⟨1156983, by rfl⟩ : syracuseStep 3085289 = 2313967) B2313967
theorem B29300467 : Blo 912577 29300467 := bstep (se 1 (by rfl) ⟨21975350, by rfl⟩ : syracuseStep 29300467 = 43950701) B43950701
theorem B3905435 : Blo 912577 3905435 := bstep (se 1 (by rfl) ⟨2929076, by rfl⟩ : syracuseStep 3905435 = 5858153) B5858153
theorem B1481819 : Blo 912577 1481819 := bstep (se 1 (by rfl) ⟨1111364, by rfl⟩ : syracuseStep 1481819 = 2222729) B2222729
theorem B39558455 : Blo 912577 39558455 := bstep (se 1 (by rfl) ⟨29668841, by rfl⟩ : syracuseStep 39558455 = 59337683) B59337683
theorem B15606431 : Blo 912577 15606431 := bstep (se 1 (by rfl) ⟨11704823, by rfl⟩ : syracuseStep 15606431 = 23409647) B23409647
theorem B7415263 : Blo 912577 7415263 := bstep (se 1 (by rfl) ⟨5561447, by rfl⟩ : syracuseStep 7415263 = 11122895) B11122895
theorem B3090527 : Blo 912577 3090527 := bstep (se 1 (by rfl) ⟨2317895, by rfl⟩ : syracuseStep 3090527 = 4635791) B4635791
theorem B3091337 : Blo 912577 3091337 := bstep (se 2 (by rfl) ⟨1159251, by rfl⟩ : syracuseStep 3091337 = 2318503) B2318503
theorem B1027327 : Blo 912577 1027327 := bstep (se 1 (by rfl) ⟨770495, by rfl⟩ : syracuseStep 1027327 = 1540991) B1540991
theorem B25046891 : Blo 912577 25046891 := bstep (se 1 (by rfl) ⟨18785168, by rfl⟩ : syracuseStep 25046891 = 37570337) B37570337
theorem B15839873 : Blo 912577 15839873 := bstep (se 2 (by rfl) ⟨5939952, by rfl⟩ : syracuseStep 15839873 = 11879905) B11879905
theorem B1028767 : Blo 912577 1028767 := bstep (se 1 (by rfl) ⟨771575, by rfl⟩ : syracuseStep 1028767 = 1543151) B1543151
theorem B26424427 : Blo 912577 26424427 := bstep (se 1 (by rfl) ⟨19818320, by rfl⟩ : syracuseStep 26424427 = 39636641) B39636641
theorem B142718381 : Blo 912577 142718381 := bstep (se 3 (by rfl) ⟨26759696, by rfl⟩ : syracuseStep 142718381 = 53519393) B53519393
theorem B14825339 : Blo 912577 14825339 := bstep (se 1 (by rfl) ⟨11119004, by rfl⟩ : syracuseStep 14825339 = 22238009) B22238009
theorem B1882793 : Blo 912577 1882793 := bstep (se 2 (by rfl) ⟨706047, by rfl⟩ : syracuseStep 1882793 = 1412095) B1412095
theorem B8799191 : Blo 912577 8799191 := bstep (se 1 (by rfl) ⟨6599393, by rfl⟩ : syracuseStep 8799191 = 13198787) B13198787
theorem B1950907 : Blo 912577 1950907 := bstep (se 1 (by rfl) ⟨1463180, by rfl⟩ : syracuseStep 1950907 = 2926361) B2926361
theorem B6932303 : Blo 912577 6932303 := bstep (se 1 (by rfl) ⟨5199227, by rfl⟩ : syracuseStep 6932303 = 10398455) B10398455
theorem B17549855 : Blo 912577 17549855 := bstep (se 1 (by rfl) ⟨13162391, by rfl⟩ : syracuseStep 17549855 = 26324783) B26324783
theorem B31673105 : Blo 912577 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B2313755 : Blo 912577 2313755 := bstep (se 1 (by rfl) ⟨1735316, by rfl⟩ : syracuseStep 2313755 = 3470633) B3470633
theorem B1953401 : Blo 912577 1953401 := bstep (se 2 (by rfl) ⟨732525, by rfl⟩ : syracuseStep 1953401 = 1465051) B1465051
theorem B2608807 : Blo 912577 2608807 := bstep (se 1 (by rfl) ⟨1956605, by rfl⟩ : syracuseStep 2608807 = 3913211) B3913211
theorem B29675585 : Blo 912577 29675585 := bstep (se 2 (by rfl) ⟨11128344, by rfl⟩ : syracuseStep 29675585 = 22256689) B22256689
theorem B15619553 : Blo 912577 15619553 := bstep (se 2 (by rfl) ⟨5857332, by rfl⟩ : syracuseStep 15619553 = 11714665) B11714665
theorem B1301231 : Blo 912577 1301231 := bstep (se 1 (by rfl) ⟨975923, by rfl⟩ : syracuseStep 1301231 = 1951847) B1951847
theorem B14080999 : Blo 912577 14080999 := bstep (se 1 (by rfl) ⟨10560749, by rfl⟩ : syracuseStep 14080999 = 21121499) B21121499
theorem B2644991 : Blo 912577 2644991 := bstep (se 1 (by rfl) ⟨1983743, by rfl⟩ : syracuseStep 2644991 = 3967487) B3967487
theorem B2056571 : Blo 912577 2056571 := bstep (se 1 (by rfl) ⟨1542428, by rfl⟩ : syracuseStep 2056571 = 3084857) B3084857
theorem B1369001 : Blo 912577 1369001 := bstep (se 2 (by rfl) ⟨513375, by rfl⟩ : syracuseStep 1369001 = 1026751) B1026751
theorem B1369055 : Blo 912577 1369055 := bstep (se 1 (by rfl) ⟨1026791, by rfl⟩ : syracuseStep 1369055 = 2053583) B2053583
theorem B2057327 : Blo 912577 2057327 := bstep (se 1 (by rfl) ⟨1542995, by rfl⟩ : syracuseStep 2057327 = 3085991) B3085991
theorem B1369391 : Blo 912577 1369391 := bstep (se 1 (by rfl) ⟨1027043, by rfl⟩ : syracuseStep 1369391 = 2054087) B2054087
theorem B1369415 : Blo 912577 1369415 := bstep (se 1 (by rfl) ⟨1027061, by rfl⟩ : syracuseStep 1369415 = 2054123) B2054123
theorem B3466577 : Blo 912577 3466577 := bstep (se 2 (by rfl) ⟨1299966, by rfl⟩ : syracuseStep 3466577 = 2599933) B2599933
theorem B2058515 : Blo 912577 2058515 := bstep (se 1 (by rfl) ⟨1543886, by rfl⟩ : syracuseStep 2058515 = 3087773) B3087773
theorem B7400603 : Blo 912577 7400603 := bstep (se 1 (by rfl) ⟨5550452, by rfl⟩ : syracuseStep 7400603 = 11100905) B11100905
theorem B912635 : Blo 912577 912635 := bstep (se 1 (by rfl) ⟨684476, by rfl⟩ : syracuseStep 912635 = 1368953) B1368953
theorem B2059631 : Blo 912577 2059631 := bstep (se 1 (by rfl) ⟨1544723, by rfl⟩ : syracuseStep 2059631 = 3089447) B3089447
theorem B1371695 : Blo 912577 1371695 := bstep (se 1 (by rfl) ⟨1028771, by rfl⟩ : syracuseStep 1371695 = 2057543) B2057543
theorem B3469007 : Blo 912577 3469007 := bstep (se 1 (by rfl) ⟨2601755, by rfl⟩ : syracuseStep 3469007 = 5203511) B5203511
theorem B913127 : Blo 912577 913127 := bstep (se 1 (by rfl) ⟨684845, by rfl⟩ : syracuseStep 913127 = 1369691) B1369691
theorem B913255 : Blo 912577 913255 := bstep (se 1 (by rfl) ⟨684941, by rfl⟩ : syracuseStep 913255 = 1369883) B1369883
theorem B1372271 : Blo 912577 1372271 := bstep (se 1 (by rfl) ⟨1029203, by rfl⟩ : syracuseStep 1372271 = 2058407) B2058407
theorem B1732985 : Blo 912577 1732985 := bstep (se 2 (by rfl) ⟨649869, by rfl⟩ : syracuseStep 1732985 = 1299739) B1299739
theorem B913951 : Blo 912577 913951 := bstep (se 1 (by rfl) ⟨685463, by rfl⟩ : syracuseStep 913951 = 1370927) B1370927
theorem B2060927 : Blo 912577 2060927 := bstep (se 1 (by rfl) ⟨1545695, by rfl⟩ : syracuseStep 2060927 = 3091391) B3091391
theorem B914151 : Blo 912577 914151 := bstep (se 1 (by rfl) ⟨685613, by rfl⟩ : syracuseStep 914151 = 1371227) B1371227
theorem B914279 : Blo 912577 914279 := bstep (se 1 (by rfl) ⟨685709, by rfl⟩ : syracuseStep 914279 = 1371419) B1371419
theorem B2061179 : Blo 912577 2061179 := bstep (se 1 (by rfl) ⟨1545884, by rfl⟩ : syracuseStep 2061179 = 3091769) B3091769
theorem B11727787 : Blo 912577 11727787 := bstep (se 1 (by rfl) ⟨8795840, by rfl⟩ : syracuseStep 11727787 = 17591681) B17591681
theorem B914535 : Blo 912577 914535 := bstep (se 1 (by rfl) ⟨685901, by rfl⟩ : syracuseStep 914535 = 1371803) B1371803
theorem B24442033 : Blo 912577 24442033 := bstep (se 2 (by rfl) ⟨9165762, by rfl⟩ : syracuseStep 24442033 = 18331525) B18331525
theorem B1373495 : Blo 912577 1373495 := bstep (se 1 (by rfl) ⟨1030121, by rfl⟩ : syracuseStep 1373495 = 2060243) B2060243
theorem B914971 : Blo 912577 914971 := bstep (se 1 (by rfl) ⟨686228, by rfl⟩ : syracuseStep 914971 = 1372457) B1372457
theorem B1374107 : Blo 912577 1374107 := bstep (se 1 (by rfl) ⟨1030580, by rfl⟩ : syracuseStep 1374107 = 2061161) B2061161
theorem B5863589 : Blo 912577 5863589 := bstep (se 4 (by rfl) ⟨549711, by rfl⟩ : syracuseStep 5863589 = 1099423) B1099423
theorem B6584489 : Blo 912577 6584489 := bstep (se 2 (by rfl) ⟨2469183, by rfl⟩ : syracuseStep 6584489 = 4938367) B4938367
theorem B1374431 : Blo 912577 1374431 := bstep (se 1 (by rfl) ⟨1030823, by rfl⟩ : syracuseStep 1374431 = 2061647) B2061647
theorem B915783 : Blo 912577 915783 := bstep (se 1 (by rfl) ⟨686837, by rfl⟩ : syracuseStep 915783 = 1373675) B1373675
theorem B915867 : Blo 912577 915867 := bstep (se 1 (by rfl) ⟨686900, by rfl⟩ : syracuseStep 915867 = 1373801) B1373801
theorem B916351 : Blo 912577 916351 := bstep (se 1 (by rfl) ⟨687263, by rfl⟩ : syracuseStep 916351 = 1374527) B1374527
theorem B3472409 : Blo 912577 3472409 := bstep (se 2 (by rfl) ⟨1302153, by rfl⟩ : syracuseStep 3472409 = 2604307) B2604307
theorem B916543 : Blo 912577 916543 := bstep (se 1 (by rfl) ⟨687407, by rfl⟩ : syracuseStep 916543 = 1374815) B1374815
theorem B1375483 : Blo 912577 1375483 := bstep (se 1 (by rfl) ⟨1031612, by rfl⟩ : syracuseStep 1375483 = 2063225) B2063225
theorem B22281601 : Blo 912577 22281601 := bstep (se 2 (by rfl) ⟨8355600, by rfl⟩ : syracuseStep 22281601 = 16711201) B16711201
theorem B9371807 : Blo 912577 9371807 := bstep (se 1 (by rfl) ⟨7028855, by rfl⟩ : syracuseStep 9371807 = 14057711) B14057711
theorem B5866127 : Blo 912577 5866127 := bstep (se 1 (by rfl) ⟨4399595, by rfl⟩ : syracuseStep 5866127 = 8799191) B8799191
theorem B4621535 : Blo 912577 4621535 := bstep (se 1 (by rfl) ⟨3466151, by rfl⟩ : syracuseStep 4621535 = 6932303) B6932303
theorem B4392539 : Blo 912577 4392539 := bstep (se 1 (by rfl) ⟨3294404, by rfl⟩ : syracuseStep 4392539 = 6588809) B6588809
theorem B11699903 : Blo 912577 11699903 := bstep (se 1 (by rfl) ⟨8774927, by rfl⟩ : syracuseStep 11699903 = 17549855) B17549855
theorem B1542503 : Blo 912577 1542503 := bstep (se 1 (by rfl) ⟨1156877, by rfl⟩ : syracuseStep 1542503 = 2313755) B2313755
theorem B3478409 : Blo 912577 3478409 := bstep (se 2 (by rfl) ⟨1304403, by rfl⟩ : syracuseStep 3478409 = 2608807) B2608807
theorem B15637049 : Blo 912577 15637049 := bstep (se 2 (by rfl) ⟨5863893, by rfl⟩ : syracuseStep 15637049 = 11727787) B11727787
theorem B35232569 : Blo 912577 35232569 := bstep (se 2 (by rfl) ⟨13212213, by rfl⟩ : syracuseStep 35232569 = 26424427) B26424427
theorem B39067289 : Blo 912577 39067289 := bstep (se 2 (by rfl) ⟨14650233, by rfl⟩ : syracuseStep 39067289 = 29300467) B29300467
theorem B1155323 : Blo 912577 1155323 := bstep (se 1 (by rfl) ⟨866492, by rfl⟩ : syracuseStep 1155323 = 1732985) B1732985
theorem B19734941 : Blo 912577 19734941 := bstep (se 3 (by rfl) ⟨3700301, by rfl⟩ : syracuseStep 19734941 = 7400603) B7400603
theorem B10559915 : Blo 912577 10559915 := bstep (se 1 (by rfl) ⟨7919936, by rfl⟩ : syracuseStep 10559915 = 15839873) B15839873
theorem B3909059 : Blo 912577 3909059 := bstep (se 1 (by rfl) ⟨2931794, by rfl⟩ : syracuseStep 3909059 = 5863589) B5863589
theorem B1255195 : Blo 912577 1255195 := bstep (se 1 (by rfl) ⟨941396, by rfl⟩ : syracuseStep 1255195 = 1882793) B1882793
theorem B15641423 : Blo 912577 15641423 := bstep (se 1 (by rfl) ⟨11731067, by rfl⟩ : syracuseStep 15641423 = 23462135) B23462135
theorem B2601209 : Blo 912577 2601209 := bstep (se 2 (by rfl) ⟨975453, by rfl⟩ : syracuseStep 2601209 = 1950907) B1950907
theorem B21115403 : Blo 912577 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B7911067 : Blo 912577 7911067 := bstep (se 1 (by rfl) ⟨5933300, by rfl⟩ : syracuseStep 7911067 = 11866601) B11866601
theorem B10404287 : Blo 912577 10404287 := bstep (se 1 (by rfl) ⟨7803215, by rfl⟩ : syracuseStep 10404287 = 15606431) B15606431
theorem B2311051 : Blo 912577 2311051 := bstep (se 1 (by rfl) ⟨1733288, by rfl⟩ : syracuseStep 2311051 = 3466577) B3466577
theorem B2933921 : Blo 912577 2933921 := bstep (se 2 (by rfl) ⟨1100220, by rfl⟩ : syracuseStep 2933921 = 2200441) B2200441
theorem B32589377 : Blo 912577 32589377 := bstep (se 2 (by rfl) ⟨12221016, by rfl⟩ : syracuseStep 32589377 = 24442033) B24442033
theorem B2312671 : Blo 912577 2312671 := bstep (se 1 (by rfl) ⟨1734503, by rfl⟩ : syracuseStep 2312671 = 3469007) B3469007
theorem B16697927 : Blo 912577 16697927 := bstep (se 1 (by rfl) ⟨12523445, by rfl⟩ : syracuseStep 16697927 = 25046891) B25046891
theorem B3951517 : Blo 912577 3951517 := bstep (se 3 (by rfl) ⟨740909, by rfl⟩ : syracuseStep 3951517 = 1481819) B1481819
theorem B95145587 : Blo 912577 95145587 := bstep (se 1 (by rfl) ⟨71359190, by rfl⟩ : syracuseStep 95145587 = 142718381) B142718381
theorem B9883559 : Blo 912577 9883559 := bstep (se 1 (by rfl) ⟨7412669, by rfl⟩ : syracuseStep 9883559 = 14825339) B14825339
theorem B29708801 : Blo 912577 29708801 := bstep (se 2 (by rfl) ⟨11140800, by rfl⟩ : syracuseStep 29708801 = 22281601) B22281601
theorem B2314939 : Blo 912577 2314939 := bstep (se 1 (by rfl) ⟨1736204, by rfl⟩ : syracuseStep 2314939 = 3472409) B3472409
theorem B2053673 : Blo 912577 2053673 := bstep (se 2 (by rfl) ⟨770127, by rfl⟩ : syracuseStep 2053673 = 1540255) B1540255
theorem B5200321 : Blo 912577 5200321 := bstep (se 2 (by rfl) ⟨1950120, by rfl⟩ : syracuseStep 5200321 = 3900241) B3900241
theorem B9887017 : Blo 912577 9887017 := bstep (se 2 (by rfl) ⟨3707631, by rfl⟩ : syracuseStep 9887017 = 7415263) B7415263
theorem B11886551 : Blo 912577 11886551 := bstep (se 1 (by rfl) ⟨8914913, by rfl⟩ : syracuseStep 11886551 = 17829827) B17829827
theorem B2056175 : Blo 912577 2056175 := bstep (se 1 (by rfl) ⟨1542131, by rfl⟩ : syracuseStep 2056175 = 3084263) B3084263
theorem B19783723 : Blo 912577 19783723 := bstep (se 1 (by rfl) ⟨14837792, by rfl⟩ : syracuseStep 19783723 = 29675585) B29675585
theorem B2056283 : Blo 912577 2056283 := bstep (se 1 (by rfl) ⟨1542212, by rfl⟩ : syracuseStep 2056283 = 3084425) B3084425
theorem B2056607 : Blo 912577 2056607 := bstep (se 1 (by rfl) ⟨1542455, by rfl⟩ : syracuseStep 2056607 = 3084911) B3084911
theorem B2056859 : Blo 912577 2056859 := bstep (se 1 (by rfl) ⟨1542644, by rfl⟩ : syracuseStep 2056859 = 3085289) B3085289
theorem B10413035 : Blo 912577 10413035 := bstep (se 1 (by rfl) ⟨7809776, by rfl⟩ : syracuseStep 10413035 = 15619553) B15619553
theorem B1369769 : Blo 912577 1369769 := bstep (se 2 (by rfl) ⟨513663, by rfl⟩ : syracuseStep 1369769 = 1027327) B1027327
theorem B1763327 : Blo 912577 1763327 := bstep (se 1 (by rfl) ⟨1322495, by rfl⟩ : syracuseStep 1763327 = 2644991) B2644991
theorem B26372303 : Blo 912577 26372303 := bstep (se 1 (by rfl) ⟨19779227, by rfl⟩ : syracuseStep 26372303 = 39558455) B39558455
theorem B10414493 : Blo 912577 10414493 := bstep (se 3 (by rfl) ⟨1952717, by rfl⟩ : syracuseStep 10414493 = 3905435) B3905435
theorem B1371047 : Blo 912577 1371047 := bstep (se 1 (by rfl) ⟨1028285, by rfl⟩ : syracuseStep 1371047 = 2056571) B2056571
theorem B912667 : Blo 912577 912667 := bstep (se 1 (by rfl) ⟨684500, by rfl⟩ : syracuseStep 912667 = 1369001) B1369001
theorem B912703 : Blo 912577 912703 := bstep (se 1 (by rfl) ⟨684527, by rfl⟩ : syracuseStep 912703 = 1369055) B1369055
theorem B1371551 : Blo 912577 1371551 := bstep (se 1 (by rfl) ⟨1028663, by rfl⟩ : syracuseStep 1371551 = 2057327) B2057327
theorem B912927 : Blo 912577 912927 := bstep (se 1 (by rfl) ⟨684695, by rfl⟩ : syracuseStep 912927 = 1369391) B1369391
theorem B1371689 : Blo 912577 1371689 := bstep (se 2 (by rfl) ⟨514383, by rfl⟩ : syracuseStep 1371689 = 1028767) B1028767
theorem B912943 : Blo 912577 912943 := bstep (se 1 (by rfl) ⟨684707, by rfl⟩ : syracuseStep 912943 = 1369415) B1369415
theorem B2060351 : Blo 912577 2060351 := bstep (se 1 (by rfl) ⟨1545263, by rfl⟩ : syracuseStep 2060351 = 3090527) B3090527
theorem B1372343 : Blo 912577 1372343 := bstep (se 1 (by rfl) ⟨1029257, by rfl⟩ : syracuseStep 1372343 = 2058515) B2058515
theorem B2060891 : Blo 912577 2060891 := bstep (se 1 (by rfl) ⟨1545668, by rfl⟩ : syracuseStep 2060891 = 3091337) B3091337
theorem B3469949 : Blo 912577 3469949 := bstep (se 3 (by rfl) ⟨650615, by rfl⟩ : syracuseStep 3469949 = 1301231) B1301231
theorem B1373087 : Blo 912577 1373087 := bstep (se 1 (by rfl) ⟨1029815, by rfl⟩ : syracuseStep 1373087 = 2059631) B2059631
theorem B914463 : Blo 912577 914463 := bstep (se 1 (by rfl) ⟨685847, by rfl⟩ : syracuseStep 914463 = 1371695) B1371695
theorem B914847 : Blo 912577 914847 := bstep (se 1 (by rfl) ⟨686135, by rfl⟩ : syracuseStep 914847 = 1372271) B1372271
theorem B1373951 : Blo 912577 1373951 := bstep (se 1 (by rfl) ⟨1030463, by rfl⟩ : syracuseStep 1373951 = 2060927) B2060927
theorem B1374119 : Blo 912577 1374119 := bstep (se 1 (by rfl) ⟨1030589, by rfl⟩ : syracuseStep 1374119 = 2061179) B2061179
theorem B915663 : Blo 912577 915663 := bstep (se 1 (by rfl) ⟨686747, by rfl⟩ : syracuseStep 915663 = 1373495) B1373495
theorem B916071 : Blo 912577 916071 := bstep (se 1 (by rfl) ⟨687053, by rfl⟩ : syracuseStep 916071 = 1374107) B1374107
theorem B18774665 : Blo 912577 18774665 := bstep (se 2 (by rfl) ⟨7040499, by rfl⟩ : syracuseStep 18774665 = 14080999) B14080999
theorem B4389659 : Blo 912577 4389659 := bstep (se 1 (by rfl) ⟨3292244, by rfl⟩ : syracuseStep 4389659 = 6584489) B6584489
theorem B916287 : Blo 912577 916287 := bstep (se 1 (by rfl) ⟨687215, by rfl⟩ : syracuseStep 916287 = 1374431) B1374431
theorem B5209069 : Blo 912577 5209069 := bstep (se 3 (by rfl) ⟨976700, by rfl⟩ : syracuseStep 5209069 = 1953401) B1953401
theorem B1833977 : Blo 912577 1833977 := bstep (se 2 (by rfl) ⟨687741, by rfl⟩ : syracuseStep 1833977 = 1375483) B1375483
theorem B26378297 : Blo 912577 26378297 := bstep (se 2 (by rfl) ⟨9891861, by rfl⟩ : syracuseStep 26378297 = 19783723) B19783723
theorem B3080861 : Blo 912577 3080861 := bstep (se 3 (by rfl) ⟨577661, by rfl⟩ : syracuseStep 3080861 = 1155323) B1155323
theorem B3081023 : Blo 912577 3081023 := bstep (se 1 (by rfl) ⟨2310767, by rfl⟩ : syracuseStep 3081023 = 4621535) B4621535
theorem B21726251 : Blo 912577 21726251 := bstep (se 1 (by rfl) ⟨16294688, by rfl⟩ : syracuseStep 21726251 = 32589377) B32589377
theorem B7799935 : Blo 912577 7799935 := bstep (se 1 (by rfl) ⟨5849951, by rfl⟩ : syracuseStep 7799935 = 11699903) B11699903
theorem B3081401 : Blo 912577 3081401 := bstep (se 2 (by rfl) ⟨1155525, by rfl⟩ : syracuseStep 3081401 = 2311051) B2311051
theorem B6589039 : Blo 912577 6589039 := bstep (se 1 (by rfl) ⟨4941779, by rfl⟩ : syracuseStep 6589039 = 9883559) B9883559
theorem B3083561 : Blo 912577 3083561 := bstep (se 2 (by rfl) ⟨1156335, by rfl⟩ : syracuseStep 3083561 = 2312671) B2312671
theorem B10424699 : Blo 912577 10424699 := bstep (se 1 (by rfl) ⟨7818524, by rfl⟩ : syracuseStep 10424699 = 15637049) B15637049
theorem B3086585 : Blo 912577 3086585 := bstep (se 2 (by rfl) ⟨1157469, by rfl⟩ : syracuseStep 3086585 = 2314939) B2314939
theorem B10427615 : Blo 912577 10427615 := bstep (se 1 (by rfl) ⟨7820711, by rfl⟩ : syracuseStep 10427615 = 15641423) B15641423
theorem B6694373 : Blo 912577 6694373 := bstep (se 4 (by rfl) ⟨627597, by rfl⟩ : syracuseStep 6694373 = 1255195) B1255195
theorem B13182689 : Blo 912577 13182689 := bstep (se 2 (by rfl) ⟨4943508, by rfl⟩ : syracuseStep 13182689 = 9887017) B9887017
theorem B2926439 : Blo 912577 2926439 := bstep (se 1 (by rfl) ⟨2194829, by rfl⟩ : syracuseStep 2926439 = 4389659) B4389659
theorem B1222651 : Blo 912577 1222651 := bstep (se 1 (by rfl) ⟨916988, by rfl⟩ : syracuseStep 1222651 = 1833977) B1833977
theorem B3910751 : Blo 912577 3910751 := bstep (se 1 (by rfl) ⟨2933063, by rfl⟩ : syracuseStep 3910751 = 5866127) B5866127
theorem B2928359 : Blo 912577 2928359 := bstep (se 1 (by rfl) ⟨2196269, by rfl⟩ : syracuseStep 2928359 = 4392539) B4392539
theorem B1028335 : Blo 912577 1028335 := bstep (se 1 (by rfl) ⟨771251, by rfl⟩ : syracuseStep 1028335 = 1542503) B1542503
theorem B19805867 : Blo 912577 19805867 := bstep (se 1 (by rfl) ⟨14854400, by rfl⟩ : syracuseStep 19805867 = 29708801) B29708801
theorem B4702205 : Blo 912577 4702205 := bstep (se 3 (by rfl) ⟨881663, by rfl⟩ : syracuseStep 4702205 = 1763327) B1763327
theorem B13156627 : Blo 912577 13156627 := bstep (se 1 (by rfl) ⟨9867470, by rfl⟩ : syracuseStep 13156627 = 19734941) B19734941
theorem B2606039 : Blo 912577 2606039 := bstep (se 1 (by rfl) ⟨1954529, by rfl⟩ : syracuseStep 2606039 = 3909059) B3909059
theorem B17581535 : Blo 912577 17581535 := bstep (se 1 (by rfl) ⟨13186151, by rfl⟩ : syracuseStep 17581535 = 26372303) B26372303
theorem B14076935 : Blo 912577 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B2313299 : Blo 912577 2313299 := bstep (se 1 (by rfl) ⟨1734974, by rfl⟩ : syracuseStep 2313299 = 3469949) B3469949
theorem B6933761 : Blo 912577 6933761 := bstep (se 2 (by rfl) ⟨2600160, by rfl⟩ : syracuseStep 6933761 = 5200321) B5200321
theorem B6247871 : Blo 912577 6247871 := bstep (se 1 (by rfl) ⟨4685903, by rfl⟩ : syracuseStep 6247871 = 9371807) B9371807
theorem B6936191 : Blo 912577 6936191 := bstep (se 1 (by rfl) ⟨5202143, by rfl⟩ : syracuseStep 6936191 = 10404287) B10404287
theorem B11131951 : Blo 912577 11131951 := bstep (se 1 (by rfl) ⟨8348963, by rfl⟩ : syracuseStep 11131951 = 16697927) B16697927
theorem B63430391 : Blo 912577 63430391 := bstep (se 1 (by rfl) ⟨47572793, by rfl⟩ : syracuseStep 63430391 = 95145587) B95145587
theorem B7823789 : Blo 912577 7823789 := bstep (se 3 (by rfl) ⟨1466960, by rfl⟩ : syracuseStep 7823789 = 2933921) B2933921
theorem B2318939 : Blo 912577 2318939 := bstep (se 1 (by rfl) ⟨1739204, by rfl⟩ : syracuseStep 2318939 = 3478409) B3478409
theorem B1369115 : Blo 912577 1369115 := bstep (se 1 (by rfl) ⟨1026836, by rfl⟩ : syracuseStep 1369115 = 2053673) B2053673
theorem B5268689 : Blo 912577 5268689 := bstep (se 2 (by rfl) ⟨1975758, by rfl⟩ : syracuseStep 5268689 = 3951517) B3951517
theorem B23488379 : Blo 912577 23488379 := bstep (se 1 (by rfl) ⟨17616284, by rfl⟩ : syracuseStep 23488379 = 35232569) B35232569
theorem B26044859 : Blo 912577 26044859 := bstep (se 1 (by rfl) ⟨19533644, by rfl⟩ : syracuseStep 26044859 = 39067289) B39067289
theorem B7924367 : Blo 912577 7924367 := bstep (se 1 (by rfl) ⟨5943275, by rfl⟩ : syracuseStep 7924367 = 11886551) B11886551
theorem B1370783 : Blo 912577 1370783 := bstep (se 1 (by rfl) ⟨1028087, by rfl⟩ : syracuseStep 1370783 = 2056175) B2056175
theorem B1370855 : Blo 912577 1370855 := bstep (se 1 (by rfl) ⟨1028141, by rfl⟩ : syracuseStep 1370855 = 2056283) B2056283
theorem B1371071 : Blo 912577 1371071 := bstep (se 1 (by rfl) ⟨1028303, by rfl⟩ : syracuseStep 1371071 = 2056607) B2056607
theorem B7039943 : Blo 912577 7039943 := bstep (se 1 (by rfl) ⟨5279957, by rfl⟩ : syracuseStep 7039943 = 10559915) B10559915
theorem B1371239 : Blo 912577 1371239 := bstep (se 1 (by rfl) ⟨1028429, by rfl⟩ : syracuseStep 1371239 = 2056859) B2056859
theorem B6942023 : Blo 912577 6942023 := bstep (se 1 (by rfl) ⟨5206517, by rfl⟩ : syracuseStep 6942023 = 10413035) B10413035
theorem B913179 : Blo 912577 913179 := bstep (se 1 (by rfl) ⟨684884, by rfl⟩ : syracuseStep 913179 = 1369769) B1369769
theorem B6942995 : Blo 912577 6942995 := bstep (se 1 (by rfl) ⟨5207246, by rfl⟩ : syracuseStep 6942995 = 10414493) B10414493
theorem B914031 : Blo 912577 914031 := bstep (se 1 (by rfl) ⟨685523, by rfl⟩ : syracuseStep 914031 = 1371047) B1371047
theorem B10548089 : Blo 912577 10548089 := bstep (se 2 (by rfl) ⟨3955533, by rfl⟩ : syracuseStep 10548089 = 7911067) B7911067
theorem B914367 : Blo 912577 914367 := bstep (se 1 (by rfl) ⟨685775, by rfl⟩ : syracuseStep 914367 = 1371551) B1371551
theorem B914459 : Blo 912577 914459 := bstep (se 1 (by rfl) ⟨685844, by rfl⟩ : syracuseStep 914459 = 1371689) B1371689
theorem B1373567 : Blo 912577 1373567 := bstep (se 1 (by rfl) ⟨1030175, by rfl⟩ : syracuseStep 1373567 = 2060351) B2060351
theorem B914895 : Blo 912577 914895 := bstep (se 1 (by rfl) ⟨686171, by rfl⟩ : syracuseStep 914895 = 1372343) B1372343
theorem B1734139 : Blo 912577 1734139 := bstep (se 1 (by rfl) ⟨1300604, by rfl⟩ : syracuseStep 1734139 = 2601209) B2601209
theorem B1373927 : Blo 912577 1373927 := bstep (se 1 (by rfl) ⟨1030445, by rfl⟩ : syracuseStep 1373927 = 2060891) B2060891
theorem B915391 : Blo 912577 915391 := bstep (se 1 (by rfl) ⟨686543, by rfl⟩ : syracuseStep 915391 = 1373087) B1373087
theorem B915967 : Blo 912577 915967 := bstep (se 1 (by rfl) ⟨686975, by rfl⟩ : syracuseStep 915967 = 1373951) B1373951
theorem B916079 : Blo 912577 916079 := bstep (se 1 (by rfl) ⟨687059, by rfl⟩ : syracuseStep 916079 = 1374119) B1374119
theorem B6945425 : Blo 912577 6945425 := bstep (se 2 (by rfl) ⟨2604534, by rfl⟩ : syracuseStep 6945425 = 5209069) B5209069
theorem B12516443 : Blo 912577 12516443 := bstep (se 1 (by rfl) ⟨9387332, by rfl⟩ : syracuseStep 12516443 = 18774665) B18774665
theorem B1737359 : Blo 912577 1737359 := bstep (se 1 (by rfl) ⟨1303019, by rfl⟩ : syracuseStep 1737359 = 2606039) B2606039
theorem B14484167 : Blo 912577 14484167 := bstep (se 1 (by rfl) ⟨10863125, by rfl⟩ : syracuseStep 14484167 = 21726251) B21726251
theorem B1542199 : Blo 912577 1542199 := bstep (se 1 (by rfl) ⟨1156649, by rfl⟩ : syracuseStep 1542199 = 2313299) B2313299
theorem B4622507 : Blo 912577 4622507 := bstep (se 1 (by rfl) ⟨3466880, by rfl⟩ : syracuseStep 4622507 = 6933761) B6933761
theorem B6949799 : Blo 912577 6949799 := bstep (se 1 (by rfl) ⟨5212349, by rfl⟩ : syracuseStep 6949799 = 10424699) B10424699
theorem B8785385 : Blo 912577 8785385 := bstep (se 2 (by rfl) ⟨3294519, by rfl⟩ : syracuseStep 8785385 = 6589039) B6589039
theorem B4165247 : Blo 912577 4165247 := bstep (se 1 (by rfl) ⟨3123935, by rfl⟩ : syracuseStep 4165247 = 6247871) B6247871
theorem B4624127 : Blo 912577 4624127 := bstep (se 1 (by rfl) ⟨3468095, by rfl⟩ : syracuseStep 4624127 = 6936191) B6936191
theorem B6951743 : Blo 912577 6951743 := bstep (se 1 (by rfl) ⟨5213807, by rfl⟩ : syracuseStep 6951743 = 10427615) B10427615
theorem B5215859 : Blo 912577 5215859 := bstep (se 1 (by rfl) ⟨3911894, by rfl⟩ : syracuseStep 5215859 = 7823789) B7823789
theorem B1545959 : Blo 912577 1545959 := bstep (se 1 (by rfl) ⟨1159469, by rfl⟩ : syracuseStep 1545959 = 2318939) B2318939
theorem B3512459 : Blo 912577 3512459 := bstep (se 1 (by rfl) ⟨2634344, by rfl⟩ : syracuseStep 3512459 = 5268689) B5268689
theorem B5282911 : Blo 912577 5282911 := bstep (se 1 (by rfl) ⟨3962183, by rfl⟩ : syracuseStep 5282911 = 7924367) B7924367
theorem B4693295 : Blo 912577 4693295 := bstep (se 1 (by rfl) ⟨3519971, by rfl⟩ : syracuseStep 4693295 = 7039943) B7039943
theorem B4628015 : Blo 912577 4628015 := bstep (se 1 (by rfl) ⟨3471011, by rfl⟩ : syracuseStep 4628015 = 6942023) B6942023
theorem B4628663 : Blo 912577 4628663 := bstep (se 1 (by rfl) ⟨3471497, by rfl⟩ : syracuseStep 4628663 = 6942995) B6942995
theorem B4630283 : Blo 912577 4630283 := bstep (se 1 (by rfl) ⟨3472712, by rfl⟩ : syracuseStep 4630283 = 6945425) B6945425
theorem B7808957 : Blo 912577 7808957 := bstep (se 3 (by rfl) ⟨1464179, by rfl⟩ : syracuseStep 7808957 = 2928359) B2928359
theorem B17542169 : Blo 912577 17542169 := bstep (se 2 (by rfl) ⟨6578313, by rfl⟩ : syracuseStep 17542169 = 13156627) B13156627
theorem B10399913 : Blo 912577 10399913 := bstep (se 2 (by rfl) ⟨3899967, by rfl⟩ : syracuseStep 10399913 = 7799935) B7799935
theorem B9384623 : Blo 912577 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B42286927 : Blo 912577 42286927 := bstep (se 1 (by rfl) ⟨31715195, by rfl⟩ : syracuseStep 42286927 = 63430391) B63430391
theorem B69452957 : Blo 912577 69452957 := bstep (se 3 (by rfl) ⟨13022429, by rfl⟩ : syracuseStep 69452957 = 26044859) B26044859
theorem B1950959 : Blo 912577 1950959 := bstep (se 1 (by rfl) ⟨1463219, by rfl⟩ : syracuseStep 1950959 = 2926439) B2926439
theorem B2312185 : Blo 912577 2312185 := bstep (se 2 (by rfl) ⟨867069, by rfl⟩ : syracuseStep 2312185 = 1734139) B1734139
theorem B2607167 : Blo 912577 2607167 := bstep (se 1 (by rfl) ⟨1955375, by rfl⟩ : syracuseStep 2607167 = 3910751) B3910751
theorem B7032059 : Blo 912577 7032059 := bstep (se 1 (by rfl) ⟨5274044, by rfl⟩ : syracuseStep 7032059 = 10548089) B10548089
theorem B8344295 : Blo 912577 8344295 := bstep (se 1 (by rfl) ⟨6258221, by rfl⟩ : syracuseStep 8344295 = 12516443) B12516443
theorem B3134803 : Blo 912577 3134803 := bstep (se 1 (by rfl) ⟨2351102, by rfl⟩ : syracuseStep 3134803 = 4702205) B4702205
theorem B17585531 : Blo 912577 17585531 := bstep (se 1 (by rfl) ⟨13189148, by rfl⟩ : syracuseStep 17585531 = 26378297) B26378297
theorem B2053907 : Blo 912577 2053907 := bstep (se 1 (by rfl) ⟨1540430, by rfl⟩ : syracuseStep 2053907 = 3080861) B3080861
theorem B2054015 : Blo 912577 2054015 := bstep (se 1 (by rfl) ⟨1540511, by rfl⟩ : syracuseStep 2054015 = 3081023) B3081023
theorem B2054267 : Blo 912577 2054267 := bstep (se 1 (by rfl) ⟨1540700, by rfl⟩ : syracuseStep 2054267 = 3081401) B3081401
theorem B11721023 : Blo 912577 11721023 := bstep (se 1 (by rfl) ⟨8790767, by rfl⟩ : syracuseStep 11721023 = 17581535) B17581535
theorem B2055707 : Blo 912577 2055707 := bstep (se 1 (by rfl) ⟨1541780, by rfl⟩ : syracuseStep 2055707 = 3083561) B3083561
theorem B1630201 : Blo 912577 1630201 := bstep (se 2 (by rfl) ⟨611325, by rfl⟩ : syracuseStep 1630201 = 1222651) B1222651
theorem B17851661 : Blo 912577 17851661 := bstep (se 3 (by rfl) ⟨3347186, by rfl⟩ : syracuseStep 17851661 = 6694373) B6694373
theorem B2057723 : Blo 912577 2057723 := bstep (se 1 (by rfl) ⟨1543292, by rfl⟩ : syracuseStep 2057723 = 3086585) B3086585
theorem B35153837 : Blo 912577 35153837 := bstep (se 3 (by rfl) ⟨6591344, by rfl⟩ : syracuseStep 35153837 = 13182689) B13182689
theorem B1371113 : Blo 912577 1371113 := bstep (se 2 (by rfl) ⟨514167, by rfl⟩ : syracuseStep 1371113 = 1028335) B1028335
theorem B912743 : Blo 912577 912743 := bstep (se 1 (by rfl) ⟨684557, by rfl⟩ : syracuseStep 912743 = 1369115) B1369115
theorem B15658919 : Blo 912577 15658919 := bstep (se 1 (by rfl) ⟨11744189, by rfl⟩ : syracuseStep 15658919 = 23488379) B23488379
theorem B913855 : Blo 912577 913855 := bstep (se 1 (by rfl) ⟨685391, by rfl⟩ : syracuseStep 913855 = 1370783) B1370783
theorem B913903 : Blo 912577 913903 := bstep (se 1 (by rfl) ⟨685427, by rfl⟩ : syracuseStep 913903 = 1370855) B1370855
theorem B914047 : Blo 912577 914047 := bstep (se 1 (by rfl) ⟨685535, by rfl⟩ : syracuseStep 914047 = 1371071) B1371071
theorem B914159 : Blo 912577 914159 := bstep (se 1 (by rfl) ⟨685619, by rfl⟩ : syracuseStep 914159 = 1371239) B1371239
theorem B915711 : Blo 912577 915711 := bstep (se 1 (by rfl) ⟨686783, by rfl⟩ : syracuseStep 915711 = 1373567) B1373567
theorem B13203911 : Blo 912577 13203911 := bstep (se 1 (by rfl) ⟨9902933, by rfl⟩ : syracuseStep 13203911 = 19805867) B19805867
theorem B915951 : Blo 912577 915951 := bstep (se 1 (by rfl) ⟨686963, by rfl⟩ : syracuseStep 915951 = 1373927) B1373927
theorem B14842601 : Blo 912577 14842601 := bstep (se 2 (by rfl) ⟨5565975, by rfl⟩ : syracuseStep 14842601 = 11131951) B11131951
theorem B46301971 : Blo 912577 46301971 := bstep (se 1 (by rfl) ⟨34726478, by rfl⟩ : syracuseStep 46301971 = 69452957) B69452957
theorem B1738111 : Blo 912577 1738111 := bstep (se 1 (by rfl) ⟨1303583, by rfl⟩ : syracuseStep 1738111 = 2607167) B2607167
theorem B3081671 : Blo 912577 3081671 := bstep (se 1 (by rfl) ⟨2311253, by rfl⟩ : syracuseStep 3081671 = 4622507) B4622507
theorem B4688039 : Blo 912577 4688039 := bstep (se 1 (by rfl) ⟨3516029, by rfl⟩ : syracuseStep 4688039 = 7032059) B7032059
theorem B3082751 : Blo 912577 3082751 := bstep (se 1 (by rfl) ⟨2312063, by rfl⟩ : syracuseStep 3082751 = 4624127) B4624127
theorem B3082913 : Blo 912577 3082913 := bstep (se 2 (by rfl) ⟨1156092, by rfl⟩ : syracuseStep 3082913 = 2312185) B2312185
theorem B3477239 : Blo 912577 3477239 := bstep (se 1 (by rfl) ⟨2607929, by rfl⟩ : syracuseStep 3477239 = 5215859) B5215859
theorem B3085343 : Blo 912577 3085343 := bstep (se 1 (by rfl) ⟨2314007, by rfl⟩ : syracuseStep 3085343 = 4628015) B4628015
theorem B3085775 : Blo 912577 3085775 := bstep (se 1 (by rfl) ⟨2314331, by rfl⟩ : syracuseStep 3085775 = 4628663) B4628663
theorem B11901107 : Blo 912577 11901107 := bstep (se 1 (by rfl) ⟨8925830, by rfl⟩ : syracuseStep 11901107 = 17851661) B17851661
theorem B3086855 : Blo 912577 3086855 := bstep (se 1 (by rfl) ⟨2315141, by rfl⟩ : syracuseStep 3086855 = 4630283) B4630283
theorem B23435891 : Blo 912577 23435891 := bstep (se 1 (by rfl) ⟨17576918, by rfl⟩ : syracuseStep 23435891 = 35153837) B35153837
theorem B2173601 : Blo 912577 2173601 := bstep (se 2 (by rfl) ⟨815100, by rfl⟩ : syracuseStep 2173601 = 1630201) B1630201
theorem B1158239 : Blo 912577 1158239 := bstep (se 1 (by rfl) ⟨868679, by rfl⟩ : syracuseStep 1158239 = 1737359) B1737359
theorem B4633199 : Blo 912577 4633199 := bstep (se 1 (by rfl) ⟨3474899, by rfl⟩ : syracuseStep 4633199 = 6949799) B6949799
theorem B4634495 : Blo 912577 4634495 := bstep (se 1 (by rfl) ⟨3475871, by rfl⟩ : syracuseStep 4634495 = 6951743) B6951743
theorem B1030639 : Blo 912577 1030639 := bstep (se 1 (by rfl) ⟨772979, by rfl⟩ : syracuseStep 1030639 = 1545959) B1545959
theorem B2341639 : Blo 912577 2341639 := bstep (se 1 (by rfl) ⟨1756229, by rfl⟩ : syracuseStep 2341639 = 3512459) B3512459
theorem B7814015 : Blo 912577 7814015 := bstep (se 1 (by rfl) ⟨5860511, by rfl⟩ : syracuseStep 7814015 = 11721023) B11721023
theorem B3128863 : Blo 912577 3128863 := bstep (se 1 (by rfl) ⟨2346647, by rfl⟩ : syracuseStep 3128863 = 4693295) B4693295
theorem B4179737 : Blo 912577 4179737 := bstep (se 2 (by rfl) ⟨1567401, by rfl⟩ : syracuseStep 4179737 = 3134803) B3134803
theorem B10439279 : Blo 912577 10439279 := bstep (se 1 (by rfl) ⟨7829459, by rfl⟩ : syracuseStep 10439279 = 15658919) B15658919
theorem B6933275 : Blo 912577 6933275 := bstep (se 1 (by rfl) ⟨5199956, by rfl⟩ : syracuseStep 6933275 = 10399913) B10399913
theorem B8802607 : Blo 912577 8802607 := bstep (se 1 (by rfl) ⟨6601955, by rfl⟩ : syracuseStep 8802607 = 13203911) B13203911
theorem B56382569 : Blo 912577 56382569 := bstep (se 2 (by rfl) ⟨21143463, by rfl⟩ : syracuseStep 56382569 = 42286927) B42286927
theorem B9656111 : Blo 912577 9656111 := bstep (se 1 (by rfl) ⟨7242083, by rfl⟩ : syracuseStep 9656111 = 14484167) B14484167
theorem B1300639 : Blo 912577 1300639 := bstep (se 1 (by rfl) ⟨975479, by rfl⟩ : syracuseStep 1300639 = 1950959) B1950959
theorem B5856923 : Blo 912577 5856923 := bstep (se 1 (by rfl) ⟨4392692, by rfl⟩ : syracuseStep 5856923 = 8785385) B8785385
theorem B2056265 : Blo 912577 2056265 := bstep (se 2 (by rfl) ⟨771099, by rfl⟩ : syracuseStep 2056265 = 1542199) B1542199
theorem B5562863 : Blo 912577 5562863 := bstep (se 1 (by rfl) ⟨4172147, by rfl⟩ : syracuseStep 5562863 = 8344295) B8344295
theorem B11723687 : Blo 912577 11723687 := bstep (se 1 (by rfl) ⟨8792765, by rfl⟩ : syracuseStep 11723687 = 17585531) B17585531
theorem B1369271 : Blo 912577 1369271 := bstep (se 1 (by rfl) ⟨1026953, by rfl⟩ : syracuseStep 1369271 = 2053907) B2053907
theorem B1369343 : Blo 912577 1369343 := bstep (se 1 (by rfl) ⟨1027007, by rfl⟩ : syracuseStep 1369343 = 2054015) B2054015
theorem B1369511 : Blo 912577 1369511 := bstep (se 1 (by rfl) ⟨1027133, by rfl⟩ : syracuseStep 1369511 = 2054267) B2054267
theorem B1370471 : Blo 912577 1370471 := bstep (se 1 (by rfl) ⟨1027853, by rfl⟩ : syracuseStep 1370471 = 2055707) B2055707
theorem B28175525 : Blo 912577 28175525 := bstep (se 4 (by rfl) ⟨2641455, by rfl⟩ : syracuseStep 28175525 = 5282911) B5282911
theorem B1371815 : Blo 912577 1371815 := bstep (se 1 (by rfl) ⟨1028861, by rfl⟩ : syracuseStep 1371815 = 2057723) B2057723
theorem B5205971 : Blo 912577 5205971 := bstep (se 1 (by rfl) ⟨3904478, by rfl⟩ : syracuseStep 5205971 = 7808957) B7808957
theorem B914075 : Blo 912577 914075 := bstep (se 1 (by rfl) ⟨685556, by rfl⟩ : syracuseStep 914075 = 1371113) B1371113
theorem B11694779 : Blo 912577 11694779 := bstep (se 1 (by rfl) ⟨8771084, by rfl⟩ : syracuseStep 11694779 = 17542169) B17542169
theorem B6256415 : Blo 912577 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B11107325 : Blo 912577 11107325 := bstep (se 3 (by rfl) ⟨2082623, by rfl⟩ : syracuseStep 11107325 = 4165247) B4165247
theorem B9895067 : Blo 912577 9895067 := bstep (se 1 (by rfl) ⟨7421300, by rfl⟩ : syracuseStep 9895067 = 14842601) B14842601
theorem B61735961 : Blo 912577 61735961 := bstep (se 2 (by rfl) ⟨23150985, by rfl⟩ : syracuseStep 61735961 = 46301971) B46301971
theorem B2786491 : Blo 912577 2786491 := bstep (se 1 (by rfl) ⟨2089868, by rfl⟩ : syracuseStep 2786491 = 4179737) B4179737
theorem B4622183 : Blo 912577 4622183 := bstep (se 1 (by rfl) ⟨3466637, by rfl⟩ : syracuseStep 4622183 = 6933275) B6933275
theorem B37588379 : Blo 912577 37588379 := bstep (se 1 (by rfl) ⟨28191284, by rfl⟩ : syracuseStep 37588379 = 56382569) B56382569
theorem B12488741 : Blo 912577 12488741 := bstep (se 4 (by rfl) ⟨1170819, by rfl⟩ : syracuseStep 12488741 = 2341639) B2341639
theorem B7934071 : Blo 912577 7934071 := bstep (se 1 (by rfl) ⟨5950553, by rfl⟩ : syracuseStep 7934071 = 11901107) B11901107
theorem B3904615 : Blo 912577 3904615 := bstep (se 1 (by rfl) ⟨2928461, by rfl⟩ : syracuseStep 3904615 = 5856923) B5856923
theorem B3708575 : Blo 912577 3708575 := bstep (se 1 (by rfl) ⟨2781431, by rfl⟩ : syracuseStep 3708575 = 5562863) B5562863
theorem B11736809 : Blo 912577 11736809 := bstep (se 2 (by rfl) ⟨4401303, by rfl⟩ : syracuseStep 11736809 = 8802607) B8802607
theorem B18783683 : Blo 912577 18783683 := bstep (se 1 (by rfl) ⟨14087762, by rfl⟩ : syracuseStep 18783683 = 28175525) B28175525
theorem B3088637 : Blo 912577 3088637 := bstep (se 3 (by rfl) ⟨579119, by rfl⟩ : syracuseStep 3088637 = 1158239) B1158239
theorem B3088799 : Blo 912577 3088799 := bstep (se 1 (by rfl) ⟨2316599, by rfl⟩ : syracuseStep 3088799 = 4633199) B4633199
theorem B4170943 : Blo 912577 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B3089663 : Blo 912577 3089663 := bstep (se 1 (by rfl) ⟨2317247, by rfl⟩ : syracuseStep 3089663 = 4634495) B4634495
theorem B4171817 : Blo 912577 4171817 := bstep (se 2 (by rfl) ⟨1564431, by rfl⟩ : syracuseStep 4171817 = 3128863) B3128863
theorem B6596711 : Blo 912577 6596711 := bstep (se 1 (by rfl) ⟨4947533, by rfl⟩ : syracuseStep 6596711 = 9895067) B9895067
theorem B3125359 : Blo 912577 3125359 := bstep (se 1 (by rfl) ⟨2344019, by rfl⟩ : syracuseStep 3125359 = 4688039) B4688039
theorem B6959519 : Blo 912577 6959519 := bstep (se 1 (by rfl) ⟨5219639, by rfl⟩ : syracuseStep 6959519 = 10439279) B10439279
theorem B6437407 : Blo 912577 6437407 := bstep (se 1 (by rfl) ⟨4828055, by rfl⟩ : syracuseStep 6437407 = 9656111) B9656111
theorem B7815791 : Blo 912577 7815791 := bstep (se 1 (by rfl) ⟨5861843, by rfl⟩ : syracuseStep 7815791 = 11723687) B11723687
theorem B2054447 : Blo 912577 2054447 := bstep (se 1 (by rfl) ⟨1540835, by rfl⟩ : syracuseStep 2054447 = 3081671) B3081671
theorem B2055167 : Blo 912577 2055167 := bstep (se 1 (by rfl) ⟨1541375, by rfl⟩ : syracuseStep 2055167 = 3082751) B3082751
theorem B2055275 : Blo 912577 2055275 := bstep (se 1 (by rfl) ⟨1541456, by rfl⟩ : syracuseStep 2055275 = 3082913) B3082913
theorem B2317481 : Blo 912577 2317481 := bstep (se 2 (by rfl) ⟨869055, by rfl⟩ : syracuseStep 2317481 = 1738111) B1738111
theorem B2318159 : Blo 912577 2318159 := bstep (se 1 (by rfl) ⟨1738619, by rfl⟩ : syracuseStep 2318159 = 3477239) B3477239
theorem B2056895 : Blo 912577 2056895 := bstep (se 1 (by rfl) ⟨1542671, by rfl⟩ : syracuseStep 2056895 = 3085343) B3085343
theorem B2057183 : Blo 912577 2057183 := bstep (se 1 (by rfl) ⟨1542887, by rfl⟩ : syracuseStep 2057183 = 3085775) B3085775
theorem B2057903 : Blo 912577 2057903 := bstep (se 1 (by rfl) ⟨1543427, by rfl⟩ : syracuseStep 2057903 = 3086855) B3086855
theorem B15623927 : Blo 912577 15623927 := bstep (se 1 (by rfl) ⟨11717945, by rfl⟩ : syracuseStep 15623927 = 23435891) B23435891
theorem B1370843 : Blo 912577 1370843 := bstep (se 1 (by rfl) ⟨1028132, by rfl⟩ : syracuseStep 1370843 = 2056265) B2056265
theorem B912847 : Blo 912577 912847 := bstep (se 1 (by rfl) ⟨684635, by rfl⟩ : syracuseStep 912847 = 1369271) B1369271
theorem B912895 : Blo 912577 912895 := bstep (se 1 (by rfl) ⟨684671, by rfl⟩ : syracuseStep 912895 = 1369343) B1369343
theorem B913007 : Blo 912577 913007 := bstep (se 1 (by rfl) ⟨684755, by rfl⟩ : syracuseStep 913007 = 1369511) B1369511
theorem B913647 : Blo 912577 913647 := bstep (se 1 (by rfl) ⟨685235, by rfl⟩ : syracuseStep 913647 = 1370471) B1370471
theorem B5796269 : Blo 912577 5796269 := bstep (se 3 (by rfl) ⟨1086800, by rfl⟩ : syracuseStep 5796269 = 2173601) B2173601
theorem B914543 : Blo 912577 914543 := bstep (se 1 (by rfl) ⟨685907, by rfl⟩ : syracuseStep 914543 = 1371815) B1371815
theorem B3470647 : Blo 912577 3470647 := bstep (se 1 (by rfl) ⟨2602985, by rfl⟩ : syracuseStep 3470647 = 5205971) B5205971
theorem B29619533 : Blo 912577 29619533 := bstep (se 3 (by rfl) ⟨5553662, by rfl⟩ : syracuseStep 29619533 = 11107325) B11107325
theorem B1734185 : Blo 912577 1734185 := bstep (se 2 (by rfl) ⟨650319, by rfl⟩ : syracuseStep 1734185 = 1300639) B1300639
theorem B7796519 : Blo 912577 7796519 := bstep (se 1 (by rfl) ⟨5847389, by rfl⟩ : syracuseStep 7796519 = 11694779) B11694779
theorem B1374185 : Blo 912577 1374185 := bstep (se 2 (by rfl) ⟨515319, by rfl⟩ : syracuseStep 1374185 = 1030639) B1030639
theorem B5209343 : Blo 912577 5209343 := bstep (se 1 (by rfl) ⟨3907007, by rfl⟩ : syracuseStep 5209343 = 7814015) B7814015
theorem B5210527 : Blo 912577 5210527 := bstep (se 1 (by rfl) ⟨3907895, by rfl⟩ : syracuseStep 5210527 = 7815791) B7815791
theorem B41157307 : Blo 912577 41157307 := bstep (se 1 (by rfl) ⟨30867980, by rfl⟩ : syracuseStep 41157307 = 61735961) B61735961
theorem B3081455 : Blo 912577 3081455 := bstep (se 1 (by rfl) ⟨2311091, by rfl⟩ : syracuseStep 3081455 = 4622183) B4622183
theorem B8325827 : Blo 912577 8325827 := bstep (se 1 (by rfl) ⟨6244370, by rfl⟩ : syracuseStep 8325827 = 12488741) B12488741
theorem B1544987 : Blo 912577 1544987 := bstep (se 1 (by rfl) ⟨1158740, by rfl⟩ : syracuseStep 1544987 = 2317481) B2317481
theorem B12522455 : Blo 912577 12522455 := bstep (se 1 (by rfl) ⟨9391841, by rfl⟩ : syracuseStep 12522455 = 18783683) B18783683
theorem B1545439 : Blo 912577 1545439 := bstep (se 1 (by rfl) ⟨1159079, by rfl⟩ : syracuseStep 1545439 = 2318159) B2318159
theorem B4167145 : Blo 912577 4167145 := bstep (se 2 (by rfl) ⟨1562679, by rfl⟩ : syracuseStep 4167145 = 3125359) B3125359
theorem B4397807 : Blo 912577 4397807 := bstep (se 1 (by rfl) ⟨3298355, by rfl⟩ : syracuseStep 4397807 = 6596711) B6596711
theorem B4627529 : Blo 912577 4627529 := bstep (se 2 (by rfl) ⟨1735323, by rfl⟩ : syracuseStep 4627529 = 3470647) B3470647
theorem B1156123 : Blo 912577 1156123 := bstep (se 1 (by rfl) ⟨867092, by rfl⟩ : syracuseStep 1156123 = 1734185) B1734185
theorem B3715321 : Blo 912577 3715321 := bstep (se 2 (by rfl) ⟨1393245, by rfl⟩ : syracuseStep 3715321 = 2786491) B2786491
theorem B2472383 : Blo 912577 2472383 := bstep (se 1 (by rfl) ⟨1854287, by rfl⟩ : syracuseStep 2472383 = 3708575) B3708575
theorem B4639679 : Blo 912577 4639679 := bstep (se 1 (by rfl) ⟨3479759, by rfl⟩ : syracuseStep 4639679 = 6959519) B6959519
theorem B19746355 : Blo 912577 19746355 := bstep (se 1 (by rfl) ⟨14809766, by rfl⟩ : syracuseStep 19746355 = 29619533) B29619533
theorem B5197679 : Blo 912577 5197679 := bstep (se 1 (by rfl) ⟨3898259, by rfl⟩ : syracuseStep 5197679 = 7796519) B7796519
theorem B5561257 : Blo 912577 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B7824539 : Blo 912577 7824539 := bstep (se 1 (by rfl) ⟨5868404, by rfl⟩ : syracuseStep 7824539 = 11736809) B11736809
theorem B1369631 : Blo 912577 1369631 := bstep (se 1 (by rfl) ⟨1027223, by rfl⟩ : syracuseStep 1369631 = 2054447) B2054447
theorem B1370111 : Blo 912577 1370111 := bstep (se 1 (by rfl) ⟨1027583, by rfl⟩ : syracuseStep 1370111 = 2055167) B2055167
theorem B1370183 : Blo 912577 1370183 := bstep (se 1 (by rfl) ⟨1027637, by rfl⟩ : syracuseStep 1370183 = 2055275) B2055275
theorem B10578761 : Blo 912577 10578761 := bstep (se 2 (by rfl) ⟨3967035, by rfl⟩ : syracuseStep 10578761 = 7934071) B7934071
theorem B2059091 : Blo 912577 2059091 := bstep (se 1 (by rfl) ⟨1544318, by rfl⟩ : syracuseStep 2059091 = 3088637) B3088637
theorem B2059199 : Blo 912577 2059199 := bstep (se 1 (by rfl) ⟨1544399, by rfl⟩ : syracuseStep 2059199 = 3088799) B3088799
theorem B1371263 : Blo 912577 1371263 := bstep (se 1 (by rfl) ⟨1028447, by rfl⟩ : syracuseStep 1371263 = 2056895) B2056895
theorem B1371455 : Blo 912577 1371455 := bstep (se 1 (by rfl) ⟨1028591, by rfl⟩ : syracuseStep 1371455 = 2057183) B2057183
theorem B2059775 : Blo 912577 2059775 := bstep (se 1 (by rfl) ⟨1544831, by rfl⟩ : syracuseStep 2059775 = 3089663) B3089663
theorem B1371935 : Blo 912577 1371935 := bstep (se 1 (by rfl) ⟨1028951, by rfl⟩ : syracuseStep 1371935 = 2057903) B2057903
theorem B10415951 : Blo 912577 10415951 := bstep (se 1 (by rfl) ⟨7811963, by rfl⟩ : syracuseStep 10415951 = 15623927) B15623927
theorem B2781211 : Blo 912577 2781211 := bstep (se 1 (by rfl) ⟨2085908, by rfl⟩ : syracuseStep 2781211 = 4171817) B4171817
theorem B5206153 : Blo 912577 5206153 := bstep (se 2 (by rfl) ⟨1952307, by rfl⟩ : syracuseStep 5206153 = 3904615) B3904615
theorem B913895 : Blo 912577 913895 := bstep (se 1 (by rfl) ⟨685421, by rfl⟩ : syracuseStep 913895 = 1370843) B1370843
theorem B3864179 : Blo 912577 3864179 := bstep (se 1 (by rfl) ⟨2898134, by rfl⟩ : syracuseStep 3864179 = 5796269) B5796269
theorem B8583209 : Blo 912577 8583209 := bstep (se 2 (by rfl) ⟨3218703, by rfl⟩ : syracuseStep 8583209 = 6437407) B6437407
theorem B100235677 : Blo 912577 100235677 := bstep (se 3 (by rfl) ⟨18794189, by rfl⟩ : syracuseStep 100235677 = 37588379) B37588379
theorem B916123 : Blo 912577 916123 := bstep (se 1 (by rfl) ⟨687092, by rfl⟩ : syracuseStep 916123 = 1374185) B1374185
theorem B3472895 : Blo 912577 3472895 := bstep (se 1 (by rfl) ⟨2604671, by rfl⟩ : syracuseStep 3472895 = 5209343) B5209343
theorem B6947369 : Blo 912577 6947369 := bstep (se 2 (by rfl) ⟨2605263, by rfl⟩ : syracuseStep 6947369 = 5210527) B5210527
theorem B1541497 : Blo 912577 1541497 := bstep (se 2 (by rfl) ⟨578061, by rfl⟩ : syracuseStep 1541497 = 1156123) B1156123
theorem B3085019 : Blo 912577 3085019 := bstep (se 1 (by rfl) ⟨2313764, by rfl⟩ : syracuseStep 3085019 = 4627529) B4627529
theorem B3708281 : Blo 912577 3708281 := bstep (se 2 (by rfl) ⟨1390605, by rfl⟩ : syracuseStep 3708281 = 2781211) B2781211
theorem B4953761 : Blo 912577 4953761 := bstep (se 2 (by rfl) ⟨1857660, by rfl⟩ : syracuseStep 4953761 = 3715321) B3715321
theorem B5216359 : Blo 912577 5216359 := bstep (se 1 (by rfl) ⟨3912269, by rfl⟩ : syracuseStep 5216359 = 7824539) B7824539
theorem B6593021 : Blo 912577 6593021 := bstep (se 3 (by rfl) ⟨1236191, by rfl⟩ : syracuseStep 6593021 = 2472383) B2472383
theorem B7052507 : Blo 912577 7052507 := bstep (se 1 (by rfl) ⟨5289380, by rfl⟩ : syracuseStep 7052507 = 10578761) B10578761
theorem B22224773 : Blo 912577 22224773 := bstep (se 4 (by rfl) ⟨2083572, by rfl⟩ : syracuseStep 22224773 = 4167145) B4167145
theorem B7415009 : Blo 912577 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B5550551 : Blo 912577 5550551 := bstep (se 1 (by rfl) ⟨4162913, by rfl⟩ : syracuseStep 5550551 = 8325827) B8325827
theorem B3093119 : Blo 912577 3093119 := bstep (se 1 (by rfl) ⟨2319839, by rfl⟩ : syracuseStep 3093119 = 4639679) B4639679
theorem B1029991 : Blo 912577 1029991 := bstep (se 1 (by rfl) ⟨772493, by rfl⟩ : syracuseStep 1029991 = 1544987) B1544987
theorem B2931871 : Blo 912577 2931871 := bstep (se 1 (by rfl) ⟨2198903, by rfl⟩ : syracuseStep 2931871 = 4397807) B4397807
theorem B26328473 : Blo 912577 26328473 := bstep (se 2 (by rfl) ⟨9873177, by rfl⟩ : syracuseStep 26328473 = 19746355) B19746355
theorem B133647569 : Blo 912577 133647569 := bstep (se 2 (by rfl) ⟨50117838, by rfl⟩ : syracuseStep 133647569 = 100235677) B100235677
theorem B2576119 : Blo 912577 2576119 := bstep (se 1 (by rfl) ⟨1932089, by rfl⟩ : syracuseStep 2576119 = 3864179) B3864179
theorem B5722139 : Blo 912577 5722139 := bstep (se 1 (by rfl) ⟨4291604, by rfl⟩ : syracuseStep 5722139 = 8583209) B8583209
theorem B2315263 : Blo 912577 2315263 := bstep (se 1 (by rfl) ⟨1736447, by rfl⟩ : syracuseStep 2315263 = 3472895) B3472895
theorem B2054303 : Blo 912577 2054303 := bstep (se 1 (by rfl) ⟨1540727, by rfl⟩ : syracuseStep 2054303 = 3081455) B3081455
theorem B54876409 : Blo 912577 54876409 := bstep (se 2 (by rfl) ⟨20578653, by rfl⟩ : syracuseStep 54876409 = 41157307) B41157307
theorem B3465119 : Blo 912577 3465119 := bstep (se 1 (by rfl) ⟨2598839, by rfl⟩ : syracuseStep 3465119 = 5197679) B5197679
theorem B8348303 : Blo 912577 8348303 := bstep (se 1 (by rfl) ⟨6261227, by rfl⟩ : syracuseStep 8348303 = 12522455) B12522455
theorem B6941537 : Blo 912577 6941537 := bstep (se 2 (by rfl) ⟨2603076, by rfl⟩ : syracuseStep 6941537 = 5206153) B5206153
theorem B913087 : Blo 912577 913087 := bstep (se 1 (by rfl) ⟨684815, by rfl⟩ : syracuseStep 913087 = 1369631) B1369631
theorem B913407 : Blo 912577 913407 := bstep (se 1 (by rfl) ⟨685055, by rfl⟩ : syracuseStep 913407 = 1370111) B1370111
theorem B913455 : Blo 912577 913455 := bstep (se 1 (by rfl) ⟨685091, by rfl⟩ : syracuseStep 913455 = 1370183) B1370183
theorem B2060585 : Blo 912577 2060585 := bstep (se 2 (by rfl) ⟨772719, by rfl⟩ : syracuseStep 2060585 = 1545439) B1545439
theorem B1372727 : Blo 912577 1372727 := bstep (se 1 (by rfl) ⟨1029545, by rfl⟩ : syracuseStep 1372727 = 2059091) B2059091
theorem B1372799 : Blo 912577 1372799 := bstep (se 1 (by rfl) ⟨1029599, by rfl⟩ : syracuseStep 1372799 = 2059199) B2059199
theorem B914175 : Blo 912577 914175 := bstep (se 1 (by rfl) ⟨685631, by rfl⟩ : syracuseStep 914175 = 1371263) B1371263
theorem B914303 : Blo 912577 914303 := bstep (se 1 (by rfl) ⟨685727, by rfl⟩ : syracuseStep 914303 = 1371455) B1371455
theorem B1373183 : Blo 912577 1373183 := bstep (se 1 (by rfl) ⟨1029887, by rfl⟩ : syracuseStep 1373183 = 2059775) B2059775
theorem B914623 : Blo 912577 914623 := bstep (se 1 (by rfl) ⟨685967, by rfl⟩ : syracuseStep 914623 = 1371935) B1371935
theorem B6943967 : Blo 912577 6943967 := bstep (se 1 (by rfl) ⟨5207975, by rfl⟩ : syracuseStep 6943967 = 10415951) B10415951
theorem B89098379 : Blo 912577 89098379 := bstep (se 1 (by rfl) ⟨66823784, by rfl⟩ : syracuseStep 89098379 = 133647569) B133647569
theorem B4395347 : Blo 912577 4395347 := bstep (se 1 (by rfl) ⟨3296510, by rfl⟩ : syracuseStep 4395347 = 6593021) B6593021
theorem B14816515 : Blo 912577 14816515 := bstep (se 1 (by rfl) ⟨11112386, by rfl⟩ : syracuseStep 14816515 = 22224773) B22224773
theorem B3087017 : Blo 912577 3087017 := bstep (se 2 (by rfl) ⟨1157631, by rfl⟩ : syracuseStep 3087017 = 2315263) B2315263
theorem B4627691 : Blo 912577 4627691 := bstep (se 1 (by rfl) ⟨3470768, by rfl⟩ : syracuseStep 4627691 = 6941537) B6941537
theorem B6955145 : Blo 912577 6955145 := bstep (se 2 (by rfl) ⟨2608179, by rfl⟩ : syracuseStep 6955145 = 5216359) B5216359
theorem B4629311 : Blo 912577 4629311 := bstep (se 1 (by rfl) ⟨3471983, by rfl⟩ : syracuseStep 4629311 = 6943967) B6943967
theorem B3909161 : Blo 912577 3909161 := bstep (se 2 (by rfl) ⟨1465935, by rfl⟩ : syracuseStep 3909161 = 2931871) B2931871
theorem B4631579 : Blo 912577 4631579 := bstep (se 1 (by rfl) ⟨3473684, by rfl⟩ : syracuseStep 4631579 = 6947369) B6947369
theorem B22262141 : Blo 912577 22262141 := bstep (se 3 (by rfl) ⟨4174151, by rfl⟩ : syracuseStep 22262141 = 8348303) B8348303
theorem B3814759 : Blo 912577 3814759 := bstep (se 1 (by rfl) ⟨2861069, by rfl⟩ : syracuseStep 3814759 = 5722139) B5722139
theorem B4701671 : Blo 912577 4701671 := bstep (se 1 (by rfl) ⟨3526253, by rfl⟩ : syracuseStep 4701671 = 7052507) B7052507
theorem B2310079 : Blo 912577 2310079 := bstep (se 1 (by rfl) ⟨1732559, by rfl⟩ : syracuseStep 2310079 = 3465119) B3465119
theorem B17552315 : Blo 912577 17552315 := bstep (se 1 (by rfl) ⟨13164236, by rfl⟩ : syracuseStep 17552315 = 26328473) B26328473
theorem B292674181 : Blo 912577 292674181 := bstep (se 4 (by rfl) ⟨27438204, by rfl⟩ : syracuseStep 292674181 = 54876409) B54876409
theorem B2055329 : Blo 912577 2055329 := bstep (se 2 (by rfl) ⟨770748, by rfl⟩ : syracuseStep 2055329 = 1541497) B1541497
theorem B2056679 : Blo 912577 2056679 := bstep (se 1 (by rfl) ⟨1542509, by rfl⟩ : syracuseStep 2056679 = 3085019) B3085019
theorem B9888749 : Blo 912577 9888749 := bstep (se 3 (by rfl) ⟨1854140, by rfl⟩ : syracuseStep 9888749 = 3708281) B3708281
theorem B3302507 : Blo 912577 3302507 := bstep (se 1 (by rfl) ⟨2476880, by rfl⟩ : syracuseStep 3302507 = 4953761) B4953761
theorem B1369535 : Blo 912577 1369535 := bstep (se 1 (by rfl) ⟨1027151, by rfl⟩ : syracuseStep 1369535 = 2054303) B2054303
theorem B3434825 : Blo 912577 3434825 := bstep (se 2 (by rfl) ⟨1288059, by rfl⟩ : syracuseStep 3434825 = 2576119) B2576119
theorem B4943339 : Blo 912577 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B1373321 : Blo 912577 1373321 := bstep (se 2 (by rfl) ⟨514995, by rfl⟩ : syracuseStep 1373321 = 1029991) B1029991
theorem B1373723 : Blo 912577 1373723 := bstep (se 1 (by rfl) ⟨1030292, by rfl⟩ : syracuseStep 1373723 = 2060585) B2060585
theorem B3700367 : Blo 912577 3700367 := bstep (se 1 (by rfl) ⟨2775275, by rfl⟩ : syracuseStep 3700367 = 5550551) B5550551
theorem B915151 : Blo 912577 915151 := bstep (se 1 (by rfl) ⟨686363, by rfl⟩ : syracuseStep 915151 = 1372727) B1372727
theorem B915199 : Blo 912577 915199 := bstep (se 1 (by rfl) ⟨686399, by rfl⟩ : syracuseStep 915199 = 1372799) B1372799
theorem B2062079 : Blo 912577 2062079 := bstep (se 1 (by rfl) ⟨1546559, by rfl⟩ : syracuseStep 2062079 = 3093119) B3093119
theorem B915455 : Blo 912577 915455 := bstep (se 1 (by rfl) ⟨686591, by rfl⟩ : syracuseStep 915455 = 1373183) B1373183
theorem B11701543 : Blo 912577 11701543 := bstep (se 1 (by rfl) ⟨8776157, by rfl⟩ : syracuseStep 11701543 = 17552315) B17552315
theorem B3085127 : Blo 912577 3085127 := bstep (se 1 (by rfl) ⟨2313845, by rfl⟩ : syracuseStep 3085127 = 4627691) B4627691
theorem B3086207 : Blo 912577 3086207 := bstep (se 1 (by rfl) ⟨2314655, by rfl⟩ : syracuseStep 3086207 = 4629311) B4629311
theorem B6592499 : Blo 912577 6592499 := bstep (se 1 (by rfl) ⟨4944374, by rfl⟩ : syracuseStep 6592499 = 9888749) B9888749
theorem B2201671 : Blo 912577 2201671 := bstep (se 1 (by rfl) ⟨1651253, by rfl⟩ : syracuseStep 2201671 = 3302507) B3302507
theorem B3087719 : Blo 912577 3087719 := bstep (se 1 (by rfl) ⟨2315789, by rfl⟩ : syracuseStep 3087719 = 4631579) B4631579
theorem B2466911 : Blo 912577 2466911 := bstep (se 1 (by rfl) ⟨1850183, by rfl⟩ : syracuseStep 2466911 = 3700367) B3700367
theorem B2930231 : Blo 912577 2930231 := bstep (se 1 (by rfl) ⟨2197673, by rfl⟩ : syracuseStep 2930231 = 4395347) B4395347
theorem B4636763 : Blo 912577 4636763 := bstep (se 1 (by rfl) ⟨3477572, by rfl⟩ : syracuseStep 4636763 = 6955145) B6955145
theorem B2606107 : Blo 912577 2606107 := bstep (se 1 (by rfl) ⟨1954580, by rfl⟩ : syracuseStep 2606107 = 3909161) B3909161
theorem B3295559 : Blo 912577 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B3134447 : Blo 912577 3134447 := bstep (se 1 (by rfl) ⟨2350835, by rfl⟩ : syracuseStep 3134447 = 4701671) B4701671
theorem B59398919 : Blo 912577 59398919 := bstep (se 1 (by rfl) ⟨44549189, by rfl⟩ : syracuseStep 59398919 = 89098379) B89098379
theorem B2058011 : Blo 912577 2058011 := bstep (se 1 (by rfl) ⟨1543508, by rfl⟩ : syracuseStep 2058011 = 3087017) B3087017
theorem B1370219 : Blo 912577 1370219 := bstep (se 1 (by rfl) ⟨1027664, by rfl⟩ : syracuseStep 1370219 = 2055329) B2055329
theorem B1371119 : Blo 912577 1371119 := bstep (se 1 (by rfl) ⟨1028339, by rfl⟩ : syracuseStep 1371119 = 2056679) B2056679
theorem B913023 : Blo 912577 913023 := bstep (se 1 (by rfl) ⟨684767, by rfl⟩ : syracuseStep 913023 = 1369535) B1369535
theorem B2289883 : Blo 912577 2289883 := bstep (se 1 (by rfl) ⟨1717412, by rfl⟩ : syracuseStep 2289883 = 3434825) B3434825
theorem B19755353 : Blo 912577 19755353 := bstep (se 2 (by rfl) ⟨7408257, by rfl⟩ : syracuseStep 19755353 = 14816515) B14816515
theorem B20345381 : Blo 912577 20345381 := bstep (se 4 (by rfl) ⟨1907379, by rfl⟩ : syracuseStep 20345381 = 3814759) B3814759
theorem B14841427 : Blo 912577 14841427 := bstep (se 1 (by rfl) ⟨11131070, by rfl⟩ : syracuseStep 14841427 = 22262141) B22262141
theorem B915547 : Blo 912577 915547 := bstep (se 1 (by rfl) ⟨686660, by rfl⟩ : syracuseStep 915547 = 1373321) B1373321
theorem B390232241 : Blo 912577 390232241 := bstep (se 2 (by rfl) ⟨146337090, by rfl⟩ : syracuseStep 390232241 = 292674181) B292674181
theorem B915815 : Blo 912577 915815 := bstep (se 1 (by rfl) ⟨686861, by rfl⟩ : syracuseStep 915815 = 1373723) B1373723
theorem B1374719 : Blo 912577 1374719 := bstep (se 1 (by rfl) ⟨1031039, by rfl⟩ : syracuseStep 1374719 = 2062079) B2062079
theorem B3080105 : Blo 912577 3080105 := bstep (se 2 (by rfl) ⟨1155039, by rfl⟩ : syracuseStep 3080105 = 2310079) B2310079
theorem B3474809 : Blo 912577 3474809 := bstep (se 2 (by rfl) ⟨1303053, by rfl⟩ : syracuseStep 3474809 = 2606107) B2606107
theorem B2197039 : Blo 912577 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B4394999 : Blo 912577 4394999 := bstep (se 1 (by rfl) ⟨3296249, by rfl⟩ : syracuseStep 4394999 = 6592499) B6592499
theorem B15602057 : Blo 912577 15602057 := bstep (se 2 (by rfl) ⟨5850771, by rfl⟩ : syracuseStep 15602057 = 11701543) B11701543
theorem B3053177 : Blo 912577 3053177 := bstep (se 2 (by rfl) ⟨1144941, by rfl⟩ : syracuseStep 3053177 = 2289883) B2289883
theorem B1644607 : Blo 912577 1644607 := bstep (se 1 (by rfl) ⟨1233455, by rfl⟩ : syracuseStep 1644607 = 2466911) B2466911
theorem B260154827 : Blo 912577 260154827 := bstep (se 1 (by rfl) ⟨195116120, by rfl⟩ : syracuseStep 260154827 = 390232241) B390232241
theorem B3091175 : Blo 912577 3091175 := bstep (se 1 (by rfl) ⟨2318381, by rfl⟩ : syracuseStep 3091175 = 4636763) B4636763
theorem B11742245 : Blo 912577 11742245 := bstep (se 4 (by rfl) ⟨1100835, by rfl⟩ : syracuseStep 11742245 = 2201671) B2201671
theorem B39599279 : Blo 912577 39599279 := bstep (se 1 (by rfl) ⟨29699459, by rfl⟩ : syracuseStep 39599279 = 59398919) B59398919
theorem B1953487 : Blo 912577 1953487 := bstep (se 1 (by rfl) ⟨1465115, by rfl⟩ : syracuseStep 1953487 = 2930231) B2930231
theorem B2053403 : Blo 912577 2053403 := bstep (se 1 (by rfl) ⟨1540052, by rfl⟩ : syracuseStep 2053403 = 3080105) B3080105
theorem B2056751 : Blo 912577 2056751 := bstep (se 1 (by rfl) ⟨1542563, by rfl⟩ : syracuseStep 2056751 = 3085127) B3085127
theorem B2089631 : Blo 912577 2089631 := bstep (se 1 (by rfl) ⟨1567223, by rfl⟩ : syracuseStep 2089631 = 3134447) B3134447
theorem B2057471 : Blo 912577 2057471 := bstep (se 1 (by rfl) ⟨1543103, by rfl⟩ : syracuseStep 2057471 = 3086207) B3086207
theorem B2058479 : Blo 912577 2058479 := bstep (se 1 (by rfl) ⟨1543859, by rfl⟩ : syracuseStep 2058479 = 3087719) B3087719
theorem B1372007 : Blo 912577 1372007 := bstep (se 1 (by rfl) ⟨1029005, by rfl⟩ : syracuseStep 1372007 = 2058011) B2058011
theorem B913479 : Blo 912577 913479 := bstep (se 1 (by rfl) ⟨685109, by rfl⟩ : syracuseStep 913479 = 1370219) B1370219
theorem B914079 : Blo 912577 914079 := bstep (se 1 (by rfl) ⟨685559, by rfl⟩ : syracuseStep 914079 = 1371119) B1371119
theorem B19788569 : Blo 912577 19788569 := bstep (se 2 (by rfl) ⟨7420713, by rfl⟩ : syracuseStep 19788569 = 14841427) B14841427
theorem B13170235 : Blo 912577 13170235 := bstep (se 1 (by rfl) ⟨9877676, by rfl⟩ : syracuseStep 13170235 = 19755353) B19755353
theorem B13563587 : Blo 912577 13563587 := bstep (se 1 (by rfl) ⟨10172690, by rfl⟩ : syracuseStep 13563587 = 20345381) B20345381
theorem B916479 : Blo 912577 916479 := bstep (se 1 (by rfl) ⟨687359, by rfl⟩ : syracuseStep 916479 = 1374719) B1374719
theorem B2035451 : Blo 912577 2035451 := bstep (se 1 (by rfl) ⟨1526588, by rfl⟩ : syracuseStep 2035451 = 3053177) B3053177
theorem B2929385 : Blo 912577 2929385 := bstep (se 2 (by rfl) ⟨1098519, by rfl⟩ : syracuseStep 2929385 = 2197039) B2197039
theorem B10401371 : Blo 912577 10401371 := bstep (se 1 (by rfl) ⟨7801028, by rfl⟩ : syracuseStep 10401371 = 15602057) B15602057
theorem B2604649 : Blo 912577 2604649 := bstep (se 2 (by rfl) ⟨976743, by rfl⟩ : syracuseStep 2604649 = 1953487) B1953487
theorem B1393087 : Blo 912577 1393087 := bstep (se 1 (by rfl) ⟨1044815, by rfl⟩ : syracuseStep 1393087 = 2089631) B2089631
theorem B13192379 : Blo 912577 13192379 := bstep (se 1 (by rfl) ⟨9894284, by rfl⟩ : syracuseStep 13192379 = 19788569) B19788569
theorem B26399519 : Blo 912577 26399519 := bstep (se 1 (by rfl) ⟨19799639, by rfl⟩ : syracuseStep 26399519 = 39599279) B39599279
theorem B11719997 : Blo 912577 11719997 := bstep (se 3 (by rfl) ⟨2197499, by rfl⟩ : syracuseStep 11719997 = 4394999) B4394999
theorem B8771237 : Blo 912577 8771237 := bstep (se 4 (by rfl) ⟨822303, by rfl⟩ : syracuseStep 8771237 = 1644607) B1644607
theorem B2316539 : Blo 912577 2316539 := bstep (se 1 (by rfl) ⟨1737404, by rfl⟩ : syracuseStep 2316539 = 3474809) B3474809
theorem B1368935 : Blo 912577 1368935 := bstep (se 1 (by rfl) ⟨1026701, by rfl⟩ : syracuseStep 1368935 = 2053403) B2053403
theorem B1371167 : Blo 912577 1371167 := bstep (se 1 (by rfl) ⟨1028375, by rfl⟩ : syracuseStep 1371167 = 2056751) B2056751
theorem B1371647 : Blo 912577 1371647 := bstep (se 1 (by rfl) ⟨1028735, by rfl⟩ : syracuseStep 1371647 = 2057471) B2057471
theorem B173436551 : Blo 912577 173436551 := bstep (se 1 (by rfl) ⟨130077413, by rfl⟩ : syracuseStep 173436551 = 260154827) B260154827
theorem B1372319 : Blo 912577 1372319 := bstep (se 1 (by rfl) ⟨1029239, by rfl⟩ : syracuseStep 1372319 = 2058479) B2058479
theorem B2060783 : Blo 912577 2060783 := bstep (se 1 (by rfl) ⟨1545587, by rfl⟩ : syracuseStep 2060783 = 3091175) B3091175
theorem B7828163 : Blo 912577 7828163 := bstep (se 1 (by rfl) ⟨5871122, by rfl⟩ : syracuseStep 7828163 = 11742245) B11742245
theorem B17560313 : Blo 912577 17560313 := bstep (se 2 (by rfl) ⟨6585117, by rfl⟩ : syracuseStep 17560313 = 13170235) B13170235
theorem B914671 : Blo 912577 914671 := bstep (se 1 (by rfl) ⟨686003, by rfl⟩ : syracuseStep 914671 = 1372007) B1372007
theorem B9042391 : Blo 912577 9042391 := bstep (se 1 (by rfl) ⟨6781793, by rfl⟩ : syracuseStep 9042391 = 13563587) B13563587
theorem B17599679 : Blo 912577 17599679 := bstep (se 1 (by rfl) ⟨13199759, by rfl⟩ : syracuseStep 17599679 = 26399519) B26399519
theorem B1544359 : Blo 912577 1544359 := bstep (se 1 (by rfl) ⟨1158269, by rfl⟩ : syracuseStep 1544359 = 2316539) B2316539
theorem B5218775 : Blo 912577 5218775 := bstep (se 1 (by rfl) ⟨3914081, by rfl⟩ : syracuseStep 5218775 = 7828163) B7828163
theorem B11706875 : Blo 912577 11706875 := bstep (se 1 (by rfl) ⟨8780156, by rfl⟩ : syracuseStep 11706875 = 17560313) B17560313
theorem B8794919 : Blo 912577 8794919 := bstep (se 1 (by rfl) ⟨6596189, by rfl⟩ : syracuseStep 8794919 = 13192379) B13192379
theorem B1356967 : Blo 912577 1356967 := bstep (se 1 (by rfl) ⟨1017725, by rfl⟩ : syracuseStep 1356967 = 2035451) B2035451
theorem B7813331 : Blo 912577 7813331 := bstep (se 1 (by rfl) ⟨5859998, by rfl⟩ : syracuseStep 7813331 = 11719997) B11719997
theorem B5847491 : Blo 912577 5847491 := bstep (se 1 (by rfl) ⟨4385618, by rfl⟩ : syracuseStep 5847491 = 8771237) B8771237
theorem B115624367 : Blo 912577 115624367 := bstep (se 1 (by rfl) ⟨86718275, by rfl⟩ : syracuseStep 115624367 = 173436551) B173436551
theorem B1952923 : Blo 912577 1952923 := bstep (se 1 (by rfl) ⟨1464692, by rfl⟩ : syracuseStep 1952923 = 2929385) B2929385
theorem B6934247 : Blo 912577 6934247 := bstep (se 1 (by rfl) ⟨5200685, by rfl⟩ : syracuseStep 6934247 = 10401371) B10401371
theorem B1857449 : Blo 912577 1857449 := bstep (se 2 (by rfl) ⟨696543, by rfl⟩ : syracuseStep 1857449 = 1393087) B1393087
theorem B912623 : Blo 912577 912623 := bstep (se 1 (by rfl) ⟨684467, by rfl⟩ : syracuseStep 912623 = 1368935) B1368935
theorem B914111 : Blo 912577 914111 := bstep (se 1 (by rfl) ⟨685583, by rfl⟩ : syracuseStep 914111 = 1371167) B1371167
theorem B914431 : Blo 912577 914431 := bstep (se 1 (by rfl) ⟨685823, by rfl⟩ : syracuseStep 914431 = 1371647) B1371647
theorem B914879 : Blo 912577 914879 := bstep (se 1 (by rfl) ⟨686159, by rfl⟩ : syracuseStep 914879 = 1372319) B1372319
theorem B1373855 : Blo 912577 1373855 := bstep (se 1 (by rfl) ⟨1030391, by rfl⟩ : syracuseStep 1373855 = 2060783) B2060783
theorem B12056521 : Blo 912577 12056521 := bstep (se 2 (by rfl) ⟨4521195, by rfl⟩ : syracuseStep 12056521 = 9042391) B9042391
theorem B3472865 : Blo 912577 3472865 := bstep (se 2 (by rfl) ⟨1302324, by rfl⟩ : syracuseStep 3472865 = 2604649) B2604649
theorem B11733119 : Blo 912577 11733119 := bstep (se 1 (by rfl) ⟨8799839, by rfl⟩ : syracuseStep 11733119 = 17599679) B17599679
theorem B4622831 : Blo 912577 4622831 := bstep (se 1 (by rfl) ⟨3467123, by rfl⟩ : syracuseStep 4622831 = 6934247) B6934247
theorem B4953197 : Blo 912577 4953197 := bstep (se 3 (by rfl) ⟨928724, by rfl⟩ : syracuseStep 4953197 = 1857449) B1857449
theorem B3479183 : Blo 912577 3479183 := bstep (se 1 (by rfl) ⟨2609387, by rfl⟩ : syracuseStep 3479183 = 5218775) B5218775
theorem B7804583 : Blo 912577 7804583 := bstep (se 1 (by rfl) ⟨5853437, by rfl⟩ : syracuseStep 7804583 = 11706875) B11706875
theorem B1809289 : Blo 912577 1809289 := bstep (se 2 (by rfl) ⟨678483, by rfl⟩ : syracuseStep 1809289 = 1356967) B1356967
theorem B77082911 : Blo 912577 77082911 := bstep (se 1 (by rfl) ⟨57812183, by rfl⟩ : syracuseStep 77082911 = 115624367) B115624367
theorem B2603897 : Blo 912577 2603897 := bstep (se 2 (by rfl) ⟨976461, by rfl⟩ : syracuseStep 2603897 = 1952923) B1952923
theorem B16075361 : Blo 912577 16075361 := bstep (se 2 (by rfl) ⟨6028260, by rfl⟩ : syracuseStep 16075361 = 12056521) B12056521
theorem B2315243 : Blo 912577 2315243 := bstep (se 1 (by rfl) ⟨1736432, by rfl⟩ : syracuseStep 2315243 = 3472865) B3472865
theorem B2059145 : Blo 912577 2059145 := bstep (se 2 (by rfl) ⟨772179, by rfl⟩ : syracuseStep 2059145 = 1544359) B1544359
theorem B15593309 : Blo 912577 15593309 := bstep (se 3 (by rfl) ⟨2923745, by rfl⟩ : syracuseStep 15593309 = 5847491) B5847491
theorem B5863279 : Blo 912577 5863279 := bstep (se 1 (by rfl) ⟨4397459, by rfl⟩ : syracuseStep 5863279 = 8794919) B8794919
theorem B915903 : Blo 912577 915903 := bstep (se 1 (by rfl) ⟨686927, by rfl⟩ : syracuseStep 915903 = 1373855) B1373855
theorem B5208887 : Blo 912577 5208887 := bstep (se 1 (by rfl) ⟨3906665, by rfl⟩ : syracuseStep 5208887 = 7813331) B7813331
theorem B3081887 : Blo 912577 3081887 := bstep (se 1 (by rfl) ⟨2311415, by rfl⟩ : syracuseStep 3081887 = 4622831) B4622831
theorem B10716907 : Blo 912577 10716907 := bstep (se 1 (by rfl) ⟨8037680, by rfl⟩ : syracuseStep 10716907 = 16075361) B16075361
theorem B1543495 : Blo 912577 1543495 := bstep (se 1 (by rfl) ⟨1157621, by rfl⟩ : syracuseStep 1543495 = 2315243) B2315243
theorem B10395539 : Blo 912577 10395539 := bstep (se 1 (by rfl) ⟨7796654, by rfl⟩ : syracuseStep 10395539 = 15593309) B15593309
theorem B51388607 : Blo 912577 51388607 := bstep (se 1 (by rfl) ⟨38541455, by rfl⟩ : syracuseStep 51388607 = 77082911) B77082911
theorem B7817705 : Blo 912577 7817705 := bstep (se 2 (by rfl) ⟨2931639, by rfl⟩ : syracuseStep 7817705 = 5863279) B5863279
theorem B2412385 : Blo 912577 2412385 := bstep (se 2 (by rfl) ⟨904644, by rfl⟩ : syracuseStep 2412385 = 1809289) B1809289
theorem B7822079 : Blo 912577 7822079 := bstep (se 1 (by rfl) ⟨5866559, by rfl⟩ : syracuseStep 7822079 = 11733119) B11733119
theorem B3302131 : Blo 912577 3302131 := bstep (se 1 (by rfl) ⟨2476598, by rfl⟩ : syracuseStep 3302131 = 4953197) B4953197
theorem B2319455 : Blo 912577 2319455 := bstep (se 1 (by rfl) ⟨1739591, by rfl⟩ : syracuseStep 2319455 = 3479183) B3479183
theorem B5203055 : Blo 912577 5203055 := bstep (se 1 (by rfl) ⟨3902291, by rfl⟩ : syracuseStep 5203055 = 7804583) B7804583
theorem B1372763 : Blo 912577 1372763 := bstep (se 1 (by rfl) ⟨1029572, by rfl⟩ : syracuseStep 1372763 = 2059145) B2059145
theorem B3472591 : Blo 912577 3472591 := bstep (se 1 (by rfl) ⟨2604443, by rfl⟩ : syracuseStep 3472591 = 5208887) B5208887
theorem B1735931 : Blo 912577 1735931 := bstep (se 1 (by rfl) ⟨1301948, by rfl⟩ : syracuseStep 1735931 = 2603897) B2603897
theorem B5211803 : Blo 912577 5211803 := bstep (se 1 (by rfl) ⟨3908852, by rfl⟩ : syracuseStep 5211803 = 7817705) B7817705
theorem B14289209 : Blo 912577 14289209 := bstep (se 2 (by rfl) ⟨5358453, by rfl⟩ : syracuseStep 14289209 = 10716907) B10716907
theorem B5214719 : Blo 912577 5214719 := bstep (se 1 (by rfl) ⟨3911039, by rfl⟩ : syracuseStep 5214719 = 7822079) B7822079
theorem B1546303 : Blo 912577 1546303 := bstep (se 1 (by rfl) ⟨1159727, by rfl⟩ : syracuseStep 1546303 = 2319455) B2319455
theorem B4629149 : Blo 912577 4629149 := bstep (se 3 (by rfl) ⟨867965, by rfl⟩ : syracuseStep 4629149 = 1735931) B1735931
theorem B4630121 : Blo 912577 4630121 := bstep (se 2 (by rfl) ⟨1736295, by rfl⟩ : syracuseStep 4630121 = 3472591) B3472591
theorem B4402841 : Blo 912577 4402841 := bstep (se 2 (by rfl) ⟨1651065, by rfl⟩ : syracuseStep 4402841 = 3302131) B3302131
theorem B6930359 : Blo 912577 6930359 := bstep (se 1 (by rfl) ⟨5197769, by rfl⟩ : syracuseStep 6930359 = 10395539) B10395539
theorem B34259071 : Blo 912577 34259071 := bstep (se 1 (by rfl) ⟨25694303, by rfl⟩ : syracuseStep 34259071 = 51388607) B51388607
theorem B12866053 : Blo 912577 12866053 := bstep (se 4 (by rfl) ⟨1206192, by rfl⟩ : syracuseStep 12866053 = 2412385) B2412385
theorem B2054591 : Blo 912577 2054591 := bstep (se 1 (by rfl) ⟨1540943, by rfl⟩ : syracuseStep 2054591 = 3081887) B3081887
theorem B2057993 : Blo 912577 2057993 := bstep (se 2 (by rfl) ⟨771747, by rfl⟩ : syracuseStep 2057993 = 1543495) B1543495
theorem B3468703 : Blo 912577 3468703 := bstep (se 1 (by rfl) ⟨2601527, by rfl⟩ : syracuseStep 3468703 = 5203055) B5203055
theorem B915175 : Blo 912577 915175 := bstep (se 1 (by rfl) ⟨686381, by rfl⟩ : syracuseStep 915175 = 1372763) B1372763
theorem B45678761 : Blo 912577 45678761 := bstep (se 2 (by rfl) ⟨17129535, by rfl⟩ : syracuseStep 45678761 = 34259071) B34259071
theorem B3474535 : Blo 912577 3474535 := bstep (se 1 (by rfl) ⟨2605901, by rfl⟩ : syracuseStep 3474535 = 5211803) B5211803
theorem B3476479 : Blo 912577 3476479 := bstep (se 1 (by rfl) ⟨2607359, by rfl⟩ : syracuseStep 3476479 = 5214719) B5214719
theorem B4624937 : Blo 912577 4624937 := bstep (se 2 (by rfl) ⟨1734351, by rfl⟩ : syracuseStep 4624937 = 3468703) B3468703
theorem B3086099 : Blo 912577 3086099 := bstep (se 1 (by rfl) ⟨2314574, by rfl⟩ : syracuseStep 3086099 = 4629149) B4629149
theorem B3086747 : Blo 912577 3086747 := bstep (se 1 (by rfl) ⟨2315060, by rfl⟩ : syracuseStep 3086747 = 4630121) B4630121
theorem B11740909 : Blo 912577 11740909 := bstep (se 3 (by rfl) ⟨2201420, by rfl⟩ : syracuseStep 11740909 = 4402841) B4402841
theorem B17154737 : Blo 912577 17154737 := bstep (se 2 (by rfl) ⟨6433026, by rfl⟩ : syracuseStep 17154737 = 12866053) B12866053
theorem B9526139 : Blo 912577 9526139 := bstep (se 1 (by rfl) ⟨7144604, by rfl⟩ : syracuseStep 9526139 = 14289209) B14289209
theorem B1369727 : Blo 912577 1369727 := bstep (se 1 (by rfl) ⟨1027295, by rfl⟩ : syracuseStep 1369727 = 2054591) B2054591
theorem B1371995 : Blo 912577 1371995 := bstep (se 1 (by rfl) ⟨1028996, by rfl⟩ : syracuseStep 1371995 = 2057993) B2057993
theorem B2061737 : Blo 912577 2061737 := bstep (se 2 (by rfl) ⟨773151, by rfl⟩ : syracuseStep 2061737 = 1546303) B1546303
theorem B4620239 : Blo 912577 4620239 := bstep (se 1 (by rfl) ⟨3465179, by rfl⟩ : syracuseStep 4620239 = 6930359) B6930359
theorem B11436491 : Blo 912577 11436491 := bstep (se 1 (by rfl) ⟨8577368, by rfl⟩ : syracuseStep 11436491 = 17154737) B17154737
theorem B3083291 : Blo 912577 3083291 := bstep (se 1 (by rfl) ⟨2312468, by rfl⟩ : syracuseStep 3083291 = 4624937) B4624937
theorem B30452507 : Blo 912577 30452507 := bstep (se 1 (by rfl) ⟨22839380, by rfl⟩ : syracuseStep 30452507 = 45678761) B45678761
theorem B4632713 : Blo 912577 4632713 := bstep (se 2 (by rfl) ⟨1737267, by rfl⟩ : syracuseStep 4632713 = 3474535) B3474535
theorem B4635305 : Blo 912577 4635305 := bstep (se 2 (by rfl) ⟨1738239, by rfl⟩ : syracuseStep 4635305 = 3476479) B3476479
theorem B15654545 : Blo 912577 15654545 := bstep (se 2 (by rfl) ⟨5870454, by rfl⟩ : syracuseStep 15654545 = 11740909) B11740909
theorem B2057399 : Blo 912577 2057399 := bstep (se 1 (by rfl) ⟨1543049, by rfl⟩ : syracuseStep 2057399 = 3086099) B3086099
theorem B2057831 : Blo 912577 2057831 := bstep (se 1 (by rfl) ⟨1543373, by rfl⟩ : syracuseStep 2057831 = 3086747) B3086747
theorem B6350759 : Blo 912577 6350759 := bstep (se 1 (by rfl) ⟨4763069, by rfl⟩ : syracuseStep 6350759 = 9526139) B9526139
theorem B913151 : Blo 912577 913151 := bstep (se 1 (by rfl) ⟨684863, by rfl⟩ : syracuseStep 913151 = 1369727) B1369727
theorem B914663 : Blo 912577 914663 := bstep (se 1 (by rfl) ⟨685997, by rfl⟩ : syracuseStep 914663 = 1371995) B1371995
theorem B1374491 : Blo 912577 1374491 := bstep (se 1 (by rfl) ⟨1030868, by rfl⟩ : syracuseStep 1374491 = 2061737) B2061737
theorem B3080159 : Blo 912577 3080159 := bstep (se 1 (by rfl) ⟨2310119, by rfl⟩ : syracuseStep 3080159 = 4620239) B4620239
theorem B3088475 : Blo 912577 3088475 := bstep (se 1 (by rfl) ⟨2316356, by rfl⟩ : syracuseStep 3088475 = 4632713) B4632713
theorem B67741429 : Blo 912577 67741429 := bstep (se 5 (by rfl) ⟨3175379, by rfl⟩ : syracuseStep 67741429 = 6350759) B6350759
theorem B3090203 : Blo 912577 3090203 := bstep (se 1 (by rfl) ⟨2317652, by rfl⟩ : syracuseStep 3090203 = 4635305) B4635305
theorem B10436363 : Blo 912577 10436363 := bstep (se 1 (by rfl) ⟨7827272, by rfl⟩ : syracuseStep 10436363 = 15654545) B15654545
theorem B20301671 : Blo 912577 20301671 := bstep (se 1 (by rfl) ⟨15226253, by rfl⟩ : syracuseStep 20301671 = 30452507) B30452507
theorem B2053439 : Blo 912577 2053439 := bstep (se 1 (by rfl) ⟨1540079, by rfl⟩ : syracuseStep 2053439 = 3080159) B3080159
theorem B7624327 : Blo 912577 7624327 := bstep (se 1 (by rfl) ⟨5718245, by rfl⟩ : syracuseStep 7624327 = 11436491) B11436491
theorem B2055527 : Blo 912577 2055527 := bstep (se 1 (by rfl) ⟨1541645, by rfl⟩ : syracuseStep 2055527 = 3083291) B3083291
theorem B1371599 : Blo 912577 1371599 := bstep (se 1 (by rfl) ⟨1028699, by rfl⟩ : syracuseStep 1371599 = 2057399) B2057399
theorem B1371887 : Blo 912577 1371887 := bstep (se 1 (by rfl) ⟨1028915, by rfl⟩ : syracuseStep 1371887 = 2057831) B2057831
theorem B916327 : Blo 912577 916327 := bstep (se 1 (by rfl) ⟨687245, by rfl⟩ : syracuseStep 916327 = 1374491) B1374491
theorem B13534447 : Blo 912577 13534447 := bstep (se 1 (by rfl) ⟨10150835, by rfl⟩ : syracuseStep 13534447 = 20301671) B20301671
theorem B10165769 : Blo 912577 10165769 := bstep (se 2 (by rfl) ⟨3812163, by rfl⟩ : syracuseStep 10165769 = 7624327) B7624327
theorem B6957575 : Blo 912577 6957575 := bstep (se 1 (by rfl) ⟨5218181, by rfl⟩ : syracuseStep 6957575 = 10436363) B10436363
theorem B90321905 : Blo 912577 90321905 := bstep (se 2 (by rfl) ⟨33870714, by rfl⟩ : syracuseStep 90321905 = 67741429) B67741429
theorem B1368959 : Blo 912577 1368959 := bstep (se 1 (by rfl) ⟨1026719, by rfl⟩ : syracuseStep 1368959 = 2053439) B2053439
theorem B1370351 : Blo 912577 1370351 := bstep (se 1 (by rfl) ⟨1027763, by rfl⟩ : syracuseStep 1370351 = 2055527) B2055527
theorem B2058983 : Blo 912577 2058983 := bstep (se 1 (by rfl) ⟨1544237, by rfl⟩ : syracuseStep 2058983 = 3088475) B3088475
theorem B2060135 : Blo 912577 2060135 := bstep (se 1 (by rfl) ⟨1545101, by rfl⟩ : syracuseStep 2060135 = 3090203) B3090203
theorem B914399 : Blo 912577 914399 := bstep (se 1 (by rfl) ⟨685799, by rfl⟩ : syracuseStep 914399 = 1371599) B1371599
theorem B914591 : Blo 912577 914591 := bstep (se 1 (by rfl) ⟨685943, by rfl⟩ : syracuseStep 914591 = 1371887) B1371887
theorem B4638383 : Blo 912577 4638383 := bstep (se 1 (by rfl) ⟨3478787, by rfl⟩ : syracuseStep 4638383 = 6957575) B6957575
theorem B60214603 : Blo 912577 60214603 := bstep (se 1 (by rfl) ⟨45160952, by rfl⟩ : syracuseStep 60214603 = 90321905) B90321905
theorem B18045929 : Blo 912577 18045929 := bstep (se 2 (by rfl) ⟨6767223, by rfl⟩ : syracuseStep 18045929 = 13534447) B13534447
theorem B6777179 : Blo 912577 6777179 := bstep (se 1 (by rfl) ⟨5082884, by rfl⟩ : syracuseStep 6777179 = 10165769) B10165769
theorem B912639 : Blo 912577 912639 := bstep (se 1 (by rfl) ⟨684479, by rfl⟩ : syracuseStep 912639 = 1368959) B1368959
theorem B913567 : Blo 912577 913567 := bstep (se 1 (by rfl) ⟨685175, by rfl⟩ : syracuseStep 913567 = 1370351) B1370351
theorem B1372655 : Blo 912577 1372655 := bstep (se 1 (by rfl) ⟨1029491, by rfl⟩ : syracuseStep 1372655 = 2058983) B2058983
theorem B1373423 : Blo 912577 1373423 := bstep (se 1 (by rfl) ⟨1030067, by rfl⟩ : syracuseStep 1373423 = 2060135) B2060135
theorem B80286137 : Blo 912577 80286137 := bstep (se 2 (by rfl) ⟨30107301, by rfl⟩ : syracuseStep 80286137 = 60214603) B60214603
theorem B12030619 : Blo 912577 12030619 := bstep (se 1 (by rfl) ⟨9022964, by rfl⟩ : syracuseStep 12030619 = 18045929) B18045929
theorem B3092255 : Blo 912577 3092255 := bstep (se 1 (by rfl) ⟨2319191, by rfl⟩ : syracuseStep 3092255 = 4638383) B4638383
theorem B4518119 : Blo 912577 4518119 := bstep (se 1 (by rfl) ⟨3388589, by rfl⟩ : syracuseStep 4518119 = 6777179) B6777179
theorem B915103 : Blo 912577 915103 := bstep (se 1 (by rfl) ⟨686327, by rfl⟩ : syracuseStep 915103 = 1372655) B1372655
theorem B915615 : Blo 912577 915615 := bstep (se 1 (by rfl) ⟨686711, by rfl⟩ : syracuseStep 915615 = 1373423) B1373423
theorem B53524091 : Blo 912577 53524091 := bstep (se 1 (by rfl) ⟨40143068, by rfl⟩ : syracuseStep 53524091 = 80286137) B80286137
theorem B16040825 : Blo 912577 16040825 := bstep (se 2 (by rfl) ⟨6015309, by rfl⟩ : syracuseStep 16040825 = 12030619) B12030619
theorem B2061503 : Blo 912577 2061503 := bstep (se 1 (by rfl) ⟨1546127, by rfl⟩ : syracuseStep 2061503 = 3092255) B3092255
theorem B3012079 : Blo 912577 3012079 := bstep (se 1 (by rfl) ⟨2259059, by rfl⟩ : syracuseStep 3012079 = 4518119) B4518119
theorem B10693883 : Blo 912577 10693883 := bstep (se 1 (by rfl) ⟨8020412, by rfl⟩ : syracuseStep 10693883 = 16040825) B16040825
theorem B4016105 : Blo 912577 4016105 := bstep (se 2 (by rfl) ⟨1506039, by rfl⟩ : syracuseStep 4016105 = 3012079) B3012079
theorem B1374335 : Blo 912577 1374335 := bstep (se 1 (by rfl) ⟨1030751, by rfl⟩ : syracuseStep 1374335 = 2061503) B2061503
theorem B35682727 : Blo 912577 35682727 := bstep (se 1 (by rfl) ⟨26762045, by rfl⟩ : syracuseStep 35682727 = 53524091) B53524091
theorem B7129255 : Blo 912577 7129255 := bstep (se 1 (by rfl) ⟨5346941, by rfl⟩ : syracuseStep 7129255 = 10693883) B10693883
theorem B2677403 : Blo 912577 2677403 := bstep (se 1 (by rfl) ⟨2008052, by rfl⟩ : syracuseStep 2677403 = 4016105) B4016105
theorem B47576969 : Blo 912577 47576969 := bstep (se 2 (by rfl) ⟨17841363, by rfl⟩ : syracuseStep 47576969 = 35682727) B35682727
theorem B916223 : Blo 912577 916223 := bstep (se 1 (by rfl) ⟨687167, by rfl⟩ : syracuseStep 916223 = 1374335) B1374335
theorem B9505673 : Blo 912577 9505673 := bstep (se 2 (by rfl) ⟨3564627, by rfl⟩ : syracuseStep 9505673 = 7129255) B7129255
theorem B1784935 : Blo 912577 1784935 := bstep (se 1 (by rfl) ⟨1338701, by rfl⟩ : syracuseStep 1784935 = 2677403) B2677403
theorem B31717979 : Blo 912577 31717979 := bstep (se 1 (by rfl) ⟨23788484, by rfl⟩ : syracuseStep 31717979 = 47576969) B47576969
theorem B21145319 : Blo 912577 21145319 := bstep (se 1 (by rfl) ⟨15858989, by rfl⟩ : syracuseStep 21145319 = 31717979) B31717979
theorem B6337115 : Blo 912577 6337115 := bstep (se 1 (by rfl) ⟨4752836, by rfl⟩ : syracuseStep 6337115 = 9505673) B9505673
theorem B9519653 : Blo 912577 9519653 := bstep (se 4 (by rfl) ⟨892467, by rfl⟩ : syracuseStep 9519653 = 1784935) B1784935
theorem B14096879 : Blo 912577 14096879 := bstep (se 1 (by rfl) ⟨10572659, by rfl⟩ : syracuseStep 14096879 = 21145319) B21145319
theorem B6346435 : Blo 912577 6346435 := bstep (se 1 (by rfl) ⟨4759826, by rfl⟩ : syracuseStep 6346435 = 9519653) B9519653
theorem B4224743 : Blo 912577 4224743 := bstep (se 1 (by rfl) ⟨3168557, by rfl⟩ : syracuseStep 4224743 = 6337115) B6337115
theorem B8461913 : Blo 912577 8461913 := bstep (se 2 (by rfl) ⟨3173217, by rfl⟩ : syracuseStep 8461913 = 6346435) B6346435
theorem B9397919 : Blo 912577 9397919 := bstep (se 1 (by rfl) ⟨7048439, by rfl⟩ : syracuseStep 9397919 = 14096879) B14096879
theorem B2816495 : Blo 912577 2816495 := bstep (se 1 (by rfl) ⟨2112371, by rfl⟩ : syracuseStep 2816495 = 4224743) B4224743
theorem B6265279 : Blo 912577 6265279 := bstep (se 1 (by rfl) ⟨4698959, by rfl⟩ : syracuseStep 6265279 = 9397919) B9397919
theorem B1877663 : Blo 912577 1877663 := bstep (se 1 (by rfl) ⟨1408247, by rfl⟩ : syracuseStep 1877663 = 2816495) B2816495
theorem B22565101 : Blo 912577 22565101 := bstep (se 3 (by rfl) ⟨4230956, by rfl⟩ : syracuseStep 22565101 = 8461913) B8461913
theorem B30086801 : Blo 912577 30086801 := bstep (se 2 (by rfl) ⟨11282550, by rfl⟩ : syracuseStep 30086801 = 22565101) B22565101
theorem B1251775 : Blo 912577 1251775 := bstep (se 1 (by rfl) ⟨938831, by rfl⟩ : syracuseStep 1251775 = 1877663) B1877663
theorem B8353705 : Blo 912577 8353705 := bstep (se 2 (by rfl) ⟨3132639, by rfl⟩ : syracuseStep 8353705 = 6265279) B6265279
theorem B20057867 : Blo 912577 20057867 := bstep (se 1 (by rfl) ⟨15043400, by rfl⟩ : syracuseStep 20057867 = 30086801) B30086801
theorem B11138273 : Blo 912577 11138273 := bstep (se 2 (by rfl) ⟨4176852, by rfl⟩ : syracuseStep 11138273 = 8353705) B8353705
theorem B1669033 : Blo 912577 1669033 := bstep (se 2 (by rfl) ⟨625887, by rfl⟩ : syracuseStep 1669033 = 1251775) B1251775
theorem B13371911 : Blo 912577 13371911 := bstep (se 1 (by rfl) ⟨10028933, by rfl⟩ : syracuseStep 13371911 = 20057867) B20057867
theorem B7425515 : Blo 912577 7425515 := bstep (se 1 (by rfl) ⟨5569136, by rfl⟩ : syracuseStep 7425515 = 11138273) B11138273
theorem B2225377 : Blo 912577 2225377 := bstep (se 2 (by rfl) ⟨834516, by rfl⟩ : syracuseStep 2225377 = 1669033) B1669033
theorem B8914607 : Blo 912577 8914607 := bstep (se 1 (by rfl) ⟨6685955, by rfl⟩ : syracuseStep 8914607 = 13371911) B13371911
theorem B4950343 : Blo 912577 4950343 := bstep (se 1 (by rfl) ⟨3712757, by rfl⟩ : syracuseStep 4950343 = 7425515) B7425515
theorem B11868677 : Blo 912577 11868677 := bstep (se 4 (by rfl) ⟨1112688, by rfl⟩ : syracuseStep 11868677 = 2225377) B2225377
theorem B5943071 : Blo 912577 5943071 := bstep (se 1 (by rfl) ⟨4457303, by rfl⟩ : syracuseStep 5943071 = 8914607) B8914607
theorem B6600457 : Blo 912577 6600457 := bstep (se 2 (by rfl) ⟨2475171, by rfl⟩ : syracuseStep 6600457 = 4950343) B4950343
theorem B7912451 : Blo 912577 7912451 := bstep (se 1 (by rfl) ⟨5934338, by rfl⟩ : syracuseStep 7912451 = 11868677) B11868677
theorem B8800609 : Blo 912577 8800609 := bstep (se 2 (by rfl) ⟨3300228, by rfl⟩ : syracuseStep 8800609 = 6600457) B6600457
theorem B3962047 : Blo 912577 3962047 := bstep (se 1 (by rfl) ⟨2971535, by rfl⟩ : syracuseStep 3962047 = 5943071) B5943071
theorem B21099869 : Blo 912577 21099869 := bstep (se 3 (by rfl) ⟨3956225, by rfl⟩ : syracuseStep 21099869 = 7912451) B7912451
theorem B11734145 : Blo 912577 11734145 := bstep (se 2 (by rfl) ⟨4400304, by rfl⟩ : syracuseStep 11734145 = 8800609) B8800609
theorem B5282729 : Blo 912577 5282729 := bstep (se 2 (by rfl) ⟨1981023, by rfl⟩ : syracuseStep 5282729 = 3962047) B3962047
theorem B14066579 : Blo 912577 14066579 := bstep (se 1 (by rfl) ⟨10549934, by rfl⟩ : syracuseStep 14066579 = 21099869) B21099869
theorem B3521819 : Blo 912577 3521819 := bstep (se 1 (by rfl) ⟨2641364, by rfl⟩ : syracuseStep 3521819 = 5282729) B5282729
theorem B7822763 : Blo 912577 7822763 := bstep (se 1 (by rfl) ⟨5867072, by rfl⟩ : syracuseStep 7822763 = 11734145) B11734145
theorem B37510877 : Blo 912577 37510877 := bstep (se 3 (by rfl) ⟨7033289, by rfl⟩ : syracuseStep 37510877 = 14066579) B14066579
theorem B5215175 : Blo 912577 5215175 := bstep (se 1 (by rfl) ⟨3911381, by rfl⟩ : syracuseStep 5215175 = 7822763) B7822763
theorem B100029005 : Blo 912577 100029005 := bstep (se 3 (by rfl) ⟨18755438, by rfl⟩ : syracuseStep 100029005 = 37510877) B37510877
theorem B2347879 : Blo 912577 2347879 := bstep (se 1 (by rfl) ⟨1760909, by rfl⟩ : syracuseStep 2347879 = 3521819) B3521819
theorem B66686003 : Blo 912577 66686003 := bstep (se 1 (by rfl) ⟨50014502, by rfl⟩ : syracuseStep 66686003 = 100029005) B100029005
theorem B3476783 : Blo 912577 3476783 := bstep (se 1 (by rfl) ⟨2607587, by rfl⟩ : syracuseStep 3476783 = 5215175) B5215175
theorem B3130505 : Blo 912577 3130505 := bstep (se 2 (by rfl) ⟨1173939, by rfl⟩ : syracuseStep 3130505 = 2347879) B2347879
theorem B2087003 : Blo 912577 2087003 := bstep (se 1 (by rfl) ⟨1565252, by rfl⟩ : syracuseStep 2087003 = 3130505) B3130505
theorem B44457335 : Blo 912577 44457335 := bstep (se 1 (by rfl) ⟨33343001, by rfl⟩ : syracuseStep 44457335 = 66686003) B66686003
theorem B2317855 : Blo 912577 2317855 := bstep (se 1 (by rfl) ⟨1738391, by rfl⟩ : syracuseStep 2317855 = 3476783) B3476783
theorem B3090473 : Blo 912577 3090473 := bstep (se 2 (by rfl) ⟨1158927, by rfl⟩ : syracuseStep 3090473 = 2317855) B2317855
theorem B29638223 : Blo 912577 29638223 := bstep (se 1 (by rfl) ⟨22228667, by rfl⟩ : syracuseStep 29638223 = 44457335) B44457335
theorem B5565341 : Blo 912577 5565341 := bstep (se 3 (by rfl) ⟨1043501, by rfl⟩ : syracuseStep 5565341 = 2087003) B2087003
theorem B3710227 : Blo 912577 3710227 := bstep (se 1 (by rfl) ⟨2782670, by rfl⟩ : syracuseStep 3710227 = 5565341) B5565341
theorem B2060315 : Blo 912577 2060315 := bstep (se 1 (by rfl) ⟨1545236, by rfl⟩ : syracuseStep 2060315 = 3090473) B3090473
theorem B19758815 : Blo 912577 19758815 := bstep (se 1 (by rfl) ⟨14819111, by rfl⟩ : syracuseStep 19758815 = 29638223) B29638223
theorem B1373543 : Blo 912577 1373543 := bstep (se 1 (by rfl) ⟨1030157, by rfl⟩ : syracuseStep 1373543 = 2060315) B2060315
theorem B4946969 : Blo 912577 4946969 := bstep (se 2 (by rfl) ⟨1855113, by rfl⟩ : syracuseStep 4946969 = 3710227) B3710227
theorem B13172543 : Blo 912577 13172543 := bstep (se 1 (by rfl) ⟨9879407, by rfl⟩ : syracuseStep 13172543 = 19758815) B19758815
theorem B3297979 : Blo 912577 3297979 := bstep (se 1 (by rfl) ⟨2473484, by rfl⟩ : syracuseStep 3297979 = 4946969) B4946969
theorem B915695 : Blo 912577 915695 := bstep (se 1 (by rfl) ⟨686771, by rfl⟩ : syracuseStep 915695 = 1373543) B1373543
theorem B8781695 : Blo 912577 8781695 := bstep (se 1 (by rfl) ⟨6586271, by rfl⟩ : syracuseStep 8781695 = 13172543) B13172543
theorem B5854463 : Blo 912577 5854463 := bstep (se 1 (by rfl) ⟨4390847, by rfl⟩ : syracuseStep 5854463 = 8781695) B8781695
theorem B17589221 : Blo 912577 17589221 := bstep (se 4 (by rfl) ⟨1648989, by rfl⟩ : syracuseStep 17589221 = 3297979) B3297979
theorem B3902975 : Blo 912577 3902975 := bstep (se 1 (by rfl) ⟨2927231, by rfl⟩ : syracuseStep 3902975 = 5854463) B5854463
theorem B11726147 : Blo 912577 11726147 := bstep (se 1 (by rfl) ⟨8794610, by rfl⟩ : syracuseStep 11726147 = 17589221) B17589221
theorem B2601983 : Blo 912577 2601983 := bstep (se 1 (by rfl) ⟨1951487, by rfl⟩ : syracuseStep 2601983 = 3902975) B3902975
theorem B7817431 : Blo 912577 7817431 := bstep (se 1 (by rfl) ⟨5863073, by rfl⟩ : syracuseStep 7817431 = 11726147) B11726147
theorem B10423241 : Blo 912577 10423241 := bstep (se 2 (by rfl) ⟨3908715, by rfl⟩ : syracuseStep 10423241 = 7817431) B7817431
theorem B6938621 : Blo 912577 6938621 := bstep (se 3 (by rfl) ⟨1300991, by rfl⟩ : syracuseStep 6938621 = 2601983) B2601983
theorem B6948827 : Blo 912577 6948827 := bstep (se 1 (by rfl) ⟨5211620, by rfl⟩ : syracuseStep 6948827 = 10423241) B10423241
theorem B4625747 : Blo 912577 4625747 := bstep (se 1 (by rfl) ⟨3469310, by rfl⟩ : syracuseStep 4625747 = 6938621) B6938621
theorem B3083831 : Blo 912577 3083831 := bstep (se 1 (by rfl) ⟨2312873, by rfl⟩ : syracuseStep 3083831 = 4625747) B4625747
theorem B4632551 : Blo 912577 4632551 := bstep (se 1 (by rfl) ⟨3474413, by rfl⟩ : syracuseStep 4632551 = 6948827) B6948827
theorem B3088367 : Blo 912577 3088367 := bstep (se 1 (by rfl) ⟨2316275, by rfl⟩ : syracuseStep 3088367 = 4632551) B4632551
theorem B2055887 : Blo 912577 2055887 := bstep (se 1 (by rfl) ⟨1541915, by rfl⟩ : syracuseStep 2055887 = 3083831) B3083831
theorem B1370591 : Blo 912577 1370591 := bstep (se 1 (by rfl) ⟨1027943, by rfl⟩ : syracuseStep 1370591 = 2055887) B2055887
theorem B2058911 : Blo 912577 2058911 := bstep (se 1 (by rfl) ⟨1544183, by rfl⟩ : syracuseStep 2058911 = 3088367) B3088367
theorem B913727 : Blo 912577 913727 := bstep (se 1 (by rfl) ⟨685295, by rfl⟩ : syracuseStep 913727 = 1370591) B1370591
theorem B1372607 : Blo 912577 1372607 := bstep (se 1 (by rfl) ⟨1029455, by rfl⟩ : syracuseStep 1372607 = 2058911) B2058911
theorem B915071 : Blo 912577 915071 := bstep (se 1 (by rfl) ⟨686303, by rfl⟩ : syracuseStep 915071 = 1372607) B1372607

theorem C0 (j : ℕ) (h1 : 228144 ≤ j) (h2 : j ≤ 228843) : Blo 912577 (4 * j + 3) := by
  interval_cases j
  · exact B912579
  · exact B912583
  · exact B912587
  · exact B912591
  · exact B912595
  · exact B912599
  · exact B912603
  · exact B912607
  · exact B912611
  · exact B912615
  · exact B912619
  · exact B912623
  · exact B912627
  · exact B912631
  · exact B912635
  · exact B912639
  · exact B912643
  · exact B912647
  · exact B912651
  · exact B912655
  · exact B912659
  · exact B912663
  · exact B912667
  · exact B912671
  · exact B912675
  · exact B912679
  · exact B912683
  · exact B912687
  · exact B912691
  · exact B912695
  · exact B912699
  · exact B912703
  · exact B912707
  · exact B912711
  · exact B912715
  · exact B912719
  · exact B912723
  · exact B912727
  · exact B912731
  · exact B912735
  · exact B912739
  · exact B912743
  · exact B912747
  · exact B912751
  · exact B912755
  · exact B912759
  · exact B912763
  · exact B912767
  · exact B912771
  · exact B912775
  · exact B912779
  · exact B912783
  · exact B912787
  · exact B912791
  · exact B912795
  · exact B912799
  · exact B912803
  · exact B912807
  · exact B912811
  · exact B912815
  · exact B912819
  · exact B912823
  · exact B912827
  · exact B912831
  · exact B912835
  · exact B912839
  · exact B912843
  · exact B912847
  · exact B912851
  · exact B912855
  · exact B912859
  · exact B912863
  · exact B912867
  · exact B912871
  · exact B912875
  · exact B912879
  · exact B912883
  · exact B912887
  · exact B912891
  · exact B912895
  · exact B912899
  · exact B912903
  · exact B912907
  · exact B912911
  · exact B912915
  · exact B912919
  · exact B912923
  · exact B912927
  · exact B912931
  · exact B912935
  · exact B912939
  · exact B912943
  · exact B912947
  · exact B912951
  · exact B912955
  · exact B912959
  · exact B912963
  · exact B912967
  · exact B912971
  · exact B912975
  · exact B912979
  · exact B912983
  · exact B912987
  · exact B912991
  · exact B912995
  · exact B912999
  · exact B913003
  · exact B913007
  · exact B913011
  · exact B913015
  · exact B913019
  · exact B913023
  · exact B913027
  · exact B913031
  · exact B913035
  · exact B913039
  · exact B913043
  · exact B913047
  · exact B913051
  · exact B913055
  · exact B913059
  · exact B913063
  · exact B913067
  · exact B913071
  · exact B913075
  · exact B913079
  · exact B913083
  · exact B913087
  · exact B913091
  · exact B913095
  · exact B913099
  · exact B913103
  · exact B913107
  · exact B913111
  · exact B913115
  · exact B913119
  · exact B913123
  · exact B913127
  · exact B913131
  · exact B913135
  · exact B913139
  · exact B913143
  · exact B913147
  · exact B913151
  · exact B913155
  · exact B913159
  · exact B913163
  · exact B913167
  · exact B913171
  · exact B913175
  · exact B913179
  · exact B913183
  · exact B913187
  · exact B913191
  · exact B913195
  · exact B913199
  · exact B913203
  · exact B913207
  · exact B913211
  · exact B913215
  · exact B913219
  · exact B913223
  · exact B913227
  · exact B913231
  · exact B913235
  · exact B913239
  · exact B913243
  · exact B913247
  · exact B913251
  · exact B913255
  · exact B913259
  · exact B913263
  · exact B913267
  · exact B913271
  · exact B913275
  · exact B913279
  · exact B913283
  · exact B913287
  · exact B913291
  · exact B913295
  · exact B913299
  · exact B913303
  · exact B913307
  · exact B913311
  · exact B913315
  · exact B913319
  · exact B913323
  · exact B913327
  · exact B913331
  · exact B913335
  · exact B913339
  · exact B913343
  · exact B913347
  · exact B913351
  · exact B913355
  · exact B913359
  · exact B913363
  · exact B913367
  · exact B913371
  · exact B913375
  · exact B913379
  · exact B913383
  · exact B913387
  · exact B913391
  · exact B913395
  · exact B913399
  · exact B913403
  · exact B913407
  · exact B913411
  · exact B913415
  · exact B913419
  · exact B913423
  · exact B913427
  · exact B913431
  · exact B913435
  · exact B913439
  · exact B913443
  · exact B913447
  · exact B913451
  · exact B913455
  · exact B913459
  · exact B913463
  · exact B913467
  · exact B913471
  · exact B913475
  · exact B913479
  · exact B913483
  · exact B913487
  · exact B913491
  · exact B913495
  · exact B913499
  · exact B913503
  · exact B913507
  · exact B913511
  · exact B913515
  · exact B913519
  · exact B913523
  · exact B913527
  · exact B913531
  · exact B913535
  · exact B913539
  · exact B913543
  · exact B913547
  · exact B913551
  · exact B913555
  · exact B913559
  · exact B913563
  · exact B913567
  · exact B913571
  · exact B913575
  · exact B913579
  · exact B913583
  · exact B913587
  · exact B913591
  · exact B913595
  · exact B913599
  · exact B913603
  · exact B913607
  · exact B913611
  · exact B913615
  · exact B913619
  · exact B913623
  · exact B913627
  · exact B913631
  · exact B913635
  · exact B913639
  · exact B913643
  · exact B913647
  · exact B913651
  · exact B913655
  · exact B913659
  · exact B913663
  · exact B913667
  · exact B913671
  · exact B913675
  · exact B913679
  · exact B913683
  · exact B913687
  · exact B913691
  · exact B913695
  · exact B913699
  · exact B913703
  · exact B913707
  · exact B913711
  · exact B913715
  · exact B913719
  · exact B913723
  · exact B913727
  · exact B913731
  · exact B913735
  · exact B913739
  · exact B913743
  · exact B913747
  · exact B913751
  · exact B913755
  · exact B913759
  · exact B913763
  · exact B913767
  · exact B913771
  · exact B913775
  · exact B913779
  · exact B913783
  · exact B913787
  · exact B913791
  · exact B913795
  · exact B913799
  · exact B913803
  · exact B913807
  · exact B913811
  · exact B913815
  · exact B913819
  · exact B913823
  · exact B913827
  · exact B913831
  · exact B913835
  · exact B913839
  · exact B913843
  · exact B913847
  · exact B913851
  · exact B913855
  · exact B913859
  · exact B913863
  · exact B913867
  · exact B913871
  · exact B913875
  · exact B913879
  · exact B913883
  · exact B913887
  · exact B913891
  · exact B913895
  · exact B913899
  · exact B913903
  · exact B913907
  · exact B913911
  · exact B913915
  · exact B913919
  · exact B913923
  · exact B913927
  · exact B913931
  · exact B913935
  · exact B913939
  · exact B913943
  · exact B913947
  · exact B913951
  · exact B913955
  · exact B913959
  · exact B913963
  · exact B913967
  · exact B913971
  · exact B913975
  · exact B913979
  · exact B913983
  · exact B913987
  · exact B913991
  · exact B913995
  · exact B913999
  · exact B914003
  · exact B914007
  · exact B914011
  · exact B914015
  · exact B914019
  · exact B914023
  · exact B914027
  · exact B914031
  · exact B914035
  · exact B914039
  · exact B914043
  · exact B914047
  · exact B914051
  · exact B914055
  · exact B914059
  · exact B914063
  · exact B914067
  · exact B914071
  · exact B914075
  · exact B914079
  · exact B914083
  · exact B914087
  · exact B914091
  · exact B914095
  · exact B914099
  · exact B914103
  · exact B914107
  · exact B914111
  · exact B914115
  · exact B914119
  · exact B914123
  · exact B914127
  · exact B914131
  · exact B914135
  · exact B914139
  · exact B914143
  · exact B914147
  · exact B914151
  · exact B914155
  · exact B914159
  · exact B914163
  · exact B914167
  · exact B914171
  · exact B914175
  · exact B914179
  · exact B914183
  · exact B914187
  · exact B914191
  · exact B914195
  · exact B914199
  · exact B914203
  · exact B914207
  · exact B914211
  · exact B914215
  · exact B914219
  · exact B914223
  · exact B914227
  · exact B914231
  · exact B914235
  · exact B914239
  · exact B914243
  · exact B914247
  · exact B914251
  · exact B914255
  · exact B914259
  · exact B914263
  · exact B914267
  · exact B914271
  · exact B914275
  · exact B914279
  · exact B914283
  · exact B914287
  · exact B914291
  · exact B914295
  · exact B914299
  · exact B914303
  · exact B914307
  · exact B914311
  · exact B914315
  · exact B914319
  · exact B914323
  · exact B914327
  · exact B914331
  · exact B914335
  · exact B914339
  · exact B914343
  · exact B914347
  · exact B914351
  · exact B914355
  · exact B914359
  · exact B914363
  · exact B914367
  · exact B914371
  · exact B914375
  · exact B914379
  · exact B914383
  · exact B914387
  · exact B914391
  · exact B914395
  · exact B914399
  · exact B914403
  · exact B914407
  · exact B914411
  · exact B914415
  · exact B914419
  · exact B914423
  · exact B914427
  · exact B914431
  · exact B914435
  · exact B914439
  · exact B914443
  · exact B914447
  · exact B914451
  · exact B914455
  · exact B914459
  · exact B914463
  · exact B914467
  · exact B914471
  · exact B914475
  · exact B914479
  · exact B914483
  · exact B914487
  · exact B914491
  · exact B914495
  · exact B914499
  · exact B914503
  · exact B914507
  · exact B914511
  · exact B914515
  · exact B914519
  · exact B914523
  · exact B914527
  · exact B914531
  · exact B914535
  · exact B914539
  · exact B914543
  · exact B914547
  · exact B914551
  · exact B914555
  · exact B914559
  · exact B914563
  · exact B914567
  · exact B914571
  · exact B914575
  · exact B914579
  · exact B914583
  · exact B914587
  · exact B914591
  · exact B914595
  · exact B914599
  · exact B914603
  · exact B914607
  · exact B914611
  · exact B914615
  · exact B914619
  · exact B914623
  · exact B914627
  · exact B914631
  · exact B914635
  · exact B914639
  · exact B914643
  · exact B914647
  · exact B914651
  · exact B914655
  · exact B914659
  · exact B914663
  · exact B914667
  · exact B914671
  · exact B914675
  · exact B914679
  · exact B914683
  · exact B914687
  · exact B914691
  · exact B914695
  · exact B914699
  · exact B914703
  · exact B914707
  · exact B914711
  · exact B914715
  · exact B914719
  · exact B914723
  · exact B914727
  · exact B914731
  · exact B914735
  · exact B914739
  · exact B914743
  · exact B914747
  · exact B914751
  · exact B914755
  · exact B914759
  · exact B914763
  · exact B914767
  · exact B914771
  · exact B914775
  · exact B914779
  · exact B914783
  · exact B914787
  · exact B914791
  · exact B914795
  · exact B914799
  · exact B914803
  · exact B914807
  · exact B914811
  · exact B914815
  · exact B914819
  · exact B914823
  · exact B914827
  · exact B914831
  · exact B914835
  · exact B914839
  · exact B914843
  · exact B914847
  · exact B914851
  · exact B914855
  · exact B914859
  · exact B914863
  · exact B914867
  · exact B914871
  · exact B914875
  · exact B914879
  · exact B914883
  · exact B914887
  · exact B914891
  · exact B914895
  · exact B914899
  · exact B914903
  · exact B914907
  · exact B914911
  · exact B914915
  · exact B914919
  · exact B914923
  · exact B914927
  · exact B914931
  · exact B914935
  · exact B914939
  · exact B914943
  · exact B914947
  · exact B914951
  · exact B914955
  · exact B914959
  · exact B914963
  · exact B914967
  · exact B914971
  · exact B914975
  · exact B914979
  · exact B914983
  · exact B914987
  · exact B914991
  · exact B914995
  · exact B914999
  · exact B915003
  · exact B915007
  · exact B915011
  · exact B915015
  · exact B915019
  · exact B915023
  · exact B915027
  · exact B915031
  · exact B915035
  · exact B915039
  · exact B915043
  · exact B915047
  · exact B915051
  · exact B915055
  · exact B915059
  · exact B915063
  · exact B915067
  · exact B915071
  · exact B915075
  · exact B915079
  · exact B915083
  · exact B915087
  · exact B915091
  · exact B915095
  · exact B915099
  · exact B915103
  · exact B915107
  · exact B915111
  · exact B915115
  · exact B915119
  · exact B915123
  · exact B915127
  · exact B915131
  · exact B915135
  · exact B915139
  · exact B915143
  · exact B915147
  · exact B915151
  · exact B915155
  · exact B915159
  · exact B915163
  · exact B915167
  · exact B915171
  · exact B915175
  · exact B915179
  · exact B915183
  · exact B915187
  · exact B915191
  · exact B915195
  · exact B915199
  · exact B915203
  · exact B915207
  · exact B915211
  · exact B915215
  · exact B915219
  · exact B915223
  · exact B915227
  · exact B915231
  · exact B915235
  · exact B915239
  · exact B915243
  · exact B915247
  · exact B915251
  · exact B915255
  · exact B915259
  · exact B915263
  · exact B915267
  · exact B915271
  · exact B915275
  · exact B915279
  · exact B915283
  · exact B915287
  · exact B915291
  · exact B915295
  · exact B915299
  · exact B915303
  · exact B915307
  · exact B915311
  · exact B915315
  · exact B915319
  · exact B915323
  · exact B915327
  · exact B915331
  · exact B915335
  · exact B915339
  · exact B915343
  · exact B915347
  · exact B915351
  · exact B915355
  · exact B915359
  · exact B915363
  · exact B915367
  · exact B915371
  · exact B915375

theorem C1 (j : ℕ) (h1 : 228844 ≤ j) (h2 : j ≤ 229143) : Blo 912577 (4 * j + 3) := by
  interval_cases j
  · exact B915379
  · exact B915383
  · exact B915387
  · exact B915391
  · exact B915395
  · exact B915399
  · exact B915403
  · exact B915407
  · exact B915411
  · exact B915415
  · exact B915419
  · exact B915423
  · exact B915427
  · exact B915431
  · exact B915435
  · exact B915439
  · exact B915443
  · exact B915447
  · exact B915451
  · exact B915455
  · exact B915459
  · exact B915463
  · exact B915467
  · exact B915471
  · exact B915475
  · exact B915479
  · exact B915483
  · exact B915487
  · exact B915491
  · exact B915495
  · exact B915499
  · exact B915503
  · exact B915507
  · exact B915511
  · exact B915515
  · exact B915519
  · exact B915523
  · exact B915527
  · exact B915531
  · exact B915535
  · exact B915539
  · exact B915543
  · exact B915547
  · exact B915551
  · exact B915555
  · exact B915559
  · exact B915563
  · exact B915567
  · exact B915571
  · exact B915575
  · exact B915579
  · exact B915583
  · exact B915587
  · exact B915591
  · exact B915595
  · exact B915599
  · exact B915603
  · exact B915607
  · exact B915611
  · exact B915615
  · exact B915619
  · exact B915623
  · exact B915627
  · exact B915631
  · exact B915635
  · exact B915639
  · exact B915643
  · exact B915647
  · exact B915651
  · exact B915655
  · exact B915659
  · exact B915663
  · exact B915667
  · exact B915671
  · exact B915675
  · exact B915679
  · exact B915683
  · exact B915687
  · exact B915691
  · exact B915695
  · exact B915699
  · exact B915703
  · exact B915707
  · exact B915711
  · exact B915715
  · exact B915719
  · exact B915723
  · exact B915727
  · exact B915731
  · exact B915735
  · exact B915739
  · exact B915743
  · exact B915747
  · exact B915751
  · exact B915755
  · exact B915759
  · exact B915763
  · exact B915767
  · exact B915771
  · exact B915775
  · exact B915779
  · exact B915783
  · exact B915787
  · exact B915791
  · exact B915795
  · exact B915799
  · exact B915803
  · exact B915807
  · exact B915811
  · exact B915815
  · exact B915819
  · exact B915823
  · exact B915827
  · exact B915831
  · exact B915835
  · exact B915839
  · exact B915843
  · exact B915847
  · exact B915851
  · exact B915855
  · exact B915859
  · exact B915863
  · exact B915867
  · exact B915871
  · exact B915875
  · exact B915879
  · exact B915883
  · exact B915887
  · exact B915891
  · exact B915895
  · exact B915899
  · exact B915903
  · exact B915907
  · exact B915911
  · exact B915915
  · exact B915919
  · exact B915923
  · exact B915927
  · exact B915931
  · exact B915935
  · exact B915939
  · exact B915943
  · exact B915947
  · exact B915951
  · exact B915955
  · exact B915959
  · exact B915963
  · exact B915967
  · exact B915971
  · exact B915975
  · exact B915979
  · exact B915983
  · exact B915987
  · exact B915991
  · exact B915995
  · exact B915999
  · exact B916003
  · exact B916007
  · exact B916011
  · exact B916015
  · exact B916019
  · exact B916023
  · exact B916027
  · exact B916031
  · exact B916035
  · exact B916039
  · exact B916043
  · exact B916047
  · exact B916051
  · exact B916055
  · exact B916059
  · exact B916063
  · exact B916067
  · exact B916071
  · exact B916075
  · exact B916079
  · exact B916083
  · exact B916087
  · exact B916091
  · exact B916095
  · exact B916099
  · exact B916103
  · exact B916107
  · exact B916111
  · exact B916115
  · exact B916119
  · exact B916123
  · exact B916127
  · exact B916131
  · exact B916135
  · exact B916139
  · exact B916143
  · exact B916147
  · exact B916151
  · exact B916155
  · exact B916159
  · exact B916163
  · exact B916167
  · exact B916171
  · exact B916175
  · exact B916179
  · exact B916183
  · exact B916187
  · exact B916191
  · exact B916195
  · exact B916199
  · exact B916203
  · exact B916207
  · exact B916211
  · exact B916215
  · exact B916219
  · exact B916223
  · exact B916227
  · exact B916231
  · exact B916235
  · exact B916239
  · exact B916243
  · exact B916247
  · exact B916251
  · exact B916255
  · exact B916259
  · exact B916263
  · exact B916267
  · exact B916271
  · exact B916275
  · exact B916279
  · exact B916283
  · exact B916287
  · exact B916291
  · exact B916295
  · exact B916299
  · exact B916303
  · exact B916307
  · exact B916311
  · exact B916315
  · exact B916319
  · exact B916323
  · exact B916327
  · exact B916331
  · exact B916335
  · exact B916339
  · exact B916343
  · exact B916347
  · exact B916351
  · exact B916355
  · exact B916359
  · exact B916363
  · exact B916367
  · exact B916371
  · exact B916375
  · exact B916379
  · exact B916383
  · exact B916387
  · exact B916391
  · exact B916395
  · exact B916399
  · exact B916403
  · exact B916407
  · exact B916411
  · exact B916415
  · exact B916419
  · exact B916423
  · exact B916427
  · exact B916431
  · exact B916435
  · exact B916439
  · exact B916443
  · exact B916447
  · exact B916451
  · exact B916455
  · exact B916459
  · exact B916463
  · exact B916467
  · exact B916471
  · exact B916475
  · exact B916479
  · exact B916483
  · exact B916487
  · exact B916491
  · exact B916495
  · exact B916499
  · exact B916503
  · exact B916507
  · exact B916511
  · exact B916515
  · exact B916519
  · exact B916523
  · exact B916527
  · exact B916531
  · exact B916535
  · exact B916539
  · exact B916543
  · exact B916547
  · exact B916551
  · exact B916555
  · exact B916559
  · exact B916563
  · exact B916567
  · exact B916571
  · exact B916575

theorem solution (m : ℕ) (hlo : 912577 ≤ m) (hhi : m ≤ 916577) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 228144 ≤ j := by omega
    have hj2 : j ≤ 229143 := by omega
    have hb : Blo 912577 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 228844 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
