-- Prove2me | solution 1 for syracuse_descends_range_1024605_1028605
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:20.889947+00:00
-- url     : https://prove2.me/submissions/44f53211-d8e0-4902-b0ae-a84c44704cb7

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


theorem B1540109 : Blo 1024605 1540109 := bbase (se 3 (by rfl) ⟨288770, by rfl⟩ : syracuseStep 1540109 = 577541) (by norm_num)
theorem B1540133 : Blo 1024605 1540133 := bbase (se 4 (by rfl) ⟨144387, by rfl⟩ : syracuseStep 1540133 = 288775) (by norm_num)
theorem B4390949 : Blo 1024605 4390949 := bbase (se 4 (by rfl) ⟨411651, by rfl⟩ : syracuseStep 4390949 = 823303) (by norm_num)
theorem B1540157 : Blo 1024605 1540157 := bbase (se 3 (by rfl) ⟨288779, by rfl⟩ : syracuseStep 1540157 = 577559) (by norm_num)
theorem B1540181 : Blo 1024605 1540181 := bbase (se 8 (by rfl) ⟨9024, by rfl⟩ : syracuseStep 1540181 = 18049) (by norm_num)
theorem B1409125 : Blo 1024605 1409125 := bbase (se 4 (by rfl) ⟨132105, by rfl⟩ : syracuseStep 1409125 = 264211) (by norm_num)
theorem B1540205 : Blo 1024605 1540205 := bbase (se 3 (by rfl) ⟨288788, by rfl⟩ : syracuseStep 1540205 = 577577) (by norm_num)
theorem B1540229 : Blo 1024605 1540229 := bbase (se 4 (by rfl) ⟨144396, by rfl⟩ : syracuseStep 1540229 = 288793) (by norm_num)
theorem B1540253 : Blo 1024605 1540253 := bbase (se 3 (by rfl) ⟨288797, by rfl⟩ : syracuseStep 1540253 = 577595) (by norm_num)
theorem B1540277 : Blo 1024605 1540277 := bbase (se 5 (by rfl) ⟨72200, by rfl⟩ : syracuseStep 1540277 = 144401) (by norm_num)
theorem B3899573 : Blo 1024605 3899573 := bbase (se 5 (by rfl) ⟨182792, by rfl⟩ : syracuseStep 3899573 = 365585) (by norm_num)
theorem B1540301 : Blo 1024605 1540301 := bbase (se 3 (by rfl) ⟨288806, by rfl⟩ : syracuseStep 1540301 = 577613) (by norm_num)
theorem B1540325 : Blo 1024605 1540325 := bbase (se 4 (by rfl) ⟨144405, by rfl⟩ : syracuseStep 1540325 = 288811) (by norm_num)
theorem B1540349 : Blo 1024605 1540349 := bbase (se 3 (by rfl) ⟨288815, by rfl⟩ : syracuseStep 1540349 = 577631) (by norm_num)
theorem B1540373 : Blo 1024605 1540373 := bbase (se 6 (by rfl) ⟨36102, by rfl⟩ : syracuseStep 1540373 = 72205) (by norm_num)
theorem B2195741 : Blo 1024605 2195741 := bbase (se 3 (by rfl) ⟨411701, by rfl⟩ : syracuseStep 2195741 = 823403) (by norm_num)
theorem B1540397 : Blo 1024605 1540397 := bbase (se 3 (by rfl) ⟨288824, by rfl⟩ : syracuseStep 1540397 = 577649) (by norm_num)
theorem B1540421 : Blo 1024605 1540421 := bbase (se 4 (by rfl) ⟨144414, by rfl⟩ : syracuseStep 1540421 = 288829) (by norm_num)
theorem B1540445 : Blo 1024605 1540445 := bbase (se 3 (by rfl) ⟨288833, by rfl⟩ : syracuseStep 1540445 = 577667) (by norm_num)
theorem B1540469 : Blo 1024605 1540469 := bbase (se 5 (by rfl) ⟨72209, by rfl⟩ : syracuseStep 1540469 = 144419) (by norm_num)
theorem B1540493 : Blo 1024605 1540493 := bbase (se 3 (by rfl) ⟨288842, by rfl⟩ : syracuseStep 1540493 = 577685) (by norm_num)
theorem B1540517 : Blo 1024605 1540517 := bbase (se 4 (by rfl) ⟨144423, by rfl⟩ : syracuseStep 1540517 = 288847) (by norm_num)
theorem B2195885 : Blo 1024605 2195885 := bbase (se 3 (by rfl) ⟨411728, by rfl⟩ : syracuseStep 2195885 = 823457) (by norm_num)
theorem B1540541 : Blo 1024605 1540541 := bbase (se 3 (by rfl) ⟨288851, by rfl⟩ : syracuseStep 1540541 = 577703) (by norm_num)
theorem B1540565 : Blo 1024605 1540565 := bbase (se 7 (by rfl) ⟨18053, by rfl⟩ : syracuseStep 1540565 = 36107) (by norm_num)
theorem B1540589 : Blo 1024605 1540589 := bbase (se 3 (by rfl) ⟨288860, by rfl⟩ : syracuseStep 1540589 = 577721) (by norm_num)
theorem B1540613 : Blo 1024605 1540613 := bbase (se 4 (by rfl) ⟨144432, by rfl⟩ : syracuseStep 1540613 = 288865) (by norm_num)
theorem B1540637 : Blo 1024605 1540637 := bbase (se 3 (by rfl) ⟨288869, by rfl⟩ : syracuseStep 1540637 = 577739) (by norm_num)
theorem B1540661 : Blo 1024605 1540661 := bbase (se 5 (by rfl) ⟨72218, by rfl⟩ : syracuseStep 1540661 = 144437) (by norm_num)
theorem B1540685 : Blo 1024605 1540685 := bbase (se 3 (by rfl) ⟨288878, by rfl⟩ : syracuseStep 1540685 = 577757) (by norm_num)
theorem B1540709 : Blo 1024605 1540709 := bbase (se 4 (by rfl) ⟨144441, by rfl⟩ : syracuseStep 1540709 = 288883) (by norm_num)
theorem B1540733 : Blo 1024605 1540733 := bbase (se 3 (by rfl) ⟨288887, by rfl⟩ : syracuseStep 1540733 = 577775) (by norm_num)
theorem B1540757 : Blo 1024605 1540757 := bbase (se 6 (by rfl) ⟨36111, by rfl⟩ : syracuseStep 1540757 = 72223) (by norm_num)
theorem B1540781 : Blo 1024605 1540781 := bbase (se 3 (by rfl) ⟨288896, by rfl⟩ : syracuseStep 1540781 = 577793) (by norm_num)
theorem B1540805 : Blo 1024605 1540805 := bbase (se 4 (by rfl) ⟨144450, by rfl⟩ : syracuseStep 1540805 = 288901) (by norm_num)
theorem B1540829 : Blo 1024605 1540829 := bbase (se 3 (by rfl) ⟨288905, by rfl⟩ : syracuseStep 1540829 = 577811) (by norm_num)
theorem B1540853 : Blo 1024605 1540853 := bbase (se 5 (by rfl) ⟨72227, by rfl⟩ : syracuseStep 1540853 = 144455) (by norm_num)
theorem B1540877 : Blo 1024605 1540877 := bbase (se 3 (by rfl) ⟨288914, by rfl⟩ : syracuseStep 1540877 = 577829) (by norm_num)
theorem B1540901 : Blo 1024605 1540901 := bbase (se 4 (by rfl) ⟨144459, by rfl⟩ : syracuseStep 1540901 = 288919) (by norm_num)
theorem B1540925 : Blo 1024605 1540925 := bbase (se 3 (by rfl) ⟨288923, by rfl⟩ : syracuseStep 1540925 = 577847) (by norm_num)
theorem B1540949 : Blo 1024605 1540949 := bbase (se 9 (by rfl) ⟨4514, by rfl⟩ : syracuseStep 1540949 = 9029) (by norm_num)
theorem B1540973 : Blo 1024605 1540973 := bbase (se 3 (by rfl) ⟨288932, by rfl⟩ : syracuseStep 1540973 = 577865) (by norm_num)
theorem B4752245 : Blo 1024605 4752245 := bbase (se 5 (by rfl) ⟨222761, by rfl⟩ : syracuseStep 4752245 = 445523) (by norm_num)
theorem B1540997 : Blo 1024605 1540997 := bbase (se 4 (by rfl) ⟨144468, by rfl⟩ : syracuseStep 1540997 = 288937) (by norm_num)
theorem B1541021 : Blo 1024605 1541021 := bbase (se 3 (by rfl) ⟨288941, by rfl⟩ : syracuseStep 1541021 = 577883) (by norm_num)
theorem B1541045 : Blo 1024605 1541045 := bbase (se 5 (by rfl) ⟨72236, by rfl⟩ : syracuseStep 1541045 = 144473) (by norm_num)
theorem B1541069 : Blo 1024605 1541069 := bbase (se 3 (by rfl) ⟨288950, by rfl⟩ : syracuseStep 1541069 = 577901) (by norm_num)
theorem B1541093 : Blo 1024605 1541093 := bbase (se 4 (by rfl) ⟨144477, by rfl⟩ : syracuseStep 1541093 = 288955) (by norm_num)
theorem B1541117 : Blo 1024605 1541117 := bbase (se 3 (by rfl) ⟨288959, by rfl⟩ : syracuseStep 1541117 = 577919) (by norm_num)
theorem B4391941 : Blo 1024605 4391941 := bbase (se 4 (by rfl) ⟨411744, by rfl⟩ : syracuseStep 4391941 = 823489) (by norm_num)
theorem B1541141 : Blo 1024605 1541141 := bbase (se 6 (by rfl) ⟨36120, by rfl⟩ : syracuseStep 1541141 = 72241) (by norm_num)
theorem B1541165 : Blo 1024605 1541165 := bbase (se 3 (by rfl) ⟨288968, by rfl⟩ : syracuseStep 1541165 = 577937) (by norm_num)
theorem B1541189 : Blo 1024605 1541189 := bbase (se 4 (by rfl) ⟨144486, by rfl⟩ : syracuseStep 1541189 = 288973) (by norm_num)
theorem B1541213 : Blo 1024605 1541213 := bbase (se 3 (by rfl) ⟨288977, by rfl⟩ : syracuseStep 1541213 = 577955) (by norm_num)
theorem B1541237 : Blo 1024605 1541237 := bbase (se 5 (by rfl) ⟨72245, by rfl⟩ : syracuseStep 1541237 = 144491) (by norm_num)
theorem B1541261 : Blo 1024605 1541261 := bbase (se 3 (by rfl) ⟨288986, by rfl⟩ : syracuseStep 1541261 = 577973) (by norm_num)
theorem B9864341 : Blo 1024605 9864341 := bbase (se 6 (by rfl) ⟨231195, by rfl⟩ : syracuseStep 9864341 = 462391) (by norm_num)
theorem B5276821 : Blo 1024605 5276821 := bbase (se 6 (by rfl) ⟨123675, by rfl⟩ : syracuseStep 5276821 = 247351) (by norm_num)
theorem B2196629 : Blo 1024605 2196629 := bbase (se 6 (by rfl) ⟨51483, by rfl⟩ : syracuseStep 2196629 = 102967) (by norm_num)
theorem B1541285 : Blo 1024605 1541285 := bbase (se 4 (by rfl) ⟨144495, by rfl⟩ : syracuseStep 1541285 = 288991) (by norm_num)
theorem B1541309 : Blo 1024605 1541309 := bbase (se 3 (by rfl) ⟨288995, by rfl⟩ : syracuseStep 1541309 = 577991) (by norm_num)
theorem B1541333 : Blo 1024605 1541333 := bbase (se 7 (by rfl) ⟨18062, by rfl⟩ : syracuseStep 1541333 = 36125) (by norm_num)
theorem B1541357 : Blo 1024605 1541357 := bbase (se 3 (by rfl) ⟨289004, by rfl⟩ : syracuseStep 1541357 = 578009) (by norm_num)
theorem B1541381 : Blo 1024605 1541381 := bbase (se 4 (by rfl) ⟨144504, by rfl⟩ : syracuseStep 1541381 = 289009) (by norm_num)
theorem B1541405 : Blo 1024605 1541405 := bbase (se 3 (by rfl) ⟨289013, by rfl⟩ : syracuseStep 1541405 = 578027) (by norm_num)
theorem B1541429 : Blo 1024605 1541429 := bbase (se 5 (by rfl) ⟨72254, by rfl⟩ : syracuseStep 1541429 = 144509) (by norm_num)
theorem B5276981 : Blo 1024605 5276981 := bbase (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) (by norm_num)
theorem B1541453 : Blo 1024605 1541453 := bbase (se 3 (by rfl) ⟨289022, by rfl⟩ : syracuseStep 1541453 = 578045) (by norm_num)
theorem B3900757 : Blo 1024605 3900757 := bbase (se 12 (by rfl) ⟨1428, by rfl⟩ : syracuseStep 3900757 = 2857) (by norm_num)
theorem B1541477 : Blo 1024605 1541477 := bbase (se 4 (by rfl) ⟨144513, by rfl⟩ : syracuseStep 1541477 = 289027) (by norm_num)
theorem B1541501 : Blo 1024605 1541501 := bbase (se 3 (by rfl) ⟨289031, by rfl⟩ : syracuseStep 1541501 = 578063) (by norm_num)
theorem B1541525 : Blo 1024605 1541525 := bbase (se 6 (by rfl) ⟨36129, by rfl⟩ : syracuseStep 1541525 = 72259) (by norm_num)
theorem B1541549 : Blo 1024605 1541549 := bbase (se 3 (by rfl) ⟨289040, by rfl⟩ : syracuseStep 1541549 = 578081) (by norm_num)
theorem B1541573 : Blo 1024605 1541573 := bbase (se 4 (by rfl) ⟨144522, by rfl⟩ : syracuseStep 1541573 = 289045) (by norm_num)
theorem B1541597 : Blo 1024605 1541597 := bbase (se 3 (by rfl) ⟨289049, by rfl⟩ : syracuseStep 1541597 = 578099) (by norm_num)
theorem B1541621 : Blo 1024605 1541621 := bbase (se 5 (by rfl) ⟨72263, by rfl⟩ : syracuseStep 1541621 = 144527) (by norm_num)
theorem B1541645 : Blo 1024605 1541645 := bbase (se 3 (by rfl) ⟨289058, by rfl⟩ : syracuseStep 1541645 = 578117) (by norm_num)
theorem B11240981 : Blo 1024605 11240981 := bbase (se 6 (by rfl) ⟨263460, by rfl⟩ : syracuseStep 11240981 = 526921) (by norm_num)
theorem B1541669 : Blo 1024605 1541669 := bbase (se 4 (by rfl) ⟨144531, by rfl⟩ : syracuseStep 1541669 = 289063) (by norm_num)
theorem B1541693 : Blo 1024605 1541693 := bbase (se 3 (by rfl) ⟨289067, by rfl⟩ : syracuseStep 1541693 = 578135) (by norm_num)
theorem B3507781 : Blo 1024605 3507781 := bbase (se 4 (by rfl) ⟨328854, by rfl⟩ : syracuseStep 3507781 = 657709) (by norm_num)
theorem B1541717 : Blo 1024605 1541717 := bbase (se 8 (by rfl) ⟨9033, by rfl⟩ : syracuseStep 1541717 = 18067) (by norm_num)
theorem B1541741 : Blo 1024605 1541741 := bbase (se 3 (by rfl) ⟨289076, by rfl⟩ : syracuseStep 1541741 = 578153) (by norm_num)
theorem B3901061 : Blo 1024605 3901061 := bbase (se 4 (by rfl) ⟨365724, by rfl⟩ : syracuseStep 3901061 = 731449) (by norm_num)
theorem B1541765 : Blo 1024605 1541765 := bbase (se 4 (by rfl) ⟨144540, by rfl⟩ : syracuseStep 1541765 = 289081) (by norm_num)
theorem B1541789 : Blo 1024605 1541789 := bbase (se 3 (by rfl) ⟨289085, by rfl⟩ : syracuseStep 1541789 = 578171) (by norm_num)
theorem B1541813 : Blo 1024605 1541813 := bbase (se 5 (by rfl) ⟨72272, by rfl⟩ : syracuseStep 1541813 = 144545) (by norm_num)
theorem B1541837 : Blo 1024605 1541837 := bbase (se 3 (by rfl) ⟨289094, by rfl⟩ : syracuseStep 1541837 = 578189) (by norm_num)
theorem B1541861 : Blo 1024605 1541861 := bbase (se 4 (by rfl) ⟨144549, by rfl⟩ : syracuseStep 1541861 = 289099) (by norm_num)
theorem B1541885 : Blo 1024605 1541885 := bbase (se 3 (by rfl) ⟨289103, by rfl⟩ : syracuseStep 1541885 = 578207) (by norm_num)
theorem B1541909 : Blo 1024605 1541909 := bbase (se 6 (by rfl) ⟨36138, by rfl⟩ : syracuseStep 1541909 = 72277) (by norm_num)
theorem B1541933 : Blo 1024605 1541933 := bbase (se 3 (by rfl) ⟨289112, by rfl⟩ : syracuseStep 1541933 = 578225) (by norm_num)
theorem B1541957 : Blo 1024605 1541957 := bbase (se 4 (by rfl) ⟨144558, by rfl⟩ : syracuseStep 1541957 = 289117) (by norm_num)
theorem B2000717 : Blo 1024605 2000717 := bbase (se 3 (by rfl) ⟨375134, by rfl⟩ : syracuseStep 2000717 = 750269) (by norm_num)
theorem B1541981 : Blo 1024605 1541981 := bbase (se 3 (by rfl) ⟨289121, by rfl⟩ : syracuseStep 1541981 = 578243) (by norm_num)
theorem B4687733 : Blo 1024605 4687733 := bbase (se 5 (by rfl) ⟨219737, by rfl⟩ : syracuseStep 4687733 = 439475) (by norm_num)
theorem B1542005 : Blo 1024605 1542005 := bbase (se 5 (by rfl) ⟨72281, by rfl⟩ : syracuseStep 1542005 = 144563) (by norm_num)
theorem B1542029 : Blo 1024605 1542029 := bbase (se 3 (by rfl) ⟨289130, by rfl⟩ : syracuseStep 1542029 = 578261) (by norm_num)
theorem B1542053 : Blo 1024605 1542053 := bbase (se 4 (by rfl) ⟨144567, by rfl⟩ : syracuseStep 1542053 = 289135) (by norm_num)
theorem B1542077 : Blo 1024605 1542077 := bbase (se 3 (by rfl) ⟨289139, by rfl⟩ : syracuseStep 1542077 = 578279) (by norm_num)
theorem B1542101 : Blo 1024605 1542101 := bbase (se 7 (by rfl) ⟨18071, by rfl⟩ : syracuseStep 1542101 = 36143) (by norm_num)
theorem B1542125 : Blo 1024605 1542125 := bbase (se 3 (by rfl) ⟨289148, by rfl⟩ : syracuseStep 1542125 = 578297) (by norm_num)
theorem B1542149 : Blo 1024605 1542149 := bbase (se 4 (by rfl) ⟨144576, by rfl⟩ : syracuseStep 1542149 = 289153) (by norm_num)
theorem B1542173 : Blo 1024605 1542173 := bbase (se 3 (by rfl) ⟨289157, by rfl⟩ : syracuseStep 1542173 = 578315) (by norm_num)
theorem B1542197 : Blo 1024605 1542197 := bbase (se 5 (by rfl) ⟨72290, by rfl⟩ : syracuseStep 1542197 = 144581) (by norm_num)
theorem B1542221 : Blo 1024605 1542221 := bbase (se 3 (by rfl) ⟨289166, by rfl⟩ : syracuseStep 1542221 = 578333) (by norm_num)
theorem B1542245 : Blo 1024605 1542245 := bbase (se 4 (by rfl) ⟨144585, by rfl⟩ : syracuseStep 1542245 = 289171) (by norm_num)
theorem B1542269 : Blo 1024605 1542269 := bbase (se 3 (by rfl) ⟨289175, by rfl⟩ : syracuseStep 1542269 = 578351) (by norm_num)
theorem B1542293 : Blo 1024605 1542293 := bbase (se 6 (by rfl) ⟨36147, by rfl⟩ : syracuseStep 1542293 = 72295) (by norm_num)
theorem B1542317 : Blo 1024605 1542317 := bbase (se 3 (by rfl) ⟨289184, by rfl⟩ : syracuseStep 1542317 = 578369) (by norm_num)
theorem B1542341 : Blo 1024605 1542341 := bbase (se 4 (by rfl) ⟨144594, by rfl⟩ : syracuseStep 1542341 = 289189) (by norm_num)
theorem B8784085 : Blo 1024605 8784085 := bbase (se 7 (by rfl) ⟨102938, by rfl⟩ : syracuseStep 8784085 = 205877) (by norm_num)
theorem B1542365 : Blo 1024605 1542365 := bbase (se 3 (by rfl) ⟨289193, by rfl⟩ : syracuseStep 1542365 = 578387) (by norm_num)
theorem B1542389 : Blo 1024605 1542389 := bbase (se 5 (by rfl) ⟨72299, by rfl⟩ : syracuseStep 1542389 = 144599) (by norm_num)
theorem B1542413 : Blo 1024605 1542413 := bbase (se 3 (by rfl) ⟨289202, by rfl⟩ : syracuseStep 1542413 = 578405) (by norm_num)
theorem B1542437 : Blo 1024605 1542437 := bbase (se 4 (by rfl) ⟨144603, by rfl⟩ : syracuseStep 1542437 = 289207) (by norm_num)
theorem B1542461 : Blo 1024605 1542461 := bbase (se 3 (by rfl) ⟨289211, by rfl⟩ : syracuseStep 1542461 = 578423) (by norm_num)
theorem B1542485 : Blo 1024605 1542485 := bbase (se 10 (by rfl) ⟨2259, by rfl⟩ : syracuseStep 1542485 = 4519) (by norm_num)
theorem B1542509 : Blo 1024605 1542509 := bbase (se 3 (by rfl) ⟨289220, by rfl⟩ : syracuseStep 1542509 = 578441) (by norm_num)
theorem B1542533 : Blo 1024605 1542533 := bbase (se 4 (by rfl) ⟨144612, by rfl⟩ : syracuseStep 1542533 = 289225) (by norm_num)
theorem B1542557 : Blo 1024605 1542557 := bbase (se 3 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 1542557 = 578459) (by norm_num)
theorem B1542581 : Blo 1024605 1542581 := bbase (se 5 (by rfl) ⟨72308, by rfl⟩ : syracuseStep 1542581 = 144617) (by norm_num)
theorem B1542605 : Blo 1024605 1542605 := bbase (se 3 (by rfl) ⟨289238, by rfl⟩ : syracuseStep 1542605 = 578477) (by norm_num)
theorem B1542629 : Blo 1024605 1542629 := bbase (se 4 (by rfl) ⟨144621, by rfl⟩ : syracuseStep 1542629 = 289243) (by norm_num)
theorem B1542653 : Blo 1024605 1542653 := bbase (se 3 (by rfl) ⟨289247, by rfl⟩ : syracuseStep 1542653 = 578495) (by norm_num)
theorem B1542677 : Blo 1024605 1542677 := bbase (se 6 (by rfl) ⟨36156, by rfl⟩ : syracuseStep 1542677 = 72313) (by norm_num)
theorem B1542701 : Blo 1024605 1542701 := bbase (se 3 (by rfl) ⟨289256, by rfl⟩ : syracuseStep 1542701 = 578513) (by norm_num)
theorem B1542725 : Blo 1024605 1542725 := bbase (se 4 (by rfl) ⟨144630, by rfl⟩ : syracuseStep 1542725 = 289261) (by norm_num)
theorem B1542749 : Blo 1024605 1542749 := bbase (se 3 (by rfl) ⟨289265, by rfl⟩ : syracuseStep 1542749 = 578531) (by norm_num)
theorem B1542773 : Blo 1024605 1542773 := bbase (se 5 (by rfl) ⟨72317, by rfl⟩ : syracuseStep 1542773 = 144635) (by norm_num)
theorem B1542797 : Blo 1024605 1542797 := bbase (se 3 (by rfl) ⟨289274, by rfl⟩ : syracuseStep 1542797 = 578549) (by norm_num)
theorem B1542821 : Blo 1024605 1542821 := bbase (se 4 (by rfl) ⟨144639, by rfl⟩ : syracuseStep 1542821 = 289279) (by norm_num)
theorem B1542845 : Blo 1024605 1542845 := bbase (se 3 (by rfl) ⟨289283, by rfl⟩ : syracuseStep 1542845 = 578567) (by norm_num)
theorem B1542869 : Blo 1024605 1542869 := bbase (se 7 (by rfl) ⟨18080, by rfl⟩ : syracuseStep 1542869 = 36161) (by norm_num)
theorem B1542893 : Blo 1024605 1542893 := bbase (se 3 (by rfl) ⟨289292, by rfl⟩ : syracuseStep 1542893 = 578585) (by norm_num)
theorem B5835509 : Blo 1024605 5835509 := bbase (se 5 (by rfl) ⟨273539, by rfl⟩ : syracuseStep 5835509 = 547079) (by norm_num)
theorem B2919509 : Blo 1024605 2919509 := bbase (se 8 (by rfl) ⟨17106, by rfl⟩ : syracuseStep 2919509 = 34213) (by norm_num)
theorem B1641629 : Blo 1024605 1641629 := bbase (se 3 (by rfl) ⟨307805, by rfl⟩ : syracuseStep 1641629 = 615611) (by norm_num)
theorem B3509669 : Blo 1024605 3509669 := bbase (se 4 (by rfl) ⟨329031, by rfl⟩ : syracuseStep 3509669 = 658063) (by norm_num)
theorem B8424949 : Blo 1024605 8424949 := bbase (se 5 (by rfl) ⟨394919, by rfl⟩ : syracuseStep 8424949 = 789839) (by norm_num)
theorem B1642141 : Blo 1024605 1642141 := bbase (se 3 (by rfl) ⟨307901, by rfl⟩ : syracuseStep 1642141 = 615803) (by norm_num)
theorem B3903173 : Blo 1024605 3903173 := bbase (se 4 (by rfl) ⟨365922, by rfl⟩ : syracuseStep 3903173 = 731845) (by norm_num)
theorem B1314637 : Blo 1024605 1314637 := bbase (se 3 (by rfl) ⟨246494, by rfl⟩ : syracuseStep 1314637 = 492989) (by norm_num)
theorem B6655925 : Blo 1024605 6655925 := bbase (se 5 (by rfl) ⟨311996, by rfl⟩ : syracuseStep 6655925 = 623993) (by norm_num)
theorem B3116981 : Blo 1024605 3116981 := bbase (se 5 (by rfl) ⟨146108, by rfl⟩ : syracuseStep 3116981 = 292217) (by norm_num)
theorem B3903461 : Blo 1024605 3903461 := bbase (se 4 (by rfl) ⟨365949, by rfl⟩ : syracuseStep 3903461 = 731899) (by norm_num)
theorem B3117125 : Blo 1024605 3117125 := bbase (se 4 (by rfl) ⟨292230, by rfl⟩ : syracuseStep 3117125 = 584461) (by norm_num)
theorem B8786069 : Blo 1024605 8786069 := bbase (se 6 (by rfl) ⟨205923, by rfl⟩ : syracuseStep 8786069 = 411847) (by norm_num)
theorem B1642685 : Blo 1024605 1642685 := bbase (se 3 (by rfl) ⟨308003, by rfl⟩ : syracuseStep 1642685 = 616007) (by norm_num)
theorem B2920693 : Blo 1024605 2920693 := bbase (se 5 (by rfl) ⟨136907, by rfl⟩ : syracuseStep 2920693 = 273815) (by norm_num)
theorem B2920853 : Blo 1024605 2920853 := bbase (se 6 (by rfl) ⟨68457, by rfl⟩ : syracuseStep 2920853 = 136915) (by norm_num)
theorem B2462213 : Blo 1024605 2462213 := bbase (se 4 (by rfl) ⟨230832, by rfl⟩ : syracuseStep 2462213 = 461665) (by norm_num)
theorem B2921093 : Blo 1024605 2921093 := bbase (se 4 (by rfl) ⟨273852, by rfl⟩ : syracuseStep 2921093 = 547705) (by norm_num)
theorem B3117797 : Blo 1024605 3117797 := bbase (se 4 (by rfl) ⟨292293, by rfl⟩ : syracuseStep 3117797 = 584587) (by norm_num)
theorem B1643237 : Blo 1024605 1643237 := bbase (se 4 (by rfl) ⟨154053, by rfl⟩ : syracuseStep 1643237 = 308107) (by norm_num)
theorem B1643269 : Blo 1024605 1643269 := bbase (se 4 (by rfl) ⟨154056, by rfl⟩ : syracuseStep 1643269 = 308113) (by norm_num)
theorem B7803701 : Blo 1024605 7803701 := bbase (se 5 (by rfl) ⟨365798, by rfl⟩ : syracuseStep 7803701 = 731597) (by norm_num)
theorem B2921285 : Blo 1024605 2921285 := bbase (se 4 (by rfl) ⟨273870, by rfl⟩ : syracuseStep 2921285 = 547741) (by norm_num)
theorem B2593741 : Blo 1024605 2593741 := bbase (se 3 (by rfl) ⟨486326, by rfl⟩ : syracuseStep 2593741 = 972653) (by norm_num)
theorem B2593853 : Blo 1024605 2593853 := bbase (se 3 (by rfl) ⟨486347, by rfl⟩ : syracuseStep 2593853 = 972695) (by norm_num)
theorem B1315921 : Blo 1024605 1315921 := bbase (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) (by norm_num)
theorem B3904645 : Blo 1024605 3904645 := bbase (se 4 (by rfl) ⟨366060, by rfl⟩ : syracuseStep 3904645 = 732121) (by norm_num)
theorem B2594045 : Blo 1024605 2594045 := bbase (se 3 (by rfl) ⟨486383, by rfl⟩ : syracuseStep 2594045 = 972767) (by norm_num)
theorem B3904949 : Blo 1024605 3904949 := bbase (se 5 (by rfl) ⟨183044, by rfl⟩ : syracuseStep 3904949 = 366089) (by norm_num)
theorem B1250869 : Blo 1024605 1250869 := bbase (se 5 (by rfl) ⟨58634, by rfl⟩ : syracuseStep 1250869 = 117269) (by norm_num)
theorem B2594389 : Blo 1024605 2594389 := bbase (se 8 (by rfl) ⟨15201, by rfl⟩ : syracuseStep 2594389 = 30403) (by norm_num)
theorem B1250905 : Blo 1024605 1250905 := bbase (se 2 (by rfl) ⟨469089, by rfl⟩ : syracuseStep 1250905 = 938179) (by norm_num)
theorem B1644197 : Blo 1024605 1644197 := bbase (se 4 (by rfl) ⟨154143, by rfl⟩ : syracuseStep 1644197 = 308287) (by norm_num)
theorem B1152697 : Blo 1024605 1152697 := bbase (se 2 (by rfl) ⟨432261, by rfl⟩ : syracuseStep 1152697 = 864523) (by norm_num)
theorem B2594501 : Blo 1024605 2594501 := bbase (se 4 (by rfl) ⟨243234, by rfl⟩ : syracuseStep 2594501 = 486469) (by norm_num)
theorem B1152733 : Blo 1024605 1152733 := bbase (se 3 (by rfl) ⟨216137, by rfl⟩ : syracuseStep 1152733 = 432275) (by norm_num)
theorem B1152769 : Blo 1024605 1152769 := bbase (se 2 (by rfl) ⟨432288, by rfl⟩ : syracuseStep 1152769 = 864577) (by norm_num)
theorem B1152805 : Blo 1024605 1152805 := bbase (se 4 (by rfl) ⟨108075, by rfl⟩ : syracuseStep 1152805 = 216151) (by norm_num)
theorem B2922277 : Blo 1024605 2922277 := bbase (se 4 (by rfl) ⟨273963, by rfl⟩ : syracuseStep 2922277 = 547927) (by norm_num)
theorem B1152841 : Blo 1024605 1152841 := bbase (se 2 (by rfl) ⟨432315, by rfl⟩ : syracuseStep 1152841 = 864631) (by norm_num)
theorem B1152877 : Blo 1024605 1152877 := bbase (se 3 (by rfl) ⟨216164, by rfl⟩ : syracuseStep 1152877 = 432329) (by norm_num)
theorem B2463605 : Blo 1024605 2463605 := bbase (se 5 (by rfl) ⟨115481, by rfl⟩ : syracuseStep 2463605 = 230963) (by norm_num)
theorem B2594693 : Blo 1024605 2594693 := bbase (se 4 (by rfl) ⟨243252, by rfl⟩ : syracuseStep 2594693 = 486505) (by norm_num)
theorem B1152913 : Blo 1024605 1152913 := bbase (se 2 (by rfl) ⟨432342, by rfl⟩ : syracuseStep 1152913 = 864685) (by norm_num)
theorem B1152949 : Blo 1024605 1152949 := bbase (se 5 (by rfl) ⟨54044, by rfl⟩ : syracuseStep 1152949 = 108089) (by norm_num)
theorem B1054661 : Blo 1024605 1054661 := bbase (se 4 (by rfl) ⟨98874, by rfl⟩ : syracuseStep 1054661 = 197749) (by norm_num)
theorem B2463701 : Blo 1024605 2463701 := bbase (se 7 (by rfl) ⟨28871, by rfl⟩ : syracuseStep 2463701 = 57743) (by norm_num)
theorem B1152985 : Blo 1024605 1152985 := bbase (se 2 (by rfl) ⟨432369, by rfl⟩ : syracuseStep 1152985 = 864739) (by norm_num)
theorem B1153021 : Blo 1024605 1153021 := bbase (se 3 (by rfl) ⟨216191, by rfl⟩ : syracuseStep 1153021 = 432383) (by norm_num)
theorem B1153057 : Blo 1024605 1153057 := bbase (se 2 (by rfl) ⟨432396, by rfl⟩ : syracuseStep 1153057 = 864793) (by norm_num)
theorem B1185841 : Blo 1024605 1185841 := bbase (se 2 (by rfl) ⟨444690, by rfl⟩ : syracuseStep 1185841 = 889381) (by norm_num)
theorem B1153093 : Blo 1024605 1153093 := bbase (se 4 (by rfl) ⟨108102, by rfl⟩ : syracuseStep 1153093 = 216205) (by norm_num)
theorem B1153129 : Blo 1024605 1153129 := bbase (se 2 (by rfl) ⟨432423, by rfl⟩ : syracuseStep 1153129 = 864847) (by norm_num)
theorem B1153165 : Blo 1024605 1153165 := bbase (se 3 (by rfl) ⟨216218, by rfl⟩ : syracuseStep 1153165 = 432437) (by norm_num)
theorem B1153201 : Blo 1024605 1153201 := bbase (se 2 (by rfl) ⟨432450, by rfl⟩ : syracuseStep 1153201 = 864901) (by norm_num)
theorem B1153237 : Blo 1024605 1153237 := bbase (se 7 (by rfl) ⟨13514, by rfl⟩ : syracuseStep 1153237 = 27029) (by norm_num)
theorem B2595037 : Blo 1024605 2595037 := bbase (se 3 (by rfl) ⟨486569, by rfl⟩ : syracuseStep 2595037 = 973139) (by norm_num)
theorem B1153273 : Blo 1024605 1153273 := bbase (se 2 (by rfl) ⟨432477, by rfl⟩ : syracuseStep 1153273 = 864955) (by norm_num)
theorem B1153309 : Blo 1024605 1153309 := bbase (se 3 (by rfl) ⟨216245, by rfl⟩ : syracuseStep 1153309 = 432491) (by norm_num)
theorem B1153345 : Blo 1024605 1153345 := bbase (se 2 (by rfl) ⟨432504, by rfl⟩ : syracuseStep 1153345 = 865009) (by norm_num)
theorem B2595149 : Blo 1024605 2595149 := bbase (se 3 (by rfl) ⟨486590, by rfl⟩ : syracuseStep 2595149 = 973181) (by norm_num)
theorem B1644877 : Blo 1024605 1644877 := bbase (se 3 (by rfl) ⟨308414, by rfl⟩ : syracuseStep 1644877 = 616829) (by norm_num)
theorem B1153381 : Blo 1024605 1153381 := bbase (se 4 (by rfl) ⟨108129, by rfl⟩ : syracuseStep 1153381 = 216259) (by norm_num)
theorem B1153417 : Blo 1024605 1153417 := bbase (se 2 (by rfl) ⟨432531, by rfl⟩ : syracuseStep 1153417 = 865063) (by norm_num)
theorem B1644941 : Blo 1024605 1644941 := bbase (se 3 (by rfl) ⟨308426, by rfl⟩ : syracuseStep 1644941 = 616853) (by norm_num)
theorem B1874333 : Blo 1024605 1874333 := bbase (se 3 (by rfl) ⟨351437, by rfl⟩ : syracuseStep 1874333 = 702875) (by norm_num)
theorem B1153453 : Blo 1024605 1153453 := bbase (se 3 (by rfl) ⟨216272, by rfl⟩ : syracuseStep 1153453 = 432545) (by norm_num)
theorem B1153489 : Blo 1024605 1153489 := bbase (se 2 (by rfl) ⟨432558, by rfl⟩ : syracuseStep 1153489 = 865117) (by norm_num)
theorem B1153525 : Blo 1024605 1153525 := bbase (se 5 (by rfl) ⟨54071, by rfl⟩ : syracuseStep 1153525 = 108143) (by norm_num)
theorem B1972741 : Blo 1024605 1972741 := bbase (se 4 (by rfl) ⟨184944, by rfl⟩ : syracuseStep 1972741 = 369889) (by norm_num)
theorem B2595341 : Blo 1024605 2595341 := bbase (se 3 (by rfl) ⟨486626, by rfl⟩ : syracuseStep 2595341 = 973253) (by norm_num)
theorem B1153561 : Blo 1024605 1153561 := bbase (se 2 (by rfl) ⟨432585, by rfl⟩ : syracuseStep 1153561 = 865171) (by norm_num)
theorem B1153597 : Blo 1024605 1153597 := bbase (se 3 (by rfl) ⟨216299, by rfl⟩ : syracuseStep 1153597 = 432599) (by norm_num)
theorem B1153633 : Blo 1024605 1153633 := bbase (se 2 (by rfl) ⟨432612, by rfl⟩ : syracuseStep 1153633 = 865225) (by norm_num)
theorem B1153669 : Blo 1024605 1153669 := bbase (se 4 (by rfl) ⟨108156, by rfl⟩ : syracuseStep 1153669 = 216313) (by norm_num)
theorem B1153705 : Blo 1024605 1153705 := bbase (se 2 (by rfl) ⟨432639, by rfl⟩ : syracuseStep 1153705 = 865279) (by norm_num)
theorem B1153741 : Blo 1024605 1153741 := bbase (se 3 (by rfl) ⟨216326, by rfl⟩ : syracuseStep 1153741 = 432653) (by norm_num)
theorem B1972957 : Blo 1024605 1972957 := bbase (se 3 (by rfl) ⟨369929, by rfl⟩ : syracuseStep 1972957 = 739859) (by norm_num)
theorem B1153777 : Blo 1024605 1153777 := bbase (se 2 (by rfl) ⟨432666, by rfl⟩ : syracuseStep 1153777 = 865333) (by norm_num)
theorem B1153813 : Blo 1024605 1153813 := bbase (se 6 (by rfl) ⟨27042, by rfl⟩ : syracuseStep 1153813 = 54085) (by norm_num)
theorem B1317665 : Blo 1024605 1317665 := bbase (se 2 (by rfl) ⟨494124, by rfl⟩ : syracuseStep 1317665 = 988249) (by norm_num)
theorem B1153849 : Blo 1024605 1153849 := bbase (se 2 (by rfl) ⟨432693, by rfl⟩ : syracuseStep 1153849 = 865387) (by norm_num)
theorem B1153885 : Blo 1024605 1153885 := bbase (se 3 (by rfl) ⟨216353, by rfl⟩ : syracuseStep 1153885 = 432707) (by norm_num)
theorem B2595685 : Blo 1024605 2595685 := bbase (se 4 (by rfl) ⟨243345, by rfl⟩ : syracuseStep 2595685 = 486691) (by norm_num)
theorem B2923381 : Blo 1024605 2923381 := bbase (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) (by norm_num)
theorem B1153921 : Blo 1024605 1153921 := bbase (se 2 (by rfl) ⟨432720, by rfl⟩ : syracuseStep 1153921 = 865441) (by norm_num)
theorem B1153957 : Blo 1024605 1153957 := bbase (se 4 (by rfl) ⟨108183, by rfl⟩ : syracuseStep 1153957 = 216367) (by norm_num)
theorem B1153993 : Blo 1024605 1153993 := bbase (se 2 (by rfl) ⟨432747, by rfl⟩ : syracuseStep 1153993 = 865495) (by norm_num)
theorem B2595797 : Blo 1024605 2595797 := bbase (se 7 (by rfl) ⟨30419, by rfl⟩ : syracuseStep 2595797 = 60839) (by norm_num)
theorem B1154029 : Blo 1024605 1154029 := bbase (se 3 (by rfl) ⟨216380, by rfl⟩ : syracuseStep 1154029 = 432761) (by norm_num)
theorem B1154065 : Blo 1024605 1154065 := bbase (se 2 (by rfl) ⟨432774, by rfl⟩ : syracuseStep 1154065 = 865549) (by norm_num)
theorem B3513365 : Blo 1024605 3513365 := bbase (se 6 (by rfl) ⟨82344, by rfl⟩ : syracuseStep 3513365 = 164689) (by norm_num)
theorem B1154101 : Blo 1024605 1154101 := bbase (se 5 (by rfl) ⟨54098, by rfl⟩ : syracuseStep 1154101 = 108197) (by norm_num)
theorem B1154137 : Blo 1024605 1154137 := bbase (se 2 (by rfl) ⟨432801, by rfl⟩ : syracuseStep 1154137 = 865603) (by norm_num)
theorem B1154173 : Blo 1024605 1154173 := bbase (se 3 (by rfl) ⟨216407, by rfl⟩ : syracuseStep 1154173 = 432815) (by norm_num)
theorem B1875077 : Blo 1024605 1875077 := bbase (se 4 (by rfl) ⟨175788, by rfl⟩ : syracuseStep 1875077 = 351577) (by norm_num)
theorem B2595989 : Blo 1024605 2595989 := bbase (se 6 (by rfl) ⟨60843, by rfl⟩ : syracuseStep 2595989 = 121687) (by norm_num)
theorem B1154209 : Blo 1024605 1154209 := bbase (se 2 (by rfl) ⟨432828, by rfl⟩ : syracuseStep 1154209 = 865657) (by norm_num)
theorem B1154245 : Blo 1024605 1154245 := bbase (se 4 (by rfl) ⟨108210, by rfl⟩ : syracuseStep 1154245 = 216421) (by norm_num)
theorem B1154281 : Blo 1024605 1154281 := bbase (se 2 (by rfl) ⟨432855, by rfl⟩ : syracuseStep 1154281 = 865711) (by norm_num)
theorem B1154317 : Blo 1024605 1154317 := bbase (se 3 (by rfl) ⟨216434, by rfl⟩ : syracuseStep 1154317 = 432869) (by norm_num)
theorem B1154353 : Blo 1024605 1154353 := bbase (se 2 (by rfl) ⟨432882, by rfl⟩ : syracuseStep 1154353 = 865765) (by norm_num)
theorem B1154389 : Blo 1024605 1154389 := bbase (se 11 (by rfl) ⟨845, by rfl⟩ : syracuseStep 1154389 = 1691) (by norm_num)
theorem B1154425 : Blo 1024605 1154425 := bbase (se 2 (by rfl) ⟨432909, by rfl⟩ : syracuseStep 1154425 = 865819) (by norm_num)
theorem B1187201 : Blo 1024605 1187201 := bbase (se 2 (by rfl) ⟨445200, by rfl⟩ : syracuseStep 1187201 = 890401) (by norm_num)
theorem B1154461 : Blo 1024605 1154461 := bbase (se 3 (by rfl) ⟨216461, by rfl⟩ : syracuseStep 1154461 = 432923) (by norm_num)
theorem B1154497 : Blo 1024605 1154497 := bbase (se 2 (by rfl) ⟨432936, by rfl⟩ : syracuseStep 1154497 = 865873) (by norm_num)
theorem B1154533 : Blo 1024605 1154533 := bbase (se 4 (by rfl) ⟨108237, by rfl⟩ : syracuseStep 1154533 = 216475) (by norm_num)
theorem B2596333 : Blo 1024605 2596333 := bbase (se 3 (by rfl) ⟨486812, by rfl⟩ : syracuseStep 2596333 = 973625) (by norm_num)
theorem B1154569 : Blo 1024605 1154569 := bbase (se 2 (by rfl) ⟨432963, by rfl⟩ : syracuseStep 1154569 = 865927) (by norm_num)
theorem B1056277 : Blo 1024605 1056277 := bbase (se 6 (by rfl) ⟨24756, by rfl⟩ : syracuseStep 1056277 = 49513) (by norm_num)
theorem B1154605 : Blo 1024605 1154605 := bbase (se 3 (by rfl) ⟨216488, by rfl⟩ : syracuseStep 1154605 = 432977) (by norm_num)
theorem B1154641 : Blo 1024605 1154641 := bbase (se 2 (by rfl) ⟨432990, by rfl⟩ : syracuseStep 1154641 = 865981) (by norm_num)
theorem B2596445 : Blo 1024605 2596445 := bbase (se 3 (by rfl) ⟨486833, by rfl⟩ : syracuseStep 2596445 = 973667) (by norm_num)
theorem B1154677 : Blo 1024605 1154677 := bbase (se 5 (by rfl) ⟨54125, by rfl⟩ : syracuseStep 1154677 = 108251) (by norm_num)
theorem B1154713 : Blo 1024605 1154713 := bbase (se 2 (by rfl) ⟨433017, by rfl⟩ : syracuseStep 1154713 = 866035) (by norm_num)
theorem B1646261 : Blo 1024605 1646261 := bbase (se 5 (by rfl) ⟨77168, by rfl⟩ : syracuseStep 1646261 = 154337) (by norm_num)
theorem B1154749 : Blo 1024605 1154749 := bbase (se 3 (by rfl) ⟨216515, by rfl⟩ : syracuseStep 1154749 = 433031) (by norm_num)
theorem B1154785 : Blo 1024605 1154785 := bbase (se 2 (by rfl) ⟨433044, by rfl⟩ : syracuseStep 1154785 = 866089) (by norm_num)
theorem B1154821 : Blo 1024605 1154821 := bbase (se 4 (by rfl) ⟨108264, by rfl⟩ : syracuseStep 1154821 = 216529) (by norm_num)
theorem B2596637 : Blo 1024605 2596637 := bbase (se 3 (by rfl) ⟨486869, by rfl⟩ : syracuseStep 2596637 = 973739) (by norm_num)
theorem B1154857 : Blo 1024605 1154857 := bbase (se 2 (by rfl) ⟨433071, by rfl⟩ : syracuseStep 1154857 = 866143) (by norm_num)
theorem B1154893 : Blo 1024605 1154893 := bbase (se 3 (by rfl) ⟨216542, by rfl⟩ : syracuseStep 1154893 = 433085) (by norm_num)
theorem B1056601 : Blo 1024605 1056601 := bbase (se 2 (by rfl) ⟨396225, by rfl⟩ : syracuseStep 1056601 = 792451) (by norm_num)
theorem B1154929 : Blo 1024605 1154929 := bbase (se 2 (by rfl) ⟨433098, by rfl⟩ : syracuseStep 1154929 = 866197) (by norm_num)
theorem B1646453 : Blo 1024605 1646453 := bbase (se 5 (by rfl) ⟨77177, by rfl⟩ : syracuseStep 1646453 = 154355) (by norm_num)
theorem B1154965 : Blo 1024605 1154965 := bbase (se 6 (by rfl) ⟨27069, by rfl⟩ : syracuseStep 1154965 = 54139) (by norm_num)
theorem B1155001 : Blo 1024605 1155001 := bbase (se 2 (by rfl) ⟨433125, by rfl⟩ : syracuseStep 1155001 = 866251) (by norm_num)
theorem B1155037 : Blo 1024605 1155037 := bbase (se 3 (by rfl) ⟨216569, by rfl⟩ : syracuseStep 1155037 = 433139) (by norm_num)
theorem B1646581 : Blo 1024605 1646581 := bbase (se 5 (by rfl) ⟨77183, by rfl⟩ : syracuseStep 1646581 = 154367) (by norm_num)
theorem B1155073 : Blo 1024605 1155073 := bbase (se 2 (by rfl) ⟨433152, by rfl⟩ : syracuseStep 1155073 = 866305) (by norm_num)
theorem B2465797 : Blo 1024605 2465797 := bbase (se 4 (by rfl) ⟨231168, by rfl⟩ : syracuseStep 2465797 = 462337) (by norm_num)
theorem B1155109 : Blo 1024605 1155109 := bbase (se 4 (by rfl) ⟨108291, by rfl⟩ : syracuseStep 1155109 = 216583) (by norm_num)
theorem B1155145 : Blo 1024605 1155145 := bbase (se 2 (by rfl) ⟨433179, by rfl⟩ : syracuseStep 1155145 = 866359) (by norm_num)
theorem B7610453 : Blo 1024605 7610453 := bbase (se 8 (by rfl) ⟨44592, by rfl⟩ : syracuseStep 7610453 = 89185) (by norm_num)
theorem B1155181 : Blo 1024605 1155181 := bbase (se 3 (by rfl) ⟨216596, by rfl⟩ : syracuseStep 1155181 = 433193) (by norm_num)
theorem B2596981 : Blo 1024605 2596981 := bbase (se 5 (by rfl) ⟨121733, by rfl⟩ : syracuseStep 2596981 = 243467) (by norm_num)
theorem B1155217 : Blo 1024605 1155217 := bbase (se 2 (by rfl) ⟨433206, by rfl⟩ : syracuseStep 1155217 = 866413) (by norm_num)
theorem B1155253 : Blo 1024605 1155253 := bbase (se 5 (by rfl) ⟨54152, by rfl⟩ : syracuseStep 1155253 = 108305) (by norm_num)
theorem B1155289 : Blo 1024605 1155289 := bbase (se 2 (by rfl) ⟨433233, by rfl⟩ : syracuseStep 1155289 = 866467) (by norm_num)
theorem B2597093 : Blo 1024605 2597093 := bbase (se 4 (by rfl) ⟨243477, by rfl⟩ : syracuseStep 2597093 = 486955) (by norm_num)
theorem B1155325 : Blo 1024605 1155325 := bbase (se 3 (by rfl) ⟨216623, by rfl⟩ : syracuseStep 1155325 = 433247) (by norm_num)
theorem B3285269 : Blo 1024605 3285269 := bbase (se 6 (by rfl) ⟨76998, by rfl⟩ : syracuseStep 3285269 = 153997) (by norm_num)
theorem B1155361 : Blo 1024605 1155361 := bbase (se 2 (by rfl) ⟨433260, by rfl⟩ : syracuseStep 1155361 = 866521) (by norm_num)
theorem B1155397 : Blo 1024605 1155397 := bbase (se 4 (by rfl) ⟨108318, by rfl⟩ : syracuseStep 1155397 = 216637) (by norm_num)
theorem B2924885 : Blo 1024605 2924885 := bbase (se 10 (by rfl) ⟨4284, by rfl⟩ : syracuseStep 2924885 = 8569) (by norm_num)
theorem B1155433 : Blo 1024605 1155433 := bbase (se 2 (by rfl) ⟨433287, by rfl⟩ : syracuseStep 1155433 = 866575) (by norm_num)
theorem B3514757 : Blo 1024605 3514757 := bbase (se 4 (by rfl) ⟨329508, by rfl⟩ : syracuseStep 3514757 = 659017) (by norm_num)
theorem B1155469 : Blo 1024605 1155469 := bbase (se 3 (by rfl) ⟨216650, by rfl⟩ : syracuseStep 1155469 = 433301) (by norm_num)
theorem B2597285 : Blo 1024605 2597285 := bbase (se 4 (by rfl) ⟨243495, by rfl⟩ : syracuseStep 2597285 = 486991) (by norm_num)
theorem B1155505 : Blo 1024605 1155505 := bbase (se 2 (by rfl) ⟨433314, by rfl⟩ : syracuseStep 1155505 = 866629) (by norm_num)
theorem B1155541 : Blo 1024605 1155541 := bbase (se 7 (by rfl) ⟨13541, by rfl⟩ : syracuseStep 1155541 = 27083) (by norm_num)
theorem B1155577 : Blo 1024605 1155577 := bbase (se 2 (by rfl) ⟨433341, by rfl⟩ : syracuseStep 1155577 = 866683) (by norm_num)
theorem B1155613 : Blo 1024605 1155613 := bbase (se 3 (by rfl) ⟨216677, by rfl⟩ : syracuseStep 1155613 = 433355) (by norm_num)
theorem B1155649 : Blo 1024605 1155649 := bbase (se 2 (by rfl) ⟨433368, by rfl⟩ : syracuseStep 1155649 = 866737) (by norm_num)
theorem B1155685 : Blo 1024605 1155685 := bbase (se 4 (by rfl) ⟨108345, by rfl⟩ : syracuseStep 1155685 = 216691) (by norm_num)
theorem B2466413 : Blo 1024605 2466413 := bbase (se 3 (by rfl) ⟨462452, by rfl⟩ : syracuseStep 2466413 = 924905) (by norm_num)
theorem B1647221 : Blo 1024605 1647221 := bbase (se 5 (by rfl) ⟨77213, by rfl⟩ : syracuseStep 1647221 = 154427) (by norm_num)
theorem B1155721 : Blo 1024605 1155721 := bbase (se 2 (by rfl) ⟨433395, by rfl⟩ : syracuseStep 1155721 = 866791) (by norm_num)
theorem B1155757 : Blo 1024605 1155757 := bbase (se 3 (by rfl) ⟨216704, by rfl⟩ : syracuseStep 1155757 = 433409) (by norm_num)
theorem B1155793 : Blo 1024605 1155793 := bbase (se 2 (by rfl) ⟨433422, by rfl⟩ : syracuseStep 1155793 = 866845) (by norm_num)
theorem B1155829 : Blo 1024605 1155829 := bbase (se 5 (by rfl) ⟨54179, by rfl⟩ : syracuseStep 1155829 = 108359) (by norm_num)
theorem B2597629 : Blo 1024605 2597629 := bbase (se 3 (by rfl) ⟨487055, by rfl⟩ : syracuseStep 2597629 = 974111) (by norm_num)
theorem B1155865 : Blo 1024605 1155865 := bbase (se 2 (by rfl) ⟨433449, by rfl⟩ : syracuseStep 1155865 = 866899) (by norm_num)
theorem B1155901 : Blo 1024605 1155901 := bbase (se 3 (by rfl) ⟨216731, by rfl⟩ : syracuseStep 1155901 = 433463) (by norm_num)
theorem B1155937 : Blo 1024605 1155937 := bbase (se 2 (by rfl) ⟨433476, by rfl⟩ : syracuseStep 1155937 = 866953) (by norm_num)
theorem B2597741 : Blo 1024605 2597741 := bbase (se 3 (by rfl) ⟨487076, by rfl⟩ : syracuseStep 2597741 = 974153) (by norm_num)
theorem B1155973 : Blo 1024605 1155973 := bbase (se 4 (by rfl) ⟨108372, by rfl⟩ : syracuseStep 1155973 = 216745) (by norm_num)
theorem B1156009 : Blo 1024605 1156009 := bbase (se 2 (by rfl) ⟨433503, by rfl⟩ : syracuseStep 1156009 = 867007) (by norm_num)
theorem B2499517 : Blo 1024605 2499517 := bbase (se 3 (by rfl) ⟨468659, by rfl⟩ : syracuseStep 2499517 = 937319) (by norm_num)
theorem B2466749 : Blo 1024605 2466749 := bbase (se 3 (by rfl) ⟨462515, by rfl⟩ : syracuseStep 2466749 = 925031) (by norm_num)
theorem B1156045 : Blo 1024605 1156045 := bbase (se 3 (by rfl) ⟨216758, by rfl⟩ : syracuseStep 1156045 = 433517) (by norm_num)
theorem B1156081 : Blo 1024605 1156081 := bbase (se 2 (by rfl) ⟨433530, by rfl⟩ : syracuseStep 1156081 = 867061) (by norm_num)
theorem B1156117 : Blo 1024605 1156117 := bbase (se 6 (by rfl) ⟨27096, by rfl⟩ : syracuseStep 1156117 = 54193) (by norm_num)
theorem B2597933 : Blo 1024605 2597933 := bbase (se 3 (by rfl) ⟨487112, by rfl⟩ : syracuseStep 2597933 = 974225) (by norm_num)
theorem B1156153 : Blo 1024605 1156153 := bbase (se 2 (by rfl) ⟨433557, by rfl⟩ : syracuseStep 1156153 = 867115) (by norm_num)
theorem B1156189 : Blo 1024605 1156189 := bbase (se 3 (by rfl) ⟨216785, by rfl⟩ : syracuseStep 1156189 = 433571) (by norm_num)
theorem B1156225 : Blo 1024605 1156225 := bbase (se 2 (by rfl) ⟨433584, by rfl⟩ : syracuseStep 1156225 = 867169) (by norm_num)
theorem B1483909 : Blo 1024605 1483909 := bbase (se 4 (by rfl) ⟨139116, by rfl⟩ : syracuseStep 1483909 = 278233) (by norm_num)
theorem B3286165 : Blo 1024605 3286165 := bbase (se 6 (by rfl) ⟨77019, by rfl⟩ : syracuseStep 3286165 = 154039) (by norm_num)
theorem B1156261 : Blo 1024605 1156261 := bbase (se 4 (by rfl) ⟨108399, by rfl⟩ : syracuseStep 1156261 = 216799) (by norm_num)
theorem B1156297 : Blo 1024605 1156297 := bbase (se 2 (by rfl) ⟨433611, by rfl⟩ : syracuseStep 1156297 = 867223) (by norm_num)
theorem B3122405 : Blo 1024605 3122405 := bbase (se 4 (by rfl) ⟨292725, by rfl⟩ : syracuseStep 3122405 = 585451) (by norm_num)
theorem B1156333 : Blo 1024605 1156333 := bbase (se 3 (by rfl) ⟨216812, by rfl⟩ : syracuseStep 1156333 = 433625) (by norm_num)
theorem B1156369 : Blo 1024605 1156369 := bbase (se 2 (by rfl) ⟨433638, by rfl⟩ : syracuseStep 1156369 = 867277) (by norm_num)
theorem B1156405 : Blo 1024605 1156405 := bbase (se 5 (by rfl) ⟨54206, by rfl⟩ : syracuseStep 1156405 = 108413) (by norm_num)
theorem B2467141 : Blo 1024605 2467141 := bbase (se 4 (by rfl) ⟨231294, by rfl⟩ : syracuseStep 2467141 = 462589) (by norm_num)
theorem B1156441 : Blo 1024605 1156441 := bbase (se 2 (by rfl) ⟨433665, by rfl⟩ : syracuseStep 1156441 = 867331) (by norm_num)
theorem B1156477 : Blo 1024605 1156477 := bbase (se 3 (by rfl) ⟨216839, by rfl⟩ : syracuseStep 1156477 = 433679) (by norm_num)
theorem B2598277 : Blo 1024605 2598277 := bbase (se 4 (by rfl) ⟨243588, by rfl⟩ : syracuseStep 2598277 = 487177) (by norm_num)
theorem B1156513 : Blo 1024605 1156513 := bbase (se 2 (by rfl) ⟨433692, by rfl⟩ : syracuseStep 1156513 = 867385) (by norm_num)
theorem B1156549 : Blo 1024605 1156549 := bbase (se 4 (by rfl) ⟨108426, by rfl⟩ : syracuseStep 1156549 = 216853) (by norm_num)
theorem B1156585 : Blo 1024605 1156585 := bbase (se 2 (by rfl) ⟨433719, by rfl⟩ : syracuseStep 1156585 = 867439) (by norm_num)
theorem B2598389 : Blo 1024605 2598389 := bbase (se 5 (by rfl) ⟨121799, by rfl⟩ : syracuseStep 2598389 = 243599) (by norm_num)
theorem B5187077 : Blo 1024605 5187077 := bbase (se 4 (by rfl) ⟨486288, by rfl⟩ : syracuseStep 5187077 = 972577) (by norm_num)
theorem B1156621 : Blo 1024605 1156621 := bbase (se 3 (by rfl) ⟨216866, by rfl⟩ : syracuseStep 1156621 = 433733) (by norm_num)
theorem B1975853 : Blo 1024605 1975853 := bbase (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) (by norm_num)
theorem B1156657 : Blo 1024605 1156657 := bbase (se 2 (by rfl) ⟨433746, by rfl⟩ : syracuseStep 1156657 = 867493) (by norm_num)
theorem B1386037 : Blo 1024605 1386037 := bbase (se 5 (by rfl) ⟨64970, by rfl⟩ : syracuseStep 1386037 = 129941) (by norm_num)
theorem B1156693 : Blo 1024605 1156693 := bbase (se 8 (by rfl) ⟨6777, by rfl⟩ : syracuseStep 1156693 = 13555) (by norm_num)
theorem B1156729 : Blo 1024605 1156729 := bbase (se 2 (by rfl) ⟨433773, by rfl⟩ : syracuseStep 1156729 = 867547) (by norm_num)
theorem B1156765 : Blo 1024605 1156765 := bbase (se 3 (by rfl) ⟨216893, by rfl⟩ : syracuseStep 1156765 = 433787) (by norm_num)
theorem B2598581 : Blo 1024605 2598581 := bbase (se 5 (by rfl) ⟨121808, by rfl⟩ : syracuseStep 2598581 = 243617) (by norm_num)
theorem B1156801 : Blo 1024605 1156801 := bbase (se 2 (by rfl) ⟨433800, by rfl⟩ : syracuseStep 1156801 = 867601) (by norm_num)
theorem B1156837 : Blo 1024605 1156837 := bbase (se 4 (by rfl) ⟨108453, by rfl⟩ : syracuseStep 1156837 = 216907) (by norm_num)
theorem B1156873 : Blo 1024605 1156873 := bbase (se 2 (by rfl) ⟨433827, by rfl⟩ : syracuseStep 1156873 = 867655) (by norm_num)
theorem B1156909 : Blo 1024605 1156909 := bbase (se 3 (by rfl) ⟨216920, by rfl⟩ : syracuseStep 1156909 = 433841) (by norm_num)
theorem B1156945 : Blo 1024605 1156945 := bbase (se 2 (by rfl) ⟨433854, by rfl⟩ : syracuseStep 1156945 = 867709) (by norm_num)
theorem B1156981 : Blo 1024605 1156981 := bbase (se 5 (by rfl) ⟨54233, by rfl⟩ : syracuseStep 1156981 = 108467) (by norm_num)
theorem B2926469 : Blo 1024605 2926469 := bbase (se 4 (by rfl) ⟨274356, by rfl⟩ : syracuseStep 2926469 = 548713) (by norm_num)
theorem B1157017 : Blo 1024605 1157017 := bbase (se 2 (by rfl) ⟨433881, by rfl⟩ : syracuseStep 1157017 = 867763) (by norm_num)
theorem B1157053 : Blo 1024605 1157053 := bbase (se 3 (by rfl) ⟨216947, by rfl⟩ : syracuseStep 1157053 = 433895) (by norm_num)
theorem B1157089 : Blo 1024605 1157089 := bbase (se 2 (by rfl) ⟨433908, by rfl⟩ : syracuseStep 1157089 = 867817) (by norm_num)
theorem B1157125 : Blo 1024605 1157125 := bbase (se 4 (by rfl) ⟨108480, by rfl⟩ : syracuseStep 1157125 = 216961) (by norm_num)
theorem B2598925 : Blo 1024605 2598925 := bbase (se 3 (by rfl) ⟨487298, by rfl⟩ : syracuseStep 2598925 = 974597) (by norm_num)
theorem B1157161 : Blo 1024605 1157161 := bbase (se 2 (by rfl) ⟨433935, by rfl⟩ : syracuseStep 1157161 = 867871) (by norm_num)
theorem B2599037 : Blo 1024605 2599037 := bbase (se 3 (by rfl) ⟨487319, by rfl⟩ : syracuseStep 2599037 = 974639) (by norm_num)
theorem B1386725 : Blo 1024605 1386725 := bbase (se 4 (by rfl) ⟨130005, by rfl⟩ : syracuseStep 1386725 = 260011) (by norm_num)
theorem B2599229 : Blo 1024605 2599229 := bbase (se 3 (by rfl) ⟨487355, by rfl⟩ : syracuseStep 2599229 = 974711) (by norm_num)
theorem B2927141 : Blo 1024605 2927141 := bbase (se 4 (by rfl) ⟨274419, by rfl⟩ : syracuseStep 2927141 = 548839) (by norm_num)
theorem B2108005 : Blo 1024605 2108005 := bbase (se 4 (by rfl) ⟨197625, by rfl⟩ : syracuseStep 2108005 = 395251) (by norm_num)
theorem B5843573 : Blo 1024605 5843573 := bbase (se 5 (by rfl) ⟨273917, by rfl⟩ : syracuseStep 5843573 = 547835) (by norm_num)
theorem B2599573 : Blo 1024605 2599573 := bbase (se 6 (by rfl) ⟨60927, by rfl⟩ : syracuseStep 2599573 = 121855) (by norm_num)
theorem B2599685 : Blo 1024605 2599685 := bbase (se 4 (by rfl) ⟨243720, by rfl⟩ : syracuseStep 2599685 = 487441) (by norm_num)
theorem B5188373 : Blo 1024605 5188373 := bbase (se 6 (by rfl) ⟨121602, by rfl⟩ : syracuseStep 5188373 = 243205) (by norm_num)
theorem B2599877 : Blo 1024605 2599877 := bbase (se 4 (by rfl) ⟨243738, by rfl⟩ : syracuseStep 2599877 = 487477) (by norm_num)
theorem B2927573 : Blo 1024605 2927573 := bbase (se 7 (by rfl) ⟨34307, by rfl⟩ : syracuseStep 2927573 = 68615) (by norm_num)
theorem B2370629 : Blo 1024605 2370629 := bbase (se 4 (by rfl) ⟨222246, by rfl⟩ : syracuseStep 2370629 = 444493) (by norm_num)
theorem B1846493 : Blo 1024605 1846493 := bbase (se 3 (by rfl) ⟨346217, by rfl⟩ : syracuseStep 1846493 = 692435) (by norm_num)
theorem B2632949 : Blo 1024605 2632949 := bbase (se 5 (by rfl) ⟨123419, by rfl⟩ : syracuseStep 2632949 = 246839) (by norm_num)
theorem B6237461 : Blo 1024605 6237461 := bbase (se 6 (by rfl) ⟨146190, by rfl⟩ : syracuseStep 6237461 = 292381) (by norm_num)
theorem B2600221 : Blo 1024605 2600221 := bbase (se 3 (by rfl) ⟨487541, by rfl⟩ : syracuseStep 2600221 = 975083) (by norm_num)
theorem B2305421 : Blo 1024605 2305421 := bbase (se 3 (by rfl) ⟨432266, by rfl⟩ : syracuseStep 2305421 = 864533) (by norm_num)
theorem B2600333 : Blo 1024605 2600333 := bbase (se 3 (by rfl) ⟨487562, by rfl⟩ : syracuseStep 2600333 = 975125) (by norm_num)
theorem B4926901 : Blo 1024605 4926901 := bbase (se 5 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 4926901 = 461897) (by norm_num)
theorem B2305493 : Blo 1024605 2305493 := bbase (se 7 (by rfl) ⟨27017, by rfl⟩ : syracuseStep 2305493 = 54035) (by norm_num)
theorem B2305565 : Blo 1024605 2305565 := bbase (se 3 (by rfl) ⟨432293, by rfl⟩ : syracuseStep 2305565 = 864587) (by norm_num)
theorem B2600525 : Blo 1024605 2600525 := bbase (se 3 (by rfl) ⟨487598, by rfl⟩ : syracuseStep 2600525 = 975197) (by norm_num)
theorem B2305637 : Blo 1024605 2305637 := bbase (se 4 (by rfl) ⟨216153, by rfl⟩ : syracuseStep 2305637 = 432307) (by norm_num)
theorem B2305709 : Blo 1024605 2305709 := bbase (se 3 (by rfl) ⟨432320, by rfl⟩ : syracuseStep 2305709 = 864641) (by norm_num)
theorem B2928325 : Blo 1024605 2928325 := bbase (se 4 (by rfl) ⟨274530, by rfl⟩ : syracuseStep 2928325 = 549061) (by norm_num)
theorem B2305781 : Blo 1024605 2305781 := bbase (se 5 (by rfl) ⟨108083, by rfl⟩ : syracuseStep 2305781 = 216167) (by norm_num)
theorem B5844757 : Blo 1024605 5844757 := bbase (se 6 (by rfl) ⟨136986, by rfl⟩ : syracuseStep 5844757 = 273973) (by norm_num)
theorem B1945397 : Blo 1024605 1945397 := bbase (se 5 (by rfl) ⟨91190, by rfl⟩ : syracuseStep 1945397 = 182381) (by norm_num)
theorem B1388341 : Blo 1024605 1388341 := bbase (se 5 (by rfl) ⟨65078, by rfl⟩ : syracuseStep 1388341 = 130157) (by norm_num)
theorem B2305853 : Blo 1024605 2305853 := bbase (se 3 (by rfl) ⟨432347, by rfl⟩ : syracuseStep 2305853 = 864695) (by norm_num)
theorem B2305925 : Blo 1024605 2305925 := bbase (se 4 (by rfl) ⟨216180, by rfl⟩ : syracuseStep 2305925 = 432361) (by norm_num)
theorem B2600869 : Blo 1024605 2600869 := bbase (se 4 (by rfl) ⟨243831, by rfl⟩ : syracuseStep 2600869 = 487663) (by norm_num)
theorem B1945549 : Blo 1024605 1945549 := bbase (se 3 (by rfl) ⟨364790, by rfl⟩ : syracuseStep 1945549 = 729581) (by norm_num)
theorem B2305997 : Blo 1024605 2305997 := bbase (se 3 (by rfl) ⟨432374, by rfl⟩ : syracuseStep 2305997 = 864749) (by norm_num)
theorem B3289061 : Blo 1024605 3289061 := bbase (se 4 (by rfl) ⟨308349, by rfl⟩ : syracuseStep 3289061 = 616699) (by norm_num)
theorem B2306069 : Blo 1024605 2306069 := bbase (se 6 (by rfl) ⟨54048, by rfl⟩ : syracuseStep 2306069 = 108097) (by norm_num)
theorem B2600981 : Blo 1024605 2600981 := bbase (se 6 (by rfl) ⟨60960, by rfl⟩ : syracuseStep 2600981 = 121921) (by norm_num)
theorem B5189669 : Blo 1024605 5189669 := bbase (se 4 (by rfl) ⟨486531, by rfl⟩ : syracuseStep 5189669 = 973063) (by norm_num)
theorem B2306141 : Blo 1024605 2306141 := bbase (se 3 (by rfl) ⟨432401, by rfl⟩ : syracuseStep 2306141 = 864803) (by norm_num)
theorem B2306213 : Blo 1024605 2306213 := bbase (se 4 (by rfl) ⟨216207, by rfl⟩ : syracuseStep 2306213 = 432415) (by norm_num)
theorem B2601173 : Blo 1024605 2601173 := bbase (se 7 (by rfl) ⟨30482, by rfl⟩ : syracuseStep 2601173 = 60965) (by norm_num)
theorem B2306285 : Blo 1024605 2306285 := bbase (se 3 (by rfl) ⟨432428, by rfl⟩ : syracuseStep 2306285 = 864857) (by norm_num)
theorem B1945853 : Blo 1024605 1945853 := bbase (se 3 (by rfl) ⟨364847, by rfl⟩ : syracuseStep 1945853 = 729695) (by norm_num)
theorem B2306357 : Blo 1024605 2306357 := bbase (se 5 (by rfl) ⟨108110, by rfl⟩ : syracuseStep 2306357 = 216221) (by norm_num)
theorem B2306429 : Blo 1024605 2306429 := bbase (se 3 (by rfl) ⟨432455, by rfl⟩ : syracuseStep 2306429 = 864911) (by norm_num)
theorem B2470285 : Blo 1024605 2470285 := bbase (se 3 (by rfl) ⟨463178, by rfl⟩ : syracuseStep 2470285 = 926357) (by norm_num)
theorem B2470333 : Blo 1024605 2470333 := bbase (se 3 (by rfl) ⟨463187, by rfl⟩ : syracuseStep 2470333 = 926375) (by norm_num)
theorem B2306501 : Blo 1024605 2306501 := bbase (se 4 (by rfl) ⟨216234, by rfl⟩ : syracuseStep 2306501 = 432469) (by norm_num)
theorem B2306573 : Blo 1024605 2306573 := bbase (se 3 (by rfl) ⟨432482, by rfl⟩ : syracuseStep 2306573 = 864965) (by norm_num)
theorem B2503181 : Blo 1024605 2503181 := bbase (se 3 (by rfl) ⟨469346, by rfl⟩ : syracuseStep 2503181 = 938693) (by norm_num)
theorem B2601517 : Blo 1024605 2601517 := bbase (se 3 (by rfl) ⟨487784, by rfl⟩ : syracuseStep 2601517 = 975569) (by norm_num)
theorem B2306645 : Blo 1024605 2306645 := bbase (se 8 (by rfl) ⟨13515, by rfl⟩ : syracuseStep 2306645 = 27031) (by norm_num)
theorem B2306717 : Blo 1024605 2306717 := bbase (se 3 (by rfl) ⟨432509, by rfl⟩ : syracuseStep 2306717 = 865019) (by norm_num)
theorem B2601629 : Blo 1024605 2601629 := bbase (se 3 (by rfl) ⟨487805, by rfl⟩ : syracuseStep 2601629 = 975611) (by norm_num)
theorem B2306789 : Blo 1024605 2306789 := bbase (se 4 (by rfl) ⟨216261, by rfl⟩ : syracuseStep 2306789 = 432523) (by norm_num)
theorem B2306861 : Blo 1024605 2306861 := bbase (se 3 (by rfl) ⟨432536, by rfl⟩ : syracuseStep 2306861 = 865073) (by norm_num)
theorem B6566741 : Blo 1024605 6566741 := bbase (se 9 (by rfl) ⟨19238, by rfl⟩ : syracuseStep 6566741 = 38477) (by norm_num)
theorem B2601821 : Blo 1024605 2601821 := bbase (se 3 (by rfl) ⟨487841, by rfl⟩ : syracuseStep 2601821 = 975683) (by norm_num)
theorem B2306933 : Blo 1024605 2306933 := bbase (se 5 (by rfl) ⟨108137, by rfl⟩ : syracuseStep 2306933 = 216275) (by norm_num)
theorem B2307005 : Blo 1024605 2307005 := bbase (se 3 (by rfl) ⟨432563, by rfl⟩ : syracuseStep 2307005 = 865127) (by norm_num)
theorem B1389541 : Blo 1024605 1389541 := bbase (se 4 (by rfl) ⟨130269, by rfl⟩ : syracuseStep 1389541 = 260539) (by norm_num)
theorem B1946605 : Blo 1024605 1946605 := bbase (se 3 (by rfl) ⟨364988, by rfl⟩ : syracuseStep 1946605 = 729977) (by norm_num)
theorem B1094645 : Blo 1024605 1094645 := bbase (se 5 (by rfl) ⟨51311, by rfl⟩ : syracuseStep 1094645 = 102623) (by norm_num)
theorem B1782773 : Blo 1024605 1782773 := bbase (se 5 (by rfl) ⟨83567, by rfl⟩ : syracuseStep 1782773 = 167135) (by norm_num)
theorem B2307077 : Blo 1024605 2307077 := bbase (se 4 (by rfl) ⟨216288, by rfl⟩ : syracuseStep 2307077 = 432577) (by norm_num)
theorem B2470949 : Blo 1024605 2470949 := bbase (se 4 (by rfl) ⟨231651, by rfl⟩ : syracuseStep 2470949 = 463303) (by norm_num)
theorem B1782853 : Blo 1024605 1782853 := bbase (se 4 (by rfl) ⟨167142, by rfl⟩ : syracuseStep 1782853 = 334285) (by norm_num)
theorem B2307149 : Blo 1024605 2307149 := bbase (se 3 (by rfl) ⟨432590, by rfl⟩ : syracuseStep 2307149 = 865181) (by norm_num)
theorem B1946749 : Blo 1024605 1946749 := bbase (se 3 (by rfl) ⟨365015, by rfl⟩ : syracuseStep 1946749 = 730031) (by norm_num)
theorem B2307221 : Blo 1024605 2307221 := bbase (se 6 (by rfl) ⟨54075, by rfl⟩ : syracuseStep 2307221 = 108151) (by norm_num)
theorem B1094833 : Blo 1024605 1094833 := bbase (se 2 (by rfl) ⟨410562, by rfl⟩ : syracuseStep 1094833 = 821125) (by norm_num)
theorem B2602165 : Blo 1024605 2602165 := bbase (se 5 (by rfl) ⟨121976, by rfl⟩ : syracuseStep 2602165 = 243953) (by norm_num)
theorem B2307293 : Blo 1024605 2307293 := bbase (se 3 (by rfl) ⟨432617, by rfl⟩ : syracuseStep 2307293 = 865235) (by norm_num)
theorem B1946909 : Blo 1024605 1946909 := bbase (se 3 (by rfl) ⟨365045, by rfl⟩ : syracuseStep 1946909 = 730091) (by norm_num)
theorem B2307365 : Blo 1024605 2307365 := bbase (se 4 (by rfl) ⟨216315, by rfl⟩ : syracuseStep 2307365 = 432631) (by norm_num)
theorem B2602277 : Blo 1024605 2602277 := bbase (se 4 (by rfl) ⟨243963, by rfl⟩ : syracuseStep 2602277 = 487927) (by norm_num)
theorem B5190965 : Blo 1024605 5190965 := bbase (se 5 (by rfl) ⟨243326, by rfl⟩ : syracuseStep 5190965 = 486653) (by norm_num)
theorem B2307437 : Blo 1024605 2307437 := bbase (se 3 (by rfl) ⟨432644, by rfl⟩ : syracuseStep 2307437 = 865289) (by norm_num)
theorem B2471293 : Blo 1024605 2471293 := bbase (se 3 (by rfl) ⟨463367, by rfl⟩ : syracuseStep 2471293 = 926735) (by norm_num)
theorem B1947053 : Blo 1024605 1947053 := bbase (se 3 (by rfl) ⟨365072, by rfl⟩ : syracuseStep 1947053 = 730145) (by norm_num)
theorem B2307509 : Blo 1024605 2307509 := bbase (se 5 (by rfl) ⟨108164, by rfl⟩ : syracuseStep 2307509 = 216329) (by norm_num)
theorem B2340317 : Blo 1024605 2340317 := bbase (se 3 (by rfl) ⟨438809, by rfl⟩ : syracuseStep 2340317 = 877619) (by norm_num)
theorem B2602469 : Blo 1024605 2602469 := bbase (se 4 (by rfl) ⟨243981, by rfl⟩ : syracuseStep 2602469 = 487963) (by norm_num)
theorem B2307581 : Blo 1024605 2307581 := bbase (se 3 (by rfl) ⟨432671, by rfl⟩ : syracuseStep 2307581 = 865343) (by norm_num)
theorem B2307653 : Blo 1024605 2307653 := bbase (se 4 (by rfl) ⟨216342, by rfl⟩ : syracuseStep 2307653 = 432685) (by norm_num)
theorem B2307725 : Blo 1024605 2307725 := bbase (se 3 (by rfl) ⟨432698, by rfl⟩ : syracuseStep 2307725 = 865397) (by norm_num)
theorem B5060245 : Blo 1024605 5060245 := bbase (se 6 (by rfl) ⟨118599, by rfl⟩ : syracuseStep 5060245 = 237199) (by norm_num)
theorem B1947341 : Blo 1024605 1947341 := bbase (se 3 (by rfl) ⟨365126, by rfl⟩ : syracuseStep 1947341 = 730253) (by norm_num)
theorem B2307797 : Blo 1024605 2307797 := bbase (se 7 (by rfl) ⟨27044, by rfl⟩ : syracuseStep 2307797 = 54089) (by norm_num)
theorem B5846741 : Blo 1024605 5846741 := bbase (se 7 (by rfl) ⟨68516, by rfl⟩ : syracuseStep 5846741 = 137033) (by norm_num)
theorem B2307869 : Blo 1024605 2307869 := bbase (se 3 (by rfl) ⟨432725, by rfl⟩ : syracuseStep 2307869 = 865451) (by norm_num)
theorem B2602813 : Blo 1024605 2602813 := bbase (se 3 (by rfl) ⟨488027, by rfl⟩ : syracuseStep 2602813 = 976055) (by norm_num)
theorem B2307941 : Blo 1024605 2307941 := bbase (se 4 (by rfl) ⟨216369, by rfl⟩ : syracuseStep 2307941 = 432739) (by norm_num)
theorem B1947493 : Blo 1024605 1947493 := bbase (se 4 (by rfl) ⟨182577, by rfl⟩ : syracuseStep 1947493 = 365155) (by norm_num)
theorem B11384725 : Blo 1024605 11384725 := bbase (se 6 (by rfl) ⟨266829, by rfl⟩ : syracuseStep 11384725 = 533659) (by norm_num)
theorem B2308013 : Blo 1024605 2308013 := bbase (se 3 (by rfl) ⟨432752, by rfl⟩ : syracuseStep 2308013 = 865505) (by norm_num)
theorem B2602925 : Blo 1024605 2602925 := bbase (se 3 (by rfl) ⟨488048, by rfl⟩ : syracuseStep 2602925 = 976097) (by norm_num)
theorem B1095653 : Blo 1024605 1095653 := bbase (se 4 (by rfl) ⟨102717, by rfl⟩ : syracuseStep 1095653 = 205435) (by norm_num)
theorem B2308085 : Blo 1024605 2308085 := bbase (se 5 (by rfl) ⟨108191, by rfl⟩ : syracuseStep 2308085 = 216383) (by norm_num)
theorem B2308157 : Blo 1024605 2308157 := bbase (se 3 (by rfl) ⟨432779, by rfl⟩ : syracuseStep 2308157 = 865559) (by norm_num)
theorem B2078797 : Blo 1024605 2078797 := bbase (se 3 (by rfl) ⟨389774, by rfl⟩ : syracuseStep 2078797 = 779549) (by norm_num)
theorem B2603117 : Blo 1024605 2603117 := bbase (se 3 (by rfl) ⟨488084, by rfl⟩ : syracuseStep 2603117 = 976169) (by norm_num)
theorem B2308229 : Blo 1024605 2308229 := bbase (se 4 (by rfl) ⟨216396, by rfl⟩ : syracuseStep 2308229 = 432793) (by norm_num)
theorem B1947797 : Blo 1024605 1947797 := bbase (se 6 (by rfl) ⟨45651, by rfl⟩ : syracuseStep 1947797 = 91303) (by norm_num)
theorem B3291317 : Blo 1024605 3291317 := bbase (se 5 (by rfl) ⟨154280, by rfl⟩ : syracuseStep 3291317 = 308561) (by norm_num)
theorem B2308301 : Blo 1024605 2308301 := bbase (se 3 (by rfl) ⟨432806, by rfl⟩ : syracuseStep 2308301 = 865613) (by norm_num)
theorem B1849549 : Blo 1024605 1849549 := bbase (se 3 (by rfl) ⟨346790, by rfl⟩ : syracuseStep 1849549 = 693581) (by norm_num)
theorem B2308373 : Blo 1024605 2308373 := bbase (se 6 (by rfl) ⟨54102, by rfl⟩ : syracuseStep 2308373 = 108205) (by norm_num)
theorem B2308445 : Blo 1024605 2308445 := bbase (se 3 (by rfl) ⟨432833, by rfl⟩ : syracuseStep 2308445 = 865667) (by norm_num)
theorem B1096097 : Blo 1024605 1096097 := bbase (se 2 (by rfl) ⟨411036, by rfl⟩ : syracuseStep 1096097 = 822073) (by norm_num)
theorem B2308517 : Blo 1024605 2308517 := bbase (se 4 (by rfl) ⟨216423, by rfl⟩ : syracuseStep 2308517 = 432847) (by norm_num)
theorem B1030577 : Blo 1024605 1030577 := bbase (se 2 (by rfl) ⟨386466, by rfl⟩ : syracuseStep 1030577 = 772933) (by norm_num)
theorem B2603461 : Blo 1024605 2603461 := bbase (se 4 (by rfl) ⟨244074, by rfl⟩ : syracuseStep 2603461 = 488149) (by norm_num)
theorem B2308589 : Blo 1024605 2308589 := bbase (se 3 (by rfl) ⟨432860, by rfl⟩ : syracuseStep 2308589 = 865721) (by norm_num)
theorem B1849853 : Blo 1024605 1849853 := bbase (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) (by norm_num)
theorem B2079245 : Blo 1024605 2079245 := bbase (se 3 (by rfl) ⟨389858, by rfl⟩ : syracuseStep 2079245 = 779717) (by norm_num)
theorem B2308661 : Blo 1024605 2308661 := bbase (se 5 (by rfl) ⟨108218, by rfl⟩ : syracuseStep 2308661 = 216437) (by norm_num)
theorem B2603573 : Blo 1024605 2603573 := bbase (se 5 (by rfl) ⟨122042, by rfl⟩ : syracuseStep 2603573 = 244085) (by norm_num)
theorem B5192261 : Blo 1024605 5192261 := bbase (se 4 (by rfl) ⟨486774, by rfl⟩ : syracuseStep 5192261 = 973549) (by norm_num)
theorem B2308733 : Blo 1024605 2308733 := bbase (se 3 (by rfl) ⟨432887, by rfl⟩ : syracuseStep 2308733 = 865775) (by norm_num)
theorem B1096345 : Blo 1024605 1096345 := bbase (se 2 (by rfl) ⟨411129, by rfl⟩ : syracuseStep 1096345 = 822259) (by norm_num)
theorem B2308805 : Blo 1024605 2308805 := bbase (se 4 (by rfl) ⟨216450, by rfl⟩ : syracuseStep 2308805 = 432901) (by norm_num)
theorem B2308877 : Blo 1024605 2308877 := bbase (se 3 (by rfl) ⟨432914, by rfl⟩ : syracuseStep 2308877 = 865829) (by norm_num)
theorem B2308949 : Blo 1024605 2308949 := bbase (se 9 (by rfl) ⟨6764, by rfl⟩ : syracuseStep 2308949 = 13529) (by norm_num)
theorem B21379925 : Blo 1024605 21379925 := bbase (se 9 (by rfl) ⟨62636, by rfl⟩ : syracuseStep 21379925 = 125273) (by norm_num)
theorem B1948549 : Blo 1024605 1948549 := bbase (se 4 (by rfl) ⟨182676, by rfl⟩ : syracuseStep 1948549 = 365353) (by norm_num)
theorem B2309021 : Blo 1024605 2309021 := bbase (se 3 (by rfl) ⟨432941, by rfl⟩ : syracuseStep 2309021 = 865883) (by norm_num)
theorem B3292085 : Blo 1024605 3292085 := bbase (se 5 (by rfl) ⟨154316, by rfl⟩ : syracuseStep 3292085 = 308633) (by norm_num)
theorem B2309093 : Blo 1024605 2309093 := bbase (se 4 (by rfl) ⟨216477, by rfl⟩ : syracuseStep 2309093 = 432955) (by norm_num)
theorem B1948693 : Blo 1024605 1948693 := bbase (se 6 (by rfl) ⟨45672, by rfl⟩ : syracuseStep 1948693 = 91345) (by norm_num)
theorem B2309165 : Blo 1024605 2309165 := bbase (se 3 (by rfl) ⟨432968, by rfl⟩ : syracuseStep 2309165 = 865937) (by norm_num)
theorem B1096777 : Blo 1024605 1096777 := bbase (se 2 (by rfl) ⟨411291, by rfl⟩ : syracuseStep 1096777 = 822583) (by norm_num)
theorem B2309237 : Blo 1024605 2309237 := bbase (se 5 (by rfl) ⟨108245, by rfl⟩ : syracuseStep 2309237 = 216491) (by norm_num)
theorem B1096849 : Blo 1024605 1096849 := bbase (se 2 (by rfl) ⟨411318, by rfl⟩ : syracuseStep 1096849 = 822637) (by norm_num)
theorem B1948853 : Blo 1024605 1948853 := bbase (se 5 (by rfl) ⟨91352, by rfl⟩ : syracuseStep 1948853 = 182705) (by norm_num)
theorem B2309309 : Blo 1024605 2309309 := bbase (se 3 (by rfl) ⟨432995, by rfl⟩ : syracuseStep 2309309 = 865991) (by norm_num)
theorem B2309381 : Blo 1024605 2309381 := bbase (se 4 (by rfl) ⟨216504, by rfl⟩ : syracuseStep 2309381 = 433009) (by norm_num)
theorem B1948997 : Blo 1024605 1948997 := bbase (se 4 (by rfl) ⟨182718, by rfl⟩ : syracuseStep 1948997 = 365437) (by norm_num)
theorem B2309453 : Blo 1024605 2309453 := bbase (se 3 (by rfl) ⟨433022, by rfl⟩ : syracuseStep 2309453 = 866045) (by norm_num)
theorem B4930901 : Blo 1024605 4930901 := bbase (se 11 (by rfl) ⟨3611, by rfl⟩ : syracuseStep 4930901 = 7223) (by norm_num)
theorem B2309525 : Blo 1024605 2309525 := bbase (se 6 (by rfl) ⟨54129, by rfl⟩ : syracuseStep 2309525 = 108259) (by norm_num)
theorem B1850789 : Blo 1024605 1850789 := bbase (se 4 (by rfl) ⟨173511, by rfl⟩ : syracuseStep 1850789 = 347023) (by norm_num)
theorem B3292597 : Blo 1024605 3292597 := bbase (se 5 (by rfl) ⟨154340, by rfl⟩ : syracuseStep 3292597 = 308681) (by norm_num)
theorem B2309597 : Blo 1024605 2309597 := bbase (se 3 (by rfl) ⟨433049, by rfl⟩ : syracuseStep 2309597 = 866099) (by norm_num)
theorem B1097221 : Blo 1024605 1097221 := bbase (se 4 (by rfl) ⟨102864, by rfl⟩ : syracuseStep 1097221 = 205729) (by norm_num)
theorem B8764949 : Blo 1024605 8764949 := bbase (se 6 (by rfl) ⟨205428, by rfl⟩ : syracuseStep 8764949 = 410857) (by norm_num)
theorem B4931093 : Blo 1024605 4931093 := bbase (se 6 (by rfl) ⟨115572, by rfl⟩ : syracuseStep 4931093 = 231145) (by norm_num)
theorem B2309669 : Blo 1024605 2309669 := bbase (se 4 (by rfl) ⟨216531, by rfl⟩ : syracuseStep 2309669 = 433063) (by norm_num)
theorem B1949285 : Blo 1024605 1949285 := bbase (se 4 (by rfl) ⟨182745, by rfl⟩ : syracuseStep 1949285 = 365491) (by norm_num)
theorem B2309741 : Blo 1024605 2309741 := bbase (se 3 (by rfl) ⟨433076, by rfl⟩ : syracuseStep 2309741 = 866153) (by norm_num)
theorem B2309813 : Blo 1024605 2309813 := bbase (se 5 (by rfl) ⟨108272, by rfl⟩ : syracuseStep 2309813 = 216545) (by norm_num)
theorem B1752781 : Blo 1024605 1752781 := bbase (se 3 (by rfl) ⟨328646, by rfl⟩ : syracuseStep 1752781 = 657293) (by norm_num)
theorem B2309885 : Blo 1024605 2309885 := bbase (se 3 (by rfl) ⟨433103, by rfl⟩ : syracuseStep 2309885 = 866207) (by norm_num)
theorem B1949437 : Blo 1024605 1949437 := bbase (se 3 (by rfl) ⟨365519, by rfl⟩ : syracuseStep 1949437 = 731039) (by norm_num)
theorem B2309957 : Blo 1024605 2309957 := bbase (se 4 (by rfl) ⟨216558, by rfl⟩ : syracuseStep 2309957 = 433117) (by norm_num)
theorem B5193557 : Blo 1024605 5193557 := bbase (se 9 (by rfl) ⟨15215, by rfl⟩ : syracuseStep 5193557 = 30431) (by norm_num)
theorem B2080613 : Blo 1024605 2080613 := bbase (se 4 (by rfl) ⟨195057, by rfl⟩ : syracuseStep 2080613 = 390115) (by norm_num)
theorem B5848949 : Blo 1024605 5848949 := bbase (se 5 (by rfl) ⟨274169, by rfl⟩ : syracuseStep 5848949 = 548339) (by norm_num)
theorem B1097597 : Blo 1024605 1097597 := bbase (se 3 (by rfl) ⟨205799, by rfl⟩ : syracuseStep 1097597 = 411599) (by norm_num)
theorem B2310029 : Blo 1024605 2310029 := bbase (se 3 (by rfl) ⟨433130, by rfl⟩ : syracuseStep 2310029 = 866261) (by norm_num)
theorem B1097669 : Blo 1024605 1097669 := bbase (se 4 (by rfl) ⟨102906, by rfl⟩ : syracuseStep 1097669 = 205813) (by norm_num)
theorem B2310101 : Blo 1024605 2310101 := bbase (se 7 (by rfl) ⟨27071, by rfl⟩ : syracuseStep 2310101 = 54143) (by norm_num)
theorem B2310173 : Blo 1024605 2310173 := bbase (se 3 (by rfl) ⟨433157, by rfl⟩ : syracuseStep 2310173 = 866315) (by norm_num)
theorem B1949741 : Blo 1024605 1949741 := bbase (se 3 (by rfl) ⟨365576, by rfl⟩ : syracuseStep 1949741 = 731153) (by norm_num)
theorem B2310245 : Blo 1024605 2310245 := bbase (se 4 (by rfl) ⟨216585, by rfl⟩ : syracuseStep 2310245 = 433171) (by norm_num)
theorem B1097857 : Blo 1024605 1097857 := bbase (se 2 (by rfl) ⟨411696, by rfl⟩ : syracuseStep 1097857 = 823393) (by norm_num)
theorem B2310317 : Blo 1024605 2310317 := bbase (se 3 (by rfl) ⟨433184, by rfl⟩ : syracuseStep 2310317 = 866369) (by norm_num)
theorem B2310389 : Blo 1024605 2310389 := bbase (se 5 (by rfl) ⟨108299, by rfl⟩ : syracuseStep 2310389 = 216599) (by norm_num)
theorem B1098041 : Blo 1024605 1098041 := bbase (se 2 (by rfl) ⟨411765, by rfl⟩ : syracuseStep 1098041 = 823531) (by norm_num)
theorem B2310461 : Blo 1024605 2310461 := bbase (se 3 (by rfl) ⟨433211, by rfl⟩ : syracuseStep 2310461 = 866423) (by norm_num)
theorem B2310533 : Blo 1024605 2310533 := bbase (se 4 (by rfl) ⟨216612, by rfl⟩ : syracuseStep 2310533 = 433225) (by norm_num)
theorem B2310605 : Blo 1024605 2310605 := bbase (se 3 (by rfl) ⟨433238, by rfl⟩ : syracuseStep 2310605 = 866477) (by norm_num)
theorem B11715029 : Blo 1024605 11715029 := bbase (se 7 (by rfl) ⟨137285, by rfl⟩ : syracuseStep 11715029 = 274571) (by norm_num)
theorem B2310677 : Blo 1024605 2310677 := bbase (se 6 (by rfl) ⟨54156, by rfl⟩ : syracuseStep 2310677 = 108313) (by norm_num)
theorem B7029269 : Blo 1024605 7029269 := bbase (se 6 (by rfl) ⟨164748, by rfl⟩ : syracuseStep 7029269 = 329497) (by norm_num)
theorem B2310749 : Blo 1024605 2310749 := bbase (se 3 (by rfl) ⟨433265, by rfl⟩ : syracuseStep 2310749 = 866531) (by norm_num)
theorem B2310821 : Blo 1024605 2310821 := bbase (se 4 (by rfl) ⟨216639, by rfl⟩ : syracuseStep 2310821 = 433279) (by norm_num)
theorem B2966213 : Blo 1024605 2966213 := bbase (se 4 (by rfl) ⟨278082, by rfl⟩ : syracuseStep 2966213 = 556165) (by norm_num)
theorem B4997861 : Blo 1024605 4997861 := bbase (se 4 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 4997861 = 937099) (by norm_num)
theorem B2310893 : Blo 1024605 2310893 := bbase (se 3 (by rfl) ⟨433292, by rfl⟩ : syracuseStep 2310893 = 866585) (by norm_num)
theorem B1950493 : Blo 1024605 1950493 := bbase (se 3 (by rfl) ⟨365717, by rfl⟩ : syracuseStep 1950493 = 731435) (by norm_num)
theorem B2310965 : Blo 1024605 2310965 := bbase (se 5 (by rfl) ⟨108326, by rfl⟩ : syracuseStep 2310965 = 216653) (by norm_num)
theorem B2311037 : Blo 1024605 2311037 := bbase (se 3 (by rfl) ⟨433319, by rfl⟩ : syracuseStep 2311037 = 866639) (by norm_num)
theorem B1950637 : Blo 1024605 1950637 := bbase (se 3 (by rfl) ⟨365744, by rfl⟩ : syracuseStep 1950637 = 731489) (by norm_num)
theorem B2081717 : Blo 1024605 2081717 := bbase (se 5 (by rfl) ⟨97580, by rfl⟩ : syracuseStep 2081717 = 195161) (by norm_num)
theorem B2311109 : Blo 1024605 2311109 := bbase (se 4 (by rfl) ⟨216666, by rfl⟩ : syracuseStep 2311109 = 433333) (by norm_num)
theorem B2311181 : Blo 1024605 2311181 := bbase (se 3 (by rfl) ⟨433346, by rfl⟩ : syracuseStep 2311181 = 866693) (by norm_num)
theorem B1459253 : Blo 1024605 1459253 := bbase (se 5 (by rfl) ⟨68402, by rfl⟩ : syracuseStep 1459253 = 136805) (by norm_num)
theorem B1950797 : Blo 1024605 1950797 := bbase (se 3 (by rfl) ⟨365774, by rfl⟩ : syracuseStep 1950797 = 731549) (by norm_num)
theorem B2311253 : Blo 1024605 2311253 := bbase (se 8 (by rfl) ⟨13542, by rfl⟩ : syracuseStep 2311253 = 27085) (by norm_num)
theorem B5194853 : Blo 1024605 5194853 := bbase (se 4 (by rfl) ⟨487017, by rfl⟩ : syracuseStep 5194853 = 974035) (by norm_num)
theorem B9847925 : Blo 1024605 9847925 := bbase (se 5 (by rfl) ⟨461621, by rfl⟩ : syracuseStep 9847925 = 923243) (by norm_num)
theorem B1459333 : Blo 1024605 1459333 := bbase (se 4 (by rfl) ⟨136812, by rfl⟩ : syracuseStep 1459333 = 273625) (by norm_num)
theorem B3294341 : Blo 1024605 3294341 := bbase (se 4 (by rfl) ⟨308844, by rfl⟩ : syracuseStep 3294341 = 617689) (by norm_num)
theorem B2311325 : Blo 1024605 2311325 := bbase (se 3 (by rfl) ⟨433373, by rfl⟩ : syracuseStep 2311325 = 866747) (by norm_num)
theorem B3458213 : Blo 1024605 3458213 := bbase (se 4 (by rfl) ⟨324207, by rfl⟩ : syracuseStep 3458213 = 648415) (by norm_num)
theorem B1950941 : Blo 1024605 1950941 := bbase (se 3 (by rfl) ⟨365801, by rfl⟩ : syracuseStep 1950941 = 731603) (by norm_num)
theorem B2344157 : Blo 1024605 2344157 := bbase (se 3 (by rfl) ⟨439529, by rfl⟩ : syracuseStep 2344157 = 879059) (by norm_num)
theorem B2311397 : Blo 1024605 2311397 := bbase (se 4 (by rfl) ⟨216693, by rfl⟩ : syracuseStep 2311397 = 433387) (by norm_num)
theorem B1459453 : Blo 1024605 1459453 := bbase (se 3 (by rfl) ⟨273647, by rfl⟩ : syracuseStep 1459453 = 547295) (by norm_num)
theorem B2311469 : Blo 1024605 2311469 := bbase (se 3 (by rfl) ⟨433400, by rfl⟩ : syracuseStep 2311469 = 866801) (by norm_num)
theorem B3294533 : Blo 1024605 3294533 := bbase (se 4 (by rfl) ⟨308862, by rfl⟩ : syracuseStep 3294533 = 617725) (by norm_num)
theorem B2966869 : Blo 1024605 2966869 := bbase (se 12 (by rfl) ⟨1086, by rfl⟩ : syracuseStep 2966869 = 2173) (by norm_num)
theorem B1459549 : Blo 1024605 1459549 := bbase (se 3 (by rfl) ⟨273665, by rfl⟩ : syracuseStep 1459549 = 547331) (by norm_num)
theorem B2311541 : Blo 1024605 2311541 := bbase (se 5 (by rfl) ⟨108353, by rfl⟩ : syracuseStep 2311541 = 216707) (by norm_num)
theorem B2311613 : Blo 1024605 2311613 := bbase (se 3 (by rfl) ⟨433427, by rfl⟩ : syracuseStep 2311613 = 866855) (by norm_num)
theorem B2344405 : Blo 1024605 2344405 := bbase (se 7 (by rfl) ⟨27473, by rfl⟩ : syracuseStep 2344405 = 54947) (by norm_num)
theorem B1951229 : Blo 1024605 1951229 := bbase (se 3 (by rfl) ⟨365855, by rfl⟩ : syracuseStep 1951229 = 731711) (by norm_num)
theorem B2311685 : Blo 1024605 2311685 := bbase (se 4 (by rfl) ⟨216720, by rfl⟩ : syracuseStep 2311685 = 433441) (by norm_num)
theorem B2311757 : Blo 1024605 2311757 := bbase (se 3 (by rfl) ⟨433454, by rfl⟩ : syracuseStep 2311757 = 866909) (by norm_num)
theorem B3458645 : Blo 1024605 3458645 := bbase (se 8 (by rfl) ⟨20265, by rfl⟩ : syracuseStep 3458645 = 40531) (by norm_num)
theorem B2311829 : Blo 1024605 2311829 := bbase (se 6 (by rfl) ⟨54183, by rfl⟩ : syracuseStep 2311829 = 108367) (by norm_num)
theorem B1951381 : Blo 1024605 1951381 := bbase (se 6 (by rfl) ⟨45735, by rfl⟩ : syracuseStep 1951381 = 91471) (by norm_num)
theorem B2311901 : Blo 1024605 2311901 := bbase (se 3 (by rfl) ⟨433481, by rfl⟩ : syracuseStep 2311901 = 866963) (by norm_num)
theorem B2311973 : Blo 1024605 2311973 := bbase (se 4 (by rfl) ⟨216747, by rfl⟩ : syracuseStep 2311973 = 433495) (by norm_num)
theorem B1460045 : Blo 1024605 1460045 := bbase (se 3 (by rfl) ⟨273758, by rfl⟩ : syracuseStep 1460045 = 547517) (by norm_num)
theorem B2312045 : Blo 1024605 2312045 := bbase (se 3 (by rfl) ⟨433508, by rfl⟩ : syracuseStep 2312045 = 867017) (by norm_num)
theorem B2312117 : Blo 1024605 2312117 := bbase (se 5 (by rfl) ⟨108380, by rfl⟩ : syracuseStep 2312117 = 216761) (by norm_num)
theorem B1951685 : Blo 1024605 1951685 := bbase (se 4 (by rfl) ⟨182970, by rfl⟩ : syracuseStep 1951685 = 365941) (by norm_num)
theorem B2312189 : Blo 1024605 2312189 := bbase (se 3 (by rfl) ⟨433535, by rfl⟩ : syracuseStep 2312189 = 867071) (by norm_num)
theorem B3459077 : Blo 1024605 3459077 := bbase (se 4 (by rfl) ⟨324288, by rfl⟩ : syracuseStep 3459077 = 648577) (by norm_num)
theorem B2312261 : Blo 1024605 2312261 := bbase (se 4 (by rfl) ⟨216774, by rfl⟩ : syracuseStep 2312261 = 433549) (by norm_num)
theorem B2312333 : Blo 1024605 2312333 := bbase (se 3 (by rfl) ⟨433562, by rfl⟩ : syracuseStep 2312333 = 867125) (by norm_num)
theorem B2312405 : Blo 1024605 2312405 := bbase (se 7 (by rfl) ⟨27098, by rfl⟩ : syracuseStep 2312405 = 54197) (by norm_num)
theorem B2312477 : Blo 1024605 2312477 := bbase (se 3 (by rfl) ⟨433589, by rfl⟩ : syracuseStep 2312477 = 867179) (by norm_num)
theorem B2312549 : Blo 1024605 2312549 := bbase (se 4 (by rfl) ⟨216801, by rfl⟩ : syracuseStep 2312549 = 433603) (by norm_num)
theorem B1460597 : Blo 1024605 1460597 := bbase (se 5 (by rfl) ⟨68465, by rfl⟩ : syracuseStep 1460597 = 136931) (by norm_num)
theorem B5196149 : Blo 1024605 5196149 := bbase (se 5 (by rfl) ⟨243569, by rfl⟩ : syracuseStep 5196149 = 487139) (by norm_num)
theorem B1296805 : Blo 1024605 1296805 := bbase (se 4 (by rfl) ⟨121575, by rfl⟩ : syracuseStep 1296805 = 243151) (by norm_num)
theorem B2312621 : Blo 1024605 2312621 := bbase (se 3 (by rfl) ⟨433616, by rfl⟩ : syracuseStep 2312621 = 867233) (by norm_num)
theorem B3459509 : Blo 1024605 3459509 := bbase (se 5 (by rfl) ⟨162164, by rfl⟩ : syracuseStep 3459509 = 324329) (by norm_num)
theorem B8767925 : Blo 1024605 8767925 := bbase (se 5 (by rfl) ⟨410996, by rfl⟩ : syracuseStep 8767925 = 821993) (by norm_num)
theorem B4377077 : Blo 1024605 4377077 := bbase (se 5 (by rfl) ⟨205175, by rfl⟩ : syracuseStep 4377077 = 410351) (by norm_num)
theorem B2312693 : Blo 1024605 2312693 := bbase (se 5 (by rfl) ⟨108407, by rfl⟩ : syracuseStep 2312693 = 216815) (by norm_num)
theorem B1296901 : Blo 1024605 1296901 := bbase (se 4 (by rfl) ⟨121584, by rfl⟩ : syracuseStep 1296901 = 243169) (by norm_num)
theorem B5556757 : Blo 1024605 5556757 := bbase (se 6 (by rfl) ⟨130236, by rfl⟩ : syracuseStep 5556757 = 260473) (by norm_num)
theorem B2312765 : Blo 1024605 2312765 := bbase (se 3 (by rfl) ⟨433643, by rfl⟩ : syracuseStep 2312765 = 867287) (by norm_num)
theorem B2312837 : Blo 1024605 2312837 := bbase (se 4 (by rfl) ⟨216828, by rfl⟩ : syracuseStep 2312837 = 433657) (by norm_num)
theorem B1231529 : Blo 1024605 1231529 := bbase (se 2 (by rfl) ⟨461823, by rfl⟩ : syracuseStep 1231529 = 923647) (by norm_num)
theorem B1297073 : Blo 1024605 1297073 := bbase (se 2 (by rfl) ⟨486402, by rfl⟩ : syracuseStep 1297073 = 972805) (by norm_num)
theorem B1952437 : Blo 1024605 1952437 := bbase (se 5 (by rfl) ⟨91520, by rfl⟩ : syracuseStep 1952437 = 183041) (by norm_num)
theorem B2312909 : Blo 1024605 2312909 := bbase (se 3 (by rfl) ⟨433670, by rfl⟩ : syracuseStep 2312909 = 867341) (by norm_num)
theorem B1297129 : Blo 1024605 1297129 := bbase (se 2 (by rfl) ⟨486423, by rfl⟩ : syracuseStep 1297129 = 972847) (by norm_num)
theorem B2312981 : Blo 1024605 2312981 := bbase (se 6 (by rfl) ⟨54210, by rfl⟩ : syracuseStep 2312981 = 108421) (by norm_num)
theorem B1952581 : Blo 1024605 1952581 := bbase (se 4 (by rfl) ⟨183054, by rfl⟩ : syracuseStep 1952581 = 366109) (by norm_num)
theorem B1297225 : Blo 1024605 1297225 := bbase (se 2 (by rfl) ⟨486459, by rfl⟩ : syracuseStep 1297225 = 972919) (by norm_num)
theorem B1231697 : Blo 1024605 1231697 := bbase (se 2 (by rfl) ⟨461886, by rfl⟩ : syracuseStep 1231697 = 923773) (by norm_num)
theorem B2313053 : Blo 1024605 2313053 := bbase (se 3 (by rfl) ⟨433697, by rfl⟩ : syracuseStep 2313053 = 867395) (by norm_num)
theorem B3459941 : Blo 1024605 3459941 := bbase (se 4 (by rfl) ⟨324369, by rfl⟩ : syracuseStep 3459941 = 648739) (by norm_num)
theorem B9882485 : Blo 1024605 9882485 := bbase (se 5 (by rfl) ⟨463241, by rfl⟩ : syracuseStep 9882485 = 926483) (by norm_num)
theorem B2313125 : Blo 1024605 2313125 := bbase (se 4 (by rfl) ⟨216855, by rfl⟩ : syracuseStep 2313125 = 433711) (by norm_num)
theorem B1952741 : Blo 1024605 1952741 := bbase (se 4 (by rfl) ⟨183069, by rfl⟩ : syracuseStep 1952741 = 366139) (by norm_num)
theorem B2313197 : Blo 1024605 2313197 := bbase (se 3 (by rfl) ⟨433724, by rfl⟩ : syracuseStep 2313197 = 867449) (by norm_num)
theorem B1297397 : Blo 1024605 1297397 := bbase (se 5 (by rfl) ⟨60815, by rfl⟩ : syracuseStep 1297397 = 121631) (by norm_num)
theorem B1297453 : Blo 1024605 1297453 := bbase (se 3 (by rfl) ⟨243272, by rfl⟩ : syracuseStep 1297453 = 486545) (by norm_num)
theorem B2313269 : Blo 1024605 2313269 := bbase (se 5 (by rfl) ⟨108434, by rfl⟩ : syracuseStep 2313269 = 216869) (by norm_num)
theorem B1461349 : Blo 1024605 1461349 := bbase (se 4 (by rfl) ⟨137001, by rfl⟩ : syracuseStep 1461349 = 274003) (by norm_num)
theorem B2313341 : Blo 1024605 2313341 := bbase (se 3 (by rfl) ⟨433751, by rfl⟩ : syracuseStep 2313341 = 867503) (by norm_num)
theorem B1232005 : Blo 1024605 1232005 := bbase (se 4 (by rfl) ⟨115500, by rfl⟩ : syracuseStep 1232005 = 231001) (by norm_num)
theorem B1297549 : Blo 1024605 1297549 := bbase (se 3 (by rfl) ⟨243290, by rfl⟩ : syracuseStep 1297549 = 486581) (by norm_num)
theorem B2313413 : Blo 1024605 2313413 := bbase (se 4 (by rfl) ⟨216882, by rfl⟩ : syracuseStep 2313413 = 433765) (by norm_num)
theorem B2084069 : Blo 1024605 2084069 := bbase (se 4 (by rfl) ⟨195381, by rfl⟩ : syracuseStep 2084069 = 390763) (by norm_num)
theorem B2313485 : Blo 1024605 2313485 := bbase (se 3 (by rfl) ⟨433778, by rfl⟩ : syracuseStep 2313485 = 867557) (by norm_num)
theorem B3460373 : Blo 1024605 3460373 := bbase (se 6 (by rfl) ⟨81102, by rfl⟩ : syracuseStep 3460373 = 162205) (by norm_num)
theorem B1297721 : Blo 1024605 1297721 := bbase (se 2 (by rfl) ⟨486645, by rfl⟩ : syracuseStep 1297721 = 973291) (by norm_num)
theorem B2313557 : Blo 1024605 2313557 := bbase (se 11 (by rfl) ⟨1694, by rfl⟩ : syracuseStep 2313557 = 3389) (by norm_num)
theorem B1232221 : Blo 1024605 1232221 := bbase (se 3 (by rfl) ⟨231041, by rfl⟩ : syracuseStep 1232221 = 462083) (by norm_num)
theorem B1297777 : Blo 1024605 1297777 := bbase (se 2 (by rfl) ⟨486666, by rfl⟩ : syracuseStep 1297777 = 973333) (by norm_num)
theorem B2313629 : Blo 1024605 2313629 := bbase (se 3 (by rfl) ⟨433805, by rfl⟩ : syracuseStep 2313629 = 867611) (by norm_num)
theorem B1297873 : Blo 1024605 1297873 := bbase (se 2 (by rfl) ⟨486702, by rfl⟩ : syracuseStep 1297873 = 973405) (by norm_num)
theorem B2313701 : Blo 1024605 2313701 := bbase (se 4 (by rfl) ⟨216909, by rfl⟩ : syracuseStep 2313701 = 433819) (by norm_num)
theorem B4935205 : Blo 1024605 4935205 := bbase (se 4 (by rfl) ⟨462675, by rfl⟩ : syracuseStep 4935205 = 925351) (by norm_num)
theorem B2313773 : Blo 1024605 2313773 := bbase (se 3 (by rfl) ⟨433832, by rfl⟩ : syracuseStep 2313773 = 867665) (by norm_num)
theorem B2313845 : Blo 1024605 2313845 := bbase (se 5 (by rfl) ⟨108461, by rfl⟩ : syracuseStep 2313845 = 216923) (by norm_num)
theorem B1298045 : Blo 1024605 1298045 := bbase (se 3 (by rfl) ⟨243383, by rfl⟩ : syracuseStep 1298045 = 486767) (by norm_num)
theorem B5197445 : Blo 1024605 5197445 := bbase (se 4 (by rfl) ⟨487260, by rfl⟩ : syracuseStep 5197445 = 974521) (by norm_num)
theorem B1232533 : Blo 1024605 1232533 := bbase (se 6 (by rfl) ⟨28887, by rfl⟩ : syracuseStep 1232533 = 57775) (by norm_num)
theorem B1298101 : Blo 1024605 1298101 := bbase (se 5 (by rfl) ⟨60848, by rfl⟩ : syracuseStep 1298101 = 121697) (by norm_num)
theorem B2313917 : Blo 1024605 2313917 := bbase (se 3 (by rfl) ⟨433859, by rfl⟩ : syracuseStep 2313917 = 867719) (by norm_num)
theorem B3460805 : Blo 1024605 3460805 := bbase (se 4 (by rfl) ⟨324450, by rfl⟩ : syracuseStep 3460805 = 648901) (by norm_num)
theorem B2313989 : Blo 1024605 2313989 := bbase (se 4 (by rfl) ⟨216936, by rfl⟩ : syracuseStep 2313989 = 433873) (by norm_num)
theorem B1298197 : Blo 1024605 1298197 := bbase (se 6 (by rfl) ⟨30426, by rfl⟩ : syracuseStep 1298197 = 60853) (by norm_num)
theorem B2314061 : Blo 1024605 2314061 := bbase (se 3 (by rfl) ⟨433886, by rfl⟩ : syracuseStep 2314061 = 867773) (by norm_num)
theorem B1462141 : Blo 1024605 1462141 := bbase (se 3 (by rfl) ⟨274151, by rfl⟩ : syracuseStep 1462141 = 548303) (by norm_num)
theorem B2314133 : Blo 1024605 2314133 := bbase (se 6 (by rfl) ⟨54237, by rfl⟩ : syracuseStep 2314133 = 108475) (by norm_num)
theorem B1298369 : Blo 1024605 1298369 := bbase (se 2 (by rfl) ⟨486888, by rfl⟩ : syracuseStep 1298369 = 973777) (by norm_num)
theorem B2314205 : Blo 1024605 2314205 := bbase (se 3 (by rfl) ⟨433913, by rfl⟩ : syracuseStep 2314205 = 867827) (by norm_num)
theorem B1298425 : Blo 1024605 1298425 := bbase (se 2 (by rfl) ⟨486909, by rfl⟩ : syracuseStep 1298425 = 973819) (by norm_num)
theorem B2314277 : Blo 1024605 2314277 := bbase (se 4 (by rfl) ⟨216963, by rfl⟩ : syracuseStep 2314277 = 433927) (by norm_num)
theorem B1298521 : Blo 1024605 1298521 := bbase (se 2 (by rfl) ⟨486945, by rfl⟩ : syracuseStep 1298521 = 973891) (by norm_num)
theorem B2314349 : Blo 1024605 2314349 := bbase (se 3 (by rfl) ⟨433940, by rfl⟩ : syracuseStep 2314349 = 867881) (by norm_num)
theorem B3461237 : Blo 1024605 3461237 := bbase (se 5 (by rfl) ⟨162245, by rfl⟩ : syracuseStep 3461237 = 324491) (by norm_num)
theorem B1462477 : Blo 1024605 1462477 := bbase (se 3 (by rfl) ⟨274214, by rfl⟩ : syracuseStep 1462477 = 548429) (by norm_num)
theorem B4378853 : Blo 1024605 4378853 := bbase (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) (by norm_num)
theorem B1298693 : Blo 1024605 1298693 := bbase (se 4 (by rfl) ⟨121752, by rfl⟩ : syracuseStep 1298693 = 243505) (by norm_num)
theorem B2674949 : Blo 1024605 2674949 := bbase (se 4 (by rfl) ⟨250776, by rfl⟩ : syracuseStep 2674949 = 501553) (by norm_num)
theorem B1298749 : Blo 1024605 1298749 := bbase (se 3 (by rfl) ⟨243515, by rfl⟩ : syracuseStep 1298749 = 487031) (by norm_num)
theorem B1298845 : Blo 1024605 1298845 := bbase (se 3 (by rfl) ⟨243533, by rfl⟩ : syracuseStep 1298845 = 487067) (by norm_num)
theorem B1462693 : Blo 1024605 1462693 := bbase (se 4 (by rfl) ⟨137127, by rfl⟩ : syracuseStep 1462693 = 274255) (by norm_num)
theorem B4379093 : Blo 1024605 4379093 := bbase (se 7 (by rfl) ⟨51317, by rfl⟩ : syracuseStep 4379093 = 102635) (by norm_num)
theorem B3461669 : Blo 1024605 3461669 := bbase (se 4 (by rfl) ⟨324531, by rfl⟩ : syracuseStep 3461669 = 649063) (by norm_num)
theorem B1561141 : Blo 1024605 1561141 := bbase (se 5 (by rfl) ⟨73178, by rfl⟩ : syracuseStep 1561141 = 146357) (by norm_num)
theorem B1299017 : Blo 1024605 1299017 := bbase (se 2 (by rfl) ⟨487131, by rfl⟩ : syracuseStep 1299017 = 974263) (by norm_num)
theorem B1299073 : Blo 1024605 1299073 := bbase (se 2 (by rfl) ⟨487152, by rfl⟩ : syracuseStep 1299073 = 974305) (by norm_num)
theorem B1299169 : Blo 1024605 1299169 := bbase (se 2 (by rfl) ⟨487188, by rfl⟩ : syracuseStep 1299169 = 974377) (by norm_num)
theorem B5559029 : Blo 1024605 5559029 := bbase (se 5 (by rfl) ⟨260579, by rfl⟩ : syracuseStep 5559029 = 521159) (by norm_num)
theorem B1463069 : Blo 1024605 1463069 := bbase (se 3 (by rfl) ⟨274325, by rfl⟩ : syracuseStep 1463069 = 548651) (by norm_num)
theorem B1757981 : Blo 1024605 1757981 := bbase (se 3 (by rfl) ⟨329621, by rfl⟩ : syracuseStep 1757981 = 659243) (by norm_num)
theorem B1299341 : Blo 1024605 1299341 := bbase (se 3 (by rfl) ⟨243626, by rfl⟩ : syracuseStep 1299341 = 487253) (by norm_num)
theorem B5198741 : Blo 1024605 5198741 := bbase (se 6 (by rfl) ⟨121845, by rfl⟩ : syracuseStep 5198741 = 243691) (by norm_num)
theorem B1299397 : Blo 1024605 1299397 := bbase (se 4 (by rfl) ⟨121818, by rfl⟩ : syracuseStep 1299397 = 243637) (by norm_num)
theorem B3462101 : Blo 1024605 3462101 := bbase (se 7 (by rfl) ⟨40571, by rfl⟩ : syracuseStep 3462101 = 81143) (by norm_num)
theorem B1299493 : Blo 1024605 1299493 := bbase (se 4 (by rfl) ⟨121827, by rfl⟩ : syracuseStep 1299493 = 243655) (by norm_num)
theorem B21353557 : Blo 1024605 21353557 := bbase (se 8 (by rfl) ⟨125118, by rfl⟩ : syracuseStep 21353557 = 250237) (by norm_num)
theorem B1234013 : Blo 1024605 1234013 := bbase (se 3 (by rfl) ⟨231377, by rfl⟩ : syracuseStep 1234013 = 462755) (by norm_num)
theorem B1234109 : Blo 1024605 1234109 := bbase (se 3 (by rfl) ⟨231395, by rfl⟩ : syracuseStep 1234109 = 462791) (by norm_num)
theorem B1299665 : Blo 1024605 1299665 := bbase (se 2 (by rfl) ⟨487374, by rfl⟩ : syracuseStep 1299665 = 974749) (by norm_num)
theorem B1234129 : Blo 1024605 1234129 := bbase (se 2 (by rfl) ⟨462798, by rfl⟩ : syracuseStep 1234129 = 925597) (by norm_num)
theorem B1299721 : Blo 1024605 1299721 := bbase (se 2 (by rfl) ⟨487395, by rfl⟩ : syracuseStep 1299721 = 974791) (by norm_num)
theorem B1234273 : Blo 1024605 1234273 := bbase (se 2 (by rfl) ⟨462852, by rfl⟩ : syracuseStep 1234273 = 925705) (by norm_num)
theorem B1299817 : Blo 1024605 1299817 := bbase (se 2 (by rfl) ⟨487431, by rfl⟩ : syracuseStep 1299817 = 974863) (by norm_num)
theorem B3462533 : Blo 1024605 3462533 := bbase (se 4 (by rfl) ⟨324612, by rfl⟩ : syracuseStep 3462533 = 649225) (by norm_num)
theorem B1168777 : Blo 1024605 1168777 := bbase (se 2 (by rfl) ⟨438291, by rfl⟩ : syracuseStep 1168777 = 876583) (by norm_num)
theorem B1168849 : Blo 1024605 1168849 := bbase (se 2 (by rfl) ⟨438318, by rfl⟩ : syracuseStep 1168849 = 876637) (by norm_num)
theorem B6247925 : Blo 1024605 6247925 := bbase (se 5 (by rfl) ⟨292871, by rfl⟩ : syracuseStep 6247925 = 585743) (by norm_num)
theorem B1299989 : Blo 1024605 1299989 := bbase (se 6 (by rfl) ⟨30468, by rfl⟩ : syracuseStep 1299989 = 60937) (by norm_num)
theorem B2250317 : Blo 1024605 2250317 := bbase (se 3 (by rfl) ⟨421934, by rfl⟩ : syracuseStep 2250317 = 843869) (by norm_num)
theorem B1300045 : Blo 1024605 1300045 := bbase (se 3 (by rfl) ⟨243758, by rfl⟩ : syracuseStep 1300045 = 487517) (by norm_num)
theorem B4806245 : Blo 1024605 4806245 := bbase (se 4 (by rfl) ⟨450585, by rfl⟩ : syracuseStep 4806245 = 901171) (by norm_num)
theorem B1169005 : Blo 1024605 1169005 := bbase (se 3 (by rfl) ⟨219188, by rfl⟩ : syracuseStep 1169005 = 438377) (by norm_num)
theorem B7788149 : Blo 1024605 7788149 := bbase (se 5 (by rfl) ⟨365069, by rfl⟩ : syracuseStep 7788149 = 730139) (by norm_num)
theorem B1300141 : Blo 1024605 1300141 := bbase (se 3 (by rfl) ⟨243776, by rfl⟩ : syracuseStep 1300141 = 487553) (by norm_num)
theorem B1562309 : Blo 1024605 1562309 := bbase (se 4 (by rfl) ⟨146466, by rfl⟩ : syracuseStep 1562309 = 292933) (by norm_num)
theorem B3462965 : Blo 1024605 3462965 := bbase (se 5 (by rfl) ⟨162326, by rfl⟩ : syracuseStep 3462965 = 324653) (by norm_num)
theorem B1300313 : Blo 1024605 1300313 := bbase (se 2 (by rfl) ⟨487617, by rfl⟩ : syracuseStep 1300313 = 975235) (by norm_num)
theorem B1300369 : Blo 1024605 1300369 := bbase (se 2 (by rfl) ⟨487638, by rfl⟩ : syracuseStep 1300369 = 975277) (by norm_num)
theorem B1300465 : Blo 1024605 1300465 := bbase (se 2 (by rfl) ⟨487674, by rfl⟩ : syracuseStep 1300465 = 975349) (by norm_num)
theorem B1300637 : Blo 1024605 1300637 := bbase (se 3 (by rfl) ⟨243869, by rfl⟩ : syracuseStep 1300637 = 487739) (by norm_num)
theorem B5200037 : Blo 1024605 5200037 := bbase (se 4 (by rfl) ⟨487503, by rfl⟩ : syracuseStep 5200037 = 975007) (by norm_num)
theorem B1464493 : Blo 1024605 1464493 := bbase (se 3 (by rfl) ⟨274592, by rfl⟩ : syracuseStep 1464493 = 549185) (by norm_num)
theorem B1300693 : Blo 1024605 1300693 := bbase (se 7 (by rfl) ⟨15242, by rfl⟩ : syracuseStep 1300693 = 30485) (by norm_num)
theorem B3463397 : Blo 1024605 3463397 := bbase (se 4 (by rfl) ⟨324693, by rfl⟩ : syracuseStep 3463397 = 649387) (by norm_num)
theorem B1300789 : Blo 1024605 1300789 := bbase (se 5 (by rfl) ⟨60974, by rfl⟩ : syracuseStep 1300789 = 121949) (by norm_num)
theorem B1300961 : Blo 1024605 1300961 := bbase (se 2 (by rfl) ⟨487860, by rfl⟩ : syracuseStep 1300961 = 975721) (by norm_num)
theorem B1301017 : Blo 1024605 1301017 := bbase (se 2 (by rfl) ⟨487881, by rfl⟩ : syracuseStep 1301017 = 975763) (by norm_num)
theorem B1301113 : Blo 1024605 1301113 := bbase (se 2 (by rfl) ⟨487917, by rfl⟩ : syracuseStep 1301113 = 975835) (by norm_num)
theorem B3463829 : Blo 1024605 3463829 := bbase (se 6 (by rfl) ⟨81183, by rfl⟩ : syracuseStep 3463829 = 162367) (by norm_num)
theorem B1039009 : Blo 1024605 1039009 := bbase (se 2 (by rfl) ⟨389628, by rfl⟩ : syracuseStep 1039009 = 779257) (by norm_num)
theorem B2218661 : Blo 1024605 2218661 := bbase (se 4 (by rfl) ⟨207999, by rfl⟩ : syracuseStep 2218661 = 415999) (by norm_num)
theorem B4381381 : Blo 1024605 4381381 := bbase (se 4 (by rfl) ⟨410754, by rfl⟩ : syracuseStep 4381381 = 821509) (by norm_num)
theorem B1170181 : Blo 1024605 1170181 := bbase (se 4 (by rfl) ⟨109704, by rfl⟩ : syracuseStep 1170181 = 219409) (by norm_num)
theorem B1301285 : Blo 1024605 1301285 := bbase (se 4 (by rfl) ⟨121995, by rfl⟩ : syracuseStep 1301285 = 243991) (by norm_num)
theorem B1170245 : Blo 1024605 1170245 := bbase (se 4 (by rfl) ⟨109710, by rfl⟩ : syracuseStep 1170245 = 219421) (by norm_num)
theorem B1301341 : Blo 1024605 1301341 := bbase (se 3 (by rfl) ⟨244001, by rfl⟩ : syracuseStep 1301341 = 488003) (by norm_num)
theorem B1301437 : Blo 1024605 1301437 := bbase (se 3 (by rfl) ⟨244019, by rfl⟩ : syracuseStep 1301437 = 488039) (by norm_num)
theorem B4938725 : Blo 1024605 4938725 := bbase (se 4 (by rfl) ⟨463005, by rfl⟩ : syracuseStep 4938725 = 926011) (by norm_num)
theorem B3464261 : Blo 1024605 3464261 := bbase (se 4 (by rfl) ⟨324774, by rfl⟩ : syracuseStep 3464261 = 649549) (by norm_num)
theorem B1301609 : Blo 1024605 1301609 := bbase (se 2 (by rfl) ⟨488103, by rfl⟩ : syracuseStep 1301609 = 976207) (by norm_num)
theorem B6577301 : Blo 1024605 6577301 := bbase (se 6 (by rfl) ⟨154155, by rfl⟩ : syracuseStep 6577301 = 308311) (by norm_num)
theorem B1301665 : Blo 1024605 1301665 := bbase (se 2 (by rfl) ⟨488124, by rfl⟩ : syracuseStep 1301665 = 976249) (by norm_num)
theorem B4447429 : Blo 1024605 4447429 := bbase (se 4 (by rfl) ⟨416946, by rfl⟩ : syracuseStep 4447429 = 833893) (by norm_num)
theorem B4676837 : Blo 1024605 4676837 := bbase (se 4 (by rfl) ⟨438453, by rfl⟩ : syracuseStep 4676837 = 876907) (by norm_num)
theorem B1301761 : Blo 1024605 1301761 := bbase (se 2 (by rfl) ⟨488160, by rfl⟩ : syracuseStep 1301761 = 976321) (by norm_num)
theorem B5201333 : Blo 1024605 5201333 := bbase (se 5 (by rfl) ⟨243812, by rfl⟩ : syracuseStep 5201333 = 487625) (by norm_num)
theorem B1170925 : Blo 1024605 1170925 := bbase (se 3 (by rfl) ⟨219548, by rfl⟩ : syracuseStep 1170925 = 439097) (by norm_num)
theorem B3464693 : Blo 1024605 3464693 := bbase (se 5 (by rfl) ⟨162407, by rfl⟩ : syracuseStep 3464693 = 324815) (by norm_num)
theorem B1040209 : Blo 1024605 1040209 := bbase (se 2 (by rfl) ⟨390078, by rfl⟩ : syracuseStep 1040209 = 780157) (by norm_num)
theorem B1335145 : Blo 1024605 1335145 := bbase (se 2 (by rfl) ⟨500679, by rfl⟩ : syracuseStep 1335145 = 1001359) (by norm_num)
theorem B3465125 : Blo 1024605 3465125 := bbase (se 4 (by rfl) ⟨324855, by rfl⟩ : syracuseStep 3465125 = 649711) (by norm_num)
theorem B3694517 : Blo 1024605 3694517 := bbase (se 5 (by rfl) ⟨173180, by rfl⟩ : syracuseStep 3694517 = 346361) (by norm_num)
theorem B1171513 : Blo 1024605 1171513 := bbase (se 2 (by rfl) ⟨439317, by rfl⟩ : syracuseStep 1171513 = 878635) (by norm_num)
theorem B1040501 : Blo 1024605 1040501 := bbase (se 5 (by rfl) ⟨48773, by rfl⟩ : syracuseStep 1040501 = 97547) (by norm_num)
theorem B4382869 : Blo 1024605 4382869 := bbase (se 6 (by rfl) ⟨102723, by rfl⟩ : syracuseStep 4382869 = 205447) (by norm_num)
theorem B4382885 : Blo 1024605 4382885 := bbase (se 4 (by rfl) ⟨410895, by rfl⟩ : syracuseStep 4382885 = 821791) (by norm_num)
theorem B4939973 : Blo 1024605 4939973 := bbase (se 4 (by rfl) ⟨463122, by rfl⟩ : syracuseStep 4939973 = 926245) (by norm_num)
theorem B3891509 : Blo 1024605 3891509 := bbase (se 5 (by rfl) ⟨182414, by rfl⟩ : syracuseStep 3891509 = 364829) (by norm_num)
theorem B18702677 : Blo 1024605 18702677 := bbase (se 10 (by rfl) ⟨27396, by rfl⟩ : syracuseStep 18702677 = 54793) (by norm_num)
theorem B1040725 : Blo 1024605 1040725 := bbase (se 10 (by rfl) ⟨1524, by rfl⟩ : syracuseStep 1040725 = 3049) (by norm_num)
theorem B3465557 : Blo 1024605 3465557 := bbase (se 10 (by rfl) ⟨5076, by rfl⟩ : syracuseStep 3465557 = 10153) (by norm_num)
theorem B1040737 : Blo 1024605 1040737 := bbase (se 2 (by rfl) ⟨390276, by rfl⟩ : syracuseStep 1040737 = 780553) (by norm_num)
theorem B1729093 : Blo 1024605 1729093 := bbase (se 4 (by rfl) ⟨162102, by rfl⟩ : syracuseStep 1729093 = 324205) (by norm_num)
theorem B3891797 : Blo 1024605 3891797 := bbase (se 8 (by rfl) ⟨22803, by rfl⟩ : syracuseStep 3891797 = 45607) (by norm_num)
theorem B1729181 : Blo 1024605 1729181 := bbase (se 3 (by rfl) ⟨324221, by rfl⟩ : syracuseStep 1729181 = 648443) (by norm_num)
theorem B5202629 : Blo 1024605 5202629 := bbase (se 4 (by rfl) ⟨487746, by rfl⟩ : syracuseStep 5202629 = 975493) (by norm_num)
theorem B3465989 : Blo 1024605 3465989 := bbase (se 4 (by rfl) ⟨324936, by rfl⟩ : syracuseStep 3465989 = 649873) (by norm_num)
theorem B1729309 : Blo 1024605 1729309 := bbase (se 3 (by rfl) ⟨324245, by rfl⟩ : syracuseStep 1729309 = 648491) (by norm_num)
theorem B1729397 : Blo 1024605 1729397 := bbase (se 5 (by rfl) ⟨81065, by rfl⟩ : syracuseStep 1729397 = 162131) (by norm_num)
theorem B1041341 : Blo 1024605 1041341 := bbase (se 3 (by rfl) ⟨195251, by rfl⟩ : syracuseStep 1041341 = 390503) (by norm_num)
theorem B1729525 : Blo 1024605 1729525 := bbase (se 5 (by rfl) ⟨81071, by rfl⟩ : syracuseStep 1729525 = 162143) (by norm_num)
theorem B2221085 : Blo 1024605 2221085 := bbase (se 3 (by rfl) ⟨416453, by rfl⟩ : syracuseStep 2221085 = 832907) (by norm_num)
theorem B2188333 : Blo 1024605 2188333 := bbase (se 3 (by rfl) ⟨410312, by rfl⟩ : syracuseStep 2188333 = 820625) (by norm_num)
theorem B1729613 : Blo 1024605 1729613 := bbase (se 3 (by rfl) ⟨324302, by rfl⟩ : syracuseStep 1729613 = 648605) (by norm_num)
theorem B7398485 : Blo 1024605 7398485 := bbase (se 8 (by rfl) ⟨43350, by rfl⟩ : syracuseStep 7398485 = 86701) (by norm_num)
theorem B2188453 : Blo 1024605 2188453 := bbase (se 4 (by rfl) ⟨205167, by rfl⟩ : syracuseStep 2188453 = 410335) (by norm_num)
theorem B3466421 : Blo 1024605 3466421 := bbase (se 5 (by rfl) ⟨162488, by rfl⟩ : syracuseStep 3466421 = 324977) (by norm_num)
theorem B1729741 : Blo 1024605 1729741 := bbase (se 3 (by rfl) ⟨324326, by rfl⟩ : syracuseStep 1729741 = 648653) (by norm_num)
theorem B1041653 : Blo 1024605 1041653 := bbase (se 5 (by rfl) ⟨48827, by rfl⟩ : syracuseStep 1041653 = 97655) (by norm_num)
theorem B14771477 : Blo 1024605 14771477 := bbase (se 6 (by rfl) ⟨346206, by rfl⟩ : syracuseStep 14771477 = 692413) (by norm_num)
theorem B1729829 : Blo 1024605 1729829 := bbase (se 4 (by rfl) ⟨162171, by rfl⟩ : syracuseStep 1729829 = 324343) (by norm_num)
theorem B4679045 : Blo 1024605 4679045 := bbase (se 4 (by rfl) ⟨438660, by rfl⟩ : syracuseStep 4679045 = 877321) (by norm_num)
theorem B2188709 : Blo 1024605 2188709 := bbase (se 4 (by rfl) ⟨205191, by rfl⟩ : syracuseStep 2188709 = 410383) (by norm_num)
theorem B1729957 : Blo 1024605 1729957 := bbase (se 4 (by rfl) ⟨162183, by rfl⟩ : syracuseStep 1729957 = 324367) (by norm_num)
theorem B1730045 : Blo 1024605 1730045 := bbase (se 3 (by rfl) ⟨324383, by rfl⟩ : syracuseStep 1730045 = 648767) (by norm_num)
theorem B4154933 : Blo 1024605 4154933 := bbase (se 5 (by rfl) ⟨194762, by rfl⟩ : syracuseStep 4154933 = 389525) (by norm_num)
theorem B3466853 : Blo 1024605 3466853 := bbase (se 4 (by rfl) ⟨325017, by rfl⟩ : syracuseStep 3466853 = 650035) (by norm_num)
theorem B1730173 : Blo 1024605 1730173 := bbase (se 3 (by rfl) ⟨324407, by rfl⟩ : syracuseStep 1730173 = 648815) (by norm_num)
theorem B1730261 : Blo 1024605 1730261 := bbase (se 7 (by rfl) ⟨20276, by rfl⟩ : syracuseStep 1730261 = 40553) (by norm_num)
theorem B14804693 : Blo 1024605 14804693 := bbase (se 7 (by rfl) ⟨173492, by rfl⟩ : syracuseStep 14804693 = 346985) (by norm_num)
theorem B3892981 : Blo 1024605 3892981 := bbase (se 5 (by rfl) ⟨182483, by rfl⟩ : syracuseStep 3892981 = 364967) (by norm_num)
theorem B1730389 : Blo 1024605 1730389 := bbase (se 9 (by rfl) ⟨5069, by rfl⟩ : syracuseStep 1730389 = 10139) (by norm_num)
theorem B1730477 : Blo 1024605 1730477 := bbase (se 3 (by rfl) ⟨324464, by rfl⟩ : syracuseStep 1730477 = 648929) (by norm_num)
theorem B5203925 : Blo 1024605 5203925 := bbase (se 7 (by rfl) ⟨60983, by rfl⟩ : syracuseStep 5203925 = 121967) (by norm_num)
theorem B3467285 : Blo 1024605 3467285 := bbase (se 6 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 3467285 = 162529) (by norm_num)
theorem B3893285 : Blo 1024605 3893285 := bbase (se 4 (by rfl) ⟨364995, by rfl⟩ : syracuseStep 3893285 = 729991) (by norm_num)
theorem B1730605 : Blo 1024605 1730605 := bbase (se 3 (by rfl) ⟨324488, by rfl⟩ : syracuseStep 1730605 = 648977) (by norm_num)
theorem B1730693 : Blo 1024605 1730693 := bbase (se 4 (by rfl) ⟨162252, by rfl⟩ : syracuseStep 1730693 = 324505) (by norm_num)
theorem B1927325 : Blo 1024605 1927325 := bbase (se 3 (by rfl) ⟨361373, by rfl⟩ : syracuseStep 1927325 = 722747) (by norm_num)
theorem B1730821 : Blo 1024605 1730821 := bbase (se 4 (by rfl) ⟨162264, by rfl⟩ : syracuseStep 1730821 = 324529) (by norm_num)
theorem B1665293 : Blo 1024605 1665293 := bbase (se 3 (by rfl) ⟨312242, by rfl⟩ : syracuseStep 1665293 = 624485) (by norm_num)
theorem B2189597 : Blo 1024605 2189597 := bbase (se 3 (by rfl) ⟨410549, by rfl⟩ : syracuseStep 2189597 = 821099) (by norm_num)
theorem B3696965 : Blo 1024605 3696965 := bbase (se 4 (by rfl) ⟨346590, by rfl⟩ : syracuseStep 3696965 = 693181) (by norm_num)
theorem B1730909 : Blo 1024605 1730909 := bbase (se 3 (by rfl) ⟨324545, by rfl⟩ : syracuseStep 1730909 = 649091) (by norm_num)
theorem B4385141 : Blo 1024605 4385141 := bbase (se 5 (by rfl) ⟨205553, by rfl⟩ : syracuseStep 4385141 = 411107) (by norm_num)
theorem B3467717 : Blo 1024605 3467717 := bbase (se 4 (by rfl) ⟨325098, by rfl⟩ : syracuseStep 3467717 = 650197) (by norm_num)
theorem B1731037 : Blo 1024605 1731037 := bbase (se 3 (by rfl) ⟨324569, by rfl⟩ : syracuseStep 1731037 = 649139) (by norm_num)
theorem B2189837 : Blo 1024605 2189837 := bbase (se 3 (by rfl) ⟨410594, by rfl⟩ : syracuseStep 2189837 = 821189) (by norm_num)
theorem B17132053 : Blo 1024605 17132053 := bbase (se 6 (by rfl) ⟨401532, by rfl⟩ : syracuseStep 17132053 = 803065) (by norm_num)
theorem B1731125 : Blo 1024605 1731125 := bbase (se 5 (by rfl) ⟨81146, by rfl⟩ : syracuseStep 1731125 = 162293) (by norm_num)
theorem B1731253 : Blo 1024605 1731253 := bbase (se 5 (by rfl) ⟨81152, by rfl⟩ : syracuseStep 1731253 = 162305) (by norm_num)
theorem B6253301 : Blo 1024605 6253301 := bbase (se 5 (by rfl) ⟨293123, by rfl⟩ : syracuseStep 6253301 = 586247) (by norm_num)
theorem B1731341 : Blo 1024605 1731341 := bbase (se 3 (by rfl) ⟨324626, by rfl⟩ : syracuseStep 1731341 = 649253) (by norm_num)
theorem B3468149 : Blo 1024605 3468149 := bbase (se 5 (by rfl) ⟨162569, by rfl⟩ : syracuseStep 3468149 = 325139) (by norm_num)
theorem B1731469 : Blo 1024605 1731469 := bbase (se 3 (by rfl) ⟨324650, by rfl⟩ : syracuseStep 1731469 = 649301) (by norm_num)
theorem B4942741 : Blo 1024605 4942741 := bbase (se 6 (by rfl) ⟨115845, by rfl⟩ : syracuseStep 4942741 = 231691) (by norm_num)
theorem B1731557 : Blo 1024605 1731557 := bbase (se 4 (by rfl) ⟨162333, by rfl⟩ : syracuseStep 1731557 = 324667) (by norm_num)
theorem B2190341 : Blo 1024605 2190341 := bbase (se 4 (by rfl) ⟨205344, by rfl⟩ : syracuseStep 2190341 = 410689) (by norm_num)
theorem B2190349 : Blo 1024605 2190349 := bbase (se 3 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 2190349 = 821381) (by norm_num)
theorem B7400501 : Blo 1024605 7400501 := bbase (se 5 (by rfl) ⟨346898, by rfl⟩ : syracuseStep 7400501 = 693797) (by norm_num)
theorem B1731685 : Blo 1024605 1731685 := bbase (se 4 (by rfl) ⟨162345, by rfl⟩ : syracuseStep 1731685 = 324691) (by norm_num)
theorem B1731773 : Blo 1024605 1731773 := bbase (se 3 (by rfl) ⟨324707, by rfl⟩ : syracuseStep 1731773 = 649415) (by norm_num)
theorem B5205221 : Blo 1024605 5205221 := bbase (se 4 (by rfl) ⟨487989, by rfl⟩ : syracuseStep 5205221 = 975979) (by norm_num)
theorem B1666333 : Blo 1024605 1666333 := bbase (se 3 (by rfl) ⟨312437, by rfl⟩ : syracuseStep 1666333 = 624875) (by norm_num)
theorem B3468581 : Blo 1024605 3468581 := bbase (se 4 (by rfl) ⟨325179, by rfl⟩ : syracuseStep 3468581 = 650359) (by norm_num)
theorem B1731901 : Blo 1024605 1731901 := bbase (se 3 (by rfl) ⟨324731, by rfl⟩ : syracuseStep 1731901 = 649463) (by norm_num)
theorem B1731989 : Blo 1024605 1731989 := bbase (se 6 (by rfl) ⟨40593, by rfl⟩ : syracuseStep 1731989 = 81187) (by norm_num)
theorem B1732117 : Blo 1024605 1732117 := bbase (se 6 (by rfl) ⟨40596, by rfl⟩ : syracuseStep 1732117 = 81193) (by norm_num)
theorem B1732205 : Blo 1024605 1732205 := bbase (se 3 (by rfl) ⟨324788, by rfl⟩ : syracuseStep 1732205 = 649577) (by norm_num)
theorem B1044149 : Blo 1024605 1044149 := bbase (se 5 (by rfl) ⟨48944, by rfl⟩ : syracuseStep 1044149 = 97889) (by norm_num)
theorem B3469013 : Blo 1024605 3469013 := bbase (se 7 (by rfl) ⟨40652, by rfl⟩ : syracuseStep 3469013 = 81305) (by norm_num)
theorem B1732333 : Blo 1024605 1732333 := bbase (se 3 (by rfl) ⟨324812, by rfl⟩ : syracuseStep 1732333 = 649625) (by norm_num)
theorem B9367285 : Blo 1024605 9367285 := bbase (se 5 (by rfl) ⟨439091, by rfl⟩ : syracuseStep 9367285 = 878183) (by norm_num)
theorem B5271317 : Blo 1024605 5271317 := bbase (se 6 (by rfl) ⟨123546, by rfl⟩ : syracuseStep 5271317 = 247093) (by norm_num)
theorem B1732421 : Blo 1024605 1732421 := bbase (se 4 (by rfl) ⟨162414, by rfl⟩ : syracuseStep 1732421 = 324829) (by norm_num)
theorem B1732549 : Blo 1024605 1732549 := bbase (se 4 (by rfl) ⟨162426, by rfl⟩ : syracuseStep 1732549 = 324853) (by norm_num)
theorem B1732637 : Blo 1024605 1732637 := bbase (se 3 (by rfl) ⟨324869, by rfl⟩ : syracuseStep 1732637 = 649739) (by norm_num)
theorem B3895397 : Blo 1024605 3895397 := bbase (se 4 (by rfl) ⟨365193, by rfl⟩ : syracuseStep 3895397 = 730387) (by norm_num)
theorem B2191477 : Blo 1024605 2191477 := bbase (se 5 (by rfl) ⟨102725, by rfl⟩ : syracuseStep 2191477 = 205451) (by norm_num)
theorem B3469445 : Blo 1024605 3469445 := bbase (se 4 (by rfl) ⟨325260, by rfl⟩ : syracuseStep 3469445 = 650521) (by norm_num)
theorem B1732765 : Blo 1024605 1732765 := bbase (se 3 (by rfl) ⟨324893, by rfl⟩ : syracuseStep 1732765 = 649787) (by norm_num)
theorem B1143001 : Blo 1024605 1143001 := bbase (se 2 (by rfl) ⟨428625, by rfl⟩ : syracuseStep 1143001 = 857251) (by norm_num)
theorem B1732853 : Blo 1024605 1732853 := bbase (se 5 (by rfl) ⟨81227, by rfl⟩ : syracuseStep 1732853 = 162455) (by norm_num)
theorem B1732981 : Blo 1024605 1732981 := bbase (se 5 (by rfl) ⟨81233, by rfl⟩ : syracuseStep 1732981 = 162467) (by norm_num)
theorem B3895685 : Blo 1024605 3895685 := bbase (se 4 (by rfl) ⟨365220, by rfl⟩ : syracuseStep 3895685 = 730441) (by norm_num)
theorem B1733069 : Blo 1024605 1733069 := bbase (se 3 (by rfl) ⟨324950, by rfl⟩ : syracuseStep 1733069 = 649901) (by norm_num)
theorem B2191853 : Blo 1024605 2191853 := bbase (se 3 (by rfl) ⟨410972, by rfl⟩ : syracuseStep 2191853 = 821945) (by norm_num)
theorem B5206517 : Blo 1024605 5206517 := bbase (se 5 (by rfl) ⟨244055, by rfl⟩ : syracuseStep 5206517 = 488111) (by norm_num)
theorem B3469877 : Blo 1024605 3469877 := bbase (se 5 (by rfl) ⟨162650, by rfl⟩ : syracuseStep 3469877 = 325301) (by norm_num)
theorem B1733197 : Blo 1024605 1733197 := bbase (se 3 (by rfl) ⟨324974, by rfl⟩ : syracuseStep 1733197 = 649949) (by norm_num)
theorem B1733285 : Blo 1024605 1733285 := bbase (se 4 (by rfl) ⟨162495, by rfl⟩ : syracuseStep 1733285 = 324991) (by norm_num)
theorem B7500533 : Blo 1024605 7500533 := bbase (se 5 (by rfl) ⟨351587, by rfl⟩ : syracuseStep 7500533 = 703175) (by norm_num)
theorem B1733413 : Blo 1024605 1733413 := bbase (se 4 (by rfl) ⟨162507, by rfl⟩ : syracuseStep 1733413 = 325015) (by norm_num)
theorem B1733501 : Blo 1024605 1733501 := bbase (se 3 (by rfl) ⟨325031, by rfl⟩ : syracuseStep 1733501 = 650063) (by norm_num)
theorem B1536917 : Blo 1024605 1536917 := bbase (se 6 (by rfl) ⟨36021, by rfl⟩ : syracuseStep 1536917 = 72043) (by norm_num)
theorem B1930133 : Blo 1024605 1930133 := bbase (se 6 (by rfl) ⟨45237, by rfl⟩ : syracuseStep 1930133 = 90475) (by norm_num)
theorem B1536941 : Blo 1024605 1536941 := bbase (se 3 (by rfl) ⟨288176, by rfl⟩ : syracuseStep 1536941 = 576353) (by norm_num)
theorem B1536965 : Blo 1024605 1536965 := bbase (se 4 (by rfl) ⟨144090, by rfl⟩ : syracuseStep 1536965 = 288181) (by norm_num)
theorem B1536989 : Blo 1024605 1536989 := bbase (se 3 (by rfl) ⟨288185, by rfl⟩ : syracuseStep 1536989 = 576371) (by norm_num)
theorem B3470309 : Blo 1024605 3470309 := bbase (se 4 (by rfl) ⟨325341, by rfl⟩ : syracuseStep 3470309 = 650683) (by norm_num)
theorem B1537013 : Blo 1024605 1537013 := bbase (se 5 (by rfl) ⟨72047, by rfl⟩ : syracuseStep 1537013 = 144095) (by norm_num)
theorem B1733629 : Blo 1024605 1733629 := bbase (se 3 (by rfl) ⟨325055, by rfl⟩ : syracuseStep 1733629 = 650111) (by norm_num)
theorem B1537037 : Blo 1024605 1537037 := bbase (se 3 (by rfl) ⟨288194, by rfl⟩ : syracuseStep 1537037 = 576389) (by norm_num)
theorem B1537061 : Blo 1024605 1537061 := bbase (se 4 (by rfl) ⟨144099, by rfl⟩ : syracuseStep 1537061 = 288199) (by norm_num)
theorem B6583349 : Blo 1024605 6583349 := bbase (se 5 (by rfl) ⟨308594, by rfl⟩ : syracuseStep 6583349 = 617189) (by norm_num)
theorem B1537085 : Blo 1024605 1537085 := bbase (se 3 (by rfl) ⟨288203, by rfl⟩ : syracuseStep 1537085 = 576407) (by norm_num)
theorem B1537109 : Blo 1024605 1537109 := bbase (se 8 (by rfl) ⟨9006, by rfl⟩ : syracuseStep 1537109 = 18013) (by norm_num)
theorem B1733717 : Blo 1024605 1733717 := bbase (se 8 (by rfl) ⟨10158, by rfl⟩ : syracuseStep 1733717 = 20317) (by norm_num)
theorem B1537133 : Blo 1024605 1537133 := bbase (se 3 (by rfl) ⟨288212, by rfl⟩ : syracuseStep 1537133 = 576425) (by norm_num)
theorem B1537157 : Blo 1024605 1537157 := bbase (se 4 (by rfl) ⟨144108, by rfl⟩ : syracuseStep 1537157 = 288217) (by norm_num)
theorem B1537181 : Blo 1024605 1537181 := bbase (se 3 (by rfl) ⟨288221, by rfl⟩ : syracuseStep 1537181 = 576443) (by norm_num)
theorem B1537205 : Blo 1024605 1537205 := bbase (se 5 (by rfl) ⟨72056, by rfl⟩ : syracuseStep 1537205 = 144113) (by norm_num)
theorem B1537229 : Blo 1024605 1537229 := bbase (se 3 (by rfl) ⟨288230, by rfl⟩ : syracuseStep 1537229 = 576461) (by norm_num)
theorem B7795925 : Blo 1024605 7795925 := bbase (se 7 (by rfl) ⟨91358, by rfl⟩ : syracuseStep 7795925 = 182717) (by norm_num)
theorem B1733845 : Blo 1024605 1733845 := bbase (se 7 (by rfl) ⟨20318, by rfl⟩ : syracuseStep 1733845 = 40637) (by norm_num)
theorem B1537253 : Blo 1024605 1537253 := bbase (se 4 (by rfl) ⟨144117, by rfl⟩ : syracuseStep 1537253 = 288235) (by norm_num)
theorem B1537277 : Blo 1024605 1537277 := bbase (se 3 (by rfl) ⟨288239, by rfl⟩ : syracuseStep 1537277 = 576479) (by norm_num)
theorem B1537301 : Blo 1024605 1537301 := bbase (se 6 (by rfl) ⟨36030, by rfl⟩ : syracuseStep 1537301 = 72061) (by norm_num)
theorem B13137173 : Blo 1024605 13137173 := bbase (se 6 (by rfl) ⟨307902, by rfl⟩ : syracuseStep 13137173 = 615805) (by norm_num)
theorem B1537325 : Blo 1024605 1537325 := bbase (se 3 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 1537325 = 576497) (by norm_num)
theorem B1733933 : Blo 1024605 1733933 := bbase (se 3 (by rfl) ⟨325112, by rfl⟩ : syracuseStep 1733933 = 650225) (by norm_num)
theorem B1537349 : Blo 1024605 1537349 := bbase (se 4 (by rfl) ⟨144126, by rfl⟩ : syracuseStep 1537349 = 288253) (by norm_num)
theorem B1537373 : Blo 1024605 1537373 := bbase (se 3 (by rfl) ⟨288257, by rfl⟩ : syracuseStep 1537373 = 576515) (by norm_num)
theorem B1537397 : Blo 1024605 1537397 := bbase (se 5 (by rfl) ⟨72065, by rfl⟩ : syracuseStep 1537397 = 144131) (by norm_num)
theorem B1537421 : Blo 1024605 1537421 := bbase (se 3 (by rfl) ⟨288266, by rfl⟩ : syracuseStep 1537421 = 576533) (by norm_num)
theorem B3470741 : Blo 1024605 3470741 := bbase (se 6 (by rfl) ⟨81345, by rfl⟩ : syracuseStep 3470741 = 162691) (by norm_num)
theorem B1537445 : Blo 1024605 1537445 := bbase (se 4 (by rfl) ⟨144135, by rfl⟩ : syracuseStep 1537445 = 288271) (by norm_num)
theorem B1734061 : Blo 1024605 1734061 := bbase (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) (by norm_num)
theorem B1537469 : Blo 1024605 1537469 := bbase (se 3 (by rfl) ⟨288275, by rfl⟩ : syracuseStep 1537469 = 576551) (by norm_num)
theorem B1537493 : Blo 1024605 1537493 := bbase (se 7 (by rfl) ⟨18017, by rfl⟩ : syracuseStep 1537493 = 36035) (by norm_num)
theorem B1537517 : Blo 1024605 1537517 := bbase (se 3 (by rfl) ⟨288284, by rfl⟩ : syracuseStep 1537517 = 576569) (by norm_num)
theorem B1537541 : Blo 1024605 1537541 := bbase (se 4 (by rfl) ⟨144144, by rfl⟩ : syracuseStep 1537541 = 288289) (by norm_num)
theorem B1734149 : Blo 1024605 1734149 := bbase (se 4 (by rfl) ⟨162576, by rfl⟩ : syracuseStep 1734149 = 325153) (by norm_num)
theorem B1537565 : Blo 1024605 1537565 := bbase (se 3 (by rfl) ⟨288293, by rfl⟩ : syracuseStep 1537565 = 576587) (by norm_num)
theorem B3896869 : Blo 1024605 3896869 := bbase (se 4 (by rfl) ⟨365331, by rfl⟩ : syracuseStep 3896869 = 730663) (by norm_num)
theorem B1537589 : Blo 1024605 1537589 := bbase (se 5 (by rfl) ⟨72074, by rfl⟩ : syracuseStep 1537589 = 144149) (by norm_num)
theorem B1537613 : Blo 1024605 1537613 := bbase (se 3 (by rfl) ⟨288302, by rfl⟩ : syracuseStep 1537613 = 576605) (by norm_num)
theorem B1537637 : Blo 1024605 1537637 := bbase (se 4 (by rfl) ⟨144153, by rfl⟩ : syracuseStep 1537637 = 288307) (by norm_num)
theorem B1537661 : Blo 1024605 1537661 := bbase (se 3 (by rfl) ⟨288311, by rfl⟩ : syracuseStep 1537661 = 576623) (by norm_num)
theorem B4748933 : Blo 1024605 4748933 := bbase (se 4 (by rfl) ⟨445212, by rfl⟩ : syracuseStep 4748933 = 890425) (by norm_num)
theorem B1734277 : Blo 1024605 1734277 := bbase (se 4 (by rfl) ⟨162588, by rfl⟩ : syracuseStep 1734277 = 325177) (by norm_num)
theorem B1537685 : Blo 1024605 1537685 := bbase (se 6 (by rfl) ⟨36039, by rfl⟩ : syracuseStep 1537685 = 72079) (by norm_num)
theorem B1537709 : Blo 1024605 1537709 := bbase (se 3 (by rfl) ⟨288320, by rfl⟩ : syracuseStep 1537709 = 576641) (by norm_num)
theorem B1537733 : Blo 1024605 1537733 := bbase (se 4 (by rfl) ⟨144162, by rfl⟩ : syracuseStep 1537733 = 288325) (by norm_num)
theorem B1537757 : Blo 1024605 1537757 := bbase (se 3 (by rfl) ⟨288329, by rfl⟩ : syracuseStep 1537757 = 576659) (by norm_num)
theorem B1734365 : Blo 1024605 1734365 := bbase (se 3 (by rfl) ⟨325193, by rfl⟩ : syracuseStep 1734365 = 650387) (by norm_num)
theorem B1537781 : Blo 1024605 1537781 := bbase (se 5 (by rfl) ⟨72083, by rfl⟩ : syracuseStep 1537781 = 144167) (by norm_num)
theorem B1537805 : Blo 1024605 1537805 := bbase (se 3 (by rfl) ⟨288338, by rfl⟩ : syracuseStep 1537805 = 576677) (by norm_num)
theorem B1537829 : Blo 1024605 1537829 := bbase (se 4 (by rfl) ⟨144171, by rfl⟩ : syracuseStep 1537829 = 288343) (by norm_num)
theorem B1537853 : Blo 1024605 1537853 := bbase (se 3 (by rfl) ⟨288347, by rfl⟩ : syracuseStep 1537853 = 576695) (by norm_num)
theorem B1406789 : Blo 1024605 1406789 := bbase (se 4 (by rfl) ⟨131886, by rfl⟩ : syracuseStep 1406789 = 263773) (by norm_num)
theorem B3471173 : Blo 1024605 3471173 := bbase (se 4 (by rfl) ⟨325422, by rfl⟩ : syracuseStep 3471173 = 650845) (by norm_num)
theorem B1537877 : Blo 1024605 1537877 := bbase (se 9 (by rfl) ⟨4505, by rfl⟩ : syracuseStep 1537877 = 9011) (by norm_num)
theorem B3897173 : Blo 1024605 3897173 := bbase (se 9 (by rfl) ⟨11417, by rfl⟩ : syracuseStep 3897173 = 22835) (by norm_num)
theorem B1734493 : Blo 1024605 1734493 := bbase (se 3 (by rfl) ⟨325217, by rfl⟩ : syracuseStep 1734493 = 650435) (by norm_num)
theorem B1537901 : Blo 1024605 1537901 := bbase (se 3 (by rfl) ⟨288356, by rfl⟩ : syracuseStep 1537901 = 576713) (by norm_num)
theorem B1537925 : Blo 1024605 1537925 := bbase (se 4 (by rfl) ⟨144180, by rfl⟩ : syracuseStep 1537925 = 288361) (by norm_num)
theorem B1537949 : Blo 1024605 1537949 := bbase (se 3 (by rfl) ⟨288365, by rfl⟩ : syracuseStep 1537949 = 576731) (by norm_num)
theorem B1537973 : Blo 1024605 1537973 := bbase (se 5 (by rfl) ⟨72092, by rfl⟩ : syracuseStep 1537973 = 144185) (by norm_num)
theorem B1734581 : Blo 1024605 1734581 := bbase (se 5 (by rfl) ⟨81308, by rfl⟩ : syracuseStep 1734581 = 162617) (by norm_num)
theorem B1112005 : Blo 1024605 1112005 := bbase (se 4 (by rfl) ⟨104250, by rfl⟩ : syracuseStep 1112005 = 208501) (by norm_num)
theorem B1537997 : Blo 1024605 1537997 := bbase (se 3 (by rfl) ⟨288374, by rfl⟩ : syracuseStep 1537997 = 576749) (by norm_num)
theorem B1538021 : Blo 1024605 1538021 := bbase (se 4 (by rfl) ⟨144189, by rfl⟩ : syracuseStep 1538021 = 288379) (by norm_num)
theorem B1538045 : Blo 1024605 1538045 := bbase (se 3 (by rfl) ⟨288383, by rfl⟩ : syracuseStep 1538045 = 576767) (by norm_num)
theorem B1538069 : Blo 1024605 1538069 := bbase (se 6 (by rfl) ⟨36048, by rfl⟩ : syracuseStep 1538069 = 72097) (by norm_num)
theorem B1538093 : Blo 1024605 1538093 := bbase (se 3 (by rfl) ⟨288392, by rfl⟩ : syracuseStep 1538093 = 576785) (by norm_num)
theorem B1734709 : Blo 1024605 1734709 := bbase (se 5 (by rfl) ⟨81314, by rfl⟩ : syracuseStep 1734709 = 162629) (by norm_num)
theorem B1538117 : Blo 1024605 1538117 := bbase (se 4 (by rfl) ⟨144198, by rfl⟩ : syracuseStep 1538117 = 288397) (by norm_num)
theorem B4683845 : Blo 1024605 4683845 := bbase (se 4 (by rfl) ⟨439110, by rfl⟩ : syracuseStep 4683845 = 878221) (by norm_num)
theorem B2193493 : Blo 1024605 2193493 := bbase (se 8 (by rfl) ⟨12852, by rfl⟩ : syracuseStep 2193493 = 25705) (by norm_num)
theorem B1538141 : Blo 1024605 1538141 := bbase (se 3 (by rfl) ⟨288401, by rfl⟩ : syracuseStep 1538141 = 576803) (by norm_num)
theorem B1538165 : Blo 1024605 1538165 := bbase (se 5 (by rfl) ⟨72101, by rfl⟩ : syracuseStep 1538165 = 144203) (by norm_num)
theorem B1538189 : Blo 1024605 1538189 := bbase (se 3 (by rfl) ⟨288410, by rfl⟩ : syracuseStep 1538189 = 576821) (by norm_num)
theorem B1734797 : Blo 1024605 1734797 := bbase (se 3 (by rfl) ⟨325274, by rfl⟩ : syracuseStep 1734797 = 650549) (by norm_num)
theorem B1538213 : Blo 1024605 1538213 := bbase (se 4 (by rfl) ⟨144207, by rfl⟩ : syracuseStep 1538213 = 288415) (by norm_num)
theorem B4159669 : Blo 1024605 4159669 := bbase (se 5 (by rfl) ⟨194984, by rfl⟩ : syracuseStep 4159669 = 389969) (by norm_num)
theorem B1112249 : Blo 1024605 1112249 := bbase (se 2 (by rfl) ⟨417093, by rfl⟩ : syracuseStep 1112249 = 834187) (by norm_num)
theorem B1538237 : Blo 1024605 1538237 := bbase (se 3 (by rfl) ⟨288419, by rfl⟩ : syracuseStep 1538237 = 576839) (by norm_num)
theorem B1407181 : Blo 1024605 1407181 := bbase (se 3 (by rfl) ⟨263846, by rfl⟩ : syracuseStep 1407181 = 527693) (by norm_num)
theorem B1538261 : Blo 1024605 1538261 := bbase (se 7 (by rfl) ⟨18026, by rfl⟩ : syracuseStep 1538261 = 36053) (by norm_num)
theorem B1538285 : Blo 1024605 1538285 := bbase (se 3 (by rfl) ⟨288428, by rfl⟩ : syracuseStep 1538285 = 576857) (by norm_num)
theorem B1538309 : Blo 1024605 1538309 := bbase (se 4 (by rfl) ⟨144216, by rfl⟩ : syracuseStep 1538309 = 288433) (by norm_num)
theorem B1734925 : Blo 1024605 1734925 := bbase (se 3 (by rfl) ⟨325298, by rfl⟩ : syracuseStep 1734925 = 650597) (by norm_num)
theorem B1538333 : Blo 1024605 1538333 := bbase (se 3 (by rfl) ⟨288437, by rfl⟩ : syracuseStep 1538333 = 576875) (by norm_num)
theorem B1538357 : Blo 1024605 1538357 := bbase (se 5 (by rfl) ⟨72110, by rfl⟩ : syracuseStep 1538357 = 144221) (by norm_num)
theorem B4389173 : Blo 1024605 4389173 := bbase (se 5 (by rfl) ⟨205742, by rfl⟩ : syracuseStep 4389173 = 411485) (by norm_num)
theorem B1538381 : Blo 1024605 1538381 := bbase (se 3 (by rfl) ⟨288446, by rfl⟩ : syracuseStep 1538381 = 576893) (by norm_num)
theorem B1538405 : Blo 1024605 1538405 := bbase (se 4 (by rfl) ⟨144225, by rfl⟩ : syracuseStep 1538405 = 288451) (by norm_num)
theorem B1735013 : Blo 1024605 1735013 := bbase (se 4 (by rfl) ⟨162657, by rfl⟩ : syracuseStep 1735013 = 325315) (by norm_num)
theorem B1538429 : Blo 1024605 1538429 := bbase (se 3 (by rfl) ⟨288455, by rfl⟩ : syracuseStep 1538429 = 576911) (by norm_num)
theorem B1538453 : Blo 1024605 1538453 := bbase (se 6 (by rfl) ⟨36057, by rfl⟩ : syracuseStep 1538453 = 72115) (by norm_num)
theorem B1538477 : Blo 1024605 1538477 := bbase (se 3 (by rfl) ⟨288464, by rfl⟩ : syracuseStep 1538477 = 576929) (by norm_num)
theorem B1538501 : Blo 1024605 1538501 := bbase (se 4 (by rfl) ⟨144234, by rfl⟩ : syracuseStep 1538501 = 288469) (by norm_num)
theorem B26442197 : Blo 1024605 26442197 := bbase (se 7 (by rfl) ⟨309869, by rfl⟩ : syracuseStep 26442197 = 619739) (by norm_num)
theorem B1538525 : Blo 1024605 1538525 := bbase (se 3 (by rfl) ⟨288473, by rfl⟩ : syracuseStep 1538525 = 576947) (by norm_num)
theorem B1735141 : Blo 1024605 1735141 := bbase (se 4 (by rfl) ⟨162669, by rfl⟩ : syracuseStep 1735141 = 325339) (by norm_num)
theorem B1538549 : Blo 1024605 1538549 := bbase (se 5 (by rfl) ⟨72119, by rfl⟩ : syracuseStep 1538549 = 144239) (by norm_num)
theorem B1538573 : Blo 1024605 1538573 := bbase (se 3 (by rfl) ⟨288482, by rfl⟩ : syracuseStep 1538573 = 576965) (by norm_num)
theorem B1538597 : Blo 1024605 1538597 := bbase (se 4 (by rfl) ⟨144243, by rfl⟩ : syracuseStep 1538597 = 288487) (by norm_num)
theorem B1538621 : Blo 1024605 1538621 := bbase (se 3 (by rfl) ⟨288491, by rfl⟩ : syracuseStep 1538621 = 576983) (by norm_num)
theorem B1735229 : Blo 1024605 1735229 := bbase (se 3 (by rfl) ⟨325355, by rfl⟩ : syracuseStep 1735229 = 650711) (by norm_num)
theorem B1538645 : Blo 1024605 1538645 := bbase (se 8 (by rfl) ⟨9015, by rfl⟩ : syracuseStep 1538645 = 18031) (by norm_num)
theorem B2226781 : Blo 1024605 2226781 := bbase (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) (by norm_num)
theorem B1538669 : Blo 1024605 1538669 := bbase (se 3 (by rfl) ⟨288500, by rfl⟩ : syracuseStep 1538669 = 577001) (by norm_num)
theorem B1538693 : Blo 1024605 1538693 := bbase (se 4 (by rfl) ⟨144252, by rfl⟩ : syracuseStep 1538693 = 288505) (by norm_num)
theorem B1538717 : Blo 1024605 1538717 := bbase (se 3 (by rfl) ⟨288509, by rfl⟩ : syracuseStep 1538717 = 577019) (by norm_num)
theorem B1538741 : Blo 1024605 1538741 := bbase (se 5 (by rfl) ⟨72128, by rfl⟩ : syracuseStep 1538741 = 144257) (by norm_num)
theorem B1735357 : Blo 1024605 1735357 := bbase (se 3 (by rfl) ⟨325379, by rfl⟩ : syracuseStep 1735357 = 650759) (by norm_num)
theorem B1538765 : Blo 1024605 1538765 := bbase (se 3 (by rfl) ⟨288518, by rfl⟩ : syracuseStep 1538765 = 577037) (by norm_num)
theorem B1538789 : Blo 1024605 1538789 := bbase (se 4 (by rfl) ⟨144261, by rfl⟩ : syracuseStep 1538789 = 288523) (by norm_num)
theorem B1538813 : Blo 1024605 1538813 := bbase (se 3 (by rfl) ⟨288527, by rfl⟩ : syracuseStep 1538813 = 577055) (by norm_num)
theorem B1538837 : Blo 1024605 1538837 := bbase (se 6 (by rfl) ⟨36066, by rfl⟩ : syracuseStep 1538837 = 72133) (by norm_num)
theorem B1735445 : Blo 1024605 1735445 := bbase (se 6 (by rfl) ⟨40674, by rfl⟩ : syracuseStep 1735445 = 81349) (by norm_num)
theorem B1538861 : Blo 1024605 1538861 := bbase (se 3 (by rfl) ⟨288536, by rfl⟩ : syracuseStep 1538861 = 577073) (by norm_num)
theorem B1538885 : Blo 1024605 1538885 := bbase (se 4 (by rfl) ⟨144270, by rfl⟩ : syracuseStep 1538885 = 288541) (by norm_num)
theorem B1538909 : Blo 1024605 1538909 := bbase (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) (by norm_num)
theorem B1538933 : Blo 1024605 1538933 := bbase (se 5 (by rfl) ⟨72137, by rfl⟩ : syracuseStep 1538933 = 144275) (by norm_num)
theorem B1538957 : Blo 1024605 1538957 := bbase (se 3 (by rfl) ⟨288554, by rfl⟩ : syracuseStep 1538957 = 577109) (by norm_num)
theorem B1735573 : Blo 1024605 1735573 := bbase (se 6 (by rfl) ⟨40677, by rfl⟩ : syracuseStep 1735573 = 81355) (by norm_num)
theorem B1538981 : Blo 1024605 1538981 := bbase (se 4 (by rfl) ⟨144279, by rfl⟩ : syracuseStep 1538981 = 288559) (by norm_num)
theorem B1539005 : Blo 1024605 1539005 := bbase (se 3 (by rfl) ⟨288563, by rfl⟩ : syracuseStep 1539005 = 577127) (by norm_num)
theorem B2194381 : Blo 1024605 2194381 := bbase (se 3 (by rfl) ⟨411446, by rfl⟩ : syracuseStep 2194381 = 822893) (by norm_num)
theorem B1539029 : Blo 1024605 1539029 := bbase (se 7 (by rfl) ⟨18035, by rfl⟩ : syracuseStep 1539029 = 36071) (by norm_num)
theorem B1539053 : Blo 1024605 1539053 := bbase (se 3 (by rfl) ⟨288572, by rfl⟩ : syracuseStep 1539053 = 577145) (by norm_num)
theorem B1735661 : Blo 1024605 1735661 := bbase (se 3 (by rfl) ⟨325436, by rfl⟩ : syracuseStep 1735661 = 650873) (by norm_num)
theorem B1539077 : Blo 1024605 1539077 := bbase (se 4 (by rfl) ⟨144288, by rfl⟩ : syracuseStep 1539077 = 288577) (by norm_num)
theorem B1539101 : Blo 1024605 1539101 := bbase (se 3 (by rfl) ⟨288581, by rfl⟩ : syracuseStep 1539101 = 577163) (by norm_num)
theorem B1539125 : Blo 1024605 1539125 := bbase (se 5 (by rfl) ⟨72146, by rfl⟩ : syracuseStep 1539125 = 144293) (by norm_num)
theorem B1539149 : Blo 1024605 1539149 := bbase (se 3 (by rfl) ⟨288590, by rfl⟩ : syracuseStep 1539149 = 577181) (by norm_num)
theorem B1539173 : Blo 1024605 1539173 := bbase (se 4 (by rfl) ⟨144297, by rfl⟩ : syracuseStep 1539173 = 288595) (by norm_num)
theorem B1539197 : Blo 1024605 1539197 := bbase (se 3 (by rfl) ⟨288599, by rfl⟩ : syracuseStep 1539197 = 577199) (by norm_num)
theorem B1539221 : Blo 1024605 1539221 := bbase (se 6 (by rfl) ⟨36075, by rfl⟩ : syracuseStep 1539221 = 72151) (by norm_num)
theorem B1539245 : Blo 1024605 1539245 := bbase (se 3 (by rfl) ⟨288608, by rfl⟩ : syracuseStep 1539245 = 577217) (by norm_num)
theorem B1539269 : Blo 1024605 1539269 := bbase (se 4 (by rfl) ⟨144306, by rfl⟩ : syracuseStep 1539269 = 288613) (by norm_num)
theorem B1539293 : Blo 1024605 1539293 := bbase (se 3 (by rfl) ⟨288617, by rfl⟩ : syracuseStep 1539293 = 577235) (by norm_num)
theorem B1539317 : Blo 1024605 1539317 := bbase (se 5 (by rfl) ⟨72155, by rfl⟩ : syracuseStep 1539317 = 144311) (by norm_num)
theorem B1539341 : Blo 1024605 1539341 := bbase (se 3 (by rfl) ⟨288626, by rfl⟩ : syracuseStep 1539341 = 577253) (by norm_num)
theorem B1539365 : Blo 1024605 1539365 := bbase (se 4 (by rfl) ⟨144315, by rfl⟩ : syracuseStep 1539365 = 288631) (by norm_num)
theorem B1539389 : Blo 1024605 1539389 := bbase (se 3 (by rfl) ⟨288635, by rfl⟩ : syracuseStep 1539389 = 577271) (by norm_num)
theorem B1539413 : Blo 1024605 1539413 := bbase (se 11 (by rfl) ⟨1127, by rfl⟩ : syracuseStep 1539413 = 2255) (by norm_num)
theorem B1539437 : Blo 1024605 1539437 := bbase (se 3 (by rfl) ⟨288644, by rfl⟩ : syracuseStep 1539437 = 577289) (by norm_num)
theorem B1539461 : Blo 1024605 1539461 := bbase (se 4 (by rfl) ⟨144324, by rfl⟩ : syracuseStep 1539461 = 288649) (by norm_num)
theorem B1539485 : Blo 1024605 1539485 := bbase (se 3 (by rfl) ⟨288653, by rfl⟩ : syracuseStep 1539485 = 577307) (by norm_num)
theorem B1539509 : Blo 1024605 1539509 := bbase (se 5 (by rfl) ⟨72164, by rfl⟩ : syracuseStep 1539509 = 144329) (by norm_num)
theorem B2194877 : Blo 1024605 2194877 := bbase (se 3 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 2194877 = 823079) (by norm_num)
theorem B1539533 : Blo 1024605 1539533 := bbase (se 3 (by rfl) ⟨288662, by rfl⟩ : syracuseStep 1539533 = 577325) (by norm_num)
theorem B1539557 : Blo 1024605 1539557 := bbase (se 4 (by rfl) ⟨144333, by rfl⟩ : syracuseStep 1539557 = 288667) (by norm_num)
theorem B1539581 : Blo 1024605 1539581 := bbase (se 3 (by rfl) ⟨288671, by rfl⟩ : syracuseStep 1539581 = 577343) (by norm_num)
theorem B1539605 : Blo 1024605 1539605 := bbase (se 6 (by rfl) ⟨36084, by rfl⟩ : syracuseStep 1539605 = 72169) (by norm_num)
theorem B1539629 : Blo 1024605 1539629 := bbase (se 3 (by rfl) ⟨288680, by rfl⟩ : syracuseStep 1539629 = 577361) (by norm_num)
theorem B1539653 : Blo 1024605 1539653 := bbase (se 4 (by rfl) ⟨144342, by rfl⟩ : syracuseStep 1539653 = 288685) (by norm_num)
theorem B1539677 : Blo 1024605 1539677 := bbase (se 3 (by rfl) ⟨288689, by rfl⟩ : syracuseStep 1539677 = 577379) (by norm_num)
theorem B3505781 : Blo 1024605 3505781 := bbase (se 5 (by rfl) ⟨164333, by rfl⟩ : syracuseStep 3505781 = 328667) (by norm_num)
theorem B1539701 : Blo 1024605 1539701 := bbase (se 5 (by rfl) ⟨72173, by rfl⟩ : syracuseStep 1539701 = 144347) (by norm_num)
theorem B1539725 : Blo 1024605 1539725 := bbase (se 3 (by rfl) ⟨288698, by rfl⟩ : syracuseStep 1539725 = 577397) (by norm_num)
theorem B1539749 : Blo 1024605 1539749 := bbase (se 4 (by rfl) ⟨144351, by rfl⟩ : syracuseStep 1539749 = 288703) (by norm_num)
theorem B1539773 : Blo 1024605 1539773 := bbase (se 3 (by rfl) ⟨288707, by rfl⟩ : syracuseStep 1539773 = 577415) (by norm_num)
theorem B1539797 : Blo 1024605 1539797 := bbase (se 7 (by rfl) ⟨18044, by rfl⟩ : syracuseStep 1539797 = 36089) (by norm_num)
theorem B1539821 : Blo 1024605 1539821 := bbase (se 3 (by rfl) ⟨288716, by rfl⟩ : syracuseStep 1539821 = 577433) (by norm_num)
theorem B1539845 : Blo 1024605 1539845 := bbase (se 4 (by rfl) ⟨144360, by rfl⟩ : syracuseStep 1539845 = 288721) (by norm_num)
theorem B1539869 : Blo 1024605 1539869 := bbase (se 3 (by rfl) ⟨288725, by rfl⟩ : syracuseStep 1539869 = 577451) (by norm_num)
theorem B1539893 : Blo 1024605 1539893 := bbase (se 5 (by rfl) ⟨72182, by rfl⟩ : syracuseStep 1539893 = 144365) (by norm_num)
theorem B1539917 : Blo 1024605 1539917 := bbase (se 3 (by rfl) ⟨288734, by rfl⟩ : syracuseStep 1539917 = 577469) (by norm_num)
theorem B1539941 : Blo 1024605 1539941 := bbase (se 4 (by rfl) ⟨144369, by rfl⟩ : syracuseStep 1539941 = 288739) (by norm_num)
theorem B1539965 : Blo 1024605 1539965 := bbase (se 3 (by rfl) ⟨288743, by rfl⟩ : syracuseStep 1539965 = 577487) (by norm_num)
theorem B1539989 : Blo 1024605 1539989 := bbase (se 6 (by rfl) ⟨36093, by rfl⟩ : syracuseStep 1539989 = 72187) (by norm_num)
theorem B3899285 : Blo 1024605 3899285 := bbase (se 6 (by rfl) ⟨91389, by rfl⟩ : syracuseStep 3899285 = 182779) (by norm_num)
theorem B1540013 : Blo 1024605 1540013 := bbase (se 3 (by rfl) ⟨288752, by rfl⟩ : syracuseStep 1540013 = 577505) (by norm_num)
theorem B1540037 : Blo 1024605 1540037 := bbase (se 4 (by rfl) ⟨144378, by rfl⟩ : syracuseStep 1540037 = 288757) (by norm_num)
theorem B1540061 : Blo 1024605 1540061 := bbase (se 3 (by rfl) ⟨288761, by rfl⟩ : syracuseStep 1540061 = 577523) (by norm_num)
theorem B1540085 : Blo 1024605 1540085 := bbase (se 5 (by rfl) ⟨72191, by rfl⟩ : syracuseStep 1540085 = 144383) (by norm_num)
theorem B1540097 : Blo 1024605 1540097 := bstep (se 2 (by rfl) ⟨577536, by rfl⟩ : syracuseStep 1540097 = 1155073) B1155073
theorem B1540115 : Blo 1024605 1540115 := bstep (se 1 (by rfl) ⟨1155086, by rfl⟩ : syracuseStep 1540115 = 2310173) B2310173
theorem B1540145 : Blo 1024605 1540145 := bstep (se 2 (by rfl) ⟨577554, by rfl⟩ : syracuseStep 1540145 = 1155109) B1155109
theorem B1540163 : Blo 1024605 1540163 := bstep (se 1 (by rfl) ⟨1155122, by rfl⟩ : syracuseStep 1540163 = 2310245) B2310245
theorem B1540193 : Blo 1024605 1540193 := bstep (se 2 (by rfl) ⟨577572, by rfl⟩ : syracuseStep 1540193 = 1155145) B1155145
theorem B1540211 : Blo 1024605 1540211 := bstep (se 1 (by rfl) ⟨1155158, by rfl⟩ : syracuseStep 1540211 = 2310317) B2310317
theorem B1540241 : Blo 1024605 1540241 := bstep (se 2 (by rfl) ⟨577590, by rfl⟩ : syracuseStep 1540241 = 1155181) B1155181
theorem B1540259 : Blo 1024605 1540259 := bstep (se 1 (by rfl) ⟨1155194, by rfl⟩ : syracuseStep 1540259 = 2310389) B2310389
theorem B1540289 : Blo 1024605 1540289 := bstep (se 2 (by rfl) ⟨577608, by rfl⟩ : syracuseStep 1540289 = 1155217) B1155217
theorem B1540307 : Blo 1024605 1540307 := bstep (se 1 (by rfl) ⟨1155230, by rfl⟩ : syracuseStep 1540307 = 2310461) B2310461
theorem B1540337 : Blo 1024605 1540337 := bstep (se 2 (by rfl) ⟨577626, by rfl⟩ : syracuseStep 1540337 = 1155253) B1155253
theorem B1540355 : Blo 1024605 1540355 := bstep (se 1 (by rfl) ⟨1155266, by rfl⟩ : syracuseStep 1540355 = 2310533) B2310533
theorem B1540385 : Blo 1024605 1540385 := bstep (se 2 (by rfl) ⟨577644, by rfl⟩ : syracuseStep 1540385 = 1155289) B1155289
theorem B1540403 : Blo 1024605 1540403 := bstep (se 1 (by rfl) ⟨1155302, by rfl⟩ : syracuseStep 1540403 = 2310605) B2310605
theorem B1540433 : Blo 1024605 1540433 := bstep (se 2 (by rfl) ⟨577662, by rfl⟩ : syracuseStep 1540433 = 1155325) B1155325
theorem B1540451 : Blo 1024605 1540451 := bstep (se 1 (by rfl) ⟨1155338, by rfl⟩ : syracuseStep 1540451 = 2310677) B2310677
theorem B4686179 : Blo 1024605 4686179 := bstep (se 1 (by rfl) ⟨3514634, by rfl⟩ : syracuseStep 4686179 = 7029269) B7029269
theorem B1540481 : Blo 1024605 1540481 := bstep (se 2 (by rfl) ⟨577680, by rfl⟩ : syracuseStep 1540481 = 1155361) B1155361
theorem B1540499 : Blo 1024605 1540499 := bstep (se 1 (by rfl) ⟨1155374, by rfl⟩ : syracuseStep 1540499 = 2310749) B2310749
theorem B1540529 : Blo 1024605 1540529 := bstep (se 2 (by rfl) ⟨577698, by rfl⟩ : syracuseStep 1540529 = 1155397) B1155397
theorem B1540547 : Blo 1024605 1540547 := bstep (se 1 (by rfl) ⟨1155410, by rfl⟩ : syracuseStep 1540547 = 2310821) B2310821
theorem B1540577 : Blo 1024605 1540577 := bstep (se 2 (by rfl) ⟨577716, by rfl⟩ : syracuseStep 1540577 = 1155433) B1155433
theorem B1540595 : Blo 1024605 1540595 := bstep (se 1 (by rfl) ⟨1155446, by rfl⟩ : syracuseStep 1540595 = 2310893) B2310893
theorem B1540625 : Blo 1024605 1540625 := bstep (se 2 (by rfl) ⟨577734, by rfl⟩ : syracuseStep 1540625 = 1155469) B1155469
theorem B1540643 : Blo 1024605 1540643 := bstep (se 1 (by rfl) ⟨1155482, by rfl⟩ : syracuseStep 1540643 = 2310965) B2310965
theorem B1540673 : Blo 1024605 1540673 := bstep (se 2 (by rfl) ⟨577752, by rfl⟩ : syracuseStep 1540673 = 1155505) B1155505
theorem B1540691 : Blo 1024605 1540691 := bstep (se 1 (by rfl) ⟨1155518, by rfl⟩ : syracuseStep 1540691 = 2311037) B2311037
theorem B1540721 : Blo 1024605 1540721 := bstep (se 2 (by rfl) ⟨577770, by rfl⟩ : syracuseStep 1540721 = 1155541) B1155541
theorem B1540739 : Blo 1024605 1540739 := bstep (se 1 (by rfl) ⟨1155554, by rfl⟩ : syracuseStep 1540739 = 2311109) B2311109
theorem B1540769 : Blo 1024605 1540769 := bstep (se 2 (by rfl) ⟨577788, by rfl⟩ : syracuseStep 1540769 = 1155577) B1155577
theorem B1540787 : Blo 1024605 1540787 := bstep (se 1 (by rfl) ⟨1155590, by rfl⟩ : syracuseStep 1540787 = 2311181) B2311181
theorem B1540817 : Blo 1024605 1540817 := bstep (se 2 (by rfl) ⟨577806, by rfl⟩ : syracuseStep 1540817 = 1155613) B1155613
theorem B1540835 : Blo 1024605 1540835 := bstep (se 1 (by rfl) ⟨1155626, by rfl⟩ : syracuseStep 1540835 = 2311253) B2311253
theorem B1540865 : Blo 1024605 1540865 := bstep (se 2 (by rfl) ⟨577824, by rfl⟩ : syracuseStep 1540865 = 1155649) B1155649
theorem B2196227 : Blo 1024605 2196227 := bstep (se 1 (by rfl) ⟨1647170, by rfl⟩ : syracuseStep 2196227 = 3294341) B3294341
theorem B1540883 : Blo 1024605 1540883 := bstep (se 1 (by rfl) ⟨1155662, by rfl⟩ : syracuseStep 1540883 = 2311325) B2311325
theorem B1540913 : Blo 1024605 1540913 := bstep (se 2 (by rfl) ⟨577842, by rfl⟩ : syracuseStep 1540913 = 1155685) B1155685
theorem B1540931 : Blo 1024605 1540931 := bstep (se 1 (by rfl) ⟨1155698, by rfl⟩ : syracuseStep 1540931 = 2311397) B2311397
theorem B1540961 : Blo 1024605 1540961 := bstep (se 2 (by rfl) ⟨577860, by rfl⟩ : syracuseStep 1540961 = 1155721) B1155721
theorem B1540979 : Blo 1024605 1540979 := bstep (se 1 (by rfl) ⟨1155734, by rfl⟩ : syracuseStep 1540979 = 2311469) B2311469
theorem B49873805 : Blo 1024605 49873805 := bstep (se 3 (by rfl) ⟨9351338, by rfl⟩ : syracuseStep 49873805 = 18702677) B18702677
theorem B1541009 : Blo 1024605 1541009 := bstep (se 2 (by rfl) ⟨577878, by rfl⟩ : syracuseStep 1541009 = 1155757) B1155757
theorem B1541027 : Blo 1024605 1541027 := bstep (se 1 (by rfl) ⟨1155770, by rfl⟩ : syracuseStep 1541027 = 2311541) B2311541
theorem B1541057 : Blo 1024605 1541057 := bstep (se 2 (by rfl) ⟨577896, by rfl⟩ : syracuseStep 1541057 = 1155793) B1155793
theorem B1541075 : Blo 1024605 1541075 := bstep (se 1 (by rfl) ⟨1155806, by rfl⟩ : syracuseStep 1541075 = 2311613) B2311613
theorem B1541105 : Blo 1024605 1541105 := bstep (se 2 (by rfl) ⟨577914, by rfl⟩ : syracuseStep 1541105 = 1155829) B1155829
theorem B1541123 : Blo 1024605 1541123 := bstep (se 1 (by rfl) ⟨1155842, by rfl⟩ : syracuseStep 1541123 = 2311685) B2311685
theorem B9372685 : Blo 1024605 9372685 := bstep (se 3 (by rfl) ⟨1757378, by rfl⟩ : syracuseStep 9372685 = 3514757) B3514757
theorem B1541153 : Blo 1024605 1541153 := bstep (se 2 (by rfl) ⟨577932, by rfl⟩ : syracuseStep 1541153 = 1155865) B1155865
theorem B1541171 : Blo 1024605 1541171 := bstep (se 1 (by rfl) ⟨1155878, by rfl⟩ : syracuseStep 1541171 = 2311757) B2311757
theorem B1541201 : Blo 1024605 1541201 := bstep (se 2 (by rfl) ⟨577950, by rfl⟩ : syracuseStep 1541201 = 1155901) B1155901
theorem B1541219 : Blo 1024605 1541219 := bstep (se 1 (by rfl) ⟨1155914, by rfl⟩ : syracuseStep 1541219 = 2311829) B2311829
theorem B1541249 : Blo 1024605 1541249 := bstep (se 2 (by rfl) ⟨577968, by rfl⟩ : syracuseStep 1541249 = 1155937) B1155937
theorem B6096005 : Blo 1024605 6096005 := bstep (se 4 (by rfl) ⟨571500, by rfl⟩ : syracuseStep 6096005 = 1143001) B1143001
theorem B1541267 : Blo 1024605 1541267 := bstep (se 1 (by rfl) ⟨1155950, by rfl⟩ : syracuseStep 1541267 = 2311901) B2311901
theorem B1541297 : Blo 1024605 1541297 := bstep (se 2 (by rfl) ⟨577986, by rfl⟩ : syracuseStep 1541297 = 1155973) B1155973
theorem B1541315 : Blo 1024605 1541315 := bstep (se 1 (by rfl) ⟨1155986, by rfl⟩ : syracuseStep 1541315 = 2311973) B2311973
theorem B1541345 : Blo 1024605 1541345 := bstep (se 2 (by rfl) ⟨578004, by rfl⟩ : syracuseStep 1541345 = 1156009) B1156009
theorem B1541363 : Blo 1024605 1541363 := bstep (se 1 (by rfl) ⟨1156022, by rfl⟩ : syracuseStep 1541363 = 2312045) B2312045
theorem B1541393 : Blo 1024605 1541393 := bstep (se 2 (by rfl) ⟨578022, by rfl⟩ : syracuseStep 1541393 = 1156045) B1156045
theorem B1541411 : Blo 1024605 1541411 := bstep (se 1 (by rfl) ⟨1156058, by rfl⟩ : syracuseStep 1541411 = 2312117) B2312117
theorem B1541441 : Blo 1024605 1541441 := bstep (se 2 (by rfl) ⟨578040, by rfl⟩ : syracuseStep 1541441 = 1156081) B1156081
theorem B1541459 : Blo 1024605 1541459 := bstep (se 1 (by rfl) ⟨1156094, by rfl⟩ : syracuseStep 1541459 = 2312189) B2312189
theorem B1541489 : Blo 1024605 1541489 := bstep (se 2 (by rfl) ⟨578058, by rfl⟩ : syracuseStep 1541489 = 1156117) B1156117
theorem B1541507 : Blo 1024605 1541507 := bstep (se 1 (by rfl) ⟨1156130, by rfl⟩ : syracuseStep 1541507 = 2312261) B2312261
theorem B2917777 : Blo 1024605 2917777 := bstep (se 2 (by rfl) ⟨1094166, by rfl⟩ : syracuseStep 2917777 = 2188333) B2188333
theorem B1541537 : Blo 1024605 1541537 := bstep (se 2 (by rfl) ⟨578076, by rfl⟩ : syracuseStep 1541537 = 1156153) B1156153
theorem B1541555 : Blo 1024605 1541555 := bstep (se 1 (by rfl) ⟨1156166, by rfl⟩ : syracuseStep 1541555 = 2312333) B2312333
theorem B1541585 : Blo 1024605 1541585 := bstep (se 2 (by rfl) ⟨578094, by rfl⟩ : syracuseStep 1541585 = 1156189) B1156189
theorem B1541603 : Blo 1024605 1541603 := bstep (se 1 (by rfl) ⟨1156202, by rfl⟩ : syracuseStep 1541603 = 2312405) B2312405
theorem B1541633 : Blo 1024605 1541633 := bstep (se 2 (by rfl) ⟨578112, by rfl⟩ : syracuseStep 1541633 = 1156225) B1156225
theorem B1541651 : Blo 1024605 1541651 := bstep (se 1 (by rfl) ⟨1156238, by rfl⟩ : syracuseStep 1541651 = 2312477) B2312477
theorem B2917937 : Blo 1024605 2917937 := bstep (se 2 (by rfl) ⟨1094226, by rfl⟩ : syracuseStep 2917937 = 2188453) B2188453
theorem B1541681 : Blo 1024605 1541681 := bstep (se 2 (by rfl) ⟨578130, by rfl⟩ : syracuseStep 1541681 = 1156261) B1156261
theorem B1541699 : Blo 1024605 1541699 := bstep (se 1 (by rfl) ⟨1156274, by rfl⟩ : syracuseStep 1541699 = 2312549) B2312549
theorem B1541729 : Blo 1024605 1541729 := bstep (se 2 (by rfl) ⟨578148, by rfl⟩ : syracuseStep 1541729 = 1156297) B1156297
theorem B1541747 : Blo 1024605 1541747 := bstep (se 1 (by rfl) ⟨1156310, by rfl⟩ : syracuseStep 1541747 = 2312621) B2312621
theorem B1541777 : Blo 1024605 1541777 := bstep (se 2 (by rfl) ⟨578166, by rfl⟩ : syracuseStep 1541777 = 1156333) B1156333
theorem B2918051 : Blo 1024605 2918051 := bstep (se 1 (by rfl) ⟨2188538, by rfl⟩ : syracuseStep 2918051 = 4377077) B4377077
theorem B1541795 : Blo 1024605 1541795 := bstep (se 1 (by rfl) ⟨1156346, by rfl⟩ : syracuseStep 1541795 = 2312693) B2312693
theorem B1541825 : Blo 1024605 1541825 := bstep (se 2 (by rfl) ⟨578184, by rfl⟩ : syracuseStep 1541825 = 1156369) B1156369
theorem B1541843 : Blo 1024605 1541843 := bstep (se 1 (by rfl) ⟨1156382, by rfl⟩ : syracuseStep 1541843 = 2312765) B2312765
theorem B1541873 : Blo 1024605 1541873 := bstep (se 2 (by rfl) ⟨578202, by rfl⟩ : syracuseStep 1541873 = 1156405) B1156405
theorem B1541891 : Blo 1024605 1541891 := bstep (se 1 (by rfl) ⟨1156418, by rfl⟩ : syracuseStep 1541891 = 2312837) B2312837
theorem B1541921 : Blo 1024605 1541921 := bstep (se 2 (by rfl) ⟨578220, by rfl⟩ : syracuseStep 1541921 = 1156441) B1156441
theorem B1541939 : Blo 1024605 1541939 := bstep (se 1 (by rfl) ⟨1156454, by rfl⟩ : syracuseStep 1541939 = 2312909) B2312909
theorem B1541969 : Blo 1024605 1541969 := bstep (se 2 (by rfl) ⟨578238, by rfl⟩ : syracuseStep 1541969 = 1156477) B1156477
theorem B1541987 : Blo 1024605 1541987 := bstep (se 1 (by rfl) ⟨1156490, by rfl⟩ : syracuseStep 1541987 = 2312981) B2312981
theorem B1542017 : Blo 1024605 1542017 := bstep (se 2 (by rfl) ⟨578256, by rfl⟩ : syracuseStep 1542017 = 1156513) B1156513
theorem B1542035 : Blo 1024605 1542035 := bstep (se 1 (by rfl) ⟨1156526, by rfl⟩ : syracuseStep 1542035 = 2313053) B2313053
theorem B6588323 : Blo 1024605 6588323 := bstep (se 1 (by rfl) ⟨4941242, by rfl⟩ : syracuseStep 6588323 = 9882485) B9882485
theorem B1542065 : Blo 1024605 1542065 := bstep (se 2 (by rfl) ⟨578274, by rfl⟩ : syracuseStep 1542065 = 1156549) B1156549
theorem B1542083 : Blo 1024605 1542083 := bstep (se 1 (by rfl) ⟨1156562, by rfl⟩ : syracuseStep 1542083 = 2313125) B2313125
theorem B1542113 : Blo 1024605 1542113 := bstep (se 2 (by rfl) ⟨578292, by rfl⟩ : syracuseStep 1542113 = 1156585) B1156585
theorem B1542131 : Blo 1024605 1542131 := bstep (se 1 (by rfl) ⟨1156598, by rfl⟩ : syracuseStep 1542131 = 2313197) B2313197
theorem B1542161 : Blo 1024605 1542161 := bstep (se 2 (by rfl) ⟨578310, by rfl⟩ : syracuseStep 1542161 = 1156621) B1156621
theorem B1542179 : Blo 1024605 1542179 := bstep (se 1 (by rfl) ⟨1156634, by rfl⟩ : syracuseStep 1542179 = 2313269) B2313269
theorem B1542209 : Blo 1024605 1542209 := bstep (se 2 (by rfl) ⟨578328, by rfl⟩ : syracuseStep 1542209 = 1156657) B1156657
theorem B3901517 : Blo 1024605 3901517 := bstep (se 3 (by rfl) ⟨731534, by rfl⟩ : syracuseStep 3901517 = 1463069) B1463069
theorem B4687949 : Blo 1024605 4687949 := bstep (se 3 (by rfl) ⟨878990, by rfl⟩ : syracuseStep 4687949 = 1757981) B1757981
theorem B1542227 : Blo 1024605 1542227 := bstep (se 1 (by rfl) ⟨1156670, by rfl⟩ : syracuseStep 1542227 = 2313341) B2313341
theorem B1542257 : Blo 1024605 1542257 := bstep (se 2 (by rfl) ⟨578346, by rfl⟩ : syracuseStep 1542257 = 1156693) B1156693
theorem B1542275 : Blo 1024605 1542275 := bstep (se 1 (by rfl) ⟨1156706, by rfl⟩ : syracuseStep 1542275 = 2313413) B2313413
theorem B1542305 : Blo 1024605 1542305 := bstep (se 2 (by rfl) ⟨578364, by rfl⟩ : syracuseStep 1542305 = 1156729) B1156729
theorem B1542323 : Blo 1024605 1542323 := bstep (se 1 (by rfl) ⟨1156742, by rfl⟩ : syracuseStep 1542323 = 2313485) B2313485
theorem B1542353 : Blo 1024605 1542353 := bstep (se 2 (by rfl) ⟨578382, by rfl⟩ : syracuseStep 1542353 = 1156765) B1156765
theorem B1542371 : Blo 1024605 1542371 := bstep (se 1 (by rfl) ⟨1156778, by rfl⟩ : syracuseStep 1542371 = 2313557) B2313557
theorem B1542401 : Blo 1024605 1542401 := bstep (se 2 (by rfl) ⟨578400, by rfl⟩ : syracuseStep 1542401 = 1156801) B1156801
theorem B1542419 : Blo 1024605 1542419 := bstep (se 1 (by rfl) ⟨1156814, by rfl⟩ : syracuseStep 1542419 = 2313629) B2313629
theorem B1542449 : Blo 1024605 1542449 := bstep (se 2 (by rfl) ⟨578418, by rfl⟩ : syracuseStep 1542449 = 1156837) B1156837
theorem B1542467 : Blo 1024605 1542467 := bstep (se 1 (by rfl) ⟨1156850, by rfl⟩ : syracuseStep 1542467 = 2313701) B2313701
theorem B1542497 : Blo 1024605 1542497 := bstep (se 2 (by rfl) ⟨578436, by rfl⟩ : syracuseStep 1542497 = 1156873) B1156873
theorem B1542515 : Blo 1024605 1542515 := bstep (se 1 (by rfl) ⟨1156886, by rfl⟩ : syracuseStep 1542515 = 2313773) B2313773
theorem B5147021 : Blo 1024605 5147021 := bstep (se 3 (by rfl) ⟨965066, by rfl⟩ : syracuseStep 5147021 = 1930133) B1930133
theorem B1542545 : Blo 1024605 1542545 := bstep (se 2 (by rfl) ⟨578454, by rfl⟩ : syracuseStep 1542545 = 1156909) B1156909
theorem B1542563 : Blo 1024605 1542563 := bstep (se 1 (by rfl) ⟨1156922, by rfl⟩ : syracuseStep 1542563 = 2313845) B2313845
theorem B1542593 : Blo 1024605 1542593 := bstep (se 2 (by rfl) ⟨578472, by rfl⟩ : syracuseStep 1542593 = 1156945) B1156945
theorem B1542611 : Blo 1024605 1542611 := bstep (se 1 (by rfl) ⟨1156958, by rfl⟩ : syracuseStep 1542611 = 2313917) B2313917
theorem B1542641 : Blo 1024605 1542641 := bstep (se 2 (by rfl) ⟨578490, by rfl⟩ : syracuseStep 1542641 = 1156981) B1156981
theorem B1542659 : Blo 1024605 1542659 := bstep (se 1 (by rfl) ⟨1156994, by rfl⟩ : syracuseStep 1542659 = 2313989) B2313989
theorem B1542689 : Blo 1024605 1542689 := bstep (se 2 (by rfl) ⟨578508, by rfl⟩ : syracuseStep 1542689 = 1157017) B1157017
theorem B1542707 : Blo 1024605 1542707 := bstep (se 1 (by rfl) ⟨1157030, by rfl⟩ : syracuseStep 1542707 = 2314061) B2314061
theorem B1542737 : Blo 1024605 1542737 := bstep (se 2 (by rfl) ⟨578526, by rfl⟩ : syracuseStep 1542737 = 1157053) B1157053
theorem B1542755 : Blo 1024605 1542755 := bstep (se 1 (by rfl) ⟨1157066, by rfl⟩ : syracuseStep 1542755 = 2314133) B2314133
theorem B1542785 : Blo 1024605 1542785 := bstep (se 2 (by rfl) ⟨578544, by rfl⟩ : syracuseStep 1542785 = 1157089) B1157089
theorem B2919053 : Blo 1024605 2919053 := bstep (se 3 (by rfl) ⟨547322, by rfl⟩ : syracuseStep 2919053 = 1094645) B1094645
theorem B1542803 : Blo 1024605 1542803 := bstep (se 1 (by rfl) ⟨1157102, by rfl⟩ : syracuseStep 1542803 = 2314205) B2314205
theorem B1542833 : Blo 1024605 1542833 := bstep (se 2 (by rfl) ⟨578562, by rfl⟩ : syracuseStep 1542833 = 1157125) B1157125
theorem B1542851 : Blo 1024605 1542851 := bstep (se 1 (by rfl) ⟨1157138, by rfl⟩ : syracuseStep 1542851 = 2314277) B2314277
theorem B1542881 : Blo 1024605 1542881 := bstep (se 2 (by rfl) ⟨578580, by rfl⟩ : syracuseStep 1542881 = 1157161) B1157161
theorem B1542899 : Blo 1024605 1542899 := bstep (se 1 (by rfl) ⟨1157174, by rfl⟩ : syracuseStep 1542899 = 2314349) B2314349
theorem B2919235 : Blo 1024605 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B2919395 : Blo 1024605 2919395 := bstep (se 1 (by rfl) ⟨2189546, by rfl⟩ : syracuseStep 2919395 = 4379093) B4379093
theorem B1641475 : Blo 1024605 1641475 := bstep (se 1 (by rfl) ⟨1231106, by rfl⟩ : syracuseStep 1641475 = 2462213) B2462213
theorem B3706019 : Blo 1024605 3706019 := bstep (se 1 (by rfl) ⟨2779514, by rfl⟩ : syracuseStep 3706019 = 5559029) B5559029
theorem B7409009 : Blo 1024605 7409009 := bstep (se 2 (by rfl) ⟨2778378, by rfl⟩ : syracuseStep 7409009 = 5556757) B5556757
theorem B22842737 : Blo 1024605 22842737 := bstep (se 2 (by rfl) ⟨8566026, by rfl⟩ : syracuseStep 22842737 = 17132053) B17132053
theorem B8785421 : Blo 1024605 8785421 := bstep (se 3 (by rfl) ⟨1647266, by rfl⟩ : syracuseStep 8785421 = 3294533) B3294533
theorem B4165283 : Blo 1024605 4165283 := bstep (se 1 (by rfl) ⟨3123962, by rfl⟩ : syracuseStep 4165283 = 6247925) B6247925
theorem B6590321 : Blo 1024605 6590321 := bstep (se 2 (by rfl) ⟨2471370, by rfl⟩ : syracuseStep 6590321 = 4942741) B4942741
theorem B1642403 : Blo 1024605 1642403 := bstep (se 1 (by rfl) ⟨1231802, by rfl⟩ : syracuseStep 1642403 = 2463605) B2463605
theorem B2920465 : Blo 1024605 2920465 := bstep (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) B2190349
theorem B11079821 : Blo 1024605 11079821 := bstep (se 3 (by rfl) ⟨2077466, by rfl⟩ : syracuseStep 11079821 = 4154933) B4154933
theorem B1642673 : Blo 1024605 1642673 := bstep (se 2 (by rfl) ⟨616002, by rfl⟩ : syracuseStep 1642673 = 1232005) B1232005
theorem B1249555 : Blo 1024605 1249555 := bstep (se 1 (by rfl) ⟨937166, by rfl⟩ : syracuseStep 1249555 = 1874333) B1874333
theorem B1479107 : Blo 1024605 1479107 := bstep (se 1 (by rfl) ⟨1109330, by rfl⟩ : syracuseStep 1479107 = 2218661) B2218661
theorem B1642961 : Blo 1024605 1642961 := bstep (se 2 (by rfl) ⟨616110, by rfl⟩ : syracuseStep 1642961 = 1232221) B1232221
theorem B1250051 : Blo 1024605 1250051 := bstep (se 1 (by rfl) ⟨937538, by rfl⟩ : syracuseStep 1250051 = 1875077) B1875077
theorem B1643377 : Blo 1024605 1643377 := bstep (se 2 (by rfl) ⟨616266, by rfl⟩ : syracuseStep 1643377 = 1232533) B1232533
theorem B3904433 : Blo 1024605 3904433 := bstep (se 2 (by rfl) ⟨1464162, by rfl⟩ : syracuseStep 3904433 = 2928325) B2928325
theorem B12489713 : Blo 1024605 12489713 := bstep (se 2 (by rfl) ⟨4683642, by rfl⟩ : syracuseStep 12489713 = 9367285) B9367285
theorem B11703365 : Blo 1024605 11703365 := bstep (se 4 (by rfl) ⟨1097190, by rfl⟩ : syracuseStep 11703365 = 2194381) B2194381
theorem B2921741 : Blo 1024605 2921741 := bstep (se 3 (by rfl) ⟨547826, by rfl⟩ : syracuseStep 2921741 = 1095653) B1095653
theorem B2594065 : Blo 1024605 2594065 := bstep (se 2 (by rfl) ⟨972774, by rfl⟩ : syracuseStep 2594065 = 1945549) B1945549
theorem B2463011 : Blo 1024605 2463011 := bstep (se 1 (by rfl) ⟨1847258, by rfl⟩ : syracuseStep 2463011 = 3694517) B3694517
theorem B2921923 : Blo 1024605 2921923 := bstep (se 1 (by rfl) ⟨2191442, by rfl⟩ : syracuseStep 2921923 = 4382885) B4382885
theorem B2921969 : Blo 1024605 2921969 := bstep (se 2 (by rfl) ⟨1095738, by rfl⟩ : syracuseStep 2921969 = 2191477) B2191477
theorem B2594339 : Blo 1024605 2594339 := bstep (se 1 (by rfl) ⟨1945754, by rfl⟩ : syracuseStep 2594339 = 3891509) B3891509
theorem B9508549 : Blo 1024605 9508549 := bstep (se 4 (by rfl) ⟨891426, by rfl⟩ : syracuseStep 9508549 = 1782853) B1782853
theorem B2594531 : Blo 1024605 2594531 := bstep (se 1 (by rfl) ⟨1945898, by rfl⟩ : syracuseStep 2594531 = 3891797) B3891797
theorem B1644275 : Blo 1024605 1644275 := bstep (se 1 (by rfl) ⟨1233206, by rfl⟩ : syracuseStep 1644275 = 2466413) B2466413
theorem B1152787 : Blo 1024605 1152787 := bstep (se 1 (by rfl) ⟨864590, by rfl⟩ : syracuseStep 1152787 = 1729181) B1729181
theorem B1152931 : Blo 1024605 1152931 := bstep (se 1 (by rfl) ⟨864698, by rfl⟩ : syracuseStep 1152931 = 1729397) B1729397
theorem B1644499 : Blo 1024605 1644499 := bstep (se 1 (by rfl) ⟨1233374, by rfl⟩ : syracuseStep 1644499 = 2466749) B2466749
theorem B1480723 : Blo 1024605 1480723 := bstep (se 1 (by rfl) ⟨1110542, by rfl⟩ : syracuseStep 1480723 = 2221085) B2221085
theorem B1153075 : Blo 1024605 1153075 := bstep (se 1 (by rfl) ⟨864806, by rfl⟩ : syracuseStep 1153075 = 1729613) B1729613
theorem B5838925 : Blo 1024605 5838925 := bstep (se 3 (by rfl) ⟨1094798, by rfl⟩ : syracuseStep 5838925 = 2189597) B2189597
theorem B1153219 : Blo 1024605 1153219 := bstep (se 1 (by rfl) ⟨864914, by rfl⟩ : syracuseStep 1153219 = 1729829) B1729829
theorem B3119363 : Blo 1024605 3119363 := bstep (se 1 (by rfl) ⟨2339522, by rfl⟩ : syracuseStep 3119363 = 4679045) B4679045
theorem B1153363 : Blo 1024605 1153363 := bstep (se 1 (by rfl) ⟨865022, by rfl⟩ : syracuseStep 1153363 = 1730045) B1730045
theorem B1317235 : Blo 1024605 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B1153507 : Blo 1024605 1153507 := bstep (se 1 (by rfl) ⟨865130, by rfl⟩ : syracuseStep 1153507 = 1730261) B1730261
theorem B9869795 : Blo 1024605 9869795 := bstep (se 1 (by rfl) ⟨7402346, by rfl⟩ : syracuseStep 9869795 = 14804693) B14804693
theorem B17570357 : Blo 1024605 17570357 := bstep (se 5 (by rfl) ⟨823610, by rfl⟩ : syracuseStep 17570357 = 1647221) B1647221
theorem B1153651 : Blo 1024605 1153651 := bstep (se 1 (by rfl) ⟨865238, by rfl⟩ : syracuseStep 1153651 = 1730477) B1730477
theorem B2595473 : Blo 1024605 2595473 := bstep (se 2 (by rfl) ⟨973302, by rfl⟩ : syracuseStep 2595473 = 1946605) B1946605
theorem B2595523 : Blo 1024605 2595523 := bstep (se 1 (by rfl) ⟨1946642, by rfl⟩ : syracuseStep 2595523 = 3893285) B3893285
theorem B1153795 : Blo 1024605 1153795 := bstep (se 1 (by rfl) ⟨865346, by rfl⟩ : syracuseStep 1153795 = 1730693) B1730693
theorem B2595665 : Blo 1024605 2595665 := bstep (se 2 (by rfl) ⟨973374, by rfl⟩ : syracuseStep 2595665 = 1946749) B1946749
theorem B2464643 : Blo 1024605 2464643 := bstep (se 1 (by rfl) ⟨1848482, by rfl⟩ : syracuseStep 2464643 = 3696965) B3696965
theorem B1153939 : Blo 1024605 1153939 := bstep (se 1 (by rfl) ⟨865454, by rfl⟩ : syracuseStep 1153939 = 1730909) B1730909
theorem B2923427 : Blo 1024605 2923427 := bstep (se 1 (by rfl) ⟨2192570, by rfl⟩ : syracuseStep 2923427 = 4385141) B4385141
theorem B1645505 : Blo 1024605 1645505 := bstep (se 2 (by rfl) ⟨617064, by rfl⟩ : syracuseStep 1645505 = 1234129) B1234129
theorem B1154083 : Blo 1024605 1154083 := bstep (se 1 (by rfl) ⟨865562, by rfl⟩ : syracuseStep 1154083 = 1731125) B1731125
theorem B3284077 : Blo 1024605 3284077 := bstep (se 3 (by rfl) ⟨615764, by rfl⟩ : syracuseStep 3284077 = 1231529) B1231529
theorem B1645697 : Blo 1024605 1645697 := bstep (se 2 (by rfl) ⟨617136, by rfl⟩ : syracuseStep 1645697 = 1234273) B1234273
theorem B4168867 : Blo 1024605 4168867 := bstep (se 1 (by rfl) ⟨3126650, by rfl⟩ : syracuseStep 4168867 = 6253301) B6253301
theorem B1154227 : Blo 1024605 1154227 := bstep (se 1 (by rfl) ⟨865670, by rfl⟩ : syracuseStep 1154227 = 1731341) B1731341
theorem B1154371 : Blo 1024605 1154371 := bstep (se 1 (by rfl) ⟨865778, by rfl⟩ : syracuseStep 1154371 = 1731557) B1731557
theorem B13180229 : Blo 1024605 13180229 := bstep (se 4 (by rfl) ⟨1235646, by rfl⟩ : syracuseStep 13180229 = 2471293) B2471293
theorem B1580419 : Blo 1024605 1580419 := bstep (se 1 (by rfl) ⟨1185314, by rfl⟩ : syracuseStep 1580419 = 2370629) B2370629
theorem B3513773 : Blo 1024605 3513773 := bstep (se 3 (by rfl) ⟨658832, by rfl⟩ : syracuseStep 3513773 = 1317665) B1317665
theorem B1154515 : Blo 1024605 1154515 := bstep (se 1 (by rfl) ⟨865886, by rfl⟩ : syracuseStep 1154515 = 1731773) B1731773
theorem B3120653 : Blo 1024605 3120653 := bstep (se 3 (by rfl) ⟨585122, by rfl⟩ : syracuseStep 3120653 = 1170245) B1170245
theorem B3284525 : Blo 1024605 3284525 := bstep (se 3 (by rfl) ⟨615848, by rfl⟩ : syracuseStep 3284525 = 1231697) B1231697
theorem B1154659 : Blo 1024605 1154659 := bstep (se 1 (by rfl) ⟨865994, by rfl⟩ : syracuseStep 1154659 = 1731989) B1731989
theorem B1154803 : Blo 1024605 1154803 := bstep (se 1 (by rfl) ⟨866102, by rfl⟩ : syracuseStep 1154803 = 1732205) B1732205
theorem B6233861 : Blo 1024605 6233861 := bstep (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) B1168849
theorem B2596657 : Blo 1024605 2596657 := bstep (se 2 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 2596657 = 1947493) B1947493
theorem B3514211 : Blo 1024605 3514211 := bstep (se 1 (by rfl) ⟨2635658, by rfl⟩ : syracuseStep 3514211 = 5271317) B5271317
theorem B15179633 : Blo 1024605 15179633 := bstep (se 2 (by rfl) ⟨5692362, by rfl⟩ : syracuseStep 15179633 = 11384725) B11384725
theorem B1154947 : Blo 1024605 1154947 := bstep (se 1 (by rfl) ⟨866210, by rfl⟩ : syracuseStep 1154947 = 1732421) B1732421
theorem B1482673 : Blo 1024605 1482673 := bstep (se 2 (by rfl) ⟨556002, by rfl⟩ : syracuseStep 1482673 = 1112005) B1112005
theorem B5840909 : Blo 1024605 5840909 := bstep (se 3 (by rfl) ⟨1095170, by rfl⟩ : syracuseStep 5840909 = 2190341) B2190341
theorem B1155091 : Blo 1024605 1155091 := bstep (se 1 (by rfl) ⟨866318, by rfl⟩ : syracuseStep 1155091 = 1732637) B1732637
theorem B1581121 : Blo 1024605 1581121 := bstep (se 2 (by rfl) ⟨592920, by rfl⟩ : syracuseStep 1581121 = 1185841) B1185841
theorem B2596931 : Blo 1024605 2596931 := bstep (se 1 (by rfl) ⟨1947698, by rfl⟩ : syracuseStep 2596931 = 3895397) B3895397
theorem B2924657 : Blo 1024605 2924657 := bstep (se 2 (by rfl) ⟨1096746, by rfl⟩ : syracuseStep 2924657 = 2193493) B2193493
theorem B1155235 : Blo 1024605 1155235 := bstep (se 1 (by rfl) ⟨866426, by rfl⟩ : syracuseStep 1155235 = 1732853) B1732853
theorem B5546225 : Blo 1024605 5546225 := bstep (se 2 (by rfl) ⟨2079834, by rfl⟩ : syracuseStep 5546225 = 4159669) B4159669
theorem B2597123 : Blo 1024605 2597123 := bstep (se 1 (by rfl) ⟨1947842, by rfl⟩ : syracuseStep 2597123 = 3895685) B3895685
theorem B2466065 : Blo 1024605 2466065 := bstep (se 2 (by rfl) ⟨924774, by rfl⟩ : syracuseStep 2466065 = 1849549) B1849549
theorem B1876241 : Blo 1024605 1876241 := bstep (se 2 (by rfl) ⟨703590, by rfl⟩ : syracuseStep 1876241 = 1407181) B1407181
theorem B1155379 : Blo 1024605 1155379 := bstep (se 1 (by rfl) ⟨866534, by rfl⟩ : syracuseStep 1155379 = 1733069) B1733069
theorem B1155523 : Blo 1024605 1155523 := bstep (se 1 (by rfl) ⟨866642, by rfl⟩ : syracuseStep 1155523 = 1733285) B1733285
theorem B1155667 : Blo 1024605 1155667 := bstep (se 1 (by rfl) ⟨866750, by rfl⟩ : syracuseStep 1155667 = 1733501) B1733501
theorem B1024611 : Blo 1024605 1024611 := bstep (se 1 (by rfl) ⟨768458, by rfl⟩ : syracuseStep 1024611 = 1536917) B1536917
theorem B1024627 : Blo 1024605 1024627 := bstep (se 1 (by rfl) ⟨768470, by rfl⟩ : syracuseStep 1024627 = 1536941) B1536941
theorem B1024643 : Blo 1024605 1024643 := bstep (se 1 (by rfl) ⟨768482, by rfl⟩ : syracuseStep 1024643 = 1536965) B1536965
theorem B1024659 : Blo 1024605 1024659 := bstep (se 1 (by rfl) ⟨768494, by rfl⟩ : syracuseStep 1024659 = 1536989) B1536989
theorem B1024675 : Blo 1024605 1024675 := bstep (se 1 (by rfl) ⟨768506, by rfl⟩ : syracuseStep 1024675 = 1537013) B1537013
theorem B1188515 : Blo 1024605 1188515 := bstep (se 1 (by rfl) ⟨891386, by rfl⟩ : syracuseStep 1188515 = 1782773) B1782773
theorem B2630321 : Blo 1024605 2630321 := bstep (se 2 (by rfl) ⟨986370, by rfl⟩ : syracuseStep 2630321 = 1972741) B1972741
theorem B1024691 : Blo 1024605 1024691 := bstep (se 1 (by rfl) ⟨768518, by rfl⟩ : syracuseStep 1024691 = 1537037) B1537037
theorem B1024707 : Blo 1024605 1024707 := bstep (se 1 (by rfl) ⟨768530, by rfl⟩ : syracuseStep 1024707 = 1537061) B1537061
theorem B1647299 : Blo 1024605 1647299 := bstep (se 1 (by rfl) ⟨1235474, by rfl⟩ : syracuseStep 1647299 = 2470949) B2470949
theorem B1024723 : Blo 1024605 1024723 := bstep (se 1 (by rfl) ⟨768542, by rfl⟩ : syracuseStep 1024723 = 1537085) B1537085
theorem B1024739 : Blo 1024605 1024739 := bstep (se 1 (by rfl) ⟨768554, by rfl⟩ : syracuseStep 1024739 = 1537109) B1537109
theorem B1155811 : Blo 1024605 1155811 := bstep (se 1 (by rfl) ⟨866858, by rfl⟩ : syracuseStep 1155811 = 1733717) B1733717
theorem B1024755 : Blo 1024605 1024755 := bstep (se 1 (by rfl) ⟨768566, by rfl⟩ : syracuseStep 1024755 = 1537133) B1537133
theorem B1024771 : Blo 1024605 1024771 := bstep (se 1 (by rfl) ⟨768578, by rfl⟩ : syracuseStep 1024771 = 1537157) B1537157
theorem B1024787 : Blo 1024605 1024787 := bstep (se 1 (by rfl) ⟨768590, by rfl⟩ : syracuseStep 1024787 = 1537181) B1537181
theorem B1024803 : Blo 1024605 1024803 := bstep (se 1 (by rfl) ⟨768602, by rfl⟩ : syracuseStep 1024803 = 1537205) B1537205
theorem B1024819 : Blo 1024605 1024819 := bstep (se 1 (by rfl) ⟨768614, by rfl⟩ : syracuseStep 1024819 = 1537229) B1537229
theorem B1024835 : Blo 1024605 1024835 := bstep (se 1 (by rfl) ⟨768626, by rfl⟩ : syracuseStep 1024835 = 1537253) B1537253
theorem B1024851 : Blo 1024605 1024851 := bstep (se 1 (by rfl) ⟨768638, by rfl⟩ : syracuseStep 1024851 = 1537277) B1537277
theorem B1024867 : Blo 1024605 1024867 := bstep (se 1 (by rfl) ⟨768650, by rfl⟩ : syracuseStep 1024867 = 1537301) B1537301
theorem B8758115 : Blo 1024605 8758115 := bstep (se 1 (by rfl) ⟨6568586, by rfl⟩ : syracuseStep 8758115 = 13137173) B13137173
theorem B1024883 : Blo 1024605 1024883 := bstep (se 1 (by rfl) ⟨768662, by rfl⟩ : syracuseStep 1024883 = 1537325) B1537325
theorem B1155955 : Blo 1024605 1155955 := bstep (se 1 (by rfl) ⟨866966, by rfl⟩ : syracuseStep 1155955 = 1733933) B1733933
theorem B1385345 : Blo 1024605 1385345 := bstep (se 2 (by rfl) ⟨519504, by rfl⟩ : syracuseStep 1385345 = 1039009) B1039009
theorem B1024899 : Blo 1024605 1024899 := bstep (se 1 (by rfl) ⟨768674, by rfl⟩ : syracuseStep 1024899 = 1537349) B1537349
theorem B1024915 : Blo 1024605 1024915 := bstep (se 1 (by rfl) ⟨768686, by rfl⟩ : syracuseStep 1024915 = 1537373) B1537373
theorem B1024931 : Blo 1024605 1024931 := bstep (se 1 (by rfl) ⟨768698, by rfl⟩ : syracuseStep 1024931 = 1537397) B1537397
theorem B5841841 : Blo 1024605 5841841 := bstep (se 2 (by rfl) ⟨2190690, by rfl⟩ : syracuseStep 5841841 = 4381381) B4381381
theorem B1024947 : Blo 1024605 1024947 := bstep (se 1 (by rfl) ⟨768710, by rfl⟩ : syracuseStep 1024947 = 1537421) B1537421
theorem B1024963 : Blo 1024605 1024963 := bstep (se 1 (by rfl) ⟨768722, by rfl⟩ : syracuseStep 1024963 = 1537445) B1537445
theorem B2630609 : Blo 1024605 2630609 := bstep (se 2 (by rfl) ⟨986478, by rfl⟩ : syracuseStep 2630609 = 1972957) B1972957
theorem B1024979 : Blo 1024605 1024979 := bstep (se 1 (by rfl) ⟨768734, by rfl⟩ : syracuseStep 1024979 = 1537469) B1537469
theorem B1024995 : Blo 1024605 1024995 := bstep (se 1 (by rfl) ⟨768746, by rfl⟩ : syracuseStep 1024995 = 1537493) B1537493
theorem B1025011 : Blo 1024605 1025011 := bstep (se 1 (by rfl) ⟨768758, by rfl⟩ : syracuseStep 1025011 = 1537517) B1537517
theorem B1025027 : Blo 1024605 1025027 := bstep (se 1 (by rfl) ⟨768770, by rfl⟩ : syracuseStep 1025027 = 1537541) B1537541
theorem B1156099 : Blo 1024605 1156099 := bstep (se 1 (by rfl) ⟨867074, by rfl⟩ : syracuseStep 1156099 = 1734149) B1734149
theorem B1025043 : Blo 1024605 1025043 := bstep (se 1 (by rfl) ⟨768782, by rfl⟩ : syracuseStep 1025043 = 1537565) B1537565
theorem B1025059 : Blo 1024605 1025059 := bstep (se 1 (by rfl) ⟨768794, by rfl⟩ : syracuseStep 1025059 = 1537589) B1537589
theorem B1025075 : Blo 1024605 1025075 := bstep (se 1 (by rfl) ⟨768806, by rfl⟩ : syracuseStep 1025075 = 1537613) B1537613
theorem B1025091 : Blo 1024605 1025091 := bstep (se 1 (by rfl) ⟨768818, by rfl⟩ : syracuseStep 1025091 = 1537637) B1537637
theorem B1025107 : Blo 1024605 1025107 := bstep (se 1 (by rfl) ⟨768830, by rfl⟩ : syracuseStep 1025107 = 1537661) B1537661
theorem B1025123 : Blo 1024605 1025123 := bstep (se 1 (by rfl) ⟨768842, by rfl⟩ : syracuseStep 1025123 = 1537685) B1537685
theorem B1025139 : Blo 1024605 1025139 := bstep (se 1 (by rfl) ⟨768854, by rfl⟩ : syracuseStep 1025139 = 1537709) B1537709
theorem B1025155 : Blo 1024605 1025155 := bstep (se 1 (by rfl) ⟨768866, by rfl⟩ : syracuseStep 1025155 = 1537733) B1537733
theorem B1025171 : Blo 1024605 1025171 := bstep (se 1 (by rfl) ⟨768878, by rfl⟩ : syracuseStep 1025171 = 1537757) B1537757
theorem B1156243 : Blo 1024605 1156243 := bstep (se 1 (by rfl) ⟨867182, by rfl⟩ : syracuseStep 1156243 = 1734365) B1734365
theorem B1025187 : Blo 1024605 1025187 := bstep (se 1 (by rfl) ⟨768890, by rfl⟩ : syracuseStep 1025187 = 1537781) B1537781
theorem B2598065 : Blo 1024605 2598065 := bstep (se 2 (by rfl) ⟨974274, by rfl⟩ : syracuseStep 2598065 = 1948549) B1948549
theorem B1025203 : Blo 1024605 1025203 := bstep (se 1 (by rfl) ⟨768902, by rfl⟩ : syracuseStep 1025203 = 1537805) B1537805
theorem B1025219 : Blo 1024605 1025219 := bstep (se 1 (by rfl) ⟨768914, by rfl⟩ : syracuseStep 1025219 = 1537829) B1537829
theorem B1025235 : Blo 1024605 1025235 := bstep (se 1 (by rfl) ⟨768926, by rfl⟩ : syracuseStep 1025235 = 1537853) B1537853
theorem B1025251 : Blo 1024605 1025251 := bstep (se 1 (by rfl) ⟨768938, by rfl⟩ : syracuseStep 1025251 = 1537877) B1537877
theorem B2598115 : Blo 1024605 2598115 := bstep (se 1 (by rfl) ⟨1948586, by rfl⟩ : syracuseStep 2598115 = 3897173) B3897173
theorem B1025267 : Blo 1024605 1025267 := bstep (se 1 (by rfl) ⟨768950, by rfl⟩ : syracuseStep 1025267 = 1537901) B1537901
theorem B1025283 : Blo 1024605 1025283 := bstep (se 1 (by rfl) ⟨768962, by rfl⟩ : syracuseStep 1025283 = 1537925) B1537925
theorem B1025299 : Blo 1024605 1025299 := bstep (se 1 (by rfl) ⟨768974, by rfl⟩ : syracuseStep 1025299 = 1537949) B1537949
theorem B1025315 : Blo 1024605 1025315 := bstep (se 1 (by rfl) ⟨768986, by rfl⟩ : syracuseStep 1025315 = 1537973) B1537973
theorem B1156387 : Blo 1024605 1156387 := bstep (se 1 (by rfl) ⟨867290, by rfl⟩ : syracuseStep 1156387 = 1734581) B1734581
theorem B1025331 : Blo 1024605 1025331 := bstep (se 1 (by rfl) ⟨768998, by rfl⟩ : syracuseStep 1025331 = 1537997) B1537997
theorem B1025347 : Blo 1024605 1025347 := bstep (se 1 (by rfl) ⟨769010, by rfl⟩ : syracuseStep 1025347 = 1538021) B1538021
theorem B1025363 : Blo 1024605 1025363 := bstep (se 1 (by rfl) ⟨769022, by rfl⟩ : syracuseStep 1025363 = 1538045) B1538045
theorem B1025379 : Blo 1024605 1025379 := bstep (se 1 (by rfl) ⟨769034, by rfl⟩ : syracuseStep 1025379 = 1538069) B1538069
theorem B2598257 : Blo 1024605 2598257 := bstep (se 2 (by rfl) ⟨974346, by rfl⟩ : syracuseStep 2598257 = 1948693) B1948693
theorem B1025395 : Blo 1024605 1025395 := bstep (se 1 (by rfl) ⟨769046, by rfl⟩ : syracuseStep 1025395 = 1538093) B1538093
theorem B1025411 : Blo 1024605 1025411 := bstep (se 1 (by rfl) ⟨769058, by rfl⟩ : syracuseStep 1025411 = 1538117) B1538117
theorem B3122563 : Blo 1024605 3122563 := bstep (se 1 (by rfl) ⟨2341922, by rfl⟩ : syracuseStep 3122563 = 4683845) B4683845
theorem B1025427 : Blo 1024605 1025427 := bstep (se 1 (by rfl) ⟨769070, by rfl⟩ : syracuseStep 1025427 = 1538141) B1538141
theorem B1025443 : Blo 1024605 1025443 := bstep (se 1 (by rfl) ⟨769082, by rfl⟩ : syracuseStep 1025443 = 1538165) B1538165
theorem B1025459 : Blo 1024605 1025459 := bstep (se 1 (by rfl) ⟨769094, by rfl⟩ : syracuseStep 1025459 = 1538189) B1538189
theorem B1156531 : Blo 1024605 1156531 := bstep (se 1 (by rfl) ⟨867398, by rfl⟩ : syracuseStep 1156531 = 1734797) B1734797
theorem B1025475 : Blo 1024605 1025475 := bstep (se 1 (by rfl) ⟨769106, by rfl⟩ : syracuseStep 1025475 = 1538213) B1538213
theorem B1025491 : Blo 1024605 1025491 := bstep (se 1 (by rfl) ⟨769118, by rfl⟩ : syracuseStep 1025491 = 1538237) B1538237
theorem B1025507 : Blo 1024605 1025507 := bstep (se 1 (by rfl) ⟨769130, by rfl⟩ : syracuseStep 1025507 = 1538261) B1538261
theorem B1025523 : Blo 1024605 1025523 := bstep (se 1 (by rfl) ⟨769142, by rfl⟩ : syracuseStep 1025523 = 1538285) B1538285
theorem B1025539 : Blo 1024605 1025539 := bstep (se 1 (by rfl) ⟨769154, by rfl⟩ : syracuseStep 1025539 = 1538309) B1538309
theorem B1025555 : Blo 1024605 1025555 := bstep (se 1 (by rfl) ⟨769166, by rfl⟩ : syracuseStep 1025555 = 1538333) B1538333
theorem B1025571 : Blo 1024605 1025571 := bstep (se 1 (by rfl) ⟨769178, by rfl⟩ : syracuseStep 1025571 = 1538357) B1538357
theorem B2926115 : Blo 1024605 2926115 := bstep (se 1 (by rfl) ⟨2194586, by rfl⟩ : syracuseStep 2926115 = 4389173) B4389173
theorem B1025587 : Blo 1024605 1025587 := bstep (se 1 (by rfl) ⟨769190, by rfl⟩ : syracuseStep 1025587 = 1538381) B1538381
theorem B1025603 : Blo 1024605 1025603 := bstep (se 1 (by rfl) ⟨769202, by rfl⟩ : syracuseStep 1025603 = 1538405) B1538405
theorem B1156675 : Blo 1024605 1156675 := bstep (se 1 (by rfl) ⟨867506, by rfl⟩ : syracuseStep 1156675 = 1735013) B1735013
theorem B1025619 : Blo 1024605 1025619 := bstep (se 1 (by rfl) ⟨769214, by rfl⟩ : syracuseStep 1025619 = 1538429) B1538429
theorem B1025635 : Blo 1024605 1025635 := bstep (se 1 (by rfl) ⟨769226, by rfl⟩ : syracuseStep 1025635 = 1538453) B1538453
theorem B1025651 : Blo 1024605 1025651 := bstep (se 1 (by rfl) ⟨769238, by rfl⟩ : syracuseStep 1025651 = 1538477) B1538477
theorem B1025667 : Blo 1024605 1025667 := bstep (se 1 (by rfl) ⟨769250, by rfl⟩ : syracuseStep 1025667 = 1538501) B1538501
theorem B1025683 : Blo 1024605 1025683 := bstep (se 1 (by rfl) ⟨769262, by rfl⟩ : syracuseStep 1025683 = 1538525) B1538525
theorem B1025699 : Blo 1024605 1025699 := bstep (se 1 (by rfl) ⟨769274, by rfl⟩ : syracuseStep 1025699 = 1538549) B1538549
theorem B1386163 : Blo 1024605 1386163 := bstep (se 1 (by rfl) ⟨1039622, by rfl⟩ : syracuseStep 1386163 = 2079245) B2079245
theorem B1025715 : Blo 1024605 1025715 := bstep (se 1 (by rfl) ⟨769286, by rfl⟩ : syracuseStep 1025715 = 1538573) B1538573
theorem B1025731 : Blo 1024605 1025731 := bstep (se 1 (by rfl) ⟨769298, by rfl⟩ : syracuseStep 1025731 = 1538597) B1538597
theorem B1025747 : Blo 1024605 1025747 := bstep (se 1 (by rfl) ⟨769310, by rfl⟩ : syracuseStep 1025747 = 1538621) B1538621
theorem B1156819 : Blo 1024605 1156819 := bstep (se 1 (by rfl) ⟨867614, by rfl⟩ : syracuseStep 1156819 = 1735229) B1735229
theorem B1025763 : Blo 1024605 1025763 := bstep (se 1 (by rfl) ⟨769322, by rfl⟩ : syracuseStep 1025763 = 1538645) B1538645
theorem B1025779 : Blo 1024605 1025779 := bstep (se 1 (by rfl) ⟨769334, by rfl⟩ : syracuseStep 1025779 = 1538669) B1538669
theorem B1025795 : Blo 1024605 1025795 := bstep (se 1 (by rfl) ⟨769346, by rfl⟩ : syracuseStep 1025795 = 1538693) B1538693
theorem B5547781 : Blo 1024605 5547781 := bstep (se 4 (by rfl) ⟨520104, by rfl⟩ : syracuseStep 5547781 = 1040209) B1040209
theorem B1025811 : Blo 1024605 1025811 := bstep (se 1 (by rfl) ⟨769358, by rfl⟩ : syracuseStep 1025811 = 1538717) B1538717
theorem B1025827 : Blo 1024605 1025827 := bstep (se 1 (by rfl) ⟨769370, by rfl⟩ : syracuseStep 1025827 = 1538741) B1538741
theorem B1025843 : Blo 1024605 1025843 := bstep (se 1 (by rfl) ⟨769382, by rfl⟩ : syracuseStep 1025843 = 1538765) B1538765
theorem B1025859 : Blo 1024605 1025859 := bstep (se 1 (by rfl) ⟨769394, by rfl⟩ : syracuseStep 1025859 = 1538789) B1538789
theorem B1025875 : Blo 1024605 1025875 := bstep (se 1 (by rfl) ⟨769406, by rfl⟩ : syracuseStep 1025875 = 1538813) B1538813
theorem B1025891 : Blo 1024605 1025891 := bstep (se 1 (by rfl) ⟨769418, by rfl⟩ : syracuseStep 1025891 = 1538837) B1538837
theorem B1156963 : Blo 1024605 1156963 := bstep (se 1 (by rfl) ⟨867722, by rfl⟩ : syracuseStep 1156963 = 1735445) B1735445
theorem B1025907 : Blo 1024605 1025907 := bstep (se 1 (by rfl) ⟨769430, by rfl⟩ : syracuseStep 1025907 = 1538861) B1538861
theorem B1025923 : Blo 1024605 1025923 := bstep (se 1 (by rfl) ⟨769442, by rfl⟩ : syracuseStep 1025923 = 1538885) B1538885
theorem B1025939 : Blo 1024605 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B1025955 : Blo 1024605 1025955 := bstep (se 1 (by rfl) ⟨769466, by rfl⟩ : syracuseStep 1025955 = 1538933) B1538933
theorem B1025971 : Blo 1024605 1025971 := bstep (se 1 (by rfl) ⟨769478, by rfl⟩ : syracuseStep 1025971 = 1538957) B1538957
theorem B1025987 : Blo 1024605 1025987 := bstep (se 1 (by rfl) ⟨769490, by rfl⟩ : syracuseStep 1025987 = 1538981) B1538981
theorem B1026003 : Blo 1024605 1026003 := bstep (se 1 (by rfl) ⟨769502, by rfl⟩ : syracuseStep 1026003 = 1539005) B1539005
theorem B1026019 : Blo 1024605 1026019 := bstep (se 1 (by rfl) ⟨769514, by rfl⟩ : syracuseStep 1026019 = 1539029) B1539029
theorem B1026035 : Blo 1024605 1026035 := bstep (se 1 (by rfl) ⟨769526, by rfl⟩ : syracuseStep 1026035 = 1539053) B1539053
theorem B1157107 : Blo 1024605 1157107 := bstep (se 1 (by rfl) ⟨867830, by rfl⟩ : syracuseStep 1157107 = 1735661) B1735661
theorem B1026051 : Blo 1024605 1026051 := bstep (se 1 (by rfl) ⟨769538, by rfl⟩ : syracuseStep 1026051 = 1539077) B1539077
theorem B1026067 : Blo 1024605 1026067 := bstep (se 1 (by rfl) ⟨769550, by rfl⟩ : syracuseStep 1026067 = 1539101) B1539101
theorem B1026083 : Blo 1024605 1026083 := bstep (se 1 (by rfl) ⟨769562, by rfl⟩ : syracuseStep 1026083 = 1539125) B1539125
theorem B1026099 : Blo 1024605 1026099 := bstep (se 1 (by rfl) ⟨769574, by rfl⟩ : syracuseStep 1026099 = 1539149) B1539149
theorem B1026115 : Blo 1024605 1026115 := bstep (se 1 (by rfl) ⟨769586, by rfl⟩ : syracuseStep 1026115 = 1539173) B1539173
theorem B1026131 : Blo 1024605 1026131 := bstep (se 1 (by rfl) ⟨769598, by rfl⟩ : syracuseStep 1026131 = 1539197) B1539197
theorem B1026147 : Blo 1024605 1026147 := bstep (se 1 (by rfl) ⟨769610, by rfl⟩ : syracuseStep 1026147 = 1539221) B1539221
theorem B1026163 : Blo 1024605 1026163 := bstep (se 1 (by rfl) ⟨769622, by rfl⟩ : syracuseStep 1026163 = 1539245) B1539245
theorem B1026179 : Blo 1024605 1026179 := bstep (se 1 (by rfl) ⟨769634, by rfl⟩ : syracuseStep 1026179 = 1539269) B1539269
theorem B5187725 : Blo 1024605 5187725 := bstep (se 3 (by rfl) ⟨972698, by rfl⟩ : syracuseStep 5187725 = 1945397) B1945397
theorem B1026195 : Blo 1024605 1026195 := bstep (se 1 (by rfl) ⟨769646, by rfl⟩ : syracuseStep 1026195 = 1539293) B1539293
theorem B1026211 : Blo 1024605 1026211 := bstep (se 1 (by rfl) ⟨769658, by rfl⟩ : syracuseStep 1026211 = 1539317) B1539317
theorem B1026227 : Blo 1024605 1026227 := bstep (se 1 (by rfl) ⟨769670, by rfl⟩ : syracuseStep 1026227 = 1539341) B1539341
theorem B1026243 : Blo 1024605 1026243 := bstep (se 1 (by rfl) ⟨769682, by rfl⟩ : syracuseStep 1026243 = 1539365) B1539365
theorem B1026259 : Blo 1024605 1026259 := bstep (se 1 (by rfl) ⟨769694, by rfl⟩ : syracuseStep 1026259 = 1539389) B1539389
theorem B3287267 : Blo 1024605 3287267 := bstep (se 1 (by rfl) ⟨2465450, by rfl⟩ : syracuseStep 3287267 = 4930901) B4930901
theorem B1026275 : Blo 1024605 1026275 := bstep (se 1 (by rfl) ⟨769706, by rfl⟩ : syracuseStep 1026275 = 1539413) B1539413
theorem B1026291 : Blo 1024605 1026291 := bstep (se 1 (by rfl) ⟨769718, by rfl⟩ : syracuseStep 1026291 = 1539437) B1539437
theorem B1026307 : Blo 1024605 1026307 := bstep (se 1 (by rfl) ⟨769730, by rfl⟩ : syracuseStep 1026307 = 1539461) B1539461
theorem B5548301 : Blo 1024605 5548301 := bstep (se 3 (by rfl) ⟨1040306, by rfl⟩ : syracuseStep 5548301 = 2080613) B2080613
theorem B2337041 : Blo 1024605 2337041 := bstep (se 2 (by rfl) ⟨876390, by rfl⟩ : syracuseStep 2337041 = 1752781) B1752781
theorem B1026323 : Blo 1024605 1026323 := bstep (se 1 (by rfl) ⟨769742, by rfl⟩ : syracuseStep 1026323 = 1539485) B1539485
theorem B1026339 : Blo 1024605 1026339 := bstep (se 1 (by rfl) ⟨769754, by rfl⟩ : syracuseStep 1026339 = 1539509) B1539509
theorem B1026355 : Blo 1024605 1026355 := bstep (se 1 (by rfl) ⟨769766, by rfl⟩ : syracuseStep 1026355 = 1539533) B1539533
theorem B1026371 : Blo 1024605 1026371 := bstep (se 1 (by rfl) ⟨769778, by rfl⟩ : syracuseStep 1026371 = 1539557) B1539557
theorem B2926925 : Blo 1024605 2926925 := bstep (se 3 (by rfl) ⟨548798, by rfl⟩ : syracuseStep 2926925 = 1097597) B1097597
theorem B2599249 : Blo 1024605 2599249 := bstep (se 2 (by rfl) ⟨974718, by rfl⟩ : syracuseStep 2599249 = 1949437) B1949437
theorem B1026387 : Blo 1024605 1026387 := bstep (se 1 (by rfl) ⟨769790, by rfl⟩ : syracuseStep 1026387 = 1539581) B1539581
theorem B5843299 : Blo 1024605 5843299 := bstep (se 1 (by rfl) ⟨4382474, by rfl⟩ : syracuseStep 5843299 = 8764949) B8764949
theorem B3287395 : Blo 1024605 3287395 := bstep (se 1 (by rfl) ⟨2465546, by rfl⟩ : syracuseStep 3287395 = 4931093) B4931093
theorem B1026403 : Blo 1024605 1026403 := bstep (se 1 (by rfl) ⟨769802, by rfl⟩ : syracuseStep 1026403 = 1539605) B1539605
theorem B1026419 : Blo 1024605 1026419 := bstep (se 1 (by rfl) ⟨769814, by rfl⟩ : syracuseStep 1026419 = 1539629) B1539629
theorem B1026435 : Blo 1024605 1026435 := bstep (se 1 (by rfl) ⟨769826, by rfl⟩ : syracuseStep 1026435 = 1539653) B1539653
theorem B1026451 : Blo 1024605 1026451 := bstep (se 1 (by rfl) ⟨769838, by rfl⟩ : syracuseStep 1026451 = 1539677) B1539677
theorem B2337187 : Blo 1024605 2337187 := bstep (se 1 (by rfl) ⟨1752890, by rfl⟩ : syracuseStep 2337187 = 3505781) B3505781
theorem B1026467 : Blo 1024605 1026467 := bstep (se 1 (by rfl) ⟨769850, by rfl⟩ : syracuseStep 1026467 = 1539701) B1539701
theorem B1026483 : Blo 1024605 1026483 := bstep (se 1 (by rfl) ⟨769862, by rfl⟩ : syracuseStep 1026483 = 1539725) B1539725
theorem B1026499 : Blo 1024605 1026499 := bstep (se 1 (by rfl) ⟨769874, by rfl⟩ : syracuseStep 1026499 = 1539749) B1539749
theorem B1026515 : Blo 1024605 1026515 := bstep (se 1 (by rfl) ⟨769886, by rfl⟩ : syracuseStep 1026515 = 1539773) B1539773
theorem B1780193 : Blo 1024605 1780193 := bstep (se 2 (by rfl) ⟨667572, by rfl⟩ : syracuseStep 1780193 = 1335145) B1335145
theorem B1026531 : Blo 1024605 1026531 := bstep (se 1 (by rfl) ⟨769898, by rfl⟩ : syracuseStep 1026531 = 1539797) B1539797
theorem B1026547 : Blo 1024605 1026547 := bstep (se 1 (by rfl) ⟨769910, by rfl⟩ : syracuseStep 1026547 = 1539821) B1539821
theorem B1026563 : Blo 1024605 1026563 := bstep (se 1 (by rfl) ⟨769922, by rfl⟩ : syracuseStep 1026563 = 1539845) B1539845
theorem B2927117 : Blo 1024605 2927117 := bstep (se 3 (by rfl) ⟨548834, by rfl⟩ : syracuseStep 2927117 = 1097669) B1097669
theorem B1026579 : Blo 1024605 1026579 := bstep (se 1 (by rfl) ⟨769934, by rfl⟩ : syracuseStep 1026579 = 1539869) B1539869
theorem B1026595 : Blo 1024605 1026595 := bstep (se 1 (by rfl) ⟨769946, by rfl⟩ : syracuseStep 1026595 = 1539893) B1539893
theorem B1026611 : Blo 1024605 1026611 := bstep (se 1 (by rfl) ⟨769958, by rfl⟩ : syracuseStep 1026611 = 1539917) B1539917
theorem B1026627 : Blo 1024605 1026627 := bstep (se 1 (by rfl) ⟨769970, by rfl⟩ : syracuseStep 1026627 = 1539941) B1539941
theorem B1026643 : Blo 1024605 1026643 := bstep (se 1 (by rfl) ⟨769982, by rfl⟩ : syracuseStep 1026643 = 1539965) B1539965
theorem B1026659 : Blo 1024605 1026659 := bstep (se 1 (by rfl) ⟨769994, by rfl⟩ : syracuseStep 1026659 = 1539989) B1539989
theorem B2599523 : Blo 1024605 2599523 := bstep (se 1 (by rfl) ⟨1949642, by rfl⟩ : syracuseStep 2599523 = 3899285) B3899285
theorem B1026675 : Blo 1024605 1026675 := bstep (se 1 (by rfl) ⟨770006, by rfl⟩ : syracuseStep 1026675 = 1540013) B1540013
theorem B1026691 : Blo 1024605 1026691 := bstep (se 1 (by rfl) ⟨770018, by rfl⟩ : syracuseStep 1026691 = 1540037) B1540037
theorem B1026707 : Blo 1024605 1026707 := bstep (se 1 (by rfl) ⟨770030, by rfl⟩ : syracuseStep 1026707 = 1540061) B1540061
theorem B1026723 : Blo 1024605 1026723 := bstep (se 1 (by rfl) ⟨770042, by rfl⟩ : syracuseStep 1026723 = 1540085) B1540085
theorem B3287729 : Blo 1024605 3287729 := bstep (se 2 (by rfl) ⟨1232898, by rfl⟩ : syracuseStep 3287729 = 2465797) B2465797
theorem B1026739 : Blo 1024605 1026739 := bstep (se 1 (by rfl) ⟨770054, by rfl⟩ : syracuseStep 1026739 = 1540109) B1540109
theorem B1026755 : Blo 1024605 1026755 := bstep (se 1 (by rfl) ⟨770066, by rfl⟩ : syracuseStep 1026755 = 1540133) B1540133
theorem B1026771 : Blo 1024605 1026771 := bstep (se 1 (by rfl) ⟨770078, by rfl⟩ : syracuseStep 1026771 = 1540157) B1540157
theorem B1026787 : Blo 1024605 1026787 := bstep (se 1 (by rfl) ⟨770090, by rfl⟩ : syracuseStep 1026787 = 1540181) B1540181
theorem B1026803 : Blo 1024605 1026803 := bstep (se 1 (by rfl) ⟨770102, by rfl⟩ : syracuseStep 1026803 = 1540205) B1540205
theorem B1026819 : Blo 1024605 1026819 := bstep (se 1 (by rfl) ⟨770114, by rfl⟩ : syracuseStep 1026819 = 1540229) B1540229
theorem B11709197 : Blo 1024605 11709197 := bstep (se 3 (by rfl) ⟨2195474, by rfl⟩ : syracuseStep 11709197 = 4390949) B4390949
theorem B1026835 : Blo 1024605 1026835 := bstep (se 1 (by rfl) ⟨770126, by rfl⟩ : syracuseStep 1026835 = 1540253) B1540253
theorem B1026851 : Blo 1024605 1026851 := bstep (se 1 (by rfl) ⟨770138, by rfl⟩ : syracuseStep 1026851 = 1540277) B1540277
theorem B2599715 : Blo 1024605 2599715 := bstep (se 1 (by rfl) ⟨1949786, by rfl⟩ : syracuseStep 2599715 = 3899573) B3899573
theorem B1878833 : Blo 1024605 1878833 := bstep (se 2 (by rfl) ⟨704562, by rfl⟩ : syracuseStep 1878833 = 1409125) B1409125
theorem B1026867 : Blo 1024605 1026867 := bstep (se 1 (by rfl) ⟨770150, by rfl⟩ : syracuseStep 1026867 = 1540301) B1540301
theorem B1026883 : Blo 1024605 1026883 := bstep (se 1 (by rfl) ⟨770162, by rfl⟩ : syracuseStep 1026883 = 1540325) B1540325
theorem B1026899 : Blo 1024605 1026899 := bstep (se 1 (by rfl) ⟨770174, by rfl⟩ : syracuseStep 1026899 = 1540349) B1540349
theorem B1026915 : Blo 1024605 1026915 := bstep (se 1 (by rfl) ⟨770186, by rfl⟩ : syracuseStep 1026915 = 1540373) B1540373
theorem B5843825 : Blo 1024605 5843825 := bstep (se 2 (by rfl) ⟨2191434, by rfl⟩ : syracuseStep 5843825 = 4382869) B4382869
theorem B1026931 : Blo 1024605 1026931 := bstep (se 1 (by rfl) ⟨770198, by rfl⟩ : syracuseStep 1026931 = 1540397) B1540397
theorem B1026947 : Blo 1024605 1026947 := bstep (se 1 (by rfl) ⟨770210, by rfl⟩ : syracuseStep 1026947 = 1540421) B1540421
theorem B1026963 : Blo 1024605 1026963 := bstep (se 1 (by rfl) ⟨770222, by rfl⟩ : syracuseStep 1026963 = 1540445) B1540445
theorem B1026979 : Blo 1024605 1026979 := bstep (se 1 (by rfl) ⟨770234, by rfl⟩ : syracuseStep 1026979 = 1540469) B1540469
theorem B1026995 : Blo 1024605 1026995 := bstep (se 1 (by rfl) ⟨770246, by rfl⟩ : syracuseStep 1026995 = 1540493) B1540493
theorem B1027011 : Blo 1024605 1027011 := bstep (se 1 (by rfl) ⟨770258, by rfl⟩ : syracuseStep 1027011 = 1540517) B1540517
theorem B1027027 : Blo 1024605 1027027 := bstep (se 1 (by rfl) ⟨770270, by rfl⟩ : syracuseStep 1027027 = 1540541) B1540541
theorem B1027043 : Blo 1024605 1027043 := bstep (se 1 (by rfl) ⟨770282, by rfl⟩ : syracuseStep 1027043 = 1540565) B1540565
theorem B7810019 : Blo 1024605 7810019 := bstep (se 1 (by rfl) ⟨5857514, by rfl⟩ : syracuseStep 7810019 = 11715029) B11715029
theorem B1027059 : Blo 1024605 1027059 := bstep (se 1 (by rfl) ⟨770294, by rfl⟩ : syracuseStep 1027059 = 1540589) B1540589
theorem B1027075 : Blo 1024605 1027075 := bstep (se 1 (by rfl) ⟨770306, by rfl⟩ : syracuseStep 1027075 = 1540613) B1540613
theorem B1027091 : Blo 1024605 1027091 := bstep (se 1 (by rfl) ⟨770318, by rfl⟩ : syracuseStep 1027091 = 1540637) B1540637
theorem B1027107 : Blo 1024605 1027107 := bstep (se 1 (by rfl) ⟨770330, by rfl⟩ : syracuseStep 1027107 = 1540661) B1540661
theorem B1027123 : Blo 1024605 1027123 := bstep (se 1 (by rfl) ⟨770342, by rfl⟩ : syracuseStep 1027123 = 1540685) B1540685
theorem B1027139 : Blo 1024605 1027139 := bstep (se 1 (by rfl) ⟨770354, by rfl⟩ : syracuseStep 1027139 = 1540709) B1540709
theorem B1027155 : Blo 1024605 1027155 := bstep (se 1 (by rfl) ⟨770366, by rfl⟩ : syracuseStep 1027155 = 1540733) B1540733
theorem B1027171 : Blo 1024605 1027171 := bstep (se 1 (by rfl) ⟨770378, by rfl⟩ : syracuseStep 1027171 = 1540757) B1540757
theorem B1387633 : Blo 1024605 1387633 := bstep (se 2 (by rfl) ⟨520362, by rfl⟩ : syracuseStep 1387633 = 1040725) B1040725
theorem B1027187 : Blo 1024605 1027187 := bstep (se 1 (by rfl) ⟨770390, by rfl⟩ : syracuseStep 1027187 = 1540781) B1540781
theorem B1387649 : Blo 1024605 1387649 := bstep (se 2 (by rfl) ⟨520368, by rfl⟩ : syracuseStep 1387649 = 1040737) B1040737
theorem B1027203 : Blo 1024605 1027203 := bstep (se 1 (by rfl) ⟨770402, by rfl⟩ : syracuseStep 1027203 = 1540805) B1540805
theorem B1027219 : Blo 1024605 1027219 := bstep (se 1 (by rfl) ⟨770414, by rfl⟩ : syracuseStep 1027219 = 1540829) B1540829
theorem B1027235 : Blo 1024605 1027235 := bstep (se 1 (by rfl) ⟨770426, by rfl⟩ : syracuseStep 1027235 = 1540853) B1540853
theorem B1027251 : Blo 1024605 1027251 := bstep (se 1 (by rfl) ⟨770438, by rfl⟩ : syracuseStep 1027251 = 1540877) B1540877
theorem B1027267 : Blo 1024605 1027267 := bstep (se 1 (by rfl) ⟨770450, by rfl⟩ : syracuseStep 1027267 = 1540901) B1540901
theorem B1027283 : Blo 1024605 1027283 := bstep (se 1 (by rfl) ⟨770462, by rfl⟩ : syracuseStep 1027283 = 1540925) B1540925
theorem B1027299 : Blo 1024605 1027299 := bstep (se 1 (by rfl) ⟨770474, by rfl⟩ : syracuseStep 1027299 = 1540949) B1540949
theorem B1027315 : Blo 1024605 1027315 := bstep (se 1 (by rfl) ⟨770486, by rfl⟩ : syracuseStep 1027315 = 1540973) B1540973
theorem B1027331 : Blo 1024605 1027331 := bstep (se 1 (by rfl) ⟨770498, by rfl⟩ : syracuseStep 1027331 = 1540997) B1540997
theorem B1027347 : Blo 1024605 1027347 := bstep (se 1 (by rfl) ⟨770510, by rfl⟩ : syracuseStep 1027347 = 1541021) B1541021
theorem B1387811 : Blo 1024605 1387811 := bstep (se 1 (by rfl) ⟨1040858, by rfl⟩ : syracuseStep 1387811 = 2081717) B2081717
theorem B1027363 : Blo 1024605 1027363 := bstep (se 1 (by rfl) ⟨770522, by rfl⟩ : syracuseStep 1027363 = 1541045) B1541045
theorem B1027379 : Blo 1024605 1027379 := bstep (se 1 (by rfl) ⟨770534, by rfl⟩ : syracuseStep 1027379 = 1541069) B1541069
theorem B1027395 : Blo 1024605 1027395 := bstep (se 1 (by rfl) ⟨770546, by rfl⟩ : syracuseStep 1027395 = 1541093) B1541093
theorem B1027411 : Blo 1024605 1027411 := bstep (se 1 (by rfl) ⟨770558, by rfl⟩ : syracuseStep 1027411 = 1541117) B1541117
theorem B1027427 : Blo 1024605 1027427 := bstep (se 1 (by rfl) ⟨770570, by rfl⟩ : syracuseStep 1027427 = 1541141) B1541141
theorem B1027443 : Blo 1024605 1027443 := bstep (se 1 (by rfl) ⟨770582, by rfl⟩ : syracuseStep 1027443 = 1541165) B1541165
theorem B1027459 : Blo 1024605 1027459 := bstep (se 1 (by rfl) ⟨770594, by rfl⟩ : syracuseStep 1027459 = 1541189) B1541189
theorem B1027475 : Blo 1024605 1027475 := bstep (se 1 (by rfl) ⟨770606, by rfl⟩ : syracuseStep 1027475 = 1541213) B1541213
theorem B6565283 : Blo 1024605 6565283 := bstep (se 1 (by rfl) ⟨4923962, by rfl⟩ : syracuseStep 6565283 = 9847925) B9847925
theorem B1027491 : Blo 1024605 1027491 := bstep (se 1 (by rfl) ⟨770618, by rfl⟩ : syracuseStep 1027491 = 1541237) B1541237
theorem B2305457 : Blo 1024605 2305457 := bstep (se 2 (by rfl) ⟨864546, by rfl⟩ : syracuseStep 2305457 = 1729093) B1729093
theorem B1027507 : Blo 1024605 1027507 := bstep (se 1 (by rfl) ⟨770630, by rfl⟩ : syracuseStep 1027507 = 1541261) B1541261
theorem B2305475 : Blo 1024605 2305475 := bstep (se 1 (by rfl) ⟨1729106, by rfl⟩ : syracuseStep 2305475 = 3458213) B3458213
theorem B1027523 : Blo 1024605 1027523 := bstep (se 1 (by rfl) ⟨770642, by rfl⟩ : syracuseStep 1027523 = 1541285) B1541285
theorem B1027539 : Blo 1024605 1027539 := bstep (se 1 (by rfl) ⟨770654, by rfl⟩ : syracuseStep 1027539 = 1541309) B1541309
theorem B1027555 : Blo 1024605 1027555 := bstep (se 1 (by rfl) ⟨770666, by rfl⟩ : syracuseStep 1027555 = 1541333) B1541333
theorem B2928109 : Blo 1024605 2928109 := bstep (se 3 (by rfl) ⟨549020, by rfl⟩ : syracuseStep 2928109 = 1098041) B1098041
theorem B1027571 : Blo 1024605 1027571 := bstep (se 1 (by rfl) ⟨770678, by rfl⟩ : syracuseStep 1027571 = 1541357) B1541357
theorem B1027587 : Blo 1024605 1027587 := bstep (se 1 (by rfl) ⟨770690, by rfl⟩ : syracuseStep 1027587 = 1541381) B1541381
theorem B1027603 : Blo 1024605 1027603 := bstep (se 1 (by rfl) ⟨770702, by rfl⟩ : syracuseStep 1027603 = 1541405) B1541405
theorem B1027619 : Blo 1024605 1027619 := bstep (se 1 (by rfl) ⟨770714, by rfl⟩ : syracuseStep 1027619 = 1541429) B1541429
theorem B3517987 : Blo 1024605 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B1027635 : Blo 1024605 1027635 := bstep (se 1 (by rfl) ⟨770726, by rfl⟩ : syracuseStep 1027635 = 1541453) B1541453
theorem B1027651 : Blo 1024605 1027651 := bstep (se 1 (by rfl) ⟨770738, by rfl⟩ : syracuseStep 1027651 = 1541477) B1541477
theorem B1027667 : Blo 1024605 1027667 := bstep (se 1 (by rfl) ⟨770750, by rfl⟩ : syracuseStep 1027667 = 1541501) B1541501
theorem B1027683 : Blo 1024605 1027683 := bstep (se 1 (by rfl) ⟨770762, by rfl⟩ : syracuseStep 1027683 = 1541525) B1541525
theorem B1027699 : Blo 1024605 1027699 := bstep (se 1 (by rfl) ⟨770774, by rfl⟩ : syracuseStep 1027699 = 1541549) B1541549
theorem B1027715 : Blo 1024605 1027715 := bstep (se 1 (by rfl) ⟨770786, by rfl⟩ : syracuseStep 1027715 = 1541573) B1541573
theorem B1027731 : Blo 1024605 1027731 := bstep (se 1 (by rfl) ⟨770798, by rfl⟩ : syracuseStep 1027731 = 1541597) B1541597
theorem B1027747 : Blo 1024605 1027747 := bstep (se 1 (by rfl) ⟨770810, by rfl⟩ : syracuseStep 1027747 = 1541621) B1541621
theorem B1027763 : Blo 1024605 1027763 := bstep (se 1 (by rfl) ⟨770822, by rfl⟩ : syracuseStep 1027763 = 1541645) B1541645
theorem B1027779 : Blo 1024605 1027779 := bstep (se 1 (by rfl) ⟨770834, by rfl⟩ : syracuseStep 1027779 = 1541669) B1541669
theorem B2305745 : Blo 1024605 2305745 := bstep (se 2 (by rfl) ⟨864654, by rfl⟩ : syracuseStep 2305745 = 1729309) B1729309
theorem B2600657 : Blo 1024605 2600657 := bstep (se 2 (by rfl) ⟨975246, by rfl⟩ : syracuseStep 2600657 = 1950493) B1950493
theorem B1027795 : Blo 1024605 1027795 := bstep (se 1 (by rfl) ⟨770846, by rfl⟩ : syracuseStep 1027795 = 1541693) B1541693
theorem B2305763 : Blo 1024605 2305763 := bstep (se 1 (by rfl) ⟨1729322, by rfl⟩ : syracuseStep 2305763 = 3458645) B3458645
theorem B1027811 : Blo 1024605 1027811 := bstep (se 1 (by rfl) ⟨770858, by rfl⟩ : syracuseStep 1027811 = 1541717) B1541717
theorem B1027827 : Blo 1024605 1027827 := bstep (se 1 (by rfl) ⟨770870, by rfl⟩ : syracuseStep 1027827 = 1541741) B1541741
theorem B2600707 : Blo 1024605 2600707 := bstep (se 1 (by rfl) ⟨1950530, by rfl⟩ : syracuseStep 2600707 = 3901061) B3901061
theorem B1027843 : Blo 1024605 1027843 := bstep (se 1 (by rfl) ⟨770882, by rfl⟩ : syracuseStep 1027843 = 1541765) B1541765
theorem B1027859 : Blo 1024605 1027859 := bstep (se 1 (by rfl) ⟨770894, by rfl⟩ : syracuseStep 1027859 = 1541789) B1541789
theorem B1027875 : Blo 1024605 1027875 := bstep (se 1 (by rfl) ⟨770906, by rfl⟩ : syracuseStep 1027875 = 1541813) B1541813
theorem B1027891 : Blo 1024605 1027891 := bstep (se 1 (by rfl) ⟨770918, by rfl⟩ : syracuseStep 1027891 = 1541837) B1541837
theorem B1027907 : Blo 1024605 1027907 := bstep (se 1 (by rfl) ⟨770930, by rfl⟩ : syracuseStep 1027907 = 1541861) B1541861
theorem B1027923 : Blo 1024605 1027923 := bstep (se 1 (by rfl) ⟨770942, by rfl⟩ : syracuseStep 1027923 = 1541885) B1541885
theorem B1027939 : Blo 1024605 1027939 := bstep (se 1 (by rfl) ⟨770954, by rfl⟩ : syracuseStep 1027939 = 1541909) B1541909
theorem B1027955 : Blo 1024605 1027955 := bstep (se 1 (by rfl) ⟨770966, by rfl⟩ : syracuseStep 1027955 = 1541933) B1541933
theorem B1027971 : Blo 1024605 1027971 := bstep (se 1 (by rfl) ⟨770978, by rfl⟩ : syracuseStep 1027971 = 1541957) B1541957
theorem B2600849 : Blo 1024605 2600849 := bstep (se 2 (by rfl) ⟨975318, by rfl⟩ : syracuseStep 2600849 = 1950637) B1950637
theorem B1027987 : Blo 1024605 1027987 := bstep (se 1 (by rfl) ⟨770990, by rfl⟩ : syracuseStep 1027987 = 1541981) B1541981
theorem B3125155 : Blo 1024605 3125155 := bstep (se 1 (by rfl) ⟨2343866, by rfl⟩ : syracuseStep 3125155 = 4687733) B4687733
theorem B1028003 : Blo 1024605 1028003 := bstep (se 1 (by rfl) ⟨771002, by rfl⟩ : syracuseStep 1028003 = 1542005) B1542005
theorem B1028019 : Blo 1024605 1028019 := bstep (se 1 (by rfl) ⟨771014, by rfl⟩ : syracuseStep 1028019 = 1542029) B1542029
theorem B1028035 : Blo 1024605 1028035 := bstep (se 1 (by rfl) ⟨771026, by rfl⟩ : syracuseStep 1028035 = 1542053) B1542053
theorem B1028051 : Blo 1024605 1028051 := bstep (se 1 (by rfl) ⟨771038, by rfl⟩ : syracuseStep 1028051 = 1542077) B1542077
theorem B1028067 : Blo 1024605 1028067 := bstep (se 1 (by rfl) ⟨771050, by rfl⟩ : syracuseStep 1028067 = 1542101) B1542101
theorem B2306033 : Blo 1024605 2306033 := bstep (se 2 (by rfl) ⟨864762, by rfl⟩ : syracuseStep 2306033 = 1729525) B1729525
theorem B1028083 : Blo 1024605 1028083 := bstep (se 1 (by rfl) ⟨771062, by rfl⟩ : syracuseStep 1028083 = 1542125) B1542125
theorem B2306051 : Blo 1024605 2306051 := bstep (se 1 (by rfl) ⟨1729538, by rfl⟩ : syracuseStep 2306051 = 3459077) B3459077
theorem B1028099 : Blo 1024605 1028099 := bstep (se 1 (by rfl) ⟨771074, by rfl⟩ : syracuseStep 1028099 = 1542149) B1542149
theorem B1028115 : Blo 1024605 1028115 := bstep (se 1 (by rfl) ⟨771086, by rfl⟩ : syracuseStep 1028115 = 1542173) B1542173
theorem B1028131 : Blo 1024605 1028131 := bstep (se 1 (by rfl) ⟨771098, by rfl⟩ : syracuseStep 1028131 = 1542197) B1542197
theorem B1028147 : Blo 1024605 1028147 := bstep (se 1 (by rfl) ⟨771110, by rfl⟩ : syracuseStep 1028147 = 1542221) B1542221
theorem B1028163 : Blo 1024605 1028163 := bstep (se 1 (by rfl) ⟨771122, by rfl⟩ : syracuseStep 1028163 = 1542245) B1542245
theorem B1028179 : Blo 1024605 1028179 := bstep (se 1 (by rfl) ⟨771134, by rfl⟩ : syracuseStep 1028179 = 1542269) B1542269
theorem B1028195 : Blo 1024605 1028195 := bstep (se 1 (by rfl) ⟨771146, by rfl⟩ : syracuseStep 1028195 = 1542293) B1542293
theorem B1028211 : Blo 1024605 1028211 := bstep (se 1 (by rfl) ⟨771158, by rfl⟩ : syracuseStep 1028211 = 1542317) B1542317
theorem B1028227 : Blo 1024605 1028227 := bstep (se 1 (by rfl) ⟨771170, by rfl⟩ : syracuseStep 1028227 = 1542341) B1542341
theorem B1028243 : Blo 1024605 1028243 := bstep (se 1 (by rfl) ⟨771182, by rfl⟩ : syracuseStep 1028243 = 1542365) B1542365
theorem B1028259 : Blo 1024605 1028259 := bstep (se 1 (by rfl) ⟨771194, by rfl⟩ : syracuseStep 1028259 = 1542389) B1542389
theorem B1945777 : Blo 1024605 1945777 := bstep (se 2 (by rfl) ⟨729666, by rfl⟩ : syracuseStep 1945777 = 1459333) B1459333
theorem B1028275 : Blo 1024605 1028275 := bstep (se 1 (by rfl) ⟨771206, by rfl⟩ : syracuseStep 1028275 = 1542413) B1542413
theorem B1028291 : Blo 1024605 1028291 := bstep (se 1 (by rfl) ⟨771218, by rfl⟩ : syracuseStep 1028291 = 1542437) B1542437
theorem B1028307 : Blo 1024605 1028307 := bstep (se 1 (by rfl) ⟨771230, by rfl⟩ : syracuseStep 1028307 = 1542461) B1542461
theorem B1028323 : Blo 1024605 1028323 := bstep (se 1 (by rfl) ⟨771242, by rfl⟩ : syracuseStep 1028323 = 1542485) B1542485
theorem B1028339 : Blo 1024605 1028339 := bstep (se 1 (by rfl) ⟨771254, by rfl⟩ : syracuseStep 1028339 = 1542509) B1542509
theorem B1028355 : Blo 1024605 1028355 := bstep (se 1 (by rfl) ⟨771266, by rfl⟩ : syracuseStep 1028355 = 1542533) B1542533
theorem B2306321 : Blo 1024605 2306321 := bstep (se 2 (by rfl) ⟨864870, by rfl⟩ : syracuseStep 2306321 = 1729741) B1729741
theorem B1028371 : Blo 1024605 1028371 := bstep (se 1 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 1028371 = 1542557) B1542557
theorem B2306339 : Blo 1024605 2306339 := bstep (se 1 (by rfl) ⟨1729754, by rfl⟩ : syracuseStep 2306339 = 3459509) B3459509
theorem B5845283 : Blo 1024605 5845283 := bstep (se 1 (by rfl) ⟨4383962, by rfl⟩ : syracuseStep 5845283 = 8767925) B8767925
theorem B1028387 : Blo 1024605 1028387 := bstep (se 1 (by rfl) ⟨771290, by rfl⟩ : syracuseStep 1028387 = 1542581) B1542581
theorem B1028403 : Blo 1024605 1028403 := bstep (se 1 (by rfl) ⟨771302, by rfl⟩ : syracuseStep 1028403 = 1542605) B1542605
theorem B1028419 : Blo 1024605 1028419 := bstep (se 1 (by rfl) ⟨771314, by rfl⟩ : syracuseStep 1028419 = 1542629) B1542629
theorem B1945937 : Blo 1024605 1945937 := bstep (se 2 (by rfl) ⟨729726, by rfl⟩ : syracuseStep 1945937 = 1459453) B1459453
theorem B1028435 : Blo 1024605 1028435 := bstep (se 1 (by rfl) ⟨771326, by rfl⟩ : syracuseStep 1028435 = 1542653) B1542653
theorem B1028451 : Blo 1024605 1028451 := bstep (se 1 (by rfl) ⟨771338, by rfl⟩ : syracuseStep 1028451 = 1542677) B1542677
theorem B1028467 : Blo 1024605 1028467 := bstep (se 1 (by rfl) ⟨771350, by rfl⟩ : syracuseStep 1028467 = 1542701) B1542701
theorem B1028483 : Blo 1024605 1028483 := bstep (se 1 (by rfl) ⟨771362, by rfl⟩ : syracuseStep 1028483 = 1542725) B1542725
theorem B1028499 : Blo 1024605 1028499 := bstep (se 1 (by rfl) ⟨771374, by rfl⟩ : syracuseStep 1028499 = 1542749) B1542749
theorem B1028515 : Blo 1024605 1028515 := bstep (se 1 (by rfl) ⟨771386, by rfl⟩ : syracuseStep 1028515 = 1542773) B1542773
theorem B1028531 : Blo 1024605 1028531 := bstep (se 1 (by rfl) ⟨771398, by rfl⟩ : syracuseStep 1028531 = 1542797) B1542797
theorem B1028547 : Blo 1024605 1028547 := bstep (se 1 (by rfl) ⟨771410, by rfl⟩ : syracuseStep 1028547 = 1542821) B1542821
theorem B1028563 : Blo 1024605 1028563 := bstep (se 1 (by rfl) ⟨771422, by rfl⟩ : syracuseStep 1028563 = 1542845) B1542845
theorem B1028579 : Blo 1024605 1028579 := bstep (se 1 (by rfl) ⟨771434, by rfl⟩ : syracuseStep 1028579 = 1542869) B1542869
theorem B1028595 : Blo 1024605 1028595 := bstep (se 1 (by rfl) ⟨771446, by rfl⟩ : syracuseStep 1028595 = 1542893) B1542893
theorem B7909901 : Blo 1024605 7909901 := bstep (se 3 (by rfl) ⟨1483106, by rfl⟩ : syracuseStep 7909901 = 2966213) B2966213
theorem B2306609 : Blo 1024605 2306609 := bstep (se 2 (by rfl) ⟨864978, by rfl⟩ : syracuseStep 2306609 = 1729957) B1729957
theorem B2306627 : Blo 1024605 2306627 := bstep (se 1 (by rfl) ⟨1729970, by rfl⟩ : syracuseStep 2306627 = 3459941) B3459941
theorem B3125873 : Blo 1024605 3125873 := bstep (se 2 (by rfl) ⟨1172202, by rfl⟩ : syracuseStep 3125873 = 2344405) B2344405
theorem B20001421 : Blo 1024605 20001421 := bstep (se 3 (by rfl) ⟨3750266, by rfl⟩ : syracuseStep 20001421 = 7500533) B7500533
theorem B1946339 : Blo 1024605 1946339 := bstep (se 1 (by rfl) ⟨1459754, by rfl⟩ : syracuseStep 1946339 = 2919509) B2919509
theorem B1094419 : Blo 1024605 1094419 := bstep (se 1 (by rfl) ⟨820814, by rfl⟩ : syracuseStep 1094419 = 1641629) B1641629
theorem B44970773 : Blo 1024605 44970773 := bstep (se 6 (by rfl) ⟨1054002, by rfl⟩ : syracuseStep 44970773 = 2108005) B2108005
theorem B2306897 : Blo 1024605 2306897 := bstep (se 2 (by rfl) ⟨865086, by rfl⟩ : syracuseStep 2306897 = 1730173) B1730173
theorem B2306915 : Blo 1024605 2306915 := bstep (se 1 (by rfl) ⟨1730186, by rfl⟩ : syracuseStep 2306915 = 3460373) B3460373
theorem B2601841 : Blo 1024605 2601841 := bstep (se 2 (by rfl) ⟨975690, by rfl⟩ : syracuseStep 2601841 = 1951381) B1951381
theorem B2339779 : Blo 1024605 2339779 := bstep (se 1 (by rfl) ⟨1754834, by rfl⟩ : syracuseStep 2339779 = 3509669) B3509669
theorem B5190641 : Blo 1024605 5190641 := bstep (se 2 (by rfl) ⟨1946490, by rfl⟩ : syracuseStep 5190641 = 3892981) B3892981
theorem B2307185 : Blo 1024605 2307185 := bstep (se 2 (by rfl) ⟨865194, by rfl⟩ : syracuseStep 2307185 = 1730389) B1730389
theorem B2307203 : Blo 1024605 2307203 := bstep (se 1 (by rfl) ⟨1730402, by rfl⟩ : syracuseStep 2307203 = 3460805) B3460805
theorem B2602115 : Blo 1024605 2602115 := bstep (se 1 (by rfl) ⟨1951586, by rfl⟩ : syracuseStep 2602115 = 3903173) B3903173
theorem B4437283 : Blo 1024605 4437283 := bstep (se 1 (by rfl) ⟨3327962, by rfl⟩ : syracuseStep 4437283 = 6655925) B6655925
theorem B2077987 : Blo 1024605 2077987 := bstep (se 1 (by rfl) ⟨1558490, by rfl⟩ : syracuseStep 2077987 = 3116981) B3116981
theorem B2602307 : Blo 1024605 2602307 := bstep (se 1 (by rfl) ⟨1951730, by rfl⟩ : syracuseStep 2602307 = 3903461) B3903461
theorem B2078083 : Blo 1024605 2078083 := bstep (se 1 (by rfl) ⟨1558562, by rfl⟩ : syracuseStep 2078083 = 3117125) B3117125
theorem B2307473 : Blo 1024605 2307473 := bstep (se 2 (by rfl) ⟨865302, by rfl⟩ : syracuseStep 2307473 = 1730605) B1730605
theorem B2307491 : Blo 1024605 2307491 := bstep (se 1 (by rfl) ⟨1730618, by rfl⟩ : syracuseStep 2307491 = 3461237) B3461237
theorem B3290701 : Blo 1024605 3290701 := bstep (se 3 (by rfl) ⟨617006, by rfl⟩ : syracuseStep 3290701 = 1234013) B1234013
theorem B1947235 : Blo 1024605 1947235 := bstep (se 1 (by rfl) ⟨1460426, by rfl⟩ : syracuseStep 1947235 = 2920853) B2920853
theorem B11712113 : Blo 1024605 11712113 := bstep (se 2 (by rfl) ⟨4392042, by rfl⟩ : syracuseStep 11712113 = 8784085) B8784085
theorem B2307761 : Blo 1024605 2307761 := bstep (se 2 (by rfl) ⟨865410, by rfl⟩ : syracuseStep 2307761 = 1730821) B1730821
theorem B2307779 : Blo 1024605 2307779 := bstep (se 1 (by rfl) ⟨1730834, by rfl⟩ : syracuseStep 2307779 = 3461669) B3461669
theorem B1947395 : Blo 1024605 1947395 := bstep (se 1 (by rfl) ⟨1460546, by rfl⟩ : syracuseStep 1947395 = 2921093) B2921093
theorem B2078531 : Blo 1024605 2078531 := bstep (se 1 (by rfl) ⟨1558898, by rfl⟩ : syracuseStep 2078531 = 3117797) B3117797
theorem B1095491 : Blo 1024605 1095491 := bstep (se 1 (by rfl) ⟨821618, by rfl⟩ : syracuseStep 1095491 = 1643237) B1643237
theorem B3290957 : Blo 1024605 3290957 := bstep (se 3 (by rfl) ⟨617054, by rfl⟩ : syracuseStep 3290957 = 1234109) B1234109
theorem B2308049 : Blo 1024605 2308049 := bstep (se 2 (by rfl) ⟨865518, by rfl⟩ : syracuseStep 2308049 = 1731037) B1731037
theorem B2308067 : Blo 1024605 2308067 := bstep (se 1 (by rfl) ⟨1731050, by rfl⟩ : syracuseStep 2308067 = 3462101) B3462101
theorem B5847173 : Blo 1024605 5847173 := bstep (se 4 (by rfl) ⟨548172, by rfl⟩ : syracuseStep 5847173 = 1096345) B1096345
theorem B2308337 : Blo 1024605 2308337 := bstep (se 2 (by rfl) ⟨865626, by rfl⟩ : syracuseStep 2308337 = 1731253) B1731253
theorem B2603249 : Blo 1024605 2603249 := bstep (se 2 (by rfl) ⟨976218, by rfl⟩ : syracuseStep 2603249 = 1952437) B1952437
theorem B2308355 : Blo 1024605 2308355 := bstep (se 1 (by rfl) ⟨1731266, by rfl⟩ : syracuseStep 2308355 = 3462533) B3462533
theorem B2603299 : Blo 1024605 2603299 := bstep (se 1 (by rfl) ⟨1952474, by rfl⟩ : syracuseStep 2603299 = 3904949) B3904949
theorem B5192099 : Blo 1024605 5192099 := bstep (se 1 (by rfl) ⟨3894074, by rfl⟩ : syracuseStep 5192099 = 7788149) B7788149
theorem B2603441 : Blo 1024605 2603441 := bstep (se 2 (by rfl) ⟨976290, by rfl⟩ : syracuseStep 2603441 = 1952581) B1952581
theorem B2308625 : Blo 1024605 2308625 := bstep (se 2 (by rfl) ⟨865734, by rfl⟩ : syracuseStep 2308625 = 1731469) B1731469
theorem B2308643 : Blo 1024605 2308643 := bstep (se 1 (by rfl) ⟨1731482, by rfl⟩ : syracuseStep 2308643 = 3462965) B3462965
theorem B94878485 : Blo 1024605 94878485 := bstep (se 6 (by rfl) ⟨2223714, by rfl⟩ : syracuseStep 94878485 = 4447429) B4447429
theorem B2308913 : Blo 1024605 2308913 := bstep (se 2 (by rfl) ⟨865842, by rfl⟩ : syracuseStep 2308913 = 1731685) B1731685
theorem B1948465 : Blo 1024605 1948465 := bstep (se 2 (by rfl) ⟨730674, by rfl⟩ : syracuseStep 1948465 = 1461349) B1461349
theorem B2308931 : Blo 1024605 2308931 := bstep (se 1 (by rfl) ⟨1731698, by rfl⟩ : syracuseStep 2308931 = 3463397) B3463397
theorem B1096627 : Blo 1024605 1096627 := bstep (se 1 (by rfl) ⟨822470, by rfl⟩ : syracuseStep 1096627 = 1644941) B1644941
theorem B2309201 : Blo 1024605 2309201 := bstep (se 2 (by rfl) ⟨865950, by rfl⟩ : syracuseStep 2309201 = 1731901) B1731901
theorem B2309219 : Blo 1024605 2309219 := bstep (se 1 (by rfl) ⟨1731914, by rfl⟩ : syracuseStep 2309219 = 3463829) B3463829
theorem B5192909 : Blo 1024605 5192909 := bstep (se 3 (by rfl) ⟨973670, by rfl⟩ : syracuseStep 5192909 = 1947341) B1947341
theorem B6569201 : Blo 1024605 6569201 := bstep (se 2 (by rfl) ⟨2463450, by rfl⟩ : syracuseStep 6569201 = 4926901) B4926901
theorem B3292483 : Blo 1024605 3292483 := bstep (se 1 (by rfl) ⟨2469362, by rfl⟩ : syracuseStep 3292483 = 4938725) B4938725
theorem B2342243 : Blo 1024605 2342243 := bstep (se 1 (by rfl) ⟨1756682, by rfl⟩ : syracuseStep 2342243 = 3513365) B3513365
theorem B2309489 : Blo 1024605 2309489 := bstep (se 2 (by rfl) ⟨866058, by rfl⟩ : syracuseStep 2309489 = 1732117) B1732117
theorem B2309507 : Blo 1024605 2309507 := bstep (se 1 (by rfl) ⟨1732130, by rfl⟩ : syracuseStep 2309507 = 3464261) B3464261
theorem B2309777 : Blo 1024605 2309777 := bstep (se 2 (by rfl) ⟨866166, by rfl⟩ : syracuseStep 2309777 = 1732333) B1732333
theorem B2309795 : Blo 1024605 2309795 := bstep (se 1 (by rfl) ⟨1732346, by rfl⟩ : syracuseStep 2309795 = 3464693) B3464693
theorem B1851121 : Blo 1024605 1851121 := bstep (se 2 (by rfl) ⟨694170, by rfl⟩ : syracuseStep 1851121 = 1388341) B1388341
theorem B1097507 : Blo 1024605 1097507 := bstep (se 1 (by rfl) ⟨823130, by rfl⟩ : syracuseStep 1097507 = 1646261) B1646261
theorem B1949521 : Blo 1024605 1949521 := bstep (se 2 (by rfl) ⟨731070, by rfl⟩ : syracuseStep 1949521 = 1462141) B1462141
theorem B6569869 : Blo 1024605 6569869 := bstep (se 3 (by rfl) ⟨1231850, by rfl⟩ : syracuseStep 6569869 = 2463701) B2463701
theorem B1097635 : Blo 1024605 1097635 := bstep (se 1 (by rfl) ⟨823226, by rfl⟩ : syracuseStep 1097635 = 1646453) B1646453
theorem B2310065 : Blo 1024605 2310065 := bstep (se 2 (by rfl) ⟨866274, by rfl⟩ : syracuseStep 2310065 = 1732549) B1732549
theorem B2310083 : Blo 1024605 2310083 := bstep (se 1 (by rfl) ⟨1732562, by rfl⟩ : syracuseStep 2310083 = 3465125) B3465125
theorem B3293315 : Blo 1024605 3293315 := bstep (se 1 (by rfl) ⟨2469986, by rfl⟩ : syracuseStep 3293315 = 4939973) B4939973
theorem B2310353 : Blo 1024605 2310353 := bstep (se 2 (by rfl) ⟨866382, by rfl⟩ : syracuseStep 2310353 = 1732765) B1732765
theorem B2310371 : Blo 1024605 2310371 := bstep (se 1 (by rfl) ⟨1732778, by rfl⟩ : syracuseStep 2310371 = 3465557) B3465557
theorem B1949923 : Blo 1024605 1949923 := bstep (se 1 (by rfl) ⟨1462442, by rfl⟩ : syracuseStep 1949923 = 2924885) B2924885
theorem B1949969 : Blo 1024605 1949969 := bstep (se 2 (by rfl) ⟨731238, by rfl⟩ : syracuseStep 1949969 = 1462477) B1462477
theorem B2965997 : Blo 1024605 2965997 := bstep (se 3 (by rfl) ⟨556124, by rfl⟩ : syracuseStep 2965997 = 1112249) B1112249
theorem B2310641 : Blo 1024605 2310641 := bstep (se 2 (by rfl) ⟨866490, by rfl⟩ : syracuseStep 2310641 = 1732981) B1732981
theorem B2310659 : Blo 1024605 2310659 := bstep (se 1 (by rfl) ⟨1732994, by rfl⟩ : syracuseStep 2310659 = 3465989) B3465989
theorem B3293713 : Blo 1024605 3293713 := bstep (se 2 (by rfl) ⟨1235142, by rfl⟩ : syracuseStep 3293713 = 2470285) B2470285
theorem B1950257 : Blo 1024605 1950257 := bstep (se 2 (by rfl) ⟨731346, by rfl⟩ : syracuseStep 1950257 = 1462693) B1462693
theorem B3293777 : Blo 1024605 3293777 := bstep (se 2 (by rfl) ⟨1235166, by rfl⟩ : syracuseStep 3293777 = 2470333) B2470333
theorem B7914181 : Blo 1024605 7914181 := bstep (se 4 (by rfl) ⟨741954, by rfl⟩ : syracuseStep 7914181 = 1483909) B1483909
theorem B4440781 : Blo 1024605 4440781 := bstep (se 3 (by rfl) ⟨832646, by rfl⟩ : syracuseStep 4440781 = 1665293) B1665293
theorem B4932323 : Blo 1024605 4932323 := bstep (se 1 (by rfl) ⟨3699242, by rfl⟩ : syracuseStep 4932323 = 7398485) B7398485
theorem B2081521 : Blo 1024605 2081521 := bstep (se 2 (by rfl) ⟨780570, by rfl⟩ : syracuseStep 2081521 = 1561141) B1561141
theorem B2310929 : Blo 1024605 2310929 := bstep (se 2 (by rfl) ⟨866598, by rfl⟩ : syracuseStep 2310929 = 1733197) B1733197
theorem B2310947 : Blo 1024605 2310947 := bstep (se 1 (by rfl) ⟨1733210, by rfl⟩ : syracuseStep 2310947 = 3466421) B3466421
theorem B2081603 : Blo 1024605 2081603 := bstep (se 1 (by rfl) ⟨1561202, by rfl⟩ : syracuseStep 2081603 = 3122405) B3122405
theorem B9847651 : Blo 1024605 9847651 := bstep (se 1 (by rfl) ⟨7385738, by rfl⟩ : syracuseStep 9847651 = 14771477) B14771477
theorem B1459139 : Blo 1024605 1459139 := bstep (se 1 (by rfl) ⟨1094354, by rfl⟩ : syracuseStep 1459139 = 2188709) B2188709
theorem B3458051 : Blo 1024605 3458051 := bstep (se 1 (by rfl) ⟨2593538, by rfl⟩ : syracuseStep 3458051 = 5187077) B5187077
theorem B2311217 : Blo 1024605 2311217 := bstep (se 2 (by rfl) ⟨866706, by rfl⟩ : syracuseStep 2311217 = 1733413) B1733413
theorem B2311235 : Blo 1024605 2311235 := bstep (se 1 (by rfl) ⟨1733426, by rfl⟩ : syracuseStep 2311235 = 3466853) B3466853
theorem B1950979 : Blo 1024605 1950979 := bstep (se 1 (by rfl) ⟨1463234, by rfl⟩ : syracuseStep 1950979 = 2926469) B2926469
theorem B3458321 : Blo 1024605 3458321 := bstep (se 2 (by rfl) ⟨1296870, by rfl⟩ : syracuseStep 3458321 = 2593741) B2593741
theorem B1852721 : Blo 1024605 1852721 := bstep (se 2 (by rfl) ⟨694770, by rfl⟩ : syracuseStep 1852721 = 1389541) B1389541
theorem B2311505 : Blo 1024605 2311505 := bstep (se 2 (by rfl) ⟨866814, by rfl⟩ : syracuseStep 2311505 = 1733629) B1733629
theorem B2311523 : Blo 1024605 2311523 := bstep (se 1 (by rfl) ⟨1733642, by rfl⟩ : syracuseStep 2311523 = 3467285) B3467285
theorem B1754561 : Blo 1024605 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B1459777 : Blo 1024605 1459777 := bstep (se 2 (by rfl) ⟨547416, by rfl⟩ : syracuseStep 1459777 = 1094833) B1094833
theorem B2311793 : Blo 1024605 2311793 := bstep (se 2 (by rfl) ⟨866922, by rfl⟩ : syracuseStep 2311793 = 1733845) B1733845
theorem B2311811 : Blo 1024605 2311811 := bstep (se 1 (by rfl) ⟨1733858, by rfl⟩ : syracuseStep 2311811 = 3467717) B3467717
theorem B1459891 : Blo 1024605 1459891 := bstep (se 1 (by rfl) ⟨1094918, by rfl⟩ : syracuseStep 1459891 = 2189837) B2189837
theorem B1951427 : Blo 1024605 1951427 := bstep (se 1 (by rfl) ⟨1463570, by rfl⟩ : syracuseStep 1951427 = 2927141) B2927141
theorem B13158085 : Blo 1024605 13158085 := bstep (se 4 (by rfl) ⟨1233570, by rfl⟩ : syracuseStep 13158085 = 2467141) B2467141
theorem B3458861 : Blo 1024605 3458861 := bstep (se 3 (by rfl) ⟨648536, by rfl⟩ : syracuseStep 3458861 = 1297073) B1297073
theorem B7784261 : Blo 1024605 7784261 := bstep (se 4 (by rfl) ⟨729774, by rfl⟩ : syracuseStep 7784261 = 1459549) B1459549
theorem B1558369 : Blo 1024605 1558369 := bstep (se 2 (by rfl) ⟨584388, by rfl⟩ : syracuseStep 1558369 = 1168777) B1168777
theorem B3458915 : Blo 1024605 3458915 := bstep (se 1 (by rfl) ⟨2594186, by rfl⟩ : syracuseStep 3458915 = 5188373) B5188373
theorem B2312081 : Blo 1024605 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B2312099 : Blo 1024605 2312099 := bstep (se 1 (by rfl) ⟨1734074, by rfl⟩ : syracuseStep 2312099 = 3468149) B3468149
theorem B1951715 : Blo 1024605 1951715 := bstep (se 1 (by rfl) ⟨1463786, by rfl⟩ : syracuseStep 1951715 = 2927573) B2927573
theorem B4933667 : Blo 1024605 4933667 := bstep (se 1 (by rfl) ⟨3700250, by rfl⟩ : syracuseStep 4933667 = 7400501) B7400501
theorem B5195825 : Blo 1024605 5195825 := bstep (se 2 (by rfl) ⟨1948434, by rfl⟩ : syracuseStep 5195825 = 3896869) B3896869
theorem B3459185 : Blo 1024605 3459185 := bstep (se 2 (by rfl) ⟨1297194, by rfl⟩ : syracuseStep 3459185 = 2594389) B2594389
theorem B1558673 : Blo 1024605 1558673 := bstep (se 2 (by rfl) ⟨584502, by rfl⟩ : syracuseStep 1558673 = 1169005) B1169005
theorem B1230995 : Blo 1024605 1230995 := bstep (se 1 (by rfl) ⟨923246, by rfl⟩ : syracuseStep 1230995 = 1846493) B1846493
theorem B1755299 : Blo 1024605 1755299 := bstep (se 1 (by rfl) ⟨1316474, by rfl⟩ : syracuseStep 1755299 = 2632949) B2632949
theorem B2312369 : Blo 1024605 2312369 := bstep (se 2 (by rfl) ⟨867138, by rfl⟩ : syracuseStep 2312369 = 1734277) B1734277
theorem B2312387 : Blo 1024605 2312387 := bstep (se 1 (by rfl) ⟨1734290, by rfl⟩ : syracuseStep 2312387 = 3468581) B3468581
theorem B2312657 : Blo 1024605 2312657 := bstep (se 2 (by rfl) ⟨867246, by rfl⟩ : syracuseStep 2312657 = 1734493) B1734493
theorem B2312675 : Blo 1024605 2312675 := bstep (se 1 (by rfl) ⟨1734506, by rfl⟩ : syracuseStep 2312675 = 3469013) B3469013
theorem B6244933 : Blo 1024605 6244933 := bstep (se 4 (by rfl) ⟨585462, by rfl⟩ : syracuseStep 6244933 = 1170925) B1170925
theorem B3459725 : Blo 1024605 3459725 := bstep (se 3 (by rfl) ⟨648698, by rfl⟩ : syracuseStep 3459725 = 1297397) B1297397
theorem B3459779 : Blo 1024605 3459779 := bstep (se 1 (by rfl) ⟨2594834, by rfl⟩ : syracuseStep 3459779 = 5189669) B5189669
theorem B2312945 : Blo 1024605 2312945 := bstep (se 2 (by rfl) ⟨867354, by rfl⟩ : syracuseStep 2312945 = 1734709) B1734709
theorem B2312963 : Blo 1024605 2312963 := bstep (se 1 (by rfl) ⟨1734722, by rfl⟩ : syracuseStep 2312963 = 3469445) B3469445
theorem B2771729 : Blo 1024605 2771729 := bstep (se 2 (by rfl) ⟨1039398, by rfl⟩ : syracuseStep 2771729 = 2078797) B2078797
theorem B1297235 : Blo 1024605 1297235 := bstep (se 1 (by rfl) ⟨972926, by rfl⟩ : syracuseStep 1297235 = 1945853) B1945853
theorem B1952657 : Blo 1024605 1952657 := bstep (se 2 (by rfl) ⟨732246, by rfl⟩ : syracuseStep 1952657 = 1464493) B1464493
theorem B7392197 : Blo 1024605 7392197 := bstep (se 4 (by rfl) ⟨693018, by rfl⟩ : syracuseStep 7392197 = 1386037) B1386037
theorem B3460049 : Blo 1024605 3460049 := bstep (se 2 (by rfl) ⟨1297518, by rfl⟩ : syracuseStep 3460049 = 2595037) B2595037
theorem B1461235 : Blo 1024605 1461235 := bstep (se 1 (by rfl) ⟨1095926, by rfl⟩ : syracuseStep 1461235 = 2191853) B2191853
theorem B2313233 : Blo 1024605 2313233 := bstep (se 2 (by rfl) ⟨867462, by rfl⟩ : syracuseStep 2313233 = 1734925) B1734925
theorem B2313251 : Blo 1024605 2313251 := bstep (se 1 (by rfl) ⟨1734938, by rfl⟩ : syracuseStep 2313251 = 3469877) B3469877
theorem B4377827 : Blo 1024605 4377827 := bstep (se 1 (by rfl) ⟨3283370, by rfl⟩ : syracuseStep 4377827 = 6566741) B6566741
theorem B12471565 : Blo 1024605 12471565 := bstep (se 3 (by rfl) ⟨2338418, by rfl⟩ : syracuseStep 12471565 = 4676837) B4676837
theorem B5557517 : Blo 1024605 5557517 := bstep (se 3 (by rfl) ⟨1042034, by rfl⟩ : syracuseStep 5557517 = 2084069) B2084069
theorem B2313521 : Blo 1024605 2313521 := bstep (se 2 (by rfl) ⟨867570, by rfl⟩ : syracuseStep 2313521 = 1735141) B1735141
theorem B2313539 : Blo 1024605 2313539 := bstep (se 1 (by rfl) ⟨1735154, by rfl⟩ : syracuseStep 2313539 = 3470309) B3470309
theorem B2969041 : Blo 1024605 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B5197283 : Blo 1024605 5197283 := bstep (se 1 (by rfl) ⟨3897962, by rfl⟩ : syracuseStep 5197283 = 7795925) B7795925
theorem B3460589 : Blo 1024605 3460589 := bstep (se 3 (by rfl) ⟨648860, by rfl⟩ : syracuseStep 3460589 = 1297721) B1297721
theorem B1297939 : Blo 1024605 1297939 := bstep (se 1 (by rfl) ⟨973454, by rfl⟩ : syracuseStep 1297939 = 1946909) B1946909
theorem B3460643 : Blo 1024605 3460643 := bstep (se 1 (by rfl) ⟨2595482, by rfl⟩ : syracuseStep 3460643 = 5190965) B5190965
theorem B2313809 : Blo 1024605 2313809 := bstep (se 2 (by rfl) ⟨867678, by rfl⟩ : syracuseStep 2313809 = 1735357) B1735357
theorem B2313827 : Blo 1024605 2313827 := bstep (se 1 (by rfl) ⟨1735370, by rfl⟩ : syracuseStep 2313827 = 3470741) B3470741
theorem B1298035 : Blo 1024605 1298035 := bstep (se 1 (by rfl) ⟨973526, by rfl⟩ : syracuseStep 1298035 = 1947053) B1947053
theorem B1560211 : Blo 1024605 1560211 := bstep (se 1 (by rfl) ⟨1170158, by rfl⟩ : syracuseStep 1560211 = 2340317) B2340317
theorem B3165869 : Blo 1024605 3165869 := bstep (se 3 (by rfl) ⟨593600, by rfl⟩ : syracuseStep 3165869 = 1187201) B1187201
theorem B1560241 : Blo 1024605 1560241 := bstep (se 2 (by rfl) ⟨585090, by rfl⟩ : syracuseStep 1560241 = 1170181) B1170181
theorem B3165955 : Blo 1024605 3165955 := bstep (se 1 (by rfl) ⟨2374466, by rfl⟩ : syracuseStep 3165955 = 4748933) B4748933
theorem B4935437 : Blo 1024605 4935437 := bstep (se 3 (by rfl) ⟨925394, by rfl⟩ : syracuseStep 4935437 = 1850789) B1850789
theorem B3460913 : Blo 1024605 3460913 := bstep (se 2 (by rfl) ⟨1297842, by rfl⟩ : syracuseStep 3460913 = 2595685) B2595685
theorem B5853005 : Blo 1024605 5853005 := bstep (se 3 (by rfl) ⟨1097438, by rfl⟩ : syracuseStep 5853005 = 2194877) B2194877
theorem B2314097 : Blo 1024605 2314097 := bstep (se 2 (by rfl) ⟨867786, by rfl⟩ : syracuseStep 2314097 = 1735573) B1735573
theorem B2314115 : Blo 1024605 2314115 := bstep (se 1 (by rfl) ⟨1735586, by rfl⟩ : syracuseStep 2314115 = 3471173) B3471173
theorem B1462369 : Blo 1024605 1462369 := bstep (se 2 (by rfl) ⟨548388, by rfl⟩ : syracuseStep 1462369 = 1096777) B1096777
theorem B1298531 : Blo 1024605 1298531 := bstep (se 1 (by rfl) ⟨973898, by rfl⟩ : syracuseStep 1298531 = 1947797) B1947797
theorem B1462465 : Blo 1024605 1462465 := bstep (se 2 (by rfl) ⟨548424, by rfl⟩ : syracuseStep 1462465 = 1096849) B1096849
theorem B5198093 : Blo 1024605 5198093 := bstep (se 3 (by rfl) ⟨974642, by rfl⟩ : syracuseStep 5198093 = 1949285) B1949285
theorem B3461453 : Blo 1024605 3461453 := bstep (se 3 (by rfl) ⟨649022, by rfl⟩ : syracuseStep 3461453 = 1298045) B1298045
theorem B1233235 : Blo 1024605 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B3461507 : Blo 1024605 3461507 := bstep (se 1 (by rfl) ⟨2596130, by rfl⟩ : syracuseStep 3461507 = 5192261) B5192261
theorem B3461777 : Blo 1024605 3461777 := bstep (se 2 (by rfl) ⟨1298166, by rfl⟩ : syracuseStep 3461777 = 2596333) B2596333
theorem B1462961 : Blo 1024605 1462961 := bstep (se 2 (by rfl) ⟨548610, by rfl⟩ : syracuseStep 1462961 = 1097221) B1097221
theorem B1299235 : Blo 1024605 1299235 := bstep (se 1 (by rfl) ⟨974426, by rfl⟩ : syracuseStep 1299235 = 1948853) B1948853
theorem B1299331 : Blo 1024605 1299331 := bstep (se 1 (by rfl) ⟨974498, by rfl⟩ : syracuseStep 1299331 = 1948997) B1948997
theorem B3462317 : Blo 1024605 3462317 := bstep (se 3 (by rfl) ⟨649184, by rfl⟩ : syracuseStep 3462317 = 1298369) B1298369
theorem B3462371 : Blo 1024605 3462371 := bstep (se 1 (by rfl) ⟨2596778, by rfl⟩ : syracuseStep 3462371 = 5193557) B5193557
theorem B1299827 : Blo 1024605 1299827 := bstep (se 1 (by rfl) ⟨974870, by rfl⟩ : syracuseStep 1299827 = 1949741) B1949741
theorem B1562017 : Blo 1024605 1562017 := bstep (se 2 (by rfl) ⟨585756, by rfl⟩ : syracuseStep 1562017 = 1171513) B1171513
theorem B3462641 : Blo 1024605 3462641 := bstep (se 2 (by rfl) ⟨1298490, by rfl⟩ : syracuseStep 3462641 = 2596981) B2596981
theorem B1463827 : Blo 1024605 1463827 := bstep (se 1 (by rfl) ⟨1097870, by rfl⟩ : syracuseStep 1463827 = 2195741) B2195741
theorem B1463923 : Blo 1024605 1463923 := bstep (se 1 (by rfl) ⟨1097942, by rfl⟩ : syracuseStep 1463923 = 2195885) B2195885
theorem B2774669 : Blo 1024605 2774669 := bstep (se 3 (by rfl) ⟨520250, by rfl⟩ : syracuseStep 2774669 = 1040501) B1040501
theorem B4380493 : Blo 1024605 4380493 := bstep (se 3 (by rfl) ⟨821342, by rfl⟩ : syracuseStep 4380493 = 1642685) B1642685
theorem B3168163 : Blo 1024605 3168163 := bstep (se 1 (by rfl) ⟨2376122, by rfl⟩ : syracuseStep 3168163 = 4752245) B4752245
theorem B5855237 : Blo 1024605 5855237 := bstep (se 4 (by rfl) ⟨548928, by rfl⟩ : syracuseStep 5855237 = 1097857) B1097857
theorem B3463181 : Blo 1024605 3463181 := bstep (se 3 (by rfl) ⟨649346, by rfl⟩ : syracuseStep 3463181 = 1298693) B1298693
theorem B7133197 : Blo 1024605 7133197 := bstep (se 3 (by rfl) ⟨1337474, by rfl⟩ : syracuseStep 7133197 = 2674949) B2674949
theorem B1300531 : Blo 1024605 1300531 := bstep (se 1 (by rfl) ⟨975398, by rfl⟩ : syracuseStep 1300531 = 1950797) B1950797
theorem B3463235 : Blo 1024605 3463235 := bstep (se 1 (by rfl) ⟨2597426, by rfl⟩ : syracuseStep 3463235 = 5194853) B5194853
theorem B6576227 : Blo 1024605 6576227 := bstep (se 1 (by rfl) ⟨4932170, by rfl⟩ : syracuseStep 6576227 = 9864341) B9864341
theorem B1464419 : Blo 1024605 1464419 := bstep (se 1 (by rfl) ⟨1098314, by rfl⟩ : syracuseStep 1464419 = 2196629) B2196629
theorem B1300627 : Blo 1024605 1300627 := bstep (se 1 (by rfl) ⟨975470, by rfl⟩ : syracuseStep 1300627 = 1950941) B1950941
theorem B1562771 : Blo 1024605 1562771 := bstep (se 1 (by rfl) ⟨1172078, by rfl⟩ : syracuseStep 1562771 = 2344157) B2344157
theorem B3463505 : Blo 1024605 3463505 := bstep (se 2 (by rfl) ⟨1298814, by rfl⟩ : syracuseStep 3463505 = 2597629) B2597629
theorem B7493987 : Blo 1024605 7493987 := bstep (se 1 (by rfl) ⟨5620490, by rfl⟩ : syracuseStep 7493987 = 11240981) B11240981
theorem B1333811 : Blo 1024605 1333811 := bstep (se 1 (by rfl) ⟨1000358, by rfl⟩ : syracuseStep 1333811 = 2000717) B2000717
theorem B1301123 : Blo 1024605 1301123 := bstep (se 1 (by rfl) ⟨975842, by rfl⟩ : syracuseStep 1301123 = 1951685) B1951685
theorem B5855921 : Blo 1024605 5855921 := bstep (se 2 (by rfl) ⟨2195970, by rfl⟩ : syracuseStep 5855921 = 4391941) B4391941
theorem B6675149 : Blo 1024605 6675149 := bstep (se 3 (by rfl) ⟨1251590, by rfl⟩ : syracuseStep 6675149 = 2503181) B2503181
theorem B3464045 : Blo 1024605 3464045 := bstep (se 3 (by rfl) ⟨649508, by rfl⟩ : syracuseStep 3464045 = 1299017) B1299017
theorem B4381553 : Blo 1024605 4381553 := bstep (se 2 (by rfl) ⟨1643082, by rfl⟩ : syracuseStep 4381553 = 3286165) B3286165
theorem B7035761 : Blo 1024605 7035761 := bstep (se 2 (by rfl) ⟨2638410, by rfl⟩ : syracuseStep 7035761 = 5276821) B5276821
theorem B3464099 : Blo 1024605 3464099 := bstep (se 1 (by rfl) ⟨2598074, by rfl⟩ : syracuseStep 3464099 = 5196149) B5196149
theorem B5201009 : Blo 1024605 5201009 := bstep (se 2 (by rfl) ⟨1950378, by rfl⟩ : syracuseStep 5201009 = 3900757) B3900757
theorem B3955825 : Blo 1024605 3955825 := bstep (se 2 (by rfl) ⟨1483434, by rfl⟩ : syracuseStep 3955825 = 2966869) B2966869
theorem B3890339 : Blo 1024605 3890339 := bstep (se 1 (by rfl) ⟨2917754, by rfl⟩ : syracuseStep 3890339 = 5835509) B5835509
theorem B3464369 : Blo 1024605 3464369 := bstep (se 2 (by rfl) ⟨1299138, by rfl⟩ : syracuseStep 3464369 = 2598277) B2598277
theorem B1301827 : Blo 1024605 1301827 := bstep (se 1 (by rfl) ⟨976370, by rfl⟩ : syracuseStep 1301827 = 1952741) B1952741
theorem B4677041 : Blo 1024605 4677041 := bstep (se 2 (by rfl) ⟨1753890, by rfl⟩ : syracuseStep 4677041 = 3507781) B3507781
theorem B7790093 : Blo 1024605 7790093 := bstep (se 3 (by rfl) ⟨1460642, by rfl⟩ : syracuseStep 7790093 = 2921285) B2921285
theorem B3464909 : Blo 1024605 3464909 := bstep (se 3 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 3464909 = 1299341) B1299341
theorem B3464963 : Blo 1024605 3464963 := bstep (se 1 (by rfl) ⟨2598722, by rfl⟩ : syracuseStep 3464963 = 5197445) B5197445
theorem B3465233 : Blo 1024605 3465233 := bstep (se 2 (by rfl) ⟨1299462, by rfl⟩ : syracuseStep 3465233 = 2598925) B2598925
theorem B5857379 : Blo 1024605 5857379 := bstep (se 1 (by rfl) ⟨4393034, by rfl⟩ : syracuseStep 5857379 = 8786069) B8786069
theorem B3891341 : Blo 1024605 3891341 := bstep (se 3 (by rfl) ⟨729626, by rfl⟩ : syracuseStep 3891341 = 1459253) B1459253
theorem B5202467 : Blo 1024605 5202467 := bstep (se 1 (by rfl) ⟨3901850, by rfl⟩ : syracuseStep 5202467 = 7803701) B7803701
theorem B3465773 : Blo 1024605 3465773 := bstep (se 3 (by rfl) ⟨649832, by rfl⟩ : syracuseStep 3465773 = 1299665) B1299665
theorem B1729073 : Blo 1024605 1729073 := bstep (se 2 (by rfl) ⟨648402, by rfl⟩ : syracuseStep 1729073 = 1296805) B1296805
theorem B3465827 : Blo 1024605 3465827 := bstep (se 1 (by rfl) ⟨2599370, by rfl⟩ : syracuseStep 3465827 = 5198741) B5198741
theorem B2777741 : Blo 1024605 2777741 := bstep (se 3 (by rfl) ⟨520826, by rfl⟩ : syracuseStep 2777741 = 1041653) B1041653
theorem B1729201 : Blo 1024605 1729201 := bstep (se 2 (by rfl) ⟨648450, by rfl⟩ : syracuseStep 1729201 = 1296901) B1296901
theorem B1729235 : Blo 1024605 1729235 := bstep (se 1 (by rfl) ⟨1296926, by rfl⟩ : syracuseStep 1729235 = 2593853) B2593853
theorem B1729363 : Blo 1024605 1729363 := bstep (se 1 (by rfl) ⟨1297022, by rfl⟩ : syracuseStep 1729363 = 2594045) B2594045
theorem B3466097 : Blo 1024605 3466097 := bstep (se 2 (by rfl) ⟨1299786, by rfl⟩ : syracuseStep 3466097 = 2599573) B2599573
theorem B1729505 : Blo 1024605 1729505 := bstep (se 2 (by rfl) ⟨648564, by rfl⟩ : syracuseStep 1729505 = 1297129) B1297129
theorem B1500211 : Blo 1024605 1500211 := bstep (se 1 (by rfl) ⟨1125158, by rfl⟩ : syracuseStep 1500211 = 2250317) B2250317
theorem B3204163 : Blo 1024605 3204163 := bstep (se 1 (by rfl) ⟨2403122, by rfl⟩ : syracuseStep 3204163 = 4806245) B4806245
theorem B1729633 : Blo 1024605 1729633 := bstep (se 2 (by rfl) ⟨648612, by rfl⟩ : syracuseStep 1729633 = 1297225) B1297225
theorem B1729667 : Blo 1024605 1729667 := bstep (se 1 (by rfl) ⟨1297250, by rfl⟩ : syracuseStep 1729667 = 2594501) B2594501
theorem B1041539 : Blo 1024605 1041539 := bstep (se 1 (by rfl) ⟨781154, by rfl⟩ : syracuseStep 1041539 = 1562309) B1562309
theorem B1729795 : Blo 1024605 1729795 := bstep (se 1 (by rfl) ⟨1297346, by rfl⟩ : syracuseStep 1729795 = 2594693) B2594693
theorem B5203277 : Blo 1024605 5203277 := bstep (se 3 (by rfl) ⟨975614, by rfl⟩ : syracuseStep 5203277 = 1951229) B1951229
theorem B3466637 : Blo 1024605 3466637 := bstep (se 3 (by rfl) ⟨649994, by rfl⟩ : syracuseStep 3466637 = 1299989) B1299989
theorem B1729937 : Blo 1024605 1729937 := bstep (se 2 (by rfl) ⟨648726, by rfl⟩ : syracuseStep 1729937 = 1297453) B1297453
theorem B3466691 : Blo 1024605 3466691 := bstep (se 1 (by rfl) ⟨2600018, by rfl⟩ : syracuseStep 3466691 = 5200037) B5200037
theorem B1730065 : Blo 1024605 1730065 := bstep (se 2 (by rfl) ⟨648774, by rfl⟩ : syracuseStep 1730065 = 1297549) B1297549
theorem B1730099 : Blo 1024605 1730099 := bstep (se 1 (by rfl) ⟨1297574, by rfl⟩ : syracuseStep 1730099 = 2595149) B2595149
theorem B1730227 : Blo 1024605 1730227 := bstep (se 1 (by rfl) ⟨1297670, by rfl⟩ : syracuseStep 1730227 = 2595341) B2595341
theorem B11691701 : Blo 1024605 11691701 := bstep (se 5 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 11691701 = 1096097) B1096097
theorem B2221777 : Blo 1024605 2221777 := bstep (se 2 (by rfl) ⟨833166, by rfl⟩ : syracuseStep 2221777 = 1666333) B1666333
theorem B3466961 : Blo 1024605 3466961 := bstep (se 2 (by rfl) ⟨1300110, by rfl⟩ : syracuseStep 3466961 = 2600221) B2600221
theorem B4384525 : Blo 1024605 4384525 := bstep (se 3 (by rfl) ⟨822098, by rfl⟩ : syracuseStep 4384525 = 1644197) B1644197
theorem B1730369 : Blo 1024605 1730369 := bstep (se 2 (by rfl) ⟨648888, by rfl⟩ : syracuseStep 1730369 = 1297777) B1297777
theorem B1730497 : Blo 1024605 1730497 := bstep (se 2 (by rfl) ⟨648936, by rfl⟩ : syracuseStep 1730497 = 1297873) B1297873
theorem B1730531 : Blo 1024605 1730531 := bstep (se 1 (by rfl) ⟨1297898, by rfl⟩ : syracuseStep 1730531 = 2595797) B2595797
theorem B11233265 : Blo 1024605 11233265 := bstep (se 2 (by rfl) ⟨4212474, by rfl⟩ : syracuseStep 11233265 = 8424949) B8424949
theorem B6580273 : Blo 1024605 6580273 := bstep (se 2 (by rfl) ⟨2467602, by rfl⟩ : syracuseStep 6580273 = 4935205) B4935205
theorem B1730659 : Blo 1024605 1730659 := bstep (se 1 (by rfl) ⟨1297994, by rfl⟩ : syracuseStep 1730659 = 2595989) B2595989
theorem B4384867 : Blo 1024605 4384867 := bstep (se 1 (by rfl) ⟨3288650, by rfl⟩ : syracuseStep 4384867 = 6577301) B6577301
theorem B3893453 : Blo 1024605 3893453 := bstep (se 3 (by rfl) ⟨730022, by rfl⟩ : syracuseStep 3893453 = 1460045) B1460045
theorem B2189521 : Blo 1024605 2189521 := bstep (se 2 (by rfl) ⟨821070, by rfl⟩ : syracuseStep 2189521 = 1642141) B1642141
theorem B3467501 : Blo 1024605 3467501 := bstep (se 3 (by rfl) ⟨650156, by rfl⟩ : syracuseStep 3467501 = 1300313) B1300313
theorem B1730801 : Blo 1024605 1730801 := bstep (se 2 (by rfl) ⟨649050, by rfl⟩ : syracuseStep 1730801 = 1298101) B1298101
theorem B3467555 : Blo 1024605 3467555 := bstep (se 1 (by rfl) ⟨2600666, by rfl⟩ : syracuseStep 3467555 = 5201333) B5201333
theorem B13330757 : Blo 1024605 13330757 := bstep (se 4 (by rfl) ⟨1249758, by rfl⟩ : syracuseStep 13330757 = 2499517) B2499517
theorem B1730929 : Blo 1024605 1730929 := bstep (se 2 (by rfl) ⟨649098, by rfl⟩ : syracuseStep 1730929 = 1298197) B1298197
theorem B7793009 : Blo 1024605 7793009 := bstep (se 2 (by rfl) ⟨2922378, by rfl⟩ : syracuseStep 7793009 = 5844757) B5844757
theorem B1730963 : Blo 1024605 1730963 := bstep (se 1 (by rfl) ⟨1298222, by rfl⟩ : syracuseStep 1730963 = 2596445) B2596445
theorem B2812429 : Blo 1024605 2812429 := bstep (se 3 (by rfl) ⟨527330, by rfl⟩ : syracuseStep 2812429 = 1054661) B1054661
theorem B1731091 : Blo 1024605 1731091 := bstep (se 1 (by rfl) ⟨1298318, by rfl⟩ : syracuseStep 1731091 = 2596637) B2596637
theorem B3467825 : Blo 1024605 3467825 := bstep (se 2 (by rfl) ⟨1300434, by rfl⟩ : syracuseStep 3467825 = 2600869) B2600869
theorem B1731233 : Blo 1024605 1731233 := bstep (se 2 (by rfl) ⟨649212, by rfl⟩ : syracuseStep 1731233 = 1298425) B1298425
theorem B5073635 : Blo 1024605 5073635 := bstep (se 1 (by rfl) ⟨3805226, by rfl⟩ : syracuseStep 5073635 = 7610453) B7610453
theorem B1731361 : Blo 1024605 1731361 := bstep (se 2 (by rfl) ⟨649260, by rfl⟩ : syracuseStep 1731361 = 1298521) B1298521
theorem B1731395 : Blo 1024605 1731395 := bstep (se 1 (by rfl) ⟨1298546, by rfl⟩ : syracuseStep 1731395 = 2597093) B2597093
theorem B2190179 : Blo 1024605 2190179 := bstep (se 1 (by rfl) ⟨1642634, by rfl⟩ : syracuseStep 2190179 = 3285269) B3285269
theorem B1731523 : Blo 1024605 1731523 := bstep (se 1 (by rfl) ⟨1298642, by rfl⟩ : syracuseStep 1731523 = 2597285) B2597285
theorem B3894257 : Blo 1024605 3894257 := bstep (se 2 (by rfl) ⟨1460346, by rfl⟩ : syracuseStep 3894257 = 2920693) B2920693
theorem B5139533 : Blo 1024605 5139533 := bstep (se 3 (by rfl) ⟨963662, by rfl⟩ : syracuseStep 5139533 = 1927325) B1927325
theorem B3468365 : Blo 1024605 3468365 := bstep (se 3 (by rfl) ⟨650318, by rfl⟩ : syracuseStep 3468365 = 1300637) B1300637
theorem B1731665 : Blo 1024605 1731665 := bstep (se 2 (by rfl) ⟨649374, by rfl⟩ : syracuseStep 1731665 = 1298749) B1298749
theorem B3468419 : Blo 1024605 3468419 := bstep (se 1 (by rfl) ⟨2601314, by rfl⟩ : syracuseStep 3468419 = 5202629) B5202629
theorem B1731793 : Blo 1024605 1731793 := bstep (se 2 (by rfl) ⟨649422, by rfl⟩ : syracuseStep 1731793 = 1298845) B1298845
theorem B1731827 : Blo 1024605 1731827 := bstep (se 1 (by rfl) ⟨1298870, by rfl⟩ : syracuseStep 1731827 = 2597741) B2597741
theorem B3697933 : Blo 1024605 3697933 := bstep (se 3 (by rfl) ⟨693362, by rfl⟩ : syracuseStep 3697933 = 1386725) B1386725
theorem B1731955 : Blo 1024605 1731955 := bstep (se 1 (by rfl) ⟨1298966, by rfl⟩ : syracuseStep 1731955 = 2597933) B2597933
theorem B3468689 : Blo 1024605 3468689 := bstep (se 2 (by rfl) ⟨1300758, by rfl⟩ : syracuseStep 3468689 = 2601517) B2601517
theorem B1732097 : Blo 1024605 1732097 := bstep (se 2 (by rfl) ⟨649536, by rfl⟩ : syracuseStep 1732097 = 1299073) B1299073
theorem B1732225 : Blo 1024605 1732225 := bstep (se 2 (by rfl) ⟨649584, by rfl⟩ : syracuseStep 1732225 = 1299169) B1299169
theorem B3894925 : Blo 1024605 3894925 := bstep (se 3 (by rfl) ⟨730298, by rfl⟩ : syracuseStep 3894925 = 1460597) B1460597
theorem B1732259 : Blo 1024605 1732259 := bstep (se 1 (by rfl) ⟨1299194, by rfl⟩ : syracuseStep 1732259 = 2598389) B2598389
theorem B2191025 : Blo 1024605 2191025 := bstep (se 2 (by rfl) ⟨821634, by rfl⟩ : syracuseStep 2191025 = 1643269) B1643269
theorem B1732387 : Blo 1024605 1732387 := bstep (se 1 (by rfl) ⟨1299290, by rfl⟩ : syracuseStep 1732387 = 2598581) B2598581
theorem B2748205 : Blo 1024605 2748205 := bstep (se 3 (by rfl) ⟨515288, by rfl⟩ : syracuseStep 2748205 = 1030577) B1030577
theorem B3469229 : Blo 1024605 3469229 := bstep (se 3 (by rfl) ⟨650480, by rfl⟩ : syracuseStep 3469229 = 1300961) B1300961
theorem B1732529 : Blo 1024605 1732529 := bstep (se 2 (by rfl) ⟨649698, by rfl⟩ : syracuseStep 1732529 = 1299397) B1299397
theorem B3469283 : Blo 1024605 3469283 := bstep (se 1 (by rfl) ⟨2601962, by rfl⟩ : syracuseStep 3469283 = 5203925) B5203925
theorem B1732657 : Blo 1024605 1732657 := bstep (se 2 (by rfl) ⟨649746, by rfl⟩ : syracuseStep 1732657 = 1299493) B1299493
theorem B1732691 : Blo 1024605 1732691 := bstep (se 1 (by rfl) ⟨1299518, by rfl⟩ : syracuseStep 1732691 = 2599037) B2599037
theorem B28471409 : Blo 1024605 28471409 := bstep (se 2 (by rfl) ⟨10676778, by rfl⟩ : syracuseStep 28471409 = 21353557) B21353557
theorem B5206193 : Blo 1024605 5206193 := bstep (se 2 (by rfl) ⟨1952322, by rfl⟩ : syracuseStep 5206193 = 3904645) B3904645
theorem B1732819 : Blo 1024605 1732819 := bstep (se 1 (by rfl) ⟨1299614, by rfl⟩ : syracuseStep 1732819 = 2599229) B2599229
theorem B3469553 : Blo 1024605 3469553 := bstep (se 2 (by rfl) ⟨1301082, by rfl⟩ : syracuseStep 3469553 = 2602165) B2602165
theorem B1732961 : Blo 1024605 1732961 := bstep (se 2 (by rfl) ⟨649860, by rfl⟩ : syracuseStep 1732961 = 1299721) B1299721
theorem B3895715 : Blo 1024605 3895715 := bstep (se 1 (by rfl) ⟨2921786, by rfl⟩ : syracuseStep 3895715 = 5843573) B5843573
theorem B1733089 : Blo 1024605 1733089 := bstep (se 2 (by rfl) ⟨649908, by rfl⟩ : syracuseStep 1733089 = 1299817) B1299817
theorem B1733123 : Blo 1024605 1733123 := bstep (se 1 (by rfl) ⟨1299842, by rfl⟩ : syracuseStep 1733123 = 2599685) B2599685
theorem B1733251 : Blo 1024605 1733251 := bstep (se 1 (by rfl) ⟨1299938, by rfl⟩ : syracuseStep 1733251 = 2599877) B2599877
theorem B1667825 : Blo 1024605 1667825 := bstep (se 2 (by rfl) ⟨625434, by rfl⟩ : syracuseStep 1667825 = 1250869) B1250869
theorem B3470093 : Blo 1024605 3470093 := bstep (se 3 (by rfl) ⟨650642, by rfl⟩ : syracuseStep 3470093 = 1301285) B1301285
theorem B1733393 : Blo 1024605 1733393 := bstep (se 2 (by rfl) ⟨650022, by rfl⟩ : syracuseStep 1733393 = 1300045) B1300045
theorem B1667873 : Blo 1024605 1667873 := bstep (se 2 (by rfl) ⟨625452, by rfl⟩ : syracuseStep 1667873 = 1250905) B1250905
theorem B3470147 : Blo 1024605 3470147 := bstep (se 1 (by rfl) ⟨2602610, by rfl⟩ : syracuseStep 3470147 = 5205221) B5205221
theorem B4158307 : Blo 1024605 4158307 := bstep (se 1 (by rfl) ⟨3118730, by rfl⟩ : syracuseStep 4158307 = 6237461) B6237461
theorem B6746993 : Blo 1024605 6746993 := bstep (se 2 (by rfl) ⟨2530122, by rfl⟩ : syracuseStep 6746993 = 5060245) B5060245
theorem B1733521 : Blo 1024605 1733521 := bstep (se 2 (by rfl) ⟨650070, by rfl⟩ : syracuseStep 1733521 = 1300141) B1300141
theorem B1536929 : Blo 1024605 1536929 := bstep (se 2 (by rfl) ⟨576348, by rfl⟩ : syracuseStep 1536929 = 1152697) B1152697
theorem B1536947 : Blo 1024605 1536947 := bstep (se 1 (by rfl) ⟨1152710, by rfl⟩ : syracuseStep 1536947 = 2305421) B2305421
theorem B1733555 : Blo 1024605 1733555 := bstep (se 1 (by rfl) ⟨1300166, by rfl⟩ : syracuseStep 1733555 = 2600333) B2600333
theorem B1536977 : Blo 1024605 1536977 := bstep (se 2 (by rfl) ⟨576366, by rfl⟩ : syracuseStep 1536977 = 1152733) B1152733
theorem B1536995 : Blo 1024605 1536995 := bstep (se 1 (by rfl) ⟨1152746, by rfl⟩ : syracuseStep 1536995 = 2305493) B2305493
theorem B1537025 : Blo 1024605 1537025 := bstep (se 2 (by rfl) ⟨576384, by rfl⟩ : syracuseStep 1537025 = 1152769) B1152769
theorem B1537043 : Blo 1024605 1537043 := bstep (se 1 (by rfl) ⟨1152782, by rfl⟩ : syracuseStep 1537043 = 2305565) B2305565
theorem B1537073 : Blo 1024605 1537073 := bstep (se 2 (by rfl) ⟨576402, by rfl⟩ : syracuseStep 1537073 = 1152805) B1152805
theorem B3896369 : Blo 1024605 3896369 := bstep (se 2 (by rfl) ⟨1461138, by rfl⟩ : syracuseStep 3896369 = 2922277) B2922277
theorem B1733683 : Blo 1024605 1733683 := bstep (se 1 (by rfl) ⟨1300262, by rfl⟩ : syracuseStep 1733683 = 2600525) B2600525
theorem B53310517 : Blo 1024605 53310517 := bstep (se 5 (by rfl) ⟨2498930, by rfl⟩ : syracuseStep 53310517 = 4997861) B4997861
theorem B1537091 : Blo 1024605 1537091 := bstep (se 1 (by rfl) ⟨1152818, by rfl⟩ : syracuseStep 1537091 = 2305637) B2305637
theorem B3470417 : Blo 1024605 3470417 := bstep (se 2 (by rfl) ⟨1301406, by rfl⟩ : syracuseStep 3470417 = 2602813) B2602813
theorem B1537121 : Blo 1024605 1537121 := bstep (se 2 (by rfl) ⟨576420, by rfl⟩ : syracuseStep 1537121 = 1152841) B1152841
theorem B1537139 : Blo 1024605 1537139 := bstep (se 1 (by rfl) ⟨1152854, by rfl⟩ : syracuseStep 1537139 = 2305709) B2305709
theorem B1537169 : Blo 1024605 1537169 := bstep (se 2 (by rfl) ⟨576438, by rfl⟩ : syracuseStep 1537169 = 1152877) B1152877
theorem B1537187 : Blo 1024605 1537187 := bstep (se 1 (by rfl) ⟨1152890, by rfl⟩ : syracuseStep 1537187 = 2305781) B2305781
theorem B1537217 : Blo 1024605 1537217 := bstep (se 2 (by rfl) ⟨576456, by rfl⟩ : syracuseStep 1537217 = 1152913) B1152913
theorem B1733825 : Blo 1024605 1733825 := bstep (se 2 (by rfl) ⟨650184, by rfl⟩ : syracuseStep 1733825 = 1300369) B1300369
theorem B1537235 : Blo 1024605 1537235 := bstep (se 1 (by rfl) ⟨1152926, by rfl⟩ : syracuseStep 1537235 = 2305853) B2305853
theorem B1537265 : Blo 1024605 1537265 := bstep (se 2 (by rfl) ⟨576474, by rfl⟩ : syracuseStep 1537265 = 1152949) B1152949
theorem B1537283 : Blo 1024605 1537283 := bstep (se 1 (by rfl) ⟨1152962, by rfl⟩ : syracuseStep 1537283 = 2305925) B2305925
theorem B1537313 : Blo 1024605 1537313 := bstep (se 2 (by rfl) ⟨576492, by rfl⟩ : syracuseStep 1537313 = 1152985) B1152985
theorem B1537331 : Blo 1024605 1537331 := bstep (se 1 (by rfl) ⟨1152998, by rfl⟩ : syracuseStep 1537331 = 2305997) B2305997
theorem B1733953 : Blo 1024605 1733953 := bstep (se 2 (by rfl) ⟨650232, by rfl⟩ : syracuseStep 1733953 = 1300465) B1300465
theorem B2192707 : Blo 1024605 2192707 := bstep (se 1 (by rfl) ⟨1644530, by rfl⟩ : syracuseStep 2192707 = 3289061) B3289061
theorem B1537361 : Blo 1024605 1537361 := bstep (se 2 (by rfl) ⟨576510, by rfl⟩ : syracuseStep 1537361 = 1153021) B1153021
theorem B1537379 : Blo 1024605 1537379 := bstep (se 1 (by rfl) ⟨1153034, by rfl⟩ : syracuseStep 1537379 = 2306069) B2306069
theorem B1733987 : Blo 1024605 1733987 := bstep (se 1 (by rfl) ⟨1300490, by rfl⟩ : syracuseStep 1733987 = 2600981) B2600981
theorem B1537409 : Blo 1024605 1537409 := bstep (se 2 (by rfl) ⟨576528, by rfl⟩ : syracuseStep 1537409 = 1153057) B1153057
theorem B1537427 : Blo 1024605 1537427 := bstep (se 1 (by rfl) ⟨1153070, by rfl⟩ : syracuseStep 1537427 = 2306141) B2306141
theorem B1537457 : Blo 1024605 1537457 := bstep (se 2 (by rfl) ⟨576546, by rfl⟩ : syracuseStep 1537457 = 1153093) B1153093
theorem B1537475 : Blo 1024605 1537475 := bstep (se 1 (by rfl) ⟨1153106, by rfl⟩ : syracuseStep 1537475 = 2306213) B2306213
theorem B1537505 : Blo 1024605 1537505 := bstep (se 2 (by rfl) ⟨576564, by rfl⟩ : syracuseStep 1537505 = 1153129) B1153129
theorem B1734115 : Blo 1024605 1734115 := bstep (se 1 (by rfl) ⟨1300586, by rfl⟩ : syracuseStep 1734115 = 2601173) B2601173
theorem B1537523 : Blo 1024605 1537523 := bstep (se 1 (by rfl) ⟨1153142, by rfl⟩ : syracuseStep 1537523 = 2306285) B2306285
theorem B1537553 : Blo 1024605 1537553 := bstep (se 2 (by rfl) ⟨576582, by rfl⟩ : syracuseStep 1537553 = 1153165) B1153165
theorem B1537571 : Blo 1024605 1537571 := bstep (se 1 (by rfl) ⟨1153178, by rfl⟩ : syracuseStep 1537571 = 2306357) B2306357
theorem B1537601 : Blo 1024605 1537601 := bstep (se 2 (by rfl) ⟨576600, by rfl⟩ : syracuseStep 1537601 = 1153201) B1153201
theorem B1537619 : Blo 1024605 1537619 := bstep (se 1 (by rfl) ⟨1153214, by rfl⟩ : syracuseStep 1537619 = 2306429) B2306429
theorem B3470957 : Blo 1024605 3470957 := bstep (se 3 (by rfl) ⟨650804, by rfl⟩ : syracuseStep 3470957 = 1301609) B1301609
theorem B1537649 : Blo 1024605 1537649 := bstep (se 2 (by rfl) ⟨576618, by rfl⟩ : syracuseStep 1537649 = 1153237) B1153237
theorem B1734257 : Blo 1024605 1734257 := bstep (se 2 (by rfl) ⟨650346, by rfl⟩ : syracuseStep 1734257 = 1300693) B1300693
theorem B1537667 : Blo 1024605 1537667 := bstep (se 1 (by rfl) ⟨1153250, by rfl⟩ : syracuseStep 1537667 = 2306501) B2306501
theorem B1537697 : Blo 1024605 1537697 := bstep (se 2 (by rfl) ⟨576636, by rfl⟩ : syracuseStep 1537697 = 1153273) B1153273
theorem B3471011 : Blo 1024605 3471011 := bstep (se 1 (by rfl) ⟨2603258, by rfl⟩ : syracuseStep 3471011 = 5206517) B5206517
theorem B1537715 : Blo 1024605 1537715 := bstep (se 1 (by rfl) ⟨1153286, by rfl⟩ : syracuseStep 1537715 = 2306573) B2306573
theorem B1537745 : Blo 1024605 1537745 := bstep (se 2 (by rfl) ⟨576654, by rfl⟩ : syracuseStep 1537745 = 1153309) B1153309
theorem B1537763 : Blo 1024605 1537763 := bstep (se 1 (by rfl) ⟨1153322, by rfl⟩ : syracuseStep 1537763 = 2306645) B2306645
theorem B1734385 : Blo 1024605 1734385 := bstep (se 2 (by rfl) ⟨650394, by rfl⟩ : syracuseStep 1734385 = 1300789) B1300789
theorem B1537793 : Blo 1024605 1537793 := bstep (se 2 (by rfl) ⟨576672, by rfl⟩ : syracuseStep 1537793 = 1153345) B1153345
theorem B2193169 : Blo 1024605 2193169 := bstep (se 2 (by rfl) ⟨822438, by rfl⟩ : syracuseStep 2193169 = 1644877) B1644877
theorem B1537811 : Blo 1024605 1537811 := bstep (se 1 (by rfl) ⟨1153358, by rfl⟩ : syracuseStep 1537811 = 2306717) B2306717
theorem B1734419 : Blo 1024605 1734419 := bstep (se 1 (by rfl) ⟨1300814, by rfl⟩ : syracuseStep 1734419 = 2601629) B2601629
theorem B1537841 : Blo 1024605 1537841 := bstep (se 2 (by rfl) ⟨576690, by rfl⟩ : syracuseStep 1537841 = 1153381) B1153381
theorem B1537859 : Blo 1024605 1537859 := bstep (se 1 (by rfl) ⟨1153394, by rfl⟩ : syracuseStep 1537859 = 2306789) B2306789
theorem B1537889 : Blo 1024605 1537889 := bstep (se 2 (by rfl) ⟨576708, by rfl⟩ : syracuseStep 1537889 = 1153417) B1153417
theorem B1537907 : Blo 1024605 1537907 := bstep (se 1 (by rfl) ⟨1153430, by rfl⟩ : syracuseStep 1537907 = 2306861) B2306861
theorem B1537937 : Blo 1024605 1537937 := bstep (se 2 (by rfl) ⟨576726, by rfl⟩ : syracuseStep 1537937 = 1153453) B1153453
theorem B1734547 : Blo 1024605 1734547 := bstep (se 1 (by rfl) ⟨1300910, by rfl⟩ : syracuseStep 1734547 = 2601821) B2601821
theorem B1537955 : Blo 1024605 1537955 := bstep (se 1 (by rfl) ⟨1153466, by rfl⟩ : syracuseStep 1537955 = 2306933) B2306933
theorem B3471281 : Blo 1024605 3471281 := bstep (se 2 (by rfl) ⟨1301730, by rfl⟩ : syracuseStep 3471281 = 2603461) B2603461
theorem B1537985 : Blo 1024605 1537985 := bstep (se 2 (by rfl) ⟨576744, by rfl⟩ : syracuseStep 1537985 = 1153489) B1153489
theorem B1538003 : Blo 1024605 1538003 := bstep (se 1 (by rfl) ⟨1153502, by rfl⟩ : syracuseStep 1538003 = 2307005) B2307005
theorem B1538033 : Blo 1024605 1538033 := bstep (se 2 (by rfl) ⟨576762, by rfl⟩ : syracuseStep 1538033 = 1153525) B1153525
theorem B1538051 : Blo 1024605 1538051 := bstep (se 1 (by rfl) ⟨1153538, by rfl⟩ : syracuseStep 1538051 = 2307077) B2307077
theorem B1538081 : Blo 1024605 1538081 := bstep (se 2 (by rfl) ⟨576780, by rfl⟩ : syracuseStep 1538081 = 1153561) B1153561
theorem B1734689 : Blo 1024605 1734689 := bstep (se 2 (by rfl) ⟨650508, by rfl⟩ : syracuseStep 1734689 = 1301017) B1301017
theorem B4388899 : Blo 1024605 4388899 := bstep (se 1 (by rfl) ⟨3291674, by rfl⟩ : syracuseStep 4388899 = 6583349) B6583349
theorem B1538099 : Blo 1024605 1538099 := bstep (se 1 (by rfl) ⟨1153574, by rfl⟩ : syracuseStep 1538099 = 2307149) B2307149
theorem B15005749 : Blo 1024605 15005749 := bstep (se 5 (by rfl) ⟨703394, by rfl⟩ : syracuseStep 15005749 = 1406789) B1406789
theorem B1538129 : Blo 1024605 1538129 := bstep (se 2 (by rfl) ⟨576798, by rfl⟩ : syracuseStep 1538129 = 1153597) B1153597
theorem B1538147 : Blo 1024605 1538147 := bstep (se 1 (by rfl) ⟨1153610, by rfl⟩ : syracuseStep 1538147 = 2307221) B2307221
theorem B1538177 : Blo 1024605 1538177 := bstep (se 2 (by rfl) ⟨576816, by rfl⟩ : syracuseStep 1538177 = 1153633) B1153633
theorem B1538195 : Blo 1024605 1538195 := bstep (se 1 (by rfl) ⟨1153646, by rfl⟩ : syracuseStep 1538195 = 2307293) B2307293
theorem B1734817 : Blo 1024605 1734817 := bstep (se 2 (by rfl) ⟨650556, by rfl⟩ : syracuseStep 1734817 = 1301113) B1301113
theorem B1538225 : Blo 1024605 1538225 := bstep (se 2 (by rfl) ⟨576834, by rfl⟩ : syracuseStep 1538225 = 1153669) B1153669
theorem B1538243 : Blo 1024605 1538243 := bstep (se 1 (by rfl) ⟨1153682, by rfl⟩ : syracuseStep 1538243 = 2307365) B2307365
theorem B1734851 : Blo 1024605 1734851 := bstep (se 1 (by rfl) ⟨1301138, by rfl⟩ : syracuseStep 1734851 = 2602277) B2602277
theorem B1538273 : Blo 1024605 1538273 := bstep (se 2 (by rfl) ⟨576852, by rfl⟩ : syracuseStep 1538273 = 1153705) B1153705
theorem B1538291 : Blo 1024605 1538291 := bstep (se 1 (by rfl) ⟨1153718, by rfl⟩ : syracuseStep 1538291 = 2307437) B2307437
theorem B1538321 : Blo 1024605 1538321 := bstep (se 2 (by rfl) ⟨576870, by rfl⟩ : syracuseStep 1538321 = 1153741) B1153741
theorem B1538339 : Blo 1024605 1538339 := bstep (se 1 (by rfl) ⟨1153754, by rfl⟩ : syracuseStep 1538339 = 2307509) B2307509
theorem B1538369 : Blo 1024605 1538369 := bstep (se 2 (by rfl) ⟨576888, by rfl⟩ : syracuseStep 1538369 = 1153777) B1153777
theorem B1734979 : Blo 1024605 1734979 := bstep (se 1 (by rfl) ⟨1301234, by rfl⟩ : syracuseStep 1734979 = 2602469) B2602469
theorem B1538387 : Blo 1024605 1538387 := bstep (se 1 (by rfl) ⟨1153790, by rfl⟩ : syracuseStep 1538387 = 2307581) B2307581
theorem B1538417 : Blo 1024605 1538417 := bstep (se 2 (by rfl) ⟨576906, by rfl⟩ : syracuseStep 1538417 = 1153813) B1153813
theorem B1538435 : Blo 1024605 1538435 := bstep (se 1 (by rfl) ⟨1153826, by rfl⟩ : syracuseStep 1538435 = 2307653) B2307653
theorem B1538465 : Blo 1024605 1538465 := bstep (se 2 (by rfl) ⟨576924, by rfl⟩ : syracuseStep 1538465 = 1153849) B1153849
theorem B1538483 : Blo 1024605 1538483 := bstep (se 1 (by rfl) ⟨1153862, by rfl⟩ : syracuseStep 1538483 = 2307725) B2307725
theorem B1538513 : Blo 1024605 1538513 := bstep (se 2 (by rfl) ⟨576942, by rfl⟩ : syracuseStep 1538513 = 1153885) B1153885
theorem B1735121 : Blo 1024605 1735121 := bstep (se 2 (by rfl) ⟨650670, by rfl⟩ : syracuseStep 1735121 = 1301341) B1301341
theorem B1538531 : Blo 1024605 1538531 := bstep (se 1 (by rfl) ⟨1153898, by rfl⟩ : syracuseStep 1538531 = 2307797) B2307797
theorem B3897827 : Blo 1024605 3897827 := bstep (se 1 (by rfl) ⟨2923370, by rfl⟩ : syracuseStep 3897827 = 5846741) B5846741
theorem B3897841 : Blo 1024605 3897841 := bstep (se 2 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 3897841 = 2923381) B2923381
theorem B1538561 : Blo 1024605 1538561 := bstep (se 2 (by rfl) ⟨576960, by rfl⟩ : syracuseStep 1538561 = 1153921) B1153921
theorem B1538579 : Blo 1024605 1538579 := bstep (se 1 (by rfl) ⟨1153934, by rfl⟩ : syracuseStep 1538579 = 2307869) B2307869
theorem B1538609 : Blo 1024605 1538609 := bstep (se 2 (by rfl) ⟨576978, by rfl⟩ : syracuseStep 1538609 = 1153957) B1153957
theorem B1538627 : Blo 1024605 1538627 := bstep (se 1 (by rfl) ⟨1153970, by rfl⟩ : syracuseStep 1538627 = 2307941) B2307941
theorem B1735249 : Blo 1024605 1735249 := bstep (se 2 (by rfl) ⟨650718, by rfl⟩ : syracuseStep 1735249 = 1301437) B1301437
theorem B1538657 : Blo 1024605 1538657 := bstep (se 2 (by rfl) ⟨576996, by rfl⟩ : syracuseStep 1538657 = 1153993) B1153993
theorem B1538675 : Blo 1024605 1538675 := bstep (se 1 (by rfl) ⟨1154006, by rfl⟩ : syracuseStep 1538675 = 2308013) B2308013
theorem B1735283 : Blo 1024605 1735283 := bstep (se 1 (by rfl) ⟨1301462, by rfl⟩ : syracuseStep 1735283 = 2602925) B2602925
theorem B1538705 : Blo 1024605 1538705 := bstep (se 2 (by rfl) ⟨577014, by rfl⟩ : syracuseStep 1538705 = 1154029) B1154029
theorem B1538723 : Blo 1024605 1538723 := bstep (se 1 (by rfl) ⟨1154042, by rfl⟩ : syracuseStep 1538723 = 2308085) B2308085
theorem B1538753 : Blo 1024605 1538753 := bstep (se 2 (by rfl) ⟨577032, by rfl⟩ : syracuseStep 1538753 = 1154065) B1154065
theorem B1538771 : Blo 1024605 1538771 := bstep (se 1 (by rfl) ⟨1154078, by rfl⟩ : syracuseStep 1538771 = 2308157) B2308157
theorem B1538801 : Blo 1024605 1538801 := bstep (se 2 (by rfl) ⟨577050, by rfl⟩ : syracuseStep 1538801 = 1154101) B1154101
theorem B1735411 : Blo 1024605 1735411 := bstep (se 1 (by rfl) ⟨1301558, by rfl⟩ : syracuseStep 1735411 = 2603117) B2603117
theorem B1538819 : Blo 1024605 1538819 := bstep (se 1 (by rfl) ⟨1154114, by rfl⟩ : syracuseStep 1538819 = 2308229) B2308229
theorem B1538849 : Blo 1024605 1538849 := bstep (se 2 (by rfl) ⟨577068, by rfl⟩ : syracuseStep 1538849 = 1154137) B1154137
theorem B2194211 : Blo 1024605 2194211 := bstep (se 1 (by rfl) ⟨1645658, by rfl⟩ : syracuseStep 2194211 = 3291317) B3291317
theorem B1538867 : Blo 1024605 1538867 := bstep (se 1 (by rfl) ⟨1154150, by rfl⟩ : syracuseStep 1538867 = 2308301) B2308301
theorem B1538897 : Blo 1024605 1538897 := bstep (se 2 (by rfl) ⟨577086, by rfl⟩ : syracuseStep 1538897 = 1154173) B1154173
theorem B1538915 : Blo 1024605 1538915 := bstep (se 1 (by rfl) ⟨1154186, by rfl⟩ : syracuseStep 1538915 = 2308373) B2308373
theorem B1538945 : Blo 1024605 1538945 := bstep (se 2 (by rfl) ⟨577104, by rfl⟩ : syracuseStep 1538945 = 1154209) B1154209
theorem B1735553 : Blo 1024605 1735553 := bstep (se 2 (by rfl) ⟨650832, by rfl⟩ : syracuseStep 1735553 = 1301665) B1301665
theorem B1538963 : Blo 1024605 1538963 := bstep (se 1 (by rfl) ⟨1154222, by rfl⟩ : syracuseStep 1538963 = 2308445) B2308445
theorem B1538993 : Blo 1024605 1538993 := bstep (se 2 (by rfl) ⟨577122, by rfl⟩ : syracuseStep 1538993 = 1154245) B1154245
theorem B1539011 : Blo 1024605 1539011 := bstep (se 1 (by rfl) ⟨1154258, by rfl⟩ : syracuseStep 1539011 = 2308517) B2308517
theorem B1539041 : Blo 1024605 1539041 := bstep (se 2 (by rfl) ⟨577140, by rfl⟩ : syracuseStep 1539041 = 1154281) B1154281
theorem B17628131 : Blo 1024605 17628131 := bstep (se 1 (by rfl) ⟨13221098, by rfl⟩ : syracuseStep 17628131 = 26442197) B26442197
theorem B1539059 : Blo 1024605 1539059 := bstep (se 1 (by rfl) ⟨1154294, by rfl⟩ : syracuseStep 1539059 = 2308589) B2308589
theorem B1735681 : Blo 1024605 1735681 := bstep (se 2 (by rfl) ⟨650880, by rfl⟩ : syracuseStep 1735681 = 1301761) B1301761
theorem B1539089 : Blo 1024605 1539089 := bstep (se 2 (by rfl) ⟨577158, by rfl⟩ : syracuseStep 1539089 = 1154317) B1154317
theorem B1539107 : Blo 1024605 1539107 := bstep (se 1 (by rfl) ⟨1154330, by rfl⟩ : syracuseStep 1539107 = 2308661) B2308661
theorem B1735715 : Blo 1024605 1735715 := bstep (se 1 (by rfl) ⟨1301786, by rfl⟩ : syracuseStep 1735715 = 2603573) B2603573
theorem B1539137 : Blo 1024605 1539137 := bstep (se 2 (by rfl) ⟨577176, by rfl⟩ : syracuseStep 1539137 = 1154353) B1154353
theorem B7011397 : Blo 1024605 7011397 := bstep (se 4 (by rfl) ⟨657318, by rfl⟩ : syracuseStep 7011397 = 1314637) B1314637
theorem B1539155 : Blo 1024605 1539155 := bstep (se 1 (by rfl) ⟨1154366, by rfl⟩ : syracuseStep 1539155 = 2308733) B2308733
theorem B1539185 : Blo 1024605 1539185 := bstep (se 2 (by rfl) ⟨577194, by rfl⟩ : syracuseStep 1539185 = 1154389) B1154389
theorem B1539203 : Blo 1024605 1539203 := bstep (se 1 (by rfl) ⟨1154402, by rfl⟩ : syracuseStep 1539203 = 2308805) B2308805
theorem B2784397 : Blo 1024605 2784397 := bstep (se 3 (by rfl) ⟨522074, by rfl⟩ : syracuseStep 2784397 = 1044149) B1044149
theorem B1539233 : Blo 1024605 1539233 := bstep (se 2 (by rfl) ⟨577212, by rfl⟩ : syracuseStep 1539233 = 1154425) B1154425
theorem B1539251 : Blo 1024605 1539251 := bstep (se 1 (by rfl) ⟨1154438, by rfl⟩ : syracuseStep 1539251 = 2308877) B2308877
theorem B1539281 : Blo 1024605 1539281 := bstep (se 2 (by rfl) ⟨577230, by rfl⟩ : syracuseStep 1539281 = 1154461) B1154461
theorem B1539299 : Blo 1024605 1539299 := bstep (se 1 (by rfl) ⟨1154474, by rfl⟩ : syracuseStep 1539299 = 2308949) B2308949
theorem B14253283 : Blo 1024605 14253283 := bstep (se 1 (by rfl) ⟨10689962, by rfl⟩ : syracuseStep 14253283 = 21379925) B21379925
theorem B4390129 : Blo 1024605 4390129 := bstep (se 2 (by rfl) ⟨1646298, by rfl⟩ : syracuseStep 4390129 = 3292597) B3292597
theorem B1539329 : Blo 1024605 1539329 := bstep (se 2 (by rfl) ⟨577248, by rfl⟩ : syracuseStep 1539329 = 1154497) B1154497
theorem B1539347 : Blo 1024605 1539347 := bstep (se 1 (by rfl) ⟨1154510, by rfl⟩ : syracuseStep 1539347 = 2309021) B2309021
theorem B2194723 : Blo 1024605 2194723 := bstep (se 1 (by rfl) ⟨1646042, by rfl⟩ : syracuseStep 2194723 = 3292085) B3292085
theorem B1539377 : Blo 1024605 1539377 := bstep (se 2 (by rfl) ⟨577266, by rfl⟩ : syracuseStep 1539377 = 1154533) B1154533
theorem B11107637 : Blo 1024605 11107637 := bstep (se 5 (by rfl) ⟨520670, by rfl⟩ : syracuseStep 11107637 = 1041341) B1041341
theorem B1539395 : Blo 1024605 1539395 := bstep (se 1 (by rfl) ⟨1154546, by rfl⟩ : syracuseStep 1539395 = 2309093) B2309093
theorem B1539425 : Blo 1024605 1539425 := bstep (se 2 (by rfl) ⟨577284, by rfl⟩ : syracuseStep 1539425 = 1154569) B1154569
theorem B1408369 : Blo 1024605 1408369 := bstep (se 2 (by rfl) ⟨528138, by rfl⟩ : syracuseStep 1408369 = 1056277) B1056277
theorem B1539443 : Blo 1024605 1539443 := bstep (se 1 (by rfl) ⟨1154582, by rfl⟩ : syracuseStep 1539443 = 2309165) B2309165
theorem B1539473 : Blo 1024605 1539473 := bstep (se 2 (by rfl) ⟨577302, by rfl⟩ : syracuseStep 1539473 = 1154605) B1154605
theorem B1539491 : Blo 1024605 1539491 := bstep (se 1 (by rfl) ⟨1154618, by rfl⟩ : syracuseStep 1539491 = 2309237) B2309237
theorem B1539521 : Blo 1024605 1539521 := bstep (se 2 (by rfl) ⟨577320, by rfl⟩ : syracuseStep 1539521 = 1154641) B1154641
theorem B1539539 : Blo 1024605 1539539 := bstep (se 1 (by rfl) ⟨1154654, by rfl⟩ : syracuseStep 1539539 = 2309309) B2309309
theorem B1539569 : Blo 1024605 1539569 := bstep (se 2 (by rfl) ⟨577338, by rfl⟩ : syracuseStep 1539569 = 1154677) B1154677
theorem B1539587 : Blo 1024605 1539587 := bstep (se 1 (by rfl) ⟨1154690, by rfl⟩ : syracuseStep 1539587 = 2309381) B2309381
theorem B1539617 : Blo 1024605 1539617 := bstep (se 2 (by rfl) ⟨577356, by rfl⟩ : syracuseStep 1539617 = 1154713) B1154713
theorem B1539635 : Blo 1024605 1539635 := bstep (se 1 (by rfl) ⟨1154726, by rfl⟩ : syracuseStep 1539635 = 2309453) B2309453
theorem B1539665 : Blo 1024605 1539665 := bstep (se 2 (by rfl) ⟨577374, by rfl⟩ : syracuseStep 1539665 = 1154749) B1154749
theorem B1539683 : Blo 1024605 1539683 := bstep (se 1 (by rfl) ⟨1154762, by rfl⟩ : syracuseStep 1539683 = 2309525) B2309525
theorem B1539713 : Blo 1024605 1539713 := bstep (se 2 (by rfl) ⟨577392, by rfl⟩ : syracuseStep 1539713 = 1154785) B1154785
theorem B1539731 : Blo 1024605 1539731 := bstep (se 1 (by rfl) ⟨1154798, by rfl⟩ : syracuseStep 1539731 = 2309597) B2309597
theorem B1539761 : Blo 1024605 1539761 := bstep (se 2 (by rfl) ⟨577410, by rfl⟩ : syracuseStep 1539761 = 1154821) B1154821
theorem B1539779 : Blo 1024605 1539779 := bstep (se 1 (by rfl) ⟨1154834, by rfl⟩ : syracuseStep 1539779 = 2309669) B2309669
theorem B1539809 : Blo 1024605 1539809 := bstep (se 2 (by rfl) ⟨577428, by rfl⟩ : syracuseStep 1539809 = 1154857) B1154857
theorem B1539827 : Blo 1024605 1539827 := bstep (se 1 (by rfl) ⟨1154870, by rfl⟩ : syracuseStep 1539827 = 2309741) B2309741
theorem B1539857 : Blo 1024605 1539857 := bstep (se 2 (by rfl) ⟨577446, by rfl⟩ : syracuseStep 1539857 = 1154893) B1154893
theorem B1408801 : Blo 1024605 1408801 := bstep (se 2 (by rfl) ⟨528300, by rfl⟩ : syracuseStep 1408801 = 1056601) B1056601
theorem B1539875 : Blo 1024605 1539875 := bstep (se 1 (by rfl) ⟨1154906, by rfl⟩ : syracuseStep 1539875 = 2309813) B2309813
theorem B1539905 : Blo 1024605 1539905 := bstep (se 2 (by rfl) ⟨577464, by rfl⟩ : syracuseStep 1539905 = 1154929) B1154929
theorem B1539923 : Blo 1024605 1539923 := bstep (se 1 (by rfl) ⟨1154942, by rfl⟩ : syracuseStep 1539923 = 2309885) B2309885
theorem B1539953 : Blo 1024605 1539953 := bstep (se 2 (by rfl) ⟨577482, by rfl⟩ : syracuseStep 1539953 = 1154965) B1154965
theorem B1539971 : Blo 1024605 1539971 := bstep (se 1 (by rfl) ⟨1154978, by rfl⟩ : syracuseStep 1539971 = 2309957) B2309957
theorem B1540001 : Blo 1024605 1540001 := bstep (se 2 (by rfl) ⟨577500, by rfl⟩ : syracuseStep 1540001 = 1155001) B1155001
theorem B3899299 : Blo 1024605 3899299 := bstep (se 1 (by rfl) ⟨2924474, by rfl⟩ : syracuseStep 3899299 = 5848949) B5848949
theorem B1540019 : Blo 1024605 1540019 := bstep (se 1 (by rfl) ⟨1155014, by rfl⟩ : syracuseStep 1540019 = 2310029) B2310029
theorem B1540049 : Blo 1024605 1540049 := bstep (se 2 (by rfl) ⟨577518, by rfl⟩ : syracuseStep 1540049 = 1155037) B1155037
theorem B1540067 : Blo 1024605 1540067 := bstep (se 1 (by rfl) ⟨1155050, by rfl⟩ : syracuseStep 1540067 = 2310101) B2310101
theorem B2195441 : Blo 1024605 2195441 := bstep (se 2 (by rfl) ⟨823290, by rfl⟩ : syracuseStep 2195441 = 1646581) B1646581
theorem B1540121 : Blo 1024605 1540121 := bstep (se 2 (by rfl) ⟨577545, by rfl⟩ : syracuseStep 1540121 = 1155091) B1155091
theorem B2195543 : Blo 1024605 2195543 := bstep (se 1 (by rfl) ⟨1646657, by rfl⟩ : syracuseStep 2195543 = 3293315) B3293315
theorem B7897189 : Blo 1024605 7897189 := bstep (se 4 (by rfl) ⟨740361, by rfl⟩ : syracuseStep 7897189 = 1480723) B1480723
theorem B1540235 : Blo 1024605 1540235 := bstep (se 1 (by rfl) ⟨1155176, by rfl⟩ : syracuseStep 1540235 = 2310353) B2310353
theorem B1540247 : Blo 1024605 1540247 := bstep (se 1 (by rfl) ⟨1155185, by rfl⟩ : syracuseStep 1540247 = 2310371) B2310371
theorem B1540313 : Blo 1024605 1540313 := bstep (se 2 (by rfl) ⟨577617, by rfl⟩ : syracuseStep 1540313 = 1155235) B1155235
theorem B1540427 : Blo 1024605 1540427 := bstep (se 1 (by rfl) ⟨1155320, by rfl⟩ : syracuseStep 1540427 = 2310641) B2310641
theorem B1540439 : Blo 1024605 1540439 := bstep (se 1 (by rfl) ⟨1155329, by rfl⟩ : syracuseStep 1540439 = 2310659) B2310659
theorem B2195851 : Blo 1024605 2195851 := bstep (se 1 (by rfl) ⟨1646888, by rfl⟩ : syracuseStep 2195851 = 3293777) B3293777
theorem B1540505 : Blo 1024605 1540505 := bstep (se 2 (by rfl) ⟨577689, by rfl⟩ : syracuseStep 1540505 = 1155379) B1155379
theorem B1540619 : Blo 1024605 1540619 := bstep (se 1 (by rfl) ⟨1155464, by rfl⟩ : syracuseStep 1540619 = 2310929) B2310929
theorem B1540631 : Blo 1024605 1540631 := bstep (se 1 (by rfl) ⟨1155473, by rfl⟩ : syracuseStep 1540631 = 2310947) B2310947
theorem B1540697 : Blo 1024605 1540697 := bstep (se 2 (by rfl) ⟨577761, by rfl⟩ : syracuseStep 1540697 = 1155523) B1155523
theorem B4391617 : Blo 1024605 4391617 := bstep (se 2 (by rfl) ⟨1646856, by rfl⟩ : syracuseStep 4391617 = 3293713) B3293713
theorem B1540811 : Blo 1024605 1540811 := bstep (se 1 (by rfl) ⟨1155608, by rfl⟩ : syracuseStep 1540811 = 2311217) B2311217
theorem B1540823 : Blo 1024605 1540823 := bstep (se 1 (by rfl) ⟨1155617, by rfl⟩ : syracuseStep 1540823 = 2311235) B2311235
theorem B4064003 : Blo 1024605 4064003 := bstep (se 1 (by rfl) ⟨3048002, by rfl⟩ : syracuseStep 4064003 = 6096005) B6096005
theorem B1540889 : Blo 1024605 1540889 := bstep (se 2 (by rfl) ⟨577833, by rfl⟩ : syracuseStep 1540889 = 1155667) B1155667
theorem B1541003 : Blo 1024605 1541003 := bstep (se 1 (by rfl) ⟨1155752, by rfl⟩ : syracuseStep 1541003 = 2311505) B2311505
theorem B1541015 : Blo 1024605 1541015 := bstep (se 1 (by rfl) ⟨1155761, by rfl⟩ : syracuseStep 1541015 = 2311523) B2311523
theorem B10552241 : Blo 1024605 10552241 := bstep (se 2 (by rfl) ⟨3957090, by rfl⟩ : syracuseStep 10552241 = 7914181) B7914181
theorem B1541081 : Blo 1024605 1541081 := bstep (se 2 (by rfl) ⟨577905, by rfl⟩ : syracuseStep 1541081 = 1155811) B1155811
theorem B7799813 : Blo 1024605 7799813 := bstep (se 4 (by rfl) ⟨731232, by rfl⟩ : syracuseStep 7799813 = 1462465) B1462465
theorem B1541195 : Blo 1024605 1541195 := bstep (se 1 (by rfl) ⟨1155896, by rfl⟩ : syracuseStep 1541195 = 2311793) B2311793
theorem B1541207 : Blo 1024605 1541207 := bstep (se 1 (by rfl) ⟨1155905, by rfl⟩ : syracuseStep 1541207 = 2311811) B2311811
theorem B1541273 : Blo 1024605 1541273 := bstep (se 2 (by rfl) ⟨577977, by rfl⟩ : syracuseStep 1541273 = 1155955) B1155955
theorem B1541387 : Blo 1024605 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B1541399 : Blo 1024605 1541399 := bstep (se 1 (by rfl) ⟨1156049, by rfl⟩ : syracuseStep 1541399 = 2312099) B2312099
theorem B4392215 : Blo 1024605 4392215 := bstep (se 1 (by rfl) ⟨3294161, by rfl⟩ : syracuseStep 4392215 = 6588323) B6588323
theorem B1541465 : Blo 1024605 1541465 := bstep (se 2 (by rfl) ⟨578049, by rfl⟩ : syracuseStep 1541465 = 1156099) B1156099
theorem B1541579 : Blo 1024605 1541579 := bstep (se 1 (by rfl) ⟨1156184, by rfl⟩ : syracuseStep 1541579 = 2312369) B2312369
theorem B1541591 : Blo 1024605 1541591 := bstep (se 1 (by rfl) ⟨1156193, by rfl⟩ : syracuseStep 1541591 = 2312387) B2312387
theorem B1541657 : Blo 1024605 1541657 := bstep (se 2 (by rfl) ⟨578121, by rfl⟩ : syracuseStep 1541657 = 1156243) B1156243
theorem B1541771 : Blo 1024605 1541771 := bstep (se 1 (by rfl) ⟨1156328, by rfl⟩ : syracuseStep 1541771 = 2312657) B2312657
theorem B1541783 : Blo 1024605 1541783 := bstep (se 1 (by rfl) ⟨1156337, by rfl⟩ : syracuseStep 1541783 = 2312675) B2312675
theorem B1541849 : Blo 1024605 1541849 := bstep (se 2 (by rfl) ⟨578193, by rfl⟩ : syracuseStep 1541849 = 1156387) B1156387
theorem B3901229 : Blo 1024605 3901229 := bstep (se 3 (by rfl) ⟨731480, by rfl⟩ : syracuseStep 3901229 = 1462961) B1462961
theorem B1541963 : Blo 1024605 1541963 := bstep (se 1 (by rfl) ⟨1156472, by rfl⟩ : syracuseStep 1541963 = 2312945) B2312945
theorem B1541975 : Blo 1024605 1541975 := bstep (se 1 (by rfl) ⟨1156481, by rfl⟩ : syracuseStep 1541975 = 2312963) B2312963
theorem B4163417 : Blo 1024605 4163417 := bstep (se 2 (by rfl) ⟨1561281, by rfl⟩ : syracuseStep 4163417 = 3122563) B3122563
theorem B1542041 : Blo 1024605 1542041 := bstep (se 2 (by rfl) ⟨578265, by rfl⟩ : syracuseStep 1542041 = 1156531) B1156531
theorem B1542155 : Blo 1024605 1542155 := bstep (se 1 (by rfl) ⟨1156616, by rfl⟩ : syracuseStep 1542155 = 2313233) B2313233
theorem B1542167 : Blo 1024605 1542167 := bstep (se 1 (by rfl) ⟨1156625, by rfl⟩ : syracuseStep 1542167 = 2313251) B2313251
theorem B1542233 : Blo 1024605 1542233 := bstep (se 2 (by rfl) ⟨578337, by rfl⟩ : syracuseStep 1542233 = 1156675) B1156675
theorem B3705011 : Blo 1024605 3705011 := bstep (se 1 (by rfl) ⟨2778758, by rfl⟩ : syracuseStep 3705011 = 5557517) B5557517
theorem B1542347 : Blo 1024605 1542347 := bstep (se 1 (by rfl) ⟨1156760, by rfl⟩ : syracuseStep 1542347 = 2313521) B2313521
theorem B1542359 : Blo 1024605 1542359 := bstep (se 1 (by rfl) ⟨1156769, by rfl⟩ : syracuseStep 1542359 = 2313539) B2313539
theorem B1542425 : Blo 1024605 1542425 := bstep (se 2 (by rfl) ⟨578409, by rfl⟩ : syracuseStep 1542425 = 1156819) B1156819
theorem B1542539 : Blo 1024605 1542539 := bstep (se 1 (by rfl) ⟨1156904, by rfl⟩ : syracuseStep 1542539 = 2313809) B2313809
theorem B1542551 : Blo 1024605 1542551 := bstep (se 1 (by rfl) ⟨1156913, by rfl⟩ : syracuseStep 1542551 = 2313827) B2313827
theorem B1542617 : Blo 1024605 1542617 := bstep (se 2 (by rfl) ⟨578481, by rfl⟩ : syracuseStep 1542617 = 1156963) B1156963
theorem B3902003 : Blo 1024605 3902003 := bstep (se 1 (by rfl) ⟨2926502, by rfl⟩ : syracuseStep 3902003 = 5853005) B5853005
theorem B1542731 : Blo 1024605 1542731 := bstep (se 1 (by rfl) ⟨1157048, by rfl⟩ : syracuseStep 1542731 = 2314097) B2314097
theorem B4393547 : Blo 1024605 4393547 := bstep (se 1 (by rfl) ⟨3295160, by rfl⟩ : syracuseStep 4393547 = 6590321) B6590321
theorem B1542743 : Blo 1024605 1542743 := bstep (se 1 (by rfl) ⟨1157057, by rfl⟩ : syracuseStep 1542743 = 2314115) B2314115
theorem B1542809 : Blo 1024605 1542809 := bstep (se 2 (by rfl) ⟨578553, by rfl⟩ : syracuseStep 1542809 = 1157107) B1157107
theorem B2919361 : Blo 1024605 2919361 := bstep (se 2 (by rfl) ⟨1094760, by rfl⟩ : syracuseStep 2919361 = 2189521) B2189521
theorem B3116249 : Blo 1024605 3116249 := bstep (se 2 (by rfl) ⟨1168593, by rfl⟩ : syracuseStep 3116249 = 2337187) B2337187
theorem B8326475 : Blo 1024605 8326475 := bstep (se 1 (by rfl) ⟨6244856, by rfl⟩ : syracuseStep 8326475 = 12489713) B12489713
theorem B7802243 : Blo 1024605 7802243 := bstep (se 1 (by rfl) ⟨5851682, by rfl⟩ : syracuseStep 7802243 = 11703365) B11703365
theorem B8326577 : Blo 1024605 8326577 := bstep (se 2 (by rfl) ⟨3122466, by rfl⟩ : syracuseStep 8326577 = 6244933) B6244933
theorem B1642007 : Blo 1024605 1642007 := bstep (se 1 (by rfl) ⟨1231505, by rfl⟩ : syracuseStep 1642007 = 2463011) B2463011
theorem B3903491 : Blo 1024605 3903491 := bstep (se 1 (by rfl) ⟨2927618, by rfl⟩ : syracuseStep 3903491 = 5855237) B5855237
theorem B3903947 : Blo 1024605 3903947 := bstep (se 1 (by rfl) ⟨2927960, by rfl⟩ : syracuseStep 3903947 = 5855921) B5855921
theorem B2921035 : Blo 1024605 2921035 := bstep (se 1 (by rfl) ⟨2190776, by rfl⟩ : syracuseStep 2921035 = 4381553) B4381553
theorem B4690507 : Blo 1024605 4690507 := bstep (se 1 (by rfl) ⟨3517880, by rfl⟩ : syracuseStep 4690507 = 7035761) B7035761
theorem B1643095 : Blo 1024605 1643095 := bstep (se 1 (by rfl) ⟨1232321, by rfl⟩ : syracuseStep 1643095 = 2464643) B2464643
theorem B3904145 : Blo 1024605 3904145 := bstep (se 2 (by rfl) ⟨1464054, by rfl⟩ : syracuseStep 3904145 = 2928109) B2928109
theorem B4690649 : Blo 1024605 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B2593559 : Blo 1024605 2593559 := bstep (se 1 (by rfl) ⟨1945169, by rfl⟩ : syracuseStep 2593559 = 3890339) B3890339
theorem B2921309 : Blo 1024605 2921309 := bstep (se 3 (by rfl) ⟨547745, by rfl⟩ : syracuseStep 2921309 = 1095491) B1095491
theorem B8786819 : Blo 1024605 8786819 := bstep (se 1 (by rfl) ⟨6590114, by rfl⟩ : syracuseStep 8786819 = 13180229) B13180229
theorem B3118027 : Blo 1024605 3118027 := bstep (se 1 (by rfl) ⟨2338520, by rfl⟩ : syracuseStep 3118027 = 4677041) B4677041
theorem B4166873 : Blo 1024605 4166873 := bstep (se 2 (by rfl) ⟨1562577, by rfl⟩ : syracuseStep 4166873 = 3125155) B3125155
theorem B3904919 : Blo 1024605 3904919 := bstep (se 1 (by rfl) ⟨2928689, by rfl⟩ : syracuseStep 3904919 = 5857379) B5857379
theorem B2594227 : Blo 1024605 2594227 := bstep (se 1 (by rfl) ⟨1945670, by rfl⟩ : syracuseStep 2594227 = 3891341) B3891341
theorem B2594369 : Blo 1024605 2594369 := bstep (se 2 (by rfl) ⟨972888, by rfl⟩ : syracuseStep 2594369 = 1945777) B1945777
theorem B3905117 : Blo 1024605 3905117 := bstep (se 3 (by rfl) ⟨732209, by rfl⟩ : syracuseStep 3905117 = 1464419) B1464419
theorem B8001125 : Blo 1024605 8001125 := bstep (se 4 (by rfl) ⟨750105, by rfl⟩ : syracuseStep 8001125 = 1500211) B1500211
theorem B1152715 : Blo 1024605 1152715 := bstep (se 1 (by rfl) ⟨864536, by rfl⟩ : syracuseStep 1152715 = 1729073) B1729073
theorem B3282653 : Blo 1024605 3282653 := bstep (se 3 (by rfl) ⟨615497, by rfl⟩ : syracuseStep 3282653 = 1230995) B1230995
theorem B4167389 : Blo 1024605 4167389 := bstep (se 3 (by rfl) ⟨781385, by rfl⟩ : syracuseStep 4167389 = 1562771) B1562771
theorem B1644313 : Blo 1024605 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B1152823 : Blo 1024605 1152823 := bstep (se 1 (by rfl) ⟨864617, by rfl⟩ : syracuseStep 1152823 = 1729235) B1729235
theorem B5838743 : Blo 1024605 5838743 := bstep (se 1 (by rfl) ⟨4379057, by rfl⟩ : syracuseStep 5838743 = 8758115) B8758115
theorem B1153003 : Blo 1024605 1153003 := bstep (se 1 (by rfl) ⟨864752, by rfl⟩ : syracuseStep 1153003 = 1729505) B1729505
theorem B1153111 : Blo 1024605 1153111 := bstep (se 1 (by rfl) ⟨864833, by rfl⟩ : syracuseStep 1153111 = 1729667) B1729667
theorem B1153291 : Blo 1024605 1153291 := bstep (se 1 (by rfl) ⟨864968, by rfl⟩ : syracuseStep 1153291 = 1729937) B1729937
theorem B1153399 : Blo 1024605 1153399 := bstep (se 1 (by rfl) ⟨865049, by rfl⟩ : syracuseStep 1153399 = 1730099) B1730099
theorem B1153579 : Blo 1024605 1153579 := bstep (se 1 (by rfl) ⟨865184, by rfl⟩ : syracuseStep 1153579 = 1730369) B1730369
theorem B3119705 : Blo 1024605 3119705 := bstep (se 2 (by rfl) ⟨1169889, by rfl⟩ : syracuseStep 3119705 = 2339779) B2339779
theorem B1153687 : Blo 1024605 1153687 := bstep (se 1 (by rfl) ⟨865265, by rfl⟩ : syracuseStep 1153687 = 1730531) B1730531
theorem B7805645 : Blo 1024605 7805645 := bstep (se 3 (by rfl) ⟨1463558, by rfl⟩ : syracuseStep 7805645 = 2927117) B2927117
theorem B2595635 : Blo 1024605 2595635 := bstep (se 1 (by rfl) ⟨1946726, by rfl⟩ : syracuseStep 2595635 = 3893453) B3893453
theorem B1153867 : Blo 1024605 1153867 := bstep (se 1 (by rfl) ⟨865400, by rfl⟩ : syracuseStep 1153867 = 1730801) B1730801
theorem B8887171 : Blo 1024605 8887171 := bstep (se 1 (by rfl) ⟨6665378, by rfl⟩ : syracuseStep 8887171 = 13330757) B13330757
theorem B1153975 : Blo 1024605 1153975 := bstep (se 1 (by rfl) ⟨865481, by rfl⟩ : syracuseStep 1153975 = 1730963) B1730963
theorem B1186795 : Blo 1024605 1186795 := bstep (se 1 (by rfl) ⟨890096, by rfl⟩ : syracuseStep 1186795 = 1780193) B1780193
theorem B2923609 : Blo 1024605 2923609 := bstep (se 2 (by rfl) ⟨1096353, by rfl⟩ : syracuseStep 2923609 = 2192707) B2192707
theorem B1154155 : Blo 1024605 1154155 := bstep (se 1 (by rfl) ⟨865616, by rfl⟩ : syracuseStep 1154155 = 1731233) B1731233
theorem B7806131 : Blo 1024605 7806131 := bstep (se 1 (by rfl) ⟨5854598, by rfl⟩ : syracuseStep 7806131 = 11709197) B11709197
theorem B1154263 : Blo 1024605 1154263 := bstep (se 1 (by rfl) ⟨865697, by rfl⟩ : syracuseStep 1154263 = 1731395) B1731395
theorem B2596171 : Blo 1024605 2596171 := bstep (se 1 (by rfl) ⟨1947128, by rfl⟩ : syracuseStep 2596171 = 3894257) B3894257
theorem B1154443 : Blo 1024605 1154443 := bstep (se 1 (by rfl) ⟨865832, by rfl⟩ : syracuseStep 1154443 = 1731665) B1731665
theorem B2596313 : Blo 1024605 2596313 := bstep (se 2 (by rfl) ⟨973617, by rfl⟩ : syracuseStep 2596313 = 1947235) B1947235
theorem B1154551 : Blo 1024605 1154551 := bstep (se 1 (by rfl) ⟨865913, by rfl⟩ : syracuseStep 1154551 = 1731827) B1731827
theorem B1154731 : Blo 1024605 1154731 := bstep (se 1 (by rfl) ⟨866048, by rfl⟩ : syracuseStep 1154731 = 1732097) B1732097
theorem B2924225 : Blo 1024605 2924225 := bstep (se 2 (by rfl) ⟨1096584, by rfl⟩ : syracuseStep 2924225 = 2193169) B2193169
theorem B5840657 : Blo 1024605 5840657 := bstep (se 2 (by rfl) ⟨2190246, by rfl⟩ : syracuseStep 5840657 = 4380493) B4380493
theorem B1154839 : Blo 1024605 1154839 := bstep (se 1 (by rfl) ⟨866129, by rfl⟩ : syracuseStep 1154839 = 1732259) B1732259
theorem B1155019 : Blo 1024605 1155019 := bstep (se 1 (by rfl) ⟨866264, by rfl⟩ : syracuseStep 1155019 = 1732529) B1732529
theorem B9510929 : Blo 1024605 9510929 := bstep (se 2 (by rfl) ⟨3566598, by rfl⟩ : syracuseStep 9510929 = 7133197) B7133197
theorem B1155127 : Blo 1024605 1155127 := bstep (se 1 (by rfl) ⟨866345, by rfl⟩ : syracuseStep 1155127 = 1732691) B1732691
theorem B18980939 : Blo 1024605 18980939 := bstep (se 1 (by rfl) ⟨14235704, by rfl⟩ : syracuseStep 18980939 = 28471409) B28471409
theorem B13705421 : Blo 1024605 13705421 := bstep (se 3 (by rfl) ⟨2569766, by rfl⟩ : syracuseStep 13705421 = 5139533) B5139533
theorem B1155307 : Blo 1024605 1155307 := bstep (se 1 (by rfl) ⟨866480, by rfl⟩ : syracuseStep 1155307 = 1732961) B1732961
theorem B2597143 : Blo 1024605 2597143 := bstep (se 1 (by rfl) ⟨1947857, by rfl⟩ : syracuseStep 2597143 = 3895715) B3895715
theorem B1155415 : Blo 1024605 1155415 := bstep (se 1 (by rfl) ⟨866561, by rfl⟩ : syracuseStep 1155415 = 1733123) B1733123
theorem B1155595 : Blo 1024605 1155595 := bstep (se 1 (by rfl) ⟨866696, by rfl⟩ : syracuseStep 1155595 = 1733393) B1733393
theorem B4497995 : Blo 1024605 4497995 := bstep (se 1 (by rfl) ⟨3373496, by rfl⟩ : syracuseStep 4497995 = 6746993) B6746993
theorem B11674205 : Blo 1024605 11674205 := bstep (se 3 (by rfl) ⟨2188913, by rfl⟩ : syracuseStep 11674205 = 4377827) B4377827
theorem B7807589 : Blo 1024605 7807589 := bstep (se 4 (by rfl) ⟨731961, by rfl⟩ : syracuseStep 7807589 = 1463923) B1463923
theorem B1024619 : Blo 1024605 1024619 := bstep (se 1 (by rfl) ⟨768464, by rfl⟩ : syracuseStep 1024619 = 1536929) B1536929
theorem B1024631 : Blo 1024605 1024631 := bstep (se 1 (by rfl) ⟨768473, by rfl⟩ : syracuseStep 1024631 = 1536947) B1536947
theorem B1155703 : Blo 1024605 1155703 := bstep (se 1 (by rfl) ⟨866777, by rfl⟩ : syracuseStep 1155703 = 1733555) B1733555
theorem B1024651 : Blo 1024605 1024651 := bstep (se 1 (by rfl) ⟨768488, by rfl⟩ : syracuseStep 1024651 = 1536977) B1536977
theorem B1024663 : Blo 1024605 1024663 := bstep (se 1 (by rfl) ⟨768497, by rfl⟩ : syracuseStep 1024663 = 1536995) B1536995
theorem B1024683 : Blo 1024605 1024683 := bstep (se 1 (by rfl) ⟨768512, by rfl⟩ : syracuseStep 1024683 = 1537025) B1537025
theorem B1024695 : Blo 1024605 1024695 := bstep (se 1 (by rfl) ⟨768521, by rfl⟩ : syracuseStep 1024695 = 1537043) B1537043
theorem B1024715 : Blo 1024605 1024715 := bstep (se 1 (by rfl) ⟨768536, by rfl⟩ : syracuseStep 1024715 = 1537073) B1537073
theorem B2597579 : Blo 1024605 2597579 := bstep (se 1 (by rfl) ⟨1948184, by rfl⟩ : syracuseStep 2597579 = 3896369) B3896369
theorem B1024727 : Blo 1024605 1024727 := bstep (se 1 (by rfl) ⟨768545, by rfl⟩ : syracuseStep 1024727 = 1537091) B1537091
theorem B1024747 : Blo 1024605 1024747 := bstep (se 1 (by rfl) ⟨768560, by rfl⟩ : syracuseStep 1024747 = 1537121) B1537121
theorem B1024759 : Blo 1024605 1024759 := bstep (se 1 (by rfl) ⟨768569, by rfl⟩ : syracuseStep 1024759 = 1537139) B1537139
theorem B1024779 : Blo 1024605 1024779 := bstep (se 1 (by rfl) ⟨768584, by rfl⟩ : syracuseStep 1024779 = 1537169) B1537169
theorem B1024791 : Blo 1024605 1024791 := bstep (se 1 (by rfl) ⟨768593, by rfl⟩ : syracuseStep 1024791 = 1537187) B1537187
theorem B1024811 : Blo 1024605 1024811 := bstep (se 1 (by rfl) ⟨768608, by rfl⟩ : syracuseStep 1024811 = 1537217) B1537217
theorem B1155883 : Blo 1024605 1155883 := bstep (se 1 (by rfl) ⟨866912, by rfl⟩ : syracuseStep 1155883 = 1733825) B1733825
theorem B1024823 : Blo 1024605 1024823 := bstep (se 1 (by rfl) ⟨768617, by rfl⟩ : syracuseStep 1024823 = 1537235) B1537235
theorem B1024843 : Blo 1024605 1024843 := bstep (se 1 (by rfl) ⟨768632, by rfl⟩ : syracuseStep 1024843 = 1537265) B1537265
theorem B1024855 : Blo 1024605 1024855 := bstep (se 1 (by rfl) ⟨768641, by rfl⟩ : syracuseStep 1024855 = 1537283) B1537283
theorem B1024875 : Blo 1024605 1024875 := bstep (se 1 (by rfl) ⟨768656, by rfl⟩ : syracuseStep 1024875 = 1537313) B1537313
theorem B1024887 : Blo 1024605 1024887 := bstep (se 1 (by rfl) ⟨768665, by rfl⟩ : syracuseStep 1024887 = 1537331) B1537331
theorem B1024907 : Blo 1024605 1024907 := bstep (se 1 (by rfl) ⟨768680, by rfl⟩ : syracuseStep 1024907 = 1537361) B1537361
theorem B1024919 : Blo 1024605 1024919 := bstep (se 1 (by rfl) ⟨768689, by rfl⟩ : syracuseStep 1024919 = 1537379) B1537379
theorem B1155991 : Blo 1024605 1155991 := bstep (se 1 (by rfl) ⟨866993, by rfl⟩ : syracuseStep 1155991 = 1733987) B1733987
theorem B1024939 : Blo 1024605 1024939 := bstep (se 1 (by rfl) ⟨768704, by rfl⟩ : syracuseStep 1024939 = 1537409) B1537409
theorem B1024951 : Blo 1024605 1024951 := bstep (se 1 (by rfl) ⟨768713, by rfl⟩ : syracuseStep 1024951 = 1537427) B1537427
theorem B1024971 : Blo 1024605 1024971 := bstep (se 1 (by rfl) ⟨768728, by rfl⟩ : syracuseStep 1024971 = 1537457) B1537457
theorem B1024983 : Blo 1024605 1024983 := bstep (se 1 (by rfl) ⟨768737, by rfl⟩ : syracuseStep 1024983 = 1537475) B1537475
theorem B1025003 : Blo 1024605 1025003 := bstep (se 1 (by rfl) ⟨768752, by rfl⟩ : syracuseStep 1025003 = 1537505) B1537505
theorem B1025015 : Blo 1024605 1025015 := bstep (se 1 (by rfl) ⟨768761, by rfl⟩ : syracuseStep 1025015 = 1537523) B1537523
theorem B1025035 : Blo 1024605 1025035 := bstep (se 1 (by rfl) ⟨768776, by rfl⟩ : syracuseStep 1025035 = 1537553) B1537553
theorem B1025047 : Blo 1024605 1025047 := bstep (se 1 (by rfl) ⟨768785, by rfl⟩ : syracuseStep 1025047 = 1537571) B1537571
theorem B1025067 : Blo 1024605 1025067 := bstep (se 1 (by rfl) ⟨768800, by rfl⟩ : syracuseStep 1025067 = 1537601) B1537601
theorem B1025079 : Blo 1024605 1025079 := bstep (se 1 (by rfl) ⟨768809, by rfl⟩ : syracuseStep 1025079 = 1537619) B1537619
theorem B2597953 : Blo 1024605 2597953 := bstep (se 2 (by rfl) ⟨974232, by rfl⟩ : syracuseStep 2597953 = 1948465) B1948465
theorem B1025099 : Blo 1024605 1025099 := bstep (se 1 (by rfl) ⟨768824, by rfl⟩ : syracuseStep 1025099 = 1537649) B1537649
theorem B1156171 : Blo 1024605 1156171 := bstep (se 1 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 1156171 = 1734257) B1734257
theorem B7808075 : Blo 1024605 7808075 := bstep (se 1 (by rfl) ⟨5856056, by rfl⟩ : syracuseStep 7808075 = 11712113) B11712113
theorem B1025111 : Blo 1024605 1025111 := bstep (se 1 (by rfl) ⟨768833, by rfl⟩ : syracuseStep 1025111 = 1537667) B1537667
theorem B1025131 : Blo 1024605 1025131 := bstep (se 1 (by rfl) ⟨768848, by rfl⟩ : syracuseStep 1025131 = 1537697) B1537697
theorem B1025143 : Blo 1024605 1025143 := bstep (se 1 (by rfl) ⟨768857, by rfl⟩ : syracuseStep 1025143 = 1537715) B1537715
theorem B1025163 : Blo 1024605 1025163 := bstep (se 1 (by rfl) ⟨768872, by rfl⟩ : syracuseStep 1025163 = 1537745) B1537745
theorem B1025175 : Blo 1024605 1025175 := bstep (se 1 (by rfl) ⟨768881, by rfl⟩ : syracuseStep 1025175 = 1537763) B1537763
theorem B1025195 : Blo 1024605 1025195 := bstep (se 1 (by rfl) ⟨768896, by rfl⟩ : syracuseStep 1025195 = 1537793) B1537793
theorem B1025207 : Blo 1024605 1025207 := bstep (se 1 (by rfl) ⟨768905, by rfl⟩ : syracuseStep 1025207 = 1537811) B1537811
theorem B1156279 : Blo 1024605 1156279 := bstep (se 1 (by rfl) ⟨867209, by rfl⟩ : syracuseStep 1156279 = 1734419) B1734419
theorem B1025227 : Blo 1024605 1025227 := bstep (se 1 (by rfl) ⟨768920, by rfl⟩ : syracuseStep 1025227 = 1537841) B1537841
theorem B1025239 : Blo 1024605 1025239 := bstep (se 1 (by rfl) ⟨768929, by rfl⟩ : syracuseStep 1025239 = 1537859) B1537859
theorem B1385687 : Blo 1024605 1385687 := bstep (se 1 (by rfl) ⟨1039265, by rfl⟩ : syracuseStep 1385687 = 2078531) B2078531
theorem B1025259 : Blo 1024605 1025259 := bstep (se 1 (by rfl) ⟨768944, by rfl⟩ : syracuseStep 1025259 = 1537889) B1537889
theorem B1025271 : Blo 1024605 1025271 := bstep (se 1 (by rfl) ⟨768953, by rfl⟩ : syracuseStep 1025271 = 1537907) B1537907
theorem B1025291 : Blo 1024605 1025291 := bstep (se 1 (by rfl) ⟨768968, by rfl⟩ : syracuseStep 1025291 = 1537937) B1537937
theorem B1025303 : Blo 1024605 1025303 := bstep (se 1 (by rfl) ⟨768977, by rfl⟩ : syracuseStep 1025303 = 1537955) B1537955
theorem B1025323 : Blo 1024605 1025323 := bstep (se 1 (by rfl) ⟨768992, by rfl⟩ : syracuseStep 1025323 = 1537985) B1537985
theorem B1025335 : Blo 1024605 1025335 := bstep (se 1 (by rfl) ⟨769001, by rfl⟩ : syracuseStep 1025335 = 1538003) B1538003
theorem B1025355 : Blo 1024605 1025355 := bstep (se 1 (by rfl) ⟨769016, by rfl⟩ : syracuseStep 1025355 = 1538033) B1538033
theorem B1025367 : Blo 1024605 1025367 := bstep (se 1 (by rfl) ⟨769025, by rfl⟩ : syracuseStep 1025367 = 1538051) B1538051
theorem B16885093 : Blo 1024605 16885093 := bstep (se 4 (by rfl) ⟨1582977, by rfl⟩ : syracuseStep 16885093 = 3165955) B3165955
theorem B1025387 : Blo 1024605 1025387 := bstep (se 1 (by rfl) ⟨769040, by rfl⟩ : syracuseStep 1025387 = 1538081) B1538081
theorem B1156459 : Blo 1024605 1156459 := bstep (se 1 (by rfl) ⟨867344, by rfl⟩ : syracuseStep 1156459 = 1734689) B1734689
theorem B1025399 : Blo 1024605 1025399 := bstep (se 1 (by rfl) ⟨769049, by rfl⟩ : syracuseStep 1025399 = 1538099) B1538099
theorem B1025419 : Blo 1024605 1025419 := bstep (se 1 (by rfl) ⟨769064, by rfl⟩ : syracuseStep 1025419 = 1538129) B1538129
theorem B1025431 : Blo 1024605 1025431 := bstep (se 1 (by rfl) ⟨769073, by rfl⟩ : syracuseStep 1025431 = 1538147) B1538147
theorem B1025451 : Blo 1024605 1025451 := bstep (se 1 (by rfl) ⟨769088, by rfl⟩ : syracuseStep 1025451 = 1538177) B1538177
theorem B9348529 : Blo 1024605 9348529 := bstep (se 2 (by rfl) ⟨3505698, by rfl⟩ : syracuseStep 9348529 = 7011397) B7011397
theorem B1025463 : Blo 1024605 1025463 := bstep (se 1 (by rfl) ⟨769097, by rfl⟩ : syracuseStep 1025463 = 1538195) B1538195
theorem B1025483 : Blo 1024605 1025483 := bstep (se 1 (by rfl) ⟨769112, by rfl⟩ : syracuseStep 1025483 = 1538225) B1538225
theorem B1025495 : Blo 1024605 1025495 := bstep (se 1 (by rfl) ⟨769121, by rfl⟩ : syracuseStep 1025495 = 1538243) B1538243
theorem B1156567 : Blo 1024605 1156567 := bstep (se 1 (by rfl) ⟨867425, by rfl⟩ : syracuseStep 1156567 = 1734851) B1734851
theorem B1025515 : Blo 1024605 1025515 := bstep (se 1 (by rfl) ⟨769136, by rfl⟩ : syracuseStep 1025515 = 1538273) B1538273
theorem B1025527 : Blo 1024605 1025527 := bstep (se 1 (by rfl) ⟨769145, by rfl⟩ : syracuseStep 1025527 = 1538291) B1538291
theorem B1025547 : Blo 1024605 1025547 := bstep (se 1 (by rfl) ⟨769160, by rfl⟩ : syracuseStep 1025547 = 1538321) B1538321
theorem B3712529 : Blo 1024605 3712529 := bstep (se 2 (by rfl) ⟨1392198, by rfl⟩ : syracuseStep 3712529 = 2784397) B2784397
theorem B1025559 : Blo 1024605 1025559 := bstep (se 1 (by rfl) ⟨769169, by rfl⟩ : syracuseStep 1025559 = 1538339) B1538339
theorem B1025579 : Blo 1024605 1025579 := bstep (se 1 (by rfl) ⟨769184, by rfl⟩ : syracuseStep 1025579 = 1538369) B1538369
theorem B1025591 : Blo 1024605 1025591 := bstep (se 1 (by rfl) ⟨769193, by rfl⟩ : syracuseStep 1025591 = 1538387) B1538387
theorem B1025611 : Blo 1024605 1025611 := bstep (se 1 (by rfl) ⟨769208, by rfl⟩ : syracuseStep 1025611 = 1538417) B1538417
theorem B1025623 : Blo 1024605 1025623 := bstep (se 1 (by rfl) ⟨769217, by rfl⟩ : syracuseStep 1025623 = 1538435) B1538435
theorem B1025643 : Blo 1024605 1025643 := bstep (se 1 (by rfl) ⟨769232, by rfl⟩ : syracuseStep 1025643 = 1538465) B1538465
theorem B1025655 : Blo 1024605 1025655 := bstep (se 1 (by rfl) ⟨769241, by rfl⟩ : syracuseStep 1025655 = 1538483) B1538483
theorem B1025675 : Blo 1024605 1025675 := bstep (se 1 (by rfl) ⟨769256, by rfl⟩ : syracuseStep 1025675 = 1538513) B1538513
theorem B1156747 : Blo 1024605 1156747 := bstep (se 1 (by rfl) ⟨867560, by rfl⟩ : syracuseStep 1156747 = 1735121) B1735121
theorem B1025687 : Blo 1024605 1025687 := bstep (se 1 (by rfl) ⟨769265, by rfl⟩ : syracuseStep 1025687 = 1538531) B1538531
theorem B2598551 : Blo 1024605 2598551 := bstep (se 1 (by rfl) ⟨1948913, by rfl⟩ : syracuseStep 2598551 = 3897827) B3897827
theorem B1025707 : Blo 1024605 1025707 := bstep (se 1 (by rfl) ⟨769280, by rfl⟩ : syracuseStep 1025707 = 1538561) B1538561
theorem B1025719 : Blo 1024605 1025719 := bstep (se 1 (by rfl) ⟨769289, by rfl⟩ : syracuseStep 1025719 = 1538579) B1538579
theorem B1025739 : Blo 1024605 1025739 := bstep (se 1 (by rfl) ⟨769304, by rfl⟩ : syracuseStep 1025739 = 1538609) B1538609
theorem B1025751 : Blo 1024605 1025751 := bstep (se 1 (by rfl) ⟨769313, by rfl⟩ : syracuseStep 1025751 = 1538627) B1538627
theorem B2926297 : Blo 1024605 2926297 := bstep (se 2 (by rfl) ⟨1097361, by rfl⟩ : syracuseStep 2926297 = 2194723) B2194723
theorem B1025771 : Blo 1024605 1025771 := bstep (se 1 (by rfl) ⟨769328, by rfl⟩ : syracuseStep 1025771 = 1538657) B1538657
theorem B1025783 : Blo 1024605 1025783 := bstep (se 1 (by rfl) ⟨769337, by rfl⟩ : syracuseStep 1025783 = 1538675) B1538675
theorem B1156855 : Blo 1024605 1156855 := bstep (se 1 (by rfl) ⟨867641, by rfl⟩ : syracuseStep 1156855 = 1735283) B1735283
theorem B1025803 : Blo 1024605 1025803 := bstep (se 1 (by rfl) ⟨769352, by rfl⟩ : syracuseStep 1025803 = 1538705) B1538705
theorem B1025815 : Blo 1024605 1025815 := bstep (se 1 (by rfl) ⟨769361, by rfl⟩ : syracuseStep 1025815 = 1538723) B1538723
theorem B1025835 : Blo 1024605 1025835 := bstep (se 1 (by rfl) ⟨769376, by rfl⟩ : syracuseStep 1025835 = 1538753) B1538753
theorem B1025847 : Blo 1024605 1025847 := bstep (se 1 (by rfl) ⟨769385, by rfl⟩ : syracuseStep 1025847 = 1538771) B1538771
theorem B1877825 : Blo 1024605 1877825 := bstep (se 2 (by rfl) ⟨704184, by rfl⟩ : syracuseStep 1877825 = 1408369) B1408369
theorem B1025867 : Blo 1024605 1025867 := bstep (se 1 (by rfl) ⟨769400, by rfl⟩ : syracuseStep 1025867 = 1538801) B1538801
theorem B1025879 : Blo 1024605 1025879 := bstep (se 1 (by rfl) ⟨769409, by rfl⟩ : syracuseStep 1025879 = 1538819) B1538819
theorem B2107225 : Blo 1024605 2107225 := bstep (se 2 (by rfl) ⟨790209, by rfl⟩ : syracuseStep 2107225 = 1580419) B1580419
theorem B63252323 : Blo 1024605 63252323 := bstep (se 1 (by rfl) ⟨47439242, by rfl⟩ : syracuseStep 63252323 = 94878485) B94878485
theorem B1025899 : Blo 1024605 1025899 := bstep (se 1 (by rfl) ⟨769424, by rfl⟩ : syracuseStep 1025899 = 1538849) B1538849
theorem B1025911 : Blo 1024605 1025911 := bstep (se 1 (by rfl) ⟨769433, by rfl⟩ : syracuseStep 1025911 = 1538867) B1538867
theorem B1025931 : Blo 1024605 1025931 := bstep (se 1 (by rfl) ⟨769448, by rfl⟩ : syracuseStep 1025931 = 1538897) B1538897
theorem B1025943 : Blo 1024605 1025943 := bstep (se 1 (by rfl) ⟨769457, by rfl⟩ : syracuseStep 1025943 = 1538915) B1538915
theorem B1025963 : Blo 1024605 1025963 := bstep (se 1 (by rfl) ⟨769472, by rfl⟩ : syracuseStep 1025963 = 1538945) B1538945
theorem B1157035 : Blo 1024605 1157035 := bstep (se 1 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 1157035 = 1735553) B1735553
theorem B1025975 : Blo 1024605 1025975 := bstep (se 1 (by rfl) ⟨769481, by rfl⟩ : syracuseStep 1025975 = 1538963) B1538963
theorem B1025995 : Blo 1024605 1025995 := bstep (se 1 (by rfl) ⟨769496, by rfl⟩ : syracuseStep 1025995 = 1538993) B1538993
theorem B1026007 : Blo 1024605 1026007 := bstep (se 1 (by rfl) ⟨769505, by rfl⟩ : syracuseStep 1026007 = 1539011) B1539011
theorem B1026027 : Blo 1024605 1026027 := bstep (se 1 (by rfl) ⟨769520, by rfl⟩ : syracuseStep 1026027 = 1539041) B1539041
theorem B1026039 : Blo 1024605 1026039 := bstep (se 1 (by rfl) ⟨769529, by rfl⟩ : syracuseStep 1026039 = 1539059) B1539059
theorem B16623629 : Blo 1024605 16623629 := bstep (se 3 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 16623629 = 6233861) B6233861
theorem B1026059 : Blo 1024605 1026059 := bstep (se 1 (by rfl) ⟨769544, by rfl⟩ : syracuseStep 1026059 = 1539089) B1539089
theorem B1026071 : Blo 1024605 1026071 := bstep (se 1 (by rfl) ⟨769553, by rfl⟩ : syracuseStep 1026071 = 1539107) B1539107
theorem B1157143 : Blo 1024605 1157143 := bstep (se 1 (by rfl) ⟨867857, by rfl⟩ : syracuseStep 1157143 = 1735715) B1735715
theorem B1026091 : Blo 1024605 1026091 := bstep (se 1 (by rfl) ⟨769568, by rfl⟩ : syracuseStep 1026091 = 1539137) B1539137
theorem B1026103 : Blo 1024605 1026103 := bstep (se 1 (by rfl) ⟨769577, by rfl⟩ : syracuseStep 1026103 = 1539155) B1539155
theorem B1026123 : Blo 1024605 1026123 := bstep (se 1 (by rfl) ⟨769592, by rfl⟩ : syracuseStep 1026123 = 1539185) B1539185
theorem B1026135 : Blo 1024605 1026135 := bstep (se 1 (by rfl) ⟨769601, by rfl⟩ : syracuseStep 1026135 = 1539203) B1539203
theorem B2926685 : Blo 1024605 2926685 := bstep (se 3 (by rfl) ⟨548753, by rfl⟩ : syracuseStep 2926685 = 1097507) B1097507
theorem B1026155 : Blo 1024605 1026155 := bstep (se 1 (by rfl) ⟨769616, by rfl⟩ : syracuseStep 1026155 = 1539233) B1539233
theorem B1026167 : Blo 1024605 1026167 := bstep (se 1 (by rfl) ⟨769625, by rfl⟩ : syracuseStep 1026167 = 1539251) B1539251
theorem B1026187 : Blo 1024605 1026187 := bstep (se 1 (by rfl) ⟨769640, by rfl⟩ : syracuseStep 1026187 = 1539281) B1539281
theorem B1026199 : Blo 1024605 1026199 := bstep (se 1 (by rfl) ⟨769649, by rfl⟩ : syracuseStep 1026199 = 1539299) B1539299
theorem B1026219 : Blo 1024605 1026219 := bstep (se 1 (by rfl) ⟨769664, by rfl⟩ : syracuseStep 1026219 = 1539329) B1539329
theorem B1026231 : Blo 1024605 1026231 := bstep (se 1 (by rfl) ⟨769673, by rfl⟩ : syracuseStep 1026231 = 1539347) B1539347
theorem B1026251 : Blo 1024605 1026251 := bstep (se 1 (by rfl) ⟨769688, by rfl⟩ : syracuseStep 1026251 = 1539377) B1539377
theorem B1026263 : Blo 1024605 1026263 := bstep (se 1 (by rfl) ⟨769697, by rfl⟩ : syracuseStep 1026263 = 1539395) B1539395
theorem B1026283 : Blo 1024605 1026283 := bstep (se 1 (by rfl) ⟨769712, by rfl⟩ : syracuseStep 1026283 = 1539425) B1539425
theorem B1026295 : Blo 1024605 1026295 := bstep (se 1 (by rfl) ⟨769721, by rfl⟩ : syracuseStep 1026295 = 1539443) B1539443
theorem B1026315 : Blo 1024605 1026315 := bstep (se 1 (by rfl) ⟨769736, by rfl⟩ : syracuseStep 1026315 = 1539473) B1539473
theorem B1026327 : Blo 1024605 1026327 := bstep (se 1 (by rfl) ⟨769745, by rfl⟩ : syracuseStep 1026327 = 1539491) B1539491
theorem B1026347 : Blo 1024605 1026347 := bstep (se 1 (by rfl) ⟨769760, by rfl⟩ : syracuseStep 1026347 = 1539521) B1539521
theorem B1026359 : Blo 1024605 1026359 := bstep (se 1 (by rfl) ⟨769769, by rfl⟩ : syracuseStep 1026359 = 1539539) B1539539
theorem B2468161 : Blo 1024605 2468161 := bstep (se 2 (by rfl) ⟨925560, by rfl⟩ : syracuseStep 2468161 = 1851121) B1851121
theorem B1026379 : Blo 1024605 1026379 := bstep (se 1 (by rfl) ⟨769784, by rfl⟩ : syracuseStep 1026379 = 1539569) B1539569
theorem B1026391 : Blo 1024605 1026391 := bstep (se 1 (by rfl) ⟨769793, by rfl⟩ : syracuseStep 1026391 = 1539587) B1539587
theorem B1026411 : Blo 1024605 1026411 := bstep (se 1 (by rfl) ⟨769808, by rfl⟩ : syracuseStep 1026411 = 1539617) B1539617
theorem B1026423 : Blo 1024605 1026423 := bstep (se 1 (by rfl) ⟨769817, by rfl⟩ : syracuseStep 1026423 = 1539635) B1539635
theorem B1878401 : Blo 1024605 1878401 := bstep (se 2 (by rfl) ⟨704400, by rfl⟩ : syracuseStep 1878401 = 1408801) B1408801
theorem B1026443 : Blo 1024605 1026443 := bstep (se 1 (by rfl) ⟨769832, by rfl⟩ : syracuseStep 1026443 = 1539665) B1539665
theorem B1026455 : Blo 1024605 1026455 := bstep (se 1 (by rfl) ⟨769841, by rfl⟩ : syracuseStep 1026455 = 1539683) B1539683
theorem B1026475 : Blo 1024605 1026475 := bstep (se 1 (by rfl) ⟨769856, by rfl⟩ : syracuseStep 1026475 = 1539713) B1539713
theorem B1026487 : Blo 1024605 1026487 := bstep (se 1 (by rfl) ⟨769865, by rfl⟩ : syracuseStep 1026487 = 1539731) B1539731
theorem B2599361 : Blo 1024605 2599361 := bstep (se 2 (by rfl) ⟨974760, by rfl⟩ : syracuseStep 2599361 = 1949521) B1949521
theorem B1026507 : Blo 1024605 1026507 := bstep (se 1 (by rfl) ⟨769880, by rfl⟩ : syracuseStep 1026507 = 1539761) B1539761
theorem B1026519 : Blo 1024605 1026519 := bstep (se 1 (by rfl) ⟨769889, by rfl⟩ : syracuseStep 1026519 = 1539779) B1539779
theorem B1026539 : Blo 1024605 1026539 := bstep (se 1 (by rfl) ⟨769904, by rfl⟩ : syracuseStep 1026539 = 1539809) B1539809
theorem B1026551 : Blo 1024605 1026551 := bstep (se 1 (by rfl) ⟨769913, by rfl⟩ : syracuseStep 1026551 = 1539827) B1539827
theorem B1026571 : Blo 1024605 1026571 := bstep (se 1 (by rfl) ⟨769928, by rfl⟩ : syracuseStep 1026571 = 1539857) B1539857
theorem B8759825 : Blo 1024605 8759825 := bstep (se 2 (by rfl) ⟨3284934, by rfl⟩ : syracuseStep 8759825 = 6569869) B6569869
theorem B1026583 : Blo 1024605 1026583 := bstep (se 1 (by rfl) ⟨769937, by rfl⟩ : syracuseStep 1026583 = 1539875) B1539875
theorem B1026603 : Blo 1024605 1026603 := bstep (se 1 (by rfl) ⟨769952, by rfl⟩ : syracuseStep 1026603 = 1539905) B1539905
theorem B1026615 : Blo 1024605 1026615 := bstep (se 1 (by rfl) ⟨769961, by rfl⟩ : syracuseStep 1026615 = 1539923) B1539923
theorem B1976897 : Blo 1024605 1976897 := bstep (se 2 (by rfl) ⟨741336, by rfl⟩ : syracuseStep 1976897 = 1482673) B1482673
theorem B1026635 : Blo 1024605 1026635 := bstep (se 1 (by rfl) ⟨769976, by rfl⟩ : syracuseStep 1026635 = 1539953) B1539953
theorem B1026647 : Blo 1024605 1026647 := bstep (se 1 (by rfl) ⟨769985, by rfl⟩ : syracuseStep 1026647 = 1539971) B1539971
theorem B1026667 : Blo 1024605 1026667 := bstep (se 1 (by rfl) ⟨770000, by rfl⟩ : syracuseStep 1026667 = 1540001) B1540001
theorem B1026679 : Blo 1024605 1026679 := bstep (se 1 (by rfl) ⟨770009, by rfl⟩ : syracuseStep 1026679 = 1540019) B1540019
theorem B1026699 : Blo 1024605 1026699 := bstep (se 1 (by rfl) ⟨770024, by rfl⟩ : syracuseStep 1026699 = 1540049) B1540049
theorem B1026711 : Blo 1024605 1026711 := bstep (se 1 (by rfl) ⟨770033, by rfl⟩ : syracuseStep 1026711 = 1540067) B1540067
theorem B1026731 : Blo 1024605 1026731 := bstep (se 1 (by rfl) ⟨770048, by rfl⟩ : syracuseStep 1026731 = 1540097) B1540097
theorem B1026743 : Blo 1024605 1026743 := bstep (se 1 (by rfl) ⟨770057, by rfl⟩ : syracuseStep 1026743 = 1540115) B1540115
theorem B1026763 : Blo 1024605 1026763 := bstep (se 1 (by rfl) ⟨770072, by rfl⟩ : syracuseStep 1026763 = 1540145) B1540145
theorem B1026775 : Blo 1024605 1026775 := bstep (se 1 (by rfl) ⟨770081, by rfl⟩ : syracuseStep 1026775 = 1540163) B1540163
theorem B1026795 : Blo 1024605 1026795 := bstep (se 1 (by rfl) ⟨770096, by rfl⟩ : syracuseStep 1026795 = 1540193) B1540193
theorem B1026807 : Blo 1024605 1026807 := bstep (se 1 (by rfl) ⟨770105, by rfl⟩ : syracuseStep 1026807 = 1540211) B1540211
theorem B1026827 : Blo 1024605 1026827 := bstep (se 1 (by rfl) ⟨770120, by rfl⟩ : syracuseStep 1026827 = 1540241) B1540241
theorem B1026839 : Blo 1024605 1026839 := bstep (se 1 (by rfl) ⟨770129, by rfl⟩ : syracuseStep 1026839 = 1540259) B1540259
theorem B1026859 : Blo 1024605 1026859 := bstep (se 1 (by rfl) ⟨770144, by rfl⟩ : syracuseStep 1026859 = 1540289) B1540289
theorem B1026871 : Blo 1024605 1026871 := bstep (se 1 (by rfl) ⟨770153, by rfl⟩ : syracuseStep 1026871 = 1540307) B1540307
theorem B1026891 : Blo 1024605 1026891 := bstep (se 1 (by rfl) ⟨770168, by rfl⟩ : syracuseStep 1026891 = 1540337) B1540337
theorem B1026903 : Blo 1024605 1026903 := bstep (se 1 (by rfl) ⟨770177, by rfl⟩ : syracuseStep 1026903 = 1540355) B1540355
theorem B1026923 : Blo 1024605 1026923 := bstep (se 1 (by rfl) ⟨770192, by rfl⟩ : syracuseStep 1026923 = 1540385) B1540385
theorem B1026935 : Blo 1024605 1026935 := bstep (se 1 (by rfl) ⟨770201, by rfl⟩ : syracuseStep 1026935 = 1540403) B1540403
theorem B1026955 : Blo 1024605 1026955 := bstep (se 1 (by rfl) ⟨770216, by rfl⟩ : syracuseStep 1026955 = 1540433) B1540433
theorem B1026967 : Blo 1024605 1026967 := bstep (se 1 (by rfl) ⟨770225, by rfl⟩ : syracuseStep 1026967 = 1540451) B1540451
theorem B1026987 : Blo 1024605 1026987 := bstep (se 1 (by rfl) ⟨770240, by rfl⟩ : syracuseStep 1026987 = 1540481) B1540481
theorem B1026999 : Blo 1024605 1026999 := bstep (se 1 (by rfl) ⟨770249, by rfl⟩ : syracuseStep 1026999 = 1540499) B1540499
theorem B1027019 : Blo 1024605 1027019 := bstep (se 1 (by rfl) ⟨770264, by rfl⟩ : syracuseStep 1027019 = 1540529) B1540529
theorem B1027031 : Blo 1024605 1027031 := bstep (se 1 (by rfl) ⟨770273, by rfl⟩ : syracuseStep 1027031 = 1540547) B1540547
theorem B2599897 : Blo 1024605 2599897 := bstep (se 2 (by rfl) ⟨974961, by rfl⟩ : syracuseStep 2599897 = 1949923) B1949923
theorem B1027051 : Blo 1024605 1027051 := bstep (se 1 (by rfl) ⟨770288, by rfl⟩ : syracuseStep 1027051 = 1540577) B1540577
theorem B1977331 : Blo 1024605 1977331 := bstep (se 1 (by rfl) ⟨1482998, by rfl⟩ : syracuseStep 1977331 = 2965997) B2965997
theorem B1027063 : Blo 1024605 1027063 := bstep (se 1 (by rfl) ⟨770297, by rfl⟩ : syracuseStep 1027063 = 1540595) B1540595
theorem B8432645 : Blo 1024605 8432645 := bstep (se 4 (by rfl) ⟨790560, by rfl⟩ : syracuseStep 8432645 = 1581121) B1581121
theorem B1027083 : Blo 1024605 1027083 := bstep (se 1 (by rfl) ⟨770312, by rfl⟩ : syracuseStep 1027083 = 1540625) B1540625
theorem B1027095 : Blo 1024605 1027095 := bstep (se 1 (by rfl) ⟨770321, by rfl⟩ : syracuseStep 1027095 = 1540643) B1540643
theorem B1027115 : Blo 1024605 1027115 := bstep (se 1 (by rfl) ⟨770336, by rfl⟩ : syracuseStep 1027115 = 1540673) B1540673
theorem B1027127 : Blo 1024605 1027127 := bstep (se 1 (by rfl) ⟨770345, by rfl⟩ : syracuseStep 1027127 = 1540691) B1540691
theorem B1027147 : Blo 1024605 1027147 := bstep (se 1 (by rfl) ⟨770360, by rfl⟩ : syracuseStep 1027147 = 1540721) B1540721
theorem B1027159 : Blo 1024605 1027159 := bstep (se 1 (by rfl) ⟨770369, by rfl⟩ : syracuseStep 1027159 = 1540739) B1540739
theorem B1027179 : Blo 1024605 1027179 := bstep (se 1 (by rfl) ⟨770384, by rfl⟩ : syracuseStep 1027179 = 1540769) B1540769
theorem B1027191 : Blo 1024605 1027191 := bstep (se 1 (by rfl) ⟨770393, by rfl⟩ : syracuseStep 1027191 = 1540787) B1540787
theorem B1027211 : Blo 1024605 1027211 := bstep (se 1 (by rfl) ⟨770408, by rfl⟩ : syracuseStep 1027211 = 1540817) B1540817
theorem B3288215 : Blo 1024605 3288215 := bstep (se 1 (by rfl) ⟨2466161, by rfl⟩ : syracuseStep 3288215 = 4932323) B4932323
theorem B1027223 : Blo 1024605 1027223 := bstep (se 1 (by rfl) ⟨770417, by rfl⟩ : syracuseStep 1027223 = 1540835) B1540835
theorem B1027243 : Blo 1024605 1027243 := bstep (se 1 (by rfl) ⟨770432, by rfl⟩ : syracuseStep 1027243 = 1540865) B1540865
theorem B1027255 : Blo 1024605 1027255 := bstep (se 1 (by rfl) ⟨770441, by rfl⟩ : syracuseStep 1027255 = 1540883) B1540883
theorem B1027275 : Blo 1024605 1027275 := bstep (se 1 (by rfl) ⟨770456, by rfl⟩ : syracuseStep 1027275 = 1540913) B1540913
theorem B1387735 : Blo 1024605 1387735 := bstep (se 1 (by rfl) ⟨1040801, by rfl⟩ : syracuseStep 1387735 = 2081603) B2081603
theorem B1027287 : Blo 1024605 1027287 := bstep (se 1 (by rfl) ⟨770465, by rfl⟩ : syracuseStep 1027287 = 1540931) B1540931
theorem B1027307 : Blo 1024605 1027307 := bstep (se 1 (by rfl) ⟨770480, by rfl⟩ : syracuseStep 1027307 = 1540961) B1540961
theorem B1027319 : Blo 1024605 1027319 := bstep (se 1 (by rfl) ⟨770489, by rfl⟩ : syracuseStep 1027319 = 1540979) B1540979
theorem B1027339 : Blo 1024605 1027339 := bstep (se 1 (by rfl) ⟨770504, by rfl⟩ : syracuseStep 1027339 = 1541009) B1541009
theorem B1027351 : Blo 1024605 1027351 := bstep (se 1 (by rfl) ⟨770513, by rfl⟩ : syracuseStep 1027351 = 1541027) B1541027
theorem B1027371 : Blo 1024605 1027371 := bstep (se 1 (by rfl) ⟨770528, by rfl⟩ : syracuseStep 1027371 = 1541057) B1541057
theorem B1027383 : Blo 1024605 1027383 := bstep (se 1 (by rfl) ⟨770537, by rfl⟩ : syracuseStep 1027383 = 1541075) B1541075
theorem B1027403 : Blo 1024605 1027403 := bstep (se 1 (by rfl) ⟨770552, by rfl⟩ : syracuseStep 1027403 = 1541105) B1541105
theorem B2305367 : Blo 1024605 2305367 := bstep (se 1 (by rfl) ⟨1729025, by rfl⟩ : syracuseStep 2305367 = 3458051) B3458051
theorem B1027415 : Blo 1024605 1027415 := bstep (se 1 (by rfl) ⟨770561, by rfl⟩ : syracuseStep 1027415 = 1541123) B1541123
theorem B1027435 : Blo 1024605 1027435 := bstep (se 1 (by rfl) ⟨770576, by rfl⟩ : syracuseStep 1027435 = 1541153) B1541153
theorem B1027447 : Blo 1024605 1027447 := bstep (se 1 (by rfl) ⟨770585, by rfl⟩ : syracuseStep 1027447 = 1541171) B1541171
theorem B1027467 : Blo 1024605 1027467 := bstep (se 1 (by rfl) ⟨770600, by rfl⟩ : syracuseStep 1027467 = 1541201) B1541201
theorem B1027479 : Blo 1024605 1027479 := bstep (se 1 (by rfl) ⟨770609, by rfl⟩ : syracuseStep 1027479 = 1541219) B1541219
theorem B1027499 : Blo 1024605 1027499 := bstep (se 1 (by rfl) ⟨770624, by rfl⟩ : syracuseStep 1027499 = 1541249) B1541249
theorem B1027511 : Blo 1024605 1027511 := bstep (se 1 (by rfl) ⟨770633, by rfl⟩ : syracuseStep 1027511 = 1541267) B1541267
theorem B1027531 : Blo 1024605 1027531 := bstep (se 1 (by rfl) ⟨770648, by rfl⟩ : syracuseStep 1027531 = 1541297) B1541297
theorem B1027543 : Blo 1024605 1027543 := bstep (se 1 (by rfl) ⟨770657, by rfl⟩ : syracuseStep 1027543 = 1541315) B1541315
theorem B1027563 : Blo 1024605 1027563 := bstep (se 1 (by rfl) ⟨770672, by rfl⟩ : syracuseStep 1027563 = 1541345) B1541345
theorem B1027575 : Blo 1024605 1027575 := bstep (se 1 (by rfl) ⟨770681, by rfl⟩ : syracuseStep 1027575 = 1541363) B1541363
theorem B2305547 : Blo 1024605 2305547 := bstep (se 1 (by rfl) ⟨1729160, by rfl⟩ : syracuseStep 2305547 = 3458321) B3458321
theorem B1027595 : Blo 1024605 1027595 := bstep (se 1 (by rfl) ⟨770696, by rfl⟩ : syracuseStep 1027595 = 1541393) B1541393
theorem B1027607 : Blo 1024605 1027607 := bstep (se 1 (by rfl) ⟨770705, by rfl⟩ : syracuseStep 1027607 = 1541411) B1541411
theorem B1027627 : Blo 1024605 1027627 := bstep (se 1 (by rfl) ⟨770720, by rfl⟩ : syracuseStep 1027627 = 1541441) B1541441
theorem B1027639 : Blo 1024605 1027639 := bstep (se 1 (by rfl) ⟨770729, by rfl⟩ : syracuseStep 1027639 = 1541459) B1541459
theorem B2305601 : Blo 1024605 2305601 := bstep (se 2 (by rfl) ⟨864600, by rfl⟩ : syracuseStep 2305601 = 1729201) B1729201
theorem B1027659 : Blo 1024605 1027659 := bstep (se 1 (by rfl) ⟨770744, by rfl⟩ : syracuseStep 1027659 = 1541489) B1541489
theorem B1027671 : Blo 1024605 1027671 := bstep (se 1 (by rfl) ⟨770753, by rfl⟩ : syracuseStep 1027671 = 1541507) B1541507
theorem B12496477 : Blo 1024605 12496477 := bstep (se 3 (by rfl) ⟨2343089, by rfl⟩ : syracuseStep 12496477 = 4686179) B4686179
theorem B1027691 : Blo 1024605 1027691 := bstep (se 1 (by rfl) ⟨770768, by rfl⟩ : syracuseStep 1027691 = 1541537) B1541537
theorem B1027703 : Blo 1024605 1027703 := bstep (se 1 (by rfl) ⟨770777, by rfl⟩ : syracuseStep 1027703 = 1541555) B1541555
theorem B1027723 : Blo 1024605 1027723 := bstep (se 1 (by rfl) ⟨770792, by rfl⟩ : syracuseStep 1027723 = 1541585) B1541585
theorem B1027735 : Blo 1024605 1027735 := bstep (se 1 (by rfl) ⟨770801, by rfl⟩ : syracuseStep 1027735 = 1541603) B1541603
theorem B1027755 : Blo 1024605 1027755 := bstep (se 1 (by rfl) ⟨770816, by rfl⟩ : syracuseStep 1027755 = 1541633) B1541633
theorem B1027767 : Blo 1024605 1027767 := bstep (se 1 (by rfl) ⟨770825, by rfl⟩ : syracuseStep 1027767 = 1541651) B1541651
theorem B1945291 : Blo 1024605 1945291 := bstep (se 1 (by rfl) ⟨1458968, by rfl⟩ : syracuseStep 1945291 = 2917937) B2917937
theorem B1027787 : Blo 1024605 1027787 := bstep (se 1 (by rfl) ⟨770840, by rfl⟩ : syracuseStep 1027787 = 1541681) B1541681
theorem B1027799 : Blo 1024605 1027799 := bstep (se 1 (by rfl) ⟨770849, by rfl⟩ : syracuseStep 1027799 = 1541699) B1541699
theorem B1027819 : Blo 1024605 1027819 := bstep (se 1 (by rfl) ⟨770864, by rfl⟩ : syracuseStep 1027819 = 1541729) B1541729
theorem B1027831 : Blo 1024605 1027831 := bstep (se 1 (by rfl) ⟨770873, by rfl⟩ : syracuseStep 1027831 = 1541747) B1541747
theorem B1027851 : Blo 1024605 1027851 := bstep (se 1 (by rfl) ⟨770888, by rfl⟩ : syracuseStep 1027851 = 1541777) B1541777
theorem B1945367 : Blo 1024605 1945367 := bstep (se 1 (by rfl) ⟨1459025, by rfl⟩ : syracuseStep 1945367 = 2918051) B2918051
theorem B1027863 : Blo 1024605 1027863 := bstep (se 1 (by rfl) ⟨770897, by rfl⟩ : syracuseStep 1027863 = 1541795) B1541795
theorem B2305817 : Blo 1024605 2305817 := bstep (se 2 (by rfl) ⟨864681, by rfl⟩ : syracuseStep 2305817 = 1729363) B1729363
theorem B1027883 : Blo 1024605 1027883 := bstep (se 1 (by rfl) ⟨770912, by rfl⟩ : syracuseStep 1027883 = 1541825) B1541825
theorem B1027895 : Blo 1024605 1027895 := bstep (se 1 (by rfl) ⟨770921, by rfl⟩ : syracuseStep 1027895 = 1541843) B1541843
theorem B1027915 : Blo 1024605 1027915 := bstep (se 1 (by rfl) ⟨770936, by rfl⟩ : syracuseStep 1027915 = 1541873) B1541873
theorem B1027927 : Blo 1024605 1027927 := bstep (se 1 (by rfl) ⟨770945, by rfl⟩ : syracuseStep 1027927 = 1541891) B1541891
theorem B3944285 : Blo 1024605 3944285 := bstep (se 3 (by rfl) ⟨739553, by rfl⟩ : syracuseStep 3944285 = 1479107) B1479107
theorem B1027947 : Blo 1024605 1027947 := bstep (se 1 (by rfl) ⟨770960, by rfl⟩ : syracuseStep 1027947 = 1541921) B1541921
theorem B2305907 : Blo 1024605 2305907 := bstep (se 1 (by rfl) ⟨1729430, by rfl⟩ : syracuseStep 2305907 = 3458861) B3458861
theorem B1027959 : Blo 1024605 1027959 := bstep (se 1 (by rfl) ⟨770969, by rfl⟩ : syracuseStep 1027959 = 1541939) B1541939
theorem B5189507 : Blo 1024605 5189507 := bstep (se 1 (by rfl) ⟨3892130, by rfl⟩ : syracuseStep 5189507 = 7784261) B7784261
theorem B1027979 : Blo 1024605 1027979 := bstep (se 1 (by rfl) ⟨770984, by rfl⟩ : syracuseStep 1027979 = 1541969) B1541969
theorem B2305943 : Blo 1024605 2305943 := bstep (se 1 (by rfl) ⟨1729457, by rfl⟩ : syracuseStep 2305943 = 3458915) B3458915
theorem B1027991 : Blo 1024605 1027991 := bstep (se 1 (by rfl) ⟨770993, by rfl⟩ : syracuseStep 1027991 = 1541987) B1541987
theorem B1028011 : Blo 1024605 1028011 := bstep (se 1 (by rfl) ⟨771008, by rfl⟩ : syracuseStep 1028011 = 1542017) B1542017
theorem B1028023 : Blo 1024605 1028023 := bstep (se 1 (by rfl) ⟨771017, by rfl⟩ : syracuseStep 1028023 = 1542035) B1542035
theorem B1028043 : Blo 1024605 1028043 := bstep (se 1 (by rfl) ⟨771032, by rfl⟩ : syracuseStep 1028043 = 1542065) B1542065
theorem B1028055 : Blo 1024605 1028055 := bstep (se 1 (by rfl) ⟨771041, by rfl⟩ : syracuseStep 1028055 = 1542083) B1542083
theorem B1028075 : Blo 1024605 1028075 := bstep (se 1 (by rfl) ⟨771056, by rfl⟩ : syracuseStep 1028075 = 1542113) B1542113
theorem B1028087 : Blo 1024605 1028087 := bstep (se 1 (by rfl) ⟨771065, by rfl⟩ : syracuseStep 1028087 = 1542131) B1542131
theorem B1028107 : Blo 1024605 1028107 := bstep (se 1 (by rfl) ⟨771080, by rfl⟩ : syracuseStep 1028107 = 1542161) B1542161
theorem B12496913 : Blo 1024605 12496913 := bstep (se 2 (by rfl) ⟨4686342, by rfl⟩ : syracuseStep 12496913 = 9372685) B9372685
theorem B1028119 : Blo 1024605 1028119 := bstep (se 1 (by rfl) ⟨771089, by rfl⟩ : syracuseStep 1028119 = 1542179) B1542179
theorem B1028139 : Blo 1024605 1028139 := bstep (se 1 (by rfl) ⟨771104, by rfl⟩ : syracuseStep 1028139 = 1542209) B1542209
theorem B2601011 : Blo 1024605 2601011 := bstep (se 1 (by rfl) ⟨1950758, by rfl⟩ : syracuseStep 2601011 = 3901517) B3901517
theorem B3125299 : Blo 1024605 3125299 := bstep (se 1 (by rfl) ⟨2343974, by rfl⟩ : syracuseStep 3125299 = 4687949) B4687949
theorem B1028151 : Blo 1024605 1028151 := bstep (se 1 (by rfl) ⟨771113, by rfl⟩ : syracuseStep 1028151 = 1542227) B1542227
theorem B2306123 : Blo 1024605 2306123 := bstep (se 1 (by rfl) ⟨1729592, by rfl⟩ : syracuseStep 2306123 = 3459185) B3459185
theorem B1028171 : Blo 1024605 1028171 := bstep (se 1 (by rfl) ⟨771128, by rfl⟩ : syracuseStep 1028171 = 1542257) B1542257
theorem B1028183 : Blo 1024605 1028183 := bstep (se 1 (by rfl) ⟨771137, by rfl⟩ : syracuseStep 1028183 = 1542275) B1542275
theorem B1028203 : Blo 1024605 1028203 := bstep (se 1 (by rfl) ⟨771152, by rfl⟩ : syracuseStep 1028203 = 1542305) B1542305
theorem B1028215 : Blo 1024605 1028215 := bstep (se 1 (by rfl) ⟨771161, by rfl⟩ : syracuseStep 1028215 = 1542323) B1542323
theorem B2306177 : Blo 1024605 2306177 := bstep (se 2 (by rfl) ⟨864816, by rfl⟩ : syracuseStep 2306177 = 1729633) B1729633
theorem B1028235 : Blo 1024605 1028235 := bstep (se 1 (by rfl) ⟨771176, by rfl⟩ : syracuseStep 1028235 = 1542353) B1542353
theorem B1028247 : Blo 1024605 1028247 := bstep (se 1 (by rfl) ⟨771185, by rfl⟩ : syracuseStep 1028247 = 1542371) B1542371
theorem B1028267 : Blo 1024605 1028267 := bstep (se 1 (by rfl) ⟨771200, by rfl⟩ : syracuseStep 1028267 = 1542401) B1542401
theorem B1028279 : Blo 1024605 1028279 := bstep (se 1 (by rfl) ⟨771209, by rfl⟩ : syracuseStep 1028279 = 1542419) B1542419
theorem B1028299 : Blo 1024605 1028299 := bstep (se 1 (by rfl) ⟨771224, by rfl⟩ : syracuseStep 1028299 = 1542449) B1542449
theorem B1028311 : Blo 1024605 1028311 := bstep (se 1 (by rfl) ⟨771233, by rfl⟩ : syracuseStep 1028311 = 1542467) B1542467
theorem B1028331 : Blo 1024605 1028331 := bstep (se 1 (by rfl) ⟨771248, by rfl⟩ : syracuseStep 1028331 = 1542497) B1542497
theorem B1028343 : Blo 1024605 1028343 := bstep (se 1 (by rfl) ⟨771257, by rfl⟩ : syracuseStep 1028343 = 1542515) B1542515
theorem B1028363 : Blo 1024605 1028363 := bstep (se 1 (by rfl) ⟨771272, by rfl⟩ : syracuseStep 1028363 = 1542545) B1542545
theorem B1028375 : Blo 1024605 1028375 := bstep (se 1 (by rfl) ⟨771281, by rfl⟩ : syracuseStep 1028375 = 1542563) B1542563
theorem B1028395 : Blo 1024605 1028395 := bstep (se 1 (by rfl) ⟨771296, by rfl⟩ : syracuseStep 1028395 = 1542593) B1542593
theorem B1028407 : Blo 1024605 1028407 := bstep (se 1 (by rfl) ⟨771305, by rfl⟩ : syracuseStep 1028407 = 1542611) B1542611
theorem B1028427 : Blo 1024605 1028427 := bstep (se 1 (by rfl) ⟨771320, by rfl⟩ : syracuseStep 1028427 = 1542641) B1542641
theorem B1028439 : Blo 1024605 1028439 := bstep (se 1 (by rfl) ⟨771329, by rfl⟩ : syracuseStep 1028439 = 1542659) B1542659
theorem B2306393 : Blo 1024605 2306393 := bstep (se 2 (by rfl) ⟨864897, by rfl⟩ : syracuseStep 2306393 = 1729795) B1729795
theorem B2601305 : Blo 1024605 2601305 := bstep (se 2 (by rfl) ⟨975489, by rfl⟩ : syracuseStep 2601305 = 1950979) B1950979
theorem B1028459 : Blo 1024605 1028459 := bstep (se 1 (by rfl) ⟨771344, by rfl⟩ : syracuseStep 1028459 = 1542689) B1542689
theorem B1028471 : Blo 1024605 1028471 := bstep (se 1 (by rfl) ⟨771353, by rfl⟩ : syracuseStep 1028471 = 1542707) B1542707
theorem B1028491 : Blo 1024605 1028491 := bstep (se 1 (by rfl) ⟨771368, by rfl⟩ : syracuseStep 1028491 = 1542737) B1542737
theorem B1028503 : Blo 1024605 1028503 := bstep (se 1 (by rfl) ⟨771377, by rfl⟩ : syracuseStep 1028503 = 1542755) B1542755
theorem B1028523 : Blo 1024605 1028523 := bstep (se 1 (by rfl) ⟨771392, by rfl⟩ : syracuseStep 1028523 = 1542785) B1542785
theorem B1946035 : Blo 1024605 1946035 := bstep (se 1 (by rfl) ⟨1459526, by rfl⟩ : syracuseStep 1946035 = 2919053) B2919053
theorem B2306483 : Blo 1024605 2306483 := bstep (se 1 (by rfl) ⟨1729862, by rfl⟩ : syracuseStep 2306483 = 3459725) B3459725
theorem B1028535 : Blo 1024605 1028535 := bstep (se 1 (by rfl) ⟨771401, by rfl⟩ : syracuseStep 1028535 = 1542803) B1542803
theorem B1028555 : Blo 1024605 1028555 := bstep (se 1 (by rfl) ⟨771416, by rfl⟩ : syracuseStep 1028555 = 1542833) B1542833
theorem B2306519 : Blo 1024605 2306519 := bstep (se 1 (by rfl) ⟨1729889, by rfl⟩ : syracuseStep 2306519 = 3459779) B3459779
theorem B1028567 : Blo 1024605 1028567 := bstep (se 1 (by rfl) ⟨771425, by rfl⟩ : syracuseStep 1028567 = 1542851) B1542851
theorem B1028587 : Blo 1024605 1028587 := bstep (se 1 (by rfl) ⟨771440, by rfl⟩ : syracuseStep 1028587 = 1542881) B1542881
theorem B1028599 : Blo 1024605 1028599 := bstep (se 1 (by rfl) ⟨771449, by rfl⟩ : syracuseStep 1028599 = 1542899) B1542899
theorem B1847819 : Blo 1024605 1847819 := bstep (se 1 (by rfl) ⟨1385864, by rfl⟩ : syracuseStep 1847819 = 2771729) B2771729
theorem B4928131 : Blo 1024605 4928131 := bstep (se 1 (by rfl) ⟨3696098, by rfl⟩ : syracuseStep 4928131 = 7392197) B7392197
theorem B2306699 : Blo 1024605 2306699 := bstep (se 1 (by rfl) ⟨1730024, by rfl⟩ : syracuseStep 2306699 = 3460049) B3460049
theorem B1946263 : Blo 1024605 1946263 := bstep (se 1 (by rfl) ⟨1459697, by rfl⟩ : syracuseStep 1946263 = 2919395) B2919395
theorem B2306753 : Blo 1024605 2306753 := bstep (se 2 (by rfl) ⟨865032, by rfl⟩ : syracuseStep 2306753 = 1730065) B1730065
theorem B1946369 : Blo 1024605 1946369 := bstep (se 2 (by rfl) ⟨729888, by rfl⟩ : syracuseStep 1946369 = 1459777) B1459777
theorem B2470679 : Blo 1024605 2470679 := bstep (se 1 (by rfl) ⟨1853009, by rfl⟩ : syracuseStep 2470679 = 3706019) B3706019
theorem B2306969 : Blo 1024605 2306969 := bstep (se 2 (by rfl) ⟨865113, by rfl⟩ : syracuseStep 2306969 = 1730227) B1730227
theorem B1946521 : Blo 1024605 1946521 := bstep (se 2 (by rfl) ⟨729945, by rfl⟩ : syracuseStep 1946521 = 1459891) B1459891
theorem B1848217 : Blo 1024605 1848217 := bstep (se 2 (by rfl) ⟨693081, by rfl⟩ : syracuseStep 1848217 = 1386163) B1386163
theorem B17544113 : Blo 1024605 17544113 := bstep (se 2 (by rfl) ⟨6579042, by rfl⟩ : syracuseStep 17544113 = 13158085) B13158085
theorem B2962369 : Blo 1024605 2962369 := bstep (se 2 (by rfl) ⟨1110888, by rfl⟩ : syracuseStep 2962369 = 2221777) B2221777
theorem B2307059 : Blo 1024605 2307059 := bstep (se 1 (by rfl) ⟨1730294, by rfl⟩ : syracuseStep 2307059 = 3460589) B3460589
theorem B5846033 : Blo 1024605 5846033 := bstep (se 2 (by rfl) ⟨2192262, by rfl⟩ : syracuseStep 5846033 = 4384525) B4384525
theorem B2307095 : Blo 1024605 2307095 := bstep (se 1 (by rfl) ⟨1730321, by rfl⟩ : syracuseStep 2307095 = 3460643) B3460643
theorem B2110579 : Blo 1024605 2110579 := bstep (se 1 (by rfl) ⟨1582934, by rfl⟩ : syracuseStep 2110579 = 3165869) B3165869
theorem B2077825 : Blo 1024605 2077825 := bstep (se 2 (by rfl) ⟨779184, by rfl⟩ : syracuseStep 2077825 = 1558369) B1558369
theorem B3290291 : Blo 1024605 3290291 := bstep (se 1 (by rfl) ⟨2467718, by rfl⟩ : syracuseStep 3290291 = 4935437) B4935437
theorem B2307275 : Blo 1024605 2307275 := bstep (se 1 (by rfl) ⟨1730456, by rfl⟩ : syracuseStep 2307275 = 3460913) B3460913
theorem B2307329 : Blo 1024605 2307329 := bstep (se 2 (by rfl) ⟨865248, by rfl⟩ : syracuseStep 2307329 = 1730497) B1730497
theorem B7386547 : Blo 1024605 7386547 := bstep (se 1 (by rfl) ⟨5539910, by rfl⟩ : syracuseStep 7386547 = 11079821) B11079821
theorem B1095115 : Blo 1024605 1095115 := bstep (se 1 (by rfl) ⟨821336, by rfl⟩ : syracuseStep 1095115 = 1642673) B1642673
theorem B2307545 : Blo 1024605 2307545 := bstep (se 2 (by rfl) ⟨865329, by rfl⟩ : syracuseStep 2307545 = 1730659) B1730659
theorem B5846489 : Blo 1024605 5846489 := bstep (se 2 (by rfl) ⟨2192433, by rfl⟩ : syracuseStep 5846489 = 4384867) B4384867
theorem B2307635 : Blo 1024605 2307635 := bstep (se 1 (by rfl) ⟨1730726, by rfl⟩ : syracuseStep 2307635 = 3461453) B3461453
theorem B2307671 : Blo 1024605 2307671 := bstep (se 1 (by rfl) ⟨1730753, by rfl⟩ : syracuseStep 2307671 = 3461507) B3461507
theorem B2307851 : Blo 1024605 2307851 := bstep (se 1 (by rfl) ⟨1730888, by rfl⟩ : syracuseStep 2307851 = 3461777) B3461777
theorem B2307905 : Blo 1024605 2307905 := bstep (se 2 (by rfl) ⟨865464, by rfl⟩ : syracuseStep 2307905 = 1730929) B1730929
theorem B2602955 : Blo 1024605 2602955 := bstep (se 1 (by rfl) ⟨1952216, by rfl⟩ : syracuseStep 2602955 = 3904433) B3904433
theorem B3749905 : Blo 1024605 3749905 := bstep (se 2 (by rfl) ⟨1406214, by rfl⟩ : syracuseStep 3749905 = 2812429) B2812429
theorem B2308121 : Blo 1024605 2308121 := bstep (se 2 (by rfl) ⟨865545, by rfl⟩ : syracuseStep 2308121 = 1731091) B1731091
theorem B2308211 : Blo 1024605 2308211 := bstep (se 1 (by rfl) ⟨1731158, by rfl⟩ : syracuseStep 2308211 = 3462317) B3462317
theorem B2308247 : Blo 1024605 2308247 := bstep (se 1 (by rfl) ⟨1731185, by rfl⟩ : syracuseStep 2308247 = 3462371) B3462371
theorem B1947827 : Blo 1024605 1947827 := bstep (se 1 (by rfl) ⟨1460870, by rfl⟩ : syracuseStep 1947827 = 2921741) B2921741
theorem B2308427 : Blo 1024605 2308427 := bstep (se 1 (by rfl) ⟨1731320, by rfl⟩ : syracuseStep 2308427 = 3462641) B3462641
theorem B1947979 : Blo 1024605 1947979 := bstep (se 1 (by rfl) ⟨1460984, by rfl⟩ : syracuseStep 1947979 = 2921969) B2921969
theorem B2308481 : Blo 1024605 2308481 := bstep (se 2 (by rfl) ⟨865680, by rfl⟩ : syracuseStep 2308481 = 1731361) B1731361
theorem B1096183 : Blo 1024605 1096183 := bstep (se 1 (by rfl) ⟨822137, by rfl⟩ : syracuseStep 1096183 = 1644275) B1644275
theorem B2308697 : Blo 1024605 2308697 := bstep (se 2 (by rfl) ⟨865761, by rfl⟩ : syracuseStep 2308697 = 1731523) B1731523
theorem B1948313 : Blo 1024605 1948313 := bstep (se 2 (by rfl) ⟨730617, by rfl⟩ : syracuseStep 1948313 = 1461235) B1461235
theorem B2308787 : Blo 1024605 2308787 := bstep (se 1 (by rfl) ⟨1731590, by rfl⟩ : syracuseStep 2308787 = 3463181) B3463181
theorem B2308823 : Blo 1024605 2308823 := bstep (se 1 (by rfl) ⟨1731617, by rfl⟩ : syracuseStep 2308823 = 3463235) B3463235
theorem B1850177 : Blo 1024605 1850177 := bstep (se 2 (by rfl) ⟨693816, by rfl⟩ : syracuseStep 1850177 = 1387633) B1387633
theorem B2079575 : Blo 1024605 2079575 := bstep (se 1 (by rfl) ⟨1559681, by rfl⟩ : syracuseStep 2079575 = 3119363) B3119363
theorem B2309003 : Blo 1024605 2309003 := bstep (se 1 (by rfl) ⟨1731752, by rfl⟩ : syracuseStep 2309003 = 3463505) B3463505
theorem B4995991 : Blo 1024605 4995991 := bstep (se 1 (by rfl) ⟨3746993, by rfl⟩ : syracuseStep 4995991 = 7493987) B7493987
theorem B2309057 : Blo 1024605 2309057 := bstep (se 2 (by rfl) ⟨865896, by rfl⟩ : syracuseStep 2309057 = 1731793) B1731793
theorem B16628753 : Blo 1024605 16628753 := bstep (se 2 (by rfl) ⟨6235782, by rfl⟩ : syracuseStep 16628753 = 12471565) B12471565
theorem B4930577 : Blo 1024605 4930577 := bstep (se 2 (by rfl) ⟨1848966, by rfl⟩ : syracuseStep 4930577 = 3697933) B3697933
theorem B11713571 : Blo 1024605 11713571 := bstep (se 1 (by rfl) ⟨8785178, by rfl⟩ : syracuseStep 11713571 = 17570357) B17570357
theorem B2309273 : Blo 1024605 2309273 := bstep (se 2 (by rfl) ⟨865977, by rfl⟩ : syracuseStep 2309273 = 1731955) B1731955
theorem B2309363 : Blo 1024605 2309363 := bstep (se 1 (by rfl) ⟨1732022, by rfl⟩ : syracuseStep 2309363 = 3464045) B3464045
theorem B2309399 : Blo 1024605 2309399 := bstep (se 1 (by rfl) ⟨1732049, by rfl⟩ : syracuseStep 2309399 = 3464099) B3464099
theorem B1948951 : Blo 1024605 1948951 := bstep (se 1 (by rfl) ⟨1461713, by rfl⟩ : syracuseStep 1948951 = 2923427) B2923427
theorem B1097003 : Blo 1024605 1097003 := bstep (se 1 (by rfl) ⟨822752, by rfl⟩ : syracuseStep 1097003 = 1645505) B1645505
theorem B2309579 : Blo 1024605 2309579 := bstep (se 1 (by rfl) ⟨1732184, by rfl⟩ : syracuseStep 2309579 = 3464369) B3464369
theorem B2309633 : Blo 1024605 2309633 := bstep (se 2 (by rfl) ⟨866112, by rfl⟩ : syracuseStep 2309633 = 1732225) B1732225
theorem B5193233 : Blo 1024605 5193233 := bstep (se 2 (by rfl) ⟨1947462, by rfl⟩ : syracuseStep 5193233 = 3894925) B3894925
theorem B2342515 : Blo 1024605 2342515 := bstep (se 1 (by rfl) ⟨1756886, by rfl⟩ : syracuseStep 2342515 = 3513773) B3513773
theorem B5193395 : Blo 1024605 5193395 := bstep (se 1 (by rfl) ⟨3895046, by rfl⟩ : syracuseStep 5193395 = 7790093) B7790093
theorem B2309849 : Blo 1024605 2309849 := bstep (se 2 (by rfl) ⟨866193, by rfl⟩ : syracuseStep 2309849 = 1732387) B1732387
theorem B2309939 : Blo 1024605 2309939 := bstep (se 1 (by rfl) ⟨1732454, by rfl⟩ : syracuseStep 2309939 = 3464909) B3464909
theorem B2309975 : Blo 1024605 2309975 := bstep (se 1 (by rfl) ⟨1732481, by rfl⟩ : syracuseStep 2309975 = 3464963) B3464963
theorem B2342807 : Blo 1024605 2342807 := bstep (se 1 (by rfl) ⟨1757105, by rfl⟩ : syracuseStep 2342807 = 3514211) B3514211
theorem B2310155 : Blo 1024605 2310155 := bstep (se 1 (by rfl) ⟨1732616, by rfl⟩ : syracuseStep 2310155 = 3465233) B3465233
theorem B2310209 : Blo 1024605 2310209 := bstep (se 2 (by rfl) ⟨866328, by rfl⟩ : syracuseStep 2310209 = 1732657) B1732657
theorem B1949771 : Blo 1024605 1949771 := bstep (se 1 (by rfl) ⟨1462328, by rfl⟩ : syracuseStep 1949771 = 2924657) B2924657
theorem B13156445 : Blo 1024605 13156445 := bstep (se 3 (by rfl) ⟨2466833, by rfl⟩ : syracuseStep 13156445 = 4933667) B4933667
theorem B1949825 : Blo 1024605 1949825 := bstep (se 2 (by rfl) ⟨731184, by rfl⟩ : syracuseStep 1949825 = 1462369) B1462369
theorem B2310425 : Blo 1024605 2310425 := bstep (se 2 (by rfl) ⟨866409, by rfl⟩ : syracuseStep 2310425 = 1732819) B1732819
theorem B17088869 : Blo 1024605 17088869 := bstep (se 4 (by rfl) ⟨1602081, by rfl⟩ : syracuseStep 17088869 = 3204163) B3204163
theorem B2310515 : Blo 1024605 2310515 := bstep (se 1 (by rfl) ⟨1732886, by rfl⟩ : syracuseStep 2310515 = 3465773) B3465773
theorem B2310551 : Blo 1024605 2310551 := bstep (se 1 (by rfl) ⟨1732913, by rfl⟩ : syracuseStep 2310551 = 3465827) B3465827
theorem B1851827 : Blo 1024605 1851827 := bstep (se 1 (by rfl) ⟨1388870, by rfl⟩ : syracuseStep 1851827 = 2777741) B2777741
theorem B1753547 : Blo 1024605 1753547 := bstep (se 1 (by rfl) ⟨1315160, by rfl⟩ : syracuseStep 1753547 = 2630321) B2630321
theorem B1098199 : Blo 1024605 1098199 := bstep (se 1 (by rfl) ⟨823649, by rfl⟩ : syracuseStep 1098199 = 1647299) B1647299
theorem B2310731 : Blo 1024605 2310731 := bstep (se 1 (by rfl) ⟨1733048, by rfl⟩ : syracuseStep 2310731 = 3466097) B3466097
theorem B2310785 : Blo 1024605 2310785 := bstep (se 2 (by rfl) ⟨866544, by rfl⟩ : syracuseStep 2310785 = 1733089) B1733089
theorem B1753739 : Blo 1024605 1753739 := bstep (se 1 (by rfl) ⟨1315304, by rfl⟩ : syracuseStep 1753739 = 2630609) B2630609
theorem B2311001 : Blo 1024605 2311001 := bstep (se 2 (by rfl) ⟨866625, by rfl⟩ : syracuseStep 2311001 = 1733251) B1733251
theorem B2311091 : Blo 1024605 2311091 := bstep (se 1 (by rfl) ⟨1733318, by rfl⟩ : syracuseStep 2311091 = 3466637) B3466637
theorem B2311127 : Blo 1024605 2311127 := bstep (se 1 (by rfl) ⟨1733345, by rfl⟩ : syracuseStep 2311127 = 3466691) B3466691
theorem B1950743 : Blo 1024605 1950743 := bstep (se 1 (by rfl) ⟨1463057, by rfl⟩ : syracuseStep 1950743 = 2926115) B2926115
theorem B1459225 : Blo 1024605 1459225 := bstep (se 2 (by rfl) ⟨547209, by rfl⟩ : syracuseStep 1459225 = 1094419) B1094419
theorem B2311307 : Blo 1024605 2311307 := bstep (se 1 (by rfl) ⟨1733480, by rfl⟩ : syracuseStep 2311307 = 3466961) B3466961
theorem B2311361 : Blo 1024605 2311361 := bstep (se 2 (by rfl) ⟨866760, by rfl⟩ : syracuseStep 2311361 = 1733521) B1733521
theorem B2311577 : Blo 1024605 2311577 := bstep (se 2 (by rfl) ⟨866841, by rfl⟩ : syracuseStep 2311577 = 1733683) B1733683
theorem B3458483 : Blo 1024605 3458483 := bstep (se 1 (by rfl) ⟨2593862, by rfl⟩ : syracuseStep 3458483 = 5187725) B5187725
theorem B3556829 : Blo 1024605 3556829 := bstep (se 3 (by rfl) ⟨666905, by rfl⟩ : syracuseStep 3556829 = 1333811) B1333811
theorem B2311667 : Blo 1024605 2311667 := bstep (se 1 (by rfl) ⟨1733750, by rfl⟩ : syracuseStep 2311667 = 3467501) B3467501
theorem B1558027 : Blo 1024605 1558027 := bstep (se 1 (by rfl) ⟨1168520, by rfl⟩ : syracuseStep 1558027 = 2337041) B2337041
theorem B2311703 : Blo 1024605 2311703 := bstep (se 1 (by rfl) ⟨1733777, by rfl⟩ : syracuseStep 2311703 = 3467555) B3467555
theorem B1951283 : Blo 1024605 1951283 := bstep (se 1 (by rfl) ⟨1463462, by rfl⟩ : syracuseStep 1951283 = 2926925) B2926925
theorem B5195339 : Blo 1024605 5195339 := bstep (se 1 (by rfl) ⟨3896504, by rfl⟩ : syracuseStep 5195339 = 7793009) B7793009
theorem B3458753 : Blo 1024605 3458753 := bstep (se 2 (by rfl) ⟨1297032, by rfl⟩ : syracuseStep 3458753 = 2594065) B2594065
theorem B2311883 : Blo 1024605 2311883 := bstep (se 1 (by rfl) ⟨1733912, by rfl⟩ : syracuseStep 2311883 = 3467825) B3467825
theorem B5916377 : Blo 1024605 5916377 := bstep (se 2 (by rfl) ⟨2218641, by rfl⟩ : syracuseStep 5916377 = 4437283) B4437283
theorem B2770649 : Blo 1024605 2770649 := bstep (se 2 (by rfl) ⟨1038993, by rfl⟩ : syracuseStep 2770649 = 2077987) B2077987
theorem B2311937 : Blo 1024605 2311937 := bstep (se 2 (by rfl) ⟨866976, by rfl⟩ : syracuseStep 2311937 = 1733953) B1733953
theorem B2770777 : Blo 1024605 2770777 := bstep (se 2 (by rfl) ⟨1039041, by rfl⟩ : syracuseStep 2770777 = 2078083) B2078083
theorem B2082689 : Blo 1024605 2082689 := bstep (se 2 (by rfl) ⟨781008, by rfl⟩ : syracuseStep 2082689 = 1562017) B1562017
theorem B1460119 : Blo 1024605 1460119 := bstep (se 1 (by rfl) ⟨1095089, by rfl⟩ : syracuseStep 1460119 = 2190179) B2190179
theorem B2312153 : Blo 1024605 2312153 := bstep (se 2 (by rfl) ⟨867057, by rfl⟩ : syracuseStep 2312153 = 1734115) B1734115
theorem B1951769 : Blo 1024605 1951769 := bstep (se 2 (by rfl) ⟨731913, by rfl⟩ : syracuseStep 1951769 = 1463827) B1463827
theorem B2312243 : Blo 1024605 2312243 := bstep (se 1 (by rfl) ⟨1734182, by rfl⟩ : syracuseStep 2312243 = 3468365) B3468365
theorem B2312279 : Blo 1024605 2312279 := bstep (se 1 (by rfl) ⟨1734209, by rfl⟩ : syracuseStep 2312279 = 3468419) B3468419
theorem B3459293 : Blo 1024605 3459293 := bstep (se 3 (by rfl) ⟨648617, by rfl⟩ : syracuseStep 3459293 = 1297235) B1297235
theorem B2312459 : Blo 1024605 2312459 := bstep (se 1 (by rfl) ⟨1734344, by rfl⟩ : syracuseStep 2312459 = 3468689) B3468689
theorem B4376855 : Blo 1024605 4376855 := bstep (se 1 (by rfl) ⟨3282641, by rfl⟩ : syracuseStep 4376855 = 6565283) B6565283
theorem B2312513 : Blo 1024605 2312513 := bstep (se 2 (by rfl) ⟨867192, by rfl⟩ : syracuseStep 2312513 = 1734385) B1734385
theorem B1460683 : Blo 1024605 1460683 := bstep (se 1 (by rfl) ⟨1095512, by rfl⟩ : syracuseStep 1460683 = 2191025) B2191025
theorem B2312729 : Blo 1024605 2312729 := bstep (se 2 (by rfl) ⟨867273, by rfl⟩ : syracuseStep 2312729 = 1734547) B1734547
theorem B2312819 : Blo 1024605 2312819 := bstep (se 1 (by rfl) ⟨1734614, by rfl⟩ : syracuseStep 2312819 = 3469229) B3469229
theorem B2312855 : Blo 1024605 2312855 := bstep (se 1 (by rfl) ⟨1734641, by rfl⟩ : syracuseStep 2312855 = 3469283) B3469283
theorem B5851865 : Blo 1024605 5851865 := bstep (se 2 (by rfl) ⟨2194449, by rfl⟩ : syracuseStep 5851865 = 4388899) B4388899
theorem B20007665 : Blo 1024605 20007665 := bstep (se 2 (by rfl) ⟨7502874, by rfl⟩ : syracuseStep 20007665 = 15005749) B15005749
theorem B7785233 : Blo 1024605 7785233 := bstep (se 2 (by rfl) ⟨2919462, by rfl⟩ : syracuseStep 7785233 = 5838925) B5838925
theorem B2313035 : Blo 1024605 2313035 := bstep (se 1 (by rfl) ⟨1734776, by rfl⟩ : syracuseStep 2313035 = 3469553) B3469553
theorem B2313089 : Blo 1024605 2313089 := bstep (se 2 (by rfl) ⟨867408, by rfl⟩ : syracuseStep 2313089 = 1734817) B1734817
theorem B1297291 : Blo 1024605 1297291 := bstep (se 1 (by rfl) ⟨972968, by rfl⟩ : syracuseStep 1297291 = 1945937) B1945937
theorem B2083915 : Blo 1024605 2083915 := bstep (se 1 (by rfl) ⟨1562936, by rfl⟩ : syracuseStep 2083915 = 3125873) B3125873
theorem B2313305 : Blo 1024605 2313305 := bstep (se 2 (by rfl) ⟨867489, by rfl⟩ : syracuseStep 2313305 = 1734979) B1734979
theorem B1297559 : Blo 1024605 1297559 := bstep (se 1 (by rfl) ⟨973169, by rfl⟩ : syracuseStep 1297559 = 1946339) B1946339
theorem B1756313 : Blo 1024605 1756313 := bstep (se 2 (by rfl) ⟨658617, by rfl⟩ : syracuseStep 1756313 = 1317235) B1317235
theorem B2313395 : Blo 1024605 2313395 := bstep (se 1 (by rfl) ⟨1735046, by rfl⟩ : syracuseStep 2313395 = 3470093) B3470093
theorem B2313431 : Blo 1024605 2313431 := bstep (se 1 (by rfl) ⟨1735073, by rfl⟩ : syracuseStep 2313431 = 3470147) B3470147
theorem B17517869 : Blo 1024605 17517869 := bstep (se 3 (by rfl) ⟨3284600, by rfl⟩ : syracuseStep 17517869 = 6569201) B6569201
theorem B5197121 : Blo 1024605 5197121 := bstep (se 2 (by rfl) ⟨1948920, by rfl⟩ : syracuseStep 5197121 = 3897841) B3897841
theorem B3460427 : Blo 1024605 3460427 := bstep (se 1 (by rfl) ⟨2595320, by rfl⟩ : syracuseStep 3460427 = 5190641) B5190641
theorem B2313611 : Blo 1024605 2313611 := bstep (se 1 (by rfl) ⟨1735208, by rfl⟩ : syracuseStep 2313611 = 3470417) B3470417
theorem B2313665 : Blo 1024605 2313665 := bstep (se 2 (by rfl) ⟨867624, by rfl⟩ : syracuseStep 2313665 = 1735249) B1735249
theorem B3460697 : Blo 1024605 3460697 := bstep (se 2 (by rfl) ⟨1297761, by rfl⟩ : syracuseStep 3460697 = 2595523) B2595523
theorem B6245981 : Blo 1024605 6245981 := bstep (se 3 (by rfl) ⟨1171121, by rfl⟩ : syracuseStep 6245981 = 2342243) B2342243
theorem B2313881 : Blo 1024605 2313881 := bstep (se 2 (by rfl) ⟨867705, by rfl⟩ : syracuseStep 2313881 = 1735411) B1735411
theorem B2313971 : Blo 1024605 2313971 := bstep (se 1 (by rfl) ⟨1735478, by rfl⟩ : syracuseStep 2313971 = 3470957) B3470957
theorem B2314007 : Blo 1024605 2314007 := bstep (se 1 (by rfl) ⟨1735505, by rfl⟩ : syracuseStep 2314007 = 3471011) B3471011
theorem B1298263 : Blo 1024605 1298263 := bstep (se 1 (by rfl) ⟨973697, by rfl⟩ : syracuseStep 1298263 = 1947395) B1947395
theorem B1462169 : Blo 1024605 1462169 := bstep (se 2 (by rfl) ⟨548313, by rfl⟩ : syracuseStep 1462169 = 1096627) B1096627
theorem B2314187 : Blo 1024605 2314187 := bstep (se 1 (by rfl) ⟨1735640, by rfl⟩ : syracuseStep 2314187 = 3471281) B3471281
theorem B2314241 : Blo 1024605 2314241 := bstep (se 2 (by rfl) ⟨867840, by rfl⟩ : syracuseStep 2314241 = 1735681) B1735681
theorem B4378769 : Blo 1024605 4378769 := bstep (se 2 (by rfl) ⟨1642038, by rfl⟩ : syracuseStep 4378769 = 3284077) B3284077
theorem B5558489 : Blo 1024605 5558489 := bstep (se 2 (by rfl) ⟨2084433, by rfl⟩ : syracuseStep 5558489 = 4168867) B4168867
theorem B3461399 : Blo 1024605 3461399 := bstep (se 1 (by rfl) ⟨2596049, by rfl⟩ : syracuseStep 3461399 = 5192099) B5192099
theorem B5853505 : Blo 1024605 5853505 := bstep (se 2 (by rfl) ⟨2195064, by rfl⟩ : syracuseStep 5853505 = 4390129) B4390129
theorem B1462807 : Blo 1024605 1462807 := bstep (se 1 (by rfl) ⟨1097105, by rfl⟩ : syracuseStep 1462807 = 2194211) B2194211
theorem B11752087 : Blo 1024605 11752087 := bstep (se 1 (by rfl) ⟨8814065, by rfl⟩ : syracuseStep 11752087 = 17628131) B17628131
theorem B3461939 : Blo 1024605 3461939 := bstep (se 1 (by rfl) ⟨2596454, by rfl⟩ : syracuseStep 3461939 = 5192909) B5192909
theorem B16896869 : Blo 1024605 16896869 := bstep (se 4 (by rfl) ⟨1584081, by rfl⟩ : syracuseStep 16896869 = 3168163) B3168163
theorem B3462209 : Blo 1024605 3462209 := bstep (se 2 (by rfl) ⟨1298328, by rfl⟩ : syracuseStep 3462209 = 2596657) B2596657
theorem B4379741 : Blo 1024605 4379741 := bstep (se 3 (by rfl) ⟨821201, by rfl⟩ : syracuseStep 4379741 = 1642403) B1642403
theorem B119821493 : Blo 1024605 119821493 := bstep (se 5 (by rfl) ⟨5616632, by rfl⟩ : syracuseStep 119821493 = 11233265) B11233265
theorem B5199065 : Blo 1024605 5199065 := bstep (se 2 (by rfl) ⟨1949649, by rfl⟩ : syracuseStep 5199065 = 3899299) B3899299
theorem B1463513 : Blo 1024605 1463513 := bstep (se 2 (by rfl) ⟨548817, by rfl⟩ : syracuseStep 1463513 = 1097635) B1097635
theorem B1463627 : Blo 1024605 1463627 := bstep (se 1 (by rfl) ⟨1097720, by rfl⟩ : syracuseStep 1463627 = 2195441) B2195441
theorem B1299979 : Blo 1024605 1299979 := bstep (se 1 (by rfl) ⟨974984, by rfl⟩ : syracuseStep 1299979 = 1949969) B1949969
theorem B3462749 : Blo 1024605 3462749 := bstep (se 3 (by rfl) ⟨649265, by rfl⟩ : syracuseStep 3462749 = 1298531) B1298531
theorem B1464151 : Blo 1024605 1464151 := bstep (se 1 (by rfl) ⟨1098113, by rfl⟩ : syracuseStep 1464151 = 2196227) B2196227
theorem B33249203 : Blo 1024605 33249203 := bstep (se 1 (by rfl) ⟨24936902, by rfl⟩ : syracuseStep 33249203 = 49873805) B49873805
theorem B6576173 : Blo 1024605 6576173 := bstep (se 3 (by rfl) ⟨1233032, by rfl⟩ : syracuseStep 6576173 = 2466065) B2466065
theorem B5003309 : Blo 1024605 5003309 := bstep (se 3 (by rfl) ⟨938120, by rfl⟩ : syracuseStep 5003309 = 1876241) B1876241
theorem B1235147 : Blo 1024605 1235147 := bstep (se 1 (by rfl) ⟨926360, by rfl⟩ : syracuseStep 1235147 = 1852721) B1852721
theorem B5921041 : Blo 1024605 5921041 := bstep (se 2 (by rfl) ⟨2220390, by rfl⟩ : syracuseStep 5921041 = 4440781) B4440781
theorem B1300951 : Blo 1024605 1300951 := bstep (se 1 (by rfl) ⟨975713, by rfl⟩ : syracuseStep 1300951 = 1951427) B1951427
theorem B13130201 : Blo 1024605 13130201 := bstep (se 2 (by rfl) ⟨4923825, by rfl⟩ : syracuseStep 13130201 = 9847651) B9847651
theorem B4381229 : Blo 1024605 4381229 := bstep (se 3 (by rfl) ⟨821480, by rfl⟩ : syracuseStep 4381229 = 1642961) B1642961
theorem B7789121 : Blo 1024605 7789121 := bstep (se 2 (by rfl) ⟨2920920, by rfl⟩ : syracuseStep 7789121 = 5841841) B5841841
theorem B3463883 : Blo 1024605 3463883 := bstep (se 1 (by rfl) ⟨2597912, by rfl⟩ : syracuseStep 3463883 = 5195825) B5195825
theorem B1039115 : Blo 1024605 1039115 := bstep (se 1 (by rfl) ⟨779336, by rfl⟩ : syracuseStep 1039115 = 1558673) B1558673
theorem B1170199 : Blo 1024605 1170199 := bstep (se 1 (by rfl) ⟨877649, by rfl⟩ : syracuseStep 1170199 = 1755299) B1755299
theorem B5200685 : Blo 1024605 5200685 := bstep (se 3 (by rfl) ⟨975128, by rfl⟩ : syracuseStep 5200685 = 1950257) B1950257
theorem B3431347 : Blo 1024605 3431347 := bstep (se 1 (by rfl) ⟨2573510, by rfl⟩ : syracuseStep 3431347 = 5147021) B5147021
theorem B3464153 : Blo 1024605 3464153 := bstep (se 2 (by rfl) ⟨1299057, by rfl⟩ : syracuseStep 3464153 = 2598115) B2598115
theorem B3169373 : Blo 1024605 3169373 := bstep (se 3 (by rfl) ⟨594257, by rfl⟩ : syracuseStep 3169373 = 1188515) B1188515
theorem B3890369 : Blo 1024605 3890369 := bstep (se 2 (by rfl) ⟨1458888, by rfl⟩ : syracuseStep 3890369 = 2917777) B2917777
theorem B1301771 : Blo 1024605 1301771 := bstep (se 1 (by rfl) ⟨976328, by rfl⟩ : syracuseStep 1301771 = 1952657) B1952657
theorem B3333469 : Blo 1024605 3333469 := bstep (se 3 (by rfl) ⟨625025, by rfl⟩ : syracuseStep 3333469 = 1250051) B1250051
theorem B119922061 : Blo 1024605 119922061 := bstep (se 3 (by rfl) ⟨22485386, by rfl⟩ : syracuseStep 119922061 = 44970773) B44970773
theorem B15228491 : Blo 1024605 15228491 := bstep (se 1 (by rfl) ⟨11421368, by rfl⟩ : syracuseStep 15228491 = 22842737) B22842737
theorem B3464855 : Blo 1024605 3464855 := bstep (se 1 (by rfl) ⟨2598641, by rfl⟩ : syracuseStep 3464855 = 5197283) B5197283
theorem B3694253 : Blo 1024605 3694253 := bstep (se 3 (by rfl) ⟨692672, by rfl⟩ : syracuseStep 3694253 = 1385345) B1385345
theorem B5856947 : Blo 1024605 5856947 := bstep (se 1 (by rfl) ⟨4392710, by rfl⟩ : syracuseStep 5856947 = 8785421) B8785421
theorem B2776855 : Blo 1024605 2776855 := bstep (se 1 (by rfl) ⟨2082641, by rfl⟩ : syracuseStep 2776855 = 4165283) B4165283
theorem B3891037 : Blo 1024605 3891037 := bstep (se 3 (by rfl) ⟨729569, by rfl⟩ : syracuseStep 3891037 = 1459139) B1459139
theorem B8773697 : Blo 1024605 8773697 := bstep (se 2 (by rfl) ⟨3290136, by rfl⟩ : syracuseStep 8773697 = 6580273) B6580273
theorem B3465395 : Blo 1024605 3465395 := bstep (se 1 (by rfl) ⟨2599046, by rfl⟩ : syracuseStep 3465395 = 5198093) B5198093
theorem B2777437 : Blo 1024605 2777437 := bstep (se 3 (by rfl) ⟨520769, by rfl⟩ : syracuseStep 2777437 = 1041539) B1041539
theorem B3465665 : Blo 1024605 3465665 := bstep (se 2 (by rfl) ⟨1299624, by rfl⟩ : syracuseStep 3465665 = 2599249) B2599249
theorem B7791065 : Blo 1024605 7791065 := bstep (se 2 (by rfl) ⟨2921649, by rfl⟩ : syracuseStep 7791065 = 5843299) B5843299
theorem B4383193 : Blo 1024605 4383193 := bstep (se 2 (by rfl) ⟨1643697, by rfl⟩ : syracuseStep 4383193 = 3287395) B3287395
theorem B3466205 : Blo 1024605 3466205 := bstep (se 3 (by rfl) ⟨649913, by rfl⟩ : syracuseStep 3466205 = 1299827) B1299827
theorem B1729559 : Blo 1024605 1729559 := bstep (se 1 (by rfl) ⟨1297169, by rfl⟩ : syracuseStep 1729559 = 2594339) B2594339
theorem B3892313 : Blo 1024605 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B1729687 : Blo 1024605 1729687 := bstep (se 1 (by rfl) ⟨1297265, by rfl⟩ : syracuseStep 1729687 = 2594531) B2594531
theorem B4678829 : Blo 1024605 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B11101445 : Blo 1024605 11101445 := bstep (se 4 (by rfl) ⟨1040760, by rfl⟩ : syracuseStep 11101445 = 2081521) B2081521
theorem B2188633 : Blo 1024605 2188633 := bstep (se 2 (by rfl) ⟨820737, by rfl⟩ : syracuseStep 2188633 = 1641475) B1641475
theorem B4384151 : Blo 1024605 4384151 := bstep (se 1 (by rfl) ⟨3288113, by rfl⟩ : syracuseStep 4384151 = 6576227) B6576227
theorem B6579863 : Blo 1024605 6579863 := bstep (se 1 (by rfl) ⟨4934897, by rfl⟩ : syracuseStep 6579863 = 9869795) B9869795
theorem B7399117 : Blo 1024605 7399117 := bstep (se 3 (by rfl) ⟨1387334, by rfl⟩ : syracuseStep 7399117 = 2774669) B2774669
theorem B1730315 : Blo 1024605 1730315 := bstep (se 1 (by rfl) ⟨1297736, by rfl⟩ : syracuseStep 1730315 = 2595473) B2595473
theorem B4450099 : Blo 1024605 4450099 := bstep (se 1 (by rfl) ⟨3337574, by rfl⟩ : syracuseStep 4450099 = 6675149) B6675149
theorem B22177637 : Blo 1024605 22177637 := bstep (se 4 (by rfl) ⟨2079153, by rfl⟩ : syracuseStep 22177637 = 4158307) B4158307
theorem B1730443 : Blo 1024605 1730443 := bstep (se 1 (by rfl) ⟨1297832, by rfl⟩ : syracuseStep 1730443 = 2595665) B2595665
theorem B3958721 : Blo 1024605 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B1730585 : Blo 1024605 1730585 := bstep (se 2 (by rfl) ⟨648969, by rfl⟩ : syracuseStep 1730585 = 1297939) B1297939
theorem B3467339 : Blo 1024605 3467339 := bstep (se 1 (by rfl) ⟨2600504, by rfl⟩ : syracuseStep 3467339 = 5201009) B5201009
theorem B1730713 : Blo 1024605 1730713 := bstep (se 2 (by rfl) ⟨649017, by rfl⟩ : syracuseStep 1730713 = 1298035) B1298035
theorem B3467609 : Blo 1024605 3467609 := bstep (se 2 (by rfl) ⟨1300353, by rfl⟩ : syracuseStep 3467609 = 2600707) B2600707
theorem B2189683 : Blo 1024605 2189683 := bstep (se 1 (by rfl) ⟨1642262, by rfl⟩ : syracuseStep 2189683 = 3284525) B3284525
theorem B3664273 : Blo 1024605 3664273 := bstep (se 2 (by rfl) ⟨1374102, by rfl⟩ : syracuseStep 3664273 = 2748205) B2748205
theorem B10119755 : Blo 1024605 10119755 := bstep (se 1 (by rfl) ⟨7589816, by rfl⟩ : syracuseStep 10119755 = 15179633) B15179633
theorem B5204573 : Blo 1024605 5204573 := bstep (se 3 (by rfl) ⟨975857, by rfl⟩ : syracuseStep 5204573 = 1951715) B1951715
theorem B3893939 : Blo 1024605 3893939 := bstep (se 1 (by rfl) ⟨2920454, by rfl⟩ : syracuseStep 3893939 = 5840909) B5840909
theorem B3893953 : Blo 1024605 3893953 := bstep (se 2 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 3893953 = 2920465) B2920465
theorem B1731287 : Blo 1024605 1731287 := bstep (se 1 (by rfl) ⟨1298465, by rfl⟩ : syracuseStep 1731287 = 2596931) B2596931
theorem B3697483 : Blo 1024605 3697483 := bstep (se 1 (by rfl) ⟨2773112, by rfl⟩ : syracuseStep 3697483 = 5546225) B5546225
theorem B1731415 : Blo 1024605 1731415 := bstep (se 1 (by rfl) ⟨1298561, by rfl⟩ : syracuseStep 1731415 = 2597123) B2597123
theorem B284322757 : Blo 1024605 284322757 := bstep (se 4 (by rfl) ⟨26655258, by rfl⟩ : syracuseStep 284322757 = 53310517) B53310517
theorem B3468311 : Blo 1024605 3468311 := bstep (se 1 (by rfl) ⟨2601233, by rfl⟩ : syracuseStep 3468311 = 5202467) B5202467
theorem B1666073 : Blo 1024605 1666073 := bstep (se 2 (by rfl) ⟨624777, by rfl⟩ : syracuseStep 1666073 = 1249555) B1249555
theorem B1732043 : Blo 1024605 1732043 := bstep (se 1 (by rfl) ⟨1299032, by rfl⟩ : syracuseStep 1732043 = 2598065) B2598065
theorem B26668561 : Blo 1024605 26668561 := bstep (se 2 (by rfl) ⟨10000710, by rfl⟩ : syracuseStep 26668561 = 20001421) B20001421
theorem B3468851 : Blo 1024605 3468851 := bstep (se 1 (by rfl) ⟨2601638, by rfl⟩ : syracuseStep 3468851 = 5203277) B5203277
theorem B1732171 : Blo 1024605 1732171 := bstep (se 1 (by rfl) ⟨1299128, by rfl⟩ : syracuseStep 1732171 = 2598257) B2598257
theorem B1732313 : Blo 1024605 1732313 := bstep (se 2 (by rfl) ⟨649617, by rfl⟩ : syracuseStep 1732313 = 1299235) B1299235
theorem B7794467 : Blo 1024605 7794467 := bstep (se 1 (by rfl) ⟨5845850, by rfl⟩ : syracuseStep 7794467 = 11691701) B11691701
theorem B2191169 : Blo 1024605 2191169 := bstep (se 2 (by rfl) ⟨821688, by rfl⟩ : syracuseStep 2191169 = 1643377) B1643377
theorem B3469121 : Blo 1024605 3469121 := bstep (se 2 (by rfl) ⟨1300920, by rfl⟩ : syracuseStep 3469121 = 2601841) B2601841
theorem B1732441 : Blo 1024605 1732441 := bstep (se 2 (by rfl) ⟨649665, by rfl⟩ : syracuseStep 1732441 = 1299331) B1299331
theorem B2191511 : Blo 1024605 2191511 := bstep (se 1 (by rfl) ⟨1643633, by rfl⟩ : syracuseStep 2191511 = 3287267) B3287267
theorem B3698867 : Blo 1024605 3698867 := bstep (se 1 (by rfl) ⟨2774150, by rfl⟩ : syracuseStep 3698867 = 5548301) B5548301
theorem B3469661 : Blo 1024605 3469661 := bstep (se 3 (by rfl) ⟨650561, by rfl⟩ : syracuseStep 3469661 = 1301123) B1301123
theorem B1733015 : Blo 1024605 1733015 := bstep (se 1 (by rfl) ⟨1299761, by rfl⟩ : syracuseStep 1733015 = 2599523) B2599523
theorem B2191819 : Blo 1024605 2191819 := bstep (se 1 (by rfl) ⟨1643864, by rfl⟩ : syracuseStep 2191819 = 3287729) B3287729
theorem B1733143 : Blo 1024605 1733143 := bstep (se 1 (by rfl) ⟨1299857, by rfl⟩ : syracuseStep 1733143 = 2599715) B2599715
theorem B3895883 : Blo 1024605 3895883 := bstep (se 1 (by rfl) ⟨2921912, by rfl⟩ : syracuseStep 3895883 = 5843825) B5843825
theorem B3895897 : Blo 1024605 3895897 := bstep (se 2 (by rfl) ⟨1460961, by rfl⟩ : syracuseStep 3895897 = 2921923) B2921923
theorem B13529693 : Blo 1024605 13529693 := bstep (se 3 (by rfl) ⟨2536817, by rfl⟩ : syracuseStep 13529693 = 5073635) B5073635
theorem B5206679 : Blo 1024605 5206679 := bstep (se 1 (by rfl) ⟨3905009, by rfl⟩ : syracuseStep 5206679 = 7810019) B7810019
theorem B4387601 : Blo 1024605 4387601 := bstep (se 2 (by rfl) ⟨1645350, by rfl⟩ : syracuseStep 4387601 = 3290701) B3290701
theorem B5010221 : Blo 1024605 5010221 := bstep (se 3 (by rfl) ⟨939416, by rfl⟩ : syracuseStep 5010221 = 1878833) B1878833
theorem B12678065 : Blo 1024605 12678065 := bstep (se 2 (by rfl) ⟨4754274, by rfl⟩ : syracuseStep 12678065 = 9508549) B9508549
theorem B1536971 : Blo 1024605 1536971 := bstep (se 1 (by rfl) ⟨1152728, by rfl⟩ : syracuseStep 1536971 = 2305457) B2305457
theorem B1536983 : Blo 1024605 1536983 := bstep (se 1 (by rfl) ⟨1152737, by rfl⟩ : syracuseStep 1536983 = 2305475) B2305475
theorem B1537049 : Blo 1024605 1537049 := bstep (se 2 (by rfl) ⟨576393, by rfl⟩ : syracuseStep 1537049 = 1152787) B1152787
theorem B1537163 : Blo 1024605 1537163 := bstep (se 1 (by rfl) ⟨1152872, by rfl⟩ : syracuseStep 1537163 = 2305745) B2305745
theorem B1733771 : Blo 1024605 1733771 := bstep (se 1 (by rfl) ⟨1300328, by rfl⟩ : syracuseStep 1733771 = 2600657) B2600657
theorem B1537175 : Blo 1024605 1537175 := bstep (se 1 (by rfl) ⟨1152881, by rfl⟩ : syracuseStep 1537175 = 2305763) B2305763
theorem B1537241 : Blo 1024605 1537241 := bstep (se 2 (by rfl) ⟨576465, by rfl⟩ : syracuseStep 1537241 = 1152931) B1152931
theorem B1733899 : Blo 1024605 1733899 := bstep (se 1 (by rfl) ⟨1300424, by rfl⟩ : syracuseStep 1733899 = 2600849) B2600849
theorem B2192665 : Blo 1024605 2192665 := bstep (se 2 (by rfl) ⟨822249, by rfl⟩ : syracuseStep 2192665 = 1644499) B1644499
theorem B1537355 : Blo 1024605 1537355 := bstep (se 1 (by rfl) ⟨1153016, by rfl⟩ : syracuseStep 1537355 = 2306033) B2306033
theorem B1537367 : Blo 1024605 1537367 := bstep (se 1 (by rfl) ⟨1153025, by rfl⟩ : syracuseStep 1537367 = 2306051) B2306051
theorem B1537433 : Blo 1024605 1537433 := bstep (se 2 (by rfl) ⟨576537, by rfl⟩ : syracuseStep 1537433 = 1153075) B1153075
theorem B1734041 : Blo 1024605 1734041 := bstep (se 2 (by rfl) ⟨650265, by rfl⟩ : syracuseStep 1734041 = 1300531) B1300531
theorem B3470795 : Blo 1024605 3470795 := bstep (se 1 (by rfl) ⟨2603096, by rfl⟩ : syracuseStep 3470795 = 5206193) B5206193
theorem B1537547 : Blo 1024605 1537547 := bstep (se 1 (by rfl) ⟨1153160, by rfl⟩ : syracuseStep 1537547 = 2306321) B2306321
theorem B1537559 : Blo 1024605 1537559 := bstep (se 1 (by rfl) ⟨1153169, by rfl⟩ : syracuseStep 1537559 = 2306339) B2306339
theorem B3896855 : Blo 1024605 3896855 := bstep (se 1 (by rfl) ⟨2922641, by rfl⟩ : syracuseStep 3896855 = 5845283) B5845283
theorem B1734169 : Blo 1024605 1734169 := bstep (se 2 (by rfl) ⟨650313, by rfl⟩ : syracuseStep 1734169 = 1300627) B1300627
theorem B1537625 : Blo 1024605 1537625 := bstep (se 2 (by rfl) ⟨576609, by rfl⟩ : syracuseStep 1537625 = 1153219) B1153219
theorem B3700397 : Blo 1024605 3700397 := bstep (se 3 (by rfl) ⟨693824, by rfl⟩ : syracuseStep 3700397 = 1387649) B1387649
theorem B4388525 : Blo 1024605 4388525 := bstep (se 3 (by rfl) ⟨822848, by rfl⟩ : syracuseStep 4388525 = 1645697) B1645697
theorem B5273267 : Blo 1024605 5273267 := bstep (se 1 (by rfl) ⟨3954950, by rfl⟩ : syracuseStep 5273267 = 7909901) B7909901
theorem B1537739 : Blo 1024605 1537739 := bstep (se 1 (by rfl) ⟨1153304, by rfl⟩ : syracuseStep 1537739 = 2306609) B2306609
theorem B1537751 : Blo 1024605 1537751 := bstep (se 1 (by rfl) ⟨1153313, by rfl⟩ : syracuseStep 1537751 = 2306627) B2306627
theorem B3471065 : Blo 1024605 3471065 := bstep (se 2 (by rfl) ⟨1301649, by rfl⟩ : syracuseStep 3471065 = 2603299) B2603299
theorem B1537817 : Blo 1024605 1537817 := bstep (se 2 (by rfl) ⟨576681, by rfl⟩ : syracuseStep 1537817 = 1153363) B1153363
theorem B1111883 : Blo 1024605 1111883 := bstep (se 1 (by rfl) ⟨833912, by rfl⟩ : syracuseStep 1111883 = 1667825) B1667825
theorem B1111915 : Blo 1024605 1111915 := bstep (se 1 (by rfl) ⟨833936, by rfl⟩ : syracuseStep 1111915 = 1667873) B1667873
theorem B1537931 : Blo 1024605 1537931 := bstep (se 1 (by rfl) ⟨1153448, by rfl⟩ : syracuseStep 1537931 = 2306897) B2306897
theorem B1537943 : Blo 1024605 1537943 := bstep (se 1 (by rfl) ⟨1153457, by rfl⟩ : syracuseStep 1537943 = 2306915) B2306915
theorem B1538009 : Blo 1024605 1538009 := bstep (se 2 (by rfl) ⟨576753, by rfl⟩ : syracuseStep 1538009 = 1153507) B1153507
theorem B1538123 : Blo 1024605 1538123 := bstep (se 1 (by rfl) ⟨1153592, by rfl⟩ : syracuseStep 1538123 = 2307185) B2307185
theorem B1538135 : Blo 1024605 1538135 := bstep (se 1 (by rfl) ⟨1153601, by rfl⟩ : syracuseStep 1538135 = 2307203) B2307203
theorem B1734743 : Blo 1024605 1734743 := bstep (se 1 (by rfl) ⟨1301057, by rfl⟩ : syracuseStep 1734743 = 2602115) B2602115
theorem B3700829 : Blo 1024605 3700829 := bstep (se 3 (by rfl) ⟨693905, by rfl⟩ : syracuseStep 3700829 = 1387811) B1387811
theorem B8321125 : Blo 1024605 8321125 := bstep (se 4 (by rfl) ⟨780105, by rfl⟩ : syracuseStep 8321125 = 1560211) B1560211
theorem B1538201 : Blo 1024605 1538201 := bstep (se 2 (by rfl) ⟨576825, by rfl⟩ : syracuseStep 1538201 = 1153651) B1153651
theorem B1734871 : Blo 1024605 1734871 := bstep (se 1 (by rfl) ⟨1301153, by rfl⟩ : syracuseStep 1734871 = 2602307) B2602307
theorem B8321285 : Blo 1024605 8321285 := bstep (se 4 (by rfl) ⟨780120, by rfl⟩ : syracuseStep 8321285 = 1560241) B1560241
theorem B1538315 : Blo 1024605 1538315 := bstep (se 1 (by rfl) ⟨1153736, by rfl⟩ : syracuseStep 1538315 = 2307473) B2307473
theorem B1538327 : Blo 1024605 1538327 := bstep (se 1 (by rfl) ⟨1153745, by rfl⟩ : syracuseStep 1538327 = 2307491) B2307491
theorem B19757357 : Blo 1024605 19757357 := bstep (se 3 (by rfl) ⟨3704504, by rfl⟩ : syracuseStep 19757357 = 7409009) B7409009
theorem B1538393 : Blo 1024605 1538393 := bstep (se 2 (by rfl) ⟨576897, by rfl⟩ : syracuseStep 1538393 = 1153795) B1153795
theorem B1538507 : Blo 1024605 1538507 := bstep (se 1 (by rfl) ⟨1153880, by rfl⟩ : syracuseStep 1538507 = 2307761) B2307761
theorem B1538519 : Blo 1024605 1538519 := bstep (se 1 (by rfl) ⟨1153889, by rfl⟩ : syracuseStep 1538519 = 2307779) B2307779
theorem B1538585 : Blo 1024605 1538585 := bstep (se 2 (by rfl) ⟨576969, by rfl⟩ : syracuseStep 1538585 = 1153939) B1153939
theorem B2193971 : Blo 1024605 2193971 := bstep (se 1 (by rfl) ⟨1645478, by rfl⟩ : syracuseStep 2193971 = 3290957) B3290957
theorem B1538699 : Blo 1024605 1538699 := bstep (se 1 (by rfl) ⟨1154024, by rfl⟩ : syracuseStep 1538699 = 2308049) B2308049
theorem B1538711 : Blo 1024605 1538711 := bstep (se 1 (by rfl) ⟨1154033, by rfl⟩ : syracuseStep 1538711 = 2308067) B2308067
theorem B29588165 : Blo 1024605 29588165 := bstep (se 4 (by rfl) ⟨2773890, by rfl⟩ : syracuseStep 29588165 = 5547781) B5547781
theorem B8321741 : Blo 1024605 8321741 := bstep (se 3 (by rfl) ⟨1560326, by rfl⟩ : syracuseStep 8321741 = 3120653) B3120653
theorem B1538777 : Blo 1024605 1538777 := bstep (se 2 (by rfl) ⟨577041, by rfl⟩ : syracuseStep 1538777 = 1154083) B1154083
theorem B3898115 : Blo 1024605 3898115 := bstep (se 1 (by rfl) ⟨2923586, by rfl⟩ : syracuseStep 3898115 = 5847173) B5847173
theorem B5274433 : Blo 1024605 5274433 := bstep (se 2 (by rfl) ⟨1977912, by rfl⟩ : syracuseStep 5274433 = 3955825) B3955825
theorem B1538891 : Blo 1024605 1538891 := bstep (se 1 (by rfl) ⟨1154168, by rfl⟩ : syracuseStep 1538891 = 2308337) B2308337
theorem B1735499 : Blo 1024605 1735499 := bstep (se 1 (by rfl) ⟨1301624, by rfl⟩ : syracuseStep 1735499 = 2603249) B2603249
theorem B1538903 : Blo 1024605 1538903 := bstep (se 1 (by rfl) ⟨1154177, by rfl⟩ : syracuseStep 1538903 = 2308355) B2308355
theorem B1538969 : Blo 1024605 1538969 := bstep (se 2 (by rfl) ⟨577113, by rfl⟩ : syracuseStep 1538969 = 1154227) B1154227
theorem B1735627 : Blo 1024605 1735627 := bstep (se 1 (by rfl) ⟨1301720, by rfl⟩ : syracuseStep 1735627 = 2603441) B2603441
theorem B19004377 : Blo 1024605 19004377 := bstep (se 2 (by rfl) ⟨7126641, by rfl⟩ : syracuseStep 19004377 = 14253283) B14253283
theorem B1539083 : Blo 1024605 1539083 := bstep (se 1 (by rfl) ⟨1154312, by rfl⟩ : syracuseStep 1539083 = 2308625) B2308625
theorem B1539095 : Blo 1024605 1539095 := bstep (se 1 (by rfl) ⟨1154321, by rfl⟩ : syracuseStep 1539095 = 2308643) B2308643
theorem B1539161 : Blo 1024605 1539161 := bstep (se 2 (by rfl) ⟨577185, by rfl⟩ : syracuseStep 1539161 = 1154371) B1154371
theorem B4389977 : Blo 1024605 4389977 := bstep (se 2 (by rfl) ⟨1646241, by rfl⟩ : syracuseStep 4389977 = 3292483) B3292483
theorem B1735769 : Blo 1024605 1735769 := bstep (se 2 (by rfl) ⟨650913, by rfl⟩ : syracuseStep 1735769 = 1301827) B1301827
theorem B1539275 : Blo 1024605 1539275 := bstep (se 1 (by rfl) ⟨1154456, by rfl⟩ : syracuseStep 1539275 = 2308913) B2308913
theorem B1539287 : Blo 1024605 1539287 := bstep (se 1 (by rfl) ⟨1154465, by rfl⟩ : syracuseStep 1539287 = 2308931) B2308931
theorem B1539353 : Blo 1024605 1539353 := bstep (se 2 (by rfl) ⟨577257, by rfl⟩ : syracuseStep 1539353 = 1154515) B1154515
theorem B1539467 : Blo 1024605 1539467 := bstep (se 1 (by rfl) ⟨1154600, by rfl⟩ : syracuseStep 1539467 = 2309201) B2309201
theorem B1539479 : Blo 1024605 1539479 := bstep (se 1 (by rfl) ⟨1154609, by rfl⟩ : syracuseStep 1539479 = 2309219) B2309219
theorem B1539545 : Blo 1024605 1539545 := bstep (se 2 (by rfl) ⟨577329, by rfl⟩ : syracuseStep 1539545 = 1154659) B1154659
theorem B7405091 : Blo 1024605 7405091 := bstep (se 1 (by rfl) ⟨5553818, by rfl⟩ : syracuseStep 7405091 = 11107637) B11107637
theorem B1539659 : Blo 1024605 1539659 := bstep (se 1 (by rfl) ⟨1154744, by rfl⟩ : syracuseStep 1539659 = 2309489) B2309489
theorem B1539671 : Blo 1024605 1539671 := bstep (se 1 (by rfl) ⟨1154753, by rfl⟩ : syracuseStep 1539671 = 2309507) B2309507
theorem B1539737 : Blo 1024605 1539737 := bstep (se 2 (by rfl) ⟨577401, by rfl⟩ : syracuseStep 1539737 = 1154803) B1154803
theorem B1539851 : Blo 1024605 1539851 := bstep (se 1 (by rfl) ⟨1154888, by rfl⟩ : syracuseStep 1539851 = 2309777) B2309777
theorem B1539863 : Blo 1024605 1539863 := bstep (se 1 (by rfl) ⟨1154897, by rfl⟩ : syracuseStep 1539863 = 2309795) B2309795
theorem B1539929 : Blo 1024605 1539929 := bstep (se 2 (by rfl) ⟨577473, by rfl⟩ : syracuseStep 1539929 = 1154947) B1154947
theorem B1540043 : Blo 1024605 1540043 := bstep (se 1 (by rfl) ⟨1155032, by rfl⟩ : syracuseStep 1540043 = 2310065) B2310065
theorem B1540055 : Blo 1024605 1540055 := bstep (se 1 (by rfl) ⟨1155041, by rfl⟩ : syracuseStep 1540055 = 2310083) B2310083
theorem B1540103 : Blo 1024605 1540103 := bstep (se 1 (by rfl) ⟨1155077, by rfl⟩ : syracuseStep 1540103 = 2310155) B2310155
theorem B1540139 : Blo 1024605 1540139 := bstep (se 1 (by rfl) ⟨1155104, by rfl⟩ : syracuseStep 1540139 = 2310209) B2310209
theorem B1540169 : Blo 1024605 1540169 := bstep (se 2 (by rfl) ⟨577563, by rfl⟩ : syracuseStep 1540169 = 1155127) B1155127
theorem B1540283 : Blo 1024605 1540283 := bstep (se 1 (by rfl) ⟨1155212, by rfl⟩ : syracuseStep 1540283 = 2310425) B2310425
theorem B1540343 : Blo 1024605 1540343 := bstep (se 1 (by rfl) ⟨1155257, by rfl⟩ : syracuseStep 1540343 = 2310515) B2310515
theorem B1540367 : Blo 1024605 1540367 := bstep (se 1 (by rfl) ⟨1155275, by rfl⟩ : syracuseStep 1540367 = 2310551) B2310551
theorem B1540409 : Blo 1024605 1540409 := bstep (se 2 (by rfl) ⟨577653, by rfl⟩ : syracuseStep 1540409 = 1155307) B1155307
theorem B1540487 : Blo 1024605 1540487 := bstep (se 1 (by rfl) ⟨1155365, by rfl⟩ : syracuseStep 1540487 = 2310731) B2310731
theorem B1540523 : Blo 1024605 1540523 := bstep (se 1 (by rfl) ⟨1155392, by rfl⟩ : syracuseStep 1540523 = 2310785) B2310785
theorem B1540553 : Blo 1024605 1540553 := bstep (se 2 (by rfl) ⟨577707, by rfl⟩ : syracuseStep 1540553 = 1155415) B1155415
theorem B3703249 : Blo 1024605 3703249 := bstep (se 2 (by rfl) ⟨1388718, by rfl⟩ : syracuseStep 3703249 = 2777437) B2777437
theorem B1540667 : Blo 1024605 1540667 := bstep (se 1 (by rfl) ⟨1155500, by rfl⟩ : syracuseStep 1540667 = 2311001) B2311001
theorem B1540727 : Blo 1024605 1540727 := bstep (se 1 (by rfl) ⟨1155545, by rfl⟩ : syracuseStep 1540727 = 2311091) B2311091
theorem B1540751 : Blo 1024605 1540751 := bstep (se 1 (by rfl) ⟨1155563, by rfl⟩ : syracuseStep 1540751 = 2311127) B2311127
theorem B1540793 : Blo 1024605 1540793 := bstep (se 2 (by rfl) ⟨577797, by rfl⟩ : syracuseStep 1540793 = 1155595) B1155595
theorem B1540871 : Blo 1024605 1540871 := bstep (se 1 (by rfl) ⟨1155653, by rfl⟩ : syracuseStep 1540871 = 2311307) B2311307
theorem B1540907 : Blo 1024605 1540907 := bstep (se 1 (by rfl) ⟨1155680, by rfl⟩ : syracuseStep 1540907 = 2311361) B2311361
theorem B1540937 : Blo 1024605 1540937 := bstep (se 2 (by rfl) ⟨577851, by rfl⟩ : syracuseStep 1540937 = 1155703) B1155703
theorem B1541051 : Blo 1024605 1541051 := bstep (se 1 (by rfl) ⟨1155788, by rfl⟩ : syracuseStep 1541051 = 2311577) B2311577
theorem B1541111 : Blo 1024605 1541111 := bstep (se 1 (by rfl) ⟨1155833, by rfl⟩ : syracuseStep 1541111 = 2311667) B2311667
theorem B1541135 : Blo 1024605 1541135 := bstep (se 1 (by rfl) ⟨1155851, by rfl⟩ : syracuseStep 1541135 = 2311703) B2311703
theorem B1541177 : Blo 1024605 1541177 := bstep (se 2 (by rfl) ⟨577941, by rfl⟩ : syracuseStep 1541177 = 1155883) B1155883
theorem B1541255 : Blo 1024605 1541255 := bstep (se 1 (by rfl) ⟨1155941, by rfl⟩ : syracuseStep 1541255 = 2311883) B2311883
theorem B1541291 : Blo 1024605 1541291 := bstep (se 1 (by rfl) ⟨1155968, by rfl⟩ : syracuseStep 1541291 = 2311937) B2311937
theorem B1541321 : Blo 1024605 1541321 := bstep (se 2 (by rfl) ⟨577995, by rfl⟩ : syracuseStep 1541321 = 1155991) B1155991
theorem B1541435 : Blo 1024605 1541435 := bstep (se 1 (by rfl) ⟨1156076, by rfl⟩ : syracuseStep 1541435 = 2312153) B2312153
theorem B1541495 : Blo 1024605 1541495 := bstep (se 1 (by rfl) ⟨1156121, by rfl⟩ : syracuseStep 1541495 = 2312243) B2312243
theorem B1541519 : Blo 1024605 1541519 := bstep (se 1 (by rfl) ⟨1156139, by rfl⟩ : syracuseStep 1541519 = 2312279) B2312279
theorem B1541561 : Blo 1024605 1541561 := bstep (se 2 (by rfl) ⟨578085, by rfl⟩ : syracuseStep 1541561 = 1156171) B1156171
theorem B1541639 : Blo 1024605 1541639 := bstep (se 1 (by rfl) ⟨1156229, by rfl⟩ : syracuseStep 1541639 = 2312459) B2312459
theorem B2917903 : Blo 1024605 2917903 := bstep (se 1 (by rfl) ⟨2188427, by rfl⟩ : syracuseStep 2917903 = 4376855) B4376855
theorem B1541675 : Blo 1024605 1541675 := bstep (se 1 (by rfl) ⟨1156256, by rfl⟩ : syracuseStep 1541675 = 2312513) B2312513
theorem B1541705 : Blo 1024605 1541705 := bstep (se 2 (by rfl) ⟨578139, by rfl⟩ : syracuseStep 1541705 = 1156279) B1156279
theorem B36079181 : Blo 1024605 36079181 := bstep (se 3 (by rfl) ⟨6764846, by rfl⟩ : syracuseStep 36079181 = 13529693) B13529693
theorem B1541819 : Blo 1024605 1541819 := bstep (se 1 (by rfl) ⟨1156364, by rfl⟩ : syracuseStep 1541819 = 2312729) B2312729
theorem B1541879 : Blo 1024605 1541879 := bstep (se 1 (by rfl) ⟨1156409, by rfl⟩ : syracuseStep 1541879 = 2312819) B2312819
theorem B1541903 : Blo 1024605 1541903 := bstep (se 1 (by rfl) ⟨1156427, by rfl⟩ : syracuseStep 1541903 = 2312855) B2312855
theorem B2918177 : Blo 1024605 2918177 := bstep (se 2 (by rfl) ⟨1094316, by rfl⟩ : syracuseStep 2918177 = 2188633) B2188633
theorem B22513457 : Blo 1024605 22513457 := bstep (se 2 (by rfl) ⟨8442546, by rfl⟩ : syracuseStep 22513457 = 16885093) B16885093
theorem B1541945 : Blo 1024605 1541945 := bstep (se 2 (by rfl) ⟨578229, by rfl⟩ : syracuseStep 1541945 = 1156459) B1156459
theorem B3901243 : Blo 1024605 3901243 := bstep (se 1 (by rfl) ⟨2925932, by rfl⟩ : syracuseStep 3901243 = 5851865) B5851865
theorem B13338443 : Blo 1024605 13338443 := bstep (se 1 (by rfl) ⟨10003832, by rfl⟩ : syracuseStep 13338443 = 20007665) B20007665
theorem B1542023 : Blo 1024605 1542023 := bstep (se 1 (by rfl) ⟨1156517, by rfl⟩ : syracuseStep 1542023 = 2313035) B2313035
theorem B1542059 : Blo 1024605 1542059 := bstep (se 1 (by rfl) ⟨1156544, by rfl⟩ : syracuseStep 1542059 = 2313089) B2313089
theorem B1542089 : Blo 1024605 1542089 := bstep (se 2 (by rfl) ⟨578283, by rfl⟩ : syracuseStep 1542089 = 1156567) B1156567
theorem B1542203 : Blo 1024605 1542203 := bstep (se 1 (by rfl) ⟨1156652, by rfl⟩ : syracuseStep 1542203 = 2313305) B2313305
theorem B1542263 : Blo 1024605 1542263 := bstep (se 1 (by rfl) ⟨1156697, by rfl⟩ : syracuseStep 1542263 = 2313395) B2313395
theorem B1542287 : Blo 1024605 1542287 := bstep (se 1 (by rfl) ⟨1156715, by rfl⟩ : syracuseStep 1542287 = 2313431) B2313431
theorem B1542329 : Blo 1024605 1542329 := bstep (se 2 (by rfl) ⟨578373, by rfl⟩ : syracuseStep 1542329 = 1156747) B1156747
theorem B1542407 : Blo 1024605 1542407 := bstep (se 1 (by rfl) ⟨1156805, by rfl⟩ : syracuseStep 1542407 = 2313611) B2313611
theorem B9865489 : Blo 1024605 9865489 := bstep (se 2 (by rfl) ⟨3699558, by rfl⟩ : syracuseStep 9865489 = 7399117) B7399117
theorem B3901729 : Blo 1024605 3901729 := bstep (se 2 (by rfl) ⟨1463148, by rfl⟩ : syracuseStep 3901729 = 2926297) B2926297
theorem B1542443 : Blo 1024605 1542443 := bstep (se 1 (by rfl) ⟨1156832, by rfl⟩ : syracuseStep 1542443 = 2313665) B2313665
theorem B1542473 : Blo 1024605 1542473 := bstep (se 2 (by rfl) ⟨578427, by rfl⟩ : syracuseStep 1542473 = 1156855) B1156855
theorem B4163987 : Blo 1024605 4163987 := bstep (se 1 (by rfl) ⟨3122990, by rfl⟩ : syracuseStep 4163987 = 6245981) B6245981
theorem B5933465 : Blo 1024605 5933465 := bstep (se 2 (by rfl) ⟨2225049, by rfl⟩ : syracuseStep 5933465 = 4450099) B4450099
theorem B1542587 : Blo 1024605 1542587 := bstep (se 1 (by rfl) ⟨1156940, by rfl⟩ : syracuseStep 1542587 = 2313881) B2313881
theorem B1542647 : Blo 1024605 1542647 := bstep (se 1 (by rfl) ⟨1156985, by rfl⟩ : syracuseStep 1542647 = 2313971) B2313971
theorem B1542671 : Blo 1024605 1542671 := bstep (se 1 (by rfl) ⟨1157003, by rfl⟩ : syracuseStep 1542671 = 2314007) B2314007
theorem B1542713 : Blo 1024605 1542713 := bstep (se 2 (by rfl) ⟨578517, by rfl⟩ : syracuseStep 1542713 = 1157035) B1157035
theorem B1542791 : Blo 1024605 1542791 := bstep (se 1 (by rfl) ⟨1157093, by rfl⟩ : syracuseStep 1542791 = 2314187) B2314187
theorem B1542827 : Blo 1024605 1542827 := bstep (se 1 (by rfl) ⟨1157120, by rfl⟩ : syracuseStep 1542827 = 2314241) B2314241
theorem B1542857 : Blo 1024605 1542857 := bstep (se 2 (by rfl) ⟨578571, by rfl⟩ : syracuseStep 1542857 = 1157143) B1157143
theorem B2919179 : Blo 1024605 2919179 := bstep (se 1 (by rfl) ⟨2189384, by rfl⟩ : syracuseStep 2919179 = 4378769) B4378769
theorem B3705659 : Blo 1024605 3705659 := bstep (se 1 (by rfl) ⟨2779244, by rfl⟩ : syracuseStep 3705659 = 5558489) B5558489
theorem B2919577 : Blo 1024605 2919577 := bstep (se 2 (by rfl) ⟨1094841, by rfl⟩ : syracuseStep 2919577 = 2189683) B2189683
theorem B4885697 : Blo 1024605 4885697 := bstep (se 2 (by rfl) ⟨1832136, by rfl⟩ : syracuseStep 4885697 = 3664273) B3664273
theorem B3902701 : Blo 1024605 3902701 := bstep (se 3 (by rfl) ⟨731756, by rfl⟩ : syracuseStep 3902701 = 1463513) B1463513
theorem B26283365 : Blo 1024605 26283365 := bstep (se 4 (by rfl) ⟨2464065, by rfl⟩ : syracuseStep 26283365 = 4928131) B4928131
theorem B2919827 : Blo 1024605 2919827 := bstep (se 1 (by rfl) ⟨2189870, by rfl⟩ : syracuseStep 2919827 = 4379741) B4379741
theorem B3903005 : Blo 1024605 3903005 := bstep (se 3 (by rfl) ⟨731813, by rfl⟩ : syracuseStep 3903005 = 1463627) B1463627
theorem B379097009 : Blo 1024605 379097009 := bstep (se 2 (by rfl) ⟨142161378, by rfl⟩ : syracuseStep 379097009 = 284322757) B284322757
theorem B8753467 : Blo 1024605 8753467 := bstep (se 1 (by rfl) ⟨6565100, by rfl⟩ : syracuseStep 8753467 = 13130201) B13130201
theorem B2920819 : Blo 1024605 2920819 := bstep (se 1 (by rfl) ⟨2190614, by rfl⟩ : syracuseStep 2920819 = 4381229) B4381229
theorem B14062045 : Blo 1024605 14062045 := bstep (se 3 (by rfl) ⟨2636633, by rfl⟩ : syracuseStep 14062045 = 5273267) B5273267
theorem B8753741 : Blo 1024605 8753741 := bstep (se 3 (by rfl) ⟨1641326, by rfl⟩ : syracuseStep 8753741 = 3282653) B3282653
theorem B11113037 : Blo 1024605 11113037 := bstep (se 3 (by rfl) ⟨2083694, by rfl⟩ : syracuseStep 11113037 = 4167389) B4167389
theorem B35558081 : Blo 1024605 35558081 := bstep (se 2 (by rfl) ⟨13334280, by rfl⟩ : syracuseStep 35558081 = 26668561) B26668561
theorem B26645285 : Blo 1024605 26645285 := bstep (se 4 (by rfl) ⟨2497995, by rfl⟩ : syracuseStep 26645285 = 4995991) B4995991
theorem B2593579 : Blo 1024605 2593579 := bstep (se 1 (by rfl) ⟨1945184, by rfl⟩ : syracuseStep 2593579 = 3890369) B3890369
theorem B2593721 : Blo 1024605 2593721 := bstep (se 2 (by rfl) ⟨972645, by rfl⟩ : syracuseStep 2593721 = 1945291) B1945291
theorem B3904631 : Blo 1024605 3904631 := bstep (se 1 (by rfl) ⟨2928473, by rfl⟩ : syracuseStep 3904631 = 5856947) B5856947
theorem B6329573 : Blo 1024605 6329573 := bstep (se 4 (by rfl) ⟨593397, by rfl⟩ : syracuseStep 6329573 = 1186795) B1186795
theorem B4167065 : Blo 1024605 4167065 := bstep (se 2 (by rfl) ⟨1562649, by rfl⟩ : syracuseStep 4167065 = 3125299) B3125299
theorem B13342157 : Blo 1024605 13342157 := bstep (se 3 (by rfl) ⟨2501654, by rfl⟩ : syracuseStep 13342157 = 5003309) B5003309
theorem B7804673 : Blo 1024605 7804673 := bstep (se 2 (by rfl) ⟨2926752, by rfl⟩ : syracuseStep 7804673 = 5853505) B5853505
theorem B2594713 : Blo 1024605 2594713 := bstep (se 2 (by rfl) ⟨973017, by rfl⟩ : syracuseStep 2594713 = 1946035) B1946035
theorem B2922425 : Blo 1024605 2922425 := bstep (se 2 (by rfl) ⟨1095909, by rfl⟩ : syracuseStep 2922425 = 2191819) B2191819
theorem B1153039 : Blo 1024605 1153039 := bstep (se 1 (by rfl) ⟨864779, by rfl⟩ : syracuseStep 1153039 = 1729559) B1729559
theorem B2594875 : Blo 1024605 2594875 := bstep (se 1 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 2594875 = 3892313) B3892313
theorem B3119219 : Blo 1024605 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B162437237 : Blo 1024605 162437237 := bstep (se 5 (by rfl) ⟨7614245, by rfl⟩ : syracuseStep 162437237 = 15228491) B15228491
theorem B2595017 : Blo 1024605 2595017 := bstep (se 2 (by rfl) ⟨973131, by rfl⟩ : syracuseStep 2595017 = 1946263) B1946263
theorem B15669449 : Blo 1024605 15669449 := bstep (se 2 (by rfl) ⟨5876043, by rfl⟩ : syracuseStep 15669449 = 11752087) B11752087
theorem B2922767 : Blo 1024605 2922767 := bstep (se 1 (by rfl) ⟨2192075, by rfl⟩ : syracuseStep 2922767 = 4384151) B4384151
theorem B1153543 : Blo 1024605 1153543 := bstep (se 1 (by rfl) ⟨865157, by rfl⟩ : syracuseStep 1153543 = 1730315) B1730315
theorem B2595361 : Blo 1024605 2595361 := bstep (se 2 (by rfl) ⟨973260, by rfl⟩ : syracuseStep 2595361 = 1946521) B1946521
theorem B2464289 : Blo 1024605 2464289 := bstep (se 2 (by rfl) ⟨924108, by rfl⟩ : syracuseStep 2464289 = 1848217) B1848217
theorem B1251883 : Blo 1024605 1251883 := bstep (se 1 (by rfl) ⟨938912, by rfl⟩ : syracuseStep 1251883 = 1877825) B1877825
theorem B14785091 : Blo 1024605 14785091 := bstep (se 1 (by rfl) ⟨11088818, by rfl⟩ : syracuseStep 14785091 = 22177637) B22177637
theorem B11082419 : Blo 1024605 11082419 := bstep (se 1 (by rfl) ⟨8311814, by rfl⟩ : syracuseStep 11082419 = 16623629) B16623629
theorem B1153723 : Blo 1024605 1153723 := bstep (se 1 (by rfl) ⟨865292, by rfl⟩ : syracuseStep 1153723 = 1730585) B1730585
theorem B5839883 : Blo 1024605 5839883 := bstep (se 1 (by rfl) ⟨4379912, by rfl⟩ : syracuseStep 5839883 = 8759825) B8759825
theorem B2923553 : Blo 1024605 2923553 := bstep (se 2 (by rfl) ⟨1096332, by rfl⟩ : syracuseStep 2923553 = 2192665) B2192665
theorem B1317931 : Blo 1024605 1317931 := bstep (se 1 (by rfl) ⟨988448, by rfl⟩ : syracuseStep 1317931 = 1976897) B1976897
theorem B2595959 : Blo 1024605 2595959 := bstep (se 1 (by rfl) ⟨1946969, by rfl⟩ : syracuseStep 2595959 = 3893939) B3893939
theorem B1154191 : Blo 1024605 1154191 := bstep (se 1 (by rfl) ⟨865643, by rfl⟩ : syracuseStep 1154191 = 1731287) B1731287
theorem B1154695 : Blo 1024605 1154695 := bstep (se 1 (by rfl) ⟨866021, by rfl⟩ : syracuseStep 1154695 = 1732043) B1732043
theorem B1482553 : Blo 1024605 1482553 := bstep (se 2 (by rfl) ⟨555957, by rfl⟩ : syracuseStep 1482553 = 1111915) B1111915
theorem B1154875 : Blo 1024605 1154875 := bstep (se 1 (by rfl) ⟨866156, by rfl⟩ : syracuseStep 1154875 = 1732313) B1732313
theorem B2629523 : Blo 1024605 2629523 := bstep (se 1 (by rfl) ⟨1972142, by rfl⟩ : syracuseStep 2629523 = 3944285) B3944285
theorem B8331275 : Blo 1024605 8331275 := bstep (se 1 (by rfl) ⟨6248456, by rfl⟩ : syracuseStep 8331275 = 12496913) B12496913
theorem B22487053 : Blo 1024605 22487053 := bstep (se 3 (by rfl) ⟨4216322, by rfl⟩ : syracuseStep 22487053 = 8432645) B8432645
theorem B2465911 : Blo 1024605 2465911 := bstep (se 1 (by rfl) ⟨1849433, by rfl⟩ : syracuseStep 2465911 = 3698867) B3698867
theorem B1155343 : Blo 1024605 1155343 := bstep (se 1 (by rfl) ⟨866507, by rfl⟩ : syracuseStep 1155343 = 1733015) B1733015
theorem B2597255 : Blo 1024605 2597255 := bstep (se 1 (by rfl) ⟨1947941, by rfl⟩ : syracuseStep 2597255 = 3895883) B3895883
theorem B2597305 : Blo 1024605 2597305 := bstep (se 2 (by rfl) ⟨973989, by rfl⟩ : syracuseStep 2597305 = 1947979) B1947979
theorem B2925067 : Blo 1024605 2925067 := bstep (se 1 (by rfl) ⟨2193800, by rfl⟩ : syracuseStep 2925067 = 4387601) B4387601
theorem B1647119 : Blo 1024605 1647119 := bstep (se 1 (by rfl) ⟨1235339, by rfl⟩ : syracuseStep 1647119 = 2470679) B2470679
theorem B1024647 : Blo 1024605 1024647 := bstep (se 1 (by rfl) ⟨768485, by rfl⟩ : syracuseStep 1024647 = 1536971) B1536971
theorem B1024655 : Blo 1024605 1024655 := bstep (se 1 (by rfl) ⟨768491, by rfl⟩ : syracuseStep 1024655 = 1536983) B1536983
theorem B1024699 : Blo 1024605 1024699 := bstep (se 1 (by rfl) ⟨768524, by rfl⟩ : syracuseStep 1024699 = 1537049) B1537049
theorem B1024775 : Blo 1024605 1024775 := bstep (se 1 (by rfl) ⟨768581, by rfl⟩ : syracuseStep 1024775 = 1537163) B1537163
theorem B1155847 : Blo 1024605 1155847 := bstep (se 1 (by rfl) ⟨866885, by rfl⟩ : syracuseStep 1155847 = 1733771) B1733771
theorem B1024783 : Blo 1024605 1024783 := bstep (se 1 (by rfl) ⟨768587, by rfl⟩ : syracuseStep 1024783 = 1537175) B1537175
theorem B2925341 : Blo 1024605 2925341 := bstep (se 3 (by rfl) ⟨548501, by rfl⟩ : syracuseStep 2925341 = 1097003) B1097003
theorem B1024827 : Blo 1024605 1024827 := bstep (se 1 (by rfl) ⟨768620, by rfl⟩ : syracuseStep 1024827 = 1537241) B1537241
theorem B1024903 : Blo 1024605 1024903 := bstep (se 1 (by rfl) ⟨768677, by rfl⟩ : syracuseStep 1024903 = 1537355) B1537355
theorem B1024911 : Blo 1024605 1024911 := bstep (se 1 (by rfl) ⟨768683, by rfl⟩ : syracuseStep 1024911 = 1537367) B1537367
theorem B1024955 : Blo 1024605 1024955 := bstep (se 1 (by rfl) ⟨768716, by rfl⟩ : syracuseStep 1024955 = 1537433) B1537433
theorem B1156027 : Blo 1024605 1156027 := bstep (se 1 (by rfl) ⟨867020, by rfl⟩ : syracuseStep 1156027 = 1734041) B1734041
theorem B1025031 : Blo 1024605 1025031 := bstep (se 1 (by rfl) ⟨768773, by rfl⟩ : syracuseStep 1025031 = 1537547) B1537547
theorem B1025039 : Blo 1024605 1025039 := bstep (se 1 (by rfl) ⟨768779, by rfl⟩ : syracuseStep 1025039 = 1537559) B1537559
theorem B2597903 : Blo 1024605 2597903 := bstep (se 1 (by rfl) ⟨1948427, by rfl⟩ : syracuseStep 2597903 = 3896855) B3896855
theorem B1025083 : Blo 1024605 1025083 := bstep (se 1 (by rfl) ⟨768812, by rfl⟩ : syracuseStep 1025083 = 1537625) B1537625
theorem B2466931 : Blo 1024605 2466931 := bstep (se 1 (by rfl) ⟨1850198, by rfl⟩ : syracuseStep 2466931 = 3700397) B3700397
theorem B2925683 : Blo 1024605 2925683 := bstep (se 1 (by rfl) ⟨2194262, by rfl⟩ : syracuseStep 2925683 = 4388525) B4388525
theorem B1025159 : Blo 1024605 1025159 := bstep (se 1 (by rfl) ⟨768869, by rfl⟩ : syracuseStep 1025159 = 1537739) B1537739
theorem B1025167 : Blo 1024605 1025167 := bstep (se 1 (by rfl) ⟨768875, by rfl⟩ : syracuseStep 1025167 = 1537751) B1537751
theorem B1025211 : Blo 1024605 1025211 := bstep (se 1 (by rfl) ⟨768908, by rfl⟩ : syracuseStep 1025211 = 1537817) B1537817
theorem B1025287 : Blo 1024605 1025287 := bstep (se 1 (by rfl) ⟨768965, by rfl⟩ : syracuseStep 1025287 = 1537931) B1537931
theorem B1025295 : Blo 1024605 1025295 := bstep (se 1 (by rfl) ⟨768971, by rfl⟩ : syracuseStep 1025295 = 1537943) B1537943
theorem B25339169 : Blo 1024605 25339169 := bstep (se 2 (by rfl) ⟨9502188, by rfl⟩ : syracuseStep 25339169 = 19004377) B19004377
theorem B1025339 : Blo 1024605 1025339 := bstep (se 1 (by rfl) ⟨769004, by rfl⟩ : syracuseStep 1025339 = 1538009) B1538009
theorem B1025415 : Blo 1024605 1025415 := bstep (se 1 (by rfl) ⟨769061, by rfl⟩ : syracuseStep 1025415 = 1538123) B1538123
theorem B1025423 : Blo 1024605 1025423 := bstep (se 1 (by rfl) ⟨769067, by rfl⟩ : syracuseStep 1025423 = 1538135) B1538135
theorem B1156495 : Blo 1024605 1156495 := bstep (se 1 (by rfl) ⟨867371, by rfl⟩ : syracuseStep 1156495 = 1734743) B1734743
theorem B2467219 : Blo 1024605 2467219 := bstep (se 1 (by rfl) ⟨1850414, by rfl⟩ : syracuseStep 2467219 = 3700829) B3700829
theorem B1025467 : Blo 1024605 1025467 := bstep (se 1 (by rfl) ⟨769100, by rfl⟩ : syracuseStep 1025467 = 1538201) B1538201
theorem B5547523 : Blo 1024605 5547523 := bstep (se 1 (by rfl) ⟨4160642, by rfl⟩ : syracuseStep 5547523 = 8321285) B8321285
theorem B1025543 : Blo 1024605 1025543 := bstep (se 1 (by rfl) ⟨769157, by rfl⟩ : syracuseStep 1025543 = 1538315) B1538315
theorem B1025551 : Blo 1024605 1025551 := bstep (se 1 (by rfl) ⟨769163, by rfl⟩ : syracuseStep 1025551 = 1538327) B1538327
theorem B1025595 : Blo 1024605 1025595 := bstep (se 1 (by rfl) ⟨769196, by rfl⟩ : syracuseStep 1025595 = 1538393) B1538393
theorem B1025671 : Blo 1024605 1025671 := bstep (se 1 (by rfl) ⟨769253, by rfl⟩ : syracuseStep 1025671 = 1538507) B1538507
theorem B1025679 : Blo 1024605 1025679 := bstep (se 1 (by rfl) ⟨769259, by rfl⟩ : syracuseStep 1025679 = 1538519) B1538519
theorem B1025723 : Blo 1024605 1025723 := bstep (se 1 (by rfl) ⟨769292, by rfl⟩ : syracuseStep 1025723 = 1538585) B1538585
theorem B2598601 : Blo 1024605 2598601 := bstep (se 2 (by rfl) ⟨974475, by rfl⟩ : syracuseStep 2598601 = 1948951) B1948951
theorem B1025799 : Blo 1024605 1025799 := bstep (se 1 (by rfl) ⟨769349, by rfl⟩ : syracuseStep 1025799 = 1538699) B1538699
theorem B1025807 : Blo 1024605 1025807 := bstep (se 1 (by rfl) ⟨769355, by rfl⟩ : syracuseStep 1025807 = 1538711) B1538711
theorem B5547827 : Blo 1024605 5547827 := bstep (se 1 (by rfl) ⟨4160870, by rfl⟩ : syracuseStep 5547827 = 8321741) B8321741
theorem B1025851 : Blo 1024605 1025851 := bstep (se 1 (by rfl) ⟨769388, by rfl⟩ : syracuseStep 1025851 = 1538777) B1538777
theorem B2598743 : Blo 1024605 2598743 := bstep (se 1 (by rfl) ⟨1949057, by rfl⟩ : syracuseStep 2598743 = 3898115) B3898115
theorem B1025927 : Blo 1024605 1025927 := bstep (se 1 (by rfl) ⟨769445, by rfl⟩ : syracuseStep 1025927 = 1538891) B1538891
theorem B1156999 : Blo 1024605 1156999 := bstep (se 1 (by rfl) ⟨867749, by rfl⟩ : syracuseStep 1156999 = 1735499) B1735499
theorem B1386383 : Blo 1024605 1386383 := bstep (se 1 (by rfl) ⟨1039787, by rfl⟩ : syracuseStep 1386383 = 2079575) B2079575
theorem B1025935 : Blo 1024605 1025935 := bstep (se 1 (by rfl) ⟨769451, by rfl⟩ : syracuseStep 1025935 = 1538903) B1538903
theorem B1025979 : Blo 1024605 1025979 := bstep (se 1 (by rfl) ⟨769484, by rfl⟩ : syracuseStep 1025979 = 1538969) B1538969
theorem B1026055 : Blo 1024605 1026055 := bstep (se 1 (by rfl) ⟨769541, by rfl⟩ : syracuseStep 1026055 = 1539083) B1539083
theorem B11085835 : Blo 1024605 11085835 := bstep (se 1 (by rfl) ⟨8314376, by rfl⟩ : syracuseStep 11085835 = 16628753) B16628753
theorem B3287051 : Blo 1024605 3287051 := bstep (se 1 (by rfl) ⟨2465288, by rfl⟩ : syracuseStep 3287051 = 4930577) B4930577
theorem B1026063 : Blo 1024605 1026063 := bstep (se 1 (by rfl) ⟨769547, by rfl⟩ : syracuseStep 1026063 = 1539095) B1539095
theorem B7809047 : Blo 1024605 7809047 := bstep (se 1 (by rfl) ⟨5856785, by rfl⟩ : syracuseStep 7809047 = 11713571) B11713571
theorem B1026107 : Blo 1024605 1026107 := bstep (se 1 (by rfl) ⟨769580, by rfl⟩ : syracuseStep 1026107 = 1539161) B1539161
theorem B2926651 : Blo 1024605 2926651 := bstep (se 1 (by rfl) ⟨2194988, by rfl⟩ : syracuseStep 2926651 = 4389977) B4389977
theorem B1157179 : Blo 1024605 1157179 := bstep (se 1 (by rfl) ⟨867884, by rfl⟩ : syracuseStep 1157179 = 1735769) B1735769
theorem B1026183 : Blo 1024605 1026183 := bstep (se 1 (by rfl) ⟨769637, by rfl⟩ : syracuseStep 1026183 = 1539275) B1539275
theorem B1026191 : Blo 1024605 1026191 := bstep (se 1 (by rfl) ⟨769643, by rfl⟩ : syracuseStep 1026191 = 1539287) B1539287
theorem B3123353 : Blo 1024605 3123353 := bstep (se 2 (by rfl) ⟨1171257, by rfl⟩ : syracuseStep 3123353 = 2342515) B2342515
theorem B5843117 : Blo 1024605 5843117 := bstep (se 3 (by rfl) ⟨1095584, by rfl⟩ : syracuseStep 5843117 = 2191169) B2191169
theorem B1026235 : Blo 1024605 1026235 := bstep (se 1 (by rfl) ⟨769676, by rfl⟩ : syracuseStep 1026235 = 1539353) B1539353
theorem B1026311 : Blo 1024605 1026311 := bstep (se 1 (by rfl) ⟨769733, by rfl⟩ : syracuseStep 1026311 = 1539467) B1539467
theorem B1026319 : Blo 1024605 1026319 := bstep (se 1 (by rfl) ⟨769739, by rfl⟩ : syracuseStep 1026319 = 1539479) B1539479
theorem B1026363 : Blo 1024605 1026363 := bstep (se 1 (by rfl) ⟨769772, by rfl⟩ : syracuseStep 1026363 = 1539545) B1539545
theorem B1026439 : Blo 1024605 1026439 := bstep (se 1 (by rfl) ⟨769829, by rfl⟩ : syracuseStep 1026439 = 1539659) B1539659
theorem B1026447 : Blo 1024605 1026447 := bstep (se 1 (by rfl) ⟨769835, by rfl⟩ : syracuseStep 1026447 = 1539671) B1539671
theorem B1026491 : Blo 1024605 1026491 := bstep (se 1 (by rfl) ⟨769868, by rfl⟩ : syracuseStep 1026491 = 1539737) B1539737
theorem B5188049 : Blo 1024605 5188049 := bstep (se 2 (by rfl) ⟨1945518, by rfl⟩ : syracuseStep 5188049 = 3891037) B3891037
theorem B1026567 : Blo 1024605 1026567 := bstep (se 1 (by rfl) ⟨769925, by rfl⟩ : syracuseStep 1026567 = 1539851) B1539851
theorem B1026575 : Blo 1024605 1026575 := bstep (se 1 (by rfl) ⟨769931, by rfl⟩ : syracuseStep 1026575 = 1539863) B1539863
theorem B1026619 : Blo 1024605 1026619 := bstep (se 1 (by rfl) ⟨769964, by rfl⟩ : syracuseStep 1026619 = 1539929) B1539929
theorem B1026695 : Blo 1024605 1026695 := bstep (se 1 (by rfl) ⟨770021, by rfl⟩ : syracuseStep 1026695 = 1540043) B1540043
theorem B1026703 : Blo 1024605 1026703 := bstep (se 1 (by rfl) ⟨770027, by rfl⟩ : syracuseStep 1026703 = 1540055) B1540055
theorem B1026747 : Blo 1024605 1026747 := bstep (se 1 (by rfl) ⟨770060, by rfl⟩ : syracuseStep 1026747 = 1540121) B1540121
theorem B19999493 : Blo 1024605 19999493 := bstep (se 4 (by rfl) ⟨1874952, by rfl⟩ : syracuseStep 19999493 = 3749905) B3749905
theorem B1026823 : Blo 1024605 1026823 := bstep (se 1 (by rfl) ⟨770117, by rfl⟩ : syracuseStep 1026823 = 1540235) B1540235
theorem B1026831 : Blo 1024605 1026831 := bstep (se 1 (by rfl) ⟨770123, by rfl⟩ : syracuseStep 1026831 = 1540247) B1540247
theorem B10529585 : Blo 1024605 10529585 := bstep (se 2 (by rfl) ⟨3948594, by rfl⟩ : syracuseStep 10529585 = 7897189) B7897189
theorem B1026875 : Blo 1024605 1026875 := bstep (se 1 (by rfl) ⟨770156, by rfl⟩ : syracuseStep 1026875 = 1540313) B1540313
theorem B1026951 : Blo 1024605 1026951 := bstep (se 1 (by rfl) ⟨770213, by rfl⟩ : syracuseStep 1026951 = 1540427) B1540427
theorem B1026959 : Blo 1024605 1026959 := bstep (se 1 (by rfl) ⟨770219, by rfl⟩ : syracuseStep 1026959 = 1540439) B1540439
theorem B1027003 : Blo 1024605 1027003 := bstep (se 1 (by rfl) ⟨770252, by rfl⟩ : syracuseStep 1027003 = 1540505) B1540505
theorem B1027079 : Blo 1024605 1027079 := bstep (se 1 (by rfl) ⟨770309, by rfl⟩ : syracuseStep 1027079 = 1540619) B1540619
theorem B1027087 : Blo 1024605 1027087 := bstep (se 1 (by rfl) ⟨770315, by rfl⟩ : syracuseStep 1027087 = 1540631) B1540631
theorem B1027131 : Blo 1024605 1027131 := bstep (se 1 (by rfl) ⟨770348, by rfl⟩ : syracuseStep 1027131 = 1540697) B1540697
theorem B1027207 : Blo 1024605 1027207 := bstep (se 1 (by rfl) ⟨770405, by rfl⟩ : syracuseStep 1027207 = 1540811) B1540811
theorem B1027215 : Blo 1024605 1027215 := bstep (se 1 (by rfl) ⟨770411, by rfl⟩ : syracuseStep 1027215 = 1540823) B1540823
theorem B2927801 : Blo 1024605 2927801 := bstep (se 2 (by rfl) ⟨1097925, by rfl⟩ : syracuseStep 2927801 = 2195851) B2195851
theorem B1027259 : Blo 1024605 1027259 := bstep (se 1 (by rfl) ⟨770444, by rfl⟩ : syracuseStep 1027259 = 1540889) B1540889
theorem B36547789 : Blo 1024605 36547789 := bstep (se 3 (by rfl) ⟨6852710, by rfl⟩ : syracuseStep 36547789 = 13705421) B13705421
theorem B1027335 : Blo 1024605 1027335 := bstep (se 1 (by rfl) ⟨770501, by rfl⟩ : syracuseStep 1027335 = 1541003) B1541003
theorem B1027343 : Blo 1024605 1027343 := bstep (se 1 (by rfl) ⟨770507, by rfl⟩ : syracuseStep 1027343 = 1541015) B1541015
theorem B5844257 : Blo 1024605 5844257 := bstep (se 2 (by rfl) ⟨2191596, by rfl⟩ : syracuseStep 5844257 = 4383193) B4383193
theorem B1027387 : Blo 1024605 1027387 := bstep (se 1 (by rfl) ⟨770540, by rfl⟩ : syracuseStep 1027387 = 1541081) B1541081
theorem B1027463 : Blo 1024605 1027463 := bstep (se 1 (by rfl) ⟨770597, by rfl⟩ : syracuseStep 1027463 = 1541195) B1541195
theorem B1027471 : Blo 1024605 1027471 := bstep (se 1 (by rfl) ⟨770603, by rfl⟩ : syracuseStep 1027471 = 1541207) B1541207
theorem B1027515 : Blo 1024605 1027515 := bstep (se 1 (by rfl) ⟨770636, by rfl⟩ : syracuseStep 1027515 = 1541273) B1541273
theorem B1027591 : Blo 1024605 1027591 := bstep (se 1 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 1027591 = 1541387) B1541387
theorem B1027599 : Blo 1024605 1027599 := bstep (se 1 (by rfl) ⟨770699, by rfl⟩ : syracuseStep 1027599 = 1541399) B1541399
theorem B2928143 : Blo 1024605 2928143 := bstep (se 1 (by rfl) ⟨2196107, by rfl⟩ : syracuseStep 2928143 = 4392215) B4392215
theorem B1027643 : Blo 1024605 1027643 := bstep (se 1 (by rfl) ⟨770732, by rfl⟩ : syracuseStep 1027643 = 1541465) B1541465
theorem B2305655 : Blo 1024605 2305655 := bstep (se 1 (by rfl) ⟨1729241, by rfl⟩ : syracuseStep 2305655 = 3458483) B3458483
theorem B1027719 : Blo 1024605 1027719 := bstep (se 1 (by rfl) ⟨770789, by rfl⟩ : syracuseStep 1027719 = 1541579) B1541579
theorem B1027727 : Blo 1024605 1027727 := bstep (se 1 (by rfl) ⟨770795, by rfl⟩ : syracuseStep 1027727 = 1541591) B1541591
theorem B1027771 : Blo 1024605 1027771 := bstep (se 1 (by rfl) ⟨770828, by rfl⟩ : syracuseStep 1027771 = 1541657) B1541657
theorem B1027847 : Blo 1024605 1027847 := bstep (se 1 (by rfl) ⟨770885, by rfl⟩ : syracuseStep 1027847 = 1541771) B1541771
theorem B1027855 : Blo 1024605 1027855 := bstep (se 1 (by rfl) ⟨770891, by rfl⟩ : syracuseStep 1027855 = 1541783) B1541783
theorem B2305835 : Blo 1024605 2305835 := bstep (se 1 (by rfl) ⟨1729376, by rfl⟩ : syracuseStep 2305835 = 3458753) B3458753
theorem B3944251 : Blo 1024605 3944251 := bstep (se 1 (by rfl) ⟨2958188, by rfl⟩ : syracuseStep 3944251 = 5916377) B5916377
theorem B1847099 : Blo 1024605 1847099 := bstep (se 1 (by rfl) ⟨1385324, by rfl⟩ : syracuseStep 1847099 = 2770649) B2770649
theorem B1027899 : Blo 1024605 1027899 := bstep (se 1 (by rfl) ⟨770924, by rfl⟩ : syracuseStep 1027899 = 1541849) B1541849
theorem B2600819 : Blo 1024605 2600819 := bstep (se 1 (by rfl) ⟨1950614, by rfl⟩ : syracuseStep 2600819 = 3901229) B3901229
theorem B1027975 : Blo 1024605 1027975 := bstep (se 1 (by rfl) ⟨770981, by rfl⟩ : syracuseStep 1027975 = 1541963) B1541963
theorem B1027983 : Blo 1024605 1027983 := bstep (se 1 (by rfl) ⟨770987, by rfl⟩ : syracuseStep 1027983 = 1541975) B1541975
theorem B1388459 : Blo 1024605 1388459 := bstep (se 1 (by rfl) ⟨1041344, by rfl⟩ : syracuseStep 1388459 = 2082689) B2082689
theorem B1028027 : Blo 1024605 1028027 := bstep (se 1 (by rfl) ⟨771020, by rfl⟩ : syracuseStep 1028027 = 1542041) B1542041
theorem B1028103 : Blo 1024605 1028103 := bstep (se 1 (by rfl) ⟨771077, by rfl⟩ : syracuseStep 1028103 = 1542155) B1542155
theorem B1028111 : Blo 1024605 1028111 := bstep (se 1 (by rfl) ⟨771083, by rfl⟩ : syracuseStep 1028111 = 1542167) B1542167
theorem B4927517 : Blo 1024605 4927517 := bstep (se 3 (by rfl) ⟨923909, by rfl⟩ : syracuseStep 4927517 = 1847819) B1847819
theorem B1945633 : Blo 1024605 1945633 := bstep (se 2 (by rfl) ⟨729612, by rfl⟩ : syracuseStep 1945633 = 1459225) B1459225
theorem B1028155 : Blo 1024605 1028155 := bstep (se 1 (by rfl) ⟨771116, by rfl⟩ : syracuseStep 1028155 = 1542233) B1542233
theorem B2470007 : Blo 1024605 2470007 := bstep (se 1 (by rfl) ⟨1852505, by rfl⟩ : syracuseStep 2470007 = 3705011) B3705011
theorem B1028231 : Blo 1024605 1028231 := bstep (se 1 (by rfl) ⟨771173, by rfl⟩ : syracuseStep 1028231 = 1542347) B1542347
theorem B1028239 : Blo 1024605 1028239 := bstep (se 1 (by rfl) ⟨771179, by rfl⟩ : syracuseStep 1028239 = 1542359) B1542359
theorem B2306195 : Blo 1024605 2306195 := bstep (se 1 (by rfl) ⟨1729646, by rfl⟩ : syracuseStep 2306195 = 3459293) B3459293
theorem B1028283 : Blo 1024605 1028283 := bstep (se 1 (by rfl) ⟨771212, by rfl⟩ : syracuseStep 1028283 = 1542425) B1542425
theorem B2306249 : Blo 1024605 2306249 := bstep (se 2 (by rfl) ⟨864843, by rfl⟩ : syracuseStep 2306249 = 1729687) B1729687
theorem B1028359 : Blo 1024605 1028359 := bstep (se 1 (by rfl) ⟨771269, by rfl⟩ : syracuseStep 1028359 = 1542539) B1542539
theorem B1028367 : Blo 1024605 1028367 := bstep (se 1 (by rfl) ⟨771275, by rfl⟩ : syracuseStep 1028367 = 1542551) B1542551
theorem B1028411 : Blo 1024605 1028411 := bstep (se 1 (by rfl) ⟨771308, by rfl⟩ : syracuseStep 1028411 = 1542617) B1542617
theorem B2601335 : Blo 1024605 2601335 := bstep (se 1 (by rfl) ⟨1951001, by rfl⟩ : syracuseStep 2601335 = 3902003) B3902003
theorem B1028487 : Blo 1024605 1028487 := bstep (se 1 (by rfl) ⟨771365, by rfl⟩ : syracuseStep 1028487 = 1542731) B1542731
theorem B2929031 : Blo 1024605 2929031 := bstep (se 1 (by rfl) ⟨2196773, by rfl⟩ : syracuseStep 2929031 = 4393547) B4393547
theorem B1028495 : Blo 1024605 1028495 := bstep (se 1 (by rfl) ⟨771371, by rfl⟩ : syracuseStep 1028495 = 1542743) B1542743
theorem B1028539 : Blo 1024605 1028539 := bstep (se 1 (by rfl) ⟨771404, by rfl⟩ : syracuseStep 1028539 = 1542809) B1542809
theorem B5190155 : Blo 1024605 5190155 := bstep (se 1 (by rfl) ⟨3892616, by rfl⟩ : syracuseStep 5190155 = 7785233) B7785233
theorem B12464705 : Blo 1024605 12464705 := bstep (se 2 (by rfl) ⟨4674264, by rfl⟩ : syracuseStep 12464705 = 9348529) B9348529
theorem B5190317 : Blo 1024605 5190317 := bstep (se 3 (by rfl) ⟨973184, by rfl⟩ : syracuseStep 5190317 = 1946369) B1946369
theorem B2077369 : Blo 1024605 2077369 := bstep (se 2 (by rfl) ⟨779013, by rfl⟩ : syracuseStep 2077369 = 1558027) B1558027
theorem B2077499 : Blo 1024605 2077499 := bstep (se 1 (by rfl) ⟨1558124, by rfl⟩ : syracuseStep 2077499 = 3116249) B3116249
theorem B11678579 : Blo 1024605 11678579 := bstep (se 1 (by rfl) ⟨8758934, by rfl⟩ : syracuseStep 11678579 = 17517869) B17517869
theorem B2306951 : Blo 1024605 2306951 := bstep (se 1 (by rfl) ⟨1730213, by rfl⟩ : syracuseStep 2306951 = 3460427) B3460427
theorem B5550983 : Blo 1024605 5550983 := bstep (se 1 (by rfl) ⟨4163237, by rfl⟩ : syracuseStep 5550983 = 8326475) B8326475
theorem B5551051 : Blo 1024605 5551051 := bstep (se 1 (by rfl) ⟨4163288, by rfl⟩ : syracuseStep 5551051 = 8326577) B8326577
theorem B1094671 : Blo 1024605 1094671 := bstep (se 1 (by rfl) ⟨821003, by rfl⟩ : syracuseStep 1094671 = 1642007) B1642007
theorem B2307131 : Blo 1024605 2307131 := bstep (se 1 (by rfl) ⟨1730348, by rfl⟩ : syracuseStep 2307131 = 3460697) B3460697
theorem B2307257 : Blo 1024605 2307257 := bstep (se 2 (by rfl) ⟨865221, by rfl⟩ : syracuseStep 2307257 = 1730443) B1730443
theorem B1946825 : Blo 1024605 1946825 := bstep (se 2 (by rfl) ⟨730059, by rfl⟩ : syracuseStep 1946825 = 1460119) B1460119
theorem B2602327 : Blo 1024605 2602327 := bstep (se 1 (by rfl) ⟨1951745, by rfl⟩ : syracuseStep 2602327 = 3903491) B3903491
theorem B2307599 : Blo 1024605 2307599 := bstep (se 1 (by rfl) ⟨1730699, by rfl⟩ : syracuseStep 2307599 = 3461399) B3461399
theorem B2307617 : Blo 1024605 2307617 := bstep (se 2 (by rfl) ⟨865356, by rfl⟩ : syracuseStep 2307617 = 1730713) B1730713
theorem B2602631 : Blo 1024605 2602631 := bstep (se 1 (by rfl) ⟨1951973, by rfl⟩ : syracuseStep 2602631 = 3903947) B3903947
theorem B3290881 : Blo 1024605 3290881 := bstep (se 2 (by rfl) ⟨1234080, by rfl⟩ : syracuseStep 3290881 = 2468161) B2468161
theorem B2602763 : Blo 1024605 2602763 := bstep (se 1 (by rfl) ⟨1952072, by rfl⟩ : syracuseStep 2602763 = 3904145) B3904145
theorem B8763173 : Blo 1024605 8763173 := bstep (se 4 (by rfl) ⟨821547, by rfl⟩ : syracuseStep 8763173 = 1643095) B1643095
theorem B3127099 : Blo 1024605 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B2307959 : Blo 1024605 2307959 := bstep (se 1 (by rfl) ⟨1730969, by rfl⟩ : syracuseStep 2307959 = 3461939) B3461939
theorem B1947539 : Blo 1024605 1947539 := bstep (se 1 (by rfl) ⟨1460654, by rfl⟩ : syracuseStep 1947539 = 2921309) B2921309
theorem B1947577 : Blo 1024605 1947577 := bstep (se 2 (by rfl) ⟨730341, by rfl⟩ : syracuseStep 1947577 = 1460683) B1460683
theorem B2308139 : Blo 1024605 2308139 := bstep (se 1 (by rfl) ⟨1731104, by rfl⟩ : syracuseStep 2308139 = 3462209) B3462209
theorem B5191937 : Blo 1024605 5191937 := bstep (se 2 (by rfl) ⟨1946976, by rfl⟩ : syracuseStep 5191937 = 3893953) B3893953
theorem B2603279 : Blo 1024605 2603279 := bstep (se 1 (by rfl) ⟨1952459, by rfl⟩ : syracuseStep 2603279 = 3904919) B3904919
theorem B2308499 : Blo 1024605 2308499 := bstep (se 1 (by rfl) ⟨1731374, by rfl⟩ : syracuseStep 2308499 = 3462749) B3462749
theorem B2603411 : Blo 1024605 2603411 := bstep (se 1 (by rfl) ⟨1952558, by rfl⟩ : syracuseStep 2603411 = 3905117) B3905117
theorem B4929977 : Blo 1024605 4929977 := bstep (se 2 (by rfl) ⟨1848741, by rfl⟩ : syracuseStep 4929977 = 3697483) B3697483
theorem B2308553 : Blo 1024605 2308553 := bstep (se 2 (by rfl) ⟨865707, by rfl⟩ : syracuseStep 2308553 = 1731415) B1731415
theorem B9484877 : Blo 1024605 9484877 := bstep (se 3 (by rfl) ⟨1778414, by rfl⟩ : syracuseStep 9484877 = 3556829) B3556829
theorem B22166135 : Blo 1024605 22166135 := bstep (se 1 (by rfl) ⟨16624601, by rfl⟩ : syracuseStep 22166135 = 33249203) B33249203
theorem B2636441 : Blo 1024605 2636441 := bstep (se 2 (by rfl) ⟨988665, by rfl⟩ : syracuseStep 2636441 = 1977331) B1977331
theorem B5192747 : Blo 1024605 5192747 := bstep (se 1 (by rfl) ⟨3894560, by rfl⟩ : syracuseStep 5192747 = 7789121) B7789121
theorem B2079803 : Blo 1024605 2079803 := bstep (se 1 (by rfl) ⟨1559852, by rfl⟩ : syracuseStep 2079803 = 3119705) B3119705
theorem B2309255 : Blo 1024605 2309255 := bstep (se 1 (by rfl) ⟨1731941, by rfl⟩ : syracuseStep 2309255 = 3463883) B3463883
theorem B2309435 : Blo 1024605 2309435 := bstep (se 1 (by rfl) ⟨1732076, by rfl⟩ : syracuseStep 2309435 = 3464153) B3464153
theorem B2309561 : Blo 1024605 2309561 := bstep (se 2 (by rfl) ⟨866085, by rfl⟩ : syracuseStep 2309561 = 1732171) B1732171
theorem B16661969 : Blo 1024605 16661969 := bstep (se 2 (by rfl) ⟨6248238, by rfl⟩ : syracuseStep 16661969 = 12496477) B12496477
theorem B2965021 : Blo 1024605 2965021 := bstep (se 3 (by rfl) ⟨555941, by rfl⟩ : syracuseStep 2965021 = 1111883) B1111883
theorem B2309903 : Blo 1024605 2309903 := bstep (se 1 (by rfl) ⟨1732427, by rfl⟩ : syracuseStep 2309903 = 3464855) B3464855
theorem B2309921 : Blo 1024605 2309921 := bstep (se 2 (by rfl) ⟨866220, by rfl⟩ : syracuseStep 2309921 = 1732441) B1732441
theorem B1949483 : Blo 1024605 1949483 := bstep (se 1 (by rfl) ⟨1462112, by rfl⟩ : syracuseStep 1949483 = 2924225) B2924225
theorem B6340619 : Blo 1024605 6340619 := bstep (se 1 (by rfl) ⟨4755464, by rfl⟩ : syracuseStep 6340619 = 9510929) B9510929
theorem B5849131 : Blo 1024605 5849131 := bstep (se 1 (by rfl) ⟨4386848, by rfl⟩ : syracuseStep 5849131 = 8773697) B8773697
theorem B2310263 : Blo 1024605 2310263 := bstep (se 1 (by rfl) ⟨1732697, by rfl⟩ : syracuseStep 2310263 = 3465395) B3465395
theorem B2310443 : Blo 1024605 2310443 := bstep (se 1 (by rfl) ⟨1732832, by rfl⟩ : syracuseStep 2310443 = 3465665) B3465665
theorem B5194043 : Blo 1024605 5194043 := bstep (se 1 (by rfl) ⟨3895532, by rfl⟩ : syracuseStep 5194043 = 7791065) B7791065
theorem B2998663 : Blo 1024605 2998663 := bstep (se 1 (by rfl) ⟨2248997, by rfl⟩ : syracuseStep 2998663 = 4497995) B4497995
theorem B7782803 : Blo 1024605 7782803 := bstep (se 1 (by rfl) ⟨5837102, by rfl⟩ : syracuseStep 7782803 = 11674205) B11674205
theorem B5194205 : Blo 1024605 5194205 := bstep (se 3 (by rfl) ⟨973913, by rfl⟩ : syracuseStep 5194205 = 1947827) B1947827
theorem B3293725 : Blo 1024605 3293725 := bstep (se 3 (by rfl) ⟨617573, by rfl⟩ : syracuseStep 3293725 = 1235147) B1235147
theorem B11256421 : Blo 1024605 11256421 := bstep (se 4 (by rfl) ⟨1055289, by rfl⟩ : syracuseStep 11256421 = 2110579) B2110579
theorem B2310803 : Blo 1024605 2310803 := bstep (se 1 (by rfl) ⟨1733102, by rfl⟩ : syracuseStep 2310803 = 3466205) B3466205
theorem B2310857 : Blo 1024605 2310857 := bstep (se 2 (by rfl) ⟨866571, by rfl⟩ : syracuseStep 2310857 = 1733143) B1733143
theorem B1950409 : Blo 1024605 1950409 := bstep (se 2 (by rfl) ⟨731403, by rfl⟩ : syracuseStep 1950409 = 1462807) B1462807
theorem B5194529 : Blo 1024605 5194529 := bstep (se 2 (by rfl) ⟨1947948, by rfl⟩ : syracuseStep 5194529 = 3895897) B3895897
theorem B2475019 : Blo 1024605 2475019 := bstep (se 1 (by rfl) ⟨1856264, by rfl⟩ : syracuseStep 2475019 = 3712529) B3712529
theorem B3949825 : Blo 1024605 3949825 := bstep (se 2 (by rfl) ⟨1481184, by rfl⟩ : syracuseStep 3949825 = 2962369) B2962369
theorem B2639147 : Blo 1024605 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B2311559 : Blo 1024605 2311559 := bstep (se 1 (by rfl) ⟨1733669, by rfl⟩ : syracuseStep 2311559 = 3467339) B3467339
theorem B1951123 : Blo 1024605 1951123 := bstep (se 1 (by rfl) ⟨1463342, by rfl⟩ : syracuseStep 1951123 = 2926685) B2926685
theorem B5850589 : Blo 1024605 5850589 := bstep (se 3 (by rfl) ⟨1096985, by rfl⟩ : syracuseStep 5850589 = 2193971) B2193971
theorem B2770433 : Blo 1024605 2770433 := bstep (se 2 (by rfl) ⟨1038912, by rfl⟩ : syracuseStep 2770433 = 2077825) B2077825
theorem B2311739 : Blo 1024605 2311739 := bstep (se 1 (by rfl) ⟨1733804, by rfl⟩ : syracuseStep 2311739 = 3467609) B3467609
theorem B2311865 : Blo 1024605 2311865 := bstep (se 2 (by rfl) ⟨866949, by rfl⟩ : syracuseStep 2311865 = 1733899) B1733899
theorem B5195501 : Blo 1024605 5195501 := bstep (se 3 (by rfl) ⟨974156, by rfl⟩ : syracuseStep 5195501 = 1948313) B1948313
theorem B39405365 : Blo 1024605 39405365 := bstep (se 5 (by rfl) ⟨1847126, by rfl⟩ : syracuseStep 39405365 = 3694253) B3694253
theorem B9848729 : Blo 1024605 9848729 := bstep (se 2 (by rfl) ⟨3693273, by rfl⟩ : syracuseStep 9848729 = 7386547) B7386547
theorem B3458969 : Blo 1024605 3458969 := bstep (se 2 (by rfl) ⟨1297113, by rfl⟩ : syracuseStep 3458969 = 2594227) B2594227
theorem B1460153 : Blo 1024605 1460153 := bstep (se 2 (by rfl) ⟨547557, by rfl⟩ : syracuseStep 1460153 = 1095115) B1095115
theorem B2312207 : Blo 1024605 2312207 := bstep (se 1 (by rfl) ⟨1734155, by rfl⟩ : syracuseStep 2312207 = 3468311) B3468311
theorem B2770973 : Blo 1024605 2770973 := bstep (se 3 (by rfl) ⟨519557, by rfl⟩ : syracuseStep 2770973 = 1039115) B1039115
theorem B2312225 : Blo 1024605 2312225 := bstep (se 2 (by rfl) ⟨867084, by rfl⟩ : syracuseStep 2312225 = 1734169) B1734169
theorem B2312567 : Blo 1024605 2312567 := bstep (se 1 (by rfl) ⟨1734425, by rfl⟩ : syracuseStep 2312567 = 3468851) B3468851
theorem B1952201 : Blo 1024605 1952201 := bstep (se 2 (by rfl) ⟨732075, by rfl⟩ : syracuseStep 1952201 = 1464151) B1464151
theorem B1296911 : Blo 1024605 1296911 := bstep (se 1 (by rfl) ⟨972683, by rfl⟩ : syracuseStep 1296911 = 1945367) B1945367
theorem B5196311 : Blo 1024605 5196311 := bstep (se 1 (by rfl) ⟨3897233, by rfl⟩ : syracuseStep 5196311 = 7794467) B7794467
theorem B2312747 : Blo 1024605 2312747 := bstep (se 1 (by rfl) ⟨1734560, by rfl⟩ : syracuseStep 2312747 = 3469121) B3469121
theorem B3459671 : Blo 1024605 3459671 := bstep (se 1 (by rfl) ⟨2594753, by rfl⟩ : syracuseStep 3459671 = 5189507) B5189507
theorem B4442861 : Blo 1024605 4442861 := bstep (se 3 (by rfl) ⟨833036, by rfl⟩ : syracuseStep 4442861 = 1666073) B1666073
theorem B1461007 : Blo 1024605 1461007 := bstep (se 1 (by rfl) ⟨1095755, by rfl⟩ : syracuseStep 1461007 = 2191511) B2191511
theorem B11094833 : Blo 1024605 11094833 := bstep (se 2 (by rfl) ⟨4160562, by rfl⟩ : syracuseStep 11094833 = 8321125) B8321125
theorem B2313107 : Blo 1024605 2313107 := bstep (se 1 (by rfl) ⟨1734830, by rfl⟩ : syracuseStep 2313107 = 3469661) B3469661
theorem B2313161 : Blo 1024605 2313161 := bstep (se 2 (by rfl) ⟨867435, by rfl⟩ : syracuseStep 2313161 = 1734871) B1734871
theorem B3460157 : Blo 1024605 3460157 := bstep (se 3 (by rfl) ⟨648779, by rfl⟩ : syracuseStep 3460157 = 1297559) B1297559
theorem B8768573 : Blo 1024605 8768573 := bstep (se 3 (by rfl) ⟨1644107, by rfl⟩ : syracuseStep 8768573 = 3288215) B3288215
theorem B1461577 : Blo 1024605 1461577 := bstep (se 2 (by rfl) ⟨548091, by rfl⟩ : syracuseStep 1461577 = 1096183) B1096183
theorem B2313863 : Blo 1024605 2313863 := bstep (se 1 (by rfl) ⟨1735397, by rfl⟩ : syracuseStep 2313863 = 3470795) B3470795
theorem B1560265 : Blo 1024605 1560265 := bstep (se 2 (by rfl) ⟨585099, by rfl⟩ : syracuseStep 1560265 = 1170199) B1170199
theorem B7032577 : Blo 1024605 7032577 := bstep (se 2 (by rfl) ⟨2637216, by rfl⟩ : syracuseStep 7032577 = 5274433) B5274433
theorem B2314043 : Blo 1024605 2314043 := bstep (se 1 (by rfl) ⟨1735532, by rfl⟩ : syracuseStep 2314043 = 3471065) B3471065
theorem B11849561 : Blo 1024605 11849561 := bstep (se 2 (by rfl) ⟨4443585, by rfl⟩ : syracuseStep 11849561 = 8887171) B8887171
theorem B2314169 : Blo 1024605 2314169 := bstep (se 2 (by rfl) ⟨867813, by rfl⟩ : syracuseStep 2314169 = 1735627) B1735627
theorem B3461561 : Blo 1024605 3461561 := bstep (se 2 (by rfl) ⟨1298085, by rfl⟩ : syracuseStep 3461561 = 2596171) B2596171
theorem B4444625 : Blo 1024605 4444625 := bstep (se 2 (by rfl) ⟨1666734, by rfl⟩ : syracuseStep 4444625 = 3333469) B3333469
theorem B159896081 : Blo 1024605 159896081 := bstep (se 2 (by rfl) ⟨59961030, by rfl⟩ : syracuseStep 159896081 = 119922061) B119922061
theorem B1233451 : Blo 1024605 1233451 := bstep (se 1 (by rfl) ⟨925088, by rfl⟩ : syracuseStep 1233451 = 1850177) B1850177
theorem B3462155 : Blo 1024605 3462155 := bstep (se 1 (by rfl) ⟨2596616, by rfl⟩ : syracuseStep 3462155 = 5193233) B5193233
theorem B4936727 : Blo 1024605 4936727 := bstep (se 1 (by rfl) ⟨3702545, by rfl⟩ : syracuseStep 4936727 = 7405091) B7405091
theorem B3462263 : Blo 1024605 3462263 := bstep (se 1 (by rfl) ⟨2596697, by rfl⟩ : syracuseStep 3462263 = 5193395) B5193395
theorem B1561871 : Blo 1024605 1561871 := bstep (se 1 (by rfl) ⟨1171403, by rfl⟩ : syracuseStep 1561871 = 2342807) B2342807
theorem B8770963 : Blo 1024605 8770963 := bstep (se 1 (by rfl) ⟨6578222, by rfl⟩ : syracuseStep 8770963 = 13156445) B13156445
theorem B1299883 : Blo 1024605 1299883 := bstep (se 1 (by rfl) ⟨974912, by rfl⟩ : syracuseStep 1299883 = 1949825) B1949825
theorem B50615837 : Blo 1024605 50615837 := bstep (se 3 (by rfl) ⟨9490469, by rfl⟩ : syracuseStep 50615837 = 18980939) B18980939
theorem B5199389 : Blo 1024605 5199389 := bstep (se 3 (by rfl) ⟨974885, by rfl⟩ : syracuseStep 5199389 = 1949771) B1949771
theorem B5854781 : Blo 1024605 5854781 := bstep (se 3 (by rfl) ⟨1097771, by rfl⟩ : syracuseStep 5854781 = 2195543) B2195543
theorem B11392579 : Blo 1024605 11392579 := bstep (se 1 (by rfl) ⟨8544434, by rfl⟩ : syracuseStep 11392579 = 17088869) B17088869
theorem B3462857 : Blo 1024605 3462857 := bstep (se 2 (by rfl) ⟨1298571, by rfl⟩ : syracuseStep 3462857 = 2597143) B2597143
theorem B1169159 : Blo 1024605 1169159 := bstep (se 1 (by rfl) ⟨876869, by rfl⟩ : syracuseStep 1169159 = 1753739) B1753739
theorem B2709335 : Blo 1024605 2709335 := bstep (se 1 (by rfl) ⟨2032001, by rfl⟩ : syracuseStep 2709335 = 4064003) B4064003
theorem B1464265 : Blo 1024605 1464265 := bstep (se 2 (by rfl) ⟨549099, by rfl⟩ : syracuseStep 1464265 = 1098199) B1098199
theorem B5199875 : Blo 1024605 5199875 := bstep (se 1 (by rfl) ⟨3899906, by rfl⟩ : syracuseStep 5199875 = 7799813) B7799813
theorem B5855489 : Blo 1024605 5855489 := bstep (se 2 (by rfl) ⟨2195808, by rfl⟩ : syracuseStep 5855489 = 4391617) B4391617
theorem B1300855 : Blo 1024605 1300855 := bstep (se 1 (by rfl) ⟨975641, by rfl⟩ : syracuseStep 1300855 = 1951283) B1951283
theorem B3463559 : Blo 1024605 3463559 := bstep (se 1 (by rfl) ⟨2597669, by rfl⟩ : syracuseStep 3463559 = 5195339) B5195339
theorem B4938205 : Blo 1024605 4938205 := bstep (se 3 (by rfl) ⟨925913, by rfl⟩ : syracuseStep 4938205 = 1851827) B1851827
theorem B4676125 : Blo 1024605 4676125 := bstep (se 3 (by rfl) ⟨876773, by rfl⟩ : syracuseStep 4676125 = 1753547) B1753547
theorem B2775611 : Blo 1024605 2775611 := bstep (se 1 (by rfl) ⟨2081708, by rfl⟩ : syracuseStep 2775611 = 4163417) B4163417
theorem B1301179 : Blo 1024605 1301179 := bstep (se 1 (by rfl) ⟨975884, by rfl⟩ : syracuseStep 1301179 = 1951769) B1951769
theorem B3463937 : Blo 1024605 3463937 := bstep (se 2 (by rfl) ⟨1298976, by rfl⟩ : syracuseStep 3463937 = 2597953) B2597953
theorem B1170875 : Blo 1024605 1170875 := bstep (se 1 (by rfl) ⟨878156, by rfl⟩ : syracuseStep 1170875 = 1756313) B1756313
theorem B13360589 : Blo 1024605 13360589 := bstep (se 3 (by rfl) ⟨2505110, by rfl⟩ : syracuseStep 13360589 = 5010221) B5010221
theorem B3464747 : Blo 1024605 3464747 := bstep (se 1 (by rfl) ⟨2598560, by rfl⟩ : syracuseStep 3464747 = 5197121) B5197121
theorem B5201495 : Blo 1024605 5201495 := bstep (se 1 (by rfl) ⟨3901121, by rfl⟩ : syracuseStep 5201495 = 7802243) B7802243
theorem B28139309 : Blo 1024605 28139309 := bstep (se 3 (by rfl) ⟨5276120, by rfl⟩ : syracuseStep 28139309 = 10552241) B10552241
theorem B5201981 : Blo 1024605 5201981 := bstep (se 3 (by rfl) ⟨975371, by rfl⟩ : syracuseStep 5201981 = 1950743) B1950743
theorem B1729039 : Blo 1024605 1729039 := bstep (se 1 (by rfl) ⟨1296779, by rfl⟩ : syracuseStep 1729039 = 2593559) B2593559
theorem B3695165 : Blo 1024605 3695165 := bstep (se 3 (by rfl) ⟨692843, by rfl⟩ : syracuseStep 3695165 = 1385687) B1385687
theorem B11264579 : Blo 1024605 11264579 := bstep (se 1 (by rfl) ⟨8448434, by rfl⟩ : syracuseStep 11264579 = 16896869) B16896869
theorem B5857879 : Blo 1024605 5857879 := bstep (se 1 (by rfl) ⟨4393409, by rfl⟩ : syracuseStep 5857879 = 8786819) B8786819
theorem B79880995 : Blo 1024605 79880995 := bstep (se 1 (by rfl) ⟨59910746, by rfl⟩ : syracuseStep 79880995 = 119821493) B119821493
theorem B3466043 : Blo 1024605 3466043 := bstep (se 1 (by rfl) ⟨2599532, by rfl⟩ : syracuseStep 3466043 = 5199065) B5199065
theorem B2777915 : Blo 1024605 2777915 := bstep (se 1 (by rfl) ⟨2083436, by rfl⟩ : syracuseStep 2777915 = 4166873) B4166873
theorem B1729579 : Blo 1024605 1729579 := bstep (se 1 (by rfl) ⟨1297184, by rfl⟩ : syracuseStep 1729579 = 2594369) B2594369
theorem B5334083 : Blo 1024605 5334083 := bstep (se 1 (by rfl) ⟨4000562, by rfl⟩ : syracuseStep 5334083 = 8001125) B8001125
theorem B1729721 : Blo 1024605 1729721 := bstep (se 2 (by rfl) ⟨648645, by rfl⟩ : syracuseStep 1729721 = 1297291) B1297291
theorem B3892481 : Blo 1024605 3892481 := bstep (se 2 (by rfl) ⟨1459680, by rfl⟩ : syracuseStep 3892481 = 2919361) B2919361
theorem B3892495 : Blo 1024605 3892495 := bstep (se 1 (by rfl) ⟨2919371, by rfl⟩ : syracuseStep 3892495 = 5838743) B5838743
theorem B3466529 : Blo 1024605 3466529 := bstep (se 2 (by rfl) ⟨1299948, by rfl⟩ : syracuseStep 3466529 = 2599897) B2599897
theorem B4384115 : Blo 1024605 4384115 := bstep (se 1 (by rfl) ⟨3288086, by rfl⟩ : syracuseStep 4384115 = 6576173) B6576173
theorem B2778553 : Blo 1024605 2778553 := bstep (se 2 (by rfl) ⟨1041957, by rfl⟩ : syracuseStep 2778553 = 2083915) B2083915
theorem B5203763 : Blo 1024605 5203763 := bstep (se 1 (by rfl) ⟨3902822, by rfl⟩ : syracuseStep 5203763 = 7805645) B7805645
theorem B3467123 : Blo 1024605 3467123 := bstep (se 1 (by rfl) ⟨2600342, by rfl⟩ : syracuseStep 3467123 = 5200685) B5200685
theorem B1730423 : Blo 1024605 1730423 := bstep (se 1 (by rfl) ⟨1297817, by rfl⟩ : syracuseStep 1730423 = 2595635) B2595635
theorem B5204087 : Blo 1024605 5204087 := bstep (se 1 (by rfl) ⟨3903065, by rfl⟩ : syracuseStep 5204087 = 7806131) B7806131
theorem B1730875 : Blo 1024605 1730875 := bstep (se 1 (by rfl) ⟨1298156, by rfl⟩ : syracuseStep 1730875 = 2596313) B2596313
theorem B1731017 : Blo 1024605 1731017 := bstep (se 2 (by rfl) ⟨649131, by rfl⟩ : syracuseStep 1731017 = 1298263) B1298263
theorem B3893771 : Blo 1024605 3893771 := bstep (se 1 (by rfl) ⟨2920328, by rfl⟩ : syracuseStep 3893771 = 5840657) B5840657
theorem B5205059 : Blo 1024605 5205059 := bstep (se 1 (by rfl) ⟨3903794, by rfl⟩ : syracuseStep 5205059 = 7807589) B7807589
theorem B1731719 : Blo 1024605 1731719 := bstep (se 1 (by rfl) ⟨1298789, by rfl⟩ : syracuseStep 1731719 = 2597579) B2597579
theorem B5205383 : Blo 1024605 5205383 := bstep (se 1 (by rfl) ⟨3904037, by rfl⟩ : syracuseStep 5205383 = 7808075) B7808075
theorem B3894713 : Blo 1024605 3894713 := bstep (se 2 (by rfl) ⟨1460517, by rfl⟩ : syracuseStep 3894713 = 2921035) B2921035
theorem B6254009 : Blo 1024605 6254009 := bstep (se 2 (by rfl) ⟨2345253, by rfl⟩ : syracuseStep 6254009 = 4690507) B4690507
theorem B7400963 : Blo 1024605 7400963 := bstep (se 1 (by rfl) ⟨5550722, by rfl⟩ : syracuseStep 7400963 = 11101445) B11101445
theorem B5009069 : Blo 1024605 5009069 := bstep (se 3 (by rfl) ⟨939200, by rfl⟩ : syracuseStep 5009069 = 1878401) B1878401
theorem B1732367 : Blo 1024605 1732367 := bstep (se 1 (by rfl) ⟨1299275, by rfl⟩ : syracuseStep 1732367 = 2598551) B2598551
theorem B4386575 : Blo 1024605 4386575 := bstep (se 1 (by rfl) ⟨3289931, by rfl⟩ : syracuseStep 4386575 = 6579863) B6579863
theorem B7401253 : Blo 1024605 7401253 := bstep (se 4 (by rfl) ⟨693867, by rfl⟩ : syracuseStep 7401253 = 1387735) B1387735
theorem B42168215 : Blo 1024605 42168215 := bstep (se 1 (by rfl) ⟨31626161, by rfl⟩ : syracuseStep 42168215 = 63252323) B63252323
theorem B4157369 : Blo 1024605 4157369 := bstep (se 2 (by rfl) ⟨1559013, by rfl⟩ : syracuseStep 4157369 = 3118027) B3118027
theorem B1732907 : Blo 1024605 1732907 := bstep (se 1 (by rfl) ⟨1299680, by rfl⟩ : syracuseStep 1732907 = 2599361) B2599361
theorem B6746503 : Blo 1024605 6746503 := bstep (se 1 (by rfl) ⟨5059877, by rfl⟩ : syracuseStep 6746503 = 10119755) B10119755
theorem B3469715 : Blo 1024605 3469715 := bstep (se 1 (by rfl) ⟨2602286, by rfl⟩ : syracuseStep 3469715 = 5204573) B5204573
theorem B1733305 : Blo 1024605 1733305 := bstep (se 2 (by rfl) ⟨649989, by rfl⟩ : syracuseStep 1733305 = 1299979) B1299979
theorem B1536911 : Blo 1024605 1536911 := bstep (se 1 (by rfl) ⟨1152683, by rfl⟩ : syracuseStep 1536911 = 2305367) B2305367
theorem B1536953 : Blo 1024605 1536953 := bstep (se 2 (by rfl) ⟨576357, by rfl⟩ : syracuseStep 1536953 = 1152715) B1152715
theorem B1537031 : Blo 1024605 1537031 := bstep (se 1 (by rfl) ⟨1152773, by rfl⟩ : syracuseStep 1537031 = 2305547) B2305547
theorem B2192417 : Blo 1024605 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B1537067 : Blo 1024605 1537067 := bstep (se 1 (by rfl) ⟨1152800, by rfl⟩ : syracuseStep 1537067 = 2305601) B2305601
theorem B1537097 : Blo 1024605 1537097 := bstep (se 2 (by rfl) ⟨576411, by rfl⟩ : syracuseStep 1537097 = 1152823) B1152823
theorem B1537211 : Blo 1024605 1537211 := bstep (se 1 (by rfl) ⟨1152908, by rfl⟩ : syracuseStep 1537211 = 2305817) B2305817
theorem B1537271 : Blo 1024605 1537271 := bstep (se 1 (by rfl) ⟨1152953, by rfl⟩ : syracuseStep 1537271 = 2305907) B2305907
theorem B1537295 : Blo 1024605 1537295 := bstep (se 1 (by rfl) ⟨1152971, by rfl⟩ : syracuseStep 1537295 = 2305943) B2305943
theorem B1537337 : Blo 1024605 1537337 := bstep (se 2 (by rfl) ⟨576501, by rfl⟩ : syracuseStep 1537337 = 1153003) B1153003
theorem B1734007 : Blo 1024605 1734007 := bstep (se 1 (by rfl) ⟨1300505, by rfl⟩ : syracuseStep 1734007 = 2601011) B2601011
theorem B1537415 : Blo 1024605 1537415 := bstep (se 1 (by rfl) ⟨1153061, by rfl⟩ : syracuseStep 1537415 = 2306123) B2306123
theorem B1537451 : Blo 1024605 1537451 := bstep (se 1 (by rfl) ⟨1153088, by rfl⟩ : syracuseStep 1537451 = 2306177) B2306177
theorem B1537481 : Blo 1024605 1537481 := bstep (se 2 (by rfl) ⟨576555, by rfl⟩ : syracuseStep 1537481 = 1153111) B1153111
theorem B1537595 : Blo 1024605 1537595 := bstep (se 1 (by rfl) ⟨1153196, by rfl⟩ : syracuseStep 1537595 = 2306393) B2306393
theorem B1734203 : Blo 1024605 1734203 := bstep (se 1 (by rfl) ⟨1300652, by rfl⟩ : syracuseStep 1734203 = 2601305) B2601305
theorem B8451661 : Blo 1024605 8451661 := bstep (se 3 (by rfl) ⟨1584686, by rfl⟩ : syracuseStep 8451661 = 3169373) B3169373
theorem B1537655 : Blo 1024605 1537655 := bstep (se 1 (by rfl) ⟨1153241, by rfl⟩ : syracuseStep 1537655 = 2306483) B2306483
theorem B1537679 : Blo 1024605 1537679 := bstep (se 1 (by rfl) ⟨1153259, by rfl⟩ : syracuseStep 1537679 = 2306519) B2306519
theorem B1537721 : Blo 1024605 1537721 := bstep (se 2 (by rfl) ⟨576645, by rfl⟩ : syracuseStep 1537721 = 1153291) B1153291
theorem B7894721 : Blo 1024605 7894721 := bstep (se 2 (by rfl) ⟨2960520, by rfl⟩ : syracuseStep 7894721 = 5921041) B5921041
theorem B1537799 : Blo 1024605 1537799 := bstep (se 1 (by rfl) ⟨1153349, by rfl⟩ : syracuseStep 1537799 = 2306699) B2306699
theorem B3471119 : Blo 1024605 3471119 := bstep (se 1 (by rfl) ⟨2603339, by rfl⟩ : syracuseStep 3471119 = 5206679) B5206679
theorem B1537835 : Blo 1024605 1537835 := bstep (se 1 (by rfl) ⟨1153376, by rfl⟩ : syracuseStep 1537835 = 2306753) B2306753
theorem B1537865 : Blo 1024605 1537865 := bstep (se 2 (by rfl) ⟨576699, by rfl⟩ : syracuseStep 1537865 = 1153399) B1153399
theorem B1537979 : Blo 1024605 1537979 := bstep (se 1 (by rfl) ⟨1153484, by rfl⟩ : syracuseStep 1537979 = 2306969) B2306969
theorem B1734601 : Blo 1024605 1734601 := bstep (se 2 (by rfl) ⟨650475, by rfl⟩ : syracuseStep 1734601 = 1300951) B1300951
theorem B11696075 : Blo 1024605 11696075 := bstep (se 1 (by rfl) ⟨8772056, by rfl⟩ : syracuseStep 11696075 = 17544113) B17544113
theorem B8452043 : Blo 1024605 8452043 := bstep (se 1 (by rfl) ⟨6339032, by rfl⟩ : syracuseStep 8452043 = 12678065) B12678065
theorem B1538039 : Blo 1024605 1538039 := bstep (se 1 (by rfl) ⟨1153529, by rfl⟩ : syracuseStep 1538039 = 2307059) B2307059
theorem B3897355 : Blo 1024605 3897355 := bstep (se 1 (by rfl) ⟨2923016, by rfl⟩ : syracuseStep 3897355 = 5846033) B5846033
theorem B1538063 : Blo 1024605 1538063 := bstep (se 1 (by rfl) ⟨1153547, by rfl⟩ : syracuseStep 1538063 = 2307095) B2307095
theorem B3471389 : Blo 1024605 3471389 := bstep (se 3 (by rfl) ⟨650885, by rfl⟩ : syracuseStep 3471389 = 1301771) B1301771
theorem B1538105 : Blo 1024605 1538105 := bstep (se 2 (by rfl) ⟨576789, by rfl⟩ : syracuseStep 1538105 = 1153579) B1153579
theorem B2193527 : Blo 1024605 2193527 := bstep (se 1 (by rfl) ⟨1645145, by rfl⟩ : syracuseStep 2193527 = 3290291) B3290291
theorem B1538183 : Blo 1024605 1538183 := bstep (se 1 (by rfl) ⟨1153637, by rfl⟩ : syracuseStep 1538183 = 2307275) B2307275
theorem B1538219 : Blo 1024605 1538219 := bstep (se 1 (by rfl) ⟨1153664, by rfl⟩ : syracuseStep 1538219 = 2307329) B2307329
theorem B1538249 : Blo 1024605 1538249 := bstep (se 2 (by rfl) ⟨576843, by rfl⟩ : syracuseStep 1538249 = 1153687) B1153687
theorem B1538363 : Blo 1024605 1538363 := bstep (se 1 (by rfl) ⟨1153772, by rfl⟩ : syracuseStep 1538363 = 2307545) B2307545
theorem B3897659 : Blo 1024605 3897659 := bstep (se 1 (by rfl) ⟨2923244, by rfl⟩ : syracuseStep 3897659 = 5846489) B5846489
theorem B1538423 : Blo 1024605 1538423 := bstep (se 1 (by rfl) ⟨1153817, by rfl⟩ : syracuseStep 1538423 = 2307635) B2307635
theorem B1538447 : Blo 1024605 1538447 := bstep (se 1 (by rfl) ⟨1153835, by rfl⟩ : syracuseStep 1538447 = 2307671) B2307671
theorem B73202069 : Blo 1024605 73202069 := bstep (se 6 (by rfl) ⟨1715673, by rfl⟩ : syracuseStep 73202069 = 3431347) B3431347
theorem B1538489 : Blo 1024605 1538489 := bstep (se 2 (by rfl) ⟨576933, by rfl⟩ : syracuseStep 1538489 = 1153867) B1153867
theorem B1538567 : Blo 1024605 1538567 := bstep (se 1 (by rfl) ⟨1153925, by rfl⟩ : syracuseStep 1538567 = 2307851) B2307851
theorem B1538603 : Blo 1024605 1538603 := bstep (se 1 (by rfl) ⟨1153952, by rfl⟩ : syracuseStep 1538603 = 2307905) B2307905
theorem B1538633 : Blo 1024605 1538633 := bstep (se 2 (by rfl) ⟨576987, by rfl⟩ : syracuseStep 1538633 = 1153975) B1153975
theorem B1735303 : Blo 1024605 1735303 := bstep (se 1 (by rfl) ⟨1301477, by rfl⟩ : syracuseStep 1735303 = 2602955) B2602955
theorem B1538747 : Blo 1024605 1538747 := bstep (se 1 (by rfl) ⟨1154060, by rfl⟩ : syracuseStep 1538747 = 2308121) B2308121
theorem B1538807 : Blo 1024605 1538807 := bstep (se 1 (by rfl) ⟨1154105, by rfl⟩ : syracuseStep 1538807 = 2308211) B2308211
theorem B1538831 : Blo 1024605 1538831 := bstep (se 1 (by rfl) ⟨1154123, by rfl⟩ : syracuseStep 1538831 = 2308247) B2308247
theorem B3898145 : Blo 1024605 3898145 := bstep (se 2 (by rfl) ⟨1461804, by rfl⟩ : syracuseStep 3898145 = 2923609) B2923609
theorem B1538873 : Blo 1024605 1538873 := bstep (se 2 (by rfl) ⟨577077, by rfl⟩ : syracuseStep 1538873 = 1154155) B1154155
theorem B13171571 : Blo 1024605 13171571 := bstep (se 1 (by rfl) ⟨9878678, by rfl⟩ : syracuseStep 13171571 = 19757357) B19757357
theorem B1538951 : Blo 1024605 1538951 := bstep (se 1 (by rfl) ⟨1154213, by rfl⟩ : syracuseStep 1538951 = 2308427) B2308427
theorem B1538987 : Blo 1024605 1538987 := bstep (se 1 (by rfl) ⟨1154240, by rfl⟩ : syracuseStep 1538987 = 2308481) B2308481
theorem B1539017 : Blo 1024605 1539017 := bstep (se 2 (by rfl) ⟨577131, by rfl⟩ : syracuseStep 1539017 = 1154263) B1154263
theorem B1539131 : Blo 1024605 1539131 := bstep (se 1 (by rfl) ⟨1154348, by rfl⟩ : syracuseStep 1539131 = 2308697) B2308697
theorem B1539191 : Blo 1024605 1539191 := bstep (se 1 (by rfl) ⟨1154393, by rfl⟩ : syracuseStep 1539191 = 2308787) B2308787
theorem B19725443 : Blo 1024605 19725443 := bstep (se 1 (by rfl) ⟨14794082, by rfl⟩ : syracuseStep 19725443 = 29588165) B29588165
theorem B11238533 : Blo 1024605 11238533 := bstep (se 4 (by rfl) ⟨1053612, by rfl⟩ : syracuseStep 11238533 = 2107225) B2107225
theorem B14777477 : Blo 1024605 14777477 := bstep (se 4 (by rfl) ⟨1385388, by rfl⟩ : syracuseStep 14777477 = 2770777) B2770777
theorem B1539215 : Blo 1024605 1539215 := bstep (se 1 (by rfl) ⟨1154411, by rfl⟩ : syracuseStep 1539215 = 2308823) B2308823
theorem B1539257 : Blo 1024605 1539257 := bstep (se 2 (by rfl) ⟨577221, by rfl⟩ : syracuseStep 1539257 = 1154443) B1154443
theorem B1539335 : Blo 1024605 1539335 := bstep (se 1 (by rfl) ⟨1154501, by rfl⟩ : syracuseStep 1539335 = 2309003) B2309003
theorem B1539371 : Blo 1024605 1539371 := bstep (se 1 (by rfl) ⟨1154528, by rfl⟩ : syracuseStep 1539371 = 2309057) B2309057
theorem B1539401 : Blo 1024605 1539401 := bstep (se 2 (by rfl) ⟨577275, by rfl⟩ : syracuseStep 1539401 = 1154551) B1154551
theorem B1539515 : Blo 1024605 1539515 := bstep (se 1 (by rfl) ⟨1154636, by rfl⟩ : syracuseStep 1539515 = 2309273) B2309273
theorem B1539575 : Blo 1024605 1539575 := bstep (se 1 (by rfl) ⟨1154681, by rfl⟩ : syracuseStep 1539575 = 2309363) B2309363
theorem B1539599 : Blo 1024605 1539599 := bstep (se 1 (by rfl) ⟨1154699, by rfl⟩ : syracuseStep 1539599 = 2309399) B2309399
theorem B1539641 : Blo 1024605 1539641 := bstep (se 2 (by rfl) ⟨577365, by rfl⟩ : syracuseStep 1539641 = 1154731) B1154731
theorem B1539719 : Blo 1024605 1539719 := bstep (se 1 (by rfl) ⟨1154789, by rfl⟩ : syracuseStep 1539719 = 2309579) B2309579
theorem B1539755 : Blo 1024605 1539755 := bstep (se 1 (by rfl) ⟨1154816, by rfl⟩ : syracuseStep 1539755 = 2309633) B2309633
theorem B1539785 : Blo 1024605 1539785 := bstep (se 2 (by rfl) ⟨577419, by rfl⟩ : syracuseStep 1539785 = 1154839) B1154839
theorem B3702473 : Blo 1024605 3702473 := bstep (se 2 (by rfl) ⟨1388427, by rfl⟩ : syracuseStep 3702473 = 2776855) B2776855
theorem B3899117 : Blo 1024605 3899117 := bstep (se 3 (by rfl) ⟨731084, by rfl⟩ : syracuseStep 3899117 = 1462169) B1462169
theorem B1539899 : Blo 1024605 1539899 := bstep (se 1 (by rfl) ⟨1154924, by rfl⟩ : syracuseStep 1539899 = 2309849) B2309849
theorem B1539959 : Blo 1024605 1539959 := bstep (se 1 (by rfl) ⟨1154969, by rfl⟩ : syracuseStep 1539959 = 2309939) B2309939
theorem B1539983 : Blo 1024605 1539983 := bstep (se 1 (by rfl) ⟨1154987, by rfl⟩ : syracuseStep 1539983 = 2309975) B2309975
theorem B1540025 : Blo 1024605 1540025 := bstep (se 2 (by rfl) ⟨577509, by rfl⟩ : syracuseStep 1540025 = 1155019) B1155019
theorem B4227079 : Blo 1024605 4227079 := bstep (se 1 (by rfl) ⟨3170309, by rfl⟩ : syracuseStep 4227079 = 6340619) B6340619
theorem B29982737 : Blo 1024605 29982737 := bstep (se 2 (by rfl) ⟨11243526, by rfl⟩ : syracuseStep 29982737 = 22487053) B22487053
theorem B7798841 : Blo 1024605 7798841 := bstep (se 2 (by rfl) ⟨2924565, by rfl⟩ : syracuseStep 7798841 = 5849131) B5849131
theorem B1540175 : Blo 1024605 1540175 := bstep (se 1 (by rfl) ⟨1155131, by rfl⟩ : syracuseStep 1540175 = 2310263) B2310263
theorem B1540295 : Blo 1024605 1540295 := bstep (se 1 (by rfl) ⟨1155221, by rfl⟩ : syracuseStep 1540295 = 2310443) B2310443
theorem B1540457 : Blo 1024605 1540457 := bstep (se 2 (by rfl) ⟨577671, by rfl⟩ : syracuseStep 1540457 = 1155343) B1155343
theorem B1540535 : Blo 1024605 1540535 := bstep (se 1 (by rfl) ⟨1155401, by rfl⟩ : syracuseStep 1540535 = 2310803) B2310803
theorem B1540571 : Blo 1024605 1540571 := bstep (se 1 (by rfl) ⟨1155428, by rfl⟩ : syracuseStep 1540571 = 2310857) B2310857
theorem B3900089 : Blo 1024605 3900089 := bstep (se 2 (by rfl) ⟨1462533, by rfl⟩ : syracuseStep 3900089 = 2925067) B2925067
theorem B4391633 : Blo 1024605 4391633 := bstep (se 2 (by rfl) ⟨1646862, by rfl⟩ : syracuseStep 4391633 = 3293725) B3293725
theorem B15008561 : Blo 1024605 15008561 := bstep (se 2 (by rfl) ⟨5628210, by rfl⟩ : syracuseStep 15008561 = 11256421) B11256421
theorem B1541039 : Blo 1024605 1541039 := bstep (se 1 (by rfl) ⟨1155779, by rfl⟩ : syracuseStep 1541039 = 2311559) B2311559
theorem B1541129 : Blo 1024605 1541129 := bstep (se 2 (by rfl) ⟨577923, by rfl⟩ : syracuseStep 1541129 = 1155847) B1155847
theorem B1541159 : Blo 1024605 1541159 := bstep (se 1 (by rfl) ⟨1155869, by rfl⟩ : syracuseStep 1541159 = 2311739) B2311739
theorem B24052787 : Blo 1024605 24052787 := bstep (se 1 (by rfl) ⟨18039590, by rfl⟩ : syracuseStep 24052787 = 36079181) B36079181
theorem B1541243 : Blo 1024605 1541243 := bstep (se 1 (by rfl) ⟨1155932, by rfl⟩ : syracuseStep 1541243 = 2311865) B2311865
theorem B15008971 : Blo 1024605 15008971 := bstep (se 1 (by rfl) ⟨11256728, by rfl⟩ : syracuseStep 15008971 = 22513457) B22513457
theorem B1541369 : Blo 1024605 1541369 := bstep (se 2 (by rfl) ⟨578013, by rfl⟩ : syracuseStep 1541369 = 1156027) B1156027
theorem B1541471 : Blo 1024605 1541471 := bstep (se 1 (by rfl) ⟨1156103, by rfl⟩ : syracuseStep 1541471 = 2312207) B2312207
theorem B1541483 : Blo 1024605 1541483 := bstep (se 1 (by rfl) ⟨1156112, by rfl⟩ : syracuseStep 1541483 = 2312225) B2312225
theorem B1541711 : Blo 1024605 1541711 := bstep (se 1 (by rfl) ⟨1156283, by rfl⟩ : syracuseStep 1541711 = 2312567) B2312567
theorem B1541831 : Blo 1024605 1541831 := bstep (se 1 (by rfl) ⟨1156373, by rfl⟩ : syracuseStep 1541831 = 2312747) B2312747
theorem B1541993 : Blo 1024605 1541993 := bstep (se 2 (by rfl) ⟨578247, by rfl⟩ : syracuseStep 1541993 = 1156495) B1156495
theorem B3704737 : Blo 1024605 3704737 := bstep (se 2 (by rfl) ⟨1389276, by rfl⟩ : syracuseStep 3704737 = 2778553) B2778553
theorem B1542071 : Blo 1024605 1542071 := bstep (se 1 (by rfl) ⟨1156553, by rfl⟩ : syracuseStep 1542071 = 2313107) B2313107
theorem B7800785 : Blo 1024605 7800785 := bstep (se 2 (by rfl) ⟨2925294, by rfl⟩ : syracuseStep 7800785 = 5850589) B5850589
theorem B1542107 : Blo 1024605 1542107 := bstep (se 1 (by rfl) ⟨1156580, by rfl⟩ : syracuseStep 1542107 = 2313161) B2313161
theorem B1542575 : Blo 1024605 1542575 := bstep (se 1 (by rfl) ⟨1156931, by rfl⟩ : syracuseStep 1542575 = 2313863) B2313863
theorem B1542665 : Blo 1024605 1542665 := bstep (se 2 (by rfl) ⟨578499, by rfl⟩ : syracuseStep 1542665 = 1156999) B1156999
theorem B1542695 : Blo 1024605 1542695 := bstep (se 1 (by rfl) ⟨1157021, by rfl⟩ : syracuseStep 1542695 = 2314043) B2314043
theorem B7899707 : Blo 1024605 7899707 := bstep (se 1 (by rfl) ⟨5924780, by rfl⟩ : syracuseStep 7899707 = 11849561) B11849561
theorem B1542779 : Blo 1024605 1542779 := bstep (se 1 (by rfl) ⟨1157084, by rfl⟩ : syracuseStep 1542779 = 2314169) B2314169
theorem B14781113 : Blo 1024605 14781113 := bstep (se 2 (by rfl) ⟨5542917, by rfl⟩ : syracuseStep 14781113 = 11085835) B11085835
theorem B3902201 : Blo 1024605 3902201 := bstep (se 2 (by rfl) ⟨1463325, by rfl⟩ : syracuseStep 3902201 = 2926651) B2926651
theorem B1542905 : Blo 1024605 1542905 := bstep (se 2 (by rfl) ⟨578589, by rfl⟩ : syracuseStep 1542905 = 1157179) B1157179
theorem B106597387 : Blo 1024605 106597387 := bstep (se 1 (by rfl) ⟨79948040, by rfl⟩ : syracuseStep 106597387 = 159896081) B159896081
theorem B5835827 : Blo 1024605 5835827 := bstep (se 1 (by rfl) ⟨4376870, by rfl⟩ : syracuseStep 5835827 = 8753741) B8753741
theorem B7408691 : Blo 1024605 7408691 := bstep (se 1 (by rfl) ⟨5556518, by rfl⟩ : syracuseStep 7408691 = 11113037) B11113037
theorem B67571117 : Blo 1024605 67571117 := bstep (se 3 (by rfl) ⟨12669584, by rfl⟩ : syracuseStep 67571117 = 25339169) B25339169
theorem B11079301 : Blo 1024605 11079301 := bstep (se 4 (by rfl) ⟨1038684, by rfl⟩ : syracuseStep 11079301 = 2077369) B2077369
theorem B3903187 : Blo 1024605 3903187 := bstep (se 1 (by rfl) ⟨2927390, by rfl⟩ : syracuseStep 3903187 = 5854781) B5854781
theorem B1806223 : Blo 1024605 1806223 := bstep (se 1 (by rfl) ⟨1354667, by rfl⟩ : syracuseStep 1806223 = 2709335) B2709335
theorem B3903659 : Blo 1024605 3903659 := bstep (se 1 (by rfl) ⟨2927744, by rfl⟩ : syracuseStep 3903659 = 5855489) B5855489
theorem B48730385 : Blo 1024605 48730385 := bstep (se 2 (by rfl) ⟨18273894, by rfl⟩ : syracuseStep 48730385 = 36547789) B36547789
theorem B1642859 : Blo 1024605 1642859 := bstep (se 1 (by rfl) ⟨1232144, by rfl⟩ : syracuseStep 1642859 = 2464289) B2464289
theorem B3117757 : Blo 1024605 3117757 := bstep (se 3 (by rfl) ⟨584579, by rfl⟩ : syracuseStep 3117757 = 1169159) B1169159
theorem B9376769 : Blo 1024605 9376769 := bstep (se 2 (by rfl) ⟨3516288, by rfl⟩ : syracuseStep 9376769 = 7032577) B7032577
theorem B9868337 : Blo 1024605 9868337 := bstep (se 2 (by rfl) ⟨3700626, by rfl⟩ : syracuseStep 9868337 = 7401253) B7401253
theorem B2594177 : Blo 1024605 2594177 := bstep (se 2 (by rfl) ⟨972816, by rfl⟩ : syracuseStep 2594177 = 1945633) B1945633
theorem B2463443 : Blo 1024605 2463443 := bstep (se 1 (by rfl) ⟨1847582, by rfl⟩ : syracuseStep 2463443 = 3695165) B3695165
theorem B7509719 : Blo 1024605 7509719 := bstep (se 1 (by rfl) ⟨5632289, by rfl⟩ : syracuseStep 7509719 = 11264579) B11264579
theorem B11671289 : Blo 1024605 11671289 := bstep (se 2 (by rfl) ⟨4376733, by rfl⟩ : syracuseStep 11671289 = 8753467) B8753467
theorem B18749393 : Blo 1024605 18749393 := bstep (se 2 (by rfl) ⟨7031022, by rfl⟩ : syracuseStep 18749393 = 14062045) B14062045
theorem B1153147 : Blo 1024605 1153147 := bstep (se 1 (by rfl) ⟨864860, by rfl⟩ : syracuseStep 1153147 = 1729721) B1729721
theorem B2594987 : Blo 1024605 2594987 := bstep (se 1 (by rfl) ⟨1946240, by rfl⟩ : syracuseStep 2594987 = 3892481) B3892481
theorem B2922743 : Blo 1024605 2922743 := bstep (se 1 (by rfl) ⟨2192057, by rfl⟩ : syracuseStep 2922743 = 4384115) B4384115
theorem B1153615 : Blo 1024605 1153615 := bstep (se 1 (by rfl) ⟨865211, by rfl⟩ : syracuseStep 1153615 = 1730423) B1730423
theorem B1154011 : Blo 1024605 1154011 := bstep (se 1 (by rfl) ⟨865508, by rfl⟩ : syracuseStep 1154011 = 1731017) B1731017
theorem B2595847 : Blo 1024605 2595847 := bstep (se 1 (by rfl) ⟨1946885, by rfl⟩ : syracuseStep 2595847 = 3893771) B3893771
theorem B7019723 : Blo 1024605 7019723 := bstep (se 1 (by rfl) ⟨5264792, by rfl⟩ : syracuseStep 7019723 = 10529585) B10529585
theorem B1154479 : Blo 1024605 1154479 := bstep (se 1 (by rfl) ⟨865859, by rfl⟩ : syracuseStep 1154479 = 1731719) B1731719
theorem B2596475 : Blo 1024605 2596475 := bstep (se 1 (by rfl) ⟨1947356, by rfl⟩ : syracuseStep 2596475 = 3894713) B3894713
theorem B4169339 : Blo 1024605 4169339 := bstep (se 1 (by rfl) ⟨3127004, by rfl⟩ : syracuseStep 4169339 = 6254009) B6254009
theorem B4169465 : Blo 1024605 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B1154911 : Blo 1024605 1154911 := bstep (se 1 (by rfl) ⟨866183, by rfl⟩ : syracuseStep 1154911 = 1732367) B1732367
theorem B2596769 : Blo 1024605 2596769 := bstep (se 2 (by rfl) ⟨973788, by rfl⟩ : syracuseStep 2596769 = 1947577) B1947577
theorem B3285011 : Blo 1024605 3285011 := bstep (se 1 (by rfl) ⟨2463758, by rfl⟩ : syracuseStep 3285011 = 4927517) B4927517
theorem B1646671 : Blo 1024605 1646671 := bstep (se 1 (by rfl) ⟨1235003, by rfl⟩ : syracuseStep 1646671 = 2470007) B2470007
theorem B63971477 : Blo 1024605 63971477 := bstep (se 6 (by rfl) ⟨1499331, by rfl⟩ : syracuseStep 63971477 = 2998663) B2998663
theorem B5546141 : Blo 1024605 5546141 := bstep (se 3 (by rfl) ⟨1039901, by rfl⟩ : syracuseStep 5546141 = 2079803) B2079803
theorem B1155271 : Blo 1024605 1155271 := bstep (se 1 (by rfl) ⟨866453, by rfl⟩ : syracuseStep 1155271 = 1732907) B1732907
theorem B1384999 : Blo 1024605 1384999 := bstep (se 1 (by rfl) ⟨1038749, by rfl⟩ : syracuseStep 1384999 = 2077499) B2077499
theorem B1024607 : Blo 1024605 1024607 := bstep (se 1 (by rfl) ⟨768455, by rfl⟩ : syracuseStep 1024607 = 1536911) B1536911
theorem B1024635 : Blo 1024605 1024635 := bstep (se 1 (by rfl) ⟨768476, by rfl⟩ : syracuseStep 1024635 = 1536953) B1536953
theorem B1024687 : Blo 1024605 1024687 := bstep (se 1 (by rfl) ⟨768515, by rfl⟩ : syracuseStep 1024687 = 1537031) B1537031
theorem B1024711 : Blo 1024605 1024711 := bstep (se 1 (by rfl) ⟨768533, by rfl⟩ : syracuseStep 1024711 = 1537067) B1537067
theorem B6234833 : Blo 1024605 6234833 := bstep (se 2 (by rfl) ⟨2338062, by rfl⟩ : syracuseStep 6234833 = 4676125) B4676125
theorem B1024731 : Blo 1024605 1024731 := bstep (se 1 (by rfl) ⟨768548, by rfl⟩ : syracuseStep 1024731 = 1537097) B1537097
theorem B1024807 : Blo 1024605 1024807 := bstep (se 1 (by rfl) ⟨768605, by rfl⟩ : syracuseStep 1024807 = 1537211) B1537211
theorem B1024847 : Blo 1024605 1024847 := bstep (se 1 (by rfl) ⟨768635, by rfl⟩ : syracuseStep 1024847 = 1537271) B1537271
theorem B1024863 : Blo 1024605 1024863 := bstep (se 1 (by rfl) ⟨768647, by rfl⟩ : syracuseStep 1024863 = 1537295) B1537295
theorem B1024891 : Blo 1024605 1024891 := bstep (se 1 (by rfl) ⟨768668, by rfl⟩ : syracuseStep 1024891 = 1537337) B1537337
theorem B1024943 : Blo 1024605 1024943 := bstep (se 1 (by rfl) ⟨768707, by rfl⟩ : syracuseStep 1024943 = 1537415) B1537415
theorem B1024967 : Blo 1024605 1024967 := bstep (se 1 (by rfl) ⟨768725, by rfl⟩ : syracuseStep 1024967 = 1537451) B1537451
theorem B1024987 : Blo 1024605 1024987 := bstep (se 1 (by rfl) ⟨768740, by rfl⟩ : syracuseStep 1024987 = 1537481) B1537481
theorem B1025063 : Blo 1024605 1025063 := bstep (se 1 (by rfl) ⟨768797, by rfl⟩ : syracuseStep 1025063 = 1537595) B1537595
theorem B1156135 : Blo 1024605 1156135 := bstep (se 1 (by rfl) ⟨867101, by rfl⟩ : syracuseStep 1156135 = 1734203) B1734203
theorem B1025103 : Blo 1024605 1025103 := bstep (se 1 (by rfl) ⟨768827, by rfl⟩ : syracuseStep 1025103 = 1537655) B1537655
theorem B1025119 : Blo 1024605 1025119 := bstep (se 1 (by rfl) ⟨768839, by rfl⟩ : syracuseStep 1025119 = 1537679) B1537679
theorem B1025147 : Blo 1024605 1025147 := bstep (se 1 (by rfl) ⟨768860, by rfl⟩ : syracuseStep 1025147 = 1537721) B1537721
theorem B3122333 : Blo 1024605 3122333 := bstep (se 3 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 3122333 = 1170875) B1170875
theorem B1025199 : Blo 1024605 1025199 := bstep (se 1 (by rfl) ⟨768899, by rfl⟩ : syracuseStep 1025199 = 1537799) B1537799
theorem B5842115 : Blo 1024605 5842115 := bstep (se 1 (by rfl) ⟨4381586, by rfl⟩ : syracuseStep 5842115 = 8763173) B8763173
theorem B1025223 : Blo 1024605 1025223 := bstep (se 1 (by rfl) ⟨768917, by rfl⟩ : syracuseStep 1025223 = 1537835) B1537835
theorem B1025243 : Blo 1024605 1025243 := bstep (se 1 (by rfl) ⟨768932, by rfl⟩ : syracuseStep 1025243 = 1537865) B1537865
theorem B1025319 : Blo 1024605 1025319 := bstep (se 1 (by rfl) ⟨768989, by rfl⟩ : syracuseStep 1025319 = 1537979) B1537979
theorem B1025359 : Blo 1024605 1025359 := bstep (se 1 (by rfl) ⟨769019, by rfl⟩ : syracuseStep 1025359 = 1538039) B1538039
theorem B1025375 : Blo 1024605 1025375 := bstep (se 1 (by rfl) ⟨769031, by rfl⟩ : syracuseStep 1025375 = 1538063) B1538063
theorem B1025403 : Blo 1024605 1025403 := bstep (se 1 (by rfl) ⟨769052, by rfl⟩ : syracuseStep 1025403 = 1538105) B1538105
theorem B1025455 : Blo 1024605 1025455 := bstep (se 1 (by rfl) ⟨769091, by rfl⟩ : syracuseStep 1025455 = 1538183) B1538183
theorem B1025479 : Blo 1024605 1025479 := bstep (se 1 (by rfl) ⟨769109, by rfl⟩ : syracuseStep 1025479 = 1538219) B1538219
theorem B1025499 : Blo 1024605 1025499 := bstep (se 1 (by rfl) ⟨769124, by rfl⟩ : syracuseStep 1025499 = 1538249) B1538249
theorem B1025575 : Blo 1024605 1025575 := bstep (se 1 (by rfl) ⟨769181, by rfl⟩ : syracuseStep 1025575 = 1538363) B1538363
theorem B2598439 : Blo 1024605 2598439 := bstep (se 1 (by rfl) ⟨1948829, by rfl⟩ : syracuseStep 2598439 = 3897659) B3897659
theorem B1025615 : Blo 1024605 1025615 := bstep (se 1 (by rfl) ⟨769211, by rfl⟩ : syracuseStep 1025615 = 1538423) B1538423
theorem B1025631 : Blo 1024605 1025631 := bstep (se 1 (by rfl) ⟨769223, by rfl⟩ : syracuseStep 1025631 = 1538447) B1538447
theorem B48801379 : Blo 1024605 48801379 := bstep (se 1 (by rfl) ⟨36601034, by rfl⟩ : syracuseStep 48801379 = 73202069) B73202069
theorem B1025659 : Blo 1024605 1025659 := bstep (se 1 (by rfl) ⟨769244, by rfl⟩ : syracuseStep 1025659 = 1538489) B1538489
theorem B3286651 : Blo 1024605 3286651 := bstep (se 1 (by rfl) ⟨2464988, by rfl⟩ : syracuseStep 3286651 = 4929977) B4929977
theorem B1025711 : Blo 1024605 1025711 := bstep (se 1 (by rfl) ⟨769283, by rfl⟩ : syracuseStep 1025711 = 1538567) B1538567
theorem B1025735 : Blo 1024605 1025735 := bstep (se 1 (by rfl) ⟨769301, by rfl⟩ : syracuseStep 1025735 = 1538603) B1538603
theorem B1025755 : Blo 1024605 1025755 := bstep (se 1 (by rfl) ⟨769316, by rfl⟩ : syracuseStep 1025755 = 1538633) B1538633
theorem B1025831 : Blo 1024605 1025831 := bstep (se 1 (by rfl) ⟨769373, by rfl⟩ : syracuseStep 1025831 = 1538747) B1538747
theorem B1025871 : Blo 1024605 1025871 := bstep (se 1 (by rfl) ⟨769403, by rfl⟩ : syracuseStep 1025871 = 1538807) B1538807
theorem B1025887 : Blo 1024605 1025887 := bstep (se 1 (by rfl) ⟨769415, by rfl⟩ : syracuseStep 1025887 = 1538831) B1538831
theorem B2598763 : Blo 1024605 2598763 := bstep (se 1 (by rfl) ⟨1949072, by rfl⟩ : syracuseStep 2598763 = 3898145) B3898145
theorem B1025915 : Blo 1024605 1025915 := bstep (se 1 (by rfl) ⟨769436, by rfl⟩ : syracuseStep 1025915 = 1538873) B1538873
theorem B1025967 : Blo 1024605 1025967 := bstep (se 1 (by rfl) ⟨769475, by rfl⟩ : syracuseStep 1025967 = 1538951) B1538951
theorem B1025991 : Blo 1024605 1025991 := bstep (se 1 (by rfl) ⟨769493, by rfl⟩ : syracuseStep 1025991 = 1538987) B1538987
theorem B1026011 : Blo 1024605 1026011 := bstep (se 1 (by rfl) ⟨769508, by rfl⟩ : syracuseStep 1026011 = 1539017) B1539017
theorem B1026087 : Blo 1024605 1026087 := bstep (se 1 (by rfl) ⟨769565, by rfl⟩ : syracuseStep 1026087 = 1539131) B1539131
theorem B1026127 : Blo 1024605 1026127 := bstep (se 1 (by rfl) ⟨769595, by rfl⟩ : syracuseStep 1026127 = 1539191) B1539191
theorem B13150295 : Blo 1024605 13150295 := bstep (se 1 (by rfl) ⟨9862721, by rfl⟩ : syracuseStep 13150295 = 19725443) B19725443
theorem B1026143 : Blo 1024605 1026143 := bstep (se 1 (by rfl) ⟨769607, by rfl⟩ : syracuseStep 1026143 = 1539215) B1539215
theorem B1026171 : Blo 1024605 1026171 := bstep (se 1 (by rfl) ⟨769628, by rfl⟩ : syracuseStep 1026171 = 1539257) B1539257
theorem B1026223 : Blo 1024605 1026223 := bstep (se 1 (by rfl) ⟨769667, by rfl⟩ : syracuseStep 1026223 = 1539335) B1539335
theorem B1026247 : Blo 1024605 1026247 := bstep (se 1 (by rfl) ⟨769685, by rfl⟩ : syracuseStep 1026247 = 1539371) B1539371
theorem B1026267 : Blo 1024605 1026267 := bstep (se 1 (by rfl) ⟨769700, by rfl⟩ : syracuseStep 1026267 = 1539401) B1539401
theorem B1026343 : Blo 1024605 1026343 := bstep (se 1 (by rfl) ⟨769757, by rfl⟩ : syracuseStep 1026343 = 1539515) B1539515
theorem B1026383 : Blo 1024605 1026383 := bstep (se 1 (by rfl) ⟨769787, by rfl⟩ : syracuseStep 1026383 = 1539575) B1539575
theorem B1026399 : Blo 1024605 1026399 := bstep (se 1 (by rfl) ⟨769799, by rfl⟩ : syracuseStep 1026399 = 1539599) B1539599
theorem B1026427 : Blo 1024605 1026427 := bstep (se 1 (by rfl) ⟨769820, by rfl⟩ : syracuseStep 1026427 = 1539641) B1539641
theorem B1976737 : Blo 1024605 1976737 := bstep (se 2 (by rfl) ⟨741276, by rfl⟩ : syracuseStep 1976737 = 1482553) B1482553
theorem B1026479 : Blo 1024605 1026479 := bstep (se 1 (by rfl) ⟨769859, by rfl⟩ : syracuseStep 1026479 = 1539719) B1539719
theorem B1026503 : Blo 1024605 1026503 := bstep (se 1 (by rfl) ⟨769877, by rfl⟩ : syracuseStep 1026503 = 1539755) B1539755
theorem B1026523 : Blo 1024605 1026523 := bstep (se 1 (by rfl) ⟨769892, by rfl⟩ : syracuseStep 1026523 = 1539785) B1539785
theorem B2468315 : Blo 1024605 2468315 := bstep (se 1 (by rfl) ⟨1851236, by rfl⟩ : syracuseStep 2468315 = 3702473) B3702473
theorem B2599411 : Blo 1024605 2599411 := bstep (se 1 (by rfl) ⟨1949558, by rfl⟩ : syracuseStep 2599411 = 3899117) B3899117
theorem B1026599 : Blo 1024605 1026599 := bstep (se 1 (by rfl) ⟨769949, by rfl⟩ : syracuseStep 1026599 = 1539899) B1539899
theorem B1026639 : Blo 1024605 1026639 := bstep (se 1 (by rfl) ⟨769979, by rfl⟩ : syracuseStep 1026639 = 1539959) B1539959
theorem B1026655 : Blo 1024605 1026655 := bstep (se 1 (by rfl) ⟨769991, by rfl⟩ : syracuseStep 1026655 = 1539983) B1539983
theorem B1026683 : Blo 1024605 1026683 := bstep (se 1 (by rfl) ⟨770012, by rfl⟩ : syracuseStep 1026683 = 1540025) B1540025
theorem B1026735 : Blo 1024605 1026735 := bstep (se 1 (by rfl) ⟨770051, by rfl⟩ : syracuseStep 1026735 = 1540103) B1540103
theorem B1026759 : Blo 1024605 1026759 := bstep (se 1 (by rfl) ⟨770069, by rfl⟩ : syracuseStep 1026759 = 1540139) B1540139
theorem B1026779 : Blo 1024605 1026779 := bstep (se 1 (by rfl) ⟨770084, by rfl⟩ : syracuseStep 1026779 = 1540169) B1540169
theorem B1026855 : Blo 1024605 1026855 := bstep (se 1 (by rfl) ⟨770141, by rfl⟩ : syracuseStep 1026855 = 1540283) B1540283
theorem B3287881 : Blo 1024605 3287881 := bstep (se 2 (by rfl) ⟨1232955, by rfl⟩ : syracuseStep 3287881 = 2465911) B2465911
theorem B1026895 : Blo 1024605 1026895 := bstep (se 1 (by rfl) ⟨770171, by rfl⟩ : syracuseStep 1026895 = 1540343) B1540343
theorem B1026911 : Blo 1024605 1026911 := bstep (se 1 (by rfl) ⟨770183, by rfl⟩ : syracuseStep 1026911 = 1540367) B1540367
theorem B1026939 : Blo 1024605 1026939 := bstep (se 1 (by rfl) ⟨770204, by rfl⟩ : syracuseStep 1026939 = 1540409) B1540409
theorem B1026991 : Blo 1024605 1026991 := bstep (se 1 (by rfl) ⟨770243, by rfl⟩ : syracuseStep 1026991 = 1540487) B1540487
theorem B5188535 : Blo 1024605 5188535 := bstep (se 1 (by rfl) ⟨3891401, by rfl⟩ : syracuseStep 5188535 = 7782803) B7782803
theorem B1027015 : Blo 1024605 1027015 := bstep (se 1 (by rfl) ⟨770261, by rfl⟩ : syracuseStep 1027015 = 1540523) B1540523
theorem B1027035 : Blo 1024605 1027035 := bstep (se 1 (by rfl) ⟨770276, by rfl⟩ : syracuseStep 1027035 = 1540553) B1540553
theorem B1027111 : Blo 1024605 1027111 := bstep (se 1 (by rfl) ⟨770333, by rfl⟩ : syracuseStep 1027111 = 1540667) B1540667
theorem B1027151 : Blo 1024605 1027151 := bstep (se 1 (by rfl) ⟨770363, by rfl⟩ : syracuseStep 1027151 = 1540727) B1540727
theorem B1027167 : Blo 1024605 1027167 := bstep (se 1 (by rfl) ⟨770375, by rfl⟩ : syracuseStep 1027167 = 1540751) B1540751
theorem B1027195 : Blo 1024605 1027195 := bstep (se 1 (by rfl) ⟨770396, by rfl⟩ : syracuseStep 1027195 = 1540793) B1540793
theorem B1027247 : Blo 1024605 1027247 := bstep (se 1 (by rfl) ⟨770435, by rfl⟩ : syracuseStep 1027247 = 1540871) B1540871
theorem B1027271 : Blo 1024605 1027271 := bstep (se 1 (by rfl) ⟨770453, by rfl⟩ : syracuseStep 1027271 = 1540907) B1540907
theorem B1027291 : Blo 1024605 1027291 := bstep (se 1 (by rfl) ⟨770468, by rfl⟩ : syracuseStep 1027291 = 1540937) B1540937
theorem B63253781 : Blo 1024605 63253781 := bstep (se 6 (by rfl) ⟨1482510, by rfl⟩ : syracuseStep 63253781 = 2965021) B2965021
theorem B1027367 : Blo 1024605 1027367 := bstep (se 1 (by rfl) ⟨770525, by rfl⟩ : syracuseStep 1027367 = 1541051) B1541051
theorem B1027407 : Blo 1024605 1027407 := bstep (se 1 (by rfl) ⟨770555, by rfl⟩ : syracuseStep 1027407 = 1541111) B1541111
theorem B1027423 : Blo 1024605 1027423 := bstep (se 1 (by rfl) ⟨770567, by rfl⟩ : syracuseStep 1027423 = 1541135) B1541135
theorem B2305385 : Blo 1024605 2305385 := bstep (se 2 (by rfl) ⟨864519, by rfl⟩ : syracuseStep 2305385 = 1729039) B1729039
theorem B1027451 : Blo 1024605 1027451 := bstep (se 1 (by rfl) ⟨770588, by rfl⟩ : syracuseStep 1027451 = 1541177) B1541177
theorem B1027503 : Blo 1024605 1027503 := bstep (se 1 (by rfl) ⟨770627, by rfl⟩ : syracuseStep 1027503 = 1541255) B1541255
theorem B1027527 : Blo 1024605 1027527 := bstep (se 1 (by rfl) ⟨770645, by rfl⟩ : syracuseStep 1027527 = 1541291) B1541291
theorem B7810505 : Blo 1024605 7810505 := bstep (se 2 (by rfl) ⟨2928939, by rfl⟩ : syracuseStep 7810505 = 5857879) B5857879
theorem B1027547 : Blo 1024605 1027547 := bstep (se 1 (by rfl) ⟨770660, by rfl⟩ : syracuseStep 1027547 = 1541321) B1541321
theorem B1027623 : Blo 1024605 1027623 := bstep (se 1 (by rfl) ⟨770717, by rfl⟩ : syracuseStep 1027623 = 1541435) B1541435
theorem B1027663 : Blo 1024605 1027663 := bstep (se 1 (by rfl) ⟨770747, by rfl⟩ : syracuseStep 1027663 = 1541495) B1541495
theorem B1027679 : Blo 1024605 1027679 := bstep (se 1 (by rfl) ⟨770759, by rfl⟩ : syracuseStep 1027679 = 1541519) B1541519
theorem B2600545 : Blo 1024605 2600545 := bstep (se 2 (by rfl) ⟨975204, by rfl⟩ : syracuseStep 2600545 = 1950409) B1950409
theorem B1027707 : Blo 1024605 1027707 := bstep (se 1 (by rfl) ⟨770780, by rfl⟩ : syracuseStep 1027707 = 1541561) B1541561
theorem B1846955 : Blo 1024605 1846955 := bstep (se 1 (by rfl) ⟨1385216, by rfl⟩ : syracuseStep 1846955 = 2770433) B2770433
theorem B1027759 : Blo 1024605 1027759 := bstep (se 1 (by rfl) ⟨770819, by rfl⟩ : syracuseStep 1027759 = 1541639) B1541639
theorem B1027783 : Blo 1024605 1027783 := bstep (se 1 (by rfl) ⟨770837, by rfl⟩ : syracuseStep 1027783 = 1541675) B1541675
theorem B1027803 : Blo 1024605 1027803 := bstep (se 1 (by rfl) ⟨770852, by rfl⟩ : syracuseStep 1027803 = 1541705) B1541705
theorem B1027879 : Blo 1024605 1027879 := bstep (se 1 (by rfl) ⟨770909, by rfl⟩ : syracuseStep 1027879 = 1541819) B1541819
theorem B1027919 : Blo 1024605 1027919 := bstep (se 1 (by rfl) ⟨770939, by rfl⟩ : syracuseStep 1027919 = 1541879) B1541879
theorem B1027935 : Blo 1024605 1027935 := bstep (se 1 (by rfl) ⟨770951, by rfl⟩ : syracuseStep 1027935 = 1541903) B1541903
theorem B1945451 : Blo 1024605 1945451 := bstep (se 1 (by rfl) ⟨1459088, by rfl⟩ : syracuseStep 1945451 = 2918177) B2918177
theorem B1027963 : Blo 1024605 1027963 := bstep (se 1 (by rfl) ⟨770972, by rfl⟩ : syracuseStep 1027963 = 1541945) B1541945
theorem B1028015 : Blo 1024605 1028015 := bstep (se 1 (by rfl) ⟨771011, by rfl⟩ : syracuseStep 1028015 = 1542023) B1542023
theorem B6565819 : Blo 1024605 6565819 := bstep (se 1 (by rfl) ⟨4924364, by rfl⟩ : syracuseStep 6565819 = 9848729) B9848729
theorem B2305979 : Blo 1024605 2305979 := bstep (se 1 (by rfl) ⟨1729484, by rfl⟩ : syracuseStep 2305979 = 3458969) B3458969
theorem B1028039 : Blo 1024605 1028039 := bstep (se 1 (by rfl) ⟨771029, by rfl⟩ : syracuseStep 1028039 = 1542059) B1542059
theorem B1028059 : Blo 1024605 1028059 := bstep (se 1 (by rfl) ⟨771044, by rfl⟩ : syracuseStep 1028059 = 1542089) B1542089
theorem B1847315 : Blo 1024605 1847315 := bstep (se 1 (by rfl) ⟨1385486, by rfl⟩ : syracuseStep 1847315 = 2770973) B2770973
theorem B1028135 : Blo 1024605 1028135 := bstep (se 1 (by rfl) ⟨771101, by rfl⟩ : syracuseStep 1028135 = 1542203) B1542203
theorem B2306105 : Blo 1024605 2306105 := bstep (se 2 (by rfl) ⟨864789, by rfl⟩ : syracuseStep 2306105 = 1729579) B1729579
theorem B1028175 : Blo 1024605 1028175 := bstep (se 1 (by rfl) ⟨771131, by rfl⟩ : syracuseStep 1028175 = 1542263) B1542263
theorem B1028191 : Blo 1024605 1028191 := bstep (se 1 (by rfl) ⟨771143, by rfl⟩ : syracuseStep 1028191 = 1542287) B1542287
theorem B1028219 : Blo 1024605 1028219 := bstep (se 1 (by rfl) ⟨771164, by rfl⟩ : syracuseStep 1028219 = 1542329) B1542329
theorem B3289241 : Blo 1024605 3289241 := bstep (se 2 (by rfl) ⟨1233465, by rfl⟩ : syracuseStep 3289241 = 2466931) B2466931
theorem B1028271 : Blo 1024605 1028271 := bstep (se 1 (by rfl) ⟨771203, by rfl⟩ : syracuseStep 1028271 = 1542407) B1542407
theorem B1028295 : Blo 1024605 1028295 := bstep (se 1 (by rfl) ⟨771221, by rfl⟩ : syracuseStep 1028295 = 1542443) B1542443
theorem B1028315 : Blo 1024605 1028315 := bstep (se 1 (by rfl) ⟨771236, by rfl⟩ : syracuseStep 1028315 = 1542473) B1542473
theorem B1028391 : Blo 1024605 1028391 := bstep (se 1 (by rfl) ⟨771293, by rfl⟩ : syracuseStep 1028391 = 1542587) B1542587
theorem B1028431 : Blo 1024605 1028431 := bstep (se 1 (by rfl) ⟨771323, by rfl⟩ : syracuseStep 1028431 = 1542647) B1542647
theorem B1028447 : Blo 1024605 1028447 := bstep (se 1 (by rfl) ⟨771335, by rfl⟩ : syracuseStep 1028447 = 1542671) B1542671
theorem B5189993 : Blo 1024605 5189993 := bstep (se 2 (by rfl) ⟨1946247, by rfl⟩ : syracuseStep 5189993 = 3892495) B3892495
theorem B1028475 : Blo 1024605 1028475 := bstep (se 1 (by rfl) ⟨771356, by rfl⟩ : syracuseStep 1028475 = 1542713) B1542713
theorem B2306447 : Blo 1024605 2306447 := bstep (se 1 (by rfl) ⟨1729835, by rfl⟩ : syracuseStep 2306447 = 3459671) B3459671
theorem B1028527 : Blo 1024605 1028527 := bstep (se 1 (by rfl) ⟨771395, by rfl⟩ : syracuseStep 1028527 = 1542791) B1542791
theorem B1028551 : Blo 1024605 1028551 := bstep (se 1 (by rfl) ⟨771413, by rfl⟩ : syracuseStep 1028551 = 1542827) B1542827
theorem B1028571 : Blo 1024605 1028571 := bstep (se 1 (by rfl) ⟨771428, by rfl⟩ : syracuseStep 1028571 = 1542857) B1542857
theorem B1946119 : Blo 1024605 1946119 := bstep (se 1 (by rfl) ⟨1459589, by rfl⟩ : syracuseStep 1946119 = 2919179) B2919179
theorem B3289625 : Blo 1024605 3289625 := bstep (se 2 (by rfl) ⟨1233609, by rfl⟩ : syracuseStep 3289625 = 2467219) B2467219
theorem B2601497 : Blo 1024605 2601497 := bstep (se 2 (by rfl) ⟨975561, by rfl⟩ : syracuseStep 2601497 = 1951123) B1951123
theorem B2470439 : Blo 1024605 2470439 := bstep (se 1 (by rfl) ⟨1852829, by rfl⟩ : syracuseStep 2470439 = 3705659) B3705659
theorem B2306771 : Blo 1024605 2306771 := bstep (se 1 (by rfl) ⟨1730078, by rfl⟩ : syracuseStep 2306771 = 3460157) B3460157
theorem B5845715 : Blo 1024605 5845715 := bstep (se 1 (by rfl) ⟨4384286, by rfl⟩ : syracuseStep 5845715 = 8768573) B8768573
theorem B71054093 : Blo 1024605 71054093 := bstep (se 3 (by rfl) ⟨13322642, by rfl⟩ : syracuseStep 71054093 = 26645285) B26645285
theorem B2602003 : Blo 1024605 2602003 := bstep (se 1 (by rfl) ⟨1951502, by rfl⟩ : syracuseStep 2602003 = 3903005) B3903005
theorem B2307707 : Blo 1024605 2307707 := bstep (se 1 (by rfl) ⟨1730780, by rfl⟩ : syracuseStep 2307707 = 3461561) B3461561
theorem B2963083 : Blo 1024605 2963083 := bstep (se 1 (by rfl) ⟨2222312, by rfl⟩ : syracuseStep 2963083 = 4444625) B4444625
theorem B13153985 : Blo 1024605 13153985 := bstep (se 2 (by rfl) ⟨4932744, by rfl⟩ : syracuseStep 13153985 = 9865489) B9865489
theorem B2307833 : Blo 1024605 2307833 := bstep (se 2 (by rfl) ⟨865437, by rfl⟩ : syracuseStep 2307833 = 1730875) B1730875
theorem B23705387 : Blo 1024605 23705387 := bstep (se 1 (by rfl) ⟨17779040, by rfl⟩ : syracuseStep 23705387 = 35558081) B35558081
theorem B2308103 : Blo 1024605 2308103 := bstep (se 1 (by rfl) ⟨1731077, by rfl⟩ : syracuseStep 2308103 = 3462155) B3462155
theorem B3291151 : Blo 1024605 3291151 := bstep (se 1 (by rfl) ⟨2468363, by rfl⟩ : syracuseStep 3291151 = 4936727) B4936727
theorem B2308175 : Blo 1024605 2308175 := bstep (se 1 (by rfl) ⟨1731131, by rfl⟩ : syracuseStep 2308175 = 3462263) B3462263
theorem B2603087 : Blo 1024605 2603087 := bstep (se 1 (by rfl) ⟨1952315, by rfl⟩ : syracuseStep 2603087 = 3904631) B3904631
theorem B8894771 : Blo 1024605 8894771 := bstep (se 1 (by rfl) ⟨6671078, by rfl⟩ : syracuseStep 8894771 = 13342157) B13342157
theorem B2308571 : Blo 1024605 2308571 := bstep (se 1 (by rfl) ⟨1731428, by rfl⟩ : syracuseStep 2308571 = 3462857) B3462857
theorem B1948283 : Blo 1024605 1948283 := bstep (se 1 (by rfl) ⟨1461212, by rfl⟩ : syracuseStep 1948283 = 2922425) B2922425
theorem B2079479 : Blo 1024605 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B1948511 : Blo 1024605 1948511 := bstep (se 1 (by rfl) ⟨1461383, by rfl⟩ : syracuseStep 1948511 = 2922767) B2922767
theorem B426031973 : Blo 1024605 426031973 := bstep (se 4 (by rfl) ⟨39940497, by rfl⟩ : syracuseStep 426031973 = 79880995) B79880995
theorem B2309039 : Blo 1024605 2309039 := bstep (se 1 (by rfl) ⟨1731779, by rfl⟩ : syracuseStep 2309039 = 3463559) B3463559
theorem B1850407 : Blo 1024605 1850407 := bstep (se 1 (by rfl) ⟨1387805, by rfl⟩ : syracuseStep 1850407 = 2775611) B2775611
theorem B1948769 : Blo 1024605 1948769 := bstep (se 2 (by rfl) ⟨730788, by rfl⟩ : syracuseStep 1948769 = 1461577) B1461577
theorem B7388279 : Blo 1024605 7388279 := bstep (se 1 (by rfl) ⟨5541209, by rfl⟩ : syracuseStep 7388279 = 11082419) B11082419
theorem B2309291 : Blo 1024605 2309291 := bstep (se 1 (by rfl) ⟨1731968, by rfl⟩ : syracuseStep 2309291 = 3463937) B3463937
theorem B1949035 : Blo 1024605 1949035 := bstep (se 1 (by rfl) ⟨1461776, by rfl⟩ : syracuseStep 1949035 = 2923553) B2923553
theorem B35569181 : Blo 1024605 35569181 := bstep (se 3 (by rfl) ⟨6669221, by rfl⟩ : syracuseStep 35569181 = 13338443) B13338443
theorem B2309831 : Blo 1024605 2309831 := bstep (se 1 (by rfl) ⟨1732373, by rfl⟩ : syracuseStep 2309831 = 3464747) B3464747
theorem B5259001 : Blo 1024605 5259001 := bstep (se 2 (by rfl) ⟨1972125, by rfl⟩ : syracuseStep 5259001 = 3944251) B3944251
theorem B18759539 : Blo 1024605 18759539 := bstep (se 1 (by rfl) ⟨14069654, by rfl⟩ : syracuseStep 18759539 = 28139309) B28139309
theorem B1753015 : Blo 1024605 1753015 := bstep (se 1 (by rfl) ⟨1314761, by rfl⟩ : syracuseStep 1753015 = 2629523) B2629523
theorem B5554183 : Blo 1024605 5554183 := bstep (se 1 (by rfl) ⟨4165637, by rfl⟩ : syracuseStep 5554183 = 8331275) B8331275
theorem B7028965 : Blo 1024605 7028965 := bstep (se 4 (by rfl) ⟨658965, by rfl⟩ : syracuseStep 7028965 = 1317931) B1317931
theorem B5849405 : Blo 1024605 5849405 := bstep (se 3 (by rfl) ⟨1096763, by rfl⟩ : syracuseStep 5849405 = 2193527) B2193527
theorem B1098079 : Blo 1024605 1098079 := bstep (se 1 (by rfl) ⟨823559, by rfl⟩ : syracuseStep 1098079 = 1647119) B1647119
theorem B8995337 : Blo 1024605 8995337 := bstep (se 2 (by rfl) ⟨3373251, by rfl⟩ : syracuseStep 8995337 = 6746503) B6746503
theorem B1950227 : Blo 1024605 1950227 := bstep (se 1 (by rfl) ⟨1462670, by rfl⟩ : syracuseStep 1950227 = 2925341) B2925341
theorem B2310695 : Blo 1024605 2310695 := bstep (se 1 (by rfl) ⟨1733021, by rfl⟩ : syracuseStep 2310695 = 3466043) B3466043
theorem B1851943 : Blo 1024605 1851943 := bstep (se 1 (by rfl) ⟨1388957, by rfl⟩ : syracuseStep 1851943 = 2777915) B2777915
theorem B3556055 : Blo 1024605 3556055 := bstep (se 1 (by rfl) ⟨2667041, by rfl⟩ : syracuseStep 3556055 = 5334083) B5334083
theorem B1950455 : Blo 1024605 1950455 := bstep (se 1 (by rfl) ⟨1462841, by rfl⟩ : syracuseStep 1950455 = 2925683) B2925683
theorem B2311019 : Blo 1024605 2311019 := bstep (se 1 (by rfl) ⟨1733264, by rfl⟩ : syracuseStep 2311019 = 3466529) B3466529
theorem B2311073 : Blo 1024605 2311073 := bstep (se 2 (by rfl) ⟨866652, by rfl⟩ : syracuseStep 2311073 = 1733305) B1733305
theorem B3458105 : Blo 1024605 3458105 := bstep (se 2 (by rfl) ⟨1296789, by rfl⟩ : syracuseStep 3458105 = 2593579) B2593579
theorem B2311415 : Blo 1024605 2311415 := bstep (se 1 (by rfl) ⟨1733561, by rfl⟩ : syracuseStep 2311415 = 3467123) B3467123
theorem B1459561 : Blo 1024605 1459561 := bstep (se 2 (by rfl) ⟨547335, by rfl⟩ : syracuseStep 1459561 = 1094671) B1094671
theorem B3458429 : Blo 1024605 3458429 := bstep (se 3 (by rfl) ⟨648455, by rfl⟩ : syracuseStep 3458429 = 1296911) B1296911
theorem B2082235 : Blo 1024605 2082235 := bstep (se 1 (by rfl) ⟨1561676, by rfl⟩ : syracuseStep 2082235 = 3123353) B3123353
theorem B3458699 : Blo 1024605 3458699 := bstep (se 1 (by rfl) ⟨2594024, by rfl⟩ : syracuseStep 3458699 = 5188049) B5188049
theorem B2312009 : Blo 1024605 2312009 := bstep (se 2 (by rfl) ⟨867003, by rfl⟩ : syracuseStep 2312009 = 1734007) B1734007
theorem B11847629 : Blo 1024605 11847629 := bstep (se 3 (by rfl) ⟨2221430, by rfl⟩ : syracuseStep 11847629 = 4442861) B4442861
theorem B15190105 : Blo 1024605 15190105 := bstep (se 2 (by rfl) ⟨5696289, by rfl⟩ : syracuseStep 15190105 = 11392579) B11392579
theorem B1951867 : Blo 1024605 1951867 := bstep (se 1 (by rfl) ⟨1463900, by rfl⟩ : syracuseStep 1951867 = 2927801) B2927801
theorem B4933975 : Blo 1024605 4933975 := bstep (se 1 (by rfl) ⟨3700481, by rfl⟩ : syracuseStep 4933975 = 7400963) B7400963
theorem B1952095 : Blo 1024605 1952095 := bstep (se 1 (by rfl) ⟨1464071, by rfl⟩ : syracuseStep 1952095 = 2928143) B2928143
theorem B3459617 : Blo 1024605 3459617 := bstep (se 2 (by rfl) ⟨1297356, by rfl⟩ : syracuseStep 3459617 = 2594713) B2594713
theorem B1231399 : Blo 1024605 1231399 := bstep (se 1 (by rfl) ⟨923549, by rfl⟩ : syracuseStep 1231399 = 1847099) B1847099
theorem B2312801 : Blo 1024605 2312801 := bstep (se 2 (by rfl) ⟨867300, by rfl⟩ : syracuseStep 2312801 = 1734601) B1734601
theorem B1952353 : Blo 1024605 1952353 := bstep (se 2 (by rfl) ⟨732132, by rfl⟩ : syracuseStep 1952353 = 1464265) B1464265
theorem B2771579 : Blo 1024605 2771579 := bstep (se 1 (by rfl) ⟨2078684, by rfl⟩ : syracuseStep 2771579 = 4157369) B4157369
theorem B5196473 : Blo 1024605 5196473 := bstep (se 2 (by rfl) ⟨1948677, by rfl⟩ : syracuseStep 5196473 = 3897355) B3897355
theorem B3459833 : Blo 1024605 3459833 := bstep (se 2 (by rfl) ⟨1297437, by rfl⟩ : syracuseStep 3459833 = 2594875) B2594875
theorem B1952687 : Blo 1024605 1952687 := bstep (se 1 (by rfl) ⟨1464515, by rfl⟩ : syracuseStep 1952687 = 2929031) B2929031
theorem B2313143 : Blo 1024605 2313143 := bstep (se 1 (by rfl) ⟨1734857, by rfl⟩ : syracuseStep 2313143 = 3469715) B3469715
theorem B3460103 : Blo 1024605 3460103 := bstep (se 1 (by rfl) ⟨2595077, by rfl⟩ : syracuseStep 3460103 = 5190155) B5190155
theorem B8309803 : Blo 1024605 8309803 := bstep (se 1 (by rfl) ⟨6232352, by rfl⟩ : syracuseStep 8309803 = 12464705) B12464705
theorem B3460211 : Blo 1024605 3460211 := bstep (se 1 (by rfl) ⟨2595158, by rfl⟩ : syracuseStep 3460211 = 5190317) B5190317
theorem B13028525 : Blo 1024605 13028525 := bstep (se 3 (by rfl) ⟨2442848, by rfl⟩ : syracuseStep 13028525 = 4885697) B4885697
theorem B7785719 : Blo 1024605 7785719 := bstep (se 1 (by rfl) ⟨5839289, by rfl⟩ : syracuseStep 7785719 = 11678579) B11678579
theorem B1461611 : Blo 1024605 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B3460481 : Blo 1024605 3460481 := bstep (se 2 (by rfl) ⟨1297680, by rfl⟩ : syracuseStep 3460481 = 2595361) B2595361
theorem B1297883 : Blo 1024605 1297883 := bstep (se 1 (by rfl) ⟨973412, by rfl⟩ : syracuseStep 1297883 = 1946825) B1946825
theorem B2313737 : Blo 1024605 2313737 := bstep (se 2 (by rfl) ⟨867651, by rfl⟩ : syracuseStep 2313737 = 1735303) B1735303
theorem B7786205 : Blo 1024605 7786205 := bstep (se 3 (by rfl) ⟨1459913, by rfl⟩ : syracuseStep 7786205 = 2919827) B2919827
theorem B5263147 : Blo 1024605 5263147 := bstep (se 1 (by rfl) ⟨3947360, by rfl⟩ : syracuseStep 5263147 = 7894721) B7894721
theorem B2314079 : Blo 1024605 2314079 := bstep (se 1 (by rfl) ⟨1735559, by rfl⟩ : syracuseStep 2314079 = 3471119) B3471119
theorem B1298359 : Blo 1024605 1298359 := bstep (se 1 (by rfl) ⟨973769, by rfl⟩ : syracuseStep 1298359 = 1947539) B1947539
theorem B2314259 : Blo 1024605 2314259 := bstep (se 1 (by rfl) ⟨1735694, by rfl⟩ : syracuseStep 2314259 = 3471389) B3471389
theorem B3461291 : Blo 1024605 3461291 := bstep (se 1 (by rfl) ⟨2595968, by rfl⟩ : syracuseStep 3461291 = 5191937) B5191937
theorem B1757627 : Blo 1024605 1757627 := bstep (se 1 (by rfl) ⟨1318220, by rfl⟩ : syracuseStep 1757627 = 2636441) B2636441
theorem B3461831 : Blo 1024605 3461831 := bstep (se 1 (by rfl) ⟨2596373, by rfl⟩ : syracuseStep 3461831 = 5192747) B5192747
theorem B9851651 : Blo 1024605 9851651 := bstep (se 1 (by rfl) ⟨7388738, by rfl⟩ : syracuseStep 9851651 = 14777477) B14777477
theorem B7492355 : Blo 1024605 7492355 := bstep (se 1 (by rfl) ⟨5619266, by rfl⟩ : syracuseStep 7492355 = 11238533) B11238533
theorem B1299655 : Blo 1024605 1299655 := bstep (se 1 (by rfl) ⟨974741, by rfl⟩ : syracuseStep 1299655 = 1949483) B1949483
theorem B3462695 : Blo 1024605 3462695 := bstep (se 1 (by rfl) ⟨2597021, by rfl⟩ : syracuseStep 3462695 = 5194043) B5194043
theorem B3462803 : Blo 1024605 3462803 := bstep (se 1 (by rfl) ⟨2597102, by rfl⟩ : syracuseStep 3462803 = 5194205) B5194205
theorem B3463019 : Blo 1024605 3463019 := bstep (se 1 (by rfl) ⟨2597264, by rfl⟩ : syracuseStep 3463019 = 5194529) B5194529
theorem B3463073 : Blo 1024605 3463073 := bstep (se 2 (by rfl) ⟨1298652, by rfl⟩ : syracuseStep 3463073 = 2597305) B2597305
theorem B3463667 : Blo 1024605 3463667 := bstep (se 1 (by rfl) ⟨2597750, by rfl⟩ : syracuseStep 3463667 = 5195501) B5195501
theorem B26270243 : Blo 1024605 26270243 := bstep (se 1 (by rfl) ⟨19702682, by rfl⟩ : syracuseStep 26270243 = 39405365) B39405365
theorem B2775991 : Blo 1024605 2775991 := bstep (se 1 (by rfl) ⟨2081993, by rfl⟩ : syracuseStep 2775991 = 4163987) B4163987
theorem B3955643 : Blo 1024605 3955643 := bstep (se 1 (by rfl) ⟨2966732, by rfl⟩ : syracuseStep 3955643 = 5933465) B5933465
theorem B5266433 : Blo 1024605 5266433 := bstep (se 2 (by rfl) ⟨1974912, by rfl⟩ : syracuseStep 5266433 = 3949825) B3949825
theorem B3464207 : Blo 1024605 3464207 := bstep (se 1 (by rfl) ⟨2598155, by rfl⟩ : syracuseStep 3464207 = 5196311) B5196311
theorem B7396555 : Blo 1024605 7396555 := bstep (se 1 (by rfl) ⟨5547416, by rfl⟩ : syracuseStep 7396555 = 11094833) B11094833
theorem B7396697 : Blo 1024605 7396697 := bstep (se 2 (by rfl) ⟨2773761, by rfl⟩ : syracuseStep 7396697 = 5547523) B5547523
theorem B3890537 : Blo 1024605 3890537 := bstep (se 2 (by rfl) ⟨1458951, by rfl⟩ : syracuseStep 3890537 = 2917903) B2917903
theorem B17522243 : Blo 1024605 17522243 := bstep (se 1 (by rfl) ⟨13141682, by rfl⟩ : syracuseStep 17522243 = 26283365) B26283365
theorem B3464801 : Blo 1024605 3464801 := bstep (se 2 (by rfl) ⟨1299300, by rfl⟩ : syracuseStep 3464801 = 2598601) B2598601
theorem B5201657 : Blo 1024605 5201657 := bstep (se 2 (by rfl) ⟨1950621, by rfl⟩ : syracuseStep 5201657 = 3901243) B3901243
theorem B19750661 : Blo 1024605 19750661 := bstep (se 4 (by rfl) ⟨1851624, by rfl⟩ : syracuseStep 19750661 = 3703249) B3703249
theorem B252731339 : Blo 1024605 252731339 := bstep (se 1 (by rfl) ⟨189548504, by rfl⟩ : syracuseStep 252731339 = 379097009) B379097009
theorem B6578405 : Blo 1024605 6578405 := bstep (se 4 (by rfl) ⟨616725, by rfl⟩ : syracuseStep 6578405 = 1233451) B1233451
theorem B5202305 : Blo 1024605 5202305 := bstep (se 2 (by rfl) ⟨1950864, by rfl⟩ : syracuseStep 5202305 = 3901729) B3901729
theorem B1729147 : Blo 1024605 1729147 := bstep (se 1 (by rfl) ⟨1296860, by rfl⟩ : syracuseStep 1729147 = 2593721) B2593721
theorem B7037725 : Blo 1024605 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B4219715 : Blo 1024605 4219715 := bstep (se 1 (by rfl) ⟨3164786, by rfl⟩ : syracuseStep 4219715 = 6329573) B6329573
theorem B1041247 : Blo 1024605 1041247 := bstep (se 1 (by rfl) ⟨780935, by rfl⟩ : syracuseStep 1041247 = 1561871) B1561871
theorem B2778043 : Blo 1024605 2778043 := bstep (se 1 (by rfl) ⟨2083532, by rfl⟩ : syracuseStep 2778043 = 4167065) B4167065
theorem B33743891 : Blo 1024605 33743891 := bstep (se 1 (by rfl) ⟨25307918, by rfl⟩ : syracuseStep 33743891 = 50615837) B50615837
theorem B3466259 : Blo 1024605 3466259 := bstep (se 1 (by rfl) ⟨2599694, by rfl⟩ : syracuseStep 3466259 = 5199389) B5199389
theorem B5203115 : Blo 1024605 5203115 := bstep (se 1 (by rfl) ⟨3902336, by rfl⟩ : syracuseStep 5203115 = 7804673) B7804673
theorem B3466583 : Blo 1024605 3466583 := bstep (se 1 (by rfl) ⟨2599937, by rfl⟩ : syracuseStep 3466583 = 5199875) B5199875
theorem B108291491 : Blo 1024605 108291491 := bstep (se 1 (by rfl) ⟨81218618, by rfl⟩ : syracuseStep 108291491 = 162437237) B162437237
theorem B7792037 : Blo 1024605 7792037 := bstep (se 4 (by rfl) ⟨730503, by rfl⟩ : syracuseStep 7792037 = 1461007) B1461007
theorem B1730011 : Blo 1024605 1730011 := bstep (se 1 (by rfl) ⟨1297508, by rfl⟩ : syracuseStep 1730011 = 2595017) B2595017
theorem B10446299 : Blo 1024605 10446299 := bstep (se 1 (by rfl) ⟨7834724, by rfl⟩ : syracuseStep 10446299 = 15669449) B15669449
theorem B3892769 : Blo 1024605 3892769 := bstep (se 2 (by rfl) ⟨1459788, by rfl⟩ : syracuseStep 3892769 = 2919577) B2919577
theorem B5203601 : Blo 1024605 5203601 := bstep (se 2 (by rfl) ⟨1951350, by rfl⟩ : syracuseStep 5203601 = 3902701) B3902701
theorem B9856727 : Blo 1024605 9856727 := bstep (se 1 (by rfl) ⟨7392545, by rfl⟩ : syracuseStep 9856727 = 14785091) B14785091
theorem B3893255 : Blo 1024605 3893255 := bstep (se 1 (by rfl) ⟨2919941, by rfl⟩ : syracuseStep 3893255 = 5839883) B5839883
theorem B1730639 : Blo 1024605 1730639 := bstep (se 1 (by rfl) ⟨1297979, by rfl⟩ : syracuseStep 1730639 = 2595959) B2595959
theorem B8907059 : Blo 1024605 8907059 := bstep (se 1 (by rfl) ⟨6680294, by rfl⟩ : syracuseStep 8907059 = 13360589) B13360589
theorem B3697021 : Blo 1024605 3697021 := bstep (se 3 (by rfl) ⟨693191, by rfl⟩ : syracuseStep 3697021 = 1386383) B1386383
theorem B3467663 : Blo 1024605 3467663 := bstep (se 1 (by rfl) ⟨2600747, by rfl⟩ : syracuseStep 3467663 = 5201495) B5201495
theorem B3893741 : Blo 1024605 3893741 := bstep (se 3 (by rfl) ⟨730076, by rfl⟩ : syracuseStep 3893741 = 1460153) B1460153
theorem B3467987 : Blo 1024605 3467987 := bstep (se 1 (by rfl) ⟨2600990, by rfl⟩ : syracuseStep 3467987 = 5201981) B5201981
theorem B13200101 : Blo 1024605 13200101 := bstep (se 4 (by rfl) ⟨1237509, by rfl⟩ : syracuseStep 13200101 = 2475019) B2475019
theorem B1731503 : Blo 1024605 1731503 := bstep (se 1 (by rfl) ⟨1298627, by rfl⟩ : syracuseStep 1731503 = 2597255) B2597255
theorem B3894425 : Blo 1024605 3894425 := bstep (se 2 (by rfl) ⟨1460409, by rfl⟩ : syracuseStep 3894425 = 2920819) B2920819
theorem B1731935 : Blo 1024605 1731935 := bstep (se 1 (by rfl) ⟨1298951, by rfl⟩ : syracuseStep 1731935 = 2597903) B2597903
theorem B5205869 : Blo 1024605 5205869 := bstep (se 3 (by rfl) ⟨976100, by rfl⟩ : syracuseStep 5205869 = 1952201) B1952201
theorem B3698551 : Blo 1024605 3698551 := bstep (se 1 (by rfl) ⟨2773913, by rfl⟩ : syracuseStep 3698551 = 5547827) B5547827
theorem B3469175 : Blo 1024605 3469175 := bstep (se 1 (by rfl) ⟨2601881, by rfl⟩ : syracuseStep 3469175 = 5203763) B5203763
theorem B1732495 : Blo 1024605 1732495 := bstep (se 1 (by rfl) ⟨1299371, by rfl⟩ : syracuseStep 1732495 = 2598743) B2598743
theorem B7401401 : Blo 1024605 7401401 := bstep (se 2 (by rfl) ⟨2775525, by rfl⟩ : syracuseStep 7401401 = 5551051) B5551051
theorem B2191367 : Blo 1024605 2191367 := bstep (se 1 (by rfl) ⟨1643525, by rfl⟩ : syracuseStep 2191367 = 3287051) B3287051
theorem B5206031 : Blo 1024605 5206031 := bstep (se 1 (by rfl) ⟨3904523, by rfl⟩ : syracuseStep 5206031 = 7809047) B7809047
theorem B3469391 : Blo 1024605 3469391 := bstep (se 1 (by rfl) ⟨2602043, by rfl⟩ : syracuseStep 3469391 = 5204087) B5204087
theorem B3895411 : Blo 1024605 3895411 := bstep (se 1 (by rfl) ⟨2921558, by rfl⟩ : syracuseStep 3895411 = 5843117) B5843117
theorem B25293005 : Blo 1024605 25293005 := bstep (se 3 (by rfl) ⟨4742438, by rfl⟩ : syracuseStep 25293005 = 9484877) B9484877
theorem B3469769 : Blo 1024605 3469769 := bstep (se 2 (by rfl) ⟨1301163, by rfl⟩ : syracuseStep 3469769 = 2602327) B2602327
theorem B13332995 : Blo 1024605 13332995 := bstep (se 1 (by rfl) ⟨9999746, by rfl⟩ : syracuseStep 13332995 = 19999493) B19999493
theorem B11694617 : Blo 1024605 11694617 := bstep (se 2 (by rfl) ⟨4385481, by rfl⟩ : syracuseStep 11694617 = 8770963) B8770963
theorem B1733177 : Blo 1024605 1733177 := bstep (se 2 (by rfl) ⟨649941, by rfl⟩ : syracuseStep 1733177 = 1299883) B1299883
theorem B3470039 : Blo 1024605 3470039 := bstep (se 1 (by rfl) ⟨2602529, by rfl⟩ : syracuseStep 3470039 = 5205059) B5205059
theorem B11268881 : Blo 1024605 11268881 := bstep (se 2 (by rfl) ⟨4225830, by rfl⟩ : syracuseStep 11268881 = 8451661) B8451661
theorem B3896171 : Blo 1024605 3896171 := bstep (se 1 (by rfl) ⟨2922128, by rfl⟩ : syracuseStep 3896171 = 5844257) B5844257
theorem B3470255 : Blo 1024605 3470255 := bstep (se 1 (by rfl) ⟨2602691, by rfl⟩ : syracuseStep 3470255 = 5205383) B5205383
theorem B4387841 : Blo 1024605 4387841 := bstep (se 2 (by rfl) ⟨1645440, by rfl⟩ : syracuseStep 4387841 = 3290881) B3290881
theorem B1537103 : Blo 1024605 1537103 := bstep (se 1 (by rfl) ⟨1152827, by rfl⟩ : syracuseStep 1537103 = 2305655) B2305655
theorem B3339379 : Blo 1024605 3339379 := bstep (se 1 (by rfl) ⟨2504534, by rfl⟩ : syracuseStep 3339379 = 5009069) B5009069
theorem B1537223 : Blo 1024605 1537223 := bstep (se 1 (by rfl) ⟨1152917, by rfl⟩ : syracuseStep 1537223 = 2305835) B2305835
theorem B1733879 : Blo 1024605 1733879 := bstep (se 1 (by rfl) ⟨1300409, by rfl⟩ : syracuseStep 1733879 = 2600819) B2600819
theorem B28112143 : Blo 1024605 28112143 := bstep (se 1 (by rfl) ⟨21084107, by rfl⟩ : syracuseStep 28112143 = 42168215) B42168215
theorem B1537385 : Blo 1024605 1537385 := bstep (se 2 (by rfl) ⟨576519, by rfl⟩ : syracuseStep 1537385 = 1153039) B1153039
theorem B1537463 : Blo 1024605 1537463 := bstep (se 1 (by rfl) ⟨1153097, by rfl⟩ : syracuseStep 1537463 = 2306195) B2306195
theorem B1537499 : Blo 1024605 1537499 := bstep (se 1 (by rfl) ⟨1153124, by rfl⟩ : syracuseStep 1537499 = 2306249) B2306249
theorem B1734223 : Blo 1024605 1734223 := bstep (se 1 (by rfl) ⟨1300667, by rfl⟩ : syracuseStep 1734223 = 2601335) B2601335
theorem B1734473 : Blo 1024605 1734473 := bstep (se 2 (by rfl) ⟨650427, by rfl⟩ : syracuseStep 1734473 = 1300855) B1300855
theorem B1537967 : Blo 1024605 1537967 := bstep (se 1 (by rfl) ⟨1153475, by rfl⟩ : syracuseStep 1537967 = 2306951) B2306951
theorem B3700655 : Blo 1024605 3700655 := bstep (se 1 (by rfl) ⟨2775491, by rfl⟩ : syracuseStep 3700655 = 5550983) B5550983
theorem B6584273 : Blo 1024605 6584273 := bstep (se 2 (by rfl) ⟨2469102, by rfl⟩ : syracuseStep 6584273 = 4938205) B4938205
theorem B1538057 : Blo 1024605 1538057 := bstep (se 2 (by rfl) ⟨576771, by rfl⟩ : syracuseStep 1538057 = 1153543) B1153543
theorem B1538087 : Blo 1024605 1538087 := bstep (se 1 (by rfl) ⟨1153565, by rfl⟩ : syracuseStep 1538087 = 2307131) B2307131
theorem B1669177 : Blo 1024605 1669177 := bstep (se 2 (by rfl) ⟨625941, by rfl⟩ : syracuseStep 1669177 = 1251883) B1251883
theorem B1538171 : Blo 1024605 1538171 := bstep (se 1 (by rfl) ⟨1153628, by rfl⟩ : syracuseStep 1538171 = 2307257) B2307257
theorem B1538297 : Blo 1024605 1538297 := bstep (se 2 (by rfl) ⟨576861, by rfl⟩ : syracuseStep 1538297 = 1153723) B1153723
theorem B1734905 : Blo 1024605 1734905 := bstep (se 2 (by rfl) ⟨650589, by rfl⟩ : syracuseStep 1734905 = 1301179) B1301179
theorem B1538399 : Blo 1024605 1538399 := bstep (se 1 (by rfl) ⟨1153799, by rfl⟩ : syracuseStep 1538399 = 2307599) B2307599
theorem B1538411 : Blo 1024605 1538411 := bstep (se 1 (by rfl) ⟨1153808, by rfl⟩ : syracuseStep 1538411 = 2307617) B2307617
theorem B8321413 : Blo 1024605 8321413 := bstep (se 4 (by rfl) ⟨780132, by rfl⟩ : syracuseStep 8321413 = 1560265) B1560265
theorem B1735087 : Blo 1024605 1735087 := bstep (se 1 (by rfl) ⟨1301315, by rfl⟩ : syracuseStep 1735087 = 2602631) B2602631
theorem B1735175 : Blo 1024605 1735175 := bstep (se 1 (by rfl) ⟨1301381, by rfl⟩ : syracuseStep 1735175 = 2602763) B2602763
theorem B1538639 : Blo 1024605 1538639 := bstep (se 1 (by rfl) ⟨1153979, by rfl⟩ : syracuseStep 1538639 = 2307959) B2307959
theorem B7797383 : Blo 1024605 7797383 := bstep (se 1 (by rfl) ⟨5848037, by rfl⟩ : syracuseStep 7797383 = 11696075) B11696075
theorem B5634695 : Blo 1024605 5634695 := bstep (se 1 (by rfl) ⟨4226021, by rfl⟩ : syracuseStep 5634695 = 8452043) B8452043
theorem B1538759 : Blo 1024605 1538759 := bstep (se 1 (by rfl) ⟨1154069, by rfl⟩ : syracuseStep 1538759 = 2308139) B2308139
theorem B1735519 : Blo 1024605 1735519 := bstep (se 1 (by rfl) ⟨1301639, by rfl⟩ : syracuseStep 1735519 = 2603279) B2603279
theorem B1538921 : Blo 1024605 1538921 := bstep (se 2 (by rfl) ⟨577095, by rfl⟩ : syracuseStep 1538921 = 1154191) B1154191
theorem B1538999 : Blo 1024605 1538999 := bstep (se 1 (by rfl) ⟨1154249, by rfl⟩ : syracuseStep 1538999 = 2308499) B2308499
theorem B1735607 : Blo 1024605 1735607 := bstep (se 1 (by rfl) ⟨1301705, by rfl⟩ : syracuseStep 1735607 = 2603411) B2603411
theorem B1539035 : Blo 1024605 1539035 := bstep (se 1 (by rfl) ⟨1154276, by rfl⟩ : syracuseStep 1539035 = 2308553) B2308553
theorem B14777423 : Blo 1024605 14777423 := bstep (se 1 (by rfl) ⟨11083067, by rfl⟩ : syracuseStep 14777423 = 22166135) B22166135
theorem B8781047 : Blo 1024605 8781047 := bstep (se 1 (by rfl) ⟨6585785, by rfl⟩ : syracuseStep 8781047 = 13171571) B13171571
theorem B11697533 : Blo 1024605 11697533 := bstep (se 3 (by rfl) ⟨2193287, by rfl⟩ : syracuseStep 11697533 = 4386575) B4386575
theorem B1539503 : Blo 1024605 1539503 := bstep (se 1 (by rfl) ⟨1154627, by rfl⟩ : syracuseStep 1539503 = 2309255) B2309255
theorem B1539593 : Blo 1024605 1539593 := bstep (se 2 (by rfl) ⟨577347, by rfl⟩ : syracuseStep 1539593 = 1154695) B1154695
theorem B1539623 : Blo 1024605 1539623 := bstep (se 1 (by rfl) ⟨1154717, by rfl⟩ : syracuseStep 1539623 = 2309435) B2309435
theorem B1539707 : Blo 1024605 1539707 := bstep (se 1 (by rfl) ⟨1154780, by rfl⟩ : syracuseStep 1539707 = 2309561) B2309561
theorem B11107979 : Blo 1024605 11107979 := bstep (se 1 (by rfl) ⟨8330984, by rfl⟩ : syracuseStep 11107979 = 16661969) B16661969
theorem B1539833 : Blo 1024605 1539833 := bstep (se 2 (by rfl) ⟨577437, by rfl⟩ : syracuseStep 1539833 = 1154875) B1154875
theorem B3702557 : Blo 1024605 3702557 := bstep (se 3 (by rfl) ⟨694229, by rfl⟩ : syracuseStep 3702557 = 1388459) B1388459
theorem B1539935 : Blo 1024605 1539935 := bstep (se 1 (by rfl) ⟨1154951, by rfl⟩ : syracuseStep 1539935 = 2309903) B2309903
theorem B1539947 : Blo 1024605 1539947 := bstep (se 1 (by rfl) ⟨1154960, by rfl⟩ : syracuseStep 1539947 = 2309921) B2309921
theorem B7405577 : Blo 1024605 7405577 := bstep (se 2 (by rfl) ⟨2777091, by rfl⟩ : syracuseStep 7405577 = 5554183) B5554183
theorem B5636105 : Blo 1024605 5636105 := bstep (se 2 (by rfl) ⟨2113539, by rfl⟩ : syracuseStep 5636105 = 4227079) B4227079
theorem B79953965 : Blo 1024605 79953965 := bstep (se 3 (by rfl) ⟨14991368, by rfl⟩ : syracuseStep 79953965 = 29982737) B29982737
theorem B2195561 : Blo 1024605 2195561 := bstep (se 2 (by rfl) ⟨823335, by rfl⟩ : syracuseStep 2195561 = 1646671) B1646671
theorem B3899603 : Blo 1024605 3899603 := bstep (se 1 (by rfl) ⟨2924702, by rfl⟩ : syracuseStep 3899603 = 5849405) B5849405
theorem B1540361 : Blo 1024605 1540361 := bstep (se 2 (by rfl) ⟨577635, by rfl⟩ : syracuseStep 1540361 = 1155271) B1155271
theorem B9371953 : Blo 1024605 9371953 := bstep (se 2 (by rfl) ⟨3514482, by rfl⟩ : syracuseStep 9371953 = 7028965) B7028965
theorem B5996891 : Blo 1024605 5996891 := bstep (se 1 (by rfl) ⟨4497668, by rfl⟩ : syracuseStep 5996891 = 8995337) B8995337
theorem B1540463 : Blo 1024605 1540463 := bstep (se 1 (by rfl) ⟨1155347, by rfl⟩ : syracuseStep 1540463 = 2310695) B2310695
theorem B1540679 : Blo 1024605 1540679 := bstep (se 1 (by rfl) ⟨1155509, by rfl⟩ : syracuseStep 1540679 = 2311019) B2311019
theorem B1540715 : Blo 1024605 1540715 := bstep (se 1 (by rfl) ⟨1155536, by rfl⟩ : syracuseStep 1540715 = 2311073) B2311073
theorem B1540943 : Blo 1024605 1540943 := bstep (se 1 (by rfl) ⟨1155707, by rfl⟩ : syracuseStep 1540943 = 2311415) B2311415
theorem B1541339 : Blo 1024605 1541339 := bstep (se 1 (by rfl) ⟨1156004, by rfl⟩ : syracuseStep 1541339 = 2312009) B2312009
theorem B3704057 : Blo 1024605 3704057 := bstep (se 2 (by rfl) ⟨1389021, by rfl⟩ : syracuseStep 3704057 = 2778043) B2778043
theorem B7898419 : Blo 1024605 7898419 := bstep (se 1 (by rfl) ⟨5923814, by rfl⟩ : syracuseStep 7898419 = 11847629) B11847629
theorem B1541513 : Blo 1024605 1541513 := bstep (se 2 (by rfl) ⟨578067, by rfl⟩ : syracuseStep 1541513 = 1156135) B1156135
theorem B6587837 : Blo 1024605 6587837 := bstep (se 3 (by rfl) ⟨1235219, by rfl⟩ : syracuseStep 6587837 = 2470439) B2470439
theorem B1541867 : Blo 1024605 1541867 := bstep (se 1 (by rfl) ⟨1156400, by rfl⟩ : syracuseStep 1541867 = 2312801) B2312801
theorem B1542095 : Blo 1024605 1542095 := bstep (se 1 (by rfl) ⟨1156571, by rfl⟩ : syracuseStep 1542095 = 2313143) B2313143
theorem B8685683 : Blo 1024605 8685683 := bstep (se 1 (by rfl) ⟨6514262, by rfl⟩ : syracuseStep 8685683 = 13028525) B13028525
theorem B1542491 : Blo 1024605 1542491 := bstep (se 1 (by rfl) ⟨1156868, by rfl⟩ : syracuseStep 1542491 = 2313737) B2313737
theorem B1542719 : Blo 1024605 1542719 := bstep (se 1 (by rfl) ⟨1157039, by rfl⟩ : syracuseStep 1542719 = 2314079) B2314079
theorem B1542839 : Blo 1024605 1542839 := bstep (se 1 (by rfl) ⟨1157129, by rfl⟩ : syracuseStep 1542839 = 2314259) B2314259
theorem B20253473 : Blo 1024605 20253473 := bstep (se 2 (by rfl) ⟨7595052, by rfl⟩ : syracuseStep 20253473 = 15190105) B15190105
theorem B1641865 : Blo 1024605 1641865 := bstep (se 2 (by rfl) ⟨615699, by rfl⟩ : syracuseStep 1641865 = 1231399) B1231399
theorem B1642295 : Blo 1024605 1642295 := bstep (se 1 (by rfl) ⟨1231721, by rfl⟩ : syracuseStep 1642295 = 2463443) B2463443
theorem B11079737 : Blo 1024605 11079737 := bstep (se 2 (by rfl) ⟨4154901, by rfl⟩ : syracuseStep 11079737 = 8309803) B8309803
theorem B17535365 : Blo 1024605 17535365 := bstep (se 4 (by rfl) ⟨1643940, by rfl⟩ : syracuseStep 17535365 = 3287881) B3287881
theorem B3510955 : Blo 1024605 3510955 := bstep (se 1 (by rfl) ⟨2633216, by rfl⟩ : syracuseStep 3510955 = 5266433) B5266433
theorem B2593691 : Blo 1024605 2593691 := bstep (se 1 (by rfl) ⟨1945268, by rfl⟩ : syracuseStep 2593691 = 3890537) B3890537
theorem B7017529 : Blo 1024605 7017529 := bstep (se 2 (by rfl) ⟨2631573, by rfl⟩ : syracuseStep 7017529 = 5263147) B5263147
theorem B8754425 : Blo 1024605 8754425 := bstep (se 2 (by rfl) ⟨3282909, by rfl⟩ : syracuseStep 8754425 = 6565819) B6565819
theorem B9868837 : Blo 1024605 9868837 := bstep (se 4 (by rfl) ⟨925203, by rfl⟩ : syracuseStep 9868837 = 1850407) B1850407
theorem B2594825 : Blo 1024605 2594825 := bstep (se 2 (by rfl) ⟨973059, by rfl⟩ : syracuseStep 2594825 = 1946119) B1946119
theorem B72194327 : Blo 1024605 72194327 := bstep (se 1 (by rfl) ⟨54145745, by rfl⟩ : syracuseStep 72194327 = 108291491) B108291491
theorem B2595179 : Blo 1024605 2595179 := bstep (se 1 (by rfl) ⟨1946384, by rfl⟩ : syracuseStep 2595179 = 3892769) B3892769
theorem B2595503 : Blo 1024605 2595503 := bstep (se 1 (by rfl) ⟨1946627, by rfl⟩ : syracuseStep 2595503 = 3893255) B3893255
theorem B1153759 : Blo 1024605 1153759 := bstep (se 1 (by rfl) ⟨865319, by rfl⟩ : syracuseStep 1153759 = 1730639) B1730639
theorem B5938039 : Blo 1024605 5938039 := bstep (se 1 (by rfl) ⟨4453529, by rfl⟩ : syracuseStep 5938039 = 8907059) B8907059
theorem B1645543 : Blo 1024605 1645543 := bstep (se 1 (by rfl) ⟨1234157, by rfl⟩ : syracuseStep 1645543 = 2468315) B2468315
theorem B2595827 : Blo 1024605 2595827 := bstep (se 1 (by rfl) ⟨1946870, by rfl⟩ : syracuseStep 2595827 = 3893741) B3893741
theorem B1154335 : Blo 1024605 1154335 := bstep (se 1 (by rfl) ⟨865751, by rfl⟩ : syracuseStep 1154335 = 1731503) B1731503
theorem B2596283 : Blo 1024605 2596283 := bstep (se 1 (by rfl) ⟨1947212, by rfl⟩ : syracuseStep 2596283 = 3894425) B3894425
theorem B1154623 : Blo 1024605 1154623 := bstep (se 1 (by rfl) ⟨865967, by rfl⟩ : syracuseStep 1154623 = 1731935) B1731935
theorem B8888663 : Blo 1024605 8888663 := bstep (se 1 (by rfl) ⟨6666497, by rfl⟩ : syracuseStep 8888663 = 13332995) B13332995
theorem B1155451 : Blo 1024605 1155451 := bstep (se 1 (by rfl) ⟨866588, by rfl⟩ : syracuseStep 1155451 = 1733177) B1733177
theorem B7512587 : Blo 1024605 7512587 := bstep (se 1 (by rfl) ⟨5634440, by rfl⟩ : syracuseStep 7512587 = 11268881) B11268881
theorem B2597447 : Blo 1024605 2597447 := bstep (se 1 (by rfl) ⟨1948085, by rfl⟩ : syracuseStep 2597447 = 3896171) B3896171
theorem B2925227 : Blo 1024605 2925227 := bstep (se 1 (by rfl) ⟨2193920, by rfl⟩ : syracuseStep 2925227 = 4387841) B4387841
theorem B1024735 : Blo 1024605 1024735 := bstep (se 1 (by rfl) ⟨768551, by rfl⟩ : syracuseStep 1024735 = 1537103) B1537103
theorem B1024815 : Blo 1024605 1024815 := bstep (se 1 (by rfl) ⟨768611, by rfl⟩ : syracuseStep 1024815 = 1537223) B1537223
theorem B1155919 : Blo 1024605 1155919 := bstep (se 1 (by rfl) ⟨866939, by rfl⟩ : syracuseStep 1155919 = 1733879) B1733879
theorem B1024923 : Blo 1024605 1024923 := bstep (se 1 (by rfl) ⟨768692, by rfl⟩ : syracuseStep 1024923 = 1537385) B1537385
theorem B1024975 : Blo 1024605 1024975 := bstep (se 1 (by rfl) ⟨768731, by rfl⟩ : syracuseStep 1024975 = 1537463) B1537463
theorem B1024999 : Blo 1024605 1024999 := bstep (se 1 (by rfl) ⟨768749, by rfl⟩ : syracuseStep 1024999 = 1537499) B1537499
theorem B15803591 : Blo 1024605 15803591 := bstep (se 1 (by rfl) ⟨11852693, by rfl⟩ : syracuseStep 15803591 = 23705387) B23705387
theorem B1156315 : Blo 1024605 1156315 := bstep (se 1 (by rfl) ⟨867236, by rfl⟩ : syracuseStep 1156315 = 1734473) B1734473
theorem B1025311 : Blo 1024605 1025311 := bstep (se 1 (by rfl) ⟨768983, by rfl⟩ : syracuseStep 1025311 = 1537967) B1537967
theorem B2467103 : Blo 1024605 2467103 := bstep (se 1 (by rfl) ⟨1850327, by rfl⟩ : syracuseStep 2467103 = 3700655) B3700655
theorem B1025371 : Blo 1024605 1025371 := bstep (se 1 (by rfl) ⟨769028, by rfl⟩ : syracuseStep 1025371 = 1538057) B1538057
theorem B1025391 : Blo 1024605 1025391 := bstep (se 1 (by rfl) ⟨769043, by rfl⟩ : syracuseStep 1025391 = 1538087) B1538087
theorem B1025447 : Blo 1024605 1025447 := bstep (se 1 (by rfl) ⟨769085, by rfl⟩ : syracuseStep 1025447 = 1538171) B1538171
theorem B1025531 : Blo 1024605 1025531 := bstep (se 1 (by rfl) ⟨769148, by rfl⟩ : syracuseStep 1025531 = 1538297) B1538297
theorem B1156603 : Blo 1024605 1156603 := bstep (se 1 (by rfl) ⟨867452, by rfl⟩ : syracuseStep 1156603 = 1734905) B1734905
theorem B1025599 : Blo 1024605 1025599 := bstep (se 1 (by rfl) ⟨769199, by rfl⟩ : syracuseStep 1025599 = 1538399) B1538399
theorem B1025607 : Blo 1024605 1025607 := bstep (se 1 (by rfl) ⟨769205, by rfl⟩ : syracuseStep 1025607 = 1538411) B1538411
theorem B1156783 : Blo 1024605 1156783 := bstep (se 1 (by rfl) ⟨867587, by rfl⟩ : syracuseStep 1156783 = 1735175) B1735175
theorem B1025759 : Blo 1024605 1025759 := bstep (se 1 (by rfl) ⟨769319, by rfl⟩ : syracuseStep 1025759 = 1538639) B1538639
theorem B1025839 : Blo 1024605 1025839 := bstep (se 1 (by rfl) ⟨769379, by rfl⟩ : syracuseStep 1025839 = 1538759) B1538759
theorem B2598713 : Blo 1024605 2598713 := bstep (se 2 (by rfl) ⟨974517, by rfl⟩ : syracuseStep 2598713 = 1949035) B1949035
theorem B1386319 : Blo 1024605 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B1025947 : Blo 1024605 1025947 := bstep (se 1 (by rfl) ⟨769460, by rfl⟩ : syracuseStep 1025947 = 1538921) B1538921
theorem B1025999 : Blo 1024605 1025999 := bstep (se 1 (by rfl) ⟨769499, by rfl⟩ : syracuseStep 1025999 = 1538999) B1538999
theorem B1157071 : Blo 1024605 1157071 := bstep (se 1 (by rfl) ⟨867803, by rfl⟩ : syracuseStep 1157071 = 1735607) B1735607
theorem B1026023 : Blo 1024605 1026023 := bstep (se 1 (by rfl) ⟨769517, by rfl⟩ : syracuseStep 1026023 = 1539035) B1539035
theorem B9873485 : Blo 1024605 9873485 := bstep (se 3 (by rfl) ⟨1851278, by rfl⟩ : syracuseStep 9873485 = 3702557) B3702557
theorem B4925519 : Blo 1024605 4925519 := bstep (se 1 (by rfl) ⟨3694139, by rfl⟩ : syracuseStep 4925519 = 7388279) B7388279
theorem B1026335 : Blo 1024605 1026335 := bstep (se 1 (by rfl) ⟨769751, by rfl⟩ : syracuseStep 1026335 = 1539503) B1539503
theorem B1026395 : Blo 1024605 1026395 := bstep (se 1 (by rfl) ⟨769796, by rfl⟩ : syracuseStep 1026395 = 1539593) B1539593
theorem B1026415 : Blo 1024605 1026415 := bstep (se 1 (by rfl) ⟨769811, by rfl⟩ : syracuseStep 1026415 = 1539623) B1539623
theorem B1026471 : Blo 1024605 1026471 := bstep (se 1 (by rfl) ⟨769853, by rfl⟩ : syracuseStep 1026471 = 1539707) B1539707
theorem B1026555 : Blo 1024605 1026555 := bstep (se 1 (by rfl) ⟨769916, by rfl⟩ : syracuseStep 1026555 = 1539833) B1539833
theorem B1026623 : Blo 1024605 1026623 := bstep (se 1 (by rfl) ⟨769967, by rfl⟩ : syracuseStep 1026623 = 1539935) B1539935
theorem B1026631 : Blo 1024605 1026631 := bstep (se 1 (by rfl) ⟨769973, by rfl⟩ : syracuseStep 1026631 = 1539947) B1539947
theorem B2337353 : Blo 1024605 2337353 := bstep (se 2 (by rfl) ⟨876507, by rfl⟩ : syracuseStep 2337353 = 1753015) B1753015
theorem B1026783 : Blo 1024605 1026783 := bstep (se 1 (by rfl) ⟨770087, by rfl⟩ : syracuseStep 1026783 = 1540175) B1540175
theorem B1026863 : Blo 1024605 1026863 := bstep (se 1 (by rfl) ⟨770147, by rfl⟩ : syracuseStep 1026863 = 1540295) B1540295
theorem B1026971 : Blo 1024605 1026971 := bstep (se 1 (by rfl) ⟨770228, by rfl⟩ : syracuseStep 1026971 = 1540457) B1540457
theorem B1027023 : Blo 1024605 1027023 := bstep (se 1 (by rfl) ⟨770267, by rfl⟩ : syracuseStep 1027023 = 1540535) B1540535
theorem B1027047 : Blo 1024605 1027047 := bstep (se 1 (by rfl) ⟨770285, by rfl⟩ : syracuseStep 1027047 = 1540571) B1540571
theorem B2600059 : Blo 1024605 2600059 := bstep (se 1 (by rfl) ⟨1950044, by rfl⟩ : syracuseStep 2600059 = 3900089) B3900089
theorem B2927755 : Blo 1024605 2927755 := bstep (se 1 (by rfl) ⟨2195816, by rfl⟩ : syracuseStep 2927755 = 4391633) B4391633
theorem B2370703 : Blo 1024605 2370703 := bstep (se 1 (by rfl) ⟨1778027, by rfl⟩ : syracuseStep 2370703 = 3556055) B3556055
theorem B10005707 : Blo 1024605 10005707 := bstep (se 1 (by rfl) ⟨7504280, by rfl⟩ : syracuseStep 10005707 = 15008561) B15008561
theorem B1027359 : Blo 1024605 1027359 := bstep (se 1 (by rfl) ⟨770519, by rfl⟩ : syracuseStep 1027359 = 1541039) B1541039
theorem B1027419 : Blo 1024605 1027419 := bstep (se 1 (by rfl) ⟨770564, by rfl⟩ : syracuseStep 1027419 = 1541129) B1541129
theorem B1027439 : Blo 1024605 1027439 := bstep (se 1 (by rfl) ⟨770579, by rfl⟩ : syracuseStep 1027439 = 1541159) B1541159
theorem B16035191 : Blo 1024605 16035191 := bstep (se 1 (by rfl) ⟨12026393, by rfl⟩ : syracuseStep 16035191 = 24052787) B24052787
theorem B2305403 : Blo 1024605 2305403 := bstep (se 1 (by rfl) ⟨1729052, by rfl⟩ : syracuseStep 2305403 = 3458105) B3458105
theorem B2469257 : Blo 1024605 2469257 := bstep (se 2 (by rfl) ⟨925971, by rfl⟩ : syracuseStep 2469257 = 1851943) B1851943
theorem B1027495 : Blo 1024605 1027495 := bstep (se 1 (by rfl) ⟨770621, by rfl⟩ : syracuseStep 1027495 = 1541243) B1541243
theorem B2305529 : Blo 1024605 2305529 := bstep (se 2 (by rfl) ⟨864573, by rfl⟩ : syracuseStep 2305529 = 1729147) B1729147
theorem B1027579 : Blo 1024605 1027579 := bstep (se 1 (by rfl) ⟨770684, by rfl⟩ : syracuseStep 1027579 = 1541369) B1541369
theorem B1027647 : Blo 1024605 1027647 := bstep (se 1 (by rfl) ⟨770735, by rfl⟩ : syracuseStep 1027647 = 1541471) B1541471
theorem B1027655 : Blo 1024605 1027655 := bstep (se 1 (by rfl) ⟨770741, by rfl⟩ : syracuseStep 1027655 = 1541483) B1541483
theorem B2305619 : Blo 1024605 2305619 := bstep (se 1 (by rfl) ⟨1729214, by rfl⟩ : syracuseStep 2305619 = 3458429) B3458429
theorem B9383633 : Blo 1024605 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B1027807 : Blo 1024605 1027807 := bstep (se 1 (by rfl) ⟨770855, by rfl⟩ : syracuseStep 1027807 = 1541711) B1541711
theorem B2305799 : Blo 1024605 2305799 := bstep (se 1 (by rfl) ⟨1729349, by rfl⟩ : syracuseStep 2305799 = 3458699) B3458699
theorem B1027887 : Blo 1024605 1027887 := bstep (se 1 (by rfl) ⟨770915, by rfl⟩ : syracuseStep 1027887 = 1541831) B1541831
theorem B1027995 : Blo 1024605 1027995 := bstep (se 1 (by rfl) ⟨770996, by rfl⟩ : syracuseStep 1027995 = 1541993) B1541993
theorem B1028047 : Blo 1024605 1028047 := bstep (se 1 (by rfl) ⟨771035, by rfl⟩ : syracuseStep 1028047 = 1542071) B1542071
theorem B1028071 : Blo 1024605 1028071 := bstep (se 1 (by rfl) ⟨771053, by rfl⟩ : syracuseStep 1028071 = 1542107) B1542107
theorem B1028383 : Blo 1024605 1028383 := bstep (se 1 (by rfl) ⟨771287, by rfl⟩ : syracuseStep 1028383 = 1542575) B1542575
theorem B1028443 : Blo 1024605 1028443 := bstep (se 1 (by rfl) ⟨771332, by rfl⟩ : syracuseStep 1028443 = 1542665) B1542665
theorem B2306411 : Blo 1024605 2306411 := bstep (se 1 (by rfl) ⟨1729808, by rfl⟩ : syracuseStep 2306411 = 3459617) B3459617
theorem B1028463 : Blo 1024605 1028463 := bstep (se 1 (by rfl) ⟨771347, by rfl⟩ : syracuseStep 1028463 = 1542695) B1542695
theorem B1847719 : Blo 1024605 1847719 := bstep (se 1 (by rfl) ⟨1385789, by rfl⟩ : syracuseStep 1847719 = 2771579) B2771579
theorem B1028519 : Blo 1024605 1028519 := bstep (se 1 (by rfl) ⟨771389, by rfl⟩ : syracuseStep 1028519 = 1542779) B1542779
theorem B1946081 : Blo 1024605 1946081 := bstep (se 2 (by rfl) ⟨729780, by rfl⟩ : syracuseStep 1946081 = 1459561) B1459561
theorem B2306555 : Blo 1024605 2306555 := bstep (se 1 (by rfl) ⟨1729916, by rfl⟩ : syracuseStep 2306555 = 3459833) B3459833
theorem B2601467 : Blo 1024605 2601467 := bstep (se 1 (by rfl) ⟨1951100, by rfl⟩ : syracuseStep 2601467 = 3902201) B3902201
theorem B1028603 : Blo 1024605 1028603 := bstep (se 1 (by rfl) ⟨771452, by rfl⟩ : syracuseStep 1028603 = 1542905) B1542905
theorem B2306681 : Blo 1024605 2306681 := bstep (se 2 (by rfl) ⟨865005, by rfl⟩ : syracuseStep 2306681 = 1730011) B1730011
theorem B2306735 : Blo 1024605 2306735 := bstep (se 1 (by rfl) ⟨1730051, by rfl⟩ : syracuseStep 2306735 = 3460103) B3460103
theorem B2306807 : Blo 1024605 2306807 := bstep (se 1 (by rfl) ⟨1730105, by rfl⟩ : syracuseStep 2306807 = 3460211) B3460211
theorem B5190479 : Blo 1024605 5190479 := bstep (se 1 (by rfl) ⟨3892859, by rfl⟩ : syracuseStep 5190479 = 7785719) B7785719
theorem B2306987 : Blo 1024605 2306987 := bstep (se 1 (by rfl) ⟨1730240, by rfl⟩ : syracuseStep 2306987 = 3460481) B3460481
theorem B5190803 : Blo 1024605 5190803 := bstep (se 1 (by rfl) ⟨3893102, by rfl⟩ : syracuseStep 5190803 = 7786205) B7786205
theorem B2307527 : Blo 1024605 2307527 := bstep (se 1 (by rfl) ⟨1730645, by rfl⟩ : syracuseStep 2307527 = 3461291) B3461291
theorem B2602439 : Blo 1024605 2602439 := bstep (se 1 (by rfl) ⟨1951829, by rfl⟩ : syracuseStep 2602439 = 3903659) B3903659
theorem B2602489 : Blo 1024605 2602489 := bstep (se 2 (by rfl) ⟨975933, by rfl⟩ : syracuseStep 2602489 = 1951867) B1951867
theorem B32486923 : Blo 1024605 32486923 := bstep (se 1 (by rfl) ⟨24365192, by rfl⟩ : syracuseStep 32486923 = 48730385) B48730385
theorem B7386661 : Blo 1024605 7386661 := bstep (se 4 (by rfl) ⟨692499, by rfl⟩ : syracuseStep 7386661 = 1384999) B1384999
theorem B1095239 : Blo 1024605 1095239 := bstep (se 1 (by rfl) ⟨821429, by rfl⟩ : syracuseStep 1095239 = 1642859) B1642859
theorem B2602793 : Blo 1024605 2602793 := bstep (se 2 (by rfl) ⟨976047, by rfl⟩ : syracuseStep 2602793 = 1952095) B1952095
theorem B2307887 : Blo 1024605 2307887 := bstep (se 1 (by rfl) ⟨1730915, by rfl⟩ : syracuseStep 2307887 = 3461831) B3461831
theorem B6567767 : Blo 1024605 6567767 := bstep (se 1 (by rfl) ⟨4925825, by rfl⟩ : syracuseStep 6567767 = 9851651) B9851651
theorem B4994903 : Blo 1024605 4994903 := bstep (se 1 (by rfl) ⟨3746177, by rfl⟩ : syracuseStep 4994903 = 7492355) B7492355
theorem B2635649 : Blo 1024605 2635649 := bstep (se 2 (by rfl) ⟨988368, by rfl⟩ : syracuseStep 2635649 = 1976737) B1976737
theorem B2603137 : Blo 1024605 2603137 := bstep (se 2 (by rfl) ⟨976176, by rfl⟩ : syracuseStep 2603137 = 1952353) B1952353
theorem B2308463 : Blo 1024605 2308463 := bstep (se 1 (by rfl) ⟨1731347, by rfl⟩ : syracuseStep 2308463 = 3462695) B3462695
theorem B2308535 : Blo 1024605 2308535 := bstep (se 1 (by rfl) ⟨1731401, by rfl⟩ : syracuseStep 2308535 = 3462803) B3462803
theorem B7780859 : Blo 1024605 7780859 := bstep (se 1 (by rfl) ⟨5835644, by rfl⟩ : syracuseStep 7780859 = 11671289) B11671289
theorem B2308679 : Blo 1024605 2308679 := bstep (se 1 (by rfl) ⟨1731509, by rfl⟩ : syracuseStep 2308679 = 3463019) B3463019
theorem B2308715 : Blo 1024605 2308715 := bstep (se 1 (by rfl) ⟨1731536, by rfl⟩ : syracuseStep 2308715 = 3463073) B3463073
theorem B12499595 : Blo 1024605 12499595 := bstep (se 1 (by rfl) ⟨9374696, by rfl⟩ : syracuseStep 12499595 = 18749393) B18749393
theorem B2309111 : Blo 1024605 2309111 := bstep (se 1 (by rfl) ⟨1731833, by rfl⟩ : syracuseStep 2309111 = 3463667) B3463667
theorem B17513495 : Blo 1024605 17513495 := bstep (se 1 (by rfl) ⟨13135121, by rfl⟩ : syracuseStep 17513495 = 26270243) B26270243
theorem B5553317 : Blo 1024605 5553317 := bstep (se 4 (by rfl) ⟨520623, by rfl⟩ : syracuseStep 5553317 = 1041247) B1041247
theorem B2637095 : Blo 1024605 2637095 := bstep (se 1 (by rfl) ⟨1977821, by rfl⟩ : syracuseStep 2637095 = 3955643) B3955643
theorem B2309471 : Blo 1024605 2309471 := bstep (se 1 (by rfl) ⟨1732103, by rfl⟩ : syracuseStep 2309471 = 3464207) B3464207
theorem B4931131 : Blo 1024605 4931131 := bstep (se 1 (by rfl) ⟨3698348, by rfl⟩ : syracuseStep 4931131 = 7396697) B7396697
theorem B11681495 : Blo 1024605 11681495 := bstep (se 1 (by rfl) ⟨8761121, by rfl⟩ : syracuseStep 11681495 = 17522243) B17522243
theorem B2309867 : Blo 1024605 2309867 := bstep (se 1 (by rfl) ⟨1732400, by rfl⟩ : syracuseStep 2309867 = 3464801) B3464801
theorem B4931401 : Blo 1024605 4931401 := bstep (se 2 (by rfl) ⟨1849275, by rfl⟩ : syracuseStep 4931401 = 3698551) B3698551
theorem B2309993 : Blo 1024605 2309993 := bstep (se 2 (by rfl) ⟨866247, by rfl⟩ : syracuseStep 2309993 = 1732495) B1732495
theorem B2408297 : Blo 1024605 2408297 := bstep (se 2 (by rfl) ⟨903111, by rfl⟩ : syracuseStep 2408297 = 1806223) B1806223
theorem B42647651 : Blo 1024605 42647651 := bstep (se 1 (by rfl) ⟨31985738, by rfl⟩ : syracuseStep 42647651 = 63971477) B63971477
theorem B5193881 : Blo 1024605 5193881 := bstep (se 2 (by rfl) ⟨1947705, by rfl⟩ : syracuseStep 5193881 = 3895411) B3895411
theorem B17810021 : Blo 1024605 17810021 := bstep (se 4 (by rfl) ⟨1669689, by rfl⟩ : syracuseStep 17810021 = 3339379) B3339379
theorem B22495927 : Blo 1024605 22495927 := bstep (se 1 (by rfl) ⟨16871945, by rfl⟩ : syracuseStep 22495927 = 33743891) B33743891
theorem B2310839 : Blo 1024605 2310839 := bstep (se 1 (by rfl) ⟨1733129, by rfl⟩ : syracuseStep 2310839 = 3466259) B3466259
theorem B2081555 : Blo 1024605 2081555 := bstep (se 1 (by rfl) ⟨1561166, by rfl⟩ : syracuseStep 2081555 = 3122333) B3122333
theorem B2311055 : Blo 1024605 2311055 := bstep (se 1 (by rfl) ⟨1733291, by rfl⟩ : syracuseStep 2311055 = 3466583) B3466583
theorem B5194691 : Blo 1024605 5194691 := bstep (se 1 (by rfl) ⟨3896018, by rfl⟩ : syracuseStep 5194691 = 7792037) B7792037
theorem B6964199 : Blo 1024605 6964199 := bstep (se 1 (by rfl) ⟨5223149, by rfl⟩ : syracuseStep 6964199 = 10446299) B10446299
theorem B6571151 : Blo 1024605 6571151 := bstep (se 1 (by rfl) ⟨4928363, by rfl⟩ : syracuseStep 6571151 = 9856727) B9856727
theorem B8766863 : Blo 1024605 8766863 := bstep (se 1 (by rfl) ⟨6575147, by rfl⟩ : syracuseStep 8766863 = 13150295) B13150295
theorem B2311775 : Blo 1024605 2311775 := bstep (se 1 (by rfl) ⟨1733831, by rfl⟩ : syracuseStep 2311775 = 3467663) B3467663
theorem B2311991 : Blo 1024605 2311991 := bstep (se 1 (by rfl) ⟨1733993, by rfl⟩ : syracuseStep 2311991 = 3467987) B3467987
theorem B8800067 : Blo 1024605 8800067 := bstep (se 1 (by rfl) ⟨6600050, by rfl⟩ : syracuseStep 8800067 = 13200101) B13200101
theorem B3459023 : Blo 1024605 3459023 := bstep (se 1 (by rfl) ⟨2594267, by rfl⟩ : syracuseStep 3459023 = 5188535) B5188535
theorem B2312297 : Blo 1024605 2312297 := bstep (se 2 (by rfl) ⟨867111, by rfl⟩ : syracuseStep 2312297 = 1734223) B1734223
theorem B3950777 : Blo 1024605 3950777 := bstep (se 2 (by rfl) ⟨1481541, by rfl⟩ : syracuseStep 3950777 = 2963083) B2963083
theorem B1231303 : Blo 1024605 1231303 := bstep (se 1 (by rfl) ⟨923477, by rfl⟩ : syracuseStep 1231303 = 1846955) B1846955
theorem B1296967 : Blo 1024605 1296967 := bstep (se 1 (by rfl) ⟨972725, by rfl⟩ : syracuseStep 1296967 = 1945451) B1945451
theorem B2312783 : Blo 1024605 2312783 := bstep (se 1 (by rfl) ⟨1734587, by rfl⟩ : syracuseStep 2312783 = 3469175) B3469175
theorem B4934267 : Blo 1024605 4934267 := bstep (se 1 (by rfl) ⟨3700700, by rfl⟩ : syracuseStep 4934267 = 7401401) B7401401
theorem B1460911 : Blo 1024605 1460911 := bstep (se 1 (by rfl) ⟨1095683, by rfl⟩ : syracuseStep 1460911 = 2191367) B2191367
theorem B1231543 : Blo 1024605 1231543 := bstep (se 1 (by rfl) ⟨923657, by rfl⟩ : syracuseStep 1231543 = 1847315) B1847315
theorem B2312927 : Blo 1024605 2312927 := bstep (se 1 (by rfl) ⟨1734695, by rfl⟩ : syracuseStep 2312927 = 3469391) B3469391
theorem B16862003 : Blo 1024605 16862003 := bstep (se 1 (by rfl) ⟨12646502, by rfl⟩ : syracuseStep 16862003 = 25293005) B25293005
theorem B3459995 : Blo 1024605 3459995 := bstep (se 1 (by rfl) ⟨2594996, by rfl⟩ : syracuseStep 3459995 = 5189993) B5189993
theorem B2313179 : Blo 1024605 2313179 := bstep (se 1 (by rfl) ⟨1734884, by rfl⟩ : syracuseStep 2313179 = 3469769) B3469769
theorem B2313359 : Blo 1024605 2313359 := bstep (se 1 (by rfl) ⟨1735019, by rfl⟩ : syracuseStep 2313359 = 3470039) B3470039
theorem B11095217 : Blo 1024605 11095217 := bstep (se 2 (by rfl) ⟨4160706, by rfl⟩ : syracuseStep 11095217 = 8321413) B8321413
theorem B47369395 : Blo 1024605 47369395 := bstep (se 1 (by rfl) ⟨35527046, by rfl⟩ : syracuseStep 47369395 = 71054093) B71054093
theorem B2313449 : Blo 1024605 2313449 := bstep (se 2 (by rfl) ⟨867543, by rfl⟩ : syracuseStep 2313449 = 1735087) B1735087
theorem B2313503 : Blo 1024605 2313503 := bstep (se 1 (by rfl) ⟨1735127, by rfl⟩ : syracuseStep 2313503 = 3470255) B3470255
theorem B2314025 : Blo 1024605 2314025 := bstep (se 2 (by rfl) ⟨867759, by rfl⟩ : syracuseStep 2314025 = 1735519) B1735519
theorem B8769323 : Blo 1024605 8769323 := bstep (se 1 (by rfl) ⟨6576992, by rfl⟩ : syracuseStep 8769323 = 13153985) B13153985
theorem B3461021 : Blo 1024605 3461021 := bstep (se 3 (by rfl) ⟨648941, by rfl⟩ : syracuseStep 3461021 = 1297883) B1297883
theorem B3461129 : Blo 1024605 3461129 := bstep (se 2 (by rfl) ⟨1297923, by rfl⟩ : syracuseStep 3461129 = 2595847) B2595847
theorem B1298855 : Blo 1024605 1298855 := bstep (se 1 (by rfl) ⟨974141, by rfl⟩ : syracuseStep 1298855 = 1948283) B1948283
theorem B5198255 : Blo 1024605 5198255 := bstep (se 1 (by rfl) ⟨3898691, by rfl⟩ : syracuseStep 5198255 = 7797383) B7797383
theorem B3756463 : Blo 1024605 3756463 := bstep (se 1 (by rfl) ⟨2817347, by rfl⟩ : syracuseStep 3756463 = 5634695) B5634695
theorem B1299007 : Blo 1024605 1299007 := bstep (se 1 (by rfl) ⟨974255, by rfl⟩ : syracuseStep 1299007 = 1948511) B1948511
theorem B284021315 : Blo 1024605 284021315 := bstep (se 1 (by rfl) ⟨213015986, by rfl⟩ : syracuseStep 284021315 = 426031973) B426031973
theorem B9851615 : Blo 1024605 9851615 := bstep (se 1 (by rfl) ⟨7388711, by rfl⟩ : syracuseStep 9851615 = 14777423) B14777423
theorem B1299179 : Blo 1024605 1299179 := bstep (se 1 (by rfl) ⟨974384, by rfl⟩ : syracuseStep 1299179 = 1948769) B1948769
theorem B5854031 : Blo 1024605 5854031 := bstep (se 1 (by rfl) ⟨4390523, by rfl⟩ : syracuseStep 5854031 = 8781047) B8781047
theorem B23712787 : Blo 1024605 23712787 := bstep (se 1 (by rfl) ⟨17784590, by rfl⟩ : syracuseStep 23712787 = 35569181) B35569181
theorem B12506359 : Blo 1024605 12506359 := bstep (se 1 (by rfl) ⟨9379769, by rfl⟩ : syracuseStep 12506359 = 18759539) B18759539
theorem B5199227 : Blo 1024605 5199227 := bstep (se 1 (by rfl) ⟨3899420, by rfl⟩ : syracuseStep 5199227 = 7798841) B7798841
theorem B1300151 : Blo 1024605 1300151 := bstep (se 1 (by rfl) ⟨975113, by rfl⟩ : syracuseStep 1300151 = 1950227) B1950227
theorem B1300303 : Blo 1024605 1300303 := bstep (se 1 (by rfl) ⟨975227, by rfl⟩ : syracuseStep 1300303 = 1950455) B1950455
theorem B5200523 : Blo 1024605 5200523 := bstep (se 1 (by rfl) ⟨3900392, by rfl⟩ : syracuseStep 5200523 = 7800785) B7800785
theorem B20011961 : Blo 1024605 20011961 := bstep (se 2 (by rfl) ⟨7504485, by rfl⟩ : syracuseStep 20011961 = 15008971) B15008971
theorem B5266471 : Blo 1024605 5266471 := bstep (se 1 (by rfl) ⟨3949853, by rfl⟩ : syracuseStep 5266471 = 7899707) B7899707
theorem B9854075 : Blo 1024605 9854075 := bstep (se 1 (by rfl) ⟨7390556, by rfl⟩ : syracuseStep 9854075 = 14781113) B14781113
theorem B3464315 : Blo 1024605 3464315 := bstep (se 1 (by rfl) ⟨2598236, by rfl⟩ : syracuseStep 3464315 = 5196473) B5196473
theorem B5856421 : Blo 1024605 5856421 := bstep (se 4 (by rfl) ⟨549039, by rfl⟩ : syracuseStep 5856421 = 1098079) B1098079
theorem B2776313 : Blo 1024605 2776313 := bstep (se 2 (by rfl) ⟨1041117, by rfl⟩ : syracuseStep 2776313 = 2082235) B2082235
theorem B19717445 : Blo 1024605 19717445 := bstep (se 4 (by rfl) ⟨1848510, by rfl⟩ : syracuseStep 19717445 = 3697021) B3697021
theorem B3890551 : Blo 1024605 3890551 := bstep (se 1 (by rfl) ⟨2917913, by rfl⟩ : syracuseStep 3890551 = 5835827) B5835827
theorem B4939127 : Blo 1024605 4939127 := bstep (se 1 (by rfl) ⟨3704345, by rfl⟩ : syracuseStep 4939127 = 7408691) B7408691
theorem B3464585 : Blo 1024605 3464585 := bstep (se 2 (by rfl) ⟨1299219, by rfl⟩ : syracuseStep 3464585 = 2598439) B2598439
theorem B65068505 : Blo 1024605 65068505 := bstep (se 2 (by rfl) ⟨24400689, by rfl⟩ : syracuseStep 65068505 = 48801379) B48801379
theorem B4382201 : Blo 1024605 4382201 := bstep (se 2 (by rfl) ⟨1643325, by rfl⟩ : syracuseStep 4382201 = 3286651) B3286651
theorem B45047411 : Blo 1024605 45047411 := bstep (se 1 (by rfl) ⟨33785558, by rfl⟩ : syracuseStep 45047411 = 67571117) B67571117
theorem B3465017 : Blo 1024605 3465017 := bstep (se 2 (by rfl) ⟨1299381, by rfl⟩ : syracuseStep 3465017 = 2598763) B2598763
theorem B4939649 : Blo 1024605 4939649 := bstep (se 2 (by rfl) ⟨1852368, by rfl⟩ : syracuseStep 4939649 = 3704737) B3704737
theorem B1171751 : Blo 1024605 1171751 := bstep (se 1 (by rfl) ⟨878813, by rfl⟩ : syracuseStep 1171751 = 1757627) B1757627
theorem B6578633 : Blo 1024605 6578633 := bstep (se 2 (by rfl) ⟨2466987, by rfl⟩ : syracuseStep 6578633 = 4933975) B4933975
theorem B3465881 : Blo 1024605 3465881 := bstep (se 2 (by rfl) ⟨1299705, by rfl⟩ : syracuseStep 3465881 = 2599411) B2599411
theorem B6251179 : Blo 1024605 6251179 := bstep (se 1 (by rfl) ⟨4688384, by rfl⟩ : syracuseStep 6251179 = 9376769) B9376769
theorem B6578891 : Blo 1024605 6578891 := bstep (se 1 (by rfl) ⟨4934168, by rfl⟩ : syracuseStep 6578891 = 9868337) B9868337
theorem B1729451 : Blo 1024605 1729451 := bstep (se 1 (by rfl) ⟨1297088, by rfl⟩ : syracuseStep 1729451 = 2594177) B2594177
theorem B5006479 : Blo 1024605 5006479 := bstep (se 1 (by rfl) ⟨3754859, by rfl⟩ : syracuseStep 5006479 = 7509719) B7509719
theorem B1729991 : Blo 1024605 1729991 := bstep (se 1 (by rfl) ⟨1297493, by rfl⟩ : syracuseStep 1729991 = 2594987) B2594987
theorem B3467393 : Blo 1024605 3467393 := bstep (se 2 (by rfl) ⟨1300272, by rfl⟩ : syracuseStep 3467393 = 2600545) B2600545
theorem B4679815 : Blo 1024605 4679815 := bstep (se 1 (by rfl) ⟨3509861, by rfl⟩ : syracuseStep 4679815 = 7019723) B7019723
theorem B14772401 : Blo 1024605 14772401 := bstep (se 2 (by rfl) ⟨5539650, by rfl⟩ : syracuseStep 14772401 = 11079301) B11079301
theorem B5204249 : Blo 1024605 5204249 := bstep (se 2 (by rfl) ⟨1951593, by rfl⟩ : syracuseStep 5204249 = 3903187) B3903187
theorem B1730983 : Blo 1024605 1730983 := bstep (se 1 (by rfl) ⟨1298237, by rfl⟩ : syracuseStep 1730983 = 2596475) B2596475
theorem B2779559 : Blo 1024605 2779559 := bstep (se 1 (by rfl) ⟨2084669, by rfl⟩ : syracuseStep 2779559 = 4169339) B4169339
theorem B3467771 : Blo 1024605 3467771 := bstep (se 1 (by rfl) ⟨2600828, by rfl⟩ : syracuseStep 3467771 = 5201657) B5201657
theorem B2779643 : Blo 1024605 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B13167107 : Blo 1024605 13167107 := bstep (se 1 (by rfl) ⟨9875330, by rfl⟩ : syracuseStep 13167107 = 19750661) B19750661
theorem B1731145 : Blo 1024605 1731145 := bstep (se 2 (by rfl) ⟨649179, by rfl⟩ : syracuseStep 1731145 = 1298359) B1298359
theorem B1731179 : Blo 1024605 1731179 := bstep (se 1 (by rfl) ⟨1298384, by rfl⟩ : syracuseStep 1731179 = 2596769) B2596769
theorem B168487559 : Blo 1024605 168487559 := bstep (se 1 (by rfl) ⟨126365669, by rfl⟩ : syracuseStep 168487559 = 252731339) B252731339
theorem B2190007 : Blo 1024605 2190007 := bstep (se 1 (by rfl) ⟨1642505, by rfl⟩ : syracuseStep 2190007 = 3285011) B3285011
theorem B568519397 : Blo 1024605 568519397 := bstep (se 4 (by rfl) ⟨53298693, by rfl⟩ : syracuseStep 568519397 = 106597387) B106597387
theorem B3697427 : Blo 1024605 3697427 := bstep (se 1 (by rfl) ⟨2773070, by rfl⟩ : syracuseStep 3697427 = 5546141) B5546141
theorem B4385603 : Blo 1024605 4385603 := bstep (se 1 (by rfl) ⟨3289202, by rfl⟩ : syracuseStep 4385603 = 6578405) B6578405
theorem B3468203 : Blo 1024605 3468203 := bstep (se 1 (by rfl) ⟨2601152, by rfl⟩ : syracuseStep 3468203 = 5202305) B5202305
theorem B4156555 : Blo 1024605 4156555 := bstep (se 1 (by rfl) ⟨3117416, by rfl⟩ : syracuseStep 4156555 = 6234833) B6234833
theorem B2813143 : Blo 1024605 2813143 := bstep (se 1 (by rfl) ⟨2109857, by rfl⟩ : syracuseStep 2813143 = 4219715) B4219715
theorem B7793981 : Blo 1024605 7793981 := bstep (se 3 (by rfl) ⟨1461371, by rfl⟩ : syracuseStep 7793981 = 2922743) B2922743
theorem B3468743 : Blo 1024605 3468743 := bstep (se 1 (by rfl) ⟨2601557, by rfl⟩ : syracuseStep 3468743 = 5203115) B5203115
theorem B3894743 : Blo 1024605 3894743 := bstep (se 1 (by rfl) ⟨2921057, by rfl⟩ : syracuseStep 3894743 = 5842115) B5842115
theorem B4157009 : Blo 1024605 4157009 := bstep (se 2 (by rfl) ⟨1558878, by rfl⟩ : syracuseStep 4157009 = 3117757) B3117757
theorem B3469067 : Blo 1024605 3469067 := bstep (se 1 (by rfl) ⟨2601800, by rfl⟩ : syracuseStep 3469067 = 5203601) B5203601
theorem B3469337 : Blo 1024605 3469337 := bstep (se 2 (by rfl) ⟨1301001, by rfl⟩ : syracuseStep 3469337 = 2602003) B2602003
theorem B1732873 : Blo 1024605 1732873 := bstep (se 2 (by rfl) ⟨649827, by rfl⟩ : syracuseStep 1732873 = 1299655) B1299655
theorem B37482857 : Blo 1024605 37482857 := bstep (se 2 (by rfl) ⟨14056071, by rfl⟩ : syracuseStep 37482857 = 28112143) B28112143
theorem B42169187 : Blo 1024605 42169187 := bstep (se 1 (by rfl) ⟨31626890, by rfl⟩ : syracuseStep 42169187 = 63253781) B63253781
theorem B1536923 : Blo 1024605 1536923 := bstep (se 1 (by rfl) ⟨1152692, by rfl⟩ : syracuseStep 1536923 = 2305385) B2305385
theorem B5207003 : Blo 1024605 5207003 := bstep (se 1 (by rfl) ⟨3905252, by rfl⟩ : syracuseStep 5207003 = 7810505) B7810505
theorem B5207165 : Blo 1024605 5207165 := bstep (se 3 (by rfl) ⟨976343, by rfl⟩ : syracuseStep 5207165 = 1952687) B1952687
theorem B3470579 : Blo 1024605 3470579 := bstep (se 1 (by rfl) ⟨2602934, by rfl⟩ : syracuseStep 3470579 = 5205869) B5205869
theorem B1537319 : Blo 1024605 1537319 := bstep (se 1 (by rfl) ⟨1152989, by rfl⟩ : syracuseStep 1537319 = 2305979) B2305979
theorem B3470687 : Blo 1024605 3470687 := bstep (se 1 (by rfl) ⟨2603015, by rfl⟩ : syracuseStep 3470687 = 5206031) B5206031
theorem B4388201 : Blo 1024605 4388201 := bstep (se 2 (by rfl) ⟨1645575, by rfl⟩ : syracuseStep 4388201 = 3291151) B3291151
theorem B1537403 : Blo 1024605 1537403 := bstep (se 1 (by rfl) ⟨1153052, by rfl⟩ : syracuseStep 1537403 = 2306105) B2306105
theorem B2225569 : Blo 1024605 2225569 := bstep (se 2 (by rfl) ⟨834588, by rfl⟩ : syracuseStep 2225569 = 1669177) B1669177
theorem B2192827 : Blo 1024605 2192827 := bstep (se 1 (by rfl) ⟨1644620, by rfl⟩ : syracuseStep 2192827 = 3289241) B3289241
theorem B1537529 : Blo 1024605 1537529 := bstep (se 2 (by rfl) ⟨576573, by rfl⟩ : syracuseStep 1537529 = 1153147) B1153147
theorem B1537631 : Blo 1024605 1537631 := bstep (se 1 (by rfl) ⟨1153223, by rfl⟩ : syracuseStep 1537631 = 2306447) B2306447
theorem B7796411 : Blo 1024605 7796411 := bstep (se 1 (by rfl) ⟨5847308, by rfl⟩ : syracuseStep 7796411 = 11694617) B11694617
theorem B2193083 : Blo 1024605 2193083 := bstep (se 1 (by rfl) ⟨1644812, by rfl⟩ : syracuseStep 2193083 = 3289625) B3289625
theorem B1734331 : Blo 1024605 1734331 := bstep (se 1 (by rfl) ⟨1300748, by rfl⟩ : syracuseStep 1734331 = 2601497) B2601497
theorem B1537847 : Blo 1024605 1537847 := bstep (se 1 (by rfl) ⟨1153385, by rfl⟩ : syracuseStep 1537847 = 2306771) B2306771
theorem B3897143 : Blo 1024605 3897143 := bstep (se 1 (by rfl) ⟨2922857, by rfl⟩ : syracuseStep 3897143 = 5845715) B5845715
theorem B1538153 : Blo 1024605 1538153 := bstep (se 2 (by rfl) ⟨576807, by rfl⟩ : syracuseStep 1538153 = 1153615) B1153615
theorem B3897629 : Blo 1024605 3897629 := bstep (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) B1461611
theorem B1538471 : Blo 1024605 1538471 := bstep (se 1 (by rfl) ⟨1153853, by rfl⟩ : syracuseStep 1538471 = 2307707) B2307707
theorem B1538555 : Blo 1024605 1538555 := bstep (se 1 (by rfl) ⟨1153916, by rfl⟩ : syracuseStep 1538555 = 2307833) B2307833
theorem B3701321 : Blo 1024605 3701321 := bstep (se 2 (by rfl) ⟨1387995, by rfl⟩ : syracuseStep 3701321 = 2775991) B2775991
theorem B1538681 : Blo 1024605 1538681 := bstep (se 2 (by rfl) ⟨577005, by rfl⟩ : syracuseStep 1538681 = 1154011) B1154011
theorem B4389515 : Blo 1024605 4389515 := bstep (se 1 (by rfl) ⟨3292136, by rfl⟩ : syracuseStep 4389515 = 6584273) B6584273
theorem B1538735 : Blo 1024605 1538735 := bstep (se 1 (by rfl) ⟨1154051, by rfl⟩ : syracuseStep 1538735 = 2308103) B2308103
theorem B1538783 : Blo 1024605 1538783 := bstep (se 1 (by rfl) ⟨1154087, by rfl⟩ : syracuseStep 1538783 = 2308175) B2308175
theorem B1735391 : Blo 1024605 1735391 := bstep (se 1 (by rfl) ⟨1301543, by rfl⟩ : syracuseStep 1735391 = 2603087) B2603087
theorem B5929847 : Blo 1024605 5929847 := bstep (se 1 (by rfl) ⟨4447385, by rfl⟩ : syracuseStep 5929847 = 8894771) B8894771
theorem B9862073 : Blo 1024605 9862073 := bstep (se 2 (by rfl) ⟨3698277, by rfl⟩ : syracuseStep 9862073 = 7396555) B7396555
theorem B1539047 : Blo 1024605 1539047 := bstep (se 1 (by rfl) ⟨1154285, by rfl⟩ : syracuseStep 1539047 = 2308571) B2308571
theorem B1539305 : Blo 1024605 1539305 := bstep (se 2 (by rfl) ⟨577239, by rfl⟩ : syracuseStep 1539305 = 1154479) B1154479
theorem B1539359 : Blo 1024605 1539359 := bstep (se 1 (by rfl) ⟨1154519, by rfl⟩ : syracuseStep 1539359 = 2309039) B2309039
theorem B1539527 : Blo 1024605 1539527 := bstep (se 1 (by rfl) ⟨1154645, by rfl⟩ : syracuseStep 1539527 = 2309291) B2309291
theorem B7798355 : Blo 1024605 7798355 := bstep (se 1 (by rfl) ⟨5848766, by rfl⟩ : syracuseStep 7798355 = 11697533) B11697533
theorem B7012001 : Blo 1024605 7012001 := bstep (se 2 (by rfl) ⟨2629500, by rfl⟩ : syracuseStep 7012001 = 5259001) B5259001
theorem B7405319 : Blo 1024605 7405319 := bstep (se 1 (by rfl) ⟨5553989, by rfl⟩ : syracuseStep 7405319 = 11107979) B11107979
theorem B1539881 : Blo 1024605 1539881 := bstep (se 2 (by rfl) ⟨577455, by rfl⟩ : syracuseStep 1539881 = 1154911) B1154911
theorem B1539887 : Blo 1024605 1539887 := bstep (se 1 (by rfl) ⟨1154915, by rfl⟩ : syracuseStep 1539887 = 2309831) B2309831
theorem B3997927 : Blo 1024605 3997927 := bstep (se 1 (by rfl) ⟨2998445, by rfl⟩ : syracuseStep 3997927 = 5996891) B5996891
theorem B1540559 : Blo 1024605 1540559 := bstep (se 1 (by rfl) ⟨1155419, by rfl⟩ : syracuseStep 1540559 = 2310839) B2310839
theorem B1540601 : Blo 1024605 1540601 := bstep (se 2 (by rfl) ⟨577725, by rfl⟩ : syracuseStep 1540601 = 1155451) B1155451
theorem B1540703 : Blo 1024605 1540703 := bstep (se 1 (by rfl) ⟨1155527, by rfl⟩ : syracuseStep 1540703 = 2311055) B2311055
theorem B4391891 : Blo 1024605 4391891 := bstep (se 1 (by rfl) ⟨3293918, by rfl⟩ : syracuseStep 4391891 = 6587837) B6587837
theorem B1541183 : Blo 1024605 1541183 := bstep (se 1 (by rfl) ⟨1155887, by rfl⟩ : syracuseStep 1541183 = 2311775) B2311775
theorem B1541225 : Blo 1024605 1541225 := bstep (se 2 (by rfl) ⟨577959, by rfl⟩ : syracuseStep 1541225 = 1155919) B1155919
theorem B1541327 : Blo 1024605 1541327 := bstep (se 1 (by rfl) ⟨1155995, by rfl⟩ : syracuseStep 1541327 = 2311991) B2311991
theorem B5866711 : Blo 1024605 5866711 := bstep (se 1 (by rfl) ⟨4400033, by rfl⟩ : syracuseStep 5866711 = 8800067) B8800067
theorem B1541531 : Blo 1024605 1541531 := bstep (se 1 (by rfl) ⟨1156148, by rfl⟩ : syracuseStep 1541531 = 2312297) B2312297
theorem B1541753 : Blo 1024605 1541753 := bstep (se 2 (by rfl) ⟨578157, by rfl⟩ : syracuseStep 1541753 = 1156315) B1156315
theorem B1541855 : Blo 1024605 1541855 := bstep (se 1 (by rfl) ⟨1156391, by rfl⟩ : syracuseStep 1541855 = 2312783) B2312783
theorem B1541951 : Blo 1024605 1541951 := bstep (se 1 (by rfl) ⟨1156463, by rfl⟩ : syracuseStep 1541951 = 2312927) B2312927
theorem B13502315 : Blo 1024605 13502315 := bstep (se 1 (by rfl) ⟨10126736, by rfl⟩ : syracuseStep 13502315 = 20253473) B20253473
theorem B11241335 : Blo 1024605 11241335 := bstep (se 1 (by rfl) ⟨8431001, by rfl⟩ : syracuseStep 11241335 = 16862003) B16862003
theorem B1542119 : Blo 1024605 1542119 := bstep (se 1 (by rfl) ⟨1156589, by rfl⟩ : syracuseStep 1542119 = 2313179) B2313179
theorem B1542137 : Blo 1024605 1542137 := bstep (se 2 (by rfl) ⟨578301, by rfl⟩ : syracuseStep 1542137 = 1156603) B1156603
theorem B1542239 : Blo 1024605 1542239 := bstep (se 1 (by rfl) ⟨1156679, by rfl⟩ : syracuseStep 1542239 = 2313359) B2313359
theorem B1542299 : Blo 1024605 1542299 := bstep (se 1 (by rfl) ⟨1156724, by rfl⟩ : syracuseStep 1542299 = 2313449) B2313449
theorem B1542335 : Blo 1024605 1542335 := bstep (se 1 (by rfl) ⟨1156751, by rfl⟩ : syracuseStep 1542335 = 2313503) B2313503
theorem B1542377 : Blo 1024605 1542377 := bstep (se 2 (by rfl) ⟨578391, by rfl⟩ : syracuseStep 1542377 = 1156783) B1156783
theorem B1542683 : Blo 1024605 1542683 := bstep (se 1 (by rfl) ⟨1157012, by rfl⟩ : syracuseStep 1542683 = 2314025) B2314025
theorem B1542761 : Blo 1024605 1542761 := bstep (se 2 (by rfl) ⟨578535, by rfl⟩ : syracuseStep 1542761 = 1157071) B1157071
theorem B3902687 : Blo 1024605 3902687 := bstep (se 1 (by rfl) ⟨2927015, by rfl⟩ : syracuseStep 3902687 = 5854031) B5854031
theorem B1641737 : Blo 1024605 1641737 := bstep (se 2 (by rfl) ⟨615651, by rfl⟩ : syracuseStep 1641737 = 1231303) B1231303
theorem B5836283 : Blo 1024605 5836283 := bstep (se 1 (by rfl) ⟨4377212, by rfl⟩ : syracuseStep 5836283 = 8754425) B8754425
theorem B5542073 : Blo 1024605 5542073 := bstep (se 2 (by rfl) ⟨2078277, by rfl⟩ : syracuseStep 5542073 = 4156555) B4156555
theorem B3903673 : Blo 1024605 3903673 := bstep (se 2 (by rfl) ⟨1463877, by rfl⟩ : syracuseStep 3903673 = 2927755) B2927755
theorem B2920637 : Blo 1024605 2920637 := bstep (se 3 (by rfl) ⟨547619, by rfl⟩ : syracuseStep 2920637 = 1095239) B1095239
theorem B13144963 : Blo 1024605 13144963 := bstep (se 1 (by rfl) ⟨9858722, by rfl⟩ : syracuseStep 13144963 = 19717445) B19717445
theorem B2463625 : Blo 1024605 2463625 := bstep (se 2 (by rfl) ⟨923859, by rfl⟩ : syracuseStep 2463625 = 1847719) B1847719
theorem B1152967 : Blo 1024605 1152967 := bstep (se 1 (by rfl) ⟨864725, by rfl⟩ : syracuseStep 1152967 = 1729451) B1729451
theorem B1153327 : Blo 1024605 1153327 := bstep (se 1 (by rfl) ⟨864995, by rfl⟩ : syracuseStep 1153327 = 1729991) B1729991
theorem B7412381 : Blo 1024605 7412381 := bstep (se 3 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 7412381 = 2779643) B2779643
theorem B3283679 : Blo 1024605 3283679 := bstep (se 1 (by rfl) ⟨2462759, by rfl⟩ : syracuseStep 3283679 = 4925519) B4925519
theorem B1154119 : Blo 1024605 1154119 := bstep (se 1 (by rfl) ⟨865589, by rfl⟩ : syracuseStep 1154119 = 1731179) B1731179
theorem B2464951 : Blo 1024605 2464951 := bstep (se 1 (by rfl) ⟨1848713, by rfl⟩ : syracuseStep 2464951 = 3697427) B3697427
theorem B2923735 : Blo 1024605 2923735 := bstep (se 1 (by rfl) ⟨2192801, by rfl⟩ : syracuseStep 2923735 = 4385603) B4385603
theorem B2923769 : Blo 1024605 2923769 := bstep (se 2 (by rfl) ⟨1096413, by rfl⟩ : syracuseStep 2923769 = 2192827) B2192827
theorem B10690127 : Blo 1024605 10690127 := bstep (se 1 (by rfl) ⟨8017595, by rfl⟩ : syracuseStep 10690127 = 16035191) B16035191
theorem B1646171 : Blo 1024605 1646171 := bstep (se 1 (by rfl) ⟨1234628, by rfl⟩ : syracuseStep 1646171 = 2469257) B2469257
theorem B2596495 : Blo 1024605 2596495 := bstep (se 1 (by rfl) ⟨1947371, by rfl⟩ : syracuseStep 2596495 = 3894743) B3894743
theorem B1024615 : Blo 1024605 1024615 := bstep (se 1 (by rfl) ⟨768461, by rfl⟩ : syracuseStep 1024615 = 1536923) B1536923
theorem B1024879 : Blo 1024605 1024879 := bstep (se 1 (by rfl) ⟨768659, by rfl⟩ : syracuseStep 1024879 = 1537319) B1537319
theorem B2925467 : Blo 1024605 2925467 := bstep (se 1 (by rfl) ⟨2194100, by rfl⟩ : syracuseStep 2925467 = 4388201) B4388201
theorem B1024935 : Blo 1024605 1024935 := bstep (se 1 (by rfl) ⟨768701, by rfl⟩ : syracuseStep 1024935 = 1537403) B1537403
theorem B1025019 : Blo 1024605 1025019 := bstep (se 1 (by rfl) ⟨768764, by rfl⟩ : syracuseStep 1025019 = 1537529) B1537529
theorem B1025087 : Blo 1024605 1025087 := bstep (se 1 (by rfl) ⟨768815, by rfl⟩ : syracuseStep 1025087 = 1537631) B1537631
theorem B1025231 : Blo 1024605 1025231 := bstep (se 1 (by rfl) ⟨768923, by rfl⟩ : syracuseStep 1025231 = 1537847) B1537847
theorem B2598095 : Blo 1024605 2598095 := bstep (se 1 (by rfl) ⟨1948571, by rfl⟩ : syracuseStep 2598095 = 3897143) B3897143
theorem B7021961 : Blo 1024605 7021961 := bstep (se 2 (by rfl) ⟨2633235, by rfl⟩ : syracuseStep 7021961 = 5266471) B5266471
theorem B1025435 : Blo 1024605 1025435 := bstep (se 1 (by rfl) ⟨769076, by rfl⟩ : syracuseStep 1025435 = 1538153) B1538153
theorem B2598419 : Blo 1024605 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B7808561 : Blo 1024605 7808561 := bstep (se 2 (by rfl) ⟨2928210, by rfl⟩ : syracuseStep 7808561 = 5856421) B5856421
theorem B1025647 : Blo 1024605 1025647 := bstep (se 1 (by rfl) ⟨769235, by rfl⟩ : syracuseStep 1025647 = 1538471) B1538471
theorem B5187239 : Blo 1024605 5187239 := bstep (se 1 (by rfl) ⟨3890429, by rfl⟩ : syracuseStep 5187239 = 7780859) B7780859
theorem B1025703 : Blo 1024605 1025703 := bstep (se 1 (by rfl) ⟨769277, by rfl⟩ : syracuseStep 1025703 = 1538555) B1538555
theorem B2467547 : Blo 1024605 2467547 := bstep (se 1 (by rfl) ⟨1850660, by rfl⟩ : syracuseStep 2467547 = 3701321) B3701321
theorem B1025787 : Blo 1024605 1025787 := bstep (se 1 (by rfl) ⟨769340, by rfl⟩ : syracuseStep 1025787 = 1538681) B1538681
theorem B8333063 : Blo 1024605 8333063 := bstep (se 1 (by rfl) ⟨6249797, by rfl⟩ : syracuseStep 8333063 = 12499595) B12499595
theorem B2926343 : Blo 1024605 2926343 := bstep (se 1 (by rfl) ⟨2194757, by rfl⟩ : syracuseStep 2926343 = 4389515) B4389515
theorem B1025823 : Blo 1024605 1025823 := bstep (se 1 (by rfl) ⟨769367, by rfl⟩ : syracuseStep 1025823 = 1538735) B1538735
theorem B1025855 : Blo 1024605 1025855 := bstep (se 1 (by rfl) ⟨769391, by rfl⟩ : syracuseStep 1025855 = 1538783) B1538783
theorem B1156927 : Blo 1024605 1156927 := bstep (se 1 (by rfl) ⟨867695, by rfl⟩ : syracuseStep 1156927 = 1735391) B1735391
theorem B5187401 : Blo 1024605 5187401 := bstep (se 2 (by rfl) ⟨1945275, by rfl⟩ : syracuseStep 5187401 = 3890551) B3890551
theorem B1026031 : Blo 1024605 1026031 := bstep (se 1 (by rfl) ⟨769523, by rfl⟩ : syracuseStep 1026031 = 1539047) B1539047
theorem B11675663 : Blo 1024605 11675663 := bstep (se 1 (by rfl) ⟨8756747, by rfl⟩ : syracuseStep 11675663 = 17513495) B17513495
theorem B1026203 : Blo 1024605 1026203 := bstep (se 1 (by rfl) ⟨769652, by rfl⟩ : syracuseStep 1026203 = 1539305) B1539305
theorem B1026239 : Blo 1024605 1026239 := bstep (se 1 (by rfl) ⟨769679, by rfl⟩ : syracuseStep 1026239 = 1539359) B1539359
theorem B1026351 : Blo 1024605 1026351 := bstep (se 1 (by rfl) ⟨769763, by rfl⟩ : syracuseStep 1026351 = 1539527) B1539527
theorem B1026587 : Blo 1024605 1026587 := bstep (se 1 (by rfl) ⟨769940, by rfl⟩ : syracuseStep 1026587 = 1539881) B1539881
theorem B1026591 : Blo 1024605 1026591 := bstep (se 1 (by rfl) ⟨769943, by rfl⟩ : syracuseStep 1026591 = 1539887) B1539887
theorem B2599735 : Blo 1024605 2599735 := bstep (se 1 (by rfl) ⟨1949801, by rfl⟩ : syracuseStep 2599735 = 3899603) B3899603
theorem B1026907 : Blo 1024605 1026907 := bstep (se 1 (by rfl) ⟨770180, by rfl⟩ : syracuseStep 1026907 = 1540361) B1540361
theorem B1026975 : Blo 1024605 1026975 := bstep (se 1 (by rfl) ⟨770231, by rfl⟩ : syracuseStep 1026975 = 1540463) B1540463
theorem B1027119 : Blo 1024605 1027119 := bstep (se 1 (by rfl) ⟨770339, by rfl⟩ : syracuseStep 1027119 = 1540679) B1540679
theorem B11873347 : Blo 1024605 11873347 := bstep (se 1 (by rfl) ⟨8905010, by rfl⟩ : syracuseStep 11873347 = 17810021) B17810021
theorem B1027143 : Blo 1024605 1027143 := bstep (se 1 (by rfl) ⟨770357, by rfl⟩ : syracuseStep 1027143 = 1540715) B1540715
theorem B1387703 : Blo 1024605 1387703 := bstep (se 1 (by rfl) ⟨1040777, by rfl⟩ : syracuseStep 1387703 = 2081555) B2081555
theorem B1027295 : Blo 1024605 1027295 := bstep (se 1 (by rfl) ⟨770471, by rfl⟩ : syracuseStep 1027295 = 1540943) B1540943
theorem B3124669 : Blo 1024605 3124669 := bstep (se 3 (by rfl) ⟨585875, by rfl⟩ : syracuseStep 3124669 = 1171751) B1171751
theorem B1027559 : Blo 1024605 1027559 := bstep (se 1 (by rfl) ⟨770669, by rfl⟩ : syracuseStep 1027559 = 1541339) B1541339
theorem B2469371 : Blo 1024605 2469371 := bstep (se 1 (by rfl) ⟨1852028, by rfl⟩ : syracuseStep 2469371 = 3704057) B3704057
theorem B8334905 : Blo 1024605 8334905 := bstep (se 2 (by rfl) ⟨3125589, by rfl⟩ : syracuseStep 8334905 = 6251179) B6251179
theorem B23703101 : Blo 1024605 23703101 := bstep (se 3 (by rfl) ⟨4444331, by rfl⟩ : syracuseStep 23703101 = 8888663) B8888663
theorem B29994569 : Blo 1024605 29994569 := bstep (se 2 (by rfl) ⟨11247963, by rfl⟩ : syracuseStep 29994569 = 22495927) B22495927
theorem B1027675 : Blo 1024605 1027675 := bstep (se 1 (by rfl) ⟨770756, by rfl⟩ : syracuseStep 1027675 = 1541513) B1541513
theorem B5844575 : Blo 1024605 5844575 := bstep (se 1 (by rfl) ⟨4383431, by rfl⟩ : syracuseStep 5844575 = 8766863) B8766863
theorem B1027911 : Blo 1024605 1027911 := bstep (se 1 (by rfl) ⟨770933, by rfl⟩ : syracuseStep 1027911 = 1541867) B1541867
theorem B2306015 : Blo 1024605 2306015 := bstep (se 1 (by rfl) ⟨1729511, by rfl⟩ : syracuseStep 2306015 = 3459023) B3459023
theorem B1028063 : Blo 1024605 1028063 := bstep (se 1 (by rfl) ⟨771047, by rfl⟩ : syracuseStep 1028063 = 1542095) B1542095
theorem B2633851 : Blo 1024605 2633851 := bstep (se 1 (by rfl) ⟨1975388, by rfl⟩ : syracuseStep 2633851 = 3950777) B3950777
theorem B1028327 : Blo 1024605 1028327 := bstep (se 1 (by rfl) ⟨771245, by rfl⟩ : syracuseStep 1028327 = 1542491) B1542491
theorem B49983749 : Blo 1024605 49983749 := bstep (se 4 (by rfl) ⟨4685976, by rfl⟩ : syracuseStep 49983749 = 9371953) B9371953
theorem B1028479 : Blo 1024605 1028479 := bstep (se 1 (by rfl) ⟨771359, by rfl⟩ : syracuseStep 1028479 = 1542719) B1542719
theorem B10531225 : Blo 1024605 10531225 := bstep (se 2 (by rfl) ⟨3949209, by rfl⟩ : syracuseStep 10531225 = 7898419) B7898419
theorem B3289511 : Blo 1024605 3289511 := bstep (se 1 (by rfl) ⟨2467133, by rfl⟩ : syracuseStep 3289511 = 4934267) B4934267
theorem B1028559 : Blo 1024605 1028559 := bstep (se 1 (by rfl) ⟨771419, by rfl⟩ : syracuseStep 1028559 = 1542839) B1542839
theorem B2306663 : Blo 1024605 2306663 := bstep (se 1 (by rfl) ⟨1729997, by rfl⟩ : syracuseStep 2306663 = 3459995) B3459995
theorem B168571637 : Blo 1024605 168571637 := bstep (se 5 (by rfl) ⟨7901795, by rfl⟩ : syracuseStep 168571637 = 15803591) B15803591
theorem B20034469 : Blo 1024605 20034469 := bstep (se 4 (by rfl) ⟨1878231, by rfl⟩ : syracuseStep 20034469 = 3756463) B3756463
theorem B1848425 : Blo 1024605 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B5846215 : Blo 1024605 5846215 := bstep (se 1 (by rfl) ⟨4384661, by rfl⟩ : syracuseStep 5846215 = 8769323) B8769323
theorem B2307347 : Blo 1024605 2307347 := bstep (se 1 (by rfl) ⟨1730510, by rfl⟩ : syracuseStep 2307347 = 3461021) B3461021
theorem B2307419 : Blo 1024605 2307419 := bstep (se 1 (by rfl) ⟨1730564, by rfl⟩ : syracuseStep 2307419 = 3461129) B3461129
theorem B7386491 : Blo 1024605 7386491 := bstep (se 1 (by rfl) ⟨5539868, by rfl⟩ : syracuseStep 7386491 = 11079737) B11079737
theorem B6239753 : Blo 1024605 6239753 := bstep (se 2 (by rfl) ⟨2339907, by rfl⟩ : syracuseStep 6239753 = 4679815) B4679815
theorem B189347543 : Blo 1024605 189347543 := bstep (se 1 (by rfl) ⟨142010657, by rfl⟩ : syracuseStep 189347543 = 284021315) B284021315
theorem B6567743 : Blo 1024605 6567743 := bstep (se 1 (by rfl) ⟨4925807, by rfl⟩ : syracuseStep 6567743 = 9851615) B9851615
theorem B2307977 : Blo 1024605 2307977 := bstep (se 2 (by rfl) ⟨865491, by rfl⟩ : syracuseStep 2307977 = 1730983) B1730983
theorem B2308193 : Blo 1024605 2308193 := bstep (se 2 (by rfl) ⟨865572, by rfl⟩ : syracuseStep 2308193 = 1731145) B1731145
theorem B18725093 : Blo 1024605 18725093 := bstep (se 4 (by rfl) ⟨1755477, by rfl⟩ : syracuseStep 18725093 = 3510955) B3510955
theorem B1947881 : Blo 1024605 1947881 := bstep (se 2 (by rfl) ⟨730455, by rfl⟩ : syracuseStep 1947881 = 1460911) B1460911
theorem B6568229 : Blo 1024605 6568229 := bstep (se 4 (by rfl) ⟨615771, by rfl⟩ : syracuseStep 6568229 = 1231543) B1231543
theorem B11680037 : Blo 1024605 11680037 := bstep (se 4 (by rfl) ⟨1095003, by rfl⟩ : syracuseStep 11680037 = 2190007) B2190007
theorem B3160937 : Blo 1024605 3160937 := bstep (se 2 (by rfl) ⟨1185351, by rfl⟩ : syracuseStep 3160937 = 2370703) B2370703
theorem B63159193 : Blo 1024605 63159193 := bstep (se 2 (by rfl) ⟨23684697, by rfl⟩ : syracuseStep 63159193 = 47369395) B47369395
theorem B3750857 : Blo 1024605 3750857 := bstep (se 2 (by rfl) ⟨1406571, by rfl⟩ : syracuseStep 3750857 = 2813143) B2813143
theorem B6569383 : Blo 1024605 6569383 := bstep (se 1 (by rfl) ⟨4927037, by rfl⟩ : syracuseStep 6569383 = 9854075) B9854075
theorem B2309543 : Blo 1024605 2309543 := bstep (se 1 (by rfl) ⟨1732157, by rfl⟩ : syracuseStep 2309543 = 3464315) B3464315
theorem B13319741 : Blo 1024605 13319741 := bstep (se 3 (by rfl) ⟨2497451, by rfl⟩ : syracuseStep 13319741 = 4994903) B4994903
theorem B3292751 : Blo 1024605 3292751 := bstep (se 1 (by rfl) ⟨2469563, by rfl⟩ : syracuseStep 3292751 = 4939127) B4939127
theorem B2309723 : Blo 1024605 2309723 := bstep (se 1 (by rfl) ⟨1732292, by rfl⟩ : syracuseStep 2309723 = 3464585) B3464585
theorem B30031607 : Blo 1024605 30031607 := bstep (se 1 (by rfl) ⟨22523705, by rfl⟩ : syracuseStep 30031607 = 45047411) B45047411
theorem B2310011 : Blo 1024605 2310011 := bstep (se 1 (by rfl) ⟨1732508, by rfl⟩ : syracuseStep 2310011 = 3465017) B3465017
theorem B3293099 : Blo 1024605 3293099 := bstep (se 1 (by rfl) ⟨2469824, by rfl⟩ : syracuseStep 3293099 = 4939649) B4939649
theorem B2310497 : Blo 1024605 2310497 := bstep (se 2 (by rfl) ⟨866436, by rfl⟩ : syracuseStep 2310497 = 1732873) B1732873
theorem B2310587 : Blo 1024605 2310587 := bstep (se 1 (by rfl) ⟨1732940, by rfl⟩ : syracuseStep 2310587 = 3465881) B3465881
theorem B1950151 : Blo 1024605 1950151 := bstep (se 1 (by rfl) ⟨1462613, by rfl⟩ : syracuseStep 1950151 = 2925227) B2925227
theorem B9356705 : Blo 1024605 9356705 := bstep (se 2 (by rfl) ⟨3508764, by rfl⟩ : syracuseStep 9356705 = 7017529) B7017529
theorem B2311595 : Blo 1024605 2311595 := bstep (se 1 (by rfl) ⟨1733696, by rfl⟩ : syracuseStep 2311595 = 3467393) B3467393
theorem B9848267 : Blo 1024605 9848267 := bstep (se 1 (by rfl) ⟨7386200, by rfl⟩ : syracuseStep 9848267 = 14772401) B14772401
theorem B1853039 : Blo 1024605 1853039 := bstep (se 1 (by rfl) ⟨1389779, by rfl⟩ : syracuseStep 1853039 = 2779559) B2779559
theorem B2311847 : Blo 1024605 2311847 := bstep (se 1 (by rfl) ⟨1733885, by rfl⟩ : syracuseStep 2311847 = 3467771) B3467771
theorem B1558235 : Blo 1024605 1558235 := bstep (se 1 (by rfl) ⟨1168676, by rfl⟩ : syracuseStep 1558235 = 2337353) B2337353
theorem B379012931 : Blo 1024605 379012931 := bstep (se 1 (by rfl) ⟨284259698, by rfl⟩ : syracuseStep 379012931 = 568519397) B568519397
theorem B2967425 : Blo 1024605 2967425 := bstep (se 2 (by rfl) ⟨1112784, by rfl⟩ : syracuseStep 2967425 = 2225569) B2225569
theorem B2312135 : Blo 1024605 2312135 := bstep (se 1 (by rfl) ⟨1734101, by rfl⟩ : syracuseStep 2312135 = 3468203) B3468203
theorem B9848881 : Blo 1024605 9848881 := bstep (se 2 (by rfl) ⟨3693330, by rfl⟩ : syracuseStep 9848881 = 7386661) B7386661
theorem B13158449 : Blo 1024605 13158449 := bstep (se 2 (by rfl) ⟨4934418, by rfl⟩ : syracuseStep 13158449 = 9868837) B9868837
theorem B6670471 : Blo 1024605 6670471 := bstep (se 1 (by rfl) ⟨5002853, by rfl⟩ : syracuseStep 6670471 = 10005707) B10005707
theorem B5195987 : Blo 1024605 5195987 := bstep (se 1 (by rfl) ⟨3896990, by rfl⟩ : syracuseStep 5195987 = 7793981) B7793981
theorem B2312441 : Blo 1024605 2312441 := bstep (se 2 (by rfl) ⟨867165, by rfl⟩ : syracuseStep 2312441 = 1734331) B1734331
theorem B2312495 : Blo 1024605 2312495 := bstep (se 1 (by rfl) ⟨1734371, by rfl⟩ : syracuseStep 2312495 = 3468743) B3468743
theorem B2771339 : Blo 1024605 2771339 := bstep (se 1 (by rfl) ⟨2078504, by rfl⟩ : syracuseStep 2771339 = 4157009) B4157009
theorem B53365229 : Blo 1024605 53365229 := bstep (se 3 (by rfl) ⟨10005980, by rfl⟩ : syracuseStep 53365229 = 20011961) B20011961
theorem B2312711 : Blo 1024605 2312711 := bstep (se 1 (by rfl) ⟨1734533, by rfl⟩ : syracuseStep 2312711 = 3469067) B3469067
theorem B2312891 : Blo 1024605 2312891 := bstep (se 1 (by rfl) ⟨1734668, by rfl⟩ : syracuseStep 2312891 = 3469337) B3469337
theorem B24988571 : Blo 1024605 24988571 := bstep (se 1 (by rfl) ⟨18741428, by rfl⟩ : syracuseStep 24988571 = 37482857) B37482857
theorem B1297387 : Blo 1024605 1297387 := bstep (se 1 (by rfl) ⟨973040, by rfl⟩ : syracuseStep 1297387 = 1946081) B1946081
theorem B3460319 : Blo 1024605 3460319 := bstep (se 1 (by rfl) ⟨2595239, by rfl⟩ : syracuseStep 3460319 = 5190479) B5190479
theorem B3460535 : Blo 1024605 3460535 := bstep (se 1 (by rfl) ⟨2595401, by rfl⟩ : syracuseStep 3460535 = 5190803) B5190803
theorem B7032253 : Blo 1024605 7032253 := bstep (se 3 (by rfl) ⟨1318547, by rfl⟩ : syracuseStep 7032253 = 2637095) B2637095
theorem B2313719 : Blo 1024605 2313719 := bstep (se 1 (by rfl) ⟨1735289, by rfl⟩ : syracuseStep 2313719 = 3470579) B3470579
theorem B2313791 : Blo 1024605 2313791 := bstep (se 1 (by rfl) ⟨1735343, by rfl⟩ : syracuseStep 2313791 = 3470687) B3470687
theorem B5197607 : Blo 1024605 5197607 := bstep (se 1 (by rfl) ⟨3898205, by rfl⟩ : syracuseStep 5197607 = 7796411) B7796411
theorem B1462055 : Blo 1024605 1462055 := bstep (se 1 (by rfl) ⟨1096541, by rfl⟩ : syracuseStep 1462055 = 2193083) B2193083
theorem B7917385 : Blo 1024605 7917385 := bstep (se 2 (by rfl) ⟨2969019, by rfl⟩ : syracuseStep 7917385 = 5938039) B5938039
theorem B4378511 : Blo 1024605 4378511 := bstep (se 1 (by rfl) ⟨3283883, by rfl⟩ : syracuseStep 4378511 = 6567767) B6567767
theorem B1757099 : Blo 1024605 1757099 := bstep (se 1 (by rfl) ⟨1317824, by rfl⟩ : syracuseStep 1757099 = 2635649) B2635649
theorem B11685869 : Blo 1024605 11685869 := bstep (se 3 (by rfl) ⟨2191100, by rfl⟩ : syracuseStep 11685869 = 4382201) B4382201
theorem B3953231 : Blo 1024605 3953231 := bstep (se 1 (by rfl) ⟨2964923, by rfl⟩ : syracuseStep 3953231 = 5929847) B5929847
theorem B6574715 : Blo 1024605 6574715 := bstep (se 1 (by rfl) ⟨4931036, by rfl⟩ : syracuseStep 6574715 = 9862073) B9862073
theorem B6574841 : Blo 1024605 6574841 := bstep (se 2 (by rfl) ⟨2465565, by rfl⟩ : syracuseStep 6574841 = 4931131) B4931131
theorem B4379453 : Blo 1024605 4379453 := bstep (se 3 (by rfl) ⟨821147, by rfl⟩ : syracuseStep 4379453 = 1642295) B1642295
theorem B5198903 : Blo 1024605 5198903 := bstep (se 1 (by rfl) ⟨3899177, by rfl⟩ : syracuseStep 5198903 = 7798355) B7798355
theorem B6575201 : Blo 1024605 6575201 := bstep (se 2 (by rfl) ⟨2465700, by rfl⟩ : syracuseStep 6575201 = 4931401) B4931401
theorem B4674667 : Blo 1024605 4674667 := bstep (se 1 (by rfl) ⟨3506000, by rfl⟩ : syracuseStep 4674667 = 7012001) B7012001
theorem B7787663 : Blo 1024605 7787663 := bstep (se 1 (by rfl) ⟨5840747, by rfl⟩ : syracuseStep 7787663 = 11681495) B11681495
theorem B4936879 : Blo 1024605 4936879 := bstep (se 1 (by rfl) ⟨3702659, by rfl⟩ : syracuseStep 4936879 = 7405319) B7405319
theorem B4937051 : Blo 1024605 4937051 := bstep (se 1 (by rfl) ⟨3702788, by rfl⟩ : syracuseStep 4937051 = 7405577) B7405577
theorem B3757403 : Blo 1024605 3757403 := bstep (se 1 (by rfl) ⟨2818052, by rfl⟩ : syracuseStep 3757403 = 5636105) B5636105
theorem B53302643 : Blo 1024605 53302643 := bstep (se 1 (by rfl) ⟨39976982, by rfl⟩ : syracuseStep 53302643 = 79953965) B79953965
theorem B28431767 : Blo 1024605 28431767 := bstep (se 1 (by rfl) ⟨21323825, by rfl⟩ : syracuseStep 28431767 = 42647651) B42647651
theorem B1463707 : Blo 1024605 1463707 := bstep (se 1 (by rfl) ⟨1097780, by rfl⟩ : syracuseStep 1463707 = 2195561) B2195561
theorem B3462587 : Blo 1024605 3462587 := bstep (se 1 (by rfl) ⟨2596940, by rfl⟩ : syracuseStep 3462587 = 5193881) B5193881
theorem B3463127 : Blo 1024605 3463127 := bstep (se 1 (by rfl) ⟨2597345, by rfl⟩ : syracuseStep 3463127 = 5194691) B5194691
theorem B4380767 : Blo 1024605 4380767 := bstep (se 1 (by rfl) ⟨3285575, by rfl⟩ : syracuseStep 4380767 = 6571151) B6571151
theorem B3463613 : Blo 1024605 3463613 := bstep (se 3 (by rfl) ⟨649427, by rfl⟩ : syracuseStep 3463613 = 1298855) B1298855
theorem B5790455 : Blo 1024605 5790455 := bstep (se 1 (by rfl) ⟨4342841, by rfl⟩ : syracuseStep 5790455 = 8685683) B8685683
theorem B6675305 : Blo 1024605 6675305 := bstep (se 2 (by rfl) ⟨2503239, by rfl⟩ : syracuseStep 6675305 = 5006479) B5006479
theorem B3464477 : Blo 1024605 3464477 := bstep (se 3 (by rfl) ⟨649589, by rfl⟩ : syracuseStep 3464477 = 1299179) B1299179
theorem B7396811 : Blo 1024605 7396811 := bstep (se 1 (by rfl) ⟨5547608, by rfl⟩ : syracuseStep 7396811 = 11095217) B11095217
theorem B112451165 : Blo 1024605 112451165 := bstep (se 3 (by rfl) ⟨21084593, by rfl⟩ : syracuseStep 112451165 = 42169187) B42169187
theorem B11690243 : Blo 1024605 11690243 := bstep (se 1 (by rfl) ⟨8767682, by rfl⟩ : syracuseStep 11690243 = 17535365) B17535365
theorem B3465503 : Blo 1024605 3465503 := bstep (se 1 (by rfl) ⟨2599127, by rfl⟩ : syracuseStep 3465503 = 5198255) B5198255
theorem B1729127 : Blo 1024605 1729127 := bstep (se 1 (by rfl) ⟨1296845, by rfl⟩ : syracuseStep 1729127 = 2593691) B2593691
theorem B6578941 : Blo 1024605 6578941 := bstep (se 3 (by rfl) ⟨1233551, by rfl⟩ : syracuseStep 6578941 = 2467103) B2467103
theorem B1729289 : Blo 1024605 1729289 := bstep (se 2 (by rfl) ⟨648483, by rfl⟩ : syracuseStep 1729289 = 1296967) B1296967
theorem B3466151 : Blo 1024605 3466151 := bstep (se 1 (by rfl) ⟨2599613, by rfl⟩ : syracuseStep 3466151 = 5199227) B5199227
theorem B1729883 : Blo 1024605 1729883 := bstep (se 1 (by rfl) ⟨1297412, by rfl⟩ : syracuseStep 1729883 = 2594825) B2594825
theorem B3466745 : Blo 1024605 3466745 := bstep (se 2 (by rfl) ⟨1300029, by rfl⟩ : syracuseStep 3466745 = 2600059) B2600059
theorem B48129551 : Blo 1024605 48129551 := bstep (se 1 (by rfl) ⟨36097163, by rfl⟩ : syracuseStep 48129551 = 72194327) B72194327
theorem B1730119 : Blo 1024605 1730119 := bstep (se 1 (by rfl) ⟨1297589, by rfl⟩ : syracuseStep 1730119 = 2595179) B2595179
theorem B3467015 : Blo 1024605 3467015 := bstep (se 1 (by rfl) ⟨2600261, by rfl⟩ : syracuseStep 3467015 = 5200523) B5200523
theorem B1730335 : Blo 1024605 1730335 := bstep (se 1 (by rfl) ⟨1297751, by rfl⟩ : syracuseStep 1730335 = 2595503) B2595503
theorem B3467069 : Blo 1024605 3467069 := bstep (se 3 (by rfl) ⟨650075, by rfl⟩ : syracuseStep 3467069 = 1300151) B1300151
theorem B2189153 : Blo 1024605 2189153 := bstep (se 2 (by rfl) ⟨820932, by rfl⟩ : syracuseStep 2189153 = 1641865) B1641865
theorem B1730551 : Blo 1024605 1730551 := bstep (se 1 (by rfl) ⟨1297913, by rfl⟩ : syracuseStep 1730551 = 2595827) B2595827
theorem B1730855 : Blo 1024605 1730855 := bstep (se 1 (by rfl) ⟨1298141, by rfl⟩ : syracuseStep 1730855 = 2596283) B2596283
theorem B43379003 : Blo 1024605 43379003 := bstep (se 1 (by rfl) ⟨32534252, by rfl⟩ : syracuseStep 43379003 = 65068505) B65068505
theorem B4385755 : Blo 1024605 4385755 := bstep (se 1 (by rfl) ⟨3289316, by rfl⟩ : syracuseStep 4385755 = 6578633) B6578633
theorem B5008391 : Blo 1024605 5008391 := bstep (se 1 (by rfl) ⟨3756293, by rfl⟩ : syracuseStep 5008391 = 7512587) B7512587
theorem B1731631 : Blo 1024605 1731631 := bstep (se 1 (by rfl) ⟨1298723, by rfl⟩ : syracuseStep 1731631 = 2597447) B2597447
theorem B4385927 : Blo 1024605 4385927 := bstep (se 1 (by rfl) ⟨3289445, by rfl⟩ : syracuseStep 4385927 = 6578891) B6578891
theorem B1732009 : Blo 1024605 1732009 := bstep (se 2 (by rfl) ⟨649503, by rfl⟩ : syracuseStep 1732009 = 1299007) B1299007
theorem B1732475 : Blo 1024605 1732475 := bstep (se 1 (by rfl) ⟨1299356, by rfl⟩ : syracuseStep 1732475 = 2598713) B2598713
theorem B31617049 : Blo 1024605 31617049 := bstep (se 2 (by rfl) ⟨11856393, by rfl⟩ : syracuseStep 31617049 = 23712787) B23712787
theorem B6582323 : Blo 1024605 6582323 := bstep (se 1 (by rfl) ⟨4936742, by rfl⟩ : syracuseStep 6582323 = 9873485) B9873485
theorem B3469499 : Blo 1024605 3469499 := bstep (se 1 (by rfl) ⟨2602124, by rfl⟩ : syracuseStep 3469499 = 5204249) B5204249
theorem B16675145 : Blo 1024605 16675145 := bstep (se 2 (by rfl) ⟨6253179, by rfl⟩ : syracuseStep 16675145 = 12506359) B12506359
theorem B8778071 : Blo 1024605 8778071 := bstep (se 1 (by rfl) ⟨6583553, by rfl⟩ : syracuseStep 8778071 = 13167107) B13167107
theorem B112325039 : Blo 1024605 112325039 := bstep (se 1 (by rfl) ⟨84243779, by rfl⟩ : syracuseStep 112325039 = 168487559) B168487559
theorem B3469985 : Blo 1024605 3469985 := bstep (se 2 (by rfl) ⟨1301244, by rfl⟩ : syracuseStep 3469985 = 2602489) B2602489
theorem B43315897 : Blo 1024605 43315897 := bstep (se 2 (by rfl) ⟨16243461, by rfl⟩ : syracuseStep 43315897 = 32486923) B32486923
theorem B1536935 : Blo 1024605 1536935 := bstep (se 1 (by rfl) ⟨1152701, by rfl⟩ : syracuseStep 1536935 = 2305403) B2305403
theorem B1537019 : Blo 1024605 1537019 := bstep (se 1 (by rfl) ⟨1152764, by rfl⟩ : syracuseStep 1537019 = 2305529) B2305529
theorem B1537079 : Blo 1024605 1537079 := bstep (se 1 (by rfl) ⟨1152809, by rfl⟩ : syracuseStep 1537079 = 2305619) B2305619
theorem B1733737 : Blo 1024605 1733737 := bstep (se 2 (by rfl) ⟨650151, by rfl⟩ : syracuseStep 1733737 = 1300303) B1300303
theorem B6255755 : Blo 1024605 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B1537199 : Blo 1024605 1537199 := bstep (se 1 (by rfl) ⟨1152899, by rfl⟩ : syracuseStep 1537199 = 2305799) B2305799
theorem B3470849 : Blo 1024605 3470849 := bstep (se 2 (by rfl) ⟨1301568, by rfl⟩ : syracuseStep 3470849 = 2603137) B2603137
theorem B1537607 : Blo 1024605 1537607 := bstep (se 1 (by rfl) ⟨1153205, by rfl⟩ : syracuseStep 1537607 = 2306411) B2306411
theorem B1537703 : Blo 1024605 1537703 := bstep (se 1 (by rfl) ⟨1153277, by rfl⟩ : syracuseStep 1537703 = 2306555) B2306555
theorem B1734311 : Blo 1024605 1734311 := bstep (se 1 (by rfl) ⟨1300733, by rfl⟩ : syracuseStep 1734311 = 2601467) B2601467
theorem B1537787 : Blo 1024605 1537787 := bstep (se 1 (by rfl) ⟨1153340, by rfl⟩ : syracuseStep 1537787 = 2306681) B2306681
theorem B14808845 : Blo 1024605 14808845 := bstep (se 3 (by rfl) ⟨2776658, by rfl⟩ : syracuseStep 14808845 = 5553317) B5553317
theorem B1537823 : Blo 1024605 1537823 := bstep (se 1 (by rfl) ⟨1153367, by rfl⟩ : syracuseStep 1537823 = 2306735) B2306735
theorem B1537871 : Blo 1024605 1537871 := bstep (se 1 (by rfl) ⟨1153403, by rfl⟩ : syracuseStep 1537871 = 2306807) B2306807
theorem B1537991 : Blo 1024605 1537991 := bstep (se 1 (by rfl) ⟨1153493, by rfl⟩ : syracuseStep 1537991 = 2306987) B2306987
theorem B3471335 : Blo 1024605 3471335 := bstep (se 1 (by rfl) ⟨2603501, by rfl⟩ : syracuseStep 3471335 = 5207003) B5207003
theorem B7403501 : Blo 1024605 7403501 := bstep (se 3 (by rfl) ⟨1388156, by rfl⟩ : syracuseStep 7403501 = 2776313) B2776313
theorem B3471443 : Blo 1024605 3471443 := bstep (se 1 (by rfl) ⟨2603582, by rfl⟩ : syracuseStep 3471443 = 5207165) B5207165
theorem B1538345 : Blo 1024605 1538345 := bstep (se 2 (by rfl) ⟨576879, by rfl⟩ : syracuseStep 1538345 = 1153759) B1153759
theorem B1538351 : Blo 1024605 1538351 := bstep (se 1 (by rfl) ⟨1153763, by rfl⟩ : syracuseStep 1538351 = 2307527) B2307527
theorem B1734959 : Blo 1024605 1734959 := bstep (se 1 (by rfl) ⟨1301219, by rfl⟩ : syracuseStep 1734959 = 2602439) B2602439
theorem B1735195 : Blo 1024605 1735195 := bstep (se 1 (by rfl) ⟨1301396, by rfl⟩ : syracuseStep 1735195 = 2602793) B2602793
theorem B1538591 : Blo 1024605 1538591 := bstep (se 1 (by rfl) ⟨1153943, by rfl⟩ : syracuseStep 1538591 = 2307887) B2307887
theorem B2194057 : Blo 1024605 2194057 := bstep (se 2 (by rfl) ⟨822771, by rfl⟩ : syracuseStep 2194057 = 1645543) B1645543
theorem B1538975 : Blo 1024605 1538975 := bstep (se 1 (by rfl) ⟨1154231, by rfl⟩ : syracuseStep 1538975 = 2308463) B2308463
theorem B1539023 : Blo 1024605 1539023 := bstep (se 1 (by rfl) ⟨1154267, by rfl⟩ : syracuseStep 1539023 = 2308535) B2308535
theorem B1539113 : Blo 1024605 1539113 := bstep (se 2 (by rfl) ⟨577167, by rfl⟩ : syracuseStep 1539113 = 1154335) B1154335
theorem B1539119 : Blo 1024605 1539119 := bstep (se 1 (by rfl) ⟨1154339, by rfl⟩ : syracuseStep 1539119 = 2308679) B2308679
theorem B1539143 : Blo 1024605 1539143 := bstep (se 1 (by rfl) ⟨1154357, by rfl⟩ : syracuseStep 1539143 = 2308715) B2308715
theorem B1539407 : Blo 1024605 1539407 := bstep (se 1 (by rfl) ⟨1154555, by rfl⟩ : syracuseStep 1539407 = 2309111) B2309111
theorem B1539497 : Blo 1024605 1539497 := bstep (se 2 (by rfl) ⟨577311, by rfl⟩ : syracuseStep 1539497 = 1154623) B1154623
theorem B1539647 : Blo 1024605 1539647 := bstep (se 1 (by rfl) ⟨1154735, by rfl⟩ : syracuseStep 1539647 = 2309471) B2309471
theorem B6422125 : Blo 1024605 6422125 := bstep (se 3 (by rfl) ⟨1204148, by rfl⟩ : syracuseStep 6422125 = 2408297) B2408297
theorem B74284789 : Blo 1024605 74284789 := bstep (se 5 (by rfl) ⟨3482099, by rfl⟩ : syracuseStep 74284789 = 6964199) B6964199
theorem B1539911 : Blo 1024605 1539911 := bstep (se 1 (by rfl) ⟨1154933, by rfl⟩ : syracuseStep 1539911 = 2309867) B2309867
theorem B1539995 : Blo 1024605 1539995 := bstep (se 1 (by rfl) ⟨1154996, by rfl⟩ : syracuseStep 1539995 = 2309993) B2309993
theorem B1540331 : Blo 1024605 1540331 := bstep (se 1 (by rfl) ⟨1155248, by rfl⟩ : syracuseStep 1540331 = 2310497) B2310497
theorem B1540391 : Blo 1024605 1540391 := bstep (se 1 (by rfl) ⟨1155293, by rfl⟩ : syracuseStep 1540391 = 2310587) B2310587
theorem B1541063 : Blo 1024605 1541063 := bstep (se 1 (by rfl) ⟨1155797, by rfl⟩ : syracuseStep 1541063 = 2311595) B2311595
theorem B1541231 : Blo 1024605 1541231 := bstep (se 1 (by rfl) ⟨1155923, by rfl⟩ : syracuseStep 1541231 = 2311847) B2311847
theorem B252675287 : Blo 1024605 252675287 := bstep (se 1 (by rfl) ⟨189506465, by rfl⟩ : syracuseStep 252675287 = 379012931) B379012931
theorem B1541423 : Blo 1024605 1541423 := bstep (se 1 (by rfl) ⟨1156067, by rfl⟩ : syracuseStep 1541423 = 2312135) B2312135
theorem B1541627 : Blo 1024605 1541627 := bstep (se 1 (by rfl) ⟨1156220, by rfl⟩ : syracuseStep 1541627 = 2312441) B2312441
theorem B1541663 : Blo 1024605 1541663 := bstep (se 1 (by rfl) ⟨1156247, by rfl⟩ : syracuseStep 1541663 = 2312495) B2312495
theorem B1541807 : Blo 1024605 1541807 := bstep (se 1 (by rfl) ⟨1156355, by rfl⟩ : syracuseStep 1541807 = 2312711) B2312711
theorem B1541927 : Blo 1024605 1541927 := bstep (se 1 (by rfl) ⟨1156445, by rfl⟩ : syracuseStep 1541927 = 2312891) B2312891
theorem B1542479 : Blo 1024605 1542479 := bstep (se 1 (by rfl) ⟨1156859, by rfl⟩ : syracuseStep 1542479 = 2313719) B2313719
theorem B1542527 : Blo 1024605 1542527 := bstep (se 1 (by rfl) ⟨1156895, by rfl⟩ : syracuseStep 1542527 = 2313791) B2313791
theorem B1542569 : Blo 1024605 1542569 := bstep (se 2 (by rfl) ⟨578463, by rfl⟩ : syracuseStep 1542569 = 1156927) B1156927
theorem B2919007 : Blo 1024605 2919007 := bstep (se 1 (by rfl) ⟨2189255, by rfl⟩ : syracuseStep 2919007 = 4378511) B4378511
theorem B2919635 : Blo 1024605 2919635 := bstep (se 1 (by rfl) ⟨2189726, by rfl⟩ : syracuseStep 2919635 = 4379453) B4379453
theorem B2920511 : Blo 1024605 2920511 := bstep (se 1 (by rfl) ⟨2190383, by rfl⟩ : syracuseStep 2920511 = 4380767) B4380767
theorem B29560949 : Blo 1024605 29560949 := bstep (se 5 (by rfl) ⟨1385669, by rfl⟩ : syracuseStep 29560949 = 2771339) B2771339
theorem B4166225 : Blo 1024605 4166225 := bstep (se 2 (by rfl) ⟨1562334, by rfl⟩ : syracuseStep 4166225 = 3124669) B3124669
theorem B9376337 : Blo 1024605 9376337 := bstep (se 2 (by rfl) ⟨3516126, by rfl⟩ : syracuseStep 9376337 = 7032253) B7032253
theorem B5837741 : Blo 1024605 5837741 := bstep (se 3 (by rfl) ⟨1094576, by rfl⟩ : syracuseStep 5837741 = 2189153) B2189153
theorem B10556513 : Blo 1024605 10556513 := bstep (se 2 (by rfl) ⟨3958692, by rfl⟩ : syracuseStep 10556513 = 7917385) B7917385
theorem B3511801 : Blo 1024605 3511801 := bstep (se 2 (by rfl) ⟨1316925, by rfl⟩ : syracuseStep 3511801 = 2633851) B2633851
theorem B1152751 : Blo 1024605 1152751 := bstep (se 1 (by rfl) ⟨864563, by rfl⟩ : syracuseStep 1152751 = 1729127) B1729127
theorem B1152859 : Blo 1024605 1152859 := bstep (se 1 (by rfl) ⟨864644, by rfl⟩ : syracuseStep 1152859 = 1729289) B1729289
theorem B115677341 : Blo 1024605 115677341 := bstep (se 3 (by rfl) ⟨21689501, by rfl⟩ : syracuseStep 115677341 = 43379003) B43379003
theorem B1153255 : Blo 1024605 1153255 := bstep (se 1 (by rfl) ⟨864941, by rfl⟩ : syracuseStep 1153255 = 1729883) B1729883
theorem B32086367 : Blo 1024605 32086367 := bstep (se 1 (by rfl) ⟨24064775, by rfl⟩ : syracuseStep 32086367 = 48129551) B48129551
theorem B1645031 : Blo 1024605 1645031 := bstep (se 1 (by rfl) ⟨1233773, by rfl⟩ : syracuseStep 1645031 = 2467547) B2467547
theorem B6232889 : Blo 1024605 6232889 := bstep (se 2 (by rfl) ⟨2337333, by rfl⟩ : syracuseStep 6232889 = 4674667) B4674667
theorem B1153903 : Blo 1024605 1153903 := bstep (se 1 (by rfl) ⟨865427, by rfl⟩ : syracuseStep 1153903 = 1730855) B1730855
theorem B2923951 : Blo 1024605 2923951 := bstep (se 1 (by rfl) ⟨2192963, by rfl⟩ : syracuseStep 2923951 = 4385927) B4385927
theorem B17800813 : Blo 1024605 17800813 := bstep (se 3 (by rfl) ⟨3337652, by rfl⟩ : syracuseStep 17800813 = 6675305) B6675305
theorem B15802067 : Blo 1024605 15802067 := bstep (se 1 (by rfl) ⟨11851550, by rfl⟩ : syracuseStep 15802067 = 23703101) B23703101
theorem B19996379 : Blo 1024605 19996379 := bstep (se 1 (by rfl) ⟨14997284, by rfl⟩ : syracuseStep 19996379 = 29994569) B29994569
theorem B3284833 : Blo 1024605 3284833 := bstep (se 2 (by rfl) ⟨1231812, by rfl⟩ : syracuseStep 3284833 = 2463625) B2463625
theorem B1154983 : Blo 1024605 1154983 := bstep (se 1 (by rfl) ⟨866237, by rfl⟩ : syracuseStep 1154983 = 1732475) B1732475
theorem B11116763 : Blo 1024605 11116763 := bstep (se 1 (by rfl) ⟨8337572, by rfl⟩ : syracuseStep 11116763 = 16675145) B16675145
theorem B74883359 : Blo 1024605 74883359 := bstep (se 1 (by rfl) ⟨56162519, by rfl⟩ : syracuseStep 74883359 = 112325039) B112325039
theorem B1024623 : Blo 1024605 1024623 := bstep (se 1 (by rfl) ⟨768467, by rfl⟩ : syracuseStep 1024623 = 1536935) B1536935
theorem B1024679 : Blo 1024605 1024679 := bstep (se 1 (by rfl) ⟨768509, by rfl⟩ : syracuseStep 1024679 = 1537019) B1537019
theorem B1024719 : Blo 1024605 1024719 := bstep (se 1 (by rfl) ⟨768539, by rfl⟩ : syracuseStep 1024719 = 1537079) B1537079
theorem B4170503 : Blo 1024605 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B1024799 : Blo 1024605 1024799 := bstep (se 1 (by rfl) ⟨768599, by rfl⟩ : syracuseStep 1024799 = 1537199) B1537199
theorem B2925409 : Blo 1024605 2925409 := bstep (se 2 (by rfl) ⟨1097028, by rfl⟩ : syracuseStep 2925409 = 2194057) B2194057
theorem B4924327 : Blo 1024605 4924327 := bstep (se 1 (by rfl) ⟨3693245, by rfl⟩ : syracuseStep 4924327 = 7386491) B7386491
theorem B1025071 : Blo 1024605 1025071 := bstep (se 1 (by rfl) ⟨768803, by rfl⟩ : syracuseStep 1025071 = 1537607) B1537607
theorem B1025135 : Blo 1024605 1025135 := bstep (se 1 (by rfl) ⟨768851, by rfl⟩ : syracuseStep 1025135 = 1537703) B1537703
theorem B1156207 : Blo 1024605 1156207 := bstep (se 1 (by rfl) ⟨867155, by rfl⟩ : syracuseStep 1156207 = 1734311) B1734311
theorem B126231695 : Blo 1024605 126231695 := bstep (se 1 (by rfl) ⟨94673771, by rfl⟩ : syracuseStep 126231695 = 189347543) B189347543
theorem B1025191 : Blo 1024605 1025191 := bstep (se 1 (by rfl) ⟨768893, by rfl⟩ : syracuseStep 1025191 = 1537787) B1537787
theorem B9872563 : Blo 1024605 9872563 := bstep (se 1 (by rfl) ⟨7404422, by rfl⟩ : syracuseStep 9872563 = 14808845) B14808845
theorem B1025215 : Blo 1024605 1025215 := bstep (se 1 (by rfl) ⟨768911, by rfl⟩ : syracuseStep 1025215 = 1537823) B1537823
theorem B1025247 : Blo 1024605 1025247 := bstep (se 1 (by rfl) ⟨768935, by rfl⟩ : syracuseStep 1025247 = 1537871) B1537871
theorem B1025327 : Blo 1024605 1025327 := bstep (se 1 (by rfl) ⟨768995, by rfl⟩ : syracuseStep 1025327 = 1537991) B1537991
theorem B22226413 : Blo 1024605 22226413 := bstep (se 3 (by rfl) ⟨4167452, by rfl⟩ : syracuseStep 22226413 = 8334905) B8334905
theorem B1025563 : Blo 1024605 1025563 := bstep (se 1 (by rfl) ⟨769172, by rfl⟩ : syracuseStep 1025563 = 1538345) B1538345
theorem B1025567 : Blo 1024605 1025567 := bstep (se 1 (by rfl) ⟨769175, by rfl⟩ : syracuseStep 1025567 = 1538351) B1538351
theorem B1156639 : Blo 1024605 1156639 := bstep (se 1 (by rfl) ⟨867479, by rfl⟩ : syracuseStep 1156639 = 1734959) B1734959
theorem B3286601 : Blo 1024605 3286601 := bstep (se 2 (by rfl) ⟨1232475, by rfl⟩ : syracuseStep 3286601 = 2464951) B2464951
theorem B1025727 : Blo 1024605 1025727 := bstep (se 1 (by rfl) ⟨769295, by rfl⟩ : syracuseStep 1025727 = 1538591) B1538591
theorem B8759177 : Blo 1024605 8759177 := bstep (se 2 (by rfl) ⟨3284691, by rfl⟩ : syracuseStep 8759177 = 6569383) B6569383
theorem B2107291 : Blo 1024605 2107291 := bstep (se 1 (by rfl) ⟨1580468, by rfl⟩ : syracuseStep 2107291 = 3160937) B3160937
theorem B1025983 : Blo 1024605 1025983 := bstep (se 1 (by rfl) ⟨769487, by rfl⟩ : syracuseStep 1025983 = 1538975) B1538975
theorem B2500571 : Blo 1024605 2500571 := bstep (se 1 (by rfl) ⟨1875428, by rfl⟩ : syracuseStep 2500571 = 3750857) B3750857
theorem B1026015 : Blo 1024605 1026015 := bstep (se 1 (by rfl) ⟨769511, by rfl⟩ : syracuseStep 1026015 = 1539023) B1539023
theorem B1026075 : Blo 1024605 1026075 := bstep (se 1 (by rfl) ⟨769556, by rfl⟩ : syracuseStep 1026075 = 1539113) B1539113
theorem B1026079 : Blo 1024605 1026079 := bstep (se 1 (by rfl) ⟨769559, by rfl⟩ : syracuseStep 1026079 = 1539119) B1539119
theorem B1026095 : Blo 1024605 1026095 := bstep (se 1 (by rfl) ⟨769571, by rfl⟩ : syracuseStep 1026095 = 1539143) B1539143
theorem B8562833 : Blo 1024605 8562833 := bstep (se 2 (by rfl) ⟨3211062, by rfl⟩ : syracuseStep 8562833 = 6422125) B6422125
theorem B1026271 : Blo 1024605 1026271 := bstep (se 1 (by rfl) ⟨769703, by rfl⟩ : syracuseStep 1026271 = 1539407) B1539407
theorem B1026331 : Blo 1024605 1026331 := bstep (se 1 (by rfl) ⟨769748, by rfl⟩ : syracuseStep 1026331 = 1539497) B1539497
theorem B1026431 : Blo 1024605 1026431 := bstep (se 1 (by rfl) ⟨769823, by rfl⟩ : syracuseStep 1026431 = 1539647) B1539647
theorem B1026607 : Blo 1024605 1026607 := bstep (se 1 (by rfl) ⟨769955, by rfl⟩ : syracuseStep 1026607 = 1539911) B1539911
theorem B1026663 : Blo 1024605 1026663 := bstep (se 1 (by rfl) ⟨769997, by rfl⟩ : syracuseStep 1026663 = 1539995) B1539995
theorem B1027039 : Blo 1024605 1027039 := bstep (se 1 (by rfl) ⟨770279, by rfl⟩ : syracuseStep 1027039 = 1540559) B1540559
theorem B1027067 : Blo 1024605 1027067 := bstep (se 1 (by rfl) ⟨770300, by rfl⟩ : syracuseStep 1027067 = 1540601) B1540601
theorem B1027135 : Blo 1024605 1027135 := bstep (se 1 (by rfl) ⟨770351, by rfl⟩ : syracuseStep 1027135 = 1540703) B1540703
theorem B2600201 : Blo 1024605 2600201 := bstep (se 2 (by rfl) ⟨975075, by rfl⟩ : syracuseStep 2600201 = 1950151) B1950151
theorem B2927927 : Blo 1024605 2927927 := bstep (se 1 (by rfl) ⟨2195945, by rfl⟩ : syracuseStep 2927927 = 4391891) B4391891
theorem B1027455 : Blo 1024605 1027455 := bstep (se 1 (by rfl) ⟨770591, by rfl⟩ : syracuseStep 1027455 = 1541183) B1541183
theorem B1027483 : Blo 1024605 1027483 := bstep (se 1 (by rfl) ⟨770612, by rfl⟩ : syracuseStep 1027483 = 1541225) B1541225
theorem B1027551 : Blo 1024605 1027551 := bstep (se 1 (by rfl) ⟨770663, by rfl⟩ : syracuseStep 1027551 = 1541327) B1541327
theorem B1027687 : Blo 1024605 1027687 := bstep (se 1 (by rfl) ⟨770765, by rfl⟩ : syracuseStep 1027687 = 1541531) B1541531
theorem B6237803 : Blo 1024605 6237803 := bstep (se 1 (by rfl) ⟨4678352, by rfl⟩ : syracuseStep 6237803 = 9356705) B9356705
theorem B6565511 : Blo 1024605 6565511 := bstep (se 1 (by rfl) ⟨4924133, by rfl⟩ : syracuseStep 6565511 = 9848267) B9848267
theorem B1027835 : Blo 1024605 1027835 := bstep (se 1 (by rfl) ⟨770876, by rfl⟩ : syracuseStep 1027835 = 1541753) B1541753
theorem B1027903 : Blo 1024605 1027903 := bstep (se 1 (by rfl) ⟨770927, by rfl⟩ : syracuseStep 1027903 = 1541855) B1541855
theorem B1027967 : Blo 1024605 1027967 := bstep (se 1 (by rfl) ⟨770975, by rfl⟩ : syracuseStep 1027967 = 1541951) B1541951
theorem B1978283 : Blo 1024605 1978283 := bstep (se 1 (by rfl) ⟨1483712, by rfl⟩ : syracuseStep 1978283 = 2967425) B2967425
theorem B1028079 : Blo 1024605 1028079 := bstep (se 1 (by rfl) ⟨771059, by rfl⟩ : syracuseStep 1028079 = 1542119) B1542119
theorem B1028091 : Blo 1024605 1028091 := bstep (se 1 (by rfl) ⟨771068, by rfl⟩ : syracuseStep 1028091 = 1542137) B1542137
theorem B1028159 : Blo 1024605 1028159 := bstep (se 1 (by rfl) ⟨771119, by rfl⟩ : syracuseStep 1028159 = 1542239) B1542239
theorem B1028199 : Blo 1024605 1028199 := bstep (se 1 (by rfl) ⟨771149, by rfl⟩ : syracuseStep 1028199 = 1542299) B1542299
theorem B1028223 : Blo 1024605 1028223 := bstep (se 1 (by rfl) ⟨771167, by rfl⟩ : syracuseStep 1028223 = 1542335) B1542335
theorem B1028251 : Blo 1024605 1028251 := bstep (se 1 (by rfl) ⟨771188, by rfl⟩ : syracuseStep 1028251 = 1542377) B1542377
theorem B1028455 : Blo 1024605 1028455 := bstep (se 1 (by rfl) ⟨771341, by rfl⟩ : syracuseStep 1028455 = 1542683) B1542683
theorem B1028507 : Blo 1024605 1028507 := bstep (se 1 (by rfl) ⟨771380, by rfl⟩ : syracuseStep 1028507 = 1542761) B1542761
theorem B16659047 : Blo 1024605 16659047 := bstep (se 1 (by rfl) ⟨12494285, by rfl⟩ : syracuseStep 16659047 = 24988571) B24988571
theorem B2306825 : Blo 1024605 2306825 := bstep (se 2 (by rfl) ⟨865059, by rfl⟩ : syracuseStep 2306825 = 1730119) B1730119
theorem B2306879 : Blo 1024605 2306879 := bstep (se 1 (by rfl) ⟨1730159, by rfl⟩ : syracuseStep 2306879 = 3460319) B3460319
theorem B2601791 : Blo 1024605 2601791 := bstep (se 1 (by rfl) ⟨1951343, by rfl⟩ : syracuseStep 2601791 = 3902687) B3902687
theorem B1094491 : Blo 1024605 1094491 := bstep (se 1 (by rfl) ⟨820868, by rfl⟩ : syracuseStep 1094491 = 1641737) B1641737
theorem B2307023 : Blo 1024605 2307023 := bstep (se 1 (by rfl) ⟨1730267, by rfl⟩ : syracuseStep 2307023 = 3460535) B3460535
theorem B2307113 : Blo 1024605 2307113 := bstep (se 2 (by rfl) ⟨865167, by rfl⟩ : syracuseStep 2307113 = 1730335) B1730335
theorem B2307401 : Blo 1024605 2307401 := bstep (se 2 (by rfl) ⟨865275, by rfl⟩ : syracuseStep 2307401 = 1730551) B1730551
theorem B1947091 : Blo 1024605 1947091 := bstep (se 1 (by rfl) ⟨1460318, by rfl⟩ : syracuseStep 1947091 = 2920637) B2920637
theorem B8893961 : Blo 1024605 8893961 := bstep (se 2 (by rfl) ⟨3335235, by rfl⟩ : syracuseStep 8893961 = 6670471) B6670471
theorem B4929133 : Blo 1024605 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B2635487 : Blo 1024605 2635487 := bstep (se 1 (by rfl) ⟨1976615, by rfl⟩ : syracuseStep 2635487 = 3953231) B3953231
theorem B5191775 : Blo 1024605 5191775 := bstep (se 1 (by rfl) ⟨3893831, by rfl⟩ : syracuseStep 5191775 = 7787663) B7787663
theorem B3291367 : Blo 1024605 3291367 := bstep (se 1 (by rfl) ⟨2468525, by rfl⟩ : syracuseStep 3291367 = 4937051) B4937051
theorem B2504935 : Blo 1024605 2504935 := bstep (se 1 (by rfl) ⟨1878701, by rfl⟩ : syracuseStep 2504935 = 3757403) B3757403
theorem B35535095 : Blo 1024605 35535095 := bstep (se 1 (by rfl) ⟨26651321, by rfl⟩ : syracuseStep 35535095 = 53302643) B53302643
theorem B2308391 : Blo 1024605 2308391 := bstep (se 1 (by rfl) ⟨1731293, by rfl⟩ : syracuseStep 2308391 = 3462587) B3462587
theorem B5847673 : Blo 1024605 5847673 := bstep (se 2 (by rfl) ⟨2192877, by rfl⟩ : syracuseStep 5847673 = 4385755) B4385755
theorem B2308751 : Blo 1024605 2308751 := bstep (se 1 (by rfl) ⟨1731563, by rfl⟩ : syracuseStep 2308751 = 3463127) B3463127
theorem B2308841 : Blo 1024605 2308841 := bstep (se 2 (by rfl) ⟨865815, by rfl⟩ : syracuseStep 2308841 = 1731631) B1731631
theorem B2309075 : Blo 1024605 2309075 := bstep (se 1 (by rfl) ⟨1731806, by rfl⟩ : syracuseStep 2309075 = 3463613) B3463613
theorem B2309345 : Blo 1024605 2309345 := bstep (se 2 (by rfl) ⟨866004, by rfl⟩ : syracuseStep 2309345 = 1732009) B1732009
theorem B1949179 : Blo 1024605 1949179 := bstep (se 1 (by rfl) ⟨1461884, by rfl⟩ : syracuseStep 1949179 = 2923769) B2923769
theorem B2309651 : Blo 1024605 2309651 := bstep (se 1 (by rfl) ⟨1732238, by rfl⟩ : syracuseStep 2309651 = 3464477) B3464477
theorem B4931207 : Blo 1024605 4931207 := bstep (se 1 (by rfl) ⟨3698405, by rfl⟩ : syracuseStep 4931207 = 7396811) B7396811
theorem B7126751 : Blo 1024605 7126751 := bstep (se 1 (by rfl) ⟨5345063, by rfl⟩ : syracuseStep 7126751 = 10690127) B10690127
theorem B1097447 : Blo 1024605 1097447 := bstep (se 1 (by rfl) ⟨823085, by rfl⟩ : syracuseStep 1097447 = 1646171) B1646171
theorem B42156065 : Blo 1024605 42156065 := bstep (se 2 (by rfl) ⟨15808524, by rfl⟩ : syracuseStep 42156065 = 31617049) B31617049
theorem B2310335 : Blo 1024605 2310335 := bstep (se 1 (by rfl) ⟨1732751, by rfl⟩ : syracuseStep 2310335 = 3465503) B3465503
theorem B63324517 : Blo 1024605 63324517 := bstep (se 4 (by rfl) ⟨5936673, by rfl⟩ : syracuseStep 63324517 = 11873347) B11873347
theorem B14041633 : Blo 1024605 14041633 := bstep (se 2 (by rfl) ⟨5265612, by rfl⟩ : syracuseStep 14041633 = 10531225) B10531225
theorem B1950311 : Blo 1024605 1950311 := bstep (se 1 (by rfl) ⟨1462733, by rfl⟩ : syracuseStep 1950311 = 2925467) B2925467
theorem B2310767 : Blo 1024605 2310767 := bstep (se 1 (by rfl) ⟨1733075, by rfl⟩ : syracuseStep 2310767 = 3466151) B3466151
theorem B57754529 : Blo 1024605 57754529 := bstep (se 2 (by rfl) ⟨21657948, by rfl⟩ : syracuseStep 57754529 = 43315897) B43315897
theorem B2311163 : Blo 1024605 2311163 := bstep (se 1 (by rfl) ⟨1733372, by rfl⟩ : syracuseStep 2311163 = 3466745) B3466745
theorem B3458159 : Blo 1024605 3458159 := bstep (se 1 (by rfl) ⟨2593619, by rfl⟩ : syracuseStep 3458159 = 5187239) B5187239
theorem B2311343 : Blo 1024605 2311343 := bstep (se 1 (by rfl) ⟨1733507, by rfl⟩ : syracuseStep 2311343 = 3467015) B3467015
theorem B1950895 : Blo 1024605 1950895 := bstep (se 1 (by rfl) ⟨1463171, by rfl⟩ : syracuseStep 1950895 = 2926343) B2926343
theorem B5555375 : Blo 1024605 5555375 := bstep (se 1 (by rfl) ⟨4166531, by rfl⟩ : syracuseStep 5555375 = 8333063) B8333063
theorem B2311379 : Blo 1024605 2311379 := bstep (se 1 (by rfl) ⟨1733534, by rfl⟩ : syracuseStep 2311379 = 3467069) B3467069
theorem B3458267 : Blo 1024605 3458267 := bstep (se 1 (by rfl) ⟨2593700, by rfl⟩ : syracuseStep 3458267 = 5187401) B5187401
theorem B7783775 : Blo 1024605 7783775 := bstep (se 1 (by rfl) ⟨5837831, by rfl⟩ : syracuseStep 7783775 = 11675663) B11675663
theorem B2311649 : Blo 1024605 2311649 := bstep (se 2 (by rfl) ⟨866868, by rfl⟩ : syracuseStep 2311649 = 1733737) B1733737
theorem B1951609 : Blo 1024605 1951609 := bstep (se 2 (by rfl) ⟨731853, by rfl⟩ : syracuseStep 1951609 = 1463707) B1463707
theorem B2312999 : Blo 1024605 2312999 := bstep (se 1 (by rfl) ⟨1734749, by rfl⟩ : syracuseStep 2312999 = 3469499) B3469499
theorem B5852047 : Blo 1024605 5852047 := bstep (se 1 (by rfl) ⟨4389035, by rfl⟩ : syracuseStep 5852047 = 8778071) B8778071
theorem B2313323 : Blo 1024605 2313323 := bstep (se 1 (by rfl) ⟨1734992, by rfl⟩ : syracuseStep 2313323 = 3469985) B3469985
theorem B112381091 : Blo 1024605 112381091 := bstep (se 1 (by rfl) ⟨84285818, by rfl⟩ : syracuseStep 112381091 = 168571637) B168571637
theorem B2313593 : Blo 1024605 2313593 := bstep (se 2 (by rfl) ⟨867597, by rfl⟩ : syracuseStep 2313593 = 1735195) B1735195
theorem B2313899 : Blo 1024605 2313899 := bstep (se 1 (by rfl) ⟨1735424, by rfl⟩ : syracuseStep 2313899 = 3470849) B3470849
theorem B4378495 : Blo 1024605 4378495 := bstep (se 1 (by rfl) ⟨3283871, by rfl⟩ : syracuseStep 4378495 = 6567743) B6567743
theorem B2314223 : Blo 1024605 2314223 := bstep (se 1 (by rfl) ⟨1735667, by rfl⟩ : syracuseStep 2314223 = 3471335) B3471335
theorem B4935667 : Blo 1024605 4935667 := bstep (se 1 (by rfl) ⟨3701750, by rfl⟩ : syracuseStep 4935667 = 7403501) B7403501
theorem B2314295 : Blo 1024605 2314295 := bstep (se 1 (by rfl) ⟨1735721, by rfl⟩ : syracuseStep 2314295 = 3471443) B3471443
theorem B1298587 : Blo 1024605 1298587 := bstep (se 1 (by rfl) ⟨973940, by rfl⟩ : syracuseStep 1298587 = 1947881) B1947881
theorem B4378819 : Blo 1024605 4378819 := bstep (se 1 (by rfl) ⟨3284114, by rfl⟩ : syracuseStep 4378819 = 6568229) B6568229
theorem B7786691 : Blo 1024605 7786691 := bstep (se 1 (by rfl) ⟨5840018, by rfl⟩ : syracuseStep 7786691 = 11680037) B11680037
theorem B3461993 : Blo 1024605 3461993 := bstep (se 2 (by rfl) ⟨1298247, by rfl⟩ : syracuseStep 3461993 = 2596495) B2596495
theorem B99046385 : Blo 1024605 99046385 := bstep (se 2 (by rfl) ⟨37142394, by rfl⟩ : syracuseStep 99046385 = 74284789) B74284789
theorem B17552861 : Blo 1024605 17552861 := bstep (se 3 (by rfl) ⟨3291161, by rfl⟩ : syracuseStep 17552861 = 6582323) B6582323
theorem B5330569 : Blo 1024605 5330569 := bstep (se 2 (by rfl) ⟨1998963, by rfl⟩ : syracuseStep 5330569 = 3997927) B3997927
theorem B8771921 : Blo 1024605 8771921 := bstep (se 2 (by rfl) ⟨3289470, by rfl⟩ : syracuseStep 8771921 = 6578941) B6578941
theorem B1235359 : Blo 1024605 1235359 := bstep (se 1 (by rfl) ⟨926519, by rfl⟩ : syracuseStep 1235359 = 1853039) B1853039
theorem B9001543 : Blo 1024605 9001543 := bstep (se 1 (by rfl) ⟨6751157, by rfl⟩ : syracuseStep 9001543 = 13502315) B13502315
theorem B7494223 : Blo 1024605 7494223 := bstep (se 1 (by rfl) ⟨5620667, by rfl⟩ : syracuseStep 7494223 = 11241335) B11241335
theorem B8772299 : Blo 1024605 8772299 := bstep (se 1 (by rfl) ⟨6579224, by rfl⟩ : syracuseStep 8772299 = 13158449) B13158449
theorem B3463991 : Blo 1024605 3463991 := bstep (se 1 (by rfl) ⟨2597993, by rfl⟩ : syracuseStep 3463991 = 5195987) B5195987
theorem B35576819 : Blo 1024605 35576819 := bstep (se 1 (by rfl) ⟨26682614, by rfl⟩ : syracuseStep 35576819 = 53365229) B53365229
theorem B3890855 : Blo 1024605 3890855 := bstep (se 1 (by rfl) ⟨2918141, by rfl⟩ : syracuseStep 3890855 = 5836283) B5836283
theorem B3465071 : Blo 1024605 3465071 := bstep (se 1 (by rfl) ⟨2598803, by rfl⟩ : syracuseStep 3465071 = 5197607) B5197607
theorem B7790579 : Blo 1024605 7790579 := bstep (se 1 (by rfl) ⟨5842934, by rfl⟩ : syracuseStep 7790579 = 11685869) B11685869
theorem B13131841 : Blo 1024605 13131841 := bstep (se 2 (by rfl) ⟨4924440, by rfl⟩ : syracuseStep 13131841 = 9848881) B9848881
theorem B3694715 : Blo 1024605 3694715 := bstep (se 1 (by rfl) ⟨2771036, by rfl⟩ : syracuseStep 3694715 = 5542073) B5542073
theorem B4383143 : Blo 1024605 4383143 := bstep (se 1 (by rfl) ⟨3287357, by rfl⟩ : syracuseStep 4383143 = 6574715) B6574715
theorem B4383227 : Blo 1024605 4383227 := bstep (se 1 (by rfl) ⟨3287420, by rfl⟩ : syracuseStep 4383227 = 6574841) B6574841
theorem B3465935 : Blo 1024605 3465935 := bstep (se 1 (by rfl) ⟨2599451, by rfl⟩ : syracuseStep 3465935 = 5198903) B5198903
theorem B4383467 : Blo 1024605 4383467 := bstep (se 1 (by rfl) ⟨3287600, by rfl⟩ : syracuseStep 4383467 = 6575201) B6575201
theorem B75818045 : Blo 1024605 75818045 := bstep (se 3 (by rfl) ⟨14215883, by rfl⟩ : syracuseStep 75818045 = 28431767) B28431767
theorem B3466313 : Blo 1024605 3466313 := bstep (se 2 (by rfl) ⟨1299867, by rfl⟩ : syracuseStep 3466313 = 2599735) B2599735
theorem B1729849 : Blo 1024605 1729849 := bstep (se 2 (by rfl) ⟨648693, by rfl⟩ : syracuseStep 1729849 = 1297387) B1297387
theorem B4941587 : Blo 1024605 4941587 := bstep (se 1 (by rfl) ⟨3706190, by rfl⟩ : syracuseStep 4941587 = 7412381) B7412381
theorem B2189119 : Blo 1024605 2189119 := bstep (se 1 (by rfl) ⟨1641839, by rfl⟩ : syracuseStep 2189119 = 3283679) B3283679
theorem B3860303 : Blo 1024605 3860303 := bstep (se 1 (by rfl) ⟨2895227, by rfl⟩ : syracuseStep 3860303 = 5790455) B5790455
theorem B4155293 : Blo 1024605 4155293 := bstep (se 3 (by rfl) ⟨779117, by rfl⟩ : syracuseStep 4155293 = 1558235) B1558235
theorem B106850501 : Blo 1024605 106850501 := bstep (se 4 (by rfl) ⟨10017234, by rfl⟩ : syracuseStep 106850501 = 20034469) B20034469
theorem B74967443 : Blo 1024605 74967443 := bstep (se 1 (by rfl) ⟨56225582, by rfl⟩ : syracuseStep 74967443 = 112451165) B112451165
theorem B7793495 : Blo 1024605 7793495 := bstep (se 1 (by rfl) ⟨5845121, by rfl⟩ : syracuseStep 7793495 = 11690243) B11690243
theorem B5204897 : Blo 1024605 5204897 := bstep (se 2 (by rfl) ⟨1951836, by rfl⟩ : syracuseStep 5204897 = 3903673) B3903673
theorem B1732063 : Blo 1024605 1732063 := bstep (se 1 (by rfl) ⟨1299047, by rfl⟩ : syracuseStep 1732063 = 2598095) B2598095
theorem B4681307 : Blo 1024605 4681307 := bstep (se 1 (by rfl) ⟨3510980, by rfl⟩ : syracuseStep 4681307 = 7021961) B7021961
theorem B1732279 : Blo 1024605 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B5205707 : Blo 1024605 5205707 := bstep (se 1 (by rfl) ⟨3904280, by rfl⟩ : syracuseStep 5205707 = 7808561) B7808561
theorem B31289125 : Blo 1024605 31289125 := bstep (se 4 (by rfl) ⟨2933355, by rfl⟩ : syracuseStep 31289125 = 5866711) B5866711
theorem B17526617 : Blo 1024605 17526617 := bstep (se 2 (by rfl) ⟨6572481, by rfl⟩ : syracuseStep 17526617 = 13144963) B13144963
theorem B6582505 : Blo 1024605 6582505 := bstep (se 2 (by rfl) ⟨2468439, by rfl⟩ : syracuseStep 6582505 = 4936879) B4936879
theorem B7794953 : Blo 1024605 7794953 := bstep (se 2 (by rfl) ⟨2923107, by rfl⟩ : syracuseStep 7794953 = 5846215) B5846215
theorem B3338927 : Blo 1024605 3338927 := bstep (se 1 (by rfl) ⟨2504195, by rfl⟩ : syracuseStep 3338927 = 5008391) B5008391
theorem B3896383 : Blo 1024605 3896383 := bstep (se 1 (by rfl) ⟨2922287, by rfl⟩ : syracuseStep 3896383 = 5844575) B5844575
theorem B1537289 : Blo 1024605 1537289 := bstep (se 2 (by rfl) ⟨576483, by rfl⟩ : syracuseStep 1537289 = 1152967) B1152967
theorem B1537343 : Blo 1024605 1537343 := bstep (se 1 (by rfl) ⟨1153007, by rfl⟩ : syracuseStep 1537343 = 2306015) B2306015
theorem B33322499 : Blo 1024605 33322499 := bstep (se 1 (by rfl) ⟨24991874, by rfl⟩ : syracuseStep 33322499 = 49983749) B49983749
theorem B2193007 : Blo 1024605 2193007 := bstep (se 1 (by rfl) ⟨1644755, by rfl⟩ : syracuseStep 2193007 = 3289511) B3289511
theorem B1537769 : Blo 1024605 1537769 := bstep (se 2 (by rfl) ⟨576663, by rfl⟩ : syracuseStep 1537769 = 1153327) B1153327
theorem B1537775 : Blo 1024605 1537775 := bstep (se 1 (by rfl) ⟨1153331, by rfl⟩ : syracuseStep 1537775 = 2306663) B2306663
theorem B3700541 : Blo 1024605 3700541 := bstep (se 3 (by rfl) ⟨693851, by rfl⟩ : syracuseStep 3700541 = 1387703) B1387703
theorem B1538231 : Blo 1024605 1538231 := bstep (se 1 (by rfl) ⟨1153673, by rfl⟩ : syracuseStep 1538231 = 2307347) B2307347
theorem B1538279 : Blo 1024605 1538279 := bstep (se 1 (by rfl) ⟨1153709, by rfl⟩ : syracuseStep 1538279 = 2307419) B2307419
theorem B4159835 : Blo 1024605 4159835 := bstep (se 1 (by rfl) ⟨3119876, by rfl⟩ : syracuseStep 4159835 = 6239753) B6239753
theorem B84212257 : Blo 1024605 84212257 := bstep (se 2 (by rfl) ⟨31579596, by rfl⟩ : syracuseStep 84212257 = 63159193) B63159193
theorem B1538651 : Blo 1024605 1538651 := bstep (se 1 (by rfl) ⟨1153988, by rfl⟩ : syracuseStep 1538651 = 2307977) B2307977
theorem B6584989 : Blo 1024605 6584989 := bstep (se 3 (by rfl) ⟨1234685, by rfl⟩ : syracuseStep 6584989 = 2469371) B2469371
theorem B1538795 : Blo 1024605 1538795 := bstep (se 1 (by rfl) ⟨1154096, by rfl⟩ : syracuseStep 1538795 = 2308193) B2308193
theorem B1538825 : Blo 1024605 1538825 := bstep (se 2 (by rfl) ⟨577059, by rfl⟩ : syracuseStep 1538825 = 1154119) B1154119
theorem B12483395 : Blo 1024605 12483395 := bstep (se 1 (by rfl) ⟨9362546, by rfl⟩ : syracuseStep 12483395 = 18725093) B18725093
theorem B35519309 : Blo 1024605 35519309 := bstep (se 3 (by rfl) ⟨6659870, by rfl⟩ : syracuseStep 35519309 = 13319741) B13319741
theorem B8780669 : Blo 1024605 8780669 := bstep (se 3 (by rfl) ⟨1646375, by rfl⟩ : syracuseStep 8780669 = 3292751) B3292751
theorem B3898313 : Blo 1024605 3898313 := bstep (se 2 (by rfl) ⟨1461867, by rfl⟩ : syracuseStep 3898313 = 2923735) B2923735
theorem B80084285 : Blo 1024605 80084285 := bstep (se 3 (by rfl) ⟨15015803, by rfl⟩ : syracuseStep 80084285 = 30031607) B30031607
theorem B3898813 : Blo 1024605 3898813 := bstep (se 3 (by rfl) ⟨731027, by rfl⟩ : syracuseStep 3898813 = 1462055) B1462055
theorem B1539695 : Blo 1024605 1539695 := bstep (se 1 (by rfl) ⟨1154771, by rfl⟩ : syracuseStep 1539695 = 2309543) B2309543
theorem B1539815 : Blo 1024605 1539815 := bstep (se 1 (by rfl) ⟨1154861, by rfl⟩ : syracuseStep 1539815 = 2309723) B2309723
theorem B4685597 : Blo 1024605 4685597 := bstep (se 3 (by rfl) ⟨878549, by rfl⟩ : syracuseStep 4685597 = 1757099) B1757099
theorem B1540007 : Blo 1024605 1540007 := bstep (se 1 (by rfl) ⟨1155005, by rfl⟩ : syracuseStep 1540007 = 2310011) B2310011
theorem B2195399 : Blo 1024605 2195399 := bstep (se 1 (by rfl) ⟨1646549, by rfl⟩ : syracuseStep 2195399 = 3293099) B3293099
theorem B1540223 : Blo 1024605 1540223 := bstep (se 1 (by rfl) ⟨1155167, by rfl⟩ : syracuseStep 1540223 = 2310335) B2310335
theorem B1540511 : Blo 1024605 1540511 := bstep (se 1 (by rfl) ⟨1155383, by rfl⟩ : syracuseStep 1540511 = 2310767) B2310767
theorem B38503019 : Blo 1024605 38503019 := bstep (se 1 (by rfl) ⟨28877264, by rfl⟩ : syracuseStep 38503019 = 57754529) B57754529
theorem B1540775 : Blo 1024605 1540775 := bstep (se 1 (by rfl) ⟨1155581, by rfl⟩ : syracuseStep 1540775 = 2311163) B2311163
theorem B1540895 : Blo 1024605 1540895 := bstep (se 1 (by rfl) ⟨1155671, by rfl⟩ : syracuseStep 1540895 = 2311343) B2311343
theorem B3703583 : Blo 1024605 3703583 := bstep (se 1 (by rfl) ⟨2777687, by rfl⟩ : syracuseStep 3703583 = 5555375) B5555375
theorem B1540919 : Blo 1024605 1540919 := bstep (se 1 (by rfl) ⟨1155689, by rfl⟩ : syracuseStep 1540919 = 2311379) B2311379
theorem B1541099 : Blo 1024605 1541099 := bstep (se 1 (by rfl) ⟨1155824, by rfl⟩ : syracuseStep 1541099 = 2311649) B2311649
theorem B3900545 : Blo 1024605 3900545 := bstep (se 2 (by rfl) ⟨1462704, by rfl⟩ : syracuseStep 3900545 = 2925409) B2925409
theorem B1541609 : Blo 1024605 1541609 := bstep (se 2 (by rfl) ⟨578103, by rfl⟩ : syracuseStep 1541609 = 1156207) B1156207
theorem B1541999 : Blo 1024605 1541999 := bstep (se 1 (by rfl) ⟨1156499, by rfl⟩ : syracuseStep 1541999 = 2312999) B2312999
theorem B1542185 : Blo 1024605 1542185 := bstep (se 2 (by rfl) ⟨578319, by rfl⟩ : syracuseStep 1542185 = 1156639) B1156639
theorem B1542215 : Blo 1024605 1542215 := bstep (se 1 (by rfl) ⟨1156661, by rfl⟩ : syracuseStep 1542215 = 2313323) B2313323
theorem B1542395 : Blo 1024605 1542395 := bstep (se 1 (by rfl) ⟨1156796, by rfl⟩ : syracuseStep 1542395 = 2313593) B2313593
theorem B2918825 : Blo 1024605 2918825 := bstep (se 2 (by rfl) ⟨1094559, by rfl⟩ : syracuseStep 2918825 = 2189119) B2189119
theorem B1542599 : Blo 1024605 1542599 := bstep (se 1 (by rfl) ⟨1156949, by rfl⟩ : syracuseStep 1542599 = 2313899) B2313899
theorem B1542815 : Blo 1024605 1542815 := bstep (se 1 (by rfl) ⟨1157111, by rfl⟩ : syracuseStep 1542815 = 2314223) B2314223
theorem B1542863 : Blo 1024605 1542863 := bstep (se 1 (by rfl) ⟨1157147, by rfl⟩ : syracuseStep 1542863 = 2314295) B2314295
theorem B202181453 : Blo 1024605 202181453 := bstep (se 3 (by rfl) ⟨37909022, by rfl⟩ : syracuseStep 202181453 = 75818045) B75818045
theorem B66030923 : Blo 1024605 66030923 := bstep (se 1 (by rfl) ⟨49523192, by rfl⟩ : syracuseStep 66030923 = 99046385) B99046385
theorem B11701907 : Blo 1024605 11701907 := bstep (se 1 (by rfl) ⟨8776430, by rfl⟩ : syracuseStep 11701907 = 17552861) B17552861
theorem B7802729 : Blo 1024605 7802729 := bstep (se 2 (by rfl) ⟨2926023, by rfl⟩ : syracuseStep 7802729 = 5852047) B5852047
theorem B5837285 : Blo 1024605 5837285 := bstep (se 4 (by rfl) ⟨547245, by rfl⟩ : syracuseStep 5837285 = 1094491) B1094491
theorem B13177565 : Blo 1024605 13177565 := bstep (se 3 (by rfl) ⟨2470793, by rfl⟩ : syracuseStep 13177565 = 4941587) B4941587
theorem B10294141 : Blo 1024605 10294141 := bstep (se 3 (by rfl) ⟨1930151, by rfl⟩ : syracuseStep 10294141 = 3860303) B3860303
theorem B41718833 : Blo 1024605 41718833 := bstep (se 2 (by rfl) ⟨15644562, by rfl⟩ : syracuseStep 41718833 = 31289125) B31289125
theorem B2593903 : Blo 1024605 2593903 := bstep (se 1 (by rfl) ⟨1945427, by rfl⟩ : syracuseStep 2593903 = 3890855) B3890855
theorem B5837993 : Blo 1024605 5837993 := bstep (se 2 (by rfl) ⟨2189247, by rfl⟩ : syracuseStep 5837993 = 4378495) B4378495
theorem B2463143 : Blo 1024605 2463143 := bstep (se 1 (by rfl) ⟨1847357, by rfl⟩ : syracuseStep 2463143 = 3694715) B3694715
theorem B7411175 : Blo 1024605 7411175 := bstep (se 1 (by rfl) ⟨5558381, by rfl⟩ : syracuseStep 7411175 = 11116763) B11116763
theorem B5838425 : Blo 1024605 5838425 := bstep (se 2 (by rfl) ⟨2189409, by rfl⟩ : syracuseStep 5838425 = 4378819) B4378819
theorem B2922095 : Blo 1024605 2922095 := bstep (se 1 (by rfl) ⟨2191571, by rfl⟩ : syracuseStep 2922095 = 4383143) B4383143
theorem B2922151 : Blo 1024605 2922151 := bstep (se 1 (by rfl) ⟨2191613, by rfl⟩ : syracuseStep 2922151 = 4383227) B4383227
theorem B2922311 : Blo 1024605 2922311 := bstep (se 1 (by rfl) ⟨2191733, by rfl⟩ : syracuseStep 2922311 = 4383467) B4383467
theorem B84154463 : Blo 1024605 84154463 := bstep (se 1 (by rfl) ⟨63115847, by rfl⟩ : syracuseStep 84154463 = 126231695) B126231695
theorem B5839451 : Blo 1024605 5839451 := bstep (se 1 (by rfl) ⟨4379588, by rfl⟩ : syracuseStep 5839451 = 8759177) B8759177
theorem B5708555 : Blo 1024605 5708555 := bstep (se 1 (by rfl) ⟨4281416, by rfl⟩ : syracuseStep 5708555 = 8562833) B8562833
theorem B49978295 : Blo 1024605 49978295 := bstep (se 1 (by rfl) ⟨37483721, by rfl⟩ : syracuseStep 49978295 = 74967443) B74967443
theorem B2596121 : Blo 1024605 2596121 := bstep (se 2 (by rfl) ⟨973545, by rfl⟩ : syracuseStep 2596121 = 1947091) B1947091
theorem B2924009 : Blo 1024605 2924009 := bstep (se 2 (by rfl) ⟨1096503, by rfl⟩ : syracuseStep 2924009 = 2193007) B2193007
theorem B3120871 : Blo 1024605 3120871 := bstep (se 1 (by rfl) ⟨2340653, by rfl⟩ : syracuseStep 3120871 = 4681307) B4681307
theorem B1647145 : Blo 1024605 1647145 := bstep (se 2 (by rfl) ⟨617679, by rfl⟩ : syracuseStep 1647145 = 1235359) B1235359
theorem B12002057 : Blo 1024605 12002057 := bstep (se 2 (by rfl) ⟨4500771, by rfl⟩ : syracuseStep 12002057 = 9001543) B9001543
theorem B1024859 : Blo 1024605 1024859 := bstep (se 1 (by rfl) ⟨768644, by rfl⟩ : syracuseStep 1024859 = 1537289) B1537289
theorem B1024895 : Blo 1024605 1024895 := bstep (se 1 (by rfl) ⟨768671, by rfl⟩ : syracuseStep 1024895 = 1537343) B1537343
theorem B1025179 : Blo 1024605 1025179 := bstep (se 1 (by rfl) ⟨768884, by rfl⟩ : syracuseStep 1025179 = 1537769) B1537769
theorem B1025183 : Blo 1024605 1025183 := bstep (se 1 (by rfl) ⟨768887, by rfl⟩ : syracuseStep 1025183 = 1537775) B1537775
theorem B2467027 : Blo 1024605 2467027 := bstep (se 1 (by rfl) ⟨1850270, by rfl⟩ : syracuseStep 2467027 = 3700541) B3700541
theorem B1025487 : Blo 1024605 1025487 := bstep (se 1 (by rfl) ⟨769115, by rfl⟩ : syracuseStep 1025487 = 1538231) B1538231
theorem B1025519 : Blo 1024605 1025519 := bstep (se 1 (by rfl) ⟨769139, by rfl⟩ : syracuseStep 1025519 = 1538279) B1538279
theorem B1025767 : Blo 1024605 1025767 := bstep (se 1 (by rfl) ⟨769325, by rfl⟩ : syracuseStep 1025767 = 1538651) B1538651
theorem B1025863 : Blo 1024605 1025863 := bstep (se 1 (by rfl) ⟨769397, by rfl⟩ : syracuseStep 1025863 = 1538795) B1538795
theorem B1025883 : Blo 1024605 1025883 := bstep (se 1 (by rfl) ⟨769412, by rfl⟩ : syracuseStep 1025883 = 1538825) B1538825
theorem B2926525 : Blo 1024605 2926525 := bstep (se 3 (by rfl) ⟨548723, by rfl⟩ : syracuseStep 2926525 = 1097447) B1097447
theorem B2598875 : Blo 1024605 2598875 := bstep (se 1 (by rfl) ⟨1949156, by rfl⟩ : syracuseStep 2598875 = 3898313) B3898313
theorem B2598905 : Blo 1024605 2598905 := bstep (se 2 (by rfl) ⟨974589, by rfl⟩ : syracuseStep 2598905 = 1949179) B1949179
theorem B23734417 : Blo 1024605 23734417 := bstep (se 2 (by rfl) ⟨8900406, by rfl⟩ : syracuseStep 23734417 = 17800813) B17800813
theorem B53389523 : Blo 1024605 53389523 := bstep (se 1 (by rfl) ⟨40042142, by rfl⟩ : syracuseStep 53389523 = 80084285) B80084285
theorem B1026463 : Blo 1024605 1026463 := bstep (se 1 (by rfl) ⟨769847, by rfl⟩ : syracuseStep 1026463 = 1539695) B1539695
theorem B3287471 : Blo 1024605 3287471 := bstep (se 1 (by rfl) ⟨2465603, by rfl⟩ : syracuseStep 3287471 = 4931207) B4931207
theorem B1026543 : Blo 1024605 1026543 := bstep (se 1 (by rfl) ⟨769907, by rfl⟩ : syracuseStep 1026543 = 1539815) B1539815
theorem B3123731 : Blo 1024605 3123731 := bstep (se 1 (by rfl) ⟨2342798, by rfl⟩ : syracuseStep 3123731 = 4685597) B4685597
theorem B1026671 : Blo 1024605 1026671 := bstep (se 1 (by rfl) ⟨770003, by rfl⟩ : syracuseStep 1026671 = 1540007) B1540007
theorem B17509121 : Blo 1024605 17509121 := bstep (se 2 (by rfl) ⟨6565920, by rfl⟩ : syracuseStep 17509121 = 13131841) B13131841
theorem B1026887 : Blo 1024605 1026887 := bstep (se 1 (by rfl) ⟨770165, by rfl⟩ : syracuseStep 1026887 = 1540331) B1540331
theorem B1026927 : Blo 1024605 1026927 := bstep (se 1 (by rfl) ⟨770195, by rfl⟩ : syracuseStep 1026927 = 1540391) B1540391
theorem B1027375 : Blo 1024605 1027375 := bstep (se 1 (by rfl) ⟨770531, by rfl⟩ : syracuseStep 1027375 = 1541063) B1541063
theorem B18722177 : Blo 1024605 18722177 := bstep (se 2 (by rfl) ⟨7020816, by rfl⟩ : syracuseStep 18722177 = 14041633) B14041633
theorem B2305439 : Blo 1024605 2305439 := bstep (se 1 (by rfl) ⟨1729079, by rfl⟩ : syracuseStep 2305439 = 3458159) B3458159
theorem B1027487 : Blo 1024605 1027487 := bstep (se 1 (by rfl) ⟨770615, by rfl⟩ : syracuseStep 1027487 = 1541231) B1541231
theorem B2305511 : Blo 1024605 2305511 := bstep (se 1 (by rfl) ⟨1729133, by rfl⟩ : syracuseStep 2305511 = 3458267) B3458267
theorem B1027615 : Blo 1024605 1027615 := bstep (se 1 (by rfl) ⟨770711, by rfl⟩ : syracuseStep 1027615 = 1541423) B1541423
theorem B5189183 : Blo 1024605 5189183 := bstep (se 1 (by rfl) ⟨3891887, by rfl⟩ : syracuseStep 5189183 = 7783775) B7783775
theorem B1027751 : Blo 1024605 1027751 := bstep (se 1 (by rfl) ⟨770813, by rfl⟩ : syracuseStep 1027751 = 1541627) B1541627
theorem B1027775 : Blo 1024605 1027775 := bstep (se 1 (by rfl) ⟨770831, by rfl⟩ : syracuseStep 1027775 = 1541663) B1541663
theorem B1027871 : Blo 1024605 1027871 := bstep (se 1 (by rfl) ⟨770903, by rfl⟩ : syracuseStep 1027871 = 1541807) B1541807
theorem B1027951 : Blo 1024605 1027951 := bstep (se 1 (by rfl) ⟨770963, by rfl⟩ : syracuseStep 1027951 = 1541927) B1541927
theorem B6565769 : Blo 1024605 6565769 := bstep (se 2 (by rfl) ⟨2462163, by rfl⟩ : syracuseStep 6565769 = 4924327) B4924327
theorem B1028319 : Blo 1024605 1028319 := bstep (se 1 (by rfl) ⟨771239, by rfl⟩ : syracuseStep 1028319 = 1542479) B1542479
theorem B2601193 : Blo 1024605 2601193 := bstep (se 2 (by rfl) ⟨975447, by rfl⟩ : syracuseStep 2601193 = 1950895) B1950895
theorem B1028351 : Blo 1024605 1028351 := bstep (se 1 (by rfl) ⟨771263, by rfl⟩ : syracuseStep 1028351 = 1542527) B1542527
theorem B1028379 : Blo 1024605 1028379 := bstep (se 1 (by rfl) ⟨771284, by rfl⟩ : syracuseStep 1028379 = 1542569) B1542569
theorem B2306465 : Blo 1024605 2306465 := bstep (se 2 (by rfl) ⟨864924, by rfl⟩ : syracuseStep 2306465 = 1729849) B1729849
theorem B29635217 : Blo 1024605 29635217 := bstep (se 2 (by rfl) ⟨11113206, by rfl⟩ : syracuseStep 29635217 = 22226413) B22226413
theorem B74920727 : Blo 1024605 74920727 := bstep (se 1 (by rfl) ⟨56190545, by rfl⟩ : syracuseStep 74920727 = 112381091) B112381091
theorem B1946423 : Blo 1024605 1946423 := bstep (se 1 (by rfl) ⟨1459817, by rfl⟩ : syracuseStep 1946423 = 2919635) B2919635
theorem B2602145 : Blo 1024605 2602145 := bstep (se 2 (by rfl) ⟨975804, by rfl⟩ : syracuseStep 2602145 = 1951609) B1951609
theorem B1947007 : Blo 1024605 1947007 := bstep (se 1 (by rfl) ⟨1460255, by rfl⟩ : syracuseStep 1947007 = 2920511) B2920511
theorem B19707299 : Blo 1024605 19707299 := bstep (se 1 (by rfl) ⟨14780474, by rfl⟩ : syracuseStep 19707299 = 29560949) B29560949
theorem B5191127 : Blo 1024605 5191127 := bstep (se 1 (by rfl) ⟨3893345, by rfl⟩ : syracuseStep 5191127 = 7786691) B7786691
theorem B2307995 : Blo 1024605 2307995 := bstep (se 1 (by rfl) ⟨1730996, by rfl⟩ : syracuseStep 2307995 = 3461993) B3461993
theorem B77118227 : Blo 1024605 77118227 := bstep (se 1 (by rfl) ⟨57838670, by rfl⟩ : syracuseStep 77118227 = 115677341) B115677341
theorem B5847947 : Blo 1024605 5847947 := bstep (se 1 (by rfl) ⟨4385960, by rfl⟩ : syracuseStep 5847947 = 8771921) B8771921
theorem B1096687 : Blo 1024605 1096687 := bstep (se 1 (by rfl) ⟨822515, by rfl⟩ : syracuseStep 1096687 = 1645031) B1645031
theorem B5848199 : Blo 1024605 5848199 := bstep (se 1 (by rfl) ⟨4386149, by rfl⟩ : syracuseStep 5848199 = 8772299) B8772299
theorem B2309327 : Blo 1024605 2309327 := bstep (se 1 (by rfl) ⟨1731995, by rfl⟩ : syracuseStep 2309327 = 3463991) B3463991
theorem B2309417 : Blo 1024605 2309417 := bstep (se 2 (by rfl) ⟨866031, by rfl⟩ : syracuseStep 2309417 = 1732063) B1732063
theorem B2309705 : Blo 1024605 2309705 := bstep (se 2 (by rfl) ⟨866139, by rfl⟩ : syracuseStep 2309705 = 1732279) B1732279
theorem B10534711 : Blo 1024605 10534711 := bstep (se 1 (by rfl) ⟨7901033, by rfl⟩ : syracuseStep 10534711 = 15802067) B15802067
theorem B2310047 : Blo 1024605 2310047 := bstep (se 1 (by rfl) ⟨1732535, by rfl⟩ : syracuseStep 2310047 = 3465071) B3465071
theorem B5193719 : Blo 1024605 5193719 := bstep (se 1 (by rfl) ⟨3895289, by rfl⟩ : syracuseStep 5193719 = 7790579) B7790579
theorem B49922239 : Blo 1024605 49922239 := bstep (se 1 (by rfl) ⟨37441679, by rfl⟩ : syracuseStep 49922239 = 74883359) B74883359
theorem B2310623 : Blo 1024605 2310623 := bstep (se 1 (by rfl) ⟨1732967, by rfl⟩ : syracuseStep 2310623 = 3465935) B3465935
theorem B2310875 : Blo 1024605 2310875 := bstep (se 1 (by rfl) ⟨1733156, by rfl⟩ : syracuseStep 2310875 = 3466313) B3466313
theorem B2770195 : Blo 1024605 2770195 := bstep (se 1 (by rfl) ⟨2077646, by rfl⟩ : syracuseStep 2770195 = 4155293) B4155293
theorem B5195177 : Blo 1024605 5195177 := bstep (se 2 (by rfl) ⟨1948191, by rfl⟩ : syracuseStep 5195177 = 3896383) B3896383
theorem B5195663 : Blo 1024605 5195663 := bstep (se 1 (by rfl) ⟨3896747, by rfl⟩ : syracuseStep 5195663 = 7793495) B7793495
theorem B6572177 : Blo 1024605 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B1951951 : Blo 1024605 1951951 := bstep (se 1 (by rfl) ⟨1463963, by rfl⟩ : syracuseStep 1951951 = 2927927) B2927927
theorem B4377007 : Blo 1024605 4377007 := bstep (se 1 (by rfl) ⟨3282755, by rfl⟩ : syracuseStep 4377007 = 6565511) B6565511
theorem B11684411 : Blo 1024605 11684411 := bstep (se 1 (by rfl) ⟨8763308, by rfl⟩ : syracuseStep 11684411 = 17526617) B17526617
theorem B18729605 : Blo 1024605 18729605 := bstep (se 4 (by rfl) ⟨1755900, by rfl⟩ : syracuseStep 18729605 = 3511801) B3511801
theorem B5196635 : Blo 1024605 5196635 := bstep (se 1 (by rfl) ⟨3897476, by rfl⟩ : syracuseStep 5196635 = 7794953) B7794953
theorem B112283009 : Blo 1024605 112283009 := bstep (se 2 (by rfl) ⟨42106128, by rfl⟩ : syracuseStep 112283009 = 84212257) B84212257
theorem B1756991 : Blo 1024605 1756991 := bstep (se 1 (by rfl) ⟨1317743, by rfl⟩ : syracuseStep 1756991 = 2635487) B2635487
theorem B3461183 : Blo 1024605 3461183 := bstep (se 1 (by rfl) ⟨2595887, by rfl⟩ : syracuseStep 3461183 = 5191775) B5191775
theorem B2773223 : Blo 1024605 2773223 := bstep (se 1 (by rfl) ⟨2079917, by rfl⟩ : syracuseStep 2773223 = 4159835) B4159835
theorem B23679539 : Blo 1024605 23679539 := bstep (se 1 (by rfl) ⟨17759654, by rfl⟩ : syracuseStep 23679539 = 35519309) B35519309
theorem B5198417 : Blo 1024605 5198417 := bstep (se 2 (by rfl) ⟨1949406, by rfl⟩ : syracuseStep 5198417 = 3898813) B3898813
theorem B5853779 : Blo 1024605 5853779 := bstep (se 1 (by rfl) ⟨4390334, by rfl⟩ : syracuseStep 5853779 = 8780669) B8780669
theorem B4379777 : Blo 1024605 4379777 := bstep (se 2 (by rfl) ⟨1642416, by rfl⟩ : syracuseStep 4379777 = 3284833) B3284833
theorem B1463599 : Blo 1024605 1463599 := bstep (se 1 (by rfl) ⟨1097699, by rfl⟩ : syracuseStep 1463599 = 2195399) B2195399
theorem B28104043 : Blo 1024605 28104043 := bstep (se 1 (by rfl) ⟨21078032, by rfl⟩ : syracuseStep 28104043 = 42156065) B42156065
theorem B1300207 : Blo 1024605 1300207 := bstep (se 1 (by rfl) ⟨975155, by rfl⟩ : syracuseStep 1300207 = 1950311) B1950311
theorem B84432689 : Blo 1024605 84432689 := bstep (se 2 (by rfl) ⟨31662258, by rfl⟩ : syracuseStep 84432689 = 63324517) B63324517
theorem B168450191 : Blo 1024605 168450191 := bstep (se 1 (by rfl) ⟨126337643, by rfl⟩ : syracuseStep 168450191 = 252675287) B252675287
theorem B13359653 : Blo 1024605 13359653 := bstep (se 4 (by rfl) ⟨1252467, by rfl⟩ : syracuseStep 13359653 = 2504935) B2504935
theorem B13163417 : Blo 1024605 13163417 := bstep (se 2 (by rfl) ⟨4936281, by rfl⟩ : syracuseStep 13163417 = 9872563) B9872563
theorem B2809721 : Blo 1024605 2809721 := bstep (se 2 (by rfl) ⟨1053645, by rfl⟩ : syracuseStep 2809721 = 2107291) B2107291
theorem B2777483 : Blo 1024605 2777483 := bstep (se 1 (by rfl) ⟨2083112, by rfl⟩ : syracuseStep 2777483 = 4166225) B4166225
theorem B6250891 : Blo 1024605 6250891 := bstep (se 1 (by rfl) ⟨4688168, by rfl⟩ : syracuseStep 6250891 = 9376337) B9376337
theorem B3891827 : Blo 1024605 3891827 := bstep (se 1 (by rfl) ⟨2918870, by rfl⟩ : syracuseStep 3891827 = 5837741) B5837741
theorem B7037675 : Blo 1024605 7037675 := bstep (se 1 (by rfl) ⟨5278256, by rfl⟩ : syracuseStep 7037675 = 10556513) B10556513
theorem B3892009 : Blo 1024605 3892009 := bstep (se 2 (by rfl) ⟨1459503, by rfl⟩ : syracuseStep 3892009 = 2919007) B2919007
theorem B21390911 : Blo 1024605 21390911 := bstep (se 1 (by rfl) ⟨16043183, by rfl⟩ : syracuseStep 21390911 = 32086367) B32086367
theorem B4155259 : Blo 1024605 4155259 := bstep (se 1 (by rfl) ⟨3116444, by rfl⟩ : syracuseStep 4155259 = 6232889) B6232889
theorem B23717879 : Blo 1024605 23717879 := bstep (se 1 (by rfl) ⟨17788409, by rfl⟩ : syracuseStep 23717879 = 35576819) B35576819
theorem B13330919 : Blo 1024605 13330919 := bstep (se 1 (by rfl) ⟨9998189, by rfl⟩ : syracuseStep 13330919 = 19996379) B19996379
theorem B6580889 : Blo 1024605 6580889 := bstep (se 2 (by rfl) ⟨2467833, by rfl⟩ : syracuseStep 6580889 = 4935667) B4935667
theorem B1731449 : Blo 1024605 1731449 := bstep (se 2 (by rfl) ⟨649293, by rfl⟩ : syracuseStep 1731449 = 1298587) B1298587
theorem B8776673 : Blo 1024605 8776673 := bstep (se 2 (by rfl) ⟨3291252, by rfl⟩ : syracuseStep 8776673 = 6582505) B6582505
theorem B2780335 : Blo 1024605 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B2191067 : Blo 1024605 2191067 := bstep (se 1 (by rfl) ⟨1643300, by rfl⟩ : syracuseStep 2191067 = 3286601) B3286601
theorem B1667047 : Blo 1024605 1667047 := bstep (se 1 (by rfl) ⟨1250285, by rfl⟩ : syracuseStep 1667047 = 2500571) B2500571
theorem B71233667 : Blo 1024605 71233667 := bstep (se 1 (by rfl) ⟨53425250, by rfl⟩ : syracuseStep 71233667 = 106850501) B106850501
theorem B3469931 : Blo 1024605 3469931 := bstep (se 1 (by rfl) ⟨2602448, by rfl⟩ : syracuseStep 3469931 = 5204897) B5204897
theorem B1733467 : Blo 1024605 1733467 := bstep (se 1 (by rfl) ⟨1300100, by rfl⟩ : syracuseStep 1733467 = 2600201) B2600201
theorem B7107425 : Blo 1024605 7107425 := bstep (se 2 (by rfl) ⟨2665284, by rfl⟩ : syracuseStep 7107425 = 5330569) B5330569
theorem B1537001 : Blo 1024605 1537001 := bstep (se 2 (by rfl) ⟨576375, by rfl⟩ : syracuseStep 1537001 = 1152751) B1152751
theorem B4158535 : Blo 1024605 4158535 := bstep (se 1 (by rfl) ⟨3118901, by rfl⟩ : syracuseStep 4158535 = 6237803) B6237803
theorem B1537145 : Blo 1024605 1537145 := bstep (se 2 (by rfl) ⟨576429, by rfl⟩ : syracuseStep 1537145 = 1152859) B1152859
theorem B3470471 : Blo 1024605 3470471 := bstep (se 1 (by rfl) ⟨2602853, by rfl⟩ : syracuseStep 3470471 = 5205707) B5205707
theorem B1537673 : Blo 1024605 1537673 := bstep (se 2 (by rfl) ⟨576627, by rfl⟩ : syracuseStep 1537673 = 1153255) B1153255
theorem B4388489 : Blo 1024605 4388489 := bstep (se 2 (by rfl) ⟨1645683, by rfl⟩ : syracuseStep 4388489 = 3291367) B3291367
theorem B11106031 : Blo 1024605 11106031 := bstep (se 1 (by rfl) ⟨8329523, by rfl⟩ : syracuseStep 11106031 = 16659047) B16659047
theorem B2225951 : Blo 1024605 2225951 := bstep (se 1 (by rfl) ⟨1669463, by rfl⟩ : syracuseStep 2225951 = 3338927) B3338927
theorem B1537883 : Blo 1024605 1537883 := bstep (se 1 (by rfl) ⟨1153412, by rfl⟩ : syracuseStep 1537883 = 2306825) B2306825
theorem B1537919 : Blo 1024605 1537919 := bstep (se 1 (by rfl) ⟨1153439, by rfl⟩ : syracuseStep 1537919 = 2306879) B2306879
theorem B1734527 : Blo 1024605 1734527 := bstep (se 1 (by rfl) ⟨1300895, by rfl⟩ : syracuseStep 1734527 = 2601791) B2601791
theorem B1538015 : Blo 1024605 1538015 := bstep (se 1 (by rfl) ⟨1153511, by rfl⟩ : syracuseStep 1538015 = 2307023) B2307023
theorem B1538075 : Blo 1024605 1538075 := bstep (se 1 (by rfl) ⟨1153556, by rfl⟩ : syracuseStep 1538075 = 2307113) B2307113
theorem B9992297 : Blo 1024605 9992297 := bstep (se 2 (by rfl) ⟨3747111, by rfl⟩ : syracuseStep 9992297 = 7494223) B7494223
theorem B7796897 : Blo 1024605 7796897 := bstep (se 2 (by rfl) ⟨2923836, by rfl⟩ : syracuseStep 7796897 = 5847673) B5847673
theorem B8779985 : Blo 1024605 8779985 := bstep (se 2 (by rfl) ⟨3292494, by rfl⟩ : syracuseStep 8779985 = 6584989) B6584989
theorem B1538267 : Blo 1024605 1538267 := bstep (se 1 (by rfl) ⟨1153700, by rfl⟩ : syracuseStep 1538267 = 2307401) B2307401
theorem B22214999 : Blo 1024605 22214999 := bstep (se 1 (by rfl) ⟨16661249, by rfl⟩ : syracuseStep 22214999 = 33322499) B33322499
theorem B5929307 : Blo 1024605 5929307 := bstep (se 1 (by rfl) ⟨4446980, by rfl⟩ : syracuseStep 5929307 = 8893961) B8893961
theorem B1538537 : Blo 1024605 1538537 := bstep (se 2 (by rfl) ⟨576951, by rfl⟩ : syracuseStep 1538537 = 1153903) B1153903
theorem B23690063 : Blo 1024605 23690063 := bstep (se 1 (by rfl) ⟨17767547, by rfl⟩ : syracuseStep 23690063 = 35535095) B35535095
theorem B1538927 : Blo 1024605 1538927 := bstep (se 1 (by rfl) ⟨1154195, by rfl⟩ : syracuseStep 1538927 = 2308391) B2308391
theorem B1539167 : Blo 1024605 1539167 := bstep (se 1 (by rfl) ⟨1154375, by rfl⟩ : syracuseStep 1539167 = 2308751) B2308751
theorem B1539227 : Blo 1024605 1539227 := bstep (se 1 (by rfl) ⟨1154420, by rfl⟩ : syracuseStep 1539227 = 2308841) B2308841
theorem B8322263 : Blo 1024605 8322263 := bstep (se 1 (by rfl) ⟨6241697, by rfl⟩ : syracuseStep 8322263 = 12483395) B12483395
theorem B3898601 : Blo 1024605 3898601 := bstep (se 2 (by rfl) ⟨1461975, by rfl⟩ : syracuseStep 3898601 = 2923951) B2923951
theorem B19004669 : Blo 1024605 19004669 := bstep (se 3 (by rfl) ⟨3563375, by rfl⟩ : syracuseStep 19004669 = 7126751) B7126751
theorem B1539383 : Blo 1024605 1539383 := bstep (se 1 (by rfl) ⟨1154537, by rfl⟩ : syracuseStep 1539383 = 2309075) B2309075
theorem B1539563 : Blo 1024605 1539563 := bstep (se 1 (by rfl) ⟨1154672, by rfl⟩ : syracuseStep 1539563 = 2309345) B2309345
theorem B1539767 : Blo 1024605 1539767 := bstep (se 1 (by rfl) ⟨1154825, by rfl⟩ : syracuseStep 1539767 = 2309651) B2309651
theorem B5275421 : Blo 1024605 5275421 := bstep (se 3 (by rfl) ⟨989141, by rfl⟩ : syracuseStep 5275421 = 1978283) B1978283
theorem B1539977 : Blo 1024605 1539977 := bstep (se 2 (by rfl) ⟨577491, by rfl⟩ : syracuseStep 1539977 = 1154983) B1154983
theorem B1540415 : Blo 1024605 1540415 := bstep (se 1 (by rfl) ⟨1155311, by rfl⟩ : syracuseStep 1540415 = 2310623) B2310623
theorem B1540583 : Blo 1024605 1540583 := bstep (se 1 (by rfl) ⟨1155437, by rfl⟩ : syracuseStep 1540583 = 2310875) B2310875
theorem B2196193 : Blo 1024605 2196193 := bstep (se 2 (by rfl) ⟨823572, by rfl⟩ : syracuseStep 2196193 = 1647145) B1647145
theorem B12486403 : Blo 1024605 12486403 := bstep (se 1 (by rfl) ⟨9364802, by rfl⟩ : syracuseStep 12486403 = 18729605) B18729605
theorem B7801271 : Blo 1024605 7801271 := bstep (se 1 (by rfl) ⟨5850953, by rfl⟩ : syracuseStep 7801271 = 11701907) B11701907
theorem B5540345 : Blo 1024605 5540345 := bstep (se 2 (by rfl) ⟨2077629, by rfl⟩ : syracuseStep 5540345 = 4155259) B4155259
theorem B3902033 : Blo 1024605 3902033 := bstep (se 2 (by rfl) ⟨1463262, by rfl⟩ : syracuseStep 3902033 = 2926525) B2926525
theorem B3902519 : Blo 1024605 3902519 := bstep (se 1 (by rfl) ⟨2926889, by rfl⟩ : syracuseStep 3902519 = 5853779) B5853779
theorem B8785043 : Blo 1024605 8785043 := bstep (se 1 (by rfl) ⟨6588782, by rfl⟩ : syracuseStep 8785043 = 13177565) B13177565
theorem B5836009 : Blo 1024605 5836009 := bstep (se 2 (by rfl) ⟨2188503, by rfl⟩ : syracuseStep 5836009 = 4377007) B4377007
theorem B2919851 : Blo 1024605 2919851 := bstep (se 1 (by rfl) ⟨2189888, by rfl⟩ : syracuseStep 2919851 = 4379777) B4379777
theorem B56102975 : Blo 1024605 56102975 := bstep (se 1 (by rfl) ⟨42077231, by rfl⟩ : syracuseStep 56102975 = 84154463) B84154463
theorem B112300127 : Blo 1024605 112300127 := bstep (se 1 (by rfl) ⟨84225095, by rfl⟩ : syracuseStep 112300127 = 168450191) B168450191
theorem B3805703 : Blo 1024605 3805703 := bstep (se 1 (by rfl) ⟨2854277, by rfl⟩ : syracuseStep 3805703 = 5708555) B5708555
theorem B1873147 : Blo 1024605 1873147 := bstep (se 1 (by rfl) ⟨1404860, by rfl⟩ : syracuseStep 1873147 = 2809721) B2809721
theorem B2594551 : Blo 1024605 2594551 := bstep (se 1 (by rfl) ⟨1945913, by rfl⟩ : syracuseStep 2594551 = 3891827) B3891827
theorem B4691783 : Blo 1024605 4691783 := bstep (se 1 (by rfl) ⟨3518837, by rfl⟩ : syracuseStep 4691783 = 7037675) B7037675
theorem B8001371 : Blo 1024605 8001371 := bstep (se 1 (by rfl) ⟨6001028, by rfl⟩ : syracuseStep 8001371 = 12002057) B12002057
theorem B14260607 : Blo 1024605 14260607 := bstep (se 1 (by rfl) ⟨10695455, by rfl⟩ : syracuseStep 14260607 = 21390911) B21390911
theorem B8329949 : Blo 1024605 8329949 := bstep (se 3 (by rfl) ⟨1561865, by rfl⟩ : syracuseStep 8329949 = 3123731) B3123731
theorem B5544713 : Blo 1024605 5544713 := bstep (se 2 (by rfl) ⟨2079267, by rfl⟩ : syracuseStep 5544713 = 4158535) B4158535
theorem B35593015 : Blo 1024605 35593015 := bstep (se 1 (by rfl) ⟨26694761, by rfl⟩ : syracuseStep 35593015 = 53389523) B53389523
theorem B2596009 : Blo 1024605 2596009 := bstep (se 2 (by rfl) ⟨973503, by rfl⟩ : syracuseStep 2596009 = 1947007) B1947007
theorem B11672747 : Blo 1024605 11672747 := bstep (se 1 (by rfl) ⟨8754560, by rfl⟩ : syracuseStep 11672747 = 17509121) B17509121
theorem B1154299 : Blo 1024605 1154299 := bstep (se 1 (by rfl) ⟨865724, by rfl⟩ : syracuseStep 1154299 = 1731449) B1731449
theorem B47489111 : Blo 1024605 47489111 := bstep (se 1 (by rfl) ⟨35616833, by rfl⟩ : syracuseStep 47489111 = 71233667) B71233667
theorem B49947151 : Blo 1024605 49947151 := bstep (se 1 (by rfl) ⟨37460363, by rfl⟩ : syracuseStep 49947151 = 74920727) B74920727
theorem B1024667 : Blo 1024605 1024667 := bstep (se 1 (by rfl) ⟨768500, by rfl⟩ : syracuseStep 1024667 = 1537001) B1537001
theorem B1024763 : Blo 1024605 1024763 := bstep (se 1 (by rfl) ⟨768572, by rfl⟩ : syracuseStep 1024763 = 1537145) B1537145
theorem B1025115 : Blo 1024605 1025115 := bstep (se 1 (by rfl) ⟨768836, by rfl⟩ : syracuseStep 1025115 = 1537673) B1537673
theorem B2925659 : Blo 1024605 2925659 := bstep (se 1 (by rfl) ⟨2194244, by rfl⟩ : syracuseStep 2925659 = 4388489) B4388489
theorem B1483967 : Blo 1024605 1483967 := bstep (se 1 (by rfl) ⟨1112975, by rfl⟩ : syracuseStep 1483967 = 2225951) B2225951
theorem B1025255 : Blo 1024605 1025255 := bstep (se 1 (by rfl) ⟨768941, by rfl⟩ : syracuseStep 1025255 = 1537883) B1537883
theorem B1025279 : Blo 1024605 1025279 := bstep (se 1 (by rfl) ⟨768959, by rfl⟩ : syracuseStep 1025279 = 1537919) B1537919
theorem B1156351 : Blo 1024605 1156351 := bstep (se 1 (by rfl) ⟨867263, by rfl⟩ : syracuseStep 1156351 = 1734527) B1734527
theorem B1025343 : Blo 1024605 1025343 := bstep (se 1 (by rfl) ⟨769007, by rfl⟩ : syracuseStep 1025343 = 1538015) B1538015
theorem B1025383 : Blo 1024605 1025383 := bstep (se 1 (by rfl) ⟨769037, by rfl⟩ : syracuseStep 1025383 = 1538075) B1538075
theorem B6661531 : Blo 1024605 6661531 := bstep (se 1 (by rfl) ⟨4996148, by rfl⟩ : syracuseStep 6661531 = 9992297) B9992297
theorem B1025511 : Blo 1024605 1025511 := bstep (se 1 (by rfl) ⟨769133, by rfl⟩ : syracuseStep 1025511 = 1538267) B1538267
theorem B1025691 : Blo 1024605 1025691 := bstep (se 1 (by rfl) ⟨769268, by rfl⟩ : syracuseStep 1025691 = 1538537) B1538537
theorem B1025951 : Blo 1024605 1025951 := bstep (se 1 (by rfl) ⟨769463, by rfl⟩ : syracuseStep 1025951 = 1538927) B1538927
theorem B1026111 : Blo 1024605 1026111 := bstep (se 1 (by rfl) ⟨769583, by rfl⟩ : syracuseStep 1026111 = 1539167) B1539167
theorem B1026151 : Blo 1024605 1026151 := bstep (se 1 (by rfl) ⟨769613, by rfl⟩ : syracuseStep 1026151 = 1539227) B1539227
theorem B5548175 : Blo 1024605 5548175 := bstep (se 1 (by rfl) ⟨4161131, by rfl⟩ : syracuseStep 5548175 = 8322263) B8322263
theorem B2599067 : Blo 1024605 2599067 := bstep (se 1 (by rfl) ⟨1949300, by rfl⟩ : syracuseStep 2599067 = 3898601) B3898601
theorem B1026255 : Blo 1024605 1026255 := bstep (se 1 (by rfl) ⟨769691, by rfl⟩ : syracuseStep 1026255 = 1539383) B1539383
theorem B1026375 : Blo 1024605 1026375 := bstep (se 1 (by rfl) ⟨769781, by rfl⟩ : syracuseStep 1026375 = 1539563) B1539563
theorem B1026511 : Blo 1024605 1026511 := bstep (se 1 (by rfl) ⟨769883, by rfl⟩ : syracuseStep 1026511 = 1539767) B1539767
theorem B3516947 : Blo 1024605 3516947 := bstep (se 1 (by rfl) ⟨2637710, by rfl⟩ : syracuseStep 3516947 = 5275421) B5275421
theorem B1026651 : Blo 1024605 1026651 := bstep (se 1 (by rfl) ⟨769988, by rfl⟩ : syracuseStep 1026651 = 1539977) B1539977
theorem B1026815 : Blo 1024605 1026815 := bstep (se 1 (by rfl) ⟨770111, by rfl⟩ : syracuseStep 1026815 = 1540223) B1540223
theorem B66562985 : Blo 1024605 66562985 := bstep (se 2 (by rfl) ⟨24961119, by rfl⟩ : syracuseStep 66562985 = 49922239) B49922239
theorem B1027007 : Blo 1024605 1027007 := bstep (se 1 (by rfl) ⟨770255, by rfl⟩ : syracuseStep 1027007 = 1540511) B1540511
theorem B25668679 : Blo 1024605 25668679 := bstep (se 1 (by rfl) ⟨19251509, by rfl⟩ : syracuseStep 25668679 = 38503019) B38503019
theorem B1027183 : Blo 1024605 1027183 := bstep (se 1 (by rfl) ⟨770387, by rfl⟩ : syracuseStep 1027183 = 1540775) B1540775
theorem B8334521 : Blo 1024605 8334521 := bstep (se 2 (by rfl) ⟨3125445, by rfl⟩ : syracuseStep 8334521 = 6250891) B6250891
theorem B1027263 : Blo 1024605 1027263 := bstep (se 1 (by rfl) ⟨770447, by rfl⟩ : syracuseStep 1027263 = 1540895) B1540895
theorem B2469055 : Blo 1024605 2469055 := bstep (se 1 (by rfl) ⟨1851791, by rfl⟩ : syracuseStep 2469055 = 3703583) B3703583
theorem B1027279 : Blo 1024605 1027279 := bstep (se 1 (by rfl) ⟨770459, by rfl⟩ : syracuseStep 1027279 = 1540919) B1540919
theorem B1027399 : Blo 1024605 1027399 := bstep (se 1 (by rfl) ⟨770549, by rfl⟩ : syracuseStep 1027399 = 1541099) B1541099
theorem B2600363 : Blo 1024605 2600363 := bstep (se 1 (by rfl) ⟨1950272, by rfl⟩ : syracuseStep 2600363 = 3900545) B3900545
theorem B1027739 : Blo 1024605 1027739 := bstep (se 1 (by rfl) ⟨770804, by rfl⟩ : syracuseStep 1027739 = 1541609) B1541609
theorem B5189345 : Blo 1024605 5189345 := bstep (se 2 (by rfl) ⟨1946004, by rfl⟩ : syracuseStep 5189345 = 3892009) B3892009
theorem B1027999 : Blo 1024605 1027999 := bstep (se 1 (by rfl) ⟨770999, by rfl⟩ : syracuseStep 1027999 = 1541999) B1541999
theorem B1028123 : Blo 1024605 1028123 := bstep (se 1 (by rfl) ⟨771092, by rfl⟩ : syracuseStep 1028123 = 1542185) B1542185
theorem B1028143 : Blo 1024605 1028143 := bstep (se 1 (by rfl) ⟨771107, by rfl⟩ : syracuseStep 1028143 = 1542215) B1542215
theorem B1028263 : Blo 1024605 1028263 := bstep (se 1 (by rfl) ⟨771197, by rfl⟩ : syracuseStep 1028263 = 1542395) B1542395
theorem B3289369 : Blo 1024605 3289369 := bstep (se 2 (by rfl) ⟨1233513, by rfl⟩ : syracuseStep 3289369 = 2467027) B2467027
theorem B1945883 : Blo 1024605 1945883 := bstep (se 1 (by rfl) ⟨1459412, by rfl⟩ : syracuseStep 1945883 = 2918825) B2918825
theorem B1028399 : Blo 1024605 1028399 := bstep (se 1 (by rfl) ⟨771299, by rfl⟩ : syracuseStep 1028399 = 1542599) B1542599
theorem B1028543 : Blo 1024605 1028543 := bstep (se 1 (by rfl) ⟨771407, by rfl⟩ : syracuseStep 1028543 = 1542815) B1542815
theorem B1028575 : Blo 1024605 1028575 := bstep (se 1 (by rfl) ⟨771431, by rfl⟩ : syracuseStep 1028575 = 1542863) B1542863
theorem B134787635 : Blo 1024605 134787635 := bstep (se 1 (by rfl) ⟨101090726, by rfl⟩ : syracuseStep 134787635 = 202181453) B202181453
theorem B44020615 : Blo 1024605 44020615 := bstep (se 1 (by rfl) ⟨33015461, by rfl⟩ : syracuseStep 44020615 = 66030923) B66030923
theorem B74855339 : Blo 1024605 74855339 := bstep (se 1 (by rfl) ⟨56141504, by rfl⟩ : syracuseStep 74855339 = 112283009) B112283009
theorem B2307455 : Blo 1024605 2307455 := bstep (se 1 (by rfl) ⟨1730591, by rfl⟩ : syracuseStep 2307455 = 3461183) B3461183
theorem B1848815 : Blo 1024605 1848815 := bstep (se 1 (by rfl) ⟨1386611, by rfl⟩ : syracuseStep 1848815 = 2773223) B2773223
theorem B2602601 : Blo 1024605 2602601 := bstep (se 2 (by rfl) ⟨975975, by rfl⟩ : syracuseStep 2602601 = 1951951) B1951951
theorem B1948063 : Blo 1024605 1948063 := bstep (se 1 (by rfl) ⟨1461047, by rfl⟩ : syracuseStep 1948063 = 2922095) B2922095
theorem B6568381 : Blo 1024605 6568381 := bstep (se 3 (by rfl) ⟨1231571, by rfl⟩ : syracuseStep 6568381 = 2463143) B2463143
theorem B1948207 : Blo 1024605 1948207 := bstep (se 1 (by rfl) ⟨1461155, by rfl⟩ : syracuseStep 1948207 = 2922311) B2922311
theorem B1949339 : Blo 1024605 1949339 := bstep (se 1 (by rfl) ⟨1462004, by rfl⟩ : syracuseStep 1949339 = 2924009) B2924009
theorem B1851655 : Blo 1024605 1851655 := bstep (se 1 (by rfl) ⟨1388741, by rfl⟩ : syracuseStep 1851655 = 2777483) B2777483
theorem B14828453 : Blo 1024605 14828453 := bstep (se 4 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 14828453 = 2780335) B2780335
theorem B2311289 : Blo 1024605 2311289 := bstep (se 2 (by rfl) ⟨866733, by rfl⟩ : syracuseStep 2311289 = 1733467) B1733467
theorem B8766589 : Blo 1024605 8766589 := bstep (se 3 (by rfl) ⟨1643735, by rfl⟩ : syracuseStep 8766589 = 3287471) B3287471
theorem B15811919 : Blo 1024605 15811919 := bstep (se 1 (by rfl) ⟨11858939, by rfl⟩ : syracuseStep 15811919 = 23717879) B23717879
theorem B3458537 : Blo 1024605 3458537 := bstep (se 2 (by rfl) ⟨1296951, by rfl⟩ : syracuseStep 3458537 = 2593903) B2593903
theorem B1951465 : Blo 1024605 1951465 := bstep (se 2 (by rfl) ⟨731799, by rfl⟩ : syracuseStep 1951465 = 1463599) B1463599
theorem B37472057 : Blo 1024605 37472057 := bstep (se 2 (by rfl) ⟨14052021, by rfl⟩ : syracuseStep 37472057 = 28104043) B28104043
theorem B5851115 : Blo 1024605 5851115 := bstep (se 1 (by rfl) ⟨4388336, by rfl⟩ : syracuseStep 5851115 = 8776673) B8776673
theorem B3459455 : Blo 1024605 3459455 := bstep (se 1 (by rfl) ⟨2594591, by rfl⟩ : syracuseStep 3459455 = 5189183) B5189183
theorem B1460711 : Blo 1024605 1460711 := bstep (se 1 (by rfl) ⟨1095533, by rfl⟩ : syracuseStep 1460711 = 2191067) B2191067
theorem B4377179 : Blo 1024605 4377179 := bstep (se 1 (by rfl) ⟨3282884, by rfl⟩ : syracuseStep 4377179 = 6565769) B6565769
theorem B2313287 : Blo 1024605 2313287 := bstep (se 1 (by rfl) ⟨1734965, by rfl⟩ : syracuseStep 2313287 = 3469931) B3469931
theorem B1297615 : Blo 1024605 1297615 := bstep (se 1 (by rfl) ⟨973211, by rfl⟩ : syracuseStep 1297615 = 1946423) B1946423
theorem B4738283 : Blo 1024605 4738283 := bstep (se 1 (by rfl) ⟨3553712, by rfl⟩ : syracuseStep 4738283 = 7107425) B7107425
theorem B2313647 : Blo 1024605 2313647 := bstep (se 1 (by rfl) ⟨1735235, by rfl⟩ : syracuseStep 2313647 = 3470471) B3470471
theorem B3460751 : Blo 1024605 3460751 := bstep (se 1 (by rfl) ⟨2595563, by rfl⟩ : syracuseStep 3460751 = 5191127) B5191127
theorem B1462249 : Blo 1024605 1462249 := bstep (se 2 (by rfl) ⟨548343, by rfl⟩ : syracuseStep 1462249 = 1096687) B1096687
theorem B5197931 : Blo 1024605 5197931 := bstep (se 1 (by rfl) ⟨3898448, by rfl⟩ : syracuseStep 5197931 = 7796897) B7796897
theorem B5853323 : Blo 1024605 5853323 := bstep (se 1 (by rfl) ⟨4389992, by rfl⟩ : syracuseStep 5853323 = 8779985) B8779985
theorem B3952871 : Blo 1024605 3952871 := bstep (se 1 (by rfl) ⟨2964653, by rfl⟩ : syracuseStep 3952871 = 5929307) B5929307
theorem B12669779 : Blo 1024605 12669779 := bstep (se 1 (by rfl) ⟨9502334, by rfl⟩ : syracuseStep 12669779 = 19004669) B19004669
theorem B14046281 : Blo 1024605 14046281 := bstep (se 2 (by rfl) ⟨5267355, by rfl⟩ : syracuseStep 14046281 = 10534711) B10534711
theorem B3462479 : Blo 1024605 3462479 := bstep (se 1 (by rfl) ⟨2596859, by rfl⟩ : syracuseStep 3462479 = 5193719) B5193719
theorem B3463451 : Blo 1024605 3463451 := bstep (se 1 (by rfl) ⟨2597588, by rfl⟩ : syracuseStep 3463451 = 5195177) B5195177
theorem B3463775 : Blo 1024605 3463775 := bstep (se 1 (by rfl) ⟨2597831, by rfl⟩ : syracuseStep 3463775 = 5195663) B5195663
theorem B4381451 : Blo 1024605 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B3693593 : Blo 1024605 3693593 := bstep (se 2 (by rfl) ⟨1385097, by rfl⟩ : syracuseStep 3693593 = 2770195) B2770195
theorem B7789607 : Blo 1024605 7789607 := bstep (se 1 (by rfl) ⟨5842205, by rfl⟩ : syracuseStep 7789607 = 11684411) B11684411
theorem B3464423 : Blo 1024605 3464423 := bstep (se 1 (by rfl) ⟨2598317, by rfl⟩ : syracuseStep 3464423 = 5196635) B5196635
theorem B1171327 : Blo 1024605 1171327 := bstep (se 1 (by rfl) ⟨878495, by rfl⟩ : syracuseStep 1171327 = 1756991) B1756991
theorem B5201819 : Blo 1024605 5201819 := bstep (se 1 (by rfl) ⟨3901364, by rfl⟩ : syracuseStep 5201819 = 7802729) B7802729
theorem B31645889 : Blo 1024605 31645889 := bstep (se 2 (by rfl) ⟨11867208, by rfl⟩ : syracuseStep 31645889 = 23734417) B23734417
theorem B3891523 : Blo 1024605 3891523 := bstep (se 1 (by rfl) ⟨2918642, by rfl⟩ : syracuseStep 3891523 = 5837285) B5837285
theorem B15786359 : Blo 1024605 15786359 := bstep (se 1 (by rfl) ⟨11839769, by rfl⟩ : syracuseStep 15786359 = 23679539) B23679539
theorem B3465611 : Blo 1024605 3465611 := bstep (se 1 (by rfl) ⟨2599208, by rfl⟩ : syracuseStep 3465611 = 5198417) B5198417
theorem B27812555 : Blo 1024605 27812555 := bstep (se 1 (by rfl) ⟨20859416, by rfl⟩ : syracuseStep 27812555 = 41718833) B41718833
theorem B3891995 : Blo 1024605 3891995 := bstep (se 1 (by rfl) ⟨2918996, by rfl⟩ : syracuseStep 3891995 = 5837993) B5837993
theorem B4940783 : Blo 1024605 4940783 := bstep (se 1 (by rfl) ⟨3705587, by rfl⟩ : syracuseStep 4940783 = 7411175) B7411175
theorem B3892283 : Blo 1024605 3892283 := bstep (se 1 (by rfl) ⟨2919212, by rfl⟩ : syracuseStep 3892283 = 5838425) B5838425
theorem B56288459 : Blo 1024605 56288459 := bstep (se 1 (by rfl) ⟨42216344, by rfl⟩ : syracuseStep 56288459 = 84432689) B84432689
theorem B8906435 : Blo 1024605 8906435 := bstep (se 1 (by rfl) ⟨6679826, by rfl⟩ : syracuseStep 8906435 = 13359653) B13359653
theorem B3892967 : Blo 1024605 3892967 := bstep (se 1 (by rfl) ⟨2919725, by rfl⟩ : syracuseStep 3892967 = 5839451) B5839451
theorem B8775611 : Blo 1024605 8775611 := bstep (se 1 (by rfl) ⟨6581708, by rfl⟩ : syracuseStep 8775611 = 13163417) B13163417
theorem B33318863 : Blo 1024605 33318863 := bstep (se 1 (by rfl) ⟨24989147, by rfl⟩ : syracuseStep 33318863 = 49978295) B49978295
theorem B1730747 : Blo 1024605 1730747 := bstep (se 1 (by rfl) ⟨1298060, by rfl⟩ : syracuseStep 1730747 = 2596121) B2596121
theorem B2222729 : Blo 1024605 2222729 := bstep (se 2 (by rfl) ⟨833523, by rfl⟩ : syracuseStep 2222729 = 1667047) B1667047
theorem B3468257 : Blo 1024605 3468257 := bstep (se 2 (by rfl) ⟨1300596, by rfl⟩ : syracuseStep 3468257 = 2601193) B2601193
theorem B13725521 : Blo 1024605 13725521 := bstep (se 2 (by rfl) ⟨5147070, by rfl⟩ : syracuseStep 13725521 = 10294141) B10294141
theorem B35549117 : Blo 1024605 35549117 := bstep (se 3 (by rfl) ⟨6665459, by rfl⟩ : syracuseStep 35549117 = 13330919) B13330919
theorem B1732583 : Blo 1024605 1732583 := bstep (se 1 (by rfl) ⟨1299437, by rfl⟩ : syracuseStep 1732583 = 2598875) B2598875
theorem B1732603 : Blo 1024605 1732603 := bstep (se 1 (by rfl) ⟨1299452, by rfl⟩ : syracuseStep 1732603 = 2598905) B2598905
theorem B4387259 : Blo 1024605 4387259 := bstep (se 1 (by rfl) ⟨3290444, by rfl⟩ : syracuseStep 4387259 = 6580889) B6580889
theorem B3896201 : Blo 1024605 3896201 := bstep (se 2 (by rfl) ⟨1461075, by rfl⟩ : syracuseStep 3896201 = 2922151) B2922151
theorem B12481451 : Blo 1024605 12481451 := bstep (se 1 (by rfl) ⟨9361088, by rfl⟩ : syracuseStep 12481451 = 18722177) B18722177
theorem B1536959 : Blo 1024605 1536959 := bstep (se 1 (by rfl) ⟨1152719, by rfl⟩ : syracuseStep 1536959 = 2305439) B2305439
theorem B14808041 : Blo 1024605 14808041 := bstep (se 2 (by rfl) ⟨5553015, by rfl⟩ : syracuseStep 14808041 = 11106031) B11106031
theorem B1733609 : Blo 1024605 1733609 := bstep (se 2 (by rfl) ⟨650103, by rfl⟩ : syracuseStep 1733609 = 1300207) B1300207
theorem B1537007 : Blo 1024605 1537007 := bstep (se 1 (by rfl) ⟨1152755, by rfl⟩ : syracuseStep 1537007 = 2305511) B2305511
theorem B1537643 : Blo 1024605 1537643 := bstep (se 1 (by rfl) ⟨1153232, by rfl⟩ : syracuseStep 1537643 = 2306465) B2306465
theorem B19756811 : Blo 1024605 19756811 := bstep (se 1 (by rfl) ⟨14817608, by rfl⟩ : syracuseStep 19756811 = 29635217) B29635217
theorem B1734763 : Blo 1024605 1734763 := bstep (se 1 (by rfl) ⟨1301072, by rfl⟩ : syracuseStep 1734763 = 2602145) B2602145
theorem B13138199 : Blo 1024605 13138199 := bstep (se 1 (by rfl) ⟨9853649, by rfl⟩ : syracuseStep 13138199 = 19707299) B19707299
theorem B1538663 : Blo 1024605 1538663 := bstep (se 1 (by rfl) ⟨1153997, by rfl⟩ : syracuseStep 1538663 = 2307995) B2307995
theorem B14809999 : Blo 1024605 14809999 := bstep (se 1 (by rfl) ⟨11107499, by rfl⟩ : syracuseStep 14809999 = 22214999) B22214999
theorem B51412151 : Blo 1024605 51412151 := bstep (se 1 (by rfl) ⟨38559113, by rfl⟩ : syracuseStep 51412151 = 77118227) B77118227
theorem B15793375 : Blo 1024605 15793375 := bstep (se 1 (by rfl) ⟨11845031, by rfl⟩ : syracuseStep 15793375 = 23690063) B23690063
theorem B3898631 : Blo 1024605 3898631 := bstep (se 1 (by rfl) ⟨2923973, by rfl⟩ : syracuseStep 3898631 = 5847947) B5847947
theorem B3898799 : Blo 1024605 3898799 := bstep (se 1 (by rfl) ⟨2924099, by rfl⟩ : syracuseStep 3898799 = 5848199) B5848199
theorem B1539551 : Blo 1024605 1539551 := bstep (se 1 (by rfl) ⟨1154663, by rfl⟩ : syracuseStep 1539551 = 2309327) B2309327
theorem B1539611 : Blo 1024605 1539611 := bstep (se 1 (by rfl) ⟨1154708, by rfl⟩ : syracuseStep 1539611 = 2309417) B2309417
theorem B4161161 : Blo 1024605 4161161 := bstep (se 2 (by rfl) ⟨1560435, by rfl⟩ : syracuseStep 4161161 = 3120871) B3120871
theorem B1539803 : Blo 1024605 1539803 := bstep (se 1 (by rfl) ⟨1154852, by rfl⟩ : syracuseStep 1539803 = 2309705) B2309705
theorem B1540031 : Blo 1024605 1540031 := bstep (se 1 (by rfl) ⟨1155023, by rfl⟩ : syracuseStep 1540031 = 2310047) B2310047
theorem B1540859 : Blo 1024605 1540859 := bstep (se 1 (by rfl) ⟨1155644, by rfl⟩ : syracuseStep 1540859 = 2311289) B2311289
theorem B3900743 : Blo 1024605 3900743 := bstep (se 1 (by rfl) ⟨2925557, by rfl⟩ : syracuseStep 3900743 = 5851115) B5851115
theorem B1541801 : Blo 1024605 1541801 := bstep (se 2 (by rfl) ⟨578175, by rfl⟩ : syracuseStep 1541801 = 1156351) B1156351
theorem B2918119 : Blo 1024605 2918119 := bstep (se 1 (by rfl) ⟨2188589, by rfl⟩ : syracuseStep 2918119 = 4377179) B4377179
theorem B1542191 : Blo 1024605 1542191 := bstep (se 1 (by rfl) ⟨1156643, by rfl⟩ : syracuseStep 1542191 = 2313287) B2313287
theorem B1542431 : Blo 1024605 1542431 := bstep (se 1 (by rfl) ⟨1156823, by rfl⟩ : syracuseStep 1542431 = 2313647) B2313647
theorem B16648537 : Blo 1024605 16648537 := bstep (se 2 (by rfl) ⟨6243201, by rfl⟩ : syracuseStep 16648537 = 12486403) B12486403
theorem B3902215 : Blo 1024605 3902215 := bstep (se 1 (by rfl) ⟨2926661, by rfl⟩ : syracuseStep 3902215 = 5853323) B5853323
theorem B7801757 : Blo 1024605 7801757 := bstep (se 3 (by rfl) ⟨1462829, by rfl⟩ : syracuseStep 7801757 = 2925659) B2925659
theorem B9507071 : Blo 1024605 9507071 := bstep (se 1 (by rfl) ⟨7130303, by rfl⟩ : syracuseStep 9507071 = 14260607) B14260607
theorem B2920967 : Blo 1024605 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B2462395 : Blo 1024605 2462395 := bstep (se 1 (by rfl) ⟨1846796, by rfl⟩ : syracuseStep 2462395 = 3693593) B3693593
theorem B31659407 : Blo 1024605 31659407 := bstep (se 1 (by rfl) ⟨23744555, by rfl⟩ : syracuseStep 31659407 = 47489111) B47489111
theorem B10524239 : Blo 1024605 10524239 := bstep (se 1 (by rfl) ⟨7893179, by rfl⟩ : syracuseStep 10524239 = 15786359) B15786359
theorem B2594663 : Blo 1024605 2594663 := bstep (se 1 (by rfl) ⟨1945997, by rfl⟩ : syracuseStep 2594663 = 3891995) B3891995
theorem B2594855 : Blo 1024605 2594855 := bstep (se 1 (by rfl) ⟨1946141, by rfl⟩ : syracuseStep 2594855 = 3892283) B3892283
theorem B37525639 : Blo 1024605 37525639 := bstep (se 1 (by rfl) ⟨28144229, by rfl⟩ : syracuseStep 37525639 = 56288459) B56288459
theorem B5937623 : Blo 1024605 5937623 := bstep (se 1 (by rfl) ⟨4453217, by rfl⟩ : syracuseStep 5937623 = 8906435) B8906435
theorem B2595311 : Blo 1024605 2595311 := bstep (se 1 (by rfl) ⟨1946483, by rfl⟩ : syracuseStep 2595311 = 3892967) B3892967
theorem B58694153 : Blo 1024605 58694153 := bstep (se 2 (by rfl) ⟨22010307, by rfl⟩ : syracuseStep 58694153 = 44020615) B44020615
theorem B1153831 : Blo 1024605 1153831 := bstep (se 1 (by rfl) ⟨865373, by rfl⟩ : syracuseStep 1153831 = 1730747) B1730747
theorem B2497529 : Blo 1024605 2497529 := bstep (se 2 (by rfl) ⟨936573, by rfl⟩ : syracuseStep 2497529 = 1873147) B1873147
theorem B1481819 : Blo 1024605 1481819 := bstep (se 1 (by rfl) ⟨1111364, by rfl⟩ : syracuseStep 1481819 = 2222729) B2222729
theorem B44375323 : Blo 1024605 44375323 := bstep (se 1 (by rfl) ⟨33281492, by rfl⟩ : syracuseStep 44375323 = 66562985) B66562985
theorem B35528165 : Blo 1024605 35528165 := bstep (se 4 (by rfl) ⟨3330765, by rfl⟩ : syracuseStep 35528165 = 6661531) B6661531
theorem B9150347 : Blo 1024605 9150347 := bstep (se 1 (by rfl) ⟨6862760, by rfl⟩ : syracuseStep 9150347 = 13725521) B13725521
theorem B23699411 : Blo 1024605 23699411 := bstep (se 1 (by rfl) ⟨17774558, by rfl⟩ : syracuseStep 23699411 = 35549117) B35549117
theorem B1155055 : Blo 1024605 1155055 := bstep (se 1 (by rfl) ⟨866291, by rfl⟩ : syracuseStep 1155055 = 1732583) B1732583
theorem B2924839 : Blo 1024605 2924839 := bstep (se 1 (by rfl) ⟨2193629, by rfl⟩ : syracuseStep 2924839 = 4387259) B4387259
theorem B89858423 : Blo 1024605 89858423 := bstep (se 1 (by rfl) ⟨67393817, by rfl⟩ : syracuseStep 89858423 = 134787635) B134787635
theorem B2597417 : Blo 1024605 2597417 := bstep (se 2 (by rfl) ⟨974031, by rfl⟩ : syracuseStep 2597417 = 1948063) B1948063
theorem B8757841 : Blo 1024605 8757841 := bstep (se 2 (by rfl) ⟨3284190, by rfl⟩ : syracuseStep 8757841 = 6568381) B6568381
theorem B2597467 : Blo 1024605 2597467 := bstep (se 1 (by rfl) ⟨1948100, by rfl⟩ : syracuseStep 2597467 = 3896201) B3896201
theorem B1024639 : Blo 1024605 1024639 := bstep (se 1 (by rfl) ⟨768479, by rfl⟩ : syracuseStep 1024639 = 1536959) B1536959
theorem B9872027 : Blo 1024605 9872027 := bstep (se 1 (by rfl) ⟨7404020, by rfl⟩ : syracuseStep 9872027 = 14808041) B14808041
theorem B1155739 : Blo 1024605 1155739 := bstep (se 1 (by rfl) ⟨866804, by rfl⟩ : syracuseStep 1155739 = 1733609) B1733609
theorem B1024671 : Blo 1024605 1024671 := bstep (se 1 (by rfl) ⟨768503, by rfl⟩ : syracuseStep 1024671 = 1537007) B1537007
theorem B2597609 : Blo 1024605 2597609 := bstep (se 2 (by rfl) ⟨974103, by rfl⟩ : syracuseStep 2597609 = 1948207) B1948207
theorem B1025095 : Blo 1024605 1025095 := bstep (se 1 (by rfl) ⟨768821, by rfl⟩ : syracuseStep 1025095 = 1537643) B1537643
theorem B47457353 : Blo 1024605 47457353 := bstep (se 2 (by rfl) ⟨17796507, by rfl⟩ : syracuseStep 47457353 = 35593015) B35593015
theorem B8758799 : Blo 1024605 8758799 := bstep (se 1 (by rfl) ⟨6569099, by rfl⟩ : syracuseStep 8758799 = 13138199) B13138199
theorem B1025775 : Blo 1024605 1025775 := bstep (se 1 (by rfl) ⟨769331, by rfl⟩ : syracuseStep 1025775 = 1538663) B1538663
theorem B2599087 : Blo 1024605 2599087 := bstep (se 1 (by rfl) ⟨1949315, by rfl⟩ : syracuseStep 2599087 = 3898631) B3898631
theorem B2599199 : Blo 1024605 2599199 := bstep (se 1 (by rfl) ⟨1949399, by rfl⟩ : syracuseStep 2599199 = 3898799) B3898799
theorem B1026367 : Blo 1024605 1026367 := bstep (se 1 (by rfl) ⟨769775, by rfl⟩ : syracuseStep 1026367 = 1539551) B1539551
theorem B1026407 : Blo 1024605 1026407 := bstep (se 1 (by rfl) ⟨769805, by rfl⟩ : syracuseStep 1026407 = 1539611) B1539611
theorem B1026535 : Blo 1024605 1026535 := bstep (se 1 (by rfl) ⟨769901, by rfl⟩ : syracuseStep 1026535 = 1539803) B1539803
theorem B1026687 : Blo 1024605 1026687 := bstep (se 1 (by rfl) ⟨770015, by rfl⟩ : syracuseStep 1026687 = 1540031) B1540031
theorem B1026943 : Blo 1024605 1026943 := bstep (se 1 (by rfl) ⟨770207, by rfl⟩ : syracuseStep 1026943 = 1540415) B1540415
theorem B1027055 : Blo 1024605 1027055 := bstep (se 1 (by rfl) ⟨770291, by rfl⟩ : syracuseStep 1027055 = 1540583) B1540583
theorem B2468873 : Blo 1024605 2468873 := bstep (se 2 (by rfl) ⟨925827, by rfl⟩ : syracuseStep 2468873 = 1851655) B1851655
theorem B5188697 : Blo 1024605 5188697 := bstep (se 2 (by rfl) ⟨1945761, by rfl⟩ : syracuseStep 5188697 = 3891523) B3891523
theorem B66596201 : Blo 1024605 66596201 := bstep (se 2 (by rfl) ⟨24973575, by rfl⟩ : syracuseStep 66596201 = 49947151) B49947151
theorem B5189021 : Blo 1024605 5189021 := bstep (se 3 (by rfl) ⟨972941, by rfl⟩ : syracuseStep 5189021 = 1945883) B1945883
theorem B2928257 : Blo 1024605 2928257 := bstep (se 2 (by rfl) ⟨1098096, by rfl⟩ : syracuseStep 2928257 = 2196193) B2196193
theorem B2305691 : Blo 1024605 2305691 := bstep (se 1 (by rfl) ⟨1729268, by rfl⟩ : syracuseStep 2305691 = 3458537) B3458537
theorem B24981371 : Blo 1024605 24981371 := bstep (se 1 (by rfl) ⟨18736028, by rfl⟩ : syracuseStep 24981371 = 37472057) B37472057
theorem B2306303 : Blo 1024605 2306303 := bstep (se 1 (by rfl) ⟨1729727, by rfl⟩ : syracuseStep 2306303 = 3459455) B3459455
theorem B2601355 : Blo 1024605 2601355 := bstep (se 1 (by rfl) ⟨1951016, by rfl⟩ : syracuseStep 2601355 = 3902033) B3902033
theorem B2601679 : Blo 1024605 2601679 := bstep (se 1 (by rfl) ⟨1951259, by rfl⟩ : syracuseStep 2601679 = 3902519) B3902519
theorem B3158855 : Blo 1024605 3158855 := bstep (se 1 (by rfl) ⟨2369141, by rfl⟩ : syracuseStep 3158855 = 4738283) B4738283
theorem B1946567 : Blo 1024605 1946567 := bstep (se 1 (by rfl) ⟨1459925, by rfl⟩ : syracuseStep 1946567 = 2919851) B2919851
theorem B2601953 : Blo 1024605 2601953 := bstep (se 2 (by rfl) ⟨975732, by rfl⟩ : syracuseStep 2601953 = 1951465) B1951465
theorem B2307167 : Blo 1024605 2307167 := bstep (se 1 (by rfl) ⟨1730375, by rfl⟩ : syracuseStep 2307167 = 3460751) B3460751
theorem B37401983 : Blo 1024605 37401983 := bstep (se 1 (by rfl) ⟨28051487, by rfl⟩ : syracuseStep 37401983 = 56102975) B56102975
theorem B2635247 : Blo 1024605 2635247 := bstep (se 1 (by rfl) ⟨1976435, by rfl⟩ : syracuseStep 2635247 = 3952871) B3952871
theorem B2537135 : Blo 1024605 2537135 := bstep (se 1 (by rfl) ⟨1902851, by rfl⟩ : syracuseStep 2537135 = 3805703) B3805703
theorem B2308319 : Blo 1024605 2308319 := bstep (se 1 (by rfl) ⟨1731239, by rfl⟩ : syracuseStep 2308319 = 3462479) B3462479
theorem B3127855 : Blo 1024605 3127855 := bstep (se 1 (by rfl) ⟨2345891, by rfl⟩ : syracuseStep 3127855 = 4691783) B4691783
theorem B34224905 : Blo 1024605 34224905 := bstep (se 2 (by rfl) ⟨12834339, by rfl⟩ : syracuseStep 34224905 = 25668679) B25668679
theorem B2308967 : Blo 1024605 2308967 := bstep (se 1 (by rfl) ⟨1731725, by rfl⟩ : syracuseStep 2308967 = 3463451) B3463451
theorem B3292073 : Blo 1024605 3292073 := bstep (se 2 (by rfl) ⟨1234527, by rfl⟩ : syracuseStep 3292073 = 2469055) B2469055
theorem B7781345 : Blo 1024605 7781345 := bstep (se 2 (by rfl) ⟨2918004, by rfl⟩ : syracuseStep 7781345 = 5836009) B5836009
theorem B2309183 : Blo 1024605 2309183 := bstep (se 1 (by rfl) ⟨1731887, by rfl⟩ : syracuseStep 2309183 = 3463775) B3463775
theorem B5553299 : Blo 1024605 5553299 := bstep (se 1 (by rfl) ⟨4164974, by rfl⟩ : syracuseStep 5553299 = 8329949) B8329949
theorem B5193071 : Blo 1024605 5193071 := bstep (se 1 (by rfl) ⟨3894803, by rfl⟩ : syracuseStep 5193071 = 7789607) B7789607
theorem B7781831 : Blo 1024605 7781831 := bstep (se 1 (by rfl) ⟨5836373, by rfl⟩ : syracuseStep 7781831 = 11672747) B11672747
theorem B2309615 : Blo 1024605 2309615 := bstep (se 1 (by rfl) ⟨1732211, by rfl⟩ : syracuseStep 2309615 = 3464423) B3464423
theorem B1949665 : Blo 1024605 1949665 := bstep (se 2 (by rfl) ⟨731124, by rfl⟩ : syracuseStep 1949665 = 1462249) B1462249
theorem B2310137 : Blo 1024605 2310137 := bstep (se 2 (by rfl) ⟨866301, by rfl⟩ : syracuseStep 2310137 = 1732603) B1732603
theorem B2310407 : Blo 1024605 2310407 := bstep (se 1 (by rfl) ⟨1732805, by rfl⟩ : syracuseStep 2310407 = 3465611) B3465611
theorem B3293855 : Blo 1024605 3293855 := bstep (se 1 (by rfl) ⟨2470391, by rfl⟩ : syracuseStep 3293855 = 4940783) B4940783
theorem B5850407 : Blo 1024605 5850407 := bstep (se 1 (by rfl) ⟨4387805, by rfl⟩ : syracuseStep 5850407 = 8775611) B8775611
theorem B2344631 : Blo 1024605 2344631 := bstep (se 1 (by rfl) ⟨1758473, by rfl⟩ : syracuseStep 2344631 = 3516947) B3516947
theorem B2312171 : Blo 1024605 2312171 := bstep (se 1 (by rfl) ⟨1734128, by rfl⟩ : syracuseStep 2312171 = 3468257) B3468257
theorem B5556347 : Blo 1024605 5556347 := bstep (se 1 (by rfl) ⟨4167260, by rfl⟩ : syracuseStep 5556347 = 8334521) B8334521
theorem B3459401 : Blo 1024605 3459401 := bstep (se 2 (by rfl) ⟨1297275, by rfl⟩ : syracuseStep 3459401 = 2594551) B2594551
theorem B3459563 : Blo 1024605 3459563 := bstep (se 1 (by rfl) ⟨2594672, by rfl⟩ : syracuseStep 3459563 = 5189345) B5189345
theorem B2313017 : Blo 1024605 2313017 := bstep (se 2 (by rfl) ⟨867381, by rfl⟩ : syracuseStep 2313017 = 1734763) B1734763
theorem B1232543 : Blo 1024605 1232543 := bstep (se 1 (by rfl) ⟨924407, by rfl⟩ : syracuseStep 1232543 = 1848815) B1848815
theorem B19746665 : Blo 1024605 19746665 := bstep (se 2 (by rfl) ⟨7404999, by rfl⟩ : syracuseStep 19746665 = 14809999) B14809999
theorem B3461345 : Blo 1024605 3461345 := bstep (se 2 (by rfl) ⟨1298004, by rfl⟩ : syracuseStep 3461345 = 2596009) B2596009
theorem B21057833 : Blo 1024605 21057833 := bstep (se 2 (by rfl) ⟨7896687, by rfl⟩ : syracuseStep 21057833 = 15793375) B15793375
theorem B2774107 : Blo 1024605 2774107 := bstep (se 1 (by rfl) ⟨2080580, by rfl⟩ : syracuseStep 2774107 = 4161161) B4161161
theorem B1299559 : Blo 1024605 1299559 := bstep (se 1 (by rfl) ⟨974669, by rfl⟩ : syracuseStep 1299559 = 1949339) B1949339
theorem B1561769 : Blo 1024605 1561769 := bstep (se 2 (by rfl) ⟨585663, by rfl⟩ : syracuseStep 1561769 = 1171327) B1171327
theorem B9885635 : Blo 1024605 9885635 := bstep (se 1 (by rfl) ⟨7414226, by rfl⟩ : syracuseStep 9885635 = 14828453) B14828453
theorem B10541279 : Blo 1024605 10541279 := bstep (se 1 (by rfl) ⟨7905959, by rfl⟩ : syracuseStep 10541279 = 15811919) B15811919
theorem B11688785 : Blo 1024605 11688785 := bstep (se 2 (by rfl) ⟨4383294, by rfl⟩ : syracuseStep 11688785 = 8766589) B8766589
theorem B5200847 : Blo 1024605 5200847 := bstep (se 1 (by rfl) ⟨3900635, by rfl⟩ : syracuseStep 5200847 = 7801271) B7801271
theorem B3693563 : Blo 1024605 3693563 := bstep (se 1 (by rfl) ⟨2770172, by rfl⟩ : syracuseStep 3693563 = 5540345) B5540345
theorem B5856695 : Blo 1024605 5856695 := bstep (se 1 (by rfl) ⟨4392521, by rfl⟩ : syracuseStep 5856695 = 8785043) B8785043
theorem B74866751 : Blo 1024605 74866751 := bstep (se 1 (by rfl) ⟨56150063, by rfl⟩ : syracuseStep 74866751 = 112300127) B112300127
theorem B3465287 : Blo 1024605 3465287 := bstep (se 1 (by rfl) ⟨2598965, by rfl⟩ : syracuseStep 3465287 = 5197931) B5197931
theorem B3957245 : Blo 1024605 3957245 := bstep (se 3 (by rfl) ⟨741983, by rfl⟩ : syracuseStep 3957245 = 1483967) B1483967
theorem B8446519 : Blo 1024605 8446519 := bstep (se 1 (by rfl) ⟨6334889, by rfl⟩ : syracuseStep 8446519 = 12669779) B12669779
theorem B9364187 : Blo 1024605 9364187 := bstep (se 1 (by rfl) ⟨7023140, by rfl⟩ : syracuseStep 9364187 = 14046281) B14046281
theorem B5334247 : Blo 1024605 5334247 := bstep (se 1 (by rfl) ⟨4000685, by rfl⟩ : syracuseStep 5334247 = 8001371) B8001371
theorem B1730153 : Blo 1024605 1730153 := bstep (se 2 (by rfl) ⟨648807, by rfl⟩ : syracuseStep 1730153 = 1297615) B1297615
theorem B3696475 : Blo 1024605 3696475 := bstep (se 1 (by rfl) ⟨2772356, by rfl⟩ : syracuseStep 3696475 = 5544713) B5544713
theorem B3467879 : Blo 1024605 3467879 := bstep (se 1 (by rfl) ⟨2600909, by rfl⟩ : syracuseStep 3467879 = 5201819) B5201819
theorem B21097259 : Blo 1024605 21097259 := bstep (se 1 (by rfl) ⟨15822944, by rfl⟩ : syracuseStep 21097259 = 31645889) B31645889
theorem B4385825 : Blo 1024605 4385825 := bstep (se 2 (by rfl) ⟨1644684, by rfl⟩ : syracuseStep 4385825 = 3289369) B3289369
theorem B18541703 : Blo 1024605 18541703 := bstep (se 1 (by rfl) ⟨13906277, by rfl⟩ : syracuseStep 18541703 = 27812555) B27812555
theorem B3895229 : Blo 1024605 3895229 := bstep (se 3 (by rfl) ⟨730355, by rfl⟩ : syracuseStep 3895229 = 1460711) B1460711
theorem B22212575 : Blo 1024605 22212575 := bstep (se 1 (by rfl) ⟨16659431, by rfl⟩ : syracuseStep 22212575 = 33318863) B33318863
theorem B3698783 : Blo 1024605 3698783 := bstep (se 1 (by rfl) ⟨2774087, by rfl⟩ : syracuseStep 3698783 = 5548175) B5548175
theorem B1732711 : Blo 1024605 1732711 := bstep (se 1 (by rfl) ⟨1299533, by rfl⟩ : syracuseStep 1732711 = 2599067) B2599067
theorem B1733575 : Blo 1024605 1733575 := bstep (se 1 (by rfl) ⟨1300181, by rfl⟩ : syracuseStep 1733575 = 2600363) B2600363
theorem B49903559 : Blo 1024605 49903559 := bstep (se 1 (by rfl) ⟨37427669, by rfl⟩ : syracuseStep 49903559 = 74855339) B74855339
theorem B8320967 : Blo 1024605 8320967 := bstep (se 1 (by rfl) ⟨6240725, by rfl⟩ : syracuseStep 8320967 = 12481451) B12481451
theorem B1538303 : Blo 1024605 1538303 := bstep (se 1 (by rfl) ⟨1153727, by rfl⟩ : syracuseStep 1538303 = 2307455) B2307455
theorem B1735067 : Blo 1024605 1735067 := bstep (se 1 (by rfl) ⟨1301300, by rfl⟩ : syracuseStep 1735067 = 2602601) B2602601
theorem B13171207 : Blo 1024605 13171207 := bstep (se 1 (by rfl) ⟨9878405, by rfl⟩ : syracuseStep 13171207 = 19756811) B19756811
theorem B1539065 : Blo 1024605 1539065 := bstep (se 2 (by rfl) ⟨577149, by rfl⟩ : syracuseStep 1539065 = 1154299) B1154299
theorem B34274767 : Blo 1024605 34274767 := bstep (se 1 (by rfl) ⟨25706075, by rfl⟩ : syracuseStep 34274767 = 51412151) B51412151
theorem B1540271 : Blo 1024605 1540271 := bstep (se 1 (by rfl) ⟨1155203, by rfl⟩ : syracuseStep 1540271 = 2310407) B2310407
theorem B3899785 : Blo 1024605 3899785 := bstep (se 2 (by rfl) ⟨1462419, by rfl⟩ : syracuseStep 3899785 = 2924839) B2924839
theorem B2195903 : Blo 1024605 2195903 := bstep (se 1 (by rfl) ⟨1646927, by rfl⟩ : syracuseStep 2195903 = 3293855) B3293855
theorem B3900271 : Blo 1024605 3900271 := bstep (se 1 (by rfl) ⟨2925203, by rfl⟩ : syracuseStep 3900271 = 5850407) B5850407
theorem B1540985 : Blo 1024605 1540985 := bstep (se 2 (by rfl) ⟨577869, by rfl⟩ : syracuseStep 1540985 = 1155739) B1155739
theorem B1541447 : Blo 1024605 1541447 := bstep (se 1 (by rfl) ⟨1156085, by rfl⟩ : syracuseStep 1541447 = 2312171) B2312171
theorem B3704231 : Blo 1024605 3704231 := bstep (se 1 (by rfl) ⟨2778173, by rfl⟩ : syracuseStep 3704231 = 5556347) B5556347
theorem B7112329 : Blo 1024605 7112329 := bstep (se 2 (by rfl) ⟨2667123, by rfl⟩ : syracuseStep 7112329 = 5334247) B5334247
theorem B1542011 : Blo 1024605 1542011 := bstep (se 1 (by rfl) ⟨1156508, by rfl⟩ : syracuseStep 1542011 = 2313017) B2313017
theorem B24971165 : Blo 1024605 24971165 := bstep (se 3 (by rfl) ⟨4682093, by rfl⟩ : syracuseStep 24971165 = 9364187) B9364187
theorem B21106271 : Blo 1024605 21106271 := bstep (se 1 (by rfl) ⟨15829703, by rfl⟩ : syracuseStep 21106271 = 31659407) B31659407
theorem B7016159 : Blo 1024605 7016159 := bstep (se 1 (by rfl) ⟨5262119, by rfl⟩ : syracuseStep 7016159 = 10524239) B10524239
theorem B6590423 : Blo 1024605 6590423 := bstep (se 1 (by rfl) ⟨4942817, by rfl⟩ : syracuseStep 6590423 = 9885635) B9885635
theorem B2462375 : Blo 1024605 2462375 := bstep (se 1 (by rfl) ⟨1846781, by rfl⟩ : syracuseStep 2462375 = 3693563) B3693563
theorem B3904463 : Blo 1024605 3904463 := bstep (se 1 (by rfl) ⟨2928347, by rfl⟩ : syracuseStep 3904463 = 5856695) B5856695
theorem B15799607 : Blo 1024605 15799607 := bstep (se 1 (by rfl) ⟨11849705, by rfl⟩ : syracuseStep 15799607 = 23699411) B23699411
theorem B49911167 : Blo 1024605 49911167 := bstep (se 1 (by rfl) ⟨37433375, by rfl⟩ : syracuseStep 49911167 = 74866751) B74866751
theorem B3283193 : Blo 1024605 3283193 := bstep (se 2 (by rfl) ⟨1231197, by rfl⟩ : syracuseStep 3283193 = 2462395) B2462395
theorem B5839199 : Blo 1024605 5839199 := bstep (se 1 (by rfl) ⟨4379399, by rfl⟩ : syracuseStep 5839199 = 8758799) B8758799
theorem B1153435 : Blo 1024605 1153435 := bstep (se 1 (by rfl) ⟨865076, by rfl⟩ : syracuseStep 1153435 = 1730153) B1730153
theorem B14064839 : Blo 1024605 14064839 := bstep (se 1 (by rfl) ⟨10548629, by rfl⟩ : syracuseStep 14064839 = 21097259) B21097259
theorem B1645915 : Blo 1024605 1645915 := bstep (se 1 (by rfl) ⟨1234436, by rfl⟩ : syracuseStep 1645915 = 2468873) B2468873
theorem B2923883 : Blo 1024605 2923883 := bstep (se 1 (by rfl) ⟨2192912, by rfl⟩ : syracuseStep 2923883 = 4385825) B4385825
theorem B12361135 : Blo 1024605 12361135 := bstep (se 1 (by rfl) ⟨9270851, by rfl⟩ : syracuseStep 12361135 = 18541703) B18541703
theorem B16654247 : Blo 1024605 16654247 := bstep (se 1 (by rfl) ⟨12490685, by rfl⟩ : syracuseStep 16654247 = 24981371) B24981371
theorem B2596819 : Blo 1024605 2596819 := bstep (se 1 (by rfl) ⟨1947614, by rfl⟩ : syracuseStep 2596819 = 3895229) B3895229
theorem B2465855 : Blo 1024605 2465855 := bstep (se 1 (by rfl) ⟨1849391, by rfl⟩ : syracuseStep 2465855 = 3698783) B3698783
theorem B2105903 : Blo 1024605 2105903 := bstep (se 1 (by rfl) ⟨1579427, by rfl⟩ : syracuseStep 2105903 = 3158855) B3158855
theorem B4170473 : Blo 1024605 4170473 := bstep (se 2 (by rfl) ⟨1563927, by rfl⟩ : syracuseStep 4170473 = 3127855) B3127855
theorem B33269039 : Blo 1024605 33269039 := bstep (se 1 (by rfl) ⟨24951779, by rfl⟩ : syracuseStep 33269039 = 49903559) B49903559
theorem B5547311 : Blo 1024605 5547311 := bstep (se 1 (by rfl) ⟨4160483, by rfl⟩ : syracuseStep 5547311 = 8320967) B8320967
theorem B1025535 : Blo 1024605 1025535 := bstep (se 1 (by rfl) ⟨769151, by rfl⟩ : syracuseStep 1025535 = 1538303) B1538303
theorem B1156711 : Blo 1024605 1156711 := bstep (se 1 (by rfl) ⟨867533, by rfl⟩ : syracuseStep 1156711 = 1735067) B1735067
theorem B3286781 : Blo 1024605 3286781 := bstep (se 3 (by rfl) ⟨616271, by rfl⟩ : syracuseStep 3286781 = 1232543) B1232543
theorem B22816603 : Blo 1024605 22816603 := bstep (se 1 (by rfl) ⟨17112452, by rfl⟩ : syracuseStep 22816603 = 34224905) B34224905
theorem B5187563 : Blo 1024605 5187563 := bstep (se 1 (by rfl) ⟨3890672, by rfl⟩ : syracuseStep 5187563 = 7781345) B7781345
theorem B1026043 : Blo 1024605 1026043 := bstep (se 1 (by rfl) ⟨769532, by rfl⟩ : syracuseStep 1026043 = 1539065) B1539065
theorem B5187887 : Blo 1024605 5187887 := bstep (se 1 (by rfl) ⟨3890915, by rfl⟩ : syracuseStep 5187887 = 7781831) B7781831
theorem B2599553 : Blo 1024605 2599553 := bstep (se 2 (by rfl) ⟨974832, by rfl⟩ : syracuseStep 2599553 = 1949665) B1949665
theorem B1027239 : Blo 1024605 1027239 := bstep (se 1 (by rfl) ⟨770429, by rfl⟩ : syracuseStep 1027239 = 1540859) B1540859
theorem B11677121 : Blo 1024605 11677121 := bstep (se 2 (by rfl) ⟨4378920, by rfl⟩ : syracuseStep 11677121 = 8757841) B8757841
theorem B2600495 : Blo 1024605 2600495 := bstep (se 1 (by rfl) ⟨1950371, by rfl⟩ : syracuseStep 2600495 = 3900743) B3900743
theorem B1027867 : Blo 1024605 1027867 := bstep (se 1 (by rfl) ⟨770900, by rfl⟩ : syracuseStep 1027867 = 1541801) B1541801
theorem B1028127 : Blo 1024605 1028127 := bstep (se 1 (by rfl) ⟨771095, by rfl⟩ : syracuseStep 1028127 = 1542191) B1542191
theorem B1028287 : Blo 1024605 1028287 := bstep (se 1 (by rfl) ⟨771215, by rfl⟩ : syracuseStep 1028287 = 1542431) B1542431
theorem B2306267 : Blo 1024605 2306267 := bstep (se 1 (by rfl) ⟨1729700, by rfl⟩ : syracuseStep 2306267 = 3459401) B3459401
theorem B2306375 : Blo 1024605 2306375 := bstep (se 1 (by rfl) ⟨1729781, by rfl⟩ : syracuseStep 2306375 = 3459563) B3459563
theorem B4928633 : Blo 1024605 4928633 := bstep (se 2 (by rfl) ⟨1848237, by rfl⟩ : syracuseStep 4928633 = 3696475) B3696475
theorem B2307563 : Blo 1024605 2307563 := bstep (se 1 (by rfl) ⟨1730672, by rfl⟩ : syracuseStep 2307563 = 3461345) B3461345
theorem B6338047 : Blo 1024605 6338047 := bstep (se 1 (by rfl) ⟨4753535, by rfl⟩ : syracuseStep 6338047 = 9507071) B9507071
theorem B14038555 : Blo 1024605 14038555 := bstep (se 1 (by rfl) ⟨10528916, by rfl⟩ : syracuseStep 14038555 = 21057833) B21057833
theorem B1947311 : Blo 1024605 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B22198049 : Blo 1024605 22198049 := bstep (se 2 (by rfl) ⟨8324268, by rfl⟩ : syracuseStep 22198049 = 16648537) B16648537
theorem B7027519 : Blo 1024605 7027519 := bstep (se 1 (by rfl) ⟨5270639, by rfl⟩ : syracuseStep 7027519 = 10541279) B10541279
theorem B2310191 : Blo 1024605 2310191 := bstep (se 1 (by rfl) ⟨1732643, by rfl⟩ : syracuseStep 2310191 = 3465287) B3465287
theorem B2310281 : Blo 1024605 2310281 := bstep (se 2 (by rfl) ⟨866355, by rfl⟩ : syracuseStep 2310281 = 1732711) B1732711
theorem B2638163 : Blo 1024605 2638163 := bstep (se 1 (by rfl) ⟨1978622, by rfl⟩ : syracuseStep 2638163 = 3957245) B3957245
theorem B14795237 : Blo 1024605 14795237 := bstep (se 4 (by rfl) ⟨1387053, by rfl⟩ : syracuseStep 14795237 = 2774107) B2774107
theorem B31638235 : Blo 1024605 31638235 := bstep (se 1 (by rfl) ⟨23728676, by rfl⟩ : syracuseStep 31638235 = 47457353) B47457353
theorem B2311433 : Blo 1024605 2311433 := bstep (se 2 (by rfl) ⟨866787, by rfl⟩ : syracuseStep 2311433 = 1733575) B1733575
theorem B156517741 : Blo 1024605 156517741 := bstep (se 3 (by rfl) ⟨29347076, by rfl⟩ : syracuseStep 156517741 = 58694153) B58694153
theorem B2311919 : Blo 1024605 2311919 := bstep (se 1 (by rfl) ⟨1733939, by rfl⟩ : syracuseStep 2311919 = 3467879) B3467879
theorem B3459131 : Blo 1024605 3459131 := bstep (se 1 (by rfl) ⟨2594348, by rfl⟩ : syracuseStep 3459131 = 5188697) B5188697
theorem B3459347 : Blo 1024605 3459347 := bstep (se 1 (by rfl) ⟨2594510, by rfl⟩ : syracuseStep 3459347 = 5189021) B5189021
theorem B1952171 : Blo 1024605 1952171 := bstep (se 1 (by rfl) ⟨1464128, by rfl⟩ : syracuseStep 1952171 = 2928257) B2928257
theorem B3951517 : Blo 1024605 3951517 := bstep (se 3 (by rfl) ⟨740909, by rfl⟩ : syracuseStep 3951517 = 1481819) B1481819
theorem B1297711 : Blo 1024605 1297711 := bstep (se 1 (by rfl) ⟨973283, by rfl⟩ : syracuseStep 1297711 = 1946567) B1946567
theorem B1756831 : Blo 1024605 1756831 := bstep (se 1 (by rfl) ⟨1317623, by rfl⟩ : syracuseStep 1756831 = 2635247) B2635247
theorem B1691423 : Blo 1024605 1691423 := bstep (se 1 (by rfl) ⟨1268567, by rfl⟩ : syracuseStep 1691423 = 2537135) B2537135
theorem B59167097 : Blo 1024605 59167097 := bstep (se 2 (by rfl) ⟨22187661, by rfl⟩ : syracuseStep 59167097 = 44375323) B44375323
theorem B45699689 : Blo 1024605 45699689 := bstep (se 2 (by rfl) ⟨17137383, by rfl⟩ : syracuseStep 45699689 = 34274767) B34274767
theorem B3462047 : Blo 1024605 3462047 := bstep (se 1 (by rfl) ⟨2596535, by rfl⟩ : syracuseStep 3462047 = 5193071) B5193071
theorem B24400925 : Blo 1024605 24400925 := bstep (se 3 (by rfl) ⟨4575173, by rfl⟩ : syracuseStep 24400925 = 9150347) B9150347
theorem B11262025 : Blo 1024605 11262025 := bstep (se 2 (by rfl) ⟨4223259, by rfl⟩ : syracuseStep 11262025 = 8446519) B8446519
theorem B3463289 : Blo 1024605 3463289 := bstep (se 2 (by rfl) ⟨1298733, by rfl⟩ : syracuseStep 3463289 = 2597467) B2597467
theorem B239622461 : Blo 1024605 239622461 := bstep (se 3 (by rfl) ⟨44929211, by rfl⟩ : syracuseStep 239622461 = 89858423) B89858423
theorem B5201171 : Blo 1024605 5201171 := bstep (se 1 (by rfl) ⟨3900878, by rfl⟩ : syracuseStep 5201171 = 7801757) B7801757
theorem B3890825 : Blo 1024605 3890825 := bstep (se 2 (by rfl) ⟨1459059, by rfl⟩ : syracuseStep 3890825 = 2918119) B2918119
theorem B13164443 : Blo 1024605 13164443 := bstep (se 1 (by rfl) ⟨9873332, by rfl⟩ : syracuseStep 13164443 = 19746665) B19746665
theorem B3465449 : Blo 1024605 3465449 := bstep (se 2 (by rfl) ⟨1299543, by rfl⟩ : syracuseStep 3465449 = 2599087) B2599087
theorem B1041179 : Blo 1024605 1041179 := bstep (se 1 (by rfl) ⟨780884, by rfl⟩ : syracuseStep 1041179 = 1561769) B1561769
theorem B5202953 : Blo 1024605 5202953 := bstep (se 2 (by rfl) ⟨1951107, by rfl⟩ : syracuseStep 5202953 = 3902215) B3902215
theorem B1729775 : Blo 1024605 1729775 := bstep (se 1 (by rfl) ⟨1297331, by rfl⟩ : syracuseStep 1729775 = 2594663) B2594663
theorem B1729903 : Blo 1024605 1729903 := bstep (se 1 (by rfl) ⟨1297427, by rfl⟩ : syracuseStep 1729903 = 2594855) B2594855
theorem B3958415 : Blo 1024605 3958415 := bstep (se 1 (by rfl) ⟨2968811, by rfl⟩ : syracuseStep 3958415 = 5937623) B5937623
theorem B1730207 : Blo 1024605 1730207 := bstep (se 1 (by rfl) ⟨1297655, by rfl⟩ : syracuseStep 1730207 = 2595311) B2595311
theorem B6252349 : Blo 1024605 6252349 := bstep (se 3 (by rfl) ⟨1172315, by rfl⟩ : syracuseStep 6252349 = 2344631) B2344631
theorem B7792523 : Blo 1024605 7792523 := bstep (se 1 (by rfl) ⟨5844392, by rfl⟩ : syracuseStep 7792523 = 11688785) B11688785
theorem B3467231 : Blo 1024605 3467231 := bstep (se 1 (by rfl) ⟨2600423, by rfl⟩ : syracuseStep 3467231 = 5200847) B5200847
theorem B1665019 : Blo 1024605 1665019 := bstep (se 1 (by rfl) ⟨1248764, by rfl⟩ : syracuseStep 1665019 = 2497529) B2497529
theorem B23685443 : Blo 1024605 23685443 := bstep (se 1 (by rfl) ⟨17764082, by rfl⟩ : syracuseStep 23685443 = 35528165) B35528165
theorem B1731611 : Blo 1024605 1731611 := bstep (se 1 (by rfl) ⟨1298708, by rfl⟩ : syracuseStep 1731611 = 2597417) B2597417
theorem B6581351 : Blo 1024605 6581351 := bstep (se 1 (by rfl) ⟨4936013, by rfl⟩ : syracuseStep 6581351 = 9872027) B9872027
theorem B1731739 : Blo 1024605 1731739 := bstep (se 1 (by rfl) ⟨1298804, by rfl⟩ : syracuseStep 1731739 = 2597609) B2597609
theorem B3468473 : Blo 1024605 3468473 := bstep (se 2 (by rfl) ⟨1300677, by rfl⟩ : syracuseStep 3468473 = 2601355) B2601355
theorem B3468905 : Blo 1024605 3468905 := bstep (se 2 (by rfl) ⟨1300839, by rfl⟩ : syracuseStep 3468905 = 2601679) B2601679
theorem B1732745 : Blo 1024605 1732745 := bstep (se 2 (by rfl) ⟨649779, by rfl⟩ : syracuseStep 1732745 = 1299559) B1299559
theorem B1732799 : Blo 1024605 1732799 := bstep (se 1 (by rfl) ⟨1299599, by rfl⟩ : syracuseStep 1732799 = 2599199) B2599199
theorem B44397467 : Blo 1024605 44397467 := bstep (se 1 (by rfl) ⟨33298100, by rfl⟩ : syracuseStep 44397467 = 66596201) B66596201
theorem B1537127 : Blo 1024605 1537127 := bstep (se 1 (by rfl) ⟨1152845, by rfl⟩ : syracuseStep 1537127 = 2305691) B2305691
theorem B14808383 : Blo 1024605 14808383 := bstep (se 1 (by rfl) ⟨11106287, by rfl⟩ : syracuseStep 14808383 = 22212575) B22212575
theorem B1537535 : Blo 1024605 1537535 := bstep (se 1 (by rfl) ⟨1153151, by rfl⟩ : syracuseStep 1537535 = 2306303) B2306303
theorem B50034185 : Blo 1024605 50034185 := bstep (se 2 (by rfl) ⟨18762819, by rfl⟩ : syracuseStep 50034185 = 37525639) B37525639
theorem B1734635 : Blo 1024605 1734635 := bstep (se 1 (by rfl) ⟨1300976, by rfl⟩ : syracuseStep 1734635 = 2601953) B2601953
theorem B17561609 : Blo 1024605 17561609 := bstep (se 2 (by rfl) ⟨6585603, by rfl⟩ : syracuseStep 17561609 = 13171207) B13171207
theorem B1538111 : Blo 1024605 1538111 := bstep (se 1 (by rfl) ⟨1153583, by rfl⟩ : syracuseStep 1538111 = 2307167) B2307167
theorem B24934655 : Blo 1024605 24934655 := bstep (se 1 (by rfl) ⟨18700991, by rfl⟩ : syracuseStep 24934655 = 37401983) B37401983
theorem B1538441 : Blo 1024605 1538441 := bstep (se 2 (by rfl) ⟨576915, by rfl⟩ : syracuseStep 1538441 = 1153831) B1153831
theorem B1538879 : Blo 1024605 1538879 := bstep (se 1 (by rfl) ⟨1154159, by rfl⟩ : syracuseStep 1538879 = 2308319) B2308319
theorem B1539311 : Blo 1024605 1539311 := bstep (se 1 (by rfl) ⟨1154483, by rfl⟩ : syracuseStep 1539311 = 2308967) B2308967
theorem B2194715 : Blo 1024605 2194715 := bstep (se 1 (by rfl) ⟨1646036, by rfl⟩ : syracuseStep 2194715 = 3292073) B3292073
theorem B1539455 : Blo 1024605 1539455 := bstep (se 1 (by rfl) ⟨1154591, by rfl⟩ : syracuseStep 1539455 = 2309183) B2309183
theorem B3702199 : Blo 1024605 3702199 := bstep (se 1 (by rfl) ⟨2776649, by rfl⟩ : syracuseStep 3702199 = 5553299) B5553299
theorem B1539743 : Blo 1024605 1539743 := bstep (se 1 (by rfl) ⟨1154807, by rfl⟩ : syracuseStep 1539743 = 2309615) B2309615
theorem B1540073 : Blo 1024605 1540073 := bstep (se 2 (by rfl) ⟨577527, by rfl⟩ : syracuseStep 1540073 = 1155055) B1155055
theorem B1540091 : Blo 1024605 1540091 := bstep (se 1 (by rfl) ⟨1155068, by rfl⟩ : syracuseStep 1540091 = 2310137) B2310137
theorem B1540127 : Blo 1024605 1540127 := bstep (se 1 (by rfl) ⟨1155095, by rfl⟩ : syracuseStep 1540127 = 2310191) B2310191
theorem B1540187 : Blo 1024605 1540187 := bstep (se 1 (by rfl) ⟨1155140, by rfl⟩ : syracuseStep 1540187 = 2310281) B2310281
theorem B9863491 : Blo 1024605 9863491 := bstep (se 1 (by rfl) ⟨7397618, by rfl⟩ : syracuseStep 9863491 = 14795237) B14795237
theorem B1540955 : Blo 1024605 1540955 := bstep (se 1 (by rfl) ⟨1155716, by rfl⟩ : syracuseStep 1540955 = 2311433) B2311433
theorem B1541279 : Blo 1024605 1541279 := bstep (se 1 (by rfl) ⟨1155959, by rfl⟩ : syracuseStep 1541279 = 2311919) B2311919
theorem B16647443 : Blo 1024605 16647443 := bstep (se 1 (by rfl) ⟨12485582, by rfl⟩ : syracuseStep 16647443 = 24971165) B24971165
theorem B1542281 : Blo 1024605 1542281 := bstep (se 2 (by rfl) ⟨578355, by rfl⟩ : syracuseStep 1542281 = 1156711) B1156711
theorem B4393615 : Blo 1024605 4393615 := bstep (se 1 (by rfl) ⟨3295211, by rfl⟩ : syracuseStep 4393615 = 6590423) B6590423
theorem B1641583 : Blo 1024605 1641583 := bstep (se 1 (by rfl) ⟨1231187, by rfl⟩ : syracuseStep 1641583 = 2462375) B2462375
theorem B159748307 : Blo 1024605 159748307 := bstep (se 1 (by rfl) ⟨119811230, by rfl⟩ : syracuseStep 159748307 = 239622461) B239622461
theorem B9376559 : Blo 1024605 9376559 := bstep (se 1 (by rfl) ⟨7032419, by rfl⟩ : syracuseStep 9376559 = 14064839) B14064839
theorem B2593883 : Blo 1024605 2593883 := bstep (se 1 (by rfl) ⟨1945412, by rfl⟩ : syracuseStep 2593883 = 3890825) B3890825
theorem B1643903 : Blo 1024605 1643903 := bstep (se 1 (by rfl) ⟨1232927, by rfl⟩ : syracuseStep 1643903 = 2465855) B2465855
theorem B1153183 : Blo 1024605 1153183 := bstep (se 1 (by rfl) ⟨864887, by rfl⟩ : syracuseStep 1153183 = 1729775) B1729775
theorem B1153471 : Blo 1024605 1153471 := bstep (se 1 (by rfl) ⟨865103, by rfl⟩ : syracuseStep 1153471 = 1730207) B1730207
theorem B1154407 : Blo 1024605 1154407 := bstep (se 1 (by rfl) ⟨865805, by rfl⟩ : syracuseStep 1154407 = 1731611) B1731611
theorem B18718073 : Blo 1024605 18718073 := bstep (se 2 (by rfl) ⟨7019277, by rfl⟩ : syracuseStep 18718073 = 14038555) B14038555
theorem B1155163 : Blo 1024605 1155163 := bstep (se 1 (by rfl) ⟨866372, by rfl⟩ : syracuseStep 1155163 = 1732745) B1732745
theorem B15016033 : Blo 1024605 15016033 := bstep (se 2 (by rfl) ⟨5631012, by rfl⟩ : syracuseStep 15016033 = 11262025) B11262025
theorem B1155199 : Blo 1024605 1155199 := bstep (se 1 (by rfl) ⟨866399, by rfl⟩ : syracuseStep 1155199 = 1732799) B1732799
theorem B29598311 : Blo 1024605 29598311 := bstep (se 1 (by rfl) ⟨22198733, by rfl⟩ : syracuseStep 29598311 = 44397467) B44397467
theorem B1024751 : Blo 1024605 1024751 := bstep (se 1 (by rfl) ⟨768563, by rfl⟩ : syracuseStep 1024751 = 1537127) B1537127
theorem B3285755 : Blo 1024605 3285755 := bstep (se 1 (by rfl) ⟨2464316, by rfl⟩ : syracuseStep 3285755 = 4928633) B4928633
theorem B9872255 : Blo 1024605 9872255 := bstep (se 1 (by rfl) ⟨7404191, by rfl⟩ : syracuseStep 9872255 = 14808383) B14808383
theorem B1025023 : Blo 1024605 1025023 := bstep (se 1 (by rfl) ⟨768767, by rfl⟩ : syracuseStep 1025023 = 1537535) B1537535
theorem B1156423 : Blo 1024605 1156423 := bstep (se 1 (by rfl) ⟨867317, by rfl⟩ : syracuseStep 1156423 = 1734635) B1734635
theorem B11707739 : Blo 1024605 11707739 := bstep (se 1 (by rfl) ⟨8780804, by rfl⟩ : syracuseStep 11707739 = 17561609) B17561609
theorem B1025407 : Blo 1024605 1025407 := bstep (se 1 (by rfl) ⟨769055, by rfl⟩ : syracuseStep 1025407 = 1538111) B1538111
theorem B16623103 : Blo 1024605 16623103 := bstep (se 1 (by rfl) ⟨12467327, by rfl⟩ : syracuseStep 16623103 = 24934655) B24934655
theorem B1025627 : Blo 1024605 1025627 := bstep (se 1 (by rfl) ⟨769220, by rfl⟩ : syracuseStep 1025627 = 1538441) B1538441
theorem B1025919 : Blo 1024605 1025919 := bstep (se 1 (by rfl) ⟨769439, by rfl⟩ : syracuseStep 1025919 = 1538879) B1538879
theorem B1026207 : Blo 1024605 1026207 := bstep (se 1 (by rfl) ⟨769655, by rfl⟩ : syracuseStep 1026207 = 1539311) B1539311
theorem B1026303 : Blo 1024605 1026303 := bstep (se 1 (by rfl) ⟨769727, by rfl⟩ : syracuseStep 1026303 = 1539455) B1539455
theorem B1026495 : Blo 1024605 1026495 := bstep (se 1 (by rfl) ⟨769871, by rfl⟩ : syracuseStep 1026495 = 1539743) B1539743
theorem B1026715 : Blo 1024605 1026715 := bstep (se 1 (by rfl) ⟨770036, by rfl⟩ : syracuseStep 1026715 = 1540073) B1540073
theorem B1026727 : Blo 1024605 1026727 := bstep (se 1 (by rfl) ⟨770045, by rfl⟩ : syracuseStep 1026727 = 1540091) B1540091
theorem B1026847 : Blo 1024605 1026847 := bstep (se 1 (by rfl) ⟨770135, by rfl⟩ : syracuseStep 1026847 = 1540271) B1540271
theorem B1027323 : Blo 1024605 1027323 := bstep (se 1 (by rfl) ⟨770492, by rfl⟩ : syracuseStep 1027323 = 1540985) B1540985
theorem B1027631 : Blo 1024605 1027631 := bstep (se 1 (by rfl) ⟨770723, by rfl⟩ : syracuseStep 1027631 = 1541447) B1541447
theorem B42184313 : Blo 1024605 42184313 := bstep (se 2 (by rfl) ⟨15819117, by rfl⟩ : syracuseStep 42184313 = 31638235) B31638235
theorem B1028007 : Blo 1024605 1028007 := bstep (se 1 (by rfl) ⟨771005, by rfl⟩ : syracuseStep 1028007 = 1542011) B1542011
theorem B2306087 : Blo 1024605 2306087 := bstep (se 1 (by rfl) ⟨1729565, by rfl⟩ : syracuseStep 2306087 = 3459131) B3459131
theorem B2306231 : Blo 1024605 2306231 := bstep (se 1 (by rfl) ⟨1729673, by rfl⟩ : syracuseStep 2306231 = 3459347) B3459347
theorem B2306537 : Blo 1024605 2306537 := bstep (se 2 (by rfl) ⟨864951, by rfl⟩ : syracuseStep 2306537 = 1729903) B1729903
theorem B14070847 : Blo 1024605 14070847 := bstep (se 1 (by rfl) ⟨10553135, by rfl⟩ : syracuseStep 14070847 = 21106271) B21106271
theorem B8336465 : Blo 1024605 8336465 := bstep (se 2 (by rfl) ⟨3126174, by rfl⟩ : syracuseStep 8336465 = 6252349) B6252349
theorem B30422137 : Blo 1024605 30422137 := bstep (se 2 (by rfl) ⟨11408301, by rfl⟩ : syracuseStep 30422137 = 22816603) B22816603
theorem B1127615 : Blo 1024605 1127615 := bstep (se 1 (by rfl) ⟨845711, by rfl⟩ : syracuseStep 1127615 = 1691423) B1691423
theorem B2308031 : Blo 1024605 2308031 := bstep (se 1 (by rfl) ⟨1731023, by rfl⟩ : syracuseStep 2308031 = 3462047) B3462047
theorem B2602975 : Blo 1024605 2602975 := bstep (se 1 (by rfl) ⟨1952231, by rfl⟩ : syracuseStep 2602975 = 3904463) B3904463
theorem B16267283 : Blo 1024605 16267283 := bstep (se 1 (by rfl) ⟨12200462, by rfl⟩ : syracuseStep 16267283 = 24400925) B24400925
theorem B10533071 : Blo 1024605 10533071 := bstep (se 1 (by rfl) ⟨7899803, by rfl⟩ : syracuseStep 10533071 = 15799607) B15799607
theorem B33274111 : Blo 1024605 33274111 := bstep (se 1 (by rfl) ⟨24955583, by rfl⟩ : syracuseStep 33274111 = 49911167) B49911167
theorem B9877949 : Blo 1024605 9877949 := bstep (se 3 (by rfl) ⟨1852115, by rfl⟩ : syracuseStep 9877949 = 3704231) B3704231
theorem B2308859 : Blo 1024605 2308859 := bstep (se 1 (by rfl) ⟨1731644, by rfl⟩ : syracuseStep 2308859 = 3463289) B3463289
theorem B2308985 : Blo 1024605 2308985 := bstep (se 2 (by rfl) ⟨865869, by rfl⟩ : syracuseStep 2308985 = 1731739) B1731739
theorem B2342441 : Blo 1024605 2342441 := bstep (se 2 (by rfl) ⟨878415, by rfl⟩ : syracuseStep 2342441 = 1756831) B1756831
theorem B1949255 : Blo 1024605 1949255 := bstep (se 1 (by rfl) ⟨1461941, by rfl⟩ : syracuseStep 1949255 = 2923883) B2923883
theorem B2310299 : Blo 1024605 2310299 := bstep (se 1 (by rfl) ⟨1732724, by rfl⟩ : syracuseStep 2310299 = 3465449) B3465449
theorem B2638943 : Blo 1024605 2638943 := bstep (se 1 (by rfl) ⟨1979207, by rfl⟩ : syracuseStep 2638943 = 3958415) B3958415
theorem B5195015 : Blo 1024605 5195015 := bstep (se 1 (by rfl) ⟨3896261, by rfl⟩ : syracuseStep 5195015 = 7792523) B7792523
theorem B2311487 : Blo 1024605 2311487 := bstep (se 1 (by rfl) ⟨1733615, by rfl⟩ : syracuseStep 2311487 = 3467231) B3467231
theorem B3458375 : Blo 1024605 3458375 := bstep (se 1 (by rfl) ⟨2593781, by rfl⟩ : syracuseStep 3458375 = 5187563) B5187563
theorem B3458591 : Blo 1024605 3458591 := bstep (se 1 (by rfl) ⟨2593943, by rfl⟩ : syracuseStep 3458591 = 5187887) B5187887
theorem B2312315 : Blo 1024605 2312315 := bstep (se 1 (by rfl) ⟨1734236, by rfl⟩ : syracuseStep 2312315 = 3468473) B3468473
theorem B7784747 : Blo 1024605 7784747 := bstep (se 1 (by rfl) ⟨5838560, by rfl⟩ : syracuseStep 7784747 = 11677121) B11677121
theorem B2312603 : Blo 1024605 2312603 := bstep (se 1 (by rfl) ⟨1734452, by rfl⟩ : syracuseStep 2312603 = 3468905) B3468905
theorem B37932421 : Blo 1024605 37932421 := bstep (se 4 (by rfl) ⟨3556164, by rfl⟩ : syracuseStep 37932421 = 7112329) B7112329
theorem B5852573 : Blo 1024605 5852573 := bstep (se 3 (by rfl) ⟨1097357, by rfl⟩ : syracuseStep 5852573 = 2194715) B2194715
theorem B1298207 : Blo 1024605 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B14798699 : Blo 1024605 14798699 := bstep (se 1 (by rfl) ⟨11099024, by rfl⟩ : syracuseStep 14798699 = 22198049) B22198049
theorem B4936265 : Blo 1024605 4936265 := bstep (se 2 (by rfl) ⟨1851099, by rfl⟩ : syracuseStep 4936265 = 3702199) B3702199
theorem B3462425 : Blo 1024605 3462425 := bstep (se 2 (by rfl) ⟨1298409, by rfl⟩ : syracuseStep 3462425 = 2596819) B2596819
theorem B1758775 : Blo 1024605 1758775 := bstep (se 1 (by rfl) ⟨1319081, by rfl⟩ : syracuseStep 1758775 = 2638163) B2638163
theorem B1463935 : Blo 1024605 1463935 := bstep (se 1 (by rfl) ⟨1097951, by rfl⟩ : syracuseStep 1463935 = 2195903) B2195903
theorem B5199713 : Blo 1024605 5199713 := bstep (se 2 (by rfl) ⟨1949892, by rfl⟩ : syracuseStep 5199713 = 3899785) B3899785
theorem B5200361 : Blo 1024605 5200361 := bstep (se 2 (by rfl) ⟨1950135, by rfl⟩ : syracuseStep 5200361 = 3900271) B3900271
theorem B1301447 : Blo 1024605 1301447 := bstep (se 1 (by rfl) ⟨976085, by rfl⟩ : syracuseStep 1301447 = 1952171) B1952171
theorem B208690321 : Blo 1024605 208690321 := bstep (se 2 (by rfl) ⟨78258870, by rfl⟩ : syracuseStep 208690321 = 156517741) B156517741
theorem B2776477 : Blo 1024605 2776477 := bstep (se 3 (by rfl) ⟨520589, by rfl⟩ : syracuseStep 2776477 = 1041179) B1041179
theorem B4677439 : Blo 1024605 4677439 := bstep (se 1 (by rfl) ⟨3508079, by rfl⟩ : syracuseStep 4677439 = 7016159) B7016159
theorem B2220025 : Blo 1024605 2220025 := bstep (se 2 (by rfl) ⟨832509, by rfl⟩ : syracuseStep 2220025 = 1665019) B1665019
theorem B39444731 : Blo 1024605 39444731 := bstep (se 1 (by rfl) ⟨29583548, by rfl⟩ : syracuseStep 39444731 = 59167097) B59167097
theorem B30466459 : Blo 1024605 30466459 := bstep (se 1 (by rfl) ⟨22849844, by rfl⟩ : syracuseStep 30466459 = 45699689) B45699689
theorem B5268689 : Blo 1024605 5268689 := bstep (se 2 (by rfl) ⟨1975758, by rfl⟩ : syracuseStep 5268689 = 3951517) B3951517
theorem B2188795 : Blo 1024605 2188795 := bstep (se 1 (by rfl) ⟨1641596, by rfl⟩ : syracuseStep 2188795 = 3283193) B3283193
theorem B3892799 : Blo 1024605 3892799 := bstep (se 1 (by rfl) ⟨2919599, by rfl⟩ : syracuseStep 3892799 = 5839199) B5839199
theorem B1730281 : Blo 1024605 1730281 := bstep (se 2 (by rfl) ⟨648855, by rfl⟩ : syracuseStep 1730281 = 1297711) B1297711
theorem B3467447 : Blo 1024605 3467447 := bstep (se 1 (by rfl) ⟨2600585, by rfl⟩ : syracuseStep 3467447 = 5201171) B5201171
theorem B8776295 : Blo 1024605 8776295 := bstep (se 1 (by rfl) ⟨6582221, by rfl⟩ : syracuseStep 8776295 = 13164443) B13164443
theorem B11102831 : Blo 1024605 11102831 := bstep (se 1 (by rfl) ⟨8327123, by rfl⟩ : syracuseStep 11102831 = 16654247) B16654247
theorem B1403935 : Blo 1024605 1403935 := bstep (se 1 (by rfl) ⟨1052951, by rfl⟩ : syracuseStep 1403935 = 2105903) B2105903
theorem B2780315 : Blo 1024605 2780315 := bstep (se 1 (by rfl) ⟨2085236, by rfl⟩ : syracuseStep 2780315 = 4170473) B4170473
theorem B3468635 : Blo 1024605 3468635 := bstep (se 1 (by rfl) ⟨2601476, by rfl⟩ : syracuseStep 3468635 = 5202953) B5202953
theorem B22179359 : Blo 1024605 22179359 := bstep (se 1 (by rfl) ⟨16634519, by rfl⟩ : syracuseStep 22179359 = 33269039) B33269039
theorem B3698207 : Blo 1024605 3698207 := bstep (se 1 (by rfl) ⟨2773655, by rfl⟩ : syracuseStep 3698207 = 5547311) B5547311
theorem B2191187 : Blo 1024605 2191187 := bstep (se 1 (by rfl) ⟨1643390, by rfl⟩ : syracuseStep 2191187 = 3286781) B3286781
theorem B15790295 : Blo 1024605 15790295 := bstep (se 1 (by rfl) ⟨11842721, by rfl⟩ : syracuseStep 15790295 = 23685443) B23685443
theorem B1733035 : Blo 1024605 1733035 := bstep (se 1 (by rfl) ⟨1299776, by rfl⟩ : syracuseStep 1733035 = 2599553) B2599553
theorem B8450729 : Blo 1024605 8450729 := bstep (se 2 (by rfl) ⟨3169023, by rfl⟩ : syracuseStep 8450729 = 6338047) B6338047
theorem B4387567 : Blo 1024605 4387567 := bstep (se 1 (by rfl) ⟨3290675, by rfl⟩ : syracuseStep 4387567 = 6581351) B6581351
theorem B1733663 : Blo 1024605 1733663 := bstep (se 1 (by rfl) ⟨1300247, by rfl⟩ : syracuseStep 1733663 = 2600495) B2600495
theorem B1537511 : Blo 1024605 1537511 := bstep (se 1 (by rfl) ⟨1153133, by rfl⟩ : syracuseStep 1537511 = 2306267) B2306267
theorem B1537583 : Blo 1024605 1537583 := bstep (se 1 (by rfl) ⟨1153187, by rfl⟩ : syracuseStep 1537583 = 2306375) B2306375
theorem B1537913 : Blo 1024605 1537913 := bstep (se 2 (by rfl) ⟨576717, by rfl⟩ : syracuseStep 1537913 = 1153435) B1153435
theorem B1538375 : Blo 1024605 1538375 := bstep (se 1 (by rfl) ⟨1153781, by rfl⟩ : syracuseStep 1538375 = 2307563) B2307563
theorem B33356123 : Blo 1024605 33356123 := bstep (se 1 (by rfl) ⟨25017092, by rfl⟩ : syracuseStep 33356123 = 50034185) B50034185
theorem B9370025 : Blo 1024605 9370025 := bstep (se 2 (by rfl) ⟨3513759, by rfl⟩ : syracuseStep 9370025 = 7027519) B7027519
theorem B2194553 : Blo 1024605 2194553 := bstep (se 2 (by rfl) ⟨822957, by rfl⟩ : syracuseStep 2194553 = 1645915) B1645915
theorem B16481513 : Blo 1024605 16481513 := bstep (se 2 (by rfl) ⟨6180567, by rfl⟩ : syracuseStep 16481513 = 12361135) B12361135
theorem B1540199 : Blo 1024605 1540199 := bstep (se 1 (by rfl) ⟨1155149, by rfl⟩ : syracuseStep 1540199 = 2310299) B2310299
theorem B1540217 : Blo 1024605 1540217 := bstep (se 2 (by rfl) ⟨577581, by rfl⟩ : syracuseStep 1540217 = 1155163) B1155163
theorem B20021377 : Blo 1024605 20021377 := bstep (se 2 (by rfl) ⟨7508016, by rfl⟩ : syracuseStep 20021377 = 15016033) B15016033
theorem B1540265 : Blo 1024605 1540265 := bstep (se 2 (by rfl) ⟨577599, by rfl⟩ : syracuseStep 1540265 = 1155199) B1155199
theorem B1540991 : Blo 1024605 1540991 := bstep (se 1 (by rfl) ⟨1155743, by rfl⟩ : syracuseStep 1540991 = 2311487) B2311487
theorem B1541543 : Blo 1024605 1541543 := bstep (se 1 (by rfl) ⟨1156157, by rfl⟩ : syracuseStep 1541543 = 2312315) B2312315
theorem B1541735 : Blo 1024605 1541735 := bstep (se 1 (by rfl) ⟨1156301, by rfl⟩ : syracuseStep 1541735 = 2312603) B2312603
theorem B1541897 : Blo 1024605 1541897 := bstep (se 2 (by rfl) ⟨578211, by rfl⟩ : syracuseStep 1541897 = 1156423) B1156423
theorem B2918393 : Blo 1024605 2918393 := bstep (se 2 (by rfl) ⟨1094397, by rfl⟩ : syracuseStep 2918393 = 2188795) B2188795
theorem B3901715 : Blo 1024605 3901715 := bstep (se 1 (by rfl) ⟨2926286, by rfl⟩ : syracuseStep 3901715 = 5852573) B5852573
theorem B9865799 : Blo 1024605 9865799 := bstep (se 1 (by rfl) ⟨7399349, by rfl⟩ : syracuseStep 9865799 = 14798699) B14798699
theorem B106498871 : Blo 1024605 106498871 := bstep (se 1 (by rfl) ⟨79874153, by rfl⟩ : syracuseStep 106498871 = 159748307) B159748307
theorem B4452060181 : Blo 1024605 4452060181 := bstep (se 6 (by rfl) ⟨104345160, by rfl⟩ : syracuseStep 4452060181 = 208690321) B208690321
theorem B19732207 : Blo 1024605 19732207 := bstep (se 1 (by rfl) ⟨14799155, by rfl⟩ : syracuseStep 19732207 = 29598311) B29598311
theorem B3512459 : Blo 1024605 3512459 := bstep (se 1 (by rfl) ⟨2634344, by rfl⟩ : syracuseStep 3512459 = 5268689) B5268689
theorem B7805159 : Blo 1024605 7805159 := bstep (se 1 (by rfl) ⟨5853869, by rfl⟩ : syracuseStep 7805159 = 11707739) B11707739
theorem B2595199 : Blo 1024605 2595199 := bstep (se 1 (by rfl) ⟨1946399, by rfl⟩ : syracuseStep 2595199 = 3892799) B3892799
theorem B14786239 : Blo 1024605 14786239 := bstep (se 1 (by rfl) ⟨11089679, by rfl⟩ : syracuseStep 14786239 = 22179359) B22179359
theorem B2465471 : Blo 1024605 2465471 := bstep (se 1 (by rfl) ⟨1849103, by rfl⟩ : syracuseStep 2465471 = 3698207) B3698207
theorem B28122875 : Blo 1024605 28122875 := bstep (se 1 (by rfl) ⟨21092156, by rfl⟩ : syracuseStep 28122875 = 42184313) B42184313
theorem B10526863 : Blo 1024605 10526863 := bstep (se 1 (by rfl) ⟨7895147, by rfl⟩ : syracuseStep 10526863 = 15790295) B15790295
theorem B43950701 : Blo 1024605 43950701 := bstep (se 3 (by rfl) ⟨8240756, by rfl⟩ : syracuseStep 43950701 = 16481513) B16481513
theorem B1155775 : Blo 1024605 1155775 := bstep (se 1 (by rfl) ⟨866831, by rfl⟩ : syracuseStep 1155775 = 1733663) B1733663
theorem B1025007 : Blo 1024605 1025007 := bstep (se 1 (by rfl) ⟨768755, by rfl⟩ : syracuseStep 1025007 = 1537511) B1537511
theorem B1025055 : Blo 1024605 1025055 := bstep (se 1 (by rfl) ⟨768791, by rfl⟩ : syracuseStep 1025055 = 1537583) B1537583
theorem B1025275 : Blo 1024605 1025275 := bstep (se 1 (by rfl) ⟨768956, by rfl⟩ : syracuseStep 1025275 = 1537913) B1537913
theorem B7022047 : Blo 1024605 7022047 := bstep (se 1 (by rfl) ⟨5266535, by rfl⟩ : syracuseStep 7022047 = 10533071) B10533071
theorem B1025583 : Blo 1024605 1025583 := bstep (se 1 (by rfl) ⟨769187, by rfl⟩ : syracuseStep 1025583 = 1538375) B1538375
theorem B6236585 : Blo 1024605 6236585 := bstep (se 2 (by rfl) ⟨2338719, by rfl⟩ : syracuseStep 6236585 = 4677439) B4677439
theorem B2960033 : Blo 1024605 2960033 := bstep (se 2 (by rfl) ⟨1110012, by rfl⟩ : syracuseStep 2960033 = 2220025) B2220025
theorem B1026751 : Blo 1024605 1026751 := bstep (se 1 (by rfl) ⟨770063, by rfl⟩ : syracuseStep 1026751 = 1540127) B1540127
theorem B1026791 : Blo 1024605 1026791 := bstep (se 1 (by rfl) ⟨770093, by rfl⟩ : syracuseStep 1026791 = 1540187) B1540187
theorem B13151321 : Blo 1024605 13151321 := bstep (se 2 (by rfl) ⟨4931745, by rfl⟩ : syracuseStep 13151321 = 9863491) B9863491
theorem B1027303 : Blo 1024605 1027303 := bstep (se 1 (by rfl) ⟨770477, by rfl⟩ : syracuseStep 1027303 = 1540955) B1540955
theorem B1027519 : Blo 1024605 1027519 := bstep (se 1 (by rfl) ⟨770639, by rfl⟩ : syracuseStep 1027519 = 1541279) B1541279
theorem B2305583 : Blo 1024605 2305583 := bstep (se 1 (by rfl) ⟨1729187, by rfl⟩ : syracuseStep 2305583 = 3458375) B3458375
theorem B2305727 : Blo 1024605 2305727 := bstep (se 1 (by rfl) ⟨1729295, by rfl⟩ : syracuseStep 2305727 = 3458591) B3458591
theorem B1028187 : Blo 1024605 1028187 := bstep (se 1 (by rfl) ⟨771140, by rfl⟩ : syracuseStep 1028187 = 1542281) B1542281
theorem B5189831 : Blo 1024605 5189831 := bstep (se 1 (by rfl) ⟨3892373, by rfl⟩ : syracuseStep 5189831 = 7784747) B7784747
theorem B22164137 : Blo 1024605 22164137 := bstep (se 2 (by rfl) ⟨8311551, by rfl⟩ : syracuseStep 22164137 = 16623103) B16623103
theorem B2307041 : Blo 1024605 2307041 := bstep (se 2 (by rfl) ⟨865140, by rfl⟩ : syracuseStep 2307041 = 1730281) B1730281
theorem B3290843 : Blo 1024605 3290843 := bstep (se 1 (by rfl) ⟨2468132, by rfl⟩ : syracuseStep 3290843 = 4936265) B4936265
theorem B2308283 : Blo 1024605 2308283 := bstep (se 1 (by rfl) ⟨1731212, by rfl⟩ : syracuseStep 2308283 = 3462425) B3462425
theorem B1095935 : Blo 1024605 1095935 := bstep (se 1 (by rfl) ⟨821951, by rfl⟩ : syracuseStep 1095935 = 1643903) B1643903
theorem B50576561 : Blo 1024605 50576561 := bstep (se 2 (by rfl) ⟨18966210, by rfl⟩ : syracuseStep 50576561 = 37932421) B37932421
theorem B7487653 : Blo 1024605 7487653 := bstep (se 4 (by rfl) ⟨701967, by rfl⟩ : syracuseStep 7487653 = 1403935) B1403935
theorem B26296487 : Blo 1024605 26296487 := bstep (se 1 (by rfl) ⟨19722365, by rfl⟩ : syracuseStep 26296487 = 39444731) B39444731
theorem B2310713 : Blo 1024605 2310713 := bstep (se 2 (by rfl) ⟨866517, by rfl⟩ : syracuseStep 2310713 = 1733035) B1733035
theorem B5850089 : Blo 1024605 5850089 := bstep (se 2 (by rfl) ⟨2193783, by rfl⟩ : syracuseStep 5850089 = 4387567) B4387567
theorem B18761129 : Blo 1024605 18761129 := bstep (se 2 (by rfl) ⟨7035423, by rfl⟩ : syracuseStep 18761129 = 14070847) B14070847
theorem B2311631 : Blo 1024605 2311631 := bstep (se 1 (by rfl) ⟨1733723, by rfl⟩ : syracuseStep 2311631 = 3467447) B3467447
theorem B5850863 : Blo 1024605 5850863 := bstep (se 1 (by rfl) ⟨4388147, by rfl⟩ : syracuseStep 5850863 = 8776295) B8776295
theorem B2345033 : Blo 1024605 2345033 := bstep (se 2 (by rfl) ⟨879387, by rfl⟩ : syracuseStep 2345033 = 1758775) B1758775
theorem B1853543 : Blo 1024605 1853543 := bstep (se 1 (by rfl) ⟨1390157, by rfl⟩ : syracuseStep 1853543 = 2780315) B2780315
theorem B1951913 : Blo 1024605 1951913 := bstep (se 2 (by rfl) ⟨731967, by rfl⟩ : syracuseStep 1951913 = 1463935) B1463935
theorem B2312423 : Blo 1024605 2312423 := bstep (se 1 (by rfl) ⟨1734317, by rfl⟩ : syracuseStep 2312423 = 3468635) B3468635
theorem B1460791 : Blo 1024605 1460791 := bstep (se 1 (by rfl) ⟨1095593, by rfl⟩ : syracuseStep 1460791 = 2191187) B2191187
theorem B5557643 : Blo 1024605 5557643 := bstep (se 1 (by rfl) ⟨4168232, by rfl⟩ : syracuseStep 5557643 = 8336465) B8336465
theorem B22237415 : Blo 1024605 22237415 := bstep (se 1 (by rfl) ⟨16678061, by rfl⟩ : syracuseStep 22237415 = 33356123) B33356123
theorem B6246683 : Blo 1024605 6246683 := bstep (se 1 (by rfl) ⟨4685012, by rfl⟩ : syracuseStep 6246683 = 9370025) B9370025
theorem B1463035 : Blo 1024605 1463035 := bstep (se 1 (by rfl) ⟨1097276, by rfl⟩ : syracuseStep 1463035 = 2194553) B2194553
theorem B3461885 : Blo 1024605 3461885 := bstep (se 3 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 3461885 = 1298207) B1298207
theorem B1561627 : Blo 1024605 1561627 := bstep (se 1 (by rfl) ⟨1171220, by rfl⟩ : syracuseStep 1561627 = 2342441) B2342441
theorem B1299503 : Blo 1024605 1299503 := bstep (se 1 (by rfl) ⟨974627, by rfl⟩ : syracuseStep 1299503 = 1949255) B1949255
theorem B1759295 : Blo 1024605 1759295 := bstep (se 1 (by rfl) ⟨1319471, by rfl⟩ : syracuseStep 1759295 = 2638943) B2638943
theorem B3463343 : Blo 1024605 3463343 := bstep (se 1 (by rfl) ⟨2597507, by rfl⟩ : syracuseStep 3463343 = 5195015) B5195015
theorem B11098295 : Blo 1024605 11098295 := bstep (se 1 (by rfl) ⟨8323721, by rfl⟩ : syracuseStep 11098295 = 16647443) B16647443
theorem B162487781 : Blo 1024605 162487781 := bstep (se 4 (by rfl) ⟨15233229, by rfl⟩ : syracuseStep 162487781 = 30466459) B30466459
theorem B3006973 : Blo 1024605 3006973 := bstep (se 3 (by rfl) ⟨563807, by rfl⟩ : syracuseStep 3006973 = 1127615) B1127615
theorem B6251039 : Blo 1024605 6251039 := bstep (se 1 (by rfl) ⟨4688279, by rfl⟩ : syracuseStep 6251039 = 9376559) B9376559
theorem B1729255 : Blo 1024605 1729255 := bstep (se 1 (by rfl) ⟨1296941, by rfl⟩ : syracuseStep 1729255 = 2593883) B2593883
theorem B5858153 : Blo 1024605 5858153 := bstep (se 2 (by rfl) ⟨2196807, by rfl⟩ : syracuseStep 5858153 = 4393615) B4393615
theorem B3466475 : Blo 1024605 3466475 := bstep (se 1 (by rfl) ⟨2599856, by rfl⟩ : syracuseStep 3466475 = 5199713) B5199713
theorem B2188777 : Blo 1024605 2188777 := bstep (se 2 (by rfl) ⟨820791, by rfl⟩ : syracuseStep 2188777 = 1641583) B1641583
theorem B3466907 : Blo 1024605 3466907 := bstep (se 1 (by rfl) ⟨2600180, by rfl⟩ : syracuseStep 3466907 = 5200361) B5200361
theorem B12478715 : Blo 1024605 12478715 := bstep (se 1 (by rfl) ⟨9359036, by rfl⟩ : syracuseStep 12478715 = 18718073) B18718073
theorem B2190503 : Blo 1024605 2190503 := bstep (se 1 (by rfl) ⟨1642877, by rfl⟩ : syracuseStep 2190503 = 3285755) B3285755
theorem B6581503 : Blo 1024605 6581503 := bstep (se 1 (by rfl) ⟨4936127, by rfl⟩ : syracuseStep 6581503 = 9872255) B9872255
theorem B40562849 : Blo 1024605 40562849 := bstep (se 2 (by rfl) ⟨15211068, by rfl⟩ : syracuseStep 40562849 = 30422137) B30422137
theorem B7401887 : Blo 1024605 7401887 := bstep (se 1 (by rfl) ⟨5551415, by rfl⟩ : syracuseStep 7401887 = 11102831) B11102831
theorem B3470525 : Blo 1024605 3470525 := bstep (se 3 (by rfl) ⟨650723, by rfl⟩ : syracuseStep 3470525 = 1301447) B1301447
theorem B3470633 : Blo 1024605 3470633 := bstep (se 2 (by rfl) ⟨1301487, by rfl⟩ : syracuseStep 3470633 = 2602975) B2602975
theorem B1537391 : Blo 1024605 1537391 := bstep (se 1 (by rfl) ⟨1153043, by rfl⟩ : syracuseStep 1537391 = 2306087) B2306087
theorem B1537487 : Blo 1024605 1537487 := bstep (se 1 (by rfl) ⟨1153115, by rfl⟩ : syracuseStep 1537487 = 2306231) B2306231
theorem B1537577 : Blo 1024605 1537577 := bstep (se 2 (by rfl) ⟨576591, by rfl⟩ : syracuseStep 1537577 = 1153183) B1153183
theorem B1537691 : Blo 1024605 1537691 := bstep (se 1 (by rfl) ⟨1153268, by rfl⟩ : syracuseStep 1537691 = 2306537) B2306537
theorem B44365481 : Blo 1024605 44365481 := bstep (se 2 (by rfl) ⟨16637055, by rfl⟩ : syracuseStep 44365481 = 33274111) B33274111
theorem B5633819 : Blo 1024605 5633819 := bstep (se 1 (by rfl) ⟨4225364, by rfl⟩ : syracuseStep 5633819 = 8450729) B8450729
theorem B1537961 : Blo 1024605 1537961 := bstep (se 2 (by rfl) ⟨576735, by rfl⟩ : syracuseStep 1537961 = 1153471) B1153471
theorem B1538687 : Blo 1024605 1538687 := bstep (se 1 (by rfl) ⟨1154015, by rfl⟩ : syracuseStep 1538687 = 2308031) B2308031
theorem B10844855 : Blo 1024605 10844855 := bstep (se 1 (by rfl) ⟨8133641, by rfl⟩ : syracuseStep 10844855 = 16267283) B16267283
theorem B6585299 : Blo 1024605 6585299 := bstep (se 1 (by rfl) ⟨4938974, by rfl⟩ : syracuseStep 6585299 = 9877949) B9877949
theorem B1539209 : Blo 1024605 1539209 := bstep (se 2 (by rfl) ⟨577203, by rfl⟩ : syracuseStep 1539209 = 1154407) B1154407
theorem B1539239 : Blo 1024605 1539239 := bstep (se 1 (by rfl) ⟨1154429, by rfl⟩ : syracuseStep 1539239 = 2308859) B2308859
theorem B3701969 : Blo 1024605 3701969 := bstep (se 2 (by rfl) ⟨1388238, by rfl⟩ : syracuseStep 3701969 = 2776477) B2776477
theorem B1539323 : Blo 1024605 1539323 := bstep (se 1 (by rfl) ⟨1154492, by rfl⟩ : syracuseStep 1539323 = 2308985) B2308985
theorem B17530991 : Blo 1024605 17530991 := bstep (se 1 (by rfl) ⟨13148243, by rfl⟩ : syracuseStep 17530991 = 26296487) B26296487
theorem B1540475 : Blo 1024605 1540475 := bstep (se 1 (by rfl) ⟨1155356, by rfl⟩ : syracuseStep 1540475 = 2310713) B2310713
theorem B3900059 : Blo 1024605 3900059 := bstep (se 1 (by rfl) ⟨2925044, by rfl⟩ : syracuseStep 3900059 = 5850089) B5850089
theorem B1541033 : Blo 1024605 1541033 := bstep (se 2 (by rfl) ⟨577887, by rfl⟩ : syracuseStep 1541033 = 1155775) B1155775
theorem B1541087 : Blo 1024605 1541087 := bstep (se 1 (by rfl) ⟨1155815, by rfl⟩ : syracuseStep 1541087 = 2311631) B2311631
theorem B3900575 : Blo 1024605 3900575 := bstep (se 1 (by rfl) ⟨2925431, by rfl⟩ : syracuseStep 3900575 = 5850863) B5850863
theorem B1541615 : Blo 1024605 1541615 := bstep (se 1 (by rfl) ⟨1156211, by rfl⟩ : syracuseStep 1541615 = 2312423) B2312423
theorem B2918369 : Blo 1024605 2918369 := bstep (se 2 (by rfl) ⟨1094388, by rfl⟩ : syracuseStep 2918369 = 2188777) B2188777
theorem B3705095 : Blo 1024605 3705095 := bstep (se 1 (by rfl) ⟨2778821, by rfl⟩ : syracuseStep 3705095 = 5557643) B5557643
theorem B4164455 : Blo 1024605 4164455 := bstep (se 1 (by rfl) ⟨3123341, by rfl⟩ : syracuseStep 4164455 = 6246683) B6246683
theorem B1643647 : Blo 1024605 1643647 := bstep (se 1 (by rfl) ⟨1232735, by rfl⟩ : syracuseStep 1643647 = 2465471) B2465471
theorem B18748583 : Blo 1024605 18748583 := bstep (se 1 (by rfl) ⟨14061437, by rfl⟩ : syracuseStep 18748583 = 28122875) B28122875
theorem B8328677 : Blo 1024605 8328677 := bstep (se 4 (by rfl) ⟨780813, by rfl⟩ : syracuseStep 8328677 = 1561627) B1561627
theorem B4167359 : Blo 1024605 4167359 := bstep (se 1 (by rfl) ⟨3125519, by rfl⟩ : syracuseStep 4167359 = 6251039) B6251039
theorem B29300467 : Blo 1024605 29300467 := bstep (se 1 (by rfl) ⟨21975350, by rfl⟩ : syracuseStep 29300467 = 43950701) B43950701
theorem B3905435 : Blo 1024605 3905435 := bstep (se 1 (by rfl) ⟨2929076, by rfl⟩ : syracuseStep 3905435 = 5858153) B5858153
theorem B2922493 : Blo 1024605 2922493 := bstep (se 3 (by rfl) ⟨547967, by rfl⟩ : syracuseStep 2922493 = 1095935) B1095935
theorem B27041899 : Blo 1024605 27041899 := bstep (se 1 (by rfl) ⟨20281424, by rfl⟩ : syracuseStep 27041899 = 40562849) B40562849
theorem B5841341 : Blo 1024605 5841341 := bstep (se 3 (by rfl) ⟨1095251, by rfl⟩ : syracuseStep 5841341 = 2190503) B2190503
theorem B1024927 : Blo 1024605 1024927 := bstep (se 1 (by rfl) ⟨768695, by rfl⟩ : syracuseStep 1024927 = 1537391) B1537391
theorem B1024991 : Blo 1024605 1024991 := bstep (se 1 (by rfl) ⟨768743, by rfl⟩ : syracuseStep 1024991 = 1537487) B1537487
theorem B1025051 : Blo 1024605 1025051 := bstep (se 1 (by rfl) ⟨768788, by rfl⟩ : syracuseStep 1025051 = 1537577) B1537577
theorem B1025127 : Blo 1024605 1025127 := bstep (se 1 (by rfl) ⟨768845, by rfl⟩ : syracuseStep 1025127 = 1537691) B1537691
theorem B1025307 : Blo 1024605 1025307 := bstep (se 1 (by rfl) ⟨768980, by rfl⟩ : syracuseStep 1025307 = 1537961) B1537961
theorem B1025791 : Blo 1024605 1025791 := bstep (se 1 (by rfl) ⟨769343, by rfl⟩ : syracuseStep 1025791 = 1538687) B1538687
theorem B1026139 : Blo 1024605 1026139 := bstep (se 1 (by rfl) ⟨769604, by rfl⟩ : syracuseStep 1026139 = 1539209) B1539209
theorem B1026159 : Blo 1024605 1026159 := bstep (se 1 (by rfl) ⟨769619, by rfl⟩ : syracuseStep 1026159 = 1539239) B1539239
theorem B2467979 : Blo 1024605 2467979 := bstep (se 1 (by rfl) ⟨1850984, by rfl⟩ : syracuseStep 2467979 = 3701969) B3701969
theorem B1026215 : Blo 1024605 1026215 := bstep (se 1 (by rfl) ⟨769661, by rfl⟩ : syracuseStep 1026215 = 1539323) B1539323
theorem B1026799 : Blo 1024605 1026799 := bstep (se 1 (by rfl) ⟨770099, by rfl⟩ : syracuseStep 1026799 = 1540199) B1540199
theorem B1026811 : Blo 1024605 1026811 := bstep (se 1 (by rfl) ⟨770108, by rfl⟩ : syracuseStep 1026811 = 1540217) B1540217
theorem B1026843 : Blo 1024605 1026843 := bstep (se 1 (by rfl) ⟨770132, by rfl⟩ : syracuseStep 1026843 = 1540265) B1540265
theorem B14035817 : Blo 1024605 14035817 := bstep (se 2 (by rfl) ⟨5263431, by rfl⟩ : syracuseStep 14035817 = 10526863) B10526863
theorem B1027327 : Blo 1024605 1027327 := bstep (se 1 (by rfl) ⟨770495, by rfl⟩ : syracuseStep 1027327 = 1540991) B1540991
theorem B1027695 : Blo 1024605 1027695 := bstep (se 1 (by rfl) ⟨770771, by rfl⟩ : syracuseStep 1027695 = 1541543) B1541543
theorem B2305673 : Blo 1024605 2305673 := bstep (se 2 (by rfl) ⟨864627, by rfl⟩ : syracuseStep 2305673 = 1729255) B1729255
theorem B1027823 : Blo 1024605 1027823 := bstep (se 1 (by rfl) ⟨770867, by rfl⟩ : syracuseStep 1027823 = 1541735) B1541735
theorem B1027931 : Blo 1024605 1027931 := bstep (se 1 (by rfl) ⟨770948, by rfl⟩ : syracuseStep 1027931 = 1541897) B1541897
theorem B1945595 : Blo 1024605 1945595 := bstep (se 1 (by rfl) ⟨1459196, by rfl⟩ : syracuseStep 1945595 = 2918393) B2918393
theorem B2601143 : Blo 1024605 2601143 := bstep (se 1 (by rfl) ⟨1950857, by rfl⟩ : syracuseStep 2601143 = 3901715) B3901715
theorem B16037189 : Blo 1024605 16037189 := bstep (se 4 (by rfl) ⟨1503486, by rfl⟩ : syracuseStep 16037189 = 3006973) B3006973
theorem B14824943 : Blo 1024605 14824943 := bstep (se 1 (by rfl) ⟨11118707, by rfl⟩ : syracuseStep 14824943 = 22237415) B22237415
theorem B2307923 : Blo 1024605 2307923 := bstep (se 1 (by rfl) ⟨1730942, by rfl⟩ : syracuseStep 2307923 = 3461885) B3461885
theorem B1947721 : Blo 1024605 1947721 := bstep (se 2 (by rfl) ⟨730395, by rfl⟩ : syracuseStep 1947721 = 1460791) B1460791
theorem B2341639 : Blo 1024605 2341639 := bstep (se 1 (by rfl) ⟨1756229, by rfl⟩ : syracuseStep 2341639 = 3512459) B3512459
theorem B2308895 : Blo 1024605 2308895 := bstep (se 1 (by rfl) ⟨1731671, by rfl⟩ : syracuseStep 2308895 = 3463343) B3463343
theorem B2310983 : Blo 1024605 2310983 := bstep (se 1 (by rfl) ⟨1733237, by rfl⟩ : syracuseStep 2310983 = 3466475) B3466475
theorem B1950713 : Blo 1024605 1950713 := bstep (se 2 (by rfl) ⟨731517, by rfl⟩ : syracuseStep 1950713 = 1463035) B1463035
theorem B2311271 : Blo 1024605 2311271 := bstep (se 1 (by rfl) ⟨1733453, by rfl⟩ : syracuseStep 2311271 = 3466907) B3466907
theorem B31573685 : Blo 1024605 31573685 := bstep (se 5 (by rfl) ⟨1480016, by rfl⟩ : syracuseStep 31573685 = 2960033) B2960033
theorem B8767547 : Blo 1024605 8767547 := bstep (se 1 (by rfl) ⟨6575660, by rfl⟩ : syracuseStep 8767547 = 13151321) B13151321
theorem B3459887 : Blo 1024605 3459887 := bstep (se 1 (by rfl) ⟨2594915, by rfl⟩ : syracuseStep 3459887 = 5189831) B5189831
theorem B4934591 : Blo 1024605 4934591 := bstep (se 1 (by rfl) ⟨3700943, by rfl⟩ : syracuseStep 4934591 = 7401887) B7401887
theorem B3460265 : Blo 1024605 3460265 := bstep (se 2 (by rfl) ⟨1297599, by rfl⟩ : syracuseStep 3460265 = 2595199) B2595199
theorem B2313683 : Blo 1024605 2313683 := bstep (se 1 (by rfl) ⟨1735262, by rfl⟩ : syracuseStep 2313683 = 3470525) B3470525
theorem B2313755 : Blo 1024605 2313755 := bstep (se 1 (by rfl) ⟨1735316, by rfl⟩ : syracuseStep 2313755 = 3470633) B3470633
theorem B29576987 : Blo 1024605 29576987 := bstep (se 1 (by rfl) ⟨22182740, by rfl⟩ : syracuseStep 29576987 = 44365481) B44365481
theorem B3755879 : Blo 1024605 3755879 := bstep (se 1 (by rfl) ⟨2816909, by rfl⟩ : syracuseStep 3755879 = 5633819) B5633819
theorem B7229903 : Blo 1024605 7229903 := bstep (se 1 (by rfl) ⟨5422427, by rfl⟩ : syracuseStep 7229903 = 10844855) B10844855
theorem B19714985 : Blo 1024605 19714985 := bstep (se 2 (by rfl) ⟨7393119, by rfl⟩ : syracuseStep 19714985 = 14786239) B14786239
theorem B26695169 : Blo 1024605 26695169 := bstep (se 2 (by rfl) ⟨10010688, by rfl⟩ : syracuseStep 26695169 = 20021377) B20021377
theorem B9983537 : Blo 1024605 9983537 := bstep (se 2 (by rfl) ⟨3743826, by rfl⟩ : syracuseStep 9983537 = 7487653) B7487653
theorem B12507419 : Blo 1024605 12507419 := bstep (se 1 (by rfl) ⟨9380564, by rfl⟩ : syracuseStep 12507419 = 18761129) B18761129
theorem B1563355 : Blo 1024605 1563355 := bstep (se 1 (by rfl) ⟨1172516, by rfl⟩ : syracuseStep 1563355 = 2345033) B2345033
theorem B1301275 : Blo 1024605 1301275 := bstep (se 1 (by rfl) ⟨975956, by rfl⟩ : syracuseStep 1301275 = 1951913) B1951913
theorem B6577199 : Blo 1024605 6577199 := bstep (se 1 (by rfl) ⟨4932899, by rfl⟩ : syracuseStep 6577199 = 9865799) B9865799
theorem B70999247 : Blo 1024605 70999247 := bstep (se 1 (by rfl) ⟨53249435, by rfl⟩ : syracuseStep 70999247 = 106498871) B106498871
theorem B9362729 : Blo 1024605 9362729 := bstep (se 2 (by rfl) ⟨3511023, by rfl⟩ : syracuseStep 9362729 = 7022047) B7022047
theorem B3465341 : Blo 1024605 3465341 := bstep (se 3 (by rfl) ⟨649751, by rfl⟩ : syracuseStep 3465341 = 1299503) B1299503
theorem B5936080241 : Blo 1024605 5936080241 := bstep (se 2 (by rfl) ⟨2226030090, by rfl⟩ : syracuseStep 5936080241 = 4452060181) B4452060181
theorem B1172863 : Blo 1024605 1172863 := bstep (se 1 (by rfl) ⟨879647, by rfl⟩ : syracuseStep 1172863 = 1759295) B1759295
theorem B7398863 : Blo 1024605 7398863 := bstep (se 1 (by rfl) ⟨5549147, by rfl⟩ : syracuseStep 7398863 = 11098295) B11098295
theorem B5203439 : Blo 1024605 5203439 := bstep (se 1 (by rfl) ⟨3902579, by rfl⟩ : syracuseStep 5203439 = 7805159) B7805159
theorem B8775337 : Blo 1024605 8775337 := bstep (se 2 (by rfl) ⟨3290751, by rfl⟩ : syracuseStep 8775337 = 6581503) B6581503
theorem B108325187 : Blo 1024605 108325187 := bstep (se 1 (by rfl) ⟨81243890, by rfl⟩ : syracuseStep 108325187 = 162487781) B162487781
theorem B4942781 : Blo 1024605 4942781 := bstep (se 3 (by rfl) ⟨926771, by rfl⟩ : syracuseStep 4942781 = 1853543) B1853543
theorem B8319143 : Blo 1024605 8319143 := bstep (se 1 (by rfl) ⟨6239357, by rfl⟩ : syracuseStep 8319143 = 12478715) B12478715
theorem B4157723 : Blo 1024605 4157723 := bstep (se 1 (by rfl) ⟨3118292, by rfl⟩ : syracuseStep 4157723 = 6236585) B6236585
theorem B26309609 : Blo 1024605 26309609 := bstep (se 2 (by rfl) ⟨9866103, by rfl⟩ : syracuseStep 26309609 = 19732207) B19732207
theorem B1537055 : Blo 1024605 1537055 := bstep (se 1 (by rfl) ⟨1152791, by rfl⟩ : syracuseStep 1537055 = 2305583) B2305583
theorem B1537151 : Blo 1024605 1537151 := bstep (se 1 (by rfl) ⟨1152863, by rfl⟩ : syracuseStep 1537151 = 2305727) B2305727
theorem B14776091 : Blo 1024605 14776091 := bstep (se 1 (by rfl) ⟨11082068, by rfl⟩ : syracuseStep 14776091 = 22164137) B22164137
theorem B1538027 : Blo 1024605 1538027 := bstep (se 1 (by rfl) ⟨1153520, by rfl⟩ : syracuseStep 1538027 = 2307041) B2307041
theorem B2193895 : Blo 1024605 2193895 := bstep (se 1 (by rfl) ⟨1645421, by rfl⟩ : syracuseStep 2193895 = 3290843) B3290843
theorem B1538855 : Blo 1024605 1538855 := bstep (se 1 (by rfl) ⟨1154141, by rfl⟩ : syracuseStep 1538855 = 2308283) B2308283
theorem B4390199 : Blo 1024605 4390199 := bstep (se 1 (by rfl) ⟨3292649, by rfl⟩ : syracuseStep 4390199 = 6585299) B6585299
theorem B33717707 : Blo 1024605 33717707 := bstep (se 1 (by rfl) ⟨25288280, by rfl⟩ : syracuseStep 33717707 = 50576561) B50576561
theorem B22184381 : Blo 1024605 22184381 := bstep (se 3 (by rfl) ⟨4159571, by rfl⟩ : syracuseStep 22184381 = 8319143) B8319143
theorem B1540655 : Blo 1024605 1540655 := bstep (se 1 (by rfl) ⟨1155491, by rfl⟩ : syracuseStep 1540655 = 2310983) B2310983
theorem B1540847 : Blo 1024605 1540847 := bstep (se 1 (by rfl) ⟨1155635, by rfl⟩ : syracuseStep 1540847 = 2311271) B2311271
theorem B11700449 : Blo 1024605 11700449 := bstep (se 2 (by rfl) ⟨4387668, by rfl⟩ : syracuseStep 11700449 = 8775337) B8775337
theorem B1542455 : Blo 1024605 1542455 := bstep (se 1 (by rfl) ⟨1156841, by rfl⟩ : syracuseStep 1542455 = 2313683) B2313683
theorem B1542503 : Blo 1024605 1542503 := bstep (se 1 (by rfl) ⟨1156877, by rfl⟩ : syracuseStep 1542503 = 2313755) B2313755
theorem B13143323 : Blo 1024605 13143323 := bstep (se 1 (by rfl) ⟨9857492, by rfl⟩ : syracuseStep 13143323 = 19714985) B19714985
theorem B17796779 : Blo 1024605 17796779 := bstep (se 1 (by rfl) ⟨13347584, by rfl⟩ : syracuseStep 17796779 = 26695169) B26695169
theorem B6655691 : Blo 1024605 6655691 := bstep (se 1 (by rfl) ⟨4991768, by rfl⟩ : syracuseStep 6655691 = 9983537) B9983537
theorem B12488741 : Blo 1024605 12488741 := bstep (se 4 (by rfl) ⟨1170819, by rfl⟩ : syracuseStep 12488741 = 2341639) B2341639
theorem B1645319 : Blo 1024605 1645319 := bstep (se 1 (by rfl) ⟨1233989, by rfl⟩ : syracuseStep 1645319 = 2467979) B2467979
theorem B39067289 : Blo 1024605 39067289 := bstep (se 2 (by rfl) ⟨14650233, by rfl⟩ : syracuseStep 39067289 = 29300467) B29300467
theorem B2596961 : Blo 1024605 2596961 := bstep (se 2 (by rfl) ⟨973860, by rfl⟩ : syracuseStep 2596961 = 1947721) B1947721
theorem B2925193 : Blo 1024605 2925193 := bstep (se 2 (by rfl) ⟨1096947, by rfl⟩ : syracuseStep 2925193 = 2193895) B2193895
theorem B17539739 : Blo 1024605 17539739 := bstep (se 1 (by rfl) ⟨13154804, by rfl⟩ : syracuseStep 17539739 = 26309609) B26309609
theorem B1024703 : Blo 1024605 1024703 := bstep (se 1 (by rfl) ⟨768527, by rfl⟩ : syracuseStep 1024703 = 1537055) B1537055
theorem B1024767 : Blo 1024605 1024767 := bstep (se 1 (by rfl) ⟨768575, by rfl⟩ : syracuseStep 1024767 = 1537151) B1537151
theorem B10691459 : Blo 1024605 10691459 := bstep (se 1 (by rfl) ⟨8018594, by rfl⟩ : syracuseStep 10691459 = 16037189) B16037189
theorem B1025351 : Blo 1024605 1025351 := bstep (se 1 (by rfl) ⟨769013, by rfl⟩ : syracuseStep 1025351 = 1538027) B1538027
theorem B1025903 : Blo 1024605 1025903 := bstep (se 1 (by rfl) ⟨769427, by rfl⟩ : syracuseStep 1025903 = 1538855) B1538855
theorem B2926799 : Blo 1024605 2926799 := bstep (se 1 (by rfl) ⟨2195099, by rfl⟩ : syracuseStep 2926799 = 4390199) B4390199
theorem B36055865 : Blo 1024605 36055865 := bstep (se 2 (by rfl) ⟨13520949, by rfl⟩ : syracuseStep 36055865 = 27041899) B27041899
theorem B1026983 : Blo 1024605 1026983 := bstep (se 1 (by rfl) ⟨770237, by rfl⟩ : syracuseStep 1026983 = 1540475) B1540475
theorem B2600039 : Blo 1024605 2600039 := bstep (se 1 (by rfl) ⟨1950029, by rfl⟩ : syracuseStep 2600039 = 3900059) B3900059
theorem B1027355 : Blo 1024605 1027355 := bstep (se 1 (by rfl) ⟨770516, by rfl⟩ : syracuseStep 1027355 = 1541033) B1541033
theorem B1027391 : Blo 1024605 1027391 := bstep (se 1 (by rfl) ⟨770543, by rfl⟩ : syracuseStep 1027391 = 1541087) B1541087
theorem B2600383 : Blo 1024605 2600383 := bstep (se 1 (by rfl) ⟨1950287, by rfl⟩ : syracuseStep 2600383 = 3900575) B3900575
theorem B1027743 : Blo 1024605 1027743 := bstep (se 1 (by rfl) ⟨770807, by rfl⟩ : syracuseStep 1027743 = 1541615) B1541615
theorem B19279741 : Blo 1024605 19279741 := bstep (se 3 (by rfl) ⟨3614951, by rfl⟩ : syracuseStep 19279741 = 7229903) B7229903
theorem B5845031 : Blo 1024605 5845031 := bstep (se 1 (by rfl) ⟨4383773, by rfl⟩ : syracuseStep 5845031 = 8767547) B8767547
theorem B2470063 : Blo 1024605 2470063 := bstep (se 1 (by rfl) ⟨1852547, by rfl⟩ : syracuseStep 2470063 = 3705095) B3705095
theorem B2306591 : Blo 1024605 2306591 := bstep (se 1 (by rfl) ⟨1729943, by rfl⟩ : syracuseStep 2306591 = 3459887) B3459887
theorem B3289727 : Blo 1024605 3289727 := bstep (se 1 (by rfl) ⟨2467295, by rfl⟩ : syracuseStep 3289727 = 4934591) B4934591
theorem B2306843 : Blo 1024605 2306843 := bstep (se 1 (by rfl) ⟨1730132, by rfl⟩ : syracuseStep 2306843 = 3460265) B3460265
theorem B2503919 : Blo 1024605 2503919 := bstep (se 1 (by rfl) ⟨1877939, by rfl⟩ : syracuseStep 2503919 = 3755879) B3755879
theorem B12499055 : Blo 1024605 12499055 := bstep (se 1 (by rfl) ⟨9374291, by rfl⟩ : syracuseStep 12499055 = 18748583) B18748583
theorem B2603623 : Blo 1024605 2603623 := bstep (se 1 (by rfl) ⟨1952717, by rfl⟩ : syracuseStep 2603623 = 3905435) B3905435
theorem B84196493 : Blo 1024605 84196493 := bstep (se 3 (by rfl) ⟨15786842, by rfl⟩ : syracuseStep 84196493 = 31573685) B31573685
theorem B47332831 : Blo 1024605 47332831 := bstep (se 1 (by rfl) ⟨35499623, by rfl⟩ : syracuseStep 47332831 = 70999247) B70999247
theorem B6241819 : Blo 1024605 6241819 := bstep (se 1 (by rfl) ⟨4681364, by rfl⟩ : syracuseStep 6241819 = 9362729) B9362729
theorem B7782317 : Blo 1024605 7782317 := bstep (se 3 (by rfl) ⟨1459184, by rfl⟩ : syracuseStep 7782317 = 2918369) B2918369
theorem B2310227 : Blo 1024605 2310227 := bstep (se 1 (by rfl) ⟨1732670, by rfl⟩ : syracuseStep 2310227 = 3465341) B3465341
theorem B4932575 : Blo 1024605 4932575 := bstep (se 1 (by rfl) ⟨3699431, by rfl⟩ : syracuseStep 4932575 = 7398863) B7398863
theorem B9357211 : Blo 1024605 9357211 := bstep (se 1 (by rfl) ⟨7017908, by rfl⟩ : syracuseStep 9357211 = 14035817) B14035817
theorem B3295187 : Blo 1024605 3295187 := bstep (se 1 (by rfl) ⟨2471390, by rfl⟩ : syracuseStep 3295187 = 4942781) B4942781
theorem B1297063 : Blo 1024605 1297063 := bstep (se 1 (by rfl) ⟨972797, by rfl⟩ : syracuseStep 1297063 = 1945595) B1945595
theorem B2771815 : Blo 1024605 2771815 := bstep (se 1 (by rfl) ⟨2078861, by rfl⟩ : syracuseStep 2771815 = 4157723) B4157723
theorem B2084473 : Blo 1024605 2084473 := bstep (se 2 (by rfl) ⟨781677, by rfl⟩ : syracuseStep 2084473 = 1563355) B1563355
theorem B9883295 : Blo 1024605 9883295 := bstep (se 1 (by rfl) ⟨7412471, by rfl⟩ : syracuseStep 9883295 = 14824943) B14824943
theorem B9850727 : Blo 1024605 9850727 := bstep (se 1 (by rfl) ⟨7388045, by rfl⟩ : syracuseStep 9850727 = 14776091) B14776091
theorem B11687327 : Blo 1024605 11687327 := bstep (se 1 (by rfl) ⟨8765495, by rfl⟩ : syracuseStep 11687327 = 17530991) B17530991
theorem B1300475 : Blo 1024605 1300475 := bstep (se 1 (by rfl) ⟨975356, by rfl⟩ : syracuseStep 1300475 = 1950713) B1950713
theorem B2776303 : Blo 1024605 2776303 := bstep (se 1 (by rfl) ⟨2082227, by rfl⟩ : syracuseStep 2776303 = 4164455) B4164455
theorem B19717991 : Blo 1024605 19717991 := bstep (se 1 (by rfl) ⟨14788493, by rfl⟩ : syracuseStep 19717991 = 29576987) B29576987
theorem B2778239 : Blo 1024605 2778239 := bstep (se 1 (by rfl) ⟨2083679, by rfl⟩ : syracuseStep 2778239 = 4167359) B4167359
theorem B22209805 : Blo 1024605 22209805 := bstep (se 3 (by rfl) ⟨4164338, by rfl⟩ : syracuseStep 22209805 = 8328677) B8328677
theorem B4384799 : Blo 1024605 4384799 := bstep (se 1 (by rfl) ⟨3288599, by rfl⟩ : syracuseStep 4384799 = 6577199) B6577199
theorem B3894227 : Blo 1024605 3894227 := bstep (se 1 (by rfl) ⟨2920670, by rfl⟩ : syracuseStep 3894227 = 5841341) B5841341
theorem B33353117 : Blo 1024605 33353117 := bstep (se 3 (by rfl) ⟨6253709, by rfl⟩ : syracuseStep 33353117 = 12507419) B12507419
theorem B3957386827 : Blo 1024605 3957386827 := bstep (se 1 (by rfl) ⟨2968040120, by rfl⟩ : syracuseStep 3957386827 = 5936080241) B5936080241
theorem B3468959 : Blo 1024605 3468959 := bstep (se 1 (by rfl) ⟨2601719, by rfl⟩ : syracuseStep 3468959 = 5203439) B5203439
theorem B2191529 : Blo 1024605 2191529 := bstep (se 2 (by rfl) ⟨821823, by rfl⟩ : syracuseStep 2191529 = 1643647) B1643647
theorem B72216791 : Blo 1024605 72216791 := bstep (se 1 (by rfl) ⟨54162593, by rfl⟩ : syracuseStep 72216791 = 108325187) B108325187
theorem B6255269 : Blo 1024605 6255269 := bstep (se 4 (by rfl) ⟨586431, by rfl⟩ : syracuseStep 6255269 = 1172863) B1172863
theorem B1537115 : Blo 1024605 1537115 := bstep (se 1 (by rfl) ⟨1152836, by rfl⟩ : syracuseStep 1537115 = 2305673) B2305673
theorem B3896657 : Blo 1024605 3896657 := bstep (se 2 (by rfl) ⟨1461246, by rfl⟩ : syracuseStep 3896657 = 2922493) B2922493
theorem B1734095 : Blo 1024605 1734095 := bstep (se 1 (by rfl) ⟨1300571, by rfl⟩ : syracuseStep 1734095 = 2601143) B2601143
theorem B1735033 : Blo 1024605 1735033 := bstep (se 2 (by rfl) ⟨650637, by rfl⟩ : syracuseStep 1735033 = 1301275) B1301275
theorem B1538615 : Blo 1024605 1538615 := bstep (se 1 (by rfl) ⟨1153961, by rfl⟩ : syracuseStep 1538615 = 2307923) B2307923
theorem B1539263 : Blo 1024605 1539263 := bstep (se 1 (by rfl) ⟨1154447, by rfl⟩ : syracuseStep 1539263 = 2308895) B2308895
theorem B22478471 : Blo 1024605 22478471 := bstep (se 1 (by rfl) ⟨16858853, by rfl⟩ : syracuseStep 22478471 = 33717707) B33717707
theorem B1540151 : Blo 1024605 1540151 := bstep (se 1 (by rfl) ⟨1155113, by rfl⟩ : syracuseStep 1540151 = 2310227) B2310227
theorem B3900257 : Blo 1024605 3900257 := bstep (se 2 (by rfl) ⟨1462596, by rfl⟩ : syracuseStep 3900257 = 2925193) B2925193
theorem B2196791 : Blo 1024605 2196791 := bstep (se 1 (by rfl) ⟨1647593, by rfl⟩ : syracuseStep 2196791 = 3295187) B3295187
theorem B7800299 : Blo 1024605 7800299 := bstep (se 1 (by rfl) ⟨5850224, by rfl⟩ : syracuseStep 7800299 = 11700449) B11700449
theorem B6588863 : Blo 1024605 6588863 := bstep (se 1 (by rfl) ⟨4941647, by rfl⟩ : syracuseStep 6588863 = 9883295) B9883295
theorem B11864519 : Blo 1024605 11864519 := bstep (se 1 (by rfl) ⟨8898389, by rfl⟩ : syracuseStep 11864519 = 17796779) B17796779
theorem B8325827 : Blo 1024605 8325827 := bstep (se 1 (by rfl) ⟨6244370, by rfl⟩ : syracuseStep 8325827 = 12488741) B12488741
theorem B13145327 : Blo 1024605 13145327 := bstep (se 1 (by rfl) ⟨9858995, by rfl⟩ : syracuseStep 13145327 = 19717991) B19717991
theorem B2923199 : Blo 1024605 2923199 := bstep (se 1 (by rfl) ⟨2192399, by rfl⟩ : syracuseStep 2923199 = 4384799) B4384799
theorem B2596151 : Blo 1024605 2596151 := bstep (se 1 (by rfl) ⟨1947113, by rfl⟩ : syracuseStep 2596151 = 3894227) B3894227
theorem B48144527 : Blo 1024605 48144527 := bstep (se 1 (by rfl) ⟨36108395, by rfl⟩ : syracuseStep 48144527 = 72216791) B72216791
theorem B4170179 : Blo 1024605 4170179 := bstep (se 1 (by rfl) ⟨3127634, by rfl⟩ : syracuseStep 4170179 = 6255269) B6255269
theorem B11117189 : Blo 1024605 11117189 := bstep (se 4 (by rfl) ⟨1042236, by rfl⟩ : syracuseStep 11117189 = 2084473) B2084473
theorem B1024743 : Blo 1024605 1024743 := bstep (se 1 (by rfl) ⟨768557, by rfl⟩ : syracuseStep 1024743 = 1537115) B1537115
theorem B2597771 : Blo 1024605 2597771 := bstep (se 1 (by rfl) ⟨1948328, by rfl⟩ : syracuseStep 2597771 = 3896657) B3896657
theorem B1156063 : Blo 1024605 1156063 := bstep (se 1 (by rfl) ⟨867047, by rfl⟩ : syracuseStep 1156063 = 1734095) B1734095
theorem B8332703 : Blo 1024605 8332703 := bstep (se 1 (by rfl) ⟨6249527, by rfl⟩ : syracuseStep 8332703 = 12499055) B12499055
theorem B1025743 : Blo 1024605 1025743 := bstep (se 1 (by rfl) ⟨769307, by rfl⟩ : syracuseStep 1025743 = 1538615) B1538615
theorem B1026175 : Blo 1024605 1026175 := bstep (se 1 (by rfl) ⟨769631, by rfl⟩ : syracuseStep 1026175 = 1539263) B1539263
theorem B14985647 : Blo 1024605 14985647 := bstep (se 1 (by rfl) ⟨11239235, by rfl⟩ : syracuseStep 14985647 = 22478471) B22478471
theorem B5188211 : Blo 1024605 5188211 := bstep (se 1 (by rfl) ⟨3891158, by rfl⟩ : syracuseStep 5188211 = 7782317) B7782317
theorem B14789587 : Blo 1024605 14789587 := bstep (se 1 (by rfl) ⟨11092190, by rfl⟩ : syracuseStep 14789587 = 22184381) B22184381
theorem B1027103 : Blo 1024605 1027103 := bstep (se 1 (by rfl) ⟨770327, by rfl⟩ : syracuseStep 1027103 = 1540655) B1540655
theorem B1027231 : Blo 1024605 1027231 := bstep (se 1 (by rfl) ⟨770423, by rfl⟩ : syracuseStep 1027231 = 1540847) B1540847
theorem B3288383 : Blo 1024605 3288383 := bstep (se 1 (by rfl) ⟨2466287, by rfl⟩ : syracuseStep 3288383 = 4932575) B4932575
theorem B1028303 : Blo 1024605 1028303 := bstep (se 1 (by rfl) ⟨771227, by rfl⟩ : syracuseStep 1028303 = 1542455) B1542455
theorem B1028335 : Blo 1024605 1028335 := bstep (se 1 (by rfl) ⟨771251, by rfl⟩ : syracuseStep 1028335 = 1542503) B1542503
theorem B8762215 : Blo 1024605 8762215 := bstep (se 1 (by rfl) ⟨6571661, by rfl⟩ : syracuseStep 8762215 = 13143323) B13143323
theorem B4437127 : Blo 1024605 4437127 := bstep (se 1 (by rfl) ⟨3327845, by rfl⟩ : syracuseStep 4437127 = 6655691) B6655691
theorem B6567151 : Blo 1024605 6567151 := bstep (se 1 (by rfl) ⟨4925363, by rfl⟩ : syracuseStep 6567151 = 9850727) B9850727
theorem B5276515769 : Blo 1024605 5276515769 := bstep (se 2 (by rfl) ⟨1978693413, by rfl⟩ : syracuseStep 5276515769 = 3957386827) B3957386827
theorem B25706321 : Blo 1024605 25706321 := bstep (se 2 (by rfl) ⟨9639870, by rfl⟩ : syracuseStep 25706321 = 19279741) B19279741
theorem B3293417 : Blo 1024605 3293417 := bstep (se 2 (by rfl) ⟨1235031, by rfl⟩ : syracuseStep 3293417 = 2470063) B2470063
theorem B7127639 : Blo 1024605 7127639 := bstep (se 1 (by rfl) ⟨5345729, by rfl⟩ : syracuseStep 7127639 = 10691459) B10691459
theorem B1852159 : Blo 1024605 1852159 := bstep (se 1 (by rfl) ⟨1389119, by rfl⟩ : syracuseStep 1852159 = 2778239) B2778239
theorem B1951199 : Blo 1024605 1951199 := bstep (se 1 (by rfl) ⟨1463399, by rfl⟩ : syracuseStep 1951199 = 2926799) B2926799
theorem B24037243 : Blo 1024605 24037243 := bstep (se 1 (by rfl) ⟨18027932, by rfl⟩ : syracuseStep 24037243 = 36055865) B36055865
theorem B22235411 : Blo 1024605 22235411 := bstep (se 1 (by rfl) ⟨16676558, by rfl⟩ : syracuseStep 22235411 = 33353117) B33353117
theorem B2312639 : Blo 1024605 2312639 := bstep (se 1 (by rfl) ⟨1734479, by rfl⟩ : syracuseStep 2312639 = 3468959) B3468959
theorem B1461019 : Blo 1024605 1461019 := bstep (se 1 (by rfl) ⟨1095764, by rfl⟩ : syracuseStep 1461019 = 2191529) B2191529
theorem B2313377 : Blo 1024605 2313377 := bstep (se 2 (by rfl) ⟨867516, by rfl⟩ : syracuseStep 2313377 = 1735033) B1735033
theorem B29613073 : Blo 1024605 29613073 := bstep (se 2 (by rfl) ⟨11104902, by rfl⟩ : syracuseStep 29613073 = 22209805) B22209805
theorem B12476281 : Blo 1024605 12476281 := bstep (se 2 (by rfl) ⟨4678605, by rfl⟩ : syracuseStep 12476281 = 9357211) B9357211
theorem B1729417 : Blo 1024605 1729417 := bstep (se 2 (by rfl) ⟨648531, by rfl⟩ : syracuseStep 1729417 = 1297063) B1297063
theorem B7791551 : Blo 1024605 7791551 := bstep (se 1 (by rfl) ⟨5843663, by rfl⟩ : syracuseStep 7791551 = 11687327) B11687327
theorem B3695753 : Blo 1024605 3695753 := bstep (se 2 (by rfl) ⟨1385907, by rfl⟩ : syracuseStep 3695753 = 2771815) B2771815
theorem B3467177 : Blo 1024605 3467177 := bstep (se 2 (by rfl) ⟨1300191, by rfl⟩ : syracuseStep 3467177 = 2600383) B2600383
theorem B26044859 : Blo 1024605 26044859 := bstep (se 1 (by rfl) ⟨19533644, by rfl⟩ : syracuseStep 26044859 = 39067289) B39067289
theorem B3467933 : Blo 1024605 3467933 := bstep (se 3 (by rfl) ⟨650237, by rfl⟩ : syracuseStep 3467933 = 1300475) B1300475
theorem B1731307 : Blo 1024605 1731307 := bstep (se 1 (by rfl) ⟨1298480, by rfl⟩ : syracuseStep 1731307 = 2596961) B2596961
theorem B11693159 : Blo 1024605 11693159 := bstep (se 1 (by rfl) ⟨8769869, by rfl⟩ : syracuseStep 11693159 = 17539739) B17539739
theorem B4387517 : Blo 1024605 4387517 := bstep (se 3 (by rfl) ⟨822659, by rfl⟩ : syracuseStep 4387517 = 1645319) B1645319
theorem B1733359 : Blo 1024605 1733359 := bstep (se 1 (by rfl) ⟨1300019, by rfl⟩ : syracuseStep 1733359 = 2600039) B2600039
theorem B3896687 : Blo 1024605 3896687 := bstep (se 1 (by rfl) ⟨2922515, by rfl⟩ : syracuseStep 3896687 = 5845031) B5845031
theorem B1537727 : Blo 1024605 1537727 := bstep (se 1 (by rfl) ⟨1153295, by rfl⟩ : syracuseStep 1537727 = 2306591) B2306591
theorem B2193151 : Blo 1024605 2193151 := bstep (se 1 (by rfl) ⟨1644863, by rfl⟩ : syracuseStep 2193151 = 3289727) B3289727
theorem B1537895 : Blo 1024605 1537895 := bstep (se 1 (by rfl) ⟨1153421, by rfl⟩ : syracuseStep 1537895 = 2306843) B2306843
theorem B3471497 : Blo 1024605 3471497 := bstep (se 2 (by rfl) ⟨1301811, by rfl⟩ : syracuseStep 3471497 = 2603623) B2603623
theorem B1669279 : Blo 1024605 1669279 := bstep (se 1 (by rfl) ⟨1251959, by rfl⟩ : syracuseStep 1669279 = 2503919) B2503919
theorem B3701737 : Blo 1024605 3701737 := bstep (se 2 (by rfl) ⟨1388151, by rfl⟩ : syracuseStep 3701737 = 2776303) B2776303
theorem B63110441 : Blo 1024605 63110441 := bstep (se 2 (by rfl) ⟨23666415, by rfl⟩ : syracuseStep 63110441 = 47332831) B47332831
theorem B8322425 : Blo 1024605 8322425 := bstep (se 2 (by rfl) ⟨3120909, by rfl⟩ : syracuseStep 8322425 = 6241819) B6241819
theorem B56130995 : Blo 1024605 56130995 := bstep (se 1 (by rfl) ⟨42098246, by rfl⟩ : syracuseStep 56130995 = 84196493) B84196493
theorem B4751759 : Blo 1024605 4751759 := bstep (se 1 (by rfl) ⟨3563819, by rfl⟩ : syracuseStep 4751759 = 7127639) B7127639
theorem B8782445 : Blo 1024605 8782445 := bstep (se 3 (by rfl) ⟨1646708, by rfl⟩ : syracuseStep 8782445 = 3293417) B3293417
theorem B1541417 : Blo 1024605 1541417 := bstep (se 2 (by rfl) ⟨578031, by rfl⟩ : syracuseStep 1541417 = 1156063) B1156063
theorem B1541759 : Blo 1024605 1541759 := bstep (se 1 (by rfl) ⟨1156319, by rfl⟩ : syracuseStep 1541759 = 2312639) B2312639
theorem B4392575 : Blo 1024605 4392575 := bstep (se 1 (by rfl) ⟨3294431, by rfl⟩ : syracuseStep 4392575 = 6588863) B6588863
theorem B1542251 : Blo 1024605 1542251 := bstep (se 1 (by rfl) ⟨1156688, by rfl⟩ : syracuseStep 1542251 = 2313377) B2313377
theorem B142445141 : Blo 1024605 142445141 := bstep (se 8 (by rfl) ⟨834639, by rfl⟩ : syracuseStep 142445141 = 1669279) B1669279
theorem B7411459 : Blo 1024605 7411459 := bstep (se 1 (by rfl) ⟨5558594, by rfl⟩ : syracuseStep 7411459 = 11117189) B11117189
theorem B8756201 : Blo 1024605 8756201 := bstep (se 2 (by rfl) ⟨3283575, by rfl⟩ : syracuseStep 8756201 = 6567151) B6567151
theorem B2924201 : Blo 1024605 2924201 := bstep (se 2 (by rfl) ⟨1096575, by rfl⟩ : syracuseStep 2924201 = 2193151) B2193151
theorem B2925011 : Blo 1024605 2925011 := bstep (se 1 (by rfl) ⟨2193758, by rfl⟩ : syracuseStep 2925011 = 4387517) B4387517
theorem B2597791 : Blo 1024605 2597791 := bstep (se 1 (by rfl) ⟨1948343, by rfl⟩ : syracuseStep 2597791 = 3896687) B3896687
theorem B1025151 : Blo 1024605 1025151 := bstep (se 1 (by rfl) ⟨768863, by rfl⟩ : syracuseStep 1025151 = 1537727) B1537727
theorem B1025263 : Blo 1024605 1025263 := bstep (se 1 (by rfl) ⟨768947, by rfl⟩ : syracuseStep 1025263 = 1537895) B1537895
theorem B128198629 : Blo 1024605 128198629 := bstep (se 4 (by rfl) ⟨12018621, by rfl⟩ : syracuseStep 128198629 = 24037243) B24037243
theorem B5548283 : Blo 1024605 5548283 := bstep (se 1 (by rfl) ⟨4161212, by rfl⟩ : syracuseStep 5548283 = 8322425) B8322425
theorem B1026767 : Blo 1024605 1026767 := bstep (se 1 (by rfl) ⟨770075, by rfl⟩ : syracuseStep 1026767 = 1540151) B1540151
theorem B2600171 : Blo 1024605 2600171 := bstep (se 1 (by rfl) ⟨1950128, by rfl⟩ : syracuseStep 2600171 = 3900257) B3900257
theorem B2469545 : Blo 1024605 2469545 := bstep (se 2 (by rfl) ⟨926079, by rfl⟩ : syracuseStep 2469545 = 1852159) B1852159
theorem B2305889 : Blo 1024605 2305889 := bstep (se 2 (by rfl) ⟨864708, by rfl⟩ : syracuseStep 2305889 = 1729417) B1729417
theorem B14823607 : Blo 1024605 14823607 := bstep (se 1 (by rfl) ⟨11117705, by rfl⟩ : syracuseStep 14823607 = 22235411) B22235411
theorem B7909679 : Blo 1024605 7909679 := bstep (se 1 (by rfl) ⟨5932259, by rfl⟩ : syracuseStep 7909679 = 11864519) B11864519
theorem B5550551 : Blo 1024605 5550551 := bstep (se 1 (by rfl) ⟨4162913, by rfl⟩ : syracuseStep 5550551 = 8325827) B8325827
theorem B8763551 : Blo 1024605 8763551 := bstep (se 1 (by rfl) ⟨6572663, by rfl⟩ : syracuseStep 8763551 = 13145327) B13145327
theorem B2308409 : Blo 1024605 2308409 := bstep (se 2 (by rfl) ⟨865653, by rfl⟩ : syracuseStep 2308409 = 1731307) B1731307
theorem B1948025 : Blo 1024605 1948025 := bstep (se 2 (by rfl) ⟨730509, by rfl⟩ : syracuseStep 1948025 = 1461019) B1461019
theorem B1948799 : Blo 1024605 1948799 := bstep (se 1 (by rfl) ⟨1461599, by rfl⟩ : syracuseStep 1948799 = 2923199) B2923199
theorem B32096351 : Blo 1024605 32096351 := bstep (se 1 (by rfl) ⟨24072263, by rfl⟩ : syracuseStep 32096351 = 48144527) B48144527
theorem B5194367 : Blo 1024605 5194367 := bstep (se 1 (by rfl) ⟨3895775, by rfl⟩ : syracuseStep 5194367 = 7791551) B7791551
theorem B5555135 : Blo 1024605 5555135 := bstep (se 1 (by rfl) ⟨4166351, by rfl⟩ : syracuseStep 5555135 = 8332703) B8332703
theorem B2311145 : Blo 1024605 2311145 := bstep (se 2 (by rfl) ⟨866679, by rfl⟩ : syracuseStep 2311145 = 1733359) B1733359
theorem B11682953 : Blo 1024605 11682953 := bstep (se 2 (by rfl) ⟨4381107, by rfl⟩ : syracuseStep 11682953 = 8762215) B8762215
theorem B69452957 : Blo 1024605 69452957 := bstep (se 3 (by rfl) ⟨13022429, by rfl⟩ : syracuseStep 69452957 = 26044859) B26044859
theorem B2311451 : Blo 1024605 2311451 := bstep (se 1 (by rfl) ⟨1733588, by rfl⟩ : syracuseStep 2311451 = 3467177) B3467177
theorem B5916169 : Blo 1024605 5916169 := bstep (se 2 (by rfl) ⟨2218563, by rfl⟩ : syracuseStep 5916169 = 4437127) B4437127
theorem B3458807 : Blo 1024605 3458807 := bstep (se 1 (by rfl) ⟨2594105, by rfl⟩ : syracuseStep 3458807 = 5188211) B5188211
theorem B2311955 : Blo 1024605 2311955 := bstep (se 1 (by rfl) ⟨1733966, by rfl⟩ : syracuseStep 2311955 = 3467933) B3467933
theorem B4935649 : Blo 1024605 4935649 := bstep (se 2 (by rfl) ⟨1850868, by rfl⟩ : syracuseStep 4935649 = 3701737) B3701737
theorem B2314331 : Blo 1024605 2314331 := bstep (se 1 (by rfl) ⟨1735748, by rfl⟩ : syracuseStep 2314331 = 3471497) B3471497
theorem B16635041 : Blo 1024605 16635041 := bstep (se 2 (by rfl) ⟨6238140, by rfl⟩ : syracuseStep 16635041 = 12476281) B12476281
theorem B1464527 : Blo 1024605 1464527 := bstep (se 1 (by rfl) ⟨1098395, by rfl⟩ : syracuseStep 1464527 = 2196791) B2196791
theorem B1300799 : Blo 1024605 1300799 := bstep (se 1 (by rfl) ⟨975599, by rfl⟩ : syracuseStep 1300799 = 1951199) B1951199
theorem B5200199 : Blo 1024605 5200199 := bstep (se 1 (by rfl) ⟨3900149, by rfl⟩ : syracuseStep 5200199 = 7800299) B7800299
theorem B9855341 : Blo 1024605 9855341 := bstep (se 3 (by rfl) ⟨1847876, by rfl⟩ : syracuseStep 9855341 = 3695753) B3695753
theorem B19719449 : Blo 1024605 19719449 := bstep (se 2 (by rfl) ⟨7394793, by rfl⟩ : syracuseStep 19719449 = 14789587) B14789587
theorem B1730767 : Blo 1024605 1730767 := bstep (se 1 (by rfl) ⟨1298075, by rfl⟩ : syracuseStep 1730767 = 2596151) B2596151
theorem B2780119 : Blo 1024605 2780119 := bstep (se 1 (by rfl) ⟨2085089, by rfl⟩ : syracuseStep 2780119 = 4170179) B4170179
theorem B1731847 : Blo 1024605 1731847 := bstep (se 1 (by rfl) ⟨1298885, by rfl⟩ : syracuseStep 1731847 = 2597771) B2597771
theorem B9990431 : Blo 1024605 9990431 := bstep (se 1 (by rfl) ⟨7492823, by rfl⟩ : syracuseStep 9990431 = 14985647) B14985647
theorem B7795439 : Blo 1024605 7795439 := bstep (se 1 (by rfl) ⟨5846579, by rfl⟩ : syracuseStep 7795439 = 11693159) B11693159
theorem B2192255 : Blo 1024605 2192255 := bstep (se 1 (by rfl) ⟨1644191, by rfl⟩ : syracuseStep 2192255 = 3288383) B3288383
theorem B149682653 : Blo 1024605 149682653 := bstep (se 3 (by rfl) ⟨28065497, by rfl⟩ : syracuseStep 149682653 = 56130995) B56130995
theorem B39484097 : Blo 1024605 39484097 := bstep (se 2 (by rfl) ⟨14806536, by rfl⟩ : syracuseStep 39484097 = 29613073) B29613073
theorem B42073627 : Blo 1024605 42073627 := bstep (se 1 (by rfl) ⟨31555220, by rfl⟩ : syracuseStep 42073627 = 63110441) B63110441
theorem B3517677179 : Blo 1024605 3517677179 := bstep (se 1 (by rfl) ⟨2638257884, by rfl⟩ : syracuseStep 3517677179 = 5276515769) B5276515769
theorem B17137547 : Blo 1024605 17137547 := bstep (se 1 (by rfl) ⟨12853160, by rfl⟩ : syracuseStep 17137547 = 25706321) B25706321
theorem B21397567 : Blo 1024605 21397567 := bstep (se 1 (by rfl) ⟨16048175, by rfl⟩ : syracuseStep 21397567 = 32096351) B32096351
theorem B3703423 : Blo 1024605 3703423 := bstep (se 1 (by rfl) ⟨2777567, by rfl⟩ : syracuseStep 3703423 = 5555135) B5555135
theorem B1540763 : Blo 1024605 1540763 := bstep (se 1 (by rfl) ⟨1155572, by rfl⟩ : syracuseStep 1540763 = 2311145) B2311145
theorem B46301971 : Blo 1024605 46301971 := bstep (se 1 (by rfl) ⟨34726478, by rfl⟩ : syracuseStep 46301971 = 69452957) B69452957
theorem B1540967 : Blo 1024605 1540967 := bstep (se 1 (by rfl) ⟨1155725, by rfl⟩ : syracuseStep 1540967 = 2311451) B2311451
theorem B1541303 : Blo 1024605 1541303 := bstep (se 1 (by rfl) ⟨1155977, by rfl⟩ : syracuseStep 1541303 = 2311955) B2311955
theorem B94963427 : Blo 1024605 94963427 := bstep (se 1 (by rfl) ⟨71222570, by rfl⟩ : syracuseStep 94963427 = 142445141) B142445141
theorem B1542887 : Blo 1024605 1542887 := bstep (se 1 (by rfl) ⟨1157165, by rfl⟩ : syracuseStep 1542887 = 2314331) B2314331
theorem B3706825 : Blo 1024605 3706825 := bstep (se 2 (by rfl) ⟨1390059, by rfl⟩ : syracuseStep 3706825 = 2780119) B2780119
theorem B5837467 : Blo 1024605 5837467 := bstep (se 1 (by rfl) ⟨4378100, by rfl⟩ : syracuseStep 5837467 = 8756201) B8756201
theorem B19764809 : Blo 1024605 19764809 := bstep (se 2 (by rfl) ⟨7411803, by rfl⟩ : syracuseStep 19764809 = 14823607) B14823607
theorem B3905405 : Blo 1024605 3905405 := bstep (se 3 (by rfl) ⟨732263, by rfl⟩ : syracuseStep 3905405 = 1464527) B1464527
theorem B13146299 : Blo 1024605 13146299 := bstep (se 1 (by rfl) ⟨9859724, by rfl⟩ : syracuseStep 13146299 = 19719449) B19719449
theorem B1646363 : Blo 1024605 1646363 := bstep (se 1 (by rfl) ⟨1234772, by rfl⟩ : syracuseStep 1646363 = 2469545) B2469545
theorem B6660287 : Blo 1024605 6660287 := bstep (se 1 (by rfl) ⟨4995215, by rfl⟩ : syracuseStep 6660287 = 9990431) B9990431
theorem B5842367 : Blo 1024605 5842367 := bstep (se 1 (by rfl) ⟨4381775, by rfl⟩ : syracuseStep 5842367 = 8763551) B8763551
theorem B99788435 : Blo 1024605 99788435 := bstep (se 1 (by rfl) ⟨74841326, by rfl⟩ : syracuseStep 99788435 = 149682653) B149682653
theorem B26322731 : Blo 1024605 26322731 := bstep (se 1 (by rfl) ⟨19742048, by rfl⟩ : syracuseStep 26322731 = 39484097) B39484097
theorem B2345118119 : Blo 1024605 2345118119 := bstep (se 1 (by rfl) ⟨1758838589, by rfl⟩ : syracuseStep 2345118119 = 3517677179) B3517677179
theorem B1027611 : Blo 1024605 1027611 := bstep (se 1 (by rfl) ⟨770708, by rfl⟩ : syracuseStep 1027611 = 1541417) B1541417
theorem B1027839 : Blo 1024605 1027839 := bstep (se 1 (by rfl) ⟨770879, by rfl⟩ : syracuseStep 1027839 = 1541759) B1541759
theorem B2928383 : Blo 1024605 2928383 := bstep (se 1 (by rfl) ⟨2196287, by rfl⟩ : syracuseStep 2928383 = 4392575) B4392575
theorem B2305871 : Blo 1024605 2305871 := bstep (se 1 (by rfl) ⟨1729403, by rfl⟩ : syracuseStep 2305871 = 3458807) B3458807
theorem B1028167 : Blo 1024605 1028167 := bstep (se 1 (by rfl) ⟨771125, by rfl⟩ : syracuseStep 1028167 = 1542251) B1542251
theorem B170931505 : Blo 1024605 170931505 := bstep (se 2 (by rfl) ⟨64099314, by rfl⟩ : syracuseStep 170931505 = 128198629) B128198629
theorem B2307689 : Blo 1024605 2307689 := bstep (se 2 (by rfl) ⟨865383, by rfl⟩ : syracuseStep 2307689 = 1730767) B1730767
theorem B11090027 : Blo 1024605 11090027 := bstep (se 1 (by rfl) ⟨8317520, by rfl⟩ : syracuseStep 11090027 = 16635041) B16635041
theorem B2309129 : Blo 1024605 2309129 := bstep (se 2 (by rfl) ⟨865923, by rfl⟩ : syracuseStep 2309129 = 1731847) B1731847
theorem B6570227 : Blo 1024605 6570227 := bstep (se 1 (by rfl) ⟨4927670, by rfl⟩ : syracuseStep 6570227 = 9855341) B9855341
theorem B1950007 : Blo 1024605 1950007 := bstep (se 1 (by rfl) ⟨1462505, by rfl⟩ : syracuseStep 1950007 = 2925011) B2925011
theorem B9881945 : Blo 1024605 9881945 := bstep (se 2 (by rfl) ⟨3705729, by rfl⟩ : syracuseStep 9881945 = 7411459) B7411459
theorem B5196797 : Blo 1024605 5196797 := bstep (se 3 (by rfl) ⟨974399, by rfl⟩ : syracuseStep 5196797 = 1948799) B1948799
theorem B5196959 : Blo 1024605 5196959 := bstep (se 1 (by rfl) ⟨3897719, by rfl⟩ : syracuseStep 5196959 = 7795439) B7795439
theorem B1461503 : Blo 1024605 1461503 := bstep (se 1 (by rfl) ⟨1096127, by rfl⟩ : syracuseStep 1461503 = 2192255) B2192255
theorem B1298683 : Blo 1024605 1298683 := bstep (se 1 (by rfl) ⟨974012, by rfl⟩ : syracuseStep 1298683 = 1948025) B1948025
theorem B11425031 : Blo 1024605 11425031 := bstep (se 1 (by rfl) ⟨8568773, by rfl⟩ : syracuseStep 11425031 = 17137547) B17137547
theorem B3167839 : Blo 1024605 3167839 := bstep (se 1 (by rfl) ⟨2375879, by rfl⟩ : syracuseStep 3167839 = 4751759) B4751759
theorem B5854963 : Blo 1024605 5854963 := bstep (se 1 (by rfl) ⟨4391222, by rfl⟩ : syracuseStep 5854963 = 8782445) B8782445
theorem B3462911 : Blo 1024605 3462911 := bstep (se 1 (by rfl) ⟨2597183, by rfl⟩ : syracuseStep 3462911 = 5194367) B5194367
theorem B7788635 : Blo 1024605 7788635 := bstep (se 1 (by rfl) ⟨5841476, by rfl⟩ : syracuseStep 7788635 = 11682953) B11682953
theorem B3463721 : Blo 1024605 3463721 := bstep (se 2 (by rfl) ⟨1298895, by rfl⟩ : syracuseStep 3463721 = 2597791) B2597791
theorem B7888225 : Blo 1024605 7888225 := bstep (se 2 (by rfl) ⟨2958084, by rfl⟩ : syracuseStep 7888225 = 5916169) B5916169
theorem B3466799 : Blo 1024605 3466799 := bstep (se 1 (by rfl) ⟨2600099, by rfl⟩ : syracuseStep 3466799 = 5200199) B5200199
theorem B6580865 : Blo 1024605 6580865 := bstep (se 2 (by rfl) ⟨2467824, by rfl⟩ : syracuseStep 6580865 = 4935649) B4935649
theorem B3468797 : Blo 1024605 3468797 := bstep (se 3 (by rfl) ⟨650399, by rfl⟩ : syracuseStep 3468797 = 1300799) B1300799
theorem B3698855 : Blo 1024605 3698855 := bstep (se 1 (by rfl) ⟨2774141, by rfl⟩ : syracuseStep 3698855 = 5548283) B5548283
theorem B1733447 : Blo 1024605 1733447 := bstep (se 1 (by rfl) ⟨1300085, by rfl⟩ : syracuseStep 1733447 = 2600171) B2600171
theorem B1537259 : Blo 1024605 1537259 := bstep (se 1 (by rfl) ⟨1152944, by rfl⟩ : syracuseStep 1537259 = 2305889) B2305889
theorem B5273119 : Blo 1024605 5273119 := bstep (se 1 (by rfl) ⟨3954839, by rfl⟩ : syracuseStep 5273119 = 7909679) B7909679
theorem B3700367 : Blo 1024605 3700367 := bstep (se 1 (by rfl) ⟨2775275, by rfl⟩ : syracuseStep 3700367 = 5550551) B5550551
theorem B1538939 : Blo 1024605 1538939 := bstep (se 1 (by rfl) ⟨1154204, by rfl⟩ : syracuseStep 1538939 = 2308409) B2308409
theorem B7797869 : Blo 1024605 7797869 := bstep (se 3 (by rfl) ⟨1462100, by rfl⟩ : syracuseStep 7797869 = 2924201) B2924201
theorem B56098169 : Blo 1024605 56098169 := bstep (se 2 (by rfl) ⟨21036813, by rfl⟩ : syracuseStep 56098169 = 42073627) B42073627
theorem B61735961 : Blo 1024605 61735961 := bstep (se 2 (by rfl) ⟨23150985, by rfl⟩ : syracuseStep 61735961 = 46301971) B46301971
theorem B63308951 : Blo 1024605 63308951 := bstep (se 1 (by rfl) ⟨47481713, by rfl⟩ : syracuseStep 63308951 = 94963427) B94963427
theorem B6587963 : Blo 1024605 6587963 := bstep (se 1 (by rfl) ⟨4940972, by rfl⟩ : syracuseStep 6587963 = 9881945) B9881945
theorem B13176539 : Blo 1024605 13176539 := bstep (se 1 (by rfl) ⟨9882404, by rfl⟩ : syracuseStep 13176539 = 19764809) B19764809
theorem B66525623 : Blo 1024605 66525623 := bstep (se 1 (by rfl) ⟨49894217, by rfl⟩ : syracuseStep 66525623 = 99788435) B99788435
theorem B227908673 : Blo 1024605 227908673 := bstep (se 2 (by rfl) ⟨85465752, by rfl⟩ : syracuseStep 227908673 = 170931505) B170931505
theorem B7806617 : Blo 1024605 7806617 := bstep (se 2 (by rfl) ⟨2927481, by rfl⟩ : syracuseStep 7806617 = 5854963) B5854963
theorem B2465903 : Blo 1024605 2465903 := bstep (se 1 (by rfl) ⟨1849427, by rfl⟩ : syracuseStep 2465903 = 3698855) B3698855
theorem B28123301 : Blo 1024605 28123301 := bstep (se 4 (by rfl) ⟨2636559, by rfl⟩ : syracuseStep 28123301 = 5273119) B5273119
theorem B1155631 : Blo 1024605 1155631 := bstep (se 1 (by rfl) ⟨866723, by rfl⟩ : syracuseStep 1155631 = 1733447) B1733447
theorem B1024839 : Blo 1024605 1024839 := bstep (se 1 (by rfl) ⟨768629, by rfl⟩ : syracuseStep 1024839 = 1537259) B1537259
theorem B2466911 : Blo 1024605 2466911 := bstep (se 1 (by rfl) ⟨1850183, by rfl⟩ : syracuseStep 2466911 = 3700367) B3700367
theorem B1025959 : Blo 1024605 1025959 := bstep (se 1 (by rfl) ⟨769469, by rfl⟩ : syracuseStep 1025959 = 1538939) B1538939
theorem B37398779 : Blo 1024605 37398779 := bstep (se 1 (by rfl) ⟨28049084, by rfl⟩ : syracuseStep 37398779 = 56098169) B56098169
theorem B2600009 : Blo 1024605 2600009 := bstep (se 2 (by rfl) ⟨975003, by rfl⟩ : syracuseStep 2600009 = 1950007) B1950007
theorem B1027175 : Blo 1024605 1027175 := bstep (se 1 (by rfl) ⟨770381, by rfl⟩ : syracuseStep 1027175 = 1540763) B1540763
theorem B1027311 : Blo 1024605 1027311 := bstep (se 1 (by rfl) ⟨770483, by rfl⟩ : syracuseStep 1027311 = 1540967) B1540967
theorem B1027535 : Blo 1024605 1027535 := bstep (se 1 (by rfl) ⟨770651, by rfl⟩ : syracuseStep 1027535 = 1541303) B1541303
theorem B1028591 : Blo 1024605 1028591 := bstep (se 1 (by rfl) ⟨771443, by rfl⟩ : syracuseStep 1028591 = 1542887) B1542887
theorem B7616687 : Blo 1024605 7616687 := bstep (se 1 (by rfl) ⟨5712515, by rfl⟩ : syracuseStep 7616687 = 11425031) B11425031
theorem B2308607 : Blo 1024605 2308607 := bstep (se 1 (by rfl) ⟨1731455, by rfl⟩ : syracuseStep 2308607 = 3462911) B3462911
theorem B2603603 : Blo 1024605 2603603 := bstep (se 1 (by rfl) ⟨1952702, by rfl⟩ : syracuseStep 2603603 = 3905405) B3905405
theorem B5192423 : Blo 1024605 5192423 := bstep (se 1 (by rfl) ⟨3894317, by rfl⟩ : syracuseStep 5192423 = 7788635) B7788635
theorem B8764199 : Blo 1024605 8764199 := bstep (se 1 (by rfl) ⟨6573149, by rfl⟩ : syracuseStep 8764199 = 13146299) B13146299
theorem B2309147 : Blo 1024605 2309147 := bstep (se 1 (by rfl) ⟨1731860, by rfl⟩ : syracuseStep 2309147 = 3463721) B3463721
theorem B4440191 : Blo 1024605 4440191 := bstep (se 1 (by rfl) ⟨3330143, by rfl⟩ : syracuseStep 4440191 = 6660287) B6660287
theorem B7783289 : Blo 1024605 7783289 := bstep (se 2 (by rfl) ⟨2918733, by rfl⟩ : syracuseStep 7783289 = 5837467) B5837467
theorem B2311199 : Blo 1024605 2311199 := bstep (se 1 (by rfl) ⟨1733399, by rfl⟩ : syracuseStep 2311199 = 3466799) B3466799
theorem B17548487 : Blo 1024605 17548487 := bstep (se 1 (by rfl) ⟨13161365, by rfl⟩ : syracuseStep 17548487 = 26322731) B26322731
theorem B1563412079 : Blo 1024605 1563412079 := bstep (se 1 (by rfl) ⟨1172559059, by rfl⟩ : syracuseStep 1563412079 = 2345118119) B2345118119
theorem B2312531 : Blo 1024605 2312531 := bstep (se 1 (by rfl) ⟨1734398, by rfl⟩ : syracuseStep 2312531 = 3468797) B3468797
theorem B1952255 : Blo 1024605 1952255 := bstep (se 1 (by rfl) ⟨1464191, by rfl⟩ : syracuseStep 1952255 = 2928383) B2928383
theorem B16895141 : Blo 1024605 16895141 := bstep (se 4 (by rfl) ⟨1583919, by rfl⟩ : syracuseStep 16895141 = 3167839) B3167839
theorem B7393351 : Blo 1024605 7393351 := bstep (se 1 (by rfl) ⟨5545013, by rfl⟩ : syracuseStep 7393351 = 11090027) B11090027
theorem B5198579 : Blo 1024605 5198579 := bstep (se 1 (by rfl) ⟨3898934, by rfl⟩ : syracuseStep 5198579 = 7797869) B7797869
theorem B28530089 : Blo 1024605 28530089 := bstep (se 2 (by rfl) ⟨10698783, by rfl⟩ : syracuseStep 28530089 = 21397567) B21397567
theorem B4380151 : Blo 1024605 4380151 := bstep (se 1 (by rfl) ⟨3285113, by rfl⟩ : syracuseStep 4380151 = 6570227) B6570227
theorem B4937897 : Blo 1024605 4937897 := bstep (se 2 (by rfl) ⟨1851711, by rfl⟩ : syracuseStep 4937897 = 3703423) B3703423
theorem B3464531 : Blo 1024605 3464531 := bstep (se 1 (by rfl) ⟨2598398, by rfl⟩ : syracuseStep 3464531 = 5196797) B5196797
theorem B3464639 : Blo 1024605 3464639 := bstep (se 1 (by rfl) ⟨2598479, by rfl⟩ : syracuseStep 3464639 = 5196959) B5196959
theorem B4942433 : Blo 1024605 4942433 := bstep (se 2 (by rfl) ⟨1853412, by rfl⟩ : syracuseStep 4942433 = 3706825) B3706825
theorem B1731577 : Blo 1024605 1731577 := bstep (se 2 (by rfl) ⟨649341, by rfl⟩ : syracuseStep 1731577 = 1298683) B1298683
theorem B3894911 : Blo 1024605 3894911 := bstep (se 1 (by rfl) ⟨2921183, by rfl⟩ : syracuseStep 3894911 = 5842367) B5842367
theorem B4387243 : Blo 1024605 4387243 := bstep (se 1 (by rfl) ⟨3290432, by rfl⟩ : syracuseStep 4387243 = 6580865) B6580865
theorem B1537247 : Blo 1024605 1537247 := bstep (se 1 (by rfl) ⟨1152935, by rfl⟩ : syracuseStep 1537247 = 2305871) B2305871
theorem B3897341 : Blo 1024605 3897341 := bstep (se 3 (by rfl) ⟨730751, by rfl⟩ : syracuseStep 3897341 = 1461503) B1461503
theorem B1538459 : Blo 1024605 1538459 := bstep (se 1 (by rfl) ⟨1153844, by rfl⟩ : syracuseStep 1538459 = 2307689) B2307689
theorem B10517633 : Blo 1024605 10517633 := bstep (se 2 (by rfl) ⟨3944112, by rfl⟩ : syracuseStep 10517633 = 7888225) B7888225
theorem B1539419 : Blo 1024605 1539419 := bstep (se 1 (by rfl) ⟨1154564, by rfl⟩ : syracuseStep 1539419 = 2309129) B2309129
theorem B4390301 : Blo 1024605 4390301 := bstep (se 3 (by rfl) ⟨823181, by rfl⟩ : syracuseStep 4390301 = 1646363) B1646363
theorem B41157307 : Blo 1024605 41157307 := bstep (se 1 (by rfl) ⟨30867980, by rfl⟩ : syracuseStep 41157307 = 61735961) B61735961
theorem B1540799 : Blo 1024605 1540799 := bstep (se 1 (by rfl) ⟨1155599, by rfl⟩ : syracuseStep 1540799 = 2311199) B2311199
theorem B1540841 : Blo 1024605 1540841 := bstep (se 2 (by rfl) ⟨577815, by rfl⟩ : syracuseStep 1540841 = 1155631) B1155631
theorem B42205967 : Blo 1024605 42205967 := bstep (se 1 (by rfl) ⟨31654475, by rfl⟩ : syracuseStep 42205967 = 63308951) B63308951
theorem B11698991 : Blo 1024605 11698991 := bstep (se 1 (by rfl) ⟨8774243, by rfl⟩ : syracuseStep 11698991 = 17548487) B17548487
theorem B4391975 : Blo 1024605 4391975 := bstep (se 1 (by rfl) ⟨3293981, by rfl⟩ : syracuseStep 4391975 = 6587963) B6587963
theorem B1541687 : Blo 1024605 1541687 := bstep (se 1 (by rfl) ⟨1156265, by rfl⟩ : syracuseStep 1541687 = 2312531) B2312531
theorem B8784359 : Blo 1024605 8784359 := bstep (se 1 (by rfl) ⟨6588269, by rfl⟩ : syracuseStep 8784359 = 13176539) B13176539
theorem B18748867 : Blo 1024605 18748867 := bstep (se 1 (by rfl) ⟨14061650, by rfl⟩ : syracuseStep 18748867 = 28123301) B28123301
theorem B1644607 : Blo 1024605 1644607 := bstep (se 1 (by rfl) ⟨1233455, by rfl⟩ : syracuseStep 1644607 = 2466911) B2466911
theorem B5840201 : Blo 1024605 5840201 := bstep (se 2 (by rfl) ⟨2190075, by rfl⟩ : syracuseStep 5840201 = 4380151) B4380151
theorem B2596607 : Blo 1024605 2596607 := bstep (se 1 (by rfl) ⟨1947455, by rfl⟩ : syracuseStep 2596607 = 3894911) B3894911
theorem B1024831 : Blo 1024605 1024831 := bstep (se 1 (by rfl) ⟨768623, by rfl⟩ : syracuseStep 1024831 = 1537247) B1537247
theorem B2598227 : Blo 1024605 2598227 := bstep (se 1 (by rfl) ⟨1948670, by rfl⟩ : syracuseStep 2598227 = 3897341) B3897341
theorem B1025639 : Blo 1024605 1025639 := bstep (se 1 (by rfl) ⟨769229, by rfl⟩ : syracuseStep 1025639 = 1538459) B1538459
theorem B5842799 : Blo 1024605 5842799 := bstep (se 1 (by rfl) ⟨4382099, by rfl⟩ : syracuseStep 5842799 = 8764199) B8764199
theorem B1026279 : Blo 1024605 1026279 := bstep (se 1 (by rfl) ⟨769709, by rfl⟩ : syracuseStep 1026279 = 1539419) B1539419
theorem B2926867 : Blo 1024605 2926867 := bstep (se 1 (by rfl) ⟨2195150, by rfl⟩ : syracuseStep 2926867 = 4390301) B4390301
theorem B11840509 : Blo 1024605 11840509 := bstep (se 3 (by rfl) ⟨2220095, by rfl⟩ : syracuseStep 11840509 = 4440191) B4440191
theorem B5188859 : Blo 1024605 5188859 := bstep (se 1 (by rfl) ⟨3891644, by rfl⟩ : syracuseStep 5188859 = 7783289) B7783289
theorem B19020059 : Blo 1024605 19020059 := bstep (se 1 (by rfl) ⟨14265044, by rfl⟩ : syracuseStep 19020059 = 28530089) B28530089
theorem B2308769 : Blo 1024605 2308769 := bstep (se 2 (by rfl) ⟨865788, by rfl⟩ : syracuseStep 2308769 = 1731577) B1731577
theorem B3291931 : Blo 1024605 3291931 := bstep (se 1 (by rfl) ⟨2468948, by rfl⟩ : syracuseStep 3291931 = 4937897) B4937897
theorem B44350415 : Blo 1024605 44350415 := bstep (se 1 (by rfl) ⟨33262811, by rfl⟩ : syracuseStep 44350415 = 66525623) B66525623
theorem B2309687 : Blo 1024605 2309687 := bstep (se 1 (by rfl) ⟨1732265, by rfl⟩ : syracuseStep 2309687 = 3464531) B3464531
theorem B2309759 : Blo 1024605 2309759 := bstep (se 1 (by rfl) ⟨1732319, by rfl⟩ : syracuseStep 2309759 = 3464639) B3464639
theorem B5849657 : Blo 1024605 5849657 := bstep (se 2 (by rfl) ⟨2193621, by rfl⟩ : syracuseStep 5849657 = 4387243) B4387243
theorem B3294955 : Blo 1024605 3294955 := bstep (se 1 (by rfl) ⟨2471216, by rfl⟩ : syracuseStep 3294955 = 4942433) B4942433
theorem B3461615 : Blo 1024605 3461615 := bstep (se 1 (by rfl) ⟨2596211, by rfl⟩ : syracuseStep 3461615 = 5192423) B5192423
theorem B6575741 : Blo 1024605 6575741 := bstep (se 3 (by rfl) ⟨1232951, by rfl⟩ : syracuseStep 6575741 = 2465903) B2465903
theorem B1042274719 : Blo 1024605 1042274719 := bstep (se 1 (by rfl) ⟨781706039, by rfl⟩ : syracuseStep 1042274719 = 1563412079) B1563412079
theorem B1301503 : Blo 1024605 1301503 := bstep (se 1 (by rfl) ⟨976127, by rfl⟩ : syracuseStep 1301503 = 1952255) B1952255
theorem B11263427 : Blo 1024605 11263427 := bstep (se 1 (by rfl) ⟨8447570, by rfl⟩ : syracuseStep 11263427 = 16895141) B16895141
theorem B3465719 : Blo 1024605 3465719 := bstep (se 1 (by rfl) ⟨2599289, by rfl⟩ : syracuseStep 3465719 = 5198579) B5198579
theorem B151939115 : Blo 1024605 151939115 := bstep (se 1 (by rfl) ⟨113954336, by rfl⟩ : syracuseStep 151939115 = 227908673) B227908673
theorem B5204411 : Blo 1024605 5204411 := bstep (se 1 (by rfl) ⟨3903308, by rfl⟩ : syracuseStep 5204411 = 7806617) B7806617
theorem B9857801 : Blo 1024605 9857801 := bstep (se 2 (by rfl) ⟨3696675, by rfl⟩ : syracuseStep 9857801 = 7393351) B7393351
theorem B20311165 : Blo 1024605 20311165 := bstep (se 3 (by rfl) ⟨3808343, by rfl⟩ : syracuseStep 20311165 = 7616687) B7616687
theorem B24932519 : Blo 1024605 24932519 := bstep (se 1 (by rfl) ⟨18699389, by rfl⟩ : syracuseStep 24932519 = 37398779) B37398779
theorem B1733339 : Blo 1024605 1733339 := bstep (se 1 (by rfl) ⟨1300004, by rfl⟩ : syracuseStep 1733339 = 2600009) B2600009
theorem B1539071 : Blo 1024605 1539071 := bstep (se 1 (by rfl) ⟨1154303, by rfl⟩ : syracuseStep 1539071 = 2308607) B2308607
theorem B1735735 : Blo 1024605 1735735 := bstep (se 1 (by rfl) ⟨1301801, by rfl⟩ : syracuseStep 1735735 = 2603603) B2603603
theorem B1539431 : Blo 1024605 1539431 := bstep (se 1 (by rfl) ⟨1154573, by rfl⟩ : syracuseStep 1539431 = 2309147) B2309147
theorem B7011755 : Blo 1024605 7011755 := bstep (se 1 (by rfl) ⟨5258816, by rfl⟩ : syracuseStep 7011755 = 10517633) B10517633
theorem B3899771 : Blo 1024605 3899771 := bstep (se 1 (by rfl) ⟨2924828, by rfl⟩ : syracuseStep 3899771 = 5849657) B5849657
theorem B7799327 : Blo 1024605 7799327 := bstep (se 1 (by rfl) ⟨5849495, by rfl⟩ : syracuseStep 7799327 = 11698991) B11698991
theorem B4393273 : Blo 1024605 4393273 := bstep (se 2 (by rfl) ⟨1647477, by rfl⟩ : syracuseStep 4393273 = 3294955) B3294955
theorem B3902489 : Blo 1024605 3902489 := bstep (se 2 (by rfl) ⟨1463433, by rfl⟩ : syracuseStep 3902489 = 2926867) B2926867
theorem B7508951 : Blo 1024605 7508951 := bstep (se 1 (by rfl) ⟨5631713, by rfl⟩ : syracuseStep 7508951 = 11263427) B11263427
theorem B101292743 : Blo 1024605 101292743 := bstep (se 1 (by rfl) ⟨75969557, by rfl⟩ : syracuseStep 101292743 = 151939115) B151939115
theorem B16621679 : Blo 1024605 16621679 := bstep (se 1 (by rfl) ⟨12466259, by rfl⟩ : syracuseStep 16621679 = 24932519) B24932519
theorem B1155559 : Blo 1024605 1155559 := bstep (se 1 (by rfl) ⟨866669, by rfl⟩ : syracuseStep 1155559 = 1733339) B1733339
theorem B1389699625 : Blo 1024605 1389699625 := bstep (se 2 (by rfl) ⟨521137359, by rfl⟩ : syracuseStep 1389699625 = 1042274719) B1042274719
theorem B29566943 : Blo 1024605 29566943 := bstep (se 1 (by rfl) ⟨22175207, by rfl⟩ : syracuseStep 29566943 = 44350415) B44350415
theorem B1026047 : Blo 1024605 1026047 := bstep (se 1 (by rfl) ⟨769535, by rfl⟩ : syracuseStep 1026047 = 1539071) B1539071
theorem B1026287 : Blo 1024605 1026287 := bstep (se 1 (by rfl) ⟨769715, by rfl⟩ : syracuseStep 1026287 = 1539431) B1539431
theorem B1027199 : Blo 1024605 1027199 := bstep (se 1 (by rfl) ⟨770399, by rfl⟩ : syracuseStep 1027199 = 1540799) B1540799
theorem B1027227 : Blo 1024605 1027227 := bstep (se 1 (by rfl) ⟨770420, by rfl⟩ : syracuseStep 1027227 = 1540841) B1540841
theorem B2927983 : Blo 1024605 2927983 := bstep (se 1 (by rfl) ⟨2195987, by rfl⟩ : syracuseStep 2927983 = 4391975) B4391975
theorem B1027791 : Blo 1024605 1027791 := bstep (se 1 (by rfl) ⟨770843, by rfl⟩ : syracuseStep 1027791 = 1541687) B1541687
theorem B2307743 : Blo 1024605 2307743 := bstep (se 1 (by rfl) ⟨1730807, by rfl⟩ : syracuseStep 2307743 = 3461615) B3461615
theorem B27081553 : Blo 1024605 27081553 := bstep (se 2 (by rfl) ⟨10155582, by rfl⟩ : syracuseStep 27081553 = 20311165) B20311165
theorem B2310479 : Blo 1024605 2310479 := bstep (se 1 (by rfl) ⟨1732859, by rfl⟩ : syracuseStep 2310479 = 3465719) B3465719
theorem B6571867 : Blo 1024605 6571867 := bstep (se 1 (by rfl) ⟨4928900, by rfl⟩ : syracuseStep 6571867 = 9857801) B9857801
theorem B3459239 : Blo 1024605 3459239 := bstep (se 1 (by rfl) ⟨2594429, by rfl⟩ : syracuseStep 3459239 = 5188859) B5188859
theorem B2314313 : Blo 1024605 2314313 := bstep (se 2 (by rfl) ⟨867867, by rfl⟩ : syracuseStep 2314313 = 1735735) B1735735
theorem B4674503 : Blo 1024605 4674503 := bstep (se 1 (by rfl) ⟨3505877, by rfl⟩ : syracuseStep 4674503 = 7011755) B7011755
theorem B8771237 : Blo 1024605 8771237 := bstep (se 4 (by rfl) ⟨822303, by rfl⟩ : syracuseStep 8771237 = 1644607) B1644607
theorem B28137311 : Blo 1024605 28137311 := bstep (se 1 (by rfl) ⟨21102983, by rfl⟩ : syracuseStep 28137311 = 42205967) B42205967
theorem B54876409 : Blo 1024605 54876409 := bstep (se 2 (by rfl) ⟨20578653, by rfl⟩ : syracuseStep 54876409 = 41157307) B41157307
theorem B5856239 : Blo 1024605 5856239 := bstep (se 1 (by rfl) ⟨4392179, by rfl⟩ : syracuseStep 5856239 = 8784359) B8784359
theorem B4383827 : Blo 1024605 4383827 := bstep (se 1 (by rfl) ⟨3287870, by rfl⟩ : syracuseStep 4383827 = 6575741) B6575741
theorem B15787345 : Blo 1024605 15787345 := bstep (se 2 (by rfl) ⟨5920254, by rfl⟩ : syracuseStep 15787345 = 11840509) B11840509
theorem B3893467 : Blo 1024605 3893467 := bstep (se 1 (by rfl) ⟨2920100, by rfl⟩ : syracuseStep 3893467 = 5840201) B5840201
theorem B1731071 : Blo 1024605 1731071 := bstep (se 1 (by rfl) ⟨1298303, by rfl⟩ : syracuseStep 1731071 = 2596607) B2596607
theorem B1732151 : Blo 1024605 1732151 := bstep (se 1 (by rfl) ⟨1299113, by rfl⟩ : syracuseStep 1732151 = 2598227) B2598227
theorem B3895199 : Blo 1024605 3895199 := bstep (se 1 (by rfl) ⟨2921399, by rfl⟩ : syracuseStep 3895199 = 5842799) B5842799
theorem B3469607 : Blo 1024605 3469607 := bstep (se 1 (by rfl) ⟨2602205, by rfl⟩ : syracuseStep 3469607 = 5204411) B5204411
theorem B24998489 : Blo 1024605 24998489 := bstep (se 2 (by rfl) ⟨9374433, by rfl⟩ : syracuseStep 24998489 = 18748867) B18748867
theorem B4389241 : Blo 1024605 4389241 := bstep (se 2 (by rfl) ⟨1645965, by rfl⟩ : syracuseStep 4389241 = 3291931) B3291931
theorem B1735337 : Blo 1024605 1735337 := bstep (se 2 (by rfl) ⟨650751, by rfl⟩ : syracuseStep 1735337 = 1301503) B1301503
theorem B12680039 : Blo 1024605 12680039 := bstep (se 1 (by rfl) ⟨9510029, by rfl⟩ : syracuseStep 12680039 = 19020059) B19020059
theorem B1539179 : Blo 1024605 1539179 := bstep (se 1 (by rfl) ⟨1154384, by rfl⟩ : syracuseStep 1539179 = 2308769) B2308769
theorem B1539791 : Blo 1024605 1539791 := bstep (se 1 (by rfl) ⟨1154843, by rfl⟩ : syracuseStep 1539791 = 2309687) B2309687
theorem B1539839 : Blo 1024605 1539839 := bstep (se 1 (by rfl) ⟨1154879, by rfl⟩ : syracuseStep 1539839 = 2309759) B2309759
theorem B1540319 : Blo 1024605 1540319 := bstep (se 1 (by rfl) ⟨1155239, by rfl⟩ : syracuseStep 1540319 = 2310479) B2310479
theorem B1540745 : Blo 1024605 1540745 := bstep (se 2 (by rfl) ⟨577779, by rfl⟩ : syracuseStep 1540745 = 1155559) B1155559
theorem B1852932833 : Blo 1024605 1852932833 := bstep (se 2 (by rfl) ⟨694849812, by rfl⟩ : syracuseStep 1852932833 = 1389699625) B1389699625
theorem B1542875 : Blo 1024605 1542875 := bstep (se 1 (by rfl) ⟨1157156, by rfl⟩ : syracuseStep 1542875 = 2314313) B2314313
theorem B3116335 : Blo 1024605 3116335 := bstep (se 1 (by rfl) ⟨2337251, by rfl⟩ : syracuseStep 3116335 = 4674503) B4674503
theorem B3903977 : Blo 1024605 3903977 := bstep (se 2 (by rfl) ⟨1463991, by rfl⟩ : syracuseStep 3903977 = 2927983) B2927983
theorem B3904159 : Blo 1024605 3904159 := bstep (se 1 (by rfl) ⟨2928119, by rfl⟩ : syracuseStep 3904159 = 5856239) B5856239
theorem B11081119 : Blo 1024605 11081119 := bstep (se 1 (by rfl) ⟨8310839, by rfl⟩ : syracuseStep 11081119 = 16621679) B16621679
theorem B2922551 : Blo 1024605 2922551 := bstep (se 1 (by rfl) ⟨2191913, by rfl⟩ : syracuseStep 2922551 = 4383827) B4383827
theorem B1154047 : Blo 1024605 1154047 := bstep (se 1 (by rfl) ⟨865535, by rfl⟩ : syracuseStep 1154047 = 1731071) B1731071
theorem B1154767 : Blo 1024605 1154767 := bstep (se 1 (by rfl) ⟨866075, by rfl⟩ : syracuseStep 1154767 = 1732151) B1732151
theorem B2596799 : Blo 1024605 2596799 := bstep (se 1 (by rfl) ⟨1947599, by rfl⟩ : syracuseStep 2596799 = 3895199) B3895199
theorem B1156891 : Blo 1024605 1156891 := bstep (se 1 (by rfl) ⟨867668, by rfl⟩ : syracuseStep 1156891 = 1735337) B1735337
theorem B1026119 : Blo 1024605 1026119 := bstep (se 1 (by rfl) ⟨769589, by rfl⟩ : syracuseStep 1026119 = 1539179) B1539179
theorem B1026527 : Blo 1024605 1026527 := bstep (se 1 (by rfl) ⟨769895, by rfl⟩ : syracuseStep 1026527 = 1539791) B1539791
theorem B1026559 : Blo 1024605 1026559 := bstep (se 1 (by rfl) ⟨769919, by rfl⟩ : syracuseStep 1026559 = 1539839) B1539839
theorem B2599847 : Blo 1024605 2599847 := bstep (se 1 (by rfl) ⟨1949885, by rfl⟩ : syracuseStep 2599847 = 3899771) B3899771
theorem B2306159 : Blo 1024605 2306159 := bstep (se 1 (by rfl) ⟨1729619, by rfl⟩ : syracuseStep 2306159 = 3459239) B3459239
theorem B21049793 : Blo 1024605 21049793 := bstep (se 2 (by rfl) ⟨7893672, by rfl⟩ : syracuseStep 21049793 = 15787345) B15787345
theorem B2601659 : Blo 1024605 2601659 := bstep (se 1 (by rfl) ⟨1951244, by rfl⟩ : syracuseStep 2601659 = 3902489) B3902489
theorem B8762489 : Blo 1024605 8762489 := bstep (se 2 (by rfl) ⟨3285933, by rfl⟩ : syracuseStep 8762489 = 6571867) B6571867
theorem B5191289 : Blo 1024605 5191289 := bstep (se 2 (by rfl) ⟨1946733, by rfl⟩ : syracuseStep 5191289 = 3893467) B3893467
theorem B5847491 : Blo 1024605 5847491 := bstep (se 1 (by rfl) ⟨4385618, by rfl⟩ : syracuseStep 5847491 = 8771237) B8771237
theorem B18758207 : Blo 1024605 18758207 := bstep (se 1 (by rfl) ⟨14068655, by rfl⟩ : syracuseStep 18758207 = 28137311) B28137311
theorem B19711295 : Blo 1024605 19711295 := bstep (se 1 (by rfl) ⟨14783471, by rfl⟩ : syracuseStep 19711295 = 29566943) B29566943
theorem B2313071 : Blo 1024605 2313071 := bstep (se 1 (by rfl) ⟨1734803, by rfl⟩ : syracuseStep 2313071 = 3469607) B3469607
theorem B16665659 : Blo 1024605 16665659 := bstep (se 1 (by rfl) ⟨12499244, by rfl⟩ : syracuseStep 16665659 = 24998489) B24998489
theorem B5852321 : Blo 1024605 5852321 := bstep (se 2 (by rfl) ⟨2194620, by rfl⟩ : syracuseStep 5852321 = 4389241) B4389241
theorem B5199551 : Blo 1024605 5199551 := bstep (se 1 (by rfl) ⟨3899663, by rfl⟩ : syracuseStep 5199551 = 7799327) B7799327
theorem B292674181 : Blo 1024605 292674181 := bstep (se 4 (by rfl) ⟨27438204, by rfl⟩ : syracuseStep 292674181 = 54876409) B54876409
theorem B5857697 : Blo 1024605 5857697 := bstep (se 2 (by rfl) ⟨2196636, by rfl⟩ : syracuseStep 5857697 = 4393273) B4393273
theorem B5005967 : Blo 1024605 5005967 := bstep (se 1 (by rfl) ⟨3754475, by rfl⟩ : syracuseStep 5005967 = 7508951) B7508951
theorem B67528495 : Blo 1024605 67528495 := bstep (se 1 (by rfl) ⟨50646371, by rfl⟩ : syracuseStep 67528495 = 101292743) B101292743
theorem B1538495 : Blo 1024605 1538495 := bstep (se 1 (by rfl) ⟨1153871, by rfl⟩ : syracuseStep 1538495 = 2307743) B2307743
theorem B36108737 : Blo 1024605 36108737 := bstep (se 2 (by rfl) ⟨13540776, by rfl⟩ : syracuseStep 36108737 = 27081553) B27081553
theorem B8453359 : Blo 1024605 8453359 := bstep (se 1 (by rfl) ⟨6340019, by rfl⟩ : syracuseStep 8453359 = 12680039) B12680039
theorem B1235288555 : Blo 1024605 1235288555 := bstep (se 1 (by rfl) ⟨926466416, by rfl⟩ : syracuseStep 1235288555 = 1852932833) B1852932833
theorem B13140863 : Blo 1024605 13140863 := bstep (se 1 (by rfl) ⟨9855647, by rfl⟩ : syracuseStep 13140863 = 19711295) B19711295
theorem B1542047 : Blo 1024605 1542047 := bstep (se 1 (by rfl) ⟨1156535, by rfl⟩ : syracuseStep 1542047 = 2313071) B2313071
theorem B11110439 : Blo 1024605 11110439 := bstep (se 1 (by rfl) ⟨8332829, by rfl⟩ : syracuseStep 11110439 = 16665659) B16665659
theorem B3901547 : Blo 1024605 3901547 := bstep (se 1 (by rfl) ⟨2926160, by rfl⟩ : syracuseStep 3901547 = 5852321) B5852321
theorem B1542521 : Blo 1024605 1542521 := bstep (se 2 (by rfl) ⟨578445, by rfl⟩ : syracuseStep 1542521 = 1156891) B1156891
theorem B3905131 : Blo 1024605 3905131 := bstep (se 1 (by rfl) ⟨2928848, by rfl⟩ : syracuseStep 3905131 = 5857697) B5857697
theorem B14033195 : Blo 1024605 14033195 := bstep (se 1 (by rfl) ⟨10524896, by rfl⟩ : syracuseStep 14033195 = 21049793) B21049793
theorem B5841659 : Blo 1024605 5841659 := bstep (se 1 (by rfl) ⟨4381244, by rfl⟩ : syracuseStep 5841659 = 8762489) B8762489
theorem B1025663 : Blo 1024605 1025663 := bstep (se 1 (by rfl) ⟨769247, by rfl⟩ : syracuseStep 1025663 = 1538495) B1538495
theorem B1026879 : Blo 1024605 1026879 := bstep (se 1 (by rfl) ⟨770159, by rfl⟩ : syracuseStep 1026879 = 1540319) B1540319
theorem B1027163 : Blo 1024605 1027163 := bstep (se 1 (by rfl) ⟨770372, by rfl⟩ : syracuseStep 1027163 = 1540745) B1540745
theorem B1028583 : Blo 1024605 1028583 := bstep (se 1 (by rfl) ⟨771437, by rfl⟩ : syracuseStep 1028583 = 1542875) B1542875
theorem B2602651 : Blo 1024605 2602651 := bstep (se 1 (by rfl) ⟨1951988, by rfl⟩ : syracuseStep 2602651 = 3903977) B3903977
theorem B1948367 : Blo 1024605 1948367 := bstep (se 1 (by rfl) ⟨1461275, by rfl⟩ : syracuseStep 1948367 = 2922551) B2922551
theorem B53396981 : Blo 1024605 53396981 := bstep (se 5 (by rfl) ⟨2502983, by rfl⟩ : syracuseStep 53396981 = 5005967) B5005967
theorem B3460859 : Blo 1024605 3460859 := bstep (se 1 (by rfl) ⟨2595644, by rfl⟩ : syracuseStep 3460859 = 5191289) B5191289
theorem B24072491 : Blo 1024605 24072491 := bstep (se 1 (by rfl) ⟨18054368, by rfl⟩ : syracuseStep 24072491 = 36108737) B36108737
theorem B12505471 : Blo 1024605 12505471 := bstep (se 1 (by rfl) ⟨9379103, by rfl⟩ : syracuseStep 12505471 = 18758207) B18758207
theorem B90037993 : Blo 1024605 90037993 := bstep (se 2 (by rfl) ⟨33764247, by rfl⟩ : syracuseStep 90037993 = 67528495) B67528495
theorem B3466367 : Blo 1024605 3466367 := bstep (se 1 (by rfl) ⟨2599775, by rfl⟩ : syracuseStep 3466367 = 5199551) B5199551
theorem B4155113 : Blo 1024605 4155113 := bstep (se 2 (by rfl) ⟨1558167, by rfl⟩ : syracuseStep 4155113 = 3116335) B3116335
theorem B1731199 : Blo 1024605 1731199 := bstep (se 1 (by rfl) ⟨1298399, by rfl⟩ : syracuseStep 1731199 = 2596799) B2596799
theorem B5205545 : Blo 1024605 5205545 := bstep (se 2 (by rfl) ⟨1952079, by rfl⟩ : syracuseStep 5205545 = 3904159) B3904159
theorem B14774825 : Blo 1024605 14774825 := bstep (se 2 (by rfl) ⟨5540559, by rfl⟩ : syracuseStep 14774825 = 11081119) B11081119
theorem B1733231 : Blo 1024605 1733231 := bstep (se 1 (by rfl) ⟨1299923, by rfl⟩ : syracuseStep 1733231 = 2599847) B2599847
theorem B1537439 : Blo 1024605 1537439 := bstep (se 1 (by rfl) ⟨1153079, by rfl⟩ : syracuseStep 1537439 = 2306159) B2306159
theorem B1734439 : Blo 1024605 1734439 := bstep (se 1 (by rfl) ⟨1300829, by rfl⟩ : syracuseStep 1734439 = 2601659) B2601659
theorem B390232241 : Blo 1024605 390232241 := bstep (se 2 (by rfl) ⟨146337090, by rfl⟩ : syracuseStep 390232241 = 292674181) B292674181
theorem B1538729 : Blo 1024605 1538729 := bstep (se 2 (by rfl) ⟨577023, by rfl⟩ : syracuseStep 1538729 = 1154047) B1154047
theorem B3898327 : Blo 1024605 3898327 := bstep (se 1 (by rfl) ⟨2923745, by rfl⟩ : syracuseStep 3898327 = 5847491) B5847491
theorem B11271145 : Blo 1024605 11271145 := bstep (se 2 (by rfl) ⟨4226679, by rfl⟩ : syracuseStep 11271145 = 8453359) B8453359
theorem B1539689 : Blo 1024605 1539689 := bstep (se 2 (by rfl) ⟨577383, by rfl⟩ : syracuseStep 1539689 = 1154767) B1154767
theorem B823525703 : Blo 1024605 823525703 := bstep (se 1 (by rfl) ⟨617644277, by rfl⟩ : syracuseStep 823525703 = 1235288555) B1235288555
theorem B7406959 : Blo 1024605 7406959 := bstep (se 1 (by rfl) ⟨5555219, by rfl⟩ : syracuseStep 7406959 = 11110439) B11110439
theorem B1155487 : Blo 1024605 1155487 := bstep (se 1 (by rfl) ⟨866615, by rfl⟩ : syracuseStep 1155487 = 1733231) B1733231
theorem B1024959 : Blo 1024605 1024959 := bstep (se 1 (by rfl) ⟨768719, by rfl⟩ : syracuseStep 1024959 = 1537439) B1537439
theorem B260154827 : Blo 1024605 260154827 := bstep (se 1 (by rfl) ⟨195116120, by rfl⟩ : syracuseStep 260154827 = 390232241) B390232241
theorem B1025819 : Blo 1024605 1025819 := bstep (se 1 (by rfl) ⟨769364, by rfl⟩ : syracuseStep 1025819 = 1538729) B1538729
theorem B1026459 : Blo 1024605 1026459 := bstep (se 1 (by rfl) ⟨769844, by rfl⟩ : syracuseStep 1026459 = 1539689) B1539689
theorem B8760575 : Blo 1024605 8760575 := bstep (se 1 (by rfl) ⟨6570431, by rfl⟩ : syracuseStep 8760575 = 13140863) B13140863
theorem B35597987 : Blo 1024605 35597987 := bstep (se 1 (by rfl) ⟨26698490, by rfl⟩ : syracuseStep 35597987 = 53396981) B53396981
theorem B1028031 : Blo 1024605 1028031 := bstep (se 1 (by rfl) ⟨771023, by rfl⟩ : syracuseStep 1028031 = 1542047) B1542047
theorem B2601031 : Blo 1024605 2601031 := bstep (se 1 (by rfl) ⟨1950773, by rfl⟩ : syracuseStep 2601031 = 3901547) B3901547
theorem B1028347 : Blo 1024605 1028347 := bstep (se 1 (by rfl) ⟨771260, by rfl⟩ : syracuseStep 1028347 = 1542521) B1542521
theorem B66695845 : Blo 1024605 66695845 := bstep (se 4 (by rfl) ⟨6252735, by rfl⟩ : syracuseStep 66695845 = 12505471) B12505471
theorem B2307239 : Blo 1024605 2307239 := bstep (se 1 (by rfl) ⟨1730429, by rfl⟩ : syracuseStep 2307239 = 3460859) B3460859
theorem B2308265 : Blo 1024605 2308265 := bstep (se 2 (by rfl) ⟨865599, by rfl⟩ : syracuseStep 2308265 = 1731199) B1731199
theorem B9355463 : Blo 1024605 9355463 := bstep (se 1 (by rfl) ⟨7016597, by rfl⟩ : syracuseStep 9355463 = 14033195) B14033195
theorem B2310911 : Blo 1024605 2310911 := bstep (se 1 (by rfl) ⟨1733183, by rfl⟩ : syracuseStep 2310911 = 3466367) B3466367
theorem B2770075 : Blo 1024605 2770075 := bstep (se 1 (by rfl) ⟨2077556, by rfl⟩ : syracuseStep 2770075 = 4155113) B4155113
theorem B2312585 : Blo 1024605 2312585 := bstep (se 2 (by rfl) ⟨867219, by rfl⟩ : syracuseStep 2312585 = 1734439) B1734439
theorem B9849883 : Blo 1024605 9849883 := bstep (se 1 (by rfl) ⟨7387412, by rfl⟩ : syracuseStep 9849883 = 14774825) B14774825
theorem B5197769 : Blo 1024605 5197769 := bstep (se 2 (by rfl) ⟨1949163, by rfl⟩ : syracuseStep 5197769 = 3898327) B3898327
theorem B15028193 : Blo 1024605 15028193 := bstep (se 2 (by rfl) ⟨5635572, by rfl⟩ : syracuseStep 15028193 = 11271145) B11271145
theorem B1298911 : Blo 1024605 1298911 := bstep (se 1 (by rfl) ⟨974183, by rfl⟩ : syracuseStep 1298911 = 1948367) B1948367
theorem B120050657 : Blo 1024605 120050657 := bstep (se 2 (by rfl) ⟨45018996, by rfl⟩ : syracuseStep 120050657 = 90037993) B90037993
theorem B16048327 : Blo 1024605 16048327 := bstep (se 1 (by rfl) ⟨12036245, by rfl⟩ : syracuseStep 16048327 = 24072491) B24072491
theorem B3894439 : Blo 1024605 3894439 := bstep (se 1 (by rfl) ⟨2920829, by rfl⟩ : syracuseStep 3894439 = 5841659) B5841659
theorem B5206841 : Blo 1024605 5206841 := bstep (se 2 (by rfl) ⟨1952565, by rfl⟩ : syracuseStep 5206841 = 3905131) B3905131
theorem B3470201 : Blo 1024605 3470201 := bstep (se 2 (by rfl) ⟨1301325, by rfl⟩ : syracuseStep 3470201 = 2602651) B2602651
theorem B3470363 : Blo 1024605 3470363 := bstep (se 1 (by rfl) ⟨2602772, by rfl⟩ : syracuseStep 3470363 = 5205545) B5205545
theorem B21397769 : Blo 1024605 21397769 := bstep (se 2 (by rfl) ⟨8024163, by rfl⟩ : syracuseStep 21397769 = 16048327) B16048327
theorem B1540607 : Blo 1024605 1540607 := bstep (se 1 (by rfl) ⟨1155455, by rfl⟩ : syracuseStep 1540607 = 2310911) B2310911
theorem B1540649 : Blo 1024605 1540649 := bstep (se 2 (by rfl) ⟨577743, by rfl⟩ : syracuseStep 1540649 = 1155487) B1155487
theorem B1541723 : Blo 1024605 1541723 := bstep (se 1 (by rfl) ⟨1156292, by rfl⟩ : syracuseStep 1541723 = 2312585) B2312585
theorem B5840383 : Blo 1024605 5840383 := bstep (se 1 (by rfl) ⟨4380287, by rfl⟩ : syracuseStep 5840383 = 8760575) B8760575
theorem B23731991 : Blo 1024605 23731991 := bstep (se 1 (by rfl) ⟨17798993, by rfl⟩ : syracuseStep 23731991 = 35597987) B35597987
theorem B6236975 : Blo 1024605 6236975 := bstep (se 1 (by rfl) ⟨4677731, by rfl⟩ : syracuseStep 6236975 = 9355463) B9355463
theorem B9875945 : Blo 1024605 9875945 := bstep (se 2 (by rfl) ⟨3703479, by rfl⟩ : syracuseStep 9875945 = 7406959) B7406959
theorem B80033771 : Blo 1024605 80033771 := bstep (se 1 (by rfl) ⟨60025328, by rfl⟩ : syracuseStep 80033771 = 120050657) B120050657
theorem B5192585 : Blo 1024605 5192585 := bstep (se 2 (by rfl) ⟨1947219, by rfl⟩ : syracuseStep 5192585 = 3894439) B3894439
theorem B2313467 : Blo 1024605 2313467 := bstep (se 1 (by rfl) ⟨1735100, by rfl⟩ : syracuseStep 2313467 = 3470201) B3470201
theorem B2313575 : Blo 1024605 2313575 := bstep (se 1 (by rfl) ⟨1735181, by rfl⟩ : syracuseStep 2313575 = 3470363) B3470363
theorem B549017135 : Blo 1024605 549017135 := bstep (se 1 (by rfl) ⟨411762851, by rfl⟩ : syracuseStep 549017135 = 823525703) B823525703
theorem B3693433 : Blo 1024605 3693433 := bstep (se 2 (by rfl) ⟨1385037, by rfl⟩ : syracuseStep 3693433 = 2770075) B2770075
theorem B3465179 : Blo 1024605 3465179 := bstep (se 1 (by rfl) ⟨2598884, by rfl⟩ : syracuseStep 3465179 = 5197769) B5197769
theorem B13133177 : Blo 1024605 13133177 := bstep (se 2 (by rfl) ⟨4924941, by rfl⟩ : syracuseStep 13133177 = 9849883) B9849883
theorem B3468041 : Blo 1024605 3468041 := bstep (se 2 (by rfl) ⟨1300515, by rfl⟩ : syracuseStep 3468041 = 2601031) B2601031
theorem B1731881 : Blo 1024605 1731881 := bstep (se 2 (by rfl) ⟨649455, by rfl⟩ : syracuseStep 1731881 = 1298911) B1298911
theorem B88927793 : Blo 1024605 88927793 := bstep (se 2 (by rfl) ⟨33347922, by rfl⟩ : syracuseStep 88927793 = 66695845) B66695845
theorem B173436551 : Blo 1024605 173436551 := bstep (se 1 (by rfl) ⟨130077413, by rfl⟩ : syracuseStep 173436551 = 260154827) B260154827
theorem B3471227 : Blo 1024605 3471227 := bstep (se 1 (by rfl) ⟨2603420, by rfl⟩ : syracuseStep 3471227 = 5206841) B5206841
theorem B1538159 : Blo 1024605 1538159 := bstep (se 1 (by rfl) ⟨1153619, by rfl⟩ : syracuseStep 1538159 = 2307239) B2307239
theorem B1538843 : Blo 1024605 1538843 := bstep (se 1 (by rfl) ⟨1154132, by rfl⟩ : syracuseStep 1538843 = 2308265) B2308265
theorem B40075181 : Blo 1024605 40075181 := bstep (se 3 (by rfl) ⟨7514096, by rfl⟩ : syracuseStep 40075181 = 15028193) B15028193
theorem B1542311 : Blo 1024605 1542311 := bstep (se 1 (by rfl) ⟨1156733, by rfl⟩ : syracuseStep 1542311 = 2313467) B2313467
theorem B1542383 : Blo 1024605 1542383 := bstep (se 1 (by rfl) ⟨1156787, by rfl⟩ : syracuseStep 1542383 = 2313575) B2313575
theorem B8755451 : Blo 1024605 8755451 := bstep (se 1 (by rfl) ⟨6566588, by rfl⟩ : syracuseStep 8755451 = 13133177) B13133177
theorem B1154587 : Blo 1024605 1154587 := bstep (se 1 (by rfl) ⟨865940, by rfl⟩ : syracuseStep 1154587 = 1731881) B1731881
theorem B59285195 : Blo 1024605 59285195 := bstep (se 1 (by rfl) ⟨44463896, by rfl⟩ : syracuseStep 59285195 = 88927793) B88927793
theorem B4924577 : Blo 1024605 4924577 := bstep (se 2 (by rfl) ⟨1846716, by rfl⟩ : syracuseStep 4924577 = 3693433) B3693433
theorem B53355847 : Blo 1024605 53355847 := bstep (se 1 (by rfl) ⟨40016885, by rfl⟩ : syracuseStep 53355847 = 80033771) B80033771
theorem B1025439 : Blo 1024605 1025439 := bstep (se 1 (by rfl) ⟨769079, by rfl⟩ : syracuseStep 1025439 = 1538159) B1538159
theorem B1025895 : Blo 1024605 1025895 := bstep (se 1 (by rfl) ⟨769421, by rfl⟩ : syracuseStep 1025895 = 1538843) B1538843
theorem B26716787 : Blo 1024605 26716787 := bstep (se 1 (by rfl) ⟨20037590, by rfl⟩ : syracuseStep 26716787 = 40075181) B40075181
theorem B14265179 : Blo 1024605 14265179 := bstep (se 1 (by rfl) ⟨10698884, by rfl⟩ : syracuseStep 14265179 = 21397769) B21397769
theorem B1027071 : Blo 1024605 1027071 := bstep (se 1 (by rfl) ⟨770303, by rfl⟩ : syracuseStep 1027071 = 1540607) B1540607
theorem B1027099 : Blo 1024605 1027099 := bstep (se 1 (by rfl) ⟨770324, by rfl⟩ : syracuseStep 1027099 = 1540649) B1540649
theorem B1027815 : Blo 1024605 1027815 := bstep (se 1 (by rfl) ⟨770861, by rfl⟩ : syracuseStep 1027815 = 1541723) B1541723
theorem B2310119 : Blo 1024605 2310119 := bstep (se 1 (by rfl) ⟨1732589, by rfl⟩ : syracuseStep 2310119 = 3465179) B3465179
theorem B2312027 : Blo 1024605 2312027 := bstep (se 1 (by rfl) ⟨1734020, by rfl⟩ : syracuseStep 2312027 = 3468041) B3468041
theorem B115624367 : Blo 1024605 115624367 := bstep (se 1 (by rfl) ⟨86718275, by rfl⟩ : syracuseStep 115624367 = 173436551) B173436551
theorem B2314151 : Blo 1024605 2314151 := bstep (se 1 (by rfl) ⟨1735613, by rfl⟩ : syracuseStep 2314151 = 3471227) B3471227
theorem B3461723 : Blo 1024605 3461723 := bstep (se 1 (by rfl) ⟨2596292, by rfl⟩ : syracuseStep 3461723 = 5192585) B5192585
theorem B7787177 : Blo 1024605 7787177 := bstep (se 2 (by rfl) ⟨2920191, by rfl⟩ : syracuseStep 7787177 = 5840383) B5840383
theorem B26335853 : Blo 1024605 26335853 := bstep (se 3 (by rfl) ⟨4937972, by rfl⟩ : syracuseStep 26335853 = 9875945) B9875945
theorem B366011423 : Blo 1024605 366011423 := bstep (se 1 (by rfl) ⟨274508567, by rfl⟩ : syracuseStep 366011423 = 549017135) B549017135
theorem B15821327 : Blo 1024605 15821327 := bstep (se 1 (by rfl) ⟨11865995, by rfl⟩ : syracuseStep 15821327 = 23731991) B23731991
theorem B4157983 : Blo 1024605 4157983 := bstep (se 1 (by rfl) ⟨3118487, by rfl⟩ : syracuseStep 4157983 = 6236975) B6236975
theorem B1541351 : Blo 1024605 1541351 := bstep (se 1 (by rfl) ⟨1156013, by rfl⟩ : syracuseStep 1541351 = 2312027) B2312027
theorem B71141129 : Blo 1024605 71141129 := bstep (se 2 (by rfl) ⟨26677923, by rfl⟩ : syracuseStep 71141129 = 53355847) B53355847
theorem B1542767 : Blo 1024605 1542767 := bstep (se 1 (by rfl) ⟨1157075, by rfl⟩ : syracuseStep 1542767 = 2314151) B2314151
theorem B5836967 : Blo 1024605 5836967 := bstep (se 1 (by rfl) ⟨4377725, by rfl⟩ : syracuseStep 5836967 = 8755451) B8755451
theorem B39523463 : Blo 1024605 39523463 := bstep (se 1 (by rfl) ⟨29642597, by rfl⟩ : syracuseStep 39523463 = 59285195) B59285195
theorem B5543977 : Blo 1024605 5543977 := bstep (se 2 (by rfl) ⟨2078991, by rfl⟩ : syracuseStep 5543977 = 4157983) B4157983
theorem B9510119 : Blo 1024605 9510119 := bstep (se 1 (by rfl) ⟨7132589, by rfl⟩ : syracuseStep 9510119 = 14265179) B14265179
theorem B1028207 : Blo 1024605 1028207 := bstep (se 1 (by rfl) ⟨771155, by rfl⟩ : syracuseStep 1028207 = 1542311) B1542311
theorem B1028255 : Blo 1024605 1028255 := bstep (se 1 (by rfl) ⟨771191, by rfl⟩ : syracuseStep 1028255 = 1542383) B1542383
theorem B77082911 : Blo 1024605 77082911 := bstep (se 1 (by rfl) ⟨57812183, by rfl⟩ : syracuseStep 77082911 = 115624367) B115624367
theorem B2307815 : Blo 1024605 2307815 := bstep (se 1 (by rfl) ⟨1730861, by rfl⟩ : syracuseStep 2307815 = 3461723) B3461723
theorem B5191451 : Blo 1024605 5191451 := bstep (se 1 (by rfl) ⟨3893588, by rfl⟩ : syracuseStep 5191451 = 7787177) B7787177
theorem B244007615 : Blo 1024605 244007615 := bstep (se 1 (by rfl) ⟨183005711, by rfl⟩ : syracuseStep 244007615 = 366011423) B366011423
theorem B17811191 : Blo 1024605 17811191 := bstep (se 1 (by rfl) ⟨13358393, by rfl⟩ : syracuseStep 17811191 = 26716787) B26716787
theorem B13132205 : Blo 1024605 13132205 := bstep (se 3 (by rfl) ⟨2462288, by rfl⟩ : syracuseStep 13132205 = 4924577) B4924577
theorem B17557235 : Blo 1024605 17557235 := bstep (se 1 (by rfl) ⟨13167926, by rfl⟩ : syracuseStep 17557235 = 26335853) B26335853
theorem B10547551 : Blo 1024605 10547551 := bstep (se 1 (by rfl) ⟨7910663, by rfl⟩ : syracuseStep 10547551 = 15821327) B15821327
theorem B1539449 : Blo 1024605 1539449 := bstep (se 2 (by rfl) ⟨577293, by rfl⟩ : syracuseStep 1539449 = 1154587) B1154587
theorem B1540079 : Blo 1024605 1540079 := bstep (se 1 (by rfl) ⟨1155059, by rfl⟩ : syracuseStep 1540079 = 2310119) B2310119
theorem B26348975 : Blo 1024605 26348975 := bstep (se 1 (by rfl) ⟨19761731, by rfl⟩ : syracuseStep 26348975 = 39523463) B39523463
theorem B8754803 : Blo 1024605 8754803 := bstep (se 1 (by rfl) ⟨6566102, by rfl⟩ : syracuseStep 8754803 = 13132205) B13132205
theorem B14063401 : Blo 1024605 14063401 := bstep (se 2 (by rfl) ⟨5273775, by rfl⟩ : syracuseStep 14063401 = 10547551) B10547551
theorem B11704823 : Blo 1024605 11704823 := bstep (se 1 (by rfl) ⟨8778617, by rfl⟩ : syracuseStep 11704823 = 17557235) B17557235
theorem B51388607 : Blo 1024605 51388607 := bstep (se 1 (by rfl) ⟨38541455, by rfl⟩ : syracuseStep 51388607 = 77082911) B77082911
theorem B1026299 : Blo 1024605 1026299 := bstep (se 1 (by rfl) ⟨769724, by rfl⟩ : syracuseStep 1026299 = 1539449) B1539449
theorem B1026719 : Blo 1024605 1026719 := bstep (se 1 (by rfl) ⟨770039, by rfl⟩ : syracuseStep 1026719 = 1540079) B1540079
theorem B162671743 : Blo 1024605 162671743 := bstep (se 1 (by rfl) ⟨122003807, by rfl⟩ : syracuseStep 162671743 = 244007615) B244007615
theorem B1027567 : Blo 1024605 1027567 := bstep (se 1 (by rfl) ⟨770675, by rfl⟩ : syracuseStep 1027567 = 1541351) B1541351
theorem B11874127 : Blo 1024605 11874127 := bstep (se 1 (by rfl) ⟨8905595, by rfl⟩ : syracuseStep 11874127 = 17811191) B17811191
theorem B47427419 : Blo 1024605 47427419 := bstep (se 1 (by rfl) ⟨35570564, by rfl⟩ : syracuseStep 47427419 = 71141129) B71141129
theorem B1028511 : Blo 1024605 1028511 := bstep (se 1 (by rfl) ⟨771383, by rfl⟩ : syracuseStep 1028511 = 1542767) B1542767
theorem B6340079 : Blo 1024605 6340079 := bstep (se 1 (by rfl) ⟨4755059, by rfl⟩ : syracuseStep 6340079 = 9510119) B9510119
theorem B7391969 : Blo 1024605 7391969 := bstep (se 2 (by rfl) ⟨2771988, by rfl⟩ : syracuseStep 7391969 = 5543977) B5543977
theorem B3460967 : Blo 1024605 3460967 := bstep (se 1 (by rfl) ⟨2595725, by rfl⟩ : syracuseStep 3460967 = 5191451) B5191451
theorem B3891311 : Blo 1024605 3891311 := bstep (se 1 (by rfl) ⟨2918483, by rfl⟩ : syracuseStep 3891311 = 5836967) B5836967
theorem B1538543 : Blo 1024605 1538543 := bstep (se 1 (by rfl) ⟨1153907, by rfl⟩ : syracuseStep 1538543 = 2307815) B2307815
theorem B17565983 : Blo 1024605 17565983 := bstep (se 1 (by rfl) ⟨13174487, by rfl⟩ : syracuseStep 17565983 = 26348975) B26348975
theorem B5836535 : Blo 1024605 5836535 := bstep (se 1 (by rfl) ⟨4377401, by rfl⟩ : syracuseStep 5836535 = 8754803) B8754803
theorem B216895657 : Blo 1024605 216895657 := bstep (se 2 (by rfl) ⟨81335871, by rfl⟩ : syracuseStep 216895657 = 162671743) B162671743
theorem B7803215 : Blo 1024605 7803215 := bstep (se 1 (by rfl) ⟨5852411, by rfl⟩ : syracuseStep 7803215 = 11704823) B11704823
theorem B15832169 : Blo 1024605 15832169 := bstep (se 2 (by rfl) ⟨5937063, by rfl⟩ : syracuseStep 15832169 = 11874127) B11874127
theorem B2594207 : Blo 1024605 2594207 := bstep (se 1 (by rfl) ⟨1945655, by rfl⟩ : syracuseStep 2594207 = 3891311) B3891311
theorem B1025695 : Blo 1024605 1025695 := bstep (se 1 (by rfl) ⟨769271, by rfl⟩ : syracuseStep 1025695 = 1538543) B1538543
theorem B4927979 : Blo 1024605 4927979 := bstep (se 1 (by rfl) ⟨3695984, by rfl⟩ : syracuseStep 4927979 = 7391969) B7391969
theorem B2307311 : Blo 1024605 2307311 := bstep (se 1 (by rfl) ⟨1730483, by rfl⟩ : syracuseStep 2307311 = 3460967) B3460967
theorem B34259071 : Blo 1024605 34259071 := bstep (se 1 (by rfl) ⟨25694303, by rfl⟩ : syracuseStep 34259071 = 51388607) B51388607
theorem B31618279 : Blo 1024605 31618279 := bstep (se 1 (by rfl) ⟨23713709, by rfl⟩ : syracuseStep 31618279 = 47427419) B47427419
theorem B16906877 : Blo 1024605 16906877 := bstep (se 3 (by rfl) ⟨3170039, by rfl⟩ : syracuseStep 16906877 = 6340079) B6340079
theorem B75004805 : Blo 1024605 75004805 := bstep (se 4 (by rfl) ⟨7031700, by rfl⟩ : syracuseStep 75004805 = 14063401) B14063401
theorem B45678761 : Blo 1024605 45678761 := bstep (se 2 (by rfl) ⟨17129535, by rfl⟩ : syracuseStep 45678761 = 34259071) B34259071
theorem B10554779 : Blo 1024605 10554779 := bstep (se 1 (by rfl) ⟨7916084, by rfl⟩ : syracuseStep 10554779 = 15832169) B15832169
theorem B3285319 : Blo 1024605 3285319 := bstep (se 1 (by rfl) ⟨2463989, by rfl⟩ : syracuseStep 3285319 = 4927979) B4927979
theorem B11710655 : Blo 1024605 11710655 := bstep (se 1 (by rfl) ⟨8782991, by rfl⟩ : syracuseStep 11710655 = 17565983) B17565983
theorem B289194209 : Blo 1024605 289194209 := bstep (se 2 (by rfl) ⟨108447828, by rfl⟩ : syracuseStep 289194209 = 216895657) B216895657
theorem B42157705 : Blo 1024605 42157705 := bstep (se 2 (by rfl) ⟨15809139, by rfl⟩ : syracuseStep 42157705 = 31618279) B31618279
theorem B3891023 : Blo 1024605 3891023 := bstep (se 1 (by rfl) ⟨2918267, by rfl⟩ : syracuseStep 3891023 = 5836535) B5836535
theorem B5202143 : Blo 1024605 5202143 := bstep (se 1 (by rfl) ⟨3901607, by rfl⟩ : syracuseStep 5202143 = 7803215) B7803215
theorem B1729471 : Blo 1024605 1729471 := bstep (se 1 (by rfl) ⟨1297103, by rfl⟩ : syracuseStep 1729471 = 2594207) B2594207
theorem B1538207 : Blo 1024605 1538207 := bstep (se 1 (by rfl) ⟨1153655, by rfl⟩ : syracuseStep 1538207 = 2307311) B2307311
theorem B11271251 : Blo 1024605 11271251 := bstep (se 1 (by rfl) ⟨8453438, by rfl⟩ : syracuseStep 11271251 = 16906877) B16906877
theorem B50003203 : Blo 1024605 50003203 := bstep (se 1 (by rfl) ⟨37502402, by rfl⟩ : syracuseStep 50003203 = 75004805) B75004805
theorem B2594015 : Blo 1024605 2594015 := bstep (se 1 (by rfl) ⟨1945511, by rfl⟩ : syracuseStep 2594015 = 3891023) B3891023
theorem B7807103 : Blo 1024605 7807103 := bstep (se 1 (by rfl) ⟨5855327, by rfl⟩ : syracuseStep 7807103 = 11710655) B11710655
theorem B1025471 : Blo 1024605 1025471 := bstep (se 1 (by rfl) ⟨769103, by rfl⟩ : syracuseStep 1025471 = 1538207) B1538207
theorem B7514167 : Blo 1024605 7514167 := bstep (se 1 (by rfl) ⟨5635625, by rfl⟩ : syracuseStep 7514167 = 11271251) B11271251
theorem B30452507 : Blo 1024605 30452507 := bstep (se 1 (by rfl) ⟨22839380, by rfl⟩ : syracuseStep 30452507 = 45678761) B45678761
theorem B2305961 : Blo 1024605 2305961 := bstep (se 2 (by rfl) ⟨864735, by rfl⟩ : syracuseStep 2305961 = 1729471) B1729471
theorem B56210273 : Blo 1024605 56210273 := bstep (se 2 (by rfl) ⟨21078852, by rfl⟩ : syracuseStep 56210273 = 42157705) B42157705
theorem B66670937 : Blo 1024605 66670937 := bstep (se 2 (by rfl) ⟨25001601, by rfl⟩ : syracuseStep 66670937 = 50003203) B50003203
theorem B192796139 : Blo 1024605 192796139 := bstep (se 1 (by rfl) ⟨144597104, by rfl⟩ : syracuseStep 192796139 = 289194209) B289194209
theorem B4380425 : Blo 1024605 4380425 := bstep (se 2 (by rfl) ⟨1642659, by rfl⟩ : syracuseStep 4380425 = 3285319) B3285319
theorem B7036519 : Blo 1024605 7036519 := bstep (se 1 (by rfl) ⟨5277389, by rfl⟩ : syracuseStep 7036519 = 10554779) B10554779
theorem B3468095 : Blo 1024605 3468095 := bstep (se 1 (by rfl) ⟨2601071, by rfl⟩ : syracuseStep 3468095 = 5202143) B5202143
theorem B2920283 : Blo 1024605 2920283 := bstep (se 1 (by rfl) ⟨2190212, by rfl⟩ : syracuseStep 2920283 = 4380425) B4380425
theorem B9382025 : Blo 1024605 9382025 := bstep (se 2 (by rfl) ⟨3518259, by rfl⟩ : syracuseStep 9382025 = 7036519) B7036519
theorem B44447291 : Blo 1024605 44447291 := bstep (se 1 (by rfl) ⟨33335468, by rfl⟩ : syracuseStep 44447291 = 66670937) B66670937
theorem B20301671 : Blo 1024605 20301671 := bstep (se 1 (by rfl) ⟨15226253, by rfl⟩ : syracuseStep 20301671 = 30452507) B30452507
theorem B2312063 : Blo 1024605 2312063 := bstep (se 1 (by rfl) ⟨1734047, by rfl⟩ : syracuseStep 2312063 = 3468095) B3468095
theorem B37473515 : Blo 1024605 37473515 := bstep (se 1 (by rfl) ⟨28105136, by rfl⟩ : syracuseStep 37473515 = 56210273) B56210273
theorem B10018889 : Blo 1024605 10018889 := bstep (se 2 (by rfl) ⟨3757083, by rfl⟩ : syracuseStep 10018889 = 7514167) B7514167
theorem B1729343 : Blo 1024605 1729343 := bstep (se 1 (by rfl) ⟨1297007, by rfl⟩ : syracuseStep 1729343 = 2594015) B2594015
theorem B514123037 : Blo 1024605 514123037 := bstep (se 3 (by rfl) ⟨96398069, by rfl⟩ : syracuseStep 514123037 = 192796139) B192796139
theorem B5204735 : Blo 1024605 5204735 := bstep (se 1 (by rfl) ⟨3903551, by rfl⟩ : syracuseStep 5204735 = 7807103) B7807103
theorem B1537307 : Blo 1024605 1537307 := bstep (se 1 (by rfl) ⟨1152980, by rfl⟩ : syracuseStep 1537307 = 2305961) B2305961
theorem B13534447 : Blo 1024605 13534447 := bstep (se 1 (by rfl) ⟨10150835, by rfl⟩ : syracuseStep 13534447 = 20301671) B20301671
theorem B1541375 : Blo 1024605 1541375 := bstep (se 1 (by rfl) ⟨1156031, by rfl⟩ : syracuseStep 1541375 = 2312063) B2312063
theorem B1152895 : Blo 1024605 1152895 := bstep (se 1 (by rfl) ⟨864671, by rfl⟩ : syracuseStep 1152895 = 1729343) B1729343
theorem B1024871 : Blo 1024605 1024871 := bstep (se 1 (by rfl) ⟨768653, by rfl⟩ : syracuseStep 1024871 = 1537307) B1537307
theorem B29631527 : Blo 1024605 29631527 := bstep (se 1 (by rfl) ⟨22223645, by rfl⟩ : syracuseStep 29631527 = 44447291) B44447291
theorem B24982343 : Blo 1024605 24982343 := bstep (se 1 (by rfl) ⟨18736757, by rfl⟩ : syracuseStep 24982343 = 37473515) B37473515
theorem B1946855 : Blo 1024605 1946855 := bstep (se 1 (by rfl) ⟨1460141, by rfl⟩ : syracuseStep 1946855 = 2920283) B2920283
theorem B25018733 : Blo 1024605 25018733 := bstep (se 3 (by rfl) ⟨4691012, by rfl⟩ : syracuseStep 25018733 = 9382025) B9382025
theorem B6679259 : Blo 1024605 6679259 := bstep (se 1 (by rfl) ⟨5009444, by rfl⟩ : syracuseStep 6679259 = 10018889) B10018889
theorem B342748691 : Blo 1024605 342748691 := bstep (se 1 (by rfl) ⟨257061518, by rfl⟩ : syracuseStep 342748691 = 514123037) B514123037
theorem B3469823 : Blo 1024605 3469823 := bstep (se 1 (by rfl) ⟨2602367, by rfl⟩ : syracuseStep 3469823 = 5204735) B5204735
theorem B16679155 : Blo 1024605 16679155 := bstep (se 1 (by rfl) ⟨12509366, by rfl⟩ : syracuseStep 16679155 = 25018733) B25018733
theorem B228499127 : Blo 1024605 228499127 := bstep (se 1 (by rfl) ⟨171374345, by rfl⟩ : syracuseStep 228499127 = 342748691) B342748691
theorem B16654895 : Blo 1024605 16654895 := bstep (se 1 (by rfl) ⟨12491171, by rfl⟩ : syracuseStep 16654895 = 24982343) B24982343
theorem B1027583 : Blo 1024605 1027583 := bstep (se 1 (by rfl) ⟨770687, by rfl⟩ : syracuseStep 1027583 = 1541375) B1541375
theorem B5191613 : Blo 1024605 5191613 := bstep (se 3 (by rfl) ⟨973427, by rfl⟩ : syracuseStep 5191613 = 1946855) B1946855
theorem B2313215 : Blo 1024605 2313215 := bstep (se 1 (by rfl) ⟨1734911, by rfl⟩ : syracuseStep 2313215 = 3469823) B3469823
theorem B18045929 : Blo 1024605 18045929 := bstep (se 2 (by rfl) ⟨6767223, by rfl⟩ : syracuseStep 18045929 = 13534447) B13534447
theorem B19754351 : Blo 1024605 19754351 := bstep (se 1 (by rfl) ⟨14815763, by rfl⟩ : syracuseStep 19754351 = 29631527) B29631527
theorem B4452839 : Blo 1024605 4452839 := bstep (se 1 (by rfl) ⟨3339629, by rfl⟩ : syracuseStep 4452839 = 6679259) B6679259
theorem B1537193 : Blo 1024605 1537193 := bstep (se 2 (by rfl) ⟨576447, by rfl⟩ : syracuseStep 1537193 = 1152895) B1152895
theorem B1542143 : Blo 1024605 1542143 := bstep (se 1 (by rfl) ⟨1156607, by rfl⟩ : syracuseStep 1542143 = 2313215) B2313215
theorem B12030619 : Blo 1024605 12030619 := bstep (se 1 (by rfl) ⟨9022964, by rfl⟩ : syracuseStep 12030619 = 18045929) B18045929
theorem B1024795 : Blo 1024605 1024795 := bstep (se 1 (by rfl) ⟨768596, by rfl⟩ : syracuseStep 1024795 = 1537193) B1537193
theorem B2968559 : Blo 1024605 2968559 := bstep (se 1 (by rfl) ⟨2226419, by rfl⟩ : syracuseStep 2968559 = 4452839) B4452839
theorem B3461075 : Blo 1024605 3461075 := bstep (se 1 (by rfl) ⟨2595806, by rfl⟩ : syracuseStep 3461075 = 5191613) B5191613
theorem B22238873 : Blo 1024605 22238873 := bstep (se 2 (by rfl) ⟨8339577, by rfl⟩ : syracuseStep 22238873 = 16679155) B16679155
theorem B152332751 : Blo 1024605 152332751 := bstep (se 1 (by rfl) ⟨114249563, by rfl⟩ : syracuseStep 152332751 = 228499127) B228499127
theorem B11103263 : Blo 1024605 11103263 := bstep (se 1 (by rfl) ⟨8327447, by rfl⟩ : syracuseStep 11103263 = 16654895) B16654895
theorem B13169567 : Blo 1024605 13169567 := bstep (se 1 (by rfl) ⟨9877175, by rfl⟩ : syracuseStep 13169567 = 19754351) B19754351
theorem B101555167 : Blo 1024605 101555167 := bstep (se 1 (by rfl) ⟨76166375, by rfl⟩ : syracuseStep 101555167 = 152332751) B152332751
theorem B1028095 : Blo 1024605 1028095 := bstep (se 1 (by rfl) ⟨771071, by rfl⟩ : syracuseStep 1028095 = 1542143) B1542143
theorem B1979039 : Blo 1024605 1979039 := bstep (se 1 (by rfl) ⟨1484279, by rfl⟩ : syracuseStep 1979039 = 2968559) B2968559
theorem B2307383 : Blo 1024605 2307383 := bstep (se 1 (by rfl) ⟨1730537, by rfl⟩ : syracuseStep 2307383 = 3461075) B3461075
theorem B14825915 : Blo 1024605 14825915 := bstep (se 1 (by rfl) ⟨11119436, by rfl⟩ : syracuseStep 14825915 = 22238873) B22238873
theorem B16040825 : Blo 1024605 16040825 := bstep (se 2 (by rfl) ⟨6015309, by rfl⟩ : syracuseStep 16040825 = 12030619) B12030619
theorem B7402175 : Blo 1024605 7402175 := bstep (se 1 (by rfl) ⟨5551631, by rfl⟩ : syracuseStep 7402175 = 11103263) B11103263
theorem B8779711 : Blo 1024605 8779711 := bstep (se 1 (by rfl) ⟨6584783, by rfl⟩ : syracuseStep 8779711 = 13169567) B13169567
theorem B5277437 : Blo 1024605 5277437 := bstep (se 3 (by rfl) ⟨989519, by rfl⟩ : syracuseStep 5277437 = 1979039) B1979039
theorem B11706281 : Blo 1024605 11706281 := bstep (se 2 (by rfl) ⟨4389855, by rfl⟩ : syracuseStep 11706281 = 8779711) B8779711
theorem B135406889 : Blo 1024605 135406889 := bstep (se 2 (by rfl) ⟨50777583, by rfl⟩ : syracuseStep 135406889 = 101555167) B101555167
theorem B10693883 : Blo 1024605 10693883 := bstep (se 1 (by rfl) ⟨8020412, by rfl⟩ : syracuseStep 10693883 = 16040825) B16040825
theorem B4934783 : Blo 1024605 4934783 := bstep (se 1 (by rfl) ⟨3701087, by rfl⟩ : syracuseStep 4934783 = 7402175) B7402175
theorem B9883943 : Blo 1024605 9883943 := bstep (se 1 (by rfl) ⟨7412957, by rfl⟩ : syracuseStep 9883943 = 14825915) B14825915
theorem B1538255 : Blo 1024605 1538255 := bstep (se 1 (by rfl) ⟨1153691, by rfl⟩ : syracuseStep 1538255 = 2307383) B2307383
theorem B6589295 : Blo 1024605 6589295 := bstep (se 1 (by rfl) ⟨4941971, by rfl⟩ : syracuseStep 6589295 = 9883943) B9883943
theorem B7804187 : Blo 1024605 7804187 := bstep (se 1 (by rfl) ⟨5853140, by rfl⟩ : syracuseStep 7804187 = 11706281) B11706281
theorem B1025503 : Blo 1024605 1025503 := bstep (se 1 (by rfl) ⟨769127, by rfl⟩ : syracuseStep 1025503 = 1538255) B1538255
theorem B3518291 : Blo 1024605 3518291 := bstep (se 1 (by rfl) ⟨2638718, by rfl⟩ : syracuseStep 3518291 = 5277437) B5277437
theorem B7129255 : Blo 1024605 7129255 := bstep (se 1 (by rfl) ⟨5346941, by rfl⟩ : syracuseStep 7129255 = 10693883) B10693883
theorem B13159421 : Blo 1024605 13159421 := bstep (se 3 (by rfl) ⟨2467391, by rfl⟩ : syracuseStep 13159421 = 4934783) B4934783
theorem B90271259 : Blo 1024605 90271259 := bstep (se 1 (by rfl) ⟨67703444, by rfl⟩ : syracuseStep 90271259 = 135406889) B135406889
theorem B4392863 : Blo 1024605 4392863 := bstep (se 1 (by rfl) ⟨3294647, by rfl⟩ : syracuseStep 4392863 = 6589295) B6589295
theorem B9505673 : Blo 1024605 9505673 := bstep (se 2 (by rfl) ⟨3564627, by rfl⟩ : syracuseStep 9505673 = 7129255) B7129255
theorem B60180839 : Blo 1024605 60180839 := bstep (se 1 (by rfl) ⟨45135629, by rfl⟩ : syracuseStep 60180839 = 90271259) B90271259
theorem B2345527 : Blo 1024605 2345527 := bstep (se 1 (by rfl) ⟨1759145, by rfl⟩ : syracuseStep 2345527 = 3518291) B3518291
theorem B8772947 : Blo 1024605 8772947 := bstep (se 1 (by rfl) ⟨6579710, by rfl⟩ : syracuseStep 8772947 = 13159421) B13159421
theorem B5202791 : Blo 1024605 5202791 := bstep (se 1 (by rfl) ⟨3902093, by rfl⟩ : syracuseStep 5202791 = 7804187) B7804187
theorem B2928575 : Blo 1024605 2928575 := bstep (se 1 (by rfl) ⟨2196431, by rfl⟩ : syracuseStep 2928575 = 4392863) B4392863
theorem B40120559 : Blo 1024605 40120559 := bstep (se 1 (by rfl) ⟨30090419, by rfl⟩ : syracuseStep 40120559 = 60180839) B60180839
theorem B6337115 : Blo 1024605 6337115 := bstep (se 1 (by rfl) ⟨4752836, by rfl⟩ : syracuseStep 6337115 = 9505673) B9505673
theorem B3127369 : Blo 1024605 3127369 := bstep (se 2 (by rfl) ⟨1172763, by rfl⟩ : syracuseStep 3127369 = 2345527) B2345527
theorem B5848631 : Blo 1024605 5848631 := bstep (se 1 (by rfl) ⟨4386473, by rfl⟩ : syracuseStep 5848631 = 8772947) B8772947
theorem B3468527 : Blo 1024605 3468527 := bstep (se 1 (by rfl) ⟨2601395, by rfl⟩ : syracuseStep 3468527 = 5202791) B5202791
theorem B4169825 : Blo 1024605 4169825 := bstep (se 2 (by rfl) ⟨1563684, by rfl⟩ : syracuseStep 4169825 = 3127369) B3127369
theorem B26747039 : Blo 1024605 26747039 := bstep (se 1 (by rfl) ⟨20060279, by rfl⟩ : syracuseStep 26747039 = 40120559) B40120559
theorem B7809533 : Blo 1024605 7809533 := bstep (se 3 (by rfl) ⟨1464287, by rfl⟩ : syracuseStep 7809533 = 2928575) B2928575
theorem B2312351 : Blo 1024605 2312351 := bstep (se 1 (by rfl) ⟨1734263, by rfl⟩ : syracuseStep 2312351 = 3468527) B3468527
theorem B4224743 : Blo 1024605 4224743 := bstep (se 1 (by rfl) ⟨3168557, by rfl⟩ : syracuseStep 4224743 = 6337115) B6337115
theorem B3899087 : Blo 1024605 3899087 := bstep (se 1 (by rfl) ⟨2924315, by rfl⟩ : syracuseStep 3899087 = 5848631) B5848631
theorem B1541567 : Blo 1024605 1541567 := bstep (se 1 (by rfl) ⟨1156175, by rfl⟩ : syracuseStep 1541567 = 2312351) B2312351
theorem B17831359 : Blo 1024605 17831359 := bstep (se 1 (by rfl) ⟨13373519, by rfl⟩ : syracuseStep 17831359 = 26747039) B26747039
theorem B2599391 : Blo 1024605 2599391 := bstep (se 1 (by rfl) ⟨1949543, by rfl⟩ : syracuseStep 2599391 = 3899087) B3899087
theorem B2779883 : Blo 1024605 2779883 := bstep (se 1 (by rfl) ⟨2084912, by rfl⟩ : syracuseStep 2779883 = 4169825) B4169825
theorem B5206355 : Blo 1024605 5206355 := bstep (se 1 (by rfl) ⟨3904766, by rfl⟩ : syracuseStep 5206355 = 7809533) B7809533
theorem B2816495 : Blo 1024605 2816495 := bstep (se 1 (by rfl) ⟨2112371, by rfl⟩ : syracuseStep 2816495 = 4224743) B4224743
theorem B95100581 : Blo 1024605 95100581 := bstep (se 4 (by rfl) ⟨8915679, by rfl⟩ : syracuseStep 95100581 = 17831359) B17831359
theorem B1877663 : Blo 1024605 1877663 := bstep (se 1 (by rfl) ⟨1408247, by rfl⟩ : syracuseStep 1877663 = 2816495) B2816495
theorem B1027711 : Blo 1024605 1027711 := bstep (se 1 (by rfl) ⟨770783, by rfl⟩ : syracuseStep 1027711 = 1541567) B1541567
theorem B1853255 : Blo 1024605 1853255 := bstep (se 1 (by rfl) ⟨1389941, by rfl⟩ : syracuseStep 1853255 = 2779883) B2779883
theorem B1732927 : Blo 1024605 1732927 := bstep (se 1 (by rfl) ⟨1299695, by rfl⟩ : syracuseStep 1732927 = 2599391) B2599391
theorem B3470903 : Blo 1024605 3470903 := bstep (se 1 (by rfl) ⟨2603177, by rfl⟩ : syracuseStep 3470903 = 5206355) B5206355
theorem B1251775 : Blo 1024605 1251775 := bstep (se 1 (by rfl) ⟨938831, by rfl⟩ : syracuseStep 1251775 = 1877663) B1877663
theorem B253601549 : Blo 1024605 253601549 := bstep (se 3 (by rfl) ⟨47550290, by rfl⟩ : syracuseStep 253601549 = 95100581) B95100581
theorem B2310569 : Blo 1024605 2310569 := bstep (se 2 (by rfl) ⟨866463, by rfl⟩ : syracuseStep 2310569 = 1732927) B1732927
theorem B2313935 : Blo 1024605 2313935 := bstep (se 1 (by rfl) ⟨1735451, by rfl⟩ : syracuseStep 2313935 = 3470903) B3470903
theorem B1235503 : Blo 1024605 1235503 := bstep (se 1 (by rfl) ⟨926627, by rfl⟩ : syracuseStep 1235503 = 1853255) B1853255
theorem B1540379 : Blo 1024605 1540379 := bstep (se 1 (by rfl) ⟨1155284, by rfl⟩ : syracuseStep 1540379 = 2310569) B2310569
theorem B1542623 : Blo 1024605 1542623 := bstep (se 1 (by rfl) ⟨1156967, by rfl⟩ : syracuseStep 1542623 = 2313935) B2313935
theorem B6589349 : Blo 1024605 6589349 := bstep (se 4 (by rfl) ⟨617751, by rfl⟩ : syracuseStep 6589349 = 1235503) B1235503
theorem B169067699 : Blo 1024605 169067699 := bstep (se 1 (by rfl) ⟨126800774, by rfl⟩ : syracuseStep 169067699 = 253601549) B253601549
theorem B1669033 : Blo 1024605 1669033 := bstep (se 2 (by rfl) ⟨625887, by rfl⟩ : syracuseStep 1669033 = 1251775) B1251775
theorem B4392899 : Blo 1024605 4392899 := bstep (se 1 (by rfl) ⟨3294674, by rfl⟩ : syracuseStep 4392899 = 6589349) B6589349
theorem B1026919 : Blo 1024605 1026919 := bstep (se 1 (by rfl) ⟨770189, by rfl⟩ : syracuseStep 1026919 = 1540379) B1540379
theorem B1028415 : Blo 1024605 1028415 := bstep (se 1 (by rfl) ⟨771311, by rfl⟩ : syracuseStep 1028415 = 1542623) B1542623
theorem B112711799 : Blo 1024605 112711799 := bstep (se 1 (by rfl) ⟨84533849, by rfl⟩ : syracuseStep 112711799 = 169067699) B169067699
theorem B2225377 : Blo 1024605 2225377 := bstep (se 2 (by rfl) ⟨834516, by rfl⟩ : syracuseStep 2225377 = 1669033) B1669033
theorem B75141199 : Blo 1024605 75141199 := bstep (se 1 (by rfl) ⟨56355899, by rfl⟩ : syracuseStep 75141199 = 112711799) B112711799
theorem B11868677 : Blo 1024605 11868677 := bstep (se 4 (by rfl) ⟨1112688, by rfl⟩ : syracuseStep 11868677 = 2225377) B2225377
theorem B2928599 : Blo 1024605 2928599 := bstep (se 1 (by rfl) ⟨2196449, by rfl⟩ : syracuseStep 2928599 = 4392899) B4392899
theorem B7912451 : Blo 1024605 7912451 := bstep (se 1 (by rfl) ⟨5934338, by rfl⟩ : syracuseStep 7912451 = 11868677) B11868677
theorem B100188265 : Blo 1024605 100188265 := bstep (se 2 (by rfl) ⟨37570599, by rfl⟩ : syracuseStep 100188265 = 75141199) B75141199
theorem B1952399 : Blo 1024605 1952399 := bstep (se 1 (by rfl) ⟨1464299, by rfl⟩ : syracuseStep 1952399 = 2928599) B2928599
theorem B133584353 : Blo 1024605 133584353 := bstep (se 2 (by rfl) ⟨50094132, by rfl⟩ : syracuseStep 133584353 = 100188265) B100188265
theorem B1301599 : Blo 1024605 1301599 := bstep (se 1 (by rfl) ⟨976199, by rfl⟩ : syracuseStep 1301599 = 1952399) B1952399
theorem B21099869 : Blo 1024605 21099869 := bstep (se 3 (by rfl) ⟨3956225, by rfl⟩ : syracuseStep 21099869 = 7912451) B7912451
theorem B14066579 : Blo 1024605 14066579 := bstep (se 1 (by rfl) ⟨10549934, by rfl⟩ : syracuseStep 14066579 = 21099869) B21099869
theorem B89056235 : Blo 1024605 89056235 := bstep (se 1 (by rfl) ⟨66792176, by rfl⟩ : syracuseStep 89056235 = 133584353) B133584353
theorem B1735465 : Blo 1024605 1735465 := bstep (se 2 (by rfl) ⟨650799, by rfl⟩ : syracuseStep 1735465 = 1301599) B1301599
theorem B2313953 : Blo 1024605 2313953 := bstep (se 2 (by rfl) ⟨867732, by rfl⟩ : syracuseStep 2313953 = 1735465) B1735465
theorem B37510877 : Blo 1024605 37510877 := bstep (se 3 (by rfl) ⟨7033289, by rfl⟩ : syracuseStep 37510877 = 14066579) B14066579
theorem B59370823 : Blo 1024605 59370823 := bstep (se 1 (by rfl) ⟨44528117, by rfl⟩ : syracuseStep 59370823 = 89056235) B89056235
theorem B1542635 : Blo 1024605 1542635 := bstep (se 1 (by rfl) ⟨1156976, by rfl⟩ : syracuseStep 1542635 = 2313953) B2313953
theorem B100029005 : Blo 1024605 100029005 := bstep (se 3 (by rfl) ⟨18755438, by rfl⟩ : syracuseStep 100029005 = 37510877) B37510877
theorem B79161097 : Blo 1024605 79161097 := bstep (se 2 (by rfl) ⟨29685411, by rfl⟩ : syracuseStep 79161097 = 59370823) B59370823
theorem B105548129 : Blo 1024605 105548129 := bstep (se 2 (by rfl) ⟨39580548, by rfl⟩ : syracuseStep 105548129 = 79161097) B79161097
theorem B66686003 : Blo 1024605 66686003 := bstep (se 1 (by rfl) ⟨50014502, by rfl⟩ : syracuseStep 66686003 = 100029005) B100029005
theorem B1028423 : Blo 1024605 1028423 := bstep (se 1 (by rfl) ⟨771317, by rfl⟩ : syracuseStep 1028423 = 1542635) B1542635
theorem B70365419 : Blo 1024605 70365419 := bstep (se 1 (by rfl) ⟨52774064, by rfl⟩ : syracuseStep 70365419 = 105548129) B105548129
theorem B44457335 : Blo 1024605 44457335 := bstep (se 1 (by rfl) ⟨33343001, by rfl⟩ : syracuseStep 44457335 = 66686003) B66686003
theorem B29638223 : Blo 1024605 29638223 := bstep (se 1 (by rfl) ⟨22228667, by rfl⟩ : syracuseStep 29638223 = 44457335) B44457335
theorem B46910279 : Blo 1024605 46910279 := bstep (se 1 (by rfl) ⟨35182709, by rfl⟩ : syracuseStep 46910279 = 70365419) B70365419
theorem B125094077 : Blo 1024605 125094077 := bstep (se 3 (by rfl) ⟨23455139, by rfl⟩ : syracuseStep 125094077 = 46910279) B46910279
theorem B19758815 : Blo 1024605 19758815 := bstep (se 1 (by rfl) ⟨14819111, by rfl⟩ : syracuseStep 19758815 = 29638223) B29638223
theorem B83396051 : Blo 1024605 83396051 := bstep (se 1 (by rfl) ⟨62547038, by rfl⟩ : syracuseStep 83396051 = 125094077) B125094077
theorem B13172543 : Blo 1024605 13172543 := bstep (se 1 (by rfl) ⟨9879407, by rfl⟩ : syracuseStep 13172543 = 19758815) B19758815
theorem B55597367 : Blo 1024605 55597367 := bstep (se 1 (by rfl) ⟨41698025, by rfl⟩ : syracuseStep 55597367 = 83396051) B83396051
theorem B8781695 : Blo 1024605 8781695 := bstep (se 1 (by rfl) ⟨6586271, by rfl⟩ : syracuseStep 8781695 = 13172543) B13172543
theorem B37064911 : Blo 1024605 37064911 := bstep (se 1 (by rfl) ⟨27798683, by rfl⟩ : syracuseStep 37064911 = 55597367) B55597367
theorem B5854463 : Blo 1024605 5854463 := bstep (se 1 (by rfl) ⟨4390847, by rfl⟩ : syracuseStep 5854463 = 8781695) B8781695
theorem B3902975 : Blo 1024605 3902975 := bstep (se 1 (by rfl) ⟨2927231, by rfl⟩ : syracuseStep 3902975 = 5854463) B5854463
theorem B49419881 : Blo 1024605 49419881 := bstep (se 2 (by rfl) ⟨18532455, by rfl⟩ : syracuseStep 49419881 = 37064911) B37064911
theorem B2601983 : Blo 1024605 2601983 := bstep (se 1 (by rfl) ⟨1951487, by rfl⟩ : syracuseStep 2601983 = 3902975) B3902975
theorem B32946587 : Blo 1024605 32946587 := bstep (se 1 (by rfl) ⟨24709940, by rfl⟩ : syracuseStep 32946587 = 49419881) B49419881
theorem B21964391 : Blo 1024605 21964391 := bstep (se 1 (by rfl) ⟨16473293, by rfl⟩ : syracuseStep 21964391 = 32946587) B32946587
theorem B1734655 : Blo 1024605 1734655 := bstep (se 1 (by rfl) ⟨1300991, by rfl⟩ : syracuseStep 1734655 = 2601983) B2601983
theorem B2312873 : Blo 1024605 2312873 := bstep (se 2 (by rfl) ⟨867327, by rfl⟩ : syracuseStep 2312873 = 1734655) B1734655
theorem B14642927 : Blo 1024605 14642927 := bstep (se 1 (by rfl) ⟨10982195, by rfl⟩ : syracuseStep 14642927 = 21964391) B21964391
theorem B1541915 : Blo 1024605 1541915 := bstep (se 1 (by rfl) ⟨1156436, by rfl⟩ : syracuseStep 1541915 = 2312873) B2312873
theorem B9761951 : Blo 1024605 9761951 := bstep (se 1 (by rfl) ⟨7321463, by rfl⟩ : syracuseStep 9761951 = 14642927) B14642927
theorem B1027943 : Blo 1024605 1027943 := bstep (se 1 (by rfl) ⟨770957, by rfl⟩ : syracuseStep 1027943 = 1541915) B1541915
theorem B6507967 : Blo 1024605 6507967 := bstep (se 1 (by rfl) ⟨4880975, by rfl⟩ : syracuseStep 6507967 = 9761951) B9761951
theorem B8677289 : Blo 1024605 8677289 := bstep (se 2 (by rfl) ⟨3253983, by rfl⟩ : syracuseStep 8677289 = 6507967) B6507967
theorem B5784859 : Blo 1024605 5784859 := bstep (se 1 (by rfl) ⟨4338644, by rfl⟩ : syracuseStep 5784859 = 8677289) B8677289
theorem B7713145 : Blo 1024605 7713145 := bstep (se 2 (by rfl) ⟨2892429, by rfl⟩ : syracuseStep 7713145 = 5784859) B5784859
theorem B10284193 : Blo 1024605 10284193 := bstep (se 2 (by rfl) ⟨3856572, by rfl⟩ : syracuseStep 10284193 = 7713145) B7713145
theorem B13712257 : Blo 1024605 13712257 := bstep (se 2 (by rfl) ⟨5142096, by rfl⟩ : syracuseStep 13712257 = 10284193) B10284193
theorem B18283009 : Blo 1024605 18283009 := bstep (se 2 (by rfl) ⟨6856128, by rfl⟩ : syracuseStep 18283009 = 13712257) B13712257
theorem B24377345 : Blo 1024605 24377345 := bstep (se 2 (by rfl) ⟨9141504, by rfl⟩ : syracuseStep 24377345 = 18283009) B18283009
theorem B16251563 : Blo 1024605 16251563 := bstep (se 1 (by rfl) ⟨12188672, by rfl⟩ : syracuseStep 16251563 = 24377345) B24377345
theorem B43337501 : Blo 1024605 43337501 := bstep (se 3 (by rfl) ⟨8125781, by rfl⟩ : syracuseStep 43337501 = 16251563) B16251563
theorem B28891667 : Blo 1024605 28891667 := bstep (se 1 (by rfl) ⟨21668750, by rfl⟩ : syracuseStep 28891667 = 43337501) B43337501
theorem B19261111 : Blo 1024605 19261111 := bstep (se 1 (by rfl) ⟨14445833, by rfl⟩ : syracuseStep 19261111 = 28891667) B28891667
theorem B25681481 : Blo 1024605 25681481 := bstep (se 2 (by rfl) ⟨9630555, by rfl⟩ : syracuseStep 25681481 = 19261111) B19261111
theorem B17120987 : Blo 1024605 17120987 := bstep (se 1 (by rfl) ⟨12840740, by rfl⟩ : syracuseStep 17120987 = 25681481) B25681481
theorem B11413991 : Blo 1024605 11413991 := bstep (se 1 (by rfl) ⟨8560493, by rfl⟩ : syracuseStep 11413991 = 17120987) B17120987
theorem B30437309 : Blo 1024605 30437309 := bstep (se 3 (by rfl) ⟨5706995, by rfl⟩ : syracuseStep 30437309 = 11413991) B11413991
theorem B20291539 : Blo 1024605 20291539 := bstep (se 1 (by rfl) ⟨15218654, by rfl⟩ : syracuseStep 20291539 = 30437309) B30437309
theorem B27055385 : Blo 1024605 27055385 := bstep (se 2 (by rfl) ⟨10145769, by rfl⟩ : syracuseStep 27055385 = 20291539) B20291539
theorem B18036923 : Blo 1024605 18036923 := bstep (se 1 (by rfl) ⟨13527692, by rfl⟩ : syracuseStep 18036923 = 27055385) B27055385
theorem B48098461 : Blo 1024605 48098461 := bstep (se 3 (by rfl) ⟨9018461, by rfl⟩ : syracuseStep 48098461 = 18036923) B18036923
theorem B64131281 : Blo 1024605 64131281 := bstep (se 2 (by rfl) ⟨24049230, by rfl⟩ : syracuseStep 64131281 = 48098461) B48098461
theorem B42754187 : Blo 1024605 42754187 := bstep (se 1 (by rfl) ⟨32065640, by rfl⟩ : syracuseStep 42754187 = 64131281) B64131281
theorem B114011165 : Blo 1024605 114011165 := bstep (se 3 (by rfl) ⟨21377093, by rfl⟩ : syracuseStep 114011165 = 42754187) B42754187
theorem B76007443 : Blo 1024605 76007443 := bstep (se 1 (by rfl) ⟨57005582, by rfl⟩ : syracuseStep 76007443 = 114011165) B114011165
theorem B101343257 : Blo 1024605 101343257 := bstep (se 2 (by rfl) ⟨38003721, by rfl⟩ : syracuseStep 101343257 = 76007443) B76007443
theorem B67562171 : Blo 1024605 67562171 := bstep (se 1 (by rfl) ⟨50671628, by rfl⟩ : syracuseStep 67562171 = 101343257) B101343257
theorem B45041447 : Blo 1024605 45041447 := bstep (se 1 (by rfl) ⟨33781085, by rfl⟩ : syracuseStep 45041447 = 67562171) B67562171
theorem B30027631 : Blo 1024605 30027631 := bstep (se 1 (by rfl) ⟨22520723, by rfl⟩ : syracuseStep 30027631 = 45041447) B45041447
theorem B40036841 : Blo 1024605 40036841 := bstep (se 2 (by rfl) ⟨15013815, by rfl⟩ : syracuseStep 40036841 = 30027631) B30027631
theorem B26691227 : Blo 1024605 26691227 := bstep (se 1 (by rfl) ⟨20018420, by rfl⟩ : syracuseStep 26691227 = 40036841) B40036841
theorem B17794151 : Blo 1024605 17794151 := bstep (se 1 (by rfl) ⟨13345613, by rfl⟩ : syracuseStep 17794151 = 26691227) B26691227
theorem B11862767 : Blo 1024605 11862767 := bstep (se 1 (by rfl) ⟨8897075, by rfl⟩ : syracuseStep 11862767 = 17794151) B17794151
theorem B7908511 : Blo 1024605 7908511 := bstep (se 1 (by rfl) ⟨5931383, by rfl⟩ : syracuseStep 7908511 = 11862767) B11862767
theorem B10544681 : Blo 1024605 10544681 := bstep (se 2 (by rfl) ⟨3954255, by rfl⟩ : syracuseStep 10544681 = 7908511) B7908511
theorem B28119149 : Blo 1024605 28119149 := bstep (se 3 (by rfl) ⟨5272340, by rfl⟩ : syracuseStep 28119149 = 10544681) B10544681
theorem B18746099 : Blo 1024605 18746099 := bstep (se 1 (by rfl) ⟨14059574, by rfl⟩ : syracuseStep 18746099 = 28119149) B28119149
theorem B12497399 : Blo 1024605 12497399 := bstep (se 1 (by rfl) ⟨9373049, by rfl⟩ : syracuseStep 12497399 = 18746099) B18746099
theorem B8331599 : Blo 1024605 8331599 := bstep (se 1 (by rfl) ⟨6248699, by rfl⟩ : syracuseStep 8331599 = 12497399) B12497399
theorem B22217597 : Blo 1024605 22217597 := bstep (se 3 (by rfl) ⟨4165799, by rfl⟩ : syracuseStep 22217597 = 8331599) B8331599
theorem B14811731 : Blo 1024605 14811731 := bstep (se 1 (by rfl) ⟨11108798, by rfl⟩ : syracuseStep 14811731 = 22217597) B22217597
theorem B9874487 : Blo 1024605 9874487 := bstep (se 1 (by rfl) ⟨7405865, by rfl⟩ : syracuseStep 9874487 = 14811731) B14811731
theorem B6582991 : Blo 1024605 6582991 := bstep (se 1 (by rfl) ⟨4937243, by rfl⟩ : syracuseStep 6582991 = 9874487) B9874487
theorem B8777321 : Blo 1024605 8777321 := bstep (se 2 (by rfl) ⟨3291495, by rfl⟩ : syracuseStep 8777321 = 6582991) B6582991
theorem B5851547 : Blo 1024605 5851547 := bstep (se 1 (by rfl) ⟨4388660, by rfl⟩ : syracuseStep 5851547 = 8777321) B8777321
theorem B3901031 : Blo 1024605 3901031 := bstep (se 1 (by rfl) ⟨2925773, by rfl⟩ : syracuseStep 3901031 = 5851547) B5851547
theorem B2600687 : Blo 1024605 2600687 := bstep (se 1 (by rfl) ⟨1950515, by rfl⟩ : syracuseStep 2600687 = 3901031) B3901031
theorem B1733791 : Blo 1024605 1733791 := bstep (se 1 (by rfl) ⟨1300343, by rfl⟩ : syracuseStep 1733791 = 2600687) B2600687
theorem B2311721 : Blo 1024605 2311721 := bstep (se 2 (by rfl) ⟨866895, by rfl⟩ : syracuseStep 2311721 = 1733791) B1733791
theorem B1541147 : Blo 1024605 1541147 := bstep (se 1 (by rfl) ⟨1155860, by rfl⟩ : syracuseStep 1541147 = 2311721) B2311721
theorem B1027431 : Blo 1024605 1027431 := bstep (se 1 (by rfl) ⟨770573, by rfl⟩ : syracuseStep 1027431 = 1541147) B1541147

theorem C0 (j : ℕ) (h1 : 256151 ≤ j) (h2 : j ≤ 256850) : Blo 1024605 (4 * j + 3) := by
  interval_cases j
  · exact B1024607
  · exact B1024611
  · exact B1024615
  · exact B1024619
  · exact B1024623
  · exact B1024627
  · exact B1024631
  · exact B1024635
  · exact B1024639
  · exact B1024643
  · exact B1024647
  · exact B1024651
  · exact B1024655
  · exact B1024659
  · exact B1024663
  · exact B1024667
  · exact B1024671
  · exact B1024675
  · exact B1024679
  · exact B1024683
  · exact B1024687
  · exact B1024691
  · exact B1024695
  · exact B1024699
  · exact B1024703
  · exact B1024707
  · exact B1024711
  · exact B1024715
  · exact B1024719
  · exact B1024723
  · exact B1024727
  · exact B1024731
  · exact B1024735
  · exact B1024739
  · exact B1024743
  · exact B1024747
  · exact B1024751
  · exact B1024755
  · exact B1024759
  · exact B1024763
  · exact B1024767
  · exact B1024771
  · exact B1024775
  · exact B1024779
  · exact B1024783
  · exact B1024787
  · exact B1024791
  · exact B1024795
  · exact B1024799
  · exact B1024803
  · exact B1024807
  · exact B1024811
  · exact B1024815
  · exact B1024819
  · exact B1024823
  · exact B1024827
  · exact B1024831
  · exact B1024835
  · exact B1024839
  · exact B1024843
  · exact B1024847
  · exact B1024851
  · exact B1024855
  · exact B1024859
  · exact B1024863
  · exact B1024867
  · exact B1024871
  · exact B1024875
  · exact B1024879
  · exact B1024883
  · exact B1024887
  · exact B1024891
  · exact B1024895
  · exact B1024899
  · exact B1024903
  · exact B1024907
  · exact B1024911
  · exact B1024915
  · exact B1024919
  · exact B1024923
  · exact B1024927
  · exact B1024931
  · exact B1024935
  · exact B1024939
  · exact B1024943
  · exact B1024947
  · exact B1024951
  · exact B1024955
  · exact B1024959
  · exact B1024963
  · exact B1024967
  · exact B1024971
  · exact B1024975
  · exact B1024979
  · exact B1024983
  · exact B1024987
  · exact B1024991
  · exact B1024995
  · exact B1024999
  · exact B1025003
  · exact B1025007
  · exact B1025011
  · exact B1025015
  · exact B1025019
  · exact B1025023
  · exact B1025027
  · exact B1025031
  · exact B1025035
  · exact B1025039
  · exact B1025043
  · exact B1025047
  · exact B1025051
  · exact B1025055
  · exact B1025059
  · exact B1025063
  · exact B1025067
  · exact B1025071
  · exact B1025075
  · exact B1025079
  · exact B1025083
  · exact B1025087
  · exact B1025091
  · exact B1025095
  · exact B1025099
  · exact B1025103
  · exact B1025107
  · exact B1025111
  · exact B1025115
  · exact B1025119
  · exact B1025123
  · exact B1025127
  · exact B1025131
  · exact B1025135
  · exact B1025139
  · exact B1025143
  · exact B1025147
  · exact B1025151
  · exact B1025155
  · exact B1025159
  · exact B1025163
  · exact B1025167
  · exact B1025171
  · exact B1025175
  · exact B1025179
  · exact B1025183
  · exact B1025187
  · exact B1025191
  · exact B1025195
  · exact B1025199
  · exact B1025203
  · exact B1025207
  · exact B1025211
  · exact B1025215
  · exact B1025219
  · exact B1025223
  · exact B1025227
  · exact B1025231
  · exact B1025235
  · exact B1025239
  · exact B1025243
  · exact B1025247
  · exact B1025251
  · exact B1025255
  · exact B1025259
  · exact B1025263
  · exact B1025267
  · exact B1025271
  · exact B1025275
  · exact B1025279
  · exact B1025283
  · exact B1025287
  · exact B1025291
  · exact B1025295
  · exact B1025299
  · exact B1025303
  · exact B1025307
  · exact B1025311
  · exact B1025315
  · exact B1025319
  · exact B1025323
  · exact B1025327
  · exact B1025331
  · exact B1025335
  · exact B1025339
  · exact B1025343
  · exact B1025347
  · exact B1025351
  · exact B1025355
  · exact B1025359
  · exact B1025363
  · exact B1025367
  · exact B1025371
  · exact B1025375
  · exact B1025379
  · exact B1025383
  · exact B1025387
  · exact B1025391
  · exact B1025395
  · exact B1025399
  · exact B1025403
  · exact B1025407
  · exact B1025411
  · exact B1025415
  · exact B1025419
  · exact B1025423
  · exact B1025427
  · exact B1025431
  · exact B1025435
  · exact B1025439
  · exact B1025443
  · exact B1025447
  · exact B1025451
  · exact B1025455
  · exact B1025459
  · exact B1025463
  · exact B1025467
  · exact B1025471
  · exact B1025475
  · exact B1025479
  · exact B1025483
  · exact B1025487
  · exact B1025491
  · exact B1025495
  · exact B1025499
  · exact B1025503
  · exact B1025507
  · exact B1025511
  · exact B1025515
  · exact B1025519
  · exact B1025523
  · exact B1025527
  · exact B1025531
  · exact B1025535
  · exact B1025539
  · exact B1025543
  · exact B1025547
  · exact B1025551
  · exact B1025555
  · exact B1025559
  · exact B1025563
  · exact B1025567
  · exact B1025571
  · exact B1025575
  · exact B1025579
  · exact B1025583
  · exact B1025587
  · exact B1025591
  · exact B1025595
  · exact B1025599
  · exact B1025603
  · exact B1025607
  · exact B1025611
  · exact B1025615
  · exact B1025619
  · exact B1025623
  · exact B1025627
  · exact B1025631
  · exact B1025635
  · exact B1025639
  · exact B1025643
  · exact B1025647
  · exact B1025651
  · exact B1025655
  · exact B1025659
  · exact B1025663
  · exact B1025667
  · exact B1025671
  · exact B1025675
  · exact B1025679
  · exact B1025683
  · exact B1025687
  · exact B1025691
  · exact B1025695
  · exact B1025699
  · exact B1025703
  · exact B1025707
  · exact B1025711
  · exact B1025715
  · exact B1025719
  · exact B1025723
  · exact B1025727
  · exact B1025731
  · exact B1025735
  · exact B1025739
  · exact B1025743
  · exact B1025747
  · exact B1025751
  · exact B1025755
  · exact B1025759
  · exact B1025763
  · exact B1025767
  · exact B1025771
  · exact B1025775
  · exact B1025779
  · exact B1025783
  · exact B1025787
  · exact B1025791
  · exact B1025795
  · exact B1025799
  · exact B1025803
  · exact B1025807
  · exact B1025811
  · exact B1025815
  · exact B1025819
  · exact B1025823
  · exact B1025827
  · exact B1025831
  · exact B1025835
  · exact B1025839
  · exact B1025843
  · exact B1025847
  · exact B1025851
  · exact B1025855
  · exact B1025859
  · exact B1025863
  · exact B1025867
  · exact B1025871
  · exact B1025875
  · exact B1025879
  · exact B1025883
  · exact B1025887
  · exact B1025891
  · exact B1025895
  · exact B1025899
  · exact B1025903
  · exact B1025907
  · exact B1025911
  · exact B1025915
  · exact B1025919
  · exact B1025923
  · exact B1025927
  · exact B1025931
  · exact B1025935
  · exact B1025939
  · exact B1025943
  · exact B1025947
  · exact B1025951
  · exact B1025955
  · exact B1025959
  · exact B1025963
  · exact B1025967
  · exact B1025971
  · exact B1025975
  · exact B1025979
  · exact B1025983
  · exact B1025987
  · exact B1025991
  · exact B1025995
  · exact B1025999
  · exact B1026003
  · exact B1026007
  · exact B1026011
  · exact B1026015
  · exact B1026019
  · exact B1026023
  · exact B1026027
  · exact B1026031
  · exact B1026035
  · exact B1026039
  · exact B1026043
  · exact B1026047
  · exact B1026051
  · exact B1026055
  · exact B1026059
  · exact B1026063
  · exact B1026067
  · exact B1026071
  · exact B1026075
  · exact B1026079
  · exact B1026083
  · exact B1026087
  · exact B1026091
  · exact B1026095
  · exact B1026099
  · exact B1026103
  · exact B1026107
  · exact B1026111
  · exact B1026115
  · exact B1026119
  · exact B1026123
  · exact B1026127
  · exact B1026131
  · exact B1026135
  · exact B1026139
  · exact B1026143
  · exact B1026147
  · exact B1026151
  · exact B1026155
  · exact B1026159
  · exact B1026163
  · exact B1026167
  · exact B1026171
  · exact B1026175
  · exact B1026179
  · exact B1026183
  · exact B1026187
  · exact B1026191
  · exact B1026195
  · exact B1026199
  · exact B1026203
  · exact B1026207
  · exact B1026211
  · exact B1026215
  · exact B1026219
  · exact B1026223
  · exact B1026227
  · exact B1026231
  · exact B1026235
  · exact B1026239
  · exact B1026243
  · exact B1026247
  · exact B1026251
  · exact B1026255
  · exact B1026259
  · exact B1026263
  · exact B1026267
  · exact B1026271
  · exact B1026275
  · exact B1026279
  · exact B1026283
  · exact B1026287
  · exact B1026291
  · exact B1026295
  · exact B1026299
  · exact B1026303
  · exact B1026307
  · exact B1026311
  · exact B1026315
  · exact B1026319
  · exact B1026323
  · exact B1026327
  · exact B1026331
  · exact B1026335
  · exact B1026339
  · exact B1026343
  · exact B1026347
  · exact B1026351
  · exact B1026355
  · exact B1026359
  · exact B1026363
  · exact B1026367
  · exact B1026371
  · exact B1026375
  · exact B1026379
  · exact B1026383
  · exact B1026387
  · exact B1026391
  · exact B1026395
  · exact B1026399
  · exact B1026403
  · exact B1026407
  · exact B1026411
  · exact B1026415
  · exact B1026419
  · exact B1026423
  · exact B1026427
  · exact B1026431
  · exact B1026435
  · exact B1026439
  · exact B1026443
  · exact B1026447
  · exact B1026451
  · exact B1026455
  · exact B1026459
  · exact B1026463
  · exact B1026467
  · exact B1026471
  · exact B1026475
  · exact B1026479
  · exact B1026483
  · exact B1026487
  · exact B1026491
  · exact B1026495
  · exact B1026499
  · exact B1026503
  · exact B1026507
  · exact B1026511
  · exact B1026515
  · exact B1026519
  · exact B1026523
  · exact B1026527
  · exact B1026531
  · exact B1026535
  · exact B1026539
  · exact B1026543
  · exact B1026547
  · exact B1026551
  · exact B1026555
  · exact B1026559
  · exact B1026563
  · exact B1026567
  · exact B1026571
  · exact B1026575
  · exact B1026579
  · exact B1026583
  · exact B1026587
  · exact B1026591
  · exact B1026595
  · exact B1026599
  · exact B1026603
  · exact B1026607
  · exact B1026611
  · exact B1026615
  · exact B1026619
  · exact B1026623
  · exact B1026627
  · exact B1026631
  · exact B1026635
  · exact B1026639
  · exact B1026643
  · exact B1026647
  · exact B1026651
  · exact B1026655
  · exact B1026659
  · exact B1026663
  · exact B1026667
  · exact B1026671
  · exact B1026675
  · exact B1026679
  · exact B1026683
  · exact B1026687
  · exact B1026691
  · exact B1026695
  · exact B1026699
  · exact B1026703
  · exact B1026707
  · exact B1026711
  · exact B1026715
  · exact B1026719
  · exact B1026723
  · exact B1026727
  · exact B1026731
  · exact B1026735
  · exact B1026739
  · exact B1026743
  · exact B1026747
  · exact B1026751
  · exact B1026755
  · exact B1026759
  · exact B1026763
  · exact B1026767
  · exact B1026771
  · exact B1026775
  · exact B1026779
  · exact B1026783
  · exact B1026787
  · exact B1026791
  · exact B1026795
  · exact B1026799
  · exact B1026803
  · exact B1026807
  · exact B1026811
  · exact B1026815
  · exact B1026819
  · exact B1026823
  · exact B1026827
  · exact B1026831
  · exact B1026835
  · exact B1026839
  · exact B1026843
  · exact B1026847
  · exact B1026851
  · exact B1026855
  · exact B1026859
  · exact B1026863
  · exact B1026867
  · exact B1026871
  · exact B1026875
  · exact B1026879
  · exact B1026883
  · exact B1026887
  · exact B1026891
  · exact B1026895
  · exact B1026899
  · exact B1026903
  · exact B1026907
  · exact B1026911
  · exact B1026915
  · exact B1026919
  · exact B1026923
  · exact B1026927
  · exact B1026931
  · exact B1026935
  · exact B1026939
  · exact B1026943
  · exact B1026947
  · exact B1026951
  · exact B1026955
  · exact B1026959
  · exact B1026963
  · exact B1026967
  · exact B1026971
  · exact B1026975
  · exact B1026979
  · exact B1026983
  · exact B1026987
  · exact B1026991
  · exact B1026995
  · exact B1026999
  · exact B1027003
  · exact B1027007
  · exact B1027011
  · exact B1027015
  · exact B1027019
  · exact B1027023
  · exact B1027027
  · exact B1027031
  · exact B1027035
  · exact B1027039
  · exact B1027043
  · exact B1027047
  · exact B1027051
  · exact B1027055
  · exact B1027059
  · exact B1027063
  · exact B1027067
  · exact B1027071
  · exact B1027075
  · exact B1027079
  · exact B1027083
  · exact B1027087
  · exact B1027091
  · exact B1027095
  · exact B1027099
  · exact B1027103
  · exact B1027107
  · exact B1027111
  · exact B1027115
  · exact B1027119
  · exact B1027123
  · exact B1027127
  · exact B1027131
  · exact B1027135
  · exact B1027139
  · exact B1027143
  · exact B1027147
  · exact B1027151
  · exact B1027155
  · exact B1027159
  · exact B1027163
  · exact B1027167
  · exact B1027171
  · exact B1027175
  · exact B1027179
  · exact B1027183
  · exact B1027187
  · exact B1027191
  · exact B1027195
  · exact B1027199
  · exact B1027203
  · exact B1027207
  · exact B1027211
  · exact B1027215
  · exact B1027219
  · exact B1027223
  · exact B1027227
  · exact B1027231
  · exact B1027235
  · exact B1027239
  · exact B1027243
  · exact B1027247
  · exact B1027251
  · exact B1027255
  · exact B1027259
  · exact B1027263
  · exact B1027267
  · exact B1027271
  · exact B1027275
  · exact B1027279
  · exact B1027283
  · exact B1027287
  · exact B1027291
  · exact B1027295
  · exact B1027299
  · exact B1027303
  · exact B1027307
  · exact B1027311
  · exact B1027315
  · exact B1027319
  · exact B1027323
  · exact B1027327
  · exact B1027331
  · exact B1027335
  · exact B1027339
  · exact B1027343
  · exact B1027347
  · exact B1027351
  · exact B1027355
  · exact B1027359
  · exact B1027363
  · exact B1027367
  · exact B1027371
  · exact B1027375
  · exact B1027379
  · exact B1027383
  · exact B1027387
  · exact B1027391
  · exact B1027395
  · exact B1027399
  · exact B1027403

theorem C1 (j : ℕ) (h1 : 256851 ≤ j) (h2 : j ≤ 257150) : Blo 1024605 (4 * j + 3) := by
  interval_cases j
  · exact B1027407
  · exact B1027411
  · exact B1027415
  · exact B1027419
  · exact B1027423
  · exact B1027427
  · exact B1027431
  · exact B1027435
  · exact B1027439
  · exact B1027443
  · exact B1027447
  · exact B1027451
  · exact B1027455
  · exact B1027459
  · exact B1027463
  · exact B1027467
  · exact B1027471
  · exact B1027475
  · exact B1027479
  · exact B1027483
  · exact B1027487
  · exact B1027491
  · exact B1027495
  · exact B1027499
  · exact B1027503
  · exact B1027507
  · exact B1027511
  · exact B1027515
  · exact B1027519
  · exact B1027523
  · exact B1027527
  · exact B1027531
  · exact B1027535
  · exact B1027539
  · exact B1027543
  · exact B1027547
  · exact B1027551
  · exact B1027555
  · exact B1027559
  · exact B1027563
  · exact B1027567
  · exact B1027571
  · exact B1027575
  · exact B1027579
  · exact B1027583
  · exact B1027587
  · exact B1027591
  · exact B1027595
  · exact B1027599
  · exact B1027603
  · exact B1027607
  · exact B1027611
  · exact B1027615
  · exact B1027619
  · exact B1027623
  · exact B1027627
  · exact B1027631
  · exact B1027635
  · exact B1027639
  · exact B1027643
  · exact B1027647
  · exact B1027651
  · exact B1027655
  · exact B1027659
  · exact B1027663
  · exact B1027667
  · exact B1027671
  · exact B1027675
  · exact B1027679
  · exact B1027683
  · exact B1027687
  · exact B1027691
  · exact B1027695
  · exact B1027699
  · exact B1027703
  · exact B1027707
  · exact B1027711
  · exact B1027715
  · exact B1027719
  · exact B1027723
  · exact B1027727
  · exact B1027731
  · exact B1027735
  · exact B1027739
  · exact B1027743
  · exact B1027747
  · exact B1027751
  · exact B1027755
  · exact B1027759
  · exact B1027763
  · exact B1027767
  · exact B1027771
  · exact B1027775
  · exact B1027779
  · exact B1027783
  · exact B1027787
  · exact B1027791
  · exact B1027795
  · exact B1027799
  · exact B1027803
  · exact B1027807
  · exact B1027811
  · exact B1027815
  · exact B1027819
  · exact B1027823
  · exact B1027827
  · exact B1027831
  · exact B1027835
  · exact B1027839
  · exact B1027843
  · exact B1027847
  · exact B1027851
  · exact B1027855
  · exact B1027859
  · exact B1027863
  · exact B1027867
  · exact B1027871
  · exact B1027875
  · exact B1027879
  · exact B1027883
  · exact B1027887
  · exact B1027891
  · exact B1027895
  · exact B1027899
  · exact B1027903
  · exact B1027907
  · exact B1027911
  · exact B1027915
  · exact B1027919
  · exact B1027923
  · exact B1027927
  · exact B1027931
  · exact B1027935
  · exact B1027939
  · exact B1027943
  · exact B1027947
  · exact B1027951
  · exact B1027955
  · exact B1027959
  · exact B1027963
  · exact B1027967
  · exact B1027971
  · exact B1027975
  · exact B1027979
  · exact B1027983
  · exact B1027987
  · exact B1027991
  · exact B1027995
  · exact B1027999
  · exact B1028003
  · exact B1028007
  · exact B1028011
  · exact B1028015
  · exact B1028019
  · exact B1028023
  · exact B1028027
  · exact B1028031
  · exact B1028035
  · exact B1028039
  · exact B1028043
  · exact B1028047
  · exact B1028051
  · exact B1028055
  · exact B1028059
  · exact B1028063
  · exact B1028067
  · exact B1028071
  · exact B1028075
  · exact B1028079
  · exact B1028083
  · exact B1028087
  · exact B1028091
  · exact B1028095
  · exact B1028099
  · exact B1028103
  · exact B1028107
  · exact B1028111
  · exact B1028115
  · exact B1028119
  · exact B1028123
  · exact B1028127
  · exact B1028131
  · exact B1028135
  · exact B1028139
  · exact B1028143
  · exact B1028147
  · exact B1028151
  · exact B1028155
  · exact B1028159
  · exact B1028163
  · exact B1028167
  · exact B1028171
  · exact B1028175
  · exact B1028179
  · exact B1028183
  · exact B1028187
  · exact B1028191
  · exact B1028195
  · exact B1028199
  · exact B1028203
  · exact B1028207
  · exact B1028211
  · exact B1028215
  · exact B1028219
  · exact B1028223
  · exact B1028227
  · exact B1028231
  · exact B1028235
  · exact B1028239
  · exact B1028243
  · exact B1028247
  · exact B1028251
  · exact B1028255
  · exact B1028259
  · exact B1028263
  · exact B1028267
  · exact B1028271
  · exact B1028275
  · exact B1028279
  · exact B1028283
  · exact B1028287
  · exact B1028291
  · exact B1028295
  · exact B1028299
  · exact B1028303
  · exact B1028307
  · exact B1028311
  · exact B1028315
  · exact B1028319
  · exact B1028323
  · exact B1028327
  · exact B1028331
  · exact B1028335
  · exact B1028339
  · exact B1028343
  · exact B1028347
  · exact B1028351
  · exact B1028355
  · exact B1028359
  · exact B1028363
  · exact B1028367
  · exact B1028371
  · exact B1028375
  · exact B1028379
  · exact B1028383
  · exact B1028387
  · exact B1028391
  · exact B1028395
  · exact B1028399
  · exact B1028403
  · exact B1028407
  · exact B1028411
  · exact B1028415
  · exact B1028419
  · exact B1028423
  · exact B1028427
  · exact B1028431
  · exact B1028435
  · exact B1028439
  · exact B1028443
  · exact B1028447
  · exact B1028451
  · exact B1028455
  · exact B1028459
  · exact B1028463
  · exact B1028467
  · exact B1028471
  · exact B1028475
  · exact B1028479
  · exact B1028483
  · exact B1028487
  · exact B1028491
  · exact B1028495
  · exact B1028499
  · exact B1028503
  · exact B1028507
  · exact B1028511
  · exact B1028515
  · exact B1028519
  · exact B1028523
  · exact B1028527
  · exact B1028531
  · exact B1028535
  · exact B1028539
  · exact B1028543
  · exact B1028547
  · exact B1028551
  · exact B1028555
  · exact B1028559
  · exact B1028563
  · exact B1028567
  · exact B1028571
  · exact B1028575
  · exact B1028579
  · exact B1028583
  · exact B1028587
  · exact B1028591
  · exact B1028595
  · exact B1028599
  · exact B1028603

theorem solution (m : ℕ) (hlo : 1024605 ≤ m) (hhi : m ≤ 1028605) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 256151 ≤ j := by omega
    have hj2 : j ≤ 257150 := by omega
    have hb : Blo 1024605 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 256851 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
