-- Prove2me | solution 1 for syracuse_descends_range_1823613_1825613
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:57:25.870988+00:00
-- url     : https://prove2.me/submissions/229808a7-8a06-49ed-b1c2-dec8434e41ed

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


theorem B4104197 : Blo 1823613 4104197 := bbase (se 4 (by rfl) ⟨384768, by rfl⟩ : syracuseStep 4104197 = 769537) (by norm_num)
theorem B2736149 : Blo 1823613 2736149 := bbase (se 6 (by rfl) ⟨64128, by rfl⟩ : syracuseStep 2736149 = 128257) (by norm_num)
theorem B2736173 : Blo 1823613 2736173 := bbase (se 3 (by rfl) ⟨513032, by rfl⟩ : syracuseStep 2736173 = 1026065) (by norm_num)
theorem B10395701 : Blo 1823613 10395701 := bbase (se 5 (by rfl) ⟨487298, by rfl⟩ : syracuseStep 10395701 = 974597) (by norm_num)
theorem B4620341 : Blo 1823613 4620341 := bbase (se 5 (by rfl) ⟨216578, by rfl⟩ : syracuseStep 4620341 = 433157) (by norm_num)
theorem B2736197 : Blo 1823613 2736197 := bbase (se 4 (by rfl) ⟨256518, by rfl⟩ : syracuseStep 2736197 = 513037) (by norm_num)
theorem B2080837 : Blo 1823613 2080837 := bbase (se 4 (by rfl) ⟨195078, by rfl⟩ : syracuseStep 2080837 = 390157) (by norm_num)
theorem B3080261 : Blo 1823613 3080261 := bbase (se 4 (by rfl) ⟨288774, by rfl⟩ : syracuseStep 3080261 = 577549) (by norm_num)
theorem B4104269 : Blo 1823613 4104269 := bbase (se 3 (by rfl) ⟨769550, by rfl⟩ : syracuseStep 4104269 = 1539101) (by norm_num)
theorem B2310221 : Blo 1823613 2310221 := bbase (se 3 (by rfl) ⟨433166, by rfl⟩ : syracuseStep 2310221 = 866333) (by norm_num)
theorem B26312789 : Blo 1823613 26312789 := bbase (se 8 (by rfl) ⟨154176, by rfl⟩ : syracuseStep 26312789 = 308353) (by norm_num)
theorem B2736221 : Blo 1823613 2736221 := bbase (se 3 (by rfl) ⟨513041, by rfl⟩ : syracuseStep 2736221 = 1026083) (by norm_num)
theorem B3465317 : Blo 1823613 3465317 := bbase (se 4 (by rfl) ⟨324873, by rfl⟩ : syracuseStep 3465317 = 649747) (by norm_num)
theorem B2736245 : Blo 1823613 2736245 := bbase (se 5 (by rfl) ⟨128261, by rfl⟩ : syracuseStep 2736245 = 256523) (by norm_num)
theorem B2310277 : Blo 1823613 2310277 := bbase (se 4 (by rfl) ⟨216588, by rfl⟩ : syracuseStep 2310277 = 433177) (by norm_num)
theorem B2736269 : Blo 1823613 2736269 := bbase (se 3 (by rfl) ⟨513050, by rfl⟩ : syracuseStep 2736269 = 1026101) (by norm_num)
theorem B4104341 : Blo 1823613 4104341 := bbase (se 6 (by rfl) ⟨96195, by rfl⟩ : syracuseStep 4104341 = 192391) (by norm_num)
theorem B2736293 : Blo 1823613 2736293 := bbase (se 4 (by rfl) ⟨256527, by rfl⟩ : syracuseStep 2736293 = 513055) (by norm_num)
theorem B2736317 : Blo 1823613 2736317 := bbase (se 3 (by rfl) ⟨513059, by rfl⟩ : syracuseStep 2736317 = 1026119) (by norm_num)
theorem B3080389 : Blo 1823613 3080389 := bbase (se 4 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 3080389 = 577573) (by norm_num)
theorem B2736341 : Blo 1823613 2736341 := bbase (se 7 (by rfl) ⟨32066, by rfl⟩ : syracuseStep 2736341 = 64133) (by norm_num)
theorem B21070037 : Blo 1823613 21070037 := bbase (se 7 (by rfl) ⟨246914, by rfl⟩ : syracuseStep 21070037 = 493829) (by norm_num)
theorem B4104413 : Blo 1823613 4104413 := bbase (se 3 (by rfl) ⟨769577, by rfl⟩ : syracuseStep 4104413 = 1539155) (by norm_num)
theorem B3162341 : Blo 1823613 3162341 := bbase (se 4 (by rfl) ⟨296469, by rfl⟩ : syracuseStep 3162341 = 592939) (by norm_num)
theorem B2310373 : Blo 1823613 2310373 := bbase (se 4 (by rfl) ⟨216597, by rfl⟩ : syracuseStep 2310373 = 433195) (by norm_num)
theorem B2736365 : Blo 1823613 2736365 := bbase (se 3 (by rfl) ⟨513068, by rfl⟩ : syracuseStep 2736365 = 1026137) (by norm_num)
theorem B5193989 : Blo 1823613 5193989 := bbase (se 4 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 5193989 = 973873) (by norm_num)
theorem B2736389 : Blo 1823613 2736389 := bbase (se 4 (by rfl) ⟨256536, by rfl⟩ : syracuseStep 2736389 = 513073) (by norm_num)
theorem B26665237 : Blo 1823613 26665237 := bbase (se 6 (by rfl) ⟨624966, by rfl⟩ : syracuseStep 26665237 = 1249933) (by norm_num)
theorem B2736413 : Blo 1823613 2736413 := bbase (se 3 (by rfl) ⟨513077, by rfl⟩ : syracuseStep 2736413 = 1026155) (by norm_num)
theorem B3080477 : Blo 1823613 3080477 := bbase (se 3 (by rfl) ⟨577589, by rfl⟩ : syracuseStep 3080477 = 1155179) (by norm_num)
theorem B4104485 : Blo 1823613 4104485 := bbase (se 4 (by rfl) ⟨384795, by rfl⟩ : syracuseStep 4104485 = 769591) (by norm_num)
theorem B2081065 : Blo 1823613 2081065 := bbase (se 2 (by rfl) ⟨780399, by rfl⟩ : syracuseStep 2081065 = 1560799) (by norm_num)
theorem B2736437 : Blo 1823613 2736437 := bbase (se 5 (by rfl) ⟨128270, by rfl⟩ : syracuseStep 2736437 = 256541) (by norm_num)
theorem B2736461 : Blo 1823613 2736461 := bbase (se 3 (by rfl) ⟨513086, by rfl⟩ : syracuseStep 2736461 = 1026173) (by norm_num)
theorem B13861205 : Blo 1823613 13861205 := bbase (se 10 (by rfl) ⟨20304, by rfl⟩ : syracuseStep 13861205 = 40609) (by norm_num)
theorem B2736485 : Blo 1823613 2736485 := bbase (se 4 (by rfl) ⟨256545, by rfl⟩ : syracuseStep 2736485 = 513091) (by norm_num)
theorem B4104557 : Blo 1823613 4104557 := bbase (se 3 (by rfl) ⟨769604, by rfl⟩ : syracuseStep 4104557 = 1539209) (by norm_num)
theorem B2736509 : Blo 1823613 2736509 := bbase (se 3 (by rfl) ⟨513095, by rfl⟩ : syracuseStep 2736509 = 1026191) (by norm_num)
theorem B9240965 : Blo 1823613 9240965 := bbase (se 4 (by rfl) ⟨866340, by rfl⟩ : syracuseStep 9240965 = 1732681) (by norm_num)
theorem B3465605 : Blo 1823613 3465605 := bbase (se 4 (by rfl) ⟨324900, by rfl⟩ : syracuseStep 3465605 = 649801) (by norm_num)
theorem B4620685 : Blo 1823613 4620685 := bbase (se 3 (by rfl) ⟨866378, by rfl⟩ : syracuseStep 4620685 = 1732757) (by norm_num)
theorem B2736533 : Blo 1823613 2736533 := bbase (se 6 (by rfl) ⟨64137, by rfl⟩ : syracuseStep 2736533 = 128275) (by norm_num)
theorem B3080605 : Blo 1823613 3080605 := bbase (se 3 (by rfl) ⟨577613, by rfl⟩ : syracuseStep 3080605 = 1155227) (by norm_num)
theorem B2597285 : Blo 1823613 2597285 := bbase (se 4 (by rfl) ⟨243495, by rfl⟩ : syracuseStep 2597285 = 486991) (by norm_num)
theorem B6160805 : Blo 1823613 6160805 := bbase (se 4 (by rfl) ⟨577575, by rfl⟩ : syracuseStep 6160805 = 1155151) (by norm_num)
theorem B2736557 : Blo 1823613 2736557 := bbase (se 3 (by rfl) ⟨513104, by rfl⟩ : syracuseStep 2736557 = 1026209) (by norm_num)
theorem B4104629 : Blo 1823613 4104629 := bbase (se 5 (by rfl) ⟨192404, by rfl⟩ : syracuseStep 4104629 = 384809) (by norm_num)
theorem B2736581 : Blo 1823613 2736581 := bbase (se 4 (by rfl) ⟨256554, by rfl⟩ : syracuseStep 2736581 = 513109) (by norm_num)
theorem B2736605 : Blo 1823613 2736605 := bbase (se 3 (by rfl) ⟨513113, by rfl⟩ : syracuseStep 2736605 = 1026227) (by norm_num)
theorem B2736629 : Blo 1823613 2736629 := bbase (se 5 (by rfl) ⟨128279, by rfl⟩ : syracuseStep 2736629 = 256559) (by norm_num)
theorem B3080693 : Blo 1823613 3080693 := bbase (se 5 (by rfl) ⟨144407, by rfl⟩ : syracuseStep 3080693 = 288815) (by norm_num)
theorem B4104701 : Blo 1823613 4104701 := bbase (se 3 (by rfl) ⟨769631, by rfl⟩ : syracuseStep 4104701 = 1539263) (by norm_num)
theorem B4620797 : Blo 1823613 4620797 := bbase (se 3 (by rfl) ⟨866399, by rfl⟩ : syracuseStep 4620797 = 1732799) (by norm_num)
theorem B2736653 : Blo 1823613 2736653 := bbase (se 3 (by rfl) ⟨513122, by rfl⟩ : syracuseStep 2736653 = 1026245) (by norm_num)
theorem B6242837 : Blo 1823613 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B3465757 : Blo 1823613 3465757 := bbase (se 3 (by rfl) ⟨649829, by rfl⟩ : syracuseStep 3465757 = 1299659) (by norm_num)
theorem B2736677 : Blo 1823613 2736677 := bbase (se 4 (by rfl) ⟨256563, by rfl⟩ : syracuseStep 2736677 = 513127) (by norm_num)
theorem B2736701 : Blo 1823613 2736701 := bbase (se 3 (by rfl) ⟨513131, by rfl⟩ : syracuseStep 2736701 = 1026263) (by norm_num)
theorem B7791173 : Blo 1823613 7791173 := bbase (se 4 (by rfl) ⟨730422, by rfl⟩ : syracuseStep 7791173 = 1460845) (by norm_num)
theorem B4104773 : Blo 1823613 4104773 := bbase (se 4 (by rfl) ⟨384822, by rfl⟩ : syracuseStep 4104773 = 769645) (by norm_num)
theorem B2736725 : Blo 1823613 2736725 := bbase (se 8 (by rfl) ⟨16035, by rfl⟩ : syracuseStep 2736725 = 32071) (by norm_num)
theorem B2736749 : Blo 1823613 2736749 := bbase (se 3 (by rfl) ⟨513140, by rfl⟩ : syracuseStep 2736749 = 1026281) (by norm_num)
theorem B6242933 : Blo 1823613 6242933 := bbase (se 5 (by rfl) ⟨292637, by rfl⟩ : syracuseStep 6242933 = 585275) (by norm_num)
theorem B2736773 : Blo 1823613 2736773 := bbase (se 4 (by rfl) ⟨256572, by rfl⟩ : syracuseStep 2736773 = 513145) (by norm_num)
theorem B4104845 : Blo 1823613 4104845 := bbase (se 3 (by rfl) ⟨769658, by rfl⟩ : syracuseStep 4104845 = 1539317) (by norm_num)
theorem B2736797 : Blo 1823613 2736797 := bbase (se 3 (by rfl) ⟨513149, by rfl⟩ : syracuseStep 2736797 = 1026299) (by norm_num)
theorem B2736821 : Blo 1823613 2736821 := bbase (se 5 (by rfl) ⟨128288, by rfl⟩ : syracuseStep 2736821 = 256577) (by norm_num)
theorem B4620989 : Blo 1823613 4620989 := bbase (se 3 (by rfl) ⟨866435, by rfl⟩ : syracuseStep 4620989 = 1732871) (by norm_num)
theorem B2736845 : Blo 1823613 2736845 := bbase (se 3 (by rfl) ⟨513158, by rfl⟩ : syracuseStep 2736845 = 1026317) (by norm_num)
theorem B4104917 : Blo 1823613 4104917 := bbase (se 7 (by rfl) ⟨48104, by rfl⟩ : syracuseStep 4104917 = 96209) (by norm_num)
theorem B2736869 : Blo 1823613 2736869 := bbase (se 4 (by rfl) ⟨256581, by rfl⟩ : syracuseStep 2736869 = 513163) (by norm_num)
theorem B13853429 : Blo 1823613 13853429 := bbase (se 5 (by rfl) ⟨649379, by rfl⟩ : syracuseStep 13853429 = 1298759) (by norm_num)
theorem B7217909 : Blo 1823613 7217909 := bbase (se 5 (by rfl) ⟨338339, by rfl⟩ : syracuseStep 7217909 = 676679) (by norm_num)
theorem B2736893 : Blo 1823613 2736893 := bbase (se 3 (by rfl) ⟨513167, by rfl⟩ : syracuseStep 2736893 = 1026335) (by norm_num)
theorem B2736917 : Blo 1823613 2736917 := bbase (se 6 (by rfl) ⟨64146, by rfl⟩ : syracuseStep 2736917 = 128293) (by norm_num)
theorem B17539861 : Blo 1823613 17539861 := bbase (se 6 (by rfl) ⟨411090, by rfl⟩ : syracuseStep 17539861 = 822181) (by norm_num)
theorem B4104989 : Blo 1823613 4104989 := bbase (se 3 (by rfl) ⟨769685, by rfl⟩ : syracuseStep 4104989 = 1539371) (by norm_num)
theorem B9233189 : Blo 1823613 9233189 := bbase (se 4 (by rfl) ⟨865611, by rfl⟩ : syracuseStep 9233189 = 1731223) (by norm_num)
theorem B2736941 : Blo 1823613 2736941 := bbase (se 3 (by rfl) ⟨513176, by rfl⟩ : syracuseStep 2736941 = 1026353) (by norm_num)
theorem B2736965 : Blo 1823613 2736965 := bbase (se 4 (by rfl) ⟨256590, by rfl⟩ : syracuseStep 2736965 = 513181) (by norm_num)
theorem B6161237 : Blo 1823613 6161237 := bbase (se 9 (by rfl) ⟨18050, by rfl⟩ : syracuseStep 6161237 = 36101) (by norm_num)
theorem B2736989 : Blo 1823613 2736989 := bbase (se 3 (by rfl) ⟨513185, by rfl⟩ : syracuseStep 2736989 = 1026371) (by norm_num)
theorem B7791461 : Blo 1823613 7791461 := bbase (se 4 (by rfl) ⟨730449, by rfl⟩ : syracuseStep 7791461 = 1460899) (by norm_num)
theorem B4105061 : Blo 1823613 4105061 := bbase (se 4 (by rfl) ⟨384849, by rfl⟩ : syracuseStep 4105061 = 769699) (by norm_num)
theorem B2737013 : Blo 1823613 2737013 := bbase (se 5 (by rfl) ⟨128297, by rfl⟩ : syracuseStep 2737013 = 256595) (by norm_num)
theorem B2737037 : Blo 1823613 2737037 := bbase (se 3 (by rfl) ⟨513194, by rfl⟩ : syracuseStep 2737037 = 1026389) (by norm_num)
theorem B2737061 : Blo 1823613 2737061 := bbase (se 4 (by rfl) ⟨256599, by rfl⟩ : syracuseStep 2737061 = 513199) (by norm_num)
theorem B4105133 : Blo 1823613 4105133 := bbase (se 3 (by rfl) ⟨769712, by rfl⟩ : syracuseStep 4105133 = 1539425) (by norm_num)
theorem B2737085 : Blo 1823613 2737085 := bbase (se 3 (by rfl) ⟨513203, by rfl⟩ : syracuseStep 2737085 = 1026407) (by norm_num)
theorem B4629437 : Blo 1823613 4629437 := bbase (se 3 (by rfl) ⟨868019, by rfl⟩ : syracuseStep 4629437 = 1736039) (by norm_num)
theorem B2597837 : Blo 1823613 2597837 := bbase (se 3 (by rfl) ⟨487094, by rfl⟩ : syracuseStep 2597837 = 974189) (by norm_num)
theorem B2737109 : Blo 1823613 2737109 := bbase (se 7 (by rfl) ⟨32075, by rfl⟩ : syracuseStep 2737109 = 64151) (by norm_num)
theorem B2737133 : Blo 1823613 2737133 := bbase (se 3 (by rfl) ⟨513212, by rfl⟩ : syracuseStep 2737133 = 1026425) (by norm_num)
theorem B4105205 : Blo 1823613 4105205 := bbase (se 5 (by rfl) ⟨192431, by rfl⟩ : syracuseStep 4105205 = 384863) (by norm_num)
theorem B2081785 : Blo 1823613 2081785 := bbase (se 2 (by rfl) ⟨780669, by rfl⟩ : syracuseStep 2081785 = 1561339) (by norm_num)
theorem B2737157 : Blo 1823613 2737157 := bbase (se 4 (by rfl) ⟨256608, by rfl⟩ : syracuseStep 2737157 = 513217) (by norm_num)
theorem B2737181 : Blo 1823613 2737181 := bbase (se 3 (by rfl) ⟨513221, by rfl⟩ : syracuseStep 2737181 = 1026443) (by norm_num)
theorem B2737205 : Blo 1823613 2737205 := bbase (se 5 (by rfl) ⟨128306, by rfl⟩ : syracuseStep 2737205 = 256613) (by norm_num)
theorem B14238773 : Blo 1823613 14238773 := bbase (se 5 (by rfl) ⟨667442, by rfl⟩ : syracuseStep 14238773 = 1334885) (by norm_num)
theorem B4105277 : Blo 1823613 4105277 := bbase (se 3 (by rfl) ⟨769739, by rfl⟩ : syracuseStep 4105277 = 1539479) (by norm_num)
theorem B2737229 : Blo 1823613 2737229 := bbase (se 3 (by rfl) ⟨513230, by rfl⟩ : syracuseStep 2737229 = 1026461) (by norm_num)
theorem B2737253 : Blo 1823613 2737253 := bbase (se 4 (by rfl) ⟨256617, by rfl⟩ : syracuseStep 2737253 = 513235) (by norm_num)
theorem B2737277 : Blo 1823613 2737277 := bbase (se 3 (by rfl) ⟨513239, by rfl⟩ : syracuseStep 2737277 = 1026479) (by norm_num)
theorem B4105349 : Blo 1823613 4105349 := bbase (se 4 (by rfl) ⟨384876, by rfl⟩ : syracuseStep 4105349 = 769753) (by norm_num)
theorem B2737301 : Blo 1823613 2737301 := bbase (se 6 (by rfl) ⟨64155, by rfl⟩ : syracuseStep 2737301 = 128311) (by norm_num)
theorem B6243493 : Blo 1823613 6243493 := bbase (se 4 (by rfl) ⟨585327, by rfl⟩ : syracuseStep 6243493 = 1170655) (by norm_num)
theorem B2737325 : Blo 1823613 2737325 := bbase (se 3 (by rfl) ⟨513248, by rfl⟩ : syracuseStep 2737325 = 1026497) (by norm_num)
theorem B1975477 : Blo 1823613 1975477 := bbase (se 5 (by rfl) ⟨92600, by rfl⟩ : syracuseStep 1975477 = 185201) (by norm_num)
theorem B2737349 : Blo 1823613 2737349 := bbase (se 4 (by rfl) ⟨256626, by rfl⟩ : syracuseStep 2737349 = 513253) (by norm_num)
theorem B4105421 : Blo 1823613 4105421 := bbase (se 3 (by rfl) ⟨769766, by rfl⟩ : syracuseStep 4105421 = 1539533) (by norm_num)
theorem B2737373 : Blo 1823613 2737373 := bbase (se 3 (by rfl) ⟨513257, by rfl⟩ : syracuseStep 2737373 = 1026515) (by norm_num)
theorem B2737397 : Blo 1823613 2737397 := bbase (se 5 (by rfl) ⟨128315, by rfl⟩ : syracuseStep 2737397 = 256631) (by norm_num)
theorem B2737421 : Blo 1823613 2737421 := bbase (se 3 (by rfl) ⟨513266, by rfl⟩ : syracuseStep 2737421 = 1026533) (by norm_num)
theorem B4105493 : Blo 1823613 4105493 := bbase (se 6 (by rfl) ⟨96222, by rfl⟩ : syracuseStep 4105493 = 192445) (by norm_num)
theorem B2737445 : Blo 1823613 2737445 := bbase (se 4 (by rfl) ⟨256635, by rfl⟩ : syracuseStep 2737445 = 513271) (by norm_num)
theorem B2737469 : Blo 1823613 2737469 := bbase (se 3 (by rfl) ⟨513275, by rfl⟩ : syracuseStep 2737469 = 1026551) (by norm_num)
theorem B4162877 : Blo 1823613 4162877 := bbase (se 3 (by rfl) ⟨780539, by rfl⟩ : syracuseStep 4162877 = 1561079) (by norm_num)
theorem B2737493 : Blo 1823613 2737493 := bbase (se 12 (by rfl) ⟨1002, by rfl⟩ : syracuseStep 2737493 = 2005) (by norm_num)
theorem B4105565 : Blo 1823613 4105565 := bbase (se 3 (by rfl) ⟨769793, by rfl⟩ : syracuseStep 4105565 = 1539587) (by norm_num)
theorem B2737517 : Blo 1823613 2737517 := bbase (se 3 (by rfl) ⟨513284, by rfl⟩ : syracuseStep 2737517 = 1026569) (by norm_num)
theorem B7398773 : Blo 1823613 7398773 := bbase (se 5 (by rfl) ⟨346817, by rfl⟩ : syracuseStep 7398773 = 693635) (by norm_num)
theorem B2737541 : Blo 1823613 2737541 := bbase (se 4 (by rfl) ⟨256644, by rfl⟩ : syracuseStep 2737541 = 513289) (by norm_num)
theorem B2737565 : Blo 1823613 2737565 := bbase (se 3 (by rfl) ⟨513293, by rfl⟩ : syracuseStep 2737565 = 1026587) (by norm_num)
theorem B5195173 : Blo 1823613 5195173 := bbase (se 4 (by rfl) ⟨487047, by rfl⟩ : syracuseStep 5195173 = 974095) (by norm_num)
theorem B4105637 : Blo 1823613 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B2737589 : Blo 1823613 2737589 := bbase (se 5 (by rfl) ⟨128324, by rfl⟩ : syracuseStep 2737589 = 256649) (by norm_num)
theorem B2737613 : Blo 1823613 2737613 := bbase (se 3 (by rfl) ⟨513302, by rfl⟩ : syracuseStep 2737613 = 1026605) (by norm_num)
theorem B2737637 : Blo 1823613 2737637 := bbase (se 4 (by rfl) ⟨256653, by rfl⟩ : syracuseStep 2737637 = 513307) (by norm_num)
theorem B4105709 : Blo 1823613 4105709 := bbase (se 3 (by rfl) ⟨769820, by rfl⟩ : syracuseStep 4105709 = 1539641) (by norm_num)
theorem B2737661 : Blo 1823613 2737661 := bbase (se 3 (by rfl) ⟨513311, by rfl⟩ : syracuseStep 2737661 = 1026623) (by norm_num)
theorem B9364997 : Blo 1823613 9364997 := bbase (se 4 (by rfl) ⟨877968, by rfl⟩ : syracuseStep 9364997 = 1755937) (by norm_num)
theorem B2737685 : Blo 1823613 2737685 := bbase (se 6 (by rfl) ⟨64164, by rfl⟩ : syracuseStep 2737685 = 128329) (by norm_num)
theorem B5842469 : Blo 1823613 5842469 := bbase (se 4 (by rfl) ⟨547731, by rfl⟩ : syracuseStep 5842469 = 1095463) (by norm_num)
theorem B2737709 : Blo 1823613 2737709 := bbase (se 3 (by rfl) ⟨513320, by rfl⟩ : syracuseStep 2737709 = 1026641) (by norm_num)
theorem B4105781 : Blo 1823613 4105781 := bbase (se 5 (by rfl) ⟨192458, by rfl⟩ : syracuseStep 4105781 = 384917) (by norm_num)
theorem B5195333 : Blo 1823613 5195333 := bbase (se 4 (by rfl) ⟨487062, by rfl⟩ : syracuseStep 5195333 = 974125) (by norm_num)
theorem B2737733 : Blo 1823613 2737733 := bbase (se 4 (by rfl) ⟨256662, by rfl⟩ : syracuseStep 2737733 = 513325) (by norm_num)
theorem B3286613 : Blo 1823613 3286613 := bbase (se 8 (by rfl) ⟨19257, by rfl⟩ : syracuseStep 3286613 = 38515) (by norm_num)
theorem B7792213 : Blo 1823613 7792213 := bbase (se 8 (by rfl) ⟨45657, by rfl⟩ : syracuseStep 7792213 = 91315) (by norm_num)
theorem B2737757 : Blo 1823613 2737757 := bbase (se 3 (by rfl) ⟨513329, by rfl⟩ : syracuseStep 2737757 = 1026659) (by norm_num)
theorem B2737781 : Blo 1823613 2737781 := bbase (se 5 (by rfl) ⟨128333, by rfl⟩ : syracuseStep 2737781 = 256667) (by norm_num)
theorem B4384381 : Blo 1823613 4384381 := bbase (se 3 (by rfl) ⟨822071, by rfl⟩ : syracuseStep 4384381 = 1644143) (by norm_num)
theorem B4105853 : Blo 1823613 4105853 := bbase (se 3 (by rfl) ⟨769847, by rfl⟩ : syracuseStep 4105853 = 1539695) (by norm_num)
theorem B2737805 : Blo 1823613 2737805 := bbase (se 3 (by rfl) ⟨513338, by rfl⟩ : syracuseStep 2737805 = 1026677) (by norm_num)
theorem B2737829 : Blo 1823613 2737829 := bbase (se 4 (by rfl) ⟨256671, by rfl⟩ : syracuseStep 2737829 = 513343) (by norm_num)
theorem B2598589 : Blo 1823613 2598589 := bbase (se 3 (by rfl) ⟨487235, by rfl⟩ : syracuseStep 2598589 = 974471) (by norm_num)
theorem B2737853 : Blo 1823613 2737853 := bbase (se 3 (by rfl) ⟨513347, by rfl⟩ : syracuseStep 2737853 = 1026695) (by norm_num)
theorem B4105925 : Blo 1823613 4105925 := bbase (se 4 (by rfl) ⟨384930, by rfl⟩ : syracuseStep 4105925 = 769861) (by norm_num)
theorem B2737877 : Blo 1823613 2737877 := bbase (se 7 (by rfl) ⟨32084, by rfl⟩ : syracuseStep 2737877 = 64169) (by norm_num)
theorem B2737901 : Blo 1823613 2737901 := bbase (se 3 (by rfl) ⟨513356, by rfl⟩ : syracuseStep 2737901 = 1026713) (by norm_num)
theorem B1976065 : Blo 1823613 1976065 := bbase (se 2 (by rfl) ⟨741024, by rfl⟩ : syracuseStep 1976065 = 1482049) (by norm_num)
theorem B2737925 : Blo 1823613 2737925 := bbase (se 4 (by rfl) ⟨256680, by rfl⟩ : syracuseStep 2737925 = 513361) (by norm_num)
theorem B4105997 : Blo 1823613 4105997 := bbase (se 3 (by rfl) ⟨769874, by rfl⟩ : syracuseStep 4105997 = 1539749) (by norm_num)
theorem B2737949 : Blo 1823613 2737949 := bbase (se 3 (by rfl) ⟨513365, by rfl⟩ : syracuseStep 2737949 = 1026731) (by norm_num)
theorem B14042933 : Blo 1823613 14042933 := bbase (se 5 (by rfl) ⟨658262, by rfl⟩ : syracuseStep 14042933 = 1316525) (by norm_num)
theorem B5195573 : Blo 1823613 5195573 := bbase (se 5 (by rfl) ⟨243542, by rfl⟩ : syracuseStep 5195573 = 487085) (by norm_num)
theorem B2737973 : Blo 1823613 2737973 := bbase (se 5 (by rfl) ⟨128342, by rfl⟩ : syracuseStep 2737973 = 256685) (by norm_num)
theorem B2737997 : Blo 1823613 2737997 := bbase (se 3 (by rfl) ⟨513374, by rfl⟩ : syracuseStep 2737997 = 1026749) (by norm_num)
theorem B4106069 : Blo 1823613 4106069 := bbase (se 9 (by rfl) ⟨12029, by rfl⟩ : syracuseStep 4106069 = 24059) (by norm_num)
theorem B2738021 : Blo 1823613 2738021 := bbase (se 4 (by rfl) ⟨256689, by rfl⟩ : syracuseStep 2738021 = 513379) (by norm_num)
theorem B6924149 : Blo 1823613 6924149 := bbase (se 5 (by rfl) ⟨324569, by rfl⟩ : syracuseStep 6924149 = 649139) (by norm_num)
theorem B2738045 : Blo 1823613 2738045 := bbase (se 3 (by rfl) ⟨513383, by rfl⟩ : syracuseStep 2738045 = 1026767) (by norm_num)
theorem B2738069 : Blo 1823613 2738069 := bbase (se 6 (by rfl) ⟨64173, by rfl⟩ : syracuseStep 2738069 = 128347) (by norm_num)
theorem B4106141 : Blo 1823613 4106141 := bbase (se 3 (by rfl) ⟨769901, by rfl⟩ : syracuseStep 4106141 = 1539803) (by norm_num)
theorem B2738093 : Blo 1823613 2738093 := bbase (se 3 (by rfl) ⟨513392, by rfl⟩ : syracuseStep 2738093 = 1026785) (by norm_num)
theorem B2738117 : Blo 1823613 2738117 := bbase (se 4 (by rfl) ⟨256698, by rfl⟩ : syracuseStep 2738117 = 513397) (by norm_num)
theorem B2738141 : Blo 1823613 2738141 := bbase (se 3 (by rfl) ⟨513401, by rfl⟩ : syracuseStep 2738141 = 1026803) (by norm_num)
theorem B4106213 : Blo 1823613 4106213 := bbase (se 4 (by rfl) ⟨384957, by rfl⟩ : syracuseStep 4106213 = 769915) (by norm_num)
theorem B5195765 : Blo 1823613 5195765 := bbase (se 5 (by rfl) ⟨243551, by rfl⟩ : syracuseStep 5195765 = 487103) (by norm_num)
theorem B2738165 : Blo 1823613 2738165 := bbase (se 5 (by rfl) ⟨128351, by rfl⟩ : syracuseStep 2738165 = 256703) (by norm_num)
theorem B2738189 : Blo 1823613 2738189 := bbase (se 3 (by rfl) ⟨513410, by rfl⟩ : syracuseStep 2738189 = 1026821) (by norm_num)
theorem B2738213 : Blo 1823613 2738213 := bbase (se 4 (by rfl) ⟨256707, by rfl⟩ : syracuseStep 2738213 = 513415) (by norm_num)
theorem B4106285 : Blo 1823613 4106285 := bbase (se 3 (by rfl) ⟨769928, by rfl⟩ : syracuseStep 4106285 = 1539857) (by norm_num)
theorem B9234485 : Blo 1823613 9234485 := bbase (se 5 (by rfl) ⟨432866, by rfl⟩ : syracuseStep 9234485 = 865733) (by norm_num)
theorem B2738237 : Blo 1823613 2738237 := bbase (se 3 (by rfl) ⟨513419, by rfl⟩ : syracuseStep 2738237 = 1026839) (by norm_num)
theorem B2738261 : Blo 1823613 2738261 := bbase (se 8 (by rfl) ⟨16044, by rfl⟩ : syracuseStep 2738261 = 32089) (by norm_num)
theorem B2738285 : Blo 1823613 2738285 := bbase (se 3 (by rfl) ⟨513428, by rfl⟩ : syracuseStep 2738285 = 1026857) (by norm_num)
theorem B4106357 : Blo 1823613 4106357 := bbase (se 5 (by rfl) ⟨192485, by rfl⟩ : syracuseStep 4106357 = 384971) (by norm_num)
theorem B2738309 : Blo 1823613 2738309 := bbase (se 4 (by rfl) ⟨256716, by rfl⟩ : syracuseStep 2738309 = 513433) (by norm_num)
theorem B6924437 : Blo 1823613 6924437 := bbase (se 6 (by rfl) ⟨162291, by rfl⟩ : syracuseStep 6924437 = 324583) (by norm_num)
theorem B2738333 : Blo 1823613 2738333 := bbase (se 3 (by rfl) ⟨513437, by rfl⟩ : syracuseStep 2738333 = 1026875) (by norm_num)
theorem B2738357 : Blo 1823613 2738357 := bbase (se 5 (by rfl) ⟨128360, by rfl⟩ : syracuseStep 2738357 = 256721) (by norm_num)
theorem B4106429 : Blo 1823613 4106429 := bbase (se 3 (by rfl) ⟨769955, by rfl⟩ : syracuseStep 4106429 = 1539911) (by norm_num)
theorem B2738381 : Blo 1823613 2738381 := bbase (se 3 (by rfl) ⟨513446, by rfl⟩ : syracuseStep 2738381 = 1026893) (by norm_num)
theorem B2738405 : Blo 1823613 2738405 := bbase (se 4 (by rfl) ⟨256725, by rfl⟩ : syracuseStep 2738405 = 513451) (by norm_num)
theorem B4106501 : Blo 1823613 4106501 := bbase (se 4 (by rfl) ⟨384984, by rfl⟩ : syracuseStep 4106501 = 769969) (by norm_num)
theorem B7792949 : Blo 1823613 7792949 := bbase (se 5 (by rfl) ⟨365294, by rfl⟩ : syracuseStep 7792949 = 730589) (by norm_num)
theorem B4106573 : Blo 1823613 4106573 := bbase (se 3 (by rfl) ⟨769982, by rfl⟩ : syracuseStep 4106573 = 1539965) (by norm_num)
theorem B4106645 : Blo 1823613 4106645 := bbase (se 6 (by rfl) ⟨96249, by rfl⟩ : syracuseStep 4106645 = 192499) (by norm_num)
theorem B7899605 : Blo 1823613 7899605 := bbase (se 7 (by rfl) ⟨92573, by rfl⟩ : syracuseStep 7899605 = 185147) (by norm_num)
theorem B4106717 : Blo 1823613 4106717 := bbase (se 3 (by rfl) ⟨770009, by rfl⟩ : syracuseStep 4106717 = 1540019) (by norm_num)
theorem B3951101 : Blo 1823613 3951101 := bbase (se 3 (by rfl) ⟨740831, by rfl⟩ : syracuseStep 3951101 = 1481663) (by norm_num)
theorem B6154757 : Blo 1823613 6154757 := bbase (se 4 (by rfl) ⟨577008, by rfl⟩ : syracuseStep 6154757 = 1154017) (by norm_num)
theorem B3287557 : Blo 1823613 3287557 := bbase (se 4 (by rfl) ⟨308208, by rfl⟩ : syracuseStep 3287557 = 616417) (by norm_num)
theorem B4106789 : Blo 1823613 4106789 := bbase (se 4 (by rfl) ⟨385011, by rfl⟩ : syracuseStep 4106789 = 770023) (by norm_num)
theorem B4106861 : Blo 1823613 4106861 := bbase (se 3 (by rfl) ⟨770036, by rfl⟩ : syracuseStep 4106861 = 1540073) (by norm_num)
theorem B4106933 : Blo 1823613 4106933 := bbase (se 5 (by rfl) ⟨192512, by rfl⟩ : syracuseStep 4106933 = 385025) (by norm_num)
theorem B4107005 : Blo 1823613 4107005 := bbase (se 3 (by rfl) ⟨770063, by rfl⟩ : syracuseStep 4107005 = 1540127) (by norm_num)
theorem B4107077 : Blo 1823613 4107077 := bbase (se 4 (by rfl) ⟨385038, by rfl⟩ : syracuseStep 4107077 = 770077) (by norm_num)
theorem B10529621 : Blo 1823613 10529621 := bbase (se 9 (by rfl) ⟨30848, by rfl⟩ : syracuseStep 10529621 = 61697) (by norm_num)
theorem B8768357 : Blo 1823613 8768357 := bbase (se 4 (by rfl) ⟨822033, by rfl⟩ : syracuseStep 8768357 = 1644067) (by norm_num)
theorem B4107149 : Blo 1823613 4107149 := bbase (se 3 (by rfl) ⟨770090, by rfl⟩ : syracuseStep 4107149 = 1540181) (by norm_num)
theorem B6155189 : Blo 1823613 6155189 := bbase (se 5 (by rfl) ⟨288524, by rfl⟩ : syracuseStep 6155189 = 577049) (by norm_num)
theorem B5196757 : Blo 1823613 5196757 := bbase (se 7 (by rfl) ⟨60899, by rfl⟩ : syracuseStep 5196757 = 121799) (by norm_num)
theorem B4107221 : Blo 1823613 4107221 := bbase (se 7 (by rfl) ⟨48131, by rfl⟩ : syracuseStep 4107221 = 96263) (by norm_num)
theorem B3288061 : Blo 1823613 3288061 := bbase (se 3 (by rfl) ⟨616511, by rfl⟩ : syracuseStep 3288061 = 1233023) (by norm_num)
theorem B4107293 : Blo 1823613 4107293 := bbase (se 3 (by rfl) ⟨770117, by rfl⟩ : syracuseStep 4107293 = 1540235) (by norm_num)
theorem B5549141 : Blo 1823613 5549141 := bbase (se 8 (by rfl) ⟨32514, by rfl⟩ : syracuseStep 5549141 = 65029) (by norm_num)
theorem B4107365 : Blo 1823613 4107365 := bbase (se 4 (by rfl) ⟨385065, by rfl⟩ : syracuseStep 4107365 = 770131) (by norm_num)
theorem B3697829 : Blo 1823613 3697829 := bbase (se 4 (by rfl) ⟨346671, by rfl⟩ : syracuseStep 3697829 = 693343) (by norm_num)
theorem B4107437 : Blo 1823613 4107437 := bbase (se 3 (by rfl) ⟨770144, by rfl⟩ : syracuseStep 4107437 = 1540289) (by norm_num)
theorem B2313461 : Blo 1823613 2313461 := bbase (se 5 (by rfl) ⟨108443, by rfl⟩ : syracuseStep 2313461 = 216887) (by norm_num)
theorem B4107509 : Blo 1823613 4107509 := bbase (se 5 (by rfl) ⟨192539, by rfl⟩ : syracuseStep 4107509 = 385079) (by norm_num)
theorem B6925621 : Blo 1823613 6925621 := bbase (se 5 (by rfl) ⟨324638, by rfl⟩ : syracuseStep 6925621 = 649277) (by norm_num)
theorem B4107581 : Blo 1823613 4107581 := bbase (se 3 (by rfl) ⟨770171, by rfl⟩ : syracuseStep 4107581 = 1540343) (by norm_num)
theorem B9235781 : Blo 1823613 9235781 := bbase (se 4 (by rfl) ⟨865854, by rfl⟩ : syracuseStep 9235781 = 1731709) (by norm_num)
theorem B6663509 : Blo 1823613 6663509 := bbase (se 11 (by rfl) ⟨4880, by rfl⟩ : syracuseStep 6663509 = 9761) (by norm_num)
theorem B52596053 : Blo 1823613 52596053 := bbase (se 11 (by rfl) ⟨38522, by rfl⟩ : syracuseStep 52596053 = 77045) (by norm_num)
theorem B6155621 : Blo 1823613 6155621 := bbase (se 4 (by rfl) ⟨577089, by rfl⟩ : syracuseStep 6155621 = 1154179) (by norm_num)
theorem B5336549 : Blo 1823613 5336549 := bbase (se 4 (by rfl) ⟨500301, by rfl⟩ : syracuseStep 5336549 = 1000603) (by norm_num)
theorem B2051581 : Blo 1823613 2051581 := bbase (se 3 (by rfl) ⟨384671, by rfl⟩ : syracuseStep 2051581 = 769343) (by norm_num)
theorem B2051617 : Blo 1823613 2051617 := bbase (se 2 (by rfl) ⟨769356, by rfl⟩ : syracuseStep 2051617 = 1538713) (by norm_num)
theorem B2051653 : Blo 1823613 2051653 := bbase (se 4 (by rfl) ⟨192342, by rfl⟩ : syracuseStep 2051653 = 384685) (by norm_num)
theorem B3042893 : Blo 1823613 3042893 := bbase (se 3 (by rfl) ⟨570542, by rfl⟩ : syracuseStep 3042893 = 1141085) (by norm_num)
theorem B6925925 : Blo 1823613 6925925 := bbase (se 4 (by rfl) ⟨649305, by rfl⟩ : syracuseStep 6925925 = 1298611) (by norm_num)
theorem B2051689 : Blo 1823613 2051689 := bbase (se 2 (by rfl) ⟨769383, by rfl⟩ : syracuseStep 2051689 = 1538767) (by norm_num)
theorem B2051725 : Blo 1823613 2051725 := bbase (se 3 (by rfl) ⟨384698, by rfl⟩ : syracuseStep 2051725 = 769397) (by norm_num)
theorem B2051761 : Blo 1823613 2051761 := bbase (se 2 (by rfl) ⟨769410, by rfl⟩ : syracuseStep 2051761 = 1538821) (by norm_num)
theorem B2051797 : Blo 1823613 2051797 := bbase (se 7 (by rfl) ⟨24044, by rfl⟩ : syracuseStep 2051797 = 48089) (by norm_num)
theorem B3895013 : Blo 1823613 3895013 := bbase (se 4 (by rfl) ⟨365157, by rfl⟩ : syracuseStep 3895013 = 730315) (by norm_num)
theorem B2051833 : Blo 1823613 2051833 := bbase (se 2 (by rfl) ⟨769437, by rfl⟩ : syracuseStep 2051833 = 1538875) (by norm_num)
theorem B6156053 : Blo 1823613 6156053 := bbase (se 6 (by rfl) ⟨144282, by rfl⟩ : syracuseStep 6156053 = 288565) (by norm_num)
theorem B2051869 : Blo 1823613 2051869 := bbase (se 3 (by rfl) ⟨384725, by rfl⟩ : syracuseStep 2051869 = 769451) (by norm_num)
theorem B2051905 : Blo 1823613 2051905 := bbase (se 2 (by rfl) ⟨769464, by rfl⟩ : syracuseStep 2051905 = 1538929) (by norm_num)
theorem B2051941 : Blo 1823613 2051941 := bbase (se 4 (by rfl) ⟨192369, by rfl⟩ : syracuseStep 2051941 = 384739) (by norm_num)
theorem B3288941 : Blo 1823613 3288941 := bbase (se 3 (by rfl) ⟨616676, by rfl⟩ : syracuseStep 3288941 = 1233353) (by norm_num)
theorem B2051977 : Blo 1823613 2051977 := bbase (se 2 (by rfl) ⟨769491, by rfl⟩ : syracuseStep 2051977 = 1538983) (by norm_num)
theorem B2052013 : Blo 1823613 2052013 := bbase (se 3 (by rfl) ⟨384752, by rfl⟩ : syracuseStep 2052013 = 769505) (by norm_num)
theorem B2052049 : Blo 1823613 2052049 := bbase (se 2 (by rfl) ⟨769518, by rfl⟩ : syracuseStep 2052049 = 1539037) (by norm_num)
theorem B4616149 : Blo 1823613 4616149 := bbase (se 7 (by rfl) ⟨54095, by rfl⟩ : syracuseStep 4616149 = 108191) (by norm_num)
theorem B2052085 : Blo 1823613 2052085 := bbase (se 5 (by rfl) ⟨96191, by rfl⟩ : syracuseStep 2052085 = 192383) (by norm_num)
theorem B2052121 : Blo 1823613 2052121 := bbase (se 2 (by rfl) ⟨769545, by rfl⟩ : syracuseStep 2052121 = 1539091) (by norm_num)
theorem B5197861 : Blo 1823613 5197861 := bbase (se 4 (by rfl) ⟨487299, by rfl⟩ : syracuseStep 5197861 = 974599) (by norm_num)
theorem B2052157 : Blo 1823613 2052157 := bbase (se 3 (by rfl) ⟨384779, by rfl⟩ : syracuseStep 2052157 = 769559) (by norm_num)
theorem B4616261 : Blo 1823613 4616261 := bbase (se 4 (by rfl) ⟨432774, by rfl⟩ : syracuseStep 4616261 = 865549) (by norm_num)
theorem B3895381 : Blo 1823613 3895381 := bbase (se 8 (by rfl) ⟨22824, by rfl⟩ : syracuseStep 3895381 = 45649) (by norm_num)
theorem B2052193 : Blo 1823613 2052193 := bbase (se 2 (by rfl) ⟨769572, by rfl⟩ : syracuseStep 2052193 = 1539145) (by norm_num)
theorem B2052229 : Blo 1823613 2052229 := bbase (se 4 (by rfl) ⟨192396, by rfl⟩ : syracuseStep 2052229 = 384793) (by norm_num)
theorem B2052265 : Blo 1823613 2052265 := bbase (se 2 (by rfl) ⟨769599, by rfl⟩ : syracuseStep 2052265 = 1539199) (by norm_num)
theorem B2191541 : Blo 1823613 2191541 := bbase (se 5 (by rfl) ⟨102728, by rfl⟩ : syracuseStep 2191541 = 205457) (by norm_num)
theorem B6574277 : Blo 1823613 6574277 := bbase (se 4 (by rfl) ⟨616338, by rfl⟩ : syracuseStep 6574277 = 1232677) (by norm_num)
theorem B6156485 : Blo 1823613 6156485 := bbase (se 4 (by rfl) ⟨577170, by rfl⟩ : syracuseStep 6156485 = 1154341) (by norm_num)
theorem B2052301 : Blo 1823613 2052301 := bbase (se 3 (by rfl) ⟨384806, by rfl⟩ : syracuseStep 2052301 = 769613) (by norm_num)
theorem B2052337 : Blo 1823613 2052337 := bbase (se 2 (by rfl) ⟨769626, by rfl⟩ : syracuseStep 2052337 = 1539253) (by norm_num)
theorem B4616453 : Blo 1823613 4616453 := bbase (se 4 (by rfl) ⟨432792, by rfl⟩ : syracuseStep 4616453 = 865585) (by norm_num)
theorem B2052373 : Blo 1823613 2052373 := bbase (se 6 (by rfl) ⟨48102, by rfl⟩ : syracuseStep 2052373 = 96205) (by norm_num)
theorem B2052409 : Blo 1823613 2052409 := bbase (se 2 (by rfl) ⟨769653, by rfl⟩ : syracuseStep 2052409 = 1539307) (by norm_num)
theorem B2052445 : Blo 1823613 2052445 := bbase (se 3 (by rfl) ⟨384833, by rfl⟩ : syracuseStep 2052445 = 769667) (by norm_num)
theorem B3699037 : Blo 1823613 3699037 := bbase (se 3 (by rfl) ⟨693569, by rfl⟩ : syracuseStep 3699037 = 1387139) (by norm_num)
theorem B3289445 : Blo 1823613 3289445 := bbase (se 4 (by rfl) ⟨308385, by rfl⟩ : syracuseStep 3289445 = 616771) (by norm_num)
theorem B2052481 : Blo 1823613 2052481 := bbase (se 2 (by rfl) ⟨769680, by rfl⟩ : syracuseStep 2052481 = 1539361) (by norm_num)
theorem B2052517 : Blo 1823613 2052517 := bbase (se 4 (by rfl) ⟨192423, by rfl⟩ : syracuseStep 2052517 = 384847) (by norm_num)
theorem B2052553 : Blo 1823613 2052553 := bbase (se 2 (by rfl) ⟨769707, by rfl⟩ : syracuseStep 2052553 = 1539415) (by norm_num)
theorem B2052589 : Blo 1823613 2052589 := bbase (se 3 (by rfl) ⟨384860, by rfl⟩ : syracuseStep 2052589 = 769721) (by norm_num)
theorem B2052625 : Blo 1823613 2052625 := bbase (se 2 (by rfl) ⟨769734, by rfl⟩ : syracuseStep 2052625 = 1539469) (by norm_num)
theorem B2052661 : Blo 1823613 2052661 := bbase (se 5 (by rfl) ⟨96218, by rfl⟩ : syracuseStep 2052661 = 192437) (by norm_num)
theorem B9237077 : Blo 1823613 9237077 := bbase (se 8 (by rfl) ⟨54123, by rfl⟩ : syracuseStep 9237077 = 108247) (by norm_num)
theorem B2052697 : Blo 1823613 2052697 := bbase (se 2 (by rfl) ⟨769761, by rfl⟩ : syracuseStep 2052697 = 1539523) (by norm_num)
theorem B4616797 : Blo 1823613 4616797 := bbase (se 3 (by rfl) ⟨865649, by rfl⟩ : syracuseStep 4616797 = 1731299) (by norm_num)
theorem B6156917 : Blo 1823613 6156917 := bbase (se 5 (by rfl) ⟨288605, by rfl⟩ : syracuseStep 6156917 = 577211) (by norm_num)
theorem B2052733 : Blo 1823613 2052733 := bbase (se 3 (by rfl) ⟨384887, by rfl⟩ : syracuseStep 2052733 = 769775) (by norm_num)
theorem B2052769 : Blo 1823613 2052769 := bbase (se 2 (by rfl) ⟨769788, by rfl⟩ : syracuseStep 2052769 = 1539577) (by norm_num)
theorem B2052805 : Blo 1823613 2052805 := bbase (se 4 (by rfl) ⟨192450, by rfl⟩ : syracuseStep 2052805 = 384901) (by norm_num)
theorem B4616909 : Blo 1823613 4616909 := bbase (se 3 (by rfl) ⟨865670, by rfl⟩ : syracuseStep 4616909 = 1731341) (by norm_num)
theorem B2052841 : Blo 1823613 2052841 := bbase (se 2 (by rfl) ⟨769815, by rfl⟩ : syracuseStep 2052841 = 1539631) (by norm_num)
theorem B2052877 : Blo 1823613 2052877 := bbase (se 3 (by rfl) ⟨384914, by rfl⟩ : syracuseStep 2052877 = 769829) (by norm_num)
theorem B5550869 : Blo 1823613 5550869 := bbase (se 6 (by rfl) ⟨130098, by rfl⟩ : syracuseStep 5550869 = 260197) (by norm_num)
theorem B2052913 : Blo 1823613 2052913 := bbase (se 2 (by rfl) ⟨769842, by rfl⟩ : syracuseStep 2052913 = 1539685) (by norm_num)
theorem B2052949 : Blo 1823613 2052949 := bbase (se 9 (by rfl) ⟨6014, by rfl⟩ : syracuseStep 2052949 = 12029) (by norm_num)
theorem B2192233 : Blo 1823613 2192233 := bbase (se 2 (by rfl) ⟨822087, by rfl⟩ : syracuseStep 2192233 = 1644175) (by norm_num)
theorem B2339705 : Blo 1823613 2339705 := bbase (se 2 (by rfl) ⟨877389, by rfl⟩ : syracuseStep 2339705 = 1754779) (by norm_num)
theorem B2052985 : Blo 1823613 2052985 := bbase (se 2 (by rfl) ⟨769869, by rfl⟩ : syracuseStep 2052985 = 1539739) (by norm_num)
theorem B4617101 : Blo 1823613 4617101 := bbase (se 3 (by rfl) ⟨865706, by rfl⟩ : syracuseStep 4617101 = 1731413) (by norm_num)
theorem B2053021 : Blo 1823613 2053021 := bbase (se 3 (by rfl) ⟨384941, by rfl⟩ : syracuseStep 2053021 = 769883) (by norm_num)
theorem B2053057 : Blo 1823613 2053057 := bbase (se 2 (by rfl) ⟨769896, by rfl⟩ : syracuseStep 2053057 = 1539793) (by norm_num)
theorem B2192329 : Blo 1823613 2192329 := bbase (se 2 (by rfl) ⟨822123, by rfl⟩ : syracuseStep 2192329 = 1644247) (by norm_num)
theorem B10392533 : Blo 1823613 10392533 := bbase (se 7 (by rfl) ⟨121787, by rfl⟩ : syracuseStep 10392533 = 243575) (by norm_num)
theorem B2339813 : Blo 1823613 2339813 := bbase (se 4 (by rfl) ⟨219357, by rfl⟩ : syracuseStep 2339813 = 438715) (by norm_num)
theorem B2053093 : Blo 1823613 2053093 := bbase (se 4 (by rfl) ⟨192477, by rfl⟩ : syracuseStep 2053093 = 384955) (by norm_num)
theorem B2053129 : Blo 1823613 2053129 := bbase (se 2 (by rfl) ⟨769923, by rfl⟩ : syracuseStep 2053129 = 1539847) (by norm_num)
theorem B14242837 : Blo 1823613 14242837 := bbase (se 6 (by rfl) ⟨333816, by rfl⟩ : syracuseStep 14242837 = 667633) (by norm_num)
theorem B3462173 : Blo 1823613 3462173 := bbase (se 3 (by rfl) ⟨649157, by rfl⟩ : syracuseStep 3462173 = 1298315) (by norm_num)
theorem B6157349 : Blo 1823613 6157349 := bbase (se 4 (by rfl) ⟨577251, by rfl⟩ : syracuseStep 6157349 = 1154503) (by norm_num)
theorem B2053165 : Blo 1823613 2053165 := bbase (se 3 (by rfl) ⟨384968, by rfl⟩ : syracuseStep 2053165 = 769937) (by norm_num)
theorem B7025717 : Blo 1823613 7025717 := bbase (se 5 (by rfl) ⟨329330, by rfl⟩ : syracuseStep 7025717 = 658661) (by norm_num)
theorem B2053201 : Blo 1823613 2053201 := bbase (se 2 (by rfl) ⟨769950, by rfl⟩ : syracuseStep 2053201 = 1539901) (by norm_num)
theorem B2053237 : Blo 1823613 2053237 := bbase (se 5 (by rfl) ⟨96245, by rfl⟩ : syracuseStep 2053237 = 192491) (by norm_num)
theorem B2053273 : Blo 1823613 2053273 := bbase (se 2 (by rfl) ⟨769977, by rfl⟩ : syracuseStep 2053273 = 1539955) (by norm_num)
theorem B2921645 : Blo 1823613 2921645 := bbase (se 3 (by rfl) ⟨547808, by rfl⟩ : syracuseStep 2921645 = 1095617) (by norm_num)
theorem B15594677 : Blo 1823613 15594677 := bbase (se 5 (by rfl) ⟨731000, by rfl⟩ : syracuseStep 15594677 = 1462001) (by norm_num)
theorem B2053309 : Blo 1823613 2053309 := bbase (se 3 (by rfl) ⟨384995, by rfl⟩ : syracuseStep 2053309 = 769991) (by norm_num)
theorem B17528021 : Blo 1823613 17528021 := bbase (se 7 (by rfl) ⟨205406, by rfl⟩ : syracuseStep 17528021 = 410813) (by norm_num)
theorem B2053345 : Blo 1823613 2053345 := bbase (se 2 (by rfl) ⟨770004, by rfl⟩ : syracuseStep 2053345 = 1540009) (by norm_num)
theorem B4617445 : Blo 1823613 4617445 := bbase (se 4 (by rfl) ⟨432885, by rfl⟩ : syracuseStep 4617445 = 865771) (by norm_num)
theorem B3077365 : Blo 1823613 3077365 := bbase (se 5 (by rfl) ⟨144251, by rfl⟩ : syracuseStep 3077365 = 288503) (by norm_num)
theorem B5846261 : Blo 1823613 5846261 := bbase (se 5 (by rfl) ⟨274043, by rfl⟩ : syracuseStep 5846261 = 548087) (by norm_num)
theorem B2053381 : Blo 1823613 2053381 := bbase (se 4 (by rfl) ⟨192504, by rfl⟩ : syracuseStep 2053381 = 385009) (by norm_num)
theorem B2053417 : Blo 1823613 2053417 := bbase (se 2 (by rfl) ⟨770031, by rfl⟩ : syracuseStep 2053417 = 1540063) (by norm_num)
theorem B2921773 : Blo 1823613 2921773 := bbase (se 3 (by rfl) ⟨547832, by rfl⟩ : syracuseStep 2921773 = 1095665) (by norm_num)
theorem B15586613 : Blo 1823613 15586613 := bbase (se 5 (by rfl) ⟨730622, by rfl⟩ : syracuseStep 15586613 = 1461245) (by norm_num)
theorem B3077453 : Blo 1823613 3077453 := bbase (se 3 (by rfl) ⟨577022, by rfl⟩ : syracuseStep 3077453 = 1154045) (by norm_num)
theorem B2053453 : Blo 1823613 2053453 := bbase (se 3 (by rfl) ⟨385022, by rfl⟩ : syracuseStep 2053453 = 770045) (by norm_num)
theorem B4617557 : Blo 1823613 4617557 := bbase (se 13 (by rfl) ⟨845, by rfl⟩ : syracuseStep 4617557 = 1691) (by norm_num)
theorem B2053489 : Blo 1823613 2053489 := bbase (se 2 (by rfl) ⟨770058, by rfl⟩ : syracuseStep 2053489 = 1540117) (by norm_num)
theorem B2053525 : Blo 1823613 2053525 := bbase (se 6 (by rfl) ⟨48129, by rfl⟩ : syracuseStep 2053525 = 96259) (by norm_num)
theorem B2053561 : Blo 1823613 2053561 := bbase (se 2 (by rfl) ⟨770085, by rfl⟩ : syracuseStep 2053561 = 1540171) (by norm_num)
theorem B3077581 : Blo 1823613 3077581 := bbase (se 3 (by rfl) ⟨577046, by rfl⟩ : syracuseStep 3077581 = 1154093) (by norm_num)
theorem B6157781 : Blo 1823613 6157781 := bbase (se 7 (by rfl) ⟨72161, by rfl⟩ : syracuseStep 6157781 = 144323) (by norm_num)
theorem B2053597 : Blo 1823613 2053597 := bbase (se 3 (by rfl) ⟨385049, by rfl⟩ : syracuseStep 2053597 = 770099) (by norm_num)
theorem B2053633 : Blo 1823613 2053633 := bbase (se 2 (by rfl) ⟨770112, by rfl⟩ : syracuseStep 2053633 = 1540225) (by norm_num)
theorem B4617749 : Blo 1823613 4617749 := bbase (se 6 (by rfl) ⟨108228, by rfl⟩ : syracuseStep 4617749 = 216457) (by norm_num)
theorem B7796245 : Blo 1823613 7796245 := bbase (se 6 (by rfl) ⟨182724, by rfl⟩ : syracuseStep 7796245 = 365449) (by norm_num)
theorem B3077669 : Blo 1823613 3077669 := bbase (se 4 (by rfl) ⟨288531, by rfl⟩ : syracuseStep 3077669 = 577063) (by norm_num)
theorem B2053669 : Blo 1823613 2053669 := bbase (se 4 (by rfl) ⟨192531, by rfl⟩ : syracuseStep 2053669 = 385063) (by norm_num)
theorem B3896885 : Blo 1823613 3896885 := bbase (se 5 (by rfl) ⟨182666, by rfl⟩ : syracuseStep 3896885 = 365333) (by norm_num)
theorem B2053705 : Blo 1823613 2053705 := bbase (se 2 (by rfl) ⟨770139, by rfl⟩ : syracuseStep 2053705 = 1540279) (by norm_num)
theorem B2053741 : Blo 1823613 2053741 := bbase (se 3 (by rfl) ⟨385076, by rfl⟩ : syracuseStep 2053741 = 770153) (by norm_num)
theorem B4159117 : Blo 1823613 4159117 := bbase (se 3 (by rfl) ⟨779834, by rfl⟩ : syracuseStep 4159117 = 1559669) (by norm_num)
theorem B2053777 : Blo 1823613 2053777 := bbase (se 2 (by rfl) ⟨770166, by rfl⟩ : syracuseStep 2053777 = 1540333) (by norm_num)
theorem B3077797 : Blo 1823613 3077797 := bbase (se 4 (by rfl) ⟨288543, by rfl⟩ : syracuseStep 3077797 = 577087) (by norm_num)
theorem B6928037 : Blo 1823613 6928037 := bbase (se 4 (by rfl) ⟨649503, by rfl⟩ : syracuseStep 6928037 = 1299007) (by norm_num)
theorem B2922157 : Blo 1823613 2922157 := bbase (se 3 (by rfl) ⟨547904, by rfl⟩ : syracuseStep 2922157 = 1095809) (by norm_num)
theorem B16643765 : Blo 1823613 16643765 := bbase (se 5 (by rfl) ⟨780176, by rfl⟩ : syracuseStep 16643765 = 1560353) (by norm_num)
theorem B2053813 : Blo 1823613 2053813 := bbase (se 5 (by rfl) ⟨96272, by rfl⟩ : syracuseStep 2053813 = 192545) (by norm_num)
theorem B3897029 : Blo 1823613 3897029 := bbase (se 4 (by rfl) ⟨365346, by rfl⟩ : syracuseStep 3897029 = 730693) (by norm_num)
theorem B2193113 : Blo 1823613 2193113 := bbase (se 2 (by rfl) ⟨822417, by rfl⟩ : syracuseStep 2193113 = 1644835) (by norm_num)
theorem B3077885 : Blo 1823613 3077885 := bbase (se 3 (by rfl) ⟨577103, by rfl⟩ : syracuseStep 3077885 = 1154207) (by norm_num)
theorem B3462925 : Blo 1823613 3462925 := bbase (se 3 (by rfl) ⟨649298, by rfl⟩ : syracuseStep 3462925 = 1298597) (by norm_num)
theorem B1947421 : Blo 1823613 1947421 := bbase (se 3 (by rfl) ⟨365141, by rfl⟩ : syracuseStep 1947421 = 730283) (by norm_num)
theorem B2340689 : Blo 1823613 2340689 := bbase (se 2 (by rfl) ⟨877758, by rfl⟩ : syracuseStep 2340689 = 1755517) (by norm_num)
theorem B9238373 : Blo 1823613 9238373 := bbase (se 4 (by rfl) ⟨866097, by rfl⟩ : syracuseStep 9238373 = 1732195) (by norm_num)
theorem B4618093 : Blo 1823613 4618093 := bbase (se 3 (by rfl) ⟨865892, by rfl⟩ : syracuseStep 4618093 = 1731785) (by norm_num)
theorem B3078013 : Blo 1823613 3078013 := bbase (se 3 (by rfl) ⟨577127, by rfl⟩ : syracuseStep 3078013 = 1154255) (by norm_num)
theorem B6158213 : Blo 1823613 6158213 := bbase (se 4 (by rfl) ⟨577332, by rfl⟩ : syracuseStep 6158213 = 1154665) (by norm_num)
theorem B3463069 : Blo 1823613 3463069 := bbase (se 3 (by rfl) ⟨649325, by rfl⟩ : syracuseStep 3463069 = 1298651) (by norm_num)
theorem B2922413 : Blo 1823613 2922413 := bbase (se 3 (by rfl) ⟨547952, by rfl⟩ : syracuseStep 2922413 = 1095905) (by norm_num)
theorem B6928325 : Blo 1823613 6928325 := bbase (se 4 (by rfl) ⟨649530, by rfl⟩ : syracuseStep 6928325 = 1299061) (by norm_num)
theorem B3332045 : Blo 1823613 3332045 := bbase (se 3 (by rfl) ⟨624758, by rfl⟩ : syracuseStep 3332045 = 1249517) (by norm_num)
theorem B1947601 : Blo 1823613 1947601 := bbase (se 2 (by rfl) ⟨730350, by rfl⟩ : syracuseStep 1947601 = 1460701) (by norm_num)
theorem B3078101 : Blo 1823613 3078101 := bbase (se 7 (by rfl) ⟨36071, by rfl⟩ : syracuseStep 3078101 = 72143) (by norm_num)
theorem B4618205 : Blo 1823613 4618205 := bbase (se 3 (by rfl) ⟨865913, by rfl⟩ : syracuseStep 4618205 = 1731827) (by norm_num)
theorem B15800309 : Blo 1823613 15800309 := bbase (se 5 (by rfl) ⟨740639, by rfl⟩ : syracuseStep 15800309 = 1481279) (by norm_num)
theorem B2308105 : Blo 1823613 2308105 := bbase (se 2 (by rfl) ⟨865539, by rfl⟩ : syracuseStep 2308105 = 1731079) (by norm_num)
theorem B3897389 : Blo 1823613 3897389 := bbase (se 3 (by rfl) ⟨730760, by rfl⟩ : syracuseStep 3897389 = 1461521) (by norm_num)
theorem B3463229 : Blo 1823613 3463229 := bbase (se 3 (by rfl) ⟨649355, by rfl⟩ : syracuseStep 3463229 = 1298711) (by norm_num)
theorem B3078229 : Blo 1823613 3078229 := bbase (se 8 (by rfl) ⟨18036, by rfl⟩ : syracuseStep 3078229 = 36073) (by norm_num)
theorem B96073813 : Blo 1823613 96073813 := bbase (se 8 (by rfl) ⟨562932, by rfl⟩ : syracuseStep 96073813 = 1125865) (by norm_num)
theorem B11696213 : Blo 1823613 11696213 := bbase (se 8 (by rfl) ⟨68532, by rfl⟩ : syracuseStep 11696213 = 137065) (by norm_num)
theorem B3700837 : Blo 1823613 3700837 := bbase (se 4 (by rfl) ⟨346953, by rfl⟩ : syracuseStep 3700837 = 693907) (by norm_num)
theorem B10393717 : Blo 1823613 10393717 := bbase (se 5 (by rfl) ⟨487205, by rfl⟩ : syracuseStep 10393717 = 974411) (by norm_num)
theorem B5847173 : Blo 1823613 5847173 := bbase (se 4 (by rfl) ⟨548172, by rfl⟩ : syracuseStep 5847173 = 1096345) (by norm_num)
theorem B3700885 : Blo 1823613 3700885 := bbase (se 6 (by rfl) ⟨86739, by rfl⟩ : syracuseStep 3700885 = 173479) (by norm_num)
theorem B4618397 : Blo 1823613 4618397 := bbase (se 3 (by rfl) ⟨865949, by rfl⟩ : syracuseStep 4618397 = 1731899) (by norm_num)
theorem B3078317 : Blo 1823613 3078317 := bbase (se 3 (by rfl) ⟨577184, by rfl⟩ : syracuseStep 3078317 = 1154369) (by norm_num)
theorem B2308277 : Blo 1823613 2308277 := bbase (se 5 (by rfl) ⟨108200, by rfl⟩ : syracuseStep 2308277 = 216401) (by norm_num)
theorem B3463373 : Blo 1823613 3463373 := bbase (se 3 (by rfl) ⟨649382, by rfl⟩ : syracuseStep 3463373 = 1298765) (by norm_num)
theorem B2308333 : Blo 1823613 2308333 := bbase (se 3 (by rfl) ⟨432812, by rfl⟩ : syracuseStep 2308333 = 865625) (by norm_num)
theorem B8321285 : Blo 1823613 8321285 := bbase (se 4 (by rfl) ⟨780120, by rfl⟩ : syracuseStep 8321285 = 1560241) (by norm_num)
theorem B3078445 : Blo 1823613 3078445 := bbase (se 3 (by rfl) ⟨577208, by rfl⟩ : syracuseStep 3078445 = 1154417) (by norm_num)
theorem B6158645 : Blo 1823613 6158645 := bbase (se 5 (by rfl) ⟨288686, by rfl⟩ : syracuseStep 6158645 = 577373) (by norm_num)
theorem B5626181 : Blo 1823613 5626181 := bbase (se 4 (by rfl) ⟨527454, by rfl⟩ : syracuseStep 5626181 = 1054909) (by norm_num)
theorem B2308429 : Blo 1823613 2308429 := bbase (se 3 (by rfl) ⟨432830, by rfl⟩ : syracuseStep 2308429 = 865661) (by norm_num)
theorem B3078533 : Blo 1823613 3078533 := bbase (se 4 (by rfl) ⟨288612, by rfl⟩ : syracuseStep 3078533 = 577225) (by norm_num)
theorem B1948045 : Blo 1823613 1948045 := bbase (se 3 (by rfl) ⟨365258, by rfl⟩ : syracuseStep 1948045 = 730517) (by norm_num)
theorem B2251157 : Blo 1823613 2251157 := bbase (se 6 (by rfl) ⟨52761, by rfl⟩ : syracuseStep 2251157 = 105523) (by norm_num)
theorem B8771989 : Blo 1823613 8771989 := bbase (se 6 (by rfl) ⟨205593, by rfl⟩ : syracuseStep 8771989 = 411187) (by norm_num)
theorem B3463661 : Blo 1823613 3463661 := bbase (se 3 (by rfl) ⟨649436, by rfl⟩ : syracuseStep 3463661 = 1298873) (by norm_num)
theorem B4618741 : Blo 1823613 4618741 := bbase (se 5 (by rfl) ⟨216503, by rfl⟩ : syracuseStep 4618741 = 433007) (by norm_num)
theorem B2308601 : Blo 1823613 2308601 := bbase (se 2 (by rfl) ⟨865725, by rfl⟩ : syracuseStep 2308601 = 1731451) (by norm_num)
theorem B3078661 : Blo 1823613 3078661 := bbase (se 4 (by rfl) ⟨288624, by rfl⟩ : syracuseStep 3078661 = 577249) (by norm_num)
theorem B1948169 : Blo 1823613 1948169 := bbase (se 2 (by rfl) ⟨730563, by rfl⟩ : syracuseStep 1948169 = 1461127) (by norm_num)
theorem B2308657 : Blo 1823613 2308657 := bbase (se 2 (by rfl) ⟨865746, by rfl⟩ : syracuseStep 2308657 = 1731493) (by norm_num)
theorem B3078749 : Blo 1823613 3078749 := bbase (se 3 (by rfl) ⟨577265, by rfl⟩ : syracuseStep 3078749 = 1154531) (by norm_num)
theorem B4618853 : Blo 1823613 4618853 := bbase (se 4 (by rfl) ⟨433017, by rfl⟩ : syracuseStep 4618853 = 866035) (by norm_num)
theorem B3463813 : Blo 1823613 3463813 := bbase (se 4 (by rfl) ⟨324732, by rfl⟩ : syracuseStep 3463813 = 649465) (by norm_num)
theorem B2308753 : Blo 1823613 2308753 := bbase (se 2 (by rfl) ⟨865782, by rfl⟩ : syracuseStep 2308753 = 1731565) (by norm_num)
theorem B3078877 : Blo 1823613 3078877 := bbase (se 3 (by rfl) ⟨577289, by rfl⟩ : syracuseStep 3078877 = 1154579) (by norm_num)
theorem B6159077 : Blo 1823613 6159077 := bbase (se 4 (by rfl) ⟨577413, by rfl⟩ : syracuseStep 6159077 = 1154827) (by norm_num)
theorem B1948421 : Blo 1823613 1948421 := bbase (se 4 (by rfl) ⟨182664, by rfl⟩ : syracuseStep 1948421 = 365329) (by norm_num)
theorem B2923285 : Blo 1823613 2923285 := bbase (se 6 (by rfl) ⟨68514, by rfl⟩ : syracuseStep 2923285 = 137029) (by norm_num)
theorem B4619045 : Blo 1823613 4619045 := bbase (se 4 (by rfl) ⟨433035, by rfl⟩ : syracuseStep 4619045 = 866071) (by norm_num)
theorem B3078965 : Blo 1823613 3078965 := bbase (se 5 (by rfl) ⟨144326, by rfl⟩ : syracuseStep 3078965 = 288653) (by norm_num)
theorem B2308925 : Blo 1823613 2308925 := bbase (se 3 (by rfl) ⟨432923, by rfl⟩ : syracuseStep 2308925 = 865847) (by norm_num)
theorem B7904069 : Blo 1823613 7904069 := bbase (se 4 (by rfl) ⟨741006, by rfl⟩ : syracuseStep 7904069 = 1482013) (by norm_num)
theorem B2308981 : Blo 1823613 2308981 := bbase (se 5 (by rfl) ⟨108233, by rfl⟩ : syracuseStep 2308981 = 216467) (by norm_num)
theorem B2923381 : Blo 1823613 2923381 := bbase (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) (by norm_num)
theorem B3898277 : Blo 1823613 3898277 := bbase (se 4 (by rfl) ⟨365463, by rfl⟩ : syracuseStep 3898277 = 730927) (by norm_num)
theorem B3079093 : Blo 1823613 3079093 := bbase (se 5 (by rfl) ⟨144332, by rfl⟩ : syracuseStep 3079093 = 288665) (by norm_num)
theorem B3464117 : Blo 1823613 3464117 := bbase (se 5 (by rfl) ⟨162380, by rfl⟩ : syracuseStep 3464117 = 324761) (by norm_num)
theorem B1850297 : Blo 1823613 1850297 := bbase (se 2 (by rfl) ⟨693861, by rfl⟩ : syracuseStep 1850297 = 1387723) (by norm_num)
theorem B8764357 : Blo 1823613 8764357 := bbase (se 4 (by rfl) ⟨821658, by rfl⟩ : syracuseStep 8764357 = 1643317) (by norm_num)
theorem B2309077 : Blo 1823613 2309077 := bbase (se 7 (by rfl) ⟨27059, by rfl⟩ : syracuseStep 2309077 = 54119) (by norm_num)
theorem B3079181 : Blo 1823613 3079181 := bbase (se 3 (by rfl) ⟨577346, by rfl⟩ : syracuseStep 3079181 = 1154693) (by norm_num)
theorem B4103189 : Blo 1823613 4103189 := bbase (se 6 (by rfl) ⟨96168, by rfl⟩ : syracuseStep 4103189 = 192337) (by norm_num)
theorem B8436757 : Blo 1823613 8436757 := bbase (se 6 (by rfl) ⟨197736, by rfl⟩ : syracuseStep 8436757 = 395473) (by norm_num)
theorem B2923541 : Blo 1823613 2923541 := bbase (se 6 (by rfl) ⟨68520, by rfl⟩ : syracuseStep 2923541 = 137041) (by norm_num)
theorem B7896101 : Blo 1823613 7896101 := bbase (se 4 (by rfl) ⟨740259, by rfl⟩ : syracuseStep 7896101 = 1480519) (by norm_num)
theorem B4217933 : Blo 1823613 4217933 := bbase (se 3 (by rfl) ⟨790862, by rfl⟩ : syracuseStep 4217933 = 1581725) (by norm_num)
theorem B10681429 : Blo 1823613 10681429 := bbase (se 8 (by rfl) ⟨62586, by rfl⟩ : syracuseStep 10681429 = 125173) (by norm_num)
theorem B4103261 : Blo 1823613 4103261 := bbase (se 3 (by rfl) ⟨769361, by rfl⟩ : syracuseStep 4103261 = 1538723) (by norm_num)
theorem B6929509 : Blo 1823613 6929509 := bbase (se 4 (by rfl) ⟨649641, by rfl⟩ : syracuseStep 6929509 = 1299283) (by norm_num)
theorem B9239669 : Blo 1823613 9239669 := bbase (se 5 (by rfl) ⟨433109, by rfl⟩ : syracuseStep 9239669 = 866219) (by norm_num)
theorem B4619389 : Blo 1823613 4619389 := bbase (se 3 (by rfl) ⟨866135, by rfl⟩ : syracuseStep 4619389 = 1732271) (by norm_num)
theorem B2309249 : Blo 1823613 2309249 := bbase (se 2 (by rfl) ⟨865968, by rfl⟩ : syracuseStep 2309249 = 1731937) (by norm_num)
theorem B3079309 : Blo 1823613 3079309 := bbase (se 3 (by rfl) ⟨577370, by rfl⟩ : syracuseStep 3079309 = 1154741) (by norm_num)
theorem B6159509 : Blo 1823613 6159509 := bbase (se 6 (by rfl) ⟨144363, by rfl⟩ : syracuseStep 6159509 = 288727) (by norm_num)
theorem B3898525 : Blo 1823613 3898525 := bbase (se 3 (by rfl) ⟨730973, by rfl⟩ : syracuseStep 3898525 = 1461947) (by norm_num)
theorem B4103333 : Blo 1823613 4103333 := bbase (se 4 (by rfl) ⟨384687, by rfl⟩ : syracuseStep 4103333 = 769375) (by norm_num)
theorem B13327541 : Blo 1823613 13327541 := bbase (se 5 (by rfl) ⟨624728, by rfl⟩ : syracuseStep 13327541 = 1249457) (by norm_num)
theorem B2309305 : Blo 1823613 2309305 := bbase (se 2 (by rfl) ⟨865989, by rfl⟩ : syracuseStep 2309305 = 1731979) (by norm_num)
theorem B1948865 : Blo 1823613 1948865 := bbase (se 2 (by rfl) ⟨730824, by rfl⟩ : syracuseStep 1948865 = 1461649) (by norm_num)
theorem B3079397 : Blo 1823613 3079397 := bbase (se 4 (by rfl) ⟨288693, by rfl⟩ : syracuseStep 3079397 = 577387) (by norm_num)
theorem B4103405 : Blo 1823613 4103405 := bbase (se 3 (by rfl) ⟨769388, by rfl⟩ : syracuseStep 4103405 = 1538777) (by norm_num)
theorem B4619501 : Blo 1823613 4619501 := bbase (se 3 (by rfl) ⟨866156, by rfl⟩ : syracuseStep 4619501 = 1732313) (by norm_num)
theorem B2309401 : Blo 1823613 2309401 := bbase (se 2 (by rfl) ⟨866025, by rfl⟩ : syracuseStep 2309401 = 1732051) (by norm_num)
theorem B4103477 : Blo 1823613 4103477 := bbase (se 5 (by rfl) ⟨192350, by rfl⟩ : syracuseStep 4103477 = 384701) (by norm_num)
theorem B2735429 : Blo 1823613 2735429 := bbase (se 4 (by rfl) ⟨256446, by rfl⟩ : syracuseStep 2735429 = 512893) (by norm_num)
theorem B2735453 : Blo 1823613 2735453 := bbase (se 3 (by rfl) ⟨512897, by rfl⟩ : syracuseStep 2735453 = 1025795) (by norm_num)
theorem B4382045 : Blo 1823613 4382045 := bbase (se 3 (by rfl) ⟨821633, by rfl⟩ : syracuseStep 4382045 = 1643267) (by norm_num)
theorem B3079525 : Blo 1823613 3079525 := bbase (se 4 (by rfl) ⟨288705, by rfl⟩ : syracuseStep 3079525 = 577411) (by norm_num)
theorem B2735477 : Blo 1823613 2735477 := bbase (se 5 (by rfl) ⟨128225, by rfl⟩ : syracuseStep 2735477 = 256451) (by norm_num)
theorem B4103549 : Blo 1823613 4103549 := bbase (se 3 (by rfl) ⟨769415, by rfl⟩ : syracuseStep 4103549 = 1538831) (by norm_num)
theorem B2465149 : Blo 1823613 2465149 := bbase (se 3 (by rfl) ⟨462215, by rfl⟩ : syracuseStep 2465149 = 924431) (by norm_num)
theorem B2735501 : Blo 1823613 2735501 := bbase (se 3 (by rfl) ⟨512906, by rfl⟩ : syracuseStep 2735501 = 1025813) (by norm_num)
theorem B6929813 : Blo 1823613 6929813 := bbase (se 6 (by rfl) ⟨162417, by rfl⟩ : syracuseStep 6929813 = 324835) (by norm_num)
theorem B2735525 : Blo 1823613 2735525 := bbase (se 4 (by rfl) ⟨256455, by rfl⟩ : syracuseStep 2735525 = 512911) (by norm_num)
theorem B4619693 : Blo 1823613 4619693 := bbase (se 3 (by rfl) ⟨866192, by rfl⟩ : syracuseStep 4619693 = 1732385) (by norm_num)
theorem B1949113 : Blo 1823613 1949113 := bbase (se 2 (by rfl) ⟨730917, by rfl⟩ : syracuseStep 1949113 = 1461835) (by norm_num)
theorem B2735549 : Blo 1823613 2735549 := bbase (se 3 (by rfl) ⟨512915, by rfl⟩ : syracuseStep 2735549 = 1025831) (by norm_num)
theorem B3079613 : Blo 1823613 3079613 := bbase (se 3 (by rfl) ⟨577427, by rfl⟩ : syracuseStep 3079613 = 1154855) (by norm_num)
theorem B4103621 : Blo 1823613 4103621 := bbase (se 4 (by rfl) ⟨384714, by rfl⟩ : syracuseStep 4103621 = 769429) (by norm_num)
theorem B2309573 : Blo 1823613 2309573 := bbase (se 4 (by rfl) ⟨216522, by rfl⟩ : syracuseStep 2309573 = 433045) (by norm_num)
theorem B5848517 : Blo 1823613 5848517 := bbase (se 4 (by rfl) ⟨548298, by rfl⟩ : syracuseStep 5848517 = 1096597) (by norm_num)
theorem B2735573 : Blo 1823613 2735573 := bbase (se 7 (by rfl) ⟨32057, by rfl⟩ : syracuseStep 2735573 = 64115) (by norm_num)
theorem B10821077 : Blo 1823613 10821077 := bbase (se 7 (by rfl) ⟨126809, by rfl⟩ : syracuseStep 10821077 = 253619) (by norm_num)
theorem B2735597 : Blo 1823613 2735597 := bbase (se 3 (by rfl) ⟨512924, by rfl⟩ : syracuseStep 2735597 = 1025849) (by norm_num)
theorem B2309629 : Blo 1823613 2309629 := bbase (se 3 (by rfl) ⟨433055, by rfl⟩ : syracuseStep 2309629 = 866111) (by norm_num)
theorem B2735621 : Blo 1823613 2735621 := bbase (se 4 (by rfl) ⟨256464, by rfl⟩ : syracuseStep 2735621 = 512929) (by norm_num)
theorem B4103693 : Blo 1823613 4103693 := bbase (se 3 (by rfl) ⟨769442, by rfl⟩ : syracuseStep 4103693 = 1538885) (by norm_num)
theorem B2735645 : Blo 1823613 2735645 := bbase (se 3 (by rfl) ⟨512933, by rfl⟩ : syracuseStep 2735645 = 1025867) (by norm_num)
theorem B4161053 : Blo 1823613 4161053 := bbase (se 3 (by rfl) ⟨780197, by rfl⟩ : syracuseStep 4161053 = 1560395) (by norm_num)
theorem B2080289 : Blo 1823613 2080289 := bbase (se 2 (by rfl) ⟨780108, by rfl⟩ : syracuseStep 2080289 = 1560217) (by norm_num)
theorem B2735669 : Blo 1823613 2735669 := bbase (se 5 (by rfl) ⟨128234, by rfl⟩ : syracuseStep 2735669 = 256469) (by norm_num)
theorem B3079741 : Blo 1823613 3079741 := bbase (se 3 (by rfl) ⟨577451, by rfl⟩ : syracuseStep 3079741 = 1154903) (by norm_num)
theorem B6159941 : Blo 1823613 6159941 := bbase (se 4 (by rfl) ⟨577494, by rfl⟩ : syracuseStep 6159941 = 1154989) (by norm_num)
theorem B2735693 : Blo 1823613 2735693 := bbase (se 3 (by rfl) ⟨512942, by rfl⟩ : syracuseStep 2735693 = 1025885) (by norm_num)
theorem B4103765 : Blo 1823613 4103765 := bbase (se 8 (by rfl) ⟨24045, by rfl⟩ : syracuseStep 4103765 = 48091) (by norm_num)
theorem B2309725 : Blo 1823613 2309725 := bbase (se 3 (by rfl) ⟨433073, by rfl⟩ : syracuseStep 2309725 = 866147) (by norm_num)
theorem B2735717 : Blo 1823613 2735717 := bbase (se 4 (by rfl) ⟨256473, by rfl⟩ : syracuseStep 2735717 = 512947) (by norm_num)
theorem B2735741 : Blo 1823613 2735741 := bbase (se 3 (by rfl) ⟨512951, by rfl⟩ : syracuseStep 2735741 = 1025903) (by norm_num)
theorem B4382333 : Blo 1823613 4382333 := bbase (se 3 (by rfl) ⟨821687, by rfl⟩ : syracuseStep 4382333 = 1643375) (by norm_num)
theorem B2735765 : Blo 1823613 2735765 := bbase (se 6 (by rfl) ⟨64119, by rfl⟩ : syracuseStep 2735765 = 128239) (by norm_num)
theorem B3079829 : Blo 1823613 3079829 := bbase (se 6 (by rfl) ⟨72183, by rfl⟩ : syracuseStep 3079829 = 144367) (by norm_num)
theorem B3899029 : Blo 1823613 3899029 := bbase (se 6 (by rfl) ⟨91383, by rfl⟩ : syracuseStep 3899029 = 182767) (by norm_num)
theorem B4103837 : Blo 1823613 4103837 := bbase (se 3 (by rfl) ⟨769469, by rfl⟩ : syracuseStep 4103837 = 1538939) (by norm_num)
theorem B3464869 : Blo 1823613 3464869 := bbase (se 4 (by rfl) ⟨324831, by rfl⟩ : syracuseStep 3464869 = 649663) (by norm_num)
theorem B2735789 : Blo 1823613 2735789 := bbase (se 3 (by rfl) ⟨512960, by rfl⟩ : syracuseStep 2735789 = 1025921) (by norm_num)
theorem B2735813 : Blo 1823613 2735813 := bbase (se 4 (by rfl) ⟨256482, by rfl⟩ : syracuseStep 2735813 = 512965) (by norm_num)
theorem B2596573 : Blo 1823613 2596573 := bbase (se 3 (by rfl) ⟨486857, by rfl⟩ : syracuseStep 2596573 = 973715) (by norm_num)
theorem B2735837 : Blo 1823613 2735837 := bbase (se 3 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 2735837 = 1025939) (by norm_num)
theorem B4103909 : Blo 1823613 4103909 := bbase (se 4 (by rfl) ⟨384741, by rfl⟩ : syracuseStep 4103909 = 769483) (by norm_num)
theorem B2735861 : Blo 1823613 2735861 := bbase (se 5 (by rfl) ⟨128243, by rfl⟩ : syracuseStep 2735861 = 256487) (by norm_num)
theorem B4620037 : Blo 1823613 4620037 := bbase (se 4 (by rfl) ⟨433128, by rfl⟩ : syracuseStep 4620037 = 866257) (by norm_num)
theorem B2309897 : Blo 1823613 2309897 := bbase (se 2 (by rfl) ⟨866211, by rfl⟩ : syracuseStep 2309897 = 1732423) (by norm_num)
theorem B2735885 : Blo 1823613 2735885 := bbase (se 3 (by rfl) ⟨512978, by rfl⟩ : syracuseStep 2735885 = 1025957) (by norm_num)
theorem B3079957 : Blo 1823613 3079957 := bbase (se 6 (by rfl) ⟨72186, by rfl⟩ : syracuseStep 3079957 = 144373) (by norm_num)
theorem B2735909 : Blo 1823613 2735909 := bbase (se 4 (by rfl) ⟨256491, by rfl⟩ : syracuseStep 2735909 = 512983) (by norm_num)
theorem B4103981 : Blo 1823613 4103981 := bbase (se 3 (by rfl) ⟨769496, by rfl⟩ : syracuseStep 4103981 = 1538993) (by norm_num)
theorem B3465013 : Blo 1823613 3465013 := bbase (se 5 (by rfl) ⟨162422, by rfl⟩ : syracuseStep 3465013 = 324845) (by norm_num)
theorem B2735933 : Blo 1823613 2735933 := bbase (se 3 (by rfl) ⟨512987, by rfl⟩ : syracuseStep 2735933 = 1025975) (by norm_num)
theorem B2309953 : Blo 1823613 2309953 := bbase (se 2 (by rfl) ⟨866232, by rfl⟩ : syracuseStep 2309953 = 1732465) (by norm_num)
theorem B2596693 : Blo 1823613 2596693 := bbase (se 9 (by rfl) ⟨7607, by rfl⟩ : syracuseStep 2596693 = 15215) (by norm_num)
theorem B2735957 : Blo 1823613 2735957 := bbase (se 9 (by rfl) ⟨8015, by rfl⟩ : syracuseStep 2735957 = 16031) (by norm_num)
theorem B2735981 : Blo 1823613 2735981 := bbase (se 3 (by rfl) ⟨512996, by rfl⟩ : syracuseStep 2735981 = 1025993) (by norm_num)
theorem B3080045 : Blo 1823613 3080045 := bbase (se 3 (by rfl) ⟨577508, by rfl⟩ : syracuseStep 3080045 = 1155017) (by norm_num)
theorem B4104053 : Blo 1823613 4104053 := bbase (se 5 (by rfl) ⟨192377, by rfl⟩ : syracuseStep 4104053 = 384755) (by norm_num)
theorem B4620149 : Blo 1823613 4620149 := bbase (se 5 (by rfl) ⟨216569, by rfl⟩ : syracuseStep 4620149 = 433139) (by norm_num)
theorem B2736005 : Blo 1823613 2736005 := bbase (se 4 (by rfl) ⟨256500, by rfl⟩ : syracuseStep 2736005 = 513001) (by norm_num)
theorem B2736029 : Blo 1823613 2736029 := bbase (se 3 (by rfl) ⟨513005, by rfl⟩ : syracuseStep 2736029 = 1026011) (by norm_num)
theorem B2310049 : Blo 1823613 2310049 := bbase (se 2 (by rfl) ⟨866268, by rfl⟩ : syracuseStep 2310049 = 1732537) (by norm_num)
theorem B2596789 : Blo 1823613 2596789 := bbase (se 5 (by rfl) ⟨121724, by rfl⟩ : syracuseStep 2596789 = 243449) (by norm_num)
theorem B2736053 : Blo 1823613 2736053 := bbase (se 5 (by rfl) ⟨128252, by rfl⟩ : syracuseStep 2736053 = 256505) (by norm_num)
theorem B4104125 : Blo 1823613 4104125 := bbase (se 3 (by rfl) ⟨769523, by rfl⟩ : syracuseStep 4104125 = 1539047) (by norm_num)
theorem B2736077 : Blo 1823613 2736077 := bbase (se 3 (by rfl) ⟨513014, by rfl⟩ : syracuseStep 2736077 = 1026029) (by norm_num)
theorem B3465173 : Blo 1823613 3465173 := bbase (se 7 (by rfl) ⟨40607, by rfl⟩ : syracuseStep 3465173 = 81215) (by norm_num)
theorem B2736101 : Blo 1823613 2736101 := bbase (se 4 (by rfl) ⟨256509, by rfl⟩ : syracuseStep 2736101 = 513019) (by norm_num)
theorem B3080173 : Blo 1823613 3080173 := bbase (se 3 (by rfl) ⟨577532, by rfl⟩ : syracuseStep 3080173 = 1155065) (by norm_num)
theorem B6160373 : Blo 1823613 6160373 := bbase (se 5 (by rfl) ⟨288767, by rfl⟩ : syracuseStep 6160373 = 577535) (by norm_num)
theorem B2736125 : Blo 1823613 2736125 := bbase (se 3 (by rfl) ⟨513023, by rfl⟩ : syracuseStep 2736125 = 1026047) (by norm_num)
theorem B2736131 : Blo 1823613 2736131 := bstep (se 1 (by rfl) ⟨2052098, by rfl⟩ : syracuseStep 2736131 = 4104197) B4104197
theorem B2736161 : Blo 1823613 2736161 := bstep (se 2 (by rfl) ⟨1026060, by rfl⟩ : syracuseStep 2736161 = 2052121) B2052121
theorem B6930467 : Blo 1823613 6930467 := bstep (se 1 (by rfl) ⟨5197850, by rfl⟩ : syracuseStep 6930467 = 10395701) B10395701
theorem B3080227 : Blo 1823613 3080227 := bstep (se 1 (by rfl) ⟨2310170, by rfl⟩ : syracuseStep 3080227 = 4620341) B4620341
theorem B6930481 : Blo 1823613 6930481 := bstep (se 2 (by rfl) ⟨2598930, by rfl⟩ : syracuseStep 6930481 = 5197861) B5197861
theorem B2736179 : Blo 1823613 2736179 := bstep (se 1 (by rfl) ⟨2052134, by rfl⟩ : syracuseStep 2736179 = 4104269) B4104269
theorem B2310211 : Blo 1823613 2310211 := bstep (se 1 (by rfl) ⟨1732658, by rfl⟩ : syracuseStep 2310211 = 3465317) B3465317
theorem B2736209 : Blo 1823613 2736209 := bstep (se 2 (by rfl) ⟨1026078, by rfl⟩ : syracuseStep 2736209 = 2052157) B2052157
theorem B2736227 : Blo 1823613 2736227 := bstep (se 1 (by rfl) ⟨2052170, by rfl⟩ : syracuseStep 2736227 = 4104341) B4104341
theorem B5193841 : Blo 1823613 5193841 := bstep (se 2 (by rfl) ⟨1947690, by rfl⟩ : syracuseStep 5193841 = 3895381) B3895381
theorem B4104305 : Blo 1823613 4104305 := bstep (se 2 (by rfl) ⟨1539114, by rfl⟩ : syracuseStep 4104305 = 3078229) B3078229
theorem B128098417 : Blo 1823613 128098417 := bstep (se 2 (by rfl) ⟨48036906, by rfl⟩ : syracuseStep 128098417 = 96073813) B96073813
theorem B2736257 : Blo 1823613 2736257 := bstep (se 2 (by rfl) ⟨1026096, by rfl⟩ : syracuseStep 2736257 = 2052193) B2052193
theorem B4382851 : Blo 1823613 4382851 := bstep (se 1 (by rfl) ⟨3287138, by rfl⟩ : syracuseStep 4382851 = 6574277) B6574277
theorem B4104323 : Blo 1823613 4104323 := bstep (se 1 (by rfl) ⟨3078242, by rfl⟩ : syracuseStep 4104323 = 6156485) B6156485
theorem B18735245 : Blo 1823613 18735245 := bstep (se 3 (by rfl) ⟨3512858, by rfl⟩ : syracuseStep 18735245 = 7025717) B7025717
theorem B2736275 : Blo 1823613 2736275 := bstep (se 1 (by rfl) ⟨2052206, by rfl⟩ : syracuseStep 2736275 = 4104413) B4104413
theorem B2736305 : Blo 1823613 2736305 := bstep (se 2 (by rfl) ⟨1026114, by rfl⟩ : syracuseStep 2736305 = 2052229) B2052229
theorem B3080369 : Blo 1823613 3080369 := bstep (se 2 (by rfl) ⟨1155138, by rfl⟩ : syracuseStep 3080369 = 2310277) B2310277
theorem B2736323 : Blo 1823613 2736323 := bstep (se 1 (by rfl) ⟨2052242, by rfl⟩ : syracuseStep 2736323 = 4104485) B4104485
theorem B11247821 : Blo 1823613 11247821 := bstep (se 3 (by rfl) ⟨2108966, by rfl⟩ : syracuseStep 11247821 = 4217933) B4217933
theorem B6160589 : Blo 1823613 6160589 := bstep (se 3 (by rfl) ⟨1155110, by rfl⟩ : syracuseStep 6160589 = 2310221) B2310221
theorem B2736353 : Blo 1823613 2736353 := bstep (se 2 (by rfl) ⟨1026132, by rfl⟩ : syracuseStep 2736353 = 2052265) B2052265
theorem B9240803 : Blo 1823613 9240803 := bstep (se 1 (by rfl) ⟨6930602, by rfl⟩ : syracuseStep 9240803 = 13861205) B13861205
theorem B2736371 : Blo 1823613 2736371 := bstep (se 1 (by rfl) ⟨2052278, by rfl⟩ : syracuseStep 2736371 = 4104557) B4104557
theorem B6160643 : Blo 1823613 6160643 := bstep (se 1 (by rfl) ⟨4620482, by rfl⟩ : syracuseStep 6160643 = 9240965) B9240965
theorem B2736401 : Blo 1823613 2736401 := bstep (se 2 (by rfl) ⟨1026150, by rfl⟩ : syracuseStep 2736401 = 2052301) B2052301
theorem B2736419 : Blo 1823613 2736419 := bstep (se 1 (by rfl) ⟨2052314, by rfl⟩ : syracuseStep 2736419 = 4104629) B4104629
theorem B3080497 : Blo 1823613 3080497 := bstep (se 2 (by rfl) ⟨1155186, by rfl⟩ : syracuseStep 3080497 = 2310373) B2310373
theorem B2736449 : Blo 1823613 2736449 := bstep (se 2 (by rfl) ⟨1026168, by rfl⟩ : syracuseStep 2736449 = 2052337) B2052337
theorem B2736467 : Blo 1823613 2736467 := bstep (se 1 (by rfl) ⟨2052350, by rfl⟩ : syracuseStep 2736467 = 4104701) B4104701
theorem B3080531 : Blo 1823613 3080531 := bstep (se 1 (by rfl) ⟨2310398, by rfl⟩ : syracuseStep 3080531 = 4620797) B4620797
theorem B2736497 : Blo 1823613 2736497 := bstep (se 2 (by rfl) ⟨1026186, by rfl⟩ : syracuseStep 2736497 = 2052373) B2052373
theorem B35553649 : Blo 1823613 35553649 := bstep (se 2 (by rfl) ⟨13332618, by rfl⟩ : syracuseStep 35553649 = 26665237) B26665237
theorem B5194115 : Blo 1823613 5194115 := bstep (se 1 (by rfl) ⟨3895586, by rfl⟩ : syracuseStep 5194115 = 7791173) B7791173
theorem B2736515 : Blo 1823613 2736515 := bstep (se 1 (by rfl) ⟨2052386, by rfl⟩ : syracuseStep 2736515 = 4104773) B4104773
theorem B4104593 : Blo 1823613 4104593 := bstep (se 2 (by rfl) ⟨1539222, by rfl⟩ : syracuseStep 4104593 = 3078445) B3078445
theorem B2736545 : Blo 1823613 2736545 := bstep (se 2 (by rfl) ⟨1026204, by rfl⟩ : syracuseStep 2736545 = 2052409) B2052409
theorem B4104611 : Blo 1823613 4104611 := bstep (se 1 (by rfl) ⟨3078458, by rfl⟩ : syracuseStep 4104611 = 6156917) B6156917
theorem B2736563 : Blo 1823613 2736563 := bstep (se 1 (by rfl) ⟨2052422, by rfl⟩ : syracuseStep 2736563 = 4104845) B4104845
theorem B2736593 : Blo 1823613 2736593 := bstep (se 2 (by rfl) ⟨1026222, by rfl⟩ : syracuseStep 2736593 = 2052445) B2052445
theorem B3080659 : Blo 1823613 3080659 := bstep (se 1 (by rfl) ⟨2310494, by rfl⟩ : syracuseStep 3080659 = 4620989) B4620989
theorem B2736611 : Blo 1823613 2736611 := bstep (se 1 (by rfl) ⟨2052458, by rfl⟩ : syracuseStep 2736611 = 4104917) B4104917
theorem B2736641 : Blo 1823613 2736641 := bstep (se 2 (by rfl) ⟨1026240, by rfl⟩ : syracuseStep 2736641 = 2052481) B2052481
theorem B2597393 : Blo 1823613 2597393 := bstep (se 2 (by rfl) ⟨974022, by rfl⟩ : syracuseStep 2597393 = 1948045) B1948045
theorem B2736659 : Blo 1823613 2736659 := bstep (se 1 (by rfl) ⟨2052494, by rfl⟩ : syracuseStep 2736659 = 4104989) B4104989
theorem B6160913 : Blo 1823613 6160913 := bstep (se 2 (by rfl) ⟨2310342, by rfl⟩ : syracuseStep 6160913 = 4620685) B4620685
theorem B2736689 : Blo 1823613 2736689 := bstep (se 2 (by rfl) ⟨1026258, by rfl⟩ : syracuseStep 2736689 = 2052517) B2052517
theorem B5194307 : Blo 1823613 5194307 := bstep (se 1 (by rfl) ⟨3895730, by rfl⟩ : syracuseStep 5194307 = 7791461) B7791461
theorem B2736707 : Blo 1823613 2736707 := bstep (se 1 (by rfl) ⟨2052530, by rfl⟩ : syracuseStep 2736707 = 4105061) B4105061
theorem B2736737 : Blo 1823613 2736737 := bstep (se 2 (by rfl) ⟨1026276, by rfl⟩ : syracuseStep 2736737 = 2052553) B2052553
theorem B2736755 : Blo 1823613 2736755 := bstep (se 1 (by rfl) ⟨2052566, by rfl⟩ : syracuseStep 2736755 = 4105133) B4105133
theorem B6169229 : Blo 1823613 6169229 := bstep (se 3 (by rfl) ⟨1156730, by rfl⟩ : syracuseStep 6169229 = 2313461) B2313461
theorem B15590029 : Blo 1823613 15590029 := bstep (se 3 (by rfl) ⟨2923130, by rfl⟩ : syracuseStep 15590029 = 5846261) B5846261
theorem B2736785 : Blo 1823613 2736785 := bstep (se 2 (by rfl) ⟨1026294, by rfl⟩ : syracuseStep 2736785 = 2052589) B2052589
theorem B2736803 : Blo 1823613 2736803 := bstep (se 1 (by rfl) ⟨2052602, by rfl⟩ : syracuseStep 2736803 = 4105205) B4105205
theorem B4383409 : Blo 1823613 4383409 := bstep (se 2 (by rfl) ⟨1643778, by rfl⟩ : syracuseStep 4383409 = 3287557) B3287557
theorem B4104881 : Blo 1823613 4104881 := bstep (se 2 (by rfl) ⟨1539330, by rfl⟩ : syracuseStep 4104881 = 3078661) B3078661
theorem B2736833 : Blo 1823613 2736833 := bstep (se 2 (by rfl) ⟨1026312, by rfl⟩ : syracuseStep 2736833 = 2052625) B2052625
theorem B4104899 : Blo 1823613 4104899 := bstep (se 1 (by rfl) ⟨3078674, by rfl⟩ : syracuseStep 4104899 = 6157349) B6157349
theorem B4621009 : Blo 1823613 4621009 := bstep (se 2 (by rfl) ⟨1732878, by rfl⟩ : syracuseStep 4621009 = 3465757) B3465757
theorem B2736851 : Blo 1823613 2736851 := bstep (se 1 (by rfl) ⟨2052638, by rfl⟩ : syracuseStep 2736851 = 4105277) B4105277
theorem B2736881 : Blo 1823613 2736881 := bstep (se 2 (by rfl) ⟨1026330, by rfl⟩ : syracuseStep 2736881 = 2052661) B2052661
theorem B2736899 : Blo 1823613 2736899 := bstep (se 1 (by rfl) ⟨2052674, by rfl⟩ : syracuseStep 2736899 = 4105349) B4105349
theorem B2736929 : Blo 1823613 2736929 := bstep (se 2 (by rfl) ⟨1026348, by rfl⟩ : syracuseStep 2736929 = 2052697) B2052697
theorem B10396451 : Blo 1823613 10396451 := bstep (se 1 (by rfl) ⟨7797338, by rfl⟩ : syracuseStep 10396451 = 15594677) B15594677
theorem B2736947 : Blo 1823613 2736947 := bstep (se 1 (by rfl) ⟨2052710, by rfl⟩ : syracuseStep 2736947 = 4105421) B4105421
theorem B2736977 : Blo 1823613 2736977 := bstep (se 2 (by rfl) ⟨1026366, by rfl⟩ : syracuseStep 2736977 = 2052733) B2052733
theorem B2736995 : Blo 1823613 2736995 := bstep (se 1 (by rfl) ⟨2052746, by rfl⟩ : syracuseStep 2736995 = 4105493) B4105493
theorem B2737025 : Blo 1823613 2737025 := bstep (se 2 (by rfl) ⟨1026384, by rfl⟩ : syracuseStep 2737025 = 2052769) B2052769
theorem B2737043 : Blo 1823613 2737043 := bstep (se 1 (by rfl) ⟨2052782, by rfl⟩ : syracuseStep 2737043 = 4105565) B4105565
theorem B4932515 : Blo 1823613 4932515 := bstep (se 1 (by rfl) ⟨3699386, by rfl⟩ : syracuseStep 4932515 = 7398773) B7398773
theorem B2737073 : Blo 1823613 2737073 := bstep (se 2 (by rfl) ⟨1026402, by rfl⟩ : syracuseStep 2737073 = 2052805) B2052805
theorem B2737091 : Blo 1823613 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B4105169 : Blo 1823613 4105169 := bstep (se 2 (by rfl) ⟨1539438, by rfl⟩ : syracuseStep 4105169 = 3078877) B3078877
theorem B2737121 : Blo 1823613 2737121 := bstep (se 2 (by rfl) ⟨1026420, by rfl⟩ : syracuseStep 2737121 = 2052841) B2052841
theorem B4105187 : Blo 1823613 4105187 := bstep (se 1 (by rfl) ⟨3078890, by rfl⟩ : syracuseStep 4105187 = 6157781) B6157781
theorem B2737139 : Blo 1823613 2737139 := bstep (se 1 (by rfl) ⟨2052854, by rfl⟩ : syracuseStep 2737139 = 4105709) B4105709
theorem B6243331 : Blo 1823613 6243331 := bstep (se 1 (by rfl) ⟨4682498, by rfl⟩ : syracuseStep 6243331 = 9364997) B9364997
theorem B9241613 : Blo 1823613 9241613 := bstep (se 3 (by rfl) ⟨1732802, by rfl⟩ : syracuseStep 9241613 = 3465605) B3465605
theorem B2737169 : Blo 1823613 2737169 := bstep (se 2 (by rfl) ⟨1026438, by rfl⟩ : syracuseStep 2737169 = 2052877) B2052877
theorem B2597923 : Blo 1823613 2597923 := bstep (se 1 (by rfl) ⟨1948442, by rfl⟩ : syracuseStep 2597923 = 3896885) B3896885
theorem B2737187 : Blo 1823613 2737187 := bstep (se 1 (by rfl) ⟨2052890, by rfl⟩ : syracuseStep 2737187 = 4105781) B4105781
theorem B2737217 : Blo 1823613 2737217 := bstep (se 2 (by rfl) ⟨1026456, by rfl⟩ : syracuseStep 2737217 = 2052913) B2052913
theorem B2737235 : Blo 1823613 2737235 := bstep (se 1 (by rfl) ⟨2052926, by rfl⟩ : syracuseStep 2737235 = 4105853) B4105853
theorem B2737265 : Blo 1823613 2737265 := bstep (se 2 (by rfl) ⟨1026474, by rfl⟩ : syracuseStep 2737265 = 2052949) B2052949
theorem B2737283 : Blo 1823613 2737283 := bstep (se 1 (by rfl) ⟨2052962, by rfl⟩ : syracuseStep 2737283 = 4105925) B4105925
theorem B2737313 : Blo 1823613 2737313 := bstep (se 2 (by rfl) ⟨1026492, by rfl⟩ : syracuseStep 2737313 = 2052985) B2052985
theorem B2737331 : Blo 1823613 2737331 := bstep (se 1 (by rfl) ⟨2052998, by rfl⟩ : syracuseStep 2737331 = 4105997) B4105997
theorem B2737361 : Blo 1823613 2737361 := bstep (se 2 (by rfl) ⟨1026510, by rfl⟩ : syracuseStep 2737361 = 2053021) B2053021
theorem B2737379 : Blo 1823613 2737379 := bstep (se 1 (by rfl) ⟨2053034, by rfl⟩ : syracuseStep 2737379 = 4106069) B4106069
theorem B4105457 : Blo 1823613 4105457 := bstep (se 2 (by rfl) ⟨1539546, by rfl⟩ : syracuseStep 4105457 = 3079093) B3079093
theorem B2737409 : Blo 1823613 2737409 := bstep (se 2 (by rfl) ⟨1026528, by rfl⟩ : syracuseStep 2737409 = 2053057) B2053057
theorem B4105475 : Blo 1823613 4105475 := bstep (se 1 (by rfl) ⟨3079106, by rfl⟩ : syracuseStep 4105475 = 6158213) B6158213
theorem B2737427 : Blo 1823613 2737427 := bstep (se 1 (by rfl) ⟨2053070, by rfl⟩ : syracuseStep 2737427 = 4106141) B4106141
theorem B2737457 : Blo 1823613 2737457 := bstep (se 2 (by rfl) ⟨1026546, by rfl⟩ : syracuseStep 2737457 = 2053093) B2053093
theorem B2221363 : Blo 1823613 2221363 := bstep (se 1 (by rfl) ⟨1666022, by rfl⟩ : syracuseStep 2221363 = 3332045) B3332045
theorem B2737475 : Blo 1823613 2737475 := bstep (se 1 (by rfl) ⟨2053106, by rfl⟩ : syracuseStep 2737475 = 4106213) B4106213
theorem B4384081 : Blo 1823613 4384081 := bstep (se 2 (by rfl) ⟨1644030, by rfl⟩ : syracuseStep 4384081 = 3288061) B3288061
theorem B2737505 : Blo 1823613 2737505 := bstep (se 2 (by rfl) ⟨1026564, by rfl⟩ : syracuseStep 2737505 = 2053129) B2053129
theorem B5195117 : Blo 1823613 5195117 := bstep (se 3 (by rfl) ⟨974084, by rfl⟩ : syracuseStep 5195117 = 1948169) B1948169
theorem B11249009 : Blo 1823613 11249009 := bstep (se 2 (by rfl) ⟨4218378, by rfl⟩ : syracuseStep 11249009 = 8436757) B8436757
theorem B18990449 : Blo 1823613 18990449 := bstep (se 2 (by rfl) ⟨7121418, by rfl⟩ : syracuseStep 18990449 = 14242837) B14242837
theorem B2598259 : Blo 1823613 2598259 := bstep (se 1 (by rfl) ⟨1948694, by rfl⟩ : syracuseStep 2598259 = 3897389) B3897389
theorem B2737523 : Blo 1823613 2737523 := bstep (se 1 (by rfl) ⟨2053142, by rfl⟩ : syracuseStep 2737523 = 4106285) B4106285
theorem B16647565 : Blo 1823613 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B2737553 : Blo 1823613 2737553 := bstep (se 2 (by rfl) ⟨1026582, by rfl⟩ : syracuseStep 2737553 = 2053165) B2053165
theorem B2737571 : Blo 1823613 2737571 := bstep (se 1 (by rfl) ⟨2053178, by rfl⟩ : syracuseStep 2737571 = 4106357) B4106357
theorem B5547437 : Blo 1823613 5547437 := bstep (se 3 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 5547437 = 2080289) B2080289
theorem B2737601 : Blo 1823613 2737601 := bstep (se 2 (by rfl) ⟨1026600, by rfl⟩ : syracuseStep 2737601 = 2053201) B2053201
theorem B2737619 : Blo 1823613 2737619 := bstep (se 1 (by rfl) ⟨2053214, by rfl⟩ : syracuseStep 2737619 = 4106429) B4106429
theorem B2737649 : Blo 1823613 2737649 := bstep (se 2 (by rfl) ⟨1026618, by rfl⟩ : syracuseStep 2737649 = 2053237) B2053237
theorem B5547523 : Blo 1823613 5547523 := bstep (se 1 (by rfl) ⟨4160642, by rfl⟩ : syracuseStep 5547523 = 8321285) B8321285
theorem B2737667 : Blo 1823613 2737667 := bstep (se 1 (by rfl) ⟨2053250, by rfl⟩ : syracuseStep 2737667 = 4106501) B4106501
theorem B4105745 : Blo 1823613 4105745 := bstep (se 2 (by rfl) ⟨1539654, by rfl⟩ : syracuseStep 4105745 = 3079309) B3079309
theorem B2737697 : Blo 1823613 2737697 := bstep (se 2 (by rfl) ⟨1026636, by rfl⟩ : syracuseStep 2737697 = 2053273) B2053273
theorem B5195299 : Blo 1823613 5195299 := bstep (se 1 (by rfl) ⟨3896474, by rfl⟩ : syracuseStep 5195299 = 7792949) B7792949
theorem B4105763 : Blo 1823613 4105763 := bstep (se 1 (by rfl) ⟨3079322, by rfl⟩ : syracuseStep 4105763 = 6158645) B6158645
theorem B8324657 : Blo 1823613 8324657 := bstep (se 2 (by rfl) ⟨3121746, by rfl⟩ : syracuseStep 8324657 = 6243493) B6243493
theorem B2737715 : Blo 1823613 2737715 := bstep (se 1 (by rfl) ⟨2053286, by rfl⟩ : syracuseStep 2737715 = 4106573) B4106573
theorem B2737745 : Blo 1823613 2737745 := bstep (se 2 (by rfl) ⟨1026654, by rfl⟩ : syracuseStep 2737745 = 2053309) B2053309
theorem B2737763 : Blo 1823613 2737763 := bstep (se 1 (by rfl) ⟨2053322, by rfl⟩ : syracuseStep 2737763 = 4106645) B4106645
theorem B2737793 : Blo 1823613 2737793 := bstep (se 2 (by rfl) ⟨1026672, by rfl⟩ : syracuseStep 2737793 = 2053345) B2053345
theorem B16647821 : Blo 1823613 16647821 := bstep (se 3 (by rfl) ⟨3121466, by rfl⟩ : syracuseStep 16647821 = 6242933) B6242933
theorem B2737811 : Blo 1823613 2737811 := bstep (se 1 (by rfl) ⟨2053358, by rfl⟩ : syracuseStep 2737811 = 4106717) B4106717
theorem B2737841 : Blo 1823613 2737841 := bstep (se 2 (by rfl) ⟨1026690, by rfl⟩ : syracuseStep 2737841 = 2053381) B2053381
theorem B2737859 : Blo 1823613 2737859 := bstep (se 1 (by rfl) ⟨2053394, by rfl⟩ : syracuseStep 2737859 = 4106789) B4106789
theorem B2737889 : Blo 1823613 2737889 := bstep (se 2 (by rfl) ⟨1026708, by rfl⟩ : syracuseStep 2737889 = 2053417) B2053417
theorem B9234161 : Blo 1823613 9234161 := bstep (se 2 (by rfl) ⟨3462810, by rfl⟩ : syracuseStep 9234161 = 6925621) B6925621
theorem B2737907 : Blo 1823613 2737907 := bstep (se 1 (by rfl) ⟨2053430, by rfl⟩ : syracuseStep 2737907 = 4106861) B4106861
theorem B2737937 : Blo 1823613 2737937 := bstep (se 2 (by rfl) ⟨1026726, by rfl⟩ : syracuseStep 2737937 = 2053453) B2053453
theorem B2737955 : Blo 1823613 2737955 := bstep (se 1 (by rfl) ⟨2053466, by rfl⟩ : syracuseStep 2737955 = 4106933) B4106933
theorem B4106033 : Blo 1823613 4106033 := bstep (se 2 (by rfl) ⟨1539762, by rfl⟩ : syracuseStep 4106033 = 3079525) B3079525
theorem B2737985 : Blo 1823613 2737985 := bstep (se 2 (by rfl) ⟨1026744, by rfl⟩ : syracuseStep 2737985 = 2053489) B2053489
theorem B4106051 : Blo 1823613 4106051 := bstep (se 1 (by rfl) ⟨3079538, by rfl⟩ : syracuseStep 4106051 = 6159077) B6159077
theorem B19728197 : Blo 1823613 19728197 := bstep (se 4 (by rfl) ⟨1849518, by rfl⟩ : syracuseStep 19728197 = 3699037) B3699037
theorem B3286865 : Blo 1823613 3286865 := bstep (se 2 (by rfl) ⟨1232574, by rfl⟩ : syracuseStep 3286865 = 2465149) B2465149
theorem B2738003 : Blo 1823613 2738003 := bstep (se 1 (by rfl) ⟨2053502, by rfl⟩ : syracuseStep 2738003 = 4107005) B4107005
theorem B2738033 : Blo 1823613 2738033 := bstep (se 2 (by rfl) ⟨1026762, by rfl⟩ : syracuseStep 2738033 = 2053525) B2053525
theorem B2738051 : Blo 1823613 2738051 := bstep (se 1 (by rfl) ⟨2053538, by rfl⟩ : syracuseStep 2738051 = 4107077) B4107077
theorem B5269379 : Blo 1823613 5269379 := bstep (se 1 (by rfl) ⟨3952034, by rfl⟩ : syracuseStep 5269379 = 7904069) B7904069
theorem B2598817 : Blo 1823613 2598817 := bstep (se 2 (by rfl) ⟨974556, by rfl⟩ : syracuseStep 2598817 = 1949113) B1949113
theorem B2738081 : Blo 1823613 2738081 := bstep (se 2 (by rfl) ⟨1026780, by rfl⟩ : syracuseStep 2738081 = 2053561) B2053561
theorem B2738099 : Blo 1823613 2738099 := bstep (se 1 (by rfl) ⟨2053574, by rfl⟩ : syracuseStep 2738099 = 4107149) B4107149
theorem B2598851 : Blo 1823613 2598851 := bstep (se 1 (by rfl) ⟨1949138, by rfl⟩ : syracuseStep 2598851 = 3898277) B3898277
theorem B15591365 : Blo 1823613 15591365 := bstep (se 4 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 15591365 = 2923381) B2923381
theorem B2738129 : Blo 1823613 2738129 := bstep (se 2 (by rfl) ⟨1026798, by rfl⟩ : syracuseStep 2738129 = 2053597) B2053597
theorem B2738147 : Blo 1823613 2738147 := bstep (se 1 (by rfl) ⟨2053610, by rfl⟩ : syracuseStep 2738147 = 4107221) B4107221
theorem B2738177 : Blo 1823613 2738177 := bstep (se 2 (by rfl) ⟨1026816, by rfl⟩ : syracuseStep 2738177 = 2053633) B2053633
theorem B5195789 : Blo 1823613 5195789 := bstep (se 3 (by rfl) ⟨974210, by rfl⟩ : syracuseStep 5195789 = 1948421) B1948421
theorem B2738195 : Blo 1823613 2738195 := bstep (se 1 (by rfl) ⟨2053646, by rfl⟩ : syracuseStep 2738195 = 4107293) B4107293
theorem B2738225 : Blo 1823613 2738225 := bstep (se 2 (by rfl) ⟨1026834, by rfl⟩ : syracuseStep 2738225 = 2053669) B2053669
theorem B2738243 : Blo 1823613 2738243 := bstep (se 1 (by rfl) ⟨2053682, by rfl⟩ : syracuseStep 2738243 = 4107365) B4107365
theorem B4106321 : Blo 1823613 4106321 := bstep (se 2 (by rfl) ⟨1539870, by rfl⟩ : syracuseStep 4106321 = 3079741) B3079741
theorem B2738273 : Blo 1823613 2738273 := bstep (se 2 (by rfl) ⟨1026852, by rfl⟩ : syracuseStep 2738273 = 2053705) B2053705
theorem B4106339 : Blo 1823613 4106339 := bstep (se 1 (by rfl) ⟨3079754, by rfl⟩ : syracuseStep 4106339 = 6159509) B6159509
theorem B10389617 : Blo 1823613 10389617 := bstep (se 2 (by rfl) ⟨3896106, by rfl⟩ : syracuseStep 10389617 = 7792213) B7792213
theorem B2738291 : Blo 1823613 2738291 := bstep (se 1 (by rfl) ⟨2053718, by rfl⟩ : syracuseStep 2738291 = 4107437) B4107437
theorem B2738321 : Blo 1823613 2738321 := bstep (se 2 (by rfl) ⟨1026870, by rfl⟩ : syracuseStep 2738321 = 2053741) B2053741
theorem B2738339 : Blo 1823613 2738339 := bstep (se 1 (by rfl) ⟨2053754, by rfl⟩ : syracuseStep 2738339 = 4107509) B4107509
theorem B2738369 : Blo 1823613 2738369 := bstep (se 2 (by rfl) ⟨1026888, by rfl⟩ : syracuseStep 2738369 = 2053777) B2053777
theorem B2738387 : Blo 1823613 2738387 := bstep (se 1 (by rfl) ⟨2053790, by rfl⟩ : syracuseStep 2738387 = 4107581) B4107581
theorem B4442339 : Blo 1823613 4442339 := bstep (se 1 (by rfl) ⟨3331754, by rfl⟩ : syracuseStep 4442339 = 6663509) B6663509
theorem B35064035 : Blo 1823613 35064035 := bstep (se 1 (by rfl) ⟨26298026, by rfl⟩ : syracuseStep 35064035 = 52596053) B52596053
theorem B2738417 : Blo 1823613 2738417 := bstep (se 2 (by rfl) ⟨1026906, by rfl⟩ : syracuseStep 2738417 = 2053813) B2053813
theorem B3557699 : Blo 1823613 3557699 := bstep (se 1 (by rfl) ⟨2668274, by rfl⟩ : syracuseStep 3557699 = 5336549) B5336549
theorem B4106609 : Blo 1823613 4106609 := bstep (se 2 (by rfl) ⟨1539978, by rfl⟩ : syracuseStep 4106609 = 3079957) B3079957
theorem B4106627 : Blo 1823613 4106627 := bstep (se 1 (by rfl) ⟨3079970, by rfl⟩ : syracuseStep 4106627 = 6159941) B6159941
theorem B11692421 : Blo 1823613 11692421 := bstep (se 4 (by rfl) ⟨1096164, by rfl⟩ : syracuseStep 11692421 = 2192329) B2192329
theorem B7793101 : Blo 1823613 7793101 := bstep (se 3 (by rfl) ⟨1461206, by rfl⟩ : syracuseStep 7793101 = 2922413) B2922413
theorem B4934125 : Blo 1823613 4934125 := bstep (se 3 (by rfl) ⟨925148, by rfl⟩ : syracuseStep 4934125 = 1850297) B1850297
theorem B6154865 : Blo 1823613 6154865 := bstep (se 2 (by rfl) ⟨2308074, by rfl⟩ : syracuseStep 6154865 = 4616149) B4616149
theorem B13855373 : Blo 1823613 13855373 := bstep (se 3 (by rfl) ⟨2597882, by rfl⟩ : syracuseStep 13855373 = 5195765) B5195765
theorem B4106897 : Blo 1823613 4106897 := bstep (se 2 (by rfl) ⟨1540086, by rfl⟩ : syracuseStep 4106897 = 3080173) B3080173
theorem B4106915 : Blo 1823613 4106915 := bstep (se 1 (by rfl) ⟨3080186, by rfl⟩ : syracuseStep 4106915 = 6160373) B6160373
theorem B17541859 : Blo 1823613 17541859 := bstep (se 1 (by rfl) ⟨13156394, by rfl⟩ : syracuseStep 17541859 = 26312789) B26312789
theorem B21056269 : Blo 1823613 21056269 := bstep (se 3 (by rfl) ⟨3948050, by rfl⟩ : syracuseStep 21056269 = 7896101) B7896101
theorem B4934449 : Blo 1823613 4934449 := bstep (se 2 (by rfl) ⟨1850418, by rfl⟩ : syracuseStep 4934449 = 3700837) B3700837
theorem B4934513 : Blo 1823613 4934513 := bstep (se 2 (by rfl) ⟨1850442, by rfl⟩ : syracuseStep 4934513 = 3700885) B3700885
theorem B4107185 : Blo 1823613 4107185 := bstep (se 2 (by rfl) ⟨1540194, by rfl⟩ : syracuseStep 4107185 = 3080389) B3080389
theorem B4107203 : Blo 1823613 4107203 := bstep (se 1 (by rfl) ⟨3080402, by rfl⟩ : syracuseStep 4107203 = 6160805) B6160805
theorem B6155405 : Blo 1823613 6155405 := bstep (se 3 (by rfl) ⟨1154138, by rfl⟩ : syracuseStep 6155405 = 2308277) B2308277
theorem B5844109 : Blo 1823613 5844109 := bstep (se 3 (by rfl) ⟨1095770, by rfl⟩ : syracuseStep 5844109 = 2191541) B2191541
theorem B9235619 : Blo 1823613 9235619 := bstep (se 1 (by rfl) ⟨6926714, by rfl⟩ : syracuseStep 9235619 = 13853429) B13853429
theorem B4811939 : Blo 1823613 4811939 := bstep (se 1 (by rfl) ⟨3608954, by rfl⟩ : syracuseStep 4811939 = 7217909) B7217909
theorem B5196973 : Blo 1823613 5196973 := bstep (se 3 (by rfl) ⟨974432, by rfl⟩ : syracuseStep 5196973 = 1948865) B1948865
theorem B6155459 : Blo 1823613 6155459 := bstep (se 1 (by rfl) ⟨4616594, by rfl⟩ : syracuseStep 6155459 = 9233189) B9233189
theorem B4107473 : Blo 1823613 4107473 := bstep (se 2 (by rfl) ⟨1540302, by rfl⟩ : syracuseStep 4107473 = 3080605) B3080605
theorem B4107491 : Blo 1823613 4107491 := bstep (se 1 (by rfl) ⟨3080618, by rfl⟩ : syracuseStep 4107491 = 6161237) B6161237
theorem B8432909 : Blo 1823613 8432909 := bstep (se 3 (by rfl) ⟨1581170, by rfl⟩ : syracuseStep 8432909 = 3162341) B3162341
theorem B6155729 : Blo 1823613 6155729 := bstep (se 2 (by rfl) ⟨2308398, by rfl⟩ : syracuseStep 6155729 = 4616797) B4616797
theorem B11685347 : Blo 1823613 11685347 := bstep (se 1 (by rfl) ⟨8764010, by rfl⟩ : syracuseStep 11685347 = 17528021) B17528021
theorem B10391075 : Blo 1823613 10391075 := bstep (se 1 (by rfl) ⟨7793306, by rfl⟩ : syracuseStep 10391075 = 15586613) B15586613
theorem B2051635 : Blo 1823613 2051635 := bstep (se 1 (by rfl) ⟨1538726, by rfl⟩ : syracuseStep 2051635 = 3077453) B3077453
theorem B3894979 : Blo 1823613 3894979 := bstep (se 1 (by rfl) ⟨2921234, by rfl⟩ : syracuseStep 3894979 = 5842469) B5842469
theorem B2051779 : Blo 1823613 2051779 := bstep (se 1 (by rfl) ⟨1538834, by rfl⟩ : syracuseStep 2051779 = 3077669) B3077669
theorem B6926093 : Blo 1823613 6926093 := bstep (se 3 (by rfl) ⟨1298642, by rfl⟩ : syracuseStep 6926093 = 2597285) B2597285
theorem B2051923 : Blo 1823613 2051923 := bstep (se 1 (by rfl) ⟨1538942, by rfl⟩ : syracuseStep 2051923 = 3077885) B3077885
theorem B4616099 : Blo 1823613 4616099 := bstep (se 1 (by rfl) ⟨3462074, by rfl⟩ : syracuseStep 4616099 = 6924149) B6924149
theorem B11685809 : Blo 1823613 11685809 := bstep (se 2 (by rfl) ⟨4382178, by rfl⟩ : syracuseStep 11685809 = 8764357) B8764357
theorem B9236429 : Blo 1823613 9236429 := bstep (se 3 (by rfl) ⟨1731830, by rfl⟩ : syracuseStep 9236429 = 3463661) B3463661
theorem B2052067 : Blo 1823613 2052067 := bstep (se 1 (by rfl) ⟨1539050, by rfl⟩ : syracuseStep 2052067 = 3078101) B3078101
theorem B6156269 : Blo 1823613 6156269 := bstep (se 3 (by rfl) ⟨1154300, by rfl⟩ : syracuseStep 6156269 = 2308601) B2308601
theorem B10539013 : Blo 1823613 10539013 := bstep (se 4 (by rfl) ⟨988032, by rfl⟩ : syracuseStep 10539013 = 1976065) B1976065
theorem B6156323 : Blo 1823613 6156323 := bstep (se 1 (by rfl) ⟨4617242, by rfl⟩ : syracuseStep 6156323 = 9234485) B9234485
theorem B4616291 : Blo 1823613 4616291 := bstep (se 1 (by rfl) ⟨3462218, by rfl⟩ : syracuseStep 4616291 = 6924437) B6924437
theorem B14241905 : Blo 1823613 14241905 := bstep (se 2 (by rfl) ⟨5340714, by rfl⟩ : syracuseStep 14241905 = 10681429) B10681429
theorem B2052211 : Blo 1823613 2052211 := bstep (se 1 (by rfl) ⟨1539158, by rfl⟩ : syracuseStep 2052211 = 3078317) B3078317
theorem B5198033 : Blo 1823613 5198033 := bstep (se 2 (by rfl) ⟨1949262, by rfl⟩ : syracuseStep 5198033 = 3898525) B3898525
theorem B2633969 : Blo 1823613 2633969 := bstep (se 2 (by rfl) ⟨987738, by rfl⟩ : syracuseStep 2633969 = 1975477) B1975477
theorem B2052355 : Blo 1823613 2052355 := bstep (se 1 (by rfl) ⟨1539266, by rfl⟩ : syracuseStep 2052355 = 3078533) B3078533
theorem B6156593 : Blo 1823613 6156593 := bstep (se 2 (by rfl) ⟨2308722, by rfl⟩ : syracuseStep 6156593 = 4617445) B4617445
theorem B2634067 : Blo 1823613 2634067 := bstep (se 1 (by rfl) ⟨1975550, by rfl⟩ : syracuseStep 2634067 = 3951101) B3951101
theorem B3895697 : Blo 1823613 3895697 := bstep (se 2 (by rfl) ⟨1460886, by rfl⟩ : syracuseStep 3895697 = 2921773) B2921773
theorem B2052499 : Blo 1823613 2052499 := bstep (se 1 (by rfl) ⟨1539374, by rfl⟩ : syracuseStep 2052499 = 3078749) B3078749
theorem B10392077 : Blo 1823613 10392077 := bstep (se 3 (by rfl) ⟨1948514, by rfl⟩ : syracuseStep 10392077 = 3897029) B3897029
theorem B2052643 : Blo 1823613 2052643 := bstep (se 1 (by rfl) ⟨1539482, by rfl⟩ : syracuseStep 2052643 = 3078965) B3078965
theorem B6926897 : Blo 1823613 6926897 := bstep (se 2 (by rfl) ⟨2597586, by rfl⟩ : syracuseStep 6926897 = 5195173) B5195173
theorem B5845571 : Blo 1823613 5845571 := bstep (se 1 (by rfl) ⟨4384178, by rfl⟩ : syracuseStep 5845571 = 8768357) B8768357
theorem B2052787 : Blo 1823613 2052787 := bstep (se 1 (by rfl) ⟨1539590, by rfl⟩ : syracuseStep 2052787 = 3079181) B3079181
theorem B3699427 : Blo 1823613 3699427 := bstep (se 1 (by rfl) ⟨2774570, by rfl⟩ : syracuseStep 3699427 = 5549141) B5549141
theorem B8885027 : Blo 1823613 8885027 := bstep (se 1 (by rfl) ⟨6663770, by rfl⟩ : syracuseStep 8885027 = 13327541) B13327541
theorem B2052931 : Blo 1823613 2052931 := bstep (se 1 (by rfl) ⟨1539698, by rfl⟩ : syracuseStep 2052931 = 3079397) B3079397
theorem B6157133 : Blo 1823613 6157133 := bstep (se 3 (by rfl) ⟨1154462, by rfl⟩ : syracuseStep 6157133 = 2308925) B2308925
theorem B5845841 : Blo 1823613 5845841 := bstep (se 2 (by rfl) ⟨2192190, by rfl⟩ : syracuseStep 5845841 = 4384381) B4384381
theorem B5198705 : Blo 1823613 5198705 := bstep (se 2 (by rfl) ⟨1949514, by rfl⟩ : syracuseStep 5198705 = 3899029) B3899029
theorem B1823619 : Blo 1823613 1823619 := bstep (se 1 (by rfl) ⟨1367714, by rfl⟩ : syracuseStep 1823619 = 2735429) B2735429
theorem B6157187 : Blo 1823613 6157187 := bstep (se 1 (by rfl) ⟨4617890, by rfl⟩ : syracuseStep 6157187 = 9235781) B9235781
theorem B3896209 : Blo 1823613 3896209 := bstep (se 2 (by rfl) ⟨1461078, by rfl⟩ : syracuseStep 3896209 = 2922157) B2922157
theorem B1823635 : Blo 1823613 1823635 := bstep (se 1 (by rfl) ⟨1367726, by rfl⟩ : syracuseStep 1823635 = 2735453) B2735453
theorem B2921363 : Blo 1823613 2921363 := bstep (se 1 (by rfl) ⟨2191022, by rfl⟩ : syracuseStep 2921363 = 4382045) B4382045
theorem B1823651 : Blo 1823613 1823651 := bstep (se 1 (by rfl) ⟨1367738, by rfl⟩ : syracuseStep 1823651 = 2735477) B2735477
theorem B1823667 : Blo 1823613 1823667 := bstep (se 1 (by rfl) ⟨1367750, by rfl⟩ : syracuseStep 1823667 = 2735501) B2735501
theorem B1823683 : Blo 1823613 1823683 := bstep (se 1 (by rfl) ⟨1367762, by rfl⟩ : syracuseStep 1823683 = 2735525) B2735525
theorem B13849541 : Blo 1823613 13849541 := bstep (se 4 (by rfl) ⟨1298394, by rfl⟩ : syracuseStep 13849541 = 2596789) B2596789
theorem B3462097 : Blo 1823613 3462097 := bstep (se 2 (by rfl) ⟨1298286, by rfl⟩ : syracuseStep 3462097 = 2596573) B2596573
theorem B1823699 : Blo 1823613 1823699 := bstep (se 1 (by rfl) ⟨1367774, by rfl⟩ : syracuseStep 1823699 = 2735549) B2735549
theorem B2053075 : Blo 1823613 2053075 := bstep (se 1 (by rfl) ⟨1539806, by rfl⟩ : syracuseStep 2053075 = 3079613) B3079613
theorem B1823715 : Blo 1823613 1823715 := bstep (se 1 (by rfl) ⟨1367786, by rfl⟩ : syracuseStep 1823715 = 2735573) B2735573
theorem B7214051 : Blo 1823613 7214051 := bstep (se 1 (by rfl) ⟨5410538, by rfl⟩ : syracuseStep 7214051 = 10821077) B10821077
theorem B6239213 : Blo 1823613 6239213 := bstep (se 3 (by rfl) ⟨1169852, by rfl⟩ : syracuseStep 6239213 = 2339705) B2339705
theorem B1823731 : Blo 1823613 1823731 := bstep (se 1 (by rfl) ⟨1367798, by rfl⟩ : syracuseStep 1823731 = 2735597) B2735597
theorem B1823747 : Blo 1823613 1823747 := bstep (se 1 (by rfl) ⟨1367810, by rfl⟩ : syracuseStep 1823747 = 2735621) B2735621
theorem B4617233 : Blo 1823613 4617233 := bstep (se 2 (by rfl) ⟨1731462, by rfl⟩ : syracuseStep 4617233 = 3462925) B3462925
theorem B1823763 : Blo 1823613 1823763 := bstep (se 1 (by rfl) ⟨1367822, by rfl⟩ : syracuseStep 1823763 = 2735645) B2735645
theorem B2774035 : Blo 1823613 2774035 := bstep (se 1 (by rfl) ⟨2080526, by rfl⟩ : syracuseStep 2774035 = 4161053) B4161053
theorem B1823779 : Blo 1823613 1823779 := bstep (se 1 (by rfl) ⟨1367834, by rfl⟩ : syracuseStep 1823779 = 2735669) B2735669
theorem B1823795 : Blo 1823613 1823795 := bstep (se 1 (by rfl) ⟨1367846, by rfl⟩ : syracuseStep 1823795 = 2735693) B2735693
theorem B2028595 : Blo 1823613 2028595 := bstep (se 1 (by rfl) ⟨1521446, by rfl⟩ : syracuseStep 2028595 = 3042893) B3042893
theorem B1823811 : Blo 1823613 1823811 := bstep (se 1 (by rfl) ⟨1367858, by rfl⟩ : syracuseStep 1823811 = 2735717) B2735717
theorem B4617283 : Blo 1823613 4617283 := bstep (se 1 (by rfl) ⟨3462962, by rfl⟩ : syracuseStep 4617283 = 6925925) B6925925
theorem B1823827 : Blo 1823613 1823827 := bstep (se 1 (by rfl) ⟨1367870, by rfl⟩ : syracuseStep 1823827 = 2735741) B2735741
theorem B2921555 : Blo 1823613 2921555 := bstep (se 1 (by rfl) ⟨2191166, by rfl⟩ : syracuseStep 2921555 = 4382333) B4382333
theorem B1823843 : Blo 1823613 1823843 := bstep (se 1 (by rfl) ⟨1367882, by rfl⟩ : syracuseStep 1823843 = 2735765) B2735765
theorem B2053219 : Blo 1823613 2053219 := bstep (se 1 (by rfl) ⟨1539914, by rfl⟩ : syracuseStep 2053219 = 3079829) B3079829
theorem B3462257 : Blo 1823613 3462257 := bstep (se 2 (by rfl) ⟨1298346, by rfl⟩ : syracuseStep 3462257 = 2596693) B2596693
theorem B1823859 : Blo 1823613 1823859 := bstep (se 1 (by rfl) ⟨1367894, by rfl⟩ : syracuseStep 1823859 = 2735789) B2735789
theorem B1823875 : Blo 1823613 1823875 := bstep (se 1 (by rfl) ⟨1367906, by rfl⟩ : syracuseStep 1823875 = 2735813) B2735813
theorem B6157457 : Blo 1823613 6157457 := bstep (se 2 (by rfl) ⟨2309046, by rfl⟩ : syracuseStep 6157457 = 4618093) B4618093
theorem B1823891 : Blo 1823613 1823891 := bstep (se 1 (by rfl) ⟨1367918, by rfl⟩ : syracuseStep 1823891 = 2735837) B2735837
theorem B1823907 : Blo 1823613 1823907 := bstep (se 1 (by rfl) ⟨1367930, by rfl⟩ : syracuseStep 1823907 = 2735861) B2735861
theorem B1823923 : Blo 1823613 1823923 := bstep (se 1 (by rfl) ⟨1367942, by rfl⟩ : syracuseStep 1823923 = 2735885) B2735885
theorem B1823939 : Blo 1823613 1823939 := bstep (se 1 (by rfl) ⟨1367954, by rfl⟩ : syracuseStep 1823939 = 2735909) B2735909
theorem B6927565 : Blo 1823613 6927565 := bstep (se 3 (by rfl) ⟨1298918, by rfl⟩ : syracuseStep 6927565 = 2597837) B2597837
theorem B4617425 : Blo 1823613 4617425 := bstep (se 2 (by rfl) ⟨1731534, by rfl⟩ : syracuseStep 4617425 = 3463069) B3463069
theorem B1823955 : Blo 1823613 1823955 := bstep (se 1 (by rfl) ⟨1367966, by rfl⟩ : syracuseStep 1823955 = 2735933) B2735933
theorem B1823971 : Blo 1823613 1823971 := bstep (se 1 (by rfl) ⟨1367978, by rfl⟩ : syracuseStep 1823971 = 2735957) B2735957
theorem B1823987 : Blo 1823613 1823987 := bstep (se 1 (by rfl) ⟨1367990, by rfl⟩ : syracuseStep 1823987 = 2735981) B2735981
theorem B2192627 : Blo 1823613 2192627 := bstep (se 1 (by rfl) ⟨1644470, by rfl⟩ : syracuseStep 2192627 = 3288941) B3288941
theorem B2053363 : Blo 1823613 2053363 := bstep (se 1 (by rfl) ⟨1540022, by rfl⟩ : syracuseStep 2053363 = 3080045) B3080045
theorem B1824003 : Blo 1823613 1824003 := bstep (se 1 (by rfl) ⟨1368002, by rfl⟩ : syracuseStep 1824003 = 2736005) B2736005
theorem B6239501 : Blo 1823613 6239501 := bstep (se 3 (by rfl) ⟨1169906, by rfl⟩ : syracuseStep 6239501 = 2339813) B2339813
theorem B1824019 : Blo 1823613 1824019 := bstep (se 1 (by rfl) ⟨1368014, by rfl⟩ : syracuseStep 1824019 = 2736029) B2736029
theorem B1824035 : Blo 1823613 1824035 := bstep (se 1 (by rfl) ⟨1368026, by rfl⟩ : syracuseStep 1824035 = 2736053) B2736053
theorem B1824051 : Blo 1823613 1824051 := bstep (se 1 (by rfl) ⟨1368038, by rfl⟩ : syracuseStep 1824051 = 2736077) B2736077
theorem B1824067 : Blo 1823613 1824067 := bstep (se 1 (by rfl) ⟨1368050, by rfl⟩ : syracuseStep 1824067 = 2736101) B2736101
theorem B1824083 : Blo 1823613 1824083 := bstep (se 1 (by rfl) ⟨1368062, by rfl⟩ : syracuseStep 1824083 = 2736125) B2736125
theorem B3077473 : Blo 1823613 3077473 := bstep (se 2 (by rfl) ⟨1154052, by rfl⟩ : syracuseStep 3077473 = 2308105) B2308105
theorem B1824099 : Blo 1823613 1824099 := bstep (se 1 (by rfl) ⟨1368074, by rfl⟩ : syracuseStep 1824099 = 2736149) B2736149
theorem B1824115 : Blo 1823613 1824115 := bstep (se 1 (by rfl) ⟨1368086, by rfl⟩ : syracuseStep 1824115 = 2736173) B2736173
theorem B3077507 : Blo 1823613 3077507 := bstep (se 1 (by rfl) ⟨2308130, by rfl⟩ : syracuseStep 3077507 = 4616261) B4616261
theorem B1824131 : Blo 1823613 1824131 := bstep (se 1 (by rfl) ⟨1368098, by rfl⟩ : syracuseStep 1824131 = 2736197) B2736197
theorem B2053507 : Blo 1823613 2053507 := bstep (se 1 (by rfl) ⟨1540130, by rfl⟩ : syracuseStep 2053507 = 3080261) B3080261
theorem B1824147 : Blo 1823613 1824147 := bstep (se 1 (by rfl) ⟨1368110, by rfl⟩ : syracuseStep 1824147 = 2736221) B2736221
theorem B1824163 : Blo 1823613 1824163 := bstep (se 1 (by rfl) ⟨1368122, by rfl⟩ : syracuseStep 1824163 = 2736245) B2736245
theorem B2774449 : Blo 1823613 2774449 := bstep (se 2 (by rfl) ⟨1040418, by rfl⟩ : syracuseStep 2774449 = 2080837) B2080837
theorem B1824179 : Blo 1823613 1824179 := bstep (se 1 (by rfl) ⟨1368134, by rfl⟩ : syracuseStep 1824179 = 2736269) B2736269
theorem B1824195 : Blo 1823613 1824195 := bstep (se 1 (by rfl) ⟨1368146, by rfl⟩ : syracuseStep 1824195 = 2736293) B2736293
theorem B1824211 : Blo 1823613 1824211 := bstep (se 1 (by rfl) ⟨1368158, by rfl⟩ : syracuseStep 1824211 = 2736317) B2736317
theorem B1824227 : Blo 1823613 1824227 := bstep (se 1 (by rfl) ⟨1368170, by rfl⟩ : syracuseStep 1824227 = 2736341) B2736341
theorem B14046691 : Blo 1823613 14046691 := bstep (se 1 (by rfl) ⟨10535018, by rfl⟩ : syracuseStep 14046691 = 21070037) B21070037
theorem B13858289 : Blo 1823613 13858289 := bstep (se 2 (by rfl) ⟨5196858, by rfl⟩ : syracuseStep 13858289 = 10393717) B10393717
theorem B1824243 : Blo 1823613 1824243 := bstep (se 1 (by rfl) ⟨1368182, by rfl⟩ : syracuseStep 1824243 = 2736365) B2736365
theorem B3077635 : Blo 1823613 3077635 := bstep (se 1 (by rfl) ⟨2308226, by rfl⟩ : syracuseStep 3077635 = 4616453) B4616453
theorem B3462659 : Blo 1823613 3462659 := bstep (se 1 (by rfl) ⟨2596994, by rfl⟩ : syracuseStep 3462659 = 5193989) B5193989
theorem B1824259 : Blo 1823613 1824259 := bstep (se 1 (by rfl) ⟨1368194, by rfl⟩ : syracuseStep 1824259 = 2736389) B2736389
theorem B1824275 : Blo 1823613 1824275 := bstep (se 1 (by rfl) ⟨1368206, by rfl⟩ : syracuseStep 1824275 = 2736413) B2736413
theorem B2053651 : Blo 1823613 2053651 := bstep (se 1 (by rfl) ⟨1540238, by rfl⟩ : syracuseStep 2053651 = 3080477) B3080477
theorem B1824291 : Blo 1823613 1824291 := bstep (se 1 (by rfl) ⟨1368218, by rfl⟩ : syracuseStep 1824291 = 2736437) B2736437
theorem B1824307 : Blo 1823613 1824307 := bstep (se 1 (by rfl) ⟨1368230, by rfl⟩ : syracuseStep 1824307 = 2736461) B2736461
theorem B1824323 : Blo 1823613 1824323 := bstep (se 1 (by rfl) ⟨1368242, by rfl⟩ : syracuseStep 1824323 = 2736485) B2736485
theorem B2192963 : Blo 1823613 2192963 := bstep (se 1 (by rfl) ⟨1644722, by rfl⟩ : syracuseStep 2192963 = 3289445) B3289445
theorem B1824339 : Blo 1823613 1824339 := bstep (se 1 (by rfl) ⟨1368254, by rfl⟩ : syracuseStep 1824339 = 2736509) B2736509
theorem B1824355 : Blo 1823613 1824355 := bstep (se 1 (by rfl) ⟨1368266, by rfl⟩ : syracuseStep 1824355 = 2736533) B2736533
theorem B1824371 : Blo 1823613 1824371 := bstep (se 1 (by rfl) ⟨1368278, by rfl⟩ : syracuseStep 1824371 = 2736557) B2736557
theorem B1824387 : Blo 1823613 1824387 := bstep (se 1 (by rfl) ⟨1368290, by rfl⟩ : syracuseStep 1824387 = 2736581) B2736581
theorem B3077777 : Blo 1823613 3077777 := bstep (se 2 (by rfl) ⟨1154166, by rfl⟩ : syracuseStep 3077777 = 2308333) B2308333
theorem B1824403 : Blo 1823613 1824403 := bstep (se 1 (by rfl) ⟨1368302, by rfl⟩ : syracuseStep 1824403 = 2736605) B2736605
theorem B1824419 : Blo 1823613 1824419 := bstep (se 1 (by rfl) ⟨1368314, by rfl⟩ : syracuseStep 1824419 = 2736629) B2736629
theorem B2053795 : Blo 1823613 2053795 := bstep (se 1 (by rfl) ⟨1540346, by rfl⟩ : syracuseStep 2053795 = 3080693) B3080693
theorem B6157997 : Blo 1823613 6157997 := bstep (se 3 (by rfl) ⟨1154624, by rfl⟩ : syracuseStep 6157997 = 2309249) B2309249
theorem B1824435 : Blo 1823613 1824435 := bstep (se 1 (by rfl) ⟨1368326, by rfl⟩ : syracuseStep 1824435 = 2736653) B2736653
theorem B1824451 : Blo 1823613 1824451 := bstep (se 1 (by rfl) ⟨1368338, by rfl⟩ : syracuseStep 1824451 = 2736677) B2736677
theorem B1824467 : Blo 1823613 1824467 := bstep (se 1 (by rfl) ⟨1368350, by rfl⟩ : syracuseStep 1824467 = 2736701) B2736701
theorem B2774753 : Blo 1823613 2774753 := bstep (se 2 (by rfl) ⟨1040532, by rfl⟩ : syracuseStep 2774753 = 2081065) B2081065
theorem B1824483 : Blo 1823613 1824483 := bstep (se 1 (by rfl) ⟨1368362, by rfl⟩ : syracuseStep 1824483 = 2736725) B2736725
theorem B6158051 : Blo 1823613 6158051 := bstep (se 1 (by rfl) ⟨4618538, by rfl⟩ : syracuseStep 6158051 = 9237077) B9237077
theorem B1824499 : Blo 1823613 1824499 := bstep (se 1 (by rfl) ⟨1368374, by rfl⟩ : syracuseStep 1824499 = 2736749) B2736749
theorem B1824515 : Blo 1823613 1824515 := bstep (se 1 (by rfl) ⟨1368386, by rfl⟩ : syracuseStep 1824515 = 2736773) B2736773
theorem B3077905 : Blo 1823613 3077905 := bstep (se 2 (by rfl) ⟨1154214, by rfl⟩ : syracuseStep 3077905 = 2308429) B2308429
theorem B1824531 : Blo 1823613 1824531 := bstep (se 1 (by rfl) ⟨1368398, by rfl⟩ : syracuseStep 1824531 = 2736797) B2736797
theorem B1824547 : Blo 1823613 1824547 := bstep (se 1 (by rfl) ⟨1368410, by rfl⟩ : syracuseStep 1824547 = 2736821) B2736821
theorem B3077939 : Blo 1823613 3077939 := bstep (se 1 (by rfl) ⟨2308454, by rfl⟩ : syracuseStep 3077939 = 4616909) B4616909
theorem B1824563 : Blo 1823613 1824563 := bstep (se 1 (by rfl) ⟨1368422, by rfl⟩ : syracuseStep 1824563 = 2736845) B2736845
theorem B1824579 : Blo 1823613 1824579 := bstep (se 1 (by rfl) ⟨1368434, by rfl⟩ : syracuseStep 1824579 = 2736869) B2736869
theorem B1824595 : Blo 1823613 1824595 := bstep (se 1 (by rfl) ⟨1368446, by rfl⟩ : syracuseStep 1824595 = 2736893) B2736893
theorem B1824611 : Blo 1823613 1824611 := bstep (se 1 (by rfl) ⟨1368458, by rfl⟩ : syracuseStep 1824611 = 2736917) B2736917
theorem B3700579 : Blo 1823613 3700579 := bstep (se 1 (by rfl) ⟨2775434, by rfl⟩ : syracuseStep 3700579 = 5550869) B5550869
theorem B11695985 : Blo 1823613 11695985 := bstep (se 2 (by rfl) ⟨4385994, by rfl⟩ : syracuseStep 11695985 = 8771989) B8771989
theorem B1824627 : Blo 1823613 1824627 := bstep (se 1 (by rfl) ⟨1368470, by rfl⟩ : syracuseStep 1824627 = 2736941) B2736941
theorem B1824643 : Blo 1823613 1824643 := bstep (se 1 (by rfl) ⟨1368482, by rfl⟩ : syracuseStep 1824643 = 2736965) B2736965
theorem B1824659 : Blo 1823613 1824659 := bstep (se 1 (by rfl) ⟨1368494, by rfl⟩ : syracuseStep 1824659 = 2736989) B2736989
theorem B1824675 : Blo 1823613 1824675 := bstep (se 1 (by rfl) ⟨1368506, by rfl⟩ : syracuseStep 1824675 = 2737013) B2737013
theorem B3078067 : Blo 1823613 3078067 := bstep (se 1 (by rfl) ⟨2308550, by rfl⟩ : syracuseStep 3078067 = 4617101) B4617101
theorem B1824691 : Blo 1823613 1824691 := bstep (se 1 (by rfl) ⟨1368518, by rfl⟩ : syracuseStep 1824691 = 2737037) B2737037
theorem B1824707 : Blo 1823613 1824707 := bstep (se 1 (by rfl) ⟨1368530, by rfl⟩ : syracuseStep 1824707 = 2737061) B2737061
theorem B1824723 : Blo 1823613 1824723 := bstep (se 1 (by rfl) ⟨1368542, by rfl⟩ : syracuseStep 1824723 = 2737085) B2737085
theorem B3086291 : Blo 1823613 3086291 := bstep (se 1 (by rfl) ⟨2314718, by rfl⟩ : syracuseStep 3086291 = 4629437) B4629437
theorem B1824739 : Blo 1823613 1824739 := bstep (se 1 (by rfl) ⟨1368554, by rfl⟩ : syracuseStep 1824739 = 2737109) B2737109
theorem B6928355 : Blo 1823613 6928355 := bstep (se 1 (by rfl) ⟨5196266, by rfl⟩ : syracuseStep 6928355 = 10392533) B10392533
theorem B6158321 : Blo 1823613 6158321 := bstep (se 2 (by rfl) ⟨2309370, by rfl⟩ : syracuseStep 6158321 = 4618741) B4618741
theorem B1824755 : Blo 1823613 1824755 := bstep (se 1 (by rfl) ⟨1368566, by rfl⟩ : syracuseStep 1824755 = 2737133) B2737133
theorem B1824771 : Blo 1823613 1824771 := bstep (se 1 (by rfl) ⟨1368578, by rfl⟩ : syracuseStep 1824771 = 2737157) B2737157
theorem B2308115 : Blo 1823613 2308115 := bstep (se 1 (by rfl) ⟨1731086, by rfl⟩ : syracuseStep 2308115 = 3462173) B3462173
theorem B1824787 : Blo 1823613 1824787 := bstep (se 1 (by rfl) ⟨1368590, by rfl⟩ : syracuseStep 1824787 = 2737181) B2737181
theorem B1824803 : Blo 1823613 1824803 := bstep (se 1 (by rfl) ⟨1368602, by rfl⟩ : syracuseStep 1824803 = 2737205) B2737205
theorem B9492515 : Blo 1823613 9492515 := bstep (se 1 (by rfl) ⟨7119386, by rfl⟩ : syracuseStep 9492515 = 14238773) B14238773
theorem B1824819 : Blo 1823613 1824819 := bstep (se 1 (by rfl) ⟨1368614, by rfl⟩ : syracuseStep 1824819 = 2737229) B2737229
theorem B3078209 : Blo 1823613 3078209 := bstep (se 2 (by rfl) ⟨1154328, by rfl⟩ : syracuseStep 3078209 = 2308657) B2308657
theorem B1824835 : Blo 1823613 1824835 := bstep (se 1 (by rfl) ⟨1368626, by rfl⟩ : syracuseStep 1824835 = 2737253) B2737253
theorem B22181957 : Blo 1823613 22181957 := bstep (se 4 (by rfl) ⟨2079558, by rfl⟩ : syracuseStep 22181957 = 4159117) B4159117
theorem B1824851 : Blo 1823613 1824851 := bstep (se 1 (by rfl) ⟨1368638, by rfl⟩ : syracuseStep 1824851 = 2737277) B2737277
theorem B1824867 : Blo 1823613 1824867 := bstep (se 1 (by rfl) ⟨1368650, by rfl⟩ : syracuseStep 1824867 = 2737301) B2737301
theorem B1947763 : Blo 1823613 1947763 := bstep (se 1 (by rfl) ⟨1460822, by rfl⟩ : syracuseStep 1947763 = 2921645) B2921645
theorem B1824883 : Blo 1823613 1824883 := bstep (se 1 (by rfl) ⟨1368662, by rfl⟩ : syracuseStep 1824883 = 2737325) B2737325
theorem B1824899 : Blo 1823613 1824899 := bstep (se 1 (by rfl) ⟨1368674, by rfl⟩ : syracuseStep 1824899 = 2737349) B2737349
theorem B1824915 : Blo 1823613 1824915 := bstep (se 1 (by rfl) ⟨1368686, by rfl⟩ : syracuseStep 1824915 = 2737373) B2737373
theorem B1824931 : Blo 1823613 1824931 := bstep (se 1 (by rfl) ⟨1368698, by rfl⟩ : syracuseStep 1824931 = 2737397) B2737397
theorem B4618417 : Blo 1823613 4618417 := bstep (se 2 (by rfl) ⟨1731906, by rfl⟩ : syracuseStep 4618417 = 3463813) B3463813
theorem B1824947 : Blo 1823613 1824947 := bstep (se 1 (by rfl) ⟨1368710, by rfl⟩ : syracuseStep 1824947 = 2737421) B2737421
theorem B24967349 : Blo 1823613 24967349 := bstep (se 5 (by rfl) ⟨1170344, by rfl⟩ : syracuseStep 24967349 = 2340689) B2340689
theorem B3078337 : Blo 1823613 3078337 := bstep (se 2 (by rfl) ⟨1154376, by rfl⟩ : syracuseStep 3078337 = 2308753) B2308753
theorem B1824963 : Blo 1823613 1824963 := bstep (se 1 (by rfl) ⟨1368722, by rfl⟩ : syracuseStep 1824963 = 2737445) B2737445
theorem B1824979 : Blo 1823613 1824979 := bstep (se 1 (by rfl) ⟨1368734, by rfl⟩ : syracuseStep 1824979 = 2737469) B2737469
theorem B2775251 : Blo 1823613 2775251 := bstep (se 1 (by rfl) ⟨2081438, by rfl⟩ : syracuseStep 2775251 = 4162877) B4162877
theorem B3078371 : Blo 1823613 3078371 := bstep (se 1 (by rfl) ⟨2308778, by rfl⟩ : syracuseStep 3078371 = 4617557) B4617557
theorem B1824995 : Blo 1823613 1824995 := bstep (se 1 (by rfl) ⟨1368746, by rfl⟩ : syracuseStep 1824995 = 2737493) B2737493
theorem B1825011 : Blo 1823613 1825011 := bstep (se 1 (by rfl) ⟨1368758, by rfl⟩ : syracuseStep 1825011 = 2737517) B2737517
theorem B1825027 : Blo 1823613 1825027 := bstep (se 1 (by rfl) ⟨1368770, by rfl⟩ : syracuseStep 1825027 = 2737541) B2737541
theorem B1825043 : Blo 1823613 1825043 := bstep (se 1 (by rfl) ⟨1368782, by rfl⟩ : syracuseStep 1825043 = 2737565) B2737565
theorem B1825059 : Blo 1823613 1825059 := bstep (se 1 (by rfl) ⟨1368794, by rfl⟩ : syracuseStep 1825059 = 2737589) B2737589
theorem B1825075 : Blo 1823613 1825075 := bstep (se 1 (by rfl) ⟨1368806, by rfl⟩ : syracuseStep 1825075 = 2737613) B2737613
theorem B1825091 : Blo 1823613 1825091 := bstep (se 1 (by rfl) ⟨1368818, by rfl⟩ : syracuseStep 1825091 = 2737637) B2737637
theorem B1825107 : Blo 1823613 1825107 := bstep (se 1 (by rfl) ⟨1368830, by rfl⟩ : syracuseStep 1825107 = 2737661) B2737661
theorem B3078499 : Blo 1823613 3078499 := bstep (se 1 (by rfl) ⟨2308874, by rfl⟩ : syracuseStep 3078499 = 4617749) B4617749
theorem B1825123 : Blo 1823613 1825123 := bstep (se 1 (by rfl) ⟨1368842, by rfl⟩ : syracuseStep 1825123 = 2737685) B2737685
theorem B3897713 : Blo 1823613 3897713 := bstep (se 2 (by rfl) ⟨1461642, by rfl⟩ : syracuseStep 3897713 = 2923285) B2923285
theorem B23386481 : Blo 1823613 23386481 := bstep (se 2 (by rfl) ⟨8769930, by rfl⟩ : syracuseStep 23386481 = 17539861) B17539861
theorem B1825139 : Blo 1823613 1825139 := bstep (se 1 (by rfl) ⟨1368854, by rfl⟩ : syracuseStep 1825139 = 2737709) B2737709
theorem B3463555 : Blo 1823613 3463555 := bstep (se 1 (by rfl) ⟨2597666, by rfl⟩ : syracuseStep 3463555 = 5195333) B5195333
theorem B1825155 : Blo 1823613 1825155 := bstep (se 1 (by rfl) ⟨1368866, by rfl⟩ : syracuseStep 1825155 = 2737733) B2737733
theorem B6003085 : Blo 1823613 6003085 := bstep (se 3 (by rfl) ⟨1125578, by rfl⟩ : syracuseStep 6003085 = 2251157) B2251157
theorem B1825171 : Blo 1823613 1825171 := bstep (se 1 (by rfl) ⟨1368878, by rfl⟩ : syracuseStep 1825171 = 2737757) B2737757
theorem B1825187 : Blo 1823613 1825187 := bstep (se 1 (by rfl) ⟨1368890, by rfl⟩ : syracuseStep 1825187 = 2737781) B2737781
theorem B1825203 : Blo 1823613 1825203 := bstep (se 1 (by rfl) ⟨1368902, by rfl⟩ : syracuseStep 1825203 = 2737805) B2737805
theorem B4618691 : Blo 1823613 4618691 := bstep (se 1 (by rfl) ⟨3464018, by rfl⟩ : syracuseStep 4618691 = 6928037) B6928037
theorem B1825219 : Blo 1823613 1825219 := bstep (se 1 (by rfl) ⟨1368914, by rfl⟩ : syracuseStep 1825219 = 2737829) B2737829
theorem B1825235 : Blo 1823613 1825235 := bstep (se 1 (by rfl) ⟨1368926, by rfl⟩ : syracuseStep 1825235 = 2737853) B2737853
theorem B2922977 : Blo 1823613 2922977 := bstep (se 2 (by rfl) ⟨1096116, by rfl⟩ : syracuseStep 2922977 = 2192233) B2192233
theorem B1825251 : Blo 1823613 1825251 := bstep (se 1 (by rfl) ⟨1368938, by rfl⟩ : syracuseStep 1825251 = 2737877) B2737877
theorem B3078641 : Blo 1823613 3078641 := bstep (se 2 (by rfl) ⟨1154490, by rfl⟩ : syracuseStep 3078641 = 2308981) B2308981
theorem B1825267 : Blo 1823613 1825267 := bstep (se 1 (by rfl) ⟨1368950, by rfl⟩ : syracuseStep 1825267 = 2737901) B2737901
theorem B1825283 : Blo 1823613 1825283 := bstep (se 1 (by rfl) ⟨1368962, by rfl⟩ : syracuseStep 1825283 = 2737925) B2737925
theorem B6158861 : Blo 1823613 6158861 := bstep (se 3 (by rfl) ⟨1154786, by rfl⟩ : syracuseStep 6158861 = 2309573) B2309573
theorem B1825299 : Blo 1823613 1825299 := bstep (se 1 (by rfl) ⟨1368974, by rfl⟩ : syracuseStep 1825299 = 2737949) B2737949
theorem B9361955 : Blo 1823613 9361955 := bstep (se 1 (by rfl) ⟨7021466, by rfl⟩ : syracuseStep 9361955 = 14042933) B14042933
theorem B3463715 : Blo 1823613 3463715 := bstep (se 1 (by rfl) ⟨2597786, by rfl⟩ : syracuseStep 3463715 = 5195573) B5195573
theorem B1825315 : Blo 1823613 1825315 := bstep (se 1 (by rfl) ⟨1368986, by rfl⟩ : syracuseStep 1825315 = 2737973) B2737973
theorem B1825331 : Blo 1823613 1825331 := bstep (se 1 (by rfl) ⟨1368998, by rfl⟩ : syracuseStep 1825331 = 2737997) B2737997
theorem B6158915 : Blo 1823613 6158915 := bstep (se 1 (by rfl) ⟨4619186, by rfl⟩ : syracuseStep 6158915 = 9238373) B9238373
theorem B1825347 : Blo 1823613 1825347 := bstep (se 1 (by rfl) ⟨1369010, by rfl⟩ : syracuseStep 1825347 = 2738021) B2738021
theorem B1825363 : Blo 1823613 1825363 := bstep (se 1 (by rfl) ⟨1369022, by rfl⟩ : syracuseStep 1825363 = 2738045) B2738045
theorem B1825379 : Blo 1823613 1825379 := bstep (se 1 (by rfl) ⟨1369034, by rfl⟩ : syracuseStep 1825379 = 2738069) B2738069
theorem B3078769 : Blo 1823613 3078769 := bstep (se 2 (by rfl) ⟨1154538, by rfl⟩ : syracuseStep 3078769 = 2309077) B2309077
theorem B6929009 : Blo 1823613 6929009 := bstep (se 2 (by rfl) ⟨2598378, by rfl⟩ : syracuseStep 6929009 = 5196757) B5196757
theorem B1825395 : Blo 1823613 1825395 := bstep (se 1 (by rfl) ⟨1369046, by rfl⟩ : syracuseStep 1825395 = 2738093) B2738093
theorem B4618883 : Blo 1823613 4618883 := bstep (se 1 (by rfl) ⟨3464162, by rfl⟩ : syracuseStep 4618883 = 6928325) B6928325
theorem B1825411 : Blo 1823613 1825411 := bstep (se 1 (by rfl) ⟨1369058, by rfl⟩ : syracuseStep 1825411 = 2738117) B2738117
theorem B3078803 : Blo 1823613 3078803 := bstep (se 1 (by rfl) ⟨2309102, by rfl⟩ : syracuseStep 3078803 = 4618205) B4618205
theorem B1825427 : Blo 1823613 1825427 := bstep (se 1 (by rfl) ⟨1369070, by rfl⟩ : syracuseStep 1825427 = 2738141) B2738141
theorem B2775713 : Blo 1823613 2775713 := bstep (se 2 (by rfl) ⟨1040892, by rfl⟩ : syracuseStep 2775713 = 2081785) B2081785
theorem B10533539 : Blo 1823613 10533539 := bstep (se 1 (by rfl) ⟨7900154, by rfl⟩ : syracuseStep 10533539 = 15800309) B15800309
theorem B1825443 : Blo 1823613 1825443 := bstep (se 1 (by rfl) ⟨1369082, by rfl⟩ : syracuseStep 1825443 = 2738165) B2738165
theorem B1825459 : Blo 1823613 1825459 := bstep (se 1 (by rfl) ⟨1369094, by rfl⟩ : syracuseStep 1825459 = 2738189) B2738189
theorem B1825475 : Blo 1823613 1825475 := bstep (se 1 (by rfl) ⟨1369106, by rfl⟩ : syracuseStep 1825475 = 2738213) B2738213
theorem B2308819 : Blo 1823613 2308819 := bstep (se 1 (by rfl) ⟨1731614, by rfl⟩ : syracuseStep 2308819 = 3463229) B3463229
theorem B1825491 : Blo 1823613 1825491 := bstep (se 1 (by rfl) ⟨1369118, by rfl⟩ : syracuseStep 1825491 = 2738237) B2738237
theorem B7797475 : Blo 1823613 7797475 := bstep (se 1 (by rfl) ⟨5848106, by rfl⟩ : syracuseStep 7797475 = 11696213) B11696213
theorem B1825507 : Blo 1823613 1825507 := bstep (se 1 (by rfl) ⟨1369130, by rfl⟩ : syracuseStep 1825507 = 2738261) B2738261
theorem B1825523 : Blo 1823613 1825523 := bstep (se 1 (by rfl) ⟨1369142, by rfl⟩ : syracuseStep 1825523 = 2738285) B2738285
theorem B3898115 : Blo 1823613 3898115 := bstep (se 1 (by rfl) ⟨2923586, by rfl⟩ : syracuseStep 3898115 = 5847173) B5847173
theorem B1825539 : Blo 1823613 1825539 := bstep (se 1 (by rfl) ⟨1369154, by rfl⟩ : syracuseStep 1825539 = 2738309) B2738309
theorem B3078931 : Blo 1823613 3078931 := bstep (se 1 (by rfl) ⟨2309198, by rfl⟩ : syracuseStep 3078931 = 4618397) B4618397
theorem B1825555 : Blo 1823613 1825555 := bstep (se 1 (by rfl) ⟨1369166, by rfl⟩ : syracuseStep 1825555 = 2738333) B2738333
theorem B1825571 : Blo 1823613 1825571 := bstep (se 1 (by rfl) ⟨1369178, by rfl⟩ : syracuseStep 1825571 = 2738357) B2738357
theorem B9239345 : Blo 1823613 9239345 := bstep (se 2 (by rfl) ⟨3464754, by rfl⟩ : syracuseStep 9239345 = 6929509) B6929509
theorem B2308915 : Blo 1823613 2308915 := bstep (se 1 (by rfl) ⟨1731686, by rfl⟩ : syracuseStep 2308915 = 3463373) B3463373
theorem B1825587 : Blo 1823613 1825587 := bstep (se 1 (by rfl) ⟨1369190, by rfl⟩ : syracuseStep 1825587 = 2738381) B2738381
theorem B1825603 : Blo 1823613 1825603 := bstep (se 1 (by rfl) ⟨1369202, by rfl⟩ : syracuseStep 1825603 = 2738405) B2738405
theorem B10386245 : Blo 1823613 10386245 := bstep (se 4 (by rfl) ⟨973710, by rfl⟩ : syracuseStep 10386245 = 1947421) B1947421
theorem B6159185 : Blo 1823613 6159185 := bstep (se 2 (by rfl) ⟨2309694, by rfl⟩ : syracuseStep 6159185 = 4619389) B4619389
theorem B3750787 : Blo 1823613 3750787 := bstep (se 1 (by rfl) ⟨2813090, by rfl⟩ : syracuseStep 3750787 = 5626181) B5626181
theorem B8764301 : Blo 1823613 8764301 := bstep (se 3 (by rfl) ⟨1643306, by rfl⟩ : syracuseStep 8764301 = 3286613) B3286613
theorem B3079073 : Blo 1823613 3079073 := bstep (se 2 (by rfl) ⟨1154652, by rfl⟩ : syracuseStep 3079073 = 2309305) B2309305
theorem B5266403 : Blo 1823613 5266403 := bstep (se 1 (by rfl) ⟨3949802, by rfl⟩ : syracuseStep 5266403 = 7899605) B7899605
theorem B4103153 : Blo 1823613 4103153 := bstep (se 2 (by rfl) ⟨1538682, by rfl⟩ : syracuseStep 4103153 = 3077365) B3077365
theorem B4103171 : Blo 1823613 4103171 := bstep (se 1 (by rfl) ⟨3077378, by rfl⟩ : syracuseStep 4103171 = 6154757) B6154757
theorem B3079201 : Blo 1823613 3079201 := bstep (se 2 (by rfl) ⟨1154700, by rfl⟩ : syracuseStep 3079201 = 2309401) B2309401
theorem B3079235 : Blo 1823613 3079235 := bstep (se 1 (by rfl) ⟨2309426, by rfl⟩ : syracuseStep 3079235 = 4618853) B4618853
theorem B44383373 : Blo 1823613 44383373 := bstep (se 3 (by rfl) ⟨8321882, by rfl⟩ : syracuseStep 44383373 = 16643765) B16643765
theorem B3079363 : Blo 1823613 3079363 := bstep (se 1 (by rfl) ⟨2309522, by rfl⟩ : syracuseStep 3079363 = 4619045) B4619045
theorem B7019747 : Blo 1823613 7019747 := bstep (se 1 (by rfl) ⟨5264810, by rfl⟩ : syracuseStep 7019747 = 10529621) B10529621
theorem B5848301 : Blo 1823613 5848301 := bstep (se 3 (by rfl) ⟨1096556, by rfl⟩ : syracuseStep 5848301 = 2193113) B2193113
theorem B10386701 : Blo 1823613 10386701 := bstep (se 3 (by rfl) ⟨1947506, by rfl⟩ : syracuseStep 10386701 = 3895013) B3895013
theorem B4103441 : Blo 1823613 4103441 := bstep (se 2 (by rfl) ⟨1538790, by rfl⟩ : syracuseStep 4103441 = 3077581) B3077581
theorem B4103459 : Blo 1823613 4103459 := bstep (se 1 (by rfl) ⟨3077594, by rfl⟩ : syracuseStep 4103459 = 6155189) B6155189
theorem B2309411 : Blo 1823613 2309411 := bstep (se 1 (by rfl) ⟨1732058, by rfl⟩ : syracuseStep 2309411 = 3464117) B3464117
theorem B2735441 : Blo 1823613 2735441 := bstep (se 2 (by rfl) ⟨1025790, by rfl⟩ : syracuseStep 2735441 = 2051581) B2051581
theorem B3079505 : Blo 1823613 3079505 := bstep (se 2 (by rfl) ⟨1154814, by rfl⟩ : syracuseStep 3079505 = 2309629) B2309629
theorem B2735459 : Blo 1823613 2735459 := bstep (se 1 (by rfl) ⟨2051594, by rfl⟩ : syracuseStep 2735459 = 4103189) B4103189
theorem B1949027 : Blo 1823613 1949027 := bstep (se 1 (by rfl) ⟨1461770, by rfl⟩ : syracuseStep 1949027 = 2923541) B2923541
theorem B6159725 : Blo 1823613 6159725 := bstep (se 3 (by rfl) ⟨1154948, by rfl⟩ : syracuseStep 6159725 = 2309897) B2309897
theorem B10394993 : Blo 1823613 10394993 := bstep (se 2 (by rfl) ⟨3898122, by rfl⟩ : syracuseStep 10394993 = 7796245) B7796245
theorem B2735489 : Blo 1823613 2735489 := bstep (se 2 (by rfl) ⟨1025808, by rfl⟩ : syracuseStep 2735489 = 2051617) B2051617
theorem B2735507 : Blo 1823613 2735507 := bstep (se 1 (by rfl) ⟨2051630, by rfl⟩ : syracuseStep 2735507 = 4103261) B4103261
theorem B6159779 : Blo 1823613 6159779 := bstep (se 1 (by rfl) ⟨4619834, by rfl⟩ : syracuseStep 6159779 = 9239669) B9239669
theorem B2735537 : Blo 1823613 2735537 := bstep (se 2 (by rfl) ⟨1025826, by rfl⟩ : syracuseStep 2735537 = 2051653) B2051653
theorem B2735555 : Blo 1823613 2735555 := bstep (se 1 (by rfl) ⟨2051666, by rfl⟩ : syracuseStep 2735555 = 4103333) B4103333
theorem B2465219 : Blo 1823613 2465219 := bstep (se 1 (by rfl) ⟨1848914, by rfl⟩ : syracuseStep 2465219 = 3697829) B3697829
theorem B3079633 : Blo 1823613 3079633 := bstep (se 2 (by rfl) ⟨1154862, by rfl⟩ : syracuseStep 3079633 = 2309725) B2309725
theorem B2735585 : Blo 1823613 2735585 := bstep (se 2 (by rfl) ⟨1025844, by rfl⟩ : syracuseStep 2735585 = 2051689) B2051689
theorem B2735603 : Blo 1823613 2735603 := bstep (se 1 (by rfl) ⟨2051702, by rfl⟩ : syracuseStep 2735603 = 4103405) B4103405
theorem B3079667 : Blo 1823613 3079667 := bstep (se 1 (by rfl) ⟨2309750, by rfl⟩ : syracuseStep 3079667 = 4619501) B4619501
theorem B2735633 : Blo 1823613 2735633 := bstep (se 2 (by rfl) ⟨1025862, by rfl⟩ : syracuseStep 2735633 = 2051725) B2051725
theorem B2735651 : Blo 1823613 2735651 := bstep (se 1 (by rfl) ⟨2051738, by rfl⟩ : syracuseStep 2735651 = 4103477) B4103477
theorem B4103729 : Blo 1823613 4103729 := bstep (se 2 (by rfl) ⟨1538898, by rfl⟩ : syracuseStep 4103729 = 3077797) B3077797
theorem B4619825 : Blo 1823613 4619825 := bstep (se 2 (by rfl) ⟨1732434, by rfl⟩ : syracuseStep 4619825 = 3464869) B3464869
theorem B2735681 : Blo 1823613 2735681 := bstep (se 2 (by rfl) ⟨1025880, by rfl⟩ : syracuseStep 2735681 = 2051761) B2051761
theorem B4103747 : Blo 1823613 4103747 := bstep (se 1 (by rfl) ⟨3077810, by rfl⟩ : syracuseStep 4103747 = 6155621) B6155621
theorem B3464785 : Blo 1823613 3464785 := bstep (se 2 (by rfl) ⟨1299294, by rfl⟩ : syracuseStep 3464785 = 2598589) B2598589
theorem B2735699 : Blo 1823613 2735699 := bstep (se 1 (by rfl) ⟨2051774, by rfl⟩ : syracuseStep 2735699 = 4103549) B4103549
theorem B4619875 : Blo 1823613 4619875 := bstep (se 1 (by rfl) ⟨3464906, by rfl⟩ : syracuseStep 4619875 = 6929813) B6929813
theorem B2735729 : Blo 1823613 2735729 := bstep (se 2 (by rfl) ⟨1025898, by rfl⟩ : syracuseStep 2735729 = 2051797) B2051797
theorem B3079795 : Blo 1823613 3079795 := bstep (se 1 (by rfl) ⟨2309846, by rfl⟩ : syracuseStep 3079795 = 4619693) B4619693
theorem B2735747 : Blo 1823613 2735747 := bstep (se 1 (by rfl) ⟨2051810, by rfl⟩ : syracuseStep 2735747 = 4103621) B4103621
theorem B3899011 : Blo 1823613 3899011 := bstep (se 1 (by rfl) ⟨2924258, by rfl⟩ : syracuseStep 3899011 = 5848517) B5848517
theorem B2735777 : Blo 1823613 2735777 := bstep (se 2 (by rfl) ⟨1025916, by rfl⟩ : syracuseStep 2735777 = 2051833) B2051833
theorem B6160049 : Blo 1823613 6160049 := bstep (se 2 (by rfl) ⟨2310018, by rfl⟩ : syracuseStep 6160049 = 4620037) B4620037
theorem B2735795 : Blo 1823613 2735795 := bstep (se 1 (by rfl) ⟨2051846, by rfl⟩ : syracuseStep 2735795 = 4103693) B4103693
theorem B2735825 : Blo 1823613 2735825 := bstep (se 2 (by rfl) ⟨1025934, by rfl⟩ : syracuseStep 2735825 = 2051869) B2051869
theorem B2735843 : Blo 1823613 2735843 := bstep (se 1 (by rfl) ⟨2051882, by rfl⟩ : syracuseStep 2735843 = 4103765) B4103765
theorem B4620017 : Blo 1823613 4620017 := bstep (se 2 (by rfl) ⟨1732506, by rfl⟩ : syracuseStep 4620017 = 3465013) B3465013
theorem B2735873 : Blo 1823613 2735873 := bstep (se 2 (by rfl) ⟨1025952, by rfl⟩ : syracuseStep 2735873 = 2051905) B2051905
theorem B3079937 : Blo 1823613 3079937 := bstep (se 2 (by rfl) ⟨1154976, by rfl⟩ : syracuseStep 3079937 = 2309953) B2309953
theorem B2735891 : Blo 1823613 2735891 := bstep (se 1 (by rfl) ⟨2051918, by rfl⟩ : syracuseStep 2735891 = 4103837) B4103837
theorem B2735921 : Blo 1823613 2735921 := bstep (se 2 (by rfl) ⟨1025970, by rfl⟩ : syracuseStep 2735921 = 2051941) B2051941
theorem B2735939 : Blo 1823613 2735939 := bstep (se 1 (by rfl) ⟨2051954, by rfl⟩ : syracuseStep 2735939 = 4103909) B4103909
theorem B4104017 : Blo 1823613 4104017 := bstep (se 2 (by rfl) ⟨1539006, by rfl⟩ : syracuseStep 4104017 = 3078013) B3078013
theorem B2735969 : Blo 1823613 2735969 := bstep (se 2 (by rfl) ⟨1025988, by rfl⟩ : syracuseStep 2735969 = 2051977) B2051977
theorem B4104035 : Blo 1823613 4104035 := bstep (se 1 (by rfl) ⟨3078026, by rfl⟩ : syracuseStep 4104035 = 6156053) B6156053
theorem B2735987 : Blo 1823613 2735987 := bstep (se 1 (by rfl) ⟨2051990, by rfl⟩ : syracuseStep 2735987 = 4103981) B4103981
theorem B3080065 : Blo 1823613 3080065 := bstep (se 2 (by rfl) ⟨1155024, by rfl⟩ : syracuseStep 3080065 = 2310049) B2310049
theorem B2736017 : Blo 1823613 2736017 := bstep (se 2 (by rfl) ⟨1026006, by rfl⟩ : syracuseStep 2736017 = 2052013) B2052013
theorem B2736035 : Blo 1823613 2736035 := bstep (se 1 (by rfl) ⟨2052026, by rfl⟩ : syracuseStep 2736035 = 4104053) B4104053
theorem B3080099 : Blo 1823613 3080099 := bstep (se 1 (by rfl) ⟨2310074, by rfl⟩ : syracuseStep 3080099 = 4620149) B4620149
theorem B2596801 : Blo 1823613 2596801 := bstep (se 2 (by rfl) ⟨973800, by rfl⟩ : syracuseStep 2596801 = 1947601) B1947601
theorem B2736065 : Blo 1823613 2736065 := bstep (se 2 (by rfl) ⟨1026024, by rfl⟩ : syracuseStep 2736065 = 2052049) B2052049
theorem B2736083 : Blo 1823613 2736083 := bstep (se 1 (by rfl) ⟨2052062, by rfl⟩ : syracuseStep 2736083 = 4104125) B4104125
theorem B2310115 : Blo 1823613 2310115 := bstep (se 1 (by rfl) ⟨1732586, by rfl⟩ : syracuseStep 2310115 = 3465173) B3465173
theorem B2736113 : Blo 1823613 2736113 := bstep (se 2 (by rfl) ⟨1026042, by rfl⟩ : syracuseStep 2736113 = 2052085) B2052085
theorem B4104215 : Blo 1823613 4104215 := bstep (se 1 (by rfl) ⟨3078161, by rfl⟩ : syracuseStep 4104215 = 6156323) B6156323
theorem B4620311 : Blo 1823613 4620311 := bstep (se 1 (by rfl) ⟨3465233, by rfl⟩ : syracuseStep 4620311 = 6930467) B6930467
theorem B9240641 : Blo 1823613 9240641 := bstep (se 2 (by rfl) ⟨3465240, by rfl⟩ : syracuseStep 9240641 = 6930481) B6930481
theorem B2736203 : Blo 1823613 2736203 := bstep (se 1 (by rfl) ⟨2052152, by rfl⟩ : syracuseStep 2736203 = 4104305) B4104305
theorem B9494603 : Blo 1823613 9494603 := bstep (se 1 (by rfl) ⟨7120952, by rfl⟩ : syracuseStep 9494603 = 14241905) B14241905
theorem B2736215 : Blo 1823613 2736215 := bstep (se 1 (by rfl) ⟨2052161, by rfl⟩ : syracuseStep 2736215 = 4104323) B4104323
theorem B3080281 : Blo 1823613 3080281 := bstep (se 2 (by rfl) ⟨1155105, by rfl⟩ : syracuseStep 3080281 = 2310211) B2310211
theorem B3465355 : Blo 1823613 3465355 := bstep (se 1 (by rfl) ⟨2599016, by rfl⟩ : syracuseStep 3465355 = 5198033) B5198033
theorem B6160535 : Blo 1823613 6160535 := bstep (se 1 (by rfl) ⟨4620401, by rfl⟩ : syracuseStep 6160535 = 9240803) B9240803
theorem B2597017 : Blo 1823613 2597017 := bstep (se 2 (by rfl) ⟨973881, by rfl⟩ : syracuseStep 2597017 = 1947763) B1947763
theorem B2736281 : Blo 1823613 2736281 := bstep (se 2 (by rfl) ⟨1026105, by rfl⟩ : syracuseStep 2736281 = 2052211) B2052211
theorem B4104395 : Blo 1823613 4104395 := bstep (se 1 (by rfl) ⟨3078296, by rfl⟩ : syracuseStep 4104395 = 6156593) B6156593
theorem B7790813 : Blo 1823613 7790813 := bstep (se 3 (by rfl) ⟨1460777, by rfl⟩ : syracuseStep 7790813 = 2921555) B2921555
theorem B4104449 : Blo 1823613 4104449 := bstep (se 2 (by rfl) ⟨1539168, by rfl⟩ : syracuseStep 4104449 = 3078337) B3078337
theorem B2597131 : Blo 1823613 2597131 := bstep (se 1 (by rfl) ⟨1947848, by rfl⟩ : syracuseStep 2597131 = 3895697) B3895697
theorem B2736395 : Blo 1823613 2736395 := bstep (se 1 (by rfl) ⟨2052296, by rfl⟩ : syracuseStep 2736395 = 4104593) B4104593
theorem B2736407 : Blo 1823613 2736407 := bstep (se 1 (by rfl) ⟨2052305, by rfl⟩ : syracuseStep 2736407 = 4104611) B4104611
theorem B2736473 : Blo 1823613 2736473 := bstep (se 2 (by rfl) ⟨1026177, by rfl⟩ : syracuseStep 2736473 = 2052355) B2052355
theorem B4112819 : Blo 1823613 4112819 := bstep (se 1 (by rfl) ⟨3084614, by rfl⟩ : syracuseStep 4112819 = 6169229) B6169229
theorem B2736587 : Blo 1823613 2736587 := bstep (se 1 (by rfl) ⟨2052440, by rfl⟩ : syracuseStep 2736587 = 4104881) B4104881
theorem B2736599 : Blo 1823613 2736599 := bstep (se 1 (by rfl) ⟨2052449, by rfl⟩ : syracuseStep 2736599 = 4104899) B4104899
theorem B4104665 : Blo 1823613 4104665 := bstep (se 2 (by rfl) ⟨1539249, by rfl⟩ : syracuseStep 4104665 = 3078499) B3078499
theorem B8004113 : Blo 1823613 8004113 := bstep (se 2 (by rfl) ⟨3001542, by rfl⟩ : syracuseStep 8004113 = 6003085) B6003085
theorem B5923351 : Blo 1823613 5923351 := bstep (se 1 (by rfl) ⟨4442513, by rfl⟩ : syracuseStep 5923351 = 8885027) B8885027
theorem B6930967 : Blo 1823613 6930967 := bstep (se 1 (by rfl) ⟨5198225, by rfl⟩ : syracuseStep 6930967 = 10396451) B10396451
theorem B2736665 : Blo 1823613 2736665 := bstep (se 2 (by rfl) ⟨1026249, by rfl⟩ : syracuseStep 2736665 = 2052499) B2052499
theorem B4104755 : Blo 1823613 4104755 := bstep (se 1 (by rfl) ⟨3078566, by rfl⟩ : syracuseStep 4104755 = 6157133) B6157133
theorem B3465803 : Blo 1823613 3465803 := bstep (se 1 (by rfl) ⟨2599352, by rfl⟩ : syracuseStep 3465803 = 5198705) B5198705
theorem B4104791 : Blo 1823613 4104791 := bstep (se 1 (by rfl) ⟨3078593, by rfl⟩ : syracuseStep 4104791 = 6157187) B6157187
theorem B9233027 : Blo 1823613 9233027 := bstep (se 1 (by rfl) ⟨6924770, by rfl⟩ : syracuseStep 9233027 = 13849541) B13849541
theorem B2736779 : Blo 1823613 2736779 := bstep (se 1 (by rfl) ⟨2052584, by rfl⟩ : syracuseStep 2736779 = 4105169) B4105169
theorem B6578833 : Blo 1823613 6578833 := bstep (se 2 (by rfl) ⟨2467062, by rfl⟩ : syracuseStep 6578833 = 4934125) B4934125
theorem B4809367 : Blo 1823613 4809367 := bstep (se 1 (by rfl) ⟨3607025, by rfl⟩ : syracuseStep 4809367 = 7214051) B7214051
theorem B2736791 : Blo 1823613 2736791 := bstep (se 1 (by rfl) ⟨2052593, by rfl⟩ : syracuseStep 2736791 = 4105187) B4105187
theorem B6161075 : Blo 1823613 6161075 := bstep (se 1 (by rfl) ⟨4620806, by rfl⟩ : syracuseStep 6161075 = 9241613) B9241613
theorem B2736857 : Blo 1823613 2736857 := bstep (se 2 (by rfl) ⟨1026321, by rfl⟩ : syracuseStep 2736857 = 2052643) B2052643
theorem B4104971 : Blo 1823613 4104971 := bstep (se 1 (by rfl) ⟨3078728, by rfl⟩ : syracuseStep 4104971 = 6157457) B6157457
theorem B4105025 : Blo 1823613 4105025 := bstep (se 2 (by rfl) ⟨1539384, by rfl⟩ : syracuseStep 4105025 = 3078769) B3078769
theorem B2736971 : Blo 1823613 2736971 := bstep (se 1 (by rfl) ⟨2052728, by rfl⟩ : syracuseStep 2736971 = 4105457) B4105457
theorem B2736983 : Blo 1823613 2736983 := bstep (se 1 (by rfl) ⟨2052737, by rfl⟩ : syracuseStep 2736983 = 4105475) B4105475
theorem B2737049 : Blo 1823613 2737049 := bstep (se 2 (by rfl) ⟨1026393, by rfl⟩ : syracuseStep 2737049 = 2052787) B2052787
theorem B6161345 : Blo 1823613 6161345 := bstep (se 2 (by rfl) ⟨2310504, by rfl⟩ : syracuseStep 6161345 = 4621009) B4621009
theorem B4932569 : Blo 1823613 4932569 := bstep (se 2 (by rfl) ⟨1849713, by rfl⟩ : syracuseStep 4932569 = 3699427) B3699427
theorem B23389145 : Blo 1823613 23389145 := bstep (se 2 (by rfl) ⟨8770929, by rfl⟩ : syracuseStep 23389145 = 17541859) B17541859
theorem B10396633 : Blo 1823613 10396633 := bstep (se 2 (by rfl) ⟨3898737, by rfl⟩ : syracuseStep 10396633 = 7797475) B7797475
theorem B2737163 : Blo 1823613 2737163 := bstep (se 1 (by rfl) ⟨2052872, by rfl⟩ : syracuseStep 2737163 = 4105745) B4105745
theorem B28075025 : Blo 1823613 28075025 := bstep (se 2 (by rfl) ⟨10528134, by rfl⟩ : syracuseStep 28075025 = 21056269) B21056269
theorem B2737175 : Blo 1823613 2737175 := bstep (se 1 (by rfl) ⟨2052881, by rfl⟩ : syracuseStep 2737175 = 4105763) B4105763
theorem B4105241 : Blo 1823613 4105241 := bstep (se 2 (by rfl) ⟨1539465, by rfl⟩ : syracuseStep 4105241 = 3078931) B3078931
theorem B2737241 : Blo 1823613 2737241 := bstep (se 2 (by rfl) ⟨1026465, by rfl⟩ : syracuseStep 2737241 = 2052931) B2052931
theorem B4105331 : Blo 1823613 4105331 := bstep (se 1 (by rfl) ⟨3078998, by rfl⟩ : syracuseStep 4105331 = 6157997) B6157997
theorem B4105367 : Blo 1823613 4105367 := bstep (se 1 (by rfl) ⟨3079025, by rfl⟩ : syracuseStep 4105367 = 6158051) B6158051
theorem B5194945 : Blo 1823613 5194945 := bstep (se 2 (by rfl) ⟨1948104, by rfl⟩ : syracuseStep 5194945 = 3896209) B3896209
theorem B2737355 : Blo 1823613 2737355 := bstep (se 1 (by rfl) ⟨2053016, by rfl⟩ : syracuseStep 2737355 = 4106033) B4106033
theorem B2737367 : Blo 1823613 2737367 := bstep (se 1 (by rfl) ⟨2053025, by rfl⟩ : syracuseStep 2737367 = 4106051) B4106051
theorem B2737433 : Blo 1823613 2737433 := bstep (se 2 (by rfl) ⟨1026537, by rfl⟩ : syracuseStep 2737433 = 2053075) B2053075
theorem B2057527 : Blo 1823613 2057527 := bstep (se 1 (by rfl) ⟨1543145, by rfl⟩ : syracuseStep 2057527 = 3086291) B3086291
theorem B4105547 : Blo 1823613 4105547 := bstep (se 1 (by rfl) ⟨3079160, by rfl⟩ : syracuseStep 4105547 = 6158321) B6158321
theorem B8324441 : Blo 1823613 8324441 := bstep (se 2 (by rfl) ⟨3121665, by rfl⟩ : syracuseStep 8324441 = 6243331) B6243331
theorem B4105601 : Blo 1823613 4105601 := bstep (se 2 (by rfl) ⟨1539600, by rfl⟩ : syracuseStep 4105601 = 3079201) B3079201
theorem B14787971 : Blo 1823613 14787971 := bstep (se 1 (by rfl) ⟨11090978, by rfl⟩ : syracuseStep 14787971 = 22181957) B22181957
theorem B2737547 : Blo 1823613 2737547 := bstep (se 1 (by rfl) ⟨2053160, by rfl⟩ : syracuseStep 2737547 = 4106321) B4106321
theorem B2737559 : Blo 1823613 2737559 := bstep (se 1 (by rfl) ⟨2053169, by rfl⟩ : syracuseStep 2737559 = 4106339) B4106339
theorem B2737625 : Blo 1823613 2737625 := bstep (se 2 (by rfl) ⟨1026609, by rfl⟩ : syracuseStep 2737625 = 2053219) B2053219
theorem B7792145 : Blo 1823613 7792145 := bstep (se 2 (by rfl) ⟨2922054, by rfl⟩ : syracuseStep 7792145 = 5844109) B5844109
theorem B2598475 : Blo 1823613 2598475 := bstep (se 1 (by rfl) ⟨1948856, by rfl⟩ : syracuseStep 2598475 = 3897713) B3897713
theorem B15590987 : Blo 1823613 15590987 := bstep (se 1 (by rfl) ⟨11693240, by rfl⟩ : syracuseStep 15590987 = 23386481) B23386481
theorem B2737739 : Blo 1823613 2737739 := bstep (se 1 (by rfl) ⟨2053304, by rfl⟩ : syracuseStep 2737739 = 4106609) B4106609
theorem B2737751 : Blo 1823613 2737751 := bstep (se 1 (by rfl) ⟨2053313, by rfl⟩ : syracuseStep 2737751 = 4106627) B4106627
theorem B4105817 : Blo 1823613 4105817 := bstep (se 2 (by rfl) ⟨1539681, by rfl⟩ : syracuseStep 4105817 = 3079363) B3079363
theorem B11847269 : Blo 1823613 11847269 := bstep (se 4 (by rfl) ⟨1110681, by rfl⟩ : syracuseStep 11847269 = 2221363) B2221363
theorem B2737817 : Blo 1823613 2737817 := bstep (se 2 (by rfl) ⟨1026681, by rfl⟩ : syracuseStep 2737817 = 2053363) B2053363
theorem B4105907 : Blo 1823613 4105907 := bstep (se 1 (by rfl) ⟨3079430, by rfl⟩ : syracuseStep 4105907 = 6158861) B6158861
theorem B29607605 : Blo 1823613 29607605 := bstep (se 5 (by rfl) ⟨1387856, by rfl⟩ : syracuseStep 29607605 = 2775713) B2775713
theorem B4105943 : Blo 1823613 4105943 := bstep (se 1 (by rfl) ⟨3079457, by rfl⟩ : syracuseStep 4105943 = 6158915) B6158915
theorem B2737931 : Blo 1823613 2737931 := bstep (se 1 (by rfl) ⟨2053448, by rfl⟩ : syracuseStep 2737931 = 4106897) B4106897
theorem B7022359 : Blo 1823613 7022359 := bstep (se 1 (by rfl) ⟨5266769, by rfl⟩ : syracuseStep 7022359 = 10533539) B10533539
theorem B2737943 : Blo 1823613 2737943 := bstep (se 1 (by rfl) ⟨2053457, by rfl⟩ : syracuseStep 2737943 = 4106915) B4106915
theorem B2598743 : Blo 1823613 2598743 := bstep (se 1 (by rfl) ⟨1949057, by rfl⟩ : syracuseStep 2598743 = 3898115) B3898115
theorem B2738009 : Blo 1823613 2738009 := bstep (se 2 (by rfl) ⟨1026753, by rfl⟩ : syracuseStep 2738009 = 2053507) B2053507
theorem B6924163 : Blo 1823613 6924163 := bstep (se 1 (by rfl) ⟨5193122, by rfl⟩ : syracuseStep 6924163 = 10386245) B10386245
theorem B4106123 : Blo 1823613 4106123 := bstep (se 1 (by rfl) ⟨3079592, by rfl⟩ : syracuseStep 4106123 = 6159185) B6159185
theorem B5842867 : Blo 1823613 5842867 := bstep (se 1 (by rfl) ⟨4382150, by rfl⟩ : syracuseStep 5842867 = 8764301) B8764301
theorem B4106177 : Blo 1823613 4106177 := bstep (se 2 (by rfl) ⟨1539816, by rfl⟩ : syracuseStep 4106177 = 3079633) B3079633
theorem B2738123 : Blo 1823613 2738123 := bstep (se 1 (by rfl) ⟨2053592, by rfl⟩ : syracuseStep 2738123 = 4107185) B4107185
theorem B2738135 : Blo 1823613 2738135 := bstep (se 1 (by rfl) ⟨2053601, by rfl⟩ : syracuseStep 2738135 = 4107203) B4107203
theorem B18728921 : Blo 1823613 18728921 := bstep (se 2 (by rfl) ⟨7023345, by rfl⟩ : syracuseStep 18728921 = 14046691) B14046691
theorem B2738201 : Blo 1823613 2738201 := bstep (se 2 (by rfl) ⟨1026825, by rfl⟩ : syracuseStep 2738201 = 2053651) B2053651
theorem B2738315 : Blo 1823613 2738315 := bstep (se 1 (by rfl) ⟨2053736, by rfl⟩ : syracuseStep 2738315 = 4107473) B4107473
theorem B4679831 : Blo 1823613 4679831 := bstep (se 1 (by rfl) ⟨3509873, by rfl⟩ : syracuseStep 4679831 = 7019747) B7019747
theorem B2738327 : Blo 1823613 2738327 := bstep (se 1 (by rfl) ⟨2053745, by rfl⟩ : syracuseStep 2738327 = 4107491) B4107491
theorem B4106393 : Blo 1823613 4106393 := bstep (se 2 (by rfl) ⟨1539897, by rfl⟩ : syracuseStep 4106393 = 3079795) B3079795
theorem B6924467 : Blo 1823613 6924467 := bstep (se 1 (by rfl) ⟨5193350, by rfl⟩ : syracuseStep 6924467 = 10386701) B10386701
theorem B5621939 : Blo 1823613 5621939 := bstep (se 1 (by rfl) ⟨4216454, by rfl⟩ : syracuseStep 5621939 = 8432909) B8432909
theorem B2738393 : Blo 1823613 2738393 := bstep (se 2 (by rfl) ⟨1026897, by rfl⟩ : syracuseStep 2738393 = 2053795) B2053795
theorem B4106483 : Blo 1823613 4106483 := bstep (se 1 (by rfl) ⟨3079862, by rfl⟩ : syracuseStep 4106483 = 6159725) B6159725
theorem B4106519 : Blo 1823613 4106519 := bstep (se 1 (by rfl) ⟨3079889, by rfl⟩ : syracuseStep 4106519 = 6159779) B6159779
theorem B13158701 : Blo 1823613 13158701 := bstep (se 3 (by rfl) ⟨2467256, by rfl⟩ : syracuseStep 13158701 = 4934513) B4934513
theorem B14051677 : Blo 1823613 14051677 := bstep (se 3 (by rfl) ⟨2634689, by rfl⟩ : syracuseStep 14051677 = 5269379) B5269379
theorem B4106699 : Blo 1823613 4106699 := bstep (se 1 (by rfl) ⟨3080024, by rfl⟩ : syracuseStep 4106699 = 6160049) B6160049
theorem B4934105 : Blo 1823613 4934105 := bstep (se 2 (by rfl) ⟨1850289, by rfl⟩ : syracuseStep 4934105 = 3700579) B3700579
theorem B4106753 : Blo 1823613 4106753 := bstep (se 2 (by rfl) ⟨1540032, by rfl⟩ : syracuseStep 4106753 = 3080065) B3080065
theorem B14052017 : Blo 1823613 14052017 := bstep (se 2 (by rfl) ⟨5269506, by rfl⟩ : syracuseStep 14052017 = 10539013) B10539013
theorem B4106969 : Blo 1823613 4106969 := bstep (se 2 (by rfl) ⟨1540113, by rfl⟩ : syracuseStep 4106969 = 3080227) B3080227
theorem B6154973 : Blo 1823613 6154973 := bstep (se 3 (by rfl) ⟨1154057, by rfl⟩ : syracuseStep 6154973 = 2308115) B2308115
theorem B7498547 : Blo 1823613 7498547 := bstep (se 1 (by rfl) ⟨5623910, by rfl⟩ : syracuseStep 7498547 = 11247821) B11247821
theorem B4107059 : Blo 1823613 4107059 := bstep (se 1 (by rfl) ⟨3080294, by rfl⟩ : syracuseStep 4107059 = 6160589) B6160589
theorem B6925121 : Blo 1823613 6925121 := bstep (se 2 (by rfl) ⟨2596920, by rfl⟩ : syracuseStep 6925121 = 5193841) B5193841
theorem B170797889 : Blo 1823613 170797889 := bstep (se 2 (by rfl) ⟨64049208, by rfl⟩ : syracuseStep 170797889 = 128098417) B128098417
theorem B4107095 : Blo 1823613 4107095 := bstep (se 1 (by rfl) ⟨3080321, by rfl⟩ : syracuseStep 4107095 = 6160643) B6160643
theorem B5843801 : Blo 1823613 5843801 := bstep (se 2 (by rfl) ⟨2191425, by rfl⟩ : syracuseStep 5843801 = 4382851) B4382851
theorem B4107275 : Blo 1823613 4107275 := bstep (se 1 (by rfl) ⟨3080456, by rfl⟩ : syracuseStep 4107275 = 6160913) B6160913
theorem B4107329 : Blo 1823613 4107329 := bstep (se 2 (by rfl) ⟨1540248, by rfl⟩ : syracuseStep 4107329 = 3080497) B3080497
theorem B10390801 : Blo 1823613 10390801 := bstep (se 2 (by rfl) ⟨3896550, by rfl⟩ : syracuseStep 10390801 = 7793101) B7793101
theorem B3288343 : Blo 1823613 3288343 := bstep (se 1 (by rfl) ⟨2466257, by rfl⟩ : syracuseStep 3288343 = 4932515) B4932515
theorem B4107545 : Blo 1823613 4107545 := bstep (se 2 (by rfl) ⟨1540329, by rfl⟩ : syracuseStep 4107545 = 3080659) B3080659
theorem B7023917 : Blo 1823613 7023917 := bstep (se 3 (by rfl) ⟨1316984, by rfl⟩ : syracuseStep 7023917 = 2633969) B2633969
theorem B23391605 : Blo 1823613 23391605 := bstep (se 5 (by rfl) ⟨1096481, by rfl⟩ : syracuseStep 23391605 = 2192963) B2192963
theorem B20786705 : Blo 1823613 20786705 := bstep (se 2 (by rfl) ⟨7795014, by rfl⟩ : syracuseStep 20786705 = 15590029) B15590029
theorem B5844545 : Blo 1823613 5844545 := bstep (se 2 (by rfl) ⟨2191704, by rfl⟩ : syracuseStep 5844545 = 4383409) B4383409
theorem B7499339 : Blo 1823613 7499339 := bstep (se 1 (by rfl) ⟨5624504, by rfl⟩ : syracuseStep 7499339 = 11249009) B11249009
theorem B12660299 : Blo 1823613 12660299 := bstep (se 1 (by rfl) ⟨9495224, by rfl⟩ : syracuseStep 12660299 = 18990449) B18990449
theorem B2051671 : Blo 1823613 2051671 := bstep (se 1 (by rfl) ⟨1538753, by rfl⟩ : syracuseStep 2051671 = 3077507) B3077507
theorem B3698291 : Blo 1823613 3698291 := bstep (se 1 (by rfl) ⟨2773718, by rfl⟩ : syracuseStep 3698291 = 5547437) B5547437
theorem B5549771 : Blo 1823613 5549771 := bstep (se 1 (by rfl) ⟨4162328, by rfl⟩ : syracuseStep 5549771 = 8324657) B8324657
theorem B2051851 : Blo 1823613 2051851 := bstep (se 1 (by rfl) ⟨1538888, by rfl⟩ : syracuseStep 2051851 = 3077777) B3077777
theorem B6156107 : Blo 1823613 6156107 := bstep (se 1 (by rfl) ⟨4617080, by rfl⟩ : syracuseStep 6156107 = 9234161) B9234161
theorem B5001049 : Blo 1823613 5001049 := bstep (se 2 (by rfl) ⟨1875393, by rfl⟩ : syracuseStep 5001049 = 3750787) B3750787
theorem B6573917 : Blo 1823613 6573917 := bstep (se 3 (by rfl) ⟨1232609, by rfl⟩ : syracuseStep 6573917 = 2465219) B2465219
theorem B2051959 : Blo 1823613 2051959 := bstep (se 1 (by rfl) ⟨1538969, by rfl⟩ : syracuseStep 2051959 = 3077939) B3077939
theorem B13152131 : Blo 1823613 13152131 := bstep (se 1 (by rfl) ⟨9864098, by rfl⟩ : syracuseStep 13152131 = 19728197) B19728197
theorem B7794605 : Blo 1823613 7794605 := bstep (se 3 (by rfl) ⟨1461488, by rfl⟩ : syracuseStep 7794605 = 2922977) B2922977
theorem B4616129 : Blo 1823613 4616129 := bstep (se 2 (by rfl) ⟨1731048, by rfl⟩ : syracuseStep 4616129 = 3462097) B3462097
theorem B6328343 : Blo 1823613 6328343 := bstep (se 1 (by rfl) ⟨4746257, by rfl⟩ : syracuseStep 6328343 = 9492515) B9492515
theorem B3698713 : Blo 1823613 3698713 := bstep (se 2 (by rfl) ⟨1387017, by rfl⟩ : syracuseStep 3698713 = 2774035) B2774035
theorem B2052139 : Blo 1823613 2052139 := bstep (se 1 (by rfl) ⟨1539104, by rfl⟩ : syracuseStep 2052139 = 3078209) B3078209
theorem B6926381 : Blo 1823613 6926381 := bstep (se 3 (by rfl) ⟨1298696, by rfl⟩ : syracuseStep 6926381 = 2597393) B2597393
theorem B6926411 : Blo 1823613 6926411 := bstep (se 1 (by rfl) ⟨5194808, by rfl⟩ : syracuseStep 6926411 = 10389617) B10389617
theorem B6156377 : Blo 1823613 6156377 := bstep (se 2 (by rfl) ⟨2308641, by rfl⟩ : syracuseStep 6156377 = 4617283) B4617283
theorem B2961559 : Blo 1823613 2961559 := bstep (se 1 (by rfl) ⟨2221169, by rfl⟩ : syracuseStep 2961559 = 4442339) B4442339
theorem B23376023 : Blo 1823613 23376023 := bstep (se 1 (by rfl) ⟨17532017, by rfl⟩ : syracuseStep 23376023 = 35064035) B35064035
theorem B2052247 : Blo 1823613 2052247 := bstep (se 1 (by rfl) ⟨1539185, by rfl⟩ : syracuseStep 2052247 = 3078371) B3078371
theorem B2371799 : Blo 1823613 2371799 := bstep (se 1 (by rfl) ⟨1778849, by rfl⟩ : syracuseStep 2371799 = 3557699) B3557699
theorem B7794947 : Blo 1823613 7794947 := bstep (se 1 (by rfl) ⟨5846210, by rfl⟩ : syracuseStep 7794947 = 11692421) B11692421
theorem B26317061 : Blo 1823613 26317061 := bstep (se 4 (by rfl) ⟨2467224, by rfl⟩ : syracuseStep 26317061 = 4934449) B4934449
theorem B9236753 : Blo 1823613 9236753 := bstep (se 2 (by rfl) ⟨3463782, by rfl⟩ : syracuseStep 9236753 = 6927565) B6927565
theorem B2052427 : Blo 1823613 2052427 := bstep (se 1 (by rfl) ⟨1539320, by rfl⟩ : syracuseStep 2052427 = 3078641) B3078641
theorem B9236915 : Blo 1823613 9236915 := bstep (se 1 (by rfl) ⟨6927686, by rfl⟩ : syracuseStep 9236915 = 13855373) B13855373
theorem B2052535 : Blo 1823613 2052535 := bstep (se 1 (by rfl) ⟨1539401, by rfl⟩ : syracuseStep 2052535 = 3078803) B3078803
theorem B5845441 : Blo 1823613 5845441 := bstep (se 2 (by rfl) ⟨2192040, by rfl⟩ : syracuseStep 5845441 = 4384081) B4384081
theorem B22196753 : Blo 1823613 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B3699265 : Blo 1823613 3699265 := bstep (se 2 (by rfl) ⟨1387224, by rfl⟩ : syracuseStep 3699265 = 2774449) B2774449
theorem B2052715 : Blo 1823613 2052715 := bstep (se 1 (by rfl) ⟨1539536, by rfl⟩ : syracuseStep 2052715 = 3079073) B3079073
theorem B3510935 : Blo 1823613 3510935 := bstep (se 1 (by rfl) ⟨2633201, by rfl⟩ : syracuseStep 3510935 = 5266403) B5266403
theorem B2052823 : Blo 1823613 2052823 := bstep (se 1 (by rfl) ⟨1539617, by rfl⟩ : syracuseStep 2052823 = 3079235) B3079235
theorem B6927065 : Blo 1823613 6927065 := bstep (se 2 (by rfl) ⟨2597649, by rfl⟩ : syracuseStep 6927065 = 5195299) B5195299
theorem B6157079 : Blo 1823613 6157079 := bstep (se 1 (by rfl) ⟨4617809, by rfl⟩ : syracuseStep 6157079 = 9235619) B9235619
theorem B3207959 : Blo 1823613 3207959 := bstep (se 1 (by rfl) ⟨2405969, by rfl⟩ : syracuseStep 3207959 = 4811939) B4811939
theorem B5198681 : Blo 1823613 5198681 := bstep (se 2 (by rfl) ⟨1949505, by rfl⟩ : syracuseStep 5198681 = 3899011) B3899011
theorem B1823627 : Blo 1823613 1823627 := bstep (se 1 (by rfl) ⟨1367720, by rfl⟩ : syracuseStep 1823627 = 2735441) B2735441
theorem B2053003 : Blo 1823613 2053003 := bstep (se 1 (by rfl) ⟨1539752, by rfl⟩ : syracuseStep 2053003 = 3079505) B3079505
theorem B1823639 : Blo 1823613 1823639 := bstep (se 1 (by rfl) ⟨1367729, by rfl⟩ : syracuseStep 1823639 = 2735459) B2735459
theorem B1823659 : Blo 1823613 1823659 := bstep (se 1 (by rfl) ⟨1367744, by rfl⟩ : syracuseStep 1823659 = 2735489) B2735489
theorem B1823671 : Blo 1823613 1823671 := bstep (se 1 (by rfl) ⟨1367753, by rfl⟩ : syracuseStep 1823671 = 2735507) B2735507
theorem B1823691 : Blo 1823613 1823691 := bstep (se 1 (by rfl) ⟨1367768, by rfl⟩ : syracuseStep 1823691 = 2735537) B2735537
theorem B1823703 : Blo 1823613 1823703 := bstep (se 1 (by rfl) ⟨1367777, by rfl⟩ : syracuseStep 1823703 = 2735555) B2735555
theorem B1823723 : Blo 1823613 1823723 := bstep (se 1 (by rfl) ⟨1367792, by rfl⟩ : syracuseStep 1823723 = 2735585) B2735585
theorem B1823735 : Blo 1823613 1823735 := bstep (se 1 (by rfl) ⟨1367801, by rfl⟩ : syracuseStep 1823735 = 2735603) B2735603
theorem B2053111 : Blo 1823613 2053111 := bstep (se 1 (by rfl) ⟨1539833, by rfl⟩ : syracuseStep 2053111 = 3079667) B3079667
theorem B1823755 : Blo 1823613 1823755 := bstep (se 1 (by rfl) ⟨1367816, by rfl⟩ : syracuseStep 1823755 = 2735633) B2735633
theorem B1823767 : Blo 1823613 1823767 := bstep (se 1 (by rfl) ⟨1367825, by rfl⟩ : syracuseStep 1823767 = 2735651) B2735651
theorem B6927383 : Blo 1823613 6927383 := bstep (se 1 (by rfl) ⟨5195537, by rfl⟩ : syracuseStep 6927383 = 10391075) B10391075
theorem B1823787 : Blo 1823613 1823787 := bstep (se 1 (by rfl) ⟨1367840, by rfl⟩ : syracuseStep 1823787 = 2735681) B2735681
theorem B1823799 : Blo 1823613 1823799 := bstep (se 1 (by rfl) ⟨1367849, by rfl⟩ : syracuseStep 1823799 = 2735699) B2735699
theorem B1823819 : Blo 1823613 1823819 := bstep (se 1 (by rfl) ⟨1367864, by rfl⟩ : syracuseStep 1823819 = 2735729) B2735729
theorem B1823831 : Blo 1823613 1823831 := bstep (se 1 (by rfl) ⟨1367873, by rfl⟩ : syracuseStep 1823831 = 2735747) B2735747
theorem B1823851 : Blo 1823613 1823851 := bstep (se 1 (by rfl) ⟨1367888, by rfl⟩ : syracuseStep 1823851 = 2735777) B2735777
theorem B1823863 : Blo 1823613 1823863 := bstep (se 1 (by rfl) ⟨1367897, by rfl⟩ : syracuseStep 1823863 = 2735795) B2735795
theorem B1823883 : Blo 1823613 1823883 := bstep (se 1 (by rfl) ⟨1367912, by rfl⟩ : syracuseStep 1823883 = 2735825) B2735825
theorem B1823895 : Blo 1823613 1823895 := bstep (se 1 (by rfl) ⟨1367921, by rfl⟩ : syracuseStep 1823895 = 2735843) B2735843
theorem B1823915 : Blo 1823613 1823915 := bstep (se 1 (by rfl) ⟨1367936, by rfl⟩ : syracuseStep 1823915 = 2735873) B2735873
theorem B2053291 : Blo 1823613 2053291 := bstep (se 1 (by rfl) ⟨1539968, by rfl⟩ : syracuseStep 2053291 = 3079937) B3079937
theorem B4617395 : Blo 1823613 4617395 := bstep (se 1 (by rfl) ⟨3463046, by rfl⟩ : syracuseStep 4617395 = 6926093) B6926093
theorem B1823927 : Blo 1823613 1823927 := bstep (se 1 (by rfl) ⟨1367945, by rfl⟩ : syracuseStep 1823927 = 2735891) B2735891
theorem B1823947 : Blo 1823613 1823947 := bstep (se 1 (by rfl) ⟨1367960, by rfl⟩ : syracuseStep 1823947 = 2735921) B2735921
theorem B1823959 : Blo 1823613 1823959 := bstep (se 1 (by rfl) ⟨1367969, by rfl⟩ : syracuseStep 1823959 = 2735939) B2735939
theorem B1823979 : Blo 1823613 1823979 := bstep (se 1 (by rfl) ⟨1367984, by rfl⟩ : syracuseStep 1823979 = 2735969) B2735969
theorem B1823991 : Blo 1823613 1823991 := bstep (se 1 (by rfl) ⟨1367993, by rfl⟩ : syracuseStep 1823991 = 2735987) B2735987
theorem B3462401 : Blo 1823613 3462401 := bstep (se 2 (by rfl) ⟨1298400, by rfl⟩ : syracuseStep 3462401 = 2596801) B2596801
theorem B1824011 : Blo 1823613 1824011 := bstep (se 1 (by rfl) ⟨1368008, by rfl⟩ : syracuseStep 1824011 = 2736017) B2736017
theorem B3077399 : Blo 1823613 3077399 := bstep (se 1 (by rfl) ⟨2308049, by rfl⟩ : syracuseStep 3077399 = 4616099) B4616099
theorem B1824023 : Blo 1823613 1824023 := bstep (se 1 (by rfl) ⟨1368017, by rfl⟩ : syracuseStep 1824023 = 2736035) B2736035
theorem B2053399 : Blo 1823613 2053399 := bstep (se 1 (by rfl) ⟨1540049, by rfl⟩ : syracuseStep 2053399 = 3080099) B3080099
theorem B1824043 : Blo 1823613 1824043 := bstep (se 1 (by rfl) ⟨1368032, by rfl⟩ : syracuseStep 1824043 = 2736065) B2736065
theorem B6157619 : Blo 1823613 6157619 := bstep (se 1 (by rfl) ⟨4618214, by rfl⟩ : syracuseStep 6157619 = 9236429) B9236429
theorem B1824055 : Blo 1823613 1824055 := bstep (se 1 (by rfl) ⟨1368041, by rfl⟩ : syracuseStep 1824055 = 2736083) B2736083
theorem B1824075 : Blo 1823613 1824075 := bstep (se 1 (by rfl) ⟨1368056, by rfl⟩ : syracuseStep 1824075 = 2736113) B2736113
theorem B1824087 : Blo 1823613 1824087 := bstep (se 1 (by rfl) ⟨1368065, by rfl⟩ : syracuseStep 1824087 = 2736131) B2736131
theorem B1824107 : Blo 1823613 1824107 := bstep (se 1 (by rfl) ⟨1368080, by rfl⟩ : syracuseStep 1824107 = 2736161) B2736161
theorem B1824119 : Blo 1823613 1824119 := bstep (se 1 (by rfl) ⟨1368089, by rfl⟩ : syracuseStep 1824119 = 2736179) B2736179
theorem B1824139 : Blo 1823613 1824139 := bstep (se 1 (by rfl) ⟨1368104, by rfl⟩ : syracuseStep 1824139 = 2736209) B2736209
theorem B3077527 : Blo 1823613 3077527 := bstep (se 1 (by rfl) ⟨2308145, by rfl⟩ : syracuseStep 3077527 = 4616291) B4616291
theorem B1824151 : Blo 1823613 1824151 := bstep (se 1 (by rfl) ⟨1368113, by rfl⟩ : syracuseStep 1824151 = 2736227) B2736227
theorem B1824171 : Blo 1823613 1824171 := bstep (se 1 (by rfl) ⟨1368128, by rfl⟩ : syracuseStep 1824171 = 2736257) B2736257
theorem B12490163 : Blo 1823613 12490163 := bstep (se 1 (by rfl) ⟨9367622, by rfl⟩ : syracuseStep 12490163 = 18735245) B18735245
theorem B1824183 : Blo 1823613 1824183 := bstep (se 1 (by rfl) ⟨1368137, by rfl⟩ : syracuseStep 1824183 = 2736275) B2736275
theorem B1824203 : Blo 1823613 1824203 := bstep (se 1 (by rfl) ⟨1368152, by rfl⟩ : syracuseStep 1824203 = 2736305) B2736305
theorem B2053579 : Blo 1823613 2053579 := bstep (se 1 (by rfl) ⟨1540184, by rfl⟩ : syracuseStep 2053579 = 3080369) B3080369
theorem B1824215 : Blo 1823613 1824215 := bstep (se 1 (by rfl) ⟨1368161, by rfl⟩ : syracuseStep 1824215 = 2736323) B2736323
theorem B1824235 : Blo 1823613 1824235 := bstep (se 1 (by rfl) ⟨1368176, by rfl⟩ : syracuseStep 1824235 = 2736353) B2736353
theorem B1824247 : Blo 1823613 1824247 := bstep (se 1 (by rfl) ⟨1368185, by rfl⟩ : syracuseStep 1824247 = 2736371) B2736371
theorem B1824267 : Blo 1823613 1824267 := bstep (se 1 (by rfl) ⟨1368200, by rfl⟩ : syracuseStep 1824267 = 2736401) B2736401
theorem B1824279 : Blo 1823613 1824279 := bstep (se 1 (by rfl) ⟨1368209, by rfl⟩ : syracuseStep 1824279 = 2736419) B2736419
theorem B1824299 : Blo 1823613 1824299 := bstep (se 1 (by rfl) ⟨1368224, by rfl⟩ : syracuseStep 1824299 = 2736449) B2736449
theorem B1824311 : Blo 1823613 1824311 := bstep (se 1 (by rfl) ⟨1368233, by rfl⟩ : syracuseStep 1824311 = 2736467) B2736467
theorem B2053687 : Blo 1823613 2053687 := bstep (se 1 (by rfl) ⟨1540265, by rfl⟩ : syracuseStep 2053687 = 3080531) B3080531
theorem B6157889 : Blo 1823613 6157889 := bstep (se 2 (by rfl) ⟨2309208, by rfl⟩ : syracuseStep 6157889 = 4618417) B4618417
theorem B1824331 : Blo 1823613 1824331 := bstep (se 1 (by rfl) ⟨1368248, by rfl⟩ : syracuseStep 1824331 = 2736497) B2736497
theorem B3462743 : Blo 1823613 3462743 := bstep (se 1 (by rfl) ⟨2597057, by rfl⟩ : syracuseStep 3462743 = 5194115) B5194115
theorem B1824343 : Blo 1823613 1824343 := bstep (se 1 (by rfl) ⟨1368257, by rfl⟩ : syracuseStep 1824343 = 2736515) B2736515
theorem B1824363 : Blo 1823613 1824363 := bstep (se 1 (by rfl) ⟨1368272, by rfl⟩ : syracuseStep 1824363 = 2736545) B2736545
theorem B1824375 : Blo 1823613 1824375 := bstep (se 1 (by rfl) ⟨1368281, by rfl⟩ : syracuseStep 1824375 = 2736563) B2736563
theorem B1824395 : Blo 1823613 1824395 := bstep (se 1 (by rfl) ⟨1368296, by rfl⟩ : syracuseStep 1824395 = 2736593) B2736593
theorem B1824407 : Blo 1823613 1824407 := bstep (se 1 (by rfl) ⟨1368305, by rfl⟩ : syracuseStep 1824407 = 2736611) B2736611
theorem B1824427 : Blo 1823613 1824427 := bstep (se 1 (by rfl) ⟨1368320, by rfl⟩ : syracuseStep 1824427 = 2736641) B2736641
theorem B6928051 : Blo 1823613 6928051 := bstep (se 1 (by rfl) ⟨5196038, by rfl⟩ : syracuseStep 6928051 = 10392077) B10392077
theorem B1824439 : Blo 1823613 1824439 := bstep (se 1 (by rfl) ⟨1368329, by rfl⟩ : syracuseStep 1824439 = 2736659) B2736659
theorem B4617931 : Blo 1823613 4617931 := bstep (se 1 (by rfl) ⟨3463448, by rfl⟩ : syracuseStep 4617931 = 6926897) B6926897
theorem B1824459 : Blo 1823613 1824459 := bstep (se 1 (by rfl) ⟨1368344, by rfl⟩ : syracuseStep 1824459 = 2736689) B2736689
theorem B1824471 : Blo 1823613 1824471 := bstep (se 1 (by rfl) ⟨1368353, by rfl⟩ : syracuseStep 1824471 = 2736707) B2736707
theorem B3897047 : Blo 1823613 3897047 := bstep (se 1 (by rfl) ⟨2922785, by rfl⟩ : syracuseStep 3897047 = 5845571) B5845571
theorem B1824491 : Blo 1823613 1824491 := bstep (se 1 (by rfl) ⟨1368368, by rfl⟩ : syracuseStep 1824491 = 2736737) B2736737
theorem B1824503 : Blo 1823613 1824503 := bstep (se 1 (by rfl) ⟨1368377, by rfl⟩ : syracuseStep 1824503 = 2736755) B2736755
theorem B1824523 : Blo 1823613 1824523 := bstep (se 1 (by rfl) ⟨1368392, by rfl⟩ : syracuseStep 1824523 = 2736785) B2736785
theorem B1824535 : Blo 1823613 1824535 := bstep (se 1 (by rfl) ⟨1368401, by rfl⟩ : syracuseStep 1824535 = 2736803) B2736803
theorem B3512089 : Blo 1823613 3512089 := bstep (se 2 (by rfl) ⟨1317033, by rfl⟩ : syracuseStep 3512089 = 2634067) B2634067
theorem B1824555 : Blo 1823613 1824555 := bstep (se 1 (by rfl) ⟨1368416, by rfl⟩ : syracuseStep 1824555 = 2736833) B2736833
theorem B1824567 : Blo 1823613 1824567 := bstep (se 1 (by rfl) ⟨1368425, by rfl⟩ : syracuseStep 1824567 = 2736851) B2736851
theorem B47404865 : Blo 1823613 47404865 := bstep (se 2 (by rfl) ⟨17776824, by rfl⟩ : syracuseStep 47404865 = 35553649) B35553649
theorem B1824587 : Blo 1823613 1824587 := bstep (se 1 (by rfl) ⟨1368440, by rfl⟩ : syracuseStep 1824587 = 2736881) B2736881
theorem B1824599 : Blo 1823613 1824599 := bstep (se 1 (by rfl) ⟨1368449, by rfl⟩ : syracuseStep 1824599 = 2736899) B2736899
theorem B4618073 : Blo 1823613 4618073 := bstep (se 2 (by rfl) ⟨1731777, by rfl⟩ : syracuseStep 4618073 = 3463555) B3463555
theorem B1824619 : Blo 1823613 1824619 := bstep (se 1 (by rfl) ⟨1368464, by rfl⟩ : syracuseStep 1824619 = 2736929) B2736929
theorem B1824631 : Blo 1823613 1824631 := bstep (se 1 (by rfl) ⟨1368473, by rfl⟩ : syracuseStep 1824631 = 2736947) B2736947
theorem B1824651 : Blo 1823613 1824651 := bstep (se 1 (by rfl) ⟨1368488, by rfl⟩ : syracuseStep 1824651 = 2736977) B2736977
theorem B3897227 : Blo 1823613 3897227 := bstep (se 1 (by rfl) ⟨2922920, by rfl⟩ : syracuseStep 3897227 = 5845841) B5845841
theorem B1824663 : Blo 1823613 1824663 := bstep (se 1 (by rfl) ⟨1368497, by rfl⟩ : syracuseStep 1824663 = 2736995) B2736995
theorem B1824683 : Blo 1823613 1824683 := bstep (se 1 (by rfl) ⟨1368512, by rfl⟩ : syracuseStep 1824683 = 2737025) B2737025
theorem B1947575 : Blo 1823613 1947575 := bstep (se 1 (by rfl) ⟨1460681, by rfl⟩ : syracuseStep 1947575 = 2921363) B2921363
theorem B1824695 : Blo 1823613 1824695 := bstep (se 1 (by rfl) ⟨1368521, by rfl⟩ : syracuseStep 1824695 = 2737043) B2737043
theorem B1824715 : Blo 1823613 1824715 := bstep (se 1 (by rfl) ⟨1368536, by rfl⟩ : syracuseStep 1824715 = 2737073) B2737073
theorem B1824727 : Blo 1823613 1824727 := bstep (se 1 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 1824727 = 2737091) B2737091
theorem B5847005 : Blo 1823613 5847005 := bstep (se 3 (by rfl) ⟨1096313, by rfl⟩ : syracuseStep 5847005 = 2192627) B2192627
theorem B1824747 : Blo 1823613 1824747 := bstep (se 1 (by rfl) ⟨1368560, by rfl⟩ : syracuseStep 1824747 = 2737121) B2737121
theorem B4159475 : Blo 1823613 4159475 := bstep (se 1 (by rfl) ⟨3119606, by rfl⟩ : syracuseStep 4159475 = 6239213) B6239213
theorem B1824759 : Blo 1823613 1824759 := bstep (se 1 (by rfl) ⟨1368569, by rfl⟩ : syracuseStep 1824759 = 2737139) B2737139
theorem B3078155 : Blo 1823613 3078155 := bstep (se 1 (by rfl) ⟨2308616, by rfl⟩ : syracuseStep 3078155 = 4617233) B4617233
theorem B1824779 : Blo 1823613 1824779 := bstep (se 1 (by rfl) ⟨1368584, by rfl⟩ : syracuseStep 1824779 = 2737169) B2737169
theorem B1824791 : Blo 1823613 1824791 := bstep (se 1 (by rfl) ⟨1368593, by rfl⟩ : syracuseStep 1824791 = 2737187) B2737187
theorem B1824811 : Blo 1823613 1824811 := bstep (se 1 (by rfl) ⟨1368608, by rfl⟩ : syracuseStep 1824811 = 2737217) B2737217
theorem B1824823 : Blo 1823613 1824823 := bstep (se 1 (by rfl) ⟨1368617, by rfl⟩ : syracuseStep 1824823 = 2737235) B2737235
theorem B2308171 : Blo 1823613 2308171 := bstep (se 1 (by rfl) ⟨1731128, by rfl⟩ : syracuseStep 2308171 = 3462257) B3462257
theorem B1824843 : Blo 1823613 1824843 := bstep (se 1 (by rfl) ⟨1368632, by rfl⟩ : syracuseStep 1824843 = 2737265) B2737265
theorem B1824855 : Blo 1823613 1824855 := bstep (se 1 (by rfl) ⟨1368641, by rfl⟩ : syracuseStep 1824855 = 2737283) B2737283
theorem B6158429 : Blo 1823613 6158429 := bstep (se 3 (by rfl) ⟨1154705, by rfl⟩ : syracuseStep 6158429 = 2309411) B2309411
theorem B1824875 : Blo 1823613 1824875 := bstep (se 1 (by rfl) ⟨1368656, by rfl⟩ : syracuseStep 1824875 = 2737313) B2737313
theorem B1824887 : Blo 1823613 1824887 := bstep (se 1 (by rfl) ⟨1368665, by rfl⟩ : syracuseStep 1824887 = 2737331) B2737331
theorem B3078283 : Blo 1823613 3078283 := bstep (se 1 (by rfl) ⟨2308712, by rfl⟩ : syracuseStep 3078283 = 4617425) B4617425
theorem B1824907 : Blo 1823613 1824907 := bstep (se 1 (by rfl) ⟨1368680, by rfl⟩ : syracuseStep 1824907 = 2737361) B2737361
theorem B1824919 : Blo 1823613 1824919 := bstep (se 1 (by rfl) ⟨1368689, by rfl⟩ : syracuseStep 1824919 = 2737379) B2737379
theorem B1824939 : Blo 1823613 1824939 := bstep (se 1 (by rfl) ⟨1368704, by rfl⟩ : syracuseStep 1824939 = 2737409) B2737409
theorem B4159667 : Blo 1823613 4159667 := bstep (se 1 (by rfl) ⟨3119750, by rfl⟩ : syracuseStep 4159667 = 6239501) B6239501
theorem B1824951 : Blo 1823613 1824951 := bstep (se 1 (by rfl) ⟨1368713, by rfl⟩ : syracuseStep 1824951 = 2737427) B2737427
theorem B1824971 : Blo 1823613 1824971 := bstep (se 1 (by rfl) ⟨1368728, by rfl⟩ : syracuseStep 1824971 = 2737457) B2737457
theorem B1824983 : Blo 1823613 1824983 := bstep (se 1 (by rfl) ⟨1368737, by rfl⟩ : syracuseStep 1824983 = 2737475) B2737475
theorem B1825003 : Blo 1823613 1825003 := bstep (se 1 (by rfl) ⟨1368752, by rfl⟩ : syracuseStep 1825003 = 2737505) B2737505
theorem B3463411 : Blo 1823613 3463411 := bstep (se 1 (by rfl) ⟨2597558, by rfl⟩ : syracuseStep 3463411 = 5195117) B5195117
theorem B1825015 : Blo 1823613 1825015 := bstep (se 1 (by rfl) ⟨1368761, by rfl⟩ : syracuseStep 1825015 = 2737523) B2737523
theorem B1825035 : Blo 1823613 1825035 := bstep (se 1 (by rfl) ⟨1368776, by rfl⟩ : syracuseStep 1825035 = 2737553) B2737553
theorem B1825047 : Blo 1823613 1825047 := bstep (se 1 (by rfl) ⟨1368785, by rfl⟩ : syracuseStep 1825047 = 2737571) B2737571
theorem B3078425 : Blo 1823613 3078425 := bstep (se 2 (by rfl) ⟨1154409, by rfl⟩ : syracuseStep 3078425 = 2308819) B2308819
theorem B1825067 : Blo 1823613 1825067 := bstep (se 1 (by rfl) ⟨1368800, by rfl⟩ : syracuseStep 1825067 = 2737601) B2737601
theorem B1825079 : Blo 1823613 1825079 := bstep (se 1 (by rfl) ⟨1368809, by rfl⟩ : syracuseStep 1825079 = 2737619) B2737619
theorem B9238859 : Blo 1823613 9238859 := bstep (se 1 (by rfl) ⟨6929144, by rfl⟩ : syracuseStep 9238859 = 13858289) B13858289
theorem B1825099 : Blo 1823613 1825099 := bstep (se 1 (by rfl) ⟨1368824, by rfl⟩ : syracuseStep 1825099 = 2737649) B2737649
theorem B2308439 : Blo 1823613 2308439 := bstep (se 1 (by rfl) ⟨1731329, by rfl⟩ : syracuseStep 2308439 = 3462659) B3462659
theorem B1825111 : Blo 1823613 1825111 := bstep (se 1 (by rfl) ⟨1368833, by rfl⟩ : syracuseStep 1825111 = 2737667) B2737667
theorem B1825131 : Blo 1823613 1825131 := bstep (se 1 (by rfl) ⟨1368848, by rfl⟩ : syracuseStep 1825131 = 2737697) B2737697
theorem B20789621 : Blo 1823613 20789621 := bstep (se 5 (by rfl) ⟨974513, by rfl⟩ : syracuseStep 20789621 = 1949027) B1949027
theorem B1825143 : Blo 1823613 1825143 := bstep (se 1 (by rfl) ⟨1368857, by rfl⟩ : syracuseStep 1825143 = 2737715) B2737715
theorem B1825163 : Blo 1823613 1825163 := bstep (se 1 (by rfl) ⟨1368872, by rfl⟩ : syracuseStep 1825163 = 2737745) B2737745
theorem B43276693 : Blo 1823613 43276693 := bstep (se 6 (by rfl) ⟨1014297, by rfl⟩ : syracuseStep 43276693 = 2028595) B2028595
theorem B1825175 : Blo 1823613 1825175 := bstep (se 1 (by rfl) ⟨1368881, by rfl⟩ : syracuseStep 1825175 = 2737763) B2737763
theorem B3078553 : Blo 1823613 3078553 := bstep (se 2 (by rfl) ⟨1154457, by rfl⟩ : syracuseStep 3078553 = 2308915) B2308915
theorem B1825195 : Blo 1823613 1825195 := bstep (se 1 (by rfl) ⟨1368896, by rfl⟩ : syracuseStep 1825195 = 2737793) B2737793
theorem B11098547 : Blo 1823613 11098547 := bstep (se 1 (by rfl) ⟨8323910, by rfl⟩ : syracuseStep 11098547 = 16647821) B16647821
theorem B1825207 : Blo 1823613 1825207 := bstep (se 1 (by rfl) ⟨1368905, by rfl⟩ : syracuseStep 1825207 = 2737811) B2737811
theorem B1825227 : Blo 1823613 1825227 := bstep (se 1 (by rfl) ⟨1368920, by rfl⟩ : syracuseStep 1825227 = 2737841) B2737841
theorem B1825239 : Blo 1823613 1825239 := bstep (se 1 (by rfl) ⟨1368929, by rfl⟩ : syracuseStep 1825239 = 2737859) B2737859
theorem B1849835 : Blo 1823613 1849835 := bstep (se 1 (by rfl) ⟨1387376, by rfl⟩ : syracuseStep 1849835 = 2774753) B2774753
theorem B1825259 : Blo 1823613 1825259 := bstep (se 1 (by rfl) ⟨1368944, by rfl⟩ : syracuseStep 1825259 = 2737889) B2737889
theorem B1825271 : Blo 1823613 1825271 := bstep (se 1 (by rfl) ⟨1368953, by rfl⟩ : syracuseStep 1825271 = 2737907) B2737907
theorem B1825291 : Blo 1823613 1825291 := bstep (se 1 (by rfl) ⟨1368968, by rfl⟩ : syracuseStep 1825291 = 2737937) B2737937
theorem B1825303 : Blo 1823613 1825303 := bstep (se 1 (by rfl) ⟨1368977, by rfl⟩ : syracuseStep 1825303 = 2737955) B2737955
theorem B1825323 : Blo 1823613 1825323 := bstep (se 1 (by rfl) ⟨1368992, by rfl⟩ : syracuseStep 1825323 = 2737985) B2737985
theorem B1825335 : Blo 1823613 1825335 := bstep (se 1 (by rfl) ⟨1369001, by rfl⟩ : syracuseStep 1825335 = 2738003) B2738003
theorem B1825355 : Blo 1823613 1825355 := bstep (se 1 (by rfl) ⟨1369016, by rfl⟩ : syracuseStep 1825355 = 2738033) B2738033
theorem B7797323 : Blo 1823613 7797323 := bstep (se 1 (by rfl) ⟨5847992, by rfl⟩ : syracuseStep 7797323 = 11695985) B11695985
theorem B1825367 : Blo 1823613 1825367 := bstep (se 1 (by rfl) ⟨1369025, by rfl⟩ : syracuseStep 1825367 = 2738051) B2738051
theorem B1825387 : Blo 1823613 1825387 := bstep (se 1 (by rfl) ⟨1369040, by rfl⟩ : syracuseStep 1825387 = 2738081) B2738081
theorem B1825399 : Blo 1823613 1825399 := bstep (se 1 (by rfl) ⟨1369049, by rfl⟩ : syracuseStep 1825399 = 2738099) B2738099
theorem B10394243 : Blo 1823613 10394243 := bstep (se 1 (by rfl) ⟨7795682, by rfl⟩ : syracuseStep 10394243 = 15591365) B15591365
theorem B1825419 : Blo 1823613 1825419 := bstep (se 1 (by rfl) ⟨1369064, by rfl⟩ : syracuseStep 1825419 = 2738129) B2738129
theorem B4618903 : Blo 1823613 4618903 := bstep (se 1 (by rfl) ⟨3464177, by rfl⟩ : syracuseStep 4618903 = 6928355) B6928355
theorem B1825431 : Blo 1823613 1825431 := bstep (se 1 (by rfl) ⟨1369073, by rfl⟩ : syracuseStep 1825431 = 2738147) B2738147
theorem B1825451 : Blo 1823613 1825451 := bstep (se 1 (by rfl) ⟨1369088, by rfl⟩ : syracuseStep 1825451 = 2738177) B2738177
theorem B3463859 : Blo 1823613 3463859 := bstep (se 1 (by rfl) ⟨2597894, by rfl⟩ : syracuseStep 3463859 = 5195789) B5195789
theorem B1825463 : Blo 1823613 1825463 := bstep (se 1 (by rfl) ⟨1369097, by rfl⟩ : syracuseStep 1825463 = 2738195) B2738195
theorem B1825483 : Blo 1823613 1825483 := bstep (se 1 (by rfl) ⟨1369112, by rfl⟩ : syracuseStep 1825483 = 2738225) B2738225
theorem B1825495 : Blo 1823613 1825495 := bstep (se 1 (by rfl) ⟨1369121, by rfl⟩ : syracuseStep 1825495 = 2738243) B2738243
theorem B3463897 : Blo 1823613 3463897 := bstep (se 2 (by rfl) ⟨1298961, by rfl⟩ : syracuseStep 3463897 = 2597923) B2597923
theorem B1825515 : Blo 1823613 1825515 := bstep (se 1 (by rfl) ⟨1369136, by rfl⟩ : syracuseStep 1825515 = 2738273) B2738273
theorem B1825527 : Blo 1823613 1825527 := bstep (se 1 (by rfl) ⟨1369145, by rfl⟩ : syracuseStep 1825527 = 2738291) B2738291
theorem B1825547 : Blo 1823613 1825547 := bstep (se 1 (by rfl) ⟨1369160, by rfl⟩ : syracuseStep 1825547 = 2738321) B2738321
theorem B1825559 : Blo 1823613 1825559 := bstep (se 1 (by rfl) ⟨1369169, by rfl⟩ : syracuseStep 1825559 = 2738339) B2738339
theorem B16644899 : Blo 1823613 16644899 := bstep (se 1 (by rfl) ⟨12483674, by rfl⟩ : syracuseStep 16644899 = 24967349) B24967349
theorem B1825579 : Blo 1823613 1825579 := bstep (se 1 (by rfl) ⟨1369184, by rfl⟩ : syracuseStep 1825579 = 2738369) B2738369
theorem B1850167 : Blo 1823613 1850167 := bstep (se 1 (by rfl) ⟨1387625, by rfl⟩ : syracuseStep 1850167 = 2775251) B2775251
theorem B1825591 : Blo 1823613 1825591 := bstep (se 1 (by rfl) ⟨1369193, by rfl⟩ : syracuseStep 1825591 = 2738387) B2738387
theorem B1825611 : Blo 1823613 1825611 := bstep (se 1 (by rfl) ⟨1369208, by rfl⟩ : syracuseStep 1825611 = 2738417) B2738417
theorem B13851485 : Blo 1823613 13851485 := bstep (se 3 (by rfl) ⟨2597153, by rfl⟩ : syracuseStep 13851485 = 5194307) B5194307
theorem B6929297 : Blo 1823613 6929297 := bstep (se 2 (by rfl) ⟨2598486, by rfl⟩ : syracuseStep 6929297 = 5196973) B5196973
theorem B3079127 : Blo 1823613 3079127 := bstep (se 1 (by rfl) ⟨2309345, by rfl⟩ : syracuseStep 3079127 = 4618691) B4618691
theorem B6241303 : Blo 1823613 6241303 := bstep (se 1 (by rfl) ⟨4680977, by rfl⟩ : syracuseStep 6241303 = 9361955) B9361955
theorem B2309143 : Blo 1823613 2309143 := bstep (se 1 (by rfl) ⟨1731857, by rfl⟩ : syracuseStep 2309143 = 3463715) B3463715
theorem B4103243 : Blo 1823613 4103243 := bstep (se 1 (by rfl) ⟨3077432, by rfl⟩ : syracuseStep 4103243 = 6154865) B6154865
theorem B4619339 : Blo 1823613 4619339 := bstep (se 1 (by rfl) ⟨3464504, by rfl⟩ : syracuseStep 4619339 = 6929009) B6929009
theorem B3079255 : Blo 1823613 3079255 := bstep (se 1 (by rfl) ⟨2309441, by rfl⟩ : syracuseStep 3079255 = 4618883) B4618883
theorem B4103297 : Blo 1823613 4103297 := bstep (se 2 (by rfl) ⟨1538736, by rfl⟩ : syracuseStep 4103297 = 3077473) B3077473
theorem B3464345 : Blo 1823613 3464345 := bstep (se 2 (by rfl) ⟨1299129, by rfl⟩ : syracuseStep 3464345 = 2598259) B2598259
theorem B6159563 : Blo 1823613 6159563 := bstep (se 1 (by rfl) ⟨4619672, by rfl⟩ : syracuseStep 6159563 = 9239345) B9239345
theorem B2735435 : Blo 1823613 2735435 := bstep (se 1 (by rfl) ⟨2051576, by rfl⟩ : syracuseStep 2735435 = 4103153) B4103153
theorem B2735447 : Blo 1823613 2735447 := bstep (se 1 (by rfl) ⟨2051585, by rfl⟩ : syracuseStep 2735447 = 4103171) B4103171
theorem B4103513 : Blo 1823613 4103513 := bstep (se 2 (by rfl) ⟨1538817, by rfl⟩ : syracuseStep 4103513 = 3077635) B3077635
theorem B7396697 : Blo 1823613 7396697 := bstep (se 2 (by rfl) ⟨2773761, by rfl⟩ : syracuseStep 7396697 = 5547523) B5547523
theorem B2735513 : Blo 1823613 2735513 := bstep (se 2 (by rfl) ⟨1025817, by rfl⟩ : syracuseStep 2735513 = 2051635) B2051635
theorem B4103603 : Blo 1823613 4103603 := bstep (se 1 (by rfl) ⟨3077702, by rfl⟩ : syracuseStep 4103603 = 6155405) B6155405
theorem B29588915 : Blo 1823613 29588915 := bstep (se 1 (by rfl) ⟨22191686, by rfl⟩ : syracuseStep 29588915 = 44383373) B44383373
theorem B4619713 : Blo 1823613 4619713 := bstep (se 2 (by rfl) ⟨1732392, by rfl⟩ : syracuseStep 4619713 = 3464785) B3464785
theorem B4103639 : Blo 1823613 4103639 := bstep (se 1 (by rfl) ⟨3077729, by rfl⟩ : syracuseStep 4103639 = 6155459) B6155459
theorem B6159833 : Blo 1823613 6159833 := bstep (se 2 (by rfl) ⟨2309937, by rfl⟩ : syracuseStep 6159833 = 4619875) B4619875
theorem B3898867 : Blo 1823613 3898867 := bstep (se 1 (by rfl) ⟨2924150, by rfl⟩ : syracuseStep 3898867 = 5848301) B5848301
theorem B2735627 : Blo 1823613 2735627 := bstep (se 1 (by rfl) ⟨2051720, by rfl⟩ : syracuseStep 2735627 = 4103441) B4103441
theorem B2735639 : Blo 1823613 2735639 := bstep (se 1 (by rfl) ⟨2051729, by rfl⟩ : syracuseStep 2735639 = 4103459) B4103459
theorem B8764973 : Blo 1823613 8764973 := bstep (se 3 (by rfl) ⟨1643432, by rfl⟩ : syracuseStep 8764973 = 3286865) B3286865
theorem B6929995 : Blo 1823613 6929995 := bstep (se 1 (by rfl) ⟨5197496, by rfl⟩ : syracuseStep 6929995 = 10394993) B10394993
theorem B5193305 : Blo 1823613 5193305 := bstep (se 2 (by rfl) ⟨1947489, by rfl⟩ : syracuseStep 5193305 = 3894979) B3894979
theorem B2735705 : Blo 1823613 2735705 := bstep (se 2 (by rfl) ⟨1025889, by rfl⟩ : syracuseStep 2735705 = 2051779) B2051779
theorem B4103819 : Blo 1823613 4103819 := bstep (se 1 (by rfl) ⟨3077864, by rfl⟩ : syracuseStep 4103819 = 6155729) B6155729
theorem B7790231 : Blo 1823613 7790231 := bstep (se 1 (by rfl) ⟨5842673, by rfl⟩ : syracuseStep 7790231 = 11685347) B11685347
theorem B4103873 : Blo 1823613 4103873 := bstep (se 2 (by rfl) ⟨1538952, by rfl⟩ : syracuseStep 4103873 = 3077905) B3077905
theorem B2735819 : Blo 1823613 2735819 := bstep (se 1 (by rfl) ⟨2051864, by rfl⟩ : syracuseStep 2735819 = 4103729) B4103729
theorem B3079883 : Blo 1823613 3079883 := bstep (se 1 (by rfl) ⟨2309912, by rfl⟩ : syracuseStep 3079883 = 4619825) B4619825
theorem B2735831 : Blo 1823613 2735831 := bstep (se 1 (by rfl) ⟨2051873, by rfl⟩ : syracuseStep 2735831 = 4103747) B4103747
theorem B2735897 : Blo 1823613 2735897 := bstep (se 2 (by rfl) ⟨1025961, by rfl⟩ : syracuseStep 2735897 = 2051923) B2051923
theorem B3080011 : Blo 1823613 3080011 := bstep (se 1 (by rfl) ⟨2310008, by rfl⟩ : syracuseStep 3080011 = 4620017) B4620017
theorem B6930269 : Blo 1823613 6930269 := bstep (se 3 (by rfl) ⟨1299425, by rfl⟩ : syracuseStep 6930269 = 2598851) B2598851
theorem B3465089 : Blo 1823613 3465089 := bstep (se 2 (by rfl) ⟨1299408, by rfl⟩ : syracuseStep 3465089 = 2598817) B2598817
theorem B2736011 : Blo 1823613 2736011 := bstep (se 1 (by rfl) ⟨2052008, by rfl⟩ : syracuseStep 2736011 = 4104017) B4104017
theorem B2736023 : Blo 1823613 2736023 := bstep (se 1 (by rfl) ⟨2052017, by rfl⟩ : syracuseStep 2736023 = 4104035) B4104035
theorem B4104089 : Blo 1823613 4104089 := bstep (se 2 (by rfl) ⟨1539033, by rfl⟩ : syracuseStep 4104089 = 3078067) B3078067
theorem B7790539 : Blo 1823613 7790539 := bstep (se 1 (by rfl) ⟨5842904, by rfl⟩ : syracuseStep 7790539 = 11685809) B11685809
theorem B2736089 : Blo 1823613 2736089 := bstep (se 2 (by rfl) ⟨1026033, by rfl⟩ : syracuseStep 2736089 = 2052067) B2052067
theorem B3080153 : Blo 1823613 3080153 := bstep (se 2 (by rfl) ⟨1155057, by rfl⟩ : syracuseStep 3080153 = 2310115) B2310115
theorem B4104179 : Blo 1823613 4104179 := bstep (se 1 (by rfl) ⟨3078134, by rfl⟩ : syracuseStep 4104179 = 6156269) B6156269
theorem B2736143 : Blo 1823613 2736143 := bstep (se 1 (by rfl) ⟨2052107, by rfl⟩ : syracuseStep 2736143 = 4104215) B4104215
theorem B4218895 : Blo 1823613 4218895 := bstep (se 1 (by rfl) ⟨3164171, by rfl⟩ : syracuseStep 4218895 = 6328343) B6328343
theorem B3080207 : Blo 1823613 3080207 := bstep (se 1 (by rfl) ⟨2310155, by rfl⟩ : syracuseStep 3080207 = 4620311) B4620311
theorem B4931617 : Blo 1823613 4931617 := bstep (se 2 (by rfl) ⟨1849356, by rfl⟩ : syracuseStep 4931617 = 3698713) B3698713
theorem B6160427 : Blo 1823613 6160427 := bstep (se 1 (by rfl) ⟨4620320, by rfl⟩ : syracuseStep 6160427 = 9240641) B9240641
theorem B2736185 : Blo 1823613 2736185 := bstep (se 2 (by rfl) ⟨1026069, by rfl⟩ : syracuseStep 2736185 = 2052139) B2052139
theorem B4104251 : Blo 1823613 4104251 := bstep (se 1 (by rfl) ⟨3078188, by rfl⟩ : syracuseStep 4104251 = 6156377) B6156377
theorem B2736263 : Blo 1823613 2736263 := bstep (se 1 (by rfl) ⟨2052197, by rfl⟩ : syracuseStep 2736263 = 4104395) B4104395
theorem B5193875 : Blo 1823613 5193875 := bstep (se 1 (by rfl) ⟨3895406, by rfl⟩ : syracuseStep 5193875 = 7790813) B7790813
theorem B2736299 : Blo 1823613 2736299 := bstep (se 1 (by rfl) ⟨2052224, by rfl⟩ : syracuseStep 2736299 = 4104449) B4104449
theorem B4104377 : Blo 1823613 4104377 := bstep (se 2 (by rfl) ⟨1539141, by rfl⟩ : syracuseStep 4104377 = 3078283) B3078283
theorem B4620473 : Blo 1823613 4620473 := bstep (se 2 (by rfl) ⟨1732677, by rfl⟩ : syracuseStep 4620473 = 3465355) B3465355
theorem B3948745 : Blo 1823613 3948745 := bstep (se 2 (by rfl) ⟨1480779, by rfl⟩ : syracuseStep 3948745 = 2961559) B2961559
theorem B2736329 : Blo 1823613 2736329 := bstep (se 2 (by rfl) ⟨1026123, by rfl⟩ : syracuseStep 2736329 = 2052247) B2052247
theorem B2736443 : Blo 1823613 2736443 := bstep (se 1 (by rfl) ⟨2052332, by rfl⟩ : syracuseStep 2736443 = 4104665) B4104665
theorem B2736503 : Blo 1823613 2736503 := bstep (se 1 (by rfl) ⟨2052377, by rfl⟩ : syracuseStep 2736503 = 4104755) B4104755
theorem B2310535 : Blo 1823613 2310535 := bstep (se 1 (by rfl) ⟨1732901, by rfl⟩ : syracuseStep 2310535 = 3465803) B3465803
theorem B2736527 : Blo 1823613 2736527 := bstep (se 1 (by rfl) ⟨2052395, by rfl⟩ : syracuseStep 2736527 = 4104791) B4104791
theorem B2736569 : Blo 1823613 2736569 := bstep (se 2 (by rfl) ⟨1026213, by rfl⟩ : syracuseStep 2736569 = 2052427) B2052427
theorem B18735569 : Blo 1823613 18735569 := bstep (se 2 (by rfl) ⟨7025838, by rfl⟩ : syracuseStep 18735569 = 14051677) B14051677
theorem B2736647 : Blo 1823613 2736647 := bstep (se 1 (by rfl) ⟨2052485, by rfl⟩ : syracuseStep 2736647 = 4104971) B4104971
theorem B4104719 : Blo 1823613 4104719 := bstep (se 1 (by rfl) ⟨3078539, by rfl⟩ : syracuseStep 4104719 = 6157079) B6157079
theorem B4104737 : Blo 1823613 4104737 := bstep (se 2 (by rfl) ⟨1539276, by rfl⟩ : syracuseStep 4104737 = 3078553) B3078553
theorem B2736683 : Blo 1823613 2736683 := bstep (se 1 (by rfl) ⟨2052512, by rfl⟩ : syracuseStep 2736683 = 4105025) B4105025
theorem B6324797 : Blo 1823613 6324797 := bstep (se 3 (by rfl) ⟨1185899, by rfl⟩ : syracuseStep 6324797 = 2371799) B2371799
theorem B2736713 : Blo 1823613 2736713 := bstep (se 2 (by rfl) ⟨1026267, by rfl⟩ : syracuseStep 2736713 = 2052535) B2052535
theorem B2736827 : Blo 1823613 2736827 := bstep (se 1 (by rfl) ⟨2052620, by rfl⟩ : syracuseStep 2736827 = 4105241) B4105241
theorem B9241289 : Blo 1823613 9241289 := bstep (se 2 (by rfl) ⟨3465483, by rfl⟩ : syracuseStep 9241289 = 6930967) B6930967
theorem B2736887 : Blo 1823613 2736887 := bstep (se 1 (by rfl) ⟨2052665, by rfl⟩ : syracuseStep 2736887 = 4105331) B4105331
theorem B4932353 : Blo 1823613 4932353 := bstep (se 2 (by rfl) ⟨1849632, by rfl⟩ : syracuseStep 4932353 = 3699265) B3699265
theorem B2736911 : Blo 1823613 2736911 := bstep (se 1 (by rfl) ⟨2052683, by rfl⟩ : syracuseStep 2736911 = 4105367) B4105367
theorem B2736953 : Blo 1823613 2736953 := bstep (se 2 (by rfl) ⟨1026357, by rfl⟩ : syracuseStep 2736953 = 2052715) B2052715
theorem B4105079 : Blo 1823613 4105079 := bstep (se 1 (by rfl) ⟨3078809, by rfl⟩ : syracuseStep 4105079 = 6157619) B6157619
theorem B2737031 : Blo 1823613 2737031 := bstep (se 1 (by rfl) ⟨2052773, by rfl⟩ : syracuseStep 2737031 = 4105547) B4105547
theorem B2737067 : Blo 1823613 2737067 := bstep (se 1 (by rfl) ⟨2052800, by rfl⟩ : syracuseStep 2737067 = 4105601) B4105601
theorem B2737097 : Blo 1823613 2737097 := bstep (se 2 (by rfl) ⟨1026411, by rfl⟩ : syracuseStep 2737097 = 2052823) B2052823
theorem B136872917 : Blo 1823613 136872917 := bstep (se 7 (by rfl) ⟨1603979, by rfl⟩ : syracuseStep 136872917 = 3207959) B3207959
theorem B5194763 : Blo 1823613 5194763 := bstep (se 1 (by rfl) ⟨3896072, by rfl⟩ : syracuseStep 5194763 = 7792145) B7792145
theorem B4105259 : Blo 1823613 4105259 := bstep (se 1 (by rfl) ⟨3078944, by rfl⟩ : syracuseStep 4105259 = 6157889) B6157889
theorem B2737211 : Blo 1823613 2737211 := bstep (se 1 (by rfl) ⟨2052908, by rfl⟩ : syracuseStep 2737211 = 4105817) B4105817
theorem B7898179 : Blo 1823613 7898179 := bstep (se 1 (by rfl) ⟨5923634, by rfl⟩ : syracuseStep 7898179 = 11847269) B11847269
theorem B2737271 : Blo 1823613 2737271 := bstep (se 1 (by rfl) ⟨2052953, by rfl⟩ : syracuseStep 2737271 = 4105907) B4105907
theorem B2598031 : Blo 1823613 2598031 := bstep (se 1 (by rfl) ⟨1948523, by rfl⟩ : syracuseStep 2598031 = 3897047) B3897047
theorem B2737295 : Blo 1823613 2737295 := bstep (se 1 (by rfl) ⟨2052971, by rfl⟩ : syracuseStep 2737295 = 4105943) B4105943
theorem B2737337 : Blo 1823613 2737337 := bstep (se 2 (by rfl) ⟨1026501, by rfl⟩ : syracuseStep 2737337 = 2053003) B2053003
theorem B2598151 : Blo 1823613 2598151 := bstep (se 1 (by rfl) ⟨1948613, by rfl⟩ : syracuseStep 2598151 = 3897227) B3897227
theorem B2737415 : Blo 1823613 2737415 := bstep (se 1 (by rfl) ⟨2053061, by rfl⟩ : syracuseStep 2737415 = 4106123) B4106123
theorem B4932893 : Blo 1823613 4932893 := bstep (se 3 (by rfl) ⟨924917, by rfl⟩ : syracuseStep 4932893 = 1849835) B1849835
theorem B13862177 : Blo 1823613 13862177 := bstep (se 2 (by rfl) ⟨5198316, by rfl⟩ : syracuseStep 13862177 = 10396633) B10396633
theorem B2737451 : Blo 1823613 2737451 := bstep (se 1 (by rfl) ⟨2053088, by rfl⟩ : syracuseStep 2737451 = 4106177) B4106177
theorem B2737481 : Blo 1823613 2737481 := bstep (se 2 (by rfl) ⟨1026555, by rfl⟩ : syracuseStep 2737481 = 2053111) B2053111
theorem B4105619 : Blo 1823613 4105619 := bstep (se 1 (by rfl) ⟨3079214, by rfl⟩ : syracuseStep 4105619 = 6158429) B6158429
theorem B2737595 : Blo 1823613 2737595 := bstep (se 1 (by rfl) ⟨2053196, by rfl⟩ : syracuseStep 2737595 = 4106393) B4106393
theorem B4105673 : Blo 1823613 4105673 := bstep (se 2 (by rfl) ⟨1539627, by rfl⟩ : syracuseStep 4105673 = 3079255) B3079255
theorem B2737655 : Blo 1823613 2737655 := bstep (se 1 (by rfl) ⟨2053241, by rfl⟩ : syracuseStep 2737655 = 4106483) B4106483
theorem B2737679 : Blo 1823613 2737679 := bstep (se 1 (by rfl) ⟨2053259, by rfl⟩ : syracuseStep 2737679 = 4106519) B4106519
theorem B2737721 : Blo 1823613 2737721 := bstep (se 2 (by rfl) ⟨1026645, by rfl⟩ : syracuseStep 2737721 = 2053291) B2053291
theorem B7399031 : Blo 1823613 7399031 := bstep (se 1 (by rfl) ⟨5549273, by rfl⟩ : syracuseStep 7399031 = 11098547) B11098547
theorem B2737799 : Blo 1823613 2737799 := bstep (se 1 (by rfl) ⟨2053349, by rfl⟩ : syracuseStep 2737799 = 4106699) B4106699
theorem B2737835 : Blo 1823613 2737835 := bstep (se 1 (by rfl) ⟨2053376, by rfl⟩ : syracuseStep 2737835 = 4106753) B4106753
theorem B13854401 : Blo 1823613 13854401 := bstep (se 2 (by rfl) ⟨5195400, by rfl⟩ : syracuseStep 13854401 = 10390801) B10390801
theorem B4384457 : Blo 1823613 4384457 := bstep (se 2 (by rfl) ⟨1644171, by rfl⟩ : syracuseStep 4384457 = 3288343) B3288343
theorem B2737865 : Blo 1823613 2737865 := bstep (se 2 (by rfl) ⟨1026699, by rfl⟩ : syracuseStep 2737865 = 2053399) B2053399
theorem B2737979 : Blo 1823613 2737979 := bstep (se 1 (by rfl) ⟨2053484, by rfl⟩ : syracuseStep 2737979 = 4106969) B4106969
theorem B4999031 : Blo 1823613 4999031 := bstep (se 1 (by rfl) ⟨3749273, by rfl⟩ : syracuseStep 4999031 = 7498547) B7498547
theorem B2738039 : Blo 1823613 2738039 := bstep (se 1 (by rfl) ⟨2053529, by rfl⟩ : syracuseStep 2738039 = 4107059) B4107059
theorem B2738063 : Blo 1823613 2738063 := bstep (se 1 (by rfl) ⟨2053547, by rfl⟩ : syracuseStep 2738063 = 4107095) B4107095
theorem B9234323 : Blo 1823613 9234323 := bstep (se 1 (by rfl) ⟨6925742, by rfl⟩ : syracuseStep 9234323 = 13851485) B13851485
theorem B2738105 : Blo 1823613 2738105 := bstep (se 2 (by rfl) ⟨1026789, by rfl⟩ : syracuseStep 2738105 = 2053579) B2053579
theorem B2738183 : Blo 1823613 2738183 := bstep (se 1 (by rfl) ⟨2053637, by rfl⟩ : syracuseStep 2738183 = 4107275) B4107275
theorem B2738219 : Blo 1823613 2738219 := bstep (se 1 (by rfl) ⟨2053664, by rfl⟩ : syracuseStep 2738219 = 4107329) B4107329
theorem B2738249 : Blo 1823613 2738249 := bstep (se 2 (by rfl) ⟨1026843, by rfl⟩ : syracuseStep 2738249 = 2053687) B2053687
theorem B4106375 : Blo 1823613 4106375 := bstep (se 1 (by rfl) ⟨3079781, by rfl⟩ : syracuseStep 4106375 = 6159563) B6159563
theorem B126412973 : Blo 1823613 126412973 := bstep (se 3 (by rfl) ⟨23702432, by rfl⟩ : syracuseStep 126412973 = 47404865) B47404865
theorem B2738363 : Blo 1823613 2738363 := bstep (se 1 (by rfl) ⟨2053772, by rfl⟩ : syracuseStep 2738363 = 4107545) B4107545
theorem B13863149 : Blo 1823613 13863149 := bstep (se 3 (by rfl) ⟨2599340, by rfl⟩ : syracuseStep 13863149 = 5198681) B5198681
theorem B4106555 : Blo 1823613 4106555 := bstep (se 1 (by rfl) ⟨3079916, by rfl⟩ : syracuseStep 4106555 = 6159833) B6159833
theorem B5843315 : Blo 1823613 5843315 := bstep (se 1 (by rfl) ⟨4382486, by rfl⟩ : syracuseStep 5843315 = 8764973) B8764973
theorem B4999559 : Blo 1823613 4999559 := bstep (se 1 (by rfl) ⟨3749669, by rfl⟩ : syracuseStep 4999559 = 7499339) B7499339
theorem B8440199 : Blo 1823613 8440199 := bstep (se 1 (by rfl) ⟨6330149, by rfl⟩ : syracuseStep 8440199 = 12660299) B12660299
theorem B4106681 : Blo 1823613 4106681 := bstep (se 2 (by rfl) ⟨1540005, by rfl⟩ : syracuseStep 4106681 = 3080011) B3080011
theorem B15592013 : Blo 1823613 15592013 := bstep (se 3 (by rfl) ⟨2923502, by rfl⟩ : syracuseStep 15592013 = 5847005) B5847005
theorem B8768087 : Blo 1823613 8768087 := bstep (se 1 (by rfl) ⟨6576065, by rfl⟩ : syracuseStep 8768087 = 13152131) B13152131
theorem B5196403 : Blo 1823613 5196403 := bstep (se 1 (by rfl) ⟨3897302, by rfl⟩ : syracuseStep 5196403 = 7794605) B7794605
theorem B15584015 : Blo 1823613 15584015 := bstep (se 1 (by rfl) ⟨11688011, by rfl⟩ : syracuseStep 15584015 = 23376023) B23376023
theorem B4107023 : Blo 1823613 4107023 := bstep (se 1 (by rfl) ⟨3080267, by rfl⟩ : syracuseStep 4107023 = 6160535) B6160535
theorem B4107041 : Blo 1823613 4107041 := bstep (se 2 (by rfl) ⟨1540140, by rfl⟩ : syracuseStep 4107041 = 3080281) B3080281
theorem B31591205 : Blo 1823613 31591205 := bstep (se 4 (by rfl) ⟨2961675, by rfl⟩ : syracuseStep 31591205 = 5923351) B5923351
theorem B5196631 : Blo 1823613 5196631 := bstep (se 1 (by rfl) ⟨3897473, by rfl⟩ : syracuseStep 5196631 = 7794947) B7794947
theorem B5336075 : Blo 1823613 5336075 := bstep (se 1 (by rfl) ⟨4002056, by rfl⟩ : syracuseStep 5336075 = 8004113) B8004113
theorem B14797835 : Blo 1823613 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B6155351 : Blo 1823613 6155351 := bstep (se 1 (by rfl) ⟨4616513, by rfl⟩ : syracuseStep 6155351 = 9233027) B9233027
theorem B4107383 : Blo 1823613 4107383 := bstep (se 1 (by rfl) ⟨3080537, by rfl⟩ : syracuseStep 4107383 = 6161075) B6161075
theorem B7793921 : Blo 1823613 7793921 := bstep (se 2 (by rfl) ⟨2922720, by rfl⟩ : syracuseStep 7793921 = 5845441) B5845441
theorem B4107563 : Blo 1823613 4107563 := bstep (se 1 (by rfl) ⟨3080672, by rfl⟩ : syracuseStep 4107563 = 6161345) B6161345
theorem B3288379 : Blo 1823613 3288379 := bstep (se 1 (by rfl) ⟨2466284, by rfl⟩ : syracuseStep 3288379 = 4932569) B4932569
theorem B15592763 : Blo 1823613 15592763 := bstep (se 1 (by rfl) ⟨11694572, by rfl⟩ : syracuseStep 15592763 = 23389145) B23389145
theorem B2051599 : Blo 1823613 2051599 := bstep (se 1 (by rfl) ⟨1538699, by rfl⟩ : syracuseStep 2051599 = 3077399) B3077399
theorem B5549627 : Blo 1823613 5549627 := bstep (se 1 (by rfl) ⟨4162220, by rfl⟩ : syracuseStep 5549627 = 8324441) B8324441
theorem B6155837 : Blo 1823613 6155837 := bstep (se 3 (by rfl) ⟨1154219, by rfl⟩ : syracuseStep 6155837 = 2308439) B2308439
theorem B9858647 : Blo 1823613 9858647 := bstep (se 1 (by rfl) ⟨7393985, by rfl⟩ : syracuseStep 9858647 = 14787971) B14787971
theorem B8326775 : Blo 1823613 8326775 := bstep (se 1 (by rfl) ⟨6245081, by rfl⟩ : syracuseStep 8326775 = 12490163) B12490163
theorem B19738403 : Blo 1823613 19738403 := bstep (se 1 (by rfl) ⟨14803802, by rfl⟩ : syracuseStep 19738403 = 29607605) B29607605
theorem B2772983 : Blo 1823613 2772983 := bstep (se 1 (by rfl) ⟨2079737, by rfl⟩ : syracuseStep 2772983 = 4159475) B4159475
theorem B2052103 : Blo 1823613 2052103 := bstep (se 1 (by rfl) ⟨1539077, by rfl⟩ : syracuseStep 2052103 = 3078155) B3078155
theorem B4616311 : Blo 1823613 4616311 := bstep (se 1 (by rfl) ⟨3462233, by rfl⟩ : syracuseStep 4616311 = 6924467) B6924467
theorem B2773111 : Blo 1823613 2773111 := bstep (se 1 (by rfl) ⟨2079833, by rfl⟩ : syracuseStep 2773111 = 4159667) B4159667
theorem B3747959 : Blo 1823613 3747959 := bstep (se 1 (by rfl) ⟨2810969, by rfl⟩ : syracuseStep 3747959 = 5621939) B5621939
theorem B2052283 : Blo 1823613 2052283 := bstep (se 1 (by rfl) ⟨1539212, by rfl⟩ : syracuseStep 2052283 = 3078425) B3078425
theorem B6926593 : Blo 1823613 6926593 := bstep (se 2 (by rfl) ⟨2597472, by rfl⟩ : syracuseStep 6926593 = 5194945) B5194945
theorem B9867557 : Blo 1823613 9867557 := bstep (se 4 (by rfl) ⟨925083, by rfl⟩ : syracuseStep 9867557 = 1850167) B1850167
theorem B3289403 : Blo 1823613 3289403 := bstep (se 1 (by rfl) ⟨2467052, by rfl⟩ : syracuseStep 3289403 = 4934105) B4934105
theorem B5198215 : Blo 1823613 5198215 := bstep (se 1 (by rfl) ⟨3898661, by rfl⟩ : syracuseStep 5198215 = 7797323) B7797323
theorem B9368011 : Blo 1823613 9368011 := bstep (se 1 (by rfl) ⟨7026008, by rfl⟩ : syracuseStep 9368011 = 14052017) B14052017
theorem B11096599 : Blo 1823613 11096599 := bstep (se 1 (by rfl) ⟨8322449, by rfl⟩ : syracuseStep 11096599 = 16644899) B16644899
theorem B4616747 : Blo 1823613 4616747 := bstep (se 1 (by rfl) ⟨3462560, by rfl⟩ : syracuseStep 4616747 = 6925121) B6925121
theorem B113865259 : Blo 1823613 113865259 := bstep (se 1 (by rfl) ⟨85398944, by rfl⟩ : syracuseStep 113865259 = 170797889) B170797889
theorem B3895867 : Blo 1823613 3895867 := bstep (se 1 (by rfl) ⟨2921900, by rfl⟩ : syracuseStep 3895867 = 5843801) B5843801
theorem B2052751 : Blo 1823613 2052751 := bstep (se 1 (by rfl) ⟨1539563, by rfl⟩ : syracuseStep 2052751 = 3079127) B3079127
theorem B5198489 : Blo 1823613 5198489 := bstep (se 2 (by rfl) ⟨1949433, by rfl⟩ : syracuseStep 5198489 = 3898867) B3898867
theorem B4682611 : Blo 1823613 4682611 := bstep (se 1 (by rfl) ⟨3511958, by rfl⟩ : syracuseStep 4682611 = 7023917) B7023917
theorem B1823623 : Blo 1823613 1823623 := bstep (se 1 (by rfl) ⟨1367717, by rfl⟩ : syracuseStep 1823623 = 2735435) B2735435
theorem B1823631 : Blo 1823613 1823631 := bstep (se 1 (by rfl) ⟨1367723, by rfl⟩ : syracuseStep 1823631 = 2735447) B2735447
theorem B9237401 : Blo 1823613 9237401 := bstep (se 2 (by rfl) ⟨3464025, by rfl⟩ : syracuseStep 9237401 = 6928051) B6928051
theorem B15594403 : Blo 1823613 15594403 := bstep (se 1 (by rfl) ⟨11695802, by rfl⟩ : syracuseStep 15594403 = 23391605) B23391605
theorem B6157241 : Blo 1823613 6157241 := bstep (se 2 (by rfl) ⟨2308965, by rfl⟩ : syracuseStep 6157241 = 4617931) B4617931
theorem B1823675 : Blo 1823613 1823675 := bstep (se 1 (by rfl) ⟨1367756, by rfl⟩ : syracuseStep 1823675 = 2735513) B2735513
theorem B1823751 : Blo 1823613 1823751 := bstep (se 1 (by rfl) ⟨1367813, by rfl⟩ : syracuseStep 1823751 = 2735627) B2735627
theorem B13857803 : Blo 1823613 13857803 := bstep (se 1 (by rfl) ⟨10393352, by rfl⟩ : syracuseStep 13857803 = 20786705) B20786705
theorem B1823759 : Blo 1823613 1823759 := bstep (se 1 (by rfl) ⟨1367819, by rfl⟩ : syracuseStep 1823759 = 2735639) B2735639
theorem B4682785 : Blo 1823613 4682785 := bstep (se 2 (by rfl) ⟨1756044, by rfl⟩ : syracuseStep 4682785 = 3512089) B3512089
theorem B3896363 : Blo 1823613 3896363 := bstep (se 1 (by rfl) ⟨2922272, by rfl⟩ : syracuseStep 3896363 = 5844545) B5844545
theorem B3462203 : Blo 1823613 3462203 := bstep (se 1 (by rfl) ⟨2596652, by rfl⟩ : syracuseStep 3462203 = 5193305) B5193305
theorem B1823803 : Blo 1823613 1823803 := bstep (se 1 (by rfl) ⟨1367852, by rfl⟩ : syracuseStep 1823803 = 2735705) B2735705
theorem B1823879 : Blo 1823613 1823879 := bstep (se 1 (by rfl) ⟨1367909, by rfl⟩ : syracuseStep 1823879 = 2735819) B2735819
theorem B3699847 : Blo 1823613 3699847 := bstep (se 1 (by rfl) ⟨2774885, by rfl⟩ : syracuseStep 3699847 = 5549771) B5549771
theorem B2053255 : Blo 1823613 2053255 := bstep (se 1 (by rfl) ⟨1539941, by rfl⟩ : syracuseStep 2053255 = 3079883) B3079883
theorem B1823887 : Blo 1823613 1823887 := bstep (se 1 (by rfl) ⟨1367915, by rfl⟩ : syracuseStep 1823887 = 2735831) B2735831
theorem B1823931 : Blo 1823613 1823931 := bstep (se 1 (by rfl) ⟨1367948, by rfl⟩ : syracuseStep 1823931 = 2735897) B2735897
theorem B49943789 : Blo 1823613 49943789 := bstep (se 3 (by rfl) ⟨9364460, by rfl⟩ : syracuseStep 49943789 = 18728921) B18728921
theorem B1824007 : Blo 1823613 1824007 := bstep (se 1 (by rfl) ⟨1368005, by rfl⟩ : syracuseStep 1824007 = 2736011) B2736011
theorem B1824015 : Blo 1823613 1824015 := bstep (se 1 (by rfl) ⟨1368011, by rfl⟩ : syracuseStep 1824015 = 2736023) B2736023
theorem B3077419 : Blo 1823613 3077419 := bstep (se 1 (by rfl) ⟨2308064, by rfl⟩ : syracuseStep 3077419 = 4616129) B4616129
theorem B1824059 : Blo 1823613 1824059 := bstep (se 1 (by rfl) ⟨1368044, by rfl⟩ : syracuseStep 1824059 = 2736089) B2736089
theorem B2053435 : Blo 1823613 2053435 := bstep (se 1 (by rfl) ⟨1540076, by rfl⟩ : syracuseStep 2053435 = 3080153) B3080153
theorem B4617587 : Blo 1823613 4617587 := bstep (se 1 (by rfl) ⟨3463190, by rfl⟩ : syracuseStep 4617587 = 6926381) B6926381
theorem B1824135 : Blo 1823613 1824135 := bstep (se 1 (by rfl) ⟨1368101, by rfl⟩ : syracuseStep 1824135 = 2736203) B2736203
theorem B4617607 : Blo 1823613 4617607 := bstep (se 1 (by rfl) ⟨3463205, by rfl⟩ : syracuseStep 4617607 = 6926411) B6926411
theorem B6329735 : Blo 1823613 6329735 := bstep (se 1 (by rfl) ⟨4747301, by rfl⟩ : syracuseStep 6329735 = 9494603) B9494603
theorem B1824143 : Blo 1823613 1824143 := bstep (se 1 (by rfl) ⟨1368107, by rfl⟩ : syracuseStep 1824143 = 2736215) B2736215
theorem B3077561 : Blo 1823613 3077561 := bstep (se 2 (by rfl) ⟨1154085, by rfl⟩ : syracuseStep 3077561 = 2308171) B2308171
theorem B1824187 : Blo 1823613 1824187 := bstep (se 1 (by rfl) ⟨1368140, by rfl⟩ : syracuseStep 1824187 = 2736281) B2736281
theorem B17544707 : Blo 1823613 17544707 := bstep (se 1 (by rfl) ⟨13158530, by rfl⟩ : syracuseStep 17544707 = 26317061) B26317061
theorem B1824263 : Blo 1823613 1824263 := bstep (se 1 (by rfl) ⟨1368197, by rfl⟩ : syracuseStep 1824263 = 2736395) B2736395
theorem B6157835 : Blo 1823613 6157835 := bstep (se 1 (by rfl) ⟨4618376, by rfl⟩ : syracuseStep 6157835 = 9236753) B9236753
theorem B1824271 : Blo 1823613 1824271 := bstep (se 1 (by rfl) ⟨1368203, by rfl⟩ : syracuseStep 1824271 = 2736407) B2736407
theorem B3462689 : Blo 1823613 3462689 := bstep (se 2 (by rfl) ⟨1298508, by rfl⟩ : syracuseStep 3462689 = 2597017) B2597017
theorem B1824315 : Blo 1823613 1824315 := bstep (se 1 (by rfl) ⟨1368236, by rfl⟩ : syracuseStep 1824315 = 2736473) B2736473
theorem B2741879 : Blo 1823613 2741879 := bstep (se 1 (by rfl) ⟨2056409, by rfl⟩ : syracuseStep 2741879 = 4112819) B4112819
theorem B6157943 : Blo 1823613 6157943 := bstep (se 1 (by rfl) ⟨4618457, by rfl⟩ : syracuseStep 6157943 = 9236915) B9236915
theorem B1824391 : Blo 1823613 1824391 := bstep (se 1 (by rfl) ⟨1368293, by rfl⟩ : syracuseStep 1824391 = 2736587) B2736587
theorem B1824399 : Blo 1823613 1824399 := bstep (se 1 (by rfl) ⟨1368299, by rfl⟩ : syracuseStep 1824399 = 2736599) B2736599
theorem B4617881 : Blo 1823613 4617881 := bstep (se 2 (by rfl) ⟨1731705, by rfl⟩ : syracuseStep 4617881 = 3463411) B3463411
theorem B3462841 : Blo 1823613 3462841 := bstep (se 2 (by rfl) ⟨1298565, by rfl⟩ : syracuseStep 3462841 = 2597131) B2597131
theorem B1824443 : Blo 1823613 1824443 := bstep (se 1 (by rfl) ⟨1368332, by rfl⟩ : syracuseStep 1824443 = 2736665) B2736665
theorem B1824519 : Blo 1823613 1824519 := bstep (se 1 (by rfl) ⟨1368389, by rfl⟩ : syracuseStep 1824519 = 2736779) B2736779
theorem B2340623 : Blo 1823613 2340623 := bstep (se 1 (by rfl) ⟨1755467, by rfl⟩ : syracuseStep 2340623 = 3510935) B3510935
theorem B1824527 : Blo 1823613 1824527 := bstep (se 1 (by rfl) ⟨1368395, by rfl⟩ : syracuseStep 1824527 = 2736791) B2736791
theorem B4618043 : Blo 1823613 4618043 := bstep (se 1 (by rfl) ⟨3463532, by rfl⟩ : syracuseStep 4618043 = 6927065) B6927065
theorem B1824571 : Blo 1823613 1824571 := bstep (se 1 (by rfl) ⟨1368428, by rfl⟩ : syracuseStep 1824571 = 2736857) B2736857
theorem B57702257 : Blo 1823613 57702257 := bstep (se 2 (by rfl) ⟨21638346, by rfl⟩ : syracuseStep 57702257 = 43276693) B43276693
theorem B1824647 : Blo 1823613 1824647 := bstep (se 1 (by rfl) ⟨1368485, by rfl⟩ : syracuseStep 1824647 = 2736971) B2736971
theorem B1824655 : Blo 1823613 1824655 := bstep (se 1 (by rfl) ⟨1368491, by rfl⟩ : syracuseStep 1824655 = 2736983) B2736983
theorem B1824699 : Blo 1823613 1824699 := bstep (se 1 (by rfl) ⟨1368524, by rfl⟩ : syracuseStep 1824699 = 2737049) B2737049
theorem B1824775 : Blo 1823613 1824775 := bstep (se 1 (by rfl) ⟨1368581, by rfl⟩ : syracuseStep 1824775 = 2737163) B2737163
theorem B18716683 : Blo 1823613 18716683 := bstep (se 1 (by rfl) ⟨14037512, by rfl⟩ : syracuseStep 18716683 = 28075025) B28075025
theorem B4618255 : Blo 1823613 4618255 := bstep (se 1 (by rfl) ⟨3463691, by rfl⟩ : syracuseStep 4618255 = 6927383) B6927383
theorem B1824783 : Blo 1823613 1824783 := bstep (se 1 (by rfl) ⟨1368587, by rfl⟩ : syracuseStep 1824783 = 2737175) B2737175
theorem B1824827 : Blo 1823613 1824827 := bstep (se 1 (by rfl) ⟨1368620, by rfl⟩ : syracuseStep 1824827 = 2737241) B2737241
theorem B3078263 : Blo 1823613 3078263 := bstep (se 1 (by rfl) ⟨2308697, by rfl⟩ : syracuseStep 3078263 = 4617395) B4617395
theorem B1824903 : Blo 1823613 1824903 := bstep (se 1 (by rfl) ⟨1368677, by rfl⟩ : syracuseStep 1824903 = 2737355) B2737355
theorem B1824911 : Blo 1823613 1824911 := bstep (se 1 (by rfl) ⟨1368683, by rfl⟩ : syracuseStep 1824911 = 2737367) B2737367
theorem B2308267 : Blo 1823613 2308267 := bstep (se 1 (by rfl) ⟨1731200, by rfl⟩ : syracuseStep 2308267 = 3462401) B3462401
theorem B1824955 : Blo 1823613 1824955 := bstep (se 1 (by rfl) ⟨1368716, by rfl⟩ : syracuseStep 1824955 = 2737433) B2737433
theorem B8771777 : Blo 1823613 8771777 := bstep (se 2 (by rfl) ⟨3289416, by rfl⟩ : syracuseStep 8771777 = 6578833) B6578833
theorem B6412489 : Blo 1823613 6412489 := bstep (se 2 (by rfl) ⟨2404683, by rfl⟩ : syracuseStep 6412489 = 4809367) B4809367
theorem B6158537 : Blo 1823613 6158537 := bstep (se 2 (by rfl) ⟨2309451, by rfl⟩ : syracuseStep 6158537 = 4618903) B4618903
theorem B1825031 : Blo 1823613 1825031 := bstep (se 1 (by rfl) ⟨1368773, by rfl⟩ : syracuseStep 1825031 = 2737547) B2737547
theorem B1825039 : Blo 1823613 1825039 := bstep (se 1 (by rfl) ⟨1368779, by rfl⟩ : syracuseStep 1825039 = 2737559) B2737559
theorem B4618529 : Blo 1823613 4618529 := bstep (se 2 (by rfl) ⟨1731948, by rfl⟩ : syracuseStep 4618529 = 3463897) B3463897
theorem B1825083 : Blo 1823613 1825083 := bstep (se 1 (by rfl) ⟨1368812, by rfl⟩ : syracuseStep 1825083 = 2737625) B2737625
theorem B10393991 : Blo 1823613 10393991 := bstep (se 1 (by rfl) ⟨7795493, by rfl⟩ : syracuseStep 10393991 = 15590987) B15590987
theorem B1825159 : Blo 1823613 1825159 := bstep (se 1 (by rfl) ⟨1368869, by rfl⟩ : syracuseStep 1825159 = 2737739) B2737739
theorem B2308495 : Blo 1823613 2308495 := bstep (se 1 (by rfl) ⟨1731371, by rfl⟩ : syracuseStep 2308495 = 3462743) B3462743
theorem B1825167 : Blo 1823613 1825167 := bstep (se 1 (by rfl) ⟨1368875, by rfl⟩ : syracuseStep 1825167 = 2737751) B2737751
theorem B1825211 : Blo 1823613 1825211 := bstep (se 1 (by rfl) ⟨1368908, by rfl⟩ : syracuseStep 1825211 = 2737817) B2737817
theorem B1825287 : Blo 1823613 1825287 := bstep (se 1 (by rfl) ⟨1368965, by rfl⟩ : syracuseStep 1825287 = 2737931) B2737931
theorem B1825295 : Blo 1823613 1825295 := bstep (se 1 (by rfl) ⟨1368971, by rfl⟩ : syracuseStep 1825295 = 2737943) B2737943
theorem B3078715 : Blo 1823613 3078715 := bstep (se 1 (by rfl) ⟨2309036, by rfl⟩ : syracuseStep 3078715 = 4618073) B4618073
theorem B1825339 : Blo 1823613 1825339 := bstep (se 1 (by rfl) ⟨1369004, by rfl⟩ : syracuseStep 1825339 = 2738009) B2738009
theorem B1825415 : Blo 1823613 1825415 := bstep (se 1 (by rfl) ⟨1369061, by rfl⟩ : syracuseStep 1825415 = 2738123) B2738123
theorem B1825423 : Blo 1823613 1825423 := bstep (se 1 (by rfl) ⟨1369067, by rfl⟩ : syracuseStep 1825423 = 2738135) B2738135
theorem B1825467 : Blo 1823613 1825467 := bstep (se 1 (by rfl) ⟨1369100, by rfl⟩ : syracuseStep 1825467 = 2738201) B2738201
theorem B8321737 : Blo 1823613 8321737 := bstep (se 2 (by rfl) ⟨3120651, by rfl⟩ : syracuseStep 8321737 = 6241303) B6241303
theorem B3078857 : Blo 1823613 3078857 := bstep (se 2 (by rfl) ⟨1154571, by rfl⟩ : syracuseStep 3078857 = 2309143) B2309143
theorem B1825543 : Blo 1823613 1825543 := bstep (se 1 (by rfl) ⟨1369157, by rfl⟩ : syracuseStep 1825543 = 2738315) B2738315
theorem B3119887 : Blo 1823613 3119887 := bstep (se 1 (by rfl) ⟨2339915, by rfl⟩ : syracuseStep 3119887 = 4679831) B4679831
theorem B1825551 : Blo 1823613 1825551 := bstep (se 1 (by rfl) ⟨1369163, by rfl⟩ : syracuseStep 1825551 = 2738327) B2738327
theorem B37452581 : Blo 1823613 37452581 := bstep (se 4 (by rfl) ⟨3511179, by rfl⟩ : syracuseStep 37452581 = 7022359) B7022359
theorem B1825595 : Blo 1823613 1825595 := bstep (se 1 (by rfl) ⟨1369196, by rfl⟩ : syracuseStep 1825595 = 2738393) B2738393
theorem B8772467 : Blo 1823613 8772467 := bstep (se 1 (by rfl) ⟨6579350, by rfl⟩ : syracuseStep 8772467 = 13158701) B13158701
theorem B6159239 : Blo 1823613 6159239 := bstep (se 1 (by rfl) ⟨4619429, by rfl⟩ : syracuseStep 6159239 = 9238859) B9238859
theorem B13859747 : Blo 1823613 13859747 := bstep (se 1 (by rfl) ⟨10394810, by rfl⟩ : syracuseStep 13859747 = 20789621) B20789621
theorem B2743369 : Blo 1823613 2743369 := bstep (se 2 (by rfl) ⟨1028763, by rfl⟩ : syracuseStep 2743369 = 2057527) B2057527
theorem B6929495 : Blo 1823613 6929495 := bstep (se 1 (by rfl) ⟨5197121, by rfl⟩ : syracuseStep 6929495 = 10394243) B10394243
theorem B2309239 : Blo 1823613 2309239 := bstep (se 1 (by rfl) ⟨1731929, by rfl⟩ : syracuseStep 2309239 = 3463859) B3463859
theorem B4103315 : Blo 1823613 4103315 := bstep (se 1 (by rfl) ⟨3077486, by rfl⟩ : syracuseStep 4103315 = 6154973) B6154973
theorem B4103369 : Blo 1823613 4103369 := bstep (se 2 (by rfl) ⟨1538763, by rfl⟩ : syracuseStep 4103369 = 3077527) B3077527
theorem B6159617 : Blo 1823613 6159617 := bstep (se 2 (by rfl) ⟨2309856, by rfl⟩ : syracuseStep 6159617 = 4619713) B4619713
theorem B4619531 : Blo 1823613 4619531 := bstep (se 1 (by rfl) ⟨3464648, by rfl⟩ : syracuseStep 4619531 = 6929297) B6929297
theorem B2735495 : Blo 1823613 2735495 := bstep (se 1 (by rfl) ⟨2051621, by rfl⟩ : syracuseStep 2735495 = 4103243) B4103243
theorem B3079559 : Blo 1823613 3079559 := bstep (se 1 (by rfl) ⟨2309669, by rfl⟩ : syracuseStep 3079559 = 4619339) B4619339
theorem B2735531 : Blo 1823613 2735531 := bstep (se 1 (by rfl) ⟨2051648, by rfl⟩ : syracuseStep 2735531 = 4103297) B4103297
theorem B3464633 : Blo 1823613 3464633 := bstep (se 2 (by rfl) ⟨1299237, by rfl⟩ : syracuseStep 3464633 = 2598475) B2598475
theorem B9239993 : Blo 1823613 9239993 := bstep (se 2 (by rfl) ⟨3464997, by rfl⟩ : syracuseStep 9239993 = 6929995) B6929995
theorem B2309563 : Blo 1823613 2309563 := bstep (se 1 (by rfl) ⟨1732172, by rfl⟩ : syracuseStep 2309563 = 3464345) B3464345
theorem B2735561 : Blo 1823613 2735561 := bstep (se 2 (by rfl) ⟨1025835, by rfl⟩ : syracuseStep 2735561 = 2051671) B2051671
theorem B2735675 : Blo 1823613 2735675 := bstep (se 1 (by rfl) ⟨2051756, by rfl⟩ : syracuseStep 2735675 = 4103513) B4103513
theorem B4931131 : Blo 1823613 4931131 := bstep (se 1 (by rfl) ⟨3698348, by rfl⟩ : syracuseStep 4931131 = 7396697) B7396697
theorem B6929981 : Blo 1823613 6929981 := bstep (se 3 (by rfl) ⟨1299371, by rfl⟩ : syracuseStep 6929981 = 2598743) B2598743
theorem B17530445 : Blo 1823613 17530445 := bstep (se 3 (by rfl) ⟨3286958, by rfl⟩ : syracuseStep 17530445 = 6573917) B6573917
theorem B2735735 : Blo 1823613 2735735 := bstep (se 1 (by rfl) ⟨2051801, by rfl⟩ : syracuseStep 2735735 = 4103603) B4103603
theorem B19725943 : Blo 1823613 19725943 := bstep (se 1 (by rfl) ⟨14794457, by rfl⟩ : syracuseStep 19725943 = 29588915) B29588915
theorem B2735759 : Blo 1823613 2735759 := bstep (se 1 (by rfl) ⟨2051819, by rfl⟩ : syracuseStep 2735759 = 4103639) B4103639
theorem B2735801 : Blo 1823613 2735801 := bstep (se 2 (by rfl) ⟨1025925, by rfl⟩ : syracuseStep 2735801 = 2051851) B2051851
theorem B2465527 : Blo 1823613 2465527 := bstep (se 1 (by rfl) ⟨1849145, by rfl⟩ : syracuseStep 2465527 = 3698291) B3698291
theorem B2735879 : Blo 1823613 2735879 := bstep (se 1 (by rfl) ⟨2051909, by rfl⟩ : syracuseStep 2735879 = 4103819) B4103819
theorem B5193487 : Blo 1823613 5193487 := bstep (se 1 (by rfl) ⟨3895115, by rfl⟩ : syracuseStep 5193487 = 7790231) B7790231
theorem B6668065 : Blo 1823613 6668065 := bstep (se 2 (by rfl) ⟨2500524, by rfl⟩ : syracuseStep 6668065 = 5001049) B5001049
theorem B2735915 : Blo 1823613 2735915 := bstep (se 1 (by rfl) ⟨2051936, by rfl⟩ : syracuseStep 2735915 = 4103873) B4103873
theorem B5193533 : Blo 1823613 5193533 := bstep (se 3 (by rfl) ⟨973787, by rfl⟩ : syracuseStep 5193533 = 1947575) B1947575
theorem B2735945 : Blo 1823613 2735945 := bstep (se 2 (by rfl) ⟨1025979, by rfl⟩ : syracuseStep 2735945 = 2051959) B2051959
theorem B9232217 : Blo 1823613 9232217 := bstep (se 2 (by rfl) ⟨3462081, by rfl⟩ : syracuseStep 9232217 = 6924163) B6924163
theorem B4104071 : Blo 1823613 4104071 := bstep (se 1 (by rfl) ⟨3078053, by rfl⟩ : syracuseStep 4104071 = 6156107) B6156107
theorem B4620179 : Blo 1823613 4620179 := bstep (se 1 (by rfl) ⟨3465134, by rfl⟩ : syracuseStep 4620179 = 6930269) B6930269
theorem B7790489 : Blo 1823613 7790489 := bstep (se 2 (by rfl) ⟨2921433, by rfl⟩ : syracuseStep 7790489 = 5842867) B5842867
theorem B2310059 : Blo 1823613 2310059 := bstep (se 1 (by rfl) ⟨1732544, by rfl⟩ : syracuseStep 2310059 = 3465089) B3465089
theorem B10387385 : Blo 1823613 10387385 := bstep (se 2 (by rfl) ⟨3895269, by rfl⟩ : syracuseStep 10387385 = 7790539) B7790539
theorem B2736059 : Blo 1823613 2736059 := bstep (se 1 (by rfl) ⟨2052044, by rfl⟩ : syracuseStep 2736059 = 4104089) B4104089
theorem B2736119 : Blo 1823613 2736119 := bstep (se 1 (by rfl) ⟨2052089, by rfl⟩ : syracuseStep 2736119 = 4104179) B4104179
theorem B2736137 : Blo 1823613 2736137 := bstep (se 2 (by rfl) ⟨1026051, by rfl⟩ : syracuseStep 2736137 = 2052103) B2052103
theorem B14229533 : Blo 1823613 14229533 := bstep (se 3 (by rfl) ⟨2668037, by rfl⟩ : syracuseStep 14229533 = 5336075) B5336075
theorem B2736167 : Blo 1823613 2736167 := bstep (se 1 (by rfl) ⟨2052125, by rfl⟩ : syracuseStep 2736167 = 4104251) B4104251
theorem B2498639 : Blo 1823613 2498639 := bstep (se 1 (by rfl) ⟨1873979, by rfl⟩ : syracuseStep 2498639 = 3747959) B3747959
theorem B2736251 : Blo 1823613 2736251 := bstep (se 1 (by rfl) ⟨2052188, by rfl⟩ : syracuseStep 2736251 = 4104377) B4104377
theorem B3080315 : Blo 1823613 3080315 := bstep (se 1 (by rfl) ⟨2310236, by rfl⟩ : syracuseStep 3080315 = 4620473) B4620473
theorem B9232541 : Blo 1823613 9232541 := bstep (se 3 (by rfl) ⟨1731101, by rfl⟩ : syracuseStep 9232541 = 3462203) B3462203
theorem B6578371 : Blo 1823613 6578371 := bstep (se 1 (by rfl) ⟨4933778, by rfl⟩ : syracuseStep 6578371 = 9867557) B9867557
theorem B2736377 : Blo 1823613 2736377 := bstep (se 2 (by rfl) ⟨1026141, by rfl⟩ : syracuseStep 2736377 = 2052283) B2052283
theorem B2736479 : Blo 1823613 2736479 := bstep (se 1 (by rfl) ⟨2052359, by rfl⟩ : syracuseStep 2736479 = 4104719) B4104719
theorem B2736491 : Blo 1823613 2736491 := bstep (se 1 (by rfl) ⟨2052368, by rfl⟩ : syracuseStep 2736491 = 4104737) B4104737
theorem B14631301 : Blo 1823613 14631301 := bstep (se 4 (by rfl) ⟨1371684, by rfl⟩ : syracuseStep 14631301 = 2743369) B2743369
theorem B3465659 : Blo 1823613 3465659 := bstep (se 1 (by rfl) ⟨2599244, by rfl⟩ : syracuseStep 3465659 = 5198489) B5198489
theorem B6160859 : Blo 1823613 6160859 := bstep (se 1 (by rfl) ⟨4620644, by rfl⟩ : syracuseStep 6160859 = 9241289) B9241289
theorem B6930953 : Blo 1823613 6930953 := bstep (se 2 (by rfl) ⟨2599107, by rfl⟩ : syracuseStep 6930953 = 5198215) B5198215
theorem B3080713 : Blo 1823613 3080713 := bstep (se 2 (by rfl) ⟨1155267, by rfl⟩ : syracuseStep 3080713 = 2310535) B2310535
theorem B2736719 : Blo 1823613 2736719 := bstep (se 1 (by rfl) ⟨2052539, by rfl⟩ : syracuseStep 2736719 = 4105079) B4105079
theorem B4104827 : Blo 1823613 4104827 := bstep (se 1 (by rfl) ⟨3078620, by rfl⟩ : syracuseStep 4104827 = 6157241) B6157241
theorem B20783789 : Blo 1823613 20783789 := bstep (se 3 (by rfl) ⟨3896960, by rfl⟩ : syracuseStep 20783789 = 7793921) B7793921
theorem B2736839 : Blo 1823613 2736839 := bstep (se 1 (by rfl) ⟨2052629, by rfl⟩ : syracuseStep 2736839 = 4105259) B4105259
theorem B14795465 : Blo 1823613 14795465 := bstep (se 2 (by rfl) ⟨5548299, by rfl⟩ : syracuseStep 14795465 = 11096599) B11096599
theorem B4104953 : Blo 1823613 4104953 := bstep (se 2 (by rfl) ⟨1539357, by rfl⟩ : syracuseStep 4104953 = 3078715) B3078715
theorem B2737001 : Blo 1823613 2737001 := bstep (se 2 (by rfl) ⟨1026375, by rfl⟩ : syracuseStep 2737001 = 2052751) B2052751
theorem B9241451 : Blo 1823613 9241451 := bstep (se 1 (by rfl) ⟨6931088, by rfl⟩ : syracuseStep 9241451 = 13862177) B13862177
theorem B4219823 : Blo 1823613 4219823 := bstep (se 1 (by rfl) ⟨3164867, by rfl⟩ : syracuseStep 4219823 = 6329735) B6329735
theorem B2737079 : Blo 1823613 2737079 := bstep (se 1 (by rfl) ⟨2052809, by rfl⟩ : syracuseStep 2737079 = 4105619) B4105619
theorem B2737115 : Blo 1823613 2737115 := bstep (se 1 (by rfl) ⟨2052836, by rfl⟩ : syracuseStep 2737115 = 4105673) B4105673
theorem B4105223 : Blo 1823613 4105223 := bstep (se 1 (by rfl) ⟨3078917, by rfl⟩ : syracuseStep 4105223 = 6157835) B6157835
theorem B1827919 : Blo 1823613 1827919 := bstep (se 1 (by rfl) ⟨1370939, by rfl⟩ : syracuseStep 1827919 = 2741879) B2741879
theorem B4105295 : Blo 1823613 4105295 := bstep (se 1 (by rfl) ⟨3078971, by rfl⟩ : syracuseStep 4105295 = 6157943) B6157943
theorem B6243481 : Blo 1823613 6243481 := bstep (se 2 (by rfl) ⟨2341305, by rfl⟩ : syracuseStep 6243481 = 4682611) B4682611
theorem B20792537 : Blo 1823613 20792537 := bstep (se 2 (by rfl) ⟨7797201, by rfl⟩ : syracuseStep 20792537 = 15594403) B15594403
theorem B6243713 : Blo 1823613 6243713 := bstep (se 2 (by rfl) ⟨2341392, by rfl⟩ : syracuseStep 6243713 = 4682785) B4682785
theorem B9233837 : Blo 1823613 9233837 := bstep (se 3 (by rfl) ⟨1731344, by rfl⟩ : syracuseStep 9233837 = 3462689) B3462689
theorem B2737583 : Blo 1823613 2737583 := bstep (se 1 (by rfl) ⟨2053187, by rfl⟩ : syracuseStep 2737583 = 4106375) B4106375
theorem B4105691 : Blo 1823613 4105691 := bstep (se 1 (by rfl) ⟨3079268, by rfl⟩ : syracuseStep 4105691 = 6158537) B6158537
theorem B9242099 : Blo 1823613 9242099 := bstep (se 1 (by rfl) ⟨6931574, by rfl⟩ : syracuseStep 9242099 = 13863149) B13863149
theorem B35563013 : Blo 1823613 35563013 := bstep (se 4 (by rfl) ⟨3334032, by rfl⟩ : syracuseStep 35563013 = 6668065) B6668065
theorem B2737673 : Blo 1823613 2737673 := bstep (se 2 (by rfl) ⟨1026627, by rfl⟩ : syracuseStep 2737673 = 2053255) B2053255
theorem B2737703 : Blo 1823613 2737703 := bstep (se 1 (by rfl) ⟨2053277, by rfl⟩ : syracuseStep 2737703 = 4106555) B4106555
theorem B2737787 : Blo 1823613 2737787 := bstep (se 1 (by rfl) ⟨2053340, by rfl⟩ : syracuseStep 2737787 = 4106681) B4106681
theorem B4384505 : Blo 1823613 4384505 := bstep (se 2 (by rfl) ⟨1644189, by rfl⟩ : syracuseStep 4384505 = 3288379) B3288379
theorem B2737913 : Blo 1823613 2737913 := bstep (se 2 (by rfl) ⟨1026717, by rfl⟩ : syracuseStep 2737913 = 2053435) B2053435
theorem B10389343 : Blo 1823613 10389343 := bstep (se 1 (by rfl) ⟨7792007, by rfl⟩ : syracuseStep 10389343 = 15584015) B15584015
theorem B2738015 : Blo 1823613 2738015 := bstep (se 1 (by rfl) ⟨2053511, by rfl⟩ : syracuseStep 2738015 = 4107023) B4107023
theorem B2738027 : Blo 1823613 2738027 := bstep (se 1 (by rfl) ⟨2053520, by rfl⟩ : syracuseStep 2738027 = 4107041) B4107041
theorem B4106159 : Blo 1823613 4106159 := bstep (se 1 (by rfl) ⟨3079619, by rfl⟩ : syracuseStep 4106159 = 6159239) B6159239
theorem B9865223 : Blo 1823613 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B2738255 : Blo 1823613 2738255 := bstep (se 1 (by rfl) ⟨2053691, by rfl⟩ : syracuseStep 2738255 = 4107383) B4107383
theorem B4106411 : Blo 1823613 4106411 := bstep (se 1 (by rfl) ⟨3079808, by rfl⟩ : syracuseStep 4106411 = 6159617) B6159617
theorem B2738375 : Blo 1823613 2738375 := bstep (se 1 (by rfl) ⟨2053781, by rfl⟩ : syracuseStep 2738375 = 4107563) B4107563
theorem B3287369 : Blo 1823613 3287369 := bstep (se 2 (by rfl) ⟨1232763, by rfl⟩ : syracuseStep 3287369 = 2465527) B2465527
theorem B6924649 : Blo 1823613 6924649 := bstep (se 2 (by rfl) ⟨2596743, by rfl⟩ : syracuseStep 6924649 = 5193487) B5193487
theorem B6572431 : Blo 1823613 6572431 := bstep (se 1 (by rfl) ⟨4929323, by rfl⟩ : syracuseStep 6572431 = 9858647) B9858647
theorem B13158935 : Blo 1823613 13158935 := bstep (se 1 (by rfl) ⟨9869201, by rfl⟩ : syracuseStep 13158935 = 19738403) B19738403
theorem B6154811 : Blo 1823613 6154811 := bstep (se 1 (by rfl) ⟨4616108, by rfl⟩ : syracuseStep 6154811 = 9232217) B9232217
theorem B6924923 : Blo 1823613 6924923 := bstep (se 1 (by rfl) ⟨5193692, by rfl⟩ : syracuseStep 6924923 = 10387385) B10387385
theorem B24955577 : Blo 1823613 24955577 := bstep (se 2 (by rfl) ⟨9358341, by rfl⟩ : syracuseStep 24955577 = 18716683) B18716683
theorem B4106951 : Blo 1823613 4106951 := bstep (se 1 (by rfl) ⟨3080213, by rfl⟩ : syracuseStep 4106951 = 6160427) B6160427
theorem B10390301 : Blo 1823613 10390301 := bstep (se 3 (by rfl) ⟨1948181, by rfl⟩ : syracuseStep 10390301 = 3896363) B3896363
theorem B6155081 : Blo 1823613 6155081 := bstep (se 2 (by rfl) ⟨2308155, by rfl⟩ : syracuseStep 6155081 = 4616311) B4616311
theorem B3697481 : Blo 1823613 3697481 := bstep (se 2 (by rfl) ⟨1386555, by rfl⟩ : syracuseStep 3697481 = 2773111) B2773111
theorem B20777957 : Blo 1823613 20777957 := bstep (se 4 (by rfl) ⟨1947933, by rfl⟩ : syracuseStep 20777957 = 3895867) B3895867
theorem B9235457 : Blo 1823613 9235457 := bstep (se 2 (by rfl) ⟨3463296, by rfl⟩ : syracuseStep 9235457 = 6926593) B6926593
theorem B3288235 : Blo 1823613 3288235 := bstep (se 1 (by rfl) ⟨2466176, by rfl⟩ : syracuseStep 3288235 = 4932353) B4932353
theorem B33295859 : Blo 1823613 33295859 := bstep (se 1 (by rfl) ⟨24971894, by rfl⟩ : syracuseStep 33295859 = 49943789) B49943789
theorem B3288595 : Blo 1823613 3288595 := bstep (se 1 (by rfl) ⟨2466446, by rfl⟩ : syracuseStep 3288595 = 4932893) B4932893
theorem B11095649 : Blo 1823613 11095649 := bstep (se 2 (by rfl) ⟨4160868, by rfl⟩ : syracuseStep 11095649 = 8321737) B8321737
theorem B2051707 : Blo 1823613 2051707 := bstep (se 1 (by rfl) ⟨1538780, by rfl⟩ : syracuseStep 2051707 = 3077561) B3077561
theorem B13332157 : Blo 1823613 13332157 := bstep (se 3 (by rfl) ⟨2499779, by rfl⟩ : syracuseStep 13332157 = 4999559) B4999559
theorem B9236267 : Blo 1823613 9236267 := bstep (se 1 (by rfl) ⟨6927200, by rfl⟩ : syracuseStep 9236267 = 13854401) B13854401
theorem B6156215 : Blo 1823613 6156215 := bstep (se 1 (by rfl) ⟨4617161, by rfl⟩ : syracuseStep 6156215 = 9234323) B9234323
theorem B2052175 : Blo 1823613 2052175 := bstep (se 1 (by rfl) ⟨1539131, by rfl⟩ : syracuseStep 2052175 = 3078263) B3078263
theorem B10530905 : Blo 1823613 10530905 := bstep (se 2 (by rfl) ⟨3949089, by rfl⟩ : syracuseStep 10530905 = 7898179) B7898179
theorem B84275315 : Blo 1823613 84275315 := bstep (se 1 (by rfl) ⟨63206486, by rfl⟩ : syracuseStep 84275315 = 126412973) B126412973
theorem B3895543 : Blo 1823613 3895543 := bstep (se 1 (by rfl) ⟨2921657, by rfl⟩ : syracuseStep 3895543 = 5843315) B5843315
theorem B19730749 : Blo 1823613 19730749 := bstep (se 3 (by rfl) ⟨3699515, by rfl⟩ : syracuseStep 19730749 = 7399031) B7399031
theorem B5845391 : Blo 1823613 5845391 := bstep (se 1 (by rfl) ⟨4384043, by rfl⟩ : syracuseStep 5845391 = 8768087) B8768087
theorem B2052571 : Blo 1823613 2052571 := bstep (se 1 (by rfl) ⟨1539428, by rfl⟩ : syracuseStep 2052571 = 3078857) B3078857
theorem B6156809 : Blo 1823613 6156809 := bstep (se 2 (by rfl) ⟨2308803, by rfl⟩ : syracuseStep 6156809 = 4617607) B4617607
theorem B6574841 : Blo 1823613 6574841 := bstep (se 2 (by rfl) ⟨2465565, by rfl⟩ : syracuseStep 6574841 = 4931131) B4931131
theorem B26301257 : Blo 1823613 26301257 := bstep (se 2 (by rfl) ⟨9862971, by rfl⟩ : syracuseStep 26301257 = 19725943) B19725943
theorem B4617121 : Blo 1823613 4617121 := bstep (se 2 (by rfl) ⟨1731420, by rfl⟩ : syracuseStep 4617121 = 3462841) B3462841
theorem B1823663 : Blo 1823613 1823663 := bstep (se 1 (by rfl) ⟨1367747, by rfl⟩ : syracuseStep 1823663 = 2735495) B2735495
theorem B2053039 : Blo 1823613 2053039 := bstep (se 1 (by rfl) ⟨1539779, by rfl⟩ : syracuseStep 2053039 = 3079559) B3079559
theorem B1823687 : Blo 1823613 1823687 := bstep (se 1 (by rfl) ⟨1367765, by rfl⟩ : syracuseStep 1823687 = 2735531) B2735531
theorem B1823707 : Blo 1823613 1823707 := bstep (se 1 (by rfl) ⟨1367780, by rfl⟩ : syracuseStep 1823707 = 2735561) B2735561
theorem B23393245 : Blo 1823613 23393245 := bstep (se 3 (by rfl) ⟨4386233, by rfl⟩ : syracuseStep 23393245 = 8772467) B8772467
theorem B1823783 : Blo 1823613 1823783 := bstep (se 1 (by rfl) ⟨1367837, by rfl⟩ : syracuseStep 1823783 = 2735675) B2735675
theorem B3699751 : Blo 1823613 3699751 := bstep (se 1 (by rfl) ⟨2774813, by rfl⟩ : syracuseStep 3699751 = 5549627) B5549627
theorem B11686963 : Blo 1823613 11686963 := bstep (se 1 (by rfl) ⟨8765222, by rfl⟩ : syracuseStep 11686963 = 17530445) B17530445
theorem B1823823 : Blo 1823613 1823823 := bstep (se 1 (by rfl) ⟨1367867, by rfl⟩ : syracuseStep 1823823 = 2735735) B2735735
theorem B5551183 : Blo 1823613 5551183 := bstep (se 1 (by rfl) ⟨4163387, by rfl⟩ : syracuseStep 5551183 = 8326775) B8326775
theorem B1823839 : Blo 1823613 1823839 := bstep (se 1 (by rfl) ⟨1367879, by rfl⟩ : syracuseStep 1823839 = 2735759) B2735759
theorem B1823867 : Blo 1823613 1823867 := bstep (se 1 (by rfl) ⟨1367900, by rfl⟩ : syracuseStep 1823867 = 2735801) B2735801
theorem B1823919 : Blo 1823613 1823919 := bstep (se 1 (by rfl) ⟨1367939, by rfl⟩ : syracuseStep 1823919 = 2735879) B2735879
theorem B1823943 : Blo 1823613 1823943 := bstep (se 1 (by rfl) ⟨1367957, by rfl⟩ : syracuseStep 1823943 = 2735915) B2735915
theorem B3462355 : Blo 1823613 3462355 := bstep (se 1 (by rfl) ⟨2596766, by rfl⟩ : syracuseStep 3462355 = 5193533) B5193533
theorem B1823963 : Blo 1823613 1823963 := bstep (se 1 (by rfl) ⟨1367972, by rfl⟩ : syracuseStep 1823963 = 2735945) B2735945
theorem B1824039 : Blo 1823613 1824039 := bstep (se 1 (by rfl) ⟨1368029, by rfl⟩ : syracuseStep 1824039 = 2736059) B2736059
theorem B1848655 : Blo 1823613 1848655 := bstep (se 1 (by rfl) ⟨1386491, by rfl⟩ : syracuseStep 1848655 = 2772983) B2772983
theorem B1824079 : Blo 1823613 1824079 := bstep (se 1 (by rfl) ⟨1368059, by rfl⟩ : syracuseStep 1824079 = 2736119) B2736119
theorem B1824095 : Blo 1823613 1824095 := bstep (se 1 (by rfl) ⟨1368071, by rfl⟩ : syracuseStep 1824095 = 2736143) B2736143
theorem B2053471 : Blo 1823613 2053471 := bstep (se 1 (by rfl) ⟨1540103, by rfl⟩ : syracuseStep 2053471 = 3080207) B3080207
theorem B6157673 : Blo 1823613 6157673 := bstep (se 2 (by rfl) ⟨2309127, by rfl⟩ : syracuseStep 6157673 = 4618255) B4618255
theorem B1824123 : Blo 1823613 1824123 := bstep (se 1 (by rfl) ⟨1368092, by rfl⟩ : syracuseStep 1824123 = 2736185) B2736185
theorem B6575489 : Blo 1823613 6575489 := bstep (se 2 (by rfl) ⟨2465808, by rfl⟩ : syracuseStep 6575489 = 4931617) B4931617
theorem B22500773 : Blo 1823613 22500773 := bstep (se 4 (by rfl) ⟨2109447, by rfl⟩ : syracuseStep 22500773 = 4218895) B4218895
theorem B1824175 : Blo 1823613 1824175 := bstep (se 1 (by rfl) ⟨1368131, by rfl⟩ : syracuseStep 1824175 = 2736263) B2736263
theorem B3462583 : Blo 1823613 3462583 := bstep (se 1 (by rfl) ⟨2596937, by rfl⟩ : syracuseStep 3462583 = 5193875) B5193875
theorem B1824199 : Blo 1823613 1824199 := bstep (se 1 (by rfl) ⟨1368149, by rfl⟩ : syracuseStep 1824199 = 2736299) B2736299
theorem B1824219 : Blo 1823613 1824219 := bstep (se 1 (by rfl) ⟨1368164, by rfl⟩ : syracuseStep 1824219 = 2736329) B2736329
theorem B1824295 : Blo 1823613 1824295 := bstep (se 1 (by rfl) ⟨1368221, by rfl⟩ : syracuseStep 1824295 = 2736443) B2736443
theorem B2192935 : Blo 1823613 2192935 := bstep (se 1 (by rfl) ⟨1644701, by rfl⟩ : syracuseStep 2192935 = 3289403) B3289403
theorem B3077689 : Blo 1823613 3077689 := bstep (se 2 (by rfl) ⟨1154133, by rfl⟩ : syracuseStep 3077689 = 2308267) B2308267
theorem B1824335 : Blo 1823613 1824335 := bstep (se 1 (by rfl) ⟨1368251, by rfl⟩ : syracuseStep 1824335 = 2736503) B2736503
theorem B1824351 : Blo 1823613 1824351 := bstep (se 1 (by rfl) ⟨1368263, by rfl⟩ : syracuseStep 1824351 = 2736527) B2736527
theorem B5264993 : Blo 1823613 5264993 := bstep (se 2 (by rfl) ⟨1974372, by rfl⟩ : syracuseStep 5264993 = 3948745) B3948745
theorem B1824379 : Blo 1823613 1824379 := bstep (se 1 (by rfl) ⟨1368284, by rfl⟩ : syracuseStep 1824379 = 2736569) B2736569
theorem B12490379 : Blo 1823613 12490379 := bstep (se 1 (by rfl) ⟨9367784, by rfl⟩ : syracuseStep 12490379 = 18735569) B18735569
theorem B1824431 : Blo 1823613 1824431 := bstep (se 1 (by rfl) ⟨1368323, by rfl⟩ : syracuseStep 1824431 = 2736647) B2736647
theorem B3077831 : Blo 1823613 3077831 := bstep (se 1 (by rfl) ⟨2308373, by rfl⟩ : syracuseStep 3077831 = 4616747) B4616747
theorem B1824455 : Blo 1823613 1824455 := bstep (se 1 (by rfl) ⟨1368341, by rfl⟩ : syracuseStep 1824455 = 2736683) B2736683
theorem B4216531 : Blo 1823613 4216531 := bstep (se 1 (by rfl) ⟨3162398, by rfl⟩ : syracuseStep 4216531 = 6324797) B6324797
theorem B1824475 : Blo 1823613 1824475 := bstep (se 1 (by rfl) ⟨1368356, by rfl⟩ : syracuseStep 1824475 = 2736713) B2736713
theorem B1824551 : Blo 1823613 1824551 := bstep (se 1 (by rfl) ⟨1368413, by rfl⟩ : syracuseStep 1824551 = 2736827) B2736827
theorem B1824591 : Blo 1823613 1824591 := bstep (se 1 (by rfl) ⟨1368443, by rfl⟩ : syracuseStep 1824591 = 2736887) B2736887
theorem B1824607 : Blo 1823613 1824607 := bstep (se 1 (by rfl) ⟨1368455, by rfl⟩ : syracuseStep 1824607 = 2736911) B2736911
theorem B3077993 : Blo 1823613 3077993 := bstep (se 2 (by rfl) ⟨1154247, by rfl⟩ : syracuseStep 3077993 = 2308495) B2308495
theorem B1824635 : Blo 1823613 1824635 := bstep (se 1 (by rfl) ⟨1368476, by rfl⟩ : syracuseStep 1824635 = 2736953) B2736953
theorem B1824687 : Blo 1823613 1824687 := bstep (se 1 (by rfl) ⟨1368515, by rfl⟩ : syracuseStep 1824687 = 2737031) B2737031
theorem B12490681 : Blo 1823613 12490681 := bstep (se 2 (by rfl) ⟨4684005, by rfl⟩ : syracuseStep 12490681 = 9368011) B9368011
theorem B6158267 : Blo 1823613 6158267 := bstep (se 1 (by rfl) ⟨4618700, by rfl⟩ : syracuseStep 6158267 = 9237401) B9237401
theorem B1824711 : Blo 1823613 1824711 := bstep (se 1 (by rfl) ⟨1368533, by rfl⟩ : syracuseStep 1824711 = 2737067) B2737067
theorem B1824731 : Blo 1823613 1824731 := bstep (se 1 (by rfl) ⟨1368548, by rfl⟩ : syracuseStep 1824731 = 2737097) B2737097
theorem B91248611 : Blo 1823613 91248611 := bstep (se 1 (by rfl) ⟨68436458, by rfl⟩ : syracuseStep 91248611 = 136872917) B136872917
theorem B3463175 : Blo 1823613 3463175 := bstep (se 1 (by rfl) ⟨2597381, by rfl⟩ : syracuseStep 3463175 = 5194763) B5194763
theorem B9238535 : Blo 1823613 9238535 := bstep (se 1 (by rfl) ⟨6928901, by rfl⟩ : syracuseStep 9238535 = 13857803) B13857803
theorem B19732517 : Blo 1823613 19732517 := bstep (se 4 (by rfl) ⟨1849923, by rfl⟩ : syracuseStep 19732517 = 3699847) B3699847
theorem B1824807 : Blo 1823613 1824807 := bstep (se 1 (by rfl) ⟨1368605, by rfl⟩ : syracuseStep 1824807 = 2737211) B2737211
theorem B151820345 : Blo 1823613 151820345 := bstep (se 2 (by rfl) ⟨56932629, by rfl⟩ : syracuseStep 151820345 = 113865259) B113865259
theorem B1824847 : Blo 1823613 1824847 := bstep (se 1 (by rfl) ⟨1368635, by rfl⟩ : syracuseStep 1824847 = 2737271) B2737271
theorem B1824863 : Blo 1823613 1824863 := bstep (se 1 (by rfl) ⟨1368647, by rfl⟩ : syracuseStep 1824863 = 2737295) B2737295
theorem B1824891 : Blo 1823613 1824891 := bstep (se 1 (by rfl) ⟨1368668, by rfl⟩ : syracuseStep 1824891 = 2737337) B2737337
theorem B6928537 : Blo 1823613 6928537 := bstep (se 2 (by rfl) ⟨2598201, by rfl⟩ : syracuseStep 6928537 = 5196403) B5196403
theorem B1824943 : Blo 1823613 1824943 := bstep (se 1 (by rfl) ⟨1368707, by rfl⟩ : syracuseStep 1824943 = 2737415) B2737415
theorem B1824967 : Blo 1823613 1824967 := bstep (se 1 (by rfl) ⟨1368725, by rfl⟩ : syracuseStep 1824967 = 2737451) B2737451
theorem B1824987 : Blo 1823613 1824987 := bstep (se 1 (by rfl) ⟨1368740, by rfl⟩ : syracuseStep 1824987 = 2737481) B2737481
theorem B3078391 : Blo 1823613 3078391 := bstep (se 1 (by rfl) ⟨2308793, by rfl⟩ : syracuseStep 3078391 = 4617587) B4617587
theorem B1825063 : Blo 1823613 1825063 := bstep (se 1 (by rfl) ⟨1368797, by rfl⟩ : syracuseStep 1825063 = 2737595) B2737595
theorem B1825103 : Blo 1823613 1825103 := bstep (se 1 (by rfl) ⟨1368827, by rfl⟩ : syracuseStep 1825103 = 2737655) B2737655
theorem B11696471 : Blo 1823613 11696471 := bstep (se 1 (by rfl) ⟨8772353, by rfl⟩ : syracuseStep 11696471 = 17544707) B17544707
theorem B1825119 : Blo 1823613 1825119 := bstep (se 1 (by rfl) ⟨1368839, by rfl⟩ : syracuseStep 1825119 = 2737679) B2737679
theorem B4159849 : Blo 1823613 4159849 := bstep (se 2 (by rfl) ⟨1559943, by rfl⟩ : syracuseStep 4159849 = 3119887) B3119887
theorem B1825147 : Blo 1823613 1825147 := bstep (se 1 (by rfl) ⟨1368860, by rfl⟩ : syracuseStep 1825147 = 2737721) B2737721
theorem B34199941 : Blo 1823613 34199941 := bstep (se 4 (by rfl) ⟨3206244, by rfl⟩ : syracuseStep 34199941 = 6412489) B6412489
theorem B1825199 : Blo 1823613 1825199 := bstep (se 1 (by rfl) ⟨1368899, by rfl⟩ : syracuseStep 1825199 = 2737799) B2737799
theorem B3078587 : Blo 1823613 3078587 := bstep (se 1 (by rfl) ⟨2308940, by rfl⟩ : syracuseStep 3078587 = 4617881) B4617881
theorem B1825223 : Blo 1823613 1825223 := bstep (se 1 (by rfl) ⟨1368917, by rfl⟩ : syracuseStep 1825223 = 2737835) B2737835
theorem B6928841 : Blo 1823613 6928841 := bstep (se 2 (by rfl) ⟨2598315, by rfl⟩ : syracuseStep 6928841 = 5196631) B5196631
theorem B2922971 : Blo 1823613 2922971 := bstep (se 1 (by rfl) ⟨2192228, by rfl⟩ : syracuseStep 2922971 = 4384457) B4384457
theorem B1825243 : Blo 1823613 1825243 := bstep (se 1 (by rfl) ⟨1368932, by rfl⟩ : syracuseStep 1825243 = 2737865) B2737865
theorem B9239021 : Blo 1823613 9239021 := bstep (se 3 (by rfl) ⟨1732316, by rfl⟩ : syracuseStep 9239021 = 3464633) B3464633
theorem B3078695 : Blo 1823613 3078695 := bstep (se 1 (by rfl) ⟨2309021, by rfl⟩ : syracuseStep 3078695 = 4618043) B4618043
theorem B1825319 : Blo 1823613 1825319 := bstep (se 1 (by rfl) ⟨1368989, by rfl⟩ : syracuseStep 1825319 = 2737979) B2737979
theorem B38468171 : Blo 1823613 38468171 := bstep (se 1 (by rfl) ⟨28851128, by rfl⟩ : syracuseStep 38468171 = 57702257) B57702257
theorem B3332687 : Blo 1823613 3332687 := bstep (se 1 (by rfl) ⟨2499515, by rfl⟩ : syracuseStep 3332687 = 4999031) B4999031
theorem B1825359 : Blo 1823613 1825359 := bstep (se 1 (by rfl) ⟨1369019, by rfl⟩ : syracuseStep 1825359 = 2738039) B2738039
theorem B1825375 : Blo 1823613 1825375 := bstep (se 1 (by rfl) ⟨1369031, by rfl⟩ : syracuseStep 1825375 = 2738063) B2738063
theorem B1825403 : Blo 1823613 1825403 := bstep (se 1 (by rfl) ⟨1369052, by rfl⟩ : syracuseStep 1825403 = 2738105) B2738105
theorem B1825455 : Blo 1823613 1825455 := bstep (se 1 (by rfl) ⟨1369091, by rfl⟩ : syracuseStep 1825455 = 2738183) B2738183
theorem B1825479 : Blo 1823613 1825479 := bstep (se 1 (by rfl) ⟨1369109, by rfl⟩ : syracuseStep 1825479 = 2738219) B2738219
theorem B1825499 : Blo 1823613 1825499 := bstep (se 1 (by rfl) ⟨1369124, by rfl⟩ : syracuseStep 1825499 = 2738249) B2738249
theorem B1825575 : Blo 1823613 1825575 := bstep (se 1 (by rfl) ⟨1369181, by rfl⟩ : syracuseStep 1825575 = 2738363) B2738363
theorem B5847851 : Blo 1823613 5847851 := bstep (se 1 (by rfl) ⟨4385888, by rfl⟩ : syracuseStep 5847851 = 8771777) B8771777
theorem B3078985 : Blo 1823613 3078985 := bstep (se 2 (by rfl) ⟨1154619, by rfl⟩ : syracuseStep 3078985 = 2309239) B2309239
theorem B3464041 : Blo 1823613 3464041 := bstep (se 2 (by rfl) ⟨1299015, by rfl⟩ : syracuseStep 3464041 = 2598031) B2598031
theorem B3079019 : Blo 1823613 3079019 := bstep (se 1 (by rfl) ⟨2309264, by rfl⟩ : syracuseStep 3079019 = 4618529) B4618529
theorem B6929327 : Blo 1823613 6929327 := bstep (se 1 (by rfl) ⟨5196995, by rfl⟩ : syracuseStep 6929327 = 10393991) B10393991
theorem B5626799 : Blo 1823613 5626799 := bstep (se 1 (by rfl) ⟨4220099, by rfl⟩ : syracuseStep 5626799 = 8440199) B8440199
theorem B3464201 : Blo 1823613 3464201 := bstep (se 2 (by rfl) ⟨1299075, by rfl⟩ : syracuseStep 3464201 = 2598151) B2598151
theorem B10394675 : Blo 1823613 10394675 := bstep (se 1 (by rfl) ⟨7796006, by rfl⟩ : syracuseStep 10394675 = 15592013) B15592013
theorem B4103225 : Blo 1823613 4103225 := bstep (se 2 (by rfl) ⟨1538709, by rfl⟩ : syracuseStep 4103225 = 3077419) B3077419
theorem B21060803 : Blo 1823613 21060803 := bstep (se 1 (by rfl) ⟨15795602, by rfl⟩ : syracuseStep 21060803 = 31591205) B31591205
theorem B24968387 : Blo 1823613 24968387 := bstep (se 1 (by rfl) ⟨18726290, by rfl⟩ : syracuseStep 24968387 = 37452581) B37452581
theorem B3079417 : Blo 1823613 3079417 := bstep (se 2 (by rfl) ⟨1154781, by rfl⟩ : syracuseStep 3079417 = 2309563) B2309563
theorem B9239831 : Blo 1823613 9239831 := bstep (se 1 (by rfl) ⟨6929873, by rfl⟩ : syracuseStep 9239831 = 13859747) B13859747
theorem B2735465 : Blo 1823613 2735465 := bstep (se 2 (by rfl) ⟨1025799, by rfl⟩ : syracuseStep 2735465 = 2051599) B2051599
theorem B6241661 : Blo 1823613 6241661 := bstep (se 3 (by rfl) ⟨1170311, by rfl⟩ : syracuseStep 6241661 = 2340623) B2340623
theorem B4103567 : Blo 1823613 4103567 := bstep (se 1 (by rfl) ⟨3077675, by rfl⟩ : syracuseStep 4103567 = 6155351) B6155351
theorem B4619663 : Blo 1823613 4619663 := bstep (se 1 (by rfl) ⟨3464747, by rfl⟩ : syracuseStep 4619663 = 6929495) B6929495
theorem B2735543 : Blo 1823613 2735543 := bstep (se 1 (by rfl) ⟨2051657, by rfl⟩ : syracuseStep 2735543 = 4103315) B4103315
theorem B2735579 : Blo 1823613 2735579 := bstep (se 1 (by rfl) ⟨2051684, by rfl⟩ : syracuseStep 2735579 = 4103369) B4103369
theorem B3079687 : Blo 1823613 3079687 := bstep (se 1 (by rfl) ⟨2309765, by rfl⟩ : syracuseStep 3079687 = 4619531) B4619531
theorem B10395175 : Blo 1823613 10395175 := bstep (se 1 (by rfl) ⟨7796381, by rfl⟩ : syracuseStep 10395175 = 15592763) B15592763
theorem B6159995 : Blo 1823613 6159995 := bstep (se 1 (by rfl) ⟨4619996, by rfl⟩ : syracuseStep 6159995 = 9239993) B9239993
theorem B4103891 : Blo 1823613 4103891 := bstep (se 1 (by rfl) ⟨3077918, by rfl⟩ : syracuseStep 4103891 = 6155837) B6155837
theorem B4619987 : Blo 1823613 4619987 := bstep (se 1 (by rfl) ⟨3464990, by rfl⟩ : syracuseStep 4619987 = 6929981) B6929981
theorem B6160157 : Blo 1823613 6160157 := bstep (se 3 (by rfl) ⟨1155029, by rfl⟩ : syracuseStep 6160157 = 2310059) B2310059
theorem B2736047 : Blo 1823613 2736047 := bstep (se 1 (by rfl) ⟨2052035, by rfl⟩ : syracuseStep 2736047 = 4104071) B4104071
theorem B3080119 : Blo 1823613 3080119 := bstep (se 1 (by rfl) ⟨2310089, by rfl⟩ : syracuseStep 3080119 = 4620179) B4620179
theorem B5193659 : Blo 1823613 5193659 := bstep (se 1 (by rfl) ⟨3895244, by rfl⟩ : syracuseStep 5193659 = 7790489) B7790489
theorem B37945421 : Blo 1823613 37945421 := bstep (se 3 (by rfl) ⟨7114766, by rfl⟩ : syracuseStep 37945421 = 14229533) B14229533
theorem B2736233 : Blo 1823613 2736233 := bstep (se 2 (by rfl) ⟨1026087, by rfl⟩ : syracuseStep 2736233 = 2052175) B2052175
theorem B28082413 : Blo 1823613 28082413 := bstep (se 3 (by rfl) ⟨5265452, by rfl⟩ : syracuseStep 28082413 = 10530905) B10530905
theorem B2310439 : Blo 1823613 2310439 := bstep (se 1 (by rfl) ⟨1732829, by rfl⟩ : syracuseStep 2310439 = 3465659) B3465659
theorem B5194057 : Blo 1823613 5194057 := bstep (se 2 (by rfl) ⟨1947771, by rfl⟩ : syracuseStep 5194057 = 3895543) B3895543
theorem B4104521 : Blo 1823613 4104521 := bstep (se 2 (by rfl) ⟨1539195, by rfl⟩ : syracuseStep 4104521 = 3078391) B3078391
theorem B4104539 : Blo 1823613 4104539 := bstep (se 1 (by rfl) ⟨3078404, by rfl⟩ : syracuseStep 4104539 = 6156809) B6156809
theorem B4620635 : Blo 1823613 4620635 := bstep (se 1 (by rfl) ⟨3465476, by rfl⟩ : syracuseStep 4620635 = 6930953) B6930953
theorem B2736551 : Blo 1823613 2736551 := bstep (se 1 (by rfl) ⟨2052413, by rfl⟩ : syracuseStep 2736551 = 4104827) B4104827
theorem B29606309 : Blo 1823613 29606309 := bstep (se 4 (by rfl) ⟨2775591, by rfl⟩ : syracuseStep 29606309 = 5551183) B5551183
theorem B1641308629 : Blo 1823613 1641308629 := bstep (se 7 (by rfl) ⟨19234085, by rfl⟩ : syracuseStep 1641308629 = 38468171) B38468171
theorem B9232865 : Blo 1823613 9232865 := bstep (se 2 (by rfl) ⟨3462324, by rfl⟩ : syracuseStep 9232865 = 6924649) B6924649
theorem B5546465 : Blo 1823613 5546465 := bstep (se 2 (by rfl) ⟨2079924, by rfl⟩ : syracuseStep 5546465 = 4159849) B4159849
theorem B4383227 : Blo 1823613 4383227 := bstep (se 1 (by rfl) ⟨3287420, by rfl⟩ : syracuseStep 4383227 = 6574841) B6574841
theorem B2736635 : Blo 1823613 2736635 := bstep (se 1 (by rfl) ⟨2052476, by rfl⟩ : syracuseStep 2736635 = 4104953) B4104953
theorem B6160967 : Blo 1823613 6160967 := bstep (se 1 (by rfl) ⟨4620725, by rfl⟩ : syracuseStep 6160967 = 9241451) B9241451
theorem B2736761 : Blo 1823613 2736761 := bstep (se 2 (by rfl) ⟨1026285, by rfl⟩ : syracuseStep 2736761 = 2052571) B2052571
theorem B2736815 : Blo 1823613 2736815 := bstep (se 1 (by rfl) ⟨2052611, by rfl⟩ : syracuseStep 2736815 = 4105223) B4105223
theorem B2736863 : Blo 1823613 2736863 := bstep (se 1 (by rfl) ⟨2052647, by rfl⟩ : syracuseStep 2736863 = 4105295) B4105295
theorem B13861691 : Blo 1823613 13861691 := bstep (se 1 (by rfl) ⟨10396268, by rfl⟩ : syracuseStep 13861691 = 20792537) B20792537
theorem B4105115 : Blo 1823613 4105115 := bstep (se 1 (by rfl) ⟨3078836, by rfl⟩ : syracuseStep 4105115 = 6157673) B6157673
theorem B4383659 : Blo 1823613 4383659 := bstep (se 1 (by rfl) ⟨3287744, by rfl⟩ : syracuseStep 4383659 = 6575489) B6575489
theorem B4162475 : Blo 1823613 4162475 := bstep (se 1 (by rfl) ⟨3121856, by rfl⟩ : syracuseStep 4162475 = 6243713) B6243713
theorem B15000515 : Blo 1823613 15000515 := bstep (se 1 (by rfl) ⟨11250386, by rfl⟩ : syracuseStep 15000515 = 22500773) B22500773
theorem B2737127 : Blo 1823613 2737127 := bstep (se 1 (by rfl) ⟨2052845, by rfl⟩ : syracuseStep 2737127 = 4105691) B4105691
theorem B6161399 : Blo 1823613 6161399 := bstep (se 1 (by rfl) ⟨4621049, by rfl⟩ : syracuseStep 6161399 = 9242099) B9242099
theorem B23708675 : Blo 1823613 23708675 := bstep (se 1 (by rfl) ⟨17781506, by rfl⟩ : syracuseStep 23708675 = 35563013) B35563013
theorem B4105313 : Blo 1823613 4105313 := bstep (se 2 (by rfl) ⟨1539492, by rfl⟩ : syracuseStep 4105313 = 3078985) B3078985
theorem B2737385 : Blo 1823613 2737385 := bstep (se 2 (by rfl) ⟨1026519, by rfl⟩ : syracuseStep 2737385 = 2053039) B2053039
theorem B2737439 : Blo 1823613 2737439 := bstep (se 1 (by rfl) ⟨2053079, by rfl⟩ : syracuseStep 2737439 = 4106159) B4106159
theorem B4105511 : Blo 1823613 4105511 := bstep (se 1 (by rfl) ⟨3079133, by rfl⟩ : syracuseStep 4105511 = 6158267) B6158267
theorem B101213563 : Blo 1823613 101213563 := bstep (se 1 (by rfl) ⟨75910172, by rfl⟩ : syracuseStep 101213563 = 151820345) B151820345
theorem B4933001 : Blo 1823613 4933001 := bstep (se 2 (by rfl) ⟨1849875, by rfl⟩ : syracuseStep 4933001 = 3699751) B3699751
theorem B15582617 : Blo 1823613 15582617 := bstep (se 2 (by rfl) ⟨5843481, by rfl⟩ : syracuseStep 15582617 = 11686963) B11686963
theorem B2737607 : Blo 1823613 2737607 := bstep (se 1 (by rfl) ⟨2053205, by rfl⟩ : syracuseStep 2737607 = 4106411) B4106411
theorem B8324641 : Blo 1823613 8324641 := bstep (se 2 (by rfl) ⟨3121740, by rfl⟩ : syracuseStep 8324641 = 6243481) B6243481
theorem B4384313 : Blo 1823613 4384313 := bstep (se 2 (by rfl) ⟨1644117, by rfl⟩ : syracuseStep 4384313 = 3288235) B3288235
theorem B4105889 : Blo 1823613 4105889 := bstep (se 2 (by rfl) ⟨1539708, by rfl⟩ : syracuseStep 4105889 = 3079417) B3079417
theorem B2737961 : Blo 1823613 2737961 := bstep (se 2 (by rfl) ⟨1026735, by rfl⟩ : syracuseStep 2737961 = 2053471) B2053471
theorem B2737967 : Blo 1823613 2737967 := bstep (se 1 (by rfl) ⟨2053475, by rfl⟩ : syracuseStep 2737967 = 4106951) B4106951
theorem B39454573 : Blo 1823613 39454573 := bstep (se 3 (by rfl) ⟨7397732, by rfl⟩ : syracuseStep 39454573 = 14795465) B14795465
theorem B4106249 : Blo 1823613 4106249 := bstep (se 2 (by rfl) ⟨1539843, by rfl⟩ : syracuseStep 4106249 = 3079687) B3079687
theorem B4384793 : Blo 1823613 4384793 := bstep (se 2 (by rfl) ⟨1644297, by rfl⟩ : syracuseStep 4384793 = 3288595) B3288595
theorem B5622041 : Blo 1823613 5622041 := bstep (se 2 (by rfl) ⟨2108265, by rfl⟩ : syracuseStep 5622041 = 4216531) B4216531
theorem B4106663 : Blo 1823613 4106663 := bstep (se 1 (by rfl) ⟨3079997, by rfl⟩ : syracuseStep 4106663 = 6159995) B6159995
theorem B4106771 : Blo 1823613 4106771 := bstep (se 1 (by rfl) ⟨3080078, by rfl⟩ : syracuseStep 4106771 = 6160157) B6160157
theorem B4106825 : Blo 1823613 4106825 := bstep (se 2 (by rfl) ⟨1540059, by rfl⟩ : syracuseStep 4106825 = 3080119) B3080119
theorem B243329629 : Blo 1823613 243329629 := bstep (se 3 (by rfl) ⟨45624305, by rfl⟩ : syracuseStep 243329629 = 91248611) B91248611
theorem B9235133 : Blo 1823613 9235133 := bstep (se 3 (by rfl) ⟨1731587, by rfl⟩ : syracuseStep 9235133 = 3463175) B3463175
theorem B56183543 : Blo 1823613 56183543 := bstep (se 1 (by rfl) ⟨42137657, by rfl⟩ : syracuseStep 56183543 = 84275315) B84275315
theorem B6155027 : Blo 1823613 6155027 := bstep (se 1 (by rfl) ⟨4616270, by rfl⟩ : syracuseStep 6155027 = 9232541) B9232541
theorem B4107239 : Blo 1823613 4107239 := bstep (se 1 (by rfl) ⟨3080429, by rfl⟩ : syracuseStep 4107239 = 6160859) B6160859
theorem B26307665 : Blo 1823613 26307665 := bstep (se 2 (by rfl) ⟨9865374, by rfl⟩ : syracuseStep 26307665 = 19730749) B19730749
theorem B13855859 : Blo 1823613 13855859 := bstep (se 1 (by rfl) ⟨10391894, by rfl⟩ : syracuseStep 13855859 = 20783789) B20783789
theorem B45599921 : Blo 1823613 45599921 := bstep (se 2 (by rfl) ⟨17099970, by rfl⟩ : syracuseStep 45599921 = 34199941) B34199941
theorem B19508401 : Blo 1823613 19508401 := bstep (se 2 (by rfl) ⟨7315650, by rfl⟩ : syracuseStep 19508401 = 14631301) B14631301
theorem B17534171 : Blo 1823613 17534171 := bstep (se 1 (by rfl) ⟨13150628, by rfl⟩ : syracuseStep 17534171 = 26301257) B26301257
theorem B2813215 : Blo 1823613 2813215 := bstep (se 1 (by rfl) ⟨2109911, by rfl⟩ : syracuseStep 2813215 = 4219823) B4219823
theorem B4107617 : Blo 1823613 4107617 := bstep (se 2 (by rfl) ⟨1540356, by rfl⟩ : syracuseStep 4107617 = 3080713) B3080713
theorem B26652149 : Blo 1823613 26652149 := bstep (se 5 (by rfl) ⟨1249319, by rfl⟩ : syracuseStep 26652149 = 2498639) B2498639
theorem B6155891 : Blo 1823613 6155891 := bstep (se 1 (by rfl) ⟨4616918, by rfl⟩ : syracuseStep 6155891 = 9233837) B9233837
theorem B3509995 : Blo 1823613 3509995 := bstep (se 1 (by rfl) ⟨2632496, by rfl⟩ : syracuseStep 3509995 = 5264993) B5264993
theorem B8326919 : Blo 1823613 8326919 := bstep (se 1 (by rfl) ⟨6245189, by rfl⟩ : syracuseStep 8326919 = 12490379) B12490379
theorem B2051887 : Blo 1823613 2051887 := bstep (se 1 (by rfl) ⟨1538915, by rfl⟩ : syracuseStep 2051887 = 3077831) B3077831
theorem B6156161 : Blo 1823613 6156161 := bstep (se 2 (by rfl) ⟨2308560, by rfl⟩ : syracuseStep 6156161 = 4617121) B4617121
theorem B2051995 : Blo 1823613 2051995 := bstep (se 1 (by rfl) ⟨1538996, by rfl⟩ : syracuseStep 2051995 = 3077993) B3077993
theorem B7794589 : Blo 1823613 7794589 := bstep (se 3 (by rfl) ⟨1461485, by rfl⟩ : syracuseStep 7794589 = 2922971) B2922971
theorem B31190993 : Blo 1823613 31190993 := bstep (se 2 (by rfl) ⟨11696622, by rfl⟩ : syracuseStep 31190993 = 23393245) B23393245
theorem B2437225 : Blo 1823613 2437225 := bstep (se 2 (by rfl) ⟨913959, by rfl⟩ : syracuseStep 2437225 = 1827919) B1827919
theorem B2191579 : Blo 1823613 2191579 := bstep (se 1 (by rfl) ⟨1643684, by rfl⟩ : syracuseStep 2191579 = 3287369) B3287369
theorem B4616473 : Blo 1823613 4616473 := bstep (se 2 (by rfl) ⟨1731177, by rfl⟩ : syracuseStep 4616473 = 3462355) B3462355
theorem B2052391 : Blo 1823613 2052391 := bstep (se 1 (by rfl) ⟨1539293, by rfl⟩ : syracuseStep 2052391 = 3078587) B3078587
theorem B2052463 : Blo 1823613 2052463 := bstep (se 1 (by rfl) ⟨1539347, by rfl⟩ : syracuseStep 2052463 = 3078695) B3078695
theorem B4616615 : Blo 1823613 4616615 := bstep (se 1 (by rfl) ⟨3462461, by rfl⟩ : syracuseStep 4616615 = 6924923) B6924923
theorem B6926867 : Blo 1823613 6926867 := bstep (se 1 (by rfl) ⟨5195150, by rfl⟩ : syracuseStep 6926867 = 10390301) B10390301
theorem B2052679 : Blo 1823613 2052679 := bstep (se 1 (by rfl) ⟨1539509, by rfl⟩ : syracuseStep 2052679 = 3079019) B3079019
theorem B4616777 : Blo 1823613 4616777 := bstep (se 2 (by rfl) ⟨1731291, by rfl⟩ : syracuseStep 4616777 = 3462583) B3462583
theorem B6156971 : Blo 1823613 6156971 := bstep (se 1 (by rfl) ⟨4617728, by rfl⟩ : syracuseStep 6156971 = 9235457) B9235457
theorem B1823643 : Blo 1823613 1823643 := bstep (se 1 (by rfl) ⟨1367732, by rfl⟩ : syracuseStep 1823643 = 2735465) B2735465
theorem B1823695 : Blo 1823613 1823695 := bstep (se 1 (by rfl) ⟨1367771, by rfl⟩ : syracuseStep 1823695 = 2735543) B2735543
theorem B1823719 : Blo 1823613 1823719 := bstep (se 1 (by rfl) ⟨1367789, by rfl⟩ : syracuseStep 1823719 = 2735579) B2735579
theorem B22197239 : Blo 1823613 22197239 := bstep (se 1 (by rfl) ⟨16647929, by rfl⟩ : syracuseStep 22197239 = 33295859) B33295859
theorem B6157511 : Blo 1823613 6157511 := bstep (se 1 (by rfl) ⟨4618133, by rfl⟩ : syracuseStep 6157511 = 9236267) B9236267
theorem B1824031 : Blo 1823613 1824031 := bstep (se 1 (by rfl) ⟨1368023, by rfl⟩ : syracuseStep 1824031 = 2736047) B2736047
theorem B3462439 : Blo 1823613 3462439 := bstep (se 1 (by rfl) ⟨2596829, by rfl⟩ : syracuseStep 3462439 = 5193659) B5193659
theorem B1824091 : Blo 1823613 1824091 := bstep (se 1 (by rfl) ⟨1368068, by rfl⟩ : syracuseStep 1824091 = 2736137) B2736137
theorem B1824111 : Blo 1823613 1824111 := bstep (se 1 (by rfl) ⟨1368083, by rfl⟩ : syracuseStep 1824111 = 2736167) B2736167
theorem B1824167 : Blo 1823613 1824167 := bstep (se 1 (by rfl) ⟨1368125, by rfl⟩ : syracuseStep 1824167 = 2736251) B2736251
theorem B2053543 : Blo 1823613 2053543 := bstep (se 1 (by rfl) ⟨1540157, by rfl⟩ : syracuseStep 2053543 = 3080315) B3080315
theorem B1824251 : Blo 1823613 1824251 := bstep (se 1 (by rfl) ⟨1368188, by rfl⟩ : syracuseStep 1824251 = 2736377) B2736377
theorem B9238049 : Blo 1823613 9238049 := bstep (se 2 (by rfl) ⟨3464268, by rfl⟩ : syracuseStep 9238049 = 6928537) B6928537
theorem B1824319 : Blo 1823613 1824319 := bstep (se 1 (by rfl) ⟨1368239, by rfl⟩ : syracuseStep 1824319 = 2736479) B2736479
theorem B1824327 : Blo 1823613 1824327 := bstep (se 1 (by rfl) ⟨1368245, by rfl⟩ : syracuseStep 1824327 = 2736491) B2736491
theorem B8771161 : Blo 1823613 8771161 := bstep (se 2 (by rfl) ⟨3289185, by rfl⟩ : syracuseStep 8771161 = 6578371) B6578371
theorem B3896927 : Blo 1823613 3896927 := bstep (se 1 (by rfl) ⟨2922695, by rfl⟩ : syracuseStep 3896927 = 5845391) B5845391
theorem B1824479 : Blo 1823613 1824479 := bstep (se 1 (by rfl) ⟨1368359, by rfl⟩ : syracuseStep 1824479 = 2736719) B2736719
theorem B1824559 : Blo 1823613 1824559 := bstep (se 1 (by rfl) ⟨1368419, by rfl⟩ : syracuseStep 1824559 = 2736839) B2736839
theorem B8763241 : Blo 1823613 8763241 := bstep (se 2 (by rfl) ⟨3286215, by rfl⟩ : syracuseStep 8763241 = 6572431) B6572431
theorem B1824667 : Blo 1823613 1824667 := bstep (se 1 (by rfl) ⟨1368500, by rfl⟩ : syracuseStep 1824667 = 2737001) B2737001
theorem B1824719 : Blo 1823613 1824719 := bstep (se 1 (by rfl) ⟨1368539, by rfl⟩ : syracuseStep 1824719 = 2737079) B2737079
theorem B1824743 : Blo 1823613 1824743 := bstep (se 1 (by rfl) ⟨1368557, by rfl⟩ : syracuseStep 1824743 = 2737115) B2737115
theorem B1825055 : Blo 1823613 1825055 := bstep (se 1 (by rfl) ⟨1368791, by rfl⟩ : syracuseStep 1825055 = 2737583) B2737583
theorem B71104837 : Blo 1823613 71104837 := bstep (se 4 (by rfl) ⟨6666078, by rfl⟩ : syracuseStep 71104837 = 13332157) B13332157
theorem B1825115 : Blo 1823613 1825115 := bstep (se 1 (by rfl) ⟨1368836, by rfl⟩ : syracuseStep 1825115 = 2737673) B2737673
theorem B1825135 : Blo 1823613 1825135 := bstep (se 1 (by rfl) ⟨1368851, by rfl⟩ : syracuseStep 1825135 = 2737703) B2737703
theorem B1825191 : Blo 1823613 1825191 := bstep (se 1 (by rfl) ⟨1368893, by rfl⟩ : syracuseStep 1825191 = 2737787) B2737787
theorem B4618721 : Blo 1823613 4618721 := bstep (se 2 (by rfl) ⟨1732020, by rfl⟩ : syracuseStep 4618721 = 3464041) B3464041
theorem B2923003 : Blo 1823613 2923003 := bstep (se 1 (by rfl) ⟨2192252, by rfl⟩ : syracuseStep 2923003 = 4384505) B4384505
theorem B1825275 : Blo 1823613 1825275 := bstep (se 1 (by rfl) ⟨1368956, by rfl⟩ : syracuseStep 1825275 = 2737913) B2737913
theorem B1825343 : Blo 1823613 1825343 := bstep (se 1 (by rfl) ⟨1369007, by rfl⟩ : syracuseStep 1825343 = 2738015) B2738015
theorem B1825351 : Blo 1823613 1825351 := bstep (se 1 (by rfl) ⟨1369013, by rfl⟩ : syracuseStep 1825351 = 2738027) B2738027
theorem B6576815 : Blo 1823613 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B6159023 : Blo 1823613 6159023 := bstep (se 1 (by rfl) ⟨4619267, by rfl⟩ : syracuseStep 6159023 = 9238535) B9238535
theorem B13155011 : Blo 1823613 13155011 := bstep (se 1 (by rfl) ⟨9866258, by rfl⟩ : syracuseStep 13155011 = 19732517) B19732517
theorem B1825503 : Blo 1823613 1825503 := bstep (se 1 (by rfl) ⟨1369127, by rfl⟩ : syracuseStep 1825503 = 2738255) B2738255
theorem B1825583 : Blo 1823613 1825583 := bstep (se 1 (by rfl) ⟨1369187, by rfl⟩ : syracuseStep 1825583 = 2738375) B2738375
theorem B8887165 : Blo 1823613 8887165 := bstep (se 3 (by rfl) ⟨1666343, by rfl⟩ : syracuseStep 8887165 = 3332687) B3332687
theorem B7797647 : Blo 1823613 7797647 := bstep (se 1 (by rfl) ⟨5848235, by rfl⟩ : syracuseStep 7797647 = 11696471) B11696471
theorem B4619227 : Blo 1823613 4619227 := bstep (se 1 (by rfl) ⟨3464420, by rfl⟩ : syracuseStep 4619227 = 6928841) B6928841
theorem B6159347 : Blo 1823613 6159347 := bstep (se 1 (by rfl) ⟨4619510, by rfl⟩ : syracuseStep 6159347 = 9239021) B9239021
theorem B8772623 : Blo 1823613 8772623 := bstep (se 1 (by rfl) ⟨6579467, by rfl⟩ : syracuseStep 8772623 = 13158935) B13158935
theorem B4103207 : Blo 1823613 4103207 := bstep (se 1 (by rfl) ⟨3077405, by rfl⟩ : syracuseStep 4103207 = 6154811) B6154811
theorem B2464873 : Blo 1823613 2464873 := bstep (se 2 (by rfl) ⟨924327, by rfl⟩ : syracuseStep 2464873 = 1848655) B1848655
theorem B16637051 : Blo 1823613 16637051 := bstep (se 1 (by rfl) ⟨12477788, by rfl⟩ : syracuseStep 16637051 = 24955577) B24955577
theorem B3898567 : Blo 1823613 3898567 := bstep (se 1 (by rfl) ⟨2923925, by rfl⟩ : syracuseStep 3898567 = 5847851) B5847851
theorem B4103387 : Blo 1823613 4103387 := bstep (se 1 (by rfl) ⟨3077540, by rfl⟩ : syracuseStep 4103387 = 6155081) B6155081
theorem B2464987 : Blo 1823613 2464987 := bstep (se 1 (by rfl) ⟨1848740, by rfl⟩ : syracuseStep 2464987 = 3697481) B3697481
theorem B4619551 : Blo 1823613 4619551 := bstep (se 1 (by rfl) ⟨3464663, by rfl⟩ : syracuseStep 4619551 = 6929327) B6929327
theorem B3751199 : Blo 1823613 3751199 := bstep (se 1 (by rfl) ⟨2813399, by rfl⟩ : syracuseStep 3751199 = 5626799) B5626799
theorem B13851971 : Blo 1823613 13851971 := bstep (se 1 (by rfl) ⟨10388978, by rfl⟩ : syracuseStep 13851971 = 20777957) B20777957
theorem B2309467 : Blo 1823613 2309467 := bstep (se 1 (by rfl) ⟨1732100, by rfl⟩ : syracuseStep 2309467 = 3464201) B3464201
theorem B6929783 : Blo 1823613 6929783 := bstep (se 1 (by rfl) ⟨5197337, by rfl⟩ : syracuseStep 6929783 = 10394675) B10394675
theorem B2735483 : Blo 1823613 2735483 := bstep (se 1 (by rfl) ⟨2051612, by rfl⟩ : syracuseStep 2735483 = 4103225) B4103225
theorem B13860233 : Blo 1823613 13860233 := bstep (se 2 (by rfl) ⟨5197587, by rfl⟩ : syracuseStep 13860233 = 10395175) B10395175
theorem B2923913 : Blo 1823613 2923913 := bstep (se 2 (by rfl) ⟨1096467, by rfl⟩ : syracuseStep 2923913 = 2192935) B2192935
theorem B4103585 : Blo 1823613 4103585 := bstep (se 2 (by rfl) ⟨1538844, by rfl⟩ : syracuseStep 4103585 = 3077689) B3077689
theorem B14040535 : Blo 1823613 14040535 := bstep (se 1 (by rfl) ⟨10530401, by rfl⟩ : syracuseStep 14040535 = 21060803) B21060803
theorem B16645591 : Blo 1823613 16645591 := bstep (se 1 (by rfl) ⟨12484193, by rfl⟩ : syracuseStep 16645591 = 24968387) B24968387
theorem B2735609 : Blo 1823613 2735609 := bstep (se 2 (by rfl) ⟨1025853, by rfl⟩ : syracuseStep 2735609 = 2051707) B2051707
theorem B6159887 : Blo 1823613 6159887 := bstep (se 1 (by rfl) ⟨4619915, by rfl⟩ : syracuseStep 6159887 = 9239831) B9239831
theorem B4161107 : Blo 1823613 4161107 := bstep (se 1 (by rfl) ⟨3120830, by rfl⟩ : syracuseStep 4161107 = 6241661) B6241661
theorem B2735711 : Blo 1823613 2735711 := bstep (se 1 (by rfl) ⟨2051783, by rfl⟩ : syracuseStep 2735711 = 4103567) B4103567
theorem B3079775 : Blo 1823613 3079775 := bstep (se 1 (by rfl) ⟨2309831, by rfl⟩ : syracuseStep 3079775 = 4619663) B4619663
theorem B7397099 : Blo 1823613 7397099 := bstep (se 1 (by rfl) ⟨5547824, by rfl⟩ : syracuseStep 7397099 = 11095649) B11095649
theorem B13852457 : Blo 1823613 13852457 := bstep (se 2 (by rfl) ⟨5194671, by rfl⟩ : syracuseStep 13852457 = 10389343) B10389343
theorem B2735927 : Blo 1823613 2735927 := bstep (se 1 (by rfl) ⟨2051945, by rfl⟩ : syracuseStep 2735927 = 4103891) B4103891
theorem B3079991 : Blo 1823613 3079991 := bstep (se 1 (by rfl) ⟨2309993, by rfl⟩ : syracuseStep 3079991 = 4619987) B4619987
theorem B16654241 : Blo 1823613 16654241 := bstep (se 2 (by rfl) ⟨6245340, by rfl⟩ : syracuseStep 16654241 = 12490681) B12490681
theorem B4104143 : Blo 1823613 4104143 := bstep (se 1 (by rfl) ⟨3078107, by rfl⟩ : syracuseStep 4104143 = 6156215) B6156215
theorem B25296947 : Blo 1823613 25296947 := bstep (se 1 (by rfl) ⟨18972710, by rfl⟩ : syracuseStep 25296947 = 37945421) B37945421
theorem B2736347 : Blo 1823613 2736347 := bstep (se 1 (by rfl) ⟨2052260, by rfl⟩ : syracuseStep 2736347 = 4104521) B4104521
theorem B2736359 : Blo 1823613 2736359 := bstep (se 1 (by rfl) ⟨2052269, by rfl⟩ : syracuseStep 2736359 = 4104539) B4104539
theorem B3080423 : Blo 1823613 3080423 := bstep (se 1 (by rfl) ⟨2310317, by rfl⟩ : syracuseStep 3080423 = 4620635) B4620635
theorem B2736521 : Blo 1823613 2736521 := bstep (se 2 (by rfl) ⟨1026195, by rfl⟩ : syracuseStep 2736521 = 2052391) B2052391
theorem B3080585 : Blo 1823613 3080585 := bstep (se 2 (by rfl) ⟨1155219, by rfl⟩ : syracuseStep 3080585 = 2310439) B2310439
theorem B94806449 : Blo 1823613 94806449 := bstep (se 2 (by rfl) ⟨35552418, by rfl⟩ : syracuseStep 94806449 = 71104837) B71104837
theorem B4104647 : Blo 1823613 4104647 := bstep (se 1 (by rfl) ⟨3078485, by rfl⟩ : syracuseStep 4104647 = 6156971) B6156971
theorem B2736617 : Blo 1823613 2736617 := bstep (se 2 (by rfl) ⟨1026231, by rfl⟩ : syracuseStep 2736617 = 2052463) B2052463
theorem B9241127 : Blo 1823613 9241127 := bstep (se 1 (by rfl) ⟨6930845, by rfl⟩ : syracuseStep 9241127 = 13861691) B13861691
theorem B2736743 : Blo 1823613 2736743 := bstep (se 1 (by rfl) ⟨2052557, by rfl⟩ : syracuseStep 2736743 = 4105115) B4105115
theorem B2188411505 : Blo 1823613 2188411505 := bstep (se 2 (by rfl) ⟨820654314, by rfl⟩ : syracuseStep 2188411505 = 1641308629) B1641308629
theorem B2736875 : Blo 1823613 2736875 := bstep (se 1 (by rfl) ⟨2052656, by rfl⟩ : syracuseStep 2736875 = 4105313) B4105313
theorem B2736905 : Blo 1823613 2736905 := bstep (se 2 (by rfl) ⟨1026339, by rfl⟩ : syracuseStep 2736905 = 2052679) B2052679
theorem B4105007 : Blo 1823613 4105007 := bstep (se 1 (by rfl) ⟨3078755, by rfl⟩ : syracuseStep 4105007 = 6157511) B6157511
theorem B2737007 : Blo 1823613 2737007 := bstep (se 1 (by rfl) ⟨2052755, by rfl⟩ : syracuseStep 2737007 = 4105511) B4105511
theorem B10388411 : Blo 1823613 10388411 := bstep (se 1 (by rfl) ⟨7791308, by rfl⟩ : syracuseStep 10388411 = 15582617) B15582617
theorem B2597951 : Blo 1823613 2597951 := bstep (se 1 (by rfl) ⟨1948463, by rfl⟩ : syracuseStep 2597951 = 3896927) B3896927
theorem B2737259 : Blo 1823613 2737259 := bstep (se 1 (by rfl) ⟨2052944, by rfl⟩ : syracuseStep 2737259 = 4105889) B4105889
theorem B2737499 : Blo 1823613 2737499 := bstep (se 1 (by rfl) ⟨2053124, by rfl⟩ : syracuseStep 2737499 = 4106249) B4106249
theorem B26011201 : Blo 1823613 26011201 := bstep (se 2 (by rfl) ⟨9754200, by rfl⟩ : syracuseStep 26011201 = 19508401) B19508401
theorem B2737775 : Blo 1823613 2737775 := bstep (se 1 (by rfl) ⟨2053331, by rfl⟩ : syracuseStep 2737775 = 4106663) B4106663
theorem B3286649 : Blo 1823613 3286649 := bstep (se 2 (by rfl) ⟨1232493, by rfl⟩ : syracuseStep 3286649 = 2464987) B2464987
theorem B2737847 : Blo 1823613 2737847 := bstep (se 1 (by rfl) ⟨2053385, by rfl⟩ : syracuseStep 2737847 = 4106771) B4106771
theorem B2737883 : Blo 1823613 2737883 := bstep (se 1 (by rfl) ⟨2053412, by rfl⟩ : syracuseStep 2737883 = 4106825) B4106825
theorem B4384543 : Blo 1823613 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B4106015 : Blo 1823613 4106015 := bstep (se 1 (by rfl) ⟨3079511, by rfl⟩ : syracuseStep 4106015 = 6159023) B6159023
theorem B37455695 : Blo 1823613 37455695 := bstep (se 1 (by rfl) ⟨28091771, by rfl⟩ : syracuseStep 37455695 = 56183543) B56183543
theorem B2738057 : Blo 1823613 2738057 := bstep (se 2 (by rfl) ⟨1026771, by rfl⟩ : syracuseStep 2738057 = 2053543) B2053543
theorem B46753685 : Blo 1823613 46753685 := bstep (se 6 (by rfl) ⟨1095789, by rfl⟩ : syracuseStep 46753685 = 2191579) B2191579
theorem B18720713 : Blo 1823613 18720713 := bstep (se 2 (by rfl) ⟨7020267, by rfl⟩ : syracuseStep 18720713 = 14040535) B14040535
theorem B22194121 : Blo 1823613 22194121 := bstep (se 2 (by rfl) ⟨8322795, by rfl⟩ : syracuseStep 22194121 = 16645591) B16645591
theorem B2738159 : Blo 1823613 2738159 := bstep (se 1 (by rfl) ⟨2053619, by rfl⟩ : syracuseStep 2738159 = 4107239) B4107239
theorem B4106231 : Blo 1823613 4106231 := bstep (se 1 (by rfl) ⟨3079673, by rfl⟩ : syracuseStep 4106231 = 6159347) B6159347
theorem B2500799 : Blo 1823613 2500799 := bstep (se 1 (by rfl) ⟨1875599, by rfl⟩ : syracuseStep 2500799 = 3751199) B3751199
theorem B9234647 : Blo 1823613 9234647 := bstep (se 1 (by rfl) ⟨6925985, by rfl⟩ : syracuseStep 9234647 = 13851971) B13851971
theorem B2738411 : Blo 1823613 2738411 := bstep (se 1 (by rfl) ⟨2053808, by rfl⟩ : syracuseStep 2738411 = 4107617) B4107617
theorem B4679993 : Blo 1823613 4679993 := bstep (se 2 (by rfl) ⟨1754997, by rfl⟩ : syracuseStep 4679993 = 3509995) B3509995
theorem B4106591 : Blo 1823613 4106591 := bstep (se 1 (by rfl) ⟨3079943, by rfl⟩ : syracuseStep 4106591 = 6159887) B6159887
theorem B11684321 : Blo 1823613 11684321 := bstep (se 2 (by rfl) ⟨4381620, by rfl⟩ : syracuseStep 11684321 = 8763241) B8763241
theorem B9234971 : Blo 1823613 9234971 := bstep (se 1 (by rfl) ⟨6926228, by rfl⟩ : syracuseStep 9234971 = 13852457) B13852457
theorem B11102827 : Blo 1823613 11102827 := bstep (se 1 (by rfl) ⟨8327120, by rfl⟩ : syracuseStep 11102827 = 16654241) B16654241
theorem B20793995 : Blo 1823613 20793995 := bstep (se 1 (by rfl) ⟨15595496, by rfl⟩ : syracuseStep 20793995 = 31190993) B31190993
theorem B11692781 : Blo 1823613 11692781 := bstep (se 3 (by rfl) ⟨2192396, by rfl⟩ : syracuseStep 11692781 = 4384793) B4384793
theorem B19737539 : Blo 1823613 19737539 := bstep (se 1 (by rfl) ⟨14803154, by rfl⟩ : syracuseStep 19737539 = 29606309) B29606309
theorem B6155243 : Blo 1823613 6155243 := bstep (se 1 (by rfl) ⟨4616432, by rfl⟩ : syracuseStep 6155243 = 9232865) B9232865
theorem B3697643 : Blo 1823613 3697643 := bstep (se 1 (by rfl) ⟨2773232, by rfl⟩ : syracuseStep 3697643 = 5546465) B5546465
theorem B6155297 : Blo 1823613 6155297 := bstep (se 2 (by rfl) ⟨2308236, by rfl⟩ : syracuseStep 6155297 = 4616473) B4616473
theorem B4107311 : Blo 1823613 4107311 := bstep (se 1 (by rfl) ⟨3080483, by rfl⟩ : syracuseStep 4107311 = 6160967) B6160967
theorem B6925409 : Blo 1823613 6925409 := bstep (se 2 (by rfl) ⟨2597028, by rfl⟩ : syracuseStep 6925409 = 5194057) B5194057
theorem B14798159 : Blo 1823613 14798159 := bstep (se 1 (by rfl) ⟨11098619, by rfl⟩ : syracuseStep 14798159 = 22197239) B22197239
theorem B4107599 : Blo 1823613 4107599 := bstep (se 1 (by rfl) ⟨3080699, by rfl⟩ : syracuseStep 4107599 = 6161399) B6161399
theorem B15805783 : Blo 1823613 15805783 := bstep (se 1 (by rfl) ⟨11854337, by rfl⟩ : syracuseStep 15805783 = 23708675) B23708675
theorem B324439505 : Blo 1823613 324439505 := bstep (se 2 (by rfl) ⟨121664814, by rfl⟩ : syracuseStep 324439505 = 243329629) B243329629
theorem B3748027 : Blo 1823613 3748027 := bstep (se 1 (by rfl) ⟨2811020, by rfl⟩ : syracuseStep 3748027 = 5622041) B5622041
theorem B5198089 : Blo 1823613 5198089 := bstep (se 2 (by rfl) ⟨1949283, by rfl⟩ : syracuseStep 5198089 = 3898567) B3898567
theorem B4616585 : Blo 1823613 4616585 := bstep (se 2 (by rfl) ⟨1731219, by rfl⟩ : syracuseStep 4616585 = 3462439) B3462439
theorem B6156755 : Blo 1823613 6156755 := bstep (se 1 (by rfl) ⟨4617566, by rfl⟩ : syracuseStep 6156755 = 9235133) B9235133
theorem B8770007 : Blo 1823613 8770007 := bstep (se 1 (by rfl) ⟨6577505, by rfl⟩ : syracuseStep 8770007 = 13155011) B13155011
theorem B134951417 : Blo 1823613 134951417 := bstep (se 2 (by rfl) ⟨50606781, by rfl⟩ : syracuseStep 134951417 = 101213563) B101213563
theorem B5198431 : Blo 1823613 5198431 := bstep (se 1 (by rfl) ⟨3898823, by rfl⟩ : syracuseStep 5198431 = 7797647) B7797647
theorem B22205117 : Blo 1823613 22205117 := bstep (se 3 (by rfl) ⟨4163459, by rfl⟩ : syracuseStep 22205117 = 8326919) B8326919
theorem B9237239 : Blo 1823613 9237239 := bstep (se 1 (by rfl) ⟨6927929, by rfl⟩ : syracuseStep 9237239 = 13855859) B13855859
theorem B11694881 : Blo 1823613 11694881 := bstep (se 2 (by rfl) ⟨4385580, by rfl⟩ : syracuseStep 11694881 = 8771161) B8771161
theorem B1823655 : Blo 1823613 1823655 := bstep (se 1 (by rfl) ⟨1367741, by rfl⟩ : syracuseStep 1823655 = 2735483) B2735483
theorem B1823739 : Blo 1823613 1823739 := bstep (se 1 (by rfl) ⟨1367804, by rfl⟩ : syracuseStep 1823739 = 2735609) B2735609
theorem B2774071 : Blo 1823613 2774071 := bstep (se 1 (by rfl) ⟨2080553, by rfl⟩ : syracuseStep 2774071 = 4161107) B4161107
theorem B1823807 : Blo 1823613 1823807 := bstep (se 1 (by rfl) ⟨1367855, by rfl⟩ : syracuseStep 1823807 = 2735711) B2735711
theorem B2053183 : Blo 1823613 2053183 := bstep (se 1 (by rfl) ⟨1539887, by rfl⟩ : syracuseStep 2053183 = 3079775) B3079775
theorem B52606097 : Blo 1823613 52606097 := bstep (se 2 (by rfl) ⟨19727286, by rfl⟩ : syracuseStep 52606097 = 39454573) B39454573
theorem B1823951 : Blo 1823613 1823951 := bstep (se 1 (by rfl) ⟨1367963, by rfl⟩ : syracuseStep 1823951 = 2735927) B2735927
theorem B2053327 : Blo 1823613 2053327 := bstep (se 1 (by rfl) ⟨1539995, by rfl⟩ : syracuseStep 2053327 = 3079991) B3079991
theorem B10392785 : Blo 1823613 10392785 := bstep (se 2 (by rfl) ⟨3897294, by rfl⟩ : syracuseStep 10392785 = 7794589) B7794589
theorem B1824155 : Blo 1823613 1824155 := bstep (se 1 (by rfl) ⟨1368116, by rfl⟩ : syracuseStep 1824155 = 2736233) B2736233
theorem B3077743 : Blo 1823613 3077743 := bstep (se 1 (by rfl) ⟨2308307, by rfl⟩ : syracuseStep 3077743 = 4616615) B4616615
theorem B1824367 : Blo 1823613 1824367 := bstep (se 1 (by rfl) ⟨1368275, by rfl⟩ : syracuseStep 1824367 = 2736551) B2736551
theorem B37443217 : Blo 1823613 37443217 := bstep (se 2 (by rfl) ⟨14041206, by rfl⟩ : syracuseStep 37443217 = 28082413) B28082413
theorem B2922151 : Blo 1823613 2922151 := bstep (se 1 (by rfl) ⟨2191613, by rfl⟩ : syracuseStep 2922151 = 4383227) B4383227
theorem B1824423 : Blo 1823613 1824423 := bstep (se 1 (by rfl) ⟨1368317, by rfl⟩ : syracuseStep 1824423 = 2736635) B2736635
theorem B4617911 : Blo 1823613 4617911 := bstep (se 1 (by rfl) ⟨3463433, by rfl⟩ : syracuseStep 4617911 = 6926867) B6926867
theorem B3077851 : Blo 1823613 3077851 := bstep (se 1 (by rfl) ⟨2308388, by rfl⟩ : syracuseStep 3077851 = 4616777) B4616777
theorem B1824507 : Blo 1823613 1824507 := bstep (se 1 (by rfl) ⟨1368380, by rfl⟩ : syracuseStep 1824507 = 2736761) B2736761
theorem B1824543 : Blo 1823613 1824543 := bstep (se 1 (by rfl) ⟨1368407, by rfl⟩ : syracuseStep 1824543 = 2736815) B2736815
theorem B1824575 : Blo 1823613 1824575 := bstep (se 1 (by rfl) ⟨1368431, by rfl⟩ : syracuseStep 1824575 = 2736863) B2736863
theorem B13145989 : Blo 1823613 13145989 := bstep (se 4 (by rfl) ⟨1232436, by rfl⟩ : syracuseStep 13145989 = 2464873) B2464873
theorem B2774983 : Blo 1823613 2774983 := bstep (se 1 (by rfl) ⟨2081237, by rfl⟩ : syracuseStep 2774983 = 4162475) B4162475
theorem B10000343 : Blo 1823613 10000343 := bstep (se 1 (by rfl) ⟨7500257, by rfl⟩ : syracuseStep 10000343 = 15000515) B15000515
theorem B1824751 : Blo 1823613 1824751 := bstep (se 1 (by rfl) ⟨1368563, by rfl⟩ : syracuseStep 1824751 = 2737127) B2737127
theorem B3897337 : Blo 1823613 3897337 := bstep (se 2 (by rfl) ⟨1461501, by rfl⟩ : syracuseStep 3897337 = 2923003) B2923003
theorem B1824923 : Blo 1823613 1824923 := bstep (se 1 (by rfl) ⟨1368692, by rfl⟩ : syracuseStep 1824923 = 2737385) B2737385
theorem B1824959 : Blo 1823613 1824959 := bstep (se 1 (by rfl) ⟨1368719, by rfl⟩ : syracuseStep 1824959 = 2737439) B2737439
theorem B1825071 : Blo 1823613 1825071 := bstep (se 1 (by rfl) ⟨1368803, by rfl⟩ : syracuseStep 1825071 = 2737607) B2737607
theorem B6158699 : Blo 1823613 6158699 := bstep (se 1 (by rfl) ⟨4619024, by rfl⟩ : syracuseStep 6158699 = 9238049) B9238049
theorem B13154669 : Blo 1823613 13154669 := bstep (se 3 (by rfl) ⟨2466500, by rfl⟩ : syracuseStep 13154669 = 4933001) B4933001
theorem B2922875 : Blo 1823613 2922875 := bstep (se 1 (by rfl) ⟨2192156, by rfl⟩ : syracuseStep 2922875 = 4384313) B4384313
theorem B1825307 : Blo 1823613 1825307 := bstep (se 1 (by rfl) ⟨1368980, by rfl⟩ : syracuseStep 1825307 = 2737961) B2737961
theorem B1825311 : Blo 1823613 1825311 := bstep (se 1 (by rfl) ⟨1368983, by rfl⟩ : syracuseStep 1825311 = 2737967) B2737967
theorem B6158969 : Blo 1823613 6158969 := bstep (se 2 (by rfl) ⟨2309613, by rfl⟩ : syracuseStep 6158969 = 4619227) B4619227
theorem B3079147 : Blo 1823613 3079147 := bstep (se 1 (by rfl) ⟨2309360, by rfl⟩ : syracuseStep 3079147 = 4618721) B4618721
theorem B6159401 : Blo 1823613 6159401 := bstep (se 2 (by rfl) ⟨2309775, by rfl⟩ : syracuseStep 6159401 = 4619551) B4619551
theorem B3750953 : Blo 1823613 3750953 := bstep (se 2 (by rfl) ⟨1406607, by rfl⟩ : syracuseStep 3750953 = 2813215) B2813215
theorem B3079289 : Blo 1823613 3079289 := bstep (se 2 (by rfl) ⟨1154733, by rfl⟩ : syracuseStep 3079289 = 2309467) B2309467
theorem B4103351 : Blo 1823613 4103351 := bstep (se 1 (by rfl) ⟨3077513, by rfl⟩ : syracuseStep 4103351 = 6155027) B6155027
theorem B47398213 : Blo 1823613 47398213 := bstep (se 4 (by rfl) ⟨4443582, by rfl⟩ : syracuseStep 47398213 = 8887165) B8887165
theorem B5848415 : Blo 1823613 5848415 := bstep (se 1 (by rfl) ⟨4386311, by rfl⟩ : syracuseStep 5848415 = 8772623) B8772623
theorem B2735471 : Blo 1823613 2735471 := bstep (se 1 (by rfl) ⟨2051603, by rfl⟩ : syracuseStep 2735471 = 4103207) B4103207
theorem B11099521 : Blo 1823613 11099521 := bstep (se 2 (by rfl) ⟨4162320, by rfl⟩ : syracuseStep 11099521 = 8324641) B8324641
theorem B17538443 : Blo 1823613 17538443 := bstep (se 1 (by rfl) ⟨13153832, by rfl⟩ : syracuseStep 17538443 = 26307665) B26307665
theorem B11091367 : Blo 1823613 11091367 := bstep (se 1 (by rfl) ⟨8318525, by rfl⟩ : syracuseStep 11091367 = 16637051) B16637051
theorem B30399947 : Blo 1823613 30399947 := bstep (se 1 (by rfl) ⟨22799960, by rfl⟩ : syracuseStep 30399947 = 45599921) B45599921
theorem B2735591 : Blo 1823613 2735591 := bstep (se 1 (by rfl) ⟨2051693, by rfl⟩ : syracuseStep 2735591 = 4103387) B4103387
theorem B11689447 : Blo 1823613 11689447 := bstep (se 1 (by rfl) ⟨8767085, by rfl⟩ : syracuseStep 11689447 = 17534171) B17534171
theorem B51994133 : Blo 1823613 51994133 := bstep (se 6 (by rfl) ⟨1218612, by rfl⟩ : syracuseStep 51994133 = 2437225) B2437225
theorem B4619855 : Blo 1823613 4619855 := bstep (se 1 (by rfl) ⟨3464891, by rfl⟩ : syracuseStep 4619855 = 6929783) B6929783
theorem B9240155 : Blo 1823613 9240155 := bstep (se 1 (by rfl) ⟨6930116, by rfl⟩ : syracuseStep 9240155 = 13860233) B13860233
theorem B1949275 : Blo 1823613 1949275 := bstep (se 1 (by rfl) ⟨1461956, by rfl⟩ : syracuseStep 1949275 = 2923913) B2923913
theorem B2735723 : Blo 1823613 2735723 := bstep (se 1 (by rfl) ⟨2051792, by rfl⟩ : syracuseStep 2735723 = 4103585) B4103585
theorem B17768099 : Blo 1823613 17768099 := bstep (se 1 (by rfl) ⟨13326074, by rfl⟩ : syracuseStep 17768099 = 26652149) B26652149
theorem B2735849 : Blo 1823613 2735849 := bstep (se 2 (by rfl) ⟨1025943, by rfl⟩ : syracuseStep 2735849 = 2051887) B2051887
theorem B4103927 : Blo 1823613 4103927 := bstep (se 1 (by rfl) ⟨3077945, by rfl⟩ : syracuseStep 4103927 = 6155891) B6155891
theorem B11689757 : Blo 1823613 11689757 := bstep (se 3 (by rfl) ⟨2191829, by rfl⟩ : syracuseStep 11689757 = 4383659) B4383659
theorem B4931399 : Blo 1823613 4931399 := bstep (se 1 (by rfl) ⟨3698549, by rfl⟩ : syracuseStep 4931399 = 7397099) B7397099
theorem B2735993 : Blo 1823613 2735993 := bstep (se 2 (by rfl) ⟨1025997, by rfl⟩ : syracuseStep 2735993 = 2051995) B2051995
theorem B4104107 : Blo 1823613 4104107 := bstep (se 1 (by rfl) ⟨3078080, by rfl⟩ : syracuseStep 4104107 = 6156161) B6156161
theorem B2736095 : Blo 1823613 2736095 := bstep (se 1 (by rfl) ⟨2052071, by rfl⟩ : syracuseStep 2736095 = 4104143) B4104143
theorem B10002541 : Blo 1823613 10002541 := bstep (se 3 (by rfl) ⟨1875476, by rfl⟩ : syracuseStep 10002541 = 3750953) B3750953
theorem B4997369 : Blo 1823613 4997369 := bstep (se 2 (by rfl) ⟨1874013, by rfl⟩ : syracuseStep 4997369 = 3748027) B3748027
theorem B14795045 : Blo 1823613 14795045 := bstep (se 4 (by rfl) ⟨1387035, by rfl⟩ : syracuseStep 14795045 = 2774071) B2774071
theorem B2736431 : Blo 1823613 2736431 := bstep (se 1 (by rfl) ⟨2052323, by rfl⟩ : syracuseStep 2736431 = 4104647) B4104647
theorem B4104503 : Blo 1823613 4104503 := bstep (se 1 (by rfl) ⟨3078377, by rfl⟩ : syracuseStep 4104503 = 6156755) B6156755
theorem B6930785 : Blo 1823613 6930785 := bstep (se 2 (by rfl) ⟨2599044, by rfl⟩ : syracuseStep 6930785 = 5198089) B5198089
theorem B6160751 : Blo 1823613 6160751 := bstep (se 1 (by rfl) ⟨4620563, by rfl⟩ : syracuseStep 6160751 = 9241127) B9241127
theorem B14803411 : Blo 1823613 14803411 := bstep (se 1 (by rfl) ⟨11102558, by rfl⟩ : syracuseStep 14803411 = 22205117) B22205117
theorem B10396133 : Blo 1823613 10396133 := bstep (se 4 (by rfl) ⟨974637, by rfl⟩ : syracuseStep 10396133 = 1949275) B1949275
theorem B2736671 : Blo 1823613 2736671 := bstep (se 1 (by rfl) ⟨2052503, by rfl⟩ : syracuseStep 2736671 = 4105007) B4105007
theorem B35070731 : Blo 1823613 35070731 := bstep (se 1 (by rfl) ⟨26303048, by rfl⟩ : syracuseStep 35070731 = 52606097) B52606097
theorem B6931241 : Blo 1823613 6931241 := bstep (se 2 (by rfl) ⟨2599215, by rfl⟩ : syracuseStep 6931241 = 5198431) B5198431
theorem B14803769 : Blo 1823613 14803769 := bstep (se 2 (by rfl) ⟨5551413, by rfl⟩ : syracuseStep 14803769 = 11102827) B11102827
theorem B2737343 : Blo 1823613 2737343 := bstep (se 1 (by rfl) ⟨2053007, by rfl⟩ : syracuseStep 2737343 = 4106015) B4106015
theorem B24970463 : Blo 1823613 24970463 := bstep (se 1 (by rfl) ⟨18727847, by rfl⟩ : syracuseStep 24970463 = 37455695) B37455695
theorem B4105529 : Blo 1823613 4105529 := bstep (se 2 (by rfl) ⟨1539573, by rfl⟩ : syracuseStep 4105529 = 3079147) B3079147
theorem B2737487 : Blo 1823613 2737487 := bstep (se 1 (by rfl) ⟨2053115, by rfl⟩ : syracuseStep 2737487 = 4106231) B4106231
theorem B2737577 : Blo 1823613 2737577 := bstep (se 2 (by rfl) ⟨1026591, by rfl⟩ : syracuseStep 2737577 = 2053183) B2053183
theorem B2737727 : Blo 1823613 2737727 := bstep (se 1 (by rfl) ⟨2053295, by rfl⟩ : syracuseStep 2737727 = 4106591) B4106591
theorem B4105799 : Blo 1823613 4105799 := bstep (se 1 (by rfl) ⟨3079349, by rfl⟩ : syracuseStep 4105799 = 6158699) B6158699
theorem B2737769 : Blo 1823613 2737769 := bstep (se 2 (by rfl) ⟨1026663, by rfl⟩ : syracuseStep 2737769 = 2053327) B2053327
theorem B4105979 : Blo 1823613 4105979 := bstep (se 1 (by rfl) ⟨3079484, by rfl⟩ : syracuseStep 4105979 = 6158969) B6158969
theorem B13862663 : Blo 1823613 13862663 := bstep (se 1 (by rfl) ⟨10396997, by rfl⟩ : syracuseStep 13862663 = 20793995) B20793995
theorem B14788489 : Blo 1823613 14788489 := bstep (se 2 (by rfl) ⟨5545683, by rfl⟩ : syracuseStep 14788489 = 11091367) B11091367
theorem B13158359 : Blo 1823613 13158359 := bstep (se 1 (by rfl) ⟨9868769, by rfl⟩ : syracuseStep 13158359 = 19737539) B19737539
theorem B26675189 : Blo 1823613 26675189 := bstep (se 5 (by rfl) ⟨1250399, by rfl⟩ : syracuseStep 26675189 = 2500799) B2500799
theorem B4106267 : Blo 1823613 4106267 := bstep (se 1 (by rfl) ⟨3079700, by rfl⟩ : syracuseStep 4106267 = 6159401) B6159401
theorem B2738207 : Blo 1823613 2738207 := bstep (se 1 (by rfl) ⟨2053655, by rfl⟩ : syracuseStep 2738207 = 4107311) B4107311
theorem B13150397 : Blo 1823613 13150397 := bstep (se 3 (by rfl) ⟨2465699, by rfl⟩ : syracuseStep 13150397 = 4931399) B4931399
theorem B49924289 : Blo 1823613 49924289 := bstep (se 2 (by rfl) ⟨18721608, by rfl⟩ : syracuseStep 49924289 = 37443217) B37443217
theorem B9865439 : Blo 1823613 9865439 := bstep (se 1 (by rfl) ⟨7399079, by rfl⟩ : syracuseStep 9865439 = 14798159) B14798159
theorem B2738399 : Blo 1823613 2738399 := bstep (se 1 (by rfl) ⟨2053799, by rfl⟩ : syracuseStep 2738399 = 4107599) B4107599
theorem B11692295 : Blo 1823613 11692295 := bstep (se 1 (by rfl) ⟨8769221, by rfl⟩ : syracuseStep 11692295 = 17538443) B17538443
theorem B34662755 : Blo 1823613 34662755 := bstep (se 1 (by rfl) ⟨25997066, by rfl⟩ : syracuseStep 34662755 = 51994133) B51994133
theorem B7793171 : Blo 1823613 7793171 := bstep (se 1 (by rfl) ⟨5844878, by rfl⟩ : syracuseStep 7793171 = 11689757) B11689757
theorem B29592161 : Blo 1823613 29592161 := bstep (se 2 (by rfl) ⟨11097060, by rfl⟩ : syracuseStep 29592161 = 22194121) B22194121
theorem B5196449 : Blo 1823613 5196449 := bstep (se 2 (by rfl) ⟨1948668, by rfl⟩ : syracuseStep 5196449 = 3897337) B3897337
theorem B63204299 : Blo 1823613 63204299 := bstep (se 1 (by rfl) ⟨47403224, by rfl⟩ : syracuseStep 63204299 = 94806449) B94806449
theorem B89967611 : Blo 1823613 89967611 := bstep (se 1 (by rfl) ⟨67475708, by rfl⟩ : syracuseStep 89967611 = 134951417) B134951417
theorem B1458941003 : Blo 1823613 1458941003 := bstep (se 1 (by rfl) ⟨1094205752, by rfl⟩ : syracuseStep 1458941003 = 2188411505) B2188411505
theorem B6925607 : Blo 1823613 6925607 := bstep (se 1 (by rfl) ⟨5194205, by rfl⟩ : syracuseStep 6925607 = 10388411) B10388411
theorem B2191099 : Blo 1823613 2191099 := bstep (se 1 (by rfl) ⟨1643324, by rfl⟩ : syracuseStep 2191099 = 3286649) B3286649
theorem B12480475 : Blo 1823613 12480475 := bstep (se 1 (by rfl) ⟨9360356, by rfl⟩ : syracuseStep 12480475 = 18720713) B18720713
theorem B6156431 : Blo 1823613 6156431 := bstep (se 1 (by rfl) ⟨4617323, by rfl⟩ : syracuseStep 6156431 = 9234647) B9234647
theorem B8769779 : Blo 1823613 8769779 := bstep (se 1 (by rfl) ⟨6577334, by rfl⟩ : syracuseStep 8769779 = 13154669) B13154669
theorem B6156647 : Blo 1823613 6156647 := bstep (se 1 (by rfl) ⟨4617485, by rfl⟩ : syracuseStep 6156647 = 9234971) B9234971
theorem B63197617 : Blo 1823613 63197617 := bstep (se 2 (by rfl) ⟨23699106, by rfl⟩ : syracuseStep 63197617 = 47398213) B47398213
theorem B21074377 : Blo 1823613 21074377 := bstep (se 2 (by rfl) ⟨7902891, by rfl⟩ : syracuseStep 21074377 = 15805783) B15805783
theorem B7795187 : Blo 1823613 7795187 := bstep (se 1 (by rfl) ⟨5846390, by rfl⟩ : syracuseStep 7795187 = 11692781) B11692781
theorem B14799361 : Blo 1823613 14799361 := bstep (se 2 (by rfl) ⟨5549760, by rfl⟩ : syracuseStep 14799361 = 11099521) B11099521
theorem B15585929 : Blo 1823613 15585929 := bstep (se 2 (by rfl) ⟨5844723, by rfl⟩ : syracuseStep 15585929 = 11689447) B11689447
theorem B4616939 : Blo 1823613 4616939 := bstep (se 1 (by rfl) ⟨3462704, by rfl⟩ : syracuseStep 4616939 = 6925409) B6925409
theorem B2052859 : Blo 1823613 2052859 := bstep (se 1 (by rfl) ⟨1539644, by rfl⟩ : syracuseStep 2052859 = 3079289) B3079289
theorem B34681601 : Blo 1823613 34681601 := bstep (se 2 (by rfl) ⟨13005600, by rfl⟩ : syracuseStep 34681601 = 26011201) B26011201
theorem B3896201 : Blo 1823613 3896201 := bstep (se 2 (by rfl) ⟨1461075, by rfl⟩ : syracuseStep 3896201 = 2922151) B2922151
theorem B1823647 : Blo 1823613 1823647 := bstep (se 1 (by rfl) ⟨1367735, by rfl⟩ : syracuseStep 1823647 = 2735471) B2735471
theorem B1823727 : Blo 1823613 1823727 := bstep (se 1 (by rfl) ⟨1367795, by rfl⟩ : syracuseStep 1823727 = 2735591) B2735591
theorem B5846057 : Blo 1823613 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B1823815 : Blo 1823613 1823815 := bstep (se 1 (by rfl) ⟨1367861, by rfl⟩ : syracuseStep 1823815 = 2735723) B2735723
theorem B1823899 : Blo 1823613 1823899 := bstep (se 1 (by rfl) ⟨1367924, by rfl⟩ : syracuseStep 1823899 = 2735849) B2735849
theorem B17527985 : Blo 1823613 17527985 := bstep (se 2 (by rfl) ⟨6572994, by rfl⟩ : syracuseStep 17527985 = 13145989) B13145989
theorem B1823995 : Blo 1823613 1823995 := bstep (se 1 (by rfl) ⟨1367996, by rfl⟩ : syracuseStep 1823995 = 2735993) B2735993
theorem B3699977 : Blo 1823613 3699977 := bstep (se 2 (by rfl) ⟨1387491, by rfl⟩ : syracuseStep 3699977 = 2774983) B2774983
theorem B1824063 : Blo 1823613 1824063 := bstep (se 1 (by rfl) ⟨1368047, by rfl⟩ : syracuseStep 1824063 = 2736095) B2736095
theorem B16864631 : Blo 1823613 16864631 := bstep (se 1 (by rfl) ⟨12648473, by rfl⟩ : syracuseStep 16864631 = 25296947) B25296947
theorem B1824231 : Blo 1823613 1824231 := bstep (se 1 (by rfl) ⟨1368173, by rfl⟩ : syracuseStep 1824231 = 2736347) B2736347
theorem B1824239 : Blo 1823613 1824239 := bstep (se 1 (by rfl) ⟨1368179, by rfl⟩ : syracuseStep 1824239 = 2736359) B2736359
theorem B2053615 : Blo 1823613 2053615 := bstep (se 1 (by rfl) ⟨1540211, by rfl⟩ : syracuseStep 2053615 = 3080423) B3080423
theorem B6927869 : Blo 1823613 6927869 := bstep (se 3 (by rfl) ⟨1298975, by rfl⟩ : syracuseStep 6927869 = 2597951) B2597951
theorem B3077723 : Blo 1823613 3077723 := bstep (se 1 (by rfl) ⟨2308292, by rfl⟩ : syracuseStep 3077723 = 4616585) B4616585
theorem B1824347 : Blo 1823613 1824347 := bstep (se 1 (by rfl) ⟨1368260, by rfl⟩ : syracuseStep 1824347 = 2736521) B2736521
theorem B2053723 : Blo 1823613 2053723 := bstep (se 1 (by rfl) ⟨1540292, by rfl⟩ : syracuseStep 2053723 = 3080585) B3080585
theorem B5846671 : Blo 1823613 5846671 := bstep (se 1 (by rfl) ⟨4385003, by rfl⟩ : syracuseStep 5846671 = 8770007) B8770007
theorem B1824411 : Blo 1823613 1824411 := bstep (se 1 (by rfl) ⟨1368308, by rfl⟩ : syracuseStep 1824411 = 2736617) B2736617
theorem B1824495 : Blo 1823613 1824495 := bstep (se 1 (by rfl) ⟨1368371, by rfl⟩ : syracuseStep 1824495 = 2736743) B2736743
theorem B1824583 : Blo 1823613 1824583 := bstep (se 1 (by rfl) ⟨1368437, by rfl⟩ : syracuseStep 1824583 = 2736875) B2736875
theorem B6158159 : Blo 1823613 6158159 := bstep (se 1 (by rfl) ⟨4618619, by rfl⟩ : syracuseStep 6158159 = 9237239) B9237239
theorem B1824603 : Blo 1823613 1824603 := bstep (se 1 (by rfl) ⟨1368452, by rfl⟩ : syracuseStep 1824603 = 2736905) B2736905
theorem B7796587 : Blo 1823613 7796587 := bstep (se 1 (by rfl) ⟨5847440, by rfl⟩ : syracuseStep 7796587 = 11694881) B11694881
theorem B1824671 : Blo 1823613 1824671 := bstep (se 1 (by rfl) ⟨1368503, by rfl⟩ : syracuseStep 1824671 = 2737007) B2737007
theorem B1824839 : Blo 1823613 1824839 := bstep (se 1 (by rfl) ⟨1368629, by rfl⟩ : syracuseStep 1824839 = 2737259) B2737259
theorem B6928523 : Blo 1823613 6928523 := bstep (se 1 (by rfl) ⟨5196392, by rfl⟩ : syracuseStep 6928523 = 10392785) B10392785
theorem B1824999 : Blo 1823613 1824999 := bstep (se 1 (by rfl) ⟨1368749, by rfl⟩ : syracuseStep 1824999 = 2737499) B2737499
theorem B1825183 : Blo 1823613 1825183 := bstep (se 1 (by rfl) ⟨1368887, by rfl⟩ : syracuseStep 1825183 = 2737775) B2737775
theorem B3078607 : Blo 1823613 3078607 := bstep (se 1 (by rfl) ⟨2308955, by rfl⟩ : syracuseStep 3078607 = 4617911) B4617911
theorem B1825231 : Blo 1823613 1825231 := bstep (se 1 (by rfl) ⟨1368923, by rfl⟩ : syracuseStep 1825231 = 2737847) B2737847
theorem B1825255 : Blo 1823613 1825255 := bstep (se 1 (by rfl) ⟨1368941, by rfl⟩ : syracuseStep 1825255 = 2737883) B2737883
theorem B1825371 : Blo 1823613 1825371 := bstep (se 1 (by rfl) ⟨1369028, by rfl⟩ : syracuseStep 1825371 = 2738057) B2738057
theorem B31169123 : Blo 1823613 31169123 := bstep (se 1 (by rfl) ⟨23376842, by rfl⟩ : syracuseStep 31169123 = 46753685) B46753685
theorem B6666895 : Blo 1823613 6666895 := bstep (se 1 (by rfl) ⟨5000171, by rfl⟩ : syracuseStep 6666895 = 10000343) B10000343
theorem B1825439 : Blo 1823613 1825439 := bstep (se 1 (by rfl) ⟨1369079, by rfl⟩ : syracuseStep 1825439 = 2738159) B2738159
theorem B1825607 : Blo 1823613 1825607 := bstep (se 1 (by rfl) ⟨1369205, by rfl⟩ : syracuseStep 1825607 = 2738411) B2738411
theorem B3119995 : Blo 1823613 3119995 := bstep (se 1 (by rfl) ⟨2339996, by rfl⟩ : syracuseStep 3119995 = 4679993) B4679993
theorem B1948583 : Blo 1823613 1948583 := bstep (se 1 (by rfl) ⟨1461437, by rfl⟩ : syracuseStep 1948583 = 2922875) B2922875
theorem B7789547 : Blo 1823613 7789547 := bstep (se 1 (by rfl) ⟨5842160, by rfl⟩ : syracuseStep 7789547 = 11684321) B11684321
theorem B47381597 : Blo 1823613 47381597 := bstep (se 3 (by rfl) ⟨8884049, by rfl⟩ : syracuseStep 47381597 = 17768099) B17768099
theorem B4103495 : Blo 1823613 4103495 := bstep (se 1 (by rfl) ⟨3077621, by rfl⟩ : syracuseStep 4103495 = 6155243) B6155243
theorem B2465095 : Blo 1823613 2465095 := bstep (se 1 (by rfl) ⟨1848821, by rfl⟩ : syracuseStep 2465095 = 3697643) B3697643
theorem B4103531 : Blo 1823613 4103531 := bstep (se 1 (by rfl) ⟨3077648, by rfl⟩ : syracuseStep 4103531 = 6155297) B6155297
theorem B2735567 : Blo 1823613 2735567 := bstep (se 1 (by rfl) ⟨2051675, by rfl⟩ : syracuseStep 2735567 = 4103351) B4103351
theorem B4103657 : Blo 1823613 4103657 := bstep (se 2 (by rfl) ⟨1538871, by rfl⟩ : syracuseStep 4103657 = 3077743) B3077743
theorem B3898943 : Blo 1823613 3898943 := bstep (se 1 (by rfl) ⟨2924207, by rfl⟩ : syracuseStep 3898943 = 5848415) B5848415
theorem B4103801 : Blo 1823613 4103801 := bstep (se 2 (by rfl) ⟨1538925, by rfl⟩ : syracuseStep 4103801 = 3077851) B3077851
theorem B20266631 : Blo 1823613 20266631 := bstep (se 1 (by rfl) ⟨15199973, by rfl⟩ : syracuseStep 20266631 = 30399947) B30399947
theorem B216293003 : Blo 1823613 216293003 := bstep (se 1 (by rfl) ⟨162219752, by rfl⟩ : syracuseStep 216293003 = 324439505) B324439505
theorem B3079903 : Blo 1823613 3079903 := bstep (se 1 (by rfl) ⟨2309927, by rfl⟩ : syracuseStep 3079903 = 4619855) B4619855
theorem B6160103 : Blo 1823613 6160103 := bstep (se 1 (by rfl) ⟨4620077, by rfl⟩ : syracuseStep 6160103 = 9240155) B9240155
theorem B2735951 : Blo 1823613 2735951 := bstep (se 1 (by rfl) ⟨2051963, by rfl⟩ : syracuseStep 2735951 = 4103927) B4103927
theorem B2736071 : Blo 1823613 2736071 := bstep (se 1 (by rfl) ⟨2052053, by rfl⟩ : syracuseStep 2736071 = 4104107) B4104107
theorem B4104287 : Blo 1823613 4104287 := bstep (se 1 (by rfl) ⟨3078215, by rfl⟩ : syracuseStep 4104287 = 6156431) B6156431
theorem B13336721 : Blo 1823613 13336721 := bstep (se 2 (by rfl) ⟨5001270, by rfl⟩ : syracuseStep 13336721 = 10002541) B10002541
theorem B9863363 : Blo 1823613 9863363 := bstep (se 1 (by rfl) ⟨7397522, by rfl⟩ : syracuseStep 9863363 = 14795045) B14795045
theorem B2736335 : Blo 1823613 2736335 := bstep (se 1 (by rfl) ⟨2052251, by rfl⟩ : syracuseStep 2736335 = 4104503) B4104503
theorem B4620523 : Blo 1823613 4620523 := bstep (se 1 (by rfl) ⟨3465392, by rfl⟩ : syracuseStep 4620523 = 6930785) B6930785
theorem B4104431 : Blo 1823613 4104431 := bstep (se 1 (by rfl) ⟨3078323, by rfl⟩ : syracuseStep 4104431 = 6156647) B6156647
theorem B6930755 : Blo 1823613 6930755 := bstep (se 1 (by rfl) ⟨5198066, by rfl⟩ : syracuseStep 6930755 = 10396133) B10396133
theorem B23380487 : Blo 1823613 23380487 := bstep (se 1 (by rfl) ⟨17535365, by rfl⟩ : syracuseStep 23380487 = 35070731) B35070731
theorem B4620827 : Blo 1823613 4620827 := bstep (se 1 (by rfl) ⟨3465620, by rfl⟩ : syracuseStep 4620827 = 6931241) B6931241
theorem B84263489 : Blo 1823613 84263489 := bstep (se 2 (by rfl) ⟨31598808, by rfl⟩ : syracuseStep 84263489 = 63197617) B63197617
theorem B28099169 : Blo 1823613 28099169 := bstep (se 2 (by rfl) ⟨10537188, by rfl⟩ : syracuseStep 28099169 = 21074377) B21074377
theorem B4104809 : Blo 1823613 4104809 := bstep (se 2 (by rfl) ⟨1539303, by rfl⟩ : syracuseStep 4104809 = 3078607) B3078607
theorem B16646975 : Blo 1823613 16646975 := bstep (se 1 (by rfl) ⟨12485231, by rfl⟩ : syracuseStep 16646975 = 24970463) B24970463
theorem B8889193 : Blo 1823613 8889193 := bstep (se 2 (by rfl) ⟨3333447, by rfl⟩ : syracuseStep 8889193 = 6666895) B6666895
theorem B2737019 : Blo 1823613 2737019 := bstep (se 1 (by rfl) ⟨2052764, by rfl⟩ : syracuseStep 2737019 = 4105529) B4105529
theorem B2737145 : Blo 1823613 2737145 := bstep (se 2 (by rfl) ⟨1026429, by rfl⟩ : syracuseStep 2737145 = 2052859) B2052859
theorem B2737199 : Blo 1823613 2737199 := bstep (se 1 (by rfl) ⟨2052899, by rfl⟩ : syracuseStep 2737199 = 4105799) B4105799
theorem B2737319 : Blo 1823613 2737319 := bstep (se 1 (by rfl) ⟨2052989, by rfl⟩ : syracuseStep 2737319 = 4105979) B4105979
theorem B9241775 : Blo 1823613 9241775 := bstep (se 1 (by rfl) ⟨6931331, by rfl⟩ : syracuseStep 9241775 = 13862663) B13862663
theorem B4105439 : Blo 1823613 4105439 := bstep (se 1 (by rfl) ⟨3079079, by rfl⟩ : syracuseStep 4105439 = 6158159) B6158159
theorem B2737511 : Blo 1823613 2737511 := bstep (se 1 (by rfl) ⟨2053133, by rfl⟩ : syracuseStep 2737511 = 4106267) B4106267
theorem B5195447 : Blo 1823613 5195447 := bstep (se 1 (by rfl) ⟨3896585, by rfl⟩ : syracuseStep 5195447 = 7793171) B7793171
theorem B19728107 : Blo 1823613 19728107 := bstep (se 1 (by rfl) ⟨14796080, by rfl⟩ : syracuseStep 19728107 = 29592161) B29592161
theorem B3286793 : Blo 1823613 3286793 := bstep (se 2 (by rfl) ⟨1232547, by rfl⟩ : syracuseStep 3286793 = 2465095) B2465095
theorem B2738153 : Blo 1823613 2738153 := bstep (se 2 (by rfl) ⟨1026807, by rfl⟩ : syracuseStep 2738153 = 2053615) B2053615
theorem B2738297 : Blo 1823613 2738297 := bstep (se 2 (by rfl) ⟨1026861, by rfl⟩ : syracuseStep 2738297 = 2053723) B2053723
theorem B4106537 : Blo 1823613 4106537 := bstep (se 2 (by rfl) ⟨1539951, by rfl⟩ : syracuseStep 4106537 = 3079903) B3079903
theorem B10389869 : Blo 1823613 10389869 := bstep (se 3 (by rfl) ⟨1948100, by rfl⟩ : syracuseStep 10389869 = 3896201) B3896201
theorem B2599295 : Blo 1823613 2599295 := bstep (se 1 (by rfl) ⟨1949471, by rfl⟩ : syracuseStep 2599295 = 3898943) B3898943
theorem B13511087 : Blo 1823613 13511087 := bstep (se 1 (by rfl) ⟨10133315, by rfl⟩ : syracuseStep 13511087 = 20266631) B20266631
theorem B5196221 : Blo 1823613 5196221 := bstep (se 3 (by rfl) ⟨974291, by rfl⟩ : syracuseStep 5196221 = 1948583) B1948583
theorem B4106735 : Blo 1823613 4106735 := bstep (se 1 (by rfl) ⟨3080051, by rfl⟩ : syracuseStep 4106735 = 6160103) B6160103
theorem B16640633 : Blo 1823613 16640633 := bstep (se 2 (by rfl) ⟨6240237, by rfl⟩ : syracuseStep 16640633 = 12480475) B12480475
theorem B4107167 : Blo 1823613 4107167 := bstep (se 1 (by rfl) ⟨3080375, by rfl⟩ : syracuseStep 4107167 = 6160751) B6160751
theorem B5196791 : Blo 1823613 5196791 := bstep (se 1 (by rfl) ⟨3897593, by rfl⟩ : syracuseStep 5196791 = 7795187) B7795187
theorem B10390619 : Blo 1823613 10390619 := bstep (se 1 (by rfl) ⟨7792964, by rfl⟩ : syracuseStep 10390619 = 15585929) B15585929
theorem B23121067 : Blo 1823613 23121067 := bstep (se 1 (by rfl) ⟨17340800, by rfl⟩ : syracuseStep 23121067 = 34681601) B34681601
theorem B133131437 : Blo 1823613 133131437 := bstep (se 3 (by rfl) ⟨24962144, by rfl⟩ : syracuseStep 133131437 = 49924289) B49924289
theorem B19737881 : Blo 1823613 19737881 := bstep (se 2 (by rfl) ⟨7401705, by rfl⟩ : syracuseStep 19737881 = 14803411) B14803411
theorem B9866605 : Blo 1823613 9866605 := bstep (se 3 (by rfl) ⟨1849988, by rfl⟩ : syracuseStep 9866605 = 3699977) B3699977
theorem B31182245 : Blo 1823613 31182245 := bstep (se 4 (by rfl) ⟨2923335, by rfl⟩ : syracuseStep 31182245 = 5846671) B5846671
theorem B11685323 : Blo 1823613 11685323 := bstep (se 1 (by rfl) ⟨8763992, by rfl⟩ : syracuseStep 11685323 = 17527985) B17527985
theorem B11243087 : Blo 1823613 11243087 := bstep (se 1 (by rfl) ⟨8432315, by rfl⟩ : syracuseStep 11243087 = 16864631) B16864631
theorem B2051815 : Blo 1823613 2051815 := bstep (se 1 (by rfl) ⟨1538861, by rfl⟩ : syracuseStep 2051815 = 3077723) B3077723
theorem B7794863 : Blo 1823613 7794863 := bstep (se 1 (by rfl) ⟨5846147, by rfl⟩ : syracuseStep 7794863 = 11692295) B11692295
theorem B20779415 : Blo 1823613 20779415 := bstep (se 1 (by rfl) ⟨15584561, by rfl⟩ : syracuseStep 20779415 = 31169123) B31169123
theorem B42136199 : Blo 1823613 42136199 := bstep (se 1 (by rfl) ⟨31602149, by rfl⟩ : syracuseStep 42136199 = 63204299) B63204299
theorem B59978407 : Blo 1823613 59978407 := bstep (se 1 (by rfl) ⟨44983805, by rfl⟩ : syracuseStep 59978407 = 89967611) B89967611
theorem B4617071 : Blo 1823613 4617071 := bstep (se 1 (by rfl) ⟨3462803, by rfl⟩ : syracuseStep 4617071 = 6925607) B6925607
theorem B1823711 : Blo 1823613 1823711 := bstep (se 1 (by rfl) ⟨1367783, by rfl⟩ : syracuseStep 1823711 = 2735567) B2735567
theorem B2921465 : Blo 1823613 2921465 := bstep (se 2 (by rfl) ⟨1095549, by rfl⟩ : syracuseStep 2921465 = 2191099) B2191099
theorem B1823967 : Blo 1823613 1823967 := bstep (se 1 (by rfl) ⟨1367975, by rfl⟩ : syracuseStep 1823967 = 2735951) B2735951
theorem B20772125 : Blo 1823613 20772125 := bstep (se 3 (by rfl) ⟨3894773, by rfl⟩ : syracuseStep 20772125 = 7789547) B7789547
theorem B1824047 : Blo 1823613 1824047 := bstep (se 1 (by rfl) ⟨1368035, by rfl⟩ : syracuseStep 1824047 = 2736071) B2736071
theorem B5846519 : Blo 1823613 5846519 := bstep (se 1 (by rfl) ⟨4384889, by rfl⟩ : syracuseStep 5846519 = 8769779) B8769779
theorem B3331579 : Blo 1823613 3331579 := bstep (se 1 (by rfl) ⟨2498684, by rfl⟩ : syracuseStep 3331579 = 4997369) B4997369
theorem B1824287 : Blo 1823613 1824287 := bstep (se 1 (by rfl) ⟨1368215, by rfl⟩ : syracuseStep 1824287 = 2736431) B2736431
theorem B1824447 : Blo 1823613 1824447 := bstep (se 1 (by rfl) ⟨1368335, by rfl⟩ : syracuseStep 1824447 = 2736671) B2736671
theorem B3077959 : Blo 1823613 3077959 := bstep (se 1 (by rfl) ⟨2308469, by rfl⟩ : syracuseStep 3077959 = 4616939) B4616939
theorem B35067725 : Blo 1823613 35067725 := bstep (se 3 (by rfl) ⟨6575198, by rfl⟩ : syracuseStep 35067725 = 13150397) B13150397
theorem B19732481 : Blo 1823613 19732481 := bstep (se 2 (by rfl) ⟨7399680, by rfl⟩ : syracuseStep 19732481 = 14799361) B14799361
theorem B3897371 : Blo 1823613 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B1824895 : Blo 1823613 1824895 := bstep (se 1 (by rfl) ⟨1368671, by rfl⟩ : syracuseStep 1824895 = 2737343) B2737343
theorem B1824991 : Blo 1823613 1824991 := bstep (se 1 (by rfl) ⟨1368743, by rfl⟩ : syracuseStep 1824991 = 2737487) B2737487
theorem B1825051 : Blo 1823613 1825051 := bstep (se 1 (by rfl) ⟨1368788, by rfl⟩ : syracuseStep 1825051 = 2737577) B2737577
theorem B4618579 : Blo 1823613 4618579 := bstep (se 1 (by rfl) ⟨3463934, by rfl⟩ : syracuseStep 4618579 = 6927869) B6927869
theorem B1825151 : Blo 1823613 1825151 := bstep (se 1 (by rfl) ⟨1368863, by rfl⟩ : syracuseStep 1825151 = 2737727) B2737727
theorem B1825179 : Blo 1823613 1825179 := bstep (se 1 (by rfl) ⟨1368884, by rfl⟩ : syracuseStep 1825179 = 2737769) B2737769
theorem B4159993 : Blo 1823613 4159993 := bstep (se 2 (by rfl) ⟨1559997, by rfl⟩ : syracuseStep 4159993 = 3119995) B3119995
theorem B8772239 : Blo 1823613 8772239 := bstep (se 1 (by rfl) ⟨6579179, by rfl⟩ : syracuseStep 8772239 = 13158359) B13158359
theorem B17783459 : Blo 1823613 17783459 := bstep (se 1 (by rfl) ⟨13337594, by rfl⟩ : syracuseStep 17783459 = 26675189) B26675189
theorem B1825471 : Blo 1823613 1825471 := bstep (se 1 (by rfl) ⟨1369103, by rfl⟩ : syracuseStep 1825471 = 2738207) B2738207
theorem B4619015 : Blo 1823613 4619015 := bstep (se 1 (by rfl) ⟨3464261, by rfl⟩ : syracuseStep 4619015 = 6928523) B6928523
theorem B6576959 : Blo 1823613 6576959 := bstep (se 1 (by rfl) ⟨4932719, by rfl⟩ : syracuseStep 6576959 = 9865439) B9865439
theorem B1825599 : Blo 1823613 1825599 := bstep (se 1 (by rfl) ⟨1369199, by rfl⟩ : syracuseStep 1825599 = 2738399) B2738399
theorem B23108503 : Blo 1823613 23108503 := bstep (se 1 (by rfl) ⟨17331377, by rfl⟩ : syracuseStep 23108503 = 34662755) B34662755
theorem B3464299 : Blo 1823613 3464299 := bstep (se 1 (by rfl) ⟨2598224, by rfl⟩ : syracuseStep 3464299 = 5196449) B5196449
theorem B972627335 : Blo 1823613 972627335 := bstep (se 1 (by rfl) ⟨729470501, by rfl⟩ : syracuseStep 972627335 = 1458941003) B1458941003
theorem B31587731 : Blo 1823613 31587731 := bstep (se 1 (by rfl) ⟨23690798, by rfl⟩ : syracuseStep 31587731 = 47381597) B47381597
theorem B39476717 : Blo 1823613 39476717 := bstep (se 3 (by rfl) ⟨7401884, by rfl⟩ : syracuseStep 39476717 = 14803769) B14803769
theorem B2735663 : Blo 1823613 2735663 := bstep (se 1 (by rfl) ⟨2051747, by rfl⟩ : syracuseStep 2735663 = 4103495) B4103495
theorem B2735687 : Blo 1823613 2735687 := bstep (se 1 (by rfl) ⟨2051765, by rfl⟩ : syracuseStep 2735687 = 4103531) B4103531
theorem B2735771 : Blo 1823613 2735771 := bstep (se 1 (by rfl) ⟨2051828, by rfl⟩ : syracuseStep 2735771 = 4103657) B4103657
theorem B2735867 : Blo 1823613 2735867 := bstep (se 1 (by rfl) ⟨2051900, by rfl⟩ : syracuseStep 2735867 = 4103801) B4103801
theorem B144195335 : Blo 1823613 144195335 := bstep (se 1 (by rfl) ⟨108146501, by rfl⟩ : syracuseStep 144195335 = 216293003) B216293003
theorem B10395449 : Blo 1823613 10395449 := bstep (se 2 (by rfl) ⟨3898293, by rfl⟩ : syracuseStep 10395449 = 7796587) B7796587
theorem B19717985 : Blo 1823613 19717985 := bstep (se 2 (by rfl) ⟨7394244, by rfl⟩ : syracuseStep 19717985 = 14788489) B14788489
theorem B2736191 : Blo 1823613 2736191 := bstep (se 1 (by rfl) ⟨2052143, by rfl⟩ : syracuseStep 2736191 = 4104287) B4104287
theorem B2736287 : Blo 1823613 2736287 := bstep (se 1 (by rfl) ⟨2052215, by rfl⟩ : syracuseStep 2736287 = 4104431) B4104431
theorem B4620503 : Blo 1823613 4620503 := bstep (se 1 (by rfl) ⟨3465377, by rfl⟩ : syracuseStep 4620503 = 6930755) B6930755
theorem B13852943 : Blo 1823613 13852943 := bstep (se 1 (by rfl) ⟨10389707, by rfl⟩ : syracuseStep 13852943 = 20779415) B20779415
theorem B6160697 : Blo 1823613 6160697 := bstep (se 2 (by rfl) ⟨2310261, by rfl⟩ : syracuseStep 6160697 = 4620523) B4620523
theorem B3080551 : Blo 1823613 3080551 := bstep (se 1 (by rfl) ⟨2310413, by rfl⟩ : syracuseStep 3080551 = 4620827) B4620827
theorem B2736539 : Blo 1823613 2736539 := bstep (se 1 (by rfl) ⟨2052404, by rfl⟩ : syracuseStep 2736539 = 4104809) B4104809
theorem B28090799 : Blo 1823613 28090799 := bstep (se 1 (by rfl) ⟨21068099, by rfl⟩ : syracuseStep 28090799 = 42136199) B42136199
theorem B5546657 : Blo 1823613 5546657 := bstep (se 2 (by rfl) ⟨2079996, by rfl⟩ : syracuseStep 5546657 = 4159993) B4159993
theorem B6161183 : Blo 1823613 6161183 := bstep (se 1 (by rfl) ⟨4620887, by rfl⟩ : syracuseStep 6161183 = 9241775) B9241775
theorem B2736959 : Blo 1823613 2736959 := bstep (se 1 (by rfl) ⟨2052719, by rfl⟩ : syracuseStep 2736959 = 4105439) B4105439
theorem B79971209 : Blo 1823613 79971209 := bstep (se 2 (by rfl) ⟨29989203, by rfl⟩ : syracuseStep 79971209 = 59978407) B59978407
theorem B6931453 : Blo 1823613 6931453 := bstep (se 3 (by rfl) ⟨1299647, by rfl⟩ : syracuseStep 6931453 = 2599295) B2599295
theorem B30811337 : Blo 1823613 30811337 := bstep (se 2 (by rfl) ⟨11554251, by rfl⟩ : syracuseStep 30811337 = 23108503) B23108503
theorem B2598247 : Blo 1823613 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B2737691 : Blo 1823613 2737691 := bstep (se 1 (by rfl) ⟨2053268, by rfl⟩ : syracuseStep 2737691 = 4106537) B4106537
theorem B30828089 : Blo 1823613 30828089 := bstep (se 2 (by rfl) ⟨11560533, by rfl⟩ : syracuseStep 30828089 = 23121067) B23121067
theorem B2737823 : Blo 1823613 2737823 := bstep (se 1 (by rfl) ⟨2053367, by rfl⟩ : syracuseStep 2737823 = 4106735) B4106735
theorem B11093755 : Blo 1823613 11093755 := bstep (se 1 (by rfl) ⟨8320316, by rfl⟩ : syracuseStep 11093755 = 16640633) B16640633
theorem B11855639 : Blo 1823613 11855639 := bstep (se 1 (by rfl) ⟨8891729, by rfl⟩ : syracuseStep 11855639 = 17783459) B17783459
theorem B4384639 : Blo 1823613 4384639 := bstep (se 1 (by rfl) ⟨3288479, by rfl⟩ : syracuseStep 4384639 = 6576959) B6576959
theorem B2738111 : Blo 1823613 2738111 := bstep (se 1 (by rfl) ⟨2053583, by rfl⟩ : syracuseStep 2738111 = 4107167) B4107167
theorem B4442105 : Blo 1823613 4442105 := bstep (se 2 (by rfl) ⟨1665789, by rfl⟩ : syracuseStep 4442105 = 3331579) B3331579
theorem B88754291 : Blo 1823613 88754291 := bstep (se 1 (by rfl) ⟨66565718, by rfl⟩ : syracuseStep 88754291 = 133131437) B133131437
theorem B13158587 : Blo 1823613 13158587 := bstep (se 1 (by rfl) ⟨9868940, by rfl⟩ : syracuseStep 13158587 = 19737881) B19737881
theorem B8891147 : Blo 1823613 8891147 := bstep (se 1 (by rfl) ⟨6668360, by rfl⟩ : syracuseStep 8891147 = 13336721) B13336721
theorem B5196575 : Blo 1823613 5196575 := bstep (se 1 (by rfl) ⟨3897431, by rfl⟩ : syracuseStep 5196575 = 7794863) B7794863
theorem B56175659 : Blo 1823613 56175659 := bstep (se 1 (by rfl) ⟨42131744, by rfl⟩ : syracuseStep 56175659 = 84263489) B84263489
theorem B13848083 : Blo 1823613 13848083 := bstep (se 1 (by rfl) ⟨10386062, by rfl⟩ : syracuseStep 13848083 = 20772125) B20772125
theorem B13152071 : Blo 1823613 13152071 := bstep (se 1 (by rfl) ⟨9864053, by rfl⟩ : syracuseStep 13152071 = 19728107) B19728107
theorem B2191195 : Blo 1823613 2191195 := bstep (se 1 (by rfl) ⟨1643396, by rfl⟩ : syracuseStep 2191195 = 3286793) B3286793
theorem B6926579 : Blo 1823613 6926579 := bstep (se 1 (by rfl) ⟨5194934, by rfl⟩ : syracuseStep 6926579 = 10389869) B10389869
theorem B9007391 : Blo 1823613 9007391 := bstep (se 1 (by rfl) ⟨6755543, by rfl⟩ : syracuseStep 9007391 = 13511087) B13511087
theorem B6927079 : Blo 1823613 6927079 := bstep (se 1 (by rfl) ⟨5195309, by rfl⟩ : syracuseStep 6927079 = 10390619) B10390619
theorem B648418223 : Blo 1823613 648418223 := bstep (se 1 (by rfl) ⟨486313667, by rfl⟩ : syracuseStep 648418223 = 972627335) B972627335
theorem B21058487 : Blo 1823613 21058487 := bstep (se 1 (by rfl) ⟨15793865, by rfl⟩ : syracuseStep 21058487 = 31587731) B31587731
theorem B20788163 : Blo 1823613 20788163 := bstep (se 1 (by rfl) ⟨15591122, by rfl⟩ : syracuseStep 20788163 = 31182245) B31182245
theorem B26317811 : Blo 1823613 26317811 := bstep (se 1 (by rfl) ⟨19738358, by rfl⟩ : syracuseStep 26317811 = 39476717) B39476717
theorem B1823775 : Blo 1823613 1823775 := bstep (se 1 (by rfl) ⟨1367831, by rfl⟩ : syracuseStep 1823775 = 2735663) B2735663
theorem B1823791 : Blo 1823613 1823791 := bstep (se 1 (by rfl) ⟨1367843, by rfl⟩ : syracuseStep 1823791 = 2735687) B2735687
theorem B1823847 : Blo 1823613 1823847 := bstep (se 1 (by rfl) ⟨1367885, by rfl⟩ : syracuseStep 1823847 = 2735771) B2735771
theorem B1823911 : Blo 1823613 1823911 := bstep (se 1 (by rfl) ⟨1367933, by rfl⟩ : syracuseStep 1823911 = 2735867) B2735867
theorem B96130223 : Blo 1823613 96130223 := bstep (se 1 (by rfl) ⟨72097667, by rfl⟩ : syracuseStep 96130223 = 144195335) B144195335
theorem B13145323 : Blo 1823613 13145323 := bstep (se 1 (by rfl) ⟨9858992, by rfl⟩ : syracuseStep 13145323 = 19717985) B19717985
theorem B6575575 : Blo 1823613 6575575 := bstep (se 1 (by rfl) ⟨4931681, by rfl⟩ : syracuseStep 6575575 = 9863363) B9863363
theorem B1824223 : Blo 1823613 1824223 := bstep (se 1 (by rfl) ⟨1368167, by rfl⟩ : syracuseStep 1824223 = 2736335) B2736335
theorem B15586991 : Blo 1823613 15586991 := bstep (se 1 (by rfl) ⟨11690243, by rfl⟩ : syracuseStep 15586991 = 23380487) B23380487
theorem B18732779 : Blo 1823613 18732779 := bstep (se 1 (by rfl) ⟨14049584, by rfl⟩ : syracuseStep 18732779 = 28099169) B28099169
theorem B6158105 : Blo 1823613 6158105 := bstep (se 2 (by rfl) ⟨2309289, by rfl⟩ : syracuseStep 6158105 = 4618579) B4618579
theorem B11097983 : Blo 1823613 11097983 := bstep (se 1 (by rfl) ⟨8323487, by rfl⟩ : syracuseStep 11097983 = 16646975) B16646975
theorem B3078047 : Blo 1823613 3078047 := bstep (se 1 (by rfl) ⟨2308535, by rfl⟩ : syracuseStep 3078047 = 4617071) B4617071
theorem B1824679 : Blo 1823613 1824679 := bstep (se 1 (by rfl) ⟨1368509, by rfl⟩ : syracuseStep 1824679 = 2737019) B2737019
theorem B1824763 : Blo 1823613 1824763 := bstep (se 1 (by rfl) ⟨1368572, by rfl⟩ : syracuseStep 1824763 = 2737145) B2737145
theorem B1824799 : Blo 1823613 1824799 := bstep (se 1 (by rfl) ⟨1368599, by rfl⟩ : syracuseStep 1824799 = 2737199) B2737199
theorem B1824879 : Blo 1823613 1824879 := bstep (se 1 (by rfl) ⟨1368659, by rfl⟩ : syracuseStep 1824879 = 2737319) B2737319
theorem B1825007 : Blo 1823613 1825007 := bstep (se 1 (by rfl) ⟨1368755, by rfl⟩ : syracuseStep 1825007 = 2737511) B2737511
theorem B3897679 : Blo 1823613 3897679 := bstep (se 1 (by rfl) ⟨2923259, by rfl⟩ : syracuseStep 3897679 = 5846519) B5846519
theorem B3463631 : Blo 1823613 3463631 := bstep (se 1 (by rfl) ⟨2597723, by rfl⟩ : syracuseStep 3463631 = 5195447) B5195447
theorem B11852257 : Blo 1823613 11852257 := bstep (se 2 (by rfl) ⟨4444596, by rfl⟩ : syracuseStep 11852257 = 8889193) B8889193
theorem B23378483 : Blo 1823613 23378483 := bstep (se 1 (by rfl) ⟨17533862, by rfl⟩ : syracuseStep 23378483 = 35067725) B35067725
theorem B1825435 : Blo 1823613 1825435 := bstep (se 1 (by rfl) ⟨1369076, by rfl⟩ : syracuseStep 1825435 = 2738153) B2738153
theorem B13154987 : Blo 1823613 13154987 := bstep (se 1 (by rfl) ⟨9866240, by rfl⟩ : syracuseStep 13154987 = 19732481) B19732481
theorem B1825531 : Blo 1823613 1825531 := bstep (se 1 (by rfl) ⟨1369148, by rfl⟩ : syracuseStep 1825531 = 2738297) B2738297
theorem B4619065 : Blo 1823613 4619065 := bstep (se 2 (by rfl) ⟨1732149, by rfl⟩ : syracuseStep 4619065 = 3464299) B3464299
theorem B3464147 : Blo 1823613 3464147 := bstep (se 1 (by rfl) ⟨2598110, by rfl⟩ : syracuseStep 3464147 = 5196221) B5196221
theorem B5848159 : Blo 1823613 5848159 := bstep (se 1 (by rfl) ⟨4386119, by rfl⟩ : syracuseStep 5848159 = 8772239) B8772239
theorem B13155473 : Blo 1823613 13155473 := bstep (se 2 (by rfl) ⟨4933302, by rfl⟩ : syracuseStep 13155473 = 9866605) B9866605
theorem B3079343 : Blo 1823613 3079343 := bstep (se 1 (by rfl) ⟨2309507, by rfl⟩ : syracuseStep 3079343 = 4619015) B4619015
theorem B3464527 : Blo 1823613 3464527 := bstep (se 1 (by rfl) ⟨2598395, by rfl⟩ : syracuseStep 3464527 = 5196791) B5196791
theorem B7790215 : Blo 1823613 7790215 := bstep (se 1 (by rfl) ⟨5842661, by rfl⟩ : syracuseStep 7790215 = 11685323) B11685323
theorem B2735753 : Blo 1823613 2735753 := bstep (se 2 (by rfl) ⟨1025907, by rfl⟩ : syracuseStep 2735753 = 2051815) B2051815
theorem B7495391 : Blo 1823613 7495391 := bstep (se 1 (by rfl) ⟨5621543, by rfl⟩ : syracuseStep 7495391 = 11243087) B11243087
theorem B4103945 : Blo 1823613 4103945 := bstep (se 2 (by rfl) ⟨1538979, by rfl⟩ : syracuseStep 4103945 = 3077959) B3077959
theorem B6930299 : Blo 1823613 6930299 := bstep (se 1 (by rfl) ⟨5197724, by rfl⟩ : syracuseStep 6930299 = 10395449) B10395449
theorem B7790573 : Blo 1823613 7790573 := bstep (se 3 (by rfl) ⟨1460732, by rfl⟩ : syracuseStep 7790573 = 2921465) B2921465
theorem B3080335 : Blo 1823613 3080335 := bstep (se 1 (by rfl) ⟨2310251, by rfl⟩ : syracuseStep 3080335 = 4620503) B4620503
theorem B6004927 : Blo 1823613 6004927 := bstep (se 1 (by rfl) ⟨4503695, by rfl⟩ : syracuseStep 6004927 = 9007391) B9007391
theorem B18727199 : Blo 1823613 18727199 := bstep (se 1 (by rfl) ⟨14045399, by rfl⟩ : syracuseStep 18727199 = 28090799) B28090799
theorem B53314139 : Blo 1823613 53314139 := bstep (se 1 (by rfl) ⟨39985604, by rfl⟩ : syracuseStep 53314139 = 79971209) B79971209
theorem B15803009 : Blo 1823613 15803009 := bstep (se 2 (by rfl) ⟨5926128, by rfl⟩ : syracuseStep 15803009 = 11852257) B11852257
theorem B64086815 : Blo 1823613 64086815 := bstep (se 1 (by rfl) ⟨48065111, by rfl⟩ : syracuseStep 64086815 = 96130223) B96130223
theorem B4105403 : Blo 1823613 4105403 := bstep (se 1 (by rfl) ⟨3079052, by rfl⟩ : syracuseStep 4105403 = 6158105) B6158105
theorem B9241937 : Blo 1823613 9241937 := bstep (se 2 (by rfl) ⟨3465726, by rfl⟩ : syracuseStep 9241937 = 6931453) B6931453
theorem B8767433 : Blo 1823613 8767433 := bstep (se 2 (by rfl) ⟨3287787, by rfl⟩ : syracuseStep 8767433 = 6575575) B6575575
theorem B35072189 : Blo 1823613 35072189 := bstep (se 3 (by rfl) ⟨6576035, by rfl⟩ : syracuseStep 35072189 = 13152071) B13152071
theorem B9235295 : Blo 1823613 9235295 := bstep (se 1 (by rfl) ⟨6926471, by rfl⟩ : syracuseStep 9235295 = 13852943) B13852943
theorem B4107131 : Blo 1823613 4107131 := bstep (se 1 (by rfl) ⟨3080348, by rfl⟩ : syracuseStep 4107131 = 6160697) B6160697
theorem B5196905 : Blo 1823613 5196905 := bstep (se 2 (by rfl) ⟨1948839, by rfl⟩ : syracuseStep 5196905 = 3897679) B3897679
theorem B4107401 : Blo 1823613 4107401 := bstep (se 2 (by rfl) ⟨1540275, by rfl⟩ : syracuseStep 4107401 = 3080551) B3080551
theorem B4107455 : Blo 1823613 4107455 := bstep (se 1 (by rfl) ⟨3080591, by rfl⟩ : syracuseStep 4107455 = 6161183) B6161183
theorem B20540891 : Blo 1823613 20540891 := bstep (se 1 (by rfl) ⟨15405668, by rfl⟩ : syracuseStep 20540891 = 30811337) B30811337
theorem B9236105 : Blo 1823613 9236105 := bstep (se 2 (by rfl) ⟨3463539, by rfl⟩ : syracuseStep 9236105 = 6927079) B6927079
theorem B10391327 : Blo 1823613 10391327 := bstep (se 1 (by rfl) ⟨7793495, by rfl⟩ : syracuseStep 10391327 = 15586991) B15586991
theorem B12488519 : Blo 1823613 12488519 := bstep (se 1 (by rfl) ⟨9366389, by rfl⟩ : syracuseStep 12488519 = 18732779) B18732779
theorem B2052031 : Blo 1823613 2052031 := bstep (se 1 (by rfl) ⟨1539023, by rfl⟩ : syracuseStep 2052031 = 3078047) B3078047
theorem B2961403 : Blo 1823613 2961403 := bstep (se 1 (by rfl) ⟨2221052, by rfl⟩ : syracuseStep 2961403 = 4442105) B4442105
theorem B17527097 : Blo 1823613 17527097 := bstep (se 2 (by rfl) ⟨6572661, by rfl⟩ : syracuseStep 17527097 = 13145323) B13145323
theorem B15585655 : Blo 1823613 15585655 := bstep (se 1 (by rfl) ⟨11689241, by rfl⟩ : syracuseStep 15585655 = 23378483) B23378483
theorem B14791085 : Blo 1823613 14791085 := bstep (se 3 (by rfl) ⟨2773328, by rfl⟩ : syracuseStep 14791085 = 5546657) B5546657
theorem B8769991 : Blo 1823613 8769991 := bstep (se 1 (by rfl) ⟨6577493, by rfl⟩ : syracuseStep 8769991 = 13154987) B13154987
theorem B5927431 : Blo 1823613 5927431 := bstep (se 1 (by rfl) ⟨4445573, by rfl⟩ : syracuseStep 5927431 = 8891147) B8891147
theorem B13857317 : Blo 1823613 13857317 := bstep (se 4 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 13857317 = 2598247) B2598247
theorem B37450439 : Blo 1823613 37450439 := bstep (se 1 (by rfl) ⟨28087829, by rfl⟩ : syracuseStep 37450439 = 56175659) B56175659
theorem B8770315 : Blo 1823613 8770315 := bstep (se 1 (by rfl) ⟨6577736, by rfl⟩ : syracuseStep 8770315 = 13155473) B13155473
theorem B2052895 : Blo 1823613 2052895 := bstep (se 1 (by rfl) ⟨1539671, by rfl⟩ : syracuseStep 2052895 = 3079343) B3079343
theorem B14791673 : Blo 1823613 14791673 := bstep (se 2 (by rfl) ⟨5546877, by rfl⟩ : syracuseStep 14791673 = 11093755) B11093755
theorem B29594621 : Blo 1823613 29594621 := bstep (se 3 (by rfl) ⟨5548991, by rfl⟩ : syracuseStep 29594621 = 11097983) B11097983
theorem B1823835 : Blo 1823613 1823835 := bstep (se 1 (by rfl) ⟨1367876, by rfl⟩ : syracuseStep 1823835 = 2735753) B2735753
theorem B2921593 : Blo 1823613 2921593 := bstep (se 2 (by rfl) ⟨1095597, by rfl⟩ : syracuseStep 2921593 = 2191195) B2191195
theorem B1729115261 : Blo 1823613 1729115261 := bstep (se 3 (by rfl) ⟨324209111, by rfl⟩ : syracuseStep 1729115261 = 648418223) B648418223
theorem B5846185 : Blo 1823613 5846185 := bstep (se 2 (by rfl) ⟨2192319, by rfl⟩ : syracuseStep 5846185 = 4384639) B4384639
theorem B9237725 : Blo 1823613 9237725 := bstep (se 3 (by rfl) ⟨1732073, by rfl⟩ : syracuseStep 9237725 = 3464147) B3464147
theorem B1824127 : Blo 1823613 1824127 := bstep (se 1 (by rfl) ⟨1368095, by rfl⟩ : syracuseStep 1824127 = 2736191) B2736191
theorem B1824191 : Blo 1823613 1824191 := bstep (se 1 (by rfl) ⟨1368143, by rfl⟩ : syracuseStep 1824191 = 2736287) B2736287
theorem B4617719 : Blo 1823613 4617719 := bstep (se 1 (by rfl) ⟨3463289, by rfl⟩ : syracuseStep 4617719 = 6926579) B6926579
theorem B1824359 : Blo 1823613 1824359 := bstep (se 1 (by rfl) ⟨1368269, by rfl⟩ : syracuseStep 1824359 = 2736539) B2736539
theorem B1824639 : Blo 1823613 1824639 := bstep (se 1 (by rfl) ⟨1368479, by rfl⟩ : syracuseStep 1824639 = 2736959) B2736959
theorem B14038991 : Blo 1823613 14038991 := bstep (se 1 (by rfl) ⟨10529243, by rfl⟩ : syracuseStep 14038991 = 21058487) B21058487
theorem B13858775 : Blo 1823613 13858775 := bstep (se 1 (by rfl) ⟨10394081, by rfl⟩ : syracuseStep 13858775 = 20788163) B20788163
theorem B17545207 : Blo 1823613 17545207 := bstep (se 1 (by rfl) ⟨13158905, by rfl⟩ : syracuseStep 17545207 = 26317811) B26317811
theorem B1825127 : Blo 1823613 1825127 := bstep (se 1 (by rfl) ⟨1368845, by rfl⟩ : syracuseStep 1825127 = 2737691) B2737691
theorem B20552059 : Blo 1823613 20552059 := bstep (se 1 (by rfl) ⟨15414044, by rfl⟩ : syracuseStep 20552059 = 30828089) B30828089
theorem B6158753 : Blo 1823613 6158753 := bstep (se 2 (by rfl) ⟨2309532, by rfl⟩ : syracuseStep 6158753 = 4619065) B4619065
theorem B1825215 : Blo 1823613 1825215 := bstep (se 1 (by rfl) ⟨1368911, by rfl⟩ : syracuseStep 1825215 = 2737823) B2737823
theorem B7903759 : Blo 1823613 7903759 := bstep (se 1 (by rfl) ⟨5927819, by rfl⟩ : syracuseStep 7903759 = 11855639) B11855639
theorem B1825407 : Blo 1823613 1825407 := bstep (se 1 (by rfl) ⟨1369055, by rfl⟩ : syracuseStep 1825407 = 2738111) B2738111
theorem B59169527 : Blo 1823613 59169527 := bstep (se 1 (by rfl) ⟨44377145, by rfl⟩ : syracuseStep 59169527 = 88754291) B88754291
theorem B8772391 : Blo 1823613 8772391 := bstep (se 1 (by rfl) ⟨6579293, by rfl⟩ : syracuseStep 8772391 = 13158587) B13158587
theorem B7797545 : Blo 1823613 7797545 := bstep (se 2 (by rfl) ⟨2924079, by rfl⟩ : syracuseStep 7797545 = 5848159) B5848159
theorem B2309087 : Blo 1823613 2309087 := bstep (se 1 (by rfl) ⟨1731815, by rfl⟩ : syracuseStep 2309087 = 3463631) B3463631
theorem B4619369 : Blo 1823613 4619369 := bstep (se 2 (by rfl) ⟨1732263, by rfl⟩ : syracuseStep 4619369 = 3464527) B3464527
theorem B3464383 : Blo 1823613 3464383 := bstep (se 1 (by rfl) ⟨2598287, by rfl⟩ : syracuseStep 3464383 = 5196575) B5196575
theorem B10386953 : Blo 1823613 10386953 := bstep (se 2 (by rfl) ⟨3895107, by rfl⟩ : syracuseStep 10386953 = 7790215) B7790215
theorem B9232055 : Blo 1823613 9232055 := bstep (se 1 (by rfl) ⟨6924041, by rfl⟩ : syracuseStep 9232055 = 13848083) B13848083
theorem B4996927 : Blo 1823613 4996927 := bstep (se 1 (by rfl) ⟨3747695, by rfl⟩ : syracuseStep 4996927 = 7495391) B7495391
theorem B2735963 : Blo 1823613 2735963 := bstep (se 1 (by rfl) ⟨2051972, by rfl⟩ : syracuseStep 2735963 = 4103945) B4103945
theorem B4620199 : Blo 1823613 4620199 := bstep (se 1 (by rfl) ⟨3465149, by rfl⟩ : syracuseStep 4620199 = 6930299) B6930299
theorem B5193715 : Blo 1823613 5193715 := bstep (se 1 (by rfl) ⟨3895286, by rfl⟩ : syracuseStep 5193715 = 7790573) B7790573
theorem B12484799 : Blo 1823613 12484799 := bstep (se 1 (by rfl) ⟨9363599, by rfl⟩ : syracuseStep 12484799 = 18727199) B18727199
theorem B10535339 : Blo 1823613 10535339 := bstep (se 1 (by rfl) ⟨7901504, by rfl⟩ : syracuseStep 10535339 = 15803009) B15803009
theorem B2736935 : Blo 1823613 2736935 := bstep (se 1 (by rfl) ⟨2052701, by rfl⟩ : syracuseStep 2736935 = 4105403) B4105403
theorem B6161291 : Blo 1823613 6161291 := bstep (se 1 (by rfl) ⟨4620968, by rfl⟩ : syracuseStep 6161291 = 9241937) B9241937
theorem B2737193 : Blo 1823613 2737193 := bstep (se 2 (by rfl) ⟨1026447, by rfl⟩ : syracuseStep 2737193 = 2052895) B2052895
theorem B23381459 : Blo 1823613 23381459 := bstep (se 1 (by rfl) ⟨17536094, by rfl⟩ : syracuseStep 23381459 = 35072189) B35072189
theorem B4105835 : Blo 1823613 4105835 := bstep (se 1 (by rfl) ⟨3079376, by rfl⟩ : syracuseStep 4105835 = 6158753) B6158753
theorem B39446351 : Blo 1823613 39446351 := bstep (se 1 (by rfl) ⟨29584763, by rfl⟩ : syracuseStep 39446351 = 59169527) B59169527
theorem B2738087 : Blo 1823613 2738087 := bstep (se 1 (by rfl) ⟨2053565, by rfl⟩ : syracuseStep 2738087 = 4107131) B4107131
theorem B109610981 : Blo 1823613 109610981 := bstep (se 4 (by rfl) ⟨10276029, by rfl⟩ : syracuseStep 109610981 = 20552059) B20552059
theorem B2738267 : Blo 1823613 2738267 := bstep (se 1 (by rfl) ⟨2053700, by rfl⟩ : syracuseStep 2738267 = 4107401) B4107401
theorem B2738303 : Blo 1823613 2738303 := bstep (se 1 (by rfl) ⟨2053727, by rfl⟩ : syracuseStep 2738303 = 4107455) B4107455
theorem B6924635 : Blo 1823613 6924635 := bstep (se 1 (by rfl) ⟨5193476, by rfl⟩ : syracuseStep 6924635 = 10386953) B10386953
theorem B6662569 : Blo 1823613 6662569 := bstep (se 2 (by rfl) ⟨2498463, by rfl⟩ : syracuseStep 6662569 = 4996927) B4996927
theorem B6154703 : Blo 1823613 6154703 := bstep (se 1 (by rfl) ⟨4616027, by rfl⟩ : syracuseStep 6154703 = 9232055) B9232055
theorem B8325679 : Blo 1823613 8325679 := bstep (se 1 (by rfl) ⟨6244259, by rfl⟩ : syracuseStep 8325679 = 12488519) B12488519
theorem B6924953 : Blo 1823613 6924953 := bstep (se 2 (by rfl) ⟨2596857, by rfl⟩ : syracuseStep 6924953 = 5193715) B5193715
theorem B4107113 : Blo 1823613 4107113 := bstep (se 2 (by rfl) ⟨1540167, by rfl⟩ : syracuseStep 4107113 = 3080335) B3080335
theorem B11684731 : Blo 1823613 11684731 := bstep (se 1 (by rfl) ⟨8763548, by rfl⟩ : syracuseStep 11684731 = 17527097) B17527097
theorem B8006569 : Blo 1823613 8006569 := bstep (se 2 (by rfl) ⟨3002463, by rfl⟩ : syracuseStep 8006569 = 6004927) B6004927
theorem B11693321 : Blo 1823613 11693321 := bstep (se 2 (by rfl) ⟨4384995, by rfl⟩ : syracuseStep 11693321 = 8769991) B8769991
theorem B19729747 : Blo 1823613 19729747 := bstep (se 1 (by rfl) ⟨14797310, by rfl⟩ : syracuseStep 19729747 = 29594621) B29594621
theorem B10538345 : Blo 1823613 10538345 := bstep (se 2 (by rfl) ⟨3951879, by rfl⟩ : syracuseStep 10538345 = 7903759) B7903759
theorem B11693753 : Blo 1823613 11693753 := bstep (se 2 (by rfl) ⟨4385157, by rfl⟩ : syracuseStep 11693753 = 8770315) B8770315
theorem B54775709 : Blo 1823613 54775709 := bstep (se 3 (by rfl) ⟨10270445, by rfl⟩ : syracuseStep 54775709 = 20540891) B20540891
theorem B5844955 : Blo 1823613 5844955 := bstep (se 1 (by rfl) ⟨4383716, by rfl⟩ : syracuseStep 5844955 = 8767433) B8767433
theorem B9359327 : Blo 1823613 9359327 := bstep (se 1 (by rfl) ⟨7019495, by rfl⟩ : syracuseStep 9359327 = 14038991) B14038991
theorem B3895457 : Blo 1823613 3895457 := bstep (se 2 (by rfl) ⟨1460796, by rfl⟩ : syracuseStep 3895457 = 2921593) B2921593
theorem B7794913 : Blo 1823613 7794913 := bstep (se 2 (by rfl) ⟨2923092, by rfl⟩ : syracuseStep 7794913 = 5846185) B5846185
theorem B5198363 : Blo 1823613 5198363 := bstep (se 1 (by rfl) ⟨3898772, by rfl⟩ : syracuseStep 5198363 = 7797545) B7797545
theorem B6156863 : Blo 1823613 6156863 := bstep (se 1 (by rfl) ⟨4617647, by rfl⟩ : syracuseStep 6156863 = 9235295) B9235295
theorem B170898173 : Blo 1823613 170898173 := bstep (se 3 (by rfl) ⟨32043407, by rfl⟩ : syracuseStep 170898173 = 64086815) B64086815
theorem B6157403 : Blo 1823613 6157403 := bstep (se 1 (by rfl) ⟨4618052, by rfl⟩ : syracuseStep 6157403 = 9236105) B9236105
theorem B6927551 : Blo 1823613 6927551 := bstep (se 1 (by rfl) ⟨5195663, by rfl⟩ : syracuseStep 6927551 = 10391327) B10391327
theorem B1823975 : Blo 1823613 1823975 := bstep (se 1 (by rfl) ⟨1367981, by rfl⟩ : syracuseStep 1823975 = 2735963) B2735963
theorem B6157565 : Blo 1823613 6157565 := bstep (se 3 (by rfl) ⟨1154543, by rfl⟩ : syracuseStep 6157565 = 2309087) B2309087
theorem B23393609 : Blo 1823613 23393609 := bstep (se 2 (by rfl) ⟨8772603, by rfl⟩ : syracuseStep 23393609 = 17545207) B17545207
theorem B9860723 : Blo 1823613 9860723 := bstep (se 1 (by rfl) ⟨7395542, by rfl⟩ : syracuseStep 9860723 = 14791085) B14791085
theorem B9238211 : Blo 1823613 9238211 := bstep (se 1 (by rfl) ⟨6928658, by rfl⟩ : syracuseStep 9238211 = 13857317) B13857317
theorem B35542759 : Blo 1823613 35542759 := bstep (se 1 (by rfl) ⟨26657069, by rfl⟩ : syracuseStep 35542759 = 53314139) B53314139
theorem B24966959 : Blo 1823613 24966959 := bstep (se 1 (by rfl) ⟨18725219, by rfl⟩ : syracuseStep 24966959 = 37450439) B37450439
theorem B20780873 : Blo 1823613 20780873 := bstep (se 2 (by rfl) ⟨7792827, by rfl⟩ : syracuseStep 20780873 = 15585655) B15585655
theorem B9861115 : Blo 1823613 9861115 := bstep (se 1 (by rfl) ⟨7395836, by rfl⟩ : syracuseStep 9861115 = 14791673) B14791673
theorem B7903241 : Blo 1823613 7903241 := bstep (se 2 (by rfl) ⟨2963715, by rfl⟩ : syracuseStep 7903241 = 5927431) B5927431
theorem B1152743507 : Blo 1823613 1152743507 := bstep (se 1 (by rfl) ⟨864557630, by rfl⟩ : syracuseStep 1152743507 = 1729115261) B1729115261
theorem B6158483 : Blo 1823613 6158483 := bstep (se 1 (by rfl) ⟨4618862, by rfl⟩ : syracuseStep 6158483 = 9237725) B9237725
theorem B3078479 : Blo 1823613 3078479 := bstep (se 1 (by rfl) ⟨2308859, by rfl⟩ : syracuseStep 3078479 = 4617719) B4617719
theorem B11696521 : Blo 1823613 11696521 := bstep (se 2 (by rfl) ⟨4386195, by rfl⟩ : syracuseStep 11696521 = 8772391) B8772391
theorem B9239183 : Blo 1823613 9239183 := bstep (se 1 (by rfl) ⟨6929387, by rfl⟩ : syracuseStep 9239183 = 13858775) B13858775
theorem B4619177 : Blo 1823613 4619177 := bstep (se 2 (by rfl) ⟨1732191, by rfl⟩ : syracuseStep 4619177 = 3464383) B3464383
theorem B3079579 : Blo 1823613 3079579 := bstep (se 1 (by rfl) ⟨2309684, by rfl⟩ : syracuseStep 3079579 = 4619369) B4619369
theorem B3464603 : Blo 1823613 3464603 := bstep (se 1 (by rfl) ⟨2598452, by rfl⟩ : syracuseStep 3464603 = 5196905) B5196905
theorem B6160265 : Blo 1823613 6160265 := bstep (se 2 (by rfl) ⟨2310099, by rfl⟩ : syracuseStep 6160265 = 4620199) B4620199
theorem B2736041 : Blo 1823613 2736041 := bstep (se 2 (by rfl) ⟨1026015, by rfl⟩ : syracuseStep 2736041 = 2052031) B2052031
theorem B15794149 : Blo 1823613 15794149 := bstep (se 4 (by rfl) ⟨1480701, by rfl⟩ : syracuseStep 15794149 = 2961403) B2961403
theorem B8323199 : Blo 1823613 8323199 := bstep (se 1 (by rfl) ⟨6242399, by rfl⟩ : syracuseStep 8323199 = 12484799) B12484799
theorem B3465575 : Blo 1823613 3465575 := bstep (se 1 (by rfl) ⟨2599181, by rfl⟩ : syracuseStep 3465575 = 5198363) B5198363
theorem B4104575 : Blo 1823613 4104575 := bstep (se 1 (by rfl) ⟨3078431, by rfl⟩ : syracuseStep 4104575 = 6156863) B6156863
theorem B10387885 : Blo 1823613 10387885 := bstep (se 3 (by rfl) ⟨1947728, by rfl⟩ : syracuseStep 10387885 = 3895457) B3895457
theorem B4104935 : Blo 1823613 4104935 := bstep (se 1 (by rfl) ⟨3078701, by rfl⟩ : syracuseStep 4104935 = 6157403) B6157403
theorem B11100905 : Blo 1823613 11100905 := bstep (se 2 (by rfl) ⟨4162839, by rfl⟩ : syracuseStep 11100905 = 8325679) B8325679
theorem B4105043 : Blo 1823613 4105043 := bstep (se 1 (by rfl) ⟨3078782, by rfl⟩ : syracuseStep 4105043 = 6157565) B6157565
theorem B2737223 : Blo 1823613 2737223 := bstep (se 1 (by rfl) ⟨2052917, by rfl⟩ : syracuseStep 2737223 = 4105835) B4105835
theorem B13853915 : Blo 1823613 13853915 := bstep (se 1 (by rfl) ⟨10390436, by rfl⟩ : syracuseStep 13853915 = 20780873) B20780873
theorem B26297567 : Blo 1823613 26297567 := bstep (se 1 (by rfl) ⟨19723175, by rfl⟩ : syracuseStep 26297567 = 39446351) B39446351
theorem B73073987 : Blo 1823613 73073987 := bstep (se 1 (by rfl) ⟨54805490, by rfl⟩ : syracuseStep 73073987 = 109610981) B109610981
theorem B5268827 : Blo 1823613 5268827 := bstep (se 1 (by rfl) ⟨3951620, by rfl⟩ : syracuseStep 5268827 = 7903241) B7903241
theorem B4105655 : Blo 1823613 4105655 := bstep (se 1 (by rfl) ⟨3079241, by rfl⟩ : syracuseStep 4105655 = 6158483) B6158483
theorem B4106105 : Blo 1823613 4106105 := bstep (se 2 (by rfl) ⟨1539789, by rfl⟩ : syracuseStep 4106105 = 3079579) B3079579
theorem B2738075 : Blo 1823613 2738075 := bstep (se 1 (by rfl) ⟨2053556, by rfl⟩ : syracuseStep 2738075 = 4107113) B4107113
theorem B66578557 : Blo 1823613 66578557 := bstep (se 3 (by rfl) ⟨12483479, by rfl⟩ : syracuseStep 66578557 = 24966959) B24966959
theorem B4106843 : Blo 1823613 4106843 := bstep (se 1 (by rfl) ⟨3080132, by rfl⟩ : syracuseStep 4106843 = 6160265) B6160265
theorem B7793273 : Blo 1823613 7793273 := bstep (se 2 (by rfl) ⟨2922477, by rfl⟩ : syracuseStep 7793273 = 5844955) B5844955
theorem B7023559 : Blo 1823613 7023559 := bstep (se 1 (by rfl) ⟨5267669, by rfl⟩ : syracuseStep 7023559 = 10535339) B10535339
theorem B8883425 : Blo 1823613 8883425 := bstep (se 2 (by rfl) ⟨3331284, by rfl⟩ : syracuseStep 8883425 = 6662569) B6662569
theorem B4107527 : Blo 1823613 4107527 := bstep (se 1 (by rfl) ⟨3080645, by rfl⟩ : syracuseStep 4107527 = 6161291) B6161291
theorem B6573815 : Blo 1823613 6573815 := bstep (se 1 (by rfl) ⟨4930361, by rfl⟩ : syracuseStep 6573815 = 9860723) B9860723
theorem B768495671 : Blo 1823613 768495671 := bstep (se 1 (by rfl) ⟨576371753, by rfl⟩ : syracuseStep 768495671 = 1152743507) B1152743507
theorem B2052319 : Blo 1823613 2052319 := bstep (se 1 (by rfl) ⟨1539239, by rfl⟩ : syracuseStep 2052319 = 3078479) B3078479
theorem B4616423 : Blo 1823613 4616423 := bstep (se 1 (by rfl) ⟨3462317, by rfl⟩ : syracuseStep 4616423 = 6924635) B6924635
theorem B4616635 : Blo 1823613 4616635 := bstep (se 1 (by rfl) ⟨3462476, by rfl⟩ : syracuseStep 4616635 = 6924953) B6924953
theorem B7795547 : Blo 1823613 7795547 := bstep (se 1 (by rfl) ⟨5846660, by rfl⟩ : syracuseStep 7795547 = 11693321) B11693321
theorem B42701701 : Blo 1823613 42701701 := bstep (se 4 (by rfl) ⟨4003284, by rfl⟩ : syracuseStep 42701701 = 8006569) B8006569
theorem B7025563 : Blo 1823613 7025563 := bstep (se 1 (by rfl) ⟨5269172, by rfl⟩ : syracuseStep 7025563 = 10538345) B10538345
theorem B7795835 : Blo 1823613 7795835 := bstep (se 1 (by rfl) ⟨5846876, by rfl⟩ : syracuseStep 7795835 = 11693753) B11693753
theorem B24958205 : Blo 1823613 24958205 := bstep (se 3 (by rfl) ⟨4679663, by rfl⟩ : syracuseStep 24958205 = 9359327) B9359327
theorem B36517139 : Blo 1823613 36517139 := bstep (se 1 (by rfl) ⟨27387854, by rfl⟩ : syracuseStep 36517139 = 54775709) B54775709
theorem B1824027 : Blo 1823613 1824027 := bstep (se 1 (by rfl) ⟨1368020, by rfl⟩ : syracuseStep 1824027 = 2736041) B2736041
theorem B21058865 : Blo 1823613 21058865 := bstep (se 2 (by rfl) ⟨7897074, by rfl⟩ : syracuseStep 21058865 = 15794149) B15794149
theorem B10393217 : Blo 1823613 10393217 := bstep (se 2 (by rfl) ⟨3897456, by rfl⟩ : syracuseStep 10393217 = 7794913) B7794913
theorem B113932115 : Blo 1823613 113932115 := bstep (se 1 (by rfl) ⟨85449086, by rfl⟩ : syracuseStep 113932115 = 170898173) B170898173
theorem B15595361 : Blo 1823613 15595361 := bstep (se 2 (by rfl) ⟨5848260, by rfl⟩ : syracuseStep 15595361 = 11696521) B11696521
theorem B1824623 : Blo 1823613 1824623 := bstep (se 1 (by rfl) ⟨1368467, by rfl⟩ : syracuseStep 1824623 = 2736935) B2736935
theorem B1824795 : Blo 1823613 1824795 := bstep (se 1 (by rfl) ⟨1368596, by rfl⟩ : syracuseStep 1824795 = 2737193) B2737193
theorem B4618367 : Blo 1823613 4618367 := bstep (se 1 (by rfl) ⟨3463775, by rfl⟩ : syracuseStep 4618367 = 6927551) B6927551
theorem B15595739 : Blo 1823613 15595739 := bstep (se 1 (by rfl) ⟨11696804, by rfl⟩ : syracuseStep 15595739 = 23393609) B23393609
theorem B15587639 : Blo 1823613 15587639 := bstep (se 1 (by rfl) ⟨11690729, by rfl⟩ : syracuseStep 15587639 = 23381459) B23381459
theorem B6158807 : Blo 1823613 6158807 := bstep (se 1 (by rfl) ⟨4619105, by rfl⟩ : syracuseStep 6158807 = 9238211) B9238211
theorem B15579641 : Blo 1823613 15579641 := bstep (se 2 (by rfl) ⟨5842365, by rfl⟩ : syracuseStep 15579641 = 11684731) B11684731
theorem B1825391 : Blo 1823613 1825391 := bstep (se 1 (by rfl) ⟨1369043, by rfl⟩ : syracuseStep 1825391 = 2738087) B2738087
theorem B1825511 : Blo 1823613 1825511 := bstep (se 1 (by rfl) ⟨1369133, by rfl⟩ : syracuseStep 1825511 = 2738267) B2738267
theorem B1825535 : Blo 1823613 1825535 := bstep (se 1 (by rfl) ⟨1369151, by rfl⟩ : syracuseStep 1825535 = 2738303) B2738303
theorem B4103135 : Blo 1823613 4103135 := bstep (se 1 (by rfl) ⟨3077351, by rfl⟩ : syracuseStep 4103135 = 6154703) B6154703
theorem B6159455 : Blo 1823613 6159455 := bstep (se 1 (by rfl) ⟨4619591, by rfl⟩ : syracuseStep 6159455 = 9239183) B9239183
theorem B105225317 : Blo 1823613 105225317 := bstep (se 4 (by rfl) ⟨9864873, by rfl⟩ : syracuseStep 105225317 = 19729747) B19729747
theorem B3079451 : Blo 1823613 3079451 := bstep (se 1 (by rfl) ⟨2309588, by rfl⟩ : syracuseStep 3079451 = 4619177) B4619177
theorem B2309735 : Blo 1823613 2309735 := bstep (se 1 (by rfl) ⟨1732301, by rfl⟩ : syracuseStep 2309735 = 3464603) B3464603
theorem B47390345 : Blo 1823613 47390345 := bstep (se 2 (by rfl) ⟨17771379, by rfl⟩ : syracuseStep 47390345 = 35542759) B35542759
theorem B13148153 : Blo 1823613 13148153 := bstep (se 2 (by rfl) ⟨4930557, by rfl⟩ : syracuseStep 13148153 = 9861115) B9861115
theorem B2310383 : Blo 1823613 2310383 := bstep (se 1 (by rfl) ⟨1732787, by rfl⟩ : syracuseStep 2310383 = 3465575) B3465575
theorem B2736383 : Blo 1823613 2736383 := bstep (se 1 (by rfl) ⟨2052287, by rfl⟩ : syracuseStep 2736383 = 4104575) B4104575
theorem B2736425 : Blo 1823613 2736425 := bstep (se 2 (by rfl) ⟨1026159, by rfl⟩ : syracuseStep 2736425 = 2052319) B2052319
theorem B2736623 : Blo 1823613 2736623 := bstep (se 1 (by rfl) ⟨2052467, by rfl⟩ : syracuseStep 2736623 = 4104935) B4104935
theorem B2736695 : Blo 1823613 2736695 := bstep (se 1 (by rfl) ⟨2052521, by rfl⟩ : syracuseStep 2736695 = 4105043) B4105043
theorem B17531711 : Blo 1823613 17531711 := bstep (se 1 (by rfl) ⟨13148783, by rfl⟩ : syracuseStep 17531711 = 26297567) B26297567
theorem B16638803 : Blo 1823613 16638803 := bstep (se 1 (by rfl) ⟨12479102, by rfl⟩ : syracuseStep 16638803 = 24958205) B24958205
theorem B14050205 : Blo 1823613 14050205 := bstep (se 3 (by rfl) ⟨2634413, by rfl⟩ : syracuseStep 14050205 = 5268827) B5268827
theorem B2737103 : Blo 1823613 2737103 := bstep (se 1 (by rfl) ⟨2052827, by rfl⟩ : syracuseStep 2737103 = 4105655) B4105655
theorem B56935601 : Blo 1823613 56935601 := bstep (se 2 (by rfl) ⟨21350850, by rfl⟩ : syracuseStep 56935601 = 42701701) B42701701
theorem B10396907 : Blo 1823613 10396907 := bstep (se 1 (by rfl) ⟨7797680, by rfl⟩ : syracuseStep 10396907 = 15595361) B15595361
theorem B2737403 : Blo 1823613 2737403 := bstep (se 1 (by rfl) ⟨2053052, by rfl⟩ : syracuseStep 2737403 = 4106105) B4106105
theorem B9364745 : Blo 1823613 9364745 := bstep (se 2 (by rfl) ⟨3511779, by rfl⟩ : syracuseStep 9364745 = 7023559) B7023559
theorem B10397159 : Blo 1823613 10397159 := bstep (se 1 (by rfl) ⟨7797869, by rfl⟩ : syracuseStep 10397159 = 15595739) B15595739
theorem B4105871 : Blo 1823613 4105871 := bstep (se 1 (by rfl) ⟨3079403, by rfl⟩ : syracuseStep 4105871 = 6158807) B6158807
theorem B2737895 : Blo 1823613 2737895 := bstep (se 1 (by rfl) ⟨2053421, by rfl⟩ : syracuseStep 2737895 = 4106843) B4106843
theorem B5195515 : Blo 1823613 5195515 := bstep (se 1 (by rfl) ⟨3896636, by rfl⟩ : syracuseStep 5195515 = 7793273) B7793273
theorem B4106303 : Blo 1823613 4106303 := bstep (se 1 (by rfl) ⟨3079727, by rfl⟩ : syracuseStep 4106303 = 6159455) B6159455
theorem B70150211 : Blo 1823613 70150211 := bstep (se 1 (by rfl) ⟨52612658, by rfl⟩ : syracuseStep 70150211 = 105225317) B105225317
theorem B2738351 : Blo 1823613 2738351 := bstep (se 1 (by rfl) ⟨2053763, by rfl⟩ : syracuseStep 2738351 = 4107527) B4107527
theorem B512330447 : Blo 1823613 512330447 := bstep (se 1 (by rfl) ⟨384247835, by rfl⟩ : syracuseStep 512330447 = 768495671) B768495671
theorem B5548799 : Blo 1823613 5548799 := bstep (se 1 (by rfl) ⟨4161599, by rfl⟩ : syracuseStep 5548799 = 8323199) B8323199
theorem B88771409 : Blo 1823613 88771409 := bstep (se 2 (by rfl) ⟨33289278, by rfl⟩ : syracuseStep 88771409 = 66578557) B66578557
theorem B7400603 : Blo 1823613 7400603 := bstep (se 1 (by rfl) ⟨5550452, by rfl⟩ : syracuseStep 7400603 = 11100905) B11100905
theorem B5197031 : Blo 1823613 5197031 := bstep (se 1 (by rfl) ⟨3897773, by rfl⟩ : syracuseStep 5197031 = 7795547) B7795547
theorem B6155513 : Blo 1823613 6155513 := bstep (se 2 (by rfl) ⟨2308317, by rfl⟩ : syracuseStep 6155513 = 4616635) B4616635
theorem B5197223 : Blo 1823613 5197223 := bstep (se 1 (by rfl) ⟨3897917, by rfl⟩ : syracuseStep 5197223 = 7795835) B7795835
theorem B9235943 : Blo 1823613 9235943 := bstep (se 1 (by rfl) ⟨6926957, by rfl⟩ : syracuseStep 9235943 = 13853915) B13853915
theorem B9367417 : Blo 1823613 9367417 := bstep (se 2 (by rfl) ⟨3512781, by rfl⟩ : syracuseStep 9367417 = 7025563) B7025563
theorem B10391759 : Blo 1823613 10391759 := bstep (se 1 (by rfl) ⟨7793819, by rfl⟩ : syracuseStep 10391759 = 15587639) B15587639
theorem B2052967 : Blo 1823613 2052967 := bstep (se 1 (by rfl) ⟨1539725, by rfl⟩ : syracuseStep 2052967 = 3079451) B3079451
theorem B31593563 : Blo 1823613 31593563 := bstep (se 1 (by rfl) ⟨23695172, by rfl⟩ : syracuseStep 31593563 = 47390345) B47390345
theorem B3077615 : Blo 1823613 3077615 := bstep (se 1 (by rfl) ⟨2308211, by rfl⟩ : syracuseStep 3077615 = 4616423) B4616423
theorem B13850513 : Blo 1823613 13850513 := bstep (se 2 (by rfl) ⟨5193942, by rfl⟩ : syracuseStep 13850513 = 10387885) B10387885
theorem B1824815 : Blo 1823613 1824815 := bstep (se 1 (by rfl) ⟨1368611, by rfl⟩ : syracuseStep 1824815 = 2737223) B2737223
theorem B24344759 : Blo 1823613 24344759 := bstep (se 1 (by rfl) ⟨18258569, by rfl⟩ : syracuseStep 24344759 = 36517139) B36517139
theorem B14039243 : Blo 1823613 14039243 := bstep (se 1 (by rfl) ⟨10529432, by rfl⟩ : syracuseStep 14039243 = 21058865) B21058865
theorem B48715991 : Blo 1823613 48715991 := bstep (se 1 (by rfl) ⟨36536993, by rfl⟩ : syracuseStep 48715991 = 73073987) B73073987
theorem B6928811 : Blo 1823613 6928811 := bstep (se 1 (by rfl) ⟨5196608, by rfl⟩ : syracuseStep 6928811 = 10393217) B10393217
theorem B75954743 : Blo 1823613 75954743 := bstep (se 1 (by rfl) ⟨56966057, by rfl⟩ : syracuseStep 75954743 = 113932115) B113932115
theorem B1825383 : Blo 1823613 1825383 := bstep (se 1 (by rfl) ⟨1369037, by rfl⟩ : syracuseStep 1825383 = 2738075) B2738075
theorem B3078911 : Blo 1823613 3078911 := bstep (se 1 (by rfl) ⟨2309183, by rfl⟩ : syracuseStep 3078911 = 4618367) B4618367
theorem B6159293 : Blo 1823613 6159293 := bstep (se 3 (by rfl) ⟨1154867, by rfl⟩ : syracuseStep 6159293 = 2309735) B2309735
theorem B10386427 : Blo 1823613 10386427 := bstep (se 1 (by rfl) ⟨7789820, by rfl⟩ : syracuseStep 10386427 = 15579641) B15579641
theorem B2735423 : Blo 1823613 2735423 := bstep (se 1 (by rfl) ⟨2051567, by rfl⟩ : syracuseStep 2735423 = 4103135) B4103135
theorem B5922283 : Blo 1823613 5922283 := bstep (se 1 (by rfl) ⟨4441712, by rfl⟩ : syracuseStep 5922283 = 8883425) B8883425
theorem B4382543 : Blo 1823613 4382543 := bstep (se 1 (by rfl) ⟨3286907, by rfl⟩ : syracuseStep 4382543 = 6573815) B6573815
theorem B8765435 : Blo 1823613 8765435 := bstep (se 1 (by rfl) ⟨6574076, by rfl⟩ : syracuseStep 8765435 = 13148153) B13148153
theorem B19734941 : Blo 1823613 19734941 := bstep (se 3 (by rfl) ⟨3700301, by rfl⟩ : syracuseStep 19734941 = 7400603) B7400603
theorem B11092535 : Blo 1823613 11092535 := bstep (se 1 (by rfl) ⟨8319401, by rfl⟩ : syracuseStep 11092535 = 16638803) B16638803
theorem B6161021 : Blo 1823613 6161021 := bstep (se 3 (by rfl) ⟨1155191, by rfl⟩ : syracuseStep 6161021 = 2310383) B2310383
theorem B21062375 : Blo 1823613 21062375 := bstep (se 1 (by rfl) ⟨15796781, by rfl⟩ : syracuseStep 21062375 = 31593563) B31593563
theorem B6931271 : Blo 1823613 6931271 := bstep (se 1 (by rfl) ⟨5198453, by rfl⟩ : syracuseStep 6931271 = 10396907) B10396907
theorem B6931439 : Blo 1823613 6931439 := bstep (se 1 (by rfl) ⟨5198579, by rfl⟩ : syracuseStep 6931439 = 10397159) B10397159
theorem B2737247 : Blo 1823613 2737247 := bstep (se 1 (by rfl) ⟨2052935, by rfl⟩ : syracuseStep 2737247 = 4105871) B4105871
theorem B2737289 : Blo 1823613 2737289 := bstep (se 2 (by rfl) ⟨1026483, by rfl⟩ : syracuseStep 2737289 = 2052967) B2052967
theorem B9233675 : Blo 1823613 9233675 := bstep (se 1 (by rfl) ⟨6925256, by rfl⟩ : syracuseStep 9233675 = 13850513) B13850513
theorem B2737535 : Blo 1823613 2737535 := bstep (se 1 (by rfl) ⟨2053151, by rfl⟩ : syracuseStep 2737535 = 4106303) B4106303
theorem B50636495 : Blo 1823613 50636495 := bstep (se 1 (by rfl) ⟨37977371, by rfl⟩ : syracuseStep 50636495 = 75954743) B75954743
theorem B59180939 : Blo 1823613 59180939 := bstep (se 1 (by rfl) ⟨44385704, by rfl⟩ : syracuseStep 59180939 = 88771409) B88771409
theorem B4106195 : Blo 1823613 4106195 := bstep (se 1 (by rfl) ⟨3079646, by rfl⟩ : syracuseStep 4106195 = 6159293) B6159293
theorem B5843623 : Blo 1823613 5843623 := bstep (se 1 (by rfl) ⟨4382717, by rfl⟩ : syracuseStep 5843623 = 8765435) B8765435
theorem B9366803 : Blo 1823613 9366803 := bstep (se 1 (by rfl) ⟨7025102, by rfl⟩ : syracuseStep 9366803 = 14050205) B14050205
theorem B24972653 : Blo 1823613 24972653 := bstep (se 3 (by rfl) ⟨4682372, by rfl⟩ : syracuseStep 24972653 = 9364745) B9364745
theorem B37957067 : Blo 1823613 37957067 := bstep (se 1 (by rfl) ⟨28467800, by rfl⟩ : syracuseStep 37957067 = 56935601) B56935601
theorem B2051743 : Blo 1823613 2051743 := bstep (se 1 (by rfl) ⟨1538807, by rfl⟩ : syracuseStep 2051743 = 3077615) B3077615
theorem B13848569 : Blo 1823613 13848569 := bstep (se 2 (by rfl) ⟨5193213, by rfl⟩ : syracuseStep 13848569 = 10386427) B10386427
theorem B9359495 : Blo 1823613 9359495 := bstep (se 1 (by rfl) ⟨7019621, by rfl⟩ : syracuseStep 9359495 = 14039243) B14039243
theorem B32477327 : Blo 1823613 32477327 := bstep (se 1 (by rfl) ⟨24357995, by rfl⟩ : syracuseStep 32477327 = 48715991) B48715991
theorem B341553631 : Blo 1823613 341553631 := bstep (se 1 (by rfl) ⟨256165223, by rfl⟩ : syracuseStep 341553631 = 512330447) B512330447
theorem B2052607 : Blo 1823613 2052607 := bstep (se 1 (by rfl) ⟨1539455, by rfl⟩ : syracuseStep 2052607 = 3078911) B3078911
theorem B3699199 : Blo 1823613 3699199 := bstep (se 1 (by rfl) ⟨2774399, by rfl⟩ : syracuseStep 3699199 = 5548799) B5548799
theorem B11686781 : Blo 1823613 11686781 := bstep (se 3 (by rfl) ⟨2191271, by rfl⟩ : syracuseStep 11686781 = 4382543) B4382543
theorem B1823615 : Blo 1823613 1823615 := bstep (se 1 (by rfl) ⟨1367711, by rfl⟩ : syracuseStep 1823615 = 2735423) B2735423
theorem B6157295 : Blo 1823613 6157295 := bstep (se 1 (by rfl) ⟨4617971, by rfl⟩ : syracuseStep 6157295 = 9235943) B9235943
theorem B6927353 : Blo 1823613 6927353 := bstep (se 2 (by rfl) ⟨2597757, by rfl⟩ : syracuseStep 6927353 = 5195515) B5195515
theorem B12489889 : Blo 1823613 12489889 := bstep (se 2 (by rfl) ⟨4683708, by rfl⟩ : syracuseStep 12489889 = 9367417) B9367417
theorem B6927839 : Blo 1823613 6927839 := bstep (se 1 (by rfl) ⟨5195879, by rfl⟩ : syracuseStep 6927839 = 10391759) B10391759
theorem B1824255 : Blo 1823613 1824255 := bstep (se 1 (by rfl) ⟨1368191, by rfl⟩ : syracuseStep 1824255 = 2736383) B2736383
theorem B1824283 : Blo 1823613 1824283 := bstep (se 1 (by rfl) ⟨1368212, by rfl⟩ : syracuseStep 1824283 = 2736425) B2736425
theorem B1824415 : Blo 1823613 1824415 := bstep (se 1 (by rfl) ⟨1368311, by rfl⟩ : syracuseStep 1824415 = 2736623) B2736623
theorem B1824463 : Blo 1823613 1824463 := bstep (se 1 (by rfl) ⟨1368347, by rfl⟩ : syracuseStep 1824463 = 2736695) B2736695
theorem B64919357 : Blo 1823613 64919357 := bstep (se 3 (by rfl) ⟨12172379, by rfl⟩ : syracuseStep 64919357 = 24344759) B24344759
theorem B11687807 : Blo 1823613 11687807 := bstep (se 1 (by rfl) ⟨8765855, by rfl⟩ : syracuseStep 11687807 = 17531711) B17531711
theorem B1824735 : Blo 1823613 1824735 := bstep (se 1 (by rfl) ⟨1368551, by rfl⟩ : syracuseStep 1824735 = 2737103) B2737103
theorem B1824935 : Blo 1823613 1824935 := bstep (se 1 (by rfl) ⟨1368701, by rfl⟩ : syracuseStep 1824935 = 2737403) B2737403
theorem B13859261 : Blo 1823613 13859261 := bstep (se 3 (by rfl) ⟨2598611, by rfl⟩ : syracuseStep 13859261 = 5197223) B5197223
theorem B1825263 : Blo 1823613 1825263 := bstep (se 1 (by rfl) ⟨1368947, by rfl⟩ : syracuseStep 1825263 = 2737895) B2737895
theorem B46766807 : Blo 1823613 46766807 := bstep (se 1 (by rfl) ⟨35075105, by rfl⟩ : syracuseStep 46766807 = 70150211) B70150211
theorem B1825567 : Blo 1823613 1825567 := bstep (se 1 (by rfl) ⟨1369175, by rfl⟩ : syracuseStep 1825567 = 2738351) B2738351
theorem B4619207 : Blo 1823613 4619207 := bstep (se 1 (by rfl) ⟨3464405, by rfl⟩ : syracuseStep 4619207 = 6928811) B6928811
theorem B7896377 : Blo 1823613 7896377 := bstep (se 2 (by rfl) ⟨2961141, by rfl⟩ : syracuseStep 7896377 = 5922283) B5922283
theorem B3464687 : Blo 1823613 3464687 := bstep (se 1 (by rfl) ⟨2598515, by rfl⟩ : syracuseStep 3464687 = 5197031) B5197031
theorem B4103675 : Blo 1823613 4103675 := bstep (se 1 (by rfl) ⟨3077756, by rfl⟩ : syracuseStep 4103675 = 6155513) B6155513
theorem B21651551 : Blo 1823613 21651551 := bstep (se 1 (by rfl) ⟨16238663, by rfl⟩ : syracuseStep 21651551 = 32477327) B32477327
theorem B13156627 : Blo 1823613 13156627 := bstep (se 1 (by rfl) ⟨9867470, by rfl⟩ : syracuseStep 13156627 = 19734941) B19734941
theorem B14041583 : Blo 1823613 14041583 := bstep (se 1 (by rfl) ⟨10531187, by rfl⟩ : syracuseStep 14041583 = 21062375) B21062375
theorem B4620847 : Blo 1823613 4620847 := bstep (se 1 (by rfl) ⟨3465635, by rfl⟩ : syracuseStep 4620847 = 6931271) B6931271
theorem B4104863 : Blo 1823613 4104863 := bstep (se 1 (by rfl) ⟨3078647, by rfl⟩ : syracuseStep 4104863 = 6157295) B6157295
theorem B4620959 : Blo 1823613 4620959 := bstep (se 1 (by rfl) ⟨3465719, by rfl⟩ : syracuseStep 4620959 = 6931439) B6931439
theorem B2736809 : Blo 1823613 2736809 := bstep (se 2 (by rfl) ⟨1026303, by rfl⟩ : syracuseStep 2736809 = 2052607) B2052607
theorem B4932265 : Blo 1823613 4932265 := bstep (se 2 (by rfl) ⟨1849599, by rfl⟩ : syracuseStep 4932265 = 3699199) B3699199
theorem B7791497 : Blo 1823613 7791497 := bstep (se 2 (by rfl) ⟨2921811, by rfl⟩ : syracuseStep 7791497 = 5843623) B5843623
theorem B43279571 : Blo 1823613 43279571 := bstep (se 1 (by rfl) ⟨32459678, by rfl⟩ : syracuseStep 43279571 = 64919357) B64919357
theorem B7791871 : Blo 1823613 7791871 := bstep (se 1 (by rfl) ⟨5843903, by rfl⟩ : syracuseStep 7791871 = 11687807) B11687807
theorem B39453959 : Blo 1823613 39453959 := bstep (se 1 (by rfl) ⟨29590469, by rfl⟩ : syracuseStep 39453959 = 59180939) B59180939
theorem B2737463 : Blo 1823613 2737463 := bstep (se 1 (by rfl) ⟨2053097, by rfl⟩ : syracuseStep 2737463 = 4106195) B4106195
theorem B9232379 : Blo 1823613 9232379 := bstep (se 1 (by rfl) ⟨6924284, by rfl⟩ : syracuseStep 9232379 = 13848569) B13848569
theorem B404875381 : Blo 1823613 404875381 := bstep (se 5 (by rfl) ⟨18978533, by rfl⟩ : syracuseStep 404875381 = 37957067) B37957067
theorem B6244535 : Blo 1823613 6244535 := bstep (se 1 (by rfl) ⟨4683401, by rfl⟩ : syracuseStep 6244535 = 9366803) B9366803
theorem B16648435 : Blo 1823613 16648435 := bstep (se 1 (by rfl) ⟨12486326, by rfl⟩ : syracuseStep 16648435 = 24972653) B24972653
theorem B31164749 : Blo 1823613 31164749 := bstep (se 3 (by rfl) ⟨5843390, by rfl⟩ : syracuseStep 31164749 = 11686781) B11686781
theorem B4107347 : Blo 1823613 4107347 := bstep (se 1 (by rfl) ⟨3080510, by rfl⟩ : syracuseStep 4107347 = 6161021) B6161021
theorem B455404841 : Blo 1823613 455404841 := bstep (se 2 (by rfl) ⟨170776815, by rfl⟩ : syracuseStep 455404841 = 341553631) B341553631
theorem B21057005 : Blo 1823613 21057005 := bstep (se 3 (by rfl) ⟨3948188, by rfl⟩ : syracuseStep 21057005 = 7896377) B7896377
theorem B6155783 : Blo 1823613 6155783 := bstep (se 1 (by rfl) ⟨4616837, by rfl⟩ : syracuseStep 6155783 = 9233675) B9233675
theorem B6239663 : Blo 1823613 6239663 := bstep (se 1 (by rfl) ⟨4679747, by rfl⟩ : syracuseStep 6239663 = 9359495) B9359495
theorem B7395023 : Blo 1823613 7395023 := bstep (se 1 (by rfl) ⟨5546267, by rfl⟩ : syracuseStep 7395023 = 11092535) B11092535
theorem B4618235 : Blo 1823613 4618235 := bstep (se 1 (by rfl) ⟨3463676, by rfl⟩ : syracuseStep 4618235 = 6927353) B6927353
theorem B1824831 : Blo 1823613 1824831 := bstep (se 1 (by rfl) ⟨1368623, by rfl⟩ : syracuseStep 1824831 = 2737247) B2737247
theorem B1824859 : Blo 1823613 1824859 := bstep (se 1 (by rfl) ⟨1368644, by rfl⟩ : syracuseStep 1824859 = 2737289) B2737289
theorem B1825023 : Blo 1823613 1825023 := bstep (se 1 (by rfl) ⟨1368767, by rfl⟩ : syracuseStep 1825023 = 2737535) B2737535
theorem B4618559 : Blo 1823613 4618559 := bstep (se 1 (by rfl) ⟨3463919, by rfl⟩ : syracuseStep 4618559 = 6927839) B6927839
theorem B33757663 : Blo 1823613 33757663 := bstep (se 1 (by rfl) ⟨25318247, by rfl⟩ : syracuseStep 33757663 = 50636495) B50636495
theorem B16653185 : Blo 1823613 16653185 := bstep (se 2 (by rfl) ⟨6244944, by rfl⟩ : syracuseStep 16653185 = 12489889) B12489889
theorem B9239507 : Blo 1823613 9239507 := bstep (se 1 (by rfl) ⟨6929630, by rfl⟩ : syracuseStep 9239507 = 13859261) B13859261
theorem B31177871 : Blo 1823613 31177871 := bstep (se 1 (by rfl) ⟨23383403, by rfl⟩ : syracuseStep 31177871 = 46766807) B46766807
theorem B3079471 : Blo 1823613 3079471 := bstep (se 1 (by rfl) ⟨2309603, by rfl⟩ : syracuseStep 3079471 = 4619207) B4619207
theorem B2735657 : Blo 1823613 2735657 := bstep (se 2 (by rfl) ⟨1025871, by rfl⟩ : syracuseStep 2735657 = 2051743) B2051743
theorem B2309791 : Blo 1823613 2309791 := bstep (se 1 (by rfl) ⟨1732343, by rfl⟩ : syracuseStep 2309791 = 3464687) B3464687
theorem B2735783 : Blo 1823613 2735783 := bstep (se 1 (by rfl) ⟨2051837, by rfl⟩ : syracuseStep 2735783 = 4103675) B4103675
theorem B14434367 : Blo 1823613 14434367 := bstep (se 1 (by rfl) ⟨10825775, by rfl⟩ : syracuseStep 14434367 = 21651551) B21651551
theorem B2736575 : Blo 1823613 2736575 := bstep (se 1 (by rfl) ⟨2052431, by rfl⟩ : syracuseStep 2736575 = 4104863) B4104863
theorem B3080639 : Blo 1823613 3080639 := bstep (se 1 (by rfl) ⟨2310479, by rfl⟩ : syracuseStep 3080639 = 4620959) B4620959
theorem B5194331 : Blo 1823613 5194331 := bstep (se 1 (by rfl) ⟨3895748, by rfl⟩ : syracuseStep 5194331 = 7791497) B7791497
theorem B6161129 : Blo 1823613 6161129 := bstep (se 2 (by rfl) ⟨2310423, by rfl⟩ : syracuseStep 6161129 = 4620847) B4620847
theorem B28853047 : Blo 1823613 28853047 := bstep (se 1 (by rfl) ⟨21639785, by rfl⟩ : syracuseStep 28853047 = 43279571) B43279571
theorem B4163023 : Blo 1823613 4163023 := bstep (se 1 (by rfl) ⟨3122267, by rfl⟩ : syracuseStep 4163023 = 6244535) B6244535
theorem B20776499 : Blo 1823613 20776499 := bstep (se 1 (by rfl) ⟨15582374, by rfl⟩ : syracuseStep 20776499 = 31164749) B31164749
theorem B10389161 : Blo 1823613 10389161 := bstep (se 2 (by rfl) ⟨3895935, by rfl⟩ : syracuseStep 10389161 = 7791871) B7791871
theorem B4105961 : Blo 1823613 4105961 := bstep (se 2 (by rfl) ⟨1539735, by rfl⟩ : syracuseStep 4105961 = 3079471) B3079471
theorem B19720061 : Blo 1823613 19720061 := bstep (se 3 (by rfl) ⟨3697511, by rfl⟩ : syracuseStep 19720061 = 7395023) B7395023
theorem B11102123 : Blo 1823613 11102123 := bstep (se 1 (by rfl) ⟨8326592, by rfl⟩ : syracuseStep 11102123 = 16653185) B16653185
theorem B2738231 : Blo 1823613 2738231 := bstep (se 1 (by rfl) ⟨2053673, by rfl⟩ : syracuseStep 2738231 = 4107347) B4107347
theorem B20785247 : Blo 1823613 20785247 := bstep (se 1 (by rfl) ⟨15588935, by rfl⟩ : syracuseStep 20785247 = 31177871) B31177871
theorem B6154919 : Blo 1823613 6154919 := bstep (se 1 (by rfl) ⟨4616189, by rfl⟩ : syracuseStep 6154919 = 9232379) B9232379
theorem B17542169 : Blo 1823613 17542169 := bstep (se 2 (by rfl) ⟨6578313, by rfl⟩ : syracuseStep 17542169 = 13156627) B13156627
theorem B45010217 : Blo 1823613 45010217 := bstep (se 2 (by rfl) ⟨16878831, by rfl⟩ : syracuseStep 45010217 = 33757663) B33757663
theorem B14038003 : Blo 1823613 14038003 := bstep (se 1 (by rfl) ⟨10528502, by rfl⟩ : syracuseStep 14038003 = 21057005) B21057005
theorem B1823771 : Blo 1823613 1823771 := bstep (se 1 (by rfl) ⟨1367828, by rfl⟩ : syracuseStep 1823771 = 2735657) B2735657
theorem B1823855 : Blo 1823613 1823855 := bstep (se 1 (by rfl) ⟨1367891, by rfl⟩ : syracuseStep 1823855 = 2735783) B2735783
theorem B539833841 : Blo 1823613 539833841 := bstep (se 2 (by rfl) ⟨202437690, by rfl⟩ : syracuseStep 539833841 = 404875381) B404875381
theorem B9361055 : Blo 1823613 9361055 := bstep (se 1 (by rfl) ⟨7020791, by rfl⟩ : syracuseStep 9361055 = 14041583) B14041583
theorem B1824539 : Blo 1823613 1824539 := bstep (se 1 (by rfl) ⟨1368404, by rfl⟩ : syracuseStep 1824539 = 2736809) B2736809
theorem B26302639 : Blo 1823613 26302639 := bstep (se 1 (by rfl) ⟨19726979, by rfl⟩ : syracuseStep 26302639 = 39453959) B39453959
theorem B1824975 : Blo 1823613 1824975 := bstep (se 1 (by rfl) ⟨1368731, by rfl⟩ : syracuseStep 1824975 = 2737463) B2737463
theorem B6576353 : Blo 1823613 6576353 := bstep (se 2 (by rfl) ⟨2466132, by rfl⟩ : syracuseStep 6576353 = 4932265) B4932265
theorem B4159775 : Blo 1823613 4159775 := bstep (se 1 (by rfl) ⟨3119831, by rfl⟩ : syracuseStep 4159775 = 6239663) B6239663
theorem B88791653 : Blo 1823613 88791653 := bstep (se 4 (by rfl) ⟨8324217, by rfl⟩ : syracuseStep 88791653 = 16648435) B16648435
theorem B3078823 : Blo 1823613 3078823 := bstep (se 1 (by rfl) ⟨2309117, by rfl⟩ : syracuseStep 3078823 = 4618235) B4618235
theorem B3079039 : Blo 1823613 3079039 := bstep (se 1 (by rfl) ⟨2309279, by rfl⟩ : syracuseStep 3079039 = 4618559) B4618559
theorem B6159671 : Blo 1823613 6159671 := bstep (se 1 (by rfl) ⟨4619753, by rfl⟩ : syracuseStep 6159671 = 9239507) B9239507
theorem B303603227 : Blo 1823613 303603227 := bstep (se 1 (by rfl) ⟨227702420, by rfl⟩ : syracuseStep 303603227 = 455404841) B455404841
theorem B3079721 : Blo 1823613 3079721 := bstep (se 2 (by rfl) ⟨1154895, by rfl⟩ : syracuseStep 3079721 = 2309791) B2309791
theorem B4103855 : Blo 1823613 4103855 := bstep (se 1 (by rfl) ⟨3077891, by rfl⟩ : syracuseStep 4103855 = 6155783) B6155783
theorem B35070185 : Blo 1823613 35070185 := bstep (se 2 (by rfl) ⟨13151319, by rfl⟩ : syracuseStep 35070185 = 26302639) B26302639
theorem B4105097 : Blo 1823613 4105097 := bstep (se 2 (by rfl) ⟨1539411, by rfl⟩ : syracuseStep 4105097 = 3078823) B3078823
theorem B38470729 : Blo 1823613 38470729 := bstep (se 2 (by rfl) ⟨14426523, by rfl⟩ : syracuseStep 38470729 = 28853047) B28853047
theorem B2737307 : Blo 1823613 2737307 := bstep (se 1 (by rfl) ⟨2052980, by rfl⟩ : syracuseStep 2737307 = 4105961) B4105961
theorem B4105385 : Blo 1823613 4105385 := bstep (se 2 (by rfl) ⟨1539519, by rfl⟩ : syracuseStep 4105385 = 3079039) B3079039
theorem B4384235 : Blo 1823613 4384235 := bstep (se 1 (by rfl) ⟨3288176, by rfl⟩ : syracuseStep 4384235 = 6576353) B6576353
theorem B24962813 : Blo 1823613 24962813 := bstep (se 3 (by rfl) ⟨4680527, by rfl⟩ : syracuseStep 24962813 = 9361055) B9361055
theorem B4106447 : Blo 1823613 4106447 := bstep (se 1 (by rfl) ⟨3079835, by rfl⟩ : syracuseStep 4106447 = 6159671) B6159671
theorem B202402151 : Blo 1823613 202402151 := bstep (se 1 (by rfl) ⟨151801613, by rfl⟩ : syracuseStep 202402151 = 303603227) B303603227
theorem B4107419 : Blo 1823613 4107419 := bstep (se 1 (by rfl) ⟨3080564, by rfl⟩ : syracuseStep 4107419 = 6161129) B6161129
theorem B6926107 : Blo 1823613 6926107 := bstep (se 1 (by rfl) ⟨5194580, by rfl⟩ : syracuseStep 6926107 = 10389161) B10389161
theorem B13856831 : Blo 1823613 13856831 := bstep (se 1 (by rfl) ⟨10392623, by rfl⟩ : syracuseStep 13856831 = 20785247) B20785247
theorem B2773183 : Blo 1823613 2773183 := bstep (se 1 (by rfl) ⟨2079887, by rfl⟩ : syracuseStep 2773183 = 4159775) B4159775
theorem B5550697 : Blo 1823613 5550697 := bstep (se 2 (by rfl) ⟨2081511, by rfl⟩ : syracuseStep 5550697 = 4163023) B4163023
theorem B11694779 : Blo 1823613 11694779 := bstep (se 1 (by rfl) ⟨8771084, by rfl⟩ : syracuseStep 11694779 = 17542169) B17542169
theorem B2053147 : Blo 1823613 2053147 := bstep (se 1 (by rfl) ⟨1539860, by rfl⟩ : syracuseStep 2053147 = 3079721) B3079721
theorem B38491645 : Blo 1823613 38491645 := bstep (se 3 (by rfl) ⟨7217183, by rfl⟩ : syracuseStep 38491645 = 14434367) B14434367
theorem B1824383 : Blo 1823613 1824383 := bstep (se 1 (by rfl) ⟨1368287, by rfl⟩ : syracuseStep 1824383 = 2736575) B2736575
theorem B2053759 : Blo 1823613 2053759 := bstep (se 1 (by rfl) ⟨1540319, by rfl⟩ : syracuseStep 2053759 = 3080639) B3080639
theorem B3462887 : Blo 1823613 3462887 := bstep (se 1 (by rfl) ⟨2597165, by rfl⟩ : syracuseStep 3462887 = 5194331) B5194331
theorem B359889227 : Blo 1823613 359889227 := bstep (se 1 (by rfl) ⟨269916920, by rfl⟩ : syracuseStep 359889227 = 539833841) B539833841
theorem B13850999 : Blo 1823613 13850999 := bstep (se 1 (by rfl) ⟨10388249, by rfl⟩ : syracuseStep 13850999 = 20776499) B20776499
theorem B13146707 : Blo 1823613 13146707 := bstep (se 1 (by rfl) ⟨9860030, by rfl⟩ : syracuseStep 13146707 = 19720061) B19720061
theorem B18717337 : Blo 1823613 18717337 := bstep (se 2 (by rfl) ⟨7019001, by rfl⟩ : syracuseStep 18717337 = 14038003) B14038003
theorem B1825487 : Blo 1823613 1825487 := bstep (se 1 (by rfl) ⟨1369115, by rfl⟩ : syracuseStep 1825487 = 2738231) B2738231
theorem B59194435 : Blo 1823613 59194435 := bstep (se 1 (by rfl) ⟨44395826, by rfl⟩ : syracuseStep 59194435 = 88791653) B88791653
theorem B4103279 : Blo 1823613 4103279 := bstep (se 1 (by rfl) ⟨3077459, by rfl⟩ : syracuseStep 4103279 = 6154919) B6154919
theorem B30006811 : Blo 1823613 30006811 := bstep (se 1 (by rfl) ⟨22505108, by rfl⟩ : syracuseStep 30006811 = 45010217) B45010217
theorem B2735903 : Blo 1823613 2735903 := bstep (se 1 (by rfl) ⟨2051927, by rfl⟩ : syracuseStep 2735903 = 4103855) B4103855
theorem B29605661 : Blo 1823613 29605661 := bstep (se 3 (by rfl) ⟨5551061, by rfl⟩ : syracuseStep 29605661 = 11102123) B11102123
theorem B23380123 : Blo 1823613 23380123 := bstep (se 1 (by rfl) ⟨17535092, by rfl⟩ : syracuseStep 23380123 = 35070185) B35070185
theorem B2736731 : Blo 1823613 2736731 := bstep (se 1 (by rfl) ⟨2052548, by rfl⟩ : syracuseStep 2736731 = 4105097) B4105097
theorem B2736923 : Blo 1823613 2736923 := bstep (se 1 (by rfl) ⟨2052692, by rfl⟩ : syracuseStep 2736923 = 4105385) B4105385
theorem B2737529 : Blo 1823613 2737529 := bstep (se 2 (by rfl) ⟨1026573, by rfl⟩ : syracuseStep 2737529 = 2053147) B2053147
theorem B2737631 : Blo 1823613 2737631 := bstep (se 1 (by rfl) ⟨2053223, by rfl⟩ : syracuseStep 2737631 = 4106447) B4106447
theorem B9233999 : Blo 1823613 9233999 := bstep (se 1 (by rfl) ⟨6925499, by rfl⟩ : syracuseStep 9233999 = 13850999) B13850999
theorem B2738279 : Blo 1823613 2738279 := bstep (se 1 (by rfl) ⟨2053709, by rfl⟩ : syracuseStep 2738279 = 4107419) B4107419
theorem B2738345 : Blo 1823613 2738345 := bstep (se 2 (by rfl) ⟨1026879, by rfl⟩ : syracuseStep 2738345 = 2053759) B2053759
theorem B9234809 : Blo 1823613 9234809 := bstep (se 2 (by rfl) ⟨3463053, by rfl⟩ : syracuseStep 9234809 = 6926107) B6926107
theorem B19737107 : Blo 1823613 19737107 := bstep (se 1 (by rfl) ⟨14802830, by rfl⟩ : syracuseStep 19737107 = 29605661) B29605661
theorem B3697577 : Blo 1823613 3697577 := bstep (se 2 (by rfl) ⟨1386591, by rfl⟩ : syracuseStep 3697577 = 2773183) B2773183
theorem B7400929 : Blo 1823613 7400929 := bstep (se 2 (by rfl) ⟨2775348, by rfl⟩ : syracuseStep 7400929 = 5550697) B5550697
theorem B16641875 : Blo 1823613 16641875 := bstep (se 1 (by rfl) ⟨12481406, by rfl⟩ : syracuseStep 16641875 = 24962813) B24962813
theorem B78925913 : Blo 1823613 78925913 := bstep (se 2 (by rfl) ⟨29597217, by rfl⟩ : syracuseStep 78925913 = 59194435) B59194435
theorem B51294305 : Blo 1823613 51294305 := bstep (se 2 (by rfl) ⟨19235364, by rfl⟩ : syracuseStep 51294305 = 38470729) B38470729
theorem B134934767 : Blo 1823613 134934767 := bstep (se 1 (by rfl) ⟨101201075, by rfl⟩ : syracuseStep 134934767 = 202402151) B202402151
theorem B1823935 : Blo 1823613 1823935 := bstep (se 1 (by rfl) ⟨1367951, by rfl⟩ : syracuseStep 1823935 = 2735903) B2735903
theorem B9237887 : Blo 1823613 9237887 := bstep (se 1 (by rfl) ⟨6928415, by rfl⟩ : syracuseStep 9237887 = 13856831) B13856831
theorem B7796519 : Blo 1823613 7796519 := bstep (se 1 (by rfl) ⟨5847389, by rfl⟩ : syracuseStep 7796519 = 11694779) B11694779
theorem B1824871 : Blo 1823613 1824871 := bstep (se 1 (by rfl) ⟨1368653, by rfl⟩ : syracuseStep 1824871 = 2737307) B2737307
theorem B99825797 : Blo 1823613 99825797 := bstep (se 4 (by rfl) ⟨9358668, by rfl⟩ : syracuseStep 99825797 = 18717337) B18717337
theorem B2922823 : Blo 1823613 2922823 := bstep (se 1 (by rfl) ⟨2192117, by rfl⟩ : syracuseStep 2922823 = 4384235) B4384235
theorem B2308591 : Blo 1823613 2308591 := bstep (se 1 (by rfl) ⟨1731443, by rfl⟩ : syracuseStep 2308591 = 3462887) B3462887
theorem B239926151 : Blo 1823613 239926151 := bstep (se 1 (by rfl) ⟨179944613, by rfl⟩ : syracuseStep 239926151 = 359889227) B359889227
theorem B8764471 : Blo 1823613 8764471 := bstep (se 1 (by rfl) ⟨6573353, by rfl⟩ : syracuseStep 8764471 = 13146707) B13146707
theorem B51322193 : Blo 1823613 51322193 := bstep (se 2 (by rfl) ⟨19245822, by rfl⟩ : syracuseStep 51322193 = 38491645) B38491645
theorem B40009081 : Blo 1823613 40009081 := bstep (se 2 (by rfl) ⟨15003405, by rfl⟩ : syracuseStep 40009081 = 30006811) B30006811
theorem B2735519 : Blo 1823613 2735519 := bstep (se 1 (by rfl) ⟨2051639, by rfl⟩ : syracuseStep 2735519 = 4103279) B4103279
theorem B52617275 : Blo 1823613 52617275 := bstep (se 1 (by rfl) ⟨39462956, by rfl⟩ : syracuseStep 52617275 = 78925913) B78925913
theorem B89956511 : Blo 1823613 89956511 := bstep (se 1 (by rfl) ⟨67467383, by rfl⟩ : syracuseStep 89956511 = 134934767) B134934767
theorem B13158071 : Blo 1823613 13158071 := bstep (se 1 (by rfl) ⟨9868553, by rfl⟩ : syracuseStep 13158071 = 19737107) B19737107
theorem B11094583 : Blo 1823613 11094583 := bstep (se 1 (by rfl) ⟨8320937, by rfl⟩ : syracuseStep 11094583 = 16641875) B16641875
theorem B34196203 : Blo 1823613 34196203 := bstep (se 1 (by rfl) ⟨25647152, by rfl⟩ : syracuseStep 34196203 = 51294305) B51294305
theorem B31173497 : Blo 1823613 31173497 := bstep (se 2 (by rfl) ⟨11690061, by rfl⟩ : syracuseStep 31173497 = 23380123) B23380123
theorem B6155999 : Blo 1823613 6155999 := bstep (se 1 (by rfl) ⟨4616999, by rfl⟩ : syracuseStep 6155999 = 9233999) B9233999
theorem B5197679 : Blo 1823613 5197679 := bstep (se 1 (by rfl) ⟨3898259, by rfl⟩ : syracuseStep 5197679 = 7796519) B7796519
theorem B11685961 : Blo 1823613 11685961 := bstep (se 2 (by rfl) ⟨4382235, by rfl⟩ : syracuseStep 11685961 = 8764471) B8764471
theorem B6156539 : Blo 1823613 6156539 := bstep (se 1 (by rfl) ⟨4617404, by rfl⟩ : syracuseStep 6156539 = 9234809) B9234809
theorem B9867905 : Blo 1823613 9867905 := bstep (se 2 (by rfl) ⟨3700464, by rfl⟩ : syracuseStep 9867905 = 7400929) B7400929
theorem B34214795 : Blo 1823613 34214795 := bstep (se 1 (by rfl) ⟨25661096, by rfl⟩ : syracuseStep 34214795 = 51322193) B51322193
theorem B1823679 : Blo 1823613 1823679 := bstep (se 1 (by rfl) ⟨1367759, by rfl⟩ : syracuseStep 1823679 = 2735519) B2735519
theorem B1824487 : Blo 1823613 1824487 := bstep (se 1 (by rfl) ⟨1368365, by rfl⟩ : syracuseStep 1824487 = 2736731) B2736731
theorem B1824615 : Blo 1823613 1824615 := bstep (se 1 (by rfl) ⟨1368461, by rfl⟩ : syracuseStep 1824615 = 2736923) B2736923
theorem B3078121 : Blo 1823613 3078121 := bstep (se 2 (by rfl) ⟨1154295, by rfl⟩ : syracuseStep 3078121 = 2308591) B2308591
theorem B1825019 : Blo 1823613 1825019 := bstep (se 1 (by rfl) ⟨1368764, by rfl⟩ : syracuseStep 1825019 = 2737529) B2737529
theorem B6158591 : Blo 1823613 6158591 := bstep (se 1 (by rfl) ⟨4618943, by rfl⟩ : syracuseStep 6158591 = 9237887) B9237887
theorem B1825087 : Blo 1823613 1825087 := bstep (se 1 (by rfl) ⟨1368815, by rfl⟩ : syracuseStep 1825087 = 2737631) B2737631
theorem B1825519 : Blo 1823613 1825519 := bstep (se 1 (by rfl) ⟨1369139, by rfl⟩ : syracuseStep 1825519 = 2738279) B2738279
theorem B66550531 : Blo 1823613 66550531 := bstep (se 1 (by rfl) ⟨49912898, by rfl⟩ : syracuseStep 66550531 = 99825797) B99825797
theorem B1825563 : Blo 1823613 1825563 := bstep (se 1 (by rfl) ⟨1369172, by rfl⟩ : syracuseStep 1825563 = 2738345) B2738345
theorem B15588389 : Blo 1823613 15588389 := bstep (se 4 (by rfl) ⟨1461411, by rfl⟩ : syracuseStep 15588389 = 2922823) B2922823
theorem B53345441 : Blo 1823613 53345441 := bstep (se 2 (by rfl) ⟨20004540, by rfl⟩ : syracuseStep 53345441 = 40009081) B40009081
theorem B2465051 : Blo 1823613 2465051 := bstep (se 1 (by rfl) ⟨1848788, by rfl⟩ : syracuseStep 2465051 = 3697577) B3697577
theorem B639803069 : Blo 1823613 639803069 := bstep (se 3 (by rfl) ⟨119963075, by rfl⟩ : syracuseStep 639803069 = 239926151) B239926151
theorem B35078183 : Blo 1823613 35078183 := bstep (se 1 (by rfl) ⟨26308637, by rfl⟩ : syracuseStep 35078183 = 52617275) B52617275
theorem B15581281 : Blo 1823613 15581281 := bstep (se 2 (by rfl) ⟨5842980, by rfl⟩ : syracuseStep 15581281 = 11685961) B11685961
theorem B4104359 : Blo 1823613 4104359 := bstep (se 1 (by rfl) ⟨3078269, by rfl⟩ : syracuseStep 4104359 = 6156539) B6156539
theorem B6578603 : Blo 1823613 6578603 := bstep (se 1 (by rfl) ⟨4933952, by rfl⟩ : syracuseStep 6578603 = 9867905) B9867905
theorem B4105727 : Blo 1823613 4105727 := bstep (se 1 (by rfl) ⟨3079295, by rfl⟩ : syracuseStep 4105727 = 6158591) B6158591
theorem B35563627 : Blo 1823613 35563627 := bstep (se 1 (by rfl) ⟨26672720, by rfl⟩ : syracuseStep 35563627 = 53345441) B53345441
theorem B426535379 : Blo 1823613 426535379 := bstep (se 1 (by rfl) ⟨319901534, by rfl⟩ : syracuseStep 426535379 = 639803069) B639803069
theorem B22809863 : Blo 1823613 22809863 := bstep (se 1 (by rfl) ⟨17107397, by rfl⟩ : syracuseStep 22809863 = 34214795) B34214795
theorem B6573469 : Blo 1823613 6573469 := bstep (se 3 (by rfl) ⟨1232525, by rfl⟩ : syracuseStep 6573469 = 2465051) B2465051
theorem B10392259 : Blo 1823613 10392259 := bstep (se 1 (by rfl) ⟨7794194, by rfl⟩ : syracuseStep 10392259 = 15588389) B15588389
theorem B59971007 : Blo 1823613 59971007 := bstep (se 1 (by rfl) ⟨44978255, by rfl⟩ : syracuseStep 59971007 = 89956511) B89956511
theorem B14792777 : Blo 1823613 14792777 := bstep (se 2 (by rfl) ⟨5547291, by rfl⟩ : syracuseStep 14792777 = 11094583) B11094583
theorem B45594937 : Blo 1823613 45594937 := bstep (se 2 (by rfl) ⟨17098101, by rfl⟩ : syracuseStep 45594937 = 34196203) B34196203
theorem B88734041 : Blo 1823613 88734041 := bstep (se 2 (by rfl) ⟨33275265, by rfl⟩ : syracuseStep 88734041 = 66550531) B66550531
theorem B8772047 : Blo 1823613 8772047 := bstep (se 1 (by rfl) ⟨6579035, by rfl⟩ : syracuseStep 8772047 = 13158071) B13158071
theorem B20782331 : Blo 1823613 20782331 := bstep (se 1 (by rfl) ⟨15586748, by rfl⟩ : syracuseStep 20782331 = 31173497) B31173497
theorem B4103999 : Blo 1823613 4103999 := bstep (se 1 (by rfl) ⟨3077999, by rfl⟩ : syracuseStep 4103999 = 6155999) B6155999
theorem B3465119 : Blo 1823613 3465119 := bstep (se 1 (by rfl) ⟨2598839, by rfl⟩ : syracuseStep 3465119 = 5197679) B5197679
theorem B4104161 : Blo 1823613 4104161 := bstep (se 2 (by rfl) ⟨1539060, by rfl⟩ : syracuseStep 4104161 = 3078121) B3078121
theorem B2736239 : Blo 1823613 2736239 := bstep (se 1 (by rfl) ⟨2052179, by rfl⟩ : syracuseStep 2736239 = 4104359) B4104359
theorem B20775041 : Blo 1823613 20775041 := bstep (se 2 (by rfl) ⟨7790640, by rfl⟩ : syracuseStep 20775041 = 15581281) B15581281
theorem B60793249 : Blo 1823613 60793249 := bstep (se 2 (by rfl) ⟨22797468, by rfl⟩ : syracuseStep 60793249 = 45594937) B45594937
theorem B60826301 : Blo 1823613 60826301 := bstep (se 3 (by rfl) ⟨11404931, by rfl⟩ : syracuseStep 60826301 = 22809863) B22809863
theorem B2737151 : Blo 1823613 2737151 := bstep (se 1 (by rfl) ⟨2052863, by rfl⟩ : syracuseStep 2737151 = 4105727) B4105727
theorem B59156027 : Blo 1823613 59156027 := bstep (se 1 (by rfl) ⟨44367020, by rfl⟩ : syracuseStep 59156027 = 88734041) B88734041
theorem B13854887 : Blo 1823613 13854887 := bstep (se 1 (by rfl) ⟨10391165, by rfl⟩ : syracuseStep 13854887 = 20782331) B20782331
theorem B47418169 : Blo 1823613 47418169 := bstep (se 2 (by rfl) ⟨17781813, by rfl⟩ : syracuseStep 47418169 = 35563627) B35563627
theorem B4385735 : Blo 1823613 4385735 := bstep (se 1 (by rfl) ⟨3289301, by rfl⟩ : syracuseStep 4385735 = 6578603) B6578603
theorem B13856345 : Blo 1823613 13856345 := bstep (se 2 (by rfl) ⟨5196129, by rfl⟩ : syracuseStep 13856345 = 10392259) B10392259
theorem B39980671 : Blo 1823613 39980671 := bstep (se 1 (by rfl) ⟨29985503, by rfl⟩ : syracuseStep 39980671 = 59971007) B59971007
theorem B284356919 : Blo 1823613 284356919 := bstep (se 1 (by rfl) ⟨213267689, by rfl⟩ : syracuseStep 284356919 = 426535379) B426535379
theorem B23385455 : Blo 1823613 23385455 := bstep (se 1 (by rfl) ⟨17539091, by rfl⟩ : syracuseStep 23385455 = 35078183) B35078183
theorem B9861851 : Blo 1823613 9861851 := bstep (se 1 (by rfl) ⟨7396388, by rfl⟩ : syracuseStep 9861851 = 14792777) B14792777
theorem B5848031 : Blo 1823613 5848031 := bstep (se 1 (by rfl) ⟨4386023, by rfl⟩ : syracuseStep 5848031 = 8772047) B8772047
theorem B8764625 : Blo 1823613 8764625 := bstep (se 2 (by rfl) ⟨3286734, by rfl⟩ : syracuseStep 8764625 = 6573469) B6573469
theorem B9240317 : Blo 1823613 9240317 := bstep (se 3 (by rfl) ⟨1732559, by rfl⟩ : syracuseStep 9240317 = 3465119) B3465119
theorem B2735999 : Blo 1823613 2735999 := bstep (se 1 (by rfl) ⟨2051999, by rfl⟩ : syracuseStep 2735999 = 4103999) B4103999
theorem B2736107 : Blo 1823613 2736107 := bstep (se 1 (by rfl) ⟨2052080, by rfl⟩ : syracuseStep 2736107 = 4104161) B4104161
theorem B189571279 : Blo 1823613 189571279 := bstep (se 1 (by rfl) ⟨142178459, by rfl⟩ : syracuseStep 189571279 = 284356919) B284356919
theorem B40550867 : Blo 1823613 40550867 := bstep (se 1 (by rfl) ⟨30413150, by rfl⟩ : syracuseStep 40550867 = 60826301) B60826301
theorem B23372333 : Blo 1823613 23372333 := bstep (se 3 (by rfl) ⟨4382312, by rfl⟩ : syracuseStep 23372333 = 8764625) B8764625
theorem B213230245 : Blo 1823613 213230245 := bstep (se 4 (by rfl) ⟨19990335, by rfl⟩ : syracuseStep 213230245 = 39980671) B39980671
theorem B15590303 : Blo 1823613 15590303 := bstep (se 1 (by rfl) ⟨11692727, by rfl⟩ : syracuseStep 15590303 = 23385455) B23385455
theorem B39437351 : Blo 1823613 39437351 := bstep (se 1 (by rfl) ⟨29578013, by rfl⟩ : syracuseStep 39437351 = 59156027) B59156027
theorem B9236591 : Blo 1823613 9236591 := bstep (se 1 (by rfl) ⟨6927443, by rfl⟩ : syracuseStep 9236591 = 13854887) B13854887
theorem B6574567 : Blo 1823613 6574567 := bstep (se 1 (by rfl) ⟨4930925, by rfl⟩ : syracuseStep 6574567 = 9861851) B9861851
theorem B9237563 : Blo 1823613 9237563 := bstep (se 1 (by rfl) ⟨6928172, by rfl⟩ : syracuseStep 9237563 = 13856345) B13856345
theorem B1823999 : Blo 1823613 1823999 := bstep (se 1 (by rfl) ⟨1367999, by rfl⟩ : syracuseStep 1823999 = 2735999) B2735999
theorem B1824071 : Blo 1823613 1824071 := bstep (se 1 (by rfl) ⟨1368053, by rfl⟩ : syracuseStep 1824071 = 2736107) B2736107
theorem B1824159 : Blo 1823613 1824159 := bstep (se 1 (by rfl) ⟨1368119, by rfl⟩ : syracuseStep 1824159 = 2736239) B2736239
theorem B13850027 : Blo 1823613 13850027 := bstep (se 1 (by rfl) ⟨10387520, by rfl⟩ : syracuseStep 13850027 = 20775041) B20775041
theorem B81057665 : Blo 1823613 81057665 := bstep (se 2 (by rfl) ⟨30396624, by rfl⟩ : syracuseStep 81057665 = 60793249) B60793249
theorem B1824767 : Blo 1823613 1824767 := bstep (se 1 (by rfl) ⟨1368575, by rfl⟩ : syracuseStep 1824767 = 2737151) B2737151
theorem B63224225 : Blo 1823613 63224225 := bstep (se 2 (by rfl) ⟨23709084, by rfl⟩ : syracuseStep 63224225 = 47418169) B47418169
theorem B2923823 : Blo 1823613 2923823 := bstep (se 1 (by rfl) ⟨2192867, by rfl⟩ : syracuseStep 2923823 = 4385735) B4385735
theorem B3898687 : Blo 1823613 3898687 := bstep (se 1 (by rfl) ⟨2924015, by rfl⟩ : syracuseStep 3898687 = 5848031) B5848031
theorem B6160211 : Blo 1823613 6160211 := bstep (se 1 (by rfl) ⟨4620158, by rfl⟩ : syracuseStep 6160211 = 9240317) B9240317
theorem B27033911 : Blo 1823613 27033911 := bstep (se 1 (by rfl) ⟨20275433, by rfl⟩ : syracuseStep 27033911 = 40550867) B40550867
theorem B15581555 : Blo 1823613 15581555 := bstep (se 1 (by rfl) ⟨11686166, by rfl⟩ : syracuseStep 15581555 = 23372333) B23372333
theorem B8766089 : Blo 1823613 8766089 := bstep (se 2 (by rfl) ⟨3287283, by rfl⟩ : syracuseStep 8766089 = 6574567) B6574567
theorem B9233351 : Blo 1823613 9233351 := bstep (se 1 (by rfl) ⟨6925013, by rfl⟩ : syracuseStep 9233351 = 13850027) B13850027
theorem B42149483 : Blo 1823613 42149483 := bstep (se 1 (by rfl) ⟨31612112, by rfl⟩ : syracuseStep 42149483 = 63224225) B63224225
theorem B4106807 : Blo 1823613 4106807 := bstep (se 1 (by rfl) ⟨3080105, by rfl⟩ : syracuseStep 4106807 = 6160211) B6160211
theorem B26291567 : Blo 1823613 26291567 := bstep (se 1 (by rfl) ⟨19718675, by rfl⟩ : syracuseStep 26291567 = 39437351) B39437351
theorem B284306993 : Blo 1823613 284306993 := bstep (se 2 (by rfl) ⟨106615122, by rfl⟩ : syracuseStep 284306993 = 213230245) B213230245
theorem B54038443 : Blo 1823613 54038443 := bstep (se 1 (by rfl) ⟨40528832, by rfl⟩ : syracuseStep 54038443 = 81057665) B81057665
theorem B5198249 : Blo 1823613 5198249 := bstep (se 2 (by rfl) ⟨1949343, by rfl⟩ : syracuseStep 5198249 = 3898687) B3898687
theorem B6157727 : Blo 1823613 6157727 := bstep (se 1 (by rfl) ⟨4618295, by rfl⟩ : syracuseStep 6157727 = 9236591) B9236591
theorem B252761705 : Blo 1823613 252761705 := bstep (se 2 (by rfl) ⟨94785639, by rfl⟩ : syracuseStep 252761705 = 189571279) B189571279
theorem B10393535 : Blo 1823613 10393535 := bstep (se 1 (by rfl) ⟨7795151, by rfl⟩ : syracuseStep 10393535 = 15590303) B15590303
theorem B6158375 : Blo 1823613 6158375 := bstep (se 1 (by rfl) ⟨4618781, by rfl⟩ : syracuseStep 6158375 = 9237563) B9237563
theorem B7796861 : Blo 1823613 7796861 := bstep (se 3 (by rfl) ⟨1461911, by rfl⟩ : syracuseStep 7796861 = 2923823) B2923823
theorem B18022607 : Blo 1823613 18022607 := bstep (se 1 (by rfl) ⟨13516955, by rfl⟩ : syracuseStep 18022607 = 27033911) B27033911
theorem B10387703 : Blo 1823613 10387703 := bstep (se 1 (by rfl) ⟨7790777, by rfl⟩ : syracuseStep 10387703 = 15581555) B15581555
theorem B3465499 : Blo 1823613 3465499 := bstep (se 1 (by rfl) ⟨2599124, by rfl⟩ : syracuseStep 3465499 = 5198249) B5198249
theorem B4105151 : Blo 1823613 4105151 := bstep (se 1 (by rfl) ⟨3078863, by rfl⟩ : syracuseStep 4105151 = 6157727) B6157727
theorem B28099655 : Blo 1823613 28099655 := bstep (se 1 (by rfl) ⟨21074741, by rfl⟩ : syracuseStep 28099655 = 42149483) B42149483
theorem B4105583 : Blo 1823613 4105583 := bstep (se 1 (by rfl) ⟨3079187, by rfl⟩ : syracuseStep 4105583 = 6158375) B6158375
theorem B2737871 : Blo 1823613 2737871 := bstep (se 1 (by rfl) ⟨2053403, by rfl⟩ : syracuseStep 2737871 = 4106807) B4106807
theorem B72051257 : Blo 1823613 72051257 := bstep (se 2 (by rfl) ⟨27019221, by rfl⟩ : syracuseStep 72051257 = 54038443) B54038443
theorem B5844059 : Blo 1823613 5844059 := bstep (se 1 (by rfl) ⟨4383044, by rfl⟩ : syracuseStep 5844059 = 8766089) B8766089
theorem B6155567 : Blo 1823613 6155567 := bstep (se 1 (by rfl) ⟨4616675, by rfl⟩ : syracuseStep 6155567 = 9233351) B9233351
theorem B70110845 : Blo 1823613 70110845 := bstep (se 3 (by rfl) ⟨13145783, by rfl⟩ : syracuseStep 70110845 = 26291567) B26291567
theorem B5197907 : Blo 1823613 5197907 := bstep (se 1 (by rfl) ⟨3898430, by rfl⟩ : syracuseStep 5197907 = 7796861) B7796861
theorem B168507803 : Blo 1823613 168507803 := bstep (se 1 (by rfl) ⟨126380852, by rfl⟩ : syracuseStep 168507803 = 252761705) B252761705
theorem B6929023 : Blo 1823613 6929023 := bstep (se 1 (by rfl) ⟨5196767, by rfl⟩ : syracuseStep 6929023 = 10393535) B10393535
theorem B189537995 : Blo 1823613 189537995 := bstep (se 1 (by rfl) ⟨142153496, by rfl⟩ : syracuseStep 189537995 = 284306993) B284306993
theorem B3465271 : Blo 1823613 3465271 := bstep (se 1 (by rfl) ⟨2598953, by rfl⟩ : syracuseStep 3465271 = 5197907) B5197907
theorem B4620665 : Blo 1823613 4620665 := bstep (se 2 (by rfl) ⟨1732749, by rfl⟩ : syracuseStep 4620665 = 3465499) B3465499
theorem B2736767 : Blo 1823613 2736767 := bstep (se 1 (by rfl) ⟨2052575, by rfl⟩ : syracuseStep 2736767 = 4105151) B4105151
theorem B2737055 : Blo 1823613 2737055 := bstep (se 1 (by rfl) ⟨2052791, by rfl⟩ : syracuseStep 2737055 = 4105583) B4105583
theorem B112338535 : Blo 1823613 112338535 := bstep (se 1 (by rfl) ⟨84253901, by rfl⟩ : syracuseStep 112338535 = 168507803) B168507803
theorem B6925135 : Blo 1823613 6925135 := bstep (se 1 (by rfl) ⟨5193851, by rfl⟩ : syracuseStep 6925135 = 10387703) B10387703
theorem B48034171 : Blo 1823613 48034171 := bstep (se 1 (by rfl) ⟨36025628, by rfl⟩ : syracuseStep 48034171 = 72051257) B72051257
theorem B505434653 : Blo 1823613 505434653 := bstep (se 3 (by rfl) ⟨94768997, by rfl⟩ : syracuseStep 505434653 = 189537995) B189537995
theorem B3896039 : Blo 1823613 3896039 := bstep (se 1 (by rfl) ⟨2922029, by rfl⟩ : syracuseStep 3896039 = 5844059) B5844059
theorem B46740563 : Blo 1823613 46740563 := bstep (se 1 (by rfl) ⟨35055422, by rfl⟩ : syracuseStep 46740563 = 70110845) B70110845
theorem B12015071 : Blo 1823613 12015071 := bstep (se 1 (by rfl) ⟨9011303, by rfl⟩ : syracuseStep 12015071 = 18022607) B18022607
theorem B18733103 : Blo 1823613 18733103 := bstep (se 1 (by rfl) ⟨14049827, by rfl⟩ : syracuseStep 18733103 = 28099655) B28099655
theorem B9238697 : Blo 1823613 9238697 := bstep (se 2 (by rfl) ⟨3464511, by rfl⟩ : syracuseStep 9238697 = 6929023) B6929023
theorem B1825247 : Blo 1823613 1825247 := bstep (se 1 (by rfl) ⟨1368935, by rfl⟩ : syracuseStep 1825247 = 2737871) B2737871
theorem B4103711 : Blo 1823613 4103711 := bstep (se 1 (by rfl) ⟨3077783, by rfl⟩ : syracuseStep 4103711 = 6155567) B6155567
theorem B4620361 : Blo 1823613 4620361 := bstep (se 2 (by rfl) ⟨1732635, by rfl⟩ : syracuseStep 4620361 = 3465271) B3465271
theorem B3080443 : Blo 1823613 3080443 := bstep (se 1 (by rfl) ⟨2310332, by rfl⟩ : syracuseStep 3080443 = 4620665) B4620665
theorem B2597359 : Blo 1823613 2597359 := bstep (se 1 (by rfl) ⟨1948019, by rfl⟩ : syracuseStep 2597359 = 3896039) B3896039
theorem B64045561 : Blo 1823613 64045561 := bstep (se 2 (by rfl) ⟨24017085, by rfl⟩ : syracuseStep 64045561 = 48034171) B48034171
theorem B9233513 : Blo 1823613 9233513 := bstep (se 2 (by rfl) ⟨3462567, by rfl⟩ : syracuseStep 9233513 = 6925135) B6925135
theorem B149784713 : Blo 1823613 149784713 := bstep (se 2 (by rfl) ⟨56169267, by rfl⟩ : syracuseStep 149784713 = 112338535) B112338535
theorem B336956435 : Blo 1823613 336956435 := bstep (se 1 (by rfl) ⟨252717326, by rfl⟩ : syracuseStep 336956435 = 505434653) B505434653
theorem B12488735 : Blo 1823613 12488735 := bstep (se 1 (by rfl) ⟨9366551, by rfl⟩ : syracuseStep 12488735 = 18733103) B18733103
theorem B1824511 : Blo 1823613 1824511 := bstep (se 1 (by rfl) ⟨1368383, by rfl⟩ : syracuseStep 1824511 = 2736767) B2736767
theorem B1824703 : Blo 1823613 1824703 := bstep (se 1 (by rfl) ⟨1368527, by rfl⟩ : syracuseStep 1824703 = 2737055) B2737055
theorem B31160375 : Blo 1823613 31160375 := bstep (se 1 (by rfl) ⟨23370281, by rfl⟩ : syracuseStep 31160375 = 46740563) B46740563
theorem B8010047 : Blo 1823613 8010047 := bstep (se 1 (by rfl) ⟨6007535, by rfl⟩ : syracuseStep 8010047 = 12015071) B12015071
theorem B6159131 : Blo 1823613 6159131 := bstep (se 1 (by rfl) ⟨4619348, by rfl⟩ : syracuseStep 6159131 = 9238697) B9238697
theorem B2735807 : Blo 1823613 2735807 := bstep (se 1 (by rfl) ⟨2051855, by rfl⟩ : syracuseStep 2735807 = 4103711) B4103711
theorem B6160481 : Blo 1823613 6160481 := bstep (se 2 (by rfl) ⟨2310180, by rfl⟩ : syracuseStep 6160481 = 4620361) B4620361
theorem B85394081 : Blo 1823613 85394081 := bstep (se 2 (by rfl) ⟨32022780, by rfl⟩ : syracuseStep 85394081 = 64045561) B64045561
theorem B4106087 : Blo 1823613 4106087 := bstep (se 1 (by rfl) ⟨3079565, by rfl⟩ : syracuseStep 4106087 = 6159131) B6159131
theorem B8325823 : Blo 1823613 8325823 := bstep (se 1 (by rfl) ⟨6244367, by rfl⟩ : syracuseStep 8325823 = 12488735) B12488735
theorem B4107257 : Blo 1823613 4107257 := bstep (se 2 (by rfl) ⟨1540221, by rfl⟩ : syracuseStep 4107257 = 3080443) B3080443
theorem B6155675 : Blo 1823613 6155675 := bstep (se 1 (by rfl) ⟨4616756, by rfl⟩ : syracuseStep 6155675 = 9233513) B9233513
theorem B21360125 : Blo 1823613 21360125 := bstep (se 3 (by rfl) ⟨4005023, by rfl⟩ : syracuseStep 21360125 = 8010047) B8010047
theorem B99856475 : Blo 1823613 99856475 := bstep (se 1 (by rfl) ⟨74892356, by rfl⟩ : syracuseStep 99856475 = 149784713) B149784713
theorem B224637623 : Blo 1823613 224637623 := bstep (se 1 (by rfl) ⟨168478217, by rfl⟩ : syracuseStep 224637623 = 336956435) B336956435
theorem B1823871 : Blo 1823613 1823871 := bstep (se 1 (by rfl) ⟨1367903, by rfl⟩ : syracuseStep 1823871 = 2735807) B2735807
theorem B3463145 : Blo 1823613 3463145 := bstep (se 2 (by rfl) ⟨1298679, by rfl⟩ : syracuseStep 3463145 = 2597359) B2597359
theorem B20773583 : Blo 1823613 20773583 := bstep (se 1 (by rfl) ⟨15580187, by rfl⟩ : syracuseStep 20773583 = 31160375) B31160375
theorem B149758415 : Blo 1823613 149758415 := bstep (se 1 (by rfl) ⟨112318811, by rfl⟩ : syracuseStep 149758415 = 224637623) B224637623
theorem B11101097 : Blo 1823613 11101097 := bstep (se 2 (by rfl) ⟨4162911, by rfl⟩ : syracuseStep 11101097 = 8325823) B8325823
theorem B2737391 : Blo 1823613 2737391 := bstep (se 1 (by rfl) ⟨2053043, by rfl⟩ : syracuseStep 2737391 = 4106087) B4106087
theorem B56960333 : Blo 1823613 56960333 := bstep (se 3 (by rfl) ⟨10680062, by rfl⟩ : syracuseStep 56960333 = 21360125) B21360125
theorem B2738171 : Blo 1823613 2738171 := bstep (se 1 (by rfl) ⟨2053628, by rfl⟩ : syracuseStep 2738171 = 4107257) B4107257
theorem B66570983 : Blo 1823613 66570983 := bstep (se 1 (by rfl) ⟨49928237, by rfl⟩ : syracuseStep 66570983 = 99856475) B99856475
theorem B4106987 : Blo 1823613 4106987 := bstep (se 1 (by rfl) ⟨3080240, by rfl⟩ : syracuseStep 4106987 = 6160481) B6160481
theorem B56929387 : Blo 1823613 56929387 := bstep (se 1 (by rfl) ⟨42697040, by rfl⟩ : syracuseStep 56929387 = 85394081) B85394081
theorem B13849055 : Blo 1823613 13849055 := bstep (se 1 (by rfl) ⟨10386791, by rfl⟩ : syracuseStep 13849055 = 20773583) B20773583
theorem B2308763 : Blo 1823613 2308763 := bstep (se 1 (by rfl) ⟨1731572, by rfl⟩ : syracuseStep 2308763 = 3463145) B3463145
theorem B4103783 : Blo 1823613 4103783 := bstep (se 1 (by rfl) ⟨3077837, by rfl⟩ : syracuseStep 4103783 = 6155675) B6155675
theorem B9232703 : Blo 1823613 9232703 := bstep (se 1 (by rfl) ⟨6924527, by rfl⟩ : syracuseStep 9232703 = 13849055) B13849055
theorem B2737991 : Blo 1823613 2737991 := bstep (se 1 (by rfl) ⟨2053493, by rfl⟩ : syracuseStep 2737991 = 4106987) B4106987
theorem B99838943 : Blo 1823613 99838943 := bstep (se 1 (by rfl) ⟨74879207, by rfl⟩ : syracuseStep 99838943 = 149758415) B149758415
theorem B37973555 : Blo 1823613 37973555 := bstep (se 1 (by rfl) ⟨28480166, by rfl⟩ : syracuseStep 37973555 = 56960333) B56960333
theorem B6156701 : Blo 1823613 6156701 := bstep (se 3 (by rfl) ⟨1154381, by rfl⟩ : syracuseStep 6156701 = 2308763) B2308763
theorem B44380655 : Blo 1823613 44380655 := bstep (se 1 (by rfl) ⟨33285491, by rfl⟩ : syracuseStep 44380655 = 66570983) B66570983
theorem B29602925 : Blo 1823613 29602925 := bstep (se 3 (by rfl) ⟨5550548, by rfl⟩ : syracuseStep 29602925 = 11101097) B11101097
theorem B1824927 : Blo 1823613 1824927 := bstep (se 1 (by rfl) ⟨1368695, by rfl⟩ : syracuseStep 1824927 = 2737391) B2737391
theorem B1825447 : Blo 1823613 1825447 := bstep (se 1 (by rfl) ⟨1369085, by rfl⟩ : syracuseStep 1825447 = 2738171) B2738171
theorem B75905849 : Blo 1823613 75905849 := bstep (se 2 (by rfl) ⟨28464693, by rfl⟩ : syracuseStep 75905849 = 56929387) B56929387
theorem B2735855 : Blo 1823613 2735855 := bstep (se 1 (by rfl) ⟨2051891, by rfl⟩ : syracuseStep 2735855 = 4103783) B4103783
theorem B4104467 : Blo 1823613 4104467 := bstep (se 1 (by rfl) ⟨3078350, by rfl⟩ : syracuseStep 4104467 = 6156701) B6156701
theorem B19735283 : Blo 1823613 19735283 := bstep (se 1 (by rfl) ⟨14801462, by rfl⟩ : syracuseStep 19735283 = 29602925) B29602925
theorem B25315703 : Blo 1823613 25315703 := bstep (se 1 (by rfl) ⟨18986777, by rfl⟩ : syracuseStep 25315703 = 37973555) B37973555
theorem B6155135 : Blo 1823613 6155135 := bstep (se 1 (by rfl) ⟨4616351, by rfl⟩ : syracuseStep 6155135 = 9232703) B9232703
theorem B1823903 : Blo 1823613 1823903 := bstep (se 1 (by rfl) ⟨1367927, by rfl⟩ : syracuseStep 1823903 = 2735855) B2735855
theorem B29587103 : Blo 1823613 29587103 := bstep (se 1 (by rfl) ⟨22190327, by rfl⟩ : syracuseStep 29587103 = 44380655) B44380655
theorem B1825327 : Blo 1823613 1825327 := bstep (se 1 (by rfl) ⟨1368995, by rfl⟩ : syracuseStep 1825327 = 2737991) B2737991
theorem B66559295 : Blo 1823613 66559295 := bstep (se 1 (by rfl) ⟨49919471, by rfl⟩ : syracuseStep 66559295 = 99838943) B99838943
theorem B202415597 : Blo 1823613 202415597 := bstep (se 3 (by rfl) ⟨37952924, by rfl⟩ : syracuseStep 202415597 = 75905849) B75905849
theorem B2736311 : Blo 1823613 2736311 := bstep (se 1 (by rfl) ⟨2052233, by rfl⟩ : syracuseStep 2736311 = 4104467) B4104467
theorem B16877135 : Blo 1823613 16877135 := bstep (se 1 (by rfl) ⟨12657851, by rfl⟩ : syracuseStep 16877135 = 25315703) B25315703
theorem B52627421 : Blo 1823613 52627421 := bstep (se 3 (by rfl) ⟨9867641, by rfl⟩ : syracuseStep 52627421 = 19735283) B19735283
theorem B44372863 : Blo 1823613 44372863 := bstep (se 1 (by rfl) ⟨33279647, by rfl⟩ : syracuseStep 44372863 = 66559295) B66559295
theorem B134943731 : Blo 1823613 134943731 := bstep (se 1 (by rfl) ⟨101207798, by rfl⟩ : syracuseStep 134943731 = 202415597) B202415597
theorem B19724735 : Blo 1823613 19724735 := bstep (se 1 (by rfl) ⟨14793551, by rfl⟩ : syracuseStep 19724735 = 29587103) B29587103
theorem B4103423 : Blo 1823613 4103423 := bstep (se 1 (by rfl) ⟨3077567, by rfl⟩ : syracuseStep 4103423 = 6155135) B6155135
theorem B59163817 : Blo 1823613 59163817 := bstep (se 2 (by rfl) ⟨22186431, by rfl⟩ : syracuseStep 59163817 = 44372863) B44372863
theorem B13149823 : Blo 1823613 13149823 := bstep (se 1 (by rfl) ⟨9862367, by rfl⟩ : syracuseStep 13149823 = 19724735) B19724735
theorem B11251423 : Blo 1823613 11251423 := bstep (se 1 (by rfl) ⟨8438567, by rfl⟩ : syracuseStep 11251423 = 16877135) B16877135
theorem B1824207 : Blo 1823613 1824207 := bstep (se 1 (by rfl) ⟨1368155, by rfl⟩ : syracuseStep 1824207 = 2736311) B2736311
theorem B89962487 : Blo 1823613 89962487 := bstep (se 1 (by rfl) ⟨67471865, by rfl⟩ : syracuseStep 89962487 = 134943731) B134943731
theorem B35084947 : Blo 1823613 35084947 := bstep (se 1 (by rfl) ⟨26313710, by rfl⟩ : syracuseStep 35084947 = 52627421) B52627421
theorem B2735615 : Blo 1823613 2735615 := bstep (se 1 (by rfl) ⟨2051711, by rfl⟩ : syracuseStep 2735615 = 4103423) B4103423
theorem B59974991 : Blo 1823613 59974991 := bstep (se 1 (by rfl) ⟨44981243, by rfl⟩ : syracuseStep 59974991 = 89962487) B89962487
theorem B17533097 : Blo 1823613 17533097 := bstep (se 2 (by rfl) ⟨6574911, by rfl⟩ : syracuseStep 17533097 = 13149823) B13149823
theorem B15001897 : Blo 1823613 15001897 := bstep (se 2 (by rfl) ⟨5625711, by rfl⟩ : syracuseStep 15001897 = 11251423) B11251423
theorem B46779929 : Blo 1823613 46779929 := bstep (se 2 (by rfl) ⟨17542473, by rfl⟩ : syracuseStep 46779929 = 35084947) B35084947
theorem B78885089 : Blo 1823613 78885089 := bstep (se 2 (by rfl) ⟨29581908, by rfl⟩ : syracuseStep 78885089 = 59163817) B59163817
theorem B1823743 : Blo 1823613 1823743 := bstep (se 1 (by rfl) ⟨1367807, by rfl⟩ : syracuseStep 1823743 = 2735615) B2735615
theorem B52590059 : Blo 1823613 52590059 := bstep (se 1 (by rfl) ⟨39442544, by rfl⟩ : syracuseStep 52590059 = 78885089) B78885089
theorem B20002529 : Blo 1823613 20002529 := bstep (se 2 (by rfl) ⟨7500948, by rfl⟩ : syracuseStep 20002529 = 15001897) B15001897
theorem B39983327 : Blo 1823613 39983327 := bstep (se 1 (by rfl) ⟨29987495, by rfl⟩ : syracuseStep 39983327 = 59974991) B59974991
theorem B11688731 : Blo 1823613 11688731 := bstep (se 1 (by rfl) ⟨8766548, by rfl⟩ : syracuseStep 11688731 = 17533097) B17533097
theorem B31186619 : Blo 1823613 31186619 := bstep (se 1 (by rfl) ⟨23389964, by rfl⟩ : syracuseStep 31186619 = 46779929) B46779929
theorem B7792487 : Blo 1823613 7792487 := bstep (se 1 (by rfl) ⟨5844365, by rfl⟩ : syracuseStep 7792487 = 11688731) B11688731
theorem B35060039 : Blo 1823613 35060039 := bstep (se 1 (by rfl) ⟨26295029, by rfl⟩ : syracuseStep 35060039 = 52590059) B52590059
theorem B13335019 : Blo 1823613 13335019 := bstep (se 1 (by rfl) ⟨10001264, by rfl⟩ : syracuseStep 13335019 = 20002529) B20002529
theorem B26655551 : Blo 1823613 26655551 := bstep (se 1 (by rfl) ⟨19991663, by rfl⟩ : syracuseStep 26655551 = 39983327) B39983327
theorem B20791079 : Blo 1823613 20791079 := bstep (se 1 (by rfl) ⟨15593309, by rfl⟩ : syracuseStep 20791079 = 31186619) B31186619
theorem B5194991 : Blo 1823613 5194991 := bstep (se 1 (by rfl) ⟨3896243, by rfl⟩ : syracuseStep 5194991 = 7792487) B7792487
theorem B23373359 : Blo 1823613 23373359 := bstep (se 1 (by rfl) ⟨17530019, by rfl⟩ : syracuseStep 23373359 = 35060039) B35060039
theorem B17770367 : Blo 1823613 17770367 := bstep (se 1 (by rfl) ⟨13327775, by rfl⟩ : syracuseStep 17770367 = 26655551) B26655551
theorem B71120101 : Blo 1823613 71120101 := bstep (se 4 (by rfl) ⟨6667509, by rfl⟩ : syracuseStep 71120101 = 13335019) B13335019
theorem B13860719 : Blo 1823613 13860719 := bstep (se 1 (by rfl) ⟨10395539, by rfl⟩ : syracuseStep 13860719 = 20791079) B20791079
theorem B15582239 : Blo 1823613 15582239 := bstep (se 1 (by rfl) ⟨11686679, by rfl⟩ : syracuseStep 15582239 = 23373359) B23373359
theorem B11846911 : Blo 1823613 11846911 := bstep (se 1 (by rfl) ⟨8885183, by rfl⟩ : syracuseStep 11846911 = 17770367) B17770367
theorem B94826801 : Blo 1823613 94826801 := bstep (se 2 (by rfl) ⟨35560050, by rfl⟩ : syracuseStep 94826801 = 71120101) B71120101
theorem B3463327 : Blo 1823613 3463327 := bstep (se 1 (by rfl) ⟨2597495, by rfl⟩ : syracuseStep 3463327 = 5194991) B5194991
theorem B9240479 : Blo 1823613 9240479 := bstep (se 1 (by rfl) ⟨6930359, by rfl⟩ : syracuseStep 9240479 = 13860719) B13860719
theorem B63217867 : Blo 1823613 63217867 := bstep (se 1 (by rfl) ⟨47413400, by rfl⟩ : syracuseStep 63217867 = 94826801) B94826801
theorem B10388159 : Blo 1823613 10388159 := bstep (se 1 (by rfl) ⟨7791119, by rfl⟩ : syracuseStep 10388159 = 15582239) B15582239
theorem B15795881 : Blo 1823613 15795881 := bstep (se 2 (by rfl) ⟨5923455, by rfl⟩ : syracuseStep 15795881 = 11846911) B11846911
theorem B4617769 : Blo 1823613 4617769 := bstep (se 2 (by rfl) ⟨1731663, by rfl⟩ : syracuseStep 4617769 = 3463327) B3463327
theorem B6160319 : Blo 1823613 6160319 := bstep (se 1 (by rfl) ⟨4620239, by rfl⟩ : syracuseStep 6160319 = 9240479) B9240479
theorem B4106879 : Blo 1823613 4106879 := bstep (se 1 (by rfl) ⟨3080159, by rfl⟩ : syracuseStep 4106879 = 6160319) B6160319
theorem B84290489 : Blo 1823613 84290489 := bstep (se 2 (by rfl) ⟨31608933, by rfl⟩ : syracuseStep 84290489 = 63217867) B63217867
theorem B6925439 : Blo 1823613 6925439 := bstep (se 1 (by rfl) ⟨5194079, by rfl⟩ : syracuseStep 6925439 = 10388159) B10388159
theorem B10530587 : Blo 1823613 10530587 := bstep (se 1 (by rfl) ⟨7897940, by rfl⟩ : syracuseStep 10530587 = 15795881) B15795881
theorem B6157025 : Blo 1823613 6157025 := bstep (se 2 (by rfl) ⟨2308884, by rfl⟩ : syracuseStep 6157025 = 4617769) B4617769
theorem B4104683 : Blo 1823613 4104683 := bstep (se 1 (by rfl) ⟨3078512, by rfl⟩ : syracuseStep 4104683 = 6157025) B6157025
theorem B2737919 : Blo 1823613 2737919 := bstep (se 1 (by rfl) ⟨2053439, by rfl⟩ : syracuseStep 2737919 = 4106879) B4106879
theorem B56193659 : Blo 1823613 56193659 := bstep (se 1 (by rfl) ⟨42145244, by rfl⟩ : syracuseStep 56193659 = 84290489) B84290489
theorem B4616959 : Blo 1823613 4616959 := bstep (se 1 (by rfl) ⟨3462719, by rfl⟩ : syracuseStep 4616959 = 6925439) B6925439
theorem B7020391 : Blo 1823613 7020391 := bstep (se 1 (by rfl) ⟨5265293, by rfl⟩ : syracuseStep 7020391 = 10530587) B10530587
theorem B2736455 : Blo 1823613 2736455 := bstep (se 1 (by rfl) ⟨2052341, by rfl⟩ : syracuseStep 2736455 = 4104683) B4104683
theorem B37462439 : Blo 1823613 37462439 := bstep (se 1 (by rfl) ⟨28096829, by rfl⟩ : syracuseStep 37462439 = 56193659) B56193659
theorem B6155945 : Blo 1823613 6155945 := bstep (se 2 (by rfl) ⟨2308479, by rfl⟩ : syracuseStep 6155945 = 4616959) B4616959
theorem B9360521 : Blo 1823613 9360521 := bstep (se 2 (by rfl) ⟨3510195, by rfl⟩ : syracuseStep 9360521 = 7020391) B7020391
theorem B1825279 : Blo 1823613 1825279 := bstep (se 1 (by rfl) ⟨1368959, by rfl⟩ : syracuseStep 1825279 = 2737919) B2737919
theorem B1824303 : Blo 1823613 1824303 := bstep (se 1 (by rfl) ⟨1368227, by rfl⟩ : syracuseStep 1824303 = 2736455) B2736455
theorem B6240347 : Blo 1823613 6240347 := bstep (se 1 (by rfl) ⟨4680260, by rfl⟩ : syracuseStep 6240347 = 9360521) B9360521
theorem B99899837 : Blo 1823613 99899837 := bstep (se 3 (by rfl) ⟨18731219, by rfl⟩ : syracuseStep 99899837 = 37462439) B37462439
theorem B4103963 : Blo 1823613 4103963 := bstep (se 1 (by rfl) ⟨3077972, by rfl⟩ : syracuseStep 4103963 = 6155945) B6155945
theorem B4160231 : Blo 1823613 4160231 := bstep (se 1 (by rfl) ⟨3120173, by rfl⟩ : syracuseStep 4160231 = 6240347) B6240347
theorem B66599891 : Blo 1823613 66599891 := bstep (se 1 (by rfl) ⟨49949918, by rfl⟩ : syracuseStep 66599891 = 99899837) B99899837
theorem B2735975 : Blo 1823613 2735975 := bstep (se 1 (by rfl) ⟨2051981, by rfl⟩ : syracuseStep 2735975 = 4103963) B4103963
theorem B2773487 : Blo 1823613 2773487 := bstep (se 1 (by rfl) ⟨2080115, by rfl⟩ : syracuseStep 2773487 = 4160231) B4160231
theorem B1823983 : Blo 1823613 1823983 := bstep (se 1 (by rfl) ⟨1367987, by rfl⟩ : syracuseStep 1823983 = 2735975) B2735975
theorem B44399927 : Blo 1823613 44399927 := bstep (se 1 (by rfl) ⟨33299945, by rfl⟩ : syracuseStep 44399927 = 66599891) B66599891
theorem B29599951 : Blo 1823613 29599951 := bstep (se 1 (by rfl) ⟨22199963, by rfl⟩ : syracuseStep 29599951 = 44399927) B44399927
theorem B7395965 : Blo 1823613 7395965 := bstep (se 3 (by rfl) ⟨1386743, by rfl⟩ : syracuseStep 7395965 = 2773487) B2773487
theorem B39466601 : Blo 1823613 39466601 := bstep (se 2 (by rfl) ⟨14799975, by rfl⟩ : syracuseStep 39466601 = 29599951) B29599951
theorem B4930643 : Blo 1823613 4930643 := bstep (se 1 (by rfl) ⟨3697982, by rfl⟩ : syracuseStep 4930643 = 7395965) B7395965
theorem B13148381 : Blo 1823613 13148381 := bstep (se 3 (by rfl) ⟨2465321, by rfl⟩ : syracuseStep 13148381 = 4930643) B4930643
theorem B26311067 : Blo 1823613 26311067 := bstep (se 1 (by rfl) ⟨19733300, by rfl⟩ : syracuseStep 26311067 = 39466601) B39466601
theorem B8765587 : Blo 1823613 8765587 := bstep (se 1 (by rfl) ⟨6574190, by rfl⟩ : syracuseStep 8765587 = 13148381) B13148381
theorem B17540711 : Blo 1823613 17540711 := bstep (se 1 (by rfl) ⟨13155533, by rfl⟩ : syracuseStep 17540711 = 26311067) B26311067
theorem B11693807 : Blo 1823613 11693807 := bstep (se 1 (by rfl) ⟨8770355, by rfl⟩ : syracuseStep 11693807 = 17540711) B17540711
theorem B11687449 : Blo 1823613 11687449 := bstep (se 2 (by rfl) ⟨4382793, by rfl⟩ : syracuseStep 11687449 = 8765587) B8765587
theorem B15583265 : Blo 1823613 15583265 := bstep (se 2 (by rfl) ⟨5843724, by rfl⟩ : syracuseStep 15583265 = 11687449) B11687449
theorem B7795871 : Blo 1823613 7795871 := bstep (se 1 (by rfl) ⟨5846903, by rfl⟩ : syracuseStep 7795871 = 11693807) B11693807
theorem B10388843 : Blo 1823613 10388843 := bstep (se 1 (by rfl) ⟨7791632, by rfl⟩ : syracuseStep 10388843 = 15583265) B15583265
theorem B5197247 : Blo 1823613 5197247 := bstep (se 1 (by rfl) ⟨3897935, by rfl⟩ : syracuseStep 5197247 = 7795871) B7795871
theorem B6925895 : Blo 1823613 6925895 := bstep (se 1 (by rfl) ⟨5194421, by rfl⟩ : syracuseStep 6925895 = 10388843) B10388843
theorem B3464831 : Blo 1823613 3464831 := bstep (se 1 (by rfl) ⟨2598623, by rfl⟩ : syracuseStep 3464831 = 5197247) B5197247
theorem B4617263 : Blo 1823613 4617263 := bstep (se 1 (by rfl) ⟨3462947, by rfl⟩ : syracuseStep 4617263 = 6925895) B6925895
theorem B2309887 : Blo 1823613 2309887 := bstep (se 1 (by rfl) ⟨1732415, by rfl⟩ : syracuseStep 2309887 = 3464831) B3464831
theorem B3078175 : Blo 1823613 3078175 := bstep (se 1 (by rfl) ⟨2308631, by rfl⟩ : syracuseStep 3078175 = 4617263) B4617263
theorem B3079849 : Blo 1823613 3079849 := bstep (se 2 (by rfl) ⟨1154943, by rfl⟩ : syracuseStep 3079849 = 2309887) B2309887
theorem B4104233 : Blo 1823613 4104233 := bstep (se 2 (by rfl) ⟨1539087, by rfl⟩ : syracuseStep 4104233 = 3078175) B3078175
theorem B4106465 : Blo 1823613 4106465 := bstep (se 2 (by rfl) ⟨1539924, by rfl⟩ : syracuseStep 4106465 = 3079849) B3079849
theorem B2736155 : Blo 1823613 2736155 := bstep (se 1 (by rfl) ⟨2052116, by rfl⟩ : syracuseStep 2736155 = 4104233) B4104233
theorem B2737643 : Blo 1823613 2737643 := bstep (se 1 (by rfl) ⟨2053232, by rfl⟩ : syracuseStep 2737643 = 4106465) B4106465
theorem B1824103 : Blo 1823613 1824103 := bstep (se 1 (by rfl) ⟨1368077, by rfl⟩ : syracuseStep 1824103 = 2736155) B2736155
theorem B1825095 : Blo 1823613 1825095 := bstep (se 1 (by rfl) ⟨1368821, by rfl⟩ : syracuseStep 1825095 = 2737643) B2737643

theorem C0 (j : ℕ) (h1 : 455903 ≤ j) (h2 : j ≤ 456402) : Blo 1823613 (4 * j + 3) := by
  interval_cases j
  · exact B1823615
  · exact B1823619
  · exact B1823623
  · exact B1823627
  · exact B1823631
  · exact B1823635
  · exact B1823639
  · exact B1823643
  · exact B1823647
  · exact B1823651
  · exact B1823655
  · exact B1823659
  · exact B1823663
  · exact B1823667
  · exact B1823671
  · exact B1823675
  · exact B1823679
  · exact B1823683
  · exact B1823687
  · exact B1823691
  · exact B1823695
  · exact B1823699
  · exact B1823703
  · exact B1823707
  · exact B1823711
  · exact B1823715
  · exact B1823719
  · exact B1823723
  · exact B1823727
  · exact B1823731
  · exact B1823735
  · exact B1823739
  · exact B1823743
  · exact B1823747
  · exact B1823751
  · exact B1823755
  · exact B1823759
  · exact B1823763
  · exact B1823767
  · exact B1823771
  · exact B1823775
  · exact B1823779
  · exact B1823783
  · exact B1823787
  · exact B1823791
  · exact B1823795
  · exact B1823799
  · exact B1823803
  · exact B1823807
  · exact B1823811
  · exact B1823815
  · exact B1823819
  · exact B1823823
  · exact B1823827
  · exact B1823831
  · exact B1823835
  · exact B1823839
  · exact B1823843
  · exact B1823847
  · exact B1823851
  · exact B1823855
  · exact B1823859
  · exact B1823863
  · exact B1823867
  · exact B1823871
  · exact B1823875
  · exact B1823879
  · exact B1823883
  · exact B1823887
  · exact B1823891
  · exact B1823895
  · exact B1823899
  · exact B1823903
  · exact B1823907
  · exact B1823911
  · exact B1823915
  · exact B1823919
  · exact B1823923
  · exact B1823927
  · exact B1823931
  · exact B1823935
  · exact B1823939
  · exact B1823943
  · exact B1823947
  · exact B1823951
  · exact B1823955
  · exact B1823959
  · exact B1823963
  · exact B1823967
  · exact B1823971
  · exact B1823975
  · exact B1823979
  · exact B1823983
  · exact B1823987
  · exact B1823991
  · exact B1823995
  · exact B1823999
  · exact B1824003
  · exact B1824007
  · exact B1824011
  · exact B1824015
  · exact B1824019
  · exact B1824023
  · exact B1824027
  · exact B1824031
  · exact B1824035
  · exact B1824039
  · exact B1824043
  · exact B1824047
  · exact B1824051
  · exact B1824055
  · exact B1824059
  · exact B1824063
  · exact B1824067
  · exact B1824071
  · exact B1824075
  · exact B1824079
  · exact B1824083
  · exact B1824087
  · exact B1824091
  · exact B1824095
  · exact B1824099
  · exact B1824103
  · exact B1824107
  · exact B1824111
  · exact B1824115
  · exact B1824119
  · exact B1824123
  · exact B1824127
  · exact B1824131
  · exact B1824135
  · exact B1824139
  · exact B1824143
  · exact B1824147
  · exact B1824151
  · exact B1824155
  · exact B1824159
  · exact B1824163
  · exact B1824167
  · exact B1824171
  · exact B1824175
  · exact B1824179
  · exact B1824183
  · exact B1824187
  · exact B1824191
  · exact B1824195
  · exact B1824199
  · exact B1824203
  · exact B1824207
  · exact B1824211
  · exact B1824215
  · exact B1824219
  · exact B1824223
  · exact B1824227
  · exact B1824231
  · exact B1824235
  · exact B1824239
  · exact B1824243
  · exact B1824247
  · exact B1824251
  · exact B1824255
  · exact B1824259
  · exact B1824263
  · exact B1824267
  · exact B1824271
  · exact B1824275
  · exact B1824279
  · exact B1824283
  · exact B1824287
  · exact B1824291
  · exact B1824295
  · exact B1824299
  · exact B1824303
  · exact B1824307
  · exact B1824311
  · exact B1824315
  · exact B1824319
  · exact B1824323
  · exact B1824327
  · exact B1824331
  · exact B1824335
  · exact B1824339
  · exact B1824343
  · exact B1824347
  · exact B1824351
  · exact B1824355
  · exact B1824359
  · exact B1824363
  · exact B1824367
  · exact B1824371
  · exact B1824375
  · exact B1824379
  · exact B1824383
  · exact B1824387
  · exact B1824391
  · exact B1824395
  · exact B1824399
  · exact B1824403
  · exact B1824407
  · exact B1824411
  · exact B1824415
  · exact B1824419
  · exact B1824423
  · exact B1824427
  · exact B1824431
  · exact B1824435
  · exact B1824439
  · exact B1824443
  · exact B1824447
  · exact B1824451
  · exact B1824455
  · exact B1824459
  · exact B1824463
  · exact B1824467
  · exact B1824471
  · exact B1824475
  · exact B1824479
  · exact B1824483
  · exact B1824487
  · exact B1824491
  · exact B1824495
  · exact B1824499
  · exact B1824503
  · exact B1824507
  · exact B1824511
  · exact B1824515
  · exact B1824519
  · exact B1824523
  · exact B1824527
  · exact B1824531
  · exact B1824535
  · exact B1824539
  · exact B1824543
  · exact B1824547
  · exact B1824551
  · exact B1824555
  · exact B1824559
  · exact B1824563
  · exact B1824567
  · exact B1824571
  · exact B1824575
  · exact B1824579
  · exact B1824583
  · exact B1824587
  · exact B1824591
  · exact B1824595
  · exact B1824599
  · exact B1824603
  · exact B1824607
  · exact B1824611
  · exact B1824615
  · exact B1824619
  · exact B1824623
  · exact B1824627
  · exact B1824631
  · exact B1824635
  · exact B1824639
  · exact B1824643
  · exact B1824647
  · exact B1824651
  · exact B1824655
  · exact B1824659
  · exact B1824663
  · exact B1824667
  · exact B1824671
  · exact B1824675
  · exact B1824679
  · exact B1824683
  · exact B1824687
  · exact B1824691
  · exact B1824695
  · exact B1824699
  · exact B1824703
  · exact B1824707
  · exact B1824711
  · exact B1824715
  · exact B1824719
  · exact B1824723
  · exact B1824727
  · exact B1824731
  · exact B1824735
  · exact B1824739
  · exact B1824743
  · exact B1824747
  · exact B1824751
  · exact B1824755
  · exact B1824759
  · exact B1824763
  · exact B1824767
  · exact B1824771
  · exact B1824775
  · exact B1824779
  · exact B1824783
  · exact B1824787
  · exact B1824791
  · exact B1824795
  · exact B1824799
  · exact B1824803
  · exact B1824807
  · exact B1824811
  · exact B1824815
  · exact B1824819
  · exact B1824823
  · exact B1824827
  · exact B1824831
  · exact B1824835
  · exact B1824839
  · exact B1824843
  · exact B1824847
  · exact B1824851
  · exact B1824855
  · exact B1824859
  · exact B1824863
  · exact B1824867
  · exact B1824871
  · exact B1824875
  · exact B1824879
  · exact B1824883
  · exact B1824887
  · exact B1824891
  · exact B1824895
  · exact B1824899
  · exact B1824903
  · exact B1824907
  · exact B1824911
  · exact B1824915
  · exact B1824919
  · exact B1824923
  · exact B1824927
  · exact B1824931
  · exact B1824935
  · exact B1824939
  · exact B1824943
  · exact B1824947
  · exact B1824951
  · exact B1824955
  · exact B1824959
  · exact B1824963
  · exact B1824967
  · exact B1824971
  · exact B1824975
  · exact B1824979
  · exact B1824983
  · exact B1824987
  · exact B1824991
  · exact B1824995
  · exact B1824999
  · exact B1825003
  · exact B1825007
  · exact B1825011
  · exact B1825015
  · exact B1825019
  · exact B1825023
  · exact B1825027
  · exact B1825031
  · exact B1825035
  · exact B1825039
  · exact B1825043
  · exact B1825047
  · exact B1825051
  · exact B1825055
  · exact B1825059
  · exact B1825063
  · exact B1825067
  · exact B1825071
  · exact B1825075
  · exact B1825079
  · exact B1825083
  · exact B1825087
  · exact B1825091
  · exact B1825095
  · exact B1825099
  · exact B1825103
  · exact B1825107
  · exact B1825111
  · exact B1825115
  · exact B1825119
  · exact B1825123
  · exact B1825127
  · exact B1825131
  · exact B1825135
  · exact B1825139
  · exact B1825143
  · exact B1825147
  · exact B1825151
  · exact B1825155
  · exact B1825159
  · exact B1825163
  · exact B1825167
  · exact B1825171
  · exact B1825175
  · exact B1825179
  · exact B1825183
  · exact B1825187
  · exact B1825191
  · exact B1825195
  · exact B1825199
  · exact B1825203
  · exact B1825207
  · exact B1825211
  · exact B1825215
  · exact B1825219
  · exact B1825223
  · exact B1825227
  · exact B1825231
  · exact B1825235
  · exact B1825239
  · exact B1825243
  · exact B1825247
  · exact B1825251
  · exact B1825255
  · exact B1825259
  · exact B1825263
  · exact B1825267
  · exact B1825271
  · exact B1825275
  · exact B1825279
  · exact B1825283
  · exact B1825287
  · exact B1825291
  · exact B1825295
  · exact B1825299
  · exact B1825303
  · exact B1825307
  · exact B1825311
  · exact B1825315
  · exact B1825319
  · exact B1825323
  · exact B1825327
  · exact B1825331
  · exact B1825335
  · exact B1825339
  · exact B1825343
  · exact B1825347
  · exact B1825351
  · exact B1825355
  · exact B1825359
  · exact B1825363
  · exact B1825367
  · exact B1825371
  · exact B1825375
  · exact B1825379
  · exact B1825383
  · exact B1825387
  · exact B1825391
  · exact B1825395
  · exact B1825399
  · exact B1825403
  · exact B1825407
  · exact B1825411
  · exact B1825415
  · exact B1825419
  · exact B1825423
  · exact B1825427
  · exact B1825431
  · exact B1825435
  · exact B1825439
  · exact B1825443
  · exact B1825447
  · exact B1825451
  · exact B1825455
  · exact B1825459
  · exact B1825463
  · exact B1825467
  · exact B1825471
  · exact B1825475
  · exact B1825479
  · exact B1825483
  · exact B1825487
  · exact B1825491
  · exact B1825495
  · exact B1825499
  · exact B1825503
  · exact B1825507
  · exact B1825511
  · exact B1825515
  · exact B1825519
  · exact B1825523
  · exact B1825527
  · exact B1825531
  · exact B1825535
  · exact B1825539
  · exact B1825543
  · exact B1825547
  · exact B1825551
  · exact B1825555
  · exact B1825559
  · exact B1825563
  · exact B1825567
  · exact B1825571
  · exact B1825575
  · exact B1825579
  · exact B1825583
  · exact B1825587
  · exact B1825591
  · exact B1825595
  · exact B1825599
  · exact B1825603
  · exact B1825607
  · exact B1825611

theorem solution (m : ℕ) (hlo : 1823613 ≤ m) (hhi : m ≤ 1825613) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 455903 ≤ j := by omega
    have hj2 : j ≤ 456402 := by omega
    have hb : Blo 1823613 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
