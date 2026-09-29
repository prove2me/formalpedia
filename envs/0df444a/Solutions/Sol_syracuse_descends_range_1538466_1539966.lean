-- Prove2me | solution 1 for syracuse_descends_range_1538466_1539966
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:05:00.924983+00:00
-- url     : https://prove2.me/submissions/f3a2051f-6e1e-49ac-970f-7176737543cc

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


theorem B1581089 : Blo 1538466 1581089 := bbase (se 2 (by rfl) ⟨592908, by rfl⟩ : syracuseStep 1581089 = 1185817) (by norm_num)
theorem B1581121 : Blo 1538466 1581121 := bbase (se 2 (by rfl) ⟨592920, by rfl⟩ : syracuseStep 1581121 = 1185841) (by norm_num)
theorem B2596981 : Blo 1538466 2596981 := bbase (se 5 (by rfl) ⟨121733, by rfl⟩ : syracuseStep 2596981 = 243467) (by norm_num)
theorem B7790741 : Blo 1538466 7790741 := bbase (se 6 (by rfl) ⟨182595, by rfl⟩ : syracuseStep 7790741 = 365191) (by norm_num)
theorem B2498725 : Blo 1538466 2498725 := bbase (se 4 (by rfl) ⟨234255, by rfl⟩ : syracuseStep 2498725 = 468511) (by norm_num)
theorem B4382885 : Blo 1538466 4382885 := bbase (se 4 (by rfl) ⟨410895, by rfl⟩ : syracuseStep 4382885 = 821791) (by norm_num)
theorem B2465957 : Blo 1538466 2465957 := bbase (se 4 (by rfl) ⟨231183, by rfl⟩ : syracuseStep 2465957 = 462367) (by norm_num)
theorem B2597069 : Blo 1538466 2597069 := bbase (se 3 (by rfl) ⟨486950, by rfl⟩ : syracuseStep 2597069 = 973901) (by norm_num)
theorem B5193989 : Blo 1538466 5193989 := bbase (se 4 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 5193989 = 973873) (by norm_num)
theorem B2597197 : Blo 1538466 2597197 := bbase (se 3 (by rfl) ⟨486974, by rfl⟩ : syracuseStep 2597197 = 973949) (by norm_num)
theorem B2597285 : Blo 1538466 2597285 := bbase (se 4 (by rfl) ⟨243495, by rfl⟩ : syracuseStep 2597285 = 486991) (by norm_num)
theorem B2597413 : Blo 1538466 2597413 := bbase (se 4 (by rfl) ⟨243507, by rfl⟩ : syracuseStep 2597413 = 487015) (by norm_num)
theorem B4932181 : Blo 1538466 4932181 := bbase (se 8 (by rfl) ⟨28899, by rfl⟩ : syracuseStep 4932181 = 57799) (by norm_num)
theorem B2597501 : Blo 1538466 2597501 := bbase (se 3 (by rfl) ⟨487031, by rfl⟩ : syracuseStep 2597501 = 974063) (by norm_num)
theorem B5194421 : Blo 1538466 5194421 := bbase (se 5 (by rfl) ⟨243488, by rfl⟩ : syracuseStep 5194421 = 486977) (by norm_num)
theorem B24011477 : Blo 1538466 24011477 := bbase (se 7 (by rfl) ⟨281384, by rfl⟩ : syracuseStep 24011477 = 562769) (by norm_num)
theorem B4997861 : Blo 1538466 4997861 := bbase (se 4 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 4997861 = 937099) (by norm_num)
theorem B2597629 : Blo 1538466 2597629 := bbase (se 3 (by rfl) ⟨487055, by rfl⟩ : syracuseStep 2597629 = 974111) (by norm_num)
theorem B2466629 : Blo 1538466 2466629 := bbase (se 4 (by rfl) ⟨231246, by rfl⟩ : syracuseStep 2466629 = 462493) (by norm_num)
theorem B2597717 : Blo 1538466 2597717 := bbase (se 9 (by rfl) ⟨7610, by rfl⟩ : syracuseStep 2597717 = 15221) (by norm_num)
theorem B3285917 : Blo 1538466 3285917 := bbase (se 3 (by rfl) ⟨616109, by rfl⟩ : syracuseStep 3285917 = 1232219) (by norm_num)
theorem B2499517 : Blo 1538466 2499517 := bbase (se 3 (by rfl) ⟨468659, by rfl⟩ : syracuseStep 2499517 = 937319) (by norm_num)
theorem B2597845 : Blo 1538466 2597845 := bbase (se 7 (by rfl) ⟨30443, by rfl⟩ : syracuseStep 2597845 = 60887) (by norm_num)
theorem B1975285 : Blo 1538466 1975285 := bbase (se 5 (by rfl) ⟨92591, by rfl⟩ : syracuseStep 1975285 = 185183) (by norm_num)
theorem B2597933 : Blo 1538466 2597933 := bbase (se 3 (by rfl) ⟨487112, by rfl⟩ : syracuseStep 2597933 = 974225) (by norm_num)
theorem B7398485 : Blo 1538466 7398485 := bbase (se 8 (by rfl) ⟨43350, by rfl⟩ : syracuseStep 7398485 = 86701) (by norm_num)
theorem B5194853 : Blo 1538466 5194853 := bbase (se 4 (by rfl) ⟨487017, by rfl⟩ : syracuseStep 5194853 = 974035) (by norm_num)
theorem B3286165 : Blo 1538466 3286165 := bbase (se 6 (by rfl) ⟨77019, by rfl⟩ : syracuseStep 3286165 = 154039) (by norm_num)
theorem B2598061 : Blo 1538466 2598061 := bbase (se 3 (by rfl) ⟨487136, by rfl⟩ : syracuseStep 2598061 = 974273) (by norm_num)
theorem B2598149 : Blo 1538466 2598149 := bbase (se 4 (by rfl) ⟨243576, by rfl⟩ : syracuseStep 2598149 = 487153) (by norm_num)
theorem B10020181 : Blo 1538466 10020181 := bbase (se 12 (by rfl) ⟨3669, by rfl⟩ : syracuseStep 10020181 = 7339) (by norm_num)
theorem B2598277 : Blo 1538466 2598277 := bbase (se 4 (by rfl) ⟨243588, by rfl⟩ : syracuseStep 2598277 = 487177) (by norm_num)
theorem B7792037 : Blo 1538466 7792037 := bbase (se 4 (by rfl) ⟨730503, by rfl⟩ : syracuseStep 7792037 = 1461007) (by norm_num)
theorem B3556829 : Blo 1538466 3556829 := bbase (se 3 (by rfl) ⟨666905, by rfl⟩ : syracuseStep 3556829 = 1333811) (by norm_num)
theorem B2598365 : Blo 1538466 2598365 := bbase (se 3 (by rfl) ⟨487193, by rfl⟩ : syracuseStep 2598365 = 974387) (by norm_num)
theorem B11240981 : Blo 1538466 11240981 := bbase (se 6 (by rfl) ⟨263460, by rfl⟩ : syracuseStep 11240981 = 526921) (by norm_num)
theorem B5195285 : Blo 1538466 5195285 := bbase (se 6 (by rfl) ⟨121764, by rfl⟩ : syracuseStep 5195285 = 243529) (by norm_num)
theorem B2598493 : Blo 1538466 2598493 := bbase (se 3 (by rfl) ⟨487217, by rfl⟩ : syracuseStep 2598493 = 974435) (by norm_num)
theorem B3286669 : Blo 1538466 3286669 := bbase (se 3 (by rfl) ⟨616250, by rfl⟩ : syracuseStep 3286669 = 1232501) (by norm_num)
theorem B11691701 : Blo 1538466 11691701 := bbase (se 5 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 11691701 = 1096097) (by norm_num)
theorem B2598581 : Blo 1538466 2598581 := bbase (se 5 (by rfl) ⟨121808, by rfl⟩ : syracuseStep 2598581 = 243617) (by norm_num)
theorem B4384469 : Blo 1538466 4384469 := bbase (se 7 (by rfl) ⟨51380, by rfl⟩ : syracuseStep 4384469 = 102761) (by norm_num)
theorem B4933349 : Blo 1538466 4933349 := bbase (se 4 (by rfl) ⟨462501, by rfl⟩ : syracuseStep 4933349 = 925003) (by norm_num)
theorem B5547781 : Blo 1538466 5547781 := bbase (se 4 (by rfl) ⟨520104, by rfl⟩ : syracuseStep 5547781 = 1040209) (by norm_num)
theorem B5547941 : Blo 1538466 5547941 := bbase (se 4 (by rfl) ⟨520119, by rfl⟩ : syracuseStep 5547941 = 1040239) (by norm_num)
theorem B5195717 : Blo 1538466 5195717 := bbase (se 4 (by rfl) ⟨487098, by rfl⟩ : syracuseStep 5195717 = 974197) (by norm_num)
theorem B11683925 : Blo 1538466 11683925 := bbase (se 8 (by rfl) ⟨68460, by rfl⟩ : syracuseStep 11683925 = 136921) (by norm_num)
theorem B3705005 : Blo 1538466 3705005 := bbase (se 3 (by rfl) ⟨694688, by rfl⟩ : syracuseStep 3705005 = 1389377) (by norm_num)
theorem B1730785 : Blo 1538466 1730785 := bbase (se 2 (by rfl) ⟨649044, by rfl⟩ : syracuseStep 1730785 = 1298089) (by norm_num)
theorem B1730821 : Blo 1538466 1730821 := bbase (se 4 (by rfl) ⟨162264, by rfl⟩ : syracuseStep 1730821 = 324529) (by norm_num)
theorem B5335301 : Blo 1538466 5335301 := bbase (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) (by norm_num)
theorem B1730857 : Blo 1538466 1730857 := bbase (se 2 (by rfl) ⟨649071, by rfl⟩ : syracuseStep 1730857 = 1298143) (by norm_num)
theorem B1755445 : Blo 1538466 1755445 := bbase (se 5 (by rfl) ⟨82286, by rfl⟩ : syracuseStep 1755445 = 164573) (by norm_num)
theorem B3696965 : Blo 1538466 3696965 := bbase (se 4 (by rfl) ⟨346590, by rfl⟩ : syracuseStep 3696965 = 693181) (by norm_num)
theorem B1730893 : Blo 1538466 1730893 := bbase (se 3 (by rfl) ⟨324542, by rfl⟩ : syracuseStep 1730893 = 649085) (by norm_num)
theorem B5843285 : Blo 1538466 5843285 := bbase (se 10 (by rfl) ⟨8559, by rfl⟩ : syracuseStep 5843285 = 17119) (by norm_num)
theorem B1730929 : Blo 1538466 1730929 := bbase (se 2 (by rfl) ⟨649098, by rfl⟩ : syracuseStep 1730929 = 1298197) (by norm_num)
theorem B5196149 : Blo 1538466 5196149 := bbase (se 5 (by rfl) ⟨243569, by rfl⟩ : syracuseStep 5196149 = 487139) (by norm_num)
theorem B4385141 : Blo 1538466 4385141 := bbase (se 5 (by rfl) ⟨205553, by rfl⟩ : syracuseStep 4385141 = 411107) (by norm_num)
theorem B3697021 : Blo 1538466 3697021 := bbase (se 3 (by rfl) ⟨693191, by rfl⟩ : syracuseStep 3697021 = 1386383) (by norm_num)
theorem B1730965 : Blo 1538466 1730965 := bbase (se 6 (by rfl) ⟨40569, by rfl⟩ : syracuseStep 1730965 = 81139) (by norm_num)
theorem B1731001 : Blo 1538466 1731001 := bbase (se 2 (by rfl) ⟨649125, by rfl⟩ : syracuseStep 1731001 = 1298251) (by norm_num)
theorem B1731037 : Blo 1538466 1731037 := bbase (se 3 (by rfl) ⟨324569, by rfl⟩ : syracuseStep 1731037 = 649139) (by norm_num)
theorem B2632181 : Blo 1538466 2632181 := bbase (se 5 (by rfl) ⟨123383, by rfl⟩ : syracuseStep 2632181 = 246767) (by norm_num)
theorem B1731073 : Blo 1538466 1731073 := bbase (se 2 (by rfl) ⟨649152, by rfl⟩ : syracuseStep 1731073 = 1298305) (by norm_num)
theorem B3287557 : Blo 1538466 3287557 := bbase (se 4 (by rfl) ⟨308208, by rfl⟩ : syracuseStep 3287557 = 616417) (by norm_num)
theorem B1731109 : Blo 1538466 1731109 := bbase (se 4 (by rfl) ⟨162291, by rfl⟩ : syracuseStep 1731109 = 324583) (by norm_num)
theorem B1731145 : Blo 1538466 1731145 := bbase (se 2 (by rfl) ⟨649179, by rfl⟩ : syracuseStep 1731145 = 1298359) (by norm_num)
theorem B1731181 : Blo 1538466 1731181 := bbase (se 3 (by rfl) ⟨324596, by rfl⟩ : syracuseStep 1731181 = 649193) (by norm_num)
theorem B5843573 : Blo 1538466 5843573 := bbase (se 5 (by rfl) ⟨273917, by rfl⟩ : syracuseStep 5843573 = 547835) (by norm_num)
theorem B1731217 : Blo 1538466 1731217 := bbase (se 2 (by rfl) ⟨649206, by rfl⟩ : syracuseStep 1731217 = 1298413) (by norm_num)
theorem B1731253 : Blo 1538466 1731253 := bbase (se 5 (by rfl) ⟨81152, by rfl⟩ : syracuseStep 1731253 = 162305) (by norm_num)
theorem B7793333 : Blo 1538466 7793333 := bbase (se 5 (by rfl) ⟨365312, by rfl⟩ : syracuseStep 7793333 = 730625) (by norm_num)
theorem B1731289 : Blo 1538466 1731289 := bbase (se 2 (by rfl) ⟨649233, by rfl⟩ : syracuseStep 1731289 = 1298467) (by norm_num)
theorem B1731325 : Blo 1538466 1731325 := bbase (se 3 (by rfl) ⟨324623, by rfl⟩ : syracuseStep 1731325 = 649247) (by norm_num)
theorem B1731361 : Blo 1538466 1731361 := bbase (se 2 (by rfl) ⟨649260, by rfl⟩ : syracuseStep 1731361 = 1298521) (by norm_num)
theorem B1755937 : Blo 1538466 1755937 := bbase (se 2 (by rfl) ⟨658476, by rfl⟩ : syracuseStep 1755937 = 1316953) (by norm_num)
theorem B5196581 : Blo 1538466 5196581 := bbase (se 4 (by rfl) ⟨487179, by rfl⟩ : syracuseStep 5196581 = 974359) (by norm_num)
theorem B1731397 : Blo 1538466 1731397 := bbase (se 4 (by rfl) ⟨162318, by rfl⟩ : syracuseStep 1731397 = 324637) (by norm_num)
theorem B1731433 : Blo 1538466 1731433 := bbase (se 2 (by rfl) ⟨649287, by rfl⟩ : syracuseStep 1731433 = 1298575) (by norm_num)
theorem B1731469 : Blo 1538466 1731469 := bbase (se 3 (by rfl) ⟨324650, by rfl⟩ : syracuseStep 1731469 = 649301) (by norm_num)
theorem B1731505 : Blo 1538466 1731505 := bbase (se 2 (by rfl) ⟨649314, by rfl⟩ : syracuseStep 1731505 = 1298629) (by norm_num)
theorem B1731541 : Blo 1538466 1731541 := bbase (se 7 (by rfl) ⟨20291, by rfl⟩ : syracuseStep 1731541 = 40583) (by norm_num)
theorem B3288053 : Blo 1538466 3288053 := bbase (se 5 (by rfl) ⟨154127, by rfl⟩ : syracuseStep 3288053 = 308255) (by norm_num)
theorem B1731577 : Blo 1538466 1731577 := bbase (se 2 (by rfl) ⟨649341, by rfl⟩ : syracuseStep 1731577 = 1298683) (by norm_num)
theorem B3894277 : Blo 1538466 3894277 := bbase (se 4 (by rfl) ⟨365088, by rfl⟩ : syracuseStep 3894277 = 730177) (by norm_num)
theorem B1731613 : Blo 1538466 1731613 := bbase (se 3 (by rfl) ⟨324677, by rfl⟩ : syracuseStep 1731613 = 649355) (by norm_num)
theorem B1731649 : Blo 1538466 1731649 := bbase (se 2 (by rfl) ⟨649368, by rfl⟩ : syracuseStep 1731649 = 1298737) (by norm_num)
theorem B3656789 : Blo 1538466 3656789 := bbase (se 8 (by rfl) ⟨21426, by rfl⟩ : syracuseStep 3656789 = 42853) (by norm_num)
theorem B1731685 : Blo 1538466 1731685 := bbase (se 4 (by rfl) ⟨162345, by rfl⟩ : syracuseStep 1731685 = 324691) (by norm_num)
theorem B3894389 : Blo 1538466 3894389 := bbase (se 5 (by rfl) ⟨182549, by rfl⟩ : syracuseStep 3894389 = 365099) (by norm_num)
theorem B1731721 : Blo 1538466 1731721 := bbase (se 2 (by rfl) ⟨649395, by rfl⟩ : syracuseStep 1731721 = 1298791) (by norm_num)
theorem B1731757 : Blo 1538466 1731757 := bbase (se 3 (by rfl) ⟨324704, by rfl⟩ : syracuseStep 1731757 = 649409) (by norm_num)
theorem B1731793 : Blo 1538466 1731793 := bbase (se 2 (by rfl) ⟨649422, by rfl⟩ : syracuseStep 1731793 = 1298845) (by norm_num)
theorem B5197013 : Blo 1538466 5197013 := bbase (se 7 (by rfl) ⟨60902, by rfl⟩ : syracuseStep 5197013 = 121805) (by norm_num)
theorem B1731829 : Blo 1538466 1731829 := bbase (se 5 (by rfl) ⟨81179, by rfl⟩ : syracuseStep 1731829 = 162359) (by norm_num)
theorem B1731865 : Blo 1538466 1731865 := bbase (se 2 (by rfl) ⟨649449, by rfl⟩ : syracuseStep 1731865 = 1298899) (by norm_num)
theorem B3894581 : Blo 1538466 3894581 := bbase (se 5 (by rfl) ⟨182558, by rfl⟩ : syracuseStep 3894581 = 365117) (by norm_num)
theorem B1731901 : Blo 1538466 1731901 := bbase (se 3 (by rfl) ⟨324731, by rfl⟩ : syracuseStep 1731901 = 649463) (by norm_num)
theorem B1731937 : Blo 1538466 1731937 := bbase (se 2 (by rfl) ⟨649476, by rfl⟩ : syracuseStep 1731937 = 1298953) (by norm_num)
theorem B3698021 : Blo 1538466 3698021 := bbase (se 4 (by rfl) ⟨346689, by rfl⟩ : syracuseStep 3698021 = 693379) (by norm_num)
theorem B1731973 : Blo 1538466 1731973 := bbase (se 4 (by rfl) ⟨162372, by rfl⟩ : syracuseStep 1731973 = 324745) (by norm_num)
theorem B1732009 : Blo 1538466 1732009 := bbase (se 2 (by rfl) ⟨649503, by rfl⟩ : syracuseStep 1732009 = 1299007) (by norm_num)
theorem B1732045 : Blo 1538466 1732045 := bbase (se 3 (by rfl) ⟨324758, by rfl⟩ : syracuseStep 1732045 = 649517) (by norm_num)
theorem B1732081 : Blo 1538466 1732081 := bbase (se 2 (by rfl) ⟨649530, by rfl⟩ : syracuseStep 1732081 = 1299061) (by norm_num)
theorem B1732117 : Blo 1538466 1732117 := bbase (se 6 (by rfl) ⟨40596, by rfl⟩ : syracuseStep 1732117 = 81193) (by norm_num)
theorem B3509813 : Blo 1538466 3509813 := bbase (se 5 (by rfl) ⟨164522, by rfl⟩ : syracuseStep 3509813 = 329045) (by norm_num)
theorem B1732153 : Blo 1538466 1732153 := bbase (se 2 (by rfl) ⟨649557, by rfl⟩ : syracuseStep 1732153 = 1299115) (by norm_num)
theorem B1732189 : Blo 1538466 1732189 := bbase (se 3 (by rfl) ⟨324785, by rfl⟩ : syracuseStep 1732189 = 649571) (by norm_num)
theorem B1732225 : Blo 1538466 1732225 := bbase (se 2 (by rfl) ⟨649584, by rfl⟩ : syracuseStep 1732225 = 1299169) (by norm_num)
theorem B3894925 : Blo 1538466 3894925 := bbase (se 3 (by rfl) ⟨730298, by rfl⟩ : syracuseStep 3894925 = 1460597) (by norm_num)
theorem B5410453 : Blo 1538466 5410453 := bbase (se 6 (by rfl) ⟨126807, by rfl⟩ : syracuseStep 5410453 = 253615) (by norm_num)
theorem B1732261 : Blo 1538466 1732261 := bbase (se 4 (by rfl) ⟨162399, by rfl⟩ : syracuseStep 1732261 = 324799) (by norm_num)
theorem B1560241 : Blo 1538466 1560241 := bbase (se 2 (by rfl) ⟨585090, by rfl⟩ : syracuseStep 1560241 = 1170181) (by norm_num)
theorem B8318645 : Blo 1538466 8318645 := bbase (se 5 (by rfl) ⟨389936, by rfl⟩ : syracuseStep 8318645 = 779873) (by norm_num)
theorem B1560265 : Blo 1538466 1560265 := bbase (se 2 (by rfl) ⟨585099, by rfl⟩ : syracuseStep 1560265 = 1170199) (by norm_num)
theorem B1732297 : Blo 1538466 1732297 := bbase (se 2 (by rfl) ⟨649611, by rfl⟩ : syracuseStep 1732297 = 1299223) (by norm_num)
theorem B1732333 : Blo 1538466 1732333 := bbase (se 3 (by rfl) ⟨324812, by rfl⟩ : syracuseStep 1732333 = 649625) (by norm_num)
theorem B3895037 : Blo 1538466 3895037 := bbase (se 3 (by rfl) ⟨730319, by rfl⟩ : syracuseStep 3895037 = 1460639) (by norm_num)
theorem B1732369 : Blo 1538466 1732369 := bbase (se 2 (by rfl) ⟨649638, by rfl⟩ : syracuseStep 1732369 = 1299277) (by norm_num)
theorem B5844757 : Blo 1538466 5844757 := bbase (se 6 (by rfl) ⟨136986, by rfl⟩ : syracuseStep 5844757 = 273973) (by norm_num)
theorem B2191141 : Blo 1538466 2191141 := bbase (se 4 (by rfl) ⟨205419, by rfl⟩ : syracuseStep 2191141 = 410839) (by norm_num)
theorem B1732405 : Blo 1538466 1732405 := bbase (se 5 (by rfl) ⟨81206, by rfl⟩ : syracuseStep 1732405 = 162413) (by norm_num)
theorem B1732441 : Blo 1538466 1732441 := bbase (se 2 (by rfl) ⟨649665, by rfl⟩ : syracuseStep 1732441 = 1299331) (by norm_num)
theorem B3288941 : Blo 1538466 3288941 := bbase (se 3 (by rfl) ⟨616676, by rfl⟩ : syracuseStep 3288941 = 1233353) (by norm_num)
theorem B3895229 : Blo 1538466 3895229 := bbase (se 3 (by rfl) ⟨730355, by rfl⟩ : syracuseStep 3895229 = 1460711) (by norm_num)
theorem B7794629 : Blo 1538466 7794629 := bbase (se 4 (by rfl) ⟨730746, by rfl⟩ : syracuseStep 7794629 = 1461493) (by norm_num)
theorem B1560589 : Blo 1538466 1560589 := bbase (se 3 (by rfl) ⟨292610, by rfl⟩ : syracuseStep 1560589 = 585221) (by norm_num)
theorem B5845061 : Blo 1538466 5845061 := bbase (se 4 (by rfl) ⟨547974, by rfl⟩ : syracuseStep 5845061 = 1095949) (by norm_num)
theorem B2191477 : Blo 1538466 2191477 := bbase (se 5 (by rfl) ⟨102725, by rfl⟩ : syracuseStep 2191477 = 205451) (by norm_num)
theorem B2920693 : Blo 1538466 2920693 := bbase (se 5 (by rfl) ⟨136907, by rfl⟩ : syracuseStep 2920693 = 273815) (by norm_num)
theorem B3895573 : Blo 1538466 3895573 := bbase (se 6 (by rfl) ⟨91302, by rfl⟩ : syracuseStep 3895573 = 182605) (by norm_num)
theorem B2191693 : Blo 1538466 2191693 := bbase (se 3 (by rfl) ⟨410942, by rfl⟩ : syracuseStep 2191693 = 821885) (by norm_num)
theorem B3895685 : Blo 1538466 3895685 := bbase (se 4 (by rfl) ⟨365220, by rfl⟩ : syracuseStep 3895685 = 730441) (by norm_num)
theorem B2920853 : Blo 1538466 2920853 := bbase (se 6 (by rfl) ⟨68457, by rfl⟩ : syracuseStep 2920853 = 136915) (by norm_num)
theorem B1642933 : Blo 1538466 1642933 := bbase (se 5 (by rfl) ⟨77012, by rfl⟩ : syracuseStep 1642933 = 154025) (by norm_num)
theorem B6574517 : Blo 1538466 6574517 := bbase (se 5 (by rfl) ⟨308180, by rfl⟩ : syracuseStep 6574517 = 616361) (by norm_num)
theorem B2773453 : Blo 1538466 2773453 := bbase (se 3 (by rfl) ⟨520022, by rfl⟩ : syracuseStep 2773453 = 1040045) (by norm_num)
theorem B3461597 : Blo 1538466 3461597 := bbase (se 3 (by rfl) ⟨649049, by rfl⟩ : syracuseStep 3461597 = 1298099) (by norm_num)
theorem B4682245 : Blo 1538466 4682245 := bbase (se 4 (by rfl) ⟨438960, by rfl⟩ : syracuseStep 4682245 = 877921) (by norm_num)
theorem B3461669 : Blo 1538466 3461669 := bbase (se 4 (by rfl) ⟨324531, by rfl⟩ : syracuseStep 3461669 = 649063) (by norm_num)
theorem B2920997 : Blo 1538466 2920997 := bbase (se 4 (by rfl) ⟨273843, by rfl⟩ : syracuseStep 2920997 = 547687) (by norm_num)
theorem B3895877 : Blo 1538466 3895877 := bbase (se 4 (by rfl) ⟨365238, by rfl⟩ : syracuseStep 3895877 = 730477) (by norm_num)
theorem B3461741 : Blo 1538466 3461741 := bbase (se 3 (by rfl) ⟨649076, by rfl⟩ : syracuseStep 3461741 = 1298153) (by norm_num)
theorem B3461813 : Blo 1538466 3461813 := bbase (se 5 (by rfl) ⟨162272, by rfl⟩ : syracuseStep 3461813 = 324545) (by norm_num)
theorem B2192069 : Blo 1538466 2192069 := bbase (se 4 (by rfl) ⟨205506, by rfl⟩ : syracuseStep 2192069 = 411013) (by norm_num)
theorem B7500533 : Blo 1538466 7500533 := bbase (se 5 (by rfl) ⟨351587, by rfl⟩ : syracuseStep 7500533 = 703175) (by norm_num)
theorem B3461885 : Blo 1538466 3461885 := bbase (se 3 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 3461885 = 1298207) (by norm_num)
theorem B3461957 : Blo 1538466 3461957 := bbase (se 4 (by rfl) ⟨324558, by rfl⟩ : syracuseStep 3461957 = 649117) (by norm_num)
theorem B2921285 : Blo 1538466 2921285 := bbase (se 4 (by rfl) ⟨273870, by rfl⟩ : syracuseStep 2921285 = 547741) (by norm_num)
theorem B1643377 : Blo 1538466 1643377 := bbase (se 2 (by rfl) ⟨616266, by rfl⟩ : syracuseStep 1643377 = 1232533) (by norm_num)
theorem B3462029 : Blo 1538466 3462029 := bbase (se 3 (by rfl) ⟨649130, by rfl⟩ : syracuseStep 3462029 = 1298261) (by norm_num)
theorem B3896221 : Blo 1538466 3896221 := bbase (se 3 (by rfl) ⟨730541, by rfl⟩ : syracuseStep 3896221 = 1461083) (by norm_num)
theorem B1643437 : Blo 1538466 1643437 := bbase (se 3 (by rfl) ⟨308144, by rfl⟩ : syracuseStep 1643437 = 616289) (by norm_num)
theorem B3462101 : Blo 1538466 3462101 := bbase (se 7 (by rfl) ⟨40571, by rfl⟩ : syracuseStep 3462101 = 81143) (by norm_num)
theorem B2921437 : Blo 1538466 2921437 := bbase (se 3 (by rfl) ⟨547769, by rfl⟩ : syracuseStep 2921437 = 1095539) (by norm_num)
theorem B3896333 : Blo 1538466 3896333 := bbase (se 3 (by rfl) ⟨730562, by rfl⟩ : syracuseStep 3896333 = 1461125) (by norm_num)
theorem B3462173 : Blo 1538466 3462173 := bbase (se 3 (by rfl) ⟨649157, by rfl⟩ : syracuseStep 3462173 = 1298315) (by norm_num)
theorem B3462245 : Blo 1538466 3462245 := bbase (se 4 (by rfl) ⟨324585, by rfl⟩ : syracuseStep 3462245 = 649171) (by norm_num)
theorem B12178549 : Blo 1538466 12178549 := bbase (se 5 (by rfl) ⟨570869, by rfl⟩ : syracuseStep 12178549 = 1141739) (by norm_num)
theorem B13145237 : Blo 1538466 13145237 := bbase (se 6 (by rfl) ⟨308091, by rfl⟩ : syracuseStep 13145237 = 616183) (by norm_num)
theorem B3749021 : Blo 1538466 3749021 := bbase (se 3 (by rfl) ⟨702941, by rfl⟩ : syracuseStep 3749021 = 1405883) (by norm_num)
theorem B3462317 : Blo 1538466 3462317 := bbase (se 3 (by rfl) ⟨649184, by rfl⟩ : syracuseStep 3462317 = 1298369) (by norm_num)
theorem B3896525 : Blo 1538466 3896525 := bbase (se 3 (by rfl) ⟨730598, by rfl⟩ : syracuseStep 3896525 = 1461197) (by norm_num)
theorem B7795925 : Blo 1538466 7795925 := bbase (se 7 (by rfl) ⟨91358, by rfl⟩ : syracuseStep 7795925 = 182717) (by norm_num)
theorem B1643753 : Blo 1538466 1643753 := bbase (se 2 (by rfl) ⟨616407, by rfl⟩ : syracuseStep 1643753 = 1232815) (by norm_num)
theorem B3462389 : Blo 1538466 3462389 := bbase (se 5 (by rfl) ⟨162299, by rfl⟩ : syracuseStep 3462389 = 324599) (by norm_num)
theorem B7501045 : Blo 1538466 7501045 := bbase (se 5 (by rfl) ⟨351611, by rfl⟩ : syracuseStep 7501045 = 703223) (by norm_num)
theorem B2921741 : Blo 1538466 2921741 := bbase (se 3 (by rfl) ⟨547826, by rfl⟩ : syracuseStep 2921741 = 1095653) (by norm_num)
theorem B7394581 : Blo 1538466 7394581 := bbase (se 6 (by rfl) ⟨173310, by rfl⟩ : syracuseStep 7394581 = 346621) (by norm_num)
theorem B3462461 : Blo 1538466 3462461 := bbase (se 3 (by rfl) ⟨649211, by rfl⟩ : syracuseStep 3462461 = 1298423) (by norm_num)
theorem B2667845 : Blo 1538466 2667845 := bbase (se 4 (by rfl) ⟨250110, by rfl⟩ : syracuseStep 2667845 = 500221) (by norm_num)
theorem B8762741 : Blo 1538466 8762741 := bbase (se 5 (by rfl) ⟨410753, by rfl⟩ : syracuseStep 8762741 = 821507) (by norm_num)
theorem B3462533 : Blo 1538466 3462533 := bbase (se 4 (by rfl) ⟨324612, by rfl⟩ : syracuseStep 3462533 = 649225) (by norm_num)
theorem B6575525 : Blo 1538466 6575525 := bbase (se 4 (by rfl) ⟨616455, by rfl⟩ : syracuseStep 6575525 = 1232911) (by norm_num)
theorem B3462605 : Blo 1538466 3462605 := bbase (se 3 (by rfl) ⟨649238, by rfl⟩ : syracuseStep 3462605 = 1298477) (by norm_num)
theorem B39998933 : Blo 1538466 39998933 := bbase (se 7 (by rfl) ⟨468737, by rfl⟩ : syracuseStep 39998933 = 937475) (by norm_num)
theorem B3462677 : Blo 1538466 3462677 := bbase (se 6 (by rfl) ⟨81156, by rfl⟩ : syracuseStep 3462677 = 162313) (by norm_num)
theorem B1947169 : Blo 1538466 1947169 := bbase (se 2 (by rfl) ⟨730188, by rfl⟩ : syracuseStep 1947169 = 1460377) (by norm_num)
theorem B3896869 : Blo 1538466 3896869 := bbase (se 4 (by rfl) ⟨365331, by rfl⟩ : syracuseStep 3896869 = 730663) (by norm_num)
theorem B3462749 : Blo 1538466 3462749 := bbase (se 3 (by rfl) ⟨649265, by rfl⟩ : syracuseStep 3462749 = 1298531) (by norm_num)
theorem B2307701 : Blo 1538466 2307701 := bbase (se 5 (by rfl) ⟨108173, by rfl⟩ : syracuseStep 2307701 = 216347) (by norm_num)
theorem B1848953 : Blo 1538466 1848953 := bbase (se 2 (by rfl) ⟨693357, by rfl⟩ : syracuseStep 1848953 = 1386715) (by norm_num)
theorem B2307725 : Blo 1538466 2307725 := bbase (se 3 (by rfl) ⟨432698, by rfl⟩ : syracuseStep 2307725 = 865397) (by norm_num)
theorem B2774669 : Blo 1538466 2774669 := bbase (se 3 (by rfl) ⟨520250, by rfl⟩ : syracuseStep 2774669 = 1040501) (by norm_num)
theorem B3896981 : Blo 1538466 3896981 := bbase (se 6 (by rfl) ⟨91335, by rfl⟩ : syracuseStep 3896981 = 182671) (by norm_num)
theorem B2307749 : Blo 1538466 2307749 := bbase (se 4 (by rfl) ⟨216351, by rfl⟩ : syracuseStep 2307749 = 432703) (by norm_num)
theorem B3462821 : Blo 1538466 3462821 := bbase (se 4 (by rfl) ⟨324639, by rfl⟩ : syracuseStep 3462821 = 649279) (by norm_num)
theorem B1644197 : Blo 1538466 1644197 := bbase (se 4 (by rfl) ⟨154143, by rfl⟩ : syracuseStep 1644197 = 308287) (by norm_num)
theorem B2307773 : Blo 1538466 2307773 := bbase (se 3 (by rfl) ⟨432707, by rfl⟩ : syracuseStep 2307773 = 865415) (by norm_num)
theorem B1947341 : Blo 1538466 1947341 := bbase (se 3 (by rfl) ⟨365126, by rfl⟩ : syracuseStep 1947341 = 730253) (by norm_num)
theorem B2307797 : Blo 1538466 2307797 := bbase (se 7 (by rfl) ⟨27044, by rfl⟩ : syracuseStep 2307797 = 54089) (by norm_num)
theorem B1644257 : Blo 1538466 1644257 := bbase (se 2 (by rfl) ⟨616596, by rfl⟩ : syracuseStep 1644257 = 1233193) (by norm_num)
theorem B2307821 : Blo 1538466 2307821 := bbase (se 3 (by rfl) ⟨432716, by rfl⟩ : syracuseStep 2307821 = 865433) (by norm_num)
theorem B3462893 : Blo 1538466 3462893 := bbase (se 3 (by rfl) ⟨649292, by rfl⟩ : syracuseStep 3462893 = 1298585) (by norm_num)
theorem B2307845 : Blo 1538466 2307845 := bbase (se 4 (by rfl) ⟨216360, by rfl⟩ : syracuseStep 2307845 = 432721) (by norm_num)
theorem B1947397 : Blo 1538466 1947397 := bbase (se 4 (by rfl) ⟨182568, by rfl⟩ : syracuseStep 1947397 = 365137) (by norm_num)
theorem B2307869 : Blo 1538466 2307869 := bbase (se 3 (by rfl) ⟨432725, by rfl⟩ : syracuseStep 2307869 = 865451) (by norm_num)
theorem B2307893 : Blo 1538466 2307893 := bbase (se 5 (by rfl) ⟨108182, by rfl⟩ : syracuseStep 2307893 = 216365) (by norm_num)
theorem B3462965 : Blo 1538466 3462965 := bbase (se 5 (by rfl) ⟨162326, by rfl⟩ : syracuseStep 3462965 = 324653) (by norm_num)
theorem B2774837 : Blo 1538466 2774837 := bbase (se 5 (by rfl) ⟨130070, by rfl⟩ : syracuseStep 2774837 = 260141) (by norm_num)
theorem B2307917 : Blo 1538466 2307917 := bbase (se 3 (by rfl) ⟨432734, by rfl⟩ : syracuseStep 2307917 = 865469) (by norm_num)
theorem B3897173 : Blo 1538466 3897173 := bbase (se 9 (by rfl) ⟨11417, by rfl⟩ : syracuseStep 3897173 = 22835) (by norm_num)
theorem B1644385 : Blo 1538466 1644385 := bbase (se 2 (by rfl) ⟨616644, by rfl⟩ : syracuseStep 1644385 = 1233289) (by norm_num)
theorem B2307941 : Blo 1538466 2307941 := bbase (se 4 (by rfl) ⟨216369, by rfl⟩ : syracuseStep 2307941 = 432739) (by norm_num)
theorem B1947493 : Blo 1538466 1947493 := bbase (se 4 (by rfl) ⟨182577, by rfl⟩ : syracuseStep 1947493 = 365155) (by norm_num)
theorem B2307965 : Blo 1538466 2307965 := bbase (se 3 (by rfl) ⟨432743, by rfl⟩ : syracuseStep 2307965 = 865487) (by norm_num)
theorem B3463037 : Blo 1538466 3463037 := bbase (se 3 (by rfl) ⟨649319, by rfl⟩ : syracuseStep 3463037 = 1298639) (by norm_num)
theorem B2307989 : Blo 1538466 2307989 := bbase (se 6 (by rfl) ⟨54093, by rfl⟩ : syracuseStep 2307989 = 108187) (by norm_num)
theorem B2308013 : Blo 1538466 2308013 := bbase (se 3 (by rfl) ⟨432752, by rfl⟩ : syracuseStep 2308013 = 865505) (by norm_num)
theorem B2308037 : Blo 1538466 2308037 := bbase (se 4 (by rfl) ⟨216378, by rfl⟩ : syracuseStep 2308037 = 432757) (by norm_num)
theorem B3463109 : Blo 1538466 3463109 := bbase (se 4 (by rfl) ⟨324666, by rfl⟩ : syracuseStep 3463109 = 649333) (by norm_num)
theorem B8320981 : Blo 1538466 8320981 := bbase (se 7 (by rfl) ⟨97511, by rfl⟩ : syracuseStep 8320981 = 195023) (by norm_num)
theorem B2308061 : Blo 1538466 2308061 := bbase (se 3 (by rfl) ⟨432761, by rfl⟩ : syracuseStep 2308061 = 865523) (by norm_num)
theorem B2308085 : Blo 1538466 2308085 := bbase (se 5 (by rfl) ⟨108191, by rfl⟩ : syracuseStep 2308085 = 216383) (by norm_num)
theorem B15800309 : Blo 1538466 15800309 := bbase (se 5 (by rfl) ⟨740639, by rfl⟩ : syracuseStep 15800309 = 1481279) (by norm_num)
theorem B2922493 : Blo 1538466 2922493 := bbase (se 3 (by rfl) ⟨547967, by rfl⟩ : syracuseStep 2922493 = 1095935) (by norm_num)
theorem B2308109 : Blo 1538466 2308109 := bbase (se 3 (by rfl) ⟨432770, by rfl⟩ : syracuseStep 2308109 = 865541) (by norm_num)
theorem B3463181 : Blo 1538466 3463181 := bbase (se 3 (by rfl) ⟨649346, by rfl⟩ : syracuseStep 3463181 = 1298693) (by norm_num)
theorem B1947665 : Blo 1538466 1947665 := bbase (se 2 (by rfl) ⟨730374, by rfl⟩ : syracuseStep 1947665 = 1460749) (by norm_num)
theorem B2308133 : Blo 1538466 2308133 := bbase (se 4 (by rfl) ⟨216387, by rfl⟩ : syracuseStep 2308133 = 432775) (by norm_num)
theorem B2308157 : Blo 1538466 2308157 := bbase (se 3 (by rfl) ⟨432779, by rfl⟩ : syracuseStep 2308157 = 865559) (by norm_num)
theorem B1947721 : Blo 1538466 1947721 := bbase (se 2 (by rfl) ⟨730395, by rfl⟩ : syracuseStep 1947721 = 1460791) (by norm_num)
theorem B2308181 : Blo 1538466 2308181 := bbase (se 8 (by rfl) ⟨13524, by rfl⟩ : syracuseStep 2308181 = 27049) (by norm_num)
theorem B96073813 : Blo 1538466 96073813 := bbase (se 8 (by rfl) ⟨562932, by rfl⟩ : syracuseStep 96073813 = 1125865) (by norm_num)
theorem B3463253 : Blo 1538466 3463253 := bbase (se 8 (by rfl) ⟨20292, by rfl⟩ : syracuseStep 3463253 = 40585) (by norm_num)
theorem B2308205 : Blo 1538466 2308205 := bbase (se 3 (by rfl) ⟨432788, by rfl⟩ : syracuseStep 2308205 = 865577) (by norm_num)
theorem B2308229 : Blo 1538466 2308229 := bbase (se 4 (by rfl) ⟨216396, by rfl⟩ : syracuseStep 2308229 = 432793) (by norm_num)
theorem B2922637 : Blo 1538466 2922637 := bbase (se 3 (by rfl) ⟨547994, by rfl⟩ : syracuseStep 2922637 = 1095989) (by norm_num)
theorem B2308253 : Blo 1538466 2308253 := bbase (se 3 (by rfl) ⟨432797, by rfl⟩ : syracuseStep 2308253 = 865595) (by norm_num)
theorem B3463325 : Blo 1538466 3463325 := bbase (se 3 (by rfl) ⟨649373, by rfl⟩ : syracuseStep 3463325 = 1298747) (by norm_num)
theorem B1947817 : Blo 1538466 1947817 := bbase (se 2 (by rfl) ⟨730431, by rfl⟩ : syracuseStep 1947817 = 1460863) (by norm_num)
theorem B3897517 : Blo 1538466 3897517 := bbase (se 3 (by rfl) ⟨730784, by rfl⟩ : syracuseStep 3897517 = 1461569) (by norm_num)
theorem B2308277 : Blo 1538466 2308277 := bbase (se 5 (by rfl) ⟨108200, by rfl⟩ : syracuseStep 2308277 = 216401) (by norm_num)
theorem B4159669 : Blo 1538466 4159669 := bbase (se 5 (by rfl) ⟨194984, by rfl⟩ : syracuseStep 4159669 = 389969) (by norm_num)
theorem B2308301 : Blo 1538466 2308301 := bbase (se 3 (by rfl) ⟨432806, by rfl⟩ : syracuseStep 2308301 = 865613) (by norm_num)
theorem B1849549 : Blo 1538466 1849549 := bbase (se 3 (by rfl) ⟨346790, by rfl⟩ : syracuseStep 1849549 = 693581) (by norm_num)
theorem B2308325 : Blo 1538466 2308325 := bbase (se 4 (by rfl) ⟨216405, by rfl⟩ : syracuseStep 2308325 = 432811) (by norm_num)
theorem B3463397 : Blo 1538466 3463397 := bbase (se 4 (by rfl) ⟨324693, by rfl⟩ : syracuseStep 3463397 = 649387) (by norm_num)
theorem B9861365 : Blo 1538466 9861365 := bbase (se 5 (by rfl) ⟨462251, by rfl⟩ : syracuseStep 9861365 = 924503) (by norm_num)
theorem B2308349 : Blo 1538466 2308349 := bbase (se 3 (by rfl) ⟨432815, by rfl⟩ : syracuseStep 2308349 = 865631) (by norm_num)
theorem B2308373 : Blo 1538466 2308373 := bbase (se 6 (by rfl) ⟨54102, by rfl⟩ : syracuseStep 2308373 = 108205) (by norm_num)
theorem B3897629 : Blo 1538466 3897629 := bbase (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) (by norm_num)
theorem B2308397 : Blo 1538466 2308397 := bbase (se 3 (by rfl) ⟨432824, by rfl⟩ : syracuseStep 2308397 = 865649) (by norm_num)
theorem B3463469 : Blo 1538466 3463469 := bbase (se 3 (by rfl) ⟨649400, by rfl⟩ : syracuseStep 3463469 = 1298801) (by norm_num)
theorem B2922797 : Blo 1538466 2922797 := bbase (se 3 (by rfl) ⟨548024, by rfl⟩ : syracuseStep 2922797 = 1096049) (by norm_num)
theorem B1849645 : Blo 1538466 1849645 := bbase (se 3 (by rfl) ⟨346808, by rfl⟩ : syracuseStep 1849645 = 693617) (by norm_num)
theorem B2308421 : Blo 1538466 2308421 := bbase (se 4 (by rfl) ⟨216414, by rfl⟩ : syracuseStep 2308421 = 432829) (by norm_num)
theorem B1947989 : Blo 1538466 1947989 := bbase (se 10 (by rfl) ⟨2853, by rfl⟩ : syracuseStep 1947989 = 5707) (by norm_num)
theorem B2308445 : Blo 1538466 2308445 := bbase (se 3 (by rfl) ⟨432833, by rfl⟩ : syracuseStep 2308445 = 865667) (by norm_num)
theorem B2308469 : Blo 1538466 2308469 := bbase (se 5 (by rfl) ⟨108209, by rfl⟩ : syracuseStep 2308469 = 216419) (by norm_num)
theorem B3463541 : Blo 1538466 3463541 := bbase (se 5 (by rfl) ⟨162353, by rfl⟩ : syracuseStep 3463541 = 324707) (by norm_num)
theorem B2308493 : Blo 1538466 2308493 := bbase (se 3 (by rfl) ⟨432842, by rfl⟩ : syracuseStep 2308493 = 865685) (by norm_num)
theorem B1948045 : Blo 1538466 1948045 := bbase (se 3 (by rfl) ⟨365258, by rfl⟩ : syracuseStep 1948045 = 730517) (by norm_num)
theorem B2308517 : Blo 1538466 2308517 := bbase (se 4 (by rfl) ⟨216423, by rfl⟩ : syracuseStep 2308517 = 432847) (by norm_num)
theorem B7018933 : Blo 1538466 7018933 := bbase (se 5 (by rfl) ⟨329012, by rfl⟩ : syracuseStep 7018933 = 658025) (by norm_num)
theorem B2308541 : Blo 1538466 2308541 := bbase (se 3 (by rfl) ⟨432851, by rfl⟩ : syracuseStep 2308541 = 865703) (by norm_num)
theorem B3463613 : Blo 1538466 3463613 := bbase (se 3 (by rfl) ⟨649427, by rfl⟩ : syracuseStep 3463613 = 1298855) (by norm_num)
theorem B2922941 : Blo 1538466 2922941 := bbase (se 3 (by rfl) ⟨548051, by rfl⟩ : syracuseStep 2922941 = 1096103) (by norm_num)
theorem B2308565 : Blo 1538466 2308565 := bbase (se 7 (by rfl) ⟨27053, by rfl⟩ : syracuseStep 2308565 = 54107) (by norm_num)
theorem B3897821 : Blo 1538466 3897821 := bbase (se 3 (by rfl) ⟨730841, by rfl⟩ : syracuseStep 3897821 = 1461683) (by norm_num)
theorem B2308589 : Blo 1538466 2308589 := bbase (se 3 (by rfl) ⟨432860, by rfl⟩ : syracuseStep 2308589 = 865721) (by norm_num)
theorem B1948141 : Blo 1538466 1948141 := bbase (se 3 (by rfl) ⟨365276, by rfl⟩ : syracuseStep 1948141 = 730553) (by norm_num)
theorem B2308613 : Blo 1538466 2308613 := bbase (se 4 (by rfl) ⟨216432, by rfl⟩ : syracuseStep 2308613 = 432865) (by norm_num)
theorem B3463685 : Blo 1538466 3463685 := bbase (se 4 (by rfl) ⟨324720, by rfl⟩ : syracuseStep 3463685 = 649441) (by norm_num)
theorem B2308637 : Blo 1538466 2308637 := bbase (se 3 (by rfl) ⟨432869, by rfl⟩ : syracuseStep 2308637 = 865739) (by norm_num)
theorem B2308661 : Blo 1538466 2308661 := bbase (se 5 (by rfl) ⟨108218, by rfl⟩ : syracuseStep 2308661 = 216437) (by norm_num)
theorem B2308685 : Blo 1538466 2308685 := bbase (se 3 (by rfl) ⟨432878, by rfl⟩ : syracuseStep 2308685 = 865757) (by norm_num)
theorem B3463757 : Blo 1538466 3463757 := bbase (se 3 (by rfl) ⟨649454, by rfl⟩ : syracuseStep 3463757 = 1298909) (by norm_num)
theorem B2308709 : Blo 1538466 2308709 := bbase (se 4 (by rfl) ⟨216441, by rfl⟩ : syracuseStep 2308709 = 432883) (by norm_num)
theorem B2308733 : Blo 1538466 2308733 := bbase (se 3 (by rfl) ⟨432887, by rfl⟩ : syracuseStep 2308733 = 865775) (by norm_num)
theorem B2308757 : Blo 1538466 2308757 := bbase (se 6 (by rfl) ⟨54111, by rfl⟩ : syracuseStep 2308757 = 108223) (by norm_num)
theorem B3463829 : Blo 1538466 3463829 := bbase (se 6 (by rfl) ⟨81183, by rfl⟩ : syracuseStep 3463829 = 162367) (by norm_num)
theorem B1948313 : Blo 1538466 1948313 := bbase (se 2 (by rfl) ⟨730617, by rfl⟩ : syracuseStep 1948313 = 1461235) (by norm_num)
theorem B2308781 : Blo 1538466 2308781 := bbase (se 3 (by rfl) ⟨432896, by rfl⟩ : syracuseStep 2308781 = 865793) (by norm_num)
theorem B4381381 : Blo 1538466 4381381 := bbase (se 4 (by rfl) ⟨410754, by rfl⟩ : syracuseStep 4381381 = 821509) (by norm_num)
theorem B2308805 : Blo 1538466 2308805 := bbase (se 4 (by rfl) ⟨216450, by rfl⟩ : syracuseStep 2308805 = 432901) (by norm_num)
theorem B1948369 : Blo 1538466 1948369 := bbase (se 2 (by rfl) ⟨730638, by rfl⟩ : syracuseStep 1948369 = 1461277) (by norm_num)
theorem B2308829 : Blo 1538466 2308829 := bbase (se 3 (by rfl) ⟨432905, by rfl⟩ : syracuseStep 2308829 = 865811) (by norm_num)
theorem B3463901 : Blo 1538466 3463901 := bbase (se 3 (by rfl) ⟨649481, by rfl⟩ : syracuseStep 3463901 = 1298963) (by norm_num)
theorem B2923229 : Blo 1538466 2923229 := bbase (se 3 (by rfl) ⟨548105, by rfl⟩ : syracuseStep 2923229 = 1096211) (by norm_num)
theorem B2308853 : Blo 1538466 2308853 := bbase (se 5 (by rfl) ⟨108227, by rfl⟩ : syracuseStep 2308853 = 216455) (by norm_num)
theorem B2308877 : Blo 1538466 2308877 := bbase (se 3 (by rfl) ⟨432914, by rfl⟩ : syracuseStep 2308877 = 865829) (by norm_num)
theorem B2308901 : Blo 1538466 2308901 := bbase (se 4 (by rfl) ⟨216459, by rfl⟩ : syracuseStep 2308901 = 432919) (by norm_num)
theorem B3463973 : Blo 1538466 3463973 := bbase (se 4 (by rfl) ⟨324747, by rfl⟩ : syracuseStep 3463973 = 649495) (by norm_num)
theorem B1948465 : Blo 1538466 1948465 := bbase (se 2 (by rfl) ⟨730674, by rfl⟩ : syracuseStep 1948465 = 1461349) (by norm_num)
theorem B2308925 : Blo 1538466 2308925 := bbase (se 3 (by rfl) ⟨432923, by rfl⟩ : syracuseStep 2308925 = 865847) (by norm_num)
theorem B2308949 : Blo 1538466 2308949 := bbase (se 9 (by rfl) ⟨6764, by rfl⟩ : syracuseStep 2308949 = 13529) (by norm_num)
theorem B67484501 : Blo 1538466 67484501 := bbase (se 9 (by rfl) ⟨197708, by rfl⟩ : syracuseStep 67484501 = 395417) (by norm_num)
theorem B2308973 : Blo 1538466 2308973 := bbase (se 3 (by rfl) ⟨432932, by rfl⟩ : syracuseStep 2308973 = 865865) (by norm_num)
theorem B3464045 : Blo 1538466 3464045 := bbase (se 3 (by rfl) ⟨649508, by rfl⟩ : syracuseStep 3464045 = 1299017) (by norm_num)
theorem B2923381 : Blo 1538466 2923381 := bbase (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) (by norm_num)
theorem B2079613 : Blo 1538466 2079613 := bbase (se 3 (by rfl) ⟨389927, by rfl⟩ : syracuseStep 2079613 = 779855) (by norm_num)
theorem B7789445 : Blo 1538466 7789445 := bbase (se 4 (by rfl) ⟨730260, by rfl⟩ : syracuseStep 7789445 = 1460521) (by norm_num)
theorem B2308997 : Blo 1538466 2308997 := bbase (se 4 (by rfl) ⟨216468, by rfl⟩ : syracuseStep 2308997 = 432937) (by norm_num)
theorem B2309021 : Blo 1538466 2309021 := bbase (se 3 (by rfl) ⟨432941, by rfl⟩ : syracuseStep 2309021 = 865883) (by norm_num)
theorem B2309045 : Blo 1538466 2309045 := bbase (se 5 (by rfl) ⟨108236, by rfl⟩ : syracuseStep 2309045 = 216473) (by norm_num)
theorem B3464117 : Blo 1538466 3464117 := bbase (se 5 (by rfl) ⟨162380, by rfl⟩ : syracuseStep 3464117 = 324761) (by norm_num)
theorem B2309069 : Blo 1538466 2309069 := bbase (se 3 (by rfl) ⟨432950, by rfl⟩ : syracuseStep 2309069 = 865901) (by norm_num)
theorem B1948637 : Blo 1538466 1948637 := bbase (se 3 (by rfl) ⟨365369, by rfl⟩ : syracuseStep 1948637 = 730739) (by norm_num)
theorem B2309093 : Blo 1538466 2309093 := bbase (se 4 (by rfl) ⟨216477, by rfl⟩ : syracuseStep 2309093 = 432955) (by norm_num)
theorem B5192693 : Blo 1538466 5192693 := bbase (se 5 (by rfl) ⟨243407, by rfl⟩ : syracuseStep 5192693 = 486815) (by norm_num)
theorem B14040053 : Blo 1538466 14040053 := bbase (se 5 (by rfl) ⟨658127, by rfl⟩ : syracuseStep 14040053 = 1316255) (by norm_num)
theorem B2309117 : Blo 1538466 2309117 := bbase (se 3 (by rfl) ⟨432959, by rfl⟩ : syracuseStep 2309117 = 865919) (by norm_num)
theorem B3464189 : Blo 1538466 3464189 := bbase (se 3 (by rfl) ⟨649535, by rfl⟩ : syracuseStep 3464189 = 1299071) (by norm_num)
theorem B4160533 : Blo 1538466 4160533 := bbase (se 6 (by rfl) ⟨97512, by rfl⟩ : syracuseStep 4160533 = 195025) (by norm_num)
theorem B2309141 : Blo 1538466 2309141 := bbase (se 6 (by rfl) ⟨54120, by rfl⟩ : syracuseStep 2309141 = 108241) (by norm_num)
theorem B1948693 : Blo 1538466 1948693 := bbase (se 6 (by rfl) ⟨45672, by rfl⟩ : syracuseStep 1948693 = 91345) (by norm_num)
theorem B2309165 : Blo 1538466 2309165 := bbase (se 3 (by rfl) ⟨432968, by rfl⟩ : syracuseStep 2309165 = 865937) (by norm_num)
theorem B2309189 : Blo 1538466 2309189 := bbase (se 4 (by rfl) ⟨216486, by rfl⟩ : syracuseStep 2309189 = 432973) (by norm_num)
theorem B3464261 : Blo 1538466 3464261 := bbase (se 4 (by rfl) ⟨324774, by rfl⟩ : syracuseStep 3464261 = 649549) (by norm_num)
theorem B2309213 : Blo 1538466 2309213 := bbase (se 3 (by rfl) ⟨432977, by rfl⟩ : syracuseStep 2309213 = 865955) (by norm_num)
theorem B2309237 : Blo 1538466 2309237 := bbase (se 5 (by rfl) ⟨108245, by rfl⟩ : syracuseStep 2309237 = 216491) (by norm_num)
theorem B1948789 : Blo 1538466 1948789 := bbase (se 5 (by rfl) ⟨91349, by rfl⟩ : syracuseStep 1948789 = 182699) (by norm_num)
theorem B2309261 : Blo 1538466 2309261 := bbase (se 3 (by rfl) ⟨432986, by rfl⟩ : syracuseStep 2309261 = 865973) (by norm_num)
theorem B3464333 : Blo 1538466 3464333 := bbase (se 3 (by rfl) ⟨649562, by rfl⟩ : syracuseStep 3464333 = 1299125) (by norm_num)
theorem B6577301 : Blo 1538466 6577301 := bbase (se 6 (by rfl) ⟨154155, by rfl⟩ : syracuseStep 6577301 = 308311) (by norm_num)
theorem B2309285 : Blo 1538466 2309285 := bbase (se 4 (by rfl) ⟨216495, by rfl⟩ : syracuseStep 2309285 = 432991) (by norm_num)
theorem B2309309 : Blo 1538466 2309309 := bbase (se 3 (by rfl) ⟨432995, by rfl⟩ : syracuseStep 2309309 = 865991) (by norm_num)
theorem B2309333 : Blo 1538466 2309333 := bbase (se 7 (by rfl) ⟨27062, by rfl⟩ : syracuseStep 2309333 = 54125) (by norm_num)
theorem B3464405 : Blo 1538466 3464405 := bbase (se 7 (by rfl) ⟨40598, by rfl⟩ : syracuseStep 3464405 = 81197) (by norm_num)
theorem B3947741 : Blo 1538466 3947741 := bbase (se 3 (by rfl) ⟨740201, by rfl⟩ : syracuseStep 3947741 = 1480403) (by norm_num)
theorem B2309357 : Blo 1538466 2309357 := bbase (se 3 (by rfl) ⟨433004, by rfl⟩ : syracuseStep 2309357 = 866009) (by norm_num)
theorem B2309381 : Blo 1538466 2309381 := bbase (se 4 (by rfl) ⟨216504, by rfl⟩ : syracuseStep 2309381 = 433009) (by norm_num)
theorem B2309405 : Blo 1538466 2309405 := bbase (se 3 (by rfl) ⟨433013, by rfl⟩ : syracuseStep 2309405 = 866027) (by norm_num)
theorem B3464477 : Blo 1538466 3464477 := bbase (se 3 (by rfl) ⟨649589, by rfl⟩ : syracuseStep 3464477 = 1299179) (by norm_num)
theorem B1948961 : Blo 1538466 1948961 := bbase (se 2 (by rfl) ⟨730860, by rfl⟩ : syracuseStep 1948961 = 1461721) (by norm_num)
theorem B2309429 : Blo 1538466 2309429 := bbase (se 5 (by rfl) ⟨108254, by rfl⟩ : syracuseStep 2309429 = 216509) (by norm_num)
theorem B2309453 : Blo 1538466 2309453 := bbase (se 3 (by rfl) ⟨433022, by rfl⟩ : syracuseStep 2309453 = 866045) (by norm_num)
theorem B3333469 : Blo 1538466 3333469 := bbase (se 3 (by rfl) ⟨625025, by rfl⟩ : syracuseStep 3333469 = 1250051) (by norm_num)
theorem B1949017 : Blo 1538466 1949017 := bbase (se 2 (by rfl) ⟨730881, by rfl⟩ : syracuseStep 1949017 = 1461763) (by norm_num)
theorem B2309477 : Blo 1538466 2309477 := bbase (se 4 (by rfl) ⟨216513, by rfl⟩ : syracuseStep 2309477 = 433027) (by norm_num)
theorem B3464549 : Blo 1538466 3464549 := bbase (se 4 (by rfl) ⟨324801, by rfl⟩ : syracuseStep 3464549 = 649603) (by norm_num)
theorem B2596205 : Blo 1538466 2596205 := bbase (se 3 (by rfl) ⟨486788, by rfl⟩ : syracuseStep 2596205 = 973577) (by norm_num)
theorem B2309501 : Blo 1538466 2309501 := bbase (se 3 (by rfl) ⟨433031, by rfl⟩ : syracuseStep 2309501 = 866063) (by norm_num)
theorem B2309525 : Blo 1538466 2309525 := bbase (se 6 (by rfl) ⟨54129, by rfl⟩ : syracuseStep 2309525 = 108259) (by norm_num)
theorem B5193125 : Blo 1538466 5193125 := bbase (se 4 (by rfl) ⟨486855, by rfl⟩ : syracuseStep 5193125 = 973711) (by norm_num)
theorem B2309549 : Blo 1538466 2309549 := bbase (se 3 (by rfl) ⟨433040, by rfl⟩ : syracuseStep 2309549 = 866081) (by norm_num)
theorem B3464621 : Blo 1538466 3464621 := bbase (se 3 (by rfl) ⟨649616, by rfl⟩ : syracuseStep 3464621 = 1299233) (by norm_num)
theorem B2080181 : Blo 1538466 2080181 := bbase (se 5 (by rfl) ⟨97508, by rfl⟩ : syracuseStep 2080181 = 195017) (by norm_num)
theorem B2309573 : Blo 1538466 2309573 := bbase (se 4 (by rfl) ⟨216522, by rfl⟩ : syracuseStep 2309573 = 433045) (by norm_num)
theorem B2465245 : Blo 1538466 2465245 := bbase (se 3 (by rfl) ⟨462233, by rfl⟩ : syracuseStep 2465245 = 924467) (by norm_num)
theorem B2309597 : Blo 1538466 2309597 := bbase (se 3 (by rfl) ⟨433049, by rfl⟩ : syracuseStep 2309597 = 866099) (by norm_num)
theorem B2596333 : Blo 1538466 2596333 := bbase (se 3 (by rfl) ⟨486812, by rfl⟩ : syracuseStep 2596333 = 973625) (by norm_num)
theorem B2309621 : Blo 1538466 2309621 := bbase (se 5 (by rfl) ⟨108263, by rfl⟩ : syracuseStep 2309621 = 216527) (by norm_num)
theorem B3464693 : Blo 1538466 3464693 := bbase (se 5 (by rfl) ⟨162407, by rfl⟩ : syracuseStep 3464693 = 324815) (by norm_num)
theorem B3120653 : Blo 1538466 3120653 := bbase (se 3 (by rfl) ⟨585122, by rfl⟩ : syracuseStep 3120653 = 1170245) (by norm_num)
theorem B2309645 : Blo 1538466 2309645 := bbase (se 3 (by rfl) ⟨433058, by rfl⟩ : syracuseStep 2309645 = 866117) (by norm_num)
theorem B8764949 : Blo 1538466 8764949 := bbase (se 6 (by rfl) ⟨205428, by rfl⟩ : syracuseStep 8764949 = 410857) (by norm_num)
theorem B4931093 : Blo 1538466 4931093 := bbase (se 6 (by rfl) ⟨115572, by rfl⟩ : syracuseStep 4931093 = 231145) (by norm_num)
theorem B2309669 : Blo 1538466 2309669 := bbase (se 4 (by rfl) ⟨216531, by rfl⟩ : syracuseStep 2309669 = 433063) (by norm_num)
theorem B2309693 : Blo 1538466 2309693 := bbase (se 3 (by rfl) ⟨433067, by rfl⟩ : syracuseStep 2309693 = 866135) (by norm_num)
theorem B3464765 : Blo 1538466 3464765 := bbase (se 3 (by rfl) ⟨649643, by rfl⟩ : syracuseStep 3464765 = 1299287) (by norm_num)
theorem B2596421 : Blo 1538466 2596421 := bbase (se 4 (by rfl) ⟨243414, by rfl⟩ : syracuseStep 2596421 = 486829) (by norm_num)
theorem B2309717 : Blo 1538466 2309717 := bbase (se 8 (by rfl) ⟨13533, by rfl⟩ : syracuseStep 2309717 = 27067) (by norm_num)
theorem B2309741 : Blo 1538466 2309741 := bbase (se 3 (by rfl) ⟨433076, by rfl⟩ : syracuseStep 2309741 = 866153) (by norm_num)
theorem B2309765 : Blo 1538466 2309765 := bbase (se 4 (by rfl) ⟨216540, by rfl⟩ : syracuseStep 2309765 = 433081) (by norm_num)
theorem B3464837 : Blo 1538466 3464837 := bbase (se 4 (by rfl) ⟨324828, by rfl⟩ : syracuseStep 3464837 = 649657) (by norm_num)
theorem B2309789 : Blo 1538466 2309789 := bbase (se 3 (by rfl) ⟨433085, by rfl⟩ : syracuseStep 2309789 = 866171) (by norm_num)
theorem B2309813 : Blo 1538466 2309813 := bbase (se 5 (by rfl) ⟨108272, by rfl⟩ : syracuseStep 2309813 = 216545) (by norm_num)
theorem B2596549 : Blo 1538466 2596549 := bbase (se 4 (by rfl) ⟨243426, by rfl⟩ : syracuseStep 2596549 = 486853) (by norm_num)
theorem B2309837 : Blo 1538466 2309837 := bbase (se 3 (by rfl) ⟨433094, by rfl⟩ : syracuseStep 2309837 = 866189) (by norm_num)
theorem B3464909 : Blo 1538466 3464909 := bbase (se 3 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 3464909 = 1299341) (by norm_num)
theorem B5922533 : Blo 1538466 5922533 := bbase (se 4 (by rfl) ⟨555237, by rfl⟩ : syracuseStep 5922533 = 1110475) (by norm_num)
theorem B2309861 : Blo 1538466 2309861 := bbase (se 4 (by rfl) ⟨216549, by rfl⟩ : syracuseStep 2309861 = 433099) (by norm_num)
theorem B2309885 : Blo 1538466 2309885 := bbase (se 3 (by rfl) ⟨433103, by rfl⟩ : syracuseStep 2309885 = 866207) (by norm_num)
theorem B2309909 : Blo 1538466 2309909 := bbase (se 6 (by rfl) ⟨54138, by rfl⟩ : syracuseStep 2309909 = 108277) (by norm_num)
theorem B2596637 : Blo 1538466 2596637 := bbase (se 3 (by rfl) ⟨486869, by rfl⟩ : syracuseStep 2596637 = 973739) (by norm_num)
theorem B2309933 : Blo 1538466 2309933 := bbase (se 3 (by rfl) ⟨433112, by rfl⟩ : syracuseStep 2309933 = 866225) (by norm_num)
theorem B5193557 : Blo 1538466 5193557 := bbase (se 9 (by rfl) ⟨15215, by rfl⟩ : syracuseStep 5193557 = 30431) (by norm_num)
theorem B2080613 : Blo 1538466 2080613 := bbase (se 4 (by rfl) ⟨195057, by rfl⟩ : syracuseStep 2080613 = 390115) (by norm_num)
theorem B2596765 : Blo 1538466 2596765 := bbase (se 3 (by rfl) ⟨486893, by rfl⟩ : syracuseStep 2596765 = 973787) (by norm_num)
theorem B37969877 : Blo 1538466 37969877 := bbase (se 7 (by rfl) ⟨444959, by rfl⟩ : syracuseStep 37969877 = 889919) (by norm_num)
theorem B14786549 : Blo 1538466 14786549 := bbase (se 5 (by rfl) ⟨693119, by rfl⟩ : syracuseStep 14786549 = 1386239) (by norm_num)
theorem B2596853 : Blo 1538466 2596853 := bbase (se 5 (by rfl) ⟨121727, by rfl⟩ : syracuseStep 2596853 = 243455) (by norm_num)
theorem B5193773 : Blo 1538466 5193773 := bstep (se 3 (by rfl) ⟨973832, by rfl⟩ : syracuseStep 5193773 = 1947665) B1947665
theorem B2596961 : Blo 1538466 2596961 := bstep (se 2 (by rfl) ⟨973860, by rfl⟩ : syracuseStep 2596961 = 1947721) B1947721
theorem B5193827 : Blo 1538466 5193827 := bstep (se 1 (by rfl) ⟨3895370, by rfl⟩ : syracuseStep 5193827 = 7790741) B7790741
theorem B128098417 : Blo 1538466 128098417 := bstep (se 2 (by rfl) ⟨48036906, by rfl⟩ : syracuseStep 128098417 = 96073813) B96073813
theorem B2597089 : Blo 1538466 2597089 := bstep (se 2 (by rfl) ⟨973908, by rfl⟩ : syracuseStep 2597089 = 1947817) B1947817
theorem B5546225 : Blo 1538466 5546225 := bstep (se 2 (by rfl) ⟨2079834, by rfl⟩ : syracuseStep 5546225 = 4159669) B4159669
theorem B2597123 : Blo 1538466 2597123 := bstep (se 1 (by rfl) ⟨1947842, by rfl⟩ : syracuseStep 2597123 = 3895685) B3895685
theorem B2466065 : Blo 1538466 2466065 := bstep (se 2 (by rfl) ⟨924774, by rfl⟩ : syracuseStep 2466065 = 1849549) B1849549
theorem B33292565 : Blo 1538466 33292565 := bstep (se 6 (by rfl) ⟨780294, by rfl⟩ : syracuseStep 33292565 = 1560589) B1560589
theorem B4383011 : Blo 1538466 4383011 := bstep (se 1 (by rfl) ⟨3287258, by rfl⟩ : syracuseStep 4383011 = 6574517) B6574517
theorem B5194097 : Blo 1538466 5194097 := bstep (se 2 (by rfl) ⟨1947786, by rfl⟩ : syracuseStep 5194097 = 3895573) B3895573
theorem B2597251 : Blo 1538466 2597251 := bstep (se 1 (by rfl) ⟨1947938, by rfl⟩ : syracuseStep 2597251 = 3895877) B3895877
theorem B16007651 : Blo 1538466 16007651 := bstep (se 1 (by rfl) ⟨12005738, by rfl⟩ : syracuseStep 16007651 = 24011477) B24011477
theorem B2597393 : Blo 1538466 2597393 := bstep (se 2 (by rfl) ⟨974022, by rfl⟩ : syracuseStep 2597393 = 1948045) B1948045
theorem B4383341 : Blo 1538466 4383341 := bstep (se 3 (by rfl) ⟨821876, by rfl⟩ : syracuseStep 4383341 = 1643753) B1643753
theorem B2597521 : Blo 1538466 2597521 := bstep (se 2 (by rfl) ⟨974070, by rfl⟩ : syracuseStep 2597521 = 1948141) B1948141
theorem B4383409 : Blo 1538466 4383409 := bstep (se 2 (by rfl) ⟨1643778, by rfl⟩ : syracuseStep 4383409 = 3287557) B3287557
theorem B6242993 : Blo 1538466 6242993 := bstep (se 2 (by rfl) ⟨2341122, by rfl⟩ : syracuseStep 6242993 = 4682245) B4682245
theorem B2597555 : Blo 1538466 2597555 := bstep (se 1 (by rfl) ⟨1948166, by rfl⟩ : syracuseStep 2597555 = 3896333) B3896333
theorem B4932323 : Blo 1538466 4932323 := bstep (se 1 (by rfl) ⟨3699242, by rfl⟩ : syracuseStep 4932323 = 7398485) B7398485
theorem B2499347 : Blo 1538466 2499347 := bstep (se 1 (by rfl) ⟨1874510, by rfl⟩ : syracuseStep 2499347 = 3749021) B3749021
theorem B2597683 : Blo 1538466 2597683 := bstep (se 1 (by rfl) ⟨1948262, by rfl⟩ : syracuseStep 2597683 = 3896525) B3896525
theorem B1778563 : Blo 1538466 1778563 := bstep (se 1 (by rfl) ⟨1333922, by rfl⟩ : syracuseStep 1778563 = 2667845) B2667845
theorem B5194637 : Blo 1538466 5194637 := bstep (se 3 (by rfl) ⟨973994, by rfl⟩ : syracuseStep 5194637 = 1947989) B1947989
theorem B5841827 : Blo 1538466 5841827 := bstep (se 1 (by rfl) ⟨4381370, by rfl⟩ : syracuseStep 5841827 = 8762741) B8762741
theorem B5841841 : Blo 1538466 5841841 := bstep (se 2 (by rfl) ⟨2190690, by rfl⟩ : syracuseStep 5841841 = 4381381) B4381381
theorem B2597825 : Blo 1538466 2597825 := bstep (se 2 (by rfl) ⟨974184, by rfl⟩ : syracuseStep 2597825 = 1948369) B1948369
theorem B5194691 : Blo 1538466 5194691 := bstep (se 1 (by rfl) ⟨3896018, by rfl⟩ : syracuseStep 5194691 = 7792037) B7792037
theorem B4383683 : Blo 1538466 4383683 := bstep (se 1 (by rfl) ⟨3287762, by rfl⟩ : syracuseStep 4383683 = 6575525) B6575525
theorem B26665955 : Blo 1538466 26665955 := bstep (se 1 (by rfl) ⟨19999466, by rfl⟩ : syracuseStep 26665955 = 39998933) B39998933
theorem B2597953 : Blo 1538466 2597953 := bstep (se 2 (by rfl) ⟨974232, by rfl⟩ : syracuseStep 2597953 = 1948465) B1948465
theorem B2597987 : Blo 1538466 2597987 := bstep (se 1 (by rfl) ⟨1948490, by rfl⟩ : syracuseStep 2597987 = 3896981) B3896981
theorem B5547149 : Blo 1538466 5547149 := bstep (se 3 (by rfl) ⟨1040090, by rfl⟩ : syracuseStep 5547149 = 2080181) B2080181
theorem B5194961 : Blo 1538466 5194961 := bstep (se 2 (by rfl) ⟨1948110, by rfl⟩ : syracuseStep 5194961 = 3896221) B3896221
theorem B2598115 : Blo 1538466 2598115 := bstep (se 1 (by rfl) ⟨1948586, by rfl⟩ : syracuseStep 2598115 = 3897173) B3897173
theorem B5547377 : Blo 1538466 5547377 := bstep (se 2 (by rfl) ⟨2080266, by rfl⟩ : syracuseStep 5547377 = 4160533) B4160533
theorem B2598257 : Blo 1538466 2598257 := bstep (se 2 (by rfl) ⟨974346, by rfl⟩ : syracuseStep 2598257 = 1948693) B1948693
theorem B2598385 : Blo 1538466 2598385 := bstep (se 2 (by rfl) ⟨974394, by rfl⟩ : syracuseStep 2598385 = 1948789) B1948789
theorem B16238065 : Blo 1538466 16238065 := bstep (se 2 (by rfl) ⟨6089274, by rfl⟩ : syracuseStep 16238065 = 12178549) B12178549
theorem B3556867 : Blo 1538466 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B9364997 : Blo 1538466 9364997 := bstep (se 4 (by rfl) ⟨877968, by rfl⟩ : syracuseStep 9364997 = 1755937) B1755937
theorem B2598419 : Blo 1538466 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B9864773 : Blo 1538466 9864773 := bstep (se 4 (by rfl) ⟨924822, by rfl⟩ : syracuseStep 9864773 = 1849645) B1849645
theorem B2598547 : Blo 1538466 2598547 := bstep (se 1 (by rfl) ⟨1948910, by rfl⟩ : syracuseStep 2598547 = 3897821) B3897821
theorem B7399117 : Blo 1538466 7399117 := bstep (se 3 (by rfl) ⟨1387334, by rfl⟩ : syracuseStep 7399117 = 2774669) B2774669
theorem B5195501 : Blo 1538466 5195501 := bstep (se 3 (by rfl) ⟨974156, by rfl⟩ : syracuseStep 5195501 = 1948313) B1948313
theorem B4384525 : Blo 1538466 4384525 := bstep (se 3 (by rfl) ⟨822098, by rfl⟩ : syracuseStep 4384525 = 1644197) B1644197
theorem B2598689 : Blo 1538466 2598689 := bstep (se 2 (by rfl) ⟨974508, by rfl⟩ : syracuseStep 2598689 = 1949017) B1949017
theorem B5195555 : Blo 1538466 5195555 := bstep (se 1 (by rfl) ⟨3896666, by rfl⟩ : syracuseStep 5195555 = 7793333) B7793333
theorem B4384685 : Blo 1538466 4384685 := bstep (se 3 (by rfl) ⟨822128, by rfl⟩ : syracuseStep 4384685 = 1644257) B1644257
theorem B3286993 : Blo 1538466 3286993 := bstep (se 2 (by rfl) ⟨1232622, by rfl⟩ : syracuseStep 3286993 = 2465245) B2465245
theorem B5195825 : Blo 1538466 5195825 := bstep (se 2 (by rfl) ⟨1948434, by rfl⟩ : syracuseStep 5195825 = 3896869) B3896869
theorem B4384867 : Blo 1538466 4384867 := bstep (se 1 (by rfl) ⟨3288650, by rfl⟩ : syracuseStep 4384867 = 6577301) B6577301
theorem B2631827 : Blo 1538466 2631827 := bstep (se 1 (by rfl) ⟨1973870, by rfl⟩ : syracuseStep 2631827 = 3947741) B3947741
theorem B1730803 : Blo 1538466 1730803 := bstep (se 1 (by rfl) ⟨1298102, by rfl⟩ : syracuseStep 1730803 = 2596205) B2596205
theorem B5548301 : Blo 1538466 5548301 := bstep (se 3 (by rfl) ⟨1040306, by rfl⟩ : syracuseStep 5548301 = 2080613) B2080613
theorem B13330757 : Blo 1538466 13330757 := bstep (se 4 (by rfl) ⟨1249758, by rfl⟩ : syracuseStep 13330757 = 2499517) B2499517
theorem B5843299 : Blo 1538466 5843299 := bstep (se 1 (by rfl) ⟨4382474, by rfl⟩ : syracuseStep 5843299 = 8764949) B8764949
theorem B3287395 : Blo 1538466 3287395 := bstep (se 1 (by rfl) ⟨2465546, by rfl⟩ : syracuseStep 3287395 = 4931093) B4931093
theorem B7793009 : Blo 1538466 7793009 := bstep (se 2 (by rfl) ⟨2922378, by rfl⟩ : syracuseStep 7793009 = 5844757) B5844757
theorem B1730947 : Blo 1538466 1730947 := bstep (se 1 (by rfl) ⟨1298210, by rfl⟩ : syracuseStep 1730947 = 2596421) B2596421
theorem B1731091 : Blo 1538466 1731091 := bstep (se 1 (by rfl) ⟨1298318, by rfl⟩ : syracuseStep 1731091 = 2596637) B2596637
theorem B5196365 : Blo 1538466 5196365 := bstep (se 3 (by rfl) ⟨974318, by rfl⟩ : syracuseStep 5196365 = 1948637) B1948637
theorem B11094641 : Blo 1538466 11094641 := bstep (se 2 (by rfl) ⟨4160490, by rfl⟩ : syracuseStep 11094641 = 8320981) B8320981
theorem B5196419 : Blo 1538466 5196419 := bstep (se 1 (by rfl) ⟨3897314, by rfl⟩ : syracuseStep 5196419 = 7794629) B7794629
theorem B9857699 : Blo 1538466 9857699 := bstep (se 1 (by rfl) ⟨7393274, by rfl⟩ : syracuseStep 9857699 = 14786549) B14786549
theorem B1731235 : Blo 1538466 1731235 := bstep (se 1 (by rfl) ⟨1298426, by rfl⟩ : syracuseStep 1731235 = 2596853) B2596853
theorem B1731379 : Blo 1538466 1731379 := bstep (se 1 (by rfl) ⟨1298534, by rfl⟩ : syracuseStep 1731379 = 2597069) B2597069
theorem B5196689 : Blo 1538466 5196689 := bstep (se 2 (by rfl) ⟨1948758, by rfl⟩ : syracuseStep 5196689 = 3897517) B3897517
theorem B1731523 : Blo 1538466 1731523 := bstep (se 1 (by rfl) ⟨1298642, by rfl⟩ : syracuseStep 1731523 = 2597285) B2597285
theorem B3894257 : Blo 1538466 3894257 := bstep (se 2 (by rfl) ⟨1460346, by rfl⟩ : syracuseStep 3894257 = 2920693) B2920693
theorem B8432645 : Blo 1538466 8432645 := bstep (se 4 (by rfl) ⟨790560, by rfl⟩ : syracuseStep 8432645 = 1581121) B1581121
theorem B1731667 : Blo 1538466 1731667 := bstep (se 1 (by rfl) ⟨1298750, by rfl⟩ : syracuseStep 1731667 = 2597501) B2597501
theorem B1731811 : Blo 1538466 1731811 := bstep (se 1 (by rfl) ⟨1298858, by rfl⟩ : syracuseStep 1731811 = 2597717) B2597717
theorem B2190577 : Blo 1538466 2190577 := bstep (se 2 (by rfl) ⟨821466, by rfl⟩ : syracuseStep 2190577 = 1642933) B1642933
theorem B9358577 : Blo 1538466 9358577 := bstep (se 2 (by rfl) ⟨3509466, by rfl⟩ : syracuseStep 9358577 = 7018933) B7018933
theorem B3697937 : Blo 1538466 3697937 := bstep (se 2 (by rfl) ⟨1386726, by rfl⟩ : syracuseStep 3697937 = 2773453) B2773453
theorem B2190611 : Blo 1538466 2190611 := bstep (se 1 (by rfl) ⟨1642958, by rfl⟩ : syracuseStep 2190611 = 3285917) B3285917
theorem B1731955 : Blo 1538466 1731955 := bstep (se 1 (by rfl) ⟨1298966, by rfl⟩ : syracuseStep 1731955 = 2597933) B2597933
theorem B5197229 : Blo 1538466 5197229 := bstep (se 3 (by rfl) ⟨974480, by rfl⟩ : syracuseStep 5197229 = 1948961) B1948961
theorem B5197283 : Blo 1538466 5197283 := bstep (se 1 (by rfl) ⟨3897962, by rfl⟩ : syracuseStep 5197283 = 7795925) B7795925
theorem B1732099 : Blo 1538466 1732099 := bstep (se 1 (by rfl) ⟨1299074, by rfl⟩ : syracuseStep 1732099 = 2598149) B2598149
theorem B1732243 : Blo 1538466 1732243 := bstep (se 1 (by rfl) ⟨1299182, by rfl⟩ : syracuseStep 1732243 = 2598365) B2598365
theorem B7794467 : Blo 1538466 7794467 := bstep (se 1 (by rfl) ⟨5845850, by rfl⟩ : syracuseStep 7794467 = 11691701) B11691701
theorem B1732387 : Blo 1538466 1732387 := bstep (se 1 (by rfl) ⟨1299290, by rfl⟩ : syracuseStep 1732387 = 2598581) B2598581
theorem B2191169 : Blo 1538466 2191169 := bstep (se 2 (by rfl) ⟨821688, by rfl⟩ : syracuseStep 2191169 = 1643377) B1643377
theorem B3288899 : Blo 1538466 3288899 := bstep (se 1 (by rfl) ⟨2466674, by rfl⟩ : syracuseStep 3288899 = 4933349) B4933349
theorem B2191249 : Blo 1538466 2191249 := bstep (se 2 (by rfl) ⟨821718, by rfl⟩ : syracuseStep 2191249 = 1643437) B1643437
theorem B3698627 : Blo 1538466 3698627 := bstep (se 1 (by rfl) ⟨2773970, by rfl⟩ : syracuseStep 3698627 = 5547941) B5547941
theorem B3895249 : Blo 1538466 3895249 := bstep (se 2 (by rfl) ⟨1460718, by rfl⟩ : syracuseStep 3895249 = 2921437) B2921437
theorem B2470003 : Blo 1538466 2470003 := bstep (se 1 (by rfl) ⟨1852502, by rfl⟩ : syracuseStep 2470003 = 3705005) B3705005
theorem B6574243 : Blo 1538466 6574243 := bstep (se 1 (by rfl) ⟨4930682, by rfl⟩ : syracuseStep 6574243 = 9861365) B9861365
theorem B3895523 : Blo 1538466 3895523 := bstep (se 1 (by rfl) ⟨2921642, by rfl⟩ : syracuseStep 3895523 = 5843285) B5843285
theorem B9859441 : Blo 1538466 9859441 := bstep (se 2 (by rfl) ⟨3697290, by rfl⟩ : syracuseStep 9859441 = 7394581) B7394581
theorem B3895715 : Blo 1538466 3895715 := bstep (se 1 (by rfl) ⟨2921786, by rfl⟩ : syracuseStep 3895715 = 5843573) B5843573
theorem B4444625 : Blo 1538466 4444625 := bstep (se 2 (by rfl) ⟨1666734, by rfl⟩ : syracuseStep 4444625 = 3333469) B3333469
theorem B5845517 : Blo 1538466 5845517 := bstep (se 3 (by rfl) ⟨1096034, by rfl⟩ : syracuseStep 5845517 = 2192069) B2192069
theorem B7795277 : Blo 1538466 7795277 := bstep (se 3 (by rfl) ⟨1461614, by rfl⟩ : syracuseStep 7795277 = 2923229) B2923229
theorem B20001421 : Blo 1538466 20001421 := bstep (se 3 (by rfl) ⟨3750266, by rfl⟩ : syracuseStep 20001421 = 7500533) B7500533
theorem B3461777 : Blo 1538466 3461777 := bstep (se 2 (by rfl) ⟨1298166, by rfl⟩ : syracuseStep 3461777 = 2596333) B2596333
theorem B3461795 : Blo 1538466 3461795 := bstep (se 1 (by rfl) ⟨2596346, by rfl⟩ : syracuseStep 3461795 = 5192693) B5192693
theorem B9360035 : Blo 1538466 9360035 := bstep (se 1 (by rfl) ⟨7020026, by rfl⟩ : syracuseStep 9360035 = 14040053) B14040053
theorem B2192035 : Blo 1538466 2192035 := bstep (se 1 (by rfl) ⟨1644026, by rfl⟩ : syracuseStep 2192035 = 3288053) B3288053
theorem B2437859 : Blo 1538466 2437859 := bstep (se 1 (by rfl) ⟨1828394, by rfl⟩ : syracuseStep 2437859 = 3656789) B3656789
theorem B7213937 : Blo 1538466 7213937 := bstep (se 2 (by rfl) ⟨2705226, by rfl⟩ : syracuseStep 7213937 = 5410453) B5410453
theorem B3462065 : Blo 1538466 3462065 := bstep (se 2 (by rfl) ⟨1298274, by rfl⟩ : syracuseStep 3462065 = 2596549) B2596549
theorem B3462083 : Blo 1538466 3462083 := bstep (se 1 (by rfl) ⟨2596562, by rfl⟩ : syracuseStep 3462083 = 5193125) B5193125
theorem B2339875 : Blo 1538466 2339875 := bstep (se 1 (by rfl) ⟨1754906, by rfl⟩ : syracuseStep 2339875 = 3509813) B3509813
theorem B2921521 : Blo 1538466 2921521 := bstep (se 2 (by rfl) ⟨1095570, by rfl⟩ : syracuseStep 2921521 = 2191141) B2191141
theorem B53310517 : Blo 1538466 53310517 := bstep (se 5 (by rfl) ⟨2498930, by rfl⟩ : syracuseStep 53310517 = 4997861) B4997861
theorem B2192513 : Blo 1538466 2192513 := bstep (se 2 (by rfl) ⟨822192, by rfl⟩ : syracuseStep 2192513 = 1644385) B1644385
theorem B3462353 : Blo 1538466 3462353 := bstep (se 2 (by rfl) ⟨1298382, by rfl⟩ : syracuseStep 3462353 = 2596765) B2596765
theorem B3462371 : Blo 1538466 3462371 := bstep (se 1 (by rfl) ⟨2596778, by rfl⟩ : syracuseStep 3462371 = 5193557) B5193557
theorem B2192627 : Blo 1538466 2192627 := bstep (se 1 (by rfl) ⟨1644470, by rfl⟩ : syracuseStep 2192627 = 3288941) B3288941
theorem B3896657 : Blo 1538466 3896657 := bstep (se 2 (by rfl) ⟨1461246, by rfl⟩ : syracuseStep 3896657 = 2922493) B2922493
theorem B3896707 : Blo 1538466 3896707 := bstep (se 1 (by rfl) ⟨2922530, by rfl⟩ : syracuseStep 3896707 = 5845061) B5845061
theorem B4216237 : Blo 1538466 4216237 := bstep (se 3 (by rfl) ⟨790544, by rfl⟩ : syracuseStep 4216237 = 1581089) B1581089
theorem B2921923 : Blo 1538466 2921923 := bstep (se 1 (by rfl) ⟨2191442, by rfl⟩ : syracuseStep 2921923 = 4382885) B4382885
theorem B1643971 : Blo 1538466 1643971 := bstep (se 1 (by rfl) ⟨1232978, by rfl⟩ : syracuseStep 1643971 = 2465957) B2465957
theorem B3462641 : Blo 1538466 3462641 := bstep (se 2 (by rfl) ⟨1298490, by rfl⟩ : syracuseStep 3462641 = 2596981) B2596981
theorem B2921969 : Blo 1538466 2921969 := bstep (se 2 (by rfl) ⟨1095738, by rfl⟩ : syracuseStep 2921969 = 2191477) B2191477
theorem B3462659 : Blo 1538466 3462659 := bstep (se 1 (by rfl) ⟨2596994, by rfl⟩ : syracuseStep 3462659 = 5193989) B5193989
theorem B3896849 : Blo 1538466 3896849 := bstep (se 2 (by rfl) ⟨1461318, by rfl⟩ : syracuseStep 3896849 = 2922637) B2922637
theorem B3331633 : Blo 1538466 3331633 := bstep (se 2 (by rfl) ⟨1249362, by rfl⟩ : syracuseStep 3331633 = 2498725) B2498725
theorem B1947235 : Blo 1538466 1947235 := bstep (se 1 (by rfl) ⟨1460426, by rfl⟩ : syracuseStep 1947235 = 2920853) B2920853
theorem B2307713 : Blo 1538466 2307713 := bstep (se 2 (by rfl) ⟨865392, by rfl⟩ : syracuseStep 2307713 = 1730785) B1730785
theorem B2307731 : Blo 1538466 2307731 := bstep (se 1 (by rfl) ⟨1730798, by rfl⟩ : syracuseStep 2307731 = 3461597) B3461597
theorem B2307761 : Blo 1538466 2307761 := bstep (se 2 (by rfl) ⟨865410, by rfl⟩ : syracuseStep 2307761 = 1730821) B1730821
theorem B2307779 : Blo 1538466 2307779 := bstep (se 1 (by rfl) ⟨1730834, by rfl⟩ : syracuseStep 2307779 = 3461669) B3461669
theorem B1947331 : Blo 1538466 1947331 := bstep (se 1 (by rfl) ⟨1460498, by rfl⟩ : syracuseStep 1947331 = 2920997) B2920997
theorem B2307809 : Blo 1538466 2307809 := bstep (se 2 (by rfl) ⟨865428, by rfl⟩ : syracuseStep 2307809 = 1730857) B1730857
theorem B2340593 : Blo 1538466 2340593 := bstep (se 2 (by rfl) ⟨877722, by rfl⟩ : syracuseStep 2340593 = 1755445) B1755445
theorem B2307827 : Blo 1538466 2307827 := bstep (se 1 (by rfl) ⟨1730870, by rfl⟩ : syracuseStep 2307827 = 3461741) B3461741
theorem B2307857 : Blo 1538466 2307857 := bstep (se 2 (by rfl) ⟨865446, by rfl⟩ : syracuseStep 2307857 = 1730893) B1730893
theorem B3462929 : Blo 1538466 3462929 := bstep (se 2 (by rfl) ⟨1298598, by rfl⟩ : syracuseStep 3462929 = 2597197) B2597197
theorem B2922257 : Blo 1538466 2922257 := bstep (se 2 (by rfl) ⟨1095846, by rfl⟩ : syracuseStep 2922257 = 2191693) B2191693
theorem B2307875 : Blo 1538466 2307875 := bstep (se 1 (by rfl) ⟨1730906, by rfl⟩ : syracuseStep 2307875 = 3461813) B3461813
theorem B3462947 : Blo 1538466 3462947 := bstep (se 1 (by rfl) ⟨2597210, by rfl⟩ : syracuseStep 3462947 = 5194421) B5194421
theorem B2307905 : Blo 1538466 2307905 := bstep (se 2 (by rfl) ⟨865464, by rfl⟩ : syracuseStep 2307905 = 1730929) B1730929
theorem B2307923 : Blo 1538466 2307923 := bstep (se 1 (by rfl) ⟨1730942, by rfl⟩ : syracuseStep 2307923 = 3461885) B3461885
theorem B2307953 : Blo 1538466 2307953 := bstep (se 2 (by rfl) ⟨865482, by rfl⟩ : syracuseStep 2307953 = 1730965) B1730965
theorem B2307971 : Blo 1538466 2307971 := bstep (se 1 (by rfl) ⟨1730978, by rfl⟩ : syracuseStep 2307971 = 3461957) B3461957
theorem B1644419 : Blo 1538466 1644419 := bstep (se 1 (by rfl) ⟨1233314, by rfl⟩ : syracuseStep 1644419 = 2466629) B2466629
theorem B2308001 : Blo 1538466 2308001 := bstep (se 2 (by rfl) ⟨865500, by rfl⟩ : syracuseStep 2308001 = 1731001) B1731001
theorem B2308019 : Blo 1538466 2308019 := bstep (se 1 (by rfl) ⟨1731014, by rfl⟩ : syracuseStep 2308019 = 3462029) B3462029
theorem B2308049 : Blo 1538466 2308049 := bstep (se 2 (by rfl) ⟨865518, by rfl⟩ : syracuseStep 2308049 = 1731037) B1731037
theorem B2308067 : Blo 1538466 2308067 := bstep (se 1 (by rfl) ⟨1731050, by rfl⟩ : syracuseStep 2308067 = 3462101) B3462101
theorem B2308097 : Blo 1538466 2308097 := bstep (se 2 (by rfl) ⟨865536, by rfl⟩ : syracuseStep 2308097 = 1731073) B1731073
theorem B2308115 : Blo 1538466 2308115 := bstep (se 1 (by rfl) ⟨1731086, by rfl⟩ : syracuseStep 2308115 = 3462173) B3462173
theorem B2308145 : Blo 1538466 2308145 := bstep (se 2 (by rfl) ⟨865554, by rfl⟩ : syracuseStep 2308145 = 1731109) B1731109
theorem B3463217 : Blo 1538466 3463217 := bstep (se 2 (by rfl) ⟨1298706, by rfl⟩ : syracuseStep 3463217 = 2597413) B2597413
theorem B2308163 : Blo 1538466 2308163 := bstep (se 1 (by rfl) ⟨1731122, by rfl⟩ : syracuseStep 2308163 = 3462245) B3462245
theorem B3463235 : Blo 1538466 3463235 := bstep (se 1 (by rfl) ⟨2597426, by rfl⟩ : syracuseStep 3463235 = 5194853) B5194853
theorem B2308193 : Blo 1538466 2308193 := bstep (se 2 (by rfl) ⟨865572, by rfl⟩ : syracuseStep 2308193 = 1731145) B1731145
theorem B8763491 : Blo 1538466 8763491 := bstep (se 1 (by rfl) ⟨6572618, by rfl⟩ : syracuseStep 8763491 = 13145237) B13145237
theorem B6576241 : Blo 1538466 6576241 := bstep (se 2 (by rfl) ⟨2466090, by rfl⟩ : syracuseStep 6576241 = 4932181) B4932181
theorem B2308211 : Blo 1538466 2308211 := bstep (se 1 (by rfl) ⟨1731158, by rfl⟩ : syracuseStep 2308211 = 3462317) B3462317
theorem B2308241 : Blo 1538466 2308241 := bstep (se 2 (by rfl) ⟨865590, by rfl⟩ : syracuseStep 2308241 = 1731181) B1731181
theorem B2308259 : Blo 1538466 2308259 := bstep (se 1 (by rfl) ⟨1731194, by rfl⟩ : syracuseStep 2308259 = 3462389) B3462389
theorem B1947827 : Blo 1538466 1947827 := bstep (se 1 (by rfl) ⟨1460870, by rfl⟩ : syracuseStep 1947827 = 2921741) B2921741
theorem B2308289 : Blo 1538466 2308289 := bstep (se 2 (by rfl) ⟨865608, by rfl⟩ : syracuseStep 2308289 = 1731217) B1731217
theorem B2308307 : Blo 1538466 2308307 := bstep (se 1 (by rfl) ⟨1731230, by rfl⟩ : syracuseStep 2308307 = 3462461) B3462461
theorem B2308337 : Blo 1538466 2308337 := bstep (se 2 (by rfl) ⟨865626, by rfl⟩ : syracuseStep 2308337 = 1731253) B1731253
theorem B2308355 : Blo 1538466 2308355 := bstep (se 1 (by rfl) ⟨1731266, by rfl⟩ : syracuseStep 2308355 = 3462533) B3462533
theorem B8321285 : Blo 1538466 8321285 := bstep (se 4 (by rfl) ⟨780120, by rfl⟩ : syracuseStep 8321285 = 1560241) B1560241
theorem B9861389 : Blo 1538466 9861389 := bstep (se 3 (by rfl) ⟨1849010, by rfl⟩ : syracuseStep 9861389 = 3698021) B3698021
theorem B2308385 : Blo 1538466 2308385 := bstep (se 2 (by rfl) ⟨865644, by rfl⟩ : syracuseStep 2308385 = 1731289) B1731289
theorem B2308403 : Blo 1538466 2308403 := bstep (se 1 (by rfl) ⟨1731302, by rfl⟩ : syracuseStep 2308403 = 3462605) B3462605
theorem B2308433 : Blo 1538466 2308433 := bstep (se 2 (by rfl) ⟨865662, by rfl⟩ : syracuseStep 2308433 = 1731325) B1731325
theorem B3463505 : Blo 1538466 3463505 := bstep (se 2 (by rfl) ⟨1298814, by rfl⟩ : syracuseStep 3463505 = 2597629) B2597629
theorem B7493987 : Blo 1538466 7493987 := bstep (se 1 (by rfl) ⟨5620490, by rfl⟩ : syracuseStep 7493987 = 11240981) B11240981
theorem B2308451 : Blo 1538466 2308451 := bstep (se 1 (by rfl) ⟨1731338, by rfl⟩ : syracuseStep 2308451 = 3462677) B3462677
theorem B3463523 : Blo 1538466 3463523 := bstep (se 1 (by rfl) ⟨2597642, by rfl⟩ : syracuseStep 3463523 = 5195285) B5195285
theorem B2308481 : Blo 1538466 2308481 := bstep (se 2 (by rfl) ⟨865680, by rfl⟩ : syracuseStep 2308481 = 1731361) B1731361
theorem B8321413 : Blo 1538466 8321413 := bstep (se 4 (by rfl) ⟨780132, by rfl⟩ : syracuseStep 8321413 = 1560265) B1560265
theorem B2308499 : Blo 1538466 2308499 := bstep (se 1 (by rfl) ⟨1731374, by rfl⟩ : syracuseStep 2308499 = 3462749) B3462749
theorem B1538467 : Blo 1538466 1538467 := bstep (se 1 (by rfl) ⟨1153850, by rfl⟩ : syracuseStep 1538467 = 2307701) B2307701
theorem B2308529 : Blo 1538466 2308529 := bstep (se 2 (by rfl) ⟨865698, by rfl⟩ : syracuseStep 2308529 = 1731397) B1731397
theorem B1538483 : Blo 1538466 1538483 := bstep (se 1 (by rfl) ⟨1153862, by rfl⟩ : syracuseStep 1538483 = 2307725) B2307725
theorem B1538499 : Blo 1538466 1538499 := bstep (se 1 (by rfl) ⟨1153874, by rfl⟩ : syracuseStep 1538499 = 2307749) B2307749
theorem B2308547 : Blo 1538466 2308547 := bstep (se 1 (by rfl) ⟨1731410, by rfl⟩ : syracuseStep 2308547 = 3462821) B3462821
theorem B1538515 : Blo 1538466 1538515 := bstep (se 1 (by rfl) ⟨1153886, by rfl⟩ : syracuseStep 1538515 = 2307773) B2307773
theorem B2308577 : Blo 1538466 2308577 := bstep (se 2 (by rfl) ⟨865716, by rfl⟩ : syracuseStep 2308577 = 1731433) B1731433
theorem B1538531 : Blo 1538466 1538531 := bstep (se 1 (by rfl) ⟨1153898, by rfl⟩ : syracuseStep 1538531 = 2307797) B2307797
theorem B2922979 : Blo 1538466 2922979 := bstep (se 1 (by rfl) ⟨2192234, by rfl⟩ : syracuseStep 2922979 = 4384469) B4384469
theorem B3897841 : Blo 1538466 3897841 := bstep (se 2 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 3897841 = 2923381) B2923381
theorem B1538547 : Blo 1538466 1538547 := bstep (se 1 (by rfl) ⟨1153910, by rfl⟩ : syracuseStep 1538547 = 2307821) B2307821
theorem B2308595 : Blo 1538466 2308595 := bstep (se 1 (by rfl) ⟨1731446, by rfl⟩ : syracuseStep 2308595 = 3462893) B3462893
theorem B1538563 : Blo 1538466 1538563 := bstep (se 1 (by rfl) ⟨1153922, by rfl⟩ : syracuseStep 1538563 = 2307845) B2307845
theorem B2308625 : Blo 1538466 2308625 := bstep (se 2 (by rfl) ⟨865734, by rfl⟩ : syracuseStep 2308625 = 1731469) B1731469
theorem B1538579 : Blo 1538466 1538579 := bstep (se 1 (by rfl) ⟨1153934, by rfl⟩ : syracuseStep 1538579 = 2307869) B2307869
theorem B1538595 : Blo 1538466 1538595 := bstep (se 1 (by rfl) ⟨1153946, by rfl⟩ : syracuseStep 1538595 = 2307893) B2307893
theorem B2308643 : Blo 1538466 2308643 := bstep (se 1 (by rfl) ⟨1731482, by rfl⟩ : syracuseStep 2308643 = 3462965) B3462965
theorem B1849891 : Blo 1538466 1849891 := bstep (se 1 (by rfl) ⟨1387418, by rfl⟩ : syracuseStep 1849891 = 2774837) B2774837
theorem B1538611 : Blo 1538466 1538611 := bstep (se 1 (by rfl) ⟨1153958, by rfl⟩ : syracuseStep 1538611 = 2307917) B2307917
theorem B2308673 : Blo 1538466 2308673 := bstep (se 2 (by rfl) ⟨865752, by rfl⟩ : syracuseStep 2308673 = 1731505) B1731505
theorem B1538627 : Blo 1538466 1538627 := bstep (se 1 (by rfl) ⟨1153970, by rfl⟩ : syracuseStep 1538627 = 2307941) B2307941
theorem B9484877 : Blo 1538466 9484877 := bstep (se 3 (by rfl) ⟨1778414, by rfl⟩ : syracuseStep 9484877 = 3556829) B3556829
theorem B1538643 : Blo 1538466 1538643 := bstep (se 1 (by rfl) ⟨1153982, by rfl⟩ : syracuseStep 1538643 = 2307965) B2307965
theorem B2308691 : Blo 1538466 2308691 := bstep (se 1 (by rfl) ⟨1731518, by rfl⟩ : syracuseStep 2308691 = 3463037) B3463037
theorem B1538659 : Blo 1538466 1538659 := bstep (se 1 (by rfl) ⟨1153994, by rfl⟩ : syracuseStep 1538659 = 2307989) B2307989
theorem B2308721 : Blo 1538466 2308721 := bstep (se 2 (by rfl) ⟨865770, by rfl⟩ : syracuseStep 2308721 = 1731541) B1731541
theorem B3463793 : Blo 1538466 3463793 := bstep (se 2 (by rfl) ⟨1298922, by rfl⟩ : syracuseStep 3463793 = 2597845) B2597845
theorem B1538675 : Blo 1538466 1538675 := bstep (se 1 (by rfl) ⟨1154006, by rfl⟩ : syracuseStep 1538675 = 2308013) B2308013
theorem B1538691 : Blo 1538466 1538691 := bstep (se 1 (by rfl) ⟨1154018, by rfl⟩ : syracuseStep 1538691 = 2308037) B2308037
theorem B2308739 : Blo 1538466 2308739 := bstep (se 1 (by rfl) ⟨1731554, by rfl⟩ : syracuseStep 2308739 = 3463109) B3463109
theorem B3463811 : Blo 1538466 3463811 := bstep (se 1 (by rfl) ⟨2597858, by rfl⟩ : syracuseStep 3463811 = 5195717) B5195717
theorem B7019149 : Blo 1538466 7019149 := bstep (se 3 (by rfl) ⟨1316090, by rfl⟩ : syracuseStep 7019149 = 2632181) B2632181
theorem B1538707 : Blo 1538466 1538707 := bstep (se 1 (by rfl) ⟨1154030, by rfl⟩ : syracuseStep 1538707 = 2308061) B2308061
theorem B2308769 : Blo 1538466 2308769 := bstep (se 2 (by rfl) ⟨865788, by rfl⟩ : syracuseStep 2308769 = 1731577) B1731577
theorem B1538723 : Blo 1538466 1538723 := bstep (se 1 (by rfl) ⟨1154042, by rfl⟩ : syracuseStep 1538723 = 2308085) B2308085
theorem B10533539 : Blo 1538466 10533539 := bstep (se 1 (by rfl) ⟨7900154, by rfl⟩ : syracuseStep 10533539 = 15800309) B15800309
theorem B5192369 : Blo 1538466 5192369 := bstep (se 2 (by rfl) ⟨1947138, by rfl⟩ : syracuseStep 5192369 = 3894277) B3894277
theorem B1538739 : Blo 1538466 1538739 := bstep (se 1 (by rfl) ⟨1154054, by rfl⟩ : syracuseStep 1538739 = 2308109) B2308109
theorem B2308787 : Blo 1538466 2308787 := bstep (se 1 (by rfl) ⟨1731590, by rfl⟩ : syracuseStep 2308787 = 3463181) B3463181
theorem B1538755 : Blo 1538466 1538755 := bstep (se 1 (by rfl) ⟨1154066, by rfl⟩ : syracuseStep 1538755 = 2308133) B2308133
theorem B29588165 : Blo 1538466 29588165 := bstep (se 4 (by rfl) ⟨2773890, by rfl⟩ : syracuseStep 29588165 = 5547781) B5547781
theorem B8321741 : Blo 1538466 8321741 := bstep (se 3 (by rfl) ⟨1560326, by rfl⟩ : syracuseStep 8321741 = 3120653) B3120653
theorem B2308817 : Blo 1538466 2308817 := bstep (se 2 (by rfl) ⟨865806, by rfl⟩ : syracuseStep 2308817 = 1731613) B1731613
theorem B1538771 : Blo 1538466 1538771 := bstep (se 1 (by rfl) ⟨1154078, by rfl⟩ : syracuseStep 1538771 = 2308157) B2308157
theorem B7789283 : Blo 1538466 7789283 := bstep (se 1 (by rfl) ⟨5841962, by rfl⟩ : syracuseStep 7789283 = 11683925) B11683925
theorem B1538787 : Blo 1538466 1538787 := bstep (se 1 (by rfl) ⟨1154090, by rfl⟩ : syracuseStep 1538787 = 2308181) B2308181
theorem B2308835 : Blo 1538466 2308835 := bstep (se 1 (by rfl) ⟨1731626, by rfl⟩ : syracuseStep 2308835 = 3463253) B3463253
theorem B1538803 : Blo 1538466 1538803 := bstep (se 1 (by rfl) ⟨1154102, by rfl⟩ : syracuseStep 1538803 = 2308205) B2308205
theorem B2308865 : Blo 1538466 2308865 := bstep (se 2 (by rfl) ⟨865824, by rfl⟩ : syracuseStep 2308865 = 1731649) B1731649
theorem B1538819 : Blo 1538466 1538819 := bstep (se 1 (by rfl) ⟨1154114, by rfl⟩ : syracuseStep 1538819 = 2308229) B2308229
theorem B1538835 : Blo 1538466 1538835 := bstep (se 1 (by rfl) ⟨1154126, by rfl⟩ : syracuseStep 1538835 = 2308253) B2308253
theorem B2308883 : Blo 1538466 2308883 := bstep (se 1 (by rfl) ⟨1731662, by rfl⟩ : syracuseStep 2308883 = 3463325) B3463325
theorem B1538851 : Blo 1538466 1538851 := bstep (se 1 (by rfl) ⟨1154138, by rfl⟩ : syracuseStep 1538851 = 2308277) B2308277
theorem B2308913 : Blo 1538466 2308913 := bstep (se 2 (by rfl) ⟨865842, by rfl⟩ : syracuseStep 2308913 = 1731685) B1731685
theorem B1538867 : Blo 1538466 1538867 := bstep (se 1 (by rfl) ⟨1154150, by rfl⟩ : syracuseStep 1538867 = 2308301) B2308301
theorem B1538883 : Blo 1538466 1538883 := bstep (se 1 (by rfl) ⟨1154162, by rfl⟩ : syracuseStep 1538883 = 2308325) B2308325
theorem B2308931 : Blo 1538466 2308931 := bstep (se 1 (by rfl) ⟨1731698, by rfl⟩ : syracuseStep 2308931 = 3463397) B3463397
theorem B1538899 : Blo 1538466 1538899 := bstep (se 1 (by rfl) ⟨1154174, by rfl⟩ : syracuseStep 1538899 = 2308349) B2308349
theorem B2308961 : Blo 1538466 2308961 := bstep (se 2 (by rfl) ⟨865860, by rfl⟩ : syracuseStep 2308961 = 1731721) B1731721
theorem B1538915 : Blo 1538466 1538915 := bstep (se 1 (by rfl) ⟨1154186, by rfl⟩ : syracuseStep 1538915 = 2308373) B2308373
theorem B4381553 : Blo 1538466 4381553 := bstep (se 2 (by rfl) ⟨1643082, by rfl⟩ : syracuseStep 4381553 = 3286165) B3286165
theorem B1538931 : Blo 1538466 1538931 := bstep (se 1 (by rfl) ⟨1154198, by rfl⟩ : syracuseStep 1538931 = 2308397) B2308397
theorem B2308979 : Blo 1538466 2308979 := bstep (se 1 (by rfl) ⟨1731734, by rfl⟩ : syracuseStep 2308979 = 3463469) B3463469
theorem B1948531 : Blo 1538466 1948531 := bstep (se 1 (by rfl) ⟨1461398, by rfl⟩ : syracuseStep 1948531 = 2922797) B2922797
theorem B2464643 : Blo 1538466 2464643 := bstep (se 1 (by rfl) ⟨1848482, by rfl⟩ : syracuseStep 2464643 = 3696965) B3696965
theorem B1538947 : Blo 1538466 1538947 := bstep (se 1 (by rfl) ⟨1154210, by rfl⟩ : syracuseStep 1538947 = 2308421) B2308421
theorem B2309009 : Blo 1538466 2309009 := bstep (se 2 (by rfl) ⟨865878, by rfl⟩ : syracuseStep 2309009 = 1731757) B1731757
theorem B3464081 : Blo 1538466 3464081 := bstep (se 2 (by rfl) ⟨1299030, by rfl⟩ : syracuseStep 3464081 = 2598061) B2598061
theorem B1538963 : Blo 1538466 1538963 := bstep (se 1 (by rfl) ⟨1154222, by rfl⟩ : syracuseStep 1538963 = 2308445) B2308445
theorem B1538979 : Blo 1538466 1538979 := bstep (se 1 (by rfl) ⟨1154234, by rfl⟩ : syracuseStep 1538979 = 2308469) B2308469
theorem B2309027 : Blo 1538466 2309027 := bstep (se 1 (by rfl) ⟨1731770, by rfl⟩ : syracuseStep 2309027 = 3463541) B3463541
theorem B3464099 : Blo 1538466 3464099 := bstep (se 1 (by rfl) ⟨2598074, by rfl⟩ : syracuseStep 3464099 = 5196149) B5196149
theorem B2923427 : Blo 1538466 2923427 := bstep (se 1 (by rfl) ⟨2192570, by rfl⟩ : syracuseStep 2923427 = 4385141) B4385141
theorem B1538995 : Blo 1538466 1538995 := bstep (se 1 (by rfl) ⟨1154246, by rfl⟩ : syracuseStep 1538995 = 2308493) B2308493
theorem B2309057 : Blo 1538466 2309057 := bstep (se 2 (by rfl) ⟨865896, by rfl⟩ : syracuseStep 2309057 = 1731793) B1731793
theorem B1539011 : Blo 1538466 1539011 := bstep (se 1 (by rfl) ⟨1154258, by rfl⟩ : syracuseStep 1539011 = 2308517) B2308517
theorem B1539027 : Blo 1538466 1539027 := bstep (se 1 (by rfl) ⟨1154270, by rfl⟩ : syracuseStep 1539027 = 2308541) B2308541
theorem B2309075 : Blo 1538466 2309075 := bstep (se 1 (by rfl) ⟨1731806, by rfl⟩ : syracuseStep 2309075 = 3463613) B3463613
theorem B1948627 : Blo 1538466 1948627 := bstep (se 1 (by rfl) ⟨1461470, by rfl⟩ : syracuseStep 1948627 = 2922941) B2922941
theorem B1539043 : Blo 1538466 1539043 := bstep (se 1 (by rfl) ⟨1154282, by rfl⟩ : syracuseStep 1539043 = 2308565) B2308565
theorem B4930541 : Blo 1538466 4930541 := bstep (se 3 (by rfl) ⟨924476, by rfl⟩ : syracuseStep 4930541 = 1848953) B1848953
theorem B2309105 : Blo 1538466 2309105 := bstep (se 2 (by rfl) ⟨865914, by rfl⟩ : syracuseStep 2309105 = 1731829) B1731829
theorem B10001393 : Blo 1538466 10001393 := bstep (se 2 (by rfl) ⟨3750522, by rfl⟩ : syracuseStep 10001393 = 7501045) B7501045
theorem B1539059 : Blo 1538466 1539059 := bstep (se 1 (by rfl) ⟨1154294, by rfl⟩ : syracuseStep 1539059 = 2308589) B2308589
theorem B1539075 : Blo 1538466 1539075 := bstep (se 1 (by rfl) ⟨1154306, by rfl⟩ : syracuseStep 1539075 = 2308613) B2308613
theorem B2309123 : Blo 1538466 2309123 := bstep (se 1 (by rfl) ⟨1731842, by rfl⟩ : syracuseStep 2309123 = 3463685) B3463685
theorem B1539091 : Blo 1538466 1539091 := bstep (se 1 (by rfl) ⟨1154318, by rfl⟩ : syracuseStep 1539091 = 2308637) B2308637
theorem B2309153 : Blo 1538466 2309153 := bstep (se 2 (by rfl) ⟨865932, by rfl⟩ : syracuseStep 2309153 = 1731865) B1731865
theorem B1539107 : Blo 1538466 1539107 := bstep (se 1 (by rfl) ⟨1154330, by rfl⟩ : syracuseStep 1539107 = 2308661) B2308661
theorem B1539123 : Blo 1538466 1539123 := bstep (se 1 (by rfl) ⟨1154342, by rfl⟩ : syracuseStep 1539123 = 2308685) B2308685
theorem B2309171 : Blo 1538466 2309171 := bstep (se 1 (by rfl) ⟨1731878, by rfl⟩ : syracuseStep 2309171 = 3463757) B3463757
theorem B1539139 : Blo 1538466 1539139 := bstep (se 1 (by rfl) ⟨1154354, by rfl⟩ : syracuseStep 1539139 = 2308709) B2308709
theorem B2309201 : Blo 1538466 2309201 := bstep (se 2 (by rfl) ⟨865950, by rfl⟩ : syracuseStep 2309201 = 1731901) B1731901
theorem B1539155 : Blo 1538466 1539155 := bstep (se 1 (by rfl) ⟨1154366, by rfl⟩ : syracuseStep 1539155 = 2308733) B2308733
theorem B1539171 : Blo 1538466 1539171 := bstep (se 1 (by rfl) ⟨1154378, by rfl⟩ : syracuseStep 1539171 = 2308757) B2308757
theorem B2309219 : Blo 1538466 2309219 := bstep (se 1 (by rfl) ⟨1731914, by rfl⟩ : syracuseStep 2309219 = 3463829) B3463829
theorem B13360241 : Blo 1538466 13360241 := bstep (se 2 (by rfl) ⟨5010090, by rfl⟩ : syracuseStep 13360241 = 10020181) B10020181
theorem B1539187 : Blo 1538466 1539187 := bstep (se 1 (by rfl) ⟨1154390, by rfl⟩ : syracuseStep 1539187 = 2308781) B2308781
theorem B2309249 : Blo 1538466 2309249 := bstep (se 2 (by rfl) ⟨865968, by rfl⟩ : syracuseStep 2309249 = 1731937) B1731937
theorem B1539203 : Blo 1538466 1539203 := bstep (se 1 (by rfl) ⟨1154402, by rfl⟩ : syracuseStep 1539203 = 2308805) B2308805
theorem B1539219 : Blo 1538466 1539219 := bstep (se 1 (by rfl) ⟨1154414, by rfl⟩ : syracuseStep 1539219 = 2308829) B2308829
theorem B2309267 : Blo 1538466 2309267 := bstep (se 1 (by rfl) ⟨1731950, by rfl⟩ : syracuseStep 2309267 = 3463901) B3463901
theorem B1539235 : Blo 1538466 1539235 := bstep (se 1 (by rfl) ⟨1154426, by rfl⟩ : syracuseStep 1539235 = 2308853) B2308853
theorem B2309297 : Blo 1538466 2309297 := bstep (se 2 (by rfl) ⟨865986, by rfl⟩ : syracuseStep 2309297 = 1731973) B1731973
theorem B3464369 : Blo 1538466 3464369 := bstep (se 2 (by rfl) ⟨1299138, by rfl⟩ : syracuseStep 3464369 = 2598277) B2598277
theorem B1539251 : Blo 1538466 1539251 := bstep (se 1 (by rfl) ⟨1154438, by rfl⟩ : syracuseStep 1539251 = 2308877) B2308877
theorem B1539267 : Blo 1538466 1539267 := bstep (se 1 (by rfl) ⟨1154450, by rfl⟩ : syracuseStep 1539267 = 2308901) B2308901
theorem B2309315 : Blo 1538466 2309315 := bstep (se 1 (by rfl) ⟨1731986, by rfl⟩ : syracuseStep 2309315 = 3463973) B3463973
theorem B3464387 : Blo 1538466 3464387 := bstep (se 1 (by rfl) ⟨2598290, by rfl⟩ : syracuseStep 3464387 = 5196581) B5196581
theorem B5192909 : Blo 1538466 5192909 := bstep (se 3 (by rfl) ⟨973670, by rfl⟩ : syracuseStep 5192909 = 1947341) B1947341
theorem B1539283 : Blo 1538466 1539283 := bstep (se 1 (by rfl) ⟨1154462, by rfl⟩ : syracuseStep 1539283 = 2308925) B2308925
theorem B2309345 : Blo 1538466 2309345 := bstep (se 2 (by rfl) ⟨866004, by rfl⟩ : syracuseStep 2309345 = 1732009) B1732009
theorem B1539299 : Blo 1538466 1539299 := bstep (se 1 (by rfl) ⟨1154474, by rfl⟩ : syracuseStep 1539299 = 2308949) B2308949
theorem B44989667 : Blo 1538466 44989667 := bstep (se 1 (by rfl) ⟨33742250, by rfl⟩ : syracuseStep 44989667 = 67484501) B67484501
theorem B1539315 : Blo 1538466 1539315 := bstep (se 1 (by rfl) ⟨1154486, by rfl⟩ : syracuseStep 1539315 = 2308973) B2308973
theorem B2309363 : Blo 1538466 2309363 := bstep (se 1 (by rfl) ⟨1732022, by rfl⟩ : syracuseStep 2309363 = 3464045) B3464045
theorem B5192963 : Blo 1538466 5192963 := bstep (se 1 (by rfl) ⟨3894722, by rfl⟩ : syracuseStep 5192963 = 7789445) B7789445
theorem B1539331 : Blo 1538466 1539331 := bstep (se 1 (by rfl) ⟨1154498, by rfl⟩ : syracuseStep 1539331 = 2308997) B2308997
theorem B2309393 : Blo 1538466 2309393 := bstep (se 2 (by rfl) ⟨866022, by rfl⟩ : syracuseStep 2309393 = 1732045) B1732045
theorem B1539347 : Blo 1538466 1539347 := bstep (se 1 (by rfl) ⟨1154510, by rfl⟩ : syracuseStep 1539347 = 2309021) B2309021
theorem B1539363 : Blo 1538466 1539363 := bstep (se 1 (by rfl) ⟨1154522, by rfl⟩ : syracuseStep 1539363 = 2309045) B2309045
theorem B2309411 : Blo 1538466 2309411 := bstep (se 1 (by rfl) ⟨1732058, by rfl⟩ : syracuseStep 2309411 = 3464117) B3464117
theorem B1539379 : Blo 1538466 1539379 := bstep (se 1 (by rfl) ⟨1154534, by rfl⟩ : syracuseStep 1539379 = 2309069) B2309069
theorem B2309441 : Blo 1538466 2309441 := bstep (se 2 (by rfl) ⟨866040, by rfl⟩ : syracuseStep 2309441 = 1732081) B1732081
theorem B1539395 : Blo 1538466 1539395 := bstep (se 1 (by rfl) ⟨1154546, by rfl⟩ : syracuseStep 1539395 = 2309093) B2309093
theorem B19717445 : Blo 1538466 19717445 := bstep (se 4 (by rfl) ⟨1848510, by rfl⟩ : syracuseStep 19717445 = 3697021) B3697021
theorem B11091269 : Blo 1538466 11091269 := bstep (se 4 (by rfl) ⟨1039806, by rfl⟩ : syracuseStep 11091269 = 2079613) B2079613
theorem B1539411 : Blo 1538466 1539411 := bstep (se 1 (by rfl) ⟨1154558, by rfl⟩ : syracuseStep 1539411 = 2309117) B2309117
theorem B2309459 : Blo 1538466 2309459 := bstep (se 1 (by rfl) ⟨1732094, by rfl⟩ : syracuseStep 2309459 = 3464189) B3464189
theorem B1539427 : Blo 1538466 1539427 := bstep (se 1 (by rfl) ⟨1154570, by rfl⟩ : syracuseStep 1539427 = 2309141) B2309141
theorem B2309489 : Blo 1538466 2309489 := bstep (se 2 (by rfl) ⟨866058, by rfl⟩ : syracuseStep 2309489 = 1732117) B1732117
theorem B1539443 : Blo 1538466 1539443 := bstep (se 1 (by rfl) ⟨1154582, by rfl⟩ : syracuseStep 1539443 = 2309165) B2309165
theorem B2596225 : Blo 1538466 2596225 := bstep (se 2 (by rfl) ⟨973584, by rfl⟩ : syracuseStep 2596225 = 1947169) B1947169
theorem B1539459 : Blo 1538466 1539459 := bstep (se 1 (by rfl) ⟨1154594, by rfl⟩ : syracuseStep 1539459 = 2309189) B2309189
theorem B2309507 : Blo 1538466 2309507 := bstep (se 1 (by rfl) ⟨1732130, by rfl⟩ : syracuseStep 2309507 = 3464261) B3464261
theorem B1539475 : Blo 1538466 1539475 := bstep (se 1 (by rfl) ⟨1154606, by rfl⟩ : syracuseStep 1539475 = 2309213) B2309213
theorem B2309537 : Blo 1538466 2309537 := bstep (se 2 (by rfl) ⟨866076, by rfl⟩ : syracuseStep 2309537 = 1732153) B1732153
theorem B2596259 : Blo 1538466 2596259 := bstep (se 1 (by rfl) ⟨1947194, by rfl⟩ : syracuseStep 2596259 = 3894389) B3894389
theorem B1539491 : Blo 1538466 1539491 := bstep (se 1 (by rfl) ⟨1154618, by rfl⟩ : syracuseStep 1539491 = 2309237) B2309237
theorem B1539507 : Blo 1538466 1539507 := bstep (se 1 (by rfl) ⟨1154630, by rfl⟩ : syracuseStep 1539507 = 2309261) B2309261
theorem B2309555 : Blo 1538466 2309555 := bstep (se 1 (by rfl) ⟨1732166, by rfl⟩ : syracuseStep 2309555 = 3464333) B3464333
theorem B1539523 : Blo 1538466 1539523 := bstep (se 1 (by rfl) ⟨1154642, by rfl⟩ : syracuseStep 1539523 = 2309285) B2309285
theorem B2309585 : Blo 1538466 2309585 := bstep (se 2 (by rfl) ⟨866094, by rfl⟩ : syracuseStep 2309585 = 1732189) B1732189
theorem B3464657 : Blo 1538466 3464657 := bstep (se 2 (by rfl) ⟨1299246, by rfl⟩ : syracuseStep 3464657 = 2598493) B2598493
theorem B1539539 : Blo 1538466 1539539 := bstep (se 1 (by rfl) ⟨1154654, by rfl⟩ : syracuseStep 1539539 = 2309309) B2309309
theorem B1539555 : Blo 1538466 1539555 := bstep (se 1 (by rfl) ⟨1154666, by rfl⟩ : syracuseStep 1539555 = 2309333) B2309333
theorem B2309603 : Blo 1538466 2309603 := bstep (se 1 (by rfl) ⟨1732202, by rfl⟩ : syracuseStep 2309603 = 3464405) B3464405
theorem B3464675 : Blo 1538466 3464675 := bstep (se 1 (by rfl) ⟨2598506, by rfl⟩ : syracuseStep 3464675 = 5197013) B5197013
theorem B1539571 : Blo 1538466 1539571 := bstep (se 1 (by rfl) ⟨1154678, by rfl⟩ : syracuseStep 1539571 = 2309357) B2309357
theorem B2309633 : Blo 1538466 2309633 := bstep (se 2 (by rfl) ⟨866112, by rfl⟩ : syracuseStep 2309633 = 1732225) B1732225
theorem B1539587 : Blo 1538466 1539587 := bstep (se 1 (by rfl) ⟨1154690, by rfl⟩ : syracuseStep 1539587 = 2309381) B2309381
theorem B7790093 : Blo 1538466 7790093 := bstep (se 3 (by rfl) ⟨1460642, by rfl⟩ : syracuseStep 7790093 = 2921285) B2921285
theorem B5193233 : Blo 1538466 5193233 := bstep (se 2 (by rfl) ⟨1947462, by rfl⟩ : syracuseStep 5193233 = 3894925) B3894925
theorem B4382225 : Blo 1538466 4382225 := bstep (se 2 (by rfl) ⟨1643334, by rfl⟩ : syracuseStep 4382225 = 3286669) B3286669
theorem B1539603 : Blo 1538466 1539603 := bstep (se 1 (by rfl) ⟨1154702, by rfl⟩ : syracuseStep 1539603 = 2309405) B2309405
theorem B2309651 : Blo 1538466 2309651 := bstep (se 1 (by rfl) ⟨1732238, by rfl⟩ : syracuseStep 2309651 = 3464477) B3464477
theorem B2596387 : Blo 1538466 2596387 := bstep (se 1 (by rfl) ⟨1947290, by rfl⟩ : syracuseStep 2596387 = 3894581) B3894581
theorem B1539619 : Blo 1538466 1539619 := bstep (se 1 (by rfl) ⟨1154714, by rfl⟩ : syracuseStep 1539619 = 2309429) B2309429
theorem B2309681 : Blo 1538466 2309681 := bstep (se 2 (by rfl) ⟨866130, by rfl⟩ : syracuseStep 2309681 = 1732261) B1732261
theorem B1539635 : Blo 1538466 1539635 := bstep (se 1 (by rfl) ⟨1154726, by rfl⟩ : syracuseStep 1539635 = 2309453) B2309453
theorem B1539651 : Blo 1538466 1539651 := bstep (se 1 (by rfl) ⟨1154738, by rfl⟩ : syracuseStep 1539651 = 2309477) B2309477
theorem B2309699 : Blo 1538466 2309699 := bstep (se 1 (by rfl) ⟨1732274, by rfl⟩ : syracuseStep 2309699 = 3464549) B3464549
theorem B1539667 : Blo 1538466 1539667 := bstep (se 1 (by rfl) ⟨1154750, by rfl⟩ : syracuseStep 1539667 = 2309501) B2309501
theorem B2309729 : Blo 1538466 2309729 := bstep (se 2 (by rfl) ⟨866148, by rfl⟩ : syracuseStep 2309729 = 1732297) B1732297
theorem B1539683 : Blo 1538466 1539683 := bstep (se 1 (by rfl) ⟨1154762, by rfl⟩ : syracuseStep 1539683 = 2309525) B2309525
theorem B1539699 : Blo 1538466 1539699 := bstep (se 1 (by rfl) ⟨1154774, by rfl⟩ : syracuseStep 1539699 = 2309549) B2309549
theorem B2309747 : Blo 1538466 2309747 := bstep (se 1 (by rfl) ⟨1732310, by rfl⟩ : syracuseStep 2309747 = 3464621) B3464621
theorem B1539715 : Blo 1538466 1539715 := bstep (se 1 (by rfl) ⟨1154786, by rfl⟩ : syracuseStep 1539715 = 2309573) B2309573
theorem B2309777 : Blo 1538466 2309777 := bstep (se 2 (by rfl) ⟨866166, by rfl⟩ : syracuseStep 2309777 = 1732333) B1732333
theorem B1539731 : Blo 1538466 1539731 := bstep (se 1 (by rfl) ⟨1154798, by rfl⟩ : syracuseStep 1539731 = 2309597) B2309597
theorem B1539747 : Blo 1538466 1539747 := bstep (se 1 (by rfl) ⟨1154810, by rfl⟩ : syracuseStep 1539747 = 2309621) B2309621
theorem B2309795 : Blo 1538466 2309795 := bstep (se 1 (by rfl) ⟨1732346, by rfl⟩ : syracuseStep 2309795 = 3464693) B3464693
theorem B2596529 : Blo 1538466 2596529 := bstep (se 2 (by rfl) ⟨973698, by rfl⟩ : syracuseStep 2596529 = 1947397) B1947397
theorem B1539763 : Blo 1538466 1539763 := bstep (se 1 (by rfl) ⟨1154822, by rfl⟩ : syracuseStep 1539763 = 2309645) B2309645
theorem B2309825 : Blo 1538466 2309825 := bstep (se 2 (by rfl) ⟨866184, by rfl⟩ : syracuseStep 2309825 = 1732369) B1732369
theorem B1539779 : Blo 1538466 1539779 := bstep (se 1 (by rfl) ⟨1154834, by rfl⟩ : syracuseStep 1539779 = 2309669) B2309669
theorem B1539795 : Blo 1538466 1539795 := bstep (se 1 (by rfl) ⟨1154846, by rfl⟩ : syracuseStep 1539795 = 2309693) B2309693
theorem B2309843 : Blo 1538466 2309843 := bstep (se 1 (by rfl) ⟨1732382, by rfl⟩ : syracuseStep 2309843 = 3464765) B3464765
theorem B1539811 : Blo 1538466 1539811 := bstep (se 1 (by rfl) ⟨1154858, by rfl⟩ : syracuseStep 1539811 = 2309717) B2309717
theorem B2309873 : Blo 1538466 2309873 := bstep (se 2 (by rfl) ⟨866202, by rfl⟩ : syracuseStep 2309873 = 1732405) B1732405
theorem B1539827 : Blo 1538466 1539827 := bstep (se 1 (by rfl) ⟨1154870, by rfl⟩ : syracuseStep 1539827 = 2309741) B2309741
theorem B1539843 : Blo 1538466 1539843 := bstep (se 1 (by rfl) ⟨1154882, by rfl⟩ : syracuseStep 1539843 = 2309765) B2309765
theorem B2309891 : Blo 1538466 2309891 := bstep (se 1 (by rfl) ⟨1732418, by rfl⟩ : syracuseStep 2309891 = 3464837) B3464837
theorem B1539859 : Blo 1538466 1539859 := bstep (se 1 (by rfl) ⟨1154894, by rfl⟩ : syracuseStep 1539859 = 2309789) B2309789
theorem B2309921 : Blo 1538466 2309921 := bstep (se 2 (by rfl) ⟨866220, by rfl⟩ : syracuseStep 2309921 = 1732441) B1732441
theorem B5545763 : Blo 1538466 5545763 := bstep (se 1 (by rfl) ⟨4159322, by rfl⟩ : syracuseStep 5545763 = 8318645) B8318645
theorem B1539875 : Blo 1538466 1539875 := bstep (se 1 (by rfl) ⟨1154906, by rfl⟩ : syracuseStep 1539875 = 2309813) B2309813
theorem B2596657 : Blo 1538466 2596657 := bstep (se 2 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 2596657 = 1947493) B1947493
theorem B1539891 : Blo 1538466 1539891 := bstep (se 1 (by rfl) ⟨1154918, by rfl⟩ : syracuseStep 1539891 = 2309837) B2309837
theorem B2309939 : Blo 1538466 2309939 := bstep (se 1 (by rfl) ⟨1732454, by rfl⟩ : syracuseStep 2309939 = 3464909) B3464909
theorem B3948355 : Blo 1538466 3948355 := bstep (se 1 (by rfl) ⟨2961266, by rfl⟩ : syracuseStep 3948355 = 5922533) B5922533
theorem B1539907 : Blo 1538466 1539907 := bstep (se 1 (by rfl) ⟨1154930, by rfl⟩ : syracuseStep 1539907 = 2309861) B2309861
theorem B2596691 : Blo 1538466 2596691 := bstep (se 1 (by rfl) ⟨1947518, by rfl⟩ : syracuseStep 2596691 = 3895037) B3895037
theorem B1539923 : Blo 1538466 1539923 := bstep (se 1 (by rfl) ⟨1154942, by rfl⟩ : syracuseStep 1539923 = 2309885) B2309885
theorem B1539939 : Blo 1538466 1539939 := bstep (se 1 (by rfl) ⟨1154954, by rfl⟩ : syracuseStep 1539939 = 2309909) B2309909
theorem B1539955 : Blo 1538466 1539955 := bstep (se 1 (by rfl) ⟨1154966, by rfl⟩ : syracuseStep 1539955 = 2309933) B2309933
theorem B101253005 : Blo 1538466 101253005 := bstep (se 3 (by rfl) ⟨18984938, by rfl⟩ : syracuseStep 101253005 = 37969877) B37969877
theorem B10534853 : Blo 1538466 10534853 := bstep (se 4 (by rfl) ⟨987642, by rfl⟩ : syracuseStep 10534853 = 1975285) B1975285
theorem B2596819 : Blo 1538466 2596819 := bstep (se 1 (by rfl) ⟨1947614, by rfl⟩ : syracuseStep 2596819 = 3895229) B3895229
theorem B22487053 : Blo 1538466 22487053 := bstep (se 3 (by rfl) ⟨4216322, by rfl⟩ : syracuseStep 22487053 = 8432645) B8432645
theorem B2597015 : Blo 1538466 2597015 := bstep (se 1 (by rfl) ⟨1947761, by rfl⟩ : syracuseStep 2597015 = 3895523) B3895523
theorem B8765657 : Blo 1538466 8765657 := bstep (se 2 (by rfl) ⟨3287121, by rfl⟩ : syracuseStep 8765657 = 6574243) B6574243
theorem B2597143 : Blo 1538466 2597143 := bstep (se 1 (by rfl) ⟨1947857, by rfl⟩ : syracuseStep 2597143 = 3895715) B3895715
theorem B35627309 : Blo 1538466 35627309 := bstep (se 3 (by rfl) ⟨6680120, by rfl⟩ : syracuseStep 35627309 = 13360241) B13360241
theorem B4161995 : Blo 1538466 4161995 := bstep (se 1 (by rfl) ⟨3121496, by rfl⟩ : syracuseStep 4161995 = 6242993) B6242993
theorem B7791065 : Blo 1538466 7791065 := bstep (se 2 (by rfl) ⟨2921649, by rfl⟩ : syracuseStep 7791065 = 5843299) B5843299
theorem B4383193 : Blo 1538466 4383193 := bstep (se 2 (by rfl) ⟨1643697, by rfl⟩ : syracuseStep 4383193 = 3287395) B3287395
theorem B5194205 : Blo 1538466 5194205 := bstep (se 3 (by rfl) ⟨973913, by rfl⟩ : syracuseStep 5194205 = 1947827) B1947827
theorem B13173349 : Blo 1538466 13173349 := bstep (se 4 (by rfl) ⟨1235001, by rfl⟩ : syracuseStep 13173349 = 2470003) B2470003
theorem B17777303 : Blo 1538466 17777303 := bstep (se 1 (by rfl) ⟨13332977, by rfl⟩ : syracuseStep 17777303 = 26665955) B26665955
theorem B2466521 : Blo 1538466 2466521 := bstep (se 2 (by rfl) ⟨924945, by rfl⟩ : syracuseStep 2466521 = 1849891) B1849891
theorem B5841629 : Blo 1538466 5841629 := bstep (se 3 (by rfl) ⟨1095305, by rfl⟩ : syracuseStep 5841629 = 2190611) B2190611
theorem B2597771 : Blo 1538466 2597771 := bstep (se 1 (by rfl) ⟨1948328, by rfl⟩ : syracuseStep 2597771 = 3896657) B3896657
theorem B6243331 : Blo 1538466 6243331 := bstep (se 1 (by rfl) ⟨4682498, by rfl⟩ : syracuseStep 6243331 = 9364997) B9364997
theorem B2597899 : Blo 1538466 2597899 := bstep (se 1 (by rfl) ⟨1948424, by rfl⟩ : syracuseStep 2597899 = 3896849) B3896849
theorem B2598041 : Blo 1538466 2598041 := bstep (se 2 (by rfl) ⟨974265, by rfl⟩ : syracuseStep 2598041 = 1948531) B1948531
theorem B76948661 : Blo 1538466 76948661 := bstep (se 5 (by rfl) ⟨3606968, by rfl⟩ : syracuseStep 76948661 = 7213937) B7213937
theorem B2598169 : Blo 1538466 2598169 := bstep (se 2 (by rfl) ⟨974313, by rfl⟩ : syracuseStep 2598169 = 1948627) B1948627
theorem B5842327 : Blo 1538466 5842327 := bstep (se 1 (by rfl) ⟨4381745, by rfl⟩ : syracuseStep 5842327 = 8763491) B8763491
theorem B1754551 : Blo 1538466 1754551 := bstep (se 1 (by rfl) ⟨1315913, by rfl⟩ : syracuseStep 1754551 = 2631827) B2631827
theorem B5547523 : Blo 1538466 5547523 := bstep (se 1 (by rfl) ⟨4160642, by rfl⟩ : syracuseStep 5547523 = 8321285) B8321285
theorem B5195339 : Blo 1538466 5195339 := bstep (se 1 (by rfl) ⟨3896504, by rfl⟩ : syracuseStep 5195339 = 7793009) B7793009
theorem B6571799 : Blo 1538466 6571799 := bstep (se 1 (by rfl) ⟨4928849, by rfl⟩ : syracuseStep 6571799 = 9857699) B9857699
theorem B7022359 : Blo 1538466 7022359 := bstep (se 1 (by rfl) ⟨5266769, by rfl⟩ : syracuseStep 7022359 = 10533539) B10533539
theorem B5547827 : Blo 1538466 5547827 := bstep (se 1 (by rfl) ⟨4160870, by rfl⟩ : syracuseStep 5547827 = 8321741) B8321741
theorem B5195609 : Blo 1538466 5195609 := bstep (se 2 (by rfl) ⟨1948353, by rfl⟩ : syracuseStep 5195609 = 3896707) B3896707
theorem B3287027 : Blo 1538466 3287027 := bstep (se 1 (by rfl) ⟨2465270, by rfl⟩ : syracuseStep 3287027 = 4930541) B4930541
theorem B7792685 : Blo 1538466 7792685 := bstep (se 3 (by rfl) ⟨1461128, by rfl⟩ : syracuseStep 7792685 = 2922257) B2922257
theorem B4442177 : Blo 1538466 4442177 := bstep (se 2 (by rfl) ⟨1665816, by rfl⟩ : syracuseStep 4442177 = 3331633) B3331633
theorem B29993111 : Blo 1538466 29993111 := bstep (se 1 (by rfl) ⟨22494833, by rfl⟩ : syracuseStep 29993111 = 44989667) B44989667
theorem B5843117 : Blo 1538466 5843117 := bstep (se 3 (by rfl) ⟨1095584, by rfl⟩ : syracuseStep 5843117 = 2191169) B2191169
theorem B9865489 : Blo 1538466 9865489 := bstep (se 2 (by rfl) ⟨3699558, by rfl⟩ : syracuseStep 9865489 = 7399117) B7399117
theorem B1730839 : Blo 1538466 1730839 := bstep (se 1 (by rfl) ⟨1298129, by rfl⟩ : syracuseStep 1730839 = 2596259) B2596259
theorem B4385117 : Blo 1538466 4385117 := bstep (se 3 (by rfl) ⟨822209, by rfl⟩ : syracuseStep 4385117 = 1644419) B1644419
theorem B1731019 : Blo 1538466 1731019 := bstep (se 1 (by rfl) ⟨1298264, by rfl⟩ : syracuseStep 1731019 = 2596529) B2596529
theorem B3697175 : Blo 1538466 3697175 := bstep (se 1 (by rfl) ⟨2772881, by rfl⟩ : syracuseStep 3697175 = 5545763) B5545763
theorem B5196311 : Blo 1538466 5196311 := bstep (se 1 (by rfl) ⟨3897233, by rfl⟩ : syracuseStep 5196311 = 7794467) B7794467
theorem B1731127 : Blo 1538466 1731127 := bstep (se 1 (by rfl) ⟨1298345, by rfl⟩ : syracuseStep 1731127 = 2596691) B2596691
theorem B7023235 : Blo 1538466 7023235 := bstep (se 1 (by rfl) ⟨5267426, by rfl⟩ : syracuseStep 7023235 = 10534853) B10534853
theorem B1731307 : Blo 1538466 1731307 := bstep (se 1 (by rfl) ⟨1298480, by rfl⟩ : syracuseStep 1731307 = 2596961) B2596961
theorem B170797889 : Blo 1538466 170797889 := bstep (se 2 (by rfl) ⟨64049208, by rfl⟩ : syracuseStep 170797889 = 128098417) B128098417
theorem B8768321 : Blo 1538466 8768321 := bstep (se 2 (by rfl) ⟨3288120, by rfl⟩ : syracuseStep 8768321 = 6576241) B6576241
theorem B3697483 : Blo 1538466 3697483 := bstep (se 1 (by rfl) ⟨2773112, by rfl⟩ : syracuseStep 3697483 = 5546225) B5546225
theorem B1731415 : Blo 1538466 1731415 := bstep (se 1 (by rfl) ⟨1298561, by rfl⟩ : syracuseStep 1731415 = 2597123) B2597123
theorem B22195043 : Blo 1538466 22195043 := bstep (se 1 (by rfl) ⟨16646282, by rfl⟩ : syracuseStep 22195043 = 33292565) B33292565
theorem B284322757 : Blo 1538466 284322757 := bstep (se 4 (by rfl) ⟨26655258, by rfl⟩ : syracuseStep 284322757 = 53310517) B53310517
theorem B1731595 : Blo 1538466 1731595 := bstep (se 1 (by rfl) ⟨1298696, by rfl⟩ : syracuseStep 1731595 = 2597393) B2597393
theorem B5196851 : Blo 1538466 5196851 := bstep (se 1 (by rfl) ⟨3897638, by rfl⟩ : syracuseStep 5196851 = 7795277) B7795277
theorem B1731703 : Blo 1538466 1731703 := bstep (se 1 (by rfl) ⟨1298777, by rfl⟩ : syracuseStep 1731703 = 2597555) B2597555
theorem B1625239 : Blo 1538466 1625239 := bstep (se 1 (by rfl) ⟨1218929, by rfl⟩ : syracuseStep 1625239 = 2437859) B2437859
theorem B3288215 : Blo 1538466 3288215 := bstep (se 1 (by rfl) ⟨2466161, by rfl⟩ : syracuseStep 3288215 = 4932323) B4932323
theorem B11095217 : Blo 1538466 11095217 := bstep (se 2 (by rfl) ⟨4160706, by rfl⟩ : syracuseStep 11095217 = 8321413) B8321413
theorem B3894551 : Blo 1538466 3894551 := bstep (se 1 (by rfl) ⟨2920913, by rfl⟩ : syracuseStep 3894551 = 5841827) B5841827
theorem B1731883 : Blo 1538466 1731883 := bstep (se 1 (by rfl) ⟨1298912, by rfl⟩ : syracuseStep 1731883 = 2597825) B2597825
theorem B5197121 : Blo 1538466 5197121 := bstep (se 2 (by rfl) ⟨1948920, by rfl⟩ : syracuseStep 5197121 = 3897841) B3897841
theorem B1731991 : Blo 1538466 1731991 := bstep (se 1 (by rfl) ⟨1298993, by rfl⟩ : syracuseStep 1731991 = 2597987) B2597987
theorem B3698099 : Blo 1538466 3698099 := bstep (se 1 (by rfl) ⟨2773574, by rfl⟩ : syracuseStep 3698099 = 5547149) B5547149
theorem B9358865 : Blo 1538466 9358865 := bstep (se 2 (by rfl) ⟨3509574, by rfl⟩ : syracuseStep 9358865 = 7019149) B7019149
theorem B26668561 : Blo 1538466 26668561 := bstep (se 2 (by rfl) ⟨10000710, by rfl⟩ : syracuseStep 26668561 = 20001421) B20001421
theorem B5844545 : Blo 1538466 5844545 := bstep (se 2 (by rfl) ⟨2191704, by rfl⟩ : syracuseStep 5844545 = 4383409) B4383409
theorem B1732171 : Blo 1538466 1732171 := bstep (se 1 (by rfl) ⟨1299128, by rfl⟩ : syracuseStep 1732171 = 2598257) B2598257
theorem B1732279 : Blo 1538466 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B1560395 : Blo 1538466 1560395 := bstep (se 1 (by rfl) ⟨1170296, by rfl⟩ : syracuseStep 1560395 = 2340593) B2340593
theorem B1732459 : Blo 1538466 1732459 := bstep (se 1 (by rfl) ⟨1299344, by rfl⟩ : syracuseStep 1732459 = 2598689) B2598689
theorem B3895361 : Blo 1538466 3895361 := bstep (se 2 (by rfl) ⟨1460760, by rfl⟩ : syracuseStep 3895361 = 2921521) B2921521
theorem B6574259 : Blo 1538466 6574259 := bstep (se 1 (by rfl) ⟨4930694, by rfl⟩ : syracuseStep 6574259 = 9861389) B9861389
theorem B3698867 : Blo 1538466 3698867 := bstep (se 1 (by rfl) ⟨2774150, by rfl⟩ : syracuseStep 3698867 = 5548301) B5548301
theorem B25293005 : Blo 1538466 25293005 := bstep (se 3 (by rfl) ⟨4742438, by rfl⟩ : syracuseStep 25293005 = 9484877) B9484877
theorem B2920769 : Blo 1538466 2920769 := bstep (se 2 (by rfl) ⟨1095288, by rfl⟩ : syracuseStep 2920769 = 2190577) B2190577
theorem B21057893 : Blo 1538466 21057893 := bstep (se 4 (by rfl) ⟨1974177, by rfl⟩ : syracuseStep 21057893 = 3948355) B3948355
theorem B3461579 : Blo 1538466 3461579 := bstep (se 1 (by rfl) ⟨2596184, by rfl⟩ : syracuseStep 3461579 = 5192369) B5192369
theorem B3461633 : Blo 1538466 3461633 := bstep (se 2 (by rfl) ⟨1298112, by rfl⟩ : syracuseStep 3461633 = 2596225) B2596225
theorem B2921035 : Blo 1538466 2921035 := bstep (se 1 (by rfl) ⟨2190776, by rfl⟩ : syracuseStep 2921035 = 4381553) B4381553
theorem B1643095 : Blo 1538466 1643095 := bstep (se 1 (by rfl) ⟨1232321, by rfl⟩ : syracuseStep 1643095 = 2464643) B2464643
theorem B3895897 : Blo 1538466 3895897 := bstep (se 2 (by rfl) ⟨1460961, by rfl⟩ : syracuseStep 3895897 = 2921923) B2921923
theorem B2191961 : Blo 1538466 2191961 := bstep (se 2 (by rfl) ⟨821985, by rfl⟩ : syracuseStep 2191961 = 1643971) B1643971
theorem B3461849 : Blo 1538466 3461849 := bstep (se 2 (by rfl) ⟨1298193, by rfl⟩ : syracuseStep 3461849 = 2596387) B2596387
theorem B6664925 : Blo 1538466 6664925 := bstep (se 3 (by rfl) ⟨1249673, by rfl⟩ : syracuseStep 6664925 = 2499347) B2499347
theorem B3461939 : Blo 1538466 3461939 := bstep (se 1 (by rfl) ⟨2596454, by rfl⟩ : syracuseStep 3461939 = 5192909) B5192909
theorem B6239051 : Blo 1538466 6239051 := bstep (se 1 (by rfl) ⟨4679288, by rfl⟩ : syracuseStep 6239051 = 9358577) B9358577
theorem B3461975 : Blo 1538466 3461975 := bstep (se 1 (by rfl) ⟨2596481, by rfl⟩ : syracuseStep 3461975 = 5192963) B5192963
theorem B13144963 : Blo 1538466 13144963 := bstep (se 1 (by rfl) ⟨9858722, by rfl⟩ : syracuseStep 13144963 = 19717445) B19717445
theorem B7394179 : Blo 1538466 7394179 := bstep (se 1 (by rfl) ⟨5545634, by rfl⟩ : syracuseStep 7394179 = 11091269) B11091269
theorem B3462155 : Blo 1538466 3462155 := bstep (se 1 (by rfl) ⟨2596616, by rfl⟩ : syracuseStep 3462155 = 5193233) B5193233
theorem B2921483 : Blo 1538466 2921483 := bstep (se 1 (by rfl) ⟨2191112, by rfl⟩ : syracuseStep 2921483 = 4382225) B4382225
theorem B5846033 : Blo 1538466 5846033 := bstep (se 2 (by rfl) ⟨2192262, by rfl⟩ : syracuseStep 5846033 = 4384525) B4384525
theorem B3462209 : Blo 1538466 3462209 := bstep (se 2 (by rfl) ⟨1298328, by rfl⟩ : syracuseStep 3462209 = 2596657) B2596657
theorem B2921665 : Blo 1538466 2921665 := bstep (se 2 (by rfl) ⟨1095624, by rfl⟩ : syracuseStep 2921665 = 2191249) B2191249
theorem B2192599 : Blo 1538466 2192599 := bstep (se 1 (by rfl) ⟨1644449, by rfl⟩ : syracuseStep 2192599 = 3288899) B3288899
theorem B3462425 : Blo 1538466 3462425 := bstep (se 2 (by rfl) ⟨1298409, by rfl⟩ : syracuseStep 3462425 = 2596819) B2596819
theorem B3462515 : Blo 1538466 3462515 := bstep (se 1 (by rfl) ⟨2596886, by rfl⟩ : syracuseStep 3462515 = 5193773) B5193773
theorem B3462551 : Blo 1538466 3462551 := bstep (se 1 (by rfl) ⟨2596913, by rfl⟩ : syracuseStep 3462551 = 5193827) B5193827
theorem B5846489 : Blo 1538466 5846489 := bstep (se 2 (by rfl) ⟨2192433, by rfl⟩ : syracuseStep 5846489 = 4384867) B4384867
theorem B2922007 : Blo 1538466 2922007 := bstep (se 1 (by rfl) ⟨2191505, by rfl⟩ : syracuseStep 2922007 = 4383011) B4383011
theorem B3462731 : Blo 1538466 3462731 := bstep (se 1 (by rfl) ⟨2597048, by rfl⟩ : syracuseStep 3462731 = 5194097) B5194097
theorem B3462785 : Blo 1538466 3462785 := bstep (se 2 (by rfl) ⟨1298544, by rfl⟩ : syracuseStep 3462785 = 2597089) B2597089
theorem B2963083 : Blo 1538466 2963083 := bstep (se 1 (by rfl) ⟨2222312, by rfl⟩ : syracuseStep 2963083 = 4444625) B4444625
theorem B10671767 : Blo 1538466 10671767 := bstep (se 1 (by rfl) ⟨8003825, by rfl⟩ : syracuseStep 10671767 = 16007651) B16007651
theorem B2307737 : Blo 1538466 2307737 := bstep (se 2 (by rfl) ⟨865401, by rfl⟩ : syracuseStep 2307737 = 1730803) B1730803
theorem B5846701 : Blo 1538466 5846701 := bstep (se 3 (by rfl) ⟨1096256, by rfl⟩ : syracuseStep 5846701 = 2192513) B2192513
theorem B3897011 : Blo 1538466 3897011 := bstep (se 1 (by rfl) ⟨2922758, by rfl⟩ : syracuseStep 3897011 = 5845517) B5845517
theorem B2922227 : Blo 1538466 2922227 := bstep (se 1 (by rfl) ⟨2191670, by rfl⟩ : syracuseStep 2922227 = 4383341) B4383341
theorem B2307851 : Blo 1538466 2307851 := bstep (se 1 (by rfl) ⟨1730888, by rfl⟩ : syracuseStep 2307851 = 3461777) B3461777
theorem B2307863 : Blo 1538466 2307863 := bstep (se 1 (by rfl) ⟨1730897, by rfl⟩ : syracuseStep 2307863 = 3461795) B3461795
theorem B6240023 : Blo 1538466 6240023 := bstep (se 1 (by rfl) ⟨4680017, by rfl⟩ : syracuseStep 6240023 = 9360035) B9360035
theorem B13145921 : Blo 1538466 13145921 := bstep (se 2 (by rfl) ⟨4929720, by rfl⟩ : syracuseStep 13145921 = 9859441) B9859441
theorem B2307929 : Blo 1538466 2307929 := bstep (se 2 (by rfl) ⟨865473, by rfl⟩ : syracuseStep 2307929 = 1730947) B1730947
theorem B3463001 : Blo 1538466 3463001 := bstep (se 2 (by rfl) ⟨1298625, by rfl⟩ : syracuseStep 3463001 = 2597251) B2597251
theorem B3463091 : Blo 1538466 3463091 := bstep (se 1 (by rfl) ⟨2597318, by rfl⟩ : syracuseStep 3463091 = 5194637) B5194637
theorem B2308043 : Blo 1538466 2308043 := bstep (se 1 (by rfl) ⟨1731032, by rfl⟩ : syracuseStep 2308043 = 3462065) B3462065
theorem B2308055 : Blo 1538466 2308055 := bstep (se 1 (by rfl) ⟨1731041, by rfl⟩ : syracuseStep 2308055 = 3462083) B3462083
theorem B3463127 : Blo 1538466 3463127 := bstep (se 1 (by rfl) ⟨2597345, by rfl⟩ : syracuseStep 3463127 = 5194691) B5194691
theorem B2922455 : Blo 1538466 2922455 := bstep (se 1 (by rfl) ⟨2191841, by rfl⟩ : syracuseStep 2922455 = 4383683) B4383683
theorem B3897305 : Blo 1538466 3897305 := bstep (se 2 (by rfl) ⟨1461489, by rfl⟩ : syracuseStep 3897305 = 2922979) B2922979
theorem B5847005 : Blo 1538466 5847005 := bstep (se 3 (by rfl) ⟨1096313, by rfl⟩ : syracuseStep 5847005 = 2192627) B2192627
theorem B2308121 : Blo 1538466 2308121 := bstep (se 2 (by rfl) ⟨865545, by rfl⟩ : syracuseStep 2308121 = 1731091) B1731091
theorem B6576173 : Blo 1538466 6576173 := bstep (se 3 (by rfl) ⟨1233032, by rfl⟩ : syracuseStep 6576173 = 2466065) B2466065
theorem B2308235 : Blo 1538466 2308235 := bstep (se 1 (by rfl) ⟨1731176, by rfl⟩ : syracuseStep 2308235 = 3462353) B3462353
theorem B3463307 : Blo 1538466 3463307 := bstep (se 1 (by rfl) ⟨2597480, by rfl⟩ : syracuseStep 3463307 = 5194961) B5194961
theorem B2308247 : Blo 1538466 2308247 := bstep (se 1 (by rfl) ⟨1731185, by rfl⟩ : syracuseStep 2308247 = 3462371) B3462371
theorem B3463361 : Blo 1538466 3463361 := bstep (se 2 (by rfl) ⟨1298760, by rfl⟩ : syracuseStep 3463361 = 2597521) B2597521
theorem B2308313 : Blo 1538466 2308313 := bstep (se 2 (by rfl) ⟨865617, by rfl⟩ : syracuseStep 2308313 = 1731235) B1731235
theorem B2922713 : Blo 1538466 2922713 := bstep (se 2 (by rfl) ⟨1096017, by rfl⟩ : syracuseStep 2922713 = 2192035) B2192035
theorem B89946389 : Blo 1538466 89946389 := bstep (se 6 (by rfl) ⟨2108118, by rfl⟩ : syracuseStep 89946389 = 4216237) B4216237
theorem B14793005 : Blo 1538466 14793005 := bstep (se 3 (by rfl) ⟨2773688, by rfl⟩ : syracuseStep 14793005 = 5547377) B5547377
theorem B2308427 : Blo 1538466 2308427 := bstep (se 1 (by rfl) ⟨1731320, by rfl⟩ : syracuseStep 2308427 = 3462641) B3462641
theorem B1947979 : Blo 1538466 1947979 := bstep (se 1 (by rfl) ⟨1460984, by rfl⟩ : syracuseStep 1947979 = 2921969) B2921969
theorem B2308439 : Blo 1538466 2308439 := bstep (se 1 (by rfl) ⟨1731329, by rfl⟩ : syracuseStep 2308439 = 3462659) B3462659
theorem B6576515 : Blo 1538466 6576515 := bstep (se 1 (by rfl) ⟨4932386, by rfl⟩ : syracuseStep 6576515 = 9864773) B9864773
theorem B2308505 : Blo 1538466 2308505 := bstep (se 2 (by rfl) ⟨865689, by rfl⟩ : syracuseStep 2308505 = 1731379) B1731379
theorem B3463577 : Blo 1538466 3463577 := bstep (se 2 (by rfl) ⟨1298841, by rfl⟩ : syracuseStep 3463577 = 2597683) B2597683
theorem B1538475 : Blo 1538466 1538475 := bstep (se 1 (by rfl) ⟨1153856, by rfl⟩ : syracuseStep 1538475 = 2307713) B2307713
theorem B1538487 : Blo 1538466 1538487 := bstep (se 1 (by rfl) ⟨1153865, by rfl⟩ : syracuseStep 1538487 = 2307731) B2307731
theorem B1538507 : Blo 1538466 1538507 := bstep (se 1 (by rfl) ⟨1153880, by rfl⟩ : syracuseStep 1538507 = 2307761) B2307761
theorem B1538519 : Blo 1538466 1538519 := bstep (se 1 (by rfl) ⟨1153889, by rfl⟩ : syracuseStep 1538519 = 2307779) B2307779
theorem B1538539 : Blo 1538466 1538539 := bstep (se 1 (by rfl) ⟨1153904, by rfl⟩ : syracuseStep 1538539 = 2307809) B2307809
theorem B3463667 : Blo 1538466 3463667 := bstep (se 1 (by rfl) ⟨2597750, by rfl⟩ : syracuseStep 3463667 = 5195501) B5195501
theorem B1538551 : Blo 1538466 1538551 := bstep (se 1 (by rfl) ⟨1153913, by rfl⟩ : syracuseStep 1538551 = 2307827) B2307827
theorem B1538571 : Blo 1538466 1538571 := bstep (se 1 (by rfl) ⟨1153928, by rfl⟩ : syracuseStep 1538571 = 2307857) B2307857
theorem B2308619 : Blo 1538466 2308619 := bstep (se 1 (by rfl) ⟨1731464, by rfl⟩ : syracuseStep 2308619 = 3462929) B3462929
theorem B1538583 : Blo 1538466 1538583 := bstep (se 1 (by rfl) ⟨1153937, by rfl⟩ : syracuseStep 1538583 = 2307875) B2307875
theorem B2308631 : Blo 1538466 2308631 := bstep (se 1 (by rfl) ⟨1731473, by rfl⟩ : syracuseStep 2308631 = 3462947) B3462947
theorem B3463703 : Blo 1538466 3463703 := bstep (se 1 (by rfl) ⟨2597777, by rfl⟩ : syracuseStep 3463703 = 5195555) B5195555
theorem B1538603 : Blo 1538466 1538603 := bstep (se 1 (by rfl) ⟨1153952, by rfl⟩ : syracuseStep 1538603 = 2307905) B2307905
theorem B1538615 : Blo 1538466 1538615 := bstep (se 1 (by rfl) ⟨1153961, by rfl⟩ : syracuseStep 1538615 = 2307923) B2307923
theorem B7789121 : Blo 1538466 7789121 := bstep (se 2 (by rfl) ⟨2920920, by rfl⟩ : syracuseStep 7789121 = 5841841) B5841841
theorem B1538635 : Blo 1538466 1538635 := bstep (se 1 (by rfl) ⟨1153976, by rfl⟩ : syracuseStep 1538635 = 2307953) B2307953
theorem B1538647 : Blo 1538466 1538647 := bstep (se 1 (by rfl) ⟨1153985, by rfl⟩ : syracuseStep 1538647 = 2307971) B2307971
theorem B2308697 : Blo 1538466 2308697 := bstep (se 2 (by rfl) ⟨865761, by rfl⟩ : syracuseStep 2308697 = 1731523) B1731523
theorem B1538667 : Blo 1538466 1538667 := bstep (se 1 (by rfl) ⟨1154000, by rfl⟩ : syracuseStep 1538667 = 2308001) B2308001
theorem B2923123 : Blo 1538466 2923123 := bstep (se 1 (by rfl) ⟨2192342, by rfl⟩ : syracuseStep 2923123 = 4384685) B4384685
theorem B1538679 : Blo 1538466 1538679 := bstep (se 1 (by rfl) ⟨1154009, by rfl⟩ : syracuseStep 1538679 = 2308019) B2308019
theorem B1538699 : Blo 1538466 1538699 := bstep (se 1 (by rfl) ⟨1154024, by rfl⟩ : syracuseStep 1538699 = 2308049) B2308049
theorem B1538711 : Blo 1538466 1538711 := bstep (se 1 (by rfl) ⟨1154033, by rfl⟩ : syracuseStep 1538711 = 2308067) B2308067
theorem B1538731 : Blo 1538466 1538731 := bstep (se 1 (by rfl) ⟨1154048, by rfl⟩ : syracuseStep 1538731 = 2308097) B2308097
theorem B1538743 : Blo 1538466 1538743 := bstep (se 1 (by rfl) ⟨1154057, by rfl⟩ : syracuseStep 1538743 = 2308115) B2308115
theorem B1538763 : Blo 1538466 1538763 := bstep (se 1 (by rfl) ⟨1154072, by rfl⟩ : syracuseStep 1538763 = 2308145) B2308145
theorem B2308811 : Blo 1538466 2308811 := bstep (se 1 (by rfl) ⟨1731608, by rfl⟩ : syracuseStep 2308811 = 3463217) B3463217
theorem B3463883 : Blo 1538466 3463883 := bstep (se 1 (by rfl) ⟨2597912, by rfl⟩ : syracuseStep 3463883 = 5195825) B5195825
theorem B1538775 : Blo 1538466 1538775 := bstep (se 1 (by rfl) ⟨1154081, by rfl⟩ : syracuseStep 1538775 = 2308163) B2308163
theorem B2308823 : Blo 1538466 2308823 := bstep (se 1 (by rfl) ⟨1731617, by rfl⟩ : syracuseStep 2308823 = 3463235) B3463235
theorem B3119833 : Blo 1538466 3119833 := bstep (se 2 (by rfl) ⟨1169937, by rfl⟩ : syracuseStep 3119833 = 2339875) B2339875
theorem B1538795 : Blo 1538466 1538795 := bstep (se 1 (by rfl) ⟨1154096, by rfl⟩ : syracuseStep 1538795 = 2308193) B2308193
theorem B1538807 : Blo 1538466 1538807 := bstep (se 1 (by rfl) ⟨1154105, by rfl⟩ : syracuseStep 1538807 = 2308211) B2308211
theorem B3463937 : Blo 1538466 3463937 := bstep (se 2 (by rfl) ⟨1298976, by rfl⟩ : syracuseStep 3463937 = 2597953) B2597953
theorem B1538827 : Blo 1538466 1538827 := bstep (se 1 (by rfl) ⟨1154120, by rfl⟩ : syracuseStep 1538827 = 2308241) B2308241
theorem B1538839 : Blo 1538466 1538839 := bstep (se 1 (by rfl) ⟨1154129, by rfl⟩ : syracuseStep 1538839 = 2308259) B2308259
theorem B2308889 : Blo 1538466 2308889 := bstep (se 2 (by rfl) ⟨865833, by rfl⟩ : syracuseStep 2308889 = 1731667) B1731667
theorem B1538859 : Blo 1538466 1538859 := bstep (se 1 (by rfl) ⟨1154144, by rfl⟩ : syracuseStep 1538859 = 2308289) B2308289
theorem B1538871 : Blo 1538466 1538871 := bstep (se 1 (by rfl) ⟨1154153, by rfl⟩ : syracuseStep 1538871 = 2308307) B2308307
theorem B1538891 : Blo 1538466 1538891 := bstep (se 1 (by rfl) ⟨1154168, by rfl⟩ : syracuseStep 1538891 = 2308337) B2308337
theorem B1538903 : Blo 1538466 1538903 := bstep (se 1 (by rfl) ⟨1154177, by rfl⟩ : syracuseStep 1538903 = 2308355) B2308355
theorem B1538923 : Blo 1538466 1538923 := bstep (se 1 (by rfl) ⟨1154192, by rfl⟩ : syracuseStep 1538923 = 2308385) B2308385
theorem B1538935 : Blo 1538466 1538935 := bstep (se 1 (by rfl) ⟨1154201, by rfl⟩ : syracuseStep 1538935 = 2308403) B2308403
theorem B8887171 : Blo 1538466 8887171 := bstep (se 1 (by rfl) ⟨6665378, by rfl⟩ : syracuseStep 8887171 = 13330757) B13330757
theorem B1538955 : Blo 1538466 1538955 := bstep (se 1 (by rfl) ⟨1154216, by rfl⟩ : syracuseStep 1538955 = 2308433) B2308433
theorem B2309003 : Blo 1538466 2309003 := bstep (se 1 (by rfl) ⟨1731752, by rfl⟩ : syracuseStep 2309003 = 3463505) B3463505
theorem B4995991 : Blo 1538466 4995991 := bstep (se 1 (by rfl) ⟨3746993, by rfl⟩ : syracuseStep 4995991 = 7493987) B7493987
theorem B1538967 : Blo 1538466 1538967 := bstep (se 1 (by rfl) ⟨1154225, by rfl⟩ : syracuseStep 1538967 = 2308451) B2308451
theorem B2309015 : Blo 1538466 2309015 := bstep (se 1 (by rfl) ⟨1731761, by rfl⟩ : syracuseStep 2309015 = 3463523) B3463523
theorem B1538987 : Blo 1538466 1538987 := bstep (se 1 (by rfl) ⟨1154240, by rfl⟩ : syracuseStep 1538987 = 2308481) B2308481
theorem B1538999 : Blo 1538466 1538999 := bstep (se 1 (by rfl) ⟨1154249, by rfl⟩ : syracuseStep 1538999 = 2308499) B2308499
theorem B1539019 : Blo 1538466 1539019 := bstep (se 1 (by rfl) ⟨1154264, by rfl⟩ : syracuseStep 1539019 = 2308529) B2308529
theorem B1539031 : Blo 1538466 1539031 := bstep (se 1 (by rfl) ⟨1154273, by rfl⟩ : syracuseStep 1539031 = 2308547) B2308547
theorem B2309081 : Blo 1538466 2309081 := bstep (se 2 (by rfl) ⟨865905, by rfl⟩ : syracuseStep 2309081 = 1731811) B1731811
theorem B3464153 : Blo 1538466 3464153 := bstep (se 2 (by rfl) ⟨1299057, by rfl⟩ : syracuseStep 3464153 = 2598115) B2598115
theorem B1539051 : Blo 1538466 1539051 := bstep (se 1 (by rfl) ⟨1154288, by rfl⟩ : syracuseStep 1539051 = 2308577) B2308577
theorem B1539063 : Blo 1538466 1539063 := bstep (se 1 (by rfl) ⟨1154297, by rfl⟩ : syracuseStep 1539063 = 2308595) B2308595
theorem B1539083 : Blo 1538466 1539083 := bstep (se 1 (by rfl) ⟨1154312, by rfl⟩ : syracuseStep 1539083 = 2308625) B2308625
theorem B1539095 : Blo 1538466 1539095 := bstep (se 1 (by rfl) ⟨1154321, by rfl⟩ : syracuseStep 1539095 = 2308643) B2308643
theorem B1539115 : Blo 1538466 1539115 := bstep (se 1 (by rfl) ⟨1154336, by rfl⟩ : syracuseStep 1539115 = 2308673) B2308673
theorem B3464243 : Blo 1538466 3464243 := bstep (se 1 (by rfl) ⟨2598182, by rfl⟩ : syracuseStep 3464243 = 5196365) B5196365
theorem B1539127 : Blo 1538466 1539127 := bstep (se 1 (by rfl) ⟨1154345, by rfl⟩ : syracuseStep 1539127 = 2308691) B2308691
theorem B1539147 : Blo 1538466 1539147 := bstep (se 1 (by rfl) ⟨1154360, by rfl⟩ : syracuseStep 1539147 = 2308721) B2308721
theorem B7396427 : Blo 1538466 7396427 := bstep (se 1 (by rfl) ⟨5547320, by rfl⟩ : syracuseStep 7396427 = 11094641) B11094641
theorem B2309195 : Blo 1538466 2309195 := bstep (se 1 (by rfl) ⟨1731896, by rfl⟩ : syracuseStep 2309195 = 3463793) B3463793
theorem B1539159 : Blo 1538466 1539159 := bstep (se 1 (by rfl) ⟨1154369, by rfl⟩ : syracuseStep 1539159 = 2308739) B2308739
theorem B2309207 : Blo 1538466 2309207 := bstep (se 1 (by rfl) ⟨1731905, by rfl⟩ : syracuseStep 2309207 = 3463811) B3463811
theorem B3464279 : Blo 1538466 3464279 := bstep (se 1 (by rfl) ⟨2598209, by rfl⟩ : syracuseStep 3464279 = 5196419) B5196419
theorem B1539179 : Blo 1538466 1539179 := bstep (se 1 (by rfl) ⟨1154384, by rfl⟩ : syracuseStep 1539179 = 2308769) B2308769
theorem B1539191 : Blo 1538466 1539191 := bstep (se 1 (by rfl) ⟨1154393, by rfl⟩ : syracuseStep 1539191 = 2308787) B2308787
theorem B19725443 : Blo 1538466 19725443 := bstep (se 1 (by rfl) ⟨14794082, by rfl⟩ : syracuseStep 19725443 = 29588165) B29588165
theorem B1539211 : Blo 1538466 1539211 := bstep (se 1 (by rfl) ⟨1154408, by rfl⟩ : syracuseStep 1539211 = 2308817) B2308817
theorem B5192855 : Blo 1538466 5192855 := bstep (se 1 (by rfl) ⟨3894641, by rfl⟩ : syracuseStep 5192855 = 7789283) B7789283
theorem B1539223 : Blo 1538466 1539223 := bstep (se 1 (by rfl) ⟨1154417, by rfl⟩ : syracuseStep 1539223 = 2308835) B2308835
theorem B2309273 : Blo 1538466 2309273 := bstep (se 2 (by rfl) ⟨865977, by rfl⟩ : syracuseStep 2309273 = 1731955) B1731955
theorem B1539243 : Blo 1538466 1539243 := bstep (se 1 (by rfl) ⟨1154432, by rfl⟩ : syracuseStep 1539243 = 2308865) B2308865
theorem B1539255 : Blo 1538466 1539255 := bstep (se 1 (by rfl) ⟨1154441, by rfl⟩ : syracuseStep 1539255 = 2308883) B2308883
theorem B1539275 : Blo 1538466 1539275 := bstep (se 1 (by rfl) ⟨1154456, by rfl⟩ : syracuseStep 1539275 = 2308913) B2308913
theorem B1539287 : Blo 1538466 1539287 := bstep (se 1 (by rfl) ⟨1154465, by rfl⟩ : syracuseStep 1539287 = 2308931) B2308931
theorem B1539307 : Blo 1538466 1539307 := bstep (se 1 (by rfl) ⟨1154480, by rfl⟩ : syracuseStep 1539307 = 2308961) B2308961
theorem B1539319 : Blo 1538466 1539319 := bstep (se 1 (by rfl) ⟨1154489, by rfl⟩ : syracuseStep 1539319 = 2308979) B2308979
theorem B1539339 : Blo 1538466 1539339 := bstep (se 1 (by rfl) ⟨1154504, by rfl⟩ : syracuseStep 1539339 = 2309009) B2309009
theorem B2309387 : Blo 1538466 2309387 := bstep (se 1 (by rfl) ⟨1732040, by rfl⟩ : syracuseStep 2309387 = 3464081) B3464081
theorem B3464459 : Blo 1538466 3464459 := bstep (se 1 (by rfl) ⟨2598344, by rfl⟩ : syracuseStep 3464459 = 5196689) B5196689
theorem B1539351 : Blo 1538466 1539351 := bstep (se 1 (by rfl) ⟨1154513, by rfl⟩ : syracuseStep 1539351 = 2309027) B2309027
theorem B2309399 : Blo 1538466 2309399 := bstep (se 1 (by rfl) ⟨1732049, by rfl⟩ : syracuseStep 2309399 = 3464099) B3464099
theorem B1948951 : Blo 1538466 1948951 := bstep (se 1 (by rfl) ⟨1461713, by rfl⟩ : syracuseStep 1948951 = 2923427) B2923427
theorem B1539371 : Blo 1538466 1539371 := bstep (se 1 (by rfl) ⟨1154528, by rfl⟩ : syracuseStep 1539371 = 2309057) B2309057
theorem B1539383 : Blo 1538466 1539383 := bstep (se 1 (by rfl) ⟨1154537, by rfl⟩ : syracuseStep 1539383 = 2309075) B2309075
theorem B3464513 : Blo 1538466 3464513 := bstep (se 2 (by rfl) ⟨1299192, by rfl⟩ : syracuseStep 3464513 = 2598385) B2598385
theorem B21650753 : Blo 1538466 21650753 := bstep (se 2 (by rfl) ⟨8119032, by rfl⟩ : syracuseStep 21650753 = 16238065) B16238065
theorem B2596171 : Blo 1538466 2596171 := bstep (se 1 (by rfl) ⟨1947128, by rfl⟩ : syracuseStep 2596171 = 3894257) B3894257
theorem B1539403 : Blo 1538466 1539403 := bstep (se 1 (by rfl) ⟨1154552, by rfl⟩ : syracuseStep 1539403 = 2309105) B2309105
theorem B6667595 : Blo 1538466 6667595 := bstep (se 1 (by rfl) ⟨5000696, by rfl⟩ : syracuseStep 6667595 = 10001393) B10001393
theorem B1539415 : Blo 1538466 1539415 := bstep (se 1 (by rfl) ⟨1154561, by rfl⟩ : syracuseStep 1539415 = 2309123) B2309123
theorem B4742489 : Blo 1538466 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B2309465 : Blo 1538466 2309465 := bstep (se 2 (by rfl) ⟨866049, by rfl⟩ : syracuseStep 2309465 = 1732099) B1732099
theorem B9485669 : Blo 1538466 9485669 := bstep (se 4 (by rfl) ⟨889281, by rfl⟩ : syracuseStep 9485669 = 1778563) B1778563
theorem B1539435 : Blo 1538466 1539435 := bstep (se 1 (by rfl) ⟨1154576, by rfl⟩ : syracuseStep 1539435 = 2309153) B2309153
theorem B1539447 : Blo 1538466 1539447 := bstep (se 1 (by rfl) ⟨1154585, by rfl⟩ : syracuseStep 1539447 = 2309171) B2309171
theorem B1539467 : Blo 1538466 1539467 := bstep (se 1 (by rfl) ⟨1154600, by rfl⟩ : syracuseStep 1539467 = 2309201) B2309201
theorem B1539479 : Blo 1538466 1539479 := bstep (se 1 (by rfl) ⟨1154609, by rfl⟩ : syracuseStep 1539479 = 2309219) B2309219
theorem B1539499 : Blo 1538466 1539499 := bstep (se 1 (by rfl) ⟨1154624, by rfl⟩ : syracuseStep 1539499 = 2309249) B2309249
theorem B1539511 : Blo 1538466 1539511 := bstep (se 1 (by rfl) ⟨1154633, by rfl⟩ : syracuseStep 1539511 = 2309267) B2309267
theorem B1539531 : Blo 1538466 1539531 := bstep (se 1 (by rfl) ⟨1154648, by rfl⟩ : syracuseStep 1539531 = 2309297) B2309297
theorem B2309579 : Blo 1538466 2309579 := bstep (se 1 (by rfl) ⟨1732184, by rfl⟩ : syracuseStep 2309579 = 3464369) B3464369
theorem B1539543 : Blo 1538466 1539543 := bstep (se 1 (by rfl) ⟨1154657, by rfl⟩ : syracuseStep 1539543 = 2309315) B2309315
theorem B2596313 : Blo 1538466 2596313 := bstep (se 2 (by rfl) ⟨973617, by rfl⟩ : syracuseStep 2596313 = 1947235) B1947235
theorem B2309591 : Blo 1538466 2309591 := bstep (se 1 (by rfl) ⟨1732193, by rfl⟩ : syracuseStep 2309591 = 3464387) B3464387
theorem B1539563 : Blo 1538466 1539563 := bstep (se 1 (by rfl) ⟨1154672, by rfl⟩ : syracuseStep 1539563 = 2309345) B2309345
theorem B1539575 : Blo 1538466 1539575 := bstep (se 1 (by rfl) ⟨1154681, by rfl⟩ : syracuseStep 1539575 = 2309363) B2309363
theorem B2465291 : Blo 1538466 2465291 := bstep (se 1 (by rfl) ⟨1848968, by rfl⟩ : syracuseStep 2465291 = 3697937) B3697937
theorem B1539595 : Blo 1538466 1539595 := bstep (se 1 (by rfl) ⟨1154696, by rfl⟩ : syracuseStep 1539595 = 2309393) B2309393
theorem B1539607 : Blo 1538466 1539607 := bstep (se 1 (by rfl) ⟨1154705, by rfl⟩ : syracuseStep 1539607 = 2309411) B2309411
theorem B2309657 : Blo 1538466 2309657 := bstep (se 2 (by rfl) ⟨866121, by rfl⟩ : syracuseStep 2309657 = 1732243) B1732243
theorem B3464729 : Blo 1538466 3464729 := bstep (se 2 (by rfl) ⟨1299273, by rfl⟩ : syracuseStep 3464729 = 2598547) B2598547
theorem B1539627 : Blo 1538466 1539627 := bstep (se 1 (by rfl) ⟨1154720, by rfl⟩ : syracuseStep 1539627 = 2309441) B2309441
theorem B1539639 : Blo 1538466 1539639 := bstep (se 1 (by rfl) ⟨1154729, by rfl⟩ : syracuseStep 1539639 = 2309459) B2309459
theorem B1539659 : Blo 1538466 1539659 := bstep (se 1 (by rfl) ⟨1154744, by rfl⟩ : syracuseStep 1539659 = 2309489) B2309489
theorem B1539671 : Blo 1538466 1539671 := bstep (se 1 (by rfl) ⟨1154753, by rfl⟩ : syracuseStep 1539671 = 2309507) B2309507
theorem B2596441 : Blo 1538466 2596441 := bstep (se 2 (by rfl) ⟨973665, by rfl⟩ : syracuseStep 2596441 = 1947331) B1947331
theorem B1539691 : Blo 1538466 1539691 := bstep (se 1 (by rfl) ⟨1154768, by rfl⟩ : syracuseStep 1539691 = 2309537) B2309537
theorem B3464819 : Blo 1538466 3464819 := bstep (se 1 (by rfl) ⟨2598614, by rfl⟩ : syracuseStep 3464819 = 5197229) B5197229
theorem B1539703 : Blo 1538466 1539703 := bstep (se 1 (by rfl) ⟨1154777, by rfl⟩ : syracuseStep 1539703 = 2309555) B2309555
theorem B1539723 : Blo 1538466 1539723 := bstep (se 1 (by rfl) ⟨1154792, by rfl⟩ : syracuseStep 1539723 = 2309585) B2309585
theorem B2309771 : Blo 1538466 2309771 := bstep (se 1 (by rfl) ⟨1732328, by rfl⟩ : syracuseStep 2309771 = 3464657) B3464657
theorem B1539735 : Blo 1538466 1539735 := bstep (se 1 (by rfl) ⟨1154801, by rfl⟩ : syracuseStep 1539735 = 2309603) B2309603
theorem B2309783 : Blo 1538466 2309783 := bstep (se 1 (by rfl) ⟨1732337, by rfl⟩ : syracuseStep 2309783 = 3464675) B3464675
theorem B3464855 : Blo 1538466 3464855 := bstep (se 1 (by rfl) ⟨2598641, by rfl⟩ : syracuseStep 3464855 = 5197283) B5197283
theorem B1539755 : Blo 1538466 1539755 := bstep (se 1 (by rfl) ⟨1154816, by rfl⟩ : syracuseStep 1539755 = 2309633) B2309633
theorem B5193395 : Blo 1538466 5193395 := bstep (se 1 (by rfl) ⟨3895046, by rfl⟩ : syracuseStep 5193395 = 7790093) B7790093
theorem B1539767 : Blo 1538466 1539767 := bstep (se 1 (by rfl) ⟨1154825, by rfl⟩ : syracuseStep 1539767 = 2309651) B2309651
theorem B1539787 : Blo 1538466 1539787 := bstep (se 1 (by rfl) ⟨1154840, by rfl⟩ : syracuseStep 1539787 = 2309681) B2309681
theorem B1539799 : Blo 1538466 1539799 := bstep (se 1 (by rfl) ⟨1154849, by rfl⟩ : syracuseStep 1539799 = 2309699) B2309699
theorem B2309849 : Blo 1538466 2309849 := bstep (se 2 (by rfl) ⟨866193, by rfl⟩ : syracuseStep 2309849 = 1732387) B1732387
theorem B1539819 : Blo 1538466 1539819 := bstep (se 1 (by rfl) ⟨1154864, by rfl⟩ : syracuseStep 1539819 = 2309729) B2309729
theorem B1539831 : Blo 1538466 1539831 := bstep (se 1 (by rfl) ⟨1154873, by rfl⟩ : syracuseStep 1539831 = 2309747) B2309747
theorem B1539851 : Blo 1538466 1539851 := bstep (se 1 (by rfl) ⟨1154888, by rfl⟩ : syracuseStep 1539851 = 2309777) B2309777
theorem B1539863 : Blo 1538466 1539863 := bstep (se 1 (by rfl) ⟨1154897, by rfl⟩ : syracuseStep 1539863 = 2309795) B2309795
theorem B1539883 : Blo 1538466 1539883 := bstep (se 1 (by rfl) ⟨1154912, by rfl⟩ : syracuseStep 1539883 = 2309825) B2309825
theorem B1539895 : Blo 1538466 1539895 := bstep (se 1 (by rfl) ⟨1154921, by rfl⟩ : syracuseStep 1539895 = 2309843) B2309843
theorem B1539915 : Blo 1538466 1539915 := bstep (se 1 (by rfl) ⟨1154936, by rfl⟩ : syracuseStep 1539915 = 2309873) B2309873
theorem B1539927 : Blo 1538466 1539927 := bstep (se 1 (by rfl) ⟨1154945, by rfl⟩ : syracuseStep 1539927 = 2309891) B2309891
theorem B9863005 : Blo 1538466 9863005 := bstep (se 3 (by rfl) ⟨1849313, by rfl⟩ : syracuseStep 9863005 = 3698627) B3698627
theorem B1539947 : Blo 1538466 1539947 := bstep (se 1 (by rfl) ⟨1154960, by rfl⟩ : syracuseStep 1539947 = 2309921) B2309921
theorem B1539959 : Blo 1538466 1539959 := bstep (se 1 (by rfl) ⟨1154969, by rfl⟩ : syracuseStep 1539959 = 2309939) B2309939
theorem B67502003 : Blo 1538466 67502003 := bstep (se 1 (by rfl) ⟨50626502, by rfl⟩ : syracuseStep 67502003 = 101253005) B101253005
theorem B5193665 : Blo 1538466 5193665 := bstep (se 2 (by rfl) ⟨1947624, by rfl⟩ : syracuseStep 5193665 = 3895249) B3895249
theorem B4382657 : Blo 1538466 4382657 := bstep (se 2 (by rfl) ⟨1643496, by rfl⟩ : syracuseStep 4382657 = 3286993) B3286993
theorem B29982737 : Blo 1538466 29982737 := bstep (se 2 (by rfl) ⟨11243526, by rfl⟩ : syracuseStep 29982737 = 22487053) B22487053
theorem B2596907 : Blo 1538466 2596907 := bstep (se 1 (by rfl) ⟨1947680, by rfl⟩ : syracuseStep 2596907 = 3895361) B3895361
theorem B4382839 : Blo 1538466 4382839 := bstep (se 1 (by rfl) ⟨3287129, by rfl⟩ : syracuseStep 4382839 = 6574259) B6574259
theorem B2465911 : Blo 1538466 2465911 := bstep (se 1 (by rfl) ⟨1849433, by rfl⟩ : syracuseStep 2465911 = 3698867) B3698867
theorem B5194043 : Blo 1538466 5194043 := bstep (se 1 (by rfl) ⟨3895532, by rfl⟩ : syracuseStep 5194043 = 7791065) B7791065
theorem B2597305 : Blo 1538466 2597305 := bstep (se 2 (by rfl) ⟨973989, by rfl⟩ : syracuseStep 2597305 = 1947979) B1947979
theorem B5194529 : Blo 1538466 5194529 := bstep (se 2 (by rfl) ⟨1947948, by rfl⟩ : syracuseStep 5194529 = 3895897) B3895897
theorem B17564465 : Blo 1538466 17564465 := bstep (se 2 (by rfl) ⟨6586674, by rfl⟩ : syracuseStep 17564465 = 13173349) B13173349
theorem B9364313 : Blo 1538466 9364313 := bstep (se 2 (by rfl) ⟨3511617, by rfl⟩ : syracuseStep 9364313 = 7023235) B7023235
theorem B2598007 : Blo 1538466 2598007 := bstep (se 1 (by rfl) ⟨1948505, by rfl⟩ : syracuseStep 2598007 = 3897011) B3897011
theorem B2598203 : Blo 1538466 2598203 := bstep (se 1 (by rfl) ⟨1948652, by rfl⟩ : syracuseStep 2598203 = 3897305) B3897305
theorem B8324441 : Blo 1538466 8324441 := bstep (se 2 (by rfl) ⟨3121665, by rfl⟩ : syracuseStep 8324441 = 6243331) B6243331
theorem B5195123 : Blo 1538466 5195123 := bstep (se 1 (by rfl) ⟨3896342, by rfl⟩ : syracuseStep 5195123 = 7792685) B7792685
theorem B4384115 : Blo 1538466 4384115 := bstep (se 1 (by rfl) ⟨3288086, by rfl⟩ : syracuseStep 4384115 = 6576173) B6576173
theorem B4384343 : Blo 1538466 4384343 := bstep (se 1 (by rfl) ⟨3288257, by rfl⟩ : syracuseStep 4384343 = 6576515) B6576515
theorem B2598601 : Blo 1538466 2598601 := bstep (se 2 (by rfl) ⟨974475, by rfl⟩ : syracuseStep 2598601 = 1948951) B1948951
theorem B14796695 : Blo 1538466 14796695 := bstep (se 1 (by rfl) ⟨11097521, by rfl⟩ : syracuseStep 14796695 = 22195043) B22195043
theorem B13150295 : Blo 1538466 13150295 := bstep (se 1 (by rfl) ⟨9862721, by rfl⟩ : syracuseStep 13150295 = 19725443) B19725443
theorem B3950777 : Blo 1538466 3950777 := bstep (se 2 (by rfl) ⟨1481541, by rfl⟩ : syracuseStep 3950777 = 2963083) B2963083
theorem B9357605 : Blo 1538466 9357605 := bstep (se 4 (by rfl) ⟨877275, by rfl⟩ : syracuseStep 9357605 = 1754551) B1754551
theorem B1730875 : Blo 1538466 1730875 := bstep (se 1 (by rfl) ⟨1298156, by rfl⟩ : syracuseStep 1730875 = 2596313) B2596313
theorem B13150673 : Blo 1538466 13150673 := bstep (se 2 (by rfl) ⟨4931502, by rfl⟩ : syracuseStep 13150673 = 9863005) B9863005
theorem B180005341 : Blo 1538466 180005341 := bstep (se 3 (by rfl) ⟨33751001, by rfl⟩ : syracuseStep 180005341 = 67502003) B67502003
theorem B1731343 : Blo 1538466 1731343 := bstep (se 1 (by rfl) ⟨1298507, by rfl⟩ : syracuseStep 1731343 = 2597015) B2597015
theorem B16862003 : Blo 1538466 16862003 := bstep (se 1 (by rfl) ⟨12646502, by rfl⟩ : syracuseStep 16862003 = 25293005) B25293005
theorem B5843771 : Blo 1538466 5843771 := bstep (se 1 (by rfl) ⟨4382828, by rfl⟩ : syracuseStep 5843771 = 8765657) B8765657
theorem B23751539 : Blo 1538466 23751539 := bstep (se 1 (by rfl) ⟨17813654, by rfl⟩ : syracuseStep 23751539 = 35627309) B35627309
theorem B8768573 : Blo 1538466 8768573 := bstep (se 3 (by rfl) ⟨1644107, by rfl⟩ : syracuseStep 8768573 = 3288215) B3288215
theorem B205196429 : Blo 1538466 205196429 := bstep (se 3 (by rfl) ⟨38474330, by rfl⟩ : syracuseStep 205196429 = 76948661) B76948661
theorem B3894419 : Blo 1538466 3894419 := bstep (se 1 (by rfl) ⟨2920814, by rfl⟩ : syracuseStep 3894419 = 5841629) B5841629
theorem B4443283 : Blo 1538466 4443283 := bstep (se 1 (by rfl) ⟨3332462, by rfl⟩ : syracuseStep 4443283 = 6664925) B6664925
theorem B1731847 : Blo 1538466 1731847 := bstep (se 1 (by rfl) ⟨1298885, by rfl⟩ : syracuseStep 1731847 = 2597771) B2597771
theorem B5844257 : Blo 1538466 5844257 := bstep (se 2 (by rfl) ⟨2191596, by rfl⟩ : syracuseStep 5844257 = 4383193) B4383193
theorem B239857037 : Blo 1538466 239857037 := bstep (se 3 (by rfl) ⟨44973194, by rfl⟩ : syracuseStep 239857037 = 89946389) B89946389
theorem B3894713 : Blo 1538466 3894713 := bstep (se 2 (by rfl) ⟨1460517, by rfl⟩ : syracuseStep 3894713 = 2921035) B2921035
theorem B1732027 : Blo 1538466 1732027 := bstep (se 1 (by rfl) ⟨1299020, by rfl⟩ : syracuseStep 1732027 = 2598041) B2598041
theorem B11693645 : Blo 1538466 11693645 := bstep (se 3 (by rfl) ⟨2192558, by rfl⟩ : syracuseStep 11693645 = 4385117) B4385117
theorem B7114511 : Blo 1538466 7114511 := bstep (se 1 (by rfl) ⟨5335883, by rfl⟩ : syracuseStep 7114511 = 10671767) B10671767
theorem B17526617 : Blo 1538466 17526617 := bstep (se 2 (by rfl) ⟨6572481, by rfl⟩ : syracuseStep 17526617 = 13144963) B13144963
theorem B9858905 : Blo 1538466 9858905 := bstep (se 2 (by rfl) ⟨3697089, by rfl⟩ : syracuseStep 9858905 = 7394179) B7394179
theorem B11849561 : Blo 1538466 11849561 := bstep (se 2 (by rfl) ⟨4443585, by rfl⟩ : syracuseStep 11849561 = 8887171) B8887171
theorem B3698551 : Blo 1538466 3698551 := bstep (se 1 (by rfl) ⟨2773913, by rfl⟩ : syracuseStep 3698551 = 5547827) B5547827
theorem B379097009 : Blo 1538466 379097009 := bstep (se 2 (by rfl) ⟨142161378, by rfl⟩ : syracuseStep 379097009 = 284322757) B284322757
theorem B2961451 : Blo 1538466 2961451 := bstep (se 1 (by rfl) ⟨2221088, by rfl⟩ : syracuseStep 2961451 = 4442177) B4442177
theorem B9859133 : Blo 1538466 9859133 := bstep (se 3 (by rfl) ⟨1848587, by rfl⟩ : syracuseStep 9859133 = 3697175) B3697175
theorem B3895411 : Blo 1538466 3895411 := bstep (se 1 (by rfl) ⟨2921558, by rfl⟩ : syracuseStep 3895411 = 5843117) B5843117
theorem B2166985 : Blo 1538466 2166985 := bstep (se 2 (by rfl) ⟨812619, by rfl⟩ : syracuseStep 2166985 = 1625239) B1625239
theorem B5845229 : Blo 1538466 5845229 := bstep (se 3 (by rfl) ⟨1095980, by rfl⟩ : syracuseStep 5845229 = 2191961) B2191961
theorem B3895553 : Blo 1538466 3895553 := bstep (se 2 (by rfl) ⟨1460832, by rfl⟩ : syracuseStep 3895553 = 2921665) B2921665
theorem B3461561 : Blo 1538466 3461561 := bstep (se 2 (by rfl) ⟨1298085, by rfl⟩ : syracuseStep 3461561 = 2596171) B2596171
theorem B113865259 : Blo 1538466 113865259 := bstep (se 1 (by rfl) ⟨85398944, by rfl⟩ : syracuseStep 113865259 = 170797889) B170797889
theorem B5845547 : Blo 1538466 5845547 := bstep (se 1 (by rfl) ⟨4384160, by rfl⟩ : syracuseStep 5845547 = 8768321) B8768321
theorem B35558081 : Blo 1538466 35558081 := bstep (se 2 (by rfl) ⟨13334280, by rfl⟩ : syracuseStep 35558081 = 26668561) B26668561
theorem B3896009 : Blo 1538466 3896009 := bstep (se 2 (by rfl) ⟨1461003, by rfl⟩ : syracuseStep 3896009 = 2922007) B2922007
theorem B3461903 : Blo 1538466 3461903 := bstep (se 1 (by rfl) ⟨2596427, by rfl⟩ : syracuseStep 3461903 = 5192855) B5192855
theorem B3461921 : Blo 1538466 3461921 := bstep (se 2 (by rfl) ⟨1298220, by rfl⟩ : syracuseStep 3461921 = 2596441) B2596441
theorem B26645285 : Blo 1538466 26645285 := bstep (se 4 (by rfl) ⟨2497995, by rfl⟩ : syracuseStep 26645285 = 4995991) B4995991
theorem B4445063 : Blo 1538466 4445063 := bstep (se 1 (by rfl) ⟨3333797, by rfl⟩ : syracuseStep 4445063 = 6667595) B6667595
theorem B7795601 : Blo 1538466 7795601 := bstep (se 2 (by rfl) ⟨2923350, by rfl⟩ : syracuseStep 7795601 = 5846701) B5846701
theorem B1643527 : Blo 1538466 1643527 := bstep (se 1 (by rfl) ⟨1232645, by rfl⟩ : syracuseStep 1643527 = 2465291) B2465291
theorem B6239243 : Blo 1538466 6239243 := bstep (se 1 (by rfl) ⟨4679432, by rfl⟩ : syracuseStep 6239243 = 9358865) B9358865
theorem B3896363 : Blo 1538466 3896363 := bstep (se 1 (by rfl) ⟨2922272, by rfl⟩ : syracuseStep 3896363 = 5844545) B5844545
theorem B3462263 : Blo 1538466 3462263 := bstep (se 1 (by rfl) ⟨2596697, by rfl⟩ : syracuseStep 3462263 = 5193395) B5193395
theorem B3462443 : Blo 1538466 3462443 := bstep (se 1 (by rfl) ⟨2596832, by rfl⟩ : syracuseStep 3462443 = 5193665) B5193665
theorem B2921771 : Blo 1538466 2921771 := bstep (se 1 (by rfl) ⟨2191328, by rfl⟩ : syracuseStep 2921771 = 4382657) B4382657
theorem B1947179 : Blo 1538466 1947179 := bstep (se 1 (by rfl) ⟨1460384, by rfl⟩ : syracuseStep 1947179 = 2920769) B2920769
theorem B14038595 : Blo 1538466 14038595 := bstep (se 1 (by rfl) ⟨10528946, by rfl⟩ : syracuseStep 14038595 = 21057893) B21057893
theorem B2307719 : Blo 1538466 2307719 := bstep (se 1 (by rfl) ⟨1730789, by rfl⟩ : syracuseStep 2307719 = 3461579) B3461579
theorem B2774663 : Blo 1538466 2774663 := bstep (se 1 (by rfl) ⟨2080997, by rfl⟩ : syracuseStep 2774663 = 4161995) B4161995
theorem B3462803 : Blo 1538466 3462803 := bstep (se 1 (by rfl) ⟨2597102, by rfl⟩ : syracuseStep 3462803 = 5194205) B5194205
theorem B2307755 : Blo 1538466 2307755 := bstep (se 1 (by rfl) ⟨1730816, by rfl⟩ : syracuseStep 2307755 = 3461633) B3461633
theorem B13153985 : Blo 1538466 13153985 := bstep (se 2 (by rfl) ⟨4932744, by rfl⟩ : syracuseStep 13153985 = 9865489) B9865489
theorem B2307785 : Blo 1538466 2307785 := bstep (se 2 (by rfl) ⟨865419, by rfl⟩ : syracuseStep 2307785 = 1730839) B1730839
theorem B3462857 : Blo 1538466 3462857 := bstep (se 2 (by rfl) ⟨1298571, by rfl⟩ : syracuseStep 3462857 = 2597143) B2597143
theorem B11851535 : Blo 1538466 11851535 := bstep (se 1 (by rfl) ⟨8888651, by rfl⟩ : syracuseStep 11851535 = 17777303) B17777303
theorem B8763173 : Blo 1538466 8763173 := bstep (se 4 (by rfl) ⟨821547, by rfl⟩ : syracuseStep 8763173 = 1643095) B1643095
theorem B2307899 : Blo 1538466 2307899 := bstep (se 1 (by rfl) ⟨1730924, by rfl⟩ : syracuseStep 2307899 = 3461849) B3461849
theorem B1644347 : Blo 1538466 1644347 := bstep (se 1 (by rfl) ⟨1233260, by rfl⟩ : syracuseStep 1644347 = 2466521) B2466521
theorem B2307959 : Blo 1538466 2307959 := bstep (se 1 (by rfl) ⟨1730969, by rfl⟩ : syracuseStep 2307959 = 3461939) B3461939
theorem B4159367 : Blo 1538466 4159367 := bstep (se 1 (by rfl) ⟨3119525, by rfl⟩ : syracuseStep 4159367 = 6239051) B6239051
theorem B2307983 : Blo 1538466 2307983 := bstep (se 1 (by rfl) ⟨1730987, by rfl⟩ : syracuseStep 2307983 = 3461975) B3461975
theorem B2308025 : Blo 1538466 2308025 := bstep (se 2 (by rfl) ⟨865509, by rfl⟩ : syracuseStep 2308025 = 1731019) B1731019
theorem B2308103 : Blo 1538466 2308103 := bstep (se 1 (by rfl) ⟨1731077, by rfl⟩ : syracuseStep 2308103 = 3462155) B3462155
theorem B1947655 : Blo 1538466 1947655 := bstep (se 1 (by rfl) ⟨1460741, by rfl⟩ : syracuseStep 1947655 = 2921483) B2921483
theorem B3897355 : Blo 1538466 3897355 := bstep (se 1 (by rfl) ⟨2923016, by rfl⟩ : syracuseStep 3897355 = 5846033) B5846033
theorem B2308139 : Blo 1538466 2308139 := bstep (se 1 (by rfl) ⟨1731104, by rfl⟩ : syracuseStep 2308139 = 3462209) B3462209
theorem B2308169 : Blo 1538466 2308169 := bstep (se 2 (by rfl) ⟨865563, by rfl⟩ : syracuseStep 2308169 = 1731127) B1731127
theorem B3897497 : Blo 1538466 3897497 := bstep (se 2 (by rfl) ⟨1461561, by rfl⟩ : syracuseStep 3897497 = 2923123) B2923123
theorem B2308283 : Blo 1538466 2308283 := bstep (se 1 (by rfl) ⟨1731212, by rfl⟩ : syracuseStep 2308283 = 3462425) B3462425
theorem B2308343 : Blo 1538466 2308343 := bstep (se 1 (by rfl) ⟨1731257, by rfl⟩ : syracuseStep 2308343 = 3462515) B3462515
theorem B2308367 : Blo 1538466 2308367 := bstep (se 1 (by rfl) ⟨1731275, by rfl⟩ : syracuseStep 2308367 = 3462551) B3462551
theorem B4159777 : Blo 1538466 4159777 := bstep (se 2 (by rfl) ⟨1559916, by rfl⟩ : syracuseStep 4159777 = 3119833) B3119833
theorem B2308409 : Blo 1538466 2308409 := bstep (se 2 (by rfl) ⟨865653, by rfl⟩ : syracuseStep 2308409 = 1731307) B1731307
theorem B3897659 : Blo 1538466 3897659 := bstep (se 1 (by rfl) ⟨2923244, by rfl⟩ : syracuseStep 3897659 = 5846489) B5846489
theorem B2308487 : Blo 1538466 2308487 := bstep (se 1 (by rfl) ⟨1731365, by rfl⟩ : syracuseStep 2308487 = 3462731) B3462731
theorem B3463559 : Blo 1538466 3463559 := bstep (se 1 (by rfl) ⟨2597669, by rfl⟩ : syracuseStep 3463559 = 5195339) B5195339
theorem B2308523 : Blo 1538466 2308523 := bstep (se 1 (by rfl) ⟨1731392, by rfl⟩ : syracuseStep 2308523 = 3462785) B3462785
theorem B4929977 : Blo 1538466 4929977 := bstep (se 2 (by rfl) ⟨1848741, by rfl⟩ : syracuseStep 4929977 = 3697483) B3697483
theorem B1538491 : Blo 1538466 1538491 := bstep (se 1 (by rfl) ⟨1153868, by rfl⟩ : syracuseStep 1538491 = 2307737) B2307737
theorem B2308553 : Blo 1538466 2308553 := bstep (se 2 (by rfl) ⟨865707, by rfl⟩ : syracuseStep 2308553 = 1731415) B1731415
theorem B1948151 : Blo 1538466 1948151 := bstep (se 1 (by rfl) ⟨1461113, by rfl⟩ : syracuseStep 1948151 = 2922227) B2922227
theorem B1538567 : Blo 1538466 1538567 := bstep (se 1 (by rfl) ⟨1153925, by rfl⟩ : syracuseStep 1538567 = 2307851) B2307851
theorem B4381199 : Blo 1538466 4381199 := bstep (se 1 (by rfl) ⟨3285899, by rfl⟩ : syracuseStep 4381199 = 6571799) B6571799
theorem B1538575 : Blo 1538466 1538575 := bstep (se 1 (by rfl) ⟨1153931, by rfl⟩ : syracuseStep 1538575 = 2307863) B2307863
theorem B4160015 : Blo 1538466 4160015 := bstep (se 1 (by rfl) ⟨3120011, by rfl⟩ : syracuseStep 4160015 = 6240023) B6240023
theorem B8763947 : Blo 1538466 8763947 := bstep (se 1 (by rfl) ⟨6572960, by rfl⟩ : syracuseStep 8763947 = 13145921) B13145921
theorem B1538619 : Blo 1538466 1538619 := bstep (se 1 (by rfl) ⟨1153964, by rfl⟩ : syracuseStep 1538619 = 2307929) B2307929
theorem B2308667 : Blo 1538466 2308667 := bstep (se 1 (by rfl) ⟨1731500, by rfl⟩ : syracuseStep 2308667 = 3463001) B3463001
theorem B3463739 : Blo 1538466 3463739 := bstep (se 1 (by rfl) ⟨2597804, by rfl⟩ : syracuseStep 3463739 = 5195609) B5195609
theorem B2308727 : Blo 1538466 2308727 := bstep (se 1 (by rfl) ⟨1731545, by rfl⟩ : syracuseStep 2308727 = 3463091) B3463091
theorem B1538695 : Blo 1538466 1538695 := bstep (se 1 (by rfl) ⟨1154021, by rfl⟩ : syracuseStep 1538695 = 2308043) B2308043
theorem B1538703 : Blo 1538466 1538703 := bstep (se 1 (by rfl) ⟨1154027, by rfl⟩ : syracuseStep 1538703 = 2308055) B2308055
theorem B2308751 : Blo 1538466 2308751 := bstep (se 1 (by rfl) ⟨1731563, by rfl⟩ : syracuseStep 2308751 = 3463127) B3463127
theorem B1948303 : Blo 1538466 1948303 := bstep (se 1 (by rfl) ⟨1461227, by rfl⟩ : syracuseStep 1948303 = 2922455) B2922455
theorem B3898003 : Blo 1538466 3898003 := bstep (se 1 (by rfl) ⟨2923502, by rfl⟩ : syracuseStep 3898003 = 5847005) B5847005
theorem B2308793 : Blo 1538466 2308793 := bstep (se 2 (by rfl) ⟨865797, by rfl⟩ : syracuseStep 2308793 = 1731595) B1731595
theorem B3463865 : Blo 1538466 3463865 := bstep (se 2 (by rfl) ⟨1298949, by rfl⟩ : syracuseStep 3463865 = 2597899) B2597899
theorem B1538747 : Blo 1538466 1538747 := bstep (se 1 (by rfl) ⟨1154060, by rfl⟩ : syracuseStep 1538747 = 2308121) B2308121
theorem B1538823 : Blo 1538466 1538823 := bstep (se 1 (by rfl) ⟨1154117, by rfl⟩ : syracuseStep 1538823 = 2308235) B2308235
theorem B2308871 : Blo 1538466 2308871 := bstep (se 1 (by rfl) ⟨1731653, by rfl⟩ : syracuseStep 2308871 = 3463307) B3463307
theorem B1538831 : Blo 1538466 1538831 := bstep (se 1 (by rfl) ⟨1154123, by rfl⟩ : syracuseStep 1538831 = 2308247) B2308247
theorem B19995407 : Blo 1538466 19995407 := bstep (se 1 (by rfl) ⟨14996555, by rfl⟩ : syracuseStep 19995407 = 29993111) B29993111
theorem B37452581 : Blo 1538466 37452581 := bstep (se 4 (by rfl) ⟨3511179, by rfl⟩ : syracuseStep 37452581 = 7022359) B7022359
theorem B2308907 : Blo 1538466 2308907 := bstep (se 1 (by rfl) ⟨1731680, by rfl⟩ : syracuseStep 2308907 = 3463361) B3463361
theorem B1538875 : Blo 1538466 1538875 := bstep (se 1 (by rfl) ⟨1154156, by rfl⟩ : syracuseStep 1538875 = 2308313) B2308313
theorem B1948475 : Blo 1538466 1948475 := bstep (se 1 (by rfl) ⟨1461356, by rfl⟩ : syracuseStep 1948475 = 2922713) B2922713
theorem B2308937 : Blo 1538466 2308937 := bstep (se 2 (by rfl) ⟨865851, by rfl⟩ : syracuseStep 2308937 = 1731703) B1731703
theorem B9862003 : Blo 1538466 9862003 := bstep (se 1 (by rfl) ⟨7396502, by rfl⟩ : syracuseStep 9862003 = 14793005) B14793005
theorem B1538951 : Blo 1538466 1538951 := bstep (se 1 (by rfl) ⟨1154213, by rfl⟩ : syracuseStep 1538951 = 2308427) B2308427
theorem B1538959 : Blo 1538466 1538959 := bstep (se 1 (by rfl) ⟨1154219, by rfl⟩ : syracuseStep 1538959 = 2308439) B2308439
theorem B1539003 : Blo 1538466 1539003 := bstep (se 1 (by rfl) ⟨1154252, by rfl⟩ : syracuseStep 1539003 = 2308505) B2308505
theorem B2309051 : Blo 1538466 2309051 := bstep (se 1 (by rfl) ⟨1731788, by rfl⟩ : syracuseStep 2309051 = 3463577) B3463577
theorem B2923465 : Blo 1538466 2923465 := bstep (se 2 (by rfl) ⟨1096299, by rfl⟩ : syracuseStep 2923465 = 2192599) B2192599
theorem B2309111 : Blo 1538466 2309111 := bstep (se 1 (by rfl) ⟨1731833, by rfl⟩ : syracuseStep 2309111 = 3463667) B3463667
theorem B1539079 : Blo 1538466 1539079 := bstep (se 1 (by rfl) ⟨1154309, by rfl⟩ : syracuseStep 1539079 = 2308619) B2308619
theorem B1539087 : Blo 1538466 1539087 := bstep (se 1 (by rfl) ⟨1154315, by rfl⟩ : syracuseStep 1539087 = 2308631) B2308631
theorem B2309135 : Blo 1538466 2309135 := bstep (se 1 (by rfl) ⟨1731851, by rfl⟩ : syracuseStep 2309135 = 3463703) B3463703
theorem B3464207 : Blo 1538466 3464207 := bstep (se 1 (by rfl) ⟨2598155, by rfl⟩ : syracuseStep 3464207 = 5196311) B5196311
theorem B3464225 : Blo 1538466 3464225 := bstep (se 2 (by rfl) ⟨1299084, by rfl⟩ : syracuseStep 3464225 = 2598169) B2598169
theorem B5192747 : Blo 1538466 5192747 := bstep (se 1 (by rfl) ⟨3894560, by rfl⟩ : syracuseStep 5192747 = 7789121) B7789121
theorem B2309177 : Blo 1538466 2309177 := bstep (se 2 (by rfl) ⟨865941, by rfl⟩ : syracuseStep 2309177 = 1731883) B1731883
theorem B1539131 : Blo 1538466 1539131 := bstep (se 1 (by rfl) ⟨1154348, by rfl⟩ : syracuseStep 1539131 = 2308697) B2308697
theorem B1539207 : Blo 1538466 1539207 := bstep (se 1 (by rfl) ⟨1154405, by rfl⟩ : syracuseStep 1539207 = 2308811) B2308811
theorem B2309255 : Blo 1538466 2309255 := bstep (se 1 (by rfl) ⟨1731941, by rfl⟩ : syracuseStep 2309255 = 3463883) B3463883
theorem B1539215 : Blo 1538466 1539215 := bstep (se 1 (by rfl) ⟨1154411, by rfl⟩ : syracuseStep 1539215 = 2308823) B2308823
theorem B2309291 : Blo 1538466 2309291 := bstep (se 1 (by rfl) ⟨1731968, by rfl⟩ : syracuseStep 2309291 = 3463937) B3463937
theorem B1539259 : Blo 1538466 1539259 := bstep (se 1 (by rfl) ⟨1154444, by rfl⟩ : syracuseStep 1539259 = 2308889) B2308889
theorem B7789769 : Blo 1538466 7789769 := bstep (se 2 (by rfl) ⟨2921163, by rfl⟩ : syracuseStep 7789769 = 5842327) B5842327
theorem B2309321 : Blo 1538466 2309321 := bstep (se 2 (by rfl) ⟨865995, by rfl⟩ : syracuseStep 2309321 = 1731991) B1731991
theorem B1539335 : Blo 1538466 1539335 := bstep (se 1 (by rfl) ⟨1154501, by rfl⟩ : syracuseStep 1539335 = 2309003) B2309003
theorem B1539343 : Blo 1538466 1539343 := bstep (se 1 (by rfl) ⟨1154507, by rfl⟩ : syracuseStep 1539343 = 2309015) B2309015
theorem B1539387 : Blo 1538466 1539387 := bstep (se 1 (by rfl) ⟨1154540, by rfl⟩ : syracuseStep 1539387 = 2309081) B2309081
theorem B2309435 : Blo 1538466 2309435 := bstep (se 1 (by rfl) ⟨1732076, by rfl⟩ : syracuseStep 2309435 = 3464153) B3464153
theorem B7396697 : Blo 1538466 7396697 := bstep (se 2 (by rfl) ⟨2773761, by rfl⟩ : syracuseStep 7396697 = 5547523) B5547523
theorem B2309495 : Blo 1538466 2309495 := bstep (se 1 (by rfl) ⟨1732121, by rfl⟩ : syracuseStep 2309495 = 3464243) B3464243
theorem B3464567 : Blo 1538466 3464567 := bstep (se 1 (by rfl) ⟨2598425, by rfl⟩ : syracuseStep 3464567 = 5196851) B5196851
theorem B4930951 : Blo 1538466 4930951 := bstep (se 1 (by rfl) ⟨3698213, by rfl⟩ : syracuseStep 4930951 = 7396427) B7396427
theorem B1539463 : Blo 1538466 1539463 := bstep (se 1 (by rfl) ⟨1154597, by rfl⟩ : syracuseStep 1539463 = 2309195) B2309195
theorem B1539471 : Blo 1538466 1539471 := bstep (se 1 (by rfl) ⟨1154603, by rfl⟩ : syracuseStep 1539471 = 2309207) B2309207
theorem B2309519 : Blo 1538466 2309519 := bstep (se 1 (by rfl) ⟨1732139, by rfl⟩ : syracuseStep 2309519 = 3464279) B3464279
theorem B2309561 : Blo 1538466 2309561 := bstep (se 2 (by rfl) ⟨866085, by rfl⟩ : syracuseStep 2309561 = 1732171) B1732171
theorem B1539515 : Blo 1538466 1539515 := bstep (se 1 (by rfl) ⟨1154636, by rfl⟩ : syracuseStep 1539515 = 2309273) B2309273
theorem B7396811 : Blo 1538466 7396811 := bstep (se 1 (by rfl) ⟨5547608, by rfl⟩ : syracuseStep 7396811 = 11095217) B11095217
theorem B1539591 : Blo 1538466 1539591 := bstep (se 1 (by rfl) ⟨1154693, by rfl⟩ : syracuseStep 1539591 = 2309387) B2309387
theorem B2309639 : Blo 1538466 2309639 := bstep (se 1 (by rfl) ⟨1732229, by rfl⟩ : syracuseStep 2309639 = 3464459) B3464459
theorem B2596367 : Blo 1538466 2596367 := bstep (se 1 (by rfl) ⟨1947275, by rfl⟩ : syracuseStep 2596367 = 3894551) B3894551
theorem B1539599 : Blo 1538466 1539599 := bstep (se 1 (by rfl) ⟨1154699, by rfl⟩ : syracuseStep 1539599 = 2309399) B2309399
theorem B4161053 : Blo 1538466 4161053 := bstep (se 3 (by rfl) ⟨780197, by rfl⟩ : syracuseStep 4161053 = 1560395) B1560395
theorem B2309675 : Blo 1538466 2309675 := bstep (se 1 (by rfl) ⟨1732256, by rfl⟩ : syracuseStep 2309675 = 3464513) B3464513
theorem B14433835 : Blo 1538466 14433835 := bstep (se 1 (by rfl) ⟨10825376, by rfl⟩ : syracuseStep 14433835 = 21650753) B21650753
theorem B3464747 : Blo 1538466 3464747 := bstep (se 1 (by rfl) ⟨2598560, by rfl⟩ : syracuseStep 3464747 = 5197121) B5197121
theorem B3161659 : Blo 1538466 3161659 := bstep (se 1 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 3161659 = 4742489) B4742489
theorem B1539643 : Blo 1538466 1539643 := bstep (se 1 (by rfl) ⟨1154732, by rfl⟩ : syracuseStep 1539643 = 2309465) B2309465
theorem B6323779 : Blo 1538466 6323779 := bstep (se 1 (by rfl) ⟨4742834, by rfl⟩ : syracuseStep 6323779 = 9485669) B9485669
theorem B2309705 : Blo 1538466 2309705 := bstep (se 2 (by rfl) ⟨866139, by rfl⟩ : syracuseStep 2309705 = 1732279) B1732279
theorem B2465399 : Blo 1538466 2465399 := bstep (se 1 (by rfl) ⟨1849049, by rfl⟩ : syracuseStep 2465399 = 3698099) B3698099
theorem B1539719 : Blo 1538466 1539719 := bstep (se 1 (by rfl) ⟨1154789, by rfl⟩ : syracuseStep 1539719 = 2309579) B2309579
theorem B1539727 : Blo 1538466 1539727 := bstep (se 1 (by rfl) ⟨1154795, by rfl⟩ : syracuseStep 1539727 = 2309591) B2309591
theorem B1539771 : Blo 1538466 1539771 := bstep (se 1 (by rfl) ⟨1154828, by rfl⟩ : syracuseStep 1539771 = 2309657) B2309657
theorem B2309819 : Blo 1538466 2309819 := bstep (se 1 (by rfl) ⟨1732364, by rfl⟩ : syracuseStep 2309819 = 3464729) B3464729
theorem B2309879 : Blo 1538466 2309879 := bstep (se 1 (by rfl) ⟨1732409, by rfl⟩ : syracuseStep 2309879 = 3464819) B3464819
theorem B1539847 : Blo 1538466 1539847 := bstep (se 1 (by rfl) ⟨1154885, by rfl⟩ : syracuseStep 1539847 = 2309771) B2309771
theorem B1539855 : Blo 1538466 1539855 := bstep (se 1 (by rfl) ⟨1154891, by rfl⟩ : syracuseStep 1539855 = 2309783) B2309783
theorem B2309903 : Blo 1538466 2309903 := bstep (se 1 (by rfl) ⟨1732427, by rfl⟩ : syracuseStep 2309903 = 3464855) B3464855
theorem B2309945 : Blo 1538466 2309945 := bstep (se 2 (by rfl) ⟨866229, by rfl⟩ : syracuseStep 2309945 = 1732459) B1732459
theorem B1539899 : Blo 1538466 1539899 := bstep (se 1 (by rfl) ⟨1154924, by rfl⟩ : syracuseStep 1539899 = 2309849) B2309849
theorem B8765405 : Blo 1538466 8765405 := bstep (se 3 (by rfl) ⟨1643513, by rfl⟩ : syracuseStep 8765405 = 3287027) B3287027
theorem B2596873 : Blo 1538466 2596873 := bstep (se 2 (by rfl) ⟨973827, by rfl⟩ : syracuseStep 2596873 = 1947655) B1947655
theorem B79953965 : Blo 1538466 79953965 := bstep (se 3 (by rfl) ⟨14991368, by rfl⟩ : syracuseStep 79953965 = 29982737) B29982737
theorem B3948601 : Blo 1538466 3948601 := bstep (se 2 (by rfl) ⟨1480725, by rfl⟩ : syracuseStep 3948601 = 2961451) B2961451
theorem B5193881 : Blo 1538466 5193881 := bstep (se 2 (by rfl) ⟨1947705, by rfl⟩ : syracuseStep 5193881 = 3895411) B3895411
theorem B2597035 : Blo 1538466 2597035 := bstep (se 1 (by rfl) ⟨1947776, by rfl⟩ : syracuseStep 2597035 = 3895553) B3895553
theorem B5546369 : Blo 1538466 5546369 := bstep (se 2 (by rfl) ⟨2079888, by rfl⟩ : syracuseStep 5546369 = 4159777) B4159777
theorem B2597339 : Blo 1538466 2597339 := bstep (se 1 (by rfl) ⟨1948004, by rfl⟩ : syracuseStep 2597339 = 3896009) B3896009
theorem B6242875 : Blo 1538466 6242875 := bstep (se 1 (by rfl) ⟨4682156, by rfl⟩ : syracuseStep 6242875 = 9364313) B9364313
theorem B2597575 : Blo 1538466 2597575 := bstep (se 1 (by rfl) ⟨1948181, by rfl⟩ : syracuseStep 2597575 = 3896363) B3896363
theorem B7791389 : Blo 1538466 7791389 := bstep (se 3 (by rfl) ⟨1460885, by rfl⟩ : syracuseStep 7791389 = 2921771) B2921771
theorem B2597737 : Blo 1538466 2597737 := bstep (se 2 (by rfl) ⟨974151, by rfl⟩ : syracuseStep 2597737 = 1948303) B1948303
theorem B13149337 : Blo 1538466 13149337 := bstep (se 2 (by rfl) ⟨4931001, by rfl⟩ : syracuseStep 13149337 = 9862003) B9862003
theorem B5842115 : Blo 1538466 5842115 := bstep (se 1 (by rfl) ⟨4381586, by rfl⟩ : syracuseStep 5842115 = 8763173) B8763173
theorem B5195069 : Blo 1538466 5195069 := bstep (se 3 (by rfl) ⟨974075, by rfl⟩ : syracuseStep 5195069 = 1948151) B1948151
theorem B8766863 : Blo 1538466 8766863 := bstep (se 1 (by rfl) ⟨6575147, by rfl⟩ : syracuseStep 8766863 = 13150295) B13150295
theorem B2598331 : Blo 1538466 2598331 := bstep (se 1 (by rfl) ⟨1948748, by rfl⟩ : syracuseStep 2598331 = 3897497) B3897497
theorem B5924377 : Blo 1538466 5924377 := bstep (se 2 (by rfl) ⟨2221641, by rfl⟩ : syracuseStep 5924377 = 4443283) B4443283
theorem B2598439 : Blo 1538466 2598439 := bstep (se 1 (by rfl) ⟨1948829, by rfl⟩ : syracuseStep 2598439 = 3897659) B3897659
theorem B3286651 : Blo 1538466 3286651 := bstep (se 1 (by rfl) ⟨2464988, by rfl⟩ : syracuseStep 3286651 = 4929977) B4929977
theorem B8767115 : Blo 1538466 8767115 := bstep (se 1 (by rfl) ⟨6575336, by rfl⟩ : syracuseStep 8767115 = 13150673) B13150673
theorem B5842631 : Blo 1538466 5842631 := bstep (se 1 (by rfl) ⟨4381973, by rfl⟩ : syracuseStep 5842631 = 8763947) B8763947
theorem B13330271 : Blo 1538466 13330271 := bstep (se 1 (by rfl) ⟨9997703, by rfl⟩ : syracuseStep 13330271 = 19995407) B19995407
theorem B11241335 : Blo 1538466 11241335 := bstep (se 1 (by rfl) ⟨8431001, by rfl⟩ : syracuseStep 11241335 = 16862003) B16862003
theorem B19245113 : Blo 1538466 19245113 := bstep (se 2 (by rfl) ⟨7216917, by rfl⟩ : syracuseStep 19245113 = 14433835) B14433835
theorem B8431705 : Blo 1538466 8431705 := bstep (se 2 (by rfl) ⟨3161889, by rfl⟩ : syracuseStep 8431705 = 6323779) B6323779
theorem B5195933 : Blo 1538466 5195933 := bstep (se 3 (by rfl) ⟨974237, by rfl⟩ : syracuseStep 5195933 = 1948475) B1948475
theorem B4384925 : Blo 1538466 4384925 := bstep (se 3 (by rfl) ⟨822173, by rfl⟩ : syracuseStep 4384925 = 1644347) B1644347
theorem B1730911 : Blo 1538466 1730911 := bstep (se 1 (by rfl) ⟨1298183, by rfl⟩ : syracuseStep 1730911 = 2596367) B2596367
theorem B11684411 : Blo 1538466 11684411 := bstep (se 1 (by rfl) ⟨8763308, by rfl⟩ : syracuseStep 11684411 = 17526617) B17526617
theorem B6572603 : Blo 1538466 6572603 := bstep (se 1 (by rfl) ⟨4929452, by rfl⟩ : syracuseStep 6572603 = 9858905) B9858905
theorem B7899707 : Blo 1538466 7899707 := bstep (se 1 (by rfl) ⟨5924780, by rfl⟩ : syracuseStep 7899707 = 11849561) B11849561
theorem B5843603 : Blo 1538466 5843603 := bstep (se 1 (by rfl) ⟨4382702, by rfl⟩ : syracuseStep 5843603 = 8765405) B8765405
theorem B5196473 : Blo 1538466 5196473 := bstep (se 2 (by rfl) ⟨1948677, by rfl⟩ : syracuseStep 5196473 = 3897355) B3897355
theorem B1731271 : Blo 1538466 1731271 := bstep (se 1 (by rfl) ⟨1298453, by rfl⟩ : syracuseStep 1731271 = 2596907) B2596907
theorem B6572755 : Blo 1538466 6572755 := bstep (se 1 (by rfl) ⟨4929566, by rfl⟩ : syracuseStep 6572755 = 9859133) B9859133
theorem B5843785 : Blo 1538466 5843785 := bstep (se 2 (by rfl) ⟨2191419, by rfl⟩ : syracuseStep 5843785 = 4382839) B4382839
theorem B3287881 : Blo 1538466 3287881 := bstep (se 2 (by rfl) ⟨1232955, by rfl⟩ : syracuseStep 3287881 = 2465911) B2465911
theorem B11709643 : Blo 1538466 11709643 := bstep (se 1 (by rfl) ⟨8782232, by rfl⟩ : syracuseStep 11709643 = 17564465) B17564465
theorem B5197067 : Blo 1538466 5197067 := bstep (se 1 (by rfl) ⟨3897800, by rfl⟩ : syracuseStep 5197067 = 7795601) B7795601
theorem B5197337 : Blo 1538466 5197337 := bstep (se 2 (by rfl) ⟨1949001, by rfl⟩ : syracuseStep 5197337 = 3898003) B3898003
theorem B1732135 : Blo 1538466 1732135 := bstep (se 1 (by rfl) ⟨1299101, by rfl⟩ : syracuseStep 1732135 = 2598203) B2598203
theorem B5549627 : Blo 1538466 5549627 := bstep (se 1 (by rfl) ⟨4162220, by rfl⟩ : syracuseStep 5549627 = 8324441) B8324441
theorem B9359063 : Blo 1538466 9359063 := bstep (se 1 (by rfl) ⟨7019297, by rfl⟩ : syracuseStep 9359063 = 14038595) B14038595
theorem B8769323 : Blo 1538466 8769323 := bstep (se 1 (by rfl) ⟨6576992, by rfl⟩ : syracuseStep 8769323 = 13153985) B13153985
theorem B7901023 : Blo 1538466 7901023 := bstep (se 1 (by rfl) ⟨5925767, by rfl⟩ : syracuseStep 7901023 = 11851535) B11851535
theorem B2772911 : Blo 1538466 2772911 := bstep (se 1 (by rfl) ⟨2079683, by rfl⟩ : syracuseStep 2772911 = 4159367) B4159367
theorem B2191369 : Blo 1538466 2191369 := bstep (se 2 (by rfl) ⟨821763, by rfl⟩ : syracuseStep 2191369 = 1643527) B1643527
theorem B2633851 : Blo 1538466 2633851 := bstep (se 1 (by rfl) ⟨1975388, by rfl⟩ : syracuseStep 2633851 = 3950777) B3950777
theorem B6238403 : Blo 1538466 6238403 := bstep (se 1 (by rfl) ⟨4678802, by rfl⟩ : syracuseStep 6238403 = 9357605) B9357605
theorem B2920799 : Blo 1538466 2920799 := bstep (se 1 (by rfl) ⟨2190599, by rfl⟩ : syracuseStep 2920799 = 4381199) B4381199
theorem B2773343 : Blo 1538466 2773343 := bstep (se 1 (by rfl) ⟨2080007, by rfl⟩ : syracuseStep 2773343 = 4160015) B4160015
theorem B6574601 : Blo 1538466 6574601 := bstep (se 2 (by rfl) ⟨2465475, by rfl⟩ : syracuseStep 6574601 = 4930951) B4930951
theorem B3895847 : Blo 1538466 3895847 := bstep (se 1 (by rfl) ⟨2921885, by rfl⟩ : syracuseStep 3895847 = 5843771) B5843771
theorem B3461831 : Blo 1538466 3461831 := bstep (se 1 (by rfl) ⟨2596373, by rfl⟩ : syracuseStep 3461831 = 5192747) B5192747
theorem B5845715 : Blo 1538466 5845715 := bstep (se 1 (by rfl) ⟨4384286, by rfl⟩ : syracuseStep 5845715 = 8768573) B8768573
theorem B4215545 : Blo 1538466 4215545 := bstep (se 2 (by rfl) ⟨1580829, by rfl⟩ : syracuseStep 4215545 = 3161659) B3161659
theorem B71054093 : Blo 1538466 71054093 := bstep (se 3 (by rfl) ⟨13322642, by rfl⟩ : syracuseStep 71054093 = 26645285) B26645285
theorem B3896171 : Blo 1538466 3896171 := bstep (se 1 (by rfl) ⟨2922128, by rfl⟩ : syracuseStep 3896171 = 5844257) B5844257
theorem B159904691 : Blo 1538466 159904691 := bstep (se 1 (by rfl) ⟨119928518, by rfl⟩ : syracuseStep 159904691 = 239857037) B239857037
theorem B2774035 : Blo 1538466 2774035 := bstep (se 1 (by rfl) ⟨2080526, by rfl⟩ : syracuseStep 2774035 = 4161053) B4161053
theorem B7795763 : Blo 1538466 7795763 := bstep (se 1 (by rfl) ⟨5846822, by rfl⟩ : syracuseStep 7795763 = 11693645) B11693645
theorem B39457853 : Blo 1538466 39457853 := bstep (se 3 (by rfl) ⟨7398347, by rfl⟩ : syracuseStep 39457853 = 14796695) B14796695
theorem B1643599 : Blo 1538466 1643599 := bstep (se 1 (by rfl) ⟨1232699, by rfl⟩ : syracuseStep 1643599 = 2465399) B2465399
theorem B3896819 : Blo 1538466 3896819 := bstep (se 1 (by rfl) ⟨2922614, by rfl⟩ : syracuseStep 3896819 = 5845229) B5845229
theorem B3462695 : Blo 1538466 3462695 := bstep (se 1 (by rfl) ⟨2597021, by rfl⟩ : syracuseStep 3462695 = 5194043) B5194043
theorem B2307707 : Blo 1538466 2307707 := bstep (se 1 (by rfl) ⟨1730780, by rfl⟩ : syracuseStep 2307707 = 3461561) B3461561
theorem B3897031 : Blo 1538466 3897031 := bstep (se 1 (by rfl) ⟨2922773, by rfl⟩ : syracuseStep 3897031 = 5845547) B5845547
theorem B547190477 : Blo 1538466 547190477 := bstep (se 3 (by rfl) ⟨102598214, by rfl⟩ : syracuseStep 547190477 = 205196429) B205196429
theorem B2307833 : Blo 1538466 2307833 := bstep (se 2 (by rfl) ⟨865437, by rfl⟩ : syracuseStep 2307833 = 1730875) B1730875
theorem B23705387 : Blo 1538466 23705387 := bstep (se 1 (by rfl) ⟨17779040, by rfl⟩ : syracuseStep 23705387 = 35558081) B35558081
theorem B2307935 : Blo 1538466 2307935 := bstep (se 1 (by rfl) ⟨1730951, by rfl⟩ : syracuseStep 2307935 = 3461903) B3461903
theorem B2307947 : Blo 1538466 2307947 := bstep (se 1 (by rfl) ⟨1730960, by rfl⟩ : syracuseStep 2307947 = 3461921) B3461921
theorem B3463019 : Blo 1538466 3463019 := bstep (se 1 (by rfl) ⟨2597264, by rfl⟩ : syracuseStep 3463019 = 5194529) B5194529
theorem B3463073 : Blo 1538466 3463073 := bstep (se 2 (by rfl) ⟨1298652, by rfl⟩ : syracuseStep 3463073 = 2597305) B2597305
theorem B2963375 : Blo 1538466 2963375 := bstep (se 1 (by rfl) ⟨2222531, by rfl⟩ : syracuseStep 2963375 = 4445063) B4445063
theorem B240007121 : Blo 1538466 240007121 := bstep (se 2 (by rfl) ⟨90002670, by rfl⟩ : syracuseStep 240007121 = 180005341) B180005341
theorem B4159495 : Blo 1538466 4159495 := bstep (se 1 (by rfl) ⟨3119621, by rfl⟩ : syracuseStep 4159495 = 6239243) B6239243
theorem B151820345 : Blo 1538466 151820345 := bstep (se 2 (by rfl) ⟨56932629, by rfl⟩ : syracuseStep 151820345 = 113865259) B113865259
theorem B2308175 : Blo 1538466 2308175 := bstep (se 1 (by rfl) ⟨1731131, by rfl⟩ : syracuseStep 2308175 = 3462263) B3462263
theorem B2308295 : Blo 1538466 2308295 := bstep (se 1 (by rfl) ⟨1731221, by rfl⟩ : syracuseStep 2308295 = 3462443) B3462443
theorem B3463415 : Blo 1538466 3463415 := bstep (se 1 (by rfl) ⟨2597561, by rfl⟩ : syracuseStep 3463415 = 5195123) B5195123
theorem B2922743 : Blo 1538466 2922743 := bstep (se 1 (by rfl) ⟨2192057, by rfl⟩ : syracuseStep 2922743 = 4384115) B4384115
theorem B2308457 : Blo 1538466 2308457 := bstep (se 2 (by rfl) ⟨865671, by rfl⟩ : syracuseStep 2308457 = 1731343) B1731343
theorem B11557253 : Blo 1538466 11557253 := bstep (se 4 (by rfl) ⟨1083492, by rfl⟩ : syracuseStep 11557253 = 2166985) B2166985
theorem B2922895 : Blo 1538466 2922895 := bstep (se 1 (by rfl) ⟨2192171, by rfl⟩ : syracuseStep 2922895 = 4384343) B4384343
theorem B1538479 : Blo 1538466 1538479 := bstep (se 1 (by rfl) ⟨1153859, by rfl⟩ : syracuseStep 1538479 = 2307719) B2307719
theorem B1849775 : Blo 1538466 1849775 := bstep (se 1 (by rfl) ⟨1387331, by rfl⟩ : syracuseStep 1849775 = 2774663) B2774663
theorem B2308535 : Blo 1538466 2308535 := bstep (se 1 (by rfl) ⟨1731401, by rfl⟩ : syracuseStep 2308535 = 3462803) B3462803
theorem B1538503 : Blo 1538466 1538503 := bstep (se 1 (by rfl) ⟨1153877, by rfl⟩ : syracuseStep 1538503 = 2307755) B2307755
theorem B1538523 : Blo 1538466 1538523 := bstep (se 1 (by rfl) ⟨1153892, by rfl⟩ : syracuseStep 1538523 = 2307785) B2307785
theorem B2308571 : Blo 1538466 2308571 := bstep (se 1 (by rfl) ⟨1731428, by rfl⟩ : syracuseStep 2308571 = 3462857) B3462857
theorem B1538599 : Blo 1538466 1538599 := bstep (se 1 (by rfl) ⟨1153949, by rfl⟩ : syracuseStep 1538599 = 2307899) B2307899
theorem B1538639 : Blo 1538466 1538639 := bstep (se 1 (by rfl) ⟨1153979, by rfl⟩ : syracuseStep 1538639 = 2307959) B2307959
theorem B1538655 : Blo 1538466 1538655 := bstep (se 1 (by rfl) ⟨1153991, by rfl⟩ : syracuseStep 1538655 = 2307983) B2307983
theorem B3897953 : Blo 1538466 3897953 := bstep (se 2 (by rfl) ⟨1461732, by rfl⟩ : syracuseStep 3897953 = 2923465) B2923465
theorem B1538683 : Blo 1538466 1538683 := bstep (se 1 (by rfl) ⟨1154012, by rfl⟩ : syracuseStep 1538683 = 2308025) B2308025
theorem B1538735 : Blo 1538466 1538735 := bstep (se 1 (by rfl) ⟨1154051, by rfl⟩ : syracuseStep 1538735 = 2308103) B2308103
theorem B1538759 : Blo 1538466 1538759 := bstep (se 1 (by rfl) ⟨1154069, by rfl⟩ : syracuseStep 1538759 = 2308139) B2308139
theorem B1538779 : Blo 1538466 1538779 := bstep (se 1 (by rfl) ⟨1154084, by rfl⟩ : syracuseStep 1538779 = 2308169) B2308169
theorem B5192477 : Blo 1538466 5192477 := bstep (se 3 (by rfl) ⟨973589, by rfl⟩ : syracuseStep 5192477 = 1947179) B1947179
theorem B1538855 : Blo 1538466 1538855 := bstep (se 1 (by rfl) ⟨1154141, by rfl⟩ : syracuseStep 1538855 = 2308283) B2308283
theorem B3464009 : Blo 1538466 3464009 := bstep (se 2 (by rfl) ⟨1299003, by rfl⟩ : syracuseStep 3464009 = 2598007) B2598007
theorem B1538895 : Blo 1538466 1538895 := bstep (se 1 (by rfl) ⟨1154171, by rfl⟩ : syracuseStep 1538895 = 2308343) B2308343
theorem B1538911 : Blo 1538466 1538911 := bstep (se 1 (by rfl) ⟨1154183, by rfl⟩ : syracuseStep 1538911 = 2308367) B2308367
theorem B1538939 : Blo 1538466 1538939 := bstep (se 1 (by rfl) ⟨1154204, by rfl⟩ : syracuseStep 1538939 = 2308409) B2308409
theorem B1538991 : Blo 1538466 1538991 := bstep (se 1 (by rfl) ⟨1154243, by rfl⟩ : syracuseStep 1538991 = 2308487) B2308487
theorem B2309039 : Blo 1538466 2309039 := bstep (se 1 (by rfl) ⟨1731779, by rfl⟩ : syracuseStep 2309039 = 3463559) B3463559
theorem B1539015 : Blo 1538466 1539015 := bstep (se 1 (by rfl) ⟨1154261, by rfl⟩ : syracuseStep 1539015 = 2308523) B2308523
theorem B1539035 : Blo 1538466 1539035 := bstep (se 1 (by rfl) ⟨1154276, by rfl⟩ : syracuseStep 1539035 = 2308553) B2308553
theorem B2309129 : Blo 1538466 2309129 := bstep (se 2 (by rfl) ⟨865923, by rfl⟩ : syracuseStep 2309129 = 1731847) B1731847
theorem B1539111 : Blo 1538466 1539111 := bstep (se 1 (by rfl) ⟨1154333, by rfl⟩ : syracuseStep 1539111 = 2308667) B2308667
theorem B2309159 : Blo 1538466 2309159 := bstep (se 1 (by rfl) ⟨1731869, by rfl⟩ : syracuseStep 2309159 = 3463739) B3463739
theorem B1539151 : Blo 1538466 1539151 := bstep (se 1 (by rfl) ⟨1154363, by rfl⟩ : syracuseStep 1539151 = 2308727) B2308727
theorem B1539167 : Blo 1538466 1539167 := bstep (se 1 (by rfl) ⟨1154375, by rfl⟩ : syracuseStep 1539167 = 2308751) B2308751
theorem B1539195 : Blo 1538466 1539195 := bstep (se 1 (by rfl) ⟨1154396, by rfl⟩ : syracuseStep 1539195 = 2308793) B2308793
theorem B2309243 : Blo 1538466 2309243 := bstep (se 1 (by rfl) ⟨1731932, by rfl⟩ : syracuseStep 2309243 = 3463865) B3463865
theorem B1539247 : Blo 1538466 1539247 := bstep (se 1 (by rfl) ⟨1154435, by rfl⟩ : syracuseStep 1539247 = 2308871) B2308871
theorem B24968387 : Blo 1538466 24968387 := bstep (se 1 (by rfl) ⟨18726290, by rfl⟩ : syracuseStep 24968387 = 37452581) B37452581
theorem B1539271 : Blo 1538466 1539271 := bstep (se 1 (by rfl) ⟨1154453, by rfl⟩ : syracuseStep 1539271 = 2308907) B2308907
theorem B1539291 : Blo 1538466 1539291 := bstep (se 1 (by rfl) ⟨1154468, by rfl⟩ : syracuseStep 1539291 = 2308937) B2308937
theorem B15834359 : Blo 1538466 15834359 := bstep (se 1 (by rfl) ⟨11875769, by rfl⟩ : syracuseStep 15834359 = 23751539) B23751539
theorem B2309369 : Blo 1538466 2309369 := bstep (se 2 (by rfl) ⟨866013, by rfl⟩ : syracuseStep 2309369 = 1732027) B1732027
theorem B1539367 : Blo 1538466 1539367 := bstep (se 1 (by rfl) ⟨1154525, by rfl⟩ : syracuseStep 1539367 = 2309051) B2309051
theorem B1539407 : Blo 1538466 1539407 := bstep (se 1 (by rfl) ⟨1154555, by rfl⟩ : syracuseStep 1539407 = 2309111) B2309111
theorem B1539423 : Blo 1538466 1539423 := bstep (se 1 (by rfl) ⟨1154567, by rfl⟩ : syracuseStep 1539423 = 2309135) B2309135
theorem B2309471 : Blo 1538466 2309471 := bstep (se 1 (by rfl) ⟨1732103, by rfl⟩ : syracuseStep 2309471 = 3464207) B3464207
theorem B2309483 : Blo 1538466 2309483 := bstep (se 1 (by rfl) ⟨1732112, by rfl⟩ : syracuseStep 2309483 = 3464225) B3464225
theorem B1539451 : Blo 1538466 1539451 := bstep (se 1 (by rfl) ⟨1154588, by rfl⟩ : syracuseStep 1539451 = 2309177) B2309177
theorem B18972029 : Blo 1538466 18972029 := bstep (se 3 (by rfl) ⟨3557255, by rfl⟩ : syracuseStep 18972029 = 7114511) B7114511
theorem B1539503 : Blo 1538466 1539503 := bstep (se 1 (by rfl) ⟨1154627, by rfl⟩ : syracuseStep 1539503 = 2309255) B2309255
theorem B2596279 : Blo 1538466 2596279 := bstep (se 1 (by rfl) ⟨1947209, by rfl⟩ : syracuseStep 2596279 = 3894419) B3894419
theorem B1539527 : Blo 1538466 1539527 := bstep (se 1 (by rfl) ⟨1154645, by rfl⟩ : syracuseStep 1539527 = 2309291) B2309291
theorem B5193179 : Blo 1538466 5193179 := bstep (se 1 (by rfl) ⟨3894884, by rfl⟩ : syracuseStep 5193179 = 7789769) B7789769
theorem B1539547 : Blo 1538466 1539547 := bstep (se 1 (by rfl) ⟨1154660, by rfl⟩ : syracuseStep 1539547 = 2309321) B2309321
theorem B1539623 : Blo 1538466 1539623 := bstep (se 1 (by rfl) ⟨1154717, by rfl⟩ : syracuseStep 1539623 = 2309435) B2309435
theorem B4931131 : Blo 1538466 4931131 := bstep (se 1 (by rfl) ⟨3698348, by rfl⟩ : syracuseStep 4931131 = 7396697) B7396697
theorem B1539663 : Blo 1538466 1539663 := bstep (se 1 (by rfl) ⟨1154747, by rfl⟩ : syracuseStep 1539663 = 2309495) B2309495
theorem B2309711 : Blo 1538466 2309711 := bstep (se 1 (by rfl) ⟨1732283, by rfl⟩ : syracuseStep 2309711 = 3464567) B3464567
theorem B1539679 : Blo 1538466 1539679 := bstep (se 1 (by rfl) ⟨1154759, by rfl⟩ : syracuseStep 1539679 = 2309519) B2309519
theorem B3464801 : Blo 1538466 3464801 := bstep (se 2 (by rfl) ⟨1299300, by rfl⟩ : syracuseStep 3464801 = 2598601) B2598601
theorem B2596475 : Blo 1538466 2596475 := bstep (se 1 (by rfl) ⟨1947356, by rfl⟩ : syracuseStep 2596475 = 3894713) B3894713
theorem B1539707 : Blo 1538466 1539707 := bstep (se 1 (by rfl) ⟨1154780, by rfl⟩ : syracuseStep 1539707 = 2309561) B2309561
theorem B4931207 : Blo 1538466 4931207 := bstep (se 1 (by rfl) ⟨3698405, by rfl⟩ : syracuseStep 4931207 = 7396811) B7396811
theorem B1539759 : Blo 1538466 1539759 := bstep (se 1 (by rfl) ⟨1154819, by rfl⟩ : syracuseStep 1539759 = 2309639) B2309639
theorem B1539783 : Blo 1538466 1539783 := bstep (se 1 (by rfl) ⟨1154837, by rfl⟩ : syracuseStep 1539783 = 2309675) B2309675
theorem B2309831 : Blo 1538466 2309831 := bstep (se 1 (by rfl) ⟨1732373, by rfl⟩ : syracuseStep 2309831 = 3464747) B3464747
theorem B1539803 : Blo 1538466 1539803 := bstep (se 1 (by rfl) ⟨1154852, by rfl⟩ : syracuseStep 1539803 = 2309705) B2309705
theorem B1539879 : Blo 1538466 1539879 := bstep (se 1 (by rfl) ⟨1154909, by rfl⟩ : syracuseStep 1539879 = 2309819) B2309819
theorem B4931401 : Blo 1538466 4931401 := bstep (se 2 (by rfl) ⟨1849275, by rfl⟩ : syracuseStep 4931401 = 3698551) B3698551
theorem B1539919 : Blo 1538466 1539919 := bstep (se 1 (by rfl) ⟨1154939, by rfl⟩ : syracuseStep 1539919 = 2309879) B2309879
theorem B1539935 : Blo 1538466 1539935 := bstep (se 1 (by rfl) ⟨1154951, by rfl⟩ : syracuseStep 1539935 = 2309903) B2309903
theorem B1539963 : Blo 1538466 1539963 := bstep (se 1 (by rfl) ⟨1154972, by rfl⟩ : syracuseStep 1539963 = 2309945) B2309945
theorem B252731339 : Blo 1538466 252731339 := bstep (se 1 (by rfl) ⟨189548504, by rfl⟩ : syracuseStep 252731339 = 379097009) B379097009
theorem B5545993 : Blo 1538466 5545993 := bstep (se 2 (by rfl) ⟨2079747, by rfl⟩ : syracuseStep 5545993 = 4159495) B4159495
theorem B4383067 : Blo 1538466 4383067 := bstep (se 1 (by rfl) ⟨3287300, by rfl⟩ : syracuseStep 4383067 = 6574601) B6574601
theorem B2597231 : Blo 1538466 2597231 := bstep (se 1 (by rfl) ⟨1947923, by rfl⟩ : syracuseStep 2597231 = 3895847) B3895847
theorem B5194259 : Blo 1538466 5194259 := bstep (se 1 (by rfl) ⟨3895694, by rfl⟩ : syracuseStep 5194259 = 7791389) B7791389
theorem B2597447 : Blo 1538466 2597447 := bstep (se 1 (by rfl) ⟨1948085, by rfl⟩ : syracuseStep 2597447 = 3896171) B3896171
theorem B106603127 : Blo 1538466 106603127 := bstep (se 1 (by rfl) ⟨79952345, by rfl⟩ : syracuseStep 106603127 = 159904691) B159904691
theorem B26305235 : Blo 1538466 26305235 := bstep (se 1 (by rfl) ⟨19728926, by rfl⟩ : syracuseStep 26305235 = 39457853) B39457853
theorem B2597879 : Blo 1538466 2597879 := bstep (se 1 (by rfl) ⟨1948409, by rfl⟩ : syracuseStep 2597879 = 3896819) B3896819
theorem B30819341 : Blo 1538466 30819341 := bstep (se 3 (by rfl) ⟨5778626, by rfl⟩ : syracuseStep 30819341 = 11557253) B11557253
theorem B7791713 : Blo 1538466 7791713 := bstep (se 2 (by rfl) ⟨2921892, by rfl⟩ : syracuseStep 7791713 = 5843785) B5843785
theorem B4932733 : Blo 1538466 4932733 := bstep (se 3 (by rfl) ⟨924887, by rfl⟩ : syracuseStep 4932733 = 1849775) B1849775
theorem B15803591 : Blo 1538466 15803591 := bstep (se 1 (by rfl) ⟨11852693, by rfl⟩ : syracuseStep 15803591 = 23705387) B23705387
theorem B1975583 : Blo 1538466 1975583 := bstep (se 1 (by rfl) ⟨1481687, by rfl⟩ : syracuseStep 1975583 = 2963375) B2963375
theorem B101213563 : Blo 1538466 101213563 := bstep (se 1 (by rfl) ⟨75910172, by rfl⟩ : syracuseStep 101213563 = 151820345) B151820345
theorem B12830075 : Blo 1538466 12830075 := bstep (se 1 (by rfl) ⟨9622556, by rfl⟩ : syracuseStep 12830075 = 19245113) B19245113
theorem B17532449 : Blo 1538466 17532449 := bstep (se 2 (by rfl) ⟨6574668, by rfl⟩ : syracuseStep 17532449 = 13149337) B13149337
theorem B2598635 : Blo 1538466 2598635 := bstep (se 1 (by rfl) ⟨1948976, by rfl⟩ : syracuseStep 2598635 = 3897953) B3897953
theorem B7899169 : Blo 1538466 7899169 := bstep (se 2 (by rfl) ⟨2962188, by rfl⟩ : syracuseStep 7899169 = 5924377) B5924377
theorem B5196041 : Blo 1538466 5196041 := bstep (se 2 (by rfl) ⟨1948515, by rfl⟩ : syracuseStep 5196041 = 3897031) B3897031
theorem B1730983 : Blo 1538466 1730983 := bstep (se 1 (by rfl) ⟨1298237, by rfl⟩ : syracuseStep 1730983 = 2596475) B2596475
theorem B3287471 : Blo 1538466 3287471 := bstep (se 1 (by rfl) ⟨2465603, by rfl⟩ : syracuseStep 3287471 = 4931207) B4931207
theorem B168487559 : Blo 1538466 168487559 := bstep (se 1 (by rfl) ⟨126365669, by rfl⟩ : syracuseStep 168487559 = 252731339) B252731339
theorem B3697579 : Blo 1538466 3697579 := bstep (se 1 (by rfl) ⟨2773184, by rfl⟩ : syracuseStep 3697579 = 5546369) B5546369
theorem B33295333 : Blo 1538466 33295333 := bstep (se 4 (by rfl) ⟨3121437, by rfl⟩ : syracuseStep 33295333 = 6242875) B6242875
theorem B1731559 : Blo 1538466 1731559 := bstep (se 1 (by rfl) ⟨1298669, by rfl⟩ : syracuseStep 1731559 = 2597339) B2597339
theorem B44969093 : Blo 1538466 44969093 := bstep (se 4 (by rfl) ⟨4215852, by rfl⟩ : syracuseStep 44969093 = 8431705) B8431705
theorem B47369395 : Blo 1538466 47369395 := bstep (se 1 (by rfl) ⟨35527046, by rfl⟩ : syracuseStep 47369395 = 71054093) B71054093
theorem B7793981 : Blo 1538466 7793981 := bstep (se 3 (by rfl) ⟨1461371, by rfl⟩ : syracuseStep 7793981 = 2922743) B2922743
theorem B5197175 : Blo 1538466 5197175 := bstep (se 1 (by rfl) ⟨3897881, by rfl⟩ : syracuseStep 5197175 = 7795763) B7795763
theorem B3894743 : Blo 1538466 3894743 := bstep (se 1 (by rfl) ⟨2921057, by rfl⟩ : syracuseStep 3894743 = 5842115) B5842115
theorem B5844575 : Blo 1538466 5844575 := bstep (se 1 (by rfl) ⟨4383431, by rfl⟩ : syracuseStep 5844575 = 8766863) B8766863
theorem B5844743 : Blo 1538466 5844743 := bstep (se 1 (by rfl) ⟨4383557, by rfl⟩ : syracuseStep 5844743 = 8767115) B8767115
theorem B3895087 : Blo 1538466 3895087 := bstep (se 1 (by rfl) ⟨2921315, by rfl⟩ : syracuseStep 3895087 = 5842631) B5842631
theorem B364793651 : Blo 1538466 364793651 := bstep (se 1 (by rfl) ⟨273595238, by rfl⟩ : syracuseStep 364793651 = 547190477) B547190477
theorem B3698713 : Blo 1538466 3698713 := bstep (se 2 (by rfl) ⟨1387017, by rfl⟩ : syracuseStep 3698713 = 2774035) B2774035
theorem B2191465 : Blo 1538466 2191465 := bstep (se 2 (by rfl) ⟨821799, by rfl⟩ : syracuseStep 2191465 = 1643599) B1643599
theorem B17535365 : Blo 1538466 17535365 := bstep (se 4 (by rfl) ⟨1643940, by rfl⟩ : syracuseStep 17535365 = 3287881) B3287881
theorem B3895735 : Blo 1538466 3895735 := bstep (se 1 (by rfl) ⟨2921801, by rfl⟩ : syracuseStep 3895735 = 5843603) B5843603
theorem B3461651 : Blo 1538466 3461651 := bstep (se 1 (by rfl) ⟨2596238, by rfl⟩ : syracuseStep 3461651 = 5192477) B5192477
theorem B3461705 : Blo 1538466 3461705 := bstep (se 2 (by rfl) ⟨1298139, by rfl⟩ : syracuseStep 3461705 = 2596279) B2596279
theorem B6574841 : Blo 1538466 6574841 := bstep (se 2 (by rfl) ⟨2465565, by rfl⟩ : syracuseStep 6574841 = 4931131) B4931131
theorem B10556239 : Blo 1538466 10556239 := bstep (se 1 (by rfl) ⟨7917179, by rfl⟩ : syracuseStep 10556239 = 15834359) B15834359
theorem B3462119 : Blo 1538466 3462119 := bstep (se 1 (by rfl) ⟨2596589, by rfl⟩ : syracuseStep 3462119 = 5193179) B5193179
theorem B3699751 : Blo 1538466 3699751 := bstep (se 1 (by rfl) ⟨2774813, by rfl⟩ : syracuseStep 3699751 = 5549627) B5549627
theorem B6575201 : Blo 1538466 6575201 := bstep (se 2 (by rfl) ⟨2465700, by rfl⟩ : syracuseStep 6575201 = 4931401) B4931401
theorem B7394429 : Blo 1538466 7394429 := bstep (se 3 (by rfl) ⟨1386455, by rfl⟩ : syracuseStep 7394429 = 2772911) B2772911
theorem B6239375 : Blo 1538466 6239375 := bstep (se 1 (by rfl) ⟨4679531, by rfl⟩ : syracuseStep 6239375 = 9359063) B9359063
theorem B5846215 : Blo 1538466 5846215 := bstep (se 1 (by rfl) ⟨4384661, by rfl⟩ : syracuseStep 5846215 = 8769323) B8769323
theorem B3462497 : Blo 1538466 3462497 := bstep (se 2 (by rfl) ⟨1298436, by rfl⟩ : syracuseStep 3462497 = 2596873) B2596873
theorem B2921825 : Blo 1538466 2921825 := bstep (se 2 (by rfl) ⟨1095684, by rfl⟩ : syracuseStep 2921825 = 2191369) B2191369
theorem B53302643 : Blo 1538466 53302643 := bstep (se 1 (by rfl) ⟨39976982, by rfl⟩ : syracuseStep 53302643 = 79953965) B79953965
theorem B5264801 : Blo 1538466 5264801 := bstep (se 2 (by rfl) ⟨1974300, by rfl⟩ : syracuseStep 5264801 = 3948601) B3948601
theorem B3462587 : Blo 1538466 3462587 := bstep (se 1 (by rfl) ⟨2596940, by rfl⟩ : syracuseStep 3462587 = 5193881) B5193881
theorem B4158935 : Blo 1538466 4158935 := bstep (se 1 (by rfl) ⟨3119201, by rfl⟩ : syracuseStep 4158935 = 6238403) B6238403
theorem B3511801 : Blo 1538466 3511801 := bstep (se 2 (by rfl) ⟨1316925, by rfl⟩ : syracuseStep 3511801 = 2633851) B2633851
theorem B3462713 : Blo 1538466 3462713 := bstep (se 2 (by rfl) ⟨1298517, by rfl⟩ : syracuseStep 3462713 = 2597035) B2597035
theorem B1848895 : Blo 1538466 1848895 := bstep (se 1 (by rfl) ⟨1386671, by rfl⟩ : syracuseStep 1848895 = 2773343) B2773343
theorem B2307881 : Blo 1538466 2307881 := bstep (se 2 (by rfl) ⟨865455, by rfl⟩ : syracuseStep 2307881 = 1730911) B1730911
theorem B2307887 : Blo 1538466 2307887 := bstep (se 1 (by rfl) ⟨1730915, by rfl⟩ : syracuseStep 2307887 = 3461831) B3461831
theorem B3897143 : Blo 1538466 3897143 := bstep (se 1 (by rfl) ⟨2922857, by rfl⟩ : syracuseStep 3897143 = 5845715) B5845715
theorem B3897193 : Blo 1538466 3897193 := bstep (se 2 (by rfl) ⟨1461447, by rfl⟩ : syracuseStep 3897193 = 2922895) B2922895
theorem B3463379 : Blo 1538466 3463379 := bstep (se 1 (by rfl) ⟨2597534, by rfl⟩ : syracuseStep 3463379 = 5195069) B5195069
theorem B7788797 : Blo 1538466 7788797 := bstep (se 3 (by rfl) ⟨1460399, by rfl⟩ : syracuseStep 7788797 = 2920799) B2920799
theorem B2308361 : Blo 1538466 2308361 := bstep (se 2 (by rfl) ⟨865635, by rfl⟩ : syracuseStep 2308361 = 1731271) B1731271
theorem B3463433 : Blo 1538466 3463433 := bstep (se 2 (by rfl) ⟨1298787, by rfl⟩ : syracuseStep 3463433 = 2597575) B2597575
theorem B8763673 : Blo 1538466 8763673 := bstep (se 2 (by rfl) ⟨3286377, by rfl⟩ : syracuseStep 8763673 = 6572755) B6572755
theorem B50592077 : Blo 1538466 50592077 := bstep (se 3 (by rfl) ⟨9486014, by rfl⟩ : syracuseStep 50592077 = 18972029) B18972029
theorem B2308463 : Blo 1538466 2308463 := bstep (se 1 (by rfl) ⟨1731347, by rfl⟩ : syracuseStep 2308463 = 3462695) B3462695
theorem B1538471 : Blo 1538466 1538471 := bstep (se 1 (by rfl) ⟨1153853, by rfl⟩ : syracuseStep 1538471 = 2307707) B2307707
theorem B3463649 : Blo 1538466 3463649 := bstep (se 2 (by rfl) ⟨1298868, by rfl⟩ : syracuseStep 3463649 = 2597737) B2597737
theorem B1538555 : Blo 1538466 1538555 := bstep (se 1 (by rfl) ⟨1153916, by rfl⟩ : syracuseStep 1538555 = 2307833) B2307833
theorem B1538623 : Blo 1538466 1538623 := bstep (se 1 (by rfl) ⟨1153967, by rfl⟩ : syracuseStep 1538623 = 2307935) B2307935
theorem B8886847 : Blo 1538466 8886847 := bstep (se 1 (by rfl) ⟨6665135, by rfl⟩ : syracuseStep 8886847 = 13330271) B13330271
theorem B1538631 : Blo 1538466 1538631 := bstep (se 1 (by rfl) ⟨1153973, by rfl⟩ : syracuseStep 1538631 = 2307947) B2307947
theorem B2308679 : Blo 1538466 2308679 := bstep (se 1 (by rfl) ⟨1731509, by rfl⟩ : syracuseStep 2308679 = 3463019) B3463019
theorem B7494223 : Blo 1538466 7494223 := bstep (se 1 (by rfl) ⟨5620667, by rfl⟩ : syracuseStep 7494223 = 11241335) B11241335
theorem B2308715 : Blo 1538466 2308715 := bstep (se 1 (by rfl) ⟨1731536, by rfl⟩ : syracuseStep 2308715 = 3463073) B3463073
theorem B160004747 : Blo 1538466 160004747 := bstep (se 1 (by rfl) ⟨120003560, by rfl⟩ : syracuseStep 160004747 = 240007121) B240007121
theorem B1538783 : Blo 1538466 1538783 := bstep (se 1 (by rfl) ⟨1154087, by rfl⟩ : syracuseStep 1538783 = 2308175) B2308175
theorem B3463955 : Blo 1538466 3463955 := bstep (se 1 (by rfl) ⟨2597966, by rfl⟩ : syracuseStep 3463955 = 5195933) B5195933
theorem B2923283 : Blo 1538466 2923283 := bstep (se 1 (by rfl) ⟨2192462, by rfl⟩ : syracuseStep 2923283 = 4384925) B4384925
theorem B1538863 : Blo 1538466 1538863 := bstep (se 1 (by rfl) ⟨1154147, by rfl⟩ : syracuseStep 1538863 = 2308295) B2308295
theorem B2308943 : Blo 1538466 2308943 := bstep (se 1 (by rfl) ⟨1731707, by rfl⟩ : syracuseStep 2308943 = 3463415) B3463415
theorem B1538971 : Blo 1538466 1538971 := bstep (se 1 (by rfl) ⟨1154228, by rfl⟩ : syracuseStep 1538971 = 2308457) B2308457
theorem B15612857 : Blo 1538466 15612857 := bstep (se 2 (by rfl) ⟨5854821, by rfl⟩ : syracuseStep 15612857 = 11709643) B11709643
theorem B1539023 : Blo 1538466 1539023 := bstep (se 1 (by rfl) ⟨1154267, by rfl⟩ : syracuseStep 1539023 = 2308535) B2308535
theorem B1539047 : Blo 1538466 1539047 := bstep (se 1 (by rfl) ⟨1154285, by rfl⟩ : syracuseStep 1539047 = 2308571) B2308571
theorem B7789607 : Blo 1538466 7789607 := bstep (se 1 (by rfl) ⟨5842205, by rfl⟩ : syracuseStep 7789607 = 11684411) B11684411
theorem B4381735 : Blo 1538466 4381735 := bstep (se 1 (by rfl) ⟨3286301, by rfl⟩ : syracuseStep 4381735 = 6572603) B6572603
theorem B5266471 : Blo 1538466 5266471 := bstep (se 1 (by rfl) ⟨3949853, by rfl⟩ : syracuseStep 5266471 = 7899707) B7899707
theorem B3464315 : Blo 1538466 3464315 := bstep (se 1 (by rfl) ⟨2598236, by rfl⟩ : syracuseStep 3464315 = 5196473) B5196473
theorem B2309339 : Blo 1538466 2309339 := bstep (se 1 (by rfl) ⟨1732004, by rfl⟩ : syracuseStep 2309339 = 3464009) B3464009
theorem B3464441 : Blo 1538466 3464441 := bstep (se 2 (by rfl) ⟨1299165, by rfl⟩ : syracuseStep 3464441 = 2598331) B2598331
theorem B1539359 : Blo 1538466 1539359 := bstep (se 1 (by rfl) ⟨1154519, by rfl⟩ : syracuseStep 1539359 = 2309039) B2309039
theorem B1539419 : Blo 1538466 1539419 := bstep (se 1 (by rfl) ⟨1154564, by rfl⟩ : syracuseStep 1539419 = 2309129) B2309129
theorem B1539439 : Blo 1538466 1539439 := bstep (se 1 (by rfl) ⟨1154579, by rfl⟩ : syracuseStep 1539439 = 2309159) B2309159
theorem B2309513 : Blo 1538466 2309513 := bstep (se 2 (by rfl) ⟨866067, by rfl⟩ : syracuseStep 2309513 = 1732135) B1732135
theorem B3464585 : Blo 1538466 3464585 := bstep (se 2 (by rfl) ⟨1299219, by rfl⟩ : syracuseStep 3464585 = 2598439) B2598439
theorem B1539495 : Blo 1538466 1539495 := bstep (se 1 (by rfl) ⟨1154621, by rfl⟩ : syracuseStep 1539495 = 2309243) B2309243
theorem B16645591 : Blo 1538466 16645591 := bstep (se 1 (by rfl) ⟨12484193, by rfl⟩ : syracuseStep 16645591 = 24968387) B24968387
theorem B4382201 : Blo 1538466 4382201 := bstep (se 2 (by rfl) ⟨1643325, by rfl⟩ : syracuseStep 4382201 = 3286651) B3286651
theorem B1539579 : Blo 1538466 1539579 := bstep (se 1 (by rfl) ⟨1154684, by rfl⟩ : syracuseStep 1539579 = 2309369) B2309369
theorem B3464711 : Blo 1538466 3464711 := bstep (se 1 (by rfl) ⟨2598533, by rfl⟩ : syracuseStep 3464711 = 5197067) B5197067
theorem B1539647 : Blo 1538466 1539647 := bstep (se 1 (by rfl) ⟨1154735, by rfl⟩ : syracuseStep 1539647 = 2309471) B2309471
theorem B1539655 : Blo 1538466 1539655 := bstep (se 1 (by rfl) ⟨1154741, by rfl⟩ : syracuseStep 1539655 = 2309483) B2309483
theorem B3464891 : Blo 1538466 3464891 := bstep (se 1 (by rfl) ⟨2598668, by rfl⟩ : syracuseStep 3464891 = 5197337) B5197337
theorem B1539807 : Blo 1538466 1539807 := bstep (se 1 (by rfl) ⟨1154855, by rfl⟩ : syracuseStep 1539807 = 2309711) B2309711
theorem B2309867 : Blo 1538466 2309867 := bstep (se 1 (by rfl) ⟨1732400, by rfl⟩ : syracuseStep 2309867 = 3464801) B3464801
theorem B10534697 : Blo 1538466 10534697 := bstep (se 2 (by rfl) ⟨3950511, by rfl⟩ : syracuseStep 10534697 = 7901023) B7901023
theorem B1539887 : Blo 1538466 1539887 := bstep (se 1 (by rfl) ⟨1154915, by rfl⟩ : syracuseStep 1539887 = 2309831) B2309831
theorem B44965813 : Blo 1538466 44965813 := bstep (se 5 (by rfl) ⟨2107772, by rfl⟩ : syracuseStep 44965813 = 4215545) B4215545
theorem B4931617 : Blo 1538466 4931617 := bstep (se 2 (by rfl) ⟨1849356, by rfl⟩ : syracuseStep 4931617 = 3698713) B3698713
theorem B11690243 : Blo 1538466 11690243 := bstep (se 1 (by rfl) ⟨8767682, by rfl⟩ : syracuseStep 11690243 = 17535365) B17535365
theorem B4383227 : Blo 1538466 4383227 := bstep (se 1 (by rfl) ⟨3287420, by rfl⟩ : syracuseStep 4383227 = 6574841) B6574841
theorem B5194313 : Blo 1538466 5194313 := bstep (se 2 (by rfl) ⟨1947867, by rfl⟩ : syracuseStep 5194313 = 3895735) B3895735
theorem B20546227 : Blo 1538466 20546227 := bstep (se 1 (by rfl) ⟨15409670, by rfl⟩ : syracuseStep 20546227 = 30819341) B30819341
theorem B5194475 : Blo 1538466 5194475 := bstep (se 1 (by rfl) ⟨3895856, by rfl⟩ : syracuseStep 5194475 = 7791713) B7791713
theorem B4383467 : Blo 1538466 4383467 := bstep (se 1 (by rfl) ⟨3287600, by rfl⟩ : syracuseStep 4383467 = 6575201) B6575201
theorem B5268221 : Blo 1538466 5268221 := bstep (se 3 (by rfl) ⟨987791, by rfl⟩ : syracuseStep 5268221 = 1975583) B1975583
theorem B8553383 : Blo 1538466 8553383 := bstep (se 1 (by rfl) ⟨6415037, by rfl⟩ : syracuseStep 8553383 = 12830075) B12830075
theorem B14074985 : Blo 1538466 14074985 := bstep (se 2 (by rfl) ⟨5278119, by rfl⟩ : syracuseStep 14074985 = 10556239) B10556239
theorem B8766589 : Blo 1538466 8766589 := bstep (se 3 (by rfl) ⟨1643735, by rfl⟩ : syracuseStep 8766589 = 3287471) B3287471
theorem B2598095 : Blo 1538466 2598095 := bstep (se 1 (by rfl) ⟨1948571, by rfl⟩ : syracuseStep 2598095 = 3897143) B3897143
theorem B44393777 : Blo 1538466 44393777 := bstep (se 2 (by rfl) ⟨16647666, by rfl⟩ : syracuseStep 44393777 = 33295333) B33295333
theorem B5842313 : Blo 1538466 5842313 := bstep (se 2 (by rfl) ⟨2190867, by rfl⟩ : syracuseStep 5842313 = 4381735) B4381735
theorem B7021961 : Blo 1538466 7021961 := bstep (se 2 (by rfl) ⟨2633235, by rfl⟩ : syracuseStep 7021961 = 5266471) B5266471
theorem B4933001 : Blo 1538466 4933001 := bstep (se 2 (by rfl) ⟨1849875, by rfl⟩ : syracuseStep 4933001 = 3699751) B3699751
theorem B33728051 : Blo 1538466 33728051 := bstep (se 1 (by rfl) ⟨25296038, by rfl⟩ : syracuseStep 33728051 = 50592077) B50592077
theorem B106669831 : Blo 1538466 106669831 := bstep (se 1 (by rfl) ⟨80002373, by rfl⟩ : syracuseStep 106669831 = 160004747) B160004747
theorem B22194121 : Blo 1538466 22194121 := bstep (se 2 (by rfl) ⟨8322795, by rfl⟩ : syracuseStep 22194121 = 16645591) B16645591
theorem B5195987 : Blo 1538466 5195987 := bstep (se 1 (by rfl) ⟨3896990, by rfl⟩ : syracuseStep 5195987 = 7793981) B7793981
theorem B19720421 : Blo 1538466 19720421 := bstep (se 4 (by rfl) ⟨1848789, by rfl⟩ : syracuseStep 19720421 = 3697579) B3697579
theorem B5196257 : Blo 1538466 5196257 := bstep (se 2 (by rfl) ⟨1948596, by rfl⟩ : syracuseStep 5196257 = 3897193) B3897193
theorem B7023131 : Blo 1538466 7023131 := bstep (se 1 (by rfl) ⟨5267348, by rfl⟩ : syracuseStep 7023131 = 10534697) B10534697
theorem B18729605 : Blo 1538466 18729605 := bstep (se 4 (by rfl) ⟨1755900, by rfl⟩ : syracuseStep 18729605 = 3511801) B3511801
theorem B1731487 : Blo 1538466 1731487 := bstep (se 1 (by rfl) ⟨1298615, by rfl⟩ : syracuseStep 1731487 = 2597231) B2597231
theorem B11684897 : Blo 1538466 11684897 := bstep (se 2 (by rfl) ⟨4381836, by rfl⟩ : syracuseStep 11684897 = 8763673) B8763673
theorem B1731631 : Blo 1538466 1731631 := bstep (se 1 (by rfl) ⟨1298723, by rfl⟩ : syracuseStep 1731631 = 2597447) B2597447
theorem B71068751 : Blo 1538466 71068751 := bstep (se 1 (by rfl) ⟨53301563, by rfl⟩ : syracuseStep 71068751 = 106603127) B106603127
theorem B5844089 : Blo 1538466 5844089 := bstep (se 2 (by rfl) ⟨2191533, by rfl⟩ : syracuseStep 5844089 = 4383067) B4383067
theorem B1731919 : Blo 1538466 1731919 := bstep (se 1 (by rfl) ⟨1298939, by rfl⟩ : syracuseStep 1731919 = 2597879) B2597879
theorem B11849129 : Blo 1538466 11849129 := bstep (se 2 (by rfl) ⟨4443423, by rfl⟩ : syracuseStep 11849129 = 8886847) B8886847
theorem B3509867 : Blo 1538466 3509867 := bstep (se 1 (by rfl) ⟨2632400, by rfl⟩ : syracuseStep 3509867 = 5264801) B5264801
theorem B2772623 : Blo 1538466 2772623 := bstep (se 1 (by rfl) ⟨2079467, by rfl⟩ : syracuseStep 2772623 = 4158935) B4158935
theorem B1732423 : Blo 1538466 1732423 := bstep (se 1 (by rfl) ⟨1299317, by rfl⟩ : syracuseStep 1732423 = 2598635) B2598635
theorem B11685869 : Blo 1538466 11685869 := bstep (se 3 (by rfl) ⟨2191100, by rfl⟩ : syracuseStep 11685869 = 4382201) B4382201
theorem B7794953 : Blo 1538466 7794953 := bstep (se 2 (by rfl) ⟨2923107, by rfl⟩ : syracuseStep 7794953 = 5846215) B5846215
theorem B112325039 : Blo 1538466 112325039 := bstep (se 1 (by rfl) ⟨84243779, by rfl⟩ : syracuseStep 112325039 = 168487559) B168487559
theorem B134951417 : Blo 1538466 134951417 := bstep (se 2 (by rfl) ⟨50606781, by rfl⟩ : syracuseStep 134951417 = 101213563) B101213563
theorem B10408571 : Blo 1538466 10408571 := bstep (se 1 (by rfl) ⟨7806428, by rfl⟩ : syracuseStep 10408571 = 15612857) B15612857
theorem B168571637 : Blo 1538466 168571637 := bstep (se 5 (by rfl) ⟨7901795, by rfl⟩ : syracuseStep 168571637 = 15803591) B15803591
theorem B29979395 : Blo 1538466 29979395 := bstep (se 1 (by rfl) ⟨22484546, by rfl⟩ : syracuseStep 29979395 = 44969093) B44969093
theorem B3896383 : Blo 1538466 3896383 := bstep (se 1 (by rfl) ⟨2922287, by rfl⟩ : syracuseStep 3896383 = 5844575) B5844575
theorem B3896495 : Blo 1538466 3896495 := bstep (se 1 (by rfl) ⟨2922371, by rfl⟩ : syracuseStep 3896495 = 5844743) B5844743
theorem B59954417 : Blo 1538466 59954417 := bstep (se 2 (by rfl) ⟨22482906, by rfl⟩ : syracuseStep 59954417 = 44965813) B44965813
theorem B7394657 : Blo 1538466 7394657 := bstep (se 2 (by rfl) ⟨2772996, by rfl⟩ : syracuseStep 7394657 = 5545993) B5545993
theorem B10532225 : Blo 1538466 10532225 := bstep (se 2 (by rfl) ⟨3949584, by rfl⟩ : syracuseStep 10532225 = 7899169) B7899169
theorem B9860773 : Blo 1538466 9860773 := bstep (se 4 (by rfl) ⟨924447, by rfl⟩ : syracuseStep 9860773 = 1848895) B1848895
theorem B2307767 : Blo 1538466 2307767 := bstep (se 1 (by rfl) ⟨1730825, by rfl⟩ : syracuseStep 2307767 = 3461651) B3461651
theorem B3462839 : Blo 1538466 3462839 := bstep (se 1 (by rfl) ⟨2597129, by rfl⟩ : syracuseStep 3462839 = 5194259) B5194259
theorem B2307803 : Blo 1538466 2307803 := bstep (se 1 (by rfl) ⟨1730852, by rfl⟩ : syracuseStep 2307803 = 3461705) B3461705
theorem B17536823 : Blo 1538466 17536823 := bstep (se 1 (by rfl) ⟨13152617, by rfl⟩ : syracuseStep 17536823 = 26305235) B26305235
theorem B11687813 : Blo 1538466 11687813 := bstep (se 4 (by rfl) ⟨1095732, by rfl⟩ : syracuseStep 11687813 = 2191465) B2191465
theorem B2307977 : Blo 1538466 2307977 := bstep (se 2 (by rfl) ⟨865491, by rfl⟩ : syracuseStep 2307977 = 1730983) B1730983
theorem B2308079 : Blo 1538466 2308079 := bstep (se 1 (by rfl) ⟨1731059, by rfl⟩ : syracuseStep 2308079 = 3462119) B3462119
theorem B4929619 : Blo 1538466 4929619 := bstep (se 1 (by rfl) ⟨3697214, by rfl⟩ : syracuseStep 4929619 = 7394429) B7394429
theorem B4159583 : Blo 1538466 4159583 := bstep (se 1 (by rfl) ⟨3119687, by rfl⟩ : syracuseStep 4159583 = 6239375) B6239375
theorem B9992297 : Blo 1538466 9992297 := bstep (se 2 (by rfl) ⟨3747111, by rfl⟩ : syracuseStep 9992297 = 7494223) B7494223
theorem B2308331 : Blo 1538466 2308331 := bstep (se 1 (by rfl) ⟨1731248, by rfl⟩ : syracuseStep 2308331 = 3462497) B3462497
theorem B1947883 : Blo 1538466 1947883 := bstep (se 1 (by rfl) ⟨1460912, by rfl⟩ : syracuseStep 1947883 = 2921825) B2921825
theorem B35535095 : Blo 1538466 35535095 := bstep (se 1 (by rfl) ⟨26651321, by rfl⟩ : syracuseStep 35535095 = 53302643) B53302643
theorem B2308391 : Blo 1538466 2308391 := bstep (se 1 (by rfl) ⟨1731293, by rfl⟩ : syracuseStep 2308391 = 3462587) B3462587
theorem B11688299 : Blo 1538466 11688299 := bstep (se 1 (by rfl) ⟨8766224, by rfl⟩ : syracuseStep 11688299 = 17532449) B17532449
theorem B2308475 : Blo 1538466 2308475 := bstep (se 1 (by rfl) ⟨1731356, by rfl⟩ : syracuseStep 2308475 = 3462713) B3462713
theorem B1538587 : Blo 1538466 1538587 := bstep (se 1 (by rfl) ⟨1153940, by rfl⟩ : syracuseStep 1538587 = 2307881) B2307881
theorem B1538591 : Blo 1538466 1538591 := bstep (se 1 (by rfl) ⟨1153943, by rfl⟩ : syracuseStep 1538591 = 2307887) B2307887
theorem B2308745 : Blo 1538466 2308745 := bstep (se 2 (by rfl) ⟨865779, by rfl⟩ : syracuseStep 2308745 = 1731559) B1731559
theorem B2308919 : Blo 1538466 2308919 := bstep (se 1 (by rfl) ⟨1731689, by rfl⟩ : syracuseStep 2308919 = 3463379) B3463379
theorem B5192531 : Blo 1538466 5192531 := bstep (se 1 (by rfl) ⟨3894398, by rfl⟩ : syracuseStep 5192531 = 7788797) B7788797
theorem B6576977 : Blo 1538466 6576977 := bstep (se 2 (by rfl) ⟨2466366, by rfl⟩ : syracuseStep 6576977 = 4932733) B4932733
theorem B1538907 : Blo 1538466 1538907 := bstep (se 1 (by rfl) ⟨1154180, by rfl⟩ : syracuseStep 1538907 = 2308361) B2308361
theorem B2308955 : Blo 1538466 2308955 := bstep (se 1 (by rfl) ⟨1731716, by rfl⟩ : syracuseStep 2308955 = 3463433) B3463433
theorem B3464027 : Blo 1538466 3464027 := bstep (se 1 (by rfl) ⟨2598020, by rfl⟩ : syracuseStep 3464027 = 5196041) B5196041
theorem B63159193 : Blo 1538466 63159193 := bstep (se 2 (by rfl) ⟨23684697, by rfl⟩ : syracuseStep 63159193 = 47369395) B47369395
theorem B1538975 : Blo 1538466 1538975 := bstep (se 1 (by rfl) ⟨1154231, by rfl⟩ : syracuseStep 1538975 = 2308463) B2308463
theorem B2309099 : Blo 1538466 2309099 := bstep (se 1 (by rfl) ⟨1731824, by rfl⟩ : syracuseStep 2309099 = 3463649) B3463649
theorem B1539119 : Blo 1538466 1539119 := bstep (se 1 (by rfl) ⟨1154339, by rfl⟩ : syracuseStep 1539119 = 2308679) B2308679
theorem B1539143 : Blo 1538466 1539143 := bstep (se 1 (by rfl) ⟨1154357, by rfl⟩ : syracuseStep 1539143 = 2308715) B2308715
theorem B2309303 : Blo 1538466 2309303 := bstep (se 1 (by rfl) ⟨1731977, by rfl⟩ : syracuseStep 2309303 = 3463955) B3463955
theorem B1948855 : Blo 1538466 1948855 := bstep (se 1 (by rfl) ⟨1461641, by rfl⟩ : syracuseStep 1948855 = 2923283) B2923283
theorem B1539295 : Blo 1538466 1539295 := bstep (se 1 (by rfl) ⟨1154471, by rfl⟩ : syracuseStep 1539295 = 2308943) B2308943
theorem B5193071 : Blo 1538466 5193071 := bstep (se 1 (by rfl) ⟨3894803, by rfl⟩ : syracuseStep 5193071 = 7789607) B7789607
theorem B2309543 : Blo 1538466 2309543 := bstep (se 1 (by rfl) ⟨1732157, by rfl⟩ : syracuseStep 2309543 = 3464315) B3464315
theorem B1539559 : Blo 1538466 1539559 := bstep (se 1 (by rfl) ⟨1154669, by rfl⟩ : syracuseStep 1539559 = 2309339) B2309339
theorem B2309627 : Blo 1538466 2309627 := bstep (se 1 (by rfl) ⟨1732220, by rfl⟩ : syracuseStep 2309627 = 3464441) B3464441
theorem B3464783 : Blo 1538466 3464783 := bstep (se 1 (by rfl) ⟨2598587, by rfl⟩ : syracuseStep 3464783 = 5197175) B5197175
theorem B1539675 : Blo 1538466 1539675 := bstep (se 1 (by rfl) ⟨1154756, by rfl⟩ : syracuseStep 1539675 = 2309513) B2309513
theorem B2309723 : Blo 1538466 2309723 := bstep (se 1 (by rfl) ⟨1732292, by rfl⟩ : syracuseStep 2309723 = 3464585) B3464585
theorem B2596495 : Blo 1538466 2596495 := bstep (se 1 (by rfl) ⟨1947371, by rfl⟩ : syracuseStep 2596495 = 3894743) B3894743
theorem B2309807 : Blo 1538466 2309807 := bstep (se 1 (by rfl) ⟨1732355, by rfl⟩ : syracuseStep 2309807 = 3464711) B3464711
theorem B5193449 : Blo 1538466 5193449 := bstep (se 2 (by rfl) ⟨1947543, by rfl⟩ : syracuseStep 5193449 = 3895087) B3895087
theorem B2309927 : Blo 1538466 2309927 := bstep (se 1 (by rfl) ⟨1732445, by rfl⟩ : syracuseStep 2309927 = 3464891) B3464891
theorem B1539911 : Blo 1538466 1539911 := bstep (se 1 (by rfl) ⟨1154933, by rfl⟩ : syracuseStep 1539911 = 2309867) B2309867
theorem B243195767 : Blo 1538466 243195767 := bstep (se 1 (by rfl) ⟨182396825, by rfl⟩ : syracuseStep 243195767 = 364793651) B364793651
theorem B74883359 : Blo 1538466 74883359 := bstep (se 1 (by rfl) ⟨56162519, by rfl⟩ : syracuseStep 74883359 = 112325039) B112325039
theorem B2597177 : Blo 1538466 2597177 := bstep (se 2 (by rfl) ⟨973941, by rfl⟩ : syracuseStep 2597177 = 1947883) B1947883
theorem B6939047 : Blo 1538466 6939047 := bstep (se 1 (by rfl) ⟨5204285, by rfl⟩ : syracuseStep 6939047 = 10408571) B10408571
theorem B5702255 : Blo 1538466 5702255 := bstep (se 1 (by rfl) ⟨4276691, by rfl⟩ : syracuseStep 5702255 = 8553383) B8553383
theorem B2597663 : Blo 1538466 2597663 := bstep (se 1 (by rfl) ⟨1948247, by rfl⟩ : syracuseStep 2597663 = 3896495) B3896495
theorem B39969611 : Blo 1538466 39969611 := bstep (se 1 (by rfl) ⟨29977208, by rfl⟩ : syracuseStep 39969611 = 59954417) B59954417
theorem B19719085 : Blo 1538466 19719085 := bstep (se 3 (by rfl) ⟨3697328, by rfl⟩ : syracuseStep 19719085 = 7394657) B7394657
theorem B11691215 : Blo 1538466 11691215 := bstep (se 1 (by rfl) ⟨8768411, by rfl⟩ : syracuseStep 11691215 = 17536823) B17536823
theorem B7791875 : Blo 1538466 7791875 := bstep (se 1 (by rfl) ⟨5843906, by rfl⟩ : syracuseStep 7791875 = 11687813) B11687813
theorem B6661531 : Blo 1538466 6661531 := bstep (se 1 (by rfl) ⟨4996148, by rfl⟩ : syracuseStep 6661531 = 9992297) B9992297
theorem B5195177 : Blo 1538466 5195177 := bstep (se 2 (by rfl) ⟨1948191, by rfl⟩ : syracuseStep 5195177 = 3896383) B3896383
theorem B7792199 : Blo 1538466 7792199 := bstep (se 1 (by rfl) ⟨5844149, by rfl⟩ : syracuseStep 7792199 = 11688299) B11688299
theorem B2598473 : Blo 1538466 2598473 := bstep (se 2 (by rfl) ⟨974427, by rfl⟩ : syracuseStep 2598473 = 1948855) B1948855
theorem B12486403 : Blo 1538466 12486403 := bstep (se 1 (by rfl) ⟨9364802, by rfl⟩ : syracuseStep 12486403 = 18729605) B18729605
theorem B4384651 : Blo 1538466 4384651 := bstep (se 1 (by rfl) ⟨3288488, by rfl⟩ : syracuseStep 4384651 = 6576977) B6576977
theorem B7899419 : Blo 1538466 7899419 := bstep (se 1 (by rfl) ⟨5924564, by rfl⟩ : syracuseStep 7899419 = 11849129) B11849129
theorem B162130511 : Blo 1538466 162130511 := bstep (se 1 (by rfl) ⟨121597883, by rfl⟩ : syracuseStep 162130511 = 243195767) B243195767
theorem B29592161 : Blo 1538466 29592161 := bstep (se 2 (by rfl) ⟨11097060, by rfl⟩ : syracuseStep 29592161 = 22194121) B22194121
theorem B6572825 : Blo 1538466 6572825 := bstep (se 2 (by rfl) ⟨2464809, by rfl⟩ : syracuseStep 6572825 = 4929619) B4929619
theorem B7793495 : Blo 1538466 7793495 := bstep (se 1 (by rfl) ⟨5845121, by rfl⟩ : syracuseStep 7793495 = 11690243) B11690243
theorem B5196635 : Blo 1538466 5196635 := bstep (se 1 (by rfl) ⟨3897476, by rfl⟩ : syracuseStep 5196635 = 7794953) B7794953
theorem B89967611 : Blo 1538466 89967611 := bstep (se 1 (by rfl) ⟨67475708, by rfl⟩ : syracuseStep 89967611 = 134951417) B134951417
theorem B112381091 : Blo 1538466 112381091 := bstep (se 1 (by rfl) ⟨84285818, by rfl⟩ : syracuseStep 112381091 = 168571637) B168571637
theorem B1732063 : Blo 1538466 1732063 := bstep (se 1 (by rfl) ⟨1299047, by rfl⟩ : syracuseStep 1732063 = 2598095) B2598095
theorem B3894875 : Blo 1538466 3894875 := bstep (se 1 (by rfl) ⟨2921156, by rfl⟩ : syracuseStep 3894875 = 5842313) B5842313
theorem B4681307 : Blo 1538466 4681307 := bstep (se 1 (by rfl) ⟨3510980, by rfl⟩ : syracuseStep 4681307 = 7021961) B7021961
theorem B109579877 : Blo 1538466 109579877 := bstep (se 4 (by rfl) ⟨10273113, by rfl⟩ : syracuseStep 109579877 = 20546227) B20546227
theorem B28085933 : Blo 1538466 28085933 := bstep (se 3 (by rfl) ⟨5266112, by rfl⟩ : syracuseStep 28085933 = 10532225) B10532225
theorem B2773055 : Blo 1538466 2773055 := bstep (se 1 (by rfl) ⟨2079791, by rfl⟩ : syracuseStep 2773055 = 4159583) B4159583
theorem B4682087 : Blo 1538466 4682087 := bstep (se 1 (by rfl) ⟨3511565, by rfl⟩ : syracuseStep 4682087 = 7023131) B7023131
theorem B3461687 : Blo 1538466 3461687 := bstep (se 1 (by rfl) ⟨2596265, by rfl⟩ : syracuseStep 3461687 = 5192531) B5192531
theorem B47379167 : Blo 1538466 47379167 := bstep (se 1 (by rfl) ⟨35534375, by rfl⟩ : syracuseStep 47379167 = 71068751) B71068751
theorem B3896059 : Blo 1538466 3896059 := bstep (se 1 (by rfl) ⟨2922044, by rfl⟩ : syracuseStep 3896059 = 5844089) B5844089
theorem B3461993 : Blo 1538466 3461993 := bstep (se 2 (by rfl) ⟨1298247, by rfl⟩ : syracuseStep 3461993 = 2596495) B2596495
theorem B3462047 : Blo 1538466 3462047 := bstep (se 1 (by rfl) ⟨2596535, by rfl⟩ : syracuseStep 3462047 = 5193071) B5193071
theorem B142226441 : Blo 1538466 142226441 := bstep (se 2 (by rfl) ⟨53334915, by rfl⟩ : syracuseStep 142226441 = 106669831) B106669831
theorem B2339911 : Blo 1538466 2339911 := bstep (se 1 (by rfl) ⟨1754933, by rfl⟩ : syracuseStep 2339911 = 3509867) B3509867
theorem B1848415 : Blo 1538466 1848415 := bstep (se 1 (by rfl) ⟨1386311, by rfl⟩ : syracuseStep 1848415 = 2772623) B2772623
theorem B3462299 : Blo 1538466 3462299 := bstep (se 1 (by rfl) ⟨2596724, by rfl⟩ : syracuseStep 3462299 = 5193449) B5193449
theorem B6575489 : Blo 1538466 6575489 := bstep (se 2 (by rfl) ⟨2465808, by rfl⟩ : syracuseStep 6575489 = 4931617) B4931617
theorem B37533293 : Blo 1538466 37533293 := bstep (se 3 (by rfl) ⟨7037492, by rfl⟩ : syracuseStep 37533293 = 14074985) B14074985
theorem B2922151 : Blo 1538466 2922151 := bstep (se 1 (by rfl) ⟨2191613, by rfl⟩ : syracuseStep 2922151 = 4383227) B4383227
theorem B3462875 : Blo 1538466 3462875 := bstep (se 1 (by rfl) ⟨2597156, by rfl⟩ : syracuseStep 3462875 = 5194313) B5194313
theorem B3462983 : Blo 1538466 3462983 := bstep (se 1 (by rfl) ⟨2597237, by rfl⟩ : syracuseStep 3462983 = 5194475) B5194475
theorem B2922311 : Blo 1538466 2922311 := bstep (se 1 (by rfl) ⟨2191733, by rfl⟩ : syracuseStep 2922311 = 4383467) B4383467
theorem B3512147 : Blo 1538466 3512147 := bstep (se 1 (by rfl) ⟨2634110, by rfl⟩ : syracuseStep 3512147 = 5268221) B5268221
theorem B19986263 : Blo 1538466 19986263 := bstep (se 1 (by rfl) ⟨14989697, by rfl⟩ : syracuseStep 19986263 = 29979395) B29979395
theorem B29595851 : Blo 1538466 29595851 := bstep (se 1 (by rfl) ⟨22196888, by rfl⟩ : syracuseStep 29595851 = 44393777) B44393777
theorem B13154669 : Blo 1538466 13154669 := bstep (se 3 (by rfl) ⟨2466500, by rfl⟩ : syracuseStep 13154669 = 4933001) B4933001
theorem B22485367 : Blo 1538466 22485367 := bstep (se 1 (by rfl) ⟨16864025, by rfl⟩ : syracuseStep 22485367 = 33728051) B33728051
theorem B1538511 : Blo 1538466 1538511 := bstep (se 1 (by rfl) ⟨1153883, by rfl⟩ : syracuseStep 1538511 = 2307767) B2307767
theorem B2308559 : Blo 1538466 2308559 := bstep (se 1 (by rfl) ⟨1731419, by rfl⟩ : syracuseStep 2308559 = 3462839) B3462839
theorem B1538535 : Blo 1538466 1538535 := bstep (se 1 (by rfl) ⟨1153901, by rfl⟩ : syracuseStep 1538535 = 2307803) B2307803
theorem B84212257 : Blo 1538466 84212257 := bstep (se 2 (by rfl) ⟨31579596, by rfl⟩ : syracuseStep 84212257 = 63159193) B63159193
theorem B2308649 : Blo 1538466 2308649 := bstep (se 2 (by rfl) ⟨865743, by rfl⟩ : syracuseStep 2308649 = 1731487) B1731487
theorem B1538651 : Blo 1538466 1538651 := bstep (se 1 (by rfl) ⟨1153988, by rfl⟩ : syracuseStep 1538651 = 2307977) B2307977
theorem B1538719 : Blo 1538466 1538719 := bstep (se 1 (by rfl) ⟨1154039, by rfl⟩ : syracuseStep 1538719 = 2308079) B2308079
theorem B2308841 : Blo 1538466 2308841 := bstep (se 2 (by rfl) ⟨865815, by rfl⟩ : syracuseStep 2308841 = 1731631) B1731631
theorem B3463991 : Blo 1538466 3463991 := bstep (se 1 (by rfl) ⟨2597993, by rfl⟩ : syracuseStep 3463991 = 5195987) B5195987
theorem B13146947 : Blo 1538466 13146947 := bstep (se 1 (by rfl) ⟨9860210, by rfl⟩ : syracuseStep 13146947 = 19720421) B19720421
theorem B1538887 : Blo 1538466 1538887 := bstep (se 1 (by rfl) ⟨1154165, by rfl⟩ : syracuseStep 1538887 = 2308331) B2308331
theorem B23690063 : Blo 1538466 23690063 := bstep (se 1 (by rfl) ⟨17767547, by rfl⟩ : syracuseStep 23690063 = 35535095) B35535095
theorem B11688785 : Blo 1538466 11688785 := bstep (se 2 (by rfl) ⟨4383294, by rfl⟩ : syracuseStep 11688785 = 8766589) B8766589
theorem B1538927 : Blo 1538466 1538927 := bstep (se 1 (by rfl) ⟨1154195, by rfl⟩ : syracuseStep 1538927 = 2308391) B2308391
theorem B1538983 : Blo 1538466 1538983 := bstep (se 1 (by rfl) ⟨1154237, by rfl⟩ : syracuseStep 1538983 = 2308475) B2308475
theorem B3464171 : Blo 1538466 3464171 := bstep (se 1 (by rfl) ⟨2598128, by rfl⟩ : syracuseStep 3464171 = 5196257) B5196257
theorem B1539163 : Blo 1538466 1539163 := bstep (se 1 (by rfl) ⟨1154372, by rfl⟩ : syracuseStep 1539163 = 2308745) B2308745
theorem B2309225 : Blo 1538466 2309225 := bstep (se 2 (by rfl) ⟨865959, by rfl⟩ : syracuseStep 2309225 = 1731919) B1731919
theorem B1539279 : Blo 1538466 1539279 := bstep (se 1 (by rfl) ⟨1154459, by rfl⟩ : syracuseStep 1539279 = 2308919) B2308919
theorem B1539303 : Blo 1538466 1539303 := bstep (se 1 (by rfl) ⟨1154477, by rfl⟩ : syracuseStep 1539303 = 2308955) B2308955
theorem B2309351 : Blo 1538466 2309351 := bstep (se 1 (by rfl) ⟨1732013, by rfl⟩ : syracuseStep 2309351 = 3464027) B3464027
theorem B1539399 : Blo 1538466 1539399 := bstep (se 1 (by rfl) ⟨1154549, by rfl⟩ : syracuseStep 1539399 = 2309099) B2309099
theorem B7789931 : Blo 1538466 7789931 := bstep (se 1 (by rfl) ⟨5842448, by rfl⟩ : syracuseStep 7789931 = 11684897) B11684897
theorem B1539535 : Blo 1538466 1539535 := bstep (se 1 (by rfl) ⟨1154651, by rfl⟩ : syracuseStep 1539535 = 2309303) B2309303
theorem B13147697 : Blo 1538466 13147697 := bstep (se 2 (by rfl) ⟨4930386, by rfl⟩ : syracuseStep 13147697 = 9860773) B9860773
theorem B1539695 : Blo 1538466 1539695 := bstep (se 1 (by rfl) ⟨1154771, by rfl⟩ : syracuseStep 1539695 = 2309543) B2309543
theorem B1539751 : Blo 1538466 1539751 := bstep (se 1 (by rfl) ⟨1154813, by rfl⟩ : syracuseStep 1539751 = 2309627) B2309627
theorem B2309855 : Blo 1538466 2309855 := bstep (se 1 (by rfl) ⟨1732391, by rfl⟩ : syracuseStep 2309855 = 3464783) B3464783
theorem B1539815 : Blo 1538466 1539815 := bstep (se 1 (by rfl) ⟨1154861, by rfl⟩ : syracuseStep 1539815 = 2309723) B2309723
theorem B2309897 : Blo 1538466 2309897 := bstep (se 2 (by rfl) ⟨866211, by rfl⟩ : syracuseStep 2309897 = 1732423) B1732423
theorem B1539871 : Blo 1538466 1539871 := bstep (se 1 (by rfl) ⟨1154903, by rfl⟩ : syracuseStep 1539871 = 2309807) B2309807
theorem B1539951 : Blo 1538466 1539951 := bstep (se 1 (by rfl) ⟨1154963, by rfl⟩ : syracuseStep 1539951 = 2309927) B2309927
theorem B7790579 : Blo 1538466 7790579 := bstep (se 1 (by rfl) ⟨5842934, by rfl⟩ : syracuseStep 7790579 = 11685869) B11685869
theorem B49922239 : Blo 1538466 49922239 := bstep (se 1 (by rfl) ⟨37441679, by rfl⟩ : syracuseStep 49922239 = 74883359) B74883359
theorem B3121391 : Blo 1538466 3121391 := bstep (se 1 (by rfl) ⟨2341043, by rfl⟩ : syracuseStep 3121391 = 4682087) B4682087
theorem B3801503 : Blo 1538466 3801503 := bstep (se 1 (by rfl) ⟨2851127, by rfl⟩ : syracuseStep 3801503 = 5702255) B5702255
theorem B5194583 : Blo 1538466 5194583 := bstep (se 1 (by rfl) ⟨3895937, by rfl⟩ : syracuseStep 5194583 = 7791875) B7791875
theorem B4383659 : Blo 1538466 4383659 := bstep (se 1 (by rfl) ⟨3287744, by rfl⟩ : syracuseStep 4383659 = 6575489) B6575489
theorem B5194745 : Blo 1538466 5194745 := bstep (se 2 (by rfl) ⟨1948029, by rfl⟩ : syracuseStep 5194745 = 3896059) B3896059
theorem B5194799 : Blo 1538466 5194799 := bstep (se 1 (by rfl) ⟨3896099, by rfl⟩ : syracuseStep 5194799 = 7792199) B7792199
theorem B108087007 : Blo 1538466 108087007 := bstep (se 1 (by rfl) ⟨81065255, by rfl⟩ : syracuseStep 108087007 = 162130511) B162130511
theorem B19728107 : Blo 1538466 19728107 := bstep (se 1 (by rfl) ⟨14796080, by rfl⟩ : syracuseStep 19728107 = 29592161) B29592161
theorem B7792523 : Blo 1538466 7792523 := bstep (se 1 (by rfl) ⟨5844392, by rfl⟩ : syracuseStep 7792523 = 11688785) B11688785
theorem B5195663 : Blo 1538466 5195663 := bstep (se 1 (by rfl) ⟨3896747, by rfl⟩ : syracuseStep 5195663 = 7793495) B7793495
theorem B9365725 : Blo 1538466 9365725 := bstep (se 3 (by rfl) ⟨1756073, by rfl⟩ : syracuseStep 9365725 = 3512147) B3512147
theorem B16648537 : Blo 1538466 16648537 := bstep (se 2 (by rfl) ⟨6243201, by rfl⟩ : syracuseStep 16648537 = 12486403) B12486403
theorem B1731451 : Blo 1538466 1731451 := bstep (se 1 (by rfl) ⟨1298588, by rfl⟩ : syracuseStep 1731451 = 2597177) B2597177
theorem B1731775 : Blo 1538466 1731775 := bstep (se 1 (by rfl) ⟨1298831, by rfl⟩ : syracuseStep 1731775 = 2597663) B2597663
theorem B94817627 : Blo 1538466 94817627 := bstep (se 1 (by rfl) ⟨71113220, by rfl⟩ : syracuseStep 94817627 = 142226441) B142226441
theorem B112283009 : Blo 1538466 112283009 := bstep (se 2 (by rfl) ⟨42106128, by rfl⟩ : syracuseStep 112283009 = 84212257) B84212257
theorem B7794143 : Blo 1538466 7794143 := bstep (se 1 (by rfl) ⟨5845607, by rfl⟩ : syracuseStep 7794143 = 11691215) B11691215
theorem B1732315 : Blo 1538466 1732315 := bstep (se 1 (by rfl) ⟨1299236, by rfl⟩ : syracuseStep 1732315 = 2598473) B2598473
theorem B25022195 : Blo 1538466 25022195 := bstep (se 1 (by rfl) ⟨18766646, by rfl⟩ : syracuseStep 25022195 = 37533293) B37533293
theorem B13324175 : Blo 1538466 13324175 := bstep (se 1 (by rfl) ⟨9993131, by rfl⟩ : syracuseStep 13324175 = 19986263) B19986263
theorem B26292113 : Blo 1538466 26292113 := bstep (se 2 (by rfl) ⟨9859542, by rfl⟩ : syracuseStep 26292113 = 19719085) B19719085
theorem B19730567 : Blo 1538466 19730567 := bstep (se 1 (by rfl) ⟨14797925, by rfl⟩ : syracuseStep 19730567 = 29595851) B29595851
theorem B8769779 : Blo 1538466 8769779 := bstep (se 1 (by rfl) ⟨6577334, by rfl⟩ : syracuseStep 8769779 = 13154669) B13154669
theorem B59978407 : Blo 1538466 59978407 := bstep (se 1 (by rfl) ⟨44983805, by rfl⟩ : syracuseStep 59978407 = 89967611) B89967611
theorem B74920727 : Blo 1538466 74920727 := bstep (se 1 (by rfl) ⟨56190545, by rfl⟩ : syracuseStep 74920727 = 112381091) B112381091
theorem B3896201 : Blo 1538466 3896201 := bstep (se 2 (by rfl) ⟨1461075, by rfl⟩ : syracuseStep 3896201 = 2922151) B2922151
theorem B73053251 : Blo 1538466 73053251 := bstep (se 1 (by rfl) ⟨54789938, by rfl⟩ : syracuseStep 73053251 = 109579877) B109579877
theorem B18723955 : Blo 1538466 18723955 := bstep (se 1 (by rfl) ⟨14042966, by rfl⟩ : syracuseStep 18723955 = 28085933) B28085933
theorem B5846201 : Blo 1538466 5846201 := bstep (se 2 (by rfl) ⟨2192325, by rfl⟩ : syracuseStep 5846201 = 4384651) B4384651
theorem B7394813 : Blo 1538466 7394813 := bstep (se 3 (by rfl) ⟨1386527, by rfl⟩ : syracuseStep 7394813 = 2773055) B2773055
theorem B2307791 : Blo 1538466 2307791 := bstep (se 1 (by rfl) ⟨1730843, by rfl⟩ : syracuseStep 2307791 = 3461687) B3461687
theorem B31586111 : Blo 1538466 31586111 := bstep (se 1 (by rfl) ⟨23689583, by rfl⟩ : syracuseStep 31586111 = 47379167) B47379167
theorem B26646407 : Blo 1538466 26646407 := bstep (se 1 (by rfl) ⟨19984805, by rfl⟩ : syracuseStep 26646407 = 39969611) B39969611
theorem B2307995 : Blo 1538466 2307995 := bstep (se 1 (by rfl) ⟨1730996, by rfl⟩ : syracuseStep 2307995 = 3461993) B3461993
theorem B2308031 : Blo 1538466 2308031 := bstep (se 1 (by rfl) ⟨1731023, by rfl⟩ : syracuseStep 2308031 = 3462047) B3462047
theorem B2308199 : Blo 1538466 2308199 := bstep (se 1 (by rfl) ⟨1731149, by rfl⟩ : syracuseStep 2308199 = 3462299) B3462299
theorem B3463451 : Blo 1538466 3463451 := bstep (se 1 (by rfl) ⟨2597588, by rfl⟩ : syracuseStep 3463451 = 5195177) B5195177
theorem B18504125 : Blo 1538466 18504125 := bstep (se 3 (by rfl) ⟨3469523, by rfl⟩ : syracuseStep 18504125 = 6939047) B6939047
theorem B2308583 : Blo 1538466 2308583 := bstep (se 1 (by rfl) ⟨1731437, by rfl⟩ : syracuseStep 2308583 = 3462875) B3462875
theorem B2308655 : Blo 1538466 2308655 := bstep (se 1 (by rfl) ⟨1731491, by rfl⟩ : syracuseStep 2308655 = 3462983) B3462983
theorem B1948207 : Blo 1538466 1948207 := bstep (se 1 (by rfl) ⟨1461155, by rfl⟩ : syracuseStep 1948207 = 2922311) B2922311
theorem B3119881 : Blo 1538466 3119881 := bstep (se 2 (by rfl) ⟨1169955, by rfl⟩ : syracuseStep 3119881 = 2339911) B2339911
theorem B2464553 : Blo 1538466 2464553 := bstep (se 2 (by rfl) ⟨924207, by rfl⟩ : syracuseStep 2464553 = 1848415) B1848415
theorem B5266279 : Blo 1538466 5266279 := bstep (se 1 (by rfl) ⟨3949709, by rfl⟩ : syracuseStep 5266279 = 7899419) B7899419
theorem B1539039 : Blo 1538466 1539039 := bstep (se 1 (by rfl) ⟨1154279, by rfl⟩ : syracuseStep 1539039 = 2308559) B2308559
theorem B1539099 : Blo 1538466 1539099 := bstep (se 1 (by rfl) ⟨1154324, by rfl⟩ : syracuseStep 1539099 = 2308649) B2308649
theorem B1539227 : Blo 1538466 1539227 := bstep (se 1 (by rfl) ⟨1154420, by rfl⟩ : syracuseStep 1539227 = 2308841) B2308841
theorem B4381883 : Blo 1538466 4381883 := bstep (se 1 (by rfl) ⟨3286412, by rfl⟩ : syracuseStep 4381883 = 6572825) B6572825
theorem B2309327 : Blo 1538466 2309327 := bstep (se 1 (by rfl) ⟨1731995, by rfl⟩ : syracuseStep 2309327 = 3463991) B3463991
theorem B8764631 : Blo 1538466 8764631 := bstep (se 1 (by rfl) ⟨6573473, by rfl⟩ : syracuseStep 8764631 = 13146947) B13146947
theorem B15793375 : Blo 1538466 15793375 := bstep (se 1 (by rfl) ⟨11845031, by rfl⟩ : syracuseStep 15793375 = 23690063) B23690063
theorem B3464423 : Blo 1538466 3464423 := bstep (se 1 (by rfl) ⟨2598317, by rfl⟩ : syracuseStep 3464423 = 5196635) B5196635
theorem B119921957 : Blo 1538466 119921957 := bstep (se 4 (by rfl) ⟨11242683, by rfl⟩ : syracuseStep 119921957 = 22485367) B22485367
theorem B2309417 : Blo 1538466 2309417 := bstep (se 2 (by rfl) ⟨866031, by rfl⟩ : syracuseStep 2309417 = 1732063) B1732063
theorem B2309447 : Blo 1538466 2309447 := bstep (se 1 (by rfl) ⟨1732085, by rfl⟩ : syracuseStep 2309447 = 3464171) B3464171
theorem B1539483 : Blo 1538466 1539483 := bstep (se 1 (by rfl) ⟨1154612, by rfl⟩ : syracuseStep 1539483 = 2309225) B2309225
theorem B35528165 : Blo 1538466 35528165 := bstep (se 4 (by rfl) ⟨3330765, by rfl⟩ : syracuseStep 35528165 = 6661531) B6661531
theorem B1539567 : Blo 1538466 1539567 := bstep (se 1 (by rfl) ⟨1154675, by rfl⟩ : syracuseStep 1539567 = 2309351) B2309351
theorem B5193287 : Blo 1538466 5193287 := bstep (se 1 (by rfl) ⟨3894965, by rfl⟩ : syracuseStep 5193287 = 7789931) B7789931
theorem B8765131 : Blo 1538466 8765131 := bstep (se 1 (by rfl) ⟨6573848, by rfl⟩ : syracuseStep 8765131 = 13147697) B13147697
theorem B2596583 : Blo 1538466 2596583 := bstep (se 1 (by rfl) ⟨1947437, by rfl⟩ : syracuseStep 2596583 = 3894875) B3894875
theorem B3120871 : Blo 1538466 3120871 := bstep (se 1 (by rfl) ⟨2340653, by rfl⟩ : syracuseStep 3120871 = 4681307) B4681307
theorem B1539903 : Blo 1538466 1539903 := bstep (se 1 (by rfl) ⟨1154927, by rfl⟩ : syracuseStep 1539903 = 2309855) B2309855
theorem B1539931 : Blo 1538466 1539931 := bstep (se 1 (by rfl) ⟨1154948, by rfl⟩ : syracuseStep 1539931 = 2309897) B2309897
theorem B5193719 : Blo 1538466 5193719 := bstep (se 1 (by rfl) ⟨3895289, by rfl⟩ : syracuseStep 5193719 = 7790579) B7790579
theorem B2080927 : Blo 1538466 2080927 := bstep (se 1 (by rfl) ⟨1560695, by rfl⟩ : syracuseStep 2080927 = 3121391) B3121391
theorem B49947151 : Blo 1538466 49947151 := bstep (se 1 (by rfl) ⟨37460363, by rfl⟩ : syracuseStep 49947151 = 74920727) B74920727
theorem B2597467 : Blo 1538466 2597467 := bstep (se 1 (by rfl) ⟨1948100, by rfl⟩ : syracuseStep 2597467 = 3896201) B3896201
theorem B48702167 : Blo 1538466 48702167 := bstep (se 1 (by rfl) ⟨36526625, by rfl⟩ : syracuseStep 48702167 = 73053251) B73053251
theorem B2597609 : Blo 1538466 2597609 := bstep (se 2 (by rfl) ⟨974103, by rfl⟩ : syracuseStep 2597609 = 1948207) B1948207
theorem B79971209 : Blo 1538466 79971209 := bstep (se 2 (by rfl) ⟨29989203, by rfl⟩ : syracuseStep 79971209 = 59978407) B59978407
theorem B5195015 : Blo 1538466 5195015 := bstep (se 1 (by rfl) ⟨3896261, by rfl⟩ : syracuseStep 5195015 = 7792523) B7792523
theorem B6572141 : Blo 1538466 6572141 := bstep (se 3 (by rfl) ⟨1232276, by rfl⟩ : syracuseStep 6572141 = 2464553) B2464553
theorem B5843087 : Blo 1538466 5843087 := bstep (se 1 (by rfl) ⟨4382315, by rfl⟩ : syracuseStep 5843087 = 8764631) B8764631
theorem B79947971 : Blo 1538466 79947971 := bstep (se 1 (by rfl) ⟨59960978, by rfl⟩ : syracuseStep 79947971 = 119921957) B119921957
theorem B63211751 : Blo 1538466 63211751 := bstep (se 1 (by rfl) ⟨47408813, by rfl⟩ : syracuseStep 63211751 = 94817627) B94817627
theorem B144116009 : Blo 1538466 144116009 := bstep (se 2 (by rfl) ⟨54043503, by rfl⟩ : syracuseStep 144116009 = 108087007) B108087007
theorem B5196095 : Blo 1538466 5196095 := bstep (se 1 (by rfl) ⟨3897071, by rfl⟩ : syracuseStep 5196095 = 7794143) B7794143
theorem B23685443 : Blo 1538466 23685443 := bstep (se 1 (by rfl) ⟨17764082, by rfl⟩ : syracuseStep 23685443 = 35528165) B35528165
theorem B1731055 : Blo 1538466 1731055 := bstep (se 1 (by rfl) ⟨1298291, by rfl⟩ : syracuseStep 1731055 = 2596583) B2596583
theorem B16681463 : Blo 1538466 16681463 := bstep (se 1 (by rfl) ⟨12511097, by rfl⟩ : syracuseStep 16681463 = 25022195) B25022195
theorem B8882783 : Blo 1538466 8882783 := bstep (se 1 (by rfl) ⟨6662087, by rfl⟩ : syracuseStep 8882783 = 13324175) B13324175
theorem B66562985 : Blo 1538466 66562985 := bstep (se 2 (by rfl) ⟨24961119, by rfl⟩ : syracuseStep 66562985 = 49922239) B49922239
theorem B10137341 : Blo 1538466 10137341 := bstep (se 3 (by rfl) ⟨1900751, by rfl⟩ : syracuseStep 10137341 = 3801503) B3801503
theorem B49950533 : Blo 1538466 49950533 := bstep (se 4 (by rfl) ⟨4682862, by rfl⟩ : syracuseStep 49950533 = 9365725) B9365725
theorem B13152071 : Blo 1538466 13152071 := bstep (se 1 (by rfl) ⟨9864053, by rfl⟩ : syracuseStep 13152071 = 19728107) B19728107
theorem B21057407 : Blo 1538466 21057407 := bstep (se 1 (by rfl) ⟨15793055, by rfl⟩ : syracuseStep 21057407 = 31586111) B31586111
theorem B17764271 : Blo 1538466 17764271 := bstep (se 1 (by rfl) ⟨13323203, by rfl⟩ : syracuseStep 17764271 = 26646407) B26646407
theorem B24965273 : Blo 1538466 24965273 := bstep (se 2 (by rfl) ⟨9361977, by rfl⟩ : syracuseStep 24965273 = 18723955) B18723955
theorem B21057833 : Blo 1538466 21057833 := bstep (se 2 (by rfl) ⟨7896687, by rfl⟩ : syracuseStep 21057833 = 15793375) B15793375
theorem B28086821 : Blo 1538466 28086821 := bstep (se 4 (by rfl) ⟨2633139, by rfl⟩ : syracuseStep 28086821 = 5266279) B5266279
theorem B2921255 : Blo 1538466 2921255 := bstep (se 1 (by rfl) ⟨2190941, by rfl⟩ : syracuseStep 2921255 = 4381883) B4381883
theorem B74855339 : Blo 1538466 74855339 := bstep (se 1 (by rfl) ⟨56141504, by rfl⟩ : syracuseStep 74855339 = 112283009) B112283009
theorem B11686841 : Blo 1538466 11686841 := bstep (se 2 (by rfl) ⟨4382565, by rfl⟩ : syracuseStep 11686841 = 8765131) B8765131
theorem B3462191 : Blo 1538466 3462191 := bstep (se 1 (by rfl) ⟨2596643, by rfl⟩ : syracuseStep 3462191 = 5193287) B5193287
theorem B17528075 : Blo 1538466 17528075 := bstep (se 1 (by rfl) ⟨13146056, by rfl⟩ : syracuseStep 17528075 = 26292113) B26292113
theorem B3462479 : Blo 1538466 3462479 := bstep (se 1 (by rfl) ⟨2596859, by rfl⟩ : syracuseStep 3462479 = 5193719) B5193719
theorem B13153711 : Blo 1538466 13153711 := bstep (se 1 (by rfl) ⟨9865283, by rfl⟩ : syracuseStep 13153711 = 19730567) B19730567
theorem B5846519 : Blo 1538466 5846519 := bstep (se 1 (by rfl) ⟨4384889, by rfl⟩ : syracuseStep 5846519 = 8769779) B8769779
theorem B22198049 : Blo 1538466 22198049 := bstep (se 2 (by rfl) ⟨8324268, by rfl⟩ : syracuseStep 22198049 = 16648537) B16648537
theorem B3463055 : Blo 1538466 3463055 := bstep (se 1 (by rfl) ⟨2597291, by rfl⟩ : syracuseStep 3463055 = 5194583) B5194583
theorem B3463163 : Blo 1538466 3463163 := bstep (se 1 (by rfl) ⟨2597372, by rfl⟩ : syracuseStep 3463163 = 5194745) B5194745
theorem B3463199 : Blo 1538466 3463199 := bstep (se 1 (by rfl) ⟨2597399, by rfl⟩ : syracuseStep 3463199 = 5194799) B5194799
theorem B3897467 : Blo 1538466 3897467 := bstep (se 1 (by rfl) ⟨2923100, by rfl⟩ : syracuseStep 3897467 = 5846201) B5846201
theorem B4929875 : Blo 1538466 4929875 := bstep (se 1 (by rfl) ⟨3697406, by rfl⟩ : syracuseStep 4929875 = 7394813) B7394813
theorem B4159841 : Blo 1538466 4159841 := bstep (se 2 (by rfl) ⟨1559940, by rfl⟩ : syracuseStep 4159841 = 3119881) B3119881
theorem B1538527 : Blo 1538466 1538527 := bstep (se 1 (by rfl) ⟨1153895, by rfl⟩ : syracuseStep 1538527 = 2307791) B2307791
theorem B2308601 : Blo 1538466 2308601 := bstep (se 2 (by rfl) ⟨865725, by rfl⟩ : syracuseStep 2308601 = 1731451) B1731451
theorem B3463775 : Blo 1538466 3463775 := bstep (se 1 (by rfl) ⟨2597831, by rfl⟩ : syracuseStep 3463775 = 5195663) B5195663
theorem B1538663 : Blo 1538466 1538663 := bstep (se 1 (by rfl) ⟨1153997, by rfl⟩ : syracuseStep 1538663 = 2307995) B2307995
theorem B1538687 : Blo 1538466 1538687 := bstep (se 1 (by rfl) ⟨1154015, by rfl⟩ : syracuseStep 1538687 = 2308031) B2308031
theorem B1538799 : Blo 1538466 1538799 := bstep (se 1 (by rfl) ⟨1154099, by rfl⟩ : syracuseStep 1538799 = 2308199) B2308199
theorem B2308967 : Blo 1538466 2308967 := bstep (se 1 (by rfl) ⟨1731725, by rfl⟩ : syracuseStep 2308967 = 3463451) B3463451
theorem B2309033 : Blo 1538466 2309033 := bstep (se 2 (by rfl) ⟨865887, by rfl⟩ : syracuseStep 2309033 = 1731775) B1731775
theorem B12336083 : Blo 1538466 12336083 := bstep (se 1 (by rfl) ⟨9252062, by rfl⟩ : syracuseStep 12336083 = 18504125) B18504125
theorem B1539055 : Blo 1538466 1539055 := bstep (se 1 (by rfl) ⟨1154291, by rfl⟩ : syracuseStep 1539055 = 2308583) B2308583
theorem B1539103 : Blo 1538466 1539103 := bstep (se 1 (by rfl) ⟨1154327, by rfl⟩ : syracuseStep 1539103 = 2308655) B2308655
theorem B1539551 : Blo 1538466 1539551 := bstep (se 1 (by rfl) ⟨1154663, by rfl⟩ : syracuseStep 1539551 = 2309327) B2309327
theorem B2309615 : Blo 1538466 2309615 := bstep (se 1 (by rfl) ⟨1732211, by rfl⟩ : syracuseStep 2309615 = 3464423) B3464423
theorem B1539611 : Blo 1538466 1539611 := bstep (se 1 (by rfl) ⟨1154708, by rfl⟩ : syracuseStep 1539611 = 2309417) B2309417
theorem B1539631 : Blo 1538466 1539631 := bstep (se 1 (by rfl) ⟨1154723, by rfl⟩ : syracuseStep 1539631 = 2309447) B2309447
theorem B2309753 : Blo 1538466 2309753 := bstep (se 2 (by rfl) ⟨866157, by rfl⟩ : syracuseStep 2309753 = 1732315) B1732315
theorem B4161161 : Blo 1538466 4161161 := bstep (se 2 (by rfl) ⟨1560435, by rfl⟩ : syracuseStep 4161161 = 3120871) B3120871
theorem B11689757 : Blo 1538466 11689757 := bstep (se 3 (by rfl) ⟨2191829, by rfl⟩ : syracuseStep 11689757 = 4383659) B4383659
theorem B53314139 : Blo 1538466 53314139 := bstep (se 1 (by rfl) ⟨39985604, by rfl⟩ : syracuseStep 53314139 = 79971209) B79971209
theorem B7791227 : Blo 1538466 7791227 := bstep (se 1 (by rfl) ⟨5843420, by rfl⟩ : syracuseStep 7791227 = 11686841) B11686841
theorem B11092909 : Blo 1538466 11092909 := bstep (se 3 (by rfl) ⟨2079920, by rfl⟩ : syracuseStep 11092909 = 4159841) B4159841
theorem B2598311 : Blo 1538466 2598311 := bstep (se 1 (by rfl) ⟨1948733, by rfl⟩ : syracuseStep 2598311 = 3897467) B3897467
theorem B53298647 : Blo 1538466 53298647 := bstep (se 1 (by rfl) ⟨39973985, by rfl⟩ : syracuseStep 53298647 = 79947971) B79947971
theorem B42141167 : Blo 1538466 42141167 := bstep (se 1 (by rfl) ⟨31605875, by rfl⟩ : syracuseStep 42141167 = 63211751) B63211751
theorem B96077339 : Blo 1538466 96077339 := bstep (se 1 (by rfl) ⟨72058004, by rfl⟩ : syracuseStep 96077339 = 144116009) B144116009
theorem B3286583 : Blo 1538466 3286583 := bstep (se 1 (by rfl) ⟨2464937, by rfl⟩ : syracuseStep 3286583 = 4929875) B4929875
theorem B7793171 : Blo 1538466 7793171 := bstep (se 1 (by rfl) ⟨5844878, by rfl⟩ : syracuseStep 7793171 = 11689757) B11689757
theorem B8768047 : Blo 1538466 8768047 := bstep (se 1 (by rfl) ⟨6576035, by rfl⟩ : syracuseStep 8768047 = 13152071) B13152071
theorem B32468111 : Blo 1538466 32468111 := bstep (se 1 (by rfl) ⟨24351083, by rfl⟩ : syracuseStep 32468111 = 48702167) B48702167
theorem B1731739 : Blo 1538466 1731739 := bstep (se 1 (by rfl) ⟨1298804, by rfl⟩ : syracuseStep 1731739 = 2597609) B2597609
theorem B66596201 : Blo 1538466 66596201 := bstep (se 2 (by rfl) ⟨24973575, by rfl⟩ : syracuseStep 66596201 = 49947151) B49947151
theorem B11685383 : Blo 1538466 11685383 := bstep (se 1 (by rfl) ⟨8764037, by rfl⟩ : syracuseStep 11685383 = 17528075) B17528075
theorem B14798699 : Blo 1538466 14798699 := bstep (se 1 (by rfl) ⟨11099024, by rfl⟩ : syracuseStep 14798699 = 22198049) B22198049
theorem B3895391 : Blo 1538466 3895391 := bstep (se 1 (by rfl) ⟨2921543, by rfl⟩ : syracuseStep 3895391 = 5843087) B5843087
theorem B15790295 : Blo 1538466 15790295 := bstep (se 1 (by rfl) ⟨11842721, by rfl⟩ : syracuseStep 15790295 = 23685443) B23685443
theorem B11120975 : Blo 1538466 11120975 := bstep (se 1 (by rfl) ⟨8340731, by rfl⟩ : syracuseStep 11120975 = 16681463) B16681463
theorem B2774107 : Blo 1538466 2774107 := bstep (se 1 (by rfl) ⟨2080580, by rfl⟩ : syracuseStep 2774107 = 4161161) B4161161
theorem B14038271 : Blo 1538466 14038271 := bstep (se 1 (by rfl) ⟨10528703, by rfl⟩ : syracuseStep 14038271 = 21057407) B21057407
theorem B11842847 : Blo 1538466 11842847 := bstep (se 1 (by rfl) ⟨8882135, by rfl⟩ : syracuseStep 11842847 = 17764271) B17764271
theorem B16643515 : Blo 1538466 16643515 := bstep (se 1 (by rfl) ⟨12482636, by rfl⟩ : syracuseStep 16643515 = 24965273) B24965273
theorem B14038555 : Blo 1538466 14038555 := bstep (se 1 (by rfl) ⟨10528916, by rfl⟩ : syracuseStep 14038555 = 21057833) B21057833
theorem B2774569 : Blo 1538466 2774569 := bstep (se 2 (by rfl) ⟨1040463, by rfl⟩ : syracuseStep 2774569 = 2080927) B2080927
theorem B18724547 : Blo 1538466 18724547 := bstep (se 1 (by rfl) ⟨14043410, by rfl⟩ : syracuseStep 18724547 = 28086821) B28086821
theorem B1947503 : Blo 1538466 1947503 := bstep (se 1 (by rfl) ⟨1460627, by rfl⟩ : syracuseStep 1947503 = 2921255) B2921255
theorem B49903559 : Blo 1538466 49903559 := bstep (se 1 (by rfl) ⟨37427669, by rfl⟩ : syracuseStep 49903559 = 74855339) B74855339
theorem B2308073 : Blo 1538466 2308073 := bstep (se 2 (by rfl) ⟨865527, by rfl⟩ : syracuseStep 2308073 = 1731055) B1731055
theorem B2308127 : Blo 1538466 2308127 := bstep (se 1 (by rfl) ⟨1731095, by rfl⟩ : syracuseStep 2308127 = 3462191) B3462191
theorem B3463289 : Blo 1538466 3463289 := bstep (se 2 (by rfl) ⟨1298733, by rfl⟩ : syracuseStep 3463289 = 2597467) B2597467
theorem B3463343 : Blo 1538466 3463343 := bstep (se 1 (by rfl) ⟨2597507, by rfl⟩ : syracuseStep 3463343 = 5195015) B5195015
theorem B2308319 : Blo 1538466 2308319 := bstep (se 1 (by rfl) ⟨1731239, by rfl⟩ : syracuseStep 2308319 = 3462479) B3462479
theorem B3897679 : Blo 1538466 3897679 := bstep (se 1 (by rfl) ⟨2923259, by rfl⟩ : syracuseStep 3897679 = 5846519) B5846519
theorem B2308703 : Blo 1538466 2308703 := bstep (se 1 (by rfl) ⟨1731527, by rfl⟩ : syracuseStep 2308703 = 3463055) B3463055
theorem B2308775 : Blo 1538466 2308775 := bstep (se 1 (by rfl) ⟨1731581, by rfl⟩ : syracuseStep 2308775 = 3463163) B3463163
theorem B2308799 : Blo 1538466 2308799 := bstep (se 1 (by rfl) ⟨1731599, by rfl⟩ : syracuseStep 2308799 = 3463199) B3463199
theorem B4381427 : Blo 1538466 4381427 := bstep (se 1 (by rfl) ⟨3286070, by rfl⟩ : syracuseStep 4381427 = 6572141) B6572141
theorem B3464063 : Blo 1538466 3464063 := bstep (se 1 (by rfl) ⟨2598047, by rfl⟩ : syracuseStep 3464063 = 5196095) B5196095
theorem B1539067 : Blo 1538466 1539067 := bstep (se 1 (by rfl) ⟨1154300, by rfl⟩ : syracuseStep 1539067 = 2308601) B2308601
theorem B5921855 : Blo 1538466 5921855 := bstep (se 1 (by rfl) ⟨4441391, by rfl⟩ : syracuseStep 5921855 = 8882783) B8882783
theorem B2309183 : Blo 1538466 2309183 := bstep (se 1 (by rfl) ⟨1731887, by rfl⟩ : syracuseStep 2309183 = 3463775) B3463775
theorem B17538281 : Blo 1538466 17538281 := bstep (se 2 (by rfl) ⟨6576855, by rfl⟩ : syracuseStep 17538281 = 13153711) B13153711
theorem B1539311 : Blo 1538466 1539311 := bstep (se 1 (by rfl) ⟨1154483, by rfl⟩ : syracuseStep 1539311 = 2308967) B2308967
theorem B44375323 : Blo 1538466 44375323 := bstep (se 1 (by rfl) ⟨33281492, by rfl⟩ : syracuseStep 44375323 = 66562985) B66562985
theorem B1539355 : Blo 1538466 1539355 := bstep (se 1 (by rfl) ⟨1154516, by rfl⟩ : syracuseStep 1539355 = 2309033) B2309033
theorem B8224055 : Blo 1538466 8224055 := bstep (se 1 (by rfl) ⟨6168041, by rfl⟩ : syracuseStep 8224055 = 12336083) B12336083
theorem B1539743 : Blo 1538466 1539743 := bstep (se 1 (by rfl) ⟨1154807, by rfl⟩ : syracuseStep 1539743 = 2309615) B2309615
theorem B1539835 : Blo 1538466 1539835 := bstep (se 1 (by rfl) ⟨1154876, by rfl⟩ : syracuseStep 1539835 = 2309753) B2309753
theorem B6758227 : Blo 1538466 6758227 := bstep (se 1 (by rfl) ⟨5068670, by rfl⟩ : syracuseStep 6758227 = 10137341) B10137341
theorem B33300355 : Blo 1538466 33300355 := bstep (se 1 (by rfl) ⟨24975266, by rfl⟩ : syracuseStep 33300355 = 49950533) B49950533
theorem B2596927 : Blo 1538466 2596927 := bstep (se 1 (by rfl) ⟨1947695, by rfl⟩ : syracuseStep 2596927 = 3895391) B3895391
theorem B10526863 : Blo 1538466 10526863 := bstep (se 1 (by rfl) ⟨7895147, by rfl⟩ : syracuseStep 10526863 = 15790295) B15790295
theorem B7413983 : Blo 1538466 7413983 := bstep (se 1 (by rfl) ⟨5560487, by rfl⟩ : syracuseStep 7413983 = 11120975) B11120975
theorem B5194151 : Blo 1538466 5194151 := bstep (se 1 (by rfl) ⟨3895613, by rfl⟩ : syracuseStep 5194151 = 7791227) B7791227
theorem B14795237 : Blo 1538466 14795237 := bstep (se 4 (by rfl) ⟨1387053, by rfl⟩ : syracuseStep 14795237 = 2774107) B2774107
theorem B11690729 : Blo 1538466 11690729 := bstep (se 2 (by rfl) ⟨4384023, by rfl⟩ : syracuseStep 11690729 = 8768047) B8768047
theorem B33269039 : Blo 1538466 33269039 := bstep (se 1 (by rfl) ⟨24951779, by rfl⟩ : syracuseStep 33269039 = 49903559) B49903559
theorem B5195447 : Blo 1538466 5195447 := bstep (se 1 (by rfl) ⟨3896585, by rfl⟩ : syracuseStep 5195447 = 7793171) B7793171
theorem B21645407 : Blo 1538466 21645407 := bstep (se 1 (by rfl) ⟨16234055, by rfl⟩ : syracuseStep 21645407 = 32468111) B32468111
theorem B11692187 : Blo 1538466 11692187 := bstep (se 1 (by rfl) ⟨8769140, by rfl⟩ : syracuseStep 11692187 = 17538281) B17538281
theorem B5482703 : Blo 1538466 5482703 := bstep (se 1 (by rfl) ⟨4112027, by rfl⟩ : syracuseStep 5482703 = 8224055) B8224055
theorem B9865799 : Blo 1538466 9865799 := bstep (se 1 (by rfl) ⟨7399349, by rfl⟩ : syracuseStep 9865799 = 14798699) B14798699
theorem B5196905 : Blo 1538466 5196905 := bstep (se 2 (by rfl) ⟨1948839, by rfl⟩ : syracuseStep 5196905 = 3897679) B3897679
theorem B9358847 : Blo 1538466 9358847 := bstep (se 1 (by rfl) ⟨7019135, by rfl⟩ : syracuseStep 9358847 = 14038271) B14038271
theorem B1732207 : Blo 1538466 1732207 := bstep (se 1 (by rfl) ⟨1299155, by rfl⟩ : syracuseStep 1732207 = 2598311) B2598311
theorem B35532431 : Blo 1538466 35532431 := bstep (se 1 (by rfl) ⟨26649323, by rfl⟩ : syracuseStep 35532431 = 53298647) B53298647
theorem B28094111 : Blo 1538466 28094111 := bstep (se 1 (by rfl) ⟨21070583, by rfl⟩ : syracuseStep 28094111 = 42141167) B42141167
theorem B2191055 : Blo 1538466 2191055 := bstep (se 1 (by rfl) ⟨1643291, by rfl⟩ : syracuseStep 2191055 = 3286583) B3286583
theorem B14790545 : Blo 1538466 14790545 := bstep (se 2 (by rfl) ⟨5546454, by rfl⟩ : syracuseStep 14790545 = 11092909) B11092909
theorem B59167097 : Blo 1538466 59167097 := bstep (se 2 (by rfl) ⟨22187661, by rfl⟩ : syracuseStep 59167097 = 44375323) B44375323
theorem B2920951 : Blo 1538466 2920951 := bstep (se 1 (by rfl) ⟨2190713, by rfl⟩ : syracuseStep 2920951 = 4381427) B4381427
theorem B3699425 : Blo 1538466 3699425 := bstep (se 2 (by rfl) ⟨1387284, by rfl⟩ : syracuseStep 3699425 = 2774569) B2774569
theorem B44397467 : Blo 1538466 44397467 := bstep (se 1 (by rfl) ⟨33298100, by rfl⟩ : syracuseStep 44397467 = 66596201) B66596201
theorem B35542759 : Blo 1538466 35542759 := bstep (se 1 (by rfl) ⟨26657069, by rfl⟩ : syracuseStep 35542759 = 53314139) B53314139
theorem B7895231 : Blo 1538466 7895231 := bstep (se 1 (by rfl) ⟨5921423, by rfl⟩ : syracuseStep 7895231 = 11842847) B11842847
theorem B64051559 : Blo 1538466 64051559 := bstep (se 1 (by rfl) ⟨48038669, by rfl⟩ : syracuseStep 64051559 = 96077339) B96077339
theorem B12483031 : Blo 1538466 12483031 := bstep (se 1 (by rfl) ⟨9362273, by rfl⟩ : syracuseStep 12483031 = 18724547) B18724547
theorem B1538715 : Blo 1538466 1538715 := bstep (se 1 (by rfl) ⟨1154036, by rfl⟩ : syracuseStep 1538715 = 2308073) B2308073
theorem B1538751 : Blo 1538466 1538751 := bstep (se 1 (by rfl) ⟨1154063, by rfl⟩ : syracuseStep 1538751 = 2308127) B2308127
theorem B2308859 : Blo 1538466 2308859 := bstep (se 1 (by rfl) ⟨1731644, by rfl⟩ : syracuseStep 2308859 = 3463289) B3463289
theorem B2308895 : Blo 1538466 2308895 := bstep (se 1 (by rfl) ⟨1731671, by rfl⟩ : syracuseStep 2308895 = 3463343) B3463343
theorem B1538879 : Blo 1538466 1538879 := bstep (se 1 (by rfl) ⟨1154159, by rfl⟩ : syracuseStep 1538879 = 2308319) B2308319
theorem B2308985 : Blo 1538466 2308985 := bstep (se 2 (by rfl) ⟨865869, by rfl⟩ : syracuseStep 2308985 = 1731739) B1731739
theorem B1539135 : Blo 1538466 1539135 := bstep (se 1 (by rfl) ⟨1154351, by rfl⟩ : syracuseStep 1539135 = 2308703) B2308703
theorem B1539183 : Blo 1538466 1539183 := bstep (se 1 (by rfl) ⟨1154387, by rfl⟩ : syracuseStep 1539183 = 2308775) B2308775
theorem B1539199 : Blo 1538466 1539199 := bstep (se 1 (by rfl) ⟨1154399, by rfl⟩ : syracuseStep 1539199 = 2308799) B2308799
theorem B22191353 : Blo 1538466 22191353 := bstep (se 2 (by rfl) ⟨8321757, by rfl⟩ : syracuseStep 22191353 = 16643515) B16643515
theorem B2309375 : Blo 1538466 2309375 := bstep (se 1 (by rfl) ⟨1732031, by rfl⟩ : syracuseStep 2309375 = 3464063) B3464063
theorem B18718073 : Blo 1538466 18718073 := bstep (se 2 (by rfl) ⟨7019277, by rfl⟩ : syracuseStep 18718073 = 14038555) B14038555
theorem B3947903 : Blo 1538466 3947903 := bstep (se 1 (by rfl) ⟨2960927, by rfl⟩ : syracuseStep 3947903 = 5921855) B5921855
theorem B1539455 : Blo 1538466 1539455 := bstep (se 1 (by rfl) ⟨1154591, by rfl⟩ : syracuseStep 1539455 = 2309183) B2309183
theorem B5193341 : Blo 1538466 5193341 := bstep (se 3 (by rfl) ⟨973751, by rfl⟩ : syracuseStep 5193341 = 1947503) B1947503
theorem B7790255 : Blo 1538466 7790255 := bstep (se 1 (by rfl) ⟨5842691, by rfl⟩ : syracuseStep 7790255 = 11685383) B11685383
theorem B9010969 : Blo 1538466 9010969 := bstep (se 2 (by rfl) ⟨3379113, by rfl⟩ : syracuseStep 9010969 = 6758227) B6758227
theorem B44400473 : Blo 1538466 44400473 := bstep (se 2 (by rfl) ⟨16650177, by rfl⟩ : syracuseStep 44400473 = 33300355) B33300355
theorem B39444731 : Blo 1538466 39444731 := bstep (se 1 (by rfl) ⟨29583548, by rfl⟩ : syracuseStep 39444731 = 59167097) B59167097
theorem B9863491 : Blo 1538466 9863491 := bstep (se 1 (by rfl) ⟨7397618, by rfl⟩ : syracuseStep 9863491 = 14795237) B14795237
theorem B2466283 : Blo 1538466 2466283 := bstep (se 1 (by rfl) ⟨1849712, by rfl⟩ : syracuseStep 2466283 = 3699425) B3699425
theorem B192234005 : Blo 1538466 192234005 := bstep (se 6 (by rfl) ⟨4505484, by rfl⟩ : syracuseStep 192234005 = 9010969) B9010969
theorem B29598311 : Blo 1538466 29598311 := bstep (se 1 (by rfl) ⟨22198733, by rfl⟩ : syracuseStep 29598311 = 44397467) B44397467
theorem B3655135 : Blo 1538466 3655135 := bstep (se 1 (by rfl) ⟨2741351, by rfl⟩ : syracuseStep 3655135 = 5482703) B5482703
theorem B5842813 : Blo 1538466 5842813 := bstep (se 3 (by rfl) ⟨1095527, by rfl⟩ : syracuseStep 5842813 = 2191055) B2191055
theorem B12478715 : Blo 1538466 12478715 := bstep (se 1 (by rfl) ⟨9359036, by rfl⟩ : syracuseStep 12478715 = 18718073) B18718073
theorem B2631935 : Blo 1538466 2631935 := bstep (se 1 (by rfl) ⟨1973951, by rfl⟩ : syracuseStep 2631935 = 3947903) B3947903
theorem B18729407 : Blo 1538466 18729407 := bstep (se 1 (by rfl) ⟨14047055, by rfl⟩ : syracuseStep 18729407 = 28094111) B28094111
theorem B29600315 : Blo 1538466 29600315 := bstep (se 1 (by rfl) ⟨22200236, by rfl⟩ : syracuseStep 29600315 = 44400473) B44400473
theorem B4942655 : Blo 1538466 4942655 := bstep (se 1 (by rfl) ⟨3706991, by rfl⟩ : syracuseStep 4942655 = 7413983) B7413983
theorem B14035817 : Blo 1538466 14035817 := bstep (se 2 (by rfl) ⟨5263431, by rfl⟩ : syracuseStep 14035817 = 10526863) B10526863
theorem B7793819 : Blo 1538466 7793819 := bstep (se 1 (by rfl) ⟨5845364, by rfl⟩ : syracuseStep 7793819 = 11690729) B11690729
theorem B3894601 : Blo 1538466 3894601 := bstep (se 2 (by rfl) ⟨1460475, by rfl⟩ : syracuseStep 3894601 = 2920951) B2920951
theorem B22179359 : Blo 1538466 22179359 := bstep (se 1 (by rfl) ⟨16634519, by rfl⟩ : syracuseStep 22179359 = 33269039) B33269039
theorem B14430271 : Blo 1538466 14430271 := bstep (se 1 (by rfl) ⟨10822703, by rfl⟩ : syracuseStep 14430271 = 21645407) B21645407
theorem B7794791 : Blo 1538466 7794791 := bstep (se 1 (by rfl) ⟨5846093, by rfl⟩ : syracuseStep 7794791 = 11692187) B11692187
theorem B5263487 : Blo 1538466 5263487 := bstep (se 1 (by rfl) ⟨3947615, by rfl⟩ : syracuseStep 5263487 = 7895231) B7895231
theorem B42701039 : Blo 1538466 42701039 := bstep (se 1 (by rfl) ⟨32025779, by rfl⟩ : syracuseStep 42701039 = 64051559) B64051559
theorem B6239231 : Blo 1538466 6239231 := bstep (se 1 (by rfl) ⟨4679423, by rfl⟩ : syracuseStep 6239231 = 9358847) B9358847
theorem B3462227 : Blo 1538466 3462227 := bstep (se 1 (by rfl) ⟨2596670, by rfl⟩ : syracuseStep 3462227 = 5193341) B5193341
theorem B23688287 : Blo 1538466 23688287 := bstep (se 1 (by rfl) ⟨17766215, by rfl⟩ : syracuseStep 23688287 = 35532431) B35532431
theorem B9860363 : Blo 1538466 9860363 := bstep (se 1 (by rfl) ⟨7395272, by rfl⟩ : syracuseStep 9860363 = 14790545) B14790545
theorem B3462569 : Blo 1538466 3462569 := bstep (se 2 (by rfl) ⟨1298463, by rfl⟩ : syracuseStep 3462569 = 2596927) B2596927
theorem B3462767 : Blo 1538466 3462767 := bstep (se 1 (by rfl) ⟨2597075, by rfl⟩ : syracuseStep 3462767 = 5194151) B5194151
theorem B16644041 : Blo 1538466 16644041 := bstep (se 2 (by rfl) ⟨6241515, by rfl⟩ : syracuseStep 16644041 = 12483031) B12483031
theorem B3463631 : Blo 1538466 3463631 := bstep (se 1 (by rfl) ⟨2597723, by rfl⟩ : syracuseStep 3463631 = 5195447) B5195447
theorem B6577199 : Blo 1538466 6577199 := bstep (se 1 (by rfl) ⟨4932899, by rfl⟩ : syracuseStep 6577199 = 9865799) B9865799
theorem B1539239 : Blo 1538466 1539239 := bstep (se 1 (by rfl) ⟨1154429, by rfl⟩ : syracuseStep 1539239 = 2308859) B2308859
theorem B1539263 : Blo 1538466 1539263 := bstep (se 1 (by rfl) ⟨1154447, by rfl⟩ : syracuseStep 1539263 = 2308895) B2308895
theorem B1539323 : Blo 1538466 1539323 := bstep (se 1 (by rfl) ⟨1154492, by rfl⟩ : syracuseStep 1539323 = 2308985) B2308985
theorem B3464603 : Blo 1538466 3464603 := bstep (se 1 (by rfl) ⟨2598452, by rfl⟩ : syracuseStep 3464603 = 5196905) B5196905
theorem B2309609 : Blo 1538466 2309609 := bstep (se 2 (by rfl) ⟨866103, by rfl⟩ : syracuseStep 2309609 = 1732207) B1732207
theorem B14794235 : Blo 1538466 14794235 := bstep (se 1 (by rfl) ⟨11095676, by rfl⟩ : syracuseStep 14794235 = 22191353) B22191353
theorem B1539583 : Blo 1538466 1539583 := bstep (se 1 (by rfl) ⟨1154687, by rfl⟩ : syracuseStep 1539583 = 2309375) B2309375
theorem B47390345 : Blo 1538466 47390345 := bstep (se 2 (by rfl) ⟨17771379, by rfl⟩ : syracuseStep 47390345 = 35542759) B35542759
theorem B5193503 : Blo 1538466 5193503 := bstep (se 1 (by rfl) ⟨3895127, by rfl⟩ : syracuseStep 5193503 = 7790255) B7790255
theorem B28467359 : Blo 1538466 28467359 := bstep (se 1 (by rfl) ⟨21350519, by rfl⟩ : syracuseStep 28467359 = 42701039) B42701039
theorem B26296487 : Blo 1538466 26296487 := bstep (se 1 (by rfl) ⟨19722365, by rfl⟩ : syracuseStep 26296487 = 39444731) B39444731
theorem B128156003 : Blo 1538466 128156003 := bstep (se 1 (by rfl) ⟨96117002, by rfl⟩ : syracuseStep 128156003 = 192234005) B192234005
theorem B12486271 : Blo 1538466 12486271 := bstep (se 1 (by rfl) ⟨9364703, by rfl⟩ : syracuseStep 12486271 = 18729407) B18729407
theorem B3295103 : Blo 1538466 3295103 := bstep (se 1 (by rfl) ⟨2471327, by rfl⟩ : syracuseStep 3295103 = 4942655) B4942655
theorem B9357211 : Blo 1538466 9357211 := bstep (se 1 (by rfl) ⟨7017908, by rfl⟩ : syracuseStep 9357211 = 14035817) B14035817
theorem B4384799 : Blo 1538466 4384799 := bstep (se 1 (by rfl) ⟨3288599, by rfl⟩ : syracuseStep 4384799 = 6577199) B6577199
theorem B5195879 : Blo 1538466 5195879 := bstep (se 1 (by rfl) ⟨3896909, by rfl⟩ : syracuseStep 5195879 = 7793819) B7793819
theorem B5196527 : Blo 1538466 5196527 := bstep (se 1 (by rfl) ⟨3897395, by rfl⟩ : syracuseStep 5196527 = 7794791) B7794791
theorem B3508991 : Blo 1538466 3508991 := bstep (se 1 (by rfl) ⟨2631743, by rfl⟩ : syracuseStep 3508991 = 5263487) B5263487
theorem B13151321 : Blo 1538466 13151321 := bstep (se 2 (by rfl) ⟨4931745, by rfl⟩ : syracuseStep 13151321 = 9863491) B9863491
theorem B3288377 : Blo 1538466 3288377 := bstep (se 2 (by rfl) ⟨1233141, by rfl⟩ : syracuseStep 3288377 = 2466283) B2466283
theorem B6573575 : Blo 1538466 6573575 := bstep (se 1 (by rfl) ⟨4930181, by rfl⟩ : syracuseStep 6573575 = 9860363) B9860363
theorem B11096027 : Blo 1538466 11096027 := bstep (se 1 (by rfl) ⟨8322020, by rfl⟩ : syracuseStep 11096027 = 16644041) B16644041
theorem B8319143 : Blo 1538466 8319143 := bstep (se 1 (by rfl) ⟨6239357, by rfl⟩ : syracuseStep 8319143 = 12478715) B12478715
theorem B31593563 : Blo 1538466 31593563 := bstep (se 1 (by rfl) ⟨23695172, by rfl⟩ : syracuseStep 31593563 = 47390345) B47390345
theorem B19494053 : Blo 1538466 19494053 := bstep (se 4 (by rfl) ⟨1827567, by rfl⟩ : syracuseStep 19494053 = 3655135) B3655135
theorem B3462335 : Blo 1538466 3462335 := bstep (se 1 (by rfl) ⟨2596751, by rfl⟩ : syracuseStep 3462335 = 5193503) B5193503
theorem B19733543 : Blo 1538466 19733543 := bstep (se 1 (by rfl) ⟨14800157, by rfl⟩ : syracuseStep 19733543 = 29600315) B29600315
theorem B19240361 : Blo 1538466 19240361 := bstep (se 2 (by rfl) ⟨7215135, by rfl⟩ : syracuseStep 19240361 = 14430271) B14430271
theorem B19732207 : Blo 1538466 19732207 := bstep (se 1 (by rfl) ⟨14799155, by rfl⟩ : syracuseStep 19732207 = 29598311) B29598311
theorem B7018493 : Blo 1538466 7018493 := bstep (se 3 (by rfl) ⟨1315967, by rfl⟩ : syracuseStep 7018493 = 2631935) B2631935
theorem B4159487 : Blo 1538466 4159487 := bstep (se 1 (by rfl) ⟨3119615, by rfl⟩ : syracuseStep 4159487 = 6239231) B6239231
theorem B2308151 : Blo 1538466 2308151 := bstep (se 1 (by rfl) ⟨1731113, by rfl⟩ : syracuseStep 2308151 = 3462227) B3462227
theorem B15792191 : Blo 1538466 15792191 := bstep (se 1 (by rfl) ⟨11844143, by rfl⟩ : syracuseStep 15792191 = 23688287) B23688287
theorem B2308379 : Blo 1538466 2308379 := bstep (se 1 (by rfl) ⟨1731284, by rfl⟩ : syracuseStep 2308379 = 3462569) B3462569
theorem B2308511 : Blo 1538466 2308511 := bstep (se 1 (by rfl) ⟨1731383, by rfl⟩ : syracuseStep 2308511 = 3462767) B3462767
theorem B2309087 : Blo 1538466 2309087 := bstep (se 1 (by rfl) ⟨1731815, by rfl⟩ : syracuseStep 2309087 = 3463631) B3463631
theorem B5192801 : Blo 1538466 5192801 := bstep (se 2 (by rfl) ⟨1947300, by rfl⟩ : syracuseStep 5192801 = 3894601) B3894601
theorem B2309735 : Blo 1538466 2309735 := bstep (se 1 (by rfl) ⟨1732301, by rfl⟩ : syracuseStep 2309735 = 3464603) B3464603
theorem B1539739 : Blo 1538466 1539739 := bstep (se 1 (by rfl) ⟨1154804, by rfl⟩ : syracuseStep 1539739 = 2309609) B2309609
theorem B9862823 : Blo 1538466 9862823 := bstep (se 1 (by rfl) ⟨7397117, by rfl⟩ : syracuseStep 9862823 = 14794235) B14794235
theorem B14786239 : Blo 1538466 14786239 := bstep (se 1 (by rfl) ⟨11089679, by rfl⟩ : syracuseStep 14786239 = 22179359) B22179359
theorem B7790417 : Blo 1538466 7790417 := bstep (se 2 (by rfl) ⟨2921406, by rfl⟩ : syracuseStep 7790417 = 5842813) B5842813
theorem B17530991 : Blo 1538466 17530991 := bstep (se 1 (by rfl) ⟨13148243, by rfl⟩ : syracuseStep 17530991 = 26296487) B26296487
theorem B22184381 : Blo 1538466 22184381 := bstep (se 3 (by rfl) ⟨4159571, by rfl⟩ : syracuseStep 22184381 = 8319143) B8319143
theorem B21062375 : Blo 1538466 21062375 := bstep (se 1 (by rfl) ⟨15796781, by rfl⟩ : syracuseStep 21062375 = 31593563) B31593563
theorem B10528127 : Blo 1538466 10528127 := bstep (se 1 (by rfl) ⟨7896095, by rfl⟩ : syracuseStep 10528127 = 15792191) B15792191
theorem B8767547 : Blo 1538466 8767547 := bstep (se 1 (by rfl) ⟨6575660, by rfl⟩ : syracuseStep 8767547 = 13151321) B13151321
theorem B16648361 : Blo 1538466 16648361 := bstep (se 2 (by rfl) ⟨6243135, by rfl⟩ : syracuseStep 16648361 = 12486271) B12486271
theorem B85437335 : Blo 1538466 85437335 := bstep (se 1 (by rfl) ⟨64078001, by rfl⟩ : syracuseStep 85437335 = 128156003) B128156003
theorem B12996035 : Blo 1538466 12996035 := bstep (se 1 (by rfl) ⟨9747026, by rfl⟩ : syracuseStep 12996035 = 19494053) B19494053
theorem B8769005 : Blo 1538466 8769005 := bstep (se 3 (by rfl) ⟨1644188, by rfl⟩ : syracuseStep 8769005 = 3288377) B3288377
theorem B35147765 : Blo 1538466 35147765 := bstep (se 5 (by rfl) ⟨1647551, by rfl⟩ : syracuseStep 35147765 = 3295103) B3295103
theorem B2772991 : Blo 1538466 2772991 := bstep (se 1 (by rfl) ⟨2079743, by rfl⟩ : syracuseStep 2772991 = 4159487) B4159487
theorem B26300861 : Blo 1538466 26300861 := bstep (se 3 (by rfl) ⟨4931411, by rfl⟩ : syracuseStep 26300861 = 9862823) B9862823
theorem B2339327 : Blo 1538466 2339327 := bstep (se 1 (by rfl) ⟨1754495, by rfl⟩ : syracuseStep 2339327 = 3508991) B3508991
theorem B3461867 : Blo 1538466 3461867 := bstep (se 1 (by rfl) ⟨2596400, by rfl⟩ : syracuseStep 3461867 = 5192801) B5192801
theorem B19714985 : Blo 1538466 19714985 := bstep (se 2 (by rfl) ⟨7393119, by rfl⟩ : syracuseStep 19714985 = 14786239) B14786239
theorem B26309609 : Blo 1538466 26309609 := bstep (se 2 (by rfl) ⟨9866103, by rfl⟩ : syracuseStep 26309609 = 19732207) B19732207
theorem B18715981 : Blo 1538466 18715981 := bstep (se 3 (by rfl) ⟨3509246, by rfl⟩ : syracuseStep 18715981 = 7018493) B7018493
theorem B18978239 : Blo 1538466 18978239 := bstep (se 1 (by rfl) ⟨14233679, by rfl⟩ : syracuseStep 18978239 = 28467359) B28467359
theorem B2308223 : Blo 1538466 2308223 := bstep (se 1 (by rfl) ⟨1731167, by rfl⟩ : syracuseStep 2308223 = 3462335) B3462335
theorem B12826907 : Blo 1538466 12826907 := bstep (se 1 (by rfl) ⟨9620180, by rfl⟩ : syracuseStep 12826907 = 19240361) B19240361
theorem B17529533 : Blo 1538466 17529533 := bstep (se 3 (by rfl) ⟨3286787, by rfl⟩ : syracuseStep 17529533 = 6573575) B6573575
theorem B2923199 : Blo 1538466 2923199 := bstep (se 1 (by rfl) ⟨2192399, by rfl⟩ : syracuseStep 2923199 = 4384799) B4384799
theorem B1538767 : Blo 1538466 1538767 := bstep (se 1 (by rfl) ⟨1154075, by rfl⟩ : syracuseStep 1538767 = 2308151) B2308151
theorem B3463919 : Blo 1538466 3463919 := bstep (se 1 (by rfl) ⟨2597939, by rfl⟩ : syracuseStep 3463919 = 5195879) B5195879
theorem B1538919 : Blo 1538466 1538919 := bstep (se 1 (by rfl) ⟨1154189, by rfl⟩ : syracuseStep 1538919 = 2308379) B2308379
theorem B1539007 : Blo 1538466 1539007 := bstep (se 1 (by rfl) ⟨1154255, by rfl⟩ : syracuseStep 1539007 = 2308511) B2308511
theorem B3464351 : Blo 1538466 3464351 := bstep (se 1 (by rfl) ⟨2598263, by rfl⟩ : syracuseStep 3464351 = 5196527) B5196527
theorem B1539391 : Blo 1538466 1539391 := bstep (se 1 (by rfl) ⟨1154543, by rfl⟩ : syracuseStep 1539391 = 2309087) B2309087
theorem B13155695 : Blo 1538466 13155695 := bstep (se 1 (by rfl) ⟨9866771, by rfl⟩ : syracuseStep 13155695 = 19733543) B19733543
theorem B1539823 : Blo 1538466 1539823 := bstep (se 1 (by rfl) ⟨1154867, by rfl⟩ : syracuseStep 1539823 = 2309735) B2309735
theorem B12476281 : Blo 1538466 12476281 := bstep (se 2 (by rfl) ⟨4678605, by rfl⟩ : syracuseStep 12476281 = 9357211) B9357211
theorem B5193611 : Blo 1538466 5193611 := bstep (se 1 (by rfl) ⟨3895208, by rfl⟩ : syracuseStep 5193611 = 7790417) B7790417
theorem B7397351 : Blo 1538466 7397351 := bstep (se 1 (by rfl) ⟨5548013, by rfl⟩ : syracuseStep 7397351 = 11096027) B11096027
theorem B14041583 : Blo 1538466 14041583 := bstep (se 1 (by rfl) ⟨10531187, by rfl⟩ : syracuseStep 14041583 = 21062375) B21062375
theorem B17539739 : Blo 1538466 17539739 := bstep (se 1 (by rfl) ⟨13154804, by rfl⟩ : syracuseStep 17539739 = 26309609) B26309609
theorem B24954641 : Blo 1538466 24954641 := bstep (se 2 (by rfl) ⟨9357990, by rfl⟩ : syracuseStep 24954641 = 18715981) B18715981
theorem B23431843 : Blo 1538466 23431843 := bstep (se 1 (by rfl) ⟨17573882, by rfl⟩ : syracuseStep 23431843 = 35147765) B35147765
theorem B3697321 : Blo 1538466 3697321 := bstep (se 2 (by rfl) ⟨1386495, by rfl⟩ : syracuseStep 3697321 = 2772991) B2772991
theorem B14789587 : Blo 1538466 14789587 := bstep (se 1 (by rfl) ⟨11092190, by rfl⟩ : syracuseStep 14789587 = 22184381) B22184381
theorem B17533907 : Blo 1538466 17533907 := bstep (se 1 (by rfl) ⟨13150430, by rfl⟩ : syracuseStep 17533907 = 26300861) B26300861
theorem B1559551 : Blo 1538466 1559551 := bstep (se 1 (by rfl) ⟨1169663, by rfl⟩ : syracuseStep 1559551 = 2339327) B2339327
theorem B13143323 : Blo 1538466 13143323 := bstep (se 1 (by rfl) ⟨9857492, by rfl⟩ : syracuseStep 13143323 = 19714985) B19714985
theorem B5845031 : Blo 1538466 5845031 := bstep (se 1 (by rfl) ⟨4383773, by rfl⟩ : syracuseStep 5845031 = 8767547) B8767547
theorem B11686355 : Blo 1538466 11686355 := bstep (se 1 (by rfl) ⟨8764766, by rfl⟩ : syracuseStep 11686355 = 17529533) B17529533
theorem B8770463 : Blo 1538466 8770463 := bstep (se 1 (by rfl) ⟨6577847, by rfl⟩ : syracuseStep 8770463 = 13155695) B13155695
theorem B8664023 : Blo 1538466 8664023 := bstep (se 1 (by rfl) ⟨6498017, by rfl⟩ : syracuseStep 8664023 = 12996035) B12996035
theorem B5846003 : Blo 1538466 5846003 := bstep (se 1 (by rfl) ⟨4384502, by rfl⟩ : syracuseStep 5846003 = 8769005) B8769005
theorem B16635041 : Blo 1538466 16635041 := bstep (se 2 (by rfl) ⟨6238140, by rfl⟩ : syracuseStep 16635041 = 12476281) B12476281
theorem B3462407 : Blo 1538466 3462407 := bstep (se 1 (by rfl) ⟨2596805, by rfl⟩ : syracuseStep 3462407 = 5193611) B5193611
theorem B11687327 : Blo 1538466 11687327 := bstep (se 1 (by rfl) ⟨8765495, by rfl⟩ : syracuseStep 11687327 = 17530991) B17530991
theorem B2307911 : Blo 1538466 2307911 := bstep (se 1 (by rfl) ⟨1730933, by rfl⟩ : syracuseStep 2307911 = 3461867) B3461867
theorem B7018751 : Blo 1538466 7018751 := bstep (se 1 (by rfl) ⟨5264063, by rfl⟩ : syracuseStep 7018751 = 10528127) B10528127
theorem B50608637 : Blo 1538466 50608637 := bstep (se 3 (by rfl) ⟨9489119, by rfl⟩ : syracuseStep 50608637 = 18978239) B18978239
theorem B1538815 : Blo 1538466 1538815 := bstep (se 1 (by rfl) ⟨1154111, by rfl⟩ : syracuseStep 1538815 = 2308223) B2308223
theorem B11098907 : Blo 1538466 11098907 := bstep (se 1 (by rfl) ⟨8324180, by rfl⟩ : syracuseStep 11098907 = 16648361) B16648361
theorem B8551271 : Blo 1538466 8551271 := bstep (se 1 (by rfl) ⟨6413453, by rfl⟩ : syracuseStep 8551271 = 12826907) B12826907
theorem B1948799 : Blo 1538466 1948799 := bstep (se 1 (by rfl) ⟨1461599, by rfl⟩ : syracuseStep 1948799 = 2923199) B2923199
theorem B2309279 : Blo 1538466 2309279 := bstep (se 1 (by rfl) ⟨1731959, by rfl⟩ : syracuseStep 2309279 = 3463919) B3463919
theorem B56958223 : Blo 1538466 56958223 := bstep (se 1 (by rfl) ⟨42718667, by rfl⟩ : syracuseStep 56958223 = 85437335) B85437335
theorem B2309567 : Blo 1538466 2309567 := bstep (se 1 (by rfl) ⟨1732175, by rfl⟩ : syracuseStep 2309567 = 3464351) B3464351
theorem B4931567 : Blo 1538466 4931567 := bstep (se 1 (by rfl) ⟨3698675, by rfl⟩ : syracuseStep 4931567 = 7397351) B7397351
theorem B7790903 : Blo 1538466 7790903 := bstep (se 1 (by rfl) ⟨5843177, by rfl⟩ : syracuseStep 7790903 = 11686355) B11686355
theorem B7791551 : Blo 1538466 7791551 := bstep (se 1 (by rfl) ⟨5843663, by rfl⟩ : syracuseStep 7791551 = 11687327) B11687327
theorem B19719449 : Blo 1538466 19719449 := bstep (se 2 (by rfl) ⟨7394793, by rfl⟩ : syracuseStep 19719449 = 14789587) B14789587
theorem B4679167 : Blo 1538466 4679167 := bstep (se 1 (by rfl) ⟨3509375, by rfl⟩ : syracuseStep 4679167 = 7018751) B7018751
theorem B7399271 : Blo 1538466 7399271 := bstep (se 1 (by rfl) ⟨5549453, by rfl⟩ : syracuseStep 7399271 = 11098907) B11098907
theorem B23104061 : Blo 1538466 23104061 := bstep (se 3 (by rfl) ⟨4332011, by rfl⟩ : syracuseStep 23104061 = 8664023) B8664023
theorem B33270421 : Blo 1538466 33270421 := bstep (se 6 (by rfl) ⟨779775, by rfl⟩ : syracuseStep 33270421 = 1559551) B1559551
theorem B3287711 : Blo 1538466 3287711 := bstep (se 1 (by rfl) ⟨2465783, by rfl⟩ : syracuseStep 3287711 = 4931567) B4931567
theorem B5196797 : Blo 1538466 5196797 := bstep (se 3 (by rfl) ⟨974399, by rfl⟩ : syracuseStep 5196797 = 1948799) B1948799
theorem B11693159 : Blo 1538466 11693159 := bstep (se 1 (by rfl) ⟨8769869, by rfl⟩ : syracuseStep 11693159 = 17539739) B17539739
theorem B33739091 : Blo 1538466 33739091 := bstep (se 1 (by rfl) ⟨25304318, by rfl⟩ : syracuseStep 33739091 = 50608637) B50608637
theorem B75944297 : Blo 1538466 75944297 := bstep (se 2 (by rfl) ⟨28479111, by rfl⟩ : syracuseStep 75944297 = 56958223) B56958223
theorem B8762215 : Blo 1538466 8762215 := bstep (se 1 (by rfl) ⟨6571661, by rfl⟩ : syracuseStep 8762215 = 13143323) B13143323
theorem B3896687 : Blo 1538466 3896687 := bstep (se 1 (by rfl) ⟨2922515, by rfl⟩ : syracuseStep 3896687 = 5845031) B5845031
theorem B9361055 : Blo 1538466 9361055 := bstep (se 1 (by rfl) ⟨7020791, by rfl⟩ : syracuseStep 9361055 = 14041583) B14041583
theorem B5846975 : Blo 1538466 5846975 := bstep (se 1 (by rfl) ⟨4385231, by rfl⟩ : syracuseStep 5846975 = 8770463) B8770463
theorem B3897335 : Blo 1538466 3897335 := bstep (se 1 (by rfl) ⟨2923001, by rfl⟩ : syracuseStep 3897335 = 5846003) B5846003
theorem B11090027 : Blo 1538466 11090027 := bstep (se 1 (by rfl) ⟨8317520, by rfl⟩ : syracuseStep 11090027 = 16635041) B16635041
theorem B2308271 : Blo 1538466 2308271 := bstep (se 1 (by rfl) ⟨1731203, by rfl⟩ : syracuseStep 2308271 = 3462407) B3462407
theorem B31242457 : Blo 1538466 31242457 := bstep (se 2 (by rfl) ⟨11715921, by rfl⟩ : syracuseStep 31242457 = 23431843) B23431843
theorem B4929761 : Blo 1538466 4929761 := bstep (se 2 (by rfl) ⟨1848660, by rfl⟩ : syracuseStep 4929761 = 3697321) B3697321
theorem B16636427 : Blo 1538466 16636427 := bstep (se 1 (by rfl) ⟨12477320, by rfl⟩ : syracuseStep 16636427 = 24954641) B24954641
theorem B1538607 : Blo 1538466 1538607 := bstep (se 1 (by rfl) ⟨1153955, by rfl⟩ : syracuseStep 1538607 = 2307911) B2307911
theorem B5700847 : Blo 1538466 5700847 := bstep (se 1 (by rfl) ⟨4275635, by rfl⟩ : syracuseStep 5700847 = 8551271) B8551271
theorem B11689271 : Blo 1538466 11689271 := bstep (se 1 (by rfl) ⟨8766953, by rfl⟩ : syracuseStep 11689271 = 17533907) B17533907
theorem B1539519 : Blo 1538466 1539519 := bstep (se 1 (by rfl) ⟨1154639, by rfl⟩ : syracuseStep 1539519 = 2309279) B2309279
theorem B1539711 : Blo 1538466 1539711 := bstep (se 1 (by rfl) ⟨1154783, by rfl⟩ : syracuseStep 1539711 = 2309567) B2309567
theorem B5193935 : Blo 1538466 5193935 := bstep (se 1 (by rfl) ⟨3895451, by rfl⟩ : syracuseStep 5193935 = 7790903) B7790903
theorem B41656609 : Blo 1538466 41656609 := bstep (se 2 (by rfl) ⟨15621228, by rfl⟩ : syracuseStep 41656609 = 31242457) B31242457
theorem B5194367 : Blo 1538466 5194367 := bstep (se 1 (by rfl) ⟨3895775, by rfl⟩ : syracuseStep 5194367 = 7791551) B7791551
theorem B44360561 : Blo 1538466 44360561 := bstep (se 2 (by rfl) ⟨16635210, by rfl⟩ : syracuseStep 44360561 = 33270421) B33270421
theorem B2597791 : Blo 1538466 2597791 := bstep (se 1 (by rfl) ⟨1948343, by rfl⟩ : syracuseStep 2597791 = 3896687) B3896687
theorem B11682953 : Blo 1538466 11682953 := bstep (se 2 (by rfl) ⟨4381107, by rfl⟩ : syracuseStep 11682953 = 8762215) B8762215
theorem B4932847 : Blo 1538466 4932847 := bstep (se 1 (by rfl) ⟨3699635, by rfl⟩ : syracuseStep 4932847 = 7399271) B7399271
theorem B2598223 : Blo 1538466 2598223 := bstep (se 1 (by rfl) ⟨1948667, by rfl⟩ : syracuseStep 2598223 = 3897335) B3897335
theorem B3286507 : Blo 1538466 3286507 := bstep (se 1 (by rfl) ⟨2464880, by rfl⟩ : syracuseStep 3286507 = 4929761) B4929761
theorem B15402707 : Blo 1538466 15402707 := bstep (se 1 (by rfl) ⟨11552030, by rfl⟩ : syracuseStep 15402707 = 23104061) B23104061
theorem B24962813 : Blo 1538466 24962813 := bstep (se 3 (by rfl) ⟨4680527, by rfl⟩ : syracuseStep 24962813 = 9361055) B9361055
theorem B7792847 : Blo 1538466 7792847 := bstep (se 1 (by rfl) ⟨5844635, by rfl⟩ : syracuseStep 7792847 = 11689271) B11689271
theorem B50629531 : Blo 1538466 50629531 := bstep (se 1 (by rfl) ⟨37972148, by rfl⟩ : syracuseStep 50629531 = 75944297) B75944297
theorem B7393351 : Blo 1538466 7393351 := bstep (se 1 (by rfl) ⟨5545013, by rfl⟩ : syracuseStep 7393351 = 11090027) B11090027
theorem B2191807 : Blo 1538466 2191807 := bstep (se 1 (by rfl) ⟨1643855, by rfl⟩ : syracuseStep 2191807 = 3287711) B3287711
theorem B6238889 : Blo 1538466 6238889 := bstep (se 2 (by rfl) ⟨2339583, by rfl⟩ : syracuseStep 6238889 = 4679167) B4679167
theorem B7795439 : Blo 1538466 7795439 := bstep (se 1 (by rfl) ⟨5846579, by rfl⟩ : syracuseStep 7795439 = 11693159) B11693159
theorem B22492727 : Blo 1538466 22492727 := bstep (se 1 (by rfl) ⟨16869545, by rfl⟩ : syracuseStep 22492727 = 33739091) B33739091
theorem B13146299 : Blo 1538466 13146299 := bstep (se 1 (by rfl) ⟨9859724, by rfl⟩ : syracuseStep 13146299 = 19719449) B19719449
theorem B3897983 : Blo 1538466 3897983 := bstep (se 1 (by rfl) ⟨2923487, by rfl⟩ : syracuseStep 3897983 = 5846975) B5846975
theorem B1538847 : Blo 1538466 1538847 := bstep (se 1 (by rfl) ⟨1154135, by rfl⟩ : syracuseStep 1538847 = 2308271) B2308271
theorem B7601129 : Blo 1538466 7601129 := bstep (se 2 (by rfl) ⟨2850423, by rfl⟩ : syracuseStep 7601129 = 5700847) B5700847
theorem B11090951 : Blo 1538466 11090951 := bstep (se 1 (by rfl) ⟨8318213, by rfl⟩ : syracuseStep 11090951 = 16636427) B16636427
theorem B3464531 : Blo 1538466 3464531 := bstep (se 1 (by rfl) ⟨2598398, by rfl⟩ : syracuseStep 3464531 = 5196797) B5196797
theorem B55542145 : Blo 1538466 55542145 := bstep (se 2 (by rfl) ⟨20828304, by rfl⟩ : syracuseStep 55542145 = 41656609) B41656609
theorem B29573707 : Blo 1538466 29573707 := bstep (se 1 (by rfl) ⟨22180280, by rfl⟩ : syracuseStep 29573707 = 44360561) B44360561
theorem B5195231 : Blo 1538466 5195231 := bstep (se 1 (by rfl) ⟨3896423, by rfl⟩ : syracuseStep 5195231 = 7792847) B7792847
theorem B2598655 : Blo 1538466 2598655 := bstep (se 1 (by rfl) ⟨1948991, by rfl⟩ : syracuseStep 2598655 = 3897983) B3897983
theorem B9857801 : Blo 1538466 9857801 := bstep (se 2 (by rfl) ⟨3696675, by rfl⟩ : syracuseStep 9857801 = 7393351) B7393351
theorem B5196959 : Blo 1538466 5196959 := bstep (se 1 (by rfl) ⟨3897719, by rfl⟩ : syracuseStep 5196959 = 7795439) B7795439
theorem B14995151 : Blo 1538466 14995151 := bstep (se 1 (by rfl) ⟨11246363, by rfl⟩ : syracuseStep 14995151 = 22492727) B22492727
theorem B10268471 : Blo 1538466 10268471 := bstep (se 1 (by rfl) ⟨7701353, by rfl⟩ : syracuseStep 10268471 = 15402707) B15402707
theorem B16641875 : Blo 1538466 16641875 := bstep (se 1 (by rfl) ⟨12481406, by rfl⟩ : syracuseStep 16641875 = 24962813) B24962813
theorem B67506041 : Blo 1538466 67506041 := bstep (se 2 (by rfl) ⟨25314765, by rfl⟩ : syracuseStep 67506041 = 50629531) B50629531
theorem B5067419 : Blo 1538466 5067419 := bstep (se 1 (by rfl) ⟨3800564, by rfl⟩ : syracuseStep 5067419 = 7601129) B7601129
theorem B7393967 : Blo 1538466 7393967 := bstep (se 1 (by rfl) ⟨5545475, by rfl⟩ : syracuseStep 7393967 = 11090951) B11090951
theorem B3462623 : Blo 1538466 3462623 := bstep (se 1 (by rfl) ⟨2596967, by rfl⟩ : syracuseStep 3462623 = 5193935) B5193935
theorem B3462911 : Blo 1538466 3462911 := bstep (se 1 (by rfl) ⟨2597183, by rfl⟩ : syracuseStep 3462911 = 5194367) B5194367
theorem B4159259 : Blo 1538466 4159259 := bstep (se 1 (by rfl) ⟨3119444, by rfl⟩ : syracuseStep 4159259 = 6238889) B6238889
theorem B2922409 : Blo 1538466 2922409 := bstep (se 2 (by rfl) ⟨1095903, by rfl⟩ : syracuseStep 2922409 = 2191807) B2191807
theorem B7788635 : Blo 1538466 7788635 := bstep (se 1 (by rfl) ⟨5841476, by rfl⟩ : syracuseStep 7788635 = 11682953) B11682953
theorem B3463721 : Blo 1538466 3463721 := bstep (se 2 (by rfl) ⟨1298895, by rfl⟩ : syracuseStep 3463721 = 2597791) B2597791
theorem B8764199 : Blo 1538466 8764199 := bstep (se 1 (by rfl) ⟨6573149, by rfl⟩ : syracuseStep 8764199 = 13146299) B13146299
theorem B6577129 : Blo 1538466 6577129 := bstep (se 2 (by rfl) ⟨2466423, by rfl⟩ : syracuseStep 6577129 = 4932847) B4932847
theorem B3464297 : Blo 1538466 3464297 := bstep (se 2 (by rfl) ⟨1299111, by rfl⟩ : syracuseStep 3464297 = 2598223) B2598223
theorem B4382009 : Blo 1538466 4382009 := bstep (se 2 (by rfl) ⟨1643253, by rfl⟩ : syracuseStep 4382009 = 3286507) B3286507
theorem B2309687 : Blo 1538466 2309687 := bstep (se 1 (by rfl) ⟨1732265, by rfl⟩ : syracuseStep 2309687 = 3464531) B3464531
theorem B74056193 : Blo 1538466 74056193 := bstep (se 2 (by rfl) ⟨27771072, by rfl⟩ : syracuseStep 74056193 = 55542145) B55542145
theorem B6571867 : Blo 1538466 6571867 := bstep (se 1 (by rfl) ⟨4928900, by rfl⟩ : syracuseStep 6571867 = 9857801) B9857801
theorem B5842799 : Blo 1538466 5842799 := bstep (se 1 (by rfl) ⟨4382099, by rfl⟩ : syracuseStep 5842799 = 8764199) B8764199
theorem B9996767 : Blo 1538466 9996767 := bstep (se 1 (by rfl) ⟨7497575, by rfl⟩ : syracuseStep 9996767 = 14995151) B14995151
theorem B11094583 : Blo 1538466 11094583 := bstep (se 1 (by rfl) ⟨8320937, by rfl⟩ : syracuseStep 11094583 = 16641875) B16641875
theorem B39431609 : Blo 1538466 39431609 := bstep (se 2 (by rfl) ⟨14786853, by rfl⟩ : syracuseStep 39431609 = 29573707) B29573707
theorem B2772839 : Blo 1538466 2772839 := bstep (se 1 (by rfl) ⟨2079629, by rfl⟩ : syracuseStep 2772839 = 4159259) B4159259
theorem B8769505 : Blo 1538466 8769505 := bstep (se 2 (by rfl) ⟨3288564, by rfl⟩ : syracuseStep 8769505 = 6577129) B6577129
theorem B13513117 : Blo 1538466 13513117 := bstep (se 3 (by rfl) ⟨2533709, by rfl⟩ : syracuseStep 13513117 = 5067419) B5067419
theorem B2921339 : Blo 1538466 2921339 := bstep (se 1 (by rfl) ⟨2191004, by rfl⟩ : syracuseStep 2921339 = 4382009) B4382009
theorem B6845647 : Blo 1538466 6845647 := bstep (se 1 (by rfl) ⟨5134235, by rfl⟩ : syracuseStep 6845647 = 10268471) B10268471
theorem B3896545 : Blo 1538466 3896545 := bstep (se 2 (by rfl) ⟨1461204, by rfl⟩ : syracuseStep 3896545 = 2922409) B2922409
theorem B45004027 : Blo 1538466 45004027 := bstep (se 1 (by rfl) ⟨33753020, by rfl⟩ : syracuseStep 45004027 = 67506041) B67506041
theorem B4929311 : Blo 1538466 4929311 := bstep (se 1 (by rfl) ⟨3696983, by rfl⟩ : syracuseStep 4929311 = 7393967) B7393967
theorem B2308415 : Blo 1538466 2308415 := bstep (se 1 (by rfl) ⟨1731311, by rfl⟩ : syracuseStep 2308415 = 3462623) B3462623
theorem B3463487 : Blo 1538466 3463487 := bstep (se 1 (by rfl) ⟨2597615, by rfl⟩ : syracuseStep 3463487 = 5195231) B5195231
theorem B2308607 : Blo 1538466 2308607 := bstep (se 1 (by rfl) ⟨1731455, by rfl⟩ : syracuseStep 2308607 = 3462911) B3462911
theorem B5192423 : Blo 1538466 5192423 := bstep (se 1 (by rfl) ⟨3894317, by rfl⟩ : syracuseStep 5192423 = 7788635) B7788635
theorem B2309147 : Blo 1538466 2309147 := bstep (se 1 (by rfl) ⟨1731860, by rfl⟩ : syracuseStep 2309147 = 3463721) B3463721
theorem B2309531 : Blo 1538466 2309531 := bstep (se 1 (by rfl) ⟨1732148, by rfl⟩ : syracuseStep 2309531 = 3464297) B3464297
theorem B3464639 : Blo 1538466 3464639 := bstep (se 1 (by rfl) ⟨2598479, by rfl⟩ : syracuseStep 3464639 = 5196959) B5196959
theorem B3464873 : Blo 1538466 3464873 := bstep (se 2 (by rfl) ⟨1299327, by rfl⟩ : syracuseStep 3464873 = 2598655) B2598655
theorem B1539791 : Blo 1538466 1539791 := bstep (se 1 (by rfl) ⟨1154843, by rfl⟩ : syracuseStep 1539791 = 2309687) B2309687
theorem B3286207 : Blo 1538466 3286207 := bstep (se 1 (by rfl) ⟨2464655, by rfl⟩ : syracuseStep 3286207 = 4929311) B4929311
theorem B9127529 : Blo 1538466 9127529 := bstep (se 2 (by rfl) ⟨3422823, by rfl⟩ : syracuseStep 9127529 = 6845647) B6845647
theorem B5195393 : Blo 1538466 5195393 := bstep (se 2 (by rfl) ⟨1948272, by rfl⟩ : syracuseStep 5195393 = 3896545) B3896545
theorem B11692673 : Blo 1538466 11692673 := bstep (se 2 (by rfl) ⟨4384752, by rfl⟩ : syracuseStep 11692673 = 8769505) B8769505
theorem B18017489 : Blo 1538466 18017489 := bstep (se 2 (by rfl) ⟨6756558, by rfl⟩ : syracuseStep 18017489 = 13513117) B13513117
theorem B3895199 : Blo 1538466 3895199 := bstep (se 1 (by rfl) ⟨2921399, by rfl⟩ : syracuseStep 3895199 = 5842799) B5842799
theorem B6664511 : Blo 1538466 6664511 := bstep (se 1 (by rfl) ⟨4998383, by rfl⟩ : syracuseStep 6664511 = 9996767) B9996767
theorem B3461615 : Blo 1538466 3461615 := bstep (se 1 (by rfl) ⟨2596211, by rfl⟩ : syracuseStep 3461615 = 5192423) B5192423
theorem B7394237 : Blo 1538466 7394237 := bstep (se 3 (by rfl) ⟨1386419, by rfl⟩ : syracuseStep 7394237 = 2772839) B2772839
theorem B8762489 : Blo 1538466 8762489 := bstep (se 2 (by rfl) ⟨3285933, by rfl⟩ : syracuseStep 8762489 = 6571867) B6571867
theorem B49370795 : Blo 1538466 49370795 := bstep (se 1 (by rfl) ⟨37028096, by rfl⟩ : syracuseStep 49370795 = 74056193) B74056193
theorem B1947559 : Blo 1538466 1947559 := bstep (se 1 (by rfl) ⟨1460669, by rfl⟩ : syracuseStep 1947559 = 2921339) B2921339
theorem B14792777 : Blo 1538466 14792777 := bstep (se 2 (by rfl) ⟨5547291, by rfl⟩ : syracuseStep 14792777 = 11094583) B11094583
theorem B1538943 : Blo 1538466 1538943 := bstep (se 1 (by rfl) ⟨1154207, by rfl⟩ : syracuseStep 1538943 = 2308415) B2308415
theorem B2308991 : Blo 1538466 2308991 := bstep (se 1 (by rfl) ⟨1731743, by rfl⟩ : syracuseStep 2308991 = 3463487) B3463487
theorem B60005369 : Blo 1538466 60005369 := bstep (se 2 (by rfl) ⟨22502013, by rfl⟩ : syracuseStep 60005369 = 45004027) B45004027
theorem B1539071 : Blo 1538466 1539071 := bstep (se 1 (by rfl) ⟨1154303, by rfl⟩ : syracuseStep 1539071 = 2308607) B2308607
theorem B1539431 : Blo 1538466 1539431 := bstep (se 1 (by rfl) ⟨1154573, by rfl⟩ : syracuseStep 1539431 = 2309147) B2309147
theorem B1539687 : Blo 1538466 1539687 := bstep (se 1 (by rfl) ⟨1154765, by rfl⟩ : syracuseStep 1539687 = 2309531) B2309531
theorem B26287739 : Blo 1538466 26287739 := bstep (se 1 (by rfl) ⟨19715804, by rfl⟩ : syracuseStep 26287739 = 39431609) B39431609
theorem B2309759 : Blo 1538466 2309759 := bstep (se 1 (by rfl) ⟨1732319, by rfl⟩ : syracuseStep 2309759 = 3464639) B3464639
theorem B2309915 : Blo 1538466 2309915 := bstep (se 1 (by rfl) ⟨1732436, by rfl⟩ : syracuseStep 2309915 = 3464873) B3464873
theorem B5841659 : Blo 1538466 5841659 := bstep (se 1 (by rfl) ⟨4381244, by rfl⟩ : syracuseStep 5841659 = 8762489) B8762489
theorem B40003579 : Blo 1538466 40003579 := bstep (se 1 (by rfl) ⟨30002684, by rfl⟩ : syracuseStep 40003579 = 60005369) B60005369
theorem B12011659 : Blo 1538466 12011659 := bstep (se 1 (by rfl) ⟨9008744, by rfl⟩ : syracuseStep 12011659 = 18017489) B18017489
theorem B17525159 : Blo 1538466 17525159 := bstep (se 1 (by rfl) ⟨13143869, by rfl⟩ : syracuseStep 17525159 = 26287739) B26287739
theorem B4443007 : Blo 1538466 4443007 := bstep (se 1 (by rfl) ⟨3332255, by rfl⟩ : syracuseStep 4443007 = 6664511) B6664511
theorem B7795115 : Blo 1538466 7795115 := bstep (se 1 (by rfl) ⟨5846336, by rfl⟩ : syracuseStep 7795115 = 11692673) B11692673
theorem B2307743 : Blo 1538466 2307743 := bstep (se 1 (by rfl) ⟨1730807, by rfl⟩ : syracuseStep 2307743 = 3461615) B3461615
theorem B4929491 : Blo 1538466 4929491 := bstep (se 1 (by rfl) ⟨3697118, by rfl⟩ : syracuseStep 4929491 = 7394237) B7394237
theorem B6085019 : Blo 1538466 6085019 := bstep (se 1 (by rfl) ⟨4563764, by rfl⟩ : syracuseStep 6085019 = 9127529) B9127529
theorem B3463595 : Blo 1538466 3463595 := bstep (se 1 (by rfl) ⟨2597696, by rfl⟩ : syracuseStep 3463595 = 5195393) B5195393
theorem B32913863 : Blo 1538466 32913863 := bstep (se 1 (by rfl) ⟨24685397, by rfl⟩ : syracuseStep 32913863 = 49370795) B49370795
theorem B9861851 : Blo 1538466 9861851 := bstep (se 1 (by rfl) ⟨7396388, by rfl⟩ : syracuseStep 9861851 = 14792777) B14792777
theorem B4381609 : Blo 1538466 4381609 := bstep (se 2 (by rfl) ⟨1643103, by rfl⟩ : syracuseStep 4381609 = 3286207) B3286207
theorem B1539327 : Blo 1538466 1539327 := bstep (se 1 (by rfl) ⟨1154495, by rfl⟩ : syracuseStep 1539327 = 2308991) B2308991
theorem B1539839 : Blo 1538466 1539839 := bstep (se 1 (by rfl) ⟨1154879, by rfl⟩ : syracuseStep 1539839 = 2309759) B2309759
theorem B1539943 : Blo 1538466 1539943 := bstep (se 1 (by rfl) ⟨1154957, by rfl⟩ : syracuseStep 1539943 = 2309915) B2309915
theorem B2596745 : Blo 1538466 2596745 := bstep (se 2 (by rfl) ⟨973779, by rfl⟩ : syracuseStep 2596745 = 1947559) B1947559
theorem B2596799 : Blo 1538466 2596799 := bstep (se 1 (by rfl) ⟨1947599, by rfl⟩ : syracuseStep 2596799 = 3895199) B3895199
theorem B64062181 : Blo 1538466 64062181 := bstep (se 4 (by rfl) ⟨6005829, by rfl⟩ : syracuseStep 64062181 = 12011659) B12011659
theorem B5924009 : Blo 1538466 5924009 := bstep (se 2 (by rfl) ⟨2221503, by rfl⟩ : syracuseStep 5924009 = 4443007) B4443007
theorem B5842145 : Blo 1538466 5842145 := bstep (se 2 (by rfl) ⟨2190804, by rfl⟩ : syracuseStep 5842145 = 4381609) B4381609
theorem B3286327 : Blo 1538466 3286327 := bstep (se 1 (by rfl) ⟨2464745, by rfl⟩ : syracuseStep 3286327 = 4929491) B4929491
theorem B4056679 : Blo 1538466 4056679 := bstep (se 1 (by rfl) ⟨3042509, by rfl⟩ : syracuseStep 4056679 = 6085019) B6085019
theorem B11683439 : Blo 1538466 11683439 := bstep (se 1 (by rfl) ⟨8762579, by rfl⟩ : syracuseStep 11683439 = 17525159) B17525159
theorem B1731163 : Blo 1538466 1731163 := bstep (se 1 (by rfl) ⟨1298372, by rfl⟩ : syracuseStep 1731163 = 2596745) B2596745
theorem B1731199 : Blo 1538466 1731199 := bstep (se 1 (by rfl) ⟨1298399, by rfl⟩ : syracuseStep 1731199 = 2596799) B2596799
theorem B5196743 : Blo 1538466 5196743 := bstep (se 1 (by rfl) ⟨3897557, by rfl⟩ : syracuseStep 5196743 = 7795115) B7795115
theorem B3894439 : Blo 1538466 3894439 := bstep (se 1 (by rfl) ⟨2920829, by rfl⟩ : syracuseStep 3894439 = 5841659) B5841659
theorem B21942575 : Blo 1538466 21942575 := bstep (se 1 (by rfl) ⟨16456931, by rfl⟩ : syracuseStep 21942575 = 32913863) B32913863
theorem B6574567 : Blo 1538466 6574567 := bstep (se 1 (by rfl) ⟨4930925, by rfl⟩ : syracuseStep 6574567 = 9861851) B9861851
theorem B1538495 : Blo 1538466 1538495 := bstep (se 1 (by rfl) ⟨1153871, by rfl⟩ : syracuseStep 1538495 = 2307743) B2307743
theorem B2309063 : Blo 1538466 2309063 := bstep (se 1 (by rfl) ⟨1731797, by rfl⟩ : syracuseStep 2309063 = 3463595) B3463595
theorem B53338105 : Blo 1538466 53338105 := bstep (se 2 (by rfl) ⟨20001789, by rfl⟩ : syracuseStep 53338105 = 40003579) B40003579
theorem B8766089 : Blo 1538466 8766089 := bstep (se 2 (by rfl) ⟨3287283, by rfl⟩ : syracuseStep 8766089 = 6574567) B6574567
theorem B3949339 : Blo 1538466 3949339 := bstep (se 1 (by rfl) ⟨2962004, by rfl⟩ : syracuseStep 3949339 = 5924009) B5924009
theorem B341664965 : Blo 1538466 341664965 := bstep (se 4 (by rfl) ⟨32031090, by rfl⟩ : syracuseStep 341664965 = 64062181) B64062181
theorem B5408905 : Blo 1538466 5408905 := bstep (se 2 (by rfl) ⟨2028339, by rfl⟩ : syracuseStep 5408905 = 4056679) B4056679
theorem B284469893 : Blo 1538466 284469893 := bstep (se 4 (by rfl) ⟨26669052, by rfl⟩ : syracuseStep 284469893 = 53338105) B53338105
theorem B3894763 : Blo 1538466 3894763 := bstep (se 1 (by rfl) ⟨2921072, by rfl⟩ : syracuseStep 3894763 = 5842145) B5842145
theorem B14628383 : Blo 1538466 14628383 := bstep (se 1 (by rfl) ⟨10971287, by rfl⟩ : syracuseStep 14628383 = 21942575) B21942575
theorem B2308217 : Blo 1538466 2308217 := bstep (se 2 (by rfl) ⟨865581, by rfl⟩ : syracuseStep 2308217 = 1731163) B1731163
theorem B2308265 : Blo 1538466 2308265 := bstep (se 2 (by rfl) ⟨865599, by rfl⟩ : syracuseStep 2308265 = 1731199) B1731199
theorem B7788959 : Blo 1538466 7788959 := bstep (se 1 (by rfl) ⟨5841719, by rfl⟩ : syracuseStep 7788959 = 11683439) B11683439
theorem B5192585 : Blo 1538466 5192585 := bstep (se 2 (by rfl) ⟨1947219, by rfl⟩ : syracuseStep 5192585 = 3894439) B3894439
theorem B4381769 : Blo 1538466 4381769 := bstep (se 2 (by rfl) ⟨1643163, by rfl⟩ : syracuseStep 4381769 = 3286327) B3286327
theorem B1539375 : Blo 1538466 1539375 := bstep (se 1 (by rfl) ⟨1154531, by rfl⟩ : syracuseStep 1539375 = 2309063) B2309063
theorem B3464495 : Blo 1538466 3464495 := bstep (se 1 (by rfl) ⟨2598371, by rfl⟩ : syracuseStep 3464495 = 5196743) B5196743
theorem B189646595 : Blo 1538466 189646595 := bstep (se 1 (by rfl) ⟨142234946, by rfl⟩ : syracuseStep 189646595 = 284469893) B284469893
theorem B7211873 : Blo 1538466 7211873 := bstep (se 2 (by rfl) ⟨2704452, by rfl⟩ : syracuseStep 7211873 = 5408905) B5408905
theorem B5844059 : Blo 1538466 5844059 := bstep (se 1 (by rfl) ⟨4383044, by rfl⟩ : syracuseStep 5844059 = 8766089) B8766089
theorem B9752255 : Blo 1538466 9752255 := bstep (se 1 (by rfl) ⟨7314191, by rfl⟩ : syracuseStep 9752255 = 14628383) B14628383
theorem B3461723 : Blo 1538466 3461723 := bstep (se 1 (by rfl) ⟨2596292, by rfl⟩ : syracuseStep 3461723 = 5192585) B5192585
theorem B2921179 : Blo 1538466 2921179 := bstep (se 1 (by rfl) ⟨2190884, by rfl⟩ : syracuseStep 2921179 = 4381769) B4381769
theorem B227776643 : Blo 1538466 227776643 := bstep (se 1 (by rfl) ⟨170832482, by rfl⟩ : syracuseStep 227776643 = 341664965) B341664965
theorem B5265785 : Blo 1538466 5265785 := bstep (se 2 (by rfl) ⟨1974669, by rfl⟩ : syracuseStep 5265785 = 3949339) B3949339
theorem B1538811 : Blo 1538466 1538811 := bstep (se 1 (by rfl) ⟨1154108, by rfl⟩ : syracuseStep 1538811 = 2308217) B2308217
theorem B1538843 : Blo 1538466 1538843 := bstep (se 1 (by rfl) ⟨1154132, by rfl⟩ : syracuseStep 1538843 = 2308265) B2308265
theorem B5192639 : Blo 1538466 5192639 := bstep (se 1 (by rfl) ⟨3894479, by rfl⟩ : syracuseStep 5192639 = 7788959) B7788959
theorem B5193017 : Blo 1538466 5193017 := bstep (se 2 (by rfl) ⟨1947381, by rfl⟩ : syracuseStep 5193017 = 3894763) B3894763
theorem B2309663 : Blo 1538466 2309663 := bstep (se 1 (by rfl) ⟨1732247, by rfl⟩ : syracuseStep 2309663 = 3464495) B3464495
theorem B3894905 : Blo 1538466 3894905 := bstep (se 2 (by rfl) ⟨1460589, by rfl⟩ : syracuseStep 3894905 = 2921179) B2921179
theorem B126431063 : Blo 1538466 126431063 := bstep (se 1 (by rfl) ⟨94823297, by rfl⟩ : syracuseStep 126431063 = 189646595) B189646595
theorem B151851095 : Blo 1538466 151851095 := bstep (se 1 (by rfl) ⟨113888321, by rfl⟩ : syracuseStep 151851095 = 227776643) B227776643
theorem B3510523 : Blo 1538466 3510523 := bstep (se 1 (by rfl) ⟨2632892, by rfl⟩ : syracuseStep 3510523 = 5265785) B5265785
theorem B3461759 : Blo 1538466 3461759 := bstep (se 1 (by rfl) ⟨2596319, by rfl⟩ : syracuseStep 3461759 = 5192639) B5192639
theorem B3896039 : Blo 1538466 3896039 := bstep (se 1 (by rfl) ⟨2922029, by rfl⟩ : syracuseStep 3896039 = 5844059) B5844059
theorem B3462011 : Blo 1538466 3462011 := bstep (se 1 (by rfl) ⟨2596508, by rfl⟩ : syracuseStep 3462011 = 5193017) B5193017
theorem B19231661 : Blo 1538466 19231661 := bstep (se 3 (by rfl) ⟨3605936, by rfl⟩ : syracuseStep 19231661 = 7211873) B7211873
theorem B6501503 : Blo 1538466 6501503 := bstep (se 1 (by rfl) ⟨4876127, by rfl⟩ : syracuseStep 6501503 = 9752255) B9752255
theorem B2307815 : Blo 1538466 2307815 := bstep (se 1 (by rfl) ⟨1730861, by rfl⟩ : syracuseStep 2307815 = 3461723) B3461723
theorem B1539775 : Blo 1538466 1539775 := bstep (se 1 (by rfl) ⟨1154831, by rfl⟩ : syracuseStep 1539775 = 2309663) B2309663
theorem B2597359 : Blo 1538466 2597359 := bstep (se 1 (by rfl) ⟨1948019, by rfl⟩ : syracuseStep 2597359 = 3896039) B3896039
theorem B12821107 : Blo 1538466 12821107 := bstep (se 1 (by rfl) ⟨9615830, by rfl⟩ : syracuseStep 12821107 = 19231661) B19231661
theorem B4334335 : Blo 1538466 4334335 := bstep (se 1 (by rfl) ⟨3250751, by rfl⟩ : syracuseStep 4334335 = 6501503) B6501503
theorem B18722789 : Blo 1538466 18722789 := bstep (se 4 (by rfl) ⟨1755261, by rfl⟩ : syracuseStep 18722789 = 3510523) B3510523
theorem B101234063 : Blo 1538466 101234063 := bstep (se 1 (by rfl) ⟨75925547, by rfl⟩ : syracuseStep 101234063 = 151851095) B151851095
theorem B2307839 : Blo 1538466 2307839 := bstep (se 1 (by rfl) ⟨1730879, by rfl⟩ : syracuseStep 2307839 = 3461759) B3461759
theorem B2308007 : Blo 1538466 2308007 := bstep (se 1 (by rfl) ⟨1731005, by rfl⟩ : syracuseStep 2308007 = 3462011) B3462011
theorem B1538543 : Blo 1538466 1538543 := bstep (se 1 (by rfl) ⟨1153907, by rfl⟩ : syracuseStep 1538543 = 2307815) B2307815
theorem B2596603 : Blo 1538466 2596603 := bstep (se 1 (by rfl) ⟨1947452, by rfl⟩ : syracuseStep 2596603 = 3894905) B3894905
theorem B84287375 : Blo 1538466 84287375 := bstep (se 1 (by rfl) ⟨63215531, by rfl⟩ : syracuseStep 84287375 = 126431063) B126431063
theorem B56191583 : Blo 1538466 56191583 := bstep (se 1 (by rfl) ⟨42143687, by rfl⟩ : syracuseStep 56191583 = 84287375) B84287375
theorem B92465813 : Blo 1538466 92465813 := bstep (se 6 (by rfl) ⟨2167167, by rfl⟩ : syracuseStep 92465813 = 4334335) B4334335
theorem B67489375 : Blo 1538466 67489375 := bstep (se 1 (by rfl) ⟨50617031, by rfl⟩ : syracuseStep 67489375 = 101234063) B101234063
theorem B3462137 : Blo 1538466 3462137 := bstep (se 2 (by rfl) ⟨1298301, by rfl⟩ : syracuseStep 3462137 = 2596603) B2596603
theorem B12481859 : Blo 1538466 12481859 := bstep (se 1 (by rfl) ⟨9361394, by rfl⟩ : syracuseStep 12481859 = 18722789) B18722789
theorem B3463145 : Blo 1538466 3463145 := bstep (se 2 (by rfl) ⟨1298679, by rfl⟩ : syracuseStep 3463145 = 2597359) B2597359
theorem B17094809 : Blo 1538466 17094809 := bstep (se 2 (by rfl) ⟨6410553, by rfl⟩ : syracuseStep 17094809 = 12821107) B12821107
theorem B1538559 : Blo 1538466 1538559 := bstep (se 1 (by rfl) ⟨1153919, by rfl⟩ : syracuseStep 1538559 = 2307839) B2307839
theorem B1538671 : Blo 1538466 1538671 := bstep (se 1 (by rfl) ⟨1154003, by rfl⟩ : syracuseStep 1538671 = 2308007) B2308007
theorem B11396539 : Blo 1538466 11396539 := bstep (se 1 (by rfl) ⟨8547404, by rfl⟩ : syracuseStep 11396539 = 17094809) B17094809
theorem B89985833 : Blo 1538466 89985833 := bstep (se 2 (by rfl) ⟨33744687, by rfl⟩ : syracuseStep 89985833 = 67489375) B67489375
theorem B2308091 : Blo 1538466 2308091 := bstep (se 1 (by rfl) ⟨1731068, by rfl⟩ : syracuseStep 2308091 = 3462137) B3462137
theorem B8321239 : Blo 1538466 8321239 := bstep (se 1 (by rfl) ⟨6240929, by rfl⟩ : syracuseStep 8321239 = 12481859) B12481859
theorem B2308763 : Blo 1538466 2308763 := bstep (se 1 (by rfl) ⟨1731572, by rfl⟩ : syracuseStep 2308763 = 3463145) B3463145
theorem B37461055 : Blo 1538466 37461055 := bstep (se 1 (by rfl) ⟨28095791, by rfl⟩ : syracuseStep 37461055 = 56191583) B56191583
theorem B61643875 : Blo 1538466 61643875 := bstep (se 1 (by rfl) ⟨46232906, by rfl⟩ : syracuseStep 61643875 = 92465813) B92465813
theorem B59990555 : Blo 1538466 59990555 := bstep (se 1 (by rfl) ⟨44992916, by rfl⟩ : syracuseStep 59990555 = 89985833) B89985833
theorem B49948073 : Blo 1538466 49948073 := bstep (se 2 (by rfl) ⟨18730527, by rfl⟩ : syracuseStep 49948073 = 37461055) B37461055
theorem B82191833 : Blo 1538466 82191833 := bstep (se 2 (by rfl) ⟨30821937, by rfl⟩ : syracuseStep 82191833 = 61643875) B61643875
theorem B11094985 : Blo 1538466 11094985 := bstep (se 2 (by rfl) ⟨4160619, by rfl⟩ : syracuseStep 11094985 = 8321239) B8321239
theorem B1538727 : Blo 1538466 1538727 := bstep (se 1 (by rfl) ⟨1154045, by rfl⟩ : syracuseStep 1538727 = 2308091) B2308091
theorem B1539175 : Blo 1538466 1539175 := bstep (se 1 (by rfl) ⟨1154381, by rfl⟩ : syracuseStep 1539175 = 2308763) B2308763
theorem B15195385 : Blo 1538466 15195385 := bstep (se 2 (by rfl) ⟨5698269, by rfl⟩ : syracuseStep 15195385 = 11396539) B11396539
theorem B159974813 : Blo 1538466 159974813 := bstep (se 3 (by rfl) ⟨29995277, by rfl⟩ : syracuseStep 159974813 = 59990555) B59990555
theorem B20260513 : Blo 1538466 20260513 := bstep (se 2 (by rfl) ⟨7597692, by rfl⟩ : syracuseStep 20260513 = 15195385) B15195385
theorem B33298715 : Blo 1538466 33298715 := bstep (se 1 (by rfl) ⟨24974036, by rfl⟩ : syracuseStep 33298715 = 49948073) B49948073
theorem B54794555 : Blo 1538466 54794555 := bstep (se 1 (by rfl) ⟨41095916, by rfl⟩ : syracuseStep 54794555 = 82191833) B82191833
theorem B14793313 : Blo 1538466 14793313 := bstep (se 2 (by rfl) ⟨5547492, by rfl⟩ : syracuseStep 14793313 = 11094985) B11094985
theorem B36529703 : Blo 1538466 36529703 := bstep (se 1 (by rfl) ⟨27397277, by rfl⟩ : syracuseStep 36529703 = 54794555) B54794555
theorem B27014017 : Blo 1538466 27014017 := bstep (se 2 (by rfl) ⟨10130256, by rfl⟩ : syracuseStep 27014017 = 20260513) B20260513
theorem B19724417 : Blo 1538466 19724417 := bstep (se 2 (by rfl) ⟨7396656, by rfl⟩ : syracuseStep 19724417 = 14793313) B14793313
theorem B106649875 : Blo 1538466 106649875 := bstep (se 1 (by rfl) ⟨79987406, by rfl⟩ : syracuseStep 106649875 = 159974813) B159974813
theorem B22199143 : Blo 1538466 22199143 := bstep (se 1 (by rfl) ⟨16649357, by rfl⟩ : syracuseStep 22199143 = 33298715) B33298715
theorem B29598857 : Blo 1538466 29598857 := bstep (se 2 (by rfl) ⟨11099571, by rfl⟩ : syracuseStep 29598857 = 22199143) B22199143
theorem B13149611 : Blo 1538466 13149611 := bstep (se 1 (by rfl) ⟨9862208, by rfl⟩ : syracuseStep 13149611 = 19724417) B19724417
theorem B142199833 : Blo 1538466 142199833 := bstep (se 2 (by rfl) ⟨53324937, by rfl⟩ : syracuseStep 142199833 = 106649875) B106649875
theorem B24353135 : Blo 1538466 24353135 := bstep (se 1 (by rfl) ⟨18264851, by rfl⟩ : syracuseStep 24353135 = 36529703) B36529703
theorem B36018689 : Blo 1538466 36018689 := bstep (se 2 (by rfl) ⟨13507008, by rfl⟩ : syracuseStep 36018689 = 27014017) B27014017
theorem B8766407 : Blo 1538466 8766407 := bstep (se 1 (by rfl) ⟨6574805, by rfl⟩ : syracuseStep 8766407 = 13149611) B13149611
theorem B189599777 : Blo 1538466 189599777 := bstep (se 2 (by rfl) ⟨71099916, by rfl⟩ : syracuseStep 189599777 = 142199833) B142199833
theorem B19732571 : Blo 1538466 19732571 := bstep (se 1 (by rfl) ⟨14799428, by rfl⟩ : syracuseStep 19732571 = 29598857) B29598857
theorem B96049837 : Blo 1538466 96049837 := bstep (se 3 (by rfl) ⟨18009344, by rfl⟩ : syracuseStep 96049837 = 36018689) B36018689
theorem B16235423 : Blo 1538466 16235423 := bstep (se 1 (by rfl) ⟨12176567, by rfl⟩ : syracuseStep 16235423 = 24353135) B24353135
theorem B128066449 : Blo 1538466 128066449 := bstep (se 2 (by rfl) ⟨48024918, by rfl⟩ : syracuseStep 128066449 = 96049837) B96049837
theorem B10823615 : Blo 1538466 10823615 := bstep (se 1 (by rfl) ⟨8117711, by rfl⟩ : syracuseStep 10823615 = 16235423) B16235423
theorem B5844271 : Blo 1538466 5844271 := bstep (se 1 (by rfl) ⟨4383203, by rfl⟩ : syracuseStep 5844271 = 8766407) B8766407
theorem B126399851 : Blo 1538466 126399851 := bstep (se 1 (by rfl) ⟨94799888, by rfl⟩ : syracuseStep 126399851 = 189599777) B189599777
theorem B13155047 : Blo 1538466 13155047 := bstep (se 1 (by rfl) ⟨9866285, by rfl⟩ : syracuseStep 13155047 = 19732571) B19732571
theorem B170755265 : Blo 1538466 170755265 := bstep (se 2 (by rfl) ⟨64033224, by rfl⟩ : syracuseStep 170755265 = 128066449) B128066449
theorem B7792361 : Blo 1538466 7792361 := bstep (se 2 (by rfl) ⟨2922135, by rfl⟩ : syracuseStep 7792361 = 5844271) B5844271
theorem B84266567 : Blo 1538466 84266567 := bstep (se 1 (by rfl) ⟨63199925, by rfl⟩ : syracuseStep 84266567 = 126399851) B126399851
theorem B8770031 : Blo 1538466 8770031 := bstep (se 1 (by rfl) ⟨6577523, by rfl⟩ : syracuseStep 8770031 = 13155047) B13155047
theorem B7215743 : Blo 1538466 7215743 := bstep (se 1 (by rfl) ⟨5411807, by rfl⟩ : syracuseStep 7215743 = 10823615) B10823615
theorem B113836843 : Blo 1538466 113836843 := bstep (se 1 (by rfl) ⟨85377632, by rfl⟩ : syracuseStep 113836843 = 170755265) B170755265
theorem B5194907 : Blo 1538466 5194907 := bstep (se 1 (by rfl) ⟨3896180, by rfl⟩ : syracuseStep 5194907 = 7792361) B7792361
theorem B4810495 : Blo 1538466 4810495 := bstep (se 1 (by rfl) ⟨3607871, by rfl⟩ : syracuseStep 4810495 = 7215743) B7215743
theorem B56177711 : Blo 1538466 56177711 := bstep (se 1 (by rfl) ⟨42133283, by rfl⟩ : syracuseStep 56177711 = 84266567) B84266567
theorem B5846687 : Blo 1538466 5846687 := bstep (se 1 (by rfl) ⟨4385015, by rfl⟩ : syracuseStep 5846687 = 8770031) B8770031
theorem B151782457 : Blo 1538466 151782457 := bstep (se 2 (by rfl) ⟨56918421, by rfl⟩ : syracuseStep 151782457 = 113836843) B113836843
theorem B37451807 : Blo 1538466 37451807 := bstep (se 1 (by rfl) ⟨28088855, by rfl⟩ : syracuseStep 37451807 = 56177711) B56177711
theorem B3463271 : Blo 1538466 3463271 := bstep (se 1 (by rfl) ⟨2597453, by rfl⟩ : syracuseStep 3463271 = 5194907) B5194907
theorem B3897791 : Blo 1538466 3897791 := bstep (se 1 (by rfl) ⟨2923343, by rfl⟩ : syracuseStep 3897791 = 5846687) B5846687
theorem B6413993 : Blo 1538466 6413993 := bstep (se 2 (by rfl) ⟨2405247, by rfl⟩ : syracuseStep 6413993 = 4810495) B4810495
theorem B202376609 : Blo 1538466 202376609 := bstep (se 2 (by rfl) ⟨75891228, by rfl⟩ : syracuseStep 202376609 = 151782457) B151782457
theorem B2598527 : Blo 1538466 2598527 := bstep (se 1 (by rfl) ⟨1948895, by rfl⟩ : syracuseStep 2598527 = 3897791) B3897791
theorem B24967871 : Blo 1538466 24967871 := bstep (se 1 (by rfl) ⟨18725903, by rfl⟩ : syracuseStep 24967871 = 37451807) B37451807
theorem B2308847 : Blo 1538466 2308847 := bstep (se 1 (by rfl) ⟨1731635, by rfl⟩ : syracuseStep 2308847 = 3463271) B3463271
theorem B4275995 : Blo 1538466 4275995 := bstep (se 1 (by rfl) ⟨3206996, by rfl⟩ : syracuseStep 4275995 = 6413993) B6413993
theorem B134917739 : Blo 1538466 134917739 := bstep (se 1 (by rfl) ⟨101188304, by rfl⟩ : syracuseStep 134917739 = 202376609) B202376609
theorem B1732351 : Blo 1538466 1732351 := bstep (se 1 (by rfl) ⟨1299263, by rfl⟩ : syracuseStep 1732351 = 2598527) B2598527
theorem B16645247 : Blo 1538466 16645247 := bstep (se 1 (by rfl) ⟨12483935, by rfl⟩ : syracuseStep 16645247 = 24967871) B24967871
theorem B1539231 : Blo 1538466 1539231 := bstep (se 1 (by rfl) ⟨1154423, by rfl⟩ : syracuseStep 1539231 = 2308847) B2308847
theorem B11402653 : Blo 1538466 11402653 := bstep (se 3 (by rfl) ⟨2137997, by rfl⟩ : syracuseStep 11402653 = 4275995) B4275995
theorem B11096831 : Blo 1538466 11096831 := bstep (se 1 (by rfl) ⟨8322623, by rfl⟩ : syracuseStep 11096831 = 16645247) B16645247
theorem B89945159 : Blo 1538466 89945159 := bstep (se 1 (by rfl) ⟨67458869, by rfl⟩ : syracuseStep 89945159 = 134917739) B134917739
theorem B15203537 : Blo 1538466 15203537 := bstep (se 2 (by rfl) ⟨5701326, by rfl⟩ : syracuseStep 15203537 = 11402653) B11402653
theorem B2309801 : Blo 1538466 2309801 := bstep (se 2 (by rfl) ⟨866175, by rfl⟩ : syracuseStep 2309801 = 1732351) B1732351
theorem B239853757 : Blo 1538466 239853757 := bstep (se 3 (by rfl) ⟨44972579, by rfl⟩ : syracuseStep 239853757 = 89945159) B89945159
theorem B7397887 : Blo 1538466 7397887 := bstep (se 1 (by rfl) ⟨5548415, by rfl⟩ : syracuseStep 7397887 = 11096831) B11096831
theorem B10135691 : Blo 1538466 10135691 := bstep (se 1 (by rfl) ⟨7601768, by rfl⟩ : syracuseStep 10135691 = 15203537) B15203537
theorem B1539867 : Blo 1538466 1539867 := bstep (se 1 (by rfl) ⟨1154900, by rfl⟩ : syracuseStep 1539867 = 2309801) B2309801
theorem B9863849 : Blo 1538466 9863849 := bstep (se 2 (by rfl) ⟨3698943, by rfl⟩ : syracuseStep 9863849 = 7397887) B7397887
theorem B319805009 : Blo 1538466 319805009 := bstep (se 2 (by rfl) ⟨119926878, by rfl⟩ : syracuseStep 319805009 = 239853757) B239853757
theorem B6757127 : Blo 1538466 6757127 := bstep (se 1 (by rfl) ⟨5067845, by rfl⟩ : syracuseStep 6757127 = 10135691) B10135691
theorem B6575899 : Blo 1538466 6575899 := bstep (se 1 (by rfl) ⟨4931924, by rfl⟩ : syracuseStep 6575899 = 9863849) B9863849
theorem B213203339 : Blo 1538466 213203339 := bstep (se 1 (by rfl) ⟨159902504, by rfl⟩ : syracuseStep 213203339 = 319805009) B319805009
theorem B4504751 : Blo 1538466 4504751 := bstep (se 1 (by rfl) ⟨3378563, by rfl⟩ : syracuseStep 4504751 = 6757127) B6757127
theorem B8767865 : Blo 1538466 8767865 := bstep (se 2 (by rfl) ⟨3287949, by rfl⟩ : syracuseStep 8767865 = 6575899) B6575899
theorem B142135559 : Blo 1538466 142135559 := bstep (se 1 (by rfl) ⟨106601669, by rfl⟩ : syracuseStep 142135559 = 213203339) B213203339
theorem B3003167 : Blo 1538466 3003167 := bstep (se 1 (by rfl) ⟨2252375, by rfl⟩ : syracuseStep 3003167 = 4504751) B4504751
theorem B94757039 : Blo 1538466 94757039 := bstep (se 1 (by rfl) ⟨71067779, by rfl⟩ : syracuseStep 94757039 = 142135559) B142135559
theorem B5845243 : Blo 1538466 5845243 := bstep (se 1 (by rfl) ⟨4383932, by rfl⟩ : syracuseStep 5845243 = 8767865) B8767865
theorem B8008445 : Blo 1538466 8008445 := bstep (se 3 (by rfl) ⟨1501583, by rfl⟩ : syracuseStep 8008445 = 3003167) B3003167
theorem B63171359 : Blo 1538466 63171359 := bstep (se 1 (by rfl) ⟨47378519, by rfl⟩ : syracuseStep 63171359 = 94757039) B94757039
theorem B7793657 : Blo 1538466 7793657 := bstep (se 2 (by rfl) ⟨2922621, by rfl⟩ : syracuseStep 7793657 = 5845243) B5845243
theorem B5338963 : Blo 1538466 5338963 := bstep (se 1 (by rfl) ⟨4004222, by rfl⟩ : syracuseStep 5338963 = 8008445) B8008445
theorem B5195771 : Blo 1538466 5195771 := bstep (se 1 (by rfl) ⟨3896828, by rfl⟩ : syracuseStep 5195771 = 7793657) B7793657
theorem B42114239 : Blo 1538466 42114239 := bstep (se 1 (by rfl) ⟨31585679, by rfl⟩ : syracuseStep 42114239 = 63171359) B63171359
theorem B7118617 : Blo 1538466 7118617 := bstep (se 2 (by rfl) ⟨2669481, by rfl⟩ : syracuseStep 7118617 = 5338963) B5338963
theorem B28076159 : Blo 1538466 28076159 := bstep (se 1 (by rfl) ⟨21057119, by rfl⟩ : syracuseStep 28076159 = 42114239) B42114239
theorem B9491489 : Blo 1538466 9491489 := bstep (se 2 (by rfl) ⟨3559308, by rfl⟩ : syracuseStep 9491489 = 7118617) B7118617
theorem B3463847 : Blo 1538466 3463847 := bstep (se 1 (by rfl) ⟨2597885, by rfl⟩ : syracuseStep 3463847 = 5195771) B5195771
theorem B74869757 : Blo 1538466 74869757 := bstep (se 3 (by rfl) ⟨14038079, by rfl⟩ : syracuseStep 74869757 = 28076159) B28076159
theorem B6327659 : Blo 1538466 6327659 := bstep (se 1 (by rfl) ⟨4745744, by rfl⟩ : syracuseStep 6327659 = 9491489) B9491489
theorem B2309231 : Blo 1538466 2309231 := bstep (se 1 (by rfl) ⟨1731923, by rfl⟩ : syracuseStep 2309231 = 3463847) B3463847
theorem B49913171 : Blo 1538466 49913171 := bstep (se 1 (by rfl) ⟨37434878, by rfl⟩ : syracuseStep 49913171 = 74869757) B74869757
theorem B1539487 : Blo 1538466 1539487 := bstep (se 1 (by rfl) ⟨1154615, by rfl⟩ : syracuseStep 1539487 = 2309231) B2309231
theorem B4218439 : Blo 1538466 4218439 := bstep (se 1 (by rfl) ⟨3163829, by rfl⟩ : syracuseStep 4218439 = 6327659) B6327659
theorem B5624585 : Blo 1538466 5624585 := bstep (se 2 (by rfl) ⟨2109219, by rfl⟩ : syracuseStep 5624585 = 4218439) B4218439
theorem B33275447 : Blo 1538466 33275447 := bstep (se 1 (by rfl) ⟨24956585, by rfl⟩ : syracuseStep 33275447 = 49913171) B49913171
theorem B3749723 : Blo 1538466 3749723 := bstep (se 1 (by rfl) ⟨2812292, by rfl⟩ : syracuseStep 3749723 = 5624585) B5624585
theorem B22183631 : Blo 1538466 22183631 := bstep (se 1 (by rfl) ⟨16637723, by rfl⟩ : syracuseStep 22183631 = 33275447) B33275447
theorem B2499815 : Blo 1538466 2499815 := bstep (se 1 (by rfl) ⟨1874861, by rfl⟩ : syracuseStep 2499815 = 3749723) B3749723
theorem B14789087 : Blo 1538466 14789087 := bstep (se 1 (by rfl) ⟨11091815, by rfl⟩ : syracuseStep 14789087 = 22183631) B22183631
theorem B9859391 : Blo 1538466 9859391 := bstep (se 1 (by rfl) ⟨7394543, by rfl⟩ : syracuseStep 9859391 = 14789087) B14789087
theorem B6666173 : Blo 1538466 6666173 := bstep (se 3 (by rfl) ⟨1249907, by rfl⟩ : syracuseStep 6666173 = 2499815) B2499815
theorem B6572927 : Blo 1538466 6572927 := bstep (se 1 (by rfl) ⟨4929695, by rfl⟩ : syracuseStep 6572927 = 9859391) B9859391
theorem B4444115 : Blo 1538466 4444115 := bstep (se 1 (by rfl) ⟨3333086, by rfl⟩ : syracuseStep 4444115 = 6666173) B6666173
theorem B47403893 : Blo 1538466 47403893 := bstep (se 5 (by rfl) ⟨2222057, by rfl⟩ : syracuseStep 47403893 = 4444115) B4444115
theorem B4381951 : Blo 1538466 4381951 := bstep (se 1 (by rfl) ⟨3286463, by rfl⟩ : syracuseStep 4381951 = 6572927) B6572927
theorem B5842601 : Blo 1538466 5842601 := bstep (se 2 (by rfl) ⟨2190975, by rfl⟩ : syracuseStep 5842601 = 4381951) B4381951
theorem B31602595 : Blo 1538466 31602595 := bstep (se 1 (by rfl) ⟨23701946, by rfl⟩ : syracuseStep 31602595 = 47403893) B47403893
theorem B3895067 : Blo 1538466 3895067 := bstep (se 1 (by rfl) ⟨2921300, by rfl⟩ : syracuseStep 3895067 = 5842601) B5842601
theorem B42136793 : Blo 1538466 42136793 := bstep (se 2 (by rfl) ⟨15801297, by rfl⟩ : syracuseStep 42136793 = 31602595) B31602595
theorem B28091195 : Blo 1538466 28091195 := bstep (se 1 (by rfl) ⟨21068396, by rfl⟩ : syracuseStep 28091195 = 42136793) B42136793
theorem B2596711 : Blo 1538466 2596711 := bstep (se 1 (by rfl) ⟨1947533, by rfl⟩ : syracuseStep 2596711 = 3895067) B3895067
theorem B18727463 : Blo 1538466 18727463 := bstep (se 1 (by rfl) ⟨14045597, by rfl⟩ : syracuseStep 18727463 = 28091195) B28091195
theorem B3462281 : Blo 1538466 3462281 := bstep (se 2 (by rfl) ⟨1298355, by rfl⟩ : syracuseStep 3462281 = 2596711) B2596711
theorem B12484975 : Blo 1538466 12484975 := bstep (se 1 (by rfl) ⟨9363731, by rfl⟩ : syracuseStep 12484975 = 18727463) B18727463
theorem B2308187 : Blo 1538466 2308187 := bstep (se 1 (by rfl) ⟨1731140, by rfl⟩ : syracuseStep 2308187 = 3462281) B3462281
theorem B16646633 : Blo 1538466 16646633 := bstep (se 2 (by rfl) ⟨6242487, by rfl⟩ : syracuseStep 16646633 = 12484975) B12484975
theorem B1538791 : Blo 1538466 1538791 := bstep (se 1 (by rfl) ⟨1154093, by rfl⟩ : syracuseStep 1538791 = 2308187) B2308187
theorem B11097755 : Blo 1538466 11097755 := bstep (se 1 (by rfl) ⟨8323316, by rfl⟩ : syracuseStep 11097755 = 16646633) B16646633
theorem B7398503 : Blo 1538466 7398503 := bstep (se 1 (by rfl) ⟨5548877, by rfl⟩ : syracuseStep 7398503 = 11097755) B11097755
theorem B4932335 : Blo 1538466 4932335 := bstep (se 1 (by rfl) ⟨3699251, by rfl⟩ : syracuseStep 4932335 = 7398503) B7398503
theorem B3288223 : Blo 1538466 3288223 := bstep (se 1 (by rfl) ⟨2466167, by rfl⟩ : syracuseStep 3288223 = 4932335) B4932335
theorem B4384297 : Blo 1538466 4384297 := bstep (se 2 (by rfl) ⟨1644111, by rfl⟩ : syracuseStep 4384297 = 3288223) B3288223
theorem B5845729 : Blo 1538466 5845729 := bstep (se 2 (by rfl) ⟨2192148, by rfl⟩ : syracuseStep 5845729 = 4384297) B4384297
theorem B7794305 : Blo 1538466 7794305 := bstep (se 2 (by rfl) ⟨2922864, by rfl⟩ : syracuseStep 7794305 = 5845729) B5845729
theorem B5196203 : Blo 1538466 5196203 := bstep (se 1 (by rfl) ⟨3897152, by rfl⟩ : syracuseStep 5196203 = 7794305) B7794305
theorem B3464135 : Blo 1538466 3464135 := bstep (se 1 (by rfl) ⟨2598101, by rfl⟩ : syracuseStep 3464135 = 5196203) B5196203
theorem B2309423 : Blo 1538466 2309423 := bstep (se 1 (by rfl) ⟨1732067, by rfl⟩ : syracuseStep 2309423 = 3464135) B3464135
theorem B1539615 : Blo 1538466 1539615 := bstep (se 1 (by rfl) ⟨1154711, by rfl⟩ : syracuseStep 1539615 = 2309423) B2309423

theorem C0 (j : ℕ) (h1 : 384616 ≤ j) (h2 : j ≤ 384990) : Blo 1538466 (4 * j + 3) := by
  interval_cases j
  · exact B1538467
  · exact B1538471
  · exact B1538475
  · exact B1538479
  · exact B1538483
  · exact B1538487
  · exact B1538491
  · exact B1538495
  · exact B1538499
  · exact B1538503
  · exact B1538507
  · exact B1538511
  · exact B1538515
  · exact B1538519
  · exact B1538523
  · exact B1538527
  · exact B1538531
  · exact B1538535
  · exact B1538539
  · exact B1538543
  · exact B1538547
  · exact B1538551
  · exact B1538555
  · exact B1538559
  · exact B1538563
  · exact B1538567
  · exact B1538571
  · exact B1538575
  · exact B1538579
  · exact B1538583
  · exact B1538587
  · exact B1538591
  · exact B1538595
  · exact B1538599
  · exact B1538603
  · exact B1538607
  · exact B1538611
  · exact B1538615
  · exact B1538619
  · exact B1538623
  · exact B1538627
  · exact B1538631
  · exact B1538635
  · exact B1538639
  · exact B1538643
  · exact B1538647
  · exact B1538651
  · exact B1538655
  · exact B1538659
  · exact B1538663
  · exact B1538667
  · exact B1538671
  · exact B1538675
  · exact B1538679
  · exact B1538683
  · exact B1538687
  · exact B1538691
  · exact B1538695
  · exact B1538699
  · exact B1538703
  · exact B1538707
  · exact B1538711
  · exact B1538715
  · exact B1538719
  · exact B1538723
  · exact B1538727
  · exact B1538731
  · exact B1538735
  · exact B1538739
  · exact B1538743
  · exact B1538747
  · exact B1538751
  · exact B1538755
  · exact B1538759
  · exact B1538763
  · exact B1538767
  · exact B1538771
  · exact B1538775
  · exact B1538779
  · exact B1538783
  · exact B1538787
  · exact B1538791
  · exact B1538795
  · exact B1538799
  · exact B1538803
  · exact B1538807
  · exact B1538811
  · exact B1538815
  · exact B1538819
  · exact B1538823
  · exact B1538827
  · exact B1538831
  · exact B1538835
  · exact B1538839
  · exact B1538843
  · exact B1538847
  · exact B1538851
  · exact B1538855
  · exact B1538859
  · exact B1538863
  · exact B1538867
  · exact B1538871
  · exact B1538875
  · exact B1538879
  · exact B1538883
  · exact B1538887
  · exact B1538891
  · exact B1538895
  · exact B1538899
  · exact B1538903
  · exact B1538907
  · exact B1538911
  · exact B1538915
  · exact B1538919
  · exact B1538923
  · exact B1538927
  · exact B1538931
  · exact B1538935
  · exact B1538939
  · exact B1538943
  · exact B1538947
  · exact B1538951
  · exact B1538955
  · exact B1538959
  · exact B1538963
  · exact B1538967
  · exact B1538971
  · exact B1538975
  · exact B1538979
  · exact B1538983
  · exact B1538987
  · exact B1538991
  · exact B1538995
  · exact B1538999
  · exact B1539003
  · exact B1539007
  · exact B1539011
  · exact B1539015
  · exact B1539019
  · exact B1539023
  · exact B1539027
  · exact B1539031
  · exact B1539035
  · exact B1539039
  · exact B1539043
  · exact B1539047
  · exact B1539051
  · exact B1539055
  · exact B1539059
  · exact B1539063
  · exact B1539067
  · exact B1539071
  · exact B1539075
  · exact B1539079
  · exact B1539083
  · exact B1539087
  · exact B1539091
  · exact B1539095
  · exact B1539099
  · exact B1539103
  · exact B1539107
  · exact B1539111
  · exact B1539115
  · exact B1539119
  · exact B1539123
  · exact B1539127
  · exact B1539131
  · exact B1539135
  · exact B1539139
  · exact B1539143
  · exact B1539147
  · exact B1539151
  · exact B1539155
  · exact B1539159
  · exact B1539163
  · exact B1539167
  · exact B1539171
  · exact B1539175
  · exact B1539179
  · exact B1539183
  · exact B1539187
  · exact B1539191
  · exact B1539195
  · exact B1539199
  · exact B1539203
  · exact B1539207
  · exact B1539211
  · exact B1539215
  · exact B1539219
  · exact B1539223
  · exact B1539227
  · exact B1539231
  · exact B1539235
  · exact B1539239
  · exact B1539243
  · exact B1539247
  · exact B1539251
  · exact B1539255
  · exact B1539259
  · exact B1539263
  · exact B1539267
  · exact B1539271
  · exact B1539275
  · exact B1539279
  · exact B1539283
  · exact B1539287
  · exact B1539291
  · exact B1539295
  · exact B1539299
  · exact B1539303
  · exact B1539307
  · exact B1539311
  · exact B1539315
  · exact B1539319
  · exact B1539323
  · exact B1539327
  · exact B1539331
  · exact B1539335
  · exact B1539339
  · exact B1539343
  · exact B1539347
  · exact B1539351
  · exact B1539355
  · exact B1539359
  · exact B1539363
  · exact B1539367
  · exact B1539371
  · exact B1539375
  · exact B1539379
  · exact B1539383
  · exact B1539387
  · exact B1539391
  · exact B1539395
  · exact B1539399
  · exact B1539403
  · exact B1539407
  · exact B1539411
  · exact B1539415
  · exact B1539419
  · exact B1539423
  · exact B1539427
  · exact B1539431
  · exact B1539435
  · exact B1539439
  · exact B1539443
  · exact B1539447
  · exact B1539451
  · exact B1539455
  · exact B1539459
  · exact B1539463
  · exact B1539467
  · exact B1539471
  · exact B1539475
  · exact B1539479
  · exact B1539483
  · exact B1539487
  · exact B1539491
  · exact B1539495
  · exact B1539499
  · exact B1539503
  · exact B1539507
  · exact B1539511
  · exact B1539515
  · exact B1539519
  · exact B1539523
  · exact B1539527
  · exact B1539531
  · exact B1539535
  · exact B1539539
  · exact B1539543
  · exact B1539547
  · exact B1539551
  · exact B1539555
  · exact B1539559
  · exact B1539563
  · exact B1539567
  · exact B1539571
  · exact B1539575
  · exact B1539579
  · exact B1539583
  · exact B1539587
  · exact B1539591
  · exact B1539595
  · exact B1539599
  · exact B1539603
  · exact B1539607
  · exact B1539611
  · exact B1539615
  · exact B1539619
  · exact B1539623
  · exact B1539627
  · exact B1539631
  · exact B1539635
  · exact B1539639
  · exact B1539643
  · exact B1539647
  · exact B1539651
  · exact B1539655
  · exact B1539659
  · exact B1539663
  · exact B1539667
  · exact B1539671
  · exact B1539675
  · exact B1539679
  · exact B1539683
  · exact B1539687
  · exact B1539691
  · exact B1539695
  · exact B1539699
  · exact B1539703
  · exact B1539707
  · exact B1539711
  · exact B1539715
  · exact B1539719
  · exact B1539723
  · exact B1539727
  · exact B1539731
  · exact B1539735
  · exact B1539739
  · exact B1539743
  · exact B1539747
  · exact B1539751
  · exact B1539755
  · exact B1539759
  · exact B1539763
  · exact B1539767
  · exact B1539771
  · exact B1539775
  · exact B1539779
  · exact B1539783
  · exact B1539787
  · exact B1539791
  · exact B1539795
  · exact B1539799
  · exact B1539803
  · exact B1539807
  · exact B1539811
  · exact B1539815
  · exact B1539819
  · exact B1539823
  · exact B1539827
  · exact B1539831
  · exact B1539835
  · exact B1539839
  · exact B1539843
  · exact B1539847
  · exact B1539851
  · exact B1539855
  · exact B1539859
  · exact B1539863
  · exact B1539867
  · exact B1539871
  · exact B1539875
  · exact B1539879
  · exact B1539883
  · exact B1539887
  · exact B1539891
  · exact B1539895
  · exact B1539899
  · exact B1539903
  · exact B1539907
  · exact B1539911
  · exact B1539915
  · exact B1539919
  · exact B1539923
  · exact B1539927
  · exact B1539931
  · exact B1539935
  · exact B1539939
  · exact B1539943
  · exact B1539947
  · exact B1539951
  · exact B1539955
  · exact B1539959
  · exact B1539963

theorem solution (m : ℕ) (hlo : 1538466 ≤ m) (hhi : m ≤ 1539966) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 384616 ≤ j := by omega
    have hj2 : j ≤ 384990 := by omega
    have hb : Blo 1538466 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
