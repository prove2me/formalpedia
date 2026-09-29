-- Prove2me | solution 1 for syracuse_descends_range_904575_906575
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T21:13:02.769168+00:00
-- url     : https://prove2.me/submissions/22879e53-5255-4cd6-91aa-e629eeb84949

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


theorem B1146889 : Blo 904575 1146889 := bbase (se 2 (by rfl) ⟨430083, by rfl⟩ : syracuseStep 1146889 = 860167) (by norm_num)
theorem B1720349 : Blo 904575 1720349 := bbase (se 3 (by rfl) ⟨322565, by rfl⟩ : syracuseStep 1720349 = 645131) (by norm_num)
theorem B3309605 : Blo 904575 3309605 := bbase (se 4 (by rfl) ⟨310275, by rfl⟩ : syracuseStep 3309605 = 620551) (by norm_num)
theorem B2293829 : Blo 904575 2293829 := bbase (se 4 (by rfl) ⟨215046, by rfl⟩ : syracuseStep 2293829 = 430093) (by norm_num)
theorem B2900053 : Blo 904575 2900053 := bbase (se 8 (by rfl) ⟨16992, by rfl⟩ : syracuseStep 2900053 = 33985) (by norm_num)
theorem B1933445 : Blo 904575 1933445 := bbase (se 4 (by rfl) ⟨181260, by rfl⟩ : syracuseStep 1933445 = 362521) (by norm_num)
theorem B2900117 : Blo 904575 2900117 := bbase (se 6 (by rfl) ⟨67971, by rfl⟩ : syracuseStep 2900117 = 135943) (by norm_num)
theorem B3440789 : Blo 904575 3440789 := bbase (se 6 (by rfl) ⟨80643, by rfl⟩ : syracuseStep 3440789 = 161287) (by norm_num)
theorem B966821 : Blo 904575 966821 := bbase (se 4 (by rfl) ⟨90639, by rfl⟩ : syracuseStep 966821 = 181279) (by norm_num)
theorem B1147061 : Blo 904575 1147061 := bbase (se 5 (by rfl) ⟨53768, by rfl⟩ : syracuseStep 1147061 = 107537) (by norm_num)
theorem B917737 : Blo 904575 917737 := bbase (se 2 (by rfl) ⟨344151, by rfl⟩ : syracuseStep 917737 = 688303) (by norm_num)
theorem B1655021 : Blo 904575 1655021 := bbase (se 3 (by rfl) ⟨310316, by rfl⟩ : syracuseStep 1655021 = 620633) (by norm_num)
theorem B1147117 : Blo 904575 1147117 := bbase (se 3 (by rfl) ⟨215084, by rfl⟩ : syracuseStep 1147117 = 430169) (by norm_num)
theorem B2294021 : Blo 904575 2294021 := bbase (se 4 (by rfl) ⟨215064, by rfl⟩ : syracuseStep 2294021 = 430129) (by norm_num)
theorem B1147213 : Blo 904575 1147213 := bbase (se 3 (by rfl) ⟨215102, by rfl⟩ : syracuseStep 1147213 = 430205) (by norm_num)
theorem B4350293 : Blo 904575 4350293 := bbase (se 10 (by rfl) ⟨6372, by rfl⟩ : syracuseStep 4350293 = 12745) (by norm_num)
theorem B2064781 : Blo 904575 2064781 := bbase (se 3 (by rfl) ⟨387146, by rfl⟩ : syracuseStep 2064781 = 774293) (by norm_num)
theorem B3056021 : Blo 904575 3056021 := bbase (se 6 (by rfl) ⟨71625, by rfl⟩ : syracuseStep 3056021 = 143251) (by norm_num)
theorem B942509 : Blo 904575 942509 := bbase (se 3 (by rfl) ⟨176720, by rfl⟩ : syracuseStep 942509 = 353441) (by norm_num)
theorem B3350965 : Blo 904575 3350965 := bbase (se 5 (by rfl) ⟨157076, by rfl⟩ : syracuseStep 3350965 = 314153) (by norm_num)
theorem B3867061 : Blo 904575 3867061 := bbase (se 5 (by rfl) ⟨181268, by rfl⟩ : syracuseStep 3867061 = 362537) (by norm_num)
theorem B4645349 : Blo 904575 4645349 := bbase (se 4 (by rfl) ⟨435501, by rfl⟩ : syracuseStep 4645349 = 871003) (by norm_num)
theorem B1450469 : Blo 904575 1450469 := bbase (se 4 (by rfl) ⟨135981, by rfl⟩ : syracuseStep 1450469 = 271963) (by norm_num)
theorem B1147385 : Blo 904575 1147385 := bbase (se 2 (by rfl) ⟨430269, by rfl⟩ : syracuseStep 1147385 = 860539) (by norm_num)
theorem B2294365 : Blo 904575 2294365 := bbase (se 3 (by rfl) ⟨430193, by rfl⟩ : syracuseStep 2294365 = 860387) (by norm_num)
theorem B1548941 : Blo 904575 1548941 := bbase (se 3 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 1548941 = 580853) (by norm_num)
theorem B2761381 : Blo 904575 2761381 := bbase (se 4 (by rfl) ⟨258879, by rfl⟩ : syracuseStep 2761381 = 517759) (by norm_num)
theorem B2294477 : Blo 904575 2294477 := bbase (se 3 (by rfl) ⟨430214, by rfl⟩ : syracuseStep 2294477 = 860429) (by norm_num)
theorem B2581253 : Blo 904575 2581253 := bbase (se 4 (by rfl) ⟨241992, by rfl⟩ : syracuseStep 2581253 = 483985) (by norm_num)
theorem B3261221 : Blo 904575 3261221 := bbase (se 4 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 3261221 = 611479) (by norm_num)
theorem B4588325 : Blo 904575 4588325 := bbase (se 4 (by rfl) ⟨430155, by rfl⟩ : syracuseStep 4588325 = 860311) (by norm_num)
theorem B3056453 : Blo 904575 3056453 := bbase (se 4 (by rfl) ⟨286542, by rfl⟩ : syracuseStep 3056453 = 573085) (by norm_num)
theorem B1450853 : Blo 904575 1450853 := bbase (se 4 (by rfl) ⟨136017, by rfl⟩ : syracuseStep 1450853 = 272035) (by norm_num)
theorem B1934189 : Blo 904575 1934189 := bbase (se 3 (by rfl) ⟨362660, by rfl⟩ : syracuseStep 1934189 = 725321) (by norm_num)
theorem B2294669 : Blo 904575 2294669 := bbase (se 3 (by rfl) ⟨430250, by rfl⟩ : syracuseStep 2294669 = 860501) (by norm_num)
theorem B967573 : Blo 904575 967573 := bbase (se 6 (by rfl) ⟨22677, by rfl⟩ : syracuseStep 967573 = 45355) (by norm_num)
theorem B967645 : Blo 904575 967645 := bbase (se 3 (by rfl) ⟨181433, by rfl⟩ : syracuseStep 967645 = 362867) (by norm_num)
theorem B1450981 : Blo 904575 1450981 := bbase (se 4 (by rfl) ⟨136029, by rfl⟩ : syracuseStep 1450981 = 272059) (by norm_num)
theorem B7734325 : Blo 904575 7734325 := bbase (se 5 (by rfl) ⟨362546, by rfl⟩ : syracuseStep 7734325 = 725093) (by norm_num)
theorem B4891765 : Blo 904575 4891765 := bbase (se 5 (by rfl) ⟨229301, by rfl⟩ : syracuseStep 4891765 = 458603) (by norm_num)
theorem B967825 : Blo 904575 967825 := bbase (se 2 (by rfl) ⟨362934, by rfl⟩ : syracuseStep 967825 = 725869) (by norm_num)
theorem B4580549 : Blo 904575 4580549 := bbase (se 4 (by rfl) ⟨429426, by rfl⟩ : syracuseStep 4580549 = 858853) (by norm_num)
theorem B3261637 : Blo 904575 3261637 := bbase (se 4 (by rfl) ⟨305778, by rfl⟩ : syracuseStep 3261637 = 611557) (by norm_num)
theorem B3261653 : Blo 904575 3261653 := bbase (se 7 (by rfl) ⟨38222, by rfl⟩ : syracuseStep 3261653 = 76445) (by norm_num)
theorem B1377493 : Blo 904575 1377493 := bbase (se 7 (by rfl) ⟨16142, by rfl⟩ : syracuseStep 1377493 = 32285) (by norm_num)
theorem B3056885 : Blo 904575 3056885 := bbase (se 5 (by rfl) ⟨143291, by rfl⟩ : syracuseStep 3056885 = 286583) (by norm_num)
theorem B3441973 : Blo 904575 3441973 := bbase (se 5 (by rfl) ⟨161342, by rfl⟩ : syracuseStep 3441973 = 322685) (by norm_num)
theorem B1631605 : Blo 904575 1631605 := bbase (se 5 (by rfl) ⟨76481, by rfl⟩ : syracuseStep 1631605 = 152963) (by norm_num)
theorem B3261941 : Blo 904575 3261941 := bbase (se 5 (by rfl) ⟨152903, by rfl⟩ : syracuseStep 3261941 = 305807) (by norm_num)
theorem B1631821 : Blo 904575 1631821 := bbase (se 3 (by rfl) ⟨305966, by rfl⟩ : syracuseStep 1631821 = 611933) (by norm_num)
theorem B10315349 : Blo 904575 10315349 := bbase (se 8 (by rfl) ⟨60441, by rfl⟩ : syracuseStep 10315349 = 120883) (by norm_num)
theorem B1934941 : Blo 904575 1934941 := bbase (se 3 (by rfl) ⟨362801, by rfl⟩ : syracuseStep 1934941 = 725603) (by norm_num)
theorem B2066077 : Blo 904575 2066077 := bbase (se 3 (by rfl) ⟨387389, by rfl⟩ : syracuseStep 2066077 = 774779) (by norm_num)
theorem B3057317 : Blo 904575 3057317 := bbase (se 4 (by rfl) ⟨286623, by rfl⟩ : syracuseStep 3057317 = 573247) (by norm_num)
theorem B4966069 : Blo 904575 4966069 := bbase (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) (by norm_num)
theorem B1935085 : Blo 904575 1935085 := bbase (se 3 (by rfl) ⟨362828, by rfl⟩ : syracuseStep 1935085 = 725657) (by norm_num)
theorem B1017661 : Blo 904575 1017661 := bbase (se 3 (by rfl) ⟨190811, by rfl⟩ : syracuseStep 1017661 = 381623) (by norm_num)
theorem B1017697 : Blo 904575 1017697 := bbase (se 2 (by rfl) ⟨381636, by rfl⟩ : syracuseStep 1017697 = 763273) (by norm_num)
theorem B1836901 : Blo 904575 1836901 := bbase (se 4 (by rfl) ⟨172209, by rfl⟩ : syracuseStep 1836901 = 344419) (by norm_num)
theorem B1017733 : Blo 904575 1017733 := bbase (se 4 (by rfl) ⟨95412, by rfl⟩ : syracuseStep 1017733 = 190825) (by norm_num)
theorem B8710037 : Blo 904575 8710037 := bbase (se 6 (by rfl) ⟨204141, by rfl⟩ : syracuseStep 8710037 = 408283) (by norm_num)
theorem B1017769 : Blo 904575 1017769 := bbase (se 2 (by rfl) ⟨381663, by rfl⟩ : syracuseStep 1017769 = 763327) (by norm_num)
theorem B1288109 : Blo 904575 1288109 := bbase (se 3 (by rfl) ⟨241520, by rfl⟩ : syracuseStep 1288109 = 483041) (by norm_num)
theorem B1017805 : Blo 904575 1017805 := bbase (se 3 (by rfl) ⟨190838, by rfl⟩ : syracuseStep 1017805 = 381677) (by norm_num)
theorem B1451981 : Blo 904575 1451981 := bbase (se 3 (by rfl) ⟨272246, by rfl⟩ : syracuseStep 1451981 = 544493) (by norm_num)
theorem B1017841 : Blo 904575 1017841 := bbase (se 2 (by rfl) ⟨381690, by rfl⟩ : syracuseStep 1017841 = 763381) (by norm_num)
theorem B1017877 : Blo 904575 1017877 := bbase (se 6 (by rfl) ⟨23856, by rfl⟩ : syracuseStep 1017877 = 47713) (by norm_num)
theorem B1017913 : Blo 904575 1017913 := bbase (se 2 (by rfl) ⟨381717, by rfl⟩ : syracuseStep 1017913 = 763435) (by norm_num)
theorem B1452109 : Blo 904575 1452109 := bbase (se 3 (by rfl) ⟨272270, by rfl⟩ : syracuseStep 1452109 = 544541) (by norm_num)
theorem B3057749 : Blo 904575 3057749 := bbase (se 8 (by rfl) ⟨17916, by rfl⟩ : syracuseStep 3057749 = 35833) (by norm_num)
theorem B1017949 : Blo 904575 1017949 := bbase (se 3 (by rfl) ⟨190865, by rfl⟩ : syracuseStep 1017949 = 381731) (by norm_num)
theorem B1935461 : Blo 904575 1935461 := bbase (se 4 (by rfl) ⟨181449, by rfl⟩ : syracuseStep 1935461 = 362899) (by norm_num)
theorem B1017985 : Blo 904575 1017985 := bbase (se 2 (by rfl) ⟨381744, by rfl⟩ : syracuseStep 1017985 = 763489) (by norm_num)
theorem B9799829 : Blo 904575 9799829 := bbase (se 6 (by rfl) ⟨229683, by rfl⟩ : syracuseStep 9799829 = 459367) (by norm_num)
theorem B1018021 : Blo 904575 1018021 := bbase (se 4 (by rfl) ⟨95439, by rfl⟩ : syracuseStep 1018021 = 190879) (by norm_num)
theorem B1018057 : Blo 904575 1018057 := bbase (se 2 (by rfl) ⟨381771, by rfl⟩ : syracuseStep 1018057 = 763543) (by norm_num)
theorem B1018093 : Blo 904575 1018093 := bbase (se 3 (by rfl) ⟨190892, by rfl⟩ : syracuseStep 1018093 = 381785) (by norm_num)
theorem B1018129 : Blo 904575 1018129 := bbase (se 2 (by rfl) ⟨381798, by rfl⟩ : syracuseStep 1018129 = 763597) (by norm_num)
theorem B3672341 : Blo 904575 3672341 := bbase (se 6 (by rfl) ⟨86070, by rfl⟩ : syracuseStep 3672341 = 172141) (by norm_num)
theorem B1018165 : Blo 904575 1018165 := bbase (se 5 (by rfl) ⟨47726, by rfl⟩ : syracuseStep 1018165 = 95453) (by norm_num)
theorem B1837397 : Blo 904575 1837397 := bbase (se 10 (by rfl) ⟨2691, by rfl⟩ : syracuseStep 1837397 = 5383) (by norm_num)
theorem B1018201 : Blo 904575 1018201 := bbase (se 2 (by rfl) ⟨381825, by rfl⟩ : syracuseStep 1018201 = 763651) (by norm_num)
theorem B1018237 : Blo 904575 1018237 := bbase (se 3 (by rfl) ⟨190919, by rfl⟩ : syracuseStep 1018237 = 381839) (by norm_num)
theorem B1018273 : Blo 904575 1018273 := bbase (se 2 (by rfl) ⟨381852, by rfl⟩ : syracuseStep 1018273 = 763705) (by norm_num)
theorem B1018309 : Blo 904575 1018309 := bbase (se 4 (by rfl) ⟨95466, by rfl⟩ : syracuseStep 1018309 = 190933) (by norm_num)
theorem B4581845 : Blo 904575 4581845 := bbase (se 7 (by rfl) ⟨53693, by rfl⟩ : syracuseStep 4581845 = 107387) (by norm_num)
theorem B1935829 : Blo 904575 1935829 := bbase (se 7 (by rfl) ⟨22685, by rfl⟩ : syracuseStep 1935829 = 45371) (by norm_num)
theorem B1018345 : Blo 904575 1018345 := bbase (se 2 (by rfl) ⟨381879, by rfl⟩ : syracuseStep 1018345 = 763759) (by norm_num)
theorem B3058181 : Blo 904575 3058181 := bbase (se 4 (by rfl) ⟨286704, by rfl⟩ : syracuseStep 3058181 = 573409) (by norm_num)
theorem B1018381 : Blo 904575 1018381 := bbase (se 3 (by rfl) ⟨190946, by rfl⟩ : syracuseStep 1018381 = 381893) (by norm_num)
theorem B1018417 : Blo 904575 1018417 := bbase (se 2 (by rfl) ⟨381906, by rfl⟩ : syracuseStep 1018417 = 763813) (by norm_num)
theorem B1018453 : Blo 904575 1018453 := bbase (se 8 (by rfl) ⟨5967, by rfl⟩ : syracuseStep 1018453 = 11935) (by norm_num)
theorem B1018489 : Blo 904575 1018489 := bbase (se 2 (by rfl) ⟨381933, by rfl⟩ : syracuseStep 1018489 = 763867) (by norm_num)
theorem B1018525 : Blo 904575 1018525 := bbase (se 3 (by rfl) ⟨190973, by rfl⟩ : syracuseStep 1018525 = 381947) (by norm_num)
theorem B1018561 : Blo 904575 1018561 := bbase (se 2 (by rfl) ⟨381960, by rfl⟩ : syracuseStep 1018561 = 763921) (by norm_num)
theorem B1526485 : Blo 904575 1526485 := bbase (se 7 (by rfl) ⟨17888, by rfl⟩ : syracuseStep 1526485 = 35777) (by norm_num)
theorem B1469141 : Blo 904575 1469141 := bbase (se 7 (by rfl) ⟨17216, by rfl⟩ : syracuseStep 1469141 = 34433) (by norm_num)
theorem B1018597 : Blo 904575 1018597 := bbase (se 4 (by rfl) ⟨95493, by rfl⟩ : syracuseStep 1018597 = 190987) (by norm_num)
theorem B1018633 : Blo 904575 1018633 := bbase (se 2 (by rfl) ⟨381987, by rfl⟩ : syracuseStep 1018633 = 763975) (by norm_num)
theorem B1526573 : Blo 904575 1526573 := bbase (se 3 (by rfl) ⟨286232, by rfl⟩ : syracuseStep 1526573 = 572465) (by norm_num)
theorem B1018669 : Blo 904575 1018669 := bbase (se 3 (by rfl) ⟨191000, by rfl⟩ : syracuseStep 1018669 = 382001) (by norm_num)
theorem B1018705 : Blo 904575 1018705 := bbase (se 2 (by rfl) ⟨382014, by rfl⟩ : syracuseStep 1018705 = 764029) (by norm_num)
theorem B2321237 : Blo 904575 2321237 := bbase (se 9 (by rfl) ⟨6800, by rfl⟩ : syracuseStep 2321237 = 13601) (by norm_num)
theorem B1018741 : Blo 904575 1018741 := bbase (se 5 (by rfl) ⟨47753, by rfl⟩ : syracuseStep 1018741 = 95507) (by norm_num)
theorem B2206597 : Blo 904575 2206597 := bbase (se 4 (by rfl) ⟨206868, by rfl⟩ : syracuseStep 2206597 = 413737) (by norm_num)
theorem B3263381 : Blo 904575 3263381 := bbase (se 6 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 3263381 = 152971) (by norm_num)
theorem B1018777 : Blo 904575 1018777 := bbase (se 2 (by rfl) ⟨382041, by rfl⟩ : syracuseStep 1018777 = 764083) (by norm_num)
theorem B1526701 : Blo 904575 1526701 := bbase (se 3 (by rfl) ⟨286256, by rfl⟩ : syracuseStep 1526701 = 572513) (by norm_num)
theorem B3058613 : Blo 904575 3058613 := bbase (se 5 (by rfl) ⟨143372, by rfl⟩ : syracuseStep 3058613 = 286745) (by norm_num)
theorem B1018813 : Blo 904575 1018813 := bbase (se 3 (by rfl) ⟨191027, by rfl⟩ : syracuseStep 1018813 = 382055) (by norm_num)
theorem B1018849 : Blo 904575 1018849 := bbase (se 2 (by rfl) ⟨382068, by rfl⟩ : syracuseStep 1018849 = 764137) (by norm_num)
theorem B7736309 : Blo 904575 7736309 := bbase (se 5 (by rfl) ⟨362639, by rfl⟩ : syracuseStep 7736309 = 725279) (by norm_num)
theorem B1633277 : Blo 904575 1633277 := bbase (se 3 (by rfl) ⟨306239, by rfl⟩ : syracuseStep 1633277 = 612479) (by norm_num)
theorem B1526789 : Blo 904575 1526789 := bbase (se 4 (by rfl) ⟨143136, by rfl⟩ : syracuseStep 1526789 = 286273) (by norm_num)
theorem B1018885 : Blo 904575 1018885 := bbase (se 4 (by rfl) ⟨95520, by rfl⟩ : syracuseStep 1018885 = 191041) (by norm_num)
theorem B1018921 : Blo 904575 1018921 := bbase (se 2 (by rfl) ⟨382095, by rfl⟩ : syracuseStep 1018921 = 764191) (by norm_num)
theorem B1018957 : Blo 904575 1018957 := bbase (se 3 (by rfl) ⟨191054, by rfl⟩ : syracuseStep 1018957 = 382109) (by norm_num)
theorem B7842901 : Blo 904575 7842901 := bbase (se 8 (by rfl) ⟨45954, by rfl⟩ : syracuseStep 7842901 = 91909) (by norm_num)
theorem B2903141 : Blo 904575 2903141 := bbase (se 4 (by rfl) ⟨272169, by rfl⟩ : syracuseStep 2903141 = 544339) (by norm_num)
theorem B1018993 : Blo 904575 1018993 := bbase (se 2 (by rfl) ⟨382122, by rfl⟩ : syracuseStep 1018993 = 764245) (by norm_num)
theorem B1526917 : Blo 904575 1526917 := bbase (se 4 (by rfl) ⟨143148, by rfl⟩ : syracuseStep 1526917 = 286297) (by norm_num)
theorem B1633421 : Blo 904575 1633421 := bbase (se 3 (by rfl) ⟨306266, by rfl⟩ : syracuseStep 1633421 = 612533) (by norm_num)
theorem B1019029 : Blo 904575 1019029 := bbase (se 6 (by rfl) ⟨23883, by rfl⟩ : syracuseStep 1019029 = 47767) (by norm_num)
theorem B4353173 : Blo 904575 4353173 := bbase (se 6 (by rfl) ⟨102027, by rfl⟩ : syracuseStep 4353173 = 204055) (by norm_num)
theorem B8694965 : Blo 904575 8694965 := bbase (se 5 (by rfl) ⟨407576, by rfl⟩ : syracuseStep 8694965 = 815153) (by norm_num)
theorem B1019065 : Blo 904575 1019065 := bbase (se 2 (by rfl) ⟨382149, by rfl⟩ : syracuseStep 1019065 = 764299) (by norm_num)
theorem B1633493 : Blo 904575 1633493 := bbase (se 7 (by rfl) ⟨19142, by rfl⟩ : syracuseStep 1633493 = 38285) (by norm_num)
theorem B1527005 : Blo 904575 1527005 := bbase (se 3 (by rfl) ⟨286313, by rfl⟩ : syracuseStep 1527005 = 572627) (by norm_num)
theorem B1019101 : Blo 904575 1019101 := bbase (se 3 (by rfl) ⟨191081, by rfl⟩ : syracuseStep 1019101 = 382163) (by norm_num)
theorem B1019137 : Blo 904575 1019137 := bbase (se 2 (by rfl) ⟨382176, by rfl⟩ : syracuseStep 1019137 = 764353) (by norm_num)
theorem B1019173 : Blo 904575 1019173 := bbase (se 4 (by rfl) ⟨95547, by rfl⟩ : syracuseStep 1019173 = 191095) (by norm_num)
theorem B3484981 : Blo 904575 3484981 := bbase (se 5 (by rfl) ⟨163358, by rfl⟩ : syracuseStep 3484981 = 326717) (by norm_num)
theorem B1289533 : Blo 904575 1289533 := bbase (se 3 (by rfl) ⟨241787, by rfl⟩ : syracuseStep 1289533 = 483575) (by norm_num)
theorem B1019209 : Blo 904575 1019209 := bbase (se 2 (by rfl) ⟨382203, by rfl⟩ : syracuseStep 1019209 = 764407) (by norm_num)
theorem B1527133 : Blo 904575 1527133 := bbase (se 3 (by rfl) ⟨286337, by rfl⟩ : syracuseStep 1527133 = 572675) (by norm_num)
theorem B3059045 : Blo 904575 3059045 := bbase (se 4 (by rfl) ⟨286785, by rfl⟩ : syracuseStep 3059045 = 573571) (by norm_num)
theorem B1019245 : Blo 904575 1019245 := bbase (se 3 (by rfl) ⟨191108, by rfl⟩ : syracuseStep 1019245 = 382217) (by norm_num)
theorem B1019281 : Blo 904575 1019281 := bbase (se 2 (by rfl) ⟨382230, by rfl⟩ : syracuseStep 1019281 = 764461) (by norm_num)
theorem B6532501 : Blo 904575 6532501 := bbase (se 6 (by rfl) ⟨153105, by rfl⟩ : syracuseStep 6532501 = 306211) (by norm_num)
theorem B1527221 : Blo 904575 1527221 := bbase (se 5 (by rfl) ⟨71588, by rfl⟩ : syracuseStep 1527221 = 143177) (by norm_num)
theorem B1019317 : Blo 904575 1019317 := bbase (se 5 (by rfl) ⟨47780, by rfl⟩ : syracuseStep 1019317 = 95561) (by norm_num)
theorem B1019353 : Blo 904575 1019353 := bbase (se 2 (by rfl) ⟨382257, by rfl⟩ : syracuseStep 1019353 = 764515) (by norm_num)
theorem B1019389 : Blo 904575 1019389 := bbase (se 3 (by rfl) ⟨191135, by rfl⟩ : syracuseStep 1019389 = 382271) (by norm_num)
theorem B1019425 : Blo 904575 1019425 := bbase (se 2 (by rfl) ⟨382284, by rfl⟩ : syracuseStep 1019425 = 764569) (by norm_num)
theorem B1527349 : Blo 904575 1527349 := bbase (se 5 (by rfl) ⟨71594, by rfl⟩ : syracuseStep 1527349 = 143189) (by norm_num)
theorem B1019461 : Blo 904575 1019461 := bbase (se 4 (by rfl) ⟨95574, by rfl⟩ : syracuseStep 1019461 = 191149) (by norm_num)
theorem B1019497 : Blo 904575 1019497 := bbase (se 2 (by rfl) ⟨382311, by rfl⟩ : syracuseStep 1019497 = 764623) (by norm_num)
theorem B1527437 : Blo 904575 1527437 := bbase (se 3 (by rfl) ⟨286394, by rfl⟩ : syracuseStep 1527437 = 572789) (by norm_num)
theorem B1019533 : Blo 904575 1019533 := bbase (se 3 (by rfl) ⟨191162, by rfl⟩ : syracuseStep 1019533 = 382325) (by norm_num)
theorem B2035349 : Blo 904575 2035349 := bbase (se 6 (by rfl) ⟨47703, by rfl⟩ : syracuseStep 2035349 = 95407) (by norm_num)
theorem B1019569 : Blo 904575 1019569 := bbase (se 2 (by rfl) ⟨382338, by rfl⟩ : syracuseStep 1019569 = 764677) (by norm_num)
theorem B1019605 : Blo 904575 1019605 := bbase (se 7 (by rfl) ⟨11948, by rfl⟩ : syracuseStep 1019605 = 23897) (by norm_num)
theorem B2035421 : Blo 904575 2035421 := bbase (se 3 (by rfl) ⟨381641, by rfl⟩ : syracuseStep 2035421 = 763283) (by norm_num)
theorem B4583141 : Blo 904575 4583141 := bbase (se 4 (by rfl) ⟨429669, by rfl⟩ : syracuseStep 4583141 = 859339) (by norm_num)
theorem B1019641 : Blo 904575 1019641 := bbase (se 2 (by rfl) ⟨382365, by rfl⟩ : syracuseStep 1019641 = 764731) (by norm_num)
theorem B1527565 : Blo 904575 1527565 := bbase (se 3 (by rfl) ⟨286418, by rfl⟩ : syracuseStep 1527565 = 572837) (by norm_num)
theorem B3059477 : Blo 904575 3059477 := bbase (se 6 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 3059477 = 143413) (by norm_num)
theorem B1019677 : Blo 904575 1019677 := bbase (se 3 (by rfl) ⟨191189, by rfl⟩ : syracuseStep 1019677 = 382379) (by norm_num)
theorem B2035493 : Blo 904575 2035493 := bbase (se 4 (by rfl) ⟨190827, by rfl⟩ : syracuseStep 2035493 = 381655) (by norm_num)
theorem B1019713 : Blo 904575 1019713 := bbase (se 2 (by rfl) ⟨382392, by rfl⟩ : syracuseStep 1019713 = 764785) (by norm_num)
theorem B1527653 : Blo 904575 1527653 := bbase (se 4 (by rfl) ⟨143217, by rfl⟩ : syracuseStep 1527653 = 286435) (by norm_num)
theorem B1019749 : Blo 904575 1019749 := bbase (se 4 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 1019749 = 191203) (by norm_num)
theorem B2035565 : Blo 904575 2035565 := bbase (se 3 (by rfl) ⟨381668, by rfl⟩ : syracuseStep 2035565 = 763337) (by norm_num)
theorem B1019785 : Blo 904575 1019785 := bbase (se 2 (by rfl) ⟨382419, by rfl⟩ : syracuseStep 1019785 = 764839) (by norm_num)
theorem B1290125 : Blo 904575 1290125 := bbase (se 3 (by rfl) ⟨241898, by rfl⟩ : syracuseStep 1290125 = 483797) (by norm_num)
theorem B1019821 : Blo 904575 1019821 := bbase (se 3 (by rfl) ⟨191216, by rfl⟩ : syracuseStep 1019821 = 382433) (by norm_num)
theorem B2035637 : Blo 904575 2035637 := bbase (se 5 (by rfl) ⟨95420, by rfl⟩ : syracuseStep 2035637 = 190841) (by norm_num)
theorem B1019857 : Blo 904575 1019857 := bbase (se 2 (by rfl) ⟨382446, by rfl⟩ : syracuseStep 1019857 = 764893) (by norm_num)
theorem B1290205 : Blo 904575 1290205 := bbase (se 3 (by rfl) ⟨241913, by rfl⟩ : syracuseStep 1290205 = 483827) (by norm_num)
theorem B1527781 : Blo 904575 1527781 := bbase (se 4 (by rfl) ⟨143229, by rfl⟩ : syracuseStep 1527781 = 286459) (by norm_num)
theorem B1019893 : Blo 904575 1019893 := bbase (se 5 (by rfl) ⟨47807, by rfl⟩ : syracuseStep 1019893 = 95615) (by norm_num)
theorem B2035709 : Blo 904575 2035709 := bbase (se 3 (by rfl) ⟨381695, by rfl⟩ : syracuseStep 2035709 = 763391) (by norm_num)
theorem B1527869 : Blo 904575 1527869 := bbase (se 3 (by rfl) ⟨286475, by rfl⟩ : syracuseStep 1527869 = 572951) (by norm_num)
theorem B2035781 : Blo 904575 2035781 := bbase (se 4 (by rfl) ⟨190854, by rfl⟩ : syracuseStep 2035781 = 381709) (by norm_num)
theorem B3436613 : Blo 904575 3436613 := bbase (se 4 (by rfl) ⟨322182, by rfl⟩ : syracuseStep 3436613 = 644365) (by norm_num)
theorem B1290325 : Blo 904575 1290325 := bbase (se 8 (by rfl) ⟨7560, by rfl⟩ : syracuseStep 1290325 = 15121) (by norm_num)
theorem B2035853 : Blo 904575 2035853 := bbase (se 3 (by rfl) ⟨381722, by rfl⟩ : syracuseStep 2035853 = 763445) (by norm_num)
theorem B2289829 : Blo 904575 2289829 := bbase (se 4 (by rfl) ⟨214671, by rfl⟩ : syracuseStep 2289829 = 429343) (by norm_num)
theorem B2576549 : Blo 904575 2576549 := bbase (se 4 (by rfl) ⟨241551, by rfl⟩ : syracuseStep 2576549 = 483103) (by norm_num)
theorem B4894901 : Blo 904575 4894901 := bbase (se 5 (by rfl) ⟨229448, by rfl⟩ : syracuseStep 4894901 = 458897) (by norm_num)
theorem B1290421 : Blo 904575 1290421 := bbase (se 5 (by rfl) ⟨60488, by rfl⟩ : syracuseStep 1290421 = 120977) (by norm_num)
theorem B1675453 : Blo 904575 1675453 := bbase (se 3 (by rfl) ⟨314147, by rfl⟩ : syracuseStep 1675453 = 628295) (by norm_num)
theorem B1527997 : Blo 904575 1527997 := bbase (se 3 (by rfl) ⟨286499, by rfl⟩ : syracuseStep 1527997 = 572999) (by norm_num)
theorem B2035925 : Blo 904575 2035925 := bbase (se 7 (by rfl) ⟨23858, by rfl⟩ : syracuseStep 2035925 = 47717) (by norm_num)
theorem B2289941 : Blo 904575 2289941 := bbase (se 6 (by rfl) ⟨53670, by rfl⟩ : syracuseStep 2289941 = 107341) (by norm_num)
theorem B1528085 : Blo 904575 1528085 := bbase (se 6 (by rfl) ⟨35814, by rfl⟩ : syracuseStep 1528085 = 71629) (by norm_num)
theorem B2035997 : Blo 904575 2035997 := bbase (se 3 (by rfl) ⟨381749, by rfl⟩ : syracuseStep 2035997 = 763499) (by norm_num)
theorem B2036069 : Blo 904575 2036069 := bbase (se 4 (by rfl) ⟨190881, by rfl⟩ : syracuseStep 2036069 = 381763) (by norm_num)
theorem B3436901 : Blo 904575 3436901 := bbase (se 4 (by rfl) ⟨322209, by rfl⟩ : syracuseStep 3436901 = 644419) (by norm_num)
theorem B1528213 : Blo 904575 1528213 := bbase (se 6 (by rfl) ⟨35817, by rfl⟩ : syracuseStep 1528213 = 71635) (by norm_num)
theorem B2036141 : Blo 904575 2036141 := bbase (se 3 (by rfl) ⟨381776, by rfl⟩ : syracuseStep 2036141 = 763553) (by norm_num)
theorem B2290133 : Blo 904575 2290133 := bbase (se 7 (by rfl) ⟨26837, by rfl⟩ : syracuseStep 2290133 = 53675) (by norm_num)
theorem B1528301 : Blo 904575 1528301 := bbase (se 3 (by rfl) ⟨286556, by rfl⟩ : syracuseStep 1528301 = 573113) (by norm_num)
theorem B2036213 : Blo 904575 2036213 := bbase (se 5 (by rfl) ⟨95447, by rfl⟩ : syracuseStep 2036213 = 190895) (by norm_num)
theorem B2036285 : Blo 904575 2036285 := bbase (se 3 (by rfl) ⟨381803, by rfl⟩ : syracuseStep 2036285 = 763607) (by norm_num)
theorem B2445893 : Blo 904575 2445893 := bbase (se 4 (by rfl) ⟨229302, by rfl⟩ : syracuseStep 2445893 = 458605) (by norm_num)
theorem B1528429 : Blo 904575 1528429 := bbase (se 3 (by rfl) ⟨286580, by rfl⟩ : syracuseStep 1528429 = 573161) (by norm_num)
theorem B2036357 : Blo 904575 2036357 := bbase (se 4 (by rfl) ⟨190908, by rfl⟩ : syracuseStep 2036357 = 381817) (by norm_num)
theorem B1766021 : Blo 904575 1766021 := bbase (se 4 (by rfl) ⟨165564, by rfl⟩ : syracuseStep 1766021 = 331129) (by norm_num)
theorem B5804693 : Blo 904575 5804693 := bbase (se 6 (by rfl) ⟨136047, by rfl⟩ : syracuseStep 5804693 = 272095) (by norm_num)
theorem B1528517 : Blo 904575 1528517 := bbase (se 4 (by rfl) ⟨143298, by rfl⟩ : syracuseStep 1528517 = 286597) (by norm_num)
theorem B2036429 : Blo 904575 2036429 := bbase (se 3 (by rfl) ⟨381830, by rfl⟩ : syracuseStep 2036429 = 763661) (by norm_num)
theorem B1676045 : Blo 904575 1676045 := bbase (se 3 (by rfl) ⟨314258, by rfl⟩ : syracuseStep 1676045 = 628517) (by norm_num)
theorem B2036501 : Blo 904575 2036501 := bbase (se 6 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 2036501 = 95461) (by norm_num)
theorem B7344917 : Blo 904575 7344917 := bbase (se 6 (by rfl) ⟨172146, by rfl⟩ : syracuseStep 7344917 = 344293) (by norm_num)
theorem B2290477 : Blo 904575 2290477 := bbase (se 3 (by rfl) ⟨429464, by rfl⟩ : syracuseStep 2290477 = 858929) (by norm_num)
theorem B2577221 : Blo 904575 2577221 := bbase (se 4 (by rfl) ⟨241614, by rfl⟩ : syracuseStep 2577221 = 483229) (by norm_num)
theorem B1528645 : Blo 904575 1528645 := bbase (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) (by norm_num)
theorem B2036573 : Blo 904575 2036573 := bbase (se 3 (by rfl) ⟨381857, by rfl⟩ : syracuseStep 2036573 = 763715) (by norm_num)
theorem B2290589 : Blo 904575 2290589 := bbase (se 3 (by rfl) ⟨429485, by rfl⟩ : syracuseStep 2290589 = 858971) (by norm_num)
theorem B1528733 : Blo 904575 1528733 := bbase (se 3 (by rfl) ⟨286637, by rfl⟩ : syracuseStep 1528733 = 573275) (by norm_num)
theorem B2036645 : Blo 904575 2036645 := bbase (se 4 (by rfl) ⟨190935, by rfl⟩ : syracuseStep 2036645 = 381871) (by norm_num)
theorem B5510069 : Blo 904575 5510069 := bbase (se 5 (by rfl) ⟨258284, by rfl⟩ : syracuseStep 5510069 = 516569) (by norm_num)
theorem B2036717 : Blo 904575 2036717 := bbase (se 3 (by rfl) ⟨381884, by rfl⟩ : syracuseStep 2036717 = 763769) (by norm_num)
theorem B4584437 : Blo 904575 4584437 := bbase (se 5 (by rfl) ⟨214895, by rfl⟩ : syracuseStep 4584437 = 429791) (by norm_num)
theorem B1528861 : Blo 904575 1528861 := bbase (se 3 (by rfl) ⟨286661, by rfl⟩ : syracuseStep 1528861 = 573323) (by norm_num)
theorem B2036789 : Blo 904575 2036789 := bbase (se 5 (by rfl) ⟨95474, by rfl⟩ : syracuseStep 2036789 = 190949) (by norm_num)
theorem B1356869 : Blo 904575 1356869 := bbase (se 4 (by rfl) ⟨127206, by rfl⟩ : syracuseStep 1356869 = 254413) (by norm_num)
theorem B1356893 : Blo 904575 1356893 := bbase (se 3 (by rfl) ⟨254417, by rfl⟩ : syracuseStep 1356893 = 508835) (by norm_num)
theorem B2290781 : Blo 904575 2290781 := bbase (se 3 (by rfl) ⟨429521, by rfl⟩ : syracuseStep 2290781 = 859043) (by norm_num)
theorem B1717357 : Blo 904575 1717357 := bbase (se 3 (by rfl) ⟨322004, by rfl⟩ : syracuseStep 1717357 = 644009) (by norm_num)
theorem B1356917 : Blo 904575 1356917 := bbase (se 5 (by rfl) ⟨63605, by rfl⟩ : syracuseStep 1356917 = 127211) (by norm_num)
theorem B2937973 : Blo 904575 2937973 := bbase (se 5 (by rfl) ⟨137717, by rfl⟩ : syracuseStep 2937973 = 275435) (by norm_num)
theorem B1528949 : Blo 904575 1528949 := bbase (se 5 (by rfl) ⟨71669, by rfl⟩ : syracuseStep 1528949 = 143339) (by norm_num)
theorem B2036861 : Blo 904575 2036861 := bbase (se 3 (by rfl) ⟨381911, by rfl⟩ : syracuseStep 2036861 = 763823) (by norm_num)
theorem B1356941 : Blo 904575 1356941 := bbase (se 3 (by rfl) ⟨254426, by rfl⟩ : syracuseStep 1356941 = 508853) (by norm_num)
theorem B6878357 : Blo 904575 6878357 := bbase (se 6 (by rfl) ⟨161211, by rfl⟩ : syracuseStep 6878357 = 322423) (by norm_num)
theorem B1356965 : Blo 904575 1356965 := bbase (se 4 (by rfl) ⟨127215, by rfl⟩ : syracuseStep 1356965 = 254431) (by norm_num)
theorem B1356989 : Blo 904575 1356989 := bbase (se 3 (by rfl) ⟨254435, by rfl⟩ : syracuseStep 1356989 = 508871) (by norm_num)
theorem B2036933 : Blo 904575 2036933 := bbase (se 4 (by rfl) ⟨190962, by rfl⟩ : syracuseStep 2036933 = 381925) (by norm_num)
theorem B1357013 : Blo 904575 1357013 := bbase (se 7 (by rfl) ⟨15902, by rfl⟩ : syracuseStep 1357013 = 31805) (by norm_num)
theorem B1357037 : Blo 904575 1357037 := bbase (se 3 (by rfl) ⟨254444, by rfl⟩ : syracuseStep 1357037 = 508889) (by norm_num)
theorem B2577653 : Blo 904575 2577653 := bbase (se 5 (by rfl) ⟨120827, by rfl⟩ : syracuseStep 2577653 = 241655) (by norm_num)
theorem B1529077 : Blo 904575 1529077 := bbase (se 5 (by rfl) ⟨71675, by rfl⟩ : syracuseStep 1529077 = 143351) (by norm_num)
theorem B1357061 : Blo 904575 1357061 := bbase (se 4 (by rfl) ⟨127224, by rfl⟩ : syracuseStep 1357061 = 254449) (by norm_num)
theorem B1717517 : Blo 904575 1717517 := bbase (se 3 (by rfl) ⟨322034, by rfl⟩ : syracuseStep 1717517 = 644069) (by norm_num)
theorem B2037005 : Blo 904575 2037005 := bbase (se 3 (by rfl) ⟨381938, by rfl⟩ : syracuseStep 2037005 = 763877) (by norm_num)
theorem B1766677 : Blo 904575 1766677 := bbase (se 6 (by rfl) ⟨41406, by rfl⟩ : syracuseStep 1766677 = 82813) (by norm_num)
theorem B1357085 : Blo 904575 1357085 := bbase (se 3 (by rfl) ⟨254453, by rfl⟩ : syracuseStep 1357085 = 508907) (by norm_num)
theorem B4355365 : Blo 904575 4355365 := bbase (se 4 (by rfl) ⟨408315, by rfl⟩ : syracuseStep 4355365 = 816631) (by norm_num)
theorem B1357109 : Blo 904575 1357109 := bbase (se 5 (by rfl) ⟨63614, by rfl⟩ : syracuseStep 1357109 = 127229) (by norm_num)
theorem B3872069 : Blo 904575 3872069 := bbase (se 4 (by rfl) ⟨363006, by rfl⟩ : syracuseStep 3872069 = 726013) (by norm_num)
theorem B1357133 : Blo 904575 1357133 := bbase (se 3 (by rfl) ⟨254462, by rfl⟩ : syracuseStep 1357133 = 508925) (by norm_num)
theorem B1529165 : Blo 904575 1529165 := bbase (se 3 (by rfl) ⟨286718, by rfl⟩ : syracuseStep 1529165 = 573437) (by norm_num)
theorem B2037077 : Blo 904575 2037077 := bbase (se 14 (by rfl) ⟨186, by rfl⟩ : syracuseStep 2037077 = 373) (by norm_num)
theorem B1357157 : Blo 904575 1357157 := bbase (se 4 (by rfl) ⟨127233, by rfl⟩ : syracuseStep 1357157 = 254467) (by norm_num)
theorem B1357181 : Blo 904575 1357181 := bbase (se 3 (by rfl) ⟨254471, by rfl⟩ : syracuseStep 1357181 = 508943) (by norm_num)
theorem B1357205 : Blo 904575 1357205 := bbase (se 6 (by rfl) ⟨31809, by rfl⟩ : syracuseStep 1357205 = 63619) (by norm_num)
theorem B1717661 : Blo 904575 1717661 := bbase (se 3 (by rfl) ⟨322061, by rfl⟩ : syracuseStep 1717661 = 644123) (by norm_num)
theorem B2037149 : Blo 904575 2037149 := bbase (se 3 (by rfl) ⟨381965, by rfl⟩ : syracuseStep 2037149 = 763931) (by norm_num)
theorem B1357229 : Blo 904575 1357229 := bbase (se 3 (by rfl) ⟨254480, by rfl⟩ : syracuseStep 1357229 = 508961) (by norm_num)
theorem B2291125 : Blo 904575 2291125 := bbase (se 5 (by rfl) ⟨107396, by rfl⟩ : syracuseStep 2291125 = 214793) (by norm_num)
theorem B1086905 : Blo 904575 1086905 := bbase (se 2 (by rfl) ⟨407589, by rfl⟩ : syracuseStep 1086905 = 815179) (by norm_num)
theorem B3052997 : Blo 904575 3052997 := bbase (se 4 (by rfl) ⟨286218, by rfl⟩ : syracuseStep 3052997 = 572437) (by norm_num)
theorem B1357253 : Blo 904575 1357253 := bbase (se 4 (by rfl) ⟨127242, by rfl⟩ : syracuseStep 1357253 = 254485) (by norm_num)
theorem B1529293 : Blo 904575 1529293 := bbase (se 3 (by rfl) ⟨286742, by rfl⟩ : syracuseStep 1529293 = 573485) (by norm_num)
theorem B1357277 : Blo 904575 1357277 := bbase (se 3 (by rfl) ⟨254489, by rfl⟩ : syracuseStep 1357277 = 508979) (by norm_num)
theorem B2037221 : Blo 904575 2037221 := bbase (se 4 (by rfl) ⟨190989, by rfl⟩ : syracuseStep 2037221 = 381979) (by norm_num)
theorem B1357301 : Blo 904575 1357301 := bbase (se 5 (by rfl) ⟨63623, by rfl⟩ : syracuseStep 1357301 = 127247) (by norm_num)
theorem B3438085 : Blo 904575 3438085 := bbase (se 4 (by rfl) ⟨322320, by rfl⟩ : syracuseStep 3438085 = 644641) (by norm_num)
theorem B1357325 : Blo 904575 1357325 := bbase (se 3 (by rfl) ⟨254498, by rfl⟩ : syracuseStep 1357325 = 508997) (by norm_num)
theorem B1357349 : Blo 904575 1357349 := bbase (se 4 (by rfl) ⟨127251, by rfl⟩ : syracuseStep 1357349 = 254503) (by norm_num)
theorem B2291237 : Blo 904575 2291237 := bbase (se 4 (by rfl) ⟨214803, by rfl⟩ : syracuseStep 2291237 = 429607) (by norm_num)
theorem B1529381 : Blo 904575 1529381 := bbase (se 4 (by rfl) ⟨143379, by rfl⟩ : syracuseStep 1529381 = 286759) (by norm_num)
theorem B2037293 : Blo 904575 2037293 := bbase (se 3 (by rfl) ⟨381992, by rfl⟩ : syracuseStep 2037293 = 763985) (by norm_num)
theorem B6870581 : Blo 904575 6870581 := bbase (se 5 (by rfl) ⟨322058, by rfl⟩ : syracuseStep 6870581 = 644117) (by norm_num)
theorem B931385 : Blo 904575 931385 := bbase (se 2 (by rfl) ⟨349269, by rfl⟩ : syracuseStep 931385 = 698539) (by norm_num)
theorem B1357373 : Blo 904575 1357373 := bbase (se 3 (by rfl) ⟨254507, by rfl⟩ : syracuseStep 1357373 = 509015) (by norm_num)
theorem B4126277 : Blo 904575 4126277 := bbase (se 4 (by rfl) ⟨386838, by rfl⟩ : syracuseStep 4126277 = 773677) (by norm_num)
theorem B1742405 : Blo 904575 1742405 := bbase (se 4 (by rfl) ⟨163350, by rfl⟩ : syracuseStep 1742405 = 326701) (by norm_num)
theorem B1357397 : Blo 904575 1357397 := bbase (se 8 (by rfl) ⟨7953, by rfl⟩ : syracuseStep 1357397 = 15907) (by norm_num)
theorem B11605589 : Blo 904575 11605589 := bbase (se 8 (by rfl) ⟨68001, by rfl⟩ : syracuseStep 11605589 = 136003) (by norm_num)
theorem B1742429 : Blo 904575 1742429 := bbase (se 3 (by rfl) ⟨326705, by rfl⟩ : syracuseStep 1742429 = 653411) (by norm_num)
theorem B3872357 : Blo 904575 3872357 := bbase (se 4 (by rfl) ⟨363033, by rfl⟩ : syracuseStep 3872357 = 726067) (by norm_num)
theorem B1357421 : Blo 904575 1357421 := bbase (se 3 (by rfl) ⟨254516, by rfl⟩ : syracuseStep 1357421 = 509033) (by norm_num)
theorem B2037365 : Blo 904575 2037365 := bbase (se 5 (by rfl) ⟨95501, by rfl⟩ : syracuseStep 2037365 = 191003) (by norm_num)
theorem B1357445 : Blo 904575 1357445 := bbase (se 4 (by rfl) ⟨127260, by rfl⟩ : syracuseStep 1357445 = 254521) (by norm_num)
theorem B1357469 : Blo 904575 1357469 := bbase (se 3 (by rfl) ⟨254525, by rfl⟩ : syracuseStep 1357469 = 509051) (by norm_num)
theorem B2479781 : Blo 904575 2479781 := bbase (se 4 (by rfl) ⟨232479, by rfl⟩ : syracuseStep 2479781 = 464959) (by norm_num)
theorem B1529509 : Blo 904575 1529509 := bbase (se 4 (by rfl) ⟨143391, by rfl⟩ : syracuseStep 1529509 = 286783) (by norm_num)
theorem B1357493 : Blo 904575 1357493 := bbase (se 5 (by rfl) ⟨63632, by rfl⟩ : syracuseStep 1357493 = 127265) (by norm_num)
theorem B1717949 : Blo 904575 1717949 := bbase (se 3 (by rfl) ⟨322115, by rfl⟩ : syracuseStep 1717949 = 644231) (by norm_num)
theorem B2037437 : Blo 904575 2037437 := bbase (se 3 (by rfl) ⟨382019, by rfl⟩ : syracuseStep 2037437 = 764039) (by norm_num)
theorem B1357517 : Blo 904575 1357517 := bbase (se 3 (by rfl) ⟨254534, by rfl⟩ : syracuseStep 1357517 = 509069) (by norm_num)
theorem B4126421 : Blo 904575 4126421 := bbase (se 7 (by rfl) ⟨48356, by rfl⟩ : syracuseStep 4126421 = 96713) (by norm_num)
theorem B3864293 : Blo 904575 3864293 := bbase (se 4 (by rfl) ⟨362277, by rfl⟩ : syracuseStep 3864293 = 724555) (by norm_num)
theorem B1357541 : Blo 904575 1357541 := bbase (se 4 (by rfl) ⟨127269, by rfl⟩ : syracuseStep 1357541 = 254539) (by norm_num)
theorem B2291429 : Blo 904575 2291429 := bbase (se 4 (by rfl) ⟨214821, by rfl⟩ : syracuseStep 2291429 = 429643) (by norm_num)
theorem B1357565 : Blo 904575 1357565 := bbase (se 3 (by rfl) ⟨254543, by rfl⟩ : syracuseStep 1357565 = 509087) (by norm_num)
theorem B1529597 : Blo 904575 1529597 := bbase (se 3 (by rfl) ⟨286799, by rfl⟩ : syracuseStep 1529597 = 573599) (by norm_num)
theorem B2037509 : Blo 904575 2037509 := bbase (se 4 (by rfl) ⟨191016, by rfl⟩ : syracuseStep 2037509 = 382033) (by norm_num)
theorem B1357589 : Blo 904575 1357589 := bbase (se 6 (by rfl) ⟨31818, by rfl⟩ : syracuseStep 1357589 = 63637) (by norm_num)
theorem B1357613 : Blo 904575 1357613 := bbase (se 3 (by rfl) ⟨254552, by rfl⟩ : syracuseStep 1357613 = 509105) (by norm_num)
theorem B3438389 : Blo 904575 3438389 := bbase (se 5 (by rfl) ⟨161174, by rfl⟩ : syracuseStep 3438389 = 322349) (by norm_num)
theorem B3143477 : Blo 904575 3143477 := bbase (se 5 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 3143477 = 294701) (by norm_num)
theorem B1357637 : Blo 904575 1357637 := bbase (se 4 (by rfl) ⟨127278, by rfl⟩ : syracuseStep 1357637 = 254557) (by norm_num)
theorem B2037581 : Blo 904575 2037581 := bbase (se 3 (by rfl) ⟨382046, by rfl⟩ : syracuseStep 2037581 = 764093) (by norm_num)
theorem B1718101 : Blo 904575 1718101 := bbase (se 9 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 1718101 = 10067) (by norm_num)
theorem B1357661 : Blo 904575 1357661 := bbase (se 3 (by rfl) ⟨254561, by rfl⟩ : syracuseStep 1357661 = 509123) (by norm_num)
theorem B3053429 : Blo 904575 3053429 := bbase (se 5 (by rfl) ⟨143129, by rfl⟩ : syracuseStep 3053429 = 286259) (by norm_num)
theorem B1357685 : Blo 904575 1357685 := bbase (se 5 (by rfl) ⟨63641, by rfl⟩ : syracuseStep 1357685 = 127283) (by norm_num)
theorem B2176885 : Blo 904575 2176885 := bbase (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) (by norm_num)
theorem B1529725 : Blo 904575 1529725 := bbase (se 3 (by rfl) ⟨286823, by rfl⟩ : syracuseStep 1529725 = 573647) (by norm_num)
theorem B1357709 : Blo 904575 1357709 := bbase (se 3 (by rfl) ⟨254570, by rfl⟩ : syracuseStep 1357709 = 509141) (by norm_num)
theorem B1087381 : Blo 904575 1087381 := bbase (se 6 (by rfl) ⟨25485, by rfl⟩ : syracuseStep 1087381 = 50971) (by norm_num)
theorem B2037653 : Blo 904575 2037653 := bbase (se 6 (by rfl) ⟨47757, by rfl⟩ : syracuseStep 2037653 = 95515) (by norm_num)
theorem B1357733 : Blo 904575 1357733 := bbase (se 4 (by rfl) ⟨127287, by rfl⟩ : syracuseStep 1357733 = 254575) (by norm_num)
theorem B1087409 : Blo 904575 1087409 := bbase (se 2 (by rfl) ⟨407778, by rfl⟩ : syracuseStep 1087409 = 815557) (by norm_num)
theorem B1357757 : Blo 904575 1357757 := bbase (se 3 (by rfl) ⟨254579, by rfl⟩ : syracuseStep 1357757 = 509159) (by norm_num)
theorem B1357781 : Blo 904575 1357781 := bbase (se 7 (by rfl) ⟨15911, by rfl⟩ : syracuseStep 1357781 = 31823) (by norm_num)
theorem B1529813 : Blo 904575 1529813 := bbase (se 7 (by rfl) ⟨17927, by rfl⟩ : syracuseStep 1529813 = 35855) (by norm_num)
theorem B2037725 : Blo 904575 2037725 := bbase (se 3 (by rfl) ⟨382073, by rfl⟩ : syracuseStep 2037725 = 764147) (by norm_num)
theorem B2578405 : Blo 904575 2578405 := bbase (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) (by norm_num)
theorem B1357805 : Blo 904575 1357805 := bbase (se 3 (by rfl) ⟨254588, by rfl⟩ : syracuseStep 1357805 = 509177) (by norm_num)
theorem B8706037 : Blo 904575 8706037 := bbase (se 5 (by rfl) ⟨408095, by rfl⟩ : syracuseStep 8706037 = 816191) (by norm_num)
theorem B1357829 : Blo 904575 1357829 := bbase (se 4 (by rfl) ⟨127296, by rfl⟩ : syracuseStep 1357829 = 254593) (by norm_num)
theorem B1357853 : Blo 904575 1357853 := bbase (se 3 (by rfl) ⟨254597, by rfl⟩ : syracuseStep 1357853 = 509195) (by norm_num)
theorem B2037797 : Blo 904575 2037797 := bbase (se 4 (by rfl) ⟨191043, by rfl⟩ : syracuseStep 2037797 = 382087) (by norm_num)
theorem B1357877 : Blo 904575 1357877 := bbase (se 5 (by rfl) ⟨63650, by rfl⟩ : syracuseStep 1357877 = 127301) (by norm_num)
theorem B2291773 : Blo 904575 2291773 := bbase (se 3 (by rfl) ⟨429707, by rfl⟩ : syracuseStep 2291773 = 859415) (by norm_num)
theorem B1357901 : Blo 904575 1357901 := bbase (se 3 (by rfl) ⟨254606, by rfl⟩ : syracuseStep 1357901 = 509213) (by norm_num)
theorem B5158997 : Blo 904575 5158997 := bbase (se 8 (by rfl) ⟨30228, by rfl⟩ : syracuseStep 5158997 = 60457) (by norm_num)
theorem B1357925 : Blo 904575 1357925 := bbase (se 4 (by rfl) ⟨127305, by rfl⟩ : syracuseStep 1357925 = 254611) (by norm_num)
theorem B1087597 : Blo 904575 1087597 := bbase (se 3 (by rfl) ⟨203924, by rfl⟩ : syracuseStep 1087597 = 407849) (by norm_num)
theorem B2037869 : Blo 904575 2037869 := bbase (se 3 (by rfl) ⟨382100, by rfl⟩ : syracuseStep 2037869 = 764201) (by norm_num)
theorem B1144945 : Blo 904575 1144945 := bbase (se 2 (by rfl) ⟨429354, by rfl⟩ : syracuseStep 1144945 = 858709) (by norm_num)
theorem B1357949 : Blo 904575 1357949 := bbase (se 3 (by rfl) ⟨254615, by rfl⟩ : syracuseStep 1357949 = 509231) (by norm_num)
theorem B1718405 : Blo 904575 1718405 := bbase (se 4 (by rfl) ⟨161100, by rfl⟩ : syracuseStep 1718405 = 322201) (by norm_num)
theorem B1357973 : Blo 904575 1357973 := bbase (se 6 (by rfl) ⟨31827, by rfl⟩ : syracuseStep 1357973 = 63655) (by norm_num)
theorem B3266725 : Blo 904575 3266725 := bbase (se 4 (by rfl) ⟨306255, by rfl⟩ : syracuseStep 3266725 = 612511) (by norm_num)
theorem B1357997 : Blo 904575 1357997 := bbase (se 3 (by rfl) ⟨254624, by rfl⟩ : syracuseStep 1357997 = 509249) (by norm_num)
theorem B2291885 : Blo 904575 2291885 := bbase (se 3 (by rfl) ⟨429728, by rfl⟩ : syracuseStep 2291885 = 859457) (by norm_num)
theorem B2037941 : Blo 904575 2037941 := bbase (se 5 (by rfl) ⟨95528, by rfl⟩ : syracuseStep 2037941 = 191057) (by norm_num)
theorem B1358021 : Blo 904575 1358021 := bbase (se 4 (by rfl) ⟨127314, by rfl⟩ : syracuseStep 1358021 = 254629) (by norm_num)
theorem B1358045 : Blo 904575 1358045 := bbase (se 3 (by rfl) ⟨254633, by rfl⟩ : syracuseStep 1358045 = 509267) (by norm_num)
theorem B1087717 : Blo 904575 1087717 := bbase (se 4 (by rfl) ⟨101973, by rfl⟩ : syracuseStep 1087717 = 203947) (by norm_num)
theorem B1358069 : Blo 904575 1358069 := bbase (se 5 (by rfl) ⟨63659, by rfl⟩ : syracuseStep 1358069 = 127319) (by norm_num)
theorem B9296117 : Blo 904575 9296117 := bbase (se 5 (by rfl) ⟨435755, by rfl⟩ : syracuseStep 9296117 = 871511) (by norm_num)
theorem B2038013 : Blo 904575 2038013 := bbase (se 3 (by rfl) ⟨382127, by rfl⟩ : syracuseStep 2038013 = 764255) (by norm_num)
theorem B4585733 : Blo 904575 4585733 := bbase (se 4 (by rfl) ⟨429912, by rfl⟩ : syracuseStep 4585733 = 859825) (by norm_num)
theorem B1358093 : Blo 904575 1358093 := bbase (se 3 (by rfl) ⟨254642, by rfl⟩ : syracuseStep 1358093 = 509285) (by norm_num)
theorem B1145117 : Blo 904575 1145117 := bbase (se 3 (by rfl) ⟨214709, by rfl⟩ : syracuseStep 1145117 = 429419) (by norm_num)
theorem B3053861 : Blo 904575 3053861 := bbase (se 4 (by rfl) ⟨286299, by rfl⟩ : syracuseStep 3053861 = 572599) (by norm_num)
theorem B1358117 : Blo 904575 1358117 := bbase (se 4 (by rfl) ⟨127323, by rfl⟩ : syracuseStep 1358117 = 254647) (by norm_num)
theorem B1358141 : Blo 904575 1358141 := bbase (se 3 (by rfl) ⟨254651, by rfl⟩ : syracuseStep 1358141 = 509303) (by norm_num)
theorem B2038085 : Blo 904575 2038085 := bbase (se 4 (by rfl) ⟨191070, by rfl⟩ : syracuseStep 2038085 = 382141) (by norm_num)
theorem B1145173 : Blo 904575 1145173 := bbase (se 10 (by rfl) ⟨1677, by rfl⟩ : syracuseStep 1145173 = 3355) (by norm_num)
theorem B1358165 : Blo 904575 1358165 := bbase (se 10 (by rfl) ⟨1989, by rfl⟩ : syracuseStep 1358165 = 3979) (by norm_num)
theorem B1358189 : Blo 904575 1358189 := bbase (se 3 (by rfl) ⟨254660, by rfl⟩ : syracuseStep 1358189 = 509321) (by norm_num)
theorem B2292077 : Blo 904575 2292077 := bbase (se 3 (by rfl) ⟨429764, by rfl⟩ : syracuseStep 2292077 = 859529) (by norm_num)
theorem B1743229 : Blo 904575 1743229 := bbase (se 3 (by rfl) ⟨326855, by rfl⟩ : syracuseStep 1743229 = 653711) (by norm_num)
theorem B1358213 : Blo 904575 1358213 := bbase (se 4 (by rfl) ⟨127332, by rfl⟩ : syracuseStep 1358213 = 254665) (by norm_num)
theorem B2038157 : Blo 904575 2038157 := bbase (se 3 (by rfl) ⟨382154, by rfl⟩ : syracuseStep 2038157 = 764309) (by norm_num)
theorem B1358237 : Blo 904575 1358237 := bbase (se 3 (by rfl) ⟨254669, by rfl⟩ : syracuseStep 1358237 = 509339) (by norm_num)
theorem B1145269 : Blo 904575 1145269 := bbase (se 5 (by rfl) ⟨53684, by rfl⟩ : syracuseStep 1145269 = 107369) (by norm_num)
theorem B1358261 : Blo 904575 1358261 := bbase (se 5 (by rfl) ⟨63668, by rfl⟩ : syracuseStep 1358261 = 127337) (by norm_num)
theorem B1358285 : Blo 904575 1358285 := bbase (se 3 (by rfl) ⟨254678, by rfl⟩ : syracuseStep 1358285 = 509357) (by norm_num)
theorem B2038229 : Blo 904575 2038229 := bbase (se 7 (by rfl) ⟨23885, by rfl⟩ : syracuseStep 2038229 = 47771) (by norm_num)
theorem B1358309 : Blo 904575 1358309 := bbase (se 4 (by rfl) ⟨127341, by rfl⟩ : syracuseStep 1358309 = 254683) (by norm_num)
theorem B1358333 : Blo 904575 1358333 := bbase (se 3 (by rfl) ⟨254687, by rfl⟩ : syracuseStep 1358333 = 509375) (by norm_num)
theorem B2177549 : Blo 904575 2177549 := bbase (se 3 (by rfl) ⟨408290, by rfl⟩ : syracuseStep 2177549 = 816581) (by norm_num)
theorem B1358357 : Blo 904575 1358357 := bbase (se 6 (by rfl) ⟨31836, by rfl⟩ : syracuseStep 1358357 = 63673) (by norm_num)
theorem B2038301 : Blo 904575 2038301 := bbase (se 3 (by rfl) ⟨382181, by rfl⟩ : syracuseStep 2038301 = 764363) (by norm_num)
theorem B1358381 : Blo 904575 1358381 := bbase (se 3 (by rfl) ⟨254696, by rfl⟩ : syracuseStep 1358381 = 509393) (by norm_num)
theorem B1358405 : Blo 904575 1358405 := bbase (se 4 (by rfl) ⟨127350, by rfl⟩ : syracuseStep 1358405 = 254701) (by norm_num)
theorem B1358429 : Blo 904575 1358429 := bbase (se 3 (by rfl) ⟨254705, by rfl⟩ : syracuseStep 1358429 = 509411) (by norm_num)
theorem B1145441 : Blo 904575 1145441 := bbase (se 2 (by rfl) ⟨429540, by rfl⟩ : syracuseStep 1145441 = 859081) (by norm_num)
theorem B1161829 : Blo 904575 1161829 := bbase (se 4 (by rfl) ⟨108921, by rfl⟩ : syracuseStep 1161829 = 217843) (by norm_num)
theorem B2038373 : Blo 904575 2038373 := bbase (se 4 (by rfl) ⟨191097, by rfl⟩ : syracuseStep 2038373 = 382195) (by norm_num)
theorem B3267173 : Blo 904575 3267173 := bbase (se 4 (by rfl) ⟨306297, by rfl⟩ : syracuseStep 3267173 = 612595) (by norm_num)
theorem B1358453 : Blo 904575 1358453 := bbase (se 5 (by rfl) ⟨63677, by rfl⟩ : syracuseStep 1358453 = 127355) (by norm_num)
theorem B1358477 : Blo 904575 1358477 := bbase (se 3 (by rfl) ⟨254714, by rfl⟩ : syracuseStep 1358477 = 509429) (by norm_num)
theorem B1145497 : Blo 904575 1145497 := bbase (se 2 (by rfl) ⟨429561, by rfl⟩ : syracuseStep 1145497 = 859123) (by norm_num)
theorem B1931941 : Blo 904575 1931941 := bbase (se 4 (by rfl) ⟨181119, by rfl⟩ : syracuseStep 1931941 = 362239) (by norm_num)
theorem B1358501 : Blo 904575 1358501 := bbase (se 4 (by rfl) ⟨127359, by rfl⟩ : syracuseStep 1358501 = 254719) (by norm_num)
theorem B2038445 : Blo 904575 2038445 := bbase (se 3 (by rfl) ⟨382208, by rfl⟩ : syracuseStep 2038445 = 764417) (by norm_num)
theorem B1358525 : Blo 904575 1358525 := bbase (se 3 (by rfl) ⟨254723, by rfl⟩ : syracuseStep 1358525 = 509447) (by norm_num)
theorem B2292421 : Blo 904575 2292421 := bbase (se 4 (by rfl) ⟨214914, by rfl⟩ : syracuseStep 2292421 = 429829) (by norm_num)
theorem B3054293 : Blo 904575 3054293 := bbase (se 7 (by rfl) ⟨35792, by rfl⟩ : syracuseStep 3054293 = 71585) (by norm_num)
theorem B1358549 : Blo 904575 1358549 := bbase (se 7 (by rfl) ⟨15920, by rfl⟩ : syracuseStep 1358549 = 31841) (by norm_num)
theorem B4897493 : Blo 904575 4897493 := bbase (se 7 (by rfl) ⟨57392, by rfl⟩ : syracuseStep 4897493 = 114785) (by norm_num)
theorem B1358573 : Blo 904575 1358573 := bbase (se 3 (by rfl) ⟨254732, by rfl⟩ : syracuseStep 1358573 = 509465) (by norm_num)
theorem B2038517 : Blo 904575 2038517 := bbase (se 5 (by rfl) ⟨95555, by rfl⟩ : syracuseStep 2038517 = 191111) (by norm_num)
theorem B1145593 : Blo 904575 1145593 := bbase (se 2 (by rfl) ⟨429597, by rfl⟩ : syracuseStep 1145593 = 859195) (by norm_num)
theorem B1358597 : Blo 904575 1358597 := bbase (se 4 (by rfl) ⟨127368, by rfl⟩ : syracuseStep 1358597 = 254737) (by norm_num)
theorem B1358621 : Blo 904575 1358621 := bbase (se 3 (by rfl) ⟨254741, by rfl⟩ : syracuseStep 1358621 = 509483) (by norm_num)
theorem B2177837 : Blo 904575 2177837 := bbase (se 3 (by rfl) ⟨408344, by rfl⟩ : syracuseStep 2177837 = 816689) (by norm_num)
theorem B2292533 : Blo 904575 2292533 := bbase (se 5 (by rfl) ⟨107462, by rfl⟩ : syracuseStep 2292533 = 214925) (by norm_num)
theorem B1358645 : Blo 904575 1358645 := bbase (se 5 (by rfl) ⟨63686, by rfl⟩ : syracuseStep 1358645 = 127373) (by norm_num)
theorem B2038589 : Blo 904575 2038589 := bbase (se 3 (by rfl) ⟨382235, by rfl⟩ : syracuseStep 2038589 = 764471) (by norm_num)
theorem B1358669 : Blo 904575 1358669 := bbase (se 3 (by rfl) ⟨254750, by rfl⟩ : syracuseStep 1358669 = 509501) (by norm_num)
theorem B1358693 : Blo 904575 1358693 := bbase (se 4 (by rfl) ⟨127377, by rfl⟩ : syracuseStep 1358693 = 254755) (by norm_num)
theorem B1719157 : Blo 904575 1719157 := bbase (se 5 (by rfl) ⟨80585, by rfl⟩ : syracuseStep 1719157 = 161171) (by norm_num)
theorem B1358717 : Blo 904575 1358717 := bbase (se 3 (by rfl) ⟨254759, by rfl⟩ : syracuseStep 1358717 = 509519) (by norm_num)
theorem B2038661 : Blo 904575 2038661 := bbase (se 4 (by rfl) ⟨191124, by rfl⟩ : syracuseStep 2038661 = 382249) (by norm_num)
theorem B1358741 : Blo 904575 1358741 := bbase (se 6 (by rfl) ⟨31845, by rfl⟩ : syracuseStep 1358741 = 63691) (by norm_num)
theorem B1145765 : Blo 904575 1145765 := bbase (se 4 (by rfl) ⟨107415, by rfl⟩ : syracuseStep 1145765 = 214831) (by norm_num)
theorem B1358765 : Blo 904575 1358765 := bbase (se 3 (by rfl) ⟨254768, by rfl⟩ : syracuseStep 1358765 = 509537) (by norm_num)
theorem B7650229 : Blo 904575 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B1358789 : Blo 904575 1358789 := bbase (se 4 (by rfl) ⟨127386, by rfl⟩ : syracuseStep 1358789 = 254773) (by norm_num)
theorem B2038733 : Blo 904575 2038733 := bbase (se 3 (by rfl) ⟨382262, by rfl⟩ : syracuseStep 2038733 = 764525) (by norm_num)
theorem B1145821 : Blo 904575 1145821 := bbase (se 3 (by rfl) ⟨214841, by rfl⟩ : syracuseStep 1145821 = 429683) (by norm_num)
theorem B1358813 : Blo 904575 1358813 := bbase (se 3 (by rfl) ⟨254777, by rfl⟩ : syracuseStep 1358813 = 509555) (by norm_num)
theorem B2292725 : Blo 904575 2292725 := bbase (se 5 (by rfl) ⟨107471, by rfl⟩ : syracuseStep 2292725 = 214943) (by norm_num)
theorem B1358837 : Blo 904575 1358837 := bbase (se 5 (by rfl) ⟨63695, by rfl⟩ : syracuseStep 1358837 = 127391) (by norm_num)
theorem B1719301 : Blo 904575 1719301 := bbase (se 4 (by rfl) ⟨161184, by rfl⟩ : syracuseStep 1719301 = 322369) (by norm_num)
theorem B1358861 : Blo 904575 1358861 := bbase (se 3 (by rfl) ⟨254786, by rfl⟩ : syracuseStep 1358861 = 509573) (by norm_num)
theorem B2038805 : Blo 904575 2038805 := bbase (se 6 (by rfl) ⟨47784, by rfl⟩ : syracuseStep 2038805 = 95569) (by norm_num)
theorem B1358885 : Blo 904575 1358885 := bbase (se 4 (by rfl) ⟨127395, by rfl⟩ : syracuseStep 1358885 = 254791) (by norm_num)
theorem B1145917 : Blo 904575 1145917 := bbase (se 3 (by rfl) ⟨214859, by rfl⟩ : syracuseStep 1145917 = 429719) (by norm_num)
theorem B1358909 : Blo 904575 1358909 := bbase (se 3 (by rfl) ⟨254795, by rfl⟩ : syracuseStep 1358909 = 509591) (by norm_num)
theorem B1358933 : Blo 904575 1358933 := bbase (se 8 (by rfl) ⟨7962, by rfl⟩ : syracuseStep 1358933 = 15925) (by norm_num)
theorem B2038877 : Blo 904575 2038877 := bbase (se 3 (by rfl) ⟨382289, by rfl⟩ : syracuseStep 2038877 = 764579) (by norm_num)
theorem B1358957 : Blo 904575 1358957 := bbase (se 3 (by rfl) ⟨254804, by rfl⟩ : syracuseStep 1358957 = 509609) (by norm_num)
theorem B1449085 : Blo 904575 1449085 := bbase (se 3 (by rfl) ⟨271703, by rfl⟩ : syracuseStep 1449085 = 543407) (by norm_num)
theorem B3054725 : Blo 904575 3054725 := bbase (se 4 (by rfl) ⟨286380, by rfl⟩ : syracuseStep 3054725 = 572761) (by norm_num)
theorem B1358981 : Blo 904575 1358981 := bbase (se 4 (by rfl) ⟨127404, by rfl⟩ : syracuseStep 1358981 = 254809) (by norm_num)
theorem B1932437 : Blo 904575 1932437 := bbase (se 6 (by rfl) ⟨45291, by rfl⟩ : syracuseStep 1932437 = 90583) (by norm_num)
theorem B1359005 : Blo 904575 1359005 := bbase (se 3 (by rfl) ⟨254813, by rfl⟩ : syracuseStep 1359005 = 509627) (by norm_num)
theorem B1719461 : Blo 904575 1719461 := bbase (se 4 (by rfl) ⟨161199, by rfl⟩ : syracuseStep 1719461 = 322399) (by norm_num)
theorem B2038949 : Blo 904575 2038949 := bbase (se 4 (by rfl) ⟨191151, by rfl⟩ : syracuseStep 2038949 = 382303) (by norm_num)
theorem B1359029 : Blo 904575 1359029 := bbase (se 5 (by rfl) ⟨63704, by rfl⟩ : syracuseStep 1359029 = 127409) (by norm_num)
theorem B1359053 : Blo 904575 1359053 := bbase (se 3 (by rfl) ⟨254822, by rfl⟩ : syracuseStep 1359053 = 509645) (by norm_num)
theorem B1359077 : Blo 904575 1359077 := bbase (se 4 (by rfl) ⟨127413, by rfl⟩ : syracuseStep 1359077 = 254827) (by norm_num)
theorem B1146089 : Blo 904575 1146089 := bbase (se 2 (by rfl) ⟨429783, by rfl⟩ : syracuseStep 1146089 = 859567) (by norm_num)
theorem B2039021 : Blo 904575 2039021 := bbase (se 3 (by rfl) ⟨382316, by rfl⟩ : syracuseStep 2039021 = 764633) (by norm_num)
theorem B1359101 : Blo 904575 1359101 := bbase (se 3 (by rfl) ⟨254831, by rfl⟩ : syracuseStep 1359101 = 509663) (by norm_num)
theorem B1359125 : Blo 904575 1359125 := bbase (se 6 (by rfl) ⟨31854, by rfl⟩ : syracuseStep 1359125 = 63709) (by norm_num)
theorem B1146145 : Blo 904575 1146145 := bbase (se 2 (by rfl) ⟨429804, by rfl⟩ : syracuseStep 1146145 = 859609) (by norm_num)
theorem B1359149 : Blo 904575 1359149 := bbase (se 3 (by rfl) ⟨254840, by rfl⟩ : syracuseStep 1359149 = 509681) (by norm_num)
theorem B1719605 : Blo 904575 1719605 := bbase (se 5 (by rfl) ⟨80606, by rfl⟩ : syracuseStep 1719605 = 161213) (by norm_num)
theorem B2039093 : Blo 904575 2039093 := bbase (se 5 (by rfl) ⟨95582, by rfl⟩ : syracuseStep 2039093 = 191165) (by norm_num)
theorem B1359173 : Blo 904575 1359173 := bbase (se 4 (by rfl) ⟨127422, by rfl⟩ : syracuseStep 1359173 = 254845) (by norm_num)
theorem B2293069 : Blo 904575 2293069 := bbase (se 3 (by rfl) ⟨429950, by rfl⟩ : syracuseStep 2293069 = 859901) (by norm_num)
theorem B1359197 : Blo 904575 1359197 := bbase (se 3 (by rfl) ⟨254849, by rfl⟩ : syracuseStep 1359197 = 509699) (by norm_num)
theorem B966001 : Blo 904575 966001 := bbase (se 2 (by rfl) ⟨362250, by rfl⟩ : syracuseStep 966001 = 724501) (by norm_num)
theorem B1359221 : Blo 904575 1359221 := bbase (se 5 (by rfl) ⟨63713, by rfl⟩ : syracuseStep 1359221 = 127427) (by norm_num)
theorem B1449341 : Blo 904575 1449341 := bbase (se 3 (by rfl) ⟨271751, by rfl⟩ : syracuseStep 1449341 = 543503) (by norm_num)
theorem B2039165 : Blo 904575 2039165 := bbase (se 3 (by rfl) ⟨382343, by rfl⟩ : syracuseStep 2039165 = 764687) (by norm_num)
theorem B1146241 : Blo 904575 1146241 := bbase (se 2 (by rfl) ⟨429840, by rfl⟩ : syracuseStep 1146241 = 859681) (by norm_num)
theorem B1359245 : Blo 904575 1359245 := bbase (se 3 (by rfl) ⟨254858, by rfl⟩ : syracuseStep 1359245 = 509717) (by norm_num)
theorem B1375645 : Blo 904575 1375645 := bbase (se 3 (by rfl) ⟨257933, by rfl⟩ : syracuseStep 1375645 = 515867) (by norm_num)
theorem B1359269 : Blo 904575 1359269 := bbase (se 4 (by rfl) ⟨127431, by rfl⟩ : syracuseStep 1359269 = 254863) (by norm_num)
theorem B6528437 : Blo 904575 6528437 := bbase (se 5 (by rfl) ⟨306020, by rfl⟩ : syracuseStep 6528437 = 612041) (by norm_num)
theorem B2293181 : Blo 904575 2293181 := bbase (se 3 (by rfl) ⟨429971, by rfl⟩ : syracuseStep 2293181 = 859943) (by norm_num)
theorem B1359293 : Blo 904575 1359293 := bbase (se 3 (by rfl) ⟨254867, by rfl⟩ : syracuseStep 1359293 = 509735) (by norm_num)
theorem B2039237 : Blo 904575 2039237 := bbase (se 4 (by rfl) ⟨191178, by rfl⟩ : syracuseStep 2039237 = 382357) (by norm_num)
theorem B3866069 : Blo 904575 3866069 := bbase (se 7 (by rfl) ⟨45305, by rfl⟩ : syracuseStep 3866069 = 90611) (by norm_num)
theorem B1359317 : Blo 904575 1359317 := bbase (se 7 (by rfl) ⟨15929, by rfl⟩ : syracuseStep 1359317 = 31859) (by norm_num)
theorem B1359341 : Blo 904575 1359341 := bbase (se 3 (by rfl) ⟨254876, by rfl⟩ : syracuseStep 1359341 = 509753) (by norm_num)
theorem B1359365 : Blo 904575 1359365 := bbase (se 4 (by rfl) ⟨127440, by rfl⟩ : syracuseStep 1359365 = 254881) (by norm_num)
theorem B2039309 : Blo 904575 2039309 := bbase (se 3 (by rfl) ⟨382370, by rfl⟩ : syracuseStep 2039309 = 764741) (by norm_num)
theorem B4587029 : Blo 904575 4587029 := bbase (se 6 (by rfl) ⟨107508, by rfl⟩ : syracuseStep 4587029 = 215017) (by norm_num)
theorem B1359389 : Blo 904575 1359389 := bbase (se 3 (by rfl) ⟨254885, by rfl⟩ : syracuseStep 1359389 = 509771) (by norm_num)
theorem B1146413 : Blo 904575 1146413 := bbase (se 3 (by rfl) ⟨214952, by rfl⟩ : syracuseStep 1146413 = 429905) (by norm_num)
theorem B2326061 : Blo 904575 2326061 := bbase (se 3 (by rfl) ⟨436136, by rfl⟩ : syracuseStep 2326061 = 872273) (by norm_num)
theorem B3055157 : Blo 904575 3055157 := bbase (se 5 (by rfl) ⟨143210, by rfl⟩ : syracuseStep 3055157 = 286421) (by norm_num)
theorem B1359413 : Blo 904575 1359413 := bbase (se 5 (by rfl) ⟨63722, by rfl⟩ : syracuseStep 1359413 = 127445) (by norm_num)
theorem B1449533 : Blo 904575 1449533 := bbase (se 3 (by rfl) ⟨271787, by rfl⟩ : syracuseStep 1449533 = 543575) (by norm_num)
theorem B1359437 : Blo 904575 1359437 := bbase (se 3 (by rfl) ⟨254894, by rfl⟩ : syracuseStep 1359437 = 509789) (by norm_num)
theorem B1719893 : Blo 904575 1719893 := bbase (se 8 (by rfl) ⟨10077, by rfl⟩ : syracuseStep 1719893 = 20155) (by norm_num)
theorem B7347797 : Blo 904575 7347797 := bbase (se 8 (by rfl) ⟨43053, by rfl⟩ : syracuseStep 7347797 = 86107) (by norm_num)
theorem B2039381 : Blo 904575 2039381 := bbase (se 8 (by rfl) ⟨11949, by rfl⟩ : syracuseStep 2039381 = 23899) (by norm_num)
theorem B1146469 : Blo 904575 1146469 := bbase (se 4 (by rfl) ⟨107481, by rfl⟩ : syracuseStep 1146469 = 214963) (by norm_num)
theorem B1359461 : Blo 904575 1359461 := bbase (se 4 (by rfl) ⟨127449, by rfl⟩ : syracuseStep 1359461 = 254899) (by norm_num)
theorem B2293373 : Blo 904575 2293373 := bbase (se 3 (by rfl) ⟨430007, by rfl⟩ : syracuseStep 2293373 = 860015) (by norm_num)
theorem B1359485 : Blo 904575 1359485 := bbase (se 3 (by rfl) ⟨254903, by rfl⟩ : syracuseStep 1359485 = 509807) (by norm_num)
theorem B1359509 : Blo 904575 1359509 := bbase (se 6 (by rfl) ⟨31863, by rfl⟩ : syracuseStep 1359509 = 63727) (by norm_num)
theorem B2039453 : Blo 904575 2039453 := bbase (se 3 (by rfl) ⟨382397, by rfl⟩ : syracuseStep 2039453 = 764795) (by norm_num)
theorem B1359533 : Blo 904575 1359533 := bbase (se 3 (by rfl) ⟨254912, by rfl⟩ : syracuseStep 1359533 = 509825) (by norm_num)
theorem B1146565 : Blo 904575 1146565 := bbase (se 4 (by rfl) ⟨107490, by rfl⟩ : syracuseStep 1146565 = 214981) (by norm_num)
theorem B1359557 : Blo 904575 1359557 := bbase (se 4 (by rfl) ⟨127458, by rfl⟩ : syracuseStep 1359557 = 254917) (by norm_num)
theorem B1359581 : Blo 904575 1359581 := bbase (se 3 (by rfl) ⟨254921, by rfl⟩ : syracuseStep 1359581 = 509843) (by norm_num)
theorem B2039525 : Blo 904575 2039525 := bbase (se 4 (by rfl) ⟨191205, by rfl⟩ : syracuseStep 2039525 = 382411) (by norm_num)
theorem B966377 : Blo 904575 966377 := bbase (se 2 (by rfl) ⟨362391, by rfl⟩ : syracuseStep 966377 = 724783) (by norm_num)
theorem B1720045 : Blo 904575 1720045 := bbase (se 3 (by rfl) ⟨322508, by rfl⟩ : syracuseStep 1720045 = 645017) (by norm_num)
theorem B1359605 : Blo 904575 1359605 := bbase (se 5 (by rfl) ⟨63731, by rfl⟩ : syracuseStep 1359605 = 127463) (by norm_num)
theorem B1359629 : Blo 904575 1359629 := bbase (se 3 (by rfl) ⟨254930, by rfl⟩ : syracuseStep 1359629 = 509861) (by norm_num)
theorem B1031953 : Blo 904575 1031953 := bbase (se 2 (by rfl) ⟨386982, by rfl⟩ : syracuseStep 1031953 = 773965) (by norm_num)
theorem B1359653 : Blo 904575 1359653 := bbase (se 4 (by rfl) ⟨127467, by rfl⟩ : syracuseStep 1359653 = 254935) (by norm_num)
theorem B2039597 : Blo 904575 2039597 := bbase (se 3 (by rfl) ⟨382424, by rfl⟩ : syracuseStep 2039597 = 764849) (by norm_num)
theorem B966449 : Blo 904575 966449 := bbase (se 2 (by rfl) ⟨362418, by rfl⟩ : syracuseStep 966449 = 724837) (by norm_num)
theorem B1359677 : Blo 904575 1359677 := bbase (se 3 (by rfl) ⟨254939, by rfl⟩ : syracuseStep 1359677 = 509879) (by norm_num)
theorem B1359701 : Blo 904575 1359701 := bbase (se 9 (by rfl) ⟨3983, by rfl⟩ : syracuseStep 1359701 = 7967) (by norm_num)
theorem B1359725 : Blo 904575 1359725 := bbase (se 3 (by rfl) ⟨254948, by rfl⟩ : syracuseStep 1359725 = 509897) (by norm_num)
theorem B1146737 : Blo 904575 1146737 := bbase (se 2 (by rfl) ⟨430026, by rfl⟩ : syracuseStep 1146737 = 860053) (by norm_num)
theorem B3669877 : Blo 904575 3669877 := bbase (se 5 (by rfl) ⟨172025, by rfl⟩ : syracuseStep 3669877 = 344051) (by norm_num)
theorem B3440501 : Blo 904575 3440501 := bbase (se 5 (by rfl) ⟨161273, by rfl⟩ : syracuseStep 3440501 = 322547) (by norm_num)
theorem B2039669 : Blo 904575 2039669 := bbase (se 5 (by rfl) ⟨95609, by rfl⟩ : syracuseStep 2039669 = 191219) (by norm_num)
theorem B1359749 : Blo 904575 1359749 := bbase (se 4 (by rfl) ⟨127476, by rfl⟩ : syracuseStep 1359749 = 254953) (by norm_num)
theorem B1032089 : Blo 904575 1032089 := bbase (se 2 (by rfl) ⟨387033, by rfl⟩ : syracuseStep 1032089 = 774067) (by norm_num)
theorem B1359773 : Blo 904575 1359773 := bbase (se 3 (by rfl) ⟨254957, by rfl⟩ : syracuseStep 1359773 = 509915) (by norm_num)
theorem B1146793 : Blo 904575 1146793 := bbase (se 2 (by rfl) ⟨430047, by rfl⟩ : syracuseStep 1146793 = 860095) (by norm_num)
theorem B1359797 : Blo 904575 1359797 := bbase (se 5 (by rfl) ⟨63740, by rfl⟩ : syracuseStep 1359797 = 127481) (by norm_num)
theorem B2039741 : Blo 904575 2039741 := bbase (se 3 (by rfl) ⟨382451, by rfl⟩ : syracuseStep 2039741 = 764903) (by norm_num)
theorem B1359821 : Blo 904575 1359821 := bbase (se 3 (by rfl) ⟨254966, by rfl⟩ : syracuseStep 1359821 = 509933) (by norm_num)
theorem B2293717 : Blo 904575 2293717 := bbase (se 7 (by rfl) ⟨26879, by rfl⟩ : syracuseStep 2293717 = 53759) (by norm_num)
theorem B3055589 : Blo 904575 3055589 := bbase (se 4 (by rfl) ⟨286461, by rfl⟩ : syracuseStep 3055589 = 572923) (by norm_num)
theorem B1359845 : Blo 904575 1359845 := bbase (se 4 (by rfl) ⟨127485, by rfl⟩ : syracuseStep 1359845 = 254971) (by norm_num)
theorem B966637 : Blo 904575 966637 := bbase (se 3 (by rfl) ⟨181244, by rfl⟩ : syracuseStep 966637 = 362489) (by norm_num)
theorem B1933301 : Blo 904575 1933301 := bbase (se 5 (by rfl) ⟨90623, by rfl⟩ : syracuseStep 1933301 = 181247) (by norm_num)
theorem B1146899 : Blo 904575 1146899 := bstep (se 1 (by rfl) ⟨860174, by rfl⟩ : syracuseStep 1146899 = 1720349) B1720349
theorem B3055697 : Blo 904575 3055697 := bstep (se 2 (by rfl) ⟨1145886, by rfl⟩ : syracuseStep 3055697 = 2291773) B2291773
theorem B1933411 : Blo 904575 1933411 := bstep (se 1 (by rfl) ⟨1450058, by rfl⟩ : syracuseStep 1933411 = 2900117) B2900117
theorem B2293859 : Blo 904575 2293859 := bstep (se 1 (by rfl) ⟨1720394, by rfl⟩ : syracuseStep 2293859 = 3440789) B3440789
theorem B3866737 : Blo 904575 3866737 := bstep (se 2 (by rfl) ⟨1450026, by rfl⟩ : syracuseStep 3866737 = 2900053) B2900053
theorem B1720433 : Blo 904575 1720433 := bstep (se 2 (by rfl) ⟨645162, by rfl⟩ : syracuseStep 1720433 = 1290325) B1290325
theorem B2900195 : Blo 904575 2900195 := bstep (se 1 (by rfl) ⟨2175146, by rfl⟩ : syracuseStep 2900195 = 4350293) B4350293
theorem B5161229 : Blo 904575 5161229 := bstep (se 3 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 5161229 = 1935461) B1935461
theorem B1450289 : Blo 904575 1450289 := bstep (se 2 (by rfl) ⟨543858, by rfl⟩ : syracuseStep 1450289 = 1087717) B1087717
theorem B3096899 : Blo 904575 3096899 := bstep (se 1 (by rfl) ⟨2322674, by rfl⟩ : syracuseStep 3096899 = 4645349) B4645349
theorem B966979 : Blo 904575 966979 := bstep (se 1 (by rfl) ⟨725234, by rfl⟩ : syracuseStep 966979 = 1450469) B1450469
theorem B1630595 : Blo 904575 1630595 := bstep (se 1 (by rfl) ⟨1222946, by rfl⟩ : syracuseStep 1630595 = 2445893) B2445893
theorem B5153165 : Blo 904575 5153165 := bstep (se 3 (by rfl) ⟨966218, by rfl⟩ : syracuseStep 5153165 = 1932437) B1932437
theorem B1720835 : Blo 904575 1720835 := bstep (se 1 (by rfl) ⟨1290626, by rfl⟩ : syracuseStep 1720835 = 2581253) B2581253
theorem B2753041 : Blo 904575 2753041 := bstep (se 2 (by rfl) ⟨1032390, by rfl⟩ : syracuseStep 2753041 = 2064781) B2064781
theorem B967235 : Blo 904575 967235 := bstep (se 1 (by rfl) ⟨725426, by rfl⟩ : syracuseStep 967235 = 1450853) B1450853
theorem B5800517 : Blo 904575 5800517 := bstep (se 4 (by rfl) ⟨543798, by rfl⟩ : syracuseStep 5800517 = 1087597) B1087597
theorem B3056237 : Blo 904575 3056237 := bstep (se 3 (by rfl) ⟨573044, by rfl⟩ : syracuseStep 3056237 = 1146089) B1146089
theorem B2581105 : Blo 904575 2581105 := bstep (se 2 (by rfl) ⟨967914, by rfl⟩ : syracuseStep 2581105 = 1935829) B1935829
theorem B3056291 : Blo 904575 3056291 := bstep (se 1 (by rfl) ⟨2292218, by rfl⟩ : syracuseStep 3056291 = 4584437) B4584437
theorem B11019077 : Blo 904575 11019077 := bstep (se 4 (by rfl) ⟨1033038, by rfl⟩ : syracuseStep 11019077 = 2066077) B2066077
theorem B2581379 : Blo 904575 2581379 := bstep (se 1 (by rfl) ⟨1936034, by rfl⟩ : syracuseStep 2581379 = 3872069) B3872069
theorem B3056561 : Blo 904575 3056561 := bstep (se 2 (by rfl) ⟨1146210, by rfl⟩ : syracuseStep 3056561 = 2292421) B2292421
theorem B6882245 : Blo 904575 6882245 := bstep (se 4 (by rfl) ⟨645210, by rfl⟩ : syracuseStep 6882245 = 1290421) B1290421
theorem B4580387 : Blo 904575 4580387 := bstep (se 1 (by rfl) ⟨3435290, by rfl⟩ : syracuseStep 4580387 = 6870581) B6870581
theorem B2581571 : Blo 904575 2581571 := bstep (se 1 (by rfl) ⟨1936178, by rfl⟩ : syracuseStep 2581571 = 3872357) B3872357
theorem B2942129 : Blo 904575 2942129 := bstep (se 2 (by rfl) ⟨1103298, by rfl⟩ : syracuseStep 2942129 = 2206597) B2206597
theorem B10200305 : Blo 904575 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B1934641 : Blo 904575 1934641 := bstep (se 2 (by rfl) ⟨725490, by rfl⟩ : syracuseStep 1934641 = 1450981) B1450981
theorem B967987 : Blo 904575 967987 := bstep (se 1 (by rfl) ⟨725990, by rfl⟩ : syracuseStep 967987 = 1451981) B1451981
theorem B3057101 : Blo 904575 3057101 := bstep (se 3 (by rfl) ⟨573206, by rfl⟩ : syracuseStep 3057101 = 1146413) B1146413
theorem B2483693 : Blo 904575 2483693 := bstep (se 3 (by rfl) ⟨465692, by rfl⟩ : syracuseStep 2483693 = 931385) B931385
theorem B3917297 : Blo 904575 3917297 := bstep (se 2 (by rfl) ⟨1468986, by rfl⟩ : syracuseStep 3917297 = 2937973) B2937973
theorem B6522353 : Blo 904575 6522353 := bstep (se 2 (by rfl) ⟨2445882, by rfl⟩ : syracuseStep 6522353 = 4891765) B4891765
theorem B3057155 : Blo 904575 3057155 := bstep (se 1 (by rfl) ⟨2292866, by rfl⟩ : syracuseStep 3057155 = 4585733) B4585733
theorem B4646413 : Blo 904575 4646413 := bstep (se 3 (by rfl) ⟨871202, by rfl⟩ : syracuseStep 4646413 = 1742405) B1742405
theorem B4646477 : Blo 904575 4646477 := bstep (se 3 (by rfl) ⟨871214, by rfl⟩ : syracuseStep 4646477 = 1742429) B1742429
theorem B1451699 : Blo 904575 1451699 := bstep (se 1 (by rfl) ⟨1088774, by rfl⟩ : syracuseStep 1451699 = 2177549) B2177549
theorem B4130509 : Blo 904575 4130509 := bstep (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) B1548941
theorem B4646641 : Blo 904575 4646641 := bstep (se 2 (by rfl) ⟨1742490, by rfl⟩ : syracuseStep 4646641 = 3484981) B3484981
theorem B4589297 : Blo 904575 4589297 := bstep (se 2 (by rfl) ⟨1720986, by rfl⟩ : syracuseStep 4589297 = 3441973) B3441973
theorem B6612749 : Blo 904575 6612749 := bstep (se 3 (by rfl) ⟨1239890, by rfl⟩ : syracuseStep 6612749 = 2479781) B2479781
theorem B3057425 : Blo 904575 3057425 := bstep (se 2 (by rfl) ⟨1146534, by rfl⟩ : syracuseStep 3057425 = 2293069) B2293069
theorem B1288001 : Blo 904575 1288001 := bstep (se 2 (by rfl) ⟨483000, by rfl⟩ : syracuseStep 1288001 = 966001) B966001
theorem B4581197 : Blo 904575 4581197 := bstep (se 3 (by rfl) ⟨858974, by rfl⟩ : syracuseStep 4581197 = 1717949) B1717949
theorem B8710001 : Blo 904575 8710001 := bstep (se 2 (by rfl) ⟨3266250, by rfl⟩ : syracuseStep 8710001 = 6532501) B6532501
theorem B1017715 : Blo 904575 1017715 := bstep (se 1 (by rfl) ⟨763286, by rfl⟩ : syracuseStep 1017715 = 1526573) B1526573
theorem B1451891 : Blo 904575 1451891 := bstep (se 1 (by rfl) ⟨1088918, by rfl⟩ : syracuseStep 1451891 = 2177837) B2177837
theorem B11003789 : Blo 904575 11003789 := bstep (se 3 (by rfl) ⟨2063210, by rfl⟩ : syracuseStep 11003789 = 4126421) B4126421
theorem B11610053 : Blo 904575 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B1017859 : Blo 904575 1017859 := bstep (se 1 (by rfl) ⟨763394, by rfl⟩ : syracuseStep 1017859 = 1526789) B1526789
theorem B1935427 : Blo 904575 1935427 := bstep (se 1 (by rfl) ⟨1451570, by rfl⟩ : syracuseStep 1935427 = 2903141) B2903141
theorem B2902115 : Blo 904575 2902115 := bstep (se 1 (by rfl) ⟨2176586, by rfl⟩ : syracuseStep 2902115 = 4353173) B4353173
theorem B1018003 : Blo 904575 1018003 := bstep (se 1 (by rfl) ⟨763502, by rfl⟩ : syracuseStep 1018003 = 1527005) B1527005
theorem B6621425 : Blo 904575 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B1018147 : Blo 904575 1018147 := bstep (se 1 (by rfl) ⟨763610, by rfl⟩ : syracuseStep 1018147 = 1527221) B1527221
theorem B4352291 : Blo 904575 4352291 := bstep (se 1 (by rfl) ⟨3264218, by rfl⟩ : syracuseStep 4352291 = 6528437) B6528437
theorem B3057965 : Blo 904575 3057965 := bstep (se 3 (by rfl) ⟨573368, by rfl⟩ : syracuseStep 3057965 = 1146737) B1146737
theorem B3058019 : Blo 904575 3058019 := bstep (se 1 (by rfl) ⟨2293514, by rfl⟩ : syracuseStep 3058019 = 4587029) B4587029
theorem B1550707 : Blo 904575 1550707 := bstep (se 1 (by rfl) ⟨1163030, by rfl⟩ : syracuseStep 1550707 = 2326061) B2326061
theorem B1018291 : Blo 904575 1018291 := bstep (se 1 (by rfl) ⟨763718, by rfl⟩ : syracuseStep 1018291 = 1527437) B1527437
theorem B3434957 : Blo 904575 3434957 := bstep (se 3 (by rfl) ⟨644054, by rfl⟩ : syracuseStep 3434957 = 1288109) B1288109
theorem B4893169 : Blo 904575 4893169 := bstep (se 2 (by rfl) ⟨1834938, by rfl⟩ : syracuseStep 4893169 = 3669877) B3669877
theorem B1018435 : Blo 904575 1018435 := bstep (se 1 (by rfl) ⟨763826, by rfl⟩ : syracuseStep 1018435 = 1527653) B1527653
theorem B5155397 : Blo 904575 5155397 := bstep (se 4 (by rfl) ⟨483318, by rfl⟩ : syracuseStep 5155397 = 966637) B966637
theorem B3058289 : Blo 904575 3058289 := bstep (se 2 (by rfl) ⟨1146858, by rfl⟩ : syracuseStep 3058289 = 2293717) B2293717
theorem B1288867 : Blo 904575 1288867 := bstep (se 1 (by rfl) ⟨966650, by rfl⟩ : syracuseStep 1288867 = 1933301) B1933301
theorem B2206403 : Blo 904575 2206403 := bstep (se 1 (by rfl) ⟨1654802, by rfl⟩ : syracuseStep 2206403 = 3309605) B3309605
theorem B1018579 : Blo 904575 1018579 := bstep (se 1 (by rfl) ⟨763934, by rfl⟩ : syracuseStep 1018579 = 1527869) B1527869
theorem B1288963 : Blo 904575 1288963 := bstep (se 1 (by rfl) ⟨966722, by rfl⟩ : syracuseStep 1288963 = 1933445) B1933445
theorem B1936145 : Blo 904575 1936145 := bstep (se 2 (by rfl) ⟨726054, by rfl⟩ : syracuseStep 1936145 = 1452109) B1452109
theorem B3263267 : Blo 904575 3263267 := bstep (se 1 (by rfl) ⟨2447450, by rfl⟩ : syracuseStep 3263267 = 4894901) B4894901
theorem B1526593 : Blo 904575 1526593 := bstep (se 2 (by rfl) ⟨572472, by rfl⟩ : syracuseStep 1526593 = 1144945) B1144945
theorem B1526627 : Blo 904575 1526627 := bstep (se 1 (by rfl) ⟨1144970, by rfl⟩ : syracuseStep 1526627 = 2289941) B2289941
theorem B1018723 : Blo 904575 1018723 := bstep (se 1 (by rfl) ⟨764042, by rfl⟩ : syracuseStep 1018723 = 1528085) B1528085
theorem B1526755 : Blo 904575 1526755 := bstep (se 1 (by rfl) ⟨1145066, by rfl⟩ : syracuseStep 1526755 = 2290133) B2290133
theorem B1018867 : Blo 904575 1018867 := bstep (se 1 (by rfl) ⟨764150, by rfl⟩ : syracuseStep 1018867 = 1528301) B1528301
theorem B3869795 : Blo 904575 3869795 := bstep (se 1 (by rfl) ⟨2902346, by rfl⟩ : syracuseStep 3869795 = 5804693) B5804693
theorem B1526897 : Blo 904575 1526897 := bstep (se 2 (by rfl) ⟨572586, by rfl⟩ : syracuseStep 1526897 = 1145173) B1145173
theorem B1019011 : Blo 904575 1019011 := bstep (se 1 (by rfl) ⟨764258, by rfl⟩ : syracuseStep 1019011 = 1528517) B1528517
theorem B23186573 : Blo 904575 23186573 := bstep (se 3 (by rfl) ⟨4347482, by rfl⟩ : syracuseStep 23186573 = 8694965) B8694965
theorem B3058829 : Blo 904575 3058829 := bstep (se 3 (by rfl) ⟨573530, by rfl⟩ : syracuseStep 3058829 = 1147061) B1147061
theorem B1117363 : Blo 904575 1117363 := bstep (se 1 (by rfl) ⟨838022, by rfl⟩ : syracuseStep 1117363 = 1676045) B1676045
theorem B2174147 : Blo 904575 2174147 := bstep (se 1 (by rfl) ⟨1630610, by rfl⟩ : syracuseStep 2174147 = 3261221) B3261221
theorem B3058883 : Blo 904575 3058883 := bstep (se 1 (by rfl) ⟨2294162, by rfl⟩ : syracuseStep 3058883 = 4588325) B4588325
theorem B6196421 : Blo 904575 6196421 := bstep (se 4 (by rfl) ⟨580914, by rfl⟩ : syracuseStep 6196421 = 1161829) B1161829
theorem B1527025 : Blo 904575 1527025 := bstep (se 2 (by rfl) ⟨572634, by rfl⟩ : syracuseStep 1527025 = 1145269) B1145269
theorem B4467953 : Blo 904575 4467953 := bstep (se 2 (by rfl) ⟨1675482, by rfl⟩ : syracuseStep 4467953 = 3350965) B3350965
theorem B5156081 : Blo 904575 5156081 := bstep (se 2 (by rfl) ⟨1933530, by rfl⟩ : syracuseStep 5156081 = 3867061) B3867061
theorem B1289459 : Blo 904575 1289459 := bstep (se 1 (by rfl) ⟨967094, by rfl⟩ : syracuseStep 1289459 = 1934189) B1934189
theorem B1527059 : Blo 904575 1527059 := bstep (se 1 (by rfl) ⟨1145294, by rfl⟩ : syracuseStep 1527059 = 2290589) B2290589
theorem B1019155 : Blo 904575 1019155 := bstep (se 1 (by rfl) ⟨764366, by rfl⟩ : syracuseStep 1019155 = 1528733) B1528733
theorem B3673379 : Blo 904575 3673379 := bstep (se 1 (by rfl) ⟨2755034, by rfl⟩ : syracuseStep 3673379 = 5510069) B5510069
theorem B904579 : Blo 904575 904579 := bstep (se 1 (by rfl) ⟨678434, by rfl⟩ : syracuseStep 904579 = 1356869) B1356869
theorem B904595 : Blo 904575 904595 := bstep (se 1 (by rfl) ⟨678446, by rfl⟩ : syracuseStep 904595 = 1356893) B1356893
theorem B1527187 : Blo 904575 1527187 := bstep (se 1 (by rfl) ⟨1145390, by rfl⟩ : syracuseStep 1527187 = 2290781) B2290781
theorem B904611 : Blo 904575 904611 := bstep (se 1 (by rfl) ⟨678458, by rfl⟩ : syracuseStep 904611 = 1356917) B1356917
theorem B1019299 : Blo 904575 1019299 := bstep (se 1 (by rfl) ⟨764474, by rfl⟩ : syracuseStep 1019299 = 1528949) B1528949
theorem B904627 : Blo 904575 904627 := bstep (se 1 (by rfl) ⟨678470, by rfl⟩ : syracuseStep 904627 = 1356941) B1356941
theorem B904643 : Blo 904575 904643 := bstep (se 1 (by rfl) ⟨678482, by rfl⟩ : syracuseStep 904643 = 1356965) B1356965
theorem B3059153 : Blo 904575 3059153 := bstep (se 2 (by rfl) ⟨1147182, by rfl⟩ : syracuseStep 3059153 = 2294365) B2294365
theorem B904659 : Blo 904575 904659 := bstep (se 1 (by rfl) ⟨678494, by rfl⟩ : syracuseStep 904659 = 1356989) B1356989
theorem B904675 : Blo 904575 904675 := bstep (se 1 (by rfl) ⟨678506, by rfl⟩ : syracuseStep 904675 = 1357013) B1357013
theorem B2174435 : Blo 904575 2174435 := bstep (se 1 (by rfl) ⟨1630826, by rfl⟩ : syracuseStep 2174435 = 3261653) B3261653
theorem B904691 : Blo 904575 904691 := bstep (se 1 (by rfl) ⟨678518, by rfl⟩ : syracuseStep 904691 = 1357037) B1357037
theorem B904707 : Blo 904575 904707 := bstep (se 1 (by rfl) ⟨678530, by rfl⟩ : syracuseStep 904707 = 1357061) B1357061
theorem B904723 : Blo 904575 904723 := bstep (se 1 (by rfl) ⟨678542, by rfl⟩ : syracuseStep 904723 = 1357085) B1357085
theorem B1527329 : Blo 904575 1527329 := bstep (se 2 (by rfl) ⟨572748, by rfl⟩ : syracuseStep 1527329 = 1145497) B1145497
theorem B904739 : Blo 904575 904739 := bstep (se 1 (by rfl) ⟨678554, by rfl⟩ : syracuseStep 904739 = 1357109) B1357109
theorem B3681841 : Blo 904575 3681841 := bstep (se 2 (by rfl) ⟨1380690, by rfl⟩ : syracuseStep 3681841 = 2761381) B2761381
theorem B904755 : Blo 904575 904755 := bstep (se 1 (by rfl) ⟨678566, by rfl⟩ : syracuseStep 904755 = 1357133) B1357133
theorem B1019443 : Blo 904575 1019443 := bstep (se 1 (by rfl) ⟨764582, by rfl⟩ : syracuseStep 1019443 = 1529165) B1529165
theorem B904771 : Blo 904575 904771 := bstep (se 1 (by rfl) ⟨678578, by rfl⟩ : syracuseStep 904771 = 1357157) B1357157
theorem B904787 : Blo 904575 904787 := bstep (se 1 (by rfl) ⟨678590, by rfl⟩ : syracuseStep 904787 = 1357181) B1357181
theorem B904803 : Blo 904575 904803 := bstep (se 1 (by rfl) ⟨678602, by rfl⟩ : syracuseStep 904803 = 1357205) B1357205
theorem B2035313 : Blo 904575 2035313 := bstep (se 2 (by rfl) ⟨763242, by rfl⟩ : syracuseStep 2035313 = 1526485) B1526485
theorem B904819 : Blo 904575 904819 := bstep (se 1 (by rfl) ⟨678614, by rfl⟩ : syracuseStep 904819 = 1357229) B1357229
theorem B2035331 : Blo 904575 2035331 := bstep (se 1 (by rfl) ⟨1526498, by rfl⟩ : syracuseStep 2035331 = 3052997) B3052997
theorem B904835 : Blo 904575 904835 := bstep (se 1 (by rfl) ⟨678626, by rfl⟩ : syracuseStep 904835 = 1357253) B1357253
theorem B904851 : Blo 904575 904851 := bstep (se 1 (by rfl) ⟨678638, by rfl⟩ : syracuseStep 904851 = 1357277) B1357277
theorem B1527457 : Blo 904575 1527457 := bstep (se 2 (by rfl) ⟨572796, by rfl⟩ : syracuseStep 1527457 = 1145593) B1145593
theorem B904867 : Blo 904575 904867 := bstep (se 1 (by rfl) ⟨678650, by rfl⟩ : syracuseStep 904867 = 1357301) B1357301
theorem B2174627 : Blo 904575 2174627 := bstep (se 1 (by rfl) ⟨1630970, by rfl⟩ : syracuseStep 2174627 = 3261941) B3261941
theorem B904883 : Blo 904575 904883 := bstep (se 1 (by rfl) ⟨678662, by rfl⟩ : syracuseStep 904883 = 1357325) B1357325
theorem B904899 : Blo 904575 904899 := bstep (se 1 (by rfl) ⟨678674, by rfl⟩ : syracuseStep 904899 = 1357349) B1357349
theorem B1527491 : Blo 904575 1527491 := bstep (se 1 (by rfl) ⟨1145618, by rfl⟩ : syracuseStep 1527491 = 2291237) B2291237
theorem B17395397 : Blo 904575 17395397 := bstep (se 4 (by rfl) ⟨1630818, by rfl⟩ : syracuseStep 17395397 = 3261637) B3261637
theorem B1019587 : Blo 904575 1019587 := bstep (se 1 (by rfl) ⟨764690, by rfl⟩ : syracuseStep 1019587 = 1529381) B1529381
theorem B904915 : Blo 904575 904915 := bstep (se 1 (by rfl) ⟨678686, by rfl⟩ : syracuseStep 904915 = 1357373) B1357373
theorem B904931 : Blo 904575 904931 := bstep (se 1 (by rfl) ⟨678698, by rfl⟩ : syracuseStep 904931 = 1357397) B1357397
theorem B6876899 : Blo 904575 6876899 := bstep (se 1 (by rfl) ⟨5157674, by rfl⟩ : syracuseStep 6876899 = 10315349) B10315349
theorem B7737059 : Blo 904575 7737059 := bstep (se 1 (by rfl) ⟨5802794, by rfl⟩ : syracuseStep 7737059 = 11605589) B11605589
theorem B904947 : Blo 904575 904947 := bstep (se 1 (by rfl) ⟨678710, by rfl⟩ : syracuseStep 904947 = 1357421) B1357421
theorem B904963 : Blo 904575 904963 := bstep (se 1 (by rfl) ⟨678722, by rfl⟩ : syracuseStep 904963 = 1357445) B1357445
theorem B904979 : Blo 904575 904979 := bstep (se 1 (by rfl) ⟨678734, by rfl⟩ : syracuseStep 904979 = 1357469) B1357469
theorem B904995 : Blo 904575 904995 := bstep (se 1 (by rfl) ⟨678746, by rfl⟩ : syracuseStep 904995 = 1357493) B1357493
theorem B905011 : Blo 904575 905011 := bstep (se 1 (by rfl) ⟨678758, by rfl⟩ : syracuseStep 905011 = 1357517) B1357517
theorem B1527619 : Blo 904575 1527619 := bstep (se 1 (by rfl) ⟨1145714, by rfl⟩ : syracuseStep 1527619 = 2291429) B2291429
theorem B2576195 : Blo 904575 2576195 := bstep (se 1 (by rfl) ⟨1932146, by rfl⟩ : syracuseStep 2576195 = 3864293) B3864293
theorem B905027 : Blo 904575 905027 := bstep (se 1 (by rfl) ⟨678770, by rfl⟩ : syracuseStep 905027 = 1357541) B1357541
theorem B905043 : Blo 904575 905043 := bstep (se 1 (by rfl) ⟨678782, by rfl⟩ : syracuseStep 905043 = 1357565) B1357565
theorem B1019731 : Blo 904575 1019731 := bstep (se 1 (by rfl) ⟨764798, by rfl⟩ : syracuseStep 1019731 = 1529597) B1529597
theorem B905059 : Blo 904575 905059 := bstep (se 1 (by rfl) ⟨678794, by rfl⟩ : syracuseStep 905059 = 1357589) B1357589
theorem B1290097 : Blo 904575 1290097 := bstep (se 2 (by rfl) ⟨483786, by rfl⟩ : syracuseStep 1290097 = 967573) B967573
theorem B905075 : Blo 904575 905075 := bstep (se 1 (by rfl) ⟨678806, by rfl⟩ : syracuseStep 905075 = 1357613) B1357613
theorem B905091 : Blo 904575 905091 := bstep (se 1 (by rfl) ⟨678818, by rfl⟩ : syracuseStep 905091 = 1357637) B1357637
theorem B4894597 : Blo 904575 4894597 := bstep (se 4 (by rfl) ⟨458868, by rfl⟩ : syracuseStep 4894597 = 917737) B917737
theorem B10309517 : Blo 904575 10309517 := bstep (se 3 (by rfl) ⟨1933034, by rfl⟩ : syracuseStep 10309517 = 3866069) B3866069
theorem B2035601 : Blo 904575 2035601 := bstep (se 2 (by rfl) ⟨763350, by rfl⟩ : syracuseStep 2035601 = 1526701) B1526701
theorem B905107 : Blo 904575 905107 := bstep (se 1 (by rfl) ⟨678830, by rfl⟩ : syracuseStep 905107 = 1357661) B1357661
theorem B2035619 : Blo 904575 2035619 := bstep (se 1 (by rfl) ⟨1526714, by rfl⟩ : syracuseStep 2035619 = 3053429) B3053429
theorem B905123 : Blo 904575 905123 := bstep (se 1 (by rfl) ⟨678842, by rfl⟩ : syracuseStep 905123 = 1357685) B1357685
theorem B905139 : Blo 904575 905139 := bstep (se 1 (by rfl) ⟨678854, by rfl⟩ : syracuseStep 905139 = 1357709) B1357709
theorem B905155 : Blo 904575 905155 := bstep (se 1 (by rfl) ⟨678866, by rfl⟩ : syracuseStep 905155 = 1357733) B1357733
theorem B1527761 : Blo 904575 1527761 := bstep (se 2 (by rfl) ⟨572910, by rfl⟩ : syracuseStep 1527761 = 1145821) B1145821
theorem B905171 : Blo 904575 905171 := bstep (se 1 (by rfl) ⟨678878, by rfl⟩ : syracuseStep 905171 = 1357757) B1357757
theorem B905187 : Blo 904575 905187 := bstep (se 1 (by rfl) ⟨678890, by rfl⟩ : syracuseStep 905187 = 1357781) B1357781
theorem B1019875 : Blo 904575 1019875 := bstep (se 1 (by rfl) ⟨764906, by rfl⟩ : syracuseStep 1019875 = 1529813) B1529813
theorem B3059693 : Blo 904575 3059693 := bstep (se 3 (by rfl) ⟨573692, by rfl⟩ : syracuseStep 3059693 = 1147385) B1147385
theorem B905203 : Blo 904575 905203 := bstep (se 1 (by rfl) ⟨678902, by rfl⟩ : syracuseStep 905203 = 1357805) B1357805
theorem B905219 : Blo 904575 905219 := bstep (se 1 (by rfl) ⟨678914, by rfl⟩ : syracuseStep 905219 = 1357829) B1357829
theorem B905235 : Blo 904575 905235 := bstep (se 1 (by rfl) ⟨678926, by rfl⟩ : syracuseStep 905235 = 1357853) B1357853
theorem B905251 : Blo 904575 905251 := bstep (se 1 (by rfl) ⟨678938, by rfl⟩ : syracuseStep 905251 = 1357877) B1357877
theorem B905267 : Blo 904575 905267 := bstep (se 1 (by rfl) ⟨678950, by rfl⟩ : syracuseStep 905267 = 1357901) B1357901
theorem B905283 : Blo 904575 905283 := bstep (se 1 (by rfl) ⟨678962, by rfl⟩ : syracuseStep 905283 = 1357925) B1357925
theorem B1527889 : Blo 904575 1527889 := bstep (se 2 (by rfl) ⟨572958, by rfl⟩ : syracuseStep 1527889 = 1145917) B1145917
theorem B905299 : Blo 904575 905299 := bstep (se 1 (by rfl) ⟨678974, by rfl⟩ : syracuseStep 905299 = 1357949) B1357949
theorem B905315 : Blo 904575 905315 := bstep (se 1 (by rfl) ⟨678986, by rfl⟩ : syracuseStep 905315 = 1357973) B1357973
theorem B6533219 : Blo 904575 6533219 := bstep (se 1 (by rfl) ⟨4899914, by rfl⟩ : syracuseStep 6533219 = 9799829) B9799829
theorem B10457201 : Blo 904575 10457201 := bstep (se 2 (by rfl) ⟨3921450, by rfl⟩ : syracuseStep 10457201 = 7842901) B7842901
theorem B905331 : Blo 904575 905331 := bstep (se 1 (by rfl) ⟨678998, by rfl⟩ : syracuseStep 905331 = 1357997) B1357997
theorem B1527923 : Blo 904575 1527923 := bstep (se 1 (by rfl) ⟨1145942, by rfl⟩ : syracuseStep 1527923 = 2291885) B2291885
theorem B905347 : Blo 904575 905347 := bstep (se 1 (by rfl) ⟨679010, by rfl⟩ : syracuseStep 905347 = 1358021) B1358021
theorem B2289809 : Blo 904575 2289809 := bstep (se 2 (by rfl) ⟨858678, by rfl⟩ : syracuseStep 2289809 = 1717357) B1717357
theorem B905363 : Blo 904575 905363 := bstep (se 1 (by rfl) ⟨679022, by rfl⟩ : syracuseStep 905363 = 1358045) B1358045
theorem B905379 : Blo 904575 905379 := bstep (se 1 (by rfl) ⟨679034, by rfl⟩ : syracuseStep 905379 = 1358069) B1358069
theorem B6197411 : Blo 904575 6197411 := bstep (se 1 (by rfl) ⟨4648058, by rfl⟩ : syracuseStep 6197411 = 9296117) B9296117
theorem B2035889 : Blo 904575 2035889 := bstep (se 2 (by rfl) ⟨763458, by rfl⟩ : syracuseStep 2035889 = 1526917) B1526917
theorem B905395 : Blo 904575 905395 := bstep (se 1 (by rfl) ⟨679046, by rfl⟩ : syracuseStep 905395 = 1358093) B1358093
theorem B1290433 : Blo 904575 1290433 := bstep (se 2 (by rfl) ⟨483912, by rfl⟩ : syracuseStep 1290433 = 967825) B967825
theorem B2035907 : Blo 904575 2035907 := bstep (se 1 (by rfl) ⟨1526930, by rfl⟩ : syracuseStep 2035907 = 3053861) B3053861
theorem B905411 : Blo 904575 905411 := bstep (se 1 (by rfl) ⟨679058, by rfl⟩ : syracuseStep 905411 = 1358117) B1358117
theorem B905427 : Blo 904575 905427 := bstep (se 1 (by rfl) ⟨679070, by rfl⟩ : syracuseStep 905427 = 1358141) B1358141
theorem B905443 : Blo 904575 905443 := bstep (se 1 (by rfl) ⟨679082, by rfl⟩ : syracuseStep 905443 = 1358165) B1358165
theorem B1224931 : Blo 904575 1224931 := bstep (se 1 (by rfl) ⟨918698, by rfl⟩ : syracuseStep 1224931 = 1837397) B1837397
theorem B905459 : Blo 904575 905459 := bstep (se 1 (by rfl) ⟨679094, by rfl⟩ : syracuseStep 905459 = 1358189) B1358189
theorem B1528051 : Blo 904575 1528051 := bstep (se 1 (by rfl) ⟨1146038, by rfl⟩ : syracuseStep 1528051 = 2292077) B2292077
theorem B905475 : Blo 904575 905475 := bstep (se 1 (by rfl) ⟨679106, by rfl⟩ : syracuseStep 905475 = 1358213) B1358213
theorem B8712461 : Blo 904575 8712461 := bstep (se 3 (by rfl) ⟨1633586, by rfl⟩ : syracuseStep 8712461 = 3267173) B3267173
theorem B905491 : Blo 904575 905491 := bstep (se 1 (by rfl) ⟨679118, by rfl⟩ : syracuseStep 905491 = 1358237) B1358237
theorem B905507 : Blo 904575 905507 := bstep (se 1 (by rfl) ⟨679130, by rfl⟩ : syracuseStep 905507 = 1358261) B1358261
theorem B905523 : Blo 904575 905523 := bstep (se 1 (by rfl) ⟨679142, by rfl⟩ : syracuseStep 905523 = 1358285) B1358285
theorem B905539 : Blo 904575 905539 := bstep (se 1 (by rfl) ⟨679154, by rfl⟩ : syracuseStep 905539 = 1358309) B1358309
theorem B905555 : Blo 904575 905555 := bstep (se 1 (by rfl) ⟨679166, by rfl⟩ : syracuseStep 905555 = 1358333) B1358333
theorem B905571 : Blo 904575 905571 := bstep (se 1 (by rfl) ⟨679178, by rfl⟩ : syracuseStep 905571 = 1358357) B1358357
theorem B2355569 : Blo 904575 2355569 := bstep (se 2 (by rfl) ⟨883338, by rfl⟩ : syracuseStep 2355569 = 1766677) B1766677
theorem B905587 : Blo 904575 905587 := bstep (se 1 (by rfl) ⟨679190, by rfl⟩ : syracuseStep 905587 = 1358381) B1358381
theorem B1528193 : Blo 904575 1528193 := bstep (se 2 (by rfl) ⟨573072, by rfl⟩ : syracuseStep 1528193 = 1146145) B1146145
theorem B905603 : Blo 904575 905603 := bstep (se 1 (by rfl) ⟨679202, by rfl⟩ : syracuseStep 905603 = 1358405) B1358405
theorem B905619 : Blo 904575 905619 := bstep (se 1 (by rfl) ⟨679214, by rfl⟩ : syracuseStep 905619 = 1358429) B1358429
theorem B905635 : Blo 904575 905635 := bstep (se 1 (by rfl) ⟨679226, by rfl⟩ : syracuseStep 905635 = 1358453) B1358453
theorem B905651 : Blo 904575 905651 := bstep (se 1 (by rfl) ⟨679238, by rfl⟩ : syracuseStep 905651 = 1358477) B1358477
theorem B905667 : Blo 904575 905667 := bstep (se 1 (by rfl) ⟨679250, by rfl⟩ : syracuseStep 905667 = 1358501) B1358501
theorem B2036177 : Blo 904575 2036177 := bstep (se 2 (by rfl) ⟨763566, by rfl⟩ : syracuseStep 2036177 = 1527133) B1527133
theorem B905683 : Blo 904575 905683 := bstep (se 1 (by rfl) ⟨679262, by rfl⟩ : syracuseStep 905683 = 1358525) B1358525
theorem B979427 : Blo 904575 979427 := bstep (se 1 (by rfl) ⟨734570, by rfl⟩ : syracuseStep 979427 = 1469141) B1469141
theorem B2036195 : Blo 904575 2036195 := bstep (se 1 (by rfl) ⟨1527146, by rfl⟩ : syracuseStep 2036195 = 3054293) B3054293
theorem B905699 : Blo 904575 905699 := bstep (se 1 (by rfl) ⟨679274, by rfl⟩ : syracuseStep 905699 = 1358549) B1358549
theorem B3264995 : Blo 904575 3264995 := bstep (se 1 (by rfl) ⟨2448746, by rfl⟩ : syracuseStep 3264995 = 4897493) B4897493
theorem B2175473 : Blo 904575 2175473 := bstep (se 2 (by rfl) ⟨815802, by rfl⟩ : syracuseStep 2175473 = 1631605) B1631605
theorem B905715 : Blo 904575 905715 := bstep (se 1 (by rfl) ⟨679286, by rfl⟩ : syracuseStep 905715 = 1358573) B1358573
theorem B1528321 : Blo 904575 1528321 := bstep (se 2 (by rfl) ⟨573120, by rfl⟩ : syracuseStep 1528321 = 1146241) B1146241
theorem B905731 : Blo 904575 905731 := bstep (se 1 (by rfl) ⟨679298, by rfl⟩ : syracuseStep 905731 = 1358597) B1358597
theorem B905747 : Blo 904575 905747 := bstep (se 1 (by rfl) ⟨679310, by rfl⟩ : syracuseStep 905747 = 1358621) B1358621
theorem B1528355 : Blo 904575 1528355 := bstep (se 1 (by rfl) ⟨1146266, by rfl⟩ : syracuseStep 1528355 = 2292533) B2292533
theorem B905763 : Blo 904575 905763 := bstep (se 1 (by rfl) ⟨679322, by rfl⟩ : syracuseStep 905763 = 1358645) B1358645
theorem B905779 : Blo 904575 905779 := bstep (se 1 (by rfl) ⟨679334, by rfl⟩ : syracuseStep 905779 = 1358669) B1358669
theorem B905795 : Blo 904575 905795 := bstep (se 1 (by rfl) ⟨679346, by rfl⟩ : syracuseStep 905795 = 1358693) B1358693
theorem B905811 : Blo 904575 905811 := bstep (se 1 (by rfl) ⟨679358, by rfl⟩ : syracuseStep 905811 = 1358717) B1358717
theorem B2175587 : Blo 904575 2175587 := bstep (se 1 (by rfl) ⟨1631690, by rfl⟩ : syracuseStep 2175587 = 3263381) B3263381
theorem B905827 : Blo 904575 905827 := bstep (se 1 (by rfl) ⟨679370, by rfl⟩ : syracuseStep 905827 = 1358741) B1358741
theorem B2577005 : Blo 904575 2577005 := bstep (se 3 (by rfl) ⟨483188, by rfl⟩ : syracuseStep 2577005 = 966377) B966377
theorem B905843 : Blo 904575 905843 := bstep (se 1 (by rfl) ⟨679382, by rfl⟩ : syracuseStep 905843 = 1358765) B1358765
theorem B905859 : Blo 904575 905859 := bstep (se 1 (by rfl) ⟨679394, by rfl⟩ : syracuseStep 905859 = 1358789) B1358789
theorem B905875 : Blo 904575 905875 := bstep (se 1 (by rfl) ⟨679406, by rfl⟩ : syracuseStep 905875 = 1358813) B1358813
theorem B5157539 : Blo 904575 5157539 := bstep (se 1 (by rfl) ⟨3868154, by rfl⟩ : syracuseStep 5157539 = 7736309) B7736309
theorem B1528483 : Blo 904575 1528483 := bstep (se 1 (by rfl) ⟨1146362, by rfl⟩ : syracuseStep 1528483 = 2292725) B2292725
theorem B905891 : Blo 904575 905891 := bstep (se 1 (by rfl) ⟨679418, by rfl⟩ : syracuseStep 905891 = 1358837) B1358837
theorem B4584113 : Blo 904575 4584113 := bstep (se 2 (by rfl) ⟨1719042, by rfl⟩ : syracuseStep 4584113 = 3438085) B3438085
theorem B905907 : Blo 904575 905907 := bstep (se 1 (by rfl) ⟨679430, by rfl⟩ : syracuseStep 905907 = 1358861) B1358861
theorem B905923 : Blo 904575 905923 := bstep (se 1 (by rfl) ⟨679442, by rfl⟩ : syracuseStep 905923 = 1358885) B1358885
theorem B905939 : Blo 904575 905939 := bstep (se 1 (by rfl) ⟨679454, by rfl⟩ : syracuseStep 905939 = 1358909) B1358909
theorem B905955 : Blo 904575 905955 := bstep (se 1 (by rfl) ⟨679466, by rfl⟩ : syracuseStep 905955 = 1358933) B1358933
theorem B2036465 : Blo 904575 2036465 := bstep (se 2 (by rfl) ⟨763674, by rfl⟩ : syracuseStep 2036465 = 1527349) B1527349
theorem B905971 : Blo 904575 905971 := bstep (se 1 (by rfl) ⟨679478, by rfl⟩ : syracuseStep 905971 = 1358957) B1358957
theorem B2036483 : Blo 904575 2036483 := bstep (se 1 (by rfl) ⟨1527362, by rfl⟩ : syracuseStep 2036483 = 3054725) B3054725
theorem B905987 : Blo 904575 905987 := bstep (se 1 (by rfl) ⟨679490, by rfl⟩ : syracuseStep 905987 = 1358981) B1358981
theorem B2175761 : Blo 904575 2175761 := bstep (se 2 (by rfl) ⟨815910, by rfl⟩ : syracuseStep 2175761 = 1631821) B1631821
theorem B906003 : Blo 904575 906003 := bstep (se 1 (by rfl) ⟨679502, by rfl⟩ : syracuseStep 906003 = 1359005) B1359005
theorem B906019 : Blo 904575 906019 := bstep (se 1 (by rfl) ⟨679514, by rfl⟩ : syracuseStep 906019 = 1359029) B1359029
theorem B2577197 : Blo 904575 2577197 := bstep (se 3 (by rfl) ⟨483224, by rfl⟩ : syracuseStep 2577197 = 966449) B966449
theorem B1528625 : Blo 904575 1528625 := bstep (se 2 (by rfl) ⟨573234, by rfl⟩ : syracuseStep 1528625 = 1146469) B1146469
theorem B906035 : Blo 904575 906035 := bstep (se 1 (by rfl) ⟨679526, by rfl⟩ : syracuseStep 906035 = 1359053) B1359053
theorem B906051 : Blo 904575 906051 := bstep (se 1 (by rfl) ⟨679538, by rfl⟩ : syracuseStep 906051 = 1359077) B1359077
theorem B906067 : Blo 904575 906067 := bstep (se 1 (by rfl) ⟨679550, by rfl⟩ : syracuseStep 906067 = 1359101) B1359101
theorem B906083 : Blo 904575 906083 := bstep (se 1 (by rfl) ⟨679562, by rfl⟩ : syracuseStep 906083 = 1359125) B1359125
theorem B906099 : Blo 904575 906099 := bstep (se 1 (by rfl) ⟨679574, by rfl⟩ : syracuseStep 906099 = 1359149) B1359149
theorem B906115 : Blo 904575 906115 := bstep (se 1 (by rfl) ⟨679586, by rfl⟩ : syracuseStep 906115 = 1359173) B1359173
theorem B906131 : Blo 904575 906131 := bstep (se 1 (by rfl) ⟨679598, by rfl⟩ : syracuseStep 906131 = 1359197) B1359197
theorem B906147 : Blo 904575 906147 := bstep (se 1 (by rfl) ⟨679610, by rfl⟩ : syracuseStep 906147 = 1359221) B1359221
theorem B1528753 : Blo 904575 1528753 := bstep (se 2 (by rfl) ⟨573282, by rfl⟩ : syracuseStep 1528753 = 1146565) B1146565
theorem B906163 : Blo 904575 906163 := bstep (se 1 (by rfl) ⟨679622, by rfl⟩ : syracuseStep 906163 = 1359245) B1359245
theorem B906179 : Blo 904575 906179 := bstep (se 1 (by rfl) ⟨679634, by rfl⟩ : syracuseStep 906179 = 1359269) B1359269
theorem B1528787 : Blo 904575 1528787 := bstep (se 1 (by rfl) ⟨1146590, by rfl⟩ : syracuseStep 1528787 = 2293181) B2293181
theorem B906195 : Blo 904575 906195 := bstep (se 1 (by rfl) ⟨679646, by rfl⟩ : syracuseStep 906195 = 1359293) B1359293
theorem B906211 : Blo 904575 906211 := bstep (se 1 (by rfl) ⟨679658, by rfl⟩ : syracuseStep 906211 = 1359317) B1359317
theorem B906227 : Blo 904575 906227 := bstep (se 1 (by rfl) ⟨679670, by rfl⟩ : syracuseStep 906227 = 1359341) B1359341
theorem B906243 : Blo 904575 906243 := bstep (se 1 (by rfl) ⟨679682, by rfl⟩ : syracuseStep 906243 = 1359365) B1359365
theorem B2036753 : Blo 904575 2036753 := bstep (se 2 (by rfl) ⟨763782, by rfl⟩ : syracuseStep 2036753 = 1527565) B1527565
theorem B906259 : Blo 904575 906259 := bstep (se 1 (by rfl) ⟨679694, by rfl⟩ : syracuseStep 906259 = 1359389) B1359389
theorem B2036771 : Blo 904575 2036771 := bstep (se 1 (by rfl) ⟨1527578, by rfl⟩ : syracuseStep 2036771 = 3055157) B3055157
theorem B906275 : Blo 904575 906275 := bstep (se 1 (by rfl) ⟨679706, by rfl⟩ : syracuseStep 906275 = 1359413) B1359413
theorem B906291 : Blo 904575 906291 := bstep (se 1 (by rfl) ⟨679718, by rfl⟩ : syracuseStep 906291 = 1359437) B1359437
theorem B906307 : Blo 904575 906307 := bstep (se 1 (by rfl) ⟨679730, by rfl⟩ : syracuseStep 906307 = 1359461) B1359461
theorem B1356881 : Blo 904575 1356881 := bstep (se 2 (by rfl) ⟨508830, by rfl⟩ : syracuseStep 1356881 = 1017661) B1017661
theorem B1528915 : Blo 904575 1528915 := bstep (se 1 (by rfl) ⟨1146686, by rfl⟩ : syracuseStep 1528915 = 2293373) B2293373
theorem B906323 : Blo 904575 906323 := bstep (se 1 (by rfl) ⟨679742, by rfl⟩ : syracuseStep 906323 = 1359485) B1359485
theorem B1356899 : Blo 904575 1356899 := bstep (se 1 (by rfl) ⟨1017674, by rfl⟩ : syracuseStep 1356899 = 2035349) B2035349
theorem B906339 : Blo 904575 906339 := bstep (se 1 (by rfl) ⟨679754, by rfl⟩ : syracuseStep 906339 = 1359509) B1359509
theorem B2290801 : Blo 904575 2290801 := bstep (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) B1718101
theorem B906355 : Blo 904575 906355 := bstep (se 1 (by rfl) ⟨679766, by rfl⟩ : syracuseStep 906355 = 1359533) B1359533
theorem B1356929 : Blo 904575 1356929 := bstep (se 2 (by rfl) ⟨508848, by rfl⟩ : syracuseStep 1356929 = 1017697) B1017697
theorem B906371 : Blo 904575 906371 := bstep (se 1 (by rfl) ⟨679778, by rfl⟩ : syracuseStep 906371 = 1359557) B1359557
theorem B1356947 : Blo 904575 1356947 := bstep (se 1 (by rfl) ⟨1017710, by rfl⟩ : syracuseStep 1356947 = 2035421) B2035421
theorem B906387 : Blo 904575 906387 := bstep (se 1 (by rfl) ⟨679790, by rfl⟩ : syracuseStep 906387 = 1359581) B1359581
theorem B906403 : Blo 904575 906403 := bstep (se 1 (by rfl) ⟨679802, by rfl⟩ : syracuseStep 906403 = 1359605) B1359605
theorem B1356977 : Blo 904575 1356977 := bstep (se 2 (by rfl) ⟨508866, by rfl⟩ : syracuseStep 1356977 = 1017733) B1017733
theorem B906419 : Blo 904575 906419 := bstep (se 1 (by rfl) ⟨679814, by rfl⟩ : syracuseStep 906419 = 1359629) B1359629
theorem B1356995 : Blo 904575 1356995 := bstep (se 1 (by rfl) ⟨1017746, by rfl⟩ : syracuseStep 1356995 = 2035493) B2035493
theorem B906435 : Blo 904575 906435 := bstep (se 1 (by rfl) ⟨679826, by rfl⟩ : syracuseStep 906435 = 1359653) B1359653
theorem B906451 : Blo 904575 906451 := bstep (se 1 (by rfl) ⟨679838, by rfl⟩ : syracuseStep 906451 = 1359677) B1359677
theorem B1357025 : Blo 904575 1357025 := bstep (se 2 (by rfl) ⟨508884, by rfl⟩ : syracuseStep 1357025 = 1017769) B1017769
theorem B1529057 : Blo 904575 1529057 := bstep (se 2 (by rfl) ⟨573396, by rfl⟩ : syracuseStep 1529057 = 1146793) B1146793
theorem B906467 : Blo 904575 906467 := bstep (se 1 (by rfl) ⟨679850, by rfl⟩ : syracuseStep 906467 = 1359701) B1359701
theorem B1357043 : Blo 904575 1357043 := bstep (se 1 (by rfl) ⟨1017782, by rfl⟩ : syracuseStep 1357043 = 2035565) B2035565
theorem B906483 : Blo 904575 906483 := bstep (se 1 (by rfl) ⟨679862, by rfl⟩ : syracuseStep 906483 = 1359725) B1359725
theorem B906499 : Blo 904575 906499 := bstep (se 1 (by rfl) ⟨679874, by rfl⟩ : syracuseStep 906499 = 1359749) B1359749
theorem B1357073 : Blo 904575 1357073 := bstep (se 2 (by rfl) ⟨508902, by rfl⟩ : syracuseStep 1357073 = 1017805) B1017805
theorem B906515 : Blo 904575 906515 := bstep (se 1 (by rfl) ⟨679886, by rfl⟩ : syracuseStep 906515 = 1359773) B1359773
theorem B1357091 : Blo 904575 1357091 := bstep (se 1 (by rfl) ⟨1017818, by rfl⟩ : syracuseStep 1357091 = 2035637) B2035637
theorem B906531 : Blo 904575 906531 := bstep (se 1 (by rfl) ⟨679898, by rfl⟩ : syracuseStep 906531 = 1359797) B1359797
theorem B2037041 : Blo 904575 2037041 := bstep (se 2 (by rfl) ⟨763890, by rfl⟩ : syracuseStep 2037041 = 1527781) B1527781
theorem B3437873 : Blo 904575 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B906547 : Blo 904575 906547 := bstep (se 1 (by rfl) ⟨679910, by rfl⟩ : syracuseStep 906547 = 1359821) B1359821
theorem B1357121 : Blo 904575 1357121 := bstep (se 2 (by rfl) ⟨508920, by rfl⟩ : syracuseStep 1357121 = 1017841) B1017841
theorem B2037059 : Blo 904575 2037059 := bstep (se 1 (by rfl) ⟨1527794, by rfl⟩ : syracuseStep 2037059 = 3055589) B3055589
theorem B906563 : Blo 904575 906563 := bstep (se 1 (by rfl) ⟨679922, by rfl⟩ : syracuseStep 906563 = 1359845) B1359845
theorem B1357139 : Blo 904575 1357139 := bstep (se 1 (by rfl) ⟨1017854, by rfl⟩ : syracuseStep 1357139 = 2035709) B2035709
theorem B1529185 : Blo 904575 1529185 := bstep (se 2 (by rfl) ⟨573444, by rfl⟩ : syracuseStep 1529185 = 1146889) B1146889
theorem B1357169 : Blo 904575 1357169 := bstep (se 2 (by rfl) ⟨508938, by rfl⟩ : syracuseStep 1357169 = 1017877) B1017877
theorem B1357187 : Blo 904575 1357187 := bstep (se 1 (by rfl) ⟨1017890, by rfl⟩ : syracuseStep 1357187 = 2035781) B2035781
theorem B2291075 : Blo 904575 2291075 := bstep (se 1 (by rfl) ⟨1718306, by rfl⟩ : syracuseStep 2291075 = 3436613) B3436613
theorem B1529219 : Blo 904575 1529219 := bstep (se 1 (by rfl) ⟨1146914, by rfl⟩ : syracuseStep 1529219 = 2293829) B2293829
theorem B1357217 : Blo 904575 1357217 := bstep (se 2 (by rfl) ⟨508956, by rfl⟩ : syracuseStep 1357217 = 1017913) B1017913
theorem B1357235 : Blo 904575 1357235 := bstep (se 1 (by rfl) ⟨1017926, by rfl⟩ : syracuseStep 1357235 = 2035853) B2035853
theorem B1717699 : Blo 904575 1717699 := bstep (se 1 (by rfl) ⟨1288274, by rfl⟩ : syracuseStep 1717699 = 2576549) B2576549
theorem B1357265 : Blo 904575 1357265 := bstep (se 2 (by rfl) ⟨508974, by rfl⟩ : syracuseStep 1357265 = 1017949) B1017949
theorem B1357283 : Blo 904575 1357283 := bstep (se 1 (by rfl) ⟨1017962, by rfl⟩ : syracuseStep 1357283 = 2035925) B2035925
theorem B1103347 : Blo 904575 1103347 := bstep (se 1 (by rfl) ⟨827510, by rfl⟩ : syracuseStep 1103347 = 1655021) B1655021
theorem B1357313 : Blo 904575 1357313 := bstep (se 2 (by rfl) ⟨508992, by rfl⟩ : syracuseStep 1357313 = 1017985) B1017985
theorem B1529347 : Blo 904575 1529347 := bstep (se 1 (by rfl) ⟨1147010, by rfl⟩ : syracuseStep 1529347 = 2294021) B2294021
theorem B1357331 : Blo 904575 1357331 := bstep (se 1 (by rfl) ⟨1017998, by rfl⟩ : syracuseStep 1357331 = 2035997) B2035997
theorem B3053105 : Blo 904575 3053105 := bstep (se 2 (by rfl) ⟨1144914, by rfl⟩ : syracuseStep 3053105 = 2289829) B2289829
theorem B1357361 : Blo 904575 1357361 := bstep (se 2 (by rfl) ⟨509010, by rfl⟩ : syracuseStep 1357361 = 1018021) B1018021
theorem B4355633 : Blo 904575 4355633 := bstep (se 2 (by rfl) ⟨1633362, by rfl⟩ : syracuseStep 4355633 = 3266725) B3266725
theorem B1357379 : Blo 904575 1357379 := bstep (se 1 (by rfl) ⟨1018034, by rfl⟩ : syracuseStep 1357379 = 2036069) B2036069
theorem B2291267 : Blo 904575 2291267 := bstep (se 1 (by rfl) ⟨1718450, by rfl⟩ : syracuseStep 2291267 = 3436901) B3436901
theorem B2233937 : Blo 904575 2233937 := bstep (se 2 (by rfl) ⟨837726, by rfl⟩ : syracuseStep 2233937 = 1675453) B1675453
theorem B2037329 : Blo 904575 2037329 := bstep (se 2 (by rfl) ⟨763998, by rfl⟩ : syracuseStep 2037329 = 1527997) B1527997
theorem B1357409 : Blo 904575 1357409 := bstep (se 2 (by rfl) ⟨509028, by rfl⟩ : syracuseStep 1357409 = 1018057) B1018057
theorem B2037347 : Blo 904575 2037347 := bstep (se 1 (by rfl) ⟨1528010, by rfl⟩ : syracuseStep 2037347 = 3056021) B3056021
theorem B1357427 : Blo 904575 1357427 := bstep (se 1 (by rfl) ⟨1018070, by rfl⟩ : syracuseStep 1357427 = 2036141) B2036141
theorem B1357457 : Blo 904575 1357457 := bstep (se 2 (by rfl) ⟨509046, by rfl⟩ : syracuseStep 1357457 = 1018093) B1018093
theorem B1529489 : Blo 904575 1529489 := bstep (se 2 (by rfl) ⟨573558, by rfl⟩ : syracuseStep 1529489 = 1147117) B1147117
theorem B1357475 : Blo 904575 1357475 := bstep (se 1 (by rfl) ⟨1018106, by rfl⟩ : syracuseStep 1357475 = 2036213) B2036213
theorem B1357505 : Blo 904575 1357505 := bstep (se 2 (by rfl) ⟨509064, by rfl⟩ : syracuseStep 1357505 = 1018129) B1018129
theorem B1357523 : Blo 904575 1357523 := bstep (se 1 (by rfl) ⟨1018142, by rfl⟩ : syracuseStep 1357523 = 2036285) B2036285
theorem B1357553 : Blo 904575 1357553 := bstep (se 2 (by rfl) ⟨509082, by rfl⟩ : syracuseStep 1357553 = 1018165) B1018165
theorem B1357571 : Blo 904575 1357571 := bstep (se 1 (by rfl) ⟨1018178, by rfl⟩ : syracuseStep 1357571 = 2036357) B2036357
theorem B2578189 : Blo 904575 2578189 := bstep (se 3 (by rfl) ⟨483410, by rfl⟩ : syracuseStep 2578189 = 966821) B966821
theorem B1529617 : Blo 904575 1529617 := bstep (se 2 (by rfl) ⟨573606, by rfl⟩ : syracuseStep 1529617 = 1147213) B1147213
theorem B1357601 : Blo 904575 1357601 := bstep (se 2 (by rfl) ⟨509100, by rfl⟩ : syracuseStep 1357601 = 1018201) B1018201
theorem B1357619 : Blo 904575 1357619 := bstep (se 1 (by rfl) ⟨1018214, by rfl⟩ : syracuseStep 1357619 = 2036429) B2036429
theorem B1529651 : Blo 904575 1529651 := bstep (se 1 (by rfl) ⟨1147238, by rfl⟩ : syracuseStep 1529651 = 2294477) B2294477
theorem B1357649 : Blo 904575 1357649 := bstep (se 2 (by rfl) ⟨509118, by rfl⟩ : syracuseStep 1357649 = 1018237) B1018237
theorem B2324305 : Blo 904575 2324305 := bstep (se 2 (by rfl) ⟨871614, by rfl⟩ : syracuseStep 2324305 = 1743229) B1743229
theorem B1357667 : Blo 904575 1357667 := bstep (se 1 (by rfl) ⟨1018250, by rfl⟩ : syracuseStep 1357667 = 2036501) B2036501
theorem B4896611 : Blo 904575 4896611 := bstep (se 1 (by rfl) ⟨3672458, by rfl⟩ : syracuseStep 4896611 = 7344917) B7344917
theorem B2037617 : Blo 904575 2037617 := bstep (se 2 (by rfl) ⟨764106, by rfl⟩ : syracuseStep 2037617 = 1528213) B1528213
theorem B1357697 : Blo 904575 1357697 := bstep (se 2 (by rfl) ⟨509136, by rfl⟩ : syracuseStep 1357697 = 1018273) B1018273
theorem B1718147 : Blo 904575 1718147 := bstep (se 1 (by rfl) ⟨1288610, by rfl⟩ : syracuseStep 1718147 = 2577221) B2577221
theorem B2037635 : Blo 904575 2037635 := bstep (se 1 (by rfl) ⟨1528226, by rfl⟩ : syracuseStep 2037635 = 3056453) B3056453
theorem B4355981 : Blo 904575 4355981 := bstep (se 3 (by rfl) ⟨816746, by rfl⟩ : syracuseStep 4355981 = 1633493) B1633493
theorem B1357715 : Blo 904575 1357715 := bstep (se 1 (by rfl) ⟨1018286, by rfl⟩ : syracuseStep 1357715 = 2036573) B2036573
theorem B1357745 : Blo 904575 1357745 := bstep (se 2 (by rfl) ⟨509154, by rfl⟩ : syracuseStep 1357745 = 1018309) B1018309
theorem B1529779 : Blo 904575 1529779 := bstep (se 1 (by rfl) ⟨1147334, by rfl⟩ : syracuseStep 1529779 = 2294669) B2294669
theorem B1357763 : Blo 904575 1357763 := bstep (se 1 (by rfl) ⟨1018322, by rfl⟩ : syracuseStep 1357763 = 2036645) B2036645
theorem B1357793 : Blo 904575 1357793 := bstep (se 2 (by rfl) ⟨509172, by rfl⟩ : syracuseStep 1357793 = 1018345) B1018345
theorem B1357811 : Blo 904575 1357811 := bstep (se 1 (by rfl) ⟨1018358, by rfl⟩ : syracuseStep 1357811 = 2036717) B2036717
theorem B1357841 : Blo 904575 1357841 := bstep (se 2 (by rfl) ⟨509190, by rfl⟩ : syracuseStep 1357841 = 1018381) B1018381
theorem B1357859 : Blo 904575 1357859 := bstep (se 1 (by rfl) ⟨1018394, by rfl⟩ : syracuseStep 1357859 = 2036789) B2036789
theorem B1357889 : Blo 904575 1357889 := bstep (se 2 (by rfl) ⟨509208, by rfl⟩ : syracuseStep 1357889 = 1018417) B1018417
theorem B3053645 : Blo 904575 3053645 := bstep (se 3 (by rfl) ⟨572558, by rfl⟩ : syracuseStep 3053645 = 1145117) B1145117
theorem B1357907 : Blo 904575 1357907 := bstep (se 1 (by rfl) ⟨1018430, by rfl⟩ : syracuseStep 1357907 = 2036861) B2036861
theorem B4585571 : Blo 904575 4585571 := bstep (se 1 (by rfl) ⟨3439178, by rfl⟩ : syracuseStep 4585571 = 6878357) B6878357
theorem B1357937 : Blo 904575 1357937 := bstep (se 2 (by rfl) ⟨509226, by rfl⟩ : syracuseStep 1357937 = 1018453) B1018453
theorem B3053699 : Blo 904575 3053699 := bstep (se 1 (by rfl) ⟨2290274, by rfl⟩ : syracuseStep 3053699 = 4580549) B4580549
theorem B1357955 : Blo 904575 1357955 := bstep (se 1 (by rfl) ⟨1018466, by rfl⟩ : syracuseStep 1357955 = 2036933) B2036933
theorem B2037905 : Blo 904575 2037905 := bstep (se 2 (by rfl) ⟨764214, by rfl⟩ : syracuseStep 2037905 = 1528429) B1528429
theorem B1357985 : Blo 904575 1357985 := bstep (se 2 (by rfl) ⟨509244, by rfl⟩ : syracuseStep 1357985 = 1018489) B1018489
theorem B1718435 : Blo 904575 1718435 := bstep (se 1 (by rfl) ⟨1288826, by rfl⟩ : syracuseStep 1718435 = 2577653) B2577653
theorem B2037923 : Blo 904575 2037923 := bstep (se 1 (by rfl) ⟨1528442, by rfl⟩ : syracuseStep 2037923 = 3056885) B3056885
theorem B1145011 : Blo 904575 1145011 := bstep (se 1 (by rfl) ⟨858758, by rfl⟩ : syracuseStep 1145011 = 1717517) B1717517
theorem B1358003 : Blo 904575 1358003 := bstep (se 1 (by rfl) ⟨1018502, by rfl⟩ : syracuseStep 1358003 = 2037005) B2037005
theorem B10303685 : Blo 904575 10303685 := bstep (se 4 (by rfl) ⟨965970, by rfl⟩ : syracuseStep 10303685 = 1931941) B1931941
theorem B1358033 : Blo 904575 1358033 := bstep (se 2 (by rfl) ⟨509262, by rfl⟩ : syracuseStep 1358033 = 1018525) B1018525
theorem B1358051 : Blo 904575 1358051 := bstep (se 1 (by rfl) ⟨1018538, by rfl⟩ : syracuseStep 1358051 = 2037077) B2037077
theorem B1358081 : Blo 904575 1358081 := bstep (se 2 (by rfl) ⟨509280, by rfl⟩ : syracuseStep 1358081 = 1018561) B1018561
theorem B1145107 : Blo 904575 1145107 := bstep (se 1 (by rfl) ⟨858830, by rfl⟩ : syracuseStep 1145107 = 1717661) B1717661
theorem B1358099 : Blo 904575 1358099 := bstep (se 1 (by rfl) ⟨1018574, by rfl⟩ : syracuseStep 1358099 = 2037149) B2037149
theorem B1358129 : Blo 904575 1358129 := bstep (se 2 (by rfl) ⟨509298, by rfl⟩ : syracuseStep 1358129 = 1018597) B1018597
theorem B1358147 : Blo 904575 1358147 := bstep (se 1 (by rfl) ⟨1018610, by rfl⟩ : syracuseStep 1358147 = 2037221) B2037221
theorem B1358177 : Blo 904575 1358177 := bstep (se 2 (by rfl) ⟨509316, by rfl⟩ : syracuseStep 1358177 = 1018633) B1018633
theorem B1358195 : Blo 904575 1358195 := bstep (se 1 (by rfl) ⟨1018646, by rfl⟩ : syracuseStep 1358195 = 2037293) B2037293
theorem B2750851 : Blo 904575 2750851 := bstep (se 1 (by rfl) ⟨2063138, by rfl⟩ : syracuseStep 2750851 = 4126277) B4126277
theorem B3053969 : Blo 904575 3053969 := bstep (se 2 (by rfl) ⟨1145238, by rfl⟩ : syracuseStep 3053969 = 2290477) B2290477
theorem B1358225 : Blo 904575 1358225 := bstep (se 2 (by rfl) ⟨509334, by rfl⟩ : syracuseStep 1358225 = 1018669) B1018669
theorem B1358243 : Blo 904575 1358243 := bstep (se 1 (by rfl) ⟨1018682, by rfl⟩ : syracuseStep 1358243 = 2037365) B2037365
theorem B2038193 : Blo 904575 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B1358273 : Blo 904575 1358273 := bstep (se 2 (by rfl) ⟨509352, by rfl⟩ : syracuseStep 1358273 = 1018705) B1018705
theorem B2038211 : Blo 904575 2038211 := bstep (se 1 (by rfl) ⟨1528658, by rfl⟩ : syracuseStep 2038211 = 3057317) B3057317
theorem B7346629 : Blo 904575 7346629 := bstep (se 4 (by rfl) ⟨688746, by rfl⟩ : syracuseStep 7346629 = 1377493) B1377493
theorem B2513357 : Blo 904575 2513357 := bstep (se 3 (by rfl) ⟨471254, by rfl⟩ : syracuseStep 2513357 = 942509) B942509
theorem B1358291 : Blo 904575 1358291 := bstep (se 1 (by rfl) ⟨1018718, by rfl⟩ : syracuseStep 1358291 = 2037437) B2037437
theorem B2898413 : Blo 904575 2898413 := bstep (se 3 (by rfl) ⟨543452, by rfl⟩ : syracuseStep 2898413 = 1086905) B1086905
theorem B1358321 : Blo 904575 1358321 := bstep (se 2 (by rfl) ⟨509370, by rfl⟩ : syracuseStep 1358321 = 1018741) B1018741
theorem B2292209 : Blo 904575 2292209 := bstep (se 2 (by rfl) ⟨859578, by rfl⟩ : syracuseStep 2292209 = 1719157) B1719157
theorem B1358339 : Blo 904575 1358339 := bstep (se 1 (by rfl) ⟨1018754, by rfl⟩ : syracuseStep 1358339 = 2037509) B2037509
theorem B1358369 : Blo 904575 1358369 := bstep (se 2 (by rfl) ⟨509388, by rfl⟩ : syracuseStep 1358369 = 1018777) B1018777
theorem B2292259 : Blo 904575 2292259 := bstep (se 1 (by rfl) ⟨1719194, by rfl⟩ : syracuseStep 2292259 = 3438389) B3438389
theorem B2095651 : Blo 904575 2095651 := bstep (se 1 (by rfl) ⟨1571738, by rfl⟩ : syracuseStep 2095651 = 3143477) B3143477
theorem B1358387 : Blo 904575 1358387 := bstep (se 1 (by rfl) ⟨1018790, by rfl⟩ : syracuseStep 1358387 = 2037581) B2037581
theorem B1358417 : Blo 904575 1358417 := bstep (se 2 (by rfl) ⟨509406, by rfl⟩ : syracuseStep 1358417 = 1018813) B1018813
theorem B1358435 : Blo 904575 1358435 := bstep (se 1 (by rfl) ⟨1018826, by rfl⟩ : syracuseStep 1358435 = 2037653) B2037653
theorem B5806691 : Blo 904575 5806691 := bstep (se 1 (by rfl) ⟨4355018, by rfl⟩ : syracuseStep 5806691 = 8710037) B8710037
theorem B1358465 : Blo 904575 1358465 := bstep (se 2 (by rfl) ⟨509424, by rfl⟩ : syracuseStep 1358465 = 1018849) B1018849
theorem B1358483 : Blo 904575 1358483 := bstep (se 1 (by rfl) ⟨1018862, by rfl⟩ : syracuseStep 1358483 = 2037725) B2037725
theorem B2292401 : Blo 904575 2292401 := bstep (se 2 (by rfl) ⟨859650, by rfl⟩ : syracuseStep 2292401 = 1719301) B1719301
theorem B1358513 : Blo 904575 1358513 := bstep (se 2 (by rfl) ⟨509442, by rfl⟩ : syracuseStep 1358513 = 1018885) B1018885
theorem B1358531 : Blo 904575 1358531 := bstep (se 1 (by rfl) ⟨1018898, by rfl⟩ : syracuseStep 1358531 = 2037797) B2037797
theorem B2038481 : Blo 904575 2038481 := bstep (se 2 (by rfl) ⟨764430, by rfl⟩ : syracuseStep 2038481 = 1528861) B1528861
theorem B1358561 : Blo 904575 1358561 := bstep (se 2 (by rfl) ⟨509460, by rfl⟩ : syracuseStep 1358561 = 1018921) B1018921
theorem B3439331 : Blo 904575 3439331 := bstep (se 1 (by rfl) ⟨2579498, by rfl⟩ : syracuseStep 3439331 = 5158997) B5158997
theorem B2038499 : Blo 904575 2038499 := bstep (se 1 (by rfl) ⟨1528874, by rfl⟩ : syracuseStep 2038499 = 3057749) B3057749
theorem B10312433 : Blo 904575 10312433 := bstep (se 2 (by rfl) ⟨3867162, by rfl⟩ : syracuseStep 10312433 = 7734325) B7734325
theorem B1358579 : Blo 904575 1358579 := bstep (se 1 (by rfl) ⟨1018934, by rfl⟩ : syracuseStep 1358579 = 2037869) B2037869
theorem B1145603 : Blo 904575 1145603 := bstep (se 1 (by rfl) ⟨859202, by rfl⟩ : syracuseStep 1145603 = 1718405) B1718405
theorem B1358609 : Blo 904575 1358609 := bstep (se 2 (by rfl) ⟨509478, by rfl⟩ : syracuseStep 1358609 = 1018957) B1018957
theorem B1358627 : Blo 904575 1358627 := bstep (se 1 (by rfl) ⟨1018970, by rfl⟩ : syracuseStep 1358627 = 2037941) B2037941
theorem B1358657 : Blo 904575 1358657 := bstep (se 2 (by rfl) ⟨509496, by rfl⟩ : syracuseStep 1358657 = 1018993) B1018993
theorem B3865421 : Blo 904575 3865421 := bstep (se 3 (by rfl) ⟨724766, by rfl⟩ : syracuseStep 3865421 = 1449533) B1449533
theorem B1932113 : Blo 904575 1932113 := bstep (se 2 (by rfl) ⟨724542, by rfl⟩ : syracuseStep 1932113 = 1449085) B1449085
theorem B1358675 : Blo 904575 1358675 := bstep (se 1 (by rfl) ⟨1019006, by rfl⟩ : syracuseStep 1358675 = 2038013) B2038013
theorem B2448227 : Blo 904575 2448227 := bstep (se 1 (by rfl) ⟨1836170, by rfl⟩ : syracuseStep 2448227 = 3672341) B3672341
theorem B1358705 : Blo 904575 1358705 := bstep (se 2 (by rfl) ⟨509514, by rfl⟩ : syracuseStep 1358705 = 1019029) B1019029
theorem B1358723 : Blo 904575 1358723 := bstep (se 1 (by rfl) ⟨1019042, by rfl⟩ : syracuseStep 1358723 = 2038085) B2038085
theorem B4586381 : Blo 904575 4586381 := bstep (se 3 (by rfl) ⟨859946, by rfl⟩ : syracuseStep 4586381 = 1719893) B1719893
theorem B1358753 : Blo 904575 1358753 := bstep (se 2 (by rfl) ⟨509532, by rfl⟩ : syracuseStep 1358753 = 1019065) B1019065
theorem B3054509 : Blo 904575 3054509 := bstep (se 3 (by rfl) ⟨572720, by rfl⟩ : syracuseStep 3054509 = 1145441) B1145441
theorem B1358771 : Blo 904575 1358771 := bstep (se 1 (by rfl) ⟨1019078, by rfl⟩ : syracuseStep 1358771 = 2038157) B2038157
theorem B1358801 : Blo 904575 1358801 := bstep (se 2 (by rfl) ⟨509550, by rfl⟩ : syracuseStep 1358801 = 1019101) B1019101
theorem B3054563 : Blo 904575 3054563 := bstep (se 1 (by rfl) ⟨2290922, by rfl⟩ : syracuseStep 3054563 = 4581845) B4581845
theorem B1358819 : Blo 904575 1358819 := bstep (se 1 (by rfl) ⟨1019114, by rfl⟩ : syracuseStep 1358819 = 2038229) B2038229
theorem B2038769 : Blo 904575 2038769 := bstep (se 2 (by rfl) ⟨764538, by rfl⟩ : syracuseStep 2038769 = 1529077) B1529077
theorem B1358849 : Blo 904575 1358849 := bstep (se 2 (by rfl) ⟨509568, by rfl⟩ : syracuseStep 1358849 = 1019137) B1019137
theorem B2038787 : Blo 904575 2038787 := bstep (se 1 (by rfl) ⟨1529090, by rfl⟩ : syracuseStep 2038787 = 3058181) B3058181
theorem B4709389 : Blo 904575 4709389 := bstep (se 3 (by rfl) ⟨883010, by rfl⟩ : syracuseStep 4709389 = 1766021) B1766021
theorem B1358867 : Blo 904575 1358867 := bstep (se 1 (by rfl) ⟨1019150, by rfl⟩ : syracuseStep 1358867 = 2038301) B2038301
theorem B1358897 : Blo 904575 1358897 := bstep (se 2 (by rfl) ⟨509586, by rfl⟩ : syracuseStep 1358897 = 1019173) B1019173
theorem B5807153 : Blo 904575 5807153 := bstep (se 2 (by rfl) ⟨2177682, by rfl⟩ : syracuseStep 5807153 = 4355365) B4355365
theorem B1358915 : Blo 904575 1358915 := bstep (se 1 (by rfl) ⟨1019186, by rfl⟩ : syracuseStep 1358915 = 2038373) B2038373
theorem B1719377 : Blo 904575 1719377 := bstep (se 2 (by rfl) ⟨644766, by rfl⟩ : syracuseStep 1719377 = 1289533) B1289533
theorem B1358945 : Blo 904575 1358945 := bstep (se 2 (by rfl) ⟨509604, by rfl⟩ : syracuseStep 1358945 = 1019209) B1019209
theorem B1358963 : Blo 904575 1358963 := bstep (se 1 (by rfl) ⟨1019222, by rfl⟩ : syracuseStep 1358963 = 2038445) B2038445
theorem B1358993 : Blo 904575 1358993 := bstep (se 2 (by rfl) ⟨509622, by rfl⟩ : syracuseStep 1358993 = 1019245) B1019245
theorem B1359011 : Blo 904575 1359011 := bstep (se 1 (by rfl) ⟨1019258, by rfl⟩ : syracuseStep 1359011 = 2038517) B2038517
theorem B1359041 : Blo 904575 1359041 := bstep (se 2 (by rfl) ⟨509640, by rfl⟩ : syracuseStep 1359041 = 1019281) B1019281
theorem B1834193 : Blo 904575 1834193 := bstep (se 2 (by rfl) ⟨687822, by rfl⟩ : syracuseStep 1834193 = 1375645) B1375645
theorem B1359059 : Blo 904575 1359059 := bstep (se 1 (by rfl) ⟨1019294, by rfl⟩ : syracuseStep 1359059 = 2038589) B2038589
theorem B1547491 : Blo 904575 1547491 := bstep (se 1 (by rfl) ⟨1160618, by rfl⟩ : syracuseStep 1547491 = 2321237) B2321237
theorem B3054833 : Blo 904575 3054833 := bstep (se 2 (by rfl) ⟨1145562, by rfl⟩ : syracuseStep 3054833 = 2291125) B2291125
theorem B1359089 : Blo 904575 1359089 := bstep (se 2 (by rfl) ⟨509658, by rfl⟩ : syracuseStep 1359089 = 1019317) B1019317
theorem B1359107 : Blo 904575 1359107 := bstep (se 1 (by rfl) ⟨1019330, by rfl⟩ : syracuseStep 1359107 = 2038661) B2038661
theorem B2039057 : Blo 904575 2039057 := bstep (se 2 (by rfl) ⟨764646, by rfl⟩ : syracuseStep 2039057 = 1529293) B1529293
theorem B1359137 : Blo 904575 1359137 := bstep (se 2 (by rfl) ⟨509676, by rfl⟩ : syracuseStep 1359137 = 1019353) B1019353
theorem B2039075 : Blo 904575 2039075 := bstep (se 1 (by rfl) ⟨1529306, by rfl⟩ : syracuseStep 2039075 = 3058613) B3058613
theorem B1359155 : Blo 904575 1359155 := bstep (se 1 (by rfl) ⟨1019366, by rfl⟩ : syracuseStep 1359155 = 2038733) B2038733
theorem B1359185 : Blo 904575 1359185 := bstep (se 2 (by rfl) ⟨509694, by rfl⟩ : syracuseStep 1359185 = 1019389) B1019389
theorem B1088851 : Blo 904575 1088851 := bstep (se 1 (by rfl) ⟨816638, by rfl⟩ : syracuseStep 1088851 = 1633277) B1633277
theorem B1359203 : Blo 904575 1359203 := bstep (se 1 (by rfl) ⟨1019402, by rfl⟩ : syracuseStep 1359203 = 2038805) B2038805
theorem B1359233 : Blo 904575 1359233 := bstep (se 2 (by rfl) ⟨509712, by rfl⟩ : syracuseStep 1359233 = 1019425) B1019425
theorem B1359251 : Blo 904575 1359251 := bstep (se 1 (by rfl) ⟨1019438, by rfl⟩ : syracuseStep 1359251 = 2038877) B2038877
theorem B1359281 : Blo 904575 1359281 := bstep (se 2 (by rfl) ⟨509730, by rfl⟩ : syracuseStep 1359281 = 1019461) B1019461
theorem B1088947 : Blo 904575 1088947 := bstep (se 1 (by rfl) ⟨816710, by rfl⟩ : syracuseStep 1088947 = 1633421) B1633421
theorem B1146307 : Blo 904575 1146307 := bstep (se 1 (by rfl) ⟨859730, by rfl⟩ : syracuseStep 1146307 = 1719461) B1719461
theorem B1359299 : Blo 904575 1359299 := bstep (se 1 (by rfl) ⟨1019474, by rfl⟩ : syracuseStep 1359299 = 2038949) B2038949
theorem B2579921 : Blo 904575 2579921 := bstep (se 2 (by rfl) ⟨967470, by rfl⟩ : syracuseStep 2579921 = 1934941) B1934941
theorem B1359329 : Blo 904575 1359329 := bstep (se 2 (by rfl) ⟨509748, by rfl⟩ : syracuseStep 1359329 = 1019497) B1019497
theorem B1359347 : Blo 904575 1359347 := bstep (se 1 (by rfl) ⟨1019510, by rfl⟩ : syracuseStep 1359347 = 2039021) B2039021
theorem B1359377 : Blo 904575 1359377 := bstep (se 2 (by rfl) ⟨509766, by rfl⟩ : syracuseStep 1359377 = 1019533) B1019533
theorem B1146403 : Blo 904575 1146403 := bstep (se 1 (by rfl) ⟨859802, by rfl⟩ : syracuseStep 1146403 = 1719605) B1719605
theorem B1359395 : Blo 904575 1359395 := bstep (se 1 (by rfl) ⟨1019546, by rfl⟩ : syracuseStep 1359395 = 2039093) B2039093
theorem B2039345 : Blo 904575 2039345 := bstep (se 2 (by rfl) ⟨764754, by rfl⟩ : syracuseStep 2039345 = 1529509) B1529509
theorem B1359425 : Blo 904575 1359425 := bstep (se 2 (by rfl) ⟨509784, by rfl⟩ : syracuseStep 1359425 = 1019569) B1019569
theorem B2039363 : Blo 904575 2039363 := bstep (se 1 (by rfl) ⟨1529522, by rfl⟩ : syracuseStep 2039363 = 3059045) B3059045
theorem B966227 : Blo 904575 966227 := bstep (se 1 (by rfl) ⟨724670, by rfl⟩ : syracuseStep 966227 = 1449341) B1449341
theorem B1359443 : Blo 904575 1359443 := bstep (se 1 (by rfl) ⟨1019582, by rfl⟩ : syracuseStep 1359443 = 2039165) B2039165
theorem B1359473 : Blo 904575 1359473 := bstep (se 2 (by rfl) ⟨509802, by rfl⟩ : syracuseStep 1359473 = 1019605) B1019605
theorem B1359491 : Blo 904575 1359491 := bstep (se 1 (by rfl) ⟨1019618, by rfl⟩ : syracuseStep 1359491 = 2039237) B2039237
theorem B2293393 : Blo 904575 2293393 := bstep (se 2 (by rfl) ⟨860022, by rfl⟩ : syracuseStep 2293393 = 1720045) B1720045
theorem B2580113 : Blo 904575 2580113 := bstep (se 2 (by rfl) ⟨967542, by rfl⟩ : syracuseStep 2580113 = 1935085) B1935085
theorem B1359521 : Blo 904575 1359521 := bstep (se 2 (by rfl) ⟨509820, by rfl⟩ : syracuseStep 1359521 = 1019641) B1019641
theorem B1359539 : Blo 904575 1359539 := bstep (se 1 (by rfl) ⟨1019654, by rfl⟩ : syracuseStep 1359539 = 2039309) B2039309
theorem B1375937 : Blo 904575 1375937 := bstep (se 2 (by rfl) ⟨515976, by rfl⟩ : syracuseStep 1375937 = 1031953) B1031953
theorem B3440333 : Blo 904575 3440333 := bstep (se 3 (by rfl) ⟨645062, by rfl⟩ : syracuseStep 3440333 = 1290125) B1290125
theorem B1359569 : Blo 904575 1359569 := bstep (se 2 (by rfl) ⟨509838, by rfl⟩ : syracuseStep 1359569 = 1019677) B1019677
theorem B4898531 : Blo 904575 4898531 := bstep (se 1 (by rfl) ⟨3673898, by rfl⟩ : syracuseStep 4898531 = 7347797) B7347797
theorem B1359587 : Blo 904575 1359587 := bstep (se 1 (by rfl) ⟨1019690, by rfl⟩ : syracuseStep 1359587 = 2039381) B2039381
theorem B2752237 : Blo 904575 2752237 := bstep (se 3 (by rfl) ⟨516044, by rfl⟩ : syracuseStep 2752237 = 1032089) B1032089
theorem B1359617 : Blo 904575 1359617 := bstep (se 2 (by rfl) ⟨509856, by rfl⟩ : syracuseStep 1359617 = 1019713) B1019713
theorem B3055373 : Blo 904575 3055373 := bstep (se 3 (by rfl) ⟨572882, by rfl⟩ : syracuseStep 3055373 = 1145765) B1145765
theorem B1359635 : Blo 904575 1359635 := bstep (se 1 (by rfl) ⟨1019726, by rfl⟩ : syracuseStep 1359635 = 2039453) B2039453
theorem B2899757 : Blo 904575 2899757 := bstep (se 3 (by rfl) ⟨543704, by rfl⟩ : syracuseStep 2899757 = 1087409) B1087409
theorem B2449201 : Blo 904575 2449201 := bstep (se 2 (by rfl) ⟨918450, by rfl⟩ : syracuseStep 2449201 = 1836901) B1836901
theorem B1359665 : Blo 904575 1359665 := bstep (se 2 (by rfl) ⟨509874, by rfl⟩ : syracuseStep 1359665 = 1019749) B1019749
theorem B3055427 : Blo 904575 3055427 := bstep (se 1 (by rfl) ⟨2291570, by rfl⟩ : syracuseStep 3055427 = 4583141) B4583141
theorem B1359683 : Blo 904575 1359683 := bstep (se 1 (by rfl) ⟨1019762, by rfl⟩ : syracuseStep 1359683 = 2039525) B2039525
theorem B5160773 : Blo 904575 5160773 := bstep (se 4 (by rfl) ⟨483822, by rfl⟩ : syracuseStep 5160773 = 967645) B967645
theorem B2039633 : Blo 904575 2039633 := bstep (se 2 (by rfl) ⟨764862, by rfl⟩ : syracuseStep 2039633 = 1529725) B1529725
theorem B1359713 : Blo 904575 1359713 := bstep (se 2 (by rfl) ⟨509892, by rfl⟩ : syracuseStep 1359713 = 1019785) B1019785
theorem B2039651 : Blo 904575 2039651 := bstep (se 1 (by rfl) ⟨1529738, by rfl⟩ : syracuseStep 2039651 = 3059477) B3059477
theorem B1449841 : Blo 904575 1449841 := bstep (se 2 (by rfl) ⟨543690, by rfl⟩ : syracuseStep 1449841 = 1087381) B1087381
theorem B1359731 : Blo 904575 1359731 := bstep (se 1 (by rfl) ⟨1019798, by rfl⟩ : syracuseStep 1359731 = 2039597) B2039597
theorem B1359761 : Blo 904575 1359761 := bstep (se 2 (by rfl) ⟨509910, by rfl⟩ : syracuseStep 1359761 = 1019821) B1019821
theorem B2293667 : Blo 904575 2293667 := bstep (se 1 (by rfl) ⟨1720250, by rfl⟩ : syracuseStep 2293667 = 3440501) B3440501
theorem B1359779 : Blo 904575 1359779 := bstep (se 1 (by rfl) ⟨1019834, by rfl⟩ : syracuseStep 1359779 = 2039669) B2039669
theorem B1359809 : Blo 904575 1359809 := bstep (se 2 (by rfl) ⟨509928, by rfl⟩ : syracuseStep 1359809 = 1019857) B1019857
theorem B1720273 : Blo 904575 1720273 := bstep (se 2 (by rfl) ⟨645102, by rfl⟩ : syracuseStep 1720273 = 1290205) B1290205
theorem B1359827 : Blo 904575 1359827 := bstep (se 1 (by rfl) ⟨1019870, by rfl⟩ : syracuseStep 1359827 = 2039741) B2039741
theorem B11608049 : Blo 904575 11608049 := bstep (se 2 (by rfl) ⟨4353018, by rfl⟩ : syracuseStep 11608049 = 8706037) B8706037
theorem B1359857 : Blo 904575 1359857 := bstep (se 2 (by rfl) ⟨509946, by rfl⟩ : syracuseStep 1359857 = 1019893) B1019893
theorem B1146955 : Blo 904575 1146955 := bstep (se 1 (by rfl) ⟨860216, by rfl⟩ : syracuseStep 1146955 = 1720433) B1720433
theorem B2580569 : Blo 904575 2580569 := bstep (se 2 (by rfl) ⟨967713, by rfl⟩ : syracuseStep 2580569 = 1935427) B1935427
theorem B1933463 : Blo 904575 1933463 := bstep (se 1 (by rfl) ⟨1450097, by rfl⟩ : syracuseStep 1933463 = 2900195) B2900195
theorem B3440819 : Blo 904575 3440819 := bstep (se 1 (by rfl) ⟨2580614, by rfl⟩ : syracuseStep 3440819 = 5161229) B5161229
theorem B5808307 : Blo 904575 5808307 := bstep (se 1 (by rfl) ⟨4356230, by rfl⟩ : syracuseStep 5808307 = 8712461) B8712461
theorem B966859 : Blo 904575 966859 := bstep (se 1 (by rfl) ⟨725144, by rfl⟩ : syracuseStep 966859 = 1450289) B1450289
theorem B2064599 : Blo 904575 2064599 := bstep (se 1 (by rfl) ⟨1548449, by rfl⟩ : syracuseStep 2064599 = 3096899) B3096899
theorem B1720577 : Blo 904575 1720577 := bstep (se 2 (by rfl) ⟨645216, by rfl⟩ : syracuseStep 1720577 = 1290433) B1290433
theorem B27885869 : Blo 904575 27885869 := bstep (se 3 (by rfl) ⟨5228600, by rfl⟩ : syracuseStep 27885869 = 10457201) B10457201
theorem B1450315 : Blo 904575 1450315 := bstep (se 1 (by rfl) ⟨1087736, by rfl⟩ : syracuseStep 1450315 = 2175473) B2175473
theorem B1147223 : Blo 904575 1147223 := bstep (se 1 (by rfl) ⟨860417, by rfl⟩ : syracuseStep 1147223 = 1720835) B1720835
theorem B3867011 : Blo 904575 3867011 := bstep (se 1 (by rfl) ⟨2900258, by rfl⟩ : syracuseStep 3867011 = 5800517) B5800517
theorem B1450391 : Blo 904575 1450391 := bstep (se 1 (by rfl) ⟨1087793, by rfl⟩ : syracuseStep 1450391 = 2175587) B2175587
theorem B3056075 : Blo 904575 3056075 := bstep (se 1 (by rfl) ⟨2292056, by rfl⟩ : syracuseStep 3056075 = 4584113) B4584113
theorem B1720919 : Blo 904575 1720919 := bstep (se 1 (by rfl) ⟨1290689, by rfl⟩ : syracuseStep 1720919 = 2581379) B2581379
theorem B4588163 : Blo 904575 4588163 := bstep (se 1 (by rfl) ⟨3441122, by rfl⟩ : syracuseStep 4588163 = 6882245) B6882245
theorem B3670721 : Blo 904575 3670721 := bstep (se 2 (by rfl) ⟨1376520, by rfl⟩ : syracuseStep 3670721 = 2753041) B2753041
theorem B3056345 : Blo 904575 3056345 := bstep (se 2 (by rfl) ⟨1146129, by rfl⟩ : syracuseStep 3056345 = 2292259) B2292259
theorem B2794201 : Blo 904575 2794201 := bstep (se 2 (by rfl) ⟨1047825, by rfl⟩ : syracuseStep 2794201 = 2095651) B2095651
theorem B3441473 : Blo 904575 3441473 := bstep (se 2 (by rfl) ⟨1290552, by rfl⟩ : syracuseStep 3441473 = 2581105) B2581105
theorem B6800203 : Blo 904575 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B1655795 : Blo 904575 1655795 := bstep (se 1 (by rfl) ⟨1241846, by rfl⟩ : syracuseStep 1655795 = 2483693) B2483693
theorem B3097651 : Blo 904575 3097651 := bstep (se 1 (by rfl) ⟨2323238, by rfl⟩ : syracuseStep 3097651 = 4646477) B4646477
theorem B967799 : Blo 904575 967799 := bstep (se 1 (by rfl) ⟨725849, by rfl⟩ : syracuseStep 967799 = 1451699) B1451699
theorem B4408499 : Blo 904575 4408499 := bstep (se 1 (by rfl) ⟨3306374, by rfl⟩ : syracuseStep 4408499 = 6612749) B6612749
theorem B6874469 : Blo 904575 6874469 := bstep (se 4 (by rfl) ⟨644481, by rfl⟩ : syracuseStep 6874469 = 1288963) B1288963
theorem B3057047 : Blo 904575 3057047 := bstep (se 1 (by rfl) ⟨2292785, by rfl⟩ : syracuseStep 3057047 = 4585571) B4585571
theorem B2901527 : Blo 904575 2901527 := bstep (se 1 (by rfl) ⟨2176145, by rfl⟩ : syracuseStep 2901527 = 4352291) B4352291
theorem B12396293 : Blo 904575 12396293 := bstep (se 4 (by rfl) ⟨1162152, by rfl⟩ : syracuseStep 12396293 = 2324305) B2324305
theorem B1451801 : Blo 904575 1451801 := bstep (se 2 (by rfl) ⟨544425, by rfl⟩ : syracuseStep 1451801 = 1088851) B1088851
theorem B6874955 : Blo 904575 6874955 := bstep (se 1 (by rfl) ⟨5156216, by rfl⟩ : syracuseStep 6874955 = 10312433) B10312433
theorem B1288075 : Blo 904575 1288075 := bstep (se 1 (by rfl) ⟨966056, by rfl⟩ : syracuseStep 1288075 = 1932113) B1932113
theorem B1017751 : Blo 904575 1017751 := bstep (se 1 (by rfl) ⟨763313, by rfl⟩ : syracuseStep 1017751 = 1526627) B1526627
theorem B1451929 : Blo 904575 1451929 := bstep (se 2 (by rfl) ⟨544473, by rfl⟩ : syracuseStep 1451929 = 1088947) B1088947
theorem B3057587 : Blo 904575 3057587 := bstep (se 1 (by rfl) ⟨2293190, by rfl⟩ : syracuseStep 3057587 = 4586381) B4586381
theorem B6195217 : Blo 904575 6195217 := bstep (se 2 (by rfl) ⟨2323206, by rfl⟩ : syracuseStep 6195217 = 4646413) B4646413
theorem B5802029 : Blo 904575 5802029 := bstep (se 3 (by rfl) ⟨1087880, by rfl⟩ : syracuseStep 5802029 = 2175761) B2175761
theorem B4909121 : Blo 904575 4909121 := bstep (se 2 (by rfl) ⟨1840920, by rfl⟩ : syracuseStep 4909121 = 3681841) B3681841
theorem B1017931 : Blo 904575 1017931 := bstep (se 1 (by rfl) ⟨763448, by rfl⟩ : syracuseStep 1017931 = 1526897) B1526897
theorem B4130947 : Blo 904575 4130947 := bstep (se 1 (by rfl) ⟨3098210, by rfl⟩ : syracuseStep 4130947 = 6196421) B6196421
theorem B1222795 : Blo 904575 1222795 := bstep (se 1 (by rfl) ⟨917096, by rfl⟩ : syracuseStep 1222795 = 1834193) B1834193
theorem B3434669 : Blo 904575 3434669 := bstep (se 3 (by rfl) ⟨644000, by rfl⟩ : syracuseStep 3434669 = 1288001) B1288001
theorem B1018039 : Blo 904575 1018039 := bstep (se 1 (by rfl) ⟨763529, by rfl⟩ : syracuseStep 1018039 = 1527059) B1527059
theorem B3057857 : Blo 904575 3057857 := bstep (se 2 (by rfl) ⟨1146696, by rfl⟩ : syracuseStep 3057857 = 2293393) B2293393
theorem B5507345 : Blo 904575 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B6195521 : Blo 904575 6195521 := bstep (se 2 (by rfl) ⟨2323320, by rfl⟩ : syracuseStep 6195521 = 4646641) B4646641
theorem B1018219 : Blo 904575 1018219 := bstep (se 1 (by rfl) ⟨763664, by rfl⟩ : syracuseStep 1018219 = 1527329) B1527329
theorem B1018327 : Blo 904575 1018327 := bstep (se 1 (by rfl) ⟨763745, by rfl⟩ : syracuseStep 1018327 = 1527491) B1527491
theorem B1018507 : Blo 904575 1018507 := bstep (se 1 (by rfl) ⟨763880, by rfl⟩ : syracuseStep 1018507 = 1527761) B1527761
theorem B3058397 : Blo 904575 3058397 := bstep (se 3 (by rfl) ⟨573449, by rfl⟩ : syracuseStep 3058397 = 1146899) B1146899
theorem B1018615 : Blo 904575 1018615 := bstep (se 1 (by rfl) ⟨763961, by rfl⟩ : syracuseStep 1018615 = 1527923) B1527923
theorem B1526539 : Blo 904575 1526539 := bstep (se 1 (by rfl) ⟨1144904, by rfl⟩ : syracuseStep 1526539 = 2289809) B2289809
theorem B4131607 : Blo 904575 4131607 := bstep (se 1 (by rfl) ⟨3098705, by rfl⟩ : syracuseStep 4131607 = 6197411) B6197411
theorem B5155649 : Blo 904575 5155649 := bstep (se 2 (by rfl) ⟨1933368, by rfl⟩ : syracuseStep 5155649 = 3866737) B3866737
theorem B6884189 : Blo 904575 6884189 := bstep (se 3 (by rfl) ⟨1290785, by rfl⟩ : syracuseStep 6884189 = 2581571) B2581571
theorem B1526681 : Blo 904575 1526681 := bstep (se 2 (by rfl) ⟨572505, by rfl⟩ : syracuseStep 1526681 = 1145011) B1145011
theorem B1018795 : Blo 904575 1018795 := bstep (se 1 (by rfl) ⟨764096, by rfl⟩ : syracuseStep 1018795 = 1528193) B1528193
theorem B3435443 : Blo 904575 3435443 := bstep (se 1 (by rfl) ⟨2576582, by rfl⟩ : syracuseStep 3435443 = 5153165) B5153165
theorem B1633241 : Blo 904575 1633241 := bstep (se 2 (by rfl) ⟨612465, by rfl⟩ : syracuseStep 1633241 = 1224931) B1224931
theorem B1018903 : Blo 904575 1018903 := bstep (se 1 (by rfl) ⟨764177, by rfl⟩ : syracuseStep 1018903 = 1528355) B1528355
theorem B1526809 : Blo 904575 1526809 := bstep (se 2 (by rfl) ⟨572553, by rfl⟩ : syracuseStep 1526809 = 1145107) B1145107
theorem B1289305 : Blo 904575 1289305 := bstep (se 2 (by rfl) ⟨483489, by rfl⟩ : syracuseStep 1289305 = 966979) B966979
theorem B4582493 : Blo 904575 4582493 := bstep (se 3 (by rfl) ⟨859217, by rfl⟩ : syracuseStep 4582493 = 1718435) B1718435
theorem B1019083 : Blo 904575 1019083 := bstep (se 1 (by rfl) ⟨764312, by rfl⟩ : syracuseStep 1019083 = 1528625) B1528625
theorem B1019191 : Blo 904575 1019191 := bstep (se 1 (by rfl) ⟨764393, by rfl⟩ : syracuseStep 1019191 = 1528787) B1528787
theorem B6524225 : Blo 904575 6524225 := bstep (se 2 (by rfl) ⟨2446584, by rfl⟩ : syracuseStep 6524225 = 4893169) B4893169
theorem B904587 : Blo 904575 904587 := bstep (se 1 (by rfl) ⟨678440, by rfl⟩ : syracuseStep 904587 = 1356881) B1356881
theorem B904599 : Blo 904575 904599 := bstep (se 1 (by rfl) ⟨678449, by rfl⟩ : syracuseStep 904599 = 1356899) B1356899
theorem B904619 : Blo 904575 904619 := bstep (se 1 (by rfl) ⟨678464, by rfl⟩ : syracuseStep 904619 = 1356929) B1356929
theorem B904631 : Blo 904575 904631 := bstep (se 1 (by rfl) ⟨678473, by rfl⟩ : syracuseStep 904631 = 1356947) B1356947
theorem B904651 : Blo 904575 904651 := bstep (se 1 (by rfl) ⟨678488, by rfl⟩ : syracuseStep 904651 = 1356977) B1356977
theorem B1961419 : Blo 904575 1961419 := bstep (se 1 (by rfl) ⟨1471064, by rfl⟩ : syracuseStep 1961419 = 2942129) B2942129
theorem B904663 : Blo 904575 904663 := bstep (se 1 (by rfl) ⟨678497, by rfl⟩ : syracuseStep 904663 = 1356995) B1356995
theorem B904683 : Blo 904575 904683 := bstep (se 1 (by rfl) ⟨678512, by rfl⟩ : syracuseStep 904683 = 1357025) B1357025
theorem B1019371 : Blo 904575 1019371 := bstep (se 1 (by rfl) ⟨764528, by rfl⟩ : syracuseStep 1019371 = 1529057) B1529057
theorem B904695 : Blo 904575 904695 := bstep (se 1 (by rfl) ⟨678521, by rfl⟩ : syracuseStep 904695 = 1357043) B1357043
theorem B904715 : Blo 904575 904715 := bstep (se 1 (by rfl) ⟨678536, by rfl⟩ : syracuseStep 904715 = 1357073) B1357073
theorem B904727 : Blo 904575 904727 := bstep (se 1 (by rfl) ⟨678545, by rfl⟩ : syracuseStep 904727 = 1357091) B1357091
theorem B904747 : Blo 904575 904747 := bstep (se 1 (by rfl) ⟨678560, by rfl⟩ : syracuseStep 904747 = 1357121) B1357121
theorem B904759 : Blo 904575 904759 := bstep (se 1 (by rfl) ⟨678569, by rfl⟩ : syracuseStep 904759 = 1357139) B1357139
theorem B904779 : Blo 904575 904779 := bstep (se 1 (by rfl) ⟨678584, by rfl⟩ : syracuseStep 904779 = 1357169) B1357169
theorem B904791 : Blo 904575 904791 := bstep (se 1 (by rfl) ⟨678593, by rfl⟩ : syracuseStep 904791 = 1357187) B1357187
theorem B1527383 : Blo 904575 1527383 := bstep (se 1 (by rfl) ⟨1145537, by rfl⟩ : syracuseStep 1527383 = 2291075) B2291075
theorem B1019479 : Blo 904575 1019479 := bstep (se 1 (by rfl) ⟨764609, by rfl⟩ : syracuseStep 1019479 = 1529219) B1529219
theorem B904811 : Blo 904575 904811 := bstep (se 1 (by rfl) ⟨678608, by rfl⟩ : syracuseStep 904811 = 1357217) B1357217
theorem B904823 : Blo 904575 904823 := bstep (se 1 (by rfl) ⟨678617, by rfl⟩ : syracuseStep 904823 = 1357235) B1357235
theorem B904843 : Blo 904575 904843 := bstep (se 1 (by rfl) ⟨678632, by rfl⟩ : syracuseStep 904843 = 1357265) B1357265
theorem B904855 : Blo 904575 904855 := bstep (se 1 (by rfl) ⟨678641, by rfl⟩ : syracuseStep 904855 = 1357283) B1357283
theorem B904875 : Blo 904575 904875 := bstep (se 1 (by rfl) ⟨678656, by rfl⟩ : syracuseStep 904875 = 1357313) B1357313
theorem B904887 : Blo 904575 904887 := bstep (se 1 (by rfl) ⟨678665, by rfl⟩ : syracuseStep 904887 = 1357331) B1357331
theorem B2035403 : Blo 904575 2035403 := bstep (se 1 (by rfl) ⟨1526552, by rfl⟩ : syracuseStep 2035403 = 3053105) B3053105
theorem B904907 : Blo 904575 904907 := bstep (se 1 (by rfl) ⟨678680, by rfl⟩ : syracuseStep 904907 = 1357361) B1357361
theorem B904919 : Blo 904575 904919 := bstep (se 1 (by rfl) ⟨678689, by rfl⟩ : syracuseStep 904919 = 1357379) B1357379
theorem B1527511 : Blo 904575 1527511 := bstep (se 1 (by rfl) ⟨1145633, by rfl⟩ : syracuseStep 1527511 = 2291267) B2291267
theorem B904939 : Blo 904575 904939 := bstep (se 1 (by rfl) ⟨678704, by rfl⟩ : syracuseStep 904939 = 1357409) B1357409
theorem B904951 : Blo 904575 904951 := bstep (se 1 (by rfl) ⟨678713, by rfl⟩ : syracuseStep 904951 = 1357427) B1357427
theorem B2035457 : Blo 904575 2035457 := bstep (se 2 (by rfl) ⟨763296, by rfl⟩ : syracuseStep 2035457 = 1526593) B1526593
theorem B904971 : Blo 904575 904971 := bstep (se 1 (by rfl) ⟨678728, by rfl⟩ : syracuseStep 904971 = 1357457) B1357457
theorem B1019659 : Blo 904575 1019659 := bstep (se 1 (by rfl) ⟨764744, by rfl⟩ : syracuseStep 1019659 = 1529489) B1529489
theorem B904983 : Blo 904575 904983 := bstep (se 1 (by rfl) ⟨678737, by rfl⟩ : syracuseStep 904983 = 1357475) B1357475
theorem B905003 : Blo 904575 905003 := bstep (se 1 (by rfl) ⟨678752, by rfl⟩ : syracuseStep 905003 = 1357505) B1357505
theorem B905015 : Blo 904575 905015 := bstep (se 1 (by rfl) ⟨678761, by rfl⟩ : syracuseStep 905015 = 1357523) B1357523
theorem B905035 : Blo 904575 905035 := bstep (se 1 (by rfl) ⟨678776, by rfl⟩ : syracuseStep 905035 = 1357553) B1357553
theorem B3059531 : Blo 904575 3059531 := bstep (se 1 (by rfl) ⟨2294648, by rfl⟩ : syracuseStep 3059531 = 4589297) B4589297
theorem B905047 : Blo 904575 905047 := bstep (se 1 (by rfl) ⟨678785, by rfl⟩ : syracuseStep 905047 = 1357571) B1357571
theorem B905067 : Blo 904575 905067 := bstep (se 1 (by rfl) ⟨678800, by rfl⟩ : syracuseStep 905067 = 1357601) B1357601
theorem B905079 : Blo 904575 905079 := bstep (se 1 (by rfl) ⟨678809, by rfl⟩ : syracuseStep 905079 = 1357619) B1357619
theorem B1019767 : Blo 904575 1019767 := bstep (se 1 (by rfl) ⟨764825, by rfl⟩ : syracuseStep 1019767 = 1529651) B1529651
theorem B905099 : Blo 904575 905099 := bstep (se 1 (by rfl) ⟨678824, by rfl⟩ : syracuseStep 905099 = 1357649) B1357649
theorem B905111 : Blo 904575 905111 := bstep (se 1 (by rfl) ⟨678833, by rfl⟩ : syracuseStep 905111 = 1357667) B1357667
theorem B3264407 : Blo 904575 3264407 := bstep (se 1 (by rfl) ⟨2448305, by rfl⟩ : syracuseStep 3264407 = 4896611) B4896611
theorem B905131 : Blo 904575 905131 := bstep (se 1 (by rfl) ⟨678848, by rfl⟩ : syracuseStep 905131 = 1357697) B1357697
theorem B7335859 : Blo 904575 7335859 := bstep (se 1 (by rfl) ⟨5501894, by rfl⟩ : syracuseStep 7335859 = 11003789) B11003789
theorem B2903987 : Blo 904575 2903987 := bstep (se 1 (by rfl) ⟨2177990, by rfl⟩ : syracuseStep 2903987 = 4355981) B4355981
theorem B905143 : Blo 904575 905143 := bstep (se 1 (by rfl) ⟨678857, by rfl⟩ : syracuseStep 905143 = 1357715) B1357715
theorem B905163 : Blo 904575 905163 := bstep (se 1 (by rfl) ⟨678872, by rfl⟩ : syracuseStep 905163 = 1357745) B1357745
theorem B905175 : Blo 904575 905175 := bstep (se 1 (by rfl) ⟨678881, by rfl⟩ : syracuseStep 905175 = 1357763) B1357763
theorem B2035673 : Blo 904575 2035673 := bstep (se 2 (by rfl) ⟨763377, by rfl⟩ : syracuseStep 2035673 = 1526755) B1526755
theorem B905195 : Blo 904575 905195 := bstep (se 1 (by rfl) ⟨678896, by rfl⟩ : syracuseStep 905195 = 1357793) B1357793
theorem B905207 : Blo 904575 905207 := bstep (se 1 (by rfl) ⟨678905, by rfl⟩ : syracuseStep 905207 = 1357811) B1357811
theorem B905227 : Blo 904575 905227 := bstep (se 1 (by rfl) ⟨678920, by rfl⟩ : syracuseStep 905227 = 1357841) B1357841
theorem B6279185 : Blo 904575 6279185 := bstep (se 2 (by rfl) ⟨2354694, by rfl⟩ : syracuseStep 6279185 = 4709389) B4709389
theorem B905239 : Blo 904575 905239 := bstep (se 1 (by rfl) ⟨678929, by rfl⟩ : syracuseStep 905239 = 1357859) B1357859
theorem B905259 : Blo 904575 905259 := bstep (se 1 (by rfl) ⟨678944, by rfl⟩ : syracuseStep 905259 = 1357889) B1357889
theorem B2035763 : Blo 904575 2035763 := bstep (se 1 (by rfl) ⟨1526822, by rfl⟩ : syracuseStep 2035763 = 3053645) B3053645
theorem B905271 : Blo 904575 905271 := bstep (se 1 (by rfl) ⟨678953, by rfl⟩ : syracuseStep 905271 = 1357907) B1357907
theorem B905291 : Blo 904575 905291 := bstep (se 1 (by rfl) ⟨678968, by rfl⟩ : syracuseStep 905291 = 1357937) B1357937
theorem B2035799 : Blo 904575 2035799 := bstep (se 1 (by rfl) ⟨1526849, by rfl⟩ : syracuseStep 2035799 = 3053699) B3053699
theorem B905303 : Blo 904575 905303 := bstep (se 1 (by rfl) ⟨678977, by rfl⟩ : syracuseStep 905303 = 1357955) B1357955
theorem B905323 : Blo 904575 905323 := bstep (se 1 (by rfl) ⟨678992, by rfl⟩ : syracuseStep 905323 = 1357985) B1357985
theorem B905335 : Blo 904575 905335 := bstep (se 1 (by rfl) ⟨679001, by rfl⟩ : syracuseStep 905335 = 1358003) B1358003
theorem B6869123 : Blo 904575 6869123 := bstep (se 1 (by rfl) ⟨5151842, by rfl⟩ : syracuseStep 6869123 = 10303685) B10303685
theorem B905355 : Blo 904575 905355 := bstep (se 1 (by rfl) ⟨679016, by rfl⟩ : syracuseStep 905355 = 1358033) B1358033
theorem B905367 : Blo 904575 905367 := bstep (se 1 (by rfl) ⟨679025, by rfl⟩ : syracuseStep 905367 = 1358051) B1358051
theorem B905387 : Blo 904575 905387 := bstep (se 1 (by rfl) ⟨679040, by rfl⟩ : syracuseStep 905387 = 1358081) B1358081
theorem B905399 : Blo 904575 905399 := bstep (se 1 (by rfl) ⟨679049, by rfl⟩ : syracuseStep 905399 = 1358099) B1358099
theorem B905419 : Blo 904575 905419 := bstep (se 1 (by rfl) ⟨679064, by rfl⟩ : syracuseStep 905419 = 1358129) B1358129
theorem B905431 : Blo 904575 905431 := bstep (se 1 (by rfl) ⟨679073, by rfl⟩ : syracuseStep 905431 = 1358147) B1358147
theorem B2576605 : Blo 904575 2576605 := bstep (se 3 (by rfl) ⟨483113, by rfl⟩ : syracuseStep 2576605 = 966227) B966227
theorem B905451 : Blo 904575 905451 := bstep (se 1 (by rfl) ⟨679088, by rfl⟩ : syracuseStep 905451 = 1358177) B1358177
theorem B905463 : Blo 904575 905463 := bstep (se 1 (by rfl) ⟨679097, by rfl⟩ : syracuseStep 905463 = 1358195) B1358195
theorem B2035979 : Blo 904575 2035979 := bstep (se 1 (by rfl) ⟨1526984, by rfl⟩ : syracuseStep 2035979 = 3053969) B3053969
theorem B905483 : Blo 904575 905483 := bstep (se 1 (by rfl) ⟨679112, by rfl⟩ : syracuseStep 905483 = 1358225) B1358225
theorem B905495 : Blo 904575 905495 := bstep (se 1 (by rfl) ⟨679121, by rfl⟩ : syracuseStep 905495 = 1358243) B1358243
theorem B905515 : Blo 904575 905515 := bstep (se 1 (by rfl) ⟨679136, by rfl⟩ : syracuseStep 905515 = 1358273) B1358273
theorem B2289971 : Blo 904575 2289971 := bstep (se 1 (by rfl) ⟨1717478, by rfl⟩ : syracuseStep 2289971 = 3434957) B3434957
theorem B1675571 : Blo 904575 1675571 := bstep (se 1 (by rfl) ⟨1256678, by rfl⟩ : syracuseStep 1675571 = 2513357) B2513357
theorem B905527 : Blo 904575 905527 := bstep (se 1 (by rfl) ⟨679145, by rfl⟩ : syracuseStep 905527 = 1358291) B1358291
theorem B2036033 : Blo 904575 2036033 := bstep (se 2 (by rfl) ⟨763512, by rfl⟩ : syracuseStep 2036033 = 1527025) B1527025
theorem B905547 : Blo 904575 905547 := bstep (se 1 (by rfl) ⟨679160, by rfl⟩ : syracuseStep 905547 = 1358321) B1358321
theorem B1528139 : Blo 904575 1528139 := bstep (se 1 (by rfl) ⟨1146104, by rfl⟩ : syracuseStep 1528139 = 2292209) B2292209
theorem B905559 : Blo 904575 905559 := bstep (se 1 (by rfl) ⟨679169, by rfl⟩ : syracuseStep 905559 = 1358339) B1358339
theorem B905579 : Blo 904575 905579 := bstep (se 1 (by rfl) ⟨679184, by rfl⟩ : syracuseStep 905579 = 1358369) B1358369
theorem B905591 : Blo 904575 905591 := bstep (se 1 (by rfl) ⟨679193, by rfl⟩ : syracuseStep 905591 = 1358387) B1358387
theorem B3436931 : Blo 904575 3436931 := bstep (se 1 (by rfl) ⟨2577698, by rfl⟩ : syracuseStep 3436931 = 5155397) B5155397
theorem B905611 : Blo 904575 905611 := bstep (se 1 (by rfl) ⟨679208, by rfl⟩ : syracuseStep 905611 = 1358417) B1358417
theorem B905623 : Blo 904575 905623 := bstep (se 1 (by rfl) ⟨679217, by rfl⟩ : syracuseStep 905623 = 1358435) B1358435
theorem B3871127 : Blo 904575 3871127 := bstep (se 1 (by rfl) ⟨2903345, by rfl⟩ : syracuseStep 3871127 = 5806691) B5806691
theorem B1290649 : Blo 904575 1290649 := bstep (se 2 (by rfl) ⟨483993, by rfl⟩ : syracuseStep 1290649 = 967987) B967987
theorem B905643 : Blo 904575 905643 := bstep (se 1 (by rfl) ⟨679232, by rfl⟩ : syracuseStep 905643 = 1358465) B1358465
theorem B905655 : Blo 904575 905655 := bstep (se 1 (by rfl) ⟨679241, by rfl⟩ : syracuseStep 905655 = 1358483) B1358483
theorem B1528267 : Blo 904575 1528267 := bstep (se 1 (by rfl) ⟨1146200, by rfl⟩ : syracuseStep 1528267 = 2292401) B2292401
theorem B905675 : Blo 904575 905675 := bstep (se 1 (by rfl) ⟨679256, by rfl⟩ : syracuseStep 905675 = 1358513) B1358513
theorem B905687 : Blo 904575 905687 := bstep (se 1 (by rfl) ⟨679265, by rfl⟩ : syracuseStep 905687 = 1358531) B1358531
theorem B1470935 : Blo 904575 1470935 := bstep (se 1 (by rfl) ⟨1103201, by rfl⟩ : syracuseStep 1470935 = 2206403) B2206403
theorem B905707 : Blo 904575 905707 := bstep (se 1 (by rfl) ⟨679280, by rfl⟩ : syracuseStep 905707 = 1358561) B1358561
theorem B905719 : Blo 904575 905719 := bstep (se 1 (by rfl) ⟨679289, by rfl⟩ : syracuseStep 905719 = 1358579) B1358579
theorem B905739 : Blo 904575 905739 := bstep (se 1 (by rfl) ⟨679304, by rfl⟩ : syracuseStep 905739 = 1358609) B1358609
theorem B1290763 : Blo 904575 1290763 := bstep (se 1 (by rfl) ⟨968072, by rfl⟩ : syracuseStep 1290763 = 1936145) B1936145
theorem B2175511 : Blo 904575 2175511 := bstep (se 1 (by rfl) ⟨1631633, by rfl⟩ : syracuseStep 2175511 = 3263267) B3263267
theorem B905751 : Blo 904575 905751 := bstep (se 1 (by rfl) ⟨679313, by rfl⟩ : syracuseStep 905751 = 1358627) B1358627
theorem B2036249 : Blo 904575 2036249 := bstep (se 2 (by rfl) ⟨763593, by rfl⟩ : syracuseStep 2036249 = 1527187) B1527187
theorem B905771 : Blo 904575 905771 := bstep (se 1 (by rfl) ⟨679328, by rfl⟩ : syracuseStep 905771 = 1358657) B1358657
theorem B2576947 : Blo 904575 2576947 := bstep (se 1 (by rfl) ⟨1932710, by rfl⟩ : syracuseStep 2576947 = 3865421) B3865421
theorem B905783 : Blo 904575 905783 := bstep (se 1 (by rfl) ⟨679337, by rfl⟩ : syracuseStep 905783 = 1358675) B1358675
theorem B905803 : Blo 904575 905803 := bstep (se 1 (by rfl) ⟨679352, by rfl⟩ : syracuseStep 905803 = 1358705) B1358705
theorem B905815 : Blo 904575 905815 := bstep (se 1 (by rfl) ⟨679361, by rfl⟩ : syracuseStep 905815 = 1358723) B1358723
theorem B2290265 : Blo 904575 2290265 := bstep (se 2 (by rfl) ⟨858849, by rfl⟩ : syracuseStep 2290265 = 1717699) B1717699
theorem B1528409 : Blo 904575 1528409 := bstep (se 2 (by rfl) ⟨573153, by rfl⟩ : syracuseStep 1528409 = 1146307) B1146307
theorem B8270437 : Blo 904575 8270437 := bstep (se 4 (by rfl) ⟨775353, by rfl⟩ : syracuseStep 8270437 = 1550707) B1550707
theorem B905835 : Blo 904575 905835 := bstep (se 1 (by rfl) ⟨679376, by rfl⟩ : syracuseStep 905835 = 1358753) B1358753
theorem B2036339 : Blo 904575 2036339 := bstep (se 1 (by rfl) ⟨1527254, by rfl⟩ : syracuseStep 2036339 = 3054509) B3054509
theorem B905847 : Blo 904575 905847 := bstep (se 1 (by rfl) ⟨679385, by rfl⟩ : syracuseStep 905847 = 1358771) B1358771
theorem B905867 : Blo 904575 905867 := bstep (se 1 (by rfl) ⟨679400, by rfl⟩ : syracuseStep 905867 = 1358801) B1358801
theorem B2036375 : Blo 904575 2036375 := bstep (se 1 (by rfl) ⟨1527281, by rfl⟩ : syracuseStep 2036375 = 3054563) B3054563
theorem B905879 : Blo 904575 905879 := bstep (se 1 (by rfl) ⟨679409, by rfl⟩ : syracuseStep 905879 = 1358819) B1358819
theorem B1471129 : Blo 904575 1471129 := bstep (se 2 (by rfl) ⟨551673, by rfl⟩ : syracuseStep 1471129 = 1103347) B1103347
theorem B905899 : Blo 904575 905899 := bstep (se 1 (by rfl) ⟨679424, by rfl⟩ : syracuseStep 905899 = 1358849) B1358849
theorem B905911 : Blo 904575 905911 := bstep (se 1 (by rfl) ⟨679433, by rfl⟩ : syracuseStep 905911 = 1358867) B1358867
theorem B905931 : Blo 904575 905931 := bstep (se 1 (by rfl) ⟨679448, by rfl⟩ : syracuseStep 905931 = 1358897) B1358897
theorem B3871435 : Blo 904575 3871435 := bstep (se 1 (by rfl) ⟨2903576, by rfl⟩ : syracuseStep 3871435 = 5807153) B5807153
theorem B905943 : Blo 904575 905943 := bstep (se 1 (by rfl) ⟨679457, by rfl⟩ : syracuseStep 905943 = 1358915) B1358915
theorem B1528537 : Blo 904575 1528537 := bstep (se 2 (by rfl) ⟨573201, by rfl⟩ : syracuseStep 1528537 = 1146403) B1146403
theorem B905963 : Blo 904575 905963 := bstep (se 1 (by rfl) ⟨679472, by rfl⟩ : syracuseStep 905963 = 1358945) B1358945
theorem B905975 : Blo 904575 905975 := bstep (se 1 (by rfl) ⟨679481, by rfl⟩ : syracuseStep 905975 = 1358963) B1358963
theorem B905995 : Blo 904575 905995 := bstep (se 1 (by rfl) ⟨679496, by rfl⟩ : syracuseStep 905995 = 1358993) B1358993
theorem B906007 : Blo 904575 906007 := bstep (se 1 (by rfl) ⟨679505, by rfl⟩ : syracuseStep 906007 = 1359011) B1359011
theorem B906027 : Blo 904575 906027 := bstep (se 1 (by rfl) ⟨679520, by rfl⟩ : syracuseStep 906027 = 1359041) B1359041
theorem B906039 : Blo 904575 906039 := bstep (se 1 (by rfl) ⟨679529, by rfl⟩ : syracuseStep 906039 = 1359059) B1359059
theorem B2978635 : Blo 904575 2978635 := bstep (se 1 (by rfl) ⟨2233976, by rfl⟩ : syracuseStep 2978635 = 4467953) B4467953
theorem B2036555 : Blo 904575 2036555 := bstep (se 1 (by rfl) ⟨1527416, by rfl⟩ : syracuseStep 2036555 = 3054833) B3054833
theorem B3437387 : Blo 904575 3437387 := bstep (se 1 (by rfl) ⟨2578040, by rfl⟩ : syracuseStep 3437387 = 5156081) B5156081
theorem B906059 : Blo 904575 906059 := bstep (se 1 (by rfl) ⟨679544, by rfl⟩ : syracuseStep 906059 = 1359089) B1359089
theorem B906071 : Blo 904575 906071 := bstep (se 1 (by rfl) ⟨679553, by rfl⟩ : syracuseStep 906071 = 1359107) B1359107
theorem B906091 : Blo 904575 906091 := bstep (se 1 (by rfl) ⟨679568, by rfl⟩ : syracuseStep 906091 = 1359137) B1359137
theorem B906103 : Blo 904575 906103 := bstep (se 1 (by rfl) ⟨679577, by rfl⟩ : syracuseStep 906103 = 1359155) B1359155
theorem B2036609 : Blo 904575 2036609 := bstep (se 2 (by rfl) ⟨763728, by rfl⟩ : syracuseStep 2036609 = 1527457) B1527457
theorem B906123 : Blo 904575 906123 := bstep (se 1 (by rfl) ⟨679592, by rfl⟩ : syracuseStep 906123 = 1359185) B1359185
theorem B906135 : Blo 904575 906135 := bstep (se 1 (by rfl) ⟨679601, by rfl⟩ : syracuseStep 906135 = 1359203) B1359203
theorem B906155 : Blo 904575 906155 := bstep (se 1 (by rfl) ⟨679616, by rfl⟩ : syracuseStep 906155 = 1359233) B1359233
theorem B906167 : Blo 904575 906167 := bstep (se 1 (by rfl) ⟨679625, by rfl⟩ : syracuseStep 906167 = 1359251) B1359251
theorem B906187 : Blo 904575 906187 := bstep (se 1 (by rfl) ⟨679640, by rfl⟩ : syracuseStep 906187 = 1359281) B1359281
theorem B906199 : Blo 904575 906199 := bstep (se 1 (by rfl) ⟨679649, by rfl⟩ : syracuseStep 906199 = 1359299) B1359299
theorem B3871709 : Blo 904575 3871709 := bstep (se 3 (by rfl) ⟨725945, by rfl⟩ : syracuseStep 3871709 = 1451891) B1451891
theorem B906219 : Blo 904575 906219 := bstep (se 1 (by rfl) ⟨679664, by rfl⟩ : syracuseStep 906219 = 1359329) B1359329
theorem B906231 : Blo 904575 906231 := bstep (se 1 (by rfl) ⟨679673, by rfl⟩ : syracuseStep 906231 = 1359347) B1359347
theorem B906251 : Blo 904575 906251 := bstep (se 1 (by rfl) ⟨679688, by rfl⟩ : syracuseStep 906251 = 1359377) B1359377
theorem B3437585 : Blo 904575 3437585 := bstep (se 2 (by rfl) ⟨1289094, by rfl⟩ : syracuseStep 3437585 = 2578189) B2578189
theorem B906263 : Blo 904575 906263 := bstep (se 1 (by rfl) ⟨679697, by rfl⟩ : syracuseStep 906263 = 1359395) B1359395
theorem B906283 : Blo 904575 906283 := bstep (se 1 (by rfl) ⟨679712, by rfl⟩ : syracuseStep 906283 = 1359425) B1359425
theorem B906295 : Blo 904575 906295 := bstep (se 1 (by rfl) ⟨679721, by rfl⟩ : syracuseStep 906295 = 1359443) B1359443
theorem B3265601 : Blo 904575 3265601 := bstep (se 2 (by rfl) ⟨1224600, by rfl⟩ : syracuseStep 3265601 = 2449201) B2449201
theorem B1356875 : Blo 904575 1356875 := bstep (se 1 (by rfl) ⟨1017656, by rfl⟩ : syracuseStep 1356875 = 2035313) B2035313
theorem B906315 : Blo 904575 906315 := bstep (se 1 (by rfl) ⟨679736, by rfl⟩ : syracuseStep 906315 = 1359473) B1359473
theorem B1356887 : Blo 904575 1356887 := bstep (se 1 (by rfl) ⟨1017665, by rfl⟩ : syracuseStep 1356887 = 2035331) B2035331
theorem B906327 : Blo 904575 906327 := bstep (se 1 (by rfl) ⟨679745, by rfl⟩ : syracuseStep 906327 = 1359491) B1359491
theorem B2036825 : Blo 904575 2036825 := bstep (se 2 (by rfl) ⟨763809, by rfl⟩ : syracuseStep 2036825 = 1527619) B1527619
theorem B906347 : Blo 904575 906347 := bstep (se 1 (by rfl) ⟨679760, by rfl⟩ : syracuseStep 906347 = 1359521) B1359521
theorem B906359 : Blo 904575 906359 := bstep (se 1 (by rfl) ⟨679769, by rfl⟩ : syracuseStep 906359 = 1359539) B1359539
theorem B11596931 : Blo 904575 11596931 := bstep (se 1 (by rfl) ⟨8697698, by rfl⟩ : syracuseStep 11596931 = 17395397) B17395397
theorem B906379 : Blo 904575 906379 := bstep (se 1 (by rfl) ⟨679784, by rfl⟩ : syracuseStep 906379 = 1359569) B1359569
theorem B4584599 : Blo 904575 4584599 := bstep (se 1 (by rfl) ⟨3438449, by rfl⟩ : syracuseStep 4584599 = 6876899) B6876899
theorem B5158039 : Blo 904575 5158039 := bstep (se 1 (by rfl) ⟨3868529, by rfl⟩ : syracuseStep 5158039 = 7737059) B7737059
theorem B1356953 : Blo 904575 1356953 := bstep (se 2 (by rfl) ⟨508857, by rfl⟩ : syracuseStep 1356953 = 1017715) B1017715
theorem B3265687 : Blo 904575 3265687 := bstep (se 1 (by rfl) ⟨2449265, by rfl⟩ : syracuseStep 3265687 = 4898531) B4898531
theorem B906391 : Blo 904575 906391 := bstep (se 1 (by rfl) ⟨679793, by rfl⟩ : syracuseStep 906391 = 1359587) B1359587
theorem B906411 : Blo 904575 906411 := bstep (se 1 (by rfl) ⟨679808, by rfl⟩ : syracuseStep 906411 = 1359617) B1359617
theorem B6526129 : Blo 904575 6526129 := bstep (se 2 (by rfl) ⟨2447298, by rfl⟩ : syracuseStep 6526129 = 4894597) B4894597
theorem B2036915 : Blo 904575 2036915 := bstep (se 1 (by rfl) ⟨1527686, by rfl⟩ : syracuseStep 2036915 = 3055373) B3055373
theorem B906423 : Blo 904575 906423 := bstep (se 1 (by rfl) ⟨679817, by rfl⟩ : syracuseStep 906423 = 1359635) B1359635
theorem B906443 : Blo 904575 906443 := bstep (se 1 (by rfl) ⟨679832, by rfl⟩ : syracuseStep 906443 = 1359665) B1359665
theorem B1717463 : Blo 904575 1717463 := bstep (se 1 (by rfl) ⟨1288097, by rfl⟩ : syracuseStep 1717463 = 2576195) B2576195
theorem B2036951 : Blo 904575 2036951 := bstep (se 1 (by rfl) ⟨1527713, by rfl⟩ : syracuseStep 2036951 = 3055427) B3055427
theorem B906455 : Blo 904575 906455 := bstep (se 1 (by rfl) ⟨679841, by rfl⟩ : syracuseStep 906455 = 1359683) B1359683
theorem B906475 : Blo 904575 906475 := bstep (se 1 (by rfl) ⟨679856, by rfl⟩ : syracuseStep 906475 = 1359713) B1359713
theorem B906487 : Blo 904575 906487 := bstep (se 1 (by rfl) ⟨679865, by rfl⟩ : syracuseStep 906487 = 1359731) B1359731
theorem B1357067 : Blo 904575 1357067 := bstep (se 1 (by rfl) ⟨1017800, by rfl⟩ : syracuseStep 1357067 = 2035601) B2035601
theorem B906507 : Blo 904575 906507 := bstep (se 1 (by rfl) ⟨679880, by rfl⟩ : syracuseStep 906507 = 1359761) B1359761
theorem B1357079 : Blo 904575 1357079 := bstep (se 1 (by rfl) ⟨1017809, by rfl⟩ : syracuseStep 1357079 = 2035619) B2035619
theorem B1529111 : Blo 904575 1529111 := bstep (se 1 (by rfl) ⟨1146833, by rfl⟩ : syracuseStep 1529111 = 2293667) B2293667
theorem B906519 : Blo 904575 906519 := bstep (se 1 (by rfl) ⟨679889, by rfl⟩ : syracuseStep 906519 = 1359779) B1359779
theorem B906539 : Blo 904575 906539 := bstep (se 1 (by rfl) ⟨679904, by rfl⟩ : syracuseStep 906539 = 1359809) B1359809
theorem B906551 : Blo 904575 906551 := bstep (se 1 (by rfl) ⟨679913, by rfl⟩ : syracuseStep 906551 = 1359827) B1359827
theorem B7738699 : Blo 904575 7738699 := bstep (se 1 (by rfl) ⟨5804024, by rfl⟩ : syracuseStep 7738699 = 11608049) B11608049
theorem B906571 : Blo 904575 906571 := bstep (se 1 (by rfl) ⟨679928, by rfl⟩ : syracuseStep 906571 = 1359857) B1359857
theorem B1357145 : Blo 904575 1357145 := bstep (se 2 (by rfl) ⟨508929, by rfl⟩ : syracuseStep 1357145 = 1017859) B1017859
theorem B2037131 : Blo 904575 2037131 := bstep (se 1 (by rfl) ⟨1527848, by rfl⟩ : syracuseStep 2037131 = 3055697) B3055697
theorem B1529239 : Blo 904575 1529239 := bstep (se 1 (by rfl) ⟨1146929, by rfl⟩ : syracuseStep 1529239 = 2293859) B2293859
theorem B4355479 : Blo 904575 4355479 := bstep (se 1 (by rfl) ⟨3266609, by rfl⟩ : syracuseStep 4355479 = 6533219) B6533219
theorem B2037185 : Blo 904575 2037185 := bstep (se 2 (by rfl) ⟨763944, by rfl⟩ : syracuseStep 2037185 = 1527889) B1527889
theorem B1357259 : Blo 904575 1357259 := bstep (se 1 (by rfl) ⟨1017944, by rfl⟩ : syracuseStep 1357259 = 2035889) B2035889
theorem B1357271 : Blo 904575 1357271 := bstep (se 1 (by rfl) ⟨1017953, by rfl⟩ : syracuseStep 1357271 = 2035907) B2035907
theorem B2577881 : Blo 904575 2577881 := bstep (se 2 (by rfl) ⟨966705, by rfl⟩ : syracuseStep 2577881 = 1933411) B1933411
theorem B1357337 : Blo 904575 1357337 := bstep (se 2 (by rfl) ⟨509001, by rfl⟩ : syracuseStep 1357337 = 1018003) B1018003
theorem B1570379 : Blo 904575 1570379 := bstep (se 1 (by rfl) ⟨1177784, by rfl⟩ : syracuseStep 1570379 = 2355569) B2355569
theorem B1087063 : Blo 904575 1087063 := bstep (se 1 (by rfl) ⟨815297, by rfl⟩ : syracuseStep 1087063 = 1630595) B1630595
theorem B7738973 : Blo 904575 7738973 := bstep (se 3 (by rfl) ⟨1451057, by rfl⟩ : syracuseStep 7738973 = 2902115) B2902115
theorem B1357451 : Blo 904575 1357451 := bstep (se 1 (by rfl) ⟨1018088, by rfl⟩ : syracuseStep 1357451 = 2036177) B2036177
theorem B1357463 : Blo 904575 1357463 := bstep (se 1 (by rfl) ⟨1018097, by rfl⟩ : syracuseStep 1357463 = 2036195) B2036195
theorem B2037401 : Blo 904575 2037401 := bstep (se 2 (by rfl) ⟨764025, by rfl⟩ : syracuseStep 2037401 = 1528051) B1528051
theorem B1357529 : Blo 904575 1357529 := bstep (se 2 (by rfl) ⟨509073, by rfl⟩ : syracuseStep 1357529 = 1018147) B1018147
theorem B1718003 : Blo 904575 1718003 := bstep (se 1 (by rfl) ⟨1288502, by rfl⟩ : syracuseStep 1718003 = 2577005) B2577005
theorem B2037491 : Blo 904575 2037491 := bstep (se 1 (by rfl) ⟨1528118, by rfl⟩ : syracuseStep 2037491 = 3056237) B3056237
theorem B2037527 : Blo 904575 2037527 := bstep (se 1 (by rfl) ⟨1528145, by rfl⟩ : syracuseStep 2037527 = 3056291) B3056291
theorem B3438359 : Blo 904575 3438359 := bstep (se 1 (by rfl) ⟨2578769, by rfl⟩ : syracuseStep 3438359 = 5157539) B5157539
theorem B1357643 : Blo 904575 1357643 := bstep (se 1 (by rfl) ⟨1018232, by rfl⟩ : syracuseStep 1357643 = 2036465) B2036465
theorem B1357655 : Blo 904575 1357655 := bstep (se 1 (by rfl) ⟨1018241, by rfl⟩ : syracuseStep 1357655 = 2036483) B2036483
theorem B3667801 : Blo 904575 3667801 := bstep (se 2 (by rfl) ⟨1375425, by rfl⟩ : syracuseStep 3667801 = 2750851) B2750851
theorem B7346051 : Blo 904575 7346051 := bstep (se 1 (by rfl) ⟨5509538, by rfl⟩ : syracuseStep 7346051 = 11019077) B11019077
theorem B1357721 : Blo 904575 1357721 := bstep (se 2 (by rfl) ⟨509145, by rfl⟩ : syracuseStep 1357721 = 1018291) B1018291
theorem B9795505 : Blo 904575 9795505 := bstep (se 2 (by rfl) ⟨3673314, by rfl⟩ : syracuseStep 9795505 = 7346629) B7346629
theorem B2037707 : Blo 904575 2037707 := bstep (se 1 (by rfl) ⟨1528280, by rfl⟩ : syracuseStep 2037707 = 3056561) B3056561
theorem B3438557 : Blo 904575 3438557 := bstep (se 3 (by rfl) ⟨644729, by rfl⟩ : syracuseStep 3438557 = 1289459) B1289459
theorem B2037761 : Blo 904575 2037761 := bstep (se 2 (by rfl) ⟨764160, by rfl⟩ : syracuseStep 2037761 = 1528321) B1528321
theorem B1357835 : Blo 904575 1357835 := bstep (se 1 (by rfl) ⟨1018376, by rfl⟩ : syracuseStep 1357835 = 2036753) B2036753
theorem B3053591 : Blo 904575 3053591 := bstep (se 1 (by rfl) ⟨2290193, by rfl⟩ : syracuseStep 3053591 = 4580387) B4580387
theorem B1357847 : Blo 904575 1357847 := bstep (se 1 (by rfl) ⟨1018385, by rfl⟩ : syracuseStep 1357847 = 2036771) B2036771
theorem B1357913 : Blo 904575 1357913 := bstep (se 2 (by rfl) ⟨509217, by rfl⟩ : syracuseStep 1357913 = 1018435) B1018435
theorem B1358027 : Blo 904575 1358027 := bstep (se 1 (by rfl) ⟨1018520, by rfl⟩ : syracuseStep 1358027 = 2037041) B2037041
theorem B2291915 : Blo 904575 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B1358039 : Blo 904575 1358039 := bstep (se 1 (by rfl) ⟨1018529, by rfl⟩ : syracuseStep 1358039 = 2037059) B2037059
theorem B1718489 : Blo 904575 1718489 := bstep (se 2 (by rfl) ⟨644433, by rfl⟩ : syracuseStep 1718489 = 1288867) B1288867
theorem B2037977 : Blo 904575 2037977 := bstep (se 2 (by rfl) ⟨764241, by rfl⟩ : syracuseStep 2037977 = 1528483) B1528483
theorem B1358105 : Blo 904575 1358105 := bstep (se 2 (by rfl) ⟨509289, by rfl⟩ : syracuseStep 1358105 = 1018579) B1018579
theorem B2038067 : Blo 904575 2038067 := bstep (se 1 (by rfl) ⟨1528550, by rfl⟩ : syracuseStep 2038067 = 3057101) B3057101
theorem B2611531 : Blo 904575 2611531 := bstep (se 1 (by rfl) ⟨1958648, by rfl⟩ : syracuseStep 2611531 = 3917297) B3917297
theorem B4348235 : Blo 904575 4348235 := bstep (se 1 (by rfl) ⟨3261176, by rfl⟩ : syracuseStep 4348235 = 6522353) B6522353
theorem B2038103 : Blo 904575 2038103 := bstep (se 1 (by rfl) ⟨1528577, by rfl⟩ : syracuseStep 2038103 = 3057155) B3057155
theorem B1489291 : Blo 904575 1489291 := bstep (se 1 (by rfl) ⟨1116968, by rfl⟩ : syracuseStep 1489291 = 2233937) B2233937
theorem B1358219 : Blo 904575 1358219 := bstep (se 1 (by rfl) ⟨1018664, by rfl⟩ : syracuseStep 1358219 = 2037329) B2037329
theorem B1358231 : Blo 904575 1358231 := bstep (se 1 (by rfl) ⟨1018673, by rfl⟩ : syracuseStep 1358231 = 2037347) B2037347
theorem B1358297 : Blo 904575 1358297 := bstep (se 2 (by rfl) ⟨509361, by rfl⟩ : syracuseStep 1358297 = 1018723) B1018723
theorem B2038283 : Blo 904575 2038283 := bstep (se 1 (by rfl) ⟨1528712, by rfl⟩ : syracuseStep 2038283 = 3057425) B3057425
theorem B3054131 : Blo 904575 3054131 := bstep (se 1 (by rfl) ⟨2290598, by rfl⟩ : syracuseStep 3054131 = 4581197) B4581197
theorem B2038337 : Blo 904575 2038337 := bstep (se 2 (by rfl) ⟨764376, by rfl⟩ : syracuseStep 2038337 = 1528753) B1528753
theorem B14678597 : Blo 904575 14678597 := bstep (se 4 (by rfl) ⟨1376118, by rfl⟩ : syracuseStep 14678597 = 2752237) B2752237
theorem B1358411 : Blo 904575 1358411 := bstep (se 1 (by rfl) ⟨1018808, by rfl⟩ : syracuseStep 1358411 = 2037617) B2037617
theorem B5806667 : Blo 904575 5806667 := bstep (se 1 (by rfl) ⟨4355000, by rfl⟩ : syracuseStep 5806667 = 8710001) B8710001
theorem B1145431 : Blo 904575 1145431 := bstep (se 1 (by rfl) ⟨859073, by rfl⟩ : syracuseStep 1145431 = 1718147) B1718147
theorem B1358423 : Blo 904575 1358423 := bstep (se 1 (by rfl) ⟨1018817, by rfl⟩ : syracuseStep 1358423 = 2037635) B2037635
theorem B2611805 : Blo 904575 2611805 := bstep (se 3 (by rfl) ⟨489713, by rfl⟩ : syracuseStep 2611805 = 979427) B979427
theorem B8706653 : Blo 904575 8706653 := bstep (se 3 (by rfl) ⟨1632497, by rfl⟩ : syracuseStep 8706653 = 3264995) B3264995
theorem B7740035 : Blo 904575 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B1358489 : Blo 904575 1358489 := bstep (se 2 (by rfl) ⟨509433, by rfl⟩ : syracuseStep 1358489 = 1018867) B1018867
theorem B1358603 : Blo 904575 1358603 := bstep (se 1 (by rfl) ⟨1018952, by rfl⟩ : syracuseStep 1358603 = 2037905) B2037905
theorem B1358615 : Blo 904575 1358615 := bstep (se 1 (by rfl) ⟨1018961, by rfl⟩ : syracuseStep 1358615 = 2037923) B2037923
theorem B2038553 : Blo 904575 2038553 := bstep (se 2 (by rfl) ⟨764457, by rfl⟩ : syracuseStep 2038553 = 1528915) B1528915
theorem B11615021 : Blo 904575 11615021 := bstep (se 3 (by rfl) ⟨2177816, by rfl⟩ : syracuseStep 11615021 = 4355633) B4355633
theorem B3054401 : Blo 904575 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B4414283 : Blo 904575 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B1358681 : Blo 904575 1358681 := bstep (se 2 (by rfl) ⟨509505, by rfl⟩ : syracuseStep 1358681 = 1019011) B1019011
theorem B2579293 : Blo 904575 2579293 := bstep (se 3 (by rfl) ⟨483617, by rfl⟩ : syracuseStep 2579293 = 967235) B967235
theorem B2038643 : Blo 904575 2038643 := bstep (se 1 (by rfl) ⟨1528982, by rfl⟩ : syracuseStep 2038643 = 3057965) B3057965
theorem B2038679 : Blo 904575 2038679 := bstep (se 1 (by rfl) ⟨1529009, by rfl⟩ : syracuseStep 2038679 = 3058019) B3058019
theorem B1489817 : Blo 904575 1489817 := bstep (se 2 (by rfl) ⟨558681, by rfl⟩ : syracuseStep 1489817 = 1117363) B1117363
theorem B1358795 : Blo 904575 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B2063321 : Blo 904575 2063321 := bstep (se 2 (by rfl) ⟨773745, by rfl⟩ : syracuseStep 2063321 = 1547491) B1547491
theorem B1358807 : Blo 904575 1358807 := bstep (se 1 (by rfl) ⟨1019105, by rfl⟩ : syracuseStep 1358807 = 2038211) B2038211
theorem B1932275 : Blo 904575 1932275 := bstep (se 1 (by rfl) ⟨1449206, by rfl⟩ : syracuseStep 1932275 = 2898413) B2898413
theorem B1358873 : Blo 904575 1358873 := bstep (se 2 (by rfl) ⟨509577, by rfl⟩ : syracuseStep 1358873 = 1019155) B1019155
theorem B6880301 : Blo 904575 6880301 := bstep (se 3 (by rfl) ⟨1290056, by rfl⟩ : syracuseStep 6880301 = 2580113) B2580113
theorem B2579521 : Blo 904575 2579521 := bstep (se 2 (by rfl) ⟨967320, by rfl⟩ : syracuseStep 2579521 = 1934641) B1934641
theorem B2038859 : Blo 904575 2038859 := bstep (se 1 (by rfl) ⟨1529144, by rfl⟩ : syracuseStep 2038859 = 3058289) B3058289
theorem B2038913 : Blo 904575 2038913 := bstep (se 2 (by rfl) ⟨764592, by rfl⟩ : syracuseStep 2038913 = 1529185) B1529185
theorem B1358987 : Blo 904575 1358987 := bstep (se 1 (by rfl) ⟨1019240, by rfl⟩ : syracuseStep 1358987 = 2038481) B2038481
theorem B2292887 : Blo 904575 2292887 := bstep (se 1 (by rfl) ⟨1719665, by rfl⟩ : syracuseStep 2292887 = 3439331) B3439331
theorem B1358999 : Blo 904575 1358999 := bstep (se 1 (by rfl) ⟨1019249, by rfl⟩ : syracuseStep 1358999 = 2038499) B2038499
theorem B1359065 : Blo 904575 1359065 := bstep (se 2 (by rfl) ⟨509649, by rfl⟩ : syracuseStep 1359065 = 1019299) B1019299
theorem B1359179 : Blo 904575 1359179 := bstep (se 1 (by rfl) ⟨1019384, by rfl⟩ : syracuseStep 1359179 = 2038769) B2038769
theorem B1359191 : Blo 904575 1359191 := bstep (se 1 (by rfl) ⟨1019393, by rfl⟩ : syracuseStep 1359191 = 2038787) B2038787
theorem B2039129 : Blo 904575 2039129 := bstep (se 2 (by rfl) ⟨764673, by rfl⟩ : syracuseStep 2039129 = 1529347) B1529347
theorem B3054941 : Blo 904575 3054941 := bstep (se 3 (by rfl) ⟨572801, by rfl⟩ : syracuseStep 3054941 = 1145603) B1145603
theorem B1146251 : Blo 904575 1146251 := bstep (se 1 (by rfl) ⟨859688, by rfl⟩ : syracuseStep 1146251 = 1719377) B1719377
theorem B2579863 : Blo 904575 2579863 := bstep (se 1 (by rfl) ⟨1934897, by rfl⟩ : syracuseStep 2579863 = 3869795) B3869795
theorem B1359257 : Blo 904575 1359257 := bstep (se 2 (by rfl) ⟨509721, by rfl⟩ : syracuseStep 1359257 = 1019443) B1019443
theorem B15457715 : Blo 904575 15457715 := bstep (se 1 (by rfl) ⟨11593286, by rfl⟩ : syracuseStep 15457715 = 23186573) B23186573
theorem B2039219 : Blo 904575 2039219 := bstep (se 1 (by rfl) ⟨1529414, by rfl⟩ : syracuseStep 2039219 = 3058829) B3058829
theorem B6872525 : Blo 904575 6872525 := bstep (se 3 (by rfl) ⟨1288598, by rfl⟩ : syracuseStep 6872525 = 2577197) B2577197
theorem B7732685 : Blo 904575 7732685 := bstep (se 3 (by rfl) ⟨1449878, by rfl⟩ : syracuseStep 7732685 = 2899757) B2899757
theorem B1449431 : Blo 904575 1449431 := bstep (se 1 (by rfl) ⟨1087073, by rfl⟩ : syracuseStep 1449431 = 2174147) B2174147
theorem B2039255 : Blo 904575 2039255 := bstep (se 1 (by rfl) ⟨1529441, by rfl⟩ : syracuseStep 2039255 = 3058883) B3058883
theorem B1359371 : Blo 904575 1359371 := bstep (se 1 (by rfl) ⟨1019528, by rfl⟩ : syracuseStep 1359371 = 2039057) B2039057
theorem B2448919 : Blo 904575 2448919 := bstep (se 1 (by rfl) ⟨1836689, by rfl⟩ : syracuseStep 2448919 = 3673379) B3673379
theorem B1359383 : Blo 904575 1359383 := bstep (se 1 (by rfl) ⟨1019537, by rfl⟩ : syracuseStep 1359383 = 2039075) B2039075
theorem B1359449 : Blo 904575 1359449 := bstep (se 2 (by rfl) ⟨509793, by rfl⟩ : syracuseStep 1359449 = 1019587) B1019587
theorem B6528605 : Blo 904575 6528605 := bstep (se 3 (by rfl) ⟨1224113, by rfl⟩ : syracuseStep 6528605 = 2448227) B2448227
theorem B1719947 : Blo 904575 1719947 := bstep (se 1 (by rfl) ⟨1289960, by rfl⟩ : syracuseStep 1719947 = 2579921) B2579921
theorem B2039435 : Blo 904575 2039435 := bstep (se 1 (by rfl) ⟨1529576, by rfl⟩ : syracuseStep 2039435 = 3059153) B3059153
theorem B1449623 : Blo 904575 1449623 := bstep (se 1 (by rfl) ⟨1087217, by rfl⟩ : syracuseStep 1449623 = 2174435) B2174435
theorem B2039489 : Blo 904575 2039489 := bstep (se 2 (by rfl) ⟨764808, by rfl⟩ : syracuseStep 2039489 = 1529617) B1529617
theorem B1359563 : Blo 904575 1359563 := bstep (se 1 (by rfl) ⟨1019672, by rfl⟩ : syracuseStep 1359563 = 2039345) B2039345
theorem B1359575 : Blo 904575 1359575 := bstep (se 1 (by rfl) ⟨1019681, by rfl⟩ : syracuseStep 1359575 = 2039363) B2039363
theorem B1449751 : Blo 904575 1449751 := bstep (se 1 (by rfl) ⟨1087313, by rfl⟩ : syracuseStep 1449751 = 2174627) B2174627
theorem B1359641 : Blo 904575 1359641 := bstep (se 2 (by rfl) ⟨509865, by rfl⟩ : syracuseStep 1359641 = 1019731) B1019731
theorem B917291 : Blo 904575 917291 := bstep (se 1 (by rfl) ⟨687968, by rfl⟩ : syracuseStep 917291 = 1375937) B1375937
theorem B2293555 : Blo 904575 2293555 := bstep (se 1 (by rfl) ⟨1720166, by rfl⟩ : syracuseStep 2293555 = 3440333) B3440333
theorem B1933121 : Blo 904575 1933121 := bstep (se 2 (by rfl) ⟨724920, by rfl⟩ : syracuseStep 1933121 = 1449841) B1449841
theorem B1720129 : Blo 904575 1720129 := bstep (se 2 (by rfl) ⟨645048, by rfl⟩ : syracuseStep 1720129 = 1290097) B1290097
theorem B3440515 : Blo 904575 3440515 := bstep (se 1 (by rfl) ⟨2580386, by rfl⟩ : syracuseStep 3440515 = 5160773) B5160773
theorem B1359755 : Blo 904575 1359755 := bstep (se 1 (by rfl) ⟨1019816, by rfl⟩ : syracuseStep 1359755 = 2039633) B2039633
theorem B1359767 : Blo 904575 1359767 := bstep (se 1 (by rfl) ⟨1019825, by rfl⟩ : syracuseStep 1359767 = 2039651) B2039651
theorem B2039705 : Blo 904575 2039705 := bstep (se 2 (by rfl) ⟨764889, by rfl⟩ : syracuseStep 2039705 = 1529779) B1529779
theorem B6873011 : Blo 904575 6873011 := bstep (se 1 (by rfl) ⟨5154758, by rfl⟩ : syracuseStep 6873011 = 10309517) B10309517
theorem B2293697 : Blo 904575 2293697 := bstep (se 2 (by rfl) ⟨860136, by rfl⟩ : syracuseStep 2293697 = 1720273) B1720273
theorem B1359833 : Blo 904575 1359833 := bstep (se 2 (by rfl) ⟨509937, by rfl⟩ : syracuseStep 1359833 = 1019875) B1019875
theorem B2039795 : Blo 904575 2039795 := bstep (se 1 (by rfl) ⟨1529846, by rfl⟩ : syracuseStep 2039795 = 3059693) B3059693
theorem B4186123 : Blo 904575 4186123 := bstep (se 1 (by rfl) ⟨3139592, by rfl⟩ : syracuseStep 4186123 = 6279185) B6279185
theorem B1720379 : Blo 904575 1720379 := bstep (se 1 (by rfl) ⟨1290284, by rfl⟩ : syracuseStep 1720379 = 2580569) B2580569
theorem B4579415 : Blo 904575 4579415 := bstep (se 1 (by rfl) ⟨3434561, by rfl⟩ : syracuseStep 4579415 = 6869123) B6869123
theorem B2293879 : Blo 904575 2293879 := bstep (se 1 (by rfl) ⟨1720409, by rfl⟩ : syracuseStep 2293879 = 3440819) B3440819
theorem B1376399 : Blo 904575 1376399 := bstep (se 1 (by rfl) ⟨1032299, by rfl⟩ : syracuseStep 1376399 = 2064599) B2064599
theorem B1147051 : Blo 904575 1147051 := bstep (se 1 (by rfl) ⟨860288, by rfl⟩ : syracuseStep 1147051 = 1720577) B1720577
theorem B8708269 : Blo 904575 8708269 := bstep (se 3 (by rfl) ⟨1632800, by rfl⟩ : syracuseStep 8708269 = 3265601) B3265601
theorem B2580751 : Blo 904575 2580751 := bstep (se 1 (by rfl) ⟨1935563, by rfl⟩ : syracuseStep 2580751 = 3871127) B3871127
theorem B2580797 : Blo 904575 2580797 := bstep (se 3 (by rfl) ⟨483899, by rfl⟩ : syracuseStep 2580797 = 967799) B967799
theorem B1147279 : Blo 904575 1147279 := bstep (se 1 (by rfl) ⟨860459, by rfl⟩ : syracuseStep 1147279 = 1720919) B1720919
theorem B3482041 : Blo 904575 3482041 := bstep (se 2 (by rfl) ⟨1305765, by rfl⟩ : syracuseStep 3482041 = 2611531) B2611531
theorem B1933753 : Blo 904575 1933753 := bstep (se 2 (by rfl) ⟨725157, by rfl⟩ : syracuseStep 1933753 = 1450315) B1450315
theorem B1720865 : Blo 904575 1720865 := bstep (se 2 (by rfl) ⟨645324, by rfl⟩ : syracuseStep 1720865 = 1290649) B1290649
theorem B2294315 : Blo 904575 2294315 := bstep (se 1 (by rfl) ⟨1720736, by rfl⟩ : syracuseStep 2294315 = 3441473) B3441473
theorem B4579901 : Blo 904575 4579901 := bstep (se 3 (by rfl) ⟨858731, by rfl⟩ : syracuseStep 4579901 = 1717463) B1717463
theorem B2581139 : Blo 904575 2581139 := bstep (se 1 (by rfl) ⟨1935854, by rfl⟩ : syracuseStep 2581139 = 3871709) B3871709
theorem B52363957 : Blo 904575 52363957 := bstep (se 5 (by rfl) ⟨2454560, by rfl⟩ : syracuseStep 52363957 = 4909121) B4909121
theorem B1721017 : Blo 904575 1721017 := bstep (se 2 (by rfl) ⟨645381, by rfl⟩ : syracuseStep 1721017 = 1290763) B1290763
theorem B2900681 : Blo 904575 2900681 := bstep (se 2 (by rfl) ⟨1087755, by rfl⟩ : syracuseStep 2900681 = 2175511) B2175511
theorem B6521573 : Blo 904575 6521573 := bstep (se 4 (by rfl) ⟨611397, by rfl⟩ : syracuseStep 6521573 = 1222795) B1222795
theorem B3056399 : Blo 904575 3056399 := bstep (se 1 (by rfl) ⟨2292299, by rfl⟩ : syracuseStep 3056399 = 4584599) B4584599
theorem B11027249 : Blo 904575 11027249 := bstep (se 2 (by rfl) ⟨4135218, by rfl⟩ : syracuseStep 11027249 = 8270437) B8270437
theorem B5161913 : Blo 904575 5161913 := bstep (se 2 (by rfl) ⟨1935717, by rfl⟩ : syracuseStep 5161913 = 3871435) B3871435
theorem B1934351 : Blo 904575 1934351 := bstep (se 1 (by rfl) ⟨1450763, by rfl⟩ : syracuseStep 1934351 = 2901527) B2901527
theorem B3056669 : Blo 904575 3056669 := bstep (se 3 (by rfl) ⟨573125, by rfl⟩ : syracuseStep 3056669 = 1146251) B1146251
theorem B3868019 : Blo 904575 3868019 := bstep (se 1 (by rfl) ⟨2901014, by rfl⟩ : syracuseStep 3868019 = 5802029) B5802029
theorem B4130201 : Blo 904575 4130201 := bstep (se 2 (by rfl) ⟨1548825, by rfl⟩ : syracuseStep 4130201 = 3097651) B3097651
theorem B3671563 : Blo 904575 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B39142925 : Blo 904575 39142925 := bstep (se 3 (by rfl) ⟨7339298, by rfl⟩ : syracuseStep 39142925 = 14678597) B14678597
theorem B4130347 : Blo 904575 4130347 := bstep (se 1 (by rfl) ⟨3097760, by rfl⟩ : syracuseStep 4130347 = 6195521) B6195521
theorem B8701505 : Blo 904575 8701505 := bstep (se 2 (by rfl) ⟨3263064, by rfl⟩ : syracuseStep 8701505 = 6526129) B6526129
theorem B6964813 : Blo 904575 6964813 := bstep (se 3 (by rfl) ⟨1305902, by rfl⟩ : syracuseStep 6964813 = 2611805) B2611805
theorem B17409613 : Blo 904575 17409613 := bstep (se 3 (by rfl) ⟨3264302, by rfl⟩ : syracuseStep 17409613 = 6528605) B6528605
theorem B7743347 : Blo 904575 7743347 := bstep (se 1 (by rfl) ⟨5807510, by rfl⟩ : syracuseStep 7743347 = 11615021) B11615021
theorem B2942855 : Blo 904575 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B4589459 : Blo 904575 4589459 := bstep (se 1 (by rfl) ⟨3442094, by rfl⟩ : syracuseStep 4589459 = 6884189) B6884189
theorem B2615225 : Blo 904575 2615225 := bstep (se 2 (by rfl) ⟨980709, by rfl⟩ : syracuseStep 2615225 = 1961419) B1961419
theorem B1017787 : Blo 904575 1017787 := bstep (se 1 (by rfl) ⟨763340, by rfl⟩ : syracuseStep 1017787 = 1526681) B1526681
theorem B993211 : Blo 904575 993211 := bstep (se 1 (by rfl) ⟨744908, by rfl⟩ : syracuseStep 993211 = 1489817) B1489817
theorem B4581683 : Blo 904575 4581683 := bstep (se 1 (by rfl) ⟨3436262, by rfl⟩ : syracuseStep 4581683 = 6872525) B6872525
theorem B5155123 : Blo 904575 5155123 := bstep (se 1 (by rfl) ⟨3866342, by rfl⟩ : syracuseStep 5155123 = 7732685) B7732685
theorem B1018255 : Blo 904575 1018255 := bstep (se 1 (by rfl) ⟨763691, by rfl⟩ : syracuseStep 1018255 = 1527383) B1527383
theorem B3058073 : Blo 904575 3058073 := bstep (se 2 (by rfl) ⟨1146777, by rfl⟩ : syracuseStep 3058073 = 2293555) B2293555
theorem B1935905 : Blo 904575 1935905 := bstep (se 2 (by rfl) ⟨725964, by rfl⟩ : syracuseStep 1935905 = 1451929) B1451929
theorem B1288747 : Blo 904575 1288747 := bstep (se 1 (by rfl) ⟨966560, by rfl⟩ : syracuseStep 1288747 = 1933121) B1933121
theorem B13060673 : Blo 904575 13060673 := bstep (se 2 (by rfl) ⟨4897752, by rfl⟩ : syracuseStep 13060673 = 9795505) B9795505
theorem B4582007 : Blo 904575 4582007 := bstep (se 1 (by rfl) ⟨3436505, by rfl⟩ : syracuseStep 4582007 = 6873011) B6873011
theorem B1935991 : Blo 904575 1935991 := bstep (se 1 (by rfl) ⟨1451993, by rfl⟩ : syracuseStep 1935991 = 2903987) B2903987
theorem B8260289 : Blo 904575 8260289 := bstep (se 2 (by rfl) ⟨3097608, by rfl⟩ : syracuseStep 8260289 = 6195217) B6195217
theorem B1288975 : Blo 904575 1288975 := bstep (se 1 (by rfl) ⟨966731, by rfl⟩ : syracuseStep 1288975 = 1933463) B1933463
theorem B13060901 : Blo 904575 13060901 := bstep (se 4 (by rfl) ⟨1224459, by rfl⟩ : syracuseStep 13060901 = 2448919) B2448919
theorem B5507929 : Blo 904575 5507929 := bstep (se 2 (by rfl) ⟨2065473, by rfl⟩ : syracuseStep 5507929 = 4130947) B4130947
theorem B18590579 : Blo 904575 18590579 := bstep (se 1 (by rfl) ⟨13942934, by rfl⟩ : syracuseStep 18590579 = 27885869) B27885869
theorem B1526647 : Blo 904575 1526647 := bstep (se 1 (by rfl) ⟨1144985, by rfl⟩ : syracuseStep 1526647 = 2289971) B2289971
theorem B1018759 : Blo 904575 1018759 := bstep (se 1 (by rfl) ⟨764069, by rfl⟩ : syracuseStep 1018759 = 1528139) B1528139
theorem B31771541 : Blo 904575 31771541 := bstep (se 6 (by rfl) ⟨744645, by rfl⟩ : syracuseStep 31771541 = 1489291) B1489291
theorem B7744409 : Blo 904575 7744409 := bstep (se 2 (by rfl) ⟨2904153, by rfl⟩ : syracuseStep 7744409 = 5808307) B5808307
theorem B3435473 : Blo 904575 3435473 := bstep (se 2 (by rfl) ⟨1288302, by rfl⟩ : syracuseStep 3435473 = 2576605) B2576605
theorem B1526843 : Blo 904575 1526843 := bstep (se 1 (by rfl) ⟨1145132, by rfl⟩ : syracuseStep 1526843 = 2290265) B2290265
theorem B1018939 : Blo 904575 1018939 := bstep (se 1 (by rfl) ⟨764204, by rfl⟩ : syracuseStep 1018939 = 1528409) B1528409
theorem B3058775 : Blo 904575 3058775 := bstep (se 1 (by rfl) ⟨2294081, by rfl⟩ : syracuseStep 3058775 = 4588163) B4588163
theorem B904583 : Blo 904575 904583 := bstep (se 1 (by rfl) ⟨678437, by rfl⟩ : syracuseStep 904583 = 1356875) B1356875
theorem B904591 : Blo 904575 904591 := bstep (se 1 (by rfl) ⟨678443, by rfl⟩ : syracuseStep 904591 = 1356887) B1356887
theorem B3435929 : Blo 904575 3435929 := bstep (se 2 (by rfl) ⟨1288473, by rfl⟩ : syracuseStep 3435929 = 2576947) B2576947
theorem B904635 : Blo 904575 904635 := bstep (se 1 (by rfl) ⟨678476, by rfl⟩ : syracuseStep 904635 = 1356953) B1356953
theorem B1527241 : Blo 904575 1527241 := bstep (se 2 (by rfl) ⟨572715, by rfl⟩ : syracuseStep 1527241 = 1145431) B1145431
theorem B904711 : Blo 904575 904711 := bstep (se 1 (by rfl) ⟨678533, by rfl⟩ : syracuseStep 904711 = 1357067) B1357067
theorem B904719 : Blo 904575 904719 := bstep (se 1 (by rfl) ⟨678539, by rfl⟩ : syracuseStep 904719 = 1357079) B1357079
theorem B1019407 : Blo 904575 1019407 := bstep (se 1 (by rfl) ⟨764555, by rfl⟩ : syracuseStep 1019407 = 1529111) B1529111
theorem B904763 : Blo 904575 904763 := bstep (se 1 (by rfl) ⟨678572, by rfl⟩ : syracuseStep 904763 = 1357145) B1357145
theorem B3059261 : Blo 904575 3059261 := bstep (se 3 (by rfl) ⟨573611, by rfl⟩ : syracuseStep 3059261 = 1147223) B1147223
theorem B4582979 : Blo 904575 4582979 := bstep (se 1 (by rfl) ⟨3437234, by rfl⟩ : syracuseStep 4582979 = 6874469) B6874469
theorem B904839 : Blo 904575 904839 := bstep (se 1 (by rfl) ⟨678629, by rfl⟩ : syracuseStep 904839 = 1357259) B1357259
theorem B904847 : Blo 904575 904847 := bstep (se 1 (by rfl) ⟨678635, by rfl⟩ : syracuseStep 904847 = 1357271) B1357271
theorem B2035385 : Blo 904575 2035385 := bstep (se 2 (by rfl) ⟨763269, by rfl⟩ : syracuseStep 2035385 = 1526539) B1526539
theorem B904891 : Blo 904575 904891 := bstep (se 1 (by rfl) ⟨678668, by rfl⟩ : syracuseStep 904891 = 1357337) B1357337
theorem B5508809 : Blo 904575 5508809 := bstep (se 2 (by rfl) ⟨2065803, by rfl⟩ : syracuseStep 5508809 = 4131607) B4131607
theorem B5156581 : Blo 904575 5156581 := bstep (se 4 (by rfl) ⟨483429, by rfl⟩ : syracuseStep 5156581 = 966859) B966859
theorem B904967 : Blo 904575 904967 := bstep (se 1 (by rfl) ⟨678725, by rfl⟩ : syracuseStep 904967 = 1357451) B1357451
theorem B904975 : Blo 904575 904975 := bstep (se 1 (by rfl) ⟨678731, by rfl⟩ : syracuseStep 904975 = 1357463) B1357463
theorem B905019 : Blo 904575 905019 := bstep (se 1 (by rfl) ⟨678764, by rfl⟩ : syracuseStep 905019 = 1357529) B1357529
theorem B905095 : Blo 904575 905095 := bstep (se 1 (by rfl) ⟨678821, by rfl⟩ : syracuseStep 905095 = 1357643) B1357643
theorem B4583303 : Blo 904575 4583303 := bstep (se 1 (by rfl) ⟨3437477, by rfl⟩ : syracuseStep 4583303 = 6874955) B6874955
theorem B905103 : Blo 904575 905103 := bstep (se 1 (by rfl) ⟨678827, by rfl⟩ : syracuseStep 905103 = 1357655) B1357655
theorem B905147 : Blo 904575 905147 := bstep (se 1 (by rfl) ⟨678860, by rfl⟩ : syracuseStep 905147 = 1357721) B1357721
theorem B905223 : Blo 904575 905223 := bstep (se 1 (by rfl) ⟨678917, by rfl⟩ : syracuseStep 905223 = 1357835) B1357835
theorem B2035727 : Blo 904575 2035727 := bstep (se 1 (by rfl) ⟨1526795, by rfl⟩ : syracuseStep 2035727 = 3053591) B3053591
theorem B905231 : Blo 904575 905231 := bstep (se 1 (by rfl) ⟨678923, by rfl⟩ : syracuseStep 905231 = 1357847) B1357847
theorem B2035745 : Blo 904575 2035745 := bstep (se 2 (by rfl) ⟨763404, by rfl⟩ : syracuseStep 2035745 = 1526809) B1526809
theorem B905275 : Blo 904575 905275 := bstep (se 1 (by rfl) ⟨678956, by rfl⟩ : syracuseStep 905275 = 1357913) B1357913
theorem B2289779 : Blo 904575 2289779 := bstep (se 1 (by rfl) ⟨1717334, by rfl⟩ : syracuseStep 2289779 = 3434669) B3434669
theorem B905351 : Blo 904575 905351 := bstep (se 1 (by rfl) ⟨679013, by rfl⟩ : syracuseStep 905351 = 1358027) B1358027
theorem B1527943 : Blo 904575 1527943 := bstep (se 1 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 1527943 = 2291915) B2291915
theorem B905359 : Blo 904575 905359 := bstep (se 1 (by rfl) ⟨679019, by rfl⟩ : syracuseStep 905359 = 1358039) B1358039
theorem B905403 : Blo 904575 905403 := bstep (se 1 (by rfl) ⟨679052, by rfl⟩ : syracuseStep 905403 = 1358105) B1358105
theorem B6877385 : Blo 904575 6877385 := bstep (se 2 (by rfl) ⟨2579019, by rfl⟩ : syracuseStep 6877385 = 5158039) B5158039
theorem B4354249 : Blo 904575 4354249 := bstep (se 2 (by rfl) ⟨1632843, by rfl⟩ : syracuseStep 4354249 = 3265687) B3265687
theorem B15470837 : Blo 904575 15470837 := bstep (se 5 (by rfl) ⟨725195, by rfl⟩ : syracuseStep 15470837 = 1450391) B1450391
theorem B905479 : Blo 904575 905479 := bstep (se 1 (by rfl) ⟨679109, by rfl⟩ : syracuseStep 905479 = 1358219) B1358219
theorem B905487 : Blo 904575 905487 := bstep (se 1 (by rfl) ⟨679115, by rfl⟩ : syracuseStep 905487 = 1358231) B1358231
theorem B905531 : Blo 904575 905531 := bstep (se 1 (by rfl) ⟨679148, by rfl⟩ : syracuseStep 905531 = 1358297) B1358297
theorem B2036087 : Blo 904575 2036087 := bstep (se 1 (by rfl) ⟨1527065, by rfl⟩ : syracuseStep 2036087 = 3054131) B3054131
theorem B905607 : Blo 904575 905607 := bstep (se 1 (by rfl) ⟨679205, by rfl⟩ : syracuseStep 905607 = 1358411) B1358411
theorem B3871111 : Blo 904575 3871111 := bstep (se 1 (by rfl) ⟨2903333, by rfl⟩ : syracuseStep 3871111 = 5806667) B5806667
theorem B905615 : Blo 904575 905615 := bstep (se 1 (by rfl) ⟨679211, by rfl⟩ : syracuseStep 905615 = 1358423) B1358423
theorem B5804435 : Blo 904575 5804435 := bstep (se 1 (by rfl) ⟨4353326, by rfl⟩ : syracuseStep 5804435 = 8706653) B8706653
theorem B10318265 : Blo 904575 10318265 := bstep (se 2 (by rfl) ⟨3869349, by rfl⟩ : syracuseStep 10318265 = 7738699) B7738699
theorem B905659 : Blo 904575 905659 := bstep (se 1 (by rfl) ⟨679244, by rfl⟩ : syracuseStep 905659 = 1358489) B1358489
theorem B905735 : Blo 904575 905735 := bstep (se 1 (by rfl) ⟨679301, by rfl⟩ : syracuseStep 905735 = 1358603) B1358603
theorem B905743 : Blo 904575 905743 := bstep (se 1 (by rfl) ⟨679307, by rfl⟩ : syracuseStep 905743 = 1358615) B1358615
theorem B59609621 : Blo 904575 59609621 := bstep (se 6 (by rfl) ⟨1397100, by rfl⟩ : syracuseStep 59609621 = 2794201) B2794201
theorem B2036267 : Blo 904575 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B3437099 : Blo 904575 3437099 := bstep (se 1 (by rfl) ⟨2577824, by rfl⟩ : syracuseStep 3437099 = 5155649) B5155649
theorem B905787 : Blo 904575 905787 := bstep (se 1 (by rfl) ⟨679340, by rfl⟩ : syracuseStep 905787 = 1358681) B1358681
theorem B2290295 : Blo 904575 2290295 := bstep (se 1 (by rfl) ⟨1717721, by rfl⟩ : syracuseStep 2290295 = 3435443) B3435443
theorem B905863 : Blo 904575 905863 := bstep (se 1 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 905863 = 1358795) B1358795
theorem B905871 : Blo 904575 905871 := bstep (se 1 (by rfl) ⟨679403, by rfl⟩ : syracuseStep 905871 = 1358807) B1358807
theorem B905915 : Blo 904575 905915 := bstep (se 1 (by rfl) ⟨679436, by rfl⟩ : syracuseStep 905915 = 1358873) B1358873
theorem B3871469 : Blo 904575 3871469 := bstep (se 3 (by rfl) ⟨725900, by rfl⟩ : syracuseStep 3871469 = 1451801) B1451801
theorem B905991 : Blo 904575 905991 := bstep (se 1 (by rfl) ⟨679493, by rfl⟩ : syracuseStep 905991 = 1358987) B1358987
theorem B1528591 : Blo 904575 1528591 := bstep (se 1 (by rfl) ⟨1146443, by rfl⟩ : syracuseStep 1528591 = 2292887) B2292887
theorem B905999 : Blo 904575 905999 := bstep (se 1 (by rfl) ⟨679499, by rfl⟩ : syracuseStep 905999 = 1358999) B1358999
theorem B2446109 : Blo 904575 2446109 := bstep (se 3 (by rfl) ⟨458645, by rfl⟩ : syracuseStep 2446109 = 917291) B917291
theorem B906043 : Blo 904575 906043 := bstep (se 1 (by rfl) ⟨679532, by rfl⟩ : syracuseStep 906043 = 1359065) B1359065
theorem B906119 : Blo 904575 906119 := bstep (se 1 (by rfl) ⟨679589, by rfl⟩ : syracuseStep 906119 = 1359179) B1359179
theorem B906127 : Blo 904575 906127 := bstep (se 1 (by rfl) ⟨679595, by rfl⟩ : syracuseStep 906127 = 1359191) B1359191
theorem B2036627 : Blo 904575 2036627 := bstep (se 1 (by rfl) ⟨1527470, by rfl⟩ : syracuseStep 2036627 = 3054941) B3054941
theorem B906171 : Blo 904575 906171 := bstep (se 1 (by rfl) ⟨679628, by rfl⟩ : syracuseStep 906171 = 1359257) B1359257
theorem B2036681 : Blo 904575 2036681 := bstep (se 2 (by rfl) ⟨763755, by rfl⟩ : syracuseStep 2036681 = 1527511) B1527511
theorem B906247 : Blo 904575 906247 := bstep (se 1 (by rfl) ⟨679685, by rfl⟩ : syracuseStep 906247 = 1359371) B1359371
theorem B906255 : Blo 904575 906255 := bstep (se 1 (by rfl) ⟨679691, by rfl⟩ : syracuseStep 906255 = 1359383) B1359383
theorem B906299 : Blo 904575 906299 := bstep (se 1 (by rfl) ⟨679724, by rfl⟩ : syracuseStep 906299 = 1359449) B1359449
theorem B1356935 : Blo 904575 1356935 := bstep (se 1 (by rfl) ⟨1017701, by rfl⟩ : syracuseStep 1356935 = 2035403) B2035403
theorem B906375 : Blo 904575 906375 := bstep (se 1 (by rfl) ⟨679781, by rfl⟩ : syracuseStep 906375 = 1359563) B1359563
theorem B906383 : Blo 904575 906383 := bstep (se 1 (by rfl) ⟨679787, by rfl⟩ : syracuseStep 906383 = 1359575) B1359575
theorem B1356971 : Blo 904575 1356971 := bstep (se 1 (by rfl) ⟨1017728, by rfl⟩ : syracuseStep 1356971 = 2035457) B2035457
theorem B1717433 : Blo 904575 1717433 := bstep (se 2 (by rfl) ⟨644037, by rfl⟩ : syracuseStep 1717433 = 1288075) B1288075
theorem B906427 : Blo 904575 906427 := bstep (se 1 (by rfl) ⟨679820, by rfl⟩ : syracuseStep 906427 = 1359641) B1359641
theorem B1357001 : Blo 904575 1357001 := bstep (se 2 (by rfl) ⟨508875, by rfl⟩ : syracuseStep 1357001 = 1017751) B1017751
theorem B4355309 : Blo 904575 4355309 := bstep (se 3 (by rfl) ⟨816620, by rfl⟩ : syracuseStep 4355309 = 1633241) B1633241
theorem B906503 : Blo 904575 906503 := bstep (se 1 (by rfl) ⟨679877, by rfl⟩ : syracuseStep 906503 = 1359755) B1359755
theorem B2176271 : Blo 904575 2176271 := bstep (se 1 (by rfl) ⟨1632203, by rfl⟩ : syracuseStep 2176271 = 3264407) B3264407
theorem B906511 : Blo 904575 906511 := bstep (se 1 (by rfl) ⟨679883, by rfl⟩ : syracuseStep 906511 = 1359767) B1359767
theorem B1529131 : Blo 904575 1529131 := bstep (se 1 (by rfl) ⟨1146848, by rfl⟩ : syracuseStep 1529131 = 2293697) B2293697
theorem B1357115 : Blo 904575 1357115 := bstep (se 1 (by rfl) ⟨1017836, by rfl⟩ : syracuseStep 1357115 = 2035673) B2035673
theorem B906555 : Blo 904575 906555 := bstep (se 1 (by rfl) ⟨679916, by rfl⟩ : syracuseStep 906555 = 1359833) B1359833
theorem B1357175 : Blo 904575 1357175 := bstep (se 1 (by rfl) ⟨1017881, by rfl⟩ : syracuseStep 1357175 = 2035763) B2035763
theorem B1357199 : Blo 904575 1357199 := bstep (se 1 (by rfl) ⟨1017899, by rfl⟩ : syracuseStep 1357199 = 2035799) B2035799
theorem B1357241 : Blo 904575 1357241 := bstep (se 2 (by rfl) ⟨508965, by rfl⟩ : syracuseStep 1357241 = 1017931) B1017931
theorem B1529273 : Blo 904575 1529273 := bstep (se 2 (by rfl) ⟨573477, by rfl⟩ : syracuseStep 1529273 = 1146955) B1146955
theorem B1357319 : Blo 904575 1357319 := bstep (se 1 (by rfl) ⟨1017989, by rfl⟩ : syracuseStep 1357319 = 2035979) B2035979
theorem B1357355 : Blo 904575 1357355 := bstep (se 1 (by rfl) ⟨1018016, by rfl⟩ : syracuseStep 1357355 = 2036033) B2036033
theorem B1357385 : Blo 904575 1357385 := bstep (se 2 (by rfl) ⟨509019, by rfl⟩ : syracuseStep 1357385 = 1018039) B1018039
theorem B2291287 : Blo 904575 2291287 := bstep (se 1 (by rfl) ⟨1718465, by rfl⟩ : syracuseStep 2291287 = 3436931) B3436931
theorem B2578007 : Blo 904575 2578007 := bstep (se 1 (by rfl) ⟨1933505, by rfl⟩ : syracuseStep 2578007 = 3867011) B3867011
theorem B2037383 : Blo 904575 2037383 := bstep (se 1 (by rfl) ⟨1528037, by rfl⟩ : syracuseStep 2037383 = 3056075) B3056075
theorem B980623 : Blo 904575 980623 := bstep (se 1 (by rfl) ⟨735467, by rfl⟩ : syracuseStep 980623 = 1470935) B1470935
theorem B1357499 : Blo 904575 1357499 := bstep (se 1 (by rfl) ⟨1018124, by rfl⟩ : syracuseStep 1357499 = 2036249) B2036249
theorem B1357559 : Blo 904575 1357559 := bstep (se 1 (by rfl) ⟨1018169, by rfl⟩ : syracuseStep 1357559 = 2036339) B2036339
theorem B1357583 : Blo 904575 1357583 := bstep (se 1 (by rfl) ⟨1018187, by rfl⟩ : syracuseStep 1357583 = 2036375) B2036375
theorem B5797669 : Blo 904575 5797669 := bstep (se 4 (by rfl) ⟨543531, by rfl⟩ : syracuseStep 5797669 = 1087063) B1087063
theorem B2447147 : Blo 904575 2447147 := bstep (se 1 (by rfl) ⟨1835360, by rfl⟩ : syracuseStep 2447147 = 3670721) B3670721
theorem B1357625 : Blo 904575 1357625 := bstep (se 2 (by rfl) ⟨509109, by rfl⟩ : syracuseStep 1357625 = 1018219) B1018219
theorem B2037563 : Blo 904575 2037563 := bstep (se 1 (by rfl) ⟨1528172, by rfl⟩ : syracuseStep 2037563 = 3056345) B3056345
theorem B17872757 : Blo 904575 17872757 := bstep (se 5 (by rfl) ⟨837785, by rfl⟩ : syracuseStep 17872757 = 1675571) B1675571
theorem B1357703 : Blo 904575 1357703 := bstep (se 1 (by rfl) ⟨1018277, by rfl⟩ : syracuseStep 1357703 = 2036555) B2036555
theorem B2291591 : Blo 904575 2291591 := bstep (se 1 (by rfl) ⟨1718693, by rfl⟩ : syracuseStep 2291591 = 3437387) B3437387
theorem B1357739 : Blo 904575 1357739 := bstep (se 1 (by rfl) ⟨1018304, by rfl⟩ : syracuseStep 1357739 = 2036609) B2036609
theorem B2037689 : Blo 904575 2037689 := bstep (se 2 (by rfl) ⟨764133, by rfl⟩ : syracuseStep 2037689 = 1528267) B1528267
theorem B1357769 : Blo 904575 1357769 := bstep (se 2 (by rfl) ⟨509163, by rfl⟩ : syracuseStep 1357769 = 1018327) B1018327
theorem B1103863 : Blo 904575 1103863 := bstep (se 1 (by rfl) ⟨827897, by rfl⟩ : syracuseStep 1103863 = 1655795) B1655795
theorem B2291723 : Blo 904575 2291723 := bstep (se 1 (by rfl) ⟨1718792, by rfl⟩ : syracuseStep 2291723 = 3437585) B3437585
theorem B1357883 : Blo 904575 1357883 := bstep (se 1 (by rfl) ⟨1018412, by rfl⟩ : syracuseStep 1357883 = 2036825) B2036825
theorem B7731287 : Blo 904575 7731287 := bstep (se 1 (by rfl) ⟨5798465, by rfl⟩ : syracuseStep 7731287 = 11596931) B11596931
theorem B16750709 : Blo 904575 16750709 := bstep (se 5 (by rfl) ⟨785189, by rfl⟩ : syracuseStep 16750709 = 1570379) B1570379
theorem B2938999 : Blo 904575 2938999 := bstep (se 1 (by rfl) ⟨2204249, by rfl⟩ : syracuseStep 2938999 = 4408499) B4408499
theorem B1357943 : Blo 904575 1357943 := bstep (se 1 (by rfl) ⟨1018457, by rfl⟩ : syracuseStep 1357943 = 2036915) B2036915
theorem B7846021 : Blo 904575 7846021 := bstep (se 4 (by rfl) ⟨735564, by rfl⟩ : syracuseStep 7846021 = 1471129) B1471129
theorem B1357967 : Blo 904575 1357967 := bstep (se 1 (by rfl) ⟨1018475, by rfl⟩ : syracuseStep 1357967 = 2036951) B2036951
theorem B1358009 : Blo 904575 1358009 := bstep (se 2 (by rfl) ⟨509253, by rfl⟩ : syracuseStep 1358009 = 1018507) B1018507
theorem B1358087 : Blo 904575 1358087 := bstep (se 1 (by rfl) ⟨1018565, by rfl⟩ : syracuseStep 1358087 = 2037131) B2037131
theorem B2038031 : Blo 904575 2038031 := bstep (se 1 (by rfl) ⟨1528523, by rfl⟩ : syracuseStep 2038031 = 3057047) B3057047
theorem B2038049 : Blo 904575 2038049 := bstep (se 2 (by rfl) ⟨764268, by rfl⟩ : syracuseStep 2038049 = 1528537) B1528537
theorem B1358123 : Blo 904575 1358123 := bstep (se 1 (by rfl) ⟨1018592, by rfl⟩ : syracuseStep 1358123 = 2037185) B2037185
theorem B1718587 : Blo 904575 1718587 := bstep (se 1 (by rfl) ⟨1288940, by rfl⟩ : syracuseStep 1718587 = 2577881) B2577881
theorem B1358153 : Blo 904575 1358153 := bstep (se 2 (by rfl) ⟨509307, by rfl⟩ : syracuseStep 1358153 = 1018615) B1018615
theorem B5159315 : Blo 904575 5159315 := bstep (se 1 (by rfl) ⟨3869486, by rfl⟩ : syracuseStep 5159315 = 7738973) B7738973
theorem B3971513 : Blo 904575 3971513 := bstep (se 2 (by rfl) ⟨1489317, by rfl⟩ : syracuseStep 3971513 = 2978635) B2978635
theorem B9066937 : Blo 904575 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B1358267 : Blo 904575 1358267 := bstep (se 1 (by rfl) ⟨1018700, by rfl⟩ : syracuseStep 1358267 = 2037401) B2037401
theorem B3439057 : Blo 904575 3439057 := bstep (se 2 (by rfl) ⟨1289646, by rfl⟩ : syracuseStep 3439057 = 2579293) B2579293
theorem B1145335 : Blo 904575 1145335 := bstep (se 1 (by rfl) ⟨859001, by rfl⟩ : syracuseStep 1145335 = 1718003) B1718003
theorem B1358327 : Blo 904575 1358327 := bstep (se 1 (by rfl) ⟨1018745, by rfl⟩ : syracuseStep 1358327 = 2037491) B2037491
theorem B8264195 : Blo 904575 8264195 := bstep (se 1 (by rfl) ⟨6198146, by rfl⟩ : syracuseStep 8264195 = 12396293) B12396293
theorem B1358351 : Blo 904575 1358351 := bstep (se 1 (by rfl) ⟨1018763, by rfl⟩ : syracuseStep 1358351 = 2037527) B2037527
theorem B2292239 : Blo 904575 2292239 := bstep (se 1 (by rfl) ⟨1719179, by rfl⟩ : syracuseStep 2292239 = 3438359) B3438359
theorem B1358393 : Blo 904575 1358393 := bstep (se 2 (by rfl) ⟨509397, by rfl⟩ : syracuseStep 1358393 = 1018795) B1018795
theorem B4897367 : Blo 904575 4897367 := bstep (se 1 (by rfl) ⟨3673025, by rfl⟩ : syracuseStep 4897367 = 7346051) B7346051
theorem B2038391 : Blo 904575 2038391 := bstep (se 1 (by rfl) ⟨1528793, by rfl⟩ : syracuseStep 2038391 = 3057587) B3057587
theorem B1358471 : Blo 904575 1358471 := bstep (se 1 (by rfl) ⟨1018853, by rfl⟩ : syracuseStep 1358471 = 2037707) B2037707
theorem B2292371 : Blo 904575 2292371 := bstep (se 1 (by rfl) ⟨1719278, by rfl⟩ : syracuseStep 2292371 = 3438557) B3438557
theorem B1358507 : Blo 904575 1358507 := bstep (se 1 (by rfl) ⟨1018880, by rfl⟩ : syracuseStep 1358507 = 2037761) B2037761
theorem B1358537 : Blo 904575 1358537 := bstep (se 2 (by rfl) ⟨509451, by rfl⟩ : syracuseStep 1358537 = 1018903) B1018903
theorem B3439361 : Blo 904575 3439361 := bstep (se 2 (by rfl) ⟨1289760, by rfl⟩ : syracuseStep 3439361 = 2579521) B2579521
theorem B1719073 : Blo 904575 1719073 := bstep (se 2 (by rfl) ⟨644652, by rfl⟩ : syracuseStep 1719073 = 1289305) B1289305
theorem B2038571 : Blo 904575 2038571 := bstep (se 1 (by rfl) ⟨1528928, by rfl⟩ : syracuseStep 2038571 = 3057857) B3057857
theorem B1145659 : Blo 904575 1145659 := bstep (se 1 (by rfl) ⟨859244, by rfl⟩ : syracuseStep 1145659 = 1718489) B1718489
theorem B1358651 : Blo 904575 1358651 := bstep (se 1 (by rfl) ⟨1018988, by rfl⟩ : syracuseStep 1358651 = 2037977) B2037977
theorem B1358711 : Blo 904575 1358711 := bstep (se 1 (by rfl) ⟨1019033, by rfl⟩ : syracuseStep 1358711 = 2038067) B2038067
theorem B2898823 : Blo 904575 2898823 := bstep (se 1 (by rfl) ⟨2174117, by rfl⟩ : syracuseStep 2898823 = 4348235) B4348235
theorem B1358735 : Blo 904575 1358735 := bstep (se 1 (by rfl) ⟨1019051, by rfl⟩ : syracuseStep 1358735 = 2038103) B2038103
theorem B1358777 : Blo 904575 1358777 := bstep (se 2 (by rfl) ⟨509541, by rfl⟩ : syracuseStep 1358777 = 1019083) B1019083
theorem B1358855 : Blo 904575 1358855 := bstep (se 1 (by rfl) ⟨1019141, by rfl⟩ : syracuseStep 1358855 = 2038283) B2038283
theorem B1358891 : Blo 904575 1358891 := bstep (se 1 (by rfl) ⟨1019168, by rfl⟩ : syracuseStep 1358891 = 2038337) B2038337
theorem B1358921 : Blo 904575 1358921 := bstep (se 2 (by rfl) ⟨509595, by rfl⟩ : syracuseStep 1358921 = 1019191) B1019191
theorem B5160023 : Blo 904575 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B2038931 : Blo 904575 2038931 := bstep (se 1 (by rfl) ⟨1529198, by rfl⟩ : syracuseStep 2038931 = 3058397) B3058397
theorem B1359035 : Blo 904575 1359035 := bstep (se 1 (by rfl) ⟨1019276, by rfl⟩ : syracuseStep 1359035 = 2038553) B2038553
theorem B3439817 : Blo 904575 3439817 := bstep (se 2 (by rfl) ⟨1289931, by rfl⟩ : syracuseStep 3439817 = 2579863) B2579863
theorem B2038985 : Blo 904575 2038985 := bstep (se 2 (by rfl) ⟨764619, by rfl⟩ : syracuseStep 2038985 = 1529239) B1529239
theorem B5807305 : Blo 904575 5807305 := bstep (se 2 (by rfl) ⟨2177739, by rfl⟩ : syracuseStep 5807305 = 4355479) B4355479
theorem B1359095 : Blo 904575 1359095 := bstep (se 1 (by rfl) ⟨1019321, by rfl⟩ : syracuseStep 1359095 = 2038643) B2038643
theorem B1359119 : Blo 904575 1359119 := bstep (se 1 (by rfl) ⟨1019339, by rfl⟩ : syracuseStep 1359119 = 2038679) B2038679
theorem B1359161 : Blo 904575 1359161 := bstep (se 2 (by rfl) ⟨509685, by rfl⟩ : syracuseStep 1359161 = 1019371) B1019371
theorem B1375547 : Blo 904575 1375547 := bstep (se 1 (by rfl) ⟨1031660, by rfl⟩ : syracuseStep 1375547 = 2063321) B2063321
theorem B4586867 : Blo 904575 4586867 := bstep (se 1 (by rfl) ⟨3440150, by rfl⟩ : syracuseStep 4586867 = 6880301) B6880301
theorem B1359239 : Blo 904575 1359239 := bstep (se 1 (by rfl) ⟨1019429, by rfl⟩ : syracuseStep 1359239 = 2038859) B2038859
theorem B3054995 : Blo 904575 3054995 := bstep (se 1 (by rfl) ⟨2291246, by rfl⟩ : syracuseStep 3054995 = 4582493) B4582493
theorem B1359275 : Blo 904575 1359275 := bstep (se 1 (by rfl) ⟨1019456, by rfl⟩ : syracuseStep 1359275 = 2038913) B2038913
theorem B1359305 : Blo 904575 1359305 := bstep (se 2 (by rfl) ⟨509739, by rfl⟩ : syracuseStep 1359305 = 1019479) B1019479
theorem B4349483 : Blo 904575 4349483 := bstep (se 1 (by rfl) ⟨3262112, by rfl⟩ : syracuseStep 4349483 = 6524225) B6524225
theorem B1359419 : Blo 904575 1359419 := bstep (se 1 (by rfl) ⟨1019564, by rfl⟩ : syracuseStep 1359419 = 2039129) B2039129
theorem B10305143 : Blo 904575 10305143 := bstep (se 1 (by rfl) ⟨7728857, by rfl⟩ : syracuseStep 10305143 = 15457715) B15457715
theorem B1359479 : Blo 904575 1359479 := bstep (se 1 (by rfl) ⟨1019609, by rfl⟩ : syracuseStep 1359479 = 2039219) B2039219
theorem B966287 : Blo 904575 966287 := bstep (se 1 (by rfl) ⟨724715, by rfl⟩ : syracuseStep 966287 = 1449431) B1449431
theorem B1359503 : Blo 904575 1359503 := bstep (se 1 (by rfl) ⟨1019627, by rfl⟩ : syracuseStep 1359503 = 2039255) B2039255
theorem B1359545 : Blo 904575 1359545 := bstep (se 2 (by rfl) ⟨509829, by rfl⟩ : syracuseStep 1359545 = 1019659) B1019659
theorem B1933001 : Blo 904575 1933001 := bstep (se 2 (by rfl) ⟨724875, by rfl⟩ : syracuseStep 1933001 = 1449751) B1449751
theorem B2293505 : Blo 904575 2293505 := bstep (se 2 (by rfl) ⟨860064, by rfl⟩ : syracuseStep 2293505 = 1720129) B1720129
theorem B1146631 : Blo 904575 1146631 := bstep (se 1 (by rfl) ⟨859973, by rfl⟩ : syracuseStep 1146631 = 1719947) B1719947
theorem B1359623 : Blo 904575 1359623 := bstep (se 1 (by rfl) ⟨1019717, by rfl⟩ : syracuseStep 1359623 = 2039435) B2039435
theorem B966415 : Blo 904575 966415 := bstep (se 1 (by rfl) ⟨724811, by rfl⟩ : syracuseStep 966415 = 1449623) B1449623
theorem B4890401 : Blo 904575 4890401 := bstep (se 2 (by rfl) ⟨1833900, by rfl⟩ : syracuseStep 4890401 = 3667801) B3667801
theorem B1359659 : Blo 904575 1359659 := bstep (se 1 (by rfl) ⟨1019744, by rfl⟩ : syracuseStep 1359659 = 2039489) B2039489
theorem B1359689 : Blo 904575 1359689 := bstep (se 2 (by rfl) ⟨509883, by rfl⟩ : syracuseStep 1359689 = 1019767) B1019767
theorem B4587353 : Blo 904575 4587353 := bstep (se 2 (by rfl) ⟨1720257, by rfl⟩ : syracuseStep 4587353 = 3440515) B3440515
theorem B2039687 : Blo 904575 2039687 := bstep (se 1 (by rfl) ⟨1529765, by rfl⟩ : syracuseStep 2039687 = 3059531) B3059531
theorem B9781145 : Blo 904575 9781145 := bstep (se 2 (by rfl) ⟨3667929, by rfl⟩ : syracuseStep 9781145 = 7335859) B7335859
theorem B1359803 : Blo 904575 1359803 := bstep (se 1 (by rfl) ⟨1019852, by rfl⟩ : syracuseStep 1359803 = 2039705) B2039705
theorem B5152733 : Blo 904575 5152733 := bstep (se 3 (by rfl) ⟨966137, by rfl⟩ : syracuseStep 5152733 = 1932275) B1932275
theorem B1359863 : Blo 904575 1359863 := bstep (se 1 (by rfl) ⟨1019897, by rfl⟩ : syracuseStep 1359863 = 2039795) B2039795
theorem B4587677 : Blo 904575 4587677 := bstep (se 3 (by rfl) ⟨860189, by rfl⟩ : syracuseStep 4587677 = 1720379) B1720379
theorem B10313891 : Blo 904575 10313891 := bstep (se 1 (by rfl) ⟨7735418, by rfl⟩ : syracuseStep 10313891 = 15470837) B15470837
theorem B10461361 : Blo 904575 10461361 := bstep (se 2 (by rfl) ⟨3923010, by rfl⟩ : syracuseStep 10461361 = 7846021) B7846021
theorem B1720531 : Blo 904575 1720531 := bstep (se 1 (by rfl) ⟨1290398, by rfl⟩ : syracuseStep 1720531 = 2580797) B2580797
theorem B39739747 : Blo 904575 39739747 := bstep (se 1 (by rfl) ⟨29804810, by rfl⟩ : syracuseStep 39739747 = 59609621) B59609621
theorem B3441001 : Blo 904575 3441001 := bstep (se 2 (by rfl) ⟨1290375, by rfl⟩ : syracuseStep 3441001 = 2580751) B2580751
theorem B3670397 : Blo 904575 3670397 := bstep (se 3 (by rfl) ⟨688199, by rfl⟩ : syracuseStep 3670397 = 1376399) B1376399
theorem B6873497 : Blo 904575 6873497 := bstep (se 2 (by rfl) ⟨2577561, by rfl⟩ : syracuseStep 6873497 = 5155123) B5155123
theorem B1720759 : Blo 904575 1720759 := bstep (se 1 (by rfl) ⟨1290569, by rfl⟩ : syracuseStep 1720759 = 2581139) B2581139
theorem B1933787 : Blo 904575 1933787 := bstep (se 1 (by rfl) ⟨1450340, by rfl⟩ : syracuseStep 1933787 = 2900681) B2900681
theorem B2580979 : Blo 904575 2580979 := bstep (se 1 (by rfl) ⟨1935734, by rfl⟩ : syracuseStep 2580979 = 3871469) B3871469
theorem B5161481 : Blo 904575 5161481 := bstep (se 2 (by rfl) ⟨1935555, by rfl⟩ : syracuseStep 5161481 = 3871111) B3871111
theorem B1630739 : Blo 904575 1630739 := bstep (se 1 (by rfl) ⟨1223054, by rfl⟩ : syracuseStep 1630739 = 2446109) B2446109
theorem B14672501 : Blo 904575 14672501 := bstep (se 5 (by rfl) ⟨687773, by rfl⟩ : syracuseStep 14672501 = 1375547) B1375547
theorem B3441275 : Blo 904575 3441275 := bstep (se 1 (by rfl) ⟨2580956, by rfl⟩ : syracuseStep 3441275 = 5161913) B5161913
theorem B2581321 : Blo 904575 2581321 := bstep (se 2 (by rfl) ⟨967995, by rfl⟩ : syracuseStep 2581321 = 1935991) B1935991
theorem B1450847 : Blo 904575 1450847 := bstep (se 1 (by rfl) ⟨1088135, by rfl⟩ : syracuseStep 1450847 = 2176271) B2176271
theorem B2294689 : Blo 904575 2294689 := bstep (se 2 (by rfl) ⟨860508, by rfl⟩ : syracuseStep 2294689 = 1721017) B1721017
theorem B5801003 : Blo 904575 5801003 := bstep (se 1 (by rfl) ⟨4350752, by rfl⟩ : syracuseStep 5801003 = 8701505) B8701505
theorem B1631431 : Blo 904575 1631431 := bstep (se 1 (by rfl) ⟨1223573, by rfl⟩ : syracuseStep 1631431 = 2447147) B2447147
theorem B5162231 : Blo 904575 5162231 := bstep (se 1 (by rfl) ⟨3871673, by rfl⟩ : syracuseStep 5162231 = 7743347) B7743347
theorem B5154191 : Blo 904575 5154191 := bstep (se 1 (by rfl) ⟨3865643, by rfl⟩ : syracuseStep 5154191 = 7731287) B7731287
theorem B11167139 : Blo 904575 11167139 := bstep (se 1 (by rfl) ⟨8375354, by rfl⟩ : syracuseStep 11167139 = 16750709) B16750709
theorem B5162413 : Blo 904575 5162413 := bstep (se 3 (by rfl) ⟨967952, by rfl⟩ : syracuseStep 5162413 = 1935905) B1935905
theorem B4588973 : Blo 904575 4588973 := bstep (se 3 (by rfl) ⟨860432, by rfl⟩ : syracuseStep 4588973 = 1720865) B1720865
theorem B7743073 : Blo 904575 7743073 := bstep (se 2 (by rfl) ⟨2903652, by rfl⟩ : syracuseStep 7743073 = 5807305) B5807305
theorem B2647675 : Blo 904575 2647675 := bstep (se 1 (by rfl) ⟨1985756, by rfl⟩ : syracuseStep 2647675 = 3971513) B3971513
theorem B5506859 : Blo 904575 5506859 := bstep (se 1 (by rfl) ⟨4130144, by rfl⟩ : syracuseStep 5506859 = 8260289) B8260289
theorem B5162939 : Blo 904575 5162939 := bstep (se 1 (by rfl) ⟨3872204, by rfl⟩ : syracuseStep 5162939 = 7744409) B7744409
theorem B1017895 : Blo 904575 1017895 := bstep (se 1 (by rfl) ⟨763421, by rfl⟩ : syracuseStep 1017895 = 1526843) B1526843
theorem B5507129 : Blo 904575 5507129 := bstep (se 2 (by rfl) ⟨2065173, by rfl⟩ : syracuseStep 5507129 = 4130347) B4130347
theorem B3057911 : Blo 904575 3057911 := bstep (se 1 (by rfl) ⟨2293433, by rfl⟩ : syracuseStep 3057911 = 4586867) B4586867
theorem B6875441 : Blo 904575 6875441 := bstep (se 2 (by rfl) ⟨2578290, by rfl⟩ : syracuseStep 6875441 = 5156581) B5156581
theorem B1288553 : Blo 904575 1288553 := bstep (se 2 (by rfl) ⟨483207, by rfl⟩ : syracuseStep 1288553 = 966415) B966415
theorem B1288667 : Blo 904575 1288667 := bstep (se 1 (by rfl) ⟨966500, by rfl⟩ : syracuseStep 1288667 = 1933001) B1933001
theorem B3672539 : Blo 904575 3672539 := bstep (se 1 (by rfl) ⟨2754404, by rfl⟩ : syracuseStep 3672539 = 5508809) B5508809
theorem B6973933 : Blo 904575 6973933 := bstep (se 3 (by rfl) ⟨1307612, by rfl⟩ : syracuseStep 6973933 = 2615225) B2615225
theorem B3058235 : Blo 904575 3058235 := bstep (se 1 (by rfl) ⟨2293676, by rfl⟩ : syracuseStep 3058235 = 4587353) B4587353
theorem B3435155 : Blo 904575 3435155 := bstep (se 1 (by rfl) ⟨2576366, by rfl⟩ : syracuseStep 3435155 = 5152733) B5152733
theorem B1526519 : Blo 904575 1526519 := bstep (se 1 (by rfl) ⟨1144889, by rfl⟩ : syracuseStep 1526519 = 2289779) B2289779
theorem B3918665 : Blo 904575 3918665 := bstep (se 2 (by rfl) ⟨1469499, by rfl⟩ : syracuseStep 3918665 = 2938999) B2938999
theorem B3058505 : Blo 904575 3058505 := bstep (se 2 (by rfl) ⟨1146939, by rfl⟩ : syracuseStep 3058505 = 2293879) B2293879
theorem B11611025 : Blo 904575 11611025 := bstep (se 2 (by rfl) ⟨4354134, by rfl⟩ : syracuseStep 11611025 = 8708269) B8708269
theorem B89303957 : Blo 904575 89303957 := bstep (se 6 (by rfl) ⟨2093061, by rfl⟩ : syracuseStep 89303957 = 4186123) B4186123
theorem B3869623 : Blo 904575 3869623 := bstep (se 1 (by rfl) ⟨2902217, by rfl⟩ : syracuseStep 3869623 = 5804435) B5804435
theorem B1526863 : Blo 904575 1526863 := bstep (se 1 (by rfl) ⟨1145147, by rfl⟩ : syracuseStep 1526863 = 2290295) B2290295
theorem B7351499 : Blo 904575 7351499 := bstep (se 1 (by rfl) ⟨5513624, by rfl⟩ : syracuseStep 7351499 = 11027249) B11027249
theorem B1527113 : Blo 904575 1527113 := bstep (se 2 (by rfl) ⟨572667, by rfl⟩ : syracuseStep 1527113 = 1145335) B1145335
theorem B1289567 : Blo 904575 1289567 := bstep (se 1 (by rfl) ⟨967175, by rfl⟩ : syracuseStep 1289567 = 1934351) B1934351
theorem B5229989 : Blo 904575 5229989 := bstep (se 4 (by rfl) ⟨490311, by rfl⟩ : syracuseStep 5229989 = 980623) B980623
theorem B904623 : Blo 904575 904623 := bstep (se 1 (by rfl) ⟨678467, by rfl⟩ : syracuseStep 904623 = 1356935) B1356935
theorem B904647 : Blo 904575 904647 := bstep (se 1 (by rfl) ⟨678485, by rfl⟩ : syracuseStep 904647 = 1356971) B1356971
theorem B904667 : Blo 904575 904667 := bstep (se 1 (by rfl) ⟨678500, by rfl⟩ : syracuseStep 904667 = 1357001) B1357001
theorem B2903539 : Blo 904575 2903539 := bstep (se 1 (by rfl) ⟨2177654, by rfl⟩ : syracuseStep 2903539 = 4355309) B4355309
theorem B904743 : Blo 904575 904743 := bstep (se 1 (by rfl) ⟨678557, by rfl⟩ : syracuseStep 904743 = 1357115) B1357115
theorem B904783 : Blo 904575 904783 := bstep (se 1 (by rfl) ⟨678587, by rfl⟩ : syracuseStep 904783 = 1357175) B1357175
theorem B904799 : Blo 904575 904799 := bstep (se 1 (by rfl) ⟨678599, by rfl⟩ : syracuseStep 904799 = 1357199) B1357199
theorem B904827 : Blo 904575 904827 := bstep (se 1 (by rfl) ⟨678620, by rfl⟩ : syracuseStep 904827 = 1357241) B1357241
theorem B1019515 : Blo 904575 1019515 := bstep (se 1 (by rfl) ⟨764636, by rfl⟩ : syracuseStep 1019515 = 1529273) B1529273
theorem B904879 : Blo 904575 904879 := bstep (se 1 (by rfl) ⟨678659, by rfl⟩ : syracuseStep 904879 = 1357319) B1357319
theorem B26095283 : Blo 904575 26095283 := bstep (se 1 (by rfl) ⟨19571462, by rfl⟩ : syracuseStep 26095283 = 39142925) B39142925
theorem B904903 : Blo 904575 904903 := bstep (se 1 (by rfl) ⟨678677, by rfl⟩ : syracuseStep 904903 = 1357355) B1357355
theorem B904923 : Blo 904575 904923 := bstep (se 1 (by rfl) ⟨678692, by rfl⟩ : syracuseStep 904923 = 1357385) B1357385
theorem B11013869 : Blo 904575 11013869 := bstep (se 3 (by rfl) ⟨2065100, by rfl⟩ : syracuseStep 11013869 = 4130201) B4130201
theorem B1527545 : Blo 904575 1527545 := bstep (se 2 (by rfl) ⟨572829, by rfl⟩ : syracuseStep 1527545 = 1145659) B1145659
theorem B7343905 : Blo 904575 7343905 := bstep (se 2 (by rfl) ⟨2753964, by rfl⟩ : syracuseStep 7343905 = 5507929) B5507929
theorem B904999 : Blo 904575 904999 := bstep (se 1 (by rfl) ⟨678749, by rfl⟩ : syracuseStep 904999 = 1357499) B1357499
theorem B2035529 : Blo 904575 2035529 := bstep (se 2 (by rfl) ⟨763323, by rfl⟩ : syracuseStep 2035529 = 1526647) B1526647
theorem B905039 : Blo 904575 905039 := bstep (se 1 (by rfl) ⟨678779, by rfl⟩ : syracuseStep 905039 = 1357559) B1357559
theorem B905055 : Blo 904575 905055 := bstep (se 1 (by rfl) ⟨678791, by rfl⟩ : syracuseStep 905055 = 1357583) B1357583
theorem B905083 : Blo 904575 905083 := bstep (se 1 (by rfl) ⟨678812, by rfl⟩ : syracuseStep 905083 = 1357625) B1357625
theorem B11915171 : Blo 904575 11915171 := bstep (se 1 (by rfl) ⟨8936378, by rfl⟩ : syracuseStep 11915171 = 17872757) B17872757
theorem B1527727 : Blo 904575 1527727 := bstep (se 1 (by rfl) ⟨1145795, by rfl⟩ : syracuseStep 1527727 = 2291591) B2291591
theorem B905135 : Blo 904575 905135 := bstep (se 1 (by rfl) ⟨678851, by rfl⟩ : syracuseStep 905135 = 1357703) B1357703
theorem B1961903 : Blo 904575 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B3059639 : Blo 904575 3059639 := bstep (se 1 (by rfl) ⟨2294729, by rfl⟩ : syracuseStep 3059639 = 4589459) B4589459
theorem B905159 : Blo 904575 905159 := bstep (se 1 (by rfl) ⟨678869, by rfl⟩ : syracuseStep 905159 = 1357739) B1357739
theorem B905179 : Blo 904575 905179 := bstep (se 1 (by rfl) ⟨678884, by rfl⟩ : syracuseStep 905179 = 1357769) B1357769
theorem B1527815 : Blo 904575 1527815 := bstep (se 1 (by rfl) ⟨1145861, by rfl⟩ : syracuseStep 1527815 = 2291723) B2291723
theorem B905255 : Blo 904575 905255 := bstep (se 1 (by rfl) ⟨678941, by rfl⟩ : syracuseStep 905255 = 1357883) B1357883
theorem B905295 : Blo 904575 905295 := bstep (se 1 (by rfl) ⟨678971, by rfl⟩ : syracuseStep 905295 = 1357943) B1357943
theorem B905311 : Blo 904575 905311 := bstep (se 1 (by rfl) ⟨678983, by rfl⟩ : syracuseStep 905311 = 1357967) B1357967
theorem B905339 : Blo 904575 905339 := bstep (se 1 (by rfl) ⟨679004, by rfl⟩ : syracuseStep 905339 = 1358009) B1358009
theorem B905391 : Blo 904575 905391 := bstep (se 1 (by rfl) ⟨679043, by rfl⟩ : syracuseStep 905391 = 1358087) B1358087
theorem B905415 : Blo 904575 905415 := bstep (se 1 (by rfl) ⟨679061, by rfl⟩ : syracuseStep 905415 = 1358123) B1358123
theorem B905435 : Blo 904575 905435 := bstep (se 1 (by rfl) ⟨679076, by rfl⟩ : syracuseStep 905435 = 1358153) B1358153
theorem B905511 : Blo 904575 905511 := bstep (se 1 (by rfl) ⟨679133, by rfl⟩ : syracuseStep 905511 = 1358267) B1358267
theorem B905551 : Blo 904575 905551 := bstep (se 1 (by rfl) ⟨679163, by rfl⟩ : syracuseStep 905551 = 1358327) B1358327
theorem B5509463 : Blo 904575 5509463 := bstep (se 1 (by rfl) ⟨4132097, by rfl⟩ : syracuseStep 5509463 = 8264195) B8264195
theorem B905567 : Blo 904575 905567 := bstep (se 1 (by rfl) ⟨679175, by rfl⟩ : syracuseStep 905567 = 1358351) B1358351
theorem B1528159 : Blo 904575 1528159 := bstep (se 1 (by rfl) ⟨1146119, by rfl⟩ : syracuseStep 1528159 = 2292239) B2292239
theorem B905595 : Blo 904575 905595 := bstep (se 1 (by rfl) ⟨679196, by rfl⟩ : syracuseStep 905595 = 1358393) B1358393
theorem B2576765 : Blo 904575 2576765 := bstep (se 3 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 2576765 = 966287) B966287
theorem B3264911 : Blo 904575 3264911 := bstep (se 1 (by rfl) ⟨2448683, by rfl⟩ : syracuseStep 3264911 = 4897367) B4897367
theorem B905647 : Blo 904575 905647 := bstep (se 1 (by rfl) ⟨679235, by rfl⟩ : syracuseStep 905647 = 1358471) B1358471
theorem B1528247 : Blo 904575 1528247 := bstep (se 1 (by rfl) ⟨1146185, by rfl⟩ : syracuseStep 1528247 = 2292371) B2292371
theorem B905671 : Blo 904575 905671 := bstep (se 1 (by rfl) ⟨679253, by rfl⟩ : syracuseStep 905671 = 1358507) B1358507
theorem B905691 : Blo 904575 905691 := bstep (se 1 (by rfl) ⟨679268, by rfl⟩ : syracuseStep 905691 = 1358537) B1358537
theorem B905767 : Blo 904575 905767 := bstep (se 1 (by rfl) ⟨679325, by rfl⟩ : syracuseStep 905767 = 1358651) B1358651
theorem B905807 : Blo 904575 905807 := bstep (se 1 (by rfl) ⟨679355, by rfl⟩ : syracuseStep 905807 = 1358711) B1358711
theorem B905823 : Blo 904575 905823 := bstep (se 1 (by rfl) ⟨679367, by rfl⟩ : syracuseStep 905823 = 1358735) B1358735
theorem B2036321 : Blo 904575 2036321 := bstep (se 2 (by rfl) ⟨763620, by rfl⟩ : syracuseStep 2036321 = 1527241) B1527241
theorem B21181027 : Blo 904575 21181027 := bstep (se 1 (by rfl) ⟨15885770, by rfl⟩ : syracuseStep 21181027 = 31771541) B31771541
theorem B905851 : Blo 904575 905851 := bstep (se 1 (by rfl) ⟨679388, by rfl⟩ : syracuseStep 905851 = 1358777) B1358777
theorem B2290315 : Blo 904575 2290315 := bstep (se 1 (by rfl) ⟨1717736, by rfl⟩ : syracuseStep 2290315 = 3435473) B3435473
theorem B905903 : Blo 904575 905903 := bstep (se 1 (by rfl) ⟨679427, by rfl⟩ : syracuseStep 905903 = 1358855) B1358855
theorem B4895417 : Blo 904575 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B905927 : Blo 904575 905927 := bstep (se 1 (by rfl) ⟨679445, by rfl⟩ : syracuseStep 905927 = 1358891) B1358891
theorem B905947 : Blo 904575 905947 := bstep (se 1 (by rfl) ⟨679460, by rfl⟩ : syracuseStep 905947 = 1358921) B1358921
theorem B9286417 : Blo 904575 9286417 := bstep (se 2 (by rfl) ⟨3482406, by rfl⟩ : syracuseStep 9286417 = 6964813) B6964813
theorem B23212817 : Blo 904575 23212817 := bstep (se 2 (by rfl) ⟨8704806, by rfl⟩ : syracuseStep 23212817 = 17409613) B17409613
theorem B906023 : Blo 904575 906023 := bstep (se 1 (by rfl) ⟨679517, by rfl⟩ : syracuseStep 906023 = 1359035) B1359035
theorem B906063 : Blo 904575 906063 := bstep (se 1 (by rfl) ⟨679547, by rfl⟩ : syracuseStep 906063 = 1359095) B1359095
theorem B906079 : Blo 904575 906079 := bstep (se 1 (by rfl) ⟨679559, by rfl⟩ : syracuseStep 906079 = 1359119) B1359119
theorem B906107 : Blo 904575 906107 := bstep (se 1 (by rfl) ⟨679580, by rfl⟩ : syracuseStep 906107 = 1359161) B1359161
theorem B906159 : Blo 904575 906159 := bstep (se 1 (by rfl) ⟨679619, by rfl⟩ : syracuseStep 906159 = 1359239) B1359239
theorem B2036663 : Blo 904575 2036663 := bstep (se 1 (by rfl) ⟨1527497, by rfl⟩ : syracuseStep 2036663 = 3054995) B3054995
theorem B2290619 : Blo 904575 2290619 := bstep (se 1 (by rfl) ⟨1717964, by rfl⟩ : syracuseStep 2290619 = 3435929) B3435929
theorem B906183 : Blo 904575 906183 := bstep (se 1 (by rfl) ⟨679637, by rfl⟩ : syracuseStep 906183 = 1359275) B1359275
theorem B906203 : Blo 904575 906203 := bstep (se 1 (by rfl) ⟨679652, by rfl⟩ : syracuseStep 906203 = 1359305) B1359305
theorem B5297125 : Blo 904575 5297125 := bstep (se 4 (by rfl) ⟨496605, by rfl⟩ : syracuseStep 5297125 = 993211) B993211
theorem B1528841 : Blo 904575 1528841 := bstep (se 2 (by rfl) ⟨573315, by rfl⟩ : syracuseStep 1528841 = 1146631) B1146631
theorem B906279 : Blo 904575 906279 := bstep (se 1 (by rfl) ⟨679709, by rfl⟩ : syracuseStep 906279 = 1359419) B1359419
theorem B7730225 : Blo 904575 7730225 := bstep (se 2 (by rfl) ⟨2898834, by rfl⟩ : syracuseStep 7730225 = 5797669) B5797669
theorem B6870095 : Blo 904575 6870095 := bstep (se 1 (by rfl) ⟨5152571, by rfl⟩ : syracuseStep 6870095 = 10305143) B10305143
theorem B906319 : Blo 904575 906319 := bstep (se 1 (by rfl) ⟨679739, by rfl⟩ : syracuseStep 906319 = 1359479) B1359479
theorem B906335 : Blo 904575 906335 := bstep (se 1 (by rfl) ⟨679751, by rfl⟩ : syracuseStep 906335 = 1359503) B1359503
theorem B1356923 : Blo 904575 1356923 := bstep (se 1 (by rfl) ⟨1017692, by rfl⟩ : syracuseStep 1356923 = 2035385) B2035385
theorem B906363 : Blo 904575 906363 := bstep (se 1 (by rfl) ⟨679772, by rfl⟩ : syracuseStep 906363 = 1359545) B1359545
theorem B1529003 : Blo 904575 1529003 := bstep (se 1 (by rfl) ⟨1146752, by rfl⟩ : syracuseStep 1529003 = 2293505) B2293505
theorem B906415 : Blo 904575 906415 := bstep (se 1 (by rfl) ⟨679811, by rfl⟩ : syracuseStep 906415 = 1359623) B1359623
theorem B906439 : Blo 904575 906439 := bstep (se 1 (by rfl) ⟨679829, by rfl⟩ : syracuseStep 906439 = 1359659) B1359659
theorem B906459 : Blo 904575 906459 := bstep (se 1 (by rfl) ⟨679844, by rfl⟩ : syracuseStep 906459 = 1359689) B1359689
theorem B1357049 : Blo 904575 1357049 := bstep (se 2 (by rfl) ⟨508893, by rfl⟩ : syracuseStep 1357049 = 1017787) B1017787
theorem B906535 : Blo 904575 906535 := bstep (se 1 (by rfl) ⟨679901, by rfl⟩ : syracuseStep 906535 = 1359803) B1359803
theorem B1471817 : Blo 904575 1471817 := bstep (se 2 (by rfl) ⟨551931, by rfl⟩ : syracuseStep 1471817 = 1103863) B1103863
theorem B906575 : Blo 904575 906575 := bstep (se 1 (by rfl) ⟨679931, by rfl⟩ : syracuseStep 906575 = 1359863) B1359863
theorem B1357151 : Blo 904575 1357151 := bstep (se 1 (by rfl) ⟨1017863, by rfl⟩ : syracuseStep 1357151 = 2035727) B2035727
theorem B1357163 : Blo 904575 1357163 := bstep (se 1 (by rfl) ⟨1017872, by rfl⟩ : syracuseStep 1357163 = 2035745) B2035745
theorem B3052943 : Blo 904575 3052943 := bstep (se 1 (by rfl) ⟨2289707, by rfl⟩ : syracuseStep 3052943 = 4579415) B4579415
theorem B4584923 : Blo 904575 4584923 := bstep (se 1 (by rfl) ⟨3438692, by rfl⟩ : syracuseStep 4584923 = 6877385) B6877385
theorem B2037257 : Blo 904575 2037257 := bstep (se 2 (by rfl) ⟨763971, by rfl⟩ : syracuseStep 2037257 = 1527943) B1527943
theorem B1529401 : Blo 904575 1529401 := bstep (se 2 (by rfl) ⟨573525, by rfl⟩ : syracuseStep 1529401 = 1147051) B1147051
theorem B1357391 : Blo 904575 1357391 := bstep (se 1 (by rfl) ⟨1018043, by rfl⟩ : syracuseStep 1357391 = 2036087) B2036087
theorem B5805665 : Blo 904575 5805665 := bstep (se 2 (by rfl) ⟨2177124, by rfl⟩ : syracuseStep 5805665 = 4354249) B4354249
theorem B6878843 : Blo 904575 6878843 := bstep (se 1 (by rfl) ⟨5159132, by rfl⟩ : syracuseStep 6878843 = 10318265) B10318265
theorem B1357511 : Blo 904575 1357511 := bstep (se 1 (by rfl) ⟨1018133, by rfl⟩ : syracuseStep 1357511 = 2036267) B2036267
theorem B2291399 : Blo 904575 2291399 := bstep (se 1 (by rfl) ⟨1718549, by rfl⟩ : syracuseStep 2291399 = 3437099) B3437099
theorem B1529543 : Blo 904575 1529543 := bstep (se 1 (by rfl) ⟨1147157, by rfl⟩ : syracuseStep 1529543 = 2294315) B2294315
theorem B3053267 : Blo 904575 3053267 := bstep (se 1 (by rfl) ⟨2289950, by rfl⟩ : syracuseStep 3053267 = 4579901) B4579901
theorem B2291449 : Blo 904575 2291449 := bstep (se 2 (by rfl) ⟨859293, by rfl⟩ : syracuseStep 2291449 = 1718587) B1718587
theorem B4347715 : Blo 904575 4347715 := bstep (se 1 (by rfl) ⟨3260786, by rfl⟩ : syracuseStep 4347715 = 6521573) B6521573
theorem B2037599 : Blo 904575 2037599 := bstep (se 1 (by rfl) ⟨1528199, by rfl⟩ : syracuseStep 2037599 = 3056399) B3056399
theorem B1357673 : Blo 904575 1357673 := bstep (se 2 (by rfl) ⟨509127, by rfl⟩ : syracuseStep 1357673 = 1018255) B1018255
theorem B1529705 : Blo 904575 1529705 := bstep (se 2 (by rfl) ⟨573639, by rfl⟩ : syracuseStep 1529705 = 1147279) B1147279
theorem B2578337 : Blo 904575 2578337 := bstep (se 2 (by rfl) ⟨966876, by rfl⟩ : syracuseStep 2578337 = 1933753) B1933753
theorem B4642721 : Blo 904575 4642721 := bstep (se 2 (by rfl) ⟨1741020, by rfl⟩ : syracuseStep 4642721 = 3482041) B3482041
theorem B12089249 : Blo 904575 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B1357751 : Blo 904575 1357751 := bstep (se 1 (by rfl) ⟨1018313, by rfl⟩ : syracuseStep 1357751 = 2036627) B2036627
theorem B4585409 : Blo 904575 4585409 := bstep (se 2 (by rfl) ⟨1719528, by rfl⟩ : syracuseStep 4585409 = 3439057) B3439057
theorem B1357787 : Blo 904575 1357787 := bstep (se 1 (by rfl) ⟨1018340, by rfl⟩ : syracuseStep 1357787 = 2036681) B2036681
theorem B2037779 : Blo 904575 2037779 := bstep (se 1 (by rfl) ⟨1528334, by rfl⟩ : syracuseStep 2037779 = 3056669) B3056669
theorem B1718329 : Blo 904575 1718329 := bstep (se 2 (by rfl) ⟨644373, by rfl⟩ : syracuseStep 1718329 = 1288747) B1288747
theorem B1144955 : Blo 904575 1144955 := bstep (se 1 (by rfl) ⟨858716, by rfl⟩ : syracuseStep 1144955 = 1717433) B1717433
theorem B69818609 : Blo 904575 69818609 := bstep (se 2 (by rfl) ⟨26181978, by rfl⟩ : syracuseStep 69818609 = 52363957) B52363957
theorem B2578679 : Blo 904575 2578679 := bstep (se 1 (by rfl) ⟨1934009, by rfl⟩ : syracuseStep 2578679 = 3868019) B3868019
theorem B1718633 : Blo 904575 1718633 := bstep (se 2 (by rfl) ⟨644487, by rfl⟩ : syracuseStep 1718633 = 1288975) B1288975
theorem B2038121 : Blo 904575 2038121 := bstep (se 2 (by rfl) ⟨764295, by rfl⟩ : syracuseStep 2038121 = 1528591) B1528591
theorem B2292097 : Blo 904575 2292097 := bstep (se 2 (by rfl) ⟨859536, by rfl⟩ : syracuseStep 2292097 = 1719073) B1719073
theorem B1718671 : Blo 904575 1718671 := bstep (se 1 (by rfl) ⟨1289003, by rfl⟩ : syracuseStep 1718671 = 2578007) B2578007
theorem B1358255 : Blo 904575 1358255 := bstep (se 1 (by rfl) ⟨1018691, by rfl⟩ : syracuseStep 1358255 = 2037383) B2037383
theorem B3865097 : Blo 904575 3865097 := bstep (se 2 (by rfl) ⟨1449411, by rfl⟩ : syracuseStep 3865097 = 2898823) B2898823
theorem B1358345 : Blo 904575 1358345 := bstep (se 2 (by rfl) ⟨509379, by rfl⟩ : syracuseStep 1358345 = 1018759) B1018759
theorem B1358375 : Blo 904575 1358375 := bstep (se 1 (by rfl) ⟨1018781, by rfl⟩ : syracuseStep 1358375 = 2037563) B2037563
theorem B1358459 : Blo 904575 1358459 := bstep (se 1 (by rfl) ⟨1018844, by rfl⟩ : syracuseStep 1358459 = 2037689) B2037689
theorem B1358585 : Blo 904575 1358585 := bstep (se 2 (by rfl) ⟨509469, by rfl⟩ : syracuseStep 1358585 = 1018939) B1018939
theorem B1358687 : Blo 904575 1358687 := bstep (se 1 (by rfl) ⟨1019015, by rfl⟩ : syracuseStep 1358687 = 2038031) B2038031
theorem B1358699 : Blo 904575 1358699 := bstep (se 1 (by rfl) ⟨1019024, by rfl⟩ : syracuseStep 1358699 = 2038049) B2038049
theorem B3054455 : Blo 904575 3054455 := bstep (se 1 (by rfl) ⟨2290841, by rfl⟩ : syracuseStep 3054455 = 4581683) B4581683
theorem B3439543 : Blo 904575 3439543 := bstep (se 1 (by rfl) ⟨2579657, by rfl⟩ : syracuseStep 3439543 = 5159315) B5159315
theorem B2038715 : Blo 904575 2038715 := bstep (se 1 (by rfl) ⟨1529036, by rfl⟩ : syracuseStep 2038715 = 3058073) B3058073
theorem B8707115 : Blo 904575 8707115 := bstep (se 1 (by rfl) ⟨6530336, by rfl⟩ : syracuseStep 8707115 = 13060673) B13060673
theorem B2038841 : Blo 904575 2038841 := bstep (se 2 (by rfl) ⟨764565, by rfl⟩ : syracuseStep 2038841 = 1529131) B1529131
theorem B3054671 : Blo 904575 3054671 := bstep (se 1 (by rfl) ⟨2291003, by rfl⟩ : syracuseStep 3054671 = 4582007) B4582007
theorem B1358927 : Blo 904575 1358927 := bstep (se 1 (by rfl) ⟨1019195, by rfl⟩ : syracuseStep 1358927 = 2038391) B2038391
theorem B2292907 : Blo 904575 2292907 := bstep (se 1 (by rfl) ⟨1719680, by rfl⟩ : syracuseStep 2292907 = 3439361) B3439361
theorem B8707267 : Blo 904575 8707267 := bstep (se 1 (by rfl) ⟨6530450, by rfl⟩ : syracuseStep 8707267 = 13060901) B13060901
theorem B1359047 : Blo 904575 1359047 := bstep (se 1 (by rfl) ⟨1019285, by rfl⟩ : syracuseStep 1359047 = 2038571) B2038571
theorem B12393719 : Blo 904575 12393719 := bstep (se 1 (by rfl) ⟨9295289, by rfl⟩ : syracuseStep 12393719 = 18590579) B18590579
theorem B1359209 : Blo 904575 1359209 := bstep (se 2 (by rfl) ⟨509703, by rfl⟩ : syracuseStep 1359209 = 1019407) B1019407
theorem B3440015 : Blo 904575 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B2039183 : Blo 904575 2039183 := bstep (se 1 (by rfl) ⟨1529387, by rfl⟩ : syracuseStep 2039183 = 3058775) B3058775
theorem B1359287 : Blo 904575 1359287 := bstep (se 1 (by rfl) ⟨1019465, by rfl⟩ : syracuseStep 1359287 = 2038931) B2038931
theorem B3055049 : Blo 904575 3055049 := bstep (se 2 (by rfl) ⟨1145643, by rfl⟩ : syracuseStep 3055049 = 2291287) B2291287
theorem B2293211 : Blo 904575 2293211 := bstep (se 1 (by rfl) ⟨1719908, by rfl⟩ : syracuseStep 2293211 = 3439817) B3439817
theorem B1359323 : Blo 904575 1359323 := bstep (se 1 (by rfl) ⟨1019492, by rfl⟩ : syracuseStep 1359323 = 2038985) B2038985
theorem B2899655 : Blo 904575 2899655 := bstep (se 1 (by rfl) ⟨2174741, by rfl⟩ : syracuseStep 2899655 = 4349483) B4349483
theorem B2039507 : Blo 904575 2039507 := bstep (se 1 (by rfl) ⟨1529630, by rfl⟩ : syracuseStep 2039507 = 3059261) B3059261
theorem B3055319 : Blo 904575 3055319 := bstep (se 1 (by rfl) ⟨2291489, by rfl⟩ : syracuseStep 3055319 = 4582979) B4582979
theorem B3260267 : Blo 904575 3260267 := bstep (se 1 (by rfl) ⟨2445200, by rfl⟩ : syracuseStep 3260267 = 4890401) B4890401
theorem B3055535 : Blo 904575 3055535 := bstep (se 1 (by rfl) ⟨2291651, by rfl⟩ : syracuseStep 3055535 = 4583303) B4583303
theorem B1359791 : Blo 904575 1359791 := bstep (se 1 (by rfl) ⟨1019843, by rfl⟩ : syracuseStep 1359791 = 2039687) B2039687
theorem B6520763 : Blo 904575 6520763 := bstep (se 1 (by rfl) ⟨4890572, by rfl⟩ : syracuseStep 6520763 = 9781145) B9781145
theorem B2294041 : Blo 904575 2294041 := bstep (se 2 (by rfl) ⟨860265, by rfl⟩ : syracuseStep 2294041 = 1720531) B1720531
theorem B3440987 : Blo 904575 3440987 := bstep (se 1 (by rfl) ⟨2580740, by rfl⟩ : syracuseStep 3440987 = 5161481) B5161481
theorem B9781667 : Blo 904575 9781667 := bstep (se 1 (by rfl) ⟨7336250, by rfl⟩ : syracuseStep 9781667 = 14672501) B14672501
theorem B2294183 : Blo 904575 2294183 := bstep (se 1 (by rfl) ⟨1720637, by rfl⟩ : syracuseStep 2294183 = 3441275) B3441275
theorem B52986329 : Blo 904575 52986329 := bstep (se 2 (by rfl) ⟨19869873, by rfl⟩ : syracuseStep 52986329 = 39739747) B39739747
theorem B4588001 : Blo 904575 4588001 := bstep (se 2 (by rfl) ⟨1720500, by rfl⟩ : syracuseStep 4588001 = 3441001) B3441001
theorem B3056129 : Blo 904575 3056129 := bstep (se 2 (by rfl) ⟨1146048, by rfl⟩ : syracuseStep 3056129 = 2292097) B2292097
theorem B15475211 : Blo 904575 15475211 := bstep (se 1 (by rfl) ⟨11606408, by rfl⟩ : syracuseStep 15475211 = 23212817) B23212817
theorem B967231 : Blo 904575 967231 := bstep (se 1 (by rfl) ⟨725423, by rfl⟩ : syracuseStep 967231 = 1450847) B1450847
theorem B2294345 : Blo 904575 2294345 := bstep (se 2 (by rfl) ⟨860379, by rfl⟩ : syracuseStep 2294345 = 1720759) B1720759
theorem B9298577 : Blo 904575 9298577 := bstep (se 2 (by rfl) ⟨3486966, by rfl⟩ : syracuseStep 9298577 = 6973933) B6973933
theorem B3441305 : Blo 904575 3441305 := bstep (se 2 (by rfl) ⟨1290489, by rfl⟩ : syracuseStep 3441305 = 2580979) B2580979
theorem B3867335 : Blo 904575 3867335 := bstep (se 1 (by rfl) ⟨2900501, by rfl⟩ : syracuseStep 3867335 = 5801003) B5801003
theorem B5153483 : Blo 904575 5153483 := bstep (se 1 (by rfl) ⟨3865112, by rfl⟩ : syracuseStep 5153483 = 7730225) B7730225
theorem B4580063 : Blo 904575 4580063 := bstep (se 1 (by rfl) ⟨3435047, by rfl⟩ : syracuseStep 4580063 = 6870095) B6870095
theorem B3441487 : Blo 904575 3441487 := bstep (se 1 (by rfl) ⟨2581115, by rfl⟩ : syracuseStep 3441487 = 5162231) B5162231
theorem B3924845 : Blo 904575 3924845 := bstep (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) B1471817
theorem B3056615 : Blo 904575 3056615 := bstep (se 1 (by rfl) ⟨2292461, by rfl⟩ : syracuseStep 3056615 = 4584923) B4584923
theorem B8700965 : Blo 904575 8700965 := bstep (se 4 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 8700965 = 1631431) B1631431
theorem B3441761 : Blo 904575 3441761 := bstep (se 2 (by rfl) ⟨1290660, by rfl⟩ : syracuseStep 3441761 = 2581321) B2581321
theorem B3671239 : Blo 904575 3671239 := bstep (se 1 (by rfl) ⟨2753429, by rfl⟩ : syracuseStep 3671239 = 5506859) B5506859
theorem B3441959 : Blo 904575 3441959 := bstep (se 1 (by rfl) ⟨2581469, by rfl⟩ : syracuseStep 3441959 = 5162939) B5162939
theorem B3056939 : Blo 904575 3056939 := bstep (se 1 (by rfl) ⟨2292704, by rfl⟩ : syracuseStep 3056939 = 4585409) B4585409
theorem B7062833 : Blo 904575 7062833 := bstep (se 2 (by rfl) ⟨2648562, by rfl⟩ : syracuseStep 7062833 = 5297125) B5297125
theorem B3671419 : Blo 904575 3671419 := bstep (se 1 (by rfl) ⟨2753564, by rfl⟩ : syracuseStep 3671419 = 5507129) B5507129
theorem B3057209 : Blo 904575 3057209 := bstep (se 2 (by rfl) ⟨1146453, by rfl⟩ : syracuseStep 3057209 = 2292907) B2292907
theorem B11609689 : Blo 904575 11609689 := bstep (se 2 (by rfl) ⟨4353633, by rfl⟩ : syracuseStep 11609689 = 8707267) B8707267
theorem B1017679 : Blo 904575 1017679 := bstep (se 1 (by rfl) ⟨763259, by rfl⟩ : syracuseStep 1017679 = 1526519) B1526519
theorem B6883217 : Blo 904575 6883217 := bstep (se 2 (by rfl) ⟨2581206, by rfl⟩ : syracuseStep 6883217 = 5162413) B5162413
theorem B10324097 : Blo 904575 10324097 := bstep (se 2 (by rfl) ⟨3871536, by rfl⟩ : syracuseStep 10324097 = 7743073) B7743073
theorem B4900999 : Blo 904575 4900999 := bstep (se 1 (by rfl) ⟨3675749, by rfl⟩ : syracuseStep 4900999 = 7351499) B7351499
theorem B1018075 : Blo 904575 1018075 := bstep (se 1 (by rfl) ⟨763556, by rfl⟩ : syracuseStep 1018075 = 1527113) B1527113
theorem B9791873 : Blo 904575 9791873 := bstep (se 2 (by rfl) ⟨3671952, by rfl⟩ : syracuseStep 9791873 = 7343905) B7343905
theorem B7342579 : Blo 904575 7342579 := bstep (se 1 (by rfl) ⟨5506934, by rfl⟩ : syracuseStep 7342579 = 11013869) B11013869
theorem B1018363 : Blo 904575 1018363 := bstep (se 1 (by rfl) ⟨763772, by rfl⟩ : syracuseStep 1018363 = 1527545) B1527545
theorem B2173511 : Blo 904575 2173511 := bstep (se 1 (by rfl) ⟨1630133, by rfl⟩ : syracuseStep 2173511 = 3260267) B3260267
theorem B1018543 : Blo 904575 1018543 := bstep (se 1 (by rfl) ⟨763907, by rfl⟩ : syracuseStep 1018543 = 1527815) B1527815
theorem B3058451 : Blo 904575 3058451 := bstep (se 1 (by rfl) ⟨2293838, by rfl⟩ : syracuseStep 3058451 = 4587677) B4587677
theorem B6875927 : Blo 904575 6875927 := bstep (se 1 (by rfl) ⟨5156945, by rfl⟩ : syracuseStep 6875927 = 10313891) B10313891
theorem B4582331 : Blo 904575 4582331 := bstep (se 1 (by rfl) ⟨3436748, by rfl⟩ : syracuseStep 4582331 = 6873497) B6873497
theorem B1018831 : Blo 904575 1018831 := bstep (se 1 (by rfl) ⟨764123, by rfl⟩ : syracuseStep 1018831 = 1528247) B1528247
theorem B1289191 : Blo 904575 1289191 := bstep (se 1 (by rfl) ⟨966893, by rfl⟩ : syracuseStep 1289191 = 1933787) B1933787
theorem B1527079 : Blo 904575 1527079 := bstep (se 1 (by rfl) ⟨1145309, by rfl⟩ : syracuseStep 1527079 = 2290619) B2290619
theorem B186182957 : Blo 904575 186182957 := bstep (se 3 (by rfl) ⟨34909304, by rfl⟩ : syracuseStep 186182957 = 69818609) B69818609
theorem B1019227 : Blo 904575 1019227 := bstep (se 1 (by rfl) ⟨764420, by rfl⟩ : syracuseStep 1019227 = 1528841) B1528841
theorem B904615 : Blo 904575 904615 := bstep (se 1 (by rfl) ⟨678461, by rfl⟩ : syracuseStep 904615 = 1356923) B1356923
theorem B1019335 : Blo 904575 1019335 := bstep (se 1 (by rfl) ⟨764501, by rfl⟩ : syracuseStep 1019335 = 1529003) B1529003
theorem B28241369 : Blo 904575 28241369 := bstep (se 2 (by rfl) ⟨10590513, by rfl⟩ : syracuseStep 28241369 = 21181027) B21181027
theorem B904699 : Blo 904575 904699 := bstep (se 1 (by rfl) ⟨678524, by rfl⟩ : syracuseStep 904699 = 1357049) B1357049
theorem B14691901 : Blo 904575 14691901 := bstep (se 3 (by rfl) ⟨2754731, by rfl⟩ : syracuseStep 14691901 = 5509463) B5509463
theorem B904767 : Blo 904575 904767 := bstep (se 1 (by rfl) ⟨678575, by rfl⟩ : syracuseStep 904767 = 1357151) B1357151
theorem B904775 : Blo 904575 904775 := bstep (se 1 (by rfl) ⟨678581, by rfl⟩ : syracuseStep 904775 = 1357163) B1357163
theorem B2035295 : Blo 904575 2035295 := bstep (se 1 (by rfl) ⟨1526471, by rfl⟩ : syracuseStep 2035295 = 3052943) B3052943
theorem B3436127 : Blo 904575 3436127 := bstep (se 1 (by rfl) ⟨2577095, by rfl⟩ : syracuseStep 3436127 = 5154191) B5154191
theorem B3436141 : Blo 904575 3436141 := bstep (se 3 (by rfl) ⟨644276, by rfl⟩ : syracuseStep 3436141 = 1288553) B1288553
theorem B3059315 : Blo 904575 3059315 := bstep (se 1 (by rfl) ⟨2294486, by rfl⟩ : syracuseStep 3059315 = 4588973) B4588973
theorem B12381889 : Blo 904575 12381889 := bstep (se 2 (by rfl) ⟨4643208, by rfl⟩ : syracuseStep 12381889 = 9286417) B9286417
theorem B904927 : Blo 904575 904927 := bstep (se 1 (by rfl) ⟨678695, by rfl⟩ : syracuseStep 904927 = 1357391) B1357391
theorem B3870443 : Blo 904575 3870443 := bstep (se 1 (by rfl) ⟨2902832, by rfl⟩ : syracuseStep 3870443 = 5805665) B5805665
theorem B905007 : Blo 904575 905007 := bstep (se 1 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 905007 = 1357511) B1357511
theorem B1527599 : Blo 904575 1527599 := bstep (se 1 (by rfl) ⟨1145699, by rfl⟩ : syracuseStep 1527599 = 2291399) B2291399
theorem B1019695 : Blo 904575 1019695 := bstep (se 1 (by rfl) ⟨764771, by rfl⟩ : syracuseStep 1019695 = 1529543) B1529543
theorem B2035511 : Blo 904575 2035511 := bstep (se 1 (by rfl) ⟨1526633, by rfl⟩ : syracuseStep 2035511 = 3053267) B3053267
theorem B3059585 : Blo 904575 3059585 := bstep (se 2 (by rfl) ⟨1147344, by rfl⟩ : syracuseStep 3059585 = 2294689) B2294689
theorem B905115 : Blo 904575 905115 := bstep (se 1 (by rfl) ⟨678836, by rfl⟩ : syracuseStep 905115 = 1357673) B1357673
theorem B3436445 : Blo 904575 3436445 := bstep (se 3 (by rfl) ⟨644333, by rfl⟩ : syracuseStep 3436445 = 1288667) B1288667
theorem B1019803 : Blo 904575 1019803 := bstep (se 1 (by rfl) ⟨764852, by rfl⟩ : syracuseStep 1019803 = 1529705) B1529705
theorem B905167 : Blo 904575 905167 := bstep (se 1 (by rfl) ⟨678875, by rfl⟩ : syracuseStep 905167 = 1357751) B1357751
theorem B905191 : Blo 904575 905191 := bstep (se 1 (by rfl) ⟨678893, by rfl⟩ : syracuseStep 905191 = 1357787) B1357787
theorem B2035817 : Blo 904575 2035817 := bstep (se 2 (by rfl) ⟨763431, by rfl⟩ : syracuseStep 2035817 = 1526863) B1526863
theorem B4583627 : Blo 904575 4583627 := bstep (se 1 (by rfl) ⟨3437720, by rfl⟩ : syracuseStep 4583627 = 6875441) B6875441
theorem B905503 : Blo 904575 905503 := bstep (se 1 (by rfl) ⟨679127, by rfl⟩ : syracuseStep 905503 = 1358255) B1358255
theorem B2576731 : Blo 904575 2576731 := bstep (se 1 (by rfl) ⟨1932548, by rfl⟩ : syracuseStep 2576731 = 3865097) B3865097
theorem B905563 : Blo 904575 905563 := bstep (se 1 (by rfl) ⟨679172, by rfl⟩ : syracuseStep 905563 = 1358345) B1358345
theorem B905583 : Blo 904575 905583 := bstep (se 1 (by rfl) ⟨679187, by rfl⟩ : syracuseStep 905583 = 1358375) B1358375
theorem B905639 : Blo 904575 905639 := bstep (se 1 (by rfl) ⟨679229, by rfl⟩ : syracuseStep 905639 = 1358459) B1358459
theorem B2290103 : Blo 904575 2290103 := bstep (se 1 (by rfl) ⟨1717577, by rfl⟩ : syracuseStep 2290103 = 3435155) B3435155
theorem B13054445 : Blo 904575 13054445 := bstep (se 3 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 13054445 = 4895417) B4895417
theorem B905723 : Blo 904575 905723 := bstep (se 1 (by rfl) ⟨679292, by rfl⟩ : syracuseStep 905723 = 1358585) B1358585
theorem B905791 : Blo 904575 905791 := bstep (se 1 (by rfl) ⟨679343, by rfl⟩ : syracuseStep 905791 = 1358687) B1358687
theorem B905799 : Blo 904575 905799 := bstep (se 1 (by rfl) ⟨679349, by rfl⟩ : syracuseStep 905799 = 1358699) B1358699
theorem B2036303 : Blo 904575 2036303 := bstep (se 1 (by rfl) ⟨1527227, by rfl⟩ : syracuseStep 2036303 = 3054455) B3054455
theorem B59535971 : Blo 904575 59535971 := bstep (se 1 (by rfl) ⟨44651978, by rfl⟩ : syracuseStep 59535971 = 89303957) B89303957
theorem B3871385 : Blo 904575 3871385 := bstep (se 2 (by rfl) ⟨1451769, by rfl⟩ : syracuseStep 3871385 = 2903539) B2903539
theorem B5804743 : Blo 904575 5804743 := bstep (se 1 (by rfl) ⟨4353557, by rfl⟩ : syracuseStep 5804743 = 8707115) B8707115
theorem B2036447 : Blo 904575 2036447 := bstep (se 1 (by rfl) ⟨1527335, by rfl⟩ : syracuseStep 2036447 = 3054671) B3054671
theorem B905951 : Blo 904575 905951 := bstep (se 1 (by rfl) ⟨679463, by rfl⟩ : syracuseStep 905951 = 1358927) B1358927
theorem B906031 : Blo 904575 906031 := bstep (se 1 (by rfl) ⟨679523, by rfl⟩ : syracuseStep 906031 = 1359047) B1359047
theorem B8262479 : Blo 904575 8262479 := bstep (se 1 (by rfl) ⟨6196859, by rfl⟩ : syracuseStep 8262479 = 12393719) B12393719
theorem B906139 : Blo 904575 906139 := bstep (se 1 (by rfl) ⟨679604, by rfl⟩ : syracuseStep 906139 = 1359209) B1359209
theorem B3486659 : Blo 904575 3486659 := bstep (se 1 (by rfl) ⟨2614994, by rfl⟩ : syracuseStep 3486659 = 5229989) B5229989
theorem B906191 : Blo 904575 906191 := bstep (se 1 (by rfl) ⟨679643, by rfl⟩ : syracuseStep 906191 = 1359287) B1359287
theorem B2036699 : Blo 904575 2036699 := bstep (se 1 (by rfl) ⟨1527524, by rfl⟩ : syracuseStep 2036699 = 3055049) B3055049
theorem B1528807 : Blo 904575 1528807 := bstep (se 1 (by rfl) ⟨1146605, by rfl⟩ : syracuseStep 1528807 = 2293211) B2293211
theorem B906215 : Blo 904575 906215 := bstep (se 1 (by rfl) ⟨679661, by rfl⟩ : syracuseStep 906215 = 1359323) B1359323
theorem B5796953 : Blo 904575 5796953 := bstep (se 2 (by rfl) ⟨2173857, by rfl⟩ : syracuseStep 5796953 = 4347715) B4347715
theorem B17396855 : Blo 904575 17396855 := bstep (se 1 (by rfl) ⟨13047641, by rfl⟩ : syracuseStep 17396855 = 26095283) B26095283
theorem B2036879 : Blo 904575 2036879 := bstep (se 1 (by rfl) ⟨1527659, by rfl⟩ : syracuseStep 2036879 = 3055319) B3055319
theorem B17388701 : Blo 904575 17388701 := bstep (se 3 (by rfl) ⟨3260381, by rfl⟩ : syracuseStep 17388701 = 6520763) B6520763
theorem B1357019 : Blo 904575 1357019 := bstep (se 1 (by rfl) ⟨1017764, by rfl⟩ : syracuseStep 1357019 = 2035529) B2035529
theorem B2036969 : Blo 904575 2036969 := bstep (se 2 (by rfl) ⟨763863, by rfl⟩ : syracuseStep 2036969 = 1527727) B1527727
theorem B7943447 : Blo 904575 7943447 := bstep (se 1 (by rfl) ⟨5957585, by rfl⟩ : syracuseStep 7943447 = 11915171) B11915171
theorem B2037023 : Blo 904575 2037023 := bstep (se 1 (by rfl) ⟨1527767, by rfl⟩ : syracuseStep 2037023 = 3055535) B3055535
theorem B1307935 : Blo 904575 1307935 := bstep (se 1 (by rfl) ⟨980951, by rfl⟩ : syracuseStep 1307935 = 1961903) B1961903
theorem B906527 : Blo 904575 906527 := bstep (se 1 (by rfl) ⟨679895, by rfl⟩ : syracuseStep 906527 = 1359791) B1359791
theorem B1357193 : Blo 904575 1357193 := bstep (se 2 (by rfl) ⟨508947, by rfl⟩ : syracuseStep 1357193 = 1017895) B1017895
theorem B2291105 : Blo 904575 2291105 := bstep (se 2 (by rfl) ⟨859164, by rfl⟩ : syracuseStep 2291105 = 1718329) B1718329
theorem B13948481 : Blo 904575 13948481 := bstep (se 2 (by rfl) ⟨5230680, by rfl⟩ : syracuseStep 13948481 = 10461361) B10461361
theorem B2446931 : Blo 904575 2446931 := bstep (se 1 (by rfl) ⟨1835198, by rfl⟩ : syracuseStep 2446931 = 3670397) B3670397
theorem B1717843 : Blo 904575 1717843 := bstep (se 1 (by rfl) ⟨1288382, by rfl⟩ : syracuseStep 1717843 = 2576765) B2576765
theorem B2176607 : Blo 904575 2176607 := bstep (se 1 (by rfl) ⟨1632455, by rfl⟩ : syracuseStep 2176607 = 3264911) B3264911
theorem B3053213 : Blo 904575 3053213 := bstep (se 3 (by rfl) ⟨572477, by rfl⟩ : syracuseStep 3053213 = 1144955) B1144955
theorem B1357547 : Blo 904575 1357547 := bstep (se 1 (by rfl) ⟨1018160, by rfl⟩ : syracuseStep 1357547 = 2036321) B2036321
theorem B2037545 : Blo 904575 2037545 := bstep (se 2 (by rfl) ⟨764079, by rfl⟩ : syracuseStep 2037545 = 1528159) B1528159
theorem B2291561 : Blo 904575 2291561 := bstep (se 2 (by rfl) ⟨859335, by rfl⟩ : syracuseStep 2291561 = 1718671) B1718671
theorem B1357775 : Blo 904575 1357775 := bstep (se 1 (by rfl) ⟨1018331, by rfl⟩ : syracuseStep 1357775 = 2036663) B2036663
theorem B3053753 : Blo 904575 3053753 := bstep (se 2 (by rfl) ⟨1145157, by rfl⟩ : syracuseStep 3053753 = 2290315) B2290315
theorem B3438845 : Blo 904575 3438845 := bstep (se 3 (by rfl) ⟨644783, by rfl⟩ : syracuseStep 3438845 = 1289567) B1289567
theorem B7444759 : Blo 904575 7444759 := bstep (se 1 (by rfl) ⟨5583569, by rfl⟩ : syracuseStep 7444759 = 11167139) B11167139
theorem B1358171 : Blo 904575 1358171 := bstep (se 1 (by rfl) ⟨1018628, by rfl⟩ : syracuseStep 1358171 = 2037257) B2037257
theorem B4585895 : Blo 904575 4585895 := bstep (se 1 (by rfl) ⟨3439421, by rfl⟩ : syracuseStep 4585895 = 6878843) B6878843
theorem B1358399 : Blo 904575 1358399 := bstep (se 1 (by rfl) ⟨1018799, by rfl⟩ : syracuseStep 1358399 = 2037599) B2037599
theorem B4586057 : Blo 904575 4586057 := bstep (se 2 (by rfl) ⟨1719771, by rfl⟩ : syracuseStep 4586057 = 3439543) B3439543
theorem B5159497 : Blo 904575 5159497 := bstep (se 2 (by rfl) ⟨1934811, by rfl⟩ : syracuseStep 5159497 = 3869623) B3869623
theorem B3095147 : Blo 904575 3095147 := bstep (se 1 (by rfl) ⟨2321360, by rfl⟩ : syracuseStep 3095147 = 4642721) B4642721
theorem B1718891 : Blo 904575 1718891 := bstep (se 1 (by rfl) ⟨1289168, by rfl⟩ : syracuseStep 1718891 = 2578337) B2578337
theorem B8059499 : Blo 904575 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B1358519 : Blo 904575 1358519 := bstep (se 1 (by rfl) ⟨1018889, by rfl⟩ : syracuseStep 1358519 = 2037779) B2037779
theorem B4348637 : Blo 904575 4348637 := bstep (se 3 (by rfl) ⟨815369, by rfl⟩ : syracuseStep 4348637 = 1630739) B1630739
theorem B1719119 : Blo 904575 1719119 := bstep (se 1 (by rfl) ⟨1289339, by rfl⟩ : syracuseStep 1719119 = 2578679) B2578679
theorem B2038607 : Blo 904575 2038607 := bstep (se 1 (by rfl) ⟨1528955, by rfl⟩ : syracuseStep 2038607 = 3057911) B3057911
theorem B1145755 : Blo 904575 1145755 := bstep (se 1 (by rfl) ⟨859316, by rfl⟩ : syracuseStep 1145755 = 1718633) B1718633
theorem B1358747 : Blo 904575 1358747 := bstep (se 1 (by rfl) ⟨1019060, by rfl⟩ : syracuseStep 1358747 = 2038121) B2038121
theorem B2448359 : Blo 904575 2448359 := bstep (se 1 (by rfl) ⟨1836269, by rfl⟩ : syracuseStep 2448359 = 3672539) B3672539
theorem B2038823 : Blo 904575 2038823 := bstep (se 1 (by rfl) ⟨1529117, by rfl⟩ : syracuseStep 2038823 = 3058235) B3058235
theorem B2612443 : Blo 904575 2612443 := bstep (se 1 (by rfl) ⟨1959332, by rfl⟩ : syracuseStep 2612443 = 3918665) B3918665
theorem B2039003 : Blo 904575 2039003 := bstep (se 1 (by rfl) ⟨1529252, by rfl⟩ : syracuseStep 2039003 = 3058505) B3058505
theorem B7740683 : Blo 904575 7740683 := bstep (se 1 (by rfl) ⟨5805512, by rfl⟩ : syracuseStep 7740683 = 11611025) B11611025
theorem B1359143 : Blo 904575 1359143 := bstep (se 1 (by rfl) ⟨1019357, by rfl⟩ : syracuseStep 1359143 = 2038715) B2038715
theorem B1359227 : Blo 904575 1359227 := bstep (se 1 (by rfl) ⟨1019420, by rfl⟩ : syracuseStep 1359227 = 2038841) B2038841
theorem B2039201 : Blo 904575 2039201 := bstep (se 2 (by rfl) ⟨764700, by rfl⟩ : syracuseStep 2039201 = 1529401) B1529401
theorem B3530233 : Blo 904575 3530233 := bstep (se 2 (by rfl) ⟨1323837, by rfl⟩ : syracuseStep 3530233 = 2647675) B2647675
theorem B1359353 : Blo 904575 1359353 := bstep (se 2 (by rfl) ⟨509757, by rfl⟩ : syracuseStep 1359353 = 1019515) B1019515
theorem B2293343 : Blo 904575 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B1359455 : Blo 904575 1359455 := bstep (se 1 (by rfl) ⟨1019591, by rfl⟩ : syracuseStep 1359455 = 2039183) B2039183
theorem B3055265 : Blo 904575 3055265 := bstep (se 2 (by rfl) ⟨1145724, by rfl⟩ : syracuseStep 3055265 = 2291449) B2291449
theorem B1933103 : Blo 904575 1933103 := bstep (se 1 (by rfl) ⟨1449827, by rfl⟩ : syracuseStep 1933103 = 2899655) B2899655
theorem B1359671 : Blo 904575 1359671 := bstep (se 1 (by rfl) ⟨1019753, by rfl⟩ : syracuseStep 1359671 = 2039507) B2039507
theorem B2039759 : Blo 904575 2039759 := bstep (se 1 (by rfl) ⟨1529819, by rfl⟩ : syracuseStep 2039759 = 3059639) B3059639
theorem B3055751 : Blo 904575 3055751 := bstep (se 1 (by rfl) ⟨2291813, by rfl⟩ : syracuseStep 3055751 = 4583627) B4583627
theorem B2293991 : Blo 904575 2293991 := bstep (se 1 (by rfl) ⟨1720493, by rfl⟩ : syracuseStep 2293991 = 3440987) B3440987
theorem B6521111 : Blo 904575 6521111 := bstep (se 1 (by rfl) ⟨4890833, by rfl⟩ : syracuseStep 6521111 = 9781667) B9781667
theorem B35324219 : Blo 904575 35324219 := bstep (se 1 (by rfl) ⟨26493164, by rfl⟩ : syracuseStep 35324219 = 52986329) B52986329
theorem B39690647 : Blo 904575 39690647 := bstep (se 1 (by rfl) ⟨29767985, by rfl⟩ : syracuseStep 39690647 = 59535971) B59535971
theorem B2580923 : Blo 904575 2580923 := bstep (se 1 (by rfl) ⟨1935692, by rfl⟩ : syracuseStep 2580923 = 3871385) B3871385
theorem B2294203 : Blo 904575 2294203 := bstep (se 1 (by rfl) ⟨1720652, by rfl⟩ : syracuseStep 2294203 = 3441305) B3441305
theorem B9790105 : Blo 904575 9790105 := bstep (se 2 (by rfl) ⟨3671289, by rfl⟩ : syracuseStep 9790105 = 7342579) B7342579
theorem B5800643 : Blo 904575 5800643 := bstep (se 1 (by rfl) ⟨4350482, by rfl⟩ : syracuseStep 5800643 = 8700965) B8700965
theorem B2294507 : Blo 904575 2294507 := bstep (se 1 (by rfl) ⟨1720880, by rfl⟩ : syracuseStep 2294507 = 3441761) B3441761
theorem B11592467 : Blo 904575 11592467 := bstep (se 1 (by rfl) ⟨8694350, by rfl⟩ : syracuseStep 11592467 = 17388701) B17388701
theorem B18834221 : Blo 904575 18834221 := bstep (se 3 (by rfl) ⟨3531416, by rfl⟩ : syracuseStep 18834221 = 7062833) B7062833
theorem B2294639 : Blo 904575 2294639 := bstep (se 1 (by rfl) ⟨1720979, by rfl⟩ : syracuseStep 2294639 = 3441959) B3441959
theorem B1631287 : Blo 904575 1631287 := bstep (se 1 (by rfl) ⟨1223465, by rfl⟩ : syracuseStep 1631287 = 2446931) B2446931
theorem B1451071 : Blo 904575 1451071 := bstep (se 1 (by rfl) ⟨1088303, by rfl⟩ : syracuseStep 1451071 = 2176607) B2176607
theorem B4588649 : Blo 904575 4588649 := bstep (se 2 (by rfl) ⟨1720743, by rfl⟩ : syracuseStep 4588649 = 3441487) B3441487
theorem B4588811 : Blo 904575 4588811 := bstep (se 1 (by rfl) ⟨3441608, by rfl⟩ : syracuseStep 4588811 = 6883217) B6883217
theorem B6882731 : Blo 904575 6882731 := bstep (se 1 (by rfl) ⟨5162048, by rfl⟩ : syracuseStep 6882731 = 10324097) B10324097
theorem B3057263 : Blo 904575 3057263 := bstep (se 1 (by rfl) ⟨2292947, by rfl⟩ : syracuseStep 3057263 = 4585895) B4585895
theorem B3483257 : Blo 904575 3483257 := bstep (se 2 (by rfl) ⟨1306221, by rfl⟩ : syracuseStep 3483257 = 2612443) B2612443
theorem B3057371 : Blo 904575 3057371 := bstep (se 1 (by rfl) ⟨2293028, by rfl⟩ : syracuseStep 3057371 = 4586057) B4586057
theorem B1632239 : Blo 904575 1632239 := bstep (se 1 (by rfl) ⟨1224179, by rfl⟩ : syracuseStep 1632239 = 2448359) B2448359
theorem B19589201 : Blo 904575 19589201 := bstep (se 2 (by rfl) ⟨7345950, by rfl⟩ : syracuseStep 19589201 = 14691901) B14691901
theorem B5154941 : Blo 904575 5154941 := bstep (se 3 (by rfl) ⟨966551, by rfl⟩ : syracuseStep 5154941 = 1933103) B1933103
theorem B4581521 : Blo 904575 4581521 := bstep (se 2 (by rfl) ⟨1718070, by rfl⟩ : syracuseStep 4581521 = 3436141) B3436141
theorem B16509185 : Blo 904575 16509185 := bstep (se 2 (by rfl) ⟨6190944, by rfl⟩ : syracuseStep 16509185 = 12381889) B12381889
theorem B18827579 : Blo 904575 18827579 := bstep (se 1 (by rfl) ⟨14120684, by rfl⟩ : syracuseStep 18827579 = 28241369) B28241369
theorem B1018399 : Blo 904575 1018399 := bstep (se 1 (by rfl) ⟨763799, by rfl⟩ : syracuseStep 1018399 = 1527599) B1527599
theorem B1526735 : Blo 904575 1526735 := bstep (se 1 (by rfl) ⟨1145051, by rfl⟩ : syracuseStep 1526735 = 2290103) B2290103
theorem B3058667 : Blo 904575 3058667 := bstep (se 1 (by rfl) ⟨2294000, by rfl⟩ : syracuseStep 3058667 = 4588001) B4588001
theorem B8702963 : Blo 904575 8702963 := bstep (se 1 (by rfl) ⟨6527222, by rfl⟩ : syracuseStep 8702963 = 13054445) B13054445
theorem B10316807 : Blo 904575 10316807 := bstep (se 1 (by rfl) ⟨7737605, by rfl⟩ : syracuseStep 10316807 = 15475211) B15475211
theorem B3058721 : Blo 904575 3058721 := bstep (se 2 (by rfl) ⟨1147020, by rfl⟩ : syracuseStep 3058721 = 2294041) B2294041
theorem B3435641 : Blo 904575 3435641 := bstep (se 2 (by rfl) ⟨1288365, by rfl⟩ : syracuseStep 3435641 = 2576731) B2576731
theorem B3435655 : Blo 904575 3435655 := bstep (se 1 (by rfl) ⟨2576741, by rfl⟩ : syracuseStep 3435655 = 5153483) B5153483
theorem B5508319 : Blo 904575 5508319 := bstep (se 1 (by rfl) ⟨4131239, by rfl⟩ : syracuseStep 5508319 = 8262479) B8262479
theorem B2616563 : Blo 904575 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B496487885 : Blo 904575 496487885 := bstep (se 3 (by rfl) ⟨93091478, by rfl⟩ : syracuseStep 496487885 = 186182957) B186182957
theorem B904679 : Blo 904575 904679 := bstep (se 1 (by rfl) ⟨678509, by rfl⟩ : syracuseStep 904679 = 1357019) B1357019
theorem B5295631 : Blo 904575 5295631 := bstep (se 1 (by rfl) ⟨3971723, by rfl⟩ : syracuseStep 5295631 = 7943447) B7943447
theorem B904795 : Blo 904575 904795 := bstep (se 1 (by rfl) ⟨678596, by rfl⟩ : syracuseStep 904795 = 1357193) B1357193
theorem B1527403 : Blo 904575 1527403 := bstep (se 1 (by rfl) ⟨1145552, by rfl⟩ : syracuseStep 1527403 = 2291105) B2291105
theorem B2035475 : Blo 904575 2035475 := bstep (se 1 (by rfl) ⟨1526606, by rfl⟩ : syracuseStep 2035475 = 3053213) B3053213
theorem B905031 : Blo 904575 905031 := bstep (se 1 (by rfl) ⟨678773, by rfl⟩ : syracuseStep 905031 = 1357547) B1357547
theorem B1527673 : Blo 904575 1527673 := bstep (se 2 (by rfl) ⟨572877, by rfl⟩ : syracuseStep 1527673 = 1145755) B1145755
theorem B1527707 : Blo 904575 1527707 := bstep (se 1 (by rfl) ⟨1145780, by rfl⟩ : syracuseStep 1527707 = 2291561) B2291561
theorem B905183 : Blo 904575 905183 := bstep (se 1 (by rfl) ⟨678887, by rfl⟩ : syracuseStep 905183 = 1357775) B1357775
theorem B2035835 : Blo 904575 2035835 := bstep (se 1 (by rfl) ⟨1526876, by rfl⟩ : syracuseStep 2035835 = 3053753) B3053753
theorem B37195949 : Blo 904575 37195949 := bstep (se 3 (by rfl) ⟨6974240, by rfl⟩ : syracuseStep 37195949 = 13948481) B13948481
theorem B5796029 : Blo 904575 5796029 := bstep (se 3 (by rfl) ⟨1086755, by rfl⟩ : syracuseStep 5796029 = 2173511) B2173511
theorem B905447 : Blo 904575 905447 := bstep (se 1 (by rfl) ⟨679085, by rfl⟩ : syracuseStep 905447 = 1358171) B1358171
theorem B4894985 : Blo 904575 4894985 := bstep (se 2 (by rfl) ⟨1835619, by rfl⟩ : syracuseStep 4894985 = 3671239) B3671239
theorem B905599 : Blo 904575 905599 := bstep (se 1 (by rfl) ⟨679199, by rfl⟩ : syracuseStep 905599 = 1358399) B1358399
theorem B2036105 : Blo 904575 2036105 := bstep (se 2 (by rfl) ⟨763539, by rfl⟩ : syracuseStep 2036105 = 1527079) B1527079
theorem B905679 : Blo 904575 905679 := bstep (se 1 (by rfl) ⟨679259, by rfl⟩ : syracuseStep 905679 = 1358519) B1358519
theorem B4895225 : Blo 904575 4895225 := bstep (se 2 (by rfl) ⟨1835709, by rfl⟩ : syracuseStep 4895225 = 3671419) B3671419
theorem B4583951 : Blo 904575 4583951 := bstep (se 1 (by rfl) ⟨3437963, by rfl⟩ : syracuseStep 4583951 = 6875927) B6875927
theorem B905831 : Blo 904575 905831 := bstep (se 1 (by rfl) ⟨679373, by rfl⟩ : syracuseStep 905831 = 1358747) B1358747
theorem B4706977 : Blo 904575 4706977 := bstep (se 2 (by rfl) ⟨1765116, by rfl⟩ : syracuseStep 4706977 = 3530233) B3530233
theorem B2290457 : Blo 904575 2290457 := bstep (se 2 (by rfl) ⟨858921, by rfl⟩ : syracuseStep 2290457 = 1717843) B1717843
theorem B15479585 : Blo 904575 15479585 := bstep (se 2 (by rfl) ⟨5804844, by rfl⟩ : syracuseStep 15479585 = 11609689) B11609689
theorem B906095 : Blo 904575 906095 := bstep (se 1 (by rfl) ⟨679571, by rfl⟩ : syracuseStep 906095 = 1359143) B1359143
theorem B906151 : Blo 904575 906151 := bstep (se 1 (by rfl) ⟨679613, by rfl⟩ : syracuseStep 906151 = 1359227) B1359227
theorem B906235 : Blo 904575 906235 := bstep (se 1 (by rfl) ⟨679676, by rfl⟩ : syracuseStep 906235 = 1359353) B1359353
theorem B1356863 : Blo 904575 1356863 := bstep (se 1 (by rfl) ⟨1017647, by rfl⟩ : syracuseStep 1356863 = 2035295) B2035295
theorem B2290751 : Blo 904575 2290751 := bstep (se 1 (by rfl) ⟨1718063, by rfl⟩ : syracuseStep 2290751 = 3436127) B3436127
theorem B1528895 : Blo 904575 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B906303 : Blo 904575 906303 := bstep (se 1 (by rfl) ⟨679727, by rfl⟩ : syracuseStep 906303 = 1359455) B1359455
theorem B1356905 : Blo 904575 1356905 := bstep (se 2 (by rfl) ⟨508839, by rfl⟩ : syracuseStep 1356905 = 1017679) B1017679
theorem B2036843 : Blo 904575 2036843 := bstep (se 1 (by rfl) ⟨1527632, by rfl⟩ : syracuseStep 2036843 = 3055265) B3055265
theorem B1357007 : Blo 904575 1357007 := bstep (se 1 (by rfl) ⟨1017755, by rfl⟩ : syracuseStep 1357007 = 2035511) B2035511
theorem B906447 : Blo 904575 906447 := bstep (se 1 (by rfl) ⟨679835, by rfl⟩ : syracuseStep 906447 = 1359671) B1359671
theorem B2290963 : Blo 904575 2290963 := bstep (se 1 (by rfl) ⟨1718222, by rfl⟩ : syracuseStep 2290963 = 3436445) B3436445
theorem B1357211 : Blo 904575 1357211 := bstep (se 1 (by rfl) ⟨1017908, by rfl⟩ : syracuseStep 1357211 = 2035817) B2035817
theorem B6534665 : Blo 904575 6534665 := bstep (se 2 (by rfl) ⟨2450499, by rfl⟩ : syracuseStep 6534665 = 4900999) B4900999
theorem B1529455 : Blo 904575 1529455 := bstep (se 1 (by rfl) ⟨1147091, by rfl⟩ : syracuseStep 1529455 = 2294183) B2294183
theorem B1357433 : Blo 904575 1357433 := bstep (se 2 (by rfl) ⟨509037, by rfl⟩ : syracuseStep 1357433 = 1018075) B1018075
theorem B5158565 : Blo 904575 5158565 := bstep (se 4 (by rfl) ⟨483615, by rfl⟩ : syracuseStep 5158565 = 967231) B967231
theorem B2037419 : Blo 904575 2037419 := bstep (se 1 (by rfl) ⟨1528064, by rfl⟩ : syracuseStep 2037419 = 3056129) B3056129
theorem B9926345 : Blo 904575 9926345 := bstep (se 2 (by rfl) ⟨3722379, by rfl⟩ : syracuseStep 9926345 = 7444759) B7444759
theorem B1529563 : Blo 904575 1529563 := bstep (se 1 (by rfl) ⟨1147172, by rfl⟩ : syracuseStep 1529563 = 2294345) B2294345
theorem B1357535 : Blo 904575 1357535 := bstep (se 1 (by rfl) ⟨1018151, by rfl⟩ : syracuseStep 1357535 = 2036303) B2036303
theorem B2578223 : Blo 904575 2578223 := bstep (se 1 (by rfl) ⟨1933667, by rfl⟩ : syracuseStep 2578223 = 3867335) B3867335
theorem B3053375 : Blo 904575 3053375 := bstep (se 1 (by rfl) ⟨2290031, by rfl⟩ : syracuseStep 3053375 = 4580063) B4580063
theorem B1357631 : Blo 904575 1357631 := bstep (se 1 (by rfl) ⟨1018223, by rfl⟩ : syracuseStep 1357631 = 2036447) B2036447
theorem B1357799 : Blo 904575 1357799 := bstep (se 1 (by rfl) ⟨1018349, by rfl⟩ : syracuseStep 1357799 = 2036699) B2036699
theorem B2037743 : Blo 904575 2037743 := bstep (se 1 (by rfl) ⟨1528307, by rfl⟩ : syracuseStep 2037743 = 3056615) B3056615
theorem B1357817 : Blo 904575 1357817 := bstep (se 2 (by rfl) ⟨509181, by rfl⟩ : syracuseStep 1357817 = 1018363) B1018363
theorem B3864635 : Blo 904575 3864635 := bstep (se 1 (by rfl) ⟨2898476, by rfl⟩ : syracuseStep 3864635 = 5796953) B5796953
theorem B11597903 : Blo 904575 11597903 := bstep (se 1 (by rfl) ⟨8698427, by rfl⟩ : syracuseStep 11597903 = 17396855) B17396855
theorem B1357919 : Blo 904575 1357919 := bstep (se 1 (by rfl) ⟨1018439, by rfl⟩ : syracuseStep 1357919 = 2036879) B2036879
theorem B6879329 : Blo 904575 6879329 := bstep (se 2 (by rfl) ⟨2579748, by rfl⟩ : syracuseStep 6879329 = 5159497) B5159497
theorem B1357979 : Blo 904575 1357979 := bstep (se 1 (by rfl) ⟨1018484, by rfl⟩ : syracuseStep 1357979 = 2036969) B2036969
theorem B1358015 : Blo 904575 1358015 := bstep (se 1 (by rfl) ⟨1018511, by rfl⟩ : syracuseStep 1358015 = 2037023) B2037023
theorem B2037959 : Blo 904575 2037959 := bstep (se 1 (by rfl) ⟨1528469, by rfl⟩ : syracuseStep 2037959 = 3056939) B3056939
theorem B1358057 : Blo 904575 1358057 := bstep (se 2 (by rfl) ⟨509271, by rfl⟩ : syracuseStep 1358057 = 1018543) B1018543
theorem B7739657 : Blo 904575 7739657 := bstep (se 2 (by rfl) ⟨2902371, by rfl⟩ : syracuseStep 7739657 = 5804743) B5804743
theorem B2038139 : Blo 904575 2038139 := bstep (se 1 (by rfl) ⟨1528604, by rfl⟩ : syracuseStep 2038139 = 3057209) B3057209
theorem B1358363 : Blo 904575 1358363 := bstep (se 1 (by rfl) ⟨1018772, by rfl⟩ : syracuseStep 1358363 = 2037545) B2037545
theorem B1358441 : Blo 904575 1358441 := bstep (se 2 (by rfl) ⟨509415, by rfl⟩ : syracuseStep 1358441 = 1018831) B1018831
theorem B1718921 : Blo 904575 1718921 := bstep (se 2 (by rfl) ⟨644595, by rfl⟩ : syracuseStep 1718921 = 1289191) B1289191
theorem B2038409 : Blo 904575 2038409 := bstep (se 2 (by rfl) ⟨764403, by rfl⟩ : syracuseStep 2038409 = 1528807) B1528807
theorem B2292563 : Blo 904575 2292563 := bstep (se 1 (by rfl) ⟨1719422, by rfl⟩ : syracuseStep 2292563 = 3438845) B3438845
theorem B6527915 : Blo 904575 6527915 := bstep (se 1 (by rfl) ⟨4895936, by rfl⟩ : syracuseStep 6527915 = 9791873) B9791873
theorem B1743913 : Blo 904575 1743913 := bstep (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) B1307935
theorem B24796205 : Blo 904575 24796205 := bstep (se 3 (by rfl) ⟨4649288, by rfl⟩ : syracuseStep 24796205 = 9298577) B9298577
theorem B2063431 : Blo 904575 2063431 := bstep (se 1 (by rfl) ⟨1547573, by rfl⟩ : syracuseStep 2063431 = 3095147) B3095147
theorem B1145927 : Blo 904575 1145927 := bstep (se 1 (by rfl) ⟨859445, by rfl⟩ : syracuseStep 1145927 = 1718891) B1718891
theorem B5372999 : Blo 904575 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B1358969 : Blo 904575 1358969 := bstep (se 2 (by rfl) ⟨509613, by rfl⟩ : syracuseStep 1358969 = 1019227) B1019227
theorem B2899091 : Blo 904575 2899091 := bstep (se 1 (by rfl) ⟨2174318, by rfl⟩ : syracuseStep 2899091 = 4348637) B4348637
theorem B2038967 : Blo 904575 2038967 := bstep (se 1 (by rfl) ⟨1529225, by rfl⟩ : syracuseStep 2038967 = 3058451) B3058451
theorem B1146079 : Blo 904575 1146079 := bstep (se 1 (by rfl) ⟨859559, by rfl⟩ : syracuseStep 1146079 = 1719119) B1719119
theorem B1359071 : Blo 904575 1359071 := bstep (se 1 (by rfl) ⟨1019303, by rfl⟩ : syracuseStep 1359071 = 2038607) B2038607
theorem B1359113 : Blo 904575 1359113 := bstep (se 2 (by rfl) ⟨509667, by rfl⟩ : syracuseStep 1359113 = 1019335) B1019335
theorem B10321181 : Blo 904575 10321181 := bstep (se 3 (by rfl) ⟨1935221, by rfl⟩ : syracuseStep 10321181 = 3870443) B3870443
theorem B3054887 : Blo 904575 3054887 := bstep (se 1 (by rfl) ⟨2291165, by rfl⟩ : syracuseStep 3054887 = 4582331) B4582331
theorem B1359215 : Blo 904575 1359215 := bstep (se 1 (by rfl) ⟨1019411, by rfl⟩ : syracuseStep 1359215 = 2038823) B2038823
theorem B1359335 : Blo 904575 1359335 := bstep (se 1 (by rfl) ⟨1019501, by rfl⟩ : syracuseStep 1359335 = 2039003) B2039003
theorem B5160455 : Blo 904575 5160455 := bstep (se 1 (by rfl) ⟨3870341, by rfl⟩ : syracuseStep 5160455 = 7740683) B7740683
theorem B1359467 : Blo 904575 1359467 := bstep (se 1 (by rfl) ⟨1019600, by rfl⟩ : syracuseStep 1359467 = 2039201) B2039201
theorem B1359593 : Blo 904575 1359593 := bstep (se 2 (by rfl) ⟨509847, by rfl⟩ : syracuseStep 1359593 = 1019695) B1019695
theorem B2039543 : Blo 904575 2039543 := bstep (se 1 (by rfl) ⟨1529657, by rfl⟩ : syracuseStep 2039543 = 3059315) B3059315
theorem B9297757 : Blo 904575 9297757 := bstep (se 3 (by rfl) ⟨1743329, by rfl⟩ : syracuseStep 9297757 = 3486659) B3486659
theorem B1359737 : Blo 904575 1359737 := bstep (se 2 (by rfl) ⟨509901, by rfl⟩ : syracuseStep 1359737 = 1019803) B1019803
theorem B2039723 : Blo 904575 2039723 := bstep (se 1 (by rfl) ⟨1529792, by rfl⟩ : syracuseStep 2039723 = 3059585) B3059585
theorem B1359839 : Blo 904575 1359839 := bstep (se 1 (by rfl) ⟨1019879, by rfl⟩ : syracuseStep 1359839 = 2039759) B2039759
theorem B24797299 : Blo 904575 24797299 := bstep (se 1 (by rfl) ⟨18597974, by rfl⟩ : syracuseStep 24797299 = 37195949) B37195949
theorem B3055805 : Blo 904575 3055805 := bstep (se 3 (by rfl) ⟨572963, by rfl⟩ : syracuseStep 3055805 = 1145927) B1145927
theorem B26460431 : Blo 904575 26460431 := bstep (se 1 (by rfl) ⟨19845323, by rfl⟩ : syracuseStep 26460431 = 39690647) B39690647
theorem B1720615 : Blo 904575 1720615 := bstep (se 1 (by rfl) ⟨1290461, by rfl⟩ : syracuseStep 1720615 = 2580923) B2580923
theorem B3055967 : Blo 904575 3055967 := bstep (se 1 (by rfl) ⟨2291975, by rfl⟩ : syracuseStep 3055967 = 4583951) B4583951
theorem B3867095 : Blo 904575 3867095 := bstep (se 1 (by rfl) ⟨2900321, by rfl⟩ : syracuseStep 3867095 = 5800643) B5800643
theorem B6275969 : Blo 904575 6275969 := bstep (se 2 (by rfl) ⟨2353488, by rfl⟩ : syracuseStep 6275969 = 4706977) B4706977
theorem B4588487 : Blo 904575 4588487 := bstep (se 1 (by rfl) ⟨3441365, by rfl⟩ : syracuseStep 4588487 = 6882731) B6882731
theorem B1323967693 : Blo 904575 1323967693 := bstep (se 3 (by rfl) ⟨248243942, by rfl⟩ : syracuseStep 1323967693 = 496487885) B496487885
theorem B13059467 : Blo 904575 13059467 := bstep (se 1 (by rfl) ⟨9794600, by rfl⟩ : syracuseStep 13059467 = 19589201) B19589201
theorem B1934761 : Blo 904575 1934761 := bstep (se 2 (by rfl) ⟨725535, by rfl⟩ : syracuseStep 1934761 = 1451071) B1451071
theorem B4580873 : Blo 904575 4580873 := bstep (se 2 (by rfl) ⟨1717827, by rfl⟩ : syracuseStep 4580873 = 3435655) B3435655
theorem B26470253 : Blo 904575 26470253 := bstep (se 3 (by rfl) ⟨4963172, by rfl⟩ : syracuseStep 26470253 = 9926345) B9926345
theorem B4351943 : Blo 904575 4351943 := bstep (se 1 (by rfl) ⟨3263957, by rfl⟩ : syracuseStep 4351943 = 6527915) B6527915
theorem B1017823 : Blo 904575 1017823 := bstep (se 1 (by rfl) ⟨763367, by rfl⟩ : syracuseStep 1017823 = 1526735) B1526735
theorem B5801975 : Blo 904575 5801975 := bstep (se 1 (by rfl) ⟨4351481, by rfl⟩ : syracuseStep 5801975 = 8702963) B8702963
theorem B3581999 : Blo 904575 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B12397009 : Blo 904575 12397009 := bstep (se 2 (by rfl) ⟨4648878, by rfl⟩ : syracuseStep 12397009 = 9297757) B9297757
theorem B1018471 : Blo 904575 1018471 := bstep (se 1 (by rfl) ⟨763853, by rfl⟩ : syracuseStep 1018471 = 1527707) B1527707
theorem B3263323 : Blo 904575 3263323 := bstep (se 1 (by rfl) ⟨2447492, by rfl⟩ : syracuseStep 3263323 = 4894985) B4894985
theorem B3263483 : Blo 904575 3263483 := bstep (se 1 (by rfl) ⟨2447612, by rfl⟩ : syracuseStep 3263483 = 4895225) B4895225
theorem B7728311 : Blo 904575 7728311 := bstep (se 1 (by rfl) ⟨5796233, by rfl⟩ : syracuseStep 7728311 = 11592467) B11592467
theorem B1526971 : Blo 904575 1526971 := bstep (se 1 (by rfl) ⟨1145228, by rfl⟩ : syracuseStep 1526971 = 2290457) B2290457
theorem B3058937 : Blo 904575 3058937 := bstep (se 2 (by rfl) ⟨1147101, by rfl⟩ : syracuseStep 3058937 = 2294203) B2294203
theorem B904575 : Blo 904575 904575 := bstep (se 1 (by rfl) ⟨678431, by rfl⟩ : syracuseStep 904575 = 1356863) B1356863
theorem B1527167 : Blo 904575 1527167 := bstep (se 1 (by rfl) ⟨1145375, by rfl⟩ : syracuseStep 1527167 = 2290751) B2290751
theorem B1019263 : Blo 904575 1019263 := bstep (se 1 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 1019263 = 1528895) B1528895
theorem B904603 : Blo 904575 904603 := bstep (se 1 (by rfl) ⟨678452, by rfl⟩ : syracuseStep 904603 = 1356905) B1356905
theorem B3059099 : Blo 904575 3059099 := bstep (se 1 (by rfl) ⟨2294324, by rfl⟩ : syracuseStep 3059099 = 4588649) B4588649
theorem B904671 : Blo 904575 904671 := bstep (se 1 (by rfl) ⟨678503, by rfl⟩ : syracuseStep 904671 = 1357007) B1357007
theorem B3059207 : Blo 904575 3059207 := bstep (se 1 (by rfl) ⟨2294405, by rfl⟩ : syracuseStep 3059207 = 4588811) B4588811
theorem B13053473 : Blo 904575 13053473 := bstep (se 2 (by rfl) ⟨4895052, by rfl⟩ : syracuseStep 13053473 = 9790105) B9790105
theorem B904807 : Blo 904575 904807 := bstep (se 1 (by rfl) ⟨678605, by rfl⟩ : syracuseStep 904807 = 1357211) B1357211
theorem B904955 : Blo 904575 904955 := bstep (se 1 (by rfl) ⟨678716, by rfl⟩ : syracuseStep 904955 = 1357433) B1357433
theorem B905023 : Blo 904575 905023 := bstep (se 1 (by rfl) ⟨678767, by rfl⟩ : syracuseStep 905023 = 1357535) B1357535
theorem B2035583 : Blo 904575 2035583 := bstep (se 1 (by rfl) ⟨1526687, by rfl⟩ : syracuseStep 2035583 = 3053375) B3053375
theorem B905087 : Blo 904575 905087 := bstep (se 1 (by rfl) ⟨678815, by rfl⟩ : syracuseStep 905087 = 1357631) B1357631
theorem B905199 : Blo 904575 905199 := bstep (se 1 (by rfl) ⟨678899, by rfl⟩ : syracuseStep 905199 = 1357799) B1357799
theorem B905211 : Blo 904575 905211 := bstep (se 1 (by rfl) ⟨678908, by rfl⟩ : syracuseStep 905211 = 1357817) B1357817
theorem B2576423 : Blo 904575 2576423 := bstep (se 1 (by rfl) ⟨1932317, by rfl⟩ : syracuseStep 2576423 = 3864635) B3864635
theorem B905279 : Blo 904575 905279 := bstep (se 1 (by rfl) ⟨678959, by rfl⟩ : syracuseStep 905279 = 1357919) B1357919
theorem B2175049 : Blo 904575 2175049 := bstep (se 2 (by rfl) ⟨815643, by rfl⟩ : syracuseStep 2175049 = 1631287) B1631287
theorem B3436627 : Blo 904575 3436627 := bstep (se 1 (by rfl) ⟨2577470, by rfl⟩ : syracuseStep 3436627 = 5154941) B5154941
theorem B905319 : Blo 904575 905319 := bstep (se 1 (by rfl) ⟨678989, by rfl⟩ : syracuseStep 905319 = 1357979) B1357979
theorem B905343 : Blo 904575 905343 := bstep (se 1 (by rfl) ⟨679007, by rfl⟩ : syracuseStep 905343 = 1358015) B1358015
theorem B905371 : Blo 904575 905371 := bstep (se 1 (by rfl) ⟨679028, by rfl⟩ : syracuseStep 905371 = 1358057) B1358057
theorem B11006123 : Blo 904575 11006123 := bstep (se 1 (by rfl) ⟨8254592, by rfl⟩ : syracuseStep 11006123 = 16509185) B16509185
theorem B1528105 : Blo 904575 1528105 := bstep (se 2 (by rfl) ⟨573039, by rfl⟩ : syracuseStep 1528105 = 1146079) B1146079
theorem B7344425 : Blo 904575 7344425 := bstep (se 2 (by rfl) ⟨2754159, by rfl⟩ : syracuseStep 7344425 = 5508319) B5508319
theorem B905575 : Blo 904575 905575 := bstep (se 1 (by rfl) ⟨679181, by rfl⟩ : syracuseStep 905575 = 1358363) B1358363
theorem B4583789 : Blo 904575 4583789 := bstep (se 3 (by rfl) ⟨859460, by rfl⟩ : syracuseStep 4583789 = 1718921) B1718921
theorem B905627 : Blo 904575 905627 := bstep (se 1 (by rfl) ⟨679220, by rfl⟩ : syracuseStep 905627 = 1358441) B1358441
theorem B1528375 : Blo 904575 1528375 := bstep (se 1 (by rfl) ⟨1146281, by rfl⟩ : syracuseStep 1528375 = 2292563) B2292563
theorem B6877871 : Blo 904575 6877871 := bstep (se 1 (by rfl) ⟨5158403, by rfl⟩ : syracuseStep 6877871 = 10316807) B10316807
theorem B2290427 : Blo 904575 2290427 := bstep (se 1 (by rfl) ⟨1717820, by rfl⟩ : syracuseStep 2290427 = 3435641) B3435641
theorem B905979 : Blo 904575 905979 := bstep (se 1 (by rfl) ⟨679484, by rfl⟩ : syracuseStep 905979 = 1358969) B1358969
theorem B2036537 : Blo 904575 2036537 := bstep (se 2 (by rfl) ⟨763701, by rfl⟩ : syracuseStep 2036537 = 1527403) B1527403
theorem B906047 : Blo 904575 906047 := bstep (se 1 (by rfl) ⟨679535, by rfl⟩ : syracuseStep 906047 = 1359071) B1359071
theorem B906075 : Blo 904575 906075 := bstep (se 1 (by rfl) ⟨679556, by rfl⟩ : syracuseStep 906075 = 1359113) B1359113
theorem B2036591 : Blo 904575 2036591 := bstep (se 1 (by rfl) ⟨1527443, by rfl⟩ : syracuseStep 2036591 = 3054887) B3054887
theorem B906143 : Blo 904575 906143 := bstep (se 1 (by rfl) ⟨679607, by rfl⟩ : syracuseStep 906143 = 1359215) B1359215
theorem B906223 : Blo 904575 906223 := bstep (se 1 (by rfl) ⟨679667, by rfl⟩ : syracuseStep 906223 = 1359335) B1359335
theorem B906311 : Blo 904575 906311 := bstep (se 1 (by rfl) ⟨679733, by rfl⟩ : syracuseStep 906311 = 1359467) B1359467
theorem B906395 : Blo 904575 906395 := bstep (se 1 (by rfl) ⟨679796, by rfl⟩ : syracuseStep 906395 = 1359593) B1359593
theorem B2036897 : Blo 904575 2036897 := bstep (se 2 (by rfl) ⟨763836, by rfl⟩ : syracuseStep 2036897 = 1527673) B1527673
theorem B1356983 : Blo 904575 1356983 := bstep (se 1 (by rfl) ⟨1017737, by rfl⟩ : syracuseStep 1356983 = 2035475) B2035475
theorem B906491 : Blo 904575 906491 := bstep (se 1 (by rfl) ⟨679868, by rfl⟩ : syracuseStep 906491 = 1359737) B1359737
theorem B906559 : Blo 904575 906559 := bstep (se 1 (by rfl) ⟨679919, by rfl⟩ : syracuseStep 906559 = 1359839) B1359839
theorem B1357223 : Blo 904575 1357223 := bstep (se 1 (by rfl) ⟨1017917, by rfl⟩ : syracuseStep 1357223 = 2035835) B2035835
theorem B2037167 : Blo 904575 2037167 := bstep (se 1 (by rfl) ⟨1527875, by rfl⟩ : syracuseStep 2037167 = 3055751) B3055751
theorem B3864019 : Blo 904575 3864019 := bstep (se 1 (by rfl) ⟨2898014, by rfl⟩ : syracuseStep 3864019 = 5796029) B5796029
theorem B1529327 : Blo 904575 1529327 := bstep (se 1 (by rfl) ⟨1146995, by rfl⟩ : syracuseStep 1529327 = 2293991) B2293991
theorem B4347407 : Blo 904575 4347407 := bstep (se 1 (by rfl) ⟨3260555, by rfl⟩ : syracuseStep 4347407 = 6521111) B6521111
theorem B1357403 : Blo 904575 1357403 := bstep (se 1 (by rfl) ⟨1018052, by rfl⟩ : syracuseStep 1357403 = 2036105) B2036105
theorem B7730909 : Blo 904575 7730909 := bstep (se 3 (by rfl) ⟨1449545, by rfl⟩ : syracuseStep 7730909 = 2899091) B2899091
theorem B1529671 : Blo 904575 1529671 := bstep (se 1 (by rfl) ⟨1147253, by rfl⟩ : syracuseStep 1529671 = 2294507) B2294507
theorem B10319723 : Blo 904575 10319723 := bstep (se 1 (by rfl) ⟨7739792, by rfl⟩ : syracuseStep 10319723 = 15479585) B15479585
theorem B12556147 : Blo 904575 12556147 := bstep (se 1 (by rfl) ⟨9417110, by rfl⟩ : syracuseStep 12556147 = 18834221) B18834221
theorem B1529759 : Blo 904575 1529759 := bstep (se 1 (by rfl) ⟨1147319, by rfl⟩ : syracuseStep 1529759 = 2294639) B2294639
theorem B6977501 : Blo 904575 6977501 := bstep (se 3 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 6977501 = 2616563) B2616563
theorem B1357865 : Blo 904575 1357865 := bstep (se 2 (by rfl) ⟨509199, by rfl⟩ : syracuseStep 1357865 = 1018399) B1018399
theorem B1357895 : Blo 904575 1357895 := bstep (se 1 (by rfl) ⟨1018421, by rfl⟩ : syracuseStep 1357895 = 2036843) B2036843
theorem B50206877 : Blo 904575 50206877 := bstep (se 3 (by rfl) ⟨9413789, by rfl⟩ : syracuseStep 50206877 = 18827579) B18827579
theorem B94197917 : Blo 904575 94197917 := bstep (se 3 (by rfl) ⟨17662109, by rfl⟩ : syracuseStep 94197917 = 35324219) B35324219
theorem B4356443 : Blo 904575 4356443 := bstep (se 1 (by rfl) ⟨3267332, by rfl⟩ : syracuseStep 4356443 = 6534665) B6534665
theorem B2038175 : Blo 904575 2038175 := bstep (se 1 (by rfl) ⟨1528631, by rfl⟩ : syracuseStep 2038175 = 3057263) B3057263
theorem B3439043 : Blo 904575 3439043 := bstep (se 1 (by rfl) ⟨2579282, by rfl⟩ : syracuseStep 3439043 = 5158565) B5158565
theorem B1358279 : Blo 904575 1358279 := bstep (se 1 (by rfl) ⟨1018709, by rfl⟩ : syracuseStep 1358279 = 2037419) B2037419
theorem B2038247 : Blo 904575 2038247 := bstep (se 1 (by rfl) ⟨1528685, by rfl⟩ : syracuseStep 2038247 = 3057371) B3057371
theorem B1718815 : Blo 904575 1718815 := bstep (se 1 (by rfl) ⟨1289111, by rfl⟩ : syracuseStep 1718815 = 2578223) B2578223
theorem B1358495 : Blo 904575 1358495 := bstep (se 1 (by rfl) ⟨1018871, by rfl⟩ : syracuseStep 1358495 = 2037743) B2037743
theorem B1088159 : Blo 904575 1088159 := bstep (se 1 (by rfl) ⟨816119, by rfl⟩ : syracuseStep 1088159 = 1632239) B1632239
theorem B7731935 : Blo 904575 7731935 := bstep (se 1 (by rfl) ⟨5798951, by rfl⟩ : syracuseStep 7731935 = 11597903) B11597903
theorem B2325217 : Blo 904575 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B4586219 : Blo 904575 4586219 := bstep (se 1 (by rfl) ⟨3439664, by rfl⟩ : syracuseStep 4586219 = 6879329) B6879329
theorem B2751241 : Blo 904575 2751241 := bstep (se 2 (by rfl) ⟨1031715, by rfl⟩ : syracuseStep 2751241 = 2063431) B2063431
theorem B3054347 : Blo 904575 3054347 := bstep (se 1 (by rfl) ⟨2290760, by rfl⟩ : syracuseStep 3054347 = 4581521) B4581521
theorem B1358639 : Blo 904575 1358639 := bstep (se 1 (by rfl) ⟨1018979, by rfl⟩ : syracuseStep 1358639 = 2037959) B2037959
theorem B5159771 : Blo 904575 5159771 := bstep (se 1 (by rfl) ⟨3869828, by rfl⟩ : syracuseStep 5159771 = 7739657) B7739657
theorem B1358759 : Blo 904575 1358759 := bstep (se 1 (by rfl) ⟨1019069, by rfl⟩ : syracuseStep 1358759 = 2038139) B2038139
theorem B9288685 : Blo 904575 9288685 := bstep (se 3 (by rfl) ⟨1741628, by rfl⟩ : syracuseStep 9288685 = 3483257) B3483257
theorem B3054617 : Blo 904575 3054617 := bstep (se 2 (by rfl) ⟨1145481, by rfl⟩ : syracuseStep 3054617 = 2290963) B2290963
theorem B1358939 : Blo 904575 1358939 := bstep (se 1 (by rfl) ⟨1019204, by rfl⟩ : syracuseStep 1358939 = 2038409) B2038409
theorem B2039111 : Blo 904575 2039111 := bstep (se 1 (by rfl) ⟨1529333, by rfl⟩ : syracuseStep 2039111 = 3058667) B3058667
theorem B7060841 : Blo 904575 7060841 := bstep (se 2 (by rfl) ⟨2647815, by rfl⟩ : syracuseStep 7060841 = 5295631) B5295631
theorem B2039147 : Blo 904575 2039147 := bstep (se 1 (by rfl) ⟨1529360, by rfl⟩ : syracuseStep 2039147 = 3058721) B3058721
theorem B16530803 : Blo 904575 16530803 := bstep (se 1 (by rfl) ⟨12398102, by rfl⟩ : syracuseStep 16530803 = 24796205) B24796205
theorem B1359311 : Blo 904575 1359311 := bstep (se 1 (by rfl) ⟨1019483, by rfl⟩ : syracuseStep 1359311 = 2038967) B2038967
theorem B2039273 : Blo 904575 2039273 := bstep (se 2 (by rfl) ⟨764727, by rfl⟩ : syracuseStep 2039273 = 1529455) B1529455
theorem B6880787 : Blo 904575 6880787 := bstep (se 1 (by rfl) ⟨5160590, by rfl⟩ : syracuseStep 6880787 = 10321181) B10321181
theorem B2039417 : Blo 904575 2039417 := bstep (se 2 (by rfl) ⟨764781, by rfl⟩ : syracuseStep 2039417 = 1529563) B1529563
theorem B3440303 : Blo 904575 3440303 := bstep (se 1 (by rfl) ⟨2580227, by rfl⟩ : syracuseStep 3440303 = 5160455) B5160455
theorem B1359695 : Blo 904575 1359695 := bstep (se 1 (by rfl) ⟨1019771, by rfl⟩ : syracuseStep 1359695 = 2039543) B2039543
theorem B1359815 : Blo 904575 1359815 := bstep (se 1 (by rfl) ⟨1019861, by rfl⟩ : syracuseStep 1359815 = 2039723) B2039723
theorem B2900065 : Blo 904575 2900065 := bstep (se 2 (by rfl) ⟨1087524, by rfl⟩ : syracuseStep 2900065 = 2175049) B2175049
theorem B33063065 : Blo 904575 33063065 := bstep (se 2 (by rfl) ⟨12398649, by rfl⟩ : syracuseStep 33063065 = 24797299) B24797299
theorem B3055859 : Blo 904575 3055859 := bstep (se 1 (by rfl) ⟨2291894, by rfl⟩ : syracuseStep 3055859 = 4583789) B4583789
theorem B2294153 : Blo 904575 2294153 := bstep (se 2 (by rfl) ⟨860307, by rfl⟩ : syracuseStep 2294153 = 1720615) B1720615
theorem B4351097 : Blo 904575 4351097 := bstep (se 2 (by rfl) ⟨1631661, by rfl⟩ : syracuseStep 4351097 = 3263323) B3263323
theorem B5153939 : Blo 904575 5153939 := bstep (se 1 (by rfl) ⟨3865454, by rfl⟩ : syracuseStep 5153939 = 7730909) B7730909
theorem B17646835 : Blo 904575 17646835 := bstep (se 1 (by rfl) ⟨13235126, by rfl⟩ : syracuseStep 17646835 = 26470253) B26470253
theorem B2901295 : Blo 904575 2901295 := bstep (se 1 (by rfl) ⟨2175971, by rfl⟩ : syracuseStep 2901295 = 4351943) B4351943
theorem B3867983 : Blo 904575 3867983 := bstep (se 1 (by rfl) ⟨2900987, by rfl⟩ : syracuseStep 3867983 = 5801975) B5801975
theorem B2901757 : Blo 904575 2901757 := bstep (se 3 (by rfl) ⟨544079, by rfl⟩ : syracuseStep 2901757 = 1088159) B1088159
theorem B5154623 : Blo 904575 5154623 := bstep (se 1 (by rfl) ⟨3865967, by rfl⟩ : syracuseStep 5154623 = 7731935) B7731935
theorem B3057479 : Blo 904575 3057479 := bstep (se 1 (by rfl) ⟨2293109, by rfl⟩ : syracuseStep 3057479 = 4586219) B4586219
theorem B11020535 : Blo 904575 11020535 := bstep (se 1 (by rfl) ⟨8265401, by rfl⟩ : syracuseStep 11020535 = 16530803) B16530803
theorem B1018111 : Blo 904575 1018111 := bstep (se 1 (by rfl) ⟨763583, by rfl⟩ : syracuseStep 1018111 = 1527167) B1527167
theorem B8702315 : Blo 904575 8702315 := bstep (se 1 (by rfl) ⟨6526736, by rfl⟩ : syracuseStep 8702315 = 13053473) B13053473
theorem B4582169 : Blo 904575 4582169 := bstep (se 2 (by rfl) ⟨1718313, by rfl⟩ : syracuseStep 4582169 = 3436627) B3436627
theorem B17640287 : Blo 904575 17640287 := bstep (se 1 (by rfl) ⟨13230215, by rfl⟩ : syracuseStep 17640287 = 26460431) B26460431
theorem B1526951 : Blo 904575 1526951 := bstep (se 1 (by rfl) ⟨1145213, by rfl⟩ : syracuseStep 1526951 = 2290427) B2290427
theorem B3058991 : Blo 904575 3058991 := bstep (se 1 (by rfl) ⟨2294243, by rfl⟩ : syracuseStep 3058991 = 4588487) B4588487
theorem B904655 : Blo 904575 904655 := bstep (se 1 (by rfl) ⟨678491, by rfl⟩ : syracuseStep 904655 = 1356983) B1356983
theorem B904815 : Blo 904575 904815 := bstep (se 1 (by rfl) ⟨678611, by rfl⟩ : syracuseStep 904815 = 1357223) B1357223
theorem B3100289 : Blo 904575 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B1019551 : Blo 904575 1019551 := bstep (se 1 (by rfl) ⟨764663, by rfl⟩ : syracuseStep 1019551 = 1529327) B1529327
theorem B904935 : Blo 904575 904935 := bstep (se 1 (by rfl) ⟨678701, by rfl⟩ : syracuseStep 904935 = 1357403) B1357403
theorem B1019839 : Blo 904575 1019839 := bstep (se 1 (by rfl) ⟨764879, by rfl⟩ : syracuseStep 1019839 = 1529759) B1529759
theorem B905243 : Blo 904575 905243 := bstep (se 1 (by rfl) ⟨678932, by rfl⟩ : syracuseStep 905243 = 1357865) B1357865
theorem B2387999 : Blo 904575 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B905263 : Blo 904575 905263 := bstep (se 1 (by rfl) ⟨678947, by rfl⟩ : syracuseStep 905263 = 1357895) B1357895
theorem B2904295 : Blo 904575 2904295 := bstep (se 1 (by rfl) ⟨2178221, by rfl⟩ : syracuseStep 2904295 = 4356443) B4356443
theorem B2035961 : Blo 904575 2035961 := bstep (se 2 (by rfl) ⟨763485, by rfl⟩ : syracuseStep 2035961 = 1526971) B1526971
theorem B1765290257 : Blo 904575 1765290257 := bstep (se 2 (by rfl) ⟨661983846, by rfl⟩ : syracuseStep 1765290257 = 1323967693) B1323967693
theorem B905519 : Blo 904575 905519 := bstep (se 1 (by rfl) ⟨679139, by rfl⟩ : syracuseStep 905519 = 1358279) B1358279
theorem B905663 : Blo 904575 905663 := bstep (se 1 (by rfl) ⟨679247, by rfl⟩ : syracuseStep 905663 = 1358495) B1358495
theorem B2036231 : Blo 904575 2036231 := bstep (se 1 (by rfl) ⟨1527173, by rfl⟩ : syracuseStep 2036231 = 3054347) B3054347
theorem B905759 : Blo 904575 905759 := bstep (se 1 (by rfl) ⟨679319, by rfl⟩ : syracuseStep 905759 = 1358639) B1358639
theorem B905839 : Blo 904575 905839 := bstep (se 1 (by rfl) ⟨679379, by rfl⟩ : syracuseStep 905839 = 1358759) B1358759
theorem B2175655 : Blo 904575 2175655 := bstep (se 1 (by rfl) ⟨1631741, by rfl⟩ : syracuseStep 2175655 = 3263483) B3263483
theorem B2036411 : Blo 904575 2036411 := bstep (se 1 (by rfl) ⟨1527308, by rfl⟩ : syracuseStep 2036411 = 3054617) B3054617
theorem B905959 : Blo 904575 905959 := bstep (se 1 (by rfl) ⟨679469, by rfl⟩ : syracuseStep 905959 = 1358939) B1358939
theorem B4707227 : Blo 904575 4707227 := bstep (se 1 (by rfl) ⟨3530420, by rfl⟩ : syracuseStep 4707227 = 7060841) B7060841
theorem B906207 : Blo 904575 906207 := bstep (se 1 (by rfl) ⟨679655, by rfl⟩ : syracuseStep 906207 = 1359311) B1359311
theorem B16741529 : Blo 904575 16741529 := bstep (se 2 (by rfl) ⟨6278073, by rfl⟩ : syracuseStep 16741529 = 12556147) B12556147
theorem B906463 : Blo 904575 906463 := bstep (se 1 (by rfl) ⟨679847, by rfl⟩ : syracuseStep 906463 = 1359695) B1359695
theorem B1357055 : Blo 904575 1357055 := bstep (se 1 (by rfl) ⟨1017791, by rfl⟩ : syracuseStep 1357055 = 2035583) B2035583
theorem B1357097 : Blo 904575 1357097 := bstep (se 2 (by rfl) ⟨508911, by rfl⟩ : syracuseStep 1357097 = 1017823) B1017823
theorem B906543 : Blo 904575 906543 := bstep (se 1 (by rfl) ⟨679907, by rfl⟩ : syracuseStep 906543 = 1359815) B1359815
theorem B1717615 : Blo 904575 1717615 := bstep (se 1 (by rfl) ⟨1288211, by rfl⟩ : syracuseStep 1717615 = 2576423) B2576423
theorem B2037203 : Blo 904575 2037203 := bstep (se 1 (by rfl) ⟨1527902, by rfl⟩ : syracuseStep 2037203 = 3055805) B3055805
theorem B4896283 : Blo 904575 4896283 := bstep (se 1 (by rfl) ⟨3672212, by rfl⟩ : syracuseStep 4896283 = 7344425) B7344425
theorem B2037311 : Blo 904575 2037311 := bstep (se 1 (by rfl) ⟨1527983, by rfl⟩ : syracuseStep 2037311 = 3055967) B3055967
theorem B2578063 : Blo 904575 2578063 := bstep (se 1 (by rfl) ⟨1933547, by rfl⟩ : syracuseStep 2578063 = 3867095) B3867095
theorem B2037473 : Blo 904575 2037473 := bstep (se 2 (by rfl) ⟨764052, by rfl⟩ : syracuseStep 2037473 = 1528105) B1528105
theorem B29349661 : Blo 904575 29349661 := bstep (se 3 (by rfl) ⟨5503061, by rfl⟩ : syracuseStep 29349661 = 11006123) B11006123
theorem B4585247 : Blo 904575 4585247 := bstep (se 1 (by rfl) ⟨3438935, by rfl⟩ : syracuseStep 4585247 = 6877871) B6877871
theorem B1357691 : Blo 904575 1357691 := bstep (se 1 (by rfl) ⟨1018268, by rfl⟩ : syracuseStep 1357691 = 2036537) B2036537
theorem B1357727 : Blo 904575 1357727 := bstep (se 1 (by rfl) ⟨1018295, by rfl⟩ : syracuseStep 1357727 = 2036591) B2036591
theorem B4183979 : Blo 904575 4183979 := bstep (se 1 (by rfl) ⟨3137984, by rfl⟩ : syracuseStep 4183979 = 6275969) B6275969
theorem B16529345 : Blo 904575 16529345 := bstep (se 2 (by rfl) ⟨6198504, by rfl⟩ : syracuseStep 16529345 = 12397009) B12397009
theorem B2291753 : Blo 904575 2291753 := bstep (se 2 (by rfl) ⟨859407, by rfl⟩ : syracuseStep 2291753 = 1718815) B1718815
theorem B2037833 : Blo 904575 2037833 := bstep (se 2 (by rfl) ⟨764187, by rfl⟩ : syracuseStep 2037833 = 1528375) B1528375
theorem B1357931 : Blo 904575 1357931 := bstep (se 1 (by rfl) ⟨1018448, by rfl⟩ : syracuseStep 1357931 = 2036897) B2036897
theorem B1357961 : Blo 904575 1357961 := bstep (se 2 (by rfl) ⟨509235, by rfl⟩ : syracuseStep 1357961 = 1018471) B1018471
theorem B8706311 : Blo 904575 8706311 := bstep (se 1 (by rfl) ⟨6529733, by rfl⟩ : syracuseStep 8706311 = 13059467) B13059467
theorem B1358111 : Blo 904575 1358111 := bstep (se 1 (by rfl) ⟨1018583, by rfl⟩ : syracuseStep 1358111 = 2037167) B2037167
theorem B3053915 : Blo 904575 3053915 := bstep (se 1 (by rfl) ⟨2290436, by rfl⟩ : syracuseStep 3053915 = 4580873) B4580873
theorem B2898271 : Blo 904575 2898271 := bstep (se 1 (by rfl) ⟨2173703, by rfl⟩ : syracuseStep 2898271 = 4347407) B4347407
theorem B3668321 : Blo 904575 3668321 := bstep (se 2 (by rfl) ⟨1375620, by rfl⟩ : syracuseStep 3668321 = 2751241) B2751241
theorem B6879815 : Blo 904575 6879815 := bstep (se 1 (by rfl) ⟨5159861, by rfl⟩ : syracuseStep 6879815 = 10319723) B10319723
theorem B12384913 : Blo 904575 12384913 := bstep (se 2 (by rfl) ⟨4644342, by rfl⟩ : syracuseStep 12384913 = 9288685) B9288685
theorem B4651667 : Blo 904575 4651667 := bstep (se 1 (by rfl) ⟨3488750, by rfl⟩ : syracuseStep 4651667 = 6977501) B6977501
theorem B33471251 : Blo 904575 33471251 := bstep (se 1 (by rfl) ⟨25103438, by rfl⟩ : syracuseStep 33471251 = 50206877) B50206877
theorem B62798611 : Blo 904575 62798611 := bstep (se 1 (by rfl) ⟨47098958, by rfl⟩ : syracuseStep 62798611 = 94197917) B94197917
theorem B1358783 : Blo 904575 1358783 := bstep (se 1 (by rfl) ⟨1019087, by rfl⟩ : syracuseStep 1358783 = 2038175) B2038175
theorem B2292695 : Blo 904575 2292695 := bstep (se 1 (by rfl) ⟨1719521, by rfl⟩ : syracuseStep 2292695 = 3439043) B3439043
theorem B1358831 : Blo 904575 1358831 := bstep (se 1 (by rfl) ⟨1019123, by rfl⟩ : syracuseStep 1358831 = 2038247) B2038247
theorem B1359017 : Blo 904575 1359017 := bstep (se 2 (by rfl) ⟨509631, by rfl⟩ : syracuseStep 1359017 = 1019263) B1019263
theorem B2579681 : Blo 904575 2579681 := bstep (se 2 (by rfl) ⟨967380, by rfl⟩ : syracuseStep 2579681 = 1934761) B1934761
theorem B3439847 : Blo 904575 3439847 := bstep (se 1 (by rfl) ⟨2579885, by rfl⟩ : syracuseStep 3439847 = 5159771) B5159771
theorem B5152025 : Blo 904575 5152025 := bstep (se 2 (by rfl) ⟨1932009, by rfl⟩ : syracuseStep 5152025 = 3864019) B3864019
theorem B5152207 : Blo 904575 5152207 := bstep (se 1 (by rfl) ⟨3864155, by rfl⟩ : syracuseStep 5152207 = 7728311) B7728311
theorem B2039291 : Blo 904575 2039291 := bstep (se 1 (by rfl) ⟨1529468, by rfl⟩ : syracuseStep 2039291 = 3058937) B3058937
theorem B1359407 : Blo 904575 1359407 := bstep (se 1 (by rfl) ⟨1019555, by rfl⟩ : syracuseStep 1359407 = 2039111) B2039111
theorem B1359431 : Blo 904575 1359431 := bstep (se 1 (by rfl) ⟨1019573, by rfl⟩ : syracuseStep 1359431 = 2039147) B2039147
theorem B2039399 : Blo 904575 2039399 := bstep (se 1 (by rfl) ⟨1529549, by rfl⟩ : syracuseStep 2039399 = 3059099) B3059099
theorem B1359515 : Blo 904575 1359515 := bstep (se 1 (by rfl) ⟨1019636, by rfl⟩ : syracuseStep 1359515 = 2039273) B2039273
theorem B2039471 : Blo 904575 2039471 := bstep (se 1 (by rfl) ⟨1529603, by rfl⟩ : syracuseStep 2039471 = 3059207) B3059207
theorem B4587191 : Blo 904575 4587191 := bstep (se 1 (by rfl) ⟨3440393, by rfl⟩ : syracuseStep 4587191 = 6880787) B6880787
theorem B1359611 : Blo 904575 1359611 := bstep (se 1 (by rfl) ⟨1019708, by rfl⟩ : syracuseStep 1359611 = 2039417) B2039417
theorem B2039561 : Blo 904575 2039561 := bstep (se 2 (by rfl) ⟨764835, by rfl⟩ : syracuseStep 2039561 = 1529671) B1529671
theorem B2293535 : Blo 904575 2293535 := bstep (se 1 (by rfl) ⟨1720151, by rfl⟩ : syracuseStep 2293535 = 3440303) B3440303
theorem B3866753 : Blo 904575 3866753 := bstep (se 2 (by rfl) ⟨1450032, by rfl⟩ : syracuseStep 3866753 = 2900065) B2900065
theorem B3138151 : Blo 904575 3138151 := bstep (se 1 (by rfl) ⟨2353613, by rfl⟩ : syracuseStep 3138151 = 4707227) B4707227
theorem B2900873 : Blo 904575 2900873 := bstep (se 2 (by rfl) ⟨1087827, by rfl⟩ : syracuseStep 2900873 = 2175655) B2175655
theorem B83731481 : Blo 904575 83731481 := bstep (se 2 (by rfl) ⟨31399305, by rfl⟩ : syracuseStep 83731481 = 62798611) B62798611
theorem B3056831 : Blo 904575 3056831 := bstep (se 1 (by rfl) ⟨2292623, by rfl⟩ : syracuseStep 3056831 = 4585247) B4585247
theorem B11019563 : Blo 904575 11019563 := bstep (se 1 (by rfl) ⟨8264672, by rfl⟩ : syracuseStep 11019563 = 16529345) B16529345
theorem B5801543 : Blo 904575 5801543 := bstep (se 1 (by rfl) ⟨4351157, by rfl⟩ : syracuseStep 5801543 = 8702315) B8702315
theorem B23529113 : Blo 904575 23529113 := bstep (se 2 (by rfl) ⟨8823417, by rfl⟩ : syracuseStep 23529113 = 17646835) B17646835
theorem B8267437 : Blo 904575 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B3868393 : Blo 904575 3868393 := bstep (se 2 (by rfl) ⟨1450647, by rfl⟩ : syracuseStep 3868393 = 2901295) B2901295
theorem B1017967 : Blo 904575 1017967 := bstep (se 1 (by rfl) ⟨763475, by rfl⟩ : syracuseStep 1017967 = 1526951) B1526951
theorem B3434683 : Blo 904575 3434683 := bstep (se 1 (by rfl) ⟨2576012, by rfl⟩ : syracuseStep 3434683 = 5152025) B5152025
theorem B3869009 : Blo 904575 3869009 := bstep (se 2 (by rfl) ⟨1450878, by rfl⟩ : syracuseStep 3869009 = 2901757) B2901757
theorem B3058127 : Blo 904575 3058127 := bstep (se 1 (by rfl) ⟨2293595, by rfl⟩ : syracuseStep 3058127 = 4587191) B4587191
theorem B6367997 : Blo 904575 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B11602925 : Blo 904575 11602925 := bstep (se 3 (by rfl) ⟨2175548, by rfl⟩ : syracuseStep 11602925 = 4351097) B4351097
theorem B3435959 : Blo 904575 3435959 := bstep (se 1 (by rfl) ⟨2576969, by rfl⟩ : syracuseStep 3435959 = 5153939) B5153939
theorem B11161019 : Blo 904575 11161019 := bstep (se 1 (by rfl) ⟨8370764, by rfl⟩ : syracuseStep 11161019 = 16741529) B16741529
theorem B904703 : Blo 904575 904703 := bstep (se 1 (by rfl) ⟨678527, by rfl⟩ : syracuseStep 904703 = 1357055) B1357055
theorem B904731 : Blo 904575 904731 := bstep (se 1 (by rfl) ⟨678548, by rfl⟩ : syracuseStep 904731 = 1357097) B1357097
theorem B3436415 : Blo 904575 3436415 := bstep (se 1 (by rfl) ⟨2577311, by rfl⟩ : syracuseStep 3436415 = 5154623) B5154623
theorem B905127 : Blo 904575 905127 := bstep (se 1 (by rfl) ⟨678845, by rfl⟩ : syracuseStep 905127 = 1357691) B1357691
theorem B905151 : Blo 904575 905151 := bstep (se 1 (by rfl) ⟨678863, by rfl⟩ : syracuseStep 905151 = 1357727) B1357727
theorem B1527835 : Blo 904575 1527835 := bstep (se 1 (by rfl) ⟨1145876, by rfl⟩ : syracuseStep 1527835 = 2291753) B2291753
theorem B905287 : Blo 904575 905287 := bstep (se 1 (by rfl) ⟨678965, by rfl⟩ : syracuseStep 905287 = 1357931) B1357931
theorem B905307 : Blo 904575 905307 := bstep (se 1 (by rfl) ⟨678980, by rfl⟩ : syracuseStep 905307 = 1357961) B1357961
theorem B5804207 : Blo 904575 5804207 := bstep (se 1 (by rfl) ⟨4353155, by rfl⟩ : syracuseStep 5804207 = 8706311) B8706311
theorem B905407 : Blo 904575 905407 := bstep (se 1 (by rfl) ⟨679055, by rfl⟩ : syracuseStep 905407 = 1358111) B1358111
theorem B2035943 : Blo 904575 2035943 := bstep (se 1 (by rfl) ⟨1526957, by rfl⟩ : syracuseStep 2035943 = 3053915) B3053915
theorem B2445547 : Blo 904575 2445547 := bstep (se 1 (by rfl) ⟨1834160, by rfl⟩ : syracuseStep 2445547 = 3668321) B3668321
theorem B3101111 : Blo 904575 3101111 := bstep (se 1 (by rfl) ⟨2325833, by rfl⟩ : syracuseStep 3101111 = 4651667) B4651667
theorem B2290153 : Blo 904575 2290153 := bstep (se 2 (by rfl) ⟨858807, by rfl⟩ : syracuseStep 2290153 = 1717615) B1717615
theorem B11760191 : Blo 904575 11760191 := bstep (se 1 (by rfl) ⟨8820143, by rfl⟩ : syracuseStep 11760191 = 17640287) B17640287
theorem B6869609 : Blo 904575 6869609 := bstep (se 2 (by rfl) ⟨2576103, by rfl⟩ : syracuseStep 6869609 = 5152207) B5152207
theorem B905855 : Blo 904575 905855 := bstep (se 1 (by rfl) ⟨679391, by rfl⟩ : syracuseStep 905855 = 1358783) B1358783
theorem B1528463 : Blo 904575 1528463 := bstep (se 1 (by rfl) ⟨1146347, by rfl⟩ : syracuseStep 1528463 = 2292695) B2292695
theorem B905887 : Blo 904575 905887 := bstep (se 1 (by rfl) ⟨679415, by rfl⟩ : syracuseStep 905887 = 1358831) B1358831
theorem B906011 : Blo 904575 906011 := bstep (se 1 (by rfl) ⟨679508, by rfl⟩ : syracuseStep 906011 = 1359017) B1359017
theorem B3437417 : Blo 904575 3437417 := bstep (se 2 (by rfl) ⟨1289031, by rfl⟩ : syracuseStep 3437417 = 2578063) B2578063
theorem B906271 : Blo 904575 906271 := bstep (se 1 (by rfl) ⟨679703, by rfl⟩ : syracuseStep 906271 = 1359407) B1359407
theorem B906287 : Blo 904575 906287 := bstep (se 1 (by rfl) ⟨679715, by rfl⟩ : syracuseStep 906287 = 1359431) B1359431
theorem B906343 : Blo 904575 906343 := bstep (se 1 (by rfl) ⟨679757, by rfl⟩ : syracuseStep 906343 = 1359515) B1359515
theorem B906407 : Blo 904575 906407 := bstep (se 1 (by rfl) ⟨679805, by rfl⟩ : syracuseStep 906407 = 1359611) B1359611
theorem B1529023 : Blo 904575 1529023 := bstep (se 1 (by rfl) ⟨1146767, by rfl⟩ : syracuseStep 1529023 = 2293535) B2293535
theorem B22042043 : Blo 904575 22042043 := bstep (se 1 (by rfl) ⟨16531532, by rfl⟩ : syracuseStep 22042043 = 33063065) B33063065
theorem B2037239 : Blo 904575 2037239 := bstep (se 1 (by rfl) ⟨1527929, by rfl⟩ : syracuseStep 2037239 = 3055859) B3055859
theorem B1357307 : Blo 904575 1357307 := bstep (se 1 (by rfl) ⟨1017980, by rfl⟩ : syracuseStep 1357307 = 2035961) B2035961
theorem B1176860171 : Blo 904575 1176860171 := bstep (se 1 (by rfl) ⟨882645128, by rfl⟩ : syracuseStep 1176860171 = 1765290257) B1765290257
theorem B1529435 : Blo 904575 1529435 := bstep (se 1 (by rfl) ⟨1147076, by rfl⟩ : syracuseStep 1529435 = 2294153) B2294153
theorem B3872393 : Blo 904575 3872393 := bstep (se 2 (by rfl) ⟨1452147, by rfl⟩ : syracuseStep 3872393 = 2904295) B2904295
theorem B1357481 : Blo 904575 1357481 := bstep (se 2 (by rfl) ⟨509055, by rfl⟩ : syracuseStep 1357481 = 1018111) B1018111
theorem B1357487 : Blo 904575 1357487 := bstep (se 1 (by rfl) ⟨1018115, by rfl⟩ : syracuseStep 1357487 = 2036231) B2036231
theorem B1357607 : Blo 904575 1357607 := bstep (se 1 (by rfl) ⟨1018205, by rfl⟩ : syracuseStep 1357607 = 2036411) B2036411
theorem B3864361 : Blo 904575 3864361 := bstep (se 2 (by rfl) ⟨1449135, by rfl⟩ : syracuseStep 3864361 = 2898271) B2898271
theorem B16513217 : Blo 904575 16513217 := bstep (se 2 (by rfl) ⟨6192456, by rfl⟩ : syracuseStep 16513217 = 12384913) B12384913
theorem B2578655 : Blo 904575 2578655 := bstep (se 1 (by rfl) ⟨1933991, by rfl⟩ : syracuseStep 2578655 = 3867983) B3867983
theorem B1358135 : Blo 904575 1358135 := bstep (se 1 (by rfl) ⟨1018601, by rfl⟩ : syracuseStep 1358135 = 2037203) B2037203
theorem B1358207 : Blo 904575 1358207 := bstep (se 1 (by rfl) ⟨1018655, by rfl⟩ : syracuseStep 1358207 = 2037311) B2037311
theorem B1358315 : Blo 904575 1358315 := bstep (se 1 (by rfl) ⟨1018736, by rfl⟩ : syracuseStep 1358315 = 2037473) B2037473
theorem B2038319 : Blo 904575 2038319 := bstep (se 1 (by rfl) ⟨1528739, by rfl⟩ : syracuseStep 2038319 = 3057479) B3057479
theorem B1358555 : Blo 904575 1358555 := bstep (se 1 (by rfl) ⟨1018916, by rfl⟩ : syracuseStep 1358555 = 2037833) B2037833
theorem B7347023 : Blo 904575 7347023 := bstep (se 1 (by rfl) ⟨5510267, by rfl⟩ : syracuseStep 7347023 = 11020535) B11020535
theorem B4586543 : Blo 904575 4586543 := bstep (se 1 (by rfl) ⟨3439907, by rfl⟩ : syracuseStep 4586543 = 6879815) B6879815
theorem B44629109 : Blo 904575 44629109 := bstep (se 5 (by rfl) ⟨2091989, by rfl⟩ : syracuseStep 44629109 = 4183979) B4183979
theorem B22314167 : Blo 904575 22314167 := bstep (se 1 (by rfl) ⟨16735625, by rfl⟩ : syracuseStep 22314167 = 33471251) B33471251
theorem B3054779 : Blo 904575 3054779 := bstep (se 1 (by rfl) ⟨2291084, by rfl⟩ : syracuseStep 3054779 = 4582169) B4582169
theorem B6528377 : Blo 904575 6528377 := bstep (se 2 (by rfl) ⟨2448141, by rfl⟩ : syracuseStep 6528377 = 4896283) B4896283
theorem B1719787 : Blo 904575 1719787 := bstep (se 1 (by rfl) ⟨1289840, by rfl⟩ : syracuseStep 1719787 = 2579681) B2579681
theorem B2293231 : Blo 904575 2293231 := bstep (se 1 (by rfl) ⟨1719923, by rfl⟩ : syracuseStep 2293231 = 3439847) B3439847
theorem B2039327 : Blo 904575 2039327 := bstep (se 1 (by rfl) ⟨1529495, by rfl⟩ : syracuseStep 2039327 = 3058991) B3058991
theorem B1359401 : Blo 904575 1359401 := bstep (se 2 (by rfl) ⟨509775, by rfl⟩ : syracuseStep 1359401 = 1019551) B1019551
theorem B1359527 : Blo 904575 1359527 := bstep (se 1 (by rfl) ⟨1019645, by rfl⟩ : syracuseStep 1359527 = 2039291) B2039291
theorem B39132881 : Blo 904575 39132881 := bstep (se 2 (by rfl) ⟨14674830, by rfl⟩ : syracuseStep 39132881 = 29349661) B29349661
theorem B1359599 : Blo 904575 1359599 := bstep (se 1 (by rfl) ⟨1019699, by rfl⟩ : syracuseStep 1359599 = 2039399) B2039399
theorem B1359647 : Blo 904575 1359647 := bstep (se 1 (by rfl) ⟨1019735, by rfl⟩ : syracuseStep 1359647 = 2039471) B2039471
theorem B1359707 : Blo 904575 1359707 := bstep (se 1 (by rfl) ⟨1019780, by rfl⟩ : syracuseStep 1359707 = 2039561) B2039561
theorem B1359785 : Blo 904575 1359785 := bstep (se 2 (by rfl) ⟨509919, by rfl⟩ : syracuseStep 1359785 = 1019839) B1019839
theorem B4579577 : Blo 904575 4579577 := bstep (se 2 (by rfl) ⟨1717341, by rfl⟩ : syracuseStep 4579577 = 3434683) B3434683
theorem B3260729 : Blo 904575 3260729 := bstep (se 2 (by rfl) ⟨1222773, by rfl⟩ : syracuseStep 3260729 = 2445547) B2445547
theorem B7840127 : Blo 904575 7840127 := bstep (se 1 (by rfl) ⟨5880095, by rfl⟩ : syracuseStep 7840127 = 11760191) B11760191
theorem B4579739 : Blo 904575 4579739 := bstep (se 1 (by rfl) ⟨3434804, by rfl⟩ : syracuseStep 4579739 = 6869609) B6869609
theorem B55820987 : Blo 904575 55820987 := bstep (se 1 (by rfl) ⟨41865740, by rfl⟩ : syracuseStep 55820987 = 83731481) B83731481
theorem B784573447 : Blo 904575 784573447 := bstep (se 1 (by rfl) ⟨588430085, by rfl⟩ : syracuseStep 784573447 = 1176860171) B1176860171
theorem B3867695 : Blo 904575 3867695 := bstep (se 1 (by rfl) ⟨2900771, by rfl⟩ : syracuseStep 3867695 = 5801543) B5801543
theorem B2581595 : Blo 904575 2581595 := bstep (se 1 (by rfl) ⟨1936196, by rfl⟩ : syracuseStep 2581595 = 3872393) B3872393
theorem B3057641 : Blo 904575 3057641 := bstep (se 2 (by rfl) ⟨1146615, by rfl⟩ : syracuseStep 3057641 = 2293231) B2293231
theorem B7735283 : Blo 904575 7735283 := bstep (se 1 (by rfl) ⟨5801462, by rfl⟩ : syracuseStep 7735283 = 11602925) B11602925
theorem B3057695 : Blo 904575 3057695 := bstep (se 1 (by rfl) ⟨2293271, by rfl⟩ : syracuseStep 3057695 = 4586543) B4586543
theorem B4352251 : Blo 904575 4352251 := bstep (se 1 (by rfl) ⟨3264188, by rfl⟩ : syracuseStep 4352251 = 6528377) B6528377
theorem B7440679 : Blo 904575 7440679 := bstep (se 1 (by rfl) ⟨5580509, by rfl⟩ : syracuseStep 7440679 = 11161019) B11161019
theorem B7735661 : Blo 904575 7735661 := bstep (se 3 (by rfl) ⟨1450436, by rfl⟩ : syracuseStep 7735661 = 2900873) B2900873
theorem B3869471 : Blo 904575 3869471 := bstep (se 1 (by rfl) ⟨2902103, by rfl⟩ : syracuseStep 3869471 = 5804207) B5804207
theorem B2067407 : Blo 904575 2067407 := bstep (se 1 (by rfl) ⟨1550555, by rfl⟩ : syracuseStep 2067407 = 3101111) B3101111
theorem B1018975 : Blo 904575 1018975 := bstep (se 1 (by rfl) ⟨764231, by rfl⟩ : syracuseStep 1018975 = 1528463) B1528463
theorem B6876413 : Blo 904575 6876413 := bstep (se 3 (by rfl) ⟨1289327, by rfl⟩ : syracuseStep 6876413 = 2578655) B2578655
theorem B44092997 : Blo 904575 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B904871 : Blo 904575 904871 := bstep (se 1 (by rfl) ⟨678653, by rfl⟩ : syracuseStep 904871 = 1357307) B1357307
theorem B1019623 : Blo 904575 1019623 := bstep (se 1 (by rfl) ⟨764717, by rfl⟩ : syracuseStep 1019623 = 1529435) B1529435
theorem B904987 : Blo 904575 904987 := bstep (se 1 (by rfl) ⟨678740, by rfl⟩ : syracuseStep 904987 = 1357481) B1357481
theorem B904991 : Blo 904575 904991 := bstep (se 1 (by rfl) ⟨678743, by rfl⟩ : syracuseStep 904991 = 1357487) B1357487
theorem B905071 : Blo 904575 905071 := bstep (se 1 (by rfl) ⟨678803, by rfl⟩ : syracuseStep 905071 = 1357607) B1357607
theorem B905423 : Blo 904575 905423 := bstep (se 1 (by rfl) ⟨679067, by rfl⟩ : syracuseStep 905423 = 1358135) B1358135
theorem B905471 : Blo 904575 905471 := bstep (se 1 (by rfl) ⟨679103, by rfl⟩ : syracuseStep 905471 = 1358207) B1358207
theorem B905543 : Blo 904575 905543 := bstep (se 1 (by rfl) ⟨679157, by rfl⟩ : syracuseStep 905543 = 1358315) B1358315
theorem B905703 : Blo 904575 905703 := bstep (se 1 (by rfl) ⟨679277, by rfl⟩ : syracuseStep 905703 = 1358555) B1358555
theorem B2036519 : Blo 904575 2036519 := bstep (se 1 (by rfl) ⟨1527389, by rfl⟩ : syracuseStep 2036519 = 3054779) B3054779
theorem B2290639 : Blo 904575 2290639 := bstep (se 1 (by rfl) ⟨1717979, by rfl⟩ : syracuseStep 2290639 = 3435959) B3435959
theorem B5157857 : Blo 904575 5157857 := bstep (se 2 (by rfl) ⟨1934196, by rfl⟩ : syracuseStep 5157857 = 3868393) B3868393
theorem B906267 : Blo 904575 906267 := bstep (se 1 (by rfl) ⟨679700, by rfl⟩ : syracuseStep 906267 = 1359401) B1359401
theorem B906351 : Blo 904575 906351 := bstep (se 1 (by rfl) ⟨679763, by rfl⟩ : syracuseStep 906351 = 1359527) B1359527
theorem B26088587 : Blo 904575 26088587 := bstep (se 1 (by rfl) ⟨19566440, by rfl⟩ : syracuseStep 26088587 = 39132881) B39132881
theorem B906399 : Blo 904575 906399 := bstep (se 1 (by rfl) ⟨679799, by rfl⟩ : syracuseStep 906399 = 1359599) B1359599
theorem B906431 : Blo 904575 906431 := bstep (se 1 (by rfl) ⟨679823, by rfl⟩ : syracuseStep 906431 = 1359647) B1359647
theorem B906471 : Blo 904575 906471 := bstep (se 1 (by rfl) ⟨679853, by rfl⟩ : syracuseStep 906471 = 1359707) B1359707
theorem B2290943 : Blo 904575 2290943 := bstep (se 1 (by rfl) ⟨1718207, by rfl⟩ : syracuseStep 2290943 = 3436415) B3436415
theorem B906523 : Blo 904575 906523 := bstep (se 1 (by rfl) ⟨679892, by rfl⟩ : syracuseStep 906523 = 1359785) B1359785
theorem B2037113 : Blo 904575 2037113 := bstep (se 2 (by rfl) ⟨763917, by rfl⟩ : syracuseStep 2037113 = 1527835) B1527835
theorem B2577835 : Blo 904575 2577835 := bstep (se 1 (by rfl) ⟨1933376, by rfl⟩ : syracuseStep 2577835 = 3866753) B3866753
theorem B1357289 : Blo 904575 1357289 := bstep (se 2 (by rfl) ⟨508983, by rfl⟩ : syracuseStep 1357289 = 1017967) B1017967
theorem B1357295 : Blo 904575 1357295 := bstep (se 1 (by rfl) ⟨1017971, by rfl⟩ : syracuseStep 1357295 = 2035943) B2035943
theorem B2291611 : Blo 904575 2291611 := bstep (se 1 (by rfl) ⟨1718708, by rfl⟩ : syracuseStep 2291611 = 3437417) B3437417
theorem B3053537 : Blo 904575 3053537 := bstep (se 2 (by rfl) ⟨1145076, by rfl⟩ : syracuseStep 3053537 = 2290153) B2290153
theorem B2037887 : Blo 904575 2037887 := bstep (se 1 (by rfl) ⟨1528415, by rfl⟩ : syracuseStep 2037887 = 3056831) B3056831
theorem B4184201 : Blo 904575 4184201 := bstep (se 2 (by rfl) ⟨1569075, by rfl⟩ : syracuseStep 4184201 = 3138151) B3138151
theorem B7346375 : Blo 904575 7346375 := bstep (se 1 (by rfl) ⟨5509781, by rfl⟩ : syracuseStep 7346375 = 11019563) B11019563
theorem B14694695 : Blo 904575 14694695 := bstep (se 1 (by rfl) ⟨11021021, by rfl⟩ : syracuseStep 14694695 = 22042043) B22042043
theorem B1358159 : Blo 904575 1358159 := bstep (se 1 (by rfl) ⟨1018619, by rfl⟩ : syracuseStep 1358159 = 2037239) B2037239
theorem B15686075 : Blo 904575 15686075 := bstep (se 1 (by rfl) ⟨11764556, by rfl⟩ : syracuseStep 15686075 = 23529113) B23529113
theorem B11008811 : Blo 904575 11008811 := bstep (se 1 (by rfl) ⟨8256608, by rfl⟩ : syracuseStep 11008811 = 16513217) B16513217
theorem B2579339 : Blo 904575 2579339 := bstep (se 1 (by rfl) ⟨1934504, by rfl⟩ : syracuseStep 2579339 = 3869009) B3869009
theorem B2038697 : Blo 904575 2038697 := bstep (se 2 (by rfl) ⟨764511, by rfl⟩ : syracuseStep 2038697 = 1529023) B1529023
theorem B2038751 : Blo 904575 2038751 := bstep (se 1 (by rfl) ⟨1529063, by rfl⟩ : syracuseStep 2038751 = 3058127) B3058127
theorem B1358879 : Blo 904575 1358879 := bstep (se 1 (by rfl) ⟨1019159, by rfl⟩ : syracuseStep 1358879 = 2038319) B2038319
theorem B4898015 : Blo 904575 4898015 := bstep (se 1 (by rfl) ⟨3673511, by rfl⟩ : syracuseStep 4898015 = 7347023) B7347023
theorem B2293049 : Blo 904575 2293049 := bstep (se 2 (by rfl) ⟨859893, by rfl⟩ : syracuseStep 2293049 = 1719787) B1719787
theorem B16981325 : Blo 904575 16981325 := bstep (se 3 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 16981325 = 6367997) B6367997
theorem B29752739 : Blo 904575 29752739 := bstep (se 1 (by rfl) ⟨22314554, by rfl⟩ : syracuseStep 29752739 = 44629109) B44629109
theorem B14876111 : Blo 904575 14876111 := bstep (se 1 (by rfl) ⟨11157083, by rfl⟩ : syracuseStep 14876111 = 22314167) B22314167
theorem B1359551 : Blo 904575 1359551 := bstep (se 1 (by rfl) ⟨1019663, by rfl⟩ : syracuseStep 1359551 = 2039327) B2039327
theorem B5152481 : Blo 904575 5152481 := bstep (se 2 (by rfl) ⟨1932180, by rfl⟩ : syracuseStep 5152481 = 3864361) B3864361
theorem B5226751 : Blo 904575 5226751 := bstep (se 1 (by rfl) ⟨3920063, by rfl⟩ : syracuseStep 5226751 = 7840127) B7840127
theorem B11157869 : Blo 904575 11157869 := bstep (se 3 (by rfl) ⟨2092100, by rfl⟩ : syracuseStep 11157869 = 4184201) B4184201
theorem B1721063 : Blo 904575 1721063 := bstep (se 1 (by rfl) ⟨1290797, by rfl⟩ : syracuseStep 1721063 = 2581595) B2581595
theorem B17392391 : Blo 904575 17392391 := bstep (se 1 (by rfl) ⟨13044293, by rfl⟩ : syracuseStep 17392391 = 26088587) B26088587
theorem B41829533 : Blo 904575 41829533 := bstep (se 3 (by rfl) ⟨7843037, by rfl⟩ : syracuseStep 41829533 = 15686075) B15686075
theorem B39683621 : Blo 904575 39683621 := bstep (se 4 (by rfl) ⟨3720339, by rfl⟩ : syracuseStep 39683621 = 7440679) B7440679
theorem B19835159 : Blo 904575 19835159 := bstep (se 1 (by rfl) ⟨14876369, by rfl⟩ : syracuseStep 19835159 = 29752739) B29752739
theorem B29395331 : Blo 904575 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B3434987 : Blo 904575 3434987 := bstep (se 1 (by rfl) ⟨2576240, by rfl⟩ : syracuseStep 3434987 = 5152481) B5152481
theorem B2173819 : Blo 904575 2173819 := bstep (se 1 (by rfl) ⟨1630364, by rfl⟩ : syracuseStep 2173819 = 3260729) B3260729
theorem B5803001 : Blo 904575 5803001 := bstep (se 2 (by rfl) ⟨2176125, by rfl⟩ : syracuseStep 5803001 = 4352251) B4352251
theorem B1527295 : Blo 904575 1527295 := bstep (se 1 (by rfl) ⟨1145471, by rfl⟩ : syracuseStep 1527295 = 2290943) B2290943
theorem B904859 : Blo 904575 904859 := bstep (se 1 (by rfl) ⟨678644, by rfl⟩ : syracuseStep 904859 = 1357289) B1357289
theorem B904863 : Blo 904575 904863 := bstep (se 1 (by rfl) ⟨678647, by rfl⟩ : syracuseStep 904863 = 1357295) B1357295
theorem B2035691 : Blo 904575 2035691 := bstep (se 1 (by rfl) ⟨1526768, by rfl⟩ : syracuseStep 2035691 = 3053537) B3053537
theorem B5156855 : Blo 904575 5156855 := bstep (se 1 (by rfl) ⟨3867641, by rfl⟩ : syracuseStep 5156855 = 7735283) B7735283
theorem B1046097929 : Blo 904575 1046097929 := bstep (se 2 (by rfl) ⟨392286723, by rfl⟩ : syracuseStep 1046097929 = 784573447) B784573447
theorem B905439 : Blo 904575 905439 := bstep (se 1 (by rfl) ⟨679079, by rfl⟩ : syracuseStep 905439 = 1358159) B1358159
theorem B5157107 : Blo 904575 5157107 := bstep (se 1 (by rfl) ⟨3867830, by rfl⟩ : syracuseStep 5157107 = 7735661) B7735661
theorem B3437113 : Blo 904575 3437113 := bstep (se 2 (by rfl) ⟨1288917, by rfl⟩ : syracuseStep 3437113 = 2577835) B2577835
theorem B905919 : Blo 904575 905919 := bstep (se 1 (by rfl) ⟨679439, by rfl⟩ : syracuseStep 905919 = 1358879) B1358879
theorem B3265343 : Blo 904575 3265343 := bstep (se 1 (by rfl) ⟨2449007, by rfl⟩ : syracuseStep 3265343 = 4898015) B4898015
theorem B4584275 : Blo 904575 4584275 := bstep (se 1 (by rfl) ⟨3438206, by rfl⟩ : syracuseStep 4584275 = 6876413) B6876413
theorem B1528699 : Blo 904575 1528699 := bstep (se 1 (by rfl) ⟨1146524, by rfl⟩ : syracuseStep 1528699 = 2293049) B2293049
theorem B9917407 : Blo 904575 9917407 := bstep (se 1 (by rfl) ⟨7438055, by rfl⟩ : syracuseStep 9917407 = 14876111) B14876111
theorem B906367 : Blo 904575 906367 := bstep (se 1 (by rfl) ⟨679775, by rfl⟩ : syracuseStep 906367 = 1359551) B1359551
theorem B3053051 : Blo 904575 3053051 := bstep (se 1 (by rfl) ⟨2289788, by rfl⟩ : syracuseStep 3053051 = 4579577) B4579577
theorem B3053159 : Blo 904575 3053159 := bstep (se 1 (by rfl) ⟨2289869, by rfl⟩ : syracuseStep 3053159 = 4579739) B4579739
theorem B37213991 : Blo 904575 37213991 := bstep (se 1 (by rfl) ⟨27910493, by rfl⟩ : syracuseStep 37213991 = 55820987) B55820987
theorem B1357679 : Blo 904575 1357679 := bstep (se 1 (by rfl) ⟨1018259, by rfl⟩ : syracuseStep 1357679 = 2036519) B2036519
theorem B3438571 : Blo 904575 3438571 := bstep (se 1 (by rfl) ⟨2578928, by rfl⟩ : syracuseStep 3438571 = 5157857) B5157857
theorem B2578463 : Blo 904575 2578463 := bstep (se 1 (by rfl) ⟨1933847, by rfl⟩ : syracuseStep 2578463 = 3867695) B3867695
theorem B1358075 : Blo 904575 1358075 := bstep (se 1 (by rfl) ⟨1018556, by rfl⟩ : syracuseStep 1358075 = 2037113) B2037113
theorem B3054185 : Blo 904575 3054185 := bstep (se 2 (by rfl) ⟨1145319, by rfl⟩ : syracuseStep 3054185 = 2290639) B2290639
theorem B2038427 : Blo 904575 2038427 := bstep (se 1 (by rfl) ⟨1528820, by rfl⟩ : syracuseStep 2038427 = 3057641) B3057641
theorem B2038463 : Blo 904575 2038463 := bstep (se 1 (by rfl) ⟨1528847, by rfl⟩ : syracuseStep 2038463 = 3057695) B3057695
theorem B1358591 : Blo 904575 1358591 := bstep (se 1 (by rfl) ⟨1018943, by rfl⟩ : syracuseStep 1358591 = 2037887) B2037887
theorem B1358633 : Blo 904575 1358633 := bstep (se 2 (by rfl) ⟨509487, by rfl⟩ : syracuseStep 1358633 = 1018975) B1018975
theorem B4897583 : Blo 904575 4897583 := bstep (se 1 (by rfl) ⟨3673187, by rfl⟩ : syracuseStep 4897583 = 7346375) B7346375
theorem B9796463 : Blo 904575 9796463 := bstep (se 1 (by rfl) ⟨7347347, by rfl⟩ : syracuseStep 9796463 = 14694695) B14694695
theorem B2579647 : Blo 904575 2579647 := bstep (se 1 (by rfl) ⟨1934735, by rfl⟩ : syracuseStep 2579647 = 3869471) B3869471
theorem B7339207 : Blo 904575 7339207 := bstep (se 1 (by rfl) ⟨5504405, by rfl⟩ : syracuseStep 7339207 = 11008811) B11008811
theorem B1719559 : Blo 904575 1719559 := bstep (se 1 (by rfl) ⟨1289669, by rfl⟩ : syracuseStep 1719559 = 2579339) B2579339
theorem B1359131 : Blo 904575 1359131 := bstep (se 1 (by rfl) ⟨1019348, by rfl⟩ : syracuseStep 1359131 = 2038697) B2038697
theorem B1359167 : Blo 904575 1359167 := bstep (se 1 (by rfl) ⟨1019375, by rfl⟩ : syracuseStep 1359167 = 2038751) B2038751
theorem B22052341 : Blo 904575 22052341 := bstep (se 5 (by rfl) ⟨1033703, by rfl⟩ : syracuseStep 22052341 = 2067407) B2067407
theorem B11320883 : Blo 904575 11320883 := bstep (se 1 (by rfl) ⟨8490662, by rfl⟩ : syracuseStep 11320883 = 16981325) B16981325
theorem B1359497 : Blo 904575 1359497 := bstep (se 2 (by rfl) ⟨509811, by rfl⟩ : syracuseStep 1359497 = 1019623) B1019623
theorem B3055481 : Blo 904575 3055481 := bstep (se 2 (by rfl) ⟨1145805, by rfl⟩ : syracuseStep 3055481 = 2291611) B2291611
theorem B1147375 : Blo 904575 1147375 := bstep (se 1 (by rfl) ⟨860531, by rfl⟩ : syracuseStep 1147375 = 1721063) B1721063
theorem B3056183 : Blo 904575 3056183 := bstep (se 1 (by rfl) ⟨2292137, by rfl⟩ : syracuseStep 3056183 = 4584275) B4584275
theorem B27886355 : Blo 904575 27886355 := bstep (se 1 (by rfl) ⟨20914766, by rfl⟩ : syracuseStep 27886355 = 41829533) B41829533
theorem B29754317 : Blo 904575 29754317 := bstep (se 3 (by rfl) ⟨5578934, by rfl⟩ : syracuseStep 29754317 = 11157869) B11157869
theorem B19596887 : Blo 904575 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B6530975 : Blo 904575 6530975 := bstep (se 1 (by rfl) ⟨4898231, by rfl⟩ : syracuseStep 6530975 = 9796463) B9796463
theorem B29403121 : Blo 904575 29403121 := bstep (se 2 (by rfl) ⟨11026170, by rfl⟩ : syracuseStep 29403121 = 22052341) B22052341
theorem B3868667 : Blo 904575 3868667 := bstep (se 1 (by rfl) ⟨2901500, by rfl⟩ : syracuseStep 3868667 = 5803001) B5803001
theorem B7547255 : Blo 904575 7547255 := bstep (se 1 (by rfl) ⟨5660441, by rfl⟩ : syracuseStep 7547255 = 11320883) B11320883
theorem B11594927 : Blo 904575 11594927 := bstep (se 1 (by rfl) ⟨8696195, by rfl⟩ : syracuseStep 11594927 = 17392391) B17392391
theorem B4582817 : Blo 904575 4582817 := bstep (se 2 (by rfl) ⟨1718556, by rfl⟩ : syracuseStep 4582817 = 3437113) B3437113
theorem B2035367 : Blo 904575 2035367 := bstep (se 1 (by rfl) ⟨1526525, by rfl⟩ : syracuseStep 2035367 = 3053051) B3053051
theorem B26455747 : Blo 904575 26455747 := bstep (se 1 (by rfl) ⟨19841810, by rfl⟩ : syracuseStep 26455747 = 39683621) B39683621
theorem B2035439 : Blo 904575 2035439 := bstep (se 1 (by rfl) ⟨1526579, by rfl⟩ : syracuseStep 2035439 = 3053159) B3053159
theorem B24809327 : Blo 904575 24809327 := bstep (se 1 (by rfl) ⟨18606995, by rfl⟩ : syracuseStep 24809327 = 37213991) B37213991
theorem B905119 : Blo 904575 905119 := bstep (se 1 (by rfl) ⟨678839, by rfl⟩ : syracuseStep 905119 = 1357679) B1357679
theorem B905383 : Blo 904575 905383 := bstep (se 1 (by rfl) ⟨679037, by rfl⟩ : syracuseStep 905383 = 1358075) B1358075
theorem B9785609 : Blo 904575 9785609 := bstep (se 2 (by rfl) ⟨3669603, by rfl⟩ : syracuseStep 9785609 = 7339207) B7339207
theorem B2289991 : Blo 904575 2289991 := bstep (se 1 (by rfl) ⟨1717493, by rfl⟩ : syracuseStep 2289991 = 3434987) B3434987
theorem B2036123 : Blo 904575 2036123 := bstep (se 1 (by rfl) ⟨1527092, by rfl⟩ : syracuseStep 2036123 = 3054185) B3054185
theorem B905727 : Blo 904575 905727 := bstep (se 1 (by rfl) ⟨679295, by rfl⟩ : syracuseStep 905727 = 1358591) B1358591
theorem B905755 : Blo 904575 905755 := bstep (se 1 (by rfl) ⟨679316, by rfl⟩ : syracuseStep 905755 = 1358633) B1358633
theorem B3265055 : Blo 904575 3265055 := bstep (se 1 (by rfl) ⟨2448791, by rfl⟩ : syracuseStep 3265055 = 4897583) B4897583
theorem B2036393 : Blo 904575 2036393 := bstep (se 2 (by rfl) ⟨763647, by rfl⟩ : syracuseStep 2036393 = 1527295) B1527295
theorem B906087 : Blo 904575 906087 := bstep (se 1 (by rfl) ⟨679565, by rfl⟩ : syracuseStep 906087 = 1359131) B1359131
theorem B906111 : Blo 904575 906111 := bstep (se 1 (by rfl) ⟨679583, by rfl⟩ : syracuseStep 906111 = 1359167) B1359167
theorem B906331 : Blo 904575 906331 := bstep (se 1 (by rfl) ⟨679748, by rfl⟩ : syracuseStep 906331 = 1359497) B1359497
theorem B52892837 : Blo 904575 52892837 := bstep (se 4 (by rfl) ⟨4958703, by rfl⟩ : syracuseStep 52892837 = 9917407) B9917407
theorem B2036987 : Blo 904575 2036987 := bstep (se 1 (by rfl) ⟨1527740, by rfl⟩ : syracuseStep 2036987 = 3055481) B3055481
theorem B4584761 : Blo 904575 4584761 := bstep (se 2 (by rfl) ⟨1719285, by rfl⟩ : syracuseStep 4584761 = 3438571) B3438571
theorem B1357127 : Blo 904575 1357127 := bstep (se 1 (by rfl) ⟨1017845, by rfl⟩ : syracuseStep 1357127 = 2035691) B2035691
theorem B3437903 : Blo 904575 3437903 := bstep (se 1 (by rfl) ⟨2578427, by rfl⟩ : syracuseStep 3437903 = 5156855) B5156855
theorem B2789594477 : Blo 904575 2789594477 := bstep (se 3 (by rfl) ⟨523048964, by rfl⟩ : syracuseStep 2789594477 = 1046097929) B1046097929
theorem B3438071 : Blo 904575 3438071 := bstep (se 1 (by rfl) ⟨2578553, by rfl⟩ : syracuseStep 3438071 = 5157107) B5157107
theorem B6969001 : Blo 904575 6969001 := bstep (se 2 (by rfl) ⟨2613375, by rfl⟩ : syracuseStep 6969001 = 5226751) B5226751
theorem B2176895 : Blo 904575 2176895 := bstep (se 1 (by rfl) ⟨1632671, by rfl⟩ : syracuseStep 2176895 = 3265343) B3265343
theorem B52893757 : Blo 904575 52893757 := bstep (se 3 (by rfl) ⟨9917579, by rfl⟩ : syracuseStep 52893757 = 19835159) B19835159
theorem B2898425 : Blo 904575 2898425 := bstep (se 2 (by rfl) ⟨1086909, by rfl⟩ : syracuseStep 2898425 = 2173819) B2173819
theorem B2038265 : Blo 904575 2038265 := bstep (se 2 (by rfl) ⟨764349, by rfl⟩ : syracuseStep 2038265 = 1528699) B1528699
theorem B1718975 : Blo 904575 1718975 := bstep (se 1 (by rfl) ⟨1289231, by rfl⟩ : syracuseStep 1718975 = 2578463) B2578463
theorem B3439529 : Blo 904575 3439529 := bstep (se 2 (by rfl) ⟨1289823, by rfl⟩ : syracuseStep 3439529 = 2579647) B2579647
theorem B2292745 : Blo 904575 2292745 := bstep (se 2 (by rfl) ⟨859779, by rfl⟩ : syracuseStep 2292745 = 1719559) B1719559
theorem B1358951 : Blo 904575 1358951 := bstep (se 1 (by rfl) ⟨1019213, by rfl⟩ : syracuseStep 1358951 = 2038427) B2038427
theorem B1358975 : Blo 904575 1358975 := bstep (se 1 (by rfl) ⟨1019231, by rfl⟩ : syracuseStep 1358975 = 2038463) B2038463
theorem B70525009 : Blo 904575 70525009 := bstep (se 2 (by rfl) ⟨26446878, by rfl⟩ : syracuseStep 70525009 = 52893757) B52893757
theorem B3056507 : Blo 904575 3056507 := bstep (se 1 (by rfl) ⟨2292380, by rfl⟩ : syracuseStep 3056507 = 4584761) B4584761
theorem B1451263 : Blo 904575 1451263 := bstep (se 1 (by rfl) ⟨1088447, by rfl⟩ : syracuseStep 1451263 = 2176895) B2176895
theorem B3056993 : Blo 904575 3056993 := bstep (se 2 (by rfl) ⟨1146372, by rfl⟩ : syracuseStep 3056993 = 2292745) B2292745
theorem B5031503 : Blo 904575 5031503 := bstep (se 1 (by rfl) ⟨3773627, by rfl⟩ : syracuseStep 5031503 = 7547255) B7547255
theorem B9292001 : Blo 904575 9292001 := bstep (se 2 (by rfl) ⟨3484500, by rfl⟩ : syracuseStep 9292001 = 6969001) B6969001
theorem B6523739 : Blo 904575 6523739 := bstep (se 1 (by rfl) ⟨4892804, by rfl⟩ : syracuseStep 6523739 = 9785609) B9785609
theorem B18590903 : Blo 904575 18590903 := bstep (se 1 (by rfl) ⟨13943177, by rfl⟩ : syracuseStep 18590903 = 27886355) B27886355
theorem B19836211 : Blo 904575 19836211 := bstep (se 1 (by rfl) ⟨14877158, by rfl⟩ : syracuseStep 19836211 = 29754317) B29754317
theorem B35261891 : Blo 904575 35261891 := bstep (se 1 (by rfl) ⟨26446418, by rfl⟩ : syracuseStep 35261891 = 52892837) B52892837
theorem B904751 : Blo 904575 904751 := bstep (se 1 (by rfl) ⟨678563, by rfl⟩ : syracuseStep 904751 = 1357127) B1357127
theorem B4353983 : Blo 904575 4353983 := bstep (se 1 (by rfl) ⟨3265487, by rfl⟩ : syracuseStep 4353983 = 6530975) B6530975
theorem B905967 : Blo 904575 905967 := bstep (se 1 (by rfl) ⟨679475, by rfl⟩ : syracuseStep 905967 = 1358951) B1358951
theorem B905983 : Blo 904575 905983 := bstep (se 1 (by rfl) ⟨679487, by rfl⟩ : syracuseStep 905983 = 1358975) B1358975
theorem B7729951 : Blo 904575 7729951 := bstep (se 1 (by rfl) ⟨5797463, by rfl⟩ : syracuseStep 7729951 = 11594927) B11594927
theorem B1356911 : Blo 904575 1356911 := bstep (se 1 (by rfl) ⟨1017683, by rfl⟩ : syracuseStep 1356911 = 2035367) B2035367
theorem B1356959 : Blo 904575 1356959 := bstep (se 1 (by rfl) ⟨1017719, by rfl⟩ : syracuseStep 1356959 = 2035439) B2035439
theorem B39204161 : Blo 904575 39204161 := bstep (se 2 (by rfl) ⟨14701560, by rfl⟩ : syracuseStep 39204161 = 29403121) B29403121
theorem B1357415 : Blo 904575 1357415 := bstep (se 1 (by rfl) ⟨1018061, by rfl⟩ : syracuseStep 1357415 = 2036123) B2036123
theorem B2176703 : Blo 904575 2176703 := bstep (se 1 (by rfl) ⟨1632527, by rfl⟩ : syracuseStep 2176703 = 3265055) B3265055
theorem B2037455 : Blo 904575 2037455 := bstep (se 1 (by rfl) ⟨1528091, by rfl⟩ : syracuseStep 2037455 = 3056183) B3056183
theorem B3053321 : Blo 904575 3053321 := bstep (se 2 (by rfl) ⟨1144995, by rfl⟩ : syracuseStep 3053321 = 2289991) B2289991
theorem B1357595 : Blo 904575 1357595 := bstep (se 1 (by rfl) ⟨1018196, by rfl⟩ : syracuseStep 1357595 = 2036393) B2036393
theorem B1529833 : Blo 904575 1529833 := bstep (se 2 (by rfl) ⟨573687, by rfl⟩ : syracuseStep 1529833 = 1147375) B1147375
theorem B1357991 : Blo 904575 1357991 := bstep (se 1 (by rfl) ⟨1018493, by rfl⟩ : syracuseStep 1357991 = 2036987) B2036987
theorem B2291935 : Blo 904575 2291935 := bstep (se 1 (by rfl) ⟨1718951, by rfl⟩ : syracuseStep 2291935 = 3437903) B3437903
theorem B1859729651 : Blo 904575 1859729651 := bstep (se 1 (by rfl) ⟨1394797238, by rfl⟩ : syracuseStep 1859729651 = 2789594477) B2789594477
theorem B2292047 : Blo 904575 2292047 := bstep (se 1 (by rfl) ⟨1719035, by rfl⟩ : syracuseStep 2292047 = 3438071) B3438071
theorem B13064591 : Blo 904575 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B2579111 : Blo 904575 2579111 := bstep (se 1 (by rfl) ⟨1934333, by rfl⟩ : syracuseStep 2579111 = 3868667) B3868667
theorem B1932283 : Blo 904575 1932283 := bstep (se 1 (by rfl) ⟨1449212, by rfl⟩ : syracuseStep 1932283 = 2898425) B2898425
theorem B1358843 : Blo 904575 1358843 := bstep (se 1 (by rfl) ⟨1019132, by rfl⟩ : syracuseStep 1358843 = 2038265) B2038265
theorem B1145983 : Blo 904575 1145983 := bstep (se 1 (by rfl) ⟨859487, by rfl⟩ : syracuseStep 1145983 = 1718975) B1718975
theorem B2293019 : Blo 904575 2293019 := bstep (se 1 (by rfl) ⟨1719764, by rfl⟩ : syracuseStep 2293019 = 3439529) B3439529
theorem B35274329 : Blo 904575 35274329 := bstep (se 2 (by rfl) ⟨13227873, by rfl⟩ : syracuseStep 35274329 = 26455747) B26455747
theorem B3055211 : Blo 904575 3055211 := bstep (se 1 (by rfl) ⟨2291408, by rfl⟩ : syracuseStep 3055211 = 4582817) B4582817
theorem B16539551 : Blo 904575 16539551 := bstep (se 1 (by rfl) ⟨12404663, by rfl⟩ : syracuseStep 16539551 = 24809327) B24809327
theorem B3055913 : Blo 904575 3055913 := bstep (se 2 (by rfl) ⟨1145967, by rfl⟩ : syracuseStep 3055913 = 2291935) B2291935
theorem B10306601 : Blo 904575 10306601 := bstep (se 2 (by rfl) ⟨3864975, by rfl⟩ : syracuseStep 10306601 = 7729951) B7729951
theorem B1451135 : Blo 904575 1451135 := bstep (se 1 (by rfl) ⟨1088351, by rfl⟩ : syracuseStep 1451135 = 2176703) B2176703
theorem B1239819767 : Blo 904575 1239819767 := bstep (se 1 (by rfl) ⟨929864825, by rfl⟩ : syracuseStep 1239819767 = 1859729651) B1859729651
theorem B1935017 : Blo 904575 1935017 := bstep (se 2 (by rfl) ⟨725631, by rfl⟩ : syracuseStep 1935017 = 1451263) B1451263
theorem B2902655 : Blo 904575 2902655 := bstep (se 1 (by rfl) ⟨2176991, by rfl⟩ : syracuseStep 2902655 = 4353983) B4353983
theorem B904607 : Blo 904575 904607 := bstep (se 1 (by rfl) ⟨678455, by rfl⟩ : syracuseStep 904607 = 1356911) B1356911
theorem B904639 : Blo 904575 904639 := bstep (se 1 (by rfl) ⟨678479, by rfl⟩ : syracuseStep 904639 = 1356959) B1356959
theorem B26136107 : Blo 904575 26136107 := bstep (se 1 (by rfl) ⟨19602080, by rfl⟩ : syracuseStep 26136107 = 39204161) B39204161
theorem B3354335 : Blo 904575 3354335 := bstep (se 1 (by rfl) ⟨2515751, by rfl⟩ : syracuseStep 3354335 = 5031503) B5031503
theorem B904943 : Blo 904575 904943 := bstep (se 1 (by rfl) ⟨678707, by rfl⟩ : syracuseStep 904943 = 1357415) B1357415
theorem B2035547 : Blo 904575 2035547 := bstep (se 1 (by rfl) ⟨1526660, by rfl⟩ : syracuseStep 2035547 = 3053321) B3053321
theorem B905063 : Blo 904575 905063 := bstep (se 1 (by rfl) ⟨678797, by rfl⟩ : syracuseStep 905063 = 1357595) B1357595
theorem B2576377 : Blo 904575 2576377 := bstep (se 2 (by rfl) ⟨966141, by rfl⟩ : syracuseStep 2576377 = 1932283) B1932283
theorem B905327 : Blo 904575 905327 := bstep (se 1 (by rfl) ⟨678995, by rfl⟩ : syracuseStep 905327 = 1357991) B1357991
theorem B1527977 : Blo 904575 1527977 := bstep (se 2 (by rfl) ⟨572991, by rfl⟩ : syracuseStep 1527977 = 1145983) B1145983
theorem B1528031 : Blo 904575 1528031 := bstep (se 1 (by rfl) ⟨1146023, by rfl⟩ : syracuseStep 1528031 = 2292047) B2292047
theorem B26448281 : Blo 904575 26448281 := bstep (se 2 (by rfl) ⟨9918105, by rfl⟩ : syracuseStep 26448281 = 19836211) B19836211
theorem B905895 : Blo 904575 905895 := bstep (se 1 (by rfl) ⟨679421, by rfl⟩ : syracuseStep 905895 = 1358843) B1358843
theorem B1528679 : Blo 904575 1528679 := bstep (se 1 (by rfl) ⟨1146509, by rfl⟩ : syracuseStep 1528679 = 2293019) B2293019
theorem B23507927 : Blo 904575 23507927 := bstep (se 1 (by rfl) ⟨17630945, by rfl⟩ : syracuseStep 23507927 = 35261891) B35261891
theorem B23516219 : Blo 904575 23516219 := bstep (se 1 (by rfl) ⟨17637164, by rfl⟩ : syracuseStep 23516219 = 35274329) B35274329
theorem B2036807 : Blo 904575 2036807 := bstep (se 1 (by rfl) ⟨1527605, by rfl⟩ : syracuseStep 2036807 = 3055211) B3055211
theorem B94033345 : Blo 904575 94033345 := bstep (se 2 (by rfl) ⟨35262504, by rfl⟩ : syracuseStep 94033345 = 70525009) B70525009
theorem B2037671 : Blo 904575 2037671 := bstep (se 1 (by rfl) ⟨1528253, by rfl⟩ : syracuseStep 2037671 = 3056507) B3056507
theorem B24778669 : Blo 904575 24778669 := bstep (se 3 (by rfl) ⟨4646000, by rfl⟩ : syracuseStep 24778669 = 9292001) B9292001
theorem B2037995 : Blo 904575 2037995 := bstep (se 1 (by rfl) ⟨1528496, by rfl⟩ : syracuseStep 2037995 = 3056993) B3056993
theorem B34838909 : Blo 904575 34838909 := bstep (se 3 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 34838909 = 13064591) B13064591
theorem B1358303 : Blo 904575 1358303 := bstep (se 1 (by rfl) ⟨1018727, by rfl⟩ : syracuseStep 1358303 = 2037455) B2037455
theorem B1719407 : Blo 904575 1719407 := bstep (se 1 (by rfl) ⟨1289555, by rfl⟩ : syracuseStep 1719407 = 2579111) B2579111
theorem B4349159 : Blo 904575 4349159 := bstep (se 1 (by rfl) ⟨3261869, by rfl⟩ : syracuseStep 4349159 = 6523739) B6523739
theorem B12393935 : Blo 904575 12393935 := bstep (se 1 (by rfl) ⟨9295451, by rfl⟩ : syracuseStep 12393935 = 18590903) B18590903
theorem B11026367 : Blo 904575 11026367 := bstep (se 1 (by rfl) ⟨8269775, by rfl⟩ : syracuseStep 11026367 = 16539551) B16539551
theorem B2039777 : Blo 904575 2039777 := bstep (se 2 (by rfl) ⟨764916, by rfl⟩ : syracuseStep 2039777 = 1529833) B1529833
theorem B15671951 : Blo 904575 15671951 := bstep (se 1 (by rfl) ⟨11753963, by rfl⟩ : syracuseStep 15671951 = 23507927) B23507927
theorem B23225939 : Blo 904575 23225939 := bstep (se 1 (by rfl) ⟨17419454, by rfl⟩ : syracuseStep 23225939 = 34838909) B34838909
theorem B1935103 : Blo 904575 1935103 := bstep (se 1 (by rfl) ⟨1451327, by rfl⟩ : syracuseStep 1935103 = 2902655) B2902655
theorem B7350911 : Blo 904575 7350911 := bstep (se 1 (by rfl) ⟨5513183, by rfl⟩ : syracuseStep 7350911 = 11026367) B11026367
theorem B3435169 : Blo 904575 3435169 := bstep (se 2 (by rfl) ⟨1288188, by rfl⟩ : syracuseStep 3435169 = 2576377) B2576377
theorem B1018651 : Blo 904575 1018651 := bstep (se 1 (by rfl) ⟨763988, by rfl⟩ : syracuseStep 1018651 = 1527977) B1527977
theorem B1018687 : Blo 904575 1018687 := bstep (se 1 (by rfl) ⟨764015, by rfl⟩ : syracuseStep 1018687 = 1528031) B1528031
theorem B17632187 : Blo 904575 17632187 := bstep (se 1 (by rfl) ⟨13224140, by rfl⟩ : syracuseStep 17632187 = 26448281) B26448281
theorem B3869693 : Blo 904575 3869693 := bstep (se 3 (by rfl) ⟨725567, by rfl⟩ : syracuseStep 3869693 = 1451135) B1451135
theorem B1019119 : Blo 904575 1019119 := bstep (se 1 (by rfl) ⟨764339, by rfl⟩ : syracuseStep 1019119 = 1528679) B1528679
theorem B1290011 : Blo 904575 1290011 := bstep (se 1 (by rfl) ⟨967508, by rfl⟩ : syracuseStep 1290011 = 1935017) B1935017
theorem B905535 : Blo 904575 905535 := bstep (se 1 (by rfl) ⟨679151, by rfl⟩ : syracuseStep 905535 = 1358303) B1358303
theorem B8262623 : Blo 904575 8262623 := bstep (se 1 (by rfl) ⟨6196967, by rfl⟩ : syracuseStep 8262623 = 12393935) B12393935
theorem B1357031 : Blo 904575 1357031 := bstep (se 1 (by rfl) ⟨1017773, by rfl⟩ : syracuseStep 1357031 = 2035547) B2035547
theorem B2037275 : Blo 904575 2037275 := bstep (se 1 (by rfl) ⟨1527956, by rfl⟩ : syracuseStep 2037275 = 3055913) B3055913
theorem B4585085 : Blo 904575 4585085 := bstep (se 3 (by rfl) ⟨859703, by rfl⟩ : syracuseStep 4585085 = 1719407) B1719407
theorem B6871067 : Blo 904575 6871067 := bstep (se 1 (by rfl) ⟨5153300, by rfl⟩ : syracuseStep 6871067 = 10306601) B10306601
theorem B15677479 : Blo 904575 15677479 := bstep (se 1 (by rfl) ⟨11758109, by rfl⟩ : syracuseStep 15677479 = 23516219) B23516219
theorem B1357871 : Blo 904575 1357871 := bstep (se 1 (by rfl) ⟨1018403, by rfl⟩ : syracuseStep 1357871 = 2036807) B2036807
theorem B826546511 : Blo 904575 826546511 := bstep (se 1 (by rfl) ⟨619909883, by rfl⟩ : syracuseStep 826546511 = 1239819767) B1239819767
theorem B1358447 : Blo 904575 1358447 := bstep (se 1 (by rfl) ⟨1018835, by rfl⟩ : syracuseStep 1358447 = 2037671) B2037671
theorem B1358663 : Blo 904575 1358663 := bstep (se 1 (by rfl) ⟨1018997, by rfl⟩ : syracuseStep 1358663 = 2037995) B2037995
theorem B125377793 : Blo 904575 125377793 := bstep (se 2 (by rfl) ⟨47016672, by rfl⟩ : syracuseStep 125377793 = 94033345) B94033345
theorem B2899439 : Blo 904575 2899439 := bstep (se 1 (by rfl) ⟨2174579, by rfl⟩ : syracuseStep 2899439 = 4349159) B4349159
theorem B17424071 : Blo 904575 17424071 := bstep (se 1 (by rfl) ⟨13068053, by rfl⟩ : syracuseStep 17424071 = 26136107) B26136107
theorem B2236223 : Blo 904575 2236223 := bstep (se 1 (by rfl) ⟨1677167, by rfl⟩ : syracuseStep 2236223 = 3354335) B3354335
theorem B33038225 : Blo 904575 33038225 := bstep (se 2 (by rfl) ⟨12389334, by rfl⟩ : syracuseStep 33038225 = 24778669) B24778669
theorem B1359851 : Blo 904575 1359851 := bstep (se 1 (by rfl) ⟨1019888, by rfl⟩ : syracuseStep 1359851 = 2039777) B2039777
theorem B4580225 : Blo 904575 4580225 := bstep (se 2 (by rfl) ⟨1717584, by rfl⟩ : syracuseStep 4580225 = 3435169) B3435169
theorem B15483959 : Blo 904575 15483959 := bstep (se 1 (by rfl) ⟨11612969, by rfl⟩ : syracuseStep 15483959 = 23225939) B23225939
theorem B3056723 : Blo 904575 3056723 := bstep (se 1 (by rfl) ⟨2292542, by rfl⟩ : syracuseStep 3056723 = 4585085) B4585085
theorem B4580711 : Blo 904575 4580711 := bstep (se 1 (by rfl) ⟨3435533, by rfl⟩ : syracuseStep 4580711 = 6871067) B6871067
theorem B4900607 : Blo 904575 4900607 := bstep (se 1 (by rfl) ⟨3675455, by rfl⟩ : syracuseStep 4900607 = 7350911) B7350911
theorem B83585195 : Blo 904575 83585195 := bstep (se 1 (by rfl) ⟨62688896, by rfl⟩ : syracuseStep 83585195 = 125377793) B125377793
theorem B10447967 : Blo 904575 10447967 := bstep (se 1 (by rfl) ⟨7835975, by rfl⟩ : syracuseStep 10447967 = 15671951) B15671951
theorem B5508415 : Blo 904575 5508415 := bstep (se 1 (by rfl) ⟨4131311, by rfl⟩ : syracuseStep 5508415 = 8262623) B8262623
theorem B904687 : Blo 904575 904687 := bstep (se 1 (by rfl) ⟨678515, by rfl⟩ : syracuseStep 904687 = 1357031) B1357031
theorem B905247 : Blo 904575 905247 := bstep (se 1 (by rfl) ⟨678935, by rfl⟩ : syracuseStep 905247 = 1357871) B1357871
theorem B551031007 : Blo 904575 551031007 := bstep (se 1 (by rfl) ⟨413273255, by rfl⟩ : syracuseStep 551031007 = 826546511) B826546511
theorem B905631 : Blo 904575 905631 := bstep (se 1 (by rfl) ⟨679223, by rfl⟩ : syracuseStep 905631 = 1358447) B1358447
theorem B905775 : Blo 904575 905775 := bstep (se 1 (by rfl) ⟨679331, by rfl⟩ : syracuseStep 905775 = 1358663) B1358663
theorem B22025483 : Blo 904575 22025483 := bstep (se 1 (by rfl) ⟨16519112, by rfl⟩ : syracuseStep 22025483 = 33038225) B33038225
theorem B906567 : Blo 904575 906567 := bstep (se 1 (by rfl) ⟨679925, by rfl⟩ : syracuseStep 906567 = 1359851) B1359851
theorem B20903305 : Blo 904575 20903305 := bstep (se 2 (by rfl) ⟨7838739, by rfl⟩ : syracuseStep 20903305 = 15677479) B15677479
theorem B1358183 : Blo 904575 1358183 := bstep (se 1 (by rfl) ⟨1018637, by rfl⟩ : syracuseStep 1358183 = 2037275) B2037275
theorem B1358201 : Blo 904575 1358201 := bstep (se 2 (by rfl) ⟨509325, by rfl⟩ : syracuseStep 1358201 = 1018651) B1018651
theorem B1358249 : Blo 904575 1358249 := bstep (se 2 (by rfl) ⟨509343, by rfl⟩ : syracuseStep 1358249 = 1018687) B1018687
theorem B1358825 : Blo 904575 1358825 := bstep (se 2 (by rfl) ⟨509559, by rfl⟩ : syracuseStep 1358825 = 1019119) B1019119
theorem B11754791 : Blo 904575 11754791 := bstep (se 1 (by rfl) ⟨8816093, by rfl⟩ : syracuseStep 11754791 = 17632187) B17632187
theorem B2579795 : Blo 904575 2579795 := bstep (se 1 (by rfl) ⟨1934846, by rfl⟩ : syracuseStep 2579795 = 3869693) B3869693
theorem B3440029 : Blo 904575 3440029 := bstep (se 3 (by rfl) ⟨645005, by rfl⟩ : syracuseStep 3440029 = 1290011) B1290011
theorem B1932959 : Blo 904575 1932959 := bstep (se 1 (by rfl) ⟨1449719, by rfl⟩ : syracuseStep 1932959 = 2899439) B2899439
theorem B2580137 : Blo 904575 2580137 := bstep (se 2 (by rfl) ⟨967551, by rfl⟩ : syracuseStep 2580137 = 1935103) B1935103
theorem B11616047 : Blo 904575 11616047 := bstep (se 1 (by rfl) ⟨8712035, by rfl⟩ : syracuseStep 11616047 = 17424071) B17424071
theorem B1490815 : Blo 904575 1490815 := bstep (se 1 (by rfl) ⟨1118111, by rfl⟩ : syracuseStep 1490815 = 2236223) B2236223
theorem B734708009 : Blo 904575 734708009 := bstep (se 2 (by rfl) ⟨275515503, by rfl⟩ : syracuseStep 734708009 = 551031007) B551031007
theorem B10322639 : Blo 904575 10322639 := bstep (se 1 (by rfl) ⟨7741979, by rfl⟩ : syracuseStep 10322639 = 15483959) B15483959
theorem B55723463 : Blo 904575 55723463 := bstep (se 1 (by rfl) ⟨41792597, by rfl⟩ : syracuseStep 55723463 = 83585195) B83585195
theorem B29378213 : Blo 904575 29378213 := bstep (se 4 (by rfl) ⟨2754207, by rfl⟩ : syracuseStep 29378213 = 5508415) B5508415
theorem B27871073 : Blo 904575 27871073 := bstep (se 2 (by rfl) ⟨10451652, by rfl⟩ : syracuseStep 27871073 = 20903305) B20903305
theorem B6965311 : Blo 904575 6965311 := bstep (se 1 (by rfl) ⟨5223983, by rfl⟩ : syracuseStep 6965311 = 10447967) B10447967
theorem B1288639 : Blo 904575 1288639 := bstep (se 1 (by rfl) ⟨966479, by rfl⟩ : syracuseStep 1288639 = 1932959) B1932959
theorem B7744031 : Blo 904575 7744031 := bstep (se 1 (by rfl) ⟨5808023, by rfl⟩ : syracuseStep 7744031 = 11616047) B11616047
theorem B14683655 : Blo 904575 14683655 := bstep (se 1 (by rfl) ⟨11012741, by rfl⟩ : syracuseStep 14683655 = 22025483) B22025483
theorem B905455 : Blo 904575 905455 := bstep (se 1 (by rfl) ⟨679091, by rfl⟩ : syracuseStep 905455 = 1358183) B1358183
theorem B905467 : Blo 904575 905467 := bstep (se 1 (by rfl) ⟨679100, by rfl⟩ : syracuseStep 905467 = 1358201) B1358201
theorem B905499 : Blo 904575 905499 := bstep (se 1 (by rfl) ⟨679124, by rfl⟩ : syracuseStep 905499 = 1358249) B1358249
theorem B905883 : Blo 904575 905883 := bstep (se 1 (by rfl) ⟨679412, by rfl⟩ : syracuseStep 905883 = 1358825) B1358825
theorem B7836527 : Blo 904575 7836527 := bstep (se 1 (by rfl) ⟨5877395, by rfl⟩ : syracuseStep 7836527 = 11754791) B11754791
theorem B1987753 : Blo 904575 1987753 := bstep (se 2 (by rfl) ⟨745407, by rfl⟩ : syracuseStep 1987753 = 1490815) B1490815
theorem B3053483 : Blo 904575 3053483 := bstep (se 1 (by rfl) ⟨2290112, by rfl⟩ : syracuseStep 3053483 = 4580225) B4580225
theorem B2037815 : Blo 904575 2037815 := bstep (se 1 (by rfl) ⟨1528361, by rfl⟩ : syracuseStep 2037815 = 3056723) B3056723
theorem B3053807 : Blo 904575 3053807 := bstep (se 1 (by rfl) ⟨2290355, by rfl⟩ : syracuseStep 3053807 = 4580711) B4580711
theorem B3267071 : Blo 904575 3267071 := bstep (se 1 (by rfl) ⟨2450303, by rfl⟩ : syracuseStep 3267071 = 4900607) B4900607
theorem B4586705 : Blo 904575 4586705 := bstep (se 2 (by rfl) ⟨1720014, by rfl⟩ : syracuseStep 4586705 = 3440029) B3440029
theorem B1719863 : Blo 904575 1719863 := bstep (se 1 (by rfl) ⟨1289897, by rfl⟩ : syracuseStep 1719863 = 2579795) B2579795
theorem B1720091 : Blo 904575 1720091 := bstep (se 1 (by rfl) ⟨1290068, by rfl⟩ : syracuseStep 1720091 = 2580137) B2580137
theorem B6881759 : Blo 904575 6881759 := bstep (se 1 (by rfl) ⟨5161319, by rfl⟩ : syracuseStep 6881759 = 10322639) B10322639
theorem B18580715 : Blo 904575 18580715 := bstep (se 1 (by rfl) ⟨13935536, by rfl⟩ : syracuseStep 18580715 = 27871073) B27871073
theorem B5162687 : Blo 904575 5162687 := bstep (se 1 (by rfl) ⟨3872015, by rfl⟩ : syracuseStep 5162687 = 7744031) B7744031
theorem B3057803 : Blo 904575 3057803 := bstep (se 1 (by rfl) ⟨2293352, by rfl⟩ : syracuseStep 3057803 = 4586705) B4586705
theorem B2035655 : Blo 904575 2035655 := bstep (se 1 (by rfl) ⟨1526741, by rfl⟩ : syracuseStep 2035655 = 3053483) B3053483
theorem B2035871 : Blo 904575 2035871 := bstep (se 1 (by rfl) ⟨1526903, by rfl⟩ : syracuseStep 2035871 = 3053807) B3053807
theorem B2650337 : Blo 904575 2650337 := bstep (se 2 (by rfl) ⟨993876, by rfl⟩ : syracuseStep 2650337 = 1987753) B1987753
theorem B9287081 : Blo 904575 9287081 := bstep (se 2 (by rfl) ⟨3482655, by rfl⟩ : syracuseStep 9287081 = 6965311) B6965311
theorem B489805339 : Blo 904575 489805339 := bstep (se 1 (by rfl) ⟨367354004, by rfl⟩ : syracuseStep 489805339 = 734708009) B734708009
theorem B5224351 : Blo 904575 5224351 := bstep (se 1 (by rfl) ⟨3918263, by rfl⟩ : syracuseStep 5224351 = 7836527) B7836527
theorem B1718185 : Blo 904575 1718185 := bstep (se 2 (by rfl) ⟨644319, by rfl⟩ : syracuseStep 1718185 = 1288639) B1288639
theorem B37148975 : Blo 904575 37148975 := bstep (se 1 (by rfl) ⟨27861731, by rfl⟩ : syracuseStep 37148975 = 55723463) B55723463
theorem B19585475 : Blo 904575 19585475 := bstep (se 1 (by rfl) ⟨14689106, by rfl⟩ : syracuseStep 19585475 = 29378213) B29378213
theorem B1358543 : Blo 904575 1358543 := bstep (se 1 (by rfl) ⟨1018907, by rfl⟩ : syracuseStep 1358543 = 2037815) B2037815
theorem B2178047 : Blo 904575 2178047 := bstep (se 1 (by rfl) ⟨1633535, by rfl⟩ : syracuseStep 2178047 = 3267071) B3267071
theorem B9789103 : Blo 904575 9789103 := bstep (se 1 (by rfl) ⟨7341827, by rfl⟩ : syracuseStep 9789103 = 14683655) B14683655
theorem B1146575 : Blo 904575 1146575 := bstep (se 1 (by rfl) ⟨859931, by rfl⟩ : syracuseStep 1146575 = 1719863) B1719863
theorem B1146727 : Blo 904575 1146727 := bstep (se 1 (by rfl) ⟨860045, by rfl⟩ : syracuseStep 1146727 = 1720091) B1720091
theorem B4587839 : Blo 904575 4587839 := bstep (se 1 (by rfl) ⟨3440879, by rfl⟩ : syracuseStep 4587839 = 6881759) B6881759
theorem B12387143 : Blo 904575 12387143 := bstep (se 1 (by rfl) ⟨9290357, by rfl⟩ : syracuseStep 12387143 = 18580715) B18580715
theorem B3441791 : Blo 904575 3441791 := bstep (se 1 (by rfl) ⟨2581343, by rfl⟩ : syracuseStep 3441791 = 5162687) B5162687
theorem B24765983 : Blo 904575 24765983 := bstep (se 1 (by rfl) ⟨18574487, by rfl⟩ : syracuseStep 24765983 = 37148975) B37148975
theorem B3057533 : Blo 904575 3057533 := bstep (se 3 (by rfl) ⟨573287, by rfl⟩ : syracuseStep 3057533 = 1146575) B1146575
theorem B13052137 : Blo 904575 13052137 := bstep (se 2 (by rfl) ⟨4894551, by rfl⟩ : syracuseStep 13052137 = 9789103) B9789103
theorem B6965801 : Blo 904575 6965801 := bstep (se 2 (by rfl) ⟨2612175, by rfl⟩ : syracuseStep 6965801 = 5224351) B5224351
theorem B905695 : Blo 904575 905695 := bstep (se 1 (by rfl) ⟨679271, by rfl⟩ : syracuseStep 905695 = 1358543) B1358543
theorem B1528969 : Blo 904575 1528969 := bstep (se 2 (by rfl) ⟨573363, by rfl⟩ : syracuseStep 1528969 = 1146727) B1146727
theorem B2290913 : Blo 904575 2290913 := bstep (se 2 (by rfl) ⟨859092, by rfl⟩ : syracuseStep 2290913 = 1718185) B1718185
theorem B1357103 : Blo 904575 1357103 := bstep (se 1 (by rfl) ⟨1017827, by rfl⟩ : syracuseStep 1357103 = 2035655) B2035655
theorem B1357247 : Blo 904575 1357247 := bstep (se 1 (by rfl) ⟨1017935, by rfl⟩ : syracuseStep 1357247 = 2035871) B2035871
theorem B1766891 : Blo 904575 1766891 := bstep (se 1 (by rfl) ⟨1325168, by rfl⟩ : syracuseStep 1766891 = 2650337) B2650337
theorem B6191387 : Blo 904575 6191387 := bstep (se 1 (by rfl) ⟨4643540, by rfl⟩ : syracuseStep 6191387 = 9287081) B9287081
theorem B2038535 : Blo 904575 2038535 := bstep (se 1 (by rfl) ⟨1528901, by rfl⟩ : syracuseStep 2038535 = 3057803) B3057803
theorem B13056983 : Blo 904575 13056983 := bstep (se 1 (by rfl) ⟨9792737, by rfl⟩ : syracuseStep 13056983 = 19585475) B19585475
theorem B653073785 : Blo 904575 653073785 := bstep (se 2 (by rfl) ⟨244902669, by rfl⟩ : syracuseStep 653073785 = 489805339) B489805339
theorem B5808125 : Blo 904575 5808125 := bstep (se 3 (by rfl) ⟨1089023, by rfl⟩ : syracuseStep 5808125 = 2178047) B2178047
theorem B8258095 : Blo 904575 8258095 := bstep (se 1 (by rfl) ⟨6193571, by rfl⟩ : syracuseStep 8258095 = 12387143) B12387143
theorem B2294527 : Blo 904575 2294527 := bstep (se 1 (by rfl) ⟨1720895, by rfl⟩ : syracuseStep 2294527 = 3441791) B3441791
theorem B4711709 : Blo 904575 4711709 := bstep (se 3 (by rfl) ⟨883445, by rfl⟩ : syracuseStep 4711709 = 1766891) B1766891
theorem B435382523 : Blo 904575 435382523 := bstep (se 1 (by rfl) ⟨326536892, by rfl⟩ : syracuseStep 435382523 = 653073785) B653073785
theorem B3058559 : Blo 904575 3058559 := bstep (se 1 (by rfl) ⟨2293919, by rfl⟩ : syracuseStep 3058559 = 4587839) B4587839
theorem B17402849 : Blo 904575 17402849 := bstep (se 2 (by rfl) ⟨6526068, by rfl⟩ : syracuseStep 17402849 = 13052137) B13052137
theorem B1527275 : Blo 904575 1527275 := bstep (se 1 (by rfl) ⟨1145456, by rfl⟩ : syracuseStep 1527275 = 2290913) B2290913
theorem B904735 : Blo 904575 904735 := bstep (se 1 (by rfl) ⟨678551, by rfl⟩ : syracuseStep 904735 = 1357103) B1357103
theorem B904831 : Blo 904575 904831 := bstep (se 1 (by rfl) ⟨678623, by rfl⟩ : syracuseStep 904831 = 1357247) B1357247
theorem B16510655 : Blo 904575 16510655 := bstep (se 1 (by rfl) ⟨12382991, by rfl⟩ : syracuseStep 16510655 = 24765983) B24765983
theorem B8704655 : Blo 904575 8704655 := bstep (se 1 (by rfl) ⟨6528491, by rfl⟩ : syracuseStep 8704655 = 13056983) B13056983
theorem B15488333 : Blo 904575 15488333 := bstep (se 3 (by rfl) ⟨2904062, by rfl⟩ : syracuseStep 15488333 = 5808125) B5808125
theorem B2038355 : Blo 904575 2038355 := bstep (se 1 (by rfl) ⟨1528766, by rfl⟩ : syracuseStep 2038355 = 3057533) B3057533
theorem B2038625 : Blo 904575 2038625 := bstep (se 2 (by rfl) ⟨764484, by rfl⟩ : syracuseStep 2038625 = 1528969) B1528969
theorem B4127591 : Blo 904575 4127591 := bstep (se 1 (by rfl) ⟨3095693, by rfl⟩ : syracuseStep 4127591 = 6191387) B6191387
theorem B4643867 : Blo 904575 4643867 := bstep (se 1 (by rfl) ⟨3482900, by rfl⟩ : syracuseStep 4643867 = 6965801) B6965801
theorem B1359023 : Blo 904575 1359023 := bstep (se 1 (by rfl) ⟨1019267, by rfl⟩ : syracuseStep 1359023 = 2038535) B2038535
theorem B11601899 : Blo 904575 11601899 := bstep (se 1 (by rfl) ⟨8701424, by rfl⟩ : syracuseStep 11601899 = 17402849) B17402849
theorem B1018183 : Blo 904575 1018183 := bstep (se 1 (by rfl) ⟨763637, by rfl⟩ : syracuseStep 1018183 = 1527275) B1527275
theorem B44043173 : Blo 904575 44043173 := bstep (se 4 (by rfl) ⟨4129047, by rfl⟩ : syracuseStep 44043173 = 8258095) B8258095
theorem B5803103 : Blo 904575 5803103 := bstep (se 1 (by rfl) ⟨4352327, by rfl⟩ : syracuseStep 5803103 = 8704655) B8704655
theorem B10325555 : Blo 904575 10325555 := bstep (se 1 (by rfl) ⟨7744166, by rfl⟩ : syracuseStep 10325555 = 15488333) B15488333
theorem B3059369 : Blo 904575 3059369 := bstep (se 2 (by rfl) ⟨1147263, by rfl⟩ : syracuseStep 3059369 = 2294527) B2294527
theorem B290255015 : Blo 904575 290255015 := bstep (se 1 (by rfl) ⟨217691261, by rfl⟩ : syracuseStep 290255015 = 435382523) B435382523
theorem B906015 : Blo 904575 906015 := bstep (se 1 (by rfl) ⟨679511, by rfl⟩ : syracuseStep 906015 = 1359023) B1359023
theorem B11007103 : Blo 904575 11007103 := bstep (se 1 (by rfl) ⟨8255327, by rfl⟩ : syracuseStep 11007103 = 16510655) B16510655
theorem B12564557 : Blo 904575 12564557 := bstep (se 3 (by rfl) ⟨2355854, by rfl⟩ : syracuseStep 12564557 = 4711709) B4711709
theorem B1358903 : Blo 904575 1358903 := bstep (se 1 (by rfl) ⟨1019177, by rfl⟩ : syracuseStep 1358903 = 2038355) B2038355
theorem B1359083 : Blo 904575 1359083 := bstep (se 1 (by rfl) ⟨1019312, by rfl⟩ : syracuseStep 1359083 = 2038625) B2038625
theorem B2751727 : Blo 904575 2751727 := bstep (se 1 (by rfl) ⟨2063795, by rfl⟩ : syracuseStep 2751727 = 4127591) B4127591
theorem B2039039 : Blo 904575 2039039 := bstep (se 1 (by rfl) ⟨1529279, by rfl⟩ : syracuseStep 2039039 = 3058559) B3058559
theorem B3095911 : Blo 904575 3095911 := bstep (se 1 (by rfl) ⟨2321933, by rfl⟩ : syracuseStep 3095911 = 4643867) B4643867
theorem B193503343 : Blo 904575 193503343 := bstep (se 1 (by rfl) ⟨145127507, by rfl⟩ : syracuseStep 193503343 = 290255015) B290255015
theorem B7734599 : Blo 904575 7734599 := bstep (se 1 (by rfl) ⟨5800949, by rfl⟩ : syracuseStep 7734599 = 11601899) B11601899
theorem B29362115 : Blo 904575 29362115 := bstep (se 1 (by rfl) ⟨22021586, by rfl⟩ : syracuseStep 29362115 = 44043173) B44043173
theorem B3868735 : Blo 904575 3868735 := bstep (se 1 (by rfl) ⟨2901551, by rfl⟩ : syracuseStep 3868735 = 5803103) B5803103
theorem B6883703 : Blo 904575 6883703 := bstep (se 1 (by rfl) ⟨5162777, by rfl⟩ : syracuseStep 6883703 = 10325555) B10325555
theorem B8376371 : Blo 904575 8376371 := bstep (se 1 (by rfl) ⟨6282278, by rfl⟩ : syracuseStep 8376371 = 12564557) B12564557
theorem B14676137 : Blo 904575 14676137 := bstep (se 2 (by rfl) ⟨5503551, by rfl⟩ : syracuseStep 14676137 = 11007103) B11007103
theorem B905935 : Blo 904575 905935 := bstep (se 1 (by rfl) ⟨679451, by rfl⟩ : syracuseStep 905935 = 1358903) B1358903
theorem B906055 : Blo 904575 906055 := bstep (se 1 (by rfl) ⟨679541, by rfl⟩ : syracuseStep 906055 = 1359083) B1359083
theorem B1357577 : Blo 904575 1357577 := bstep (se 2 (by rfl) ⟨509091, by rfl⟩ : syracuseStep 1357577 = 1018183) B1018183
theorem B3668969 : Blo 904575 3668969 := bstep (se 2 (by rfl) ⟨1375863, by rfl⟩ : syracuseStep 3668969 = 2751727) B2751727
theorem B4127881 : Blo 904575 4127881 := bstep (se 2 (by rfl) ⟨1547955, by rfl⟩ : syracuseStep 4127881 = 3095911) B3095911
theorem B1359359 : Blo 904575 1359359 := bstep (se 1 (by rfl) ⟨1019519, by rfl⟩ : syracuseStep 1359359 = 2039039) B2039039
theorem B2039579 : Blo 904575 2039579 := bstep (se 1 (by rfl) ⟨1529684, by rfl⟩ : syracuseStep 2039579 = 3059369) B3059369
theorem B4589135 : Blo 904575 4589135 := bstep (se 1 (by rfl) ⟨3441851, by rfl⟩ : syracuseStep 4589135 = 6883703) B6883703
theorem B9784091 : Blo 904575 9784091 := bstep (se 1 (by rfl) ⟨7338068, by rfl⟩ : syracuseStep 9784091 = 14676137) B14676137
theorem B5156399 : Blo 904575 5156399 := bstep (se 1 (by rfl) ⟨3867299, by rfl⟩ : syracuseStep 5156399 = 7734599) B7734599
theorem B905051 : Blo 904575 905051 := bstep (se 1 (by rfl) ⟨678788, by rfl⟩ : syracuseStep 905051 = 1357577) B1357577
theorem B2445979 : Blo 904575 2445979 := bstep (se 1 (by rfl) ⟨1834484, by rfl⟩ : syracuseStep 2445979 = 3668969) B3668969
theorem B906239 : Blo 904575 906239 := bstep (se 1 (by rfl) ⟨679679, by rfl⟩ : syracuseStep 906239 = 1359359) B1359359
theorem B5584247 : Blo 904575 5584247 := bstep (se 1 (by rfl) ⟨4188185, by rfl⟩ : syracuseStep 5584247 = 8376371) B8376371
theorem B5158313 : Blo 904575 5158313 := bstep (se 2 (by rfl) ⟨1934367, by rfl⟩ : syracuseStep 5158313 = 3868735) B3868735
theorem B258004457 : Blo 904575 258004457 := bstep (se 2 (by rfl) ⟨96751671, by rfl⟩ : syracuseStep 258004457 = 193503343) B193503343
theorem B5503841 : Blo 904575 5503841 := bstep (se 2 (by rfl) ⟨2063940, by rfl⟩ : syracuseStep 5503841 = 4127881) B4127881
theorem B78298973 : Blo 904575 78298973 := bstep (se 3 (by rfl) ⟨14681057, by rfl⟩ : syracuseStep 78298973 = 29362115) B29362115
theorem B1359719 : Blo 904575 1359719 := bstep (se 1 (by rfl) ⟨1019789, by rfl⟩ : syracuseStep 1359719 = 2039579) B2039579
theorem B3261305 : Blo 904575 3261305 := bstep (se 2 (by rfl) ⟨1222989, by rfl⟩ : syracuseStep 3261305 = 2445979) B2445979
theorem B6522727 : Blo 904575 6522727 := bstep (se 1 (by rfl) ⟨4892045, by rfl⟩ : syracuseStep 6522727 = 9784091) B9784091
theorem B3722831 : Blo 904575 3722831 := bstep (se 1 (by rfl) ⟨2792123, by rfl⟩ : syracuseStep 3722831 = 5584247) B5584247
theorem B172002971 : Blo 904575 172002971 := bstep (se 1 (by rfl) ⟨129002228, by rfl⟩ : syracuseStep 172002971 = 258004457) B258004457
theorem B3059423 : Blo 904575 3059423 := bstep (se 1 (by rfl) ⟨2294567, by rfl⟩ : syracuseStep 3059423 = 4589135) B4589135
theorem B3437599 : Blo 904575 3437599 := bstep (se 1 (by rfl) ⟨2578199, by rfl⟩ : syracuseStep 3437599 = 5156399) B5156399
theorem B906479 : Blo 904575 906479 := bstep (se 1 (by rfl) ⟨679859, by rfl⟩ : syracuseStep 906479 = 1359719) B1359719
theorem B3438875 : Blo 904575 3438875 := bstep (se 1 (by rfl) ⟨2579156, by rfl⟩ : syracuseStep 3438875 = 5158313) B5158313
theorem B3669227 : Blo 904575 3669227 := bstep (se 1 (by rfl) ⟨2751920, by rfl⟩ : syracuseStep 3669227 = 5503841) B5503841
theorem B52199315 : Blo 904575 52199315 := bstep (se 1 (by rfl) ⟨39149486, by rfl⟩ : syracuseStep 52199315 = 78298973) B78298973
theorem B2174203 : Blo 904575 2174203 := bstep (se 1 (by rfl) ⟨1630652, by rfl⟩ : syracuseStep 2174203 = 3261305) B3261305
theorem B4583465 : Blo 904575 4583465 := bstep (se 2 (by rfl) ⟨1718799, by rfl⟩ : syracuseStep 4583465 = 3437599) B3437599
theorem B458674589 : Blo 904575 458674589 := bstep (se 3 (by rfl) ⟨86001485, by rfl⟩ : syracuseStep 458674589 = 172002971) B172002971
theorem B2446151 : Blo 904575 2446151 := bstep (se 1 (by rfl) ⟨1834613, by rfl⟩ : syracuseStep 2446151 = 3669227) B3669227
theorem B8696969 : Blo 904575 8696969 := bstep (se 2 (by rfl) ⟨3261363, by rfl⟩ : syracuseStep 8696969 = 6522727) B6522727
theorem B2292583 : Blo 904575 2292583 := bstep (se 1 (by rfl) ⟨1719437, by rfl⟩ : syracuseStep 2292583 = 3438875) B3438875
theorem B2481887 : Blo 904575 2481887 := bstep (se 1 (by rfl) ⟨1861415, by rfl⟩ : syracuseStep 2481887 = 3722831) B3722831
theorem B2039615 : Blo 904575 2039615 := bstep (se 1 (by rfl) ⟨1529711, by rfl⟩ : syracuseStep 2039615 = 3059423) B3059423
theorem B34799543 : Blo 904575 34799543 := bstep (se 1 (by rfl) ⟨26099657, by rfl⟩ : syracuseStep 34799543 = 52199315) B52199315
theorem B3055643 : Blo 904575 3055643 := bstep (se 1 (by rfl) ⟨2291732, by rfl⟩ : syracuseStep 3055643 = 4583465) B4583465
theorem B305783059 : Blo 904575 305783059 := bstep (se 1 (by rfl) ⟨229337294, by rfl⟩ : syracuseStep 305783059 = 458674589) B458674589
theorem B26092277 : Blo 904575 26092277 := bstep (se 5 (by rfl) ⟨1223075, by rfl⟩ : syracuseStep 26092277 = 2446151) B2446151
theorem B3056777 : Blo 904575 3056777 := bstep (se 2 (by rfl) ⟨1146291, by rfl⟩ : syracuseStep 3056777 = 2292583) B2292583
theorem B5797979 : Blo 904575 5797979 := bstep (se 1 (by rfl) ⟨4348484, by rfl⟩ : syracuseStep 5797979 = 8696969) B8696969
theorem B2898937 : Blo 904575 2898937 := bstep (se 2 (by rfl) ⟨1087101, by rfl⟩ : syracuseStep 2898937 = 2174203) B2174203
theorem B1654591 : Blo 904575 1654591 := bstep (se 1 (by rfl) ⟨1240943, by rfl⟩ : syracuseStep 1654591 = 2481887) B2481887
theorem B1359743 : Blo 904575 1359743 := bstep (se 1 (by rfl) ⟨1019807, by rfl⟩ : syracuseStep 1359743 = 2039615) B2039615
theorem B23199695 : Blo 904575 23199695 := bstep (se 1 (by rfl) ⟨17399771, by rfl⟩ : syracuseStep 23199695 = 34799543) B34799543
theorem B2206121 : Blo 904575 2206121 := bstep (se 2 (by rfl) ⟨827295, by rfl⟩ : syracuseStep 2206121 = 1654591) B1654591
theorem B407710745 : Blo 904575 407710745 := bstep (se 2 (by rfl) ⟨152891529, by rfl⟩ : syracuseStep 407710745 = 305783059) B305783059
theorem B17394851 : Blo 904575 17394851 := bstep (se 1 (by rfl) ⟨13046138, by rfl⟩ : syracuseStep 17394851 = 26092277) B26092277
theorem B906495 : Blo 904575 906495 := bstep (se 1 (by rfl) ⟨679871, by rfl⟩ : syracuseStep 906495 = 1359743) B1359743
theorem B2037095 : Blo 904575 2037095 := bstep (se 1 (by rfl) ⟨1527821, by rfl⟩ : syracuseStep 2037095 = 3055643) B3055643
theorem B2037851 : Blo 904575 2037851 := bstep (se 1 (by rfl) ⟨1528388, by rfl⟩ : syracuseStep 2037851 = 3056777) B3056777
theorem B3865249 : Blo 904575 3865249 := bstep (se 2 (by rfl) ⟨1449468, by rfl⟩ : syracuseStep 3865249 = 2898937) B2898937
theorem B3865319 : Blo 904575 3865319 := bstep (se 1 (by rfl) ⟨2898989, by rfl⟩ : syracuseStep 3865319 = 5797979) B5797979
theorem B15466463 : Blo 904575 15466463 := bstep (se 1 (by rfl) ⟨11599847, by rfl⟩ : syracuseStep 15466463 = 23199695) B23199695
theorem B5153665 : Blo 904575 5153665 := bstep (se 2 (by rfl) ⟨1932624, by rfl⟩ : syracuseStep 5153665 = 3865249) B3865249
theorem B5882989 : Blo 904575 5882989 := bstep (se 3 (by rfl) ⟨1103060, by rfl⟩ : syracuseStep 5882989 = 2206121) B2206121
theorem B2576879 : Blo 904575 2576879 := bstep (se 1 (by rfl) ⟨1932659, by rfl⟩ : syracuseStep 2576879 = 3865319) B3865319
theorem B271807163 : Blo 904575 271807163 := bstep (se 1 (by rfl) ⟨203855372, by rfl⟩ : syracuseStep 271807163 = 407710745) B407710745
theorem B11596567 : Blo 904575 11596567 := bstep (se 1 (by rfl) ⟨8697425, by rfl⟩ : syracuseStep 11596567 = 17394851) B17394851
theorem B10310975 : Blo 904575 10310975 := bstep (se 1 (by rfl) ⟨7733231, by rfl⟩ : syracuseStep 10310975 = 15466463) B15466463
theorem B1358063 : Blo 904575 1358063 := bstep (se 1 (by rfl) ⟨1018547, by rfl⟩ : syracuseStep 1358063 = 2037095) B2037095
theorem B1358567 : Blo 904575 1358567 := bstep (se 1 (by rfl) ⟨1018925, by rfl⟩ : syracuseStep 1358567 = 2037851) B2037851
theorem B6873983 : Blo 904575 6873983 := bstep (se 1 (by rfl) ⟨5155487, by rfl⟩ : syracuseStep 6873983 = 10310975) B10310975
theorem B15462089 : Blo 904575 15462089 := bstep (se 2 (by rfl) ⟨5798283, by rfl⟩ : syracuseStep 15462089 = 11596567) B11596567
theorem B7843985 : Blo 904575 7843985 := bstep (se 2 (by rfl) ⟨2941494, by rfl⟩ : syracuseStep 7843985 = 5882989) B5882989
theorem B905375 : Blo 904575 905375 := bstep (se 1 (by rfl) ⟨679031, by rfl⟩ : syracuseStep 905375 = 1358063) B1358063
theorem B905711 : Blo 904575 905711 := bstep (se 1 (by rfl) ⟨679283, by rfl⟩ : syracuseStep 905711 = 1358567) B1358567
theorem B1717919 : Blo 904575 1717919 := bstep (se 1 (by rfl) ⟨1288439, by rfl⟩ : syracuseStep 1717919 = 2576879) B2576879
theorem B181204775 : Blo 904575 181204775 := bstep (se 1 (by rfl) ⟨135903581, by rfl⟩ : syracuseStep 181204775 = 271807163) B271807163
theorem B6871553 : Blo 904575 6871553 := bstep (se 2 (by rfl) ⟨2576832, by rfl⟩ : syracuseStep 6871553 = 5153665) B5153665
theorem B4581035 : Blo 904575 4581035 := bstep (se 1 (by rfl) ⟨3435776, by rfl⟩ : syracuseStep 4581035 = 6871553) B6871553
theorem B10308059 : Blo 904575 10308059 := bstep (se 1 (by rfl) ⟨7731044, by rfl⟩ : syracuseStep 10308059 = 15462089) B15462089
theorem B5229323 : Blo 904575 5229323 := bstep (se 1 (by rfl) ⟨3921992, by rfl⟩ : syracuseStep 5229323 = 7843985) B7843985
theorem B4582655 : Blo 904575 4582655 := bstep (se 1 (by rfl) ⟨3436991, by rfl⟩ : syracuseStep 4582655 = 6873983) B6873983
theorem B120803183 : Blo 904575 120803183 := bstep (se 1 (by rfl) ⟨90602387, by rfl⟩ : syracuseStep 120803183 = 181204775) B181204775
theorem B1145279 : Blo 904575 1145279 := bstep (se 1 (by rfl) ⟨858959, by rfl⟩ : syracuseStep 1145279 = 1717919) B1717919
theorem B3486215 : Blo 904575 3486215 := bstep (se 1 (by rfl) ⟨2614661, by rfl⟩ : syracuseStep 3486215 = 5229323) B5229323
theorem B3054023 : Blo 904575 3054023 := bstep (se 1 (by rfl) ⟨2290517, by rfl⟩ : syracuseStep 3054023 = 4581035) B4581035
theorem B3054077 : Blo 904575 3054077 := bstep (se 3 (by rfl) ⟨572639, by rfl⟩ : syracuseStep 3054077 = 1145279) B1145279
theorem B6872039 : Blo 904575 6872039 := bstep (se 1 (by rfl) ⟨5154029, by rfl⟩ : syracuseStep 6872039 = 10308059) B10308059
theorem B3055103 : Blo 904575 3055103 := bstep (se 1 (by rfl) ⟨2291327, by rfl⟩ : syracuseStep 3055103 = 4582655) B4582655
theorem B80535455 : Blo 904575 80535455 := bstep (se 1 (by rfl) ⟨60401591, by rfl⟩ : syracuseStep 80535455 = 120803183) B120803183
theorem B4581359 : Blo 904575 4581359 := bstep (se 1 (by rfl) ⟨3436019, by rfl⟩ : syracuseStep 4581359 = 6872039) B6872039
theorem B2036015 : Blo 904575 2036015 := bstep (se 1 (by rfl) ⟨1527011, by rfl⟩ : syracuseStep 2036015 = 3054023) B3054023
theorem B2036051 : Blo 904575 2036051 := bstep (se 1 (by rfl) ⟨1527038, by rfl⟩ : syracuseStep 2036051 = 3054077) B3054077
theorem B2036735 : Blo 904575 2036735 := bstep (se 1 (by rfl) ⟨1527551, by rfl⟩ : syracuseStep 2036735 = 3055103) B3055103
theorem B2324143 : Blo 904575 2324143 := bstep (se 1 (by rfl) ⟨1743107, by rfl⟩ : syracuseStep 2324143 = 3486215) B3486215
theorem B53690303 : Blo 904575 53690303 := bstep (se 1 (by rfl) ⟨40267727, by rfl⟩ : syracuseStep 53690303 = 80535455) B80535455
theorem B3098857 : Blo 904575 3098857 := bstep (se 2 (by rfl) ⟨1162071, by rfl⟩ : syracuseStep 3098857 = 2324143) B2324143
theorem B35793535 : Blo 904575 35793535 := bstep (se 1 (by rfl) ⟨26845151, by rfl⟩ : syracuseStep 35793535 = 53690303) B53690303
theorem B1357343 : Blo 904575 1357343 := bstep (se 1 (by rfl) ⟨1018007, by rfl⟩ : syracuseStep 1357343 = 2036015) B2036015
theorem B1357367 : Blo 904575 1357367 := bstep (se 1 (by rfl) ⟨1018025, by rfl⟩ : syracuseStep 1357367 = 2036051) B2036051
theorem B1357823 : Blo 904575 1357823 := bstep (se 1 (by rfl) ⟨1018367, by rfl⟩ : syracuseStep 1357823 = 2036735) B2036735
theorem B3054239 : Blo 904575 3054239 := bstep (se 1 (by rfl) ⟨2290679, by rfl⟩ : syracuseStep 3054239 = 4581359) B4581359
theorem B4131809 : Blo 904575 4131809 := bstep (se 2 (by rfl) ⟨1549428, by rfl⟩ : syracuseStep 4131809 = 3098857) B3098857
theorem B904895 : Blo 904575 904895 := bstep (se 1 (by rfl) ⟨678671, by rfl⟩ : syracuseStep 904895 = 1357343) B1357343
theorem B904911 : Blo 904575 904911 := bstep (se 1 (by rfl) ⟨678683, by rfl⟩ : syracuseStep 904911 = 1357367) B1357367
theorem B905215 : Blo 904575 905215 := bstep (se 1 (by rfl) ⟨678911, by rfl⟩ : syracuseStep 905215 = 1357823) B1357823
theorem B2036159 : Blo 904575 2036159 := bstep (se 1 (by rfl) ⟨1527119, by rfl⟩ : syracuseStep 2036159 = 3054239) B3054239
theorem B47724713 : Blo 904575 47724713 := bstep (se 2 (by rfl) ⟨17896767, by rfl⟩ : syracuseStep 47724713 = 35793535) B35793535
theorem B2754539 : Blo 904575 2754539 := bstep (se 1 (by rfl) ⟨2065904, by rfl⟩ : syracuseStep 2754539 = 4131809) B4131809
theorem B1357439 : Blo 904575 1357439 := bstep (se 1 (by rfl) ⟨1018079, by rfl⟩ : syracuseStep 1357439 = 2036159) B2036159
theorem B31816475 : Blo 904575 31816475 := bstep (se 1 (by rfl) ⟨23862356, by rfl⟩ : syracuseStep 31816475 = 47724713) B47724713
theorem B1836359 : Blo 904575 1836359 := bstep (se 1 (by rfl) ⟨1377269, by rfl⟩ : syracuseStep 1836359 = 2754539) B2754539
theorem B21210983 : Blo 904575 21210983 := bstep (se 1 (by rfl) ⟨15908237, by rfl⟩ : syracuseStep 21210983 = 31816475) B31816475
theorem B904959 : Blo 904575 904959 := bstep (se 1 (by rfl) ⟨678719, by rfl⟩ : syracuseStep 904959 = 1357439) B1357439
theorem B14140655 : Blo 904575 14140655 := bstep (se 1 (by rfl) ⟨10605491, by rfl⟩ : syracuseStep 14140655 = 21210983) B21210983
theorem B1224239 : Blo 904575 1224239 := bstep (se 1 (by rfl) ⟨918179, by rfl⟩ : syracuseStep 1224239 = 1836359) B1836359
theorem B3264637 : Blo 904575 3264637 := bstep (se 3 (by rfl) ⟨612119, by rfl⟩ : syracuseStep 3264637 = 1224239) B1224239
theorem B9427103 : Blo 904575 9427103 := bstep (se 1 (by rfl) ⟨7070327, by rfl⟩ : syracuseStep 9427103 = 14140655) B14140655
theorem B6284735 : Blo 904575 6284735 := bstep (se 1 (by rfl) ⟨4713551, by rfl⟩ : syracuseStep 6284735 = 9427103) B9427103
theorem B4352849 : Blo 904575 4352849 := bstep (se 2 (by rfl) ⟨1632318, by rfl⟩ : syracuseStep 4352849 = 3264637) B3264637
theorem B2901899 : Blo 904575 2901899 := bstep (se 1 (by rfl) ⟨2176424, by rfl⟩ : syracuseStep 2901899 = 4352849) B4352849
theorem B4189823 : Blo 904575 4189823 := bstep (se 1 (by rfl) ⟨3142367, by rfl⟩ : syracuseStep 4189823 = 6284735) B6284735
theorem B1934599 : Blo 904575 1934599 := bstep (se 1 (by rfl) ⟨1450949, by rfl⟩ : syracuseStep 1934599 = 2901899) B2901899
theorem B2793215 : Blo 904575 2793215 := bstep (se 1 (by rfl) ⟨2094911, by rfl⟩ : syracuseStep 2793215 = 4189823) B4189823
theorem B1862143 : Blo 904575 1862143 := bstep (se 1 (by rfl) ⟨1396607, by rfl⟩ : syracuseStep 1862143 = 2793215) B2793215
theorem B2579465 : Blo 904575 2579465 := bstep (se 2 (by rfl) ⟨967299, by rfl⟩ : syracuseStep 2579465 = 1934599) B1934599
theorem B9931429 : Blo 904575 9931429 := bstep (se 4 (by rfl) ⟨931071, by rfl⟩ : syracuseStep 9931429 = 1862143) B1862143
theorem B1719643 : Blo 904575 1719643 := bstep (se 1 (by rfl) ⟨1289732, by rfl⟩ : syracuseStep 1719643 = 2579465) B2579465
theorem B52967621 : Blo 904575 52967621 := bstep (se 4 (by rfl) ⟨4965714, by rfl⟩ : syracuseStep 52967621 = 9931429) B9931429
theorem B2292857 : Blo 904575 2292857 := bstep (se 2 (by rfl) ⟨859821, by rfl⟩ : syracuseStep 2292857 = 1719643) B1719643
theorem B35311747 : Blo 904575 35311747 := bstep (se 1 (by rfl) ⟨26483810, by rfl⟩ : syracuseStep 35311747 = 52967621) B52967621
theorem B1528571 : Blo 904575 1528571 := bstep (se 1 (by rfl) ⟨1146428, by rfl⟩ : syracuseStep 1528571 = 2292857) B2292857
theorem B47082329 : Blo 904575 47082329 := bstep (se 2 (by rfl) ⟨17655873, by rfl⟩ : syracuseStep 47082329 = 35311747) B35311747
theorem B1019047 : Blo 904575 1019047 := bstep (se 1 (by rfl) ⟨764285, by rfl⟩ : syracuseStep 1019047 = 1528571) B1528571
theorem B31388219 : Blo 904575 31388219 := bstep (se 1 (by rfl) ⟨23541164, by rfl⟩ : syracuseStep 31388219 = 47082329) B47082329
theorem B1358729 : Blo 904575 1358729 := bstep (se 2 (by rfl) ⟨509523, by rfl⟩ : syracuseStep 1358729 = 1019047) B1019047
theorem B20925479 : Blo 904575 20925479 := bstep (se 1 (by rfl) ⟨15694109, by rfl⟩ : syracuseStep 20925479 = 31388219) B31388219
theorem B905819 : Blo 904575 905819 := bstep (se 1 (by rfl) ⟨679364, by rfl⟩ : syracuseStep 905819 = 1358729) B1358729
theorem B13950319 : Blo 904575 13950319 := bstep (se 1 (by rfl) ⟨10462739, by rfl⟩ : syracuseStep 13950319 = 20925479) B20925479
theorem B18600425 : Blo 904575 18600425 := bstep (se 2 (by rfl) ⟨6975159, by rfl⟩ : syracuseStep 18600425 = 13950319) B13950319
theorem B12400283 : Blo 904575 12400283 := bstep (se 1 (by rfl) ⟨9300212, by rfl⟩ : syracuseStep 12400283 = 18600425) B18600425
theorem B8266855 : Blo 904575 8266855 := bstep (se 1 (by rfl) ⟨6200141, by rfl⟩ : syracuseStep 8266855 = 12400283) B12400283
theorem B11022473 : Blo 904575 11022473 := bstep (se 2 (by rfl) ⟨4133427, by rfl⟩ : syracuseStep 11022473 = 8266855) B8266855
theorem B7348315 : Blo 904575 7348315 := bstep (se 1 (by rfl) ⟨5511236, by rfl⟩ : syracuseStep 7348315 = 11022473) B11022473
theorem B9797753 : Blo 904575 9797753 := bstep (se 2 (by rfl) ⟨3674157, by rfl⟩ : syracuseStep 9797753 = 7348315) B7348315
theorem B6531835 : Blo 904575 6531835 := bstep (se 1 (by rfl) ⟨4898876, by rfl⟩ : syracuseStep 6531835 = 9797753) B9797753
theorem B8709113 : Blo 904575 8709113 := bstep (se 2 (by rfl) ⟨3265917, by rfl⟩ : syracuseStep 8709113 = 6531835) B6531835
theorem B5806075 : Blo 904575 5806075 := bstep (se 1 (by rfl) ⟨4354556, by rfl⟩ : syracuseStep 5806075 = 8709113) B8709113
theorem B7741433 : Blo 904575 7741433 := bstep (se 2 (by rfl) ⟨2903037, by rfl⟩ : syracuseStep 7741433 = 5806075) B5806075
theorem B5160955 : Blo 904575 5160955 := bstep (se 1 (by rfl) ⟨3870716, by rfl⟩ : syracuseStep 5160955 = 7741433) B7741433
theorem B6881273 : Blo 904575 6881273 := bstep (se 2 (by rfl) ⟨2580477, by rfl⟩ : syracuseStep 6881273 = 5160955) B5160955
theorem B4587515 : Blo 904575 4587515 := bstep (se 1 (by rfl) ⟨3440636, by rfl⟩ : syracuseStep 4587515 = 6881273) B6881273
theorem B3058343 : Blo 904575 3058343 := bstep (se 1 (by rfl) ⟨2293757, by rfl⟩ : syracuseStep 3058343 = 4587515) B4587515
theorem B2038895 : Blo 904575 2038895 := bstep (se 1 (by rfl) ⟨1529171, by rfl⟩ : syracuseStep 2038895 = 3058343) B3058343
theorem B1359263 : Blo 904575 1359263 := bstep (se 1 (by rfl) ⟨1019447, by rfl⟩ : syracuseStep 1359263 = 2038895) B2038895
theorem B906175 : Blo 904575 906175 := bstep (se 1 (by rfl) ⟨679631, by rfl⟩ : syracuseStep 906175 = 1359263) B1359263

theorem C0 (j : ℕ) (h1 : 226143 ≤ j) (h2 : j ≤ 226643) : Blo 904575 (4 * j + 3) := by
  interval_cases j
  · exact B904575
  · exact B904579
  · exact B904583
  · exact B904587
  · exact B904591
  · exact B904595
  · exact B904599
  · exact B904603
  · exact B904607
  · exact B904611
  · exact B904615
  · exact B904619
  · exact B904623
  · exact B904627
  · exact B904631
  · exact B904635
  · exact B904639
  · exact B904643
  · exact B904647
  · exact B904651
  · exact B904655
  · exact B904659
  · exact B904663
  · exact B904667
  · exact B904671
  · exact B904675
  · exact B904679
  · exact B904683
  · exact B904687
  · exact B904691
  · exact B904695
  · exact B904699
  · exact B904703
  · exact B904707
  · exact B904711
  · exact B904715
  · exact B904719
  · exact B904723
  · exact B904727
  · exact B904731
  · exact B904735
  · exact B904739
  · exact B904743
  · exact B904747
  · exact B904751
  · exact B904755
  · exact B904759
  · exact B904763
  · exact B904767
  · exact B904771
  · exact B904775
  · exact B904779
  · exact B904783
  · exact B904787
  · exact B904791
  · exact B904795
  · exact B904799
  · exact B904803
  · exact B904807
  · exact B904811
  · exact B904815
  · exact B904819
  · exact B904823
  · exact B904827
  · exact B904831
  · exact B904835
  · exact B904839
  · exact B904843
  · exact B904847
  · exact B904851
  · exact B904855
  · exact B904859
  · exact B904863
  · exact B904867
  · exact B904871
  · exact B904875
  · exact B904879
  · exact B904883
  · exact B904887
  · exact B904891
  · exact B904895
  · exact B904899
  · exact B904903
  · exact B904907
  · exact B904911
  · exact B904915
  · exact B904919
  · exact B904923
  · exact B904927
  · exact B904931
  · exact B904935
  · exact B904939
  · exact B904943
  · exact B904947
  · exact B904951
  · exact B904955
  · exact B904959
  · exact B904963
  · exact B904967
  · exact B904971
  · exact B904975
  · exact B904979
  · exact B904983
  · exact B904987
  · exact B904991
  · exact B904995
  · exact B904999
  · exact B905003
  · exact B905007
  · exact B905011
  · exact B905015
  · exact B905019
  · exact B905023
  · exact B905027
  · exact B905031
  · exact B905035
  · exact B905039
  · exact B905043
  · exact B905047
  · exact B905051
  · exact B905055
  · exact B905059
  · exact B905063
  · exact B905067
  · exact B905071
  · exact B905075
  · exact B905079
  · exact B905083
  · exact B905087
  · exact B905091
  · exact B905095
  · exact B905099
  · exact B905103
  · exact B905107
  · exact B905111
  · exact B905115
  · exact B905119
  · exact B905123
  · exact B905127
  · exact B905131
  · exact B905135
  · exact B905139
  · exact B905143
  · exact B905147
  · exact B905151
  · exact B905155
  · exact B905159
  · exact B905163
  · exact B905167
  · exact B905171
  · exact B905175
  · exact B905179
  · exact B905183
  · exact B905187
  · exact B905191
  · exact B905195
  · exact B905199
  · exact B905203
  · exact B905207
  · exact B905211
  · exact B905215
  · exact B905219
  · exact B905223
  · exact B905227
  · exact B905231
  · exact B905235
  · exact B905239
  · exact B905243
  · exact B905247
  · exact B905251
  · exact B905255
  · exact B905259
  · exact B905263
  · exact B905267
  · exact B905271
  · exact B905275
  · exact B905279
  · exact B905283
  · exact B905287
  · exact B905291
  · exact B905295
  · exact B905299
  · exact B905303
  · exact B905307
  · exact B905311
  · exact B905315
  · exact B905319
  · exact B905323
  · exact B905327
  · exact B905331
  · exact B905335
  · exact B905339
  · exact B905343
  · exact B905347
  · exact B905351
  · exact B905355
  · exact B905359
  · exact B905363
  · exact B905367
  · exact B905371
  · exact B905375
  · exact B905379
  · exact B905383
  · exact B905387
  · exact B905391
  · exact B905395
  · exact B905399
  · exact B905403
  · exact B905407
  · exact B905411
  · exact B905415
  · exact B905419
  · exact B905423
  · exact B905427
  · exact B905431
  · exact B905435
  · exact B905439
  · exact B905443
  · exact B905447
  · exact B905451
  · exact B905455
  · exact B905459
  · exact B905463
  · exact B905467
  · exact B905471
  · exact B905475
  · exact B905479
  · exact B905483
  · exact B905487
  · exact B905491
  · exact B905495
  · exact B905499
  · exact B905503
  · exact B905507
  · exact B905511
  · exact B905515
  · exact B905519
  · exact B905523
  · exact B905527
  · exact B905531
  · exact B905535
  · exact B905539
  · exact B905543
  · exact B905547
  · exact B905551
  · exact B905555
  · exact B905559
  · exact B905563
  · exact B905567
  · exact B905571
  · exact B905575
  · exact B905579
  · exact B905583
  · exact B905587
  · exact B905591
  · exact B905595
  · exact B905599
  · exact B905603
  · exact B905607
  · exact B905611
  · exact B905615
  · exact B905619
  · exact B905623
  · exact B905627
  · exact B905631
  · exact B905635
  · exact B905639
  · exact B905643
  · exact B905647
  · exact B905651
  · exact B905655
  · exact B905659
  · exact B905663
  · exact B905667
  · exact B905671
  · exact B905675
  · exact B905679
  · exact B905683
  · exact B905687
  · exact B905691
  · exact B905695
  · exact B905699
  · exact B905703
  · exact B905707
  · exact B905711
  · exact B905715
  · exact B905719
  · exact B905723
  · exact B905727
  · exact B905731
  · exact B905735
  · exact B905739
  · exact B905743
  · exact B905747
  · exact B905751
  · exact B905755
  · exact B905759
  · exact B905763
  · exact B905767
  · exact B905771
  · exact B905775
  · exact B905779
  · exact B905783
  · exact B905787
  · exact B905791
  · exact B905795
  · exact B905799
  · exact B905803
  · exact B905807
  · exact B905811
  · exact B905815
  · exact B905819
  · exact B905823
  · exact B905827
  · exact B905831
  · exact B905835
  · exact B905839
  · exact B905843
  · exact B905847
  · exact B905851
  · exact B905855
  · exact B905859
  · exact B905863
  · exact B905867
  · exact B905871
  · exact B905875
  · exact B905879
  · exact B905883
  · exact B905887
  · exact B905891
  · exact B905895
  · exact B905899
  · exact B905903
  · exact B905907
  · exact B905911
  · exact B905915
  · exact B905919
  · exact B905923
  · exact B905927
  · exact B905931
  · exact B905935
  · exact B905939
  · exact B905943
  · exact B905947
  · exact B905951
  · exact B905955
  · exact B905959
  · exact B905963
  · exact B905967
  · exact B905971
  · exact B905975
  · exact B905979
  · exact B905983
  · exact B905987
  · exact B905991
  · exact B905995
  · exact B905999
  · exact B906003
  · exact B906007
  · exact B906011
  · exact B906015
  · exact B906019
  · exact B906023
  · exact B906027
  · exact B906031
  · exact B906035
  · exact B906039
  · exact B906043
  · exact B906047
  · exact B906051
  · exact B906055
  · exact B906059
  · exact B906063
  · exact B906067
  · exact B906071
  · exact B906075
  · exact B906079
  · exact B906083
  · exact B906087
  · exact B906091
  · exact B906095
  · exact B906099
  · exact B906103
  · exact B906107
  · exact B906111
  · exact B906115
  · exact B906119
  · exact B906123
  · exact B906127
  · exact B906131
  · exact B906135
  · exact B906139
  · exact B906143
  · exact B906147
  · exact B906151
  · exact B906155
  · exact B906159
  · exact B906163
  · exact B906167
  · exact B906171
  · exact B906175
  · exact B906179
  · exact B906183
  · exact B906187
  · exact B906191
  · exact B906195
  · exact B906199
  · exact B906203
  · exact B906207
  · exact B906211
  · exact B906215
  · exact B906219
  · exact B906223
  · exact B906227
  · exact B906231
  · exact B906235
  · exact B906239
  · exact B906243
  · exact B906247
  · exact B906251
  · exact B906255
  · exact B906259
  · exact B906263
  · exact B906267
  · exact B906271
  · exact B906275
  · exact B906279
  · exact B906283
  · exact B906287
  · exact B906291
  · exact B906295
  · exact B906299
  · exact B906303
  · exact B906307
  · exact B906311
  · exact B906315
  · exact B906319
  · exact B906323
  · exact B906327
  · exact B906331
  · exact B906335
  · exact B906339
  · exact B906343
  · exact B906347
  · exact B906351
  · exact B906355
  · exact B906359
  · exact B906363
  · exact B906367
  · exact B906371
  · exact B906375
  · exact B906379
  · exact B906383
  · exact B906387
  · exact B906391
  · exact B906395
  · exact B906399
  · exact B906403
  · exact B906407
  · exact B906411
  · exact B906415
  · exact B906419
  · exact B906423
  · exact B906427
  · exact B906431
  · exact B906435
  · exact B906439
  · exact B906443
  · exact B906447
  · exact B906451
  · exact B906455
  · exact B906459
  · exact B906463
  · exact B906467
  · exact B906471
  · exact B906475
  · exact B906479
  · exact B906483
  · exact B906487
  · exact B906491
  · exact B906495
  · exact B906499
  · exact B906503
  · exact B906507
  · exact B906511
  · exact B906515
  · exact B906519
  · exact B906523
  · exact B906527
  · exact B906531
  · exact B906535
  · exact B906539
  · exact B906543
  · exact B906547
  · exact B906551
  · exact B906555
  · exact B906559
  · exact B906563
  · exact B906567
  · exact B906571
  · exact B906575

theorem solution (m : ℕ) (hlo : 904575 ≤ m) (hhi : m ≤ 906575) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 226143 ≤ j := by omega
    have hj2 : j ≤ 226643 := by omega
    have hb : Blo 904575 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
