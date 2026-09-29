-- Prove2me | solution 1 for syracuse_descends_range_842353_846353
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:53.074707+00:00
-- url     : https://prove2.me/submissions/8efa1f30-d161-4820-b728-b50706ce1b88

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


theorem B2850821 : Blo 842353 2850821 := bbase (se 4 (by rfl) ⟨267264, by rfl⟩ : syracuseStep 2850821 = 534529) (by norm_num)
theorem B1900565 : Blo 842353 1900565 := bbase (se 6 (by rfl) ⟨44544, by rfl⟩ : syracuseStep 1900565 = 89089) (by norm_num)
theorem B1605653 : Blo 842353 1605653 := bbase (se 6 (by rfl) ⟨37632, by rfl⟩ : syracuseStep 1605653 = 75265) (by norm_num)
theorem B950305 : Blo 842353 950305 := bbase (se 2 (by rfl) ⟨356364, by rfl⟩ : syracuseStep 950305 = 712729) (by norm_num)
theorem B950341 : Blo 842353 950341 := bbase (se 4 (by rfl) ⟨89094, by rfl⟩ : syracuseStep 950341 = 178189) (by norm_num)
theorem B1900637 : Blo 842353 1900637 := bbase (se 3 (by rfl) ⟨356369, by rfl⟩ : syracuseStep 1900637 = 712739) (by norm_num)
theorem B950377 : Blo 842353 950377 := bbase (se 2 (by rfl) ⟨356391, by rfl⟩ : syracuseStep 950377 = 712783) (by norm_num)
theorem B1081469 : Blo 842353 1081469 := bbase (se 3 (by rfl) ⟨202775, by rfl⟩ : syracuseStep 1081469 = 405551) (by norm_num)
theorem B3211397 : Blo 842353 3211397 := bbase (se 4 (by rfl) ⟨301068, by rfl⟩ : syracuseStep 3211397 = 602137) (by norm_num)
theorem B950413 : Blo 842353 950413 := bbase (se 3 (by rfl) ⟨178202, by rfl⟩ : syracuseStep 950413 = 356405) (by norm_num)
theorem B1900709 : Blo 842353 1900709 := bbase (se 4 (by rfl) ⟨178191, by rfl⟩ : syracuseStep 1900709 = 356383) (by norm_num)
theorem B950449 : Blo 842353 950449 := bbase (se 2 (by rfl) ⟨356418, by rfl⟩ : syracuseStep 950449 = 712837) (by norm_num)
theorem B950485 : Blo 842353 950485 := bbase (se 7 (by rfl) ⟨11138, by rfl⟩ : syracuseStep 950485 = 22277) (by norm_num)
theorem B1900781 : Blo 842353 1900781 := bbase (se 3 (by rfl) ⟨356396, by rfl⟩ : syracuseStep 1900781 = 712793) (by norm_num)
theorem B4817141 : Blo 842353 4817141 := bbase (se 5 (by rfl) ⟨225803, by rfl⟩ : syracuseStep 4817141 = 451607) (by norm_num)
theorem B950521 : Blo 842353 950521 := bbase (se 2 (by rfl) ⟨356445, by rfl⟩ : syracuseStep 950521 = 712891) (by norm_num)
theorem B950557 : Blo 842353 950557 := bbase (se 3 (by rfl) ⟨178229, by rfl⟩ : syracuseStep 950557 = 356459) (by norm_num)
theorem B1802533 : Blo 842353 1802533 := bbase (se 4 (by rfl) ⟨168987, by rfl⟩ : syracuseStep 1802533 = 337975) (by norm_num)
theorem B1900853 : Blo 842353 1900853 := bbase (se 5 (by rfl) ⟨89102, by rfl⟩ : syracuseStep 1900853 = 178205) (by norm_num)
theorem B2031925 : Blo 842353 2031925 := bbase (se 5 (by rfl) ⟨95246, by rfl⟩ : syracuseStep 2031925 = 190493) (by norm_num)
theorem B950593 : Blo 842353 950593 := bbase (se 2 (by rfl) ⟨356472, by rfl⟩ : syracuseStep 950593 = 712945) (by norm_num)
theorem B950629 : Blo 842353 950629 := bbase (se 4 (by rfl) ⟨89121, by rfl⟩ : syracuseStep 950629 = 178243) (by norm_num)
theorem B1900925 : Blo 842353 1900925 := bbase (se 3 (by rfl) ⟨356423, by rfl⟩ : syracuseStep 1900925 = 712847) (by norm_num)
theorem B950665 : Blo 842353 950665 := bbase (se 2 (by rfl) ⟨356499, by rfl⟩ : syracuseStep 950665 = 712999) (by norm_num)
theorem B950701 : Blo 842353 950701 := bbase (se 3 (by rfl) ⟨178256, by rfl⟩ : syracuseStep 950701 = 356513) (by norm_num)
theorem B2851253 : Blo 842353 2851253 := bbase (se 5 (by rfl) ⟨133652, by rfl⟩ : syracuseStep 2851253 = 267305) (by norm_num)
theorem B1900997 : Blo 842353 1900997 := bbase (se 4 (by rfl) ⟨178218, by rfl⟩ : syracuseStep 1900997 = 356437) (by norm_num)
theorem B950737 : Blo 842353 950737 := bbase (se 2 (by rfl) ⟨356526, by rfl⟩ : syracuseStep 950737 = 713053) (by norm_num)
theorem B1081817 : Blo 842353 1081817 := bbase (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) (by norm_num)
theorem B950773 : Blo 842353 950773 := bbase (se 5 (by rfl) ⟨44567, by rfl⟩ : syracuseStep 950773 = 89135) (by norm_num)
theorem B1901069 : Blo 842353 1901069 := bbase (se 3 (by rfl) ⟨356450, by rfl⟩ : syracuseStep 1901069 = 712901) (by norm_num)
theorem B950809 : Blo 842353 950809 := bbase (se 2 (by rfl) ⟨356553, by rfl⟩ : syracuseStep 950809 = 713107) (by norm_num)
theorem B2163245 : Blo 842353 2163245 := bbase (se 3 (by rfl) ⟨405608, by rfl⟩ : syracuseStep 2163245 = 811217) (by norm_num)
theorem B950845 : Blo 842353 950845 := bbase (se 3 (by rfl) ⟨178283, by rfl⟩ : syracuseStep 950845 = 356567) (by norm_num)
theorem B1901141 : Blo 842353 1901141 := bbase (se 8 (by rfl) ⟨11139, by rfl⟩ : syracuseStep 1901141 = 22279) (by norm_num)
theorem B950881 : Blo 842353 950881 := bbase (se 2 (by rfl) ⟨356580, by rfl⟩ : syracuseStep 950881 = 713161) (by norm_num)
theorem B950917 : Blo 842353 950917 := bbase (se 4 (by rfl) ⟨89148, by rfl⟩ : syracuseStep 950917 = 178297) (by norm_num)
theorem B1901213 : Blo 842353 1901213 := bbase (se 3 (by rfl) ⟨356477, by rfl⟩ : syracuseStep 1901213 = 712955) (by norm_num)
theorem B950953 : Blo 842353 950953 := bbase (se 2 (by rfl) ⟨356607, by rfl⟩ : syracuseStep 950953 = 713215) (by norm_num)
theorem B4063925 : Blo 842353 4063925 := bbase (se 5 (by rfl) ⟨190496, by rfl⟩ : syracuseStep 4063925 = 380993) (by norm_num)
theorem B950989 : Blo 842353 950989 := bbase (se 3 (by rfl) ⟨178310, by rfl⟩ : syracuseStep 950989 = 356621) (by norm_num)
theorem B1901285 : Blo 842353 1901285 := bbase (se 4 (by rfl) ⟨178245, by rfl⟩ : syracuseStep 1901285 = 356491) (by norm_num)
theorem B951025 : Blo 842353 951025 := bbase (se 2 (by rfl) ⟨356634, by rfl⟩ : syracuseStep 951025 = 713269) (by norm_num)
theorem B1606405 : Blo 842353 1606405 := bbase (se 4 (by rfl) ⟨150600, by rfl⟩ : syracuseStep 1606405 = 301201) (by norm_num)
theorem B951061 : Blo 842353 951061 := bbase (se 6 (by rfl) ⟨22290, by rfl⟩ : syracuseStep 951061 = 44581) (by norm_num)
theorem B1901357 : Blo 842353 1901357 := bbase (se 3 (by rfl) ⟨356504, by rfl⟩ : syracuseStep 1901357 = 713009) (by norm_num)
theorem B951097 : Blo 842353 951097 := bbase (se 2 (by rfl) ⟨356661, by rfl⟩ : syracuseStep 951097 = 713323) (by norm_num)
theorem B2032445 : Blo 842353 2032445 := bbase (se 3 (by rfl) ⟨381083, by rfl⟩ : syracuseStep 2032445 = 762167) (by norm_num)
theorem B951133 : Blo 842353 951133 := bbase (se 3 (by rfl) ⟨178337, by rfl⟩ : syracuseStep 951133 = 356675) (by norm_num)
theorem B2851685 : Blo 842353 2851685 := bbase (se 4 (by rfl) ⟨267345, by rfl⟩ : syracuseStep 2851685 = 534691) (by norm_num)
theorem B1901429 : Blo 842353 1901429 := bbase (se 5 (by rfl) ⟨89129, by rfl⟩ : syracuseStep 1901429 = 178259) (by norm_num)
theorem B951169 : Blo 842353 951169 := bbase (se 2 (by rfl) ⟨356688, by rfl⟩ : syracuseStep 951169 = 713377) (by norm_num)
theorem B1606549 : Blo 842353 1606549 := bbase (se 6 (by rfl) ⟨37653, by rfl⟩ : syracuseStep 1606549 = 75307) (by norm_num)
theorem B951205 : Blo 842353 951205 := bbase (se 4 (by rfl) ⟨89175, by rfl⟩ : syracuseStep 951205 = 178351) (by norm_num)
theorem B1901501 : Blo 842353 1901501 := bbase (se 3 (by rfl) ⟨356531, by rfl⟩ : syracuseStep 1901501 = 713063) (by norm_num)
theorem B951241 : Blo 842353 951241 := bbase (se 2 (by rfl) ⟨356715, by rfl⟩ : syracuseStep 951241 = 713431) (by norm_num)
theorem B951277 : Blo 842353 951277 := bbase (se 3 (by rfl) ⟨178364, by rfl⟩ : syracuseStep 951277 = 356729) (by norm_num)
theorem B1901573 : Blo 842353 1901573 := bbase (se 4 (by rfl) ⟨178272, by rfl⟩ : syracuseStep 1901573 = 356545) (by norm_num)
theorem B951313 : Blo 842353 951313 := bbase (se 2 (by rfl) ⟨356742, by rfl⟩ : syracuseStep 951313 = 713485) (by norm_num)
theorem B951349 : Blo 842353 951349 := bbase (se 5 (by rfl) ⟨44594, by rfl⟩ : syracuseStep 951349 = 89189) (by norm_num)
theorem B1606709 : Blo 842353 1606709 := bbase (se 5 (by rfl) ⟨75314, by rfl⟩ : syracuseStep 1606709 = 150629) (by norm_num)
theorem B1901645 : Blo 842353 1901645 := bbase (se 3 (by rfl) ⟨356558, by rfl⟩ : syracuseStep 1901645 = 713117) (by norm_num)
theorem B951385 : Blo 842353 951385 := bbase (se 2 (by rfl) ⟨356769, by rfl⟩ : syracuseStep 951385 = 713539) (by norm_num)
theorem B951421 : Blo 842353 951421 := bbase (se 3 (by rfl) ⟨178391, by rfl⟩ : syracuseStep 951421 = 356783) (by norm_num)
theorem B1901717 : Blo 842353 1901717 := bbase (se 6 (by rfl) ⟨44571, by rfl⟩ : syracuseStep 1901717 = 89143) (by norm_num)
theorem B1803421 : Blo 842353 1803421 := bbase (se 3 (by rfl) ⟨338141, by rfl⟩ : syracuseStep 1803421 = 676283) (by norm_num)
theorem B951457 : Blo 842353 951457 := bbase (se 2 (by rfl) ⟨356796, by rfl⟩ : syracuseStep 951457 = 713593) (by norm_num)
theorem B2032829 : Blo 842353 2032829 := bbase (se 3 (by rfl) ⟨381155, by rfl⟩ : syracuseStep 2032829 = 762311) (by norm_num)
theorem B951493 : Blo 842353 951493 := bbase (se 4 (by rfl) ⟨89202, by rfl⟩ : syracuseStep 951493 = 178405) (by norm_num)
theorem B1901789 : Blo 842353 1901789 := bbase (se 3 (by rfl) ⟨356585, by rfl⟩ : syracuseStep 1901789 = 713171) (by norm_num)
theorem B951529 : Blo 842353 951529 := bbase (se 2 (by rfl) ⟨356823, by rfl⟩ : syracuseStep 951529 = 713647) (by norm_num)
theorem B2032877 : Blo 842353 2032877 := bbase (se 3 (by rfl) ⟨381164, by rfl⟩ : syracuseStep 2032877 = 762329) (by norm_num)
theorem B2032885 : Blo 842353 2032885 := bbase (se 5 (by rfl) ⟨95291, by rfl⟩ : syracuseStep 2032885 = 190583) (by norm_num)
theorem B951565 : Blo 842353 951565 := bbase (se 3 (by rfl) ⟨178418, by rfl⟩ : syracuseStep 951565 = 356837) (by norm_num)
theorem B1803541 : Blo 842353 1803541 := bbase (se 6 (by rfl) ⟨42270, by rfl⟩ : syracuseStep 1803541 = 84541) (by norm_num)
theorem B2852117 : Blo 842353 2852117 := bbase (se 6 (by rfl) ⟨66846, by rfl⟩ : syracuseStep 2852117 = 133693) (by norm_num)
theorem B1901861 : Blo 842353 1901861 := bbase (se 4 (by rfl) ⟨178299, by rfl⟩ : syracuseStep 1901861 = 356599) (by norm_num)
theorem B3212581 : Blo 842353 3212581 := bbase (se 4 (by rfl) ⟨301179, by rfl⟩ : syracuseStep 3212581 = 602359) (by norm_num)
theorem B951601 : Blo 842353 951601 := bbase (se 2 (by rfl) ⟨356850, by rfl⟩ : syracuseStep 951601 = 713701) (by norm_num)
theorem B951637 : Blo 842353 951637 := bbase (se 12 (by rfl) ⟨348, by rfl⟩ : syracuseStep 951637 = 697) (by norm_num)
theorem B1901933 : Blo 842353 1901933 := bbase (se 3 (by rfl) ⟨356612, by rfl⟩ : syracuseStep 1901933 = 713225) (by norm_num)
theorem B951673 : Blo 842353 951673 := bbase (se 2 (by rfl) ⟨356877, by rfl⟩ : syracuseStep 951673 = 713755) (by norm_num)
theorem B4818325 : Blo 842353 4818325 := bbase (se 6 (by rfl) ⟨112929, by rfl⟩ : syracuseStep 4818325 = 225859) (by norm_num)
theorem B951709 : Blo 842353 951709 := bbase (se 3 (by rfl) ⟨178445, by rfl⟩ : syracuseStep 951709 = 356891) (by norm_num)
theorem B1902005 : Blo 842353 1902005 := bbase (se 5 (by rfl) ⟨89156, by rfl⟩ : syracuseStep 1902005 = 178313) (by norm_num)
theorem B951745 : Blo 842353 951745 := bbase (se 2 (by rfl) ⟨356904, by rfl⟩ : syracuseStep 951745 = 713809) (by norm_num)
theorem B3900869 : Blo 842353 3900869 := bbase (se 4 (by rfl) ⟨365706, by rfl⟩ : syracuseStep 3900869 = 731413) (by norm_num)
theorem B951781 : Blo 842353 951781 := bbase (se 4 (by rfl) ⟨89229, by rfl⟩ : syracuseStep 951781 = 178459) (by norm_num)
theorem B1902077 : Blo 842353 1902077 := bbase (se 3 (by rfl) ⟨356639, by rfl⟩ : syracuseStep 1902077 = 713279) (by norm_num)
theorem B951817 : Blo 842353 951817 := bbase (se 2 (by rfl) ⟨356931, by rfl⟩ : syracuseStep 951817 = 713863) (by norm_num)
theorem B1803797 : Blo 842353 1803797 := bbase (se 6 (by rfl) ⟨42276, by rfl⟩ : syracuseStep 1803797 = 84553) (by norm_num)
theorem B951853 : Blo 842353 951853 := bbase (se 3 (by rfl) ⟨178472, by rfl⟩ : syracuseStep 951853 = 356945) (by norm_num)
theorem B1902149 : Blo 842353 1902149 := bbase (se 4 (by rfl) ⟨178326, by rfl⟩ : syracuseStep 1902149 = 356653) (by norm_num)
theorem B951889 : Blo 842353 951889 := bbase (se 2 (by rfl) ⟨356958, by rfl⟩ : syracuseStep 951889 = 713917) (by norm_num)
theorem B3212885 : Blo 842353 3212885 := bbase (se 8 (by rfl) ⟨18825, by rfl⟩ : syracuseStep 3212885 = 37651) (by norm_num)
theorem B1082981 : Blo 842353 1082981 := bbase (se 4 (by rfl) ⟨101529, by rfl⟩ : syracuseStep 1082981 = 203059) (by norm_num)
theorem B951925 : Blo 842353 951925 := bbase (se 5 (by rfl) ⟨44621, by rfl⟩ : syracuseStep 951925 = 89243) (by norm_num)
theorem B1902221 : Blo 842353 1902221 := bbase (se 3 (by rfl) ⟨356666, by rfl⟩ : syracuseStep 1902221 = 713333) (by norm_num)
theorem B951961 : Blo 842353 951961 := bbase (se 2 (by rfl) ⟨356985, by rfl⟩ : syracuseStep 951961 = 713971) (by norm_num)
theorem B951997 : Blo 842353 951997 := bbase (se 3 (by rfl) ⟨178499, by rfl⟩ : syracuseStep 951997 = 356999) (by norm_num)
theorem B2852549 : Blo 842353 2852549 := bbase (se 4 (by rfl) ⟨267426, by rfl⟩ : syracuseStep 2852549 = 534853) (by norm_num)
theorem B3049157 : Blo 842353 3049157 := bbase (se 4 (by rfl) ⟨285858, by rfl⟩ : syracuseStep 3049157 = 571717) (by norm_num)
theorem B1902293 : Blo 842353 1902293 := bbase (se 7 (by rfl) ⟨22292, by rfl⟩ : syracuseStep 1902293 = 44585) (by norm_num)
theorem B952033 : Blo 842353 952033 := bbase (se 2 (by rfl) ⟨357012, by rfl⟩ : syracuseStep 952033 = 714025) (by norm_num)
theorem B952069 : Blo 842353 952069 := bbase (se 4 (by rfl) ⟨89256, by rfl⟩ : syracuseStep 952069 = 178513) (by norm_num)
theorem B1902365 : Blo 842353 1902365 := bbase (se 3 (by rfl) ⟨356693, by rfl⟩ : syracuseStep 1902365 = 713387) (by norm_num)
theorem B952105 : Blo 842353 952105 := bbase (se 2 (by rfl) ⟨357039, by rfl⟩ : syracuseStep 952105 = 714079) (by norm_num)
theorem B1083193 : Blo 842353 1083193 := bbase (se 2 (by rfl) ⟨406197, by rfl⟩ : syracuseStep 1083193 = 812395) (by norm_num)
theorem B952141 : Blo 842353 952141 := bbase (se 3 (by rfl) ⟨178526, by rfl⟩ : syracuseStep 952141 = 357053) (by norm_num)
theorem B1902437 : Blo 842353 1902437 := bbase (se 4 (by rfl) ⟨178353, by rfl⟩ : syracuseStep 1902437 = 356707) (by norm_num)
theorem B3901301 : Blo 842353 3901301 := bbase (se 5 (by rfl) ⟨182873, by rfl⟩ : syracuseStep 3901301 = 365747) (by norm_num)
theorem B1902509 : Blo 842353 1902509 := bbase (se 3 (by rfl) ⟨356720, by rfl⟩ : syracuseStep 1902509 = 713441) (by norm_num)
theorem B1902581 : Blo 842353 1902581 := bbase (se 5 (by rfl) ⟨89183, by rfl⟩ : syracuseStep 1902581 = 178367) (by norm_num)
theorem B1902653 : Blo 842353 1902653 := bbase (se 3 (by rfl) ⟨356747, by rfl⟩ : syracuseStep 1902653 = 713495) (by norm_num)
theorem B4065349 : Blo 842353 4065349 := bbase (se 4 (by rfl) ⟨381126, by rfl⟩ : syracuseStep 4065349 = 762253) (by norm_num)
theorem B2852981 : Blo 842353 2852981 := bbase (se 5 (by rfl) ⟨133733, by rfl⟩ : syracuseStep 2852981 = 267467) (by norm_num)
theorem B3049589 : Blo 842353 3049589 := bbase (se 5 (by rfl) ⟨142949, by rfl⟩ : syracuseStep 3049589 = 285899) (by norm_num)
theorem B1902725 : Blo 842353 1902725 := bbase (se 4 (by rfl) ⟨178380, by rfl⟩ : syracuseStep 1902725 = 356761) (by norm_num)
theorem B1902797 : Blo 842353 1902797 := bbase (se 3 (by rfl) ⟨356774, by rfl⟩ : syracuseStep 1902797 = 713549) (by norm_num)
theorem B1902869 : Blo 842353 1902869 := bbase (se 6 (by rfl) ⟨44598, by rfl⟩ : syracuseStep 1902869 = 89197) (by norm_num)
theorem B1902941 : Blo 842353 1902941 := bbase (se 3 (by rfl) ⟨356801, by rfl⟩ : syracuseStep 1902941 = 713603) (by norm_num)
theorem B2132365 : Blo 842353 2132365 := bbase (se 3 (by rfl) ⟨399818, by rfl⟩ : syracuseStep 2132365 = 799637) (by norm_num)
theorem B1804685 : Blo 842353 1804685 := bbase (se 3 (by rfl) ⟨338378, by rfl⟩ : syracuseStep 1804685 = 676757) (by norm_num)
theorem B1903013 : Blo 842353 1903013 := bbase (se 4 (by rfl) ⟨178407, by rfl⟩ : syracuseStep 1903013 = 356815) (by norm_num)
theorem B1903085 : Blo 842353 1903085 := bbase (se 3 (by rfl) ⟨356828, by rfl⟩ : syracuseStep 1903085 = 713657) (by norm_num)
theorem B4327925 : Blo 842353 4327925 := bbase (se 5 (by rfl) ⟨202871, by rfl⟩ : syracuseStep 4327925 = 405743) (by norm_num)
theorem B2132477 : Blo 842353 2132477 := bbase (se 3 (by rfl) ⟨399839, by rfl⟩ : syracuseStep 2132477 = 799679) (by norm_num)
theorem B2853413 : Blo 842353 2853413 := bbase (se 4 (by rfl) ⟨267507, by rfl⟩ : syracuseStep 2853413 = 535015) (by norm_num)
theorem B1903157 : Blo 842353 1903157 := bbase (se 5 (by rfl) ⟨89210, by rfl⟩ : syracuseStep 1903157 = 178421) (by norm_num)
theorem B1804925 : Blo 842353 1804925 := bbase (se 3 (by rfl) ⟨338423, by rfl⟩ : syracuseStep 1804925 = 676847) (by norm_num)
theorem B1903229 : Blo 842353 1903229 := bbase (se 3 (by rfl) ⟨356855, by rfl⟩ : syracuseStep 1903229 = 713711) (by norm_num)
theorem B854669 : Blo 842353 854669 := bbase (se 3 (by rfl) ⟨160250, by rfl⟩ : syracuseStep 854669 = 320501) (by norm_num)
theorem B2132669 : Blo 842353 2132669 := bbase (se 3 (by rfl) ⟨399875, by rfl⟩ : syracuseStep 2132669 = 799751) (by norm_num)
theorem B1903301 : Blo 842353 1903301 := bbase (se 4 (by rfl) ⟨178434, by rfl⟩ : syracuseStep 1903301 = 356869) (by norm_num)
theorem B6163157 : Blo 842353 6163157 := bbase (se 7 (by rfl) ⟨72224, by rfl⟩ : syracuseStep 6163157 = 144449) (by norm_num)
theorem B3607253 : Blo 842353 3607253 := bbase (se 7 (by rfl) ⟨42272, by rfl⟩ : syracuseStep 3607253 = 84545) (by norm_num)
theorem B1084153 : Blo 842353 1084153 := bbase (se 2 (by rfl) ⟨406557, by rfl⟩ : syracuseStep 1084153 = 813115) (by norm_num)
theorem B1903373 : Blo 842353 1903373 := bbase (se 3 (by rfl) ⟨356882, by rfl⟩ : syracuseStep 1903373 = 713765) (by norm_num)
theorem B3083093 : Blo 842353 3083093 := bbase (se 9 (by rfl) ⟨9032, by rfl⟩ : syracuseStep 3083093 = 18065) (by norm_num)
theorem B1903445 : Blo 842353 1903445 := bbase (se 9 (by rfl) ⟨5576, by rfl⟩ : syracuseStep 1903445 = 11153) (by norm_num)
theorem B1903517 : Blo 842353 1903517 := bbase (se 3 (by rfl) ⟨356909, by rfl⟩ : syracuseStep 1903517 = 713819) (by norm_num)
theorem B2853845 : Blo 842353 2853845 := bbase (se 7 (by rfl) ⟨33443, by rfl⟩ : syracuseStep 2853845 = 66887) (by norm_num)
theorem B1084385 : Blo 842353 1084385 := bbase (se 2 (by rfl) ⟨406644, by rfl⟩ : syracuseStep 1084385 = 813289) (by norm_num)
theorem B1903589 : Blo 842353 1903589 := bbase (se 4 (by rfl) ⟨178461, by rfl⟩ : syracuseStep 1903589 = 356923) (by norm_num)
theorem B1281029 : Blo 842353 1281029 := bbase (se 4 (by rfl) ⟨120096, by rfl⟩ : syracuseStep 1281029 = 240193) (by norm_num)
theorem B2133013 : Blo 842353 2133013 := bbase (se 6 (by rfl) ⟨49992, by rfl⟩ : syracuseStep 2133013 = 99985) (by norm_num)
theorem B1903661 : Blo 842353 1903661 := bbase (se 3 (by rfl) ⟨356936, by rfl⟩ : syracuseStep 1903661 = 713873) (by norm_num)
theorem B14421077 : Blo 842353 14421077 := bbase (se 8 (by rfl) ⟨84498, by rfl⟩ : syracuseStep 14421077 = 168997) (by norm_num)
theorem B1805429 : Blo 842353 1805429 := bbase (se 5 (by rfl) ⟨84629, by rfl⟩ : syracuseStep 1805429 = 169259) (by norm_num)
theorem B1903733 : Blo 842353 1903733 := bbase (se 5 (by rfl) ⟨89237, by rfl⟩ : syracuseStep 1903733 = 178475) (by norm_num)
theorem B1805437 : Blo 842353 1805437 := bbase (se 3 (by rfl) ⟨338519, by rfl⟩ : syracuseStep 1805437 = 677039) (by norm_num)
theorem B2133125 : Blo 842353 2133125 := bbase (se 4 (by rfl) ⟨199980, by rfl⟩ : syracuseStep 2133125 = 399961) (by norm_num)
theorem B1903805 : Blo 842353 1903805 := bbase (se 3 (by rfl) ⟨356963, by rfl⟩ : syracuseStep 1903805 = 713927) (by norm_num)
theorem B1903877 : Blo 842353 1903877 := bbase (se 4 (by rfl) ⟨178488, by rfl⟩ : syracuseStep 1903877 = 356977) (by norm_num)
theorem B855317 : Blo 842353 855317 := bbase (se 6 (by rfl) ⟨20046, by rfl⟩ : syracuseStep 855317 = 40093) (by norm_num)
theorem B2133317 : Blo 842353 2133317 := bbase (se 4 (by rfl) ⟨199998, by rfl⟩ : syracuseStep 2133317 = 399997) (by norm_num)
theorem B1903949 : Blo 842353 1903949 := bbase (se 3 (by rfl) ⟨356990, by rfl⟩ : syracuseStep 1903949 = 713981) (by norm_num)
theorem B2854277 : Blo 842353 2854277 := bbase (se 4 (by rfl) ⟨267588, by rfl⟩ : syracuseStep 2854277 = 535177) (by norm_num)
theorem B1904021 : Blo 842353 1904021 := bbase (se 6 (by rfl) ⟨44625, by rfl⟩ : syracuseStep 1904021 = 89251) (by norm_num)
theorem B1904093 : Blo 842353 1904093 := bbase (se 3 (by rfl) ⟨357017, by rfl⟩ : syracuseStep 1904093 = 714035) (by norm_num)
theorem B1904165 : Blo 842353 1904165 := bbase (se 4 (by rfl) ⟨178515, by rfl⟩ : syracuseStep 1904165 = 357031) (by norm_num)
theorem B1904237 : Blo 842353 1904237 := bbase (se 3 (by rfl) ⟨357044, by rfl⟩ : syracuseStep 1904237 = 714089) (by norm_num)
theorem B2133661 : Blo 842353 2133661 := bbase (se 3 (by rfl) ⟨400061, by rfl⟩ : syracuseStep 2133661 = 800123) (by norm_num)
theorem B1085185 : Blo 842353 1085185 := bbase (se 2 (by rfl) ⟨406944, by rfl⟩ : syracuseStep 1085185 = 813889) (by norm_num)
theorem B2133773 : Blo 842353 2133773 := bbase (se 3 (by rfl) ⟨400082, by rfl⟩ : syracuseStep 2133773 = 800165) (by norm_num)
theorem B2854709 : Blo 842353 2854709 := bbase (se 5 (by rfl) ⟨133814, by rfl⟩ : syracuseStep 2854709 = 267629) (by norm_num)
theorem B1707949 : Blo 842353 1707949 := bbase (se 3 (by rfl) ⟨320240, by rfl⟩ : syracuseStep 1707949 = 640481) (by norm_num)
theorem B2133965 : Blo 842353 2133965 := bbase (se 3 (by rfl) ⟨400118, by rfl⟩ : syracuseStep 2133965 = 800237) (by norm_num)
theorem B13176917 : Blo 842353 13176917 := bbase (se 8 (by rfl) ⟨77208, by rfl⟩ : syracuseStep 13176917 = 154417) (by norm_num)
theorem B1806565 : Blo 842353 1806565 := bbase (se 4 (by rfl) ⟨169365, by rfl⟩ : syracuseStep 1806565 = 338731) (by norm_num)
theorem B2855141 : Blo 842353 2855141 := bbase (se 4 (by rfl) ⟨267669, by rfl⟩ : syracuseStep 2855141 = 535339) (by norm_num)
theorem B12521749 : Blo 842353 12521749 := bbase (se 6 (by rfl) ⟨293478, by rfl⟩ : syracuseStep 12521749 = 586957) (by norm_num)
theorem B2134309 : Blo 842353 2134309 := bbase (se 4 (by rfl) ⟨200091, by rfl⟩ : syracuseStep 2134309 = 400183) (by norm_num)
theorem B1282397 : Blo 842353 1282397 := bbase (se 3 (by rfl) ⟨240449, by rfl⟩ : syracuseStep 1282397 = 480899) (by norm_num)
theorem B2134421 : Blo 842353 2134421 := bbase (se 6 (by rfl) ⟨50025, by rfl⟩ : syracuseStep 2134421 = 100051) (by norm_num)
theorem B1708469 : Blo 842353 1708469 := bbase (se 5 (by rfl) ⟨80084, by rfl⟩ : syracuseStep 1708469 = 160169) (by norm_num)
theorem B3609029 : Blo 842353 3609029 := bbase (se 4 (by rfl) ⟨338346, by rfl⟩ : syracuseStep 3609029 = 676693) (by norm_num)
theorem B8098325 : Blo 842353 8098325 := bbase (se 6 (by rfl) ⟨189804, by rfl⟩ : syracuseStep 8098325 = 379609) (by norm_num)
theorem B2134613 : Blo 842353 2134613 := bbase (se 8 (by rfl) ⟨12507, by rfl⟩ : syracuseStep 2134613 = 25015) (by norm_num)
theorem B1806941 : Blo 842353 1806941 := bbase (se 3 (by rfl) ⟨338801, by rfl⟩ : syracuseStep 1806941 = 677603) (by norm_num)
theorem B2855573 : Blo 842353 2855573 := bbase (se 6 (by rfl) ⟨66927, by rfl⟩ : syracuseStep 2855573 = 133855) (by norm_num)
theorem B3609269 : Blo 842353 3609269 := bbase (se 5 (by rfl) ⟨169184, by rfl⟩ : syracuseStep 3609269 = 338369) (by norm_num)
theorem B2134957 : Blo 842353 2134957 := bbase (se 3 (by rfl) ⟨400304, by rfl⟩ : syracuseStep 2134957 = 800609) (by norm_num)
theorem B857081 : Blo 842353 857081 := bbase (se 2 (by rfl) ⟨321405, by rfl⟩ : syracuseStep 857081 = 642811) (by norm_num)
theorem B857089 : Blo 842353 857089 := bbase (se 2 (by rfl) ⟨321408, by rfl⟩ : syracuseStep 857089 = 642817) (by norm_num)
theorem B2135069 : Blo 842353 2135069 := bbase (se 3 (by rfl) ⟨400325, by rfl⟩ : syracuseStep 2135069 = 800651) (by norm_num)
theorem B2856005 : Blo 842353 2856005 := bbase (se 4 (by rfl) ⟨267750, by rfl⟩ : syracuseStep 2856005 = 535501) (by norm_num)
theorem B2888885 : Blo 842353 2888885 := bbase (se 5 (by rfl) ⟨135416, by rfl⟩ : syracuseStep 2888885 = 270833) (by norm_num)
theorem B2135261 : Blo 842353 2135261 := bbase (se 3 (by rfl) ⟨400361, by rfl⟩ : syracuseStep 2135261 = 800723) (by norm_num)
theorem B1283365 : Blo 842353 1283365 := bbase (se 4 (by rfl) ⟨120315, by rfl⟩ : syracuseStep 1283365 = 240631) (by norm_num)
theorem B1447213 : Blo 842353 1447213 := bbase (se 3 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 1447213 = 542705) (by norm_num)
theorem B1217917 : Blo 842353 1217917 := bbase (se 3 (by rfl) ⟨228359, by rfl⟩ : syracuseStep 1217917 = 456719) (by norm_num)
theorem B2856437 : Blo 842353 2856437 := bbase (se 5 (by rfl) ⟨133895, by rfl⟩ : syracuseStep 2856437 = 267791) (by norm_num)
theorem B2135605 : Blo 842353 2135605 := bbase (se 5 (by rfl) ⟨100106, by rfl⟩ : syracuseStep 2135605 = 200213) (by norm_num)
theorem B4265621 : Blo 842353 4265621 := bbase (se 6 (by rfl) ⟨99975, by rfl⟩ : syracuseStep 4265621 = 199951) (by norm_num)
theorem B1644197 : Blo 842353 1644197 := bbase (se 4 (by rfl) ⟨154143, by rfl⟩ : syracuseStep 1644197 = 308287) (by norm_num)
theorem B2135717 : Blo 842353 2135717 := bbase (se 4 (by rfl) ⟨200223, by rfl⟩ : syracuseStep 2135717 = 400447) (by norm_num)
theorem B2135909 : Blo 842353 2135909 := bbase (se 4 (by rfl) ⟨200241, by rfl⟩ : syracuseStep 2135909 = 400483) (by norm_num)
theorem B3250133 : Blo 842353 3250133 := bbase (se 7 (by rfl) ⟨38087, by rfl⟩ : syracuseStep 3250133 = 76175) (by norm_num)
theorem B2136253 : Blo 842353 2136253 := bbase (se 3 (by rfl) ⟨400547, by rfl⟩ : syracuseStep 2136253 = 801095) (by norm_num)
theorem B2136365 : Blo 842353 2136365 := bbase (se 3 (by rfl) ⟨400568, by rfl⟩ : syracuseStep 2136365 = 801137) (by norm_num)
theorem B1350029 : Blo 842353 1350029 := bbase (se 3 (by rfl) ⟨253130, by rfl⟩ : syracuseStep 1350029 = 506261) (by norm_num)
theorem B2169301 : Blo 842353 2169301 := bbase (se 7 (by rfl) ⟨25421, by rfl⟩ : syracuseStep 2169301 = 50843) (by norm_num)
theorem B2136557 : Blo 842353 2136557 := bbase (se 3 (by rfl) ⟨400604, by rfl⟩ : syracuseStep 2136557 = 801209) (by norm_num)
theorem B5413493 : Blo 842353 5413493 := bbase (se 5 (by rfl) ⟨253757, by rfl⟩ : syracuseStep 5413493 = 507515) (by norm_num)
theorem B4332197 : Blo 842353 4332197 := bbase (se 4 (by rfl) ⟨406143, by rfl⟩ : syracuseStep 4332197 = 812287) (by norm_num)
theorem B989869 : Blo 842353 989869 := bbase (se 3 (by rfl) ⟨185600, by rfl⟩ : syracuseStep 989869 = 371201) (by norm_num)
theorem B4692725 : Blo 842353 4692725 := bbase (se 5 (by rfl) ⟨219971, by rfl⟩ : syracuseStep 4692725 = 439943) (by norm_num)
theorem B2136901 : Blo 842353 2136901 := bbase (se 4 (by rfl) ⟨200334, by rfl⟩ : syracuseStep 2136901 = 400669) (by norm_num)
theorem B3119957 : Blo 842353 3119957 := bbase (se 9 (by rfl) ⟨9140, by rfl⟩ : syracuseStep 3119957 = 18281) (by norm_num)
theorem B1284989 : Blo 842353 1284989 := bbase (se 3 (by rfl) ⟨240935, by rfl⟩ : syracuseStep 1284989 = 481871) (by norm_num)
theorem B1350541 : Blo 842353 1350541 := bbase (se 3 (by rfl) ⟨253226, by rfl⟩ : syracuseStep 1350541 = 506453) (by norm_num)
theorem B4266917 : Blo 842353 4266917 := bbase (se 4 (by rfl) ⟨400023, by rfl⟩ : syracuseStep 4266917 = 800047) (by norm_num)
theorem B3611557 : Blo 842353 3611557 := bbase (se 4 (by rfl) ⟨338583, by rfl⟩ : syracuseStep 3611557 = 677167) (by norm_num)
theorem B2137013 : Blo 842353 2137013 := bbase (se 5 (by rfl) ⟨100172, by rfl⟩ : syracuseStep 2137013 = 200345) (by norm_num)
theorem B2137205 : Blo 842353 2137205 := bbase (se 5 (by rfl) ⟨100181, by rfl⟩ : syracuseStep 2137205 = 200363) (by norm_num)
theorem B6855797 : Blo 842353 6855797 := bbase (se 5 (by rfl) ⟨321365, by rfl⟩ : syracuseStep 6855797 = 642731) (by norm_num)
theorem B3415445 : Blo 842353 3415445 := bbase (se 6 (by rfl) ⟨80049, by rfl⟩ : syracuseStep 3415445 = 160099) (by norm_num)
theorem B2137549 : Blo 842353 2137549 := bbase (se 3 (by rfl) ⟨400790, by rfl⟩ : syracuseStep 2137549 = 801581) (by norm_num)
theorem B2137661 : Blo 842353 2137661 := bbase (se 3 (by rfl) ⟨400811, by rfl⟩ : syracuseStep 2137661 = 801623) (by norm_num)
theorem B925409 : Blo 842353 925409 := bbase (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) (by norm_num)
theorem B2137853 : Blo 842353 2137853 := bbase (se 3 (by rfl) ⟨400847, by rfl⟩ : syracuseStep 2137853 = 801695) (by norm_num)
theorem B2400005 : Blo 842353 2400005 := bbase (se 4 (by rfl) ⟨225000, by rfl⟩ : syracuseStep 2400005 = 450001) (by norm_num)
theorem B1351541 : Blo 842353 1351541 := bbase (se 5 (by rfl) ⟨63353, by rfl⟩ : syracuseStep 1351541 = 126707) (by norm_num)
theorem B13705109 : Blo 842353 13705109 := bbase (se 6 (by rfl) ⟨321213, by rfl⟩ : syracuseStep 13705109 = 642427) (by norm_num)
theorem B1712101 : Blo 842353 1712101 := bbase (se 4 (by rfl) ⟨160509, by rfl⟩ : syracuseStep 1712101 = 321019) (by norm_num)
theorem B1351669 : Blo 842353 1351669 := bbase (se 5 (by rfl) ⟨63359, by rfl⟩ : syracuseStep 1351669 = 126719) (by norm_num)
theorem B1351733 : Blo 842353 1351733 := bbase (se 5 (by rfl) ⟨63362, by rfl⟩ : syracuseStep 1351733 = 126725) (by norm_num)
theorem B2138197 : Blo 842353 2138197 := bbase (se 8 (by rfl) ⟨12528, by rfl⟩ : syracuseStep 2138197 = 25057) (by norm_num)
theorem B16425109 : Blo 842353 16425109 := bbase (se 6 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 16425109 = 769927) (by norm_num)
theorem B9117845 : Blo 842353 9117845 := bbase (se 6 (by rfl) ⟨213699, by rfl⟩ : syracuseStep 9117845 = 427399) (by norm_num)
theorem B2564261 : Blo 842353 2564261 := bbase (se 4 (by rfl) ⟨240399, by rfl⟩ : syracuseStep 2564261 = 480799) (by norm_num)
theorem B4268213 : Blo 842353 4268213 := bbase (se 5 (by rfl) ⟨200072, by rfl⟩ : syracuseStep 4268213 = 400145) (by norm_num)
theorem B2138309 : Blo 842353 2138309 := bbase (se 4 (by rfl) ⟨200466, by rfl⟩ : syracuseStep 2138309 = 400933) (by norm_num)
theorem B3613045 : Blo 842353 3613045 := bbase (se 5 (by rfl) ⟨169361, by rfl⟩ : syracuseStep 3613045 = 338723) (by norm_num)
theorem B2138501 : Blo 842353 2138501 := bbase (se 4 (by rfl) ⟨200484, by rfl⟩ : syracuseStep 2138501 = 400969) (by norm_num)
theorem B3613061 : Blo 842353 3613061 := bbase (se 4 (by rfl) ⟨338724, by rfl⟩ : syracuseStep 3613061 = 677449) (by norm_num)
theorem B1286533 : Blo 842353 1286533 := bbase (se 4 (by rfl) ⟨120612, by rfl⟩ : syracuseStep 1286533 = 241225) (by norm_num)
theorem B1155589 : Blo 842353 1155589 := bbase (se 4 (by rfl) ⟨108336, by rfl⟩ : syracuseStep 1155589 = 216673) (by norm_num)
theorem B2138845 : Blo 842353 2138845 := bbase (se 3 (by rfl) ⟨401033, by rfl⟩ : syracuseStep 2138845 = 802067) (by norm_num)
theorem B2138957 : Blo 842353 2138957 := bbase (se 3 (by rfl) ⟨401054, by rfl⟩ : syracuseStep 2138957 = 802109) (by norm_num)
theorem B6595445 : Blo 842353 6595445 := bbase (se 5 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 6595445 = 618323) (by norm_num)
theorem B2139149 : Blo 842353 2139149 := bbase (se 3 (by rfl) ⟨401090, by rfl⟩ : syracuseStep 2139149 = 802181) (by norm_num)
theorem B2401589 : Blo 842353 2401589 := bbase (se 5 (by rfl) ⟨112574, by rfl⟩ : syracuseStep 2401589 = 225149) (by norm_num)
theorem B1353053 : Blo 842353 1353053 := bbase (se 3 (by rfl) ⟨253697, by rfl⟩ : syracuseStep 1353053 = 507395) (by norm_num)
theorem B2139493 : Blo 842353 2139493 := bbase (se 4 (by rfl) ⟨200577, by rfl⟩ : syracuseStep 2139493 = 401155) (by norm_num)
theorem B4269509 : Blo 842353 4269509 := bbase (se 4 (by rfl) ⟨400266, by rfl⟩ : syracuseStep 4269509 = 800533) (by norm_num)
theorem B2139605 : Blo 842353 2139605 := bbase (se 7 (by rfl) ⟨25073, by rfl⟩ : syracuseStep 2139605 = 50147) (by norm_num)
theorem B1353181 : Blo 842353 1353181 := bbase (se 3 (by rfl) ⟨253721, by rfl⟩ : syracuseStep 1353181 = 507443) (by norm_num)
theorem B2139797 : Blo 842353 2139797 := bbase (se 6 (by rfl) ⟨50151, by rfl⟩ : syracuseStep 2139797 = 100303) (by norm_num)
theorem B2402261 : Blo 842353 2402261 := bbase (se 7 (by rfl) ⟨28151, by rfl⟩ : syracuseStep 2402261 = 56303) (by norm_num)
theorem B2140141 : Blo 842353 2140141 := bbase (se 3 (by rfl) ⟨401276, by rfl⟩ : syracuseStep 2140141 = 802553) (by norm_num)
theorem B2140253 : Blo 842353 2140253 := bbase (se 3 (by rfl) ⟨401297, by rfl⟩ : syracuseStep 2140253 = 802595) (by norm_num)
theorem B1353989 : Blo 842353 1353989 := bbase (se 4 (by rfl) ⟨126936, by rfl⟩ : syracuseStep 1353989 = 253873) (by norm_num)
theorem B2140445 : Blo 842353 2140445 := bbase (se 3 (by rfl) ⟨401333, by rfl⟩ : syracuseStep 2140445 = 802667) (by norm_num)
theorem B3909941 : Blo 842353 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B2402693 : Blo 842353 2402693 := bbase (se 4 (by rfl) ⟨225252, by rfl⟩ : syracuseStep 2402693 = 450505) (by norm_num)
theorem B6072821 : Blo 842353 6072821 := bbase (se 5 (by rfl) ⟨284663, by rfl⟩ : syracuseStep 6072821 = 569327) (by norm_num)
theorem B2599445 : Blo 842353 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B1354277 : Blo 842353 1354277 := bbase (se 4 (by rfl) ⟨126963, by rfl⟩ : syracuseStep 1354277 = 253927) (by norm_num)
theorem B2140789 : Blo 842353 2140789 := bbase (se 5 (by rfl) ⟨100349, by rfl⟩ : syracuseStep 2140789 = 200699) (by norm_num)
theorem B4270805 : Blo 842353 4270805 := bbase (se 7 (by rfl) ⟨50048, by rfl⟩ : syracuseStep 4270805 = 100097) (by norm_num)
theorem B2140901 : Blo 842353 2140901 := bbase (se 4 (by rfl) ⟨200709, by rfl⟩ : syracuseStep 2140901 = 401419) (by norm_num)
theorem B3418949 : Blo 842353 3418949 := bbase (se 4 (by rfl) ⟨320526, by rfl⟩ : syracuseStep 3418949 = 641053) (by norm_num)
theorem B2141093 : Blo 842353 2141093 := bbase (se 4 (by rfl) ⟨200727, by rfl⟩ : syracuseStep 2141093 = 401455) (by norm_num)
theorem B1354693 : Blo 842353 1354693 := bbase (se 4 (by rfl) ⟨127002, by rfl⟩ : syracuseStep 1354693 = 254005) (by norm_num)
theorem B2403445 : Blo 842353 2403445 := bbase (se 5 (by rfl) ⟨112661, by rfl⟩ : syracuseStep 2403445 = 225323) (by norm_num)
theorem B1518725 : Blo 842353 1518725 := bbase (se 4 (by rfl) ⟨142380, by rfl⟩ : syracuseStep 1518725 = 284761) (by norm_num)
theorem B2141437 : Blo 842353 2141437 := bbase (se 3 (by rfl) ⟨401519, by rfl⟩ : syracuseStep 2141437 = 803039) (by norm_num)
theorem B1518869 : Blo 842353 1518869 := bbase (se 6 (by rfl) ⟨35598, by rfl⟩ : syracuseStep 1518869 = 71197) (by norm_num)
theorem B1518949 : Blo 842353 1518949 := bbase (se 4 (by rfl) ⟨142401, by rfl⟩ : syracuseStep 1518949 = 284803) (by norm_num)
theorem B2141549 : Blo 842353 2141549 := bbase (se 3 (by rfl) ⟨401540, by rfl⟩ : syracuseStep 2141549 = 803081) (by norm_num)
theorem B1715573 : Blo 842353 1715573 := bbase (se 5 (by rfl) ⟨80417, by rfl⟩ : syracuseStep 1715573 = 160835) (by norm_num)
theorem B1519013 : Blo 842353 1519013 := bbase (se 4 (by rfl) ⟨142407, by rfl⟩ : syracuseStep 1519013 = 284815) (by norm_num)
theorem B2141741 : Blo 842353 2141741 := bbase (se 3 (by rfl) ⟨401576, by rfl⟩ : syracuseStep 2141741 = 803153) (by norm_num)
theorem B1355629 : Blo 842353 1355629 := bbase (se 3 (by rfl) ⟨254180, by rfl⟩ : syracuseStep 1355629 = 508361) (by norm_num)
theorem B4566901 : Blo 842353 4566901 := bbase (se 5 (by rfl) ⟨214073, by rfl⟩ : syracuseStep 4566901 = 428147) (by norm_num)
theorem B2142085 : Blo 842353 2142085 := bbase (se 4 (by rfl) ⟨200820, by rfl⟩ : syracuseStep 2142085 = 401641) (by norm_num)
theorem B2699237 : Blo 842353 2699237 := bbase (se 4 (by rfl) ⟨253053, by rfl⟩ : syracuseStep 2699237 = 506107) (by norm_num)
theorem B4272101 : Blo 842353 4272101 := bbase (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) (by norm_num)
theorem B2142197 : Blo 842353 2142197 := bbase (se 5 (by rfl) ⟨100415, by rfl⟩ : syracuseStep 2142197 = 200831) (by norm_num)
theorem B1028101 : Blo 842353 1028101 := bbase (se 4 (by rfl) ⟨96384, by rfl⟩ : syracuseStep 1028101 = 192769) (by norm_num)
theorem B3420229 : Blo 842353 3420229 := bbase (se 4 (by rfl) ⟨320646, by rfl⟩ : syracuseStep 3420229 = 641293) (by norm_num)
theorem B1650797 : Blo 842353 1650797 := bbase (se 3 (by rfl) ⟨309524, by rfl⟩ : syracuseStep 1650797 = 619049) (by norm_num)
theorem B1421509 : Blo 842353 1421509 := bbase (se 4 (by rfl) ⟨133266, by rfl⟩ : syracuseStep 1421509 = 266533) (by norm_num)
theorem B1421597 : Blo 842353 1421597 := bbase (se 3 (by rfl) ⟨266549, by rfl⟩ : syracuseStep 1421597 = 533099) (by norm_num)
theorem B2601269 : Blo 842353 2601269 := bbase (se 5 (by rfl) ⟨121934, by rfl⟩ : syracuseStep 2601269 = 243869) (by norm_num)
theorem B1421725 : Blo 842353 1421725 := bbase (se 3 (by rfl) ⟨266573, by rfl⟩ : syracuseStep 1421725 = 533147) (by norm_num)
theorem B5485013 : Blo 842353 5485013 := bbase (se 7 (by rfl) ⟨64277, by rfl⟩ : syracuseStep 5485013 = 128555) (by norm_num)
theorem B1421813 : Blo 842353 1421813 := bbase (se 5 (by rfl) ⟨66647, by rfl⟩ : syracuseStep 1421813 = 133295) (by norm_num)
theorem B1421941 : Blo 842353 1421941 := bbase (se 5 (by rfl) ⟨66653, by rfl⟩ : syracuseStep 1421941 = 133307) (by norm_num)
theorem B1422029 : Blo 842353 1422029 := bbase (se 3 (by rfl) ⟨266630, by rfl⟩ : syracuseStep 1422029 = 533261) (by norm_num)
theorem B1422157 : Blo 842353 1422157 := bbase (se 3 (by rfl) ⟨266654, by rfl⟩ : syracuseStep 1422157 = 533309) (by norm_num)
theorem B1422245 : Blo 842353 1422245 := bbase (se 4 (by rfl) ⟨133335, by rfl⟩ : syracuseStep 1422245 = 266671) (by norm_num)
theorem B1422373 : Blo 842353 1422373 := bbase (se 4 (by rfl) ⟨133347, by rfl⟩ : syracuseStep 1422373 = 266695) (by norm_num)
theorem B1422461 : Blo 842353 1422461 := bbase (se 3 (by rfl) ⟨266711, by rfl⟩ : syracuseStep 1422461 = 533423) (by norm_num)
theorem B963733 : Blo 842353 963733 := bbase (se 6 (by rfl) ⟨22587, by rfl⟩ : syracuseStep 963733 = 45175) (by norm_num)
theorem B3421349 : Blo 842353 3421349 := bbase (se 4 (by rfl) ⟨320751, by rfl⟩ : syracuseStep 3421349 = 641503) (by norm_num)
theorem B4273397 : Blo 842353 4273397 := bbase (se 5 (by rfl) ⟨200315, by rfl⟩ : syracuseStep 4273397 = 400631) (by norm_num)
theorem B1422589 : Blo 842353 1422589 := bbase (se 3 (by rfl) ⟨266735, by rfl⟩ : syracuseStep 1422589 = 533471) (by norm_num)
theorem B1422677 : Blo 842353 1422677 := bbase (se 13 (by rfl) ⟨260, by rfl⟩ : syracuseStep 1422677 = 521) (by norm_num)
theorem B1848685 : Blo 842353 1848685 := bbase (se 3 (by rfl) ⟨346628, by rfl⟩ : syracuseStep 1848685 = 693257) (by norm_num)
theorem B2700661 : Blo 842353 2700661 := bbase (se 5 (by rfl) ⟨126593, by rfl⟩ : syracuseStep 2700661 = 253187) (by norm_num)
theorem B1422805 : Blo 842353 1422805 := bbase (se 7 (by rfl) ⟨16673, by rfl⟩ : syracuseStep 1422805 = 33347) (by norm_num)
theorem B1422893 : Blo 842353 1422893 := bbase (se 3 (by rfl) ⟨266792, by rfl⟩ : syracuseStep 1422893 = 533585) (by norm_num)
theorem B1423021 : Blo 842353 1423021 := bbase (se 3 (by rfl) ⟨266816, by rfl⟩ : syracuseStep 1423021 = 533633) (by norm_num)
theorem B3847925 : Blo 842353 3847925 := bbase (se 5 (by rfl) ⟨180371, by rfl⟩ : syracuseStep 3847925 = 360743) (by norm_num)
theorem B1423109 : Blo 842353 1423109 := bbase (se 4 (by rfl) ⟨133416, by rfl⟩ : syracuseStep 1423109 = 266833) (by norm_num)
theorem B1423237 : Blo 842353 1423237 := bbase (se 4 (by rfl) ⟨133428, by rfl⟩ : syracuseStep 1423237 = 266857) (by norm_num)
theorem B2406293 : Blo 842353 2406293 := bbase (se 6 (by rfl) ⟨56397, by rfl⟩ : syracuseStep 2406293 = 112795) (by norm_num)
theorem B6404021 : Blo 842353 6404021 := bbase (se 5 (by rfl) ⟨300188, by rfl⟩ : syracuseStep 6404021 = 600377) (by norm_num)
theorem B1423325 : Blo 842353 1423325 := bbase (se 3 (by rfl) ⟨266873, by rfl⟩ : syracuseStep 1423325 = 533747) (by norm_num)
theorem B11548693 : Blo 842353 11548693 := bbase (se 6 (by rfl) ⟨270672, by rfl⟩ : syracuseStep 11548693 = 541345) (by norm_num)
theorem B1423453 : Blo 842353 1423453 := bbase (se 3 (by rfl) ⟨266897, by rfl⟩ : syracuseStep 1423453 = 533795) (by norm_num)
theorem B964717 : Blo 842353 964717 := bbase (se 3 (by rfl) ⟨180884, by rfl⟩ : syracuseStep 964717 = 361769) (by norm_num)
theorem B9615509 : Blo 842353 9615509 := bbase (se 6 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 9615509 = 450727) (by norm_num)
theorem B1423541 : Blo 842353 1423541 := bbase (se 5 (by rfl) ⟨66728, by rfl⟩ : syracuseStep 1423541 = 133457) (by norm_num)
theorem B1423669 : Blo 842353 1423669 := bbase (se 5 (by rfl) ⟨66734, by rfl⟩ : syracuseStep 1423669 = 133469) (by norm_num)
theorem B1423757 : Blo 842353 1423757 := bbase (se 3 (by rfl) ⟨266954, by rfl⟩ : syracuseStep 1423757 = 533909) (by norm_num)
theorem B4274693 : Blo 842353 4274693 := bbase (se 4 (by rfl) ⟨400752, by rfl⟩ : syracuseStep 4274693 = 801505) (by norm_num)
theorem B1423885 : Blo 842353 1423885 := bbase (se 3 (by rfl) ⟨266978, by rfl⟩ : syracuseStep 1423885 = 533957) (by norm_num)
theorem B1423973 : Blo 842353 1423973 := bbase (se 4 (by rfl) ⟨133497, by rfl⟩ : syracuseStep 1423973 = 266995) (by norm_num)
theorem B1522357 : Blo 842353 1522357 := bbase (se 5 (by rfl) ⟨71360, by rfl⟩ : syracuseStep 1522357 = 142721) (by norm_num)
theorem B899797 : Blo 842353 899797 := bbase (se 7 (by rfl) ⟨10544, by rfl⟩ : syracuseStep 899797 = 21089) (by norm_num)
theorem B4799189 : Blo 842353 4799189 := bbase (se 7 (by rfl) ⟨56240, by rfl⟩ : syracuseStep 4799189 = 112481) (by norm_num)
theorem B1424101 : Blo 842353 1424101 := bbase (se 4 (by rfl) ⟨133509, by rfl⟩ : syracuseStep 1424101 = 267019) (by norm_num)
theorem B899857 : Blo 842353 899857 := bbase (se 2 (by rfl) ⟨337446, by rfl⟩ : syracuseStep 899857 = 674893) (by norm_num)
theorem B1424189 : Blo 842353 1424189 := bbase (se 3 (by rfl) ⟨267035, by rfl⟩ : syracuseStep 1424189 = 534071) (by norm_num)
theorem B4111253 : Blo 842353 4111253 := bbase (se 6 (by rfl) ⟨96357, by rfl⟩ : syracuseStep 4111253 = 192715) (by norm_num)
theorem B2702261 : Blo 842353 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B1424317 : Blo 842353 1424317 := bbase (se 3 (by rfl) ⟨267059, by rfl⟩ : syracuseStep 1424317 = 534119) (by norm_num)
theorem B1424405 : Blo 842353 1424405 := bbase (se 6 (by rfl) ⟨33384, by rfl⟩ : syracuseStep 1424405 = 66769) (by norm_num)
theorem B2407477 : Blo 842353 2407477 := bbase (se 5 (by rfl) ⟨112850, by rfl⟩ : syracuseStep 2407477 = 225701) (by norm_num)
theorem B900173 : Blo 842353 900173 := bbase (se 3 (by rfl) ⟨168782, by rfl⟩ : syracuseStep 900173 = 337565) (by norm_num)
theorem B1522813 : Blo 842353 1522813 := bbase (se 3 (by rfl) ⟨285527, by rfl⟩ : syracuseStep 1522813 = 571055) (by norm_num)
theorem B1424533 : Blo 842353 1424533 := bbase (se 6 (by rfl) ⟨33387, by rfl⟩ : syracuseStep 1424533 = 66775) (by norm_num)
theorem B2407637 : Blo 842353 2407637 := bbase (se 7 (by rfl) ⟨28214, by rfl⟩ : syracuseStep 2407637 = 56429) (by norm_num)
theorem B1424621 : Blo 842353 1424621 := bbase (se 3 (by rfl) ⟨267116, by rfl⟩ : syracuseStep 1424621 = 534233) (by norm_num)
theorem B1424749 : Blo 842353 1424749 := bbase (se 3 (by rfl) ⟨267140, by rfl⟩ : syracuseStep 1424749 = 534281) (by norm_num)
theorem B1424837 : Blo 842353 1424837 := bbase (se 4 (by rfl) ⟨133578, by rfl⟩ : syracuseStep 1424837 = 267157) (by norm_num)
theorem B2407877 : Blo 842353 2407877 := bbase (se 4 (by rfl) ⟨225738, by rfl⟩ : syracuseStep 2407877 = 451477) (by norm_num)
theorem B900617 : Blo 842353 900617 := bbase (se 2 (by rfl) ⟨337731, by rfl⟩ : syracuseStep 900617 = 675463) (by norm_num)
theorem B900677 : Blo 842353 900677 := bbase (se 4 (by rfl) ⟨84438, by rfl⟩ : syracuseStep 900677 = 168877) (by norm_num)
theorem B1424965 : Blo 842353 1424965 := bbase (se 4 (by rfl) ⟨133590, by rfl⟩ : syracuseStep 1424965 = 267181) (by norm_num)
theorem B2408069 : Blo 842353 2408069 := bbase (se 4 (by rfl) ⟨225756, by rfl⟩ : syracuseStep 2408069 = 451513) (by norm_num)
theorem B1425053 : Blo 842353 1425053 := bbase (se 3 (by rfl) ⟨267197, by rfl⟩ : syracuseStep 1425053 = 534395) (by norm_num)
theorem B900805 : Blo 842353 900805 := bbase (se 4 (by rfl) ⟨84450, by rfl⟩ : syracuseStep 900805 = 168901) (by norm_num)
theorem B4275989 : Blo 842353 4275989 := bbase (se 6 (by rfl) ⟨100218, by rfl⟩ : syracuseStep 4275989 = 200437) (by norm_num)
theorem B1425181 : Blo 842353 1425181 := bbase (se 3 (by rfl) ⟨267221, by rfl⟩ : syracuseStep 1425181 = 534443) (by norm_num)
theorem B1425269 : Blo 842353 1425269 := bbase (se 5 (by rfl) ⟨66809, by rfl⟩ : syracuseStep 1425269 = 133619) (by norm_num)
theorem B7225301 : Blo 842353 7225301 := bbase (se 7 (by rfl) ⟨84671, by rfl⟩ : syracuseStep 7225301 = 169343) (by norm_num)
theorem B1425397 : Blo 842353 1425397 := bbase (se 5 (by rfl) ⟨66815, by rfl⟩ : syracuseStep 1425397 = 133631) (by norm_num)
theorem B2703365 : Blo 842353 2703365 := bbase (se 4 (by rfl) ⟨253440, by rfl⟩ : syracuseStep 2703365 = 506881) (by norm_num)
theorem B1523741 : Blo 842353 1523741 := bbase (se 3 (by rfl) ⟨285701, by rfl⟩ : syracuseStep 1523741 = 571403) (by norm_num)
theorem B1425485 : Blo 842353 1425485 := bbase (se 3 (by rfl) ⟨267278, by rfl⟩ : syracuseStep 1425485 = 534557) (by norm_num)
theorem B901249 : Blo 842353 901249 := bbase (se 2 (by rfl) ⟨337968, by rfl⟩ : syracuseStep 901249 = 675937) (by norm_num)
theorem B1523909 : Blo 842353 1523909 := bbase (se 4 (by rfl) ⟨142866, by rfl⟩ : syracuseStep 1523909 = 285733) (by norm_num)
theorem B1425613 : Blo 842353 1425613 := bbase (se 3 (by rfl) ⟨267302, by rfl⟩ : syracuseStep 1425613 = 534605) (by norm_num)
theorem B901369 : Blo 842353 901369 := bbase (se 2 (by rfl) ⟨338013, by rfl⟩ : syracuseStep 901369 = 676027) (by norm_num)
theorem B1425701 : Blo 842353 1425701 := bbase (se 4 (by rfl) ⟨133659, by rfl⟩ : syracuseStep 1425701 = 267319) (by norm_num)
theorem B10797461 : Blo 842353 10797461 := bbase (se 6 (by rfl) ⟨253065, by rfl⟩ : syracuseStep 10797461 = 506131) (by norm_num)
theorem B1425829 : Blo 842353 1425829 := bbase (se 4 (by rfl) ⟨133671, by rfl⟩ : syracuseStep 1425829 = 267343) (by norm_num)
theorem B7717301 : Blo 842353 7717301 := bbase (se 5 (by rfl) ⟨361748, by rfl⟩ : syracuseStep 7717301 = 723497) (by norm_num)
theorem B1524197 : Blo 842353 1524197 := bbase (se 4 (by rfl) ⟨142893, by rfl⟩ : syracuseStep 1524197 = 285787) (by norm_num)
theorem B901621 : Blo 842353 901621 := bbase (se 5 (by rfl) ⟨42263, by rfl⟩ : syracuseStep 901621 = 84527) (by norm_num)
theorem B901625 : Blo 842353 901625 := bbase (se 2 (by rfl) ⟨338109, by rfl⟩ : syracuseStep 901625 = 676219) (by norm_num)
theorem B1425917 : Blo 842353 1425917 := bbase (se 3 (by rfl) ⟨267359, by rfl⟩ : syracuseStep 1425917 = 534719) (by norm_num)
theorem B2409061 : Blo 842353 2409061 := bbase (se 4 (by rfl) ⟨225849, by rfl⟩ : syracuseStep 2409061 = 451699) (by norm_num)
theorem B1426045 : Blo 842353 1426045 := bbase (se 3 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 1426045 = 534767) (by norm_num)
theorem B1426133 : Blo 842353 1426133 := bbase (se 7 (by rfl) ⟨16712, by rfl⟩ : syracuseStep 1426133 = 33425) (by norm_num)
theorem B1426261 : Blo 842353 1426261 := bbase (se 9 (by rfl) ⟨4178, by rfl⟩ : syracuseStep 1426261 = 8357) (by norm_num)
theorem B1426349 : Blo 842353 1426349 := bbase (se 3 (by rfl) ⟨267440, by rfl⟩ : syracuseStep 1426349 = 534881) (by norm_num)
theorem B4277285 : Blo 842353 4277285 := bbase (se 4 (by rfl) ⟨400995, by rfl⟩ : syracuseStep 4277285 = 801991) (by norm_num)
theorem B902189 : Blo 842353 902189 := bbase (se 3 (by rfl) ⟨169160, by rfl⟩ : syracuseStep 902189 = 338321) (by norm_num)
theorem B1426477 : Blo 842353 1426477 := bbase (se 3 (by rfl) ⟨267464, by rfl⟩ : syracuseStep 1426477 = 534929) (by norm_num)
theorem B1066117 : Blo 842353 1066117 := bbase (se 4 (by rfl) ⟨99948, by rfl⟩ : syracuseStep 1066117 = 199897) (by norm_num)
theorem B1426565 : Blo 842353 1426565 := bbase (se 4 (by rfl) ⟨133740, by rfl⟩ : syracuseStep 1426565 = 267481) (by norm_num)
theorem B4048069 : Blo 842353 4048069 := bbase (se 4 (by rfl) ⟨379506, by rfl⟩ : syracuseStep 4048069 = 759013) (by norm_num)
theorem B1066213 : Blo 842353 1066213 := bbase (se 4 (by rfl) ⟨99957, by rfl⟩ : syracuseStep 1066213 = 199915) (by norm_num)
theorem B902377 : Blo 842353 902377 := bbase (se 2 (by rfl) ⟨338391, by rfl⟩ : syracuseStep 902377 = 676783) (by norm_num)
theorem B1426693 : Blo 842353 1426693 := bbase (se 4 (by rfl) ⟨133752, by rfl⟩ : syracuseStep 1426693 = 267505) (by norm_num)
theorem B1099045 : Blo 842353 1099045 := bbase (se 4 (by rfl) ⟨103035, by rfl⟩ : syracuseStep 1099045 = 206071) (by norm_num)
theorem B1426781 : Blo 842353 1426781 := bbase (se 3 (by rfl) ⟨267521, by rfl⟩ : syracuseStep 1426781 = 535043) (by norm_num)
theorem B1066385 : Blo 842353 1066385 := bbase (se 2 (by rfl) ⟨399894, by rfl⟩ : syracuseStep 1066385 = 799789) (by norm_num)
theorem B1066441 : Blo 842353 1066441 := bbase (se 2 (by rfl) ⟨399915, by rfl⟩ : syracuseStep 1066441 = 799831) (by norm_num)
theorem B1426909 : Blo 842353 1426909 := bbase (se 3 (by rfl) ⟨267545, by rfl⟩ : syracuseStep 1426909 = 535091) (by norm_num)
theorem B1066537 : Blo 842353 1066537 := bbase (se 2 (by rfl) ⟨399951, by rfl⟩ : syracuseStep 1066537 = 799903) (by norm_num)
theorem B1426997 : Blo 842353 1426997 := bbase (se 5 (by rfl) ⟨66890, by rfl⟩ : syracuseStep 1426997 = 133781) (by norm_num)
theorem B1427125 : Blo 842353 1427125 := bbase (se 5 (by rfl) ⟨66896, by rfl⟩ : syracuseStep 1427125 = 133793) (by norm_num)
theorem B1066709 : Blo 842353 1066709 := bbase (se 7 (by rfl) ⟨12500, by rfl⟩ : syracuseStep 1066709 = 25001) (by norm_num)
theorem B2279125 : Blo 842353 2279125 := bbase (se 7 (by rfl) ⟨26708, by rfl⟩ : syracuseStep 2279125 = 53417) (by norm_num)
theorem B1066765 : Blo 842353 1066765 := bbase (se 3 (by rfl) ⟨200018, by rfl⟩ : syracuseStep 1066765 = 400037) (by norm_num)
theorem B1427213 : Blo 842353 1427213 := bbase (se 3 (by rfl) ⟨267602, by rfl⟩ : syracuseStep 1427213 = 535205) (by norm_num)
theorem B1066861 : Blo 842353 1066861 := bbase (se 3 (by rfl) ⟨200036, by rfl⟩ : syracuseStep 1066861 = 400073) (by norm_num)
theorem B2705285 : Blo 842353 2705285 := bbase (se 4 (by rfl) ⟨253620, by rfl⟩ : syracuseStep 2705285 = 507241) (by norm_num)
theorem B1427341 : Blo 842353 1427341 := bbase (se 3 (by rfl) ⟨267626, by rfl⟩ : syracuseStep 1427341 = 535253) (by norm_num)
theorem B1263533 : Blo 842353 1263533 := bbase (se 3 (by rfl) ⟨236912, by rfl⟩ : syracuseStep 1263533 = 473825) (by norm_num)
theorem B1263557 : Blo 842353 1263557 := bbase (se 4 (by rfl) ⟨118458, by rfl⟩ : syracuseStep 1263557 = 236917) (by norm_num)
theorem B1263581 : Blo 842353 1263581 := bbase (se 3 (by rfl) ⟨236921, by rfl⟩ : syracuseStep 1263581 = 473843) (by norm_num)
theorem B1427429 : Blo 842353 1427429 := bbase (se 4 (by rfl) ⟨133821, by rfl⟩ : syracuseStep 1427429 = 267643) (by norm_num)
theorem B1263605 : Blo 842353 1263605 := bbase (se 5 (by rfl) ⟨59231, by rfl⟩ : syracuseStep 1263605 = 118463) (by norm_num)
theorem B1263629 : Blo 842353 1263629 := bbase (se 3 (by rfl) ⟨236930, by rfl⟩ : syracuseStep 1263629 = 473861) (by norm_num)
theorem B1067033 : Blo 842353 1067033 := bbase (se 2 (by rfl) ⟨400137, by rfl⟩ : syracuseStep 1067033 = 800275) (by norm_num)
theorem B903197 : Blo 842353 903197 := bbase (se 3 (by rfl) ⟨169349, by rfl⟩ : syracuseStep 903197 = 338699) (by norm_num)
theorem B1263653 : Blo 842353 1263653 := bbase (se 4 (by rfl) ⟨118467, by rfl⟩ : syracuseStep 1263653 = 236935) (by norm_num)
theorem B1263677 : Blo 842353 1263677 := bbase (se 3 (by rfl) ⟨236939, by rfl⟩ : syracuseStep 1263677 = 473879) (by norm_num)
theorem B1067089 : Blo 842353 1067089 := bbase (se 2 (by rfl) ⟨400158, by rfl⟩ : syracuseStep 1067089 = 800317) (by norm_num)
theorem B1263701 : Blo 842353 1263701 := bbase (se 8 (by rfl) ⟨7404, by rfl⟩ : syracuseStep 1263701 = 14809) (by norm_num)
theorem B1427557 : Blo 842353 1427557 := bbase (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) (by norm_num)
theorem B1263725 : Blo 842353 1263725 := bbase (se 3 (by rfl) ⟨236948, by rfl⟩ : syracuseStep 1263725 = 473897) (by norm_num)
theorem B1263749 : Blo 842353 1263749 := bbase (se 4 (by rfl) ⟨118476, by rfl⟩ : syracuseStep 1263749 = 236953) (by norm_num)
theorem B1263773 : Blo 842353 1263773 := bbase (se 3 (by rfl) ⟨236957, by rfl⟩ : syracuseStep 1263773 = 473915) (by norm_num)
theorem B1067185 : Blo 842353 1067185 := bbase (se 2 (by rfl) ⟨400194, by rfl⟩ : syracuseStep 1067185 = 800389) (by norm_num)
theorem B1263797 : Blo 842353 1263797 := bbase (se 5 (by rfl) ⟨59240, by rfl⟩ : syracuseStep 1263797 = 118481) (by norm_num)
theorem B1427645 : Blo 842353 1427645 := bbase (se 3 (by rfl) ⟨267683, by rfl⟩ : syracuseStep 1427645 = 535367) (by norm_num)
theorem B1263821 : Blo 842353 1263821 := bbase (se 3 (by rfl) ⟨236966, by rfl⟩ : syracuseStep 1263821 = 473933) (by norm_num)
theorem B1263845 : Blo 842353 1263845 := bbase (se 4 (by rfl) ⟨118485, by rfl⟩ : syracuseStep 1263845 = 236971) (by norm_num)
theorem B1263869 : Blo 842353 1263869 := bbase (se 3 (by rfl) ⟨236975, by rfl⟩ : syracuseStep 1263869 = 473951) (by norm_num)
theorem B1263893 : Blo 842353 1263893 := bbase (se 6 (by rfl) ⟨29622, by rfl⟩ : syracuseStep 1263893 = 59245) (by norm_num)
theorem B1263917 : Blo 842353 1263917 := bbase (se 3 (by rfl) ⟨236984, by rfl⟩ : syracuseStep 1263917 = 473969) (by norm_num)
theorem B4278581 : Blo 842353 4278581 := bbase (se 5 (by rfl) ⟨200558, by rfl⟩ : syracuseStep 4278581 = 401117) (by norm_num)
theorem B1427773 : Blo 842353 1427773 := bbase (se 3 (by rfl) ⟨267707, by rfl⟩ : syracuseStep 1427773 = 535415) (by norm_num)
theorem B1263941 : Blo 842353 1263941 := bbase (se 4 (by rfl) ⟨118494, by rfl⟩ : syracuseStep 1263941 = 236989) (by norm_num)
theorem B1263965 : Blo 842353 1263965 := bbase (se 3 (by rfl) ⟨236993, by rfl⟩ : syracuseStep 1263965 = 473987) (by norm_num)
theorem B1067357 : Blo 842353 1067357 := bbase (se 3 (by rfl) ⟨200129, by rfl⟩ : syracuseStep 1067357 = 400259) (by norm_num)
theorem B1263989 : Blo 842353 1263989 := bbase (se 5 (by rfl) ⟨59249, by rfl⟩ : syracuseStep 1263989 = 118499) (by norm_num)
theorem B1264013 : Blo 842353 1264013 := bbase (se 3 (by rfl) ⟨237002, by rfl⟩ : syracuseStep 1264013 = 474005) (by norm_num)
theorem B1067413 : Blo 842353 1067413 := bbase (se 6 (by rfl) ⟨25017, by rfl⟩ : syracuseStep 1067413 = 50035) (by norm_num)
theorem B1427861 : Blo 842353 1427861 := bbase (se 6 (by rfl) ⟨33465, by rfl⟩ : syracuseStep 1427861 = 66931) (by norm_num)
theorem B1264037 : Blo 842353 1264037 := bbase (se 4 (by rfl) ⟨118503, by rfl⟩ : syracuseStep 1264037 = 237007) (by norm_num)
theorem B1264061 : Blo 842353 1264061 := bbase (se 3 (by rfl) ⟨237011, by rfl⟩ : syracuseStep 1264061 = 474023) (by norm_num)
theorem B1264085 : Blo 842353 1264085 := bbase (se 7 (by rfl) ⟨14813, by rfl⟩ : syracuseStep 1264085 = 29627) (by norm_num)
theorem B903641 : Blo 842353 903641 := bbase (se 2 (by rfl) ⟨338865, by rfl⟩ : syracuseStep 903641 = 677731) (by norm_num)
theorem B1264109 : Blo 842353 1264109 := bbase (se 3 (by rfl) ⟨237020, by rfl⟩ : syracuseStep 1264109 = 474041) (by norm_num)
theorem B1067509 : Blo 842353 1067509 := bbase (se 5 (by rfl) ⟨50039, by rfl⟩ : syracuseStep 1067509 = 100079) (by norm_num)
theorem B1264133 : Blo 842353 1264133 := bbase (se 4 (by rfl) ⟨118512, by rfl⟩ : syracuseStep 1264133 = 237025) (by norm_num)
theorem B1427989 : Blo 842353 1427989 := bbase (se 6 (by rfl) ⟨33468, by rfl⟩ : syracuseStep 1427989 = 66937) (by norm_num)
theorem B1264157 : Blo 842353 1264157 := bbase (se 3 (by rfl) ⟨237029, by rfl⟩ : syracuseStep 1264157 = 474059) (by norm_num)
theorem B1264181 : Blo 842353 1264181 := bbase (se 5 (by rfl) ⟨59258, by rfl⟩ : syracuseStep 1264181 = 118517) (by norm_num)
theorem B5130805 : Blo 842353 5130805 := bbase (se 5 (by rfl) ⟨240506, by rfl⟩ : syracuseStep 5130805 = 481013) (by norm_num)
theorem B1624637 : Blo 842353 1624637 := bbase (se 3 (by rfl) ⟨304619, by rfl⟩ : syracuseStep 1624637 = 609239) (by norm_num)
theorem B1264205 : Blo 842353 1264205 := bbase (se 3 (by rfl) ⟨237038, by rfl⟩ : syracuseStep 1264205 = 474077) (by norm_num)
theorem B1264229 : Blo 842353 1264229 := bbase (se 4 (by rfl) ⟨118521, by rfl⟩ : syracuseStep 1264229 = 237043) (by norm_num)
theorem B1428077 : Blo 842353 1428077 := bbase (se 3 (by rfl) ⟨267764, by rfl⟩ : syracuseStep 1428077 = 535529) (by norm_num)
theorem B1264253 : Blo 842353 1264253 := bbase (se 3 (by rfl) ⟨237047, by rfl⟩ : syracuseStep 1264253 = 474095) (by norm_num)
theorem B1264277 : Blo 842353 1264277 := bbase (se 6 (by rfl) ⟨29631, by rfl⟩ : syracuseStep 1264277 = 59263) (by norm_num)
theorem B1067681 : Blo 842353 1067681 := bbase (se 2 (by rfl) ⟨400380, by rfl⟩ : syracuseStep 1067681 = 800761) (by norm_num)
theorem B1264301 : Blo 842353 1264301 := bbase (se 3 (by rfl) ⟨237056, by rfl⟩ : syracuseStep 1264301 = 474113) (by norm_num)
theorem B1264325 : Blo 842353 1264325 := bbase (se 4 (by rfl) ⟨118530, by rfl⟩ : syracuseStep 1264325 = 237061) (by norm_num)
theorem B1067737 : Blo 842353 1067737 := bbase (se 2 (by rfl) ⟨400401, by rfl⟩ : syracuseStep 1067737 = 800803) (by norm_num)
theorem B1264349 : Blo 842353 1264349 := bbase (se 3 (by rfl) ⟨237065, by rfl⟩ : syracuseStep 1264349 = 474131) (by norm_num)
theorem B1428205 : Blo 842353 1428205 := bbase (se 3 (by rfl) ⟨267788, by rfl⟩ : syracuseStep 1428205 = 535577) (by norm_num)
theorem B1264373 : Blo 842353 1264373 := bbase (se 5 (by rfl) ⟨59267, by rfl⟩ : syracuseStep 1264373 = 118535) (by norm_num)
theorem B1264397 : Blo 842353 1264397 := bbase (se 3 (by rfl) ⟨237074, by rfl⟩ : syracuseStep 1264397 = 474149) (by norm_num)
theorem B16468757 : Blo 842353 16468757 := bbase (se 6 (by rfl) ⟨385986, by rfl⟩ : syracuseStep 16468757 = 771973) (by norm_num)
theorem B1264421 : Blo 842353 1264421 := bbase (se 4 (by rfl) ⟨118539, by rfl⟩ : syracuseStep 1264421 = 237079) (by norm_num)
theorem B1067833 : Blo 842353 1067833 := bbase (se 2 (by rfl) ⟨400437, by rfl⟩ : syracuseStep 1067833 = 800875) (by norm_num)
theorem B1264445 : Blo 842353 1264445 := bbase (se 3 (by rfl) ⟨237083, by rfl⟩ : syracuseStep 1264445 = 474167) (by norm_num)
theorem B1264469 : Blo 842353 1264469 := bbase (se 9 (by rfl) ⟨3704, by rfl⟩ : syracuseStep 1264469 = 7409) (by norm_num)
theorem B1264493 : Blo 842353 1264493 := bbase (se 3 (by rfl) ⟨237092, by rfl⟩ : syracuseStep 1264493 = 474185) (by norm_num)
theorem B7228277 : Blo 842353 7228277 := bbase (se 5 (by rfl) ⟨338825, by rfl⟩ : syracuseStep 7228277 = 677651) (by norm_num)
theorem B1264517 : Blo 842353 1264517 := bbase (se 4 (by rfl) ⟨118548, by rfl⟩ : syracuseStep 1264517 = 237097) (by norm_num)
theorem B1264541 : Blo 842353 1264541 := bbase (se 3 (by rfl) ⟨237101, by rfl⟩ : syracuseStep 1264541 = 474203) (by norm_num)
theorem B1264565 : Blo 842353 1264565 := bbase (se 5 (by rfl) ⟨59276, by rfl⟩ : syracuseStep 1264565 = 118553) (by norm_num)
theorem B1264589 : Blo 842353 1264589 := bbase (se 3 (by rfl) ⟨237110, by rfl⟩ : syracuseStep 1264589 = 474221) (by norm_num)
theorem B1264613 : Blo 842353 1264613 := bbase (se 4 (by rfl) ⟨118557, by rfl⟩ : syracuseStep 1264613 = 237115) (by norm_num)
theorem B1068005 : Blo 842353 1068005 := bbase (se 4 (by rfl) ⟨100125, by rfl⟩ : syracuseStep 1068005 = 200251) (by norm_num)
theorem B1264637 : Blo 842353 1264637 := bbase (se 3 (by rfl) ⟨237119, by rfl⟩ : syracuseStep 1264637 = 474239) (by norm_num)
theorem B1264661 : Blo 842353 1264661 := bbase (se 6 (by rfl) ⟨29640, by rfl⟩ : syracuseStep 1264661 = 59281) (by norm_num)
theorem B1068061 : Blo 842353 1068061 := bbase (se 3 (by rfl) ⟨200261, by rfl⟩ : syracuseStep 1068061 = 400523) (by norm_num)
theorem B1264685 : Blo 842353 1264685 := bbase (se 3 (by rfl) ⟨237128, by rfl⟩ : syracuseStep 1264685 = 474257) (by norm_num)
theorem B1264709 : Blo 842353 1264709 := bbase (se 4 (by rfl) ⟨118566, by rfl⟩ : syracuseStep 1264709 = 237133) (by norm_num)
theorem B1264733 : Blo 842353 1264733 := bbase (se 3 (by rfl) ⟨237137, by rfl⟩ : syracuseStep 1264733 = 474275) (by norm_num)
theorem B1264757 : Blo 842353 1264757 := bbase (se 5 (by rfl) ⟨59285, by rfl⟩ : syracuseStep 1264757 = 118571) (by norm_num)
theorem B1068157 : Blo 842353 1068157 := bbase (se 3 (by rfl) ⟨200279, by rfl⟩ : syracuseStep 1068157 = 400559) (by norm_num)
theorem B1264781 : Blo 842353 1264781 := bbase (se 3 (by rfl) ⟨237146, by rfl⟩ : syracuseStep 1264781 = 474293) (by norm_num)
theorem B1264805 : Blo 842353 1264805 := bbase (se 4 (by rfl) ⟨118575, by rfl⟩ : syracuseStep 1264805 = 237151) (by norm_num)
theorem B1264829 : Blo 842353 1264829 := bbase (se 3 (by rfl) ⟨237155, by rfl⟩ : syracuseStep 1264829 = 474311) (by norm_num)
theorem B1264853 : Blo 842353 1264853 := bbase (se 7 (by rfl) ⟨14822, by rfl⟩ : syracuseStep 1264853 = 29645) (by norm_num)
theorem B1264877 : Blo 842353 1264877 := bbase (se 3 (by rfl) ⟨237164, by rfl⟩ : syracuseStep 1264877 = 474329) (by norm_num)
theorem B1264901 : Blo 842353 1264901 := bbase (se 4 (by rfl) ⟨118584, by rfl⟩ : syracuseStep 1264901 = 237169) (by norm_num)
theorem B2706709 : Blo 842353 2706709 := bbase (se 6 (by rfl) ⟨63438, by rfl⟩ : syracuseStep 2706709 = 126877) (by norm_num)
theorem B1264925 : Blo 842353 1264925 := bbase (se 3 (by rfl) ⟨237173, by rfl⟩ : syracuseStep 1264925 = 474347) (by norm_num)
theorem B1068329 : Blo 842353 1068329 := bbase (se 2 (by rfl) ⟨400623, by rfl⟩ : syracuseStep 1068329 = 801247) (by norm_num)
theorem B1264949 : Blo 842353 1264949 := bbase (se 5 (by rfl) ⟨59294, by rfl⟩ : syracuseStep 1264949 = 118589) (by norm_num)
theorem B1264973 : Blo 842353 1264973 := bbase (se 3 (by rfl) ⟨237182, by rfl⟩ : syracuseStep 1264973 = 474365) (by norm_num)
theorem B1625437 : Blo 842353 1625437 := bbase (se 3 (by rfl) ⟨304769, by rfl⟩ : syracuseStep 1625437 = 609539) (by norm_num)
theorem B1068385 : Blo 842353 1068385 := bbase (se 2 (by rfl) ⟨400644, by rfl⟩ : syracuseStep 1068385 = 801289) (by norm_num)
theorem B1264997 : Blo 842353 1264997 := bbase (se 4 (by rfl) ⟨118593, by rfl⟩ : syracuseStep 1264997 = 237187) (by norm_num)
theorem B1265021 : Blo 842353 1265021 := bbase (se 3 (by rfl) ⟨237191, by rfl⟩ : syracuseStep 1265021 = 474383) (by norm_num)
theorem B1265045 : Blo 842353 1265045 := bbase (se 6 (by rfl) ⟨29649, by rfl⟩ : syracuseStep 1265045 = 59299) (by norm_num)
theorem B1265069 : Blo 842353 1265069 := bbase (se 3 (by rfl) ⟨237200, by rfl⟩ : syracuseStep 1265069 = 474401) (by norm_num)
theorem B1953197 : Blo 842353 1953197 := bbase (se 3 (by rfl) ⟨366224, by rfl⟩ : syracuseStep 1953197 = 732449) (by norm_num)
theorem B1068481 : Blo 842353 1068481 := bbase (se 2 (by rfl) ⟨400680, by rfl⟩ : syracuseStep 1068481 = 801361) (by norm_num)
theorem B1265093 : Blo 842353 1265093 := bbase (se 4 (by rfl) ⟨118602, by rfl⟩ : syracuseStep 1265093 = 237205) (by norm_num)
theorem B1265117 : Blo 842353 1265117 := bbase (se 3 (by rfl) ⟨237209, by rfl⟩ : syracuseStep 1265117 = 474419) (by norm_num)
theorem B7687669 : Blo 842353 7687669 := bbase (se 5 (by rfl) ⟨360359, by rfl⟩ : syracuseStep 7687669 = 720719) (by norm_num)
theorem B1265141 : Blo 842353 1265141 := bbase (se 5 (by rfl) ⟨59303, by rfl⟩ : syracuseStep 1265141 = 118607) (by norm_num)
theorem B1265165 : Blo 842353 1265165 := bbase (se 3 (by rfl) ⟨237218, by rfl⟩ : syracuseStep 1265165 = 474437) (by norm_num)
theorem B1265189 : Blo 842353 1265189 := bbase (se 4 (by rfl) ⟨118611, by rfl⟩ : syracuseStep 1265189 = 237223) (by norm_num)
theorem B1265213 : Blo 842353 1265213 := bbase (se 3 (by rfl) ⟨237227, by rfl⟩ : syracuseStep 1265213 = 474455) (by norm_num)
theorem B4279877 : Blo 842353 4279877 := bbase (se 4 (by rfl) ⟨401238, by rfl⟩ : syracuseStep 4279877 = 802477) (by norm_num)
theorem B1199701 : Blo 842353 1199701 := bbase (se 8 (by rfl) ⟨7029, by rfl⟩ : syracuseStep 1199701 = 14059) (by norm_num)
theorem B1265237 : Blo 842353 1265237 := bbase (se 8 (by rfl) ⟨7413, by rfl⟩ : syracuseStep 1265237 = 14827) (by norm_num)
theorem B1265261 : Blo 842353 1265261 := bbase (se 3 (by rfl) ⟨237236, by rfl⟩ : syracuseStep 1265261 = 474473) (by norm_num)
theorem B1068653 : Blo 842353 1068653 := bbase (se 3 (by rfl) ⟨200372, by rfl⟩ : syracuseStep 1068653 = 400745) (by norm_num)
theorem B1265285 : Blo 842353 1265285 := bbase (se 4 (by rfl) ⟨118620, by rfl⟩ : syracuseStep 1265285 = 237241) (by norm_num)
theorem B1265309 : Blo 842353 1265309 := bbase (se 3 (by rfl) ⟨237245, by rfl⟩ : syracuseStep 1265309 = 474491) (by norm_num)
theorem B1068709 : Blo 842353 1068709 := bbase (se 4 (by rfl) ⟨100191, by rfl⟩ : syracuseStep 1068709 = 200383) (by norm_num)
theorem B1265333 : Blo 842353 1265333 := bbase (se 5 (by rfl) ⟨59312, by rfl⟩ : syracuseStep 1265333 = 118625) (by norm_num)
theorem B1265357 : Blo 842353 1265357 := bbase (se 3 (by rfl) ⟨237254, by rfl⟩ : syracuseStep 1265357 = 474509) (by norm_num)
theorem B2707157 : Blo 842353 2707157 := bbase (se 7 (by rfl) ⟨31724, by rfl⟩ : syracuseStep 2707157 = 63449) (by norm_num)
theorem B1265381 : Blo 842353 1265381 := bbase (se 4 (by rfl) ⟨118629, by rfl⟩ : syracuseStep 1265381 = 237259) (by norm_num)
theorem B1265405 : Blo 842353 1265405 := bbase (se 3 (by rfl) ⟨237263, by rfl⟩ : syracuseStep 1265405 = 474527) (by norm_num)
theorem B1068805 : Blo 842353 1068805 := bbase (se 4 (by rfl) ⟨100200, by rfl⟩ : syracuseStep 1068805 = 200401) (by norm_num)
theorem B1265429 : Blo 842353 1265429 := bbase (se 6 (by rfl) ⟨29658, by rfl⟩ : syracuseStep 1265429 = 59317) (by norm_num)
theorem B1265453 : Blo 842353 1265453 := bbase (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) (by norm_num)
theorem B1265477 : Blo 842353 1265477 := bbase (se 4 (by rfl) ⟨118638, by rfl⟩ : syracuseStep 1265477 = 237277) (by norm_num)
theorem B1265501 : Blo 842353 1265501 := bbase (se 3 (by rfl) ⟨237281, by rfl⟩ : syracuseStep 1265501 = 474563) (by norm_num)
theorem B1265525 : Blo 842353 1265525 := bbase (se 5 (by rfl) ⟨59321, by rfl⟩ : syracuseStep 1265525 = 118643) (by norm_num)
theorem B1265549 : Blo 842353 1265549 := bbase (se 3 (by rfl) ⟨237290, by rfl⟩ : syracuseStep 1265549 = 474581) (by norm_num)
theorem B1200037 : Blo 842353 1200037 := bbase (se 4 (by rfl) ⟨112503, by rfl⟩ : syracuseStep 1200037 = 225007) (by norm_num)
theorem B1265573 : Blo 842353 1265573 := bbase (se 4 (by rfl) ⟨118647, by rfl⟩ : syracuseStep 1265573 = 237295) (by norm_num)
theorem B1068977 : Blo 842353 1068977 := bbase (se 2 (by rfl) ⟨400866, by rfl⟩ : syracuseStep 1068977 = 801733) (by norm_num)
theorem B7196597 : Blo 842353 7196597 := bbase (se 5 (by rfl) ⟨337340, by rfl⟩ : syracuseStep 7196597 = 674681) (by norm_num)
theorem B1265597 : Blo 842353 1265597 := bbase (se 3 (by rfl) ⟨237299, by rfl⟩ : syracuseStep 1265597 = 474599) (by norm_num)
theorem B1265621 : Blo 842353 1265621 := bbase (se 7 (by rfl) ⟨14831, by rfl⟩ : syracuseStep 1265621 = 29663) (by norm_num)
theorem B1069033 : Blo 842353 1069033 := bbase (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) (by norm_num)
theorem B1265645 : Blo 842353 1265645 := bbase (se 3 (by rfl) ⟨237308, by rfl⟩ : syracuseStep 1265645 = 474617) (by norm_num)
theorem B8114165 : Blo 842353 8114165 := bbase (se 5 (by rfl) ⟨380351, by rfl⟩ : syracuseStep 8114165 = 760703) (by norm_num)
theorem B1265669 : Blo 842353 1265669 := bbase (se 4 (by rfl) ⟨118656, by rfl⟩ : syracuseStep 1265669 = 237313) (by norm_num)
theorem B1265693 : Blo 842353 1265693 := bbase (se 3 (by rfl) ⟨237317, by rfl⟩ : syracuseStep 1265693 = 474635) (by norm_num)
theorem B1265717 : Blo 842353 1265717 := bbase (se 5 (by rfl) ⟨59330, by rfl⟩ : syracuseStep 1265717 = 118661) (by norm_num)
theorem B1069129 : Blo 842353 1069129 := bbase (se 2 (by rfl) ⟨400923, by rfl⟩ : syracuseStep 1069129 = 801847) (by norm_num)
theorem B1265741 : Blo 842353 1265741 := bbase (se 3 (by rfl) ⟨237326, by rfl⟩ : syracuseStep 1265741 = 474653) (by norm_num)
theorem B1265765 : Blo 842353 1265765 := bbase (se 4 (by rfl) ⟨118665, by rfl⟩ : syracuseStep 1265765 = 237331) (by norm_num)
theorem B1200253 : Blo 842353 1200253 := bbase (se 3 (by rfl) ⟨225047, by rfl⟩ : syracuseStep 1200253 = 450095) (by norm_num)
theorem B1265789 : Blo 842353 1265789 := bbase (se 3 (by rfl) ⟨237335, by rfl⟩ : syracuseStep 1265789 = 474671) (by norm_num)
theorem B1265813 : Blo 842353 1265813 := bbase (se 6 (by rfl) ⟨29667, by rfl⟩ : syracuseStep 1265813 = 59335) (by norm_num)
theorem B1265837 : Blo 842353 1265837 := bbase (se 3 (by rfl) ⟨237344, by rfl⟩ : syracuseStep 1265837 = 474689) (by norm_num)
theorem B1265861 : Blo 842353 1265861 := bbase (se 4 (by rfl) ⟨118674, by rfl⟩ : syracuseStep 1265861 = 237349) (by norm_num)
theorem B1265885 : Blo 842353 1265885 := bbase (se 3 (by rfl) ⟨237353, by rfl⟩ : syracuseStep 1265885 = 474707) (by norm_num)
theorem B1265909 : Blo 842353 1265909 := bbase (se 5 (by rfl) ⟨59339, by rfl⟩ : syracuseStep 1265909 = 118679) (by norm_num)
theorem B1069301 : Blo 842353 1069301 := bbase (se 5 (by rfl) ⟨50123, by rfl⟩ : syracuseStep 1069301 = 100247) (by norm_num)
theorem B1265933 : Blo 842353 1265933 := bbase (se 3 (by rfl) ⟨237362, by rfl⟩ : syracuseStep 1265933 = 474725) (by norm_num)
theorem B1265957 : Blo 842353 1265957 := bbase (se 4 (by rfl) ⟨118683, by rfl⟩ : syracuseStep 1265957 = 237367) (by norm_num)
theorem B1069357 : Blo 842353 1069357 := bbase (se 3 (by rfl) ⟨200504, by rfl⟩ : syracuseStep 1069357 = 401009) (by norm_num)
theorem B1265981 : Blo 842353 1265981 := bbase (se 3 (by rfl) ⟨237371, by rfl⟩ : syracuseStep 1265981 = 474743) (by norm_num)
theorem B1266005 : Blo 842353 1266005 := bbase (se 10 (by rfl) ⟨1854, by rfl⟩ : syracuseStep 1266005 = 3709) (by norm_num)
theorem B1266029 : Blo 842353 1266029 := bbase (se 3 (by rfl) ⟨237380, by rfl⟩ : syracuseStep 1266029 = 474761) (by norm_num)
theorem B1266053 : Blo 842353 1266053 := bbase (se 4 (by rfl) ⟨118692, by rfl⟩ : syracuseStep 1266053 = 237385) (by norm_num)
theorem B1069453 : Blo 842353 1069453 := bbase (se 3 (by rfl) ⟨200522, by rfl⟩ : syracuseStep 1069453 = 401045) (by norm_num)
theorem B1266077 : Blo 842353 1266077 := bbase (se 3 (by rfl) ⟨237389, by rfl⟩ : syracuseStep 1266077 = 474779) (by norm_num)
theorem B1266101 : Blo 842353 1266101 := bbase (se 5 (by rfl) ⟨59348, by rfl⟩ : syracuseStep 1266101 = 118697) (by norm_num)
theorem B1266125 : Blo 842353 1266125 := bbase (se 3 (by rfl) ⟨237398, by rfl⟩ : syracuseStep 1266125 = 474797) (by norm_num)
theorem B3199445 : Blo 842353 3199445 := bbase (se 7 (by rfl) ⟨37493, by rfl⟩ : syracuseStep 3199445 = 74987) (by norm_num)
theorem B1266149 : Blo 842353 1266149 := bbase (se 4 (by rfl) ⟨118701, by rfl⟩ : syracuseStep 1266149 = 237403) (by norm_num)
theorem B1200629 : Blo 842353 1200629 := bbase (se 5 (by rfl) ⟨56279, by rfl⟩ : syracuseStep 1200629 = 112559) (by norm_num)
theorem B1266173 : Blo 842353 1266173 := bbase (se 3 (by rfl) ⟨237407, by rfl⟩ : syracuseStep 1266173 = 474815) (by norm_num)
theorem B1266197 : Blo 842353 1266197 := bbase (se 6 (by rfl) ⟨29676, by rfl⟩ : syracuseStep 1266197 = 59353) (by norm_num)
theorem B1266221 : Blo 842353 1266221 := bbase (se 3 (by rfl) ⟨237416, by rfl⟩ : syracuseStep 1266221 = 474833) (by norm_num)
theorem B1069625 : Blo 842353 1069625 := bbase (se 2 (by rfl) ⟨401109, by rfl⟩ : syracuseStep 1069625 = 802219) (by norm_num)
theorem B1266245 : Blo 842353 1266245 := bbase (se 4 (by rfl) ⟨118710, by rfl⟩ : syracuseStep 1266245 = 237421) (by norm_num)
theorem B1266269 : Blo 842353 1266269 := bbase (se 3 (by rfl) ⟨237425, by rfl⟩ : syracuseStep 1266269 = 474851) (by norm_num)
theorem B1069681 : Blo 842353 1069681 := bbase (se 2 (by rfl) ⟨401130, by rfl⟩ : syracuseStep 1069681 = 802261) (by norm_num)
theorem B1266293 : Blo 842353 1266293 := bbase (se 5 (by rfl) ⟨59357, by rfl⟩ : syracuseStep 1266293 = 118715) (by norm_num)
theorem B1266317 : Blo 842353 1266317 := bbase (se 3 (by rfl) ⟨237434, by rfl⟩ : syracuseStep 1266317 = 474869) (by norm_num)
theorem B12145301 : Blo 842353 12145301 := bbase (se 6 (by rfl) ⟨284655, by rfl⟩ : syracuseStep 12145301 = 569311) (by norm_num)
theorem B1266341 : Blo 842353 1266341 := bbase (se 4 (by rfl) ⟨118719, by rfl⟩ : syracuseStep 1266341 = 237439) (by norm_num)
theorem B1266365 : Blo 842353 1266365 := bbase (se 3 (by rfl) ⟨237443, by rfl⟩ : syracuseStep 1266365 = 474887) (by norm_num)
theorem B1069777 : Blo 842353 1069777 := bbase (se 2 (by rfl) ⟨401166, by rfl⟩ : syracuseStep 1069777 = 802333) (by norm_num)
theorem B1266389 : Blo 842353 1266389 := bbase (se 7 (by rfl) ⟨14840, by rfl⟩ : syracuseStep 1266389 = 29681) (by norm_num)
theorem B1266413 : Blo 842353 1266413 := bbase (se 3 (by rfl) ⟨237452, by rfl⟩ : syracuseStep 1266413 = 474905) (by norm_num)
theorem B3199733 : Blo 842353 3199733 := bbase (se 5 (by rfl) ⟨149987, by rfl⟩ : syracuseStep 3199733 = 299975) (by norm_num)
theorem B1266437 : Blo 842353 1266437 := bbase (se 4 (by rfl) ⟨118728, by rfl⟩ : syracuseStep 1266437 = 237457) (by norm_num)
theorem B1266461 : Blo 842353 1266461 := bbase (se 3 (by rfl) ⟨237461, by rfl⟩ : syracuseStep 1266461 = 474923) (by norm_num)
theorem B1266485 : Blo 842353 1266485 := bbase (se 5 (by rfl) ⟨59366, by rfl⟩ : syracuseStep 1266485 = 118733) (by norm_num)
theorem B1266509 : Blo 842353 1266509 := bbase (se 3 (by rfl) ⟨237470, by rfl⟩ : syracuseStep 1266509 = 474941) (by norm_num)
theorem B4281173 : Blo 842353 4281173 := bbase (se 9 (by rfl) ⟨12542, by rfl⟩ : syracuseStep 4281173 = 25085) (by norm_num)
theorem B1266533 : Blo 842353 1266533 := bbase (se 4 (by rfl) ⟨118737, by rfl⟩ : syracuseStep 1266533 = 237475) (by norm_num)
theorem B3855221 : Blo 842353 3855221 := bbase (se 5 (by rfl) ⟨180713, by rfl⟩ : syracuseStep 3855221 = 361427) (by norm_num)
theorem B1266557 : Blo 842353 1266557 := bbase (se 3 (by rfl) ⟨237479, by rfl⟩ : syracuseStep 1266557 = 474959) (by norm_num)
theorem B1069949 : Blo 842353 1069949 := bbase (se 3 (by rfl) ⟨200615, by rfl⟩ : syracuseStep 1069949 = 401231) (by norm_num)
theorem B1266581 : Blo 842353 1266581 := bbase (se 6 (by rfl) ⟨29685, by rfl⟩ : syracuseStep 1266581 = 59371) (by norm_num)
theorem B1266605 : Blo 842353 1266605 := bbase (se 3 (by rfl) ⟨237488, by rfl⟩ : syracuseStep 1266605 = 474977) (by norm_num)
theorem B1070005 : Blo 842353 1070005 := bbase (se 5 (by rfl) ⟨50156, by rfl⟩ : syracuseStep 1070005 = 100313) (by norm_num)
theorem B1627069 : Blo 842353 1627069 := bbase (se 3 (by rfl) ⟨305075, by rfl⟩ : syracuseStep 1627069 = 610151) (by norm_num)
theorem B1266629 : Blo 842353 1266629 := bbase (se 4 (by rfl) ⟨118746, by rfl⟩ : syracuseStep 1266629 = 237493) (by norm_num)
theorem B1266653 : Blo 842353 1266653 := bbase (se 3 (by rfl) ⟨237497, by rfl⟩ : syracuseStep 1266653 = 474995) (by norm_num)
theorem B1463269 : Blo 842353 1463269 := bbase (se 4 (by rfl) ⟨137181, by rfl⟩ : syracuseStep 1463269 = 274363) (by norm_num)
theorem B1266677 : Blo 842353 1266677 := bbase (se 5 (by rfl) ⟨59375, by rfl⟩ : syracuseStep 1266677 = 118751) (by norm_num)
theorem B1266701 : Blo 842353 1266701 := bbase (se 3 (by rfl) ⟨237506, by rfl⟩ : syracuseStep 1266701 = 475013) (by norm_num)
theorem B1070101 : Blo 842353 1070101 := bbase (se 6 (by rfl) ⟨25080, by rfl⟩ : syracuseStep 1070101 = 50161) (by norm_num)
theorem B1266725 : Blo 842353 1266725 := bbase (se 4 (by rfl) ⟨118755, by rfl⟩ : syracuseStep 1266725 = 237511) (by norm_num)
theorem B1266749 : Blo 842353 1266749 := bbase (se 3 (by rfl) ⟨237515, by rfl⟩ : syracuseStep 1266749 = 475031) (by norm_num)
theorem B1266773 : Blo 842353 1266773 := bbase (se 8 (by rfl) ⟨7422, by rfl⟩ : syracuseStep 1266773 = 14845) (by norm_num)
theorem B1266797 : Blo 842353 1266797 := bbase (se 3 (by rfl) ⟨237524, by rfl⟩ : syracuseStep 1266797 = 475049) (by norm_num)
theorem B1266821 : Blo 842353 1266821 := bbase (se 4 (by rfl) ⟨118764, by rfl⟩ : syracuseStep 1266821 = 237529) (by norm_num)
theorem B1266845 : Blo 842353 1266845 := bbase (se 3 (by rfl) ⟨237533, by rfl⟩ : syracuseStep 1266845 = 475067) (by norm_num)
theorem B1266869 : Blo 842353 1266869 := bbase (se 5 (by rfl) ⟨59384, by rfl⟩ : syracuseStep 1266869 = 118769) (by norm_num)
theorem B1070273 : Blo 842353 1070273 := bbase (se 2 (by rfl) ⟨401352, by rfl⟩ : syracuseStep 1070273 = 802705) (by norm_num)
theorem B1266893 : Blo 842353 1266893 := bbase (se 3 (by rfl) ⟨237542, by rfl⟩ : syracuseStep 1266893 = 475085) (by norm_num)
theorem B1266917 : Blo 842353 1266917 := bbase (se 4 (by rfl) ⟨118773, by rfl⟩ : syracuseStep 1266917 = 237547) (by norm_num)
theorem B1070329 : Blo 842353 1070329 := bbase (se 2 (by rfl) ⟨401373, by rfl⟩ : syracuseStep 1070329 = 802747) (by norm_num)
theorem B1266941 : Blo 842353 1266941 := bbase (se 3 (by rfl) ⟨237551, by rfl⟩ : syracuseStep 1266941 = 475103) (by norm_num)
theorem B1266965 : Blo 842353 1266965 := bbase (se 6 (by rfl) ⟨29694, by rfl⟩ : syracuseStep 1266965 = 59389) (by norm_num)
theorem B1266989 : Blo 842353 1266989 := bbase (se 3 (by rfl) ⟨237560, by rfl⟩ : syracuseStep 1266989 = 475121) (by norm_num)
theorem B1267013 : Blo 842353 1267013 := bbase (se 4 (by rfl) ⟨118782, by rfl⟩ : syracuseStep 1267013 = 237565) (by norm_num)
theorem B1070425 : Blo 842353 1070425 := bbase (se 2 (by rfl) ⟨401409, by rfl⟩ : syracuseStep 1070425 = 802819) (by norm_num)
theorem B1267037 : Blo 842353 1267037 := bbase (se 3 (by rfl) ⟨237569, by rfl⟩ : syracuseStep 1267037 = 475139) (by norm_num)
theorem B1267061 : Blo 842353 1267061 := bbase (se 5 (by rfl) ⟨59393, by rfl⟩ : syracuseStep 1267061 = 118787) (by norm_num)
theorem B1922429 : Blo 842353 1922429 := bbase (se 3 (by rfl) ⟨360455, by rfl⟩ : syracuseStep 1922429 = 720911) (by norm_num)
theorem B1267085 : Blo 842353 1267085 := bbase (se 3 (by rfl) ⟨237578, by rfl⟩ : syracuseStep 1267085 = 475157) (by norm_num)
theorem B1267109 : Blo 842353 1267109 := bbase (se 4 (by rfl) ⟨118791, by rfl⟩ : syracuseStep 1267109 = 237583) (by norm_num)
theorem B1267133 : Blo 842353 1267133 := bbase (se 3 (by rfl) ⟨237587, by rfl⟩ : syracuseStep 1267133 = 475175) (by norm_num)
theorem B1267157 : Blo 842353 1267157 := bbase (se 7 (by rfl) ⟨14849, by rfl⟩ : syracuseStep 1267157 = 29699) (by norm_num)
theorem B1267181 : Blo 842353 1267181 := bbase (se 3 (by rfl) ⟨237596, by rfl⟩ : syracuseStep 1267181 = 475193) (by norm_num)
theorem B1267205 : Blo 842353 1267205 := bbase (se 4 (by rfl) ⟨118800, by rfl⟩ : syracuseStep 1267205 = 237601) (by norm_num)
theorem B1070597 : Blo 842353 1070597 := bbase (se 4 (by rfl) ⟨100368, by rfl⟩ : syracuseStep 1070597 = 200737) (by norm_num)
theorem B6411797 : Blo 842353 6411797 := bbase (se 6 (by rfl) ⟨150276, by rfl⟩ : syracuseStep 6411797 = 300553) (by norm_num)
theorem B1267229 : Blo 842353 1267229 := bbase (se 3 (by rfl) ⟨237605, by rfl⟩ : syracuseStep 1267229 = 475211) (by norm_num)
theorem B1267253 : Blo 842353 1267253 := bbase (se 5 (by rfl) ⟨59402, by rfl⟩ : syracuseStep 1267253 = 118805) (by norm_num)
theorem B1070653 : Blo 842353 1070653 := bbase (se 3 (by rfl) ⟨200747, by rfl⟩ : syracuseStep 1070653 = 401495) (by norm_num)
theorem B1267277 : Blo 842353 1267277 := bbase (se 3 (by rfl) ⟨237614, by rfl⟩ : syracuseStep 1267277 = 475229) (by norm_num)
theorem B1267301 : Blo 842353 1267301 := bbase (se 4 (by rfl) ⟨118809, by rfl⟩ : syracuseStep 1267301 = 237619) (by norm_num)
theorem B1267325 : Blo 842353 1267325 := bbase (se 3 (by rfl) ⟨237623, by rfl⟩ : syracuseStep 1267325 = 475247) (by norm_num)
theorem B1267349 : Blo 842353 1267349 := bbase (se 6 (by rfl) ⟨29703, by rfl⟩ : syracuseStep 1267349 = 59407) (by norm_num)
theorem B1070749 : Blo 842353 1070749 := bbase (se 3 (by rfl) ⟨200765, by rfl⟩ : syracuseStep 1070749 = 401531) (by norm_num)
theorem B1562285 : Blo 842353 1562285 := bbase (se 3 (by rfl) ⟨292928, by rfl⟩ : syracuseStep 1562285 = 585857) (by norm_num)
theorem B1267373 : Blo 842353 1267373 := bbase (se 3 (by rfl) ⟨237632, by rfl⟩ : syracuseStep 1267373 = 475265) (by norm_num)
theorem B1267397 : Blo 842353 1267397 := bbase (se 4 (by rfl) ⟨118818, by rfl⟩ : syracuseStep 1267397 = 237637) (by norm_num)
theorem B1267421 : Blo 842353 1267421 := bbase (se 3 (by rfl) ⟨237641, by rfl⟩ : syracuseStep 1267421 = 475283) (by norm_num)
theorem B1267445 : Blo 842353 1267445 := bbase (se 5 (by rfl) ⟨59411, by rfl⟩ : syracuseStep 1267445 = 118823) (by norm_num)
theorem B1267469 : Blo 842353 1267469 := bbase (se 3 (by rfl) ⟨237650, by rfl⟩ : syracuseStep 1267469 = 475301) (by norm_num)
theorem B1267493 : Blo 842353 1267493 := bbase (se 4 (by rfl) ⟨118827, by rfl⟩ : syracuseStep 1267493 = 237655) (by norm_num)
theorem B1267517 : Blo 842353 1267517 := bbase (se 3 (by rfl) ⟨237659, by rfl⟩ : syracuseStep 1267517 = 475319) (by norm_num)
theorem B1070921 : Blo 842353 1070921 := bbase (se 2 (by rfl) ⟨401595, by rfl⟩ : syracuseStep 1070921 = 803191) (by norm_num)
theorem B1267541 : Blo 842353 1267541 := bbase (se 9 (by rfl) ⟨3713, by rfl⟩ : syracuseStep 1267541 = 7427) (by norm_num)
theorem B1267565 : Blo 842353 1267565 := bbase (se 3 (by rfl) ⟨237668, by rfl⟩ : syracuseStep 1267565 = 475337) (by norm_num)
theorem B1070977 : Blo 842353 1070977 := bbase (se 2 (by rfl) ⟨401616, by rfl⟩ : syracuseStep 1070977 = 803233) (by norm_num)
theorem B1202053 : Blo 842353 1202053 := bbase (se 4 (by rfl) ⟨112692, by rfl⟩ : syracuseStep 1202053 = 225385) (by norm_num)
theorem B1267589 : Blo 842353 1267589 := bbase (se 4 (by rfl) ⟨118836, by rfl⟩ : syracuseStep 1267589 = 237673) (by norm_num)
theorem B3200917 : Blo 842353 3200917 := bbase (se 6 (by rfl) ⟨75021, by rfl⟩ : syracuseStep 3200917 = 150043) (by norm_num)
theorem B1267613 : Blo 842353 1267613 := bbase (se 3 (by rfl) ⟨237677, by rfl⟩ : syracuseStep 1267613 = 475355) (by norm_num)
theorem B2709413 : Blo 842353 2709413 := bbase (se 4 (by rfl) ⟨254007, by rfl⟩ : syracuseStep 2709413 = 508015) (by norm_num)
theorem B1267637 : Blo 842353 1267637 := bbase (se 5 (by rfl) ⟨59420, by rfl⟩ : syracuseStep 1267637 = 118841) (by norm_num)
theorem B1267661 : Blo 842353 1267661 := bbase (se 3 (by rfl) ⟨237686, by rfl⟩ : syracuseStep 1267661 = 475373) (by norm_num)
theorem B1071073 : Blo 842353 1071073 := bbase (se 2 (by rfl) ⟨401652, by rfl⟩ : syracuseStep 1071073 = 803305) (by norm_num)
theorem B1267685 : Blo 842353 1267685 := bbase (se 4 (by rfl) ⟨118845, by rfl⟩ : syracuseStep 1267685 = 237691) (by norm_num)
theorem B1267709 : Blo 842353 1267709 := bbase (se 3 (by rfl) ⟨237695, by rfl⟩ : syracuseStep 1267709 = 475391) (by norm_num)
theorem B1267733 : Blo 842353 1267733 := bbase (se 6 (by rfl) ⟨29712, by rfl⟩ : syracuseStep 1267733 = 59425) (by norm_num)
theorem B1267757 : Blo 842353 1267757 := bbase (se 3 (by rfl) ⟨237704, by rfl⟩ : syracuseStep 1267757 = 475409) (by norm_num)
theorem B1267781 : Blo 842353 1267781 := bbase (se 4 (by rfl) ⟨118854, by rfl⟩ : syracuseStep 1267781 = 237709) (by norm_num)
theorem B1267805 : Blo 842353 1267805 := bbase (se 3 (by rfl) ⟨237713, by rfl⟩ : syracuseStep 1267805 = 475427) (by norm_num)
theorem B4282469 : Blo 842353 4282469 := bbase (se 4 (by rfl) ⟨401481, by rfl⟩ : syracuseStep 4282469 = 802963) (by norm_num)
theorem B1267829 : Blo 842353 1267829 := bbase (se 5 (by rfl) ⟨59429, by rfl⟩ : syracuseStep 1267829 = 118859) (by norm_num)
theorem B1267853 : Blo 842353 1267853 := bbase (se 3 (by rfl) ⟨237722, by rfl⟩ : syracuseStep 1267853 = 475445) (by norm_num)
theorem B17356949 : Blo 842353 17356949 := bbase (se 6 (by rfl) ⟨406803, by rfl⟩ : syracuseStep 17356949 = 813607) (by norm_num)
theorem B1267877 : Blo 842353 1267877 := bbase (se 4 (by rfl) ⟨118863, by rfl⟩ : syracuseStep 1267877 = 237727) (by norm_num)
theorem B1267901 : Blo 842353 1267901 := bbase (se 3 (by rfl) ⟨237731, by rfl⟩ : syracuseStep 1267901 = 475463) (by norm_num)
theorem B3201221 : Blo 842353 3201221 := bbase (se 4 (by rfl) ⟨300114, by rfl⟩ : syracuseStep 3201221 = 600229) (by norm_num)
theorem B1267925 : Blo 842353 1267925 := bbase (se 7 (by rfl) ⟨14858, by rfl⟩ : syracuseStep 1267925 = 29717) (by norm_num)
theorem B1267949 : Blo 842353 1267949 := bbase (se 3 (by rfl) ⟨237740, by rfl⟩ : syracuseStep 1267949 = 475481) (by norm_num)
theorem B1267973 : Blo 842353 1267973 := bbase (se 4 (by rfl) ⟨118872, by rfl⟩ : syracuseStep 1267973 = 237745) (by norm_num)
theorem B1267997 : Blo 842353 1267997 := bbase (se 3 (by rfl) ⟨237749, by rfl⟩ : syracuseStep 1267997 = 475499) (by norm_num)
theorem B1268021 : Blo 842353 1268021 := bbase (se 5 (by rfl) ⟨59438, by rfl⟩ : syracuseStep 1268021 = 118877) (by norm_num)
theorem B1268045 : Blo 842353 1268045 := bbase (se 3 (by rfl) ⟨237758, by rfl⟩ : syracuseStep 1268045 = 475517) (by norm_num)
theorem B2677093 : Blo 842353 2677093 := bbase (se 4 (by rfl) ⟨250977, by rfl⟩ : syracuseStep 2677093 = 501955) (by norm_num)
theorem B1268069 : Blo 842353 1268069 := bbase (se 4 (by rfl) ⟨118881, by rfl⟩ : syracuseStep 1268069 = 237763) (by norm_num)
theorem B1268093 : Blo 842353 1268093 := bbase (se 3 (by rfl) ⟨237767, by rfl⟩ : syracuseStep 1268093 = 475535) (by norm_num)
theorem B1268117 : Blo 842353 1268117 := bbase (se 6 (by rfl) ⟨29721, by rfl⟩ : syracuseStep 1268117 = 59443) (by norm_num)
theorem B1268141 : Blo 842353 1268141 := bbase (se 3 (by rfl) ⟨237776, by rfl⟩ : syracuseStep 1268141 = 475553) (by norm_num)
theorem B1268165 : Blo 842353 1268165 := bbase (se 4 (by rfl) ⟨118890, by rfl⟩ : syracuseStep 1268165 = 237781) (by norm_num)
theorem B1202645 : Blo 842353 1202645 := bbase (se 7 (by rfl) ⟨14093, by rfl⟩ : syracuseStep 1202645 = 28187) (by norm_num)
theorem B1268189 : Blo 842353 1268189 := bbase (se 3 (by rfl) ⟨237785, by rfl⟩ : syracuseStep 1268189 = 475571) (by norm_num)
theorem B1268213 : Blo 842353 1268213 := bbase (se 5 (by rfl) ⟨59447, by rfl⟩ : syracuseStep 1268213 = 118895) (by norm_num)
theorem B1268237 : Blo 842353 1268237 := bbase (se 3 (by rfl) ⟨237794, by rfl⟩ : syracuseStep 1268237 = 475589) (by norm_num)
theorem B1202725 : Blo 842353 1202725 := bbase (se 4 (by rfl) ⟨112755, by rfl⟩ : syracuseStep 1202725 = 225511) (by norm_num)
theorem B1268261 : Blo 842353 1268261 := bbase (se 4 (by rfl) ⟨118899, by rfl⟩ : syracuseStep 1268261 = 237799) (by norm_num)
theorem B1268285 : Blo 842353 1268285 := bbase (se 3 (by rfl) ⟨237803, by rfl⟩ : syracuseStep 1268285 = 475607) (by norm_num)
theorem B1268309 : Blo 842353 1268309 := bbase (se 8 (by rfl) ⟨7431, by rfl⟩ : syracuseStep 1268309 = 14863) (by norm_num)
theorem B1268333 : Blo 842353 1268333 := bbase (se 3 (by rfl) ⟨237812, by rfl⟩ : syracuseStep 1268333 = 475625) (by norm_num)
theorem B1268357 : Blo 842353 1268357 := bbase (se 4 (by rfl) ⟨118908, by rfl⟩ : syracuseStep 1268357 = 237817) (by norm_num)
theorem B1825429 : Blo 842353 1825429 := bbase (se 6 (by rfl) ⟨42783, by rfl⟩ : syracuseStep 1825429 = 85567) (by norm_num)
theorem B1202845 : Blo 842353 1202845 := bbase (se 3 (by rfl) ⟨225533, by rfl⟩ : syracuseStep 1202845 = 451067) (by norm_num)
theorem B1268381 : Blo 842353 1268381 := bbase (se 3 (by rfl) ⟨237821, by rfl⟩ : syracuseStep 1268381 = 475643) (by norm_num)
theorem B1268405 : Blo 842353 1268405 := bbase (se 5 (by rfl) ⟨59456, by rfl⟩ : syracuseStep 1268405 = 118913) (by norm_num)
theorem B1268429 : Blo 842353 1268429 := bbase (se 3 (by rfl) ⟨237830, by rfl⟩ : syracuseStep 1268429 = 475661) (by norm_num)
theorem B1268453 : Blo 842353 1268453 := bbase (se 4 (by rfl) ⟨118917, by rfl⟩ : syracuseStep 1268453 = 237835) (by norm_num)
theorem B1202941 : Blo 842353 1202941 := bbase (se 3 (by rfl) ⟨225551, by rfl⟩ : syracuseStep 1202941 = 451103) (by norm_num)
theorem B1268477 : Blo 842353 1268477 := bbase (se 3 (by rfl) ⟨237839, by rfl⟩ : syracuseStep 1268477 = 475679) (by norm_num)
theorem B1268501 : Blo 842353 1268501 := bbase (se 6 (by rfl) ⟨29730, by rfl⟩ : syracuseStep 1268501 = 59461) (by norm_num)
theorem B1268525 : Blo 842353 1268525 := bbase (se 3 (by rfl) ⟨237848, by rfl⟩ : syracuseStep 1268525 = 475697) (by norm_num)
theorem B1268549 : Blo 842353 1268549 := bbase (se 4 (by rfl) ⟨118926, by rfl⟩ : syracuseStep 1268549 = 237853) (by norm_num)
theorem B1268573 : Blo 842353 1268573 := bbase (se 3 (by rfl) ⟨237857, by rfl⟩ : syracuseStep 1268573 = 475715) (by norm_num)
theorem B1825637 : Blo 842353 1825637 := bbase (se 4 (by rfl) ⟨171153, by rfl⟩ : syracuseStep 1825637 = 342307) (by norm_num)
theorem B1268597 : Blo 842353 1268597 := bbase (se 5 (by rfl) ⟨59465, by rfl⟩ : syracuseStep 1268597 = 118931) (by norm_num)
theorem B1268621 : Blo 842353 1268621 := bbase (se 3 (by rfl) ⟨237866, by rfl⟩ : syracuseStep 1268621 = 475733) (by norm_num)
theorem B1268645 : Blo 842353 1268645 := bbase (se 4 (by rfl) ⟨118935, by rfl⟩ : syracuseStep 1268645 = 237871) (by norm_num)
theorem B1268669 : Blo 842353 1268669 := bbase (se 3 (by rfl) ⟨237875, by rfl⟩ : syracuseStep 1268669 = 475751) (by norm_num)
theorem B1268693 : Blo 842353 1268693 := bbase (se 7 (by rfl) ⟨14867, by rfl⟩ : syracuseStep 1268693 = 29735) (by norm_num)
theorem B1268717 : Blo 842353 1268717 := bbase (se 3 (by rfl) ⟨237884, by rfl⟩ : syracuseStep 1268717 = 475769) (by norm_num)
theorem B5790709 : Blo 842353 5790709 := bbase (se 5 (by rfl) ⟨271439, by rfl⟩ : syracuseStep 5790709 = 542879) (by norm_num)
theorem B1268741 : Blo 842353 1268741 := bbase (se 4 (by rfl) ⟨118944, by rfl⟩ : syracuseStep 1268741 = 237889) (by norm_num)
theorem B1268765 : Blo 842353 1268765 := bbase (se 3 (by rfl) ⟨237893, by rfl⟩ : syracuseStep 1268765 = 475787) (by norm_num)
theorem B1268789 : Blo 842353 1268789 := bbase (se 5 (by rfl) ⟨59474, by rfl⟩ : syracuseStep 1268789 = 118949) (by norm_num)
theorem B1268813 : Blo 842353 1268813 := bbase (se 3 (by rfl) ⟨237902, by rfl⟩ : syracuseStep 1268813 = 475805) (by norm_num)
theorem B1268837 : Blo 842353 1268837 := bbase (se 4 (by rfl) ⟨118953, by rfl⟩ : syracuseStep 1268837 = 237907) (by norm_num)
theorem B2284661 : Blo 842353 2284661 := bbase (se 5 (by rfl) ⟨107093, by rfl⟩ : syracuseStep 2284661 = 214187) (by norm_num)
theorem B1268861 : Blo 842353 1268861 := bbase (se 3 (by rfl) ⟨237911, by rfl⟩ : syracuseStep 1268861 = 475823) (by norm_num)
theorem B5397653 : Blo 842353 5397653 := bbase (se 6 (by rfl) ⟨126507, by rfl⟩ : syracuseStep 5397653 = 253015) (by norm_num)
theorem B1268885 : Blo 842353 1268885 := bbase (se 6 (by rfl) ⟨29739, by rfl⟩ : syracuseStep 1268885 = 59479) (by norm_num)
theorem B1924253 : Blo 842353 1924253 := bbase (se 3 (by rfl) ⟨360797, by rfl⟩ : syracuseStep 1924253 = 721595) (by norm_num)
theorem B1268909 : Blo 842353 1268909 := bbase (se 3 (by rfl) ⟨237920, by rfl⟩ : syracuseStep 1268909 = 475841) (by norm_num)
theorem B1268933 : Blo 842353 1268933 := bbase (se 4 (by rfl) ⟨118962, by rfl⟩ : syracuseStep 1268933 = 237925) (by norm_num)
theorem B1268957 : Blo 842353 1268957 := bbase (se 3 (by rfl) ⟨237929, by rfl⟩ : syracuseStep 1268957 = 475859) (by norm_num)
theorem B1203437 : Blo 842353 1203437 := bbase (se 3 (by rfl) ⟨225644, by rfl⟩ : syracuseStep 1203437 = 451289) (by norm_num)
theorem B1268981 : Blo 842353 1268981 := bbase (se 5 (by rfl) ⟨59483, by rfl⟩ : syracuseStep 1268981 = 118967) (by norm_num)
theorem B1269005 : Blo 842353 1269005 := bbase (se 3 (by rfl) ⟨237938, by rfl⟩ : syracuseStep 1269005 = 475877) (by norm_num)
theorem B1269029 : Blo 842353 1269029 := bbase (se 4 (by rfl) ⟨118971, by rfl⟩ : syracuseStep 1269029 = 237943) (by norm_num)
theorem B1269053 : Blo 842353 1269053 := bbase (se 3 (by rfl) ⟨237947, by rfl⟩ : syracuseStep 1269053 = 475895) (by norm_num)
theorem B1269077 : Blo 842353 1269077 := bbase (se 11 (by rfl) ⟨929, by rfl⟩ : syracuseStep 1269077 = 1859) (by norm_num)
theorem B1269101 : Blo 842353 1269101 := bbase (se 3 (by rfl) ⟨237956, by rfl⟩ : syracuseStep 1269101 = 475913) (by norm_num)
theorem B4283765 : Blo 842353 4283765 := bbase (se 5 (by rfl) ⟨200801, by rfl⟩ : syracuseStep 4283765 = 401603) (by norm_num)
theorem B1269125 : Blo 842353 1269125 := bbase (se 4 (by rfl) ⟨118980, by rfl⟩ : syracuseStep 1269125 = 237961) (by norm_num)
theorem B1269149 : Blo 842353 1269149 := bbase (se 3 (by rfl) ⟨237965, by rfl⟩ : syracuseStep 1269149 = 475931) (by norm_num)
theorem B1269173 : Blo 842353 1269173 := bbase (se 5 (by rfl) ⟨59492, by rfl⟩ : syracuseStep 1269173 = 118985) (by norm_num)
theorem B1269197 : Blo 842353 1269197 := bbase (se 3 (by rfl) ⟨237974, by rfl⟩ : syracuseStep 1269197 = 475949) (by norm_num)
theorem B1269221 : Blo 842353 1269221 := bbase (se 4 (by rfl) ⟨118989, by rfl⟩ : syracuseStep 1269221 = 237979) (by norm_num)
theorem B1269245 : Blo 842353 1269245 := bbase (se 3 (by rfl) ⟨237983, by rfl⟩ : syracuseStep 1269245 = 475967) (by norm_num)
theorem B1269269 : Blo 842353 1269269 := bbase (se 6 (by rfl) ⟨29748, by rfl⟩ : syracuseStep 1269269 = 59497) (by norm_num)
theorem B1269293 : Blo 842353 1269293 := bbase (se 3 (by rfl) ⟨237992, by rfl⟩ : syracuseStep 1269293 = 475985) (by norm_num)
theorem B1269317 : Blo 842353 1269317 := bbase (se 4 (by rfl) ⟨118998, by rfl⟩ : syracuseStep 1269317 = 237997) (by norm_num)
theorem B20012629 : Blo 842353 20012629 := bbase (se 8 (by rfl) ⟨117261, by rfl⟩ : syracuseStep 20012629 = 234523) (by norm_num)
theorem B1269341 : Blo 842353 1269341 := bbase (se 3 (by rfl) ⟨238001, by rfl⟩ : syracuseStep 1269341 = 476003) (by norm_num)
theorem B1269365 : Blo 842353 1269365 := bbase (se 5 (by rfl) ⟨59501, by rfl⟩ : syracuseStep 1269365 = 119003) (by norm_num)
theorem B1269389 : Blo 842353 1269389 := bbase (se 3 (by rfl) ⟨238010, by rfl⟩ : syracuseStep 1269389 = 476021) (by norm_num)
theorem B974497 : Blo 842353 974497 := bbase (se 2 (by rfl) ⟨365436, by rfl⟩ : syracuseStep 974497 = 730873) (by norm_num)
theorem B1269413 : Blo 842353 1269413 := bbase (se 4 (by rfl) ⟨119007, by rfl⟩ : syracuseStep 1269413 = 238015) (by norm_num)
theorem B1269437 : Blo 842353 1269437 := bbase (se 3 (by rfl) ⟨238019, by rfl⟩ : syracuseStep 1269437 = 476039) (by norm_num)
theorem B1269461 : Blo 842353 1269461 := bbase (se 7 (by rfl) ⟨14876, by rfl⟩ : syracuseStep 1269461 = 29753) (by norm_num)
theorem B1269485 : Blo 842353 1269485 := bbase (se 3 (by rfl) ⟨238028, by rfl⟩ : syracuseStep 1269485 = 476057) (by norm_num)
theorem B1269509 : Blo 842353 1269509 := bbase (se 4 (by rfl) ⟨119016, by rfl⟩ : syracuseStep 1269509 = 238033) (by norm_num)
theorem B1203989 : Blo 842353 1203989 := bbase (se 6 (by rfl) ⟨28218, by rfl⟩ : syracuseStep 1203989 = 56437) (by norm_num)
theorem B4054853 : Blo 842353 4054853 := bbase (se 4 (by rfl) ⟨380142, by rfl⟩ : syracuseStep 4054853 = 760285) (by norm_num)
theorem B1925221 : Blo 842353 1925221 := bbase (se 4 (by rfl) ⟨180489, by rfl⟩ : syracuseStep 1925221 = 360979) (by norm_num)
theorem B3203333 : Blo 842353 3203333 := bbase (se 4 (by rfl) ⟨300312, by rfl⟩ : syracuseStep 3203333 = 600625) (by norm_num)
theorem B4809077 : Blo 842353 4809077 := bbase (se 5 (by rfl) ⟨225425, by rfl⟩ : syracuseStep 4809077 = 450851) (by norm_num)
theorem B2318725 : Blo 842353 2318725 := bbase (se 4 (by rfl) ⟨217380, by rfl⟩ : syracuseStep 2318725 = 434761) (by norm_num)
theorem B2843045 : Blo 842353 2843045 := bbase (se 4 (by rfl) ⟨266535, by rfl⟩ : syracuseStep 2843045 = 533071) (by norm_num)
theorem B1139141 : Blo 842353 1139141 := bbase (se 4 (by rfl) ⟨106794, by rfl⟩ : syracuseStep 1139141 = 213589) (by norm_num)
theorem B1139173 : Blo 842353 1139173 := bbase (se 4 (by rfl) ⟨106797, by rfl⟩ : syracuseStep 1139173 = 213595) (by norm_num)
theorem B1204741 : Blo 842353 1204741 := bbase (se 4 (by rfl) ⟨112944, by rfl⟩ : syracuseStep 1204741 = 225889) (by norm_num)
theorem B3203621 : Blo 842353 3203621 := bbase (se 4 (by rfl) ⟨300339, by rfl⟩ : syracuseStep 3203621 = 600679) (by norm_num)
theorem B6087413 : Blo 842353 6087413 := bbase (se 5 (by rfl) ⟨285347, by rfl⟩ : syracuseStep 6087413 = 570695) (by norm_num)
theorem B2843477 : Blo 842353 2843477 := bbase (se 9 (by rfl) ⟨8330, by rfl⟩ : syracuseStep 2843477 = 16661) (by norm_num)
theorem B1926317 : Blo 842353 1926317 := bbase (se 3 (by rfl) ⟨361184, by rfl⟩ : syracuseStep 1926317 = 722369) (by norm_num)
theorem B4056277 : Blo 842353 4056277 := bbase (se 7 (by rfl) ⟨47534, by rfl⟩ : syracuseStep 4056277 = 95069) (by norm_num)
theorem B2843909 : Blo 842353 2843909 := bbase (se 4 (by rfl) ⟨266616, by rfl⟩ : syracuseStep 2843909 = 533233) (by norm_num)
theorem B2024813 : Blo 842353 2024813 := bbase (se 3 (by rfl) ⟨379652, by rfl⟩ : syracuseStep 2024813 = 759305) (by norm_num)
theorem B976249 : Blo 842353 976249 := bbase (se 2 (by rfl) ⟨366093, by rfl⟩ : syracuseStep 976249 = 732187) (by norm_num)
theorem B2024957 : Blo 842353 2024957 := bbase (se 3 (by rfl) ⟨379679, by rfl⟩ : syracuseStep 2024957 = 759359) (by norm_num)
theorem B3860021 : Blo 842353 3860021 := bbase (se 5 (by rfl) ⟨180938, by rfl⟩ : syracuseStep 3860021 = 361877) (by norm_num)
theorem B2844341 : Blo 842353 2844341 := bbase (se 5 (by rfl) ⟨133328, by rfl⟩ : syracuseStep 2844341 = 266657) (by norm_num)
theorem B3204805 : Blo 842353 3204805 := bbase (se 4 (by rfl) ⟨300450, by rfl⟩ : syracuseStep 3204805 = 600901) (by norm_num)
theorem B1042157 : Blo 842353 1042157 := bbase (se 3 (by rfl) ⟨195404, by rfl⟩ : syracuseStep 1042157 = 390809) (by norm_num)
theorem B3860261 : Blo 842353 3860261 := bbase (se 4 (by rfl) ⟨361899, by rfl⟩ : syracuseStep 3860261 = 723799) (by norm_num)
theorem B1599365 : Blo 842353 1599365 := bbase (se 4 (by rfl) ⟨149940, by rfl⟩ : syracuseStep 1599365 = 299881) (by norm_num)
theorem B3860405 : Blo 842353 3860405 := bbase (se 5 (by rfl) ⟨180956, by rfl⟩ : syracuseStep 3860405 = 361913) (by norm_num)
theorem B1140709 : Blo 842353 1140709 := bbase (se 4 (by rfl) ⟨106941, by rfl⟩ : syracuseStep 1140709 = 213883) (by norm_num)
theorem B3205109 : Blo 842353 3205109 := bbase (se 5 (by rfl) ⟨150239, by rfl⟩ : syracuseStep 3205109 = 300479) (by norm_num)
theorem B1599517 : Blo 842353 1599517 := bbase (se 3 (by rfl) ⟨299909, by rfl⟩ : syracuseStep 1599517 = 599819) (by norm_num)
theorem B1370189 : Blo 842353 1370189 := bbase (se 3 (by rfl) ⟨256910, by rfl⟩ : syracuseStep 1370189 = 513821) (by norm_num)
theorem B2844773 : Blo 842353 2844773 := bbase (se 4 (by rfl) ⟨266697, by rfl⟩ : syracuseStep 2844773 = 533395) (by norm_num)
theorem B1042601 : Blo 842353 1042601 := bbase (se 2 (by rfl) ⟨390975, by rfl⟩ : syracuseStep 1042601 = 781951) (by norm_num)
theorem B1599821 : Blo 842353 1599821 := bbase (se 3 (by rfl) ⟨299966, by rfl⟩ : syracuseStep 1599821 = 599933) (by norm_num)
theorem B2845205 : Blo 842353 2845205 := bbase (se 6 (by rfl) ⟨66684, by rfl⟩ : syracuseStep 2845205 = 133369) (by norm_num)
theorem B1895309 : Blo 842353 1895309 := bbase (se 3 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 1895309 = 710741) (by norm_num)
theorem B5401525 : Blo 842353 5401525 := bbase (se 5 (by rfl) ⟨253196, by rfl⟩ : syracuseStep 5401525 = 506393) (by norm_num)
theorem B2845637 : Blo 842353 2845637 := bbase (se 4 (by rfl) ⟨266778, by rfl⟩ : syracuseStep 2845637 = 533557) (by norm_num)
theorem B1895381 : Blo 842353 1895381 := bbase (se 7 (by rfl) ⟨22211, by rfl⟩ : syracuseStep 1895381 = 44423) (by norm_num)
theorem B1895453 : Blo 842353 1895453 := bbase (se 3 (by rfl) ⟨355397, by rfl⟩ : syracuseStep 1895453 = 710795) (by norm_num)
theorem B1600573 : Blo 842353 1600573 := bbase (se 3 (by rfl) ⟨300107, by rfl⟩ : syracuseStep 1600573 = 600215) (by norm_num)
theorem B1895525 : Blo 842353 1895525 := bbase (se 4 (by rfl) ⟨177705, by rfl⟩ : syracuseStep 1895525 = 355411) (by norm_num)
theorem B1895597 : Blo 842353 1895597 := bbase (se 3 (by rfl) ⟨355424, by rfl⟩ : syracuseStep 1895597 = 710849) (by norm_num)
theorem B1600717 : Blo 842353 1600717 := bbase (se 3 (by rfl) ⟨300134, by rfl⟩ : syracuseStep 1600717 = 600269) (by norm_num)
theorem B1895669 : Blo 842353 1895669 := bbase (se 5 (by rfl) ⟨88859, by rfl⟩ : syracuseStep 1895669 = 177719) (by norm_num)
theorem B1895741 : Blo 842353 1895741 := bbase (se 3 (by rfl) ⟨355451, by rfl⟩ : syracuseStep 1895741 = 710903) (by norm_num)
theorem B1600877 : Blo 842353 1600877 := bbase (se 3 (by rfl) ⟨300164, by rfl⟩ : syracuseStep 1600877 = 600329) (by norm_num)
theorem B2846069 : Blo 842353 2846069 := bbase (se 5 (by rfl) ⟨133409, by rfl⟩ : syracuseStep 2846069 = 266819) (by norm_num)
theorem B1895813 : Blo 842353 1895813 := bbase (se 4 (by rfl) ⟨177732, by rfl⟩ : syracuseStep 1895813 = 355465) (by norm_num)
theorem B9498005 : Blo 842353 9498005 := bbase (se 6 (by rfl) ⟨222609, by rfl⟩ : syracuseStep 9498005 = 445219) (by norm_num)
theorem B1895885 : Blo 842353 1895885 := bbase (se 3 (by rfl) ⟨355478, by rfl⟩ : syracuseStep 1895885 = 710957) (by norm_num)
theorem B2026957 : Blo 842353 2026957 := bbase (se 3 (by rfl) ⟨380054, by rfl⟩ : syracuseStep 2026957 = 760109) (by norm_num)
theorem B1601021 : Blo 842353 1601021 := bbase (se 3 (by rfl) ⟨300191, by rfl⟩ : syracuseStep 1601021 = 600383) (by norm_num)
theorem B1895957 : Blo 842353 1895957 := bbase (se 6 (by rfl) ⟨44436, by rfl⟩ : syracuseStep 1895957 = 88873) (by norm_num)
theorem B1896029 : Blo 842353 1896029 := bbase (se 3 (by rfl) ⟨355505, by rfl⟩ : syracuseStep 1896029 = 711011) (by norm_num)
theorem B1896101 : Blo 842353 1896101 := bbase (se 4 (by rfl) ⟨177759, by rfl⟩ : syracuseStep 1896101 = 355519) (by norm_num)
theorem B2059997 : Blo 842353 2059997 := bbase (se 3 (by rfl) ⟨386249, by rfl⟩ : syracuseStep 2059997 = 772499) (by norm_num)
theorem B1896173 : Blo 842353 1896173 := bbase (se 3 (by rfl) ⟨355532, by rfl⟩ : syracuseStep 1896173 = 711065) (by norm_num)
theorem B1601309 : Blo 842353 1601309 := bbase (se 3 (by rfl) ⟨300245, by rfl⟩ : syracuseStep 1601309 = 600491) (by norm_num)
theorem B2846501 : Blo 842353 2846501 := bbase (se 4 (by rfl) ⟨266859, by rfl⟩ : syracuseStep 2846501 = 533719) (by norm_num)
theorem B1896245 : Blo 842353 1896245 := bbase (se 5 (by rfl) ⟨88886, by rfl⟩ : syracuseStep 1896245 = 177773) (by norm_num)
theorem B3600197 : Blo 842353 3600197 := bbase (se 4 (by rfl) ⟨337518, by rfl⟩ : syracuseStep 3600197 = 675037) (by norm_num)
theorem B1896317 : Blo 842353 1896317 := bbase (se 3 (by rfl) ⟨355559, by rfl⟩ : syracuseStep 1896317 = 711119) (by norm_num)
theorem B1601461 : Blo 842353 1601461 := bbase (se 5 (by rfl) ⟨75068, by rfl⟩ : syracuseStep 1601461 = 150137) (by norm_num)
theorem B1896389 : Blo 842353 1896389 := bbase (se 4 (by rfl) ⟨177786, by rfl⟩ : syracuseStep 1896389 = 355573) (by norm_num)
theorem B1896461 : Blo 842353 1896461 := bbase (se 3 (by rfl) ⟨355586, by rfl⟩ : syracuseStep 1896461 = 711173) (by norm_num)
theorem B3207221 : Blo 842353 3207221 := bbase (se 5 (by rfl) ⟨150338, by rfl⟩ : syracuseStep 3207221 = 300677) (by norm_num)
theorem B1896533 : Blo 842353 1896533 := bbase (se 8 (by rfl) ⟨11112, by rfl⟩ : syracuseStep 1896533 = 22225) (by norm_num)
theorem B15429781 : Blo 842353 15429781 := bbase (se 6 (by rfl) ⟨361635, by rfl⟩ : syracuseStep 15429781 = 723271) (by norm_num)
theorem B1896605 : Blo 842353 1896605 := bbase (se 3 (by rfl) ⟨355613, by rfl⟩ : syracuseStep 1896605 = 711227) (by norm_num)
theorem B2846933 : Blo 842353 2846933 := bbase (se 7 (by rfl) ⟨33362, by rfl⟩ : syracuseStep 2846933 = 66725) (by norm_num)
theorem B1896677 : Blo 842353 1896677 := bbase (se 4 (by rfl) ⟨177813, by rfl⟩ : syracuseStep 1896677 = 355627) (by norm_num)
theorem B1601765 : Blo 842353 1601765 := bbase (se 4 (by rfl) ⟨150165, by rfl⟩ : syracuseStep 1601765 = 300331) (by norm_num)
theorem B913685 : Blo 842353 913685 := bbase (se 6 (by rfl) ⟨21414, by rfl⟩ : syracuseStep 913685 = 42829) (by norm_num)
theorem B1896749 : Blo 842353 1896749 := bbase (se 3 (by rfl) ⟨355640, by rfl⟩ : syracuseStep 1896749 = 711281) (by norm_num)
theorem B3207509 : Blo 842353 3207509 := bbase (se 10 (by rfl) ⟨4698, by rfl⟩ : syracuseStep 3207509 = 9397) (by norm_num)
theorem B1896821 : Blo 842353 1896821 := bbase (se 5 (by rfl) ⟨88913, by rfl⟩ : syracuseStep 1896821 = 177827) (by norm_num)
theorem B1012133 : Blo 842353 1012133 := bbase (se 4 (by rfl) ⟨94887, by rfl⟩ : syracuseStep 1012133 = 189775) (by norm_num)
theorem B1896893 : Blo 842353 1896893 := bbase (se 3 (by rfl) ⟨355667, by rfl⟩ : syracuseStep 1896893 = 711335) (by norm_num)
theorem B3043781 : Blo 842353 3043781 := bbase (se 4 (by rfl) ⟨285354, by rfl⟩ : syracuseStep 3043781 = 570709) (by norm_num)
theorem B1143277 : Blo 842353 1143277 := bbase (se 3 (by rfl) ⟨214364, by rfl⟩ : syracuseStep 1143277 = 428729) (by norm_num)
theorem B1143293 : Blo 842353 1143293 := bbase (se 3 (by rfl) ⟨214367, by rfl⟩ : syracuseStep 1143293 = 428735) (by norm_num)
theorem B1896965 : Blo 842353 1896965 := bbase (se 4 (by rfl) ⟨177840, by rfl⟩ : syracuseStep 1896965 = 355681) (by norm_num)
theorem B1143325 : Blo 842353 1143325 := bbase (se 3 (by rfl) ⟨214373, by rfl⟩ : syracuseStep 1143325 = 428747) (by norm_num)
theorem B1897037 : Blo 842353 1897037 := bbase (se 3 (by rfl) ⟨355694, by rfl⟩ : syracuseStep 1897037 = 711389) (by norm_num)
theorem B2847365 : Blo 842353 2847365 := bbase (se 4 (by rfl) ⟨266940, by rfl⟩ : syracuseStep 2847365 = 533881) (by norm_num)
theorem B1897109 : Blo 842353 1897109 := bbase (se 6 (by rfl) ⟨44463, by rfl⟩ : syracuseStep 1897109 = 88927) (by norm_num)
theorem B1012441 : Blo 842353 1012441 := bbase (se 2 (by rfl) ⟨379665, by rfl⟩ : syracuseStep 1012441 = 759331) (by norm_num)
theorem B1897181 : Blo 842353 1897181 := bbase (se 3 (by rfl) ⟨355721, by rfl⟩ : syracuseStep 1897181 = 711443) (by norm_num)
theorem B1897253 : Blo 842353 1897253 := bbase (se 4 (by rfl) ⟨177867, by rfl⟩ : syracuseStep 1897253 = 355735) (by norm_num)
theorem B3601205 : Blo 842353 3601205 := bbase (se 5 (by rfl) ⟨168806, by rfl⟩ : syracuseStep 3601205 = 337613) (by norm_num)
theorem B2028341 : Blo 842353 2028341 := bbase (se 5 (by rfl) ⟨95078, by rfl⟩ : syracuseStep 2028341 = 190157) (by norm_num)
theorem B2028349 : Blo 842353 2028349 := bbase (se 3 (by rfl) ⟨380315, by rfl⟩ : syracuseStep 2028349 = 760631) (by norm_num)
theorem B1897325 : Blo 842353 1897325 := bbase (se 3 (by rfl) ⟨355748, by rfl⟩ : syracuseStep 1897325 = 711497) (by norm_num)
theorem B1897397 : Blo 842353 1897397 := bbase (se 5 (by rfl) ⟨88940, by rfl⟩ : syracuseStep 1897397 = 177881) (by norm_num)
theorem B914377 : Blo 842353 914377 := bbase (se 2 (by rfl) ⟨342891, by rfl⟩ : syracuseStep 914377 = 685783) (by norm_num)
theorem B1602517 : Blo 842353 1602517 := bbase (se 7 (by rfl) ⟨18779, by rfl⟩ : syracuseStep 1602517 = 37559) (by norm_num)
theorem B1897469 : Blo 842353 1897469 := bbase (se 3 (by rfl) ⟨355775, by rfl⟩ : syracuseStep 1897469 = 711551) (by norm_num)
theorem B2847797 : Blo 842353 2847797 := bbase (se 5 (by rfl) ⟨133490, by rfl⟩ : syracuseStep 2847797 = 266981) (by norm_num)
theorem B1897541 : Blo 842353 1897541 := bbase (se 4 (by rfl) ⟨177894, by rfl⟩ : syracuseStep 1897541 = 355789) (by norm_num)
theorem B1012829 : Blo 842353 1012829 := bbase (se 3 (by rfl) ⟨189905, by rfl⟩ : syracuseStep 1012829 = 379811) (by norm_num)
theorem B1602661 : Blo 842353 1602661 := bbase (se 4 (by rfl) ⟨150249, by rfl⟩ : syracuseStep 1602661 = 300499) (by norm_num)
theorem B6419573 : Blo 842353 6419573 := bbase (se 5 (by rfl) ⟨300917, by rfl⟩ : syracuseStep 6419573 = 601835) (by norm_num)
theorem B1897613 : Blo 842353 1897613 := bbase (se 3 (by rfl) ⟨355802, by rfl⟩ : syracuseStep 1897613 = 711605) (by norm_num)
theorem B1897685 : Blo 842353 1897685 := bbase (se 7 (by rfl) ⟨22238, by rfl⟩ : syracuseStep 1897685 = 44477) (by norm_num)
theorem B1602821 : Blo 842353 1602821 := bbase (se 4 (by rfl) ⟨150264, by rfl⟩ : syracuseStep 1602821 = 300529) (by norm_num)
theorem B1897757 : Blo 842353 1897757 := bbase (se 3 (by rfl) ⟨355829, by rfl⟩ : syracuseStep 1897757 = 711659) (by norm_num)
theorem B1799509 : Blo 842353 1799509 := bbase (se 13 (by rfl) ⟨329, by rfl⟩ : syracuseStep 1799509 = 659) (by norm_num)
theorem B1897829 : Blo 842353 1897829 := bbase (se 4 (by rfl) ⟨177921, by rfl⟩ : syracuseStep 1897829 = 355843) (by norm_num)
theorem B1602965 : Blo 842353 1602965 := bbase (se 6 (by rfl) ⟨37569, by rfl⟩ : syracuseStep 1602965 = 75139) (by norm_num)
theorem B1897901 : Blo 842353 1897901 := bbase (se 3 (by rfl) ⟨355856, by rfl⟩ : syracuseStep 1897901 = 711713) (by norm_num)
theorem B1013185 : Blo 842353 1013185 := bbase (se 2 (by rfl) ⟨379944, by rfl⟩ : syracuseStep 1013185 = 759889) (by norm_num)
theorem B947677 : Blo 842353 947677 := bbase (se 3 (by rfl) ⟨177689, by rfl⟩ : syracuseStep 947677 = 355379) (by norm_num)
theorem B2848229 : Blo 842353 2848229 := bbase (se 4 (by rfl) ⟨267021, by rfl⟩ : syracuseStep 2848229 = 534043) (by norm_num)
theorem B1897973 : Blo 842353 1897973 := bbase (se 5 (by rfl) ⟨88967, by rfl⟩ : syracuseStep 1897973 = 177935) (by norm_num)
theorem B3208693 : Blo 842353 3208693 := bbase (se 5 (by rfl) ⟨150407, by rfl⟩ : syracuseStep 3208693 = 300815) (by norm_num)
theorem B947713 : Blo 842353 947713 := bbase (se 2 (by rfl) ⟨355392, by rfl⟩ : syracuseStep 947713 = 710785) (by norm_num)
theorem B947749 : Blo 842353 947749 := bbase (se 4 (by rfl) ⟨88851, by rfl⟩ : syracuseStep 947749 = 177703) (by norm_num)
theorem B1898045 : Blo 842353 1898045 := bbase (se 3 (by rfl) ⟨355883, by rfl⟩ : syracuseStep 1898045 = 711767) (by norm_num)
theorem B947785 : Blo 842353 947785 := bbase (se 2 (by rfl) ⟨355419, by rfl⟩ : syracuseStep 947785 = 710839) (by norm_num)
theorem B947821 : Blo 842353 947821 := bbase (se 3 (by rfl) ⟨177716, by rfl⟩ : syracuseStep 947821 = 355433) (by norm_num)
theorem B1898117 : Blo 842353 1898117 := bbase (se 4 (by rfl) ⟨177948, by rfl⟩ : syracuseStep 1898117 = 355897) (by norm_num)
theorem B947857 : Blo 842353 947857 := bbase (se 2 (by rfl) ⟨355446, by rfl⟩ : syracuseStep 947857 = 710893) (by norm_num)
theorem B915101 : Blo 842353 915101 := bbase (se 3 (by rfl) ⟨171581, by rfl⟩ : syracuseStep 915101 = 343163) (by norm_num)
theorem B947893 : Blo 842353 947893 := bbase (se 5 (by rfl) ⟨44432, by rfl⟩ : syracuseStep 947893 = 88865) (by norm_num)
theorem B1603253 : Blo 842353 1603253 := bbase (se 5 (by rfl) ⟨75152, by rfl⟩ : syracuseStep 1603253 = 150305) (by norm_num)
theorem B1898189 : Blo 842353 1898189 := bbase (se 3 (by rfl) ⟨355910, by rfl⟩ : syracuseStep 1898189 = 711821) (by norm_num)
theorem B947929 : Blo 842353 947929 := bbase (se 2 (by rfl) ⟨355473, by rfl⟩ : syracuseStep 947929 = 710947) (by norm_num)
theorem B1373917 : Blo 842353 1373917 := bbase (se 3 (by rfl) ⟨257609, by rfl⟩ : syracuseStep 1373917 = 515219) (by norm_num)
theorem B947965 : Blo 842353 947965 := bbase (se 3 (by rfl) ⟨177743, by rfl⟩ : syracuseStep 947965 = 355487) (by norm_num)
theorem B1013521 : Blo 842353 1013521 := bbase (se 2 (by rfl) ⟨380070, by rfl⟩ : syracuseStep 1013521 = 760141) (by norm_num)
theorem B1898261 : Blo 842353 1898261 := bbase (se 6 (by rfl) ⟨44490, by rfl⟩ : syracuseStep 1898261 = 88981) (by norm_num)
theorem B948001 : Blo 842353 948001 := bbase (se 2 (by rfl) ⟨355500, by rfl⟩ : syracuseStep 948001 = 711001) (by norm_num)
theorem B2029349 : Blo 842353 2029349 := bbase (se 4 (by rfl) ⟨190251, by rfl⟩ : syracuseStep 2029349 = 380503) (by norm_num)
theorem B3208997 : Blo 842353 3208997 := bbase (se 4 (by rfl) ⟨300843, by rfl⟩ : syracuseStep 3208997 = 601687) (by norm_num)
theorem B948037 : Blo 842353 948037 := bbase (se 4 (by rfl) ⟨88878, by rfl⟩ : syracuseStep 948037 = 177757) (by norm_num)
theorem B1603405 : Blo 842353 1603405 := bbase (se 3 (by rfl) ⟨300638, by rfl⟩ : syracuseStep 1603405 = 601277) (by norm_num)
theorem B1898333 : Blo 842353 1898333 := bbase (se 3 (by rfl) ⟨355937, by rfl⟩ : syracuseStep 1898333 = 711875) (by norm_num)
theorem B948073 : Blo 842353 948073 := bbase (se 2 (by rfl) ⟨355527, by rfl⟩ : syracuseStep 948073 = 711055) (by norm_num)
theorem B948109 : Blo 842353 948109 := bbase (se 3 (by rfl) ⟨177770, by rfl⟩ : syracuseStep 948109 = 355541) (by norm_num)
theorem B2848661 : Blo 842353 2848661 := bbase (se 6 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 2848661 = 133531) (by norm_num)
theorem B1898405 : Blo 842353 1898405 := bbase (se 4 (by rfl) ⟨177975, by rfl⟩ : syracuseStep 1898405 = 355951) (by norm_num)
theorem B948145 : Blo 842353 948145 := bbase (se 2 (by rfl) ⟨355554, by rfl⟩ : syracuseStep 948145 = 711109) (by norm_num)
theorem B948181 : Blo 842353 948181 := bbase (se 7 (by rfl) ⟨11111, by rfl⟩ : syracuseStep 948181 = 22223) (by norm_num)
theorem B1898477 : Blo 842353 1898477 := bbase (se 3 (by rfl) ⟨355964, by rfl⟩ : syracuseStep 1898477 = 711929) (by norm_num)
theorem B948217 : Blo 842353 948217 := bbase (se 2 (by rfl) ⟨355581, by rfl⟩ : syracuseStep 948217 = 711163) (by norm_num)
theorem B948253 : Blo 842353 948253 := bbase (se 3 (by rfl) ⟨177797, by rfl⟩ : syracuseStep 948253 = 355595) (by norm_num)
theorem B1898549 : Blo 842353 1898549 := bbase (se 5 (by rfl) ⟨88994, by rfl⟩ : syracuseStep 1898549 = 177989) (by norm_num)
theorem B948289 : Blo 842353 948289 := bbase (se 2 (by rfl) ⟨355608, by rfl⟩ : syracuseStep 948289 = 711217) (by norm_num)
theorem B948325 : Blo 842353 948325 := bbase (se 4 (by rfl) ⟨88905, by rfl⟩ : syracuseStep 948325 = 177811) (by norm_num)
theorem B1898621 : Blo 842353 1898621 := bbase (se 3 (by rfl) ⟨355991, by rfl⟩ : syracuseStep 1898621 = 711983) (by norm_num)
theorem B1603709 : Blo 842353 1603709 := bbase (se 3 (by rfl) ⟨300695, by rfl⟩ : syracuseStep 1603709 = 601391) (by norm_num)
theorem B948361 : Blo 842353 948361 := bbase (se 2 (by rfl) ⟨355635, by rfl⟩ : syracuseStep 948361 = 711271) (by norm_num)
theorem B948397 : Blo 842353 948397 := bbase (se 3 (by rfl) ⟨177824, by rfl⟩ : syracuseStep 948397 = 355649) (by norm_num)
theorem B1898693 : Blo 842353 1898693 := bbase (se 4 (by rfl) ⟨178002, by rfl⟩ : syracuseStep 1898693 = 356005) (by norm_num)
theorem B1800397 : Blo 842353 1800397 := bbase (se 3 (by rfl) ⟨337574, by rfl⟩ : syracuseStep 1800397 = 675149) (by norm_num)
theorem B948433 : Blo 842353 948433 := bbase (se 2 (by rfl) ⟨355662, by rfl⟩ : syracuseStep 948433 = 711325) (by norm_num)
theorem B948469 : Blo 842353 948469 := bbase (se 5 (by rfl) ⟨44459, by rfl⟩ : syracuseStep 948469 = 88919) (by norm_num)
theorem B3045637 : Blo 842353 3045637 := bbase (se 4 (by rfl) ⟨285528, by rfl⟩ : syracuseStep 3045637 = 571057) (by norm_num)
theorem B1898765 : Blo 842353 1898765 := bbase (se 3 (by rfl) ⟨356018, by rfl⟩ : syracuseStep 1898765 = 712037) (by norm_num)
theorem B948505 : Blo 842353 948505 := bbase (se 2 (by rfl) ⟨355689, by rfl⟩ : syracuseStep 948505 = 711379) (by norm_num)
theorem B948541 : Blo 842353 948541 := bbase (se 3 (by rfl) ⟨177851, by rfl⟩ : syracuseStep 948541 = 355703) (by norm_num)
theorem B2849093 : Blo 842353 2849093 := bbase (se 4 (by rfl) ⟨267102, by rfl⟩ : syracuseStep 2849093 = 534205) (by norm_num)
theorem B1898837 : Blo 842353 1898837 := bbase (se 10 (by rfl) ⟨2781, by rfl⟩ : syracuseStep 1898837 = 5563) (by norm_num)
theorem B948577 : Blo 842353 948577 := bbase (se 2 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 948577 = 711433) (by norm_num)
theorem B948613 : Blo 842353 948613 := bbase (se 4 (by rfl) ⟨88932, by rfl⟩ : syracuseStep 948613 = 177865) (by norm_num)
theorem B1898909 : Blo 842353 1898909 := bbase (se 3 (by rfl) ⟨356045, by rfl⟩ : syracuseStep 1898909 = 712091) (by norm_num)
theorem B948649 : Blo 842353 948649 := bbase (se 2 (by rfl) ⟨355743, by rfl⟩ : syracuseStep 948649 = 711487) (by norm_num)
theorem B948685 : Blo 842353 948685 := bbase (se 3 (by rfl) ⟨177878, by rfl⟩ : syracuseStep 948685 = 355757) (by norm_num)
theorem B1898981 : Blo 842353 1898981 := bbase (se 4 (by rfl) ⟨178029, by rfl⟩ : syracuseStep 1898981 = 356059) (by norm_num)
theorem B948721 : Blo 842353 948721 := bbase (se 2 (by rfl) ⟨355770, by rfl⟩ : syracuseStep 948721 = 711541) (by norm_num)
theorem B948757 : Blo 842353 948757 := bbase (se 6 (by rfl) ⟨22236, by rfl⟩ : syracuseStep 948757 = 44473) (by norm_num)
theorem B3602981 : Blo 842353 3602981 := bbase (se 4 (by rfl) ⟨337779, by rfl⟩ : syracuseStep 3602981 = 675559) (by norm_num)
theorem B2030117 : Blo 842353 2030117 := bbase (se 4 (by rfl) ⟨190323, by rfl⟩ : syracuseStep 2030117 = 380647) (by norm_num)
theorem B1899053 : Blo 842353 1899053 := bbase (se 3 (by rfl) ⟨356072, by rfl⟩ : syracuseStep 1899053 = 712145) (by norm_num)
theorem B948793 : Blo 842353 948793 := bbase (se 2 (by rfl) ⟨355797, by rfl⟩ : syracuseStep 948793 = 711595) (by norm_num)
theorem B948829 : Blo 842353 948829 := bbase (se 3 (by rfl) ⟨177905, by rfl⟩ : syracuseStep 948829 = 355811) (by norm_num)
theorem B3078773 : Blo 842353 3078773 := bbase (se 5 (by rfl) ⟨144317, by rfl⟩ : syracuseStep 3078773 = 288635) (by norm_num)
theorem B1899125 : Blo 842353 1899125 := bbase (se 5 (by rfl) ⟨89021, by rfl⟩ : syracuseStep 1899125 = 178043) (by norm_num)
theorem B948865 : Blo 842353 948865 := bbase (se 2 (by rfl) ⟨355824, by rfl⟩ : syracuseStep 948865 = 711649) (by norm_num)
theorem B1014401 : Blo 842353 1014401 := bbase (se 2 (by rfl) ⟨380400, by rfl⟩ : syracuseStep 1014401 = 760801) (by norm_num)
theorem B948901 : Blo 842353 948901 := bbase (se 4 (by rfl) ⟨88959, by rfl⟩ : syracuseStep 948901 = 177919) (by norm_num)
theorem B1800893 : Blo 842353 1800893 := bbase (se 3 (by rfl) ⟨337667, by rfl⟩ : syracuseStep 1800893 = 675335) (by norm_num)
theorem B1899197 : Blo 842353 1899197 := bbase (se 3 (by rfl) ⟨356099, by rfl⟩ : syracuseStep 1899197 = 712199) (by norm_num)
theorem B948937 : Blo 842353 948937 := bbase (se 2 (by rfl) ⟨355851, by rfl⟩ : syracuseStep 948937 = 711703) (by norm_num)
theorem B948973 : Blo 842353 948973 := bbase (se 3 (by rfl) ⟨177932, by rfl⟩ : syracuseStep 948973 = 355865) (by norm_num)
theorem B2849525 : Blo 842353 2849525 := bbase (se 5 (by rfl) ⟨133571, by rfl⟩ : syracuseStep 2849525 = 267143) (by norm_num)
theorem B1899269 : Blo 842353 1899269 := bbase (se 4 (by rfl) ⟨178056, by rfl⟩ : syracuseStep 1899269 = 356113) (by norm_num)
theorem B949009 : Blo 842353 949009 := bbase (se 2 (by rfl) ⟨355878, by rfl⟩ : syracuseStep 949009 = 711757) (by norm_num)
theorem B949045 : Blo 842353 949045 := bbase (se 5 (by rfl) ⟨44486, by rfl⟩ : syracuseStep 949045 = 88973) (by norm_num)
theorem B1899341 : Blo 842353 1899341 := bbase (se 3 (by rfl) ⟨356126, by rfl⟩ : syracuseStep 1899341 = 712253) (by norm_num)
theorem B949081 : Blo 842353 949081 := bbase (se 2 (by rfl) ⟨355905, by rfl⟩ : syracuseStep 949081 = 711811) (by norm_num)
theorem B1604461 : Blo 842353 1604461 := bbase (se 3 (by rfl) ⟨300836, by rfl⟩ : syracuseStep 1604461 = 601673) (by norm_num)
theorem B949117 : Blo 842353 949117 := bbase (se 3 (by rfl) ⟨177959, by rfl⟩ : syracuseStep 949117 = 355919) (by norm_num)
theorem B1899413 : Blo 842353 1899413 := bbase (se 6 (by rfl) ⟨44517, by rfl⟩ : syracuseStep 1899413 = 89035) (by norm_num)
theorem B949153 : Blo 842353 949153 := bbase (se 2 (by rfl) ⟨355932, by rfl⟩ : syracuseStep 949153 = 711865) (by norm_num)
theorem B1014709 : Blo 842353 1014709 := bbase (se 5 (by rfl) ⟨47564, by rfl⟩ : syracuseStep 1014709 = 95129) (by norm_num)
theorem B949189 : Blo 842353 949189 := bbase (se 4 (by rfl) ⟨88986, by rfl⟩ : syracuseStep 949189 = 177973) (by norm_num)
theorem B1899485 : Blo 842353 1899485 := bbase (se 3 (by rfl) ⟨356153, by rfl⟩ : syracuseStep 1899485 = 712307) (by norm_num)
theorem B949225 : Blo 842353 949225 := bbase (se 2 (by rfl) ⟨355959, by rfl⟩ : syracuseStep 949225 = 711919) (by norm_num)
theorem B1604605 : Blo 842353 1604605 := bbase (se 3 (by rfl) ⟨300863, by rfl⟩ : syracuseStep 1604605 = 601727) (by norm_num)
theorem B949261 : Blo 842353 949261 := bbase (se 3 (by rfl) ⟨177986, by rfl⟩ : syracuseStep 949261 = 355973) (by norm_num)
theorem B1899557 : Blo 842353 1899557 := bbase (se 4 (by rfl) ⟨178083, by rfl⟩ : syracuseStep 1899557 = 356167) (by norm_num)
theorem B949297 : Blo 842353 949297 := bbase (se 2 (by rfl) ⟨355986, by rfl⟩ : syracuseStep 949297 = 711973) (by norm_num)
theorem B949333 : Blo 842353 949333 := bbase (se 8 (by rfl) ⟨5562, by rfl⟩ : syracuseStep 949333 = 11125) (by norm_num)
theorem B1899629 : Blo 842353 1899629 := bbase (se 3 (by rfl) ⟨356180, by rfl⟩ : syracuseStep 1899629 = 712361) (by norm_num)
theorem B949369 : Blo 842353 949369 := bbase (se 2 (by rfl) ⟨356013, by rfl⟩ : syracuseStep 949369 = 712027) (by norm_num)
theorem B949405 : Blo 842353 949405 := bbase (se 3 (by rfl) ⟨178013, by rfl⟩ : syracuseStep 949405 = 356027) (by norm_num)
theorem B1604765 : Blo 842353 1604765 := bbase (se 3 (by rfl) ⟨300893, by rfl⟩ : syracuseStep 1604765 = 601787) (by norm_num)
theorem B2849957 : Blo 842353 2849957 := bbase (se 4 (by rfl) ⟨267183, by rfl⟩ : syracuseStep 2849957 = 534367) (by norm_num)
theorem B1899701 : Blo 842353 1899701 := bbase (se 5 (by rfl) ⟨89048, by rfl⟩ : syracuseStep 1899701 = 178097) (by norm_num)
theorem B949441 : Blo 842353 949441 := bbase (se 2 (by rfl) ⟨356040, by rfl⟩ : syracuseStep 949441 = 712081) (by norm_num)
theorem B949477 : Blo 842353 949477 := bbase (se 4 (by rfl) ⟨89013, by rfl⟩ : syracuseStep 949477 = 178027) (by norm_num)
theorem B1899773 : Blo 842353 1899773 := bbase (se 3 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 1899773 = 712415) (by norm_num)
theorem B949513 : Blo 842353 949513 := bbase (se 2 (by rfl) ⟨356067, by rfl⟩ : syracuseStep 949513 = 712135) (by norm_num)
theorem B949549 : Blo 842353 949549 := bbase (se 3 (by rfl) ⟨178040, by rfl⟩ : syracuseStep 949549 = 356081) (by norm_num)
theorem B1604909 : Blo 842353 1604909 := bbase (se 3 (by rfl) ⟨300920, by rfl⟩ : syracuseStep 1604909 = 601841) (by norm_num)
theorem B1015093 : Blo 842353 1015093 := bbase (se 5 (by rfl) ⟨47582, by rfl⟩ : syracuseStep 1015093 = 95165) (by norm_num)
theorem B1015097 : Blo 842353 1015097 := bbase (se 2 (by rfl) ⟨380661, by rfl⟩ : syracuseStep 1015097 = 761323) (by norm_num)
theorem B1899845 : Blo 842353 1899845 := bbase (se 4 (by rfl) ⟨178110, by rfl⟩ : syracuseStep 1899845 = 356221) (by norm_num)
theorem B949585 : Blo 842353 949585 := bbase (se 2 (by rfl) ⟨356094, by rfl⟩ : syracuseStep 949585 = 712189) (by norm_num)
theorem B949621 : Blo 842353 949621 := bbase (se 5 (by rfl) ⟨44513, by rfl⟩ : syracuseStep 949621 = 89027) (by norm_num)
theorem B4062581 : Blo 842353 4062581 := bbase (se 5 (by rfl) ⟨190433, by rfl⟩ : syracuseStep 4062581 = 380867) (by norm_num)
theorem B1899917 : Blo 842353 1899917 := bbase (se 3 (by rfl) ⟨356234, by rfl⟩ : syracuseStep 1899917 = 712469) (by norm_num)
theorem B949657 : Blo 842353 949657 := bbase (se 2 (by rfl) ⟨356121, by rfl⟩ : syracuseStep 949657 = 712243) (by norm_num)
theorem B949693 : Blo 842353 949693 := bbase (se 3 (by rfl) ⟨178067, by rfl⟩ : syracuseStep 949693 = 356135) (by norm_num)
theorem B1899989 : Blo 842353 1899989 := bbase (se 7 (by rfl) ⟨22265, by rfl⟩ : syracuseStep 1899989 = 44531) (by norm_num)
theorem B949729 : Blo 842353 949729 := bbase (se 2 (by rfl) ⟨356148, by rfl⟩ : syracuseStep 949729 = 712297) (by norm_num)
theorem B949765 : Blo 842353 949765 := bbase (se 4 (by rfl) ⟨89040, by rfl⟩ : syracuseStep 949765 = 178081) (by norm_num)
theorem B1900061 : Blo 842353 1900061 := bbase (se 3 (by rfl) ⟨356261, by rfl⟩ : syracuseStep 1900061 = 712523) (by norm_num)
theorem B949801 : Blo 842353 949801 := bbase (se 2 (by rfl) ⟨356175, by rfl⟩ : syracuseStep 949801 = 712351) (by norm_num)
theorem B1801781 : Blo 842353 1801781 := bbase (se 5 (by rfl) ⟨84458, by rfl⟩ : syracuseStep 1801781 = 168917) (by norm_num)
theorem B949837 : Blo 842353 949837 := bbase (se 3 (by rfl) ⟨178094, by rfl⟩ : syracuseStep 949837 = 356189) (by norm_num)
theorem B1605197 : Blo 842353 1605197 := bbase (se 3 (by rfl) ⟨300974, by rfl⟩ : syracuseStep 1605197 = 601949) (by norm_num)
theorem B2850389 : Blo 842353 2850389 := bbase (se 8 (by rfl) ⟨16701, by rfl⟩ : syracuseStep 2850389 = 33403) (by norm_num)
theorem B1900133 : Blo 842353 1900133 := bbase (se 4 (by rfl) ⟨178137, by rfl⟩ : syracuseStep 1900133 = 356275) (by norm_num)
theorem B949873 : Blo 842353 949873 := bbase (se 2 (by rfl) ⟨356202, by rfl⟩ : syracuseStep 949873 = 712405) (by norm_num)
theorem B949909 : Blo 842353 949909 := bbase (se 6 (by rfl) ⟨22263, by rfl⟩ : syracuseStep 949909 = 44527) (by norm_num)
theorem B1801901 : Blo 842353 1801901 := bbase (se 3 (by rfl) ⟨337856, by rfl⟩ : syracuseStep 1801901 = 675713) (by norm_num)
theorem B1900205 : Blo 842353 1900205 := bbase (se 3 (by rfl) ⟨356288, by rfl⟩ : syracuseStep 1900205 = 712577) (by norm_num)
theorem B949945 : Blo 842353 949945 := bbase (se 2 (by rfl) ⟨356229, by rfl⟩ : syracuseStep 949945 = 712459) (by norm_num)
theorem B1015501 : Blo 842353 1015501 := bbase (se 3 (by rfl) ⟨190406, by rfl⟩ : syracuseStep 1015501 = 380813) (by norm_num)
theorem B949981 : Blo 842353 949981 := bbase (se 3 (by rfl) ⟨178121, by rfl⟩ : syracuseStep 949981 = 356243) (by norm_num)
theorem B1605349 : Blo 842353 1605349 := bbase (se 4 (by rfl) ⟨150501, by rfl⟩ : syracuseStep 1605349 = 301003) (by norm_num)
theorem B1900277 : Blo 842353 1900277 := bbase (se 5 (by rfl) ⟨89075, by rfl⟩ : syracuseStep 1900277 = 178151) (by norm_num)
theorem B950017 : Blo 842353 950017 := bbase (se 2 (by rfl) ⟨356256, by rfl⟩ : syracuseStep 950017 = 712513) (by norm_num)
theorem B950053 : Blo 842353 950053 := bbase (se 4 (by rfl) ⟨89067, by rfl⟩ : syracuseStep 950053 = 178135) (by norm_num)
theorem B1900349 : Blo 842353 1900349 := bbase (se 3 (by rfl) ⟨356315, by rfl⟩ : syracuseStep 1900349 = 712631) (by norm_num)
theorem B950089 : Blo 842353 950089 := bbase (se 2 (by rfl) ⟨356283, by rfl⟩ : syracuseStep 950089 = 712567) (by norm_num)
theorem B3211109 : Blo 842353 3211109 := bbase (se 4 (by rfl) ⟨301041, by rfl⟩ : syracuseStep 3211109 = 602083) (by norm_num)
theorem B950125 : Blo 842353 950125 := bbase (se 3 (by rfl) ⟨178148, by rfl⟩ : syracuseStep 950125 = 356297) (by norm_num)
theorem B1900421 : Blo 842353 1900421 := bbase (se 4 (by rfl) ⟨178164, by rfl⟩ : syracuseStep 1900421 = 356329) (by norm_num)
theorem B950161 : Blo 842353 950161 := bbase (se 2 (by rfl) ⟨356310, by rfl⟩ : syracuseStep 950161 = 712621) (by norm_num)
theorem B950197 : Blo 842353 950197 := bbase (se 5 (by rfl) ⟨44540, by rfl⟩ : syracuseStep 950197 = 89081) (by norm_num)
theorem B1900493 : Blo 842353 1900493 := bbase (se 3 (by rfl) ⟨356342, by rfl⟩ : syracuseStep 1900493 = 712685) (by norm_num)
theorem B950233 : Blo 842353 950233 := bbase (se 2 (by rfl) ⟨356337, by rfl⟩ : syracuseStep 950233 = 712675) (by norm_num)
theorem B950269 : Blo 842353 950269 := bbase (se 3 (by rfl) ⟨178175, by rfl⟩ : syracuseStep 950269 = 356351) (by norm_num)
theorem B1802243 : Blo 842353 1802243 := bstep (se 1 (by rfl) ⟨1351682, by rfl⟩ : syracuseStep 1802243 = 2703365) B2703365
theorem B1900547 : Blo 842353 1900547 := bstep (se 1 (by rfl) ⟨1425410, by rfl⟩ : syracuseStep 1900547 = 2850821) B2850821
theorem B950323 : Blo 842353 950323 := bstep (se 1 (by rfl) ⟨712742, by rfl⟩ : syracuseStep 950323 = 1425485) B1425485
theorem B2850929 : Blo 842353 2850929 := bstep (se 2 (by rfl) ⟨1069098, by rfl⟩ : syracuseStep 2850929 = 2138197) B2138197
theorem B1015939 : Blo 842353 1015939 := bstep (se 1 (by rfl) ⟨761954, by rfl⟩ : syracuseStep 1015939 = 1523909) B1523909
theorem B3604621 : Blo 842353 3604621 := bstep (se 3 (by rfl) ⟨675866, by rfl⟩ : syracuseStep 3604621 = 1351733) B1351733
theorem B3211427 : Blo 842353 3211427 := bstep (se 1 (by rfl) ⟨2408570, by rfl⟩ : syracuseStep 3211427 = 4817141) B4817141
theorem B950467 : Blo 842353 950467 := bstep (se 1 (by rfl) ⟨712850, by rfl⟩ : syracuseStep 950467 = 1425701) B1425701
theorem B1900817 : Blo 842353 1900817 := bstep (se 2 (by rfl) ⟨712806, by rfl⟩ : syracuseStep 1900817 = 1425613) B1425613
theorem B1900835 : Blo 842353 1900835 := bstep (se 1 (by rfl) ⟨1425626, by rfl⟩ : syracuseStep 1900835 = 2851253) B2851253
theorem B5144867 : Blo 842353 5144867 := bstep (se 1 (by rfl) ⟨3858650, by rfl⟩ : syracuseStep 5144867 = 7717301) B7717301
theorem B16253237 : Blo 842353 16253237 := bstep (se 5 (by rfl) ⟨761870, by rfl⟩ : syracuseStep 16253237 = 1523741) B1523741
theorem B2883917 : Blo 842353 2883917 := bstep (se 3 (by rfl) ⟨540734, by rfl⟩ : syracuseStep 2883917 = 1081469) B1081469
theorem B950611 : Blo 842353 950611 := bstep (se 1 (by rfl) ⟨712958, by rfl⟩ : syracuseStep 950611 = 1425917) B1425917
theorem B950755 : Blo 842353 950755 := bstep (se 1 (by rfl) ⟨713066, by rfl⟩ : syracuseStep 950755 = 1426133) B1426133
theorem B4817393 : Blo 842353 4817393 := bstep (se 2 (by rfl) ⟨1806522, by rfl⟩ : syracuseStep 4817393 = 3613045) B3613045
theorem B1901105 : Blo 842353 1901105 := bstep (se 2 (by rfl) ⟨712914, by rfl⟩ : syracuseStep 1901105 = 1425829) B1425829
theorem B1901123 : Blo 842353 1901123 := bstep (se 1 (by rfl) ⟨1425842, by rfl⟩ : syracuseStep 1901123 = 2851685) B2851685
theorem B5145157 : Blo 842353 5145157 := bstep (se 4 (by rfl) ⟨482358, by rfl⟩ : syracuseStep 5145157 = 964717) B964717
theorem B950899 : Blo 842353 950899 := bstep (se 1 (by rfl) ⟨713174, by rfl⟩ : syracuseStep 950899 = 1426349) B1426349
theorem B2851469 : Blo 842353 2851469 := bstep (se 3 (by rfl) ⟨534650, by rfl⟩ : syracuseStep 2851469 = 1069301) B1069301
theorem B1606321 : Blo 842353 1606321 := bstep (se 2 (by rfl) ⟨602370, by rfl⟩ : syracuseStep 1606321 = 1204741) B1204741
theorem B2851523 : Blo 842353 2851523 := bstep (se 1 (by rfl) ⟨2138642, by rfl⟩ : syracuseStep 2851523 = 4277285) B4277285
theorem B951043 : Blo 842353 951043 := bstep (se 1 (by rfl) ⟨713282, by rfl⟩ : syracuseStep 951043 = 1426565) B1426565
theorem B3212081 : Blo 842353 3212081 := bstep (se 2 (by rfl) ⟨1204530, by rfl⟩ : syracuseStep 3212081 = 2409061) B2409061
theorem B1901393 : Blo 842353 1901393 := bstep (se 2 (by rfl) ⟨713022, by rfl⟩ : syracuseStep 1901393 = 1426045) B1426045
theorem B1901411 : Blo 842353 1901411 := bstep (se 1 (by rfl) ⟨1426058, by rfl⟩ : syracuseStep 1901411 = 2852117) B2852117
theorem B951187 : Blo 842353 951187 := bstep (se 1 (by rfl) ⟨713390, by rfl⟩ : syracuseStep 951187 = 1426781) B1426781
theorem B2851793 : Blo 842353 2851793 := bstep (se 2 (by rfl) ⟨1069422, by rfl⟩ : syracuseStep 2851793 = 2138845) B2138845
theorem B951331 : Blo 842353 951331 := bstep (se 1 (by rfl) ⟨713498, by rfl⟩ : syracuseStep 951331 = 1426997) B1426997
theorem B1901681 : Blo 842353 1901681 := bstep (se 2 (by rfl) ⟨713130, by rfl⟩ : syracuseStep 1901681 = 1426261) B1426261
theorem B1901699 : Blo 842353 1901699 := bstep (se 1 (by rfl) ⟨1426274, by rfl⟩ : syracuseStep 1901699 = 2852549) B2852549
theorem B2032771 : Blo 842353 2032771 := bstep (se 1 (by rfl) ⟨1524578, by rfl⟩ : syracuseStep 2032771 = 3049157) B3049157
theorem B951475 : Blo 842353 951475 := bstep (se 1 (by rfl) ⟨713606, by rfl⟩ : syracuseStep 951475 = 1427213) B1427213
theorem B4064525 : Blo 842353 4064525 := bstep (se 3 (by rfl) ⟨762098, by rfl⟩ : syracuseStep 4064525 = 1524197) B1524197
theorem B951619 : Blo 842353 951619 := bstep (se 1 (by rfl) ⟨713714, by rfl⟩ : syracuseStep 951619 = 1427429) B1427429
theorem B3048781 : Blo 842353 3048781 := bstep (se 3 (by rfl) ⟨571646, by rfl⟩ : syracuseStep 3048781 = 1143293) B1143293
theorem B1901969 : Blo 842353 1901969 := bstep (se 2 (by rfl) ⟨713238, by rfl⟩ : syracuseStep 1901969 = 1426477) B1426477
theorem B1901987 : Blo 842353 1901987 := bstep (se 1 (by rfl) ⟨1426490, by rfl⟩ : syracuseStep 1901987 = 2852981) B2852981
theorem B5768653 : Blo 842353 5768653 := bstep (se 3 (by rfl) ⟨1081622, by rfl⟩ : syracuseStep 5768653 = 2163245) B2163245
theorem B951763 : Blo 842353 951763 := bstep (se 1 (by rfl) ⟨713822, by rfl⟩ : syracuseStep 951763 = 1427645) B1427645
theorem B2852333 : Blo 842353 2852333 := bstep (se 3 (by rfl) ⟨534812, by rfl⟩ : syracuseStep 2852333 = 1069625) B1069625
theorem B2852387 : Blo 842353 2852387 := bstep (se 1 (by rfl) ⟨2139290, by rfl⟩ : syracuseStep 2852387 = 4278581) B4278581
theorem B951907 : Blo 842353 951907 := bstep (se 1 (by rfl) ⟨713930, by rfl⟩ : syracuseStep 951907 = 1427861) B1427861
theorem B5408369 : Blo 842353 5408369 := bstep (se 2 (by rfl) ⟨2028138, by rfl⟩ : syracuseStep 5408369 = 4056277) B4056277
theorem B1902257 : Blo 842353 1902257 := bstep (se 2 (by rfl) ⟨713346, by rfl⟩ : syracuseStep 1902257 = 1426693) B1426693
theorem B1902275 : Blo 842353 1902275 := bstep (se 1 (by rfl) ⟨1426706, by rfl⟩ : syracuseStep 1902275 = 2853413) B2853413
theorem B952051 : Blo 842353 952051 := bstep (se 1 (by rfl) ⟨714038, by rfl⟩ : syracuseStep 952051 = 1428077) B1428077
theorem B2852657 : Blo 842353 2852657 := bstep (se 2 (by rfl) ⟨1069746, by rfl⟩ : syracuseStep 2852657 = 2139493) B2139493
theorem B10979171 : Blo 842353 10979171 := bstep (se 1 (by rfl) ⟨8234378, by rfl⟩ : syracuseStep 10979171 = 16468757) B16468757
theorem B6424433 : Blo 842353 6424433 := bstep (se 2 (by rfl) ⟨2409162, by rfl⟩ : syracuseStep 6424433 = 4818325) B4818325
theorem B4818851 : Blo 842353 4818851 := bstep (se 1 (by rfl) ⟨3614138, by rfl⟩ : syracuseStep 4818851 = 7228277) B7228277
theorem B1804241 : Blo 842353 1804241 := bstep (se 2 (by rfl) ⟨676590, by rfl⟩ : syracuseStep 1804241 = 1353181) B1353181
theorem B1902545 : Blo 842353 1902545 := bstep (se 2 (by rfl) ⟨713454, by rfl⟩ : syracuseStep 1902545 = 1426909) B1426909
theorem B1902563 : Blo 842353 1902563 := bstep (se 1 (by rfl) ⟨1426922, by rfl⟩ : syracuseStep 1902563 = 2853845) B2853845
theorem B1902833 : Blo 842353 1902833 := bstep (se 2 (by rfl) ⟨713562, by rfl⟩ : syracuseStep 1902833 = 1427125) B1427125
theorem B1902851 : Blo 842353 1902851 := bstep (se 1 (by rfl) ⟨1427138, by rfl⟩ : syracuseStep 1902851 = 2854277) B2854277
theorem B2853197 : Blo 842353 2853197 := bstep (se 3 (by rfl) ⟨534974, by rfl⟩ : syracuseStep 2853197 = 1069949) B1069949
theorem B2853251 : Blo 842353 2853251 := bstep (se 1 (by rfl) ⟨2139938, by rfl⟩ : syracuseStep 2853251 = 4279877) B4279877
theorem B1804771 : Blo 842353 1804771 := bstep (se 1 (by rfl) ⟨1353578, by rfl⟩ : syracuseStep 1804771 = 2707157) B2707157
theorem B1903121 : Blo 842353 1903121 := bstep (se 2 (by rfl) ⟨713670, by rfl⟩ : syracuseStep 1903121 = 1427341) B1427341
theorem B1903139 : Blo 842353 1903139 := bstep (se 1 (by rfl) ⟨1427354, by rfl⟩ : syracuseStep 1903139 = 2854709) B2854709
theorem B6097477 : Blo 842353 6097477 := bstep (se 4 (by rfl) ⟨571638, by rfl⟩ : syracuseStep 6097477 = 1143277) B1143277
theorem B2853521 : Blo 842353 2853521 := bstep (se 2 (by rfl) ⟨1070070, by rfl⟩ : syracuseStep 2853521 = 2140141) B2140141
theorem B5409443 : Blo 842353 5409443 := bstep (se 1 (by rfl) ⟨4057082, by rfl⟩ : syracuseStep 5409443 = 8114165) B8114165
theorem B6163141 : Blo 842353 6163141 := bstep (se 4 (by rfl) ⟨577794, by rfl⟩ : syracuseStep 6163141 = 1155589) B1155589
theorem B2132689 : Blo 842353 2132689 := bstep (se 2 (by rfl) ⟨799758, by rfl⟩ : syracuseStep 2132689 = 1599517) B1599517
theorem B8784611 : Blo 842353 8784611 := bstep (se 1 (by rfl) ⟨6588458, by rfl⟩ : syracuseStep 8784611 = 13176917) B13176917
theorem B1903409 : Blo 842353 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B1903427 : Blo 842353 1903427 := bstep (se 1 (by rfl) ⟨1427570, by rfl⟩ : syracuseStep 1903427 = 2855141) B2855141
theorem B6097733 : Blo 842353 6097733 := bstep (se 4 (by rfl) ⟨571662, by rfl⟩ : syracuseStep 6097733 = 1143325) B1143325
theorem B2132963 : Blo 842353 2132963 := bstep (se 1 (by rfl) ⟨1599722, by rfl⟩ : syracuseStep 2132963 = 3199445) B3199445
theorem B1903697 : Blo 842353 1903697 := bstep (se 2 (by rfl) ⟨713886, by rfl⟩ : syracuseStep 1903697 = 1427773) B1427773
theorem B8096867 : Blo 842353 8096867 := bstep (se 1 (by rfl) ⟨6072650, by rfl⟩ : syracuseStep 8096867 = 12145301) B12145301
theorem B1903715 : Blo 842353 1903715 := bstep (se 1 (by rfl) ⟨1427786, by rfl⟩ : syracuseStep 1903715 = 2855573) B2855573
theorem B7703693 : Blo 842353 7703693 := bstep (se 3 (by rfl) ⟨1444442, by rfl⟩ : syracuseStep 7703693 = 2888885) B2888885
theorem B2133155 : Blo 842353 2133155 := bstep (se 1 (by rfl) ⟨1599866, by rfl⟩ : syracuseStep 2133155 = 3199733) B3199733
theorem B2854061 : Blo 842353 2854061 := bstep (se 3 (by rfl) ⟨535136, by rfl⟩ : syracuseStep 2854061 = 1070273) B1070273
theorem B2854115 : Blo 842353 2854115 := bstep (se 1 (by rfl) ⟨2140586, by rfl⟩ : syracuseStep 2854115 = 4281173) B4281173
theorem B1903985 : Blo 842353 1903985 := bstep (se 2 (by rfl) ⟨713994, by rfl⟩ : syracuseStep 1903985 = 1427989) B1427989
theorem B1904003 : Blo 842353 1904003 := bstep (se 1 (by rfl) ⟨1428002, by rfl⟩ : syracuseStep 1904003 = 2856005) B2856005
theorem B2854385 : Blo 842353 2854385 := bstep (se 2 (by rfl) ⟨1070394, by rfl⟩ : syracuseStep 2854385 = 2140789) B2140789
theorem B1281619 : Blo 842353 1281619 := bstep (se 1 (by rfl) ⟨961214, by rfl⟩ : syracuseStep 1281619 = 1922429) B1922429
theorem B1904273 : Blo 842353 1904273 := bstep (se 2 (by rfl) ⟨714102, by rfl⟩ : syracuseStep 1904273 = 1428205) B1428205
theorem B1445537 : Blo 842353 1445537 := bstep (se 2 (by rfl) ⟨542076, by rfl⟩ : syracuseStep 1445537 = 1084153) B1084153
theorem B1904291 : Blo 842353 1904291 := bstep (se 1 (by rfl) ⟨1428218, by rfl⟩ : syracuseStep 1904291 = 2856437) B2856437
theorem B32476949 : Blo 842353 32476949 := bstep (se 6 (by rfl) ⟨761178, by rfl⟩ : syracuseStep 32476949 = 1522357) B1522357
theorem B1806257 : Blo 842353 1806257 := bstep (se 2 (by rfl) ⟨677346, by rfl⟩ : syracuseStep 1806257 = 1354693) B1354693
theorem B1806275 : Blo 842353 1806275 := bstep (se 1 (by rfl) ⟨1354706, by rfl⟩ : syracuseStep 1806275 = 2709413) B2709413
theorem B2166755 : Blo 842353 2166755 := bstep (se 1 (by rfl) ⟨1625066, by rfl⟩ : syracuseStep 2166755 = 3250133) B3250133
theorem B2854925 : Blo 842353 2854925 := bstep (se 3 (by rfl) ⟨535298, by rfl⟩ : syracuseStep 2854925 = 1070597) B1070597
theorem B2854979 : Blo 842353 2854979 := bstep (se 1 (by rfl) ⟨2141234, by rfl⟩ : syracuseStep 2854979 = 4282469) B4282469
theorem B2134097 : Blo 842353 2134097 := bstep (se 2 (by rfl) ⟨800286, by rfl⟩ : syracuseStep 2134097 = 1600573) B1600573
theorem B11571299 : Blo 842353 11571299 := bstep (se 1 (by rfl) ⟨8678474, by rfl⟩ : syracuseStep 11571299 = 17356949) B17356949
theorem B2134147 : Blo 842353 2134147 := bstep (se 1 (by rfl) ⟨1600610, by rfl⟩ : syracuseStep 2134147 = 3201221) B3201221
theorem B10293389 : Blo 842353 10293389 := bstep (se 3 (by rfl) ⟨1930010, by rfl⟩ : syracuseStep 10293389 = 3860021) B3860021
theorem B2887949 : Blo 842353 2887949 := bstep (se 3 (by rfl) ⟨541490, by rfl⟩ : syracuseStep 2887949 = 1082981) B1082981
theorem B2134289 : Blo 842353 2134289 := bstep (se 2 (by rfl) ⟨800358, by rfl⟩ : syracuseStep 2134289 = 1600717) B1600717
theorem B2855249 : Blo 842353 2855249 := bstep (se 2 (by rfl) ⟨1070718, by rfl⟩ : syracuseStep 2855249 = 2141437) B2141437
theorem B3608945 : Blo 842353 3608945 := bstep (se 2 (by rfl) ⟨1353354, by rfl⟩ : syracuseStep 3608945 = 2706709) B2706709
theorem B3608995 : Blo 842353 3608995 := bstep (se 1 (by rfl) ⟨2706746, by rfl⟩ : syracuseStep 3608995 = 5413493) B5413493
theorem B2888131 : Blo 842353 2888131 := bstep (se 1 (by rfl) ⟨2166098, by rfl⟩ : syracuseStep 2888131 = 4332197) B4332197
theorem B2167249 : Blo 842353 2167249 := bstep (se 2 (by rfl) ⟨812718, by rfl⟩ : syracuseStep 2167249 = 1625437) B1625437
theorem B1282835 : Blo 842353 1282835 := bstep (se 1 (by rfl) ⟨962126, by rfl⟩ : syracuseStep 1282835 = 1924253) B1924253
theorem B2855789 : Blo 842353 2855789 := bstep (se 3 (by rfl) ⟨535460, by rfl⟩ : syracuseStep 2855789 = 1070921) B1070921
theorem B2855843 : Blo 842353 2855843 := bstep (se 1 (by rfl) ⟨2141882, by rfl⟩ : syracuseStep 2855843 = 4283765) B4283765
theorem B9638837 : Blo 842353 9638837 := bstep (se 5 (by rfl) ⟨451820, by rfl⟩ : syracuseStep 9638837 = 903641) B903641
theorem B1446913 : Blo 842353 1446913 := bstep (se 2 (by rfl) ⟨542592, by rfl⟩ : syracuseStep 1446913 = 1085185) B1085185
theorem B4264973 : Blo 842353 4264973 := bstep (se 3 (by rfl) ⟨799682, by rfl⟩ : syracuseStep 4264973 = 1599365) B1599365
theorem B7214093 : Blo 842353 7214093 := bstep (se 3 (by rfl) ⟨1352642, by rfl⟩ : syracuseStep 7214093 = 2705285) B2705285
theorem B1807505 : Blo 842353 1807505 := bstep (se 2 (by rfl) ⟨677814, by rfl⟩ : syracuseStep 1807505 = 1355629) B1355629
theorem B2856113 : Blo 842353 2856113 := bstep (se 2 (by rfl) ⟨1071042, by rfl⟩ : syracuseStep 2856113 = 2142085) B2142085
theorem B2135281 : Blo 842353 2135281 := bstep (se 2 (by rfl) ⟨800730, by rfl⟩ : syracuseStep 2135281 = 1601461) B1601461
theorem B4560305 : Blo 842353 4560305 := bstep (se 2 (by rfl) ⟨1710114, by rfl⟩ : syracuseStep 4560305 = 3420229) B3420229
theorem B1709507 : Blo 842353 1709507 := bstep (se 1 (by rfl) ⟨1282130, by rfl⟩ : syracuseStep 1709507 = 2564261) B2564261
theorem B2135555 : Blo 842353 2135555 := bstep (se 1 (by rfl) ⟨1601666, by rfl⟩ : syracuseStep 2135555 = 3203333) B3203333
theorem B8132237 : Blo 842353 8132237 := bstep (se 3 (by rfl) ⟨1524794, by rfl⟩ : syracuseStep 8132237 = 3049589) B3049589
theorem B2135747 : Blo 842353 2135747 := bstep (se 1 (by rfl) ⟨1601810, by rfl⟩ : syracuseStep 2135747 = 3203621) B3203621
theorem B4396963 : Blo 842353 4396963 := bstep (se 1 (by rfl) ⟨3297722, by rfl⟩ : syracuseStep 4396963 = 6595445) B6595445
theorem B1284211 : Blo 842353 1284211 := bstep (se 1 (by rfl) ⟨963158, by rfl⟩ : syracuseStep 1284211 = 1926317) B1926317
theorem B1349875 : Blo 842353 1349875 := bstep (se 1 (by rfl) ⟨1012406, by rfl⟩ : syracuseStep 1349875 = 2024813) B2024813
theorem B1349921 : Blo 842353 1349921 := bstep (se 2 (by rfl) ⟨506220, by rfl⟩ : syracuseStep 1349921 = 1012441) B1012441
theorem B2169425 : Blo 842353 2169425 := bstep (se 2 (by rfl) ⟨813534, by rfl⟩ : syracuseStep 2169425 = 1627069) B1627069
theorem B1219169 : Blo 842353 1219169 := bstep (se 2 (by rfl) ⟨457188, by rfl⟩ : syracuseStep 1219169 = 914377) B914377
theorem B2136689 : Blo 842353 2136689 := bstep (se 2 (by rfl) ⟨801258, by rfl⟩ : syracuseStep 2136689 = 1602517) B1602517
theorem B11541133 : Blo 842353 11541133 := bstep (se 3 (by rfl) ⟨2163962, by rfl⟩ : syracuseStep 11541133 = 4327925) B4327925
theorem B2136739 : Blo 842353 2136739 := bstep (se 1 (by rfl) ⟨1602554, by rfl⟩ : syracuseStep 2136739 = 3205109) B3205109
theorem B5413645 : Blo 842353 5413645 := bstep (se 3 (by rfl) ⟨1015058, by rfl⟩ : syracuseStep 5413645 = 2030117) B2030117
theorem B3611405 : Blo 842353 3611405 := bstep (se 3 (by rfl) ⟨677138, by rfl⟩ : syracuseStep 3611405 = 1354277) B1354277
theorem B2136881 : Blo 842353 2136881 := bstep (se 2 (by rfl) ⟨801330, by rfl⟩ : syracuseStep 2136881 = 1602661) B1602661
theorem B4332365 : Blo 842353 4332365 := bstep (se 3 (by rfl) ⟨812318, by rfl⟩ : syracuseStep 4332365 = 1624637) B1624637
theorem B1284977 : Blo 842353 1284977 := bstep (se 2 (by rfl) ⟨481866, by rfl⟩ : syracuseStep 1284977 = 963733) B963733
theorem B1711153 : Blo 842353 1711153 := bstep (se 2 (by rfl) ⟨641682, by rfl⟩ : syracuseStep 1711153 = 1283365) B1283365
theorem B2399345 : Blo 842353 2399345 := bstep (se 2 (by rfl) ⟨899754, by rfl⟩ : syracuseStep 2399345 = 1799509) B1799509
theorem B2464913 : Blo 842353 2464913 := bstep (se 2 (by rfl) ⟨924342, by rfl⟩ : syracuseStep 2464913 = 1848685) B1848685
theorem B1350913 : Blo 842353 1350913 := bstep (se 2 (by rfl) ⟨506592, by rfl⟩ : syracuseStep 1350913 = 1013185) B1013185
theorem B6495557 : Blo 842353 6495557 := bstep (se 4 (by rfl) ⟨608958, by rfl⟩ : syracuseStep 6495557 = 1217917) B1217917
theorem B6332003 : Blo 842353 6332003 := bstep (se 1 (by rfl) ⟨4749002, by rfl⟩ : syracuseStep 6332003 = 9498005) B9498005
theorem B1351361 : Blo 842353 1351361 := bstep (se 2 (by rfl) ⟨506760, by rfl⟩ : syracuseStep 1351361 = 1013521) B1013521
theorem B2137873 : Blo 842353 2137873 := bstep (se 2 (by rfl) ⟨801702, by rfl⟩ : syracuseStep 2137873 = 1603405) B1603405
theorem B4267889 : Blo 842353 4267889 := bstep (se 2 (by rfl) ⟨1600458, by rfl⟩ : syracuseStep 4267889 = 3200917) B3200917
theorem B2400131 : Blo 842353 2400131 := bstep (se 1 (by rfl) ⟨1800098, by rfl⟩ : syracuseStep 2400131 = 3600197) B3600197
theorem B2891693 : Blo 842353 2891693 := bstep (se 3 (by rfl) ⟨542192, by rfl⟩ : syracuseStep 2891693 = 1084385) B1084385
theorem B3416077 : Blo 842353 3416077 := bstep (se 3 (by rfl) ⟨640514, by rfl⟩ : syracuseStep 3416077 = 1281029) B1281029
theorem B2138147 : Blo 842353 2138147 := bstep (se 1 (by rfl) ⟨1603610, by rfl⟩ : syracuseStep 2138147 = 3207221) B3207221
theorem B2400461 : Blo 842353 2400461 := bstep (se 3 (by rfl) ⟨450086, by rfl⟩ : syracuseStep 2400461 = 900173) B900173
theorem B2138339 : Blo 842353 2138339 := bstep (se 1 (by rfl) ⟨1603754, by rfl⟩ : syracuseStep 2138339 = 3207509) B3207509
theorem B2400529 : Blo 842353 2400529 := bstep (se 2 (by rfl) ⟨900198, by rfl⟩ : syracuseStep 2400529 = 1800397) B1800397
theorem B2400803 : Blo 842353 2400803 := bstep (se 1 (by rfl) ⟨1800602, by rfl⟩ : syracuseStep 2400803 = 3601205) B3601205
theorem B1352227 : Blo 842353 1352227 := bstep (se 1 (by rfl) ⟨1014170, by rfl⟩ : syracuseStep 1352227 = 2028341) B2028341
theorem B2892401 : Blo 842353 2892401 := bstep (se 2 (by rfl) ⟨1084650, by rfl⟩ : syracuseStep 2892401 = 2169301) B2169301
theorem B2433905 : Blo 842353 2433905 := bstep (se 2 (by rfl) ⟨912714, by rfl⟩ : syracuseStep 2433905 = 1825429) B1825429
theorem B1319825 : Blo 842353 1319825 := bstep (se 2 (by rfl) ⟨494934, by rfl⟩ : syracuseStep 1319825 = 989869) B989869
theorem B2139281 : Blo 842353 2139281 := bstep (se 2 (by rfl) ⟨802230, by rfl⟩ : syracuseStep 2139281 = 1604461) B1604461
theorem B2565283 : Blo 842353 2565283 := bstep (se 1 (by rfl) ⟨1923962, by rfl⟩ : syracuseStep 2565283 = 3847925) B3847925
theorem B1352899 : Blo 842353 1352899 := bstep (se 1 (by rfl) ⟨1014674, by rfl⟩ : syracuseStep 1352899 = 2029349) B2029349
theorem B2139331 : Blo 842353 2139331 := bstep (se 1 (by rfl) ⟨1604498, by rfl⟩ : syracuseStep 2139331 = 3208997) B3208997
theorem B1352945 : Blo 842353 1352945 := bstep (se 2 (by rfl) ⟨507354, by rfl⟩ : syracuseStep 1352945 = 1014709) B1014709
theorem B4269347 : Blo 842353 4269347 := bstep (se 1 (by rfl) ⟨3202010, by rfl⟩ : syracuseStep 4269347 = 6404021) B6404021
theorem B2139473 : Blo 842353 2139473 := bstep (se 2 (by rfl) ⟨802302, by rfl⟩ : syracuseStep 2139473 = 1604605) B1604605
theorem B2401645 : Blo 842353 2401645 := bstep (se 3 (by rfl) ⟨450308, by rfl⟩ : syracuseStep 2401645 = 900617) B900617
theorem B2401805 : Blo 842353 2401805 := bstep (se 3 (by rfl) ⟨450338, by rfl⟩ : syracuseStep 2401805 = 900677) B900677
theorem B5777029 : Blo 842353 5777029 := bstep (se 4 (by rfl) ⟨541596, by rfl⟩ : syracuseStep 5777029 = 1083193) B1083193
theorem B2401987 : Blo 842353 2401987 := bstep (se 1 (by rfl) ⟨1801490, by rfl⟩ : syracuseStep 2401987 = 3602981) B3602981
theorem B1353457 : Blo 842353 1353457 := bstep (se 2 (by rfl) ⟨507546, by rfl⟩ : syracuseStep 1353457 = 1015093) B1015093
theorem B2467757 : Blo 842353 2467757 := bstep (se 3 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 2467757 = 925409) B925409
theorem B4270157 : Blo 842353 4270157 := bstep (se 3 (by rfl) ⟨800654, by rfl⟩ : syracuseStep 4270157 = 1601309) B1601309
theorem B26683505 : Blo 842353 26683505 := bstep (se 2 (by rfl) ⟨10006314, by rfl⟩ : syracuseStep 26683505 = 20012629) B20012629
theorem B1354001 : Blo 842353 1354001 := bstep (se 2 (by rfl) ⟨507750, by rfl⟩ : syracuseStep 1354001 = 1015501) B1015501
theorem B2140465 : Blo 842353 2140465 := bstep (se 2 (by rfl) ⟨802674, by rfl⟩ : syracuseStep 2140465 = 1605349) B1605349
theorem B2140739 : Blo 842353 2140739 := bstep (se 1 (by rfl) ⟨1605554, by rfl⟩ : syracuseStep 2140739 = 3211109) B3211109
theorem B2140931 : Blo 842353 2140931 := bstep (se 1 (by rfl) ⟨1605698, by rfl⟩ : syracuseStep 2140931 = 3211397) B3211397
theorem B2566961 : Blo 842353 2566961 := bstep (se 2 (by rfl) ⟨962610, by rfl⟩ : syracuseStep 2566961 = 1925221) B1925221
theorem B21900145 : Blo 842353 21900145 := bstep (se 2 (by rfl) ⟨8212554, by rfl⟩ : syracuseStep 21900145 = 16425109) B16425109
theorem B2403377 : Blo 842353 2403377 := bstep (se 2 (by rfl) ⟨901266, by rfl⟩ : syracuseStep 2403377 = 1802533) B1802533
theorem B1354963 : Blo 842353 1354963 := bstep (se 1 (by rfl) ⟨1016222, by rfl⟩ : syracuseStep 1354963 = 2032445) B2032445
theorem B2436493 : Blo 842353 2436493 := bstep (se 3 (by rfl) ⟨456842, by rfl⟩ : syracuseStep 2436493 = 913685) B913685
theorem B1355219 : Blo 842353 1355219 := bstep (se 1 (by rfl) ⟨1016414, by rfl⟩ : syracuseStep 1355219 = 2032829) B2032829
theorem B2600579 : Blo 842353 2600579 := bstep (se 1 (by rfl) ⟨1950434, by rfl⟩ : syracuseStep 2600579 = 3900869) B3900869
theorem B2141873 : Blo 842353 2141873 := bstep (se 2 (by rfl) ⟨803202, by rfl⟩ : syracuseStep 2141873 = 1606405) B1606405
theorem B2141923 : Blo 842353 2141923 := bstep (se 1 (by rfl) ⟨1606442, by rfl⟩ : syracuseStep 2141923 = 3212885) B3212885
theorem B2699021 : Blo 842353 2699021 := bstep (se 3 (by rfl) ⟨506066, by rfl⟩ : syracuseStep 2699021 = 1012133) B1012133
theorem B2142065 : Blo 842353 2142065 := bstep (se 2 (by rfl) ⟨803274, by rfl⟩ : syracuseStep 2142065 = 1606549) B1606549
theorem B2600867 : Blo 842353 2600867 := bstep (se 1 (by rfl) ⟨1950650, by rfl⟩ : syracuseStep 2600867 = 3901301) B3901301
theorem B2404333 : Blo 842353 2404333 := bstep (se 3 (by rfl) ⟨450812, by rfl⟩ : syracuseStep 2404333 = 901625) B901625
theorem B1421489 : Blo 842353 1421489 := bstep (se 2 (by rfl) ⟨533058, by rfl⟩ : syracuseStep 1421489 = 1066117) B1066117
theorem B2404561 : Blo 842353 2404561 := bstep (se 2 (by rfl) ⟨901710, by rfl⟩ : syracuseStep 2404561 = 1803421) B1803421
theorem B1421617 : Blo 842353 1421617 := bstep (se 2 (by rfl) ⟨533106, by rfl⟩ : syracuseStep 1421617 = 1066213) B1066213
theorem B1421651 : Blo 842353 1421651 := bstep (se 1 (by rfl) ⟨1066238, by rfl⟩ : syracuseStep 1421651 = 2132477) B2132477
theorem B2404721 : Blo 842353 2404721 := bstep (se 2 (by rfl) ⟨901770, by rfl⟩ : syracuseStep 2404721 = 1803541) B1803541
theorem B11121077 : Blo 842353 11121077 := bstep (se 5 (by rfl) ⟨521300, by rfl⟩ : syracuseStep 11121077 = 1042601) B1042601
theorem B1421779 : Blo 842353 1421779 := bstep (se 1 (by rfl) ⟨1066334, by rfl⟩ : syracuseStep 1421779 = 2132669) B2132669
theorem B4108771 : Blo 842353 4108771 := bstep (se 1 (by rfl) ⟨3081578, by rfl⟩ : syracuseStep 4108771 = 6163157) B6163157
theorem B2404835 : Blo 842353 2404835 := bstep (se 1 (by rfl) ⟨1803626, by rfl⟩ : syracuseStep 2404835 = 3607253) B3607253
theorem B1421921 : Blo 842353 1421921 := bstep (se 2 (by rfl) ⟨533220, by rfl⟩ : syracuseStep 1421921 = 1066441) B1066441
theorem B6861509 : Blo 842353 6861509 := bstep (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) B1286533
theorem B12366533 : Blo 842353 12366533 := bstep (se 4 (by rfl) ⟨1159362, by rfl⟩ : syracuseStep 12366533 = 2318725) B2318725
theorem B1422049 : Blo 842353 1422049 := bstep (se 2 (by rfl) ⟨533268, by rfl⟩ : syracuseStep 1422049 = 1066537) B1066537
theorem B9614051 : Blo 842353 9614051 := bstep (se 1 (by rfl) ⟨7210538, by rfl⟩ : syracuseStep 9614051 = 14421077) B14421077
theorem B1422083 : Blo 842353 1422083 := bstep (se 1 (by rfl) ⟨1066562, by rfl⟩ : syracuseStep 1422083 = 2133125) B2133125
theorem B1422211 : Blo 842353 1422211 := bstep (se 1 (by rfl) ⟨1066658, by rfl⟩ : syracuseStep 1422211 = 2133317) B2133317
theorem B4273073 : Blo 842353 4273073 := bstep (se 2 (by rfl) ⟨1602402, by rfl⟩ : syracuseStep 4273073 = 3204805) B3204805
theorem B1422353 : Blo 842353 1422353 := bstep (se 2 (by rfl) ⟨533382, by rfl⟩ : syracuseStep 1422353 = 1066765) B1066765
theorem B1422481 : Blo 842353 1422481 := bstep (se 2 (by rfl) ⟨533430, by rfl⟩ : syracuseStep 1422481 = 1066861) B1066861
theorem B1422515 : Blo 842353 1422515 := bstep (se 1 (by rfl) ⟨1066886, by rfl⟩ : syracuseStep 1422515 = 2133773) B2133773
theorem B6075589 : Blo 842353 6075589 := bstep (se 4 (by rfl) ⟨569586, by rfl⟩ : syracuseStep 6075589 = 1139173) B1139173
theorem B4797731 : Blo 842353 4797731 := bstep (se 1 (by rfl) ⟨3598298, by rfl⟩ : syracuseStep 4797731 = 7196597) B7196597
theorem B1520945 : Blo 842353 1520945 := bstep (se 2 (by rfl) ⟨570354, by rfl⟩ : syracuseStep 1520945 = 1140709) B1140709
theorem B1422643 : Blo 842353 1422643 := bstep (se 1 (by rfl) ⟨1066982, by rfl⟩ : syracuseStep 1422643 = 2133965) B2133965
theorem B5420465 : Blo 842353 5420465 := bstep (se 2 (by rfl) ⟨2032674, by rfl⟩ : syracuseStep 5420465 = 4065349) B4065349
theorem B1422785 : Blo 842353 1422785 := bstep (se 2 (by rfl) ⟨533544, by rfl⟩ : syracuseStep 1422785 = 1067089) B1067089
theorem B2405837 : Blo 842353 2405837 := bstep (se 3 (by rfl) ⟨451094, by rfl⟩ : syracuseStep 2405837 = 902189) B902189
theorem B1422913 : Blo 842353 1422913 := bstep (se 2 (by rfl) ⟨533592, by rfl⟩ : syracuseStep 1422913 = 1067185) B1067185
theorem B2700877 : Blo 842353 2700877 := bstep (se 3 (by rfl) ⟨506414, by rfl⟩ : syracuseStep 2700877 = 1012829) B1012829
theorem B1422947 : Blo 842353 1422947 := bstep (se 1 (by rfl) ⟨1067210, by rfl⟩ : syracuseStep 1422947 = 2134421) B2134421
theorem B2406019 : Blo 842353 2406019 := bstep (se 1 (by rfl) ⟨1804514, by rfl⟩ : syracuseStep 2406019 = 3609029) B3609029
theorem B1423075 : Blo 842353 1423075 := bstep (se 1 (by rfl) ⟨1067306, by rfl⟩ : syracuseStep 1423075 = 2134613) B2134613
theorem B2406179 : Blo 842353 2406179 := bstep (se 1 (by rfl) ⟨1804634, by rfl⟩ : syracuseStep 2406179 = 3609269) B3609269
theorem B1423217 : Blo 842353 1423217 := bstep (se 2 (by rfl) ⟨533706, by rfl⟩ : syracuseStep 1423217 = 1067413) B1067413
theorem B2570147 : Blo 842353 2570147 := bstep (se 1 (by rfl) ⟨1927610, by rfl⟩ : syracuseStep 2570147 = 3855221) B3855221
theorem B10827701 : Blo 842353 10827701 := bstep (se 5 (by rfl) ⟨507548, by rfl⟩ : syracuseStep 10827701 = 1015097) B1015097
theorem B5421005 : Blo 842353 5421005 := bstep (se 3 (by rfl) ⟨1016438, by rfl⟩ : syracuseStep 5421005 = 2032877) B2032877
theorem B1423345 : Blo 842353 1423345 := bstep (se 2 (by rfl) ⟨533754, by rfl⟩ : syracuseStep 1423345 = 1067509) B1067509
theorem B1423379 : Blo 842353 1423379 := bstep (se 1 (by rfl) ⟨1067534, by rfl⟩ : syracuseStep 1423379 = 2135069) B2135069
theorem B1423507 : Blo 842353 1423507 := bstep (se 1 (by rfl) ⟨1067630, by rfl⟩ : syracuseStep 1423507 = 2135261) B2135261
theorem B1423649 : Blo 842353 1423649 := bstep (se 2 (by rfl) ⟨533868, by rfl⟩ : syracuseStep 1423649 = 1067737) B1067737
theorem B13678901 : Blo 842353 13678901 := bstep (se 5 (by rfl) ⟨641198, by rfl⟩ : syracuseStep 13678901 = 1282397) B1282397
theorem B4274531 : Blo 842353 4274531 := bstep (se 1 (by rfl) ⟨3205898, by rfl⟩ : syracuseStep 4274531 = 6411797) B6411797
theorem B1423777 : Blo 842353 1423777 := bstep (se 2 (by rfl) ⟨533916, by rfl⟩ : syracuseStep 1423777 = 1067833) B1067833
theorem B1423811 : Blo 842353 1423811 := bstep (se 1 (by rfl) ⟨1067858, by rfl⟩ : syracuseStep 1423811 = 2135717) B2135717
theorem B1423939 : Blo 842353 1423939 := bstep (se 1 (by rfl) ⟨1067954, by rfl⟩ : syracuseStep 1423939 = 2135909) B2135909
theorem B1424081 : Blo 842353 1424081 := bstep (se 2 (by rfl) ⟨534030, by rfl⟩ : syracuseStep 1424081 = 1068061) B1068061
theorem B1424209 : Blo 842353 1424209 := bstep (se 2 (by rfl) ⟨534078, by rfl⟩ : syracuseStep 1424209 = 1068157) B1068157
theorem B2407249 : Blo 842353 2407249 := bstep (se 2 (by rfl) ⟨902718, by rfl⟩ : syracuseStep 2407249 = 1805437) B1805437
theorem B1424243 : Blo 842353 1424243 := bstep (se 1 (by rfl) ⟨1068182, by rfl⟩ : syracuseStep 1424243 = 2136365) B2136365
theorem B900019 : Blo 842353 900019 := bstep (se 1 (by rfl) ⟨675014, by rfl⟩ : syracuseStep 900019 = 1350029) B1350029
theorem B1424371 : Blo 842353 1424371 := bstep (se 1 (by rfl) ⟨1068278, by rfl⟩ : syracuseStep 1424371 = 2136557) B2136557
theorem B1424513 : Blo 842353 1424513 := bstep (se 2 (by rfl) ⟨534192, by rfl⟩ : syracuseStep 1424513 = 1068385) B1068385
theorem B4275341 : Blo 842353 4275341 := bstep (se 3 (by rfl) ⟨801626, by rfl⟩ : syracuseStep 4275341 = 1603253) B1603253
theorem B3128483 : Blo 842353 3128483 := bstep (se 1 (by rfl) ⟨2346362, by rfl⟩ : syracuseStep 3128483 = 4692725) B4692725
theorem B2079971 : Blo 842353 2079971 := bstep (se 1 (by rfl) ⟨1559978, by rfl⟩ : syracuseStep 2079971 = 3119957) B3119957
theorem B1424641 : Blo 842353 1424641 := bstep (se 2 (by rfl) ⟨534240, by rfl⟩ : syracuseStep 1424641 = 1068481) B1068481
theorem B2702609 : Blo 842353 2702609 := bstep (se 2 (by rfl) ⟨1013478, by rfl⟩ : syracuseStep 2702609 = 2026957) B2026957
theorem B1424675 : Blo 842353 1424675 := bstep (se 1 (by rfl) ⟨1068506, by rfl⟩ : syracuseStep 1424675 = 2137013) B2137013
theorem B1424803 : Blo 842353 1424803 := bstep (se 1 (by rfl) ⟨1068602, by rfl⟩ : syracuseStep 1424803 = 2137205) B2137205
theorem B1523107 : Blo 842353 1523107 := bstep (se 1 (by rfl) ⟨1142330, by rfl⟩ : syracuseStep 1523107 = 2284661) B2284661
theorem B1424945 : Blo 842353 1424945 := bstep (se 2 (by rfl) ⟨534354, by rfl⟩ : syracuseStep 1424945 = 1068709) B1068709
theorem B2276963 : Blo 842353 2276963 := bstep (se 1 (by rfl) ⟨1707722, by rfl⟩ : syracuseStep 2276963 = 3415445) B3415445
theorem B1425073 : Blo 842353 1425073 := bstep (se 2 (by rfl) ⟨534402, by rfl⟩ : syracuseStep 1425073 = 1068805) B1068805
theorem B1425107 : Blo 842353 1425107 := bstep (se 1 (by rfl) ⟨1068830, by rfl⟩ : syracuseStep 1425107 = 2137661) B2137661
theorem B1425235 : Blo 842353 1425235 := bstep (se 1 (by rfl) ⟨1068926, by rfl⟩ : syracuseStep 1425235 = 2137853) B2137853
theorem B2703235 : Blo 842353 2703235 := bstep (se 1 (by rfl) ⟨2027426, by rfl⟩ : syracuseStep 2703235 = 4054853) B4054853
theorem B901027 : Blo 842353 901027 := bstep (se 1 (by rfl) ⟨675770, by rfl⟩ : syracuseStep 901027 = 1351541) B1351541
theorem B30883781 : Blo 842353 30883781 := bstep (se 4 (by rfl) ⟨2895354, by rfl⟩ : syracuseStep 30883781 = 5790709) B5790709
theorem B1425377 : Blo 842353 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B2408525 : Blo 842353 2408525 := bstep (se 3 (by rfl) ⟨451598, by rfl⟩ : syracuseStep 2408525 = 903197) B903197
theorem B1425505 : Blo 842353 1425505 := bstep (se 2 (by rfl) ⟨534564, by rfl⟩ : syracuseStep 1425505 = 1069129) B1069129
theorem B6078563 : Blo 842353 6078563 := bstep (se 1 (by rfl) ⟨4558922, by rfl⟩ : syracuseStep 6078563 = 9117845) B9117845
theorem B1425539 : Blo 842353 1425539 := bstep (se 1 (by rfl) ⟨1069154, by rfl⟩ : syracuseStep 1425539 = 2138309) B2138309
theorem B3653837 : Blo 842353 3653837 := bstep (se 3 (by rfl) ⟨685094, by rfl⟩ : syracuseStep 3653837 = 1370189) B1370189
theorem B1425667 : Blo 842353 1425667 := bstep (se 1 (by rfl) ⟨1069250, by rfl⟩ : syracuseStep 1425667 = 2138501) B2138501
theorem B2408707 : Blo 842353 2408707 := bstep (se 1 (by rfl) ⟨1806530, by rfl⟩ : syracuseStep 2408707 = 3613061) B3613061
theorem B2408753 : Blo 842353 2408753 := bstep (se 2 (by rfl) ⟨903282, by rfl⟩ : syracuseStep 2408753 = 1806565) B1806565
theorem B16695665 : Blo 842353 16695665 := bstep (se 2 (by rfl) ⟨6260874, by rfl⟩ : syracuseStep 16695665 = 12521749) B12521749
theorem B1425809 : Blo 842353 1425809 := bstep (se 2 (by rfl) ⟨534678, by rfl⟩ : syracuseStep 1425809 = 1069357) B1069357
theorem B1425937 : Blo 842353 1425937 := bstep (se 2 (by rfl) ⟨534726, by rfl⟩ : syracuseStep 1425937 = 1069453) B1069453
theorem B1425971 : Blo 842353 1425971 := bstep (se 1 (by rfl) ⟨1069478, by rfl⟩ : syracuseStep 1425971 = 2138957) B2138957
theorem B1426099 : Blo 842353 1426099 := bstep (se 1 (by rfl) ⟨1069574, by rfl⟩ : syracuseStep 1426099 = 2139149) B2139149
theorem B1426241 : Blo 842353 1426241 := bstep (se 2 (by rfl) ⟨534840, by rfl⟩ : syracuseStep 1426241 = 1069681) B1069681
theorem B902035 : Blo 842353 902035 := bstep (se 1 (by rfl) ⟨676526, by rfl⟩ : syracuseStep 902035 = 1353053) B1353053
theorem B1426369 : Blo 842353 1426369 := bstep (se 2 (by rfl) ⟨534888, by rfl⟩ : syracuseStep 1426369 = 1069777) B1069777
theorem B1426403 : Blo 842353 1426403 := bstep (se 1 (by rfl) ⟨1069802, by rfl⟩ : syracuseStep 1426403 = 2139605) B2139605
theorem B2704465 : Blo 842353 2704465 := bstep (se 2 (by rfl) ⟨1014174, by rfl⟩ : syracuseStep 2704465 = 2028349) B2028349
theorem B1426531 : Blo 842353 1426531 := bstep (se 1 (by rfl) ⟨1069898, by rfl⟩ : syracuseStep 1426531 = 2139797) B2139797
theorem B2573507 : Blo 842353 2573507 := bstep (se 1 (by rfl) ⟨1930130, by rfl⟩ : syracuseStep 2573507 = 3860261) B3860261
theorem B1426673 : Blo 842353 1426673 := bstep (se 2 (by rfl) ⟨535002, by rfl⟩ : syracuseStep 1426673 = 1070005) B1070005
theorem B2573603 : Blo 842353 2573603 := bstep (se 1 (by rfl) ⟨1930202, by rfl⟩ : syracuseStep 2573603 = 3860405) B3860405
theorem B1951025 : Blo 842353 1951025 := bstep (se 2 (by rfl) ⟨731634, by rfl⟩ : syracuseStep 1951025 = 1463269) B1463269
theorem B1426801 : Blo 842353 1426801 := bstep (se 2 (by rfl) ⟨535050, by rfl⟩ : syracuseStep 1426801 = 1070101) B1070101
theorem B1426835 : Blo 842353 1426835 := bstep (se 1 (by rfl) ⟨1070126, by rfl⟩ : syracuseStep 1426835 = 2140253) B2140253
theorem B902659 : Blo 842353 902659 := bstep (se 1 (by rfl) ⟨676994, by rfl⟩ : syracuseStep 902659 = 1353989) B1353989
theorem B1426963 : Blo 842353 1426963 := bstep (se 1 (by rfl) ⟨1070222, by rfl⟩ : syracuseStep 1426963 = 2140445) B2140445
theorem B2606627 : Blo 842353 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B1066547 : Blo 842353 1066547 := bstep (se 1 (by rfl) ⟨799910, by rfl⟩ : syracuseStep 1066547 = 1599821) B1599821
theorem B1427105 : Blo 842353 1427105 := bstep (se 2 (by rfl) ⟨535164, by rfl⟩ : syracuseStep 1427105 = 1070329) B1070329
theorem B4048547 : Blo 842353 4048547 := bstep (se 1 (by rfl) ⟨3036410, by rfl⟩ : syracuseStep 4048547 = 6072821) B6072821
theorem B2705069 : Blo 842353 2705069 := bstep (se 3 (by rfl) ⟨507200, by rfl⟩ : syracuseStep 2705069 = 1014401) B1014401
theorem B2279117 : Blo 842353 2279117 := bstep (se 3 (by rfl) ⟨427334, by rfl⟩ : syracuseStep 2279117 = 854669) B854669
theorem B1427233 : Blo 842353 1427233 := bstep (se 2 (by rfl) ⟨535212, by rfl⟩ : syracuseStep 1427233 = 1070425) B1070425
theorem B1427267 : Blo 842353 1427267 := bstep (se 1 (by rfl) ⟨1070450, by rfl⟩ : syracuseStep 1427267 = 2140901) B2140901
theorem B2279299 : Blo 842353 2279299 := bstep (se 1 (by rfl) ⟨1709474, by rfl⟩ : syracuseStep 2279299 = 3418949) B3418949
theorem B1263539 : Blo 842353 1263539 := bstep (se 1 (by rfl) ⟨947654, by rfl⟩ : syracuseStep 1263539 = 1895309) B1895309
theorem B1427395 : Blo 842353 1427395 := bstep (se 1 (by rfl) ⟨1070546, by rfl⟩ : syracuseStep 1427395 = 2141093) B2141093
theorem B1263569 : Blo 842353 1263569 := bstep (se 2 (by rfl) ⟨473838, by rfl⟩ : syracuseStep 1263569 = 947677) B947677
theorem B1263587 : Blo 842353 1263587 := bstep (se 1 (by rfl) ⟨947690, by rfl⟩ : syracuseStep 1263587 = 1895381) B1895381
theorem B4278257 : Blo 842353 4278257 := bstep (se 2 (by rfl) ⟨1604346, by rfl⟩ : syracuseStep 4278257 = 3208693) B3208693
theorem B1263617 : Blo 842353 1263617 := bstep (se 2 (by rfl) ⟨473856, by rfl⟩ : syracuseStep 1263617 = 947713) B947713
theorem B1263635 : Blo 842353 1263635 := bstep (se 1 (by rfl) ⟨947726, by rfl⟩ : syracuseStep 1263635 = 1895453) B1895453
theorem B1263665 : Blo 842353 1263665 := bstep (se 2 (by rfl) ⟨473874, by rfl⟩ : syracuseStep 1263665 = 947749) B947749
theorem B1263683 : Blo 842353 1263683 := bstep (se 1 (by rfl) ⟨947762, by rfl⟩ : syracuseStep 1263683 = 1895525) B1895525
theorem B1427537 : Blo 842353 1427537 := bstep (se 2 (by rfl) ⟨535326, by rfl⟩ : syracuseStep 1427537 = 1070653) B1070653
theorem B1263713 : Blo 842353 1263713 := bstep (se 2 (by rfl) ⟨473892, by rfl⟩ : syracuseStep 1263713 = 947785) B947785
theorem B1263731 : Blo 842353 1263731 := bstep (se 1 (by rfl) ⟨947798, by rfl⟩ : syracuseStep 1263731 = 1895597) B1895597
theorem B1263761 : Blo 842353 1263761 := bstep (se 2 (by rfl) ⟨473910, by rfl⟩ : syracuseStep 1263761 = 947821) B947821
theorem B1263779 : Blo 842353 1263779 := bstep (se 1 (by rfl) ⟨947834, by rfl⟩ : syracuseStep 1263779 = 1895669) B1895669
theorem B1263809 : Blo 842353 1263809 := bstep (se 2 (by rfl) ⟨473928, by rfl⟩ : syracuseStep 1263809 = 947857) B947857
theorem B1427665 : Blo 842353 1427665 := bstep (se 2 (by rfl) ⟨535374, by rfl⟩ : syracuseStep 1427665 = 1070749) B1070749
theorem B1263827 : Blo 842353 1263827 := bstep (se 1 (by rfl) ⟨947870, by rfl⟩ : syracuseStep 1263827 = 1895741) B1895741
theorem B1263857 : Blo 842353 1263857 := bstep (se 2 (by rfl) ⟨473946, by rfl⟩ : syracuseStep 1263857 = 947893) B947893
theorem B1067251 : Blo 842353 1067251 := bstep (se 1 (by rfl) ⟨800438, by rfl⟩ : syracuseStep 1067251 = 1600877) B1600877
theorem B1427699 : Blo 842353 1427699 := bstep (se 1 (by rfl) ⟨1070774, by rfl⟩ : syracuseStep 1427699 = 2141549) B2141549
theorem B1263875 : Blo 842353 1263875 := bstep (se 1 (by rfl) ⟨947906, by rfl⟩ : syracuseStep 1263875 = 1895813) B1895813
theorem B4868365 : Blo 842353 4868365 := bstep (se 3 (by rfl) ⟨912818, by rfl⟩ : syracuseStep 4868365 = 1825637) B1825637
theorem B1263905 : Blo 842353 1263905 := bstep (se 2 (by rfl) ⟨473964, by rfl⟩ : syracuseStep 1263905 = 947929) B947929
theorem B1263923 : Blo 842353 1263923 := bstep (se 1 (by rfl) ⟨947942, by rfl⟩ : syracuseStep 1263923 = 1895885) B1895885
theorem B3426637 : Blo 842353 3426637 := bstep (se 3 (by rfl) ⟨642494, by rfl⟩ : syracuseStep 3426637 = 1284989) B1284989
theorem B1263953 : Blo 842353 1263953 := bstep (se 2 (by rfl) ⟨473982, by rfl⟩ : syracuseStep 1263953 = 947965) B947965
theorem B1067347 : Blo 842353 1067347 := bstep (se 1 (by rfl) ⟨800510, by rfl⟩ : syracuseStep 1067347 = 1601021) B1601021
theorem B1263971 : Blo 842353 1263971 := bstep (se 1 (by rfl) ⟨947978, by rfl⟩ : syracuseStep 1263971 = 1895957) B1895957
theorem B1427827 : Blo 842353 1427827 := bstep (se 1 (by rfl) ⟨1070870, by rfl⟩ : syracuseStep 1427827 = 2141741) B2141741
theorem B1264001 : Blo 842353 1264001 := bstep (se 2 (by rfl) ⟨474000, by rfl⟩ : syracuseStep 1264001 = 948001) B948001
theorem B1264019 : Blo 842353 1264019 := bstep (se 1 (by rfl) ⟨948014, by rfl⟩ : syracuseStep 1264019 = 1896029) B1896029
theorem B1264049 : Blo 842353 1264049 := bstep (se 2 (by rfl) ⟨474018, by rfl⟩ : syracuseStep 1264049 = 948037) B948037
theorem B1264067 : Blo 842353 1264067 := bstep (se 1 (by rfl) ⟨948050, by rfl⟩ : syracuseStep 1264067 = 1896101) B1896101
theorem B1264097 : Blo 842353 1264097 := bstep (se 2 (by rfl) ⟨474036, by rfl⟩ : syracuseStep 1264097 = 948073) B948073
theorem B1264115 : Blo 842353 1264115 := bstep (se 1 (by rfl) ⟨948086, by rfl⟩ : syracuseStep 1264115 = 1896173) B1896173
theorem B1427969 : Blo 842353 1427969 := bstep (se 2 (by rfl) ⟨535488, by rfl⟩ : syracuseStep 1427969 = 1070977) B1070977
theorem B1264145 : Blo 842353 1264145 := bstep (se 2 (by rfl) ⟨474054, by rfl⟩ : syracuseStep 1264145 = 948109) B948109
theorem B1264163 : Blo 842353 1264163 := bstep (se 1 (by rfl) ⟨948122, by rfl⟩ : syracuseStep 1264163 = 1896245) B1896245
theorem B1264193 : Blo 842353 1264193 := bstep (se 2 (by rfl) ⟨474072, by rfl⟩ : syracuseStep 1264193 = 948145) B948145
theorem B1264211 : Blo 842353 1264211 := bstep (se 1 (by rfl) ⟨948158, by rfl⟩ : syracuseStep 1264211 = 1896317) B1896317
theorem B1264241 : Blo 842353 1264241 := bstep (se 2 (by rfl) ⟨474090, by rfl⟩ : syracuseStep 1264241 = 948181) B948181
theorem B1428097 : Blo 842353 1428097 := bstep (se 2 (by rfl) ⟨535536, by rfl⟩ : syracuseStep 1428097 = 1071073) B1071073
theorem B1264259 : Blo 842353 1264259 := bstep (se 1 (by rfl) ⟨948194, by rfl⟩ : syracuseStep 1264259 = 1896389) B1896389
theorem B1264289 : Blo 842353 1264289 := bstep (se 2 (by rfl) ⟨474108, by rfl⟩ : syracuseStep 1264289 = 948217) B948217
theorem B1428131 : Blo 842353 1428131 := bstep (se 1 (by rfl) ⟨1071098, by rfl⟩ : syracuseStep 1428131 = 2142197) B2142197
theorem B1264307 : Blo 842353 1264307 := bstep (se 1 (by rfl) ⟨948230, by rfl⟩ : syracuseStep 1264307 = 1896461) B1896461
theorem B1264337 : Blo 842353 1264337 := bstep (se 2 (by rfl) ⟨474126, by rfl⟩ : syracuseStep 1264337 = 948253) B948253
theorem B1264355 : Blo 842353 1264355 := bstep (se 1 (by rfl) ⟨948266, by rfl⟩ : syracuseStep 1264355 = 1896533) B1896533
theorem B1100531 : Blo 842353 1100531 := bstep (se 1 (by rfl) ⟨825398, by rfl⟩ : syracuseStep 1100531 = 1650797) B1650797
theorem B1264385 : Blo 842353 1264385 := bstep (se 2 (by rfl) ⟨474144, by rfl⟩ : syracuseStep 1264385 = 948289) B948289
theorem B1264403 : Blo 842353 1264403 := bstep (se 1 (by rfl) ⟨948302, by rfl⟩ : syracuseStep 1264403 = 1896605) B1896605
theorem B1264433 : Blo 842353 1264433 := bstep (se 2 (by rfl) ⟨474162, by rfl⟩ : syracuseStep 1264433 = 948325) B948325
theorem B1264451 : Blo 842353 1264451 := bstep (se 1 (by rfl) ⟨948338, by rfl⟩ : syracuseStep 1264451 = 1896677) B1896677
theorem B1067843 : Blo 842353 1067843 := bstep (se 1 (by rfl) ⟨800882, by rfl⟩ : syracuseStep 1067843 = 1601765) B1601765
theorem B1264481 : Blo 842353 1264481 := bstep (se 2 (by rfl) ⟨474180, by rfl⟩ : syracuseStep 1264481 = 948361) B948361
theorem B1264499 : Blo 842353 1264499 := bstep (se 1 (by rfl) ⟨948374, by rfl⟩ : syracuseStep 1264499 = 1896749) B1896749
theorem B1264529 : Blo 842353 1264529 := bstep (se 2 (by rfl) ⟨474198, by rfl⟩ : syracuseStep 1264529 = 948397) B948397
theorem B1264547 : Blo 842353 1264547 := bstep (se 1 (by rfl) ⟨948410, by rfl⟩ : syracuseStep 1264547 = 1896821) B1896821
theorem B1264577 : Blo 842353 1264577 := bstep (se 2 (by rfl) ⟨474216, by rfl⟩ : syracuseStep 1264577 = 948433) B948433
theorem B1264595 : Blo 842353 1264595 := bstep (se 1 (by rfl) ⟨948446, by rfl⟩ : syracuseStep 1264595 = 1896893) B1896893
theorem B3656675 : Blo 842353 3656675 := bstep (se 1 (by rfl) ⟨2742506, by rfl⟩ : syracuseStep 3656675 = 5485013) B5485013
theorem B1264625 : Blo 842353 1264625 := bstep (se 2 (by rfl) ⟨474234, by rfl⟩ : syracuseStep 1264625 = 948469) B948469
theorem B1264643 : Blo 842353 1264643 := bstep (se 1 (by rfl) ⟨948482, by rfl⟩ : syracuseStep 1264643 = 1896965) B1896965
theorem B1264673 : Blo 842353 1264673 := bstep (se 2 (by rfl) ⟨474252, by rfl⟩ : syracuseStep 1264673 = 948505) B948505
theorem B1264691 : Blo 842353 1264691 := bstep (se 1 (by rfl) ⟨948518, by rfl⟩ : syracuseStep 1264691 = 1897037) B1897037
theorem B1264721 : Blo 842353 1264721 := bstep (se 2 (by rfl) ⟨474270, by rfl⟩ : syracuseStep 1264721 = 948541) B948541
theorem B1264739 : Blo 842353 1264739 := bstep (se 1 (by rfl) ⟨948554, by rfl⟩ : syracuseStep 1264739 = 1897109) B1897109
theorem B1264769 : Blo 842353 1264769 := bstep (se 2 (by rfl) ⟨474288, by rfl⟩ : syracuseStep 1264769 = 948577) B948577
theorem B1264787 : Blo 842353 1264787 := bstep (se 1 (by rfl) ⟨948590, by rfl⟩ : syracuseStep 1264787 = 1897181) B1897181
theorem B1264817 : Blo 842353 1264817 := bstep (se 2 (by rfl) ⟨474306, by rfl⟩ : syracuseStep 1264817 = 948613) B948613
theorem B1264835 : Blo 842353 1264835 := bstep (se 1 (by rfl) ⟨948626, by rfl⟩ : syracuseStep 1264835 = 1897253) B1897253
theorem B1264865 : Blo 842353 1264865 := bstep (se 2 (by rfl) ⟨474324, by rfl⟩ : syracuseStep 1264865 = 948649) B948649
theorem B1264883 : Blo 842353 1264883 := bstep (se 1 (by rfl) ⟨948662, by rfl⟩ : syracuseStep 1264883 = 1897325) B1897325
theorem B1264913 : Blo 842353 1264913 := bstep (se 2 (by rfl) ⟨474342, by rfl⟩ : syracuseStep 1264913 = 948685) B948685
theorem B1264931 : Blo 842353 1264931 := bstep (se 1 (by rfl) ⟨948698, by rfl⟩ : syracuseStep 1264931 = 1897397) B1897397
theorem B1264961 : Blo 842353 1264961 := bstep (se 2 (by rfl) ⟨474360, by rfl⟩ : syracuseStep 1264961 = 948721) B948721
theorem B1264979 : Blo 842353 1264979 := bstep (se 1 (by rfl) ⟨948734, by rfl⟩ : syracuseStep 1264979 = 1897469) B1897469
theorem B1265009 : Blo 842353 1265009 := bstep (se 2 (by rfl) ⟨474378, by rfl⟩ : syracuseStep 1265009 = 948757) B948757
theorem B1265027 : Blo 842353 1265027 := bstep (se 1 (by rfl) ⟨948770, by rfl⟩ : syracuseStep 1265027 = 1897541) B1897541
theorem B4050317 : Blo 842353 4050317 := bstep (se 3 (by rfl) ⟨759434, by rfl⟩ : syracuseStep 4050317 = 1518869) B1518869
theorem B2280845 : Blo 842353 2280845 := bstep (se 3 (by rfl) ⟨427658, by rfl⟩ : syracuseStep 2280845 = 855317) B855317
theorem B1265057 : Blo 842353 1265057 := bstep (se 2 (by rfl) ⟨474396, by rfl⟩ : syracuseStep 1265057 = 948793) B948793
theorem B4279715 : Blo 842353 4279715 := bstep (se 1 (by rfl) ⟨3209786, by rfl⟩ : syracuseStep 4279715 = 6419573) B6419573
theorem B1265075 : Blo 842353 1265075 := bstep (se 1 (by rfl) ⟨948806, by rfl⟩ : syracuseStep 1265075 = 1897613) B1897613
theorem B2280899 : Blo 842353 2280899 := bstep (se 1 (by rfl) ⟨1710674, by rfl⟩ : syracuseStep 2280899 = 3421349) B3421349
theorem B1265105 : Blo 842353 1265105 := bstep (se 2 (by rfl) ⟨474414, by rfl⟩ : syracuseStep 1265105 = 948829) B948829
theorem B1265123 : Blo 842353 1265123 := bstep (se 1 (by rfl) ⟨948842, by rfl⟩ : syracuseStep 1265123 = 1897685) B1897685
theorem B1265153 : Blo 842353 1265153 := bstep (se 2 (by rfl) ⟨474432, by rfl⟩ : syracuseStep 1265153 = 948865) B948865
theorem B1068547 : Blo 842353 1068547 := bstep (se 1 (by rfl) ⟨801410, by rfl⟩ : syracuseStep 1068547 = 1602821) B1602821
theorem B1265171 : Blo 842353 1265171 := bstep (se 1 (by rfl) ⟨948878, by rfl⟩ : syracuseStep 1265171 = 1897757) B1897757
theorem B1265201 : Blo 842353 1265201 := bstep (se 2 (by rfl) ⟨474450, by rfl⟩ : syracuseStep 1265201 = 948901) B948901
theorem B1265219 : Blo 842353 1265219 := bstep (se 1 (by rfl) ⟨948914, by rfl⟩ : syracuseStep 1265219 = 1897829) B1897829
theorem B1265249 : Blo 842353 1265249 := bstep (se 2 (by rfl) ⟨474468, by rfl⟩ : syracuseStep 1265249 = 948937) B948937
theorem B1068643 : Blo 842353 1068643 := bstep (se 1 (by rfl) ⟨801482, by rfl⟩ : syracuseStep 1068643 = 1602965) B1602965
theorem B1199729 : Blo 842353 1199729 := bstep (se 2 (by rfl) ⟨449898, by rfl⟩ : syracuseStep 1199729 = 899797) B899797
theorem B1265267 : Blo 842353 1265267 := bstep (se 1 (by rfl) ⟨948950, by rfl⟩ : syracuseStep 1265267 = 1897901) B1897901
theorem B1265297 : Blo 842353 1265297 := bstep (se 2 (by rfl) ⟨474486, by rfl⟩ : syracuseStep 1265297 = 948973) B948973
theorem B1265315 : Blo 842353 1265315 := bstep (se 1 (by rfl) ⟨948986, by rfl⟩ : syracuseStep 1265315 = 1897973) B1897973
theorem B1199809 : Blo 842353 1199809 := bstep (se 2 (by rfl) ⟨449928, by rfl⟩ : syracuseStep 1199809 = 899857) B899857
theorem B1265345 : Blo 842353 1265345 := bstep (se 2 (by rfl) ⟨474504, by rfl⟩ : syracuseStep 1265345 = 949009) B949009
theorem B1265363 : Blo 842353 1265363 := bstep (se 1 (by rfl) ⟨949022, by rfl⟩ : syracuseStep 1265363 = 1898045) B1898045
theorem B46157525 : Blo 842353 46157525 := bstep (se 7 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 46157525 = 1081817) B1081817
theorem B1265393 : Blo 842353 1265393 := bstep (se 2 (by rfl) ⟨474522, by rfl⟩ : syracuseStep 1265393 = 949045) B949045
theorem B1265411 : Blo 842353 1265411 := bstep (se 1 (by rfl) ⟨949058, by rfl⟩ : syracuseStep 1265411 = 1898117) B1898117
theorem B4050701 : Blo 842353 4050701 := bstep (se 3 (by rfl) ⟨759506, by rfl⟩ : syracuseStep 4050701 = 1519013) B1519013
theorem B1265441 : Blo 842353 1265441 := bstep (se 2 (by rfl) ⟨474540, by rfl⟩ : syracuseStep 1265441 = 949081) B949081
theorem B1265459 : Blo 842353 1265459 := bstep (se 1 (by rfl) ⟨949094, by rfl⟩ : syracuseStep 1265459 = 1898189) B1898189
theorem B1265489 : Blo 842353 1265489 := bstep (se 2 (by rfl) ⟨474558, by rfl⟩ : syracuseStep 1265489 = 949117) B949117
theorem B1265507 : Blo 842353 1265507 := bstep (se 1 (by rfl) ⟨949130, by rfl⟩ : syracuseStep 1265507 = 1898261) B1898261
theorem B1265537 : Blo 842353 1265537 := bstep (se 2 (by rfl) ⟨474576, by rfl⟩ : syracuseStep 1265537 = 949153) B949153
theorem B1265555 : Blo 842353 1265555 := bstep (se 1 (by rfl) ⟨949166, by rfl⟩ : syracuseStep 1265555 = 1898333) B1898333
theorem B1265585 : Blo 842353 1265585 := bstep (se 2 (by rfl) ⟨474594, by rfl⟩ : syracuseStep 1265585 = 949189) B949189
theorem B1265603 : Blo 842353 1265603 := bstep (se 1 (by rfl) ⟨949202, by rfl⟩ : syracuseStep 1265603 = 1898405) B1898405
theorem B1265633 : Blo 842353 1265633 := bstep (se 2 (by rfl) ⟨474612, by rfl⟩ : syracuseStep 1265633 = 949225) B949225
theorem B1265651 : Blo 842353 1265651 := bstep (se 1 (by rfl) ⟨949238, by rfl⟩ : syracuseStep 1265651 = 1898477) B1898477
theorem B1265681 : Blo 842353 1265681 := bstep (se 2 (by rfl) ⟨474630, by rfl⟩ : syracuseStep 1265681 = 949261) B949261
theorem B1265699 : Blo 842353 1265699 := bstep (se 1 (by rfl) ⟨949274, by rfl⟩ : syracuseStep 1265699 = 1898549) B1898549
theorem B1265729 : Blo 842353 1265729 := bstep (se 2 (by rfl) ⟨474648, by rfl⟩ : syracuseStep 1265729 = 949297) B949297
theorem B1265747 : Blo 842353 1265747 := bstep (se 1 (by rfl) ⟨949310, by rfl⟩ : syracuseStep 1265747 = 1898621) B1898621
theorem B1069139 : Blo 842353 1069139 := bstep (se 1 (by rfl) ⟨801854, by rfl⟩ : syracuseStep 1069139 = 1603709) B1603709
theorem B6410339 : Blo 842353 6410339 := bstep (se 1 (by rfl) ⟨4807754, by rfl⟩ : syracuseStep 6410339 = 9615509) B9615509
theorem B1265777 : Blo 842353 1265777 := bstep (se 2 (by rfl) ⟨474666, by rfl⟩ : syracuseStep 1265777 = 949333) B949333
theorem B1265795 : Blo 842353 1265795 := bstep (se 1 (by rfl) ⟨949346, by rfl⟩ : syracuseStep 1265795 = 1898693) B1898693
theorem B1265825 : Blo 842353 1265825 := bstep (se 2 (by rfl) ⟨474684, by rfl⟩ : syracuseStep 1265825 = 949369) B949369
theorem B1265843 : Blo 842353 1265843 := bstep (se 1 (by rfl) ⟨949382, by rfl⟩ : syracuseStep 1265843 = 1898765) B1898765
theorem B4280525 : Blo 842353 4280525 := bstep (se 3 (by rfl) ⟨802598, by rfl⟩ : syracuseStep 4280525 = 1605197) B1605197
theorem B1265873 : Blo 842353 1265873 := bstep (se 2 (by rfl) ⟨474702, by rfl⟩ : syracuseStep 1265873 = 949405) B949405
theorem B1265891 : Blo 842353 1265891 := bstep (se 1 (by rfl) ⟨949418, by rfl⟩ : syracuseStep 1265891 = 1898837) B1898837
theorem B1265921 : Blo 842353 1265921 := bstep (se 2 (by rfl) ⟨474720, by rfl⟩ : syracuseStep 1265921 = 949441) B949441
theorem B1265939 : Blo 842353 1265939 := bstep (se 1 (by rfl) ⟨949454, by rfl⟩ : syracuseStep 1265939 = 1898909) B1898909
theorem B1265969 : Blo 842353 1265969 := bstep (se 2 (by rfl) ⟨474738, by rfl⟩ : syracuseStep 1265969 = 949477) B949477
theorem B1265987 : Blo 842353 1265987 := bstep (se 1 (by rfl) ⟨949490, by rfl⟩ : syracuseStep 1265987 = 1898981) B1898981
theorem B1266017 : Blo 842353 1266017 := bstep (se 2 (by rfl) ⟨474756, by rfl⟩ : syracuseStep 1266017 = 949513) B949513
theorem B1266035 : Blo 842353 1266035 := bstep (se 1 (by rfl) ⟨949526, by rfl⟩ : syracuseStep 1266035 = 1899053) B1899053
theorem B1266065 : Blo 842353 1266065 := bstep (se 2 (by rfl) ⟨474774, by rfl⟩ : syracuseStep 1266065 = 949549) B949549
theorem B2052515 : Blo 842353 2052515 := bstep (se 1 (by rfl) ⟨1539386, by rfl⟩ : syracuseStep 2052515 = 3078773) B3078773
theorem B1266083 : Blo 842353 1266083 := bstep (se 1 (by rfl) ⟨949562, by rfl⟩ : syracuseStep 1266083 = 1899125) B1899125
theorem B1266113 : Blo 842353 1266113 := bstep (se 2 (by rfl) ⟨474792, by rfl⟩ : syracuseStep 1266113 = 949585) B949585
theorem B1200595 : Blo 842353 1200595 := bstep (se 1 (by rfl) ⟨900446, by rfl⟩ : syracuseStep 1200595 = 1800893) B1800893
theorem B1266131 : Blo 842353 1266131 := bstep (se 1 (by rfl) ⟨949598, by rfl⟩ : syracuseStep 1266131 = 1899197) B1899197
theorem B3199459 : Blo 842353 3199459 := bstep (se 1 (by rfl) ⟨2399594, by rfl⟩ : syracuseStep 3199459 = 4799189) B4799189
theorem B1266161 : Blo 842353 1266161 := bstep (se 2 (by rfl) ⟨474810, by rfl⟩ : syracuseStep 1266161 = 949621) B949621
theorem B1266179 : Blo 842353 1266179 := bstep (se 1 (by rfl) ⟨949634, by rfl⟩ : syracuseStep 1266179 = 1899269) B1899269
theorem B1266209 : Blo 842353 1266209 := bstep (se 2 (by rfl) ⟨474828, by rfl⟩ : syracuseStep 1266209 = 949657) B949657
theorem B1266227 : Blo 842353 1266227 := bstep (se 1 (by rfl) ⟨949670, by rfl⟩ : syracuseStep 1266227 = 1899341) B1899341
theorem B5493325 : Blo 842353 5493325 := bstep (se 3 (by rfl) ⟨1029998, by rfl⟩ : syracuseStep 5493325 = 2059997) B2059997
theorem B1266257 : Blo 842353 1266257 := bstep (se 2 (by rfl) ⟨474846, by rfl⟩ : syracuseStep 1266257 = 949693) B949693
theorem B2740835 : Blo 842353 2740835 := bstep (se 1 (by rfl) ⟨2055626, by rfl⟩ : syracuseStep 2740835 = 4111253) B4111253
theorem B1266275 : Blo 842353 1266275 := bstep (se 1 (by rfl) ⟨949706, by rfl⟩ : syracuseStep 1266275 = 1899413) B1899413
theorem B1266305 : Blo 842353 1266305 := bstep (se 2 (by rfl) ⟨474864, by rfl⟩ : syracuseStep 1266305 = 949729) B949729
theorem B1266323 : Blo 842353 1266323 := bstep (se 1 (by rfl) ⟨949742, by rfl⟩ : syracuseStep 1266323 = 1899485) B1899485
theorem B1266353 : Blo 842353 1266353 := bstep (se 2 (by rfl) ⟨474882, by rfl⟩ : syracuseStep 1266353 = 949765) B949765
theorem B1266371 : Blo 842353 1266371 := bstep (se 1 (by rfl) ⟨949778, by rfl⟩ : syracuseStep 1266371 = 1899557) B1899557
theorem B1266401 : Blo 842353 1266401 := bstep (se 2 (by rfl) ⟨474900, by rfl⟩ : syracuseStep 1266401 = 949801) B949801
theorem B1266419 : Blo 842353 1266419 := bstep (se 1 (by rfl) ⟨949814, by rfl⟩ : syracuseStep 1266419 = 1899629) B1899629
theorem B1266449 : Blo 842353 1266449 := bstep (se 2 (by rfl) ⟨474918, by rfl⟩ : syracuseStep 1266449 = 949837) B949837
theorem B1069843 : Blo 842353 1069843 := bstep (se 1 (by rfl) ⟨802382, by rfl⟩ : syracuseStep 1069843 = 1604765) B1604765
theorem B1266467 : Blo 842353 1266467 := bstep (se 1 (by rfl) ⟨949850, by rfl⟩ : syracuseStep 1266467 = 1899701) B1899701
theorem B1266497 : Blo 842353 1266497 := bstep (se 2 (by rfl) ⟨474936, by rfl⟩ : syracuseStep 1266497 = 949873) B949873
theorem B1266515 : Blo 842353 1266515 := bstep (se 1 (by rfl) ⟨949886, by rfl⟩ : syracuseStep 1266515 = 1899773) B1899773
theorem B1266545 : Blo 842353 1266545 := bstep (se 2 (by rfl) ⟨474954, by rfl⟩ : syracuseStep 1266545 = 949909) B949909
theorem B1069939 : Blo 842353 1069939 := bstep (se 1 (by rfl) ⟨802454, by rfl⟩ : syracuseStep 1069939 = 1604909) B1604909
theorem B1299329 : Blo 842353 1299329 := bstep (se 2 (by rfl) ⟨487248, by rfl⟩ : syracuseStep 1299329 = 974497) B974497
theorem B1266563 : Blo 842353 1266563 := bstep (se 1 (by rfl) ⟨949922, by rfl⟩ : syracuseStep 1266563 = 1899845) B1899845
theorem B1266593 : Blo 842353 1266593 := bstep (se 2 (by rfl) ⟨474972, by rfl⟩ : syracuseStep 1266593 = 949945) B949945
theorem B2708387 : Blo 842353 2708387 := bstep (se 1 (by rfl) ⟨2031290, by rfl⟩ : syracuseStep 2708387 = 4062581) B4062581
theorem B1201073 : Blo 842353 1201073 := bstep (se 2 (by rfl) ⟨450402, by rfl⟩ : syracuseStep 1201073 = 900805) B900805
theorem B1266611 : Blo 842353 1266611 := bstep (se 1 (by rfl) ⟨949958, by rfl⟩ : syracuseStep 1266611 = 1899917) B1899917
theorem B1266641 : Blo 842353 1266641 := bstep (se 2 (by rfl) ⟨474990, by rfl⟩ : syracuseStep 1266641 = 949981) B949981
theorem B1266659 : Blo 842353 1266659 := bstep (se 1 (by rfl) ⟨949994, by rfl⟩ : syracuseStep 1266659 = 1899989) B1899989
theorem B1266689 : Blo 842353 1266689 := bstep (se 2 (by rfl) ⟨475008, by rfl⟩ : syracuseStep 1266689 = 950017) B950017
theorem B1266707 : Blo 842353 1266707 := bstep (se 1 (by rfl) ⟨950030, by rfl⟩ : syracuseStep 1266707 = 1900061) B1900061
theorem B1201187 : Blo 842353 1201187 := bstep (se 1 (by rfl) ⟨900890, by rfl⟩ : syracuseStep 1201187 = 1801781) B1801781
theorem B1266737 : Blo 842353 1266737 := bstep (se 2 (by rfl) ⟨475026, by rfl⟩ : syracuseStep 1266737 = 950053) B950053
theorem B1266755 : Blo 842353 1266755 := bstep (se 1 (by rfl) ⟨950066, by rfl⟩ : syracuseStep 1266755 = 1900133) B1900133
theorem B1266785 : Blo 842353 1266785 := bstep (se 2 (by rfl) ⟨475044, by rfl⟩ : syracuseStep 1266785 = 950089) B950089
theorem B1201267 : Blo 842353 1201267 := bstep (se 1 (by rfl) ⟨900950, by rfl⟩ : syracuseStep 1201267 = 1801901) B1801901
theorem B1266803 : Blo 842353 1266803 := bstep (se 1 (by rfl) ⟨950102, by rfl⟩ : syracuseStep 1266803 = 1900205) B1900205
theorem B1266833 : Blo 842353 1266833 := bstep (se 2 (by rfl) ⟨475062, by rfl⟩ : syracuseStep 1266833 = 950125) B950125
theorem B1266851 : Blo 842353 1266851 := bstep (se 1 (by rfl) ⟨950138, by rfl⟩ : syracuseStep 1266851 = 1900277) B1900277
theorem B1266881 : Blo 842353 1266881 := bstep (se 2 (by rfl) ⟨475080, by rfl⟩ : syracuseStep 1266881 = 950161) B950161
theorem B1266899 : Blo 842353 1266899 := bstep (se 1 (by rfl) ⟨950174, by rfl⟩ : syracuseStep 1266899 = 1900349) B1900349
theorem B1266929 : Blo 842353 1266929 := bstep (se 2 (by rfl) ⟨475098, by rfl⟩ : syracuseStep 1266929 = 950197) B950197
theorem B1266947 : Blo 842353 1266947 := bstep (se 1 (by rfl) ⟨950210, by rfl⟩ : syracuseStep 1266947 = 1900421) B1900421
theorem B1266977 : Blo 842353 1266977 := bstep (se 2 (by rfl) ⟨475116, by rfl⟩ : syracuseStep 1266977 = 950233) B950233
theorem B2282801 : Blo 842353 2282801 := bstep (se 2 (by rfl) ⟨856050, by rfl⟩ : syracuseStep 2282801 = 1712101) B1712101
theorem B1266995 : Blo 842353 1266995 := bstep (se 1 (by rfl) ⟨950246, by rfl⟩ : syracuseStep 1266995 = 1900493) B1900493
theorem B1267025 : Blo 842353 1267025 := bstep (se 2 (by rfl) ⟨475134, by rfl⟩ : syracuseStep 1267025 = 950269) B950269
theorem B1267043 : Blo 842353 1267043 := bstep (se 1 (by rfl) ⟨950282, by rfl⟩ : syracuseStep 1267043 = 1900565) B1900565
theorem B1070435 : Blo 842353 1070435 := bstep (se 1 (by rfl) ⟨802826, by rfl⟩ : syracuseStep 1070435 = 1605653) B1605653
theorem B1267073 : Blo 842353 1267073 := bstep (se 2 (by rfl) ⟨475152, by rfl⟩ : syracuseStep 1267073 = 950305) B950305
theorem B1267091 : Blo 842353 1267091 := bstep (se 1 (by rfl) ⟨950318, by rfl⟩ : syracuseStep 1267091 = 1900637) B1900637
theorem B1267121 : Blo 842353 1267121 := bstep (se 2 (by rfl) ⟨475170, by rfl⟩ : syracuseStep 1267121 = 950341) B950341
theorem B1267139 : Blo 842353 1267139 := bstep (se 1 (by rfl) ⟨950354, by rfl⟩ : syracuseStep 1267139 = 1900709) B1900709
theorem B1267169 : Blo 842353 1267169 := bstep (se 2 (by rfl) ⟨475188, by rfl⟩ : syracuseStep 1267169 = 950377) B950377
theorem B1267187 : Blo 842353 1267187 := bstep (se 1 (by rfl) ⟨950390, by rfl⟩ : syracuseStep 1267187 = 1900781) B1900781
theorem B1267217 : Blo 842353 1267217 := bstep (se 2 (by rfl) ⟨475206, by rfl⟩ : syracuseStep 1267217 = 950413) B950413
theorem B1267235 : Blo 842353 1267235 := bstep (se 1 (by rfl) ⟨950426, by rfl⟩ : syracuseStep 1267235 = 1900853) B1900853
theorem B1267265 : Blo 842353 1267265 := bstep (se 2 (by rfl) ⟨475224, by rfl⟩ : syracuseStep 1267265 = 950449) B950449
theorem B1267283 : Blo 842353 1267283 := bstep (se 1 (by rfl) ⟨950462, by rfl⟩ : syracuseStep 1267283 = 1900925) B1900925
theorem B7198307 : Blo 842353 7198307 := bstep (se 1 (by rfl) ⟨5398730, by rfl⟩ : syracuseStep 7198307 = 10797461) B10797461
theorem B1267313 : Blo 842353 1267313 := bstep (se 2 (by rfl) ⟨475242, by rfl⟩ : syracuseStep 1267313 = 950485) B950485
theorem B1267331 : Blo 842353 1267331 := bstep (se 1 (by rfl) ⟨950498, by rfl⟩ : syracuseStep 1267331 = 1900997) B1900997
theorem B1201825 : Blo 842353 1201825 := bstep (se 2 (by rfl) ⟨450684, by rfl⟩ : syracuseStep 1201825 = 901369) B901369
theorem B1267361 : Blo 842353 1267361 := bstep (se 2 (by rfl) ⟨475260, by rfl⟩ : syracuseStep 1267361 = 950521) B950521
theorem B1267379 : Blo 842353 1267379 := bstep (se 1 (by rfl) ⟨950534, by rfl⟩ : syracuseStep 1267379 = 1901069) B1901069
theorem B1267409 : Blo 842353 1267409 := bstep (se 2 (by rfl) ⟨475278, by rfl⟩ : syracuseStep 1267409 = 950557) B950557
theorem B1267427 : Blo 842353 1267427 := bstep (se 1 (by rfl) ⟨950570, by rfl⟩ : syracuseStep 1267427 = 1901141) B1901141
theorem B2709233 : Blo 842353 2709233 := bstep (se 2 (by rfl) ⟨1015962, by rfl⟩ : syracuseStep 2709233 = 2031925) B2031925
theorem B1267457 : Blo 842353 1267457 := bstep (se 2 (by rfl) ⟨475296, by rfl⟩ : syracuseStep 1267457 = 950593) B950593
theorem B1267475 : Blo 842353 1267475 := bstep (se 1 (by rfl) ⟨950606, by rfl⟩ : syracuseStep 1267475 = 1901213) B1901213
theorem B2709283 : Blo 842353 2709283 := bstep (se 1 (by rfl) ⟨2031962, by rfl⟩ : syracuseStep 2709283 = 4063925) B4063925
theorem B1267505 : Blo 842353 1267505 := bstep (se 2 (by rfl) ⟨475314, by rfl⟩ : syracuseStep 1267505 = 950629) B950629
theorem B1267523 : Blo 842353 1267523 := bstep (se 1 (by rfl) ⟨950642, by rfl⟩ : syracuseStep 1267523 = 1901285) B1901285
theorem B1267553 : Blo 842353 1267553 := bstep (se 2 (by rfl) ⟨475332, by rfl⟩ : syracuseStep 1267553 = 950665) B950665
theorem B1267571 : Blo 842353 1267571 := bstep (se 1 (by rfl) ⟨950678, by rfl⟩ : syracuseStep 1267571 = 1901357) B1901357
theorem B1267601 : Blo 842353 1267601 := bstep (se 2 (by rfl) ⟨475350, by rfl⟩ : syracuseStep 1267601 = 950701) B950701
theorem B1267619 : Blo 842353 1267619 := bstep (se 1 (by rfl) ⟨950714, by rfl⟩ : syracuseStep 1267619 = 1901429) B1901429
theorem B1267649 : Blo 842353 1267649 := bstep (se 2 (by rfl) ⟨475368, by rfl⟩ : syracuseStep 1267649 = 950737) B950737
theorem B1267667 : Blo 842353 1267667 := bstep (se 1 (by rfl) ⟨950750, by rfl⟩ : syracuseStep 1267667 = 1901501) B1901501
theorem B1267697 : Blo 842353 1267697 := bstep (se 2 (by rfl) ⟨475386, by rfl⟩ : syracuseStep 1267697 = 950773) B950773
theorem B1267715 : Blo 842353 1267715 := bstep (se 1 (by rfl) ⟨950786, by rfl⟩ : syracuseStep 1267715 = 1901573) B1901573
theorem B4806661 : Blo 842353 4806661 := bstep (se 4 (by rfl) ⟨450624, by rfl⟩ : syracuseStep 4806661 = 901249) B901249
theorem B1267745 : Blo 842353 1267745 := bstep (se 2 (by rfl) ⟨475404, by rfl⟩ : syracuseStep 1267745 = 950809) B950809
theorem B1071139 : Blo 842353 1071139 := bstep (se 1 (by rfl) ⟨803354, by rfl⟩ : syracuseStep 1071139 = 1606709) B1606709
theorem B1267763 : Blo 842353 1267763 := bstep (se 1 (by rfl) ⟨950822, by rfl⟩ : syracuseStep 1267763 = 1901645) B1901645
theorem B1267793 : Blo 842353 1267793 := bstep (se 2 (by rfl) ⟨475422, by rfl⟩ : syracuseStep 1267793 = 950845) B950845
theorem B1267811 : Blo 842353 1267811 := bstep (se 1 (by rfl) ⟨950858, by rfl⟩ : syracuseStep 1267811 = 1901717) B1901717
theorem B1267841 : Blo 842353 1267841 := bstep (se 2 (by rfl) ⟨475440, by rfl⟩ : syracuseStep 1267841 = 950881) B950881
theorem B1267859 : Blo 842353 1267859 := bstep (se 1 (by rfl) ⟨950894, by rfl⟩ : syracuseStep 1267859 = 1901789) B1901789
theorem B1267889 : Blo 842353 1267889 := bstep (se 2 (by rfl) ⟨475458, by rfl⟩ : syracuseStep 1267889 = 950917) B950917
theorem B1267907 : Blo 842353 1267907 := bstep (se 1 (by rfl) ⟨950930, by rfl⟩ : syracuseStep 1267907 = 1901861) B1901861
theorem B1267937 : Blo 842353 1267937 := bstep (se 2 (by rfl) ⟨475476, by rfl⟩ : syracuseStep 1267937 = 950953) B950953
theorem B1267955 : Blo 842353 1267955 := bstep (se 1 (by rfl) ⟨950966, by rfl⟩ : syracuseStep 1267955 = 1901933) B1901933
theorem B1267985 : Blo 842353 1267985 := bstep (se 2 (by rfl) ⟨475494, by rfl⟩ : syracuseStep 1267985 = 950989) B950989
theorem B1268003 : Blo 842353 1268003 := bstep (se 1 (by rfl) ⟨951002, by rfl⟩ : syracuseStep 1268003 = 1902005) B1902005
theorem B1268033 : Blo 842353 1268033 := bstep (se 2 (by rfl) ⟨475512, by rfl⟩ : syracuseStep 1268033 = 951025) B951025
theorem B1268051 : Blo 842353 1268051 := bstep (se 1 (by rfl) ⟨951038, by rfl⟩ : syracuseStep 1268051 = 1902077) B1902077
theorem B1202531 : Blo 842353 1202531 := bstep (se 1 (by rfl) ⟨901898, by rfl⟩ : syracuseStep 1202531 = 1803797) B1803797
theorem B1268081 : Blo 842353 1268081 := bstep (se 2 (by rfl) ⟨475530, by rfl⟩ : syracuseStep 1268081 = 951061) B951061
theorem B1268099 : Blo 842353 1268099 := bstep (se 1 (by rfl) ⟨951074, by rfl⟩ : syracuseStep 1268099 = 1902149) B1902149
theorem B1268129 : Blo 842353 1268129 := bstep (se 2 (by rfl) ⟨475548, by rfl⟩ : syracuseStep 1268129 = 951097) B951097
theorem B1268147 : Blo 842353 1268147 := bstep (se 1 (by rfl) ⟨951110, by rfl⟩ : syracuseStep 1268147 = 1902221) B1902221
theorem B1268177 : Blo 842353 1268177 := bstep (se 2 (by rfl) ⟨475566, by rfl⟩ : syracuseStep 1268177 = 951133) B951133
theorem B1268195 : Blo 842353 1268195 := bstep (se 1 (by rfl) ⟨951146, by rfl⟩ : syracuseStep 1268195 = 1902293) B1902293
theorem B1268225 : Blo 842353 1268225 := bstep (se 2 (by rfl) ⟨475584, by rfl⟩ : syracuseStep 1268225 = 951169) B951169
theorem B3037709 : Blo 842353 3037709 := bstep (se 3 (by rfl) ⟨569570, by rfl⟩ : syracuseStep 3037709 = 1139141) B1139141
theorem B1268243 : Blo 842353 1268243 := bstep (se 1 (by rfl) ⟨951182, by rfl⟩ : syracuseStep 1268243 = 1902365) B1902365
theorem B1268273 : Blo 842353 1268273 := bstep (se 2 (by rfl) ⟨475602, by rfl⟩ : syracuseStep 1268273 = 951205) B951205
theorem B1268291 : Blo 842353 1268291 := bstep (se 1 (by rfl) ⟨951218, by rfl⟩ : syracuseStep 1268291 = 1902437) B1902437
theorem B1268321 : Blo 842353 1268321 := bstep (se 2 (by rfl) ⟨475620, by rfl⟩ : syracuseStep 1268321 = 951241) B951241
theorem B842355 : Blo 842353 842355 := bstep (se 1 (by rfl) ⟨631766, by rfl⟩ : syracuseStep 842355 = 1263533) B1263533
theorem B1268339 : Blo 842353 1268339 := bstep (se 1 (by rfl) ⟨951254, by rfl⟩ : syracuseStep 1268339 = 1902509) B1902509
theorem B842371 : Blo 842353 842371 := bstep (se 1 (by rfl) ⟨631778, by rfl⟩ : syracuseStep 842371 = 1263557) B1263557
theorem B3201677 : Blo 842353 3201677 := bstep (se 3 (by rfl) ⟨600314, by rfl⟩ : syracuseStep 3201677 = 1200629) B1200629
theorem B1268369 : Blo 842353 1268369 := bstep (se 2 (by rfl) ⟨475638, by rfl⟩ : syracuseStep 1268369 = 951277) B951277
theorem B842387 : Blo 842353 842387 := bstep (se 1 (by rfl) ⟨631790, by rfl⟩ : syracuseStep 842387 = 1263581) B1263581
theorem B842403 : Blo 842353 842403 := bstep (se 1 (by rfl) ⟨631802, by rfl⟩ : syracuseStep 842403 = 1263605) B1263605
theorem B1268387 : Blo 842353 1268387 := bstep (se 1 (by rfl) ⟨951290, by rfl⟩ : syracuseStep 1268387 = 1902581) B1902581
theorem B842419 : Blo 842353 842419 := bstep (se 1 (by rfl) ⟨631814, by rfl⟩ : syracuseStep 842419 = 1263629) B1263629
theorem B1268417 : Blo 842353 1268417 := bstep (se 2 (by rfl) ⟨475656, by rfl⟩ : syracuseStep 1268417 = 951313) B951313
theorem B842435 : Blo 842353 842435 := bstep (se 1 (by rfl) ⟨631826, by rfl⟩ : syracuseStep 842435 = 1263653) B1263653
theorem B842451 : Blo 842353 842451 := bstep (se 1 (by rfl) ⟨631838, by rfl⟩ : syracuseStep 842451 = 1263677) B1263677
theorem B1268435 : Blo 842353 1268435 := bstep (se 1 (by rfl) ⟨951326, by rfl⟩ : syracuseStep 1268435 = 1902653) B1902653
theorem B842467 : Blo 842353 842467 := bstep (se 1 (by rfl) ⟨631850, by rfl⟩ : syracuseStep 842467 = 1263701) B1263701
theorem B1268465 : Blo 842353 1268465 := bstep (se 2 (by rfl) ⟨475674, by rfl⟩ : syracuseStep 1268465 = 951349) B951349
theorem B842483 : Blo 842353 842483 := bstep (se 1 (by rfl) ⟨631862, by rfl⟩ : syracuseStep 842483 = 1263725) B1263725
theorem B842499 : Blo 842353 842499 := bstep (se 1 (by rfl) ⟨631874, by rfl⟩ : syracuseStep 842499 = 1263749) B1263749
theorem B1268483 : Blo 842353 1268483 := bstep (se 1 (by rfl) ⟨951362, by rfl⟩ : syracuseStep 1268483 = 1902725) B1902725
theorem B842515 : Blo 842353 842515 := bstep (se 1 (by rfl) ⟨631886, by rfl⟩ : syracuseStep 842515 = 1263773) B1263773
theorem B1268513 : Blo 842353 1268513 := bstep (se 2 (by rfl) ⟨475692, by rfl⟩ : syracuseStep 1268513 = 951385) B951385
theorem B842531 : Blo 842353 842531 := bstep (se 1 (by rfl) ⟨631898, by rfl⟩ : syracuseStep 842531 = 1263797) B1263797
theorem B842547 : Blo 842353 842547 := bstep (se 1 (by rfl) ⟨631910, by rfl⟩ : syracuseStep 842547 = 1263821) B1263821
theorem B1268531 : Blo 842353 1268531 := bstep (se 1 (by rfl) ⟨951398, by rfl⟩ : syracuseStep 1268531 = 1902797) B1902797
theorem B842563 : Blo 842353 842563 := bstep (se 1 (by rfl) ⟨631922, by rfl⟩ : syracuseStep 842563 = 1263845) B1263845
theorem B1268561 : Blo 842353 1268561 := bstep (se 2 (by rfl) ⟨475710, by rfl⟩ : syracuseStep 1268561 = 951421) B951421
theorem B842579 : Blo 842353 842579 := bstep (se 1 (by rfl) ⟨631934, by rfl⟩ : syracuseStep 842579 = 1263869) B1263869
theorem B842595 : Blo 842353 842595 := bstep (se 1 (by rfl) ⟨631946, by rfl⟩ : syracuseStep 842595 = 1263893) B1263893
theorem B1268579 : Blo 842353 1268579 := bstep (se 1 (by rfl) ⟨951434, by rfl⟩ : syracuseStep 1268579 = 1902869) B1902869
theorem B842611 : Blo 842353 842611 := bstep (se 1 (by rfl) ⟨631958, by rfl⟩ : syracuseStep 842611 = 1263917) B1263917
theorem B1268609 : Blo 842353 1268609 := bstep (se 2 (by rfl) ⟨475728, by rfl⟩ : syracuseStep 1268609 = 951457) B951457
theorem B842627 : Blo 842353 842627 := bstep (se 1 (by rfl) ⟨631970, by rfl⟩ : syracuseStep 842627 = 1263941) B1263941
theorem B842643 : Blo 842353 842643 := bstep (se 1 (by rfl) ⟨631982, by rfl⟩ : syracuseStep 842643 = 1263965) B1263965
theorem B1268627 : Blo 842353 1268627 := bstep (se 1 (by rfl) ⟨951470, by rfl⟩ : syracuseStep 1268627 = 1902941) B1902941
theorem B842659 : Blo 842353 842659 := bstep (se 1 (by rfl) ⟨631994, by rfl⟩ : syracuseStep 842659 = 1263989) B1263989
theorem B5397425 : Blo 842353 5397425 := bstep (se 2 (by rfl) ⟨2024034, by rfl⟩ : syracuseStep 5397425 = 4048069) B4048069
theorem B1268657 : Blo 842353 1268657 := bstep (se 2 (by rfl) ⟨475746, by rfl⟩ : syracuseStep 1268657 = 951493) B951493
theorem B842675 : Blo 842353 842675 := bstep (se 1 (by rfl) ⟨632006, by rfl⟩ : syracuseStep 842675 = 1264013) B1264013
theorem B842691 : Blo 842353 842691 := bstep (se 1 (by rfl) ⟨632018, by rfl⟩ : syracuseStep 842691 = 1264037) B1264037
theorem B1268675 : Blo 842353 1268675 := bstep (se 1 (by rfl) ⟨951506, by rfl⟩ : syracuseStep 1268675 = 1903013) B1903013
theorem B842707 : Blo 842353 842707 := bstep (se 1 (by rfl) ⟨632030, by rfl⟩ : syracuseStep 842707 = 1264061) B1264061
theorem B1203169 : Blo 842353 1203169 := bstep (se 2 (by rfl) ⟨451188, by rfl⟩ : syracuseStep 1203169 = 902377) B902377
theorem B1268705 : Blo 842353 1268705 := bstep (se 2 (by rfl) ⟨475764, by rfl⟩ : syracuseStep 1268705 = 951529) B951529
theorem B842723 : Blo 842353 842723 := bstep (se 1 (by rfl) ⟨632042, by rfl⟩ : syracuseStep 842723 = 1264085) B1264085
theorem B2710513 : Blo 842353 2710513 := bstep (se 2 (by rfl) ⟨1016442, by rfl⟩ : syracuseStep 2710513 = 2032885) B2032885
theorem B842739 : Blo 842353 842739 := bstep (se 1 (by rfl) ⟨632054, by rfl⟩ : syracuseStep 842739 = 1264109) B1264109
theorem B1268723 : Blo 842353 1268723 := bstep (se 1 (by rfl) ⟨951542, by rfl⟩ : syracuseStep 1268723 = 1903085) B1903085
theorem B842755 : Blo 842353 842755 := bstep (se 1 (by rfl) ⟨632066, by rfl⟩ : syracuseStep 842755 = 1264133) B1264133
theorem B1268753 : Blo 842353 1268753 := bstep (se 2 (by rfl) ⟨475782, by rfl⟩ : syracuseStep 1268753 = 951565) B951565
theorem B842771 : Blo 842353 842771 := bstep (se 1 (by rfl) ⟨632078, by rfl⟩ : syracuseStep 842771 = 1264157) B1264157
theorem B842787 : Blo 842353 842787 := bstep (se 1 (by rfl) ⟨632090, by rfl⟩ : syracuseStep 842787 = 1264181) B1264181
theorem B1268771 : Blo 842353 1268771 := bstep (se 1 (by rfl) ⟨951578, by rfl⟩ : syracuseStep 1268771 = 1903157) B1903157
theorem B1465393 : Blo 842353 1465393 := bstep (se 2 (by rfl) ⟨549522, by rfl⟩ : syracuseStep 1465393 = 1099045) B1099045
theorem B4283441 : Blo 842353 4283441 := bstep (se 2 (by rfl) ⟨1606290, by rfl⟩ : syracuseStep 4283441 = 3212581) B3212581
theorem B842803 : Blo 842353 842803 := bstep (se 1 (by rfl) ⟨632102, by rfl⟩ : syracuseStep 842803 = 1264205) B1264205
theorem B1268801 : Blo 842353 1268801 := bstep (se 2 (by rfl) ⟨475800, by rfl⟩ : syracuseStep 1268801 = 951601) B951601
theorem B842819 : Blo 842353 842819 := bstep (se 1 (by rfl) ⟨632114, by rfl⟩ : syracuseStep 842819 = 1264229) B1264229
theorem B842835 : Blo 842353 842835 := bstep (se 1 (by rfl) ⟨632126, by rfl⟩ : syracuseStep 842835 = 1264253) B1264253
theorem B1203283 : Blo 842353 1203283 := bstep (se 1 (by rfl) ⟨902462, by rfl⟩ : syracuseStep 1203283 = 1804925) B1804925
theorem B1268819 : Blo 842353 1268819 := bstep (se 1 (by rfl) ⟨951614, by rfl⟩ : syracuseStep 1268819 = 1903229) B1903229
theorem B842851 : Blo 842353 842851 := bstep (se 1 (by rfl) ⟨632138, by rfl⟩ : syracuseStep 842851 = 1264277) B1264277
theorem B1268849 : Blo 842353 1268849 := bstep (se 2 (by rfl) ⟨475818, by rfl⟩ : syracuseStep 1268849 = 951637) B951637
theorem B842867 : Blo 842353 842867 := bstep (se 1 (by rfl) ⟨632150, by rfl⟩ : syracuseStep 842867 = 1264301) B1264301
theorem B842883 : Blo 842353 842883 := bstep (se 1 (by rfl) ⟨632162, by rfl⟩ : syracuseStep 842883 = 1264325) B1264325
theorem B1268867 : Blo 842353 1268867 := bstep (se 1 (by rfl) ⟨951650, by rfl⟩ : syracuseStep 1268867 = 1903301) B1903301
theorem B842899 : Blo 842353 842899 := bstep (se 1 (by rfl) ⟨632174, by rfl⟩ : syracuseStep 842899 = 1264349) B1264349
theorem B1301665 : Blo 842353 1301665 := bstep (se 2 (by rfl) ⟨488124, by rfl⟩ : syracuseStep 1301665 = 976249) B976249
theorem B1268897 : Blo 842353 1268897 := bstep (se 2 (by rfl) ⟨475836, by rfl⟩ : syracuseStep 1268897 = 951673) B951673
theorem B842915 : Blo 842353 842915 := bstep (se 1 (by rfl) ⟨632186, by rfl⟩ : syracuseStep 842915 = 1264373) B1264373
theorem B842931 : Blo 842353 842931 := bstep (se 1 (by rfl) ⟨632198, by rfl⟩ : syracuseStep 842931 = 1264397) B1264397
theorem B1268915 : Blo 842353 1268915 := bstep (se 1 (by rfl) ⟨951686, by rfl⟩ : syracuseStep 1268915 = 1903373) B1903373
theorem B842947 : Blo 842353 842947 := bstep (se 1 (by rfl) ⟨632210, by rfl⟩ : syracuseStep 842947 = 1264421) B1264421
theorem B14277829 : Blo 842353 14277829 := bstep (se 4 (by rfl) ⟨1338546, by rfl⟩ : syracuseStep 14277829 = 2677093) B2677093
theorem B1268945 : Blo 842353 1268945 := bstep (se 2 (by rfl) ⟨475854, by rfl⟩ : syracuseStep 1268945 = 951709) B951709
theorem B842963 : Blo 842353 842963 := bstep (se 1 (by rfl) ⟨632222, by rfl⟩ : syracuseStep 842963 = 1264445) B1264445
theorem B842979 : Blo 842353 842979 := bstep (se 1 (by rfl) ⟨632234, by rfl⟩ : syracuseStep 842979 = 1264469) B1264469
theorem B2055395 : Blo 842353 2055395 := bstep (se 1 (by rfl) ⟨1541546, by rfl⟩ : syracuseStep 2055395 = 3083093) B3083093
theorem B1268963 : Blo 842353 1268963 := bstep (se 1 (by rfl) ⟨951722, by rfl⟩ : syracuseStep 1268963 = 1903445) B1903445
theorem B842995 : Blo 842353 842995 := bstep (se 1 (by rfl) ⟨632246, by rfl⟩ : syracuseStep 842995 = 1264493) B1264493
theorem B1268993 : Blo 842353 1268993 := bstep (se 2 (by rfl) ⟨475872, by rfl⟩ : syracuseStep 1268993 = 951745) B951745
theorem B843011 : Blo 842353 843011 := bstep (se 1 (by rfl) ⟨632258, by rfl⟩ : syracuseStep 843011 = 1264517) B1264517
theorem B843027 : Blo 842353 843027 := bstep (se 1 (by rfl) ⟨632270, by rfl⟩ : syracuseStep 843027 = 1264541) B1264541
theorem B1269011 : Blo 842353 1269011 := bstep (se 1 (by rfl) ⟨951758, by rfl⟩ : syracuseStep 1269011 = 1903517) B1903517
theorem B843043 : Blo 842353 843043 := bstep (se 1 (by rfl) ⟨632282, by rfl⟩ : syracuseStep 843043 = 1264565) B1264565
theorem B1269041 : Blo 842353 1269041 := bstep (se 2 (by rfl) ⟨475890, by rfl⟩ : syracuseStep 1269041 = 951781) B951781
theorem B843059 : Blo 842353 843059 := bstep (se 1 (by rfl) ⟨632294, by rfl⟩ : syracuseStep 843059 = 1264589) B1264589
theorem B843075 : Blo 842353 843075 := bstep (se 1 (by rfl) ⟨632306, by rfl⟩ : syracuseStep 843075 = 1264613) B1264613
theorem B1269059 : Blo 842353 1269059 := bstep (se 1 (by rfl) ⟨951794, by rfl⟩ : syracuseStep 1269059 = 1903589) B1903589
theorem B843091 : Blo 842353 843091 := bstep (se 1 (by rfl) ⟨632318, by rfl⟩ : syracuseStep 843091 = 1264637) B1264637
theorem B1269089 : Blo 842353 1269089 := bstep (se 2 (by rfl) ⟨475908, by rfl⟩ : syracuseStep 1269089 = 951817) B951817
theorem B843107 : Blo 842353 843107 := bstep (se 1 (by rfl) ⟨632330, by rfl⟩ : syracuseStep 843107 = 1264661) B1264661
theorem B843123 : Blo 842353 843123 := bstep (se 1 (by rfl) ⟨632342, by rfl⟩ : syracuseStep 843123 = 1264685) B1264685
theorem B1269107 : Blo 842353 1269107 := bstep (se 1 (by rfl) ⟨951830, by rfl⟩ : syracuseStep 1269107 = 1903661) B1903661
theorem B843139 : Blo 842353 843139 := bstep (se 1 (by rfl) ⟨632354, by rfl⟩ : syracuseStep 843139 = 1264709) B1264709
theorem B1269137 : Blo 842353 1269137 := bstep (se 2 (by rfl) ⟨475926, by rfl⟩ : syracuseStep 1269137 = 951853) B951853
theorem B843155 : Blo 842353 843155 := bstep (se 1 (by rfl) ⟨632366, by rfl⟩ : syracuseStep 843155 = 1264733) B1264733
theorem B843171 : Blo 842353 843171 := bstep (se 1 (by rfl) ⟨632378, by rfl⟩ : syracuseStep 843171 = 1264757) B1264757
theorem B1269155 : Blo 842353 1269155 := bstep (se 1 (by rfl) ⟨951866, by rfl⟩ : syracuseStep 1269155 = 1903733) B1903733
theorem B843187 : Blo 842353 843187 := bstep (se 1 (by rfl) ⟨632390, by rfl⟩ : syracuseStep 843187 = 1264781) B1264781
theorem B1269185 : Blo 842353 1269185 := bstep (se 2 (by rfl) ⟨475944, by rfl⟩ : syracuseStep 1269185 = 951889) B951889
theorem B843203 : Blo 842353 843203 := bstep (se 1 (by rfl) ⟨632402, by rfl⟩ : syracuseStep 843203 = 1264805) B1264805
theorem B843219 : Blo 842353 843219 := bstep (se 1 (by rfl) ⟨632414, by rfl⟩ : syracuseStep 843219 = 1264829) B1264829
theorem B1269203 : Blo 842353 1269203 := bstep (se 1 (by rfl) ⟨951902, by rfl⟩ : syracuseStep 1269203 = 1903805) B1903805
theorem B843235 : Blo 842353 843235 := bstep (se 1 (by rfl) ⟨632426, by rfl⟩ : syracuseStep 843235 = 1264853) B1264853
theorem B1269233 : Blo 842353 1269233 := bstep (se 2 (by rfl) ⟨475962, by rfl⟩ : syracuseStep 1269233 = 951925) B951925
theorem B843251 : Blo 842353 843251 := bstep (se 1 (by rfl) ⟨632438, by rfl⟩ : syracuseStep 843251 = 1264877) B1264877
theorem B843267 : Blo 842353 843267 := bstep (se 1 (by rfl) ⟨632450, by rfl⟩ : syracuseStep 843267 = 1264901) B1264901
theorem B1269251 : Blo 842353 1269251 := bstep (se 1 (by rfl) ⟨951938, by rfl⟩ : syracuseStep 1269251 = 1903877) B1903877
theorem B843283 : Blo 842353 843283 := bstep (se 1 (by rfl) ⟨632462, by rfl⟩ : syracuseStep 843283 = 1264925) B1264925
theorem B1269281 : Blo 842353 1269281 := bstep (se 2 (by rfl) ⟨475980, by rfl⟩ : syracuseStep 1269281 = 951961) B951961
theorem B843299 : Blo 842353 843299 := bstep (se 1 (by rfl) ⟨632474, by rfl⟩ : syracuseStep 843299 = 1264949) B1264949
theorem B843315 : Blo 842353 843315 := bstep (se 1 (by rfl) ⟨632486, by rfl⟩ : syracuseStep 843315 = 1264973) B1264973
theorem B1269299 : Blo 842353 1269299 := bstep (se 1 (by rfl) ⟨951974, by rfl⟩ : syracuseStep 1269299 = 1903949) B1903949
theorem B843331 : Blo 842353 843331 := bstep (se 1 (by rfl) ⟨632498, by rfl⟩ : syracuseStep 843331 = 1264997) B1264997
theorem B1269329 : Blo 842353 1269329 := bstep (se 2 (by rfl) ⟨475998, by rfl⟩ : syracuseStep 1269329 = 951997) B951997
theorem B843347 : Blo 842353 843347 := bstep (se 1 (by rfl) ⟨632510, by rfl⟩ : syracuseStep 843347 = 1265021) B1265021
theorem B843363 : Blo 842353 843363 := bstep (se 1 (by rfl) ⟨632522, by rfl⟩ : syracuseStep 843363 = 1265045) B1265045
theorem B1269347 : Blo 842353 1269347 := bstep (se 1 (by rfl) ⟨952010, by rfl⟩ : syracuseStep 1269347 = 1904021) B1904021
theorem B3038833 : Blo 842353 3038833 := bstep (se 2 (by rfl) ⟨1139562, by rfl⟩ : syracuseStep 3038833 = 2279125) B2279125
theorem B1302131 : Blo 842353 1302131 := bstep (se 1 (by rfl) ⟨976598, by rfl⟩ : syracuseStep 1302131 = 1953197) B1953197
theorem B843379 : Blo 842353 843379 := bstep (se 1 (by rfl) ⟨632534, by rfl⟩ : syracuseStep 843379 = 1265069) B1265069
theorem B1269377 : Blo 842353 1269377 := bstep (se 2 (by rfl) ⟨476016, by rfl⟩ : syracuseStep 1269377 = 952033) B952033
theorem B843395 : Blo 842353 843395 := bstep (se 1 (by rfl) ⟨632546, by rfl⟩ : syracuseStep 843395 = 1265093) B1265093
theorem B843411 : Blo 842353 843411 := bstep (se 1 (by rfl) ⟨632558, by rfl⟩ : syracuseStep 843411 = 1265117) B1265117
theorem B1269395 : Blo 842353 1269395 := bstep (se 1 (by rfl) ⟨952046, by rfl⟩ : syracuseStep 1269395 = 1904093) B1904093
theorem B843427 : Blo 842353 843427 := bstep (se 1 (by rfl) ⟨632570, by rfl⟩ : syracuseStep 843427 = 1265141) B1265141
theorem B1269425 : Blo 842353 1269425 := bstep (se 2 (by rfl) ⟨476034, by rfl⟩ : syracuseStep 1269425 = 952069) B952069
theorem B843443 : Blo 842353 843443 := bstep (se 1 (by rfl) ⟨632582, by rfl⟩ : syracuseStep 843443 = 1265165) B1265165
theorem B843459 : Blo 842353 843459 := bstep (se 1 (by rfl) ⟨632594, by rfl⟩ : syracuseStep 843459 = 1265189) B1265189
theorem B1269443 : Blo 842353 1269443 := bstep (se 1 (by rfl) ⟨952082, by rfl⟩ : syracuseStep 1269443 = 1904165) B1904165
theorem B843475 : Blo 842353 843475 := bstep (se 1 (by rfl) ⟨632606, by rfl⟩ : syracuseStep 843475 = 1265213) B1265213
theorem B1269473 : Blo 842353 1269473 := bstep (se 2 (by rfl) ⟨476052, by rfl⟩ : syracuseStep 1269473 = 952105) B952105
theorem B843491 : Blo 842353 843491 := bstep (se 1 (by rfl) ⟨632618, by rfl⟩ : syracuseStep 843491 = 1265237) B1265237
theorem B843507 : Blo 842353 843507 := bstep (se 1 (by rfl) ⟨632630, by rfl⟩ : syracuseStep 843507 = 1265261) B1265261
theorem B1269491 : Blo 842353 1269491 := bstep (se 1 (by rfl) ⟨952118, by rfl⟩ : syracuseStep 1269491 = 1904237) B1904237
theorem B843523 : Blo 842353 843523 := bstep (se 1 (by rfl) ⟨632642, by rfl⟩ : syracuseStep 843523 = 1265285) B1265285
theorem B1269521 : Blo 842353 1269521 := bstep (se 2 (by rfl) ⟨476070, by rfl⟩ : syracuseStep 1269521 = 952141) B952141
theorem B843539 : Blo 842353 843539 := bstep (se 1 (by rfl) ⟨632654, by rfl⟩ : syracuseStep 843539 = 1265309) B1265309
theorem B843555 : Blo 842353 843555 := bstep (se 1 (by rfl) ⟨632666, by rfl⟩ : syracuseStep 843555 = 1265333) B1265333
theorem B843571 : Blo 842353 843571 := bstep (se 1 (by rfl) ⟨632678, by rfl⟩ : syracuseStep 843571 = 1265357) B1265357
theorem B843587 : Blo 842353 843587 := bstep (se 1 (by rfl) ⟨632690, by rfl⟩ : syracuseStep 843587 = 1265381) B1265381
theorem B843603 : Blo 842353 843603 := bstep (se 1 (by rfl) ⟨632702, by rfl⟩ : syracuseStep 843603 = 1265405) B1265405
theorem B843619 : Blo 842353 843619 := bstep (se 1 (by rfl) ⟨632714, by rfl⟩ : syracuseStep 843619 = 1265429) B1265429
theorem B843635 : Blo 842353 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B843651 : Blo 842353 843651 := bstep (se 1 (by rfl) ⟨632738, by rfl⟩ : syracuseStep 843651 = 1265477) B1265477
theorem B843667 : Blo 842353 843667 := bstep (se 1 (by rfl) ⟨632750, by rfl⟩ : syracuseStep 843667 = 1265501) B1265501
theorem B843683 : Blo 842353 843683 := bstep (se 1 (by rfl) ⟨632762, by rfl⟩ : syracuseStep 843683 = 1265525) B1265525
theorem B843699 : Blo 842353 843699 := bstep (se 1 (by rfl) ⟨632774, by rfl⟩ : syracuseStep 843699 = 1265549) B1265549
theorem B843715 : Blo 842353 843715 := bstep (se 1 (by rfl) ⟨632786, by rfl⟩ : syracuseStep 843715 = 1265573) B1265573
theorem B4808645 : Blo 842353 4808645 := bstep (se 4 (by rfl) ⟨450810, by rfl⟩ : syracuseStep 4808645 = 901621) B901621
theorem B843731 : Blo 842353 843731 := bstep (se 1 (by rfl) ⟨632798, by rfl⟩ : syracuseStep 843731 = 1265597) B1265597
theorem B843747 : Blo 842353 843747 := bstep (se 1 (by rfl) ⟨632810, by rfl⟩ : syracuseStep 843747 = 1265621) B1265621
theorem B2285549 : Blo 842353 2285549 := bstep (se 3 (by rfl) ⟨428540, by rfl⟩ : syracuseStep 2285549 = 857081) B857081
theorem B843763 : Blo 842353 843763 := bstep (se 1 (by rfl) ⟨632822, by rfl⟩ : syracuseStep 843763 = 1265645) B1265645
theorem B843779 : Blo 842353 843779 := bstep (se 1 (by rfl) ⟨632834, by rfl⟩ : syracuseStep 843779 = 1265669) B1265669
theorem B843795 : Blo 842353 843795 := bstep (se 1 (by rfl) ⟨632846, by rfl⟩ : syracuseStep 843795 = 1265693) B1265693
theorem B843811 : Blo 842353 843811 := bstep (se 1 (by rfl) ⟨632858, by rfl⟩ : syracuseStep 843811 = 1265717) B1265717
theorem B843827 : Blo 842353 843827 := bstep (se 1 (by rfl) ⟨632870, by rfl⟩ : syracuseStep 843827 = 1265741) B1265741
theorem B843843 : Blo 842353 843843 := bstep (se 1 (by rfl) ⟨632882, by rfl⟩ : syracuseStep 843843 = 1265765) B1265765
theorem B843859 : Blo 842353 843859 := bstep (se 1 (by rfl) ⟨632894, by rfl⟩ : syracuseStep 843859 = 1265789) B1265789
theorem B843875 : Blo 842353 843875 := bstep (se 1 (by rfl) ⟨632906, by rfl⟩ : syracuseStep 843875 = 1265813) B1265813
theorem B843891 : Blo 842353 843891 := bstep (se 1 (by rfl) ⟨632918, by rfl⟩ : syracuseStep 843891 = 1265837) B1265837
theorem B843907 : Blo 842353 843907 := bstep (se 1 (by rfl) ⟨632930, by rfl⟩ : syracuseStep 843907 = 1265861) B1265861
theorem B843923 : Blo 842353 843923 := bstep (se 1 (by rfl) ⟨632942, by rfl⟩ : syracuseStep 843923 = 1265885) B1265885
theorem B843939 : Blo 842353 843939 := bstep (se 1 (by rfl) ⟨632954, by rfl⟩ : syracuseStep 843939 = 1265909) B1265909
theorem B843955 : Blo 842353 843955 := bstep (se 1 (by rfl) ⟨632966, by rfl⟩ : syracuseStep 843955 = 1265933) B1265933
theorem B843971 : Blo 842353 843971 := bstep (se 1 (by rfl) ⟨632978, by rfl⟩ : syracuseStep 843971 = 1265957) B1265957
theorem B843987 : Blo 842353 843987 := bstep (se 1 (by rfl) ⟨632990, by rfl⟩ : syracuseStep 843987 = 1265981) B1265981
theorem B844003 : Blo 842353 844003 := bstep (se 1 (by rfl) ⟨633002, by rfl⟩ : syracuseStep 844003 = 1266005) B1266005
theorem B844019 : Blo 842353 844019 := bstep (se 1 (by rfl) ⟨633014, by rfl⟩ : syracuseStep 844019 = 1266029) B1266029
theorem B844035 : Blo 842353 844035 := bstep (se 1 (by rfl) ⟨633026, by rfl⟩ : syracuseStep 844035 = 1266053) B1266053
theorem B844051 : Blo 842353 844051 := bstep (se 1 (by rfl) ⟨633038, by rfl⟩ : syracuseStep 844051 = 1266077) B1266077
theorem B1138979 : Blo 842353 1138979 := bstep (se 1 (by rfl) ⟨854234, by rfl⟩ : syracuseStep 1138979 = 1708469) B1708469
theorem B844067 : Blo 842353 844067 := bstep (se 1 (by rfl) ⟨633050, by rfl⟩ : syracuseStep 844067 = 1266101) B1266101
theorem B844083 : Blo 842353 844083 := bstep (se 1 (by rfl) ⟨633062, by rfl⟩ : syracuseStep 844083 = 1266125) B1266125
theorem B844099 : Blo 842353 844099 := bstep (se 1 (by rfl) ⟨633074, by rfl⟩ : syracuseStep 844099 = 1266149) B1266149
theorem B844115 : Blo 842353 844115 := bstep (se 1 (by rfl) ⟨633086, by rfl⟩ : syracuseStep 844115 = 1266173) B1266173
theorem B5398883 : Blo 842353 5398883 := bstep (se 1 (by rfl) ⟨4049162, by rfl⟩ : syracuseStep 5398883 = 8098325) B8098325
theorem B844131 : Blo 842353 844131 := bstep (se 1 (by rfl) ⟨633098, by rfl⟩ : syracuseStep 844131 = 1266197) B1266197
theorem B844147 : Blo 842353 844147 := bstep (se 1 (by rfl) ⟨633110, by rfl⟩ : syracuseStep 844147 = 1266221) B1266221
theorem B844163 : Blo 842353 844163 := bstep (se 1 (by rfl) ⟨633122, by rfl⟩ : syracuseStep 844163 = 1266245) B1266245
theorem B844179 : Blo 842353 844179 := bstep (se 1 (by rfl) ⟨633134, by rfl⟩ : syracuseStep 844179 = 1266269) B1266269
theorem B1204627 : Blo 842353 1204627 := bstep (se 1 (by rfl) ⟨903470, by rfl⟩ : syracuseStep 1204627 = 1806941) B1806941
theorem B844195 : Blo 842353 844195 := bstep (se 1 (by rfl) ⟨633146, by rfl⟩ : syracuseStep 844195 = 1266293) B1266293
theorem B844211 : Blo 842353 844211 := bstep (se 1 (by rfl) ⟨633158, by rfl⟩ : syracuseStep 844211 = 1266317) B1266317
theorem B844227 : Blo 842353 844227 := bstep (se 1 (by rfl) ⟨633170, by rfl⟩ : syracuseStep 844227 = 1266341) B1266341
theorem B844243 : Blo 842353 844243 := bstep (se 1 (by rfl) ⟨633182, by rfl⟩ : syracuseStep 844243 = 1266365) B1266365
theorem B844259 : Blo 842353 844259 := bstep (se 1 (by rfl) ⟨633194, by rfl⟩ : syracuseStep 844259 = 1266389) B1266389
theorem B844275 : Blo 842353 844275 := bstep (se 1 (by rfl) ⟨633206, by rfl⟩ : syracuseStep 844275 = 1266413) B1266413
theorem B844291 : Blo 842353 844291 := bstep (se 1 (by rfl) ⟨633218, by rfl⟩ : syracuseStep 844291 = 1266437) B1266437
theorem B2843153 : Blo 842353 2843153 := bstep (se 2 (by rfl) ⟨1066182, by rfl⟩ : syracuseStep 2843153 = 2132365) B2132365
theorem B844307 : Blo 842353 844307 := bstep (se 1 (by rfl) ⟨633230, by rfl⟩ : syracuseStep 844307 = 1266461) B1266461
theorem B844323 : Blo 842353 844323 := bstep (se 1 (by rfl) ⟨633242, by rfl⟩ : syracuseStep 844323 = 1266485) B1266485
theorem B844339 : Blo 842353 844339 := bstep (se 1 (by rfl) ⟨633254, by rfl⟩ : syracuseStep 844339 = 1266509) B1266509
theorem B844355 : Blo 842353 844355 := bstep (se 1 (by rfl) ⟨633266, by rfl⟩ : syracuseStep 844355 = 1266533) B1266533
theorem B844371 : Blo 842353 844371 := bstep (se 1 (by rfl) ⟨633278, by rfl⟩ : syracuseStep 844371 = 1266557) B1266557
theorem B844387 : Blo 842353 844387 := bstep (se 1 (by rfl) ⟨633290, by rfl⟩ : syracuseStep 844387 = 1266581) B1266581
theorem B844403 : Blo 842353 844403 := bstep (se 1 (by rfl) ⟨633302, by rfl⟩ : syracuseStep 844403 = 1266605) B1266605
theorem B844419 : Blo 842353 844419 := bstep (se 1 (by rfl) ⟨633314, by rfl⟩ : syracuseStep 844419 = 1266629) B1266629
theorem B844435 : Blo 842353 844435 := bstep (se 1 (by rfl) ⟨633326, by rfl⟩ : syracuseStep 844435 = 1266653) B1266653
theorem B844451 : Blo 842353 844451 := bstep (se 1 (by rfl) ⟨633338, by rfl⟩ : syracuseStep 844451 = 1266677) B1266677
theorem B844467 : Blo 842353 844467 := bstep (se 1 (by rfl) ⟨633350, by rfl⟩ : syracuseStep 844467 = 1266701) B1266701
theorem B844483 : Blo 842353 844483 := bstep (se 1 (by rfl) ⟨633362, by rfl⟩ : syracuseStep 844483 = 1266725) B1266725
theorem B844499 : Blo 842353 844499 := bstep (se 1 (by rfl) ⟨633374, by rfl⟩ : syracuseStep 844499 = 1266749) B1266749
theorem B844515 : Blo 842353 844515 := bstep (se 1 (by rfl) ⟨633386, by rfl⟩ : syracuseStep 844515 = 1266773) B1266773
theorem B6841073 : Blo 842353 6841073 := bstep (se 2 (by rfl) ⟨2565402, by rfl⟩ : syracuseStep 6841073 = 5130805) B5130805
theorem B844531 : Blo 842353 844531 := bstep (se 1 (by rfl) ⟨633398, by rfl⟩ : syracuseStep 844531 = 1266797) B1266797
theorem B844547 : Blo 842353 844547 := bstep (se 1 (by rfl) ⟨633410, by rfl⟩ : syracuseStep 844547 = 1266821) B1266821
theorem B844563 : Blo 842353 844563 := bstep (se 1 (by rfl) ⟨633422, by rfl⟩ : syracuseStep 844563 = 1266845) B1266845
theorem B844579 : Blo 842353 844579 := bstep (se 1 (by rfl) ⟨633434, by rfl⟩ : syracuseStep 844579 = 1266869) B1266869
theorem B844595 : Blo 842353 844595 := bstep (se 1 (by rfl) ⟨633446, by rfl⟩ : syracuseStep 844595 = 1266893) B1266893
theorem B844611 : Blo 842353 844611 := bstep (se 1 (by rfl) ⟨633458, by rfl⟩ : syracuseStep 844611 = 1266917) B1266917
theorem B844627 : Blo 842353 844627 := bstep (se 1 (by rfl) ⟨633470, by rfl⟩ : syracuseStep 844627 = 1266941) B1266941
theorem B844643 : Blo 842353 844643 := bstep (se 1 (by rfl) ⟨633482, by rfl⟩ : syracuseStep 844643 = 1266965) B1266965
theorem B844659 : Blo 842353 844659 := bstep (se 1 (by rfl) ⟨633494, by rfl⟩ : syracuseStep 844659 = 1266989) B1266989
theorem B844675 : Blo 842353 844675 := bstep (se 1 (by rfl) ⟨633506, by rfl⟩ : syracuseStep 844675 = 1267013) B1267013
theorem B844691 : Blo 842353 844691 := bstep (se 1 (by rfl) ⟨633518, by rfl⟩ : syracuseStep 844691 = 1267037) B1267037
theorem B844707 : Blo 842353 844707 := bstep (se 1 (by rfl) ⟨633530, by rfl⟩ : syracuseStep 844707 = 1267061) B1267061
theorem B844723 : Blo 842353 844723 := bstep (se 1 (by rfl) ⟨633542, by rfl⟩ : syracuseStep 844723 = 1267085) B1267085
theorem B844739 : Blo 842353 844739 := bstep (se 1 (by rfl) ⟨633554, by rfl⟩ : syracuseStep 844739 = 1267109) B1267109
theorem B844755 : Blo 842353 844755 := bstep (se 1 (by rfl) ⟨633566, by rfl⟩ : syracuseStep 844755 = 1267133) B1267133
theorem B844771 : Blo 842353 844771 := bstep (se 1 (by rfl) ⟨633578, by rfl⟩ : syracuseStep 844771 = 1267157) B1267157
theorem B844787 : Blo 842353 844787 := bstep (se 1 (by rfl) ⟨633590, by rfl⟩ : syracuseStep 844787 = 1267181) B1267181
theorem B844803 : Blo 842353 844803 := bstep (se 1 (by rfl) ⟨633602, by rfl⟩ : syracuseStep 844803 = 1267205) B1267205
theorem B844819 : Blo 842353 844819 := bstep (se 1 (by rfl) ⟨633614, by rfl⟩ : syracuseStep 844819 = 1267229) B1267229
theorem B844835 : Blo 842353 844835 := bstep (se 1 (by rfl) ⟨633626, by rfl⟩ : syracuseStep 844835 = 1267253) B1267253
theorem B2843693 : Blo 842353 2843693 := bstep (se 3 (by rfl) ⟨533192, by rfl⟩ : syracuseStep 2843693 = 1066385) B1066385
theorem B844851 : Blo 842353 844851 := bstep (se 1 (by rfl) ⟨633638, by rfl⟩ : syracuseStep 844851 = 1267277) B1267277
theorem B844867 : Blo 842353 844867 := bstep (se 1 (by rfl) ⟨633650, by rfl⟩ : syracuseStep 844867 = 1267301) B1267301
theorem B844883 : Blo 842353 844883 := bstep (se 1 (by rfl) ⟨633662, by rfl⟩ : syracuseStep 844883 = 1267325) B1267325
theorem B2843747 : Blo 842353 2843747 := bstep (se 1 (by rfl) ⟨2132810, by rfl⟩ : syracuseStep 2843747 = 4265621) B4265621
theorem B844899 : Blo 842353 844899 := bstep (se 1 (by rfl) ⟨633674, by rfl⟩ : syracuseStep 844899 = 1267349) B1267349
theorem B1041523 : Blo 842353 1041523 := bstep (se 1 (by rfl) ⟨781142, by rfl⟩ : syracuseStep 1041523 = 1562285) B1562285
theorem B844915 : Blo 842353 844915 := bstep (se 1 (by rfl) ⟨633686, by rfl⟩ : syracuseStep 844915 = 1267373) B1267373
theorem B844931 : Blo 842353 844931 := bstep (se 1 (by rfl) ⟨633698, by rfl⟩ : syracuseStep 844931 = 1267397) B1267397
theorem B844947 : Blo 842353 844947 := bstep (se 1 (by rfl) ⟨633710, by rfl⟩ : syracuseStep 844947 = 1267421) B1267421
theorem B844963 : Blo 842353 844963 := bstep (se 1 (by rfl) ⟨633722, by rfl⟩ : syracuseStep 844963 = 1267445) B1267445
theorem B844979 : Blo 842353 844979 := bstep (se 1 (by rfl) ⟨633734, by rfl⟩ : syracuseStep 844979 = 1267469) B1267469
theorem B844995 : Blo 842353 844995 := bstep (se 1 (by rfl) ⟨633746, by rfl⟩ : syracuseStep 844995 = 1267493) B1267493
theorem B845011 : Blo 842353 845011 := bstep (se 1 (by rfl) ⟨633758, by rfl⟩ : syracuseStep 845011 = 1267517) B1267517
theorem B845027 : Blo 842353 845027 := bstep (se 1 (by rfl) ⟨633770, by rfl⟩ : syracuseStep 845027 = 1267541) B1267541
theorem B7202033 : Blo 842353 7202033 := bstep (se 2 (by rfl) ⟨2700762, by rfl⟩ : syracuseStep 7202033 = 5401525) B5401525
theorem B845043 : Blo 842353 845043 := bstep (se 1 (by rfl) ⟨633782, by rfl⟩ : syracuseStep 845043 = 1267565) B1267565
theorem B845059 : Blo 842353 845059 := bstep (se 1 (by rfl) ⟨633794, by rfl⟩ : syracuseStep 845059 = 1267589) B1267589
theorem B845075 : Blo 842353 845075 := bstep (se 1 (by rfl) ⟨633806, by rfl⟩ : syracuseStep 845075 = 1267613) B1267613
theorem B845091 : Blo 842353 845091 := bstep (se 1 (by rfl) ⟨633818, by rfl⟩ : syracuseStep 845091 = 1267637) B1267637
theorem B845107 : Blo 842353 845107 := bstep (se 1 (by rfl) ⟨633830, by rfl⟩ : syracuseStep 845107 = 1267661) B1267661
theorem B845123 : Blo 842353 845123 := bstep (se 1 (by rfl) ⟨633842, by rfl⟩ : syracuseStep 845123 = 1267685) B1267685
theorem B6415685 : Blo 842353 6415685 := bstep (se 4 (by rfl) ⟨601470, by rfl⟩ : syracuseStep 6415685 = 1202941) B1202941
theorem B5399885 : Blo 842353 5399885 := bstep (se 3 (by rfl) ⟨1012478, by rfl⟩ : syracuseStep 5399885 = 2024957) B2024957
theorem B845139 : Blo 842353 845139 := bstep (se 1 (by rfl) ⟨633854, by rfl⟩ : syracuseStep 845139 = 1267709) B1267709
theorem B845155 : Blo 842353 845155 := bstep (se 1 (by rfl) ⟨633866, by rfl⟩ : syracuseStep 845155 = 1267733) B1267733
theorem B2844017 : Blo 842353 2844017 := bstep (se 2 (by rfl) ⟨1066506, by rfl⟩ : syracuseStep 2844017 = 2133013) B2133013
theorem B845171 : Blo 842353 845171 := bstep (se 1 (by rfl) ⟨633878, by rfl⟩ : syracuseStep 845171 = 1267757) B1267757
theorem B845187 : Blo 842353 845187 := bstep (se 1 (by rfl) ⟨633890, by rfl⟩ : syracuseStep 845187 = 1267781) B1267781
theorem B845203 : Blo 842353 845203 := bstep (se 1 (by rfl) ⟨633902, by rfl⟩ : syracuseStep 845203 = 1267805) B1267805
theorem B845219 : Blo 842353 845219 := bstep (se 1 (by rfl) ⟨633914, by rfl⟩ : syracuseStep 845219 = 1267829) B1267829
theorem B845235 : Blo 842353 845235 := bstep (se 1 (by rfl) ⟨633926, by rfl⟩ : syracuseStep 845235 = 1267853) B1267853
theorem B845251 : Blo 842353 845251 := bstep (se 1 (by rfl) ⟨633938, by rfl⟩ : syracuseStep 845251 = 1267877) B1267877
theorem B845267 : Blo 842353 845267 := bstep (se 1 (by rfl) ⟨633950, by rfl⟩ : syracuseStep 845267 = 1267901) B1267901
theorem B845283 : Blo 842353 845283 := bstep (se 1 (by rfl) ⟨633962, by rfl⟩ : syracuseStep 845283 = 1267925) B1267925
theorem B3204593 : Blo 842353 3204593 := bstep (se 2 (by rfl) ⟨1201722, by rfl⟩ : syracuseStep 3204593 = 2403445) B2403445
theorem B845299 : Blo 842353 845299 := bstep (se 1 (by rfl) ⟨633974, by rfl⟩ : syracuseStep 845299 = 1267949) B1267949
theorem B845315 : Blo 842353 845315 := bstep (se 1 (by rfl) ⟨633986, by rfl⟩ : syracuseStep 845315 = 1267973) B1267973
theorem B845331 : Blo 842353 845331 := bstep (se 1 (by rfl) ⟨633998, by rfl⟩ : syracuseStep 845331 = 1267997) B1267997
theorem B845347 : Blo 842353 845347 := bstep (se 1 (by rfl) ⟨634010, by rfl⟩ : syracuseStep 845347 = 1268021) B1268021
theorem B845363 : Blo 842353 845363 := bstep (se 1 (by rfl) ⟨634022, by rfl⟩ : syracuseStep 845363 = 1268045) B1268045
theorem B845379 : Blo 842353 845379 := bstep (se 1 (by rfl) ⟨634034, by rfl⟩ : syracuseStep 845379 = 1268069) B1268069
theorem B845395 : Blo 842353 845395 := bstep (se 1 (by rfl) ⟨634046, by rfl⟩ : syracuseStep 845395 = 1268093) B1268093
theorem B845411 : Blo 842353 845411 := bstep (se 1 (by rfl) ⟨634058, by rfl⟩ : syracuseStep 845411 = 1268117) B1268117
theorem B845427 : Blo 842353 845427 := bstep (se 1 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 845427 = 1268141) B1268141
theorem B845443 : Blo 842353 845443 := bstep (se 1 (by rfl) ⟨634082, by rfl⟩ : syracuseStep 845443 = 1268165) B1268165
theorem B845459 : Blo 842353 845459 := bstep (se 1 (by rfl) ⟨634094, by rfl⟩ : syracuseStep 845459 = 1268189) B1268189
theorem B845475 : Blo 842353 845475 := bstep (se 1 (by rfl) ⟨634106, by rfl⟩ : syracuseStep 845475 = 1268213) B1268213
theorem B845491 : Blo 842353 845491 := bstep (se 1 (by rfl) ⟨634118, by rfl⟩ : syracuseStep 845491 = 1268237) B1268237
theorem B845507 : Blo 842353 845507 := bstep (se 1 (by rfl) ⟨634130, by rfl⟩ : syracuseStep 845507 = 1268261) B1268261
theorem B845523 : Blo 842353 845523 := bstep (se 1 (by rfl) ⟨634142, by rfl⟩ : syracuseStep 845523 = 1268285) B1268285
theorem B845539 : Blo 842353 845539 := bstep (se 1 (by rfl) ⟨634154, by rfl⟩ : syracuseStep 845539 = 1268309) B1268309
theorem B845555 : Blo 842353 845555 := bstep (se 1 (by rfl) ⟨634166, by rfl⟩ : syracuseStep 845555 = 1268333) B1268333
theorem B845571 : Blo 842353 845571 := bstep (se 1 (by rfl) ⟨634178, by rfl⟩ : syracuseStep 845571 = 1268357) B1268357
theorem B4384525 : Blo 842353 4384525 := bstep (se 3 (by rfl) ⟨822098, by rfl⟩ : syracuseStep 4384525 = 1644197) B1644197
theorem B845587 : Blo 842353 845587 := bstep (se 1 (by rfl) ⟨634190, by rfl⟩ : syracuseStep 845587 = 1268381) B1268381
theorem B845603 : Blo 842353 845603 := bstep (se 1 (by rfl) ⟨634202, by rfl⟩ : syracuseStep 845603 = 1268405) B1268405
theorem B2025265 : Blo 842353 2025265 := bstep (se 2 (by rfl) ⟨759474, by rfl⟩ : syracuseStep 2025265 = 1518949) B1518949
theorem B845619 : Blo 842353 845619 := bstep (se 1 (by rfl) ⟨634214, by rfl⟩ : syracuseStep 845619 = 1268429) B1268429
theorem B845635 : Blo 842353 845635 := bstep (se 1 (by rfl) ⟨634226, by rfl⟩ : syracuseStep 845635 = 1268453) B1268453
theorem B845651 : Blo 842353 845651 := bstep (se 1 (by rfl) ⟨634238, by rfl⟩ : syracuseStep 845651 = 1268477) B1268477
theorem B845667 : Blo 842353 845667 := bstep (se 1 (by rfl) ⟨634250, by rfl⟩ : syracuseStep 845667 = 1268501) B1268501
theorem B845683 : Blo 842353 845683 := bstep (se 1 (by rfl) ⟨634262, by rfl⟩ : syracuseStep 845683 = 1268525) B1268525
theorem B845699 : Blo 842353 845699 := bstep (se 1 (by rfl) ⟨634274, by rfl⟩ : syracuseStep 845699 = 1268549) B1268549
theorem B2844557 : Blo 842353 2844557 := bstep (se 3 (by rfl) ⟨533354, by rfl⟩ : syracuseStep 2844557 = 1066709) B1066709
theorem B845715 : Blo 842353 845715 := bstep (se 1 (by rfl) ⟨634286, by rfl⟩ : syracuseStep 845715 = 1268573) B1268573
theorem B845731 : Blo 842353 845731 := bstep (se 1 (by rfl) ⟨634298, by rfl⟩ : syracuseStep 845731 = 1268597) B1268597
theorem B845747 : Blo 842353 845747 := bstep (se 1 (by rfl) ⟨634310, by rfl⟩ : syracuseStep 845747 = 1268621) B1268621
theorem B2844611 : Blo 842353 2844611 := bstep (se 1 (by rfl) ⟨2133458, by rfl⟩ : syracuseStep 2844611 = 4266917) B4266917
theorem B845763 : Blo 842353 845763 := bstep (se 1 (by rfl) ⟨634322, by rfl⟩ : syracuseStep 845763 = 1268645) B1268645
theorem B2779085 : Blo 842353 2779085 := bstep (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) B1042157
theorem B845779 : Blo 842353 845779 := bstep (se 1 (by rfl) ⟨634334, by rfl⟩ : syracuseStep 845779 = 1268669) B1268669
theorem B845795 : Blo 842353 845795 := bstep (se 1 (by rfl) ⟨634346, by rfl⟩ : syracuseStep 845795 = 1268693) B1268693
theorem B10250225 : Blo 842353 10250225 := bstep (se 2 (by rfl) ⟨3843834, by rfl⟩ : syracuseStep 10250225 = 7687669) B7687669
theorem B845811 : Blo 842353 845811 := bstep (se 1 (by rfl) ⟨634358, by rfl⟩ : syracuseStep 845811 = 1268717) B1268717
theorem B845827 : Blo 842353 845827 := bstep (se 1 (by rfl) ⟨634370, by rfl⟩ : syracuseStep 845827 = 1268741) B1268741
theorem B845843 : Blo 842353 845843 := bstep (se 1 (by rfl) ⟨634382, by rfl⟩ : syracuseStep 845843 = 1268765) B1268765
theorem B845859 : Blo 842353 845859 := bstep (se 1 (by rfl) ⟨634394, by rfl⟩ : syracuseStep 845859 = 1268789) B1268789
theorem B845875 : Blo 842353 845875 := bstep (se 1 (by rfl) ⟨634406, by rfl⟩ : syracuseStep 845875 = 1268813) B1268813
theorem B845891 : Blo 842353 845891 := bstep (se 1 (by rfl) ⟨634418, by rfl⟩ : syracuseStep 845891 = 1268837) B1268837
theorem B845907 : Blo 842353 845907 := bstep (se 1 (by rfl) ⟨634430, by rfl⟩ : syracuseStep 845907 = 1268861) B1268861
theorem B3598435 : Blo 842353 3598435 := bstep (se 1 (by rfl) ⟨2698826, by rfl⟩ : syracuseStep 3598435 = 5397653) B5397653
theorem B845923 : Blo 842353 845923 := bstep (se 1 (by rfl) ⟨634442, by rfl⟩ : syracuseStep 845923 = 1268885) B1268885
theorem B1599601 : Blo 842353 1599601 := bstep (se 2 (by rfl) ⟨599850, by rfl⟩ : syracuseStep 1599601 = 1199701) B1199701
theorem B845939 : Blo 842353 845939 := bstep (se 1 (by rfl) ⟨634454, by rfl⟩ : syracuseStep 845939 = 1268909) B1268909
theorem B845955 : Blo 842353 845955 := bstep (se 1 (by rfl) ⟨634466, by rfl⟩ : syracuseStep 845955 = 1268933) B1268933
theorem B845971 : Blo 842353 845971 := bstep (se 1 (by rfl) ⟨634478, by rfl⟩ : syracuseStep 845971 = 1268957) B1268957
theorem B845987 : Blo 842353 845987 := bstep (se 1 (by rfl) ⟨634490, by rfl⟩ : syracuseStep 845987 = 1268981) B1268981
theorem B846003 : Blo 842353 846003 := bstep (se 1 (by rfl) ⟨634502, by rfl⟩ : syracuseStep 846003 = 1269005) B1269005
theorem B846019 : Blo 842353 846019 := bstep (se 1 (by rfl) ⟨634514, by rfl⟩ : syracuseStep 846019 = 1269029) B1269029
theorem B2844881 : Blo 842353 2844881 := bstep (se 2 (by rfl) ⟨1066830, by rfl⟩ : syracuseStep 2844881 = 2133661) B2133661
theorem B846035 : Blo 842353 846035 := bstep (se 1 (by rfl) ⟨634526, by rfl⟩ : syracuseStep 846035 = 1269053) B1269053
theorem B846051 : Blo 842353 846051 := bstep (se 1 (by rfl) ⟨634538, by rfl⟩ : syracuseStep 846051 = 1269077) B1269077
theorem B846067 : Blo 842353 846067 := bstep (se 1 (by rfl) ⟨634550, by rfl⟩ : syracuseStep 846067 = 1269101) B1269101
theorem B846083 : Blo 842353 846083 := bstep (se 1 (by rfl) ⟨634562, by rfl⟩ : syracuseStep 846083 = 1269125) B1269125
theorem B846099 : Blo 842353 846099 := bstep (se 1 (by rfl) ⟨634574, by rfl⟩ : syracuseStep 846099 = 1269149) B1269149
theorem B846115 : Blo 842353 846115 := bstep (se 1 (by rfl) ⟨634586, by rfl⟩ : syracuseStep 846115 = 1269173) B1269173
theorem B846131 : Blo 842353 846131 := bstep (se 1 (by rfl) ⟨634598, by rfl⟩ : syracuseStep 846131 = 1269197) B1269197
theorem B846147 : Blo 842353 846147 := bstep (se 1 (by rfl) ⟨634610, by rfl⟩ : syracuseStep 846147 = 1269221) B1269221
theorem B846163 : Blo 842353 846163 := bstep (se 1 (by rfl) ⟨634622, by rfl⟩ : syracuseStep 846163 = 1269245) B1269245
theorem B846179 : Blo 842353 846179 := bstep (se 1 (by rfl) ⟨634634, by rfl⟩ : syracuseStep 846179 = 1269269) B1269269
theorem B846195 : Blo 842353 846195 := bstep (se 1 (by rfl) ⟨634646, by rfl⟩ : syracuseStep 846195 = 1269293) B1269293
theorem B846211 : Blo 842353 846211 := bstep (se 1 (by rfl) ⟨634658, by rfl⟩ : syracuseStep 846211 = 1269317) B1269317
theorem B846227 : Blo 842353 846227 := bstep (se 1 (by rfl) ⟨634670, by rfl⟩ : syracuseStep 846227 = 1269341) B1269341
theorem B846243 : Blo 842353 846243 := bstep (se 1 (by rfl) ⟨634682, by rfl⟩ : syracuseStep 846243 = 1269365) B1269365
theorem B846259 : Blo 842353 846259 := bstep (se 1 (by rfl) ⟨634694, by rfl⟩ : syracuseStep 846259 = 1269389) B1269389
theorem B846275 : Blo 842353 846275 := bstep (se 1 (by rfl) ⟨634706, by rfl⟩ : syracuseStep 846275 = 1269413) B1269413
theorem B846291 : Blo 842353 846291 := bstep (se 1 (by rfl) ⟨634718, by rfl⟩ : syracuseStep 846291 = 1269437) B1269437
theorem B846307 : Blo 842353 846307 := bstep (se 1 (by rfl) ⟨634730, by rfl⟩ : syracuseStep 846307 = 1269461) B1269461
theorem B6089201 : Blo 842353 6089201 := bstep (se 2 (by rfl) ⟨2283450, by rfl⟩ : syracuseStep 6089201 = 4566901) B4566901
theorem B846323 : Blo 842353 846323 := bstep (se 1 (by rfl) ⟨634742, by rfl⟩ : syracuseStep 846323 = 1269485) B1269485
theorem B1600003 : Blo 842353 1600003 := bstep (se 1 (by rfl) ⟨1200002, by rfl⟩ : syracuseStep 1600003 = 2400005) B2400005
theorem B846339 : Blo 842353 846339 := bstep (se 1 (by rfl) ⟨634754, by rfl⟩ : syracuseStep 846339 = 1269509) B1269509
theorem B1600049 : Blo 842353 1600049 := bstep (se 2 (by rfl) ⟨600018, by rfl⟩ : syracuseStep 1600049 = 1200037) B1200037
theorem B9136739 : Blo 842353 9136739 := bstep (se 1 (by rfl) ⟨6852554, by rfl⟩ : syracuseStep 9136739 = 13705109) B13705109
theorem B1370801 : Blo 842353 1370801 := bstep (se 2 (by rfl) ⟨514050, by rfl⟩ : syracuseStep 1370801 = 1028101) B1028101
theorem B2845421 : Blo 842353 2845421 := bstep (se 3 (by rfl) ⟨533516, by rfl⟩ : syracuseStep 2845421 = 1067033) B1067033
theorem B2845475 : Blo 842353 2845475 := bstep (se 1 (by rfl) ⟨2134106, by rfl⟩ : syracuseStep 2845475 = 4268213) B4268213
theorem B1600337 : Blo 842353 1600337 := bstep (se 2 (by rfl) ⟨600126, by rfl⟩ : syracuseStep 1600337 = 1200253) B1200253
theorem B20573041 : Blo 842353 20573041 := bstep (se 2 (by rfl) ⟨7714890, by rfl⟩ : syracuseStep 20573041 = 15429781) B15429781
theorem B3206051 : Blo 842353 3206051 := bstep (se 1 (by rfl) ⟨2404538, by rfl⟩ : syracuseStep 3206051 = 4809077) B4809077
theorem B1895345 : Blo 842353 1895345 := bstep (se 2 (by rfl) ⟨710754, by rfl⟩ : syracuseStep 1895345 = 1421509) B1421509
theorem B1895363 : Blo 842353 1895363 := bstep (se 1 (by rfl) ⟨1421522, by rfl⟩ : syracuseStep 1895363 = 2843045) B2843045
theorem B2845745 : Blo 842353 2845745 := bstep (se 2 (by rfl) ⟨1067154, by rfl⟩ : syracuseStep 2845745 = 2134309) B2134309
theorem B4058275 : Blo 842353 4058275 := bstep (se 1 (by rfl) ⟨3043706, by rfl⟩ : syracuseStep 4058275 = 6087413) B6087413
theorem B1895633 : Blo 842353 1895633 := bstep (se 2 (by rfl) ⟨710862, by rfl⟩ : syracuseStep 1895633 = 1421725) B1421725
theorem B1895651 : Blo 842353 1895651 := bstep (se 1 (by rfl) ⟨1421738, by rfl⟩ : syracuseStep 1895651 = 2843477) B2843477
theorem B1895921 : Blo 842353 1895921 := bstep (se 2 (by rfl) ⟨710970, by rfl⟩ : syracuseStep 1895921 = 1421941) B1421941
theorem B1895939 : Blo 842353 1895939 := bstep (se 1 (by rfl) ⟨1421954, by rfl⟩ : syracuseStep 1895939 = 2843909) B2843909
theorem B1601059 : Blo 842353 1601059 := bstep (se 1 (by rfl) ⟨1200794, by rfl⟩ : syracuseStep 1601059 = 2401589) B2401589
theorem B2846285 : Blo 842353 2846285 := bstep (se 3 (by rfl) ⟨533678, by rfl⟩ : syracuseStep 2846285 = 1067357) B1067357
theorem B2846339 : Blo 842353 2846339 := bstep (se 1 (by rfl) ⟨2134754, by rfl⟩ : syracuseStep 2846339 = 4269509) B4269509
theorem B4812493 : Blo 842353 4812493 := bstep (se 3 (by rfl) ⟨902342, by rfl⟩ : syracuseStep 4812493 = 1804685) B1804685
theorem B1896209 : Blo 842353 1896209 := bstep (se 2 (by rfl) ⟨711078, by rfl⟩ : syracuseStep 1896209 = 1422157) B1422157
theorem B1896227 : Blo 842353 1896227 := bstep (se 1 (by rfl) ⟨1422170, by rfl⟩ : syracuseStep 1896227 = 2844341) B2844341
theorem B3207053 : Blo 842353 3207053 := bstep (se 3 (by rfl) ⟨601322, by rfl⟩ : syracuseStep 3207053 = 1202645) B1202645
theorem B2846609 : Blo 842353 2846609 := bstep (se 2 (by rfl) ⟨1067478, by rfl⟩ : syracuseStep 2846609 = 2134957) B2134957
theorem B1601507 : Blo 842353 1601507 := bstep (se 1 (by rfl) ⟨1201130, by rfl⟩ : syracuseStep 1601507 = 2402261) B2402261
theorem B1142785 : Blo 842353 1142785 := bstep (se 2 (by rfl) ⟨428544, by rfl⟩ : syracuseStep 1142785 = 857089) B857089
theorem B1896497 : Blo 842353 1896497 := bstep (se 2 (by rfl) ⟨711186, by rfl⟩ : syracuseStep 1896497 = 1422373) B1422373
theorem B1896515 : Blo 842353 1896515 := bstep (se 1 (by rfl) ⟨1422386, by rfl⟩ : syracuseStep 1896515 = 2844773) B2844773
theorem B1601795 : Blo 842353 1601795 := bstep (se 1 (by rfl) ⟨1201346, by rfl⟩ : syracuseStep 1601795 = 2402693) B2402693
theorem B9761077 : Blo 842353 9761077 := bstep (se 5 (by rfl) ⟨457550, by rfl⟩ : syracuseStep 9761077 = 915101) B915101
theorem B1896785 : Blo 842353 1896785 := bstep (se 2 (by rfl) ⟨711294, by rfl⟩ : syracuseStep 1896785 = 1422589) B1422589
theorem B1896803 : Blo 842353 1896803 := bstep (se 1 (by rfl) ⟨1422602, by rfl⟩ : syracuseStep 1896803 = 2845205) B2845205
theorem B1732963 : Blo 842353 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B1929617 : Blo 842353 1929617 := bstep (se 2 (by rfl) ⟨723606, by rfl⟩ : syracuseStep 1929617 = 1447213) B1447213
theorem B2847149 : Blo 842353 2847149 := bstep (se 3 (by rfl) ⟨533840, by rfl⟩ : syracuseStep 2847149 = 1067681) B1067681
theorem B2847203 : Blo 842353 2847203 := bstep (se 1 (by rfl) ⟨2135402, by rfl⟩ : syracuseStep 2847203 = 4270805) B4270805
theorem B3600881 : Blo 842353 3600881 := bstep (se 2 (by rfl) ⟨1350330, by rfl⟩ : syracuseStep 3600881 = 2700661) B2700661
theorem B1897073 : Blo 842353 1897073 := bstep (se 2 (by rfl) ⟨711402, by rfl⟩ : syracuseStep 1897073 = 1422805) B1422805
theorem B1897091 : Blo 842353 1897091 := bstep (se 1 (by rfl) ⟨1422818, by rfl⟩ : syracuseStep 1897091 = 2845637) B2845637
theorem B2847473 : Blo 842353 2847473 := bstep (se 2 (by rfl) ⟨1067802, by rfl⟩ : syracuseStep 2847473 = 2135605) B2135605
theorem B1012483 : Blo 842353 1012483 := bstep (se 1 (by rfl) ⟨759362, by rfl⟩ : syracuseStep 1012483 = 1518725) B1518725
theorem B1897361 : Blo 842353 1897361 := bstep (se 2 (by rfl) ⟨711510, by rfl⟩ : syracuseStep 1897361 = 1423021) B1423021
theorem B1897379 : Blo 842353 1897379 := bstep (se 1 (by rfl) ⟨1423034, by rfl⟩ : syracuseStep 1897379 = 2846069) B2846069
theorem B1143715 : Blo 842353 1143715 := bstep (se 1 (by rfl) ⟨857786, by rfl⟩ : syracuseStep 1143715 = 1715573) B1715573
theorem B1831889 : Blo 842353 1831889 := bstep (se 2 (by rfl) ⟨686958, by rfl⟩ : syracuseStep 1831889 = 1373917) B1373917
theorem B7206029 : Blo 842353 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B1897649 : Blo 842353 1897649 := bstep (se 2 (by rfl) ⟨711618, by rfl⟩ : syracuseStep 1897649 = 1423237) B1423237
theorem B1602737 : Blo 842353 1602737 := bstep (se 2 (by rfl) ⟨601026, by rfl⟩ : syracuseStep 1602737 = 1202053) B1202053
theorem B1897667 : Blo 842353 1897667 := bstep (se 1 (by rfl) ⟨1423250, by rfl⟩ : syracuseStep 1897667 = 2846501) B2846501
theorem B2848013 : Blo 842353 2848013 := bstep (se 3 (by rfl) ⟨534002, by rfl⟩ : syracuseStep 2848013 = 1068005) B1068005
theorem B1799491 : Blo 842353 1799491 := bstep (se 1 (by rfl) ⟨1349618, by rfl⟩ : syracuseStep 1799491 = 2699237) B2699237
theorem B2848067 : Blo 842353 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B15398257 : Blo 842353 15398257 := bstep (se 2 (by rfl) ⟨5774346, by rfl⟩ : syracuseStep 15398257 = 11548693) B11548693
theorem B1897937 : Blo 842353 1897937 := bstep (se 2 (by rfl) ⟨711726, by rfl⟩ : syracuseStep 1897937 = 1423453) B1423453
theorem B1897955 : Blo 842353 1897955 := bstep (se 1 (by rfl) ⟨1423466, by rfl⟩ : syracuseStep 1897955 = 2846933) B2846933
theorem B947731 : Blo 842353 947731 := bstep (se 1 (by rfl) ⟨710798, by rfl⟩ : syracuseStep 947731 = 1421597) B1421597
theorem B1734179 : Blo 842353 1734179 := bstep (se 1 (by rfl) ⟨1300634, by rfl⟩ : syracuseStep 1734179 = 2601269) B2601269
theorem B2848337 : Blo 842353 2848337 := bstep (se 2 (by rfl) ⟨1068126, by rfl⟩ : syracuseStep 2848337 = 2136253) B2136253
theorem B2029187 : Blo 842353 2029187 := bstep (se 1 (by rfl) ⟨1521890, by rfl⟩ : syracuseStep 2029187 = 3043781) B3043781
theorem B4814477 : Blo 842353 4814477 := bstep (se 3 (by rfl) ⟨902714, by rfl⟩ : syracuseStep 4814477 = 1805429) B1805429
theorem B18282125 : Blo 842353 18282125 := bstep (se 3 (by rfl) ⟨3427898, by rfl⟩ : syracuseStep 18282125 = 6855797) B6855797
theorem B947875 : Blo 842353 947875 := bstep (se 1 (by rfl) ⟨710906, by rfl⟩ : syracuseStep 947875 = 1421813) B1421813
theorem B4060849 : Blo 842353 4060849 := bstep (se 2 (by rfl) ⟨1522818, by rfl⟩ : syracuseStep 4060849 = 3045637) B3045637
theorem B1898225 : Blo 842353 1898225 := bstep (se 2 (by rfl) ⟨711834, by rfl⟩ : syracuseStep 1898225 = 1423669) B1423669
theorem B1898243 : Blo 842353 1898243 := bstep (se 1 (by rfl) ⟨1423682, by rfl⟩ : syracuseStep 1898243 = 2847365) B2847365
theorem B948019 : Blo 842353 948019 := bstep (se 1 (by rfl) ⟨711014, by rfl⟩ : syracuseStep 948019 = 1422029) B1422029
theorem B948163 : Blo 842353 948163 := bstep (se 1 (by rfl) ⟨711122, by rfl⟩ : syracuseStep 948163 = 1422245) B1422245
theorem B3209165 : Blo 842353 3209165 := bstep (se 3 (by rfl) ⟨601718, by rfl⟩ : syracuseStep 3209165 = 1203437) B1203437
theorem B1898513 : Blo 842353 1898513 := bstep (se 2 (by rfl) ⟨711942, by rfl⟩ : syracuseStep 1898513 = 1423885) B1423885
theorem B1898531 : Blo 842353 1898531 := bstep (se 1 (by rfl) ⟨1423898, by rfl⟩ : syracuseStep 1898531 = 2847797) B2847797
theorem B1603633 : Blo 842353 1603633 := bstep (se 2 (by rfl) ⟨601362, by rfl⟩ : syracuseStep 1603633 = 1202725) B1202725
theorem B948307 : Blo 842353 948307 := bstep (se 1 (by rfl) ⟨711230, by rfl⟩ : syracuseStep 948307 = 1422461) B1422461
theorem B2848877 : Blo 842353 2848877 := bstep (se 3 (by rfl) ⟨534164, by rfl⟩ : syracuseStep 2848877 = 1068329) B1068329
theorem B2848931 : Blo 842353 2848931 := bstep (se 1 (by rfl) ⟨2136698, by rfl⟩ : syracuseStep 2848931 = 4273397) B4273397
theorem B1603793 : Blo 842353 1603793 := bstep (se 2 (by rfl) ⟨601422, by rfl⟩ : syracuseStep 1603793 = 1202845) B1202845
theorem B948451 : Blo 842353 948451 := bstep (se 1 (by rfl) ⟨711338, by rfl⟩ : syracuseStep 948451 = 1422677) B1422677
theorem B1898801 : Blo 842353 1898801 := bstep (se 2 (by rfl) ⟨712050, by rfl⟩ : syracuseStep 1898801 = 1424101) B1424101
theorem B1898819 : Blo 842353 1898819 := bstep (se 1 (by rfl) ⟨1424114, by rfl⟩ : syracuseStep 1898819 = 2848229) B2848229
theorem B948595 : Blo 842353 948595 := bstep (se 1 (by rfl) ⟨711446, by rfl⟩ : syracuseStep 948595 = 1422893) B1422893
theorem B2849201 : Blo 842353 2849201 := bstep (se 2 (by rfl) ⟨1068450, by rfl⟩ : syracuseStep 2849201 = 2136901) B2136901
theorem B948739 : Blo 842353 948739 := bstep (se 1 (by rfl) ⟨711554, by rfl⟩ : syracuseStep 948739 = 1423109) B1423109
theorem B1800721 : Blo 842353 1800721 := bstep (se 2 (by rfl) ⟨675270, by rfl⟩ : syracuseStep 1800721 = 1350541) B1350541
theorem B4815409 : Blo 842353 4815409 := bstep (se 2 (by rfl) ⟨1805778, by rfl⟩ : syracuseStep 4815409 = 3611557) B3611557
theorem B1899089 : Blo 842353 1899089 := bstep (se 2 (by rfl) ⟨712158, by rfl⟩ : syracuseStep 1899089 = 1424317) B1424317
theorem B1899107 : Blo 842353 1899107 := bstep (se 1 (by rfl) ⟨1424330, by rfl⟩ : syracuseStep 1899107 = 2848661) B2848661
theorem B1604195 : Blo 842353 1604195 := bstep (se 1 (by rfl) ⟨1203146, by rfl⟩ : syracuseStep 1604195 = 2406293) B2406293
theorem B948883 : Blo 842353 948883 := bstep (se 1 (by rfl) ⟨711662, by rfl⟩ : syracuseStep 948883 = 1423325) B1423325
theorem B3209969 : Blo 842353 3209969 := bstep (se 2 (by rfl) ⟨1203738, by rfl⟩ : syracuseStep 3209969 = 2407477) B2407477
theorem B949027 : Blo 842353 949027 := bstep (se 1 (by rfl) ⟨711770, by rfl⟩ : syracuseStep 949027 = 1423541) B1423541
theorem B2030417 : Blo 842353 2030417 := bstep (se 2 (by rfl) ⟨761406, by rfl⟩ : syracuseStep 2030417 = 1522813) B1522813
theorem B1899377 : Blo 842353 1899377 := bstep (se 2 (by rfl) ⟨712266, by rfl⟩ : syracuseStep 1899377 = 1424533) B1424533
theorem B1899395 : Blo 842353 1899395 := bstep (se 1 (by rfl) ⟨1424546, by rfl⟩ : syracuseStep 1899395 = 2849093) B2849093
theorem B949171 : Blo 842353 949171 := bstep (se 1 (by rfl) ⟨711878, by rfl⟩ : syracuseStep 949171 = 1423757) B1423757
theorem B2849741 : Blo 842353 2849741 := bstep (se 3 (by rfl) ⟨534326, by rfl⟩ : syracuseStep 2849741 = 1068653) B1068653
theorem B2849795 : Blo 842353 2849795 := bstep (se 1 (by rfl) ⟨2137346, by rfl⟩ : syracuseStep 2849795 = 4274693) B4274693
theorem B6421517 : Blo 842353 6421517 := bstep (se 3 (by rfl) ⟨1204034, by rfl⟩ : syracuseStep 6421517 = 2408069) B2408069
theorem B949315 : Blo 842353 949315 := bstep (se 1 (by rfl) ⟨711986, by rfl⟩ : syracuseStep 949315 = 1423973) B1423973
theorem B1899665 : Blo 842353 1899665 := bstep (se 2 (by rfl) ⟨712374, by rfl⟩ : syracuseStep 1899665 = 1424749) B1424749
theorem B1899683 : Blo 842353 1899683 := bstep (se 1 (by rfl) ⟨1424762, by rfl⟩ : syracuseStep 1899683 = 2849525) B2849525
theorem B949459 : Blo 842353 949459 := bstep (se 1 (by rfl) ⟨712094, by rfl⟩ : syracuseStep 949459 = 1424189) B1424189
theorem B2850065 : Blo 842353 2850065 := bstep (se 2 (by rfl) ⟨1068774, by rfl⟩ : syracuseStep 2850065 = 2137549) B2137549
theorem B949603 : Blo 842353 949603 := bstep (se 1 (by rfl) ⟨712202, by rfl⟩ : syracuseStep 949603 = 1424405) B1424405
theorem B3210637 : Blo 842353 3210637 := bstep (se 3 (by rfl) ⟨601994, by rfl⟩ : syracuseStep 3210637 = 1203989) B1203989
theorem B1899953 : Blo 842353 1899953 := bstep (se 2 (by rfl) ⟨712482, by rfl⟩ : syracuseStep 1899953 = 1424965) B1424965
theorem B1899971 : Blo 842353 1899971 := bstep (se 1 (by rfl) ⟨1424978, by rfl⟩ : syracuseStep 1899971 = 2849957) B2849957
theorem B1605091 : Blo 842353 1605091 := bstep (se 1 (by rfl) ⟨1203818, by rfl⟩ : syracuseStep 1605091 = 2407637) B2407637
theorem B949747 : Blo 842353 949747 := bstep (se 1 (by rfl) ⟨712310, by rfl⟩ : syracuseStep 949747 = 1424621) B1424621
theorem B9109061 : Blo 842353 9109061 := bstep (se 4 (by rfl) ⟨853974, by rfl⟩ : syracuseStep 9109061 = 1707949) B1707949
theorem B949891 : Blo 842353 949891 := bstep (se 1 (by rfl) ⟨712418, by rfl⟩ : syracuseStep 949891 = 1424837) B1424837
theorem B1605251 : Blo 842353 1605251 := bstep (se 1 (by rfl) ⟨1203938, by rfl⟩ : syracuseStep 1605251 = 2407877) B2407877
theorem B1900241 : Blo 842353 1900241 := bstep (se 2 (by rfl) ⟨712590, by rfl⟩ : syracuseStep 1900241 = 1425181) B1425181
theorem B1900259 : Blo 842353 1900259 := bstep (se 1 (by rfl) ⟨1425194, by rfl⟩ : syracuseStep 1900259 = 2850389) B2850389
theorem B950035 : Blo 842353 950035 := bstep (se 1 (by rfl) ⟨712526, by rfl⟩ : syracuseStep 950035 = 1425053) B1425053
theorem B2850605 : Blo 842353 2850605 := bstep (se 3 (by rfl) ⟨534488, by rfl⟩ : syracuseStep 2850605 = 1068977) B1068977
theorem B2850659 : Blo 842353 2850659 := bstep (se 1 (by rfl) ⟨2137994, by rfl⟩ : syracuseStep 2850659 = 4275989) B4275989
theorem B950179 : Blo 842353 950179 := bstep (se 1 (by rfl) ⟨712634, by rfl⟩ : syracuseStep 950179 = 1425269) B1425269
theorem B4816867 : Blo 842353 4816867 := bstep (se 1 (by rfl) ⟨3612650, by rfl⟩ : syracuseStep 4816867 = 7225301) B7225301
theorem B1802225 : Blo 842353 1802225 := bstep (se 2 (by rfl) ⟨675834, by rfl⟩ : syracuseStep 1802225 = 1351669) B1351669
theorem B1900529 : Blo 842353 1900529 := bstep (se 2 (by rfl) ⟨712698, by rfl⟩ : syracuseStep 1900529 = 1425397) B1425397
theorem B1605683 : Blo 842353 1605683 := bstep (se 1 (by rfl) ⟨1204262, by rfl⟩ : syracuseStep 1605683 = 2408525) B2408525
theorem B18219077 : Blo 842353 18219077 := bstep (se 4 (by rfl) ⟨1708038, by rfl⟩ : syracuseStep 18219077 = 3416077) B3416077
theorem B1900619 : Blo 842353 1900619 := bstep (se 1 (by rfl) ⟨1425464, by rfl⟩ : syracuseStep 1900619 = 2850929) B2850929
theorem B950359 : Blo 842353 950359 := bstep (se 1 (by rfl) ⟨712769, by rfl⟩ : syracuseStep 950359 = 1425539) B1425539
theorem B1900673 : Blo 842353 1900673 := bstep (se 2 (by rfl) ⟨712752, by rfl⟩ : syracuseStep 1900673 = 1425505) B1425505
theorem B1605835 : Blo 842353 1605835 := bstep (se 1 (by rfl) ⟨1204376, by rfl⟩ : syracuseStep 1605835 = 2408753) B2408753
theorem B2851037 : Blo 842353 2851037 := bstep (se 3 (by rfl) ⟨534569, by rfl⟩ : syracuseStep 2851037 = 1069139) B1069139
theorem B950539 : Blo 842353 950539 := bstep (se 1 (by rfl) ⟨712904, by rfl⟩ : syracuseStep 950539 = 1425809) B1425809
theorem B3211595 : Blo 842353 3211595 := bstep (se 1 (by rfl) ⟨2408696, by rfl⟩ : syracuseStep 3211595 = 4817393) B4817393
theorem B1900889 : Blo 842353 1900889 := bstep (se 2 (by rfl) ⟨712833, by rfl⟩ : syracuseStep 1900889 = 1425667) B1425667
theorem B3211609 : Blo 842353 3211609 := bstep (se 2 (by rfl) ⟨1204353, by rfl⟩ : syracuseStep 3211609 = 2408707) B2408707
theorem B950647 : Blo 842353 950647 := bstep (se 1 (by rfl) ⟨712985, by rfl⟩ : syracuseStep 950647 = 1425971) B1425971
theorem B1900979 : Blo 842353 1900979 := bstep (se 1 (by rfl) ⟨1425734, by rfl⟩ : syracuseStep 1900979 = 2851469) B2851469
theorem B1901015 : Blo 842353 1901015 := bstep (se 1 (by rfl) ⟨1425761, by rfl⟩ : syracuseStep 1901015 = 2851523) B2851523
theorem B1606169 : Blo 842353 1606169 := bstep (se 2 (by rfl) ⟨602313, by rfl⟩ : syracuseStep 1606169 = 1204627) B1204627
theorem B950827 : Blo 842353 950827 := bstep (se 1 (by rfl) ⟨713120, by rfl⟩ : syracuseStep 950827 = 1426241) B1426241
theorem B1901195 : Blo 842353 1901195 := bstep (se 1 (by rfl) ⟨1425896, by rfl⟩ : syracuseStep 1901195 = 2851793) B2851793
theorem B950935 : Blo 842353 950935 := bstep (se 1 (by rfl) ⟨713201, by rfl⟩ : syracuseStep 950935 = 1426403) B1426403
theorem B1901249 : Blo 842353 1901249 := bstep (se 2 (by rfl) ⟨712968, by rfl⟩ : syracuseStep 1901249 = 1425937) B1425937
theorem B1802969 : Blo 842353 1802969 := bstep (se 2 (by rfl) ⟨676113, by rfl⟩ : syracuseStep 1802969 = 1352227) B1352227
theorem B951115 : Blo 842353 951115 := bstep (se 1 (by rfl) ⟨713336, by rfl⟩ : syracuseStep 951115 = 1426673) B1426673
theorem B1901465 : Blo 842353 1901465 := bstep (se 2 (by rfl) ⟨713049, by rfl⟩ : syracuseStep 1901465 = 1426099) B1426099
theorem B951223 : Blo 842353 951223 := bstep (se 1 (by rfl) ⟨713417, by rfl⟩ : syracuseStep 951223 = 1426835) B1426835
theorem B1901555 : Blo 842353 1901555 := bstep (se 1 (by rfl) ⟨1426166, by rfl⟩ : syracuseStep 1901555 = 2852333) B2852333
theorem B1901591 : Blo 842353 1901591 := bstep (se 1 (by rfl) ⟨1426193, by rfl⟩ : syracuseStep 1901591 = 2852387) B2852387
theorem B3605579 : Blo 842353 3605579 := bstep (se 1 (by rfl) ⟨2704184, by rfl⟩ : syracuseStep 3605579 = 5408369) B5408369
theorem B5473373 : Blo 842353 5473373 := bstep (se 3 (by rfl) ⟨1026257, by rfl⟩ : syracuseStep 5473373 = 2052515) B2052515
theorem B951403 : Blo 842353 951403 := bstep (se 1 (by rfl) ⟨713552, by rfl⟩ : syracuseStep 951403 = 1427105) B1427105
theorem B1803379 : Blo 842353 1803379 := bstep (se 1 (by rfl) ⟨1352534, by rfl⟩ : syracuseStep 1803379 = 2705069) B2705069
theorem B1901771 : Blo 842353 1901771 := bstep (se 1 (by rfl) ⟨1426328, by rfl⟩ : syracuseStep 1901771 = 2852657) B2852657
theorem B951511 : Blo 842353 951511 := bstep (se 1 (by rfl) ⟨713633, by rfl⟩ : syracuseStep 951511 = 1427267) B1427267
theorem B1901825 : Blo 842353 1901825 := bstep (se 2 (by rfl) ⟨713184, by rfl⟩ : syracuseStep 1901825 = 1426369) B1426369
theorem B3212567 : Blo 842353 3212567 := bstep (se 1 (by rfl) ⟨2409425, by rfl⟩ : syracuseStep 3212567 = 4818851) B4818851
theorem B2852171 : Blo 842353 2852171 := bstep (se 1 (by rfl) ⟨2139128, by rfl⟩ : syracuseStep 2852171 = 4278257) B4278257
theorem B951691 : Blo 842353 951691 := bstep (se 1 (by rfl) ⟨713768, by rfl⟩ : syracuseStep 951691 = 1427537) B1427537
theorem B3605953 : Blo 842353 3605953 := bstep (se 2 (by rfl) ⟨1352232, by rfl⟩ : syracuseStep 3605953 = 2704465) B2704465
theorem B1902041 : Blo 842353 1902041 := bstep (se 2 (by rfl) ⟨713265, by rfl⟩ : syracuseStep 1902041 = 1426531) B1426531
theorem B951799 : Blo 842353 951799 := bstep (se 1 (by rfl) ⟨713849, by rfl⟩ : syracuseStep 951799 = 1427699) B1427699
theorem B1902131 : Blo 842353 1902131 := bstep (se 1 (by rfl) ⟨1426598, by rfl⟩ : syracuseStep 1902131 = 2853197) B2853197
theorem B1902167 : Blo 842353 1902167 := bstep (se 1 (by rfl) ⟨1426625, by rfl⟩ : syracuseStep 1902167 = 2853251) B2853251
theorem B1803865 : Blo 842353 1803865 := bstep (se 2 (by rfl) ⟨676449, by rfl⟩ : syracuseStep 1803865 = 1352899) B1352899
theorem B2852441 : Blo 842353 2852441 := bstep (se 2 (by rfl) ⟨1069665, by rfl⟩ : syracuseStep 2852441 = 2139331) B2139331
theorem B7308893 : Blo 842353 7308893 := bstep (se 3 (by rfl) ⟨1370417, by rfl⟩ : syracuseStep 7308893 = 2740835) B2740835
theorem B951979 : Blo 842353 951979 := bstep (se 1 (by rfl) ⟨713984, by rfl⟩ : syracuseStep 951979 = 1427969) B1427969
theorem B1902347 : Blo 842353 1902347 := bstep (se 1 (by rfl) ⟨1426760, by rfl⟩ : syracuseStep 1902347 = 2853521) B2853521
theorem B4065041 : Blo 842353 4065041 := bstep (se 2 (by rfl) ⟨1524390, by rfl⟩ : syracuseStep 4065041 = 3048781) B3048781
theorem B3606295 : Blo 842353 3606295 := bstep (se 1 (by rfl) ⟨2704721, by rfl⟩ : syracuseStep 3606295 = 5409443) B5409443
theorem B952087 : Blo 842353 952087 := bstep (se 1 (by rfl) ⟨714065, by rfl⟩ : syracuseStep 952087 = 1428131) B1428131
theorem B1902401 : Blo 842353 1902401 := bstep (se 2 (by rfl) ⟨713400, by rfl⟩ : syracuseStep 1902401 = 1426801) B1426801
theorem B4065155 : Blo 842353 4065155 := bstep (se 1 (by rfl) ⟨3048866, by rfl⟩ : syracuseStep 4065155 = 6097733) B6097733
theorem B1902617 : Blo 842353 1902617 := bstep (se 2 (by rfl) ⟨713481, by rfl⟩ : syracuseStep 1902617 = 1426963) B1426963
theorem B1902707 : Blo 842353 1902707 := bstep (se 1 (by rfl) ⟨1427030, by rfl⟩ : syracuseStep 1902707 = 2854061) B2854061
theorem B1902743 : Blo 842353 1902743 := bstep (se 1 (by rfl) ⟨1427057, by rfl⟩ : syracuseStep 1902743 = 2854115) B2854115
theorem B7702705 : Blo 842353 7702705 := bstep (se 2 (by rfl) ⟨2888514, by rfl⟩ : syracuseStep 7702705 = 5777029) B5777029
theorem B2853143 : Blo 842353 2853143 := bstep (se 1 (by rfl) ⟨2139857, by rfl⟩ : syracuseStep 2853143 = 4279715) B4279715
theorem B1804609 : Blo 842353 1804609 := bstep (se 2 (by rfl) ⟨676728, by rfl⟩ : syracuseStep 1804609 = 1353457) B1353457
theorem B1902923 : Blo 842353 1902923 := bstep (se 1 (by rfl) ⟨1427192, by rfl⟩ : syracuseStep 1902923 = 2854385) B2854385
theorem B1902977 : Blo 842353 1902977 := bstep (se 2 (by rfl) ⟨713616, by rfl⟩ : syracuseStep 1902977 = 1427233) B1427233
theorem B22219157 : Blo 842353 22219157 := bstep (se 6 (by rfl) ⟨520761, by rfl⟩ : syracuseStep 22219157 = 1041523) B1041523
theorem B30771683 : Blo 842353 30771683 := bstep (se 1 (by rfl) ⟨23078762, by rfl⟩ : syracuseStep 30771683 = 46157525) B46157525
theorem B4885037 : Blo 842353 4885037 := bstep (se 3 (by rfl) ⟨915944, by rfl⟩ : syracuseStep 4885037 = 1831889) B1831889
theorem B1903193 : Blo 842353 1903193 := bstep (se 2 (by rfl) ⟨713697, by rfl⟩ : syracuseStep 1903193 = 1427395) B1427395
theorem B1903283 : Blo 842353 1903283 := bstep (se 1 (by rfl) ⟨1427462, by rfl⟩ : syracuseStep 1903283 = 2854925) B2854925
theorem B1903319 : Blo 842353 1903319 := bstep (se 1 (by rfl) ⟨1427489, by rfl⟩ : syracuseStep 1903319 = 2854979) B2854979
theorem B9603845 : Blo 842353 9603845 := bstep (se 4 (by rfl) ⟨900360, by rfl⟩ : syracuseStep 9603845 = 1800721) B1800721
theorem B2853683 : Blo 842353 2853683 := bstep (se 1 (by rfl) ⟨2140262, by rfl⟩ : syracuseStep 2853683 = 4280525) B4280525
theorem B2132801 : Blo 842353 2132801 := bstep (se 2 (by rfl) ⟨799800, by rfl⟩ : syracuseStep 2132801 = 1599601) B1599601
theorem B1903499 : Blo 842353 1903499 := bstep (se 1 (by rfl) ⟨1427624, by rfl⟩ : syracuseStep 1903499 = 2855249) B2855249
theorem B1903553 : Blo 842353 1903553 := bstep (se 2 (by rfl) ⟨713832, by rfl⟩ : syracuseStep 1903553 = 1427665) B1427665
theorem B6491153 : Blo 842353 6491153 := bstep (se 2 (by rfl) ⟨2434182, by rfl⟩ : syracuseStep 6491153 = 4868365) B4868365
theorem B2853953 : Blo 842353 2853953 := bstep (se 2 (by rfl) ⟨1070232, by rfl⟩ : syracuseStep 2853953 = 2140465) B2140465
theorem B1903769 : Blo 842353 1903769 := bstep (se 2 (by rfl) ⟨713913, by rfl⟩ : syracuseStep 1903769 = 1427827) B1427827
theorem B1903859 : Blo 842353 1903859 := bstep (se 1 (by rfl) ⟨1427894, by rfl⟩ : syracuseStep 1903859 = 2855789) B2855789
theorem B1805591 : Blo 842353 1805591 := bstep (se 1 (by rfl) ⟨1354193, by rfl⟩ : syracuseStep 1805591 = 2708387) B2708387
theorem B1903895 : Blo 842353 1903895 := bstep (se 1 (by rfl) ⟨1427921, by rfl⟩ : syracuseStep 1903895 = 2855843) B2855843
theorem B6425891 : Blo 842353 6425891 := bstep (se 1 (by rfl) ⟨4819418, by rfl⟩ : syracuseStep 6425891 = 9638837) B9638837
theorem B2133337 : Blo 842353 2133337 := bstep (se 2 (by rfl) ⟨800001, by rfl⟩ : syracuseStep 2133337 = 1600003) B1600003
theorem B8129969 : Blo 842353 8129969 := bstep (se 2 (by rfl) ⟨3048738, by rfl⟩ : syracuseStep 8129969 = 6097477) B6097477
theorem B1904075 : Blo 842353 1904075 := bstep (se 1 (by rfl) ⟨1428056, by rfl⟩ : syracuseStep 1904075 = 2856113) B2856113
theorem B1904129 : Blo 842353 1904129 := bstep (se 2 (by rfl) ⟨714048, by rfl⟩ : syracuseStep 1904129 = 1428097) B1428097
theorem B2854493 : Blo 842353 2854493 := bstep (se 3 (by rfl) ⟨535217, by rfl⟩ : syracuseStep 2854493 = 1070435) B1070435
theorem B12160813 : Blo 842353 12160813 := bstep (se 3 (by rfl) ⟨2280152, by rfl⟩ : syracuseStep 12160813 = 4560305) B4560305
theorem B29200193 : Blo 842353 29200193 := bstep (se 2 (by rfl) ⟨10950072, by rfl⟩ : syracuseStep 29200193 = 21900145) B21900145
theorem B27430721 : Blo 842353 27430721 := bstep (se 2 (by rfl) ⟨10286520, by rfl⟩ : syracuseStep 27430721 = 20573041) B20573041
theorem B1806155 : Blo 842353 1806155 := bstep (se 1 (by rfl) ⟨1354616, by rfl⟩ : syracuseStep 1806155 = 2709233) B2709233
theorem B6951005 : Blo 842353 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B5411033 : Blo 842353 5411033 := bstep (se 2 (by rfl) ⟨2029137, by rfl⟩ : syracuseStep 5411033 = 4058275) B4058275
theorem B1806617 : Blo 842353 1806617 := bstep (se 2 (by rfl) ⟨677481, by rfl⟩ : syracuseStep 1806617 = 1354963) B1354963
theorem B1446283 : Blo 842353 1446283 := bstep (se 1 (by rfl) ⟨1084712, by rfl⟩ : syracuseStep 1446283 = 2169425) B2169425
theorem B2134451 : Blo 842353 2134451 := bstep (se 1 (by rfl) ⟨1600838, by rfl⟩ : syracuseStep 2134451 = 3201677) B3201677
theorem B3248657 : Blo 842353 3248657 := bstep (se 2 (by rfl) ⟨1218246, by rfl⟩ : syracuseStep 3248657 = 2436493) B2436493
theorem B2888243 : Blo 842353 2888243 := bstep (se 1 (by rfl) ⟨2166182, by rfl⟩ : syracuseStep 2888243 = 4332365) B4332365
theorem B856651 : Blo 842353 856651 := bstep (se 1 (by rfl) ⟨642488, by rfl⟩ : syracuseStep 856651 = 1284977) B1284977
theorem B2855627 : Blo 842353 2855627 := bstep (se 1 (by rfl) ⟨2141720, by rfl⟩ : syracuseStep 2855627 = 4283441) B4283441
theorem B2134745 : Blo 842353 2134745 := bstep (se 2 (by rfl) ⟨800529, by rfl⟩ : syracuseStep 2134745 = 1601059) B1601059
theorem B1643275 : Blo 842353 1643275 := bstep (se 1 (by rfl) ⟨1232456, by rfl⟩ : syracuseStep 1643275 = 2464913) B2464913
theorem B1708825 : Blo 842353 1708825 := bstep (se 2 (by rfl) ⟨640809, by rfl⟩ : syracuseStep 1708825 = 1281619) B1281619
theorem B2855897 : Blo 842353 2855897 := bstep (se 2 (by rfl) ⟨1070961, by rfl⟩ : syracuseStep 2855897 = 2141923) B2141923
theorem B14456069 : Blo 842353 14456069 := bstep (se 4 (by rfl) ⟨1355256, by rfl⟩ : syracuseStep 14456069 = 2710513) B2710513
theorem B13014769 : Blo 842353 13014769 := bstep (se 2 (by rfl) ⟨4880538, by rfl⟩ : syracuseStep 13014769 = 9761077) B9761077
theorem B4560715 : Blo 842353 4560715 := bstep (se 1 (by rfl) ⟨3420536, by rfl⟩ : syracuseStep 4560715 = 6841073) B6841073
theorem B2889665 : Blo 842353 2889665 := bstep (se 2 (by rfl) ⟨1083624, by rfl⟩ : syracuseStep 2889665 = 2167249) B2167249
theorem B4265945 : Blo 842353 4265945 := bstep (se 2 (by rfl) ⟨1599729, by rfl⟩ : syracuseStep 4265945 = 3199459) B3199459
theorem B5478361 : Blo 842353 5478361 := bstep (se 2 (by rfl) ⟨2054385, by rfl⟩ : syracuseStep 5478361 = 4108771) B4108771
theorem B3610669 : Blo 842353 3610669 := bstep (se 3 (by rfl) ⟨677000, by rfl⟩ : syracuseStep 3610669 = 1354001) B1354001
theorem B2136395 : Blo 842353 2136395 := bstep (se 1 (by rfl) ⟨1602296, by rfl⟩ : syracuseStep 2136395 = 3204593) B3204593
theorem B1645171 : Blo 842353 1645171 := bstep (se 1 (by rfl) ⟨1233878, by rfl⟩ : syracuseStep 1645171 = 2467757) B2467757
theorem B8100557 : Blo 842353 8100557 := bstep (se 3 (by rfl) ⟨1518854, by rfl⟩ : syracuseStep 8100557 = 3037709) B3037709
theorem B3251117 : Blo 842353 3251117 := bstep (se 3 (by rfl) ⟨609584, by rfl⟩ : syracuseStep 3251117 = 1219169) B1219169
theorem B8100785 : Blo 842353 8100785 := bstep (se 2 (by rfl) ⟨3037794, by rfl⟩ : syracuseStep 8100785 = 6075589) B6075589
theorem B2399321 : Blo 842353 2399321 := bstep (se 2 (by rfl) ⟨899745, by rfl⟩ : syracuseStep 2399321 = 1799491) B1799491
theorem B1711307 : Blo 842353 1711307 := bstep (se 1 (by rfl) ⟨1283480, by rfl⟩ : syracuseStep 1711307 = 2566961) B2566961
theorem B2137367 : Blo 842353 2137367 := bstep (se 1 (by rfl) ⟨1603025, by rfl⟩ : syracuseStep 2137367 = 3206051) B3206051
theorem B4267565 : Blo 842353 4267565 := bstep (se 3 (by rfl) ⟨800168, by rfl⟩ : syracuseStep 4267565 = 1600337) B1600337
theorem B5414465 : Blo 842353 5414465 := bstep (se 2 (by rfl) ⟨2030424, by rfl⟩ : syracuseStep 5414465 = 4060849) B4060849
theorem B3612377 : Blo 842353 3612377 := bstep (se 2 (by rfl) ⟨1354641, by rfl⟩ : syracuseStep 3612377 = 2709283) B2709283
theorem B2138035 : Blo 842353 2138035 := bstep (se 1 (by rfl) ⟨1603526, by rfl⟩ : syracuseStep 2138035 = 3207053) B3207053
theorem B2138177 : Blo 842353 2138177 := bstep (se 2 (by rfl) ⟨801816, by rfl⟩ : syracuseStep 2138177 = 1603633) B1603633
theorem B1712281 : Blo 842353 1712281 := bstep (se 2 (by rfl) ⟨642105, by rfl⟩ : syracuseStep 1712281 = 1284211) B1284211
theorem B1286411 : Blo 842353 1286411 := bstep (se 1 (by rfl) ⟨964808, by rfl⟩ : syracuseStep 1286411 = 1929617) B1929617
theorem B7414051 : Blo 842353 7414051 := bstep (se 1 (by rfl) ⟨5560538, by rfl⟩ : syracuseStep 7414051 = 11121077) B11121077
theorem B2400587 : Blo 842353 2400587 := bstep (se 1 (by rfl) ⟨1800440, by rfl⟩ : syracuseStep 2400587 = 3600881) B3600881
theorem B3613643 : Blo 842353 3613643 := bstep (se 1 (by rfl) ⟨2710232, by rfl⟩ : syracuseStep 3613643 = 5420465) B5420465
theorem B7218193 : Blo 842353 7218193 := bstep (se 2 (by rfl) ⟨2706822, by rfl⟩ : syracuseStep 7218193 = 5413645) B5413645
theorem B1352791 : Blo 842353 1352791 := bstep (se 1 (by rfl) ⟨1014593, by rfl⟩ : syracuseStep 1352791 = 2029187) B2029187
theorem B1713431 : Blo 842353 1713431 := bstep (se 1 (by rfl) ⟨1285073, by rfl⟩ : syracuseStep 1713431 = 2570147) B2570147
theorem B7218467 : Blo 842353 7218467 := bstep (se 1 (by rfl) ⟨5413850, by rfl⟩ : syracuseStep 7218467 = 10827701) B10827701
theorem B2139443 : Blo 842353 2139443 := bstep (se 1 (by rfl) ⟨1604582, by rfl⟩ : syracuseStep 2139443 = 3209165) B3209165
theorem B3614003 : Blo 842353 3614003 := bstep (se 1 (by rfl) ⟨2710502, by rfl⟩ : syracuseStep 3614003 = 5421005) B5421005
theorem B9119267 : Blo 842353 9119267 := bstep (se 1 (by rfl) ⟨6839450, by rfl⟩ : syracuseStep 9119267 = 13678901) B13678901
theorem B2139979 : Blo 842353 2139979 := bstep (se 1 (by rfl) ⟨1604984, by rfl⟩ : syracuseStep 2139979 = 3209969) B3209969
theorem B1353611 : Blo 842353 1353611 := bstep (se 1 (by rfl) ⟨1015208, by rfl⟩ : syracuseStep 1353611 = 2030417) B2030417
theorem B2140121 : Blo 842353 2140121 := bstep (se 2 (by rfl) ⟨802545, by rfl⟩ : syracuseStep 2140121 = 1605091) B1605091
theorem B1386647 : Blo 842353 1386647 := bstep (se 1 (by rfl) ⟨1039985, by rfl⟩ : syracuseStep 1386647 = 2079971) B2079971
theorem B6072707 : Blo 842353 6072707 := bstep (se 1 (by rfl) ⟨4554530, by rfl⟩ : syracuseStep 6072707 = 9109061) B9109061
theorem B1517975 : Blo 842353 1517975 := bstep (se 1 (by rfl) ⟨1138481, by rfl⟩ : syracuseStep 1517975 = 2276963) B2276963
theorem B82356749 : Blo 842353 82356749 := bstep (se 3 (by rfl) ⟨15441890, by rfl⟩ : syracuseStep 82356749 = 30883781) B30883781
theorem B5778013 : Blo 842353 5778013 := bstep (se 3 (by rfl) ⟨1083377, by rfl⟩ : syracuseStep 5778013 = 2166755) B2166755
theorem B2140951 : Blo 842353 2140951 := bstep (se 1 (by rfl) ⟨1605713, by rfl⟩ : syracuseStep 2140951 = 3211427) B3211427
theorem B2435891 : Blo 842353 2435891 := bstep (se 1 (by rfl) ⟨1826918, by rfl⟩ : syracuseStep 2435891 = 3653837) B3653837
theorem B1354585 : Blo 842353 1354585 := bstep (se 2 (by rfl) ⟨507969, by rfl⟩ : syracuseStep 1354585 = 1015939) B1015939
theorem B2141387 : Blo 842353 2141387 := bstep (se 1 (by rfl) ⟨1606040, by rfl⟩ : syracuseStep 2141387 = 3212081) B3212081
theorem B4271453 : Blo 842353 4271453 := bstep (se 3 (by rfl) ⟨800897, by rfl⟩ : syracuseStep 4271453 = 1601795) B1601795
theorem B6860209 : Blo 842353 6860209 := bstep (se 2 (by rfl) ⟨2572578, by rfl⟩ : syracuseStep 6860209 = 5145157) B5145157
theorem B1715671 : Blo 842353 1715671 := bstep (se 1 (by rfl) ⟨1286753, by rfl⟩ : syracuseStep 1715671 = 2573507) B2573507
theorem B1715735 : Blo 842353 1715735 := bstep (se 1 (by rfl) ⟨1286801, by rfl⟩ : syracuseStep 1715735 = 2573603) B2573603
theorem B2141761 : Blo 842353 2141761 := bstep (se 2 (by rfl) ⟨803160, by rfl⟩ : syracuseStep 2141761 = 1606321) B1606321
theorem B1519411 : Blo 842353 1519411 := bstep (se 1 (by rfl) ⟨1139558, by rfl⟩ : syracuseStep 1519411 = 2279117) B2279117
theorem B7319447 : Blo 842353 7319447 := bstep (se 1 (by rfl) ⟨5489585, by rfl⟩ : syracuseStep 7319447 = 10979171) B10979171
theorem B3420377 : Blo 842353 3420377 := bstep (se 2 (by rfl) ⟨1282641, by rfl⟩ : syracuseStep 3420377 = 2565283) B2565283
theorem B1421975 : Blo 842353 1421975 := bstep (se 1 (by rfl) ⟨1066481, by rfl⟩ : syracuseStep 1421975 = 2132963) B2132963
theorem B3420893 : Blo 842353 3420893 := bstep (se 3 (by rfl) ⟨641417, by rfl⟩ : syracuseStep 3420893 = 1282835) B1282835
theorem B1422103 : Blo 842353 1422103 := bstep (se 1 (by rfl) ⟨1066577, by rfl⟩ : syracuseStep 1422103 = 2133155) B2133155
theorem B2700211 : Blo 842353 2700211 := bstep (se 1 (by rfl) ⟨2025158, by rfl⟩ : syracuseStep 2700211 = 4050317) B4050317
theorem B5846033 : Blo 842353 5846033 := bstep (se 2 (by rfl) ⟨2192262, by rfl⟩ : syracuseStep 5846033 = 4384525) B4384525
theorem B3519533 : Blo 842353 3519533 := bstep (se 3 (by rfl) ⟨659912, by rfl⟩ : syracuseStep 3519533 = 1319825) B1319825
theorem B2700353 : Blo 842353 2700353 := bstep (se 2 (by rfl) ⟨1012632, by rfl⟩ : syracuseStep 2700353 = 2025265) B2025265
theorem B2700467 : Blo 842353 2700467 := bstep (se 1 (by rfl) ⟨2025350, by rfl⟩ : syracuseStep 2700467 = 4050701) B4050701
theorem B1422731 : Blo 842353 1422731 := bstep (se 1 (by rfl) ⟨1067048, by rfl⟩ : syracuseStep 1422731 = 2134097) B2134097
theorem B4273559 : Blo 842353 4273559 := bstep (se 1 (by rfl) ⟨3205169, by rfl⟩ : syracuseStep 4273559 = 6410339) B6410339
theorem B7714199 : Blo 842353 7714199 := bstep (se 1 (by rfl) ⟨5785649, by rfl⟩ : syracuseStep 7714199 = 11571299) B11571299
theorem B6862259 : Blo 842353 6862259 := bstep (se 1 (by rfl) ⟨5146694, by rfl⟩ : syracuseStep 6862259 = 10293389) B10293389
theorem B4797913 : Blo 842353 4797913 := bstep (se 2 (by rfl) ⟨1799217, by rfl⟩ : syracuseStep 4797913 = 3598435) B3598435
theorem B1422859 : Blo 842353 1422859 := bstep (se 1 (by rfl) ⟨1067144, by rfl⟩ : syracuseStep 1422859 = 2134289) B2134289
theorem B2405963 : Blo 842353 2405963 := bstep (se 1 (by rfl) ⟨1804472, by rfl⟩ : syracuseStep 2405963 = 3608945) B3608945
theorem B1423001 : Blo 842353 1423001 := bstep (se 2 (by rfl) ⟨533625, by rfl⟩ : syracuseStep 1423001 = 1067251) B1067251
theorem B4568849 : Blo 842353 4568849 := bstep (se 2 (by rfl) ⟨1713318, by rfl⟩ : syracuseStep 4568849 = 3426637) B3426637
theorem B1423129 : Blo 842353 1423129 := bstep (se 2 (by rfl) ⟨533673, by rfl⟩ : syracuseStep 1423129 = 1067347) B1067347
theorem B866219 : Blo 842353 866219 := bstep (se 1 (by rfl) ⟨649664, by rfl⟩ : syracuseStep 866219 = 1299329) B1299329
theorem B2406361 : Blo 842353 2406361 := bstep (se 2 (by rfl) ⟨902385, by rfl⟩ : syracuseStep 2406361 = 1804771) B1804771
theorem B1423703 : Blo 842353 1423703 := bstep (se 1 (by rfl) ⟨1067777, by rfl⟩ : syracuseStep 1423703 = 2135555) B2135555
theorem B4798871 : Blo 842353 4798871 := bstep (se 1 (by rfl) ⟨3599153, by rfl⟩ : syracuseStep 4798871 = 7198307) B7198307
theorem B5421491 : Blo 842353 5421491 := bstep (se 1 (by rfl) ⟨4066118, by rfl⟩ : syracuseStep 5421491 = 8132237) B8132237
theorem B1423831 : Blo 842353 1423831 := bstep (se 1 (by rfl) ⟨1067873, by rfl⟩ : syracuseStep 1423831 = 2135747) B2135747
theorem B899947 : Blo 842353 899947 := bstep (se 1 (by rfl) ⟨674960, by rfl⟩ : syracuseStep 899947 = 1349921) B1349921
theorem B1424459 : Blo 842353 1424459 := bstep (se 1 (by rfl) ⟨1068344, by rfl⟩ : syracuseStep 1424459 = 2136689) B2136689
theorem B10796125 : Blo 842353 10796125 := bstep (se 3 (by rfl) ⟨2024273, by rfl⟩ : syracuseStep 10796125 = 4048547) B4048547
theorem B2407603 : Blo 842353 2407603 := bstep (se 1 (by rfl) ⟨1805702, by rfl⟩ : syracuseStep 2407603 = 3611405) B3611405
theorem B1424587 : Blo 842353 1424587 := bstep (se 1 (by rfl) ⟨1068440, by rfl⟩ : syracuseStep 1424587 = 2136881) B2136881
theorem B1424729 : Blo 842353 1424729 := bstep (se 2 (by rfl) ⟨534273, by rfl⟩ : syracuseStep 1424729 = 1068547) B1068547
theorem B1424857 : Blo 842353 1424857 := bstep (se 2 (by rfl) ⟨534321, by rfl⟩ : syracuseStep 1424857 = 1068643) B1068643
theorem B868087 : Blo 842353 868087 := bstep (se 1 (by rfl) ⟨651065, by rfl⟩ : syracuseStep 868087 = 1302131) B1302131
theorem B1523699 : Blo 842353 1523699 := bstep (se 1 (by rfl) ⟨1142774, by rfl⟩ : syracuseStep 1523699 = 2285549) B2285549
theorem B1523713 : Blo 842353 1523713 := bstep (se 2 (by rfl) ⟨571392, by rfl⟩ : syracuseStep 1523713 = 1142785) B1142785
theorem B1425431 : Blo 842353 1425431 := bstep (se 1 (by rfl) ⟨1069073, by rfl⟩ : syracuseStep 1425431 = 2138147) B2138147
theorem B1425559 : Blo 842353 1425559 := bstep (se 1 (by rfl) ⟨1069169, by rfl⟩ : syracuseStep 1425559 = 2138339) B2138339
theorem B18497909 : Blo 842353 18497909 := bstep (se 5 (by rfl) ⟨867089, by rfl⟩ : syracuseStep 18497909 = 1734179) B1734179
theorem B2310617 : Blo 842353 2310617 := bstep (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) B1732963
theorem B1622603 : Blo 842353 1622603 := bstep (se 1 (by rfl) ⟨1216952, by rfl⟩ : syracuseStep 1622603 = 2433905) B2433905
theorem B3850841 : Blo 842353 3850841 := bstep (se 2 (by rfl) ⟨1444065, by rfl⟩ : syracuseStep 3850841 = 2888131) B2888131
theorem B1426187 : Blo 842353 1426187 := bstep (se 1 (by rfl) ⟨1069640, by rfl⟩ : syracuseStep 1426187 = 2139281) B2139281
theorem B7324433 : Blo 842353 7324433 := bstep (se 2 (by rfl) ⟨2746662, by rfl⟩ : syracuseStep 7324433 = 5493325) B5493325
theorem B4801355 : Blo 842353 4801355 := bstep (se 1 (by rfl) ⟨3601016, by rfl⟩ : syracuseStep 4801355 = 7202033) B7202033
theorem B901963 : Blo 842353 901963 := bstep (se 1 (by rfl) ⟨676472, by rfl⟩ : syracuseStep 901963 = 1352945) B1352945
theorem B4277123 : Blo 842353 4277123 := bstep (se 1 (by rfl) ⟨3207842, by rfl⟩ : syracuseStep 4277123 = 6415685) B6415685
theorem B1426315 : Blo 842353 1426315 := bstep (se 1 (by rfl) ⟨1069736, by rfl⟩ : syracuseStep 1426315 = 2139473) B2139473
theorem B1426457 : Blo 842353 1426457 := bstep (se 2 (by rfl) ⟨534921, by rfl⟩ : syracuseStep 1426457 = 1069843) B1069843
theorem B1426585 : Blo 842353 1426585 := bstep (se 2 (by rfl) ⟨534969, by rfl⟩ : syracuseStep 1426585 = 1069939) B1069939
theorem B1524953 : Blo 842353 1524953 := bstep (se 2 (by rfl) ⟨571857, by rfl⟩ : syracuseStep 1524953 = 1143715) B1143715
theorem B1852723 : Blo 842353 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B6833483 : Blo 842353 6833483 := bstep (se 1 (by rfl) ⟨5125112, by rfl⟩ : syracuseStep 6833483 = 10250225) B10250225
theorem B24364637 : Blo 842353 24364637 := bstep (se 3 (by rfl) ⟨4568369, by rfl⟩ : syracuseStep 24364637 = 9136739) B9136739
theorem B1066699 : Blo 842353 1066699 := bstep (se 1 (by rfl) ⟨800024, by rfl⟩ : syracuseStep 1066699 = 1600049) B1600049
theorem B1427159 : Blo 842353 1427159 := bstep (se 1 (by rfl) ⟨1070369, by rfl⟩ : syracuseStep 1427159 = 2140739) B2140739
theorem B3655469 : Blo 842353 3655469 := bstep (se 3 (by rfl) ⟨685400, by rfl⟩ : syracuseStep 3655469 = 1370801) B1370801
theorem B20531009 : Blo 842353 20531009 := bstep (se 2 (by rfl) ⟨7699128, by rfl⟩ : syracuseStep 20531009 = 15398257) B15398257
theorem B1427287 : Blo 842353 1427287 := bstep (se 1 (by rfl) ⟨1070465, by rfl⟩ : syracuseStep 1427287 = 2140931) B2140931
theorem B1263563 : Blo 842353 1263563 := bstep (se 1 (by rfl) ⟨947672, by rfl⟩ : syracuseStep 1263563 = 1895345) B1895345
theorem B1263575 : Blo 842353 1263575 := bstep (se 1 (by rfl) ⟨947681, by rfl⟩ : syracuseStep 1263575 = 1895363) B1895363
theorem B2934749 : Blo 842353 2934749 := bstep (se 3 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 2934749 = 1100531) B1100531
theorem B1263641 : Blo 842353 1263641 := bstep (se 2 (by rfl) ⟨473865, by rfl⟩ : syracuseStep 1263641 = 947731) B947731
theorem B1263755 : Blo 842353 1263755 := bstep (se 1 (by rfl) ⟨947816, by rfl⟩ : syracuseStep 1263755 = 1895633) B1895633
theorem B1263767 : Blo 842353 1263767 := bstep (se 1 (by rfl) ⟨947825, by rfl⟩ : syracuseStep 1263767 = 1895651) B1895651
theorem B1263833 : Blo 842353 1263833 := bstep (se 2 (by rfl) ⟨473937, by rfl⟩ : syracuseStep 1263833 = 947875) B947875
theorem B903479 : Blo 842353 903479 := bstep (se 1 (by rfl) ⟨677609, by rfl⟩ : syracuseStep 903479 = 1355219) B1355219
theorem B1263947 : Blo 842353 1263947 := bstep (se 1 (by rfl) ⟨947960, by rfl⟩ : syracuseStep 1263947 = 1895921) B1895921
theorem B1263959 : Blo 842353 1263959 := bstep (se 1 (by rfl) ⟨947969, by rfl⟩ : syracuseStep 1263959 = 1895939) B1895939
theorem B1264025 : Blo 842353 1264025 := bstep (se 2 (by rfl) ⟨474009, by rfl⟩ : syracuseStep 1264025 = 948019) B948019
theorem B1427915 : Blo 842353 1427915 := bstep (se 1 (by rfl) ⟨1070936, by rfl⟩ : syracuseStep 1427915 = 2141873) B2141873
theorem B1264139 : Blo 842353 1264139 := bstep (se 1 (by rfl) ⟨948104, by rfl⟩ : syracuseStep 1264139 = 1896209) B1896209
theorem B1264151 : Blo 842353 1264151 := bstep (se 1 (by rfl) ⟨948113, by rfl⟩ : syracuseStep 1264151 = 1896227) B1896227
theorem B1428043 : Blo 842353 1428043 := bstep (se 1 (by rfl) ⟨1071032, by rfl⟩ : syracuseStep 1428043 = 2142065) B2142065
theorem B1264217 : Blo 842353 1264217 := bstep (se 2 (by rfl) ⟨474081, by rfl⟩ : syracuseStep 1264217 = 948163) B948163
theorem B9751133 : Blo 842353 9751133 := bstep (se 3 (by rfl) ⟨1828337, by rfl⟩ : syracuseStep 9751133 = 3656675) B3656675
theorem B1067671 : Blo 842353 1067671 := bstep (se 1 (by rfl) ⟨800753, by rfl⟩ : syracuseStep 1067671 = 1601507) B1601507
theorem B6408881 : Blo 842353 6408881 := bstep (se 2 (by rfl) ⟨2403330, by rfl⟩ : syracuseStep 6408881 = 4806661) B4806661
theorem B1264331 : Blo 842353 1264331 := bstep (se 1 (by rfl) ⟨948248, by rfl⟩ : syracuseStep 1264331 = 1896497) B1896497
theorem B1264343 : Blo 842353 1264343 := bstep (se 1 (by rfl) ⟨948257, by rfl⟩ : syracuseStep 1264343 = 1896515) B1896515
theorem B1428185 : Blo 842353 1428185 := bstep (se 2 (by rfl) ⟨535569, by rfl⟩ : syracuseStep 1428185 = 1071139) B1071139
theorem B1264409 : Blo 842353 1264409 := bstep (se 2 (by rfl) ⟨474153, by rfl⟩ : syracuseStep 1264409 = 948307) B948307
theorem B1264523 : Blo 842353 1264523 := bstep (se 1 (by rfl) ⟨948392, by rfl⟩ : syracuseStep 1264523 = 1896785) B1896785
theorem B1264535 : Blo 842353 1264535 := bstep (se 1 (by rfl) ⟨948401, by rfl⟩ : syracuseStep 1264535 = 1896803) B1896803
theorem B1264601 : Blo 842353 1264601 := bstep (se 2 (by rfl) ⟨474225, by rfl⟩ : syracuseStep 1264601 = 948451) B948451
theorem B1264715 : Blo 842353 1264715 := bstep (se 1 (by rfl) ⟨948536, by rfl⟩ : syracuseStep 1264715 = 1897073) B1897073
theorem B1264727 : Blo 842353 1264727 := bstep (se 1 (by rfl) ⟨948545, by rfl⟩ : syracuseStep 1264727 = 1897091) B1897091
theorem B8342621 : Blo 842353 8342621 := bstep (se 3 (by rfl) ⟨1564241, by rfl⟩ : syracuseStep 8342621 = 3128483) B3128483
theorem B4574339 : Blo 842353 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B8244355 : Blo 842353 8244355 := bstep (se 1 (by rfl) ⟨6183266, by rfl⟩ : syracuseStep 8244355 = 12366533) B12366533
theorem B6409367 : Blo 842353 6409367 := bstep (se 1 (by rfl) ⟨4807025, by rfl⟩ : syracuseStep 6409367 = 9614051) B9614051
theorem B1264793 : Blo 842353 1264793 := bstep (se 2 (by rfl) ⟨474297, by rfl⟩ : syracuseStep 1264793 = 948595) B948595
theorem B1264907 : Blo 842353 1264907 := bstep (se 1 (by rfl) ⟨948680, by rfl⟩ : syracuseStep 1264907 = 1897361) B1897361
theorem B1264919 : Blo 842353 1264919 := bstep (se 1 (by rfl) ⟨948689, by rfl⟩ : syracuseStep 1264919 = 1897379) B1897379
theorem B1264985 : Blo 842353 1264985 := bstep (se 2 (by rfl) ⟨474369, by rfl⟩ : syracuseStep 1264985 = 948739) B948739
theorem B4804019 : Blo 842353 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B1265099 : Blo 842353 1265099 := bstep (se 1 (by rfl) ⟨948824, by rfl⟩ : syracuseStep 1265099 = 1897649) B1897649
theorem B1068491 : Blo 842353 1068491 := bstep (se 1 (by rfl) ⟨801368, by rfl⟩ : syracuseStep 1068491 = 1602737) B1602737
theorem B1265111 : Blo 842353 1265111 := bstep (se 1 (by rfl) ⟨948833, by rfl⟩ : syracuseStep 1265111 = 1897667) B1897667
theorem B17321485 : Blo 842353 17321485 := bstep (se 3 (by rfl) ⟨3247778, by rfl⟩ : syracuseStep 17321485 = 6495557) B6495557
theorem B15388177 : Blo 842353 15388177 := bstep (se 2 (by rfl) ⟨5770566, by rfl⟩ : syracuseStep 15388177 = 11541133) B11541133
theorem B3198487 : Blo 842353 3198487 := bstep (se 1 (by rfl) ⟨2398865, by rfl⟩ : syracuseStep 3198487 = 4797731) B4797731
theorem B1265177 : Blo 842353 1265177 := bstep (se 2 (by rfl) ⟨474441, by rfl⟩ : syracuseStep 1265177 = 948883) B948883
theorem B1265291 : Blo 842353 1265291 := bstep (se 1 (by rfl) ⟨948968, by rfl⟩ : syracuseStep 1265291 = 1897937) B1897937
theorem B1265303 : Blo 842353 1265303 := bstep (se 1 (by rfl) ⟨948977, by rfl⟩ : syracuseStep 1265303 = 1897955) B1897955
theorem B6082253 : Blo 842353 6082253 := bstep (se 3 (by rfl) ⟨1140422, by rfl⟩ : syracuseStep 6082253 = 2280845) B2280845
theorem B1265369 : Blo 842353 1265369 := bstep (se 2 (by rfl) ⟨474513, by rfl⟩ : syracuseStep 1265369 = 949027) B949027
theorem B1265483 : Blo 842353 1265483 := bstep (se 1 (by rfl) ⟨949112, by rfl⟩ : syracuseStep 1265483 = 1898225) B1898225
theorem B1265495 : Blo 842353 1265495 := bstep (se 1 (by rfl) ⟨949121, by rfl⟩ : syracuseStep 1265495 = 1898243) B1898243
theorem B6082397 : Blo 842353 6082397 := bstep (se 3 (by rfl) ⟨1140449, by rfl⟩ : syracuseStep 6082397 = 2280899) B2280899
theorem B1200025 : Blo 842353 1200025 := bstep (se 2 (by rfl) ⟨450009, by rfl⟩ : syracuseStep 1200025 = 900019) B900019
theorem B1265561 : Blo 842353 1265561 := bstep (se 2 (by rfl) ⟨474585, by rfl⟩ : syracuseStep 1265561 = 949171) B949171
theorem B1265675 : Blo 842353 1265675 := bstep (se 1 (by rfl) ⟨949256, by rfl⟩ : syracuseStep 1265675 = 1898513) B1898513
theorem B1265687 : Blo 842353 1265687 := bstep (se 1 (by rfl) ⟨949265, by rfl⟩ : syracuseStep 1265687 = 1898531) B1898531
theorem B2281537 : Blo 842353 2281537 := bstep (se 2 (by rfl) ⟨855576, by rfl⟩ : syracuseStep 2281537 = 1711153) B1711153
theorem B1953857 : Blo 842353 1953857 := bstep (se 2 (by rfl) ⟨732696, by rfl⟩ : syracuseStep 1953857 = 1465393) B1465393
theorem B1265753 : Blo 842353 1265753 := bstep (se 2 (by rfl) ⟨474657, by rfl⟩ : syracuseStep 1265753 = 949315) B949315
theorem B1069195 : Blo 842353 1069195 := bstep (se 1 (by rfl) ⟨801896, by rfl⟩ : syracuseStep 1069195 = 1603793) B1603793
theorem B1265867 : Blo 842353 1265867 := bstep (se 1 (by rfl) ⟨949400, by rfl⟩ : syracuseStep 1265867 = 1898801) B1898801
theorem B1265879 : Blo 842353 1265879 := bstep (se 1 (by rfl) ⟨949409, by rfl⟩ : syracuseStep 1265879 = 1898819) B1898819
theorem B1265945 : Blo 842353 1265945 := bstep (se 2 (by rfl) ⟨474729, by rfl⟩ : syracuseStep 1265945 = 949459) B949459
theorem B3199277 : Blo 842353 3199277 := bstep (se 3 (by rfl) ⟨599864, by rfl⟩ : syracuseStep 3199277 = 1199729) B1199729
theorem B1266059 : Blo 842353 1266059 := bstep (se 1 (by rfl) ⟨949544, by rfl⟩ : syracuseStep 1266059 = 1899089) B1899089
theorem B1266071 : Blo 842353 1266071 := bstep (se 1 (by rfl) ⟨949553, by rfl⟩ : syracuseStep 1266071 = 1899107) B1899107
theorem B1069463 : Blo 842353 1069463 := bstep (se 1 (by rfl) ⟨802097, by rfl⟩ : syracuseStep 1069463 = 1604195) B1604195
theorem B3854765 : Blo 842353 3854765 := bstep (se 3 (by rfl) ⟨722768, by rfl⟩ : syracuseStep 3854765 = 1445537) B1445537
theorem B1266137 : Blo 842353 1266137 := bstep (se 2 (by rfl) ⟨474801, by rfl⟩ : syracuseStep 1266137 = 949603) B949603
theorem B4280849 : Blo 842353 4280849 := bstep (se 2 (by rfl) ⟨1605318, by rfl⟩ : syracuseStep 4280849 = 3210637) B3210637
theorem B1266251 : Blo 842353 1266251 := bstep (se 1 (by rfl) ⟨949688, by rfl⟩ : syracuseStep 1266251 = 1899377) B1899377
theorem B1266263 : Blo 842353 1266263 := bstep (se 1 (by rfl) ⟨949697, by rfl⟩ : syracuseStep 1266263 = 1899395) B1899395
theorem B1266329 : Blo 842353 1266329 := bstep (se 2 (by rfl) ⟨474873, by rfl⟩ : syracuseStep 1266329 = 949747) B949747
theorem B4281011 : Blo 842353 4281011 := bstep (se 1 (by rfl) ⟨3210758, by rfl⟩ : syracuseStep 4281011 = 6421517) B6421517
theorem B1266443 : Blo 842353 1266443 := bstep (se 1 (by rfl) ⟨949832, by rfl⟩ : syracuseStep 1266443 = 1899665) B1899665
theorem B1266455 : Blo 842353 1266455 := bstep (se 1 (by rfl) ⟨949841, by rfl⟩ : syracuseStep 1266455 = 1899683) B1899683
theorem B4051777 : Blo 842353 4051777 := bstep (se 2 (by rfl) ⟨1519416, by rfl⟩ : syracuseStep 4051777 = 3038833) B3038833
theorem B1266521 : Blo 842353 1266521 := bstep (se 2 (by rfl) ⟨474945, by rfl⟩ : syracuseStep 1266521 = 949891) B949891
theorem B4805477 : Blo 842353 4805477 := bstep (se 4 (by rfl) ⟨450513, by rfl⟩ : syracuseStep 4805477 = 901027) B901027
theorem B1266635 : Blo 842353 1266635 := bstep (se 1 (by rfl) ⟨949976, by rfl⟩ : syracuseStep 1266635 = 1899953) B1899953
theorem B1266647 : Blo 842353 1266647 := bstep (se 1 (by rfl) ⟨949985, by rfl⟩ : syracuseStep 1266647 = 1899971) B1899971
theorem B1266713 : Blo 842353 1266713 := bstep (se 2 (by rfl) ⟨475017, by rfl⟩ : syracuseStep 1266713 = 950035) B950035
theorem B1070167 : Blo 842353 1070167 := bstep (se 1 (by rfl) ⟨802625, by rfl⟩ : syracuseStep 1070167 = 1605251) B1605251
theorem B6935645 : Blo 842353 6935645 := bstep (se 3 (by rfl) ⟨1300433, by rfl⟩ : syracuseStep 6935645 = 2600867) B2600867
theorem B1266827 : Blo 842353 1266827 := bstep (se 1 (by rfl) ⟨950120, by rfl⟩ : syracuseStep 1266827 = 1900241) B1900241
theorem B1266839 : Blo 842353 1266839 := bstep (se 1 (by rfl) ⟨950129, by rfl⟩ : syracuseStep 1266839 = 1900259) B1900259
theorem B1266905 : Blo 842353 1266905 := bstep (se 2 (by rfl) ⟨475089, by rfl⟩ : syracuseStep 1266905 = 950179) B950179
theorem B1201483 : Blo 842353 1201483 := bstep (se 1 (by rfl) ⟨901112, by rfl⟩ : syracuseStep 1201483 = 1802225) B1802225
theorem B1267019 : Blo 842353 1267019 := bstep (se 1 (by rfl) ⟨950264, by rfl⟩ : syracuseStep 1267019 = 1900529) B1900529
theorem B1201495 : Blo 842353 1201495 := bstep (se 1 (by rfl) ⟨901121, by rfl⟩ : syracuseStep 1201495 = 1802243) B1802243
theorem B1267031 : Blo 842353 1267031 := bstep (se 1 (by rfl) ⟨950273, by rfl⟩ : syracuseStep 1267031 = 1900547) B1900547
theorem B4052375 : Blo 842353 4052375 := bstep (se 1 (by rfl) ⟨3039281, by rfl⟩ : syracuseStep 4052375 = 6078563) B6078563
theorem B1267097 : Blo 842353 1267097 := bstep (se 2 (by rfl) ⟨475161, by rfl⟩ : syracuseStep 1267097 = 950323) B950323
theorem B1267211 : Blo 842353 1267211 := bstep (se 1 (by rfl) ⟨950408, by rfl⟩ : syracuseStep 1267211 = 1900817) B1900817
theorem B4806161 : Blo 842353 4806161 := bstep (se 2 (by rfl) ⟨1802310, by rfl⟩ : syracuseStep 4806161 = 3604621) B3604621
theorem B1267223 : Blo 842353 1267223 := bstep (se 1 (by rfl) ⟨950417, by rfl⟩ : syracuseStep 1267223 = 1900835) B1900835
theorem B3429911 : Blo 842353 3429911 := bstep (se 1 (by rfl) ⟨2572433, by rfl⟩ : syracuseStep 3429911 = 5144867) B5144867
theorem B10835491 : Blo 842353 10835491 := bstep (se 1 (by rfl) ⟨8126618, by rfl⟩ : syracuseStep 10835491 = 16253237) B16253237
theorem B1922611 : Blo 842353 1922611 := bstep (se 1 (by rfl) ⟨1441958, by rfl⟩ : syracuseStep 1922611 = 2883917) B2883917
theorem B11130443 : Blo 842353 11130443 := bstep (se 1 (by rfl) ⟨8347832, by rfl⟩ : syracuseStep 11130443 = 16695665) B16695665
theorem B1267289 : Blo 842353 1267289 := bstep (se 2 (by rfl) ⟨475233, by rfl⟩ : syracuseStep 1267289 = 950467) B950467
theorem B3200705 : Blo 842353 3200705 := bstep (se 2 (by rfl) ⟨1200264, by rfl⟩ : syracuseStep 3200705 = 2400529) B2400529
theorem B1267403 : Blo 842353 1267403 := bstep (se 1 (by rfl) ⟨950552, by rfl⟩ : syracuseStep 1267403 = 1901105) B1901105
theorem B1267415 : Blo 842353 1267415 := bstep (se 1 (by rfl) ⟨950561, by rfl⟩ : syracuseStep 1267415 = 1901123) B1901123
theorem B1267481 : Blo 842353 1267481 := bstep (se 2 (by rfl) ⟨475305, by rfl⟩ : syracuseStep 1267481 = 950611) B950611
theorem B1267595 : Blo 842353 1267595 := bstep (se 1 (by rfl) ⟨950696, by rfl⟩ : syracuseStep 1267595 = 1901393) B1901393
theorem B1267607 : Blo 842353 1267607 := bstep (se 1 (by rfl) ⟨950705, by rfl⟩ : syracuseStep 1267607 = 1901411) B1901411
theorem B1267673 : Blo 842353 1267673 := bstep (se 2 (by rfl) ⟨475377, by rfl⟩ : syracuseStep 1267673 = 950755) B950755
theorem B1267787 : Blo 842353 1267787 := bstep (se 1 (by rfl) ⟨950840, by rfl⟩ : syracuseStep 1267787 = 1901681) B1901681
theorem B1267799 : Blo 842353 1267799 := bstep (se 1 (by rfl) ⟨950849, by rfl⟩ : syracuseStep 1267799 = 1901699) B1901699
theorem B3037277 : Blo 842353 3037277 := bstep (se 3 (by rfl) ⟨569489, by rfl⟩ : syracuseStep 3037277 = 1138979) B1138979
theorem B1267865 : Blo 842353 1267865 := bstep (se 2 (by rfl) ⟨475449, by rfl⟩ : syracuseStep 1267865 = 950899) B950899
theorem B2709683 : Blo 842353 2709683 := bstep (se 1 (by rfl) ⟨2032262, by rfl⟩ : syracuseStep 2709683 = 4064525) B4064525
theorem B1267979 : Blo 842353 1267979 := bstep (se 1 (by rfl) ⟨950984, by rfl⟩ : syracuseStep 1267979 = 1901969) B1901969
theorem B1267991 : Blo 842353 1267991 := bstep (se 1 (by rfl) ⟨950993, by rfl⟩ : syracuseStep 1267991 = 1901987) B1901987
theorem B1268057 : Blo 842353 1268057 := bstep (se 2 (by rfl) ⟨475521, by rfl⟩ : syracuseStep 1268057 = 951043) B951043
theorem B1268171 : Blo 842353 1268171 := bstep (se 1 (by rfl) ⟨951128, by rfl⟩ : syracuseStep 1268171 = 1902257) B1902257
theorem B1268183 : Blo 842353 1268183 := bstep (se 1 (by rfl) ⟨951137, by rfl⟩ : syracuseStep 1268183 = 1902275) B1902275
theorem B1268249 : Blo 842353 1268249 := bstep (se 2 (by rfl) ⟨475593, by rfl⟩ : syracuseStep 1268249 = 951187) B951187
theorem B4282955 : Blo 842353 4282955 := bstep (se 1 (by rfl) ⟨3212216, by rfl⟩ : syracuseStep 4282955 = 6424433) B6424433
theorem B842359 : Blo 842353 842359 := bstep (se 1 (by rfl) ⟨631769, by rfl⟩ : syracuseStep 842359 = 1263539) B1263539
theorem B842379 : Blo 842353 842379 := bstep (se 1 (by rfl) ⟨631784, by rfl⟩ : syracuseStep 842379 = 1263569) B1263569
theorem B1268363 : Blo 842353 1268363 := bstep (se 1 (by rfl) ⟨951272, by rfl⟩ : syracuseStep 1268363 = 1902545) B1902545
theorem B842391 : Blo 842353 842391 := bstep (se 1 (by rfl) ⟨631793, by rfl⟩ : syracuseStep 842391 = 1263587) B1263587
theorem B1268375 : Blo 842353 1268375 := bstep (se 1 (by rfl) ⟨951281, by rfl⟩ : syracuseStep 1268375 = 1902563) B1902563
theorem B842411 : Blo 842353 842411 := bstep (se 1 (by rfl) ⟨631808, by rfl⟩ : syracuseStep 842411 = 1263617) B1263617
theorem B842423 : Blo 842353 842423 := bstep (se 1 (by rfl) ⟨631817, by rfl⟩ : syracuseStep 842423 = 1263635) B1263635
theorem B842443 : Blo 842353 842443 := bstep (se 1 (by rfl) ⟨631832, by rfl⟩ : syracuseStep 842443 = 1263665) B1263665
theorem B842455 : Blo 842353 842455 := bstep (se 1 (by rfl) ⟨631841, by rfl⟩ : syracuseStep 842455 = 1263683) B1263683
theorem B1268441 : Blo 842353 1268441 := bstep (se 2 (by rfl) ⟨475665, by rfl⟩ : syracuseStep 1268441 = 951331) B951331
theorem B842475 : Blo 842353 842475 := bstep (se 1 (by rfl) ⟨631856, by rfl⟩ : syracuseStep 842475 = 1263713) B1263713
theorem B842487 : Blo 842353 842487 := bstep (se 1 (by rfl) ⟨631865, by rfl⟩ : syracuseStep 842487 = 1263731) B1263731
theorem B842507 : Blo 842353 842507 := bstep (se 1 (by rfl) ⟨631880, by rfl⟩ : syracuseStep 842507 = 1263761) B1263761
theorem B842519 : Blo 842353 842519 := bstep (se 1 (by rfl) ⟨631889, by rfl⟩ : syracuseStep 842519 = 1263779) B1263779
theorem B842539 : Blo 842353 842539 := bstep (se 1 (by rfl) ⟨631904, by rfl⟩ : syracuseStep 842539 = 1263809) B1263809
theorem B842551 : Blo 842353 842551 := bstep (se 1 (by rfl) ⟨631913, by rfl⟩ : syracuseStep 842551 = 1263827) B1263827
theorem B842571 : Blo 842353 842571 := bstep (se 1 (by rfl) ⟨631928, by rfl⟩ : syracuseStep 842571 = 1263857) B1263857
theorem B1268555 : Blo 842353 1268555 := bstep (se 1 (by rfl) ⟨951416, by rfl⟩ : syracuseStep 1268555 = 1902833) B1902833
theorem B842583 : Blo 842353 842583 := bstep (se 1 (by rfl) ⟨631937, by rfl⟩ : syracuseStep 842583 = 1263875) B1263875
theorem B1268567 : Blo 842353 1268567 := bstep (se 1 (by rfl) ⟨951425, by rfl⟩ : syracuseStep 1268567 = 1902851) B1902851
theorem B2710361 : Blo 842353 2710361 := bstep (se 2 (by rfl) ⟨1016385, by rfl⟩ : syracuseStep 2710361 = 2032771) B2032771
theorem B842603 : Blo 842353 842603 := bstep (se 1 (by rfl) ⟨631952, by rfl⟩ : syracuseStep 842603 = 1263905) B1263905
theorem B842615 : Blo 842353 842615 := bstep (se 1 (by rfl) ⟨631961, by rfl⟩ : syracuseStep 842615 = 1263923) B1263923
theorem B842635 : Blo 842353 842635 := bstep (se 1 (by rfl) ⟨631976, by rfl⟩ : syracuseStep 842635 = 1263953) B1263953
theorem B842647 : Blo 842353 842647 := bstep (se 1 (by rfl) ⟨631985, by rfl⟩ : syracuseStep 842647 = 1263971) B1263971
theorem B1268633 : Blo 842353 1268633 := bstep (se 2 (by rfl) ⟨475737, by rfl⟩ : syracuseStep 1268633 = 951475) B951475
theorem B842667 : Blo 842353 842667 := bstep (se 1 (by rfl) ⟨632000, by rfl⟩ : syracuseStep 842667 = 1264001) B1264001
theorem B842679 : Blo 842353 842679 := bstep (se 1 (by rfl) ⟨632009, by rfl⟩ : syracuseStep 842679 = 1264019) B1264019
theorem B842699 : Blo 842353 842699 := bstep (se 1 (by rfl) ⟨632024, by rfl⟩ : syracuseStep 842699 = 1264049) B1264049
theorem B842711 : Blo 842353 842711 := bstep (se 1 (by rfl) ⟨632033, by rfl⟩ : syracuseStep 842711 = 1264067) B1264067
theorem B842731 : Blo 842353 842731 := bstep (se 1 (by rfl) ⟨632048, by rfl⟩ : syracuseStep 842731 = 1264097) B1264097
theorem B842743 : Blo 842353 842743 := bstep (se 1 (by rfl) ⟨632057, by rfl⟩ : syracuseStep 842743 = 1264115) B1264115
theorem B842763 : Blo 842353 842763 := bstep (se 1 (by rfl) ⟨632072, by rfl⟩ : syracuseStep 842763 = 1264145) B1264145
theorem B1268747 : Blo 842353 1268747 := bstep (se 1 (by rfl) ⟨951560, by rfl⟩ : syracuseStep 1268747 = 1903121) B1903121
theorem B842775 : Blo 842353 842775 := bstep (se 1 (by rfl) ⟨632081, by rfl⟩ : syracuseStep 842775 = 1264163) B1264163
theorem B1268759 : Blo 842353 1268759 := bstep (se 1 (by rfl) ⟨951569, by rfl⟩ : syracuseStep 1268759 = 1903139) B1903139
theorem B842795 : Blo 842353 842795 := bstep (se 1 (by rfl) ⟨632096, by rfl⟩ : syracuseStep 842795 = 1264193) B1264193
theorem B842807 : Blo 842353 842807 := bstep (se 1 (by rfl) ⟨632105, by rfl⟩ : syracuseStep 842807 = 1264211) B1264211
theorem B842827 : Blo 842353 842827 := bstep (se 1 (by rfl) ⟨632120, by rfl⟩ : syracuseStep 842827 = 1264241) B1264241
theorem B842839 : Blo 842353 842839 := bstep (se 1 (by rfl) ⟨632129, by rfl⟩ : syracuseStep 842839 = 1264259) B1264259
theorem B1268825 : Blo 842353 1268825 := bstep (se 2 (by rfl) ⟨475809, by rfl⟩ : syracuseStep 1268825 = 951619) B951619
theorem B842859 : Blo 842353 842859 := bstep (se 1 (by rfl) ⟨632144, by rfl⟩ : syracuseStep 842859 = 1264289) B1264289
theorem B842871 : Blo 842353 842871 := bstep (se 1 (by rfl) ⟨632153, by rfl⟩ : syracuseStep 842871 = 1264307) B1264307
theorem B842891 : Blo 842353 842891 := bstep (se 1 (by rfl) ⟨632168, by rfl⟩ : syracuseStep 842891 = 1264337) B1264337
theorem B3202193 : Blo 842353 3202193 := bstep (se 2 (by rfl) ⟨1200822, by rfl⟩ : syracuseStep 3202193 = 2401645) B2401645
theorem B842903 : Blo 842353 842903 := bstep (se 1 (by rfl) ⟨632177, by rfl⟩ : syracuseStep 842903 = 1264355) B1264355
theorem B5856407 : Blo 842353 5856407 := bstep (se 1 (by rfl) ⟨4392305, by rfl⟩ : syracuseStep 5856407 = 8784611) B8784611
theorem B842923 : Blo 842353 842923 := bstep (se 1 (by rfl) ⟨632192, by rfl⟩ : syracuseStep 842923 = 1264385) B1264385
theorem B842935 : Blo 842353 842935 := bstep (se 1 (by rfl) ⟨632201, by rfl⟩ : syracuseStep 842935 = 1264403) B1264403
theorem B842955 : Blo 842353 842955 := bstep (se 1 (by rfl) ⟨632216, by rfl⟩ : syracuseStep 842955 = 1264433) B1264433
theorem B1268939 : Blo 842353 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B842967 : Blo 842353 842967 := bstep (se 1 (by rfl) ⟨632225, by rfl⟩ : syracuseStep 842967 = 1264451) B1264451
theorem B1268951 : Blo 842353 1268951 := bstep (se 1 (by rfl) ⟨951713, by rfl⟩ : syracuseStep 1268951 = 1903427) B1903427
theorem B842987 : Blo 842353 842987 := bstep (se 1 (by rfl) ⟨632240, by rfl⟩ : syracuseStep 842987 = 1264481) B1264481
theorem B842999 : Blo 842353 842999 := bstep (se 1 (by rfl) ⟨632249, by rfl⟩ : syracuseStep 842999 = 1264499) B1264499
theorem B843019 : Blo 842353 843019 := bstep (se 1 (by rfl) ⟨632264, by rfl⟩ : syracuseStep 843019 = 1264529) B1264529
theorem B7691537 : Blo 842353 7691537 := bstep (se 2 (by rfl) ⟨2884326, by rfl⟩ : syracuseStep 7691537 = 5768653) B5768653
theorem B843031 : Blo 842353 843031 := bstep (se 1 (by rfl) ⟨632273, by rfl⟩ : syracuseStep 843031 = 1264547) B1264547
theorem B1269017 : Blo 842353 1269017 := bstep (se 2 (by rfl) ⟨475881, by rfl⟩ : syracuseStep 1269017 = 951763) B951763
theorem B843051 : Blo 842353 843051 := bstep (se 1 (by rfl) ⟨632288, by rfl⟩ : syracuseStep 843051 = 1264577) B1264577
theorem B843063 : Blo 842353 843063 := bstep (se 1 (by rfl) ⟨632297, by rfl⟩ : syracuseStep 843063 = 1264595) B1264595
theorem B843083 : Blo 842353 843083 := bstep (se 1 (by rfl) ⟨632312, by rfl⟩ : syracuseStep 843083 = 1264625) B1264625
theorem B843095 : Blo 842353 843095 := bstep (se 1 (by rfl) ⟨632321, by rfl⟩ : syracuseStep 843095 = 1264643) B1264643
theorem B1203545 : Blo 842353 1203545 := bstep (se 2 (by rfl) ⟨451329, by rfl⟩ : syracuseStep 1203545 = 902659) B902659
theorem B843115 : Blo 842353 843115 := bstep (se 1 (by rfl) ⟨632336, by rfl⟩ : syracuseStep 843115 = 1264673) B1264673
theorem B843127 : Blo 842353 843127 := bstep (se 1 (by rfl) ⟨632345, by rfl⟩ : syracuseStep 843127 = 1264691) B1264691
theorem B843147 : Blo 842353 843147 := bstep (se 1 (by rfl) ⟨632360, by rfl⟩ : syracuseStep 843147 = 1264721) B1264721
theorem B1269131 : Blo 842353 1269131 := bstep (se 1 (by rfl) ⟨951848, by rfl⟩ : syracuseStep 1269131 = 1903697) B1903697
theorem B5397911 : Blo 842353 5397911 := bstep (se 1 (by rfl) ⟨4048433, by rfl⟩ : syracuseStep 5397911 = 8096867) B8096867
theorem B843159 : Blo 842353 843159 := bstep (se 1 (by rfl) ⟨632369, by rfl⟩ : syracuseStep 843159 = 1264739) B1264739
theorem B1269143 : Blo 842353 1269143 := bstep (se 1 (by rfl) ⟨951857, by rfl⟩ : syracuseStep 1269143 = 1903715) B1903715
theorem B843179 : Blo 842353 843179 := bstep (se 1 (by rfl) ⟨632384, by rfl⟩ : syracuseStep 843179 = 1264769) B1264769
theorem B5135795 : Blo 842353 5135795 := bstep (se 1 (by rfl) ⟨3851846, by rfl⟩ : syracuseStep 5135795 = 7703693) B7703693
theorem B843191 : Blo 842353 843191 := bstep (se 1 (by rfl) ⟨632393, by rfl⟩ : syracuseStep 843191 = 1264787) B1264787
theorem B843211 : Blo 842353 843211 := bstep (se 1 (by rfl) ⟨632408, by rfl⟩ : syracuseStep 843211 = 1264817) B1264817
theorem B843223 : Blo 842353 843223 := bstep (se 1 (by rfl) ⟨632417, by rfl⟩ : syracuseStep 843223 = 1264835) B1264835
theorem B1269209 : Blo 842353 1269209 := bstep (se 2 (by rfl) ⟨475953, by rfl⟩ : syracuseStep 1269209 = 951907) B951907
theorem B843243 : Blo 842353 843243 := bstep (se 1 (by rfl) ⟨632432, by rfl⟩ : syracuseStep 843243 = 1264865) B1264865
theorem B843255 : Blo 842353 843255 := bstep (se 1 (by rfl) ⟨632441, by rfl⟩ : syracuseStep 843255 = 1264883) B1264883
theorem B843275 : Blo 842353 843275 := bstep (se 1 (by rfl) ⟨632456, by rfl⟩ : syracuseStep 843275 = 1264913) B1264913
theorem B843287 : Blo 842353 843287 := bstep (se 1 (by rfl) ⟨632465, by rfl⟩ : syracuseStep 843287 = 1264931) B1264931
theorem B843307 : Blo 842353 843307 := bstep (se 1 (by rfl) ⟨632480, by rfl⟩ : syracuseStep 843307 = 1264961) B1264961
theorem B843319 : Blo 842353 843319 := bstep (se 1 (by rfl) ⟨632489, by rfl⟩ : syracuseStep 843319 = 1264979) B1264979
theorem B843339 : Blo 842353 843339 := bstep (se 1 (by rfl) ⟨632504, by rfl⟩ : syracuseStep 843339 = 1265009) B1265009
theorem B1269323 : Blo 842353 1269323 := bstep (se 1 (by rfl) ⟨951992, by rfl⟩ : syracuseStep 1269323 = 1903985) B1903985
theorem B843351 : Blo 842353 843351 := bstep (se 1 (by rfl) ⟨632513, by rfl⟩ : syracuseStep 843351 = 1265027) B1265027
theorem B1269335 : Blo 842353 1269335 := bstep (se 1 (by rfl) ⟨952001, by rfl⟩ : syracuseStep 1269335 = 1904003) B1904003
theorem B3202649 : Blo 842353 3202649 := bstep (se 2 (by rfl) ⟨1200993, by rfl⟩ : syracuseStep 3202649 = 2401987) B2401987
theorem B843371 : Blo 842353 843371 := bstep (se 1 (by rfl) ⟨632528, by rfl⟩ : syracuseStep 843371 = 1265057) B1265057
theorem B843383 : Blo 842353 843383 := bstep (se 1 (by rfl) ⟨632537, by rfl⟩ : syracuseStep 843383 = 1265075) B1265075
theorem B843403 : Blo 842353 843403 := bstep (se 1 (by rfl) ⟨632552, by rfl⟩ : syracuseStep 843403 = 1265105) B1265105
theorem B843415 : Blo 842353 843415 := bstep (se 1 (by rfl) ⟨632561, by rfl⟩ : syracuseStep 843415 = 1265123) B1265123
theorem B1269401 : Blo 842353 1269401 := bstep (se 2 (by rfl) ⟨476025, by rfl⟩ : syracuseStep 1269401 = 952051) B952051
theorem B843435 : Blo 842353 843435 := bstep (se 1 (by rfl) ⟨632576, by rfl⟩ : syracuseStep 843435 = 1265153) B1265153
theorem B843447 : Blo 842353 843447 := bstep (se 1 (by rfl) ⟨632585, by rfl⟩ : syracuseStep 843447 = 1265171) B1265171
theorem B843467 : Blo 842353 843467 := bstep (se 1 (by rfl) ⟨632600, by rfl⟩ : syracuseStep 843467 = 1265201) B1265201
theorem B843479 : Blo 842353 843479 := bstep (se 1 (by rfl) ⟨632609, by rfl⟩ : syracuseStep 843479 = 1265219) B1265219
theorem B843499 : Blo 842353 843499 := bstep (se 1 (by rfl) ⟨632624, by rfl⟩ : syracuseStep 843499 = 1265249) B1265249
theorem B843511 : Blo 842353 843511 := bstep (se 1 (by rfl) ⟨632633, by rfl⟩ : syracuseStep 843511 = 1265267) B1265267
theorem B843531 : Blo 842353 843531 := bstep (se 1 (by rfl) ⟨632648, by rfl⟩ : syracuseStep 843531 = 1265297) B1265297
theorem B1269515 : Blo 842353 1269515 := bstep (se 1 (by rfl) ⟨952136, by rfl⟩ : syracuseStep 1269515 = 1904273) B1904273
theorem B843543 : Blo 842353 843543 := bstep (se 1 (by rfl) ⟨632657, by rfl⟩ : syracuseStep 843543 = 1265315) B1265315
theorem B1269527 : Blo 842353 1269527 := bstep (se 1 (by rfl) ⟨952145, by rfl⟩ : syracuseStep 1269527 = 1904291) B1904291
theorem B843563 : Blo 842353 843563 := bstep (se 1 (by rfl) ⟨632672, by rfl⟩ : syracuseStep 843563 = 1265345) B1265345
theorem B3202861 : Blo 842353 3202861 := bstep (se 3 (by rfl) ⟨600536, by rfl⟩ : syracuseStep 3202861 = 1201073) B1201073
theorem B843575 : Blo 842353 843575 := bstep (se 1 (by rfl) ⟨632681, by rfl⟩ : syracuseStep 843575 = 1265363) B1265363
theorem B843595 : Blo 842353 843595 := bstep (se 1 (by rfl) ⟨632696, by rfl⟩ : syracuseStep 843595 = 1265393) B1265393
theorem B843607 : Blo 842353 843607 := bstep (se 1 (by rfl) ⟨632705, by rfl⟩ : syracuseStep 843607 = 1265411) B1265411
theorem B3039065 : Blo 842353 3039065 := bstep (se 2 (by rfl) ⟨1139649, by rfl⟩ : syracuseStep 3039065 = 2279299) B2279299
theorem B21651299 : Blo 842353 21651299 := bstep (se 1 (by rfl) ⟨16238474, by rfl⟩ : syracuseStep 21651299 = 32476949) B32476949
theorem B843627 : Blo 842353 843627 := bstep (se 1 (by rfl) ⟨632720, by rfl⟩ : syracuseStep 843627 = 1265441) B1265441
theorem B843639 : Blo 842353 843639 := bstep (se 1 (by rfl) ⟨632729, by rfl⟩ : syracuseStep 843639 = 1265459) B1265459
theorem B843659 : Blo 842353 843659 := bstep (se 1 (by rfl) ⟨632744, by rfl⟩ : syracuseStep 843659 = 1265489) B1265489
theorem B843671 : Blo 842353 843671 := bstep (se 1 (by rfl) ⟨632753, by rfl⟩ : syracuseStep 843671 = 1265507) B1265507
theorem B843691 : Blo 842353 843691 := bstep (se 1 (by rfl) ⟨632768, by rfl⟩ : syracuseStep 843691 = 1265537) B1265537
theorem B843703 : Blo 842353 843703 := bstep (se 1 (by rfl) ⟨632777, by rfl⟩ : syracuseStep 843703 = 1265555) B1265555
theorem B843723 : Blo 842353 843723 := bstep (se 1 (by rfl) ⟨632792, by rfl⟩ : syracuseStep 843723 = 1265585) B1265585
theorem B843735 : Blo 842353 843735 := bstep (se 1 (by rfl) ⟨632801, by rfl⟩ : syracuseStep 843735 = 1265603) B1265603
theorem B1204183 : Blo 842353 1204183 := bstep (se 1 (by rfl) ⟨903137, by rfl⟩ : syracuseStep 1204183 = 1806275) B1806275
theorem B843755 : Blo 842353 843755 := bstep (se 1 (by rfl) ⟨632816, by rfl⟩ : syracuseStep 843755 = 1265633) B1265633
theorem B843767 : Blo 842353 843767 := bstep (se 1 (by rfl) ⟨632825, by rfl⟩ : syracuseStep 843767 = 1265651) B1265651
theorem B843787 : Blo 842353 843787 := bstep (se 1 (by rfl) ⟨632840, by rfl⟩ : syracuseStep 843787 = 1265681) B1265681
theorem B843799 : Blo 842353 843799 := bstep (se 1 (by rfl) ⟨632849, by rfl⟩ : syracuseStep 843799 = 1265699) B1265699
theorem B843819 : Blo 842353 843819 := bstep (se 1 (by rfl) ⟨632864, by rfl⟩ : syracuseStep 843819 = 1265729) B1265729
theorem B843831 : Blo 842353 843831 := bstep (se 1 (by rfl) ⟨632873, by rfl⟩ : syracuseStep 843831 = 1265747) B1265747
theorem B843851 : Blo 842353 843851 := bstep (se 1 (by rfl) ⟨632888, by rfl⟩ : syracuseStep 843851 = 1265777) B1265777
theorem B843863 : Blo 842353 843863 := bstep (se 1 (by rfl) ⟨632897, by rfl⟩ : syracuseStep 843863 = 1265795) B1265795
theorem B3203165 : Blo 842353 3203165 := bstep (se 3 (by rfl) ⟨600593, by rfl⟩ : syracuseStep 3203165 = 1201187) B1201187
theorem B843883 : Blo 842353 843883 := bstep (se 1 (by rfl) ⟨632912, by rfl⟩ : syracuseStep 843883 = 1265825) B1265825
theorem B843895 : Blo 842353 843895 := bstep (se 1 (by rfl) ⟨632921, by rfl⟩ : syracuseStep 843895 = 1265843) B1265843
theorem B843915 : Blo 842353 843915 := bstep (se 1 (by rfl) ⟨632936, by rfl⟩ : syracuseStep 843915 = 1265873) B1265873
theorem B843927 : Blo 842353 843927 := bstep (se 1 (by rfl) ⟨632945, by rfl⟩ : syracuseStep 843927 = 1265891) B1265891
theorem B843947 : Blo 842353 843947 := bstep (se 1 (by rfl) ⟨632960, by rfl⟩ : syracuseStep 843947 = 1265921) B1265921
theorem B1925299 : Blo 842353 1925299 := bstep (se 1 (by rfl) ⟨1443974, by rfl⟩ : syracuseStep 1925299 = 2887949) B2887949
theorem B843959 : Blo 842353 843959 := bstep (se 1 (by rfl) ⟨632969, by rfl⟩ : syracuseStep 843959 = 1265939) B1265939
theorem B843979 : Blo 842353 843979 := bstep (se 1 (by rfl) ⟨632984, by rfl⟩ : syracuseStep 843979 = 1265969) B1265969
theorem B843991 : Blo 842353 843991 := bstep (se 1 (by rfl) ⟨632993, by rfl⟩ : syracuseStep 843991 = 1265987) B1265987
theorem B844011 : Blo 842353 844011 := bstep (se 1 (by rfl) ⟨633008, by rfl⟩ : syracuseStep 844011 = 1266017) B1266017
theorem B844023 : Blo 842353 844023 := bstep (se 1 (by rfl) ⟨633017, by rfl⟩ : syracuseStep 844023 = 1266035) B1266035
theorem B844043 : Blo 842353 844043 := bstep (se 1 (by rfl) ⟨633032, by rfl⟩ : syracuseStep 844043 = 1266065) B1266065
theorem B844055 : Blo 842353 844055 := bstep (se 1 (by rfl) ⟨633041, by rfl⟩ : syracuseStep 844055 = 1266083) B1266083
theorem B844075 : Blo 842353 844075 := bstep (se 1 (by rfl) ⟨633056, by rfl⟩ : syracuseStep 844075 = 1266113) B1266113
theorem B844087 : Blo 842353 844087 := bstep (se 1 (by rfl) ⟨633065, by rfl⟩ : syracuseStep 844087 = 1266131) B1266131
theorem B844107 : Blo 842353 844107 := bstep (se 1 (by rfl) ⟨633080, by rfl⟩ : syracuseStep 844107 = 1266161) B1266161
theorem B844119 : Blo 842353 844119 := bstep (se 1 (by rfl) ⟨633089, by rfl⟩ : syracuseStep 844119 = 1266179) B1266179
theorem B844139 : Blo 842353 844139 := bstep (se 1 (by rfl) ⟨633104, by rfl⟩ : syracuseStep 844139 = 1266209) B1266209
theorem B844151 : Blo 842353 844151 := bstep (se 1 (by rfl) ⟨633113, by rfl⟩ : syracuseStep 844151 = 1266227) B1266227
theorem B844171 : Blo 842353 844171 := bstep (se 1 (by rfl) ⟨633128, by rfl⟩ : syracuseStep 844171 = 1266257) B1266257
theorem B844183 : Blo 842353 844183 := bstep (se 1 (by rfl) ⟨633137, by rfl⟩ : syracuseStep 844183 = 1266275) B1266275
theorem B844203 : Blo 842353 844203 := bstep (se 1 (by rfl) ⟨633152, by rfl⟩ : syracuseStep 844203 = 1266305) B1266305
theorem B844215 : Blo 842353 844215 := bstep (se 1 (by rfl) ⟨633161, by rfl⟩ : syracuseStep 844215 = 1266323) B1266323
theorem B844235 : Blo 842353 844235 := bstep (se 1 (by rfl) ⟨633176, by rfl⟩ : syracuseStep 844235 = 1266353) B1266353
theorem B844247 : Blo 842353 844247 := bstep (se 1 (by rfl) ⟨633185, by rfl⟩ : syracuseStep 844247 = 1266371) B1266371
theorem B844267 : Blo 842353 844267 := bstep (se 1 (by rfl) ⟨633200, by rfl⟩ : syracuseStep 844267 = 1266401) B1266401
theorem B844279 : Blo 842353 844279 := bstep (se 1 (by rfl) ⟨633209, by rfl⟩ : syracuseStep 844279 = 1266419) B1266419
theorem B844299 : Blo 842353 844299 := bstep (se 1 (by rfl) ⟨633224, by rfl⟩ : syracuseStep 844299 = 1266449) B1266449
theorem B844311 : Blo 842353 844311 := bstep (se 1 (by rfl) ⟨633233, by rfl⟩ : syracuseStep 844311 = 1266467) B1266467
theorem B844331 : Blo 842353 844331 := bstep (se 1 (by rfl) ⟨633248, by rfl⟩ : syracuseStep 844331 = 1266497) B1266497
theorem B844343 : Blo 842353 844343 := bstep (se 1 (by rfl) ⟨633257, by rfl⟩ : syracuseStep 844343 = 1266515) B1266515
theorem B844363 : Blo 842353 844363 := bstep (se 1 (by rfl) ⟨633272, by rfl⟩ : syracuseStep 844363 = 1266545) B1266545
theorem B844375 : Blo 842353 844375 := bstep (se 1 (by rfl) ⟨633281, by rfl⟩ : syracuseStep 844375 = 1266563) B1266563
theorem B844395 : Blo 842353 844395 := bstep (se 1 (by rfl) ⟨633296, by rfl⟩ : syracuseStep 844395 = 1266593) B1266593
theorem B844407 : Blo 842353 844407 := bstep (se 1 (by rfl) ⟨633305, by rfl⟩ : syracuseStep 844407 = 1266611) B1266611
theorem B844427 : Blo 842353 844427 := bstep (se 1 (by rfl) ⟨633320, by rfl⟩ : syracuseStep 844427 = 1266641) B1266641
theorem B844439 : Blo 842353 844439 := bstep (se 1 (by rfl) ⟨633329, by rfl⟩ : syracuseStep 844439 = 1266659) B1266659
theorem B844459 : Blo 842353 844459 := bstep (se 1 (by rfl) ⟨633344, by rfl⟩ : syracuseStep 844459 = 1266689) B1266689
theorem B2843315 : Blo 842353 2843315 := bstep (se 1 (by rfl) ⟨2132486, by rfl⟩ : syracuseStep 2843315 = 4264973) B4264973
theorem B4809395 : Blo 842353 4809395 := bstep (se 1 (by rfl) ⟨3607046, by rfl⟩ : syracuseStep 4809395 = 7214093) B7214093
theorem B844471 : Blo 842353 844471 := bstep (se 1 (by rfl) ⟨633353, by rfl⟩ : syracuseStep 844471 = 1266707) B1266707
theorem B844491 : Blo 842353 844491 := bstep (se 1 (by rfl) ⟨633368, by rfl⟩ : syracuseStep 844491 = 1266737) B1266737
theorem B844503 : Blo 842353 844503 := bstep (se 1 (by rfl) ⟨633377, by rfl⟩ : syracuseStep 844503 = 1266755) B1266755
theorem B844523 : Blo 842353 844523 := bstep (se 1 (by rfl) ⟨633392, by rfl⟩ : syracuseStep 844523 = 1266785) B1266785
theorem B844535 : Blo 842353 844535 := bstep (se 1 (by rfl) ⟨633401, by rfl⟩ : syracuseStep 844535 = 1266803) B1266803
theorem B844555 : Blo 842353 844555 := bstep (se 1 (by rfl) ⟨633416, by rfl⟩ : syracuseStep 844555 = 1266833) B1266833
theorem B1205003 : Blo 842353 1205003 := bstep (se 1 (by rfl) ⟨903752, by rfl⟩ : syracuseStep 1205003 = 1807505) B1807505
theorem B844567 : Blo 842353 844567 := bstep (se 1 (by rfl) ⟨633425, by rfl⟩ : syracuseStep 844567 = 1266851) B1266851
theorem B844587 : Blo 842353 844587 := bstep (se 1 (by rfl) ⟨633440, by rfl⟩ : syracuseStep 844587 = 1266881) B1266881
theorem B5202733 : Blo 842353 5202733 := bstep (se 3 (by rfl) ⟨975512, by rfl⟩ : syracuseStep 5202733 = 1951025) B1951025
theorem B6087469 : Blo 842353 6087469 := bstep (se 3 (by rfl) ⟨1141400, by rfl⟩ : syracuseStep 6087469 = 2282801) B2282801
theorem B844599 : Blo 842353 844599 := bstep (se 1 (by rfl) ⟨633449, by rfl⟩ : syracuseStep 844599 = 1266899) B1266899
theorem B844619 : Blo 842353 844619 := bstep (se 1 (by rfl) ⟨633464, by rfl⟩ : syracuseStep 844619 = 1266929) B1266929
theorem B844631 : Blo 842353 844631 := bstep (se 1 (by rfl) ⟨633473, by rfl⟩ : syracuseStep 844631 = 1266947) B1266947
theorem B844651 : Blo 842353 844651 := bstep (se 1 (by rfl) ⟨633488, by rfl⟩ : syracuseStep 844651 = 1266977) B1266977
theorem B844663 : Blo 842353 844663 := bstep (se 1 (by rfl) ⟨633497, by rfl⟩ : syracuseStep 844663 = 1266995) B1266995
theorem B844683 : Blo 842353 844683 := bstep (se 1 (by rfl) ⟨633512, by rfl⟩ : syracuseStep 844683 = 1267025) B1267025
theorem B844695 : Blo 842353 844695 := bstep (se 1 (by rfl) ⟨633521, by rfl⟩ : syracuseStep 844695 = 1267043) B1267043
theorem B844715 : Blo 842353 844715 := bstep (se 1 (by rfl) ⟨633536, by rfl⟩ : syracuseStep 844715 = 1267073) B1267073
theorem B8217521 : Blo 842353 8217521 := bstep (se 2 (by rfl) ⟨3081570, by rfl⟩ : syracuseStep 8217521 = 6163141) B6163141
theorem B844727 : Blo 842353 844727 := bstep (se 1 (by rfl) ⟨633545, by rfl⟩ : syracuseStep 844727 = 1267091) B1267091
theorem B2843585 : Blo 842353 2843585 := bstep (se 2 (by rfl) ⟨1066344, by rfl⟩ : syracuseStep 2843585 = 2132689) B2132689
theorem B844747 : Blo 842353 844747 := bstep (se 1 (by rfl) ⟨633560, by rfl⟩ : syracuseStep 844747 = 1267121) B1267121
theorem B1139671 : Blo 842353 1139671 := bstep (se 1 (by rfl) ⟨854753, by rfl⟩ : syracuseStep 1139671 = 1709507) B1709507
theorem B844759 : Blo 842353 844759 := bstep (se 1 (by rfl) ⟨633569, by rfl⟩ : syracuseStep 844759 = 1267139) B1267139
theorem B844779 : Blo 842353 844779 := bstep (se 1 (by rfl) ⟨633584, by rfl⟩ : syracuseStep 844779 = 1267169) B1267169
theorem B844791 : Blo 842353 844791 := bstep (se 1 (by rfl) ⟨633593, by rfl⟩ : syracuseStep 844791 = 1267187) B1267187
theorem B844811 : Blo 842353 844811 := bstep (se 1 (by rfl) ⟨633608, by rfl⟩ : syracuseStep 844811 = 1267217) B1267217
theorem B844823 : Blo 842353 844823 := bstep (se 1 (by rfl) ⟨633617, by rfl⟩ : syracuseStep 844823 = 1267235) B1267235
theorem B844843 : Blo 842353 844843 := bstep (se 1 (by rfl) ⟨633632, by rfl⟩ : syracuseStep 844843 = 1267265) B1267265
theorem B844855 : Blo 842353 844855 := bstep (se 1 (by rfl) ⟨633641, by rfl⟩ : syracuseStep 844855 = 1267283) B1267283
theorem B844875 : Blo 842353 844875 := bstep (se 1 (by rfl) ⟨633656, by rfl⟩ : syracuseStep 844875 = 1267313) B1267313
theorem B844887 : Blo 842353 844887 := bstep (se 1 (by rfl) ⟨633665, by rfl⟩ : syracuseStep 844887 = 1267331) B1267331
theorem B844907 : Blo 842353 844907 := bstep (se 1 (by rfl) ⟨633680, by rfl⟩ : syracuseStep 844907 = 1267361) B1267361
theorem B844919 : Blo 842353 844919 := bstep (se 1 (by rfl) ⟨633689, by rfl⟩ : syracuseStep 844919 = 1267379) B1267379
theorem B844939 : Blo 842353 844939 := bstep (se 1 (by rfl) ⟨633704, by rfl⟩ : syracuseStep 844939 = 1267409) B1267409
theorem B844951 : Blo 842353 844951 := bstep (se 1 (by rfl) ⟨633713, by rfl⟩ : syracuseStep 844951 = 1267427) B1267427
theorem B844971 : Blo 842353 844971 := bstep (se 1 (by rfl) ⟨633728, by rfl⟩ : syracuseStep 844971 = 1267457) B1267457
theorem B844983 : Blo 842353 844983 := bstep (se 1 (by rfl) ⟨633737, by rfl⟩ : syracuseStep 844983 = 1267475) B1267475
theorem B845003 : Blo 842353 845003 := bstep (se 1 (by rfl) ⟨633752, by rfl⟩ : syracuseStep 845003 = 1267505) B1267505
theorem B845015 : Blo 842353 845015 := bstep (se 1 (by rfl) ⟨633761, by rfl⟩ : syracuseStep 845015 = 1267523) B1267523
theorem B845035 : Blo 842353 845035 := bstep (se 1 (by rfl) ⟨633776, by rfl⟩ : syracuseStep 845035 = 1267553) B1267553
theorem B845047 : Blo 842353 845047 := bstep (se 1 (by rfl) ⟨633785, by rfl⟩ : syracuseStep 845047 = 1267571) B1267571
theorem B845067 : Blo 842353 845067 := bstep (se 1 (by rfl) ⟨633800, by rfl⟩ : syracuseStep 845067 = 1267601) B1267601
theorem B845079 : Blo 842353 845079 := bstep (se 1 (by rfl) ⟨633809, by rfl⟩ : syracuseStep 845079 = 1267619) B1267619
theorem B845099 : Blo 842353 845099 := bstep (se 1 (by rfl) ⟨633824, by rfl⟩ : syracuseStep 845099 = 1267649) B1267649
theorem B845111 : Blo 842353 845111 := bstep (se 1 (by rfl) ⟨633833, by rfl⟩ : syracuseStep 845111 = 1267667) B1267667
theorem B845131 : Blo 842353 845131 := bstep (se 1 (by rfl) ⟨633848, by rfl⟩ : syracuseStep 845131 = 1267697) B1267697
theorem B845143 : Blo 842353 845143 := bstep (se 1 (by rfl) ⟨633857, by rfl⟩ : syracuseStep 845143 = 1267715) B1267715
theorem B5399909 : Blo 842353 5399909 := bstep (se 4 (by rfl) ⟨506241, by rfl⟩ : syracuseStep 5399909 = 1012483) B1012483
theorem B845163 : Blo 842353 845163 := bstep (se 1 (by rfl) ⟨633872, by rfl⟩ : syracuseStep 845163 = 1267745) B1267745
theorem B845175 : Blo 842353 845175 := bstep (se 1 (by rfl) ⟨633881, by rfl⟩ : syracuseStep 845175 = 1267763) B1267763
theorem B845195 : Blo 842353 845195 := bstep (se 1 (by rfl) ⟨633896, by rfl⟩ : syracuseStep 845195 = 1267793) B1267793
theorem B845207 : Blo 842353 845207 := bstep (se 1 (by rfl) ⟨633905, by rfl⟩ : syracuseStep 845207 = 1267811) B1267811
theorem B845227 : Blo 842353 845227 := bstep (se 1 (by rfl) ⟨633920, by rfl⟩ : syracuseStep 845227 = 1267841) B1267841
theorem B845239 : Blo 842353 845239 := bstep (se 1 (by rfl) ⟨633929, by rfl⟩ : syracuseStep 845239 = 1267859) B1267859
theorem B845259 : Blo 842353 845259 := bstep (se 1 (by rfl) ⟨633944, by rfl⟩ : syracuseStep 845259 = 1267889) B1267889
theorem B845271 : Blo 842353 845271 := bstep (se 1 (by rfl) ⟨633953, by rfl⟩ : syracuseStep 845271 = 1267907) B1267907
theorem B2844125 : Blo 842353 2844125 := bstep (se 3 (by rfl) ⟨533273, by rfl⟩ : syracuseStep 2844125 = 1066547) B1066547
theorem B845291 : Blo 842353 845291 := bstep (se 1 (by rfl) ⟨633968, by rfl⟩ : syracuseStep 845291 = 1267937) B1267937
theorem B845303 : Blo 842353 845303 := bstep (se 1 (by rfl) ⟨633977, by rfl⟩ : syracuseStep 845303 = 1267955) B1267955
theorem B845323 : Blo 842353 845323 := bstep (se 1 (by rfl) ⟨633992, by rfl⟩ : syracuseStep 845323 = 1267985) B1267985
theorem B845335 : Blo 842353 845335 := bstep (se 1 (by rfl) ⟨634001, by rfl⟩ : syracuseStep 845335 = 1268003) B1268003
theorem B845355 : Blo 842353 845355 := bstep (se 1 (by rfl) ⟨634016, by rfl⟩ : syracuseStep 845355 = 1268033) B1268033
theorem B845367 : Blo 842353 845367 := bstep (se 1 (by rfl) ⟨634025, by rfl⟩ : syracuseStep 845367 = 1268051) B1268051
theorem B845387 : Blo 842353 845387 := bstep (se 1 (by rfl) ⟨634040, by rfl⟩ : syracuseStep 845387 = 1268081) B1268081
theorem B845399 : Blo 842353 845399 := bstep (se 1 (by rfl) ⟨634049, by rfl⟩ : syracuseStep 845399 = 1268099) B1268099
theorem B845419 : Blo 842353 845419 := bstep (se 1 (by rfl) ⟨634064, by rfl⟩ : syracuseStep 845419 = 1268129) B1268129
theorem B845431 : Blo 842353 845431 := bstep (se 1 (by rfl) ⟨634073, by rfl⟩ : syracuseStep 845431 = 1268147) B1268147
theorem B845451 : Blo 842353 845451 := bstep (se 1 (by rfl) ⟨634088, by rfl⟩ : syracuseStep 845451 = 1268177) B1268177
theorem B845463 : Blo 842353 845463 := bstep (se 1 (by rfl) ⟨634097, by rfl⟩ : syracuseStep 845463 = 1268195) B1268195
theorem B845483 : Blo 842353 845483 := bstep (se 1 (by rfl) ⟨634112, by rfl⟩ : syracuseStep 845483 = 1268225) B1268225
theorem B845495 : Blo 842353 845495 := bstep (se 1 (by rfl) ⟨634121, by rfl⟩ : syracuseStep 845495 = 1268243) B1268243
theorem B845515 : Blo 842353 845515 := bstep (se 1 (by rfl) ⟨634136, by rfl⟩ : syracuseStep 845515 = 1268273) B1268273
theorem B845527 : Blo 842353 845527 := bstep (se 1 (by rfl) ⟨634145, by rfl⟩ : syracuseStep 845527 = 1268291) B1268291
theorem B845547 : Blo 842353 845547 := bstep (se 1 (by rfl) ⟨634160, by rfl⟩ : syracuseStep 845547 = 1268321) B1268321
theorem B845559 : Blo 842353 845559 := bstep (se 1 (by rfl) ⟨634169, by rfl⟩ : syracuseStep 845559 = 1268339) B1268339
theorem B845579 : Blo 842353 845579 := bstep (se 1 (by rfl) ⟨634184, by rfl⟩ : syracuseStep 845579 = 1268369) B1268369
theorem B845591 : Blo 842353 845591 := bstep (se 1 (by rfl) ⟨634193, by rfl⟩ : syracuseStep 845591 = 1268387) B1268387
theorem B845611 : Blo 842353 845611 := bstep (se 1 (by rfl) ⟨634208, by rfl⟩ : syracuseStep 845611 = 1268417) B1268417
theorem B845623 : Blo 842353 845623 := bstep (se 1 (by rfl) ⟨634217, by rfl⟩ : syracuseStep 845623 = 1268435) B1268435
theorem B845643 : Blo 842353 845643 := bstep (se 1 (by rfl) ⟨634232, by rfl⟩ : syracuseStep 845643 = 1268465) B1268465
theorem B845655 : Blo 842353 845655 := bstep (se 1 (by rfl) ⟨634241, by rfl⟩ : syracuseStep 845655 = 1268483) B1268483
theorem B845675 : Blo 842353 845675 := bstep (se 1 (by rfl) ⟨634256, by rfl⟩ : syracuseStep 845675 = 1268513) B1268513
theorem B845687 : Blo 842353 845687 := bstep (se 1 (by rfl) ⟨634265, by rfl⟩ : syracuseStep 845687 = 1268531) B1268531
theorem B845707 : Blo 842353 845707 := bstep (se 1 (by rfl) ⟨634280, by rfl⟩ : syracuseStep 845707 = 1268561) B1268561
theorem B845719 : Blo 842353 845719 := bstep (se 1 (by rfl) ⟨634289, by rfl⟩ : syracuseStep 845719 = 1268579) B1268579
theorem B845739 : Blo 842353 845739 := bstep (se 1 (by rfl) ⟨634304, by rfl⟩ : syracuseStep 845739 = 1268609) B1268609
theorem B845751 : Blo 842353 845751 := bstep (se 1 (by rfl) ⟨634313, by rfl⟩ : syracuseStep 845751 = 1268627) B1268627
theorem B3598283 : Blo 842353 3598283 := bstep (se 1 (by rfl) ⟨2698712, by rfl⟩ : syracuseStep 3598283 = 5397425) B5397425
theorem B845771 : Blo 842353 845771 := bstep (se 1 (by rfl) ⟨634328, by rfl⟩ : syracuseStep 845771 = 1268657) B1268657
theorem B845783 : Blo 842353 845783 := bstep (se 1 (by rfl) ⟨634337, by rfl⟩ : syracuseStep 845783 = 1268675) B1268675
theorem B845803 : Blo 842353 845803 := bstep (se 1 (by rfl) ⟨634352, by rfl⟩ : syracuseStep 845803 = 1268705) B1268705
theorem B845815 : Blo 842353 845815 := bstep (se 1 (by rfl) ⟨634361, by rfl⟩ : syracuseStep 845815 = 1268723) B1268723
theorem B845835 : Blo 842353 845835 := bstep (se 1 (by rfl) ⟨634376, by rfl⟩ : syracuseStep 845835 = 1268753) B1268753
theorem B845847 : Blo 842353 845847 := bstep (se 1 (by rfl) ⟨634385, by rfl⟩ : syracuseStep 845847 = 1268771) B1268771
theorem B845867 : Blo 842353 845867 := bstep (se 1 (by rfl) ⟨634400, by rfl⟩ : syracuseStep 845867 = 1268801) B1268801
theorem B845879 : Blo 842353 845879 := bstep (se 1 (by rfl) ⟨634409, by rfl⟩ : syracuseStep 845879 = 1268819) B1268819
theorem B1599563 : Blo 842353 1599563 := bstep (se 1 (by rfl) ⟨1199672, by rfl⟩ : syracuseStep 1599563 = 2399345) B2399345
theorem B845899 : Blo 842353 845899 := bstep (se 1 (by rfl) ⟨634424, by rfl⟩ : syracuseStep 845899 = 1268849) B1268849
theorem B845911 : Blo 842353 845911 := bstep (se 1 (by rfl) ⟨634433, by rfl⟩ : syracuseStep 845911 = 1268867) B1268867
theorem B4810853 : Blo 842353 4810853 := bstep (se 4 (by rfl) ⟨451017, by rfl⟩ : syracuseStep 4810853 = 902035) B902035
theorem B845931 : Blo 842353 845931 := bstep (se 1 (by rfl) ⟨634448, by rfl⟩ : syracuseStep 845931 = 1268897) B1268897
theorem B845943 : Blo 842353 845943 := bstep (se 1 (by rfl) ⟨634457, by rfl⟩ : syracuseStep 845943 = 1268915) B1268915
theorem B845963 : Blo 842353 845963 := bstep (se 1 (by rfl) ⟨634472, by rfl⟩ : syracuseStep 845963 = 1268945) B1268945
theorem B1370263 : Blo 842353 1370263 := bstep (se 1 (by rfl) ⟨1027697, by rfl⟩ : syracuseStep 1370263 = 2055395) B2055395
theorem B845975 : Blo 842353 845975 := bstep (se 1 (by rfl) ⟨634481, by rfl⟩ : syracuseStep 845975 = 1268963) B1268963
theorem B845995 : Blo 842353 845995 := bstep (se 1 (by rfl) ⟨634496, by rfl⟩ : syracuseStep 845995 = 1268993) B1268993
theorem B846007 : Blo 842353 846007 := bstep (se 1 (by rfl) ⟨634505, by rfl⟩ : syracuseStep 846007 = 1269011) B1269011
theorem B846027 : Blo 842353 846027 := bstep (se 1 (by rfl) ⟨634520, by rfl⟩ : syracuseStep 846027 = 1269041) B1269041
theorem B846039 : Blo 842353 846039 := bstep (se 1 (by rfl) ⟨634529, by rfl⟩ : syracuseStep 846039 = 1269059) B1269059
theorem B846059 : Blo 842353 846059 := bstep (se 1 (by rfl) ⟨634544, by rfl⟩ : syracuseStep 846059 = 1269089) B1269089
theorem B846071 : Blo 842353 846071 := bstep (se 1 (by rfl) ⟨634553, by rfl⟩ : syracuseStep 846071 = 1269107) B1269107
theorem B1599745 : Blo 842353 1599745 := bstep (se 2 (by rfl) ⟨599904, by rfl⟩ : syracuseStep 1599745 = 1199809) B1199809
theorem B846091 : Blo 842353 846091 := bstep (se 1 (by rfl) ⟨634568, by rfl⟩ : syracuseStep 846091 = 1269137) B1269137
theorem B6416657 : Blo 842353 6416657 := bstep (se 2 (by rfl) ⟨2406246, by rfl⟩ : syracuseStep 6416657 = 4812493) B4812493
theorem B846103 : Blo 842353 846103 := bstep (se 1 (by rfl) ⟨634577, by rfl⟩ : syracuseStep 846103 = 1269155) B1269155
theorem B846123 : Blo 842353 846123 := bstep (se 1 (by rfl) ⟨634592, by rfl⟩ : syracuseStep 846123 = 1269185) B1269185
theorem B846135 : Blo 842353 846135 := bstep (se 1 (by rfl) ⟨634601, by rfl⟩ : syracuseStep 846135 = 1269203) B1269203
theorem B846155 : Blo 842353 846155 := bstep (se 1 (by rfl) ⟨634616, by rfl⟩ : syracuseStep 846155 = 1269233) B1269233
theorem B846167 : Blo 842353 846167 := bstep (se 1 (by rfl) ⟨634625, by rfl⟩ : syracuseStep 846167 = 1269251) B1269251
theorem B846187 : Blo 842353 846187 := bstep (se 1 (by rfl) ⟨634640, by rfl⟩ : syracuseStep 846187 = 1269281) B1269281
theorem B846199 : Blo 842353 846199 := bstep (se 1 (by rfl) ⟨634649, by rfl⟩ : syracuseStep 846199 = 1269299) B1269299
theorem B846219 : Blo 842353 846219 := bstep (se 1 (by rfl) ⟨634664, by rfl⟩ : syracuseStep 846219 = 1269329) B1269329
theorem B4221335 : Blo 842353 4221335 := bstep (se 1 (by rfl) ⟨3166001, by rfl⟩ : syracuseStep 4221335 = 6332003) B6332003
theorem B846231 : Blo 842353 846231 := bstep (se 1 (by rfl) ⟨634673, by rfl⟩ : syracuseStep 846231 = 1269347) B1269347
theorem B846251 : Blo 842353 846251 := bstep (se 1 (by rfl) ⟨634688, by rfl⟩ : syracuseStep 846251 = 1269377) B1269377
theorem B846263 : Blo 842353 846263 := bstep (se 1 (by rfl) ⟨634697, by rfl⟩ : syracuseStep 846263 = 1269395) B1269395
theorem B846283 : Blo 842353 846283 := bstep (se 1 (by rfl) ⟨634712, by rfl⟩ : syracuseStep 846283 = 1269425) B1269425
theorem B846295 : Blo 842353 846295 := bstep (se 1 (by rfl) ⟨634721, by rfl⟩ : syracuseStep 846295 = 1269443) B1269443
theorem B846315 : Blo 842353 846315 := bstep (se 1 (by rfl) ⟨634736, by rfl⟩ : syracuseStep 846315 = 1269473) B1269473
theorem B846327 : Blo 842353 846327 := bstep (se 1 (by rfl) ⟨634745, by rfl⟩ : syracuseStep 846327 = 1269491) B1269491
theorem B846347 : Blo 842353 846347 := bstep (se 1 (by rfl) ⟨634760, by rfl⟩ : syracuseStep 846347 = 1269521) B1269521
theorem B4811309 : Blo 842353 4811309 := bstep (se 3 (by rfl) ⟨902120, by rfl⟩ : syracuseStep 4811309 = 1804241) B1804241
theorem B2845259 : Blo 842353 2845259 := bstep (se 1 (by rfl) ⟨2133944, by rfl⟩ : syracuseStep 2845259 = 4267889) B4267889
theorem B1600087 : Blo 842353 1600087 := bstep (se 1 (by rfl) ⟨1200065, by rfl⟩ : syracuseStep 1600087 = 2400131) B2400131
theorem B1927795 : Blo 842353 1927795 := bstep (se 1 (by rfl) ⟨1445846, by rfl⟩ : syracuseStep 1927795 = 2891693) B2891693
theorem B3205763 : Blo 842353 3205763 := bstep (se 1 (by rfl) ⟨2404322, by rfl⟩ : syracuseStep 3205763 = 4808645) B4808645
theorem B3205777 : Blo 842353 3205777 := bstep (se 2 (by rfl) ⟨1202166, by rfl⟩ : syracuseStep 3205777 = 2404333) B2404333
theorem B1600307 : Blo 842353 1600307 := bstep (se 1 (by rfl) ⟨1200230, by rfl⟩ : syracuseStep 1600307 = 2400461) B2400461
theorem B2845529 : Blo 842353 2845529 := bstep (se 2 (by rfl) ⟨1067073, by rfl⟩ : syracuseStep 2845529 = 2134147) B2134147
theorem B3599255 : Blo 842353 3599255 := bstep (se 1 (by rfl) ⟨2699441, by rfl⟩ : syracuseStep 3599255 = 5398883) B5398883
theorem B3206081 : Blo 842353 3206081 := bstep (se 2 (by rfl) ⟨1202280, by rfl⟩ : syracuseStep 3206081 = 2404561) B2404561
theorem B1895435 : Blo 842353 1895435 := bstep (se 1 (by rfl) ⟨1421576, by rfl⟩ : syracuseStep 1895435 = 2843153) B2843153
theorem B1600535 : Blo 842353 1600535 := bstep (se 1 (by rfl) ⟨1200401, by rfl⟩ : syracuseStep 1600535 = 2400803) B2400803
theorem B1895489 : Blo 842353 1895489 := bstep (se 2 (by rfl) ⟨710808, by rfl⟩ : syracuseStep 1895489 = 1421617) B1421617
theorem B1928267 : Blo 842353 1928267 := bstep (se 1 (by rfl) ⟨1446200, by rfl⟩ : syracuseStep 1928267 = 2892401) B2892401
theorem B4811993 : Blo 842353 4811993 := bstep (se 2 (by rfl) ⟨1804497, by rfl⟩ : syracuseStep 4811993 = 3608995) B3608995
theorem B1895705 : Blo 842353 1895705 := bstep (se 2 (by rfl) ⟨710889, by rfl⟩ : syracuseStep 1895705 = 1421779) B1421779
theorem B1600793 : Blo 842353 1600793 := bstep (se 2 (by rfl) ⟨600297, by rfl⟩ : syracuseStep 1600793 = 1200595) B1200595
theorem B1895795 : Blo 842353 1895795 := bstep (se 1 (by rfl) ⟨1421846, by rfl⟩ : syracuseStep 1895795 = 2843693) B2843693
theorem B1895831 : Blo 842353 1895831 := bstep (se 1 (by rfl) ⟨1421873, by rfl⟩ : syracuseStep 1895831 = 2843747) B2843747
theorem B2846231 : Blo 842353 2846231 := bstep (se 1 (by rfl) ⟨2134673, by rfl⟩ : syracuseStep 2846231 = 4269347) B4269347
theorem B3599923 : Blo 842353 3599923 := bstep (se 1 (by rfl) ⟨2699942, by rfl⟩ : syracuseStep 3599923 = 5399885) B5399885
theorem B1896011 : Blo 842353 1896011 := bstep (se 1 (by rfl) ⟨1422008, by rfl⟩ : syracuseStep 1896011 = 2844017) B2844017
theorem B3206749 : Blo 842353 3206749 := bstep (se 3 (by rfl) ⟨601265, by rfl⟩ : syracuseStep 3206749 = 1202531) B1202531
theorem B1896065 : Blo 842353 1896065 := bstep (se 2 (by rfl) ⟨711024, by rfl⟩ : syracuseStep 1896065 = 1422049) B1422049
theorem B1601203 : Blo 842353 1601203 := bstep (se 1 (by rfl) ⟨1200902, by rfl⟩ : syracuseStep 1601203 = 2401805) B2401805
theorem B1896281 : Blo 842353 1896281 := bstep (se 2 (by rfl) ⟨711105, by rfl⟩ : syracuseStep 1896281 = 1422211) B1422211
theorem B1896371 : Blo 842353 1896371 := bstep (se 1 (by rfl) ⟨1422278, by rfl⟩ : syracuseStep 1896371 = 2844557) B2844557
theorem B1896407 : Blo 842353 1896407 := bstep (se 1 (by rfl) ⟨1422305, by rfl⟩ : syracuseStep 1896407 = 2844611) B2844611
theorem B1929217 : Blo 842353 1929217 := bstep (se 2 (by rfl) ⟨723456, by rfl⟩ : syracuseStep 1929217 = 1446913) B1446913
theorem B2846771 : Blo 842353 2846771 := bstep (se 1 (by rfl) ⟨2135078, by rfl⟩ : syracuseStep 2846771 = 4270157) B4270157
theorem B17789003 : Blo 842353 17789003 := bstep (se 1 (by rfl) ⟨13341752, by rfl⟩ : syracuseStep 17789003 = 26683505) B26683505
theorem B1896587 : Blo 842353 1896587 := bstep (se 1 (by rfl) ⟨1422440, by rfl⟩ : syracuseStep 1896587 = 2844881) B2844881
theorem B1601689 : Blo 842353 1601689 := bstep (se 2 (by rfl) ⟨600633, by rfl⟩ : syracuseStep 1601689 = 1201267) B1201267
theorem B1896641 : Blo 842353 1896641 := bstep (se 2 (by rfl) ⟨711240, by rfl⟩ : syracuseStep 1896641 = 1422481) B1422481
theorem B2847041 : Blo 842353 2847041 := bstep (se 2 (by rfl) ⟨1067640, by rfl⟩ : syracuseStep 2847041 = 2135281) B2135281
theorem B4059467 : Blo 842353 4059467 := bstep (se 1 (by rfl) ⟨3044600, by rfl⟩ : syracuseStep 4059467 = 6089201) B6089201
theorem B1896857 : Blo 842353 1896857 := bstep (se 2 (by rfl) ⟨711321, by rfl⟩ : syracuseStep 1896857 = 1422643) B1422643
theorem B1896947 : Blo 842353 1896947 := bstep (se 1 (by rfl) ⟨1422710, by rfl⟩ : syracuseStep 1896947 = 2845421) B2845421
theorem B1896983 : Blo 842353 1896983 := bstep (se 1 (by rfl) ⟨1422737, by rfl⟩ : syracuseStep 1896983 = 2845475) B2845475
theorem B1897163 : Blo 842353 1897163 := bstep (se 1 (by rfl) ⟨1422872, by rfl⟩ : syracuseStep 1897163 = 2845745) B2845745
theorem B1602251 : Blo 842353 1602251 := bstep (se 1 (by rfl) ⟨1201688, by rfl⟩ : syracuseStep 1602251 = 2403377) B2403377
theorem B1897217 : Blo 842353 1897217 := bstep (se 2 (by rfl) ⟨711456, by rfl⟩ : syracuseStep 1897217 = 1422913) B1422913
theorem B3601169 : Blo 842353 3601169 := bstep (se 2 (by rfl) ⟨1350438, by rfl⟩ : syracuseStep 3601169 = 2700877) B2700877
theorem B3208025 : Blo 842353 3208025 := bstep (se 2 (by rfl) ⟨1203009, by rfl⟩ : syracuseStep 3208025 = 2406019) B2406019
theorem B2847581 : Blo 842353 2847581 := bstep (se 3 (by rfl) ⟨533921, by rfl⟩ : syracuseStep 2847581 = 1067843) B1067843
theorem B8123237 : Blo 842353 8123237 := bstep (se 4 (by rfl) ⟨761553, by rfl⟩ : syracuseStep 8123237 = 1523107) B1523107
theorem B1602433 : Blo 842353 1602433 := bstep (se 2 (by rfl) ⟨600912, by rfl⟩ : syracuseStep 1602433 = 1201825) B1201825
theorem B1897433 : Blo 842353 1897433 := bstep (se 2 (by rfl) ⟨711537, by rfl⟩ : syracuseStep 1897433 = 1423075) B1423075
theorem B1897523 : Blo 842353 1897523 := bstep (se 1 (by rfl) ⟨1423142, by rfl⟩ : syracuseStep 1897523 = 2846285) B2846285
theorem B1897559 : Blo 842353 1897559 := bstep (se 1 (by rfl) ⟨1423169, by rfl⟩ : syracuseStep 1897559 = 2846339) B2846339
theorem B1733719 : Blo 842353 1733719 := bstep (se 1 (by rfl) ⟨1300289, by rfl⟩ : syracuseStep 1733719 = 2600579) B2600579
theorem B1799347 : Blo 842353 1799347 := bstep (se 1 (by rfl) ⟨1349510, by rfl⟩ : syracuseStep 1799347 = 2699021) B2699021
theorem B5862617 : Blo 842353 5862617 := bstep (se 2 (by rfl) ⟨2198481, by rfl⟩ : syracuseStep 5862617 = 4396963) B4396963
theorem B1897739 : Blo 842353 1897739 := bstep (se 1 (by rfl) ⟨1423304, by rfl⟩ : syracuseStep 1897739 = 2846609) B2846609
theorem B1897793 : Blo 842353 1897793 := bstep (se 2 (by rfl) ⟨711672, by rfl⟩ : syracuseStep 1897793 = 1423345) B1423345
theorem B947659 : Blo 842353 947659 := bstep (se 1 (by rfl) ⟨710744, by rfl⟩ : syracuseStep 947659 = 1421489) B1421489
theorem B1898009 : Blo 842353 1898009 := bstep (se 2 (by rfl) ⟨711753, by rfl⟩ : syracuseStep 1898009 = 1423507) B1423507
theorem B947767 : Blo 842353 947767 := bstep (se 1 (by rfl) ⟨710825, by rfl⟩ : syracuseStep 947767 = 1421651) B1421651
theorem B1603147 : Blo 842353 1603147 := bstep (se 1 (by rfl) ⟨1202360, by rfl⟩ : syracuseStep 1603147 = 2404721) B2404721
theorem B1898099 : Blo 842353 1898099 := bstep (se 1 (by rfl) ⟨1423574, by rfl⟩ : syracuseStep 1898099 = 2847149) B2847149
theorem B1898135 : Blo 842353 1898135 := bstep (se 1 (by rfl) ⟨1423601, by rfl⟩ : syracuseStep 1898135 = 2847203) B2847203
theorem B1603223 : Blo 842353 1603223 := bstep (se 1 (by rfl) ⟨1202417, by rfl⟩ : syracuseStep 1603223 = 2404835) B2404835
theorem B1799833 : Blo 842353 1799833 := bstep (se 2 (by rfl) ⟨674937, by rfl⟩ : syracuseStep 1799833 = 1349875) B1349875
theorem B947947 : Blo 842353 947947 := bstep (se 1 (by rfl) ⟨710960, by rfl⟩ : syracuseStep 947947 = 1421921) B1421921
theorem B1898315 : Blo 842353 1898315 := bstep (se 1 (by rfl) ⟨1423736, by rfl⟩ : syracuseStep 1898315 = 2847473) B2847473
theorem B948055 : Blo 842353 948055 := bstep (se 1 (by rfl) ⟨711041, by rfl⟩ : syracuseStep 948055 = 1422083) B1422083
theorem B1898369 : Blo 842353 1898369 := bstep (se 2 (by rfl) ⟨711888, by rfl⟩ : syracuseStep 1898369 = 1423777) B1423777
theorem B2848715 : Blo 842353 2848715 := bstep (se 1 (by rfl) ⟨2136536, by rfl⟩ : syracuseStep 2848715 = 4273073) B4273073
theorem B948235 : Blo 842353 948235 := bstep (se 1 (by rfl) ⟨711176, by rfl⟩ : syracuseStep 948235 = 1422353) B1422353
theorem B6420545 : Blo 842353 6420545 := bstep (se 2 (by rfl) ⟨2407704, by rfl⟩ : syracuseStep 6420545 = 4815409) B4815409
theorem B1898585 : Blo 842353 1898585 := bstep (se 2 (by rfl) ⟨711969, by rfl⟩ : syracuseStep 1898585 = 1423939) B1423939
theorem B948343 : Blo 842353 948343 := bstep (se 1 (by rfl) ⟨711257, by rfl⟩ : syracuseStep 948343 = 1422515) B1422515
theorem B1898675 : Blo 842353 1898675 := bstep (se 1 (by rfl) ⟨1424006, by rfl⟩ : syracuseStep 1898675 = 2848013) B2848013
theorem B1013963 : Blo 842353 1013963 := bstep (se 1 (by rfl) ⟨760472, by rfl⟩ : syracuseStep 1013963 = 1520945) B1520945
theorem B1898711 : Blo 842353 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B2848985 : Blo 842353 2848985 := bstep (se 2 (by rfl) ⟨1068369, by rfl⟩ : syracuseStep 2848985 = 2136739) B2136739
theorem B948523 : Blo 842353 948523 := bstep (se 1 (by rfl) ⟨711392, by rfl⟩ : syracuseStep 948523 = 1422785) B1422785
theorem B1603891 : Blo 842353 1603891 := bstep (se 1 (by rfl) ⟨1202918, by rfl⟩ : syracuseStep 1603891 = 2405837) B2405837
theorem B1898891 : Blo 842353 1898891 := bstep (se 1 (by rfl) ⟨1424168, by rfl⟩ : syracuseStep 1898891 = 2848337) B2848337
theorem B948631 : Blo 842353 948631 := bstep (se 1 (by rfl) ⟨711473, by rfl⟩ : syracuseStep 948631 = 1422947) B1422947
theorem B3209651 : Blo 842353 3209651 := bstep (se 1 (by rfl) ⟨2407238, by rfl⟩ : syracuseStep 3209651 = 4814477) B4814477
theorem B12188083 : Blo 842353 12188083 := bstep (se 1 (by rfl) ⟨9141062, by rfl⟩ : syracuseStep 12188083 = 18282125) B18282125
theorem B1898945 : Blo 842353 1898945 := bstep (se 2 (by rfl) ⟨712104, by rfl⟩ : syracuseStep 1898945 = 1424209) B1424209
theorem B3209665 : Blo 842353 3209665 := bstep (se 2 (by rfl) ⟨1203624, by rfl⟩ : syracuseStep 3209665 = 2407249) B2407249
theorem B1604119 : Blo 842353 1604119 := bstep (se 1 (by rfl) ⟨1203089, by rfl⟩ : syracuseStep 1604119 = 2406179) B2406179
theorem B948811 : Blo 842353 948811 := bstep (se 1 (by rfl) ⟨711608, by rfl⟩ : syracuseStep 948811 = 1423217) B1423217
theorem B1604225 : Blo 842353 1604225 := bstep (se 2 (by rfl) ⟨601584, by rfl⟩ : syracuseStep 1604225 = 1203169) B1203169
theorem B1899161 : Blo 842353 1899161 := bstep (se 2 (by rfl) ⟨712185, by rfl⟩ : syracuseStep 1899161 = 1424371) B1424371
theorem B948919 : Blo 842353 948919 := bstep (se 1 (by rfl) ⟨711689, by rfl⟩ : syracuseStep 948919 = 1423379) B1423379
theorem B1899251 : Blo 842353 1899251 := bstep (se 1 (by rfl) ⟨1424438, by rfl⟩ : syracuseStep 1899251 = 2848877) B2848877
theorem B1899287 : Blo 842353 1899287 := bstep (se 1 (by rfl) ⟨1424465, by rfl⟩ : syracuseStep 1899287 = 2848931) B2848931
theorem B1604377 : Blo 842353 1604377 := bstep (se 2 (by rfl) ⟨601641, by rfl⟩ : syracuseStep 1604377 = 1203283) B1203283
theorem B949099 : Blo 842353 949099 := bstep (se 1 (by rfl) ⟨711824, by rfl⟩ : syracuseStep 949099 = 1423649) B1423649
theorem B1735553 : Blo 842353 1735553 := bstep (se 2 (by rfl) ⟨650832, by rfl⟩ : syracuseStep 1735553 = 1301665) B1301665
theorem B2849687 : Blo 842353 2849687 := bstep (se 1 (by rfl) ⟨2137265, by rfl⟩ : syracuseStep 2849687 = 4274531) B4274531
theorem B19037105 : Blo 842353 19037105 := bstep (se 2 (by rfl) ⟨7138914, by rfl⟩ : syracuseStep 19037105 = 14277829) B14277829
theorem B1899467 : Blo 842353 1899467 := bstep (se 1 (by rfl) ⟨1424600, by rfl⟩ : syracuseStep 1899467 = 2849201) B2849201
theorem B949207 : Blo 842353 949207 := bstep (se 1 (by rfl) ⟨711905, by rfl⟩ : syracuseStep 949207 = 1423811) B1423811
theorem B1801217 : Blo 842353 1801217 := bstep (se 2 (by rfl) ⟨675456, by rfl⟩ : syracuseStep 1801217 = 1350913) B1350913
theorem B1899521 : Blo 842353 1899521 := bstep (se 2 (by rfl) ⟨712320, by rfl⟩ : syracuseStep 1899521 = 1424641) B1424641
theorem B949387 : Blo 842353 949387 := bstep (se 1 (by rfl) ⟨712040, by rfl⟩ : syracuseStep 949387 = 1424081) B1424081
theorem B3603629 : Blo 842353 3603629 := bstep (se 3 (by rfl) ⟨675680, by rfl⟩ : syracuseStep 3603629 = 1351361) B1351361
theorem B1899737 : Blo 842353 1899737 := bstep (se 2 (by rfl) ⟨712401, by rfl⟩ : syracuseStep 1899737 = 1424803) B1424803
theorem B949495 : Blo 842353 949495 := bstep (se 1 (by rfl) ⟨712121, by rfl⟩ : syracuseStep 949495 = 1424243) B1424243
theorem B1899827 : Blo 842353 1899827 := bstep (se 1 (by rfl) ⟨1424870, by rfl⟩ : syracuseStep 1899827 = 2849741) B2849741
theorem B1899863 : Blo 842353 1899863 := bstep (se 1 (by rfl) ⟨1424897, by rfl⟩ : syracuseStep 1899863 = 2849795) B2849795
theorem B949675 : Blo 842353 949675 := bstep (se 1 (by rfl) ⟨712256, by rfl⟩ : syracuseStep 949675 = 1424513) B1424513
theorem B2850227 : Blo 842353 2850227 := bstep (se 1 (by rfl) ⟨2137670, by rfl⟩ : syracuseStep 2850227 = 4275341) B4275341
theorem B1801739 : Blo 842353 1801739 := bstep (se 1 (by rfl) ⟨1351304, by rfl⟩ : syracuseStep 1801739 = 2702609) B2702609
theorem B1900043 : Blo 842353 1900043 := bstep (se 1 (by rfl) ⟨1425032, by rfl⟩ : syracuseStep 1900043 = 2850065) B2850065
theorem B949783 : Blo 842353 949783 := bstep (se 1 (by rfl) ⟨712337, by rfl⟩ : syracuseStep 949783 = 1424675) B1424675
theorem B1900097 : Blo 842353 1900097 := bstep (se 2 (by rfl) ⟨712536, by rfl⟩ : syracuseStep 1900097 = 1425073) B1425073
theorem B2850497 : Blo 842353 2850497 := bstep (se 2 (by rfl) ⟨1068936, by rfl⟩ : syracuseStep 2850497 = 2137873) B2137873
theorem B949963 : Blo 842353 949963 := bstep (se 1 (by rfl) ⟨712472, by rfl⟩ : syracuseStep 949963 = 1424945) B1424945
theorem B1900313 : Blo 842353 1900313 := bstep (se 2 (by rfl) ⟨712617, by rfl⟩ : syracuseStep 1900313 = 1425235) B1425235
theorem B4816685 : Blo 842353 4816685 := bstep (se 3 (by rfl) ⟨903128, by rfl⟩ : syracuseStep 4816685 = 1806257) B1806257
theorem B950071 : Blo 842353 950071 := bstep (se 1 (by rfl) ⟨712553, by rfl⟩ : syracuseStep 950071 = 1425107) B1425107
theorem B3604313 : Blo 842353 3604313 := bstep (se 2 (by rfl) ⟨1351617, by rfl⟩ : syracuseStep 3604313 = 2703235) B2703235
theorem B1900403 : Blo 842353 1900403 := bstep (se 1 (by rfl) ⟨1425302, by rfl⟩ : syracuseStep 1900403 = 2850605) B2850605
theorem B1900439 : Blo 842353 1900439 := bstep (se 1 (by rfl) ⟨1425329, by rfl⟩ : syracuseStep 1900439 = 2850659) B2850659
theorem B6422489 : Blo 842353 6422489 := bstep (se 2 (by rfl) ⟨2408433, by rfl⟩ : syracuseStep 6422489 = 4816867) B4816867
theorem B950251 : Blo 842353 950251 := bstep (se 1 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 950251 = 1425377) B1425377
theorem B2031617 : Blo 842353 2031617 := bstep (se 2 (by rfl) ⟨761856, by rfl⟩ : syracuseStep 2031617 = 1523713) B1523713
theorem B950287 : Blo 842353 950287 := bstep (se 1 (by rfl) ⟨712715, by rfl⟩ : syracuseStep 950287 = 1425431) B1425431
theorem B1900691 : Blo 842353 1900691 := bstep (se 1 (by rfl) ⟨1425518, by rfl⟩ : syracuseStep 1900691 = 2851037) B2851037
theorem B1900745 : Blo 842353 1900745 := bstep (se 2 (by rfl) ⟨712779, by rfl⟩ : syracuseStep 1900745 = 1425559) B1425559
theorem B1081735 : Blo 842353 1081735 := bstep (se 1 (by rfl) ⟨811301, by rfl⟩ : syracuseStep 1081735 = 1622603) B1622603
theorem B950791 : Blo 842353 950791 := bstep (se 1 (by rfl) ⟨713093, by rfl⟩ : syracuseStep 950791 = 1426187) B1426187
theorem B4882955 : Blo 842353 4882955 := bstep (se 1 (by rfl) ⟨3662216, by rfl⟩ : syracuseStep 4882955 = 7324433) B7324433
theorem B2851415 : Blo 842353 2851415 := bstep (se 1 (by rfl) ⟨2138561, by rfl⟩ : syracuseStep 2851415 = 4277123) B4277123
theorem B950971 : Blo 842353 950971 := bstep (se 1 (by rfl) ⟨713228, by rfl⟩ : syracuseStep 950971 = 1426457) B1426457
theorem B1016635 : Blo 842353 1016635 := bstep (se 1 (by rfl) ⟨762476, by rfl⟩ : syracuseStep 1016635 = 1524953) B1524953
theorem B4555655 : Blo 842353 4555655 := bstep (se 1 (by rfl) ⟨3416741, by rfl⟩ : syracuseStep 4555655 = 6833483) B6833483
theorem B1901447 : Blo 842353 1901447 := bstep (se 1 (by rfl) ⟨1426085, by rfl⟩ : syracuseStep 1901447 = 2852171) B2852171
theorem B1901627 : Blo 842353 1901627 := bstep (se 1 (by rfl) ⟨1426220, by rfl⟩ : syracuseStep 1901627 = 2852441) B2852441
theorem B2851901 : Blo 842353 2851901 := bstep (se 3 (by rfl) ⟨534731, by rfl⟩ : syracuseStep 2851901 = 1069463) B1069463
theorem B951439 : Blo 842353 951439 := bstep (se 1 (by rfl) ⟨713579, by rfl⟩ : syracuseStep 951439 = 1427159) B1427159
theorem B1901753 : Blo 842353 1901753 := bstep (se 2 (by rfl) ⟨713157, by rfl⟩ : syracuseStep 1901753 = 1426315) B1426315
theorem B6161645 : Blo 842353 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B1803721 : Blo 842353 1803721 := bstep (se 2 (by rfl) ⟨676395, by rfl⟩ : syracuseStep 1803721 = 1352791) B1352791
theorem B1902095 : Blo 842353 1902095 := bstep (se 1 (by rfl) ⟨1426571, by rfl⟩ : syracuseStep 1902095 = 2853143) B2853143
theorem B1902113 : Blo 842353 1902113 := bstep (se 2 (by rfl) ⟨713292, by rfl⟩ : syracuseStep 1902113 = 1426585) B1426585
theorem B951943 : Blo 842353 951943 := bstep (se 1 (by rfl) ⟨713957, by rfl⟩ : syracuseStep 951943 = 1427915) B1427915
theorem B20514455 : Blo 842353 20514455 := bstep (se 1 (by rfl) ⟨15385841, by rfl⟩ : syracuseStep 20514455 = 30771683) B30771683
theorem B952123 : Blo 842353 952123 := bstep (se 1 (by rfl) ⟨714092, by rfl⟩ : syracuseStep 952123 = 1428185) B1428185
theorem B1902455 : Blo 842353 1902455 := bstep (se 1 (by rfl) ⟨1426841, by rfl⟩ : syracuseStep 1902455 = 2853683) B2853683
theorem B4327435 : Blo 842353 4327435 := bstep (se 1 (by rfl) ⟨3245576, by rfl⟩ : syracuseStep 4327435 = 6491153) B6491153
theorem B3213341 : Blo 842353 3213341 := bstep (se 3 (by rfl) ⟨602501, by rfl⟩ : syracuseStep 3213341 = 1205003) B1205003
theorem B1902635 : Blo 842353 1902635 := bstep (se 1 (by rfl) ⟨1426976, by rfl⟩ : syracuseStep 1902635 = 2853953) B2853953
theorem B3049559 : Blo 842353 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B10815605 : Blo 842353 10815605 := bstep (se 5 (by rfl) ⟨506981, by rfl⟩ : syracuseStep 10815605 = 1013963) B1013963
theorem B1902995 : Blo 842353 1902995 := bstep (se 1 (by rfl) ⟨1427246, by rfl⟩ : syracuseStep 1902995 = 2854493) B2854493
theorem B2853305 : Blo 842353 2853305 := bstep (se 2 (by rfl) ⟨1069989, by rfl⟩ : syracuseStep 2853305 = 2139979) B2139979
theorem B1903049 : Blo 842353 1903049 := bstep (se 2 (by rfl) ⟨713643, by rfl⟩ : syracuseStep 1903049 = 1427287) B1427287
theorem B19466795 : Blo 842353 19466795 := bstep (se 1 (by rfl) ⟨14600096, by rfl⟩ : syracuseStep 19466795 = 29200193) B29200193
theorem B18287147 : Blo 842353 18287147 := bstep (se 1 (by rfl) ⟨13715360, by rfl⟩ : syracuseStep 18287147 = 27430721) B27430721
theorem B3607355 : Blo 842353 3607355 := bstep (se 1 (by rfl) ⟨2705516, by rfl⟩ : syracuseStep 3607355 = 5411033) B5411033
theorem B2132851 : Blo 842353 2132851 := bstep (se 1 (by rfl) ⟨1599638, by rfl⟩ : syracuseStep 2132851 = 3199277) B3199277
theorem B2132993 : Blo 842353 2132993 := bstep (se 2 (by rfl) ⟨799872, by rfl⟩ : syracuseStep 2132993 = 1599745) B1599745
theorem B2165771 : Blo 842353 2165771 := bstep (se 1 (by rfl) ⟨1624328, by rfl⟩ : syracuseStep 2165771 = 3248657) B3248657
theorem B2853899 : Blo 842353 2853899 := bstep (se 1 (by rfl) ⟨2140424, by rfl⟩ : syracuseStep 2853899 = 4280849) B4280849
theorem B2854007 : Blo 842353 2854007 := bstep (se 1 (by rfl) ⟨2140505, by rfl⟩ : syracuseStep 2854007 = 4281011) B4281011
theorem B1903751 : Blo 842353 1903751 := bstep (se 1 (by rfl) ⟨1427813, by rfl⟩ : syracuseStep 1903751 = 2855627) B2855627
theorem B1903931 : Blo 842353 1903931 := bstep (se 1 (by rfl) ⟨1427948, by rfl⟩ : syracuseStep 1903931 = 2855897) B2855897
theorem B4623763 : Blo 842353 4623763 := bstep (se 1 (by rfl) ⟨3467822, by rfl⟩ : syracuseStep 4623763 = 6935645) B6935645
theorem B1904057 : Blo 842353 1904057 := bstep (se 2 (by rfl) ⟨714021, by rfl⟩ : syracuseStep 1904057 = 1428043) B1428043
theorem B2133449 : Blo 842353 2133449 := bstep (se 2 (by rfl) ⟨800043, by rfl⟩ : syracuseStep 2133449 = 1600087) B1600087
theorem B7704017 : Blo 842353 7704017 := bstep (se 2 (by rfl) ⟨2889006, by rfl⟩ : syracuseStep 7704017 = 5778013) B5778013
theorem B9637379 : Blo 842353 9637379 := bstep (se 1 (by rfl) ⟨7228034, by rfl⟩ : syracuseStep 9637379 = 14456069) B14456069
theorem B2854601 : Blo 842353 2854601 := bstep (se 2 (by rfl) ⟨1070475, by rfl⟩ : syracuseStep 2854601 = 2140951) B2140951
theorem B1806113 : Blo 842353 1806113 := bstep (se 2 (by rfl) ⟨677292, by rfl⟩ : syracuseStep 1806113 = 1354585) B1354585
theorem B2133803 : Blo 842353 2133803 := bstep (se 1 (by rfl) ⟨1600352, by rfl⟩ : syracuseStep 2133803 = 3200705) B3200705
theorem B9146429 : Blo 842353 9146429 := bstep (se 3 (by rfl) ⟨1714955, by rfl⟩ : syracuseStep 9146429 = 3429911) B3429911
theorem B1806455 : Blo 842353 1806455 := bstep (se 1 (by rfl) ⟨1354841, by rfl⟩ : syracuseStep 1806455 = 2709683) B2709683
theorem B2855303 : Blo 842353 2855303 := bstep (se 1 (by rfl) ⟨2141477, by rfl⟩ : syracuseStep 2855303 = 4282955) B4282955
theorem B1806907 : Blo 842353 1806907 := bstep (se 1 (by rfl) ⟨1355180, by rfl⟩ : syracuseStep 1806907 = 2710361) B2710361
theorem B9146945 : Blo 842353 9146945 := bstep (se 2 (by rfl) ⟨3430104, by rfl⟩ : syracuseStep 9146945 = 6860209) B6860209
theorem B20517569 : Blo 842353 20517569 := bstep (se 2 (by rfl) ⟨7694088, by rfl⟩ : syracuseStep 20517569 = 15388177) B15388177
theorem B4264649 : Blo 842353 4264649 := bstep (se 2 (by rfl) ⟨1599243, by rfl⟩ : syracuseStep 4264649 = 3198487) B3198487
theorem B2855681 : Blo 842353 2855681 := bstep (se 2 (by rfl) ⟨1070880, by rfl⟩ : syracuseStep 2855681 = 2141761) B2141761
theorem B2134795 : Blo 842353 2134795 := bstep (se 1 (by rfl) ⟨1601096, by rfl⟩ : syracuseStep 2134795 = 3202193) B3202193
theorem B3904271 : Blo 842353 3904271 := bstep (se 1 (by rfl) ⟨2928203, by rfl⟩ : syracuseStep 3904271 = 5856407) B5856407
theorem B2134937 : Blo 842353 2134937 := bstep (se 2 (by rfl) ⟨800601, by rfl⟩ : syracuseStep 2134937 = 1601203) B1601203
theorem B3609629 : Blo 842353 3609629 := bstep (se 3 (by rfl) ⟨676805, by rfl⟩ : syracuseStep 3609629 = 1353611) B1353611
theorem B2135099 : Blo 842353 2135099 := bstep (se 1 (by rfl) ⟨1601324, by rfl⟩ : syracuseStep 2135099 = 3202649) B3202649
theorem B2135443 : Blo 842353 2135443 := bstep (se 1 (by rfl) ⟨1601582, by rfl⟩ : syracuseStep 2135443 = 3203165) B3203165
theorem B2135585 : Blo 842353 2135585 := bstep (se 2 (by rfl) ⟨800844, by rfl⟩ : syracuseStep 2135585 = 1601689) B1601689
theorem B5478347 : Blo 842353 5478347 := bstep (se 1 (by rfl) ⟨4108760, by rfl⟩ : syracuseStep 5478347 = 8217521) B8217521
theorem B59251085 : Blo 842353 59251085 := bstep (se 3 (by rfl) ⟨11109578, by rfl⟩ : syracuseStep 59251085 = 22219157) B22219157
theorem B2136577 : Blo 842353 2136577 := bstep (se 2 (by rfl) ⟨801216, by rfl⟩ : syracuseStep 2136577 = 1602433) B1602433
theorem B2398855 : Blo 842353 2398855 := bstep (se 1 (by rfl) ⟨1799141, by rfl⟩ : syracuseStep 2398855 = 3598283) B3598283
theorem B924431 : Blo 842353 924431 := bstep (se 1 (by rfl) ⟨693323, by rfl⟩ : syracuseStep 924431 = 1386647) B1386647
theorem B2399129 : Blo 842353 2399129 := bstep (se 2 (by rfl) ⟨899673, by rfl⟩ : syracuseStep 2399129 = 1799347) B1799347
theorem B2137175 : Blo 842353 2137175 := bstep (se 1 (by rfl) ⟨1602881, by rfl⟩ : syracuseStep 2137175 = 3205763) B3205763
theorem B6397217 : Blo 842353 6397217 := bstep (se 2 (by rfl) ⟨2398956, by rfl⟩ : syracuseStep 6397217 = 4797913) B4797913
theorem B2137387 : Blo 842353 2137387 := bstep (se 1 (by rfl) ⟨1603040, by rfl⟩ : syracuseStep 2137387 = 3206081) B3206081
theorem B1285511 : Blo 842353 1285511 := bstep (se 1 (by rfl) ⟨964133, by rfl⟩ : syracuseStep 1285511 = 1928267) B1928267
theorem B2563481 : Blo 842353 2563481 := bstep (se 2 (by rfl) ⟨961305, by rfl⟩ : syracuseStep 2563481 = 1922611) B1922611
theorem B2137529 : Blo 842353 2137529 := bstep (se 2 (by rfl) ⟨801573, by rfl⟩ : syracuseStep 2137529 = 1603147) B1603147
theorem B6495709 : Blo 842353 6495709 := bstep (se 3 (by rfl) ⟨1217945, by rfl⟩ : syracuseStep 6495709 = 2435891) B2435891
theorem B2399777 : Blo 842353 2399777 := bstep (se 2 (by rfl) ⟨899916, by rfl⟩ : syracuseStep 2399777 = 1799833) B1799833
theorem B4628141 : Blo 842353 4628141 := bstep (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) B1735553
theorem B6398189 : Blo 842353 6398189 := bstep (se 3 (by rfl) ⟨1199660, by rfl⟩ : syracuseStep 6398189 = 2399321) B2399321
theorem B2138521 : Blo 842353 2138521 := bstep (se 2 (by rfl) ⟨801945, by rfl⟩ : syracuseStep 2138521 = 1603891) B1603891
theorem B9609677 : Blo 842353 9609677 := bstep (se 3 (by rfl) ⟨1801814, by rfl⟩ : syracuseStep 9609677 = 3603629) B3603629
theorem B2400779 : Blo 842353 2400779 := bstep (se 1 (by rfl) ⟨1800584, by rfl⟩ : syracuseStep 2400779 = 3601169) B3601169
theorem B4563485 : Blo 842353 4563485 := bstep (se 3 (by rfl) ⟨855653, by rfl⟩ : syracuseStep 4563485 = 1711307) B1711307
theorem B2138683 : Blo 842353 2138683 := bstep (se 1 (by rfl) ⟨1604012, by rfl⟩ : syracuseStep 2138683 = 3208025) B3208025
theorem B5415491 : Blo 842353 5415491 := bstep (se 1 (by rfl) ⟨4061618, by rfl⟩ : syracuseStep 5415491 = 8123237) B8123237
theorem B2138825 : Blo 842353 2138825 := bstep (se 2 (by rfl) ⟨802059, by rfl⟩ : syracuseStep 2138825 = 1604119) B1604119
theorem B3908411 : Blo 842353 3908411 := bstep (se 1 (by rfl) ⟨2931308, by rfl⟩ : syracuseStep 3908411 = 5862617) B5862617
theorem B2139169 : Blo 842353 2139169 := bstep (se 2 (by rfl) ⟨802188, by rfl⟩ : syracuseStep 2139169 = 1604377) B1604377
theorem B4629797 : Blo 842353 4629797 := bstep (se 4 (by rfl) ⟨434043, by rfl⟩ : syracuseStep 4629797 = 868087) B868087
theorem B14394833 : Blo 842353 14394833 := bstep (se 2 (by rfl) ⟨5398062, by rfl⟩ : syracuseStep 14394833 = 10796125) B10796125
theorem B2139767 : Blo 842353 2139767 := bstep (se 1 (by rfl) ⟨1604825, by rfl⟩ : syracuseStep 2139767 = 3209651) B3209651
theorem B3614327 : Blo 842353 3614327 := bstep (se 1 (by rfl) ⟨2710745, by rfl⟩ : syracuseStep 3614327 = 5421491) B5421491
theorem B24323813 : Blo 842353 24323813 := bstep (se 4 (by rfl) ⟨2280357, by rfl⟩ : syracuseStep 24323813 = 4560715) B4560715
theorem B12691403 : Blo 842353 12691403 := bstep (se 1 (by rfl) ⟨9518552, by rfl⟩ : syracuseStep 12691403 = 19037105) B19037105
theorem B6400133 : Blo 842353 6400133 := bstep (se 4 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 6400133 = 1200025) B1200025
theorem B4270481 : Blo 842353 4270481 := bstep (se 2 (by rfl) ⟨1601430, by rfl⟩ : syracuseStep 4270481 = 3202861) B3202861
theorem B2402875 : Blo 842353 2402875 := bstep (se 1 (by rfl) ⟨1802156, by rfl⟩ : syracuseStep 2402875 = 3604313) B3604313
theorem B2141063 : Blo 842353 2141063 := bstep (se 1 (by rfl) ⟨1605797, by rfl⟩ : syracuseStep 2141063 = 3211595) B3211595
theorem B2567065 : Blo 842353 2567065 := bstep (se 2 (by rfl) ⟨962649, by rfl⟩ : syracuseStep 2567065 = 1925299) B1925299
theorem B12331939 : Blo 842353 12331939 := bstep (se 1 (by rfl) ⟨9248954, by rfl⟩ : syracuseStep 12331939 = 18497909) B18497909
theorem B2141113 : Blo 842353 2141113 := bstep (se 2 (by rfl) ⟨802917, by rfl⟩ : syracuseStep 2141113 = 1605835) B1605835
theorem B2567227 : Blo 842353 2567227 := bstep (se 1 (by rfl) ⟨1925420, by rfl⟩ : syracuseStep 2567227 = 3850841) B3850841
theorem B2403719 : Blo 842353 2403719 := bstep (se 1 (by rfl) ⟨1802789, by rfl⟩ : syracuseStep 2403719 = 3605579) B3605579
theorem B2141711 : Blo 842353 2141711 := bstep (se 1 (by rfl) ⟨1606283, by rfl⟩ : syracuseStep 2141711 = 3212567) B3212567
theorem B2436979 : Blo 842353 2436979 := bstep (se 1 (by rfl) ⟨1827734, by rfl⟩ : syracuseStep 2436979 = 3655469) B3655469
theorem B1519561 : Blo 842353 1519561 := bstep (se 2 (by rfl) ⟨569835, by rfl⟩ : syracuseStep 1519561 = 1139671) B1139671
theorem B2404505 : Blo 842353 2404505 := bstep (se 2 (by rfl) ⟨901689, by rfl⟩ : syracuseStep 2404505 = 1803379) B1803379
theorem B3256691 : Blo 842353 3256691 := bstep (se 1 (by rfl) ⟨2442518, by rfl⟩ : syracuseStep 3256691 = 4885037) B4885037
theorem B6500755 : Blo 842353 6500755 := bstep (se 1 (by rfl) ⟨4875566, by rfl⟩ : syracuseStep 6500755 = 9751133) B9751133
theorem B2470297 : Blo 842353 2470297 := bstep (se 2 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 2470297 = 1852723) B1852723
theorem B4272587 : Blo 842353 4272587 := bstep (se 1 (by rfl) ⟨3204440, by rfl⟩ : syracuseStep 4272587 = 6408881) B6408881
theorem B6402563 : Blo 842353 6402563 := bstep (se 1 (by rfl) ⟨4801922, by rfl⟩ : syracuseStep 6402563 = 9603845) B9603845
theorem B1421867 : Blo 842353 1421867 := bstep (se 1 (by rfl) ⟨1066400, by rfl⟩ : syracuseStep 1421867 = 2132801) B2132801
theorem B9122381 : Blo 842353 9122381 := bstep (se 3 (by rfl) ⟨1710446, by rfl⟩ : syracuseStep 9122381 = 3420893) B3420893
theorem B4272911 : Blo 842353 4272911 := bstep (se 1 (by rfl) ⟨3204683, by rfl⟩ : syracuseStep 4272911 = 6409367) B6409367
theorem B2405153 : Blo 842353 2405153 := bstep (se 2 (by rfl) ⟨901932, by rfl⟩ : syracuseStep 2405153 = 1803865) B1803865
theorem B1422265 : Blo 842353 1422265 := bstep (se 2 (by rfl) ⟨533349, by rfl⟩ : syracuseStep 1422265 = 1066699) B1066699
theorem B5419979 : Blo 842353 5419979 := bstep (se 1 (by rfl) ⟨4064984, by rfl⟩ : syracuseStep 5419979 = 8129969) B8129969
theorem B4634003 : Blo 842353 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B10270273 : Blo 842353 10270273 := bstep (se 2 (by rfl) ⟨3851352, by rfl⟩ : syracuseStep 10270273 = 7702705) B7702705
theorem B14595661 : Blo 842353 14595661 := bstep (se 3 (by rfl) ⟨2736686, by rfl⟩ : syracuseStep 14595661 = 5473373) B5473373
theorem B2569843 : Blo 842353 2569843 := bstep (se 1 (by rfl) ⟨1927382, by rfl⟩ : syracuseStep 2569843 = 3854765) B3854765
theorem B1422967 : Blo 842353 1422967 := bstep (se 1 (by rfl) ⟨1067225, by rfl⟩ : syracuseStep 1422967 = 2134451) B2134451
theorem B2406145 : Blo 842353 2406145 := bstep (se 2 (by rfl) ⟨902304, by rfl⟩ : syracuseStep 2406145 = 1804609) B1804609
theorem B1423163 : Blo 842353 1423163 := bstep (se 1 (by rfl) ⟨1067372, by rfl⟩ : syracuseStep 1423163 = 2134745) B2134745
theorem B4569149 : Blo 842353 4569149 := bstep (se 3 (by rfl) ⟨856715, by rfl⟩ : syracuseStep 4569149 = 1713431) B1713431
theorem B2570393 : Blo 842353 2570393 := bstep (se 2 (by rfl) ⟨963897, by rfl⟩ : syracuseStep 2570393 = 1927795) B1927795
theorem B4274369 : Blo 842353 4274369 := bstep (se 2 (by rfl) ⟨1602888, by rfl⟩ : syracuseStep 4274369 = 3205777) B3205777
theorem B1423561 : Blo 842353 1423561 := bstep (se 2 (by rfl) ⟨533835, by rfl⟩ : syracuseStep 1423561 = 1067671) B1067671
theorem B2701583 : Blo 842353 2701583 := bstep (se 1 (by rfl) ⟨2026187, by rfl⟩ : syracuseStep 2701583 = 4052375) B4052375
theorem B7420295 : Blo 842353 7420295 := bstep (se 1 (by rfl) ⟨5565221, by rfl⟩ : syracuseStep 7420295 = 11130443) B11130443
theorem B10992473 : Blo 842353 10992473 := bstep (se 2 (by rfl) ⟨4122177, by rfl⟩ : syracuseStep 10992473 = 8244355) B8244355
theorem B1424263 : Blo 842353 1424263 := bstep (se 1 (by rfl) ⟨1068197, by rfl⟩ : syracuseStep 1424263 = 2136395) B2136395
theorem B4799897 : Blo 842353 4799897 := bstep (se 2 (by rfl) ⟨1799961, by rfl⟩ : syracuseStep 4799897 = 3599923) B3599923
theorem B4275665 : Blo 842353 4275665 := bstep (se 2 (by rfl) ⟨1603374, by rfl⟩ : syracuseStep 4275665 = 3206749) B3206749
theorem B1424911 : Blo 842353 1424911 := bstep (se 1 (by rfl) ⟨1068683, by rfl⟩ : syracuseStep 1424911 = 2137367) B2137367
theorem B3423863 : Blo 842353 3423863 := bstep (se 1 (by rfl) ⟨2567897, by rfl⟩ : syracuseStep 3423863 = 5135795) B5135795
theorem B2309917 : Blo 842353 2309917 := bstep (se 3 (by rfl) ⟨433109, by rfl⟩ : syracuseStep 2309917 = 866219) B866219
theorem B14434199 : Blo 842353 14434199 := bstep (se 1 (by rfl) ⟨10825649, by rfl⟩ : syracuseStep 14434199 = 21651299) B21651299
theorem B2572289 : Blo 842353 2572289 := bstep (se 2 (by rfl) ⟨964608, by rfl⟩ : syracuseStep 2572289 = 1929217) B1929217
theorem B1425451 : Blo 842353 1425451 := bstep (se 1 (by rfl) ⟨1069088, by rfl⟩ : syracuseStep 1425451 = 2138177) B2138177
theorem B1425593 : Blo 842353 1425593 := bstep (se 2 (by rfl) ⟨534597, by rfl⟩ : syracuseStep 1425593 = 1069195) B1069195
theorem B2409095 : Blo 842353 2409095 := bstep (se 1 (by rfl) ⟨1806821, by rfl⟩ : syracuseStep 2409095 = 3613643) B3613643
theorem B2409277 : Blo 842353 2409277 := bstep (se 3 (by rfl) ⟨451739, by rfl⟩ : syracuseStep 2409277 = 903479) B903479
theorem B1426295 : Blo 842353 1426295 := bstep (se 1 (by rfl) ⟨1069721, by rfl⟩ : syracuseStep 1426295 = 2139443) B2139443
theorem B2409335 : Blo 842353 2409335 := bstep (se 1 (by rfl) ⟨1807001, by rfl⟩ : syracuseStep 2409335 = 3614003) B3614003
theorem B6079511 : Blo 842353 6079511 := bstep (se 1 (by rfl) ⟨4559633, by rfl⟩ : syracuseStep 6079511 = 9119267) B9119267
theorem B2278433 : Blo 842353 2278433 := bstep (se 2 (by rfl) ⟨854412, by rfl⟩ : syracuseStep 2278433 = 1708825) B1708825
theorem B11256893 : Blo 842353 11256893 := bstep (se 3 (by rfl) ⟨2110667, by rfl⟩ : syracuseStep 11256893 = 4221335) B4221335
theorem B1426747 : Blo 842353 1426747 := bstep (se 1 (by rfl) ⟨1070060, by rfl⟩ : syracuseStep 1426747 = 2140121) B2140121
theorem B1066375 : Blo 842353 1066375 := bstep (se 1 (by rfl) ⟨799781, by rfl⟩ : syracuseStep 1066375 = 1599563) B1599563
theorem B2311625 : Blo 842353 2311625 := bstep (se 2 (by rfl) ⟨866859, by rfl⟩ : syracuseStep 2311625 = 1733719) B1733719
theorem B1426889 : Blo 842353 1426889 := bstep (se 2 (by rfl) ⟨535083, by rfl⟩ : syracuseStep 1426889 = 1070167) B1070167
theorem B4277771 : Blo 842353 4277771 := bstep (se 1 (by rfl) ⟨3208328, by rfl⟩ : syracuseStep 4277771 = 6416657) B6416657
theorem B4048471 : Blo 842353 4048471 := bstep (se 1 (by rfl) ⟨3036353, by rfl⟩ : syracuseStep 4048471 = 6072707) B6072707
theorem B4277933 : Blo 842353 4277933 := bstep (se 3 (by rfl) ⟨802112, by rfl⟩ : syracuseStep 4277933 = 1604225) B1604225
theorem B54904499 : Blo 842353 54904499 := bstep (se 1 (by rfl) ⟨41178374, by rfl⟩ : syracuseStep 54904499 = 82356749) B82356749
theorem B6407909 : Blo 842353 6407909 := bstep (se 4 (by rfl) ⟨600741, by rfl⟩ : syracuseStep 6407909 = 1201483) B1201483
theorem B1066871 : Blo 842353 1066871 := bstep (se 1 (by rfl) ⟨800153, by rfl⟩ : syracuseStep 1066871 = 1600307) B1600307
theorem B1263545 : Blo 842353 1263545 := bstep (se 2 (by rfl) ⟨473829, by rfl⟩ : syracuseStep 1263545 = 947659) B947659
theorem B1263623 : Blo 842353 1263623 := bstep (se 1 (by rfl) ⟨947717, by rfl⟩ : syracuseStep 1263623 = 1895435) B1895435
theorem B1067023 : Blo 842353 1067023 := bstep (se 1 (by rfl) ⟨800267, by rfl⟩ : syracuseStep 1067023 = 1600535) B1600535
theorem B1263659 : Blo 842353 1263659 := bstep (se 1 (by rfl) ⟨947744, by rfl⟩ : syracuseStep 1263659 = 1895489) B1895489
theorem B1263689 : Blo 842353 1263689 := bstep (se 2 (by rfl) ⟨473883, by rfl⟩ : syracuseStep 1263689 = 947767) B947767
theorem B1427591 : Blo 842353 1427591 := bstep (se 1 (by rfl) ⟨1070693, by rfl⟩ : syracuseStep 1427591 = 2141387) B2141387
theorem B1263803 : Blo 842353 1263803 := bstep (se 1 (by rfl) ⟨947852, by rfl⟩ : syracuseStep 1263803 = 1895705) B1895705
theorem B1067195 : Blo 842353 1067195 := bstep (se 1 (by rfl) ⟨800396, by rfl⟩ : syracuseStep 1067195 = 1600793) B1600793
theorem B1263863 : Blo 842353 1263863 := bstep (se 1 (by rfl) ⟨947897, by rfl⟩ : syracuseStep 1263863 = 1895795) B1895795
theorem B1263887 : Blo 842353 1263887 := bstep (se 1 (by rfl) ⟨947915, by rfl⟩ : syracuseStep 1263887 = 1895831) B1895831
theorem B1263929 : Blo 842353 1263929 := bstep (se 2 (by rfl) ⟨473973, by rfl⟩ : syracuseStep 1263929 = 947947) B947947
theorem B17353025 : Blo 842353 17353025 := bstep (se 2 (by rfl) ⟨6507384, by rfl⟩ : syracuseStep 17353025 = 13014769) B13014769
theorem B1264007 : Blo 842353 1264007 := bstep (se 1 (by rfl) ⟨948005, by rfl⟩ : syracuseStep 1264007 = 1896011) B1896011
theorem B1264043 : Blo 842353 1264043 := bstep (se 1 (by rfl) ⟨948032, by rfl⟩ : syracuseStep 1264043 = 1896065) B1896065
theorem B1264073 : Blo 842353 1264073 := bstep (se 2 (by rfl) ⟨474027, by rfl⟩ : syracuseStep 1264073 = 948055) B948055
theorem B8669645 : Blo 842353 8669645 := bstep (se 3 (by rfl) ⟨1625558, by rfl⟩ : syracuseStep 8669645 = 3251117) B3251117
theorem B1264187 : Blo 842353 1264187 := bstep (se 1 (by rfl) ⟨948140, by rfl⟩ : syracuseStep 1264187 = 1896281) B1896281
theorem B1264247 : Blo 842353 1264247 := bstep (se 1 (by rfl) ⟨948185, by rfl⟩ : syracuseStep 1264247 = 1896371) B1896371
theorem B1264271 : Blo 842353 1264271 := bstep (se 1 (by rfl) ⟨948203, by rfl⟩ : syracuseStep 1264271 = 1896407) B1896407
theorem B4803245 : Blo 842353 4803245 := bstep (se 3 (by rfl) ⟨900608, by rfl⟩ : syracuseStep 4803245 = 1801217) B1801217
theorem B1264313 : Blo 842353 1264313 := bstep (se 2 (by rfl) ⟨474117, by rfl⟩ : syracuseStep 1264313 = 948235) B948235
theorem B1264391 : Blo 842353 1264391 := bstep (se 1 (by rfl) ⟨948293, by rfl⟩ : syracuseStep 1264391 = 1896587) B1896587
theorem B1264427 : Blo 842353 1264427 := bstep (se 1 (by rfl) ⟨948320, by rfl⟩ : syracuseStep 1264427 = 1896641) B1896641
theorem B2280251 : Blo 842353 2280251 := bstep (se 1 (by rfl) ⟨1710188, by rfl⟩ : syracuseStep 2280251 = 3420377) B3420377
theorem B1264457 : Blo 842353 1264457 := bstep (se 2 (by rfl) ⟨474171, by rfl⟩ : syracuseStep 1264457 = 948343) B948343
theorem B2706311 : Blo 842353 2706311 := bstep (se 1 (by rfl) ⟨2029733, by rfl⟩ : syracuseStep 2706311 = 4059467) B4059467
theorem B1264571 : Blo 842353 1264571 := bstep (se 1 (by rfl) ⟨948428, by rfl⟩ : syracuseStep 1264571 = 1896857) B1896857
theorem B1264631 : Blo 842353 1264631 := bstep (se 1 (by rfl) ⟨948473, by rfl⟩ : syracuseStep 1264631 = 1896947) B1896947
theorem B1264655 : Blo 842353 1264655 := bstep (se 1 (by rfl) ⟨948491, by rfl⟩ : syracuseStep 1264655 = 1896983) B1896983
theorem B1264697 : Blo 842353 1264697 := bstep (se 2 (by rfl) ⟨474261, by rfl⟩ : syracuseStep 1264697 = 948523) B948523
theorem B1264775 : Blo 842353 1264775 := bstep (se 1 (by rfl) ⟨948581, by rfl⟩ : syracuseStep 1264775 = 1897163) B1897163
theorem B1068167 : Blo 842353 1068167 := bstep (se 1 (by rfl) ⟨801125, by rfl⟩ : syracuseStep 1068167 = 1602251) B1602251
theorem B1264811 : Blo 842353 1264811 := bstep (se 1 (by rfl) ⟨948608, by rfl⟩ : syracuseStep 1264811 = 1897217) B1897217
theorem B1264841 : Blo 842353 1264841 := bstep (se 2 (by rfl) ⟨474315, by rfl⟩ : syracuseStep 1264841 = 948631) B948631
theorem B4279553 : Blo 842353 4279553 := bstep (se 2 (by rfl) ⟨1604832, by rfl⟩ : syracuseStep 4279553 = 3209665) B3209665
theorem B1264955 : Blo 842353 1264955 := bstep (se 1 (by rfl) ⟨948716, by rfl⟩ : syracuseStep 1264955 = 1897433) B1897433
theorem B2346355 : Blo 842353 2346355 := bstep (se 1 (by rfl) ⟨1759766, by rfl⟩ : syracuseStep 2346355 = 3519533) B3519533
theorem B1265015 : Blo 842353 1265015 := bstep (se 1 (by rfl) ⟨948761, by rfl⟩ : syracuseStep 1265015 = 1897523) B1897523
theorem B1265039 : Blo 842353 1265039 := bstep (se 1 (by rfl) ⟨948779, by rfl⟩ : syracuseStep 1265039 = 1897559) B1897559
theorem B1265081 : Blo 842353 1265081 := bstep (se 2 (by rfl) ⟨474405, by rfl⟩ : syracuseStep 1265081 = 948811) B948811
theorem B1265159 : Blo 842353 1265159 := bstep (se 1 (by rfl) ⟨948869, by rfl⟩ : syracuseStep 1265159 = 1897739) B1897739
theorem B1265195 : Blo 842353 1265195 := bstep (se 1 (by rfl) ⟨948896, by rfl⟩ : syracuseStep 1265195 = 1897793) B1897793
theorem B1265225 : Blo 842353 1265225 := bstep (se 2 (by rfl) ⟨474459, by rfl⟩ : syracuseStep 1265225 = 948919) B948919
theorem B4574839 : Blo 842353 4574839 := bstep (se 1 (by rfl) ⟨3431129, by rfl⟩ : syracuseStep 4574839 = 6862259) B6862259
theorem B1265339 : Blo 842353 1265339 := bstep (se 1 (by rfl) ⟨949004, by rfl⟩ : syracuseStep 1265339 = 1898009) B1898009
theorem B1265399 : Blo 842353 1265399 := bstep (se 1 (by rfl) ⟨949049, by rfl⟩ : syracuseStep 1265399 = 1898099) B1898099
theorem B1265423 : Blo 842353 1265423 := bstep (se 1 (by rfl) ⟨949067, by rfl⟩ : syracuseStep 1265423 = 1898135) B1898135
theorem B1068815 : Blo 842353 1068815 := bstep (se 1 (by rfl) ⟨801611, by rfl⟩ : syracuseStep 1068815 = 1603223) B1603223
theorem B1199929 : Blo 842353 1199929 := bstep (se 2 (by rfl) ⟨449973, by rfl⟩ : syracuseStep 1199929 = 899947) B899947
theorem B1265465 : Blo 842353 1265465 := bstep (se 2 (by rfl) ⟨474549, by rfl⟩ : syracuseStep 1265465 = 949099) B949099
theorem B1265543 : Blo 842353 1265543 := bstep (se 1 (by rfl) ⟨949157, by rfl⟩ : syracuseStep 1265543 = 1898315) B1898315
theorem B1265579 : Blo 842353 1265579 := bstep (se 1 (by rfl) ⟨949184, by rfl⟩ : syracuseStep 1265579 = 1898369) B1898369
theorem B1265609 : Blo 842353 1265609 := bstep (se 2 (by rfl) ⟨474603, by rfl⟩ : syracuseStep 1265609 = 949207) B949207
theorem B4280363 : Blo 842353 4280363 := bstep (se 1 (by rfl) ⟨3210272, by rfl⟩ : syracuseStep 4280363 = 6420545) B6420545
theorem B1265723 : Blo 842353 1265723 := bstep (se 1 (by rfl) ⟨949292, by rfl⟩ : syracuseStep 1265723 = 1898585) B1898585
theorem B1265783 : Blo 842353 1265783 := bstep (se 1 (by rfl) ⟨949337, by rfl⟩ : syracuseStep 1265783 = 1898675) B1898675
theorem B1265807 : Blo 842353 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B14438573 : Blo 842353 14438573 := bstep (se 3 (by rfl) ⟨2707232, by rfl⟩ : syracuseStep 14438573 = 5414465) B5414465
theorem B1265849 : Blo 842353 1265849 := bstep (se 2 (by rfl) ⟨474693, by rfl⟩ : syracuseStep 1265849 = 949387) B949387
theorem B1265927 : Blo 842353 1265927 := bstep (se 1 (by rfl) ⟨949445, by rfl⟩ : syracuseStep 1265927 = 1898891) B1898891
theorem B3199247 : Blo 842353 3199247 := bstep (se 1 (by rfl) ⟨2399435, by rfl⟩ : syracuseStep 3199247 = 4798871) B4798871
theorem B1265963 : Blo 842353 1265963 := bstep (se 1 (by rfl) ⟨949472, by rfl⟩ : syracuseStep 1265963 = 1898945) B1898945
theorem B1265993 : Blo 842353 1265993 := bstep (se 2 (by rfl) ⟨474747, by rfl⟩ : syracuseStep 1265993 = 949495) B949495
theorem B1266107 : Blo 842353 1266107 := bstep (se 1 (by rfl) ⟨949580, by rfl⟩ : syracuseStep 1266107 = 1899161) B1899161
theorem B1266167 : Blo 842353 1266167 := bstep (se 1 (by rfl) ⟨949625, by rfl⟩ : syracuseStep 1266167 = 1899251) B1899251
theorem B1266191 : Blo 842353 1266191 := bstep (se 1 (by rfl) ⟨949643, by rfl⟩ : syracuseStep 1266191 = 1899287) B1899287
theorem B1266233 : Blo 842353 1266233 := bstep (se 2 (by rfl) ⟨474837, by rfl⟩ : syracuseStep 1266233 = 949675) B949675
theorem B1266311 : Blo 842353 1266311 := bstep (se 1 (by rfl) ⟨949733, by rfl⟩ : syracuseStep 1266311 = 1899467) B1899467
theorem B1266347 : Blo 842353 1266347 := bstep (se 1 (by rfl) ⟨949760, by rfl⟩ : syracuseStep 1266347 = 1899521) B1899521
theorem B1266377 : Blo 842353 1266377 := bstep (se 2 (by rfl) ⟨474891, by rfl⟩ : syracuseStep 1266377 = 949783) B949783
theorem B1266491 : Blo 842353 1266491 := bstep (se 1 (by rfl) ⟨949868, by rfl⟩ : syracuseStep 1266491 = 1899737) B1899737
theorem B1266551 : Blo 842353 1266551 := bstep (se 1 (by rfl) ⟨949913, by rfl⟩ : syracuseStep 1266551 = 1899827) B1899827
theorem B1266575 : Blo 842353 1266575 := bstep (se 1 (by rfl) ⟨949931, by rfl⟩ : syracuseStep 1266575 = 1899863) B1899863
theorem B1266617 : Blo 842353 1266617 := bstep (se 2 (by rfl) ⟨474981, by rfl⟩ : syracuseStep 1266617 = 949963) B949963
theorem B1201159 : Blo 842353 1201159 := bstep (se 1 (by rfl) ⟨900869, by rfl⟩ : syracuseStep 1201159 = 1801739) B1801739
theorem B1266695 : Blo 842353 1266695 := bstep (se 1 (by rfl) ⟨950021, by rfl⟩ : syracuseStep 1266695 = 1900043) B1900043
theorem B1266731 : Blo 842353 1266731 := bstep (se 1 (by rfl) ⟨950048, by rfl⟩ : syracuseStep 1266731 = 1900097) B1900097
theorem B1266761 : Blo 842353 1266761 := bstep (se 2 (by rfl) ⟨475035, by rfl⟩ : syracuseStep 1266761 = 950071) B950071
theorem B29217925 : Blo 842353 29217925 := bstep (se 4 (by rfl) ⟨2739180, by rfl⟩ : syracuseStep 29217925 = 5478361) B5478361
theorem B1266875 : Blo 842353 1266875 := bstep (se 1 (by rfl) ⟨950156, by rfl⟩ : syracuseStep 1266875 = 1900313) B1900313
theorem B1266935 : Blo 842353 1266935 := bstep (se 1 (by rfl) ⟨950201, by rfl⟩ : syracuseStep 1266935 = 1900403) B1900403
theorem B1266959 : Blo 842353 1266959 := bstep (se 1 (by rfl) ⟨950219, by rfl⟩ : syracuseStep 1266959 = 1900439) B1900439
theorem B1267001 : Blo 842353 1267001 := bstep (se 2 (by rfl) ⟨475125, by rfl⟩ : syracuseStep 1267001 = 950251) B950251
theorem B4281659 : Blo 842353 4281659 := bstep (se 1 (by rfl) ⟨3211244, by rfl⟩ : syracuseStep 4281659 = 6422489) B6422489
theorem B12146051 : Blo 842353 12146051 := bstep (se 1 (by rfl) ⟨9109538, by rfl⟩ : syracuseStep 12146051 = 18219077) B18219077
theorem B1267079 : Blo 842353 1267079 := bstep (se 1 (by rfl) ⟨950309, by rfl⟩ : syracuseStep 1267079 = 1900619) B1900619
theorem B1267115 : Blo 842353 1267115 := bstep (se 1 (by rfl) ⟨950336, by rfl⟩ : syracuseStep 1267115 = 1900673) B1900673
theorem B1267145 : Blo 842353 1267145 := bstep (se 2 (by rfl) ⟨475179, by rfl⟩ : syracuseStep 1267145 = 950359) B950359
theorem B4281821 : Blo 842353 4281821 := bstep (se 3 (by rfl) ⟨802841, by rfl⟩ : syracuseStep 4281821 = 1605683) B1605683
theorem B2283041 : Blo 842353 2283041 := bstep (se 2 (by rfl) ⟨856140, by rfl⟩ : syracuseStep 2283041 = 1712281) B1712281
theorem B1267259 : Blo 842353 1267259 := bstep (se 1 (by rfl) ⟨950444, by rfl⟩ : syracuseStep 1267259 = 1900889) B1900889
theorem B1267319 : Blo 842353 1267319 := bstep (se 1 (by rfl) ⟨950489, by rfl⟩ : syracuseStep 1267319 = 1900979) B1900979
theorem B1267343 : Blo 842353 1267343 := bstep (se 1 (by rfl) ⟨950507, by rfl⟩ : syracuseStep 1267343 = 1901015) B1901015
theorem B1267385 : Blo 842353 1267385 := bstep (se 2 (by rfl) ⟨475269, by rfl⟩ : syracuseStep 1267385 = 950539) B950539
theorem B9885401 : Blo 842353 9885401 := bstep (se 2 (by rfl) ⟨3707025, by rfl⟩ : syracuseStep 9885401 = 7414051) B7414051
theorem B1267463 : Blo 842353 1267463 := bstep (se 1 (by rfl) ⟨950597, by rfl⟩ : syracuseStep 1267463 = 1901195) B1901195
theorem B4282145 : Blo 842353 4282145 := bstep (se 2 (by rfl) ⟨1605804, by rfl⟩ : syracuseStep 4282145 = 3211609) B3211609
theorem B1267499 : Blo 842353 1267499 := bstep (se 1 (by rfl) ⟨950624, by rfl⟩ : syracuseStep 1267499 = 1901249) B1901249
theorem B1201979 : Blo 842353 1201979 := bstep (se 1 (by rfl) ⟨901484, by rfl⟩ : syracuseStep 1201979 = 1802969) B1802969
theorem B1267529 : Blo 842353 1267529 := bstep (se 2 (by rfl) ⟨475323, by rfl⟩ : syracuseStep 1267529 = 950647) B950647
theorem B3200903 : Blo 842353 3200903 := bstep (se 1 (by rfl) ⟨2400677, by rfl⟩ : syracuseStep 3200903 = 4801355) B4801355
theorem B1267643 : Blo 842353 1267643 := bstep (se 1 (by rfl) ⟨950732, by rfl⟩ : syracuseStep 1267643 = 1901465) B1901465
theorem B1267703 : Blo 842353 1267703 := bstep (se 1 (by rfl) ⟨950777, by rfl⟩ : syracuseStep 1267703 = 1901555) B1901555
theorem B1267727 : Blo 842353 1267727 := bstep (se 1 (by rfl) ⟨950795, by rfl⟩ : syracuseStep 1267727 = 1901591) B1901591
theorem B1267769 : Blo 842353 1267769 := bstep (se 2 (by rfl) ⟨475413, by rfl⟩ : syracuseStep 1267769 = 950827) B950827
theorem B1267847 : Blo 842353 1267847 := bstep (se 1 (by rfl) ⟨950885, by rfl⟩ : syracuseStep 1267847 = 1901771) B1901771
theorem B1267883 : Blo 842353 1267883 := bstep (se 1 (by rfl) ⟨950912, by rfl⟩ : syracuseStep 1267883 = 1901825) B1901825
theorem B1267913 : Blo 842353 1267913 := bstep (se 2 (by rfl) ⟨475467, by rfl⟩ : syracuseStep 1267913 = 950935) B950935
theorem B1268027 : Blo 842353 1268027 := bstep (se 1 (by rfl) ⟨951020, by rfl⟩ : syracuseStep 1268027 = 1902041) B1902041
theorem B1268087 : Blo 842353 1268087 := bstep (se 1 (by rfl) ⟨951065, by rfl⟩ : syracuseStep 1268087 = 1902131) B1902131
theorem B1268111 : Blo 842353 1268111 := bstep (se 1 (by rfl) ⟨951083, by rfl⟩ : syracuseStep 1268111 = 1902167) B1902167
theorem B6936977 : Blo 842353 6936977 := bstep (se 2 (by rfl) ⟨2601366, by rfl⟩ : syracuseStep 6936977 = 5202733) B5202733
theorem B8116625 : Blo 842353 8116625 := bstep (se 2 (by rfl) ⟨3043734, by rfl⟩ : syracuseStep 8116625 = 6087469) B6087469
theorem B4872595 : Blo 842353 4872595 := bstep (se 1 (by rfl) ⟨3654446, by rfl⟩ : syracuseStep 4872595 = 7308893) B7308893
theorem B16243091 : Blo 842353 16243091 := bstep (se 1 (by rfl) ⟨12182318, by rfl⟩ : syracuseStep 16243091 = 24364637) B24364637
theorem B1202617 : Blo 842353 1202617 := bstep (se 2 (by rfl) ⟨450981, by rfl⟩ : syracuseStep 1202617 = 901963) B901963
theorem B1268153 : Blo 842353 1268153 := bstep (se 2 (by rfl) ⟨475557, by rfl⟩ : syracuseStep 1268153 = 951115) B951115
theorem B1268231 : Blo 842353 1268231 := bstep (se 1 (by rfl) ⟨951173, by rfl⟩ : syracuseStep 1268231 = 1902347) B1902347
theorem B2710027 : Blo 842353 2710027 := bstep (se 1 (by rfl) ⟨2032520, by rfl⟩ : syracuseStep 2710027 = 4065041) B4065041
theorem B13687339 : Blo 842353 13687339 := bstep (se 1 (by rfl) ⟨10265504, by rfl⟩ : syracuseStep 13687339 = 20531009) B20531009
theorem B1268267 : Blo 842353 1268267 := bstep (se 1 (by rfl) ⟨951200, by rfl⟩ : syracuseStep 1268267 = 1902401) B1902401
theorem B1268297 : Blo 842353 1268297 := bstep (se 2 (by rfl) ⟨475611, by rfl⟩ : syracuseStep 1268297 = 951223) B951223
theorem B2710103 : Blo 842353 2710103 := bstep (se 1 (by rfl) ⟨2032577, by rfl⟩ : syracuseStep 2710103 = 4065155) B4065155
theorem B842375 : Blo 842353 842375 := bstep (se 1 (by rfl) ⟨631781, by rfl⟩ : syracuseStep 842375 = 1263563) B1263563
theorem B842383 : Blo 842353 842383 := bstep (se 1 (by rfl) ⟨631787, by rfl⟩ : syracuseStep 842383 = 1263575) B1263575
theorem B842427 : Blo 842353 842427 := bstep (se 1 (by rfl) ⟨631820, by rfl⟩ : syracuseStep 842427 = 1263641) B1263641
theorem B1268411 : Blo 842353 1268411 := bstep (se 1 (by rfl) ⟨951308, by rfl⟩ : syracuseStep 1268411 = 1902617) B1902617
theorem B9624257 : Blo 842353 9624257 := bstep (se 2 (by rfl) ⟨3609096, by rfl⟩ : syracuseStep 9624257 = 7218193) B7218193
theorem B4283117 : Blo 842353 4283117 := bstep (se 3 (by rfl) ⟨803084, by rfl⟩ : syracuseStep 4283117 = 1606169) B1606169
theorem B1268471 : Blo 842353 1268471 := bstep (se 1 (by rfl) ⟨951353, by rfl⟩ : syracuseStep 1268471 = 1902707) B1902707
theorem B842503 : Blo 842353 842503 := bstep (se 1 (by rfl) ⟨631877, by rfl⟩ : syracuseStep 842503 = 1263755) B1263755
theorem B842511 : Blo 842353 842511 := bstep (se 1 (by rfl) ⟨631883, by rfl⟩ : syracuseStep 842511 = 1263767) B1263767
theorem B1268495 : Blo 842353 1268495 := bstep (se 1 (by rfl) ⟨951371, by rfl⟩ : syracuseStep 1268495 = 1902743) B1902743
theorem B1268537 : Blo 842353 1268537 := bstep (se 2 (by rfl) ⟨475701, by rfl⟩ : syracuseStep 1268537 = 951403) B951403
theorem B842555 : Blo 842353 842555 := bstep (se 1 (by rfl) ⟨631916, by rfl⟩ : syracuseStep 842555 = 1263833) B1263833
theorem B842631 : Blo 842353 842631 := bstep (se 1 (by rfl) ⟨631973, by rfl⟩ : syracuseStep 842631 = 1263947) B1263947
theorem B1268615 : Blo 842353 1268615 := bstep (se 1 (by rfl) ⟨951461, by rfl⟩ : syracuseStep 1268615 = 1902923) B1902923
theorem B842639 : Blo 842353 842639 := bstep (se 1 (by rfl) ⟨631979, by rfl⟩ : syracuseStep 842639 = 1263959) B1263959
theorem B1268651 : Blo 842353 1268651 := bstep (se 1 (by rfl) ⟨951488, by rfl⟩ : syracuseStep 1268651 = 1902977) B1902977
theorem B842683 : Blo 842353 842683 := bstep (se 1 (by rfl) ⟨632012, by rfl⟩ : syracuseStep 842683 = 1264025) B1264025
theorem B1268681 : Blo 842353 1268681 := bstep (se 2 (by rfl) ⟨475755, by rfl⟩ : syracuseStep 1268681 = 951511) B951511
theorem B842759 : Blo 842353 842759 := bstep (se 1 (by rfl) ⟨632069, by rfl⟩ : syracuseStep 842759 = 1264139) B1264139
theorem B842767 : Blo 842353 842767 := bstep (se 1 (by rfl) ⟨632075, by rfl⟩ : syracuseStep 842767 = 1264151) B1264151
theorem B842811 : Blo 842353 842811 := bstep (se 1 (by rfl) ⟨632108, by rfl⟩ : syracuseStep 842811 = 1264217) B1264217
theorem B1268795 : Blo 842353 1268795 := bstep (se 1 (by rfl) ⟨951596, by rfl⟩ : syracuseStep 1268795 = 1903193) B1903193
theorem B1268855 : Blo 842353 1268855 := bstep (se 1 (by rfl) ⟨951641, by rfl⟩ : syracuseStep 1268855 = 1903283) B1903283
theorem B842887 : Blo 842353 842887 := bstep (se 1 (by rfl) ⟨632165, by rfl⟩ : syracuseStep 842887 = 1264331) B1264331
theorem B842895 : Blo 842353 842895 := bstep (se 1 (by rfl) ⟨632171, by rfl⟩ : syracuseStep 842895 = 1264343) B1264343
theorem B1268879 : Blo 842353 1268879 := bstep (se 1 (by rfl) ⟨951659, by rfl⟩ : syracuseStep 1268879 = 1903319) B1903319
theorem B1268921 : Blo 842353 1268921 := bstep (se 2 (by rfl) ⟨475845, by rfl⟩ : syracuseStep 1268921 = 951691) B951691
theorem B842939 : Blo 842353 842939 := bstep (se 1 (by rfl) ⟨632204, by rfl⟩ : syracuseStep 842939 = 1264409) B1264409
theorem B4807937 : Blo 842353 4807937 := bstep (se 2 (by rfl) ⟨1802976, by rfl⟩ : syracuseStep 4807937 = 3605953) B3605953
theorem B843015 : Blo 842353 843015 := bstep (se 1 (by rfl) ⟨632261, by rfl⟩ : syracuseStep 843015 = 1264523) B1264523
theorem B1268999 : Blo 842353 1268999 := bstep (se 1 (by rfl) ⟨951749, by rfl⟩ : syracuseStep 1268999 = 1903499) B1903499
theorem B843023 : Blo 842353 843023 := bstep (se 1 (by rfl) ⟨632267, by rfl⟩ : syracuseStep 843023 = 1264535) B1264535
theorem B1269035 : Blo 842353 1269035 := bstep (se 1 (by rfl) ⟨951776, by rfl⟩ : syracuseStep 1269035 = 1903553) B1903553
theorem B843067 : Blo 842353 843067 := bstep (se 1 (by rfl) ⟨632300, by rfl⟩ : syracuseStep 843067 = 1264601) B1264601
theorem B1269065 : Blo 842353 1269065 := bstep (se 2 (by rfl) ⟨475899, by rfl⟩ : syracuseStep 1269065 = 951799) B951799
theorem B843143 : Blo 842353 843143 := bstep (se 1 (by rfl) ⟨632357, by rfl⟩ : syracuseStep 843143 = 1264715) B1264715
theorem B843151 : Blo 842353 843151 := bstep (se 1 (by rfl) ⟨632363, by rfl⟩ : syracuseStep 843151 = 1264727) B1264727
theorem B5561747 : Blo 842353 5561747 := bstep (se 1 (by rfl) ⟨4171310, by rfl⟩ : syracuseStep 5561747 = 8342621) B8342621
theorem B843195 : Blo 842353 843195 := bstep (se 1 (by rfl) ⟨632396, by rfl⟩ : syracuseStep 843195 = 1264793) B1264793
theorem B1269179 : Blo 842353 1269179 := bstep (se 1 (by rfl) ⟨951884, by rfl⟩ : syracuseStep 1269179 = 1903769) B1903769
theorem B1269239 : Blo 842353 1269239 := bstep (se 1 (by rfl) ⟨951929, by rfl⟩ : syracuseStep 1269239 = 1903859) B1903859
theorem B843271 : Blo 842353 843271 := bstep (se 1 (by rfl) ⟨632453, by rfl⟩ : syracuseStep 843271 = 1264907) B1264907
theorem B843279 : Blo 842353 843279 := bstep (se 1 (by rfl) ⟨632459, by rfl⟩ : syracuseStep 843279 = 1264919) B1264919
theorem B1269263 : Blo 842353 1269263 := bstep (se 1 (by rfl) ⟨951947, by rfl⟩ : syracuseStep 1269263 = 1903895) B1903895
theorem B4283927 : Blo 842353 4283927 := bstep (se 1 (by rfl) ⟨3212945, by rfl⟩ : syracuseStep 4283927 = 6425891) B6425891
theorem B1269305 : Blo 842353 1269305 := bstep (se 2 (by rfl) ⟨475989, by rfl⟩ : syracuseStep 1269305 = 951979) B951979
theorem B843323 : Blo 842353 843323 := bstep (se 1 (by rfl) ⟨632492, by rfl⟩ : syracuseStep 843323 = 1264985) B1264985
theorem B3202679 : Blo 842353 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B843399 : Blo 842353 843399 := bstep (se 1 (by rfl) ⟨632549, by rfl⟩ : syracuseStep 843399 = 1265099) B1265099
theorem B1269383 : Blo 842353 1269383 := bstep (se 1 (by rfl) ⟨952037, by rfl⟩ : syracuseStep 1269383 = 1904075) B1904075
theorem B843407 : Blo 842353 843407 := bstep (se 1 (by rfl) ⟨632555, by rfl⟩ : syracuseStep 843407 = 1265111) B1265111
theorem B1269419 : Blo 842353 1269419 := bstep (se 1 (by rfl) ⟨952064, by rfl⟩ : syracuseStep 1269419 = 1904129) B1904129
theorem B843451 : Blo 842353 843451 := bstep (se 1 (by rfl) ⟨632588, by rfl⟩ : syracuseStep 843451 = 1265177) B1265177
theorem B4808393 : Blo 842353 4808393 := bstep (se 2 (by rfl) ⟨1803147, by rfl⟩ : syracuseStep 4808393 = 3606295) B3606295
theorem B1269449 : Blo 842353 1269449 := bstep (se 2 (by rfl) ⟨476043, by rfl⟩ : syracuseStep 1269449 = 952087) B952087
theorem B843527 : Blo 842353 843527 := bstep (se 1 (by rfl) ⟨632645, by rfl⟩ : syracuseStep 843527 = 1265291) B1265291
theorem B843535 : Blo 842353 843535 := bstep (se 1 (by rfl) ⟨632651, by rfl⟩ : syracuseStep 843535 = 1265303) B1265303
theorem B4054835 : Blo 842353 4054835 := bstep (se 1 (by rfl) ⟨3041126, by rfl⟩ : syracuseStep 4054835 = 6082253) B6082253
theorem B843579 : Blo 842353 843579 := bstep (se 1 (by rfl) ⟨632684, by rfl⟩ : syracuseStep 843579 = 1265369) B1265369
theorem B843655 : Blo 842353 843655 := bstep (se 1 (by rfl) ⟨632741, by rfl⟩ : syracuseStep 843655 = 1265483) B1265483
theorem B1204103 : Blo 842353 1204103 := bstep (se 1 (by rfl) ⟨903077, by rfl⟩ : syracuseStep 1204103 = 1806155) B1806155
theorem B843663 : Blo 842353 843663 := bstep (se 1 (by rfl) ⟨632747, by rfl⟩ : syracuseStep 843663 = 1265495) B1265495
theorem B4054931 : Blo 842353 4054931 := bstep (se 1 (by rfl) ⟨3041198, by rfl⟩ : syracuseStep 4054931 = 6082397) B6082397
theorem B843707 : Blo 842353 843707 := bstep (se 1 (by rfl) ⟨632780, by rfl⟩ : syracuseStep 843707 = 1265561) B1265561
theorem B843783 : Blo 842353 843783 := bstep (se 1 (by rfl) ⟨632837, by rfl⟩ : syracuseStep 843783 = 1265675) B1265675
theorem B843791 : Blo 842353 843791 := bstep (se 1 (by rfl) ⟨632843, by rfl⟩ : syracuseStep 843791 = 1265687) B1265687
theorem B1302571 : Blo 842353 1302571 := bstep (se 1 (by rfl) ⟨976928, by rfl⟩ : syracuseStep 1302571 = 1953857) B1953857
theorem B843835 : Blo 842353 843835 := bstep (se 1 (by rfl) ⟨632876, by rfl⟩ : syracuseStep 843835 = 1265753) B1265753
theorem B13721717 : Blo 842353 13721717 := bstep (se 5 (by rfl) ⟨643205, by rfl⟩ : syracuseStep 13721717 = 1286411) B1286411
theorem B843911 : Blo 842353 843911 := bstep (se 1 (by rfl) ⟨632933, by rfl⟩ : syracuseStep 843911 = 1265867) B1265867
theorem B843919 : Blo 842353 843919 := bstep (se 1 (by rfl) ⟨632939, by rfl⟩ : syracuseStep 843919 = 1265879) B1265879
theorem B843963 : Blo 842353 843963 := bstep (se 1 (by rfl) ⟨632972, by rfl⟩ : syracuseStep 843963 = 1265945) B1265945
theorem B1204411 : Blo 842353 1204411 := bstep (se 1 (by rfl) ⟨903308, by rfl⟩ : syracuseStep 1204411 = 1806617) B1806617
theorem B1827017 : Blo 842353 1827017 := bstep (se 2 (by rfl) ⟨685131, by rfl⟩ : syracuseStep 1827017 = 1370263) B1370263
theorem B844039 : Blo 842353 844039 := bstep (se 1 (by rfl) ⟨633029, by rfl⟩ : syracuseStep 844039 = 1266059) B1266059
theorem B844047 : Blo 842353 844047 := bstep (se 1 (by rfl) ⟨633035, by rfl⟩ : syracuseStep 844047 = 1266071) B1266071
theorem B844091 : Blo 842353 844091 := bstep (se 1 (by rfl) ⟨633068, by rfl⟩ : syracuseStep 844091 = 1266137) B1266137
theorem B1925495 : Blo 842353 1925495 := bstep (se 1 (by rfl) ⟨1444121, by rfl⟩ : syracuseStep 1925495 = 2888243) B2888243
theorem B844167 : Blo 842353 844167 := bstep (se 1 (by rfl) ⟨633125, by rfl⟩ : syracuseStep 844167 = 1266251) B1266251
theorem B844175 : Blo 842353 844175 := bstep (se 1 (by rfl) ⟨633131, by rfl⟩ : syracuseStep 844175 = 1266263) B1266263
theorem B844219 : Blo 842353 844219 := bstep (se 1 (by rfl) ⟨633164, by rfl⟩ : syracuseStep 844219 = 1266329) B1266329
theorem B844295 : Blo 842353 844295 := bstep (se 1 (by rfl) ⟨633221, by rfl⟩ : syracuseStep 844295 = 1266443) B1266443
theorem B844303 : Blo 842353 844303 := bstep (se 1 (by rfl) ⟨633227, by rfl⟩ : syracuseStep 844303 = 1266455) B1266455
theorem B844347 : Blo 842353 844347 := bstep (se 1 (by rfl) ⟨633260, by rfl⟩ : syracuseStep 844347 = 1266521) B1266521
theorem B3203651 : Blo 842353 3203651 := bstep (se 1 (by rfl) ⟨2402738, by rfl⟩ : syracuseStep 3203651 = 4805477) B4805477
theorem B8774245 : Blo 842353 8774245 := bstep (se 4 (by rfl) ⟨822585, by rfl⟩ : syracuseStep 8774245 = 1645171) B1645171
theorem B844423 : Blo 842353 844423 := bstep (se 1 (by rfl) ⟨633317, by rfl⟩ : syracuseStep 844423 = 1266635) B1266635
theorem B844431 : Blo 842353 844431 := bstep (se 1 (by rfl) ⟨633323, by rfl⟩ : syracuseStep 844431 = 1266647) B1266647
theorem B844475 : Blo 842353 844475 := bstep (se 1 (by rfl) ⟨633356, by rfl⟩ : syracuseStep 844475 = 1266713) B1266713
theorem B844551 : Blo 842353 844551 := bstep (se 1 (by rfl) ⟨633413, by rfl⟩ : syracuseStep 844551 = 1266827) B1266827
theorem B844559 : Blo 842353 844559 := bstep (se 1 (by rfl) ⟨633419, by rfl⟩ : syracuseStep 844559 = 1266839) B1266839
theorem B844603 : Blo 842353 844603 := bstep (se 1 (by rfl) ⟨633452, by rfl⟩ : syracuseStep 844603 = 1266905) B1266905
theorem B844679 : Blo 842353 844679 := bstep (se 1 (by rfl) ⟨633509, by rfl⟩ : syracuseStep 844679 = 1267019) B1267019
theorem B844687 : Blo 842353 844687 := bstep (se 1 (by rfl) ⟨633515, by rfl⟩ : syracuseStep 844687 = 1267031) B1267031
theorem B844731 : Blo 842353 844731 := bstep (se 1 (by rfl) ⟨633548, by rfl⟩ : syracuseStep 844731 = 1267097) B1267097
theorem B844807 : Blo 842353 844807 := bstep (se 1 (by rfl) ⟨633605, by rfl⟩ : syracuseStep 844807 = 1267211) B1267211
theorem B3204107 : Blo 842353 3204107 := bstep (se 1 (by rfl) ⟨2403080, by rfl⟩ : syracuseStep 3204107 = 4806161) B4806161
theorem B844815 : Blo 842353 844815 := bstep (se 1 (by rfl) ⟨633611, by rfl⟩ : syracuseStep 844815 = 1267223) B1267223
theorem B844859 : Blo 842353 844859 := bstep (se 1 (by rfl) ⟨633644, by rfl⟩ : syracuseStep 844859 = 1267289) B1267289
theorem B844935 : Blo 842353 844935 := bstep (se 1 (by rfl) ⟨633701, by rfl⟩ : syracuseStep 844935 = 1267403) B1267403
theorem B844943 : Blo 842353 844943 := bstep (se 1 (by rfl) ⟨633707, by rfl⟩ : syracuseStep 844943 = 1267415) B1267415
theorem B844987 : Blo 842353 844987 := bstep (se 1 (by rfl) ⟨633740, by rfl⟩ : syracuseStep 844987 = 1267481) B1267481
theorem B845063 : Blo 842353 845063 := bstep (se 1 (by rfl) ⟨633797, by rfl⟩ : syracuseStep 845063 = 1267595) B1267595
theorem B845071 : Blo 842353 845071 := bstep (se 1 (by rfl) ⟨633803, by rfl⟩ : syracuseStep 845071 = 1267607) B1267607
theorem B1926443 : Blo 842353 1926443 := bstep (se 1 (by rfl) ⟨1444832, by rfl⟩ : syracuseStep 1926443 = 2889665) B2889665
theorem B2843963 : Blo 842353 2843963 := bstep (se 1 (by rfl) ⟨2132972, by rfl⟩ : syracuseStep 2843963 = 4265945) B4265945
theorem B845115 : Blo 842353 845115 := bstep (se 1 (by rfl) ⟨633836, by rfl⟩ : syracuseStep 845115 = 1267673) B1267673
theorem B845191 : Blo 842353 845191 := bstep (se 1 (by rfl) ⟨633893, by rfl⟩ : syracuseStep 845191 = 1267787) B1267787
theorem B845199 : Blo 842353 845199 := bstep (se 1 (by rfl) ⟨633899, by rfl⟩ : syracuseStep 845199 = 1267799) B1267799
theorem B2024851 : Blo 842353 2024851 := bstep (se 1 (by rfl) ⟨1518638, by rfl⟩ : syracuseStep 2024851 = 3037277) B3037277
theorem B845243 : Blo 842353 845243 := bstep (se 1 (by rfl) ⟨633932, by rfl⟩ : syracuseStep 845243 = 1267865) B1267865
theorem B845319 : Blo 842353 845319 := bstep (se 1 (by rfl) ⟨633989, by rfl⟩ : syracuseStep 845319 = 1267979) B1267979
theorem B845327 : Blo 842353 845327 := bstep (se 1 (by rfl) ⟨633995, by rfl⟩ : syracuseStep 845327 = 1267991) B1267991
theorem B845371 : Blo 842353 845371 := bstep (se 1 (by rfl) ⟨634028, by rfl⟩ : syracuseStep 845371 = 1268057) B1268057
theorem B845447 : Blo 842353 845447 := bstep (se 1 (by rfl) ⟨634085, by rfl⟩ : syracuseStep 845447 = 1268171) B1268171
theorem B845455 : Blo 842353 845455 := bstep (se 1 (by rfl) ⟨634091, by rfl⟩ : syracuseStep 845455 = 1268183) B1268183
theorem B845499 : Blo 842353 845499 := bstep (se 1 (by rfl) ⟨634124, by rfl⟩ : syracuseStep 845499 = 1268249) B1268249
theorem B845575 : Blo 842353 845575 := bstep (se 1 (by rfl) ⟨634181, by rfl⟩ : syracuseStep 845575 = 1268363) B1268363
theorem B845583 : Blo 842353 845583 := bstep (se 1 (by rfl) ⟨634187, by rfl⟩ : syracuseStep 845583 = 1268375) B1268375
theorem B2844449 : Blo 842353 2844449 := bstep (se 2 (by rfl) ⟨1066668, by rfl⟩ : syracuseStep 2844449 = 2133337) B2133337
theorem B5400371 : Blo 842353 5400371 := bstep (se 1 (by rfl) ⟨4050278, by rfl⟩ : syracuseStep 5400371 = 8100557) B8100557
theorem B845627 : Blo 842353 845627 := bstep (se 1 (by rfl) ⟨634220, by rfl⟩ : syracuseStep 845627 = 1268441) B1268441
theorem B845703 : Blo 842353 845703 := bstep (se 1 (by rfl) ⟨634277, by rfl⟩ : syracuseStep 845703 = 1268555) B1268555
theorem B845711 : Blo 842353 845711 := bstep (se 1 (by rfl) ⟨634283, by rfl⟩ : syracuseStep 845711 = 1268567) B1268567
theorem B845755 : Blo 842353 845755 := bstep (se 1 (by rfl) ⟨634316, by rfl⟩ : syracuseStep 845755 = 1268633) B1268633
theorem B2287561 : Blo 842353 2287561 := bstep (se 2 (by rfl) ⟨857835, by rfl⟩ : syracuseStep 2287561 = 1715671) B1715671
theorem B5400523 : Blo 842353 5400523 := bstep (se 1 (by rfl) ⟨4050392, by rfl⟩ : syracuseStep 5400523 = 8100785) B8100785
theorem B845831 : Blo 842353 845831 := bstep (se 1 (by rfl) ⟨634373, by rfl⟩ : syracuseStep 845831 = 1268747) B1268747
theorem B845839 : Blo 842353 845839 := bstep (se 1 (by rfl) ⟨634379, by rfl⟩ : syracuseStep 845839 = 1268759) B1268759
theorem B23095313 : Blo 842353 23095313 := bstep (se 2 (by rfl) ⟨8660742, by rfl⟩ : syracuseStep 23095313 = 17321485) B17321485
theorem B845883 : Blo 842353 845883 := bstep (se 1 (by rfl) ⟨634412, by rfl⟩ : syracuseStep 845883 = 1268825) B1268825
theorem B845959 : Blo 842353 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B845967 : Blo 842353 845967 := bstep (se 1 (by rfl) ⟨634475, by rfl⟩ : syracuseStep 845967 = 1268951) B1268951
theorem B846011 : Blo 842353 846011 := bstep (se 1 (by rfl) ⟨634508, by rfl⟩ : syracuseStep 846011 = 1269017) B1269017
theorem B846087 : Blo 842353 846087 := bstep (se 1 (by rfl) ⟨634565, by rfl⟩ : syracuseStep 846087 = 1269131) B1269131
theorem B3598607 : Blo 842353 3598607 := bstep (se 1 (by rfl) ⟨2698955, by rfl⟩ : syracuseStep 3598607 = 5397911) B5397911
theorem B846095 : Blo 842353 846095 := bstep (se 1 (by rfl) ⟨634571, by rfl⟩ : syracuseStep 846095 = 1269143) B1269143
theorem B846139 : Blo 842353 846139 := bstep (se 1 (by rfl) ⟨634604, by rfl⟩ : syracuseStep 846139 = 1269209) B1269209
theorem B2845043 : Blo 842353 2845043 := bstep (se 1 (by rfl) ⟨2133782, by rfl⟩ : syracuseStep 2845043 = 4267565) B4267565
theorem B846215 : Blo 842353 846215 := bstep (se 1 (by rfl) ⟨634661, by rfl⟩ : syracuseStep 846215 = 1269323) B1269323
theorem B846223 : Blo 842353 846223 := bstep (se 1 (by rfl) ⟨634667, by rfl⟩ : syracuseStep 846223 = 1269335) B1269335
theorem B16214417 : Blo 842353 16214417 := bstep (se 2 (by rfl) ⟨6080406, by rfl⟩ : syracuseStep 16214417 = 12160813) B12160813
theorem B2025881 : Blo 842353 2025881 := bstep (se 2 (by rfl) ⟨759705, by rfl⟩ : syracuseStep 2025881 = 1519411) B1519411
theorem B846267 : Blo 842353 846267 := bstep (se 1 (by rfl) ⟨634700, by rfl⟩ : syracuseStep 846267 = 1269401) B1269401
theorem B846343 : Blo 842353 846343 := bstep (se 1 (by rfl) ⟨634757, by rfl⟩ : syracuseStep 846343 = 1269515) B1269515
theorem B846351 : Blo 842353 846351 := bstep (se 1 (by rfl) ⟨634763, by rfl⟩ : syracuseStep 846351 = 1269527) B1269527
theorem B2026043 : Blo 842353 2026043 := bstep (se 1 (by rfl) ⟨1519532, by rfl⟩ : syracuseStep 2026043 = 3039065) B3039065
theorem B7825997 : Blo 842353 7825997 := bstep (se 3 (by rfl) ⟨1467374, by rfl⟩ : syracuseStep 7825997 = 2934749) B2934749
theorem B3042049 : Blo 842353 3042049 := bstep (se 2 (by rfl) ⟨1140768, by rfl⟩ : syracuseStep 3042049 = 2281537) B2281537
theorem B1600391 : Blo 842353 1600391 := bstep (se 1 (by rfl) ⟨1200293, by rfl⟩ : syracuseStep 1600391 = 2400587) B2400587
theorem B1895543 : Blo 842353 1895543 := bstep (se 1 (by rfl) ⟨1421657, by rfl⟩ : syracuseStep 1895543 = 2843315) B2843315
theorem B3206263 : Blo 842353 3206263 := bstep (se 1 (by rfl) ⟨2404697, by rfl⟩ : syracuseStep 3206263 = 4809395) B4809395
theorem B1928377 : Blo 842353 1928377 := bstep (se 2 (by rfl) ⟨723141, by rfl⟩ : syracuseStep 1928377 = 1446283) B1446283
theorem B1895723 : Blo 842353 1895723 := bstep (se 1 (by rfl) ⟨1421792, by rfl⟩ : syracuseStep 1895723 = 2843585) B2843585
theorem B1142201 : Blo 842353 1142201 := bstep (se 2 (by rfl) ⟨428325, by rfl⟩ : syracuseStep 1142201 = 856651) B856651
theorem B4812311 : Blo 842353 4812311 := bstep (se 1 (by rfl) ⟨3609233, by rfl⟩ : syracuseStep 4812311 = 7218467) B7218467
theorem B3599939 : Blo 842353 3599939 := bstep (se 1 (by rfl) ⟨2699954, by rfl⟩ : syracuseStep 3599939 = 5399909) B5399909
theorem B1896083 : Blo 842353 1896083 := bstep (se 1 (by rfl) ⟨1422062, by rfl⟩ : syracuseStep 1896083 = 2844125) B2844125
theorem B2191033 : Blo 842353 2191033 := bstep (se 2 (by rfl) ⟨821637, by rfl⟩ : syracuseStep 2191033 = 1643275) B1643275
theorem B1896137 : Blo 842353 1896137 := bstep (se 2 (by rfl) ⟨711051, by rfl⟩ : syracuseStep 1896137 = 1422103) B1422103
theorem B5402369 : Blo 842353 5402369 := bstep (se 2 (by rfl) ⟨2025888, by rfl⟩ : syracuseStep 5402369 = 4051777) B4051777
theorem B3600281 : Blo 842353 3600281 := bstep (se 2 (by rfl) ⟨1350105, by rfl⟩ : syracuseStep 3600281 = 2700211) B2700211
theorem B3207235 : Blo 842353 3207235 := bstep (se 1 (by rfl) ⟨2405426, by rfl⟩ : syracuseStep 3207235 = 4810853) B4810853
theorem B1011983 : Blo 842353 1011983 := bstep (se 1 (by rfl) ⟨758987, by rfl⟩ : syracuseStep 1011983 = 1517975) B1517975
theorem B3207539 : Blo 842353 3207539 := bstep (se 1 (by rfl) ⟨2405654, by rfl⟩ : syracuseStep 3207539 = 4811309) B4811309
theorem B1896839 : Blo 842353 1896839 := bstep (se 1 (by rfl) ⟨1422629, by rfl⟩ : syracuseStep 1896839 = 2845259) B2845259
theorem B1601993 : Blo 842353 1601993 := bstep (se 2 (by rfl) ⟨600747, by rfl⟩ : syracuseStep 1601993 = 1201495) B1201495
theorem B1897019 : Blo 842353 1897019 := bstep (se 1 (by rfl) ⟨1422764, by rfl⟩ : syracuseStep 1897019 = 2845529) B2845529
theorem B1897145 : Blo 842353 1897145 := bstep (se 2 (by rfl) ⟨711429, by rfl⟩ : syracuseStep 1897145 = 1422859) B1422859
theorem B14447321 : Blo 842353 14447321 := bstep (se 2 (by rfl) ⟨5417745, by rfl⟩ : syracuseStep 14447321 = 10835491) B10835491
theorem B3207995 : Blo 842353 3207995 := bstep (se 1 (by rfl) ⟨2405996, by rfl⟩ : syracuseStep 3207995 = 4811993) B4811993
theorem B2847635 : Blo 842353 2847635 := bstep (se 1 (by rfl) ⟨2135726, by rfl⟩ : syracuseStep 2847635 = 4271453) B4271453
theorem B1897487 : Blo 842353 1897487 := bstep (se 1 (by rfl) ⟨1423115, by rfl⟩ : syracuseStep 1897487 = 2846231) B2846231
theorem B1143823 : Blo 842353 1143823 := bstep (se 1 (by rfl) ⟨857867, by rfl⟩ : syracuseStep 1143823 = 1715735) B1715735
theorem B1897505 : Blo 842353 1897505 := bstep (se 2 (by rfl) ⟨711564, by rfl⟩ : syracuseStep 1897505 = 1423129) B1423129
theorem B9598013 : Blo 842353 9598013 := bstep (se 3 (by rfl) ⟨1799627, by rfl⟩ : syracuseStep 9598013 = 3599255) B3599255
theorem B4879631 : Blo 842353 4879631 := bstep (se 1 (by rfl) ⟨3659723, by rfl⟩ : syracuseStep 4879631 = 7319447) B7319447
theorem B3208481 : Blo 842353 3208481 := bstep (se 2 (by rfl) ⟨1203180, by rfl⟩ : syracuseStep 3208481 = 2406361) B2406361
theorem B1897847 : Blo 842353 1897847 := bstep (se 1 (by rfl) ⟨1423385, by rfl⟩ : syracuseStep 1897847 = 2846771) B2846771
theorem B11859335 : Blo 842353 11859335 := bstep (se 1 (by rfl) ⟨8894501, by rfl⟩ : syracuseStep 11859335 = 17789003) B17789003
theorem B4814225 : Blo 842353 4814225 := bstep (se 2 (by rfl) ⟨1805334, by rfl⟩ : syracuseStep 4814225 = 3610669) B3610669
theorem B1898027 : Blo 842353 1898027 := bstep (se 1 (by rfl) ⟨1423520, by rfl⟩ : syracuseStep 1898027 = 2847041) B2847041
theorem B947983 : Blo 842353 947983 := bstep (se 1 (by rfl) ⟨710987, by rfl⟩ : syracuseStep 947983 = 1421975) B1421975
theorem B1898387 : Blo 842353 1898387 := bstep (se 1 (by rfl) ⟨1423790, by rfl⟩ : syracuseStep 1898387 = 2847581) B2847581
theorem B16250777 : Blo 842353 16250777 := bstep (se 2 (by rfl) ⟨6094041, by rfl⟩ : syracuseStep 16250777 = 12188083) B12188083
theorem B1898441 : Blo 842353 1898441 := bstep (se 2 (by rfl) ⟨711915, by rfl⟩ : syracuseStep 1898441 = 1423831) B1423831
theorem B3897355 : Blo 842353 3897355 := bstep (se 1 (by rfl) ⟨2923016, by rfl⟩ : syracuseStep 3897355 = 5846033) B5846033
theorem B1800235 : Blo 842353 1800235 := bstep (se 1 (by rfl) ⟨1350176, by rfl⟩ : syracuseStep 1800235 = 2700353) B2700353
theorem B20510765 : Blo 842353 20510765 := bstep (se 3 (by rfl) ⟨3845768, by rfl⟩ : syracuseStep 20510765 = 7691537) B7691537
theorem B4814909 : Blo 842353 4814909 := bstep (se 3 (by rfl) ⟨902795, by rfl⟩ : syracuseStep 4814909 = 1805591) B1805591
theorem B1800311 : Blo 842353 1800311 := bstep (se 1 (by rfl) ⟨1350233, by rfl⟩ : syracuseStep 1800311 = 2700467) B2700467
theorem B3209453 : Blo 842353 3209453 := bstep (se 3 (by rfl) ⟨601772, by rfl⟩ : syracuseStep 3209453 = 1203545) B1203545
theorem B948487 : Blo 842353 948487 := bstep (se 1 (by rfl) ⟨711365, by rfl⟩ : syracuseStep 948487 = 1422731) B1422731
theorem B2849039 : Blo 842353 2849039 := bstep (se 1 (by rfl) ⟨2136779, by rfl⟩ : syracuseStep 2849039 = 4273559) B4273559
theorem B5142799 : Blo 842353 5142799 := bstep (se 1 (by rfl) ⟨3857099, by rfl⟩ : syracuseStep 5142799 = 7714199) B7714199
theorem B1603975 : Blo 842353 1603975 := bstep (se 1 (by rfl) ⟨1202981, by rfl⟩ : syracuseStep 1603975 = 2405963) B2405963
theorem B948667 : Blo 842353 948667 := bstep (se 1 (by rfl) ⟨711500, by rfl⟩ : syracuseStep 948667 = 1423001) B1423001
theorem B3045899 : Blo 842353 3045899 := bstep (se 1 (by rfl) ⟨2284424, by rfl⟩ : syracuseStep 3045899 = 4568849) B4568849
theorem B2849309 : Blo 842353 2849309 := bstep (se 3 (by rfl) ⟨534245, by rfl⟩ : syracuseStep 2849309 = 1068491) B1068491
theorem B1899143 : Blo 842353 1899143 := bstep (se 1 (by rfl) ⟨1424357, by rfl⟩ : syracuseStep 1899143 = 2848715) B2848715
theorem B1899323 : Blo 842353 1899323 := bstep (se 1 (by rfl) ⟨1424492, by rfl⟩ : syracuseStep 1899323 = 2848985) B2848985
theorem B949135 : Blo 842353 949135 := bstep (se 1 (by rfl) ⟨711851, by rfl⟩ : syracuseStep 949135 = 1423703) B1423703
theorem B3210137 : Blo 842353 3210137 := bstep (se 2 (by rfl) ⟨1203801, by rfl⟩ : syracuseStep 3210137 = 2407603) B2407603
theorem B1899449 : Blo 842353 1899449 := bstep (se 2 (by rfl) ⟨712293, by rfl⟩ : syracuseStep 1899449 = 1424587) B1424587
theorem B9633005 : Blo 842353 9633005 := bstep (se 3 (by rfl) ⟨1806188, by rfl⟩ : syracuseStep 9633005 = 3612377) B3612377
theorem B1899791 : Blo 842353 1899791 := bstep (se 1 (by rfl) ⟨1424843, by rfl⟩ : syracuseStep 1899791 = 2849687) B2849687
theorem B1899809 : Blo 842353 1899809 := bstep (se 2 (by rfl) ⟨712428, by rfl⟩ : syracuseStep 1899809 = 1424857) B1424857
theorem B949639 : Blo 842353 949639 := bstep (se 1 (by rfl) ⟨712229, by rfl⟩ : syracuseStep 949639 = 1424459) B1424459
theorem B949819 : Blo 842353 949819 := bstep (se 1 (by rfl) ⟨712364, by rfl⟩ : syracuseStep 949819 = 1424729) B1424729
theorem B1900151 : Blo 842353 1900151 := bstep (se 1 (by rfl) ⟨1425113, by rfl⟩ : syracuseStep 1900151 = 2850227) B2850227
theorem B1900331 : Blo 842353 1900331 := bstep (se 1 (by rfl) ⟨1425248, by rfl⟩ : syracuseStep 1900331 = 2850497) B2850497
theorem B3211123 : Blo 842353 3211123 := bstep (se 1 (by rfl) ⟨2408342, by rfl⟩ : syracuseStep 3211123 = 4816685) B4816685
theorem B2850713 : Blo 842353 2850713 := bstep (se 2 (by rfl) ⟨1069017, by rfl⟩ : syracuseStep 2850713 = 2138035) B2138035
theorem B1605577 : Blo 842353 1605577 := bstep (se 2 (by rfl) ⟨602091, by rfl⟩ : syracuseStep 1605577 = 1204183) B1204183
theorem B1015799 : Blo 842353 1015799 := bstep (se 1 (by rfl) ⟨761849, by rfl⟩ : syracuseStep 1015799 = 1523699) B1523699
theorem B1900601 : Blo 842353 1900601 := bstep (se 2 (by rfl) ⟨712725, by rfl⟩ : syracuseStep 1900601 = 1425451) B1425451
theorem B950395 : Blo 842353 950395 := bstep (se 1 (by rfl) ⟨712796, by rfl⟩ : syracuseStep 950395 = 1425593) B1425593
theorem B6947045 : Blo 842353 6947045 := bstep (se 4 (by rfl) ⟨651285, by rfl⟩ : syracuseStep 6947045 = 1302571) B1302571
theorem B1605881 : Blo 842353 1605881 := bstep (se 2 (by rfl) ⟨602205, by rfl⟩ : syracuseStep 1605881 = 1204411) B1204411
theorem B1900943 : Blo 842353 1900943 := bstep (se 1 (by rfl) ⟨1425707, by rfl⟩ : syracuseStep 1900943 = 2851415) B2851415
theorem B1606063 : Blo 842353 1606063 := bstep (se 1 (by rfl) ⟨1204547, by rfl⟩ : syracuseStep 1606063 = 2409095) B2409095
theorem B2851361 : Blo 842353 2851361 := bstep (se 2 (by rfl) ⟨1069260, by rfl⟩ : syracuseStep 2851361 = 2138521) B2138521
theorem B950863 : Blo 842353 950863 := bstep (se 1 (by rfl) ⟨713147, by rfl⟩ : syracuseStep 950863 = 1426295) B1426295
theorem B1606223 : Blo 842353 1606223 := bstep (se 1 (by rfl) ⟨1204667, by rfl⟩ : syracuseStep 1606223 = 2409335) B2409335
theorem B7504595 : Blo 842353 7504595 := bstep (se 1 (by rfl) ⟨5628446, by rfl⟩ : syracuseStep 7504595 = 11256893) B11256893
theorem B1901267 : Blo 842353 1901267 := bstep (se 1 (by rfl) ⟨1425950, by rfl⟩ : syracuseStep 1901267 = 2851901) B2851901
theorem B2851577 : Blo 842353 2851577 := bstep (se 2 (by rfl) ⟨1069341, by rfl⟩ : syracuseStep 2851577 = 2138683) B2138683
theorem B11698993 : Blo 842353 11698993 := bstep (se 2 (by rfl) ⟨4387122, by rfl⟩ : syracuseStep 11698993 = 8774245) B8774245
theorem B951259 : Blo 842353 951259 := bstep (se 1 (by rfl) ⟨713444, by rfl⟩ : syracuseStep 951259 = 1426889) B1426889
theorem B8684509 : Blo 842353 8684509 := bstep (se 3 (by rfl) ⟨1628345, by rfl⟩ : syracuseStep 8684509 = 3256691) B3256691
theorem B2851847 : Blo 842353 2851847 := bstep (se 1 (by rfl) ⟨2138885, by rfl⟩ : syracuseStep 2851847 = 4277771) B4277771
theorem B3212369 : Blo 842353 3212369 := bstep (se 2 (by rfl) ⟨1204638, by rfl⟩ : syracuseStep 3212369 = 2409277) B2409277
theorem B2851955 : Blo 842353 2851955 := bstep (se 1 (by rfl) ⟨2138966, by rfl⟩ : syracuseStep 2851955 = 4277933) B4277933
theorem B36602999 : Blo 842353 36602999 := bstep (se 1 (by rfl) ⟨27452249, by rfl⟩ : syracuseStep 36602999 = 54904499) B54904499
theorem B2852225 : Blo 842353 2852225 := bstep (se 2 (by rfl) ⟨1069584, by rfl⟩ : syracuseStep 2852225 = 2139169) B2139169
theorem B2033039 : Blo 842353 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B7210403 : Blo 842353 7210403 := bstep (se 1 (by rfl) ⟨5407802, by rfl⟩ : syracuseStep 7210403 = 10815605) B10815605
theorem B951727 : Blo 842353 951727 := bstep (se 1 (by rfl) ⟨713795, by rfl⟩ : syracuseStep 951727 = 1427591) B1427591
theorem B11568683 : Blo 842353 11568683 := bstep (se 1 (by rfl) ⟨8676512, by rfl⟩ : syracuseStep 11568683 = 17353025) B17353025
theorem B1902203 : Blo 842353 1902203 := bstep (se 1 (by rfl) ⟨1426652, by rfl⟩ : syracuseStep 1902203 = 2853305) B2853305
theorem B12977863 : Blo 842353 12977863 := bstep (se 1 (by rfl) ⟨9733397, by rfl⟩ : syracuseStep 12977863 = 19466795) B19466795
theorem B12191431 : Blo 842353 12191431 := bstep (se 1 (by rfl) ⟨9143573, by rfl⟩ : syracuseStep 12191431 = 18287147) B18287147
theorem B1902329 : Blo 842353 1902329 := bstep (se 2 (by rfl) ⟨713373, by rfl⟩ : syracuseStep 1902329 = 1426747) B1426747
theorem B1804207 : Blo 842353 1804207 := bstep (se 1 (by rfl) ⟨1353155, by rfl⟩ : syracuseStep 1804207 = 2706311) B2706311
theorem B1443847 : Blo 842353 1443847 := bstep (se 1 (by rfl) ⟨1082885, by rfl⟩ : syracuseStep 1443847 = 2165771) B2165771
theorem B1902599 : Blo 842353 1902599 := bstep (se 1 (by rfl) ⟨1426949, by rfl⟩ : syracuseStep 1902599 = 2853899) B2853899
theorem B5769253 : Blo 842353 5769253 := bstep (se 4 (by rfl) ⟨540867, by rfl⟩ : syracuseStep 5769253 = 1081735) B1081735
theorem B1902671 : Blo 842353 1902671 := bstep (se 1 (by rfl) ⟨1427003, by rfl⟩ : syracuseStep 1902671 = 2854007) B2854007
theorem B34670693 : Blo 842353 34670693 := bstep (se 4 (by rfl) ⟨3250377, by rfl⟩ : syracuseStep 34670693 = 6500755) B6500755
theorem B2853035 : Blo 842353 2853035 := bstep (se 1 (by rfl) ⟨2139776, by rfl⟩ : syracuseStep 2853035 = 4279553) B4279553
theorem B6424919 : Blo 842353 6424919 := bstep (se 1 (by rfl) ⟨4818689, by rfl⟩ : syracuseStep 6424919 = 9637379) B9637379
theorem B1903067 : Blo 842353 1903067 := bstep (se 1 (by rfl) ⟨1427300, by rfl⟩ : syracuseStep 1903067 = 2854601) B2854601
theorem B3050081 : Blo 842353 3050081 := bstep (se 2 (by rfl) ⟨1143780, by rfl⟩ : syracuseStep 3050081 = 2287561) B2287561
theorem B2853575 : Blo 842353 2853575 := bstep (se 1 (by rfl) ⟨2140181, by rfl⟩ : syracuseStep 2853575 = 4280363) B4280363
theorem B6097619 : Blo 842353 6097619 := bstep (se 1 (by rfl) ⟨4573214, by rfl⟩ : syracuseStep 6097619 = 9146429) B9146429
theorem B2132831 : Blo 842353 2132831 := bstep (se 1 (by rfl) ⟨1599623, by rfl⟩ : syracuseStep 2132831 = 3199247) B3199247
theorem B1903535 : Blo 842353 1903535 := bstep (se 1 (by rfl) ⟨1427651, by rfl⟩ : syracuseStep 1903535 = 2855303) B2855303
theorem B1903787 : Blo 842353 1903787 := bstep (se 1 (by rfl) ⟨1427840, by rfl⟩ : syracuseStep 1903787 = 2855681) B2855681
theorem B2854439 : Blo 842353 2854439 := bstep (se 1 (by rfl) ⟨2140829, by rfl⟩ : syracuseStep 2854439 = 4281659) B4281659
theorem B8097367 : Blo 842353 8097367 := bstep (se 1 (by rfl) ⟨6073025, by rfl⟩ : syracuseStep 8097367 = 12146051) B12146051
theorem B2854547 : Blo 842353 2854547 := bstep (se 1 (by rfl) ⟨2140910, by rfl⟩ : syracuseStep 2854547 = 4281821) B4281821
theorem B6590267 : Blo 842353 6590267 := bstep (se 1 (by rfl) ⟨4942700, by rfl⟩ : syracuseStep 6590267 = 9885401) B9885401
theorem B2854763 : Blo 842353 2854763 := bstep (se 1 (by rfl) ⟨2141072, by rfl⟩ : syracuseStep 2854763 = 4282145) B4282145
theorem B6164333 : Blo 842353 6164333 := bstep (se 3 (by rfl) ⟨1155812, by rfl⟩ : syracuseStep 6164333 = 2311625) B2311625
theorem B2854817 : Blo 842353 2854817 := bstep (se 2 (by rfl) ⟨1070556, by rfl⟩ : syracuseStep 2854817 = 2141113) B2141113
theorem B2133935 : Blo 842353 2133935 := bstep (se 1 (by rfl) ⟨1600451, by rfl⟩ : syracuseStep 2133935 = 3200903) B3200903
theorem B5411083 : Blo 842353 5411083 := bstep (se 1 (by rfl) ⟨4058312, by rfl⟩ : syracuseStep 5411083 = 8116625) B8116625
theorem B4624651 : Blo 842353 4624651 := bstep (se 1 (by rfl) ⟨3468488, by rfl⟩ : syracuseStep 4624651 = 6936977) B6936977
theorem B2855411 : Blo 842353 2855411 := bstep (se 1 (by rfl) ⟨2141558, by rfl⟩ : syracuseStep 2855411 = 4283117) B4283117
theorem B6165017 : Blo 842353 6165017 := bstep (se 2 (by rfl) ⟨2311881, by rfl⟩ : syracuseStep 6165017 = 4623763) B4623763
theorem B6099785 : Blo 842353 6099785 := bstep (se 2 (by rfl) ⟨2287419, by rfl⟩ : syracuseStep 6099785 = 4574839) B4574839
theorem B4264811 : Blo 842353 4264811 := bstep (se 1 (by rfl) ⟨3198608, by rfl⟩ : syracuseStep 4264811 = 6397217) B6397217
theorem B3707831 : Blo 842353 3707831 := bstep (se 1 (by rfl) ⟨2780873, by rfl⟩ : syracuseStep 3707831 = 5561747) B5561747
theorem B1708987 : Blo 842353 1708987 := bstep (se 1 (by rfl) ⟨1281740, by rfl⟩ : syracuseStep 1708987 = 2563481) B2563481
theorem B2855951 : Blo 842353 2855951 := bstep (se 1 (by rfl) ⟨2141963, by rfl⟩ : syracuseStep 2855951 = 4283927) B4283927
theorem B2135119 : Blo 842353 2135119 := bstep (se 1 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 2135119 = 3202679) B3202679
theorem B3085427 : Blo 842353 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B3249305 : Blo 842353 3249305 := bstep (se 2 (by rfl) ⟨1218489, by rfl⟩ : syracuseStep 3249305 = 2436979) B2436979
theorem B9147811 : Blo 842353 9147811 := bstep (se 1 (by rfl) ⟨6860858, by rfl⟩ : syracuseStep 9147811 = 13721717) B13721717
theorem B1218011 : Blo 842353 1218011 := bstep (se 1 (by rfl) ⟨913508, by rfl⟩ : syracuseStep 1218011 = 1827017) B1827017
theorem B4265459 : Blo 842353 4265459 := bstep (se 1 (by rfl) ⟨3199094, by rfl⟩ : syracuseStep 4265459 = 6398189) B6398189
theorem B1283663 : Blo 842353 1283663 := bstep (se 1 (by rfl) ⟨962747, by rfl⟩ : syracuseStep 1283663 = 1925495) B1925495
theorem B2135767 : Blo 842353 2135767 := bstep (se 1 (by rfl) ⟨1601825, by rfl⟩ : syracuseStep 2135767 = 3203651) B3203651
theorem B3610327 : Blo 842353 3610327 := bstep (se 1 (by rfl) ⟨2707745, by rfl⟩ : syracuseStep 3610327 = 5415491) B5415491
theorem B2136071 : Blo 842353 2136071 := bstep (se 1 (by rfl) ⟨1602053, by rfl⟩ : syracuseStep 2136071 = 3204107) B3204107
theorem B3086531 : Blo 842353 3086531 := bstep (se 1 (by rfl) ⟨2314898, by rfl⟩ : syracuseStep 3086531 = 4629797) B4629797
theorem B8460935 : Blo 842353 8460935 := bstep (se 1 (by rfl) ⟨6345701, by rfl⟩ : syracuseStep 8460935 = 12691403) B12691403
theorem B4266755 : Blo 842353 4266755 := bstep (se 1 (by rfl) ⟨3200066, by rfl⟩ : syracuseStep 4266755 = 6400133) B6400133
theorem B2399071 : Blo 842353 2399071 := bstep (se 1 (by rfl) ⟨1799303, by rfl⟩ : syracuseStep 2399071 = 3598607) B3598607
theorem B1350587 : Blo 842353 1350587 := bstep (se 1 (by rfl) ⟨1012940, by rfl⟩ : syracuseStep 1350587 = 2025881) B2025881
theorem B1350695 : Blo 842353 1350695 := bstep (se 1 (by rfl) ⟨1013021, by rfl⟩ : syracuseStep 1350695 = 2026043) B2026043
theorem B5217331 : Blo 842353 5217331 := bstep (se 1 (by rfl) ⟨3912998, by rfl⟩ : syracuseStep 5217331 = 7825997) B7825997
theorem B2465149 : Blo 842353 2465149 := bstep (se 3 (by rfl) ⟨462215, by rfl⟩ : syracuseStep 2465149 = 924431) B924431
theorem B2399959 : Blo 842353 2399959 := bstep (se 1 (by rfl) ⟨1799969, by rfl⟩ : syracuseStep 2399959 = 3599939) B3599939
theorem B2400187 : Blo 842353 2400187 := bstep (se 1 (by rfl) ⟨1800140, by rfl⟩ : syracuseStep 2400187 = 3600281) B3600281
theorem B2400313 : Blo 842353 2400313 := bstep (se 2 (by rfl) ⟨900117, by rfl⟩ : syracuseStep 2400313 = 1800235) B1800235
theorem B2138359 : Blo 842353 2138359 := bstep (se 1 (by rfl) ⟨1603769, by rfl⟩ : syracuseStep 2138359 = 3207539) B3207539
theorem B4268375 : Blo 842353 4268375 := bstep (se 1 (by rfl) ⟨3201281, by rfl⟩ : syracuseStep 4268375 = 6402563) B6402563
theorem B6857065 : Blo 842353 6857065 := bstep (se 2 (by rfl) ⟨2571399, by rfl⟩ : syracuseStep 6857065 = 5142799) B5142799
theorem B2138633 : Blo 842353 2138633 := bstep (se 2 (by rfl) ⟨801987, by rfl⟩ : syracuseStep 2138633 = 1603975) B1603975
theorem B6496793 : Blo 842353 6496793 := bstep (se 2 (by rfl) ⟨2436297, by rfl⟩ : syracuseStep 6496793 = 4872595) B4872595
theorem B2138663 : Blo 842353 2138663 := bstep (se 1 (by rfl) ⟨1603997, by rfl⟩ : syracuseStep 2138663 = 3207995) B3207995
theorem B3613319 : Blo 842353 3613319 := bstep (se 1 (by rfl) ⟨2709989, by rfl⟩ : syracuseStep 3613319 = 5419979) B5419979
theorem B3613369 : Blo 842353 3613369 := bstep (se 2 (by rfl) ⟨1355013, by rfl⟩ : syracuseStep 3613369 = 2710027) B2710027
theorem B6398675 : Blo 842353 6398675 := bstep (se 1 (by rfl) ⟨4799006, by rfl⟩ : syracuseStep 6398675 = 9598013) B9598013
theorem B3253087 : Blo 842353 3253087 := bstep (se 1 (by rfl) ⟨2439815, by rfl⟩ : syracuseStep 3253087 = 4879631) B4879631
theorem B2138987 : Blo 842353 2138987 := bstep (se 1 (by rfl) ⟨1604240, by rfl⟩ : syracuseStep 2138987 = 3208481) B3208481
theorem B7906223 : Blo 842353 7906223 := bstep (se 1 (by rfl) ⟨5929667, by rfl⟩ : syracuseStep 7906223 = 11859335) B11859335
theorem B3089335 : Blo 842353 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B13673843 : Blo 842353 13673843 := bstep (se 1 (by rfl) ⟨10255382, by rfl⟩ : syracuseStep 13673843 = 20510765) B20510765
theorem B1713595 : Blo 842353 1713595 := bstep (se 1 (by rfl) ⟨1285196, by rfl⟩ : syracuseStep 1713595 = 2570393) B2570393
theorem B2139635 : Blo 842353 2139635 := bstep (se 1 (by rfl) ⟨1604726, by rfl⟩ : syracuseStep 2139635 = 3209453) B3209453
theorem B2140091 : Blo 842353 2140091 := bstep (se 1 (by rfl) ⟨1605068, by rfl⟩ : syracuseStep 2140091 = 3210137) B3210137
theorem B8660945 : Blo 842353 8660945 := bstep (se 2 (by rfl) ⟨3247854, by rfl⟩ : syracuseStep 8660945 = 6495709) B6495709
theorem B2140769 : Blo 842353 2140769 := bstep (se 2 (by rfl) ⟨802788, by rfl⟩ : syracuseStep 2140769 = 1605577) B1605577
theorem B1354411 : Blo 842353 1354411 := bstep (se 1 (by rfl) ⟨1015808, by rfl⟩ : syracuseStep 1354411 = 2031617) B2031617
theorem B1714859 : Blo 842353 1714859 := bstep (se 1 (by rfl) ⟨1286144, by rfl⟩ : syracuseStep 1714859 = 2572289) B2572289
theorem B23079653 : Blo 842353 23079653 := bstep (se 4 (by rfl) ⟨2163717, by rfl⟩ : syracuseStep 23079653 = 4327435) B4327435
theorem B1518955 : Blo 842353 1518955 := bstep (se 1 (by rfl) ⟨1139216, by rfl⟩ : syracuseStep 1518955 = 2278433) B2278433
theorem B4107763 : Blo 842353 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B1355513 : Blo 842353 1355513 := bstep (se 2 (by rfl) ⟨508317, by rfl⟩ : syracuseStep 1355513 = 1016635) B1016635
theorem B13676303 : Blo 842353 13676303 := bstep (se 1 (by rfl) ⟨10257227, by rfl⟩ : syracuseStep 13676303 = 20514455) B20514455
theorem B4271939 : Blo 842353 4271939 := bstep (se 1 (by rfl) ⟨3203954, by rfl⟩ : syracuseStep 4271939 = 6407909) B6407909
theorem B2142227 : Blo 842353 2142227 := bstep (se 1 (by rfl) ⟨1606670, by rfl⟩ : syracuseStep 2142227 = 3213341) B3213341
theorem B6402077 : Blo 842353 6402077 := bstep (se 3 (by rfl) ⟨1200389, by rfl⟩ : syracuseStep 6402077 = 2400779) B2400779
theorem B24391853 : Blo 842353 24391853 := bstep (se 3 (by rfl) ⟨4573472, by rfl⟩ : syracuseStep 24391853 = 9146945) B9146945
theorem B5779763 : Blo 842353 5779763 := bstep (se 1 (by rfl) ⟨4334822, by rfl⟩ : syracuseStep 5779763 = 8669645) B8669645
theorem B1421833 : Blo 842353 1421833 := bstep (se 2 (by rfl) ⟨533187, by rfl⟩ : syracuseStep 1421833 = 1066375) B1066375
theorem B2699801 : Blo 842353 2699801 := bstep (se 2 (by rfl) ⟨1012425, by rfl⟩ : syracuseStep 2699801 = 2024851) B2024851
theorem B1520167 : Blo 842353 1520167 := bstep (se 1 (by rfl) ⟨1140125, by rfl⟩ : syracuseStep 1520167 = 2280251) B2280251
theorem B2404903 : Blo 842353 2404903 := bstep (se 1 (by rfl) ⟨1803677, by rfl⟩ : syracuseStep 2404903 = 3607355) B3607355
theorem B2404961 : Blo 842353 2404961 := bstep (se 2 (by rfl) ⟨901860, by rfl⟩ : syracuseStep 2404961 = 1803721) B1803721
theorem B1421995 : Blo 842353 1421995 := bstep (se 1 (by rfl) ⟨1066496, by rfl⟩ : syracuseStep 1421995 = 2132993) B2132993
theorem B1422299 : Blo 842353 1422299 := bstep (se 1 (by rfl) ⟨1066724, by rfl⟩ : syracuseStep 1422299 = 2133449) B2133449
theorem B1422535 : Blo 842353 1422535 := bstep (se 1 (by rfl) ⟨1066901, by rfl⟩ : syracuseStep 1422535 = 2133803) B2133803
theorem B1422697 : Blo 842353 1422697 := bstep (se 2 (by rfl) ⟨533511, by rfl⟩ : syracuseStep 1422697 = 1067023) B1067023
theorem B10794485 : Blo 842353 10794485 := bstep (se 5 (by rfl) ⟨505991, by rfl⟩ : syracuseStep 10794485 = 1011983) B1011983
theorem B13678379 : Blo 842353 13678379 := bstep (se 1 (by rfl) ⟨10258784, by rfl⟩ : syracuseStep 13678379 = 20517569) B20517569
theorem B2602847 : Blo 842353 2602847 := bstep (se 1 (by rfl) ⟨1952135, by rfl⟩ : syracuseStep 2602847 = 3904271) B3904271
theorem B1423291 : Blo 842353 1423291 := bstep (se 1 (by rfl) ⟨1067468, by rfl⟩ : syracuseStep 1423291 = 2134937) B2134937
theorem B2406419 : Blo 842353 2406419 := bstep (se 1 (by rfl) ⟨1804814, by rfl⟩ : syracuseStep 2406419 = 3609629) B3609629
theorem B1423399 : Blo 842353 1423399 := bstep (se 1 (by rfl) ⟨1067549, by rfl⟩ : syracuseStep 1423399 = 2135099) B2135099
theorem B1423723 : Blo 842353 1423723 := bstep (se 1 (by rfl) ⟨1067792, by rfl⟩ : syracuseStep 1423723 = 2135585) B2135585
theorem B1522027 : Blo 842353 1522027 := bstep (se 1 (by rfl) ⟨1141520, by rfl⟩ : syracuseStep 1522027 = 2283041) B2283041
theorem B3422753 : Blo 842353 3422753 := bstep (se 2 (by rfl) ⟨1283532, by rfl⟩ : syracuseStep 3422753 = 2567065) B2567065
theorem B3652231 : Blo 842353 3652231 := bstep (se 1 (by rfl) ⟨2739173, by rfl⟩ : syracuseStep 3652231 = 5478347) B5478347
theorem B3422969 : Blo 842353 3422969 := bstep (se 2 (by rfl) ⟨1283613, by rfl⟩ : syracuseStep 3422969 = 2567227) B2567227
theorem B4275017 : Blo 842353 4275017 := bstep (se 2 (by rfl) ⟨1603131, by rfl⟩ : syracuseStep 4275017 = 3206263) B3206263
theorem B39500723 : Blo 842353 39500723 := bstep (se 1 (by rfl) ⟨29625542, by rfl⟩ : syracuseStep 39500723 = 59251085) B59251085
theorem B10828727 : Blo 842353 10828727 := bstep (se 1 (by rfl) ⟨8121545, by rfl⟩ : syracuseStep 10828727 = 16243091) B16243091
theorem B3128473 : Blo 842353 3128473 := bstep (se 2 (by rfl) ⟨1173177, by rfl⟩ : syracuseStep 3128473 = 2346355) B2346355
theorem B1424783 : Blo 842353 1424783 := bstep (se 1 (by rfl) ⟨1068587, by rfl⟩ : syracuseStep 1424783 = 2137175) B2137175
theorem B1425019 : Blo 842353 1425019 := bstep (se 1 (by rfl) ⟨1068764, by rfl⟩ : syracuseStep 1425019 = 2137529) B2137529
theorem B2703223 : Blo 842353 2703223 := bstep (se 1 (by rfl) ⟨2027417, by rfl⟩ : syracuseStep 2703223 = 4054835) B4054835
theorem B2703287 : Blo 842353 2703287 := bstep (se 1 (by rfl) ⟨2027465, by rfl⟩ : syracuseStep 2703287 = 4054931) B4054931
theorem B4276313 : Blo 842353 4276313 := bstep (se 2 (by rfl) ⟨1603617, by rfl⟩ : syracuseStep 4276313 = 3207235) B3207235
theorem B52084853 : Blo 842353 52084853 := bstep (se 5 (by rfl) ⟨2441477, by rfl⟩ : syracuseStep 52084853 = 4882955) B4882955
theorem B6406451 : Blo 842353 6406451 := bstep (se 1 (by rfl) ⟨4804838, by rfl⟩ : syracuseStep 6406451 = 9609677) B9609677
theorem B4800829 : Blo 842353 4800829 := bstep (se 3 (by rfl) ⟨900155, by rfl⟩ : syracuseStep 4800829 = 1800311) B1800311
theorem B1425883 : Blo 842353 1425883 := bstep (se 1 (by rfl) ⟨1069412, by rfl⟩ : syracuseStep 1425883 = 2138825) B2138825
theorem B3293729 : Blo 842353 3293729 := bstep (se 2 (by rfl) ⟨1235148, by rfl⟩ : syracuseStep 3293729 = 2470297) B2470297
theorem B2605607 : Blo 842353 2605607 := bstep (se 1 (by rfl) ⟨1954205, by rfl⟩ : syracuseStep 2605607 = 3908411) B3908411
theorem B2409209 : Blo 842353 2409209 := bstep (se 2 (by rfl) ⟨903453, by rfl⟩ : syracuseStep 2409209 = 1806907) B1806907
theorem B1426511 : Blo 842353 1426511 := bstep (se 1 (by rfl) ⟨1069883, by rfl⟩ : syracuseStep 1426511 = 2139767) B2139767
theorem B2409551 : Blo 842353 2409551 := bstep (se 1 (by rfl) ⟨1807163, by rfl⟩ : syracuseStep 2409551 = 3614327) B3614327
theorem B1525097 : Blo 842353 1525097 := bstep (se 2 (by rfl) ⟨571911, by rfl⟩ : syracuseStep 1525097 = 1143823) B1143823
theorem B7226941 : Blo 842353 7226941 := bstep (se 3 (by rfl) ⟨1355051, by rfl⟩ : syracuseStep 7226941 = 2710103) B2710103
theorem B1066927 : Blo 842353 1066927 := bstep (se 1 (by rfl) ⟨800195, by rfl⟩ : syracuseStep 1066927 = 1600391) B1600391
theorem B1427375 : Blo 842353 1427375 := bstep (se 1 (by rfl) ⟨1070531, by rfl⟩ : syracuseStep 1427375 = 2141063) B2141063
theorem B1263695 : Blo 842353 1263695 := bstep (se 1 (by rfl) ⟨947771, by rfl⟩ : syracuseStep 1263695 = 1895543) B1895543
theorem B3426457 : Blo 842353 3426457 := bstep (se 2 (by rfl) ⟨1284921, by rfl⟩ : syracuseStep 3426457 = 2569843) B2569843
theorem B1263815 : Blo 842353 1263815 := bstep (se 1 (by rfl) ⟨947861, by rfl⟩ : syracuseStep 1263815 = 1895723) B1895723
theorem B1427807 : Blo 842353 1427807 := bstep (se 1 (by rfl) ⟨1070855, by rfl⟩ : syracuseStep 1427807 = 2141711) B2141711
theorem B1263977 : Blo 842353 1263977 := bstep (se 2 (by rfl) ⟨473991, by rfl⟩ : syracuseStep 1263977 = 947983) B947983
theorem B1264055 : Blo 842353 1264055 := bstep (se 1 (by rfl) ⟨948041, by rfl⟩ : syracuseStep 1264055 = 1896083) B1896083
theorem B1264091 : Blo 842353 1264091 := bstep (se 1 (by rfl) ⟨948068, by rfl⟩ : syracuseStep 1264091 = 1896137) B1896137
theorem B5196473 : Blo 842353 5196473 := bstep (se 2 (by rfl) ⟨1948677, by rfl⟩ : syracuseStep 5196473 = 3897355) B3897355
theorem B1264559 : Blo 842353 1264559 := bstep (se 1 (by rfl) ⟨948419, by rfl⟩ : syracuseStep 1264559 = 1896839) B1896839
theorem B1067995 : Blo 842353 1067995 := bstep (se 1 (by rfl) ⟨800996, by rfl⟩ : syracuseStep 1067995 = 1601993) B1601993
theorem B1264649 : Blo 842353 1264649 := bstep (se 2 (by rfl) ⟨474243, by rfl⟩ : syracuseStep 1264649 = 948487) B948487
theorem B1264679 : Blo 842353 1264679 := bstep (se 1 (by rfl) ⟨948509, by rfl⟩ : syracuseStep 1264679 = 1897019) B1897019
theorem B6081587 : Blo 842353 6081587 := bstep (se 1 (by rfl) ⟨4561190, by rfl⟩ : syracuseStep 6081587 = 9122381) B9122381
theorem B1264763 : Blo 842353 1264763 := bstep (se 1 (by rfl) ⟨948572, by rfl⟩ : syracuseStep 1264763 = 1897145) B1897145
theorem B1264889 : Blo 842353 1264889 := bstep (se 2 (by rfl) ⟨474333, by rfl⟩ : syracuseStep 1264889 = 948667) B948667
theorem B1264991 : Blo 842353 1264991 := bstep (se 1 (by rfl) ⟨948743, by rfl⟩ : syracuseStep 1264991 = 1897487) B1897487
theorem B1265003 : Blo 842353 1265003 := bstep (se 1 (by rfl) ⟨948752, by rfl⟩ : syracuseStep 1265003 = 1897505) B1897505
theorem B3198473 : Blo 842353 3198473 := bstep (se 2 (by rfl) ⟨1199427, by rfl⟩ : syracuseStep 3198473 = 2398855) B2398855
theorem B1265231 : Blo 842353 1265231 := bstep (se 1 (by rfl) ⟨948923, by rfl⟩ : syracuseStep 1265231 = 1897847) B1897847
theorem B11685509 : Blo 842353 11685509 := bstep (se 4 (by rfl) ⟨1095516, by rfl⟩ : syracuseStep 11685509 = 2191033) B2191033
theorem B3428029 : Blo 842353 3428029 := bstep (se 3 (by rfl) ⟨642755, by rfl⟩ : syracuseStep 3428029 = 1285511) B1285511
theorem B1265351 : Blo 842353 1265351 := bstep (se 1 (by rfl) ⟨949013, by rfl⟩ : syracuseStep 1265351 = 1898027) B1898027
theorem B1265513 : Blo 842353 1265513 := bstep (se 2 (by rfl) ⟨474567, by rfl⟩ : syracuseStep 1265513 = 949135) B949135
theorem B1265591 : Blo 842353 1265591 := bstep (se 1 (by rfl) ⟨949193, by rfl⟩ : syracuseStep 1265591 = 1898387) B1898387
theorem B10833851 : Blo 842353 10833851 := bstep (se 1 (by rfl) ⟨8125388, by rfl⟩ : syracuseStep 10833851 = 16250777) B16250777
theorem B1265627 : Blo 842353 1265627 := bstep (se 1 (by rfl) ⟨949220, by rfl⟩ : syracuseStep 1265627 = 1898441) B1898441
theorem B1266095 : Blo 842353 1266095 := bstep (se 1 (by rfl) ⟨949571, by rfl⟩ : syracuseStep 1266095 = 1899143) B1899143
theorem B1266185 : Blo 842353 1266185 := bstep (se 2 (by rfl) ⟨474819, by rfl⟩ : syracuseStep 1266185 = 949639) B949639
theorem B1266215 : Blo 842353 1266215 := bstep (se 1 (by rfl) ⟨949661, by rfl⟩ : syracuseStep 1266215 = 1899323) B1899323
theorem B7328315 : Blo 842353 7328315 := bstep (se 1 (by rfl) ⟨5496236, by rfl⟩ : syracuseStep 7328315 = 10992473) B10992473
theorem B1266299 : Blo 842353 1266299 := bstep (se 1 (by rfl) ⟨949724, by rfl⟩ : syracuseStep 1266299 = 1899449) B1899449
theorem B1266425 : Blo 842353 1266425 := bstep (se 2 (by rfl) ⟨474909, by rfl⟩ : syracuseStep 1266425 = 949819) B949819
theorem B1266527 : Blo 842353 1266527 := bstep (se 1 (by rfl) ⟨949895, by rfl⟩ : syracuseStep 1266527 = 1899791) B1899791
theorem B1266539 : Blo 842353 1266539 := bstep (se 1 (by rfl) ⟨949904, by rfl⟩ : syracuseStep 1266539 = 1899809) B1899809
theorem B3199931 : Blo 842353 3199931 := bstep (se 1 (by rfl) ⟨2399948, by rfl⟩ : syracuseStep 3199931 = 4799897) B4799897
theorem B2282575 : Blo 842353 2282575 := bstep (se 1 (by rfl) ⟨1711931, by rfl⟩ : syracuseStep 2282575 = 3423863) B3423863
theorem B1266767 : Blo 842353 1266767 := bstep (se 1 (by rfl) ⟨950075, by rfl⟩ : syracuseStep 1266767 = 1900151) B1900151
theorem B4281497 : Blo 842353 4281497 := bstep (se 2 (by rfl) ⟨1605561, by rfl⟩ : syracuseStep 4281497 = 3211123) B3211123
theorem B1266887 : Blo 842353 1266887 := bstep (se 1 (by rfl) ⟨950165, by rfl⟩ : syracuseStep 1266887 = 1900331) B1900331
theorem B9622799 : Blo 842353 9622799 := bstep (se 1 (by rfl) ⟨7217099, by rfl⟩ : syracuseStep 9622799 = 14434199) B14434199
theorem B2708797 : Blo 842353 2708797 := bstep (se 3 (by rfl) ⟨507899, by rfl⟩ : syracuseStep 2708797 = 1015799) B1015799
theorem B1267049 : Blo 842353 1267049 := bstep (se 2 (by rfl) ⟨475143, by rfl⟩ : syracuseStep 1267049 = 950287) B950287
theorem B1267127 : Blo 842353 1267127 := bstep (se 1 (by rfl) ⟨950345, by rfl⟩ : syracuseStep 1267127 = 1900691) B1900691
theorem B1267163 : Blo 842353 1267163 := bstep (se 1 (by rfl) ⟨950372, by rfl⟩ : syracuseStep 1267163 = 1900745) B1900745
theorem B3037103 : Blo 842353 3037103 := bstep (se 1 (by rfl) ⟨2277827, by rfl⟩ : syracuseStep 3037103 = 4555655) B4555655
theorem B1267631 : Blo 842353 1267631 := bstep (se 1 (by rfl) ⟨950723, by rfl⟩ : syracuseStep 1267631 = 1901447) B1901447
theorem B1267721 : Blo 842353 1267721 := bstep (se 2 (by rfl) ⟨475395, by rfl⟩ : syracuseStep 1267721 = 950791) B950791
theorem B4053007 : Blo 842353 4053007 := bstep (se 1 (by rfl) ⟨3039755, by rfl⟩ : syracuseStep 4053007 = 6079511) B6079511
theorem B1267751 : Blo 842353 1267751 := bstep (se 1 (by rfl) ⟨950813, by rfl⟩ : syracuseStep 1267751 = 1901627) B1901627
theorem B1267835 : Blo 842353 1267835 := bstep (se 1 (by rfl) ⟨950876, by rfl⟩ : syracuseStep 1267835 = 1901753) B1901753
theorem B1267961 : Blo 842353 1267961 := bstep (se 2 (by rfl) ⟨475485, by rfl⟩ : syracuseStep 1267961 = 950971) B950971
theorem B1268063 : Blo 842353 1268063 := bstep (se 1 (by rfl) ⟨951047, by rfl⟩ : syracuseStep 1268063 = 1902095) B1902095
theorem B1268075 : Blo 842353 1268075 := bstep (se 1 (by rfl) ⟨951056, by rfl⟩ : syracuseStep 1268075 = 1902113) B1902113
theorem B1268303 : Blo 842353 1268303 := bstep (se 1 (by rfl) ⟨951227, by rfl⟩ : syracuseStep 1268303 = 1902455) B1902455
theorem B842363 : Blo 842353 842363 := bstep (se 1 (by rfl) ⟨631772, by rfl⟩ : syracuseStep 842363 = 1263545) B1263545
theorem B842415 : Blo 842353 842415 := bstep (se 1 (by rfl) ⟨631811, by rfl⟩ : syracuseStep 842415 = 1263623) B1263623
theorem B842439 : Blo 842353 842439 := bstep (se 1 (by rfl) ⟨631829, by rfl⟩ : syracuseStep 842439 = 1263659) B1263659
theorem B1268423 : Blo 842353 1268423 := bstep (se 1 (by rfl) ⟨951317, by rfl⟩ : syracuseStep 1268423 = 1902635) B1902635
theorem B842459 : Blo 842353 842459 := bstep (se 1 (by rfl) ⟨631844, by rfl⟩ : syracuseStep 842459 = 1263689) B1263689
theorem B842535 : Blo 842353 842535 := bstep (se 1 (by rfl) ⟨631901, by rfl⟩ : syracuseStep 842535 = 1263803) B1263803
theorem B842575 : Blo 842353 842575 := bstep (se 1 (by rfl) ⟨631931, by rfl⟩ : syracuseStep 842575 = 1263863) B1263863
theorem B842591 : Blo 842353 842591 := bstep (se 1 (by rfl) ⟨631943, by rfl⟩ : syracuseStep 842591 = 1263887) B1263887
theorem B1268585 : Blo 842353 1268585 := bstep (se 2 (by rfl) ⟨475719, by rfl⟩ : syracuseStep 1268585 = 951439) B951439
theorem B842619 : Blo 842353 842619 := bstep (se 1 (by rfl) ⟨631964, by rfl⟩ : syracuseStep 842619 = 1263929) B1263929
theorem B842671 : Blo 842353 842671 := bstep (se 1 (by rfl) ⟨632003, by rfl⟩ : syracuseStep 842671 = 1264007) B1264007
theorem B1268663 : Blo 842353 1268663 := bstep (se 1 (by rfl) ⟨951497, by rfl⟩ : syracuseStep 1268663 = 1902995) B1902995
theorem B842695 : Blo 842353 842695 := bstep (se 1 (by rfl) ⟨632021, by rfl⟩ : syracuseStep 842695 = 1264043) B1264043
theorem B842715 : Blo 842353 842715 := bstep (se 1 (by rfl) ⟨632036, by rfl⟩ : syracuseStep 842715 = 1264073) B1264073
theorem B1268699 : Blo 842353 1268699 := bstep (se 1 (by rfl) ⟨951524, by rfl⟩ : syracuseStep 1268699 = 1903049) B1903049
theorem B842791 : Blo 842353 842791 := bstep (se 1 (by rfl) ⟨632093, by rfl⟩ : syracuseStep 842791 = 1264187) B1264187
theorem B842831 : Blo 842353 842831 := bstep (se 1 (by rfl) ⟨632123, by rfl⟩ : syracuseStep 842831 = 1264247) B1264247
theorem B842847 : Blo 842353 842847 := bstep (se 1 (by rfl) ⟨632135, by rfl⟩ : syracuseStep 842847 = 1264271) B1264271
theorem B3202163 : Blo 842353 3202163 := bstep (se 1 (by rfl) ⟨2401622, by rfl⟩ : syracuseStep 3202163 = 4803245) B4803245
theorem B842875 : Blo 842353 842875 := bstep (se 1 (by rfl) ⟨632156, by rfl⟩ : syracuseStep 842875 = 1264313) B1264313
theorem B842927 : Blo 842353 842927 := bstep (se 1 (by rfl) ⟨632195, by rfl⟩ : syracuseStep 842927 = 1264391) B1264391
theorem B842951 : Blo 842353 842951 := bstep (se 1 (by rfl) ⟨632213, by rfl⟩ : syracuseStep 842951 = 1264427) B1264427
theorem B842971 : Blo 842353 842971 := bstep (se 1 (by rfl) ⟨632228, by rfl⟩ : syracuseStep 842971 = 1264457) B1264457
theorem B843047 : Blo 842353 843047 := bstep (se 1 (by rfl) ⟨632285, by rfl⟩ : syracuseStep 843047 = 1264571) B1264571
theorem B843087 : Blo 842353 843087 := bstep (se 1 (by rfl) ⟨632315, by rfl⟩ : syracuseStep 843087 = 1264631) B1264631
theorem B843103 : Blo 842353 843103 := bstep (se 1 (by rfl) ⟨632327, by rfl⟩ : syracuseStep 843103 = 1264655) B1264655
theorem B843131 : Blo 842353 843131 := bstep (se 1 (by rfl) ⟨632348, by rfl⟩ : syracuseStep 843131 = 1264697) B1264697
theorem B6413741 : Blo 842353 6413741 := bstep (se 3 (by rfl) ⟨1202576, by rfl⟩ : syracuseStep 6413741 = 2405153) B2405153
theorem B843183 : Blo 842353 843183 := bstep (se 1 (by rfl) ⟨632387, by rfl⟩ : syracuseStep 843183 = 1264775) B1264775
theorem B1269167 : Blo 842353 1269167 := bstep (se 1 (by rfl) ⟨951875, by rfl⟩ : syracuseStep 1269167 = 1903751) B1903751
theorem B843207 : Blo 842353 843207 := bstep (se 1 (by rfl) ⟨632405, by rfl⟩ : syracuseStep 843207 = 1264811) B1264811
theorem B5397961 : Blo 842353 5397961 := bstep (se 2 (by rfl) ⟨2024235, by rfl⟩ : syracuseStep 5397961 = 4048471) B4048471
theorem B843227 : Blo 842353 843227 := bstep (se 1 (by rfl) ⟨632420, by rfl⟩ : syracuseStep 843227 = 1264841) B1264841
theorem B1269257 : Blo 842353 1269257 := bstep (se 2 (by rfl) ⟨475971, by rfl⟩ : syracuseStep 1269257 = 951943) B951943
theorem B843303 : Blo 842353 843303 := bstep (se 1 (by rfl) ⟨632477, by rfl⟩ : syracuseStep 843303 = 1264955) B1264955
theorem B1269287 : Blo 842353 1269287 := bstep (se 1 (by rfl) ⟨951965, by rfl⟩ : syracuseStep 1269287 = 1903931) B1903931
theorem B843343 : Blo 842353 843343 := bstep (se 1 (by rfl) ⟨632507, by rfl⟩ : syracuseStep 843343 = 1265015) B1265015
theorem B843359 : Blo 842353 843359 := bstep (se 1 (by rfl) ⟨632519, by rfl⟩ : syracuseStep 843359 = 1265039) B1265039
theorem B843387 : Blo 842353 843387 := bstep (se 1 (by rfl) ⟨632540, by rfl⟩ : syracuseStep 843387 = 1265081) B1265081
theorem B1269371 : Blo 842353 1269371 := bstep (se 1 (by rfl) ⟨952028, by rfl⟩ : syracuseStep 1269371 = 1904057) B1904057
theorem B5136011 : Blo 842353 5136011 := bstep (se 1 (by rfl) ⟨3852008, by rfl⟩ : syracuseStep 5136011 = 7704017) B7704017
theorem B843439 : Blo 842353 843439 := bstep (se 1 (by rfl) ⟨632579, by rfl⟩ : syracuseStep 843439 = 1265159) B1265159
theorem B843463 : Blo 842353 843463 := bstep (se 1 (by rfl) ⟨632597, by rfl⟩ : syracuseStep 843463 = 1265195) B1265195
theorem B843483 : Blo 842353 843483 := bstep (se 1 (by rfl) ⟨632612, by rfl⟩ : syracuseStep 843483 = 1265225) B1265225
theorem B1269497 : Blo 842353 1269497 := bstep (se 2 (by rfl) ⟨476061, by rfl⟩ : syracuseStep 1269497 = 952123) B952123
theorem B843559 : Blo 842353 843559 := bstep (se 1 (by rfl) ⟨632669, by rfl⟩ : syracuseStep 843559 = 1265339) B1265339
theorem B843599 : Blo 842353 843599 := bstep (se 1 (by rfl) ⟨632699, by rfl⟩ : syracuseStep 843599 = 1265399) B1265399
theorem B843615 : Blo 842353 843615 := bstep (se 1 (by rfl) ⟨632711, by rfl⟩ : syracuseStep 843615 = 1265423) B1265423
theorem B1204075 : Blo 842353 1204075 := bstep (se 1 (by rfl) ⟨903056, by rfl⟩ : syracuseStep 1204075 = 1806113) B1806113
theorem B843643 : Blo 842353 843643 := bstep (se 1 (by rfl) ⟨632732, by rfl⟩ : syracuseStep 843643 = 1265465) B1265465
theorem B843695 : Blo 842353 843695 := bstep (se 1 (by rfl) ⟨632771, by rfl⟩ : syracuseStep 843695 = 1265543) B1265543
theorem B7200697 : Blo 842353 7200697 := bstep (se 2 (by rfl) ⟨2700261, by rfl⟩ : syracuseStep 7200697 = 5400523) B5400523
theorem B843719 : Blo 842353 843719 := bstep (se 1 (by rfl) ⟨632789, by rfl⟩ : syracuseStep 843719 = 1265579) B1265579
theorem B843739 : Blo 842353 843739 := bstep (se 1 (by rfl) ⟨632804, by rfl⟩ : syracuseStep 843739 = 1265609) B1265609
theorem B843815 : Blo 842353 843815 := bstep (se 1 (by rfl) ⟨632861, by rfl⟩ : syracuseStep 843815 = 1265723) B1265723
theorem B843855 : Blo 842353 843855 := bstep (se 1 (by rfl) ⟨632891, by rfl⟩ : syracuseStep 843855 = 1265783) B1265783
theorem B1204303 : Blo 842353 1204303 := bstep (se 1 (by rfl) ⟨903227, by rfl⟩ : syracuseStep 1204303 = 1806455) B1806455
theorem B843871 : Blo 842353 843871 := bstep (se 1 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 843871 = 1265807) B1265807
theorem B9625715 : Blo 842353 9625715 := bstep (se 1 (by rfl) ⟨7219286, by rfl⟩ : syracuseStep 9625715 = 14438573) B14438573
theorem B843899 : Blo 842353 843899 := bstep (se 1 (by rfl) ⟨632924, by rfl⟩ : syracuseStep 843899 = 1265849) B1265849
theorem B843951 : Blo 842353 843951 := bstep (se 1 (by rfl) ⟨632963, by rfl⟩ : syracuseStep 843951 = 1265927) B1265927
theorem B843975 : Blo 842353 843975 := bstep (se 1 (by rfl) ⟨632981, by rfl⟩ : syracuseStep 843975 = 1265963) B1265963
theorem B843995 : Blo 842353 843995 := bstep (se 1 (by rfl) ⟨632996, by rfl⟩ : syracuseStep 843995 = 1265993) B1265993
theorem B844071 : Blo 842353 844071 := bstep (se 1 (by rfl) ⟨633053, by rfl⟩ : syracuseStep 844071 = 1266107) B1266107
theorem B844111 : Blo 842353 844111 := bstep (se 1 (by rfl) ⟨633083, by rfl⟩ : syracuseStep 844111 = 1266167) B1266167
theorem B844127 : Blo 842353 844127 := bstep (se 1 (by rfl) ⟨633095, by rfl⟩ : syracuseStep 844127 = 1266191) B1266191
theorem B844155 : Blo 842353 844155 := bstep (se 1 (by rfl) ⟨633116, by rfl⟩ : syracuseStep 844155 = 1266233) B1266233
theorem B844207 : Blo 842353 844207 := bstep (se 1 (by rfl) ⟨633155, by rfl⟩ : syracuseStep 844207 = 1266311) B1266311
theorem B844231 : Blo 842353 844231 := bstep (se 1 (by rfl) ⟨633173, by rfl⟩ : syracuseStep 844231 = 1266347) B1266347
theorem B2843099 : Blo 842353 2843099 := bstep (se 1 (by rfl) ⟨2132324, by rfl⟩ : syracuseStep 2843099 = 4264649) B4264649
theorem B844251 : Blo 842353 844251 := bstep (se 1 (by rfl) ⟨633188, by rfl⟩ : syracuseStep 844251 = 1266377) B1266377
theorem B844327 : Blo 842353 844327 := bstep (se 1 (by rfl) ⟨633245, by rfl⟩ : syracuseStep 844327 = 1266491) B1266491
theorem B844367 : Blo 842353 844367 := bstep (se 1 (by rfl) ⟨633275, by rfl⟩ : syracuseStep 844367 = 1266551) B1266551
theorem B844383 : Blo 842353 844383 := bstep (se 1 (by rfl) ⟨633287, by rfl⟩ : syracuseStep 844383 = 1266575) B1266575
theorem B844411 : Blo 842353 844411 := bstep (se 1 (by rfl) ⟨633308, by rfl⟩ : syracuseStep 844411 = 1266617) B1266617
theorem B844463 : Blo 842353 844463 := bstep (se 1 (by rfl) ⟨633347, by rfl⟩ : syracuseStep 844463 = 1266695) B1266695
theorem B844487 : Blo 842353 844487 := bstep (se 1 (by rfl) ⟨633365, by rfl⟩ : syracuseStep 844487 = 1266731) B1266731
theorem B844507 : Blo 842353 844507 := bstep (se 1 (by rfl) ⟨633380, by rfl⟩ : syracuseStep 844507 = 1266761) B1266761
theorem B3203833 : Blo 842353 3203833 := bstep (se 2 (by rfl) ⟨1201437, by rfl⟩ : syracuseStep 3203833 = 2402875) B2402875
theorem B5137181 : Blo 842353 5137181 := bstep (se 3 (by rfl) ⟨963221, by rfl⟩ : syracuseStep 5137181 = 1926443) B1926443
theorem B844583 : Blo 842353 844583 := bstep (se 1 (by rfl) ⟨633437, by rfl⟩ : syracuseStep 844583 = 1266875) B1266875
theorem B844623 : Blo 842353 844623 := bstep (se 1 (by rfl) ⟨633467, by rfl⟩ : syracuseStep 844623 = 1266935) B1266935
theorem B844639 : Blo 842353 844639 := bstep (se 1 (by rfl) ⟨633479, by rfl⟩ : syracuseStep 844639 = 1266959) B1266959
theorem B844667 : Blo 842353 844667 := bstep (se 1 (by rfl) ⟨633500, by rfl⟩ : syracuseStep 844667 = 1267001) B1267001
theorem B844719 : Blo 842353 844719 := bstep (se 1 (by rfl) ⟨633539, by rfl⟩ : syracuseStep 844719 = 1267079) B1267079
theorem B844743 : Blo 842353 844743 := bstep (se 1 (by rfl) ⟨633557, by rfl⟩ : syracuseStep 844743 = 1267115) B1267115
theorem B844763 : Blo 842353 844763 := bstep (se 1 (by rfl) ⟨633572, by rfl⟩ : syracuseStep 844763 = 1267145) B1267145
theorem B4056065 : Blo 842353 4056065 := bstep (se 2 (by rfl) ⟨1521024, by rfl⟩ : syracuseStep 4056065 = 3042049) B3042049
theorem B844839 : Blo 842353 844839 := bstep (se 1 (by rfl) ⟨633629, by rfl⟩ : syracuseStep 844839 = 1267259) B1267259
theorem B844879 : Blo 842353 844879 := bstep (se 1 (by rfl) ⟨633659, by rfl⟩ : syracuseStep 844879 = 1267319) B1267319
theorem B844895 : Blo 842353 844895 := bstep (se 1 (by rfl) ⟨633671, by rfl⟩ : syracuseStep 844895 = 1267343) B1267343
theorem B844923 : Blo 842353 844923 := bstep (se 1 (by rfl) ⟨633692, by rfl⟩ : syracuseStep 844923 = 1267385) B1267385
theorem B2843801 : Blo 842353 2843801 := bstep (se 2 (by rfl) ⟨1066425, by rfl⟩ : syracuseStep 2843801 = 2132851) B2132851
theorem B844975 : Blo 842353 844975 := bstep (se 1 (by rfl) ⟨633731, by rfl⟩ : syracuseStep 844975 = 1267463) B1267463
theorem B844999 : Blo 842353 844999 := bstep (se 1 (by rfl) ⟨633749, by rfl⟩ : syracuseStep 844999 = 1267499) B1267499
theorem B16442585 : Blo 842353 16442585 := bstep (se 2 (by rfl) ⟨6165969, by rfl⟩ : syracuseStep 16442585 = 12331939) B12331939
theorem B845019 : Blo 842353 845019 := bstep (se 1 (by rfl) ⟨633764, by rfl⟩ : syracuseStep 845019 = 1267529) B1267529
theorem B845095 : Blo 842353 845095 := bstep (se 1 (by rfl) ⟨633821, by rfl⟩ : syracuseStep 845095 = 1267643) B1267643
theorem B845135 : Blo 842353 845135 := bstep (se 1 (by rfl) ⟨633851, by rfl⟩ : syracuseStep 845135 = 1267703) B1267703
theorem B845151 : Blo 842353 845151 := bstep (se 1 (by rfl) ⟨633863, by rfl⟩ : syracuseStep 845151 = 1267727) B1267727
theorem B845179 : Blo 842353 845179 := bstep (se 1 (by rfl) ⟨633884, by rfl⟩ : syracuseStep 845179 = 1267769) B1267769
theorem B845231 : Blo 842353 845231 := bstep (se 1 (by rfl) ⟨633923, by rfl⟩ : syracuseStep 845231 = 1267847) B1267847
theorem B845255 : Blo 842353 845255 := bstep (se 1 (by rfl) ⟨633941, by rfl⟩ : syracuseStep 845255 = 1267883) B1267883
theorem B845275 : Blo 842353 845275 := bstep (se 1 (by rfl) ⟨633956, by rfl⟩ : syracuseStep 845275 = 1267913) B1267913
theorem B845351 : Blo 842353 845351 := bstep (se 1 (by rfl) ⟨634013, by rfl⟩ : syracuseStep 845351 = 1268027) B1268027
theorem B845391 : Blo 842353 845391 := bstep (se 1 (by rfl) ⟨634043, by rfl⟩ : syracuseStep 845391 = 1268087) B1268087
theorem B845407 : Blo 842353 845407 := bstep (se 1 (by rfl) ⟨634055, by rfl⟩ : syracuseStep 845407 = 1268111) B1268111
theorem B845435 : Blo 842353 845435 := bstep (se 1 (by rfl) ⟨634076, by rfl⟩ : syracuseStep 845435 = 1268153) B1268153
theorem B845487 : Blo 842353 845487 := bstep (se 1 (by rfl) ⟨634115, by rfl⟩ : syracuseStep 845487 = 1268231) B1268231
theorem B845511 : Blo 842353 845511 := bstep (se 1 (by rfl) ⟨634133, by rfl⟩ : syracuseStep 845511 = 1268267) B1268267
theorem B845531 : Blo 842353 845531 := bstep (se 1 (by rfl) ⟨634148, by rfl⟩ : syracuseStep 845531 = 1268297) B1268297
theorem B845607 : Blo 842353 845607 := bstep (se 1 (by rfl) ⟨634205, by rfl⟩ : syracuseStep 845607 = 1268411) B1268411
theorem B6416171 : Blo 842353 6416171 := bstep (se 1 (by rfl) ⟨4812128, by rfl⟩ : syracuseStep 6416171 = 9624257) B9624257
theorem B845647 : Blo 842353 845647 := bstep (se 1 (by rfl) ⟨634235, by rfl⟩ : syracuseStep 845647 = 1268471) B1268471
theorem B845663 : Blo 842353 845663 := bstep (se 1 (by rfl) ⟨634247, by rfl⟩ : syracuseStep 845663 = 1268495) B1268495
theorem B845691 : Blo 842353 845691 := bstep (se 1 (by rfl) ⟨634268, by rfl⟩ : syracuseStep 845691 = 1268537) B1268537
theorem B845743 : Blo 842353 845743 := bstep (se 1 (by rfl) ⟨634307, by rfl⟩ : syracuseStep 845743 = 1268615) B1268615
theorem B1599419 : Blo 842353 1599419 := bstep (se 1 (by rfl) ⟨1199564, by rfl⟩ : syracuseStep 1599419 = 2399129) B2399129
theorem B845767 : Blo 842353 845767 := bstep (se 1 (by rfl) ⟨634325, by rfl⟩ : syracuseStep 845767 = 1268651) B1268651
theorem B845787 : Blo 842353 845787 := bstep (se 1 (by rfl) ⟨634340, by rfl⟩ : syracuseStep 845787 = 1268681) B1268681
theorem B845863 : Blo 842353 845863 := bstep (se 1 (by rfl) ⟨634397, by rfl⟩ : syracuseStep 845863 = 1268795) B1268795
theorem B845903 : Blo 842353 845903 := bstep (se 1 (by rfl) ⟨634427, by rfl⟩ : syracuseStep 845903 = 1268855) B1268855
theorem B845919 : Blo 842353 845919 := bstep (se 1 (by rfl) ⟨634439, by rfl⟩ : syracuseStep 845919 = 1268879) B1268879
theorem B845947 : Blo 842353 845947 := bstep (se 1 (by rfl) ⟨634460, by rfl⟩ : syracuseStep 845947 = 1268921) B1268921
theorem B3205277 : Blo 842353 3205277 := bstep (se 3 (by rfl) ⟨600989, by rfl⟩ : syracuseStep 3205277 = 1201979) B1201979
theorem B3205291 : Blo 842353 3205291 := bstep (se 1 (by rfl) ⟨2403968, by rfl⟩ : syracuseStep 3205291 = 4807937) B4807937
theorem B845999 : Blo 842353 845999 := bstep (se 1 (by rfl) ⟨634499, by rfl⟩ : syracuseStep 845999 = 1268999) B1268999
theorem B846023 : Blo 842353 846023 := bstep (se 1 (by rfl) ⟨634517, by rfl⟩ : syracuseStep 846023 = 1269035) B1269035
theorem B846043 : Blo 842353 846043 := bstep (se 1 (by rfl) ⟨634532, by rfl⟩ : syracuseStep 846043 = 1269065) B1269065
theorem B846119 : Blo 842353 846119 := bstep (se 1 (by rfl) ⟨634589, by rfl⟩ : syracuseStep 846119 = 1269179) B1269179
theorem B2844989 : Blo 842353 2844989 := bstep (se 3 (by rfl) ⟨533435, by rfl⟩ : syracuseStep 2844989 = 1066871) B1066871
theorem B846159 : Blo 842353 846159 := bstep (se 1 (by rfl) ⟨634619, by rfl⟩ : syracuseStep 846159 = 1269239) B1269239
theorem B846175 : Blo 842353 846175 := bstep (se 1 (by rfl) ⟨634631, by rfl⟩ : syracuseStep 846175 = 1269263) B1269263
theorem B1599851 : Blo 842353 1599851 := bstep (se 1 (by rfl) ⟨1199888, by rfl⟩ : syracuseStep 1599851 = 2399777) B2399777
theorem B846203 : Blo 842353 846203 := bstep (se 1 (by rfl) ⟨634652, by rfl⟩ : syracuseStep 846203 = 1269305) B1269305
theorem B1599905 : Blo 842353 1599905 := bstep (se 2 (by rfl) ⟨599964, by rfl⟩ : syracuseStep 1599905 = 1199929) B1199929
theorem B846255 : Blo 842353 846255 := bstep (se 1 (by rfl) ⟨634691, by rfl⟩ : syracuseStep 846255 = 1269383) B1269383
theorem B846279 : Blo 842353 846279 := bstep (se 1 (by rfl) ⟨634709, by rfl⟩ : syracuseStep 846279 = 1269419) B1269419
theorem B3205595 : Blo 842353 3205595 := bstep (se 1 (by rfl) ⟨2404196, by rfl⟩ : syracuseStep 3205595 = 4808393) B4808393
theorem B846299 : Blo 842353 846299 := bstep (se 1 (by rfl) ⟨634724, by rfl⟩ : syracuseStep 846299 = 1269449) B1269449
theorem B2026081 : Blo 842353 2026081 := bstep (se 2 (by rfl) ⟨759780, by rfl⟩ : syracuseStep 2026081 = 1519561) B1519561
theorem B3042323 : Blo 842353 3042323 := bstep (se 1 (by rfl) ⟨2281742, by rfl⟩ : syracuseStep 3042323 = 4563485) B4563485
theorem B2845853 : Blo 842353 2845853 := bstep (se 3 (by rfl) ⟨533597, by rfl⟩ : syracuseStep 2845853 = 1067195) B1067195
theorem B1895975 : Blo 842353 1895975 := bstep (se 1 (by rfl) ⟨1421981, by rfl⟩ : syracuseStep 1895975 = 2843963) B2843963
theorem B10284677 : Blo 842353 10284677 := bstep (se 4 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 10284677 = 1928377) B1928377
theorem B9596555 : Blo 842353 9596555 := bstep (se 1 (by rfl) ⟨7197416, by rfl⟩ : syracuseStep 9596555 = 14394833) B14394833
theorem B2846393 : Blo 842353 2846393 := bstep (se 2 (by rfl) ⟨1067397, by rfl⟩ : syracuseStep 2846393 = 2134795) B2134795
theorem B19787453 : Blo 842353 19787453 := bstep (se 3 (by rfl) ⟨3710147, by rfl⟩ : syracuseStep 19787453 = 7420295) B7420295
theorem B16215875 : Blo 842353 16215875 := bstep (se 1 (by rfl) ⟨12161906, by rfl⟩ : syracuseStep 16215875 = 24323813) B24323813
theorem B1896299 : Blo 842353 1896299 := bstep (se 1 (by rfl) ⟨1422224, by rfl⟩ : syracuseStep 1896299 = 2844449) B2844449
theorem B3600247 : Blo 842353 3600247 := bstep (se 1 (by rfl) ⟨2700185, by rfl⟩ : syracuseStep 3600247 = 5400371) B5400371
theorem B1896353 : Blo 842353 1896353 := bstep (se 2 (by rfl) ⟨711132, by rfl⟩ : syracuseStep 1896353 = 1422265) B1422265
theorem B1601545 : Blo 842353 1601545 := bstep (se 2 (by rfl) ⟨600579, by rfl⟩ : syracuseStep 1601545 = 1201159) B1201159
theorem B15396875 : Blo 842353 15396875 := bstep (se 1 (by rfl) ⟨11547656, by rfl⟩ : syracuseStep 15396875 = 23095313) B23095313
theorem B38957233 : Blo 842353 38957233 := bstep (se 2 (by rfl) ⟨14608962, by rfl⟩ : syracuseStep 38957233 = 29217925) B29217925
theorem B1896695 : Blo 842353 1896695 := bstep (se 1 (by rfl) ⟨1422521, by rfl⟩ : syracuseStep 1896695 = 2845043) B2845043
theorem B10809611 : Blo 842353 10809611 := bstep (se 1 (by rfl) ⟨8107208, by rfl⟩ : syracuseStep 10809611 = 16214417) B16214417
theorem B2846987 : Blo 842353 2846987 := bstep (se 1 (by rfl) ⟨2135240, by rfl⟩ : syracuseStep 2846987 = 4270481) B4270481
theorem B2847257 : Blo 842353 2847257 := bstep (se 2 (by rfl) ⟨1067721, by rfl⟩ : syracuseStep 2847257 = 2135443) B2135443
theorem B13693697 : Blo 842353 13693697 := bstep (se 2 (by rfl) ⟨5135136, by rfl⟩ : syracuseStep 13693697 = 10270273) B10270273
theorem B19460881 : Blo 842353 19460881 := bstep (se 2 (by rfl) ⟨7297830, by rfl⟩ : syracuseStep 19460881 = 14595661) B14595661
theorem B1897289 : Blo 842353 1897289 := bstep (se 2 (by rfl) ⟨711483, by rfl⟩ : syracuseStep 1897289 = 1422967) B1422967
theorem B1602479 : Blo 842353 1602479 := bstep (se 1 (by rfl) ⟨1201859, by rfl⟩ : syracuseStep 1602479 = 2403719) B2403719
theorem B3208193 : Blo 842353 3208193 := bstep (se 2 (by rfl) ⟨1203072, by rfl⟩ : syracuseStep 3208193 = 2406145) B2406145
theorem B3208207 : Blo 842353 3208207 := bstep (se 1 (by rfl) ⟨2406155, by rfl⟩ : syracuseStep 3208207 = 4812311) B4812311
theorem B3601579 : Blo 842353 3601579 := bstep (se 1 (by rfl) ⟨2701184, by rfl⟩ : syracuseStep 3601579 = 5402369) B5402369
theorem B1603003 : Blo 842353 1603003 := bstep (se 1 (by rfl) ⟨1202252, by rfl⟩ : syracuseStep 1603003 = 2404505) B2404505
theorem B1898081 : Blo 842353 1898081 := bstep (se 2 (by rfl) ⟨711780, by rfl⟩ : syracuseStep 1898081 = 1423561) B1423561
theorem B2848391 : Blo 842353 2848391 := bstep (se 1 (by rfl) ⟨2136293, by rfl⟩ : syracuseStep 2848391 = 4272587) B4272587
theorem B2848445 : Blo 842353 2848445 := bstep (se 3 (by rfl) ⟨534083, by rfl⟩ : syracuseStep 2848445 = 1068167) B1068167
theorem B947911 : Blo 842353 947911 := bstep (se 1 (by rfl) ⟨710933, by rfl⟩ : syracuseStep 947911 = 1421867) B1421867
theorem B9631547 : Blo 842353 9631547 := bstep (se 1 (by rfl) ⟨7223660, by rfl⟩ : syracuseStep 9631547 = 14447321) B14447321
theorem B2848607 : Blo 842353 2848607 := bstep (se 1 (by rfl) ⟨2136455, by rfl⟩ : syracuseStep 2848607 = 4272911) B4272911
theorem B1603489 : Blo 842353 1603489 := bstep (se 2 (by rfl) ⟨601308, by rfl⟩ : syracuseStep 1603489 = 1202617) B1202617
theorem B1898423 : Blo 842353 1898423 := bstep (se 1 (by rfl) ⟨1423817, by rfl⟩ : syracuseStep 1898423 = 2847635) B2847635
theorem B2848769 : Blo 842353 2848769 := bstep (se 2 (by rfl) ⟨1068288, by rfl⟩ : syracuseStep 2848769 = 2136577) B2136577
theorem B18249785 : Blo 842353 18249785 := bstep (se 2 (by rfl) ⟨6843669, by rfl⟩ : syracuseStep 18249785 = 13687339) B13687339
theorem B3209483 : Blo 842353 3209483 := bstep (se 1 (by rfl) ⟨2407112, by rfl⟩ : syracuseStep 3209483 = 4814225) B4814225
theorem B3045869 : Blo 842353 3045869 := bstep (se 3 (by rfl) ⟨571100, by rfl⟩ : syracuseStep 3045869 = 1142201) B1142201
theorem B1899017 : Blo 842353 1899017 := bstep (se 2 (by rfl) ⟨712131, by rfl⟩ : syracuseStep 1899017 = 1424263) B1424263
theorem B948775 : Blo 842353 948775 := bstep (se 1 (by rfl) ⟨711581, by rfl⟩ : syracuseStep 948775 = 1423163) B1423163
theorem B3046099 : Blo 842353 3046099 := bstep (se 1 (by rfl) ⟨2284574, by rfl⟩ : syracuseStep 3046099 = 4569149) B4569149
theorem B3209939 : Blo 842353 3209939 := bstep (se 1 (by rfl) ⟨2407454, by rfl⟩ : syracuseStep 3209939 = 4814909) B4814909
theorem B2849579 : Blo 842353 2849579 := bstep (se 1 (by rfl) ⟨2137184, by rfl⟩ : syracuseStep 2849579 = 4274369) B4274369
theorem B1801055 : Blo 842353 1801055 := bstep (se 1 (by rfl) ⟨1350791, by rfl⟩ : syracuseStep 1801055 = 2701583) B2701583
theorem B1899359 : Blo 842353 1899359 := bstep (se 1 (by rfl) ⟨1424519, by rfl⟩ : syracuseStep 1899359 = 2849039) B2849039
theorem B2030599 : Blo 842353 2030599 := bstep (se 1 (by rfl) ⟨1522949, by rfl⟩ : syracuseStep 2030599 = 3045899) B3045899
theorem B1899539 : Blo 842353 1899539 := bstep (se 1 (by rfl) ⟨1424654, by rfl⟩ : syracuseStep 1899539 = 2849309) B2849309
theorem B2849849 : Blo 842353 2849849 := bstep (se 2 (by rfl) ⟨1068693, by rfl⟩ : syracuseStep 2849849 = 2137387) B2137387
theorem B1899881 : Blo 842353 1899881 := bstep (se 2 (by rfl) ⟨712455, by rfl⟩ : syracuseStep 1899881 = 1424911) B1424911
theorem B2850173 : Blo 842353 2850173 := bstep (se 3 (by rfl) ⟨534407, by rfl⟩ : syracuseStep 2850173 = 1068815) B1068815
theorem B6422003 : Blo 842353 6422003 := bstep (se 1 (by rfl) ⟨4816502, by rfl⟩ : syracuseStep 6422003 = 9633005) B9633005
theorem B2850443 : Blo 842353 2850443 := bstep (se 1 (by rfl) ⟨2137832, by rfl⟩ : syracuseStep 2850443 = 4275665) B4275665
theorem B3210941 : Blo 842353 3210941 := bstep (se 3 (by rfl) ⟨602051, by rfl⟩ : syracuseStep 3210941 = 1204103) B1204103
theorem B3079889 : Blo 842353 3079889 := bstep (se 2 (by rfl) ⟨1154958, by rfl⟩ : syracuseStep 3079889 = 2309917) B2309917
theorem B1900475 : Blo 842353 1900475 := bstep (se 1 (by rfl) ⟨1425356, by rfl⟩ : syracuseStep 1900475 = 2850713) B2850713
theorem B2850875 : Blo 842353 2850875 := bstep (se 1 (by rfl) ⟨2138156, by rfl⟩ : syracuseStep 2850875 = 4276313) B4276313
theorem B1605737 : Blo 842353 1605737 := bstep (se 2 (by rfl) ⟨602151, by rfl⟩ : syracuseStep 1605737 = 1204303) B1204303
theorem B2851145 : Blo 842353 2851145 := bstep (se 2 (by rfl) ⟨1069179, by rfl⟩ : syracuseStep 2851145 = 2138359) B2138359
theorem B2195819 : Blo 842353 2195819 := bstep (se 1 (by rfl) ⟨1646864, by rfl⟩ : syracuseStep 2195819 = 3293729) B3293729
theorem B1900907 : Blo 842353 1900907 := bstep (se 1 (by rfl) ⟨1425680, by rfl⟩ : syracuseStep 1900907 = 2851361) B2851361
theorem B1737071 : Blo 842353 1737071 := bstep (se 1 (by rfl) ⟨1302803, by rfl⟩ : syracuseStep 1737071 = 2605607) B2605607
theorem B1901051 : Blo 842353 1901051 := bstep (se 1 (by rfl) ⟨1425788, by rfl⟩ : syracuseStep 1901051 = 2851577) B2851577
theorem B1606139 : Blo 842353 1606139 := bstep (se 1 (by rfl) ⟨1204604, by rfl⟩ : syracuseStep 1606139 = 2409209) B2409209
theorem B1901177 : Blo 842353 1901177 := bstep (se 2 (by rfl) ⟨712941, by rfl⟩ : syracuseStep 1901177 = 1425883) B1425883
theorem B1901231 : Blo 842353 1901231 := bstep (se 1 (by rfl) ⟨1425923, by rfl⟩ : syracuseStep 1901231 = 2851847) B2851847
theorem B951007 : Blo 842353 951007 := bstep (se 1 (by rfl) ⟨713255, by rfl⟩ : syracuseStep 951007 = 1426511) B1426511
theorem B1606367 : Blo 842353 1606367 := bstep (se 1 (by rfl) ⟨1204775, by rfl⟩ : syracuseStep 1606367 = 2409551) B2409551
theorem B1901303 : Blo 842353 1901303 := bstep (se 1 (by rfl) ⟨1425977, by rfl⟩ : syracuseStep 1901303 = 2851955) B2851955
theorem B1016731 : Blo 842353 1016731 := bstep (se 1 (by rfl) ⟨762548, by rfl⟩ : syracuseStep 1016731 = 1525097) B1525097
theorem B4817825 : Blo 842353 4817825 := bstep (se 2 (by rfl) ⟨1806684, by rfl⟩ : syracuseStep 4817825 = 3613369) B3613369
theorem B1901483 : Blo 842353 1901483 := bstep (se 1 (by rfl) ⟨1426112, by rfl⟩ : syracuseStep 1901483 = 2852225) B2852225
theorem B15598657 : Blo 842353 15598657 := bstep (se 2 (by rfl) ⟨5849496, by rfl⟩ : syracuseStep 15598657 = 11698993) B11698993
theorem B951583 : Blo 842353 951583 := bstep (se 1 (by rfl) ⟨713687, by rfl⟩ : syracuseStep 951583 = 1427375) B1427375
theorem B1902023 : Blo 842353 1902023 := bstep (se 1 (by rfl) ⟨1426517, by rfl⟩ : syracuseStep 1902023 = 2853035) B2853035
theorem B951871 : Blo 842353 951871 := bstep (se 1 (by rfl) ⟨713903, by rfl⟩ : syracuseStep 951871 = 1427807) B1427807
theorem B2033387 : Blo 842353 2033387 := bstep (se 1 (by rfl) ⟨1525040, by rfl⟩ : syracuseStep 2033387 = 3050081) B3050081
theorem B1902383 : Blo 842353 1902383 := bstep (se 1 (by rfl) ⟨1426787, by rfl⟩ : syracuseStep 1902383 = 2853575) B2853575
theorem B4065079 : Blo 842353 4065079 := bstep (se 1 (by rfl) ⟨3048809, by rfl⟩ : syracuseStep 4065079 = 6097619) B6097619
theorem B36571013 : Blo 842353 36571013 := bstep (se 4 (by rfl) ⟨3428532, by rfl⟩ : syracuseStep 36571013 = 6857065) B6857065
theorem B9635921 : Blo 842353 9635921 := bstep (se 2 (by rfl) ⟨3613470, by rfl⟩ : syracuseStep 9635921 = 7226941) B7226941
theorem B16255241 : Blo 842353 16255241 := bstep (se 2 (by rfl) ⟨6095715, by rfl⟩ : syracuseStep 16255241 = 12191431) B12191431
theorem B2132315 : Blo 842353 2132315 := bstep (se 1 (by rfl) ⟨1599236, by rfl⟩ : syracuseStep 2132315 = 3198473) B3198473
theorem B1902959 : Blo 842353 1902959 := bstep (se 1 (by rfl) ⟨1427219, by rfl⟩ : syracuseStep 1902959 = 2854439) B2854439
theorem B1903031 : Blo 842353 1903031 := bstep (se 1 (by rfl) ⟨1427273, by rfl⟩ : syracuseStep 1903031 = 2854547) B2854547
theorem B4393511 : Blo 842353 4393511 := bstep (se 1 (by rfl) ⟨3295133, by rfl⟩ : syracuseStep 4393511 = 6590267) B6590267
theorem B1903175 : Blo 842353 1903175 := bstep (se 1 (by rfl) ⟨1427381, by rfl⟩ : syracuseStep 1903175 = 2854763) B2854763
theorem B1903211 : Blo 842353 1903211 := bstep (se 1 (by rfl) ⟨1427408, by rfl⟩ : syracuseStep 1903211 = 2854817) B2854817
theorem B1903607 : Blo 842353 1903607 := bstep (se 1 (by rfl) ⟨1427705, by rfl⟩ : syracuseStep 1903607 = 2855411) B2855411
theorem B4885543 : Blo 842353 4885543 := bstep (se 1 (by rfl) ⟨3664157, by rfl⟩ : syracuseStep 4885543 = 7328315) B7328315
theorem B4066523 : Blo 842353 4066523 := bstep (se 1 (by rfl) ⟨3049892, by rfl⟩ : syracuseStep 4066523 = 6099785) B6099785
theorem B2133287 : Blo 842353 2133287 := bstep (se 1 (by rfl) ⟨1599965, by rfl⟩ : syracuseStep 2133287 = 3199931) B3199931
theorem B1903967 : Blo 842353 1903967 := bstep (se 1 (by rfl) ⟨1427975, by rfl⟩ : syracuseStep 1903967 = 2855951) B2855951
theorem B2166203 : Blo 842353 2166203 := bstep (se 1 (by rfl) ⟨1624652, by rfl⟩ : syracuseStep 2166203 = 3249305) B3249305
theorem B2854331 : Blo 842353 2854331 := bstep (se 1 (by rfl) ⟨2140748, by rfl⟩ : syracuseStep 2854331 = 4281497) B4281497
theorem B855775 : Blo 842353 855775 := bstep (se 1 (by rfl) ⟨641831, by rfl⟩ : syracuseStep 855775 = 1283663) B1283663
theorem B3248029 : Blo 842353 3248029 := bstep (se 3 (by rfl) ⟨609005, by rfl⟩ : syracuseStep 3248029 = 1218011) B1218011
theorem B5640623 : Blo 842353 5640623 := bstep (se 1 (by rfl) ⟨4230467, by rfl⟩ : syracuseStep 5640623 = 8460935) B8460935
theorem B2134775 : Blo 842353 2134775 := bstep (se 1 (by rfl) ⟨1601081, by rfl⟩ : syracuseStep 2134775 = 3202163) B3202163
theorem B2135393 : Blo 842353 2135393 := bstep (se 2 (by rfl) ⟨800772, by rfl⟩ : syracuseStep 2135393 = 1601545) B1601545
theorem B51942977 : Blo 842353 51942977 := bstep (se 2 (by rfl) ⟨19478616, by rfl⟩ : syracuseStep 51942977 = 38957233) B38957233
theorem B6166201 : Blo 842353 6166201 := bstep (se 2 (by rfl) ⟨2312325, by rfl⟩ : syracuseStep 6166201 = 4624651) B4624651
theorem B7214777 : Blo 842353 7214777 := bstep (se 2 (by rfl) ⟨2705541, by rfl⟩ : syracuseStep 7214777 = 5411083) B5411083
theorem B4331195 : Blo 842353 4331195 := bstep (se 1 (by rfl) ⟨3248396, by rfl⟩ : syracuseStep 4331195 = 6496793) B6496793
theorem B4265783 : Blo 842353 4265783 := bstep (se 1 (by rfl) ⟨3199337, by rfl⟩ : syracuseStep 4265783 = 6398675) B6398675
theorem B16685189 : Blo 842353 16685189 := bstep (se 4 (by rfl) ⟨1564236, by rfl⟩ : syracuseStep 16685189 = 3128473) B3128473
theorem B9115895 : Blo 842353 9115895 := bstep (se 1 (by rfl) ⟨6836921, by rfl⟩ : syracuseStep 9115895 = 13673843) B13673843
theorem B4266269 : Blo 842353 4266269 := bstep (se 3 (by rfl) ⟨799925, by rfl⟩ : syracuseStep 4266269 = 1599851) B1599851
theorem B5773963 : Blo 842353 5773963 := bstep (se 1 (by rfl) ⟨4330472, by rfl⟩ : syracuseStep 5773963 = 8660945) B8660945
theorem B2136851 : Blo 842353 2136851 := bstep (se 1 (by rfl) ⟨1602638, by rfl⟩ : syracuseStep 2136851 = 3205277) B3205277
theorem B2137063 : Blo 842353 2137063 := bstep (se 1 (by rfl) ⟨1602797, by rfl⟩ : syracuseStep 2137063 = 3205595) B3205595
theorem B3611729 : Blo 842353 3611729 := bstep (se 2 (by rfl) ⟨1354398, by rfl⟩ : syracuseStep 3611729 = 2708797) B2708797
theorem B12197081 : Blo 842353 12197081 := bstep (se 2 (by rfl) ⟨4573905, by rfl⟩ : syracuseStep 12197081 = 9147811) B9147811
theorem B8101093 : Blo 842353 8101093 := bstep (se 4 (by rfl) ⟨759477, by rfl⟩ : syracuseStep 8101093 = 1518955) B1518955
theorem B2137337 : Blo 842353 2137337 := bstep (se 2 (by rfl) ⟨801501, by rfl⟩ : syracuseStep 2137337 = 1603003) B1603003
theorem B6856451 : Blo 842353 6856451 := bstep (se 1 (by rfl) ⟨5142338, by rfl⟩ : syracuseStep 6856451 = 10284677) B10284677
theorem B6397703 : Blo 842353 6397703 := bstep (se 1 (by rfl) ⟨4798277, by rfl⟩ : syracuseStep 6397703 = 9596555) B9596555
theorem B9117535 : Blo 842353 9117535 := bstep (se 1 (by rfl) ⟨6838151, by rfl⟩ : syracuseStep 9117535 = 13676303) B13676303
theorem B2137985 : Blo 842353 2137985 := bstep (se 2 (by rfl) ⟨801744, by rfl⟩ : syracuseStep 2137985 = 1603489) B1603489
theorem B10264583 : Blo 842353 10264583 := bstep (se 1 (by rfl) ⟨7698437, by rfl⟩ : syracuseStep 10264583 = 15396875) B15396875
theorem B4268051 : Blo 842353 4268051 := bstep (se 1 (by rfl) ⟨3201038, by rfl⟩ : syracuseStep 4268051 = 6402077) B6402077
theorem B16261235 : Blo 842353 16261235 := bstep (se 1 (by rfl) ⟨12195926, by rfl⟩ : syracuseStep 16261235 = 24391853) B24391853
theorem B2138795 : Blo 842353 2138795 := bstep (se 1 (by rfl) ⟨1604096, by rfl⟩ : syracuseStep 2138795 = 3208193) B3208193
theorem B69215269 : Blo 842353 69215269 := bstep (se 4 (by rfl) ⟨6488931, by rfl⟩ : syracuseStep 69215269 = 12977863) B12977863
theorem B9118919 : Blo 842353 9118919 := bstep (se 1 (by rfl) ⟨6839189, by rfl⟩ : syracuseStep 9118919 = 13678379) B13678379
theorem B12166523 : Blo 842353 12166523 := bstep (se 1 (by rfl) ⟨9124892, by rfl⟩ : syracuseStep 12166523 = 18249785) B18249785
theorem B6956441 : Blo 842353 6956441 := bstep (se 2 (by rfl) ⟨2608665, by rfl⟩ : syracuseStep 6956441 = 5217331) B5217331
theorem B2139655 : Blo 842353 2139655 := bstep (se 1 (by rfl) ⟨1604741, by rfl⟩ : syracuseStep 2139655 = 3209483) B3209483
theorem B2139959 : Blo 842353 2139959 := bstep (se 1 (by rfl) ⟨1604969, by rfl⟩ : syracuseStep 2139959 = 3209939) B3209939
theorem B3286865 : Blo 842353 3286865 := bstep (se 2 (by rfl) ⟨1232574, by rfl⟩ : syracuseStep 3286865 = 2465149) B2465149
theorem B7219151 : Blo 842353 7219151 := bstep (se 1 (by rfl) ⟨5414363, by rfl⟩ : syracuseStep 7219151 = 10828727) B10828727
theorem B3614701 : Blo 842353 3614701 := bstep (se 3 (by rfl) ⟨677756, by rfl⟩ : syracuseStep 3614701 = 1355513) B1355513
theorem B2140627 : Blo 842353 2140627 := bstep (se 1 (by rfl) ⟨1605470, by rfl⟩ : syracuseStep 2140627 = 3210941) B3210941
theorem B4631363 : Blo 842353 4631363 := bstep (se 1 (by rfl) ⟨3473522, by rfl⟩ : syracuseStep 4631363 = 6947045) B6947045
theorem B4270967 : Blo 842353 4270967 := bstep (se 1 (by rfl) ⟨3203225, by rfl⟩ : syracuseStep 4270967 = 6406451) B6406451
theorem B6401105 : Blo 842353 6401105 := bstep (se 2 (by rfl) ⟨2400414, by rfl⟩ : syracuseStep 6401105 = 4800829) B4800829
theorem B2141417 : Blo 842353 2141417 := bstep (se 2 (by rfl) ⟨803031, by rfl⟩ : syracuseStep 2141417 = 1606063) B1606063
theorem B2141579 : Blo 842353 2141579 := bstep (se 1 (by rfl) ⟨1606184, by rfl⟩ : syracuseStep 2141579 = 3212369) B3212369
theorem B4271777 : Blo 842353 4271777 := bstep (se 2 (by rfl) ⟨1601916, by rfl⟩ : syracuseStep 4271777 = 3203833) B3203833
theorem B7712455 : Blo 842353 7712455 := bstep (se 1 (by rfl) ⟨5784341, by rfl⟩ : syracuseStep 7712455 = 11568683) B11568683
theorem B4337449 : Blo 842353 4337449 := bstep (se 2 (by rfl) ⟨1626543, by rfl⟩ : syracuseStep 4337449 = 3253087) B3253087
theorem B11579345 : Blo 842353 11579345 := bstep (se 2 (by rfl) ⟨4342254, by rfl⟩ : syracuseStep 11579345 = 8684509) B8684509
theorem B23113795 : Blo 842353 23113795 := bstep (se 1 (by rfl) ⟨17335346, by rfl⟩ : syracuseStep 23113795 = 34670693) B34670693
theorem B1421887 : Blo 842353 1421887 := bstep (se 1 (by rfl) ⟨1066415, by rfl⟩ : syracuseStep 1421887 = 2132831) B2132831
theorem B21083261 : Blo 842353 21083261 := bstep (se 3 (by rfl) ⟨3953111, by rfl⟩ : syracuseStep 21083261 = 7906223) B7906223
theorem B1422569 : Blo 842353 1422569 := bstep (se 2 (by rfl) ⟨533463, by rfl⟩ : syracuseStep 1422569 = 1066927) B1066927
theorem B2405609 : Blo 842353 2405609 := bstep (se 2 (by rfl) ⟨902103, by rfl⟩ : syracuseStep 2405609 = 1804207) B1804207
theorem B4109555 : Blo 842353 4109555 := bstep (se 1 (by rfl) ⟨3082166, by rfl⟩ : syracuseStep 4109555 = 6164333) B6164333
theorem B1127689 : Blo 842353 1127689 := bstep (se 2 (by rfl) ⟨422883, by rfl⟩ : syracuseStep 1127689 = 845767) B845767
theorem B1422623 : Blo 842353 1422623 := bstep (se 1 (by rfl) ⟨1066967, by rfl⟩ : syracuseStep 1422623 = 2133935) B2133935
theorem B7222567 : Blo 842353 7222567 := bstep (se 1 (by rfl) ⟨5416925, by rfl⟩ : syracuseStep 7222567 = 10833851) B10833851
theorem B4568609 : Blo 842353 4568609 := bstep (se 2 (by rfl) ⟨1713228, by rfl⟩ : syracuseStep 4568609 = 3426457) B3426457
theorem B4273721 : Blo 842353 4273721 := bstep (se 2 (by rfl) ⟨1602645, by rfl⟩ : syracuseStep 4273721 = 3205291) B3205291
theorem B4110011 : Blo 842353 4110011 := bstep (se 1 (by rfl) ⟨3082508, by rfl⟩ : syracuseStep 4110011 = 6165017) B6165017
theorem B2471887 : Blo 842353 2471887 := bstep (se 1 (by rfl) ⟨1853915, by rfl⟩ : syracuseStep 2471887 = 3707831) B3707831
theorem B2701441 : Blo 842353 2701441 := bstep (se 2 (by rfl) ⟨1013040, by rfl⟩ : syracuseStep 2701441 = 2026081) B2026081
theorem B7223525 : Blo 842353 7223525 := bstep (se 4 (by rfl) ⟨677205, by rfl⟩ : syracuseStep 7223525 = 1354411) B1354411
theorem B5421437 : Blo 842353 5421437 := bstep (se 3 (by rfl) ⟨1016519, by rfl⟩ : syracuseStep 5421437 = 2033039) B2033039
theorem B1423993 : Blo 842353 1423993 := bstep (se 2 (by rfl) ⟨533997, by rfl⟩ : syracuseStep 1423993 = 1067995) B1067995
theorem B1424047 : Blo 842353 1424047 := bstep (se 1 (by rfl) ⟨1068035, by rfl⟩ : syracuseStep 1424047 = 2136071) B2136071
theorem B103791365 : Blo 842353 103791365 := bstep (se 4 (by rfl) ⟨9730440, by rfl⟩ : syracuseStep 103791365 = 19460881) B19460881
theorem B900391 : Blo 842353 900391 := bstep (se 1 (by rfl) ⟨675293, by rfl⟩ : syracuseStep 900391 = 1350587) B1350587
theorem B10796489 : Blo 842353 10796489 := bstep (se 2 (by rfl) ⟨4048683, by rfl⟩ : syracuseStep 10796489 = 8097367) B8097367
theorem B4570705 : Blo 842353 4570705 := bstep (se 2 (by rfl) ⟨1714014, by rfl⟩ : syracuseStep 4570705 = 3428029) B3428029
theorem B4275827 : Blo 842353 4275827 := bstep (se 1 (by rfl) ⟨3206870, by rfl⟩ : syracuseStep 4275827 = 6413741) B6413741
theorem B3424007 : Blo 842353 3424007 := bstep (se 1 (by rfl) ⟨2568005, by rfl⟩ : syracuseStep 3424007 = 5136011) B5136011
theorem B4800329 : Blo 842353 4800329 := bstep (se 2 (by rfl) ⟨1800123, by rfl⟩ : syracuseStep 4800329 = 3600247) B3600247
theorem B1425755 : Blo 842353 1425755 := bstep (se 1 (by rfl) ⟨1069316, by rfl⟩ : syracuseStep 1425755 = 2138633) B2138633
theorem B1425775 : Blo 842353 1425775 := bstep (se 1 (by rfl) ⟨1069331, by rfl⟩ : syracuseStep 1425775 = 2138663) B2138663
theorem B2408879 : Blo 842353 2408879 := bstep (se 1 (by rfl) ⟨1806659, by rfl⟩ : syracuseStep 2408879 = 3613319) B3613319
theorem B3424787 : Blo 842353 3424787 := bstep (se 1 (by rfl) ⟨2568590, by rfl⟩ : syracuseStep 3424787 = 5137181) B5137181
theorem B1425991 : Blo 842353 1425991 := bstep (se 1 (by rfl) ⟨1069493, by rfl⟩ : syracuseStep 1425991 = 2138987) B2138987
theorem B2704043 : Blo 842353 2704043 := bstep (se 1 (by rfl) ⟨2028032, by rfl⟩ : syracuseStep 2704043 = 4056065) B4056065
theorem B10961723 : Blo 842353 10961723 := bstep (se 1 (by rfl) ⟨8221292, by rfl⟩ : syracuseStep 10961723 = 16442585) B16442585
theorem B1426423 : Blo 842353 1426423 := bstep (se 1 (by rfl) ⟨1069817, by rfl⟩ : syracuseStep 1426423 = 2139635) B2139635
theorem B4277447 : Blo 842353 4277447 := bstep (se 1 (by rfl) ⟨3208085, by rfl⟩ : syracuseStep 4277447 = 6416171) B6416171
theorem B2278649 : Blo 842353 2278649 := bstep (se 2 (by rfl) ⟨854493, by rfl⟩ : syracuseStep 2278649 = 1708987) B1708987
theorem B1066279 : Blo 842353 1066279 := bstep (se 1 (by rfl) ⟨799709, by rfl⟩ : syracuseStep 1066279 = 1599419) B1599419
theorem B1426727 : Blo 842353 1426727 := bstep (se 1 (by rfl) ⟨1070045, by rfl⟩ : syracuseStep 1426727 = 2140091) B2140091
theorem B4277609 : Blo 842353 4277609 := bstep (se 2 (by rfl) ⟨1604103, by rfl⟩ : syracuseStep 4277609 = 3208207) B3208207
theorem B4802105 : Blo 842353 4802105 := bstep (se 2 (by rfl) ⟨1800789, by rfl⟩ : syracuseStep 4802105 = 3601579) B3601579
theorem B1066603 : Blo 842353 1066603 := bstep (se 1 (by rfl) ⟨799952, by rfl⟩ : syracuseStep 1066603 = 1599905) B1599905
theorem B1427179 : Blo 842353 1427179 := bstep (se 1 (by rfl) ⟨1070384, by rfl⟩ : syracuseStep 1427179 = 2140769) B2140769
theorem B15386435 : Blo 842353 15386435 := bstep (se 1 (by rfl) ⟨11539826, by rfl⟩ : syracuseStep 15386435 = 23079653) B23079653
theorem B4802813 : Blo 842353 4802813 := bstep (se 3 (by rfl) ⟨900527, by rfl⟩ : syracuseStep 4802813 = 1801055) B1801055
theorem B1263881 : Blo 842353 1263881 := bstep (se 2 (by rfl) ⟨473955, by rfl⟩ : syracuseStep 1263881 = 947911) B947911
theorem B1263983 : Blo 842353 1263983 := bstep (se 1 (by rfl) ⟨947987, by rfl⟩ : syracuseStep 1263983 = 1895975) B1895975
theorem B13191635 : Blo 842353 13191635 := bstep (se 1 (by rfl) ⟨9893726, by rfl⟩ : syracuseStep 13191635 = 19787453) B19787453
theorem B105335261 : Blo 842353 105335261 := bstep (se 3 (by rfl) ⟨19750361, by rfl⟩ : syracuseStep 105335261 = 39500723) B39500723
theorem B1264199 : Blo 842353 1264199 := bstep (se 1 (by rfl) ⟨948149, by rfl⟩ : syracuseStep 1264199 = 1896299) B1896299
theorem B21908069 : Blo 842353 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B1264235 : Blo 842353 1264235 := bstep (se 1 (by rfl) ⟨948176, by rfl⟩ : syracuseStep 1264235 = 1896353) B1896353
theorem B1428151 : Blo 842353 1428151 := bstep (se 1 (by rfl) ⟨1071113, by rfl⟩ : syracuseStep 1428151 = 2142227) B2142227
theorem B1264463 : Blo 842353 1264463 := bstep (se 1 (by rfl) ⟨948347, by rfl⟩ : syracuseStep 1264463 = 1896695) B1896695
theorem B3853175 : Blo 842353 3853175 := bstep (se 1 (by rfl) ⟨2889881, by rfl⟩ : syracuseStep 3853175 = 5779763) B5779763
theorem B9129131 : Blo 842353 9129131 := bstep (se 1 (by rfl) ⟨6846848, by rfl⟩ : syracuseStep 9129131 = 13693697) B13693697
theorem B1264859 : Blo 842353 1264859 := bstep (se 1 (by rfl) ⟨948644, by rfl⟩ : syracuseStep 1264859 = 1897289) B1897289
theorem B1068319 : Blo 842353 1068319 := bstep (se 1 (by rfl) ⟨801239, by rfl⟩ : syracuseStep 1068319 = 1602479) B1602479
theorem B1265033 : Blo 842353 1265033 := bstep (se 2 (by rfl) ⟨474387, by rfl⟩ : syracuseStep 1265033 = 948775) B948775
theorem B4869641 : Blo 842353 4869641 := bstep (se 2 (by rfl) ⟨1826115, by rfl⟩ : syracuseStep 4869641 = 3652231) B3652231
theorem B7196323 : Blo 842353 7196323 := bstep (se 1 (by rfl) ⟨5397242, by rfl⟩ : syracuseStep 7196323 = 10794485) B10794485
theorem B1265387 : Blo 842353 1265387 := bstep (se 1 (by rfl) ⟨949040, by rfl⟩ : syracuseStep 1265387 = 1898081) B1898081
theorem B3198761 : Blo 842353 3198761 := bstep (se 2 (by rfl) ⟨1199535, by rfl⟩ : syracuseStep 3198761 = 2399071) B2399071
theorem B1265615 : Blo 842353 1265615 := bstep (se 1 (by rfl) ⟨949211, by rfl⟩ : syracuseStep 1265615 = 1898423) B1898423
theorem B2707465 : Blo 842353 2707465 := bstep (se 2 (by rfl) ⟨1015299, by rfl⟩ : syracuseStep 2707465 = 2030599) B2030599
theorem B1266011 : Blo 842353 1266011 := bstep (se 1 (by rfl) ⟨949508, by rfl⟩ : syracuseStep 1266011 = 1899017) B1899017
theorem B2281835 : Blo 842353 2281835 := bstep (se 1 (by rfl) ⟨1711376, by rfl⟩ : syracuseStep 2281835 = 3422753) B3422753
theorem B2281979 : Blo 842353 2281979 := bstep (se 1 (by rfl) ⟨1711484, by rfl⟩ : syracuseStep 2281979 = 3422969) B3422969
theorem B1266239 : Blo 842353 1266239 := bstep (se 1 (by rfl) ⟨949679, by rfl⟩ : syracuseStep 1266239 = 1899359) B1899359
theorem B7197281 : Blo 842353 7197281 := bstep (se 2 (by rfl) ⟨2698980, by rfl⟩ : syracuseStep 7197281 = 5397961) B5397961
theorem B1266359 : Blo 842353 1266359 := bstep (se 1 (by rfl) ⟨949769, by rfl⟩ : syracuseStep 1266359 = 1899539) B1899539
theorem B1266587 : Blo 842353 1266587 := bstep (se 1 (by rfl) ⟨949940, by rfl⟩ : syracuseStep 1266587 = 1899881) B1899881
theorem B3199945 : Blo 842353 3199945 := bstep (se 2 (by rfl) ⟨1199979, by rfl⟩ : syracuseStep 3199945 = 2399959) B2399959
theorem B4281335 : Blo 842353 4281335 := bstep (se 1 (by rfl) ⟨3211001, by rfl⟩ : syracuseStep 4281335 = 6422003) B6422003
theorem B2053259 : Blo 842353 2053259 := bstep (se 1 (by rfl) ⟨1539944, by rfl⟩ : syracuseStep 2053259 = 3079889) B3079889
theorem B3200249 : Blo 842353 3200249 := bstep (se 2 (by rfl) ⟨1200093, by rfl⟩ : syracuseStep 3200249 = 2400187) B2400187
theorem B1266983 : Blo 842353 1266983 := bstep (se 1 (by rfl) ⟨950237, by rfl⟩ : syracuseStep 1266983 = 1900475) B1900475
theorem B1267067 : Blo 842353 1267067 := bstep (se 1 (by rfl) ⟨950300, by rfl⟩ : syracuseStep 1267067 = 1900601) B1900601
theorem B3200417 : Blo 842353 3200417 := bstep (se 2 (by rfl) ⟨1200156, by rfl⟩ : syracuseStep 3200417 = 2400313) B2400313
theorem B34723235 : Blo 842353 34723235 := bstep (se 1 (by rfl) ⟨26042426, by rfl⟩ : syracuseStep 34723235 = 52084853) B52084853
theorem B1267193 : Blo 842353 1267193 := bstep (se 2 (by rfl) ⟨475197, by rfl⟩ : syracuseStep 1267193 = 950395) B950395
theorem B1070587 : Blo 842353 1070587 := bstep (se 1 (by rfl) ⟨802940, by rfl⟩ : syracuseStep 1070587 = 1605881) B1605881
theorem B1267295 : Blo 842353 1267295 := bstep (se 1 (by rfl) ⟨950471, by rfl⟩ : syracuseStep 1267295 = 1900943) B1900943
theorem B1070815 : Blo 842353 1070815 := bstep (se 1 (by rfl) ⟨803111, by rfl⟩ : syracuseStep 1070815 = 1606223) B1606223
theorem B5003063 : Blo 842353 5003063 := bstep (se 1 (by rfl) ⟨3752297, by rfl⟩ : syracuseStep 5003063 = 7504595) B7504595
theorem B1267511 : Blo 842353 1267511 := bstep (se 1 (by rfl) ⟨950633, by rfl⟩ : syracuseStep 1267511 = 1901267) B1901267
theorem B24401999 : Blo 842353 24401999 := bstep (se 1 (by rfl) ⟨18301499, by rfl⟩ : syracuseStep 24401999 = 36602999) B36602999
theorem B1267817 : Blo 842353 1267817 := bstep (se 2 (by rfl) ⟨475431, by rfl⟩ : syracuseStep 1267817 = 950863) B950863
theorem B4806935 : Blo 842353 4806935 := bstep (se 1 (by rfl) ⟨3605201, by rfl⟩ : syracuseStep 4806935 = 7210403) B7210403
theorem B1268135 : Blo 842353 1268135 := bstep (se 1 (by rfl) ⟨951101, by rfl⟩ : syracuseStep 1268135 = 1902203) B1902203
theorem B1268219 : Blo 842353 1268219 := bstep (se 1 (by rfl) ⟨951164, by rfl⟩ : syracuseStep 1268219 = 1902329) B1902329
theorem B4119113 : Blo 842353 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B1268345 : Blo 842353 1268345 := bstep (se 2 (by rfl) ⟨475629, by rfl⟩ : syracuseStep 1268345 = 951259) B951259
theorem B1268399 : Blo 842353 1268399 := bstep (se 1 (by rfl) ⟨951299, by rfl⟩ : syracuseStep 1268399 = 1902599) B1902599
theorem B842463 : Blo 842353 842463 := bstep (se 1 (by rfl) ⟨631847, by rfl⟩ : syracuseStep 842463 = 1263695) B1263695
theorem B1268447 : Blo 842353 1268447 := bstep (se 1 (by rfl) ⟨951335, by rfl⟩ : syracuseStep 1268447 = 1902671) B1902671
theorem B842543 : Blo 842353 842543 := bstep (se 1 (by rfl) ⟨631907, by rfl⟩ : syracuseStep 842543 = 1263815) B1263815
theorem B4283279 : Blo 842353 4283279 := bstep (se 1 (by rfl) ⟨3212459, by rfl⟩ : syracuseStep 4283279 = 6424919) B6424919
theorem B842651 : Blo 842353 842651 := bstep (se 1 (by rfl) ⟨631988, by rfl⟩ : syracuseStep 842651 = 1263977) B1263977
theorem B842703 : Blo 842353 842703 := bstep (se 1 (by rfl) ⟨632027, by rfl⟩ : syracuseStep 842703 = 1264055) B1264055
theorem B842727 : Blo 842353 842727 := bstep (se 1 (by rfl) ⟨632045, by rfl⟩ : syracuseStep 842727 = 1264091) B1264091
theorem B1268711 : Blo 842353 1268711 := bstep (se 1 (by rfl) ⟨951533, by rfl⟩ : syracuseStep 1268711 = 1903067) B1903067
theorem B3464315 : Blo 842353 3464315 := bstep (se 1 (by rfl) ⟨2598236, by rfl⟩ : syracuseStep 3464315 = 5196473) B5196473
theorem B1268969 : Blo 842353 1268969 := bstep (se 2 (by rfl) ⟨475863, by rfl⟩ : syracuseStep 1268969 = 951727) B951727
theorem B2284793 : Blo 842353 2284793 := bstep (se 2 (by rfl) ⟨856797, by rfl⟩ : syracuseStep 2284793 = 1713595) B1713595
theorem B843039 : Blo 842353 843039 := bstep (se 1 (by rfl) ⟨632279, by rfl⟩ : syracuseStep 843039 = 1264559) B1264559
theorem B1269023 : Blo 842353 1269023 := bstep (se 1 (by rfl) ⟨951767, by rfl⟩ : syracuseStep 1269023 = 1903535) B1903535
theorem B843099 : Blo 842353 843099 := bstep (se 1 (by rfl) ⟨632324, by rfl⟩ : syracuseStep 843099 = 1264649) B1264649
theorem B843119 : Blo 842353 843119 := bstep (se 1 (by rfl) ⟨632339, by rfl⟩ : syracuseStep 843119 = 1264679) B1264679
theorem B4054391 : Blo 842353 4054391 := bstep (se 1 (by rfl) ⟨3040793, by rfl⟩ : syracuseStep 4054391 = 6081587) B6081587
theorem B843175 : Blo 842353 843175 := bstep (se 1 (by rfl) ⟨632381, by rfl⟩ : syracuseStep 843175 = 1264763) B1264763
theorem B1269191 : Blo 842353 1269191 := bstep (se 1 (by rfl) ⟨951893, by rfl⟩ : syracuseStep 1269191 = 1903787) B1903787
theorem B843259 : Blo 842353 843259 := bstep (se 1 (by rfl) ⟨632444, by rfl⟩ : syracuseStep 843259 = 1264889) B1264889
theorem B843327 : Blo 842353 843327 := bstep (se 1 (by rfl) ⟨632495, by rfl⟩ : syracuseStep 843327 = 1264991) B1264991
theorem B843335 : Blo 842353 843335 := bstep (se 1 (by rfl) ⟨632501, by rfl⟩ : syracuseStep 843335 = 1265003) B1265003
theorem B843487 : Blo 842353 843487 := bstep (se 1 (by rfl) ⟨632615, by rfl⟩ : syracuseStep 843487 = 1265231) B1265231
theorem B7790339 : Blo 842353 7790339 := bstep (se 1 (by rfl) ⟨5842754, by rfl⟩ : syracuseStep 7790339 = 11685509) B11685509
theorem B843567 : Blo 842353 843567 := bstep (se 1 (by rfl) ⟨632675, by rfl⟩ : syracuseStep 843567 = 1265351) B1265351
theorem B843675 : Blo 842353 843675 := bstep (se 1 (by rfl) ⟨632756, by rfl⟩ : syracuseStep 843675 = 1265513) B1265513
theorem B843727 : Blo 842353 843727 := bstep (se 1 (by rfl) ⟨632795, by rfl⟩ : syracuseStep 843727 = 1265591) B1265591
theorem B843751 : Blo 842353 843751 := bstep (se 1 (by rfl) ⟨632813, by rfl⟩ : syracuseStep 843751 = 1265627) B1265627
theorem B1925129 : Blo 842353 1925129 := bstep (se 2 (by rfl) ⟨721923, by rfl⟩ : syracuseStep 1925129 = 1443847) B1443847
theorem B7692337 : Blo 842353 7692337 := bstep (se 2 (by rfl) ⟨2884626, by rfl⟩ : syracuseStep 7692337 = 5769253) B5769253
theorem B844063 : Blo 842353 844063 := bstep (se 1 (by rfl) ⟨633047, by rfl⟩ : syracuseStep 844063 = 1266095) B1266095
theorem B844123 : Blo 842353 844123 := bstep (se 1 (by rfl) ⟨633092, by rfl⟩ : syracuseStep 844123 = 1266185) B1266185
theorem B844143 : Blo 842353 844143 := bstep (se 1 (by rfl) ⟨633107, by rfl⟩ : syracuseStep 844143 = 1266215) B1266215
theorem B844199 : Blo 842353 844199 := bstep (se 1 (by rfl) ⟨633149, by rfl⟩ : syracuseStep 844199 = 1266299) B1266299
theorem B844283 : Blo 842353 844283 := bstep (se 1 (by rfl) ⟨633212, by rfl⟩ : syracuseStep 844283 = 1266425) B1266425
theorem B844351 : Blo 842353 844351 := bstep (se 1 (by rfl) ⟨633263, by rfl⟩ : syracuseStep 844351 = 1266527) B1266527
theorem B2843207 : Blo 842353 2843207 := bstep (se 1 (by rfl) ⟨2132405, by rfl⟩ : syracuseStep 2843207 = 4264811) B4264811
theorem B844359 : Blo 842353 844359 := bstep (se 1 (by rfl) ⟨633269, by rfl⟩ : syracuseStep 844359 = 1266539) B1266539
theorem B844511 : Blo 842353 844511 := bstep (se 1 (by rfl) ⟨633383, by rfl⟩ : syracuseStep 844511 = 1266767) B1266767
theorem B2056951 : Blo 842353 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B844591 : Blo 842353 844591 := bstep (se 1 (by rfl) ⟨633443, by rfl⟩ : syracuseStep 844591 = 1266887) B1266887
theorem B6415199 : Blo 842353 6415199 := bstep (se 1 (by rfl) ⟨4811399, by rfl⟩ : syracuseStep 6415199 = 9622799) B9622799
theorem B844699 : Blo 842353 844699 := bstep (se 1 (by rfl) ⟨633524, by rfl⟩ : syracuseStep 844699 = 1267049) B1267049
theorem B844751 : Blo 842353 844751 := bstep (se 1 (by rfl) ⟨633563, by rfl⟩ : syracuseStep 844751 = 1267127) B1267127
theorem B844775 : Blo 842353 844775 := bstep (se 1 (by rfl) ⟨633581, by rfl⟩ : syracuseStep 844775 = 1267163) B1267163
theorem B2843639 : Blo 842353 2843639 := bstep (se 1 (by rfl) ⟨2132729, by rfl⟩ : syracuseStep 2843639 = 4265459) B4265459
theorem B2024735 : Blo 842353 2024735 := bstep (se 1 (by rfl) ⟨1518551, by rfl⟩ : syracuseStep 2024735 = 3037103) B3037103
theorem B845087 : Blo 842353 845087 := bstep (se 1 (by rfl) ⟨633815, by rfl⟩ : syracuseStep 845087 = 1267631) B1267631
theorem B845147 : Blo 842353 845147 := bstep (se 1 (by rfl) ⟨633860, by rfl⟩ : syracuseStep 845147 = 1267721) B1267721
theorem B845167 : Blo 842353 845167 := bstep (se 1 (by rfl) ⟨633875, by rfl⟩ : syracuseStep 845167 = 1267751) B1267751
theorem B845223 : Blo 842353 845223 := bstep (se 1 (by rfl) ⟨633917, by rfl⟩ : syracuseStep 845223 = 1267835) B1267835
theorem B2057687 : Blo 842353 2057687 := bstep (se 1 (by rfl) ⟨1543265, by rfl⟩ : syracuseStep 2057687 = 3086531) B3086531
theorem B845307 : Blo 842353 845307 := bstep (se 1 (by rfl) ⟨633980, by rfl⟩ : syracuseStep 845307 = 1267961) B1267961
theorem B845375 : Blo 842353 845375 := bstep (se 1 (by rfl) ⟨634031, by rfl⟩ : syracuseStep 845375 = 1268063) B1268063
theorem B845383 : Blo 842353 845383 := bstep (se 1 (by rfl) ⟨634037, by rfl⟩ : syracuseStep 845383 = 1268075) B1268075
theorem B845535 : Blo 842353 845535 := bstep (se 1 (by rfl) ⟨634151, by rfl⟩ : syracuseStep 845535 = 1268303) B1268303
theorem B845615 : Blo 842353 845615 := bstep (se 1 (by rfl) ⟨634211, by rfl⟩ : syracuseStep 845615 = 1268423) B1268423
theorem B2844503 : Blo 842353 2844503 := bstep (se 1 (by rfl) ⟨2133377, by rfl⟩ : syracuseStep 2844503 = 4266755) B4266755
theorem B845723 : Blo 842353 845723 := bstep (se 1 (by rfl) ⟨634292, by rfl⟩ : syracuseStep 845723 = 1268585) B1268585
theorem B845775 : Blo 842353 845775 := bstep (se 1 (by rfl) ⟨634331, by rfl⟩ : syracuseStep 845775 = 1268663) B1268663
theorem B845799 : Blo 842353 845799 := bstep (se 1 (by rfl) ⟨634349, by rfl⟩ : syracuseStep 845799 = 1268699) B1268699
theorem B846111 : Blo 842353 846111 := bstep (se 1 (by rfl) ⟨634583, by rfl⟩ : syracuseStep 846111 = 1269167) B1269167
theorem B846171 : Blo 842353 846171 := bstep (se 1 (by rfl) ⟨634628, by rfl⟩ : syracuseStep 846171 = 1269257) B1269257
theorem B846191 : Blo 842353 846191 := bstep (se 1 (by rfl) ⟨634643, by rfl⟩ : syracuseStep 846191 = 1269287) B1269287
theorem B846247 : Blo 842353 846247 := bstep (se 1 (by rfl) ⟨634685, by rfl⟩ : syracuseStep 846247 = 1269371) B1269371
theorem B846331 : Blo 842353 846331 := bstep (se 1 (by rfl) ⟨634748, by rfl⟩ : syracuseStep 846331 = 1269497) B1269497
theorem B6417143 : Blo 842353 6417143 := bstep (se 1 (by rfl) ⟨4812857, by rfl⟩ : syracuseStep 6417143 = 9625715) B9625715
theorem B2845583 : Blo 842353 2845583 := bstep (se 1 (by rfl) ⟨2134187, by rfl⟩ : syracuseStep 2845583 = 4268375) B4268375
theorem B1895399 : Blo 842353 1895399 := bstep (se 1 (by rfl) ⟨1421549, by rfl⟩ : syracuseStep 1895399 = 2843099) B2843099
theorem B1895777 : Blo 842353 1895777 := bstep (se 2 (by rfl) ⟨710916, by rfl⟩ : syracuseStep 1895777 = 1421833) B1421833
theorem B2026889 : Blo 842353 2026889 := bstep (se 2 (by rfl) ⟨760083, by rfl⟩ : syracuseStep 2026889 = 1520167) B1520167
theorem B3206537 : Blo 842353 3206537 := bstep (se 2 (by rfl) ⟨1202451, by rfl⟩ : syracuseStep 3206537 = 2404903) B2404903
theorem B1895867 : Blo 842353 1895867 := bstep (se 1 (by rfl) ⟨1421900, by rfl⟩ : syracuseStep 1895867 = 2843801) B2843801
theorem B1895993 : Blo 842353 1895993 := bstep (se 2 (by rfl) ⟨710997, by rfl⟩ : syracuseStep 1895993 = 1421995) B1421995
theorem B2846825 : Blo 842353 2846825 := bstep (se 2 (by rfl) ⟨1067559, by rfl⟩ : syracuseStep 2846825 = 2135119) B2135119
theorem B3043433 : Blo 842353 3043433 := bstep (se 2 (by rfl) ⟨1141287, by rfl⟩ : syracuseStep 3043433 = 2282575) B2282575
theorem B1896659 : Blo 842353 1896659 := bstep (se 1 (by rfl) ⟨1422494, by rfl⟩ : syracuseStep 1896659 = 2844989) B2844989
theorem B1896713 : Blo 842353 1896713 := bstep (se 2 (by rfl) ⟨711267, by rfl⟩ : syracuseStep 1896713 = 1422535) B1422535
theorem B1143239 : Blo 842353 1143239 := bstep (se 1 (by rfl) ⟨857429, by rfl⟩ : syracuseStep 1143239 = 1714859) B1714859
theorem B1896929 : Blo 842353 1896929 := bstep (se 2 (by rfl) ⟨711348, by rfl⟩ : syracuseStep 1896929 = 1422697) B1422697
theorem B2028215 : Blo 842353 2028215 := bstep (se 1 (by rfl) ⟨1521161, by rfl⟩ : syracuseStep 2028215 = 3042323) B3042323
theorem B1897235 : Blo 842353 1897235 := bstep (se 1 (by rfl) ⟨1422926, by rfl⟩ : syracuseStep 1897235 = 2845853) B2845853
theorem B2847689 : Blo 842353 2847689 := bstep (se 2 (by rfl) ⟨1067883, by rfl⟩ : syracuseStep 2847689 = 2135767) B2135767
theorem B4813769 : Blo 842353 4813769 := bstep (se 2 (by rfl) ⟨1805163, by rfl⟩ : syracuseStep 4813769 = 3610327) B3610327
theorem B1897595 : Blo 842353 1897595 := bstep (se 1 (by rfl) ⟨1423196, by rfl⟩ : syracuseStep 1897595 = 2846393) B2846393
theorem B10810583 : Blo 842353 10810583 := bstep (se 1 (by rfl) ⟨8107937, by rfl⟩ : syracuseStep 10810583 = 16215875) B16215875
theorem B2847959 : Blo 842353 2847959 := bstep (se 1 (by rfl) ⟨2135969, by rfl⟩ : syracuseStep 2847959 = 4271939) B4271939
theorem B1897721 : Blo 842353 1897721 := bstep (se 2 (by rfl) ⟨711645, by rfl⟩ : syracuseStep 1897721 = 1423291) B1423291
theorem B5404009 : Blo 842353 5404009 := bstep (se 2 (by rfl) ⟨2026503, by rfl⟩ : syracuseStep 5404009 = 4053007) B4053007
theorem B1897865 : Blo 842353 1897865 := bstep (se 2 (by rfl) ⟨711699, by rfl⟩ : syracuseStep 1897865 = 1423399) B1423399
theorem B3601853 : Blo 842353 3601853 := bstep (se 3 (by rfl) ⟨675347, by rfl⟩ : syracuseStep 3601853 = 1350695) B1350695
theorem B7206407 : Blo 842353 7206407 := bstep (se 1 (by rfl) ⟨5404805, by rfl⟩ : syracuseStep 7206407 = 10809611) B10809611
theorem B1897991 : Blo 842353 1897991 := bstep (se 1 (by rfl) ⟨1423493, by rfl⟩ : syracuseStep 1897991 = 2846987) B2846987
theorem B1799867 : Blo 842353 1799867 := bstep (se 1 (by rfl) ⟨1349900, by rfl⟩ : syracuseStep 1799867 = 2699801) B2699801
theorem B1898171 : Blo 842353 1898171 := bstep (se 1 (by rfl) ⟨1423628, by rfl⟩ : syracuseStep 1898171 = 2847257) B2847257
theorem B1603307 : Blo 842353 1603307 := bstep (se 1 (by rfl) ⟨1202480, by rfl⟩ : syracuseStep 1603307 = 2404961) B2404961
theorem B1898297 : Blo 842353 1898297 := bstep (se 2 (by rfl) ⟨711861, by rfl⟩ : syracuseStep 1898297 = 1423723) B1423723
theorem B2029369 : Blo 842353 2029369 := bstep (se 2 (by rfl) ⟨761013, by rfl⟩ : syracuseStep 2029369 = 1522027) B1522027
theorem B948199 : Blo 842353 948199 := bstep (se 1 (by rfl) ⟨711149, by rfl⟩ : syracuseStep 948199 = 1422299) B1422299
theorem B4061465 : Blo 842353 4061465 := bstep (se 2 (by rfl) ⟨1523049, by rfl⟩ : syracuseStep 4061465 = 3046099) B3046099
theorem B1898927 : Blo 842353 1898927 := bstep (se 1 (by rfl) ⟨1424195, by rfl⟩ : syracuseStep 1898927 = 2848391) B2848391
theorem B1898963 : Blo 842353 1898963 := bstep (se 1 (by rfl) ⟨1424222, by rfl⟩ : syracuseStep 1898963 = 2848445) B2848445
theorem B6421031 : Blo 842353 6421031 := bstep (se 1 (by rfl) ⟨4815773, by rfl⟩ : syracuseStep 6421031 = 9631547) B9631547
theorem B1899071 : Blo 842353 1899071 := bstep (se 1 (by rfl) ⟨1424303, by rfl⟩ : syracuseStep 1899071 = 2848607) B2848607
theorem B1735231 : Blo 842353 1735231 := bstep (se 1 (by rfl) ⟨1301423, by rfl⟩ : syracuseStep 1735231 = 2602847) B2602847
theorem B1899179 : Blo 842353 1899179 := bstep (se 1 (by rfl) ⟨1424384, by rfl⟩ : syracuseStep 1899179 = 2848769) B2848769
theorem B1604279 : Blo 842353 1604279 := bstep (se 1 (by rfl) ⟨1203209, by rfl⟩ : syracuseStep 1604279 = 2406419) B2406419
theorem B2030579 : Blo 842353 2030579 := bstep (se 1 (by rfl) ⟨1522934, by rfl⟩ : syracuseStep 2030579 = 3045869) B3045869
theorem B1899719 : Blo 842353 1899719 := bstep (se 1 (by rfl) ⟨1424789, by rfl⟩ : syracuseStep 1899719 = 2849579) B2849579
theorem B2850011 : Blo 842353 2850011 := bstep (se 1 (by rfl) ⟨2137508, by rfl⟩ : syracuseStep 2850011 = 4275017) B4275017
theorem B1899899 : Blo 842353 1899899 := bstep (se 1 (by rfl) ⟨1424924, by rfl⟩ : syracuseStep 1899899 = 2849849) B2849849
theorem B1900025 : Blo 842353 1900025 := bstep (se 2 (by rfl) ⟨712509, by rfl⟩ : syracuseStep 1900025 = 1425019) B1425019
theorem B1900115 : Blo 842353 1900115 := bstep (se 1 (by rfl) ⟨1425086, by rfl⟩ : syracuseStep 1900115 = 2850173) B2850173
theorem B949855 : Blo 842353 949855 := bstep (se 1 (by rfl) ⟨712391, by rfl⟩ : syracuseStep 949855 = 1424783) B1424783
theorem B1900295 : Blo 842353 1900295 := bstep (se 1 (by rfl) ⟨1425221, by rfl⟩ : syracuseStep 1900295 = 2850443) B2850443
theorem B1605433 : Blo 842353 1605433 := bstep (se 2 (by rfl) ⟨602037, by rfl⟩ : syracuseStep 1605433 = 1204075) B1204075
theorem B3604297 : Blo 842353 3604297 := bstep (se 2 (by rfl) ⟨1351611, by rfl⟩ : syracuseStep 3604297 = 2703223) B2703223
theorem B9600929 : Blo 842353 9600929 := bstep (se 2 (by rfl) ⟨3600348, by rfl⟩ : syracuseStep 9600929 = 7200697) B7200697
theorem B1802191 : Blo 842353 1802191 := bstep (se 1 (by rfl) ⟨1351643, by rfl⟩ : syracuseStep 1802191 = 2703287) B2703287
theorem B1900583 : Blo 842353 1900583 := bstep (se 1 (by rfl) ⟨1425437, by rfl⟩ : syracuseStep 1900583 = 2850875) B2850875
theorem B1900763 : Blo 842353 1900763 := bstep (se 1 (by rfl) ⟨1425572, by rfl⟩ : syracuseStep 1900763 = 2851145) B2851145
theorem B950503 : Blo 842353 950503 := bstep (se 1 (by rfl) ⟨712877, by rfl⟩ : syracuseStep 950503 = 1425755) B1425755
theorem B41025797 : Blo 842353 41025797 := bstep (se 4 (by rfl) ⟨3846168, by rfl⟩ : syracuseStep 41025797 = 7692337) B7692337
theorem B1605919 : Blo 842353 1605919 := bstep (se 1 (by rfl) ⟨1204439, by rfl⟩ : syracuseStep 1605919 = 2408879) B2408879
theorem B1901033 : Blo 842353 1901033 := bstep (se 2 (by rfl) ⟨712887, by rfl⟩ : syracuseStep 1901033 = 1425775) B1425775
theorem B7307815 : Blo 842353 7307815 := bstep (se 1 (by rfl) ⟨5480861, by rfl⟩ : syracuseStep 7307815 = 10961723) B10961723
theorem B3211883 : Blo 842353 3211883 := bstep (se 1 (by rfl) ⟨2408912, by rfl⟩ : syracuseStep 3211883 = 4817825) B4817825
theorem B1901321 : Blo 842353 1901321 := bstep (se 2 (by rfl) ⟨712995, by rfl⟩ : syracuseStep 1901321 = 1425991) B1425991
theorem B2851631 : Blo 842353 2851631 := bstep (se 1 (by rfl) ⟨2138723, by rfl⟩ : syracuseStep 2851631 = 4277447) B4277447
theorem B951151 : Blo 842353 951151 := bstep (se 1 (by rfl) ⟨713363, by rfl⟩ : syracuseStep 951151 = 1426727) B1426727
theorem B2851739 : Blo 842353 2851739 := bstep (se 1 (by rfl) ⟨2138804, by rfl⟩ : syracuseStep 2851739 = 4277609) B4277609
theorem B3048637 : Blo 842353 3048637 := bstep (se 3 (by rfl) ⟨571619, by rfl⟩ : syracuseStep 3048637 = 1143239) B1143239
theorem B10257623 : Blo 842353 10257623 := bstep (se 1 (by rfl) ⟨7693217, by rfl⟩ : syracuseStep 10257623 = 15386435) B15386435
theorem B24380675 : Blo 842353 24380675 := bstep (se 1 (by rfl) ⟨18285506, by rfl⟩ : syracuseStep 24380675 = 36571013) B36571013
theorem B1901897 : Blo 842353 1901897 := bstep (se 2 (by rfl) ⟨713211, by rfl⟩ : syracuseStep 1901897 = 1426423) B1426423
theorem B6423947 : Blo 842353 6423947 := bstep (se 1 (by rfl) ⟨4817960, by rfl⟩ : syracuseStep 6423947 = 9635921) B9635921
theorem B70223507 : Blo 842353 70223507 := bstep (se 1 (by rfl) ⟨52667630, by rfl⟩ : syracuseStep 70223507 = 105335261) B105335261
theorem B7210781 : Blo 842353 7210781 := bstep (se 3 (by rfl) ⟨1352021, by rfl⟩ : syracuseStep 7210781 = 2704043) B2704043
theorem B2852873 : Blo 842353 2852873 := bstep (se 2 (by rfl) ⟨1069827, by rfl⟩ : syracuseStep 2852873 = 2139655) B2139655
theorem B1902887 : Blo 842353 1902887 := bstep (se 1 (by rfl) ⟨1427165, by rfl⟩ : syracuseStep 1902887 = 2854331) B2854331
theorem B1902905 : Blo 842353 1902905 := bstep (se 2 (by rfl) ⟨713589, by rfl⟩ : syracuseStep 1902905 = 1427179) B1427179
theorem B3246427 : Blo 842353 3246427 := bstep (se 1 (by rfl) ⟨2434820, by rfl⟩ : syracuseStep 3246427 = 4869641) B4869641
theorem B2132507 : Blo 842353 2132507 := bstep (se 1 (by rfl) ⟨1599380, by rfl⟩ : syracuseStep 2132507 = 3198761) B3198761
theorem B4819601 : Blo 842353 4819601 := bstep (se 2 (by rfl) ⟨1807350, by rfl⟩ : syracuseStep 4819601 = 3614701) B3614701
theorem B24317117 : Blo 842353 24317117 := bstep (se 3 (by rfl) ⟨4559459, by rfl⟩ : syracuseStep 24317117 = 9118919) B9118919
theorem B2854169 : Blo 842353 2854169 := bstep (se 2 (by rfl) ⟨1070313, by rfl⟩ : syracuseStep 2854169 = 2140627) B2140627
theorem B2854223 : Blo 842353 2854223 := bstep (se 1 (by rfl) ⟨2140667, by rfl⟩ : syracuseStep 2854223 = 4281335) B4281335
theorem B2133499 : Blo 842353 2133499 := bstep (se 1 (by rfl) ⟨1600124, by rfl⟩ : syracuseStep 2133499 = 3200249) B3200249
theorem B1904201 : Blo 842353 1904201 := bstep (se 2 (by rfl) ⟨714075, by rfl⟩ : syracuseStep 1904201 = 1428151) B1428151
theorem B2133611 : Blo 842353 2133611 := bstep (se 1 (by rfl) ⟨1600208, by rfl⟩ : syracuseStep 2133611 = 3200417) B3200417
theorem B2887463 : Blo 842353 2887463 := bstep (se 1 (by rfl) ⟨2165597, by rfl⟩ : syracuseStep 2887463 = 4331195) B4331195
theorem B2855519 : Blo 842353 2855519 := bstep (se 1 (by rfl) ⟨2141639, by rfl⟩ : syracuseStep 2855519 = 4283279) B4283279
theorem B8131387 : Blo 842353 8131387 := bstep (se 1 (by rfl) ⟨6098540, by rfl⟩ : syracuseStep 8131387 = 12197081) B12197081
theorem B4265135 : Blo 842353 4265135 := bstep (se 1 (by rfl) ⟨3198851, by rfl⟩ : syracuseStep 4265135 = 6397703) B6397703
theorem B4330705 : Blo 842353 4330705 := bstep (se 2 (by rfl) ⟨1624014, by rfl⟩ : syracuseStep 4330705 = 3248029) B3248029
theorem B1283419 : Blo 842353 1283419 := bstep (se 1 (by rfl) ⟨962564, by rfl⟩ : syracuseStep 1283419 = 1925129) B1925129
theorem B3609953 : Blo 842353 3609953 := bstep (se 2 (by rfl) ⟨1353732, by rfl⟩ : syracuseStep 3609953 = 2707465) B2707465
theorem B4266593 : Blo 842353 4266593 := bstep (se 2 (by rfl) ⟨1599972, by rfl⟩ : syracuseStep 4266593 = 3199945) B3199945
theorem B3087575 : Blo 842353 3087575 := bstep (se 1 (by rfl) ⟨2315681, by rfl⟩ : syracuseStep 3087575 = 4631363) B4631363
theorem B4267403 : Blo 842353 4267403 := bstep (se 1 (by rfl) ⟨3200552, by rfl⟩ : syracuseStep 4267403 = 6401105) B6401105
theorem B1351259 : Blo 842353 1351259 := bstep (se 1 (by rfl) ⟨1013444, by rfl⟩ : syracuseStep 1351259 = 2026889) B2026889
theorem B2137691 : Blo 842353 2137691 := bstep (se 1 (by rfl) ⟨1603268, by rfl⟩ : syracuseStep 2137691 = 3206537) B3206537
theorem B1352143 : Blo 842353 1352143 := bstep (se 1 (by rfl) ⟨1014107, by rfl⟩ : syracuseStep 1352143 = 2028215) B2028215
theorem B2401235 : Blo 842353 2401235 := bstep (se 1 (by rfl) ⟨1800926, by rfl⟩ : syracuseStep 2401235 = 3601853) B3601853
theorem B5776541 : Blo 842353 5776541 := bstep (se 3 (by rfl) ⟨1083101, by rfl⟩ : syracuseStep 5776541 = 2166203) B2166203
theorem B4564133 : Blo 842353 4564133 := bstep (se 4 (by rfl) ⟨427887, by rfl⟩ : syracuseStep 4564133 = 855775) B855775
theorem B41100533 : Blo 842353 41100533 := bstep (se 5 (by rfl) ⟨1926587, by rfl⟩ : syracuseStep 41100533 = 3853175) B3853175
theorem B3614291 : Blo 842353 3614291 := bstep (se 1 (by rfl) ⟨2710718, by rfl⟩ : syracuseStep 3614291 = 5421437) B5421437
theorem B1353719 : Blo 842353 1353719 := bstep (se 1 (by rfl) ⟨1015289, by rfl⟩ : syracuseStep 1353719 = 2030579) B2030579
theorem B2140577 : Blo 842353 2140577 := bstep (se 2 (by rfl) ⟨802716, by rfl⟩ : syracuseStep 2140577 = 1605433) B1605433
theorem B13183397 : Blo 842353 13183397 := bstep (se 4 (by rfl) ⟨1235943, by rfl⟩ : syracuseStep 13183397 = 2471887) B2471887
theorem B2402921 : Blo 842353 2402921 := bstep (se 2 (by rfl) ⟨901095, by rfl⟩ : syracuseStep 2402921 = 1802191) B1802191
theorem B6400619 : Blo 842353 6400619 := bstep (se 1 (by rfl) ⟨4800464, by rfl⟩ : syracuseStep 6400619 = 9600929) B9600929
theorem B1158047 : Blo 842353 1158047 := bstep (se 1 (by rfl) ⟨868535, by rfl⟩ : syracuseStep 1158047 = 1737071) B1737071
theorem B1355591 : Blo 842353 1355591 := bstep (se 1 (by rfl) ⟨1016693, by rfl⟩ : syracuseStep 1355591 = 2033387) B2033387
theorem B92287025 : Blo 842353 92287025 := bstep (se 2 (by rfl) ⟨34607634, by rfl⟩ : syracuseStep 92287025 = 69215269) B69215269
theorem B1421543 : Blo 842353 1421543 := bstep (se 1 (by rfl) ⟨1066157, by rfl⟩ : syracuseStep 1421543 = 2132315) B2132315
theorem B8794423 : Blo 842353 8794423 := bstep (se 1 (by rfl) ⟨6595817, by rfl⟩ : syracuseStep 8794423 = 13191635) B13191635
theorem B2929007 : Blo 842353 2929007 := bstep (se 1 (by rfl) ⟨2196755, by rfl⟩ : syracuseStep 2929007 = 4393511) B4393511
theorem B1421705 : Blo 842353 1421705 := bstep (se 2 (by rfl) ⟨533139, by rfl⟩ : syracuseStep 1421705 = 1066279) B1066279
theorem B1422137 : Blo 842353 1422137 := bstep (se 2 (by rfl) ⟨533301, by rfl⟩ : syracuseStep 1422137 = 1066603) B1066603
theorem B1422191 : Blo 842353 1422191 := bstep (se 1 (by rfl) ⟨1066643, by rfl⟩ : syracuseStep 1422191 = 2133287) B2133287
theorem B5420105 : Blo 842353 5420105 := bstep (se 2 (by rfl) ⟨2032539, by rfl⟩ : syracuseStep 5420105 = 4065079) B4065079
theorem B1521223 : Blo 842353 1521223 := bstep (se 1 (by rfl) ⟨1140917, by rfl⟩ : syracuseStep 1521223 = 2281835) B2281835
theorem B4798187 : Blo 842353 4798187 := bstep (se 1 (by rfl) ⟨3598640, by rfl⟩ : syracuseStep 4798187 = 7197281) B7197281
theorem B1423183 : Blo 842353 1423183 := bstep (se 1 (by rfl) ⟨1067387, by rfl⟩ : syracuseStep 1423183 = 2134775) B2134775
theorem B10958813 : Blo 842353 10958813 := bstep (se 3 (by rfl) ⟨2054777, by rfl⟩ : syracuseStep 10958813 = 4109555) B4109555
theorem B6076397 : Blo 842353 6076397 := bstep (se 3 (by rfl) ⟨1139324, by rfl⟩ : syracuseStep 6076397 = 2278649) B2278649
theorem B1423595 : Blo 842353 1423595 := bstep (se 1 (by rfl) ⟨1067696, by rfl⟩ : syracuseStep 1423595 = 2135393) B2135393
theorem B23148823 : Blo 842353 23148823 := bstep (se 1 (by rfl) ⟨17361617, by rfl⟩ : syracuseStep 23148823 = 34723235) B34723235
theorem B16267999 : Blo 842353 16267999 := bstep (se 1 (by rfl) ⟨12200999, by rfl⟩ : syracuseStep 16267999 = 24401999) B24401999
theorem B11123459 : Blo 842353 11123459 := bstep (se 1 (by rfl) ⟨8342594, by rfl⟩ : syracuseStep 11123459 = 16685189) B16685189
theorem B6077263 : Blo 842353 6077263 := bstep (se 1 (by rfl) ⟨4557947, by rfl⟩ : syracuseStep 6077263 = 9115895) B9115895
theorem B1424425 : Blo 842353 1424425 := bstep (se 2 (by rfl) ⟨534159, by rfl⟩ : syracuseStep 1424425 = 1068319) B1068319
theorem B4799645 : Blo 842353 4799645 := bstep (se 3 (by rfl) ⟨899933, by rfl⟩ : syracuseStep 4799645 = 1799867) B1799867
theorem B1424567 : Blo 842353 1424567 := bstep (se 1 (by rfl) ⟨1068425, by rfl⟩ : syracuseStep 1424567 = 2136851) B2136851
theorem B2407819 : Blo 842353 2407819 := bstep (se 1 (by rfl) ⟨1805864, by rfl⟩ : syracuseStep 2407819 = 3611729) B3611729
theorem B2309543 : Blo 842353 2309543 := bstep (se 1 (by rfl) ⟨1732157, by rfl⟩ : syracuseStep 2309543 = 3464315) B3464315
theorem B5422565 : Blo 842353 5422565 := bstep (se 4 (by rfl) ⟨508365, by rfl⟩ : syracuseStep 5422565 = 1016731) B1016731
theorem B1424891 : Blo 842353 1424891 := bstep (se 1 (by rfl) ⟨1068668, by rfl⟩ : syracuseStep 1424891 = 2137337) B2137337
theorem B1523195 : Blo 842353 1523195 := bstep (se 1 (by rfl) ⟨1142396, by rfl⟩ : syracuseStep 1523195 = 2284793) B2284793
theorem B8764973 : Blo 842353 8764973 := bstep (se 3 (by rfl) ⟨1643432, by rfl⟩ : syracuseStep 8764973 = 3286865) B3286865
theorem B2702927 : Blo 842353 2702927 := bstep (se 1 (by rfl) ⟨2027195, by rfl⟩ : syracuseStep 2702927 = 4054391) B4054391
theorem B5193559 : Blo 842353 5193559 := bstep (se 1 (by rfl) ⟨3895169, by rfl⟩ : syracuseStep 5193559 = 7790339) B7790339
theorem B4570967 : Blo 842353 4570967 := bstep (se 1 (by rfl) ⟨3428225, by rfl⟩ : syracuseStep 4570967 = 6856451) B6856451
theorem B1425323 : Blo 842353 1425323 := bstep (se 1 (by rfl) ⟨1068992, by rfl⟩ : syracuseStep 1425323 = 2137985) B2137985
theorem B30818393 : Blo 842353 30818393 := bstep (se 2 (by rfl) ⟨11556897, by rfl⟩ : syracuseStep 30818393 = 23113795) B23113795
theorem B1425863 : Blo 842353 1425863 := bstep (se 1 (by rfl) ⟨1069397, by rfl⟩ : syracuseStep 1425863 = 2138795) B2138795
theorem B4276799 : Blo 842353 4276799 := bstep (se 1 (by rfl) ⟨3207599, by rfl⟩ : syracuseStep 4276799 = 6415199) B6415199
theorem B8111015 : Blo 842353 8111015 := bstep (se 1 (by rfl) ⟨6083261, by rfl⟩ : syracuseStep 8111015 = 12166523) B12166523
theorem B4637627 : Blo 842353 4637627 := bstep (se 1 (by rfl) ⟨3478220, by rfl⟩ : syracuseStep 4637627 = 6956441) B6956441
theorem B1426639 : Blo 842353 1426639 := bstep (se 1 (by rfl) ⟨1069979, by rfl⟩ : syracuseStep 1426639 = 2139959) B2139959
theorem B6014341 : Blo 842353 6014341 := bstep (se 4 (by rfl) ⟨563844, by rfl⟩ : syracuseStep 6014341 = 1127689) B1127689
theorem B4278095 : Blo 842353 4278095 := bstep (se 1 (by rfl) ⟨3208571, by rfl⟩ : syracuseStep 4278095 = 6417143) B6417143
theorem B1263599 : Blo 842353 1263599 := bstep (se 1 (by rfl) ⟨947699, by rfl⟩ : syracuseStep 1263599 = 1895399) B1895399
theorem B1427449 : Blo 842353 1427449 := bstep (se 2 (by rfl) ⟨535293, by rfl⟩ : syracuseStep 1427449 = 1070587) B1070587
theorem B1427611 : Blo 842353 1427611 := bstep (se 1 (by rfl) ⟨1070708, by rfl⟩ : syracuseStep 1427611 = 2141417) B2141417
theorem B1263851 : Blo 842353 1263851 := bstep (se 1 (by rfl) ⟨947888, by rfl⟩ : syracuseStep 1263851 = 1895777) B1895777
theorem B1427719 : Blo 842353 1427719 := bstep (se 1 (by rfl) ⟨1070789, by rfl⟩ : syracuseStep 1427719 = 2141579) B2141579
theorem B1263911 : Blo 842353 1263911 := bstep (se 1 (by rfl) ⟨947933, by rfl⟩ : syracuseStep 1263911 = 1895867) B1895867
theorem B1427753 : Blo 842353 1427753 := bstep (se 2 (by rfl) ⟨535407, by rfl⟩ : syracuseStep 1427753 = 1070815) B1070815
theorem B1263995 : Blo 842353 1263995 := bstep (se 1 (by rfl) ⟨947996, by rfl⟩ : syracuseStep 1263995 = 1895993) B1895993
theorem B2705825 : Blo 842353 2705825 := bstep (se 2 (by rfl) ⟨1014684, by rfl⟩ : syracuseStep 2705825 = 2029369) B2029369
theorem B1264265 : Blo 842353 1264265 := bstep (se 2 (by rfl) ⟨474099, by rfl⟩ : syracuseStep 1264265 = 948199) B948199
theorem B7719563 : Blo 842353 7719563 := bstep (se 1 (by rfl) ⟨5789672, by rfl⟩ : syracuseStep 7719563 = 11579345) B11579345
theorem B1264439 : Blo 842353 1264439 := bstep (se 1 (by rfl) ⟨948329, by rfl⟩ : syracuseStep 1264439 = 1896659) B1896659
theorem B1264475 : Blo 842353 1264475 := bstep (se 1 (by rfl) ⟨948356, by rfl⟩ : syracuseStep 1264475 = 1896713) B1896713
theorem B1264619 : Blo 842353 1264619 := bstep (se 1 (by rfl) ⟨948464, by rfl⟩ : syracuseStep 1264619 = 1896929) B1896929
theorem B1264823 : Blo 842353 1264823 := bstep (se 1 (by rfl) ⟨948617, by rfl⟩ : syracuseStep 1264823 = 1897235) B1897235
theorem B1265063 : Blo 842353 1265063 := bstep (se 1 (by rfl) ⟨948797, by rfl⟩ : syracuseStep 1265063 = 1897595) B1897595
theorem B2313641 : Blo 842353 2313641 := bstep (se 2 (by rfl) ⟨867615, by rfl⟩ : syracuseStep 2313641 = 1735231) B1735231
theorem B1265147 : Blo 842353 1265147 := bstep (se 1 (by rfl) ⟨948860, by rfl⟩ : syracuseStep 1265147 = 1897721) B1897721
theorem B1265243 : Blo 842353 1265243 := bstep (se 1 (by rfl) ⟨948932, by rfl⟩ : syracuseStep 1265243 = 1897865) B1897865
theorem B4804271 : Blo 842353 4804271 := bstep (se 1 (by rfl) ⟨3603203, by rfl⟩ : syracuseStep 4804271 = 7206407) B7206407
theorem B1265327 : Blo 842353 1265327 := bstep (se 1 (by rfl) ⟨948995, by rfl⟩ : syracuseStep 1265327 = 1897991) B1897991
theorem B1265447 : Blo 842353 1265447 := bstep (se 1 (by rfl) ⟨949085, by rfl⟩ : syracuseStep 1265447 = 1898171) B1898171
theorem B2740007 : Blo 842353 2740007 := bstep (se 1 (by rfl) ⟨2055005, by rfl⟩ : syracuseStep 2740007 = 4110011) B4110011
theorem B1068871 : Blo 842353 1068871 := bstep (se 1 (by rfl) ⟨801653, by rfl⟩ : syracuseStep 1068871 = 1603307) B1603307
theorem B1265531 : Blo 842353 1265531 := bstep (se 1 (by rfl) ⟨949148, by rfl⟩ : syracuseStep 1265531 = 1898297) B1898297
theorem B2707643 : Blo 842353 2707643 := bstep (se 1 (by rfl) ⟨2030732, by rfl⟩ : syracuseStep 2707643 = 4061465) B4061465
theorem B1265951 : Blo 842353 1265951 := bstep (se 1 (by rfl) ⟨949463, by rfl⟩ : syracuseStep 1265951 = 1898927) B1898927
theorem B10801457 : Blo 842353 10801457 := bstep (se 2 (by rfl) ⟨4050546, by rfl⟩ : syracuseStep 10801457 = 8101093) B8101093
theorem B1265975 : Blo 842353 1265975 := bstep (se 1 (by rfl) ⟨949481, by rfl⟩ : syracuseStep 1265975 = 1898963) B1898963
theorem B4280687 : Blo 842353 4280687 := bstep (se 1 (by rfl) ⟨3210515, by rfl⟩ : syracuseStep 4280687 = 6421031) B6421031
theorem B1266047 : Blo 842353 1266047 := bstep (se 1 (by rfl) ⟨949535, by rfl⟩ : syracuseStep 1266047 = 1899071) B1899071
theorem B1200521 : Blo 842353 1200521 := bstep (se 2 (by rfl) ⟨450195, by rfl⟩ : syracuseStep 1200521 = 900391) B900391
theorem B1266119 : Blo 842353 1266119 := bstep (se 1 (by rfl) ⟨949589, by rfl⟩ : syracuseStep 1266119 = 1899179) B1899179
theorem B1069519 : Blo 842353 1069519 := bstep (se 1 (by rfl) ⟨802139, by rfl⟩ : syracuseStep 1069519 = 1604279) B1604279
theorem B69194243 : Blo 842353 69194243 := bstep (se 1 (by rfl) ⟨51895682, by rfl⟩ : syracuseStep 69194243 = 103791365) B103791365
theorem B1266473 : Blo 842353 1266473 := bstep (se 2 (by rfl) ⟨474927, by rfl⟩ : syracuseStep 1266473 = 949855) B949855
theorem B1266479 : Blo 842353 1266479 := bstep (se 1 (by rfl) ⟨949859, by rfl⟩ : syracuseStep 1266479 = 1899719) B1899719
theorem B1266599 : Blo 842353 1266599 := bstep (se 1 (by rfl) ⟨949949, by rfl⟩ : syracuseStep 1266599 = 1899899) B1899899
theorem B7197659 : Blo 842353 7197659 := bstep (se 1 (by rfl) ⟨5398244, by rfl⟩ : syracuseStep 7197659 = 10796489) B10796489
theorem B1266683 : Blo 842353 1266683 := bstep (se 1 (by rfl) ⟨950012, by rfl⟩ : syracuseStep 1266683 = 1900025) B1900025
theorem B1266743 : Blo 842353 1266743 := bstep (se 1 (by rfl) ⟨950057, by rfl⟩ : syracuseStep 1266743 = 1900115) B1900115
theorem B4805729 : Blo 842353 4805729 := bstep (se 2 (by rfl) ⟨1802148, by rfl⟩ : syracuseStep 4805729 = 3604297) B3604297
theorem B2282671 : Blo 842353 2282671 := bstep (se 1 (by rfl) ⟨1712003, by rfl⟩ : syracuseStep 2282671 = 3424007) B3424007
theorem B1266863 : Blo 842353 1266863 := bstep (se 1 (by rfl) ⟨950147, by rfl⟩ : syracuseStep 1266863 = 1900295) B1900295
theorem B3200219 : Blo 842353 3200219 := bstep (se 1 (by rfl) ⟨2400164, by rfl⟩ : syracuseStep 3200219 = 4800329) B4800329
theorem B1070491 : Blo 842353 1070491 := bstep (se 1 (by rfl) ⟨802868, by rfl⟩ : syracuseStep 1070491 = 1605737) B1605737
theorem B1463879 : Blo 842353 1463879 := bstep (se 1 (by rfl) ⟨1097909, by rfl⟩ : syracuseStep 1463879 = 2195819) B2195819
theorem B1267271 : Blo 842353 1267271 := bstep (se 1 (by rfl) ⟨950453, by rfl⟩ : syracuseStep 1267271 = 1900907) B1900907
theorem B8115821 : Blo 842353 8115821 := bstep (se 3 (by rfl) ⟨1521716, by rfl⟩ : syracuseStep 8115821 = 3043433) B3043433
theorem B1267367 : Blo 842353 1267367 := bstep (se 1 (by rfl) ⟨950525, by rfl⟩ : syracuseStep 1267367 = 1901051) B1901051
theorem B1070759 : Blo 842353 1070759 := bstep (se 1 (by rfl) ⟨803069, by rfl⟩ : syracuseStep 1070759 = 1606139) B1606139
theorem B2283191 : Blo 842353 2283191 := bstep (se 1 (by rfl) ⟨1712393, by rfl⟩ : syracuseStep 2283191 = 3424787) B3424787
theorem B1267451 : Blo 842353 1267451 := bstep (se 1 (by rfl) ⟨950588, by rfl⟩ : syracuseStep 1267451 = 1901177) B1901177
theorem B1267487 : Blo 842353 1267487 := bstep (se 1 (by rfl) ⟨950615, by rfl⟩ : syracuseStep 1267487 = 1901231) B1901231
theorem B1070911 : Blo 842353 1070911 := bstep (se 1 (by rfl) ⟨803183, by rfl⟩ : syracuseStep 1070911 = 1606367) B1606367
theorem B1267535 : Blo 842353 1267535 := bstep (se 1 (by rfl) ⟨950651, by rfl⟩ : syracuseStep 1267535 = 1901303) B1901303
theorem B1267655 : Blo 842353 1267655 := bstep (se 1 (by rfl) ⟨950741, by rfl⟩ : syracuseStep 1267655 = 1901483) B1901483
theorem B1268009 : Blo 842353 1268009 := bstep (se 2 (by rfl) ⟨475503, by rfl⟩ : syracuseStep 1268009 = 951007) B951007
theorem B1268015 : Blo 842353 1268015 := bstep (se 1 (by rfl) ⟨951011, by rfl⟩ : syracuseStep 1268015 = 1902023) B1902023
theorem B2742601 : Blo 842353 2742601 := bstep (se 2 (by rfl) ⟨1028475, by rfl⟩ : syracuseStep 2742601 = 2056951) B2056951
theorem B3201403 : Blo 842353 3201403 := bstep (se 1 (by rfl) ⟨2401052, by rfl⟩ : syracuseStep 3201403 = 4802105) B4802105
theorem B1268255 : Blo 842353 1268255 := bstep (se 1 (by rfl) ⟨951191, by rfl⟩ : syracuseStep 1268255 = 1902383) B1902383
theorem B6085277 : Blo 842353 6085277 := bstep (se 3 (by rfl) ⟨1140989, by rfl⟩ : syracuseStep 6085277 = 2281979) B2281979
theorem B20798209 : Blo 842353 20798209 := bstep (se 2 (by rfl) ⟨7799328, by rfl⟩ : syracuseStep 20798209 = 15598657) B15598657
theorem B3201875 : Blo 842353 3201875 := bstep (se 1 (by rfl) ⟨2401406, by rfl⟩ : syracuseStep 3201875 = 4802813) B4802813
theorem B842587 : Blo 842353 842587 := bstep (se 1 (by rfl) ⟨631940, by rfl⟩ : syracuseStep 842587 = 1263881) B1263881
theorem B10836827 : Blo 842353 10836827 := bstep (se 1 (by rfl) ⟨8127620, by rfl⟩ : syracuseStep 10836827 = 16255241) B16255241
theorem B842655 : Blo 842353 842655 := bstep (se 1 (by rfl) ⟨631991, by rfl⟩ : syracuseStep 842655 = 1263983) B1263983
theorem B1268639 : Blo 842353 1268639 := bstep (se 1 (by rfl) ⟨951479, by rfl⟩ : syracuseStep 1268639 = 1902959) B1902959
theorem B1268687 : Blo 842353 1268687 := bstep (se 1 (by rfl) ⟨951515, by rfl⟩ : syracuseStep 1268687 = 1903031) B1903031
theorem B1268777 : Blo 842353 1268777 := bstep (se 2 (by rfl) ⟨475791, by rfl⟩ : syracuseStep 1268777 = 951583) B951583
theorem B842799 : Blo 842353 842799 := bstep (se 1 (by rfl) ⟨632099, by rfl⟩ : syracuseStep 842799 = 1264199) B1264199
theorem B1268783 : Blo 842353 1268783 := bstep (se 1 (by rfl) ⟨951587, by rfl⟩ : syracuseStep 1268783 = 1903175) B1903175
theorem B14605379 : Blo 842353 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B842823 : Blo 842353 842823 := bstep (se 1 (by rfl) ⟨632117, by rfl⟩ : syracuseStep 842823 = 1264235) B1264235
theorem B1268807 : Blo 842353 1268807 := bstep (se 1 (by rfl) ⟨951605, by rfl⟩ : syracuseStep 1268807 = 1903211) B1903211
theorem B842975 : Blo 842353 842975 := bstep (se 1 (by rfl) ⟨632231, by rfl⟩ : syracuseStep 842975 = 1264463) B1264463
theorem B1269071 : Blo 842353 1269071 := bstep (se 1 (by rfl) ⟨951803, by rfl⟩ : syracuseStep 1269071 = 1903607) B1903607
theorem B1269161 : Blo 842353 1269161 := bstep (se 2 (by rfl) ⟨475935, by rfl⟩ : syracuseStep 1269161 = 951871) B951871
theorem B6086087 : Blo 842353 6086087 := bstep (se 1 (by rfl) ⟨4564565, by rfl⟩ : syracuseStep 6086087 = 9129131) B9129131
theorem B843239 : Blo 842353 843239 := bstep (se 1 (by rfl) ⟨632429, by rfl⟩ : syracuseStep 843239 = 1264859) B1264859
theorem B2711015 : Blo 842353 2711015 := bstep (se 1 (by rfl) ⟨2033261, by rfl⟩ : syracuseStep 2711015 = 4066523) B4066523
theorem B1269311 : Blo 842353 1269311 := bstep (se 1 (by rfl) ⟨951983, by rfl⟩ : syracuseStep 1269311 = 1903967) B1903967
theorem B843355 : Blo 842353 843355 := bstep (se 1 (by rfl) ⟨632516, by rfl⟩ : syracuseStep 843355 = 1265033) B1265033
theorem B843591 : Blo 842353 843591 := bstep (se 1 (by rfl) ⟨632693, by rfl⟩ : syracuseStep 843591 = 1265387) B1265387
theorem B843743 : Blo 842353 843743 := bstep (se 1 (by rfl) ⟨632807, by rfl⟩ : syracuseStep 843743 = 1265615) B1265615
theorem B844007 : Blo 842353 844007 := bstep (se 1 (by rfl) ⟨633005, by rfl⟩ : syracuseStep 844007 = 1266011) B1266011
theorem B3760415 : Blo 842353 3760415 := bstep (se 1 (by rfl) ⟨2820311, by rfl⟩ : syracuseStep 3760415 = 5640623) B5640623
theorem B56222029 : Blo 842353 56222029 := bstep (se 3 (by rfl) ⟨10541630, by rfl⟩ : syracuseStep 56222029 = 21083261) B21083261
theorem B844159 : Blo 842353 844159 := bstep (se 1 (by rfl) ⟨633119, by rfl⟩ : syracuseStep 844159 = 1266239) B1266239
theorem B844239 : Blo 842353 844239 := bstep (se 1 (by rfl) ⟨633179, by rfl⟩ : syracuseStep 844239 = 1266359) B1266359
theorem B844391 : Blo 842353 844391 := bstep (se 1 (by rfl) ⟨633293, by rfl⟩ : syracuseStep 844391 = 1266587) B1266587
theorem B5399293 : Blo 842353 5399293 := bstep (se 3 (by rfl) ⟨1012367, by rfl⟩ : syracuseStep 5399293 = 2024735) B2024735
theorem B1368839 : Blo 842353 1368839 := bstep (se 1 (by rfl) ⟨1026629, by rfl⟩ : syracuseStep 1368839 = 2053259) B2053259
theorem B844655 : Blo 842353 844655 := bstep (se 1 (by rfl) ⟨633491, by rfl⟩ : syracuseStep 844655 = 1266983) B1266983
theorem B844711 : Blo 842353 844711 := bstep (se 1 (by rfl) ⟨633533, by rfl⟩ : syracuseStep 844711 = 1267067) B1267067
theorem B844795 : Blo 842353 844795 := bstep (se 1 (by rfl) ⟨633596, by rfl⟩ : syracuseStep 844795 = 1267193) B1267193
theorem B34628651 : Blo 842353 34628651 := bstep (se 1 (by rfl) ⟨25971488, by rfl⟩ : syracuseStep 34628651 = 51942977) B51942977
theorem B844863 : Blo 842353 844863 := bstep (se 1 (by rfl) ⟨633647, by rfl⟩ : syracuseStep 844863 = 1267295) B1267295
theorem B4809851 : Blo 842353 4809851 := bstep (se 1 (by rfl) ⟨3607388, by rfl⟩ : syracuseStep 4809851 = 7214777) B7214777
theorem B2843855 : Blo 842353 2843855 := bstep (se 1 (by rfl) ⟨2132891, by rfl⟩ : syracuseStep 2843855 = 4265783) B4265783
theorem B3335375 : Blo 842353 3335375 := bstep (se 1 (by rfl) ⟨2501531, by rfl⟩ : syracuseStep 3335375 = 5003063) B5003063
theorem B845007 : Blo 842353 845007 := bstep (se 1 (by rfl) ⟨633755, by rfl⟩ : syracuseStep 845007 = 1267511) B1267511
theorem B6514057 : Blo 842353 6514057 := bstep (se 2 (by rfl) ⟨2442771, by rfl⟩ : syracuseStep 6514057 = 4885543) B4885543
theorem B845211 : Blo 842353 845211 := bstep (se 1 (by rfl) ⟨633908, by rfl⟩ : syracuseStep 845211 = 1267817) B1267817
theorem B12182957 : Blo 842353 12182957 := bstep (se 3 (by rfl) ⟨2284304, by rfl⟩ : syracuseStep 12182957 = 4568609) B4568609
theorem B3204623 : Blo 842353 3204623 := bstep (se 1 (by rfl) ⟨2403467, by rfl⟩ : syracuseStep 3204623 = 4806935) B4806935
theorem B2844179 : Blo 842353 2844179 := bstep (se 1 (by rfl) ⟨2133134, by rfl⟩ : syracuseStep 2844179 = 4266269) B4266269
theorem B845423 : Blo 842353 845423 := bstep (se 1 (by rfl) ⟨634067, by rfl⟩ : syracuseStep 845423 = 1268135) B1268135
theorem B845479 : Blo 842353 845479 := bstep (se 1 (by rfl) ⟨634109, by rfl⟩ : syracuseStep 845479 = 1268219) B1268219
theorem B2746075 : Blo 842353 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B845563 : Blo 842353 845563 := bstep (se 1 (by rfl) ⟨634172, by rfl⟩ : syracuseStep 845563 = 1268345) B1268345
theorem B845599 : Blo 842353 845599 := bstep (se 1 (by rfl) ⟨634199, by rfl⟩ : syracuseStep 845599 = 1268399) B1268399
theorem B845631 : Blo 842353 845631 := bstep (se 1 (by rfl) ⟨634223, by rfl⟩ : syracuseStep 845631 = 1268447) B1268447
theorem B845807 : Blo 842353 845807 := bstep (se 1 (by rfl) ⟨634355, by rfl⟩ : syracuseStep 845807 = 1268711) B1268711
theorem B845979 : Blo 842353 845979 := bstep (se 1 (by rfl) ⟨634484, by rfl⟩ : syracuseStep 845979 = 1268969) B1268969
theorem B846015 : Blo 842353 846015 := bstep (se 1 (by rfl) ⟨634511, by rfl⟩ : syracuseStep 846015 = 1269023) B1269023
theorem B9595097 : Blo 842353 9595097 := bstep (se 2 (by rfl) ⟨3598161, by rfl⟩ : syracuseStep 9595097 = 7196323) B7196323
theorem B10283273 : Blo 842353 10283273 := bstep (se 2 (by rfl) ⟨3856227, by rfl⟩ : syracuseStep 10283273 = 7712455) B7712455
theorem B846127 : Blo 842353 846127 := bstep (se 1 (by rfl) ⟨634595, by rfl⟩ : syracuseStep 846127 = 1269191) B1269191
theorem B6843055 : Blo 842353 6843055 := bstep (se 1 (by rfl) ⟨5132291, by rfl⟩ : syracuseStep 6843055 = 10264583) B10264583
theorem B2845367 : Blo 842353 2845367 := bstep (se 1 (by rfl) ⟨2134025, by rfl⟩ : syracuseStep 2845367 = 4268051) B4268051
theorem B10840823 : Blo 842353 10840823 := bstep (se 1 (by rfl) ⟨8130617, by rfl⟩ : syracuseStep 10840823 = 16261235) B16261235
theorem B1895471 : Blo 842353 1895471 := bstep (se 1 (by rfl) ⟨1421603, by rfl⟩ : syracuseStep 1895471 = 2843207) B2843207
theorem B1895759 : Blo 842353 1895759 := bstep (se 1 (by rfl) ⟨1421819, by rfl⟩ : syracuseStep 1895759 = 2843639) B2843639
theorem B1895849 : Blo 842353 1895849 := bstep (se 2 (by rfl) ⟨710943, by rfl⟩ : syracuseStep 1895849 = 1421887) B1421887
theorem B1371791 : Blo 842353 1371791 := bstep (se 1 (by rfl) ⟨1028843, by rfl⟩ : syracuseStep 1371791 = 2057687) B2057687
theorem B1896335 : Blo 842353 1896335 := bstep (se 1 (by rfl) ⟨1422251, by rfl⟩ : syracuseStep 1896335 = 2844503) B2844503
theorem B4812767 : Blo 842353 4812767 := bstep (se 1 (by rfl) ⟨3609575, by rfl⟩ : syracuseStep 4812767 = 7219151) B7219151
theorem B9630089 : Blo 842353 9630089 := bstep (se 2 (by rfl) ⟨3611283, by rfl⟩ : syracuseStep 9630089 = 7222567) B7222567
theorem B7205345 : Blo 842353 7205345 := bstep (se 2 (by rfl) ⟨2702004, by rfl⟩ : syracuseStep 7205345 = 5404009) B5404009
theorem B2847311 : Blo 842353 2847311 := bstep (se 1 (by rfl) ⟨2135483, by rfl⟩ : syracuseStep 2847311 = 4270967) B4270967
theorem B1897055 : Blo 842353 1897055 := bstep (se 1 (by rfl) ⟨1422791, by rfl⟩ : syracuseStep 1897055 = 2845583) B2845583
theorem B8221601 : Blo 842353 8221601 := bstep (se 2 (by rfl) ⟨3083100, by rfl⟩ : syracuseStep 8221601 = 6166201) B6166201
theorem B2847851 : Blo 842353 2847851 := bstep (se 1 (by rfl) ⟨2135888, by rfl⟩ : syracuseStep 2847851 = 4271777) B4271777
theorem B1897883 : Blo 842353 1897883 := bstep (se 1 (by rfl) ⟨1423412, by rfl⟩ : syracuseStep 1897883 = 2846825) B2846825
theorem B3601921 : Blo 842353 3601921 := bstep (se 2 (by rfl) ⟨1350720, by rfl⟩ : syracuseStep 3601921 = 2701441) B2701441
theorem B1898459 : Blo 842353 1898459 := bstep (se 1 (by rfl) ⟨1423844, by rfl⟩ : syracuseStep 1898459 = 2847689) B2847689
theorem B3209179 : Blo 842353 3209179 := bstep (se 1 (by rfl) ⟨2406884, by rfl⟩ : syracuseStep 3209179 = 4813769) B4813769
theorem B7207055 : Blo 842353 7207055 := bstep (se 1 (by rfl) ⟨5405291, by rfl⟩ : syracuseStep 7207055 = 10810583) B10810583
theorem B1898639 : Blo 842353 1898639 := bstep (se 1 (by rfl) ⟨1423979, by rfl⟩ : syracuseStep 1898639 = 2847959) B2847959
theorem B948379 : Blo 842353 948379 := bstep (se 1 (by rfl) ⟨711284, by rfl⟩ : syracuseStep 948379 = 1422569) B1422569
theorem B1603739 : Blo 842353 1603739 := bstep (se 1 (by rfl) ⟨1202804, by rfl⟩ : syracuseStep 1603739 = 2405609) B2405609
theorem B1898657 : Blo 842353 1898657 := bstep (se 2 (by rfl) ⟨711996, by rfl⟩ : syracuseStep 1898657 = 1423993) B1423993
theorem B7698617 : Blo 842353 7698617 := bstep (se 2 (by rfl) ⟨2886981, by rfl⟩ : syracuseStep 7698617 = 5773963) B5773963
theorem B948415 : Blo 842353 948415 := bstep (se 1 (by rfl) ⟨711311, by rfl⟩ : syracuseStep 948415 = 1422623) B1422623
theorem B1898729 : Blo 842353 1898729 := bstep (se 2 (by rfl) ⟨712023, by rfl⟩ : syracuseStep 1898729 = 1424047) B1424047
theorem B2849147 : Blo 842353 2849147 := bstep (se 1 (by rfl) ⟨2136860, by rfl⟩ : syracuseStep 2849147 = 4273721) B4273721
theorem B2849417 : Blo 842353 2849417 := bstep (se 2 (by rfl) ⟨1068531, by rfl⟩ : syracuseStep 2849417 = 2137063) B2137063
theorem B4815683 : Blo 842353 4815683 := bstep (se 1 (by rfl) ⟨3611762, by rfl⟩ : syracuseStep 4815683 = 7223525) B7223525
theorem B23133061 : Blo 842353 23133061 := bstep (se 4 (by rfl) ⟨2168724, by rfl⟩ : syracuseStep 23133061 = 4337449) B4337449
theorem B6094273 : Blo 842353 6094273 := bstep (se 2 (by rfl) ⟨2285352, by rfl⟩ : syracuseStep 6094273 = 4570705) B4570705
theorem B1900007 : Blo 842353 1900007 := bstep (se 1 (by rfl) ⟨1425005, by rfl⟩ : syracuseStep 1900007 = 2850011) B2850011
theorem B2850551 : Blo 842353 2850551 := bstep (se 1 (by rfl) ⟨2137913, by rfl⟩ : syracuseStep 2850551 = 4275827) B4275827
theorem B12156713 : Blo 842353 12156713 := bstep (se 2 (by rfl) ⟨4558767, by rfl⟩ : syracuseStep 12156713 = 9117535) B9117535
theorem B20545595 : Blo 842353 20545595 := bstep (se 1 (by rfl) ⟨15409196, by rfl⟩ : syracuseStep 20545595 = 30818393) B30818393
theorem B950575 : Blo 842353 950575 := bstep (se 1 (by rfl) ⟨712931, by rfl⟩ : syracuseStep 950575 = 1425863) B1425863
theorem B2851199 : Blo 842353 2851199 := bstep (se 1 (by rfl) ⟨2138399, by rfl⟩ : syracuseStep 2851199 = 4276799) B4276799
theorem B1901087 : Blo 842353 1901087 := bstep (se 1 (by rfl) ⟨1425815, by rfl⟩ : syracuseStep 1901087 = 2851631) B2851631
theorem B1901159 : Blo 842353 1901159 := bstep (se 1 (by rfl) ⟨1425869, by rfl⟩ : syracuseStep 1901159 = 2851739) B2851739
theorem B5407343 : Blo 842353 5407343 := bstep (se 1 (by rfl) ⟨4055507, by rfl⟩ : syracuseStep 5407343 = 8111015) B8111015
theorem B16253783 : Blo 842353 16253783 := bstep (se 1 (by rfl) ⟨12190337, by rfl⟩ : syracuseStep 16253783 = 24380675) B24380675
theorem B2852063 : Blo 842353 2852063 := bstep (se 1 (by rfl) ⟨2139047, by rfl⟩ : syracuseStep 2852063 = 4278095) B4278095
theorem B1901915 : Blo 842353 1901915 := bstep (se 1 (by rfl) ⟨1426436, by rfl⟩ : syracuseStep 1901915 = 2852873) B2852873
theorem B951835 : Blo 842353 951835 := bstep (se 1 (by rfl) ⟨713876, by rfl⟩ : syracuseStep 951835 = 1427753) B1427753
theorem B4064849 : Blo 842353 4064849 := bstep (se 2 (by rfl) ⟨1524318, by rfl⟩ : syracuseStep 4064849 = 3048637) B3048637
theorem B1902185 : Blo 842353 1902185 := bstep (se 2 (by rfl) ⟨713319, by rfl⟩ : syracuseStep 1902185 = 1426639) B1426639
theorem B1803883 : Blo 842353 1803883 := bstep (se 1 (by rfl) ⟨1352912, by rfl⟩ : syracuseStep 1803883 = 2705825) B2705825
theorem B3213067 : Blo 842353 3213067 := bstep (se 1 (by rfl) ⟨2409800, by rfl⟩ : syracuseStep 3213067 = 4819601) B4819601
theorem B8685409 : Blo 842353 8685409 := bstep (se 2 (by rfl) ⟨3257028, by rfl⟩ : syracuseStep 8685409 = 6514057) B6514057
theorem B1902779 : Blo 842353 1902779 := bstep (se 1 (by rfl) ⟨1427084, by rfl⟩ : syracuseStep 1902779 = 2854169) B2854169
theorem B1902815 : Blo 842353 1902815 := bstep (se 1 (by rfl) ⟨1427111, by rfl⟩ : syracuseStep 1902815 = 2854223) B2854223
theorem B7211429 : Blo 842353 7211429 := bstep (se 4 (by rfl) ⟨676071, by rfl⟩ : syracuseStep 7211429 = 1352143) B1352143
theorem B1903265 : Blo 842353 1903265 := bstep (se 2 (by rfl) ⟨713724, by rfl⟩ : syracuseStep 1903265 = 1427449) B1427449
theorem B1805095 : Blo 842353 1805095 := bstep (se 1 (by rfl) ⟨1353821, by rfl⟩ : syracuseStep 1805095 = 2707643) B2707643
theorem B1903481 : Blo 842353 1903481 := bstep (se 2 (by rfl) ⟨713805, by rfl⟩ : syracuseStep 1903481 = 1427611) B1427611
theorem B2853791 : Blo 842353 2853791 := bstep (se 1 (by rfl) ⟨2140343, by rfl⟩ : syracuseStep 2853791 = 4280687) B4280687
theorem B1903625 : Blo 842353 1903625 := bstep (se 2 (by rfl) ⟨713859, by rfl⟩ : syracuseStep 1903625 = 1427719) B1427719
theorem B1903679 : Blo 842353 1903679 := bstep (se 1 (by rfl) ⟨1427759, by rfl⟩ : syracuseStep 1903679 = 2855519) B2855519
theorem B4328569 : Blo 842353 4328569 := bstep (se 2 (by rfl) ⟨1623213, by rfl⟩ : syracuseStep 4328569 = 3246427) B3246427
theorem B2133479 : Blo 842353 2133479 := bstep (se 1 (by rfl) ⟨1600109, by rfl⟩ : syracuseStep 2133479 = 3200219) B3200219
theorem B5410547 : Blo 842353 5410547 := bstep (se 1 (by rfl) ⟨4057910, by rfl⟩ : syracuseStep 5410547 = 8115821) B8115821
theorem B3903677 : Blo 842353 3903677 := bstep (se 3 (by rfl) ⟨731939, by rfl⟩ : syracuseStep 3903677 = 1463879) B1463879
theorem B2855357 : Blo 842353 2855357 := bstep (se 3 (by rfl) ⟨535379, by rfl⟩ : syracuseStep 2855357 = 1070759) B1070759
theorem B2134583 : Blo 842353 2134583 := bstep (se 1 (by rfl) ⟨1600937, by rfl⟩ : syracuseStep 2134583 = 3201875) B3201875
theorem B9736919 : Blo 842353 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B1807343 : Blo 842353 1807343 := bstep (se 1 (by rfl) ⟨1355507, by rfl⟩ : syracuseStep 1807343 = 2711015) B2711015
theorem B3609917 : Blo 842353 3609917 := bstep (se 3 (by rfl) ⟨676859, by rfl⟩ : syracuseStep 3609917 = 1353719) B1353719
theorem B27400355 : Blo 842353 27400355 := bstep (se 1 (by rfl) ⟨20550266, by rfl⟩ : syracuseStep 27400355 = 41100533) B41100533
theorem B2136415 : Blo 842353 2136415 := bstep (se 1 (by rfl) ⟨1602311, by rfl⟩ : syracuseStep 2136415 = 3204623) B3204623
theorem B6396731 : Blo 842353 6396731 := bstep (se 1 (by rfl) ⟨4797548, by rfl⟩ : syracuseStep 6396731 = 9595097) B9595097
theorem B6855515 : Blo 842353 6855515 := bstep (se 1 (by rfl) ⟨5141636, by rfl⟩ : syracuseStep 6855515 = 10283273) B10283273
theorem B5774273 : Blo 842353 5774273 := bstep (se 2 (by rfl) ⟨2165352, by rfl⟩ : syracuseStep 5774273 = 4330705) B4330705
theorem B8788931 : Blo 842353 8788931 := bstep (se 1 (by rfl) ⟨6591698, by rfl⟩ : syracuseStep 8788931 = 13183397) B13183397
theorem B20585501 : Blo 842353 20585501 := bstep (se 3 (by rfl) ⟨3859781, by rfl⟩ : syracuseStep 20585501 = 7719563) B7719563
theorem B4267079 : Blo 842353 4267079 := bstep (se 1 (by rfl) ⟨3200309, by rfl⟩ : syracuseStep 4267079 = 6400619) B6400619
theorem B1711225 : Blo 842353 1711225 := bstep (se 2 (by rfl) ⟨641709, by rfl⟩ : syracuseStep 1711225 = 1283419) B1283419
theorem B4268537 : Blo 842353 4268537 := bstep (se 2 (by rfl) ⟨1600701, by rfl⟩ : syracuseStep 4268537 = 3201403) B3201403
theorem B5481067 : Blo 842353 5481067 := bstep (se 1 (by rfl) ⟨4110800, by rfl⟩ : syracuseStep 5481067 = 8221601) B8221601
theorem B3613403 : Blo 842353 3613403 := bstep (se 1 (by rfl) ⟨2710052, by rfl⟩ : syracuseStep 3613403 = 5420105) B5420105
theorem B27730945 : Blo 842353 27730945 := bstep (se 2 (by rfl) ⟨10399104, by rfl⟩ : syracuseStep 27730945 = 20798209) B20798209
theorem B8103017 : Blo 842353 8103017 := bstep (se 2 (by rfl) ⟨3038631, by rfl⟩ : syracuseStep 8103017 = 6077263) B6077263
theorem B6169709 : Blo 842353 6169709 := bstep (se 3 (by rfl) ⟨1156820, by rfl⟩ : syracuseStep 6169709 = 2313641) B2313641
theorem B30844081 : Blo 842353 30844081 := bstep (se 2 (by rfl) ⟨11566530, by rfl⟩ : syracuseStep 30844081 = 23133061) B23133061
theorem B7415639 : Blo 842353 7415639 := bstep (se 1 (by rfl) ⟨5561729, by rfl⟩ : syracuseStep 7415639 = 11123459) B11123459
theorem B3615043 : Blo 842353 3615043 := bstep (se 1 (by rfl) ⟨2711282, by rfl⟩ : syracuseStep 3615043 = 5422565) B5422565
theorem B5843315 : Blo 842353 5843315 := bstep (se 1 (by rfl) ⟨4382486, by rfl⟩ : syracuseStep 5843315 = 8764973) B8764973
theorem B6924745 : Blo 842353 6924745 := bstep (se 2 (by rfl) ⟨2596779, by rfl⟩ : syracuseStep 6924745 = 5193559) B5193559
theorem B8104475 : Blo 842353 8104475 := bstep (se 1 (by rfl) ⟨6078356, by rfl⟩ : syracuseStep 8104475 = 12156713) B12156713
theorem B2141225 : Blo 842353 2141225 := bstep (se 2 (by rfl) ⟨802959, by rfl⟩ : syracuseStep 2141225 = 1605919) B1605919
theorem B2141255 : Blo 842353 2141255 := bstep (se 1 (by rfl) ⟨1605941, by rfl⟩ : syracuseStep 2141255 = 3211883) B3211883
theorem B3091751 : Blo 842353 3091751 := bstep (se 1 (by rfl) ⟨2318813, by rfl⟩ : syracuseStep 3091751 = 4637627) B4637627
theorem B9743753 : Blo 842353 9743753 := bstep (se 2 (by rfl) ⟨3653907, by rfl⟩ : syracuseStep 9743753 = 7307815) B7307815
theorem B32452757 : Blo 842353 32452757 := bstep (se 6 (by rfl) ⟨760611, by rfl⟩ : syracuseStep 32452757 = 1521223) B1521223
theorem B1421671 : Blo 842353 1421671 := bstep (se 1 (by rfl) ⟨1066253, by rfl⟩ : syracuseStep 1421671 = 2132507) B2132507
theorem B3650237 : Blo 842353 3650237 := bstep (se 3 (by rfl) ⟨684419, by rfl⟩ : syracuseStep 3650237 = 1368839) B1368839
theorem B1422407 : Blo 842353 1422407 := bstep (se 1 (by rfl) ⟨1066805, by rfl⟩ : syracuseStep 1422407 = 2133611) B2133611
theorem B8894333 : Blo 842353 8894333 := bstep (se 3 (by rfl) ⟨1667687, by rfl⟩ : syracuseStep 8894333 = 3335375) B3335375
theorem B4798439 : Blo 842353 4798439 := bstep (se 1 (by rfl) ⟨3598829, by rfl⟩ : syracuseStep 4798439 = 7197659) B7197659
theorem B9124073 : Blo 842353 9124073 := bstep (se 2 (by rfl) ⟨3421527, by rfl⟩ : syracuseStep 9124073 = 6843055) B6843055
theorem B2406635 : Blo 842353 2406635 := bstep (se 1 (by rfl) ⟨1804976, by rfl⟩ : syracuseStep 2406635 = 3609953) B3609953
theorem B1522127 : Blo 842353 1522127 := bstep (se 1 (by rfl) ⟨1141595, by rfl⟩ : syracuseStep 1522127 = 2283191) B2283191
theorem B7224551 : Blo 842353 7224551 := bstep (se 1 (by rfl) ⟨5418413, by rfl⟩ : syracuseStep 7224551 = 10836827) B10836827
theorem B900839 : Blo 842353 900839 := bstep (se 1 (by rfl) ⟨675629, by rfl⟩ : syracuseStep 900839 = 1351259) B1351259
theorem B1425127 : Blo 842353 1425127 := bstep (se 1 (by rfl) ⟨1068845, by rfl⟩ : syracuseStep 1425127 = 2137691) B2137691
theorem B1425161 : Blo 842353 1425161 := bstep (se 2 (by rfl) ⟨534435, by rfl⟩ : syracuseStep 1425161 = 1068871) B1068871
theorem B16203725 : Blo 842353 16203725 := bstep (se 3 (by rfl) ⟨3038198, by rfl⟩ : syracuseStep 16203725 = 6076397) B6076397
theorem B2506943 : Blo 842353 2506943 := bstep (se 1 (by rfl) ⟨1880207, by rfl⟩ : syracuseStep 2506943 = 3760415) B3760415
theorem B4276637 : Blo 842353 4276637 := bstep (se 3 (by rfl) ⟨801869, by rfl⟩ : syracuseStep 4276637 = 1603739) B1603739
theorem B1426025 : Blo 842353 1426025 := bstep (se 2 (by rfl) ⟨534759, by rfl⟩ : syracuseStep 1426025 = 1069519) B1069519
theorem B23085767 : Blo 842353 23085767 := bstep (se 1 (by rfl) ⟨17314325, by rfl⟩ : syracuseStep 23085767 = 34628651) B34628651
theorem B3851027 : Blo 842353 3851027 := bstep (se 1 (by rfl) ⟨2888270, by rfl⟩ : syracuseStep 3851027 = 5776541) B5776541
theorem B12174245 : Blo 842353 12174245 := bstep (se 4 (by rfl) ⟨1141335, by rfl⟩ : syracuseStep 12174245 = 2282671) B2282671
theorem B2409527 : Blo 842353 2409527 := bstep (se 1 (by rfl) ⟨1807145, by rfl⟩ : syracuseStep 2409527 = 3614291) B3614291
theorem B1427051 : Blo 842353 1427051 := bstep (se 1 (by rfl) ⟨1070288, by rfl⟩ : syracuseStep 1427051 = 2140577) B2140577
theorem B7227215 : Blo 842353 7227215 := bstep (se 1 (by rfl) ⟨5420411, by rfl⟩ : syracuseStep 7227215 = 10840823) B10840823
theorem B1427321 : Blo 842353 1427321 := bstep (se 2 (by rfl) ⟨535245, by rfl⟩ : syracuseStep 1427321 = 1070491) B1070491
theorem B4802561 : Blo 842353 4802561 := bstep (se 2 (by rfl) ⟨1800960, by rfl⟩ : syracuseStep 4802561 = 3601921) B3601921
theorem B1263647 : Blo 842353 1263647 := bstep (se 1 (by rfl) ⟨947735, by rfl⟩ : syracuseStep 1263647 = 1895471) B1895471
theorem B1263839 : Blo 842353 1263839 := bstep (se 1 (by rfl) ⟨947879, by rfl⟩ : syracuseStep 1263839 = 1895759) B1895759
theorem B1263899 : Blo 842353 1263899 := bstep (se 1 (by rfl) ⟨947924, by rfl⟩ : syracuseStep 1263899 = 1895849) B1895849
theorem B1427881 : Blo 842353 1427881 := bstep (se 2 (by rfl) ⟨535455, by rfl⟩ : syracuseStep 1427881 = 1070911) B1070911
theorem B903727 : Blo 842353 903727 := bstep (se 1 (by rfl) ⟨677795, by rfl⟩ : syracuseStep 903727 = 1355591) B1355591
theorem B1264223 : Blo 842353 1264223 := bstep (se 1 (by rfl) ⟨948167, by rfl⟩ : syracuseStep 1264223 = 1896335) B1896335
theorem B4278905 : Blo 842353 4278905 := bstep (se 2 (by rfl) ⟨1604589, by rfl⟩ : syracuseStep 4278905 = 3209179) B3209179
theorem B61524683 : Blo 842353 61524683 := bstep (se 1 (by rfl) ⟨46143512, by rfl⟩ : syracuseStep 61524683 = 92287025) B92287025
theorem B1264505 : Blo 842353 1264505 := bstep (se 2 (by rfl) ⟨474189, by rfl⟩ : syracuseStep 1264505 = 948379) B948379
theorem B1952671 : Blo 842353 1952671 := bstep (se 1 (by rfl) ⟨1464503, by rfl⟩ : syracuseStep 1952671 = 2929007) B2929007
theorem B1264553 : Blo 842353 1264553 := bstep (se 2 (by rfl) ⟨474207, by rfl⟩ : syracuseStep 1264553 = 948415) B948415
theorem B4803563 : Blo 842353 4803563 := bstep (se 1 (by rfl) ⟨3602672, by rfl⟩ : syracuseStep 4803563 = 7205345) B7205345
theorem B1264703 : Blo 842353 1264703 := bstep (se 1 (by rfl) ⟨948527, by rfl⟩ : syracuseStep 1264703 = 1897055) B1897055
theorem B3656801 : Blo 842353 3656801 := bstep (se 2 (by rfl) ⟨1371300, by rfl⟩ : syracuseStep 3656801 = 2742601) B2742601
theorem B1265255 : Blo 842353 1265255 := bstep (se 1 (by rfl) ⟨948941, by rfl⟩ : syracuseStep 1265255 = 1897883) B1897883
theorem B3198791 : Blo 842353 3198791 := bstep (se 1 (by rfl) ⟨2399093, by rfl⟩ : syracuseStep 3198791 = 4798187) B4798187
theorem B1265639 : Blo 842353 1265639 := bstep (se 1 (by rfl) ⟨949229, by rfl⟩ : syracuseStep 1265639 = 1898459) B1898459
theorem B4804703 : Blo 842353 4804703 := bstep (se 1 (by rfl) ⟨3603527, by rfl⟩ : syracuseStep 4804703 = 7207055) B7207055
theorem B1265759 : Blo 842353 1265759 := bstep (se 1 (by rfl) ⟨949319, by rfl⟩ : syracuseStep 1265759 = 1898639) B1898639
theorem B1265771 : Blo 842353 1265771 := bstep (se 1 (by rfl) ⟨949328, by rfl⟩ : syracuseStep 1265771 = 1898657) B1898657
theorem B5132411 : Blo 842353 5132411 := bstep (se 1 (by rfl) ⟨3849308, by rfl⟩ : syracuseStep 5132411 = 7698617) B7698617
theorem B1265819 : Blo 842353 1265819 := bstep (se 1 (by rfl) ⟨949364, by rfl⟩ : syracuseStep 1265819 = 1898729) B1898729
theorem B3199763 : Blo 842353 3199763 := bstep (se 1 (by rfl) ⟨2399822, by rfl⟩ : syracuseStep 3199763 = 4799645) B4799645
theorem B1266671 : Blo 842353 1266671 := bstep (se 1 (by rfl) ⟨950003, by rfl⟩ : syracuseStep 1266671 = 1900007) B1900007
theorem B1267055 : Blo 842353 1267055 := bstep (se 1 (by rfl) ⟨950291, by rfl⟩ : syracuseStep 1267055 = 1900583) B1900583
theorem B1267175 : Blo 842353 1267175 := bstep (se 1 (by rfl) ⟨950381, by rfl⟩ : syracuseStep 1267175 = 1900763) B1900763
theorem B27350531 : Blo 842353 27350531 := bstep (se 1 (by rfl) ⟨20512898, by rfl⟩ : syracuseStep 27350531 = 41025797) B41025797
theorem B1267337 : Blo 842353 1267337 := bstep (se 2 (by rfl) ⟨475251, by rfl⟩ : syracuseStep 1267337 = 950503) B950503
theorem B1267355 : Blo 842353 1267355 := bstep (se 1 (by rfl) ⟨950516, by rfl⟩ : syracuseStep 1267355 = 1901033) B1901033
theorem B1267547 : Blo 842353 1267547 := bstep (se 1 (by rfl) ⟨950660, by rfl⟩ : syracuseStep 1267547 = 1901321) B1901321
theorem B6838415 : Blo 842353 6838415 := bstep (se 1 (by rfl) ⟨5128811, by rfl⟩ : syracuseStep 6838415 = 10257623) B10257623
theorem B1267931 : Blo 842353 1267931 := bstep (se 1 (by rfl) ⟨950948, by rfl⟩ : syracuseStep 1267931 = 1901897) B1901897
theorem B4282631 : Blo 842353 4282631 := bstep (se 1 (by rfl) ⟨3211973, by rfl⟩ : syracuseStep 4282631 = 6423947) B6423947
theorem B7199057 : Blo 842353 7199057 := bstep (se 2 (by rfl) ⟨2699646, by rfl⟩ : syracuseStep 7199057 = 5399293) B5399293
theorem B3201389 : Blo 842353 3201389 := bstep (se 3 (by rfl) ⟨600260, by rfl⟩ : syracuseStep 3201389 = 1200521) B1200521
theorem B46815671 : Blo 842353 46815671 := bstep (se 1 (by rfl) ⟨35111753, by rfl⟩ : syracuseStep 46815671 = 70223507) B70223507
theorem B1268201 : Blo 842353 1268201 := bstep (se 2 (by rfl) ⟨475575, by rfl⟩ : syracuseStep 1268201 = 951151) B951151
theorem B4807187 : Blo 842353 4807187 := bstep (se 1 (by rfl) ⟨3605390, by rfl⟩ : syracuseStep 4807187 = 7210781) B7210781
theorem B842399 : Blo 842353 842399 := bstep (se 1 (by rfl) ⟨631799, by rfl⟩ : syracuseStep 842399 = 1263599) B1263599
theorem B842567 : Blo 842353 842567 := bstep (se 1 (by rfl) ⟨631925, by rfl⟩ : syracuseStep 842567 = 1263851) B1263851
theorem B842607 : Blo 842353 842607 := bstep (se 1 (by rfl) ⟨631955, by rfl⟩ : syracuseStep 842607 = 1263911) B1263911
theorem B1268591 : Blo 842353 1268591 := bstep (se 1 (by rfl) ⟨951443, by rfl⟩ : syracuseStep 1268591 = 1902887) B1902887
theorem B1268603 : Blo 842353 1268603 := bstep (se 1 (by rfl) ⟨951452, by rfl⟩ : syracuseStep 1268603 = 1902905) B1902905
theorem B842663 : Blo 842353 842663 := bstep (se 1 (by rfl) ⟨631997, by rfl⟩ : syracuseStep 842663 = 1263995) B1263995
theorem B299850821 : Blo 842353 299850821 := bstep (se 4 (by rfl) ⟨28111014, by rfl⟩ : syracuseStep 299850821 = 56222029) B56222029
theorem B842843 : Blo 842353 842843 := bstep (se 1 (by rfl) ⟨632132, by rfl⟩ : syracuseStep 842843 = 1264265) B1264265
theorem B8019121 : Blo 842353 8019121 := bstep (se 2 (by rfl) ⟨3007170, by rfl⟩ : syracuseStep 8019121 = 6014341) B6014341
theorem B842959 : Blo 842353 842959 := bstep (se 1 (by rfl) ⟨632219, by rfl⟩ : syracuseStep 842959 = 1264439) B1264439
theorem B842983 : Blo 842353 842983 := bstep (se 1 (by rfl) ⟨632237, by rfl⟩ : syracuseStep 842983 = 1264475) B1264475
theorem B843079 : Blo 842353 843079 := bstep (se 1 (by rfl) ⟨632309, by rfl⟩ : syracuseStep 843079 = 1264619) B1264619
theorem B843215 : Blo 842353 843215 := bstep (se 1 (by rfl) ⟨632411, by rfl⟩ : syracuseStep 843215 = 1264823) B1264823
theorem B16211411 : Blo 842353 16211411 := bstep (se 1 (by rfl) ⟨12158558, by rfl⟩ : syracuseStep 16211411 = 24317117) B24317117
theorem B843375 : Blo 842353 843375 := bstep (se 1 (by rfl) ⟨632531, by rfl⟩ : syracuseStep 843375 = 1265063) B1265063
theorem B3661433 : Blo 842353 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B843431 : Blo 842353 843431 := bstep (se 1 (by rfl) ⟨632573, by rfl⟩ : syracuseStep 843431 = 1265147) B1265147
theorem B1269467 : Blo 842353 1269467 := bstep (se 1 (by rfl) ⟨952100, by rfl⟩ : syracuseStep 1269467 = 1904201) B1904201
theorem B843495 : Blo 842353 843495 := bstep (se 1 (by rfl) ⟨632621, by rfl⟩ : syracuseStep 843495 = 1265243) B1265243
theorem B3202847 : Blo 842353 3202847 := bstep (se 1 (by rfl) ⟨2402135, by rfl⟩ : syracuseStep 3202847 = 4804271) B4804271
theorem B843551 : Blo 842353 843551 := bstep (se 1 (by rfl) ⟨632663, by rfl⟩ : syracuseStep 843551 = 1265327) B1265327
theorem B843631 : Blo 842353 843631 := bstep (se 1 (by rfl) ⟨632723, by rfl⟩ : syracuseStep 843631 = 1265447) B1265447
theorem B1924975 : Blo 842353 1924975 := bstep (se 1 (by rfl) ⟨1443731, by rfl⟩ : syracuseStep 1924975 = 2887463) B2887463
theorem B843687 : Blo 842353 843687 := bstep (se 1 (by rfl) ⟨632765, by rfl⟩ : syracuseStep 843687 = 1265531) B1265531
theorem B843967 : Blo 842353 843967 := bstep (se 1 (by rfl) ⟨632975, by rfl⟩ : syracuseStep 843967 = 1265951) B1265951
theorem B7200971 : Blo 842353 7200971 := bstep (se 1 (by rfl) ⟨5400728, by rfl⟩ : syracuseStep 7200971 = 10801457) B10801457
theorem B843983 : Blo 842353 843983 := bstep (se 1 (by rfl) ⟨632987, by rfl⟩ : syracuseStep 843983 = 1265975) B1265975
theorem B844031 : Blo 842353 844031 := bstep (se 1 (by rfl) ⟨633023, by rfl⟩ : syracuseStep 844031 = 1266047) B1266047
theorem B844079 : Blo 842353 844079 := bstep (se 1 (by rfl) ⟨633059, by rfl⟩ : syracuseStep 844079 = 1266119) B1266119
theorem B46129495 : Blo 842353 46129495 := bstep (se 1 (by rfl) ⟨34597121, by rfl⟩ : syracuseStep 46129495 = 69194243) B69194243
theorem B844315 : Blo 842353 844315 := bstep (se 1 (by rfl) ⟨633236, by rfl⟩ : syracuseStep 844315 = 1266473) B1266473
theorem B844319 : Blo 842353 844319 := bstep (se 1 (by rfl) ⟨633239, by rfl⟩ : syracuseStep 844319 = 1266479) B1266479
theorem B844399 : Blo 842353 844399 := bstep (se 1 (by rfl) ⟨633299, by rfl⟩ : syracuseStep 844399 = 1266599) B1266599
theorem B844455 : Blo 842353 844455 := bstep (se 1 (by rfl) ⟨633341, by rfl⟩ : syracuseStep 844455 = 1266683) B1266683
theorem B844495 : Blo 842353 844495 := bstep (se 1 (by rfl) ⟨633371, by rfl⟩ : syracuseStep 844495 = 1266743) B1266743
theorem B3203819 : Blo 842353 3203819 := bstep (se 1 (by rfl) ⟨2402864, by rfl⟩ : syracuseStep 3203819 = 4805729) B4805729
theorem B2843423 : Blo 842353 2843423 := bstep (se 1 (by rfl) ⟨2132567, by rfl⟩ : syracuseStep 2843423 = 4265135) B4265135
theorem B844575 : Blo 842353 844575 := bstep (se 1 (by rfl) ⟨633431, by rfl⟩ : syracuseStep 844575 = 1266863) B1266863
theorem B844847 : Blo 842353 844847 := bstep (se 1 (by rfl) ⟨633635, by rfl⟩ : syracuseStep 844847 = 1267271) B1267271
theorem B844911 : Blo 842353 844911 := bstep (se 1 (by rfl) ⟨633683, by rfl⟩ : syracuseStep 844911 = 1267367) B1267367
theorem B844967 : Blo 842353 844967 := bstep (se 1 (by rfl) ⟨633725, by rfl⟩ : syracuseStep 844967 = 1267451) B1267451
theorem B844991 : Blo 842353 844991 := bstep (se 1 (by rfl) ⟨633743, by rfl⟩ : syracuseStep 844991 = 1267487) B1267487
theorem B845023 : Blo 842353 845023 := bstep (se 1 (by rfl) ⟨633767, by rfl⟩ : syracuseStep 845023 = 1267535) B1267535
theorem B845103 : Blo 842353 845103 := bstep (se 1 (by rfl) ⟨633827, by rfl⟩ : syracuseStep 845103 = 1267655) B1267655
theorem B845339 : Blo 842353 845339 := bstep (se 1 (by rfl) ⟨634004, by rfl⟩ : syracuseStep 845339 = 1268009) B1268009
theorem B845343 : Blo 842353 845343 := bstep (se 1 (by rfl) ⟨634007, by rfl⟩ : syracuseStep 845343 = 1268015) B1268015
theorem B845503 : Blo 842353 845503 := bstep (se 1 (by rfl) ⟨634127, by rfl⟩ : syracuseStep 845503 = 1268255) B1268255
theorem B2844395 : Blo 842353 2844395 := bstep (se 1 (by rfl) ⟨2133296, by rfl⟩ : syracuseStep 2844395 = 4266593) B4266593
theorem B4056851 : Blo 842353 4056851 := bstep (se 1 (by rfl) ⟨3042638, by rfl⟩ : syracuseStep 4056851 = 6085277) B6085277
theorem B845759 : Blo 842353 845759 := bstep (se 1 (by rfl) ⟨634319, by rfl⟩ : syracuseStep 845759 = 1268639) B1268639
theorem B845791 : Blo 842353 845791 := bstep (se 1 (by rfl) ⟨634343, by rfl⟩ : syracuseStep 845791 = 1268687) B1268687
theorem B2844665 : Blo 842353 2844665 := bstep (se 2 (by rfl) ⟨1066749, by rfl⟩ : syracuseStep 2844665 = 2133499) B2133499
theorem B845851 : Blo 842353 845851 := bstep (se 1 (by rfl) ⟨634388, by rfl⟩ : syracuseStep 845851 = 1268777) B1268777
theorem B845855 : Blo 842353 845855 := bstep (se 1 (by rfl) ⟨634391, by rfl⟩ : syracuseStep 845855 = 1268783) B1268783
theorem B845871 : Blo 842353 845871 := bstep (se 1 (by rfl) ⟨634403, by rfl⟩ : syracuseStep 845871 = 1268807) B1268807
theorem B2058383 : Blo 842353 2058383 := bstep (se 1 (by rfl) ⟨1543787, by rfl⟩ : syracuseStep 2058383 = 3087575) B3087575
theorem B846047 : Blo 842353 846047 := bstep (se 1 (by rfl) ⟨634535, by rfl⟩ : syracuseStep 846047 = 1269071) B1269071
theorem B2844935 : Blo 842353 2844935 := bstep (se 1 (by rfl) ⟨2133701, by rfl⟩ : syracuseStep 2844935 = 4267403) B4267403
theorem B846107 : Blo 842353 846107 := bstep (se 1 (by rfl) ⟨634580, by rfl⟩ : syracuseStep 846107 = 1269161) B1269161
theorem B4057391 : Blo 842353 4057391 := bstep (se 1 (by rfl) ⟨3043043, by rfl⟩ : syracuseStep 4057391 = 6086087) B6086087
theorem B846207 : Blo 842353 846207 := bstep (se 1 (by rfl) ⟨634655, by rfl⟩ : syracuseStep 846207 = 1269311) B1269311
theorem B11725897 : Blo 842353 11725897 := bstep (se 2 (by rfl) ⟨4397211, by rfl⟩ : syracuseStep 11725897 = 8794423) B8794423
theorem B1600823 : Blo 842353 1600823 := bstep (se 1 (by rfl) ⟨1200617, by rfl⟩ : syracuseStep 1600823 = 2401235) B2401235
theorem B3206567 : Blo 842353 3206567 := bstep (se 1 (by rfl) ⟨2404925, by rfl⟩ : syracuseStep 3206567 = 4809851) B4809851
theorem B3042755 : Blo 842353 3042755 := bstep (se 1 (by rfl) ⟨2282066, by rfl⟩ : syracuseStep 3042755 = 4564133) B4564133
theorem B1895903 : Blo 842353 1895903 := bstep (se 1 (by rfl) ⟨1421927, by rfl⟩ : syracuseStep 1895903 = 2843855) B2843855
theorem B8121971 : Blo 842353 8121971 := bstep (se 1 (by rfl) ⟨6091478, by rfl⟩ : syracuseStep 8121971 = 12182957) B12182957
theorem B1896119 : Blo 842353 1896119 := bstep (se 1 (by rfl) ⟨1422089, by rfl⟩ : syracuseStep 1896119 = 2844179) B2844179
theorem B10841849 : Blo 842353 10841849 := bstep (se 2 (by rfl) ⟨4065693, by rfl⟩ : syracuseStep 10841849 = 8131387) B8131387
theorem B1601947 : Blo 842353 1601947 := bstep (se 1 (by rfl) ⟨1201460, by rfl⟩ : syracuseStep 1601947 = 2402921) B2402921
theorem B1896911 : Blo 842353 1896911 := bstep (se 1 (by rfl) ⟨1422683, by rfl⟩ : syracuseStep 1896911 = 2845367) B2845367
theorem B914527 : Blo 842353 914527 := bstep (se 1 (by rfl) ⟨685895, by rfl⟩ : syracuseStep 914527 = 1371791) B1371791
theorem B1897577 : Blo 842353 1897577 := bstep (se 2 (by rfl) ⟨711591, by rfl⟩ : syracuseStep 1897577 = 1423183) B1423183
theorem B3208511 : Blo 842353 3208511 := bstep (se 1 (by rfl) ⟨2406383, by rfl⟩ : syracuseStep 3208511 = 4812767) B4812767
theorem B947695 : Blo 842353 947695 := bstep (se 1 (by rfl) ⟨710771, by rfl⟩ : syracuseStep 947695 = 1421543) B1421543
theorem B947803 : Blo 842353 947803 := bstep (se 1 (by rfl) ⟨710852, by rfl⟩ : syracuseStep 947803 = 1421705) B1421705
theorem B6420059 : Blo 842353 6420059 := bstep (se 1 (by rfl) ⟨4815044, by rfl⟩ : syracuseStep 6420059 = 9630089) B9630089
theorem B30865097 : Blo 842353 30865097 := bstep (se 2 (by rfl) ⟨11574411, by rfl⟩ : syracuseStep 30865097 = 23148823) B23148823
theorem B1898207 : Blo 842353 1898207 := bstep (se 1 (by rfl) ⟨1423655, by rfl⟩ : syracuseStep 1898207 = 2847311) B2847311
theorem B948091 : Blo 842353 948091 := bstep (se 1 (by rfl) ⟨711068, by rfl⟩ : syracuseStep 948091 = 1422137) B1422137
theorem B948127 : Blo 842353 948127 := bstep (se 1 (by rfl) ⟨711095, by rfl⟩ : syracuseStep 948127 = 1422191) B1422191
theorem B1898567 : Blo 842353 1898567 := bstep (se 1 (by rfl) ⟨1423925, by rfl⟩ : syracuseStep 1898567 = 2847851) B2847851
theorem B21690665 : Blo 842353 21690665 := bstep (se 2 (by rfl) ⟨8133999, by rfl⟩ : syracuseStep 21690665 = 16267999) B16267999
theorem B7305875 : Blo 842353 7305875 := bstep (se 1 (by rfl) ⟨5479406, by rfl⟩ : syracuseStep 7305875 = 10958813) B10958813
theorem B1899233 : Blo 842353 1899233 := bstep (se 2 (by rfl) ⟨712212, by rfl⟩ : syracuseStep 1899233 = 1424425) B1424425
theorem B949063 : Blo 842353 949063 := bstep (se 1 (by rfl) ⟨711797, by rfl⟩ : syracuseStep 949063 = 1423595) B1423595
theorem B7207805 : Blo 842353 7207805 := bstep (se 3 (by rfl) ⟨1351463, by rfl⟩ : syracuseStep 7207805 = 2702927) B2702927
theorem B1899431 : Blo 842353 1899431 := bstep (se 1 (by rfl) ⟨1424573, by rfl⟩ : syracuseStep 1899431 = 2849147) B2849147
theorem B12352501 : Blo 842353 12352501 := bstep (se 5 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 12352501 = 1158047) B1158047
theorem B1899611 : Blo 842353 1899611 := bstep (se 1 (by rfl) ⟨1424708, by rfl⟩ : syracuseStep 1899611 = 2849417) B2849417
theorem B3210425 : Blo 842353 3210425 := bstep (se 2 (by rfl) ⟨1203909, by rfl⟩ : syracuseStep 3210425 = 2407819) B2407819
theorem B3210455 : Blo 842353 3210455 := bstep (se 1 (by rfl) ⟨2407841, by rfl⟩ : syracuseStep 3210455 = 4815683) B4815683
theorem B8125697 : Blo 842353 8125697 := bstep (se 2 (by rfl) ⟨3047136, by rfl⟩ : syracuseStep 8125697 = 6094273) B6094273
theorem B7306685 : Blo 842353 7306685 := bstep (se 3 (by rfl) ⟨1370003, by rfl⟩ : syracuseStep 7306685 = 2740007) B2740007
theorem B949711 : Blo 842353 949711 := bstep (se 1 (by rfl) ⟨712283, by rfl⟩ : syracuseStep 949711 = 1424567) B1424567
theorem B1539695 : Blo 842353 1539695 := bstep (se 1 (by rfl) ⟨1154771, by rfl⟩ : syracuseStep 1539695 = 2309543) B2309543
theorem B949927 : Blo 842353 949927 := bstep (se 1 (by rfl) ⟨712445, by rfl⟩ : syracuseStep 949927 = 1424891) B1424891
theorem B1015463 : Blo 842353 1015463 := bstep (se 1 (by rfl) ⟨761597, by rfl⟩ : syracuseStep 1015463 = 1523195) B1523195
theorem B1900367 : Blo 842353 1900367 := bstep (se 1 (by rfl) ⟨1425275, by rfl⟩ : syracuseStep 1900367 = 2850551) B2850551
theorem B3047311 : Blo 842353 3047311 := bstep (se 1 (by rfl) ⟨2285483, by rfl⟩ : syracuseStep 3047311 = 4570967) B4570967
theorem B950215 : Blo 842353 950215 := bstep (se 1 (by rfl) ⟨712661, by rfl⟩ : syracuseStep 950215 = 1425323) B1425323
theorem B13697063 : Blo 842353 13697063 := bstep (se 1 (by rfl) ⟨10272797, by rfl⟩ : syracuseStep 13697063 = 20545595) B20545595
theorem B1900799 : Blo 842353 1900799 := bstep (se 1 (by rfl) ⟨1425599, by rfl⟩ : syracuseStep 1900799 = 2851199) B2851199
theorem B2851091 : Blo 842353 2851091 := bstep (se 1 (by rfl) ⟨2138318, by rfl⟩ : syracuseStep 2851091 = 4276637) B4276637
theorem B950683 : Blo 842353 950683 := bstep (se 1 (by rfl) ⟨713012, by rfl⟩ : syracuseStep 950683 = 1426025) B1426025
theorem B3604895 : Blo 842353 3604895 := bstep (se 1 (by rfl) ⟨2703671, by rfl⟩ : syracuseStep 3604895 = 5407343) B5407343
theorem B61505993 : Blo 842353 61505993 := bstep (se 2 (by rfl) ⟨23064747, by rfl⟩ : syracuseStep 61505993 = 46129495) B46129495
theorem B6685181 : Blo 842353 6685181 := bstep (se 3 (by rfl) ⟨1253471, by rfl⟩ : syracuseStep 6685181 = 2506943) B2506943
theorem B7308089 : Blo 842353 7308089 := bstep (se 2 (by rfl) ⟨2740533, by rfl⟩ : syracuseStep 7308089 = 5481067) B5481067
theorem B1901375 : Blo 842353 1901375 := bstep (se 1 (by rfl) ⟨1426031, by rfl⟩ : syracuseStep 1901375 = 2852063) B2852063
theorem B951367 : Blo 842353 951367 := bstep (se 1 (by rfl) ⟨713525, by rfl⟩ : syracuseStep 951367 = 1427051) B1427051
theorem B4818143 : Blo 842353 4818143 := bstep (se 1 (by rfl) ⟨3613607, by rfl⟩ : syracuseStep 4818143 = 7227215) B7227215
theorem B951547 : Blo 842353 951547 := bstep (se 1 (by rfl) ⟨713660, by rfl⟩ : syracuseStep 951547 = 1427321) B1427321
theorem B41125441 : Blo 842353 41125441 := bstep (se 2 (by rfl) ⟨15422040, by rfl⟩ : syracuseStep 41125441 = 30844081) B30844081
theorem B2852603 : Blo 842353 2852603 := bstep (se 1 (by rfl) ⟨2139452, by rfl⟩ : syracuseStep 2852603 = 4278905) B4278905
theorem B1902527 : Blo 842353 1902527 := bstep (se 1 (by rfl) ⟨1426895, by rfl⟩ : syracuseStep 1902527 = 2853791) B2853791
theorem B3607031 : Blo 842353 3607031 := bstep (se 1 (by rfl) ⟨2705273, by rfl⟩ : syracuseStep 3607031 = 5410547) B5410547
theorem B2132527 : Blo 842353 2132527 := bstep (se 1 (by rfl) ⟨1599395, by rfl⟩ : syracuseStep 2132527 = 3198791) B3198791
theorem B6425405 : Blo 842353 6425405 := bstep (se 3 (by rfl) ⟨1204763, by rfl⟩ : syracuseStep 6425405 = 2409527) B2409527
theorem B1903571 : Blo 842353 1903571 := bstep (se 1 (by rfl) ⟨1427678, by rfl⟩ : syracuseStep 1903571 = 2855357) B2855357
theorem B4820057 : Blo 842353 4820057 := bstep (se 2 (by rfl) ⟨1807521, by rfl⟩ : syracuseStep 4820057 = 3615043) B3615043
theorem B6491279 : Blo 842353 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B2133175 : Blo 842353 2133175 := bstep (se 1 (by rfl) ⟨1599881, by rfl⟩ : syracuseStep 2133175 = 3199763) B3199763
theorem B1903841 : Blo 842353 1903841 := bstep (se 2 (by rfl) ⟨713940, by rfl⟩ : syracuseStep 1903841 = 1427881) B1427881
theorem B4558943 : Blo 842353 4558943 := bstep (se 1 (by rfl) ⟨3419207, by rfl⟩ : syracuseStep 4558943 = 6838415) B6838415
theorem B15634529 : Blo 842353 15634529 := bstep (se 2 (by rfl) ⟨5862948, by rfl⟩ : syracuseStep 15634529 = 11725897) B11725897
theorem B5771425 : Blo 842353 5771425 := bstep (se 2 (by rfl) ⟨2164284, by rfl⟩ : syracuseStep 5771425 = 4328569) B4328569
theorem B2855087 : Blo 842353 2855087 := bstep (se 1 (by rfl) ⟨2141315, by rfl⟩ : syracuseStep 2855087 = 4282631) B4282631
theorem B2134259 : Blo 842353 2134259 := bstep (se 1 (by rfl) ⟨1600694, by rfl⟩ : syracuseStep 2134259 = 3201389) B3201389
theorem B4264487 : Blo 842353 4264487 := bstep (se 1 (by rfl) ⟨3198365, by rfl⟩ : syracuseStep 4264487 = 6396731) B6396731
theorem B10818269 : Blo 842353 10818269 := bstep (se 3 (by rfl) ⟨2028425, by rfl⟩ : syracuseStep 10818269 = 4056851) B4056851
theorem B2135231 : Blo 842353 2135231 := bstep (se 1 (by rfl) ⟨1601423, by rfl⟩ : syracuseStep 2135231 = 3202847) B3202847
theorem B2135879 : Blo 842353 2135879 := bstep (se 1 (by rfl) ⟨1601909, by rfl⟩ : syracuseStep 2135879 = 3203819) B3203819
theorem B2135929 : Blo 842353 2135929 := bstep (se 2 (by rfl) ⟨800973, by rfl⟩ : syracuseStep 2135929 = 1601947) B1601947
theorem B1219369 : Blo 842353 1219369 := bstep (se 2 (by rfl) ⟨457263, by rfl⟩ : syracuseStep 1219369 = 914527) B914527
theorem B6495835 : Blo 842353 6495835 := bstep (se 1 (by rfl) ⟨4871876, by rfl⟩ : syracuseStep 6495835 = 9743753) B9743753
theorem B2137711 : Blo 842353 2137711 := bstep (se 1 (by rfl) ⟨1603283, by rfl⟩ : syracuseStep 2137711 = 3206567) B3206567
theorem B5414647 : Blo 842353 5414647 := bstep (se 1 (by rfl) ⟨4060985, by rfl⟩ : syracuseStep 5414647 = 8121971) B8121971
theorem B21635171 : Blo 842353 21635171 := bstep (se 1 (by rfl) ⟨16226378, by rfl⟩ : syracuseStep 21635171 = 32452757) B32452757
theorem B2433491 : Blo 842353 2433491 := bstep (se 1 (by rfl) ⟨1825118, by rfl⟩ : syracuseStep 2433491 = 3650237) B3650237
theorem B4268861 : Blo 842353 4268861 := bstep (se 3 (by rfl) ⟨800411, by rfl⟩ : syracuseStep 4268861 = 1600823) B1600823
theorem B2139007 : Blo 842353 2139007 := bstep (se 1 (by rfl) ⟨1604255, by rfl⟩ : syracuseStep 2139007 = 3208511) B3208511
theorem B14460443 : Blo 842353 14460443 := bstep (se 1 (by rfl) ⟨10845332, by rfl⟩ : syracuseStep 14460443 = 21690665) B21690665
theorem B10692161 : Blo 842353 10692161 := bstep (se 2 (by rfl) ⟨4009560, by rfl⟩ : syracuseStep 10692161 = 8019121) B8019121
theorem B2402237 : Blo 842353 2402237 := bstep (se 3 (by rfl) ⟨450419, by rfl⟩ : syracuseStep 2402237 = 900839) B900839
theorem B2140283 : Blo 842353 2140283 := bstep (se 1 (by rfl) ⟨1605212, by rfl⟩ : syracuseStep 2140283 = 3210425) B3210425
theorem B2140303 : Blo 842353 2140303 := bstep (se 1 (by rfl) ⟨1605227, by rfl⟩ : syracuseStep 2140303 = 3210455) B3210455
theorem B5417131 : Blo 842353 5417131 := bstep (se 1 (by rfl) ⟨4062848, by rfl⟩ : syracuseStep 5417131 = 8125697) B8125697
theorem B1026463 : Blo 842353 1026463 := bstep (se 1 (by rfl) ⟨769847, by rfl⟩ : syracuseStep 1026463 = 1539695) B1539695
theorem B2566633 : Blo 842353 2566633 := bstep (se 2 (by rfl) ⟨962487, by rfl⟩ : syracuseStep 2566633 = 1924975) B1924975
theorem B2567351 : Blo 842353 2567351 := bstep (se 1 (by rfl) ⟨1925513, by rfl⟩ : syracuseStep 2567351 = 3851027) B3851027
theorem B36974593 : Blo 842353 36974593 := bstep (se 2 (by rfl) ⟨13865472, by rfl⟩ : syracuseStep 36974593 = 27730945) B27730945
theorem B2437867 : Blo 842353 2437867 := bstep (se 1 (by rfl) ⟨1828400, by rfl⟩ : syracuseStep 2437867 = 3656801) B3656801
theorem B2405177 : Blo 842353 2405177 := bstep (se 2 (by rfl) ⟨901941, by rfl⟩ : syracuseStep 2405177 = 1803883) B1803883
theorem B1422319 : Blo 842353 1422319 := bstep (se 1 (by rfl) ⟨1066739, by rfl⟩ : syracuseStep 1422319 = 2133479) B2133479
theorem B11580545 : Blo 842353 11580545 := bstep (se 2 (by rfl) ⟨4342704, by rfl⟩ : syracuseStep 11580545 = 8685409) B8685409
theorem B3421607 : Blo 842353 3421607 := bstep (se 1 (by rfl) ⟨2566205, by rfl⟩ : syracuseStep 3421607 = 5132411) B5132411
theorem B2602451 : Blo 842353 2602451 := bstep (se 1 (by rfl) ⟨1951838, by rfl⟩ : syracuseStep 2602451 = 3903677) B3903677
theorem B1423055 : Blo 842353 1423055 := bstep (se 1 (by rfl) ⟨1067291, by rfl⟩ : syracuseStep 1423055 = 2134583) B2134583
theorem B2406611 : Blo 842353 2406611 := bstep (se 1 (by rfl) ⟨1804958, by rfl⟩ : syracuseStep 2406611 = 3609917) B3609917
theorem B18233687 : Blo 842353 18233687 := bstep (se 1 (by rfl) ⟨13675265, by rfl⟩ : syracuseStep 18233687 = 27350531) B27350531
theorem B2603561 : Blo 842353 2603561 := bstep (se 2 (by rfl) ⟨976335, by rfl⟩ : syracuseStep 2603561 = 1952671) B1952671
theorem B18266903 : Blo 842353 18266903 := bstep (se 1 (by rfl) ⟨13700177, by rfl⟩ : syracuseStep 18266903 = 27400355) B27400355
theorem B4799371 : Blo 842353 4799371 := bstep (se 1 (by rfl) ⟨3599528, by rfl⟩ : syracuseStep 4799371 = 7199057) B7199057
theorem B31210447 : Blo 842353 31210447 := bstep (se 1 (by rfl) ⟨23407835, by rfl⟩ : syracuseStep 31210447 = 46815671) B46815671
theorem B4570343 : Blo 842353 4570343 := bstep (se 1 (by rfl) ⟨3427757, by rfl⟩ : syracuseStep 4570343 = 6855515) B6855515
theorem B3849515 : Blo 842353 3849515 := bstep (se 1 (by rfl) ⟨2887136, by rfl⟩ : syracuseStep 3849515 = 5774273) B5774273
theorem B199900547 : Blo 842353 199900547 := bstep (se 1 (by rfl) ⟨149925410, by rfl⟩ : syracuseStep 199900547 = 299850821) B299850821
theorem B2440955 : Blo 842353 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B4800647 : Blo 842353 4800647 := bstep (se 1 (by rfl) ⟨3600485, by rfl⟩ : syracuseStep 4800647 = 7200971) B7200971
theorem B5489021 : Blo 842353 5489021 := bstep (se 3 (by rfl) ⟨1029191, by rfl⟩ : syracuseStep 5489021 = 2058383) B2058383
theorem B2408935 : Blo 842353 2408935 := bstep (se 1 (by rfl) ⟨1806701, by rfl⟩ : syracuseStep 2408935 = 3613403) B3613403
theorem B9126533 : Blo 842353 9126533 := bstep (se 4 (by rfl) ⟨855612, by rfl⟩ : syracuseStep 9126533 = 1711225) B1711225
theorem B4113139 : Blo 842353 4113139 := bstep (se 1 (by rfl) ⟨3084854, by rfl⟩ : syracuseStep 4113139 = 6169709) B6169709
theorem B21611933 : Blo 842353 21611933 := bstep (se 3 (by rfl) ⟨4052237, by rfl⟩ : syracuseStep 21611933 = 8104475) B8104475
theorem B2704927 : Blo 842353 2704927 := bstep (se 1 (by rfl) ⟨2028695, by rfl⟩ : syracuseStep 2704927 = 4057391) B4057391
theorem B1263593 : Blo 842353 1263593 := bstep (se 2 (by rfl) ⟨473847, by rfl⟩ : syracuseStep 1263593 = 947695) B947695
theorem B1427483 : Blo 842353 1427483 := bstep (se 1 (by rfl) ⟨1070612, by rfl⟩ : syracuseStep 1427483 = 2141225) B2141225
theorem B1427503 : Blo 842353 1427503 := bstep (se 1 (by rfl) ⟨1070627, by rfl⟩ : syracuseStep 1427503 = 2141255) B2141255
theorem B1263737 : Blo 842353 1263737 := bstep (se 2 (by rfl) ⟨473901, by rfl⟩ : syracuseStep 1263737 = 947803) B947803
theorem B1263935 : Blo 842353 1263935 := bstep (se 1 (by rfl) ⟨947951, by rfl⟩ : syracuseStep 1263935 = 1895903) B1895903
theorem B1264079 : Blo 842353 1264079 := bstep (se 1 (by rfl) ⟨948059, by rfl⟩ : syracuseStep 1264079 = 1896119) B1896119
theorem B1264121 : Blo 842353 1264121 := bstep (se 2 (by rfl) ⟨474045, by rfl⟩ : syracuseStep 1264121 = 948091) B948091
theorem B7227899 : Blo 842353 7227899 := bstep (se 1 (by rfl) ⟨5420924, by rfl⟩ : syracuseStep 7227899 = 10841849) B10841849
theorem B1264169 : Blo 842353 1264169 := bstep (se 2 (by rfl) ⟨474063, by rfl⟩ : syracuseStep 1264169 = 948127) B948127
theorem B1264607 : Blo 842353 1264607 := bstep (se 1 (by rfl) ⟨948455, by rfl⟩ : syracuseStep 1264607 = 1896911) B1896911
theorem B1265051 : Blo 842353 1265051 := bstep (se 1 (by rfl) ⟨948788, by rfl⟩ : syracuseStep 1265051 = 1897577) B1897577
theorem B4280039 : Blo 842353 4280039 := bstep (se 1 (by rfl) ⟨3210029, by rfl⟩ : syracuseStep 4280039 = 6420059) B6420059
theorem B1265417 : Blo 842353 1265417 := bstep (se 2 (by rfl) ⟨474531, by rfl⟩ : syracuseStep 1265417 = 949063) B949063
theorem B1265471 : Blo 842353 1265471 := bstep (se 1 (by rfl) ⟨949103, by rfl⟩ : syracuseStep 1265471 = 1898207) B1898207
theorem B3198959 : Blo 842353 3198959 := bstep (se 1 (by rfl) ⟨2399219, by rfl⟩ : syracuseStep 3198959 = 4798439) B4798439
theorem B16470001 : Blo 842353 16470001 := bstep (se 2 (by rfl) ⟨6176250, by rfl⟩ : syracuseStep 16470001 = 12352501) B12352501
theorem B1265711 : Blo 842353 1265711 := bstep (se 1 (by rfl) ⟨949283, by rfl⟩ : syracuseStep 1265711 = 1898567) B1898567
theorem B6082715 : Blo 842353 6082715 := bstep (se 1 (by rfl) ⟨4562036, by rfl⟩ : syracuseStep 6082715 = 9124073) B9124073
theorem B4870583 : Blo 842353 4870583 := bstep (se 1 (by rfl) ⟨3652937, by rfl⟩ : syracuseStep 4870583 = 7305875) B7305875
theorem B2707901 : Blo 842353 2707901 := bstep (se 3 (by rfl) ⟨507731, by rfl⟩ : syracuseStep 2707901 = 1015463) B1015463
theorem B1266155 : Blo 842353 1266155 := bstep (se 1 (by rfl) ⟨949616, by rfl⟩ : syracuseStep 1266155 = 1899233) B1899233
theorem B4805203 : Blo 842353 4805203 := bstep (se 1 (by rfl) ⟨3603902, by rfl⟩ : syracuseStep 4805203 = 7207805) B7207805
theorem B1266281 : Blo 842353 1266281 := bstep (se 2 (by rfl) ⟨474855, by rfl⟩ : syracuseStep 1266281 = 949711) B949711
theorem B1266287 : Blo 842353 1266287 := bstep (se 1 (by rfl) ⟨949715, by rfl⟩ : syracuseStep 1266287 = 1899431) B1899431
theorem B1266407 : Blo 842353 1266407 := bstep (se 1 (by rfl) ⟨949805, by rfl⟩ : syracuseStep 1266407 = 1899611) B1899611
theorem B1266569 : Blo 842353 1266569 := bstep (se 2 (by rfl) ⟨474963, by rfl⟩ : syracuseStep 1266569 = 949927) B949927
theorem B4871123 : Blo 842353 4871123 := bstep (se 1 (by rfl) ⟨3653342, by rfl⟩ : syracuseStep 4871123 = 7306685) B7306685
theorem B1266911 : Blo 842353 1266911 := bstep (se 1 (by rfl) ⟨950183, by rfl⟩ : syracuseStep 1266911 = 1900367) B1900367
theorem B1266953 : Blo 842353 1266953 := bstep (se 2 (by rfl) ⟨475107, by rfl⟩ : syracuseStep 1266953 = 950215) B950215
theorem B10802483 : Blo 842353 10802483 := bstep (se 1 (by rfl) ⟨8101862, by rfl⟩ : syracuseStep 10802483 = 16203725) B16203725
theorem B1267391 : Blo 842353 1267391 := bstep (se 1 (by rfl) ⟨950543, by rfl⟩ : syracuseStep 1267391 = 1901087) B1901087
theorem B1267433 : Blo 842353 1267433 := bstep (se 2 (by rfl) ⟨475287, by rfl⟩ : syracuseStep 1267433 = 950575) B950575
theorem B1267439 : Blo 842353 1267439 := bstep (se 1 (by rfl) ⟨950579, by rfl⟩ : syracuseStep 1267439 = 1901159) B1901159
theorem B10835855 : Blo 842353 10835855 := bstep (se 1 (by rfl) ⟨8126891, by rfl⟩ : syracuseStep 10835855 = 16253783) B16253783
theorem B8116163 : Blo 842353 8116163 := bstep (se 1 (by rfl) ⟨6087122, by rfl⟩ : syracuseStep 8116163 = 12174245) B12174245
theorem B1267943 : Blo 842353 1267943 := bstep (se 1 (by rfl) ⟨950957, by rfl⟩ : syracuseStep 1267943 = 1901915) B1901915
theorem B2709899 : Blo 842353 2709899 := bstep (se 1 (by rfl) ⟨2032424, by rfl⟩ : syracuseStep 2709899 = 4064849) B4064849
theorem B1268123 : Blo 842353 1268123 := bstep (se 1 (by rfl) ⟨951092, by rfl⟩ : syracuseStep 1268123 = 1902185) B1902185
theorem B3201707 : Blo 842353 3201707 := bstep (se 1 (by rfl) ⟨2401280, by rfl⟩ : syracuseStep 3201707 = 4802561) B4802561
theorem B842431 : Blo 842353 842431 := bstep (se 1 (by rfl) ⟨631823, by rfl⟩ : syracuseStep 842431 = 1263647) B1263647
theorem B1268519 : Blo 842353 1268519 := bstep (se 1 (by rfl) ⟨951389, by rfl⟩ : syracuseStep 1268519 = 1902779) B1902779
theorem B842559 : Blo 842353 842559 := bstep (se 1 (by rfl) ⟨631919, by rfl⟩ : syracuseStep 842559 = 1263839) B1263839
theorem B1268543 : Blo 842353 1268543 := bstep (se 1 (by rfl) ⟨951407, by rfl⟩ : syracuseStep 1268543 = 1902815) B1902815
theorem B842599 : Blo 842353 842599 := bstep (se 1 (by rfl) ⟨631949, by rfl⟩ : syracuseStep 842599 = 1263899) B1263899
theorem B4807619 : Blo 842353 4807619 := bstep (se 1 (by rfl) ⟨3605714, by rfl⟩ : syracuseStep 4807619 = 7211429) B7211429
theorem B842815 : Blo 842353 842815 := bstep (se 1 (by rfl) ⟨632111, by rfl⟩ : syracuseStep 842815 = 1264223) B1264223
theorem B1268843 : Blo 842353 1268843 := bstep (se 1 (by rfl) ⟨951632, by rfl⟩ : syracuseStep 1268843 = 1903265) B1903265
theorem B41016455 : Blo 842353 41016455 := bstep (se 1 (by rfl) ⟨30762341, by rfl⟩ : syracuseStep 41016455 = 61524683) B61524683
theorem B61562045 : Blo 842353 61562045 := bstep (se 3 (by rfl) ⟨11542883, by rfl⟩ : syracuseStep 61562045 = 23085767) B23085767
theorem B843003 : Blo 842353 843003 := bstep (se 1 (by rfl) ⟨632252, by rfl⟩ : syracuseStep 843003 = 1264505) B1264505
theorem B1268987 : Blo 842353 1268987 := bstep (se 1 (by rfl) ⟨951740, by rfl⟩ : syracuseStep 1268987 = 1903481) B1903481
theorem B843035 : Blo 842353 843035 := bstep (se 1 (by rfl) ⟨632276, by rfl⟩ : syracuseStep 843035 = 1264553) B1264553
theorem B3202375 : Blo 842353 3202375 := bstep (se 1 (by rfl) ⟨2401781, by rfl⟩ : syracuseStep 3202375 = 4803563) B4803563
theorem B1269083 : Blo 842353 1269083 := bstep (se 1 (by rfl) ⟨951812, by rfl⟩ : syracuseStep 1269083 = 1903625) B1903625
theorem B1269113 : Blo 842353 1269113 := bstep (se 2 (by rfl) ⟨475917, by rfl⟩ : syracuseStep 1269113 = 951835) B951835
theorem B843135 : Blo 842353 843135 := bstep (se 1 (by rfl) ⟨632351, by rfl⟩ : syracuseStep 843135 = 1264703) B1264703
theorem B1269119 : Blo 842353 1269119 := bstep (se 1 (by rfl) ⟨951839, by rfl⟩ : syracuseStep 1269119 = 1903679) B1903679
theorem B4284089 : Blo 842353 4284089 := bstep (se 2 (by rfl) ⟨1606533, by rfl⟩ : syracuseStep 4284089 = 3213067) B3213067
theorem B843503 : Blo 842353 843503 := bstep (se 1 (by rfl) ⟨632627, by rfl⟩ : syracuseStep 843503 = 1265255) B1265255
theorem B843759 : Blo 842353 843759 := bstep (se 1 (by rfl) ⟨632819, by rfl⟩ : syracuseStep 843759 = 1265639) B1265639
theorem B3203135 : Blo 842353 3203135 := bstep (se 1 (by rfl) ⟨2402351, by rfl⟩ : syracuseStep 3203135 = 4804703) B4804703
theorem B843839 : Blo 842353 843839 := bstep (se 1 (by rfl) ⟨632879, by rfl⟩ : syracuseStep 843839 = 1265759) B1265759
theorem B843847 : Blo 842353 843847 := bstep (se 1 (by rfl) ⟨632885, by rfl⟩ : syracuseStep 843847 = 1265771) B1265771
theorem B843879 : Blo 842353 843879 := bstep (se 1 (by rfl) ⟨632909, by rfl⟩ : syracuseStep 843879 = 1265819) B1265819
theorem B9232993 : Blo 842353 9232993 := bstep (se 2 (by rfl) ⟨3462372, by rfl⟩ : syracuseStep 9232993 = 6924745) B6924745
theorem B844447 : Blo 842353 844447 := bstep (se 1 (by rfl) ⟨633335, by rfl⟩ : syracuseStep 844447 = 1266671) B1266671
theorem B1204895 : Blo 842353 1204895 := bstep (se 1 (by rfl) ⟨903671, by rfl⟩ : syracuseStep 1204895 = 1807343) B1807343
theorem B1204969 : Blo 842353 1204969 := bstep (se 2 (by rfl) ⟨451863, by rfl⟩ : syracuseStep 1204969 = 903727) B903727
theorem B844703 : Blo 842353 844703 := bstep (se 1 (by rfl) ⟨633527, by rfl⟩ : syracuseStep 844703 = 1267055) B1267055
theorem B844783 : Blo 842353 844783 := bstep (se 1 (by rfl) ⟨633587, by rfl⟩ : syracuseStep 844783 = 1267175) B1267175
theorem B844891 : Blo 842353 844891 := bstep (se 1 (by rfl) ⟨633668, by rfl⟩ : syracuseStep 844891 = 1267337) B1267337
theorem B844903 : Blo 842353 844903 := bstep (se 1 (by rfl) ⟨633677, by rfl⟩ : syracuseStep 844903 = 1267355) B1267355
theorem B845031 : Blo 842353 845031 := bstep (se 1 (by rfl) ⟨633773, by rfl⟩ : syracuseStep 845031 = 1267547) B1267547
theorem B845287 : Blo 842353 845287 := bstep (se 1 (by rfl) ⟨633965, by rfl⟩ : syracuseStep 845287 = 1267931) B1267931
theorem B9627173 : Blo 842353 9627173 := bstep (se 4 (by rfl) ⟨902547, by rfl⟩ : syracuseStep 9627173 = 1805095) B1805095
theorem B845467 : Blo 842353 845467 := bstep (se 1 (by rfl) ⟨634100, by rfl⟩ : syracuseStep 845467 = 1268201) B1268201
theorem B3204791 : Blo 842353 3204791 := bstep (se 1 (by rfl) ⟨2403593, by rfl⟩ : syracuseStep 3204791 = 4807187) B4807187
theorem B82306925 : Blo 842353 82306925 := bstep (se 3 (by rfl) ⟨15432548, by rfl⟩ : syracuseStep 82306925 = 30865097) B30865097
theorem B845727 : Blo 842353 845727 := bstep (se 1 (by rfl) ⟨634295, by rfl⟩ : syracuseStep 845727 = 1268591) B1268591
theorem B845735 : Blo 842353 845735 := bstep (se 1 (by rfl) ⟨634301, by rfl⟩ : syracuseStep 845735 = 1268603) B1268603
theorem B5859287 : Blo 842353 5859287 := bstep (se 1 (by rfl) ⟨4394465, by rfl⟩ : syracuseStep 5859287 = 8788931) B8788931
theorem B13723667 : Blo 842353 13723667 := bstep (se 1 (by rfl) ⟨10292750, by rfl⟩ : syracuseStep 13723667 = 20585501) B20585501
theorem B2844719 : Blo 842353 2844719 := bstep (se 1 (by rfl) ⟨2133539, by rfl⟩ : syracuseStep 2844719 = 4267079) B4267079
theorem B10807607 : Blo 842353 10807607 := bstep (se 1 (by rfl) ⟨8105705, by rfl⟩ : syracuseStep 10807607 = 16211411) B16211411
theorem B23718221 : Blo 842353 23718221 := bstep (se 3 (by rfl) ⟨4447166, by rfl⟩ : syracuseStep 23718221 = 8894333) B8894333
theorem B846311 : Blo 842353 846311 := bstep (se 1 (by rfl) ⟨634733, by rfl⟩ : syracuseStep 846311 = 1269467) B1269467
theorem B2845691 : Blo 842353 2845691 := bstep (se 1 (by rfl) ⟨2134268, by rfl⟩ : syracuseStep 2845691 = 4268537) B4268537
theorem B1895561 : Blo 842353 1895561 := bstep (se 2 (by rfl) ⟨710835, by rfl⟩ : syracuseStep 1895561 = 1421671) B1421671
theorem B1895615 : Blo 842353 1895615 := bstep (se 1 (by rfl) ⟨1421711, by rfl⟩ : syracuseStep 1895615 = 2843423) B2843423
theorem B5402011 : Blo 842353 5402011 := bstep (se 1 (by rfl) ⟨4051508, by rfl⟩ : syracuseStep 5402011 = 8103017) B8103017
theorem B1896263 : Blo 842353 1896263 := bstep (se 1 (by rfl) ⟨1422197, by rfl⟩ : syracuseStep 1896263 = 2844395) B2844395
theorem B4943759 : Blo 842353 4943759 := bstep (se 1 (by rfl) ⟨3707819, by rfl⟩ : syracuseStep 4943759 = 7415639) B7415639
theorem B1896443 : Blo 842353 1896443 := bstep (se 1 (by rfl) ⟨1422332, by rfl⟩ : syracuseStep 1896443 = 2844665) B2844665
theorem B1896623 : Blo 842353 1896623 := bstep (se 1 (by rfl) ⟨1422467, by rfl⟩ : syracuseStep 1896623 = 2844935) B2844935
theorem B3895543 : Blo 842353 3895543 := bstep (se 1 (by rfl) ⟨2921657, by rfl⟩ : syracuseStep 3895543 = 5843315) B5843315
theorem B2061167 : Blo 842353 2061167 := bstep (se 1 (by rfl) ⟨1545875, by rfl⟩ : syracuseStep 2061167 = 3091751) B3091751
theorem B2028503 : Blo 842353 2028503 := bstep (se 1 (by rfl) ⟨1521377, by rfl⟩ : syracuseStep 2028503 = 3042755) B3042755
theorem B2848553 : Blo 842353 2848553 := bstep (se 2 (by rfl) ⟨1068207, by rfl⟩ : syracuseStep 2848553 = 2136415) B2136415
theorem B948271 : Blo 842353 948271 := bstep (se 1 (by rfl) ⟨711203, by rfl⟩ : syracuseStep 948271 = 1422407) B1422407
theorem B1604423 : Blo 842353 1604423 := bstep (se 1 (by rfl) ⟨1203317, by rfl⟩ : syracuseStep 1604423 = 2406635) B2406635
theorem B1014751 : Blo 842353 1014751 := bstep (se 1 (by rfl) ⟨761063, by rfl⟩ : syracuseStep 1014751 = 1522127) B1522127
theorem B4816367 : Blo 842353 4816367 := bstep (se 1 (by rfl) ⟨3612275, by rfl⟩ : syracuseStep 4816367 = 7224551) B7224551
theorem B1900169 : Blo 842353 1900169 := bstep (se 2 (by rfl) ⟨712563, by rfl⟩ : syracuseStep 1900169 = 1425127) B1425127
theorem B950107 : Blo 842353 950107 := bstep (se 1 (by rfl) ⟨712580, by rfl⟩ : syracuseStep 950107 = 1425161) B1425161
theorem B4063081 : Blo 842353 4063081 := bstep (se 2 (by rfl) ⟨1523655, by rfl⟩ : syracuseStep 4063081 = 3047311) B3047311
theorem B1900727 : Blo 842353 1900727 := bstep (se 1 (by rfl) ⟨1425545, by rfl⟩ : syracuseStep 1900727 = 2851091) B2851091
theorem B4456787 : Blo 842353 4456787 := bstep (se 1 (by rfl) ⟨3342590, by rfl⟩ : syracuseStep 4456787 = 6685181) B6685181
theorem B3211913 : Blo 842353 3211913 := bstep (se 2 (by rfl) ⟨1204467, by rfl⟩ : syracuseStep 3211913 = 2408935) B2408935
theorem B3212095 : Blo 842353 3212095 := bstep (se 1 (by rfl) ⟨2409071, by rfl⟩ : syracuseStep 3212095 = 4818143) B4818143
theorem B1606625 : Blo 842353 1606625 := bstep (se 2 (by rfl) ⟨602484, by rfl⟩ : syracuseStep 1606625 = 1204969) B1204969
theorem B1901735 : Blo 842353 1901735 := bstep (se 1 (by rfl) ⟨1426301, by rfl⟩ : syracuseStep 1901735 = 2852603) B2852603
theorem B2852009 : Blo 842353 2852009 := bstep (se 2 (by rfl) ⟨1069503, by rfl⟩ : syracuseStep 2852009 = 2139007) B2139007
theorem B951655 : Blo 842353 951655 := bstep (se 1 (by rfl) ⟨713741, by rfl⟩ : syracuseStep 951655 = 1427483) B1427483
theorem B4818599 : Blo 842353 4818599 := bstep (se 1 (by rfl) ⟨3613949, by rfl⟩ : syracuseStep 4818599 = 7227899) B7227899
theorem B3213053 : Blo 842353 3213053 := bstep (se 3 (by rfl) ⟨602447, by rfl⟩ : syracuseStep 3213053 = 1204895) B1204895
theorem B3606569 : Blo 842353 3606569 := bstep (se 2 (by rfl) ⟨1352463, by rfl⟩ : syracuseStep 3606569 = 2704927) B2704927
theorem B3213371 : Blo 842353 3213371 := bstep (se 1 (by rfl) ⟨2410028, by rfl⟩ : syracuseStep 3213371 = 4820057) B4820057
theorem B4327519 : Blo 842353 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B2853359 : Blo 842353 2853359 := bstep (se 1 (by rfl) ⟨2140019, by rfl⟩ : syracuseStep 2853359 = 4280039) B4280039
theorem B5409341 : Blo 842353 5409341 := bstep (se 3 (by rfl) ⟨1014251, by rfl⟩ : syracuseStep 5409341 = 2028503) B2028503
theorem B2132639 : Blo 842353 2132639 := bstep (se 1 (by rfl) ⟨1599479, by rfl⟩ : syracuseStep 2132639 = 3198959) B3198959
theorem B1903337 : Blo 842353 1903337 := bstep (se 2 (by rfl) ⟨713751, by rfl⟩ : syracuseStep 1903337 = 1427503) B1427503
theorem B10423019 : Blo 842353 10423019 := bstep (se 1 (by rfl) ⟨7817264, by rfl⟩ : syracuseStep 10423019 = 15634529) B15634529
theorem B1903391 : Blo 842353 1903391 := bstep (se 1 (by rfl) ⟨1427543, by rfl⟩ : syracuseStep 1903391 = 2855087) B2855087
theorem B2853737 : Blo 842353 2853737 := bstep (se 2 (by rfl) ⟨1070151, by rfl⟩ : syracuseStep 2853737 = 2140303) B2140303
theorem B3247055 : Blo 842353 3247055 := bstep (se 1 (by rfl) ⟨2435291, by rfl⟩ : syracuseStep 3247055 = 4870583) B4870583
theorem B1805267 : Blo 842353 1805267 := bstep (se 1 (by rfl) ⟨1353950, by rfl⟩ : syracuseStep 1805267 = 2707901) B2707901
theorem B7212179 : Blo 842353 7212179 := bstep (se 1 (by rfl) ⟨5409134, by rfl⟩ : syracuseStep 7212179 = 10818269) B10818269
theorem B3247415 : Blo 842353 3247415 := bstep (se 1 (by rfl) ⟨2435561, by rfl⟩ : syracuseStep 3247415 = 4871123) B4871123
theorem B5410775 : Blo 842353 5410775 := bstep (se 1 (by rfl) ⟨4058081, by rfl⟩ : syracuseStep 5410775 = 8116163) B8116163
theorem B1806599 : Blo 842353 1806599 := bstep (se 1 (by rfl) ⟨1354949, by rfl⟩ : syracuseStep 1806599 = 2709899) B2709899
theorem B2134471 : Blo 842353 2134471 := bstep (se 1 (by rfl) ⟨1600853, by rfl⟩ : syracuseStep 2134471 = 3201707) B3201707
theorem B2856059 : Blo 842353 2856059 := bstep (se 1 (by rfl) ⟨2142044, by rfl⟩ : syracuseStep 2856059 = 4284089) B4284089
theorem B5412005 : Blo 842353 5412005 := bstep (se 4 (by rfl) ⟨507375, by rfl⟩ : syracuseStep 5412005 = 1014751) B1014751
theorem B21960001 : Blo 842353 21960001 := bstep (se 2 (by rfl) ⟨8235000, by rfl⟩ : syracuseStep 21960001 = 16470001) B16470001
theorem B2135423 : Blo 842353 2135423 := bstep (se 1 (by rfl) ⟨1601567, by rfl⟩ : syracuseStep 2135423 = 3203135) B3203135
theorem B14423447 : Blo 842353 14423447 := bstep (se 1 (by rfl) ⟨10817585, by rfl⟩ : syracuseStep 14423447 = 21635171) B21635171
theorem B9640295 : Blo 842353 9640295 := bstep (se 1 (by rfl) ⟨7230221, by rfl⟩ : syracuseStep 9640295 = 14460443) B14460443
theorem B2136527 : Blo 842353 2136527 := bstep (se 1 (by rfl) ⟨1602395, by rfl⟩ : syracuseStep 2136527 = 3204791) B3204791
theorem B3906191 : Blo 842353 3906191 := bstep (se 1 (by rfl) ⟨2929643, by rfl⟩ : syracuseStep 3906191 = 5859287) B5859287
theorem B9149111 : Blo 842353 9149111 := bstep (se 1 (by rfl) ⟨6861833, by rfl⟩ : syracuseStep 9149111 = 13723667) B13723667
theorem B1711567 : Blo 842353 1711567 := bstep (se 1 (by rfl) ⟨1283675, by rfl⟩ : syracuseStep 1711567 = 2567351) B2567351
theorem B21897877 : Blo 842353 21897877 := bstep (se 6 (by rfl) ⟨513231, by rfl⟩ : syracuseStep 21897877 = 1026463) B1026463
theorem B6399161 : Blo 842353 6399161 := bstep (se 2 (by rfl) ⟨2399685, by rfl⟩ : syracuseStep 6399161 = 4799371) B4799371
theorem B4269833 : Blo 842353 4269833 := bstep (se 2 (by rfl) ⟨1601187, by rfl⟩ : syracuseStep 4269833 = 3202375) B3202375
theorem B8661113 : Blo 842353 8661113 := bstep (se 2 (by rfl) ⟨3247917, by rfl⟩ : syracuseStep 8661113 = 6495835) B6495835
theorem B2566343 : Blo 842353 2566343 := bstep (se 1 (by rfl) ⟨1924757, by rfl⟩ : syracuseStep 2566343 = 3849515) B3849515
theorem B7219529 : Blo 842353 7219529 := bstep (se 2 (by rfl) ⟨2707323, by rfl⟩ : syracuseStep 7219529 = 5414647) B5414647
theorem B13183357 : Blo 842353 13183357 := bstep (se 3 (by rfl) ⟨2471879, by rfl⟩ : syracuseStep 13183357 = 4943759) B4943759
theorem B5417441 : Blo 842353 5417441 := bstep (se 2 (by rfl) ⟨2031540, by rfl⟩ : syracuseStep 5417441 = 4063081) B4063081
theorem B2403263 : Blo 842353 2403263 := bstep (se 1 (by rfl) ⟨1802447, by rfl⟩ : syracuseStep 2403263 = 3604895) B3604895
theorem B41003995 : Blo 842353 41003995 := bstep (se 1 (by rfl) ⟨30752996, by rfl⟩ : syracuseStep 41003995 = 61505993) B61505993
theorem B5484185 : Blo 842353 5484185 := bstep (se 2 (by rfl) ⟨2056569, by rfl⟩ : syracuseStep 5484185 = 4113139) B4113139
theorem B2404687 : Blo 842353 2404687 := bstep (se 1 (by rfl) ⟨1803515, by rfl⟩ : syracuseStep 2404687 = 3607031) B3607031
theorem B54833921 : Blo 842353 54833921 := bstep (se 2 (by rfl) ⟨20562720, by rfl⟩ : syracuseStep 54833921 = 41125441) B41125441
theorem B1422839 : Blo 842353 1422839 := bstep (se 1 (by rfl) ⟨1067129, by rfl⟩ : syracuseStep 1422839 = 2134259) B2134259
theorem B7222841 : Blo 842353 7222841 := bstep (se 2 (by rfl) ⟨2708565, by rfl⟩ : syracuseStep 7222841 = 5417131) B5417131
theorem B3422177 : Blo 842353 3422177 := bstep (se 2 (by rfl) ⟨1283316, by rfl⟩ : syracuseStep 3422177 = 2566633) B2566633
theorem B1423487 : Blo 842353 1423487 := bstep (se 1 (by rfl) ⟨1067615, by rfl⟩ : syracuseStep 1423487 = 2135231) B2135231
theorem B9124285 : Blo 842353 9124285 := bstep (se 3 (by rfl) ⟨1710803, by rfl⟩ : syracuseStep 9124285 = 3421607) B3421607
theorem B1423919 : Blo 842353 1423919 := bstep (se 1 (by rfl) ⟨1067939, by rfl⟩ : syracuseStep 1423919 = 2135879) B2135879
theorem B7223903 : Blo 842353 7223903 := bstep (se 1 (by rfl) ⟨5417927, by rfl⟩ : syracuseStep 7223903 = 10835855) B10835855
theorem B27344303 : Blo 842353 27344303 := bstep (se 1 (by rfl) ⟨20508227, by rfl⟩ : syracuseStep 27344303 = 41016455) B41016455
theorem B41041363 : Blo 842353 41041363 := bstep (se 1 (by rfl) ⟨30781022, by rfl⟩ : syracuseStep 41041363 = 61562045) B61562045
theorem B6405965 : Blo 842353 6405965 := bstep (se 3 (by rfl) ⟨1201118, by rfl⟩ : syracuseStep 6405965 = 2402237) B2402237
theorem B49299457 : Blo 842353 49299457 := bstep (se 2 (by rfl) ⟨18487296, by rfl⟩ : syracuseStep 49299457 = 36974593) B36974593
theorem B1622327 : Blo 842353 1622327 := bstep (se 1 (by rfl) ⟨1216745, by rfl⟩ : syracuseStep 1622327 = 2433491) B2433491
theorem B5194057 : Blo 842353 5194057 := bstep (se 2 (by rfl) ⟨1947771, by rfl⟩ : syracuseStep 5194057 = 3895543) B3895543
theorem B6406937 : Blo 842353 6406937 := bstep (se 2 (by rfl) ⟨2402601, by rfl⟩ : syracuseStep 6406937 = 4805203) B4805203
theorem B7128107 : Blo 842353 7128107 := bstep (se 1 (by rfl) ⟨5346080, by rfl⟩ : syracuseStep 7128107 = 10692161) B10692161
theorem B54871283 : Blo 842353 54871283 := bstep (se 1 (by rfl) ⟨41153462, by rfl⟩ : syracuseStep 54871283 = 82306925) B82306925
theorem B1426855 : Blo 842353 1426855 := bstep (se 1 (by rfl) ⟨1070141, by rfl⟩ : syracuseStep 1426855 = 2140283) B2140283
theorem B15812147 : Blo 842353 15812147 := bstep (se 1 (by rfl) ⟨11859110, by rfl⟩ : syracuseStep 15812147 = 23718221) B23718221
theorem B1263707 : Blo 842353 1263707 := bstep (se 1 (by rfl) ⟨947780, by rfl⟩ : syracuseStep 1263707 = 1895561) B1895561
theorem B1263743 : Blo 842353 1263743 := bstep (se 1 (by rfl) ⟨947807, by rfl⟩ : syracuseStep 1263743 = 1895615) B1895615
theorem B1264175 : Blo 842353 1264175 := bstep (se 1 (by rfl) ⟨948131, by rfl⟩ : syracuseStep 1264175 = 1896263) B1896263
theorem B1264295 : Blo 842353 1264295 := bstep (se 1 (by rfl) ⟨948221, by rfl⟩ : syracuseStep 1264295 = 1896443) B1896443
theorem B1264361 : Blo 842353 1264361 := bstep (se 2 (by rfl) ⟨474135, by rfl⟩ : syracuseStep 1264361 = 948271) B948271
theorem B1264415 : Blo 842353 1264415 := bstep (se 1 (by rfl) ⟨948311, by rfl⟩ : syracuseStep 1264415 = 1896623) B1896623
theorem B7720363 : Blo 842353 7720363 := bstep (se 1 (by rfl) ⟨5790272, by rfl⟩ : syracuseStep 7720363 = 11580545) B11580545
theorem B1625825 : Blo 842353 1625825 := bstep (se 2 (by rfl) ⟨609684, by rfl⟩ : syracuseStep 1625825 = 1219369) B1219369
theorem B12177935 : Blo 842353 12177935 := bstep (se 1 (by rfl) ⟨9133451, by rfl⟩ : syracuseStep 12177935 = 18266903) B18266903
theorem B1069615 : Blo 842353 1069615 := bstep (se 1 (by rfl) ⟨802211, by rfl⟩ : syracuseStep 1069615 = 1604423) B1604423
theorem B1266779 : Blo 842353 1266779 := bstep (se 1 (by rfl) ⟨950084, by rfl⟩ : syracuseStep 1266779 = 1900169) B1900169
theorem B1266809 : Blo 842353 1266809 := bstep (se 2 (by rfl) ⟨475053, by rfl⟩ : syracuseStep 1266809 = 950107) B950107
theorem B1627303 : Blo 842353 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B9131375 : Blo 842353 9131375 := bstep (se 1 (by rfl) ⟨6848531, by rfl⟩ : syracuseStep 9131375 = 13697063) B13697063
theorem B3200431 : Blo 842353 3200431 := bstep (se 1 (by rfl) ⟨2400323, by rfl⟩ : syracuseStep 3200431 = 4800647) B4800647
theorem B1267199 : Blo 842353 1267199 := bstep (se 1 (by rfl) ⟨950399, by rfl⟩ : syracuseStep 1267199 = 1900799) B1900799
theorem B3659347 : Blo 842353 3659347 := bstep (se 1 (by rfl) ⟨2744510, by rfl⟩ : syracuseStep 3659347 = 5489021) B5489021
theorem B6084355 : Blo 842353 6084355 := bstep (se 1 (by rfl) ⟨4563266, by rfl⟩ : syracuseStep 6084355 = 9126533) B9126533
theorem B1267577 : Blo 842353 1267577 := bstep (se 2 (by rfl) ⟨475341, by rfl⟩ : syracuseStep 1267577 = 950683) B950683
theorem B4872059 : Blo 842353 4872059 := bstep (se 1 (by rfl) ⟨3654044, by rfl⟩ : syracuseStep 4872059 = 7308089) B7308089
theorem B1267583 : Blo 842353 1267583 := bstep (se 1 (by rfl) ⟨950687, by rfl⟩ : syracuseStep 1267583 = 1901375) B1901375
theorem B14407955 : Blo 842353 14407955 := bstep (se 1 (by rfl) ⟨10805966, by rfl⟩ : syracuseStep 14407955 = 21611933) B21611933
theorem B1268351 : Blo 842353 1268351 := bstep (se 1 (by rfl) ⟨951263, by rfl⟩ : syracuseStep 1268351 = 1902527) B1902527
theorem B842395 : Blo 842353 842395 := bstep (se 1 (by rfl) ⟨631796, by rfl⟩ : syracuseStep 842395 = 1263593) B1263593
theorem B842491 : Blo 842353 842491 := bstep (se 1 (by rfl) ⟨631868, by rfl⟩ : syracuseStep 842491 = 1263737) B1263737
theorem B1268489 : Blo 842353 1268489 := bstep (se 2 (by rfl) ⟨475683, by rfl⟩ : syracuseStep 1268489 = 951367) B951367
theorem B842623 : Blo 842353 842623 := bstep (se 1 (by rfl) ⟨631967, by rfl⟩ : syracuseStep 842623 = 1263935) B1263935
theorem B842719 : Blo 842353 842719 := bstep (se 1 (by rfl) ⟨632039, by rfl⟩ : syracuseStep 842719 = 1264079) B1264079
theorem B1268729 : Blo 842353 1268729 := bstep (se 2 (by rfl) ⟨475773, by rfl⟩ : syracuseStep 1268729 = 951547) B951547
theorem B842747 : Blo 842353 842747 := bstep (se 1 (by rfl) ⟨632060, by rfl⟩ : syracuseStep 842747 = 1264121) B1264121
theorem B842779 : Blo 842353 842779 := bstep (se 1 (by rfl) ⟨632084, by rfl⟩ : syracuseStep 842779 = 1264169) B1264169
theorem B4283603 : Blo 842353 4283603 := bstep (se 1 (by rfl) ⟨3212702, by rfl⟩ : syracuseStep 4283603 = 6425405) B6425405
theorem B1269047 : Blo 842353 1269047 := bstep (se 1 (by rfl) ⟨951785, by rfl⟩ : syracuseStep 1269047 = 1903571) B1903571
theorem B843071 : Blo 842353 843071 := bstep (se 1 (by rfl) ⟨632303, by rfl⟩ : syracuseStep 843071 = 1264607) B1264607
theorem B1269227 : Blo 842353 1269227 := bstep (se 1 (by rfl) ⟨951920, by rfl⟩ : syracuseStep 1269227 = 1903841) B1903841
theorem B843367 : Blo 842353 843367 := bstep (se 1 (by rfl) ⟨632525, by rfl⟩ : syracuseStep 843367 = 1265051) B1265051
theorem B5496445 : Blo 842353 5496445 := bstep (se 3 (by rfl) ⟨1030583, by rfl⟩ : syracuseStep 5496445 = 2061167) B2061167
theorem B843611 : Blo 842353 843611 := bstep (se 1 (by rfl) ⟨632708, by rfl⟩ : syracuseStep 843611 = 1265417) B1265417
theorem B843647 : Blo 842353 843647 := bstep (se 1 (by rfl) ⟨632735, by rfl⟩ : syracuseStep 843647 = 1265471) B1265471
theorem B843807 : Blo 842353 843807 := bstep (se 1 (by rfl) ⟨632855, by rfl⟩ : syracuseStep 843807 = 1265711) B1265711
theorem B3039295 : Blo 842353 3039295 := bstep (se 1 (by rfl) ⟨2279471, by rfl⟩ : syracuseStep 3039295 = 4558943) B4558943
theorem B4055143 : Blo 842353 4055143 := bstep (se 1 (by rfl) ⟨3041357, by rfl⟩ : syracuseStep 4055143 = 6082715) B6082715
theorem B844103 : Blo 842353 844103 := bstep (se 1 (by rfl) ⟨633077, by rfl⟩ : syracuseStep 844103 = 1266155) B1266155
theorem B2842991 : Blo 842353 2842991 := bstep (se 1 (by rfl) ⟨2132243, by rfl⟩ : syracuseStep 2842991 = 4264487) B4264487
theorem B844187 : Blo 842353 844187 := bstep (se 1 (by rfl) ⟨633140, by rfl⟩ : syracuseStep 844187 = 1266281) B1266281
theorem B844191 : Blo 842353 844191 := bstep (se 1 (by rfl) ⟨633143, by rfl⟩ : syracuseStep 844191 = 1266287) B1266287
theorem B844271 : Blo 842353 844271 := bstep (se 1 (by rfl) ⟨633203, by rfl⟩ : syracuseStep 844271 = 1266407) B1266407
theorem B49242629 : Blo 842353 49242629 := bstep (se 4 (by rfl) ⟨4616496, by rfl⟩ : syracuseStep 49242629 = 9232993) B9232993
theorem B844379 : Blo 842353 844379 := bstep (se 1 (by rfl) ⟨633284, by rfl⟩ : syracuseStep 844379 = 1266569) B1266569
theorem B2843369 : Blo 842353 2843369 := bstep (se 2 (by rfl) ⟨1066263, by rfl⟩ : syracuseStep 2843369 = 2132527) B2132527
theorem B844607 : Blo 842353 844607 := bstep (se 1 (by rfl) ⟨633455, by rfl⟩ : syracuseStep 844607 = 1266911) B1266911
theorem B844635 : Blo 842353 844635 := bstep (se 1 (by rfl) ⟨633476, by rfl⟩ : syracuseStep 844635 = 1266953) B1266953
theorem B7201655 : Blo 842353 7201655 := bstep (se 1 (by rfl) ⟨5401241, by rfl⟩ : syracuseStep 7201655 = 10802483) B10802483
theorem B844927 : Blo 842353 844927 := bstep (se 1 (by rfl) ⟨633695, by rfl⟩ : syracuseStep 844927 = 1267391) B1267391
theorem B844955 : Blo 842353 844955 := bstep (se 1 (by rfl) ⟨633716, by rfl⟩ : syracuseStep 844955 = 1267433) B1267433
theorem B844959 : Blo 842353 844959 := bstep (se 1 (by rfl) ⟨633719, by rfl⟩ : syracuseStep 844959 = 1267439) B1267439
theorem B13001957 : Blo 842353 13001957 := bstep (se 4 (by rfl) ⟨1218933, by rfl⟩ : syracuseStep 13001957 = 2437867) B2437867
theorem B845295 : Blo 842353 845295 := bstep (se 1 (by rfl) ⟨633971, by rfl⟩ : syracuseStep 845295 = 1267943) B1267943
theorem B2844233 : Blo 842353 2844233 := bstep (se 2 (by rfl) ⟨1066587, by rfl⟩ : syracuseStep 2844233 = 2133175) B2133175
theorem B845415 : Blo 842353 845415 := bstep (se 1 (by rfl) ⟨634061, by rfl⟩ : syracuseStep 845415 = 1268123) B1268123
theorem B845679 : Blo 842353 845679 := bstep (se 1 (by rfl) ⟨634259, by rfl⟩ : syracuseStep 845679 = 1268519) B1268519
theorem B7202681 : Blo 842353 7202681 := bstep (se 2 (by rfl) ⟨2701005, by rfl⟩ : syracuseStep 7202681 = 5402011) B5402011
theorem B845695 : Blo 842353 845695 := bstep (se 1 (by rfl) ⟨634271, by rfl⟩ : syracuseStep 845695 = 1268543) B1268543
theorem B3205079 : Blo 842353 3205079 := bstep (se 1 (by rfl) ⟨2403809, by rfl⟩ : syracuseStep 3205079 = 4807619) B4807619
theorem B845895 : Blo 842353 845895 := bstep (se 1 (by rfl) ⟨634421, by rfl⟩ : syracuseStep 845895 = 1268843) B1268843
theorem B845991 : Blo 842353 845991 := bstep (se 1 (by rfl) ⟨634493, by rfl⟩ : syracuseStep 845991 = 1268987) B1268987
theorem B846055 : Blo 842353 846055 := bstep (se 1 (by rfl) ⟨634541, by rfl⟩ : syracuseStep 846055 = 1269083) B1269083
theorem B846075 : Blo 842353 846075 := bstep (se 1 (by rfl) ⟨634556, by rfl⟩ : syracuseStep 846075 = 1269113) B1269113
theorem B846079 : Blo 842353 846079 := bstep (se 1 (by rfl) ⟨634559, by rfl⟩ : syracuseStep 846079 = 1269119) B1269119
theorem B7695233 : Blo 842353 7695233 := bstep (se 2 (by rfl) ⟨2885712, by rfl⟩ : syracuseStep 7695233 = 5771425) B5771425
theorem B2845907 : Blo 842353 2845907 := bstep (se 1 (by rfl) ⟨2134430, by rfl⟩ : syracuseStep 2845907 = 4268861) B4268861
theorem B6417629 : Blo 842353 6417629 := bstep (se 3 (by rfl) ⟨1203305, by rfl⟩ : syracuseStep 6417629 = 2406611) B2406611
theorem B6418115 : Blo 842353 6418115 := bstep (se 1 (by rfl) ⟨4813586, by rfl⟩ : syracuseStep 6418115 = 9627173) B9627173
theorem B1896425 : Blo 842353 1896425 := bstep (se 2 (by rfl) ⟨711159, by rfl⟩ : syracuseStep 1896425 = 1422319) B1422319
theorem B1896479 : Blo 842353 1896479 := bstep (se 1 (by rfl) ⟨1422359, by rfl⟩ : syracuseStep 1896479 = 2844719) B2844719
theorem B6942829 : Blo 842353 6942829 := bstep (se 3 (by rfl) ⟨1301780, by rfl⟩ : syracuseStep 6942829 = 2603561) B2603561
theorem B7205071 : Blo 842353 7205071 := bstep (se 1 (by rfl) ⟨5403803, by rfl⟩ : syracuseStep 7205071 = 10807607) B10807607
theorem B1897127 : Blo 842353 1897127 := bstep (se 1 (by rfl) ⟨1422845, by rfl⟩ : syracuseStep 1897127 = 2845691) B2845691
theorem B2847905 : Blo 842353 2847905 := bstep (se 2 (by rfl) ⟨1067964, by rfl⟩ : syracuseStep 2847905 = 2135929) B2135929
theorem B1603451 : Blo 842353 1603451 := bstep (se 1 (by rfl) ⟨1202588, by rfl⟩ : syracuseStep 1603451 = 2405177) B2405177
theorem B1734967 : Blo 842353 1734967 := bstep (se 1 (by rfl) ⟨1301225, by rfl⟩ : syracuseStep 1734967 = 2602451) B2602451
theorem B948703 : Blo 842353 948703 := bstep (se 1 (by rfl) ⟨711527, by rfl⟩ : syracuseStep 948703 = 1423055) B1423055
theorem B1899035 : Blo 842353 1899035 := bstep (se 1 (by rfl) ⟨1424276, by rfl⟩ : syracuseStep 1899035 = 2848553) B2848553
theorem B41613929 : Blo 842353 41613929 := bstep (se 2 (by rfl) ⟨15605223, by rfl⟩ : syracuseStep 41613929 = 31210447) B31210447
theorem B12155791 : Blo 842353 12155791 := bstep (se 1 (by rfl) ⟨9116843, by rfl⟩ : syracuseStep 12155791 = 18233687) B18233687
theorem B2850281 : Blo 842353 2850281 := bstep (se 2 (by rfl) ⟨1068855, by rfl⟩ : syracuseStep 2850281 = 2137711) B2137711
theorem B3046895 : Blo 842353 3046895 := bstep (se 1 (by rfl) ⟨2285171, by rfl⟩ : syracuseStep 3046895 = 4570343) B4570343
theorem B133267031 : Blo 842353 133267031 := bstep (se 1 (by rfl) ⟨99950273, by rfl⟩ : syracuseStep 133267031 = 199900547) B199900547
theorem B3210911 : Blo 842353 3210911 := bstep (se 1 (by rfl) ⟨2408183, by rfl⟩ : syracuseStep 3210911 = 4816367) B4816367
theorem B65732609 : Blo 842353 65732609 := bstep (se 2 (by rfl) ⟨24649728, by rfl⟩ : syracuseStep 65732609 = 49299457) B49299457
theorem B5406857 : Blo 842353 5406857 := bstep (se 2 (by rfl) ⟨2027571, by rfl⟩ : syracuseStep 5406857 = 4055143) B4055143
theorem B4752071 : Blo 842353 4752071 := bstep (se 1 (by rfl) ⟨3564053, by rfl⟩ : syracuseStep 4752071 = 7128107) B7128107
theorem B1901339 : Blo 842353 1901339 := bstep (se 1 (by rfl) ⟨1426004, by rfl⟩ : syracuseStep 1901339 = 2852009) B2852009
theorem B4326205 : Blo 842353 4326205 := bstep (se 3 (by rfl) ⟨811163, by rfl⟩ : syracuseStep 4326205 = 1622327) B1622327
theorem B29197169 : Blo 842353 29197169 := bstep (se 2 (by rfl) ⟨10948938, by rfl⟩ : syracuseStep 29197169 = 21897877) B21897877
theorem B3212399 : Blo 842353 3212399 := bstep (se 1 (by rfl) ⟨2409299, by rfl⟩ : syracuseStep 3212399 = 4818599) B4818599
theorem B1902239 : Blo 842353 1902239 := bstep (se 1 (by rfl) ⟨1426679, by rfl⟩ : syracuseStep 1902239 = 2853359) B2853359
theorem B3606227 : Blo 842353 3606227 := bstep (se 1 (by rfl) ⟨2704670, by rfl⟩ : syracuseStep 3606227 = 5409341) B5409341
theorem B1902473 : Blo 842353 1902473 := bstep (se 2 (by rfl) ⟨713427, by rfl⟩ : syracuseStep 1902473 = 1426855) B1426855
theorem B1902491 : Blo 842353 1902491 := bstep (se 1 (by rfl) ⟨1426868, by rfl⟩ : syracuseStep 1902491 = 2853737) B2853737
theorem B2164703 : Blo 842353 2164703 := bstep (se 1 (by rfl) ⟨1623527, by rfl⟩ : syracuseStep 2164703 = 3247055) B3247055
theorem B2164943 : Blo 842353 2164943 := bstep (se 1 (by rfl) ⟨1623707, by rfl⟩ : syracuseStep 2164943 = 3247415) B3247415
theorem B1083883 : Blo 842353 1083883 := bstep (se 1 (by rfl) ⟨812912, by rfl⟩ : syracuseStep 1083883 = 1625825) B1625825
theorem B3607183 : Blo 842353 3607183 := bstep (se 1 (by rfl) ⟨2705387, by rfl⟩ : syracuseStep 3607183 = 5410775) B5410775
theorem B5770025 : Blo 842353 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B1904039 : Blo 842353 1904039 := bstep (se 1 (by rfl) ⟨1428029, by rfl⟩ : syracuseStep 1904039 = 2856059) B2856059
theorem B3608003 : Blo 842353 3608003 := bstep (se 1 (by rfl) ⟨2706002, by rfl⟩ : syracuseStep 3608003 = 5412005) B5412005
theorem B3248039 : Blo 842353 3248039 := bstep (se 1 (by rfl) ⟨2436029, by rfl⟩ : syracuseStep 3248039 = 4872059) B4872059
theorem B9605303 : Blo 842353 9605303 := bstep (se 1 (by rfl) ⟨7203977, by rfl⟩ : syracuseStep 9605303 = 14407955) B14407955
theorem B6426863 : Blo 842353 6426863 := bstep (se 1 (by rfl) ⟨4820147, by rfl⟩ : syracuseStep 6426863 = 9640295) B9640295
theorem B6099407 : Blo 842353 6099407 := bstep (se 1 (by rfl) ⟨4574555, by rfl⟩ : syracuseStep 6099407 = 9149111) B9149111
theorem B10293817 : Blo 842353 10293817 := bstep (se 2 (by rfl) ⟨3860181, by rfl⟩ : syracuseStep 10293817 = 7720363) B7720363
theorem B2855735 : Blo 842353 2855735 := bstep (se 1 (by rfl) ⟨2141801, by rfl⟩ : syracuseStep 2855735 = 4283603) B4283603
theorem B9606761 : Blo 842353 9606761 := bstep (se 2 (by rfl) ⟨3602535, by rfl⟩ : syracuseStep 9606761 = 7205071) B7205071
theorem B4266107 : Blo 842353 4266107 := bstep (se 1 (by rfl) ⟨3199580, by rfl⟩ : syracuseStep 4266107 = 6399161) B6399161
theorem B2136719 : Blo 842353 2136719 := bstep (se 1 (by rfl) ⟨1602539, by rfl⟩ : syracuseStep 2136719 = 3205079) B3205079
theorem B5774075 : Blo 842353 5774075 := bstep (se 1 (by rfl) ⟨4330556, by rfl⟩ : syracuseStep 5774075 = 8661113) B8661113
theorem B1710895 : Blo 842353 1710895 := bstep (se 1 (by rfl) ⟨1283171, by rfl⟩ : syracuseStep 1710895 = 2566343) B2566343
theorem B2169737 : Blo 842353 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B3611627 : Blo 842353 3611627 := bstep (se 1 (by rfl) ⟨2708720, by rfl⟩ : syracuseStep 3611627 = 5417441) B5417441
theorem B4267241 : Blo 842353 4267241 := bstep (se 2 (by rfl) ⟨1600215, by rfl⟩ : syracuseStep 4267241 = 3200431) B3200431
theorem B27794717 : Blo 842353 27794717 := bstep (se 3 (by rfl) ⟨5211509, by rfl⟩ : syracuseStep 27794717 = 10423019) B10423019
theorem B12165713 : Blo 842353 12165713 := bstep (se 2 (by rfl) ⟨4562142, by rfl⟩ : syracuseStep 12165713 = 9124285) B9124285
theorem B18229535 : Blo 842353 18229535 := bstep (se 1 (by rfl) ⟨13672151, by rfl⟩ : syracuseStep 18229535 = 27344303) B27344303
theorem B88844687 : Blo 842353 88844687 := bstep (se 1 (by rfl) ⟨66633515, by rfl⟩ : syracuseStep 88844687 = 133267031) B133267031
theorem B2140607 : Blo 842353 2140607 := bstep (se 1 (by rfl) ⟨1605455, by rfl⟩ : syracuseStep 2140607 = 3210911) B3210911
theorem B4270643 : Blo 842353 4270643 := bstep (se 1 (by rfl) ⟨3202982, by rfl⟩ : syracuseStep 4270643 = 6405965) B6405965
theorem B2141275 : Blo 842353 2141275 := bstep (se 1 (by rfl) ⟨1605956, by rfl⟩ : syracuseStep 2141275 = 3211913) B3211913
theorem B6925409 : Blo 842353 6925409 := bstep (se 2 (by rfl) ⟨2597028, by rfl⟩ : syracuseStep 6925409 = 5194057) B5194057
theorem B4271291 : Blo 842353 4271291 := bstep (se 1 (by rfl) ⟨3203468, by rfl⟩ : syracuseStep 4271291 = 6406937) B6406937
theorem B36580855 : Blo 842353 36580855 := bstep (se 1 (by rfl) ⟨27435641, by rfl⟩ : syracuseStep 36580855 = 54871283) B54871283
theorem B2142035 : Blo 842353 2142035 := bstep (se 1 (by rfl) ⟨1606526, by rfl⟩ : syracuseStep 2142035 = 3213053) B3213053
theorem B2404379 : Blo 842353 2404379 := bstep (se 1 (by rfl) ⟨1803284, by rfl⟩ : syracuseStep 2404379 = 3606569) B3606569
theorem B2142247 : Blo 842353 2142247 := bstep (se 1 (by rfl) ⟨1606685, by rfl⟩ : syracuseStep 2142247 = 3213371) B3213371
theorem B1421759 : Blo 842353 1421759 := bstep (se 1 (by rfl) ⟨1066319, by rfl⟩ : syracuseStep 1421759 = 2132639) B2132639
theorem B17577809 : Blo 842353 17577809 := bstep (se 2 (by rfl) ⟨6591678, by rfl⟩ : syracuseStep 17577809 = 13183357) B13183357
theorem B1423615 : Blo 842353 1423615 := bstep (se 1 (by rfl) ⟨1067711, by rfl⟩ : syracuseStep 1423615 = 2135423) B2135423
theorem B9615631 : Blo 842353 9615631 := bstep (se 1 (by rfl) ⟨7211723, by rfl⟩ : syracuseStep 9615631 = 14423447) B14423447
theorem B54671993 : Blo 842353 54671993 := bstep (se 2 (by rfl) ⟨20501997, by rfl⟩ : syracuseStep 54671993 = 41003995) B41003995
theorem B1424351 : Blo 842353 1424351 := bstep (se 1 (by rfl) ⟨1068263, by rfl⟩ : syracuseStep 1424351 = 2136527) B2136527
theorem B9257105 : Blo 842353 9257105 := bstep (se 2 (by rfl) ⟨3471414, by rfl⟩ : syracuseStep 9257105 = 6942829) B6942829
theorem B4801103 : Blo 842353 4801103 := bstep (se 1 (by rfl) ⟨3600827, by rfl⟩ : syracuseStep 4801103 = 7201655) B7201655
theorem B1426153 : Blo 842353 1426153 := bstep (se 2 (by rfl) ⟨534807, by rfl⟩ : syracuseStep 1426153 = 1069615) B1069615
theorem B8667971 : Blo 842353 8667971 := bstep (se 1 (by rfl) ⟨6500978, by rfl⟩ : syracuseStep 8667971 = 13001957) B13001957
theorem B4801787 : Blo 842353 4801787 := bstep (se 1 (by rfl) ⟨3601340, by rfl⟩ : syracuseStep 4801787 = 7202681) B7202681
theorem B29280001 : Blo 842353 29280001 := bstep (se 2 (by rfl) ⟨10980000, by rfl⟩ : syracuseStep 29280001 = 21960001) B21960001
theorem B5130155 : Blo 842353 5130155 := bstep (se 1 (by rfl) ⟨3847616, by rfl⟩ : syracuseStep 5130155 = 7695233) B7695233
theorem B4278419 : Blo 842353 4278419 := bstep (se 1 (by rfl) ⟨3208814, by rfl⟩ : syracuseStep 4278419 = 6417629) B6417629
theorem B8112473 : Blo 842353 8112473 := bstep (se 2 (by rfl) ⟨3042177, by rfl⟩ : syracuseStep 8112473 = 6084355) B6084355
theorem B3656123 : Blo 842353 3656123 := bstep (se 1 (by rfl) ⟨2742092, by rfl⟩ : syracuseStep 3656123 = 5484185) B5484185
theorem B4278743 : Blo 842353 4278743 := bstep (se 1 (by rfl) ⟨3209057, by rfl⟩ : syracuseStep 4278743 = 6418115) B6418115
theorem B1264283 : Blo 842353 1264283 := bstep (se 1 (by rfl) ⟨948212, by rfl⟩ : syracuseStep 1264283 = 1896425) B1896425
theorem B1264319 : Blo 842353 1264319 := bstep (se 1 (by rfl) ⟨948239, by rfl⟩ : syracuseStep 1264319 = 1896479) B1896479
theorem B2313289 : Blo 842353 2313289 := bstep (se 2 (by rfl) ⟨867483, by rfl⟩ : syracuseStep 2313289 = 1734967) B1734967
theorem B1264751 : Blo 842353 1264751 := bstep (se 1 (by rfl) ⟨948563, by rfl⟩ : syracuseStep 1264751 = 1897127) B1897127
theorem B36555947 : Blo 842353 36555947 := bstep (se 1 (by rfl) ⟨27416960, by rfl⟩ : syracuseStep 36555947 = 54833921) B54833921
theorem B1264937 : Blo 842353 1264937 := bstep (se 2 (by rfl) ⟨474351, by rfl⟩ : syracuseStep 1264937 = 948703) B948703
theorem B16207721 : Blo 842353 16207721 := bstep (se 2 (by rfl) ⟨6077895, by rfl⟩ : syracuseStep 16207721 = 12155791) B12155791
theorem B1068967 : Blo 842353 1068967 := bstep (se 1 (by rfl) ⟨801725, by rfl⟩ : syracuseStep 1068967 = 1603451) B1603451
theorem B2281451 : Blo 842353 2281451 := bstep (se 1 (by rfl) ⟨1711088, by rfl⟩ : syracuseStep 2281451 = 3422177) B3422177
theorem B1266023 : Blo 842353 1266023 := bstep (se 1 (by rfl) ⟨949517, by rfl⟩ : syracuseStep 1266023 = 1899035) B1899035
theorem B27742619 : Blo 842353 27742619 := bstep (se 1 (by rfl) ⟨20806964, by rfl⟩ : syracuseStep 27742619 = 41613929) B41613929
theorem B2282089 : Blo 842353 2282089 := bstep (se 2 (by rfl) ⟨855783, by rfl⟩ : syracuseStep 2282089 = 1711567) B1711567
theorem B7328593 : Blo 842353 7328593 := bstep (se 2 (by rfl) ⟨2748222, by rfl⟩ : syracuseStep 7328593 = 5496445) B5496445
theorem B4052393 : Blo 842353 4052393 := bstep (se 2 (by rfl) ⟨1519647, by rfl⟩ : syracuseStep 4052393 = 3039295) B3039295
theorem B1267151 : Blo 842353 1267151 := bstep (se 1 (by rfl) ⟨950363, by rfl⟩ : syracuseStep 1267151 = 1900727) B1900727
theorem B1071083 : Blo 842353 1071083 := bstep (se 1 (by rfl) ⟨803312, by rfl⟩ : syracuseStep 1071083 = 1606625) B1606625
theorem B1267823 : Blo 842353 1267823 := bstep (se 1 (by rfl) ⟨950867, by rfl⟩ : syracuseStep 1267823 = 1901735) B1901735
theorem B10541431 : Blo 842353 10541431 := bstep (se 1 (by rfl) ⟨7906073, by rfl⟩ : syracuseStep 10541431 = 15812147) B15812147
theorem B4282793 : Blo 842353 4282793 := bstep (se 2 (by rfl) ⟨1606047, by rfl⟩ : syracuseStep 4282793 = 3212095) B3212095
theorem B842471 : Blo 842353 842471 := bstep (se 1 (by rfl) ⟨631853, by rfl⟩ : syracuseStep 842471 = 1263707) B1263707
theorem B842495 : Blo 842353 842495 := bstep (se 1 (by rfl) ⟨631871, by rfl⟩ : syracuseStep 842495 = 1263743) B1263743
theorem B842783 : Blo 842353 842783 := bstep (se 1 (by rfl) ⟨632087, by rfl⟩ : syracuseStep 842783 = 1264175) B1264175
theorem B842863 : Blo 842353 842863 := bstep (se 1 (by rfl) ⟨632147, by rfl⟩ : syracuseStep 842863 = 1264295) B1264295
theorem B1268873 : Blo 842353 1268873 := bstep (se 2 (by rfl) ⟨475827, by rfl⟩ : syracuseStep 1268873 = 951655) B951655
theorem B842907 : Blo 842353 842907 := bstep (se 1 (by rfl) ⟨632180, by rfl⟩ : syracuseStep 842907 = 1264361) B1264361
theorem B1268891 : Blo 842353 1268891 := bstep (se 1 (by rfl) ⟨951668, by rfl⟩ : syracuseStep 1268891 = 1903337) B1903337
theorem B842943 : Blo 842353 842943 := bstep (se 1 (by rfl) ⟨632207, by rfl⟩ : syracuseStep 842943 = 1264415) B1264415
theorem B1268927 : Blo 842353 1268927 := bstep (se 1 (by rfl) ⟨951695, by rfl⟩ : syracuseStep 1268927 = 1903391) B1903391
theorem B1203511 : Blo 842353 1203511 := bstep (se 1 (by rfl) ⟨902633, by rfl⟩ : syracuseStep 1203511 = 1805267) B1805267
theorem B4808119 : Blo 842353 4808119 := bstep (se 1 (by rfl) ⟨3606089, by rfl⟩ : syracuseStep 4808119 = 7212179) B7212179
theorem B1204399 : Blo 842353 1204399 := bstep (se 1 (by rfl) ⟨903299, by rfl⟩ : syracuseStep 1204399 = 1806599) B1806599
theorem B8118623 : Blo 842353 8118623 := bstep (se 1 (by rfl) ⟨6088967, by rfl⟩ : syracuseStep 8118623 = 12177935) B12177935
theorem B844519 : Blo 842353 844519 := bstep (se 1 (by rfl) ⟨633389, by rfl⟩ : syracuseStep 844519 = 1266779) B1266779
theorem B844539 : Blo 842353 844539 := bstep (se 1 (by rfl) ⟨633404, by rfl⟩ : syracuseStep 844539 = 1266809) B1266809
theorem B47539061 : Blo 842353 47539061 := bstep (se 5 (by rfl) ⟨2228393, by rfl⟩ : syracuseStep 47539061 = 4456787) B4456787
theorem B6087583 : Blo 842353 6087583 := bstep (se 1 (by rfl) ⟨4565687, by rfl⟩ : syracuseStep 6087583 = 9131375) B9131375
theorem B844799 : Blo 842353 844799 := bstep (se 1 (by rfl) ⟨633599, by rfl⟩ : syracuseStep 844799 = 1267199) B1267199
theorem B845051 : Blo 842353 845051 := bstep (se 1 (by rfl) ⟨633788, by rfl⟩ : syracuseStep 845051 = 1267577) B1267577
theorem B845055 : Blo 842353 845055 := bstep (se 1 (by rfl) ⟨633791, by rfl⟩ : syracuseStep 845055 = 1267583) B1267583
theorem B845567 : Blo 842353 845567 := bstep (se 1 (by rfl) ⟨634175, by rfl⟩ : syracuseStep 845567 = 1268351) B1268351
theorem B845659 : Blo 842353 845659 := bstep (se 1 (by rfl) ⟨634244, by rfl⟩ : syracuseStep 845659 = 1268489) B1268489
theorem B845819 : Blo 842353 845819 := bstep (se 1 (by rfl) ⟨634364, by rfl⟩ : syracuseStep 845819 = 1268729) B1268729
theorem B846031 : Blo 842353 846031 := bstep (se 1 (by rfl) ⟨634523, by rfl⟩ : syracuseStep 846031 = 1269047) B1269047
theorem B846151 : Blo 842353 846151 := bstep (se 1 (by rfl) ⟨634613, by rfl⟩ : syracuseStep 846151 = 1269227) B1269227
theorem B1895327 : Blo 842353 1895327 := bstep (se 1 (by rfl) ⟨1421495, by rfl⟩ : syracuseStep 1895327 = 2842991) B2842991
theorem B32828419 : Blo 842353 32828419 := bstep (se 1 (by rfl) ⟨24621314, by rfl⟩ : syracuseStep 32828419 = 49242629) B49242629
theorem B3206249 : Blo 842353 3206249 := bstep (se 2 (by rfl) ⟨1202343, by rfl⟩ : syracuseStep 3206249 = 2404687) B2404687
theorem B1895579 : Blo 842353 1895579 := bstep (se 1 (by rfl) ⟨1421684, by rfl⟩ : syracuseStep 1895579 = 2843369) B2843369
theorem B2845961 : Blo 842353 2845961 := bstep (se 2 (by rfl) ⟨1067235, by rfl⟩ : syracuseStep 2845961 = 2134471) B2134471
theorem B1896155 : Blo 842353 1896155 := bstep (se 1 (by rfl) ⟨1422116, by rfl⟩ : syracuseStep 1896155 = 2844233) B2844233
theorem B2846555 : Blo 842353 2846555 := bstep (se 1 (by rfl) ⟨2134916, by rfl⟩ : syracuseStep 2846555 = 4269833) B4269833
theorem B4813019 : Blo 842353 4813019 := bstep (se 1 (by rfl) ⟨3609764, by rfl⟩ : syracuseStep 4813019 = 7219529) B7219529
theorem B10416509 : Blo 842353 10416509 := bstep (se 3 (by rfl) ⟨1953095, by rfl⟩ : syracuseStep 10416509 = 3906191) B3906191
theorem B1602175 : Blo 842353 1602175 := bstep (se 1 (by rfl) ⟨1201631, by rfl⟩ : syracuseStep 1602175 = 2403263) B2403263
theorem B4879129 : Blo 842353 4879129 := bstep (se 2 (by rfl) ⟨1829673, by rfl⟩ : syracuseStep 4879129 = 3659347) B3659347
theorem B1897271 : Blo 842353 1897271 := bstep (se 1 (by rfl) ⟨1422953, by rfl⟩ : syracuseStep 1897271 = 2845907) B2845907
theorem B1898603 : Blo 842353 1898603 := bstep (se 1 (by rfl) ⟨1423952, by rfl⟩ : syracuseStep 1898603 = 2847905) B2847905
theorem B948559 : Blo 842353 948559 := bstep (se 1 (by rfl) ⟨711419, by rfl⟩ : syracuseStep 948559 = 1422839) B1422839
theorem B4815227 : Blo 842353 4815227 := bstep (se 1 (by rfl) ⟨3611420, by rfl⟩ : syracuseStep 4815227 = 7222841) B7222841
theorem B948991 : Blo 842353 948991 := bstep (se 1 (by rfl) ⟨711743, by rfl⟩ : syracuseStep 948991 = 1423487) B1423487
theorem B949279 : Blo 842353 949279 := bstep (se 1 (by rfl) ⟨711959, by rfl⟩ : syracuseStep 949279 = 1423919) B1423919
theorem B4815935 : Blo 842353 4815935 := bstep (se 1 (by rfl) ⟨3611951, by rfl⟩ : syracuseStep 4815935 = 7223903) B7223903
theorem B54721817 : Blo 842353 54721817 := bstep (se 2 (by rfl) ⟨20520681, by rfl⟩ : syracuseStep 54721817 = 41041363) B41041363
theorem B1900187 : Blo 842353 1900187 := bstep (se 1 (by rfl) ⟨1425140, by rfl⟩ : syracuseStep 1900187 = 2850281) B2850281
theorem B2031263 : Blo 842353 2031263 := bstep (se 1 (by rfl) ⟨1523447, by rfl⟩ : syracuseStep 2031263 = 3046895) B3046895
theorem B3604571 : Blo 842353 3604571 := bstep (se 1 (by rfl) ⟨2703428, by rfl⟩ : syracuseStep 3604571 = 5406857) B5406857
theorem B19464779 : Blo 842353 19464779 := bstep (se 1 (by rfl) ⟨14598584, by rfl⟩ : syracuseStep 19464779 = 29197169) B29197169
theorem B6423461 : Blo 842353 6423461 := bstep (se 4 (by rfl) ⟨602199, by rfl⟩ : syracuseStep 6423461 = 1204399) B1204399
theorem B1901537 : Blo 842353 1901537 := bstep (se 2 (by rfl) ⟨713076, by rfl⟩ : syracuseStep 1901537 = 1426153) B1426153
theorem B5768273 : Blo 842353 5768273 := bstep (se 2 (by rfl) ⟨2163102, by rfl⟩ : syracuseStep 5768273 = 4326205) B4326205
theorem B2852279 : Blo 842353 2852279 := bstep (se 1 (by rfl) ⟨2139209, by rfl⟩ : syracuseStep 2852279 = 4278419) B4278419
theorem B1443295 : Blo 842353 1443295 := bstep (se 1 (by rfl) ⟨1082471, by rfl⟩ : syracuseStep 1443295 = 2164943) B2164943
theorem B5408315 : Blo 842353 5408315 := bstep (se 1 (by rfl) ⟨4056236, by rfl⟩ : syracuseStep 5408315 = 8112473) B8112473
theorem B2852495 : Blo 842353 2852495 := bstep (se 1 (by rfl) ⟨2139371, by rfl⟩ : syracuseStep 2852495 = 4278743) B4278743
theorem B4066271 : Blo 842353 4066271 := bstep (se 1 (by rfl) ⟨3049703, by rfl⟩ : syracuseStep 4066271 = 6099407) B6099407
theorem B1903823 : Blo 842353 1903823 := bstep (se 1 (by rfl) ⟨1427867, by rfl⟩ : syracuseStep 1903823 = 2855735) B2855735
theorem B1445177 : Blo 842353 1445177 := bstep (se 2 (by rfl) ⟨541941, by rfl⟩ : syracuseStep 1445177 = 1083883) B1083883
theorem B2855033 : Blo 842353 2855033 := bstep (se 2 (by rfl) ⟨1070637, by rfl⟩ : syracuseStep 2855033 = 2141275) B2141275
theorem B2855195 : Blo 842353 2855195 := bstep (se 1 (by rfl) ⟨2141396, by rfl⟩ : syracuseStep 2855195 = 4282793) B4282793
theorem B1446491 : Blo 842353 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B5772541 : Blo 842353 5772541 := bstep (se 3 (by rfl) ⟨1082351, by rfl⟩ : syracuseStep 5772541 = 2164703) B2164703
theorem B2856221 : Blo 842353 2856221 := bstep (se 3 (by rfl) ⟨535541, by rfl⟩ : syracuseStep 2856221 = 1071083) B1071083
theorem B175084901 : Blo 842353 175084901 := bstep (se 4 (by rfl) ⟨16414209, by rfl⟩ : syracuseStep 175084901 = 32828419) B32828419
theorem B2856329 : Blo 842353 2856329 := bstep (se 2 (by rfl) ⟨1071123, by rfl⟩ : syracuseStep 2856329 = 2142247) B2142247
theorem B5412415 : Blo 842353 5412415 := bstep (se 1 (by rfl) ⟨4059311, by rfl⟩ : syracuseStep 5412415 = 8118623) B8118623
theorem B31692707 : Blo 842353 31692707 := bstep (se 1 (by rfl) ⟨23769530, by rfl⟩ : syracuseStep 31692707 = 47539061) B47539061
theorem B2136233 : Blo 842353 2136233 := bstep (se 2 (by rfl) ⟨801087, by rfl⟩ : syracuseStep 2136233 = 1602175) B1602175
theorem B9771457 : Blo 842353 9771457 := bstep (se 2 (by rfl) ⟨3664296, by rfl⟩ : syracuseStep 9771457 = 7328593) B7328593
theorem B2137499 : Blo 842353 2137499 := bstep (se 1 (by rfl) ⟨1603124, by rfl⟩ : syracuseStep 2137499 = 3206249) B3206249
theorem B12820841 : Blo 842353 12820841 := bstep (se 2 (by rfl) ⟨4807815, by rfl⟩ : syracuseStep 12820841 = 9615631) B9615631
theorem B36447995 : Blo 842353 36447995 := bstep (se 1 (by rfl) ⟨27335996, by rfl⟩ : syracuseStep 36447995 = 54671993) B54671993
theorem B36481211 : Blo 842353 36481211 := bstep (se 1 (by rfl) ⟨27360908, by rfl⟩ : syracuseStep 36481211 = 54721817) B54721817
theorem B8661437 : Blo 842353 8661437 := bstep (se 3 (by rfl) ⟨1624019, by rfl⟩ : syracuseStep 8661437 = 3248039) B3248039
theorem B1354175 : Blo 842353 1354175 := bstep (se 1 (by rfl) ⟨1015631, by rfl⟩ : syracuseStep 1354175 = 2031263) B2031263
theorem B43821739 : Blo 842353 43821739 := bstep (se 1 (by rfl) ⟨32866304, by rfl⟩ : syracuseStep 43821739 = 65732609) B65732609
theorem B6171403 : Blo 842353 6171403 := bstep (se 1 (by rfl) ⟨4628552, by rfl⟩ : syracuseStep 6171403 = 9257105) B9257105
theorem B5778647 : Blo 842353 5778647 := bstep (se 1 (by rfl) ⟨4333985, by rfl⟩ : syracuseStep 5778647 = 8667971) B8667971
theorem B2141599 : Blo 842353 2141599 := bstep (se 1 (by rfl) ⟨1606199, by rfl⟩ : syracuseStep 2141599 = 3212399) B3212399
theorem B2404151 : Blo 842353 2404151 := bstep (se 1 (by rfl) ⟨1803113, by rfl⟩ : syracuseStep 2404151 = 3606227) B3606227
theorem B3420103 : Blo 842353 3420103 := bstep (se 1 (by rfl) ⟨2565077, by rfl⟩ : syracuseStep 3420103 = 5130155) B5130155
theorem B2437415 : Blo 842353 2437415 := bstep (se 1 (by rfl) ⟨1828061, by rfl⟩ : syracuseStep 2437415 = 3656123) B3656123
theorem B3846683 : Blo 842353 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B39040001 : Blo 842353 39040001 := bstep (se 2 (by rfl) ⟨14640000, by rfl⟩ : syracuseStep 39040001 = 29280001) B29280001
theorem B6403535 : Blo 842353 6403535 := bstep (se 1 (by rfl) ⟨4802651, by rfl⟩ : syracuseStep 6403535 = 9605303) B9605303
theorem B2701595 : Blo 842353 2701595 := bstep (se 1 (by rfl) ⟨2026196, by rfl⟩ : syracuseStep 2701595 = 4052393) B4052393
theorem B6404507 : Blo 842353 6404507 := bstep (se 1 (by rfl) ⟨4803380, by rfl⟩ : syracuseStep 6404507 = 9606761) B9606761
theorem B1424479 : Blo 842353 1424479 := bstep (se 1 (by rfl) ⟨1068359, by rfl⟩ : syracuseStep 1424479 = 2136719) B2136719
theorem B3849383 : Blo 842353 3849383 := bstep (se 1 (by rfl) ⟨2887037, by rfl⟩ : syracuseStep 3849383 = 5774075) B5774075
theorem B2407751 : Blo 842353 2407751 := bstep (se 1 (by rfl) ⟨1805813, by rfl⟩ : syracuseStep 2407751 = 3611627) B3611627
theorem B48774473 : Blo 842353 48774473 := bstep (se 2 (by rfl) ⟨18290427, by rfl⟩ : syracuseStep 48774473 = 36580855) B36580855
theorem B18529811 : Blo 842353 18529811 := bstep (se 1 (by rfl) ⟨13897358, by rfl⟩ : syracuseStep 18529811 = 27794717) B27794717
theorem B1425289 : Blo 842353 1425289 := bstep (se 2 (by rfl) ⟨534483, by rfl⟩ : syracuseStep 1425289 = 1068967) B1068967
theorem B12337541 : Blo 842353 12337541 := bstep (se 4 (by rfl) ⟨1156644, by rfl⟩ : syracuseStep 12337541 = 2313289) B2313289
theorem B8110475 : Blo 842353 8110475 := bstep (se 1 (by rfl) ⟨6082856, by rfl⟩ : syracuseStep 8110475 = 12165713) B12165713
theorem B6505505 : Blo 842353 6505505 := bstep (se 2 (by rfl) ⟨2439564, by rfl⟩ : syracuseStep 6505505 = 4879129) B4879129
theorem B59229791 : Blo 842353 59229791 := bstep (se 1 (by rfl) ⟨44422343, by rfl⟩ : syracuseStep 59229791 = 88844687) B88844687
theorem B1427071 : Blo 842353 1427071 := bstep (se 1 (by rfl) ⟨1070303, by rfl⟩ : syracuseStep 1427071 = 2140607) B2140607
theorem B1263551 : Blo 842353 1263551 := bstep (se 1 (by rfl) ⟨947663, by rfl⟩ : syracuseStep 1263551 = 1895327) B1895327
theorem B1263719 : Blo 842353 1263719 := bstep (se 1 (by rfl) ⟨947789, by rfl⟩ : syracuseStep 1263719 = 1895579) B1895579
theorem B1264103 : Blo 842353 1264103 := bstep (se 1 (by rfl) ⟨948077, by rfl⟩ : syracuseStep 1264103 = 1896155) B1896155
theorem B1428023 : Blo 842353 1428023 := bstep (se 1 (by rfl) ⟨1071017, by rfl⟩ : syracuseStep 1428023 = 2142035) B2142035
theorem B1264745 : Blo 842353 1264745 := bstep (se 2 (by rfl) ⟨474279, by rfl⟩ : syracuseStep 1264745 = 948559) B948559
theorem B1264847 : Blo 842353 1264847 := bstep (se 1 (by rfl) ⟨948635, by rfl⟩ : syracuseStep 1264847 = 1897271) B1897271
theorem B1265321 : Blo 842353 1265321 := bstep (se 2 (by rfl) ⟨474495, by rfl⟩ : syracuseStep 1265321 = 948991) B948991
theorem B2281193 : Blo 842353 2281193 := bstep (se 2 (by rfl) ⟨855447, by rfl⟩ : syracuseStep 2281193 = 1710895) B1710895
theorem B9621341 : Blo 842353 9621341 := bstep (se 3 (by rfl) ⟨1804001, by rfl⟩ : syracuseStep 9621341 = 3608003) B3608003
theorem B11718539 : Blo 842353 11718539 := bstep (se 1 (by rfl) ⟨8788904, by rfl⟩ : syracuseStep 11718539 = 17577809) B17577809
theorem B1265705 : Blo 842353 1265705 := bstep (se 2 (by rfl) ⟨474639, by rfl⟩ : syracuseStep 1265705 = 949279) B949279
theorem B1265735 : Blo 842353 1265735 := bstep (se 1 (by rfl) ⟨949301, by rfl⟩ : syracuseStep 1265735 = 1898603) B1898603
theorem B6410825 : Blo 842353 6410825 := bstep (se 2 (by rfl) ⟨2404059, by rfl⟩ : syracuseStep 6410825 = 4808119) B4808119
theorem B1266791 : Blo 842353 1266791 := bstep (se 1 (by rfl) ⟨950093, by rfl⟩ : syracuseStep 1266791 = 1900187) B1900187
theorem B6083869 : Blo 842353 6083869 := bstep (se 3 (by rfl) ⟨1140725, by rfl⟩ : syracuseStep 6083869 = 2281451) B2281451
theorem B3200735 : Blo 842353 3200735 := bstep (se 1 (by rfl) ⟨2400551, by rfl⟩ : syracuseStep 3200735 = 4801103) B4801103
theorem B3168047 : Blo 842353 3168047 := bstep (se 1 (by rfl) ⟨2376035, by rfl⟩ : syracuseStep 3168047 = 4752071) B4752071
theorem B1267559 : Blo 842353 1267559 := bstep (se 1 (by rfl) ⟨950669, by rfl⟩ : syracuseStep 1267559 = 1901339) B1901339
theorem B3201191 : Blo 842353 3201191 := bstep (se 1 (by rfl) ⟨2400893, by rfl⟩ : syracuseStep 3201191 = 4801787) B4801787
theorem B73980317 : Blo 842353 73980317 := bstep (se 3 (by rfl) ⟨13871309, by rfl⟩ : syracuseStep 73980317 = 27742619) B27742619
theorem B1268159 : Blo 842353 1268159 := bstep (se 1 (by rfl) ⟨951119, by rfl⟩ : syracuseStep 1268159 = 1902239) B1902239
theorem B8116777 : Blo 842353 8116777 := bstep (se 2 (by rfl) ⟨3043791, by rfl⟩ : syracuseStep 8116777 = 6087583) B6087583
theorem B1268315 : Blo 842353 1268315 := bstep (se 1 (by rfl) ⟨951236, by rfl⟩ : syracuseStep 1268315 = 1902473) B1902473
theorem B1268327 : Blo 842353 1268327 := bstep (se 1 (by rfl) ⟨951245, by rfl⟩ : syracuseStep 1268327 = 1902491) B1902491
theorem B842855 : Blo 842353 842855 := bstep (se 1 (by rfl) ⟨632141, by rfl⟩ : syracuseStep 842855 = 1264283) B1264283
theorem B842879 : Blo 842353 842879 := bstep (se 1 (by rfl) ⟨632159, by rfl⟩ : syracuseStep 842879 = 1264319) B1264319
theorem B843167 : Blo 842353 843167 := bstep (se 1 (by rfl) ⟨632375, by rfl⟩ : syracuseStep 843167 = 1264751) B1264751
theorem B24370631 : Blo 842353 24370631 := bstep (se 1 (by rfl) ⟨18277973, by rfl⟩ : syracuseStep 24370631 = 36555947) B36555947
theorem B843291 : Blo 842353 843291 := bstep (se 1 (by rfl) ⟨632468, by rfl⟩ : syracuseStep 843291 = 1264937) B1264937
theorem B1269359 : Blo 842353 1269359 := bstep (se 1 (by rfl) ⟨952019, by rfl⟩ : syracuseStep 1269359 = 1904039) B1904039
theorem B10805147 : Blo 842353 10805147 := bstep (se 1 (by rfl) ⟨8103860, by rfl⟩ : syracuseStep 10805147 = 16207721) B16207721
theorem B4284575 : Blo 842353 4284575 := bstep (se 1 (by rfl) ⟨3213431, by rfl⟩ : syracuseStep 4284575 = 6426863) B6426863
theorem B844015 : Blo 842353 844015 := bstep (se 1 (by rfl) ⟨633011, by rfl⟩ : syracuseStep 844015 = 1266023) B1266023
theorem B4809577 : Blo 842353 4809577 := bstep (se 2 (by rfl) ⟨1803591, by rfl⟩ : syracuseStep 4809577 = 3607183) B3607183
theorem B844767 : Blo 842353 844767 := bstep (se 1 (by rfl) ⟨633575, by rfl⟩ : syracuseStep 844767 = 1267151) B1267151
theorem B845215 : Blo 842353 845215 := bstep (se 1 (by rfl) ⟨633911, by rfl⟩ : syracuseStep 845215 = 1267823) B1267823
theorem B2844071 : Blo 842353 2844071 := bstep (se 1 (by rfl) ⟨2133053, by rfl⟩ : syracuseStep 2844071 = 4266107) B4266107
theorem B845915 : Blo 842353 845915 := bstep (se 1 (by rfl) ⟨634436, by rfl⟩ : syracuseStep 845915 = 1268873) B1268873
theorem B845927 : Blo 842353 845927 := bstep (se 1 (by rfl) ⟨634445, by rfl⟩ : syracuseStep 845927 = 1268891) B1268891
theorem B845951 : Blo 842353 845951 := bstep (se 1 (by rfl) ⟨634463, by rfl⟩ : syracuseStep 845951 = 1268927) B1268927
theorem B2844827 : Blo 842353 2844827 := bstep (se 1 (by rfl) ⟨2133620, by rfl⟩ : syracuseStep 2844827 = 4267241) B4267241
theorem B13725089 : Blo 842353 13725089 := bstep (se 2 (by rfl) ⟨5146908, by rfl⟩ : syracuseStep 13725089 = 10293817) B10293817
theorem B3042785 : Blo 842353 3042785 := bstep (se 2 (by rfl) ⟨1141044, by rfl⟩ : syracuseStep 3042785 = 2282089) B2282089
theorem B12153023 : Blo 842353 12153023 := bstep (se 1 (by rfl) ⟨9114767, by rfl⟩ : syracuseStep 12153023 = 18229535) B18229535
theorem B2847095 : Blo 842353 2847095 := bstep (se 1 (by rfl) ⟨2135321, by rfl⟩ : syracuseStep 2847095 = 4270643) B4270643
theorem B4616939 : Blo 842353 4616939 := bstep (se 1 (by rfl) ⟨3462704, by rfl⟩ : syracuseStep 4616939 = 6925409) B6925409
theorem B2847527 : Blo 842353 2847527 := bstep (se 1 (by rfl) ⟨2135645, by rfl⟩ : syracuseStep 2847527 = 4271291) B4271291
theorem B1897307 : Blo 842353 1897307 := bstep (se 1 (by rfl) ⟨1422980, by rfl⟩ : syracuseStep 1897307 = 2845961) B2845961
theorem B1897703 : Blo 842353 1897703 := bstep (se 1 (by rfl) ⟨1423277, by rfl⟩ : syracuseStep 1897703 = 2846555) B2846555
theorem B1602919 : Blo 842353 1602919 := bstep (se 1 (by rfl) ⟨1202189, by rfl⟩ : syracuseStep 1602919 = 2404379) B2404379
theorem B3208679 : Blo 842353 3208679 := bstep (se 1 (by rfl) ⟨2406509, by rfl⟩ : syracuseStep 3208679 = 4813019) B4813019
theorem B6944339 : Blo 842353 6944339 := bstep (se 1 (by rfl) ⟨5208254, by rfl⟩ : syracuseStep 6944339 = 10416509) B10416509
theorem B947839 : Blo 842353 947839 := bstep (se 1 (by rfl) ⟨710879, by rfl⟩ : syracuseStep 947839 = 1421759) B1421759
theorem B1898153 : Blo 842353 1898153 := bstep (se 2 (by rfl) ⟨711807, by rfl⟩ : syracuseStep 1898153 = 1423615) B1423615
theorem B14055241 : Blo 842353 14055241 := bstep (se 2 (by rfl) ⟨5270715, by rfl⟩ : syracuseStep 14055241 = 10541431) B10541431
theorem B3210151 : Blo 842353 3210151 := bstep (se 1 (by rfl) ⟨2407613, by rfl⟩ : syracuseStep 3210151 = 4815227) B4815227
theorem B1604681 : Blo 842353 1604681 := bstep (se 2 (by rfl) ⟨601755, by rfl⟩ : syracuseStep 1604681 = 1203511) B1203511
theorem B949567 : Blo 842353 949567 := bstep (se 1 (by rfl) ⟨712175, by rfl⟩ : syracuseStep 949567 = 1424351) B1424351
theorem B3210623 : Blo 842353 3210623 := bstep (se 1 (by rfl) ⟨2407967, by rfl⟩ : syracuseStep 3210623 = 4815935) B4815935
theorem B8225027 : Blo 842353 8225027 := bstep (se 1 (by rfl) ⟨6168770, by rfl⟩ : syracuseStep 8225027 = 12337541) B12337541
theorem B5406983 : Blo 842353 5406983 := bstep (se 1 (by rfl) ⟨4055237, by rfl⟩ : syracuseStep 5406983 = 8110475) B8110475
theorem B12976519 : Blo 842353 12976519 := bstep (se 1 (by rfl) ⟨9732389, by rfl⟩ : syracuseStep 12976519 = 19464779) B19464779
theorem B1901519 : Blo 842353 1901519 := bstep (se 1 (by rfl) ⟨1426139, by rfl⟩ : syracuseStep 1901519 = 2852279) B2852279
theorem B3605543 : Blo 842353 3605543 := bstep (se 1 (by rfl) ⟨2704157, by rfl⟩ : syracuseStep 3605543 = 5408315) B5408315
theorem B39486527 : Blo 842353 39486527 := bstep (se 1 (by rfl) ⟨29614895, by rfl⟩ : syracuseStep 39486527 = 59229791) B59229791
theorem B1901663 : Blo 842353 1901663 := bstep (se 1 (by rfl) ⟨1426247, by rfl⟩ : syracuseStep 1901663 = 2852495) B2852495
theorem B952015 : Blo 842353 952015 := bstep (se 1 (by rfl) ⟨714011, by rfl⟩ : syracuseStep 952015 = 1428023) B1428023
theorem B1902761 : Blo 842353 1902761 := bstep (se 2 (by rfl) ⟨713535, by rfl⟩ : syracuseStep 1902761 = 1427071) B1427071
theorem B1903355 : Blo 842353 1903355 := bstep (se 1 (by rfl) ⟨1427516, by rfl⟩ : syracuseStep 1903355 = 2855033) B2855033
theorem B1903463 : Blo 842353 1903463 := bstep (se 1 (by rfl) ⟨1427597, by rfl⟩ : syracuseStep 1903463 = 2855195) B2855195
theorem B1904147 : Blo 842353 1904147 := bstep (se 1 (by rfl) ⟨1428110, by rfl⟩ : syracuseStep 1904147 = 2856221) B2856221
theorem B58428985 : Blo 842353 58428985 := bstep (se 2 (by rfl) ⟨21910869, by rfl⟩ : syracuseStep 58428985 = 43821739) B43821739
theorem B116723267 : Blo 842353 116723267 := bstep (se 1 (by rfl) ⟨87542450, by rfl⟩ : syracuseStep 116723267 = 175084901) B175084901
theorem B1904219 : Blo 842353 1904219 := bstep (se 1 (by rfl) ⟨1428164, by rfl⟩ : syracuseStep 1904219 = 2856329) B2856329
theorem B8228537 : Blo 842353 8228537 := bstep (se 2 (by rfl) ⟨3085701, by rfl⟩ : syracuseStep 8228537 = 6171403) B6171403
theorem B2133823 : Blo 842353 2133823 := bstep (se 1 (by rfl) ⟨1600367, by rfl⟩ : syracuseStep 2133823 = 3200735) B3200735
theorem B2134127 : Blo 842353 2134127 := bstep (se 1 (by rfl) ⟨1600595, by rfl⟩ : syracuseStep 2134127 = 3201191) B3201191
theorem B49320211 : Blo 842353 49320211 := bstep (se 1 (by rfl) ⟨36990158, by rfl⟩ : syracuseStep 49320211 = 73980317) B73980317
theorem B2855465 : Blo 842353 2855465 := bstep (se 2 (by rfl) ⟨1070799, by rfl⟩ : syracuseStep 2855465 = 2141599) B2141599
theorem B4560137 : Blo 842353 4560137 := bstep (se 2 (by rfl) ⟨1710051, by rfl⟩ : syracuseStep 4560137 = 3420103) B3420103
theorem B2856383 : Blo 842353 2856383 := bstep (se 1 (by rfl) ⟨2142287, by rfl⟩ : syracuseStep 2856383 = 4284575) B4284575
theorem B24320807 : Blo 842353 24320807 := bstep (se 1 (by rfl) ⟨18240605, by rfl⟩ : syracuseStep 24320807 = 36481211) B36481211
theorem B5774291 : Blo 842353 5774291 := bstep (se 1 (by rfl) ⟨4330718, by rfl⟩ : syracuseStep 5774291 = 8661437) B8661437
theorem B2137225 : Blo 842353 2137225 := bstep (se 2 (by rfl) ⟨801459, by rfl⟩ : syracuseStep 2137225 = 1602919) B1602919
theorem B7216553 : Blo 842353 7216553 := bstep (se 2 (by rfl) ⟨2706207, by rfl⟩ : syracuseStep 7216553 = 5412415) B5412415
theorem B9150059 : Blo 842353 9150059 := bstep (se 1 (by rfl) ⟨6862544, by rfl⟩ : syracuseStep 9150059 = 13725089) B13725089
theorem B8102015 : Blo 842353 8102015 := bstep (se 1 (by rfl) ⟨6076511, by rfl⟩ : syracuseStep 8102015 = 12153023) B12153023
theorem B2564455 : Blo 842353 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B26026667 : Blo 842353 26026667 := bstep (se 1 (by rfl) ⟨19520000, by rfl⟩ : syracuseStep 26026667 = 39040001) B39040001
theorem B10822369 : Blo 842353 10822369 := bstep (se 2 (by rfl) ⟨4058388, by rfl⟩ : syracuseStep 10822369 = 8116777) B8116777
theorem B4269023 : Blo 842353 4269023 := bstep (se 1 (by rfl) ⟨3201767, by rfl⟩ : syracuseStep 4269023 = 6403535) B6403535
theorem B2139119 : Blo 842353 2139119 := bstep (se 1 (by rfl) ⟨1604339, by rfl⟩ : syracuseStep 2139119 = 3208679) B3208679
theorem B4629559 : Blo 842353 4629559 := bstep (se 1 (by rfl) ⟨3472169, by rfl⟩ : syracuseStep 4629559 = 6944339) B6944339
theorem B4269671 : Blo 842353 4269671 := bstep (se 1 (by rfl) ⟨3202253, by rfl⟩ : syracuseStep 4269671 = 6404507) B6404507
theorem B2566255 : Blo 842353 2566255 := bstep (se 1 (by rfl) ⟨1924691, by rfl⟩ : syracuseStep 2566255 = 3849383) B3849383
theorem B32516315 : Blo 842353 32516315 := bstep (se 1 (by rfl) ⟨24387236, by rfl⟩ : syracuseStep 32516315 = 48774473) B48774473
theorem B2140415 : Blo 842353 2140415 := bstep (se 1 (by rfl) ⟨1605311, by rfl⟩ : syracuseStep 2140415 = 3210623) B3210623
theorem B2403047 : Blo 842353 2403047 := bstep (se 1 (by rfl) ⟨1802285, by rfl⟩ : syracuseStep 2403047 = 3604571) B3604571
theorem B4337003 : Blo 842353 4337003 := bstep (se 1 (by rfl) ⟨3252752, by rfl⟩ : syracuseStep 4337003 = 6505505) B6505505
theorem B963451 : Blo 842353 963451 := bstep (se 1 (by rfl) ⟨722588, by rfl⟩ : syracuseStep 963451 = 1445177) B1445177
theorem B1520795 : Blo 842353 1520795 := bstep (se 1 (by rfl) ⟨1140596, by rfl⟩ : syracuseStep 1520795 = 2281193) B2281193
theorem B7812359 : Blo 842353 7812359 := bstep (se 1 (by rfl) ⟨5859269, by rfl⟩ : syracuseStep 7812359 = 11718539) B11718539
theorem B15382061 : Blo 842353 15382061 := bstep (se 3 (by rfl) ⟨2884136, by rfl⟩ : syracuseStep 15382061 = 5768273) B5768273
theorem B4273883 : Blo 842353 4273883 := bstep (se 1 (by rfl) ⟨3205412, by rfl⟩ : syracuseStep 4273883 = 6410825) B6410825
theorem B964327 : Blo 842353 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B2112031 : Blo 842353 2112031 := bstep (se 1 (by rfl) ⟨1584023, by rfl⟩ : syracuseStep 2112031 = 3168047) B3168047
theorem B1424155 : Blo 842353 1424155 := bstep (se 1 (by rfl) ⟨1068116, by rfl⟩ : syracuseStep 1424155 = 2136233) B2136233
theorem B1424999 : Blo 842353 1424999 := bstep (se 1 (by rfl) ⟨1068749, by rfl⟩ : syracuseStep 1424999 = 2137499) B2137499
theorem B24298663 : Blo 842353 24298663 := bstep (se 1 (by rfl) ⟨18223997, by rfl⟩ : syracuseStep 24298663 = 36447995) B36447995
theorem B902783 : Blo 842353 902783 := bstep (se 1 (by rfl) ⟨677087, by rfl⟩ : syracuseStep 902783 = 1354175) B1354175
theorem B8111825 : Blo 842353 8111825 := bstep (se 2 (by rfl) ⟨3041934, by rfl⟩ : syracuseStep 8111825 = 6083869) B6083869
theorem B3852431 : Blo 842353 3852431 := bstep (se 1 (by rfl) ⟨2889323, by rfl⟩ : syracuseStep 3852431 = 5778647) B5778647
theorem B1263785 : Blo 842353 1263785 := bstep (se 2 (by rfl) ⟨473919, by rfl⟩ : syracuseStep 1263785 = 947839) B947839
theorem B1624943 : Blo 842353 1624943 := bstep (se 1 (by rfl) ⟨1218707, by rfl⟩ : syracuseStep 1624943 = 2437415) B2437415
theorem B1264871 : Blo 842353 1264871 := bstep (se 1 (by rfl) ⟨948653, by rfl⟩ : syracuseStep 1264871 = 1897307) B1897307
theorem B13028609 : Blo 842353 13028609 := bstep (se 2 (by rfl) ⟨4885728, by rfl⟩ : syracuseStep 13028609 = 9771457) B9771457
theorem B1265135 : Blo 842353 1265135 := bstep (se 1 (by rfl) ⟨948851, by rfl⟩ : syracuseStep 1265135 = 1897703) B1897703
theorem B1265435 : Blo 842353 1265435 := bstep (se 1 (by rfl) ⟨949076, by rfl⟩ : syracuseStep 1265435 = 1898153) B1898153
theorem B4280201 : Blo 842353 4280201 := bstep (se 2 (by rfl) ⟨1605075, by rfl⟩ : syracuseStep 4280201 = 3210151) B3210151
theorem B1266089 : Blo 842353 1266089 := bstep (se 2 (by rfl) ⟨474783, by rfl⟩ : syracuseStep 1266089 = 949567) B949567
theorem B1069787 : Blo 842353 1069787 := bstep (se 1 (by rfl) ⟨802340, by rfl⟩ : syracuseStep 1069787 = 1604681) B1604681
theorem B4282307 : Blo 842353 4282307 := bstep (se 1 (by rfl) ⟨3211730, by rfl⟩ : syracuseStep 4282307 = 6423461) B6423461
theorem B1267691 : Blo 842353 1267691 := bstep (se 1 (by rfl) ⟨950768, by rfl⟩ : syracuseStep 1267691 = 1901537) B1901537
theorem B6412769 : Blo 842353 6412769 := bstep (se 2 (by rfl) ⟨2404788, by rfl⟩ : syracuseStep 6412769 = 4809577) B4809577
theorem B842367 : Blo 842353 842367 := bstep (se 1 (by rfl) ⟨631775, by rfl⟩ : syracuseStep 842367 = 1263551) B1263551
theorem B842479 : Blo 842353 842479 := bstep (se 1 (by rfl) ⟨631859, by rfl⟩ : syracuseStep 842479 = 1263719) B1263719
theorem B842735 : Blo 842353 842735 := bstep (se 1 (by rfl) ⟨632051, by rfl⟩ : syracuseStep 842735 = 1264103) B1264103
theorem B1924393 : Blo 842353 1924393 := bstep (se 2 (by rfl) ⟨721647, by rfl⟩ : syracuseStep 1924393 = 1443295) B1443295
theorem B2710847 : Blo 842353 2710847 := bstep (se 1 (by rfl) ⟨2033135, by rfl⟩ : syracuseStep 2710847 = 4066271) B4066271
theorem B843163 : Blo 842353 843163 := bstep (se 1 (by rfl) ⟨632372, by rfl⟩ : syracuseStep 843163 = 1264745) B1264745
theorem B843231 : Blo 842353 843231 := bstep (se 1 (by rfl) ⟨632423, by rfl⟩ : syracuseStep 843231 = 1264847) B1264847
theorem B1269215 : Blo 842353 1269215 := bstep (se 1 (by rfl) ⟨951911, by rfl⟩ : syracuseStep 1269215 = 1903823) B1903823
theorem B843547 : Blo 842353 843547 := bstep (se 1 (by rfl) ⟨632660, by rfl⟩ : syracuseStep 843547 = 1265321) B1265321
theorem B6414227 : Blo 842353 6414227 := bstep (se 1 (by rfl) ⟨4810670, by rfl⟩ : syracuseStep 6414227 = 9621341) B9621341
theorem B843803 : Blo 842353 843803 := bstep (se 1 (by rfl) ⟨632852, by rfl⟩ : syracuseStep 843803 = 1265705) B1265705
theorem B843823 : Blo 842353 843823 := bstep (se 1 (by rfl) ⟨632867, by rfl⟩ : syracuseStep 843823 = 1265735) B1265735
theorem B844527 : Blo 842353 844527 := bstep (se 1 (by rfl) ⟨633395, by rfl⟩ : syracuseStep 844527 = 1266791) B1266791
theorem B845039 : Blo 842353 845039 := bstep (se 1 (by rfl) ⟨633779, by rfl⟩ : syracuseStep 845039 = 1267559) B1267559
theorem B21128471 : Blo 842353 21128471 := bstep (se 1 (by rfl) ⟨15846353, by rfl⟩ : syracuseStep 21128471 = 31692707) B31692707
theorem B845439 : Blo 842353 845439 := bstep (se 1 (by rfl) ⟨634079, by rfl⟩ : syracuseStep 845439 = 1268159) B1268159
theorem B845543 : Blo 842353 845543 := bstep (se 1 (by rfl) ⟨634157, by rfl⟩ : syracuseStep 845543 = 1268315) B1268315
theorem B845551 : Blo 842353 845551 := bstep (se 1 (by rfl) ⟨634163, by rfl⟩ : syracuseStep 845551 = 1268327) B1268327
theorem B16247087 : Blo 842353 16247087 := bstep (se 1 (by rfl) ⟨12185315, by rfl⟩ : syracuseStep 16247087 = 24370631) B24370631
theorem B846239 : Blo 842353 846239 := bstep (se 1 (by rfl) ⟨634679, by rfl⟩ : syracuseStep 846239 = 1269359) B1269359
theorem B7203431 : Blo 842353 7203431 := bstep (se 1 (by rfl) ⟨5402573, by rfl⟩ : syracuseStep 7203431 = 10805147) B10805147
theorem B8547227 : Blo 842353 8547227 := bstep (se 1 (by rfl) ⟨6410420, by rfl⟩ : syracuseStep 8547227 = 12820841) B12820841
theorem B1896047 : Blo 842353 1896047 := bstep (se 1 (by rfl) ⟨1422035, by rfl⟩ : syracuseStep 1896047 = 2844071) B2844071
theorem B1896551 : Blo 842353 1896551 := bstep (se 1 (by rfl) ⟨1422413, by rfl⟩ : syracuseStep 1896551 = 2844827) B2844827
theorem B7696721 : Blo 842353 7696721 := bstep (se 2 (by rfl) ⟨2886270, by rfl⟩ : syracuseStep 7696721 = 5772541) B5772541
theorem B2028523 : Blo 842353 2028523 := bstep (se 1 (by rfl) ⟨1521392, by rfl⟩ : syracuseStep 2028523 = 3042785) B3042785
theorem B18740321 : Blo 842353 18740321 := bstep (se 2 (by rfl) ⟨7027620, by rfl⟩ : syracuseStep 18740321 = 14055241) B14055241
theorem B1602767 : Blo 842353 1602767 := bstep (se 1 (by rfl) ⟨1202075, by rfl⟩ : syracuseStep 1602767 = 2404151) B2404151
theorem B1898063 : Blo 842353 1898063 := bstep (se 1 (by rfl) ⟨1423547, by rfl⟩ : syracuseStep 1898063 = 2847095) B2847095
theorem B3077959 : Blo 842353 3077959 := bstep (se 1 (by rfl) ⟨2308469, by rfl⟩ : syracuseStep 3077959 = 4616939) B4616939
theorem B1898351 : Blo 842353 1898351 := bstep (se 1 (by rfl) ⟨1423763, by rfl⟩ : syracuseStep 1898351 = 2847527) B2847527
theorem B1899305 : Blo 842353 1899305 := bstep (se 2 (by rfl) ⟨712239, by rfl⟩ : syracuseStep 1899305 = 1424479) B1424479
theorem B1801063 : Blo 842353 1801063 := bstep (se 1 (by rfl) ⟨1350797, by rfl⟩ : syracuseStep 1801063 = 2701595) B2701595
theorem B1605167 : Blo 842353 1605167 := bstep (se 1 (by rfl) ⟨1203875, by rfl⟩ : syracuseStep 1605167 = 2407751) B2407751
theorem B12353207 : Blo 842353 12353207 := bstep (se 1 (by rfl) ⟨9264905, by rfl⟩ : syracuseStep 12353207 = 18529811) B18529811
theorem B1900385 : Blo 842353 1900385 := bstep (se 2 (by rfl) ⟨712644, by rfl⟩ : syracuseStep 1900385 = 1425289) B1425289
theorem B3604655 : Blo 842353 3604655 := bstep (se 1 (by rfl) ⟨2703491, by rfl⟩ : syracuseStep 3604655 = 5406983) B5406983
theorem B17302025 : Blo 842353 17302025 := bstep (se 2 (by rfl) ⟨6488259, by rfl⟩ : syracuseStep 17302025 = 12976519) B12976519
theorem B5407883 : Blo 842353 5407883 := bstep (se 1 (by rfl) ⟨4055912, by rfl⟩ : syracuseStep 5407883 = 8111825) B8111825
theorem B2852765 : Blo 842353 2852765 := bstep (se 3 (by rfl) ⟨534893, by rfl⟩ : syracuseStep 2852765 = 1069787) B1069787
theorem B1083295 : Blo 842353 1083295 := bstep (se 1 (by rfl) ⟨812471, by rfl⟩ : syracuseStep 1083295 = 1624943) B1624943
theorem B8685739 : Blo 842353 8685739 := bstep (se 1 (by rfl) ⟨6514304, by rfl⟩ : syracuseStep 8685739 = 13028609) B13028609
theorem B2853467 : Blo 842353 2853467 := bstep (se 1 (by rfl) ⟨2140100, by rfl⟩ : syracuseStep 2853467 = 4280201) B4280201
theorem B1903643 : Blo 842353 1903643 := bstep (se 1 (by rfl) ⟨1427732, by rfl⟩ : syracuseStep 1903643 = 2855465) B2855465
theorem B1904255 : Blo 842353 1904255 := bstep (se 1 (by rfl) ⟨1428191, by rfl⟩ : syracuseStep 1904255 = 2856383) B2856383
theorem B2854871 : Blo 842353 2854871 := bstep (se 1 (by rfl) ⟨2141153, by rfl⟩ : syracuseStep 2854871 = 4282307) B4282307
theorem B6100039 : Blo 842353 6100039 := bstep (se 1 (by rfl) ⟨4575029, by rfl⟩ : syracuseStep 6100039 = 9150059) B9150059
theorem B1284601 : Blo 842353 1284601 := bstep (se 2 (by rfl) ⟨481725, by rfl⟩ : syracuseStep 1284601 = 963451) B963451
theorem B2891335 : Blo 842353 2891335 := bstep (se 1 (by rfl) ⟨2168501, by rfl⟩ : syracuseStep 2891335 = 4337003) B4337003
theorem B1285769 : Blo 842353 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B4103945 : Blo 842353 4103945 := bstep (se 2 (by rfl) ⟨1538979, by rfl⟩ : syracuseStep 4103945 = 3077959) B3077959
theorem B12493547 : Blo 842353 12493547 := bstep (se 1 (by rfl) ⟨9370160, by rfl⟩ : syracuseStep 12493547 = 18740321) B18740321
theorem B2401417 : Blo 842353 2401417 := bstep (se 2 (by rfl) ⟨900531, by rfl⟩ : syracuseStep 2401417 = 1801063) B1801063
theorem B2565857 : Blo 842353 2565857 := bstep (se 2 (by rfl) ⟨962196, by rfl⟩ : syracuseStep 2565857 = 1924393) B1924393
theorem B32941885 : Blo 842353 32941885 := bstep (se 3 (by rfl) ⟨6176603, by rfl⟩ : syracuseStep 32941885 = 12353207) B12353207
theorem B5483351 : Blo 842353 5483351 := bstep (se 1 (by rfl) ⟨4112513, by rfl⟩ : syracuseStep 5483351 = 8225027) B8225027
theorem B3419273 : Blo 842353 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B2403695 : Blo 842353 2403695 := bstep (se 1 (by rfl) ⟨1802771, by rfl⟩ : syracuseStep 2403695 = 3605543) B3605543
theorem B26324351 : Blo 842353 26324351 := bstep (se 1 (by rfl) ⟨19743263, by rfl⟩ : syracuseStep 26324351 = 39486527) B39486527
theorem B14429825 : Blo 842353 14429825 := bstep (se 2 (by rfl) ⟨5411184, by rfl⟩ : syracuseStep 14429825 = 10822369) B10822369
theorem B6172745 : Blo 842353 6172745 := bstep (se 2 (by rfl) ⟨2314779, by rfl⟩ : syracuseStep 6172745 = 4629559) B4629559
theorem B2568287 : Blo 842353 2568287 := bstep (se 1 (by rfl) ⟨1926215, by rfl⟩ : syracuseStep 2568287 = 3852431) B3852431
theorem B5485691 : Blo 842353 5485691 := bstep (se 1 (by rfl) ⟨4114268, by rfl⟩ : syracuseStep 5485691 = 8228537) B8228537
theorem B1422751 : Blo 842353 1422751 := bstep (se 1 (by rfl) ⟨1067063, by rfl⟩ : syracuseStep 1422751 = 2134127) B2134127
theorem B3421673 : Blo 842353 3421673 := bstep (se 2 (by rfl) ⟨1283127, by rfl⟩ : syracuseStep 3421673 = 2566255) B2566255
theorem B4274045 : Blo 842353 4274045 := bstep (se 3 (by rfl) ⟨801383, by rfl⟩ : syracuseStep 4274045 = 1602767) B1602767
theorem B4275179 : Blo 842353 4275179 := bstep (se 1 (by rfl) ⟨3206384, by rfl⟩ : syracuseStep 4275179 = 6412769) B6412769
theorem B2407421 : Blo 842353 2407421 := bstep (se 3 (by rfl) ⟨451391, by rfl⟩ : syracuseStep 2407421 = 902783) B902783
theorem B3849527 : Blo 842353 3849527 := bstep (se 1 (by rfl) ⟨2887145, by rfl⟩ : syracuseStep 3849527 = 5774291) B5774291
theorem B77905313 : Blo 842353 77905313 := bstep (se 2 (by rfl) ⟨29214492, by rfl⟩ : syracuseStep 77905313 = 58428985) B58428985
theorem B4276151 : Blo 842353 4276151 := bstep (se 1 (by rfl) ⟨3207113, by rfl⟩ : syracuseStep 4276151 = 6414227) B6414227
theorem B17351111 : Blo 842353 17351111 := bstep (se 1 (by rfl) ⟨13013333, by rfl⟩ : syracuseStep 17351111 = 26026667) B26026667
theorem B1426079 : Blo 842353 1426079 := bstep (se 1 (by rfl) ⟨1069559, by rfl⟩ : syracuseStep 1426079 = 2139119) B2139119
theorem B2704697 : Blo 842353 2704697 := bstep (se 2 (by rfl) ⟨1014261, by rfl⟩ : syracuseStep 2704697 = 2028523) B2028523
theorem B21677543 : Blo 842353 21677543 := bstep (se 1 (by rfl) ⟨16258157, by rfl⟩ : syracuseStep 21677543 = 32516315) B32516315
theorem B1426943 : Blo 842353 1426943 := bstep (se 1 (by rfl) ⟨1070207, by rfl⟩ : syracuseStep 1426943 = 2140415) B2140415
theorem B10831391 : Blo 842353 10831391 := bstep (se 1 (by rfl) ⟨8123543, by rfl⟩ : syracuseStep 10831391 = 16247087) B16247087
theorem B4802287 : Blo 842353 4802287 := bstep (se 1 (by rfl) ⟨3601715, by rfl⟩ : syracuseStep 4802287 = 7203431) B7203431
theorem B1264031 : Blo 842353 1264031 := bstep (se 1 (by rfl) ⟨948023, by rfl⟩ : syracuseStep 1264031 = 1896047) B1896047
theorem B1264367 : Blo 842353 1264367 := bstep (se 1 (by rfl) ⟨948275, by rfl⟩ : syracuseStep 1264367 = 1896551) B1896551
theorem B5131147 : Blo 842353 5131147 := bstep (se 1 (by rfl) ⟨3848360, by rfl⟩ : syracuseStep 5131147 = 7696721) B7696721
theorem B7228925 : Blo 842353 7228925 := bstep (se 3 (by rfl) ⟨1355423, by rfl⟩ : syracuseStep 7228925 = 2710847) B2710847
theorem B1265375 : Blo 842353 1265375 := bstep (se 1 (by rfl) ⟨949031, by rfl⟩ : syracuseStep 1265375 = 1898063) B1898063
theorem B1265567 : Blo 842353 1265567 := bstep (se 1 (by rfl) ⟨949175, by rfl⟩ : syracuseStep 1265567 = 1898351) B1898351
theorem B1266203 : Blo 842353 1266203 := bstep (se 1 (by rfl) ⟨949652, by rfl⟩ : syracuseStep 1266203 = 1899305) B1899305
theorem B1070111 : Blo 842353 1070111 := bstep (se 1 (by rfl) ⟨802583, by rfl⟩ : syracuseStep 1070111 = 1605167) B1605167
theorem B1266923 : Blo 842353 1266923 := bstep (se 1 (by rfl) ⟨950192, by rfl⟩ : syracuseStep 1266923 = 1900385) B1900385
theorem B1267679 : Blo 842353 1267679 := bstep (se 1 (by rfl) ⟨950759, by rfl⟩ : syracuseStep 1267679 = 1901519) B1901519
theorem B1267775 : Blo 842353 1267775 := bstep (se 1 (by rfl) ⟨950831, by rfl⟩ : syracuseStep 1267775 = 1901663) B1901663
theorem B842523 : Blo 842353 842523 := bstep (se 1 (by rfl) ⟨631892, by rfl⟩ : syracuseStep 842523 = 1263785) B1263785
theorem B1268507 : Blo 842353 1268507 := bstep (se 1 (by rfl) ⟨951380, by rfl⟩ : syracuseStep 1268507 = 1902761) B1902761
theorem B32398217 : Blo 842353 32398217 := bstep (se 2 (by rfl) ⟨12149331, by rfl⟩ : syracuseStep 32398217 = 24298663) B24298663
theorem B1268903 : Blo 842353 1268903 := bstep (se 1 (by rfl) ⟨951677, by rfl⟩ : syracuseStep 1268903 = 1903355) B1903355
theorem B1268975 : Blo 842353 1268975 := bstep (se 1 (by rfl) ⟨951731, by rfl⟩ : syracuseStep 1268975 = 1903463) B1903463
theorem B843247 : Blo 842353 843247 := bstep (se 1 (by rfl) ⟨632435, by rfl⟩ : syracuseStep 843247 = 1264871) B1264871
theorem B1269353 : Blo 842353 1269353 := bstep (se 2 (by rfl) ⟨476007, by rfl⟩ : syracuseStep 1269353 = 952015) B952015
theorem B843423 : Blo 842353 843423 := bstep (se 1 (by rfl) ⟨632567, by rfl⟩ : syracuseStep 843423 = 1265135) B1265135
theorem B1269431 : Blo 842353 1269431 := bstep (se 1 (by rfl) ⟨952073, by rfl⟩ : syracuseStep 1269431 = 1904147) B1904147
theorem B77815511 : Blo 842353 77815511 := bstep (se 1 (by rfl) ⟨58361633, by rfl⟩ : syracuseStep 77815511 = 116723267) B116723267
theorem B1269479 : Blo 842353 1269479 := bstep (se 1 (by rfl) ⟨952109, by rfl⟩ : syracuseStep 1269479 = 1904219) B1904219
theorem B843623 : Blo 842353 843623 := bstep (se 1 (by rfl) ⟨632717, by rfl⟩ : syracuseStep 843623 = 1265435) B1265435
theorem B844059 : Blo 842353 844059 := bstep (se 1 (by rfl) ⟨633044, by rfl⟩ : syracuseStep 844059 = 1266089) B1266089
theorem B3040091 : Blo 842353 3040091 := bstep (se 1 (by rfl) ⟨2280068, by rfl⟩ : syracuseStep 3040091 = 4560137) B4560137
theorem B845127 : Blo 842353 845127 := bstep (se 1 (by rfl) ⟨633845, by rfl⟩ : syracuseStep 845127 = 1267691) B1267691
theorem B16213871 : Blo 842353 16213871 := bstep (se 1 (by rfl) ⟨12160403, by rfl⟩ : syracuseStep 16213871 = 24320807) B24320807
theorem B4811035 : Blo 842353 4811035 := bstep (se 1 (by rfl) ⟨3608276, by rfl⟩ : syracuseStep 4811035 = 7216553) B7216553
theorem B846143 : Blo 842353 846143 := bstep (se 1 (by rfl) ⟨634607, by rfl⟩ : syracuseStep 846143 = 1269215) B1269215
theorem B2845097 : Blo 842353 2845097 := bstep (se 2 (by rfl) ⟨1066911, by rfl⟩ : syracuseStep 2845097 = 2133823) B2133823
theorem B5401343 : Blo 842353 5401343 := bstep (se 1 (by rfl) ⟨4051007, by rfl⟩ : syracuseStep 5401343 = 8102015) B8102015
theorem B65760281 : Blo 842353 65760281 := bstep (se 2 (by rfl) ⟨24660105, by rfl⟩ : syracuseStep 65760281 = 49320211) B49320211
theorem B2846015 : Blo 842353 2846015 := bstep (se 1 (by rfl) ⟨2134511, by rfl⟩ : syracuseStep 2846015 = 4269023) B4269023
theorem B14085647 : Blo 842353 14085647 := bstep (se 1 (by rfl) ⟨10564235, by rfl⟩ : syracuseStep 14085647 = 21128471) B21128471
theorem B2846447 : Blo 842353 2846447 := bstep (se 1 (by rfl) ⟨2134835, by rfl⟩ : syracuseStep 2846447 = 4269671) B4269671
theorem B1602031 : Blo 842353 1602031 := bstep (se 1 (by rfl) ⟨1201523, by rfl⟩ : syracuseStep 1602031 = 2403047) B2403047
theorem B5698151 : Blo 842353 5698151 := bstep (se 1 (by rfl) ⟨4273613, by rfl⟩ : syracuseStep 5698151 = 8547227) B8547227
theorem B2816041 : Blo 842353 2816041 := bstep (se 2 (by rfl) ⟨1056015, by rfl⟩ : syracuseStep 2816041 = 2112031) B2112031
theorem B1013863 : Blo 842353 1013863 := bstep (se 1 (by rfl) ⟨760397, by rfl⟩ : syracuseStep 1013863 = 1520795) B1520795
theorem B5208239 : Blo 842353 5208239 := bstep (se 1 (by rfl) ⟨3906179, by rfl⟩ : syracuseStep 5208239 = 7812359) B7812359
theorem B10254707 : Blo 842353 10254707 := bstep (se 1 (by rfl) ⟨7691030, by rfl⟩ : syracuseStep 10254707 = 15382061) B15382061
theorem B1898873 : Blo 842353 1898873 := bstep (se 2 (by rfl) ⟨712077, by rfl⟩ : syracuseStep 1898873 = 1424155) B1424155
theorem B2849255 : Blo 842353 2849255 := bstep (se 1 (by rfl) ⟨2136941, by rfl⟩ : syracuseStep 2849255 = 4273883) B4273883
theorem B2849633 : Blo 842353 2849633 := bstep (se 2 (by rfl) ⟨1068612, by rfl⟩ : syracuseStep 2849633 = 2137225) B2137225
theorem B949999 : Blo 842353 949999 := bstep (se 1 (by rfl) ⟨712499, by rfl⟩ : syracuseStep 949999 = 1424999) B1424999
theorem B11534683 : Blo 842353 11534683 := bstep (se 1 (by rfl) ⟨8651012, by rfl⟩ : syracuseStep 11534683 = 17302025) B17302025
theorem B950719 : Blo 842353 950719 := bstep (se 1 (by rfl) ⟨713039, by rfl⟩ : syracuseStep 950719 = 1426079) B1426079
theorem B3605255 : Blo 842353 3605255 := bstep (se 1 (by rfl) ⟨2703941, by rfl⟩ : syracuseStep 3605255 = 5407883) B5407883
theorem B1803131 : Blo 842353 1803131 := bstep (se 1 (by rfl) ⟨1352348, by rfl⟩ : syracuseStep 1803131 = 2704697) B2704697
theorem B14451695 : Blo 842353 14451695 := bstep (se 1 (by rfl) ⟨10838771, by rfl⟩ : syracuseStep 14451695 = 21677543) B21677543
theorem B951295 : Blo 842353 951295 := bstep (se 1 (by rfl) ⟨713471, by rfl⟩ : syracuseStep 951295 = 1426943) B1426943
theorem B46269629 : Blo 842353 46269629 := bstep (se 3 (by rfl) ⟨8675555, by rfl⟩ : syracuseStep 46269629 = 17351111) B17351111
theorem B1901843 : Blo 842353 1901843 := bstep (se 1 (by rfl) ⟨1426382, by rfl⟩ : syracuseStep 1901843 = 2852765) B2852765
theorem B1902311 : Blo 842353 1902311 := bstep (se 1 (by rfl) ⟨1426733, by rfl⟩ : syracuseStep 1902311 = 2853467) B2853467
theorem B4819283 : Blo 842353 4819283 := bstep (se 1 (by rfl) ⟨3614462, by rfl⟩ : syracuseStep 4819283 = 7228925) B7228925
theorem B1903247 : Blo 842353 1903247 := bstep (se 1 (by rfl) ⟨1427435, by rfl⟩ : syracuseStep 1903247 = 2854871) B2854871
theorem B2853629 : Blo 842353 2853629 := bstep (se 3 (by rfl) ⟨535055, by rfl⟩ : syracuseStep 2853629 = 1070111) B1070111
theorem B21598811 : Blo 842353 21598811 := bstep (se 1 (by rfl) ⟨16199108, by rfl⟩ : syracuseStep 21598811 = 32398217) B32398217
theorem B857179 : Blo 842353 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B51877007 : Blo 842353 51877007 := bstep (se 1 (by rfl) ⟨38907755, by rfl⟩ : syracuseStep 51877007 = 77815511) B77815511
theorem B8329031 : Blo 842353 8329031 := bstep (se 1 (by rfl) ⟨6246773, by rfl⟩ : syracuseStep 8329031 = 12493547) B12493547
theorem B2136041 : Blo 842353 2136041 := bstep (se 2 (by rfl) ⟨801015, by rfl⟩ : syracuseStep 2136041 = 1602031) B1602031
theorem B1710571 : Blo 842353 1710571 := bstep (se 1 (by rfl) ⟨1282928, by rfl⟩ : syracuseStep 1710571 = 2565857) B2565857
theorem B8133385 : Blo 842353 8133385 := bstep (se 2 (by rfl) ⟨3050019, by rfl⟩ : syracuseStep 8133385 = 6100039) B6100039
theorem B1712191 : Blo 842353 1712191 := bstep (se 1 (by rfl) ⟨1284143, by rfl⟩ : syracuseStep 1712191 = 2568287) B2568287
theorem B1351817 : Blo 842353 1351817 := bstep (se 2 (by rfl) ⟨506931, by rfl⟩ : syracuseStep 1351817 = 1013863) B1013863
theorem B1712801 : Blo 842353 1712801 := bstep (se 2 (by rfl) ⟨642300, by rfl⟩ : syracuseStep 1712801 = 1284601) B1284601
theorem B5777573 : Blo 842353 5777573 := bstep (se 4 (by rfl) ⟨541647, by rfl⟩ : syracuseStep 5777573 = 1083295) B1083295
theorem B2566351 : Blo 842353 2566351 := bstep (se 1 (by rfl) ⟨1924763, by rfl⟩ : syracuseStep 2566351 = 3849527) B3849527
theorem B2403103 : Blo 842353 2403103 := bstep (se 1 (by rfl) ⟨1802327, by rfl⟩ : syracuseStep 2403103 = 3604655) B3604655
theorem B16460653 : Blo 842353 16460653 := bstep (se 3 (by rfl) ⟨3086372, by rfl⟩ : syracuseStep 16460653 = 6172745) B6172745
theorem B7220927 : Blo 842353 7220927 := bstep (se 1 (by rfl) ⟨5415695, by rfl⟩ : syracuseStep 7220927 = 10831391) B10831391
theorem B6403049 : Blo 842353 6403049 := bstep (se 2 (by rfl) ⟨2401143, by rfl⟩ : syracuseStep 6403049 = 4802287) B4802287
theorem B43922513 : Blo 842353 43922513 := bstep (se 2 (by rfl) ⟨16470942, by rfl⟩ : syracuseStep 43922513 = 32941885) B32941885
theorem B11580985 : Blo 842353 11580985 := bstep (se 2 (by rfl) ⟨4342869, by rfl⟩ : syracuseStep 11580985 = 8685739) B8685739
theorem B14628509 : Blo 842353 14628509 := bstep (se 3 (by rfl) ⟨2742845, by rfl⟩ : syracuseStep 14628509 = 5485691) B5485691
theorem B2735963 : Blo 842353 2735963 := bstep (se 1 (by rfl) ⟨2051972, by rfl⟩ : syracuseStep 2735963 = 4103945) B4103945
theorem B3655567 : Blo 842353 3655567 := bstep (se 1 (by rfl) ⟨2741675, by rfl⟩ : syracuseStep 3655567 = 5483351) B5483351
theorem B14403581 : Blo 842353 14403581 := bstep (se 3 (by rfl) ⟨2700671, by rfl⟩ : syracuseStep 14403581 = 5401343) B5401343
theorem B2279515 : Blo 842353 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B17549567 : Blo 842353 17549567 := bstep (se 1 (by rfl) ⟨13162175, by rfl⟩ : syracuseStep 17549567 = 26324351) B26324351
theorem B9390431 : Blo 842353 9390431 := bstep (se 1 (by rfl) ⟨7042823, by rfl⟩ : syracuseStep 9390431 = 14085647) B14085647
theorem B9619883 : Blo 842353 9619883 := bstep (se 1 (by rfl) ⟨7214912, by rfl⟩ : syracuseStep 9619883 = 14429825) B14429825
theorem B3754721 : Blo 842353 3754721 := bstep (se 2 (by rfl) ⟨1408020, by rfl⟩ : syracuseStep 3754721 = 2816041) B2816041
theorem B6409853 : Blo 842353 6409853 := bstep (se 3 (by rfl) ⟨1201847, by rfl⟩ : syracuseStep 6409853 = 2403695) B2403695
theorem B2281115 : Blo 842353 2281115 := bstep (se 1 (by rfl) ⟨1710836, by rfl⟩ : syracuseStep 2281115 = 3421673) B3421673
theorem B6836471 : Blo 842353 6836471 := bstep (se 1 (by rfl) ⟨5127353, by rfl⟩ : syracuseStep 6836471 = 10254707) B10254707
theorem B1265915 : Blo 842353 1265915 := bstep (se 1 (by rfl) ⟨949436, by rfl⟩ : syracuseStep 1265915 = 1898873) B1898873
theorem B3855113 : Blo 842353 3855113 := bstep (se 2 (by rfl) ⟨1445667, by rfl⟩ : syracuseStep 3855113 = 2891335) B2891335
theorem B1266665 : Blo 842353 1266665 := bstep (se 2 (by rfl) ⟨474999, by rfl⟩ : syracuseStep 1266665 = 949999) B949999
theorem B3201889 : Blo 842353 3201889 := bstep (se 2 (by rfl) ⟨1200708, by rfl⟩ : syracuseStep 3201889 = 2401417) B2401417
theorem B842687 : Blo 842353 842687 := bstep (se 1 (by rfl) ⟨632015, by rfl⟩ : syracuseStep 842687 = 1264031) B1264031
theorem B842911 : Blo 842353 842911 := bstep (se 1 (by rfl) ⟨632183, by rfl⟩ : syracuseStep 842911 = 1264367) B1264367
theorem B1269095 : Blo 842353 1269095 := bstep (se 1 (by rfl) ⟨951821, by rfl⟩ : syracuseStep 1269095 = 1903643) B1903643
theorem B1269503 : Blo 842353 1269503 := bstep (se 1 (by rfl) ⟨952127, by rfl⟩ : syracuseStep 1269503 = 1904255) B1904255
theorem B843583 : Blo 842353 843583 := bstep (se 1 (by rfl) ⟨632687, by rfl⟩ : syracuseStep 843583 = 1265375) B1265375
theorem B843711 : Blo 842353 843711 := bstep (se 1 (by rfl) ⟨632783, by rfl⟩ : syracuseStep 843711 = 1265567) B1265567
theorem B844135 : Blo 842353 844135 := bstep (se 1 (by rfl) ⟨633101, by rfl⟩ : syracuseStep 844135 = 1266203) B1266203
theorem B6414713 : Blo 842353 6414713 := bstep (se 2 (by rfl) ⟨2405517, by rfl⟩ : syracuseStep 6414713 = 4811035) B4811035
theorem B844615 : Blo 842353 844615 := bstep (se 1 (by rfl) ⟨633461, by rfl⟩ : syracuseStep 844615 = 1266923) B1266923
theorem B6841529 : Blo 842353 6841529 := bstep (se 2 (by rfl) ⟨2565573, by rfl⟩ : syracuseStep 6841529 = 5131147) B5131147
theorem B845119 : Blo 842353 845119 := bstep (se 1 (by rfl) ⟨633839, by rfl⟩ : syracuseStep 845119 = 1267679) B1267679
theorem B845183 : Blo 842353 845183 := bstep (se 1 (by rfl) ⟨633887, by rfl⟩ : syracuseStep 845183 = 1267775) B1267775
theorem B845671 : Blo 842353 845671 := bstep (se 1 (by rfl) ⟨634253, by rfl⟩ : syracuseStep 845671 = 1268507) B1268507
theorem B845935 : Blo 842353 845935 := bstep (se 1 (by rfl) ⟨634451, by rfl⟩ : syracuseStep 845935 = 1268903) B1268903
theorem B845983 : Blo 842353 845983 := bstep (se 1 (by rfl) ⟨634487, by rfl⟩ : syracuseStep 845983 = 1268975) B1268975
theorem B846235 : Blo 842353 846235 := bstep (se 1 (by rfl) ⟨634676, by rfl⟩ : syracuseStep 846235 = 1269353) B1269353
theorem B846287 : Blo 842353 846287 := bstep (se 1 (by rfl) ⟨634715, by rfl⟩ : syracuseStep 846287 = 1269431) B1269431
theorem B846319 : Blo 842353 846319 := bstep (se 1 (by rfl) ⟨634739, by rfl⟩ : syracuseStep 846319 = 1269479) B1269479
theorem B2026727 : Blo 842353 2026727 := bstep (se 1 (by rfl) ⟨1520045, by rfl⟩ : syracuseStep 2026727 = 3040091) B3040091
theorem B10809247 : Blo 842353 10809247 := bstep (se 1 (by rfl) ⟨8106935, by rfl⟩ : syracuseStep 10809247 = 16213871) B16213871
theorem B1896731 : Blo 842353 1896731 := bstep (se 1 (by rfl) ⟨1422548, by rfl⟩ : syracuseStep 1896731 = 2845097) B2845097
theorem B1897001 : Blo 842353 1897001 := bstep (se 2 (by rfl) ⟨711375, by rfl⟩ : syracuseStep 1897001 = 1422751) B1422751
theorem B43840187 : Blo 842353 43840187 := bstep (se 1 (by rfl) ⟨32880140, by rfl⟩ : syracuseStep 43840187 = 65760281) B65760281
theorem B1897343 : Blo 842353 1897343 := bstep (se 1 (by rfl) ⟨1423007, by rfl⟩ : syracuseStep 1897343 = 2846015) B2846015
theorem B1897631 : Blo 842353 1897631 := bstep (se 1 (by rfl) ⟨1423223, by rfl⟩ : syracuseStep 1897631 = 2846447) B2846447
theorem B3798767 : Blo 842353 3798767 := bstep (se 1 (by rfl) ⟨2849075, by rfl⟩ : syracuseStep 3798767 = 5698151) B5698151
theorem B2849363 : Blo 842353 2849363 := bstep (se 1 (by rfl) ⟨2137022, by rfl⟩ : syracuseStep 2849363 = 4274045) B4274045
theorem B3472159 : Blo 842353 3472159 := bstep (se 1 (by rfl) ⟨2604119, by rfl⟩ : syracuseStep 3472159 = 5208239) B5208239
theorem B1899503 : Blo 842353 1899503 := bstep (se 1 (by rfl) ⟨1424627, by rfl⟩ : syracuseStep 1899503 = 2849255) B2849255
theorem B1899755 : Blo 842353 1899755 := bstep (se 1 (by rfl) ⟨1424816, by rfl⟩ : syracuseStep 1899755 = 2849633) B2849633
theorem B2850119 : Blo 842353 2850119 := bstep (se 1 (by rfl) ⟨2137589, by rfl⟩ : syracuseStep 2850119 = 4275179) B4275179
theorem B1604947 : Blo 842353 1604947 := bstep (se 1 (by rfl) ⟨1203710, by rfl⟩ : syracuseStep 1604947 = 2407421) B2407421
theorem B51936875 : Blo 842353 51936875 := bstep (se 1 (by rfl) ⟨38952656, by rfl⟩ : syracuseStep 51936875 = 77905313) B77905313
theorem B2850767 : Blo 842353 2850767 := bstep (se 1 (by rfl) ⟨2138075, by rfl⟩ : syracuseStep 2850767 = 4276151) B4276151
theorem B9634463 : Blo 842353 9634463 := bstep (se 1 (by rfl) ⟨7225847, by rfl⟩ : syracuseStep 9634463 = 14451695) B14451695
theorem B9602387 : Blo 842353 9602387 := bstep (se 1 (by rfl) ⟨7201790, by rfl⟩ : syracuseStep 9602387 = 14403581) B14403581
theorem B11699711 : Blo 842353 11699711 := bstep (se 1 (by rfl) ⟨8774783, by rfl⟩ : syracuseStep 11699711 = 17549567) B17549567
theorem B3212855 : Blo 842353 3212855 := bstep (se 1 (by rfl) ⟨2409641, by rfl⟩ : syracuseStep 3212855 = 4819283) B4819283
theorem B6260287 : Blo 842353 6260287 := bstep (se 1 (by rfl) ⟨4695215, by rfl⟩ : syracuseStep 6260287 = 9390431) B9390431
theorem B1902419 : Blo 842353 1902419 := bstep (se 1 (by rfl) ⟨1426814, by rfl⟩ : syracuseStep 1902419 = 2853629) B2853629
theorem B4557647 : Blo 842353 4557647 := bstep (se 1 (by rfl) ⟨3418235, by rfl⟩ : syracuseStep 4557647 = 6836471) B6836471
theorem B15406861 : Blo 842353 15406861 := bstep (se 3 (by rfl) ⟨2888786, by rfl⟩ : syracuseStep 15406861 = 5777573) B5777573
theorem B4561019 : Blo 842353 4561019 := bstep (se 1 (by rfl) ⟨3420764, by rfl⟩ : syracuseStep 4561019 = 6841529) B6841529
theorem B1351151 : Blo 842353 1351151 := bstep (se 1 (by rfl) ⟨1013363, by rfl⟩ : syracuseStep 1351151 = 2026727) B2026727
theorem B4268699 : Blo 842353 4268699 := bstep (se 1 (by rfl) ⟨3201524, by rfl⟩ : syracuseStep 4268699 = 6403049) B6403049
theorem B4629545 : Blo 842353 4629545 := bstep (se 2 (by rfl) ⟨1736079, by rfl⟩ : syracuseStep 4629545 = 3472159) B3472159
theorem B4269185 : Blo 842353 4269185 := bstep (se 2 (by rfl) ⟨1600944, by rfl⟩ : syracuseStep 4269185 = 3201889) B3201889
theorem B2532511 : Blo 842353 2532511 := bstep (se 1 (by rfl) ⟨1899383, by rfl⟩ : syracuseStep 2532511 = 3798767) B3798767
theorem B2139929 : Blo 842353 2139929 := bstep (se 2 (by rfl) ⟨802473, by rfl⟩ : syracuseStep 2139929 = 1604947) B1604947
theorem B15379577 : Blo 842353 15379577 := bstep (se 2 (by rfl) ⟨5767341, by rfl⟩ : syracuseStep 15379577 = 11534683) B11534683
theorem B2403503 : Blo 842353 2403503 := bstep (se 1 (by rfl) ⟨1802627, by rfl⟩ : syracuseStep 2403503 = 3605255) B3605255
theorem B30846419 : Blo 842353 30846419 := bstep (se 1 (by rfl) ⟨23134814, by rfl⟩ : syracuseStep 30846419 = 46269629) B46269629
theorem B2503147 : Blo 842353 2503147 := bstep (se 1 (by rfl) ⟨1877360, by rfl⟩ : syracuseStep 2503147 = 3754721) B3754721
theorem B4273235 : Blo 842353 4273235 := bstep (se 1 (by rfl) ⟨3204926, by rfl⟩ : syracuseStep 4273235 = 6409853) B6409853
theorem B1520743 : Blo 842353 1520743 := bstep (se 1 (by rfl) ⟨1140557, by rfl⟩ : syracuseStep 1520743 = 2281115) B2281115
theorem B3421801 : Blo 842353 3421801 := bstep (se 2 (by rfl) ⟨1283175, by rfl⟩ : syracuseStep 3421801 = 2566351) B2566351
theorem B14399207 : Blo 842353 14399207 := bstep (se 1 (by rfl) ⟨10799405, by rfl⟩ : syracuseStep 14399207 = 21598811) B21598811
theorem B2570075 : Blo 842353 2570075 := bstep (se 1 (by rfl) ⟨1927556, by rfl⟩ : syracuseStep 2570075 = 3855113) B3855113
theorem B34584671 : Blo 842353 34584671 := bstep (se 1 (by rfl) ⟨25938503, by rfl⟩ : syracuseStep 34584671 = 51877007) B51877007
theorem B5552687 : Blo 842353 5552687 := bstep (se 1 (by rfl) ⟨4164515, by rfl⟩ : syracuseStep 5552687 = 8329031) B8329031
theorem B1424027 : Blo 842353 1424027 := bstep (se 1 (by rfl) ⟨1068020, by rfl⟩ : syracuseStep 1424027 = 2136041) B2136041
theorem B901211 : Blo 842353 901211 := bstep (se 1 (by rfl) ⟨675908, by rfl⟩ : syracuseStep 901211 = 1351817) B1351817
theorem B4276475 : Blo 842353 4276475 := bstep (se 1 (by rfl) ⟨3207356, by rfl⟩ : syracuseStep 4276475 = 6414713) B6414713
theorem B1264487 : Blo 842353 1264487 := bstep (se 1 (by rfl) ⟨948365, by rfl⟩ : syracuseStep 1264487 = 1896731) B1896731
theorem B1264667 : Blo 842353 1264667 := bstep (se 1 (by rfl) ⟨948500, by rfl⟩ : syracuseStep 1264667 = 1897001) B1897001
theorem B1264895 : Blo 842353 1264895 := bstep (se 1 (by rfl) ⟨948671, by rfl⟩ : syracuseStep 1264895 = 1897343) B1897343
theorem B2280761 : Blo 842353 2280761 := bstep (se 2 (by rfl) ⟨855285, by rfl⟩ : syracuseStep 2280761 = 1710571) B1710571
theorem B29281675 : Blo 842353 29281675 := bstep (se 1 (by rfl) ⟨21961256, by rfl⟩ : syracuseStep 29281675 = 43922513) B43922513
theorem B1265087 : Blo 842353 1265087 := bstep (se 1 (by rfl) ⟨948815, by rfl⟩ : syracuseStep 1265087 = 1897631) B1897631
theorem B9752339 : Blo 842353 9752339 := bstep (se 1 (by rfl) ⟨7314254, by rfl⟩ : syracuseStep 9752339 = 14628509) B14628509
theorem B1266335 : Blo 842353 1266335 := bstep (se 1 (by rfl) ⟨949751, by rfl⟩ : syracuseStep 1266335 = 1899503) B1899503
theorem B1266503 : Blo 842353 1266503 := bstep (se 1 (by rfl) ⟨949877, by rfl⟩ : syracuseStep 1266503 = 1899755) B1899755
theorem B34624583 : Blo 842353 34624583 := bstep (se 1 (by rfl) ⟨25968437, by rfl⟩ : syracuseStep 34624583 = 51936875) B51936875
theorem B1823975 : Blo 842353 1823975 := bstep (se 1 (by rfl) ⟨1367981, by rfl⟩ : syracuseStep 1823975 = 2735963) B2735963
theorem B2282921 : Blo 842353 2282921 := bstep (se 2 (by rfl) ⟨856095, by rfl⟩ : syracuseStep 2282921 = 1712191) B1712191
theorem B1202087 : Blo 842353 1202087 := bstep (se 1 (by rfl) ⟨901565, by rfl⟩ : syracuseStep 1202087 = 1803131) B1803131
theorem B1267625 : Blo 842353 1267625 := bstep (se 2 (by rfl) ⟨475359, by rfl⟩ : syracuseStep 1267625 = 950719) B950719
theorem B1267895 : Blo 842353 1267895 := bstep (se 1 (by rfl) ⟨950921, by rfl⟩ : syracuseStep 1267895 = 1901843) B1901843
theorem B1268207 : Blo 842353 1268207 := bstep (se 1 (by rfl) ⟨951155, by rfl⟩ : syracuseStep 1268207 = 1902311) B1902311
theorem B1268393 : Blo 842353 1268393 := bstep (se 2 (by rfl) ⟨475647, by rfl⟩ : syracuseStep 1268393 = 951295) B951295
theorem B6413255 : Blo 842353 6413255 := bstep (se 1 (by rfl) ⟨4809941, by rfl⟩ : syracuseStep 6413255 = 9619883) B9619883
theorem B1268831 : Blo 842353 1268831 := bstep (se 1 (by rfl) ⟨951623, by rfl⟩ : syracuseStep 1268831 = 1903247) B1903247
theorem B4874089 : Blo 842353 4874089 := bstep (se 2 (by rfl) ⟨1827783, by rfl⟩ : syracuseStep 4874089 = 3655567) B3655567
theorem B3039353 : Blo 842353 3039353 := bstep (se 2 (by rfl) ⟨1139757, by rfl⟩ : syracuseStep 3039353 = 2279515) B2279515
theorem B843943 : Blo 842353 843943 := bstep (se 1 (by rfl) ⟨632957, by rfl⟩ : syracuseStep 843943 = 1265915) B1265915
theorem B844443 : Blo 842353 844443 := bstep (se 1 (by rfl) ⟨633332, by rfl⟩ : syracuseStep 844443 = 1266665) B1266665
theorem B3204137 : Blo 842353 3204137 := bstep (se 2 (by rfl) ⟨1201551, by rfl⟩ : syracuseStep 3204137 = 2403103) B2403103
theorem B21947537 : Blo 842353 21947537 := bstep (se 2 (by rfl) ⟨8230326, by rfl⟩ : syracuseStep 21947537 = 16460653) B16460653
theorem B846063 : Blo 842353 846063 := bstep (se 1 (by rfl) ⟨634547, by rfl⟩ : syracuseStep 846063 = 1269095) B1269095
theorem B846335 : Blo 842353 846335 := bstep (se 1 (by rfl) ⟨634751, by rfl⟩ : syracuseStep 846335 = 1269503) B1269503
theorem B14412329 : Blo 842353 14412329 := bstep (se 2 (by rfl) ⟨5404623, by rfl⟩ : syracuseStep 14412329 = 10809247) B10809247
theorem B1141867 : Blo 842353 1141867 := bstep (se 1 (by rfl) ⟨856400, by rfl⟩ : syracuseStep 1141867 = 1712801) B1712801
theorem B1142905 : Blo 842353 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B4813951 : Blo 842353 4813951 := bstep (se 1 (by rfl) ⟨3610463, by rfl⟩ : syracuseStep 4813951 = 7220927) B7220927
theorem B61765253 : Blo 842353 61765253 := bstep (se 4 (by rfl) ⟨5790492, by rfl⟩ : syracuseStep 61765253 = 11580985) B11580985
theorem B29226791 : Blo 842353 29226791 := bstep (se 1 (by rfl) ⟨21920093, by rfl⟩ : syracuseStep 29226791 = 43840187) B43840187
theorem B10844513 : Blo 842353 10844513 := bstep (se 2 (by rfl) ⟨4066692, by rfl⟩ : syracuseStep 10844513 = 8133385) B8133385
theorem B1899575 : Blo 842353 1899575 := bstep (se 1 (by rfl) ⟨1424681, by rfl⟩ : syracuseStep 1899575 = 2849363) B2849363
theorem B1900079 : Blo 842353 1900079 := bstep (se 1 (by rfl) ⟨1425059, by rfl⟩ : syracuseStep 1900079 = 2850119) B2850119
theorem B1900511 : Blo 842353 1900511 := bstep (se 1 (by rfl) ⟨1425383, by rfl⟩ : syracuseStep 1900511 = 2850767) B2850767
theorem B2850983 : Blo 842353 2850983 := bstep (se 1 (by rfl) ⟨2138237, by rfl⟩ : syracuseStep 2850983 = 4276475) B4276475
theorem B6422975 : Blo 842353 6422975 := bstep (se 1 (by rfl) ⟨4817231, by rfl⟩ : syracuseStep 6422975 = 9634463) B9634463
theorem B7799807 : Blo 842353 7799807 := bstep (se 1 (by rfl) ⟨5849855, by rfl⟩ : syracuseStep 7799807 = 11699711) B11699711
theorem B1215983 : Blo 842353 1215983 := bstep (se 1 (by rfl) ⟨911987, by rfl⟩ : syracuseStep 1215983 = 1823975) B1823975
theorem B2136091 : Blo 842353 2136091 := bstep (se 1 (by rfl) ⟨1602068, by rfl⟩ : syracuseStep 2136091 = 3204137) B3204137
theorem B3086363 : Blo 842353 3086363 := bstep (se 1 (by rfl) ⟨2314772, by rfl⟩ : syracuseStep 3086363 = 4629545) B4629545
theorem B13506725 : Blo 842353 13506725 := bstep (se 4 (by rfl) ⟨1266255, by rfl⟩ : syracuseStep 13506725 = 2532511) B2532511
theorem B9608219 : Blo 842353 9608219 := bstep (se 1 (by rfl) ⟨7206164, by rfl⟩ : syracuseStep 9608219 = 14412329) B14412329
theorem B4562401 : Blo 842353 4562401 := bstep (se 2 (by rfl) ⟨1710900, by rfl⟩ : syracuseStep 4562401 = 3421801) B3421801
theorem B1713383 : Blo 842353 1713383 := bstep (se 1 (by rfl) ⟨1285037, by rfl⟩ : syracuseStep 1713383 = 2570075) B2570075
theorem B6498785 : Blo 842353 6498785 := bstep (se 2 (by rfl) ⟨2437044, by rfl⟩ : syracuseStep 6498785 = 4874089) B4874089
theorem B2403229 : Blo 842353 2403229 := bstep (se 3 (by rfl) ⟨450605, by rfl⟩ : syracuseStep 2403229 = 901211) B901211
theorem B6401591 : Blo 842353 6401591 := bstep (se 1 (by rfl) ⟨4801193, by rfl⟩ : syracuseStep 6401591 = 9602387) B9602387
theorem B2141903 : Blo 842353 2141903 := bstep (se 1 (by rfl) ⟨1606427, by rfl⟩ : syracuseStep 2141903 = 3212855) B3212855
theorem B1520507 : Blo 842353 1520507 := bstep (se 1 (by rfl) ⟨1140380, by rfl⟩ : syracuseStep 1520507 = 2280761) B2280761
theorem B6501559 : Blo 842353 6501559 := bstep (se 1 (by rfl) ⟨4876169, by rfl⟩ : syracuseStep 6501559 = 9752339) B9752339
theorem B23083055 : Blo 842353 23083055 := bstep (se 1 (by rfl) ⟨17312291, by rfl⟩ : syracuseStep 23083055 = 34624583) B34624583
theorem B1521947 : Blo 842353 1521947 := bstep (se 1 (by rfl) ⟨1141460, by rfl⟩ : syracuseStep 1521947 = 2282921) B2282921
theorem B1522489 : Blo 842353 1522489 := bstep (se 2 (by rfl) ⟨570933, by rfl⟩ : syracuseStep 1522489 = 1141867) B1141867
theorem B39042233 : Blo 842353 39042233 := bstep (se 2 (by rfl) ⟨14640837, by rfl⟩ : syracuseStep 39042233 = 29281675) B29281675
theorem B4275503 : Blo 842353 4275503 := bstep (se 1 (by rfl) ⟨3206627, by rfl⟩ : syracuseStep 4275503 = 6413255) B6413255
theorem B77938109 : Blo 842353 77938109 := bstep (se 3 (by rfl) ⟨14613395, by rfl⟩ : syracuseStep 77938109 = 29226791) B29226791
theorem B900767 : Blo 842353 900767 := bstep (se 1 (by rfl) ⟨675575, by rfl⟩ : syracuseStep 900767 = 1351151) B1351151
theorem B1523873 : Blo 842353 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B14631691 : Blo 842353 14631691 := bstep (se 1 (by rfl) ⟨10973768, by rfl⟩ : syracuseStep 14631691 = 21947537) B21947537
theorem B1426619 : Blo 842353 1426619 := bstep (se 1 (by rfl) ⟨1069964, by rfl⟩ : syracuseStep 1426619 = 2139929) B2139929
theorem B20564279 : Blo 842353 20564279 := bstep (se 1 (by rfl) ⟨15423209, by rfl⟩ : syracuseStep 20564279 = 30846419) B30846419
theorem B41176835 : Blo 842353 41176835 := bstep (se 1 (by rfl) ⟨30882626, by rfl⟩ : syracuseStep 41176835 = 61765253) B61765253
theorem B23056447 : Blo 842353 23056447 := bstep (se 1 (by rfl) ⟨17292335, by rfl⟩ : syracuseStep 23056447 = 34584671) B34584671
theorem B7229675 : Blo 842353 7229675 := bstep (se 1 (by rfl) ⟨5422256, by rfl⟩ : syracuseStep 7229675 = 10844513) B10844513
theorem B1266383 : Blo 842353 1266383 := bstep (se 1 (by rfl) ⟨949787, by rfl⟩ : syracuseStep 1266383 = 1899575) B1899575
theorem B1266719 : Blo 842353 1266719 := bstep (se 1 (by rfl) ⟨950039, by rfl⟩ : syracuseStep 1266719 = 1900079) B1900079
theorem B1267007 : Blo 842353 1267007 := bstep (se 1 (by rfl) ⟨950255, by rfl⟩ : syracuseStep 1267007 = 1900511) B1900511
theorem B1268279 : Blo 842353 1268279 := bstep (se 1 (by rfl) ⟨951209, by rfl⟩ : syracuseStep 1268279 = 1902419) B1902419
theorem B3038431 : Blo 842353 3038431 := bstep (se 1 (by rfl) ⟨2278823, by rfl⟩ : syracuseStep 3038431 = 4557647) B4557647
theorem B842991 : Blo 842353 842991 := bstep (se 1 (by rfl) ⟨632243, by rfl⟩ : syracuseStep 842991 = 1264487) B1264487
theorem B843111 : Blo 842353 843111 := bstep (se 1 (by rfl) ⟨632333, by rfl⟩ : syracuseStep 843111 = 1264667) B1264667
theorem B8347049 : Blo 842353 8347049 := bstep (se 2 (by rfl) ⟨3130143, by rfl⟩ : syracuseStep 8347049 = 6260287) B6260287
theorem B843263 : Blo 842353 843263 := bstep (se 1 (by rfl) ⟨632447, by rfl⟩ : syracuseStep 843263 = 1264895) B1264895
theorem B843391 : Blo 842353 843391 := bstep (se 1 (by rfl) ⟨632543, by rfl⟩ : syracuseStep 843391 = 1265087) B1265087
theorem B844223 : Blo 842353 844223 := bstep (se 1 (by rfl) ⟨633167, by rfl⟩ : syracuseStep 844223 = 1266335) B1266335
theorem B844335 : Blo 842353 844335 := bstep (se 1 (by rfl) ⟨633251, by rfl⟩ : syracuseStep 844335 = 1266503) B1266503
theorem B845083 : Blo 842353 845083 := bstep (se 1 (by rfl) ⟨633812, by rfl⟩ : syracuseStep 845083 = 1267625) B1267625
theorem B3040679 : Blo 842353 3040679 := bstep (se 1 (by rfl) ⟨2280509, by rfl⟩ : syracuseStep 3040679 = 4561019) B4561019
theorem B845263 : Blo 842353 845263 := bstep (se 1 (by rfl) ⟨633947, by rfl⟩ : syracuseStep 845263 = 1267895) B1267895
theorem B845471 : Blo 842353 845471 := bstep (se 1 (by rfl) ⟨634103, by rfl⟩ : syracuseStep 845471 = 1268207) B1268207
theorem B845595 : Blo 842353 845595 := bstep (se 1 (by rfl) ⟨634196, by rfl⟩ : syracuseStep 845595 = 1268393) B1268393
theorem B845887 : Blo 842353 845887 := bstep (se 1 (by rfl) ⟨634415, by rfl⟩ : syracuseStep 845887 = 1268831) B1268831
theorem B3205565 : Blo 842353 3205565 := bstep (se 3 (by rfl) ⟨601043, by rfl⟩ : syracuseStep 3205565 = 1202087) B1202087
theorem B2026235 : Blo 842353 2026235 := bstep (se 1 (by rfl) ⟨1519676, by rfl⟩ : syracuseStep 2026235 = 3039353) B3039353
theorem B2845799 : Blo 842353 2845799 := bstep (se 1 (by rfl) ⟨2134349, by rfl⟩ : syracuseStep 2845799 = 4268699) B4268699
theorem B3337529 : Blo 842353 3337529 := bstep (se 2 (by rfl) ⟨1251573, by rfl⟩ : syracuseStep 3337529 = 2503147) B2503147
theorem B2846123 : Blo 842353 2846123 := bstep (se 1 (by rfl) ⟨2134592, by rfl⟩ : syracuseStep 2846123 = 4269185) B4269185
theorem B2027657 : Blo 842353 2027657 := bstep (se 2 (by rfl) ⟨760371, by rfl⟩ : syracuseStep 2027657 = 1520743) B1520743
theorem B6418601 : Blo 842353 6418601 := bstep (se 2 (by rfl) ⟨2406975, by rfl⟩ : syracuseStep 6418601 = 4813951) B4813951
theorem B10253051 : Blo 842353 10253051 := bstep (se 1 (by rfl) ⟨7689788, by rfl⟩ : syracuseStep 10253051 = 15379577) B15379577
theorem B1602335 : Blo 842353 1602335 := bstep (se 1 (by rfl) ⟨1201751, by rfl⟩ : syracuseStep 1602335 = 2403503) B2403503
theorem B20542481 : Blo 842353 20542481 := bstep (se 2 (by rfl) ⟨7703430, by rfl⟩ : syracuseStep 20542481 = 15406861) B15406861
theorem B2848823 : Blo 842353 2848823 := bstep (se 1 (by rfl) ⟨2136617, by rfl⟩ : syracuseStep 2848823 = 4273235) B4273235
theorem B9599471 : Blo 842353 9599471 := bstep (se 1 (by rfl) ⟨7199603, by rfl⟩ : syracuseStep 9599471 = 14399207) B14399207
theorem B3701791 : Blo 842353 3701791 := bstep (se 1 (by rfl) ⟨2776343, by rfl⟩ : syracuseStep 3701791 = 5552687) B5552687
theorem B949351 : Blo 842353 949351 := bstep (se 1 (by rfl) ⟨712013, by rfl⟩ : syracuseStep 949351 = 1424027) B1424027
theorem B1015915 : Blo 842353 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B1900655 : Blo 842353 1900655 := bstep (se 1 (by rfl) ⟨1425491, by rfl⟩ : syracuseStep 1900655 = 2850983) B2850983
theorem B951079 : Blo 842353 951079 := bstep (se 1 (by rfl) ⟨713309, by rfl⟩ : syracuseStep 951079 = 1426619) B1426619
theorem B4819783 : Blo 842353 4819783 := bstep (se 1 (by rfl) ⟨3614837, by rfl⟩ : syracuseStep 4819783 = 7229675) B7229675
theorem B30741929 : Blo 842353 30741929 := bstep (se 2 (by rfl) ⟨11528223, by rfl⟩ : syracuseStep 30741929 = 23056447) B23056447
theorem B2137043 : Blo 842353 2137043 := bstep (se 1 (by rfl) ⟨1602782, by rfl⟩ : syracuseStep 2137043 = 3205565) B3205565
theorem B4332523 : Blo 842353 4332523 := bstep (se 1 (by rfl) ⟨3249392, by rfl⟩ : syracuseStep 4332523 = 6498785) B6498785
theorem B4267727 : Blo 842353 4267727 := bstep (se 1 (by rfl) ⟨3200795, by rfl⟩ : syracuseStep 4267727 = 6401591) B6401591
theorem B1351771 : Blo 842353 1351771 := bstep (se 1 (by rfl) ⟨1013828, by rfl⟩ : syracuseStep 1351771 = 2027657) B2027657
theorem B6399647 : Blo 842353 6399647 := bstep (se 1 (by rfl) ⟨4799735, by rfl⟩ : syracuseStep 6399647 = 9599471) B9599471
theorem B2402045 : Blo 842353 2402045 := bstep (se 3 (by rfl) ⟨450383, by rfl⟩ : syracuseStep 2402045 = 900767) B900767
theorem B26028155 : Blo 842353 26028155 := bstep (se 1 (by rfl) ⟨19521116, by rfl⟩ : syracuseStep 26028155 = 39042233) B39042233
theorem B19508921 : Blo 842353 19508921 := bstep (se 2 (by rfl) ⟨7315845, by rfl⟩ : syracuseStep 19508921 = 14631691) B14631691
theorem B13709519 : Blo 842353 13709519 := bstep (se 1 (by rfl) ⟨10282139, by rfl⟩ : syracuseStep 13709519 = 20564279) B20564279
theorem B6405479 : Blo 842353 6405479 := bstep (se 1 (by rfl) ⟨4804109, by rfl⟩ : syracuseStep 6405479 = 9608219) B9608219
theorem B19742885 : Blo 842353 19742885 := bstep (se 4 (by rfl) ⟨1850895, by rfl⟩ : syracuseStep 19742885 = 3701791) B3701791
theorem B8668745 : Blo 842353 8668745 := bstep (se 2 (by rfl) ⟨3250779, by rfl⟩ : syracuseStep 8668745 = 6501559) B6501559
theorem B1427935 : Blo 842353 1427935 := bstep (se 1 (by rfl) ⟨1070951, by rfl⟩ : syracuseStep 1427935 = 2141903) B2141903
theorem B4279067 : Blo 842353 4279067 := bstep (se 1 (by rfl) ⟨3209300, by rfl⟩ : syracuseStep 4279067 = 6418601) B6418601
theorem B6835367 : Blo 842353 6835367 := bstep (se 1 (by rfl) ⟨5126525, by rfl⟩ : syracuseStep 6835367 = 10253051) B10253051
theorem B1068223 : Blo 842353 1068223 := bstep (se 1 (by rfl) ⟨801167, by rfl⟩ : syracuseStep 1068223 = 1602335) B1602335
theorem B8900077 : Blo 842353 8900077 := bstep (se 3 (by rfl) ⟨1668764, by rfl⟩ : syracuseStep 8900077 = 3337529) B3337529
theorem B15388703 : Blo 842353 15388703 := bstep (se 1 (by rfl) ⟨11541527, by rfl⟩ : syracuseStep 15388703 = 23083055) B23083055
theorem B1265801 : Blo 842353 1265801 := bstep (se 2 (by rfl) ⟨474675, by rfl⟩ : syracuseStep 1265801 = 949351) B949351
theorem B4051241 : Blo 842353 4051241 := bstep (se 2 (by rfl) ⟨1519215, by rfl⟩ : syracuseStep 4051241 = 3038431) B3038431
theorem B6083201 : Blo 842353 6083201 := bstep (se 2 (by rfl) ⟨2281200, by rfl⟩ : syracuseStep 6083201 = 4562401) B4562401
theorem B51958739 : Blo 842353 51958739 := bstep (se 1 (by rfl) ⟨38969054, by rfl⟩ : syracuseStep 51958739 = 77938109) B77938109
theorem B4281983 : Blo 842353 4281983 := bstep (se 1 (by rfl) ⟨3211487, by rfl⟩ : syracuseStep 4281983 = 6422975) B6422975
theorem B5199871 : Blo 842353 5199871 := bstep (se 1 (by rfl) ⟨3899903, by rfl⟩ : syracuseStep 5199871 = 7799807) B7799807
theorem B27451223 : Blo 842353 27451223 := bstep (se 1 (by rfl) ⟨20588417, by rfl⟩ : syracuseStep 27451223 = 41176835) B41176835
theorem B844255 : Blo 842353 844255 := bstep (se 1 (by rfl) ⟨633191, by rfl⟩ : syracuseStep 844255 = 1266383) B1266383
theorem B844479 : Blo 842353 844479 := bstep (se 1 (by rfl) ⟨633359, by rfl⟩ : syracuseStep 844479 = 1266719) B1266719
theorem B844671 : Blo 842353 844671 := bstep (se 1 (by rfl) ⟨633503, by rfl⟩ : syracuseStep 844671 = 1267007) B1267007
theorem B3204305 : Blo 842353 3204305 := bstep (se 2 (by rfl) ⟨1201614, by rfl⟩ : syracuseStep 3204305 = 2403229) B2403229
theorem B2057575 : Blo 842353 2057575 := bstep (se 1 (by rfl) ⟨1543181, by rfl⟩ : syracuseStep 2057575 = 3086363) B3086363
theorem B9004483 : Blo 842353 9004483 := bstep (se 1 (by rfl) ⟨6753362, by rfl⟩ : syracuseStep 9004483 = 13506725) B13506725
theorem B845519 : Blo 842353 845519 := bstep (se 1 (by rfl) ⟨634139, by rfl⟩ : syracuseStep 845519 = 1268279) B1268279
theorem B5564699 : Blo 842353 5564699 := bstep (se 1 (by rfl) ⟨4173524, by rfl⟩ : syracuseStep 5564699 = 8347049) B8347049
theorem B4058525 : Blo 842353 4058525 := bstep (se 3 (by rfl) ⟨760973, by rfl⟩ : syracuseStep 4058525 = 1521947) B1521947
theorem B1142255 : Blo 842353 1142255 := bstep (se 1 (by rfl) ⟨856691, by rfl⟩ : syracuseStep 1142255 = 1713383) B1713383
theorem B2027119 : Blo 842353 2027119 := bstep (se 1 (by rfl) ⟨1520339, by rfl⟩ : syracuseStep 2027119 = 3040679) B3040679
theorem B5403293 : Blo 842353 5403293 := bstep (se 3 (by rfl) ⟨1013117, by rfl⟩ : syracuseStep 5403293 = 2026235) B2026235
theorem B1897199 : Blo 842353 1897199 := bstep (se 1 (by rfl) ⟨1422899, by rfl⟩ : syracuseStep 1897199 = 2845799) B2845799
theorem B1897415 : Blo 842353 1897415 := bstep (se 1 (by rfl) ⟨1423061, by rfl⟩ : syracuseStep 1897415 = 2846123) B2846123
theorem B2848121 : Blo 842353 2848121 := bstep (se 2 (by rfl) ⟨1068045, by rfl⟩ : syracuseStep 2848121 = 2136091) B2136091
theorem B1013671 : Blo 842353 1013671 := bstep (se 1 (by rfl) ⟨760253, by rfl⟩ : syracuseStep 1013671 = 1520507) B1520507
theorem B13694987 : Blo 842353 13694987 := bstep (se 1 (by rfl) ⟨10271240, by rfl⟩ : syracuseStep 13694987 = 20542481) B20542481
theorem B2029985 : Blo 842353 2029985 := bstep (se 2 (by rfl) ⟨761244, by rfl⟩ : syracuseStep 2029985 = 1522489) B1522489
theorem B3242621 : Blo 842353 3242621 := bstep (se 3 (by rfl) ⟨607991, by rfl⟩ : syracuseStep 3242621 = 1215983) B1215983
theorem B1899215 : Blo 842353 1899215 := bstep (se 1 (by rfl) ⟨1424411, by rfl⟩ : syracuseStep 1899215 = 2848823) B2848823
theorem B2850335 : Blo 842353 2850335 := bstep (se 1 (by rfl) ⟨2137751, by rfl⟩ : syracuseStep 2850335 = 4275503) B4275503
theorem B7209445 : Blo 842353 7209445 := bstep (se 4 (by rfl) ⟨675885, by rfl⟩ : syracuseStep 7209445 = 1351771) B1351771
theorem B16221869 : Blo 842353 16221869 := bstep (se 3 (by rfl) ⟨3041600, by rfl⟩ : syracuseStep 16221869 = 6083201) B6083201
theorem B2852711 : Blo 842353 2852711 := bstep (se 1 (by rfl) ⟨2139533, by rfl⟩ : syracuseStep 2852711 = 4279067) B4279067
theorem B4556911 : Blo 842353 4556911 := bstep (se 1 (by rfl) ⟨3417683, by rfl⟩ : syracuseStep 4556911 = 6835367) B6835367
theorem B10259135 : Blo 842353 10259135 := bstep (se 1 (by rfl) ⟨7694351, by rfl⟩ : syracuseStep 10259135 = 15388703) B15388703
theorem B1903913 : Blo 842353 1903913 := bstep (se 2 (by rfl) ⟨713967, by rfl⟩ : syracuseStep 1903913 = 1427935) B1427935
theorem B34639159 : Blo 842353 34639159 := bstep (se 1 (by rfl) ⟨25979369, by rfl⟩ : syracuseStep 34639159 = 51958739) B51958739
theorem B2854655 : Blo 842353 2854655 := bstep (se 1 (by rfl) ⟨2140991, by rfl⟩ : syracuseStep 2854655 = 4281983) B4281983
theorem B6426377 : Blo 842353 6426377 := bstep (se 2 (by rfl) ⟨2409891, by rfl⟩ : syracuseStep 6426377 = 4819783) B4819783
theorem B11866769 : Blo 842353 11866769 := bstep (se 2 (by rfl) ⟨4450038, by rfl⟩ : syracuseStep 11866769 = 8900077) B8900077
theorem B2136203 : Blo 842353 2136203 := bstep (se 1 (by rfl) ⟨1602152, by rfl⟩ : syracuseStep 2136203 = 3204305) B3204305
theorem B4266431 : Blo 842353 4266431 := bstep (se 1 (by rfl) ⟨3199823, by rfl⟩ : syracuseStep 4266431 = 6399647) B6399647
theorem B3709799 : Blo 842353 3709799 := bstep (se 1 (by rfl) ⟨2782349, by rfl⟩ : syracuseStep 3709799 = 5564699) B5564699
theorem B1351561 : Blo 842353 1351561 := bstep (se 2 (by rfl) ⟨506835, by rfl⟩ : syracuseStep 1351561 = 1013671) B1013671
theorem B10822733 : Blo 842353 10822733 := bstep (se 3 (by rfl) ⟨2029262, by rfl⟩ : syracuseStep 10822733 = 4058525) B4058525
theorem B5776697 : Blo 842353 5776697 := bstep (se 2 (by rfl) ⟨2166261, by rfl⟩ : syracuseStep 5776697 = 4332523) B4332523
theorem B1353323 : Blo 842353 1353323 := bstep (se 1 (by rfl) ⟨1014992, by rfl⟩ : syracuseStep 1353323 = 2029985) B2029985
theorem B4270319 : Blo 842353 4270319 := bstep (se 1 (by rfl) ⟨3202739, by rfl⟩ : syracuseStep 4270319 = 6405479) B6405479
theorem B1354553 : Blo 842353 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B5779163 : Blo 842353 5779163 := bstep (se 1 (by rfl) ⟨4334372, by rfl⟩ : syracuseStep 5779163 = 8668745) B8668745
theorem B12005977 : Blo 842353 12005977 := bstep (se 2 (by rfl) ⟨4502241, by rfl⟩ : syracuseStep 12005977 = 9004483) B9004483
theorem B2700827 : Blo 842353 2700827 := bstep (se 1 (by rfl) ⟨2025620, by rfl⟩ : syracuseStep 2700827 = 4051241) B4051241
theorem B20494619 : Blo 842353 20494619 := bstep (se 1 (by rfl) ⟨15370964, by rfl⟩ : syracuseStep 20494619 = 30741929) B30741929
theorem B1424297 : Blo 842353 1424297 := bstep (se 2 (by rfl) ⟨534111, by rfl⟩ : syracuseStep 1424297 = 1068223) B1068223
theorem B1424695 : Blo 842353 1424695 := bstep (se 1 (by rfl) ⟨1068521, by rfl⟩ : syracuseStep 1424695 = 2137043) B2137043
theorem B2702825 : Blo 842353 2702825 := bstep (se 2 (by rfl) ⟨1013559, by rfl⟩ : syracuseStep 2702825 = 2027119) B2027119
theorem B18300815 : Blo 842353 18300815 := bstep (se 1 (by rfl) ⟨13725611, by rfl⟩ : syracuseStep 18300815 = 27451223) B27451223
theorem B17352103 : Blo 842353 17352103 := bstep (se 1 (by rfl) ⟨13014077, by rfl⟩ : syracuseStep 17352103 = 26028155) B26028155
theorem B6933161 : Blo 842353 6933161 := bstep (se 2 (by rfl) ⟨2599935, by rfl⟩ : syracuseStep 6933161 = 5199871) B5199871
theorem B1264799 : Blo 842353 1264799 := bstep (se 1 (by rfl) ⟨948599, by rfl⟩ : syracuseStep 1264799 = 1897199) B1897199
theorem B1264943 : Blo 842353 1264943 := bstep (se 1 (by rfl) ⟨948707, by rfl⟩ : syracuseStep 1264943 = 1897415) B1897415
theorem B9129991 : Blo 842353 9129991 := bstep (se 1 (by rfl) ⟨6847493, by rfl⟩ : syracuseStep 9129991 = 13694987) B13694987
theorem B1266143 : Blo 842353 1266143 := bstep (se 1 (by rfl) ⟨949607, by rfl⟩ : syracuseStep 1266143 = 1899215) B1899215
theorem B1267103 : Blo 842353 1267103 := bstep (se 1 (by rfl) ⟨950327, by rfl⟩ : syracuseStep 1267103 = 1900655) B1900655
theorem B13161923 : Blo 842353 13161923 := bstep (se 1 (by rfl) ⟨9871442, by rfl⟩ : syracuseStep 13161923 = 19742885) B19742885
theorem B1268105 : Blo 842353 1268105 := bstep (se 2 (by rfl) ⟨475539, by rfl⟩ : syracuseStep 1268105 = 951079) B951079
theorem B2743433 : Blo 842353 2743433 := bstep (se 2 (by rfl) ⟨1028787, by rfl⟩ : syracuseStep 2743433 = 2057575) B2057575
theorem B843867 : Blo 842353 843867 := bstep (se 1 (by rfl) ⟨632900, by rfl⟩ : syracuseStep 843867 = 1265801) B1265801
theorem B2845151 : Blo 842353 2845151 := bstep (se 1 (by rfl) ⟨2133863, by rfl⟩ : syracuseStep 2845151 = 4267727) B4267727
theorem B1601363 : Blo 842353 1601363 := bstep (se 1 (by rfl) ⟨1201022, by rfl⟩ : syracuseStep 1601363 = 2402045) B2402045
theorem B13005947 : Blo 842353 13005947 := bstep (se 1 (by rfl) ⟨9754460, by rfl⟩ : syracuseStep 13005947 = 19508921) B19508921
theorem B9139679 : Blo 842353 9139679 := bstep (se 1 (by rfl) ⟨6854759, by rfl⟩ : syracuseStep 9139679 = 13709519) B13709519
theorem B3602195 : Blo 842353 3602195 := bstep (se 1 (by rfl) ⟨2701646, by rfl⟩ : syracuseStep 3602195 = 5403293) B5403293
theorem B1898747 : Blo 842353 1898747 := bstep (se 1 (by rfl) ⟨1424060, by rfl⟩ : syracuseStep 1898747 = 2848121) B2848121
theorem B3046013 : Blo 842353 3046013 := bstep (se 3 (by rfl) ⟨571127, by rfl⟩ : syracuseStep 3046013 = 1142255) B1142255
theorem B2161747 : Blo 842353 2161747 := bstep (se 1 (by rfl) ⟨1621310, by rfl⟩ : syracuseStep 2161747 = 3242621) B3242621
theorem B1900223 : Blo 842353 1900223 := bstep (se 1 (by rfl) ⟨1425167, by rfl⟩ : syracuseStep 1900223 = 2850335) B2850335
theorem B10814579 : Blo 842353 10814579 := bstep (se 1 (by rfl) ⟨8110934, by rfl⟩ : syracuseStep 10814579 = 16221869) B16221869
theorem B1901807 : Blo 842353 1901807 := bstep (se 1 (by rfl) ⟨1426355, by rfl⟩ : syracuseStep 1901807 = 2852711) B2852711
theorem B23136137 : Blo 842353 23136137 := bstep (se 2 (by rfl) ⟨8676051, by rfl⟩ : syracuseStep 23136137 = 17352103) B17352103
theorem B1903103 : Blo 842353 1903103 := bstep (se 1 (by rfl) ⟨1427327, by rfl⟩ : syracuseStep 1903103 = 2854655) B2854655
theorem B15404525 : Blo 842353 15404525 := bstep (se 3 (by rfl) ⟨2888348, by rfl⟩ : syracuseStep 15404525 = 5776697) B5776697
theorem B7215155 : Blo 842353 7215155 := bstep (se 1 (by rfl) ⟨5411366, by rfl⟩ : syracuseStep 7215155 = 10822733) B10822733
theorem B18488429 : Blo 842353 18488429 := bstep (se 3 (by rfl) ⟨3466580, by rfl⟩ : syracuseStep 18488429 = 6933161) B6933161
theorem B2401463 : Blo 842353 2401463 := bstep (se 1 (by rfl) ⟨1801097, by rfl⟩ : syracuseStep 2401463 = 3602195) B3602195
theorem B12200543 : Blo 842353 12200543 := bstep (se 1 (by rfl) ⟨9150407, by rfl⟩ : syracuseStep 12200543 = 18300815) B18300815
theorem B9612593 : Blo 842353 9612593 := bstep (se 2 (by rfl) ⟨3604722, by rfl⟩ : syracuseStep 9612593 = 7209445) B7209445
theorem B6075881 : Blo 842353 6075881 := bstep (se 2 (by rfl) ⟨2278455, by rfl⟩ : syracuseStep 6075881 = 4556911) B4556911
theorem B34682525 : Blo 842353 34682525 := bstep (se 3 (by rfl) ⟨6502973, by rfl⟩ : syracuseStep 34682525 = 13005947) B13005947
theorem B7911179 : Blo 842353 7911179 := bstep (se 1 (by rfl) ⟨5933384, by rfl⟩ : syracuseStep 7911179 = 11866769) B11866769
theorem B1424135 : Blo 842353 1424135 := bstep (se 1 (by rfl) ⟨1068101, by rfl⟩ : syracuseStep 1424135 = 2136203) B2136203
theorem B46185545 : Blo 842353 46185545 := bstep (se 2 (by rfl) ⟨17319579, by rfl⟩ : syracuseStep 46185545 = 34639159) B34639159
theorem B2473199 : Blo 842353 2473199 := bstep (se 1 (by rfl) ⟨1854899, by rfl⟩ : syracuseStep 2473199 = 3709799) B3709799
theorem B12173321 : Blo 842353 12173321 := bstep (se 2 (by rfl) ⟨4564995, by rfl⟩ : syracuseStep 12173321 = 9129991) B9129991
theorem B16007969 : Blo 842353 16007969 := bstep (se 2 (by rfl) ⟨6002988, by rfl⟩ : syracuseStep 16007969 = 12005977) B12005977
theorem B902215 : Blo 842353 902215 := bstep (se 1 (by rfl) ⟨676661, by rfl⟩ : syracuseStep 902215 = 1353323) B1353323
theorem B903035 : Blo 842353 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B3852775 : Blo 842353 3852775 := bstep (se 1 (by rfl) ⟨2889581, by rfl⟩ : syracuseStep 3852775 = 5779163) B5779163
theorem B1067575 : Blo 842353 1067575 := bstep (se 1 (by rfl) ⟨800681, by rfl⟩ : syracuseStep 1067575 = 1601363) B1601363
theorem B1265831 : Blo 842353 1265831 := bstep (se 1 (by rfl) ⟨949373, by rfl⟩ : syracuseStep 1265831 = 1898747) B1898747
theorem B1266815 : Blo 842353 1266815 := bstep (se 1 (by rfl) ⟨950111, by rfl⟩ : syracuseStep 1266815 = 1900223) B1900223
theorem B6839423 : Blo 842353 6839423 := bstep (se 1 (by rfl) ⟨5129567, by rfl⟩ : syracuseStep 6839423 = 10259135) B10259135
theorem B843199 : Blo 842353 843199 := bstep (se 1 (by rfl) ⟨632399, by rfl⟩ : syracuseStep 843199 = 1264799) B1264799
theorem B1269275 : Blo 842353 1269275 := bstep (se 1 (by rfl) ⟨951956, by rfl⟩ : syracuseStep 1269275 = 1903913) B1903913
theorem B843295 : Blo 842353 843295 := bstep (se 1 (by rfl) ⟨632471, by rfl⟩ : syracuseStep 843295 = 1264943) B1264943
theorem B4284251 : Blo 842353 4284251 := bstep (se 1 (by rfl) ⟨3213188, by rfl⟩ : syracuseStep 4284251 = 6426377) B6426377
theorem B844095 : Blo 842353 844095 := bstep (se 1 (by rfl) ⟨633071, by rfl⟩ : syracuseStep 844095 = 1266143) B1266143
theorem B844735 : Blo 842353 844735 := bstep (se 1 (by rfl) ⟨633551, by rfl⟩ : syracuseStep 844735 = 1267103) B1267103
theorem B8774615 : Blo 842353 8774615 := bstep (se 1 (by rfl) ⟨6580961, by rfl⟩ : syracuseStep 8774615 = 13161923) B13161923
theorem B845403 : Blo 842353 845403 := bstep (se 1 (by rfl) ⟨634052, by rfl⟩ : syracuseStep 845403 = 1268105) B1268105
theorem B2844287 : Blo 842353 2844287 := bstep (se 1 (by rfl) ⟨2133215, by rfl⟩ : syracuseStep 2844287 = 4266431) B4266431
theorem B1828955 : Blo 842353 1828955 := bstep (se 1 (by rfl) ⟨1371716, by rfl⟩ : syracuseStep 1828955 = 2743433) B2743433
theorem B11529317 : Blo 842353 11529317 := bstep (se 4 (by rfl) ⟨1080873, by rfl⟩ : syracuseStep 11529317 = 2161747) B2161747
theorem B2846879 : Blo 842353 2846879 := bstep (se 1 (by rfl) ⟨2135159, by rfl⟩ : syracuseStep 2846879 = 4270319) B4270319
theorem B1896767 : Blo 842353 1896767 := bstep (se 1 (by rfl) ⟨1422575, by rfl⟩ : syracuseStep 1896767 = 2845151) B2845151
theorem B6093119 : Blo 842353 6093119 := bstep (se 1 (by rfl) ⟨4569839, by rfl⟩ : syracuseStep 6093119 = 9139679) B9139679
theorem B1800551 : Blo 842353 1800551 := bstep (se 1 (by rfl) ⟨1350413, by rfl⟩ : syracuseStep 1800551 = 2700827) B2700827
theorem B13663079 : Blo 842353 13663079 := bstep (se 1 (by rfl) ⟨10247309, by rfl⟩ : syracuseStep 13663079 = 20494619) B20494619
theorem B1899593 : Blo 842353 1899593 := bstep (se 2 (by rfl) ⟨712347, by rfl⟩ : syracuseStep 1899593 = 1424695) B1424695
theorem B2030675 : Blo 842353 2030675 := bstep (se 1 (by rfl) ⟨1523006, by rfl⟩ : syracuseStep 2030675 = 3046013) B3046013
theorem B949531 : Blo 842353 949531 := bstep (se 1 (by rfl) ⟨712148, by rfl⟩ : syracuseStep 949531 = 1424297) B1424297
theorem B1801883 : Blo 842353 1801883 := bstep (se 1 (by rfl) ⟨1351412, by rfl⟩ : syracuseStep 1801883 = 2702825) B2702825
theorem B1802081 : Blo 842353 1802081 := bstep (se 2 (by rfl) ⟨675780, by rfl⟩ : syracuseStep 1802081 = 1351561) B1351561
theorem B7209719 : Blo 842353 7209719 := bstep (se 1 (by rfl) ⟨5407289, by rfl⟩ : syracuseStep 7209719 = 10814579) B10814579
theorem B12325619 : Blo 842353 12325619 := bstep (se 1 (by rfl) ⟨9244214, by rfl⟩ : syracuseStep 12325619 = 18488429) B18488429
theorem B4559615 : Blo 842353 4559615 := bstep (se 1 (by rfl) ⟨3419711, by rfl⟩ : syracuseStep 4559615 = 6839423) B6839423
theorem B2856167 : Blo 842353 2856167 := bstep (se 1 (by rfl) ⟨2142125, by rfl⟩ : syracuseStep 2856167 = 4284251) B4284251
theorem B1219303 : Blo 842353 1219303 := bstep (se 1 (by rfl) ⟨914477, by rfl⟩ : syracuseStep 1219303 = 1828955) B1828955
theorem B8133695 : Blo 842353 8133695 := bstep (se 1 (by rfl) ⟨6100271, by rfl⟩ : syracuseStep 8133695 = 12200543) B12200543
theorem B5415133 : Blo 842353 5415133 := bstep (se 3 (by rfl) ⟨1015337, by rfl⟩ : syracuseStep 5415133 = 2030675) B2030675
theorem B30744845 : Blo 842353 30744845 := bstep (se 3 (by rfl) ⟨5764658, by rfl⟩ : syracuseStep 30744845 = 11529317) B11529317
theorem B1648799 : Blo 842353 1648799 := bstep (se 1 (by rfl) ⟨1236599, by rfl⟩ : syracuseStep 1648799 = 2473199) B2473199
theorem B10269683 : Blo 842353 10269683 := bstep (se 1 (by rfl) ⟨7702262, by rfl⟩ : syracuseStep 10269683 = 15404525) B15404525
theorem B1423433 : Blo 842353 1423433 := bstep (se 2 (by rfl) ⟨533787, by rfl⟩ : syracuseStep 1423433 = 1067575) B1067575
theorem B2408093 : Blo 842353 2408093 := bstep (se 3 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 2408093 = 903035) B903035
theorem B5849743 : Blo 842353 5849743 := bstep (se 1 (by rfl) ⟨4387307, by rfl⟩ : syracuseStep 5849743 = 8774615) B8774615
theorem B6408395 : Blo 842353 6408395 := bstep (se 1 (by rfl) ⟨4806296, by rfl⟩ : syracuseStep 6408395 = 9612593) B9612593
theorem B1264511 : Blo 842353 1264511 := bstep (se 1 (by rfl) ⟨948383, by rfl⟩ : syracuseStep 1264511 = 1896767) B1896767
theorem B4050587 : Blo 842353 4050587 := bstep (se 1 (by rfl) ⟨3037940, by rfl⟩ : syracuseStep 4050587 = 6075881) B6075881
theorem B23121683 : Blo 842353 23121683 := bstep (se 1 (by rfl) ⟨17341262, by rfl⟩ : syracuseStep 23121683 = 34682525) B34682525
theorem B1200367 : Blo 842353 1200367 := bstep (se 1 (by rfl) ⟨900275, by rfl⟩ : syracuseStep 1200367 = 1800551) B1800551
theorem B1266041 : Blo 842353 1266041 := bstep (se 2 (by rfl) ⟨474765, by rfl⟩ : syracuseStep 1266041 = 949531) B949531
theorem B4805021 : Blo 842353 4805021 := bstep (se 3 (by rfl) ⟨900941, by rfl⟩ : syracuseStep 4805021 = 1801883) B1801883
theorem B30790363 : Blo 842353 30790363 := bstep (se 1 (by rfl) ⟨23092772, by rfl⟩ : syracuseStep 30790363 = 46185545) B46185545
theorem B1266395 : Blo 842353 1266395 := bstep (se 1 (by rfl) ⟨949796, by rfl⟩ : syracuseStep 1266395 = 1899593) B1899593
theorem B1201387 : Blo 842353 1201387 := bstep (se 1 (by rfl) ⟨901040, by rfl⟩ : syracuseStep 1201387 = 1802081) B1802081
theorem B8115547 : Blo 842353 8115547 := bstep (se 1 (by rfl) ⟨6086660, by rfl⟩ : syracuseStep 8115547 = 12173321) B12173321
theorem B1267871 : Blo 842353 1267871 := bstep (se 1 (by rfl) ⟨950903, by rfl⟩ : syracuseStep 1267871 = 1901807) B1901807
theorem B15424091 : Blo 842353 15424091 := bstep (se 1 (by rfl) ⟨11568068, by rfl⟩ : syracuseStep 15424091 = 23136137) B23136137
theorem B1202953 : Blo 842353 1202953 := bstep (se 2 (by rfl) ⟨451107, by rfl⟩ : syracuseStep 1202953 = 902215) B902215
theorem B1268735 : Blo 842353 1268735 := bstep (se 1 (by rfl) ⟨951551, by rfl⟩ : syracuseStep 1268735 = 1903103) B1903103
theorem B42687917 : Blo 842353 42687917 := bstep (se 3 (by rfl) ⟨8003984, by rfl⟩ : syracuseStep 42687917 = 16007969) B16007969
theorem B843887 : Blo 842353 843887 := bstep (se 1 (by rfl) ⟨632915, by rfl⟩ : syracuseStep 843887 = 1265831) B1265831
theorem B5137033 : Blo 842353 5137033 := bstep (se 2 (by rfl) ⟨1926387, by rfl⟩ : syracuseStep 5137033 = 3852775) B3852775
theorem B844543 : Blo 842353 844543 := bstep (se 1 (by rfl) ⟨633407, by rfl⟩ : syracuseStep 844543 = 1266815) B1266815
theorem B4810103 : Blo 842353 4810103 := bstep (se 1 (by rfl) ⟨3607577, by rfl⟩ : syracuseStep 4810103 = 7215155) B7215155
theorem B846183 : Blo 842353 846183 := bstep (se 1 (by rfl) ⟨634637, by rfl⟩ : syracuseStep 846183 = 1269275) B1269275
theorem B1600975 : Blo 842353 1600975 := bstep (se 1 (by rfl) ⟨1200731, by rfl⟩ : syracuseStep 1600975 = 2401463) B2401463
theorem B1896191 : Blo 842353 1896191 := bstep (se 1 (by rfl) ⟨1422143, by rfl⟩ : syracuseStep 1896191 = 2844287) B2844287
theorem B1897919 : Blo 842353 1897919 := bstep (se 1 (by rfl) ⟨1423439, by rfl⟩ : syracuseStep 1897919 = 2846879) B2846879
theorem B5274119 : Blo 842353 5274119 := bstep (se 1 (by rfl) ⟨3955589, by rfl⟩ : syracuseStep 5274119 = 7911179) B7911179
theorem B4062079 : Blo 842353 4062079 := bstep (se 1 (by rfl) ⟨3046559, by rfl⟩ : syracuseStep 4062079 = 6093119) B6093119
theorem B949423 : Blo 842353 949423 := bstep (se 1 (by rfl) ⟨712067, by rfl⟩ : syracuseStep 949423 = 1424135) B1424135
theorem B9108719 : Blo 842353 9108719 := bstep (se 1 (by rfl) ⟨6831539, by rfl⟩ : syracuseStep 9108719 = 13663079) B13663079
theorem B6849377 : Blo 842353 6849377 := bstep (se 2 (by rfl) ⟨2568516, by rfl⟩ : syracuseStep 6849377 = 5137033) B5137033
theorem B7799657 : Blo 842353 7799657 := bstep (se 2 (by rfl) ⟨2924871, by rfl⟩ : syracuseStep 7799657 = 5849743) B5849743
theorem B32868317 : Blo 842353 32868317 := bstep (se 3 (by rfl) ⟨6162809, by rfl⟩ : syracuseStep 32868317 = 12325619) B12325619
theorem B1904111 : Blo 842353 1904111 := bstep (se 1 (by rfl) ⟨1428083, by rfl⟩ : syracuseStep 1904111 = 2856167) B2856167
theorem B2134633 : Blo 842353 2134633 := bstep (se 2 (by rfl) ⟨800487, by rfl⟩ : syracuseStep 2134633 = 1600975) B1600975
theorem B21664421 : Blo 842353 21664421 := bstep (se 4 (by rfl) ⟨2031039, by rfl⟩ : syracuseStep 21664421 = 4062079) B4062079
theorem B14064317 : Blo 842353 14064317 := bstep (se 3 (by rfl) ⟨2637059, by rfl⟩ : syracuseStep 14064317 = 5274119) B5274119
theorem B10820729 : Blo 842353 10820729 := bstep (se 2 (by rfl) ⟨4057773, by rfl⟩ : syracuseStep 10820729 = 8115547) B8115547
theorem B6072479 : Blo 842353 6072479 := bstep (se 1 (by rfl) ⟨4554359, by rfl⟩ : syracuseStep 6072479 = 9108719) B9108719
theorem B7220177 : Blo 842353 7220177 := bstep (se 2 (by rfl) ⟨2707566, by rfl⟩ : syracuseStep 7220177 = 5415133) B5415133
theorem B4272263 : Blo 842353 4272263 := bstep (se 1 (by rfl) ⟨3204197, by rfl⟩ : syracuseStep 4272263 = 6408395) B6408395
theorem B2700391 : Blo 842353 2700391 := bstep (se 1 (by rfl) ⟨2025293, by rfl⟩ : syracuseStep 2700391 = 4050587) B4050587
theorem B15414455 : Blo 842353 15414455 := bstep (se 1 (by rfl) ⟨11560841, by rfl⟩ : syracuseStep 15414455 = 23121683) B23121683
theorem B5422463 : Blo 842353 5422463 := bstep (se 1 (by rfl) ⟨4066847, by rfl⟩ : syracuseStep 5422463 = 8133695) B8133695
theorem B28458611 : Blo 842353 28458611 := bstep (se 1 (by rfl) ⟨21343958, by rfl⟩ : syracuseStep 28458611 = 42687917) B42687917
theorem B20496563 : Blo 842353 20496563 := bstep (se 1 (by rfl) ⟨15372422, by rfl⟩ : syracuseStep 20496563 = 30744845) B30744845
theorem B1099199 : Blo 842353 1099199 := bstep (se 1 (by rfl) ⟨824399, by rfl⟩ : syracuseStep 1099199 = 1648799) B1648799
theorem B1264127 : Blo 842353 1264127 := bstep (se 1 (by rfl) ⟨948095, by rfl⟩ : syracuseStep 1264127 = 1896191) B1896191
theorem B1265279 : Blo 842353 1265279 := bstep (se 1 (by rfl) ⟨948959, by rfl⟩ : syracuseStep 1265279 = 1897919) B1897919
theorem B1625737 : Blo 842353 1625737 := bstep (se 2 (by rfl) ⟨609651, by rfl⟩ : syracuseStep 1625737 = 1219303) B1219303
theorem B1265897 : Blo 842353 1265897 := bstep (se 2 (by rfl) ⟨474711, by rfl⟩ : syracuseStep 1265897 = 949423) B949423
theorem B4806479 : Blo 842353 4806479 := bstep (se 1 (by rfl) ⟨3604859, by rfl⟩ : syracuseStep 4806479 = 7209719) B7209719
theorem B843007 : Blo 842353 843007 := bstep (se 1 (by rfl) ⟨632255, by rfl⟩ : syracuseStep 843007 = 1264511) B1264511
theorem B844027 : Blo 842353 844027 := bstep (se 1 (by rfl) ⟨633020, by rfl⟩ : syracuseStep 844027 = 1266041) B1266041
theorem B3203347 : Blo 842353 3203347 := bstep (se 1 (by rfl) ⟨2402510, by rfl⟩ : syracuseStep 3203347 = 4805021) B4805021
theorem B844263 : Blo 842353 844263 := bstep (se 1 (by rfl) ⟨633197, by rfl⟩ : syracuseStep 844263 = 1266395) B1266395
theorem B3039743 : Blo 842353 3039743 := bstep (se 1 (by rfl) ⟨2279807, by rfl⟩ : syracuseStep 3039743 = 4559615) B4559615
theorem B845247 : Blo 842353 845247 := bstep (se 1 (by rfl) ⟨633935, by rfl⟩ : syracuseStep 845247 = 1267871) B1267871
theorem B10282727 : Blo 842353 10282727 := bstep (se 1 (by rfl) ⟨7712045, by rfl⟩ : syracuseStep 10282727 = 15424091) B15424091
theorem B845823 : Blo 842353 845823 := bstep (se 1 (by rfl) ⟨634367, by rfl⟩ : syracuseStep 845823 = 1268735) B1268735
theorem B1600489 : Blo 842353 1600489 := bstep (se 2 (by rfl) ⟨600183, by rfl⟩ : syracuseStep 1600489 = 1200367) B1200367
theorem B3206735 : Blo 842353 3206735 := bstep (se 1 (by rfl) ⟨2405051, by rfl⟩ : syracuseStep 3206735 = 4810103) B4810103
theorem B41053817 : Blo 842353 41053817 := bstep (se 2 (by rfl) ⟨15395181, by rfl⟩ : syracuseStep 41053817 = 30790363) B30790363
theorem B1601849 : Blo 842353 1601849 := bstep (se 2 (by rfl) ⟨600693, by rfl⟩ : syracuseStep 1601849 = 1201387) B1201387
theorem B6846455 : Blo 842353 6846455 := bstep (se 1 (by rfl) ⟨5134841, by rfl⟩ : syracuseStep 6846455 = 10269683) B10269683
theorem B1603937 : Blo 842353 1603937 := bstep (se 2 (by rfl) ⟨601476, by rfl⟩ : syracuseStep 1603937 = 1202953) B1202953
theorem B948955 : Blo 842353 948955 := bstep (se 1 (by rfl) ⟨711716, by rfl⟩ : syracuseStep 948955 = 1423433) B1423433
theorem B1605395 : Blo 842353 1605395 := bstep (se 1 (by rfl) ⟨1204046, by rfl⟩ : syracuseStep 1605395 = 2408093) B2408093
theorem B13664375 : Blo 842353 13664375 := bstep (se 1 (by rfl) ⟨10248281, by rfl⟩ : syracuseStep 13664375 = 20496563) B20496563
theorem B2133985 : Blo 842353 2133985 := bstep (se 2 (by rfl) ⟨800244, by rfl⟩ : syracuseStep 2133985 = 1600489) B1600489
theorem B9376211 : Blo 842353 9376211 := bstep (se 1 (by rfl) ⟨7032158, by rfl⟩ : syracuseStep 9376211 = 14064317) B14064317
theorem B7213819 : Blo 842353 7213819 := bstep (se 1 (by rfl) ⟨5410364, by rfl⟩ : syracuseStep 7213819 = 10820729) B10820729
theorem B2167649 : Blo 842353 2167649 := bstep (se 2 (by rfl) ⟨812868, by rfl⟩ : syracuseStep 2167649 = 1625737) B1625737
theorem B18257213 : Blo 842353 18257213 := bstep (se 3 (by rfl) ⟨3423227, by rfl⟩ : syracuseStep 18257213 = 6846455) B6846455
theorem B2137823 : Blo 842353 2137823 := bstep (se 1 (by rfl) ⟨1603367, by rfl⟩ : syracuseStep 2137823 = 3206735) B3206735
theorem B3614975 : Blo 842353 3614975 := bstep (se 1 (by rfl) ⟨2711231, by rfl⟩ : syracuseStep 3614975 = 5422463) B5422463
theorem B4271129 : Blo 842353 4271129 := bstep (se 2 (by rfl) ⟨1601673, by rfl⟩ : syracuseStep 4271129 = 3203347) B3203347
theorem B4566251 : Blo 842353 4566251 := bstep (se 1 (by rfl) ⟨3424688, by rfl⟩ : syracuseStep 4566251 = 6849377) B6849377
theorem B2931197 : Blo 842353 2931197 := bstep (se 3 (by rfl) ⟨549599, by rfl⟩ : syracuseStep 2931197 = 1099199) B1099199
theorem B4048319 : Blo 842353 4048319 := bstep (se 1 (by rfl) ⟨3036239, by rfl⟩ : syracuseStep 4048319 = 6072479) B6072479
theorem B1067899 : Blo 842353 1067899 := bstep (se 1 (by rfl) ⟨800924, by rfl⟩ : syracuseStep 1067899 = 1601849) B1601849
theorem B10276303 : Blo 842353 10276303 := bstep (se 1 (by rfl) ⟨7707227, by rfl⟩ : syracuseStep 10276303 = 15414455) B15414455
theorem B1265273 : Blo 842353 1265273 := bstep (se 2 (by rfl) ⟨474477, by rfl⟩ : syracuseStep 1265273 = 948955) B948955
theorem B1069291 : Blo 842353 1069291 := bstep (se 1 (by rfl) ⟨801968, by rfl⟩ : syracuseStep 1069291 = 1603937) B1603937
theorem B1070263 : Blo 842353 1070263 := bstep (se 1 (by rfl) ⟨802697, by rfl⟩ : syracuseStep 1070263 = 1605395) B1605395
theorem B21912211 : Blo 842353 21912211 := bstep (se 1 (by rfl) ⟨16434158, by rfl⟩ : syracuseStep 21912211 = 32868317) B32868317
theorem B842751 : Blo 842353 842751 := bstep (se 1 (by rfl) ⟨632063, by rfl⟩ : syracuseStep 842751 = 1264127) B1264127
theorem B1269407 : Blo 842353 1269407 := bstep (se 1 (by rfl) ⟨952055, by rfl⟩ : syracuseStep 1269407 = 1904111) B1904111
theorem B843519 : Blo 842353 843519 := bstep (se 1 (by rfl) ⟨632639, by rfl⟩ : syracuseStep 843519 = 1265279) B1265279
theorem B843931 : Blo 842353 843931 := bstep (se 1 (by rfl) ⟨632948, by rfl⟩ : syracuseStep 843931 = 1265897) B1265897
theorem B14442947 : Blo 842353 14442947 := bstep (se 1 (by rfl) ⟨10832210, by rfl⟩ : syracuseStep 14442947 = 21664421) B21664421
theorem B3204319 : Blo 842353 3204319 := bstep (se 1 (by rfl) ⟨2403239, by rfl⟩ : syracuseStep 3204319 = 4806479) B4806479
theorem B27420605 : Blo 842353 27420605 := bstep (se 3 (by rfl) ⟨5141363, by rfl⟩ : syracuseStep 27420605 = 10282727) B10282727
theorem B2026495 : Blo 842353 2026495 := bstep (se 1 (by rfl) ⟨1519871, by rfl⟩ : syracuseStep 2026495 = 3039743) B3039743
theorem B2846177 : Blo 842353 2846177 := bstep (se 2 (by rfl) ⟨1067316, by rfl⟩ : syracuseStep 2846177 = 2134633) B2134633
theorem B3600521 : Blo 842353 3600521 := bstep (se 2 (by rfl) ⟨1350195, by rfl⟩ : syracuseStep 3600521 = 2700391) B2700391
theorem B4813451 : Blo 842353 4813451 := bstep (se 1 (by rfl) ⟨3610088, by rfl⟩ : syracuseStep 4813451 = 7220177) B7220177
theorem B2848175 : Blo 842353 2848175 := bstep (se 1 (by rfl) ⟨2136131, by rfl⟩ : syracuseStep 2848175 = 4272263) B4272263
theorem B83196341 : Blo 842353 83196341 := bstep (se 5 (by rfl) ⟨3899828, by rfl⟩ : syracuseStep 83196341 = 7799657) B7799657
theorem B109476845 : Blo 842353 109476845 := bstep (se 3 (by rfl) ⟨20526908, by rfl⟩ : syracuseStep 109476845 = 41053817) B41053817
theorem B18972407 : Blo 842353 18972407 := bstep (se 1 (by rfl) ⟨14229305, by rfl⟩ : syracuseStep 18972407 = 28458611) B28458611
theorem B9109583 : Blo 842353 9109583 := bstep (se 1 (by rfl) ⟨6832187, by rfl⟩ : syracuseStep 9109583 = 13664375) B13664375
theorem B1445099 : Blo 842353 1445099 := bstep (se 1 (by rfl) ⟨1083824, by rfl⟩ : syracuseStep 1445099 = 2167649) B2167649
theorem B13701737 : Blo 842353 13701737 := bstep (se 2 (by rfl) ⟨5138151, by rfl⟩ : syracuseStep 13701737 = 10276303) B10276303
theorem B31266101 : Blo 842353 31266101 := bstep (se 5 (by rfl) ⟨1465598, by rfl⟩ : syracuseStep 31266101 = 2931197) B2931197
theorem B2400347 : Blo 842353 2400347 := bstep (se 1 (by rfl) ⟨1800260, by rfl⟩ : syracuseStep 2400347 = 3600521) B3600521
theorem B72984563 : Blo 842353 72984563 := bstep (se 1 (by rfl) ⟨54738422, by rfl⟩ : syracuseStep 72984563 = 109476845) B109476845
theorem B2698879 : Blo 842353 2698879 := bstep (se 1 (by rfl) ⟨2024159, by rfl⟩ : syracuseStep 2698879 = 4048319) B4048319
theorem B4272425 : Blo 842353 4272425 := bstep (se 2 (by rfl) ⟨1602159, by rfl⟩ : syracuseStep 4272425 = 3204319) B3204319
theorem B116865125 : Blo 842353 116865125 := bstep (se 4 (by rfl) ⟨10956105, by rfl⟩ : syracuseStep 116865125 = 21912211) B21912211
theorem B12171475 : Blo 842353 12171475 := bstep (se 1 (by rfl) ⟨9128606, by rfl⟩ : syracuseStep 12171475 = 18257213) B18257213
theorem B1423865 : Blo 842353 1423865 := bstep (se 2 (by rfl) ⟨533949, by rfl⟩ : syracuseStep 1423865 = 1067899) B1067899
theorem B2701993 : Blo 842353 2701993 := bstep (se 2 (by rfl) ⟨1013247, by rfl⟩ : syracuseStep 2701993 = 2026495) B2026495
theorem B1425215 : Blo 842353 1425215 := bstep (se 1 (by rfl) ⟨1068911, by rfl⟩ : syracuseStep 1425215 = 2137823) B2137823
theorem B1425721 : Blo 842353 1425721 := bstep (se 2 (by rfl) ⟨534645, by rfl⟩ : syracuseStep 1425721 = 1069291) B1069291
theorem B9618425 : Blo 842353 9618425 := bstep (se 2 (by rfl) ⟨3606909, by rfl⟩ : syracuseStep 9618425 = 7213819) B7213819
theorem B2409983 : Blo 842353 2409983 := bstep (se 1 (by rfl) ⟨1807487, by rfl⟩ : syracuseStep 2409983 = 3614975) B3614975
theorem B1427017 : Blo 842353 1427017 := bstep (se 2 (by rfl) ⟨535131, by rfl⟩ : syracuseStep 1427017 = 1070263) B1070263
theorem B12176669 : Blo 842353 12176669 := bstep (se 3 (by rfl) ⟨2283125, by rfl⟩ : syracuseStep 12176669 = 4566251) B4566251
theorem B55464227 : Blo 842353 55464227 := bstep (se 1 (by rfl) ⟨41598170, by rfl⟩ : syracuseStep 55464227 = 83196341) B83196341
theorem B843515 : Blo 842353 843515 := bstep (se 1 (by rfl) ⟨632636, by rfl⟩ : syracuseStep 843515 = 1265273) B1265273
theorem B6250807 : Blo 842353 6250807 := bstep (se 1 (by rfl) ⟨4688105, by rfl⟩ : syracuseStep 6250807 = 9376211) B9376211
theorem B846271 : Blo 842353 846271 := bstep (se 1 (by rfl) ⟨634703, by rfl⟩ : syracuseStep 846271 = 1269407) B1269407
theorem B2845313 : Blo 842353 2845313 := bstep (se 2 (by rfl) ⟨1066992, by rfl⟩ : syracuseStep 2845313 = 2133985) B2133985
theorem B9628631 : Blo 842353 9628631 := bstep (se 1 (by rfl) ⟨7221473, by rfl⟩ : syracuseStep 9628631 = 14442947) B14442947
theorem B18280403 : Blo 842353 18280403 := bstep (se 1 (by rfl) ⟨13710302, by rfl⟩ : syracuseStep 18280403 = 27420605) B27420605
theorem B2847419 : Blo 842353 2847419 := bstep (se 1 (by rfl) ⟨2135564, by rfl⟩ : syracuseStep 2847419 = 4271129) B4271129
theorem B1897451 : Blo 842353 1897451 := bstep (se 1 (by rfl) ⟨1423088, by rfl⟩ : syracuseStep 1897451 = 2846177) B2846177
theorem B3208967 : Blo 842353 3208967 := bstep (se 1 (by rfl) ⟨2406725, by rfl⟩ : syracuseStep 3208967 = 4813451) B4813451
theorem B1898783 : Blo 842353 1898783 := bstep (se 1 (by rfl) ⟨1424087, by rfl⟩ : syracuseStep 1898783 = 2848175) B2848175
theorem B12648271 : Blo 842353 12648271 := bstep (se 1 (by rfl) ⟨9486203, by rfl⟩ : syracuseStep 12648271 = 18972407) B18972407
theorem B1900961 : Blo 842353 1900961 := bstep (se 2 (by rfl) ⟨712860, by rfl⟩ : syracuseStep 1900961 = 1425721) B1425721
theorem B1606655 : Blo 842353 1606655 := bstep (se 1 (by rfl) ⟨1204991, by rfl⟩ : syracuseStep 1606655 = 2409983) B2409983
theorem B1902689 : Blo 842353 1902689 := bstep (se 2 (by rfl) ⟨713508, by rfl⟩ : syracuseStep 1902689 = 1427017) B1427017
theorem B20844067 : Blo 842353 20844067 := bstep (se 1 (by rfl) ⟨15633050, by rfl⟩ : syracuseStep 20844067 = 31266101) B31266101
theorem B16228633 : Blo 842353 16228633 := bstep (se 2 (by rfl) ⟨6085737, by rfl⟩ : syracuseStep 16228633 = 12171475) B12171475
theorem B2139311 : Blo 842353 2139311 := bstep (se 1 (by rfl) ⟨1604483, by rfl⟩ : syracuseStep 2139311 = 3208967) B3208967
theorem B6073055 : Blo 842353 6073055 := bstep (se 1 (by rfl) ⟨4554791, by rfl⟩ : syracuseStep 6073055 = 9109583) B9109583
theorem B8334409 : Blo 842353 8334409 := bstep (se 2 (by rfl) ⟨3125403, by rfl⟩ : syracuseStep 8334409 = 6250807) B6250807
theorem B36976151 : Blo 842353 36976151 := bstep (se 1 (by rfl) ⟨27732113, by rfl⟩ : syracuseStep 36976151 = 55464227) B55464227
theorem B3853597 : Blo 842353 3853597 := bstep (se 3 (by rfl) ⟨722549, by rfl⟩ : syracuseStep 3853597 = 1445099) B1445099
theorem B1264967 : Blo 842353 1264967 := bstep (se 1 (by rfl) ⟨948725, by rfl⟩ : syracuseStep 1264967 = 1897451) B1897451
theorem B77910083 : Blo 842353 77910083 := bstep (se 1 (by rfl) ⟨58432562, by rfl⟩ : syracuseStep 77910083 = 116865125) B116865125
theorem B1265855 : Blo 842353 1265855 := bstep (se 1 (by rfl) ⟨949391, by rfl⟩ : syracuseStep 1265855 = 1898783) B1898783
theorem B16864361 : Blo 842353 16864361 := bstep (se 2 (by rfl) ⟨6324135, by rfl⟩ : syracuseStep 16864361 = 12648271) B12648271
theorem B6412283 : Blo 842353 6412283 := bstep (se 1 (by rfl) ⟨4809212, by rfl⟩ : syracuseStep 6412283 = 9618425) B9618425
theorem B8117779 : Blo 842353 8117779 := bstep (se 1 (by rfl) ⟨6088334, by rfl⟩ : syracuseStep 8117779 = 12176669) B12176669
theorem B9134491 : Blo 842353 9134491 := bstep (se 1 (by rfl) ⟨6850868, by rfl⟩ : syracuseStep 9134491 = 13701737) B13701737
theorem B3598505 : Blo 842353 3598505 := bstep (se 2 (by rfl) ⟨1349439, by rfl⟩ : syracuseStep 3598505 = 2698879) B2698879
theorem B1600231 : Blo 842353 1600231 := bstep (se 1 (by rfl) ⟨1200173, by rfl⟩ : syracuseStep 1600231 = 2400347) B2400347
theorem B48656375 : Blo 842353 48656375 := bstep (se 1 (by rfl) ⟨36492281, by rfl⟩ : syracuseStep 48656375 = 72984563) B72984563
theorem B1896875 : Blo 842353 1896875 := bstep (se 1 (by rfl) ⟨1422656, by rfl⟩ : syracuseStep 1896875 = 2845313) B2845313
theorem B6419087 : Blo 842353 6419087 := bstep (se 1 (by rfl) ⟨4814315, by rfl⟩ : syracuseStep 6419087 = 9628631) B9628631
theorem B12186935 : Blo 842353 12186935 := bstep (se 1 (by rfl) ⟨9140201, by rfl⟩ : syracuseStep 12186935 = 18280403) B18280403
theorem B2848283 : Blo 842353 2848283 := bstep (se 1 (by rfl) ⟨2136212, by rfl⟩ : syracuseStep 2848283 = 4272425) B4272425
theorem B1898279 : Blo 842353 1898279 := bstep (se 1 (by rfl) ⟨1423709, by rfl⟩ : syracuseStep 1898279 = 2847419) B2847419
theorem B3602657 : Blo 842353 3602657 := bstep (se 2 (by rfl) ⟨1350996, by rfl⟩ : syracuseStep 3602657 = 2701993) B2701993
theorem B949243 : Blo 842353 949243 := bstep (se 1 (by rfl) ⟨711932, by rfl⟩ : syracuseStep 949243 = 1423865) B1423865
theorem B950143 : Blo 842353 950143 := bstep (se 1 (by rfl) ⟨712607, by rfl⟩ : syracuseStep 950143 = 1425215) B1425215
theorem B51940055 : Blo 842353 51940055 := bstep (se 1 (by rfl) ⟨38955041, by rfl⟩ : syracuseStep 51940055 = 77910083) B77910083
theorem B11242907 : Blo 842353 11242907 := bstep (se 1 (by rfl) ⟨8432180, by rfl⟩ : syracuseStep 11242907 = 16864361) B16864361
theorem B2133641 : Blo 842353 2133641 := bstep (se 2 (by rfl) ⟨800115, by rfl⟩ : syracuseStep 2133641 = 1600231) B1600231
theorem B11112545 : Blo 842353 11112545 := bstep (se 2 (by rfl) ⟨4167204, by rfl⟩ : syracuseStep 11112545 = 8334409) B8334409
theorem B27792089 : Blo 842353 27792089 := bstep (se 2 (by rfl) ⟨10422033, by rfl⟩ : syracuseStep 27792089 = 20844067) B20844067
theorem B2399003 : Blo 842353 2399003 := bstep (se 1 (by rfl) ⟨1799252, by rfl⟩ : syracuseStep 2399003 = 3598505) B3598505
theorem B24650767 : Blo 842353 24650767 := bstep (se 1 (by rfl) ⟨18488075, by rfl⟩ : syracuseStep 24650767 = 36976151) B36976151
theorem B2401771 : Blo 842353 2401771 := bstep (se 1 (by rfl) ⟨1801328, by rfl⟩ : syracuseStep 2401771 = 3602657) B3602657
theorem B10823705 : Blo 842353 10823705 := bstep (se 2 (by rfl) ⟨4058889, by rfl⟩ : syracuseStep 10823705 = 8117779) B8117779
theorem B21638177 : Blo 842353 21638177 := bstep (se 2 (by rfl) ⟨8114316, by rfl⟩ : syracuseStep 21638177 = 16228633) B16228633
theorem B4274855 : Blo 842353 4274855 := bstep (se 1 (by rfl) ⟨3206141, by rfl⟩ : syracuseStep 4274855 = 6412283) B6412283
theorem B1426207 : Blo 842353 1426207 := bstep (se 1 (by rfl) ⟨1069655, by rfl⟩ : syracuseStep 1426207 = 2139311) B2139311
theorem B4048703 : Blo 842353 4048703 := bstep (se 1 (by rfl) ⟨3036527, by rfl⟩ : syracuseStep 4048703 = 6073055) B6073055
theorem B1264583 : Blo 842353 1264583 := bstep (se 1 (by rfl) ⟨948437, by rfl⟩ : syracuseStep 1264583 = 1896875) B1896875
theorem B4279391 : Blo 842353 4279391 := bstep (se 1 (by rfl) ⟨3209543, by rfl⟩ : syracuseStep 4279391 = 6419087) B6419087
theorem B1265519 : Blo 842353 1265519 := bstep (se 1 (by rfl) ⟨949139, by rfl⟩ : syracuseStep 1265519 = 1898279) B1898279
theorem B1265657 : Blo 842353 1265657 := bstep (se 2 (by rfl) ⟨474621, by rfl⟩ : syracuseStep 1265657 = 949243) B949243
theorem B1266857 : Blo 842353 1266857 := bstep (se 2 (by rfl) ⟨475071, by rfl⟩ : syracuseStep 1266857 = 950143) B950143
theorem B1267307 : Blo 842353 1267307 := bstep (se 1 (by rfl) ⟨950480, by rfl⟩ : syracuseStep 1267307 = 1900961) B1900961
theorem B12179321 : Blo 842353 12179321 := bstep (se 2 (by rfl) ⟨4567245, by rfl⟩ : syracuseStep 12179321 = 9134491) B9134491
theorem B1268459 : Blo 842353 1268459 := bstep (se 1 (by rfl) ⟨951344, by rfl⟩ : syracuseStep 1268459 = 1902689) B1902689
theorem B843311 : Blo 842353 843311 := bstep (se 1 (by rfl) ⟨632483, by rfl⟩ : syracuseStep 843311 = 1264967) B1264967
theorem B4284413 : Blo 842353 4284413 := bstep (se 3 (by rfl) ⟨803327, by rfl⟩ : syracuseStep 4284413 = 1606655) B1606655
theorem B843903 : Blo 842353 843903 := bstep (se 1 (by rfl) ⟨632927, by rfl⟩ : syracuseStep 843903 = 1265855) B1265855
theorem B5138129 : Blo 842353 5138129 := bstep (se 2 (by rfl) ⟨1926798, by rfl⟩ : syracuseStep 5138129 = 3853597) B3853597
theorem B32437583 : Blo 842353 32437583 := bstep (se 1 (by rfl) ⟨24328187, by rfl⟩ : syracuseStep 32437583 = 48656375) B48656375
theorem B8124623 : Blo 842353 8124623 := bstep (se 1 (by rfl) ⟨6093467, by rfl⟩ : syracuseStep 8124623 = 12186935) B12186935
theorem B1898855 : Blo 842353 1898855 := bstep (se 1 (by rfl) ⟨1424141, by rfl⟩ : syracuseStep 1898855 = 2848283) B2848283
theorem B1901609 : Blo 842353 1901609 := bstep (se 2 (by rfl) ⟨713103, by rfl⟩ : syracuseStep 1901609 = 1426207) B1426207
theorem B32867689 : Blo 842353 32867689 := bstep (se 2 (by rfl) ⟨12325383, by rfl⟩ : syracuseStep 32867689 = 24650767) B24650767
theorem B2852927 : Blo 842353 2852927 := bstep (se 1 (by rfl) ⟨2139695, by rfl⟩ : syracuseStep 2852927 = 4279391) B4279391
theorem B7408363 : Blo 842353 7408363 := bstep (se 1 (by rfl) ⟨5556272, by rfl⟩ : syracuseStep 7408363 = 11112545) B11112545
theorem B2856275 : Blo 842353 2856275 := bstep (se 1 (by rfl) ⟨2142206, by rfl⟩ : syracuseStep 2856275 = 4284413) B4284413
theorem B7215803 : Blo 842353 7215803 := bstep (se 1 (by rfl) ⟨5411852, by rfl⟩ : syracuseStep 7215803 = 10823705) B10823705
theorem B14425451 : Blo 842353 14425451 := bstep (se 1 (by rfl) ⟨10819088, by rfl⟩ : syracuseStep 14425451 = 21638177) B21638177
theorem B5416415 : Blo 842353 5416415 := bstep (se 1 (by rfl) ⟨4062311, by rfl⟩ : syracuseStep 5416415 = 8124623) B8124623
theorem B2699135 : Blo 842353 2699135 := bstep (se 1 (by rfl) ⟨2024351, by rfl⟩ : syracuseStep 2699135 = 4048703) B4048703
theorem B1422427 : Blo 842353 1422427 := bstep (se 1 (by rfl) ⟨1066820, by rfl⟩ : syracuseStep 1422427 = 2133641) B2133641
theorem B18528059 : Blo 842353 18528059 := bstep (se 1 (by rfl) ⟨13896044, by rfl⟩ : syracuseStep 18528059 = 27792089) B27792089
theorem B3425419 : Blo 842353 3425419 := bstep (se 1 (by rfl) ⟨2569064, by rfl⟩ : syracuseStep 3425419 = 5138129) B5138129
theorem B1265903 : Blo 842353 1265903 := bstep (se 1 (by rfl) ⟨949427, by rfl⟩ : syracuseStep 1265903 = 1898855) B1898855
theorem B34626703 : Blo 842353 34626703 := bstep (se 1 (by rfl) ⟨25970027, by rfl⟩ : syracuseStep 34626703 = 51940055) B51940055
theorem B843055 : Blo 842353 843055 := bstep (se 1 (by rfl) ⟨632291, by rfl⟩ : syracuseStep 843055 = 1264583) B1264583
theorem B3202361 : Blo 842353 3202361 := bstep (se 2 (by rfl) ⟨1200885, by rfl⟩ : syracuseStep 3202361 = 2401771) B2401771
theorem B7495271 : Blo 842353 7495271 := bstep (se 1 (by rfl) ⟨5621453, by rfl⟩ : syracuseStep 7495271 = 11242907) B11242907
theorem B843679 : Blo 842353 843679 := bstep (se 1 (by rfl) ⟨632759, by rfl⟩ : syracuseStep 843679 = 1265519) B1265519
theorem B843771 : Blo 842353 843771 := bstep (se 1 (by rfl) ⟨632828, by rfl⟩ : syracuseStep 843771 = 1265657) B1265657
theorem B844571 : Blo 842353 844571 := bstep (se 1 (by rfl) ⟨633428, by rfl⟩ : syracuseStep 844571 = 1266857) B1266857
theorem B844871 : Blo 842353 844871 := bstep (se 1 (by rfl) ⟨633653, by rfl⟩ : syracuseStep 844871 = 1267307) B1267307
theorem B8119547 : Blo 842353 8119547 := bstep (se 1 (by rfl) ⟨6089660, by rfl⟩ : syracuseStep 8119547 = 12179321) B12179321
theorem B845639 : Blo 842353 845639 := bstep (se 1 (by rfl) ⟨634229, by rfl⟩ : syracuseStep 845639 = 1268459) B1268459
theorem B1599335 : Blo 842353 1599335 := bstep (se 1 (by rfl) ⟨1199501, by rfl⟩ : syracuseStep 1599335 = 2399003) B2399003
theorem B21625055 : Blo 842353 21625055 := bstep (se 1 (by rfl) ⟨16218791, by rfl⟩ : syracuseStep 21625055 = 32437583) B32437583
theorem B2849903 : Blo 842353 2849903 := bstep (se 1 (by rfl) ⟨2137427, by rfl⟩ : syracuseStep 2849903 = 4274855) B4274855
theorem B1901951 : Blo 842353 1901951 := bstep (se 1 (by rfl) ⟨1426463, by rfl⟩ : syracuseStep 1901951 = 2852927) B2852927
theorem B1904183 : Blo 842353 1904183 := bstep (se 1 (by rfl) ⟨1428137, by rfl⟩ : syracuseStep 1904183 = 2856275) B2856275
theorem B2134907 : Blo 842353 2134907 := bstep (se 1 (by rfl) ⟨1601180, by rfl⟩ : syracuseStep 2134907 = 3202361) B3202361
theorem B5413031 : Blo 842353 5413031 := bstep (se 1 (by rfl) ⟨4059773, by rfl⟩ : syracuseStep 5413031 = 8119547) B8119547
theorem B3610943 : Blo 842353 3610943 := bstep (se 1 (by rfl) ⟨2708207, by rfl⟩ : syracuseStep 3610943 = 5416415) B5416415
theorem B43823585 : Blo 842353 43823585 := bstep (se 2 (by rfl) ⟨16433844, by rfl⟩ : syracuseStep 43823585 = 32867689) B32867689
theorem B9877817 : Blo 842353 9877817 := bstep (se 2 (by rfl) ⟨3704181, by rfl⟩ : syracuseStep 9877817 = 7408363) B7408363
theorem B9616967 : Blo 842353 9616967 := bstep (se 1 (by rfl) ⟨7212725, by rfl⟩ : syracuseStep 9616967 = 14425451) B14425451
theorem B4996847 : Blo 842353 4996847 := bstep (se 1 (by rfl) ⟨3747635, by rfl⟩ : syracuseStep 4996847 = 7495271) B7495271
theorem B18268901 : Blo 842353 18268901 := bstep (se 4 (by rfl) ⟨1712709, by rfl⟩ : syracuseStep 18268901 = 3425419) B3425419
theorem B1066223 : Blo 842353 1066223 := bstep (se 1 (by rfl) ⟨799667, by rfl⟩ : syracuseStep 1066223 = 1599335) B1599335
theorem B1267739 : Blo 842353 1267739 := bstep (se 1 (by rfl) ⟨950804, by rfl⟩ : syracuseStep 1267739 = 1901609) B1901609
theorem B843935 : Blo 842353 843935 := bstep (se 1 (by rfl) ⟨632951, by rfl⟩ : syracuseStep 843935 = 1265903) B1265903
theorem B4810535 : Blo 842353 4810535 := bstep (se 1 (by rfl) ⟨3607901, by rfl⟩ : syracuseStep 4810535 = 7215803) B7215803
theorem B49408157 : Blo 842353 49408157 := bstep (se 3 (by rfl) ⟨9264029, by rfl⟩ : syracuseStep 49408157 = 18528059) B18528059
theorem B1896569 : Blo 842353 1896569 := bstep (se 2 (by rfl) ⟨711213, by rfl⟩ : syracuseStep 1896569 = 1422427) B1422427
theorem B1799423 : Blo 842353 1799423 := bstep (se 1 (by rfl) ⟨1349567, by rfl⟩ : syracuseStep 1799423 = 2699135) B2699135
theorem B14416703 : Blo 842353 14416703 := bstep (se 1 (by rfl) ⟨10812527, by rfl⟩ : syracuseStep 14416703 = 21625055) B21625055
theorem B46168937 : Blo 842353 46168937 := bstep (se 2 (by rfl) ⟨17313351, by rfl⟩ : syracuseStep 46168937 = 34626703) B34626703
theorem B1899935 : Blo 842353 1899935 := bstep (se 1 (by rfl) ⟨1424951, by rfl⟩ : syracuseStep 1899935 = 2849903) B2849903
theorem B3608687 : Blo 842353 3608687 := bstep (se 1 (by rfl) ⟨2706515, by rfl⟩ : syracuseStep 3608687 = 5413031) B5413031
theorem B9611135 : Blo 842353 9611135 := bstep (se 1 (by rfl) ⟨7208351, by rfl⟩ : syracuseStep 9611135 = 14416703) B14416703
theorem B30779291 : Blo 842353 30779291 := bstep (se 1 (by rfl) ⟨23084468, by rfl⟩ : syracuseStep 30779291 = 46168937) B46168937
theorem B1423271 : Blo 842353 1423271 := bstep (se 1 (by rfl) ⟨1067453, by rfl⟩ : syracuseStep 1423271 = 2134907) B2134907
theorem B2407295 : Blo 842353 2407295 := bstep (se 1 (by rfl) ⟨1805471, by rfl⟩ : syracuseStep 2407295 = 3610943) B3610943
theorem B1264379 : Blo 842353 1264379 := bstep (se 1 (by rfl) ⟨948284, by rfl⟩ : syracuseStep 1264379 = 1896569) B1896569
theorem B29215723 : Blo 842353 29215723 := bstep (se 1 (by rfl) ⟨21911792, by rfl⟩ : syracuseStep 29215723 = 43823585) B43823585
theorem B1199615 : Blo 842353 1199615 := bstep (se 1 (by rfl) ⟨899711, by rfl⟩ : syracuseStep 1199615 = 1799423) B1799423
theorem B13324925 : Blo 842353 13324925 := bstep (se 3 (by rfl) ⟨2498423, by rfl⟩ : syracuseStep 13324925 = 4996847) B4996847
theorem B1266623 : Blo 842353 1266623 := bstep (se 1 (by rfl) ⟨949967, by rfl⟩ : syracuseStep 1266623 = 1899935) B1899935
theorem B6411311 : Blo 842353 6411311 := bstep (se 1 (by rfl) ⟨4808483, by rfl⟩ : syracuseStep 6411311 = 9616967) B9616967
theorem B12179267 : Blo 842353 12179267 := bstep (se 1 (by rfl) ⟨9134450, by rfl⟩ : syracuseStep 12179267 = 18268901) B18268901
theorem B1267967 : Blo 842353 1267967 := bstep (se 1 (by rfl) ⟨950975, by rfl⟩ : syracuseStep 1267967 = 1901951) B1901951
theorem B1269455 : Blo 842353 1269455 := bstep (se 1 (by rfl) ⟨952091, by rfl⟩ : syracuseStep 1269455 = 1904183) B1904183
theorem B2843261 : Blo 842353 2843261 := bstep (se 3 (by rfl) ⟨533111, by rfl⟩ : syracuseStep 2843261 = 1066223) B1066223
theorem B845159 : Blo 842353 845159 := bstep (se 1 (by rfl) ⟨633869, by rfl⟩ : syracuseStep 845159 = 1267739) B1267739
theorem B131755085 : Blo 842353 131755085 := bstep (se 3 (by rfl) ⟨24704078, by rfl⟩ : syracuseStep 131755085 = 49408157) B49408157
theorem B3207023 : Blo 842353 3207023 := bstep (se 1 (by rfl) ⟨2405267, by rfl⟩ : syracuseStep 3207023 = 4810535) B4810535
theorem B6585211 : Blo 842353 6585211 := bstep (se 1 (by rfl) ⟨4938908, by rfl⟩ : syracuseStep 6585211 = 9877817) B9877817
theorem B8883283 : Blo 842353 8883283 := bstep (se 1 (by rfl) ⟨6662462, by rfl⟩ : syracuseStep 8883283 = 13324925) B13324925
theorem B20519527 : Blo 842353 20519527 := bstep (se 1 (by rfl) ⟨15389645, by rfl⟩ : syracuseStep 20519527 = 30779291) B30779291
theorem B2138015 : Blo 842353 2138015 := bstep (se 1 (by rfl) ⟨1603511, by rfl⟩ : syracuseStep 2138015 = 3207023) B3207023
theorem B2405791 : Blo 842353 2405791 := bstep (se 1 (by rfl) ⟨1804343, by rfl⟩ : syracuseStep 2405791 = 3608687) B3608687
theorem B4274207 : Blo 842353 4274207 := bstep (se 1 (by rfl) ⟨3205655, by rfl⟩ : syracuseStep 4274207 = 6411311) B6411311
theorem B6407423 : Blo 842353 6407423 := bstep (se 1 (by rfl) ⟨4805567, by rfl⟩ : syracuseStep 6407423 = 9611135) B9611135
theorem B87836723 : Blo 842353 87836723 := bstep (se 1 (by rfl) ⟨65877542, by rfl⟩ : syracuseStep 87836723 = 131755085) B131755085
theorem B3198973 : Blo 842353 3198973 := bstep (se 3 (by rfl) ⟨599807, by rfl⟩ : syracuseStep 3198973 = 1199615) B1199615
theorem B842919 : Blo 842353 842919 := bstep (se 1 (by rfl) ⟨632189, by rfl⟩ : syracuseStep 842919 = 1264379) B1264379
theorem B844415 : Blo 842353 844415 := bstep (se 1 (by rfl) ⟨633311, by rfl⟩ : syracuseStep 844415 = 1266623) B1266623
theorem B8119511 : Blo 842353 8119511 := bstep (se 1 (by rfl) ⟨6089633, by rfl⟩ : syracuseStep 8119511 = 12179267) B12179267
theorem B38954297 : Blo 842353 38954297 := bstep (se 2 (by rfl) ⟨14607861, by rfl⟩ : syracuseStep 38954297 = 29215723) B29215723
theorem B845311 : Blo 842353 845311 := bstep (se 1 (by rfl) ⟨633983, by rfl⟩ : syracuseStep 845311 = 1267967) B1267967
theorem B846303 : Blo 842353 846303 := bstep (se 1 (by rfl) ⟨634727, by rfl⟩ : syracuseStep 846303 = 1269455) B1269455
theorem B1895507 : Blo 842353 1895507 := bstep (se 1 (by rfl) ⟨1421630, by rfl⟩ : syracuseStep 1895507 = 2843261) B2843261
theorem B8780281 : Blo 842353 8780281 := bstep (se 2 (by rfl) ⟨3292605, by rfl⟩ : syracuseStep 8780281 = 6585211) B6585211
theorem B948847 : Blo 842353 948847 := bstep (se 1 (by rfl) ⟨711635, by rfl⟩ : syracuseStep 948847 = 1423271) B1423271
theorem B1604863 : Blo 842353 1604863 := bstep (se 1 (by rfl) ⟨1203647, by rfl⟩ : syracuseStep 1604863 = 2407295) B2407295
theorem B58557815 : Blo 842353 58557815 := bstep (se 1 (by rfl) ⟨43918361, by rfl⟩ : syracuseStep 58557815 = 87836723) B87836723
theorem B46828165 : Blo 842353 46828165 := bstep (se 4 (by rfl) ⟨4390140, by rfl⟩ : syracuseStep 46828165 = 8780281) B8780281
theorem B4265297 : Blo 842353 4265297 := bstep (se 2 (by rfl) ⟨1599486, by rfl⟩ : syracuseStep 4265297 = 3198973) B3198973
theorem B5413007 : Blo 842353 5413007 := bstep (se 1 (by rfl) ⟨4059755, by rfl⟩ : syracuseStep 5413007 = 8119511) B8119511
theorem B2139817 : Blo 842353 2139817 := bstep (se 2 (by rfl) ⟨802431, by rfl⟩ : syracuseStep 2139817 = 1604863) B1604863
theorem B4271615 : Blo 842353 4271615 := bstep (se 1 (by rfl) ⟨3203711, by rfl⟩ : syracuseStep 4271615 = 6407423) B6407423
theorem B11844377 : Blo 842353 11844377 := bstep (se 2 (by rfl) ⟨4441641, by rfl⟩ : syracuseStep 11844377 = 8883283) B8883283
theorem B1425343 : Blo 842353 1425343 := bstep (se 1 (by rfl) ⟨1069007, by rfl⟩ : syracuseStep 1425343 = 2138015) B2138015
theorem B25969531 : Blo 842353 25969531 := bstep (se 1 (by rfl) ⟨19477148, by rfl⟩ : syracuseStep 25969531 = 38954297) B38954297
theorem B1263671 : Blo 842353 1263671 := bstep (se 1 (by rfl) ⟨947753, by rfl⟩ : syracuseStep 1263671 = 1895507) B1895507
theorem B1265129 : Blo 842353 1265129 := bstep (se 2 (by rfl) ⟨474423, by rfl⟩ : syracuseStep 1265129 = 948847) B948847
theorem B3207721 : Blo 842353 3207721 := bstep (se 2 (by rfl) ⟨1202895, by rfl⟩ : syracuseStep 3207721 = 2405791) B2405791
theorem B27359369 : Blo 842353 27359369 := bstep (se 2 (by rfl) ⟨10259763, by rfl⟩ : syracuseStep 27359369 = 20519527) B20519527
theorem B2849471 : Blo 842353 2849471 := bstep (se 1 (by rfl) ⟨2137103, by rfl⟩ : syracuseStep 2849471 = 4274207) B4274207
theorem B2853089 : Blo 842353 2853089 := bstep (se 2 (by rfl) ⟨1069908, by rfl⟩ : syracuseStep 2853089 = 2139817) B2139817
theorem B3608671 : Blo 842353 3608671 := bstep (se 1 (by rfl) ⟨2706503, by rfl⟩ : syracuseStep 3608671 = 5413007) B5413007
theorem B39038543 : Blo 842353 39038543 := bstep (se 1 (by rfl) ⟨29278907, by rfl⟩ : syracuseStep 39038543 = 58557815) B58557815
theorem B62437553 : Blo 842353 62437553 := bstep (se 2 (by rfl) ⟨23414082, by rfl⟩ : syracuseStep 62437553 = 46828165) B46828165
theorem B4276961 : Blo 842353 4276961 := bstep (se 2 (by rfl) ⟨1603860, by rfl⟩ : syracuseStep 4276961 = 3207721) B3207721
theorem B18239579 : Blo 842353 18239579 := bstep (se 1 (by rfl) ⟨13679684, by rfl⟩ : syracuseStep 18239579 = 27359369) B27359369
theorem B34626041 : Blo 842353 34626041 := bstep (se 2 (by rfl) ⟨12984765, by rfl⟩ : syracuseStep 34626041 = 25969531) B25969531
theorem B842447 : Blo 842353 842447 := bstep (se 1 (by rfl) ⟨631835, by rfl⟩ : syracuseStep 842447 = 1263671) B1263671
theorem B843419 : Blo 842353 843419 := bstep (se 1 (by rfl) ⟨632564, by rfl⟩ : syracuseStep 843419 = 1265129) B1265129
theorem B2843531 : Blo 842353 2843531 := bstep (se 1 (by rfl) ⟨2132648, by rfl⟩ : syracuseStep 2843531 = 4265297) B4265297
theorem B2847743 : Blo 842353 2847743 := bstep (se 1 (by rfl) ⟨2135807, by rfl⟩ : syracuseStep 2847743 = 4271615) B4271615
theorem B1899647 : Blo 842353 1899647 := bstep (se 1 (by rfl) ⟨1424735, by rfl⟩ : syracuseStep 1899647 = 2849471) B2849471
theorem B7896251 : Blo 842353 7896251 := bstep (se 1 (by rfl) ⟨5922188, by rfl⟩ : syracuseStep 7896251 = 11844377) B11844377
theorem B1900457 : Blo 842353 1900457 := bstep (se 2 (by rfl) ⟨712671, by rfl⟩ : syracuseStep 1900457 = 1425343) B1425343
theorem B2851307 : Blo 842353 2851307 := bstep (se 1 (by rfl) ⟨2138480, by rfl⟩ : syracuseStep 2851307 = 4276961) B4276961
theorem B1902059 : Blo 842353 1902059 := bstep (se 1 (by rfl) ⟨1426544, by rfl⟩ : syracuseStep 1902059 = 2853089) B2853089
theorem B12159719 : Blo 842353 12159719 := bstep (se 1 (by rfl) ⟨9119789, by rfl⟩ : syracuseStep 12159719 = 18239579) B18239579
theorem B26025695 : Blo 842353 26025695 := bstep (se 1 (by rfl) ⟨19519271, by rfl⟩ : syracuseStep 26025695 = 39038543) B39038543
theorem B41625035 : Blo 842353 41625035 := bstep (se 1 (by rfl) ⟨31218776, by rfl⟩ : syracuseStep 41625035 = 62437553) B62437553
theorem B23084027 : Blo 842353 23084027 := bstep (se 1 (by rfl) ⟨17313020, by rfl⟩ : syracuseStep 23084027 = 34626041) B34626041
theorem B21056669 : Blo 842353 21056669 := bstep (se 3 (by rfl) ⟨3948125, by rfl⟩ : syracuseStep 21056669 = 7896251) B7896251
theorem B1266431 : Blo 842353 1266431 := bstep (se 1 (by rfl) ⟨949823, by rfl⟩ : syracuseStep 1266431 = 1899647) B1899647
theorem B1266971 : Blo 842353 1266971 := bstep (se 1 (by rfl) ⟨950228, by rfl⟩ : syracuseStep 1266971 = 1900457) B1900457
theorem B4811561 : Blo 842353 4811561 := bstep (se 2 (by rfl) ⟨1804335, by rfl⟩ : syracuseStep 4811561 = 3608671) B3608671
theorem B1895687 : Blo 842353 1895687 := bstep (se 1 (by rfl) ⟨1421765, by rfl⟩ : syracuseStep 1895687 = 2843531) B2843531
theorem B1898495 : Blo 842353 1898495 := bstep (se 1 (by rfl) ⟨1423871, by rfl⟩ : syracuseStep 1898495 = 2847743) B2847743
theorem B1900871 : Blo 842353 1900871 := bstep (se 1 (by rfl) ⟨1425653, by rfl⟩ : syracuseStep 1900871 = 2851307) B2851307
theorem B8106479 : Blo 842353 8106479 := bstep (se 1 (by rfl) ⟨6079859, by rfl⟩ : syracuseStep 8106479 = 12159719) B12159719
theorem B14037779 : Blo 842353 14037779 := bstep (se 1 (by rfl) ⟨10528334, by rfl⟩ : syracuseStep 14037779 = 21056669) B21056669
theorem B17350463 : Blo 842353 17350463 := bstep (se 1 (by rfl) ⟨13012847, by rfl⟩ : syracuseStep 17350463 = 26025695) B26025695
theorem B1263791 : Blo 842353 1263791 := bstep (se 1 (by rfl) ⟨947843, by rfl⟩ : syracuseStep 1263791 = 1895687) B1895687
theorem B1265663 : Blo 842353 1265663 := bstep (se 1 (by rfl) ⟨949247, by rfl⟩ : syracuseStep 1265663 = 1898495) B1898495
theorem B15389351 : Blo 842353 15389351 := bstep (se 1 (by rfl) ⟨11542013, by rfl⟩ : syracuseStep 15389351 = 23084027) B23084027
theorem B1268039 : Blo 842353 1268039 := bstep (se 1 (by rfl) ⟨951029, by rfl⟩ : syracuseStep 1268039 = 1902059) B1902059
theorem B844287 : Blo 842353 844287 := bstep (se 1 (by rfl) ⟨633215, by rfl⟩ : syracuseStep 844287 = 1266431) B1266431
theorem B844647 : Blo 842353 844647 := bstep (se 1 (by rfl) ⟨633485, by rfl⟩ : syracuseStep 844647 = 1266971) B1266971
theorem B27750023 : Blo 842353 27750023 := bstep (se 1 (by rfl) ⟨20812517, by rfl⟩ : syracuseStep 27750023 = 41625035) B41625035
theorem B3207707 : Blo 842353 3207707 := bstep (se 1 (by rfl) ⟨2405780, by rfl⟩ : syracuseStep 3207707 = 4811561) B4811561
theorem B10259567 : Blo 842353 10259567 := bstep (se 1 (by rfl) ⟨7694675, by rfl⟩ : syracuseStep 10259567 = 15389351) B15389351
theorem B2138471 : Blo 842353 2138471 := bstep (se 1 (by rfl) ⟨1603853, by rfl⟩ : syracuseStep 2138471 = 3207707) B3207707
theorem B18500015 : Blo 842353 18500015 := bstep (se 1 (by rfl) ⟨13875011, by rfl⟩ : syracuseStep 18500015 = 27750023) B27750023
theorem B9358519 : Blo 842353 9358519 := bstep (se 1 (by rfl) ⟨7018889, by rfl⟩ : syracuseStep 9358519 = 14037779) B14037779
theorem B1267247 : Blo 842353 1267247 := bstep (se 1 (by rfl) ⟨950435, by rfl⟩ : syracuseStep 1267247 = 1900871) B1900871
theorem B842527 : Blo 842353 842527 := bstep (se 1 (by rfl) ⟨631895, by rfl⟩ : syracuseStep 842527 = 1263791) B1263791
theorem B843775 : Blo 842353 843775 := bstep (se 1 (by rfl) ⟨632831, by rfl⟩ : syracuseStep 843775 = 1265663) B1265663
theorem B845359 : Blo 842353 845359 := bstep (se 1 (by rfl) ⟨634019, by rfl⟩ : syracuseStep 845359 = 1268039) B1268039
theorem B5404319 : Blo 842353 5404319 := bstep (se 1 (by rfl) ⟨4053239, by rfl⟩ : syracuseStep 5404319 = 8106479) B8106479
theorem B11566975 : Blo 842353 11566975 := bstep (se 1 (by rfl) ⟨8675231, by rfl⟩ : syracuseStep 11566975 = 17350463) B17350463
theorem B12333343 : Blo 842353 12333343 := bstep (se 1 (by rfl) ⟨9250007, by rfl⟩ : syracuseStep 12333343 = 18500015) B18500015
theorem B1425647 : Blo 842353 1425647 := bstep (se 1 (by rfl) ⟨1069235, by rfl⟩ : syracuseStep 1425647 = 2138471) B2138471
theorem B15422633 : Blo 842353 15422633 := bstep (se 2 (by rfl) ⟨5783487, by rfl⟩ : syracuseStep 15422633 = 11566975) B11566975
theorem B6839711 : Blo 842353 6839711 := bstep (se 1 (by rfl) ⟨5129783, by rfl⟩ : syracuseStep 6839711 = 10259567) B10259567
theorem B844831 : Blo 842353 844831 := bstep (se 1 (by rfl) ⟨633623, by rfl⟩ : syracuseStep 844831 = 1267247) B1267247
theorem B12478025 : Blo 842353 12478025 := bstep (se 2 (by rfl) ⟨4679259, by rfl⟩ : syracuseStep 12478025 = 9358519) B9358519
theorem B3602879 : Blo 842353 3602879 := bstep (se 1 (by rfl) ⟨2702159, by rfl⟩ : syracuseStep 3602879 = 5404319) B5404319
theorem B950431 : Blo 842353 950431 := bstep (se 1 (by rfl) ⟨712823, by rfl⟩ : syracuseStep 950431 = 1425647) B1425647
theorem B4559807 : Blo 842353 4559807 := bstep (se 1 (by rfl) ⟨3419855, by rfl⟩ : syracuseStep 4559807 = 6839711) B6839711
theorem B2401919 : Blo 842353 2401919 := bstep (se 1 (by rfl) ⟨1801439, by rfl⟩ : syracuseStep 2401919 = 3602879) B3602879
theorem B10281755 : Blo 842353 10281755 := bstep (se 1 (by rfl) ⟨7711316, by rfl⟩ : syracuseStep 10281755 = 15422633) B15422633
theorem B16444457 : Blo 842353 16444457 := bstep (se 2 (by rfl) ⟨6166671, by rfl⟩ : syracuseStep 16444457 = 12333343) B12333343
theorem B8318683 : Blo 842353 8318683 := bstep (se 1 (by rfl) ⟨6239012, by rfl⟩ : syracuseStep 8318683 = 12478025) B12478025
theorem B6854503 : Blo 842353 6854503 := bstep (se 1 (by rfl) ⟨5140877, by rfl⟩ : syracuseStep 6854503 = 10281755) B10281755
theorem B11091577 : Blo 842353 11091577 := bstep (se 2 (by rfl) ⟨4159341, by rfl⟩ : syracuseStep 11091577 = 8318683) B8318683
theorem B10962971 : Blo 842353 10962971 := bstep (se 1 (by rfl) ⟨8222228, by rfl⟩ : syracuseStep 10962971 = 16444457) B16444457
theorem B1267241 : Blo 842353 1267241 := bstep (se 2 (by rfl) ⟨475215, by rfl⟩ : syracuseStep 1267241 = 950431) B950431
theorem B3039871 : Blo 842353 3039871 := bstep (se 1 (by rfl) ⟨2279903, by rfl⟩ : syracuseStep 3039871 = 4559807) B4559807
theorem B1601279 : Blo 842353 1601279 := bstep (se 1 (by rfl) ⟨1200959, by rfl⟩ : syracuseStep 1601279 = 2401919) B2401919
theorem B7308647 : Blo 842353 7308647 := bstep (se 1 (by rfl) ⟨5481485, by rfl⟩ : syracuseStep 7308647 = 10962971) B10962971
theorem B14788769 : Blo 842353 14788769 := bstep (se 2 (by rfl) ⟨5545788, by rfl⟩ : syracuseStep 14788769 = 11091577) B11091577
theorem B1067519 : Blo 842353 1067519 := bstep (se 1 (by rfl) ⟨800639, by rfl⟩ : syracuseStep 1067519 = 1601279) B1601279
theorem B4053161 : Blo 842353 4053161 := bstep (se 2 (by rfl) ⟨1519935, by rfl⟩ : syracuseStep 4053161 = 3039871) B3039871
theorem B844827 : Blo 842353 844827 := bstep (se 1 (by rfl) ⟨633620, by rfl⟩ : syracuseStep 844827 = 1267241) B1267241
theorem B9139337 : Blo 842353 9139337 := bstep (se 2 (by rfl) ⟨3427251, by rfl⟩ : syracuseStep 9139337 = 6854503) B6854503
theorem B2702107 : Blo 842353 2702107 := bstep (se 1 (by rfl) ⟨2026580, by rfl⟩ : syracuseStep 2702107 = 4053161) B4053161
theorem B39436717 : Blo 842353 39436717 := bstep (se 3 (by rfl) ⟨7394384, by rfl⟩ : syracuseStep 39436717 = 14788769) B14788769
theorem B4872431 : Blo 842353 4872431 := bstep (se 1 (by rfl) ⟨3654323, by rfl⟩ : syracuseStep 4872431 = 7308647) B7308647
theorem B2846717 : Blo 842353 2846717 := bstep (se 3 (by rfl) ⟨533759, by rfl⟩ : syracuseStep 2846717 = 1067519) B1067519
theorem B6092891 : Blo 842353 6092891 := bstep (se 1 (by rfl) ⟨4569668, by rfl⟩ : syracuseStep 6092891 = 9139337) B9139337
theorem B12993149 : Blo 842353 12993149 := bstep (se 3 (by rfl) ⟨2436215, by rfl⟩ : syracuseStep 12993149 = 4872431) B4872431
theorem B52582289 : Blo 842353 52582289 := bstep (se 2 (by rfl) ⟨19718358, by rfl⟩ : syracuseStep 52582289 = 39436717) B39436717
theorem B1897811 : Blo 842353 1897811 := bstep (se 1 (by rfl) ⟨1423358, by rfl⟩ : syracuseStep 1897811 = 2846717) B2846717
theorem B3602809 : Blo 842353 3602809 := bstep (se 2 (by rfl) ⟨1351053, by rfl⟩ : syracuseStep 3602809 = 2702107) B2702107
theorem B4061927 : Blo 842353 4061927 := bstep (se 1 (by rfl) ⟨3046445, by rfl⟩ : syracuseStep 4061927 = 6092891) B6092891
theorem B140219437 : Blo 842353 140219437 := bstep (se 3 (by rfl) ⟨26291144, by rfl⟩ : syracuseStep 140219437 = 52582289) B52582289
theorem B8662099 : Blo 842353 8662099 := bstep (se 1 (by rfl) ⟨6496574, by rfl⟩ : syracuseStep 8662099 = 12993149) B12993149
theorem B4803745 : Blo 842353 4803745 := bstep (se 2 (by rfl) ⟨1801404, by rfl⟩ : syracuseStep 4803745 = 3602809) B3602809
theorem B1265207 : Blo 842353 1265207 := bstep (se 1 (by rfl) ⟨948905, by rfl⟩ : syracuseStep 1265207 = 1897811) B1897811
theorem B2707951 : Blo 842353 2707951 := bstep (se 1 (by rfl) ⟨2030963, by rfl⟩ : syracuseStep 2707951 = 4061927) B4061927
theorem B3610601 : Blo 842353 3610601 := bstep (se 2 (by rfl) ⟨1353975, by rfl⟩ : syracuseStep 3610601 = 2707951) B2707951
theorem B11549465 : Blo 842353 11549465 := bstep (se 2 (by rfl) ⟨4331049, by rfl⟩ : syracuseStep 11549465 = 8662099) B8662099
theorem B6404993 : Blo 842353 6404993 := bstep (se 2 (by rfl) ⟨2401872, by rfl⟩ : syracuseStep 6404993 = 4803745) B4803745
theorem B186959249 : Blo 842353 186959249 := bstep (se 2 (by rfl) ⟨70109718, by rfl⟩ : syracuseStep 186959249 = 140219437) B140219437
theorem B843471 : Blo 842353 843471 := bstep (se 1 (by rfl) ⟨632603, by rfl⟩ : syracuseStep 843471 = 1265207) B1265207
theorem B4269995 : Blo 842353 4269995 := bstep (se 1 (by rfl) ⟨3202496, by rfl⟩ : syracuseStep 4269995 = 6404993) B6404993
theorem B2407067 : Blo 842353 2407067 := bstep (se 1 (by rfl) ⟨1805300, by rfl⟩ : syracuseStep 2407067 = 3610601) B3610601
theorem B124639499 : Blo 842353 124639499 := bstep (se 1 (by rfl) ⟨93479624, by rfl⟩ : syracuseStep 124639499 = 186959249) B186959249
theorem B7699643 : Blo 842353 7699643 := bstep (se 1 (by rfl) ⟨5774732, by rfl⟩ : syracuseStep 7699643 = 11549465) B11549465
theorem B5133095 : Blo 842353 5133095 := bstep (se 1 (by rfl) ⟨3849821, by rfl⟩ : syracuseStep 5133095 = 7699643) B7699643
theorem B83092999 : Blo 842353 83092999 := bstep (se 1 (by rfl) ⟨62319749, by rfl⟩ : syracuseStep 83092999 = 124639499) B124639499
theorem B2846663 : Blo 842353 2846663 := bstep (se 1 (by rfl) ⟨2134997, by rfl⟩ : syracuseStep 2846663 = 4269995) B4269995
theorem B1604711 : Blo 842353 1604711 := bstep (se 1 (by rfl) ⟨1203533, by rfl⟩ : syracuseStep 1604711 = 2407067) B2407067
theorem B110790665 : Blo 842353 110790665 := bstep (se 2 (by rfl) ⟨41546499, by rfl⟩ : syracuseStep 110790665 = 83092999) B83092999
theorem B3422063 : Blo 842353 3422063 := bstep (se 1 (by rfl) ⟨2566547, by rfl⟩ : syracuseStep 3422063 = 5133095) B5133095
theorem B4279229 : Blo 842353 4279229 := bstep (se 3 (by rfl) ⟨802355, by rfl⟩ : syracuseStep 4279229 = 1604711) B1604711
theorem B1897775 : Blo 842353 1897775 := bstep (se 1 (by rfl) ⟨1423331, by rfl⟩ : syracuseStep 1897775 = 2846663) B2846663
theorem B73860443 : Blo 842353 73860443 := bstep (se 1 (by rfl) ⟨55395332, by rfl⟩ : syracuseStep 73860443 = 110790665) B110790665
theorem B2852819 : Blo 842353 2852819 := bstep (se 1 (by rfl) ⟨2139614, by rfl⟩ : syracuseStep 2852819 = 4279229) B4279229
theorem B1265183 : Blo 842353 1265183 := bstep (se 1 (by rfl) ⟨948887, by rfl⟩ : syracuseStep 1265183 = 1897775) B1897775
theorem B2281375 : Blo 842353 2281375 := bstep (se 1 (by rfl) ⟨1711031, by rfl⟩ : syracuseStep 2281375 = 3422063) B3422063
theorem B1901879 : Blo 842353 1901879 := bstep (se 1 (by rfl) ⟨1426409, by rfl⟩ : syracuseStep 1901879 = 2852819) B2852819
theorem B49240295 : Blo 842353 49240295 := bstep (se 1 (by rfl) ⟨36930221, by rfl⟩ : syracuseStep 49240295 = 73860443) B73860443
theorem B843455 : Blo 842353 843455 := bstep (se 1 (by rfl) ⟨632591, by rfl⟩ : syracuseStep 843455 = 1265183) B1265183
theorem B3041833 : Blo 842353 3041833 := bstep (se 2 (by rfl) ⟨1140687, by rfl⟩ : syracuseStep 3041833 = 2281375) B2281375
theorem B1267919 : Blo 842353 1267919 := bstep (se 1 (by rfl) ⟨950939, by rfl⟩ : syracuseStep 1267919 = 1901879) B1901879
theorem B4055777 : Blo 842353 4055777 := bstep (se 2 (by rfl) ⟨1520916, by rfl⟩ : syracuseStep 4055777 = 3041833) B3041833
theorem B32826863 : Blo 842353 32826863 := bstep (se 1 (by rfl) ⟨24620147, by rfl⟩ : syracuseStep 32826863 = 49240295) B49240295
theorem B2703851 : Blo 842353 2703851 := bstep (se 1 (by rfl) ⟨2027888, by rfl⟩ : syracuseStep 2703851 = 4055777) B4055777
theorem B845279 : Blo 842353 845279 := bstep (se 1 (by rfl) ⟨633959, by rfl⟩ : syracuseStep 845279 = 1267919) B1267919
theorem B21884575 : Blo 842353 21884575 := bstep (se 1 (by rfl) ⟨16413431, by rfl⟩ : syracuseStep 21884575 = 32826863) B32826863
theorem B1802567 : Blo 842353 1802567 := bstep (se 1 (by rfl) ⟨1351925, by rfl⟩ : syracuseStep 1802567 = 2703851) B2703851
theorem B29179433 : Blo 842353 29179433 := bstep (se 2 (by rfl) ⟨10942287, by rfl⟩ : syracuseStep 29179433 = 21884575) B21884575
theorem B19452955 : Blo 842353 19452955 := bstep (se 1 (by rfl) ⟨14589716, by rfl⟩ : syracuseStep 19452955 = 29179433) B29179433
theorem B1201711 : Blo 842353 1201711 := bstep (se 1 (by rfl) ⟨901283, by rfl⟩ : syracuseStep 1201711 = 1802567) B1802567
theorem B25937273 : Blo 842353 25937273 := bstep (se 2 (by rfl) ⟨9726477, by rfl⟩ : syracuseStep 25937273 = 19452955) B19452955
theorem B1602281 : Blo 842353 1602281 := bstep (se 2 (by rfl) ⟨600855, by rfl⟩ : syracuseStep 1602281 = 1201711) B1201711
theorem B4272749 : Blo 842353 4272749 := bstep (se 3 (by rfl) ⟨801140, by rfl⟩ : syracuseStep 4272749 = 1602281) B1602281
theorem B69166061 : Blo 842353 69166061 := bstep (se 3 (by rfl) ⟨12968636, by rfl⟩ : syracuseStep 69166061 = 25937273) B25937273
theorem B46110707 : Blo 842353 46110707 := bstep (se 1 (by rfl) ⟨34583030, by rfl⟩ : syracuseStep 46110707 = 69166061) B69166061
theorem B2848499 : Blo 842353 2848499 := bstep (se 1 (by rfl) ⟨2136374, by rfl⟩ : syracuseStep 2848499 = 4272749) B4272749
theorem B30740471 : Blo 842353 30740471 := bstep (se 1 (by rfl) ⟨23055353, by rfl⟩ : syracuseStep 30740471 = 46110707) B46110707
theorem B1898999 : Blo 842353 1898999 := bstep (se 1 (by rfl) ⟨1424249, by rfl⟩ : syracuseStep 1898999 = 2848499) B2848499
theorem B20493647 : Blo 842353 20493647 := bstep (se 1 (by rfl) ⟨15370235, by rfl⟩ : syracuseStep 20493647 = 30740471) B30740471
theorem B1265999 : Blo 842353 1265999 := bstep (se 1 (by rfl) ⟨949499, by rfl⟩ : syracuseStep 1265999 = 1898999) B1898999
theorem B843999 : Blo 842353 843999 := bstep (se 1 (by rfl) ⟨632999, by rfl⟩ : syracuseStep 843999 = 1265999) B1265999
theorem B13662431 : Blo 842353 13662431 := bstep (se 1 (by rfl) ⟨10246823, by rfl⟩ : syracuseStep 13662431 = 20493647) B20493647
theorem B9108287 : Blo 842353 9108287 := bstep (se 1 (by rfl) ⟨6831215, by rfl⟩ : syracuseStep 9108287 = 13662431) B13662431
theorem B6072191 : Blo 842353 6072191 := bstep (se 1 (by rfl) ⟨4554143, by rfl⟩ : syracuseStep 6072191 = 9108287) B9108287
theorem B4048127 : Blo 842353 4048127 := bstep (se 1 (by rfl) ⟨3036095, by rfl⟩ : syracuseStep 4048127 = 6072191) B6072191
theorem B2698751 : Blo 842353 2698751 := bstep (se 1 (by rfl) ⟨2024063, by rfl⟩ : syracuseStep 2698751 = 4048127) B4048127
theorem B1799167 : Blo 842353 1799167 := bstep (se 1 (by rfl) ⟨1349375, by rfl⟩ : syracuseStep 1799167 = 2698751) B2698751
theorem B2398889 : Blo 842353 2398889 := bstep (se 2 (by rfl) ⟨899583, by rfl⟩ : syracuseStep 2398889 = 1799167) B1799167
theorem B1599259 : Blo 842353 1599259 := bstep (se 1 (by rfl) ⟨1199444, by rfl⟩ : syracuseStep 1599259 = 2398889) B2398889
theorem B2132345 : Blo 842353 2132345 := bstep (se 2 (by rfl) ⟨799629, by rfl⟩ : syracuseStep 2132345 = 1599259) B1599259
theorem B1421563 : Blo 842353 1421563 := bstep (se 1 (by rfl) ⟨1066172, by rfl⟩ : syracuseStep 1421563 = 2132345) B2132345
theorem B1895417 : Blo 842353 1895417 := bstep (se 2 (by rfl) ⟨710781, by rfl⟩ : syracuseStep 1895417 = 1421563) B1421563
theorem B1263611 : Blo 842353 1263611 := bstep (se 1 (by rfl) ⟨947708, by rfl⟩ : syracuseStep 1263611 = 1895417) B1895417
theorem B842407 : Blo 842353 842407 := bstep (se 1 (by rfl) ⟨631805, by rfl⟩ : syracuseStep 842407 = 1263611) B1263611

theorem C0 (j : ℕ) (h1 : 210588 ≤ j) (h2 : j ≤ 211287) : Blo 842353 (4 * j + 3) := by
  interval_cases j
  · exact B842355
  · exact B842359
  · exact B842363
  · exact B842367
  · exact B842371
  · exact B842375
  · exact B842379
  · exact B842383
  · exact B842387
  · exact B842391
  · exact B842395
  · exact B842399
  · exact B842403
  · exact B842407
  · exact B842411
  · exact B842415
  · exact B842419
  · exact B842423
  · exact B842427
  · exact B842431
  · exact B842435
  · exact B842439
  · exact B842443
  · exact B842447
  · exact B842451
  · exact B842455
  · exact B842459
  · exact B842463
  · exact B842467
  · exact B842471
  · exact B842475
  · exact B842479
  · exact B842483
  · exact B842487
  · exact B842491
  · exact B842495
  · exact B842499
  · exact B842503
  · exact B842507
  · exact B842511
  · exact B842515
  · exact B842519
  · exact B842523
  · exact B842527
  · exact B842531
  · exact B842535
  · exact B842539
  · exact B842543
  · exact B842547
  · exact B842551
  · exact B842555
  · exact B842559
  · exact B842563
  · exact B842567
  · exact B842571
  · exact B842575
  · exact B842579
  · exact B842583
  · exact B842587
  · exact B842591
  · exact B842595
  · exact B842599
  · exact B842603
  · exact B842607
  · exact B842611
  · exact B842615
  · exact B842619
  · exact B842623
  · exact B842627
  · exact B842631
  · exact B842635
  · exact B842639
  · exact B842643
  · exact B842647
  · exact B842651
  · exact B842655
  · exact B842659
  · exact B842663
  · exact B842667
  · exact B842671
  · exact B842675
  · exact B842679
  · exact B842683
  · exact B842687
  · exact B842691
  · exact B842695
  · exact B842699
  · exact B842703
  · exact B842707
  · exact B842711
  · exact B842715
  · exact B842719
  · exact B842723
  · exact B842727
  · exact B842731
  · exact B842735
  · exact B842739
  · exact B842743
  · exact B842747
  · exact B842751
  · exact B842755
  · exact B842759
  · exact B842763
  · exact B842767
  · exact B842771
  · exact B842775
  · exact B842779
  · exact B842783
  · exact B842787
  · exact B842791
  · exact B842795
  · exact B842799
  · exact B842803
  · exact B842807
  · exact B842811
  · exact B842815
  · exact B842819
  · exact B842823
  · exact B842827
  · exact B842831
  · exact B842835
  · exact B842839
  · exact B842843
  · exact B842847
  · exact B842851
  · exact B842855
  · exact B842859
  · exact B842863
  · exact B842867
  · exact B842871
  · exact B842875
  · exact B842879
  · exact B842883
  · exact B842887
  · exact B842891
  · exact B842895
  · exact B842899
  · exact B842903
  · exact B842907
  · exact B842911
  · exact B842915
  · exact B842919
  · exact B842923
  · exact B842927
  · exact B842931
  · exact B842935
  · exact B842939
  · exact B842943
  · exact B842947
  · exact B842951
  · exact B842955
  · exact B842959
  · exact B842963
  · exact B842967
  · exact B842971
  · exact B842975
  · exact B842979
  · exact B842983
  · exact B842987
  · exact B842991
  · exact B842995
  · exact B842999
  · exact B843003
  · exact B843007
  · exact B843011
  · exact B843015
  · exact B843019
  · exact B843023
  · exact B843027
  · exact B843031
  · exact B843035
  · exact B843039
  · exact B843043
  · exact B843047
  · exact B843051
  · exact B843055
  · exact B843059
  · exact B843063
  · exact B843067
  · exact B843071
  · exact B843075
  · exact B843079
  · exact B843083
  · exact B843087
  · exact B843091
  · exact B843095
  · exact B843099
  · exact B843103
  · exact B843107
  · exact B843111
  · exact B843115
  · exact B843119
  · exact B843123
  · exact B843127
  · exact B843131
  · exact B843135
  · exact B843139
  · exact B843143
  · exact B843147
  · exact B843151
  · exact B843155
  · exact B843159
  · exact B843163
  · exact B843167
  · exact B843171
  · exact B843175
  · exact B843179
  · exact B843183
  · exact B843187
  · exact B843191
  · exact B843195
  · exact B843199
  · exact B843203
  · exact B843207
  · exact B843211
  · exact B843215
  · exact B843219
  · exact B843223
  · exact B843227
  · exact B843231
  · exact B843235
  · exact B843239
  · exact B843243
  · exact B843247
  · exact B843251
  · exact B843255
  · exact B843259
  · exact B843263
  · exact B843267
  · exact B843271
  · exact B843275
  · exact B843279
  · exact B843283
  · exact B843287
  · exact B843291
  · exact B843295
  · exact B843299
  · exact B843303
  · exact B843307
  · exact B843311
  · exact B843315
  · exact B843319
  · exact B843323
  · exact B843327
  · exact B843331
  · exact B843335
  · exact B843339
  · exact B843343
  · exact B843347
  · exact B843351
  · exact B843355
  · exact B843359
  · exact B843363
  · exact B843367
  · exact B843371
  · exact B843375
  · exact B843379
  · exact B843383
  · exact B843387
  · exact B843391
  · exact B843395
  · exact B843399
  · exact B843403
  · exact B843407
  · exact B843411
  · exact B843415
  · exact B843419
  · exact B843423
  · exact B843427
  · exact B843431
  · exact B843435
  · exact B843439
  · exact B843443
  · exact B843447
  · exact B843451
  · exact B843455
  · exact B843459
  · exact B843463
  · exact B843467
  · exact B843471
  · exact B843475
  · exact B843479
  · exact B843483
  · exact B843487
  · exact B843491
  · exact B843495
  · exact B843499
  · exact B843503
  · exact B843507
  · exact B843511
  · exact B843515
  · exact B843519
  · exact B843523
  · exact B843527
  · exact B843531
  · exact B843535
  · exact B843539
  · exact B843543
  · exact B843547
  · exact B843551
  · exact B843555
  · exact B843559
  · exact B843563
  · exact B843567
  · exact B843571
  · exact B843575
  · exact B843579
  · exact B843583
  · exact B843587
  · exact B843591
  · exact B843595
  · exact B843599
  · exact B843603
  · exact B843607
  · exact B843611
  · exact B843615
  · exact B843619
  · exact B843623
  · exact B843627
  · exact B843631
  · exact B843635
  · exact B843639
  · exact B843643
  · exact B843647
  · exact B843651
  · exact B843655
  · exact B843659
  · exact B843663
  · exact B843667
  · exact B843671
  · exact B843675
  · exact B843679
  · exact B843683
  · exact B843687
  · exact B843691
  · exact B843695
  · exact B843699
  · exact B843703
  · exact B843707
  · exact B843711
  · exact B843715
  · exact B843719
  · exact B843723
  · exact B843727
  · exact B843731
  · exact B843735
  · exact B843739
  · exact B843743
  · exact B843747
  · exact B843751
  · exact B843755
  · exact B843759
  · exact B843763
  · exact B843767
  · exact B843771
  · exact B843775
  · exact B843779
  · exact B843783
  · exact B843787
  · exact B843791
  · exact B843795
  · exact B843799
  · exact B843803
  · exact B843807
  · exact B843811
  · exact B843815
  · exact B843819
  · exact B843823
  · exact B843827
  · exact B843831
  · exact B843835
  · exact B843839
  · exact B843843
  · exact B843847
  · exact B843851
  · exact B843855
  · exact B843859
  · exact B843863
  · exact B843867
  · exact B843871
  · exact B843875
  · exact B843879
  · exact B843883
  · exact B843887
  · exact B843891
  · exact B843895
  · exact B843899
  · exact B843903
  · exact B843907
  · exact B843911
  · exact B843915
  · exact B843919
  · exact B843923
  · exact B843927
  · exact B843931
  · exact B843935
  · exact B843939
  · exact B843943
  · exact B843947
  · exact B843951
  · exact B843955
  · exact B843959
  · exact B843963
  · exact B843967
  · exact B843971
  · exact B843975
  · exact B843979
  · exact B843983
  · exact B843987
  · exact B843991
  · exact B843995
  · exact B843999
  · exact B844003
  · exact B844007
  · exact B844011
  · exact B844015
  · exact B844019
  · exact B844023
  · exact B844027
  · exact B844031
  · exact B844035
  · exact B844039
  · exact B844043
  · exact B844047
  · exact B844051
  · exact B844055
  · exact B844059
  · exact B844063
  · exact B844067
  · exact B844071
  · exact B844075
  · exact B844079
  · exact B844083
  · exact B844087
  · exact B844091
  · exact B844095
  · exact B844099
  · exact B844103
  · exact B844107
  · exact B844111
  · exact B844115
  · exact B844119
  · exact B844123
  · exact B844127
  · exact B844131
  · exact B844135
  · exact B844139
  · exact B844143
  · exact B844147
  · exact B844151
  · exact B844155
  · exact B844159
  · exact B844163
  · exact B844167
  · exact B844171
  · exact B844175
  · exact B844179
  · exact B844183
  · exact B844187
  · exact B844191
  · exact B844195
  · exact B844199
  · exact B844203
  · exact B844207
  · exact B844211
  · exact B844215
  · exact B844219
  · exact B844223
  · exact B844227
  · exact B844231
  · exact B844235
  · exact B844239
  · exact B844243
  · exact B844247
  · exact B844251
  · exact B844255
  · exact B844259
  · exact B844263
  · exact B844267
  · exact B844271
  · exact B844275
  · exact B844279
  · exact B844283
  · exact B844287
  · exact B844291
  · exact B844295
  · exact B844299
  · exact B844303
  · exact B844307
  · exact B844311
  · exact B844315
  · exact B844319
  · exact B844323
  · exact B844327
  · exact B844331
  · exact B844335
  · exact B844339
  · exact B844343
  · exact B844347
  · exact B844351
  · exact B844355
  · exact B844359
  · exact B844363
  · exact B844367
  · exact B844371
  · exact B844375
  · exact B844379
  · exact B844383
  · exact B844387
  · exact B844391
  · exact B844395
  · exact B844399
  · exact B844403
  · exact B844407
  · exact B844411
  · exact B844415
  · exact B844419
  · exact B844423
  · exact B844427
  · exact B844431
  · exact B844435
  · exact B844439
  · exact B844443
  · exact B844447
  · exact B844451
  · exact B844455
  · exact B844459
  · exact B844463
  · exact B844467
  · exact B844471
  · exact B844475
  · exact B844479
  · exact B844483
  · exact B844487
  · exact B844491
  · exact B844495
  · exact B844499
  · exact B844503
  · exact B844507
  · exact B844511
  · exact B844515
  · exact B844519
  · exact B844523
  · exact B844527
  · exact B844531
  · exact B844535
  · exact B844539
  · exact B844543
  · exact B844547
  · exact B844551
  · exact B844555
  · exact B844559
  · exact B844563
  · exact B844567
  · exact B844571
  · exact B844575
  · exact B844579
  · exact B844583
  · exact B844587
  · exact B844591
  · exact B844595
  · exact B844599
  · exact B844603
  · exact B844607
  · exact B844611
  · exact B844615
  · exact B844619
  · exact B844623
  · exact B844627
  · exact B844631
  · exact B844635
  · exact B844639
  · exact B844643
  · exact B844647
  · exact B844651
  · exact B844655
  · exact B844659
  · exact B844663
  · exact B844667
  · exact B844671
  · exact B844675
  · exact B844679
  · exact B844683
  · exact B844687
  · exact B844691
  · exact B844695
  · exact B844699
  · exact B844703
  · exact B844707
  · exact B844711
  · exact B844715
  · exact B844719
  · exact B844723
  · exact B844727
  · exact B844731
  · exact B844735
  · exact B844739
  · exact B844743
  · exact B844747
  · exact B844751
  · exact B844755
  · exact B844759
  · exact B844763
  · exact B844767
  · exact B844771
  · exact B844775
  · exact B844779
  · exact B844783
  · exact B844787
  · exact B844791
  · exact B844795
  · exact B844799
  · exact B844803
  · exact B844807
  · exact B844811
  · exact B844815
  · exact B844819
  · exact B844823
  · exact B844827
  · exact B844831
  · exact B844835
  · exact B844839
  · exact B844843
  · exact B844847
  · exact B844851
  · exact B844855
  · exact B844859
  · exact B844863
  · exact B844867
  · exact B844871
  · exact B844875
  · exact B844879
  · exact B844883
  · exact B844887
  · exact B844891
  · exact B844895
  · exact B844899
  · exact B844903
  · exact B844907
  · exact B844911
  · exact B844915
  · exact B844919
  · exact B844923
  · exact B844927
  · exact B844931
  · exact B844935
  · exact B844939
  · exact B844943
  · exact B844947
  · exact B844951
  · exact B844955
  · exact B844959
  · exact B844963
  · exact B844967
  · exact B844971
  · exact B844975
  · exact B844979
  · exact B844983
  · exact B844987
  · exact B844991
  · exact B844995
  · exact B844999
  · exact B845003
  · exact B845007
  · exact B845011
  · exact B845015
  · exact B845019
  · exact B845023
  · exact B845027
  · exact B845031
  · exact B845035
  · exact B845039
  · exact B845043
  · exact B845047
  · exact B845051
  · exact B845055
  · exact B845059
  · exact B845063
  · exact B845067
  · exact B845071
  · exact B845075
  · exact B845079
  · exact B845083
  · exact B845087
  · exact B845091
  · exact B845095
  · exact B845099
  · exact B845103
  · exact B845107
  · exact B845111
  · exact B845115
  · exact B845119
  · exact B845123
  · exact B845127
  · exact B845131
  · exact B845135
  · exact B845139
  · exact B845143
  · exact B845147
  · exact B845151

theorem C1 (j : ℕ) (h1 : 211288 ≤ j) (h2 : j ≤ 211587) : Blo 842353 (4 * j + 3) := by
  interval_cases j
  · exact B845155
  · exact B845159
  · exact B845163
  · exact B845167
  · exact B845171
  · exact B845175
  · exact B845179
  · exact B845183
  · exact B845187
  · exact B845191
  · exact B845195
  · exact B845199
  · exact B845203
  · exact B845207
  · exact B845211
  · exact B845215
  · exact B845219
  · exact B845223
  · exact B845227
  · exact B845231
  · exact B845235
  · exact B845239
  · exact B845243
  · exact B845247
  · exact B845251
  · exact B845255
  · exact B845259
  · exact B845263
  · exact B845267
  · exact B845271
  · exact B845275
  · exact B845279
  · exact B845283
  · exact B845287
  · exact B845291
  · exact B845295
  · exact B845299
  · exact B845303
  · exact B845307
  · exact B845311
  · exact B845315
  · exact B845319
  · exact B845323
  · exact B845327
  · exact B845331
  · exact B845335
  · exact B845339
  · exact B845343
  · exact B845347
  · exact B845351
  · exact B845355
  · exact B845359
  · exact B845363
  · exact B845367
  · exact B845371
  · exact B845375
  · exact B845379
  · exact B845383
  · exact B845387
  · exact B845391
  · exact B845395
  · exact B845399
  · exact B845403
  · exact B845407
  · exact B845411
  · exact B845415
  · exact B845419
  · exact B845423
  · exact B845427
  · exact B845431
  · exact B845435
  · exact B845439
  · exact B845443
  · exact B845447
  · exact B845451
  · exact B845455
  · exact B845459
  · exact B845463
  · exact B845467
  · exact B845471
  · exact B845475
  · exact B845479
  · exact B845483
  · exact B845487
  · exact B845491
  · exact B845495
  · exact B845499
  · exact B845503
  · exact B845507
  · exact B845511
  · exact B845515
  · exact B845519
  · exact B845523
  · exact B845527
  · exact B845531
  · exact B845535
  · exact B845539
  · exact B845543
  · exact B845547
  · exact B845551
  · exact B845555
  · exact B845559
  · exact B845563
  · exact B845567
  · exact B845571
  · exact B845575
  · exact B845579
  · exact B845583
  · exact B845587
  · exact B845591
  · exact B845595
  · exact B845599
  · exact B845603
  · exact B845607
  · exact B845611
  · exact B845615
  · exact B845619
  · exact B845623
  · exact B845627
  · exact B845631
  · exact B845635
  · exact B845639
  · exact B845643
  · exact B845647
  · exact B845651
  · exact B845655
  · exact B845659
  · exact B845663
  · exact B845667
  · exact B845671
  · exact B845675
  · exact B845679
  · exact B845683
  · exact B845687
  · exact B845691
  · exact B845695
  · exact B845699
  · exact B845703
  · exact B845707
  · exact B845711
  · exact B845715
  · exact B845719
  · exact B845723
  · exact B845727
  · exact B845731
  · exact B845735
  · exact B845739
  · exact B845743
  · exact B845747
  · exact B845751
  · exact B845755
  · exact B845759
  · exact B845763
  · exact B845767
  · exact B845771
  · exact B845775
  · exact B845779
  · exact B845783
  · exact B845787
  · exact B845791
  · exact B845795
  · exact B845799
  · exact B845803
  · exact B845807
  · exact B845811
  · exact B845815
  · exact B845819
  · exact B845823
  · exact B845827
  · exact B845831
  · exact B845835
  · exact B845839
  · exact B845843
  · exact B845847
  · exact B845851
  · exact B845855
  · exact B845859
  · exact B845863
  · exact B845867
  · exact B845871
  · exact B845875
  · exact B845879
  · exact B845883
  · exact B845887
  · exact B845891
  · exact B845895
  · exact B845899
  · exact B845903
  · exact B845907
  · exact B845911
  · exact B845915
  · exact B845919
  · exact B845923
  · exact B845927
  · exact B845931
  · exact B845935
  · exact B845939
  · exact B845943
  · exact B845947
  · exact B845951
  · exact B845955
  · exact B845959
  · exact B845963
  · exact B845967
  · exact B845971
  · exact B845975
  · exact B845979
  · exact B845983
  · exact B845987
  · exact B845991
  · exact B845995
  · exact B845999
  · exact B846003
  · exact B846007
  · exact B846011
  · exact B846015
  · exact B846019
  · exact B846023
  · exact B846027
  · exact B846031
  · exact B846035
  · exact B846039
  · exact B846043
  · exact B846047
  · exact B846051
  · exact B846055
  · exact B846059
  · exact B846063
  · exact B846067
  · exact B846071
  · exact B846075
  · exact B846079
  · exact B846083
  · exact B846087
  · exact B846091
  · exact B846095
  · exact B846099
  · exact B846103
  · exact B846107
  · exact B846111
  · exact B846115
  · exact B846119
  · exact B846123
  · exact B846127
  · exact B846131
  · exact B846135
  · exact B846139
  · exact B846143
  · exact B846147
  · exact B846151
  · exact B846155
  · exact B846159
  · exact B846163
  · exact B846167
  · exact B846171
  · exact B846175
  · exact B846179
  · exact B846183
  · exact B846187
  · exact B846191
  · exact B846195
  · exact B846199
  · exact B846203
  · exact B846207
  · exact B846211
  · exact B846215
  · exact B846219
  · exact B846223
  · exact B846227
  · exact B846231
  · exact B846235
  · exact B846239
  · exact B846243
  · exact B846247
  · exact B846251
  · exact B846255
  · exact B846259
  · exact B846263
  · exact B846267
  · exact B846271
  · exact B846275
  · exact B846279
  · exact B846283
  · exact B846287
  · exact B846291
  · exact B846295
  · exact B846299
  · exact B846303
  · exact B846307
  · exact B846311
  · exact B846315
  · exact B846319
  · exact B846323
  · exact B846327
  · exact B846331
  · exact B846335
  · exact B846339
  · exact B846343
  · exact B846347
  · exact B846351

theorem solution (m : ℕ) (hlo : 842353 ≤ m) (hhi : m ≤ 846353) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 210588 ≤ j := by omega
    have hj2 : j ≤ 211587 := by omega
    have hb : Blo 842353 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 211288 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
