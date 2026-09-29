-- Prove2me | solution 1 for syracuse_descends_range_570811_574811
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:39.389724+00:00
-- url     : https://prove2.me/submissions/cc842d63-bc8e-442d-9037-9f00d45692a0

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


theorem B917669 : Blo 570811 917669 := bbase (se 4 (by rfl) ⟨86031, by rfl⟩ : syracuseStep 917669 = 172063) (by norm_num)
theorem B1933685 : Blo 570811 1933685 := bbase (se 5 (by rfl) ⟨90641, by rfl⟩ : syracuseStep 1933685 = 181283) (by norm_num)
theorem B688709 : Blo 570811 688709 := bbase (se 4 (by rfl) ⟨64566, by rfl⟩ : syracuseStep 688709 = 129133) (by norm_num)
theorem B918125 : Blo 570811 918125 := bbase (se 3 (by rfl) ⟨172148, by rfl⟩ : syracuseStep 918125 = 344297) (by norm_num)
theorem B4358933 : Blo 570811 4358933 := bbase (se 6 (by rfl) ⟨102162, by rfl⟩ : syracuseStep 4358933 = 204325) (by norm_num)
theorem B1934117 : Blo 570811 1934117 := bbase (se 4 (by rfl) ⟨181323, by rfl⟩ : syracuseStep 1934117 = 362647) (by norm_num)
theorem B17662805 : Blo 570811 17662805 := bbase (se 9 (by rfl) ⟨51746, by rfl⟩ : syracuseStep 17662805 = 103493) (by norm_num)
theorem B1377157 : Blo 570811 1377157 := bbase (se 4 (by rfl) ⟨129108, by rfl⟩ : syracuseStep 1377157 = 258217) (by norm_num)
theorem B1835941 : Blo 570811 1835941 := bbase (se 4 (by rfl) ⟨172119, by rfl⟩ : syracuseStep 1835941 = 344239) (by norm_num)
theorem B3671189 : Blo 570811 3671189 := bbase (se 6 (by rfl) ⟨86043, by rfl⟩ : syracuseStep 3671189 = 172087) (by norm_num)
theorem B4129973 : Blo 570811 4129973 := bbase (se 5 (by rfl) ⟨193592, by rfl⟩ : syracuseStep 4129973 = 387185) (by norm_num)
theorem B4654261 : Blo 570811 4654261 := bbase (se 5 (by rfl) ⟨218168, by rfl⟩ : syracuseStep 4654261 = 436337) (by norm_num)
theorem B2786501 : Blo 570811 2786501 := bbase (se 4 (by rfl) ⟨261234, by rfl⟩ : syracuseStep 2786501 = 522469) (by norm_num)
theorem B1934549 : Blo 570811 1934549 := bbase (se 7 (by rfl) ⟨22670, by rfl⟩ : syracuseStep 1934549 = 45341) (by norm_num)
theorem B689401 : Blo 570811 689401 := bbase (se 2 (by rfl) ⟨258525, by rfl⟩ : syracuseStep 689401 = 517051) (by norm_num)
theorem B689405 : Blo 570811 689405 := bbase (se 3 (by rfl) ⟨129263, by rfl⟩ : syracuseStep 689405 = 258527) (by norm_num)
theorem B1181077 : Blo 570811 1181077 := bbase (se 6 (by rfl) ⟨27681, by rfl⟩ : syracuseStep 1181077 = 55363) (by norm_num)
theorem B1377773 : Blo 570811 1377773 := bbase (se 3 (by rfl) ⟨258332, by rfl⟩ : syracuseStep 1377773 = 516665) (by norm_num)
theorem B722449 : Blo 570811 722449 := bbase (se 2 (by rfl) ⟨270918, by rfl⟩ : syracuseStep 722449 = 541837) (by norm_num)
theorem B919117 : Blo 570811 919117 := bbase (se 3 (by rfl) ⟨172334, by rfl⟩ : syracuseStep 919117 = 344669) (by norm_num)
theorem B1934981 : Blo 570811 1934981 := bbase (se 4 (by rfl) ⟨181404, by rfl⟩ : syracuseStep 1934981 = 362809) (by norm_num)
theorem B1377965 : Blo 570811 1377965 := bbase (se 3 (by rfl) ⟨258368, by rfl⟩ : syracuseStep 1377965 = 516737) (by norm_num)
theorem B722621 : Blo 570811 722621 := bbase (se 3 (by rfl) ⟨135491, by rfl⟩ : syracuseStep 722621 = 270983) (by norm_num)
theorem B1836773 : Blo 570811 1836773 := bbase (se 4 (by rfl) ⟨172197, by rfl⟩ : syracuseStep 1836773 = 344395) (by norm_num)
theorem B689905 : Blo 570811 689905 := bbase (se 2 (by rfl) ⟨258714, by rfl⟩ : syracuseStep 689905 = 517429) (by norm_num)
theorem B722677 : Blo 570811 722677 := bbase (se 5 (by rfl) ⟨33875, by rfl⟩ : syracuseStep 722677 = 67751) (by norm_num)
theorem B1378061 : Blo 570811 1378061 := bbase (se 3 (by rfl) ⟨258386, by rfl⟩ : syracuseStep 1378061 = 516773) (by norm_num)
theorem B722773 : Blo 570811 722773 := bbase (se 9 (by rfl) ⟨2117, by rfl⟩ : syracuseStep 722773 = 4235) (by norm_num)
theorem B722945 : Blo 570811 722945 := bbase (se 2 (by rfl) ⟨271104, by rfl⟩ : syracuseStep 722945 = 542209) (by norm_num)
theorem B2066485 : Blo 570811 2066485 := bbase (se 5 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 2066485 = 193733) (by norm_num)
theorem B1935413 : Blo 570811 1935413 := bbase (se 5 (by rfl) ⟨90722, by rfl⟩ : syracuseStep 1935413 = 181445) (by norm_num)
theorem B723001 : Blo 570811 723001 := bbase (se 2 (by rfl) ⟨271125, by rfl⟩ : syracuseStep 723001 = 542251) (by norm_num)
theorem B690289 : Blo 570811 690289 := bbase (se 2 (by rfl) ⟨258858, by rfl⟩ : syracuseStep 690289 = 517717) (by norm_num)
theorem B5376149 : Blo 570811 5376149 := bbase (se 6 (by rfl) ⟨126003, by rfl⟩ : syracuseStep 5376149 = 252007) (by norm_num)
theorem B723097 : Blo 570811 723097 := bbase (se 2 (by rfl) ⟨271161, by rfl⟩ : syracuseStep 723097 = 542323) (by norm_num)
theorem B919765 : Blo 570811 919765 := bbase (se 7 (by rfl) ⟨10778, by rfl⟩ : syracuseStep 919765 = 21557) (by norm_num)
theorem B2328821 : Blo 570811 2328821 := bbase (se 5 (by rfl) ⟨109163, by rfl⟩ : syracuseStep 2328821 = 218327) (by norm_num)
theorem B10455317 : Blo 570811 10455317 := bbase (se 6 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 10455317 = 490093) (by norm_num)
theorem B4131125 : Blo 570811 4131125 := bbase (se 5 (by rfl) ⟨193646, by rfl⟩ : syracuseStep 4131125 = 387293) (by norm_num)
theorem B723269 : Blo 570811 723269 := bbase (se 4 (by rfl) ⟨67806, by rfl⟩ : syracuseStep 723269 = 135613) (by norm_num)
theorem B1083773 : Blo 570811 1083773 := bbase (se 3 (by rfl) ⟨203207, by rfl⟩ : syracuseStep 1083773 = 406415) (by norm_num)
theorem B723325 : Blo 570811 723325 := bbase (se 3 (by rfl) ⟨135623, by rfl⟩ : syracuseStep 723325 = 271247) (by norm_num)
theorem B723421 : Blo 570811 723421 := bbase (se 3 (by rfl) ⟨135641, by rfl⟩ : syracuseStep 723421 = 271283) (by norm_num)
theorem B1935845 : Blo 570811 1935845 := bbase (se 4 (by rfl) ⟨181485, by rfl⟩ : syracuseStep 1935845 = 362971) (by norm_num)
theorem B1083917 : Blo 570811 1083917 := bbase (se 3 (by rfl) ⟨203234, by rfl⟩ : syracuseStep 1083917 = 406469) (by norm_num)
theorem B723593 : Blo 570811 723593 := bbase (se 2 (by rfl) ⟨271347, by rfl⟩ : syracuseStep 723593 = 542695) (by norm_num)
theorem B723649 : Blo 570811 723649 := bbase (se 2 (by rfl) ⟨271368, by rfl⟩ : syracuseStep 723649 = 542737) (by norm_num)
theorem B723745 : Blo 570811 723745 := bbase (se 2 (by rfl) ⟨271404, by rfl⟩ : syracuseStep 723745 = 542809) (by norm_num)
theorem B1084205 : Blo 570811 1084205 := bbase (se 3 (by rfl) ⟨203288, by rfl⟩ : syracuseStep 1084205 = 406577) (by norm_num)
theorem B1936277 : Blo 570811 1936277 := bbase (se 6 (by rfl) ⟨45381, by rfl⟩ : syracuseStep 1936277 = 90763) (by norm_num)
theorem B1084357 : Blo 570811 1084357 := bbase (se 4 (by rfl) ⟨101658, by rfl⟩ : syracuseStep 1084357 = 203317) (by norm_num)
theorem B723917 : Blo 570811 723917 := bbase (se 3 (by rfl) ⟨135734, by rfl⟩ : syracuseStep 723917 = 271469) (by norm_num)
theorem B723973 : Blo 570811 723973 := bbase (se 4 (by rfl) ⟨67872, by rfl⟩ : syracuseStep 723973 = 135745) (by norm_num)
theorem B1543205 : Blo 570811 1543205 := bbase (se 4 (by rfl) ⟨144675, by rfl⟩ : syracuseStep 1543205 = 289351) (by norm_num)
theorem B1444949 : Blo 570811 1444949 := bbase (se 8 (by rfl) ⟨8466, by rfl⟩ : syracuseStep 1444949 = 16933) (by norm_num)
theorem B724069 : Blo 570811 724069 := bbase (se 4 (by rfl) ⟨67881, by rfl⟩ : syracuseStep 724069 = 135763) (by norm_num)
theorem B920693 : Blo 570811 920693 := bbase (se 5 (by rfl) ⟨43157, by rfl⟩ : syracuseStep 920693 = 86315) (by norm_num)
theorem B1084661 : Blo 570811 1084661 := bbase (se 5 (by rfl) ⟨50843, by rfl⟩ : syracuseStep 1084661 = 101687) (by norm_num)
theorem B724241 : Blo 570811 724241 := bbase (se 2 (by rfl) ⟨271590, by rfl⟩ : syracuseStep 724241 = 543181) (by norm_num)
theorem B1445141 : Blo 570811 1445141 := bbase (se 6 (by rfl) ⟨33870, by rfl⟩ : syracuseStep 1445141 = 67741) (by norm_num)
theorem B1936709 : Blo 570811 1936709 := bbase (se 4 (by rfl) ⟨181566, by rfl⟩ : syracuseStep 1936709 = 363133) (by norm_num)
theorem B724297 : Blo 570811 724297 := bbase (se 2 (by rfl) ⟨271611, by rfl⟩ : syracuseStep 724297 = 543223) (by norm_num)
theorem B724393 : Blo 570811 724393 := bbase (se 2 (by rfl) ⟨271647, by rfl⟩ : syracuseStep 724393 = 543295) (by norm_num)
theorem B1543637 : Blo 570811 1543637 := bbase (se 7 (by rfl) ⟨18089, by rfl⟩ : syracuseStep 1543637 = 36179) (by norm_num)
theorem B5213717 : Blo 570811 5213717 := bbase (se 6 (by rfl) ⟨122196, by rfl⟩ : syracuseStep 5213717 = 244393) (by norm_num)
theorem B1838645 : Blo 570811 1838645 := bbase (se 5 (by rfl) ⟨86186, by rfl⟩ : syracuseStep 1838645 = 172373) (by norm_num)
theorem B1674821 : Blo 570811 1674821 := bbase (se 4 (by rfl) ⟨157014, by rfl⟩ : syracuseStep 1674821 = 314029) (by norm_num)
theorem B724565 : Blo 570811 724565 := bbase (se 8 (by rfl) ⟨4245, by rfl⟩ : syracuseStep 724565 = 8491) (by norm_num)
theorem B1445485 : Blo 570811 1445485 := bbase (se 3 (by rfl) ⟨271028, by rfl⟩ : syracuseStep 1445485 = 542057) (by norm_num)
theorem B2330245 : Blo 570811 2330245 := bbase (se 4 (by rfl) ⟨218460, by rfl⟩ : syracuseStep 2330245 = 436921) (by norm_num)
theorem B724621 : Blo 570811 724621 := bbase (se 3 (by rfl) ⟨135866, by rfl⟩ : syracuseStep 724621 = 271733) (by norm_num)
theorem B1445597 : Blo 570811 1445597 := bbase (se 3 (by rfl) ⟨271049, by rfl⟩ : syracuseStep 1445597 = 542099) (by norm_num)
theorem B724717 : Blo 570811 724717 := bbase (se 3 (by rfl) ⟨135884, by rfl⟩ : syracuseStep 724717 = 271769) (by norm_num)
theorem B1937141 : Blo 570811 1937141 := bbase (se 5 (by rfl) ⟨90803, by rfl⟩ : syracuseStep 1937141 = 181607) (by norm_num)
theorem B35163989 : Blo 570811 35163989 := bbase (se 9 (by rfl) ⟨103019, by rfl⟩ : syracuseStep 35163989 = 206039) (by norm_num)
theorem B18550613 : Blo 570811 18550613 := bbase (se 9 (by rfl) ⟨54347, by rfl⟩ : syracuseStep 18550613 = 108695) (by norm_num)
theorem B1740677 : Blo 570811 1740677 := bbase (se 4 (by rfl) ⟨163188, by rfl⟩ : syracuseStep 1740677 = 326377) (by norm_num)
theorem B724889 : Blo 570811 724889 := bbase (se 2 (by rfl) ⟨271833, by rfl⟩ : syracuseStep 724889 = 543667) (by norm_num)
theorem B1445789 : Blo 570811 1445789 := bbase (se 3 (by rfl) ⟨271085, by rfl⟩ : syracuseStep 1445789 = 542171) (by norm_num)
theorem B724945 : Blo 570811 724945 := bbase (se 2 (by rfl) ⟨271854, by rfl⟩ : syracuseStep 724945 = 543709) (by norm_num)
theorem B1085413 : Blo 570811 1085413 := bbase (se 4 (by rfl) ⟨101757, by rfl⟩ : syracuseStep 1085413 = 203515) (by norm_num)
theorem B725041 : Blo 570811 725041 := bbase (se 2 (by rfl) ⟨271890, by rfl⟩ : syracuseStep 725041 = 543781) (by norm_num)
theorem B1085557 : Blo 570811 1085557 := bbase (se 5 (by rfl) ⟨50885, by rfl⟩ : syracuseStep 1085557 = 101771) (by norm_num)
theorem B1380493 : Blo 570811 1380493 := bbase (se 3 (by rfl) ⟨258842, by rfl⟩ : syracuseStep 1380493 = 517685) (by norm_num)
theorem B856229 : Blo 570811 856229 := bbase (se 4 (by rfl) ⟨80271, by rfl⟩ : syracuseStep 856229 = 160543) (by norm_num)
theorem B1937573 : Blo 570811 1937573 := bbase (se 4 (by rfl) ⟨181647, by rfl⟩ : syracuseStep 1937573 = 363295) (by norm_num)
theorem B856253 : Blo 570811 856253 := bbase (se 3 (by rfl) ⟨160547, by rfl⟩ : syracuseStep 856253 = 321095) (by norm_num)
theorem B856277 : Blo 570811 856277 := bbase (se 7 (by rfl) ⟨10034, by rfl⟩ : syracuseStep 856277 = 20069) (by norm_num)
theorem B725213 : Blo 570811 725213 := bbase (se 3 (by rfl) ⟨135977, by rfl⟩ : syracuseStep 725213 = 271955) (by norm_num)
theorem B856301 : Blo 570811 856301 := bbase (se 3 (by rfl) ⟨160556, by rfl⟩ : syracuseStep 856301 = 321113) (by norm_num)
theorem B1446133 : Blo 570811 1446133 := bbase (se 5 (by rfl) ⟨67787, by rfl⟩ : syracuseStep 1446133 = 135575) (by norm_num)
theorem B856325 : Blo 570811 856325 := bbase (se 4 (by rfl) ⟨80280, by rfl⟩ : syracuseStep 856325 = 160561) (by norm_num)
theorem B1085717 : Blo 570811 1085717 := bbase (se 6 (by rfl) ⟨25446, by rfl⟩ : syracuseStep 1085717 = 50893) (by norm_num)
theorem B725269 : Blo 570811 725269 := bbase (se 6 (by rfl) ⟨16998, by rfl⟩ : syracuseStep 725269 = 33997) (by norm_num)
theorem B856349 : Blo 570811 856349 := bbase (se 3 (by rfl) ⟨160565, by rfl⟩ : syracuseStep 856349 = 321131) (by norm_num)
theorem B856373 : Blo 570811 856373 := bbase (se 5 (by rfl) ⟨40142, by rfl⟩ : syracuseStep 856373 = 80285) (by norm_num)
theorem B856397 : Blo 570811 856397 := bbase (se 3 (by rfl) ⟨160574, by rfl⟩ : syracuseStep 856397 = 321149) (by norm_num)
theorem B856421 : Blo 570811 856421 := bbase (se 4 (by rfl) ⟨80289, by rfl⟩ : syracuseStep 856421 = 160579) (by norm_num)
theorem B1446245 : Blo 570811 1446245 := bbase (se 4 (by rfl) ⟨135585, by rfl⟩ : syracuseStep 1446245 = 271171) (by norm_num)
theorem B725365 : Blo 570811 725365 := bbase (se 5 (by rfl) ⟨34001, by rfl⟩ : syracuseStep 725365 = 68003) (by norm_num)
theorem B856445 : Blo 570811 856445 := bbase (se 3 (by rfl) ⟨160583, by rfl⟩ : syracuseStep 856445 = 321167) (by norm_num)
theorem B856469 : Blo 570811 856469 := bbase (se 6 (by rfl) ⟨20073, by rfl⟩ : syracuseStep 856469 = 40147) (by norm_num)
theorem B9802133 : Blo 570811 9802133 := bbase (se 6 (by rfl) ⟨229737, by rfl⟩ : syracuseStep 9802133 = 459475) (by norm_num)
theorem B1085861 : Blo 570811 1085861 := bbase (se 4 (by rfl) ⟨101799, by rfl⟩ : syracuseStep 1085861 = 203599) (by norm_num)
theorem B856493 : Blo 570811 856493 := bbase (se 3 (by rfl) ⟨160592, by rfl⟩ : syracuseStep 856493 = 321185) (by norm_num)
theorem B856517 : Blo 570811 856517 := bbase (se 4 (by rfl) ⟨80298, by rfl⟩ : syracuseStep 856517 = 160597) (by norm_num)
theorem B856541 : Blo 570811 856541 := bbase (se 3 (by rfl) ⟨160601, by rfl⟩ : syracuseStep 856541 = 321203) (by norm_num)
theorem B1380829 : Blo 570811 1380829 := bbase (se 3 (by rfl) ⟨258905, by rfl⟩ : syracuseStep 1380829 = 517811) (by norm_num)
theorem B856565 : Blo 570811 856565 := bbase (se 5 (by rfl) ⟨40151, by rfl⟩ : syracuseStep 856565 = 80303) (by norm_num)
theorem B856589 : Blo 570811 856589 := bbase (se 3 (by rfl) ⟨160610, by rfl⟩ : syracuseStep 856589 = 321221) (by norm_num)
theorem B725537 : Blo 570811 725537 := bbase (se 2 (by rfl) ⟨272076, by rfl⟩ : syracuseStep 725537 = 544153) (by norm_num)
theorem B856613 : Blo 570811 856613 := bbase (se 4 (by rfl) ⟨80307, by rfl⟩ : syracuseStep 856613 = 160615) (by norm_num)
theorem B1446437 : Blo 570811 1446437 := bbase (se 4 (by rfl) ⟨135603, by rfl⟩ : syracuseStep 1446437 = 271207) (by norm_num)
theorem B856637 : Blo 570811 856637 := bbase (se 3 (by rfl) ⟨160619, by rfl⟩ : syracuseStep 856637 = 321239) (by norm_num)
theorem B856661 : Blo 570811 856661 := bbase (se 8 (by rfl) ⟨5019, by rfl⟩ : syracuseStep 856661 = 10039) (by norm_num)
theorem B4887125 : Blo 570811 4887125 := bbase (se 8 (by rfl) ⟨28635, by rfl⟩ : syracuseStep 4887125 = 57271) (by norm_num)
theorem B1938005 : Blo 570811 1938005 := bbase (se 8 (by rfl) ⟨11355, by rfl⟩ : syracuseStep 1938005 = 22711) (by norm_num)
theorem B725593 : Blo 570811 725593 := bbase (se 2 (by rfl) ⟨272097, by rfl⟩ : syracuseStep 725593 = 544195) (by norm_num)
theorem B856685 : Blo 570811 856685 := bbase (se 3 (by rfl) ⟨160628, by rfl⟩ : syracuseStep 856685 = 321257) (by norm_num)
theorem B856709 : Blo 570811 856709 := bbase (se 4 (by rfl) ⟨80316, by rfl⟩ : syracuseStep 856709 = 160633) (by norm_num)
theorem B856733 : Blo 570811 856733 := bbase (se 3 (by rfl) ⟨160637, by rfl⟩ : syracuseStep 856733 = 321275) (by norm_num)
theorem B856757 : Blo 570811 856757 := bbase (se 5 (by rfl) ⟨40160, by rfl⟩ : syracuseStep 856757 = 80321) (by norm_num)
theorem B725689 : Blo 570811 725689 := bbase (se 2 (by rfl) ⟨272133, by rfl⟩ : syracuseStep 725689 = 544267) (by norm_num)
theorem B1086149 : Blo 570811 1086149 := bbase (se 4 (by rfl) ⟨101826, by rfl⟩ : syracuseStep 1086149 = 203653) (by norm_num)
theorem B856781 : Blo 570811 856781 := bbase (se 3 (by rfl) ⟨160646, by rfl⟩ : syracuseStep 856781 = 321293) (by norm_num)
theorem B856805 : Blo 570811 856805 := bbase (se 4 (by rfl) ⟨80325, by rfl⟩ : syracuseStep 856805 = 160651) (by norm_num)
theorem B856829 : Blo 570811 856829 := bbase (se 3 (by rfl) ⟨160655, by rfl⟩ : syracuseStep 856829 = 321311) (by norm_num)
theorem B856853 : Blo 570811 856853 := bbase (se 6 (by rfl) ⟨20082, by rfl⟩ : syracuseStep 856853 = 40165) (by norm_num)
theorem B856877 : Blo 570811 856877 := bbase (se 3 (by rfl) ⟨160664, by rfl⟩ : syracuseStep 856877 = 321329) (by norm_num)
theorem B856901 : Blo 570811 856901 := bbase (se 4 (by rfl) ⟨80334, by rfl⟩ : syracuseStep 856901 = 160669) (by norm_num)
theorem B8262485 : Blo 570811 8262485 := bbase (se 9 (by rfl) ⟨24206, by rfl⟩ : syracuseStep 8262485 = 48413) (by norm_num)
theorem B856925 : Blo 570811 856925 := bbase (se 3 (by rfl) ⟨160673, by rfl⟩ : syracuseStep 856925 = 321347) (by norm_num)
theorem B1086301 : Blo 570811 1086301 := bbase (se 3 (by rfl) ⟨203681, by rfl⟩ : syracuseStep 1086301 = 407363) (by norm_num)
theorem B725861 : Blo 570811 725861 := bbase (se 4 (by rfl) ⟨68049, by rfl⟩ : syracuseStep 725861 = 136099) (by norm_num)
theorem B856949 : Blo 570811 856949 := bbase (se 5 (by rfl) ⟨40169, by rfl⟩ : syracuseStep 856949 = 80339) (by norm_num)
theorem B1446781 : Blo 570811 1446781 := bbase (se 3 (by rfl) ⟨271271, by rfl⟩ : syracuseStep 1446781 = 542543) (by norm_num)
theorem B856973 : Blo 570811 856973 := bbase (se 3 (by rfl) ⟨160682, by rfl⟩ : syracuseStep 856973 = 321365) (by norm_num)
theorem B725917 : Blo 570811 725917 := bbase (se 3 (by rfl) ⟨136109, by rfl⟩ : syracuseStep 725917 = 272219) (by norm_num)
theorem B856997 : Blo 570811 856997 := bbase (se 4 (by rfl) ⟨80343, by rfl⟩ : syracuseStep 856997 = 160687) (by norm_num)
theorem B857021 : Blo 570811 857021 := bbase (se 3 (by rfl) ⟨160691, by rfl⟩ : syracuseStep 857021 = 321383) (by norm_num)
theorem B857045 : Blo 570811 857045 := bbase (se 7 (by rfl) ⟨10043, by rfl⟩ : syracuseStep 857045 = 20087) (by norm_num)
theorem B857069 : Blo 570811 857069 := bbase (se 3 (by rfl) ⟨160700, by rfl⟩ : syracuseStep 857069 = 321401) (by norm_num)
theorem B1446893 : Blo 570811 1446893 := bbase (se 3 (by rfl) ⟨271292, by rfl⟩ : syracuseStep 1446893 = 542585) (by norm_num)
theorem B726013 : Blo 570811 726013 := bbase (se 3 (by rfl) ⟨136127, by rfl⟩ : syracuseStep 726013 = 272255) (by norm_num)
theorem B857093 : Blo 570811 857093 := bbase (se 4 (by rfl) ⟨80352, by rfl⟩ : syracuseStep 857093 = 160705) (by norm_num)
theorem B1938437 : Blo 570811 1938437 := bbase (se 4 (by rfl) ⟨181728, by rfl⟩ : syracuseStep 1938437 = 363457) (by norm_num)
theorem B857117 : Blo 570811 857117 := bbase (se 3 (by rfl) ⟨160709, by rfl⟩ : syracuseStep 857117 = 321419) (by norm_num)
theorem B857141 : Blo 570811 857141 := bbase (se 5 (by rfl) ⟨40178, by rfl⟩ : syracuseStep 857141 = 80357) (by norm_num)
theorem B857165 : Blo 570811 857165 := bbase (se 3 (by rfl) ⟨160718, by rfl⟩ : syracuseStep 857165 = 321437) (by norm_num)
theorem B857189 : Blo 570811 857189 := bbase (se 4 (by rfl) ⟨80361, by rfl⟩ : syracuseStep 857189 = 160723) (by norm_num)
theorem B857213 : Blo 570811 857213 := bbase (se 3 (by rfl) ⟨160727, by rfl⟩ : syracuseStep 857213 = 321455) (by norm_num)
theorem B1086605 : Blo 570811 1086605 := bbase (se 3 (by rfl) ⟨203738, by rfl⟩ : syracuseStep 1086605 = 407477) (by norm_num)
theorem B857237 : Blo 570811 857237 := bbase (se 6 (by rfl) ⟨20091, by rfl⟩ : syracuseStep 857237 = 40183) (by norm_num)
theorem B726185 : Blo 570811 726185 := bbase (se 2 (by rfl) ⟨272319, by rfl⟩ : syracuseStep 726185 = 544639) (by norm_num)
theorem B857261 : Blo 570811 857261 := bbase (se 3 (by rfl) ⟨160736, by rfl⟩ : syracuseStep 857261 = 321473) (by norm_num)
theorem B1447085 : Blo 570811 1447085 := bbase (se 3 (by rfl) ⟨271328, by rfl⟩ : syracuseStep 1447085 = 542657) (by norm_num)
theorem B857285 : Blo 570811 857285 := bbase (se 4 (by rfl) ⟨80370, by rfl⟩ : syracuseStep 857285 = 160741) (by norm_num)
theorem B857309 : Blo 570811 857309 := bbase (se 3 (by rfl) ⟨160745, by rfl⟩ : syracuseStep 857309 = 321491) (by norm_num)
theorem B726241 : Blo 570811 726241 := bbase (se 2 (by rfl) ⟨272340, by rfl⟩ : syracuseStep 726241 = 544681) (by norm_num)
theorem B857333 : Blo 570811 857333 := bbase (se 5 (by rfl) ⟨40187, by rfl⟩ : syracuseStep 857333 = 80375) (by norm_num)
theorem B857357 : Blo 570811 857357 := bbase (se 3 (by rfl) ⟨160754, by rfl⟩ : syracuseStep 857357 = 321509) (by norm_num)
theorem B857381 : Blo 570811 857381 := bbase (se 4 (by rfl) ⟨80379, by rfl⟩ : syracuseStep 857381 = 160759) (by norm_num)
theorem B857405 : Blo 570811 857405 := bbase (se 3 (by rfl) ⟨160763, by rfl⟩ : syracuseStep 857405 = 321527) (by norm_num)
theorem B726337 : Blo 570811 726337 := bbase (se 2 (by rfl) ⟨272376, by rfl⟩ : syracuseStep 726337 = 544753) (by norm_num)
theorem B857429 : Blo 570811 857429 := bbase (se 14 (by rfl) ⟨78, by rfl⟩ : syracuseStep 857429 = 157) (by norm_num)
theorem B857453 : Blo 570811 857453 := bbase (se 3 (by rfl) ⟨160772, by rfl⟩ : syracuseStep 857453 = 321545) (by norm_num)
theorem B857477 : Blo 570811 857477 := bbase (se 4 (by rfl) ⟨80388, by rfl⟩ : syracuseStep 857477 = 160777) (by norm_num)
theorem B857501 : Blo 570811 857501 := bbase (se 3 (by rfl) ⟨160781, by rfl⟩ : syracuseStep 857501 = 321563) (by norm_num)
theorem B857525 : Blo 570811 857525 := bbase (se 5 (by rfl) ⟨40196, by rfl⟩ : syracuseStep 857525 = 80393) (by norm_num)
theorem B1938869 : Blo 570811 1938869 := bbase (se 5 (by rfl) ⟨90884, by rfl⟩ : syracuseStep 1938869 = 181769) (by norm_num)
theorem B857549 : Blo 570811 857549 := bbase (se 3 (by rfl) ⟨160790, by rfl⟩ : syracuseStep 857549 = 321581) (by norm_num)
theorem B857573 : Blo 570811 857573 := bbase (se 4 (by rfl) ⟨80397, by rfl⟩ : syracuseStep 857573 = 160795) (by norm_num)
theorem B726509 : Blo 570811 726509 := bbase (se 3 (by rfl) ⟨136220, by rfl⟩ : syracuseStep 726509 = 272441) (by norm_num)
theorem B857597 : Blo 570811 857597 := bbase (se 3 (by rfl) ⟨160799, by rfl⟩ : syracuseStep 857597 = 321599) (by norm_num)
theorem B1447429 : Blo 570811 1447429 := bbase (se 4 (by rfl) ⟨135696, by rfl⟩ : syracuseStep 1447429 = 271393) (by norm_num)
theorem B857621 : Blo 570811 857621 := bbase (se 6 (by rfl) ⟨20100, by rfl⟩ : syracuseStep 857621 = 40201) (by norm_num)
theorem B726565 : Blo 570811 726565 := bbase (se 4 (by rfl) ⟨68115, by rfl⟩ : syracuseStep 726565 = 136231) (by norm_num)
theorem B857645 : Blo 570811 857645 := bbase (se 3 (by rfl) ⟨160808, by rfl⟩ : syracuseStep 857645 = 321617) (by norm_num)
theorem B857669 : Blo 570811 857669 := bbase (se 4 (by rfl) ⟨80406, by rfl⟩ : syracuseStep 857669 = 160813) (by norm_num)
theorem B824909 : Blo 570811 824909 := bbase (se 3 (by rfl) ⟨154670, by rfl⟩ : syracuseStep 824909 = 309341) (by norm_num)
theorem B857693 : Blo 570811 857693 := bbase (se 3 (by rfl) ⟨160817, by rfl⟩ : syracuseStep 857693 = 321635) (by norm_num)
theorem B1119853 : Blo 570811 1119853 := bbase (se 3 (by rfl) ⟨209972, by rfl⟩ : syracuseStep 1119853 = 419945) (by norm_num)
theorem B857717 : Blo 570811 857717 := bbase (se 5 (by rfl) ⟨40205, by rfl⟩ : syracuseStep 857717 = 80411) (by norm_num)
theorem B1447541 : Blo 570811 1447541 := bbase (se 5 (by rfl) ⟨67853, by rfl⟩ : syracuseStep 1447541 = 135707) (by norm_num)
theorem B726661 : Blo 570811 726661 := bbase (se 4 (by rfl) ⟨68124, by rfl⟩ : syracuseStep 726661 = 136249) (by norm_num)
theorem B857741 : Blo 570811 857741 := bbase (se 3 (by rfl) ⟨160826, by rfl⟩ : syracuseStep 857741 = 321653) (by norm_num)
theorem B857765 : Blo 570811 857765 := bbase (se 4 (by rfl) ⟨80415, by rfl⟩ : syracuseStep 857765 = 160831) (by norm_num)
theorem B857789 : Blo 570811 857789 := bbase (se 3 (by rfl) ⟨160835, by rfl⟩ : syracuseStep 857789 = 321671) (by norm_num)
theorem B857813 : Blo 570811 857813 := bbase (se 7 (by rfl) ⟨10052, by rfl⟩ : syracuseStep 857813 = 20105) (by norm_num)
theorem B857837 : Blo 570811 857837 := bbase (se 3 (by rfl) ⟨160844, by rfl⟩ : syracuseStep 857837 = 321689) (by norm_num)
theorem B857861 : Blo 570811 857861 := bbase (se 4 (by rfl) ⟨80424, by rfl⟩ : syracuseStep 857861 = 160849) (by norm_num)
theorem B857885 : Blo 570811 857885 := bbase (se 3 (by rfl) ⟨160853, by rfl⟩ : syracuseStep 857885 = 321707) (by norm_num)
theorem B726833 : Blo 570811 726833 := bbase (se 2 (by rfl) ⟨272562, by rfl⟩ : syracuseStep 726833 = 545125) (by norm_num)
theorem B857909 : Blo 570811 857909 := bbase (se 5 (by rfl) ⟨40214, by rfl⟩ : syracuseStep 857909 = 80429) (by norm_num)
theorem B1447733 : Blo 570811 1447733 := bbase (se 5 (by rfl) ⟨67862, by rfl⟩ : syracuseStep 1447733 = 135725) (by norm_num)
theorem B857933 : Blo 570811 857933 := bbase (se 3 (by rfl) ⟨160862, by rfl⟩ : syracuseStep 857933 = 321725) (by norm_num)
theorem B857957 : Blo 570811 857957 := bbase (se 4 (by rfl) ⟨80433, by rfl⟩ : syracuseStep 857957 = 160867) (by norm_num)
theorem B1939301 : Blo 570811 1939301 := bbase (se 4 (by rfl) ⟨181809, by rfl⟩ : syracuseStep 1939301 = 363619) (by norm_num)
theorem B726889 : Blo 570811 726889 := bbase (se 2 (by rfl) ⟨272583, by rfl⟩ : syracuseStep 726889 = 545167) (by norm_num)
theorem B857981 : Blo 570811 857981 := bbase (se 3 (by rfl) ⟨160871, by rfl⟩ : syracuseStep 857981 = 321743) (by norm_num)
theorem B1087357 : Blo 570811 1087357 := bbase (se 3 (by rfl) ⟨203879, by rfl⟩ : syracuseStep 1087357 = 407759) (by norm_num)
theorem B858005 : Blo 570811 858005 := bbase (se 6 (by rfl) ⟨20109, by rfl⟩ : syracuseStep 858005 = 40219) (by norm_num)
theorem B858029 : Blo 570811 858029 := bbase (se 3 (by rfl) ⟨160880, by rfl⟩ : syracuseStep 858029 = 321761) (by norm_num)
theorem B858053 : Blo 570811 858053 := bbase (se 4 (by rfl) ⟨80442, by rfl⟩ : syracuseStep 858053 = 160885) (by norm_num)
theorem B726985 : Blo 570811 726985 := bbase (se 2 (by rfl) ⟨272619, by rfl⟩ : syracuseStep 726985 = 545239) (by norm_num)
theorem B858077 : Blo 570811 858077 := bbase (se 3 (by rfl) ⟨160889, by rfl⟩ : syracuseStep 858077 = 321779) (by norm_num)
theorem B858101 : Blo 570811 858101 := bbase (se 5 (by rfl) ⟨40223, by rfl⟩ : syracuseStep 858101 = 80447) (by norm_num)
theorem B858125 : Blo 570811 858125 := bbase (se 3 (by rfl) ⟨160898, by rfl⟩ : syracuseStep 858125 = 321797) (by norm_num)
theorem B1087501 : Blo 570811 1087501 := bbase (se 3 (by rfl) ⟨203906, by rfl⟩ : syracuseStep 1087501 = 407813) (by norm_num)
theorem B858149 : Blo 570811 858149 := bbase (se 4 (by rfl) ⟨80451, by rfl⟩ : syracuseStep 858149 = 160903) (by norm_num)
theorem B858173 : Blo 570811 858173 := bbase (se 3 (by rfl) ⟨160907, by rfl⟩ : syracuseStep 858173 = 321815) (by norm_num)
theorem B858197 : Blo 570811 858197 := bbase (se 8 (by rfl) ⟨5028, by rfl⟩ : syracuseStep 858197 = 10057) (by norm_num)
theorem B858221 : Blo 570811 858221 := bbase (se 3 (by rfl) ⟨160916, by rfl⟩ : syracuseStep 858221 = 321833) (by norm_num)
theorem B4954229 : Blo 570811 4954229 := bbase (se 5 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 4954229 = 464459) (by norm_num)
theorem B727157 : Blo 570811 727157 := bbase (se 5 (by rfl) ⟨34085, by rfl⟩ : syracuseStep 727157 = 68171) (by norm_num)
theorem B858245 : Blo 570811 858245 := bbase (se 4 (by rfl) ⟨80460, by rfl⟩ : syracuseStep 858245 = 160921) (by norm_num)
theorem B1448077 : Blo 570811 1448077 := bbase (se 3 (by rfl) ⟨271514, by rfl⟩ : syracuseStep 1448077 = 543029) (by norm_num)
theorem B858269 : Blo 570811 858269 := bbase (se 3 (by rfl) ⟨160925, by rfl⟩ : syracuseStep 858269 = 321851) (by norm_num)
theorem B1087661 : Blo 570811 1087661 := bbase (se 3 (by rfl) ⟨203936, by rfl⟩ : syracuseStep 1087661 = 407873) (by norm_num)
theorem B727213 : Blo 570811 727213 := bbase (se 3 (by rfl) ⟨136352, by rfl⟩ : syracuseStep 727213 = 272705) (by norm_num)
theorem B858293 : Blo 570811 858293 := bbase (se 5 (by rfl) ⟨40232, by rfl⟩ : syracuseStep 858293 = 80465) (by norm_num)
theorem B858317 : Blo 570811 858317 := bbase (se 3 (by rfl) ⟨160934, by rfl⟩ : syracuseStep 858317 = 321869) (by norm_num)
theorem B858341 : Blo 570811 858341 := bbase (se 4 (by rfl) ⟨80469, by rfl⟩ : syracuseStep 858341 = 160939) (by norm_num)
theorem B825589 : Blo 570811 825589 := bbase (se 5 (by rfl) ⟨38699, by rfl⟩ : syracuseStep 825589 = 77399) (by norm_num)
theorem B1448189 : Blo 570811 1448189 := bbase (se 3 (by rfl) ⟨271535, by rfl⟩ : syracuseStep 1448189 = 543071) (by norm_num)
theorem B858365 : Blo 570811 858365 := bbase (se 3 (by rfl) ⟨160943, by rfl⟩ : syracuseStep 858365 = 321887) (by norm_num)
theorem B1841413 : Blo 570811 1841413 := bbase (se 4 (by rfl) ⟨172632, by rfl⟩ : syracuseStep 1841413 = 345265) (by norm_num)
theorem B727309 : Blo 570811 727309 := bbase (se 3 (by rfl) ⟨136370, by rfl⟩ : syracuseStep 727309 = 272741) (by norm_num)
theorem B858389 : Blo 570811 858389 := bbase (se 6 (by rfl) ⟨20118, by rfl⟩ : syracuseStep 858389 = 40237) (by norm_num)
theorem B1939733 : Blo 570811 1939733 := bbase (se 6 (by rfl) ⟨45462, by rfl⟩ : syracuseStep 1939733 = 90925) (by norm_num)
theorem B1284389 : Blo 570811 1284389 := bbase (se 4 (by rfl) ⟨120411, by rfl⟩ : syracuseStep 1284389 = 240823) (by norm_num)
theorem B2169125 : Blo 570811 2169125 := bbase (se 4 (by rfl) ⟨203355, by rfl⟩ : syracuseStep 2169125 = 406711) (by norm_num)
theorem B858413 : Blo 570811 858413 := bbase (se 3 (by rfl) ⟨160952, by rfl⟩ : syracuseStep 858413 = 321905) (by norm_num)
theorem B1087805 : Blo 570811 1087805 := bbase (se 3 (by rfl) ⟨203963, by rfl⟩ : syracuseStep 1087805 = 407927) (by norm_num)
theorem B858437 : Blo 570811 858437 := bbase (se 4 (by rfl) ⟨80478, by rfl⟩ : syracuseStep 858437 = 160957) (by norm_num)
theorem B858461 : Blo 570811 858461 := bbase (se 3 (by rfl) ⟨160961, by rfl⟩ : syracuseStep 858461 = 321923) (by norm_num)
theorem B1284461 : Blo 570811 1284461 := bbase (se 3 (by rfl) ⟨240836, by rfl⟩ : syracuseStep 1284461 = 481673) (by norm_num)
theorem B858485 : Blo 570811 858485 := bbase (se 5 (by rfl) ⟨40241, by rfl⟩ : syracuseStep 858485 = 80483) (by norm_num)
theorem B858509 : Blo 570811 858509 := bbase (se 3 (by rfl) ⟨160970, by rfl⟩ : syracuseStep 858509 = 321941) (by norm_num)
theorem B858533 : Blo 570811 858533 := bbase (se 4 (by rfl) ⟨80487, by rfl⟩ : syracuseStep 858533 = 160975) (by norm_num)
theorem B1284533 : Blo 570811 1284533 := bbase (se 5 (by rfl) ⟨60212, by rfl⟩ : syracuseStep 1284533 = 120425) (by norm_num)
theorem B727481 : Blo 570811 727481 := bbase (se 2 (by rfl) ⟨272805, by rfl⟩ : syracuseStep 727481 = 545611) (by norm_num)
theorem B1448381 : Blo 570811 1448381 := bbase (se 3 (by rfl) ⟨271571, by rfl⟩ : syracuseStep 1448381 = 543143) (by norm_num)
theorem B858557 : Blo 570811 858557 := bbase (se 3 (by rfl) ⟨160979, by rfl⟩ : syracuseStep 858557 = 321959) (by norm_num)
theorem B858581 : Blo 570811 858581 := bbase (se 7 (by rfl) ⟨10061, by rfl⟩ : syracuseStep 858581 = 20123) (by norm_num)
theorem B858605 : Blo 570811 858605 := bbase (se 3 (by rfl) ⟨160988, by rfl⟩ : syracuseStep 858605 = 321977) (by norm_num)
theorem B1284605 : Blo 570811 1284605 := bbase (se 3 (by rfl) ⟨240863, by rfl⟩ : syracuseStep 1284605 = 481727) (by norm_num)
theorem B858629 : Blo 570811 858629 := bbase (se 4 (by rfl) ⟨80496, by rfl⟩ : syracuseStep 858629 = 160993) (by norm_num)
theorem B858653 : Blo 570811 858653 := bbase (se 3 (by rfl) ⟨160997, by rfl⟩ : syracuseStep 858653 = 321995) (by norm_num)
theorem B858677 : Blo 570811 858677 := bbase (se 5 (by rfl) ⟨40250, by rfl⟩ : syracuseStep 858677 = 80501) (by norm_num)
theorem B1284677 : Blo 570811 1284677 := bbase (se 4 (by rfl) ⟨120438, by rfl⟩ : syracuseStep 1284677 = 240877) (by norm_num)
theorem B2169413 : Blo 570811 2169413 := bbase (se 4 (by rfl) ⟨203382, by rfl⟩ : syracuseStep 2169413 = 406765) (by norm_num)
theorem B858701 : Blo 570811 858701 := bbase (se 3 (by rfl) ⟨161006, by rfl⟩ : syracuseStep 858701 = 322013) (by norm_num)
theorem B1088093 : Blo 570811 1088093 := bbase (se 3 (by rfl) ⟨204017, by rfl⟩ : syracuseStep 1088093 = 408035) (by norm_num)
theorem B858725 : Blo 570811 858725 := bbase (se 4 (by rfl) ⟨80505, by rfl⟩ : syracuseStep 858725 = 161011) (by norm_num)
theorem B858749 : Blo 570811 858749 := bbase (se 3 (by rfl) ⟨161015, by rfl⟩ : syracuseStep 858749 = 322031) (by norm_num)
theorem B1284749 : Blo 570811 1284749 := bbase (se 3 (by rfl) ⟨240890, by rfl⟩ : syracuseStep 1284749 = 481781) (by norm_num)
theorem B858773 : Blo 570811 858773 := bbase (se 6 (by rfl) ⟨20127, by rfl⟩ : syracuseStep 858773 = 40255) (by norm_num)
theorem B858797 : Blo 570811 858797 := bbase (se 3 (by rfl) ⟨161024, by rfl⟩ : syracuseStep 858797 = 322049) (by norm_num)
theorem B858821 : Blo 570811 858821 := bbase (se 4 (by rfl) ⟨80514, by rfl⟩ : syracuseStep 858821 = 161029) (by norm_num)
theorem B1284821 : Blo 570811 1284821 := bbase (se 7 (by rfl) ⟨15056, by rfl⟩ : syracuseStep 1284821 = 30113) (by norm_num)
theorem B858845 : Blo 570811 858845 := bbase (se 3 (by rfl) ⟨161033, by rfl⟩ : syracuseStep 858845 = 322067) (by norm_num)
theorem B858869 : Blo 570811 858869 := bbase (se 5 (by rfl) ⟨40259, by rfl⟩ : syracuseStep 858869 = 80519) (by norm_num)
theorem B1088245 : Blo 570811 1088245 := bbase (se 5 (by rfl) ⟨51011, by rfl⟩ : syracuseStep 1088245 = 102023) (by norm_num)
theorem B629497 : Blo 570811 629497 := bbase (se 2 (by rfl) ⟨236061, by rfl⟩ : syracuseStep 629497 = 472123) (by norm_num)
theorem B858893 : Blo 570811 858893 := bbase (se 3 (by rfl) ⟨161042, by rfl⟩ : syracuseStep 858893 = 322085) (by norm_num)
theorem B1448725 : Blo 570811 1448725 := bbase (se 6 (by rfl) ⟨33954, by rfl⟩ : syracuseStep 1448725 = 67909) (by norm_num)
theorem B1284893 : Blo 570811 1284893 := bbase (se 3 (by rfl) ⟨240917, by rfl⟩ : syracuseStep 1284893 = 481835) (by norm_num)
theorem B629537 : Blo 570811 629537 := bbase (se 2 (by rfl) ⟨236076, by rfl⟩ : syracuseStep 629537 = 472153) (by norm_num)
theorem B858917 : Blo 570811 858917 := bbase (se 4 (by rfl) ⟨80523, by rfl⟩ : syracuseStep 858917 = 161047) (by norm_num)
theorem B858941 : Blo 570811 858941 := bbase (se 3 (by rfl) ⟨161051, by rfl⟩ : syracuseStep 858941 = 322103) (by norm_num)
theorem B2890565 : Blo 570811 2890565 := bbase (se 4 (by rfl) ⟨270990, by rfl⟩ : syracuseStep 2890565 = 541981) (by norm_num)
theorem B858965 : Blo 570811 858965 := bbase (se 9 (by rfl) ⟨2516, by rfl⟩ : syracuseStep 858965 = 5033) (by norm_num)
theorem B1284965 : Blo 570811 1284965 := bbase (se 4 (by rfl) ⟨120465, by rfl⟩ : syracuseStep 1284965 = 240931) (by norm_num)
theorem B858989 : Blo 570811 858989 := bbase (se 3 (by rfl) ⟨161060, by rfl⟩ : syracuseStep 858989 = 322121) (by norm_num)
theorem B1448837 : Blo 570811 1448837 := bbase (se 4 (by rfl) ⟨135828, by rfl⟩ : syracuseStep 1448837 = 271657) (by norm_num)
theorem B859013 : Blo 570811 859013 := bbase (se 4 (by rfl) ⟨80532, by rfl⟩ : syracuseStep 859013 = 161065) (by norm_num)
theorem B859037 : Blo 570811 859037 := bbase (se 3 (by rfl) ⟨161069, by rfl⟩ : syracuseStep 859037 = 322139) (by norm_num)
theorem B1285037 : Blo 570811 1285037 := bbase (se 3 (by rfl) ⟨240944, by rfl⟩ : syracuseStep 1285037 = 481889) (by norm_num)
theorem B859061 : Blo 570811 859061 := bbase (se 5 (by rfl) ⟨40268, by rfl⟩ : syracuseStep 859061 = 80537) (by norm_num)
theorem B859085 : Blo 570811 859085 := bbase (se 3 (by rfl) ⟨161078, by rfl⟩ : syracuseStep 859085 = 322157) (by norm_num)
theorem B859109 : Blo 570811 859109 := bbase (se 4 (by rfl) ⟨80541, by rfl⟩ : syracuseStep 859109 = 161083) (by norm_num)
theorem B1285109 : Blo 570811 1285109 := bbase (se 5 (by rfl) ⟨60239, by rfl⟩ : syracuseStep 1285109 = 120479) (by norm_num)
theorem B859133 : Blo 570811 859133 := bbase (se 3 (by rfl) ⟨161087, by rfl⟩ : syracuseStep 859133 = 322175) (by norm_num)
theorem B859157 : Blo 570811 859157 := bbase (se 6 (by rfl) ⟨20136, by rfl⟩ : syracuseStep 859157 = 40273) (by norm_num)
theorem B1088549 : Blo 570811 1088549 := bbase (se 4 (by rfl) ⟨102051, by rfl⟩ : syracuseStep 1088549 = 204103) (by norm_num)
theorem B859181 : Blo 570811 859181 := bbase (se 3 (by rfl) ⟨161096, by rfl⟩ : syracuseStep 859181 = 322193) (by norm_num)
theorem B3677237 : Blo 570811 3677237 := bbase (se 5 (by rfl) ⟨172370, by rfl⟩ : syracuseStep 3677237 = 344741) (by norm_num)
theorem B1285181 : Blo 570811 1285181 := bbase (se 3 (by rfl) ⟨240971, by rfl⟩ : syracuseStep 1285181 = 481943) (by norm_num)
theorem B1449029 : Blo 570811 1449029 := bbase (se 4 (by rfl) ⟨135846, by rfl⟩ : syracuseStep 1449029 = 271693) (by norm_num)
theorem B859205 : Blo 570811 859205 := bbase (se 4 (by rfl) ⟨80550, by rfl⟩ : syracuseStep 859205 = 161101) (by norm_num)
theorem B859229 : Blo 570811 859229 := bbase (se 3 (by rfl) ⟨161105, by rfl⟩ : syracuseStep 859229 = 322211) (by norm_num)
theorem B859253 : Blo 570811 859253 := bbase (se 5 (by rfl) ⟨40277, by rfl⟩ : syracuseStep 859253 = 80555) (by norm_num)
theorem B1285253 : Blo 570811 1285253 := bbase (se 4 (by rfl) ⟨120492, by rfl⟩ : syracuseStep 1285253 = 240985) (by norm_num)
theorem B859277 : Blo 570811 859277 := bbase (se 3 (by rfl) ⟨161114, by rfl⟩ : syracuseStep 859277 = 322229) (by norm_num)
theorem B859301 : Blo 570811 859301 := bbase (se 4 (by rfl) ⟨80559, by rfl⟩ : syracuseStep 859301 = 161119) (by norm_num)
theorem B859325 : Blo 570811 859325 := bbase (se 3 (by rfl) ⟨161123, by rfl⟩ : syracuseStep 859325 = 322247) (by norm_num)
theorem B1285325 : Blo 570811 1285325 := bbase (se 3 (by rfl) ⟨240998, by rfl⟩ : syracuseStep 1285325 = 481997) (by norm_num)
theorem B859349 : Blo 570811 859349 := bbase (se 7 (by rfl) ⟨10070, by rfl⟩ : syracuseStep 859349 = 20141) (by norm_num)
theorem B859373 : Blo 570811 859373 := bbase (se 3 (by rfl) ⟨161132, by rfl⟩ : syracuseStep 859373 = 322265) (by norm_num)
theorem B859397 : Blo 570811 859397 := bbase (se 4 (by rfl) ⟨80568, by rfl⟩ : syracuseStep 859397 = 161137) (by norm_num)
theorem B1285397 : Blo 570811 1285397 := bbase (se 6 (by rfl) ⟨30126, by rfl⟩ : syracuseStep 1285397 = 60253) (by norm_num)
theorem B859421 : Blo 570811 859421 := bbase (se 3 (by rfl) ⟨161141, by rfl⟩ : syracuseStep 859421 = 322283) (by norm_num)
theorem B859445 : Blo 570811 859445 := bbase (se 5 (by rfl) ⟨40286, by rfl⟩ : syracuseStep 859445 = 80573) (by norm_num)
theorem B859469 : Blo 570811 859469 := bbase (se 3 (by rfl) ⟨161150, by rfl⟩ : syracuseStep 859469 = 322301) (by norm_num)
theorem B1285469 : Blo 570811 1285469 := bbase (se 3 (by rfl) ⟨241025, by rfl⟩ : syracuseStep 1285469 = 482051) (by norm_num)
theorem B859493 : Blo 570811 859493 := bbase (se 4 (by rfl) ⟨80577, by rfl⟩ : syracuseStep 859493 = 161155) (by norm_num)
theorem B859517 : Blo 570811 859517 := bbase (se 3 (by rfl) ⟨161159, by rfl⟩ : syracuseStep 859517 = 322319) (by norm_num)
theorem B859541 : Blo 570811 859541 := bbase (se 6 (by rfl) ⟨20145, by rfl⟩ : syracuseStep 859541 = 40291) (by norm_num)
theorem B1219997 : Blo 570811 1219997 := bbase (se 3 (by rfl) ⟨228749, by rfl⟩ : syracuseStep 1219997 = 457499) (by norm_num)
theorem B1449373 : Blo 570811 1449373 := bbase (se 3 (by rfl) ⟨271757, by rfl⟩ : syracuseStep 1449373 = 543515) (by norm_num)
theorem B1285541 : Blo 570811 1285541 := bbase (se 4 (by rfl) ⟨120519, by rfl⟩ : syracuseStep 1285541 = 241039) (by norm_num)
theorem B859565 : Blo 570811 859565 := bbase (se 3 (by rfl) ⟨161168, by rfl⟩ : syracuseStep 859565 = 322337) (by norm_num)
theorem B859589 : Blo 570811 859589 := bbase (se 4 (by rfl) ⟨80586, by rfl⟩ : syracuseStep 859589 = 161173) (by norm_num)
theorem B859613 : Blo 570811 859613 := bbase (se 3 (by rfl) ⟨161177, by rfl⟩ : syracuseStep 859613 = 322355) (by norm_num)
theorem B1285613 : Blo 570811 1285613 := bbase (se 3 (by rfl) ⟨241052, by rfl⟩ : syracuseStep 1285613 = 482105) (by norm_num)
theorem B859637 : Blo 570811 859637 := bbase (se 5 (by rfl) ⟨40295, by rfl⟩ : syracuseStep 859637 = 80591) (by norm_num)
theorem B1449485 : Blo 570811 1449485 := bbase (se 3 (by rfl) ⟨271778, by rfl⟩ : syracuseStep 1449485 = 543557) (by norm_num)
theorem B859661 : Blo 570811 859661 := bbase (se 3 (by rfl) ⟨161186, by rfl⟩ : syracuseStep 859661 = 322373) (by norm_num)
theorem B859685 : Blo 570811 859685 := bbase (se 4 (by rfl) ⟨80595, by rfl⟩ : syracuseStep 859685 = 161191) (by norm_num)
theorem B1220141 : Blo 570811 1220141 := bbase (se 3 (by rfl) ⟨228776, by rfl⟩ : syracuseStep 1220141 = 457553) (by norm_num)
theorem B1285685 : Blo 570811 1285685 := bbase (se 5 (by rfl) ⟨60266, by rfl⟩ : syracuseStep 1285685 = 120533) (by norm_num)
theorem B859709 : Blo 570811 859709 := bbase (se 3 (by rfl) ⟨161195, by rfl⟩ : syracuseStep 859709 = 322391) (by norm_num)
theorem B859733 : Blo 570811 859733 := bbase (se 8 (by rfl) ⟨5037, by rfl⟩ : syracuseStep 859733 = 10075) (by norm_num)
theorem B859757 : Blo 570811 859757 := bbase (se 3 (by rfl) ⟨161204, by rfl⟩ : syracuseStep 859757 = 322409) (by norm_num)
theorem B1285757 : Blo 570811 1285757 := bbase (se 3 (by rfl) ⟨241079, by rfl⟩ : syracuseStep 1285757 = 482159) (by norm_num)
theorem B859781 : Blo 570811 859781 := bbase (se 4 (by rfl) ⟨80604, by rfl⟩ : syracuseStep 859781 = 161209) (by norm_num)
theorem B859805 : Blo 570811 859805 := bbase (se 3 (by rfl) ⟨161213, by rfl⟩ : syracuseStep 859805 = 322427) (by norm_num)
theorem B859829 : Blo 570811 859829 := bbase (se 5 (by rfl) ⟨40304, by rfl⟩ : syracuseStep 859829 = 80609) (by norm_num)
theorem B1285829 : Blo 570811 1285829 := bbase (se 4 (by rfl) ⟨120546, by rfl⟩ : syracuseStep 1285829 = 241093) (by norm_num)
theorem B2760389 : Blo 570811 2760389 := bbase (se 4 (by rfl) ⟨258786, by rfl⟩ : syracuseStep 2760389 = 517573) (by norm_num)
theorem B1449677 : Blo 570811 1449677 := bbase (se 3 (by rfl) ⟨271814, by rfl⟩ : syracuseStep 1449677 = 543629) (by norm_num)
theorem B859853 : Blo 570811 859853 := bbase (se 3 (by rfl) ⟨161222, by rfl⟩ : syracuseStep 859853 = 322445) (by norm_num)
theorem B3776213 : Blo 570811 3776213 := bbase (se 7 (by rfl) ⟨44252, by rfl⟩ : syracuseStep 3776213 = 88505) (by norm_num)
theorem B2170597 : Blo 570811 2170597 := bbase (se 4 (by rfl) ⟨203493, by rfl⟩ : syracuseStep 2170597 = 406987) (by norm_num)
theorem B859877 : Blo 570811 859877 := bbase (se 4 (by rfl) ⟨80613, by rfl⟩ : syracuseStep 859877 = 161227) (by norm_num)
theorem B859901 : Blo 570811 859901 := bbase (se 3 (by rfl) ⟨161231, by rfl⟩ : syracuseStep 859901 = 322463) (by norm_num)
theorem B1285901 : Blo 570811 1285901 := bbase (se 3 (by rfl) ⟨241106, by rfl⟩ : syracuseStep 1285901 = 482213) (by norm_num)
theorem B859925 : Blo 570811 859925 := bbase (se 6 (by rfl) ⟨20154, by rfl⟩ : syracuseStep 859925 = 40309) (by norm_num)
theorem B1089301 : Blo 570811 1089301 := bbase (se 6 (by rfl) ⟨25530, by rfl⟩ : syracuseStep 1089301 = 51061) (by norm_num)
theorem B859949 : Blo 570811 859949 := bbase (se 3 (by rfl) ⟨161240, by rfl⟩ : syracuseStep 859949 = 322481) (by norm_num)
theorem B3088181 : Blo 570811 3088181 := bbase (se 5 (by rfl) ⟨144758, by rfl⟩ : syracuseStep 3088181 = 289517) (by norm_num)
theorem B859973 : Blo 570811 859973 := bbase (se 4 (by rfl) ⟨80622, by rfl⟩ : syracuseStep 859973 = 161245) (by norm_num)
theorem B1285973 : Blo 570811 1285973 := bbase (se 9 (by rfl) ⟨3767, by rfl⟩ : syracuseStep 1285973 = 7535) (by norm_num)
theorem B859997 : Blo 570811 859997 := bbase (se 3 (by rfl) ⟨161249, by rfl⟩ : syracuseStep 859997 = 322499) (by norm_num)
theorem B860021 : Blo 570811 860021 := bbase (se 5 (by rfl) ⟨40313, by rfl⟩ : syracuseStep 860021 = 80627) (by norm_num)
theorem B860045 : Blo 570811 860045 := bbase (se 3 (by rfl) ⟨161258, by rfl⟩ : syracuseStep 860045 = 322517) (by norm_num)
theorem B1220501 : Blo 570811 1220501 := bbase (se 6 (by rfl) ⟨28605, by rfl⟩ : syracuseStep 1220501 = 57211) (by norm_num)
theorem B1286045 : Blo 570811 1286045 := bbase (se 3 (by rfl) ⟨241133, by rfl⟩ : syracuseStep 1286045 = 482267) (by norm_num)
theorem B991133 : Blo 570811 991133 := bbase (se 3 (by rfl) ⟨185837, by rfl⟩ : syracuseStep 991133 = 371675) (by norm_num)
theorem B860069 : Blo 570811 860069 := bbase (se 4 (by rfl) ⟨80631, by rfl⟩ : syracuseStep 860069 = 161263) (by norm_num)
theorem B1089445 : Blo 570811 1089445 := bbase (se 4 (by rfl) ⟨102135, by rfl⟩ : syracuseStep 1089445 = 204271) (by norm_num)
theorem B860093 : Blo 570811 860093 := bbase (se 3 (by rfl) ⟨161267, by rfl⟩ : syracuseStep 860093 = 322535) (by norm_num)
theorem B663493 : Blo 570811 663493 := bbase (se 4 (by rfl) ⟨62202, by rfl⟩ : syracuseStep 663493 = 124405) (by norm_num)
theorem B860117 : Blo 570811 860117 := bbase (se 7 (by rfl) ⟨10079, by rfl⟩ : syracuseStep 860117 = 20159) (by norm_num)
theorem B1286117 : Blo 570811 1286117 := bbase (se 4 (by rfl) ⟨120573, by rfl⟩ : syracuseStep 1286117 = 241147) (by norm_num)
theorem B860141 : Blo 570811 860141 := bbase (se 3 (by rfl) ⟨161276, by rfl⟩ : syracuseStep 860141 = 322553) (by norm_num)
theorem B860165 : Blo 570811 860165 := bbase (se 4 (by rfl) ⟨80640, by rfl⟩ : syracuseStep 860165 = 161281) (by norm_num)
theorem B2170901 : Blo 570811 2170901 := bbase (se 6 (by rfl) ⟨50880, by rfl⟩ : syracuseStep 2170901 = 101761) (by norm_num)
theorem B860189 : Blo 570811 860189 := bbase (se 3 (by rfl) ⟨161285, by rfl⟩ : syracuseStep 860189 = 322571) (by norm_num)
theorem B1450021 : Blo 570811 1450021 := bbase (se 4 (by rfl) ⟨135939, by rfl⟩ : syracuseStep 1450021 = 271879) (by norm_num)
theorem B1286189 : Blo 570811 1286189 := bbase (se 3 (by rfl) ⟨241160, by rfl⟩ : syracuseStep 1286189 = 482321) (by norm_num)
theorem B860213 : Blo 570811 860213 := bbase (se 5 (by rfl) ⟨40322, by rfl⟩ : syracuseStep 860213 = 80645) (by norm_num)
theorem B1089605 : Blo 570811 1089605 := bbase (se 4 (by rfl) ⟨102150, by rfl⟩ : syracuseStep 1089605 = 204301) (by norm_num)
theorem B860237 : Blo 570811 860237 := bbase (se 3 (by rfl) ⟨161294, by rfl⟩ : syracuseStep 860237 = 322589) (by norm_num)
theorem B2891861 : Blo 570811 2891861 := bbase (se 8 (by rfl) ⟨16944, by rfl⟩ : syracuseStep 2891861 = 33889) (by norm_num)
theorem B860261 : Blo 570811 860261 := bbase (se 4 (by rfl) ⟨80649, by rfl⟩ : syracuseStep 860261 = 161299) (by norm_num)
theorem B1286261 : Blo 570811 1286261 := bbase (se 5 (by rfl) ⟨60293, by rfl⟩ : syracuseStep 1286261 = 120587) (by norm_num)
theorem B860285 : Blo 570811 860285 := bbase (se 3 (by rfl) ⟨161303, by rfl⟩ : syracuseStep 860285 = 322607) (by norm_num)
theorem B1450133 : Blo 570811 1450133 := bbase (se 6 (by rfl) ⟨33987, by rfl⟩ : syracuseStep 1450133 = 67975) (by norm_num)
theorem B860309 : Blo 570811 860309 := bbase (se 6 (by rfl) ⟨20163, by rfl⟩ : syracuseStep 860309 = 40327) (by norm_num)
theorem B860333 : Blo 570811 860333 := bbase (se 3 (by rfl) ⟨161312, by rfl⟩ : syracuseStep 860333 = 322625) (by norm_num)
theorem B1286333 : Blo 570811 1286333 := bbase (se 3 (by rfl) ⟨241187, by rfl⟩ : syracuseStep 1286333 = 482375) (by norm_num)
theorem B860357 : Blo 570811 860357 := bbase (se 4 (by rfl) ⟨80658, by rfl⟩ : syracuseStep 860357 = 161317) (by norm_num)
theorem B1089749 : Blo 570811 1089749 := bbase (se 7 (by rfl) ⟨12770, by rfl⟩ : syracuseStep 1089749 = 25541) (by norm_num)
theorem B860381 : Blo 570811 860381 := bbase (se 3 (by rfl) ⟨161321, by rfl⟩ : syracuseStep 860381 = 322643) (by norm_num)
theorem B860405 : Blo 570811 860405 := bbase (se 5 (by rfl) ⟨40331, by rfl⟩ : syracuseStep 860405 = 80663) (by norm_num)
theorem B1286405 : Blo 570811 1286405 := bbase (se 4 (by rfl) ⟨120600, by rfl⟩ : syracuseStep 1286405 = 241201) (by norm_num)
theorem B860429 : Blo 570811 860429 := bbase (se 3 (by rfl) ⟨161330, by rfl⟩ : syracuseStep 860429 = 322661) (by norm_num)
theorem B860453 : Blo 570811 860453 := bbase (se 4 (by rfl) ⟨80667, by rfl⟩ : syracuseStep 860453 = 161335) (by norm_num)
theorem B860477 : Blo 570811 860477 := bbase (se 3 (by rfl) ⟨161339, by rfl⟩ : syracuseStep 860477 = 322679) (by norm_num)
theorem B2203973 : Blo 570811 2203973 := bbase (se 4 (by rfl) ⟨206622, by rfl⟩ : syracuseStep 2203973 = 413245) (by norm_num)
theorem B1286477 : Blo 570811 1286477 := bbase (se 3 (by rfl) ⟨241214, by rfl⟩ : syracuseStep 1286477 = 482429) (by norm_num)
theorem B1450325 : Blo 570811 1450325 := bbase (se 10 (by rfl) ⟨2124, by rfl⟩ : syracuseStep 1450325 = 4249) (by norm_num)
theorem B860501 : Blo 570811 860501 := bbase (se 10 (by rfl) ⟨1260, by rfl⟩ : syracuseStep 860501 = 2521) (by norm_num)
theorem B860525 : Blo 570811 860525 := bbase (se 3 (by rfl) ⟨161348, by rfl⟩ : syracuseStep 860525 = 322697) (by norm_num)
theorem B860549 : Blo 570811 860549 := bbase (se 4 (by rfl) ⟨80676, by rfl⟩ : syracuseStep 860549 = 161353) (by norm_num)
theorem B1286549 : Blo 570811 1286549 := bbase (se 6 (by rfl) ⟨30153, by rfl⟩ : syracuseStep 1286549 = 60307) (by norm_num)
theorem B860573 : Blo 570811 860573 := bbase (se 3 (by rfl) ⟨161357, by rfl⟩ : syracuseStep 860573 = 322715) (by norm_num)
theorem B860597 : Blo 570811 860597 := bbase (se 5 (by rfl) ⟨40340, by rfl⟩ : syracuseStep 860597 = 80681) (by norm_num)
theorem B860621 : Blo 570811 860621 := bbase (se 3 (by rfl) ⟨161366, by rfl⟩ : syracuseStep 860621 = 322733) (by norm_num)
theorem B1286621 : Blo 570811 1286621 := bbase (se 3 (by rfl) ⟨241241, by rfl⟩ : syracuseStep 1286621 = 482483) (by norm_num)
theorem B860645 : Blo 570811 860645 := bbase (se 4 (by rfl) ⟨80685, by rfl⟩ : syracuseStep 860645 = 161371) (by norm_num)
theorem B1090037 : Blo 570811 1090037 := bbase (se 5 (by rfl) ⟨51095, by rfl⟩ : syracuseStep 1090037 = 102191) (by norm_num)
theorem B860669 : Blo 570811 860669 := bbase (se 3 (by rfl) ⟨161375, by rfl⟩ : syracuseStep 860669 = 322751) (by norm_num)
theorem B860693 : Blo 570811 860693 := bbase (se 6 (by rfl) ⟨20172, by rfl⟩ : syracuseStep 860693 = 40345) (by norm_num)
theorem B1286693 : Blo 570811 1286693 := bbase (se 4 (by rfl) ⟨120627, by rfl⟩ : syracuseStep 1286693 = 241255) (by norm_num)
theorem B860717 : Blo 570811 860717 := bbase (se 3 (by rfl) ⟨161384, by rfl⟩ : syracuseStep 860717 = 322769) (by norm_num)
theorem B860741 : Blo 570811 860741 := bbase (se 4 (by rfl) ⟨80694, by rfl⟩ : syracuseStep 860741 = 161389) (by norm_num)
theorem B5218901 : Blo 570811 5218901 := bbase (se 8 (by rfl) ⟨30579, by rfl⟩ : syracuseStep 5218901 = 61159) (by norm_num)
theorem B860765 : Blo 570811 860765 := bbase (se 3 (by rfl) ⟨161393, by rfl⟩ : syracuseStep 860765 = 322787) (by norm_num)
theorem B1286765 : Blo 570811 1286765 := bbase (se 3 (by rfl) ⟨241268, by rfl⟩ : syracuseStep 1286765 = 482537) (by norm_num)
theorem B860789 : Blo 570811 860789 := bbase (se 5 (by rfl) ⟨40349, by rfl⟩ : syracuseStep 860789 = 80699) (by norm_num)
theorem B860813 : Blo 570811 860813 := bbase (se 3 (by rfl) ⟨161402, by rfl⟩ : syracuseStep 860813 = 322805) (by norm_num)
theorem B1090189 : Blo 570811 1090189 := bbase (se 3 (by rfl) ⟨204410, by rfl⟩ : syracuseStep 1090189 = 408821) (by norm_num)
theorem B860837 : Blo 570811 860837 := bbase (se 4 (by rfl) ⟨80703, by rfl⟩ : syracuseStep 860837 = 161407) (by norm_num)
theorem B1450669 : Blo 570811 1450669 := bbase (se 3 (by rfl) ⟨272000, by rfl⟩ : syracuseStep 1450669 = 544001) (by norm_num)
theorem B1286837 : Blo 570811 1286837 := bbase (se 5 (by rfl) ⟨60320, by rfl⟩ : syracuseStep 1286837 = 120641) (by norm_num)
theorem B860861 : Blo 570811 860861 := bbase (se 3 (by rfl) ⟨161411, by rfl⟩ : syracuseStep 860861 = 322823) (by norm_num)
theorem B860885 : Blo 570811 860885 := bbase (se 7 (by rfl) ⟨10088, by rfl⟩ : syracuseStep 860885 = 20177) (by norm_num)
theorem B860909 : Blo 570811 860909 := bbase (se 3 (by rfl) ⟨161420, by rfl⟩ : syracuseStep 860909 = 322841) (by norm_num)
theorem B1286909 : Blo 570811 1286909 := bbase (se 3 (by rfl) ⟨241295, by rfl⟩ : syracuseStep 1286909 = 482591) (by norm_num)
theorem B860933 : Blo 570811 860933 := bbase (se 4 (by rfl) ⟨80712, by rfl⟩ : syracuseStep 860933 = 161425) (by norm_num)
theorem B1221389 : Blo 570811 1221389 := bbase (se 3 (by rfl) ⟨229010, by rfl⟩ : syracuseStep 1221389 = 458021) (by norm_num)
theorem B1450781 : Blo 570811 1450781 := bbase (se 3 (by rfl) ⟨272021, by rfl⟩ : syracuseStep 1450781 = 544043) (by norm_num)
theorem B860957 : Blo 570811 860957 := bbase (se 3 (by rfl) ⟨161429, by rfl⟩ : syracuseStep 860957 = 322859) (by norm_num)
theorem B860981 : Blo 570811 860981 := bbase (se 5 (by rfl) ⟨40358, by rfl⟩ : syracuseStep 860981 = 80717) (by norm_num)
theorem B1286981 : Blo 570811 1286981 := bbase (se 4 (by rfl) ⟨120654, by rfl⟩ : syracuseStep 1286981 = 241309) (by norm_num)
theorem B861005 : Blo 570811 861005 := bbase (se 3 (by rfl) ⟨161438, by rfl⟩ : syracuseStep 861005 = 322877) (by norm_num)
theorem B861029 : Blo 570811 861029 := bbase (se 4 (by rfl) ⟨80721, by rfl⟩ : syracuseStep 861029 = 161443) (by norm_num)
theorem B861053 : Blo 570811 861053 := bbase (se 3 (by rfl) ⟨161447, by rfl⟩ : syracuseStep 861053 = 322895) (by norm_num)
theorem B1287053 : Blo 570811 1287053 := bbase (se 3 (by rfl) ⟨241322, by rfl⟩ : syracuseStep 1287053 = 482645) (by norm_num)
theorem B861077 : Blo 570811 861077 := bbase (se 6 (by rfl) ⟨20181, by rfl⟩ : syracuseStep 861077 = 40363) (by norm_num)
theorem B861101 : Blo 570811 861101 := bbase (se 3 (by rfl) ⟨161456, by rfl⟩ : syracuseStep 861101 = 322913) (by norm_num)
theorem B1090493 : Blo 570811 1090493 := bbase (se 3 (by rfl) ⟨204467, by rfl⟩ : syracuseStep 1090493 = 408935) (by norm_num)
theorem B861125 : Blo 570811 861125 := bbase (se 4 (by rfl) ⟨80730, by rfl⟩ : syracuseStep 861125 = 161461) (by norm_num)
theorem B1287125 : Blo 570811 1287125 := bbase (se 7 (by rfl) ⟨15083, by rfl⟩ : syracuseStep 1287125 = 30167) (by norm_num)
theorem B1450973 : Blo 570811 1450973 := bbase (se 3 (by rfl) ⟨272057, by rfl⟩ : syracuseStep 1450973 = 544115) (by norm_num)
theorem B861149 : Blo 570811 861149 := bbase (se 3 (by rfl) ⟨161465, by rfl⟩ : syracuseStep 861149 = 322931) (by norm_num)
theorem B861173 : Blo 570811 861173 := bbase (se 5 (by rfl) ⟨40367, by rfl⟩ : syracuseStep 861173 = 80735) (by norm_num)
theorem B1221637 : Blo 570811 1221637 := bbase (se 4 (by rfl) ⟨114528, by rfl⟩ : syracuseStep 1221637 = 229057) (by norm_num)
theorem B861197 : Blo 570811 861197 := bbase (se 3 (by rfl) ⟨161474, by rfl⟩ : syracuseStep 861197 = 322949) (by norm_num)
theorem B1287197 : Blo 570811 1287197 := bbase (se 3 (by rfl) ⟨241349, by rfl⟩ : syracuseStep 1287197 = 482699) (by norm_num)
theorem B861221 : Blo 570811 861221 := bbase (se 4 (by rfl) ⟨80739, by rfl⟩ : syracuseStep 861221 = 161479) (by norm_num)
theorem B861245 : Blo 570811 861245 := bbase (se 3 (by rfl) ⟨161483, by rfl⟩ : syracuseStep 861245 = 322967) (by norm_num)
theorem B5022805 : Blo 570811 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B861269 : Blo 570811 861269 := bbase (se 8 (by rfl) ⟨5046, by rfl⟩ : syracuseStep 861269 = 10093) (by norm_num)
theorem B1287269 : Blo 570811 1287269 := bbase (se 4 (by rfl) ⟨120681, by rfl⟩ : syracuseStep 1287269 = 241363) (by norm_num)
theorem B861293 : Blo 570811 861293 := bbase (se 3 (by rfl) ⟨161492, by rfl⟩ : syracuseStep 861293 = 322985) (by norm_num)
theorem B861317 : Blo 570811 861317 := bbase (se 4 (by rfl) ⟨80748, by rfl⟩ : syracuseStep 861317 = 161497) (by norm_num)
theorem B861341 : Blo 570811 861341 := bbase (se 3 (by rfl) ⟨161501, by rfl⟩ : syracuseStep 861341 = 323003) (by norm_num)
theorem B1287341 : Blo 570811 1287341 := bbase (se 3 (by rfl) ⟨241376, by rfl⟩ : syracuseStep 1287341 = 482753) (by norm_num)
theorem B861365 : Blo 570811 861365 := bbase (se 5 (by rfl) ⟨40376, by rfl⟩ : syracuseStep 861365 = 80753) (by norm_num)
theorem B861389 : Blo 570811 861389 := bbase (se 3 (by rfl) ⟨161510, by rfl⟩ : syracuseStep 861389 = 323021) (by norm_num)
theorem B861413 : Blo 570811 861413 := bbase (se 4 (by rfl) ⟨80757, by rfl⟩ : syracuseStep 861413 = 161515) (by norm_num)
theorem B1287413 : Blo 570811 1287413 := bbase (se 5 (by rfl) ⟨60347, by rfl⟩ : syracuseStep 1287413 = 120695) (by norm_num)
theorem B861437 : Blo 570811 861437 := bbase (se 3 (by rfl) ⟨161519, by rfl⟩ : syracuseStep 861437 = 323039) (by norm_num)
theorem B861461 : Blo 570811 861461 := bbase (se 6 (by rfl) ⟨20190, by rfl⟩ : syracuseStep 861461 = 40381) (by norm_num)
theorem B861485 : Blo 570811 861485 := bbase (se 3 (by rfl) ⟨161528, by rfl⟩ : syracuseStep 861485 = 323057) (by norm_num)
theorem B1451317 : Blo 570811 1451317 := bbase (se 5 (by rfl) ⟨68030, by rfl⟩ : syracuseStep 1451317 = 136061) (by norm_num)
theorem B1287485 : Blo 570811 1287485 := bbase (se 3 (by rfl) ⟨241403, by rfl⟩ : syracuseStep 1287485 = 482807) (by norm_num)
theorem B861509 : Blo 570811 861509 := bbase (se 4 (by rfl) ⟨80766, by rfl⟩ : syracuseStep 861509 = 161533) (by norm_num)
theorem B861533 : Blo 570811 861533 := bbase (se 3 (by rfl) ⟨161537, by rfl⟩ : syracuseStep 861533 = 323075) (by norm_num)
theorem B2893157 : Blo 570811 2893157 := bbase (se 4 (by rfl) ⟨271233, by rfl⟩ : syracuseStep 2893157 = 542467) (by norm_num)
theorem B861557 : Blo 570811 861557 := bbase (se 5 (by rfl) ⟨40385, by rfl⟩ : syracuseStep 861557 = 80771) (by norm_num)
theorem B1287557 : Blo 570811 1287557 := bbase (se 4 (by rfl) ⟨120708, by rfl⟩ : syracuseStep 1287557 = 241417) (by norm_num)
theorem B861581 : Blo 570811 861581 := bbase (se 3 (by rfl) ⟨161546, by rfl⟩ : syracuseStep 861581 = 323093) (by norm_num)
theorem B1451429 : Blo 570811 1451429 := bbase (se 4 (by rfl) ⟨136071, by rfl⟩ : syracuseStep 1451429 = 272143) (by norm_num)
theorem B861605 : Blo 570811 861605 := bbase (se 4 (by rfl) ⟨80775, by rfl⟩ : syracuseStep 861605 = 161551) (by norm_num)
theorem B861629 : Blo 570811 861629 := bbase (se 3 (by rfl) ⟨161555, by rfl⟩ : syracuseStep 861629 = 323111) (by norm_num)
theorem B1287629 : Blo 570811 1287629 := bbase (se 3 (by rfl) ⟨241430, by rfl⟩ : syracuseStep 1287629 = 482861) (by norm_num)
theorem B861653 : Blo 570811 861653 := bbase (se 7 (by rfl) ⟨10097, by rfl⟩ : syracuseStep 861653 = 20195) (by norm_num)
theorem B697837 : Blo 570811 697837 := bbase (se 3 (by rfl) ⟨130844, by rfl⟩ : syracuseStep 697837 = 261689) (by norm_num)
theorem B861677 : Blo 570811 861677 := bbase (se 3 (by rfl) ⟨161564, by rfl⟩ : syracuseStep 861677 = 323129) (by norm_num)
theorem B1222141 : Blo 570811 1222141 := bbase (se 3 (by rfl) ⟨229151, by rfl⟩ : syracuseStep 1222141 = 458303) (by norm_num)
theorem B861701 : Blo 570811 861701 := bbase (se 4 (by rfl) ⟨80784, by rfl⟩ : syracuseStep 861701 = 161569) (by norm_num)
theorem B1287701 : Blo 570811 1287701 := bbase (se 6 (by rfl) ⟨30180, by rfl⟩ : syracuseStep 1287701 = 60361) (by norm_num)
theorem B861725 : Blo 570811 861725 := bbase (se 3 (by rfl) ⟨161573, by rfl⟩ : syracuseStep 861725 = 323147) (by norm_num)
theorem B861749 : Blo 570811 861749 := bbase (se 5 (by rfl) ⟨40394, by rfl⟩ : syracuseStep 861749 = 80789) (by norm_num)
theorem B861773 : Blo 570811 861773 := bbase (se 3 (by rfl) ⟨161582, by rfl⟩ : syracuseStep 861773 = 323165) (by norm_num)
theorem B1746517 : Blo 570811 1746517 := bbase (se 8 (by rfl) ⟨10233, by rfl⟩ : syracuseStep 1746517 = 20467) (by norm_num)
theorem B1287773 : Blo 570811 1287773 := bbase (se 3 (by rfl) ⟨241457, by rfl⟩ : syracuseStep 1287773 = 482915) (by norm_num)
theorem B1451621 : Blo 570811 1451621 := bbase (se 4 (by rfl) ⟨136089, by rfl⟩ : syracuseStep 1451621 = 272179) (by norm_num)
theorem B861797 : Blo 570811 861797 := bbase (se 4 (by rfl) ⟨80793, by rfl⟩ : syracuseStep 861797 = 161587) (by norm_num)
theorem B861821 : Blo 570811 861821 := bbase (se 3 (by rfl) ⟨161591, by rfl⟩ : syracuseStep 861821 = 323183) (by norm_num)
theorem B861845 : Blo 570811 861845 := bbase (se 6 (by rfl) ⟨20199, by rfl⟩ : syracuseStep 861845 = 40399) (by norm_num)
theorem B1287845 : Blo 570811 1287845 := bbase (se 4 (by rfl) ⟨120735, by rfl⟩ : syracuseStep 1287845 = 241471) (by norm_num)
theorem B861869 : Blo 570811 861869 := bbase (se 3 (by rfl) ⟨161600, by rfl⟩ : syracuseStep 861869 = 323201) (by norm_num)
theorem B1091245 : Blo 570811 1091245 := bbase (se 3 (by rfl) ⟨204608, by rfl⟩ : syracuseStep 1091245 = 409217) (by norm_num)
theorem B861893 : Blo 570811 861893 := bbase (se 4 (by rfl) ⟨80802, by rfl⟩ : syracuseStep 861893 = 161605) (by norm_num)
theorem B861917 : Blo 570811 861917 := bbase (se 3 (by rfl) ⟨161609, by rfl⟩ : syracuseStep 861917 = 323219) (by norm_num)
theorem B1287917 : Blo 570811 1287917 := bbase (se 3 (by rfl) ⟨241484, by rfl⟩ : syracuseStep 1287917 = 482969) (by norm_num)
theorem B861941 : Blo 570811 861941 := bbase (se 5 (by rfl) ⟨40403, by rfl⟩ : syracuseStep 861941 = 80807) (by norm_num)
theorem B861965 : Blo 570811 861965 := bbase (se 3 (by rfl) ⟨161618, by rfl⟩ : syracuseStep 861965 = 323237) (by norm_num)
theorem B861989 : Blo 570811 861989 := bbase (se 4 (by rfl) ⟨80811, by rfl⟩ : syracuseStep 861989 = 161623) (by norm_num)
theorem B1287989 : Blo 570811 1287989 := bbase (se 5 (by rfl) ⟨60374, by rfl⟩ : syracuseStep 1287989 = 120749) (by norm_num)
theorem B862013 : Blo 570811 862013 := bbase (se 3 (by rfl) ⟨161627, by rfl⟩ : syracuseStep 862013 = 323255) (by norm_num)
theorem B862037 : Blo 570811 862037 := bbase (se 9 (by rfl) ⟨2525, by rfl⟩ : syracuseStep 862037 = 5051) (by norm_num)
theorem B862061 : Blo 570811 862061 := bbase (se 3 (by rfl) ⟨161636, by rfl⟩ : syracuseStep 862061 = 323273) (by norm_num)
theorem B1288061 : Blo 570811 1288061 := bbase (se 3 (by rfl) ⟨241511, by rfl⟩ : syracuseStep 1288061 = 483023) (by norm_num)
theorem B862085 : Blo 570811 862085 := bbase (se 4 (by rfl) ⟨80820, by rfl⟩ : syracuseStep 862085 = 161641) (by norm_num)
theorem B829325 : Blo 570811 829325 := bbase (se 3 (by rfl) ⟨155498, by rfl⟩ : syracuseStep 829325 = 310997) (by norm_num)
theorem B3254165 : Blo 570811 3254165 := bbase (se 6 (by rfl) ⟨76269, by rfl⟩ : syracuseStep 3254165 = 152539) (by norm_num)
theorem B862109 : Blo 570811 862109 := bbase (se 3 (by rfl) ⟨161645, by rfl⟩ : syracuseStep 862109 = 323291) (by norm_num)
theorem B862133 : Blo 570811 862133 := bbase (se 5 (by rfl) ⟨40412, by rfl⟩ : syracuseStep 862133 = 80825) (by norm_num)
theorem B1451965 : Blo 570811 1451965 := bbase (se 3 (by rfl) ⟨272243, by rfl⟩ : syracuseStep 1451965 = 544487) (by norm_num)
theorem B1288133 : Blo 570811 1288133 := bbase (se 4 (by rfl) ⟨120762, by rfl⟩ : syracuseStep 1288133 = 241525) (by norm_num)
theorem B862157 : Blo 570811 862157 := bbase (se 3 (by rfl) ⟨161654, by rfl⟩ : syracuseStep 862157 = 323309) (by norm_num)
theorem B862181 : Blo 570811 862181 := bbase (se 4 (by rfl) ⟨80829, by rfl⟩ : syracuseStep 862181 = 161659) (by norm_num)
theorem B4335605 : Blo 570811 4335605 := bbase (se 5 (by rfl) ⟨203231, by rfl⟩ : syracuseStep 4335605 = 406463) (by norm_num)
theorem B862205 : Blo 570811 862205 := bbase (se 3 (by rfl) ⟨161663, by rfl⟩ : syracuseStep 862205 = 323327) (by norm_num)
theorem B1288205 : Blo 570811 1288205 := bbase (se 3 (by rfl) ⟨241538, by rfl⟩ : syracuseStep 1288205 = 483077) (by norm_num)
theorem B1452077 : Blo 570811 1452077 := bbase (se 3 (by rfl) ⟨272264, by rfl⟩ : syracuseStep 1452077 = 544529) (by norm_num)
theorem B2173013 : Blo 570811 2173013 := bbase (se 8 (by rfl) ⟨12732, by rfl⟩ : syracuseStep 2173013 = 25465) (by norm_num)
theorem B1288277 : Blo 570811 1288277 := bbase (se 8 (by rfl) ⟨7548, by rfl⟩ : syracuseStep 1288277 = 15097) (by norm_num)
theorem B1288349 : Blo 570811 1288349 := bbase (se 3 (by rfl) ⟨241565, by rfl⟩ : syracuseStep 1288349 = 483131) (by norm_num)
theorem B1288421 : Blo 570811 1288421 := bbase (se 4 (by rfl) ⟨120789, by rfl⟩ : syracuseStep 1288421 = 241579) (by norm_num)
theorem B1452269 : Blo 570811 1452269 := bbase (se 3 (by rfl) ⟨272300, by rfl⟩ : syracuseStep 1452269 = 544601) (by norm_num)
theorem B1288493 : Blo 570811 1288493 := bbase (se 3 (by rfl) ⟨241592, by rfl⟩ : syracuseStep 1288493 = 483185) (by norm_num)
theorem B2173301 : Blo 570811 2173301 := bbase (se 5 (by rfl) ⟨101873, by rfl⟩ : syracuseStep 2173301 = 203747) (by norm_num)
theorem B1223029 : Blo 570811 1223029 := bbase (se 5 (by rfl) ⟨57329, by rfl⟩ : syracuseStep 1223029 = 114659) (by norm_num)
theorem B1288565 : Blo 570811 1288565 := bbase (se 5 (by rfl) ⟨60401, by rfl⟩ : syracuseStep 1288565 = 120803) (by norm_num)
theorem B1288637 : Blo 570811 1288637 := bbase (se 3 (by rfl) ⟨241619, by rfl⟩ : syracuseStep 1288637 = 483239) (by norm_num)
theorem B1288709 : Blo 570811 1288709 := bbase (se 4 (by rfl) ⟨120816, by rfl⟩ : syracuseStep 1288709 = 241633) (by norm_num)
theorem B1452613 : Blo 570811 1452613 := bbase (se 4 (by rfl) ⟨136182, by rfl⟩ : syracuseStep 1452613 = 272365) (by norm_num)
theorem B1288781 : Blo 570811 1288781 := bbase (se 3 (by rfl) ⟨241646, by rfl⟩ : syracuseStep 1288781 = 483293) (by norm_num)
theorem B2894453 : Blo 570811 2894453 := bbase (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) (by norm_num)
theorem B1288853 : Blo 570811 1288853 := bbase (se 6 (by rfl) ⟨30207, by rfl⟩ : syracuseStep 1288853 = 60415) (by norm_num)
theorem B1452725 : Blo 570811 1452725 := bbase (se 5 (by rfl) ⟨68096, by rfl⟩ : syracuseStep 1452725 = 136193) (by norm_num)
theorem B1288925 : Blo 570811 1288925 := bbase (se 3 (by rfl) ⟨241673, by rfl⟩ : syracuseStep 1288925 = 483347) (by norm_num)
theorem B1288997 : Blo 570811 1288997 := bbase (se 4 (by rfl) ⟨120843, by rfl⟩ : syracuseStep 1288997 = 241687) (by norm_num)
theorem B1223525 : Blo 570811 1223525 := bbase (se 4 (by rfl) ⟨114705, by rfl⟩ : syracuseStep 1223525 = 229411) (by norm_num)
theorem B1289069 : Blo 570811 1289069 := bbase (se 3 (by rfl) ⟨241700, by rfl⟩ : syracuseStep 1289069 = 483401) (by norm_num)
theorem B1452917 : Blo 570811 1452917 := bbase (se 5 (by rfl) ⟨68105, by rfl⟩ : syracuseStep 1452917 = 136211) (by norm_num)
theorem B1289141 : Blo 570811 1289141 := bbase (se 5 (by rfl) ⟨60428, by rfl⟩ : syracuseStep 1289141 = 120857) (by norm_num)
theorem B1158085 : Blo 570811 1158085 := bbase (se 4 (by rfl) ⟨108570, by rfl⟩ : syracuseStep 1158085 = 217141) (by norm_num)
theorem B1289213 : Blo 570811 1289213 := bbase (se 3 (by rfl) ⟨241727, by rfl⟩ : syracuseStep 1289213 = 483455) (by norm_num)
theorem B3255349 : Blo 570811 3255349 := bbase (se 5 (by rfl) ⟨152594, by rfl⟩ : syracuseStep 3255349 = 305189) (by norm_num)
theorem B1289285 : Blo 570811 1289285 := bbase (se 4 (by rfl) ⟨120870, by rfl⟩ : syracuseStep 1289285 = 241741) (by norm_num)
theorem B1289357 : Blo 570811 1289357 := bbase (se 3 (by rfl) ⟨241754, by rfl⟩ : syracuseStep 1289357 = 483509) (by norm_num)
theorem B1453261 : Blo 570811 1453261 := bbase (se 3 (by rfl) ⟨272486, by rfl⟩ : syracuseStep 1453261 = 544973) (by norm_num)
theorem B1289429 : Blo 570811 1289429 := bbase (se 7 (by rfl) ⟨15110, by rfl⟩ : syracuseStep 1289429 = 30221) (by norm_num)
theorem B1289501 : Blo 570811 1289501 := bbase (se 3 (by rfl) ⟨241781, by rfl⟩ : syracuseStep 1289501 = 483563) (by norm_num)
theorem B1453373 : Blo 570811 1453373 := bbase (se 3 (by rfl) ⟨272507, by rfl⟩ : syracuseStep 1453373 = 545015) (by norm_num)
theorem B1289573 : Blo 570811 1289573 := bbase (se 4 (by rfl) ⟨120897, by rfl⟩ : syracuseStep 1289573 = 241795) (by norm_num)
theorem B1289645 : Blo 570811 1289645 := bbase (se 3 (by rfl) ⟨241808, by rfl⟩ : syracuseStep 1289645 = 483617) (by norm_num)
theorem B5385685 : Blo 570811 5385685 := bbase (se 7 (by rfl) ⟨63113, by rfl⟩ : syracuseStep 5385685 = 126227) (by norm_num)
theorem B1289717 : Blo 570811 1289717 := bbase (se 5 (by rfl) ⟨60455, by rfl⟩ : syracuseStep 1289717 = 120911) (by norm_num)
theorem B1453565 : Blo 570811 1453565 := bbase (se 3 (by rfl) ⟨272543, by rfl⟩ : syracuseStep 1453565 = 545087) (by norm_num)
theorem B2174485 : Blo 570811 2174485 := bbase (se 6 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 2174485 = 101929) (by norm_num)
theorem B1289789 : Blo 570811 1289789 := bbase (se 3 (by rfl) ⟨241835, by rfl⟩ : syracuseStep 1289789 = 483671) (by norm_num)
theorem B1289861 : Blo 570811 1289861 := bbase (se 4 (by rfl) ⟨120924, by rfl⟩ : syracuseStep 1289861 = 241849) (by norm_num)
theorem B1289933 : Blo 570811 1289933 := bbase (se 3 (by rfl) ⟨241862, by rfl⟩ : syracuseStep 1289933 = 483725) (by norm_num)
theorem B1224413 : Blo 570811 1224413 := bbase (se 3 (by rfl) ⟨229577, by rfl⟩ : syracuseStep 1224413 = 459155) (by norm_num)
theorem B1290005 : Blo 570811 1290005 := bbase (se 6 (by rfl) ⟨30234, by rfl⟩ : syracuseStep 1290005 = 60469) (by norm_num)
theorem B2174789 : Blo 570811 2174789 := bbase (se 4 (by rfl) ⟨203886, by rfl⟩ : syracuseStep 2174789 = 407773) (by norm_num)
theorem B1224533 : Blo 570811 1224533 := bbase (se 9 (by rfl) ⟨3587, by rfl⟩ : syracuseStep 1224533 = 7175) (by norm_num)
theorem B1453909 : Blo 570811 1453909 := bbase (se 9 (by rfl) ⟨4259, by rfl⟩ : syracuseStep 1453909 = 8519) (by norm_num)
theorem B1290077 : Blo 570811 1290077 := bbase (se 3 (by rfl) ⟨241889, by rfl⟩ : syracuseStep 1290077 = 483779) (by norm_num)
theorem B2895749 : Blo 570811 2895749 := bbase (se 4 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 2895749 = 542953) (by norm_num)
theorem B1290149 : Blo 570811 1290149 := bbase (se 4 (by rfl) ⟨120951, by rfl⟩ : syracuseStep 1290149 = 241903) (by norm_num)
theorem B1454021 : Blo 570811 1454021 := bbase (se 4 (by rfl) ⟨136314, by rfl⟩ : syracuseStep 1454021 = 272629) (by norm_num)
theorem B1290221 : Blo 570811 1290221 := bbase (se 3 (by rfl) ⟨241916, by rfl⟩ : syracuseStep 1290221 = 483833) (by norm_num)
theorem B1159213 : Blo 570811 1159213 := bbase (se 3 (by rfl) ⟨217352, by rfl⟩ : syracuseStep 1159213 = 434705) (by norm_num)
theorem B1290293 : Blo 570811 1290293 := bbase (se 5 (by rfl) ⟨60482, by rfl⟩ : syracuseStep 1290293 = 120965) (by norm_num)
theorem B1290365 : Blo 570811 1290365 := bbase (se 3 (by rfl) ⟨241943, by rfl⟩ : syracuseStep 1290365 = 483887) (by norm_num)
theorem B1454213 : Blo 570811 1454213 := bbase (se 4 (by rfl) ⟨136332, by rfl⟩ : syracuseStep 1454213 = 272665) (by norm_num)
theorem B1290437 : Blo 570811 1290437 := bbase (se 4 (by rfl) ⟨120978, by rfl⟩ : syracuseStep 1290437 = 241957) (by norm_num)
theorem B1290509 : Blo 570811 1290509 := bbase (se 3 (by rfl) ⟨241970, by rfl⟩ : syracuseStep 1290509 = 483941) (by norm_num)
theorem B1290581 : Blo 570811 1290581 := bbase (se 10 (by rfl) ⟨1890, by rfl⟩ : syracuseStep 1290581 = 3781) (by norm_num)
theorem B1290653 : Blo 570811 1290653 := bbase (se 3 (by rfl) ⟨241997, by rfl⟩ : syracuseStep 1290653 = 483995) (by norm_num)
theorem B1225165 : Blo 570811 1225165 := bbase (se 3 (by rfl) ⟨229718, by rfl⟩ : syracuseStep 1225165 = 459437) (by norm_num)
theorem B1454557 : Blo 570811 1454557 := bbase (se 3 (by rfl) ⟨272729, by rfl⟩ : syracuseStep 1454557 = 545459) (by norm_num)
theorem B1290725 : Blo 570811 1290725 := bbase (se 4 (by rfl) ⟨121005, by rfl⟩ : syracuseStep 1290725 = 242011) (by norm_num)
theorem B1290797 : Blo 570811 1290797 := bbase (se 3 (by rfl) ⟨242024, by rfl⟩ : syracuseStep 1290797 = 484049) (by norm_num)
theorem B1454669 : Blo 570811 1454669 := bbase (se 3 (by rfl) ⟨272750, by rfl⟩ : syracuseStep 1454669 = 545501) (by norm_num)
theorem B1290869 : Blo 570811 1290869 := bbase (se 5 (by rfl) ⟨60509, by rfl⟩ : syracuseStep 1290869 = 121019) (by norm_num)
theorem B963245 : Blo 570811 963245 := bbase (se 3 (by rfl) ⟨180608, by rfl⟩ : syracuseStep 963245 = 361217) (by norm_num)
theorem B1290941 : Blo 570811 1290941 := bbase (se 3 (by rfl) ⟨242051, by rfl⟩ : syracuseStep 1290941 = 484103) (by norm_num)
theorem B1159901 : Blo 570811 1159901 := bbase (se 3 (by rfl) ⟨217481, by rfl⟩ : syracuseStep 1159901 = 434963) (by norm_num)
theorem B1159933 : Blo 570811 1159933 := bbase (se 3 (by rfl) ⟨217487, by rfl⟩ : syracuseStep 1159933 = 434975) (by norm_num)
theorem B1291013 : Blo 570811 1291013 := bbase (se 4 (by rfl) ⟨121032, by rfl⟩ : syracuseStep 1291013 = 242065) (by norm_num)
theorem B1454861 : Blo 570811 1454861 := bbase (se 3 (by rfl) ⟨272786, by rfl⟩ : syracuseStep 1454861 = 545573) (by norm_num)
theorem B963373 : Blo 570811 963373 := bbase (se 3 (by rfl) ⟨180632, by rfl⟩ : syracuseStep 963373 = 361265) (by norm_num)
theorem B734017 : Blo 570811 734017 := bbase (se 2 (by rfl) ⟨275256, by rfl⟩ : syracuseStep 734017 = 550513) (by norm_num)
theorem B1028933 : Blo 570811 1028933 := bbase (se 4 (by rfl) ⟨96462, by rfl⟩ : syracuseStep 1028933 = 192925) (by norm_num)
theorem B1291085 : Blo 570811 1291085 := bbase (se 3 (by rfl) ⟨242078, by rfl⟩ : syracuseStep 1291085 = 484157) (by norm_num)
theorem B963461 : Blo 570811 963461 := bbase (se 4 (by rfl) ⟨90324, by rfl⟩ : syracuseStep 963461 = 180649) (by norm_num)
theorem B1291157 : Blo 570811 1291157 := bbase (se 6 (by rfl) ⟨30261, by rfl⟩ : syracuseStep 1291157 = 60523) (by norm_num)
theorem B1291229 : Blo 570811 1291229 := bbase (se 3 (by rfl) ⟨242105, by rfl⟩ : syracuseStep 1291229 = 484211) (by norm_num)
theorem B3257333 : Blo 570811 3257333 := bbase (se 5 (by rfl) ⟨152687, by rfl⟩ : syracuseStep 3257333 = 305375) (by norm_num)
theorem B963589 : Blo 570811 963589 := bbase (se 4 (by rfl) ⟨90336, by rfl⟩ : syracuseStep 963589 = 180673) (by norm_num)
theorem B1291301 : Blo 570811 1291301 := bbase (se 4 (by rfl) ⟨121059, by rfl⟩ : syracuseStep 1291301 = 242119) (by norm_num)
theorem B963677 : Blo 570811 963677 := bbase (se 3 (by rfl) ⟨180689, by rfl⟩ : syracuseStep 963677 = 361379) (by norm_num)
theorem B1291373 : Blo 570811 1291373 := bbase (se 3 (by rfl) ⟨242132, by rfl⟩ : syracuseStep 1291373 = 484265) (by norm_num)
theorem B2897045 : Blo 570811 2897045 := bbase (se 6 (by rfl) ⟨67899, by rfl⟩ : syracuseStep 2897045 = 135799) (by norm_num)
theorem B1291445 : Blo 570811 1291445 := bbase (se 5 (by rfl) ⟨60536, by rfl⟩ : syracuseStep 1291445 = 121073) (by norm_num)
theorem B963805 : Blo 570811 963805 := bbase (se 3 (by rfl) ⟨180713, by rfl⟩ : syracuseStep 963805 = 361427) (by norm_num)
theorem B1291517 : Blo 570811 1291517 := bbase (se 3 (by rfl) ⟨242159, by rfl⟩ : syracuseStep 1291517 = 484319) (by norm_num)
theorem B2438437 : Blo 570811 2438437 := bbase (se 4 (by rfl) ⟨228603, by rfl⟩ : syracuseStep 2438437 = 457207) (by norm_num)
theorem B734513 : Blo 570811 734513 := bbase (se 2 (by rfl) ⟨275442, by rfl⟩ : syracuseStep 734513 = 550885) (by norm_num)
theorem B963893 : Blo 570811 963893 := bbase (se 5 (by rfl) ⟨45182, by rfl⟩ : syracuseStep 963893 = 90365) (by norm_num)
theorem B1029437 : Blo 570811 1029437 := bbase (se 3 (by rfl) ⟨193019, by rfl⟩ : syracuseStep 1029437 = 386039) (by norm_num)
theorem B1291589 : Blo 570811 1291589 := bbase (se 4 (by rfl) ⟨121086, by rfl⟩ : syracuseStep 1291589 = 242173) (by norm_num)
theorem B1226053 : Blo 570811 1226053 := bbase (se 4 (by rfl) ⟨114942, by rfl⟩ : syracuseStep 1226053 = 229885) (by norm_num)
theorem B1291661 : Blo 570811 1291661 := bbase (se 3 (by rfl) ⟨242186, by rfl⟩ : syracuseStep 1291661 = 484373) (by norm_num)
theorem B964021 : Blo 570811 964021 := bbase (se 5 (by rfl) ⟨45188, by rfl⟩ : syracuseStep 964021 = 90377) (by norm_num)
theorem B1226173 : Blo 570811 1226173 := bbase (se 3 (by rfl) ⟨229907, by rfl⟩ : syracuseStep 1226173 = 459815) (by norm_num)
theorem B1291733 : Blo 570811 1291733 := bbase (se 7 (by rfl) ⟨15137, by rfl⟩ : syracuseStep 1291733 = 30275) (by norm_num)
theorem B964109 : Blo 570811 964109 := bbase (se 3 (by rfl) ⟨180770, by rfl⟩ : syracuseStep 964109 = 361541) (by norm_num)
theorem B1291805 : Blo 570811 1291805 := bbase (se 3 (by rfl) ⟨242213, by rfl⟩ : syracuseStep 1291805 = 484427) (by norm_num)
theorem B1291877 : Blo 570811 1291877 := bbase (se 4 (by rfl) ⟨121113, by rfl⟩ : syracuseStep 1291877 = 242227) (by norm_num)
theorem B964237 : Blo 570811 964237 := bbase (se 3 (by rfl) ⟨180794, by rfl⟩ : syracuseStep 964237 = 361589) (by norm_num)
theorem B1291949 : Blo 570811 1291949 := bbase (se 3 (by rfl) ⟨242240, by rfl⟩ : syracuseStep 1291949 = 484481) (by norm_num)
theorem B1226429 : Blo 570811 1226429 := bbase (se 3 (by rfl) ⟨229955, by rfl⟩ : syracuseStep 1226429 = 459911) (by norm_num)
theorem B964325 : Blo 570811 964325 := bbase (se 4 (by rfl) ⟨90405, by rfl⟩ : syracuseStep 964325 = 180811) (by norm_num)
theorem B1292021 : Blo 570811 1292021 := bbase (se 5 (by rfl) ⟨60563, by rfl⟩ : syracuseStep 1292021 = 121127) (by norm_num)
theorem B1292093 : Blo 570811 1292093 := bbase (se 3 (by rfl) ⟨242267, by rfl⟩ : syracuseStep 1292093 = 484535) (by norm_num)
theorem B1161029 : Blo 570811 1161029 := bbase (se 4 (by rfl) ⟨108846, by rfl⟩ : syracuseStep 1161029 = 217693) (by norm_num)
theorem B964453 : Blo 570811 964453 := bbase (se 4 (by rfl) ⟨90417, by rfl⟩ : syracuseStep 964453 = 180835) (by norm_num)
theorem B2176901 : Blo 570811 2176901 := bbase (se 4 (by rfl) ⟨204084, by rfl⟩ : syracuseStep 2176901 = 408169) (by norm_num)
theorem B1292165 : Blo 570811 1292165 := bbase (se 4 (by rfl) ⟨121140, by rfl⟩ : syracuseStep 1292165 = 242281) (by norm_num)
theorem B1161101 : Blo 570811 1161101 := bbase (se 3 (by rfl) ⟨217706, by rfl⟩ : syracuseStep 1161101 = 435413) (by norm_num)
theorem B964541 : Blo 570811 964541 := bbase (se 3 (by rfl) ⟨180851, by rfl⟩ : syracuseStep 964541 = 361703) (by norm_num)
theorem B1292237 : Blo 570811 1292237 := bbase (se 3 (by rfl) ⟨242294, by rfl⟩ : syracuseStep 1292237 = 484589) (by norm_num)
theorem B2439173 : Blo 570811 2439173 := bbase (se 4 (by rfl) ⟨228672, by rfl⟩ : syracuseStep 2439173 = 457345) (by norm_num)
theorem B1292309 : Blo 570811 1292309 := bbase (se 6 (by rfl) ⟨30288, by rfl⟩ : syracuseStep 1292309 = 60577) (by norm_num)
theorem B964669 : Blo 570811 964669 := bbase (se 3 (by rfl) ⟨180875, by rfl⟩ : syracuseStep 964669 = 361751) (by norm_num)
theorem B1292381 : Blo 570811 1292381 := bbase (se 3 (by rfl) ⟨242321, by rfl⟩ : syracuseStep 1292381 = 484643) (by norm_num)
theorem B964757 : Blo 570811 964757 := bbase (se 6 (by rfl) ⟨22611, by rfl⟩ : syracuseStep 964757 = 45223) (by norm_num)
theorem B2177189 : Blo 570811 2177189 := bbase (se 4 (by rfl) ⟨204111, by rfl⟩ : syracuseStep 2177189 = 408223) (by norm_num)
theorem B1292453 : Blo 570811 1292453 := bbase (se 4 (by rfl) ⟨121167, by rfl⟩ : syracuseStep 1292453 = 242335) (by norm_num)
theorem B1292525 : Blo 570811 1292525 := bbase (se 3 (by rfl) ⟨242348, by rfl⟩ : syracuseStep 1292525 = 484697) (by norm_num)
theorem B964885 : Blo 570811 964885 := bbase (se 6 (by rfl) ⟨22614, by rfl⟩ : syracuseStep 964885 = 45229) (by norm_num)
theorem B1292597 : Blo 570811 1292597 := bbase (se 5 (by rfl) ⟨60590, by rfl⟩ : syracuseStep 1292597 = 121181) (by norm_num)
theorem B964973 : Blo 570811 964973 := bbase (se 3 (by rfl) ⟨180932, by rfl⟩ : syracuseStep 964973 = 361865) (by norm_num)
theorem B1292669 : Blo 570811 1292669 := bbase (se 3 (by rfl) ⟨242375, by rfl⟩ : syracuseStep 1292669 = 484751) (by norm_num)
theorem B2898341 : Blo 570811 2898341 := bbase (se 4 (by rfl) ⟨271719, by rfl⟩ : syracuseStep 2898341 = 543439) (by norm_num)
theorem B1292741 : Blo 570811 1292741 := bbase (se 4 (by rfl) ⟨121194, by rfl⟩ : syracuseStep 1292741 = 242389) (by norm_num)
theorem B965101 : Blo 570811 965101 := bbase (se 3 (by rfl) ⟨180956, by rfl⟩ : syracuseStep 965101 = 361913) (by norm_num)
theorem B1292813 : Blo 570811 1292813 := bbase (se 3 (by rfl) ⟨242402, by rfl⟩ : syracuseStep 1292813 = 484805) (by norm_num)
theorem B1227317 : Blo 570811 1227317 := bbase (se 5 (by rfl) ⟨57530, by rfl⟩ : syracuseStep 1227317 = 115061) (by norm_num)
theorem B965189 : Blo 570811 965189 := bbase (se 4 (by rfl) ⟨90486, by rfl⟩ : syracuseStep 965189 = 180973) (by norm_num)
theorem B1292885 : Blo 570811 1292885 := bbase (se 8 (by rfl) ⟨7575, by rfl⟩ : syracuseStep 1292885 = 15151) (by norm_num)
theorem B1292957 : Blo 570811 1292957 := bbase (se 3 (by rfl) ⟨242429, by rfl⟩ : syracuseStep 1292957 = 484859) (by norm_num)
theorem B965317 : Blo 570811 965317 := bbase (se 4 (by rfl) ⟨90498, by rfl⟩ : syracuseStep 965317 = 180997) (by norm_num)
theorem B1293029 : Blo 570811 1293029 := bbase (se 4 (by rfl) ⟨121221, by rfl⟩ : syracuseStep 1293029 = 242443) (by norm_num)
theorem B965405 : Blo 570811 965405 := bbase (se 3 (by rfl) ⟨181013, by rfl⟩ : syracuseStep 965405 = 362027) (by norm_num)
theorem B1227557 : Blo 570811 1227557 := bbase (se 4 (by rfl) ⟨115083, by rfl⟩ : syracuseStep 1227557 = 230167) (by norm_num)
theorem B1293101 : Blo 570811 1293101 := bbase (se 3 (by rfl) ⟨242456, by rfl⟩ : syracuseStep 1293101 = 484913) (by norm_num)
theorem B1293173 : Blo 570811 1293173 := bbase (se 5 (by rfl) ⟨60617, by rfl⟩ : syracuseStep 1293173 = 121235) (by norm_num)
theorem B965533 : Blo 570811 965533 := bbase (se 3 (by rfl) ⟨181037, by rfl⟩ : syracuseStep 965533 = 362075) (by norm_num)
theorem B1293245 : Blo 570811 1293245 := bbase (se 3 (by rfl) ⟨242483, by rfl⟩ : syracuseStep 1293245 = 484967) (by norm_num)
theorem B965621 : Blo 570811 965621 := bbase (se 5 (by rfl) ⟨45263, by rfl⟩ : syracuseStep 965621 = 90527) (by norm_num)
theorem B1293317 : Blo 570811 1293317 := bbase (se 4 (by rfl) ⟨121248, by rfl⟩ : syracuseStep 1293317 = 242497) (by norm_num)
theorem B6536213 : Blo 570811 6536213 := bbase (se 6 (by rfl) ⟨153192, by rfl⟩ : syracuseStep 6536213 = 306385) (by norm_num)
theorem B965749 : Blo 570811 965749 := bbase (se 5 (by rfl) ⟨45269, by rfl⟩ : syracuseStep 965749 = 90539) (by norm_num)
theorem B3259541 : Blo 570811 3259541 := bbase (se 6 (by rfl) ⟨76395, by rfl⟩ : syracuseStep 3259541 = 152791) (by norm_num)
theorem B11025557 : Blo 570811 11025557 := bbase (se 6 (by rfl) ⟨258411, by rfl⟩ : syracuseStep 11025557 = 516823) (by norm_num)
theorem B965837 : Blo 570811 965837 := bbase (se 3 (by rfl) ⟨181094, by rfl⟩ : syracuseStep 965837 = 362189) (by norm_num)
theorem B933125 : Blo 570811 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B2178373 : Blo 570811 2178373 := bbase (se 4 (by rfl) ⟨204222, by rfl⟩ : syracuseStep 2178373 = 408445) (by norm_num)
theorem B965965 : Blo 570811 965965 := bbase (se 3 (by rfl) ⟨181118, by rfl⟩ : syracuseStep 965965 = 362237) (by norm_num)
theorem B966053 : Blo 570811 966053 := bbase (se 4 (by rfl) ⟨90567, by rfl⟩ : syracuseStep 966053 = 181135) (by norm_num)
theorem B1031629 : Blo 570811 1031629 := bbase (se 3 (by rfl) ⟨193430, by rfl⟩ : syracuseStep 1031629 = 386861) (by norm_num)
theorem B736781 : Blo 570811 736781 := bbase (se 3 (by rfl) ⟨138146, by rfl⟩ : syracuseStep 736781 = 276293) (by norm_num)
theorem B966181 : Blo 570811 966181 := bbase (se 4 (by rfl) ⟨90579, by rfl⟩ : syracuseStep 966181 = 181159) (by norm_num)
theorem B2178677 : Blo 570811 2178677 := bbase (se 5 (by rfl) ⟨102125, by rfl⟩ : syracuseStep 2178677 = 204251) (by norm_num)
theorem B966269 : Blo 570811 966269 := bbase (se 3 (by rfl) ⟨181175, by rfl⟩ : syracuseStep 966269 = 362351) (by norm_num)
theorem B2899637 : Blo 570811 2899637 := bbase (se 5 (by rfl) ⟨135920, by rfl⟩ : syracuseStep 2899637 = 271841) (by norm_num)
theorem B1654501 : Blo 570811 1654501 := bbase (se 4 (by rfl) ⟨155109, by rfl⟩ : syracuseStep 1654501 = 310219) (by norm_num)
theorem B966397 : Blo 570811 966397 := bbase (se 3 (by rfl) ⟨181199, by rfl⟩ : syracuseStep 966397 = 362399) (by norm_num)
theorem B3358549 : Blo 570811 3358549 := bbase (se 9 (by rfl) ⟨9839, by rfl⟩ : syracuseStep 3358549 = 19679) (by norm_num)
theorem B966485 : Blo 570811 966485 := bbase (se 9 (by rfl) ⟨2831, by rfl⟩ : syracuseStep 966485 = 5663) (by norm_num)
theorem B966613 : Blo 570811 966613 := bbase (se 7 (by rfl) ⟨11327, by rfl⟩ : syracuseStep 966613 = 22655) (by norm_num)
theorem B868357 : Blo 570811 868357 := bbase (se 4 (by rfl) ⟨81408, by rfl⟩ : syracuseStep 868357 = 162817) (by norm_num)
theorem B1032205 : Blo 570811 1032205 := bbase (se 3 (by rfl) ⟨193538, by rfl⟩ : syracuseStep 1032205 = 387077) (by norm_num)
theorem B966701 : Blo 570811 966701 := bbase (se 3 (by rfl) ⟨181256, by rfl⟩ : syracuseStep 966701 = 362513) (by norm_num)
theorem B966829 : Blo 570811 966829 := bbase (se 3 (by rfl) ⟨181280, by rfl⟩ : syracuseStep 966829 = 362561) (by norm_num)
theorem B966917 : Blo 570811 966917 := bbase (se 4 (by rfl) ⟨90648, by rfl⟩ : syracuseStep 966917 = 181297) (by norm_num)
theorem B967045 : Blo 570811 967045 := bbase (se 4 (by rfl) ⟨90660, by rfl⟩ : syracuseStep 967045 = 181321) (by norm_num)
theorem B967133 : Blo 570811 967133 := bbase (se 3 (by rfl) ⟨181337, by rfl⟩ : syracuseStep 967133 = 362675) (by norm_num)
theorem B967261 : Blo 570811 967261 := bbase (se 3 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 967261 = 362723) (by norm_num)
theorem B967349 : Blo 570811 967349 := bbase (se 5 (by rfl) ⟨45344, by rfl⟩ : syracuseStep 967349 = 90689) (by norm_num)
theorem B1164037 : Blo 570811 1164037 := bbase (se 4 (by rfl) ⟨109128, by rfl⟩ : syracuseStep 1164037 = 218257) (by norm_num)
theorem B1164053 : Blo 570811 1164053 := bbase (se 6 (by rfl) ⟨27282, by rfl⟩ : syracuseStep 1164053 = 54565) (by norm_num)
theorem B1033013 : Blo 570811 1033013 := bbase (se 5 (by rfl) ⟨48422, by rfl⟩ : syracuseStep 1033013 = 96845) (by norm_num)
theorem B967477 : Blo 570811 967477 := bbase (se 5 (by rfl) ⟨45350, by rfl⟩ : syracuseStep 967477 = 90701) (by norm_num)
theorem B967565 : Blo 570811 967565 := bbase (se 3 (by rfl) ⟨181418, by rfl⟩ : syracuseStep 967565 = 362837) (by norm_num)
theorem B2900933 : Blo 570811 2900933 := bbase (se 4 (by rfl) ⟨271962, by rfl⟩ : syracuseStep 2900933 = 543925) (by norm_num)
theorem B836573 : Blo 570811 836573 := bbase (se 3 (by rfl) ⟨156857, by rfl⟩ : syracuseStep 836573 = 313715) (by norm_num)
theorem B967693 : Blo 570811 967693 := bbase (se 3 (by rfl) ⟨181442, by rfl⟩ : syracuseStep 967693 = 362885) (by norm_num)
theorem B967781 : Blo 570811 967781 := bbase (se 4 (by rfl) ⟨90729, by rfl⟩ : syracuseStep 967781 = 181459) (by norm_num)
theorem B2442469 : Blo 570811 2442469 := bbase (se 4 (by rfl) ⟨228981, by rfl⟩ : syracuseStep 2442469 = 457963) (by norm_num)
theorem B1033445 : Blo 570811 1033445 := bbase (se 4 (by rfl) ⟨96885, by rfl⟩ : syracuseStep 1033445 = 193771) (by norm_num)
theorem B967909 : Blo 570811 967909 := bbase (se 4 (by rfl) ⟨90741, by rfl⟩ : syracuseStep 967909 = 181483) (by norm_num)
theorem B967997 : Blo 570811 967997 := bbase (se 3 (by rfl) ⟨181499, by rfl⟩ : syracuseStep 967997 = 362999) (by norm_num)
theorem B1033589 : Blo 570811 1033589 := bbase (se 5 (by rfl) ⟨48449, by rfl⟩ : syracuseStep 1033589 = 96899) (by norm_num)
theorem B1164661 : Blo 570811 1164661 := bbase (se 5 (by rfl) ⟨54593, by rfl⟩ : syracuseStep 1164661 = 109187) (by norm_num)
theorem B968125 : Blo 570811 968125 := bbase (se 3 (by rfl) ⟨181523, by rfl⟩ : syracuseStep 968125 = 363047) (by norm_num)
theorem B968213 : Blo 570811 968213 := bbase (se 6 (by rfl) ⟨22692, by rfl⟩ : syracuseStep 968213 = 45385) (by norm_num)
theorem B4343381 : Blo 570811 4343381 := bbase (se 8 (by rfl) ⟨25449, by rfl⟩ : syracuseStep 4343381 = 50899) (by norm_num)
theorem B1033813 : Blo 570811 1033813 := bbase (se 8 (by rfl) ⟨6057, by rfl⟩ : syracuseStep 1033813 = 12115) (by norm_num)
theorem B968341 : Blo 570811 968341 := bbase (se 6 (by rfl) ⟨22695, by rfl⟩ : syracuseStep 968341 = 45391) (by norm_num)
theorem B2180789 : Blo 570811 2180789 := bbase (se 5 (by rfl) ⟨102224, by rfl⟩ : syracuseStep 2180789 = 204449) (by norm_num)
theorem B968429 : Blo 570811 968429 := bbase (se 3 (by rfl) ⟨181580, by rfl⟩ : syracuseStep 968429 = 363161) (by norm_num)
theorem B1165117 : Blo 570811 1165117 := bbase (se 3 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 1165117 = 436919) (by norm_num)
theorem B968557 : Blo 570811 968557 := bbase (se 3 (by rfl) ⟨181604, by rfl⟩ : syracuseStep 968557 = 363209) (by norm_num)
theorem B1034165 : Blo 570811 1034165 := bbase (se 5 (by rfl) ⟨48476, by rfl⟩ : syracuseStep 1034165 = 96953) (by norm_num)
theorem B968645 : Blo 570811 968645 := bbase (se 4 (by rfl) ⟨90810, by rfl⟩ : syracuseStep 968645 = 181621) (by norm_num)
theorem B2181077 : Blo 570811 2181077 := bbase (se 7 (by rfl) ⟨25559, by rfl⟩ : syracuseStep 2181077 = 51119) (by norm_num)
theorem B968773 : Blo 570811 968773 := bbase (se 4 (by rfl) ⟨90822, by rfl⟩ : syracuseStep 968773 = 181645) (by norm_num)
theorem B968861 : Blo 570811 968861 := bbase (se 3 (by rfl) ⟨181661, by rfl⟩ : syracuseStep 968861 = 363323) (by norm_num)
theorem B2902229 : Blo 570811 2902229 := bbase (se 7 (by rfl) ⟨34010, by rfl⟩ : syracuseStep 2902229 = 68021) (by norm_num)
theorem B968989 : Blo 570811 968989 := bbase (se 3 (by rfl) ⟨181685, by rfl⟩ : syracuseStep 968989 = 363371) (by norm_num)
theorem B969077 : Blo 570811 969077 := bbase (se 5 (by rfl) ⟨45425, by rfl⟩ : syracuseStep 969077 = 90851) (by norm_num)
theorem B969205 : Blo 570811 969205 := bbase (se 5 (by rfl) ⟨45431, by rfl⟩ : syracuseStep 969205 = 90863) (by norm_num)
theorem B969293 : Blo 570811 969293 := bbase (se 3 (by rfl) ⟨181742, by rfl⟩ : syracuseStep 969293 = 363485) (by norm_num)
theorem B1100477 : Blo 570811 1100477 := bbase (se 3 (by rfl) ⟨206339, by rfl⟩ : syracuseStep 1100477 = 412679) (by norm_num)
theorem B871117 : Blo 570811 871117 := bbase (se 3 (by rfl) ⟨163334, by rfl⟩ : syracuseStep 871117 = 326669) (by norm_num)
theorem B969421 : Blo 570811 969421 := bbase (se 3 (by rfl) ⟨181766, by rfl⟩ : syracuseStep 969421 = 363533) (by norm_num)
theorem B969509 : Blo 570811 969509 := bbase (se 4 (by rfl) ⟨90891, by rfl⟩ : syracuseStep 969509 = 181783) (by norm_num)
theorem B969637 : Blo 570811 969637 := bbase (se 4 (by rfl) ⟨90903, by rfl⟩ : syracuseStep 969637 = 181807) (by norm_num)
theorem B5721013 : Blo 570811 5721013 := bbase (se 5 (by rfl) ⟨268172, by rfl⟩ : syracuseStep 5721013 = 536345) (by norm_num)
theorem B3492821 : Blo 570811 3492821 := bbase (se 7 (by rfl) ⟨40931, by rfl⟩ : syracuseStep 3492821 = 81863) (by norm_num)
theorem B969725 : Blo 570811 969725 := bbase (se 3 (by rfl) ⟨181823, by rfl⟩ : syracuseStep 969725 = 363647) (by norm_num)
theorem B2182261 : Blo 570811 2182261 := bbase (se 5 (by rfl) ⟨102293, by rfl⟩ : syracuseStep 2182261 = 204587) (by norm_num)
theorem B969853 : Blo 570811 969853 := bbase (se 3 (by rfl) ⟨181847, by rfl⟩ : syracuseStep 969853 = 363695) (by norm_num)
theorem B642181 : Blo 570811 642181 := bbase (se 4 (by rfl) ⟨60204, by rfl⟩ : syracuseStep 642181 = 120409) (by norm_num)
theorem B642217 : Blo 570811 642217 := bbase (se 2 (by rfl) ⟨240831, by rfl⟩ : syracuseStep 642217 = 481663) (by norm_num)
theorem B642253 : Blo 570811 642253 := bbase (se 3 (by rfl) ⟨120422, by rfl⟩ : syracuseStep 642253 = 240845) (by norm_num)
theorem B969941 : Blo 570811 969941 := bbase (se 7 (by rfl) ⟨11366, by rfl⟩ : syracuseStep 969941 = 22733) (by norm_num)
theorem B642289 : Blo 570811 642289 := bbase (se 2 (by rfl) ⟨240858, by rfl⟩ : syracuseStep 642289 = 481717) (by norm_num)
theorem B642325 : Blo 570811 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B642361 : Blo 570811 642361 := bbase (se 2 (by rfl) ⟨240885, by rfl⟩ : syracuseStep 642361 = 481771) (by norm_num)
theorem B609601 : Blo 570811 609601 := bbase (se 2 (by rfl) ⟨228600, by rfl⟩ : syracuseStep 609601 = 457201) (by norm_num)
theorem B642397 : Blo 570811 642397 := bbase (se 3 (by rfl) ⟨120449, by rfl⟩ : syracuseStep 642397 = 240899) (by norm_num)
theorem B642433 : Blo 570811 642433 := bbase (se 2 (by rfl) ⟨240912, by rfl⟩ : syracuseStep 642433 = 481825) (by norm_num)
theorem B2477461 : Blo 570811 2477461 := bbase (se 6 (by rfl) ⟨58065, by rfl⟩ : syracuseStep 2477461 = 116131) (by norm_num)
theorem B642469 : Blo 570811 642469 := bbase (se 4 (by rfl) ⟨60231, by rfl⟩ : syracuseStep 642469 = 120463) (by norm_num)
theorem B609725 : Blo 570811 609725 := bbase (se 3 (by rfl) ⟨114323, by rfl⟩ : syracuseStep 609725 = 228647) (by norm_num)
theorem B642505 : Blo 570811 642505 := bbase (se 2 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 642505 = 481879) (by norm_num)
theorem B2903525 : Blo 570811 2903525 := bbase (se 4 (by rfl) ⟨272205, by rfl⟩ : syracuseStep 2903525 = 544411) (by norm_num)
theorem B642541 : Blo 570811 642541 := bbase (se 3 (by rfl) ⟨120476, by rfl⟩ : syracuseStep 642541 = 240953) (by norm_num)
theorem B642577 : Blo 570811 642577 := bbase (se 2 (by rfl) ⟨240966, by rfl⟩ : syracuseStep 642577 = 481933) (by norm_num)
theorem B642613 : Blo 570811 642613 := bbase (se 5 (by rfl) ⟨30122, by rfl⟩ : syracuseStep 642613 = 60245) (by norm_num)
theorem B642649 : Blo 570811 642649 := bbase (se 2 (by rfl) ⟨240993, by rfl⟩ : syracuseStep 642649 = 481987) (by norm_num)
theorem B642685 : Blo 570811 642685 := bbase (se 3 (by rfl) ⟨120503, by rfl⟩ : syracuseStep 642685 = 241007) (by norm_num)
theorem B642721 : Blo 570811 642721 := bbase (se 2 (by rfl) ⟨241020, by rfl⟩ : syracuseStep 642721 = 482041) (by norm_num)
theorem B609977 : Blo 570811 609977 := bbase (se 2 (by rfl) ⟨228741, by rfl⟩ : syracuseStep 609977 = 457483) (by norm_num)
theorem B642757 : Blo 570811 642757 := bbase (se 4 (by rfl) ⟨60258, by rfl⟩ : syracuseStep 642757 = 120517) (by norm_num)
theorem B642793 : Blo 570811 642793 := bbase (se 2 (by rfl) ⟨241047, by rfl⟩ : syracuseStep 642793 = 482095) (by norm_num)
theorem B642829 : Blo 570811 642829 := bbase (se 3 (by rfl) ⟨120530, by rfl⟩ : syracuseStep 642829 = 241061) (by norm_num)
theorem B642865 : Blo 570811 642865 := bbase (se 2 (by rfl) ⟨241074, by rfl⟩ : syracuseStep 642865 = 482149) (by norm_num)
theorem B642901 : Blo 570811 642901 := bbase (se 9 (by rfl) ⟨1883, by rfl⟩ : syracuseStep 642901 = 3767) (by norm_num)
theorem B642937 : Blo 570811 642937 := bbase (se 2 (by rfl) ⟨241101, by rfl⟩ : syracuseStep 642937 = 482203) (by norm_num)
theorem B1625989 : Blo 570811 1625989 := bbase (se 4 (by rfl) ⟨152436, by rfl⟩ : syracuseStep 1625989 = 304873) (by norm_num)
theorem B642973 : Blo 570811 642973 := bbase (se 3 (by rfl) ⟨120557, by rfl⟩ : syracuseStep 642973 = 241115) (by norm_num)
theorem B643009 : Blo 570811 643009 := bbase (se 2 (by rfl) ⟨241128, by rfl⟩ : syracuseStep 643009 = 482257) (by norm_num)
theorem B643045 : Blo 570811 643045 := bbase (se 4 (by rfl) ⟨60285, by rfl⟩ : syracuseStep 643045 = 120571) (by norm_num)
theorem B643081 : Blo 570811 643081 := bbase (se 2 (by rfl) ⟨241155, by rfl⟩ : syracuseStep 643081 = 482311) (by norm_num)
theorem B1626149 : Blo 570811 1626149 := bbase (se 4 (by rfl) ⟨152451, by rfl⟩ : syracuseStep 1626149 = 304903) (by norm_num)
theorem B643117 : Blo 570811 643117 := bbase (se 3 (by rfl) ⟨120584, by rfl⟩ : syracuseStep 643117 = 241169) (by norm_num)
theorem B643153 : Blo 570811 643153 := bbase (se 2 (by rfl) ⟨241182, by rfl⟩ : syracuseStep 643153 = 482365) (by norm_num)
theorem B610421 : Blo 570811 610421 := bbase (se 5 (by rfl) ⟨28613, by rfl⟩ : syracuseStep 610421 = 57227) (by norm_num)
theorem B643189 : Blo 570811 643189 := bbase (se 5 (by rfl) ⟨30149, by rfl⟩ : syracuseStep 643189 = 60299) (by norm_num)
theorem B2445461 : Blo 570811 2445461 := bbase (se 6 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 2445461 = 114631) (by norm_num)
theorem B643225 : Blo 570811 643225 := bbase (se 2 (by rfl) ⟨241209, by rfl⟩ : syracuseStep 643225 = 482419) (by norm_num)
theorem B643261 : Blo 570811 643261 := bbase (se 3 (by rfl) ⟨120611, by rfl⟩ : syracuseStep 643261 = 241223) (by norm_num)
theorem B774365 : Blo 570811 774365 := bbase (se 3 (by rfl) ⟨145193, by rfl⟩ : syracuseStep 774365 = 290387) (by norm_num)
theorem B643297 : Blo 570811 643297 := bbase (se 2 (by rfl) ⟨241236, by rfl⟩ : syracuseStep 643297 = 482473) (by norm_num)
theorem B643333 : Blo 570811 643333 := bbase (se 4 (by rfl) ⟨60312, by rfl⟩ : syracuseStep 643333 = 120625) (by norm_num)
theorem B1626389 : Blo 570811 1626389 := bbase (se 6 (by rfl) ⟨38118, by rfl⟩ : syracuseStep 1626389 = 76237) (by norm_num)
theorem B643369 : Blo 570811 643369 := bbase (se 2 (by rfl) ⟨241263, by rfl⟩ : syracuseStep 643369 = 482527) (by norm_num)
theorem B643405 : Blo 570811 643405 := bbase (se 3 (by rfl) ⟨120638, by rfl⟩ : syracuseStep 643405 = 241277) (by norm_num)
theorem B610669 : Blo 570811 610669 := bbase (se 3 (by rfl) ⟨114500, by rfl⟩ : syracuseStep 610669 = 229001) (by norm_num)
theorem B643441 : Blo 570811 643441 := bbase (se 2 (by rfl) ⟨241290, by rfl⟩ : syracuseStep 643441 = 482581) (by norm_num)
theorem B643477 : Blo 570811 643477 := bbase (se 6 (by rfl) ⟨15081, by rfl⟩ : syracuseStep 643477 = 30163) (by norm_num)
theorem B643513 : Blo 570811 643513 := bbase (se 2 (by rfl) ⟨241317, by rfl⟩ : syracuseStep 643513 = 482635) (by norm_num)
theorem B1626581 : Blo 570811 1626581 := bbase (se 7 (by rfl) ⟨19061, by rfl⟩ : syracuseStep 1626581 = 38123) (by norm_num)
theorem B643549 : Blo 570811 643549 := bbase (se 3 (by rfl) ⟨120665, by rfl⟩ : syracuseStep 643549 = 241331) (by norm_num)
theorem B643585 : Blo 570811 643585 := bbase (se 2 (by rfl) ⟨241344, by rfl⟩ : syracuseStep 643585 = 482689) (by norm_num)
theorem B643621 : Blo 570811 643621 := bbase (se 4 (by rfl) ⟨60339, by rfl⟩ : syracuseStep 643621 = 120679) (by norm_num)
theorem B643657 : Blo 570811 643657 := bbase (se 2 (by rfl) ⟨241371, by rfl⟩ : syracuseStep 643657 = 482743) (by norm_num)
theorem B643693 : Blo 570811 643693 := bbase (se 3 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 643693 = 241385) (by norm_num)
theorem B643729 : Blo 570811 643729 := bbase (se 2 (by rfl) ⟨241398, by rfl⟩ : syracuseStep 643729 = 482797) (by norm_num)
theorem B643765 : Blo 570811 643765 := bbase (se 5 (by rfl) ⟨30176, by rfl⟩ : syracuseStep 643765 = 60353) (by norm_num)
theorem B840389 : Blo 570811 840389 := bbase (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) (by norm_num)
theorem B643801 : Blo 570811 643801 := bbase (se 2 (by rfl) ⟨241425, by rfl⟩ : syracuseStep 643801 = 482851) (by norm_num)
theorem B2904821 : Blo 570811 2904821 := bbase (se 5 (by rfl) ⟨136163, by rfl⟩ : syracuseStep 2904821 = 272327) (by norm_num)
theorem B643837 : Blo 570811 643837 := bbase (se 3 (by rfl) ⟨120719, by rfl⟩ : syracuseStep 643837 = 241439) (by norm_num)
theorem B643873 : Blo 570811 643873 := bbase (se 2 (by rfl) ⟨241452, by rfl⟩ : syracuseStep 643873 = 482905) (by norm_num)
theorem B611113 : Blo 570811 611113 := bbase (se 2 (by rfl) ⟨229167, by rfl⟩ : syracuseStep 611113 = 458335) (by norm_num)
theorem B643909 : Blo 570811 643909 := bbase (se 4 (by rfl) ⟨60366, by rfl⟩ : syracuseStep 643909 = 120733) (by norm_num)
theorem B611173 : Blo 570811 611173 := bbase (se 4 (by rfl) ⟨57297, by rfl⟩ : syracuseStep 611173 = 114595) (by norm_num)
theorem B643945 : Blo 570811 643945 := bbase (se 2 (by rfl) ⟨241479, by rfl⟩ : syracuseStep 643945 = 482959) (by norm_num)
theorem B643981 : Blo 570811 643981 := bbase (se 3 (by rfl) ⟨120746, by rfl⟩ : syracuseStep 643981 = 241493) (by norm_num)
theorem B644017 : Blo 570811 644017 := bbase (se 2 (by rfl) ⟨241506, by rfl⟩ : syracuseStep 644017 = 483013) (by norm_num)
theorem B775117 : Blo 570811 775117 := bbase (se 3 (by rfl) ⟨145334, by rfl⟩ : syracuseStep 775117 = 290669) (by norm_num)
theorem B644053 : Blo 570811 644053 := bbase (se 7 (by rfl) ⟨7547, by rfl⟩ : syracuseStep 644053 = 15095) (by norm_num)
theorem B644089 : Blo 570811 644089 := bbase (se 2 (by rfl) ⟨241533, by rfl⟩ : syracuseStep 644089 = 483067) (by norm_num)
theorem B644125 : Blo 570811 644125 := bbase (se 3 (by rfl) ⟨120773, by rfl⟩ : syracuseStep 644125 = 241547) (by norm_num)
theorem B578621 : Blo 570811 578621 := bbase (se 3 (by rfl) ⟨108491, by rfl⟩ : syracuseStep 578621 = 216983) (by norm_num)
theorem B644161 : Blo 570811 644161 := bbase (se 2 (by rfl) ⟨241560, by rfl⟩ : syracuseStep 644161 = 483121) (by norm_num)
theorem B644197 : Blo 570811 644197 := bbase (se 4 (by rfl) ⟨60393, by rfl⟩ : syracuseStep 644197 = 120787) (by norm_num)
theorem B578669 : Blo 570811 578669 := bbase (se 3 (by rfl) ⟨108500, by rfl⟩ : syracuseStep 578669 = 217001) (by norm_num)
theorem B2446469 : Blo 570811 2446469 := bbase (se 4 (by rfl) ⟨229356, by rfl⟩ : syracuseStep 2446469 = 458713) (by norm_num)
theorem B644233 : Blo 570811 644233 := bbase (se 2 (by rfl) ⟨241587, by rfl⟩ : syracuseStep 644233 = 483175) (by norm_num)
theorem B611489 : Blo 570811 611489 := bbase (se 2 (by rfl) ⟨229308, by rfl⟩ : syracuseStep 611489 = 458617) (by norm_num)
theorem B644269 : Blo 570811 644269 := bbase (se 3 (by rfl) ⟨120800, by rfl⟩ : syracuseStep 644269 = 241601) (by norm_num)
theorem B644305 : Blo 570811 644305 := bbase (se 2 (by rfl) ⟨241614, by rfl⟩ : syracuseStep 644305 = 483229) (by norm_num)
theorem B644341 : Blo 570811 644341 := bbase (se 5 (by rfl) ⟨30203, by rfl⟩ : syracuseStep 644341 = 60407) (by norm_num)
theorem B644377 : Blo 570811 644377 := bbase (se 2 (by rfl) ⟨241641, by rfl⟩ : syracuseStep 644377 = 483283) (by norm_num)
theorem B644413 : Blo 570811 644413 := bbase (se 3 (by rfl) ⟨120827, by rfl⟩ : syracuseStep 644413 = 241655) (by norm_num)
theorem B3659093 : Blo 570811 3659093 := bbase (se 15 (by rfl) ⟨167, by rfl⟩ : syracuseStep 3659093 = 335) (by norm_num)
theorem B644449 : Blo 570811 644449 := bbase (se 2 (by rfl) ⟨241668, by rfl⟩ : syracuseStep 644449 = 483337) (by norm_num)
theorem B644485 : Blo 570811 644485 := bbase (se 4 (by rfl) ⟨60420, by rfl⟩ : syracuseStep 644485 = 120841) (by norm_num)
theorem B578957 : Blo 570811 578957 := bbase (se 3 (by rfl) ⟨108554, by rfl⟩ : syracuseStep 578957 = 217109) (by norm_num)
theorem B644521 : Blo 570811 644521 := bbase (se 2 (by rfl) ⟨241695, by rfl⟩ : syracuseStep 644521 = 483391) (by norm_num)
theorem B1627573 : Blo 570811 1627573 := bbase (se 5 (by rfl) ⟨76292, by rfl⟩ : syracuseStep 1627573 = 152585) (by norm_num)
theorem B644557 : Blo 570811 644557 := bbase (se 3 (by rfl) ⟨120854, by rfl⟩ : syracuseStep 644557 = 241709) (by norm_num)
theorem B644593 : Blo 570811 644593 := bbase (se 2 (by rfl) ⟨241722, by rfl⟩ : syracuseStep 644593 = 483445) (by norm_num)
theorem B644629 : Blo 570811 644629 := bbase (se 6 (by rfl) ⟨15108, by rfl⟩ : syracuseStep 644629 = 30217) (by norm_num)
theorem B1398325 : Blo 570811 1398325 := bbase (se 5 (by rfl) ⟨65546, by rfl⟩ : syracuseStep 1398325 = 131093) (by norm_num)
theorem B644665 : Blo 570811 644665 := bbase (se 2 (by rfl) ⟨241749, by rfl⟩ : syracuseStep 644665 = 483499) (by norm_num)
theorem B611933 : Blo 570811 611933 := bbase (se 3 (by rfl) ⟨114737, by rfl⟩ : syracuseStep 611933 = 229475) (by norm_num)
theorem B644701 : Blo 570811 644701 := bbase (se 3 (by rfl) ⟨120881, by rfl⟩ : syracuseStep 644701 = 241763) (by norm_num)
theorem B644737 : Blo 570811 644737 := bbase (se 2 (by rfl) ⟨241776, by rfl⟩ : syracuseStep 644737 = 483553) (by norm_num)
theorem B611993 : Blo 570811 611993 := bbase (se 2 (by rfl) ⟨229497, by rfl⟩ : syracuseStep 611993 = 458995) (by norm_num)
theorem B644773 : Blo 570811 644773 := bbase (se 4 (by rfl) ⟨60447, by rfl⟩ : syracuseStep 644773 = 120895) (by norm_num)
theorem B644809 : Blo 570811 644809 := bbase (se 2 (by rfl) ⟨241803, by rfl⟩ : syracuseStep 644809 = 483607) (by norm_num)
theorem B644845 : Blo 570811 644845 := bbase (se 3 (by rfl) ⟨120908, by rfl⟩ : syracuseStep 644845 = 241817) (by norm_num)
theorem B644881 : Blo 570811 644881 := bbase (se 2 (by rfl) ⟨241830, by rfl⟩ : syracuseStep 644881 = 483661) (by norm_num)
theorem B612121 : Blo 570811 612121 := bbase (se 2 (by rfl) ⟨229545, by rfl⟩ : syracuseStep 612121 = 459091) (by norm_num)
theorem B644917 : Blo 570811 644917 := bbase (se 5 (by rfl) ⟨30230, by rfl⟩ : syracuseStep 644917 = 60461) (by norm_num)
theorem B644953 : Blo 570811 644953 := bbase (se 2 (by rfl) ⟨241857, by rfl⟩ : syracuseStep 644953 = 483715) (by norm_num)
theorem B644989 : Blo 570811 644989 := bbase (se 3 (by rfl) ⟨120935, by rfl⟩ : syracuseStep 644989 = 241871) (by norm_num)
theorem B645025 : Blo 570811 645025 := bbase (se 2 (by rfl) ⟨241884, by rfl⟩ : syracuseStep 645025 = 483769) (by norm_num)
theorem B1103797 : Blo 570811 1103797 := bbase (se 5 (by rfl) ⟨51740, by rfl⟩ : syracuseStep 1103797 = 103481) (by norm_num)
theorem B645061 : Blo 570811 645061 := bbase (se 4 (by rfl) ⟨60474, by rfl⟩ : syracuseStep 645061 = 120949) (by norm_num)
theorem B645097 : Blo 570811 645097 := bbase (se 2 (by rfl) ⟨241911, by rfl⟩ : syracuseStep 645097 = 483823) (by norm_num)
theorem B2906117 : Blo 570811 2906117 := bbase (se 4 (by rfl) ⟨272448, by rfl⟩ : syracuseStep 2906117 = 544897) (by norm_num)
theorem B645133 : Blo 570811 645133 := bbase (se 3 (by rfl) ⟨120962, by rfl⟩ : syracuseStep 645133 = 241925) (by norm_num)
theorem B645169 : Blo 570811 645169 := bbase (se 2 (by rfl) ⟨241938, by rfl⟩ : syracuseStep 645169 = 483877) (by norm_num)
theorem B645205 : Blo 570811 645205 := bbase (se 8 (by rfl) ⟨3780, by rfl⟩ : syracuseStep 645205 = 7561) (by norm_num)
theorem B1103957 : Blo 570811 1103957 := bbase (se 8 (by rfl) ⟨6468, by rfl⟩ : syracuseStep 1103957 = 12937) (by norm_num)
theorem B645241 : Blo 570811 645241 := bbase (se 2 (by rfl) ⟨241965, by rfl⟩ : syracuseStep 645241 = 483931) (by norm_num)
theorem B645277 : Blo 570811 645277 := bbase (se 3 (by rfl) ⟨120989, by rfl⟩ : syracuseStep 645277 = 241979) (by norm_num)
theorem B645313 : Blo 570811 645313 := bbase (se 2 (by rfl) ⟨241992, by rfl⟩ : syracuseStep 645313 = 483985) (by norm_num)
theorem B612565 : Blo 570811 612565 := bbase (se 7 (by rfl) ⟨7178, by rfl⟩ : syracuseStep 612565 = 14357) (by norm_num)
theorem B645349 : Blo 570811 645349 := bbase (se 4 (by rfl) ⟨60501, by rfl⟩ : syracuseStep 645349 = 121003) (by norm_num)
theorem B645385 : Blo 570811 645385 := bbase (se 2 (by rfl) ⟨242019, by rfl⟩ : syracuseStep 645385 = 484039) (by norm_num)
theorem B2611493 : Blo 570811 2611493 := bbase (se 4 (by rfl) ⟨244827, by rfl⟩ : syracuseStep 2611493 = 489655) (by norm_num)
theorem B645421 : Blo 570811 645421 := bbase (se 3 (by rfl) ⟨121016, by rfl⟩ : syracuseStep 645421 = 242033) (by norm_num)
theorem B612685 : Blo 570811 612685 := bbase (se 3 (by rfl) ⟨114878, by rfl⟩ : syracuseStep 612685 = 229757) (by norm_num)
theorem B645457 : Blo 570811 645457 := bbase (se 2 (by rfl) ⟨242046, by rfl⟩ : syracuseStep 645457 = 484093) (by norm_num)
theorem B645493 : Blo 570811 645493 := bbase (se 5 (by rfl) ⟨30257, by rfl⟩ : syracuseStep 645493 = 60515) (by norm_num)
theorem B645529 : Blo 570811 645529 := bbase (se 2 (by rfl) ⟨242073, by rfl⟩ : syracuseStep 645529 = 484147) (by norm_num)
theorem B645565 : Blo 570811 645565 := bbase (se 3 (by rfl) ⟨121043, by rfl⟩ : syracuseStep 645565 = 242087) (by norm_num)
theorem B645601 : Blo 570811 645601 := bbase (se 2 (by rfl) ⟨242100, by rfl⟩ : syracuseStep 645601 = 484201) (by norm_num)
theorem B1628677 : Blo 570811 1628677 := bbase (se 4 (by rfl) ⟨152688, by rfl⟩ : syracuseStep 1628677 = 305377) (by norm_num)
theorem B645637 : Blo 570811 645637 := bbase (se 4 (by rfl) ⟨60528, by rfl⟩ : syracuseStep 645637 = 121057) (by norm_num)
theorem B1858085 : Blo 570811 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B645673 : Blo 570811 645673 := bbase (se 2 (by rfl) ⟨242127, by rfl⟩ : syracuseStep 645673 = 484255) (by norm_num)
theorem B2316869 : Blo 570811 2316869 := bbase (se 4 (by rfl) ⟨217206, by rfl⟩ : syracuseStep 2316869 = 434413) (by norm_num)
theorem B612937 : Blo 570811 612937 := bbase (se 2 (by rfl) ⟨229851, by rfl⟩ : syracuseStep 612937 = 459703) (by norm_num)
theorem B612941 : Blo 570811 612941 := bbase (se 3 (by rfl) ⟨114926, by rfl⟩ : syracuseStep 612941 = 229853) (by norm_num)
theorem B645709 : Blo 570811 645709 := bbase (se 3 (by rfl) ⟨121070, by rfl⟩ : syracuseStep 645709 = 242141) (by norm_num)
theorem B645745 : Blo 570811 645745 := bbase (se 2 (by rfl) ⟨242154, by rfl⟩ : syracuseStep 645745 = 484309) (by norm_num)
theorem B645781 : Blo 570811 645781 := bbase (se 6 (by rfl) ⟨15135, by rfl⟩ : syracuseStep 645781 = 30271) (by norm_num)
theorem B645817 : Blo 570811 645817 := bbase (se 2 (by rfl) ⟨242181, by rfl⟩ : syracuseStep 645817 = 484363) (by norm_num)
theorem B645853 : Blo 570811 645853 := bbase (se 3 (by rfl) ⟨121097, by rfl⟩ : syracuseStep 645853 = 242195) (by norm_num)
theorem B1465085 : Blo 570811 1465085 := bbase (se 3 (by rfl) ⟨274703, by rfl⟩ : syracuseStep 1465085 = 549407) (by norm_num)
theorem B645889 : Blo 570811 645889 := bbase (se 2 (by rfl) ⟨242208, by rfl⟩ : syracuseStep 645889 = 484417) (by norm_num)
theorem B580385 : Blo 570811 580385 := bbase (se 2 (by rfl) ⟨217644, by rfl⟩ : syracuseStep 580385 = 435289) (by norm_num)
theorem B645925 : Blo 570811 645925 := bbase (se 4 (by rfl) ⟨60555, by rfl⟩ : syracuseStep 645925 = 121111) (by norm_num)
theorem B645961 : Blo 570811 645961 := bbase (se 2 (by rfl) ⟨242235, by rfl⟩ : syracuseStep 645961 = 484471) (by norm_num)
theorem B1104725 : Blo 570811 1104725 := bbase (se 9 (by rfl) ⟨3236, by rfl⟩ : syracuseStep 1104725 = 6473) (by norm_num)
theorem B1858405 : Blo 570811 1858405 := bbase (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) (by norm_num)
theorem B645997 : Blo 570811 645997 := bbase (se 3 (by rfl) ⟨121124, by rfl⟩ : syracuseStep 645997 = 242249) (by norm_num)
theorem B2448245 : Blo 570811 2448245 := bbase (se 5 (by rfl) ⟨114761, by rfl⟩ : syracuseStep 2448245 = 229523) (by norm_num)
theorem B646033 : Blo 570811 646033 := bbase (se 2 (by rfl) ⟨242262, by rfl⟩ : syracuseStep 646033 = 484525) (by norm_num)
theorem B646069 : Blo 570811 646069 := bbase (se 5 (by rfl) ⟨30284, by rfl⟩ : syracuseStep 646069 = 60569) (by norm_num)
theorem B646105 : Blo 570811 646105 := bbase (se 2 (by rfl) ⟨242289, by rfl⟩ : syracuseStep 646105 = 484579) (by norm_num)
theorem B646141 : Blo 570811 646141 := bbase (se 3 (by rfl) ⟨121151, by rfl⟩ : syracuseStep 646141 = 242303) (by norm_num)
theorem B646177 : Blo 570811 646177 := bbase (se 2 (by rfl) ⟨242316, by rfl⟩ : syracuseStep 646177 = 484633) (by norm_num)
theorem B580645 : Blo 570811 580645 := bbase (se 4 (by rfl) ⟨54435, by rfl⟩ : syracuseStep 580645 = 108871) (by norm_num)
theorem B646213 : Blo 570811 646213 := bbase (se 4 (by rfl) ⟨60582, by rfl⟩ : syracuseStep 646213 = 121165) (by norm_num)
theorem B646249 : Blo 570811 646249 := bbase (se 2 (by rfl) ⟨242343, by rfl⟩ : syracuseStep 646249 = 484687) (by norm_num)
theorem B613505 : Blo 570811 613505 := bbase (se 2 (by rfl) ⟨230064, by rfl⟩ : syracuseStep 613505 = 460129) (by norm_num)
theorem B646285 : Blo 570811 646285 := bbase (se 3 (by rfl) ⟨121178, by rfl⟩ : syracuseStep 646285 = 242357) (by norm_num)
theorem B646321 : Blo 570811 646321 := bbase (se 2 (by rfl) ⟨242370, by rfl⟩ : syracuseStep 646321 = 484741) (by norm_num)
theorem B646357 : Blo 570811 646357 := bbase (se 7 (by rfl) ⟨7574, by rfl⟩ : syracuseStep 646357 = 15149) (by norm_num)
theorem B646393 : Blo 570811 646393 := bbase (se 2 (by rfl) ⟨242397, by rfl⟩ : syracuseStep 646393 = 484795) (by norm_num)
theorem B2907413 : Blo 570811 2907413 := bbase (se 6 (by rfl) ⟨68142, by rfl⟩ : syracuseStep 2907413 = 136285) (by norm_num)
theorem B646429 : Blo 570811 646429 := bbase (se 3 (by rfl) ⟨121205, by rfl⟩ : syracuseStep 646429 = 242411) (by norm_num)
theorem B613693 : Blo 570811 613693 := bbase (se 3 (by rfl) ⟨115067, by rfl⟩ : syracuseStep 613693 = 230135) (by norm_num)
theorem B646465 : Blo 570811 646465 := bbase (se 2 (by rfl) ⟨242424, by rfl⟩ : syracuseStep 646465 = 484849) (by norm_num)
theorem B646501 : Blo 570811 646501 := bbase (se 4 (by rfl) ⟨60609, by rfl⟩ : syracuseStep 646501 = 121219) (by norm_num)
theorem B646537 : Blo 570811 646537 := bbase (se 2 (by rfl) ⟨242451, by rfl⟩ : syracuseStep 646537 = 484903) (by norm_num)
theorem B646573 : Blo 570811 646573 := bbase (se 3 (by rfl) ⟨121232, by rfl⟩ : syracuseStep 646573 = 242465) (by norm_num)
theorem B1564085 : Blo 570811 1564085 := bbase (se 5 (by rfl) ⟨73316, by rfl⟩ : syracuseStep 1564085 = 146633) (by norm_num)
theorem B646609 : Blo 570811 646609 := bbase (se 2 (by rfl) ⟨242478, by rfl⟩ : syracuseStep 646609 = 484957) (by norm_num)
theorem B646645 : Blo 570811 646645 := bbase (se 5 (by rfl) ⟨30311, by rfl⟩ : syracuseStep 646645 = 60623) (by norm_num)
theorem B581261 : Blo 570811 581261 := bbase (se 3 (by rfl) ⟨108986, by rfl⟩ : syracuseStep 581261 = 217973) (by norm_num)
theorem B581293 : Blo 570811 581293 := bbase (se 3 (by rfl) ⟨108992, by rfl⟩ : syracuseStep 581293 = 217985) (by norm_num)
theorem B4972373 : Blo 570811 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B2318213 : Blo 570811 2318213 := bbase (se 4 (by rfl) ⟨217332, by rfl⟩ : syracuseStep 2318213 = 434665) (by norm_num)
theorem B1630181 : Blo 570811 1630181 := bbase (se 4 (by rfl) ⟨152829, by rfl⟩ : syracuseStep 1630181 = 305659) (by norm_num)
theorem B1302589 : Blo 570811 1302589 := bbase (se 3 (by rfl) ⟨244235, by rfl⟩ : syracuseStep 1302589 = 488471) (by norm_num)
theorem B1401013 : Blo 570811 1401013 := bbase (se 5 (by rfl) ⟨65672, by rfl⟩ : syracuseStep 1401013 = 131345) (by norm_num)
theorem B2908709 : Blo 570811 2908709 := bbase (se 4 (by rfl) ⟨272691, by rfl⟩ : syracuseStep 2908709 = 545383) (by norm_num)
theorem B1303285 : Blo 570811 1303285 := bbase (se 5 (by rfl) ⟨61091, by rfl⟩ : syracuseStep 1303285 = 122183) (by norm_num)
theorem B3269429 : Blo 570811 3269429 := bbase (se 5 (by rfl) ⟨153254, by rfl⟩ : syracuseStep 3269429 = 306509) (by norm_num)
theorem B4351157 : Blo 570811 4351157 := bbase (se 5 (by rfl) ⟨203960, by rfl⟩ : syracuseStep 4351157 = 407921) (by norm_num)
theorem B1991861 : Blo 570811 1991861 := bbase (se 5 (by rfl) ⟨93368, by rfl⟩ : syracuseStep 1991861 = 186737) (by norm_num)
theorem B1631765 : Blo 570811 1631765 := bbase (se 6 (by rfl) ⟨38244, by rfl⟩ : syracuseStep 1631765 = 76489) (by norm_num)
theorem B747073 : Blo 570811 747073 := bbase (se 2 (by rfl) ⟨280152, by rfl⟩ : syracuseStep 747073 = 560305) (by norm_num)
theorem B1926773 : Blo 570811 1926773 := bbase (se 5 (by rfl) ⟨90317, by rfl⟩ : syracuseStep 1926773 = 180635) (by norm_num)
theorem B1468309 : Blo 570811 1468309 := bbase (se 6 (by rfl) ⟨34413, by rfl⟩ : syracuseStep 1468309 = 68827) (by norm_num)
theorem B1304597 : Blo 570811 1304597 := bbase (se 6 (by rfl) ⟨30576, by rfl⟩ : syracuseStep 1304597 = 61153) (by norm_num)
theorem B1927205 : Blo 570811 1927205 := bbase (se 4 (by rfl) ⟨180675, by rfl⟩ : syracuseStep 1927205 = 361351) (by norm_num)
theorem B2943125 : Blo 570811 2943125 := bbase (se 6 (by rfl) ⟨68979, by rfl⟩ : syracuseStep 2943125 = 137959) (by norm_num)
theorem B1632437 : Blo 570811 1632437 := bbase (se 5 (by rfl) ⟨76520, by rfl⟩ : syracuseStep 1632437 = 153041) (by norm_num)
theorem B813245 : Blo 570811 813245 := bbase (se 3 (by rfl) ⟨152483, by rfl⟩ : syracuseStep 813245 = 304967) (by norm_num)
theorem B1927637 : Blo 570811 1927637 := bbase (se 7 (by rfl) ⟨22589, by rfl⟩ : syracuseStep 1927637 = 45179) (by norm_num)
theorem B1632869 : Blo 570811 1632869 := bbase (se 4 (by rfl) ⟨153081, by rfl⟩ : syracuseStep 1632869 = 306163) (by norm_num)
theorem B1174181 : Blo 570811 1174181 := bbase (se 4 (by rfl) ⟨110079, by rfl⟩ : syracuseStep 1174181 = 220159) (by norm_num)
theorem B1928069 : Blo 570811 1928069 := bbase (se 4 (by rfl) ⟨180756, by rfl⟩ : syracuseStep 1928069 = 361513) (by norm_num)
theorem B813997 : Blo 570811 813997 := bbase (se 3 (by rfl) ⟨152624, by rfl⟩ : syracuseStep 813997 = 305249) (by norm_num)
theorem B2747317 : Blo 570811 2747317 := bbase (se 5 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 2747317 = 257561) (by norm_num)
theorem B2452517 : Blo 570811 2452517 := bbase (se 4 (by rfl) ⟨229923, by rfl⟩ : syracuseStep 2452517 = 459847) (by norm_num)
theorem B4942997 : Blo 570811 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B1928501 : Blo 570811 1928501 := bbase (se 5 (by rfl) ⟨90398, by rfl⟩ : syracuseStep 1928501 = 180797) (by norm_num)
theorem B1469765 : Blo 570811 1469765 := bbase (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) (by norm_num)
theorem B1633621 : Blo 570811 1633621 := bbase (se 11 (by rfl) ⟨1196, by rfl⟩ : syracuseStep 1633621 = 2393) (by norm_num)
theorem B1043885 : Blo 570811 1043885 := bbase (se 3 (by rfl) ⟨195728, by rfl⟩ : syracuseStep 1043885 = 391457) (by norm_num)
theorem B2321941 : Blo 570811 2321941 := bbase (se 6 (by rfl) ⟨54420, by rfl⟩ : syracuseStep 2321941 = 108841) (by norm_num)
theorem B814789 : Blo 570811 814789 := bbase (se 4 (by rfl) ⟨76386, by rfl⟩ : syracuseStep 814789 = 152773) (by norm_num)
theorem B978653 : Blo 570811 978653 := bbase (se 3 (by rfl) ⟨183497, by rfl⟩ : syracuseStep 978653 = 366995) (by norm_num)
theorem B1928933 : Blo 570811 1928933 := bbase (se 4 (by rfl) ⟨180837, by rfl⟩ : syracuseStep 1928933 = 361675) (by norm_num)
theorem B1830725 : Blo 570811 1830725 := bbase (se 4 (by rfl) ⟨171630, by rfl⟩ : syracuseStep 1830725 = 343261) (by norm_num)
theorem B1830853 : Blo 570811 1830853 := bbase (se 4 (by rfl) ⟨171642, by rfl⟩ : syracuseStep 1830853 = 343285) (by norm_num)
theorem B2060245 : Blo 570811 2060245 := bbase (se 7 (by rfl) ⟨24143, by rfl⟩ : syracuseStep 2060245 = 48287) (by norm_num)
theorem B815125 : Blo 570811 815125 := bbase (se 6 (by rfl) ⟨19104, by rfl⟩ : syracuseStep 815125 = 38209) (by norm_num)
theorem B1929365 : Blo 570811 1929365 := bbase (se 6 (by rfl) ⟨45219, by rfl⟩ : syracuseStep 1929365 = 90439) (by norm_num)
theorem B618725 : Blo 570811 618725 := bbase (se 4 (by rfl) ⟨58005, by rfl⟩ : syracuseStep 618725 = 116011) (by norm_num)
theorem B815341 : Blo 570811 815341 := bbase (se 3 (by rfl) ⟨152876, by rfl⟩ : syracuseStep 815341 = 305753) (by norm_num)
theorem B782669 : Blo 570811 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B5566805 : Blo 570811 5566805 := bbase (se 10 (by rfl) ⟨8154, by rfl⟩ : syracuseStep 5566805 = 16309) (by norm_num)
theorem B2322917 : Blo 570811 2322917 := bbase (se 4 (by rfl) ⟨217773, by rfl⟩ : syracuseStep 2322917 = 435547) (by norm_num)
theorem B1470997 : Blo 570811 1470997 := bbase (se 6 (by rfl) ⟨34476, by rfl⟩ : syracuseStep 1470997 = 68953) (by norm_num)
theorem B1929797 : Blo 570811 1929797 := bbase (se 4 (by rfl) ⟨180918, by rfl⟩ : syracuseStep 1929797 = 361837) (by norm_num)
theorem B815717 : Blo 570811 815717 := bbase (se 4 (by rfl) ⟨76473, by rfl⟩ : syracuseStep 815717 = 152947) (by norm_num)
theorem B651961 : Blo 570811 651961 := bbase (se 2 (by rfl) ⟨244485, by rfl⟩ : syracuseStep 651961 = 488971) (by norm_num)
theorem B4879061 : Blo 570811 4879061 := bbase (se 7 (by rfl) ⟨57176, by rfl⟩ : syracuseStep 4879061 = 114353) (by norm_num)
theorem B2454293 : Blo 570811 2454293 := bbase (se 6 (by rfl) ⟨57522, by rfl⟩ : syracuseStep 2454293 = 115045) (by norm_num)
theorem B652153 : Blo 570811 652153 := bbase (se 2 (by rfl) ⟨244557, by rfl⟩ : syracuseStep 652153 = 489115) (by norm_num)
theorem B1930229 : Blo 570811 1930229 := bbase (se 5 (by rfl) ⟨90479, by rfl⟩ : syracuseStep 1930229 = 180959) (by norm_num)
theorem B2454533 : Blo 570811 2454533 := bbase (se 4 (by rfl) ⟨230112, by rfl⟩ : syracuseStep 2454533 = 460225) (by norm_num)
theorem B1373197 : Blo 570811 1373197 := bbase (se 3 (by rfl) ⟨257474, by rfl⟩ : syracuseStep 1373197 = 514949) (by norm_num)
theorem B914485 : Blo 570811 914485 := bbase (se 5 (by rfl) ⟨42866, by rfl⟩ : syracuseStep 914485 = 85733) (by norm_num)
theorem B1373429 : Blo 570811 1373429 := bbase (se 5 (by rfl) ⟨64379, by rfl⟩ : syracuseStep 1373429 = 128759) (by norm_num)
theorem B2061557 : Blo 570811 2061557 := bbase (se 5 (by rfl) ⟨96635, by rfl⟩ : syracuseStep 2061557 = 193271) (by norm_num)
theorem B3667189 : Blo 570811 3667189 := bbase (se 5 (by rfl) ⟨171899, by rfl⟩ : syracuseStep 3667189 = 343799) (by norm_num)
theorem B1373573 : Blo 570811 1373573 := bbase (se 4 (by rfl) ⟨128772, by rfl⟩ : syracuseStep 1373573 = 257545) (by norm_num)
theorem B2651525 : Blo 570811 2651525 := bbase (se 4 (by rfl) ⟨248580, by rfl⟩ : syracuseStep 2651525 = 497161) (by norm_num)
theorem B1930661 : Blo 570811 1930661 := bbase (se 4 (by rfl) ⟨180999, by rfl⟩ : syracuseStep 1930661 = 361999) (by norm_num)
theorem B1373813 : Blo 570811 1373813 := bbase (se 5 (by rfl) ⟨64397, by rfl⟩ : syracuseStep 1373813 = 128795) (by norm_num)
theorem B2291381 : Blo 570811 2291381 := bbase (se 5 (by rfl) ⟨107408, by rfl⟩ : syracuseStep 2291381 = 214817) (by norm_num)
theorem B2487989 : Blo 570811 2487989 := bbase (se 5 (by rfl) ⟨116624, by rfl⟩ : syracuseStep 2487989 = 233249) (by norm_num)
theorem B915157 : Blo 570811 915157 := bbase (se 7 (by rfl) ⟨10724, by rfl⟩ : syracuseStep 915157 = 21449) (by norm_num)
theorem B882389 : Blo 570811 882389 := bbase (se 7 (by rfl) ⟨10340, by rfl⟩ : syracuseStep 882389 = 20681) (by norm_num)
theorem B6190805 : Blo 570811 6190805 := bbase (se 7 (by rfl) ⟨72548, by rfl⟩ : syracuseStep 6190805 = 145097) (by norm_num)
theorem B1931093 : Blo 570811 1931093 := bbase (se 9 (by rfl) ⟨5657, by rfl⟩ : syracuseStep 1931093 = 11315) (by norm_num)
theorem B1046405 : Blo 570811 1046405 := bbase (se 4 (by rfl) ⟨98100, by rfl⟩ : syracuseStep 1046405 = 196201) (by norm_num)
theorem B817141 : Blo 570811 817141 := bbase (se 5 (by rfl) ⟨38303, by rfl⟩ : syracuseStep 817141 = 76607) (by norm_num)
theorem B1177669 : Blo 570811 1177669 := bbase (se 4 (by rfl) ⟨110406, by rfl⟩ : syracuseStep 1177669 = 220813) (by norm_num)
theorem B1636469 : Blo 570811 1636469 := bbase (se 5 (by rfl) ⟨76709, by rfl⟩ : syracuseStep 1636469 = 153419) (by norm_num)
theorem B1931525 : Blo 570811 1931525 := bbase (se 4 (by rfl) ⟨181080, by rfl⟩ : syracuseStep 1931525 = 362161) (by norm_num)
theorem B784685 : Blo 570811 784685 := bbase (se 3 (by rfl) ⟨147128, by rfl⟩ : syracuseStep 784685 = 294257) (by norm_num)
theorem B686441 : Blo 570811 686441 := bbase (se 2 (by rfl) ⟨257415, by rfl⟩ : syracuseStep 686441 = 514831) (by norm_num)
theorem B1374581 : Blo 570811 1374581 := bbase (se 5 (by rfl) ⟨64433, by rfl⟩ : syracuseStep 1374581 = 128867) (by norm_num)
theorem B981445 : Blo 570811 981445 := bbase (se 4 (by rfl) ⟨92010, by rfl⟩ : syracuseStep 981445 = 184021) (by norm_num)
theorem B588341 : Blo 570811 588341 := bbase (se 5 (by rfl) ⟨27578, by rfl⟩ : syracuseStep 588341 = 55157) (by norm_num)
theorem B817733 : Blo 570811 817733 := bbase (se 4 (by rfl) ⟨76662, by rfl⟩ : syracuseStep 817733 = 153325) (by norm_num)
theorem B1964645 : Blo 570811 1964645 := bbase (se 4 (by rfl) ⟨184185, by rfl⟩ : syracuseStep 1964645 = 368371) (by norm_num)
theorem B1047181 : Blo 570811 1047181 := bbase (se 3 (by rfl) ⟨196346, by rfl⟩ : syracuseStep 1047181 = 392693) (by norm_num)
theorem B817813 : Blo 570811 817813 := bbase (se 6 (by rfl) ⟨19167, by rfl⟩ : syracuseStep 817813 = 38335) (by norm_num)
theorem B1931957 : Blo 570811 1931957 := bbase (se 5 (by rfl) ⟨90560, by rfl⟩ : syracuseStep 1931957 = 181121) (by norm_num)
theorem B916157 : Blo 570811 916157 := bbase (se 3 (by rfl) ⟨171779, by rfl⟩ : syracuseStep 916157 = 343559) (by norm_num)
theorem B817933 : Blo 570811 817933 := bbase (se 3 (by rfl) ⟨153362, by rfl⟩ : syracuseStep 817933 = 306725) (by norm_num)
theorem B1833749 : Blo 570811 1833749 := bbase (se 6 (by rfl) ⟨42978, by rfl⟩ : syracuseStep 1833749 = 85957) (by norm_num)
theorem B1178389 : Blo 570811 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B2063141 : Blo 570811 2063141 := bbase (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) (by norm_num)
theorem B818029 : Blo 570811 818029 := bbase (se 3 (by rfl) ⟨153380, by rfl⟩ : syracuseStep 818029 = 306761) (by norm_num)
theorem B1309661 : Blo 570811 1309661 := bbase (se 3 (by rfl) ⟨245561, by rfl⟩ : syracuseStep 1309661 = 491123) (by norm_num)
theorem B2751509 : Blo 570811 2751509 := bbase (se 6 (by rfl) ⟨64488, by rfl⟩ : syracuseStep 2751509 = 128977) (by norm_num)
theorem B2227301 : Blo 570811 2227301 := bbase (se 4 (by rfl) ⟨208809, by rfl⟩ : syracuseStep 2227301 = 417619) (by norm_num)
theorem B1932389 : Blo 570811 1932389 := bbase (se 4 (by rfl) ⟨181161, by rfl⟩ : syracuseStep 1932389 = 362323) (by norm_num)
theorem B588961 : Blo 570811 588961 := bbase (se 2 (by rfl) ⟨220860, by rfl⟩ : syracuseStep 588961 = 441721) (by norm_num)
theorem B1965269 : Blo 570811 1965269 := bbase (se 7 (by rfl) ⟨23030, by rfl⟩ : syracuseStep 1965269 = 46061) (by norm_num)
theorem B654689 : Blo 570811 654689 := bbase (se 2 (by rfl) ⟨245508, by rfl⟩ : syracuseStep 654689 = 491017) (by norm_num)
theorem B4128245 : Blo 570811 4128245 := bbase (se 5 (by rfl) ⟨193511, by rfl⟩ : syracuseStep 4128245 = 387023) (by norm_num)
theorem B9895445 : Blo 570811 9895445 := bbase (se 6 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 9895445 = 463849) (by norm_num)
theorem B687637 : Blo 570811 687637 := bbase (se 6 (by rfl) ⟨16116, by rfl⟩ : syracuseStep 687637 = 32233) (by norm_num)
theorem B1932821 : Blo 570811 1932821 := bbase (se 6 (by rfl) ⟨45300, by rfl⟩ : syracuseStep 1932821 = 90601) (by norm_num)
theorem B687709 : Blo 570811 687709 := bbase (se 3 (by rfl) ⟨128945, by rfl⟩ : syracuseStep 687709 = 257891) (by norm_num)
theorem B1474141 : Blo 570811 1474141 := bbase (se 3 (by rfl) ⟨276401, by rfl⟩ : syracuseStep 1474141 = 552803) (by norm_num)
theorem B1375957 : Blo 570811 1375957 := bbase (se 7 (by rfl) ⟨16124, by rfl⟩ : syracuseStep 1375957 = 32249) (by norm_num)
theorem B1933253 : Blo 570811 1933253 := bbase (se 4 (by rfl) ⟨181242, by rfl⟩ : syracuseStep 1933253 = 362485) (by norm_num)
theorem B1376273 : Blo 570811 1376273 := bstep (se 2 (by rfl) ⟨516102, by rfl⟩ : syracuseStep 1376273 = 1032205) B1032205
theorem B1933361 : Blo 570811 1933361 := bstep (se 2 (by rfl) ⟨725010, by rfl⟩ : syracuseStep 1933361 = 1450021) B1450021
theorem B1736785 : Blo 570811 1736785 := bstep (se 2 (by rfl) ⟨651294, by rfl⟩ : syracuseStep 1736785 = 1302589) B1302589
theorem B1868017 : Blo 570811 1868017 := bstep (se 2 (by rfl) ⟨700506, by rfl⟩ : syracuseStep 1868017 = 1401013) B1401013
theorem B688675 : Blo 570811 688675 := bstep (se 1 (by rfl) ⟨516506, by rfl⟩ : syracuseStep 688675 = 1033013) B1033013
theorem B2064973 : Blo 570811 2064973 := bstep (se 3 (by rfl) ⟨387182, by rfl⟩ : syracuseStep 2064973 = 774365) B774365
theorem B1933901 : Blo 570811 1933901 := bstep (se 3 (by rfl) ⟨362606, by rfl⟩ : syracuseStep 1933901 = 725213) B725213
theorem B1933955 : Blo 570811 1933955 := bstep (se 1 (by rfl) ⟨1450466, by rfl⟩ : syracuseStep 1933955 = 2900933) B2900933
theorem B2753315 : Blo 570811 2753315 := bstep (se 1 (by rfl) ⟨2064986, by rfl⟩ : syracuseStep 2753315 = 4129973) B4129973
theorem B1934225 : Blo 570811 1934225 := bstep (se 2 (by rfl) ⟨725334, by rfl⟩ : syracuseStep 1934225 = 1450669) B1450669
theorem B689059 : Blo 570811 689059 := bstep (se 1 (by rfl) ⟨516794, by rfl⟩ : syracuseStep 689059 = 1033589) B1033589
theorem B1737713 : Blo 570811 1737713 := bstep (se 2 (by rfl) ⟨651642, by rfl⟩ : syracuseStep 1737713 = 1303285) B1303285
theorem B918515 : Blo 570811 918515 := bstep (se 1 (by rfl) ⟨688886, by rfl⟩ : syracuseStep 918515 = 1377773) B1377773
theorem B918643 : Blo 570811 918643 := bstep (se 1 (by rfl) ⟨688982, by rfl⟩ : syracuseStep 918643 = 1377965) B1377965
theorem B1836209 : Blo 570811 1836209 := bstep (se 2 (by rfl) ⟨688578, by rfl⟩ : syracuseStep 1836209 = 1377157) B1377157
theorem B918707 : Blo 570811 918707 := bstep (se 1 (by rfl) ⟨689030, by rfl⟩ : syracuseStep 918707 = 1378061) B1378061
theorem B1934765 : Blo 570811 1934765 := bstep (se 3 (by rfl) ⟨362768, by rfl⟩ : syracuseStep 1934765 = 725537) B725537
theorem B1934819 : Blo 570811 1934819 := bstep (se 1 (by rfl) ⟨1451114, by rfl⟩ : syracuseStep 1934819 = 2902229) B2902229
theorem B1836557 : Blo 570811 1836557 := bstep (se 3 (by rfl) ⟨344354, by rfl⟩ : syracuseStep 1836557 = 688709) B688709
theorem B2754083 : Blo 570811 2754083 := bstep (se 1 (by rfl) ⟨2065562, by rfl⟩ : syracuseStep 2754083 = 4131125) B4131125
theorem B722515 : Blo 570811 722515 := bstep (se 1 (by rfl) ⟨541886, by rfl⟩ : syracuseStep 722515 = 1083773) B1083773
theorem B919201 : Blo 570811 919201 := bstep (se 2 (by rfl) ⟨344700, by rfl⟩ : syracuseStep 919201 = 689401) B689401
theorem B722611 : Blo 570811 722611 := bstep (se 1 (by rfl) ⟨541958, by rfl⟩ : syracuseStep 722611 = 1083917) B1083917
theorem B1935089 : Blo 570811 1935089 := bstep (se 2 (by rfl) ⟨725658, by rfl⟩ : syracuseStep 1935089 = 1451317) B1451317
theorem B2328547 : Blo 570811 2328547 := bstep (se 1 (by rfl) ⟨1746410, by rfl⟩ : syracuseStep 2328547 = 3492821) B3492821
theorem B2328689 : Blo 570811 2328689 := bstep (se 2 (by rfl) ⟨873258, by rfl⟩ : syracuseStep 2328689 = 1746517) B1746517
theorem B723107 : Blo 570811 723107 := bstep (se 1 (by rfl) ⟨542330, by rfl⟩ : syracuseStep 723107 = 1084661) B1084661
theorem B1935629 : Blo 570811 1935629 := bstep (se 3 (by rfl) ⟨362930, by rfl⟩ : syracuseStep 1935629 = 725861) B725861
theorem B919873 : Blo 570811 919873 := bstep (se 2 (by rfl) ⟨344952, by rfl⟩ : syracuseStep 919873 = 689905) B689905
theorem B1935683 : Blo 570811 1935683 := bstep (se 1 (by rfl) ⟨1451762, by rfl⟩ : syracuseStep 1935683 = 2903525) B2903525
theorem B3475811 : Blo 570811 3475811 := bstep (se 1 (by rfl) ⟨2606858, by rfl⟩ : syracuseStep 3475811 = 5213717) B5213717
theorem B1116547 : Blo 570811 1116547 := bstep (se 1 (by rfl) ⟨837410, by rfl⟩ : syracuseStep 1116547 = 1674821) B1674821
theorem B2230861 : Blo 570811 2230861 := bstep (se 3 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 2230861 = 836573) B836573
theorem B1935953 : Blo 570811 1935953 := bstep (se 2 (by rfl) ⟨725982, by rfl⟩ : syracuseStep 1935953 = 1451965) B1451965
theorem B1084099 : Blo 570811 1084099 := bstep (se 1 (by rfl) ⟨813074, by rfl⟩ : syracuseStep 1084099 = 1626149) B1626149
theorem B2755313 : Blo 570811 2755313 := bstep (se 2 (by rfl) ⟨1033242, by rfl⟩ : syracuseStep 2755313 = 2066485) B2066485
theorem B1542989 : Blo 570811 1542989 := bstep (se 3 (by rfl) ⟨289310, by rfl⟩ : syracuseStep 1542989 = 578621) B578621
theorem B1084259 : Blo 570811 1084259 := bstep (se 1 (by rfl) ⟨813194, by rfl⟩ : syracuseStep 1084259 = 1626389) B1626389
theorem B723811 : Blo 570811 723811 := bstep (se 1 (by rfl) ⟨542858, by rfl⟩ : syracuseStep 723811 = 1085717) B1085717
theorem B723907 : Blo 570811 723907 := bstep (se 1 (by rfl) ⟨542930, by rfl⟩ : syracuseStep 723907 = 1085861) B1085861
theorem B1543117 : Blo 570811 1543117 := bstep (se 3 (by rfl) ⟨289334, by rfl⟩ : syracuseStep 1543117 = 578669) B578669
theorem B1936493 : Blo 570811 1936493 := bstep (se 3 (by rfl) ⟨363092, by rfl⟩ : syracuseStep 1936493 = 726185) B726185
theorem B1936547 : Blo 570811 1936547 := bstep (se 1 (by rfl) ⟨1452410, by rfl⟩ : syracuseStep 1936547 = 2904821) B2904821
theorem B7834805 : Blo 570811 7834805 := bstep (se 5 (by rfl) ⟨367256, by rfl⟩ : syracuseStep 7834805 = 734513) B734513
theorem B5508323 : Blo 570811 5508323 := bstep (se 1 (by rfl) ⟨4131242, by rfl⟩ : syracuseStep 5508323 = 8262485) B8262485
theorem B2755853 : Blo 570811 2755853 := bstep (se 3 (by rfl) ⟨516722, by rfl⟩ : syracuseStep 2755853 = 1033445) B1033445
theorem B1838413 : Blo 570811 1838413 := bstep (se 3 (by rfl) ⟨344702, by rfl⟩ : syracuseStep 1838413 = 689405) B689405
theorem B1936817 : Blo 570811 1936817 := bstep (se 2 (by rfl) ⟨726306, by rfl⟩ : syracuseStep 1936817 = 1452613) B1452613
theorem B724403 : Blo 570811 724403 := bstep (se 1 (by rfl) ⟨543302, by rfl⟩ : syracuseStep 724403 = 1086605) B1086605
theorem B3477125 : Blo 570811 3477125 := bstep (se 4 (by rfl) ⟨325980, by rfl⟩ : syracuseStep 3477125 = 651961) B651961
theorem B1085329 : Blo 570811 1085329 := bstep (se 2 (by rfl) ⟨406998, by rfl⟩ : syracuseStep 1085329 = 813997) B813997
theorem B1445809 : Blo 570811 1445809 := bstep (se 2 (by rfl) ⟨542178, by rfl⟩ : syracuseStep 1445809 = 1084357) B1084357
theorem B1544113 : Blo 570811 1544113 := bstep (se 2 (by rfl) ⟨579042, by rfl⟩ : syracuseStep 1544113 = 1158085) B1158085
theorem B1937357 : Blo 570811 1937357 := bstep (se 3 (by rfl) ⟨363254, by rfl⟩ : syracuseStep 1937357 = 726509) B726509
theorem B1937411 : Blo 570811 1937411 := bstep (se 1 (by rfl) ⟨1453058, by rfl⟩ : syracuseStep 1937411 = 2906117) B2906117
theorem B725107 : Blo 570811 725107 := bstep (se 1 (by rfl) ⟨543830, by rfl⟩ : syracuseStep 725107 = 1087661) B1087661
theorem B856241 : Blo 570811 856241 := bstep (se 2 (by rfl) ⟨321090, by rfl⟩ : syracuseStep 856241 = 642181) B642181
theorem B856259 : Blo 570811 856259 := bstep (se 1 (by rfl) ⟨642194, by rfl⟩ : syracuseStep 856259 = 1284389) B1284389
theorem B1446083 : Blo 570811 1446083 := bstep (se 1 (by rfl) ⟨1084562, by rfl⟩ : syracuseStep 1446083 = 2169125) B2169125
theorem B1740995 : Blo 570811 1740995 := bstep (se 1 (by rfl) ⟨1305746, by rfl⟩ : syracuseStep 1740995 = 2611493) B2611493
theorem B2199757 : Blo 570811 2199757 := bstep (se 3 (by rfl) ⟨412454, by rfl⟩ : syracuseStep 2199757 = 824909) B824909
theorem B725203 : Blo 570811 725203 := bstep (se 1 (by rfl) ⟨543902, by rfl⟩ : syracuseStep 725203 = 1087805) B1087805
theorem B856289 : Blo 570811 856289 := bstep (se 2 (by rfl) ⟨321108, by rfl⟩ : syracuseStep 856289 = 642217) B642217
theorem B856307 : Blo 570811 856307 := bstep (se 1 (by rfl) ⟨642230, by rfl⟩ : syracuseStep 856307 = 1284461) B1284461
theorem B856337 : Blo 570811 856337 := bstep (se 2 (by rfl) ⟨321126, by rfl⟩ : syracuseStep 856337 = 642253) B642253
theorem B1937681 : Blo 570811 1937681 := bstep (se 2 (by rfl) ⟨726630, by rfl⟩ : syracuseStep 1937681 = 1453261) B1453261
theorem B18583829 : Blo 570811 18583829 := bstep (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) B871117
theorem B856355 : Blo 570811 856355 := bstep (se 1 (by rfl) ⟨642266, by rfl⟩ : syracuseStep 856355 = 1284533) B1284533
theorem B856385 : Blo 570811 856385 := bstep (se 2 (by rfl) ⟨321144, by rfl⟩ : syracuseStep 856385 = 642289) B642289
theorem B856403 : Blo 570811 856403 := bstep (se 1 (by rfl) ⟨642302, by rfl⟩ : syracuseStep 856403 = 1284605) B1284605
theorem B856433 : Blo 570811 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B856451 : Blo 570811 856451 := bstep (se 1 (by rfl) ⟨642338, by rfl⟩ : syracuseStep 856451 = 1284677) B1284677
theorem B1446275 : Blo 570811 1446275 := bstep (se 1 (by rfl) ⟨1084706, by rfl⟩ : syracuseStep 1446275 = 2169413) B2169413
theorem B1544579 : Blo 570811 1544579 := bstep (se 1 (by rfl) ⟨1158434, by rfl⟩ : syracuseStep 1544579 = 2316869) B2316869
theorem B856481 : Blo 570811 856481 := bstep (se 2 (by rfl) ⟨321180, by rfl⟩ : syracuseStep 856481 = 642361) B642361
theorem B856499 : Blo 570811 856499 := bstep (se 1 (by rfl) ⟨642374, by rfl⟩ : syracuseStep 856499 = 1284749) B1284749
theorem B856529 : Blo 570811 856529 := bstep (se 2 (by rfl) ⟨321198, by rfl⟩ : syracuseStep 856529 = 642397) B642397
theorem B856547 : Blo 570811 856547 := bstep (se 1 (by rfl) ⟨642410, by rfl⟩ : syracuseStep 856547 = 1284821) B1284821
theorem B856577 : Blo 570811 856577 := bstep (se 2 (by rfl) ⟨321216, by rfl⟩ : syracuseStep 856577 = 642433) B642433
theorem B856595 : Blo 570811 856595 := bstep (se 1 (by rfl) ⟨642446, by rfl⟩ : syracuseStep 856595 = 1284893) B1284893
theorem B856625 : Blo 570811 856625 := bstep (se 2 (by rfl) ⟨321234, by rfl⟩ : syracuseStep 856625 = 642469) B642469
theorem B856643 : Blo 570811 856643 := bstep (se 1 (by rfl) ⟨642482, by rfl⟩ : syracuseStep 856643 = 1284965) B1284965
theorem B4362821 : Blo 570811 4362821 := bstep (se 4 (by rfl) ⟨409014, by rfl⟩ : syracuseStep 4362821 = 818029) B818029
theorem B856673 : Blo 570811 856673 := bstep (se 2 (by rfl) ⟨321252, by rfl⟩ : syracuseStep 856673 = 642505) B642505
theorem B7180913 : Blo 570811 7180913 := bstep (se 2 (by rfl) ⟨2692842, by rfl⟩ : syracuseStep 7180913 = 5385685) B5385685
theorem B856691 : Blo 570811 856691 := bstep (se 1 (by rfl) ⟨642518, by rfl⟩ : syracuseStep 856691 = 1285037) B1285037
theorem B856721 : Blo 570811 856721 := bstep (se 2 (by rfl) ⟨321270, by rfl⟩ : syracuseStep 856721 = 642541) B642541
theorem B856739 : Blo 570811 856739 := bstep (se 1 (by rfl) ⟨642554, by rfl⟩ : syracuseStep 856739 = 1285109) B1285109
theorem B856769 : Blo 570811 856769 := bstep (se 2 (by rfl) ⟨321288, by rfl⟩ : syracuseStep 856769 = 642577) B642577
theorem B725699 : Blo 570811 725699 := bstep (se 1 (by rfl) ⟨544274, by rfl⟩ : syracuseStep 725699 = 1088549) B1088549
theorem B856787 : Blo 570811 856787 := bstep (se 1 (by rfl) ⟨642590, by rfl⟩ : syracuseStep 856787 = 1285181) B1285181
theorem B856817 : Blo 570811 856817 := bstep (se 2 (by rfl) ⟨321306, by rfl⟩ : syracuseStep 856817 = 642613) B642613
theorem B856835 : Blo 570811 856835 := bstep (se 1 (by rfl) ⟨642626, by rfl⟩ : syracuseStep 856835 = 1285253) B1285253
theorem B856865 : Blo 570811 856865 := bstep (se 2 (by rfl) ⟨321324, by rfl⟩ : syracuseStep 856865 = 642649) B642649
theorem B1938221 : Blo 570811 1938221 := bstep (se 3 (by rfl) ⟨363416, by rfl⟩ : syracuseStep 1938221 = 726833) B726833
theorem B856883 : Blo 570811 856883 := bstep (se 1 (by rfl) ⟨642662, by rfl⟩ : syracuseStep 856883 = 1285325) B1285325
theorem B856913 : Blo 570811 856913 := bstep (se 2 (by rfl) ⟨321342, by rfl⟩ : syracuseStep 856913 = 642685) B642685
theorem B856931 : Blo 570811 856931 := bstep (se 1 (by rfl) ⟨642698, by rfl⟩ : syracuseStep 856931 = 1285397) B1285397
theorem B1938275 : Blo 570811 1938275 := bstep (se 1 (by rfl) ⟨1453706, by rfl⟩ : syracuseStep 1938275 = 2907413) B2907413
theorem B856961 : Blo 570811 856961 := bstep (se 2 (by rfl) ⟨321360, by rfl⟩ : syracuseStep 856961 = 642721) B642721
theorem B856979 : Blo 570811 856979 := bstep (se 1 (by rfl) ⟨642734, by rfl⟩ : syracuseStep 856979 = 1285469) B1285469
theorem B857009 : Blo 570811 857009 := bstep (se 2 (by rfl) ⟨321378, by rfl⟩ : syracuseStep 857009 = 642757) B642757
theorem B1086385 : Blo 570811 1086385 := bstep (se 2 (by rfl) ⟨407394, by rfl⟩ : syracuseStep 1086385 = 814789) B814789
theorem B857027 : Blo 570811 857027 := bstep (se 1 (by rfl) ⟨642770, by rfl⟩ : syracuseStep 857027 = 1285541) B1285541
theorem B857057 : Blo 570811 857057 := bstep (se 2 (by rfl) ⟨321396, by rfl⟩ : syracuseStep 857057 = 642793) B642793
theorem B857075 : Blo 570811 857075 := bstep (se 1 (by rfl) ⟨642806, by rfl⟩ : syracuseStep 857075 = 1285613) B1285613
theorem B2790413 : Blo 570811 2790413 := bstep (se 3 (by rfl) ⟨523202, by rfl⟩ : syracuseStep 2790413 = 1046405) B1046405
theorem B857105 : Blo 570811 857105 := bstep (se 2 (by rfl) ⟨321414, by rfl⟩ : syracuseStep 857105 = 642829) B642829
theorem B857123 : Blo 570811 857123 := bstep (se 1 (by rfl) ⟨642842, by rfl⟩ : syracuseStep 857123 = 1285685) B1285685
theorem B857153 : Blo 570811 857153 := bstep (se 2 (by rfl) ⟨321432, by rfl⟩ : syracuseStep 857153 = 642865) B642865
theorem B857171 : Blo 570811 857171 := bstep (se 1 (by rfl) ⟨642878, by rfl⟩ : syracuseStep 857171 = 1285757) B1285757
theorem B857201 : Blo 570811 857201 := bstep (se 2 (by rfl) ⟨321450, by rfl⟩ : syracuseStep 857201 = 642901) B642901
theorem B1938545 : Blo 570811 1938545 := bstep (se 2 (by rfl) ⟨726954, by rfl⟩ : syracuseStep 1938545 = 1453909) B1453909
theorem B857219 : Blo 570811 857219 := bstep (se 1 (by rfl) ⟨642914, by rfl⟩ : syracuseStep 857219 = 1285829) B1285829
theorem B1840259 : Blo 570811 1840259 := bstep (se 1 (by rfl) ⟨1380194, by rfl⟩ : syracuseStep 1840259 = 2760389) B2760389
theorem B2757773 : Blo 570811 2757773 := bstep (se 3 (by rfl) ⟨517082, by rfl⟩ : syracuseStep 2757773 = 1034165) B1034165
theorem B857249 : Blo 570811 857249 := bstep (se 2 (by rfl) ⟨321468, by rfl⟩ : syracuseStep 857249 = 642937) B642937
theorem B2167985 : Blo 570811 2167985 := bstep (se 2 (by rfl) ⟨812994, by rfl⟩ : syracuseStep 2167985 = 1625989) B1625989
theorem B857267 : Blo 570811 857267 := bstep (se 1 (by rfl) ⟨642950, by rfl⟩ : syracuseStep 857267 = 1285901) B1285901
theorem B857297 : Blo 570811 857297 := bstep (se 2 (by rfl) ⟨321486, by rfl⟩ : syracuseStep 857297 = 642973) B642973
theorem B857315 : Blo 570811 857315 := bstep (se 1 (by rfl) ⟨642986, by rfl⟩ : syracuseStep 857315 = 1285973) B1285973
theorem B3314915 : Blo 570811 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B857345 : Blo 570811 857345 := bstep (se 2 (by rfl) ⟨321504, by rfl⟩ : syracuseStep 857345 = 643009) B643009
theorem B1545475 : Blo 570811 1545475 := bstep (se 1 (by rfl) ⟨1159106, by rfl⟩ : syracuseStep 1545475 = 2318213) B2318213
theorem B857363 : Blo 570811 857363 := bstep (se 1 (by rfl) ⟨643022, by rfl⟩ : syracuseStep 857363 = 1286045) B1286045
theorem B660755 : Blo 570811 660755 := bstep (se 1 (by rfl) ⟨495566, by rfl⟩ : syracuseStep 660755 = 991133) B991133
theorem B857393 : Blo 570811 857393 := bstep (se 2 (by rfl) ⟨321522, by rfl⟩ : syracuseStep 857393 = 643045) B643045
theorem B1447217 : Blo 570811 1447217 := bstep (se 2 (by rfl) ⟨542706, by rfl⟩ : syracuseStep 1447217 = 1085413) B1085413
theorem B857411 : Blo 570811 857411 := bstep (se 1 (by rfl) ⟨643058, by rfl⟩ : syracuseStep 857411 = 1286117) B1286117
theorem B1086787 : Blo 570811 1086787 := bstep (se 1 (by rfl) ⟨815090, by rfl⟩ : syracuseStep 1086787 = 1630181) B1630181
theorem B857441 : Blo 570811 857441 := bstep (se 2 (by rfl) ⟨321540, by rfl⟩ : syracuseStep 857441 = 643081) B643081
theorem B1447267 : Blo 570811 1447267 := bstep (se 1 (by rfl) ⟨1085450, by rfl⟩ : syracuseStep 1447267 = 2170901) B2170901
theorem B1086833 : Blo 570811 1086833 := bstep (se 2 (by rfl) ⟨407562, by rfl⟩ : syracuseStep 1086833 = 815125) B815125
theorem B857459 : Blo 570811 857459 := bstep (se 1 (by rfl) ⟨643094, by rfl⟩ : syracuseStep 857459 = 1286189) B1286189
theorem B726403 : Blo 570811 726403 := bstep (se 1 (by rfl) ⟨544802, by rfl⟩ : syracuseStep 726403 = 1089605) B1089605
theorem B3478925 : Blo 570811 3478925 := bstep (se 3 (by rfl) ⟨652298, by rfl⟩ : syracuseStep 3478925 = 1304597) B1304597
theorem B857489 : Blo 570811 857489 := bstep (se 2 (by rfl) ⟨321558, by rfl⟩ : syracuseStep 857489 = 643117) B643117
theorem B1545617 : Blo 570811 1545617 := bstep (se 2 (by rfl) ⟨579606, by rfl⟩ : syracuseStep 1545617 = 1159213) B1159213
theorem B857507 : Blo 570811 857507 := bstep (se 1 (by rfl) ⟨643130, by rfl⟩ : syracuseStep 857507 = 1286261) B1286261
theorem B857537 : Blo 570811 857537 := bstep (se 2 (by rfl) ⟨321576, by rfl⟩ : syracuseStep 857537 = 643153) B643153
theorem B857555 : Blo 570811 857555 := bstep (se 1 (by rfl) ⟨643166, by rfl⟩ : syracuseStep 857555 = 1286333) B1286333
theorem B726499 : Blo 570811 726499 := bstep (se 1 (by rfl) ⟨544874, by rfl⟩ : syracuseStep 726499 = 1089749) B1089749
theorem B857585 : Blo 570811 857585 := bstep (se 2 (by rfl) ⟨321594, by rfl⟩ : syracuseStep 857585 = 643189) B643189
theorem B1447409 : Blo 570811 1447409 := bstep (se 2 (by rfl) ⟨542778, by rfl⟩ : syracuseStep 1447409 = 1085557) B1085557
theorem B857603 : Blo 570811 857603 := bstep (se 1 (by rfl) ⟨643202, by rfl⟩ : syracuseStep 857603 = 1286405) B1286405
theorem B1840657 : Blo 570811 1840657 := bstep (se 2 (by rfl) ⟨690246, by rfl⟩ : syracuseStep 1840657 = 1380493) B1380493
theorem B857633 : Blo 570811 857633 := bstep (se 2 (by rfl) ⟨321612, by rfl⟩ : syracuseStep 857633 = 643225) B643225
theorem B857651 : Blo 570811 857651 := bstep (se 1 (by rfl) ⟨643238, by rfl⟩ : syracuseStep 857651 = 1286477) B1286477
theorem B857681 : Blo 570811 857681 := bstep (se 2 (by rfl) ⟨321630, by rfl⟩ : syracuseStep 857681 = 643261) B643261
theorem B857699 : Blo 570811 857699 := bstep (se 1 (by rfl) ⟨643274, by rfl⟩ : syracuseStep 857699 = 1286549) B1286549
theorem B857729 : Blo 570811 857729 := bstep (se 2 (by rfl) ⟨321648, by rfl⟩ : syracuseStep 857729 = 643297) B643297
theorem B1939085 : Blo 570811 1939085 := bstep (se 3 (by rfl) ⟨363578, by rfl⟩ : syracuseStep 1939085 = 727157) B727157
theorem B1087121 : Blo 570811 1087121 := bstep (se 2 (by rfl) ⟨407670, by rfl⟩ : syracuseStep 1087121 = 815341) B815341
theorem B857747 : Blo 570811 857747 := bstep (se 1 (by rfl) ⟨643310, by rfl⟩ : syracuseStep 857747 = 1286621) B1286621
theorem B857777 : Blo 570811 857777 := bstep (se 2 (by rfl) ⟨321666, by rfl⟩ : syracuseStep 857777 = 643333) B643333
theorem B857795 : Blo 570811 857795 := bstep (se 1 (by rfl) ⟨643346, by rfl⟩ : syracuseStep 857795 = 1286693) B1286693
theorem B1939139 : Blo 570811 1939139 := bstep (se 1 (by rfl) ⟨1454354, by rfl⟩ : syracuseStep 1939139 = 2908709) B2908709
theorem B857825 : Blo 570811 857825 := bstep (se 2 (by rfl) ⟨321684, by rfl⟩ : syracuseStep 857825 = 643369) B643369
theorem B3479267 : Blo 570811 3479267 := bstep (se 1 (by rfl) ⟨2609450, by rfl⟩ : syracuseStep 3479267 = 5218901) B5218901
theorem B857843 : Blo 570811 857843 := bstep (se 1 (by rfl) ⟨643382, by rfl⟩ : syracuseStep 857843 = 1286765) B1286765
theorem B857873 : Blo 570811 857873 := bstep (se 2 (by rfl) ⟨321702, by rfl⟩ : syracuseStep 857873 = 643405) B643405
theorem B857891 : Blo 570811 857891 := bstep (se 1 (by rfl) ⟨643418, by rfl⟩ : syracuseStep 857891 = 1286837) B1286837
theorem B857921 : Blo 570811 857921 := bstep (se 2 (by rfl) ⟨321720, by rfl⟩ : syracuseStep 857921 = 643441) B643441
theorem B2168653 : Blo 570811 2168653 := bstep (se 3 (by rfl) ⟨406622, by rfl⟩ : syracuseStep 2168653 = 813245) B813245
theorem B857939 : Blo 570811 857939 := bstep (se 1 (by rfl) ⟨643454, by rfl⟩ : syracuseStep 857939 = 1286909) B1286909
theorem B857969 : Blo 570811 857969 := bstep (se 2 (by rfl) ⟨321738, by rfl⟩ : syracuseStep 857969 = 643477) B643477
theorem B857987 : Blo 570811 857987 := bstep (se 1 (by rfl) ⟨643490, by rfl⟩ : syracuseStep 857987 = 1286981) B1286981
theorem B858017 : Blo 570811 858017 := bstep (se 2 (by rfl) ⟨321756, by rfl⟩ : syracuseStep 858017 = 643513) B643513
theorem B858035 : Blo 570811 858035 := bstep (se 1 (by rfl) ⟨643526, by rfl⟩ : syracuseStep 858035 = 1287053) B1287053
theorem B858065 : Blo 570811 858065 := bstep (se 2 (by rfl) ⟨321774, by rfl⟩ : syracuseStep 858065 = 643549) B643549
theorem B1939409 : Blo 570811 1939409 := bstep (se 2 (by rfl) ⟨727278, by rfl⟩ : syracuseStep 1939409 = 1454557) B1454557
theorem B726995 : Blo 570811 726995 := bstep (se 1 (by rfl) ⟨545246, by rfl⟩ : syracuseStep 726995 = 1090493) B1090493
theorem B1841105 : Blo 570811 1841105 := bstep (se 2 (by rfl) ⟨690414, by rfl⟩ : syracuseStep 1841105 = 1380829) B1380829
theorem B858083 : Blo 570811 858083 := bstep (se 1 (by rfl) ⟨643562, by rfl⟩ : syracuseStep 858083 = 1287125) B1287125
theorem B858113 : Blo 570811 858113 := bstep (se 2 (by rfl) ⟨321792, by rfl⟩ : syracuseStep 858113 = 643585) B643585
theorem B858131 : Blo 570811 858131 := bstep (se 1 (by rfl) ⟨643598, by rfl⟩ : syracuseStep 858131 = 1287197) B1287197
theorem B858161 : Blo 570811 858161 := bstep (se 2 (by rfl) ⟨321810, by rfl⟩ : syracuseStep 858161 = 643621) B643621
theorem B858179 : Blo 570811 858179 := bstep (se 1 (by rfl) ⟨643634, by rfl⟩ : syracuseStep 858179 = 1287269) B1287269
theorem B858209 : Blo 570811 858209 := bstep (se 2 (by rfl) ⟨321828, by rfl⟩ : syracuseStep 858209 = 643657) B643657
theorem B858227 : Blo 570811 858227 := bstep (se 1 (by rfl) ⟨643670, by rfl⟩ : syracuseStep 858227 = 1287341) B1287341
theorem B858257 : Blo 570811 858257 := bstep (se 2 (by rfl) ⟨321846, by rfl⟩ : syracuseStep 858257 = 643693) B643693
theorem B858275 : Blo 570811 858275 := bstep (se 1 (by rfl) ⟨643706, by rfl⟩ : syracuseStep 858275 = 1287413) B1287413
theorem B858305 : Blo 570811 858305 := bstep (se 2 (by rfl) ⟨321864, by rfl⟩ : syracuseStep 858305 = 643729) B643729
theorem B858323 : Blo 570811 858323 := bstep (se 1 (by rfl) ⟨643742, by rfl⟩ : syracuseStep 858323 = 1287485) B1287485
theorem B858353 : Blo 570811 858353 := bstep (se 2 (by rfl) ⟨321882, by rfl⟩ : syracuseStep 858353 = 643765) B643765
theorem B858371 : Blo 570811 858371 := bstep (se 1 (by rfl) ⟨643778, by rfl⟩ : syracuseStep 858371 = 1287557) B1287557
theorem B858401 : Blo 570811 858401 := bstep (se 2 (by rfl) ⟨321900, by rfl⟩ : syracuseStep 858401 = 643801) B643801
theorem B858419 : Blo 570811 858419 := bstep (se 1 (by rfl) ⟨643814, by rfl⟩ : syracuseStep 858419 = 1287629) B1287629
theorem B1546577 : Blo 570811 1546577 := bstep (se 2 (by rfl) ⟨579966, by rfl⟩ : syracuseStep 1546577 = 1159933) B1159933
theorem B858449 : Blo 570811 858449 := bstep (se 2 (by rfl) ⟨321918, by rfl⟩ : syracuseStep 858449 = 643837) B643837
theorem B858467 : Blo 570811 858467 := bstep (se 1 (by rfl) ⟨643850, by rfl⟩ : syracuseStep 858467 = 1287701) B1287701
theorem B1087843 : Blo 570811 1087843 := bstep (se 1 (by rfl) ⟨815882, by rfl⟩ : syracuseStep 1087843 = 1631765) B1631765
theorem B858497 : Blo 570811 858497 := bstep (se 2 (by rfl) ⟨321936, by rfl⟩ : syracuseStep 858497 = 643873) B643873
theorem B1284497 : Blo 570811 1284497 := bstep (se 2 (by rfl) ⟨481686, by rfl⟩ : syracuseStep 1284497 = 963373) B963373
theorem B858515 : Blo 570811 858515 := bstep (se 1 (by rfl) ⟨643886, by rfl⟩ : syracuseStep 858515 = 1287773) B1287773
theorem B1284515 : Blo 570811 1284515 := bstep (se 1 (by rfl) ⟨963386, by rfl⟩ : syracuseStep 1284515 = 1926773) B1926773
theorem B858545 : Blo 570811 858545 := bstep (se 2 (by rfl) ⟨321954, by rfl⟩ : syracuseStep 858545 = 643909) B643909
theorem B858563 : Blo 570811 858563 := bstep (se 1 (by rfl) ⟨643922, by rfl⟩ : syracuseStep 858563 = 1287845) B1287845
theorem B1448401 : Blo 570811 1448401 := bstep (se 2 (by rfl) ⟨543150, by rfl⟩ : syracuseStep 1448401 = 1086301) B1086301
theorem B858593 : Blo 570811 858593 := bstep (se 2 (by rfl) ⟨321972, by rfl⟩ : syracuseStep 858593 = 643945) B643945
theorem B1939949 : Blo 570811 1939949 := bstep (se 3 (by rfl) ⟨363740, by rfl⟩ : syracuseStep 1939949 = 727481) B727481
theorem B858611 : Blo 570811 858611 := bstep (se 1 (by rfl) ⟨643958, by rfl⟩ : syracuseStep 858611 = 1287917) B1287917
theorem B858641 : Blo 570811 858641 := bstep (se 2 (by rfl) ⟨321990, by rfl⟩ : syracuseStep 858641 = 643981) B643981
theorem B858659 : Blo 570811 858659 := bstep (se 1 (by rfl) ⟨643994, by rfl⟩ : syracuseStep 858659 = 1287989) B1287989
theorem B858689 : Blo 570811 858689 := bstep (se 2 (by rfl) ⟨322008, by rfl⟩ : syracuseStep 858689 = 644017) B644017
theorem B858707 : Blo 570811 858707 := bstep (se 1 (by rfl) ⟨644030, by rfl⟩ : syracuseStep 858707 = 1288061) B1288061
theorem B2169443 : Blo 570811 2169443 := bstep (se 1 (by rfl) ⟨1627082, by rfl⟩ : syracuseStep 2169443 = 3254165) B3254165
theorem B858737 : Blo 570811 858737 := bstep (se 2 (by rfl) ⟨322026, by rfl⟩ : syracuseStep 858737 = 644053) B644053
theorem B858755 : Blo 570811 858755 := bstep (se 1 (by rfl) ⟨644066, by rfl⟩ : syracuseStep 858755 = 1288133) B1288133
theorem B858785 : Blo 570811 858785 := bstep (se 2 (by rfl) ⟨322044, by rfl⟩ : syracuseStep 858785 = 644089) B644089
theorem B2890403 : Blo 570811 2890403 := bstep (se 1 (by rfl) ⟨2167802, by rfl⟩ : syracuseStep 2890403 = 4335605) B4335605
theorem B1284785 : Blo 570811 1284785 := bstep (se 2 (by rfl) ⟨481794, by rfl⟩ : syracuseStep 1284785 = 963589) B963589
theorem B858803 : Blo 570811 858803 := bstep (se 1 (by rfl) ⟨644102, by rfl⟩ : syracuseStep 858803 = 1288205) B1288205
theorem B1284803 : Blo 570811 1284803 := bstep (se 1 (by rfl) ⟨963602, by rfl⟩ : syracuseStep 1284803 = 1927205) B1927205
theorem B858833 : Blo 570811 858833 := bstep (se 2 (by rfl) ⟨322062, by rfl⟩ : syracuseStep 858833 = 644125) B644125
theorem B1448675 : Blo 570811 1448675 := bstep (se 1 (by rfl) ⟨1086506, by rfl⟩ : syracuseStep 1448675 = 2173013) B2173013
theorem B858851 : Blo 570811 858851 := bstep (se 1 (by rfl) ⟨644138, by rfl⟩ : syracuseStep 858851 = 1288277) B1288277
theorem B1219313 : Blo 570811 1219313 := bstep (se 2 (by rfl) ⟨457242, by rfl⟩ : syracuseStep 1219313 = 914485) B914485
theorem B858881 : Blo 570811 858881 := bstep (se 2 (by rfl) ⟨322080, by rfl⟩ : syracuseStep 858881 = 644161) B644161
theorem B858899 : Blo 570811 858899 := bstep (se 1 (by rfl) ⟨644174, by rfl⟩ : syracuseStep 858899 = 1288349) B1288349
theorem B1088291 : Blo 570811 1088291 := bstep (se 1 (by rfl) ⟨816218, by rfl⟩ : syracuseStep 1088291 = 1632437) B1632437
theorem B858929 : Blo 570811 858929 := bstep (se 2 (by rfl) ⟨322098, by rfl⟩ : syracuseStep 858929 = 644197) B644197
theorem B858947 : Blo 570811 858947 := bstep (se 1 (by rfl) ⟨644210, by rfl⟩ : syracuseStep 858947 = 1288421) B1288421
theorem B858977 : Blo 570811 858977 := bstep (se 2 (by rfl) ⟨322116, by rfl⟩ : syracuseStep 858977 = 644233) B644233
theorem B858995 : Blo 570811 858995 := bstep (se 1 (by rfl) ⟨644246, by rfl⟩ : syracuseStep 858995 = 1288493) B1288493
theorem B859025 : Blo 570811 859025 := bstep (se 2 (by rfl) ⟨322134, by rfl⟩ : syracuseStep 859025 = 644269) B644269
theorem B1448867 : Blo 570811 1448867 := bstep (se 1 (by rfl) ⟨1086650, by rfl⟩ : syracuseStep 1448867 = 2173301) B2173301
theorem B859043 : Blo 570811 859043 := bstep (se 1 (by rfl) ⟨644282, by rfl⟩ : syracuseStep 859043 = 1288565) B1288565
theorem B859073 : Blo 570811 859073 := bstep (se 2 (by rfl) ⟨322152, by rfl⟩ : syracuseStep 859073 = 644305) B644305
theorem B1285073 : Blo 570811 1285073 := bstep (se 2 (by rfl) ⟨481902, by rfl⟩ : syracuseStep 1285073 = 963805) B963805
theorem B859091 : Blo 570811 859091 := bstep (se 1 (by rfl) ⟨644318, by rfl⟩ : syracuseStep 859091 = 1288637) B1288637
theorem B1285091 : Blo 570811 1285091 := bstep (se 1 (by rfl) ⟨963818, by rfl⟩ : syracuseStep 1285091 = 1927637) B1927637
theorem B4889585 : Blo 570811 4889585 := bstep (se 2 (by rfl) ⟨1833594, by rfl⟩ : syracuseStep 4889585 = 3667189) B3667189
theorem B859121 : Blo 570811 859121 := bstep (se 2 (by rfl) ⟨322170, by rfl⟩ : syracuseStep 859121 = 644341) B644341
theorem B859139 : Blo 570811 859139 := bstep (se 1 (by rfl) ⟨644354, by rfl⟩ : syracuseStep 859139 = 1288709) B1288709
theorem B859169 : Blo 570811 859169 := bstep (se 2 (by rfl) ⟨322188, by rfl⟩ : syracuseStep 859169 = 644377) B644377
theorem B3251249 : Blo 570811 3251249 := bstep (se 2 (by rfl) ⟨1219218, by rfl⟩ : syracuseStep 3251249 = 2438437) B2438437
theorem B859187 : Blo 570811 859187 := bstep (se 1 (by rfl) ⟨644390, by rfl⟩ : syracuseStep 859187 = 1288781) B1288781
theorem B1088579 : Blo 570811 1088579 := bstep (se 1 (by rfl) ⟨816434, by rfl⟩ : syracuseStep 1088579 = 1632869) B1632869
theorem B859217 : Blo 570811 859217 := bstep (se 2 (by rfl) ⟨322206, by rfl⟩ : syracuseStep 859217 = 644413) B644413
theorem B859235 : Blo 570811 859235 := bstep (se 1 (by rfl) ⟨644426, by rfl⟩ : syracuseStep 859235 = 1288853) B1288853
theorem B859265 : Blo 570811 859265 := bstep (se 2 (by rfl) ⟨322224, by rfl⟩ : syracuseStep 859265 = 644449) B644449
theorem B859283 : Blo 570811 859283 := bstep (se 1 (by rfl) ⟨644462, by rfl⟩ : syracuseStep 859283 = 1288925) B1288925
theorem B859313 : Blo 570811 859313 := bstep (se 2 (by rfl) ⟨322242, by rfl⟩ : syracuseStep 859313 = 644485) B644485
theorem B859331 : Blo 570811 859331 := bstep (se 1 (by rfl) ⟨644498, by rfl⟩ : syracuseStep 859331 = 1288997) B1288997
theorem B859361 : Blo 570811 859361 := bstep (se 2 (by rfl) ⟨322260, by rfl⟩ : syracuseStep 859361 = 644521) B644521
theorem B1285361 : Blo 570811 1285361 := bstep (se 2 (by rfl) ⟨482010, by rfl⟩ : syracuseStep 1285361 = 964021) B964021
theorem B2170097 : Blo 570811 2170097 := bstep (se 2 (by rfl) ⟨813786, by rfl⟩ : syracuseStep 2170097 = 1627573) B1627573
theorem B859379 : Blo 570811 859379 := bstep (se 1 (by rfl) ⟨644534, by rfl⟩ : syracuseStep 859379 = 1289069) B1289069
theorem B1285379 : Blo 570811 1285379 := bstep (se 1 (by rfl) ⟨964034, by rfl⟩ : syracuseStep 1285379 = 1928069) B1928069
theorem B859409 : Blo 570811 859409 := bstep (se 2 (by rfl) ⟨322278, by rfl⟩ : syracuseStep 859409 = 644557) B644557
theorem B859427 : Blo 570811 859427 := bstep (se 1 (by rfl) ⟨644570, by rfl⟩ : syracuseStep 859427 = 1289141) B1289141
theorem B859457 : Blo 570811 859457 := bstep (se 2 (by rfl) ⟨322296, by rfl⟩ : syracuseStep 859457 = 644593) B644593
theorem B3906893 : Blo 570811 3906893 := bstep (se 3 (by rfl) ⟨732542, by rfl⟩ : syracuseStep 3906893 = 1465085) B1465085
theorem B859475 : Blo 570811 859475 := bstep (se 1 (by rfl) ⟨644606, by rfl⟩ : syracuseStep 859475 = 1289213) B1289213
theorem B859505 : Blo 570811 859505 := bstep (se 2 (by rfl) ⟨322314, by rfl⟩ : syracuseStep 859505 = 644629) B644629
theorem B859523 : Blo 570811 859523 := bstep (se 1 (by rfl) ⟨644642, by rfl⟩ : syracuseStep 859523 = 1289285) B1289285
theorem B859553 : Blo 570811 859553 := bstep (se 2 (by rfl) ⟨322332, by rfl⟩ : syracuseStep 859553 = 644665) B644665
theorem B1547693 : Blo 570811 1547693 := bstep (se 3 (by rfl) ⟨290192, by rfl⟩ : syracuseStep 1547693 = 580385) B580385
theorem B859571 : Blo 570811 859571 := bstep (se 1 (by rfl) ⟨644678, by rfl⟩ : syracuseStep 859571 = 1289357) B1289357
theorem B2891213 : Blo 570811 2891213 := bstep (se 3 (by rfl) ⟨542102, by rfl⟩ : syracuseStep 2891213 = 1084205) B1084205
theorem B859601 : Blo 570811 859601 := bstep (se 2 (by rfl) ⟨322350, by rfl⟩ : syracuseStep 859601 = 644701) B644701
theorem B859619 : Blo 570811 859619 := bstep (se 1 (by rfl) ⟨644714, by rfl⟩ : syracuseStep 859619 = 1289429) B1289429
theorem B859649 : Blo 570811 859649 := bstep (se 2 (by rfl) ⟨322368, by rfl⟩ : syracuseStep 859649 = 644737) B644737
theorem B1285649 : Blo 570811 1285649 := bstep (se 2 (by rfl) ⟨482118, by rfl⟩ : syracuseStep 1285649 = 964237) B964237
theorem B859667 : Blo 570811 859667 := bstep (se 1 (by rfl) ⟨644750, by rfl⟩ : syracuseStep 859667 = 1289501) B1289501
theorem B1285667 : Blo 570811 1285667 := bstep (se 1 (by rfl) ⟨964250, by rfl⟩ : syracuseStep 1285667 = 1928501) B1928501
theorem B859697 : Blo 570811 859697 := bstep (se 2 (by rfl) ⟨322386, by rfl⟩ : syracuseStep 859697 = 644773) B644773
theorem B859715 : Blo 570811 859715 := bstep (se 1 (by rfl) ⟨644786, by rfl⟩ : syracuseStep 859715 = 1289573) B1289573
theorem B859745 : Blo 570811 859745 := bstep (se 2 (by rfl) ⟨322404, by rfl⟩ : syracuseStep 859745 = 644809) B644809
theorem B859763 : Blo 570811 859763 := bstep (se 1 (by rfl) ⟨644822, by rfl⟩ : syracuseStep 859763 = 1289645) B1289645
theorem B859793 : Blo 570811 859793 := bstep (se 2 (by rfl) ⟨322422, by rfl⟩ : syracuseStep 859793 = 644845) B644845
theorem B859811 : Blo 570811 859811 := bstep (se 1 (by rfl) ⟨644858, by rfl⟩ : syracuseStep 859811 = 1289717) B1289717
theorem B859841 : Blo 570811 859841 := bstep (se 2 (by rfl) ⟨322440, by rfl⟩ : syracuseStep 859841 = 644881) B644881
theorem B859859 : Blo 570811 859859 := bstep (se 1 (by rfl) ⟨644894, by rfl⟩ : syracuseStep 859859 = 1289789) B1289789
theorem B859889 : Blo 570811 859889 := bstep (se 2 (by rfl) ⟨322458, by rfl⟩ : syracuseStep 859889 = 644917) B644917
theorem B859907 : Blo 570811 859907 := bstep (se 1 (by rfl) ⟨644930, by rfl⟩ : syracuseStep 859907 = 1289861) B1289861
theorem B859937 : Blo 570811 859937 := bstep (se 2 (by rfl) ⟨322476, by rfl⟩ : syracuseStep 859937 = 644953) B644953
theorem B1285937 : Blo 570811 1285937 := bstep (se 2 (by rfl) ⟨482226, by rfl⟩ : syracuseStep 1285937 = 964453) B964453
theorem B859955 : Blo 570811 859955 := bstep (se 1 (by rfl) ⟨644966, by rfl⟩ : syracuseStep 859955 = 1289933) B1289933
theorem B1285955 : Blo 570811 1285955 := bstep (se 1 (by rfl) ⟨964466, by rfl⟩ : syracuseStep 1285955 = 1928933) B1928933
theorem B1449809 : Blo 570811 1449809 := bstep (se 2 (by rfl) ⟨543678, by rfl⟩ : syracuseStep 1449809 = 1087357) B1087357
theorem B859985 : Blo 570811 859985 := bstep (se 2 (by rfl) ⟨322494, by rfl⟩ : syracuseStep 859985 = 644989) B644989
theorem B860003 : Blo 570811 860003 := bstep (se 1 (by rfl) ⟨645002, by rfl⟩ : syracuseStep 860003 = 1290005) B1290005
theorem B860033 : Blo 570811 860033 := bstep (se 2 (by rfl) ⟨322512, by rfl⟩ : syracuseStep 860033 = 645025) B645025
theorem B1220483 : Blo 570811 1220483 := bstep (se 1 (by rfl) ⟨915362, by rfl⟩ : syracuseStep 1220483 = 1830725) B1830725
theorem B1449859 : Blo 570811 1449859 := bstep (se 1 (by rfl) ⟨1087394, by rfl⟩ : syracuseStep 1449859 = 2174789) B2174789
theorem B860051 : Blo 570811 860051 := bstep (se 1 (by rfl) ⟨645038, by rfl⟩ : syracuseStep 860051 = 1290077) B1290077
theorem B860081 : Blo 570811 860081 := bstep (se 2 (by rfl) ⟨322530, by rfl⟩ : syracuseStep 860081 = 645061) B645061
theorem B860099 : Blo 570811 860099 := bstep (se 1 (by rfl) ⟨645074, by rfl⟩ : syracuseStep 860099 = 1290149) B1290149
theorem B860129 : Blo 570811 860129 := bstep (se 2 (by rfl) ⟨322548, by rfl⟩ : syracuseStep 860129 = 645097) B645097
theorem B1089521 : Blo 570811 1089521 := bstep (se 2 (by rfl) ⟨408570, by rfl⟩ : syracuseStep 1089521 = 817141) B817141
theorem B860147 : Blo 570811 860147 := bstep (se 1 (by rfl) ⟨645110, by rfl⟩ : syracuseStep 860147 = 1290221) B1290221
theorem B1450001 : Blo 570811 1450001 := bstep (se 2 (by rfl) ⟨543750, by rfl⟩ : syracuseStep 1450001 = 1087501) B1087501
theorem B860177 : Blo 570811 860177 := bstep (se 2 (by rfl) ⟨322566, by rfl⟩ : syracuseStep 860177 = 645133) B645133
theorem B860195 : Blo 570811 860195 := bstep (se 1 (by rfl) ⟨645146, by rfl⟩ : syracuseStep 860195 = 1290293) B1290293
theorem B860225 : Blo 570811 860225 := bstep (se 2 (by rfl) ⟨322584, by rfl⟩ : syracuseStep 860225 = 645169) B645169
theorem B1286225 : Blo 570811 1286225 := bstep (se 2 (by rfl) ⟨482334, by rfl⟩ : syracuseStep 1286225 = 964669) B964669
theorem B860243 : Blo 570811 860243 := bstep (se 1 (by rfl) ⟨645182, by rfl⟩ : syracuseStep 860243 = 1290365) B1290365
theorem B1286243 : Blo 570811 1286243 := bstep (se 1 (by rfl) ⟨964682, by rfl⟩ : syracuseStep 1286243 = 1929365) B1929365
theorem B860273 : Blo 570811 860273 := bstep (se 2 (by rfl) ⟨322602, by rfl⟩ : syracuseStep 860273 = 645205) B645205
theorem B860291 : Blo 570811 860291 := bstep (se 1 (by rfl) ⟨645218, by rfl⟩ : syracuseStep 860291 = 1290437) B1290437
theorem B860321 : Blo 570811 860321 := bstep (se 2 (by rfl) ⟨322620, by rfl⟩ : syracuseStep 860321 = 645241) B645241
theorem B860339 : Blo 570811 860339 := bstep (se 1 (by rfl) ⟨645254, by rfl⟩ : syracuseStep 860339 = 1290509) B1290509
theorem B860369 : Blo 570811 860369 := bstep (se 2 (by rfl) ⟨322638, by rfl⟩ : syracuseStep 860369 = 645277) B645277
theorem B3711203 : Blo 570811 3711203 := bstep (se 1 (by rfl) ⟨2783402, by rfl⟩ : syracuseStep 3711203 = 5566805) B5566805
theorem B860387 : Blo 570811 860387 := bstep (se 1 (by rfl) ⟨645290, by rfl⟩ : syracuseStep 860387 = 1290581) B1290581
theorem B860417 : Blo 570811 860417 := bstep (se 2 (by rfl) ⟨322656, by rfl⟩ : syracuseStep 860417 = 645313) B645313
theorem B860435 : Blo 570811 860435 := bstep (se 1 (by rfl) ⟨645326, by rfl⟩ : syracuseStep 860435 = 1290653) B1290653
theorem B860465 : Blo 570811 860465 := bstep (se 2 (by rfl) ⟨322674, by rfl⟩ : syracuseStep 860465 = 645349) B645349
theorem B1548611 : Blo 570811 1548611 := bstep (se 1 (by rfl) ⟨1161458, by rfl⟩ : syracuseStep 1548611 = 2322917) B2322917
theorem B860483 : Blo 570811 860483 := bstep (se 1 (by rfl) ⟨645362, by rfl⟩ : syracuseStep 860483 = 1290725) B1290725
theorem B860513 : Blo 570811 860513 := bstep (se 2 (by rfl) ⟨322692, by rfl⟩ : syracuseStep 860513 = 645385) B645385
theorem B1286513 : Blo 570811 1286513 := bstep (se 2 (by rfl) ⟨482442, by rfl⟩ : syracuseStep 1286513 = 964885) B964885
theorem B860531 : Blo 570811 860531 := bstep (se 1 (by rfl) ⟨645398, by rfl⟩ : syracuseStep 860531 = 1290797) B1290797
theorem B1286531 : Blo 570811 1286531 := bstep (se 1 (by rfl) ⟨964898, by rfl⟩ : syracuseStep 1286531 = 1929797) B1929797
theorem B860561 : Blo 570811 860561 := bstep (se 2 (by rfl) ⟨322710, by rfl⟩ : syracuseStep 860561 = 645421) B645421
theorem B860579 : Blo 570811 860579 := bstep (se 1 (by rfl) ⟨645434, by rfl⟩ : syracuseStep 860579 = 1290869) B1290869
theorem B860609 : Blo 570811 860609 := bstep (se 2 (by rfl) ⟨322728, by rfl⟩ : syracuseStep 860609 = 645457) B645457
theorem B5513669 : Blo 570811 5513669 := bstep (se 4 (by rfl) ⟨516906, by rfl⟩ : syracuseStep 5513669 = 1033813) B1033813
theorem B860627 : Blo 570811 860627 := bstep (se 1 (by rfl) ⟨645470, by rfl⟩ : syracuseStep 860627 = 1290941) B1290941
theorem B3252707 : Blo 570811 3252707 := bstep (se 1 (by rfl) ⟨2439530, by rfl⟩ : syracuseStep 3252707 = 4879061) B4879061
theorem B860657 : Blo 570811 860657 := bstep (se 2 (by rfl) ⟨322746, by rfl⟩ : syracuseStep 860657 = 645493) B645493
theorem B860675 : Blo 570811 860675 := bstep (se 1 (by rfl) ⟨645506, by rfl⟩ : syracuseStep 860675 = 1291013) B1291013
theorem B860705 : Blo 570811 860705 := bstep (se 2 (by rfl) ⟨322764, by rfl⟩ : syracuseStep 860705 = 645529) B645529
theorem B860723 : Blo 570811 860723 := bstep (se 1 (by rfl) ⟨645542, by rfl⟩ : syracuseStep 860723 = 1291085) B1291085
theorem B5972549 : Blo 570811 5972549 := bstep (se 4 (by rfl) ⟨559926, by rfl⟩ : syracuseStep 5972549 = 1119853) B1119853
theorem B860753 : Blo 570811 860753 := bstep (se 2 (by rfl) ⟨322782, by rfl⟩ : syracuseStep 860753 = 645565) B645565
theorem B860771 : Blo 570811 860771 := bstep (se 1 (by rfl) ⟨645578, by rfl⟩ : syracuseStep 860771 = 1291157) B1291157
theorem B860801 : Blo 570811 860801 := bstep (se 2 (by rfl) ⟨322800, by rfl⟩ : syracuseStep 860801 = 645601) B645601
theorem B1286801 : Blo 570811 1286801 := bstep (se 2 (by rfl) ⟨482550, by rfl⟩ : syracuseStep 1286801 = 965101) B965101
theorem B860819 : Blo 570811 860819 := bstep (se 1 (by rfl) ⟨645614, by rfl⟩ : syracuseStep 860819 = 1291229) B1291229
theorem B1286819 : Blo 570811 1286819 := bstep (se 1 (by rfl) ⟨965114, by rfl⟩ : syracuseStep 1286819 = 1930229) B1930229
theorem B2171555 : Blo 570811 2171555 := bstep (se 1 (by rfl) ⟨1628666, by rfl⟩ : syracuseStep 2171555 = 3257333) B3257333
theorem B2171569 : Blo 570811 2171569 := bstep (se 2 (by rfl) ⟨814338, by rfl⟩ : syracuseStep 2171569 = 1628677) B1628677
theorem B860849 : Blo 570811 860849 := bstep (se 2 (by rfl) ⟨322818, by rfl⟩ : syracuseStep 860849 = 645637) B645637
theorem B860867 : Blo 570811 860867 := bstep (se 1 (by rfl) ⟨645650, by rfl⟩ : syracuseStep 860867 = 1291301) B1291301
theorem B860897 : Blo 570811 860897 := bstep (se 2 (by rfl) ⟨322836, by rfl⟩ : syracuseStep 860897 = 645673) B645673
theorem B860915 : Blo 570811 860915 := bstep (se 1 (by rfl) ⟨645686, by rfl⟩ : syracuseStep 860915 = 1291373) B1291373
theorem B860945 : Blo 570811 860945 := bstep (se 2 (by rfl) ⟨322854, by rfl⟩ : syracuseStep 860945 = 645709) B645709
theorem B860963 : Blo 570811 860963 := bstep (se 1 (by rfl) ⟨645722, by rfl⟩ : syracuseStep 860963 = 1291445) B1291445
theorem B860993 : Blo 570811 860993 := bstep (se 2 (by rfl) ⟨322872, by rfl⟩ : syracuseStep 860993 = 645745) B645745
theorem B861011 : Blo 570811 861011 := bstep (se 1 (by rfl) ⟨645758, by rfl⟩ : syracuseStep 861011 = 1291517) B1291517
theorem B861041 : Blo 570811 861041 := bstep (se 2 (by rfl) ⟨322890, by rfl⟩ : syracuseStep 861041 = 645781) B645781
theorem B1090417 : Blo 570811 1090417 := bstep (se 2 (by rfl) ⟨408906, by rfl⟩ : syracuseStep 1090417 = 817813) B817813
theorem B861059 : Blo 570811 861059 := bstep (se 1 (by rfl) ⟨645794, by rfl⟩ : syracuseStep 861059 = 1291589) B1291589
theorem B861089 : Blo 570811 861089 := bstep (se 2 (by rfl) ⟨322908, by rfl⟩ : syracuseStep 861089 = 645817) B645817
theorem B1745837 : Blo 570811 1745837 := bstep (se 3 (by rfl) ⟨327344, by rfl⟩ : syracuseStep 1745837 = 654689) B654689
theorem B1287089 : Blo 570811 1287089 := bstep (se 2 (by rfl) ⟨482658, by rfl⟩ : syracuseStep 1287089 = 965317) B965317
theorem B861107 : Blo 570811 861107 := bstep (se 1 (by rfl) ⟨645830, by rfl⟩ : syracuseStep 861107 = 1291661) B1291661
theorem B1287107 : Blo 570811 1287107 := bstep (se 1 (by rfl) ⟨965330, by rfl⟩ : syracuseStep 1287107 = 1930661) B1930661
theorem B861137 : Blo 570811 861137 := bstep (se 2 (by rfl) ⟨322926, by rfl⟩ : syracuseStep 861137 = 645853) B645853
theorem B861155 : Blo 570811 861155 := bstep (se 1 (by rfl) ⟨645866, by rfl⟩ : syracuseStep 861155 = 1291733) B1291733
theorem B1450993 : Blo 570811 1450993 := bstep (se 2 (by rfl) ⟨544122, by rfl⟩ : syracuseStep 1450993 = 1088245) B1088245
theorem B861185 : Blo 570811 861185 := bstep (se 2 (by rfl) ⟨322944, by rfl⟩ : syracuseStep 861185 = 645889) B645889
theorem B1090577 : Blo 570811 1090577 := bstep (se 2 (by rfl) ⟨408966, by rfl⟩ : syracuseStep 1090577 = 817933) B817933
theorem B861203 : Blo 570811 861203 := bstep (se 1 (by rfl) ⟨645902, by rfl⟩ : syracuseStep 861203 = 1291805) B1291805
theorem B861233 : Blo 570811 861233 := bstep (se 2 (by rfl) ⟨322962, by rfl⟩ : syracuseStep 861233 = 645925) B645925
theorem B861251 : Blo 570811 861251 := bstep (se 1 (by rfl) ⟨645938, by rfl⟩ : syracuseStep 861251 = 1291877) B1291877
theorem B861281 : Blo 570811 861281 := bstep (se 2 (by rfl) ⟨322980, by rfl⟩ : syracuseStep 861281 = 645961) B645961
theorem B861299 : Blo 570811 861299 := bstep (se 1 (by rfl) ⟨645974, by rfl⟩ : syracuseStep 861299 = 1291949) B1291949
theorem B861329 : Blo 570811 861329 := bstep (se 2 (by rfl) ⟨322998, by rfl⟩ : syracuseStep 861329 = 645997) B645997
theorem B861347 : Blo 570811 861347 := bstep (se 1 (by rfl) ⟨646010, by rfl⟩ : syracuseStep 861347 = 1292021) B1292021
theorem B861377 : Blo 570811 861377 := bstep (se 2 (by rfl) ⟨323016, by rfl⟩ : syracuseStep 861377 = 646033) B646033
theorem B1287377 : Blo 570811 1287377 := bstep (se 2 (by rfl) ⟨482766, by rfl⟩ : syracuseStep 1287377 = 965533) B965533
theorem B861395 : Blo 570811 861395 := bstep (se 1 (by rfl) ⟨646046, by rfl⟩ : syracuseStep 861395 = 1292093) B1292093
theorem B1287395 : Blo 570811 1287395 := bstep (se 1 (by rfl) ⟨965546, by rfl⟩ : syracuseStep 1287395 = 1931093) B1931093
theorem B861425 : Blo 570811 861425 := bstep (se 2 (by rfl) ⟨323034, by rfl⟩ : syracuseStep 861425 = 646069) B646069
theorem B1451267 : Blo 570811 1451267 := bstep (se 1 (by rfl) ⟨1088450, by rfl⟩ : syracuseStep 1451267 = 2176901) B2176901
theorem B861443 : Blo 570811 861443 := bstep (se 1 (by rfl) ⟨646082, by rfl⟩ : syracuseStep 861443 = 1292165) B1292165
theorem B861473 : Blo 570811 861473 := bstep (se 2 (by rfl) ⟨323052, by rfl⟩ : syracuseStep 861473 = 646105) B646105
theorem B861491 : Blo 570811 861491 := bstep (se 1 (by rfl) ⟨646118, by rfl⟩ : syracuseStep 861491 = 1292237) B1292237
theorem B861521 : Blo 570811 861521 := bstep (se 2 (by rfl) ⟨323070, by rfl⟩ : syracuseStep 861521 = 646141) B646141
theorem B861539 : Blo 570811 861539 := bstep (se 1 (by rfl) ⟨646154, by rfl⟩ : syracuseStep 861539 = 1292309) B1292309
theorem B861569 : Blo 570811 861569 := bstep (se 2 (by rfl) ⟨323088, by rfl⟩ : syracuseStep 861569 = 646177) B646177
theorem B861587 : Blo 570811 861587 := bstep (se 1 (by rfl) ⟨646190, by rfl⟩ : syracuseStep 861587 = 1292381) B1292381
theorem B1090979 : Blo 570811 1090979 := bstep (se 1 (by rfl) ⟨818234, by rfl⟩ : syracuseStep 1090979 = 1636469) B1636469
theorem B861617 : Blo 570811 861617 := bstep (se 2 (by rfl) ⟨323106, by rfl⟩ : syracuseStep 861617 = 646213) B646213
theorem B1451459 : Blo 570811 1451459 := bstep (se 1 (by rfl) ⟨1088594, by rfl⟩ : syracuseStep 1451459 = 2177189) B2177189
theorem B861635 : Blo 570811 861635 := bstep (se 1 (by rfl) ⟨646226, by rfl⟩ : syracuseStep 861635 = 1292453) B1292453
theorem B3253709 : Blo 570811 3253709 := bstep (se 3 (by rfl) ⟨610070, by rfl⟩ : syracuseStep 3253709 = 1220141) B1220141
theorem B861665 : Blo 570811 861665 := bstep (se 2 (by rfl) ⟨323124, by rfl⟩ : syracuseStep 861665 = 646249) B646249
theorem B1287665 : Blo 570811 1287665 := bstep (se 2 (by rfl) ⟨482874, by rfl⟩ : syracuseStep 1287665 = 965749) B965749
theorem B861683 : Blo 570811 861683 := bstep (se 1 (by rfl) ⟨646262, by rfl⟩ : syracuseStep 861683 = 1292525) B1292525
theorem B1287683 : Blo 570811 1287683 := bstep (se 1 (by rfl) ⟨965762, by rfl⟩ : syracuseStep 1287683 = 1931525) B1931525
theorem B861713 : Blo 570811 861713 := bstep (se 2 (by rfl) ⟨323142, by rfl⟩ : syracuseStep 861713 = 646285) B646285
theorem B861731 : Blo 570811 861731 := bstep (se 1 (by rfl) ⟨646298, by rfl⟩ : syracuseStep 861731 = 1292597) B1292597
theorem B861761 : Blo 570811 861761 := bstep (se 2 (by rfl) ⟨323160, by rfl⟩ : syracuseStep 861761 = 646321) B646321
theorem B861779 : Blo 570811 861779 := bstep (se 1 (by rfl) ⟨646334, by rfl⟩ : syracuseStep 861779 = 1292669) B1292669
theorem B861809 : Blo 570811 861809 := bstep (se 2 (by rfl) ⟨323178, by rfl⟩ : syracuseStep 861809 = 646357) B646357
theorem B861827 : Blo 570811 861827 := bstep (se 1 (by rfl) ⟨646370, by rfl⟩ : syracuseStep 861827 = 1292741) B1292741
theorem B861857 : Blo 570811 861857 := bstep (se 2 (by rfl) ⟨323196, by rfl⟩ : syracuseStep 861857 = 646393) B646393
theorem B861875 : Blo 570811 861875 := bstep (se 1 (by rfl) ⟨646406, by rfl⟩ : syracuseStep 861875 = 1292813) B1292813
theorem B1550029 : Blo 570811 1550029 := bstep (se 3 (by rfl) ⟨290630, by rfl⟩ : syracuseStep 1550029 = 581261) B581261
theorem B861905 : Blo 570811 861905 := bstep (se 2 (by rfl) ⟨323214, by rfl⟩ : syracuseStep 861905 = 646429) B646429
theorem B861923 : Blo 570811 861923 := bstep (se 1 (by rfl) ⟨646442, by rfl⟩ : syracuseStep 861923 = 1292885) B1292885
theorem B861953 : Blo 570811 861953 := bstep (se 2 (by rfl) ⟨323232, by rfl⟩ : syracuseStep 861953 = 646465) B646465
theorem B1287953 : Blo 570811 1287953 := bstep (se 2 (by rfl) ⟨482982, by rfl⟩ : syracuseStep 1287953 = 965965) B965965
theorem B861971 : Blo 570811 861971 := bstep (se 1 (by rfl) ⟨646478, by rfl⟩ : syracuseStep 861971 = 1292957) B1292957
theorem B1287971 : Blo 570811 1287971 := bstep (se 1 (by rfl) ⟨965978, by rfl⟩ : syracuseStep 1287971 = 1931957) B1931957
theorem B862001 : Blo 570811 862001 := bstep (se 2 (by rfl) ⟨323250, by rfl⟩ : syracuseStep 862001 = 646501) B646501
theorem B862019 : Blo 570811 862019 := bstep (se 1 (by rfl) ⟨646514, by rfl⟩ : syracuseStep 862019 = 1293029) B1293029
theorem B862049 : Blo 570811 862049 := bstep (se 2 (by rfl) ⟨323268, by rfl⟩ : syracuseStep 862049 = 646537) B646537
theorem B1222499 : Blo 570811 1222499 := bstep (se 1 (by rfl) ⟨916874, by rfl⟩ : syracuseStep 1222499 = 1833749) B1833749
theorem B862067 : Blo 570811 862067 := bstep (se 1 (by rfl) ⟨646550, by rfl⟩ : syracuseStep 862067 = 1293101) B1293101
theorem B862097 : Blo 570811 862097 := bstep (se 2 (by rfl) ⟨323286, by rfl⟩ : syracuseStep 862097 = 646573) B646573
theorem B862115 : Blo 570811 862115 := bstep (se 1 (by rfl) ⟨646586, by rfl⟩ : syracuseStep 862115 = 1293173) B1293173
theorem B862145 : Blo 570811 862145 := bstep (se 2 (by rfl) ⟨323304, by rfl⟩ : syracuseStep 862145 = 646609) B646609
theorem B862163 : Blo 570811 862163 := bstep (se 1 (by rfl) ⟨646622, by rfl⟩ : syracuseStep 862163 = 1293245) B1293245
theorem B862193 : Blo 570811 862193 := bstep (se 2 (by rfl) ⟨323322, by rfl⟩ : syracuseStep 862193 = 646645) B646645
theorem B862211 : Blo 570811 862211 := bstep (se 1 (by rfl) ⟨646658, by rfl⟩ : syracuseStep 862211 = 1293317) B1293317
theorem B1288241 : Blo 570811 1288241 := bstep (se 2 (by rfl) ⟨483090, by rfl⟩ : syracuseStep 1288241 = 966181) B966181
theorem B1484867 : Blo 570811 1484867 := bstep (se 1 (by rfl) ⟨1113650, by rfl⟩ : syracuseStep 1484867 = 2227301) B2227301
theorem B1288259 : Blo 570811 1288259 := bstep (se 1 (by rfl) ⟨966194, by rfl⟩ : syracuseStep 1288259 = 1932389) B1932389
theorem B2173027 : Blo 570811 2173027 := bstep (se 1 (by rfl) ⟨1629770, by rfl⟩ : syracuseStep 2173027 = 3259541) B3259541
theorem B7350371 : Blo 570811 7350371 := bstep (se 1 (by rfl) ⟨5512778, by rfl⟩ : syracuseStep 7350371 = 11025557) B11025557
theorem B2894129 : Blo 570811 2894129 := bstep (se 2 (by rfl) ⟨1085298, by rfl⟩ : syracuseStep 2894129 = 2170597) B2170597
theorem B2206001 : Blo 570811 2206001 := bstep (se 2 (by rfl) ⟨827250, by rfl⟩ : syracuseStep 2206001 = 1654501) B1654501
theorem B1288529 : Blo 570811 1288529 := bstep (se 2 (by rfl) ⟨483198, by rfl⟩ : syracuseStep 1288529 = 966397) B966397
theorem B6596963 : Blo 570811 6596963 := bstep (se 1 (by rfl) ⟨4947722, by rfl⟩ : syracuseStep 6596963 = 9895445) B9895445
theorem B1288547 : Blo 570811 1288547 := bstep (se 1 (by rfl) ⟨966410, by rfl⟩ : syracuseStep 1288547 = 1932821) B1932821
theorem B1452401 : Blo 570811 1452401 := bstep (se 2 (by rfl) ⟨544650, by rfl⟩ : syracuseStep 1452401 = 1089301) B1089301
theorem B1452451 : Blo 570811 1452451 := bstep (se 1 (by rfl) ⟨1089338, by rfl⟩ : syracuseStep 1452451 = 2178677) B2178677
theorem B1452593 : Blo 570811 1452593 := bstep (se 2 (by rfl) ⟨544722, by rfl⟩ : syracuseStep 1452593 = 1089445) B1089445
theorem B1288817 : Blo 570811 1288817 := bstep (se 2 (by rfl) ⟨483306, by rfl⟩ : syracuseStep 1288817 = 966613) B966613
theorem B1288835 : Blo 570811 1288835 := bstep (se 1 (by rfl) ⟨966626, by rfl⟩ : syracuseStep 1288835 = 1933253) B1933253
theorem B1157809 : Blo 570811 1157809 := bstep (se 2 (by rfl) ⟨434178, by rfl⟩ : syracuseStep 1157809 = 868357) B868357
theorem B1289105 : Blo 570811 1289105 := bstep (se 2 (by rfl) ⟨483414, by rfl⟩ : syracuseStep 1289105 = 966829) B966829
theorem B1289123 : Blo 570811 1289123 := bstep (se 1 (by rfl) ⟨966842, by rfl⟩ : syracuseStep 1289123 = 1933685) B1933685
theorem B1289393 : Blo 570811 1289393 := bstep (se 2 (by rfl) ⟨483522, by rfl⟩ : syracuseStep 1289393 = 967045) B967045
theorem B1289411 : Blo 570811 1289411 := bstep (se 1 (by rfl) ⟨967058, by rfl⟩ : syracuseStep 1289411 = 1934117) B1934117
theorem B11775203 : Blo 570811 11775203 := bstep (se 1 (by rfl) ⟨8831402, by rfl⟩ : syracuseStep 11775203 = 17662805) B17662805
theorem B3681541 : Blo 570811 3681541 := bstep (se 4 (by rfl) ⟨345144, by rfl⟩ : syracuseStep 3681541 = 690289) B690289
theorem B1649933 : Blo 570811 1649933 := bstep (se 3 (by rfl) ⟨309362, by rfl⟩ : syracuseStep 1649933 = 618725) B618725
theorem B1289681 : Blo 570811 1289681 := bstep (se 2 (by rfl) ⟨483630, by rfl⟩ : syracuseStep 1289681 = 967261) B967261
theorem B1289699 : Blo 570811 1289699 := bstep (se 1 (by rfl) ⟨967274, by rfl⟩ : syracuseStep 1289699 = 1934549) B1934549
theorem B1453585 : Blo 570811 1453585 := bstep (se 2 (by rfl) ⟨545094, by rfl⟩ : syracuseStep 1453585 = 1090189) B1090189
theorem B1552049 : Blo 570811 1552049 := bstep (se 2 (by rfl) ⟨582018, by rfl⟩ : syracuseStep 1552049 = 1164037) B1164037
theorem B2895587 : Blo 570811 2895587 := bstep (se 1 (by rfl) ⟨2171690, by rfl⟩ : syracuseStep 2895587 = 4343381) B4343381
theorem B1289969 : Blo 570811 1289969 := bstep (se 2 (by rfl) ⟨483738, by rfl⟩ : syracuseStep 1289969 = 967477) B967477
theorem B1289987 : Blo 570811 1289987 := bstep (se 1 (by rfl) ⟨967490, by rfl⟩ : syracuseStep 1289987 = 1934981) B1934981
theorem B1453859 : Blo 570811 1453859 := bstep (se 1 (by rfl) ⟨1090394, by rfl⟩ : syracuseStep 1453859 = 2180789) B2180789
theorem B1224515 : Blo 570811 1224515 := bstep (se 1 (by rfl) ⟨918386, by rfl⟩ : syracuseStep 1224515 = 1836773) B1836773
theorem B4337549 : Blo 570811 4337549 := bstep (se 3 (by rfl) ⟨813290, by rfl⟩ : syracuseStep 4337549 = 1626581) B1626581
theorem B1454051 : Blo 570811 1454051 := bstep (se 1 (by rfl) ⟨1090538, by rfl⟩ : syracuseStep 1454051 = 2181077) B2181077
theorem B1290257 : Blo 570811 1290257 := bstep (se 2 (by rfl) ⟨483846, by rfl⟩ : syracuseStep 1290257 = 967693) B967693
theorem B1290275 : Blo 570811 1290275 := bstep (se 1 (by rfl) ⟨967706, by rfl⟩ : syracuseStep 1290275 = 1935413) B1935413
theorem B3584099 : Blo 570811 3584099 := bstep (se 1 (by rfl) ⟨2688074, by rfl⟩ : syracuseStep 3584099 = 5376149) B5376149
theorem B6697073 : Blo 570811 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B1552547 : Blo 570811 1552547 := bstep (se 1 (by rfl) ⟨1164410, by rfl⟩ : syracuseStep 1552547 = 2328821) B2328821
theorem B6205681 : Blo 570811 6205681 := bstep (se 2 (by rfl) ⟨2327130, by rfl⟩ : syracuseStep 6205681 = 4654261) B4654261
theorem B2175245 : Blo 570811 2175245 := bstep (se 3 (by rfl) ⟨407858, by rfl⟩ : syracuseStep 2175245 = 815717) B815717
theorem B3256625 : Blo 570811 3256625 := bstep (se 2 (by rfl) ⟨1221234, by rfl⟩ : syracuseStep 3256625 = 2442469) B2442469
theorem B1290545 : Blo 570811 1290545 := bstep (se 2 (by rfl) ⟨483954, by rfl⟩ : syracuseStep 1290545 = 967909) B967909
theorem B1290563 : Blo 570811 1290563 := bstep (se 1 (by rfl) ⟨967922, by rfl⟩ : syracuseStep 1290563 = 1935845) B1935845
theorem B2896397 : Blo 570811 2896397 := bstep (se 3 (by rfl) ⟨543074, by rfl⟩ : syracuseStep 2896397 = 1086149) B1086149
theorem B2241037 : Blo 570811 2241037 := bstep (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) B840389
theorem B1290833 : Blo 570811 1290833 := bstep (se 2 (by rfl) ⟨484062, by rfl⟩ : syracuseStep 1290833 = 968125) B968125
theorem B1290851 : Blo 570811 1290851 := bstep (se 1 (by rfl) ⟨968138, by rfl⟩ : syracuseStep 1290851 = 1936277) B1936277
theorem B930449 : Blo 570811 930449 := bstep (se 2 (by rfl) ⟨348918, by rfl⟩ : syracuseStep 930449 = 697837) B697837
theorem B963265 : Blo 570811 963265 := bstep (se 2 (by rfl) ⟨361224, by rfl⟩ : syracuseStep 963265 = 722449) B722449
theorem B1028803 : Blo 570811 1028803 := bstep (se 1 (by rfl) ⟨771602, by rfl⟩ : syracuseStep 1028803 = 1543205) B1543205
theorem B963299 : Blo 570811 963299 := bstep (se 1 (by rfl) ⟨722474, by rfl⟩ : syracuseStep 963299 = 1444949) B1444949
theorem B963427 : Blo 570811 963427 := bstep (se 1 (by rfl) ⟨722570, by rfl⟩ : syracuseStep 963427 = 1445141) B1445141
theorem B1291121 : Blo 570811 1291121 := bstep (se 2 (by rfl) ⟨484170, by rfl⟩ : syracuseStep 1291121 = 968341) B968341
theorem B1291139 : Blo 570811 1291139 := bstep (se 1 (by rfl) ⟨968354, by rfl⟩ : syracuseStep 1291139 = 1936709) B1936709
theorem B1454993 : Blo 570811 1454993 := bstep (se 2 (by rfl) ⟨545622, by rfl⟩ : syracuseStep 1454993 = 1091245) B1091245
theorem B1029091 : Blo 570811 1029091 := bstep (se 1 (by rfl) ⟨771818, by rfl⟩ : syracuseStep 1029091 = 1543637) B1543637
theorem B963569 : Blo 570811 963569 := bstep (se 2 (by rfl) ⟨361338, by rfl⟩ : syracuseStep 963569 = 722677) B722677
theorem B1225763 : Blo 570811 1225763 := bstep (se 1 (by rfl) ⟨919322, by rfl⟩ : syracuseStep 1225763 = 1838645) B1838645
theorem B1553489 : Blo 570811 1553489 := bstep (se 2 (by rfl) ⟨582558, by rfl⟩ : syracuseStep 1553489 = 1165117) B1165117
theorem B963697 : Blo 570811 963697 := bstep (se 2 (by rfl) ⟨361386, by rfl⟩ : syracuseStep 963697 = 722773) B722773
theorem B1291409 : Blo 570811 1291409 := bstep (se 2 (by rfl) ⟨484278, by rfl⟩ : syracuseStep 1291409 = 968557) B968557
theorem B963731 : Blo 570811 963731 := bstep (se 1 (by rfl) ⟨722798, by rfl⟩ : syracuseStep 963731 = 1445597) B1445597
theorem B1291427 : Blo 570811 1291427 := bstep (se 1 (by rfl) ⟨968570, by rfl⟩ : syracuseStep 1291427 = 1937141) B1937141
theorem B23442659 : Blo 570811 23442659 := bstep (se 1 (by rfl) ⟨17581994, by rfl⟩ : syracuseStep 23442659 = 35163989) B35163989
theorem B12367075 : Blo 570811 12367075 := bstep (se 1 (by rfl) ⟨9275306, by rfl⟩ : syracuseStep 12367075 = 18550613) B18550613
theorem B963859 : Blo 570811 963859 := bstep (se 1 (by rfl) ⟨722894, by rfl⟩ : syracuseStep 963859 = 1445789) B1445789
theorem B964001 : Blo 570811 964001 := bstep (se 2 (by rfl) ⟨361500, by rfl⟩ : syracuseStep 964001 = 723001) B723001
theorem B1291697 : Blo 570811 1291697 := bstep (se 2 (by rfl) ⟨484386, by rfl⟩ : syracuseStep 1291697 = 968773) B968773
theorem B570819 : Blo 570811 570819 := bstep (se 1 (by rfl) ⟨428114, by rfl⟩ : syracuseStep 570819 = 856229) B856229
theorem B1291715 : Blo 570811 1291715 := bstep (se 1 (by rfl) ⟨968786, by rfl⟩ : syracuseStep 1291715 = 1937573) B1937573
theorem B570835 : Blo 570811 570835 := bstep (se 1 (by rfl) ⟨428126, by rfl⟩ : syracuseStep 570835 = 856253) B856253
theorem B570851 : Blo 570811 570851 := bstep (se 1 (by rfl) ⟨428138, by rfl⟩ : syracuseStep 570851 = 856277) B856277
theorem B570867 : Blo 570811 570867 := bstep (se 1 (by rfl) ⟨428150, by rfl⟩ : syracuseStep 570867 = 856301) B856301
theorem B570883 : Blo 570811 570883 := bstep (se 1 (by rfl) ⟨428162, by rfl⟩ : syracuseStep 570883 = 856325) B856325
theorem B570899 : Blo 570811 570899 := bstep (se 1 (by rfl) ⟨428174, by rfl⟩ : syracuseStep 570899 = 856349) B856349
theorem B964129 : Blo 570811 964129 := bstep (se 2 (by rfl) ⟨361548, by rfl⟩ : syracuseStep 964129 = 723097) B723097
theorem B570915 : Blo 570811 570915 := bstep (se 1 (by rfl) ⟨428186, by rfl⟩ : syracuseStep 570915 = 856373) B856373
theorem B570931 : Blo 570811 570931 := bstep (se 1 (by rfl) ⟨428198, by rfl⟩ : syracuseStep 570931 = 856397) B856397
theorem B570947 : Blo 570811 570947 := bstep (se 1 (by rfl) ⟨428210, by rfl⟩ : syracuseStep 570947 = 856421) B856421
theorem B964163 : Blo 570811 964163 := bstep (se 1 (by rfl) ⟨723122, by rfl⟩ : syracuseStep 964163 = 1446245) B1446245
theorem B570963 : Blo 570811 570963 := bstep (se 1 (by rfl) ⟨428222, by rfl⟩ : syracuseStep 570963 = 856445) B856445
theorem B570979 : Blo 570811 570979 := bstep (se 1 (by rfl) ⟨428234, by rfl⟩ : syracuseStep 570979 = 856469) B856469
theorem B6534755 : Blo 570811 6534755 := bstep (se 1 (by rfl) ⟨4901066, by rfl⟩ : syracuseStep 6534755 = 9802133) B9802133
theorem B1226353 : Blo 570811 1226353 := bstep (se 2 (by rfl) ⟨459882, by rfl⟩ : syracuseStep 1226353 = 919765) B919765
theorem B570995 : Blo 570811 570995 := bstep (se 1 (by rfl) ⟨428246, by rfl⟩ : syracuseStep 570995 = 856493) B856493
theorem B571011 : Blo 570811 571011 := bstep (se 1 (by rfl) ⟨428258, by rfl⟩ : syracuseStep 571011 = 856517) B856517
theorem B571027 : Blo 570811 571027 := bstep (se 1 (by rfl) ⟨428270, by rfl⟩ : syracuseStep 571027 = 856541) B856541
theorem B571043 : Blo 570811 571043 := bstep (se 1 (by rfl) ⟨428282, by rfl⟩ : syracuseStep 571043 = 856565) B856565
theorem B571059 : Blo 570811 571059 := bstep (se 1 (by rfl) ⟨428294, by rfl⟩ : syracuseStep 571059 = 856589) B856589
theorem B571075 : Blo 570811 571075 := bstep (se 1 (by rfl) ⟨428306, by rfl⟩ : syracuseStep 571075 = 856613) B856613
theorem B964291 : Blo 570811 964291 := bstep (se 1 (by rfl) ⟨723218, by rfl⟩ : syracuseStep 964291 = 1446437) B1446437
theorem B1291985 : Blo 570811 1291985 := bstep (se 2 (by rfl) ⟨484494, by rfl⟩ : syracuseStep 1291985 = 968989) B968989
theorem B571091 : Blo 570811 571091 := bstep (se 1 (by rfl) ⟨428318, by rfl⟩ : syracuseStep 571091 = 856637) B856637
theorem B571107 : Blo 570811 571107 := bstep (se 1 (by rfl) ⟨428330, by rfl⟩ : syracuseStep 571107 = 856661) B856661
theorem B3258083 : Blo 570811 3258083 := bstep (se 1 (by rfl) ⟨2443562, by rfl⟩ : syracuseStep 3258083 = 4887125) B4887125
theorem B1292003 : Blo 570811 1292003 := bstep (se 1 (by rfl) ⟨969002, by rfl⟩ : syracuseStep 1292003 = 1938005) B1938005
theorem B571123 : Blo 570811 571123 := bstep (se 1 (by rfl) ⟨428342, by rfl⟩ : syracuseStep 571123 = 856685) B856685
theorem B571139 : Blo 570811 571139 := bstep (se 1 (by rfl) ⟨428354, by rfl⟩ : syracuseStep 571139 = 856709) B856709
theorem B571155 : Blo 570811 571155 := bstep (se 1 (by rfl) ⟨428366, by rfl⟩ : syracuseStep 571155 = 856733) B856733
theorem B571171 : Blo 570811 571171 := bstep (se 1 (by rfl) ⟨428378, by rfl⟩ : syracuseStep 571171 = 856757) B856757
theorem B571187 : Blo 570811 571187 := bstep (se 1 (by rfl) ⟨428390, by rfl⟩ : syracuseStep 571187 = 856781) B856781
theorem B571203 : Blo 570811 571203 := bstep (se 1 (by rfl) ⟨428402, by rfl⟩ : syracuseStep 571203 = 856805) B856805
theorem B964433 : Blo 570811 964433 := bstep (se 2 (by rfl) ⟨361662, by rfl⟩ : syracuseStep 964433 = 723325) B723325
theorem B571219 : Blo 570811 571219 := bstep (se 1 (by rfl) ⟨428414, by rfl⟩ : syracuseStep 571219 = 856829) B856829
theorem B571235 : Blo 570811 571235 := bstep (se 1 (by rfl) ⟨428426, by rfl⟩ : syracuseStep 571235 = 856853) B856853
theorem B571251 : Blo 570811 571251 := bstep (se 1 (by rfl) ⟨428438, by rfl⟩ : syracuseStep 571251 = 856877) B856877
theorem B571267 : Blo 570811 571267 := bstep (se 1 (by rfl) ⟨428450, by rfl⟩ : syracuseStep 571267 = 856901) B856901
theorem B571283 : Blo 570811 571283 := bstep (se 1 (by rfl) ⟨428462, by rfl⟩ : syracuseStep 571283 = 856925) B856925
theorem B571299 : Blo 570811 571299 := bstep (se 1 (by rfl) ⟨428474, by rfl⟩ : syracuseStep 571299 = 856949) B856949
theorem B571315 : Blo 570811 571315 := bstep (se 1 (by rfl) ⟨428486, by rfl⟩ : syracuseStep 571315 = 856973) B856973
theorem B571331 : Blo 570811 571331 := bstep (se 1 (by rfl) ⟨428498, by rfl⟩ : syracuseStep 571331 = 856997) B856997
theorem B964561 : Blo 570811 964561 := bstep (se 2 (by rfl) ⟨361710, by rfl⟩ : syracuseStep 964561 = 723421) B723421
theorem B571347 : Blo 570811 571347 := bstep (se 1 (by rfl) ⟨428510, by rfl⟩ : syracuseStep 571347 = 857021) B857021
theorem B571363 : Blo 570811 571363 := bstep (se 1 (by rfl) ⟨428522, by rfl⟩ : syracuseStep 571363 = 857045) B857045
theorem B1292273 : Blo 570811 1292273 := bstep (se 2 (by rfl) ⟨484602, by rfl⟩ : syracuseStep 1292273 = 969205) B969205
theorem B571379 : Blo 570811 571379 := bstep (se 1 (by rfl) ⟨428534, by rfl⟩ : syracuseStep 571379 = 857069) B857069
theorem B964595 : Blo 570811 964595 := bstep (se 1 (by rfl) ⟨723446, by rfl⟩ : syracuseStep 964595 = 1446893) B1446893
theorem B571395 : Blo 570811 571395 := bstep (se 1 (by rfl) ⟨428546, by rfl⟩ : syracuseStep 571395 = 857093) B857093
theorem B1292291 : Blo 570811 1292291 := bstep (se 1 (by rfl) ⟨969218, by rfl⟩ : syracuseStep 1292291 = 1938437) B1938437
theorem B571411 : Blo 570811 571411 := bstep (se 1 (by rfl) ⟨428558, by rfl⟩ : syracuseStep 571411 = 857117) B857117
theorem B571427 : Blo 570811 571427 := bstep (se 1 (by rfl) ⟨428570, by rfl⟩ : syracuseStep 571427 = 857141) B857141
theorem B571443 : Blo 570811 571443 := bstep (se 1 (by rfl) ⟨428582, by rfl⟩ : syracuseStep 571443 = 857165) B857165
theorem B571459 : Blo 570811 571459 := bstep (se 1 (by rfl) ⟨428594, by rfl⟩ : syracuseStep 571459 = 857189) B857189
theorem B571475 : Blo 570811 571475 := bstep (se 1 (by rfl) ⟨428606, by rfl⟩ : syracuseStep 571475 = 857213) B857213
theorem B571491 : Blo 570811 571491 := bstep (se 1 (by rfl) ⟨428618, by rfl⟩ : syracuseStep 571491 = 857237) B857237
theorem B571507 : Blo 570811 571507 := bstep (se 1 (by rfl) ⟨428630, by rfl⟩ : syracuseStep 571507 = 857261) B857261
theorem B964723 : Blo 570811 964723 := bstep (se 1 (by rfl) ⟨723542, by rfl⟩ : syracuseStep 964723 = 1447085) B1447085
theorem B571523 : Blo 570811 571523 := bstep (se 1 (by rfl) ⟨428642, by rfl⟩ : syracuseStep 571523 = 857285) B857285
theorem B571539 : Blo 570811 571539 := bstep (se 1 (by rfl) ⟨428654, by rfl⟩ : syracuseStep 571539 = 857309) B857309
theorem B571555 : Blo 570811 571555 := bstep (se 1 (by rfl) ⟨428666, by rfl⟩ : syracuseStep 571555 = 857333) B857333
theorem B571571 : Blo 570811 571571 := bstep (se 1 (by rfl) ⟨428678, by rfl⟩ : syracuseStep 571571 = 857357) B857357
theorem B571587 : Blo 570811 571587 := bstep (se 1 (by rfl) ⟨428690, by rfl⟩ : syracuseStep 571587 = 857381) B857381
theorem B571603 : Blo 570811 571603 := bstep (se 1 (by rfl) ⟨428702, by rfl⟩ : syracuseStep 571603 = 857405) B857405
theorem B2439395 : Blo 570811 2439395 := bstep (se 1 (by rfl) ⟨1829546, by rfl⟩ : syracuseStep 2439395 = 3659093) B3659093
theorem B571619 : Blo 570811 571619 := bstep (se 1 (by rfl) ⟨428714, by rfl⟩ : syracuseStep 571619 = 857429) B857429
theorem B571635 : Blo 570811 571635 := bstep (se 1 (by rfl) ⟨428726, by rfl⟩ : syracuseStep 571635 = 857453) B857453
theorem B964865 : Blo 570811 964865 := bstep (se 2 (by rfl) ⟨361824, by rfl⟩ : syracuseStep 964865 = 723649) B723649
theorem B571651 : Blo 570811 571651 := bstep (se 1 (by rfl) ⟨428738, by rfl⟩ : syracuseStep 571651 = 857477) B857477
theorem B1292561 : Blo 570811 1292561 := bstep (se 2 (by rfl) ⟨484710, by rfl⟩ : syracuseStep 1292561 = 969421) B969421
theorem B571667 : Blo 570811 571667 := bstep (se 1 (by rfl) ⟨428750, by rfl⟩ : syracuseStep 571667 = 857501) B857501
theorem B571683 : Blo 570811 571683 := bstep (se 1 (by rfl) ⟨428762, by rfl⟩ : syracuseStep 571683 = 857525) B857525
theorem B1292579 : Blo 570811 1292579 := bstep (se 1 (by rfl) ⟨969434, by rfl⟩ : syracuseStep 1292579 = 1938869) B1938869
theorem B571699 : Blo 570811 571699 := bstep (se 1 (by rfl) ⟨428774, by rfl⟩ : syracuseStep 571699 = 857549) B857549
theorem B571715 : Blo 570811 571715 := bstep (se 1 (by rfl) ⟨428786, by rfl⟩ : syracuseStep 571715 = 857573) B857573
theorem B571731 : Blo 570811 571731 := bstep (se 1 (by rfl) ⟨428798, by rfl⟩ : syracuseStep 571731 = 857597) B857597
theorem B571747 : Blo 570811 571747 := bstep (se 1 (by rfl) ⟨428810, by rfl⟩ : syracuseStep 571747 = 857621) B857621
theorem B571763 : Blo 570811 571763 := bstep (se 1 (by rfl) ⟨428822, by rfl⟩ : syracuseStep 571763 = 857645) B857645
theorem B964993 : Blo 570811 964993 := bstep (se 2 (by rfl) ⟨361872, by rfl⟩ : syracuseStep 964993 = 723745) B723745
theorem B571779 : Blo 570811 571779 := bstep (se 1 (by rfl) ⟨428834, by rfl⟩ : syracuseStep 571779 = 857669) B857669
theorem B571795 : Blo 570811 571795 := bstep (se 1 (by rfl) ⟨428846, by rfl⟩ : syracuseStep 571795 = 857693) B857693
theorem B571811 : Blo 570811 571811 := bstep (se 1 (by rfl) ⟨428858, by rfl⟩ : syracuseStep 571811 = 857717) B857717
theorem B965027 : Blo 570811 965027 := bstep (se 1 (by rfl) ⟨723770, by rfl⟩ : syracuseStep 965027 = 1447541) B1447541
theorem B571827 : Blo 570811 571827 := bstep (se 1 (by rfl) ⟨428870, by rfl⟩ : syracuseStep 571827 = 857741) B857741
theorem B571843 : Blo 570811 571843 := bstep (se 1 (by rfl) ⟨428882, by rfl⟩ : syracuseStep 571843 = 857765) B857765
theorem B571859 : Blo 570811 571859 := bstep (se 1 (by rfl) ⟨428894, by rfl⟩ : syracuseStep 571859 = 857789) B857789
theorem B571875 : Blo 570811 571875 := bstep (se 1 (by rfl) ⟨428906, by rfl⟩ : syracuseStep 571875 = 857813) B857813
theorem B571891 : Blo 570811 571891 := bstep (se 1 (by rfl) ⟨428918, by rfl⟩ : syracuseStep 571891 = 857837) B857837
theorem B571907 : Blo 570811 571907 := bstep (se 1 (by rfl) ⟨428930, by rfl⟩ : syracuseStep 571907 = 857861) B857861
theorem B571923 : Blo 570811 571923 := bstep (se 1 (by rfl) ⟨428942, by rfl⟩ : syracuseStep 571923 = 857885) B857885
theorem B571939 : Blo 570811 571939 := bstep (se 1 (by rfl) ⟨428954, by rfl⟩ : syracuseStep 571939 = 857909) B857909
theorem B965155 : Blo 570811 965155 := bstep (se 1 (by rfl) ⟨723866, by rfl⟩ : syracuseStep 965155 = 1447733) B1447733
theorem B1292849 : Blo 570811 1292849 := bstep (se 2 (by rfl) ⟨484818, by rfl⟩ : syracuseStep 1292849 = 969637) B969637
theorem B571955 : Blo 570811 571955 := bstep (se 1 (by rfl) ⟨428966, by rfl⟩ : syracuseStep 571955 = 857933) B857933
theorem B571971 : Blo 570811 571971 := bstep (se 1 (by rfl) ⟨428978, by rfl⟩ : syracuseStep 571971 = 857957) B857957
theorem B1292867 : Blo 570811 1292867 := bstep (se 1 (by rfl) ⟨969650, by rfl⟩ : syracuseStep 1292867 = 1939301) B1939301
theorem B571987 : Blo 570811 571987 := bstep (se 1 (by rfl) ⟨428990, by rfl⟩ : syracuseStep 571987 = 857981) B857981
theorem B572003 : Blo 570811 572003 := bstep (se 1 (by rfl) ⟨429002, by rfl⟩ : syracuseStep 572003 = 858005) B858005
theorem B572019 : Blo 570811 572019 := bstep (se 1 (by rfl) ⟨429014, by rfl⟩ : syracuseStep 572019 = 858029) B858029
theorem B572035 : Blo 570811 572035 := bstep (se 1 (by rfl) ⟨429026, by rfl⟩ : syracuseStep 572035 = 858053) B858053
theorem B3357317 : Blo 570811 3357317 := bstep (se 4 (by rfl) ⟨314748, by rfl⟩ : syracuseStep 3357317 = 629497) B629497
theorem B572051 : Blo 570811 572051 := bstep (se 1 (by rfl) ⟨429038, by rfl⟩ : syracuseStep 572051 = 858077) B858077
theorem B572067 : Blo 570811 572067 := bstep (se 1 (by rfl) ⟨429050, by rfl⟩ : syracuseStep 572067 = 858101) B858101
theorem B965297 : Blo 570811 965297 := bstep (se 2 (by rfl) ⟨361986, by rfl⟩ : syracuseStep 965297 = 723973) B723973
theorem B572083 : Blo 570811 572083 := bstep (se 1 (by rfl) ⟨429062, by rfl⟩ : syracuseStep 572083 = 858125) B858125
theorem B572099 : Blo 570811 572099 := bstep (se 1 (by rfl) ⟨429074, by rfl⟩ : syracuseStep 572099 = 858149) B858149
theorem B572115 : Blo 570811 572115 := bstep (se 1 (by rfl) ⟨429086, by rfl⟩ : syracuseStep 572115 = 858173) B858173
theorem B572131 : Blo 570811 572131 := bstep (se 1 (by rfl) ⟨429098, by rfl⟩ : syracuseStep 572131 = 858197) B858197
theorem B735971 : Blo 570811 735971 := bstep (se 1 (by rfl) ⟨551978, by rfl⟩ : syracuseStep 735971 = 1103957) B1103957
theorem B4340465 : Blo 570811 4340465 := bstep (se 2 (by rfl) ⟨1627674, by rfl⟩ : syracuseStep 4340465 = 3255349) B3255349
theorem B572147 : Blo 570811 572147 := bstep (se 1 (by rfl) ⟨429110, by rfl⟩ : syracuseStep 572147 = 858221) B858221
theorem B572163 : Blo 570811 572163 := bstep (se 1 (by rfl) ⟨429122, by rfl⟩ : syracuseStep 572163 = 858245) B858245
theorem B572179 : Blo 570811 572179 := bstep (se 1 (by rfl) ⟨429134, by rfl⟩ : syracuseStep 572179 = 858269) B858269
theorem B572195 : Blo 570811 572195 := bstep (se 1 (by rfl) ⟨429146, by rfl⟩ : syracuseStep 572195 = 858293) B858293
theorem B965425 : Blo 570811 965425 := bstep (se 2 (by rfl) ⟨362034, by rfl⟩ : syracuseStep 965425 = 724069) B724069
theorem B572211 : Blo 570811 572211 := bstep (se 1 (by rfl) ⟨429158, by rfl⟩ : syracuseStep 572211 = 858317) B858317
theorem B6175541 : Blo 570811 6175541 := bstep (se 5 (by rfl) ⟨289478, by rfl⟩ : syracuseStep 6175541 = 578957) B578957
theorem B572227 : Blo 570811 572227 := bstep (se 1 (by rfl) ⟨429170, by rfl⟩ : syracuseStep 572227 = 858341) B858341
theorem B1293137 : Blo 570811 1293137 := bstep (se 2 (by rfl) ⟨484926, by rfl⟩ : syracuseStep 1293137 = 969853) B969853
theorem B965459 : Blo 570811 965459 := bstep (se 1 (by rfl) ⟨724094, by rfl⟩ : syracuseStep 965459 = 1448189) B1448189
theorem B572243 : Blo 570811 572243 := bstep (se 1 (by rfl) ⟨429182, by rfl⟩ : syracuseStep 572243 = 858365) B858365
theorem B572259 : Blo 570811 572259 := bstep (se 1 (by rfl) ⟨429194, by rfl⟩ : syracuseStep 572259 = 858389) B858389
theorem B1293155 : Blo 570811 1293155 := bstep (se 1 (by rfl) ⟨969866, by rfl⟩ : syracuseStep 1293155 = 1939733) B1939733
theorem B572275 : Blo 570811 572275 := bstep (se 1 (by rfl) ⟨429206, by rfl⟩ : syracuseStep 572275 = 858413) B858413
theorem B572291 : Blo 570811 572291 := bstep (se 1 (by rfl) ⟨429218, by rfl⟩ : syracuseStep 572291 = 858437) B858437
theorem B572307 : Blo 570811 572307 := bstep (se 1 (by rfl) ⟨429230, by rfl⟩ : syracuseStep 572307 = 858461) B858461
theorem B572323 : Blo 570811 572323 := bstep (se 1 (by rfl) ⟨429242, by rfl⟩ : syracuseStep 572323 = 858485) B858485
theorem B572339 : Blo 570811 572339 := bstep (se 1 (by rfl) ⟨429254, by rfl⟩ : syracuseStep 572339 = 858509) B858509
theorem B572355 : Blo 570811 572355 := bstep (se 1 (by rfl) ⟨429266, by rfl⟩ : syracuseStep 572355 = 858533) B858533
theorem B965587 : Blo 570811 965587 := bstep (se 1 (by rfl) ⟨724190, by rfl⟩ : syracuseStep 965587 = 1448381) B1448381
theorem B572371 : Blo 570811 572371 := bstep (se 1 (by rfl) ⟨429278, by rfl⟩ : syracuseStep 572371 = 858557) B858557
theorem B572387 : Blo 570811 572387 := bstep (se 1 (by rfl) ⟨429290, by rfl⟩ : syracuseStep 572387 = 858581) B858581
theorem B572403 : Blo 570811 572403 := bstep (se 1 (by rfl) ⟨429302, by rfl⟩ : syracuseStep 572403 = 858605) B858605
theorem B572419 : Blo 570811 572419 := bstep (se 1 (by rfl) ⟨429314, by rfl⟩ : syracuseStep 572419 = 858629) B858629
theorem B572435 : Blo 570811 572435 := bstep (se 1 (by rfl) ⟨429326, by rfl⟩ : syracuseStep 572435 = 858653) B858653
theorem B572451 : Blo 570811 572451 := bstep (se 1 (by rfl) ⟨429338, by rfl⟩ : syracuseStep 572451 = 858677) B858677
theorem B572467 : Blo 570811 572467 := bstep (se 1 (by rfl) ⟨429350, by rfl⟩ : syracuseStep 572467 = 858701) B858701
theorem B572483 : Blo 570811 572483 := bstep (se 1 (by rfl) ⟨429362, by rfl⟩ : syracuseStep 572483 = 858725) B858725
theorem B572499 : Blo 570811 572499 := bstep (se 1 (by rfl) ⟨429374, by rfl⟩ : syracuseStep 572499 = 858749) B858749
theorem B965729 : Blo 570811 965729 := bstep (se 2 (by rfl) ⟨362148, by rfl⟩ : syracuseStep 965729 = 724297) B724297
theorem B572515 : Blo 570811 572515 := bstep (se 1 (by rfl) ⟨429386, by rfl⟩ : syracuseStep 572515 = 858773) B858773
theorem B2178161 : Blo 570811 2178161 := bstep (se 2 (by rfl) ⟨816810, by rfl⟩ : syracuseStep 2178161 = 1633621) B1633621
theorem B572531 : Blo 570811 572531 := bstep (se 1 (by rfl) ⟨429398, by rfl⟩ : syracuseStep 572531 = 858797) B858797
theorem B572547 : Blo 570811 572547 := bstep (se 1 (by rfl) ⟨429410, by rfl⟩ : syracuseStep 572547 = 858821) B858821
theorem B572563 : Blo 570811 572563 := bstep (se 1 (by rfl) ⟨429422, by rfl⟩ : syracuseStep 572563 = 858845) B858845
theorem B572579 : Blo 570811 572579 := bstep (se 1 (by rfl) ⟨429434, by rfl⟩ : syracuseStep 572579 = 858869) B858869
theorem B572595 : Blo 570811 572595 := bstep (se 1 (by rfl) ⟨429446, by rfl⟩ : syracuseStep 572595 = 858893) B858893
theorem B572611 : Blo 570811 572611 := bstep (se 1 (by rfl) ⟨429458, by rfl⟩ : syracuseStep 572611 = 858917) B858917
theorem B572627 : Blo 570811 572627 := bstep (se 1 (by rfl) ⟨429470, by rfl⟩ : syracuseStep 572627 = 858941) B858941
theorem B965857 : Blo 570811 965857 := bstep (se 2 (by rfl) ⟨362196, by rfl⟩ : syracuseStep 965857 = 724393) B724393
theorem B572643 : Blo 570811 572643 := bstep (se 1 (by rfl) ⟨429482, by rfl⟩ : syracuseStep 572643 = 858965) B858965
theorem B572659 : Blo 570811 572659 := bstep (se 1 (by rfl) ⟨429494, by rfl⟩ : syracuseStep 572659 = 858989) B858989
theorem B965891 : Blo 570811 965891 := bstep (se 1 (by rfl) ⟨724418, by rfl⟩ : syracuseStep 965891 = 1448837) B1448837
theorem B572675 : Blo 570811 572675 := bstep (se 1 (by rfl) ⟨429506, by rfl⟩ : syracuseStep 572675 = 859013) B859013
theorem B572691 : Blo 570811 572691 := bstep (se 1 (by rfl) ⟨429518, by rfl⟩ : syracuseStep 572691 = 859037) B859037
theorem B572707 : Blo 570811 572707 := bstep (se 1 (by rfl) ⟨429530, by rfl⟩ : syracuseStep 572707 = 859061) B859061
theorem B572723 : Blo 570811 572723 := bstep (se 1 (by rfl) ⟨429542, by rfl⟩ : syracuseStep 572723 = 859085) B859085
theorem B572739 : Blo 570811 572739 := bstep (se 1 (by rfl) ⟨429554, by rfl⟩ : syracuseStep 572739 = 859109) B859109
theorem B572755 : Blo 570811 572755 := bstep (se 1 (by rfl) ⟨429566, by rfl⟩ : syracuseStep 572755 = 859133) B859133
theorem B572771 : Blo 570811 572771 := bstep (se 1 (by rfl) ⟨429578, by rfl⟩ : syracuseStep 572771 = 859157) B859157
theorem B3095921 : Blo 570811 3095921 := bstep (se 2 (by rfl) ⟨1160970, by rfl⟩ : syracuseStep 3095921 = 2321941) B2321941
theorem B2899313 : Blo 570811 2899313 := bstep (se 2 (by rfl) ⟨1087242, by rfl⟩ : syracuseStep 2899313 = 2174485) B2174485
theorem B572787 : Blo 570811 572787 := bstep (se 1 (by rfl) ⟨429590, by rfl⟩ : syracuseStep 572787 = 859181) B859181
theorem B966019 : Blo 570811 966019 := bstep (se 1 (by rfl) ⟨724514, by rfl⟩ : syracuseStep 966019 = 1449029) B1449029
theorem B572803 : Blo 570811 572803 := bstep (se 1 (by rfl) ⟨429602, by rfl⟩ : syracuseStep 572803 = 859205) B859205
theorem B572819 : Blo 570811 572819 := bstep (se 1 (by rfl) ⟨429614, by rfl⟩ : syracuseStep 572819 = 859229) B859229
theorem B572835 : Blo 570811 572835 := bstep (se 1 (by rfl) ⟨429626, by rfl⟩ : syracuseStep 572835 = 859253) B859253
theorem B572851 : Blo 570811 572851 := bstep (se 1 (by rfl) ⟨429638, by rfl⟩ : syracuseStep 572851 = 859277) B859277
theorem B572867 : Blo 570811 572867 := bstep (se 1 (by rfl) ⟨429650, by rfl⟩ : syracuseStep 572867 = 859301) B859301
theorem B572883 : Blo 570811 572883 := bstep (se 1 (by rfl) ⟨429662, by rfl⟩ : syracuseStep 572883 = 859325) B859325
theorem B572899 : Blo 570811 572899 := bstep (se 1 (by rfl) ⟨429674, by rfl⟩ : syracuseStep 572899 = 859349) B859349
theorem B572915 : Blo 570811 572915 := bstep (se 1 (by rfl) ⟨429686, by rfl⟩ : syracuseStep 572915 = 859373) B859373
theorem B572931 : Blo 570811 572931 := bstep (se 1 (by rfl) ⟨429698, by rfl⟩ : syracuseStep 572931 = 859397) B859397
theorem B966161 : Blo 570811 966161 := bstep (se 2 (by rfl) ⟨362310, by rfl⟩ : syracuseStep 966161 = 724621) B724621
theorem B572947 : Blo 570811 572947 := bstep (se 1 (by rfl) ⟨429710, by rfl⟩ : syracuseStep 572947 = 859421) B859421
theorem B572963 : Blo 570811 572963 := bstep (se 1 (by rfl) ⟨429722, by rfl⟩ : syracuseStep 572963 = 859445) B859445
theorem B572979 : Blo 570811 572979 := bstep (se 1 (by rfl) ⟨429734, by rfl⟩ : syracuseStep 572979 = 859469) B859469
theorem B572995 : Blo 570811 572995 := bstep (se 1 (by rfl) ⟨429746, by rfl⟩ : syracuseStep 572995 = 859493) B859493
theorem B573011 : Blo 570811 573011 := bstep (se 1 (by rfl) ⟨429758, by rfl⟩ : syracuseStep 573011 = 859517) B859517
theorem B573027 : Blo 570811 573027 := bstep (se 1 (by rfl) ⟨429770, by rfl⟩ : syracuseStep 573027 = 859541) B859541
theorem B573043 : Blo 570811 573043 := bstep (se 1 (by rfl) ⟨429782, by rfl⟩ : syracuseStep 573043 = 859565) B859565
theorem B573059 : Blo 570811 573059 := bstep (se 1 (by rfl) ⟨429794, by rfl⟩ : syracuseStep 573059 = 859589) B859589
theorem B966289 : Blo 570811 966289 := bstep (se 2 (by rfl) ⟨362358, by rfl⟩ : syracuseStep 966289 = 724717) B724717
theorem B573075 : Blo 570811 573075 := bstep (se 1 (by rfl) ⟨429806, by rfl⟩ : syracuseStep 573075 = 859613) B859613
theorem B573091 : Blo 570811 573091 := bstep (se 1 (by rfl) ⟨429818, by rfl⟩ : syracuseStep 573091 = 859637) B859637
theorem B966323 : Blo 570811 966323 := bstep (se 1 (by rfl) ⟨724742, by rfl⟩ : syracuseStep 966323 = 1449485) B1449485
theorem B573107 : Blo 570811 573107 := bstep (se 1 (by rfl) ⟨429830, by rfl⟩ : syracuseStep 573107 = 859661) B859661
theorem B573123 : Blo 570811 573123 := bstep (se 1 (by rfl) ⟨429842, by rfl⟩ : syracuseStep 573123 = 859685) B859685
theorem B3096269 : Blo 570811 3096269 := bstep (se 3 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 3096269 = 1161101) B1161101
theorem B2211533 : Blo 570811 2211533 := bstep (se 3 (by rfl) ⟨414662, by rfl⟩ : syracuseStep 2211533 = 829325) B829325
theorem B573139 : Blo 570811 573139 := bstep (se 1 (by rfl) ⟨429854, by rfl⟩ : syracuseStep 573139 = 859709) B859709
theorem B573155 : Blo 570811 573155 := bstep (se 1 (by rfl) ⟨429866, by rfl⟩ : syracuseStep 573155 = 859733) B859733
theorem B573171 : Blo 570811 573171 := bstep (se 1 (by rfl) ⟨429878, by rfl⟩ : syracuseStep 573171 = 859757) B859757
theorem B573187 : Blo 570811 573187 := bstep (se 1 (by rfl) ⟨429890, by rfl⟩ : syracuseStep 573187 = 859781) B859781
theorem B573203 : Blo 570811 573203 := bstep (se 1 (by rfl) ⟨429902, by rfl⟩ : syracuseStep 573203 = 859805) B859805
theorem B573219 : Blo 570811 573219 := bstep (se 1 (by rfl) ⟨429914, by rfl⟩ : syracuseStep 573219 = 859829) B859829
theorem B966451 : Blo 570811 966451 := bstep (se 1 (by rfl) ⟨724838, by rfl⟩ : syracuseStep 966451 = 1449677) B1449677
theorem B573235 : Blo 570811 573235 := bstep (se 1 (by rfl) ⟨429926, by rfl⟩ : syracuseStep 573235 = 859853) B859853
theorem B573251 : Blo 570811 573251 := bstep (se 1 (by rfl) ⟨429938, by rfl⟩ : syracuseStep 573251 = 859877) B859877
theorem B573267 : Blo 570811 573267 := bstep (se 1 (by rfl) ⟨429950, by rfl⟩ : syracuseStep 573267 = 859901) B859901
theorem B573283 : Blo 570811 573283 := bstep (se 1 (by rfl) ⟨429962, by rfl⟩ : syracuseStep 573283 = 859925) B859925
theorem B573299 : Blo 570811 573299 := bstep (se 1 (by rfl) ⟨429974, by rfl⟩ : syracuseStep 573299 = 859949) B859949
theorem B573315 : Blo 570811 573315 := bstep (se 1 (by rfl) ⟨429986, by rfl⟩ : syracuseStep 573315 = 859973) B859973
theorem B573331 : Blo 570811 573331 := bstep (se 1 (by rfl) ⟨429998, by rfl⟩ : syracuseStep 573331 = 859997) B859997
theorem B573347 : Blo 570811 573347 := bstep (se 1 (by rfl) ⟨430010, by rfl⟩ : syracuseStep 573347 = 860021) B860021
theorem B2441137 : Blo 570811 2441137 := bstep (se 2 (by rfl) ⟨915426, by rfl⟩ : syracuseStep 2441137 = 1830853) B1830853
theorem B573363 : Blo 570811 573363 := bstep (se 1 (by rfl) ⟨430022, by rfl⟩ : syracuseStep 573363 = 860045) B860045
theorem B966593 : Blo 570811 966593 := bstep (se 2 (by rfl) ⟨362472, by rfl⟩ : syracuseStep 966593 = 724945) B724945
theorem B573379 : Blo 570811 573379 := bstep (se 1 (by rfl) ⟨430034, by rfl⟩ : syracuseStep 573379 = 860069) B860069
theorem B573395 : Blo 570811 573395 := bstep (se 1 (by rfl) ⟨430046, by rfl⟩ : syracuseStep 573395 = 860093) B860093
theorem B573411 : Blo 570811 573411 := bstep (se 1 (by rfl) ⟨430058, by rfl⟩ : syracuseStep 573411 = 860117) B860117
theorem B573427 : Blo 570811 573427 := bstep (se 1 (by rfl) ⟨430070, by rfl⟩ : syracuseStep 573427 = 860141) B860141
theorem B573443 : Blo 570811 573443 := bstep (se 1 (by rfl) ⟨430082, by rfl⟩ : syracuseStep 573443 = 860165) B860165
theorem B573459 : Blo 570811 573459 := bstep (se 1 (by rfl) ⟨430094, by rfl⟩ : syracuseStep 573459 = 860189) B860189
theorem B573475 : Blo 570811 573475 := bstep (se 1 (by rfl) ⟨430106, by rfl⟩ : syracuseStep 573475 = 860213) B860213
theorem B573491 : Blo 570811 573491 := bstep (se 1 (by rfl) ⟨430118, by rfl⟩ : syracuseStep 573491 = 860237) B860237
theorem B966721 : Blo 570811 966721 := bstep (se 2 (by rfl) ⟨362520, by rfl⟩ : syracuseStep 966721 = 725041) B725041
theorem B573507 : Blo 570811 573507 := bstep (se 1 (by rfl) ⟨430130, by rfl⟩ : syracuseStep 573507 = 860261) B860261
theorem B573523 : Blo 570811 573523 := bstep (se 1 (by rfl) ⟨430142, by rfl⟩ : syracuseStep 573523 = 860285) B860285
theorem B966755 : Blo 570811 966755 := bstep (se 1 (by rfl) ⟨725066, by rfl⟩ : syracuseStep 966755 = 1450133) B1450133
theorem B573539 : Blo 570811 573539 := bstep (se 1 (by rfl) ⟨430154, by rfl⟩ : syracuseStep 573539 = 860309) B860309
theorem B573555 : Blo 570811 573555 := bstep (se 1 (by rfl) ⟨430166, by rfl⟩ : syracuseStep 573555 = 860333) B860333
theorem B573571 : Blo 570811 573571 := bstep (se 1 (by rfl) ⟨430178, by rfl⟩ : syracuseStep 573571 = 860357) B860357
theorem B573587 : Blo 570811 573587 := bstep (se 1 (by rfl) ⟨430190, by rfl⟩ : syracuseStep 573587 = 860381) B860381
theorem B573603 : Blo 570811 573603 := bstep (se 1 (by rfl) ⟨430202, by rfl⟩ : syracuseStep 573603 = 860405) B860405
theorem B573619 : Blo 570811 573619 := bstep (se 1 (by rfl) ⟨430214, by rfl⟩ : syracuseStep 573619 = 860429) B860429
theorem B573635 : Blo 570811 573635 := bstep (se 1 (by rfl) ⟨430226, by rfl⟩ : syracuseStep 573635 = 860453) B860453
theorem B573651 : Blo 570811 573651 := bstep (se 1 (by rfl) ⟨430238, by rfl⟩ : syracuseStep 573651 = 860477) B860477
theorem B966883 : Blo 570811 966883 := bstep (se 1 (by rfl) ⟨725162, by rfl⟩ : syracuseStep 966883 = 1450325) B1450325
theorem B573667 : Blo 570811 573667 := bstep (se 1 (by rfl) ⟨430250, by rfl⟩ : syracuseStep 573667 = 860501) B860501
theorem B573683 : Blo 570811 573683 := bstep (se 1 (by rfl) ⟨430262, by rfl⟩ : syracuseStep 573683 = 860525) B860525
theorem B573699 : Blo 570811 573699 := bstep (se 1 (by rfl) ⟨430274, by rfl⟩ : syracuseStep 573699 = 860549) B860549
theorem B573715 : Blo 570811 573715 := bstep (se 1 (by rfl) ⟨430286, by rfl⟩ : syracuseStep 573715 = 860573) B860573
theorem B573731 : Blo 570811 573731 := bstep (se 1 (by rfl) ⟨430298, by rfl⟩ : syracuseStep 573731 = 860597) B860597
theorem B573747 : Blo 570811 573747 := bstep (se 1 (by rfl) ⟨430310, by rfl⟩ : syracuseStep 573747 = 860621) B860621
theorem B573763 : Blo 570811 573763 := bstep (se 1 (by rfl) ⟨430322, by rfl⟩ : syracuseStep 573763 = 860645) B860645
theorem B573779 : Blo 570811 573779 := bstep (se 1 (by rfl) ⟨430334, by rfl⟩ : syracuseStep 573779 = 860669) B860669
theorem B573795 : Blo 570811 573795 := bstep (se 1 (by rfl) ⟨430346, by rfl⟩ : syracuseStep 573795 = 860693) B860693
theorem B967025 : Blo 570811 967025 := bstep (se 2 (by rfl) ⟨362634, by rfl⟩ : syracuseStep 967025 = 725269) B725269
theorem B573811 : Blo 570811 573811 := bstep (se 1 (by rfl) ⟨430358, by rfl⟩ : syracuseStep 573811 = 860717) B860717
theorem B573827 : Blo 570811 573827 := bstep (se 1 (by rfl) ⟨430370, by rfl⟩ : syracuseStep 573827 = 860741) B860741
theorem B573843 : Blo 570811 573843 := bstep (se 1 (by rfl) ⟨430382, by rfl⟩ : syracuseStep 573843 = 860765) B860765
theorem B573859 : Blo 570811 573859 := bstep (se 1 (by rfl) ⟨430394, by rfl⟩ : syracuseStep 573859 = 860789) B860789
theorem B573875 : Blo 570811 573875 := bstep (se 1 (by rfl) ⟨430406, by rfl⟩ : syracuseStep 573875 = 860813) B860813
theorem B573891 : Blo 570811 573891 := bstep (se 1 (by rfl) ⟨430418, by rfl⟩ : syracuseStep 573891 = 860837) B860837
theorem B573907 : Blo 570811 573907 := bstep (se 1 (by rfl) ⟨430430, by rfl⟩ : syracuseStep 573907 = 860861) B860861
theorem B573923 : Blo 570811 573923 := bstep (se 1 (by rfl) ⟨430442, by rfl⟩ : syracuseStep 573923 = 860885) B860885
theorem B967153 : Blo 570811 967153 := bstep (se 2 (by rfl) ⟨362682, by rfl⟩ : syracuseStep 967153 = 725365) B725365
theorem B573939 : Blo 570811 573939 := bstep (se 1 (by rfl) ⟨430454, by rfl⟩ : syracuseStep 573939 = 860909) B860909
theorem B573955 : Blo 570811 573955 := bstep (se 1 (by rfl) ⟨430466, by rfl⟩ : syracuseStep 573955 = 860933) B860933
theorem B967187 : Blo 570811 967187 := bstep (se 1 (by rfl) ⟨725390, by rfl⟩ : syracuseStep 967187 = 1450781) B1450781
theorem B573971 : Blo 570811 573971 := bstep (se 1 (by rfl) ⟨430478, by rfl⟩ : syracuseStep 573971 = 860957) B860957
theorem B573987 : Blo 570811 573987 := bstep (se 1 (by rfl) ⟨430490, by rfl⟩ : syracuseStep 573987 = 860981) B860981
theorem B2179619 : Blo 570811 2179619 := bstep (se 1 (by rfl) ⟨1634714, by rfl⟩ : syracuseStep 2179619 = 3269429) B3269429
theorem B574003 : Blo 570811 574003 := bstep (se 1 (by rfl) ⟨430502, by rfl⟩ : syracuseStep 574003 = 861005) B861005
theorem B574019 : Blo 570811 574019 := bstep (se 1 (by rfl) ⟨430514, by rfl⟩ : syracuseStep 574019 = 861029) B861029
theorem B574035 : Blo 570811 574035 := bstep (se 1 (by rfl) ⟨430526, by rfl⟩ : syracuseStep 574035 = 861053) B861053
theorem B574051 : Blo 570811 574051 := bstep (se 1 (by rfl) ⟨430538, by rfl⟩ : syracuseStep 574051 = 861077) B861077
theorem B574067 : Blo 570811 574067 := bstep (se 1 (by rfl) ⟨430550, by rfl⟩ : syracuseStep 574067 = 861101) B861101
theorem B574083 : Blo 570811 574083 := bstep (se 1 (by rfl) ⟨430562, by rfl⟩ : syracuseStep 574083 = 861125) B861125
theorem B967315 : Blo 570811 967315 := bstep (se 1 (by rfl) ⟨725486, by rfl⟩ : syracuseStep 967315 = 1450973) B1450973
theorem B574099 : Blo 570811 574099 := bstep (se 1 (by rfl) ⟨430574, by rfl⟩ : syracuseStep 574099 = 861149) B861149
theorem B574115 : Blo 570811 574115 := bstep (se 1 (by rfl) ⟨430586, by rfl⟩ : syracuseStep 574115 = 861173) B861173
theorem B574131 : Blo 570811 574131 := bstep (se 1 (by rfl) ⟨430598, by rfl⟩ : syracuseStep 574131 = 861197) B861197
theorem B574147 : Blo 570811 574147 := bstep (se 1 (by rfl) ⟨430610, by rfl⟩ : syracuseStep 574147 = 861221) B861221
theorem B574163 : Blo 570811 574163 := bstep (se 1 (by rfl) ⟨430622, by rfl⟩ : syracuseStep 574163 = 861245) B861245
theorem B574179 : Blo 570811 574179 := bstep (se 1 (by rfl) ⟨430634, by rfl⟩ : syracuseStep 574179 = 861269) B861269
theorem B574195 : Blo 570811 574195 := bstep (se 1 (by rfl) ⟨430646, by rfl⟩ : syracuseStep 574195 = 861293) B861293
theorem B574211 : Blo 570811 574211 := bstep (se 1 (by rfl) ⟨430658, by rfl⟩ : syracuseStep 574211 = 861317) B861317
theorem B574227 : Blo 570811 574227 := bstep (se 1 (by rfl) ⟨430670, by rfl⟩ : syracuseStep 574227 = 861341) B861341
theorem B967457 : Blo 570811 967457 := bstep (se 2 (by rfl) ⟨362796, by rfl⟩ : syracuseStep 967457 = 725593) B725593
theorem B2900771 : Blo 570811 2900771 := bstep (se 1 (by rfl) ⟨2175578, by rfl⟩ : syracuseStep 2900771 = 4351157) B4351157
theorem B574243 : Blo 570811 574243 := bstep (se 1 (by rfl) ⟨430682, by rfl⟩ : syracuseStep 574243 = 861365) B861365
theorem B1327907 : Blo 570811 1327907 := bstep (se 1 (by rfl) ⟨995930, by rfl⟩ : syracuseStep 1327907 = 1991861) B1991861
theorem B574259 : Blo 570811 574259 := bstep (se 1 (by rfl) ⟨430694, by rfl⟩ : syracuseStep 574259 = 861389) B861389
theorem B574275 : Blo 570811 574275 := bstep (se 1 (by rfl) ⟨430706, by rfl⟩ : syracuseStep 574275 = 861413) B861413
theorem B574291 : Blo 570811 574291 := bstep (se 1 (by rfl) ⟨430718, by rfl⟩ : syracuseStep 574291 = 861437) B861437
theorem B574307 : Blo 570811 574307 := bstep (se 1 (by rfl) ⟨430730, by rfl⟩ : syracuseStep 574307 = 861461) B861461
theorem B574323 : Blo 570811 574323 := bstep (se 1 (by rfl) ⟨430742, by rfl⟩ : syracuseStep 574323 = 861485) B861485
theorem B574339 : Blo 570811 574339 := bstep (se 1 (by rfl) ⟨430754, by rfl⟩ : syracuseStep 574339 = 861509) B861509
theorem B574355 : Blo 570811 574355 := bstep (se 1 (by rfl) ⟨430766, by rfl⟩ : syracuseStep 574355 = 861533) B861533
theorem B967585 : Blo 570811 967585 := bstep (se 2 (by rfl) ⟨362844, by rfl⟩ : syracuseStep 967585 = 725689) B725689
theorem B574371 : Blo 570811 574371 := bstep (se 1 (by rfl) ⟨430778, by rfl⟩ : syracuseStep 574371 = 861557) B861557
theorem B574387 : Blo 570811 574387 := bstep (se 1 (by rfl) ⟨430790, by rfl⟩ : syracuseStep 574387 = 861581) B861581
theorem B967619 : Blo 570811 967619 := bstep (se 1 (by rfl) ⟨725714, by rfl⟩ : syracuseStep 967619 = 1451429) B1451429
theorem B574403 : Blo 570811 574403 := bstep (se 1 (by rfl) ⟨430802, by rfl⟩ : syracuseStep 574403 = 861605) B861605
theorem B574419 : Blo 570811 574419 := bstep (se 1 (by rfl) ⟨430814, by rfl⟩ : syracuseStep 574419 = 861629) B861629
theorem B574435 : Blo 570811 574435 := bstep (se 1 (by rfl) ⟨430826, by rfl⟩ : syracuseStep 574435 = 861653) B861653
theorem B574451 : Blo 570811 574451 := bstep (se 1 (by rfl) ⟨430838, by rfl⟩ : syracuseStep 574451 = 861677) B861677
theorem B574467 : Blo 570811 574467 := bstep (se 1 (by rfl) ⟨430850, by rfl⟩ : syracuseStep 574467 = 861701) B861701
theorem B574483 : Blo 570811 574483 := bstep (se 1 (by rfl) ⟨430862, by rfl⟩ : syracuseStep 574483 = 861725) B861725
theorem B574499 : Blo 570811 574499 := bstep (se 1 (by rfl) ⟨430874, by rfl⟩ : syracuseStep 574499 = 861749) B861749
theorem B574515 : Blo 570811 574515 := bstep (se 1 (by rfl) ⟨430886, by rfl⟩ : syracuseStep 574515 = 861773) B861773
theorem B967747 : Blo 570811 967747 := bstep (se 1 (by rfl) ⟨725810, by rfl⟩ : syracuseStep 967747 = 1451621) B1451621
theorem B574531 : Blo 570811 574531 := bstep (se 1 (by rfl) ⟨430898, by rfl⟩ : syracuseStep 574531 = 861797) B861797
theorem B574547 : Blo 570811 574547 := bstep (se 1 (by rfl) ⟨430910, by rfl⟩ : syracuseStep 574547 = 861821) B861821
theorem B574563 : Blo 570811 574563 := bstep (se 1 (by rfl) ⟨430922, by rfl⟩ : syracuseStep 574563 = 861845) B861845
theorem B574579 : Blo 570811 574579 := bstep (se 1 (by rfl) ⟨430934, by rfl⟩ : syracuseStep 574579 = 861869) B861869
theorem B574595 : Blo 570811 574595 := bstep (se 1 (by rfl) ⟨430946, by rfl⟩ : syracuseStep 574595 = 861893) B861893
theorem B574611 : Blo 570811 574611 := bstep (se 1 (by rfl) ⟨430958, by rfl⟩ : syracuseStep 574611 = 861917) B861917
theorem B869537 : Blo 570811 869537 := bstep (se 2 (by rfl) ⟨326076, by rfl⟩ : syracuseStep 869537 = 652153) B652153
theorem B574627 : Blo 570811 574627 := bstep (se 1 (by rfl) ⟨430970, by rfl⟩ : syracuseStep 574627 = 861941) B861941
theorem B574643 : Blo 570811 574643 := bstep (se 1 (by rfl) ⟨430982, by rfl⟩ : syracuseStep 574643 = 861965) B861965
theorem B574659 : Blo 570811 574659 := bstep (se 1 (by rfl) ⟨430994, by rfl⟩ : syracuseStep 574659 = 861989) B861989
theorem B967889 : Blo 570811 967889 := bstep (se 2 (by rfl) ⟨362958, by rfl⟩ : syracuseStep 967889 = 725917) B725917
theorem B574675 : Blo 570811 574675 := bstep (se 1 (by rfl) ⟨431006, by rfl⟩ : syracuseStep 574675 = 862013) B862013
theorem B574691 : Blo 570811 574691 := bstep (se 1 (by rfl) ⟨431018, by rfl⟩ : syracuseStep 574691 = 862037) B862037
theorem B574707 : Blo 570811 574707 := bstep (se 1 (by rfl) ⟨431030, by rfl⟩ : syracuseStep 574707 = 862061) B862061
theorem B574723 : Blo 570811 574723 := bstep (se 1 (by rfl) ⟨431042, by rfl⟩ : syracuseStep 574723 = 862085) B862085
theorem B1033489 : Blo 570811 1033489 := bstep (se 2 (by rfl) ⟨387558, by rfl⟩ : syracuseStep 1033489 = 775117) B775117
theorem B574739 : Blo 570811 574739 := bstep (se 1 (by rfl) ⟨431054, by rfl⟩ : syracuseStep 574739 = 862109) B862109
theorem B574755 : Blo 570811 574755 := bstep (se 1 (by rfl) ⟨431066, by rfl⟩ : syracuseStep 574755 = 862133) B862133
theorem B574771 : Blo 570811 574771 := bstep (se 1 (by rfl) ⟨431078, by rfl⟩ : syracuseStep 574771 = 862157) B862157
theorem B574787 : Blo 570811 574787 := bstep (se 1 (by rfl) ⟨431090, by rfl⟩ : syracuseStep 574787 = 862181) B862181
theorem B968017 : Blo 570811 968017 := bstep (se 2 (by rfl) ⟨363006, by rfl⟩ : syracuseStep 968017 = 726013) B726013
theorem B574803 : Blo 570811 574803 := bstep (se 1 (by rfl) ⟨431102, by rfl⟩ : syracuseStep 574803 = 862205) B862205
theorem B968051 : Blo 570811 968051 := bstep (se 1 (by rfl) ⟨726038, by rfl⟩ : syracuseStep 968051 = 1452077) B1452077
theorem B968179 : Blo 570811 968179 := bstep (se 1 (by rfl) ⟨726134, by rfl⟩ : syracuseStep 968179 = 1452269) B1452269
theorem B2180621 : Blo 570811 2180621 := bstep (se 3 (by rfl) ⟨408866, by rfl⟩ : syracuseStep 2180621 = 817733) B817733
theorem B2901581 : Blo 570811 2901581 := bstep (se 3 (by rfl) ⟨544046, by rfl⟩ : syracuseStep 2901581 = 1088093) B1088093
theorem B968321 : Blo 570811 968321 := bstep (se 2 (by rfl) ⟨363120, by rfl⟩ : syracuseStep 968321 = 726241) B726241
theorem B968449 : Blo 570811 968449 := bstep (se 2 (by rfl) ⟨363168, by rfl⟩ : syracuseStep 968449 = 726337) B726337
theorem B3131149 : Blo 570811 3131149 := bstep (se 3 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 3131149 = 1174181) B1174181
theorem B968483 : Blo 570811 968483 := bstep (se 1 (by rfl) ⟨726362, by rfl⟩ : syracuseStep 968483 = 1452725) B1452725
theorem B2934605 : Blo 570811 2934605 := bstep (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) B1100477
theorem B2443085 : Blo 570811 2443085 := bstep (se 3 (by rfl) ⟨458078, by rfl⟩ : syracuseStep 2443085 = 916157) B916157
theorem B968611 : Blo 570811 968611 := bstep (se 1 (by rfl) ⟨726458, by rfl⟩ : syracuseStep 968611 = 1452917) B1452917
theorem B6211525 : Blo 570811 6211525 := bstep (se 4 (by rfl) ⟨582330, by rfl⟩ : syracuseStep 6211525 = 1164661) B1164661
theorem B968753 : Blo 570811 968753 := bstep (se 2 (by rfl) ⟨363282, by rfl⟩ : syracuseStep 968753 = 726565) B726565
theorem B3295331 : Blo 570811 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B968881 : Blo 570811 968881 := bstep (se 2 (by rfl) ⟨363330, by rfl⟩ : syracuseStep 968881 = 726661) B726661
theorem B968915 : Blo 570811 968915 := bstep (se 1 (by rfl) ⟨726686, by rfl⟩ : syracuseStep 968915 = 1453373) B1453373
theorem B969043 : Blo 570811 969043 := bstep (se 1 (by rfl) ⟨726782, by rfl⟩ : syracuseStep 969043 = 1453565) B1453565
theorem B969185 : Blo 570811 969185 := bstep (se 2 (by rfl) ⟨363444, by rfl⟩ : syracuseStep 969185 = 726889) B726889
theorem B969313 : Blo 570811 969313 := bstep (se 2 (by rfl) ⟨363492, by rfl⟩ : syracuseStep 969313 = 726985) B726985
theorem B969347 : Blo 570811 969347 := bstep (se 1 (by rfl) ⟨727010, by rfl⟩ : syracuseStep 969347 = 1454021) B1454021
theorem B969475 : Blo 570811 969475 := bstep (se 1 (by rfl) ⟨727106, by rfl⟩ : syracuseStep 969475 = 1454213) B1454213
theorem B969617 : Blo 570811 969617 := bstep (se 2 (by rfl) ⟨363606, by rfl⟩ : syracuseStep 969617 = 727213) B727213
theorem B1100785 : Blo 570811 1100785 := bstep (se 2 (by rfl) ⟨412794, by rfl⟩ : syracuseStep 1100785 = 825589) B825589
theorem B3984389 : Blo 570811 3984389 := bstep (se 4 (by rfl) ⟨373536, by rfl⟩ : syracuseStep 3984389 = 747073) B747073
theorem B969745 : Blo 570811 969745 := bstep (se 2 (by rfl) ⟨363654, by rfl⟩ : syracuseStep 969745 = 727309) B727309
theorem B969779 : Blo 570811 969779 := bstep (se 1 (by rfl) ⟨727334, by rfl⟩ : syracuseStep 969779 = 1454669) B1454669
theorem B4901957 : Blo 570811 4901957 := bstep (se 4 (by rfl) ⟨459558, by rfl⟩ : syracuseStep 4901957 = 919117) B919117
theorem B642163 : Blo 570811 642163 := bstep (se 1 (by rfl) ⟨481622, by rfl⟩ : syracuseStep 642163 = 963245) B963245
theorem B773267 : Blo 570811 773267 := bstep (se 1 (by rfl) ⟨579950, by rfl⟩ : syracuseStep 773267 = 1159901) B1159901
theorem B969907 : Blo 570811 969907 := bstep (se 1 (by rfl) ⟨727430, by rfl⟩ : syracuseStep 969907 = 1454861) B1454861
theorem B642307 : Blo 570811 642307 := bstep (se 1 (by rfl) ⟨481730, by rfl⟩ : syracuseStep 642307 = 963461) B963461
theorem B642451 : Blo 570811 642451 := bstep (se 1 (by rfl) ⟨481838, by rfl⟩ : syracuseStep 642451 = 963677) B963677
theorem B3919373 : Blo 570811 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B1396241 : Blo 570811 1396241 := bstep (se 2 (by rfl) ⟨523590, by rfl⟩ : syracuseStep 1396241 = 1047181) B1047181
theorem B642595 : Blo 570811 642595 := bstep (se 1 (by rfl) ⟨481946, by rfl⟩ : syracuseStep 642595 = 963893) B963893
theorem B642739 : Blo 570811 642739 := bstep (se 1 (by rfl) ⟨482054, by rfl⟩ : syracuseStep 642739 = 964109) B964109
theorem B1527587 : Blo 570811 1527587 := bstep (se 1 (by rfl) ⟨1145690, by rfl⟩ : syracuseStep 1527587 = 2291381) B2291381
theorem B1658659 : Blo 570811 1658659 := bstep (se 1 (by rfl) ⟨1243994, by rfl⟩ : syracuseStep 1658659 = 2487989) B2487989
theorem B2477873 : Blo 570811 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B642883 : Blo 570811 642883 := bstep (se 1 (by rfl) ⟨482162, by rfl⟩ : syracuseStep 642883 = 964325) B964325
theorem B1625933 : Blo 570811 1625933 := bstep (se 3 (by rfl) ⟨304862, by rfl⟩ : syracuseStep 1625933 = 609725) B609725
theorem B774019 : Blo 570811 774019 := bstep (se 1 (by rfl) ⟨580514, by rfl⟩ : syracuseStep 774019 = 1161029) B1161029
theorem B643027 : Blo 570811 643027 := bstep (se 1 (by rfl) ⟨482270, by rfl⟩ : syracuseStep 643027 = 964541) B964541
theorem B1626115 : Blo 570811 1626115 := bstep (se 1 (by rfl) ⟨1219586, by rfl⟩ : syracuseStep 1626115 = 2439173) B2439173
theorem B774193 : Blo 570811 774193 := bstep (se 2 (by rfl) ⟨290322, by rfl⟩ : syracuseStep 774193 = 580645) B580645
theorem B643171 : Blo 570811 643171 := bstep (se 1 (by rfl) ⟨482378, by rfl⟩ : syracuseStep 643171 = 964757) B964757
theorem B643315 : Blo 570811 643315 := bstep (se 1 (by rfl) ⟨482486, by rfl⟩ : syracuseStep 643315 = 964973) B964973
theorem B643459 : Blo 570811 643459 := bstep (se 1 (by rfl) ⟨482594, by rfl⟩ : syracuseStep 643459 = 965189) B965189
theorem B2904497 : Blo 570811 2904497 := bstep (se 2 (by rfl) ⟨1089186, by rfl⟩ : syracuseStep 2904497 = 2178373) B2178373
theorem B17912261 : Blo 570811 17912261 := bstep (se 4 (by rfl) ⟨1679274, by rfl⟩ : syracuseStep 17912261 = 3358549) B3358549
theorem B1626605 : Blo 570811 1626605 := bstep (se 3 (by rfl) ⟨304988, by rfl⟩ : syracuseStep 1626605 = 609977) B609977
theorem B643603 : Blo 570811 643603 := bstep (se 1 (by rfl) ⟨482702, by rfl⟩ : syracuseStep 643603 = 965405) B965405
theorem B2609741 : Blo 570811 2609741 := bstep (se 3 (by rfl) ⟨489326, by rfl⟩ : syracuseStep 2609741 = 978653) B978653
theorem B873107 : Blo 570811 873107 := bstep (se 1 (by rfl) ⟨654830, by rfl⟩ : syracuseStep 873107 = 1309661) B1309661
theorem B643747 : Blo 570811 643747 := bstep (se 1 (by rfl) ⟨482810, by rfl⟩ : syracuseStep 643747 = 965621) B965621
theorem B643891 : Blo 570811 643891 := bstep (se 1 (by rfl) ⟨482918, by rfl⟩ : syracuseStep 643891 = 965837) B965837
theorem B775057 : Blo 570811 775057 := bstep (se 2 (by rfl) ⟨290646, by rfl⟩ : syracuseStep 775057 = 581293) B581293
theorem B644035 : Blo 570811 644035 := bstep (se 1 (by rfl) ⟨483026, by rfl⟩ : syracuseStep 644035 = 966053) B966053
theorem B4641805 : Blo 570811 4641805 := bstep (se 3 (by rfl) ⟨870338, by rfl⟩ : syracuseStep 4641805 = 1740677) B1740677
theorem B644179 : Blo 570811 644179 := bstep (se 1 (by rfl) ⟨483134, by rfl⟩ : syracuseStep 644179 = 966269) B966269
theorem B644323 : Blo 570811 644323 := bstep (se 1 (by rfl) ⟨483242, by rfl⟩ : syracuseStep 644323 = 966485) B966485
theorem B644467 : Blo 570811 644467 := bstep (se 1 (by rfl) ⟨483350, by rfl⟩ : syracuseStep 644467 = 966701) B966701
theorem B644611 : Blo 570811 644611 := bstep (se 1 (by rfl) ⟨483458, by rfl⟩ : syracuseStep 644611 = 966917) B966917
theorem B1627789 : Blo 570811 1627789 := bstep (se 3 (by rfl) ⟨305210, by rfl⟩ : syracuseStep 1627789 = 610421) B610421
theorem B644755 : Blo 570811 644755 := bstep (se 1 (by rfl) ⟨483566, by rfl⟩ : syracuseStep 644755 = 967133) B967133
theorem B612083 : Blo 570811 612083 := bstep (se 1 (by rfl) ⟨459062, by rfl⟩ : syracuseStep 612083 = 918125) B918125
theorem B2447117 : Blo 570811 2447117 := bstep (se 3 (by rfl) ⟨458834, by rfl⟩ : syracuseStep 2447117 = 917669) B917669
theorem B644899 : Blo 570811 644899 := bstep (se 1 (by rfl) ⟨483674, by rfl⟩ : syracuseStep 644899 = 967349) B967349
theorem B2905955 : Blo 570811 2905955 := bstep (se 1 (by rfl) ⟨2179466, by rfl⟩ : syracuseStep 2905955 = 4358933) B4358933
theorem B776035 : Blo 570811 776035 := bstep (se 1 (by rfl) ⟨582026, by rfl⟩ : syracuseStep 776035 = 1164053) B1164053
theorem B645043 : Blo 570811 645043 := bstep (se 1 (by rfl) ⟨483782, by rfl⟩ : syracuseStep 645043 = 967565) B967565
theorem B645187 : Blo 570811 645187 := bstep (se 1 (by rfl) ⟨483890, by rfl⟩ : syracuseStep 645187 = 967781) B967781
theorem B2447459 : Blo 570811 2447459 := bstep (se 1 (by rfl) ⟨1835594, by rfl⟩ : syracuseStep 2447459 = 3671189) B3671189
theorem B1857667 : Blo 570811 1857667 := bstep (se 1 (by rfl) ⟨1393250, by rfl⟩ : syracuseStep 1857667 = 2786501) B2786501
theorem B2087117 : Blo 570811 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B645331 : Blo 570811 645331 := bstep (se 1 (by rfl) ⟨483998, by rfl⟩ : syracuseStep 645331 = 967997) B967997
theorem B645475 : Blo 570811 645475 := bstep (se 1 (by rfl) ⟨484106, by rfl⟩ : syracuseStep 645475 = 968213) B968213
theorem B3267013 : Blo 570811 3267013 := bstep (se 4 (by rfl) ⟨306282, by rfl⟩ : syracuseStep 3267013 = 612565) B612565
theorem B645619 : Blo 570811 645619 := bstep (se 1 (by rfl) ⟨484214, by rfl⟩ : syracuseStep 645619 = 968429) B968429
theorem B2447921 : Blo 570811 2447921 := bstep (se 2 (by rfl) ⟨917970, by rfl⟩ : syracuseStep 2447921 = 1835941) B1835941
theorem B645763 : Blo 570811 645763 := bstep (se 1 (by rfl) ⟨484322, by rfl⟩ : syracuseStep 645763 = 968645) B968645
theorem B2906765 : Blo 570811 2906765 := bstep (se 3 (by rfl) ⟨545018, by rfl⟩ : syracuseStep 2906765 = 1090037) B1090037
theorem B1628849 : Blo 570811 1628849 := bstep (se 2 (by rfl) ⟨610818, by rfl⟩ : syracuseStep 1628849 = 1221637) B1221637
theorem B645907 : Blo 570811 645907 := bstep (se 1 (by rfl) ⟨484430, by rfl⟩ : syracuseStep 645907 = 968861) B968861
theorem B6970211 : Blo 570811 6970211 := bstep (se 1 (by rfl) ⟨5227658, by rfl⟩ : syracuseStep 6970211 = 10455317) B10455317
theorem B646051 : Blo 570811 646051 := bstep (se 1 (by rfl) ⟨484538, by rfl⟩ : syracuseStep 646051 = 969077) B969077
theorem B646195 : Blo 570811 646195 := bstep (se 1 (by rfl) ⟨484646, by rfl⟩ : syracuseStep 646195 = 969293) B969293
theorem B646339 : Blo 570811 646339 := bstep (se 1 (by rfl) ⟨484754, by rfl⟩ : syracuseStep 646339 = 969509) B969509
theorem B1629521 : Blo 570811 1629521 := bstep (se 2 (by rfl) ⟨611070, by rfl⟩ : syracuseStep 1629521 = 1222141) B1222141
theorem B646483 : Blo 570811 646483 := bstep (se 1 (by rfl) ⟨484862, by rfl⟩ : syracuseStep 646483 = 969725) B969725
theorem B646627 : Blo 570811 646627 := bstep (se 1 (by rfl) ⟨484970, by rfl⟩ : syracuseStep 646627 = 969941) B969941
theorem B1957745 : Blo 570811 1957745 := bstep (se 2 (by rfl) ⟨734154, by rfl⟩ : syracuseStep 1957745 = 1468309) B1468309
theorem B1630307 : Blo 570811 1630307 := bstep (se 1 (by rfl) ⟨1222730, by rfl⟩ : syracuseStep 1630307 = 2445461) B2445461
theorem B3268997 : Blo 570811 3268997 := bstep (se 4 (by rfl) ⟨306468, by rfl⟩ : syracuseStep 3268997 = 612937) B612937
theorem B1630637 : Blo 570811 1630637 := bstep (se 3 (by rfl) ⟨305744, by rfl⟩ : syracuseStep 1630637 = 611489) B611489
theorem B1630705 : Blo 570811 1630705 := bstep (se 2 (by rfl) ⟨611514, by rfl⟩ : syracuseStep 1630705 = 1223029) B1223029
theorem B1630979 : Blo 570811 1630979 := bstep (se 1 (by rfl) ⟨1223234, by rfl⟩ : syracuseStep 1630979 = 2446469) B2446469
theorem B7628017 : Blo 570811 7628017 := bstep (se 2 (by rfl) ⟨2860506, by rfl⟩ : syracuseStep 7628017 = 5721013) B5721013
theorem B3663089 : Blo 570811 3663089 := bstep (se 2 (by rfl) ⟨1373658, by rfl⟩ : syracuseStep 3663089 = 2747317) B2747317
theorem B3302819 : Blo 570811 3302819 := bstep (se 1 (by rfl) ⟨2477114, by rfl⟩ : syracuseStep 3302819 = 4954229) B4954229
theorem B2909681 : Blo 570811 2909681 := bstep (se 2 (by rfl) ⟨1091130, by rfl⟩ : syracuseStep 2909681 = 2182261) B2182261
theorem B1631821 : Blo 570811 1631821 := bstep (se 3 (by rfl) ⟨305966, by rfl⟩ : syracuseStep 1631821 = 611933) B611933
theorem B1238723 : Blo 570811 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B1631981 : Blo 570811 1631981 := bstep (se 3 (by rfl) ⟨305996, by rfl⟩ : syracuseStep 1631981 = 611993) B611993
theorem B812801 : Blo 570811 812801 := bstep (se 2 (by rfl) ⟨304800, by rfl⟩ : syracuseStep 812801 = 609601) B609601
theorem B1926989 : Blo 570811 1926989 := bstep (se 3 (by rfl) ⟨361310, by rfl⟩ : syracuseStep 1926989 = 722621) B722621
theorem B3303281 : Blo 570811 3303281 := bstep (se 2 (by rfl) ⟨1238730, by rfl⟩ : syracuseStep 3303281 = 2477461) B2477461
theorem B1927043 : Blo 570811 1927043 := bstep (se 1 (by rfl) ⟨1445282, by rfl⟩ : syracuseStep 1927043 = 2890565) B2890565
theorem B1632163 : Blo 570811 1632163 := bstep (se 1 (by rfl) ⟨1224122, by rfl⟩ : syracuseStep 1632163 = 2448245) B2448245
theorem B2451491 : Blo 570811 2451491 := bstep (se 1 (by rfl) ⟨1838618, by rfl⟩ : syracuseStep 2451491 = 3677237) B3677237
theorem B1927313 : Blo 570811 1927313 := bstep (se 2 (by rfl) ⟨722742, by rfl⟩ : syracuseStep 1927313 = 1445485) B1445485
theorem B3106993 : Blo 570811 3106993 := bstep (se 2 (by rfl) ⟨1165122, by rfl⟩ : syracuseStep 3106993 = 2330245) B2330245
theorem B813331 : Blo 570811 813331 := bstep (se 1 (by rfl) ⟨609998, by rfl⟩ : syracuseStep 813331 = 1219997) B1219997
theorem B1042723 : Blo 570811 1042723 := bstep (se 1 (by rfl) ⟨782042, by rfl⟩ : syracuseStep 1042723 = 1564085) B1564085
theorem B2517475 : Blo 570811 2517475 := bstep (se 1 (by rfl) ⟨1888106, by rfl⟩ : syracuseStep 2517475 = 3776213) B3776213
theorem B2058787 : Blo 570811 2058787 := bstep (se 1 (by rfl) ⟨1544090, by rfl⟩ : syracuseStep 2058787 = 3088181) B3088181
theorem B813667 : Blo 570811 813667 := bstep (se 1 (by rfl) ⟨610250, by rfl⟩ : syracuseStep 813667 = 1220501) B1220501
theorem B2746993 : Blo 570811 2746993 := bstep (se 2 (by rfl) ⟨1030122, by rfl⟩ : syracuseStep 2746993 = 2060245) B2060245
theorem B1927853 : Blo 570811 1927853 := bstep (se 3 (by rfl) ⟨361472, by rfl⟩ : syracuseStep 1927853 = 722945) B722945
theorem B1927907 : Blo 570811 1927907 := bstep (se 1 (by rfl) ⟨1445930, by rfl⟩ : syracuseStep 1927907 = 2891861) B2891861
theorem B7858997 : Blo 570811 7858997 := bstep (se 5 (by rfl) ⟨368390, by rfl⟩ : syracuseStep 7858997 = 736781) B736781
theorem B1469315 : Blo 570811 1469315 := bstep (se 1 (by rfl) ⟨1101986, by rfl⟩ : syracuseStep 1469315 = 2203973) B2203973
theorem B1928177 : Blo 570811 1928177 := bstep (se 2 (by rfl) ⟨723066, by rfl⟩ : syracuseStep 1928177 = 1446133) B1446133
theorem B814225 : Blo 570811 814225 := bstep (se 2 (by rfl) ⟨305334, by rfl⟩ : syracuseStep 814225 = 610669) B610669
theorem B814259 : Blo 570811 814259 := bstep (se 1 (by rfl) ⟨610694, by rfl⟩ : syracuseStep 814259 = 1221389) B1221389
theorem B1633553 : Blo 570811 1633553 := bstep (se 2 (by rfl) ⟨612582, by rfl⟩ : syracuseStep 1633553 = 1225165) B1225165
theorem B1961329 : Blo 570811 1961329 := bstep (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) B1470997
theorem B2092493 : Blo 570811 2092493 := bstep (se 3 (by rfl) ⟨392342, by rfl⟩ : syracuseStep 2092493 = 784685) B784685
theorem B1928717 : Blo 570811 1928717 := bstep (se 3 (by rfl) ⟨361634, by rfl⟩ : syracuseStep 1928717 = 723269) B723269
theorem B1928771 : Blo 570811 1928771 := bstep (se 1 (by rfl) ⟨1446578, by rfl⟩ : syracuseStep 1928771 = 2893157) B2893157
theorem B1830509 : Blo 570811 1830509 := bstep (se 3 (by rfl) ⟨343220, by rfl⟩ : syracuseStep 1830509 = 686441) B686441
theorem B3665549 : Blo 570811 3665549 := bstep (se 3 (by rfl) ⟨687290, by rfl⟩ : syracuseStep 3665549 = 1374581) B1374581
theorem B814817 : Blo 570811 814817 := bstep (se 2 (by rfl) ⟨305556, by rfl⟩ : syracuseStep 814817 = 611113) B611113
theorem B978689 : Blo 570811 978689 := bstep (se 2 (by rfl) ⟨367008, by rfl⟩ : syracuseStep 978689 = 734017) B734017
theorem B814897 : Blo 570811 814897 := bstep (se 2 (by rfl) ⟨305586, by rfl⟩ : syracuseStep 814897 = 611173) B611173
theorem B1929041 : Blo 570811 1929041 := bstep (se 2 (by rfl) ⟨723390, by rfl⟩ : syracuseStep 1929041 = 1446781) B1446781
theorem B1830929 : Blo 570811 1830929 := bstep (se 2 (by rfl) ⟨686598, by rfl⟩ : syracuseStep 1830929 = 1373197) B1373197
theorem B1962083 : Blo 570811 1962083 := bstep (se 1 (by rfl) ⟨1471562, by rfl⟩ : syracuseStep 1962083 = 2943125) B2943125
theorem B1568909 : Blo 570811 1568909 := bstep (se 3 (by rfl) ⟨294170, by rfl⟩ : syracuseStep 1568909 = 588341) B588341
theorem B3272845 : Blo 570811 3272845 := bstep (se 3 (by rfl) ⟨613658, by rfl⟩ : syracuseStep 3272845 = 1227317) B1227317
theorem B1634509 : Blo 570811 1634509 := bstep (se 3 (by rfl) ⟨306470, by rfl⟩ : syracuseStep 1634509 = 612941) B612941
theorem B1929581 : Blo 570811 1929581 := bstep (se 3 (by rfl) ⟨361796, by rfl⟩ : syracuseStep 1929581 = 723593) B723593
theorem B1929635 : Blo 570811 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B1634737 : Blo 570811 1634737 := bstep (se 2 (by rfl) ⟨613026, by rfl⟩ : syracuseStep 1634737 = 1226053) B1226053
theorem B815683 : Blo 570811 815683 := bstep (se 1 (by rfl) ⟨611762, by rfl⟩ : syracuseStep 815683 = 1223525) B1223525
theorem B1634897 : Blo 570811 1634897 := bstep (se 2 (by rfl) ⟨613086, by rfl⟩ : syracuseStep 1634897 = 1226173) B1226173
theorem B1929905 : Blo 570811 1929905 := bstep (se 2 (by rfl) ⟨723714, by rfl⟩ : syracuseStep 1929905 = 1447429) B1447429
theorem B1635011 : Blo 570811 1635011 := bstep (se 1 (by rfl) ⟨1226258, by rfl⟩ : syracuseStep 1635011 = 2452517) B2452517
theorem B1864433 : Blo 570811 1864433 := bstep (se 2 (by rfl) ⟨699162, by rfl⟩ : syracuseStep 1864433 = 1398325) B1398325
theorem B2945933 : Blo 570811 2945933 := bstep (se 3 (by rfl) ⟨552362, by rfl⟩ : syracuseStep 2945933 = 1104725) B1104725
theorem B816161 : Blo 570811 816161 := bstep (se 2 (by rfl) ⟨306060, by rfl⟩ : syracuseStep 816161 = 612121) B612121
theorem B816275 : Blo 570811 816275 := bstep (se 1 (by rfl) ⟨612206, by rfl⟩ : syracuseStep 816275 = 1224413) B1224413
theorem B1930445 : Blo 570811 1930445 := bstep (se 3 (by rfl) ⟨361958, by rfl⟩ : syracuseStep 1930445 = 723917) B723917
theorem B816355 : Blo 570811 816355 := bstep (se 1 (by rfl) ⟨612266, by rfl⟩ : syracuseStep 816355 = 1224533) B1224533
theorem B1471729 : Blo 570811 1471729 := bstep (se 2 (by rfl) ⟨551898, by rfl⟩ : syracuseStep 1471729 = 1103797) B1103797
theorem B1930499 : Blo 570811 1930499 := bstep (se 1 (by rfl) ⟨1447874, by rfl⟩ : syracuseStep 1930499 = 2895749) B2895749
theorem B1570225 : Blo 570811 1570225 := bstep (se 2 (by rfl) ⟨588834, by rfl⟩ : syracuseStep 1570225 = 1177669) B1177669
theorem B1930769 : Blo 570811 1930769 := bstep (se 2 (by rfl) ⟨724038, by rfl⟩ : syracuseStep 1930769 = 1448077) B1448077
theorem B2455181 : Blo 570811 2455181 := bstep (se 3 (by rfl) ⟨460346, by rfl⟩ : syracuseStep 2455181 = 920693) B920693
theorem B1636013 : Blo 570811 1636013 := bstep (se 3 (by rfl) ⟨306752, by rfl⟩ : syracuseStep 1636013 = 613505) B613505
theorem B2455217 : Blo 570811 2455217 := bstep (se 2 (by rfl) ⟨920706, by rfl⟩ : syracuseStep 2455217 = 1841413) B1841413
theorem B6715061 : Blo 570811 6715061 := bstep (se 5 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 6715061 = 629537) B629537
theorem B816913 : Blo 570811 816913 := bstep (se 2 (by rfl) ⟨306342, by rfl⟩ : syracuseStep 816913 = 612685) B612685
theorem B25196309 : Blo 570811 25196309 := bstep (se 6 (by rfl) ⟨590538, by rfl⟩ : syracuseStep 25196309 = 1181077) B1181077
theorem B3667781 : Blo 570811 3667781 := bstep (se 4 (by rfl) ⟨343854, by rfl⟩ : syracuseStep 3667781 = 687709) B687709
theorem B1636195 : Blo 570811 1636195 := bstep (se 1 (by rfl) ⟨1227146, by rfl⟩ : syracuseStep 1636195 = 2454293) B2454293
theorem B685955 : Blo 570811 685955 := bstep (se 1 (by rfl) ⟨514466, by rfl⟩ : syracuseStep 685955 = 1028933) B1028933
theorem B1308593 : Blo 570811 1308593 := bstep (se 2 (by rfl) ⟨490722, by rfl⟩ : syracuseStep 1308593 = 981445) B981445
theorem B1636355 : Blo 570811 1636355 := bstep (se 1 (by rfl) ⟨1227266, by rfl⟩ : syracuseStep 1636355 = 2454533) B2454533
theorem B2488333 : Blo 570811 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B1931309 : Blo 570811 1931309 := bstep (se 3 (by rfl) ⟨362120, by rfl⟩ : syracuseStep 1931309 = 724241) B724241
theorem B1931363 : Blo 570811 1931363 := bstep (se 1 (by rfl) ⟨1448522, by rfl⟩ : syracuseStep 1931363 = 2897045) B2897045
theorem B915619 : Blo 570811 915619 := bstep (se 1 (by rfl) ⟨686714, by rfl⟩ : syracuseStep 915619 = 1373429) B1373429
theorem B1374371 : Blo 570811 1374371 := bstep (se 1 (by rfl) ⟨1030778, by rfl⟩ : syracuseStep 1374371 = 2061557) B2061557
theorem B686291 : Blo 570811 686291 := bstep (se 1 (by rfl) ⟨514718, by rfl⟩ : syracuseStep 686291 = 1029437) B1029437
theorem B1767683 : Blo 570811 1767683 := bstep (se 1 (by rfl) ⟨1325762, by rfl⟩ : syracuseStep 1767683 = 2651525) B2651525
theorem B915715 : Blo 570811 915715 := bstep (se 1 (by rfl) ⟨686786, by rfl⟩ : syracuseStep 915715 = 1373573) B1373573
theorem B1931633 : Blo 570811 1931633 := bstep (se 2 (by rfl) ⟨724362, by rfl⟩ : syracuseStep 1931633 = 1448725) B1448725
theorem B1571185 : Blo 570811 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B915875 : Blo 570811 915875 := bstep (se 1 (by rfl) ⟨686906, by rfl⟩ : syracuseStep 915875 = 1373813) B1373813
theorem B4880837 : Blo 570811 4880837 := bstep (se 4 (by rfl) ⟨457578, by rfl⟩ : syracuseStep 4880837 = 915157) B915157
theorem B2783693 : Blo 570811 2783693 := bstep (se 3 (by rfl) ⟨521942, by rfl⟩ : syracuseStep 2783693 = 1043885) B1043885
theorem B817619 : Blo 570811 817619 := bstep (se 1 (by rfl) ⟨613214, by rfl⟩ : syracuseStep 817619 = 1226429) B1226429
theorem B588259 : Blo 570811 588259 := bstep (se 1 (by rfl) ⟨441194, by rfl⟩ : syracuseStep 588259 = 882389) B882389
theorem B4127203 : Blo 570811 4127203 := bstep (se 1 (by rfl) ⟨3095402, by rfl⟩ : syracuseStep 4127203 = 6190805) B6190805
theorem B785281 : Blo 570811 785281 := bstep (se 2 (by rfl) ⟨294480, by rfl⟩ : syracuseStep 785281 = 588961) B588961
theorem B1932173 : Blo 570811 1932173 := bstep (se 3 (by rfl) ⟨362282, by rfl⟩ : syracuseStep 1932173 = 724565) B724565
theorem B1932227 : Blo 570811 1932227 := bstep (se 1 (by rfl) ⟨1449170, by rfl⟩ : syracuseStep 1932227 = 2898341) B2898341
theorem B1309763 : Blo 570811 1309763 := bstep (se 1 (by rfl) ⟨982322, by rfl⟩ : syracuseStep 1309763 = 1964645) B1964645
theorem B818257 : Blo 570811 818257 := bstep (se 2 (by rfl) ⟨306846, by rfl⟩ : syracuseStep 818257 = 613693) B613693
theorem B1375427 : Blo 570811 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B818371 : Blo 570811 818371 := bstep (se 1 (by rfl) ⟨613778, by rfl⟩ : syracuseStep 818371 = 1227557) B1227557
theorem B1932497 : Blo 570811 1932497 := bstep (se 2 (by rfl) ⟨724686, by rfl⟩ : syracuseStep 1932497 = 1449373) B1449373
theorem B1375505 : Blo 570811 1375505 := bstep (se 2 (by rfl) ⟨515814, by rfl⟩ : syracuseStep 1375505 = 1031629) B1031629
theorem B1834339 : Blo 570811 1834339 := bstep (se 1 (by rfl) ⟨1375754, by rfl⟩ : syracuseStep 1834339 = 2751509) B2751509
theorem B4357475 : Blo 570811 4357475 := bstep (se 1 (by rfl) ⟨3268106, by rfl⟩ : syracuseStep 4357475 = 6536213) B6536213
theorem B916849 : Blo 570811 916849 := bstep (se 2 (by rfl) ⟨343818, by rfl⟩ : syracuseStep 916849 = 687637) B687637
theorem B1965521 : Blo 570811 1965521 := bstep (se 2 (by rfl) ⟨737070, by rfl⟩ : syracuseStep 1965521 = 1474141) B1474141
theorem B1310179 : Blo 570811 1310179 := bstep (se 1 (by rfl) ⟨982634, by rfl⟩ : syracuseStep 1310179 = 1965269) B1965269
theorem B1834609 : Blo 570811 1834609 := bstep (se 2 (by rfl) ⟨687978, by rfl⟩ : syracuseStep 1834609 = 1375957) B1375957
theorem B2752163 : Blo 570811 2752163 := bstep (se 1 (by rfl) ⟨2064122, by rfl⟩ : syracuseStep 2752163 = 4128245) B4128245
theorem B1933037 : Blo 570811 1933037 := bstep (se 3 (by rfl) ⟨362444, by rfl⟩ : syracuseStep 1933037 = 724889) B724889
theorem B1933091 : Blo 570811 1933091 := bstep (se 1 (by rfl) ⟨1449818, by rfl⟩ : syracuseStep 1933091 = 2899637) B2899637
theorem B884657 : Blo 570811 884657 := bstep (se 2 (by rfl) ⟨331746, by rfl⟩ : syracuseStep 884657 = 663493) B663493
theorem B917515 : Blo 570811 917515 := bstep (se 1 (by rfl) ⟨688136, by rfl⟩ : syracuseStep 917515 = 1376273) B1376273
theorem B4882477 : Blo 570811 4882477 := bstep (se 3 (by rfl) ⟨915464, by rfl⟩ : syracuseStep 4882477 = 1830929) B1830929
theorem B2490689 : Blo 570811 2490689 := bstep (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) B1868017
theorem B1835543 : Blo 570811 1835543 := bstep (se 1 (by rfl) ⟨1376657, by rfl⟩ : syracuseStep 1835543 = 2753315) B2753315
theorem B1933847 : Blo 570811 1933847 := bstep (se 1 (by rfl) ⟨1450385, by rfl⟩ : syracuseStep 1933847 = 2900771) B2900771
theorem B918233 : Blo 570811 918233 := bstep (se 2 (by rfl) ⟨344337, by rfl⟩ : syracuseStep 918233 = 688675) B688675
theorem B2753297 : Blo 570811 2753297 := bstep (se 2 (by rfl) ⟨1032486, by rfl⟩ : syracuseStep 2753297 = 2064973) B2064973
theorem B1836055 : Blo 570811 1836055 := bstep (se 1 (by rfl) ⟨1377041, by rfl⟩ : syracuseStep 1836055 = 2754083) B2754083
theorem B1934387 : Blo 570811 1934387 := bstep (se 1 (by rfl) ⟨1450790, by rfl⟩ : syracuseStep 1934387 = 2901581) B2901581
theorem B918745 : Blo 570811 918745 := bstep (se 2 (by rfl) ⟨344529, by rfl⟩ : syracuseStep 918745 = 689059) B689059
theorem B1934657 : Blo 570811 1934657 := bstep (se 2 (by rfl) ⟨725496, by rfl⟩ : syracuseStep 1934657 = 1450993) B1450993
theorem B4883813 : Blo 570811 4883813 := bstep (se 4 (by rfl) ⟨457857, by rfl⟩ : syracuseStep 4883813 = 915715) B915715
theorem B2196887 : Blo 570811 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B15926797 : Blo 570811 15926797 := bstep (se 3 (by rfl) ⟨2986274, by rfl⟩ : syracuseStep 15926797 = 5972549) B5972549
theorem B1377985 : Blo 570811 1377985 := bstep (se 2 (by rfl) ⟨516744, by rfl⟩ : syracuseStep 1377985 = 1033489) B1033489
theorem B1836875 : Blo 570811 1836875 := bstep (se 1 (by rfl) ⟨1377656, by rfl⟩ : syracuseStep 1836875 = 2755313) B2755313
theorem B1935197 : Blo 570811 1935197 := bstep (se 3 (by rfl) ⟨362849, by rfl⟩ : syracuseStep 1935197 = 725699) B725699
theorem B722839 : Blo 570811 722839 := bstep (se 1 (by rfl) ⟨542129, by rfl⟩ : syracuseStep 722839 = 1084259) B1084259
theorem B2656259 : Blo 570811 2656259 := bstep (se 1 (by rfl) ⟨1992194, by rfl⟩ : syracuseStep 2656259 = 3984389) B3984389
theorem B3541085 : Blo 570811 3541085 := bstep (se 3 (by rfl) ⟨663953, by rfl⟩ : syracuseStep 3541085 = 1327907) B1327907
theorem B3672215 : Blo 570811 3672215 := bstep (se 1 (by rfl) ⟨2754161, by rfl⟩ : syracuseStep 3672215 = 5508323) B5508323
theorem B1837235 : Blo 570811 1837235 := bstep (se 1 (by rfl) ⟨1377926, by rfl⟩ : syracuseStep 1837235 = 2755853) B2755853
theorem B2066705 : Blo 570811 2066705 := bstep (se 2 (by rfl) ⟨775014, by rfl⟩ : syracuseStep 2066705 = 1550029) B1550029
theorem B1018391 : Blo 570811 1018391 := bstep (se 1 (by rfl) ⟨763793, by rfl⟩ : syracuseStep 1018391 = 1527587) B1527587
theorem B1083955 : Blo 570811 1083955 := bstep (se 1 (by rfl) ⟨812966, by rfl⟩ : syracuseStep 1083955 = 1625933) B1625933
theorem B10980197 : Blo 570811 10980197 := bstep (se 4 (by rfl) ⟨1029393, by rfl⟩ : syracuseStep 10980197 = 2058787) B2058787
theorem B12389219 : Blo 570811 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B1936331 : Blo 570811 1936331 := bstep (se 1 (by rfl) ⟨1452248, by rfl⟩ : syracuseStep 1936331 = 2904497) B2904497
theorem B1084403 : Blo 570811 1084403 := bstep (se 1 (by rfl) ⟨813302, by rfl⟩ : syracuseStep 1084403 = 1626605) B1626605
theorem B1084441 : Blo 570811 1084441 := bstep (se 2 (by rfl) ⟨406665, by rfl⟩ : syracuseStep 1084441 = 813331) B813331
theorem B1739827 : Blo 570811 1739827 := bstep (se 1 (by rfl) ⟨1304870, by rfl⟩ : syracuseStep 1739827 = 2609741) B2609741
theorem B4787275 : Blo 570811 4787275 := bstep (se 1 (by rfl) ⟨3590456, by rfl⟩ : syracuseStep 4787275 = 7180913) B7180913
theorem B1936601 : Blo 570811 1936601 := bstep (se 2 (by rfl) ⟨726225, by rfl⟩ : syracuseStep 1936601 = 1452451) B1452451
theorem B1445323 : Blo 570811 1445323 := bstep (se 1 (by rfl) ⟨1083992, by rfl⟩ : syracuseStep 1445323 = 2167985) B2167985
theorem B1084889 : Blo 570811 1084889 := bstep (se 2 (by rfl) ⟨406833, by rfl⟩ : syracuseStep 1084889 = 813667) B813667
theorem B1543745 : Blo 570811 1543745 := bstep (se 2 (by rfl) ⟨578904, by rfl⟩ : syracuseStep 1543745 = 1157809) B1157809
theorem B724555 : Blo 570811 724555 := bstep (se 1 (by rfl) ⟨543416, by rfl⟩ : syracuseStep 724555 = 1086833) B1086833
theorem B1445465 : Blo 570811 1445465 := bstep (se 2 (by rfl) ⟨542049, by rfl⟩ : syracuseStep 1445465 = 1084099) B1084099
theorem B1937303 : Blo 570811 1937303 := bstep (se 1 (by rfl) ⟨1452977, by rfl⟩ : syracuseStep 1937303 = 2905955) B2905955
theorem B856217 : Blo 570811 856217 := bstep (se 2 (by rfl) ⟨321081, by rfl⟩ : syracuseStep 856217 = 642163) B642163
theorem B1085633 : Blo 570811 1085633 := bstep (se 2 (by rfl) ⟨407112, by rfl⟩ : syracuseStep 1085633 = 814225) B814225
theorem B856331 : Blo 570811 856331 := bstep (se 1 (by rfl) ⟨642248, by rfl⟩ : syracuseStep 856331 = 1284497) B1284497
theorem B856343 : Blo 570811 856343 := bstep (se 1 (by rfl) ⟨642257, by rfl⟩ : syracuseStep 856343 = 1284515) B1284515
theorem B856409 : Blo 570811 856409 := bstep (se 2 (by rfl) ⟨321153, by rfl⟩ : syracuseStep 856409 = 642307) B642307
theorem B1446295 : Blo 570811 1446295 := bstep (se 1 (by rfl) ⟨1084721, by rfl⟩ : syracuseStep 1446295 = 2169443) B2169443
theorem B1937843 : Blo 570811 1937843 := bstep (se 1 (by rfl) ⟨1453382, by rfl⟩ : syracuseStep 1937843 = 2906765) B2906765
theorem B856523 : Blo 570811 856523 := bstep (se 1 (by rfl) ⟨642392, by rfl⟩ : syracuseStep 856523 = 1284785) B1284785
theorem B1085899 : Blo 570811 1085899 := bstep (se 1 (by rfl) ⟨814424, by rfl⟩ : syracuseStep 1085899 = 1628849) B1628849
theorem B856535 : Blo 570811 856535 := bstep (se 1 (by rfl) ⟨642401, by rfl⟩ : syracuseStep 856535 = 1284803) B1284803
theorem B725527 : Blo 570811 725527 := bstep (se 1 (by rfl) ⟨544145, by rfl⟩ : syracuseStep 725527 = 1088291) B1088291
theorem B856601 : Blo 570811 856601 := bstep (se 2 (by rfl) ⟨321225, by rfl⟩ : syracuseStep 856601 = 642451) B642451
theorem B856715 : Blo 570811 856715 := bstep (se 1 (by rfl) ⟨642536, by rfl⟩ : syracuseStep 856715 = 1285073) B1285073
theorem B856727 : Blo 570811 856727 := bstep (se 1 (by rfl) ⟨642545, by rfl⟩ : syracuseStep 856727 = 1285091) B1285091
theorem B2167469 : Blo 570811 2167469 := bstep (se 3 (by rfl) ⟨406400, by rfl⟩ : syracuseStep 2167469 = 812801) B812801
theorem B1938113 : Blo 570811 1938113 := bstep (se 2 (by rfl) ⟨726792, by rfl⟩ : syracuseStep 1938113 = 1453585) B1453585
theorem B2167499 : Blo 570811 2167499 := bstep (se 1 (by rfl) ⟨1625624, by rfl⟩ : syracuseStep 2167499 = 3251249) B3251249
theorem B856793 : Blo 570811 856793 := bstep (se 2 (by rfl) ⟨321297, by rfl⟩ : syracuseStep 856793 = 642595) B642595
theorem B856907 : Blo 570811 856907 := bstep (se 1 (by rfl) ⟨642680, by rfl⟩ : syracuseStep 856907 = 1285361) B1285361
theorem B1446731 : Blo 570811 1446731 := bstep (se 1 (by rfl) ⟨1085048, by rfl⟩ : syracuseStep 1446731 = 2170097) B2170097
theorem B856919 : Blo 570811 856919 := bstep (se 1 (by rfl) ⟨642689, by rfl⟩ : syracuseStep 856919 = 1285379) B1285379
theorem B1086347 : Blo 570811 1086347 := bstep (se 1 (by rfl) ⟨814760, by rfl⟩ : syracuseStep 1086347 = 1629521) B1629521
theorem B856985 : Blo 570811 856985 := bstep (se 2 (by rfl) ⟨321369, by rfl⟩ : syracuseStep 856985 = 642739) B642739
theorem B857099 : Blo 570811 857099 := bstep (se 1 (by rfl) ⟨642824, by rfl⟩ : syracuseStep 857099 = 1285649) B1285649
theorem B857111 : Blo 570811 857111 := bstep (se 1 (by rfl) ⟨642833, by rfl⟩ : syracuseStep 857111 = 1285667) B1285667
theorem B1086529 : Blo 570811 1086529 := bstep (se 2 (by rfl) ⟨407448, by rfl⟩ : syracuseStep 1086529 = 814897) B814897
theorem B857177 : Blo 570811 857177 := bstep (se 2 (by rfl) ⟨321441, by rfl⟩ : syracuseStep 857177 = 642883) B642883
theorem B1447105 : Blo 570811 1447105 := bstep (se 2 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 1447105 = 1085329) B1085329
theorem B857291 : Blo 570811 857291 := bstep (se 1 (by rfl) ⟨642968, by rfl⟩ : syracuseStep 857291 = 1285937) B1285937
theorem B857303 : Blo 570811 857303 := bstep (se 1 (by rfl) ⟨642977, by rfl⟩ : syracuseStep 857303 = 1285955) B1285955
theorem B1938653 : Blo 570811 1938653 := bstep (se 3 (by rfl) ⟨363497, by rfl⟩ : syracuseStep 1938653 = 726995) B726995
theorem B857369 : Blo 570811 857369 := bstep (se 2 (by rfl) ⟨321513, by rfl⟩ : syracuseStep 857369 = 643027) B643027
theorem B726347 : Blo 570811 726347 := bstep (se 1 (by rfl) ⟨544760, by rfl⟩ : syracuseStep 726347 = 1089521) B1089521
theorem B2168153 : Blo 570811 2168153 := bstep (se 2 (by rfl) ⟨813057, by rfl⟩ : syracuseStep 2168153 = 1626115) B1626115
theorem B857483 : Blo 570811 857483 := bstep (se 1 (by rfl) ⟨643112, by rfl⟩ : syracuseStep 857483 = 1286225) B1286225
theorem B857495 : Blo 570811 857495 := bstep (se 1 (by rfl) ⟨643121, by rfl⟩ : syracuseStep 857495 = 1286243) B1286243
theorem B1086871 : Blo 570811 1086871 := bstep (se 1 (by rfl) ⟨815153, by rfl⟩ : syracuseStep 1086871 = 1630307) B1630307
theorem B857561 : Blo 570811 857561 := bstep (se 2 (by rfl) ⟨321585, by rfl⟩ : syracuseStep 857561 = 643171) B643171
theorem B4363793 : Blo 570811 4363793 := bstep (se 2 (by rfl) ⟨1636422, by rfl⟩ : syracuseStep 4363793 = 3272845) B3272845
theorem B857675 : Blo 570811 857675 := bstep (se 1 (by rfl) ⟨643256, by rfl⟩ : syracuseStep 857675 = 1286513) B1286513
theorem B857687 : Blo 570811 857687 := bstep (se 1 (by rfl) ⟨643265, by rfl⟩ : syracuseStep 857687 = 1286531) B1286531
theorem B1087091 : Blo 570811 1087091 := bstep (se 1 (by rfl) ⟨815318, by rfl⟩ : syracuseStep 1087091 = 1630637) B1630637
theorem B3675779 : Blo 570811 3675779 := bstep (se 1 (by rfl) ⟨2756834, by rfl⟩ : syracuseStep 3675779 = 5513669) B5513669
theorem B2168471 : Blo 570811 2168471 := bstep (se 1 (by rfl) ⟨1626353, by rfl⟩ : syracuseStep 2168471 = 3252707) B3252707
theorem B857753 : Blo 570811 857753 := bstep (se 2 (by rfl) ⟨321657, by rfl⟩ : syracuseStep 857753 = 643315) B643315
theorem B857867 : Blo 570811 857867 := bstep (se 1 (by rfl) ⟨643400, by rfl⟩ : syracuseStep 857867 = 1286801) B1286801
theorem B857879 : Blo 570811 857879 := bstep (se 1 (by rfl) ⟨643409, by rfl⟩ : syracuseStep 857879 = 1286819) B1286819
theorem B1447703 : Blo 570811 1447703 := bstep (se 1 (by rfl) ⟨1085777, by rfl⟩ : syracuseStep 1447703 = 2171555) B2171555
theorem B1087319 : Blo 570811 1087319 := bstep (se 1 (by rfl) ⟨815489, by rfl⟩ : syracuseStep 1087319 = 1630979) B1630979
theorem B857945 : Blo 570811 857945 := bstep (se 2 (by rfl) ⟨321729, by rfl⟩ : syracuseStep 857945 = 643459) B643459
theorem B858059 : Blo 570811 858059 := bstep (se 1 (by rfl) ⟨643544, by rfl⟩ : syracuseStep 858059 = 1287089) B1287089
theorem B858071 : Blo 570811 858071 := bstep (se 1 (by rfl) ⟨643553, by rfl⟩ : syracuseStep 858071 = 1287107) B1287107
theorem B727051 : Blo 570811 727051 := bstep (se 1 (by rfl) ⟨545288, by rfl⟩ : syracuseStep 727051 = 1090577) B1090577
theorem B858137 : Blo 570811 858137 := bstep (se 2 (by rfl) ⟨321801, by rfl⟩ : syracuseStep 858137 = 643603) B643603
theorem B1087577 : Blo 570811 1087577 := bstep (se 2 (by rfl) ⟨407841, by rfl⟩ : syracuseStep 1087577 = 815683) B815683
theorem B858251 : Blo 570811 858251 := bstep (se 1 (by rfl) ⟨643688, by rfl⟩ : syracuseStep 858251 = 1287377) B1287377
theorem B858263 : Blo 570811 858263 := bstep (se 1 (by rfl) ⟨643697, by rfl⟩ : syracuseStep 858263 = 1287395) B1287395
theorem B858329 : Blo 570811 858329 := bstep (se 2 (by rfl) ⟨321873, by rfl⟩ : syracuseStep 858329 = 643747) B643747
theorem B1284353 : Blo 570811 1284353 := bstep (se 2 (by rfl) ⟨481632, by rfl⟩ : syracuseStep 1284353 = 963265) B963265
theorem B2201879 : Blo 570811 2201879 := bstep (se 1 (by rfl) ⟨1651409, by rfl⟩ : syracuseStep 2201879 = 3302819) B3302819
theorem B727319 : Blo 570811 727319 := bstep (se 1 (by rfl) ⟨545489, by rfl⟩ : syracuseStep 727319 = 1090979) B1090979
theorem B2169139 : Blo 570811 2169139 := bstep (se 1 (by rfl) ⟨1626854, by rfl⟩ : syracuseStep 2169139 = 3253709) B3253709
theorem B858443 : Blo 570811 858443 := bstep (se 1 (by rfl) ⟨643832, by rfl⟩ : syracuseStep 858443 = 1287665) B1287665
theorem B1939787 : Blo 570811 1939787 := bstep (se 1 (by rfl) ⟨1454840, by rfl⟩ : syracuseStep 1939787 = 2909681) B2909681
theorem B858455 : Blo 570811 858455 := bstep (se 1 (by rfl) ⟨643841, by rfl⟩ : syracuseStep 858455 = 1287683) B1287683
theorem B858521 : Blo 570811 858521 := bstep (se 2 (by rfl) ⟨321945, by rfl⟩ : syracuseStep 858521 = 643891) B643891
theorem B825815 : Blo 570811 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B1284569 : Blo 570811 1284569 := bstep (se 2 (by rfl) ⟨481713, by rfl⟩ : syracuseStep 1284569 = 963427) B963427
theorem B1087987 : Blo 570811 1087987 := bstep (se 1 (by rfl) ⟨815990, by rfl⟩ : syracuseStep 1087987 = 1631981) B1631981
theorem B858635 : Blo 570811 858635 := bstep (se 1 (by rfl) ⟨643976, by rfl⟩ : syracuseStep 858635 = 1287953) B1287953
theorem B858647 : Blo 570811 858647 := bstep (se 1 (by rfl) ⟨643985, by rfl⟩ : syracuseStep 858647 = 1287971) B1287971
theorem B1284659 : Blo 570811 1284659 := bstep (se 1 (by rfl) ⟨963494, by rfl⟩ : syracuseStep 1284659 = 1926989) B1926989
theorem B1448513 : Blo 570811 1448513 := bstep (se 2 (by rfl) ⟨543192, by rfl⟩ : syracuseStep 1448513 = 1086385) B1086385
theorem B2202187 : Blo 570811 2202187 := bstep (se 1 (by rfl) ⟨1651640, by rfl⟩ : syracuseStep 2202187 = 3303281) B3303281
theorem B1284695 : Blo 570811 1284695 := bstep (se 1 (by rfl) ⟨963521, by rfl⟩ : syracuseStep 1284695 = 1927043) B1927043
theorem B858713 : Blo 570811 858713 := bstep (se 2 (by rfl) ⟨322017, by rfl⟩ : syracuseStep 858713 = 644035) B644035
theorem B858827 : Blo 570811 858827 := bstep (se 1 (by rfl) ⟨644120, by rfl⟩ : syracuseStep 858827 = 1288241) B1288241
theorem B989911 : Blo 570811 989911 := bstep (se 1 (by rfl) ⟨742433, by rfl⟩ : syracuseStep 989911 = 1484867) B1484867
theorem B858839 : Blo 570811 858839 := bstep (se 1 (by rfl) ⟨644129, by rfl⟩ : syracuseStep 858839 = 1288259) B1288259
theorem B1284875 : Blo 570811 1284875 := bstep (se 1 (by rfl) ⟨963656, by rfl⟩ : syracuseStep 1284875 = 1927313) B1927313
theorem B858905 : Blo 570811 858905 := bstep (se 2 (by rfl) ⟨322089, by rfl⟩ : syracuseStep 858905 = 644179) B644179
theorem B1284929 : Blo 570811 1284929 := bstep (se 2 (by rfl) ⟨481848, by rfl⟩ : syracuseStep 1284929 = 963697) B963697
theorem B859019 : Blo 570811 859019 := bstep (se 1 (by rfl) ⟨644264, by rfl⟩ : syracuseStep 859019 = 1288529) B1288529
theorem B4397975 : Blo 570811 4397975 := bstep (se 1 (by rfl) ⟨3298481, by rfl⟩ : syracuseStep 4397975 = 6596963) B6596963
theorem B859031 : Blo 570811 859031 := bstep (se 1 (by rfl) ⟨644273, by rfl⟩ : syracuseStep 859031 = 1288547) B1288547
theorem B16489433 : Blo 570811 16489433 := bstep (se 2 (by rfl) ⟨6183537, by rfl⟩ : syracuseStep 16489433 = 12367075) B12367075
theorem B859097 : Blo 570811 859097 := bstep (se 2 (by rfl) ⟨322161, by rfl⟩ : syracuseStep 859097 = 644323) B644323
theorem B1088473 : Blo 570811 1088473 := bstep (se 2 (by rfl) ⟨408177, by rfl⟩ : syracuseStep 1088473 = 816355) B816355
theorem B1285145 : Blo 570811 1285145 := bstep (se 2 (by rfl) ⟨481929, by rfl⟩ : syracuseStep 1285145 = 963859) B963859
theorem B859211 : Blo 570811 859211 := bstep (se 1 (by rfl) ⟨644408, by rfl⟩ : syracuseStep 859211 = 1288817) B1288817
theorem B859223 : Blo 570811 859223 := bstep (se 1 (by rfl) ⟨644417, by rfl⟩ : syracuseStep 859223 = 1288835) B1288835
theorem B1449049 : Blo 570811 1449049 := bstep (se 2 (by rfl) ⟨543393, by rfl⟩ : syracuseStep 1449049 = 1086787) B1086787
theorem B1285235 : Blo 570811 1285235 := bstep (se 1 (by rfl) ⟨963926, by rfl⟩ : syracuseStep 1285235 = 1927853) B1927853
theorem B1285271 : Blo 570811 1285271 := bstep (se 1 (by rfl) ⟨963953, by rfl⟩ : syracuseStep 1285271 = 1927907) B1927907
theorem B859289 : Blo 570811 859289 := bstep (se 2 (by rfl) ⟨322233, by rfl⟩ : syracuseStep 859289 = 644467) B644467
theorem B859403 : Blo 570811 859403 := bstep (se 1 (by rfl) ⟨644552, by rfl⟩ : syracuseStep 859403 = 1289105) B1289105
theorem B859415 : Blo 570811 859415 := bstep (se 1 (by rfl) ⟨644561, by rfl⟩ : syracuseStep 859415 = 1289123) B1289123
theorem B3251501 : Blo 570811 3251501 := bstep (se 3 (by rfl) ⟨609656, by rfl⟩ : syracuseStep 3251501 = 1219313) B1219313
theorem B1285451 : Blo 570811 1285451 := bstep (se 1 (by rfl) ⟨964088, by rfl⟩ : syracuseStep 1285451 = 1928177) B1928177
theorem B859481 : Blo 570811 859481 := bstep (se 2 (by rfl) ⟨322305, by rfl⟩ : syracuseStep 859481 = 644611) B644611
theorem B1285505 : Blo 570811 1285505 := bstep (se 2 (by rfl) ⟨482064, by rfl⟩ : syracuseStep 1285505 = 964129) B964129
theorem B859595 : Blo 570811 859595 := bstep (se 1 (by rfl) ⟨644696, by rfl⟩ : syracuseStep 859595 = 1289393) B1289393
theorem B859607 : Blo 570811 859607 := bstep (se 1 (by rfl) ⟨644705, by rfl⟩ : syracuseStep 859607 = 1289411) B1289411
theorem B1089035 : Blo 570811 1089035 := bstep (se 1 (by rfl) ⟨816776, by rfl⟩ : syracuseStep 1089035 = 1633553) B1633553
theorem B2170385 : Blo 570811 2170385 := bstep (se 2 (by rfl) ⟨813894, by rfl⟩ : syracuseStep 2170385 = 1627789) B1627789
theorem B859673 : Blo 570811 859673 := bstep (se 2 (by rfl) ⟨322377, by rfl⟩ : syracuseStep 859673 = 644755) B644755
theorem B1285721 : Blo 570811 1285721 := bstep (se 2 (by rfl) ⟨482145, by rfl⟩ : syracuseStep 1285721 = 964291) B964291
theorem B859787 : Blo 570811 859787 := bstep (se 1 (by rfl) ⟨644840, by rfl⟩ : syracuseStep 859787 = 1289681) B1289681
theorem B859799 : Blo 570811 859799 := bstep (se 1 (by rfl) ⟨644849, by rfl⟩ : syracuseStep 859799 = 1289699) B1289699
theorem B1285811 : Blo 570811 1285811 := bstep (se 1 (by rfl) ⟨964358, by rfl⟩ : syracuseStep 1285811 = 1928717) B1928717
theorem B1089217 : Blo 570811 1089217 := bstep (se 2 (by rfl) ⟨408456, by rfl⟩ : syracuseStep 1089217 = 816913) B816913
theorem B1285847 : Blo 570811 1285847 := bstep (se 1 (by rfl) ⟨964385, by rfl⟩ : syracuseStep 1285847 = 1928771) B1928771
theorem B859865 : Blo 570811 859865 := bstep (se 2 (by rfl) ⟨322449, by rfl⟩ : syracuseStep 859865 = 644899) B644899
theorem B1220339 : Blo 570811 1220339 := bstep (se 1 (by rfl) ⟨915254, by rfl⟩ : syracuseStep 1220339 = 1830509) B1830509
theorem B2891537 : Blo 570811 2891537 := bstep (se 2 (by rfl) ⟨1084326, by rfl⟩ : syracuseStep 2891537 = 2168653) B2168653
theorem B859979 : Blo 570811 859979 := bstep (se 1 (by rfl) ⟨644984, by rfl⟩ : syracuseStep 859979 = 1289969) B1289969
theorem B859991 : Blo 570811 859991 := bstep (se 1 (by rfl) ⟨644993, by rfl⟩ : syracuseStep 859991 = 1289987) B1289987
theorem B1286027 : Blo 570811 1286027 := bstep (se 1 (by rfl) ⟨964520, by rfl⟩ : syracuseStep 1286027 = 1929041) B1929041
theorem B860057 : Blo 570811 860057 := bstep (se 2 (by rfl) ⟨322521, by rfl⟩ : syracuseStep 860057 = 645043) B645043
theorem B2891699 : Blo 570811 2891699 := bstep (se 1 (by rfl) ⟨2168774, by rfl⟩ : syracuseStep 2891699 = 4337549) B4337549
theorem B1286081 : Blo 570811 1286081 := bstep (se 2 (by rfl) ⟨482280, by rfl⟩ : syracuseStep 1286081 = 964561) B964561
theorem B860171 : Blo 570811 860171 := bstep (se 1 (by rfl) ⟨645128, by rfl⟩ : syracuseStep 860171 = 1290257) B1290257
theorem B3317777 : Blo 570811 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B860183 : Blo 570811 860183 := bstep (se 1 (by rfl) ⟨645137, by rfl⟩ : syracuseStep 860183 = 1290275) B1290275
theorem B4464715 : Blo 570811 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B860249 : Blo 570811 860249 := bstep (se 2 (by rfl) ⟨322593, by rfl⟩ : syracuseStep 860249 = 645187) B645187
theorem B1286297 : Blo 570811 1286297 := bstep (se 2 (by rfl) ⟨482361, by rfl⟩ : syracuseStep 1286297 = 964723) B964723
theorem B1450163 : Blo 570811 1450163 := bstep (se 1 (by rfl) ⟨1087622, by rfl⟩ : syracuseStep 1450163 = 2175245) B2175245
theorem B2171083 : Blo 570811 2171083 := bstep (se 1 (by rfl) ⟨1628312, by rfl⟩ : syracuseStep 2171083 = 3256625) B3256625
theorem B860363 : Blo 570811 860363 := bstep (se 1 (by rfl) ⟨645272, by rfl⟩ : syracuseStep 860363 = 1290545) B1290545
theorem B860375 : Blo 570811 860375 := bstep (se 1 (by rfl) ⟨645281, by rfl⟩ : syracuseStep 860375 = 1290563) B1290563
theorem B1220825 : Blo 570811 1220825 := bstep (se 2 (by rfl) ⟨457809, by rfl⟩ : syracuseStep 1220825 = 915619) B915619
theorem B1286387 : Blo 570811 1286387 := bstep (se 1 (by rfl) ⟨964790, by rfl⟩ : syracuseStep 1286387 = 1929581) B1929581
theorem B1286423 : Blo 570811 1286423 := bstep (se 1 (by rfl) ⟨964817, by rfl⟩ : syracuseStep 1286423 = 1929635) B1929635
theorem B860441 : Blo 570811 860441 := bstep (se 2 (by rfl) ⟨322665, by rfl⟩ : syracuseStep 860441 = 645331) B645331
theorem B860555 : Blo 570811 860555 := bstep (se 1 (by rfl) ⟨645416, by rfl⟩ : syracuseStep 860555 = 1290833) B1290833
theorem B1089931 : Blo 570811 1089931 := bstep (se 1 (by rfl) ⟨817448, by rfl⟩ : syracuseStep 1089931 = 1634897) B1634897
theorem B860567 : Blo 570811 860567 := bstep (se 1 (by rfl) ⟨645425, by rfl⟩ : syracuseStep 860567 = 1290851) B1290851
theorem B1286603 : Blo 570811 1286603 := bstep (se 1 (by rfl) ⟨964952, by rfl⟩ : syracuseStep 1286603 = 1929905) B1929905
theorem B1090007 : Blo 570811 1090007 := bstep (se 1 (by rfl) ⟨817505, by rfl⟩ : syracuseStep 1090007 = 1635011) B1635011
theorem B1450457 : Blo 570811 1450457 := bstep (se 2 (by rfl) ⟨543921, by rfl⟩ : syracuseStep 1450457 = 1087843) B1087843
theorem B860633 : Blo 570811 860633 := bstep (se 2 (by rfl) ⟨322737, by rfl⟩ : syracuseStep 860633 = 645475) B645475
theorem B2171357 : Blo 570811 2171357 := bstep (se 3 (by rfl) ⟨407129, by rfl⟩ : syracuseStep 2171357 = 814259) B814259
theorem B1286657 : Blo 570811 1286657 := bstep (se 2 (by rfl) ⟨482496, by rfl⟩ : syracuseStep 1286657 = 964993) B964993
theorem B860747 : Blo 570811 860747 := bstep (se 1 (by rfl) ⟨645560, by rfl⟩ : syracuseStep 860747 = 1291121) B1291121
theorem B860759 : Blo 570811 860759 := bstep (se 1 (by rfl) ⟨645569, by rfl⟩ : syracuseStep 860759 = 1291139) B1291139
theorem B860825 : Blo 570811 860825 := bstep (se 2 (by rfl) ⟨322809, by rfl⟩ : syracuseStep 860825 = 645619) B645619
theorem B1286873 : Blo 570811 1286873 := bstep (se 2 (by rfl) ⟨482577, by rfl⟩ : syracuseStep 1286873 = 965155) B965155
theorem B860939 : Blo 570811 860939 := bstep (se 1 (by rfl) ⟨645704, by rfl⟩ : syracuseStep 860939 = 1291409) B1291409
theorem B860951 : Blo 570811 860951 := bstep (se 1 (by rfl) ⟨645713, by rfl⟩ : syracuseStep 860951 = 1291427) B1291427
theorem B1286963 : Blo 570811 1286963 := bstep (se 1 (by rfl) ⟨965222, by rfl⟩ : syracuseStep 1286963 = 1930445) B1930445
theorem B1286999 : Blo 570811 1286999 := bstep (se 1 (by rfl) ⟨965249, by rfl⟩ : syracuseStep 1286999 = 1930499) B1930499
theorem B861017 : Blo 570811 861017 := bstep (se 2 (by rfl) ⟨322881, by rfl⟩ : syracuseStep 861017 = 645763) B645763
theorem B861131 : Blo 570811 861131 := bstep (se 1 (by rfl) ⟨645848, by rfl⟩ : syracuseStep 861131 = 1291697) B1291697
theorem B861143 : Blo 570811 861143 := bstep (se 1 (by rfl) ⟨645857, by rfl⟩ : syracuseStep 861143 = 1291715) B1291715
theorem B1287179 : Blo 570811 1287179 := bstep (se 1 (by rfl) ⟨965384, by rfl⟩ : syracuseStep 1287179 = 1930769) B1930769
theorem B861209 : Blo 570811 861209 := bstep (se 2 (by rfl) ⟨322953, by rfl⟩ : syracuseStep 861209 = 645907) B645907
theorem B1287233 : Blo 570811 1287233 := bstep (se 2 (by rfl) ⟨482712, by rfl⟩ : syracuseStep 1287233 = 965425) B965425
theorem B1090675 : Blo 570811 1090675 := bstep (se 1 (by rfl) ⟨818006, by rfl⟩ : syracuseStep 1090675 = 1636013) B1636013
theorem B861323 : Blo 570811 861323 := bstep (se 1 (by rfl) ⟨645992, by rfl⟩ : syracuseStep 861323 = 1291985) B1291985
theorem B2172055 : Blo 570811 2172055 := bstep (se 1 (by rfl) ⟨1629041, by rfl⟩ : syracuseStep 2172055 = 3258083) B3258083
theorem B861335 : Blo 570811 861335 := bstep (se 1 (by rfl) ⟨646001, by rfl⟩ : syracuseStep 861335 = 1292003) B1292003
theorem B861401 : Blo 570811 861401 := bstep (se 2 (by rfl) ⟨323025, by rfl⟩ : syracuseStep 861401 = 646051) B646051
theorem B1287449 : Blo 570811 1287449 := bstep (se 2 (by rfl) ⟨482793, by rfl⟩ : syracuseStep 1287449 = 965587) B965587
theorem B861515 : Blo 570811 861515 := bstep (se 1 (by rfl) ⟨646136, by rfl⟩ : syracuseStep 861515 = 1292273) B1292273
theorem B861527 : Blo 570811 861527 := bstep (se 1 (by rfl) ⟨646145, by rfl⟩ : syracuseStep 861527 = 1292291) B1292291
theorem B1090903 : Blo 570811 1090903 := bstep (se 1 (by rfl) ⟨818177, by rfl⟩ : syracuseStep 1090903 = 1636355) B1636355
theorem B1287539 : Blo 570811 1287539 := bstep (se 1 (by rfl) ⟨965654, by rfl⟩ : syracuseStep 1287539 = 1931309) B1931309
theorem B1287575 : Blo 570811 1287575 := bstep (se 1 (by rfl) ⟨965681, by rfl⟩ : syracuseStep 1287575 = 1931363) B1931363
theorem B861593 : Blo 570811 861593 := bstep (se 2 (by rfl) ⟨323097, by rfl⟩ : syracuseStep 861593 = 646195) B646195
theorem B1091009 : Blo 570811 1091009 := bstep (se 2 (by rfl) ⟨409128, by rfl⟩ : syracuseStep 1091009 = 818257) B818257
theorem B861707 : Blo 570811 861707 := bstep (se 1 (by rfl) ⟨646280, by rfl⟩ : syracuseStep 861707 = 1292561) B1292561
theorem B861719 : Blo 570811 861719 := bstep (se 1 (by rfl) ⟨646289, by rfl⟩ : syracuseStep 861719 = 1292579) B1292579
theorem B1287755 : Blo 570811 1287755 := bstep (se 1 (by rfl) ⟨965816, by rfl⟩ : syracuseStep 1287755 = 1931633) B1931633
theorem B861785 : Blo 570811 861785 := bstep (se 2 (by rfl) ⟨323169, by rfl⟩ : syracuseStep 861785 = 646339) B646339
theorem B1091161 : Blo 570811 1091161 := bstep (se 2 (by rfl) ⟨409185, by rfl⟩ : syracuseStep 1091161 = 818371) B818371
theorem B1287809 : Blo 570811 1287809 := bstep (se 2 (by rfl) ⟨482928, by rfl⟩ : syracuseStep 1287809 = 965857) B965857
theorem B3253891 : Blo 570811 3253891 := bstep (se 1 (by rfl) ⟨2440418, by rfl⟩ : syracuseStep 3253891 = 4880837) B4880837
theorem B861899 : Blo 570811 861899 := bstep (se 1 (by rfl) ⟨646424, by rfl⟩ : syracuseStep 861899 = 1292849) B1292849
theorem B861911 : Blo 570811 861911 := bstep (se 1 (by rfl) ⟨646433, by rfl⟩ : syracuseStep 861911 = 1292867) B1292867
theorem B2238211 : Blo 570811 2238211 := bstep (se 1 (by rfl) ⟨1678658, by rfl⟩ : syracuseStep 2238211 = 3357317) B3357317
theorem B861977 : Blo 570811 861977 := bstep (se 2 (by rfl) ⟨323241, by rfl⟩ : syracuseStep 861977 = 646483) B646483
theorem B1222465 : Blo 570811 1222465 := bstep (se 2 (by rfl) ⟨458424, by rfl⟩ : syracuseStep 1222465 = 916849) B916849
theorem B2893643 : Blo 570811 2893643 := bstep (se 1 (by rfl) ⟨2170232, by rfl⟩ : syracuseStep 2893643 = 4340465) B4340465
theorem B1288025 : Blo 570811 1288025 := bstep (se 2 (by rfl) ⟨483009, by rfl⟩ : syracuseStep 1288025 = 966019) B966019
theorem B862091 : Blo 570811 862091 := bstep (se 1 (by rfl) ⟨646568, by rfl⟩ : syracuseStep 862091 = 1293137) B1293137
theorem B862103 : Blo 570811 862103 := bstep (se 1 (by rfl) ⟨646577, by rfl⟩ : syracuseStep 862103 = 1293155) B1293155
theorem B2172845 : Blo 570811 2172845 := bstep (se 3 (by rfl) ⟨407408, by rfl⟩ : syracuseStep 2172845 = 814817) B814817
theorem B1288115 : Blo 570811 1288115 := bstep (se 1 (by rfl) ⟨966086, by rfl⟩ : syracuseStep 1288115 = 1932173) B1932173
theorem B1288151 : Blo 570811 1288151 := bstep (se 1 (by rfl) ⟨966113, by rfl⟩ : syracuseStep 1288151 = 1932227) B1932227
theorem B1746905 : Blo 570811 1746905 := bstep (se 2 (by rfl) ⟨655089, by rfl⟩ : syracuseStep 1746905 = 1310179) B1310179
theorem B862169 : Blo 570811 862169 := bstep (se 2 (by rfl) ⟨323313, by rfl⟩ : syracuseStep 862169 = 646627) B646627
theorem B1452107 : Blo 570811 1452107 := bstep (se 1 (by rfl) ⟨1089080, by rfl⟩ : syracuseStep 1452107 = 2178161) B2178161
theorem B1288331 : Blo 570811 1288331 := bstep (se 1 (by rfl) ⟨966248, by rfl⟩ : syracuseStep 1288331 = 1932497) B1932497
theorem B1288385 : Blo 570811 1288385 := bstep (se 2 (by rfl) ⟨483144, by rfl⟩ : syracuseStep 1288385 = 966289) B966289
theorem B1288601 : Blo 570811 1288601 := bstep (se 2 (by rfl) ⟨483225, by rfl⟩ : syracuseStep 1288601 = 966451) B966451
theorem B1288691 : Blo 570811 1288691 := bstep (se 1 (by rfl) ⟨966518, by rfl⟩ : syracuseStep 1288691 = 1933037) B1933037
theorem B1288727 : Blo 570811 1288727 := bstep (se 1 (by rfl) ⟨966545, by rfl⟩ : syracuseStep 1288727 = 1933091) B1933091
theorem B3254849 : Blo 570811 3254849 := bstep (se 2 (by rfl) ⟨1220568, by rfl⟩ : syracuseStep 3254849 = 2441137) B2441137
theorem B1288907 : Blo 570811 1288907 := bstep (se 1 (by rfl) ⟨966680, by rfl⟩ : syracuseStep 1288907 = 1933361) B1933361
theorem B1288961 : Blo 570811 1288961 := bstep (se 2 (by rfl) ⟨483360, by rfl⟩ : syracuseStep 1288961 = 966721) B966721
theorem B1289177 : Blo 570811 1289177 := bstep (se 2 (by rfl) ⟨483441, by rfl⟩ : syracuseStep 1289177 = 966883) B966883
theorem B1453079 : Blo 570811 1453079 := bstep (se 1 (by rfl) ⟨1089809, by rfl⟩ : syracuseStep 1453079 = 2179619) B2179619
theorem B1289267 : Blo 570811 1289267 := bstep (se 1 (by rfl) ⟨966950, by rfl⟩ : syracuseStep 1289267 = 1933901) B1933901
theorem B1289303 : Blo 570811 1289303 := bstep (se 1 (by rfl) ⟨966977, by rfl⟩ : syracuseStep 1289303 = 1933955) B1933955
theorem B1289483 : Blo 570811 1289483 := bstep (se 1 (by rfl) ⟨967112, by rfl⟩ : syracuseStep 1289483 = 1934225) B1934225
theorem B2174273 : Blo 570811 2174273 := bstep (se 2 (by rfl) ⟨815352, by rfl⟩ : syracuseStep 2174273 = 1630705) B1630705
theorem B1289537 : Blo 570811 1289537 := bstep (se 2 (by rfl) ⟨483576, by rfl⟩ : syracuseStep 1289537 = 967153) B967153
theorem B1158475 : Blo 570811 1158475 := bstep (se 1 (by rfl) ⟨868856, by rfl⟩ : syracuseStep 1158475 = 1737713) B1737713
theorem B1289753 : Blo 570811 1289753 := bstep (se 2 (by rfl) ⟨483657, by rfl⟩ : syracuseStep 1289753 = 967315) B967315
theorem B2895425 : Blo 570811 2895425 := bstep (se 2 (by rfl) ⟨1085784, by rfl⟩ : syracuseStep 2895425 = 2171569) B2171569
theorem B1289843 : Blo 570811 1289843 := bstep (se 1 (by rfl) ⟨967382, by rfl⟩ : syracuseStep 1289843 = 1934765) B1934765
theorem B1289879 : Blo 570811 1289879 := bstep (se 1 (by rfl) ⟨967409, by rfl⟩ : syracuseStep 1289879 = 1934819) B1934819
theorem B1224371 : Blo 570811 1224371 := bstep (se 1 (by rfl) ⟨918278, by rfl⟩ : syracuseStep 1224371 = 1836557) B1836557
theorem B1453747 : Blo 570811 1453747 := bstep (se 1 (by rfl) ⟨1090310, by rfl⟩ : syracuseStep 1453747 = 2180621) B2180621
theorem B1453889 : Blo 570811 1453889 := bstep (se 2 (by rfl) ⟨545208, by rfl⟩ : syracuseStep 1453889 = 1090417) B1090417
theorem B1290059 : Blo 570811 1290059 := bstep (se 1 (by rfl) ⟨967544, by rfl⟩ : syracuseStep 1290059 = 1935089) B1935089
theorem B1290113 : Blo 570811 1290113 := bstep (se 2 (by rfl) ⟨483792, by rfl⟩ : syracuseStep 1290113 = 967585) B967585
theorem B1552459 : Blo 570811 1552459 := bstep (se 1 (by rfl) ⟨1164344, by rfl⟩ : syracuseStep 1552459 = 2328689) B2328689
theorem B1290329 : Blo 570811 1290329 := bstep (se 2 (by rfl) ⟨483873, by rfl⟩ : syracuseStep 1290329 = 967747) B967747
theorem B1224857 : Blo 570811 1224857 := bstep (se 2 (by rfl) ⟨459321, by rfl⟩ : syracuseStep 1224857 = 918643) B918643
theorem B1290419 : Blo 570811 1290419 := bstep (se 1 (by rfl) ⟨967814, by rfl⟩ : syracuseStep 1290419 = 1935629) B1935629
theorem B1290455 : Blo 570811 1290455 := bstep (se 1 (by rfl) ⟨967841, by rfl⟩ : syracuseStep 1290455 = 1935683) B1935683
theorem B10170689 : Blo 570811 10170689 := bstep (se 2 (by rfl) ⟨3814008, by rfl⟩ : syracuseStep 10170689 = 7628017) B7628017
theorem B1290635 : Blo 570811 1290635 := bstep (se 1 (by rfl) ⟨967976, by rfl⟩ : syracuseStep 1290635 = 1935953) B1935953
theorem B1290689 : Blo 570811 1290689 := bstep (se 2 (by rfl) ⟨484008, by rfl⟩ : syracuseStep 1290689 = 968017) B968017
theorem B1290905 : Blo 570811 1290905 := bstep (se 2 (by rfl) ⟨484089, by rfl⟩ : syracuseStep 1290905 = 968179) B968179
theorem B1290995 : Blo 570811 1290995 := bstep (se 1 (by rfl) ⟨968246, by rfl⟩ : syracuseStep 1290995 = 1936493) B1936493
theorem B2175761 : Blo 570811 2175761 := bstep (se 2 (by rfl) ⟨815910, by rfl⟩ : syracuseStep 2175761 = 1631821) B1631821
theorem B1291031 : Blo 570811 1291031 := bstep (se 1 (by rfl) ⟨968273, by rfl⟩ : syracuseStep 1291031 = 1936547) B1936547
theorem B963353 : Blo 570811 963353 := bstep (se 2 (by rfl) ⟨361257, by rfl⟩ : syracuseStep 963353 = 722515) B722515
theorem B5223203 : Blo 570811 5223203 := bstep (se 1 (by rfl) ⟨3917402, by rfl⟩ : syracuseStep 5223203 = 7834805) B7834805
theorem B1225601 : Blo 570811 1225601 := bstep (se 2 (by rfl) ⟨459600, by rfl⟩ : syracuseStep 1225601 = 919201) B919201
theorem B963481 : Blo 570811 963481 := bstep (se 2 (by rfl) ⟨361305, by rfl⟩ : syracuseStep 963481 = 722611) B722611
theorem B1291211 : Blo 570811 1291211 := bstep (se 1 (by rfl) ⟨968408, by rfl⟩ : syracuseStep 1291211 = 1936817) B1936817
theorem B1291265 : Blo 570811 1291265 := bstep (se 2 (by rfl) ⟨484224, by rfl⟩ : syracuseStep 1291265 = 968449) B968449
theorem B930827 : Blo 570811 930827 := bstep (se 1 (by rfl) ⟨698120, by rfl⟩ : syracuseStep 930827 = 1396241) B1396241
theorem B4174865 : Blo 570811 4174865 := bstep (se 2 (by rfl) ⟨1565574, by rfl⟩ : syracuseStep 4174865 = 3131149) B3131149
theorem B1651915 : Blo 570811 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B2176217 : Blo 570811 2176217 := bstep (se 2 (by rfl) ⟨816081, by rfl⟩ : syracuseStep 2176217 = 1632163) B1632163
theorem B1291481 : Blo 570811 1291481 := bstep (se 2 (by rfl) ⟨484305, by rfl⟩ : syracuseStep 1291481 = 968611) B968611
theorem B1291571 : Blo 570811 1291571 := bstep (se 1 (by rfl) ⟨968678, by rfl⟩ : syracuseStep 1291571 = 1937357) B1937357
theorem B1291607 : Blo 570811 1291607 := bstep (se 1 (by rfl) ⟨968705, by rfl⟩ : syracuseStep 1291607 = 1937411) B1937411
theorem B2176429 : Blo 570811 2176429 := bstep (se 3 (by rfl) ⟨408080, by rfl⟩ : syracuseStep 2176429 = 816161) B816161
theorem B570827 : Blo 570811 570827 := bstep (se 1 (by rfl) ⟨428120, by rfl⟩ : syracuseStep 570827 = 856241) B856241
theorem B570839 : Blo 570811 570839 := bstep (se 1 (by rfl) ⟨428129, by rfl⟩ : syracuseStep 570839 = 856259) B856259
theorem B964055 : Blo 570811 964055 := bstep (se 1 (by rfl) ⟨723041, by rfl⟩ : syracuseStep 964055 = 1446083) B1446083
theorem B2897369 : Blo 570811 2897369 := bstep (se 2 (by rfl) ⟨1086513, by rfl⟩ : syracuseStep 2897369 = 2173027) B2173027
theorem B1160663 : Blo 570811 1160663 := bstep (se 1 (by rfl) ⟨870497, by rfl⟩ : syracuseStep 1160663 = 1740995) B1740995
theorem B570859 : Blo 570811 570859 := bstep (se 1 (by rfl) ⟨428144, by rfl⟩ : syracuseStep 570859 = 856289) B856289
theorem B570871 : Blo 570811 570871 := bstep (se 1 (by rfl) ⟨428153, by rfl⟩ : syracuseStep 570871 = 856307) B856307
theorem B570891 : Blo 570811 570891 := bstep (se 1 (by rfl) ⟨428168, by rfl⟩ : syracuseStep 570891 = 856337) B856337
theorem B1291787 : Blo 570811 1291787 := bstep (se 1 (by rfl) ⟨968840, by rfl⟩ : syracuseStep 1291787 = 1937681) B1937681
theorem B570903 : Blo 570811 570903 := bstep (se 1 (by rfl) ⟨428177, by rfl⟩ : syracuseStep 570903 = 856355) B856355
theorem B570923 : Blo 570811 570923 := bstep (se 1 (by rfl) ⟨428192, by rfl⟩ : syracuseStep 570923 = 856385) B856385
theorem B570935 : Blo 570811 570935 := bstep (se 1 (by rfl) ⟨428201, by rfl⟩ : syracuseStep 570935 = 856403) B856403
theorem B1291841 : Blo 570811 1291841 := bstep (se 2 (by rfl) ⟨484440, by rfl⟩ : syracuseStep 1291841 = 968881) B968881
theorem B4142657 : Blo 570811 4142657 := bstep (se 2 (by rfl) ⟨1553496, by rfl⟩ : syracuseStep 4142657 = 3106993) B3106993
theorem B570955 : Blo 570811 570955 := bstep (se 1 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 570955 = 856433) B856433
theorem B570967 : Blo 570811 570967 := bstep (se 1 (by rfl) ⟨428225, by rfl⟩ : syracuseStep 570967 = 856451) B856451
theorem B964183 : Blo 570811 964183 := bstep (se 1 (by rfl) ⟨723137, by rfl⟩ : syracuseStep 964183 = 1446275) B1446275
theorem B1029719 : Blo 570811 1029719 := bstep (se 1 (by rfl) ⟨772289, by rfl⟩ : syracuseStep 1029719 = 1544579) B1544579
theorem B570987 : Blo 570811 570987 := bstep (se 1 (by rfl) ⟨428240, by rfl⟩ : syracuseStep 570987 = 856481) B856481
theorem B570999 : Blo 570811 570999 := bstep (se 1 (by rfl) ⟨428249, by rfl⟩ : syracuseStep 570999 = 856499) B856499
theorem B11941507 : Blo 570811 11941507 := bstep (se 1 (by rfl) ⟨8956130, by rfl⟩ : syracuseStep 11941507 = 17912261) B17912261
theorem B571019 : Blo 570811 571019 := bstep (se 1 (by rfl) ⟨428264, by rfl⟩ : syracuseStep 571019 = 856529) B856529
theorem B571031 : Blo 570811 571031 := bstep (se 1 (by rfl) ⟨428273, by rfl⟩ : syracuseStep 571031 = 856547) B856547
theorem B571051 : Blo 570811 571051 := bstep (se 1 (by rfl) ⟨428288, by rfl⟩ : syracuseStep 571051 = 856577) B856577
theorem B571063 : Blo 570811 571063 := bstep (se 1 (by rfl) ⟨428297, by rfl⟩ : syracuseStep 571063 = 856595) B856595
theorem B571083 : Blo 570811 571083 := bstep (se 1 (by rfl) ⟨428312, by rfl⟩ : syracuseStep 571083 = 856625) B856625
theorem B7354061 : Blo 570811 7354061 := bstep (se 3 (by rfl) ⟨1378886, by rfl⟩ : syracuseStep 7354061 = 2757773) B2757773
theorem B571095 : Blo 570811 571095 := bstep (se 1 (by rfl) ⟨428321, by rfl⟩ : syracuseStep 571095 = 856643) B856643
theorem B2176733 : Blo 570811 2176733 := bstep (se 3 (by rfl) ⟨408137, by rfl⟩ : syracuseStep 2176733 = 816275) B816275
theorem B571115 : Blo 570811 571115 := bstep (se 1 (by rfl) ⟨428336, by rfl⟩ : syracuseStep 571115 = 856673) B856673
theorem B571127 : Blo 570811 571127 := bstep (se 1 (by rfl) ⟨428345, by rfl⟩ : syracuseStep 571127 = 856691) B856691
theorem B1226497 : Blo 570811 1226497 := bstep (se 2 (by rfl) ⟨459936, by rfl⟩ : syracuseStep 1226497 = 919873) B919873
theorem B571147 : Blo 570811 571147 := bstep (se 1 (by rfl) ⟨428360, by rfl⟩ : syracuseStep 571147 = 856721) B856721
theorem B571159 : Blo 570811 571159 := bstep (se 1 (by rfl) ⟨428369, by rfl⟩ : syracuseStep 571159 = 856739) B856739
theorem B1292057 : Blo 570811 1292057 := bstep (se 2 (by rfl) ⟨484521, by rfl⟩ : syracuseStep 1292057 = 969043) B969043
theorem B571179 : Blo 570811 571179 := bstep (se 1 (by rfl) ⟨428384, by rfl⟩ : syracuseStep 571179 = 856769) B856769
theorem B4896557 : Blo 570811 4896557 := bstep (se 3 (by rfl) ⟨918104, by rfl⟩ : syracuseStep 4896557 = 1836209) B1836209
theorem B571191 : Blo 570811 571191 := bstep (se 1 (by rfl) ⟨428393, by rfl⟩ : syracuseStep 571191 = 856787) B856787
theorem B571211 : Blo 570811 571211 := bstep (se 1 (by rfl) ⟨428408, by rfl⟩ : syracuseStep 571211 = 856817) B856817
theorem B571223 : Blo 570811 571223 := bstep (se 1 (by rfl) ⟨428417, by rfl⟩ : syracuseStep 571223 = 856835) B856835
theorem B571243 : Blo 570811 571243 := bstep (se 1 (by rfl) ⟨428432, by rfl⟩ : syracuseStep 571243 = 856865) B856865
theorem B1292147 : Blo 570811 1292147 := bstep (se 1 (by rfl) ⟨969110, by rfl⟩ : syracuseStep 1292147 = 1938221) B1938221
theorem B571255 : Blo 570811 571255 := bstep (se 1 (by rfl) ⟨428441, by rfl⟩ : syracuseStep 571255 = 856883) B856883
theorem B571275 : Blo 570811 571275 := bstep (se 1 (by rfl) ⟨428456, by rfl⟩ : syracuseStep 571275 = 856913) B856913
theorem B571287 : Blo 570811 571287 := bstep (se 1 (by rfl) ⟨428465, by rfl⟩ : syracuseStep 571287 = 856931) B856931
theorem B1292183 : Blo 570811 1292183 := bstep (se 1 (by rfl) ⟨969137, by rfl⟩ : syracuseStep 1292183 = 1938275) B1938275
theorem B571307 : Blo 570811 571307 := bstep (se 1 (by rfl) ⟨428480, by rfl⟩ : syracuseStep 571307 = 856961) B856961
theorem B571319 : Blo 570811 571319 := bstep (se 1 (by rfl) ⟨428489, by rfl⟩ : syracuseStep 571319 = 856979) B856979
theorem B571339 : Blo 570811 571339 := bstep (se 1 (by rfl) ⟨428504, by rfl⟩ : syracuseStep 571339 = 857009) B857009
theorem B571351 : Blo 570811 571351 := bstep (se 1 (by rfl) ⟨428513, by rfl⟩ : syracuseStep 571351 = 857027) B857027
theorem B3356633 : Blo 570811 3356633 := bstep (se 2 (by rfl) ⟨1258737, by rfl⟩ : syracuseStep 3356633 = 2517475) B2517475
theorem B571371 : Blo 570811 571371 := bstep (se 1 (by rfl) ⟨428528, by rfl⟩ : syracuseStep 571371 = 857057) B857057
theorem B571383 : Blo 570811 571383 := bstep (se 1 (by rfl) ⟨428537, by rfl⟩ : syracuseStep 571383 = 857075) B857075
theorem B571403 : Blo 570811 571403 := bstep (se 1 (by rfl) ⟨428552, by rfl⟩ : syracuseStep 571403 = 857105) B857105
theorem B571415 : Blo 570811 571415 := bstep (se 1 (by rfl) ⟨428561, by rfl⟩ : syracuseStep 571415 = 857123) B857123
theorem B571435 : Blo 570811 571435 := bstep (se 1 (by rfl) ⟨428576, by rfl⟩ : syracuseStep 571435 = 857153) B857153
theorem B571447 : Blo 570811 571447 := bstep (se 1 (by rfl) ⟨428585, by rfl⟩ : syracuseStep 571447 = 857171) B857171
theorem B571467 : Blo 570811 571467 := bstep (se 1 (by rfl) ⟨428600, by rfl⟩ : syracuseStep 571467 = 857201) B857201
theorem B1292363 : Blo 570811 1292363 := bstep (se 1 (by rfl) ⟨969272, by rfl⟩ : syracuseStep 1292363 = 1938545) B1938545
theorem B571479 : Blo 570811 571479 := bstep (se 1 (by rfl) ⟨428609, by rfl⟩ : syracuseStep 571479 = 857219) B857219
theorem B1226839 : Blo 570811 1226839 := bstep (se 1 (by rfl) ⟨920129, by rfl⟩ : syracuseStep 1226839 = 1840259) B1840259
theorem B571499 : Blo 570811 571499 := bstep (se 1 (by rfl) ⟨428624, by rfl⟩ : syracuseStep 571499 = 857249) B857249
theorem B571511 : Blo 570811 571511 := bstep (se 1 (by rfl) ⟨428633, by rfl⟩ : syracuseStep 571511 = 857267) B857267
theorem B1292417 : Blo 570811 1292417 := bstep (se 2 (by rfl) ⟨484656, by rfl⟩ : syracuseStep 1292417 = 969313) B969313
theorem B571531 : Blo 570811 571531 := bstep (se 1 (by rfl) ⟨428648, by rfl⟩ : syracuseStep 571531 = 857297) B857297
theorem B571543 : Blo 570811 571543 := bstep (se 1 (by rfl) ⟨428657, by rfl⟩ : syracuseStep 571543 = 857315) B857315
theorem B2209943 : Blo 570811 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B571563 : Blo 570811 571563 := bstep (se 1 (by rfl) ⟨428672, by rfl⟩ : syracuseStep 571563 = 857345) B857345
theorem B571575 : Blo 570811 571575 := bstep (se 1 (by rfl) ⟨428681, by rfl⟩ : syracuseStep 571575 = 857363) B857363
theorem B571595 : Blo 570811 571595 := bstep (se 1 (by rfl) ⟨428696, by rfl⟩ : syracuseStep 571595 = 857393) B857393
theorem B964811 : Blo 570811 964811 := bstep (se 1 (by rfl) ⟨723608, by rfl⟩ : syracuseStep 964811 = 1447217) B1447217
theorem B571607 : Blo 570811 571607 := bstep (se 1 (by rfl) ⟨428705, by rfl⟩ : syracuseStep 571607 = 857411) B857411
theorem B571627 : Blo 570811 571627 := bstep (se 1 (by rfl) ⟨428720, by rfl⟩ : syracuseStep 571627 = 857441) B857441
theorem B571639 : Blo 570811 571639 := bstep (se 1 (by rfl) ⟨428729, by rfl⟩ : syracuseStep 571639 = 857459) B857459
theorem B571659 : Blo 570811 571659 := bstep (se 1 (by rfl) ⟨428744, by rfl⟩ : syracuseStep 571659 = 857489) B857489
theorem B1030411 : Blo 570811 1030411 := bstep (se 1 (by rfl) ⟨772808, by rfl⟩ : syracuseStep 1030411 = 1545617) B1545617
theorem B571671 : Blo 570811 571671 := bstep (se 1 (by rfl) ⟨428753, by rfl⟩ : syracuseStep 571671 = 857507) B857507
theorem B571691 : Blo 570811 571691 := bstep (se 1 (by rfl) ⟨428768, by rfl⟩ : syracuseStep 571691 = 857537) B857537
theorem B571703 : Blo 570811 571703 := bstep (se 1 (by rfl) ⟨428777, by rfl⟩ : syracuseStep 571703 = 857555) B857555
theorem B571723 : Blo 570811 571723 := bstep (se 1 (by rfl) ⟨428792, by rfl⟩ : syracuseStep 571723 = 857585) B857585
theorem B964939 : Blo 570811 964939 := bstep (se 1 (by rfl) ⟨723704, by rfl⟩ : syracuseStep 964939 = 1447409) B1447409
theorem B571735 : Blo 570811 571735 := bstep (se 1 (by rfl) ⟨428801, by rfl⟩ : syracuseStep 571735 = 857603) B857603
theorem B1292633 : Blo 570811 1292633 := bstep (se 2 (by rfl) ⟨484737, by rfl⟩ : syracuseStep 1292633 = 969475) B969475
theorem B571755 : Blo 570811 571755 := bstep (se 1 (by rfl) ⟨428816, by rfl⟩ : syracuseStep 571755 = 857633) B857633
theorem B571767 : Blo 570811 571767 := bstep (se 1 (by rfl) ⟨428825, by rfl⟩ : syracuseStep 571767 = 857651) B857651
theorem B571787 : Blo 570811 571787 := bstep (se 1 (by rfl) ⟨428840, by rfl⟩ : syracuseStep 571787 = 857681) B857681
theorem B571799 : Blo 570811 571799 := bstep (se 1 (by rfl) ⟨428849, by rfl⟩ : syracuseStep 571799 = 857699) B857699
theorem B571819 : Blo 570811 571819 := bstep (se 1 (by rfl) ⟨428864, by rfl⟩ : syracuseStep 571819 = 857729) B857729
theorem B1292723 : Blo 570811 1292723 := bstep (se 1 (by rfl) ⟨969542, by rfl⟩ : syracuseStep 1292723 = 1939085) B1939085
theorem B571831 : Blo 570811 571831 := bstep (se 1 (by rfl) ⟨428873, by rfl⟩ : syracuseStep 571831 = 857747) B857747
theorem B571851 : Blo 570811 571851 := bstep (se 1 (by rfl) ⟨428888, by rfl⟩ : syracuseStep 571851 = 857777) B857777
theorem B571863 : Blo 570811 571863 := bstep (se 1 (by rfl) ⟨428897, by rfl⟩ : syracuseStep 571863 = 857795) B857795
theorem B1292759 : Blo 570811 1292759 := bstep (se 1 (by rfl) ⟨969569, by rfl⟩ : syracuseStep 1292759 = 1939139) B1939139
theorem B965081 : Blo 570811 965081 := bstep (se 2 (by rfl) ⟨361905, by rfl⟩ : syracuseStep 965081 = 723811) B723811
theorem B571883 : Blo 570811 571883 := bstep (se 1 (by rfl) ⟨428912, by rfl⟩ : syracuseStep 571883 = 857825) B857825
theorem B571895 : Blo 570811 571895 := bstep (se 1 (by rfl) ⟨428921, by rfl⟩ : syracuseStep 571895 = 857843) B857843
theorem B571915 : Blo 570811 571915 := bstep (se 1 (by rfl) ⟨428936, by rfl⟩ : syracuseStep 571915 = 857873) B857873
theorem B571927 : Blo 570811 571927 := bstep (se 1 (by rfl) ⟨428945, by rfl⟩ : syracuseStep 571927 = 857891) B857891
theorem B571947 : Blo 570811 571947 := bstep (se 1 (by rfl) ⟨428960, by rfl⟩ : syracuseStep 571947 = 857921) B857921
theorem B571959 : Blo 570811 571959 := bstep (se 1 (by rfl) ⟨428969, by rfl⟩ : syracuseStep 571959 = 857939) B857939
theorem B571979 : Blo 570811 571979 := bstep (se 1 (by rfl) ⟨428984, by rfl⟩ : syracuseStep 571979 = 857969) B857969
theorem B571991 : Blo 570811 571991 := bstep (se 1 (by rfl) ⟨428993, by rfl⟩ : syracuseStep 571991 = 857987) B857987
theorem B965209 : Blo 570811 965209 := bstep (se 2 (by rfl) ⟨361953, by rfl⟩ : syracuseStep 965209 = 723907) B723907
theorem B572011 : Blo 570811 572011 := bstep (se 1 (by rfl) ⟨429008, by rfl⟩ : syracuseStep 572011 = 858017) B858017
theorem B572023 : Blo 570811 572023 := bstep (se 1 (by rfl) ⟨429017, by rfl⟩ : syracuseStep 572023 = 858035) B858035
theorem B572043 : Blo 570811 572043 := bstep (se 1 (by rfl) ⟨429032, by rfl⟩ : syracuseStep 572043 = 858065) B858065
theorem B1292939 : Blo 570811 1292939 := bstep (se 1 (by rfl) ⟨969704, by rfl⟩ : syracuseStep 1292939 = 1939409) B1939409
theorem B1227403 : Blo 570811 1227403 := bstep (se 1 (by rfl) ⟨920552, by rfl⟩ : syracuseStep 1227403 = 1841105) B1841105
theorem B572055 : Blo 570811 572055 := bstep (se 1 (by rfl) ⟨429041, by rfl⟩ : syracuseStep 572055 = 858083) B858083
theorem B572075 : Blo 570811 572075 := bstep (se 1 (by rfl) ⟨429056, by rfl⟩ : syracuseStep 572075 = 858113) B858113
theorem B572087 : Blo 570811 572087 := bstep (se 1 (by rfl) ⟨429065, by rfl⟩ : syracuseStep 572087 = 858131) B858131
theorem B1292993 : Blo 570811 1292993 := bstep (se 2 (by rfl) ⟨484872, by rfl⟩ : syracuseStep 1292993 = 969745) B969745
theorem B572107 : Blo 570811 572107 := bstep (se 1 (by rfl) ⟨429080, by rfl⟩ : syracuseStep 572107 = 858161) B858161
theorem B572119 : Blo 570811 572119 := bstep (se 1 (by rfl) ⟨429089, by rfl⟩ : syracuseStep 572119 = 858179) B858179
theorem B572139 : Blo 570811 572139 := bstep (se 1 (by rfl) ⟨429104, by rfl⟩ : syracuseStep 572139 = 858209) B858209
theorem B572151 : Blo 570811 572151 := bstep (se 1 (by rfl) ⟨429113, by rfl⟩ : syracuseStep 572151 = 858227) B858227
theorem B572171 : Blo 570811 572171 := bstep (se 1 (by rfl) ⟨429128, by rfl⟩ : syracuseStep 572171 = 858257) B858257
theorem B572183 : Blo 570811 572183 := bstep (se 1 (by rfl) ⟨429137, by rfl⟩ : syracuseStep 572183 = 858275) B858275
theorem B572203 : Blo 570811 572203 := bstep (se 1 (by rfl) ⟨429152, by rfl⟩ : syracuseStep 572203 = 858305) B858305
theorem B1391411 : Blo 570811 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B572215 : Blo 570811 572215 := bstep (se 1 (by rfl) ⟨429161, by rfl⟩ : syracuseStep 572215 = 858323) B858323
theorem B572235 : Blo 570811 572235 := bstep (se 1 (by rfl) ⟨429176, by rfl⟩ : syracuseStep 572235 = 858353) B858353
theorem B572247 : Blo 570811 572247 := bstep (se 1 (by rfl) ⟨429185, by rfl⟩ : syracuseStep 572247 = 858371) B858371
theorem B572267 : Blo 570811 572267 := bstep (se 1 (by rfl) ⟨429200, by rfl⟩ : syracuseStep 572267 = 858401) B858401
theorem B572279 : Blo 570811 572279 := bstep (se 1 (by rfl) ⟨429209, by rfl⟩ : syracuseStep 572279 = 858419) B858419
theorem B1031051 : Blo 570811 1031051 := bstep (se 1 (by rfl) ⟨773288, by rfl⟩ : syracuseStep 1031051 = 1546577) B1546577
theorem B572299 : Blo 570811 572299 := bstep (se 1 (by rfl) ⟨429224, by rfl⟩ : syracuseStep 572299 = 858449) B858449
theorem B572311 : Blo 570811 572311 := bstep (se 1 (by rfl) ⟨429233, by rfl⟩ : syracuseStep 572311 = 858467) B858467
theorem B1293209 : Blo 570811 1293209 := bstep (se 2 (by rfl) ⟨484953, by rfl⟩ : syracuseStep 1293209 = 969907) B969907
theorem B572331 : Blo 570811 572331 := bstep (se 1 (by rfl) ⟨429248, by rfl⟩ : syracuseStep 572331 = 858497) B858497
theorem B572343 : Blo 570811 572343 := bstep (se 1 (by rfl) ⟨429257, by rfl⟩ : syracuseStep 572343 = 858515) B858515
theorem B572363 : Blo 570811 572363 := bstep (se 1 (by rfl) ⟨429272, by rfl⟩ : syracuseStep 572363 = 858545) B858545
theorem B572375 : Blo 570811 572375 := bstep (se 1 (by rfl) ⟨429281, by rfl⟩ : syracuseStep 572375 = 858563) B858563
theorem B572395 : Blo 570811 572395 := bstep (se 1 (by rfl) ⟨429296, by rfl⟩ : syracuseStep 572395 = 858593) B858593
theorem B1293299 : Blo 570811 1293299 := bstep (se 1 (by rfl) ⟨969974, by rfl⟩ : syracuseStep 1293299 = 1939949) B1939949
theorem B572407 : Blo 570811 572407 := bstep (se 1 (by rfl) ⟨429305, by rfl⟩ : syracuseStep 572407 = 858611) B858611
theorem B572427 : Blo 570811 572427 := bstep (se 1 (by rfl) ⟨429320, by rfl⟩ : syracuseStep 572427 = 858641) B858641
theorem B572439 : Blo 570811 572439 := bstep (se 1 (by rfl) ⟨429329, by rfl⟩ : syracuseStep 572439 = 858659) B858659
theorem B572459 : Blo 570811 572459 := bstep (se 1 (by rfl) ⟨429344, by rfl⟩ : syracuseStep 572459 = 858689) B858689
theorem B2898989 : Blo 570811 2898989 := bstep (se 3 (by rfl) ⟨543560, by rfl⟩ : syracuseStep 2898989 = 1087121) B1087121
theorem B572471 : Blo 570811 572471 := bstep (se 1 (by rfl) ⟨429353, by rfl⟩ : syracuseStep 572471 = 858707) B858707
theorem B572491 : Blo 570811 572491 := bstep (se 1 (by rfl) ⟨429368, by rfl⟩ : syracuseStep 572491 = 858737) B858737
theorem B572503 : Blo 570811 572503 := bstep (se 1 (by rfl) ⟨429377, by rfl⟩ : syracuseStep 572503 = 858755) B858755
theorem B572523 : Blo 570811 572523 := bstep (se 1 (by rfl) ⟨429392, by rfl⟩ : syracuseStep 572523 = 858785) B858785
theorem B572535 : Blo 570811 572535 := bstep (se 1 (by rfl) ⟨429401, by rfl⟩ : syracuseStep 572535 = 858803) B858803
theorem B572555 : Blo 570811 572555 := bstep (se 1 (by rfl) ⟨429416, by rfl⟩ : syracuseStep 572555 = 858833) B858833
theorem B965783 : Blo 570811 965783 := bstep (se 1 (by rfl) ⟨724337, by rfl⟩ : syracuseStep 965783 = 1448675) B1448675
theorem B572567 : Blo 570811 572567 := bstep (se 1 (by rfl) ⟨429425, by rfl⟩ : syracuseStep 572567 = 858851) B858851
theorem B572587 : Blo 570811 572587 := bstep (se 1 (by rfl) ⟨429440, by rfl⟩ : syracuseStep 572587 = 858881) B858881
theorem B572599 : Blo 570811 572599 := bstep (se 1 (by rfl) ⟨429449, by rfl⟩ : syracuseStep 572599 = 858899) B858899
theorem B572619 : Blo 570811 572619 := bstep (se 1 (by rfl) ⟨429464, by rfl⟩ : syracuseStep 572619 = 858929) B858929
theorem B572631 : Blo 570811 572631 := bstep (se 1 (by rfl) ⟨429473, by rfl⟩ : syracuseStep 572631 = 858947) B858947
theorem B572651 : Blo 570811 572651 := bstep (se 1 (by rfl) ⟨429488, by rfl⟩ : syracuseStep 572651 = 858977) B858977
theorem B572663 : Blo 570811 572663 := bstep (se 1 (by rfl) ⟨429497, by rfl⟩ : syracuseStep 572663 = 858995) B858995
theorem B572683 : Blo 570811 572683 := bstep (se 1 (by rfl) ⟨429512, by rfl⟩ : syracuseStep 572683 = 859025) B859025
theorem B965911 : Blo 570811 965911 := bstep (se 1 (by rfl) ⟨724433, by rfl⟩ : syracuseStep 965911 = 1448867) B1448867
theorem B572695 : Blo 570811 572695 := bstep (se 1 (by rfl) ⟨429521, by rfl⟩ : syracuseStep 572695 = 859043) B859043
theorem B572715 : Blo 570811 572715 := bstep (se 1 (by rfl) ⟨429536, by rfl⟩ : syracuseStep 572715 = 859073) B859073
theorem B572727 : Blo 570811 572727 := bstep (se 1 (by rfl) ⟨429545, by rfl⟩ : syracuseStep 572727 = 859091) B859091
theorem B3259723 : Blo 570811 3259723 := bstep (se 1 (by rfl) ⟨2444792, by rfl⟩ : syracuseStep 3259723 = 4889585) B4889585
theorem B572747 : Blo 570811 572747 := bstep (se 1 (by rfl) ⟨429560, by rfl⟩ : syracuseStep 572747 = 859121) B859121
theorem B572759 : Blo 570811 572759 := bstep (se 1 (by rfl) ⟨429569, by rfl⟩ : syracuseStep 572759 = 859139) B859139
theorem B572779 : Blo 570811 572779 := bstep (se 1 (by rfl) ⟨429584, by rfl⟩ : syracuseStep 572779 = 859169) B859169
theorem B572791 : Blo 570811 572791 := bstep (se 1 (by rfl) ⟨429593, by rfl⟩ : syracuseStep 572791 = 859187) B859187
theorem B572811 : Blo 570811 572811 := bstep (se 1 (by rfl) ⟨429608, by rfl⟩ : syracuseStep 572811 = 859217) B859217
theorem B572823 : Blo 570811 572823 := bstep (se 1 (by rfl) ⟨429617, by rfl⟩ : syracuseStep 572823 = 859235) B859235
theorem B572843 : Blo 570811 572843 := bstep (se 1 (by rfl) ⟨429632, by rfl⟩ : syracuseStep 572843 = 859265) B859265
theorem B572855 : Blo 570811 572855 := bstep (se 1 (by rfl) ⟨429641, by rfl⟩ : syracuseStep 572855 = 859283) B859283
theorem B572875 : Blo 570811 572875 := bstep (se 1 (by rfl) ⟨429656, by rfl⟩ : syracuseStep 572875 = 859313) B859313
theorem B572887 : Blo 570811 572887 := bstep (se 1 (by rfl) ⟨429665, by rfl⟩ : syracuseStep 572887 = 859331) B859331
theorem B572907 : Blo 570811 572907 := bstep (se 1 (by rfl) ⟨429680, by rfl⟩ : syracuseStep 572907 = 859361) B859361
theorem B572919 : Blo 570811 572919 := bstep (se 1 (by rfl) ⟨429689, by rfl⟩ : syracuseStep 572919 = 859379) B859379
theorem B572939 : Blo 570811 572939 := bstep (se 1 (by rfl) ⟨429704, by rfl⟩ : syracuseStep 572939 = 859409) B859409
theorem B572951 : Blo 570811 572951 := bstep (se 1 (by rfl) ⟨429713, by rfl⟩ : syracuseStep 572951 = 859427) B859427
theorem B572971 : Blo 570811 572971 := bstep (se 1 (by rfl) ⟨429728, by rfl⟩ : syracuseStep 572971 = 859457) B859457
theorem B2604595 : Blo 570811 2604595 := bstep (se 1 (by rfl) ⟨1953446, by rfl⟩ : syracuseStep 2604595 = 3906893) B3906893
theorem B572983 : Blo 570811 572983 := bstep (se 1 (by rfl) ⟨429737, by rfl⟩ : syracuseStep 572983 = 859475) B859475
theorem B573003 : Blo 570811 573003 := bstep (se 1 (by rfl) ⟨429752, by rfl⟩ : syracuseStep 573003 = 859505) B859505
theorem B573015 : Blo 570811 573015 := bstep (se 1 (by rfl) ⟨429761, by rfl⟩ : syracuseStep 573015 = 859523) B859523
theorem B3259997 : Blo 570811 3259997 := bstep (se 3 (by rfl) ⟨611249, by rfl⟩ : syracuseStep 3259997 = 1222499) B1222499
theorem B573035 : Blo 570811 573035 := bstep (se 1 (by rfl) ⟨429776, by rfl⟩ : syracuseStep 573035 = 859553) B859553
theorem B1031795 : Blo 570811 1031795 := bstep (se 1 (by rfl) ⟨773846, by rfl⟩ : syracuseStep 1031795 = 1547693) B1547693
theorem B573047 : Blo 570811 573047 := bstep (se 1 (by rfl) ⟨429785, by rfl⟩ : syracuseStep 573047 = 859571) B859571
theorem B573067 : Blo 570811 573067 := bstep (se 1 (by rfl) ⟨429800, by rfl⟩ : syracuseStep 573067 = 859601) B859601
theorem B573079 : Blo 570811 573079 := bstep (se 1 (by rfl) ⟨429809, by rfl⟩ : syracuseStep 573079 = 859619) B859619
theorem B573099 : Blo 570811 573099 := bstep (se 1 (by rfl) ⟨429824, by rfl⟩ : syracuseStep 573099 = 859649) B859649
theorem B573111 : Blo 570811 573111 := bstep (se 1 (by rfl) ⟨429833, by rfl⟩ : syracuseStep 573111 = 859667) B859667
theorem B573131 : Blo 570811 573131 := bstep (se 1 (by rfl) ⟨429848, by rfl⟩ : syracuseStep 573131 = 859697) B859697
theorem B573143 : Blo 570811 573143 := bstep (se 1 (by rfl) ⟨429857, by rfl⟩ : syracuseStep 573143 = 859715) B859715
theorem B2211545 : Blo 570811 2211545 := bstep (se 2 (by rfl) ⟨829329, by rfl⟩ : syracuseStep 2211545 = 1658659) B1658659
theorem B573163 : Blo 570811 573163 := bstep (se 1 (by rfl) ⟨429872, by rfl⟩ : syracuseStep 573163 = 859745) B859745
theorem B573175 : Blo 570811 573175 := bstep (se 1 (by rfl) ⟨429881, by rfl⟩ : syracuseStep 573175 = 859763) B859763
theorem B573195 : Blo 570811 573195 := bstep (se 1 (by rfl) ⟨429896, by rfl⟩ : syracuseStep 573195 = 859793) B859793
theorem B573207 : Blo 570811 573207 := bstep (se 1 (by rfl) ⟨429905, by rfl⟩ : syracuseStep 573207 = 859811) B859811
theorem B573227 : Blo 570811 573227 := bstep (se 1 (by rfl) ⟨429920, by rfl⟩ : syracuseStep 573227 = 859841) B859841
theorem B3489581 : Blo 570811 3489581 := bstep (se 3 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 3489581 = 1308593) B1308593
theorem B573239 : Blo 570811 573239 := bstep (se 1 (by rfl) ⟨429929, by rfl⟩ : syracuseStep 573239 = 859859) B859859
theorem B573259 : Blo 570811 573259 := bstep (se 1 (by rfl) ⟨429944, by rfl⟩ : syracuseStep 573259 = 859889) B859889
theorem B573271 : Blo 570811 573271 := bstep (se 1 (by rfl) ⟨429953, by rfl⟩ : syracuseStep 573271 = 859907) B859907
theorem B1032025 : Blo 570811 1032025 := bstep (se 2 (by rfl) ⟨387009, by rfl⟩ : syracuseStep 1032025 = 774019) B774019
theorem B573291 : Blo 570811 573291 := bstep (se 1 (by rfl) ⟨429968, by rfl⟩ : syracuseStep 573291 = 859937) B859937
theorem B573303 : Blo 570811 573303 := bstep (se 1 (by rfl) ⟨429977, by rfl⟩ : syracuseStep 573303 = 859955) B859955
theorem B966539 : Blo 570811 966539 := bstep (se 1 (by rfl) ⟨724904, by rfl⟩ : syracuseStep 966539 = 1449809) B1449809
theorem B573323 : Blo 570811 573323 := bstep (se 1 (by rfl) ⟨429992, by rfl⟩ : syracuseStep 573323 = 859985) B859985
theorem B573335 : Blo 570811 573335 := bstep (se 1 (by rfl) ⟨430001, by rfl⟩ : syracuseStep 573335 = 860003) B860003
theorem B573355 : Blo 570811 573355 := bstep (se 1 (by rfl) ⟨430016, by rfl⟩ : syracuseStep 573355 = 860033) B860033
theorem B573367 : Blo 570811 573367 := bstep (se 1 (by rfl) ⟨430025, by rfl⟩ : syracuseStep 573367 = 860051) B860051
theorem B573387 : Blo 570811 573387 := bstep (se 1 (by rfl) ⟨430040, by rfl⟩ : syracuseStep 573387 = 860081) B860081
theorem B573399 : Blo 570811 573399 := bstep (se 1 (by rfl) ⟨430049, by rfl⟩ : syracuseStep 573399 = 860099) B860099
theorem B573419 : Blo 570811 573419 := bstep (se 1 (by rfl) ⟨430064, by rfl⟩ : syracuseStep 573419 = 860129) B860129
theorem B573431 : Blo 570811 573431 := bstep (se 1 (by rfl) ⟨430073, by rfl⟩ : syracuseStep 573431 = 860147) B860147
theorem B966667 : Blo 570811 966667 := bstep (se 1 (by rfl) ⟨725000, by rfl⟩ : syracuseStep 966667 = 1450001) B1450001
theorem B573451 : Blo 570811 573451 := bstep (se 1 (by rfl) ⟨430088, by rfl⟩ : syracuseStep 573451 = 860177) B860177
theorem B573463 : Blo 570811 573463 := bstep (se 1 (by rfl) ⟨430097, by rfl⟩ : syracuseStep 573463 = 860195) B860195
theorem B573483 : Blo 570811 573483 := bstep (se 1 (by rfl) ⟨430112, by rfl⟩ : syracuseStep 573483 = 860225) B860225
theorem B573495 : Blo 570811 573495 := bstep (se 1 (by rfl) ⟨430121, by rfl⟩ : syracuseStep 573495 = 860243) B860243
theorem B1032257 : Blo 570811 1032257 := bstep (se 2 (by rfl) ⟨387096, by rfl⟩ : syracuseStep 1032257 = 774193) B774193
theorem B24756293 : Blo 570811 24756293 := bstep (se 4 (by rfl) ⟨2320902, by rfl⟩ : syracuseStep 24756293 = 4641805) B4641805
theorem B573515 : Blo 570811 573515 := bstep (se 1 (by rfl) ⟨430136, by rfl⟩ : syracuseStep 573515 = 860273) B860273
theorem B573527 : Blo 570811 573527 := bstep (se 1 (by rfl) ⟨430145, by rfl⟩ : syracuseStep 573527 = 860291) B860291
theorem B573547 : Blo 570811 573547 := bstep (se 1 (by rfl) ⟨430160, by rfl⟩ : syracuseStep 573547 = 860321) B860321
theorem B573559 : Blo 570811 573559 := bstep (se 1 (by rfl) ⟨430169, by rfl⟩ : syracuseStep 573559 = 860339) B860339
theorem B573579 : Blo 570811 573579 := bstep (se 1 (by rfl) ⟨430184, by rfl⟩ : syracuseStep 573579 = 860369) B860369
theorem B2474135 : Blo 570811 2474135 := bstep (se 1 (by rfl) ⟨1855601, by rfl⟩ : syracuseStep 2474135 = 3711203) B3711203
theorem B573591 : Blo 570811 573591 := bstep (se 1 (by rfl) ⟨430193, by rfl⟩ : syracuseStep 573591 = 860387) B860387
theorem B966809 : Blo 570811 966809 := bstep (se 2 (by rfl) ⟨362553, by rfl⟩ : syracuseStep 966809 = 725107) B725107
theorem B573611 : Blo 570811 573611 := bstep (se 1 (by rfl) ⟨430208, by rfl⟩ : syracuseStep 573611 = 860417) B860417
theorem B573623 : Blo 570811 573623 := bstep (se 1 (by rfl) ⟨430217, by rfl⟩ : syracuseStep 573623 = 860435) B860435
theorem B573643 : Blo 570811 573643 := bstep (se 1 (by rfl) ⟨430232, by rfl⟩ : syracuseStep 573643 = 860465) B860465
theorem B1032407 : Blo 570811 1032407 := bstep (se 1 (by rfl) ⟨774305, by rfl⟩ : syracuseStep 1032407 = 1548611) B1548611
theorem B573655 : Blo 570811 573655 := bstep (se 1 (by rfl) ⟨430241, by rfl⟩ : syracuseStep 573655 = 860483) B860483
theorem B573675 : Blo 570811 573675 := bstep (se 1 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 573675 = 860513) B860513
theorem B573687 : Blo 570811 573687 := bstep (se 1 (by rfl) ⟨430265, by rfl⟩ : syracuseStep 573687 = 860531) B860531
theorem B2179331 : Blo 570811 2179331 := bstep (se 1 (by rfl) ⟨1634498, by rfl⟩ : syracuseStep 2179331 = 3268997) B3268997
theorem B573707 : Blo 570811 573707 := bstep (se 1 (by rfl) ⟨430280, by rfl⟩ : syracuseStep 573707 = 860561) B860561
theorem B2933009 : Blo 570811 2933009 := bstep (se 2 (by rfl) ⟨1099878, by rfl⟩ : syracuseStep 2933009 = 2199757) B2199757
theorem B2179345 : Blo 570811 2179345 := bstep (se 2 (by rfl) ⟨817254, by rfl⟩ : syracuseStep 2179345 = 1634509) B1634509
theorem B573719 : Blo 570811 573719 := bstep (se 1 (by rfl) ⟨430289, by rfl⟩ : syracuseStep 573719 = 860579) B860579
theorem B966937 : Blo 570811 966937 := bstep (se 2 (by rfl) ⟨362601, by rfl⟩ : syracuseStep 966937 = 725203) B725203
theorem B573739 : Blo 570811 573739 := bstep (se 1 (by rfl) ⟨430304, by rfl⟩ : syracuseStep 573739 = 860609) B860609
theorem B573751 : Blo 570811 573751 := bstep (se 1 (by rfl) ⟨430313, by rfl⟩ : syracuseStep 573751 = 860627) B860627
theorem B8274241 : Blo 570811 8274241 := bstep (se 2 (by rfl) ⟨3102840, by rfl⟩ : syracuseStep 8274241 = 6205681) B6205681
theorem B573771 : Blo 570811 573771 := bstep (se 1 (by rfl) ⟨430328, by rfl⟩ : syracuseStep 573771 = 860657) B860657
theorem B573783 : Blo 570811 573783 := bstep (se 1 (by rfl) ⟨430337, by rfl⟩ : syracuseStep 573783 = 860675) B860675
theorem B573803 : Blo 570811 573803 := bstep (se 1 (by rfl) ⟨430352, by rfl⟩ : syracuseStep 573803 = 860705) B860705
theorem B573815 : Blo 570811 573815 := bstep (se 1 (by rfl) ⟨430361, by rfl⟩ : syracuseStep 573815 = 860723) B860723
theorem B573835 : Blo 570811 573835 := bstep (se 1 (by rfl) ⟨430376, by rfl⟩ : syracuseStep 573835 = 860753) B860753
theorem B573847 : Blo 570811 573847 := bstep (se 1 (by rfl) ⟨430385, by rfl⟩ : syracuseStep 573847 = 860771) B860771
theorem B573867 : Blo 570811 573867 := bstep (se 1 (by rfl) ⟨430400, by rfl⟩ : syracuseStep 573867 = 860801) B860801
theorem B573879 : Blo 570811 573879 := bstep (se 1 (by rfl) ⟨430409, by rfl⟩ : syracuseStep 573879 = 860819) B860819
theorem B573899 : Blo 570811 573899 := bstep (se 1 (by rfl) ⟨430424, by rfl⟩ : syracuseStep 573899 = 860849) B860849
theorem B573911 : Blo 570811 573911 := bstep (se 1 (by rfl) ⟨430433, by rfl⟩ : syracuseStep 573911 = 860867) B860867
theorem B573931 : Blo 570811 573931 := bstep (se 1 (by rfl) ⟨430448, by rfl⟩ : syracuseStep 573931 = 860897) B860897
theorem B573943 : Blo 570811 573943 := bstep (se 1 (by rfl) ⟨430457, by rfl⟩ : syracuseStep 573943 = 860915) B860915
theorem B573963 : Blo 570811 573963 := bstep (se 1 (by rfl) ⟨430472, by rfl⟩ : syracuseStep 573963 = 860945) B860945
theorem B573975 : Blo 570811 573975 := bstep (se 1 (by rfl) ⟨430481, by rfl⟩ : syracuseStep 573975 = 860963) B860963
theorem B573995 : Blo 570811 573995 := bstep (se 1 (by rfl) ⟨430496, by rfl⟩ : syracuseStep 573995 = 860993) B860993
theorem B574007 : Blo 570811 574007 := bstep (se 1 (by rfl) ⟨430505, by rfl⟩ : syracuseStep 574007 = 861011) B861011
theorem B2179649 : Blo 570811 2179649 := bstep (se 2 (by rfl) ⟨817368, by rfl⟩ : syracuseStep 2179649 = 1634737) B1634737
theorem B574027 : Blo 570811 574027 := bstep (se 1 (by rfl) ⟨430520, by rfl⟩ : syracuseStep 574027 = 861041) B861041
theorem B574039 : Blo 570811 574039 := bstep (se 1 (by rfl) ⟨430529, by rfl⟩ : syracuseStep 574039 = 861059) B861059
theorem B574059 : Blo 570811 574059 := bstep (se 1 (by rfl) ⟨430544, by rfl⟩ : syracuseStep 574059 = 861089) B861089
theorem B1163891 : Blo 570811 1163891 := bstep (se 1 (by rfl) ⟨872918, by rfl⟩ : syracuseStep 1163891 = 1745837) B1745837
theorem B574071 : Blo 570811 574071 := bstep (se 1 (by rfl) ⟨430553, by rfl⟩ : syracuseStep 574071 = 861107) B861107
theorem B574091 : Blo 570811 574091 := bstep (se 1 (by rfl) ⟨430568, by rfl⟩ : syracuseStep 574091 = 861137) B861137
theorem B574103 : Blo 570811 574103 := bstep (se 1 (by rfl) ⟨430577, by rfl⟩ : syracuseStep 574103 = 861155) B861155
theorem B574123 : Blo 570811 574123 := bstep (se 1 (by rfl) ⟨430592, by rfl⟩ : syracuseStep 574123 = 861185) B861185
theorem B574135 : Blo 570811 574135 := bstep (se 1 (by rfl) ⟨430601, by rfl⟩ : syracuseStep 574135 = 861203) B861203
theorem B574155 : Blo 570811 574155 := bstep (se 1 (by rfl) ⟨430616, by rfl⟩ : syracuseStep 574155 = 861233) B861233
theorem B574167 : Blo 570811 574167 := bstep (se 1 (by rfl) ⟨430625, by rfl⟩ : syracuseStep 574167 = 861251) B861251
theorem B574187 : Blo 570811 574187 := bstep (se 1 (by rfl) ⟨430640, by rfl⟩ : syracuseStep 574187 = 861281) B861281
theorem B574199 : Blo 570811 574199 := bstep (se 1 (by rfl) ⟨430649, by rfl⟩ : syracuseStep 574199 = 861299) B861299
theorem B574219 : Blo 570811 574219 := bstep (se 1 (by rfl) ⟨430664, by rfl⟩ : syracuseStep 574219 = 861329) B861329
theorem B574231 : Blo 570811 574231 := bstep (se 1 (by rfl) ⟨430673, by rfl⟩ : syracuseStep 574231 = 861347) B861347
theorem B574251 : Blo 570811 574251 := bstep (se 1 (by rfl) ⟨430688, by rfl⟩ : syracuseStep 574251 = 861377) B861377
theorem B5882669 : Blo 570811 5882669 := bstep (se 3 (by rfl) ⟨1103000, by rfl⟩ : syracuseStep 5882669 = 2206001) B2206001
theorem B574263 : Blo 570811 574263 := bstep (se 1 (by rfl) ⟨430697, by rfl⟩ : syracuseStep 574263 = 861395) B861395
theorem B2442059 : Blo 570811 2442059 := bstep (se 1 (by rfl) ⟨1831544, by rfl⟩ : syracuseStep 2442059 = 3663089) B3663089
theorem B574283 : Blo 570811 574283 := bstep (se 1 (by rfl) ⟨430712, by rfl⟩ : syracuseStep 574283 = 861425) B861425
theorem B967511 : Blo 570811 967511 := bstep (se 1 (by rfl) ⟨725633, by rfl⟩ : syracuseStep 967511 = 1451267) B1451267
theorem B574295 : Blo 570811 574295 := bstep (se 1 (by rfl) ⟨430721, by rfl⟩ : syracuseStep 574295 = 861443) B861443
theorem B574315 : Blo 570811 574315 := bstep (se 1 (by rfl) ⟨430736, by rfl⟩ : syracuseStep 574315 = 861473) B861473
theorem B574327 : Blo 570811 574327 := bstep (se 1 (by rfl) ⟨430745, by rfl⟩ : syracuseStep 574327 = 861491) B861491
theorem B574347 : Blo 570811 574347 := bstep (se 1 (by rfl) ⟨430760, by rfl⟩ : syracuseStep 574347 = 861521) B861521
theorem B574359 : Blo 570811 574359 := bstep (se 1 (by rfl) ⟨430769, by rfl⟩ : syracuseStep 574359 = 861539) B861539
theorem B574379 : Blo 570811 574379 := bstep (se 1 (by rfl) ⟨430784, by rfl⟩ : syracuseStep 574379 = 861569) B861569
theorem B574391 : Blo 570811 574391 := bstep (se 1 (by rfl) ⟨430793, by rfl⟩ : syracuseStep 574391 = 861587) B861587
theorem B574411 : Blo 570811 574411 := bstep (se 1 (by rfl) ⟨430808, by rfl⟩ : syracuseStep 574411 = 861617) B861617
theorem B967639 : Blo 570811 967639 := bstep (se 1 (by rfl) ⟨725729, by rfl⟩ : syracuseStep 967639 = 1451459) B1451459
theorem B574423 : Blo 570811 574423 := bstep (se 1 (by rfl) ⟨430817, by rfl⟩ : syracuseStep 574423 = 861635) B861635
theorem B574443 : Blo 570811 574443 := bstep (se 1 (by rfl) ⟨430832, by rfl⟩ : syracuseStep 574443 = 861665) B861665
theorem B574455 : Blo 570811 574455 := bstep (se 1 (by rfl) ⟨430841, by rfl⟩ : syracuseStep 574455 = 861683) B861683
theorem B574475 : Blo 570811 574475 := bstep (se 1 (by rfl) ⟨430856, by rfl⟩ : syracuseStep 574475 = 861713) B861713
theorem B574487 : Blo 570811 574487 := bstep (se 1 (by rfl) ⟨430865, by rfl⟩ : syracuseStep 574487 = 861731) B861731
theorem B574507 : Blo 570811 574507 := bstep (se 1 (by rfl) ⟨430880, by rfl⟩ : syracuseStep 574507 = 861761) B861761
theorem B574519 : Blo 570811 574519 := bstep (se 1 (by rfl) ⟨430889, by rfl⟩ : syracuseStep 574519 = 861779) B861779
theorem B574539 : Blo 570811 574539 := bstep (se 1 (by rfl) ⟨430904, by rfl⟩ : syracuseStep 574539 = 861809) B861809
theorem B574551 : Blo 570811 574551 := bstep (se 1 (by rfl) ⟨430913, by rfl⟩ : syracuseStep 574551 = 861827) B861827
theorem B574571 : Blo 570811 574571 := bstep (se 1 (by rfl) ⟨430928, by rfl⟩ : syracuseStep 574571 = 861857) B861857
theorem B574583 : Blo 570811 574583 := bstep (se 1 (by rfl) ⟨430937, by rfl⟩ : syracuseStep 574583 = 861875) B861875
theorem B574603 : Blo 570811 574603 := bstep (se 1 (by rfl) ⟨430952, by rfl⟩ : syracuseStep 574603 = 861905) B861905
theorem B574615 : Blo 570811 574615 := bstep (se 1 (by rfl) ⟨430961, by rfl⟩ : syracuseStep 574615 = 861923) B861923
theorem B574635 : Blo 570811 574635 := bstep (se 1 (by rfl) ⟨430976, by rfl⟩ : syracuseStep 574635 = 861953) B861953
theorem B574647 : Blo 570811 574647 := bstep (se 1 (by rfl) ⟨430985, by rfl⟩ : syracuseStep 574647 = 861971) B861971
theorem B1033409 : Blo 570811 1033409 := bstep (se 2 (by rfl) ⟨387528, by rfl⟩ : syracuseStep 1033409 = 775057) B775057
theorem B574667 : Blo 570811 574667 := bstep (se 1 (by rfl) ⟨431000, by rfl⟩ : syracuseStep 574667 = 862001) B862001
theorem B574679 : Blo 570811 574679 := bstep (se 1 (by rfl) ⟨431009, by rfl⟩ : syracuseStep 574679 = 862019) B862019
theorem B2180317 : Blo 570811 2180317 := bstep (se 3 (by rfl) ⟨408809, by rfl⟩ : syracuseStep 2180317 = 817619) B817619
theorem B574699 : Blo 570811 574699 := bstep (se 1 (by rfl) ⟨431024, by rfl⟩ : syracuseStep 574699 = 862049) B862049
theorem B574711 : Blo 570811 574711 := bstep (se 1 (by rfl) ⟨431033, by rfl⟩ : syracuseStep 574711 = 862067) B862067
theorem B574731 : Blo 570811 574731 := bstep (se 1 (by rfl) ⟨431048, by rfl⟩ : syracuseStep 574731 = 862097) B862097
theorem B574743 : Blo 570811 574743 := bstep (se 1 (by rfl) ⟨431057, by rfl⟩ : syracuseStep 574743 = 862115) B862115
theorem B574763 : Blo 570811 574763 := bstep (se 1 (by rfl) ⟨431072, by rfl⟩ : syracuseStep 574763 = 862145) B862145
theorem B574775 : Blo 570811 574775 := bstep (se 1 (by rfl) ⟨431081, by rfl⟩ : syracuseStep 574775 = 862163) B862163
theorem B574795 : Blo 570811 574795 := bstep (se 1 (by rfl) ⟨431096, by rfl⟩ : syracuseStep 574795 = 862193) B862193
theorem B574807 : Blo 570811 574807 := bstep (se 1 (by rfl) ⟨431105, by rfl⟩ : syracuseStep 574807 = 862211) B862211
theorem B4900247 : Blo 570811 4900247 := bstep (se 1 (by rfl) ⟨3675185, by rfl⟩ : syracuseStep 4900247 = 7350371) B7350371
theorem B968267 : Blo 570811 968267 := bstep (se 1 (by rfl) ⟨726200, by rfl⟩ : syracuseStep 968267 = 1452401) B1452401
theorem B968395 : Blo 570811 968395 := bstep (se 1 (by rfl) ⟨726296, by rfl⟩ : syracuseStep 968395 = 1452593) B1452593
theorem B968537 : Blo 570811 968537 := bstep (se 2 (by rfl) ⟨363201, by rfl⟩ : syracuseStep 968537 = 726403) B726403
theorem B968665 : Blo 570811 968665 := bstep (se 2 (by rfl) ⟨363249, by rfl⟩ : syracuseStep 968665 = 726499) B726499
theorem B16468109 : Blo 570811 16468109 := bstep (se 3 (by rfl) ⟨3087770, by rfl⟩ : syracuseStep 16468109 = 6175541) B6175541
theorem B7850135 : Blo 570811 7850135 := bstep (se 1 (by rfl) ⟨5887601, by rfl⟩ : syracuseStep 7850135 = 11775203) B11775203
theorem B1099955 : Blo 570811 1099955 := bstep (se 1 (by rfl) ⟨824966, by rfl⟩ : syracuseStep 1099955 = 1649933) B1649933
theorem B4114637 : Blo 570811 4114637 := bstep (se 3 (by rfl) ⟨771494, by rfl⟩ : syracuseStep 4114637 = 1542989) B1542989
theorem B1394995 : Blo 570811 1394995 := bstep (se 1 (by rfl) ⟨1046246, by rfl⟩ : syracuseStep 1394995 = 2092493) B2092493
theorem B2443699 : Blo 570811 2443699 := bstep (se 1 (by rfl) ⟨1832774, by rfl⟩ : syracuseStep 2443699 = 3665549) B3665549
theorem B1034699 : Blo 570811 1034699 := bstep (se 1 (by rfl) ⟨776024, by rfl⟩ : syracuseStep 1034699 = 1552049) B1552049
theorem B1034713 : Blo 570811 1034713 := bstep (se 2 (by rfl) ⟨388017, by rfl⟩ : syracuseStep 1034713 = 776035) B776035
theorem B2181593 : Blo 570811 2181593 := bstep (se 2 (by rfl) ⟨818097, by rfl⟩ : syracuseStep 2181593 = 1636195) B1636195
theorem B969239 : Blo 570811 969239 := bstep (se 1 (by rfl) ⟨726929, by rfl⟩ : syracuseStep 969239 = 1453859) B1453859
theorem B969367 : Blo 570811 969367 := bstep (se 1 (by rfl) ⟨727025, by rfl⟩ : syracuseStep 969367 = 1454051) B1454051
theorem B1035031 : Blo 570811 1035031 := bstep (se 1 (by rfl) ⟨776273, by rfl⟩ : syracuseStep 1035031 = 1552547) B1552547
theorem B2476889 : Blo 570811 2476889 := bstep (se 2 (by rfl) ⟨928833, by rfl⟩ : syracuseStep 2476889 = 1857667) B1857667
theorem B2902877 : Blo 570811 2902877 := bstep (se 3 (by rfl) ⟨544289, by rfl⟩ : syracuseStep 2902877 = 1088579) B1088579
theorem B642199 : Blo 570811 642199 := bstep (se 1 (by rfl) ⟨481649, by rfl⟩ : syracuseStep 642199 = 963299) B963299
theorem B969995 : Blo 570811 969995 := bstep (se 1 (by rfl) ⟨727496, by rfl⟩ : syracuseStep 969995 = 1454993) B1454993
theorem B642379 : Blo 570811 642379 := bstep (se 1 (by rfl) ⟨481784, by rfl⟩ : syracuseStep 642379 = 963569) B963569
theorem B1035659 : Blo 570811 1035659 := bstep (se 1 (by rfl) ⟨776744, by rfl⟩ : syracuseStep 1035659 = 1553489) B1553489
theorem B642487 : Blo 570811 642487 := bstep (se 1 (by rfl) ⟨481865, by rfl⟩ : syracuseStep 642487 = 963731) B963731
theorem B642667 : Blo 570811 642667 := bstep (se 1 (by rfl) ⟨482000, by rfl⟩ : syracuseStep 642667 = 964001) B964001
theorem B642775 : Blo 570811 642775 := bstep (se 1 (by rfl) ⟨482081, by rfl⟩ : syracuseStep 642775 = 964163) B964163
theorem B4476707 : Blo 570811 4476707 := bstep (se 1 (by rfl) ⟨3357530, by rfl⟩ : syracuseStep 4476707 = 6715061) B6715061
theorem B16797539 : Blo 570811 16797539 := bstep (se 1 (by rfl) ⟨12598154, by rfl⟩ : syracuseStep 16797539 = 25196309) B25196309
theorem B2445187 : Blo 570811 2445187 := bstep (se 1 (by rfl) ⟨1833890, by rfl⟩ : syracuseStep 2445187 = 3667781) B3667781
theorem B642955 : Blo 570811 642955 := bstep (se 1 (by rfl) ⟨482216, by rfl⟩ : syracuseStep 642955 = 964433) B964433
theorem B643063 : Blo 570811 643063 := bstep (se 1 (by rfl) ⟨482297, by rfl⟩ : syracuseStep 643063 = 964595) B964595
theorem B1626263 : Blo 570811 1626263 := bstep (se 1 (by rfl) ⟨1219697, by rfl⟩ : syracuseStep 1626263 = 2439395) B2439395
theorem B643243 : Blo 570811 643243 := bstep (se 1 (by rfl) ⟨482432, by rfl⟩ : syracuseStep 643243 = 964865) B964865
theorem B610583 : Blo 570811 610583 := bstep (se 1 (by rfl) ⟨457937, by rfl⟩ : syracuseStep 610583 = 915875) B915875
theorem B643351 : Blo 570811 643351 := bstep (se 1 (by rfl) ⟨482513, by rfl⟩ : syracuseStep 643351 = 965027) B965027
theorem B1855795 : Blo 570811 1855795 := bstep (se 1 (by rfl) ⟨1391846, by rfl⟩ : syracuseStep 1855795 = 2783693) B2783693
theorem B643531 : Blo 570811 643531 := bstep (se 1 (by rfl) ⟨482648, by rfl⟩ : syracuseStep 643531 = 965297) B965297
theorem B2445785 : Blo 570811 2445785 := bstep (se 2 (by rfl) ⟨917169, by rfl⟩ : syracuseStep 2445785 = 1834339) B1834339
theorem B643639 : Blo 570811 643639 := bstep (se 1 (by rfl) ⟨482729, by rfl⟩ : syracuseStep 643639 = 965459) B965459
theorem B873175 : Blo 570811 873175 := bstep (se 1 (by rfl) ⟨654881, by rfl⟩ : syracuseStep 873175 = 1309763) B1309763
theorem B643819 : Blo 570811 643819 := bstep (se 1 (by rfl) ⟨482864, by rfl⟩ : syracuseStep 643819 = 965729) B965729
theorem B2446145 : Blo 570811 2446145 := bstep (se 2 (by rfl) ⟨917304, by rfl⟩ : syracuseStep 2446145 = 1834609) B1834609
theorem B643927 : Blo 570811 643927 := bstep (se 1 (by rfl) ⟨482945, by rfl⟩ : syracuseStep 643927 = 965891) B965891
theorem B3265373 : Blo 570811 3265373 := bstep (se 3 (by rfl) ⟨612257, by rfl⟩ : syracuseStep 3265373 = 1224515) B1224515
theorem B2904983 : Blo 570811 2904983 := bstep (se 1 (by rfl) ⟨2178737, by rfl⟩ : syracuseStep 2904983 = 4357475) B4357475
theorem B644107 : Blo 570811 644107 := bstep (se 1 (by rfl) ⟨483080, by rfl⟩ : syracuseStep 644107 = 966161) B966161
theorem B644215 : Blo 570811 644215 := bstep (se 1 (by rfl) ⟨483161, by rfl⟩ : syracuseStep 644215 = 966323) B966323
theorem B644395 : Blo 570811 644395 := bstep (se 1 (by rfl) ⟨483296, by rfl⟩ : syracuseStep 644395 = 966593) B966593
theorem B644503 : Blo 570811 644503 := bstep (se 1 (by rfl) ⟨483377, by rfl⟩ : syracuseStep 644503 = 966755) B966755
theorem B2315713 : Blo 570811 2315713 := bstep (se 2 (by rfl) ⟨868392, by rfl⟩ : syracuseStep 2315713 = 1736785) B1736785
theorem B644683 : Blo 570811 644683 := bstep (se 1 (by rfl) ⟨483512, by rfl⟩ : syracuseStep 644683 = 967025) B967025
theorem B5232221 : Blo 570811 5232221 := bstep (se 3 (by rfl) ⟨981041, by rfl⟩ : syracuseStep 5232221 = 1962083) B1962083
theorem B9557597 : Blo 570811 9557597 := bstep (se 3 (by rfl) ⟨1792049, by rfl⟩ : syracuseStep 9557597 = 3584099) B3584099
theorem B644791 : Blo 570811 644791 := bstep (se 1 (by rfl) ⟨483593, by rfl⟩ : syracuseStep 644791 = 967187) B967187
theorem B644971 : Blo 570811 644971 := bstep (se 1 (by rfl) ⟨483728, by rfl⟩ : syracuseStep 644971 = 967457) B967457
theorem B645079 : Blo 570811 645079 := bstep (se 1 (by rfl) ⟨483809, by rfl⟩ : syracuseStep 645079 = 967619) B967619
theorem B612343 : Blo 570811 612343 := bstep (se 1 (by rfl) ⟨459257, by rfl⟩ : syracuseStep 612343 = 918515) B918515
theorem B579691 : Blo 570811 579691 := bstep (se 1 (by rfl) ⟨434768, by rfl⟩ : syracuseStep 579691 = 869537) B869537
theorem B645259 : Blo 570811 645259 := bstep (se 1 (by rfl) ⟨483944, by rfl⟩ : syracuseStep 645259 = 967889) B967889
theorem B645367 : Blo 570811 645367 := bstep (se 1 (by rfl) ⟨484025, by rfl⟩ : syracuseStep 645367 = 968051) B968051
theorem B645547 : Blo 570811 645547 := bstep (se 1 (by rfl) ⟨484160, by rfl⟩ : syracuseStep 645547 = 968321) B968321
theorem B645655 : Blo 570811 645655 := bstep (se 1 (by rfl) ⟨484241, by rfl⟩ : syracuseStep 645655 = 968483) B968483
theorem B1956403 : Blo 570811 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B1628723 : Blo 570811 1628723 := bstep (se 1 (by rfl) ⟨1221542, by rfl⟩ : syracuseStep 1628723 = 2443085) B2443085
theorem B645835 : Blo 570811 645835 := bstep (se 1 (by rfl) ⟨484376, by rfl⟩ : syracuseStep 645835 = 968753) B968753
theorem B645943 : Blo 570811 645943 := bstep (se 1 (by rfl) ⟨484457, by rfl⟩ : syracuseStep 645943 = 968915) B968915
theorem B5561189 : Blo 570811 5561189 := bstep (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) B1042723
theorem B2317207 : Blo 570811 2317207 := bstep (se 1 (by rfl) ⟨1737905, by rfl⟩ : syracuseStep 2317207 = 3475811) B3475811
theorem B646123 : Blo 570811 646123 := bstep (se 1 (by rfl) ⟨484592, by rfl⟩ : syracuseStep 646123 = 969185) B969185
theorem B2481197 : Blo 570811 2481197 := bstep (se 3 (by rfl) ⟨465224, by rfl⟩ : syracuseStep 2481197 = 930449) B930449
theorem B646231 : Blo 570811 646231 := bstep (se 1 (by rfl) ⟨484673, by rfl⟩ : syracuseStep 646231 = 969347) B969347
theorem B646411 : Blo 570811 646411 := bstep (se 1 (by rfl) ⟨484808, by rfl⟩ : syracuseStep 646411 = 969617) B969617
theorem B5954917 : Blo 570811 5954917 := bstep (se 4 (by rfl) ⟨558273, by rfl⟩ : syracuseStep 5954917 = 1116547) B1116547
theorem B646519 : Blo 570811 646519 := bstep (se 1 (by rfl) ⟨484889, by rfl⟩ : syracuseStep 646519 = 969779) B969779
theorem B3267971 : Blo 570811 3267971 := bstep (se 1 (by rfl) ⟨2450978, by rfl⟩ : syracuseStep 3267971 = 4901957) B4901957
theorem B2612915 : Blo 570811 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B8282033 : Blo 570811 8282033 := bstep (se 2 (by rfl) ⟨3105762, by rfl⟩ : syracuseStep 8282033 = 6211525) B6211525
theorem B3104729 : Blo 570811 3104729 := bstep (se 2 (by rfl) ⟨1164273, by rfl⟩ : syracuseStep 3104729 = 2328547) B2328547
theorem B11952197 : Blo 570811 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B2908547 : Blo 570811 2908547 := bstep (se 1 (by rfl) ⟨2181410, by rfl⟩ : syracuseStep 2908547 = 4362821) B4362821
theorem B582071 : Blo 570811 582071 := bstep (se 1 (by rfl) ⟨436553, by rfl⟩ : syracuseStep 582071 = 873107) B873107
theorem B2449885 : Blo 570811 2449885 := bstep (se 3 (by rfl) ⟨459353, by rfl⟩ : syracuseStep 2449885 = 918707) B918707
theorem B1860275 : Blo 570811 1860275 := bstep (se 1 (by rfl) ⟨1395206, by rfl⟩ : syracuseStep 1860275 = 2790413) B2790413
theorem B1762013 : Blo 570811 1762013 := bstep (se 3 (by rfl) ⟨330377, by rfl⟩ : syracuseStep 1762013 = 660755) B660755
theorem B2974481 : Blo 570811 2974481 := bstep (se 2 (by rfl) ⟨1115430, by rfl⟩ : syracuseStep 2974481 = 2230861) B2230861
theorem B3662657 : Blo 570811 3662657 := bstep (se 2 (by rfl) ⟨1373496, by rfl⟩ : syracuseStep 3662657 = 2746993) B2746993
theorem B2319283 : Blo 570811 2319283 := bstep (se 1 (by rfl) ⟨1739462, by rfl⟩ : syracuseStep 2319283 = 3478925) B3478925
theorem B2319511 : Blo 570811 2319511 := bstep (se 1 (by rfl) ⟨1739633, by rfl⟩ : syracuseStep 2319511 = 3479267) B3479267
theorem B1631411 : Blo 570811 1631411 := bstep (se 1 (by rfl) ⟨1223558, by rfl⟩ : syracuseStep 1631411 = 2447117) B2447117
theorem B2057489 : Blo 570811 2057489 := bstep (se 2 (by rfl) ⟨771558, by rfl⟩ : syracuseStep 2057489 = 1543117) B1543117
theorem B1467713 : Blo 570811 1467713 := bstep (se 2 (by rfl) ⟨550392, by rfl⟩ : syracuseStep 1467713 = 1100785) B1100785
theorem B1631639 : Blo 570811 1631639 := bstep (se 1 (by rfl) ⟨1223729, by rfl⟩ : syracuseStep 1631639 = 2447459) B2447459
theorem B4908721 : Blo 570811 4908721 := bstep (se 2 (by rfl) ⟨1840770, by rfl⟩ : syracuseStep 4908721 = 3681541) B3681541
theorem B1631947 : Blo 570811 1631947 := bstep (se 1 (by rfl) ⟨1223960, by rfl⟩ : syracuseStep 1631947 = 2447921) B2447921
theorem B2451217 : Blo 570811 2451217 := bstep (se 2 (by rfl) ⟨919206, by rfl⟩ : syracuseStep 2451217 = 1838413) B1838413
theorem B1926935 : Blo 570811 1926935 := bstep (se 1 (by rfl) ⟨1445201, by rfl⟩ : syracuseStep 1926935 = 2890403) B2890403
theorem B2615105 : Blo 570811 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B4646807 : Blo 570811 4646807 := bstep (se 1 (by rfl) ⟨3485105, by rfl⟩ : syracuseStep 4646807 = 6970211) B6970211
theorem B1632221 : Blo 570811 1632221 := bstep (se 3 (by rfl) ⟨306041, by rfl⟩ : syracuseStep 1632221 = 612083) B612083
theorem B1927475 : Blo 570811 1927475 := bstep (se 1 (by rfl) ⟨1445606, by rfl⟩ : syracuseStep 1927475 = 2891213) B2891213
theorem B1829213 : Blo 570811 1829213 := bstep (se 3 (by rfl) ⟨342977, by rfl⟩ : syracuseStep 1829213 = 685955) B685955
theorem B1927745 : Blo 570811 1927745 := bstep (se 2 (by rfl) ⟨722904, by rfl⟩ : syracuseStep 1927745 = 1445809) B1445809
theorem B2058817 : Blo 570811 2058817 := bstep (se 2 (by rfl) ⟨772056, by rfl⟩ : syracuseStep 2058817 = 1544113) B1544113
theorem B1305163 : Blo 570811 1305163 := bstep (se 1 (by rfl) ⟨978872, by rfl⟩ : syracuseStep 1305163 = 1957745) B1957745
theorem B813655 : Blo 570811 813655 := bstep (se 1 (by rfl) ⟨610241, by rfl⟩ : syracuseStep 813655 = 1220483) B1220483
theorem B1928285 : Blo 570811 1928285 := bstep (se 3 (by rfl) ⟨361553, by rfl⟩ : syracuseStep 1928285 = 723107) B723107
theorem B1830109 : Blo 570811 1830109 := bstep (se 3 (by rfl) ⟨343145, by rfl⟩ : syracuseStep 1830109 = 686291) B686291
theorem B4713821 : Blo 570811 4713821 := bstep (se 3 (by rfl) ⟨883841, by rfl⟩ : syracuseStep 4713821 = 1767683) B1767683
theorem B1371737 : Blo 570811 1371737 := bstep (se 2 (by rfl) ⟨514401, by rfl⟩ : syracuseStep 1371737 = 1028803) B1028803
theorem B1372121 : Blo 570811 1372121 := bstep (se 2 (by rfl) ⟨514545, by rfl⟩ : syracuseStep 1372121 = 1029091) B1029091
theorem B1634327 : Blo 570811 1634327 := bstep (se 1 (by rfl) ⟨1225745, by rfl⟩ : syracuseStep 1634327 = 2451491) B2451491
theorem B1929419 : Blo 570811 1929419 := bstep (se 1 (by rfl) ⟨1447064, by rfl⟩ : syracuseStep 1929419 = 2894129) B2894129
theorem B1962305 : Blo 570811 1962305 := bstep (se 2 (by rfl) ⟨735864, by rfl⟩ : syracuseStep 1962305 = 1471729) B1471729
theorem B2060633 : Blo 570811 2060633 := bstep (se 2 (by rfl) ⟨772737, by rfl⟩ : syracuseStep 2060633 = 1545475) B1545475
theorem B1929689 : Blo 570811 1929689 := bstep (se 2 (by rfl) ⟨723633, by rfl⟩ : syracuseStep 1929689 = 1447267) B1447267
theorem B5239331 : Blo 570811 5239331 := bstep (se 1 (by rfl) ⟨3929498, by rfl⟩ : syracuseStep 5239331 = 7858997) B7858997
theorem B2093633 : Blo 570811 2093633 := bstep (se 2 (by rfl) ⟨785112, by rfl⟩ : syracuseStep 2093633 = 1570225) B1570225
theorem B979543 : Blo 570811 979543 := bstep (se 1 (by rfl) ⟨734657, by rfl⟩ : syracuseStep 979543 = 1469315) B1469315
theorem B1962589 : Blo 570811 1962589 := bstep (se 3 (by rfl) ⟨367985, by rfl⟩ : syracuseStep 1962589 = 735971) B735971
theorem B2454209 : Blo 570811 2454209 := bstep (se 2 (by rfl) ⟨920328, by rfl⟩ : syracuseStep 2454209 = 1840657) B1840657
theorem B1635137 : Blo 570811 1635137 := bstep (se 2 (by rfl) ⟨613176, by rfl⟩ : syracuseStep 1635137 = 1226353) B1226353
theorem B1930391 : Blo 570811 1930391 := bstep (se 1 (by rfl) ⟨1447793, by rfl⟩ : syracuseStep 1930391 = 2895587) B2895587
theorem B652459 : Blo 570811 652459 := bstep (se 1 (by rfl) ⟨489344, by rfl⟩ : syracuseStep 652459 = 978689) B978689
theorem B1045939 : Blo 570811 1045939 := bstep (se 1 (by rfl) ⟨784454, by rfl⟩ : syracuseStep 1045939 = 1568909) B1568909
theorem B1930931 : Blo 570811 1930931 := bstep (se 1 (by rfl) ⟨1448198, by rfl⟩ : syracuseStep 1930931 = 2896397) B2896397
theorem B2062045 : Blo 570811 2062045 := bstep (se 3 (by rfl) ⟨386633, by rfl⟩ : syracuseStep 2062045 = 773267) B773267
theorem B2094913 : Blo 570811 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B1242955 : Blo 570811 1242955 := bstep (se 1 (by rfl) ⟨932216, by rfl⟩ : syracuseStep 1242955 = 1864433) B1864433
theorem B3667805 : Blo 570811 3667805 := bstep (se 3 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 3667805 = 1375427) B1375427
theorem B4356017 : Blo 570811 4356017 := bstep (se 2 (by rfl) ⟨1633506, by rfl⟩ : syracuseStep 4356017 = 3267013) B3267013
theorem B1963955 : Blo 570811 1963955 := bstep (se 1 (by rfl) ⟨1472966, by rfl⟩ : syracuseStep 1963955 = 2945933) B2945933
theorem B1931201 : Blo 570811 1931201 := bstep (se 2 (by rfl) ⟨724200, by rfl⟩ : syracuseStep 1931201 = 1448401) B1448401
theorem B784345 : Blo 570811 784345 := bstep (se 2 (by rfl) ⟨294129, by rfl⟩ : syracuseStep 784345 = 588259) B588259
theorem B5502937 : Blo 570811 5502937 := bstep (se 2 (by rfl) ⟨2063601, by rfl⟩ : syracuseStep 5502937 = 4127203) B4127203
theorem B817175 : Blo 570811 817175 := bstep (se 1 (by rfl) ⟨612881, by rfl⟩ : syracuseStep 817175 = 1225763) B1225763
theorem B15628439 : Blo 570811 15628439 := bstep (se 1 (by rfl) ⟨11721329, by rfl⟩ : syracuseStep 15628439 = 23442659) B23442659
theorem B8255789 : Blo 570811 8255789 := bstep (se 3 (by rfl) ⟨1547960, by rfl⟩ : syracuseStep 8255789 = 3095921) B3095921
theorem B4356503 : Blo 570811 4356503 := bstep (se 1 (by rfl) ⟨3267377, by rfl⟩ : syracuseStep 4356503 = 6534755) B6534755
theorem B1636787 : Blo 570811 1636787 := bstep (se 1 (by rfl) ⟨1227590, by rfl⟩ : syracuseStep 1636787 = 2455181) B2455181
theorem B1636811 : Blo 570811 1636811 := bstep (se 1 (by rfl) ⟨1227608, by rfl⟩ : syracuseStep 1636811 = 2455217) B2455217
theorem B1931741 : Blo 570811 1931741 := bstep (se 3 (by rfl) ⟨362201, by rfl⟩ : syracuseStep 1931741 = 724403) B724403
theorem B1047041 : Blo 570811 1047041 := bstep (se 2 (by rfl) ⟨392640, by rfl⟩ : syracuseStep 1047041 = 785281) B785281
theorem B916247 : Blo 570811 916247 := bstep (se 1 (by rfl) ⟨687185, by rfl⟩ : syracuseStep 916247 = 1374371) B1374371
theorem B9272333 : Blo 570811 9272333 := bstep (se 3 (by rfl) ⟨1738562, by rfl⟩ : syracuseStep 9272333 = 3477125) B3477125
theorem B917003 : Blo 570811 917003 := bstep (se 1 (by rfl) ⟨687752, by rfl⟩ : syracuseStep 917003 = 1375505) B1375505
theorem B1932875 : Blo 570811 1932875 := bstep (se 1 (by rfl) ⟨1449656, by rfl⟩ : syracuseStep 1932875 = 2899313) B2899313
theorem B1310347 : Blo 570811 1310347 := bstep (se 1 (by rfl) ⟨982760, by rfl⟩ : syracuseStep 1310347 = 1965521) B1965521
theorem B1834775 : Blo 570811 1834775 := bstep (se 1 (by rfl) ⟨1376081, by rfl⟩ : syracuseStep 1834775 = 2752163) B2752163
theorem B2064179 : Blo 570811 2064179 := bstep (se 1 (by rfl) ⟨1548134, by rfl⟩ : syracuseStep 2064179 = 3096269) B3096269
theorem B1474355 : Blo 570811 1474355 := bstep (se 1 (by rfl) ⟨1105766, by rfl⟩ : syracuseStep 1474355 = 2211533) B2211533
theorem B1933145 : Blo 570811 1933145 := bstep (se 2 (by rfl) ⟨724929, by rfl⟩ : syracuseStep 1933145 = 1449859) B1449859
theorem B589771 : Blo 570811 589771 := bstep (se 1 (by rfl) ⟨442328, by rfl⟩ : syracuseStep 589771 = 884657) B884657
theorem B688171 : Blo 570811 688171 := bstep (se 1 (by rfl) ⟨516128, by rfl⟩ : syracuseStep 688171 = 1032257) B1032257
theorem B688271 : Blo 570811 688271 := bstep (se 1 (by rfl) ⟨516203, by rfl⟩ : syracuseStep 688271 = 1032407) B1032407
theorem B1835531 : Blo 570811 1835531 := bstep (se 1 (by rfl) ⟨1376648, by rfl⟩ : syracuseStep 1835531 = 2753297) B2753297
theorem B1770839 : Blo 570811 1770839 := bstep (se 1 (by rfl) ⟨1328129, by rfl⟩ : syracuseStep 1770839 = 2656259) B2656259
theorem B2360723 : Blo 570811 2360723 := bstep (se 1 (by rfl) ⟨1770542, by rfl⟩ : syracuseStep 2360723 = 3541085) B3541085
theorem B10978739 : Blo 570811 10978739 := bstep (se 1 (by rfl) ⟨8234054, by rfl⟩ : syracuseStep 10978739 = 16468109) B16468109
theorem B1377803 : Blo 570811 1377803 := bstep (se 1 (by rfl) ⟨1033352, by rfl⟩ : syracuseStep 1377803 = 2066705) B2066705
theorem B1935251 : Blo 570811 1935251 := bstep (se 1 (by rfl) ⟨1451438, by rfl⟩ : syracuseStep 1935251 = 2902877) B2902877
theorem B8259479 : Blo 570811 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B722935 : Blo 570811 722935 := bstep (se 1 (by rfl) ⟨542201, by rfl⟩ : syracuseStep 722935 = 1084403) B1084403
theorem B21235729 : Blo 570811 21235729 := bstep (se 2 (by rfl) ⟨7963398, by rfl⟩ : syracuseStep 21235729 = 15926797) B15926797
theorem B1837313 : Blo 570811 1837313 := bstep (se 2 (by rfl) ⟨688992, by rfl⟩ : syracuseStep 1837313 = 1377985) B1377985
theorem B690439 : Blo 570811 690439 := bstep (se 1 (by rfl) ⟨517829, by rfl⟩ : syracuseStep 690439 = 1035659) B1035659
theorem B723259 : Blo 570811 723259 := bstep (se 1 (by rfl) ⟨542444, by rfl⟩ : syracuseStep 723259 = 1084889) B1084889
theorem B2984471 : Blo 570811 2984471 := bstep (se 1 (by rfl) ⟨2238353, by rfl⟩ : syracuseStep 2984471 = 4476707) B4476707
theorem B1084175 : Blo 570811 1084175 := bstep (se 1 (by rfl) ⟨813131, by rfl⟩ : syracuseStep 1084175 = 1626263) B1626263
theorem B723755 : Blo 570811 723755 := bstep (se 1 (by rfl) ⟨542816, by rfl⟩ : syracuseStep 723755 = 1085633) B1085633
theorem B1444979 : Blo 570811 1444979 := bstep (se 1 (by rfl) ⟨1083734, by rfl⟩ : syracuseStep 1444979 = 2167469) B2167469
theorem B1444999 : Blo 570811 1444999 := bstep (se 1 (by rfl) ⟨1083749, by rfl⟩ : syracuseStep 1444999 = 2167499) B2167499
theorem B2755757 : Blo 570811 2755757 := bstep (se 3 (by rfl) ⟨516704, by rfl⟩ : syracuseStep 2755757 = 1033409) B1033409
theorem B724231 : Blo 570811 724231 := bstep (se 1 (by rfl) ⟨543173, by rfl⟩ : syracuseStep 724231 = 1086347) B1086347
theorem B1936655 : Blo 570811 1936655 := bstep (se 1 (by rfl) ⟨1452491, by rfl⟩ : syracuseStep 1936655 = 2904983) B2904983
theorem B1445273 : Blo 570811 1445273 := bstep (se 2 (by rfl) ⟨541977, by rfl⟩ : syracuseStep 1445273 = 1083955) B1083955
theorem B1740217 : Blo 570811 1740217 := bstep (se 2 (by rfl) ⟨652581, by rfl⟩ : syracuseStep 1740217 = 1305163) B1305163
theorem B1936925 : Blo 570811 1936925 := bstep (se 3 (by rfl) ⟨363173, by rfl⟩ : syracuseStep 1936925 = 726347) B726347
theorem B1445435 : Blo 570811 1445435 := bstep (se 1 (by rfl) ⟨1084076, by rfl⟩ : syracuseStep 1445435 = 2168153) B2168153
theorem B1380041 : Blo 570811 1380041 := bstep (se 2 (by rfl) ⟨517515, by rfl⟩ : syracuseStep 1380041 = 1035031) B1035031
theorem B724727 : Blo 570811 724727 := bstep (se 1 (by rfl) ⟨543545, by rfl⟩ : syracuseStep 724727 = 1087091) B1087091
theorem B1445647 : Blo 570811 1445647 := bstep (se 1 (by rfl) ⟨1084235, by rfl⟩ : syracuseStep 1445647 = 2168471) B2168471
theorem B5279525 : Blo 570811 5279525 := bstep (se 4 (by rfl) ⟨494955, by rfl⟩ : syracuseStep 5279525 = 989911) B989911
theorem B724879 : Blo 570811 724879 := bstep (se 1 (by rfl) ⟨543659, by rfl⟩ : syracuseStep 724879 = 1087319) B1087319
theorem B1445921 : Blo 570811 1445921 := bstep (se 2 (by rfl) ⟨542220, by rfl⟩ : syracuseStep 1445921 = 1084441) B1084441
theorem B725051 : Blo 570811 725051 := bstep (se 1 (by rfl) ⟨543788, by rfl⟩ : syracuseStep 725051 = 1087577) B1087577
theorem B856235 : Blo 570811 856235 := bstep (se 1 (by rfl) ⟨642176, by rfl⟩ : syracuseStep 856235 = 1284353) B1284353
theorem B856265 : Blo 570811 856265 := bstep (se 2 (by rfl) ⟨321099, by rfl⟩ : syracuseStep 856265 = 642199) B642199
theorem B23433461 : Blo 570811 23433461 := bstep (se 5 (by rfl) ⟨1098443, by rfl⟩ : syracuseStep 23433461 = 2196887) B2196887
theorem B856379 : Blo 570811 856379 := bstep (se 1 (by rfl) ⟨642284, by rfl⟩ : syracuseStep 856379 = 1284569) B1284569
theorem B856439 : Blo 570811 856439 := bstep (se 1 (by rfl) ⟨642329, by rfl⟩ : syracuseStep 856439 = 1284659) B1284659
theorem B1085815 : Blo 570811 1085815 := bstep (se 1 (by rfl) ⟨814361, by rfl⟩ : syracuseStep 1085815 = 1628723) B1628723
theorem B856463 : Blo 570811 856463 := bstep (se 1 (by rfl) ⟨642347, by rfl⟩ : syracuseStep 856463 = 1284695) B1284695
theorem B856505 : Blo 570811 856505 := bstep (se 2 (by rfl) ⟨321189, by rfl⟩ : syracuseStep 856505 = 642379) B642379
theorem B1544633 : Blo 570811 1544633 := bstep (se 2 (by rfl) ⟨579237, by rfl⟩ : syracuseStep 1544633 = 1158475) B1158475
theorem B856583 : Blo 570811 856583 := bstep (se 1 (by rfl) ⟨642437, by rfl⟩ : syracuseStep 856583 = 1284875) B1284875
theorem B856619 : Blo 570811 856619 := bstep (se 1 (by rfl) ⟨642464, by rfl⟩ : syracuseStep 856619 = 1284929) B1284929
theorem B3707459 : Blo 570811 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B856649 : Blo 570811 856649 := bstep (se 2 (by rfl) ⟨321243, by rfl⟩ : syracuseStep 856649 = 642487) B642487
theorem B856763 : Blo 570811 856763 := bstep (se 1 (by rfl) ⟨642572, by rfl⟩ : syracuseStep 856763 = 1285145) B1285145
theorem B856823 : Blo 570811 856823 := bstep (se 1 (by rfl) ⟨642617, by rfl⟩ : syracuseStep 856823 = 1285235) B1285235
theorem B856847 : Blo 570811 856847 := bstep (se 1 (by rfl) ⟨642635, by rfl⟩ : syracuseStep 856847 = 1285271) B1285271
theorem B856889 : Blo 570811 856889 := bstep (se 2 (by rfl) ⟨321333, by rfl⟩ : syracuseStep 856889 = 642667) B642667
theorem B2167667 : Blo 570811 2167667 := bstep (se 1 (by rfl) ⟨1625750, by rfl⟩ : syracuseStep 2167667 = 3251501) B3251501
theorem B856967 : Blo 570811 856967 := bstep (se 1 (by rfl) ⟨642725, by rfl⟩ : syracuseStep 856967 = 1285451) B1285451
theorem B1938329 : Blo 570811 1938329 := bstep (se 2 (by rfl) ⟨726873, by rfl⟩ : syracuseStep 1938329 = 1453747) B1453747
theorem B857003 : Blo 570811 857003 := bstep (se 1 (by rfl) ⟨642752, by rfl⟩ : syracuseStep 857003 = 1285505) B1285505
theorem B857033 : Blo 570811 857033 := bstep (se 2 (by rfl) ⟨321387, by rfl⟩ : syracuseStep 857033 = 642775) B642775
theorem B726023 : Blo 570811 726023 := bstep (se 1 (by rfl) ⟨544517, by rfl⟩ : syracuseStep 726023 = 1089035) B1089035
theorem B1446923 : Blo 570811 1446923 := bstep (se 1 (by rfl) ⟨1085192, by rfl⟩ : syracuseStep 1446923 = 2170385) B2170385
theorem B857147 : Blo 570811 857147 := bstep (se 1 (by rfl) ⟨642860, by rfl⟩ : syracuseStep 857147 = 1285721) B1285721
theorem B857207 : Blo 570811 857207 := bstep (se 1 (by rfl) ⟨642905, by rfl⟩ : syracuseStep 857207 = 1285811) B1285811
theorem B1741943 : Blo 570811 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B857231 : Blo 570811 857231 := bstep (se 1 (by rfl) ⟨642923, by rfl⟩ : syracuseStep 857231 = 1285847) B1285847
theorem B857273 : Blo 570811 857273 := bstep (se 2 (by rfl) ⟨321477, by rfl⟩ : syracuseStep 857273 = 642955) B642955
theorem B4658413 : Blo 570811 4658413 := bstep (se 3 (by rfl) ⟨873452, by rfl⟩ : syracuseStep 4658413 = 1746905) B1746905
theorem B857351 : Blo 570811 857351 := bstep (se 1 (by rfl) ⟨643013, by rfl⟩ : syracuseStep 857351 = 1286027) B1286027
theorem B857387 : Blo 570811 857387 := bstep (se 1 (by rfl) ⟨643040, by rfl⟩ : syracuseStep 857387 = 1286081) B1286081
theorem B2069819 : Blo 570811 2069819 := bstep (se 1 (by rfl) ⟨1552364, by rfl⟩ : syracuseStep 2069819 = 3104729) B3104729
theorem B857417 : Blo 570811 857417 := bstep (se 2 (by rfl) ⟨321531, by rfl⟩ : syracuseStep 857417 = 643063) B643063
theorem B7968131 : Blo 570811 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B2069945 : Blo 570811 2069945 := bstep (se 2 (by rfl) ⟨776229, by rfl⟩ : syracuseStep 2069945 = 1552459) B1552459
theorem B857531 : Blo 570811 857531 := bstep (se 1 (by rfl) ⟨643148, by rfl⟩ : syracuseStep 857531 = 1286297) B1286297
theorem B857591 : Blo 570811 857591 := bstep (se 1 (by rfl) ⟨643193, by rfl⟩ : syracuseStep 857591 = 1286387) B1286387
theorem B857615 : Blo 570811 857615 := bstep (se 1 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 857615 = 1286423) B1286423
theorem B857657 : Blo 570811 857657 := bstep (se 2 (by rfl) ⟨321621, by rfl⟩ : syracuseStep 857657 = 643243) B643243
theorem B1939031 : Blo 570811 1939031 := bstep (se 1 (by rfl) ⟨1454273, by rfl⟩ : syracuseStep 1939031 = 2908547) B2908547
theorem B857735 : Blo 570811 857735 := bstep (se 1 (by rfl) ⟨643301, by rfl⟩ : syracuseStep 857735 = 1286603) B1286603
theorem B726671 : Blo 570811 726671 := bstep (se 1 (by rfl) ⟨545003, by rfl⟩ : syracuseStep 726671 = 1090007) B1090007
theorem B1447571 : Blo 570811 1447571 := bstep (se 1 (by rfl) ⟨1085678, by rfl⟩ : syracuseStep 1447571 = 2171357) B2171357
theorem B857771 : Blo 570811 857771 := bstep (se 1 (by rfl) ⟨643328, by rfl⟩ : syracuseStep 857771 = 1286657) B1286657
theorem B857801 : Blo 570811 857801 := bstep (se 2 (by rfl) ⟨321675, by rfl⟩ : syracuseStep 857801 = 643351) B643351
theorem B857915 : Blo 570811 857915 := bstep (se 1 (by rfl) ⟨643436, by rfl⟩ : syracuseStep 857915 = 1286873) B1286873
theorem B857975 : Blo 570811 857975 := bstep (se 1 (by rfl) ⟨643481, by rfl⟩ : syracuseStep 857975 = 1286963) B1286963
theorem B857999 : Blo 570811 857999 := bstep (se 1 (by rfl) ⟨643499, by rfl⟩ : syracuseStep 857999 = 1286999) B1286999
theorem B1447865 : Blo 570811 1447865 := bstep (se 2 (by rfl) ⟨542949, by rfl⟩ : syracuseStep 1447865 = 1085899) B1085899
theorem B858041 : Blo 570811 858041 := bstep (se 2 (by rfl) ⟨321765, by rfl⟩ : syracuseStep 858041 = 643531) B643531
theorem B858119 : Blo 570811 858119 := bstep (se 1 (by rfl) ⟨643589, by rfl⟩ : syracuseStep 858119 = 1287179) B1287179
theorem B858155 : Blo 570811 858155 := bstep (se 1 (by rfl) ⟨643616, by rfl⟩ : syracuseStep 858155 = 1287233) B1287233
theorem B1939517 : Blo 570811 1939517 := bstep (se 3 (by rfl) ⟨363659, by rfl⟩ : syracuseStep 1939517 = 727319) B727319
theorem B858185 : Blo 570811 858185 := bstep (se 2 (by rfl) ⟨321819, by rfl⟩ : syracuseStep 858185 = 643639) B643639
theorem B1087607 : Blo 570811 1087607 := bstep (se 1 (by rfl) ⟨815705, by rfl⟩ : syracuseStep 1087607 = 1631411) B1631411
theorem B858299 : Blo 570811 858299 := bstep (se 1 (by rfl) ⟨643724, by rfl⟩ : syracuseStep 858299 = 1287449) B1287449
theorem B858359 : Blo 570811 858359 := bstep (se 1 (by rfl) ⟨643769, by rfl⟩ : syracuseStep 858359 = 1287539) B1287539
theorem B858383 : Blo 570811 858383 := bstep (se 1 (by rfl) ⟨643787, by rfl⟩ : syracuseStep 858383 = 1287575) B1287575
theorem B1087759 : Blo 570811 1087759 := bstep (se 1 (by rfl) ⟨815819, by rfl⟩ : syracuseStep 1087759 = 1631639) B1631639
theorem B858425 : Blo 570811 858425 := bstep (se 2 (by rfl) ⟨321909, by rfl⟩ : syracuseStep 858425 = 643819) B643819
theorem B858503 : Blo 570811 858503 := bstep (se 1 (by rfl) ⟨643877, by rfl⟩ : syracuseStep 858503 = 1287755) B1287755
theorem B858539 : Blo 570811 858539 := bstep (se 1 (by rfl) ⟨643904, by rfl⟩ : syracuseStep 858539 = 1287809) B1287809
theorem B858569 : Blo 570811 858569 := bstep (se 2 (by rfl) ⟨321963, by rfl⟩ : syracuseStep 858569 = 643927) B643927
theorem B4364765 : Blo 570811 4364765 := bstep (se 3 (by rfl) ⟨818393, by rfl⟩ : syracuseStep 4364765 = 1636787) B1636787
theorem B1284623 : Blo 570811 1284623 := bstep (se 1 (by rfl) ⟨963467, by rfl⟩ : syracuseStep 1284623 = 1926935) B1926935
theorem B2759197 : Blo 570811 2759197 := bstep (se 3 (by rfl) ⟨517349, by rfl⟩ : syracuseStep 2759197 = 1034699) B1034699
theorem B1284641 : Blo 570811 1284641 := bstep (se 2 (by rfl) ⟨481740, by rfl⟩ : syracuseStep 1284641 = 963481) B963481
theorem B858683 : Blo 570811 858683 := bstep (se 1 (by rfl) ⟨644012, by rfl⟩ : syracuseStep 858683 = 1288025) B1288025
theorem B2202173 : Blo 570811 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B1448563 : Blo 570811 1448563 := bstep (se 1 (by rfl) ⟨1086422, by rfl⟩ : syracuseStep 1448563 = 2172845) B2172845
theorem B858743 : Blo 570811 858743 := bstep (se 1 (by rfl) ⟨644057, by rfl⟩ : syracuseStep 858743 = 1288115) B1288115
theorem B858767 : Blo 570811 858767 := bstep (se 1 (by rfl) ⟨644075, by rfl⟩ : syracuseStep 858767 = 1288151) B1288151
theorem B1088147 : Blo 570811 1088147 := bstep (se 1 (by rfl) ⟨816110, by rfl⟩ : syracuseStep 1088147 = 1632221) B1632221
theorem B858809 : Blo 570811 858809 := bstep (se 2 (by rfl) ⟨322053, by rfl⟩ : syracuseStep 858809 = 644107) B644107
theorem B1448705 : Blo 570811 1448705 := bstep (se 2 (by rfl) ⟨543264, by rfl⟩ : syracuseStep 1448705 = 1086529) B1086529
theorem B858887 : Blo 570811 858887 := bstep (se 1 (by rfl) ⟨644165, by rfl⟩ : syracuseStep 858887 = 1288331) B1288331
theorem B858923 : Blo 570811 858923 := bstep (se 1 (by rfl) ⟨644192, by rfl⟩ : syracuseStep 858923 = 1288385) B1288385
theorem B858953 : Blo 570811 858953 := bstep (se 2 (by rfl) ⟨322107, by rfl⟩ : syracuseStep 858953 = 644215) B644215
theorem B1284983 : Blo 570811 1284983 := bstep (se 1 (by rfl) ⟨963737, by rfl⟩ : syracuseStep 1284983 = 1927475) B1927475
theorem B1219475 : Blo 570811 1219475 := bstep (se 1 (by rfl) ⟨914606, by rfl⟩ : syracuseStep 1219475 = 1829213) B1829213
theorem B2202553 : Blo 570811 2202553 := bstep (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) B1651915
theorem B859067 : Blo 570811 859067 := bstep (se 1 (by rfl) ⟨644300, by rfl⟩ : syracuseStep 859067 = 1288601) B1288601
theorem B859127 : Blo 570811 859127 := bstep (se 1 (by rfl) ⟨644345, by rfl⟩ : syracuseStep 859127 = 1288691) B1288691
theorem B859151 : Blo 570811 859151 := bstep (se 1 (by rfl) ⟨644363, by rfl⟩ : syracuseStep 859151 = 1288727) B1288727
theorem B1285163 : Blo 570811 1285163 := bstep (se 1 (by rfl) ⟨963872, by rfl⟩ : syracuseStep 1285163 = 1927745) B1927745
theorem B2169899 : Blo 570811 2169899 := bstep (se 1 (by rfl) ⟨1627424, by rfl⟩ : syracuseStep 2169899 = 3254849) B3254849
theorem B859193 : Blo 570811 859193 := bstep (se 2 (by rfl) ⟨322197, by rfl⟩ : syracuseStep 859193 = 644395) B644395
theorem B859271 : Blo 570811 859271 := bstep (se 1 (by rfl) ⟨644453, by rfl⟩ : syracuseStep 859271 = 1288907) B1288907
theorem B859307 : Blo 570811 859307 := bstep (se 1 (by rfl) ⟨644480, by rfl⟩ : syracuseStep 859307 = 1288961) B1288961
theorem B1449161 : Blo 570811 1449161 := bstep (se 2 (by rfl) ⟨543435, by rfl⟩ : syracuseStep 1449161 = 1086871) B1086871
theorem B859337 : Blo 570811 859337 := bstep (se 2 (by rfl) ⟨322251, by rfl⟩ : syracuseStep 859337 = 644503) B644503
theorem B3087617 : Blo 570811 3087617 := bstep (se 2 (by rfl) ⟨1157856, by rfl⟩ : syracuseStep 3087617 = 2315713) B2315713
theorem B859451 : Blo 570811 859451 := bstep (se 1 (by rfl) ⟨644588, by rfl⟩ : syracuseStep 859451 = 1289177) B1289177
theorem B859511 : Blo 570811 859511 := bstep (se 1 (by rfl) ⟨644633, by rfl⟩ : syracuseStep 859511 = 1289267) B1289267
theorem B859535 : Blo 570811 859535 := bstep (se 1 (by rfl) ⟨644651, by rfl⟩ : syracuseStep 859535 = 1289303) B1289303
theorem B1285523 : Blo 570811 1285523 := bstep (se 1 (by rfl) ⟨964142, by rfl⟩ : syracuseStep 1285523 = 1928285) B1928285
theorem B859577 : Blo 570811 859577 := bstep (se 2 (by rfl) ⟨322341, by rfl⟩ : syracuseStep 859577 = 644683) B644683
theorem B1285577 : Blo 570811 1285577 := bstep (se 2 (by rfl) ⟨482091, by rfl⟩ : syracuseStep 1285577 = 964183) B964183
theorem B859655 : Blo 570811 859655 := bstep (se 1 (by rfl) ⟨644741, by rfl⟩ : syracuseStep 859655 = 1289483) B1289483
theorem B1449515 : Blo 570811 1449515 := bstep (se 1 (by rfl) ⟨1087136, by rfl⟩ : syracuseStep 1449515 = 2174273) B2174273
theorem B859691 : Blo 570811 859691 := bstep (se 1 (by rfl) ⟨644768, by rfl⟩ : syracuseStep 859691 = 1289537) B1289537
theorem B859721 : Blo 570811 859721 := bstep (se 2 (by rfl) ⟨322395, by rfl⟩ : syracuseStep 859721 = 644791) B644791
theorem B859835 : Blo 570811 859835 := bstep (se 1 (by rfl) ⟨644876, by rfl⟩ : syracuseStep 859835 = 1289753) B1289753
theorem B859895 : Blo 570811 859895 := bstep (se 1 (by rfl) ⟨644921, by rfl⟩ : syracuseStep 859895 = 1289843) B1289843
theorem B2793217 : Blo 570811 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B859919 : Blo 570811 859919 := bstep (se 1 (by rfl) ⟨644939, by rfl⟩ : syracuseStep 859919 = 1289879) B1289879
theorem B859961 : Blo 570811 859961 := bstep (se 2 (by rfl) ⟨322485, by rfl⟩ : syracuseStep 859961 = 644971) B644971
theorem B860039 : Blo 570811 860039 := bstep (se 1 (by rfl) ⟨645029, by rfl⟩ : syracuseStep 860039 = 1290059) B1290059
theorem B860075 : Blo 570811 860075 := bstep (se 1 (by rfl) ⟨645056, by rfl⟩ : syracuseStep 860075 = 1290113) B1290113
theorem B860105 : Blo 570811 860105 := bstep (se 2 (by rfl) ⟨322539, by rfl⟩ : syracuseStep 860105 = 645079) B645079
theorem B1089551 : Blo 570811 1089551 := bstep (se 1 (by rfl) ⟨817163, by rfl⟩ : syracuseStep 1089551 = 1634327) B1634327
theorem B860219 : Blo 570811 860219 := bstep (se 1 (by rfl) ⟨645164, by rfl⟩ : syracuseStep 860219 = 1290329) B1290329
theorem B860279 : Blo 570811 860279 := bstep (se 1 (by rfl) ⟨645209, by rfl⟩ : syracuseStep 860279 = 1290419) B1290419
theorem B1286279 : Blo 570811 1286279 := bstep (se 1 (by rfl) ⟨964709, by rfl⟩ : syracuseStep 1286279 = 1929419) B1929419
theorem B860303 : Blo 570811 860303 := bstep (se 1 (by rfl) ⟨645227, by rfl⟩ : syracuseStep 860303 = 1290455) B1290455
theorem B860345 : Blo 570811 860345 := bstep (se 2 (by rfl) ⟨322629, by rfl⟩ : syracuseStep 860345 = 645259) B645259
theorem B860423 : Blo 570811 860423 := bstep (se 1 (by rfl) ⟨645317, by rfl⟩ : syracuseStep 860423 = 1290635) B1290635
theorem B860459 : Blo 570811 860459 := bstep (se 1 (by rfl) ⟨645344, by rfl⟩ : syracuseStep 860459 = 1290689) B1290689
theorem B1286459 : Blo 570811 1286459 := bstep (se 1 (by rfl) ⟨964844, by rfl⟩ : syracuseStep 1286459 = 1929689) B1929689
theorem B860489 : Blo 570811 860489 := bstep (se 2 (by rfl) ⟨322683, by rfl⟩ : syracuseStep 860489 = 645367) B645367
theorem B2892185 : Blo 570811 2892185 := bstep (se 2 (by rfl) ⟨1084569, by rfl⟩ : syracuseStep 2892185 = 2169139) B2169139
theorem B1286585 : Blo 570811 1286585 := bstep (se 2 (by rfl) ⟨482469, by rfl⟩ : syracuseStep 1286585 = 964939) B964939
theorem B860603 : Blo 570811 860603 := bstep (se 1 (by rfl) ⟨645452, by rfl⟩ : syracuseStep 860603 = 1290905) B1290905
theorem B860663 : Blo 570811 860663 := bstep (se 1 (by rfl) ⟨645497, by rfl⟩ : syracuseStep 860663 = 1290995) B1290995
theorem B1450507 : Blo 570811 1450507 := bstep (se 1 (by rfl) ⟨1087880, by rfl⟩ : syracuseStep 1450507 = 2175761) B2175761
theorem B860687 : Blo 570811 860687 := bstep (se 1 (by rfl) ⟨645515, by rfl⟩ : syracuseStep 860687 = 1291031) B1291031
theorem B3482135 : Blo 570811 3482135 := bstep (se 1 (by rfl) ⟨2611601, by rfl⟩ : syracuseStep 3482135 = 5223203) B5223203
theorem B1090091 : Blo 570811 1090091 := bstep (se 1 (by rfl) ⟨817568, by rfl⟩ : syracuseStep 1090091 = 1635137) B1635137
theorem B860729 : Blo 570811 860729 := bstep (se 2 (by rfl) ⟨322773, by rfl⟩ : syracuseStep 860729 = 645547) B645547
theorem B860807 : Blo 570811 860807 := bstep (se 1 (by rfl) ⟨645605, by rfl⟩ : syracuseStep 860807 = 1291211) B1291211
theorem B1450649 : Blo 570811 1450649 := bstep (se 2 (by rfl) ⟨543993, by rfl⟩ : syracuseStep 1450649 = 1087987) B1087987
theorem B860843 : Blo 570811 860843 := bstep (se 1 (by rfl) ⟨645632, by rfl⟩ : syracuseStep 860843 = 1291265) B1291265
theorem B860873 : Blo 570811 860873 := bstep (se 2 (by rfl) ⟨322827, by rfl⟩ : syracuseStep 860873 = 645655) B645655
theorem B1286927 : Blo 570811 1286927 := bstep (se 1 (by rfl) ⟨965195, by rfl⟩ : syracuseStep 1286927 = 1930391) B1930391
theorem B1286945 : Blo 570811 1286945 := bstep (se 2 (by rfl) ⟨482604, by rfl⟩ : syracuseStep 1286945 = 965209) B965209
theorem B1450811 : Blo 570811 1450811 := bstep (se 1 (by rfl) ⟨1088108, by rfl⟩ : syracuseStep 1450811 = 2176217) B2176217
theorem B860987 : Blo 570811 860987 := bstep (se 1 (by rfl) ⟨645740, by rfl⟩ : syracuseStep 860987 = 1291481) B1291481
theorem B861047 : Blo 570811 861047 := bstep (se 1 (by rfl) ⟨645785, by rfl⟩ : syracuseStep 861047 = 1291571) B1291571
theorem B861071 : Blo 570811 861071 := bstep (se 1 (by rfl) ⟨645803, by rfl⟩ : syracuseStep 861071 = 1291607) B1291607
theorem B861113 : Blo 570811 861113 := bstep (se 2 (by rfl) ⟨322917, by rfl⟩ : syracuseStep 861113 = 645835) B645835
theorem B861191 : Blo 570811 861191 := bstep (se 1 (by rfl) ⟨645893, by rfl⟩ : syracuseStep 861191 = 1291787) B1291787
theorem B861227 : Blo 570811 861227 := bstep (se 1 (by rfl) ⟨645920, by rfl⟩ : syracuseStep 861227 = 1291841) B1291841
theorem B2761771 : Blo 570811 2761771 := bstep (se 1 (by rfl) ⟨2071328, by rfl⟩ : syracuseStep 2761771 = 4142657) B4142657
theorem B861257 : Blo 570811 861257 := bstep (se 2 (by rfl) ⟨322971, by rfl⟩ : syracuseStep 861257 = 645943) B645943
theorem B1287287 : Blo 570811 1287287 := bstep (se 1 (by rfl) ⟨965465, by rfl⟩ : syracuseStep 1287287 = 1930931) B1930931
theorem B1451155 : Blo 570811 1451155 := bstep (se 1 (by rfl) ⟨1088366, by rfl⟩ : syracuseStep 1451155 = 2176733) B2176733
theorem B861371 : Blo 570811 861371 := bstep (se 1 (by rfl) ⟨646028, by rfl⟩ : syracuseStep 861371 = 1292057) B1292057
theorem B3089609 : Blo 570811 3089609 := bstep (se 2 (by rfl) ⟨1158603, by rfl⟩ : syracuseStep 3089609 = 2317207) B2317207
theorem B861431 : Blo 570811 861431 := bstep (se 1 (by rfl) ⟨646073, by rfl⟩ : syracuseStep 861431 = 1292147) B1292147
theorem B861455 : Blo 570811 861455 := bstep (se 1 (by rfl) ⟨646091, by rfl⟩ : syracuseStep 861455 = 1292183) B1292183
theorem B1451297 : Blo 570811 1451297 := bstep (se 2 (by rfl) ⟨544236, by rfl⟩ : syracuseStep 1451297 = 1088473) B1088473
theorem B1287467 : Blo 570811 1287467 := bstep (se 1 (by rfl) ⟨965600, by rfl⟩ : syracuseStep 1287467 = 1931201) B1931201
theorem B861497 : Blo 570811 861497 := bstep (se 2 (by rfl) ⟨323061, by rfl⟩ : syracuseStep 861497 = 646123) B646123
theorem B2237755 : Blo 570811 2237755 := bstep (se 1 (by rfl) ⟨1678316, by rfl⟩ : syracuseStep 2237755 = 3356633) B3356633
theorem B11937125 : Blo 570811 11937125 := bstep (se 4 (by rfl) ⟨1119105, by rfl⟩ : syracuseStep 11937125 = 2238211) B2238211
theorem B861575 : Blo 570811 861575 := bstep (se 1 (by rfl) ⟨646181, by rfl⟩ : syracuseStep 861575 = 1292363) B1292363
theorem B861611 : Blo 570811 861611 := bstep (se 1 (by rfl) ⟨646208, by rfl⟩ : syracuseStep 861611 = 1292417) B1292417
theorem B861641 : Blo 570811 861641 := bstep (se 2 (by rfl) ⟨323115, by rfl⟩ : syracuseStep 861641 = 646231) B646231
theorem B861755 : Blo 570811 861755 := bstep (se 1 (by rfl) ⟨646316, by rfl⟩ : syracuseStep 861755 = 1292633) B1292633
theorem B861815 : Blo 570811 861815 := bstep (se 1 (by rfl) ⟨646361, by rfl⟩ : syracuseStep 861815 = 1292723) B1292723
theorem B1091207 : Blo 570811 1091207 := bstep (se 1 (by rfl) ⟨818405, by rfl⟩ : syracuseStep 1091207 = 1636811) B1636811
theorem B861839 : Blo 570811 861839 := bstep (se 1 (by rfl) ⟨646379, by rfl⟩ : syracuseStep 861839 = 1292759) B1292759
theorem B1287827 : Blo 570811 1287827 := bstep (se 1 (by rfl) ⟨965870, by rfl⟩ : syracuseStep 1287827 = 1931741) B1931741
theorem B698027 : Blo 570811 698027 := bstep (se 1 (by rfl) ⟨523520, by rfl⟩ : syracuseStep 698027 = 1047041) B1047041
theorem B861881 : Blo 570811 861881 := bstep (se 2 (by rfl) ⟨323205, by rfl⟩ : syracuseStep 861881 = 646411) B646411
theorem B1287881 : Blo 570811 1287881 := bstep (se 2 (by rfl) ⟨482955, by rfl⟩ : syracuseStep 1287881 = 965911) B965911
theorem B861959 : Blo 570811 861959 := bstep (se 1 (by rfl) ⟨646469, by rfl⟩ : syracuseStep 861959 = 1292939) B1292939
theorem B861995 : Blo 570811 861995 := bstep (se 1 (by rfl) ⟨646496, by rfl⟩ : syracuseStep 861995 = 1292993) B1292993
theorem B7939889 : Blo 570811 7939889 := bstep (se 2 (by rfl) ⟨2977458, by rfl⟩ : syracuseStep 7939889 = 5954917) B5954917
theorem B862025 : Blo 570811 862025 := bstep (se 2 (by rfl) ⟨323259, by rfl⟩ : syracuseStep 862025 = 646519) B646519
theorem B927607 : Blo 570811 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B862139 : Blo 570811 862139 := bstep (se 1 (by rfl) ⟨646604, by rfl⟩ : syracuseStep 862139 = 1293209) B1293209
theorem B862199 : Blo 570811 862199 := bstep (se 1 (by rfl) ⟨646649, by rfl⟩ : syracuseStep 862199 = 1293299) B1293299
theorem B1747129 : Blo 570811 1747129 := bstep (se 2 (by rfl) ⟨655173, by rfl⟩ : syracuseStep 1747129 = 1310347) B1310347
theorem B1452289 : Blo 570811 1452289 := bstep (se 2 (by rfl) ⟨544608, by rfl⟩ : syracuseStep 1452289 = 1089217) B1089217
theorem B1288583 : Blo 570811 1288583 := bstep (se 1 (by rfl) ⟨966437, by rfl⟩ : syracuseStep 1288583 = 1932875) B1932875
theorem B2173331 : Blo 570811 2173331 := bstep (se 1 (by rfl) ⟨1629998, by rfl⟩ : syracuseStep 2173331 = 3259997) B3259997
theorem B1223183 : Blo 570811 1223183 := bstep (se 1 (by rfl) ⟨917387, by rfl⟩ : syracuseStep 1223183 = 1834775) B1834775
theorem B1288763 : Blo 570811 1288763 := bstep (se 1 (by rfl) ⟨966572, by rfl⟩ : syracuseStep 1288763 = 1933145) B1933145
theorem B1223353 : Blo 570811 1223353 := bstep (se 2 (by rfl) ⟨458757, by rfl⟩ : syracuseStep 1223353 = 917515) B917515
theorem B1288889 : Blo 570811 1288889 := bstep (se 2 (by rfl) ⟨483333, by rfl⟩ : syracuseStep 1288889 = 966667) B966667
theorem B1649423 : Blo 570811 1649423 := bstep (se 1 (by rfl) ⟨1237067, by rfl⟩ : syracuseStep 1649423 = 2474135) B2474135
theorem B1452887 : Blo 570811 1452887 := bstep (se 1 (by rfl) ⟨1089665, by rfl⟩ : syracuseStep 1452887 = 2179331) B2179331
theorem B2894777 : Blo 570811 2894777 := bstep (se 2 (by rfl) ⟨1085541, by rfl⟩ : syracuseStep 2894777 = 2171083) B2171083
theorem B1223695 : Blo 570811 1223695 := bstep (se 1 (by rfl) ⟨917771, by rfl⟩ : syracuseStep 1223695 = 1835543) B1835543
theorem B1289231 : Blo 570811 1289231 := bstep (se 1 (by rfl) ⟨966923, by rfl⟩ : syracuseStep 1289231 = 1933847) B1933847
theorem B1289249 : Blo 570811 1289249 := bstep (se 2 (by rfl) ⟨483468, by rfl⟩ : syracuseStep 1289249 = 966937) B966937
theorem B1453099 : Blo 570811 1453099 := bstep (se 1 (by rfl) ⟨1089824, by rfl⟩ : syracuseStep 1453099 = 2179649) B2179649
theorem B1453241 : Blo 570811 1453241 := bstep (se 2 (by rfl) ⟨544965, by rfl⟩ : syracuseStep 1453241 = 1089931) B1089931
theorem B1289591 : Blo 570811 1289591 := bstep (se 1 (by rfl) ⟨967193, by rfl⟩ : syracuseStep 1289591 = 1934387) B1934387
theorem B1289771 : Blo 570811 1289771 := bstep (se 1 (by rfl) ⟨967328, by rfl⟩ : syracuseStep 1289771 = 1934657) B1934657
theorem B3255875 : Blo 570811 3255875 := bstep (se 1 (by rfl) ⟨2441906, by rfl⟩ : syracuseStep 3255875 = 4883813) B4883813
theorem B1290131 : Blo 570811 1290131 := bstep (se 1 (by rfl) ⟨967598, by rfl⟩ : syracuseStep 1290131 = 1935197) B1935197
theorem B3092377 : Blo 570811 3092377 := bstep (se 2 (by rfl) ⟨1159641, by rfl⟩ : syracuseStep 3092377 = 2319283) B2319283
theorem B1290185 : Blo 570811 1290185 := bstep (se 2 (by rfl) ⟨483819, by rfl⟩ : syracuseStep 1290185 = 967639) B967639
theorem B733303 : Blo 570811 733303 := bstep (se 1 (by rfl) ⟨549977, by rfl⟩ : syracuseStep 733303 = 1099955) B1099955
theorem B1224823 : Blo 570811 1224823 := bstep (se 1 (by rfl) ⟨918617, by rfl⟩ : syracuseStep 1224823 = 1837235) B1837235
theorem B1454233 : Blo 570811 1454233 := bstep (se 2 (by rfl) ⟨545337, by rfl⟩ : syracuseStep 1454233 = 1090675) B1090675
theorem B2896073 : Blo 570811 2896073 := bstep (se 2 (by rfl) ⟨1086027, by rfl⟩ : syracuseStep 2896073 = 2172055) B2172055
theorem B3092681 : Blo 570811 3092681 := bstep (se 2 (by rfl) ⟨1159755, by rfl⟩ : syracuseStep 3092681 = 2319511) B2319511
theorem B1454395 : Blo 570811 1454395 := bstep (se 1 (by rfl) ⟨1090796, by rfl⟩ : syracuseStep 1454395 = 2181593) B2181593
theorem B1454537 : Blo 570811 1454537 := bstep (se 2 (by rfl) ⟨545451, by rfl⟩ : syracuseStep 1454537 = 1090903) B1090903
theorem B1651259 : Blo 570811 1651259 := bstep (se 1 (by rfl) ⟨1238444, by rfl⟩ : syracuseStep 1651259 = 2476889) B2476889
theorem B7320131 : Blo 570811 7320131 := bstep (se 1 (by rfl) ⟨5490098, by rfl⟩ : syracuseStep 7320131 = 10980197) B10980197
theorem B1290887 : Blo 570811 1290887 := bstep (se 1 (by rfl) ⟨968165, by rfl⟩ : syracuseStep 1290887 = 1936331) B1936331
theorem B1454881 : Blo 570811 1454881 := bstep (se 2 (by rfl) ⟨545580, by rfl⟩ : syracuseStep 1454881 = 1091161) B1091161
theorem B1291067 : Blo 570811 1291067 := bstep (se 1 (by rfl) ⟨968300, by rfl⟩ : syracuseStep 1291067 = 1936601) B1936601
theorem B4338521 : Blo 570811 4338521 := bstep (se 2 (by rfl) ⟨1626945, by rfl⟩ : syracuseStep 4338521 = 3253891) B3253891
theorem B2175929 : Blo 570811 2175929 := bstep (se 2 (by rfl) ⟨815973, by rfl⟩ : syracuseStep 2175929 = 1631947) B1631947
theorem B1291193 : Blo 570811 1291193 := bstep (se 2 (by rfl) ⟨484197, by rfl⟩ : syracuseStep 1291193 = 968395) B968395
theorem B963643 : Blo 570811 963643 := bstep (se 1 (by rfl) ⟨722732, by rfl⟩ : syracuseStep 963643 = 1445465) B1445465
theorem B5518469 : Blo 570811 5518469 := bstep (se 4 (by rfl) ⟨517356, by rfl⟩ : syracuseStep 5518469 = 1034713) B1034713
theorem B963785 : Blo 570811 963785 := bstep (se 2 (by rfl) ⟨361419, by rfl⟩ : syracuseStep 963785 = 722839) B722839
theorem B1291535 : Blo 570811 1291535 := bstep (se 1 (by rfl) ⟨968651, by rfl⟩ : syracuseStep 1291535 = 1937303) B1937303
theorem B1291553 : Blo 570811 1291553 := bstep (se 2 (by rfl) ⟨484332, by rfl⟩ : syracuseStep 1291553 = 968665) B968665
theorem B570811 : Blo 570811 570811 := bstep (se 1 (by rfl) ⟨428108, by rfl⟩ : syracuseStep 570811 = 856217) B856217
theorem B570887 : Blo 570811 570887 := bstep (se 1 (by rfl) ⟨428165, by rfl⟩ : syracuseStep 570887 = 856331) B856331
theorem B570895 : Blo 570811 570895 := bstep (se 1 (by rfl) ⟨428171, by rfl⟩ : syracuseStep 570895 = 856343) B856343
theorem B570939 : Blo 570811 570939 := bstep (se 1 (by rfl) ⟨428204, by rfl⟩ : syracuseStep 570939 = 856409) B856409
theorem B1291895 : Blo 570811 1291895 := bstep (se 1 (by rfl) ⟨968921, by rfl⟩ : syracuseStep 1291895 = 1937843) B1937843
theorem B571015 : Blo 570811 571015 := bstep (se 1 (by rfl) ⟨428261, by rfl⟩ : syracuseStep 571015 = 856523) B856523
theorem B571023 : Blo 570811 571023 := bstep (se 1 (by rfl) ⟨428267, by rfl⟩ : syracuseStep 571023 = 856535) B856535
theorem B571067 : Blo 570811 571067 := bstep (se 1 (by rfl) ⟨428300, by rfl⟩ : syracuseStep 571067 = 856601) B856601
theorem B571143 : Blo 570811 571143 := bstep (se 1 (by rfl) ⟨428357, by rfl⟩ : syracuseStep 571143 = 856715) B856715
theorem B571151 : Blo 570811 571151 := bstep (se 1 (by rfl) ⟨428363, by rfl⟩ : syracuseStep 571151 = 856727) B856727
theorem B4339493 : Blo 570811 4339493 := bstep (se 4 (by rfl) ⟨406827, by rfl⟩ : syracuseStep 4339493 = 813655) B813655
theorem B1292075 : Blo 570811 1292075 := bstep (se 1 (by rfl) ⟨969056, by rfl⟩ : syracuseStep 1292075 = 1938113) B1938113
theorem B571195 : Blo 570811 571195 := bstep (se 1 (by rfl) ⟨428396, by rfl⟩ : syracuseStep 571195 = 856793) B856793
theorem B571271 : Blo 570811 571271 := bstep (se 1 (by rfl) ⟨428453, by rfl⟩ : syracuseStep 571271 = 856907) B856907
theorem B964487 : Blo 570811 964487 := bstep (se 1 (by rfl) ⟨723365, by rfl⟩ : syracuseStep 964487 = 1446731) B1446731
theorem B571279 : Blo 570811 571279 := bstep (se 1 (by rfl) ⟨428459, by rfl⟩ : syracuseStep 571279 = 856919) B856919
theorem B2176915 : Blo 570811 2176915 := bstep (se 1 (by rfl) ⟨1632686, by rfl⟩ : syracuseStep 2176915 = 3265373) B3265373
theorem B3258265 : Blo 570811 3258265 := bstep (se 2 (by rfl) ⟨1221849, by rfl⟩ : syracuseStep 3258265 = 2443699) B2443699
theorem B571323 : Blo 570811 571323 := bstep (se 1 (by rfl) ⟨428492, by rfl⟩ : syracuseStep 571323 = 856985) B856985
theorem B571399 : Blo 570811 571399 := bstep (se 1 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 571399 = 857099) B857099
theorem B571407 : Blo 570811 571407 := bstep (se 1 (by rfl) ⟨428555, by rfl⟩ : syracuseStep 571407 = 857111) B857111
theorem B571451 : Blo 570811 571451 := bstep (se 1 (by rfl) ⟨428588, by rfl⟩ : syracuseStep 571451 = 857177) B857177
theorem B571527 : Blo 570811 571527 := bstep (se 1 (by rfl) ⟨428645, by rfl⟩ : syracuseStep 571527 = 857291) B857291
theorem B571535 : Blo 570811 571535 := bstep (se 1 (by rfl) ⟨428651, by rfl⟩ : syracuseStep 571535 = 857303) B857303
theorem B1292435 : Blo 570811 1292435 := bstep (se 1 (by rfl) ⟨969326, by rfl⟩ : syracuseStep 1292435 = 1938653) B1938653
theorem B571579 : Blo 570811 571579 := bstep (se 1 (by rfl) ⟨428684, by rfl⟩ : syracuseStep 571579 = 857369) B857369
theorem B1292489 : Blo 570811 1292489 := bstep (se 2 (by rfl) ⟨484683, by rfl⟩ : syracuseStep 1292489 = 969367) B969367
theorem B571655 : Blo 570811 571655 := bstep (se 1 (by rfl) ⟨428741, by rfl⟩ : syracuseStep 571655 = 857483) B857483
theorem B571663 : Blo 570811 571663 := bstep (se 1 (by rfl) ⟨428747, by rfl⟩ : syracuseStep 571663 = 857495) B857495
theorem B571707 : Blo 570811 571707 := bstep (se 1 (by rfl) ⟨428780, by rfl⟩ : syracuseStep 571707 = 857561) B857561
theorem B571783 : Blo 570811 571783 := bstep (se 1 (by rfl) ⟨428837, by rfl⟩ : syracuseStep 571783 = 857675) B857675
theorem B571791 : Blo 570811 571791 := bstep (se 1 (by rfl) ⟨428843, by rfl⟩ : syracuseStep 571791 = 857687) B857687
theorem B3488147 : Blo 570811 3488147 := bstep (se 1 (by rfl) ⟨2616110, by rfl⟩ : syracuseStep 3488147 = 5232221) B5232221
theorem B6371731 : Blo 570811 6371731 := bstep (se 1 (by rfl) ⟨4778798, by rfl⟩ : syracuseStep 6371731 = 9557597) B9557597
theorem B571835 : Blo 570811 571835 := bstep (se 1 (by rfl) ⟨428876, by rfl⟩ : syracuseStep 571835 = 857753) B857753
theorem B571911 : Blo 570811 571911 := bstep (se 1 (by rfl) ⟨428933, by rfl⟩ : syracuseStep 571911 = 857867) B857867
theorem B571919 : Blo 570811 571919 := bstep (se 1 (by rfl) ⟨428939, by rfl⟩ : syracuseStep 571919 = 857879) B857879
theorem B965135 : Blo 570811 965135 := bstep (se 1 (by rfl) ⟨723851, by rfl⟩ : syracuseStep 965135 = 1447703) B1447703
theorem B571963 : Blo 570811 571963 := bstep (se 1 (by rfl) ⟨428972, by rfl⟩ : syracuseStep 571963 = 857945) B857945
theorem B3095101 : Blo 570811 3095101 := bstep (se 3 (by rfl) ⟨580331, by rfl⟩ : syracuseStep 3095101 = 1160663) B1160663
theorem B572039 : Blo 570811 572039 := bstep (se 1 (by rfl) ⟨429029, by rfl⟩ : syracuseStep 572039 = 858059) B858059
theorem B572047 : Blo 570811 572047 := bstep (se 1 (by rfl) ⟨429035, by rfl⟩ : syracuseStep 572047 = 858071) B858071
theorem B572091 : Blo 570811 572091 := bstep (se 1 (by rfl) ⟨429068, by rfl⟩ : syracuseStep 572091 = 858137) B858137
theorem B572167 : Blo 570811 572167 := bstep (se 1 (by rfl) ⟨429125, by rfl⟩ : syracuseStep 572167 = 858251) B858251
theorem B572175 : Blo 570811 572175 := bstep (se 1 (by rfl) ⟨429131, by rfl⟩ : syracuseStep 572175 = 858263) B858263
theorem B572219 : Blo 570811 572219 := bstep (se 1 (by rfl) ⟨429164, by rfl⟩ : syracuseStep 572219 = 858329) B858329
theorem B572295 : Blo 570811 572295 := bstep (se 1 (by rfl) ⟨429221, by rfl⟩ : syracuseStep 572295 = 858443) B858443
theorem B1293191 : Blo 570811 1293191 := bstep (se 1 (by rfl) ⟨969893, by rfl⟩ : syracuseStep 1293191 = 1939787) B1939787
theorem B572303 : Blo 570811 572303 := bstep (se 1 (by rfl) ⟨429227, by rfl⟩ : syracuseStep 572303 = 858455) B858455
theorem B572347 : Blo 570811 572347 := bstep (se 1 (by rfl) ⟨429260, by rfl⟩ : syracuseStep 572347 = 858521) B858521
theorem B2440145 : Blo 570811 2440145 := bstep (se 2 (by rfl) ⟨915054, by rfl⟩ : syracuseStep 2440145 = 1830109) B1830109
theorem B572423 : Blo 570811 572423 := bstep (se 1 (by rfl) ⟨429317, by rfl⟩ : syracuseStep 572423 = 858635) B858635
theorem B572431 : Blo 570811 572431 := bstep (se 1 (by rfl) ⟨429323, by rfl⟩ : syracuseStep 572431 = 858647) B858647
theorem B965675 : Blo 570811 965675 := bstep (se 1 (by rfl) ⟨724256, by rfl⟩ : syracuseStep 965675 = 1448513) B1448513
theorem B572475 : Blo 570811 572475 := bstep (se 1 (by rfl) ⟨429356, by rfl⟩ : syracuseStep 572475 = 858713) B858713
theorem B572551 : Blo 570811 572551 := bstep (se 1 (by rfl) ⟨429413, by rfl⟩ : syracuseStep 572551 = 858827) B858827
theorem B572559 : Blo 570811 572559 := bstep (se 1 (by rfl) ⟨429419, by rfl⟩ : syracuseStep 572559 = 858839) B858839
theorem B572603 : Blo 570811 572603 := bstep (se 1 (by rfl) ⟨429452, by rfl⟩ : syracuseStep 572603 = 858905) B858905
theorem B6208757 : Blo 570811 6208757 := bstep (se 5 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 6208757 = 582071) B582071
theorem B572679 : Blo 570811 572679 := bstep (se 1 (by rfl) ⟨429509, by rfl⟩ : syracuseStep 572679 = 859019) B859019
theorem B2931983 : Blo 570811 2931983 := bstep (se 1 (by rfl) ⟨2198987, by rfl⟩ : syracuseStep 2931983 = 4397975) B4397975
theorem B572687 : Blo 570811 572687 := bstep (se 1 (by rfl) ⟨429515, by rfl⟩ : syracuseStep 572687 = 859031) B859031
theorem B10992955 : Blo 570811 10992955 := bstep (se 1 (by rfl) ⟨8244716, by rfl⟩ : syracuseStep 10992955 = 16489433) B16489433
theorem B572731 : Blo 570811 572731 := bstep (se 1 (by rfl) ⟨429548, by rfl⟩ : syracuseStep 572731 = 859097) B859097
theorem B572807 : Blo 570811 572807 := bstep (se 1 (by rfl) ⟨429605, by rfl⟩ : syracuseStep 572807 = 859211) B859211
theorem B572815 : Blo 570811 572815 := bstep (se 1 (by rfl) ⟨429611, by rfl⟩ : syracuseStep 572815 = 859223) B859223
theorem B966073 : Blo 570811 966073 := bstep (se 2 (by rfl) ⟨362277, by rfl⟩ : syracuseStep 966073 = 724555) B724555
theorem B572859 : Blo 570811 572859 := bstep (se 1 (by rfl) ⟨429644, by rfl⟩ : syracuseStep 572859 = 859289) B859289
theorem B572935 : Blo 570811 572935 := bstep (se 1 (by rfl) ⟨429701, by rfl⟩ : syracuseStep 572935 = 859403) B859403
theorem B572943 : Blo 570811 572943 := bstep (se 1 (by rfl) ⟨429707, by rfl⟩ : syracuseStep 572943 = 859415) B859415
theorem B4898333 : Blo 570811 4898333 := bstep (se 3 (by rfl) ⟨918437, by rfl⟩ : syracuseStep 4898333 = 1836875) B1836875
theorem B572987 : Blo 570811 572987 := bstep (se 1 (by rfl) ⟨429740, by rfl⟩ : syracuseStep 572987 = 859481) B859481
theorem B2178647 : Blo 570811 2178647 := bstep (se 1 (by rfl) ⟨1633985, by rfl⟩ : syracuseStep 2178647 = 3267971) B3267971
theorem B573063 : Blo 570811 573063 := bstep (se 1 (by rfl) ⟨429797, by rfl⟩ : syracuseStep 573063 = 859595) B859595
theorem B573071 : Blo 570811 573071 := bstep (se 1 (by rfl) ⟨429803, by rfl⟩ : syracuseStep 573071 = 859607) B859607
theorem B573115 : Blo 570811 573115 := bstep (se 1 (by rfl) ⟨429836, by rfl⟩ : syracuseStep 573115 = 859673) B859673
theorem B573191 : Blo 570811 573191 := bstep (se 1 (by rfl) ⟨429893, by rfl⟩ : syracuseStep 573191 = 859787) B859787
theorem B573199 : Blo 570811 573199 := bstep (se 1 (by rfl) ⟨429899, by rfl⟩ : syracuseStep 573199 = 859799) B859799
theorem B573243 : Blo 570811 573243 := bstep (se 1 (by rfl) ⟨429932, by rfl⟩ : syracuseStep 573243 = 859865) B859865
theorem B3260249 : Blo 570811 3260249 := bstep (se 2 (by rfl) ⟨1222593, by rfl⟩ : syracuseStep 3260249 = 2445187) B2445187
theorem B573319 : Blo 570811 573319 := bstep (se 1 (by rfl) ⟨429989, by rfl⟩ : syracuseStep 573319 = 859979) B859979
theorem B573327 : Blo 570811 573327 := bstep (se 1 (by rfl) ⟨429995, by rfl⟩ : syracuseStep 573327 = 859991) B859991
theorem B573371 : Blo 570811 573371 := bstep (se 1 (by rfl) ⟨430028, by rfl⟩ : syracuseStep 573371 = 860057) B860057
theorem B5521355 : Blo 570811 5521355 := bstep (se 1 (by rfl) ⟨4141016, by rfl⟩ : syracuseStep 5521355 = 8282033) B8282033
theorem B573447 : Blo 570811 573447 := bstep (se 1 (by rfl) ⟨430085, by rfl⟩ : syracuseStep 573447 = 860171) B860171
theorem B2211851 : Blo 570811 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B573455 : Blo 570811 573455 := bstep (se 1 (by rfl) ⟨430091, by rfl⟩ : syracuseStep 573455 = 860183) B860183
theorem B573499 : Blo 570811 573499 := bstep (se 1 (by rfl) ⟨430124, by rfl⟩ : syracuseStep 573499 = 860249) B860249
theorem B2179133 : Blo 570811 2179133 := bstep (se 3 (by rfl) ⟨408587, by rfl⟩ : syracuseStep 2179133 = 817175) B817175
theorem B966775 : Blo 570811 966775 := bstep (se 1 (by rfl) ⟨725081, by rfl⟩ : syracuseStep 966775 = 1450163) B1450163
theorem B573575 : Blo 570811 573575 := bstep (se 1 (by rfl) ⟨430181, by rfl⟩ : syracuseStep 573575 = 860363) B860363
theorem B573583 : Blo 570811 573583 := bstep (se 1 (by rfl) ⟨430187, by rfl⟩ : syracuseStep 573583 = 860375) B860375
theorem B573627 : Blo 570811 573627 := bstep (se 1 (by rfl) ⟨430220, by rfl⟩ : syracuseStep 573627 = 860441) B860441
theorem B573703 : Blo 570811 573703 := bstep (se 1 (by rfl) ⟨430277, by rfl⟩ : syracuseStep 573703 = 860555) B860555
theorem B573711 : Blo 570811 573711 := bstep (se 1 (by rfl) ⟨430283, by rfl⟩ : syracuseStep 573711 = 860567) B860567
theorem B966971 : Blo 570811 966971 := bstep (se 1 (by rfl) ⟨725228, by rfl⟩ : syracuseStep 966971 = 1450457) B1450457
theorem B573755 : Blo 570811 573755 := bstep (se 1 (by rfl) ⟨430316, by rfl⟩ : syracuseStep 573755 = 860633) B860633
theorem B573831 : Blo 570811 573831 := bstep (se 1 (by rfl) ⟨430373, by rfl⟩ : syracuseStep 573831 = 860747) B860747
theorem B573839 : Blo 570811 573839 := bstep (se 1 (by rfl) ⟨430379, by rfl⟩ : syracuseStep 573839 = 860759) B860759
theorem B2474393 : Blo 570811 2474393 := bstep (se 2 (by rfl) ⟨927897, by rfl⟩ : syracuseStep 2474393 = 1855795) B1855795
theorem B573883 : Blo 570811 573883 := bstep (se 1 (by rfl) ⟨430412, by rfl⟩ : syracuseStep 573883 = 860825) B860825
theorem B573959 : Blo 570811 573959 := bstep (se 1 (by rfl) ⟨430469, by rfl⟩ : syracuseStep 573959 = 860939) B860939
theorem B1982987 : Blo 570811 1982987 := bstep (se 1 (by rfl) ⟨1487240, by rfl⟩ : syracuseStep 1982987 = 2974481) B2974481
theorem B573967 : Blo 570811 573967 := bstep (se 1 (by rfl) ⟨430475, by rfl⟩ : syracuseStep 573967 = 860951) B860951
theorem B2441771 : Blo 570811 2441771 := bstep (se 1 (by rfl) ⟨1831328, by rfl⟩ : syracuseStep 2441771 = 3662657) B3662657
theorem B574011 : Blo 570811 574011 := bstep (se 1 (by rfl) ⟨430508, by rfl⟩ : syracuseStep 574011 = 861017) B861017
theorem B574087 : Blo 570811 574087 := bstep (se 1 (by rfl) ⟨430565, by rfl⟩ : syracuseStep 574087 = 861131) B861131
theorem B574095 : Blo 570811 574095 := bstep (se 1 (by rfl) ⟨430571, by rfl⟩ : syracuseStep 574095 = 861143) B861143
theorem B574139 : Blo 570811 574139 := bstep (se 1 (by rfl) ⟨430604, by rfl⟩ : syracuseStep 574139 = 861209) B861209
theorem B967369 : Blo 570811 967369 := bstep (se 2 (by rfl) ⟨362763, by rfl⟩ : syracuseStep 967369 = 725527) B725527
theorem B574215 : Blo 570811 574215 := bstep (se 1 (by rfl) ⟨430661, by rfl⟩ : syracuseStep 574215 = 861323) B861323
theorem B574223 : Blo 570811 574223 := bstep (se 1 (by rfl) ⟨430667, by rfl⟩ : syracuseStep 574223 = 861335) B861335
theorem B574267 : Blo 570811 574267 := bstep (se 1 (by rfl) ⟨430700, by rfl⟩ : syracuseStep 574267 = 861401) B861401
theorem B574343 : Blo 570811 574343 := bstep (se 1 (by rfl) ⟨430757, by rfl⟩ : syracuseStep 574343 = 861515) B861515
theorem B574351 : Blo 570811 574351 := bstep (se 1 (by rfl) ⟨430763, by rfl⟩ : syracuseStep 574351 = 861527) B861527
theorem B574395 : Blo 570811 574395 := bstep (se 1 (by rfl) ⟨430796, by rfl⟩ : syracuseStep 574395 = 861593) B861593
theorem B1164233 : Blo 570811 1164233 := bstep (se 2 (by rfl) ⟨436587, by rfl⟩ : syracuseStep 1164233 = 873175) B873175
theorem B574471 : Blo 570811 574471 := bstep (se 1 (by rfl) ⟨430853, by rfl⟩ : syracuseStep 574471 = 861707) B861707
theorem B574479 : Blo 570811 574479 := bstep (se 1 (by rfl) ⟨430859, by rfl⟩ : syracuseStep 574479 = 861719) B861719
theorem B574523 : Blo 570811 574523 := bstep (se 1 (by rfl) ⟨430892, by rfl⟩ : syracuseStep 574523 = 861785) B861785
theorem B4899973 : Blo 570811 4899973 := bstep (se 4 (by rfl) ⟨459372, by rfl⟩ : syracuseStep 4899973 = 918745) B918745
theorem B574599 : Blo 570811 574599 := bstep (se 1 (by rfl) ⟨430949, by rfl⟩ : syracuseStep 574599 = 861899) B861899
theorem B574607 : Blo 570811 574607 := bstep (se 1 (by rfl) ⟨430955, by rfl⟩ : syracuseStep 574607 = 861911) B861911
theorem B574651 : Blo 570811 574651 := bstep (se 1 (by rfl) ⟨430988, by rfl⟩ : syracuseStep 574651 = 861977) B861977
theorem B574727 : Blo 570811 574727 := bstep (se 1 (by rfl) ⟨431045, by rfl⟩ : syracuseStep 574727 = 862091) B862091
theorem B3097871 : Blo 570811 3097871 := bstep (se 1 (by rfl) ⟨2323403, by rfl⟩ : syracuseStep 3097871 = 4646807) B4646807
theorem B574735 : Blo 570811 574735 := bstep (se 1 (by rfl) ⟨431051, by rfl⟩ : syracuseStep 574735 = 862103) B862103
theorem B574779 : Blo 570811 574779 := bstep (se 1 (by rfl) ⟨431084, by rfl⟩ : syracuseStep 574779 = 862169) B862169
theorem B968071 : Blo 570811 968071 := bstep (se 1 (by rfl) ⟨726053, by rfl⟩ : syracuseStep 968071 = 1452107) B1452107
theorem B869945 : Blo 570811 869945 := bstep (se 2 (by rfl) ⟨326229, by rfl⟩ : syracuseStep 869945 = 652459) B652459
theorem B2901905 : Blo 570811 2901905 := bstep (se 2 (by rfl) ⟨1088214, by rfl⟩ : syracuseStep 2901905 = 2176429) B2176429
theorem B1394585 : Blo 570811 1394585 := bstep (se 2 (by rfl) ⟨522969, by rfl⟩ : syracuseStep 1394585 = 1045939) B1045939
theorem B968719 : Blo 570811 968719 := bstep (se 1 (by rfl) ⟨726539, by rfl⟩ : syracuseStep 968719 = 1453079) B1453079
theorem B1657273 : Blo 570811 1657273 := bstep (se 2 (by rfl) ⟨621477, by rfl⟩ : syracuseStep 1657273 = 1242955) B1242955
theorem B969259 : Blo 570811 969259 := bstep (se 1 (by rfl) ⟨726944, by rfl⟩ : syracuseStep 969259 = 1453889) B1453889
theorem B969401 : Blo 570811 969401 := bstep (se 2 (by rfl) ⟨363525, by rfl⟩ : syracuseStep 969401 = 727051) B727051
theorem B772921 : Blo 570811 772921 := bstep (se 2 (by rfl) ⟨289845, by rfl⟩ : syracuseStep 772921 = 579691) B579691
theorem B3492887 : Blo 570811 3492887 := bstep (se 1 (by rfl) ⟨2619665, by rfl⟩ : syracuseStep 3492887 = 5239331) B5239331
theorem B1395755 : Blo 570811 1395755 := bstep (se 1 (by rfl) ⟨1046816, by rfl⟩ : syracuseStep 1395755 = 2093633) B2093633
theorem B642235 : Blo 570811 642235 := bstep (se 1 (by rfl) ⟨481676, by rfl⟩ : syracuseStep 642235 = 963353) B963353
theorem B63688037 : Blo 570811 63688037 := bstep (se 4 (by rfl) ⟨5970753, by rfl⟩ : syracuseStep 63688037 = 11941507) B11941507
theorem B2608537 : Blo 570811 2608537 := bstep (se 2 (by rfl) ⟨978201, by rfl⟩ : syracuseStep 2608537 = 1956403) B1956403
theorem B2936249 : Blo 570811 2936249 := bstep (se 2 (by rfl) ⟨1101093, by rfl⟩ : syracuseStep 2936249 = 2202187) B2202187
theorem B642703 : Blo 570811 642703 := bstep (se 1 (by rfl) ⟨482027, by rfl⟩ : syracuseStep 642703 = 964055) B964055
theorem B4902707 : Blo 570811 4902707 := bstep (se 1 (by rfl) ⟨3677030, by rfl⟩ : syracuseStep 4902707 = 7354061) B7354061
theorem B3264371 : Blo 570811 3264371 := bstep (se 1 (by rfl) ⟨2448278, by rfl⟩ : syracuseStep 3264371 = 4896557) B4896557
theorem B2445203 : Blo 570811 2445203 := bstep (se 1 (by rfl) ⟨1833902, by rfl⟩ : syracuseStep 2445203 = 3667805) B3667805
theorem B2904011 : Blo 570811 2904011 := bstep (se 1 (by rfl) ⟨2178008, by rfl⟩ : syracuseStep 2904011 = 4356017) B4356017
theorem B643207 : Blo 570811 643207 := bstep (se 1 (by rfl) ⟨482405, by rfl⟩ : syracuseStep 643207 = 964811) B964811
theorem B4116653 : Blo 570811 4116653 := bstep (se 3 (by rfl) ⟨771872, by rfl⟩ : syracuseStep 4116653 = 1543745) B1543745
theorem B2904335 : Blo 570811 2904335 := bstep (se 1 (by rfl) ⟨2178251, by rfl⟩ : syracuseStep 2904335 = 4356503) B4356503
theorem B643387 : Blo 570811 643387 := bstep (se 1 (by rfl) ⟨482540, by rfl⟩ : syracuseStep 643387 = 965081) B965081
theorem B4346297 : Blo 570811 4346297 := bstep (se 2 (by rfl) ⟨1629861, by rfl⟩ : syracuseStep 4346297 = 3259723) B3259723
theorem B610831 : Blo 570811 610831 := bstep (se 1 (by rfl) ⟨458123, by rfl⟩ : syracuseStep 610831 = 916247) B916247
theorem B6181555 : Blo 570811 6181555 := bstep (se 1 (by rfl) ⟨4636166, by rfl⟩ : syracuseStep 6181555 = 9272333) B9272333
theorem B643855 : Blo 570811 643855 := bstep (se 1 (by rfl) ⟨482891, by rfl⟩ : syracuseStep 643855 = 965783) B965783
theorem B611335 : Blo 570811 611335 := bstep (se 1 (by rfl) ⟨458501, by rfl⟩ : syracuseStep 611335 = 917003) B917003
theorem B644359 : Blo 570811 644359 := bstep (se 1 (by rfl) ⟨483269, by rfl⟩ : syracuseStep 644359 = 966539) B966539
theorem B3265829 : Blo 570811 3265829 := bstep (se 4 (by rfl) ⟨306171, by rfl⟩ : syracuseStep 3265829 = 612343) B612343
theorem B16504195 : Blo 570811 16504195 := bstep (se 1 (by rfl) ⟨12378146, by rfl⟩ : syracuseStep 16504195 = 24756293) B24756293
theorem B6509969 : Blo 570811 6509969 := bstep (se 2 (by rfl) ⟨2441238, by rfl⟩ : syracuseStep 6509969 = 4882477) B4882477
theorem B5952953 : Blo 570811 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B644539 : Blo 570811 644539 := bstep (se 1 (by rfl) ⟨483404, by rfl⟩ : syracuseStep 644539 = 966809) B966809
theorem B1955339 : Blo 570811 1955339 := bstep (se 1 (by rfl) ⟨1466504, by rfl⟩ : syracuseStep 1955339 = 2933009) B2933009
theorem B2905793 : Blo 570811 2905793 := bstep (se 2 (by rfl) ⟨1089672, by rfl⟩ : syracuseStep 2905793 = 2179345) B2179345
theorem B775927 : Blo 570811 775927 := bstep (se 1 (by rfl) ⟨581945, by rfl⟩ : syracuseStep 775927 = 1163891) B1163891
theorem B11032321 : Blo 570811 11032321 := bstep (se 2 (by rfl) ⟨4137120, by rfl⟩ : syracuseStep 11032321 = 8274241) B8274241
theorem B612155 : Blo 570811 612155 := bstep (se 1 (by rfl) ⟨459116, by rfl⟩ : syracuseStep 612155 = 918233) B918233
theorem B3921779 : Blo 570811 3921779 := bstep (se 1 (by rfl) ⟨2941334, by rfl⟩ : syracuseStep 3921779 = 5882669) B5882669
theorem B1628039 : Blo 570811 1628039 := bstep (se 1 (by rfl) ⟨1221029, by rfl⟩ : syracuseStep 1628039 = 2442059) B2442059
theorem B645007 : Blo 570811 645007 := bstep (se 1 (by rfl) ⟨483755, by rfl⟩ : syracuseStep 645007 = 967511) B967511
theorem B3266513 : Blo 570811 3266513 := bstep (se 2 (by rfl) ⟨1224942, by rfl⟩ : syracuseStep 3266513 = 2449885) B2449885
theorem B27121837 : Blo 570811 27121837 := bstep (se 3 (by rfl) ⟨5085344, by rfl⟩ : syracuseStep 27121837 = 10170689) B10170689
theorem B6641837 : Blo 570811 6641837 := bstep (se 3 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 6641837 = 2490689) B2490689
theorem B3266831 : Blo 570811 3266831 := bstep (se 1 (by rfl) ⟨2450123, by rfl⟩ : syracuseStep 3266831 = 4900247) B4900247
theorem B645511 : Blo 570811 645511 := bstep (se 1 (by rfl) ⟨484133, by rfl⟩ : syracuseStep 645511 = 968267) B968267
theorem B645691 : Blo 570811 645691 := bstep (se 1 (by rfl) ⟨484268, by rfl⟩ : syracuseStep 645691 = 968537) B968537
theorem B2448073 : Blo 570811 2448073 := bstep (se 2 (by rfl) ⟨918027, by rfl⟩ : syracuseStep 2448073 = 1836055) B1836055
theorem B2448143 : Blo 570811 2448143 := bstep (se 1 (by rfl) ⟨1836107, by rfl⟩ : syracuseStep 2448143 = 3672215) B3672215
theorem B5233423 : Blo 570811 5233423 := bstep (se 1 (by rfl) ⟨3925067, by rfl⟩ : syracuseStep 5233423 = 7850135) B7850135
theorem B2743091 : Blo 570811 2743091 := bstep (se 1 (by rfl) ⟨2057318, by rfl⟩ : syracuseStep 2743091 = 4114637) B4114637
theorem B2907089 : Blo 570811 2907089 := bstep (se 2 (by rfl) ⟨1090158, by rfl⟩ : syracuseStep 2907089 = 2180317) B2180317
theorem B646159 : Blo 570811 646159 := bstep (se 1 (by rfl) ⟨484619, by rfl⟩ : syracuseStep 646159 = 969239) B969239
theorem B646663 : Blo 570811 646663 := bstep (se 1 (by rfl) ⟨484997, by rfl⟩ : syracuseStep 646663 = 969995) B969995
theorem B6544961 : Blo 570811 6544961 := bstep (se 2 (by rfl) ⟨2454360, by rfl⟩ : syracuseStep 6544961 = 4908721) B4908721
theorem B3268289 : Blo 570811 3268289 := bstep (se 2 (by rfl) ⟨1225608, by rfl⟩ : syracuseStep 3268289 = 2451217) B2451217
theorem B1629953 : Blo 570811 1629953 := bstep (se 2 (by rfl) ⟨611232, by rfl⟩ : syracuseStep 1629953 = 1222465) B1222465
theorem B11198359 : Blo 570811 11198359 := bstep (se 1 (by rfl) ⟨8398769, by rfl⟩ : syracuseStep 11198359 = 16797539) B16797539
theorem B6512885 : Blo 570811 6512885 := bstep (se 5 (by rfl) ⟨305291, by rfl⟩ : syracuseStep 6512885 = 610583) B610583
theorem B1630523 : Blo 570811 1630523 := bstep (se 1 (by rfl) ⟨1222892, by rfl⟩ : syracuseStep 1630523 = 2445785) B2445785
theorem B1859993 : Blo 570811 1859993 := bstep (se 2 (by rfl) ⟨697497, by rfl⟩ : syracuseStep 1859993 = 1394995) B1394995
theorem B1630763 : Blo 570811 1630763 := bstep (se 1 (by rfl) ⟨1223072, by rfl⟩ : syracuseStep 1630763 = 2446145) B2446145
theorem B2745089 : Blo 570811 2745089 := bstep (se 2 (by rfl) ⟨1029408, by rfl⟩ : syracuseStep 2745089 = 2058817) B2058817
theorem B2909195 : Blo 570811 2909195 := bstep (se 1 (by rfl) ⟨2181896, by rfl⟩ : syracuseStep 2909195 = 4363793) B4363793
theorem B2450519 : Blo 570811 2450519 := bstep (se 1 (by rfl) ⟨1837889, by rfl⟩ : syracuseStep 2450519 = 3675779) B3675779
theorem B2909357 : Blo 570811 2909357 := bstep (se 3 (by rfl) ⟨545504, by rfl⟩ : syracuseStep 2909357 = 1091009) B1091009
theorem B2319769 : Blo 570811 2319769 := bstep (se 2 (by rfl) ⟨869913, by rfl⟩ : syracuseStep 2319769 = 1739827) B1739827
theorem B6383033 : Blo 570811 6383033 := bstep (se 2 (by rfl) ⟨2393637, by rfl⟩ : syracuseStep 6383033 = 4787275) B4787275
theorem B1467919 : Blo 570811 1467919 := bstep (se 1 (by rfl) ⟨1100939, by rfl⟩ : syracuseStep 1467919 = 2201879) B2201879
theorem B1927097 : Blo 570811 1927097 := bstep (se 2 (by rfl) ⟨722661, by rfl⟩ : syracuseStep 1927097 = 1445323) B1445323
theorem B6973613 : Blo 570811 6973613 := bstep (se 3 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 6973613 = 2615105) B2615105
theorem B813559 : Blo 570811 813559 := bstep (se 1 (by rfl) ⟨610169, by rfl⟩ : syracuseStep 813559 = 1220339) B1220339
theorem B1927691 : Blo 570811 1927691 := bstep (se 1 (by rfl) ⟨1445768, by rfl⟩ : syracuseStep 1927691 = 2891537) B2891537
theorem B1927799 : Blo 570811 1927799 := bstep (se 1 (by rfl) ⟨1445849, by rfl⟩ : syracuseStep 1927799 = 2891699) B2891699
theorem B813883 : Blo 570811 813883 := bstep (se 1 (by rfl) ⟨610412, by rfl⟩ : syracuseStep 813883 = 1220825) B1220825
theorem B5893181 : Blo 570811 5893181 := bstep (se 3 (by rfl) ⟨1104971, by rfl⟩ : syracuseStep 5893181 = 2209943) B2209943
theorem B1240183 : Blo 570811 1240183 := bstep (se 1 (by rfl) ⟨930137, by rfl⟩ : syracuseStep 1240183 = 1860275) B1860275
theorem B1174675 : Blo 570811 1174675 := bstep (se 1 (by rfl) ⟨881006, by rfl⟩ : syracuseStep 1174675 = 1762013) B1762013
theorem B1928393 : Blo 570811 1928393 := bstep (se 2 (by rfl) ⟨723147, by rfl⟩ : syracuseStep 1928393 = 1446295) B1446295
theorem B1306057 : Blo 570811 1306057 := bstep (se 2 (by rfl) ⟨489771, by rfl⟩ : syracuseStep 1306057 = 979543) B979543
theorem B2616785 : Blo 570811 2616785 := bstep (se 2 (by rfl) ⟨981294, by rfl⟩ : syracuseStep 2616785 = 1962589) B1962589
theorem B1371659 : Blo 570811 1371659 := bstep (se 1 (by rfl) ⟨1028744, by rfl⟩ : syracuseStep 1371659 = 2057489) B2057489
theorem B978475 : Blo 570811 978475 := bstep (se 1 (by rfl) ⟨733856, by rfl⟩ : syracuseStep 978475 = 1467713) B1467713
theorem B1929095 : Blo 570811 1929095 := bstep (se 1 (by rfl) ⟨1446821, by rfl⟩ : syracuseStep 1929095 = 2893643) B2893643
theorem B2715709 : Blo 570811 2715709 := bstep (se 3 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 2715709 = 1018391) B1018391
theorem B1929473 : Blo 570811 1929473 := bstep (se 2 (by rfl) ⟨723552, by rfl⟩ : syracuseStep 1929473 = 1447105) B1447105
theorem B3142547 : Blo 570811 3142547 := bstep (se 1 (by rfl) ⟨2356910, by rfl⟩ : syracuseStep 3142547 = 4713821) B4713821
theorem B2749393 : Blo 570811 2749393 := bstep (se 2 (by rfl) ⟨1031022, by rfl⟩ : syracuseStep 2749393 = 2062045) B2062045
theorem B1635329 : Blo 570811 1635329 := bstep (se 2 (by rfl) ⟨613248, by rfl⟩ : syracuseStep 1635329 = 1226497) B1226497
theorem B2749469 : Blo 570811 2749469 := bstep (se 3 (by rfl) ⟨515525, by rfl⟩ : syracuseStep 2749469 = 1031051) B1031051
theorem B1930283 : Blo 570811 1930283 := bstep (se 1 (by rfl) ⟨1447712, by rfl⟩ : syracuseStep 1930283 = 2895425) B2895425
theorem B914491 : Blo 570811 914491 := bstep (se 1 (by rfl) ⟨685868, by rfl⟩ : syracuseStep 914491 = 1371737) B1371737
theorem B816247 : Blo 570811 816247 := bstep (se 1 (by rfl) ⟨612185, by rfl⟩ : syracuseStep 816247 = 1224371) B1224371
theorem B1045793 : Blo 570811 1045793 := bstep (se 2 (by rfl) ⟨392172, by rfl⟩ : syracuseStep 1045793 = 784345) B784345
theorem B7337249 : Blo 570811 7337249 := bstep (se 2 (by rfl) ⟨2751468, by rfl⟩ : syracuseStep 7337249 = 5502937) B5502937
theorem B914747 : Blo 570811 914747 := bstep (se 1 (by rfl) ⟨686060, by rfl⟩ : syracuseStep 914747 = 1372121) B1372121
theorem B816571 : Blo 570811 816571 := bstep (se 1 (by rfl) ⟨612428, by rfl⟩ : syracuseStep 816571 = 1224857) B1224857
theorem B1635785 : Blo 570811 1635785 := bstep (se 2 (by rfl) ⟨613419, by rfl⟩ : syracuseStep 1635785 = 1226839) B1226839
theorem B6616525 : Blo 570811 6616525 := bstep (se 3 (by rfl) ⟨1240598, by rfl⟩ : syracuseStep 6616525 = 2481197) B2481197
theorem B1308203 : Blo 570811 1308203 := bstep (se 1 (by rfl) ⟨981152, by rfl⟩ : syracuseStep 1308203 = 1962305) B1962305
theorem B1373755 : Blo 570811 1373755 := bstep (se 1 (by rfl) ⟨1030316, by rfl⟩ : syracuseStep 1373755 = 2060633) B2060633
theorem B1373881 : Blo 570811 1373881 := bstep (se 2 (by rfl) ⟨515205, by rfl⟩ : syracuseStep 1373881 = 1030411) B1030411
theorem B1636139 : Blo 570811 1636139 := bstep (se 1 (by rfl) ⟨1227104, by rfl⟩ : syracuseStep 1636139 = 2454209) B2454209
theorem B817067 : Blo 570811 817067 := bstep (se 1 (by rfl) ⟨612800, by rfl⟩ : syracuseStep 817067 = 1225601) B1225601
theorem B620551 : Blo 570811 620551 := bstep (se 1 (by rfl) ⟨465413, by rfl⟩ : syracuseStep 620551 = 930827) B930827
theorem B2783243 : Blo 570811 2783243 := bstep (se 1 (by rfl) ⟨2087432, by rfl⟩ : syracuseStep 2783243 = 4174865) B4174865
theorem B1636537 : Blo 570811 1636537 := bstep (se 2 (by rfl) ⟨613701, by rfl⟩ : syracuseStep 1636537 = 1227403) B1227403
theorem B1931579 : Blo 570811 1931579 := bstep (se 1 (by rfl) ⟨1448684, by rfl⟩ : syracuseStep 1931579 = 2897369) B2897369
theorem B686479 : Blo 570811 686479 := bstep (se 1 (by rfl) ⟨514859, by rfl⟩ : syracuseStep 686479 = 1029719) B1029719
theorem B1309303 : Blo 570811 1309303 := bstep (se 1 (by rfl) ⟨981977, by rfl⟩ : syracuseStep 1309303 = 1963955) B1963955
theorem B10418959 : Blo 570811 10418959 := bstep (se 1 (by rfl) ⟨7814219, by rfl⟩ : syracuseStep 10418959 = 15628439) B15628439
theorem B1932065 : Blo 570811 1932065 := bstep (se 2 (by rfl) ⟨724524, by rfl⟩ : syracuseStep 1932065 = 1449049) B1449049
theorem B5503859 : Blo 570811 5503859 := bstep (se 1 (by rfl) ⟨4127894, by rfl⟩ : syracuseStep 5503859 = 8255789) B8255789
theorem B1932659 : Blo 570811 1932659 := bstep (se 1 (by rfl) ⟨1449494, by rfl⟩ : syracuseStep 1932659 = 2898989) B2898989
theorem B3472793 : Blo 570811 3472793 := bstep (se 2 (by rfl) ⟨1302297, by rfl⟩ : syracuseStep 3472793 = 2604595) B2604595
theorem B9305549 : Blo 570811 9305549 := bstep (se 3 (by rfl) ⟨1744790, by rfl⟩ : syracuseStep 9305549 = 3489581) B3489581
theorem B687863 : Blo 570811 687863 := bstep (se 1 (by rfl) ⟨515897, by rfl⟩ : syracuseStep 687863 = 1031795) B1031795
theorem B1376033 : Blo 570811 1376033 := bstep (se 2 (by rfl) ⟨516012, by rfl⟩ : syracuseStep 1376033 = 1032025) B1032025
theorem B1474363 : Blo 570811 1474363 := bstep (se 1 (by rfl) ⟨1105772, by rfl⟩ : syracuseStep 1474363 = 2211545) B2211545
theorem B1376119 : Blo 570811 1376119 := bstep (se 1 (by rfl) ⟨1032089, by rfl⟩ : syracuseStep 1376119 = 2064179) B2064179
theorem B982903 : Blo 570811 982903 := bstep (se 1 (by rfl) ⟨737177, by rfl⟩ : syracuseStep 982903 = 1474355) B1474355
theorem B786361 : Blo 570811 786361 := bstep (se 2 (by rfl) ⟨294885, by rfl⟩ : syracuseStep 786361 = 589771) B589771
theorem B5898269 : Blo 570811 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B3309605 : Blo 570811 3309605 := bstep (se 4 (by rfl) ⟨310275, by rfl⟩ : syracuseStep 3309605 = 620551) B620551
theorem B917561 : Blo 570811 917561 := bstep (se 2 (by rfl) ⟨344085, by rfl⟩ : syracuseStep 917561 = 688171) B688171
theorem B1933469 : Blo 570811 1933469 := bstep (se 3 (by rfl) ⟨362525, by rfl⟩ : syracuseStep 1933469 = 725051) B725051
theorem B1835389 : Blo 570811 1835389 := bstep (se 3 (by rfl) ⟨344135, by rfl⟩ : syracuseStep 1835389 = 688271) B688271
theorem B1934009 : Blo 570811 1934009 := bstep (se 2 (by rfl) ⟨725253, by rfl⟩ : syracuseStep 1934009 = 1450507) B1450507
theorem B2065247 : Blo 570811 2065247 := bstep (se 1 (by rfl) ⟨1548935, by rfl⟩ : syracuseStep 2065247 = 3097871) B3097871
theorem B1180559 : Blo 570811 1180559 := bstep (se 1 (by rfl) ⟨885419, by rfl⟩ : syracuseStep 1180559 = 1770839) B1770839
theorem B918535 : Blo 570811 918535 := bstep (se 1 (by rfl) ⟨688901, by rfl⟩ : syracuseStep 918535 = 1377803) B1377803
theorem B1934603 : Blo 570811 1934603 := bstep (se 1 (by rfl) ⟨1450952, by rfl⟩ : syracuseStep 1934603 = 2901905) B2901905
theorem B5506319 : Blo 570811 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B1934873 : Blo 570811 1934873 := bstep (se 2 (by rfl) ⟨725577, by rfl⟩ : syracuseStep 1934873 = 1451155) B1451155
theorem B2983673 : Blo 570811 2983673 := bstep (se 2 (by rfl) ⟨1118877, by rfl⟩ : syracuseStep 2983673 = 2237755) B2237755
theorem B722783 : Blo 570811 722783 := bstep (se 1 (by rfl) ⟨542087, by rfl⟩ : syracuseStep 722783 = 1084175) B1084175
theorem B1837171 : Blo 570811 1837171 := bstep (se 1 (by rfl) ⟨1377878, by rfl⟩ : syracuseStep 1837171 = 2755757) B2755757
theorem B920027 : Blo 570811 920027 := bstep (se 1 (by rfl) ⟨690020, by rfl⟩ : syracuseStep 920027 = 1380041) B1380041
theorem B1936007 : Blo 570811 1936007 := bstep (se 1 (by rfl) ⟨1452005, by rfl⟩ : syracuseStep 1936007 = 2904011) B2904011
theorem B4360877 : Blo 570811 4360877 := bstep (se 3 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 4360877 = 1635329) B1635329
theorem B1936061 : Blo 570811 1936061 := bstep (se 3 (by rfl) ⟨363011, by rfl⟩ : syracuseStep 1936061 = 726023) B726023
theorem B28314305 : Blo 570811 28314305 := bstep (se 2 (by rfl) ⟨10617864, by rfl⟩ : syracuseStep 28314305 = 21235729) B21235729
theorem B1936223 : Blo 570811 1936223 := bstep (se 1 (by rfl) ⟨1452167, by rfl⟩ : syracuseStep 1936223 = 2904335) B2904335
theorem B2329505 : Blo 570811 2329505 := bstep (se 2 (by rfl) ⟨873564, by rfl⟩ : syracuseStep 2329505 = 1747129) B1747129
theorem B1936385 : Blo 570811 1936385 := bstep (se 2 (by rfl) ⟨726144, by rfl⟩ : syracuseStep 1936385 = 1452289) B1452289
theorem B920585 : Blo 570811 920585 := bstep (se 2 (by rfl) ⟨345219, by rfl⟩ : syracuseStep 920585 = 690439) B690439
theorem B1445111 : Blo 570811 1445111 := bstep (se 1 (by rfl) ⟨1083833, by rfl⟩ : syracuseStep 1445111 = 2167667) B2167667
theorem B6982949 : Blo 570811 6982949 := bstep (se 4 (by rfl) ⟨654651, by rfl⟩ : syracuseStep 6982949 = 1309303) B1309303
theorem B1084745 : Blo 570811 1084745 := bstep (se 2 (by rfl) ⟨406779, by rfl⟩ : syracuseStep 1084745 = 813559) B813559
theorem B1379879 : Blo 570811 1379879 := bstep (se 1 (by rfl) ⟨1034909, by rfl⟩ : syracuseStep 1379879 = 2069819) B2069819
theorem B5312087 : Blo 570811 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B3968635 : Blo 570811 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B1379963 : Blo 570811 1379963 := bstep (se 1 (by rfl) ⟨1034972, by rfl⟩ : syracuseStep 1379963 = 2069945) B2069945
theorem B6524549 : Blo 570811 6524549 := bstep (se 4 (by rfl) ⟨611676, by rfl⟩ : syracuseStep 6524549 = 1223353) B1223353
theorem B6295261 : Blo 570811 6295261 := bstep (se 3 (by rfl) ⟨1180361, by rfl⟩ : syracuseStep 6295261 = 2360723) B2360723
theorem B1085177 : Blo 570811 1085177 := bstep (se 2 (by rfl) ⟨406941, by rfl⟩ : syracuseStep 1085177 = 813883) B813883
theorem B1937195 : Blo 570811 1937195 := bstep (se 1 (by rfl) ⟨1452896, by rfl⟩ : syracuseStep 1937195 = 2905793) B2905793
theorem B1937465 : Blo 570811 1937465 := bstep (se 2 (by rfl) ⟨726549, by rfl⟩ : syracuseStep 1937465 = 1453099) B1453099
theorem B4427891 : Blo 570811 4427891 := bstep (se 1 (by rfl) ⟨3320918, by rfl⟩ : syracuseStep 4427891 = 6641837) B6641837
theorem B856313 : Blo 570811 856313 := bstep (se 2 (by rfl) ⟨321117, by rfl⟩ : syracuseStep 856313 = 642235) B642235
theorem B856415 : Blo 570811 856415 := bstep (se 1 (by rfl) ⟨642311, by rfl⟩ : syracuseStep 856415 = 1284623) B1284623
theorem B856427 : Blo 570811 856427 := bstep (se 1 (by rfl) ⟨642320, by rfl⟩ : syracuseStep 856427 = 1284641) B1284641
theorem B1937789 : Blo 570811 1937789 := bstep (se 3 (by rfl) ⟨363335, by rfl⟩ : syracuseStep 1937789 = 726671) B726671
theorem B725431 : Blo 570811 725431 := bstep (se 1 (by rfl) ⟨544073, by rfl⟩ : syracuseStep 725431 = 1088147) B1088147
theorem B3478049 : Blo 570811 3478049 := bstep (se 2 (by rfl) ⟨1304268, by rfl⟩ : syracuseStep 3478049 = 2608537) B2608537
theorem B856655 : Blo 570811 856655 := bstep (se 1 (by rfl) ⟨642491, by rfl⟩ : syracuseStep 856655 = 1284983) B1284983
theorem B1741409 : Blo 570811 1741409 := bstep (se 2 (by rfl) ⟨653028, by rfl⟩ : syracuseStep 1741409 = 1306057) B1306057
theorem B1938059 : Blo 570811 1938059 := bstep (se 1 (by rfl) ⟨1453544, by rfl⟩ : syracuseStep 1938059 = 2907089) B2907089
theorem B856775 : Blo 570811 856775 := bstep (se 1 (by rfl) ⟨642581, by rfl⟩ : syracuseStep 856775 = 1285163) B1285163
theorem B1446599 : Blo 570811 1446599 := bstep (se 1 (by rfl) ⟨1084949, by rfl⟩ : syracuseStep 1446599 = 2169899) B2169899
theorem B856937 : Blo 570811 856937 := bstep (se 2 (by rfl) ⟨321351, by rfl⟩ : syracuseStep 856937 = 642703) B642703
theorem B857015 : Blo 570811 857015 := bstep (se 1 (by rfl) ⟨642761, by rfl⟩ : syracuseStep 857015 = 1285523) B1285523
theorem B857051 : Blo 570811 857051 := bstep (se 1 (by rfl) ⟨642788, by rfl⟩ : syracuseStep 857051 = 1285577) B1285577
theorem B4363307 : Blo 570811 4363307 := bstep (se 1 (by rfl) ⟨3272480, by rfl⟩ : syracuseStep 4363307 = 6544961) B6544961
theorem B1086635 : Blo 570811 1086635 := bstep (se 1 (by rfl) ⟨814976, by rfl⟩ : syracuseStep 1086635 = 1629953) B1629953
theorem B857519 : Blo 570811 857519 := bstep (se 1 (by rfl) ⟨643139, by rfl⟩ : syracuseStep 857519 = 1286279) B1286279
theorem B857609 : Blo 570811 857609 := bstep (se 2 (by rfl) ⟨321603, by rfl⟩ : syracuseStep 857609 = 643207) B643207
theorem B1938977 : Blo 570811 1938977 := bstep (se 2 (by rfl) ⟨727116, by rfl⟩ : syracuseStep 1938977 = 1454233) B1454233
theorem B857639 : Blo 570811 857639 := bstep (se 1 (by rfl) ⟨643229, by rfl⟩ : syracuseStep 857639 = 1286459) B1286459
theorem B1087015 : Blo 570811 1087015 := bstep (se 1 (by rfl) ⟨815261, by rfl⟩ : syracuseStep 1087015 = 1630523) B1630523
theorem B857723 : Blo 570811 857723 := bstep (se 1 (by rfl) ⟨643292, by rfl⟩ : syracuseStep 857723 = 1286585) B1286585
theorem B1087175 : Blo 570811 1087175 := bstep (se 1 (by rfl) ⟨815381, by rfl⟩ : syracuseStep 1087175 = 1630763) B1630763
theorem B726727 : Blo 570811 726727 := bstep (se 1 (by rfl) ⟨545045, by rfl⟩ : syracuseStep 726727 = 1090091) B1090091
theorem B857849 : Blo 570811 857849 := bstep (se 2 (by rfl) ⟨321693, by rfl⟩ : syracuseStep 857849 = 643387) B643387
theorem B1939193 : Blo 570811 1939193 := bstep (se 2 (by rfl) ⟨727197, by rfl⟩ : syracuseStep 1939193 = 1454395) B1454395
theorem B1447753 : Blo 570811 1447753 := bstep (se 2 (by rfl) ⟨542907, by rfl⟩ : syracuseStep 1447753 = 1085815) B1085815
theorem B857951 : Blo 570811 857951 := bstep (se 1 (by rfl) ⟨643463, by rfl⟩ : syracuseStep 857951 = 1286927) B1286927
theorem B857963 : Blo 570811 857963 := bstep (se 1 (by rfl) ⟨643472, by rfl⟩ : syracuseStep 857963 = 1286945) B1286945
theorem B1939463 : Blo 570811 1939463 := bstep (se 1 (by rfl) ⟨1454597, by rfl⟩ : syracuseStep 1939463 = 2909195) B2909195
theorem B858191 : Blo 570811 858191 := bstep (se 1 (by rfl) ⟨643643, by rfl⟩ : syracuseStep 858191 = 1287287) B1287287
theorem B1939571 : Blo 570811 1939571 := bstep (se 1 (by rfl) ⟨1454678, by rfl⟩ : syracuseStep 1939571 = 2909357) B2909357
theorem B858311 : Blo 570811 858311 := bstep (se 1 (by rfl) ⟨643733, by rfl⟩ : syracuseStep 858311 = 1287467) B1287467
theorem B858473 : Blo 570811 858473 := bstep (se 2 (by rfl) ⟨321927, by rfl⟩ : syracuseStep 858473 = 643855) B643855
theorem B1939841 : Blo 570811 1939841 := bstep (se 2 (by rfl) ⟨727440, by rfl⟩ : syracuseStep 1939841 = 1454881) B1454881
theorem B727471 : Blo 570811 727471 := bstep (se 1 (by rfl) ⟨545603, by rfl⟩ : syracuseStep 727471 = 1091207) B1091207
theorem B858551 : Blo 570811 858551 := bstep (se 1 (by rfl) ⟨643913, by rfl⟩ : syracuseStep 858551 = 1287827) B1287827
theorem B858587 : Blo 570811 858587 := bstep (se 1 (by rfl) ⟨643940, by rfl⟩ : syracuseStep 858587 = 1287881) B1287881
theorem B1284731 : Blo 570811 1284731 := bstep (se 1 (by rfl) ⟨963548, by rfl⟩ : syracuseStep 1284731 = 1927097) B1927097
theorem B1219321 : Blo 570811 1219321 := bstep (se 2 (by rfl) ⟨457245, by rfl⟩ : syracuseStep 1219321 = 914491) B914491
theorem B1284857 : Blo 570811 1284857 := bstep (se 2 (by rfl) ⟨481821, by rfl⟩ : syracuseStep 1284857 = 963643) B963643
theorem B1088329 : Blo 570811 1088329 := bstep (se 2 (by rfl) ⟨408123, by rfl⟩ : syracuseStep 1088329 = 816247) B816247
theorem B859055 : Blo 570811 859055 := bstep (se 1 (by rfl) ⟨644291, by rfl⟩ : syracuseStep 859055 = 1288583) B1288583
theorem B1448887 : Blo 570811 1448887 := bstep (se 1 (by rfl) ⟨1086665, by rfl⟩ : syracuseStep 1448887 = 2173331) B2173331
theorem B1285127 : Blo 570811 1285127 := bstep (se 1 (by rfl) ⟨963845, by rfl⟩ : syracuseStep 1285127 = 1927691) B1927691
theorem B859145 : Blo 570811 859145 := bstep (se 2 (by rfl) ⟨322179, by rfl⟩ : syracuseStep 859145 = 644359) B644359
theorem B859175 : Blo 570811 859175 := bstep (se 1 (by rfl) ⟨644381, by rfl⟩ : syracuseStep 859175 = 1288763) B1288763
theorem B1285199 : Blo 570811 1285199 := bstep (se 1 (by rfl) ⟨963899, by rfl⟩ : syracuseStep 1285199 = 1927799) B1927799
theorem B7445621 : Blo 570811 7445621 := bstep (se 5 (by rfl) ⟨349013, by rfl⟩ : syracuseStep 7445621 = 698027) B698027
theorem B859259 : Blo 570811 859259 := bstep (se 1 (by rfl) ⟨644444, by rfl⟩ : syracuseStep 859259 = 1288889) B1288889
theorem B859385 : Blo 570811 859385 := bstep (se 2 (by rfl) ⟨322269, by rfl⟩ : syracuseStep 859385 = 644539) B644539
theorem B8822033 : Blo 570811 8822033 := bstep (se 2 (by rfl) ⟨3308262, by rfl⟩ : syracuseStep 8822033 = 6616525) B6616525
theorem B859487 : Blo 570811 859487 := bstep (se 1 (by rfl) ⟨644615, by rfl⟩ : syracuseStep 859487 = 1289231) B1289231
theorem B859499 : Blo 570811 859499 := bstep (se 1 (by rfl) ⟨644624, by rfl⟩ : syracuseStep 859499 = 1289249) B1289249
theorem B4398461 : Blo 570811 4398461 := bstep (se 3 (by rfl) ⟨824711, by rfl⟩ : syracuseStep 4398461 = 1649423) B1649423
theorem B1285595 : Blo 570811 1285595 := bstep (se 1 (by rfl) ⟨964196, by rfl⟩ : syracuseStep 1285595 = 1928393) B1928393
theorem B859727 : Blo 570811 859727 := bstep (se 1 (by rfl) ⟨644795, by rfl⟩ : syracuseStep 859727 = 1289591) B1289591
theorem B1744523 : Blo 570811 1744523 := bstep (se 1 (by rfl) ⟨1308392, by rfl⟩ : syracuseStep 1744523 = 2616785) B2616785
theorem B859847 : Blo 570811 859847 := bstep (se 1 (by rfl) ⟨644885, by rfl⟩ : syracuseStep 859847 = 1289771) B1289771
theorem B2170583 : Blo 570811 2170583 := bstep (se 1 (by rfl) ⟨1627937, by rfl⟩ : syracuseStep 2170583 = 3255875) B3255875
theorem B3251933 : Blo 570811 3251933 := bstep (se 3 (by rfl) ⟨609737, by rfl⟩ : syracuseStep 3251933 = 1219475) B1219475
theorem B860009 : Blo 570811 860009 := bstep (se 2 (by rfl) ⟨322503, by rfl⟩ : syracuseStep 860009 = 645007) B645007
theorem B1286063 : Blo 570811 1286063 := bstep (se 1 (by rfl) ⟨964547, by rfl⟩ : syracuseStep 1286063 = 1929095) B1929095
theorem B860087 : Blo 570811 860087 := bstep (se 1 (by rfl) ⟨645065, by rfl⟩ : syracuseStep 860087 = 1290131) B1290131
theorem B860123 : Blo 570811 860123 := bstep (se 1 (by rfl) ⟨645092, by rfl⟩ : syracuseStep 860123 = 1290185) B1290185
theorem B9314365 : Blo 570811 9314365 := bstep (se 3 (by rfl) ⟨1746443, by rfl⟩ : syracuseStep 9314365 = 3492887) B3492887
theorem B1286315 : Blo 570811 1286315 := bstep (se 1 (by rfl) ⟨964736, by rfl⟩ : syracuseStep 1286315 = 1929473) B1929473
theorem B1450345 : Blo 570811 1450345 := bstep (se 2 (by rfl) ⟨543879, by rfl⟩ : syracuseStep 1450345 = 1087759) B1087759
theorem B860591 : Blo 570811 860591 := bstep (se 1 (by rfl) ⟨645443, by rfl⟩ : syracuseStep 860591 = 1290887) B1290887
theorem B860681 : Blo 570811 860681 := bstep (se 2 (by rfl) ⟨322755, by rfl⟩ : syracuseStep 860681 = 645511) B645511
theorem B8495641 : Blo 570811 8495641 := bstep (se 2 (by rfl) ⟨3185865, by rfl⟩ : syracuseStep 8495641 = 6371731) B6371731
theorem B860711 : Blo 570811 860711 := bstep (se 1 (by rfl) ⟨645533, by rfl⟩ : syracuseStep 860711 = 1291067) B1291067
theorem B2892347 : Blo 570811 2892347 := bstep (se 1 (by rfl) ⟨2169260, by rfl⟩ : syracuseStep 2892347 = 4338521) B4338521
theorem B1450619 : Blo 570811 1450619 := bstep (se 1 (by rfl) ⟨1087964, by rfl⟩ : syracuseStep 1450619 = 2175929) B2175929
theorem B860795 : Blo 570811 860795 := bstep (se 1 (by rfl) ⟨645596, by rfl⟩ : syracuseStep 860795 = 1291193) B1291193
theorem B8233645 : Blo 570811 8233645 := bstep (se 3 (by rfl) ⟨1543808, by rfl⟩ : syracuseStep 8233645 = 3087617) B3087617
theorem B1286855 : Blo 570811 1286855 := bstep (se 1 (by rfl) ⟨965141, by rfl⟩ : syracuseStep 1286855 = 1930283) B1930283
theorem B3678929 : Blo 570811 3678929 := bstep (se 2 (by rfl) ⟨1379598, by rfl⟩ : syracuseStep 3678929 = 2759197) B2759197
theorem B860921 : Blo 570811 860921 := bstep (se 2 (by rfl) ⟨322845, by rfl⟩ : syracuseStep 860921 = 645691) B645691
theorem B3678979 : Blo 570811 3678979 := bstep (se 1 (by rfl) ⟨2759234, by rfl⟩ : syracuseStep 3678979 = 5518469) B5518469
theorem B861023 : Blo 570811 861023 := bstep (se 1 (by rfl) ⟨645767, by rfl⟩ : syracuseStep 861023 = 1291535) B1291535
theorem B697195 : Blo 570811 697195 := bstep (se 1 (by rfl) ⟨522896, by rfl⟩ : syracuseStep 697195 = 1045793) B1045793
theorem B4891499 : Blo 570811 4891499 := bstep (se 1 (by rfl) ⟨3668624, by rfl⟩ : syracuseStep 4891499 = 7337249) B7337249
theorem B861035 : Blo 570811 861035 := bstep (se 1 (by rfl) ⟨645776, by rfl⟩ : syracuseStep 861035 = 1291553) B1291553
theorem B1090523 : Blo 570811 1090523 := bstep (se 1 (by rfl) ⟨817892, by rfl⟩ : syracuseStep 1090523 = 1635785) B1635785
theorem B861263 : Blo 570811 861263 := bstep (se 1 (by rfl) ⟨645947, by rfl⟩ : syracuseStep 861263 = 1291895) B1291895
theorem B2892995 : Blo 570811 2892995 := bstep (se 1 (by rfl) ⟨2169746, by rfl⟩ : syracuseStep 2892995 = 4339493) B4339493
theorem B861383 : Blo 570811 861383 := bstep (se 1 (by rfl) ⟨646037, by rfl⟩ : syracuseStep 861383 = 1292075) B1292075
theorem B1090759 : Blo 570811 1090759 := bstep (se 1 (by rfl) ⟨818069, by rfl⟩ : syracuseStep 1090759 = 1636139) B1636139
theorem B861545 : Blo 570811 861545 := bstep (se 2 (by rfl) ⟨323079, by rfl⟩ : syracuseStep 861545 = 646159) B646159
theorem B861623 : Blo 570811 861623 := bstep (se 1 (by rfl) ⟨646217, by rfl⟩ : syracuseStep 861623 = 1292435) B1292435
theorem B861659 : Blo 570811 861659 := bstep (se 1 (by rfl) ⟨646244, by rfl⟩ : syracuseStep 861659 = 1292489) B1292489
theorem B1287719 : Blo 570811 1287719 := bstep (se 1 (by rfl) ⟨965789, by rfl⟩ : syracuseStep 1287719 = 1931579) B1931579
theorem B14657273 : Blo 570811 14657273 := bstep (se 2 (by rfl) ⟨5496477, by rfl⟩ : syracuseStep 14657273 = 10992955) B10992955
theorem B1288043 : Blo 570811 1288043 := bstep (se 1 (by rfl) ⟨966032, by rfl⟩ : syracuseStep 1288043 = 1932065) B1932065
theorem B1288097 : Blo 570811 1288097 := bstep (se 2 (by rfl) ⟨483036, by rfl⟩ : syracuseStep 1288097 = 966073) B966073
theorem B862127 : Blo 570811 862127 := bstep (se 1 (by rfl) ⟨646595, by rfl⟩ : syracuseStep 862127 = 1293191) B1293191
theorem B862217 : Blo 570811 862217 := bstep (se 2 (by rfl) ⟨323331, by rfl⟩ : syracuseStep 862217 = 646663) B646663
theorem B4139171 : Blo 570811 4139171 := bstep (se 1 (by rfl) ⟨3104378, by rfl⟩ : syracuseStep 4139171 = 6208757) B6208757
theorem B1288439 : Blo 570811 1288439 := bstep (se 1 (by rfl) ⟨966329, by rfl⟩ : syracuseStep 1288439 = 1932659) B1932659
theorem B6203699 : Blo 570811 6203699 := bstep (se 1 (by rfl) ⟨4652774, by rfl⟩ : syracuseStep 6203699 = 9305549) B9305549
theorem B1452431 : Blo 570811 1452431 := bstep (se 1 (by rfl) ⟨1089323, by rfl⟩ : syracuseStep 1452431 = 2178647) B2178647
theorem B2173499 : Blo 570811 2173499 := bstep (se 1 (by rfl) ⟨1630124, by rfl⟩ : syracuseStep 2173499 = 3260249) B3260249
theorem B3680903 : Blo 570811 3680903 := bstep (se 1 (by rfl) ⟨2760677, by rfl⟩ : syracuseStep 3680903 = 5521355) B5521355
theorem B1452755 : Blo 570811 1452755 := bstep (se 1 (by rfl) ⟨1089566, by rfl⟩ : syracuseStep 1452755 = 2179133) B2179133
theorem B1289033 : Blo 570811 1289033 := bstep (se 2 (by rfl) ⟨483387, by rfl⟩ : syracuseStep 1289033 = 966775) B966775
theorem B1321991 : Blo 570811 1321991 := bstep (se 1 (by rfl) ⟨991493, by rfl⟩ : syracuseStep 1321991 = 1982987) B1982987
theorem B1223687 : Blo 570811 1223687 := bstep (se 1 (by rfl) ⟨917765, by rfl⟩ : syracuseStep 1223687 = 1835531) B1835531
theorem B3910949 : Blo 570811 3910949 := bstep (se 4 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 3910949 = 733303) B733303
theorem B1289825 : Blo 570811 1289825 := bstep (se 2 (by rfl) ⟨483684, by rfl⟩ : syracuseStep 1289825 = 967369) B967369
theorem B7319159 : Blo 570811 7319159 := bstep (se 1 (by rfl) ⟨5489369, by rfl⟩ : syracuseStep 7319159 = 10978739) B10978739
theorem B6598381 : Blo 570811 6598381 := bstep (se 3 (by rfl) ⟨1237196, by rfl⟩ : syracuseStep 6598381 = 2474393) B2474393
theorem B1290167 : Blo 570811 1290167 := bstep (se 1 (by rfl) ⟨967625, by rfl⟩ : syracuseStep 1290167 = 1935251) B1935251
theorem B929723 : Blo 570811 929723 := bstep (se 1 (by rfl) ⟨697292, by rfl⟩ : syracuseStep 929723 = 1394585) B1394585
theorem B3682361 : Blo 570811 3682361 := bstep (se 2 (by rfl) ⟨1380885, by rfl⟩ : syracuseStep 3682361 = 2761771) B2761771
theorem B1224875 : Blo 570811 1224875 := bstep (se 1 (by rfl) ⟨918656, by rfl⟩ : syracuseStep 1224875 = 1837313) B1837313
theorem B6533297 : Blo 570811 6533297 := bstep (se 2 (by rfl) ⟨2449986, by rfl⟩ : syracuseStep 6533297 = 4899973) B4899973
theorem B1290761 : Blo 570811 1290761 := bstep (se 2 (by rfl) ⟨484035, by rfl⟩ : syracuseStep 1290761 = 968071) B968071
theorem B930503 : Blo 570811 930503 := bstep (se 1 (by rfl) ⟨697877, by rfl⟩ : syracuseStep 930503 = 1395755) B1395755
theorem B963319 : Blo 570811 963319 := bstep (se 1 (by rfl) ⟨722489, by rfl⟩ : syracuseStep 963319 = 1444979) B1444979
theorem B1291103 : Blo 570811 1291103 := bstep (se 1 (by rfl) ⟨968327, by rfl⟩ : syracuseStep 1291103 = 1936655) B1936655
theorem B963515 : Blo 570811 963515 := bstep (se 1 (by rfl) ⟨722636, by rfl⟩ : syracuseStep 963515 = 1445273) B1445273
theorem B1291283 : Blo 570811 1291283 := bstep (se 1 (by rfl) ⟨968462, by rfl⟩ : syracuseStep 1291283 = 1936925) B1936925
theorem B963623 : Blo 570811 963623 := bstep (se 1 (by rfl) ⟨722717, by rfl⟩ : syracuseStep 963623 = 1445435) B1445435
theorem B3519683 : Blo 570811 3519683 := bstep (se 1 (by rfl) ⟨2639762, by rfl⟩ : syracuseStep 3519683 = 5279525) B5279525
theorem B2176247 : Blo 570811 2176247 := bstep (se 1 (by rfl) ⟨1632185, by rfl⟩ : syracuseStep 2176247 = 3264371) B3264371
theorem B963913 : Blo 570811 963913 := bstep (se 2 (by rfl) ⟨361467, by rfl⟩ : syracuseStep 963913 = 722935) B722935
theorem B1291625 : Blo 570811 1291625 := bstep (se 2 (by rfl) ⟨484359, by rfl⟩ : syracuseStep 1291625 = 968719) B968719
theorem B963947 : Blo 570811 963947 := bstep (se 1 (by rfl) ⟨722960, by rfl⟩ : syracuseStep 963947 = 1445921) B1445921
theorem B3257765 : Blo 570811 3257765 := bstep (se 4 (by rfl) ⟨305415, by rfl⟩ : syracuseStep 3257765 = 610831) B610831
theorem B570823 : Blo 570811 570823 := bstep (se 1 (by rfl) ⟨428117, by rfl⟩ : syracuseStep 570823 = 856235) B856235
theorem B570843 : Blo 570811 570843 := bstep (se 1 (by rfl) ⟨428132, by rfl⟩ : syracuseStep 570843 = 856265) B856265
theorem B570919 : Blo 570811 570919 := bstep (se 1 (by rfl) ⟨428189, by rfl⟩ : syracuseStep 570919 = 856379) B856379
theorem B570959 : Blo 570811 570959 := bstep (se 1 (by rfl) ⟨428219, by rfl⟩ : syracuseStep 570959 = 856439) B856439
theorem B570975 : Blo 570811 570975 := bstep (se 1 (by rfl) ⟨428231, by rfl⟩ : syracuseStep 570975 = 856463) B856463
theorem B571003 : Blo 570811 571003 := bstep (se 1 (by rfl) ⟨428252, by rfl⟩ : syracuseStep 571003 = 856505) B856505
theorem B1029755 : Blo 570811 1029755 := bstep (se 1 (by rfl) ⟨772316, by rfl⟩ : syracuseStep 1029755 = 1544633) B1544633
theorem B2897531 : Blo 570811 2897531 := bstep (se 1 (by rfl) ⟨2173148, by rfl⟩ : syracuseStep 2897531 = 4346297) B4346297
theorem B571055 : Blo 570811 571055 := bstep (se 1 (by rfl) ⟨428291, by rfl⟩ : syracuseStep 571055 = 856583) B856583
theorem B571079 : Blo 570811 571079 := bstep (se 1 (by rfl) ⟨428309, by rfl⟩ : syracuseStep 571079 = 856619) B856619
theorem B2471639 : Blo 570811 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B571099 : Blo 570811 571099 := bstep (se 1 (by rfl) ⟨428324, by rfl⟩ : syracuseStep 571099 = 856649) B856649
theorem B964345 : Blo 570811 964345 := bstep (se 2 (by rfl) ⟨361629, by rfl⟩ : syracuseStep 964345 = 723259) B723259
theorem B571175 : Blo 570811 571175 := bstep (se 1 (by rfl) ⟨428381, by rfl⟩ : syracuseStep 571175 = 856763) B856763
theorem B571215 : Blo 570811 571215 := bstep (se 1 (by rfl) ⟨428411, by rfl⟩ : syracuseStep 571215 = 856823) B856823
theorem B571231 : Blo 570811 571231 := bstep (se 1 (by rfl) ⟨428423, by rfl⟩ : syracuseStep 571231 = 856847) B856847
theorem B571259 : Blo 570811 571259 := bstep (se 1 (by rfl) ⟨428444, by rfl⟩ : syracuseStep 571259 = 856889) B856889
theorem B2209697 : Blo 570811 2209697 := bstep (se 2 (by rfl) ⟨828636, by rfl⟩ : syracuseStep 2209697 = 1657273) B1657273
theorem B571311 : Blo 570811 571311 := bstep (se 1 (by rfl) ⟨428483, by rfl⟩ : syracuseStep 571311 = 856967) B856967
theorem B1292219 : Blo 570811 1292219 := bstep (se 1 (by rfl) ⟨969164, by rfl⟩ : syracuseStep 1292219 = 1938329) B1938329
theorem B571335 : Blo 570811 571335 := bstep (se 1 (by rfl) ⟨428501, by rfl⟩ : syracuseStep 571335 = 857003) B857003
theorem B571355 : Blo 570811 571355 := bstep (se 1 (by rfl) ⟨428516, by rfl⟩ : syracuseStep 571355 = 857033) B857033
theorem B964615 : Blo 570811 964615 := bstep (se 1 (by rfl) ⟨723461, by rfl⟩ : syracuseStep 964615 = 1446923) B1446923
theorem B571431 : Blo 570811 571431 := bstep (se 1 (by rfl) ⟨428573, by rfl⟩ : syracuseStep 571431 = 857147) B857147
theorem B1292345 : Blo 570811 1292345 := bstep (se 2 (by rfl) ⟨484629, by rfl⟩ : syracuseStep 1292345 = 969259) B969259
theorem B571471 : Blo 570811 571471 := bstep (se 1 (by rfl) ⟨428603, by rfl⟩ : syracuseStep 571471 = 857207) B857207
theorem B571487 : Blo 570811 571487 := bstep (se 1 (by rfl) ⟨428615, by rfl⟩ : syracuseStep 571487 = 857231) B857231
theorem B571515 : Blo 570811 571515 := bstep (se 1 (by rfl) ⟨428636, by rfl⟩ : syracuseStep 571515 = 857273) B857273
theorem B2439325 : Blo 570811 2439325 := bstep (se 3 (by rfl) ⟨457373, by rfl⟩ : syracuseStep 2439325 = 914747) B914747
theorem B571567 : Blo 570811 571567 := bstep (se 1 (by rfl) ⟨428675, by rfl⟩ : syracuseStep 571567 = 857351) B857351
theorem B2177219 : Blo 570811 2177219 := bstep (se 1 (by rfl) ⟨1632914, by rfl⟩ : syracuseStep 2177219 = 3265829) B3265829
theorem B571591 : Blo 570811 571591 := bstep (se 1 (by rfl) ⟨428693, by rfl⟩ : syracuseStep 571591 = 857387) B857387
theorem B571611 : Blo 570811 571611 := bstep (se 1 (by rfl) ⟨428708, by rfl⟩ : syracuseStep 571611 = 857417) B857417
theorem B4339979 : Blo 570811 4339979 := bstep (se 1 (by rfl) ⟨3254984, by rfl⟩ : syracuseStep 4339979 = 6509969) B6509969
theorem B571687 : Blo 570811 571687 := bstep (se 1 (by rfl) ⟨428765, by rfl⟩ : syracuseStep 571687 = 857531) B857531
theorem B571727 : Blo 570811 571727 := bstep (se 1 (by rfl) ⟨428795, by rfl⟩ : syracuseStep 571727 = 857591) B857591
theorem B571743 : Blo 570811 571743 := bstep (se 1 (by rfl) ⟨428807, by rfl⟩ : syracuseStep 571743 = 857615) B857615
theorem B571771 : Blo 570811 571771 := bstep (se 1 (by rfl) ⟨428828, by rfl⟩ : syracuseStep 571771 = 857657) B857657
theorem B1292687 : Blo 570811 1292687 := bstep (se 1 (by rfl) ⟨969515, by rfl⟩ : syracuseStep 1292687 = 1939031) B1939031
theorem B571823 : Blo 570811 571823 := bstep (se 1 (by rfl) ⟨428867, by rfl⟩ : syracuseStep 571823 = 857735) B857735
theorem B965047 : Blo 570811 965047 := bstep (se 1 (by rfl) ⟨723785, by rfl⟩ : syracuseStep 965047 = 1447571) B1447571
theorem B571847 : Blo 570811 571847 := bstep (se 1 (by rfl) ⟨428885, by rfl⟩ : syracuseStep 571847 = 857771) B857771
theorem B571867 : Blo 570811 571867 := bstep (se 1 (by rfl) ⟨428900, by rfl⟩ : syracuseStep 571867 = 857801) B857801
theorem B571943 : Blo 570811 571943 := bstep (se 1 (by rfl) ⟨428957, by rfl⟩ : syracuseStep 571943 = 857915) B857915
theorem B571983 : Blo 570811 571983 := bstep (se 1 (by rfl) ⟨428987, by rfl⟩ : syracuseStep 571983 = 857975) B857975
theorem B571999 : Blo 570811 571999 := bstep (se 1 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 571999 = 857999) B857999
theorem B965243 : Blo 570811 965243 := bstep (se 1 (by rfl) ⟨723932, by rfl⟩ : syracuseStep 965243 = 1447865) B1447865
theorem B572027 : Blo 570811 572027 := bstep (se 1 (by rfl) ⟨429020, by rfl⟩ : syracuseStep 572027 = 858041) B858041
theorem B2177675 : Blo 570811 2177675 := bstep (se 1 (by rfl) ⟨1633256, by rfl⟩ : syracuseStep 2177675 = 3266513) B3266513
theorem B572079 : Blo 570811 572079 := bstep (se 1 (by rfl) ⟨429059, by rfl⟩ : syracuseStep 572079 = 858119) B858119
theorem B572103 : Blo 570811 572103 := bstep (se 1 (by rfl) ⟨429077, by rfl⟩ : syracuseStep 572103 = 858155) B858155
theorem B1293011 : Blo 570811 1293011 := bstep (se 1 (by rfl) ⟨969758, by rfl⟩ : syracuseStep 1293011 = 1939517) B1939517
theorem B572123 : Blo 570811 572123 := bstep (se 1 (by rfl) ⟨429092, by rfl⟩ : syracuseStep 572123 = 858185) B858185
theorem B572199 : Blo 570811 572199 := bstep (se 1 (by rfl) ⟨429149, by rfl⟩ : syracuseStep 572199 = 858299) B858299
theorem B1653577 : Blo 570811 1653577 := bstep (se 2 (by rfl) ⟨620091, by rfl⟩ : syracuseStep 1653577 = 1240183) B1240183
theorem B572239 : Blo 570811 572239 := bstep (se 1 (by rfl) ⟨429179, by rfl⟩ : syracuseStep 572239 = 858359) B858359
theorem B572255 : Blo 570811 572255 := bstep (se 1 (by rfl) ⟨429191, by rfl⟩ : syracuseStep 572255 = 858383) B858383
theorem B2177887 : Blo 570811 2177887 := bstep (se 1 (by rfl) ⟨1633415, by rfl⟩ : syracuseStep 2177887 = 3266831) B3266831
theorem B572283 : Blo 570811 572283 := bstep (se 1 (by rfl) ⟨429212, by rfl⟩ : syracuseStep 572283 = 858425) B858425
theorem B572335 : Blo 570811 572335 := bstep (se 1 (by rfl) ⟨429251, by rfl⟩ : syracuseStep 572335 = 858503) B858503
theorem B572359 : Blo 570811 572359 := bstep (se 1 (by rfl) ⟨429269, by rfl⟩ : syracuseStep 572359 = 858539) B858539
theorem B572379 : Blo 570811 572379 := bstep (se 1 (by rfl) ⟨429284, by rfl⟩ : syracuseStep 572379 = 858569) B858569
theorem B965641 : Blo 570811 965641 := bstep (se 2 (by rfl) ⟨362115, by rfl⟩ : syracuseStep 965641 = 724231) B724231
theorem B572455 : Blo 570811 572455 := bstep (se 1 (by rfl) ⟨429341, by rfl⟩ : syracuseStep 572455 = 858683) B858683
theorem B572495 : Blo 570811 572495 := bstep (se 1 (by rfl) ⟨429371, by rfl⟩ : syracuseStep 572495 = 858743) B858743
theorem B572511 : Blo 570811 572511 := bstep (se 1 (by rfl) ⟨429383, by rfl⟩ : syracuseStep 572511 = 858767) B858767
theorem B572539 : Blo 570811 572539 := bstep (se 1 (by rfl) ⟨429404, by rfl⟩ : syracuseStep 572539 = 858809) B858809
theorem B965803 : Blo 570811 965803 := bstep (se 1 (by rfl) ⟨724352, by rfl⟩ : syracuseStep 965803 = 1448705) B1448705
theorem B572591 : Blo 570811 572591 := bstep (se 1 (by rfl) ⟨429443, by rfl⟩ : syracuseStep 572591 = 858887) B858887
theorem B572615 : Blo 570811 572615 := bstep (se 1 (by rfl) ⟨429461, by rfl⟩ : syracuseStep 572615 = 858923) B858923
theorem B572635 : Blo 570811 572635 := bstep (se 1 (by rfl) ⟨429476, by rfl⟩ : syracuseStep 572635 = 858953) B858953
theorem B572711 : Blo 570811 572711 := bstep (se 1 (by rfl) ⟨429533, by rfl⟩ : syracuseStep 572711 = 859067) B859067
theorem B572751 : Blo 570811 572751 := bstep (se 1 (by rfl) ⟨429563, by rfl⟩ : syracuseStep 572751 = 859127) B859127
theorem B572767 : Blo 570811 572767 := bstep (se 1 (by rfl) ⟨429575, by rfl⟩ : syracuseStep 572767 = 859151) B859151
theorem B572795 : Blo 570811 572795 := bstep (se 1 (by rfl) ⟨429596, by rfl⟩ : syracuseStep 572795 = 859193) B859193
theorem B572847 : Blo 570811 572847 := bstep (se 1 (by rfl) ⟨429635, by rfl⟩ : syracuseStep 572847 = 859271) B859271
theorem B572871 : Blo 570811 572871 := bstep (se 1 (by rfl) ⟨429653, by rfl⟩ : syracuseStep 572871 = 859307) B859307
theorem B966107 : Blo 570811 966107 := bstep (se 1 (by rfl) ⟨724580, by rfl⟩ : syracuseStep 966107 = 1449161) B1449161
theorem B572891 : Blo 570811 572891 := bstep (se 1 (by rfl) ⟨429668, by rfl⟩ : syracuseStep 572891 = 859337) B859337
theorem B572967 : Blo 570811 572967 := bstep (se 1 (by rfl) ⟨429725, by rfl⟩ : syracuseStep 572967 = 859451) B859451
theorem B573007 : Blo 570811 573007 := bstep (se 1 (by rfl) ⟨429755, by rfl⟩ : syracuseStep 573007 = 859511) B859511
theorem B573023 : Blo 570811 573023 := bstep (se 1 (by rfl) ⟨429767, by rfl⟩ : syracuseStep 573023 = 859535) B859535
theorem B573051 : Blo 570811 573051 := bstep (se 1 (by rfl) ⟨429788, by rfl⟩ : syracuseStep 573051 = 859577) B859577
theorem B573103 : Blo 570811 573103 := bstep (se 1 (by rfl) ⟨429827, by rfl⟩ : syracuseStep 573103 = 859655) B859655
theorem B4341437 : Blo 570811 4341437 := bstep (se 3 (by rfl) ⟨814019, by rfl⟩ : syracuseStep 4341437 = 1628039) B1628039
theorem B966343 : Blo 570811 966343 := bstep (se 1 (by rfl) ⟨724757, by rfl⟩ : syracuseStep 966343 = 1449515) B1449515
theorem B573127 : Blo 570811 573127 := bstep (se 1 (by rfl) ⟨429845, by rfl⟩ : syracuseStep 573127 = 859691) B859691
theorem B573147 : Blo 570811 573147 := bstep (se 1 (by rfl) ⟨429860, by rfl⟩ : syracuseStep 573147 = 859721) B859721
theorem B2178845 : Blo 570811 2178845 := bstep (se 3 (by rfl) ⟨408533, by rfl⟩ : syracuseStep 2178845 = 817067) B817067
theorem B573223 : Blo 570811 573223 := bstep (se 1 (by rfl) ⟨429917, by rfl⟩ : syracuseStep 573223 = 859835) B859835
theorem B2178859 : Blo 570811 2178859 := bstep (se 1 (by rfl) ⟨1634144, by rfl⟩ : syracuseStep 2178859 = 3268289) B3268289
theorem B573263 : Blo 570811 573263 := bstep (se 1 (by rfl) ⟨429947, by rfl⟩ : syracuseStep 573263 = 859895) B859895
theorem B573279 : Blo 570811 573279 := bstep (se 1 (by rfl) ⟨429959, by rfl⟩ : syracuseStep 573279 = 859919) B859919
theorem B966505 : Blo 570811 966505 := bstep (se 2 (by rfl) ⟨362439, by rfl⟩ : syracuseStep 966505 = 724879) B724879
theorem B573307 : Blo 570811 573307 := bstep (se 1 (by rfl) ⟨429980, by rfl⟩ : syracuseStep 573307 = 859961) B859961
theorem B573359 : Blo 570811 573359 := bstep (se 1 (by rfl) ⟨430019, by rfl⟩ : syracuseStep 573359 = 860039) B860039
theorem B573383 : Blo 570811 573383 := bstep (se 1 (by rfl) ⟨430037, by rfl⟩ : syracuseStep 573383 = 860075) B860075
theorem B573403 : Blo 570811 573403 := bstep (se 1 (by rfl) ⟨430052, by rfl⟩ : syracuseStep 573403 = 860105) B860105
theorem B573479 : Blo 570811 573479 := bstep (se 1 (by rfl) ⟨430109, by rfl⟩ : syracuseStep 573479 = 860219) B860219
theorem B573519 : Blo 570811 573519 := bstep (se 1 (by rfl) ⟨430139, by rfl⟩ : syracuseStep 573519 = 860279) B860279
theorem B3620945 : Blo 570811 3620945 := bstep (se 2 (by rfl) ⟨1357854, by rfl⟩ : syracuseStep 3620945 = 2715709) B2715709
theorem B573535 : Blo 570811 573535 := bstep (se 1 (by rfl) ⟨430151, by rfl⟩ : syracuseStep 573535 = 860303) B860303
theorem B14631029 : Blo 570811 14631029 := bstep (se 5 (by rfl) ⟨685829, by rfl⟩ : syracuseStep 14631029 = 1371659) B1371659
theorem B573563 : Blo 570811 573563 := bstep (se 1 (by rfl) ⟨430172, by rfl⟩ : syracuseStep 573563 = 860345) B860345
theorem B4341923 : Blo 570811 4341923 := bstep (se 1 (by rfl) ⟨3256442, by rfl⟩ : syracuseStep 4341923 = 6512885) B6512885
theorem B573615 : Blo 570811 573615 := bstep (se 1 (by rfl) ⟨430211, by rfl⟩ : syracuseStep 573615 = 860423) B860423
theorem B573639 : Blo 570811 573639 := bstep (se 1 (by rfl) ⟨430229, by rfl⟩ : syracuseStep 573639 = 860459) B860459
theorem B573659 : Blo 570811 573659 := bstep (se 1 (by rfl) ⟨430244, by rfl⟩ : syracuseStep 573659 = 860489) B860489
theorem B573735 : Blo 570811 573735 := bstep (se 1 (by rfl) ⟨430301, by rfl⟩ : syracuseStep 573735 = 860603) B860603
theorem B2900285 : Blo 570811 2900285 := bstep (se 3 (by rfl) ⟨543803, by rfl⟩ : syracuseStep 2900285 = 1087607) B1087607
theorem B573775 : Blo 570811 573775 := bstep (se 1 (by rfl) ⟨430331, by rfl⟩ : syracuseStep 573775 = 860663) B860663
theorem B573791 : Blo 570811 573791 := bstep (se 1 (by rfl) ⟨430343, by rfl⟩ : syracuseStep 573791 = 860687) B860687
theorem B573819 : Blo 570811 573819 := bstep (se 1 (by rfl) ⟨430364, by rfl⟩ : syracuseStep 573819 = 860729) B860729
theorem B573871 : Blo 570811 573871 := bstep (se 1 (by rfl) ⟨430403, by rfl⟩ : syracuseStep 573871 = 860807) B860807
theorem B967099 : Blo 570811 967099 := bstep (se 1 (by rfl) ⟨725324, by rfl⟩ : syracuseStep 967099 = 1450649) B1450649
theorem B573895 : Blo 570811 573895 := bstep (se 1 (by rfl) ⟨430421, by rfl⟩ : syracuseStep 573895 = 860843) B860843
theorem B573915 : Blo 570811 573915 := bstep (se 1 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 573915 = 860873) B860873
theorem B967207 : Blo 570811 967207 := bstep (se 1 (by rfl) ⟨725405, by rfl⟩ : syracuseStep 967207 = 1450811) B1450811
theorem B573991 : Blo 570811 573991 := bstep (se 1 (by rfl) ⟨430493, by rfl⟩ : syracuseStep 573991 = 860987) B860987
theorem B574031 : Blo 570811 574031 := bstep (se 1 (by rfl) ⟨430523, by rfl⟩ : syracuseStep 574031 = 861047) B861047
theorem B574047 : Blo 570811 574047 := bstep (se 1 (by rfl) ⟨430535, by rfl⟩ : syracuseStep 574047 = 861071) B861071
theorem B574075 : Blo 570811 574075 := bstep (se 1 (by rfl) ⟨430556, by rfl⟩ : syracuseStep 574075 = 861113) B861113
theorem B574127 : Blo 570811 574127 := bstep (se 1 (by rfl) ⟨430595, by rfl⟩ : syracuseStep 574127 = 861191) B861191
theorem B574151 : Blo 570811 574151 := bstep (se 1 (by rfl) ⟨430613, by rfl⟩ : syracuseStep 574151 = 861227) B861227
theorem B574171 : Blo 570811 574171 := bstep (se 1 (by rfl) ⟨430628, by rfl⟩ : syracuseStep 574171 = 861257) B861257
theorem B574247 : Blo 570811 574247 := bstep (se 1 (by rfl) ⟨430685, by rfl⟩ : syracuseStep 574247 = 861371) B861371
theorem B574287 : Blo 570811 574287 := bstep (se 1 (by rfl) ⟨430715, by rfl⟩ : syracuseStep 574287 = 861431) B861431
theorem B574303 : Blo 570811 574303 := bstep (se 1 (by rfl) ⟨430727, by rfl⟩ : syracuseStep 574303 = 861455) B861455
theorem B967531 : Blo 570811 967531 := bstep (se 1 (by rfl) ⟨725648, by rfl⟩ : syracuseStep 967531 = 1451297) B1451297
theorem B574331 : Blo 570811 574331 := bstep (se 1 (by rfl) ⟨430748, by rfl⟩ : syracuseStep 574331 = 861497) B861497
theorem B8242073 : Blo 570811 8242073 := bstep (se 2 (by rfl) ⟨3090777, by rfl⟩ : syracuseStep 8242073 = 6181555) B6181555
theorem B574383 : Blo 570811 574383 := bstep (se 1 (by rfl) ⟨430787, by rfl⟩ : syracuseStep 574383 = 861575) B861575
theorem B574407 : Blo 570811 574407 := bstep (se 1 (by rfl) ⟨430805, by rfl⟩ : syracuseStep 574407 = 861611) B861611
theorem B574427 : Blo 570811 574427 := bstep (se 1 (by rfl) ⟨430820, by rfl⟩ : syracuseStep 574427 = 861641) B861641
theorem B574503 : Blo 570811 574503 := bstep (se 1 (by rfl) ⟨430877, by rfl⟩ : syracuseStep 574503 = 861755) B861755
theorem B574543 : Blo 570811 574543 := bstep (se 1 (by rfl) ⟨430907, by rfl⟩ : syracuseStep 574543 = 861815) B861815
theorem B574559 : Blo 570811 574559 := bstep (se 1 (by rfl) ⟨430919, by rfl⟩ : syracuseStep 574559 = 861839) B861839
theorem B574587 : Blo 570811 574587 := bstep (se 1 (by rfl) ⟨430940, by rfl⟩ : syracuseStep 574587 = 861881) B861881
theorem B574639 : Blo 570811 574639 := bstep (se 1 (by rfl) ⟨430979, by rfl⟩ : syracuseStep 574639 = 861959) B861959
theorem B574663 : Blo 570811 574663 := bstep (se 1 (by rfl) ⟨430997, by rfl⟩ : syracuseStep 574663 = 861995) B861995
theorem B5293259 : Blo 570811 5293259 := bstep (se 1 (by rfl) ⟨3969944, by rfl⟩ : syracuseStep 5293259 = 7939889) B7939889
theorem B574683 : Blo 570811 574683 := bstep (se 1 (by rfl) ⟨431012, by rfl⟩ : syracuseStep 574683 = 862025) B862025
theorem B574759 : Blo 570811 574759 := bstep (se 1 (by rfl) ⟨431069, by rfl⟩ : syracuseStep 574759 = 862139) B862139
theorem B574799 : Blo 570811 574799 := bstep (se 1 (by rfl) ⟨431099, by rfl⟩ : syracuseStep 574799 = 862199) B862199
theorem B6211217 : Blo 570811 6211217 := bstep (se 2 (by rfl) ⟨2329206, by rfl⟩ : syracuseStep 6211217 = 4658413) B4658413
theorem B22005593 : Blo 570811 22005593 := bstep (se 2 (by rfl) ⟨8252097, by rfl⟩ : syracuseStep 22005593 = 16504195) B16504195
theorem B968591 : Blo 570811 968591 := bstep (se 1 (by rfl) ⟨726443, by rfl⟩ : syracuseStep 968591 = 1452887) B1452887
theorem B968827 : Blo 570811 968827 := bstep (se 1 (by rfl) ⟨726620, by rfl⟩ : syracuseStep 968827 = 1453241) B1453241
theorem B12372101 : Blo 570811 12372101 := bstep (se 4 (by rfl) ⟨1159884, by rfl⟩ : syracuseStep 12372101 = 2319769) B2319769
theorem B1034569 : Blo 570811 1034569 := bstep (se 2 (by rfl) ⟨387963, by rfl⟩ : syracuseStep 1034569 = 775927) B775927
theorem B2902553 : Blo 570811 2902553 := bstep (se 2 (by rfl) ⟨1088457, by rfl⟩ : syracuseStep 2902553 = 2176915) B2176915
theorem B4344353 : Blo 570811 4344353 := bstep (se 2 (by rfl) ⟨1629132, by rfl⟩ : syracuseStep 4344353 = 3258265) B3258265
theorem B6507053 : Blo 570811 6507053 := bstep (se 3 (by rfl) ⟨1220072, by rfl⟩ : syracuseStep 6507053 = 2440145) B2440145
theorem B36162449 : Blo 570811 36162449 := bstep (se 2 (by rfl) ⟨13560918, by rfl⟩ : syracuseStep 36162449 = 27121837) B27121837
theorem B2182049 : Blo 570811 2182049 := bstep (se 2 (by rfl) ⟨818268, by rfl⟩ : syracuseStep 2182049 = 1636537) B1636537
theorem B969691 : Blo 570811 969691 := bstep (se 1 (by rfl) ⟨727268, by rfl⟩ : syracuseStep 969691 = 1454537) B1454537
theorem B1100839 : Blo 570811 1100839 := bstep (se 1 (by rfl) ⟨825629, by rfl⟩ : syracuseStep 1100839 = 1651259) B1651259
theorem B642523 : Blo 570811 642523 := bstep (se 1 (by rfl) ⟨481892, by rfl⟩ : syracuseStep 642523 = 963785) B963785
theorem B3264097 : Blo 570811 3264097 := bstep (se 2 (by rfl) ⟨1224036, by rfl⟩ : syracuseStep 3264097 = 2448073) B2448073
theorem B872135 : Blo 570811 872135 := bstep (se 1 (by rfl) ⟨654101, by rfl⟩ : syracuseStep 872135 = 1308203) B1308203
theorem B2936737 : Blo 570811 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B642991 : Blo 570811 642991 := bstep (se 1 (by rfl) ⟨482243, by rfl⟩ : syracuseStep 642991 = 964487) B964487
theorem B1855495 : Blo 570811 1855495 := bstep (se 1 (by rfl) ⟨1391621, by rfl⟩ : syracuseStep 1855495 = 2783243) B2783243
theorem B643423 : Blo 570811 643423 := bstep (se 1 (by rfl) ⟨482567, by rfl⟩ : syracuseStep 643423 = 965135) B965135
theorem B643783 : Blo 570811 643783 := bstep (se 1 (by rfl) ⟨482837, by rfl⟩ : syracuseStep 643783 = 965675) B965675
theorem B1954655 : Blo 570811 1954655 := bstep (se 1 (by rfl) ⟨1465991, by rfl⟩ : syracuseStep 1954655 = 2931983) B2931983
theorem B2315195 : Blo 570811 2315195 := bstep (se 1 (by rfl) ⟨1736396, by rfl⟩ : syracuseStep 2315195 = 3472793) B3472793
theorem B3724289 : Blo 570811 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B3265555 : Blo 570811 3265555 := bstep (se 1 (by rfl) ⟨2449166, by rfl⟩ : syracuseStep 3265555 = 4898333) B4898333
theorem B14931145 : Blo 570811 14931145 := bstep (se 2 (by rfl) ⟨5599179, by rfl⟩ : syracuseStep 14931145 = 11198359) B11198359
theorem B2905469 : Blo 570811 2905469 := bstep (se 3 (by rfl) ⟨544775, by rfl⟩ : syracuseStep 2905469 = 1089551) B1089551
theorem B644647 : Blo 570811 644647 := bstep (se 1 (by rfl) ⟨483485, by rfl⟩ : syracuseStep 644647 = 966971) B966971
theorem B1627847 : Blo 570811 1627847 := bstep (se 1 (by rfl) ⟨1220885, by rfl⟩ : syracuseStep 1627847 = 2441771) B2441771
theorem B776155 : Blo 570811 776155 := bstep (se 1 (by rfl) ⟨582116, by rfl⟩ : syracuseStep 776155 = 1164233) B1164233
theorem B1989647 : Blo 570811 1989647 := bstep (se 1 (by rfl) ⟨1492235, by rfl⟩ : syracuseStep 1989647 = 2984471) B2984471
theorem B646267 : Blo 570811 646267 := bstep (se 1 (by rfl) ⟨484700, by rfl⟩ : syracuseStep 646267 = 969401) B969401
theorem B1957225 : Blo 570811 1957225 := bstep (se 2 (by rfl) ⟨733959, by rfl⟩ : syracuseStep 1957225 = 1467919) B1467919
theorem B1957499 : Blo 570811 1957499 := bstep (se 1 (by rfl) ⟨1468124, by rfl⟩ : syracuseStep 1957499 = 2936249) B2936249
theorem B1236809 : Blo 570811 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B3268471 : Blo 570811 3268471 := bstep (se 1 (by rfl) ⟨2451353, by rfl⟩ : syracuseStep 3268471 = 4902707) B4902707
theorem B1630135 : Blo 570811 1630135 := bstep (se 1 (by rfl) ⟨1222601, by rfl⟩ : syracuseStep 1630135 = 2445203) B2445203
theorem B7331917 : Blo 570811 7331917 := bstep (se 3 (by rfl) ⟨1374734, by rfl⟩ : syracuseStep 7331917 = 2749469) B2749469
theorem B2744435 : Blo 570811 2744435 := bstep (se 1 (by rfl) ⟨2058326, by rfl⟩ : syracuseStep 2744435 = 4116653) B4116653
theorem B15622307 : Blo 570811 15622307 := bstep (se 1 (by rfl) ⟨11716730, by rfl⟩ : syracuseStep 15622307 = 23433461) B23433461
theorem B4645181 : Blo 570811 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B1303559 : Blo 570811 1303559 := bstep (se 1 (by rfl) ⟨977669, by rfl⟩ : syracuseStep 1303559 = 1955339) B1955339
theorem B2614519 : Blo 570811 2614519 := bstep (se 1 (by rfl) ⟨1960889, by rfl⟩ : syracuseStep 2614519 = 3921779) B3921779
theorem B1631593 : Blo 570811 1631593 := bstep (se 2 (by rfl) ⟨611847, by rfl⟩ : syracuseStep 1631593 = 1223695) B1223695
theorem B2319853 : Blo 570811 2319853 := bstep (se 3 (by rfl) ⟨434972, by rfl⟩ : syracuseStep 2319853 = 869945) B869945
theorem B1926665 : Blo 570811 1926665 := bstep (se 2 (by rfl) ⟨722499, by rfl⟩ : syracuseStep 1926665 = 1444999) B1444999
theorem B1566233 : Blo 570811 1566233 := bstep (se 2 (by rfl) ⟨587337, by rfl⟩ : syracuseStep 1566233 = 1174675) B1174675
theorem B4122245 : Blo 570811 4122245 := bstep (se 4 (by rfl) ⟨386460, by rfl⟩ : syracuseStep 4122245 = 772921) B772921
theorem B2909843 : Blo 570811 2909843 := bstep (se 1 (by rfl) ⟨2182382, by rfl⟩ : syracuseStep 2909843 = 4364765) B4364765
theorem B1468115 : Blo 570811 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B1632095 : Blo 570811 1632095 := bstep (se 1 (by rfl) ⟨1224071, by rfl⟩ : syracuseStep 1632095 = 2448143) B2448143
theorem B1828727 : Blo 570811 1828727 := bstep (se 1 (by rfl) ⟨1371545, by rfl⟩ : syracuseStep 1828727 = 2743091) B2743091
theorem B2320289 : Blo 570811 2320289 := bstep (se 2 (by rfl) ⟨870108, by rfl⟩ : syracuseStep 2320289 = 1740217) B1740217
theorem B1304633 : Blo 570811 1304633 := bstep (se 2 (by rfl) ⟨489237, by rfl⟩ : syracuseStep 1304633 = 978475) B978475
theorem B1632413 : Blo 570811 1632413 := bstep (se 3 (by rfl) ⟨306077, by rfl⟩ : syracuseStep 1632413 = 612155) B612155
theorem B1927529 : Blo 570811 1927529 := bstep (se 2 (by rfl) ⟨722823, by rfl⟩ : syracuseStep 1927529 = 1445647) B1445647
theorem B4123169 : Blo 570811 4123169 := bstep (se 2 (by rfl) ⟨1546188, by rfl⟩ : syracuseStep 4123169 = 3092377) B3092377
theorem B1633097 : Blo 570811 1633097 := bstep (se 2 (by rfl) ⟨612411, by rfl⟩ : syracuseStep 1633097 = 1224823) B1224823
theorem B1928123 : Blo 570811 1928123 := bstep (se 1 (by rfl) ⟨1446092, by rfl⟩ : syracuseStep 1928123 = 2892185) B2892185
theorem B1239995 : Blo 570811 1239995 := bstep (se 1 (by rfl) ⟨929996, by rfl⟩ : syracuseStep 1239995 = 1859993) B1859993
theorem B2321423 : Blo 570811 2321423 := bstep (se 1 (by rfl) ⟨1741067, by rfl⟩ : syracuseStep 2321423 = 3482135) B3482135
theorem B1830059 : Blo 570811 1830059 := bstep (se 1 (by rfl) ⟨1372544, by rfl⟩ : syracuseStep 1830059 = 2745089) B2745089
theorem B1633679 : Blo 570811 1633679 := bstep (se 1 (by rfl) ⟨1225259, by rfl⟩ : syracuseStep 1633679 = 2450519) B2450519
theorem B2059739 : Blo 570811 2059739 := bstep (se 1 (by rfl) ⟨1544804, by rfl⟩ : syracuseStep 2059739 = 3089609) B3089609
theorem B7958083 : Blo 570811 7958083 := bstep (se 1 (by rfl) ⟨5968562, by rfl⟩ : syracuseStep 7958083 = 11937125) B11937125
theorem B4255355 : Blo 570811 4255355 := bstep (se 1 (by rfl) ⟨3191516, by rfl⟩ : syracuseStep 4255355 = 6383033) B6383033
theorem B3665857 : Blo 570811 3665857 := bstep (se 2 (by rfl) ⟨1374696, by rfl⟩ : syracuseStep 3665857 = 2749393) B2749393
theorem B815113 : Blo 570811 815113 := bstep (se 2 (by rfl) ⟨305667, by rfl⟩ : syracuseStep 815113 = 611335) B611335
theorem B4649075 : Blo 570811 4649075 := bstep (se 1 (by rfl) ⟨3486806, by rfl⟩ : syracuseStep 4649075 = 6973613) B6973613
theorem B815455 : Blo 570811 815455 := bstep (se 1 (by rfl) ⟨611591, by rfl⟩ : syracuseStep 815455 = 1223183) B1223183
theorem B1929851 : Blo 570811 1929851 := bstep (se 1 (by rfl) ⟨1447388, by rfl⟩ : syracuseStep 1929851 = 2894777) B2894777
theorem B3928787 : Blo 570811 3928787 := bstep (se 1 (by rfl) ⟨2946590, by rfl⟩ : syracuseStep 3928787 = 5893181) B5893181
theorem B1831673 : Blo 570811 1831673 := bstep (se 2 (by rfl) ⟨686877, by rfl⟩ : syracuseStep 1831673 = 1373755) B1373755
theorem B1930013 : Blo 570811 1930013 := bstep (se 3 (by rfl) ⟨361877, by rfl⟩ : syracuseStep 1930013 = 723755) B723755
theorem B1831841 : Blo 570811 1831841 := bstep (se 2 (by rfl) ⟨686940, by rfl⟩ : syracuseStep 1831841 = 1373881) B1373881
theorem B4355045 : Blo 570811 4355045 := bstep (se 4 (by rfl) ⟨408285, by rfl⟩ : syracuseStep 4355045 = 816571) B816571
theorem B14709761 : Blo 570811 14709761 := bstep (se 2 (by rfl) ⟨5516160, by rfl⟩ : syracuseStep 14709761 = 11032321) B11032321
theorem B1930715 : Blo 570811 1930715 := bstep (se 1 (by rfl) ⟨1448036, by rfl⟩ : syracuseStep 1930715 = 2896073) B2896073
theorem B2061787 : Blo 570811 2061787 := bstep (se 1 (by rfl) ⟨1546340, by rfl⟩ : syracuseStep 2061787 = 3092681) B3092681
theorem B4880087 : Blo 570811 4880087 := bstep (se 1 (by rfl) ⟨3660065, by rfl⟩ : syracuseStep 4880087 = 7320131) B7320131
theorem B915305 : Blo 570811 915305 := bstep (se 2 (by rfl) ⟨343239, by rfl⟩ : syracuseStep 915305 = 686479) B686479
theorem B2095031 : Blo 570811 2095031 := bstep (se 1 (by rfl) ⟨1571273, by rfl⟩ : syracuseStep 2095031 = 3142547) B3142547
theorem B4126801 : Blo 570811 4126801 := bstep (se 2 (by rfl) ⟨1547550, by rfl⟩ : syracuseStep 4126801 = 3095101) B3095101
theorem B1931417 : Blo 570811 1931417 := bstep (se 2 (by rfl) ⟨724281, by rfl⟩ : syracuseStep 1931417 = 1448563) B1448563
theorem B169834765 : Blo 570811 169834765 := bstep (se 3 (by rfl) ⟨31844018, by rfl⟩ : syracuseStep 169834765 = 63688037) B63688037
theorem B6977897 : Blo 570811 6977897 := bstep (se 2 (by rfl) ⟨2616711, by rfl⟩ : syracuseStep 6977897 = 5233423) B5233423
theorem B13891945 : Blo 570811 13891945 := bstep (se 2 (by rfl) ⟨5209479, by rfl⟩ : syracuseStep 13891945 = 10418959) B10418959
theorem B2325431 : Blo 570811 2325431 := bstep (se 1 (by rfl) ⟨1744073, by rfl⟩ : syracuseStep 2325431 = 3488147) B3488147
theorem B3669239 : Blo 570811 3669239 := bstep (se 1 (by rfl) ⟨2751929, by rfl⟩ : syracuseStep 3669239 = 5503859) B5503859
theorem B1834301 : Blo 570811 1834301 := bstep (se 3 (by rfl) ⟨343931, by rfl⟩ : syracuseStep 1834301 = 687863) B687863
theorem B1932605 : Blo 570811 1932605 := bstep (se 3 (by rfl) ⟨362363, by rfl⟩ : syracuseStep 1932605 = 724727) B724727
theorem B3669421 : Blo 570811 3669421 := bstep (se 3 (by rfl) ⟨688016, by rfl⟩ : syracuseStep 3669421 = 1376033) B1376033
theorem B1965817 : Blo 570811 1965817 := bstep (se 2 (by rfl) ⟨737181, by rfl⟩ : syracuseStep 1965817 = 1474363) B1474363
theorem B1834825 : Blo 570811 1834825 := bstep (se 2 (by rfl) ⟨688059, by rfl⟩ : syracuseStep 1834825 = 1376119) B1376119
theorem B1310537 : Blo 570811 1310537 := bstep (se 2 (by rfl) ⟨491451, by rfl⟩ : syracuseStep 1310537 = 982903) B982903
theorem B1048481 : Blo 570811 1048481 := bstep (se 2 (by rfl) ⟨393180, by rfl⟩ : syracuseStep 1048481 = 786361) B786361
theorem B15728717 : Blo 570811 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B12419153 : Blo 570811 12419153 := bstep (se 2 (by rfl) ⟨4657182, by rfl⟩ : syracuseStep 12419153 = 9314365) B9314365
theorem B1933523 : Blo 570811 1933523 := bstep (se 1 (by rfl) ⟨1450142, by rfl⟩ : syracuseStep 1933523 = 2900285) B2900285
theorem B1933793 : Blo 570811 1933793 := bstep (se 2 (by rfl) ⟨725172, by rfl⟩ : syracuseStep 1933793 = 1450345) B1450345
theorem B1376831 : Blo 570811 1376831 := bstep (se 1 (by rfl) ⟨1032623, by rfl⟩ : syracuseStep 1376831 = 2065247) B2065247
theorem B10978193 : Blo 570811 10978193 := bstep (se 2 (by rfl) ⟨4116822, by rfl⟩ : syracuseStep 10978193 = 8233645) B8233645
theorem B1935035 : Blo 570811 1935035 := bstep (se 1 (by rfl) ⟨1451276, by rfl⟩ : syracuseStep 1935035 = 2902553) B2902553
theorem B18876203 : Blo 570811 18876203 := bstep (se 1 (by rfl) ⟨14157152, by rfl⟩ : syracuseStep 18876203 = 28314305) B28314305
theorem B4884461 : Blo 570811 4884461 := bstep (se 3 (by rfl) ⟨915836, by rfl⟩ : syracuseStep 4884461 = 1831673) B1831673
theorem B723163 : Blo 570811 723163 := bstep (se 1 (by rfl) ⟨542372, by rfl⟩ : syracuseStep 723163 = 1084745) B1084745
theorem B919919 : Blo 570811 919919 := bstep (se 1 (by rfl) ⟨689939, by rfl⟩ : syracuseStep 919919 = 1379879) B1379879
theorem B3148157 : Blo 570811 3148157 := bstep (se 3 (by rfl) ⟨590279, by rfl⟩ : syracuseStep 3148157 = 1180559) B1180559
theorem B3541391 : Blo 570811 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B2951927 : Blo 570811 2951927 := bstep (se 1 (by rfl) ⟨2213945, by rfl⟩ : syracuseStep 2951927 = 4427891) B4427891
theorem B1379425 : Blo 570811 1379425 := bstep (se 2 (by rfl) ⟨517284, by rfl⟩ : syracuseStep 1379425 = 1034569) B1034569
theorem B1543463 : Blo 570811 1543463 := bstep (se 1 (by rfl) ⟨1157597, by rfl⟩ : syracuseStep 1543463 = 2315195) B2315195
theorem B14683517 : Blo 570811 14683517 := bstep (se 3 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 14683517 = 5506319) B5506319
theorem B1936979 : Blo 570811 1936979 := bstep (se 1 (by rfl) ⟨1452734, by rfl⟩ : syracuseStep 1936979 = 2905469) B2905469
theorem B1085231 : Blo 570811 1085231 := bstep (se 1 (by rfl) ⟨813923, by rfl⟩ : syracuseStep 1085231 = 1627847) B1627847
theorem B724783 : Blo 570811 724783 := bstep (se 1 (by rfl) ⟨543587, by rfl⟩ : syracuseStep 724783 = 1087175) B1087175
theorem B856487 : Blo 570811 856487 := bstep (se 1 (by rfl) ⟨642365, by rfl⟩ : syracuseStep 856487 = 1284731) B1284731
theorem B856571 : Blo 570811 856571 := bstep (se 1 (by rfl) ⟨642428, by rfl⟩ : syracuseStep 856571 = 1284857) B1284857
theorem B856697 : Blo 570811 856697 := bstep (se 2 (by rfl) ⟨321261, by rfl⟩ : syracuseStep 856697 = 642523) B642523
theorem B856751 : Blo 570811 856751 := bstep (se 1 (by rfl) ⟨642563, by rfl⟩ : syracuseStep 856751 = 1285127) B1285127
theorem B856799 : Blo 570811 856799 := bstep (se 1 (by rfl) ⟨642599, by rfl⟩ : syracuseStep 856799 = 1285199) B1285199
theorem B8393681 : Blo 570811 8393681 := bstep (se 2 (by rfl) ⟨3147630, by rfl⟩ : syracuseStep 8393681 = 6295261) B6295261
theorem B857063 : Blo 570811 857063 := bstep (se 1 (by rfl) ⟨642797, by rfl⟩ : syracuseStep 857063 = 1285595) B1285595
theorem B1447055 : Blo 570811 1447055 := bstep (se 1 (by rfl) ⟨1085291, by rfl⟩ : syracuseStep 1447055 = 2170583) B2170583
theorem B2167955 : Blo 570811 2167955 := bstep (se 1 (by rfl) ⟨1625966, by rfl⟩ : syracuseStep 2167955 = 3251933) B3251933
theorem B857321 : Blo 570811 857321 := bstep (se 2 (by rfl) ⟨321495, by rfl⟩ : syracuseStep 857321 = 642991) B642991
theorem B4887809 : Blo 570811 4887809 := bstep (se 2 (by rfl) ⟨1832928, by rfl⟩ : syracuseStep 4887809 = 3665857) B3665857
theorem B857375 : Blo 570811 857375 := bstep (se 1 (by rfl) ⟨643031, by rfl⟩ : syracuseStep 857375 = 1286063) B1286063
theorem B857543 : Blo 570811 857543 := bstep (se 1 (by rfl) ⟨643157, by rfl⟩ : syracuseStep 857543 = 1286315) B1286315
theorem B3479021 : Blo 570811 3479021 := bstep (se 3 (by rfl) ⟨652316, by rfl⟩ : syracuseStep 3479021 = 1304633) B1304633
theorem B857897 : Blo 570811 857897 := bstep (se 2 (by rfl) ⟨321711, by rfl⟩ : syracuseStep 857897 = 643423) B643423
theorem B1087273 : Blo 570811 1087273 := bstep (se 2 (by rfl) ⟨407727, by rfl⟩ : syracuseStep 1087273 = 815455) B815455
theorem B857903 : Blo 570811 857903 := bstep (se 1 (by rfl) ⟨643427, by rfl⟩ : syracuseStep 857903 = 1286855) B1286855
theorem B858377 : Blo 570811 858377 := bstep (se 2 (by rfl) ⟨321891, by rfl⟩ : syracuseStep 858377 = 643783) B643783
theorem B1284425 : Blo 570811 1284425 := bstep (se 2 (by rfl) ⟨481659, by rfl⟩ : syracuseStep 1284425 = 963319) B963319
theorem B1284443 : Blo 570811 1284443 := bstep (se 1 (by rfl) ⟨963332, by rfl⟩ : syracuseStep 1284443 = 1926665) B1926665
theorem B858479 : Blo 570811 858479 := bstep (se 1 (by rfl) ⟨643859, by rfl⟩ : syracuseStep 858479 = 1287719) B1287719
theorem B1939895 : Blo 570811 1939895 := bstep (se 1 (by rfl) ⟨1454921, by rfl⟩ : syracuseStep 1939895 = 2909843) B2909843
theorem B9771515 : Blo 570811 9771515 := bstep (se 1 (by rfl) ⟨7328636, by rfl⟩ : syracuseStep 9771515 = 14657273) B14657273
theorem B1088063 : Blo 570811 1088063 := bstep (se 1 (by rfl) ⟨816047, by rfl⟩ : syracuseStep 1088063 = 1632095) B1632095
theorem B858695 : Blo 570811 858695 := bstep (se 1 (by rfl) ⟨644021, by rfl⟩ : syracuseStep 858695 = 1288043) B1288043
theorem B1219151 : Blo 570811 1219151 := bstep (se 1 (by rfl) ⟨914363, by rfl⟩ : syracuseStep 1219151 = 1828727) B1828727
theorem B1546859 : Blo 570811 1546859 := bstep (se 1 (by rfl) ⟨1160144, by rfl⟩ : syracuseStep 1546859 = 2320289) B2320289
theorem B858731 : Blo 570811 858731 := bstep (se 1 (by rfl) ⟨644048, by rfl⟩ : syracuseStep 858731 = 1288097) B1288097
theorem B2759447 : Blo 570811 2759447 := bstep (se 1 (by rfl) ⟨2069585, by rfl⟩ : syracuseStep 2759447 = 4139171) B4139171
theorem B858959 : Blo 570811 858959 := bstep (se 1 (by rfl) ⟨644219, by rfl⟩ : syracuseStep 858959 = 1288439) B1288439
theorem B4135799 : Blo 570811 4135799 := bstep (se 1 (by rfl) ⟨3101849, by rfl⟩ : syracuseStep 4135799 = 6203699) B6203699
theorem B1285019 : Blo 570811 1285019 := bstep (se 1 (by rfl) ⟨963764, by rfl⟩ : syracuseStep 1285019 = 1927529) B1927529
theorem B1448999 : Blo 570811 1448999 := bstep (se 1 (by rfl) ⟨1086749, by rfl⟩ : syracuseStep 1448999 = 2173499) B2173499
theorem B1285217 : Blo 570811 1285217 := bstep (se 2 (by rfl) ⟨481956, by rfl⟩ : syracuseStep 1285217 = 963913) B963913
theorem B859355 : Blo 570811 859355 := bstep (se 1 (by rfl) ⟨644516, by rfl⟩ : syracuseStep 859355 = 1289033) B1289033
theorem B1088731 : Blo 570811 1088731 := bstep (se 1 (by rfl) ⟨816548, by rfl⟩ : syracuseStep 1088731 = 1633097) B1633097
theorem B1285415 : Blo 570811 1285415 := bstep (se 1 (by rfl) ⟨964061, by rfl⟩ : syracuseStep 1285415 = 1928123) B1928123
theorem B1547615 : Blo 570811 1547615 := bstep (se 1 (by rfl) ⟨1160711, by rfl⟩ : syracuseStep 1547615 = 2321423) B2321423
theorem B1449353 : Blo 570811 1449353 := bstep (se 2 (by rfl) ⟨543507, by rfl⟩ : syracuseStep 1449353 = 1087015) B1087015
theorem B859529 : Blo 570811 859529 := bstep (se 2 (by rfl) ⟨322323, by rfl⟩ : syracuseStep 859529 = 644647) B644647
theorem B1220039 : Blo 570811 1220039 := bstep (se 1 (by rfl) ⟨915029, by rfl⟩ : syracuseStep 1220039 = 1830059) B1830059
theorem B1089119 : Blo 570811 1089119 := bstep (se 1 (by rfl) ⟨816839, by rfl⟩ : syracuseStep 1089119 = 1633679) B1633679
theorem B1285793 : Blo 570811 1285793 := bstep (se 2 (by rfl) ⟨482172, by rfl⟩ : syracuseStep 1285793 = 964345) B964345
theorem B859883 : Blo 570811 859883 := bstep (se 1 (by rfl) ⟨644912, by rfl⟩ : syracuseStep 859883 = 1289825) B1289825
theorem B860111 : Blo 570811 860111 := bstep (se 1 (by rfl) ⟨645083, by rfl⟩ : syracuseStep 860111 = 1290167) B1290167
theorem B1286153 : Blo 570811 1286153 := bstep (se 2 (by rfl) ⟨482307, by rfl⟩ : syracuseStep 1286153 = 964615) B964615
theorem B3252433 : Blo 570811 3252433 := bstep (se 2 (by rfl) ⟨1219662, by rfl⟩ : syracuseStep 3252433 = 2439325) B2439325
theorem B860507 : Blo 570811 860507 := bstep (se 1 (by rfl) ⟨645380, by rfl⟩ : syracuseStep 860507 = 1290761) B1290761
theorem B1286567 : Blo 570811 1286567 := bstep (se 1 (by rfl) ⟨964925, by rfl⟩ : syracuseStep 1286567 = 1929851) B1929851
theorem B18522593 : Blo 570811 18522593 := bstep (se 2 (by rfl) ⟨6945972, by rfl⟩ : syracuseStep 18522593 = 13891945) B13891945
theorem B1286675 : Blo 570811 1286675 := bstep (se 1 (by rfl) ⟨965006, by rfl⟩ : syracuseStep 1286675 = 1930013) B1930013
theorem B860735 : Blo 570811 860735 := bstep (se 1 (by rfl) ⟨645551, by rfl⟩ : syracuseStep 860735 = 1291103) B1291103
theorem B1286729 : Blo 570811 1286729 := bstep (se 2 (by rfl) ⟨482523, by rfl⟩ : syracuseStep 1286729 = 965047) B965047
theorem B1221227 : Blo 570811 1221227 := bstep (se 1 (by rfl) ⟨915920, by rfl⟩ : syracuseStep 1221227 = 1831841) B1831841
theorem B9806507 : Blo 570811 9806507 := bstep (se 1 (by rfl) ⟨7354880, by rfl⟩ : syracuseStep 9806507 = 14709761) B14709761
theorem B860855 : Blo 570811 860855 := bstep (se 1 (by rfl) ⟨645641, by rfl⟩ : syracuseStep 860855 = 1291283) B1291283
theorem B18621197 : Blo 570811 18621197 := bstep (se 3 (by rfl) ⟨3491474, by rfl⟩ : syracuseStep 18621197 = 6982949) B6982949
theorem B1450831 : Blo 570811 1450831 := bstep (se 1 (by rfl) ⟨1088123, by rfl⟩ : syracuseStep 1450831 = 2176247) B2176247
theorem B861083 : Blo 570811 861083 := bstep (se 1 (by rfl) ⟨645812, by rfl⟩ : syracuseStep 861083 = 1291625) B1291625
theorem B2171843 : Blo 570811 2171843 := bstep (se 1 (by rfl) ⟨1628882, by rfl⟩ : syracuseStep 2171843 = 3257765) B3257765
theorem B1287143 : Blo 570811 1287143 := bstep (se 1 (by rfl) ⟨965357, by rfl⟩ : syracuseStep 1287143 = 1930715) B1930715
theorem B1451105 : Blo 570811 1451105 := bstep (se 2 (by rfl) ⟨544164, by rfl⟩ : syracuseStep 1451105 = 1088329) B1088329
theorem B3253391 : Blo 570811 3253391 := bstep (se 1 (by rfl) ⟨2440043, by rfl⟩ : syracuseStep 3253391 = 4880087) B4880087
theorem B861479 : Blo 570811 861479 := bstep (se 1 (by rfl) ⟨646109, by rfl⟩ : syracuseStep 861479 = 1292219) B1292219
theorem B1287521 : Blo 570811 1287521 := bstep (se 2 (by rfl) ⟨482820, by rfl⟩ : syracuseStep 1287521 = 965641) B965641
theorem B861563 : Blo 570811 861563 := bstep (se 1 (by rfl) ⟨646172, by rfl⟩ : syracuseStep 861563 = 1292345) B1292345
theorem B1287611 : Blo 570811 1287611 := bstep (se 1 (by rfl) ⟨965708, by rfl⟩ : syracuseStep 1287611 = 1931417) B1931417
theorem B1451479 : Blo 570811 1451479 := bstep (se 1 (by rfl) ⟨1088609, by rfl⟩ : syracuseStep 1451479 = 2177219) B2177219
theorem B861689 : Blo 570811 861689 := bstep (se 2 (by rfl) ⟨323133, by rfl⟩ : syracuseStep 861689 = 646267) B646267
theorem B2893319 : Blo 570811 2893319 := bstep (se 1 (by rfl) ⟨2169989, by rfl⟩ : syracuseStep 2893319 = 4339979) B4339979
theorem B1287737 : Blo 570811 1287737 := bstep (se 2 (by rfl) ⟨482901, by rfl⟩ : syracuseStep 1287737 = 965803) B965803
theorem B861791 : Blo 570811 861791 := bstep (se 1 (by rfl) ⟨646343, by rfl⟩ : syracuseStep 861791 = 1292687) B1292687
theorem B3679901 : Blo 570811 3679901 := bstep (se 3 (by rfl) ⟨689981, by rfl⟩ : syracuseStep 3679901 = 1379963) B1379963
theorem B11347613 : Blo 570811 11347613 := bstep (se 3 (by rfl) ⟨2127677, by rfl⟩ : syracuseStep 11347613 = 4255355) B4255355
theorem B1451783 : Blo 570811 1451783 := bstep (se 1 (by rfl) ⟨1088837, by rfl⟩ : syracuseStep 1451783 = 2177675) B2177675
theorem B862007 : Blo 570811 862007 := bstep (se 1 (by rfl) ⟨646505, by rfl⟩ : syracuseStep 862007 = 1293011) B1293011
theorem B4892561 : Blo 570811 4892561 := bstep (se 2 (by rfl) ⟨1834710, by rfl⟩ : syracuseStep 4892561 = 3669421) B3669421
theorem B1550287 : Blo 570811 1550287 := bstep (se 1 (by rfl) ⟨1162715, by rfl⟩ : syracuseStep 1550287 = 2325431) B2325431
theorem B2893805 : Blo 570811 2893805 := bstep (se 3 (by rfl) ⟨542588, by rfl⟩ : syracuseStep 2893805 = 1085177) B1085177
theorem B1222867 : Blo 570811 1222867 := bstep (se 1 (by rfl) ⟨917150, by rfl⟩ : syracuseStep 1222867 = 1834301) B1834301
theorem B1288403 : Blo 570811 1288403 := bstep (se 1 (by rfl) ⟨966302, by rfl⟩ : syracuseStep 1288403 = 1932605) B1932605
theorem B1288457 : Blo 570811 1288457 := bstep (se 2 (by rfl) ⟨483171, by rfl⟩ : syracuseStep 1288457 = 966343) B966343
theorem B2894291 : Blo 570811 2894291 := bstep (se 1 (by rfl) ⟨2170718, by rfl⟩ : syracuseStep 2894291 = 4341437) B4341437
theorem B1288673 : Blo 570811 1288673 := bstep (se 2 (by rfl) ⟨483252, by rfl⟩ : syracuseStep 1288673 = 966505) B966505
theorem B1452563 : Blo 570811 1452563 := bstep (se 1 (by rfl) ⟨1089422, by rfl⟩ : syracuseStep 1452563 = 2178845) B2178845
theorem B2173513 : Blo 570811 2173513 := bstep (se 2 (by rfl) ⟨815067, by rfl⟩ : syracuseStep 2173513 = 1630135) B1630135
theorem B698987 : Blo 570811 698987 := bstep (se 1 (by rfl) ⟨524240, by rfl⟩ : syracuseStep 698987 = 1048481) B1048481
theorem B2206403 : Blo 570811 2206403 := bstep (se 1 (by rfl) ⟨1654802, by rfl⟩ : syracuseStep 2206403 = 3309605) B3309605
theorem B9775889 : Blo 570811 9775889 := bstep (se 2 (by rfl) ⟨3665958, by rfl⟩ : syracuseStep 9775889 = 7331917) B7331917
theorem B1288979 : Blo 570811 1288979 := bstep (se 1 (by rfl) ⟨966734, by rfl⟩ : syracuseStep 1288979 = 1933469) B1933469
theorem B2894615 : Blo 570811 2894615 := bstep (se 1 (by rfl) ⟨2170961, by rfl⟩ : syracuseStep 2894615 = 4341923) B4341923
theorem B1289339 : Blo 570811 1289339 := bstep (se 1 (by rfl) ⟨967004, by rfl⟩ : syracuseStep 1289339 = 1934009) B1934009
theorem B1289465 : Blo 570811 1289465 := bstep (se 2 (by rfl) ⟨483549, by rfl⟩ : syracuseStep 1289465 = 967099) B967099
theorem B1289609 : Blo 570811 1289609 := bstep (se 2 (by rfl) ⟨483603, by rfl⟩ : syracuseStep 1289609 = 967207) B967207
theorem B1289735 : Blo 570811 1289735 := bstep (se 1 (by rfl) ⟨967301, by rfl⟩ : syracuseStep 1289735 = 1934603) B1934603
theorem B1289915 : Blo 570811 1289915 := bstep (se 1 (by rfl) ⟨967436, by rfl⟩ : syracuseStep 1289915 = 1934873) B1934873
theorem B4140811 : Blo 570811 4140811 := bstep (se 1 (by rfl) ⟨3105608, by rfl⟩ : syracuseStep 4140811 = 6211217) B6211217
theorem B929593 : Blo 570811 929593 := bstep (se 2 (by rfl) ⟨348597, by rfl⟩ : syracuseStep 929593 = 697195) B697195
theorem B1290041 : Blo 570811 1290041 := bstep (se 2 (by rfl) ⟨483765, by rfl⟩ : syracuseStep 1290041 = 967531) B967531
theorem B1224713 : Blo 570811 1224713 := bstep (se 2 (by rfl) ⟨459267, by rfl⟩ : syracuseStep 1224713 = 918535) B918535
theorem B1454345 : Blo 570811 1454345 := bstep (se 2 (by rfl) ⟨545379, by rfl⟩ : syracuseStep 1454345 = 1090759) B1090759
theorem B3486025 : Blo 570811 3486025 := bstep (se 2 (by rfl) ⟨1307259, by rfl⟩ : syracuseStep 3486025 = 2614519) B2614519
theorem B2896235 : Blo 570811 2896235 := bstep (se 1 (by rfl) ⟨2172176, by rfl⟩ : syracuseStep 2896235 = 4344353) B4344353
theorem B4338035 : Blo 570811 4338035 := bstep (se 1 (by rfl) ⟨3253526, by rfl⟩ : syracuseStep 4338035 = 6507053) B6507053
theorem B1290671 : Blo 570811 1290671 := bstep (se 1 (by rfl) ⟨968003, by rfl⟩ : syracuseStep 1290671 = 1936007) B1936007
theorem B1290707 : Blo 570811 1290707 := bstep (se 1 (by rfl) ⟨968030, by rfl⟩ : syracuseStep 1290707 = 1936061) B1936061
theorem B2175457 : Blo 570811 2175457 := bstep (se 2 (by rfl) ⟨815796, by rfl⟩ : syracuseStep 2175457 = 1631593) B1631593
theorem B1290815 : Blo 570811 1290815 := bstep (se 1 (by rfl) ⟨968111, by rfl⟩ : syracuseStep 1290815 = 1936223) B1936223
theorem B1553003 : Blo 570811 1553003 := bstep (se 1 (by rfl) ⟨1164752, by rfl⟩ : syracuseStep 1553003 = 2329505) B2329505
theorem B1454699 : Blo 570811 1454699 := bstep (se 1 (by rfl) ⟨1091024, by rfl⟩ : syracuseStep 1454699 = 2182049) B2182049
theorem B3093137 : Blo 570811 3093137 := bstep (se 2 (by rfl) ⟨1159926, by rfl⟩ : syracuseStep 3093137 = 2319853) B2319853
theorem B1290923 : Blo 570811 1290923 := bstep (se 1 (by rfl) ⟨968192, by rfl⟩ : syracuseStep 1290923 = 1936385) B1936385
theorem B963407 : Blo 570811 963407 := bstep (se 1 (by rfl) ⟨722555, by rfl⟩ : syracuseStep 963407 = 1445111) B1445111
theorem B1291463 : Blo 570811 1291463 := bstep (se 1 (by rfl) ⟨968597, by rfl⟩ : syracuseStep 1291463 = 1937195) B1937195
theorem B1291643 : Blo 570811 1291643 := bstep (se 1 (by rfl) ⟨968732, by rfl⟩ : syracuseStep 1291643 = 1937465) B1937465
theorem B1291769 : Blo 570811 1291769 := bstep (se 2 (by rfl) ⟨484413, by rfl⟩ : syracuseStep 1291769 = 968827) B968827
theorem B570875 : Blo 570811 570875 := bstep (se 1 (by rfl) ⟨428156, by rfl⟩ : syracuseStep 570875 = 856313) B856313
theorem B570943 : Blo 570811 570943 := bstep (se 1 (by rfl) ⟨428207, by rfl⟩ : syracuseStep 570943 = 856415) B856415
theorem B570951 : Blo 570811 570951 := bstep (se 1 (by rfl) ⟨428213, by rfl⟩ : syracuseStep 570951 = 856427) B856427
theorem B1291859 : Blo 570811 1291859 := bstep (se 1 (by rfl) ⟨968894, by rfl⟩ : syracuseStep 1291859 = 1937789) B1937789
theorem B571103 : Blo 570811 571103 := bstep (se 1 (by rfl) ⟨428327, by rfl⟩ : syracuseStep 571103 = 856655) B856655
theorem B1160939 : Blo 570811 1160939 := bstep (se 1 (by rfl) ⟨870704, by rfl⟩ : syracuseStep 1160939 = 1741409) B1741409
theorem B1292039 : Blo 570811 1292039 := bstep (se 1 (by rfl) ⟨969029, by rfl⟩ : syracuseStep 1292039 = 1938059) B1938059
theorem B2897693 : Blo 570811 2897693 := bstep (se 3 (by rfl) ⟨543317, by rfl⟩ : syracuseStep 2897693 = 1086635) B1086635
theorem B571183 : Blo 570811 571183 := bstep (se 1 (by rfl) ⟨428387, by rfl⟩ : syracuseStep 571183 = 856775) B856775
theorem B964399 : Blo 570811 964399 := bstep (se 1 (by rfl) ⟨723299, by rfl⟩ : syracuseStep 964399 = 1446599) B1446599
theorem B571291 : Blo 570811 571291 := bstep (se 1 (by rfl) ⟨428468, by rfl⟩ : syracuseStep 571291 = 856937) B856937
theorem B571343 : Blo 570811 571343 := bstep (se 1 (by rfl) ⟨428507, by rfl⟩ : syracuseStep 571343 = 857015) B857015
theorem B571367 : Blo 570811 571367 := bstep (se 1 (by rfl) ⟨428525, by rfl⟩ : syracuseStep 571367 = 857051) B857051
theorem B571679 : Blo 570811 571679 := bstep (se 1 (by rfl) ⟨428759, by rfl⟩ : syracuseStep 571679 = 857519) B857519
theorem B571739 : Blo 570811 571739 := bstep (se 1 (by rfl) ⟨428804, by rfl⟩ : syracuseStep 571739 = 857609) B857609
theorem B1292651 : Blo 570811 1292651 := bstep (se 1 (by rfl) ⟨969488, by rfl⟩ : syracuseStep 1292651 = 1938977) B1938977
theorem B571759 : Blo 570811 571759 := bstep (se 1 (by rfl) ⟨428819, by rfl⟩ : syracuseStep 571759 = 857639) B857639
theorem B571815 : Blo 570811 571815 := bstep (se 1 (by rfl) ⟨428861, by rfl⟩ : syracuseStep 571815 = 857723) B857723
theorem B571899 : Blo 570811 571899 := bstep (se 1 (by rfl) ⟨428924, by rfl⟩ : syracuseStep 571899 = 857849) B857849
theorem B1292795 : Blo 570811 1292795 := bstep (se 1 (by rfl) ⟨969596, by rfl⟩ : syracuseStep 1292795 = 1939193) B1939193
theorem B571967 : Blo 570811 571967 := bstep (se 1 (by rfl) ⟨428975, by rfl⟩ : syracuseStep 571967 = 857951) B857951
theorem B571975 : Blo 570811 571975 := bstep (se 1 (by rfl) ⟨428981, by rfl⟩ : syracuseStep 571975 = 857963) B857963
theorem B1292921 : Blo 570811 1292921 := bstep (se 2 (by rfl) ⟨484845, by rfl⟩ : syracuseStep 1292921 = 969691) B969691
theorem B1292975 : Blo 570811 1292975 := bstep (se 1 (by rfl) ⟨969731, by rfl⟩ : syracuseStep 1292975 = 1939463) B1939463
theorem B572127 : Blo 570811 572127 := bstep (se 1 (by rfl) ⟨429095, by rfl⟩ : syracuseStep 572127 = 858191) B858191
theorem B1293047 : Blo 570811 1293047 := bstep (se 1 (by rfl) ⟨969785, by rfl⟩ : syracuseStep 1293047 = 1939571) B1939571
theorem B572207 : Blo 570811 572207 := bstep (se 1 (by rfl) ⟨429155, by rfl⟩ : syracuseStep 572207 = 858311) B858311
theorem B572315 : Blo 570811 572315 := bstep (se 1 (by rfl) ⟨429236, by rfl⟩ : syracuseStep 572315 = 858473) B858473
theorem B1293227 : Blo 570811 1293227 := bstep (se 1 (by rfl) ⟨969920, by rfl⟩ : syracuseStep 1293227 = 1939841) B1939841
theorem B572367 : Blo 570811 572367 := bstep (se 1 (by rfl) ⟨429275, by rfl⟩ : syracuseStep 572367 = 858551) B858551
theorem B572391 : Blo 570811 572391 := bstep (se 1 (by rfl) ⟨429293, by rfl⟩ : syracuseStep 572391 = 858587) B858587
theorem B572703 : Blo 570811 572703 := bstep (se 1 (by rfl) ⟨429527, by rfl⟩ : syracuseStep 572703 = 859055) B859055
theorem B572763 : Blo 570811 572763 := bstep (se 1 (by rfl) ⟨429572, by rfl⟩ : syracuseStep 572763 = 859145) B859145
theorem B1326431 : Blo 570811 1326431 := bstep (se 1 (by rfl) ⟨994823, by rfl⟩ : syracuseStep 1326431 = 1989647) B1989647
theorem B572783 : Blo 570811 572783 := bstep (se 1 (by rfl) ⟨429587, by rfl⟩ : syracuseStep 572783 = 859175) B859175
theorem B572839 : Blo 570811 572839 := bstep (se 1 (by rfl) ⟨429629, by rfl⟩ : syracuseStep 572839 = 859259) B859259
theorem B5291513 : Blo 570811 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B572923 : Blo 570811 572923 := bstep (se 1 (by rfl) ⟨429692, by rfl⟩ : syracuseStep 572923 = 859385) B859385
theorem B5881355 : Blo 570811 5881355 := bstep (se 1 (by rfl) ⟨4411016, by rfl⟩ : syracuseStep 5881355 = 8822033) B8822033
theorem B572991 : Blo 570811 572991 := bstep (se 1 (by rfl) ⟨429743, by rfl⟩ : syracuseStep 572991 = 859487) B859487
theorem B572999 : Blo 570811 572999 := bstep (se 1 (by rfl) ⟨429749, by rfl⟩ : syracuseStep 572999 = 859499) B859499
theorem B2932307 : Blo 570811 2932307 := bstep (se 1 (by rfl) ⟨2199230, by rfl⟩ : syracuseStep 2932307 = 4398461) B4398461
theorem B2440813 : Blo 570811 2440813 := bstep (se 3 (by rfl) ⟨457652, by rfl⟩ : syracuseStep 2440813 = 915305) B915305
theorem B8797841 : Blo 570811 8797841 := bstep (se 2 (by rfl) ⟨3299190, by rfl⟩ : syracuseStep 8797841 = 6598381) B6598381
theorem B573151 : Blo 570811 573151 := bstep (se 1 (by rfl) ⟨429863, by rfl⟩ : syracuseStep 573151 = 859727) B859727
theorem B1163015 : Blo 570811 1163015 := bstep (se 1 (by rfl) ⟨872261, by rfl⟩ : syracuseStep 1163015 = 1744523) B1744523
theorem B573231 : Blo 570811 573231 := bstep (se 1 (by rfl) ⟨429923, by rfl⟩ : syracuseStep 573231 = 859847) B859847
theorem B5586749 : Blo 570811 5586749 := bstep (se 3 (by rfl) ⟨1047515, by rfl⟩ : syracuseStep 5586749 = 2095031) B2095031
theorem B3915649 : Blo 570811 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B573339 : Blo 570811 573339 := bstep (se 1 (by rfl) ⟨430004, by rfl⟩ : syracuseStep 573339 = 860009) B860009
theorem B573391 : Blo 570811 573391 := bstep (se 1 (by rfl) ⟨430043, by rfl⟩ : syracuseStep 573391 = 860087) B860087
theorem B573415 : Blo 570811 573415 := bstep (se 1 (by rfl) ⟨430061, by rfl⟩ : syracuseStep 573415 = 860123) B860123
theorem B2473993 : Blo 570811 2473993 := bstep (se 2 (by rfl) ⟨927747, by rfl⟩ : syracuseStep 2473993 = 1855495) B1855495
theorem B3096787 : Blo 570811 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B573727 : Blo 570811 573727 := bstep (se 1 (by rfl) ⟨430295, by rfl⟩ : syracuseStep 573727 = 860591) B860591
theorem B573787 : Blo 570811 573787 := bstep (se 1 (by rfl) ⟨430340, by rfl⟩ : syracuseStep 573787 = 860681) B860681
theorem B573807 : Blo 570811 573807 := bstep (se 1 (by rfl) ⟨430355, by rfl⟩ : syracuseStep 573807 = 860711) B860711
theorem B967079 : Blo 570811 967079 := bstep (se 1 (by rfl) ⟨725309, by rfl⟩ : syracuseStep 967079 = 1450619) B1450619
theorem B573863 : Blo 570811 573863 := bstep (se 1 (by rfl) ⟨430397, by rfl⟩ : syracuseStep 573863 = 860795) B860795
theorem B573947 : Blo 570811 573947 := bstep (se 1 (by rfl) ⟨430460, by rfl⟩ : syracuseStep 573947 = 860921) B860921
theorem B574015 : Blo 570811 574015 := bstep (se 1 (by rfl) ⟨430511, by rfl⟩ : syracuseStep 574015 = 861023) B861023
theorem B3260999 : Blo 570811 3260999 := bstep (se 1 (by rfl) ⟨2445749, by rfl⟩ : syracuseStep 3260999 = 4891499) B4891499
theorem B574023 : Blo 570811 574023 := bstep (se 1 (by rfl) ⟨430517, by rfl⟩ : syracuseStep 574023 = 861035) B861035
theorem B967241 : Blo 570811 967241 := bstep (se 2 (by rfl) ⟨362715, by rfl⟩ : syracuseStep 967241 = 725431) B725431
theorem B869039 : Blo 570811 869039 := bstep (se 1 (by rfl) ⟨651779, by rfl⟩ : syracuseStep 869039 = 1303559) B1303559
theorem B574175 : Blo 570811 574175 := bstep (se 1 (by rfl) ⟨430631, by rfl⟩ : syracuseStep 574175 = 861263) B861263
theorem B574255 : Blo 570811 574255 := bstep (se 1 (by rfl) ⟨430691, by rfl⟩ : syracuseStep 574255 = 861383) B861383
theorem B574363 : Blo 570811 574363 := bstep (se 1 (by rfl) ⟨430772, by rfl⟩ : syracuseStep 574363 = 861545) B861545
theorem B574415 : Blo 570811 574415 := bstep (se 1 (by rfl) ⟨430811, by rfl⟩ : syracuseStep 574415 = 861623) B861623
theorem B574439 : Blo 570811 574439 := bstep (se 1 (by rfl) ⟨430829, by rfl⟩ : syracuseStep 574439 = 861659) B861659
theorem B574751 : Blo 570811 574751 := bstep (se 1 (by rfl) ⟨431063, by rfl⟩ : syracuseStep 574751 = 862127) B862127
theorem B574811 : Blo 570811 574811 := bstep (se 1 (by rfl) ⟨431108, by rfl⟩ : syracuseStep 574811 = 862217) B862217
theorem B35276309 : Blo 570811 35276309 := bstep (se 6 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 35276309 = 1653577) B1653577
theorem B968287 : Blo 570811 968287 := bstep (se 1 (by rfl) ⟨726215, by rfl⟩ : syracuseStep 968287 = 1452431) B1452431
theorem B19908193 : Blo 570811 19908193 := bstep (se 2 (by rfl) ⟨7465572, by rfl⟩ : syracuseStep 19908193 = 14931145) B14931145
theorem B968503 : Blo 570811 968503 := bstep (se 1 (by rfl) ⟨726377, by rfl⟩ : syracuseStep 968503 = 1452755) B1452755
theorem B2607299 : Blo 570811 2607299 := bstep (se 1 (by rfl) ⟨1955474, by rfl⟩ : syracuseStep 2607299 = 3910949) B3910949
theorem B26364149 : Blo 570811 26364149 := bstep (se 5 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 26364149 = 2471639) B2471639
theorem B968969 : Blo 570811 968969 := bstep (se 2 (by rfl) ⟨363363, by rfl⟩ : syracuseStep 968969 = 726727) B726727
theorem B1034873 : Blo 570811 1034873 := bstep (se 2 (by rfl) ⟨388077, by rfl⟩ : syracuseStep 1034873 = 776155) B776155
theorem B3263165 : Blo 570811 3263165 := bstep (se 3 (by rfl) ⟨611843, by rfl⟩ : syracuseStep 3263165 = 1223687) B1223687
theorem B3099383 : Blo 570811 3099383 := bstep (se 1 (by rfl) ⟨2324537, by rfl⟩ : syracuseStep 3099383 = 4649075) B4649075
theorem B226446353 : Blo 570811 226446353 := bstep (se 2 (by rfl) ⟨84917382, by rfl⟩ : syracuseStep 226446353 = 169834765) B169834765
theorem B969961 : Blo 570811 969961 := bstep (se 2 (by rfl) ⟨363735, by rfl⟩ : syracuseStep 969961 = 727471) B727471
theorem B642343 : Blo 570811 642343 := bstep (se 1 (by rfl) ⟨481757, by rfl⟩ : syracuseStep 642343 = 963515) B963515
theorem B9784637 : Blo 570811 9784637 := bstep (se 3 (by rfl) ⟨1834619, by rfl⟩ : syracuseStep 9784637 = 3669239) B3669239
theorem B2903363 : Blo 570811 2903363 := bstep (se 1 (by rfl) ⟨2177522, by rfl⟩ : syracuseStep 2903363 = 4355045) B4355045
theorem B642415 : Blo 570811 642415 := bstep (se 1 (by rfl) ⟨481811, by rfl⟩ : syracuseStep 642415 = 963623) B963623
theorem B2346455 : Blo 570811 2346455 := bstep (se 1 (by rfl) ⟨1759841, by rfl⟩ : syracuseStep 2346455 = 3519683) B3519683
theorem B642631 : Blo 570811 642631 := bstep (se 1 (by rfl) ⟨481973, by rfl⟩ : syracuseStep 642631 = 963947) B963947
theorem B1625761 : Blo 570811 1625761 := bstep (se 2 (by rfl) ⟨609660, by rfl⟩ : syracuseStep 1625761 = 1219321) B1219321
theorem B2903849 : Blo 570811 2903849 := bstep (se 2 (by rfl) ⟨1088943, by rfl⟩ : syracuseStep 2903849 = 2177887) B2177887
theorem B643495 : Blo 570811 643495 := bstep (se 1 (by rfl) ⟨482621, by rfl⟩ : syracuseStep 643495 = 965243) B965243
theorem B2609633 : Blo 570811 2609633 := bstep (se 2 (by rfl) ⟨978612, by rfl⟩ : syracuseStep 2609633 = 1957225) B1957225
theorem B3298157 : Blo 570811 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B3494765 : Blo 570811 3494765 := bstep (se 3 (by rfl) ⟨655268, by rfl⟩ : syracuseStep 3494765 = 1310537) B1310537
theorem B644071 : Blo 570811 644071 := bstep (se 1 (by rfl) ⟨483053, by rfl⟩ : syracuseStep 644071 = 966107) B966107
theorem B2905145 : Blo 570811 2905145 := bstep (se 2 (by rfl) ⟨1089429, by rfl⟩ : syracuseStep 2905145 = 2178859) B2178859
theorem B2446433 : Blo 570811 2446433 := bstep (se 2 (by rfl) ⟨917412, by rfl⟩ : syracuseStep 2446433 = 1834825) B1834825
theorem B2479261 : Blo 570811 2479261 := bstep (se 3 (by rfl) ⟨464861, by rfl⟩ : syracuseStep 2479261 = 929723) B929723
theorem B611707 : Blo 570811 611707 := bstep (se 1 (by rfl) ⟨458780, by rfl⟩ : syracuseStep 611707 = 917561) B917561
theorem B4347269 : Blo 570811 4347269 := bstep (se 4 (by rfl) ⟨407556, by rfl⟩ : syracuseStep 4347269 = 815113) B815113
theorem B9754019 : Blo 570811 9754019 := bstep (se 1 (by rfl) ⟨7315514, by rfl⟩ : syracuseStep 9754019 = 14631029) B14631029
theorem B9819629 : Blo 570811 9819629 := bstep (se 3 (by rfl) ⟨1841180, by rfl⟩ : syracuseStep 9819629 = 3682361) B3682361
theorem B9655853 : Blo 570811 9655853 := bstep (se 3 (by rfl) ⟨1810472, by rfl⟩ : syracuseStep 9655853 = 3620945) B3620945
theorem B2447185 : Blo 570811 2447185 := bstep (se 2 (by rfl) ⟨917694, by rfl⟩ : syracuseStep 2447185 = 1835389) B1835389
theorem B5494715 : Blo 570811 5494715 := bstep (se 1 (by rfl) ⟨4121036, by rfl⟩ : syracuseStep 5494715 = 8242073) B8242073
theorem B11327521 : Blo 570811 11327521 := bstep (se 2 (by rfl) ⟨4247820, by rfl⟩ : syracuseStep 11327521 = 8495641) B8495641
theorem B3528839 : Blo 570811 3528839 := bstep (se 1 (by rfl) ⟨2646629, by rfl⟩ : syracuseStep 3528839 = 5293259) B5293259
theorem B4905305 : Blo 570811 4905305 := bstep (se 2 (by rfl) ⟨1839489, by rfl⟩ : syracuseStep 4905305 = 3678979) B3678979
theorem B14670395 : Blo 570811 14670395 := bstep (se 1 (by rfl) ⟨11002796, by rfl⟩ : syracuseStep 14670395 = 22005593) B22005593
theorem B645727 : Blo 570811 645727 := bstep (se 1 (by rfl) ⟨484295, by rfl⟩ : syracuseStep 645727 = 968591) B968591
theorem B8248067 : Blo 570811 8248067 := bstep (se 1 (by rfl) ⟨6186050, by rfl⟩ : syracuseStep 8248067 = 12372101) B12372101
theorem B613351 : Blo 570811 613351 := bstep (se 1 (by rfl) ⟨460013, by rfl⟩ : syracuseStep 613351 = 920027) B920027
theorem B2907251 : Blo 570811 2907251 := bstep (se 1 (by rfl) ⟨2180438, by rfl⟩ : syracuseStep 2907251 = 4360877) B4360877
theorem B24108299 : Blo 570811 24108299 := bstep (se 1 (by rfl) ⟨18081224, by rfl⟩ : syracuseStep 24108299 = 36162449) B36162449
theorem B4349699 : Blo 570811 4349699 := bstep (se 1 (by rfl) ⟨3262274, by rfl⟩ : syracuseStep 4349699 = 6524549) B6524549
theorem B581423 : Blo 570811 581423 := bstep (se 1 (by rfl) ⟨436067, by rfl⟩ : syracuseStep 581423 = 872135) B872135
theorem B2908061 : Blo 570811 2908061 := bstep (se 3 (by rfl) ⟨545261, by rfl⟩ : syracuseStep 2908061 = 1090523) B1090523
theorem B2449561 : Blo 570811 2449561 := bstep (se 2 (by rfl) ⟨918585, by rfl⟩ : syracuseStep 2449561 = 1837171) B1837171
theorem B2318699 : Blo 570811 2318699 := bstep (se 1 (by rfl) ⟨1739024, by rfl⟩ : syracuseStep 2318699 = 3478049) B3478049
theorem B1303103 : Blo 570811 1303103 := bstep (se 1 (by rfl) ⟨977327, by rfl⟩ : syracuseStep 1303103 = 1954655) B1954655
theorem B2482859 : Blo 570811 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B2908871 : Blo 570811 2908871 := bstep (se 1 (by rfl) ⟨2181653, by rfl⟩ : syracuseStep 2908871 = 4363307) B4363307
theorem B1467785 : Blo 570811 1467785 := bstep (se 2 (by rfl) ⟨550419, by rfl⟩ : syracuseStep 1467785 = 1100839) B1100839
theorem B7956461 : Blo 570811 7956461 := bstep (se 3 (by rfl) ⟨1491836, by rfl⟩ : syracuseStep 7956461 = 2983673) B2983673
theorem B10610777 : Blo 570811 10610777 := bstep (se 2 (by rfl) ⟨3979041, by rfl⟩ : syracuseStep 10610777 = 7958083) B7958083
theorem B4352129 : Blo 570811 4352129 := bstep (se 2 (by rfl) ⟨1632048, by rfl⟩ : syracuseStep 4352129 = 3264097) B3264097
theorem B1927421 : Blo 570811 1927421 := bstep (se 3 (by rfl) ⟨361391, by rfl⟩ : syracuseStep 1927421 = 722783) B722783
theorem B1304999 : Blo 570811 1304999 := bstep (se 1 (by rfl) ⟨978749, by rfl⟩ : syracuseStep 1304999 = 1957499) B1957499
theorem B1829623 : Blo 570811 1829623 := bstep (se 1 (by rfl) ⟨1372217, by rfl⟩ : syracuseStep 1829623 = 2744435) B2744435
theorem B10414871 : Blo 570811 10414871 := bstep (se 1 (by rfl) ⟨7811153, by rfl⟩ : syracuseStep 10414871 = 15622307) B15622307
theorem B1928231 : Blo 570811 1928231 := bstep (se 1 (by rfl) ⟨1446173, by rfl⟩ : syracuseStep 1928231 = 2892347) B2892347
theorem B4353101 : Blo 570811 4353101 := bstep (se 3 (by rfl) ⟨816206, by rfl⟩ : syracuseStep 4353101 = 1632413) B1632413
theorem B2452619 : Blo 570811 2452619 := bstep (se 1 (by rfl) ⟨1839464, by rfl⟩ : syracuseStep 2452619 = 3678929) B3678929
theorem B1928663 : Blo 570811 1928663 := bstep (se 1 (by rfl) ⟨1446497, by rfl⟩ : syracuseStep 1928663 = 2892995) B2892995
theorem B1044155 : Blo 570811 1044155 := bstep (se 1 (by rfl) ⟨783116, by rfl⟩ : syracuseStep 1044155 = 1566233) B1566233
theorem B2748163 : Blo 570811 2748163 := bstep (se 1 (by rfl) ⟨2061122, by rfl⟩ : syracuseStep 2748163 = 4122245) B4122245
theorem B978743 : Blo 570811 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B4354073 : Blo 570811 4354073 := bstep (se 2 (by rfl) ⟨1632777, by rfl⟩ : syracuseStep 4354073 = 3265555) B3265555
theorem B2748779 : Blo 570811 2748779 := bstep (se 1 (by rfl) ⟨2061584, by rfl⟩ : syracuseStep 2748779 = 4123169) B4123169
theorem B2453935 : Blo 570811 2453935 := bstep (se 1 (by rfl) ⟨1840451, by rfl⟩ : syracuseStep 2453935 = 3680903) B3680903
theorem B2749049 : Blo 570811 2749049 := bstep (se 2 (by rfl) ⟨1030893, by rfl⟩ : syracuseStep 2749049 = 2061787) B2061787
theorem B881327 : Blo 570811 881327 := bstep (se 1 (by rfl) ⟨660995, by rfl⟩ : syracuseStep 881327 = 1321991) B1321991
theorem B1373159 : Blo 570811 1373159 := bstep (se 1 (by rfl) ⟨1029869, by rfl⟩ : syracuseStep 1373159 = 2059739) B2059739
theorem B4879439 : Blo 570811 4879439 := bstep (se 1 (by rfl) ⟨3659579, by rfl⟩ : syracuseStep 4879439 = 7319159) B7319159
theorem B1930337 : Blo 570811 1930337 := bstep (se 2 (by rfl) ⟨723876, by rfl⟩ : syracuseStep 1930337 = 1447753) B1447753
theorem B3306653 : Blo 570811 3306653 := bstep (se 3 (by rfl) ⟨619997, by rfl⟩ : syracuseStep 3306653 = 1239995) B1239995
theorem B2454893 : Blo 570811 2454893 := bstep (se 3 (by rfl) ⟨460292, by rfl⟩ : syracuseStep 2454893 = 920585) B920585
theorem B5502401 : Blo 570811 5502401 := bstep (se 2 (by rfl) ⟨2063400, by rfl⟩ : syracuseStep 5502401 = 4126801) B4126801
theorem B816583 : Blo 570811 816583 := bstep (se 1 (by rfl) ⟨612437, by rfl⟩ : syracuseStep 816583 = 1224875) B1224875
theorem B4355531 : Blo 570811 4355531 := bstep (se 1 (by rfl) ⟨3266648, by rfl⟩ : syracuseStep 4355531 = 6533297) B6533297
theorem B19854989 : Blo 570811 19854989 := bstep (se 3 (by rfl) ⟨3722810, by rfl⟩ : syracuseStep 19854989 = 7445621) B7445621
theorem B620335 : Blo 570811 620335 := bstep (se 1 (by rfl) ⟨465251, by rfl⟩ : syracuseStep 620335 = 930503) B930503
theorem B2619191 : Blo 570811 2619191 := bstep (se 1 (by rfl) ⟨1964393, by rfl⟩ : syracuseStep 2619191 = 3928787) B3928787
theorem B686503 : Blo 570811 686503 := bstep (se 1 (by rfl) ⟨514877, by rfl⟩ : syracuseStep 686503 = 1029755) B1029755
theorem B1931687 : Blo 570811 1931687 := bstep (se 1 (by rfl) ⟨1448765, by rfl⟩ : syracuseStep 1931687 = 2897531) B2897531
theorem B1931849 : Blo 570811 1931849 := bstep (se 2 (by rfl) ⟨724443, by rfl⟩ : syracuseStep 1931849 = 1448887) B1448887
theorem B1473131 : Blo 570811 1473131 := bstep (se 1 (by rfl) ⟨1104848, by rfl⟩ : syracuseStep 1473131 = 2209697) B2209697
theorem B4651931 : Blo 570811 4651931 := bstep (se 1 (by rfl) ⟨3488948, by rfl⟩ : syracuseStep 4651931 = 6977897) B6977897
theorem B2621089 : Blo 570811 2621089 := bstep (se 2 (by rfl) ⟨982908, by rfl⟩ : syracuseStep 2621089 = 1965817) B1965817
theorem B4357961 : Blo 570811 4357961 := bstep (se 2 (by rfl) ⟨1634235, by rfl⟩ : syracuseStep 4357961 = 3268471) B3268471
theorem B10485811 : Blo 570811 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B4129049 : Blo 570811 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B917887 : Blo 570811 917887 := bstep (se 1 (by rfl) ⟨688415, by rfl⟩ : syracuseStep 917887 = 1376831) B1376831
theorem B1934441 : Blo 570811 1934441 := bstep (se 2 (by rfl) ⟨725415, by rfl⟩ : syracuseStep 1934441 = 1450831) B1450831
theorem B12584135 : Blo 570811 12584135 := bstep (se 1 (by rfl) ⟨9438101, by rfl⟩ : syracuseStep 12584135 = 18876203) B18876203
theorem B1738199 : Blo 570811 1738199 := bstep (se 1 (by rfl) ⟨1303649, by rfl⟩ : syracuseStep 1738199 = 2607299) B2607299
theorem B2360927 : Blo 570811 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B689915 : Blo 570811 689915 := bstep (se 1 (by rfl) ⟨517436, by rfl⟩ : syracuseStep 689915 = 1034873) B1034873
theorem B6620957 : Blo 570811 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B2066255 : Blo 570811 2066255 := bstep (se 1 (by rfl) ⟨1549691, by rfl⟩ : syracuseStep 2066255 = 3099383) B3099383
theorem B1967951 : Blo 570811 1967951 := bstep (se 1 (by rfl) ⟨1475963, by rfl⟩ : syracuseStep 1967951 = 2951927) B2951927
theorem B1935305 : Blo 570811 1935305 := bstep (se 2 (by rfl) ⟨725739, by rfl⟩ : syracuseStep 1935305 = 1451479) B1451479
theorem B150964235 : Blo 570811 150964235 := bstep (se 1 (by rfl) ⟨113223176, by rfl⟩ : syracuseStep 150964235 = 226446353) B226446353
theorem B26544257 : Blo 570811 26544257 := bstep (se 2 (by rfl) ⟨9954096, by rfl⟩ : syracuseStep 26544257 = 19908193) B19908193
theorem B6523091 : Blo 570811 6523091 := bstep (se 1 (by rfl) ⟨4892318, by rfl⟩ : syracuseStep 6523091 = 9784637) B9784637
theorem B1935575 : Blo 570811 1935575 := bstep (se 1 (by rfl) ⟨1451681, by rfl⟩ : syracuseStep 1935575 = 2903363) B2903363
theorem B1935899 : Blo 570811 1935899 := bstep (se 1 (by rfl) ⟨1451924, by rfl⟩ : syracuseStep 1935899 = 2903849) B2903849
theorem B723487 : Blo 570811 723487 := bstep (se 1 (by rfl) ⟨542615, by rfl⟩ : syracuseStep 723487 = 1085231) B1085231
theorem B2067049 : Blo 570811 2067049 := bstep (se 2 (by rfl) ⟨775143, by rfl⟩ : syracuseStep 2067049 = 1550287) B1550287
theorem B1739755 : Blo 570811 1739755 := bstep (se 1 (by rfl) ⟨1304816, by rfl⟩ : syracuseStep 1739755 = 2609633) B2609633
theorem B2198771 : Blo 570811 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B2329843 : Blo 570811 2329843 := bstep (se 1 (by rfl) ⟨1747382, by rfl⟩ : syracuseStep 2329843 = 3494765) B3494765
theorem B1936763 : Blo 570811 1936763 := bstep (se 1 (by rfl) ⟨1452572, by rfl⟩ : syracuseStep 1936763 = 2905145) B2905145
theorem B1445303 : Blo 570811 1445303 := bstep (se 1 (by rfl) ⟨1083977, by rfl⟩ : syracuseStep 1445303 = 2167955) B2167955
theorem B1839233 : Blo 570811 1839233 := bstep (se 2 (by rfl) ⟨689712, by rfl⟩ : syracuseStep 1839233 = 1379425) B1379425
theorem B856283 : Blo 570811 856283 := bstep (se 1 (by rfl) ⟨642212, by rfl⟩ : syracuseStep 856283 = 1284425) B1284425
theorem B856295 : Blo 570811 856295 := bstep (se 1 (by rfl) ⟨642221, by rfl⟩ : syracuseStep 856295 = 1284443) B1284443
theorem B725375 : Blo 570811 725375 := bstep (se 1 (by rfl) ⟨544031, by rfl⟩ : syracuseStep 725375 = 1088063) B1088063
theorem B856457 : Blo 570811 856457 := bstep (se 2 (by rfl) ⟨321171, by rfl⟩ : syracuseStep 856457 = 642343) B642343
theorem B856553 : Blo 570811 856553 := bstep (se 2 (by rfl) ⟨321207, by rfl⟩ : syracuseStep 856553 = 642415) B642415
theorem B2757199 : Blo 570811 2757199 := bstep (se 1 (by rfl) ⟨2067899, by rfl⟩ : syracuseStep 2757199 = 4135799) B4135799
theorem B856679 : Blo 570811 856679 := bstep (se 1 (by rfl) ⟨642509, by rfl⟩ : syracuseStep 856679 = 1285019) B1285019
theorem B856811 : Blo 570811 856811 := bstep (se 1 (by rfl) ⟨642608, by rfl⟩ : syracuseStep 856811 = 1285217) B1285217
theorem B1938167 : Blo 570811 1938167 := bstep (se 1 (by rfl) ⟨1453625, by rfl⟩ : syracuseStep 1938167 = 2907251) B2907251
theorem B856841 : Blo 570811 856841 := bstep (se 2 (by rfl) ⟨321315, by rfl⟩ : syracuseStep 856841 = 642631) B642631
theorem B856943 : Blo 570811 856943 := bstep (se 1 (by rfl) ⟨642707, by rfl⟩ : syracuseStep 856943 = 1285415) B1285415
theorem B2167681 : Blo 570811 2167681 := bstep (se 2 (by rfl) ⟨812880, by rfl⟩ : syracuseStep 2167681 = 1625761) B1625761
theorem B726079 : Blo 570811 726079 := bstep (se 1 (by rfl) ⟨544559, by rfl⟩ : syracuseStep 726079 = 1089119) B1089119
theorem B857195 : Blo 570811 857195 := bstep (se 1 (by rfl) ⟨642896, by rfl⟩ : syracuseStep 857195 = 1285793) B1285793
theorem B1938707 : Blo 570811 1938707 := bstep (se 1 (by rfl) ⟨1454030, by rfl⟩ : syracuseStep 1938707 = 2908061) B2908061
theorem B857435 : Blo 570811 857435 := bstep (se 1 (by rfl) ⟨643076, by rfl⟩ : syracuseStep 857435 = 1286153) B1286153
theorem B1545799 : Blo 570811 1545799 := bstep (se 1 (by rfl) ⟨1159349, by rfl⟩ : syracuseStep 1545799 = 2318699) B2318699
theorem B857711 : Blo 570811 857711 := bstep (se 1 (by rfl) ⟨643283, by rfl⟩ : syracuseStep 857711 = 1286567) B1286567
theorem B857783 : Blo 570811 857783 := bstep (se 1 (by rfl) ⟨643337, by rfl⟩ : syracuseStep 857783 = 1286675) B1286675
theorem B857819 : Blo 570811 857819 := bstep (se 1 (by rfl) ⟨643364, by rfl⟩ : syracuseStep 857819 = 1286729) B1286729
theorem B1939247 : Blo 570811 1939247 := bstep (se 1 (by rfl) ⟨1454435, by rfl⟩ : syracuseStep 1939247 = 2908871) B2908871
theorem B857993 : Blo 570811 857993 := bstep (se 2 (by rfl) ⟨321747, by rfl⟩ : syracuseStep 857993 = 643495) B643495
theorem B1447895 : Blo 570811 1447895 := bstep (se 1 (by rfl) ⟨1085921, by rfl⟩ : syracuseStep 1447895 = 2171843) B2171843
theorem B858095 : Blo 570811 858095 := bstep (se 1 (by rfl) ⟨643571, by rfl⟩ : syracuseStep 858095 = 1287143) B1287143
theorem B2168927 : Blo 570811 2168927 := bstep (se 1 (by rfl) ⟨1626695, by rfl⟩ : syracuseStep 2168927 = 3253391) B3253391
theorem B858347 : Blo 570811 858347 := bstep (se 1 (by rfl) ⟨643760, by rfl⟩ : syracuseStep 858347 = 1287521) B1287521
theorem B858407 : Blo 570811 858407 := bstep (se 1 (by rfl) ⟨643805, by rfl⟩ : syracuseStep 858407 = 1287611) B1287611
theorem B8395085 : Blo 570811 8395085 := bstep (se 3 (by rfl) ⟨1574078, by rfl⟩ : syracuseStep 8395085 = 3148157) B3148157
theorem B858491 : Blo 570811 858491 := bstep (se 1 (by rfl) ⟨643868, by rfl⟩ : syracuseStep 858491 = 1287737) B1287737
theorem B858761 : Blo 570811 858761 := bstep (se 2 (by rfl) ⟨322035, by rfl⟩ : syracuseStep 858761 = 644071) B644071
theorem B858935 : Blo 570811 858935 := bstep (se 1 (by rfl) ⟨644201, by rfl⟩ : syracuseStep 858935 = 1288403) B1288403
theorem B1284947 : Blo 570811 1284947 := bstep (se 1 (by rfl) ⟨963710, by rfl⟩ : syracuseStep 1284947 = 1927421) B1927421
theorem B858971 : Blo 570811 858971 := bstep (se 1 (by rfl) ⟨644228, by rfl⟩ : syracuseStep 858971 = 1288457) B1288457
theorem B859115 : Blo 570811 859115 := bstep (se 1 (by rfl) ⟨644336, by rfl⟩ : syracuseStep 859115 = 1288673) B1288673
theorem B859319 : Blo 570811 859319 := bstep (se 1 (by rfl) ⟨644489, by rfl⟩ : syracuseStep 859319 = 1288979) B1288979
theorem B1088777 : Blo 570811 1088777 := bstep (se 2 (by rfl) ⟨408291, by rfl⟩ : syracuseStep 1088777 = 816583) B816583
theorem B1285487 : Blo 570811 1285487 := bstep (se 1 (by rfl) ⟨964115, by rfl⟩ : syracuseStep 1285487 = 1928231) B1928231
theorem B859559 : Blo 570811 859559 := bstep (se 1 (by rfl) ⟨644669, by rfl⟩ : syracuseStep 859559 = 1289339) B1289339
theorem B859643 : Blo 570811 859643 := bstep (se 1 (by rfl) ⟨644732, by rfl⟩ : syracuseStep 859643 = 1289465) B1289465
theorem B859739 : Blo 570811 859739 := bstep (se 1 (by rfl) ⟨644804, by rfl⟩ : syracuseStep 859739 = 1289609) B1289609
theorem B1285775 : Blo 570811 1285775 := bstep (se 1 (by rfl) ⟨964331, by rfl⟩ : syracuseStep 1285775 = 1928663) B1928663
theorem B859823 : Blo 570811 859823 := bstep (se 1 (by rfl) ⟨644867, by rfl⟩ : syracuseStep 859823 = 1289735) B1289735
theorem B1449697 : Blo 570811 1449697 := bstep (se 2 (by rfl) ⟨543636, by rfl⟩ : syracuseStep 1449697 = 1087273) B1087273
theorem B1285865 : Blo 570811 1285865 := bstep (se 2 (by rfl) ⟨482199, by rfl⟩ : syracuseStep 1285865 = 964399) B964399
theorem B827113 : Blo 570811 827113 := bstep (se 2 (by rfl) ⟨310167, by rfl⟩ : syracuseStep 827113 = 620335) B620335
theorem B696103 : Blo 570811 696103 := bstep (se 1 (by rfl) ⟨522077, by rfl⟩ : syracuseStep 696103 = 1044155) B1044155
theorem B859943 : Blo 570811 859943 := bstep (se 1 (by rfl) ⟨644957, by rfl⟩ : syracuseStep 859943 = 1289915) B1289915
theorem B860027 : Blo 570811 860027 := bstep (se 1 (by rfl) ⟨645020, by rfl⟩ : syracuseStep 860027 = 1290041) B1290041
theorem B2892023 : Blo 570811 2892023 := bstep (se 1 (by rfl) ⟨2169017, by rfl⟩ : syracuseStep 2892023 = 4338035) B4338035
theorem B860447 : Blo 570811 860447 := bstep (se 1 (by rfl) ⟨645335, by rfl⟩ : syracuseStep 860447 = 1290671) B1290671
theorem B860471 : Blo 570811 860471 := bstep (se 1 (by rfl) ⟨645353, by rfl⟩ : syracuseStep 860471 = 1290707) B1290707
theorem B860543 : Blo 570811 860543 := bstep (se 1 (by rfl) ⟨645407, by rfl⟩ : syracuseStep 860543 = 1290815) B1290815
theorem B860615 : Blo 570811 860615 := bstep (se 1 (by rfl) ⟨645461, by rfl⟩ : syracuseStep 860615 = 1290923) B1290923
theorem B3252959 : Blo 570811 3252959 := bstep (se 1 (by rfl) ⟨2439719, by rfl⟩ : syracuseStep 3252959 = 4879439) B4879439
theorem B1286891 : Blo 570811 1286891 := bstep (se 1 (by rfl) ⟨965168, by rfl⟩ : syracuseStep 1286891 = 1930337) B1930337
theorem B2204435 : Blo 570811 2204435 := bstep (se 1 (by rfl) ⟨1653326, by rfl⟩ : syracuseStep 2204435 = 3306653) B3306653
theorem B860969 : Blo 570811 860969 := bstep (se 2 (by rfl) ⟨322863, by rfl⟩ : syracuseStep 860969 = 645727) B645727
theorem B860975 : Blo 570811 860975 := bstep (se 1 (by rfl) ⟨645731, by rfl⟩ : syracuseStep 860975 = 1291463) B1291463
theorem B861095 : Blo 570811 861095 := bstep (se 1 (by rfl) ⟨645821, by rfl⟩ : syracuseStep 861095 = 1291643) B1291643
theorem B861179 : Blo 570811 861179 := bstep (se 1 (by rfl) ⟨645884, by rfl⟩ : syracuseStep 861179 = 1291769) B1291769
theorem B861239 : Blo 570811 861239 := bstep (se 1 (by rfl) ⟨645929, by rfl⟩ : syracuseStep 861239 = 1291859) B1291859
theorem B861359 : Blo 570811 861359 := bstep (se 1 (by rfl) ⟨646019, by rfl⟩ : syracuseStep 861359 = 1292039) B1292039
theorem B1746127 : Blo 570811 1746127 := bstep (se 1 (by rfl) ⟨1309595, by rfl⟩ : syracuseStep 1746127 = 2619191) B2619191
theorem B861767 : Blo 570811 861767 := bstep (se 1 (by rfl) ⟨646325, by rfl⟩ : syracuseStep 861767 = 1292651) B1292651
theorem B1287791 : Blo 570811 1287791 := bstep (se 1 (by rfl) ⟨965843, by rfl⟩ : syracuseStep 1287791 = 1931687) B1931687
theorem B1451641 : Blo 570811 1451641 := bstep (se 2 (by rfl) ⟨544365, by rfl⟩ : syracuseStep 1451641 = 1088731) B1088731
theorem B861863 : Blo 570811 861863 := bstep (se 1 (by rfl) ⟨646397, by rfl⟩ : syracuseStep 861863 = 1292795) B1292795
theorem B1287899 : Blo 570811 1287899 := bstep (se 1 (by rfl) ⟨965924, by rfl⟩ : syracuseStep 1287899 = 1931849) B1931849
theorem B861947 : Blo 570811 861947 := bstep (se 1 (by rfl) ⟨646460, by rfl⟩ : syracuseStep 861947 = 1292921) B1292921
theorem B861983 : Blo 570811 861983 := bstep (se 1 (by rfl) ⟨646487, by rfl⟩ : syracuseStep 861983 = 1292975) B1292975
theorem B862031 : Blo 570811 862031 := bstep (se 1 (by rfl) ⟨646523, by rfl⟩ : syracuseStep 862031 = 1293047) B1293047
theorem B862151 : Blo 570811 862151 := bstep (se 1 (by rfl) ⟨646613, by rfl⟩ : syracuseStep 862151 = 1293227) B1293227
theorem B1550461 : Blo 570811 1550461 := bstep (se 3 (by rfl) ⟨290711, by rfl⟩ : syracuseStep 1550461 = 581423) B581423
theorem B3254417 : Blo 570811 3254417 := bstep (se 2 (by rfl) ⟨1220406, by rfl⟩ : syracuseStep 3254417 = 2440813) B2440813
theorem B5220865 : Blo 570811 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B1289015 : Blo 570811 1289015 := bstep (se 1 (by rfl) ⟨966761, by rfl⟩ : syracuseStep 1289015 = 1933523) B1933523
theorem B4336577 : Blo 570811 4336577 := bstep (se 2 (by rfl) ⟨1626216, by rfl⟩ : syracuseStep 4336577 = 3252433) B3252433
theorem B1289195 : Blo 570811 1289195 := bstep (se 1 (by rfl) ⟨966896, by rfl⟩ : syracuseStep 1289195 = 1933793) B1933793
theorem B2173999 : Blo 570811 2173999 := bstep (se 1 (by rfl) ⟨1630499, by rfl⟩ : syracuseStep 2173999 = 3260999) B3260999
theorem B7318795 : Blo 570811 7318795 := bstep (se 1 (by rfl) ⟨5489096, by rfl⟩ : syracuseStep 7318795 = 10978193) B10978193
theorem B1290023 : Blo 570811 1290023 := bstep (se 1 (by rfl) ⟨967517, by rfl⟩ : syracuseStep 1290023 = 1935035) B1935035
theorem B3256307 : Blo 570811 3256307 := bstep (se 1 (by rfl) ⟨2442230, by rfl⟩ : syracuseStep 3256307 = 4884461) B4884461
theorem B17576099 : Blo 570811 17576099 := bstep (se 1 (by rfl) ⟨13182074, by rfl⟩ : syracuseStep 17576099 = 26364149) B26364149
theorem B2175443 : Blo 570811 2175443 := bstep (se 1 (by rfl) ⟨1631582, by rfl⟩ : syracuseStep 2175443 = 3263165) B3263165
theorem B1291049 : Blo 570811 1291049 := bstep (se 2 (by rfl) ⟨484143, by rfl⟩ : syracuseStep 1291049 = 968287) B968287
theorem B1028975 : Blo 570811 1028975 := bstep (se 1 (by rfl) ⟨771731, by rfl⟩ : syracuseStep 1028975 = 1543463) B1543463
theorem B1291319 : Blo 570811 1291319 := bstep (se 1 (by rfl) ⟨968489, by rfl⟩ : syracuseStep 1291319 = 1936979) B1936979
theorem B1291337 : Blo 570811 1291337 := bstep (se 2 (by rfl) ⟨484251, by rfl⟩ : syracuseStep 1291337 = 968503) B968503
theorem B570991 : Blo 570811 570991 := bstep (se 1 (by rfl) ⟨428243, by rfl⟩ : syracuseStep 570991 = 856487) B856487
theorem B964217 : Blo 570811 964217 := bstep (se 2 (by rfl) ⟨361581, by rfl⟩ : syracuseStep 964217 = 723163) B723163
theorem B571047 : Blo 570811 571047 := bstep (se 1 (by rfl) ⟨428285, by rfl⟩ : syracuseStep 571047 = 856571) B856571
theorem B571131 : Blo 570811 571131 := bstep (se 1 (by rfl) ⟨428348, by rfl⟩ : syracuseStep 571131 = 856697) B856697
theorem B571167 : Blo 570811 571167 := bstep (se 1 (by rfl) ⟨428375, by rfl⟩ : syracuseStep 571167 = 856751) B856751
theorem B571199 : Blo 570811 571199 := bstep (se 1 (by rfl) ⟨428399, by rfl⟩ : syracuseStep 571199 = 856799) B856799
theorem B571375 : Blo 570811 571375 := bstep (se 1 (by rfl) ⟨428531, by rfl⟩ : syracuseStep 571375 = 857063) B857063
theorem B964703 : Blo 570811 964703 := bstep (se 1 (by rfl) ⟨723527, by rfl⟩ : syracuseStep 964703 = 1447055) B1447055
theorem B2898017 : Blo 570811 2898017 := bstep (se 2 (by rfl) ⟨1086756, by rfl⟩ : syracuseStep 2898017 = 2173513) B2173513
theorem B571547 : Blo 570811 571547 := bstep (se 1 (by rfl) ⟨428660, by rfl⟩ : syracuseStep 571547 = 857321) B857321
theorem B3258539 : Blo 570811 3258539 := bstep (se 1 (by rfl) ⟨2443904, by rfl⟩ : syracuseStep 3258539 = 4887809) B4887809
theorem B571583 : Blo 570811 571583 := bstep (se 1 (by rfl) ⟨428687, by rfl⟩ : syracuseStep 571583 = 857375) B857375
theorem B2898179 : Blo 570811 2898179 := bstep (se 1 (by rfl) ⟨2173634, by rfl⟩ : syracuseStep 2898179 = 4347269) B4347269
theorem B6502679 : Blo 570811 6502679 := bstep (se 1 (by rfl) ⟨4877009, by rfl⟩ : syracuseStep 6502679 = 9754019) B9754019
theorem B571695 : Blo 570811 571695 := bstep (se 1 (by rfl) ⟨428771, by rfl⟩ : syracuseStep 571695 = 857543) B857543
theorem B2439497 : Blo 570811 2439497 := bstep (se 2 (by rfl) ⟨914811, by rfl⟩ : syracuseStep 2439497 = 1829623) B1829623
theorem B571931 : Blo 570811 571931 := bstep (se 1 (by rfl) ⟨428948, by rfl⟩ : syracuseStep 571931 = 857897) B857897
theorem B571935 : Blo 570811 571935 := bstep (se 1 (by rfl) ⟨428951, by rfl⟩ : syracuseStep 571935 = 857903) B857903
theorem B572251 : Blo 570811 572251 := bstep (se 1 (by rfl) ⟨429188, by rfl⟩ : syracuseStep 572251 = 858377) B858377
theorem B572319 : Blo 570811 572319 := bstep (se 1 (by rfl) ⟨429239, by rfl⟩ : syracuseStep 572319 = 858479) B858479
theorem B1293263 : Blo 570811 1293263 := bstep (se 1 (by rfl) ⟨969947, by rfl⟩ : syracuseStep 1293263 = 1939895) B1939895
theorem B1293281 : Blo 570811 1293281 := bstep (se 2 (by rfl) ⟨484980, by rfl⟩ : syracuseStep 1293281 = 969961) B969961
theorem B9780263 : Blo 570811 9780263 := bstep (se 1 (by rfl) ⟨7335197, by rfl⟩ : syracuseStep 9780263 = 14670395) B14670395
theorem B572463 : Blo 570811 572463 := bstep (se 1 (by rfl) ⟨429347, by rfl⟩ : syracuseStep 572463 = 858695) B858695
theorem B1031239 : Blo 570811 1031239 := bstep (se 1 (by rfl) ⟨773429, by rfl⟩ : syracuseStep 1031239 = 1546859) B1546859
theorem B572487 : Blo 570811 572487 := bstep (se 1 (by rfl) ⟨429365, by rfl⟩ : syracuseStep 572487 = 858731) B858731
theorem B572639 : Blo 570811 572639 := bstep (se 1 (by rfl) ⟨429479, by rfl⟩ : syracuseStep 572639 = 858959) B858959
theorem B965999 : Blo 570811 965999 := bstep (se 1 (by rfl) ⟨724499, by rfl⟩ : syracuseStep 965999 = 1448999) B1448999
theorem B572903 : Blo 570811 572903 := bstep (se 1 (by rfl) ⟨429677, by rfl⟩ : syracuseStep 572903 = 859355) B859355
theorem B16072199 : Blo 570811 16072199 := bstep (se 1 (by rfl) ⟨12054149, by rfl⟩ : syracuseStep 16072199 = 24108299) B24108299
theorem B1031743 : Blo 570811 1031743 := bstep (se 1 (by rfl) ⟨773807, by rfl⟩ : syracuseStep 1031743 = 1547615) B1547615
theorem B966235 : Blo 570811 966235 := bstep (se 1 (by rfl) ⟨724676, by rfl⟩ : syracuseStep 966235 = 1449353) B1449353
theorem B573019 : Blo 570811 573019 := bstep (se 1 (by rfl) ⟨429764, by rfl⟩ : syracuseStep 573019 = 859529) B859529
theorem B966377 : Blo 570811 966377 := bstep (se 2 (by rfl) ⟨362391, by rfl⟩ : syracuseStep 966377 = 724783) B724783
theorem B573255 : Blo 570811 573255 := bstep (se 1 (by rfl) ⟨429941, by rfl⟩ : syracuseStep 573255 = 859883) B859883
theorem B2899799 : Blo 570811 2899799 := bstep (se 1 (by rfl) ⟨2174849, by rfl⟩ : syracuseStep 2899799 = 4349699) B4349699
theorem B573407 : Blo 570811 573407 := bstep (se 1 (by rfl) ⟨430055, by rfl⟩ : syracuseStep 573407 = 860111) B860111
theorem B573671 : Blo 570811 573671 := bstep (se 1 (by rfl) ⟨430253, by rfl⟩ : syracuseStep 573671 = 860507) B860507
theorem B868735 : Blo 570811 868735 := bstep (se 1 (by rfl) ⟨651551, by rfl⟩ : syracuseStep 868735 = 1303103) B1303103
theorem B573823 : Blo 570811 573823 := bstep (se 1 (by rfl) ⟨430367, by rfl⟩ : syracuseStep 573823 = 860735) B860735
theorem B6537671 : Blo 570811 6537671 := bstep (se 1 (by rfl) ⟨4903253, by rfl⟩ : syracuseStep 6537671 = 9806507) B9806507
theorem B573903 : Blo 570811 573903 := bstep (se 1 (by rfl) ⟨430427, by rfl⟩ : syracuseStep 573903 = 860855) B860855
theorem B574055 : Blo 570811 574055 := bstep (se 1 (by rfl) ⟨430541, by rfl⟩ : syracuseStep 574055 = 861083) B861083
theorem B2900609 : Blo 570811 2900609 := bstep (se 2 (by rfl) ⟨1087728, by rfl⟩ : syracuseStep 2900609 = 2175457) B2175457
theorem B967403 : Blo 570811 967403 := bstep (se 1 (by rfl) ⟨725552, by rfl⟩ : syracuseStep 967403 = 1451105) B1451105
theorem B574319 : Blo 570811 574319 := bstep (se 1 (by rfl) ⟨430739, by rfl⟩ : syracuseStep 574319 = 861479) B861479
theorem B574375 : Blo 570811 574375 := bstep (se 1 (by rfl) ⟨430781, by rfl⟩ : syracuseStep 574375 = 861563) B861563
theorem B574459 : Blo 570811 574459 := bstep (se 1 (by rfl) ⟨430844, by rfl⟩ : syracuseStep 574459 = 861689) B861689
theorem B574527 : Blo 570811 574527 := bstep (se 1 (by rfl) ⟨430895, by rfl⟩ : syracuseStep 574527 = 861791) B861791
theorem B967855 : Blo 570811 967855 := bstep (se 1 (by rfl) ⟨725891, by rfl⟩ : syracuseStep 967855 = 1451783) B1451783
theorem B574671 : Blo 570811 574671 := bstep (se 1 (by rfl) ⟨431003, by rfl⟩ : syracuseStep 574671 = 862007) B862007
theorem B3261707 : Blo 570811 3261707 := bstep (se 1 (by rfl) ⟨2446280, by rfl⟩ : syracuseStep 3261707 = 4892561) B4892561
theorem B2901419 : Blo 570811 2901419 := bstep (se 1 (by rfl) ⟨2176064, by rfl⟩ : syracuseStep 2901419 = 4352129) B4352129
theorem B869999 : Blo 570811 869999 := bstep (se 1 (by rfl) ⟨652499, by rfl⟩ : syracuseStep 869999 = 1304999) B1304999
theorem B968375 : Blo 570811 968375 := bstep (se 1 (by rfl) ⟨726281, by rfl⟩ : syracuseStep 968375 = 1452563) B1452563
theorem B2902067 : Blo 570811 2902067 := bstep (se 1 (by rfl) ⟨2176550, by rfl⟩ : syracuseStep 2902067 = 4353101) B4353101
theorem B7358525 : Blo 570811 7358525 := bstep (se 3 (by rfl) ⟨1379723, by rfl⟩ : syracuseStep 7358525 = 2759447) B2759447
theorem B3262913 : Blo 570811 3262913 := bstep (se 2 (by rfl) ⟨1223592, by rfl⟩ : syracuseStep 3262913 = 2447185) B2447185
theorem B2902715 : Blo 570811 2902715 := bstep (se 1 (by rfl) ⟨2177036, by rfl⟩ : syracuseStep 2902715 = 4354073) B4354073
theorem B969563 : Blo 570811 969563 := bstep (se 1 (by rfl) ⟨727172, by rfl⟩ : syracuseStep 969563 = 1454345) B1454345
theorem B1035335 : Blo 570811 1035335 := bstep (se 1 (by rfl) ⟨776501, by rfl⟩ : syracuseStep 1035335 = 1553003) B1553003
theorem B969799 : Blo 570811 969799 := bstep (se 1 (by rfl) ⟨727349, by rfl⟩ : syracuseStep 969799 = 1454699) B1454699
theorem B642271 : Blo 570811 642271 := bstep (se 1 (by rfl) ⟨481703, by rfl⟩ : syracuseStep 642271 = 963407) B963407
theorem B2903687 : Blo 570811 2903687 := bstep (se 1 (by rfl) ⟨2177765, by rfl⟩ : syracuseStep 2903687 = 4355531) B4355531
theorem B773959 : Blo 570811 773959 := bstep (se 1 (by rfl) ⟨580469, by rfl⟩ : syracuseStep 773959 = 1160939) B1160939
theorem B3101287 : Blo 570811 3101287 := bstep (se 1 (by rfl) ⟨2325965, by rfl⟩ : syracuseStep 3101287 = 4651931) B4651931
theorem B3494785 : Blo 570811 3494785 := bstep (se 2 (by rfl) ⟨1310544, by rfl⟩ : syracuseStep 3494785 = 2621089) B2621089
theorem B3527675 : Blo 570811 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B3920903 : Blo 570811 3920903 := bstep (se 1 (by rfl) ⟨2940677, by rfl⟩ : syracuseStep 3920903 = 5881355) B5881355
theorem B1954871 : Blo 570811 1954871 := bstep (se 1 (by rfl) ⟨1466153, by rfl⟩ : syracuseStep 1954871 = 2932307) B2932307
theorem B775343 : Blo 570811 775343 := bstep (se 1 (by rfl) ⟨581507, by rfl⟩ : syracuseStep 775343 = 1163015) B1163015
theorem B3724499 : Blo 570811 3724499 := bstep (se 1 (by rfl) ⟨2793374, by rfl⟩ : syracuseStep 3724499 = 5586749) B5586749
theorem B2905307 : Blo 570811 2905307 := bstep (se 1 (by rfl) ⟨2178980, by rfl⟩ : syracuseStep 2905307 = 4357961) B4357961
theorem B3298657 : Blo 570811 3298657 := bstep (se 2 (by rfl) ⟨1236996, by rfl⟩ : syracuseStep 3298657 = 2473993) B2473993
theorem B8279435 : Blo 570811 8279435 := bstep (se 1 (by rfl) ⟨6209576, by rfl⟩ : syracuseStep 8279435 = 12419153) B12419153
theorem B3266081 : Blo 570811 3266081 := bstep (se 2 (by rfl) ⟨1224780, by rfl⟩ : syracuseStep 3266081 = 2449561) B2449561
theorem B644719 : Blo 570811 644719 := bstep (se 1 (by rfl) ⟨483539, by rfl⟩ : syracuseStep 644719 = 967079) B967079
theorem B644827 : Blo 570811 644827 := bstep (se 1 (by rfl) ⟨483620, by rfl⟩ : syracuseStep 644827 = 967241) B967241
theorem B579359 : Blo 570811 579359 := bstep (se 1 (by rfl) ⟨434519, by rfl⟩ : syracuseStep 579359 = 869039) B869039
theorem B23517539 : Blo 570811 23517539 := bstep (se 1 (by rfl) ⟨17638154, by rfl⟩ : syracuseStep 23517539 = 35276309) B35276309
theorem B645979 : Blo 570811 645979 := bstep (se 1 (by rfl) ⟨484484, by rfl⟩ : syracuseStep 645979 = 968969) B968969
theorem B613279 : Blo 570811 613279 := bstep (se 1 (by rfl) ⟨459959, by rfl⟩ : syracuseStep 613279 = 919919) B919919
theorem B2350205 : Blo 570811 2350205 := bstep (se 3 (by rfl) ⟨440663, by rfl⟩ : syracuseStep 2350205 = 881327) B881327
theorem B9789011 : Blo 570811 9789011 := bstep (se 1 (by rfl) ⟨7341758, by rfl⟩ : syracuseStep 9789011 = 14683517) B14683517
theorem B1564303 : Blo 570811 1564303 := bstep (se 1 (by rfl) ⟨1173227, by rfl⟩ : syracuseStep 1564303 = 2346455) B2346455
theorem B3661757 : Blo 570811 3661757 := bstep (se 3 (by rfl) ⟨686579, by rfl⟩ : syracuseStep 3661757 = 1373159) B1373159
theorem B1630489 : Blo 570811 1630489 := bstep (se 2 (by rfl) ⟨611433, by rfl⟩ : syracuseStep 1630489 = 1222867) B1222867
theorem B5595787 : Blo 570811 5595787 := bstep (se 1 (by rfl) ⟨4196840, by rfl⟩ : syracuseStep 5595787 = 8393681) B8393681
theorem B1630955 : Blo 570811 1630955 := bstep (se 1 (by rfl) ⟨1223216, by rfl⟩ : syracuseStep 1630955 = 2446433) B2446433
theorem B2319347 : Blo 570811 2319347 := bstep (se 1 (by rfl) ⟨1739510, by rfl⟩ : syracuseStep 2319347 = 3479021) B3479021
theorem B6546419 : Blo 570811 6546419 := bstep (se 1 (by rfl) ⟨4909814, by rfl⟩ : syracuseStep 6546419 = 9819629) B9819629
theorem B3663143 : Blo 570811 3663143 := bstep (se 1 (by rfl) ⟨2747357, by rfl⟩ : syracuseStep 3663143 = 5494715) B5494715
theorem B2352559 : Blo 570811 2352559 := bstep (se 1 (by rfl) ⟨1764419, by rfl⟩ : syracuseStep 2352559 = 3528839) B3528839
theorem B25748941 : Blo 570811 25748941 := bstep (se 3 (by rfl) ⟨4827926, by rfl⟩ : syracuseStep 25748941 = 9655853) B9655853
theorem B3270203 : Blo 570811 3270203 := bstep (se 1 (by rfl) ⟨2452652, by rfl⟩ : syracuseStep 3270203 = 4905305) B4905305
theorem B6514343 : Blo 570811 6514343 := bstep (se 1 (by rfl) ⟨4885757, by rfl⟩ : syracuseStep 6514343 = 9771515) B9771515
theorem B812767 : Blo 570811 812767 := bstep (se 1 (by rfl) ⟨609575, by rfl⟩ : syracuseStep 812767 = 1219151) B1219151
theorem B5498711 : Blo 570811 5498711 := bstep (se 1 (by rfl) ⟨4124033, by rfl⟩ : syracuseStep 5498711 = 8248067) B8248067
theorem B813359 : Blo 570811 813359 := bstep (se 1 (by rfl) ⟨610019, by rfl⟩ : syracuseStep 813359 = 1220039) B1220039
theorem B3664217 : Blo 570811 3664217 := bstep (se 2 (by rfl) ⟨1374081, by rfl⟩ : syracuseStep 3664217 = 2748163) B2748163
theorem B1239457 : Blo 570811 1239457 := bstep (se 2 (by rfl) ⟨464796, by rfl⟩ : syracuseStep 1239457 = 929593) B929593
theorem B3271205 : Blo 570811 3271205 := bstep (se 4 (by rfl) ⟨306675, by rfl⟩ : syracuseStep 3271205 = 613351) B613351
theorem B12348395 : Blo 570811 12348395 := bstep (se 1 (by rfl) ⟨9261296, by rfl⟩ : syracuseStep 12348395 = 18522593) B18522593
theorem B814151 : Blo 570811 814151 := bstep (se 1 (by rfl) ⟨610613, by rfl⟩ : syracuseStep 814151 = 1221227) B1221227
theorem B4648033 : Blo 570811 4648033 := bstep (se 2 (by rfl) ⟨1743012, by rfl⟩ : syracuseStep 4648033 = 3486025) B3486025
theorem B12414131 : Blo 570811 12414131 := bstep (se 1 (by rfl) ⟨9310598, by rfl⟩ : syracuseStep 12414131 = 18621197) B18621197
theorem B3271913 : Blo 570811 3271913 := bstep (se 2 (by rfl) ⟨1226967, by rfl⟩ : syracuseStep 3271913 = 2453935) B2453935
theorem B978523 : Blo 570811 978523 := bstep (se 1 (by rfl) ⟨733892, by rfl⟩ : syracuseStep 978523 = 1467785) B1467785
theorem B1928879 : Blo 570811 1928879 := bstep (se 1 (by rfl) ⟨1446659, by rfl⟩ : syracuseStep 1928879 = 2893319) B2893319
theorem B2453267 : Blo 570811 2453267 := bstep (se 1 (by rfl) ⟨1839950, by rfl⟩ : syracuseStep 2453267 = 3679901) B3679901
theorem B7565075 : Blo 570811 7565075 := bstep (se 1 (by rfl) ⟨5673806, by rfl⟩ : syracuseStep 7565075 = 11347613) B11347613
theorem B1929203 : Blo 570811 1929203 := bstep (se 1 (by rfl) ⟨1446902, by rfl⟩ : syracuseStep 1929203 = 2893805) B2893805
theorem B5304307 : Blo 570811 5304307 := bstep (se 1 (by rfl) ⟨3978230, by rfl⟩ : syracuseStep 5304307 = 7956461) B7956461
theorem B7073851 : Blo 570811 7073851 := bstep (se 1 (by rfl) ⟨5305388, by rfl⟩ : syracuseStep 7073851 = 10610777) B10610777
theorem B3305681 : Blo 570811 3305681 := bstep (se 2 (by rfl) ⟨1239630, by rfl⟩ : syracuseStep 3305681 = 2479261) B2479261
theorem B1863965 : Blo 570811 1863965 := bstep (se 3 (by rfl) ⟨349493, by rfl⟩ : syracuseStep 1863965 = 698987) B698987
theorem B1929527 : Blo 570811 1929527 := bstep (se 1 (by rfl) ⟨1447145, by rfl⟩ : syracuseStep 1929527 = 2894291) B2894291
theorem B1470935 : Blo 570811 1470935 := bstep (se 1 (by rfl) ⟨1103201, by rfl⟩ : syracuseStep 1470935 = 2206403) B2206403
theorem B815609 : Blo 570811 815609 := bstep (se 2 (by rfl) ⟨305853, by rfl⟩ : syracuseStep 815609 = 611707) B611707
theorem B6517259 : Blo 570811 6517259 := bstep (se 1 (by rfl) ⟨4887944, by rfl⟩ : syracuseStep 6517259 = 9775889) B9775889
theorem B6943247 : Blo 570811 6943247 := bstep (se 1 (by rfl) ⟨5207435, by rfl⟩ : syracuseStep 6943247 = 10414871) B10414871
theorem B1929743 : Blo 570811 1929743 := bstep (se 1 (by rfl) ⟨1447307, by rfl⟩ : syracuseStep 1929743 = 2894615) B2894615
theorem B1635079 : Blo 570811 1635079 := bstep (se 1 (by rfl) ⟨1226309, by rfl⟩ : syracuseStep 1635079 = 2452619) B2452619
theorem B652495 : Blo 570811 652495 := bstep (se 1 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 652495 = 978743) B978743
theorem B816475 : Blo 570811 816475 := bstep (se 1 (by rfl) ⟨612356, by rfl⟩ : syracuseStep 816475 = 1224713) B1224713
theorem B15103361 : Blo 570811 15103361 := bstep (se 2 (by rfl) ⟨5663760, by rfl⟩ : syracuseStep 15103361 = 11327521) B11327521
theorem B1832519 : Blo 570811 1832519 := bstep (se 1 (by rfl) ⟨1374389, by rfl⟩ : syracuseStep 1832519 = 2748779) B2748779
theorem B1930823 : Blo 570811 1930823 := bstep (se 1 (by rfl) ⟨1448117, by rfl⟩ : syracuseStep 1930823 = 2896235) B2896235
theorem B1832699 : Blo 570811 1832699 := bstep (se 1 (by rfl) ⟨1374524, by rfl⟩ : syracuseStep 1832699 = 2749049) B2749049
theorem B2062091 : Blo 570811 2062091 := bstep (se 1 (by rfl) ⟨1546568, by rfl⟩ : syracuseStep 2062091 = 3093137) B3093137
theorem B915337 : Blo 570811 915337 := bstep (se 2 (by rfl) ⟨343251, by rfl⟩ : syracuseStep 915337 = 686503) B686503
theorem B1636595 : Blo 570811 1636595 := bstep (se 1 (by rfl) ⟨1227446, by rfl⟩ : syracuseStep 1636595 = 2454893) B2454893
theorem B3668267 : Blo 570811 3668267 := bstep (se 1 (by rfl) ⟨2751200, by rfl⟩ : syracuseStep 3668267 = 5502401) B5502401
theorem B13236659 : Blo 570811 13236659 := bstep (se 1 (by rfl) ⟨9927494, by rfl⟩ : syracuseStep 13236659 = 19854989) B19854989
theorem B1931795 : Blo 570811 1931795 := bstep (se 1 (by rfl) ⟨1448846, by rfl⟩ : syracuseStep 1931795 = 2897693) B2897693
theorem B22084325 : Blo 570811 22084325 := bstep (se 4 (by rfl) ⟨2070405, by rfl⟩ : syracuseStep 22084325 = 4140811) B4140811
theorem B982087 : Blo 570811 982087 := bstep (se 1 (by rfl) ⟨736565, by rfl⟩ : syracuseStep 982087 = 1473131) B1473131
theorem B884287 : Blo 570811 884287 := bstep (se 1 (by rfl) ⟨663215, by rfl⟩ : syracuseStep 884287 = 1326431) B1326431
theorem B5865227 : Blo 570811 5865227 := bstep (se 1 (by rfl) ⟨4398920, by rfl⟩ : syracuseStep 5865227 = 8797841) B8797841
theorem B2752699 : Blo 570811 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B4358447 : Blo 570811 4358447 := bstep (se 1 (by rfl) ⟨3268835, by rfl⟩ : syracuseStep 4358447 = 6537671) B6537671
theorem B1933739 : Blo 570811 1933739 := bstep (se 1 (by rfl) ⟨1450304, by rfl⟩ : syracuseStep 1933739 = 2900609) B2900609
theorem B8389423 : Blo 570811 8389423 := bstep (se 1 (by rfl) ⟨6292067, by rfl⟩ : syracuseStep 8389423 = 12584135) B12584135
theorem B1934279 : Blo 570811 1934279 := bstep (se 1 (by rfl) ⟨1450709, by rfl⟩ : syracuseStep 1934279 = 2901419) B2901419
theorem B1934333 : Blo 570811 1934333 := bstep (se 3 (by rfl) ⟨362687, by rfl⟩ : syracuseStep 1934333 = 725375) B725375
theorem B1377503 : Blo 570811 1377503 := bstep (se 1 (by rfl) ⟨1033127, by rfl⟩ : syracuseStep 1377503 = 2066255) B2066255
theorem B1311967 : Blo 570811 1311967 := bstep (se 1 (by rfl) ⟨983975, by rfl⟩ : syracuseStep 1311967 = 1967951) B1967951
theorem B1934711 : Blo 570811 1934711 := bstep (se 1 (by rfl) ⟨1451033, by rfl⟩ : syracuseStep 1934711 = 2902067) B2902067
theorem B17696171 : Blo 570811 17696171 := bstep (se 1 (by rfl) ⟨13272128, by rfl⟩ : syracuseStep 17696171 = 26544257) B26544257
theorem B2328169 : Blo 570811 2328169 := bstep (se 2 (by rfl) ⟨873063, by rfl⟩ : syracuseStep 2328169 = 1746127) B1746127
theorem B1935143 : Blo 570811 1935143 := bstep (se 1 (by rfl) ⟨1451357, by rfl⟩ : syracuseStep 1935143 = 2902715) B2902715
theorem B20875157 : Blo 570811 20875157 := bstep (se 6 (by rfl) ⟨489261, by rfl⟩ : syracuseStep 20875157 = 978523) B978523
theorem B690223 : Blo 570811 690223 := bstep (se 1 (by rfl) ⟨517667, by rfl⟩ : syracuseStep 690223 = 1035335) B1035335
theorem B1935521 : Blo 570811 1935521 := bstep (se 2 (by rfl) ⟨725820, by rfl⟩ : syracuseStep 1935521 = 1451641) B1451641
theorem B1083689 : Blo 570811 1083689 := bstep (se 2 (by rfl) ⟨406383, by rfl⟩ : syracuseStep 1083689 = 812767) B812767
theorem B1935791 : Blo 570811 1935791 := bstep (se 1 (by rfl) ⟨1451843, by rfl⟩ : syracuseStep 1935791 = 2903687) B2903687
theorem B2067281 : Blo 570811 2067281 := bstep (se 2 (by rfl) ⟨775230, by rfl⟩ : syracuseStep 2067281 = 1550461) B1550461
theorem B2067581 : Blo 570811 2067581 := bstep (se 3 (by rfl) ⟨387671, by rfl⟩ : syracuseStep 2067581 = 775343) B775343
theorem B9931997 : Blo 570811 9931997 := bstep (se 3 (by rfl) ⟨1862249, by rfl⟩ : syracuseStep 9931997 = 3724499) B3724499
theorem B2756065 : Blo 570811 2756065 := bstep (se 2 (by rfl) ⟨1033524, by rfl⟩ : syracuseStep 2756065 = 2067049) B2067049
theorem B1936871 : Blo 570811 1936871 := bstep (se 1 (by rfl) ⟨1452653, by rfl⟩ : syracuseStep 1936871 = 2905307) B2905307
theorem B1445951 : Blo 570811 1445951 := bstep (se 1 (by rfl) ⟨1084463, by rfl⟩ : syracuseStep 1445951 = 2168927) B2168927
theorem B6295805 : Blo 570811 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B856361 : Blo 570811 856361 := bstep (se 2 (by rfl) ⟨321135, by rfl⟩ : syracuseStep 856361 = 642271) B642271
theorem B856631 : Blo 570811 856631 := bstep (se 1 (by rfl) ⟨642473, by rfl⟩ : syracuseStep 856631 = 1284947) B1284947
theorem B1839773 : Blo 570811 1839773 := bstep (se 3 (by rfl) ⟨344957, by rfl⟩ : syracuseStep 1839773 = 689915) B689915
theorem B1544957 : Blo 570811 1544957 := bstep (se 3 (by rfl) ⟨289679, by rfl⟩ : syracuseStep 1544957 = 579359) B579359
theorem B725851 : Blo 570811 725851 := bstep (se 1 (by rfl) ⟨544388, by rfl⟩ : syracuseStep 725851 = 1088777) B1088777
theorem B856991 : Blo 570811 856991 := bstep (se 1 (by rfl) ⟨642743, by rfl⟩ : syracuseStep 856991 = 1285487) B1285487
theorem B6526007 : Blo 570811 6526007 := bstep (se 1 (by rfl) ⟨4894505, by rfl⟩ : syracuseStep 6526007 = 9789011) B9789011
theorem B857183 : Blo 570811 857183 := bstep (se 1 (by rfl) ⟨642887, by rfl⟩ : syracuseStep 857183 = 1285775) B1285775
theorem B857243 : Blo 570811 857243 := bstep (se 1 (by rfl) ⟨642932, by rfl⟩ : syracuseStep 857243 = 1285865) B1285865
theorem B2168639 : Blo 570811 2168639 := bstep (se 1 (by rfl) ⟨1626479, by rfl⟩ : syracuseStep 2168639 = 3252959) B3252959
theorem B857927 : Blo 570811 857927 := bstep (se 1 (by rfl) ⟨643445, by rfl⟩ : syracuseStep 857927 = 1286891) B1286891
theorem B1546231 : Blo 570811 1546231 := bstep (se 1 (by rfl) ⟨1159673, by rfl⟩ : syracuseStep 1546231 = 2319347) B2319347
theorem B4364279 : Blo 570811 4364279 := bstep (se 1 (by rfl) ⟨3273209, by rfl⟩ : syracuseStep 4364279 = 6546419) B6546419
theorem B3676265 : Blo 570811 3676265 := bstep (se 2 (by rfl) ⟨1378599, by rfl⟩ : syracuseStep 3676265 = 2757199) B2757199
theorem B2168957 : Blo 570811 2168957 := bstep (se 3 (by rfl) ⟨406679, by rfl⟩ : syracuseStep 2168957 = 813359) B813359
theorem B4135049 : Blo 570811 4135049 := bstep (se 2 (by rfl) ⟨1550643, by rfl⟩ : syracuseStep 4135049 = 3101287) B3101287
theorem B858527 : Blo 570811 858527 := bstep (se 1 (by rfl) ⟨643895, by rfl⟩ : syracuseStep 858527 = 1287791) B1287791
theorem B858599 : Blo 570811 858599 := bstep (se 1 (by rfl) ⟨643949, by rfl⟩ : syracuseStep 858599 = 1287899) B1287899
theorem B2890241 : Blo 570811 2890241 := bstep (se 2 (by rfl) ⟨1083840, by rfl⟩ : syracuseStep 2890241 = 2167681) B2167681
theorem B4659713 : Blo 570811 4659713 := bstep (se 2 (by rfl) ⟨1747392, by rfl⟩ : syracuseStep 4659713 = 3494785) B3494785
theorem B2169611 : Blo 570811 2169611 := bstep (se 1 (by rfl) ⟨1627208, by rfl⟩ : syracuseStep 2169611 = 3254417) B3254417
theorem B1088633 : Blo 570811 1088633 := bstep (se 2 (by rfl) ⟨408237, by rfl⟩ : syracuseStep 1088633 = 816475) B816475
theorem B4398209 : Blo 570811 4398209 := bstep (se 2 (by rfl) ⟨1649328, by rfl⟩ : syracuseStep 4398209 = 3298657) B3298657
theorem B859343 : Blo 570811 859343 := bstep (se 1 (by rfl) ⟨644507, by rfl⟩ : syracuseStep 859343 = 1289015) B1289015
theorem B2891051 : Blo 570811 2891051 := bstep (se 1 (by rfl) ⟨2168288, by rfl⟩ : syracuseStep 2891051 = 4336577) B4336577
theorem B8232263 : Blo 570811 8232263 := bstep (se 1 (by rfl) ⟨6174197, by rfl⟩ : syracuseStep 8232263 = 12348395) B12348395
theorem B859463 : Blo 570811 859463 := bstep (se 1 (by rfl) ⟨644597, by rfl⟩ : syracuseStep 859463 = 1289195) B1289195
theorem B859625 : Blo 570811 859625 := bstep (se 2 (by rfl) ⟨322359, by rfl⟩ : syracuseStep 859625 = 644719) B644719
theorem B859769 : Blo 570811 859769 := bstep (se 2 (by rfl) ⟨322413, by rfl⟩ : syracuseStep 859769 = 644827) B644827
theorem B1285919 : Blo 570811 1285919 := bstep (se 1 (by rfl) ⟨964439, by rfl⟩ : syracuseStep 1285919 = 1928879) B1928879
theorem B1220449 : Blo 570811 1220449 := bstep (se 2 (by rfl) ⟨457668, by rfl⟩ : syracuseStep 1220449 = 915337) B915337
theorem B860015 : Blo 570811 860015 := bstep (se 1 (by rfl) ⟨645011, by rfl⟩ : syracuseStep 860015 = 1290023) B1290023
theorem B2170871 : Blo 570811 2170871 := bstep (se 1 (by rfl) ⟨1628153, by rfl⟩ : syracuseStep 2170871 = 3256307) B3256307
theorem B1286135 : Blo 570811 1286135 := bstep (se 1 (by rfl) ⟨964601, by rfl⟩ : syracuseStep 1286135 = 1929203) B1929203
theorem B2203787 : Blo 570811 2203787 := bstep (se 1 (by rfl) ⟨1652840, by rfl⟩ : syracuseStep 2203787 = 3305681) B3305681
theorem B2171069 : Blo 570811 2171069 := bstep (se 3 (by rfl) ⟨407075, by rfl⟩ : syracuseStep 2171069 = 814151) B814151
theorem B1286351 : Blo 570811 1286351 := bstep (se 1 (by rfl) ⟨964763, by rfl⟩ : syracuseStep 1286351 = 1929527) B1929527
theorem B1450295 : Blo 570811 1450295 := bstep (se 1 (by rfl) ⟨1087721, by rfl⟩ : syracuseStep 1450295 = 2175443) B2175443
theorem B4628831 : Blo 570811 4628831 := bstep (se 1 (by rfl) ⟨3471623, by rfl⟩ : syracuseStep 4628831 = 6943247) B6943247
theorem B1286495 : Blo 570811 1286495 := bstep (se 1 (by rfl) ⟨964871, by rfl⟩ : syracuseStep 1286495 = 1929743) B1929743
theorem B860699 : Blo 570811 860699 := bstep (se 1 (by rfl) ⟨645524, by rfl⟩ : syracuseStep 860699 = 1291049) B1291049
theorem B860879 : Blo 570811 860879 := bstep (se 1 (by rfl) ⟨645659, by rfl⟩ : syracuseStep 860879 = 1291319) B1291319
theorem B860891 : Blo 570811 860891 := bstep (se 1 (by rfl) ⟨645668, by rfl⟩ : syracuseStep 860891 = 1291337) B1291337
theorem B10068907 : Blo 570811 10068907 := bstep (se 1 (by rfl) ⟨7551680, by rfl⟩ : syracuseStep 10068907 = 15103361) B15103361
theorem B1221679 : Blo 570811 1221679 := bstep (se 1 (by rfl) ⟨916259, by rfl⟩ : syracuseStep 1221679 = 1832519) B1832519
theorem B1287215 : Blo 570811 1287215 := bstep (se 1 (by rfl) ⟨965411, by rfl⟩ : syracuseStep 1287215 = 1930823) B1930823
theorem B861305 : Blo 570811 861305 := bstep (se 2 (by rfl) ⟨322989, by rfl⟩ : syracuseStep 861305 = 645979) B645979
theorem B1221799 : Blo 570811 1221799 := bstep (se 1 (by rfl) ⟨916349, by rfl⟩ : syracuseStep 1221799 = 1832699) B1832699
theorem B2172359 : Blo 570811 2172359 := bstep (se 1 (by rfl) ⟨1629269, by rfl⟩ : syracuseStep 2172359 = 3258539) B3258539
theorem B1091063 : Blo 570811 1091063 := bstep (se 1 (by rfl) ⟨818297, by rfl⟩ : syracuseStep 1091063 = 1636595) B1636595
theorem B4335119 : Blo 570811 4335119 := bstep (se 1 (by rfl) ⟨3251339, by rfl⟩ : syracuseStep 4335119 = 6502679) B6502679
theorem B3712549 : Blo 570811 3712549 := bstep (se 4 (by rfl) ⟨348051, by rfl⟩ : syracuseStep 3712549 = 696103) B696103
theorem B8824439 : Blo 570811 8824439 := bstep (se 1 (by rfl) ⟨6618329, by rfl⟩ : syracuseStep 8824439 = 13236659) B13236659
theorem B1287863 : Blo 570811 1287863 := bstep (se 1 (by rfl) ⟨965897, by rfl⟩ : syracuseStep 1287863 = 1931795) B1931795
theorem B14722883 : Blo 570811 14722883 := bstep (se 1 (by rfl) ⟨11042162, by rfl⟩ : syracuseStep 14722883 = 22084325) B22084325
theorem B862175 : Blo 570811 862175 := bstep (se 1 (by rfl) ⟨646631, by rfl⟩ : syracuseStep 862175 = 1293263) B1293263
theorem B862187 : Blo 570811 862187 := bstep (se 1 (by rfl) ⟨646640, by rfl⟩ : syracuseStep 862187 = 1293281) B1293281
theorem B1288313 : Blo 570811 1288313 := bstep (se 2 (by rfl) ⟨483117, by rfl⟩ : syracuseStep 1288313 = 966235) B966235
theorem B3910151 : Blo 570811 3910151 := bstep (se 1 (by rfl) ⟨2932613, by rfl⟩ : syracuseStep 3910151 = 5865227) B5865227
theorem B2173985 : Blo 570811 2173985 := bstep (se 2 (by rfl) ⟨815244, by rfl⟩ : syracuseStep 2173985 = 1630489) B1630489
theorem B1158313 : Blo 570811 1158313 := bstep (se 2 (by rfl) ⟨434367, by rfl⟩ : syracuseStep 1158313 = 868735) B868735
theorem B1223849 : Blo 570811 1223849 := bstep (se 2 (by rfl) ⟨458943, by rfl⟩ : syracuseStep 1223849 = 917887) B917887
theorem B1289627 : Blo 570811 1289627 := bstep (se 1 (by rfl) ⟨967220, by rfl⟩ : syracuseStep 1289627 = 1934441) B1934441
theorem B2174471 : Blo 570811 2174471 := bstep (se 1 (by rfl) ⟨1630853, by rfl⟩ : syracuseStep 2174471 = 3261707) B3261707
theorem B1158799 : Blo 570811 1158799 := bstep (se 1 (by rfl) ⟨869099, by rfl⟩ : syracuseStep 1158799 = 1738199) B1738199
theorem B1290203 : Blo 570811 1290203 := bstep (se 1 (by rfl) ⟨967652, by rfl⟩ : syracuseStep 1290203 = 1935305) B1935305
theorem B2174957 : Blo 570811 2174957 := bstep (se 3 (by rfl) ⟨407804, by rfl⟩ : syracuseStep 2174957 = 815609) B815609
theorem B100642823 : Blo 570811 100642823 := bstep (se 1 (by rfl) ⟨75482117, by rfl⟩ : syracuseStep 100642823 = 150964235) B150964235
theorem B1290383 : Blo 570811 1290383 := bstep (se 1 (by rfl) ⟨967787, by rfl⟩ : syracuseStep 1290383 = 1935575) B1935575
theorem B1290473 : Blo 570811 1290473 := bstep (se 2 (by rfl) ⟨483927, by rfl⟩ : syracuseStep 1290473 = 967855) B967855
theorem B2175275 : Blo 570811 2175275 := bstep (se 1 (by rfl) ⟨1631456, by rfl⟩ : syracuseStep 2175275 = 3262913) B3262913
theorem B1290599 : Blo 570811 1290599 := bstep (se 1 (by rfl) ⟨967949, by rfl⟩ : syracuseStep 1290599 = 1935899) B1935899
theorem B1291175 : Blo 570811 1291175 := bstep (se 1 (by rfl) ⟨968381, by rfl⟩ : syracuseStep 1291175 = 1936763) B1936763
theorem B963535 : Blo 570811 963535 := bstep (se 1 (by rfl) ⟨722651, by rfl⟩ : syracuseStep 963535 = 1445303) B1445303
theorem B570855 : Blo 570811 570855 := bstep (se 1 (by rfl) ⟨428141, by rfl⟩ : syracuseStep 570855 = 856283) B856283
theorem B570863 : Blo 570811 570863 := bstep (se 1 (by rfl) ⟨428147, by rfl⟩ : syracuseStep 570863 = 856295) B856295
theorem B570971 : Blo 570811 570971 := bstep (se 1 (by rfl) ⟨428228, by rfl⟩ : syracuseStep 570971 = 856457) B856457
theorem B571035 : Blo 570811 571035 := bstep (se 1 (by rfl) ⟨428276, by rfl⟩ : syracuseStep 571035 = 856553) B856553
theorem B571119 : Blo 570811 571119 := bstep (se 1 (by rfl) ⟨428339, by rfl⟩ : syracuseStep 571119 = 856679) B856679
theorem B571207 : Blo 570811 571207 := bstep (se 1 (by rfl) ⟨428405, by rfl⟩ : syracuseStep 571207 = 856811) B856811
theorem B1292111 : Blo 570811 1292111 := bstep (se 1 (by rfl) ⟨969083, by rfl⟩ : syracuseStep 1292111 = 1938167) B1938167
theorem B571227 : Blo 570811 571227 := bstep (se 1 (by rfl) ⟨428420, by rfl⟩ : syracuseStep 571227 = 856841) B856841
theorem B1652609 : Blo 570811 1652609 := bstep (se 2 (by rfl) ⟨619728, by rfl⟩ : syracuseStep 1652609 = 1239457) B1239457
theorem B571295 : Blo 570811 571295 := bstep (se 1 (by rfl) ⟨428471, by rfl⟩ : syracuseStep 571295 = 856943) B856943
theorem B6961153 : Blo 570811 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B964649 : Blo 570811 964649 := bstep (se 2 (by rfl) ⟨361743, by rfl⟩ : syracuseStep 964649 = 723487) B723487
theorem B571463 : Blo 570811 571463 := bstep (se 1 (by rfl) ⟨428597, by rfl⟩ : syracuseStep 571463 = 857195) B857195
theorem B1292471 : Blo 570811 1292471 := bstep (se 1 (by rfl) ⟨969353, by rfl⟩ : syracuseStep 1292471 = 1938707) B1938707
theorem B571623 : Blo 570811 571623 := bstep (se 1 (by rfl) ⟨428717, by rfl⟩ : syracuseStep 571623 = 857435) B857435
theorem B5519623 : Blo 570811 5519623 := bstep (se 1 (by rfl) ⟨4139717, by rfl⟩ : syracuseStep 5519623 = 8279435) B8279435
theorem B2177387 : Blo 570811 2177387 := bstep (se 1 (by rfl) ⟨1633040, by rfl⟩ : syracuseStep 2177387 = 3266081) B3266081
theorem B571807 : Blo 570811 571807 := bstep (se 1 (by rfl) ⟨428855, by rfl⟩ : syracuseStep 571807 = 857711) B857711
theorem B571855 : Blo 570811 571855 := bstep (se 1 (by rfl) ⟨428891, by rfl⟩ : syracuseStep 571855 = 857783) B857783
theorem B571879 : Blo 570811 571879 := bstep (se 1 (by rfl) ⟨428909, by rfl⟩ : syracuseStep 571879 = 857819) B857819
theorem B1292831 : Blo 570811 1292831 := bstep (se 1 (by rfl) ⟨969623, by rfl⟩ : syracuseStep 1292831 = 1939247) B1939247
theorem B571995 : Blo 570811 571995 := bstep (se 1 (by rfl) ⟨428996, by rfl⟩ : syracuseStep 571995 = 857993) B857993
theorem B965263 : Blo 570811 965263 := bstep (se 1 (by rfl) ⟨723947, by rfl⟩ : syracuseStep 965263 = 1447895) B1447895
theorem B572063 : Blo 570811 572063 := bstep (se 1 (by rfl) ⟨429047, by rfl⟩ : syracuseStep 572063 = 858095) B858095
theorem B2898665 : Blo 570811 2898665 := bstep (se 2 (by rfl) ⟨1086999, by rfl⟩ : syracuseStep 2898665 = 2173999) B2173999
theorem B1293065 : Blo 570811 1293065 := bstep (se 2 (by rfl) ⟨484899, by rfl⟩ : syracuseStep 1293065 = 969799) B969799
theorem B572231 : Blo 570811 572231 := bstep (se 1 (by rfl) ⟨429173, by rfl⟩ : syracuseStep 572231 = 858347) B858347
theorem B572271 : Blo 570811 572271 := bstep (se 1 (by rfl) ⟨429203, by rfl⟩ : syracuseStep 572271 = 858407) B858407
theorem B15678359 : Blo 570811 15678359 := bstep (se 1 (by rfl) ⟨11758769, by rfl⟩ : syracuseStep 15678359 = 23517539) B23517539
theorem B572327 : Blo 570811 572327 := bstep (se 1 (by rfl) ⟨429245, by rfl⟩ : syracuseStep 572327 = 858491) B858491
theorem B572507 : Blo 570811 572507 := bstep (se 1 (by rfl) ⟨429380, by rfl⟩ : syracuseStep 572507 = 858761) B858761
theorem B572623 : Blo 570811 572623 := bstep (se 1 (by rfl) ⟨429467, by rfl⟩ : syracuseStep 572623 = 858935) B858935
theorem B572647 : Blo 570811 572647 := bstep (se 1 (by rfl) ⟨429485, by rfl⟩ : syracuseStep 572647 = 858971) B858971
theorem B572743 : Blo 570811 572743 := bstep (se 1 (by rfl) ⟨429557, by rfl⟩ : syracuseStep 572743 = 859115) B859115
theorem B572879 : Blo 570811 572879 := bstep (se 1 (by rfl) ⟨429659, by rfl⟩ : syracuseStep 572879 = 859319) B859319
theorem B573039 : Blo 570811 573039 := bstep (se 1 (by rfl) ⟨429779, by rfl⟩ : syracuseStep 573039 = 859559) B859559
theorem B573095 : Blo 570811 573095 := bstep (se 1 (by rfl) ⟨429821, by rfl⟩ : syracuseStep 573095 = 859643) B859643
theorem B573159 : Blo 570811 573159 := bstep (se 1 (by rfl) ⟨429869, by rfl⟩ : syracuseStep 573159 = 859739) B859739
theorem B1031945 : Blo 570811 1031945 := bstep (se 2 (by rfl) ⟨386979, by rfl⟩ : syracuseStep 1031945 = 773959) B773959
theorem B573215 : Blo 570811 573215 := bstep (se 1 (by rfl) ⟨429911, by rfl⟩ : syracuseStep 573215 = 859823) B859823
theorem B573295 : Blo 570811 573295 := bstep (se 1 (by rfl) ⟨429971, by rfl⟩ : syracuseStep 573295 = 859943) B859943
theorem B573351 : Blo 570811 573351 := bstep (se 1 (by rfl) ⟨430013, by rfl⟩ : syracuseStep 573351 = 860027) B860027
theorem B2441171 : Blo 570811 2441171 := bstep (se 1 (by rfl) ⟨1830878, by rfl⟩ : syracuseStep 2441171 = 3661757) B3661757
theorem B573631 : Blo 570811 573631 := bstep (se 1 (by rfl) ⟨430223, by rfl⟩ : syracuseStep 573631 = 860447) B860447
theorem B573647 : Blo 570811 573647 := bstep (se 1 (by rfl) ⟨430235, by rfl⟩ : syracuseStep 573647 = 860471) B860471
theorem B573695 : Blo 570811 573695 := bstep (se 1 (by rfl) ⟨430271, by rfl⟩ : syracuseStep 573695 = 860543) B860543
theorem B573743 : Blo 570811 573743 := bstep (se 1 (by rfl) ⟨430307, by rfl⟩ : syracuseStep 573743 = 860615) B860615
theorem B24789509 : Blo 570811 24789509 := bstep (se 4 (by rfl) ⟨2324016, by rfl⟩ : syracuseStep 24789509 = 4648033) B4648033
theorem B573979 : Blo 570811 573979 := bstep (se 1 (by rfl) ⟨430484, by rfl⟩ : syracuseStep 573979 = 860969) B860969
theorem B573983 : Blo 570811 573983 := bstep (se 1 (by rfl) ⟨430487, by rfl⟩ : syracuseStep 573983 = 860975) B860975
theorem B574063 : Blo 570811 574063 := bstep (se 1 (by rfl) ⟨430547, by rfl⟩ : syracuseStep 574063 = 861095) B861095
theorem B574119 : Blo 570811 574119 := bstep (se 1 (by rfl) ⟨430589, by rfl⟩ : syracuseStep 574119 = 861179) B861179
theorem B574159 : Blo 570811 574159 := bstep (se 1 (by rfl) ⟨430619, by rfl⟩ : syracuseStep 574159 = 861239) B861239
theorem B574239 : Blo 570811 574239 := bstep (se 1 (by rfl) ⟨430679, by rfl⟩ : syracuseStep 574239 = 861359) B861359
theorem B2442095 : Blo 570811 2442095 := bstep (se 1 (by rfl) ⟨1831571, by rfl⟩ : syracuseStep 2442095 = 3663143) B3663143
theorem B2180105 : Blo 570811 2180105 := bstep (se 2 (by rfl) ⟨817539, by rfl⟩ : syracuseStep 2180105 = 1635079) B1635079
theorem B2180135 : Blo 570811 2180135 := bstep (se 1 (by rfl) ⟨1635101, by rfl⟩ : syracuseStep 2180135 = 3270203) B3270203
theorem B574511 : Blo 570811 574511 := bstep (se 1 (by rfl) ⟨430883, by rfl⟩ : syracuseStep 574511 = 861767) B861767
theorem B4342895 : Blo 570811 4342895 := bstep (se 1 (by rfl) ⟨3257171, by rfl⟩ : syracuseStep 4342895 = 6514343) B6514343
theorem B574575 : Blo 570811 574575 := bstep (se 1 (by rfl) ⟨430931, by rfl⟩ : syracuseStep 574575 = 861863) B861863
theorem B574631 : Blo 570811 574631 := bstep (se 1 (by rfl) ⟨430973, by rfl⟩ : syracuseStep 574631 = 861947) B861947
theorem B574655 : Blo 570811 574655 := bstep (se 1 (by rfl) ⟨430991, by rfl⟩ : syracuseStep 574655 = 861983) B861983
theorem B574687 : Blo 570811 574687 := bstep (se 1 (by rfl) ⟨431015, by rfl⟩ : syracuseStep 574687 = 862031) B862031
theorem B574767 : Blo 570811 574767 := bstep (se 1 (by rfl) ⟨431075, by rfl⟩ : syracuseStep 574767 = 862151) B862151
theorem B968105 : Blo 570811 968105 := bstep (se 2 (by rfl) ⟨363039, by rfl⟩ : syracuseStep 968105 = 726079) B726079
theorem B2442811 : Blo 570811 2442811 := bstep (se 1 (by rfl) ⟨1832108, by rfl⟩ : syracuseStep 2442811 = 3664217) B3664217
theorem B869993 : Blo 570811 869993 := bstep (se 2 (by rfl) ⟨326247, by rfl⟩ : syracuseStep 869993 = 652495) B652495
theorem B2180803 : Blo 570811 2180803 := bstep (se 1 (by rfl) ⟨1635602, by rfl⟩ : syracuseStep 2180803 = 3271205) B3271205
theorem B8276087 : Blo 570811 8276087 := bstep (se 1 (by rfl) ⟨6207065, by rfl⟩ : syracuseStep 8276087 = 12414131) B12414131
theorem B2181275 : Blo 570811 2181275 := bstep (se 1 (by rfl) ⟨1635956, by rfl⟩ : syracuseStep 2181275 = 3271913) B3271913
theorem B11717399 : Blo 570811 11717399 := bstep (se 1 (by rfl) ⟨8788049, by rfl⟩ : syracuseStep 11717399 = 17576099) B17576099
theorem B4344839 : Blo 570811 4344839 := bstep (se 1 (by rfl) ⟨3258629, by rfl⟩ : syracuseStep 4344839 = 6517259) B6517259
theorem B642811 : Blo 570811 642811 := bstep (se 1 (by rfl) ⟨482108, by rfl⟩ : syracuseStep 642811 = 964217) B964217
theorem B643135 : Blo 570811 643135 := bstep (se 1 (by rfl) ⟨482351, by rfl⟩ : syracuseStep 643135 = 964703) B964703
theorem B2445511 : Blo 570811 2445511 := bstep (se 1 (by rfl) ⟨1834133, by rfl⟩ : syracuseStep 2445511 = 3668267) B3668267
theorem B1626331 : Blo 570811 1626331 := bstep (se 1 (by rfl) ⟨1219748, by rfl⟩ : syracuseStep 1626331 = 2439497) B2439497
theorem B6542045 : Blo 570811 6542045 := bstep (se 3 (by rfl) ⟨1226633, by rfl⟩ : syracuseStep 6542045 = 2453267) B2453267
theorem B643999 : Blo 570811 643999 := bstep (se 1 (by rfl) ⟨482999, by rfl⟩ : syracuseStep 643999 = 965999) B965999
theorem B1102817 : Blo 570811 1102817 := bstep (se 2 (by rfl) ⟨413556, by rfl⟩ : syracuseStep 1102817 = 827113) B827113
theorem B644251 : Blo 570811 644251 := bstep (se 1 (by rfl) ⟨483188, by rfl⟩ : syracuseStep 644251 = 966377) B966377
theorem B13981081 : Blo 570811 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B4904621 : Blo 570811 4904621 := bstep (se 3 (by rfl) ⟨919616, by rfl⟩ : syracuseStep 4904621 = 1839233) B1839233
theorem B644935 : Blo 570811 644935 := bstep (se 1 (by rfl) ⟨483701, by rfl⟩ : syracuseStep 644935 = 967403) B967403
theorem B4970573 : Blo 570811 4970573 := bstep (se 3 (by rfl) ⟨931982, by rfl⟩ : syracuseStep 4970573 = 1863965) B1863965
theorem B645583 : Blo 570811 645583 := bstep (se 1 (by rfl) ⟨484187, by rfl⟩ : syracuseStep 645583 = 968375) B968375
theorem B4413971 : Blo 570811 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B133487189 : Blo 570811 133487189 := bstep (se 8 (by rfl) ⟨782151, by rfl⟩ : syracuseStep 133487189 = 1564303) B1564303
theorem B4905683 : Blo 570811 4905683 := bstep (se 1 (by rfl) ⟨3679262, by rfl⟩ : syracuseStep 4905683 = 7358525) B7358525
theorem B4348727 : Blo 570811 4348727 := bstep (se 1 (by rfl) ⟨3261545, by rfl⟩ : syracuseStep 4348727 = 6523091) B6523091
theorem B646375 : Blo 570811 646375 := bstep (se 1 (by rfl) ⟨484781, by rfl⟩ : syracuseStep 646375 = 969563) B969563
theorem B3136745 : Blo 570811 3136745 := bstep (se 2 (by rfl) ⟨1176279, by rfl⟩ : syracuseStep 3136745 = 2352559) B2352559
theorem B34331921 : Blo 570811 34331921 := bstep (se 2 (by rfl) ⟨12874470, by rfl⟩ : syracuseStep 34331921 = 25748941) B25748941
theorem B4349213 : Blo 570811 4349213 := bstep (se 3 (by rfl) ⟨815477, by rfl⟩ : syracuseStep 4349213 = 1630955) B1630955
theorem B1465847 : Blo 570811 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B2351783 : Blo 570811 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B2613935 : Blo 570811 2613935 := bstep (se 1 (by rfl) ⟨1960451, by rfl⟩ : syracuseStep 2613935 = 3920903) B3920903
theorem B1303247 : Blo 570811 1303247 := bstep (se 1 (by rfl) ⟨977435, by rfl⟩ : syracuseStep 1303247 = 1954871) B1954871
theorem B29844197 : Blo 570811 29844197 := bstep (se 4 (by rfl) ⟨2797893, by rfl⟩ : syracuseStep 29844197 = 5595787) B5595787
theorem B2319673 : Blo 570811 2319673 := bstep (se 2 (by rfl) ⟨869877, by rfl⟩ : syracuseStep 2319673 = 1739755) B1739755
theorem B5596723 : Blo 570811 5596723 := bstep (se 1 (by rfl) ⟨4197542, by rfl⟩ : syracuseStep 5596723 = 8395085) B8395085
theorem B2319997 : Blo 570811 2319997 := bstep (se 3 (by rfl) ⟨434999, by rfl⟩ : syracuseStep 2319997 = 869999) B869999
theorem B3106457 : Blo 570811 3106457 := bstep (se 2 (by rfl) ⟨1164921, by rfl⟩ : syracuseStep 3106457 = 2329843) B2329843
theorem B9758393 : Blo 570811 9758393 := bstep (se 2 (by rfl) ⟨3659397, by rfl⟩ : syracuseStep 9758393 = 7318795) B7318795
theorem B1566803 : Blo 570811 1566803 := bstep (se 1 (by rfl) ⟨1175102, by rfl⟩ : syracuseStep 1566803 = 2350205) B2350205
theorem B7072409 : Blo 570811 7072409 := bstep (se 2 (by rfl) ⟨2652153, by rfl⟩ : syracuseStep 7072409 = 5304307) B5304307
theorem B9431801 : Blo 570811 9431801 := bstep (se 2 (by rfl) ⟨3536925, by rfl⟩ : syracuseStep 9431801 = 7073851) B7073851
theorem B1928015 : Blo 570811 1928015 := bstep (se 1 (by rfl) ⟨1446011, by rfl⟩ : syracuseStep 1928015 = 2892023) B2892023
theorem B5237797 : Blo 570811 5237797 := bstep (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) B982087
theorem B1469623 : Blo 570811 1469623 := bstep (se 1 (by rfl) ⟨1102217, by rfl⟩ : syracuseStep 1469623 = 2204435) B2204435
theorem B3665807 : Blo 570811 3665807 := bstep (se 1 (by rfl) ⟨2749355, by rfl⟩ : syracuseStep 3665807 = 5498711) B5498711
theorem B2061065 : Blo 570811 2061065 := bstep (se 2 (by rfl) ⟨772899, by rfl⟩ : syracuseStep 2061065 = 1545799) B1545799
theorem B5043383 : Blo 570811 5043383 := bstep (se 1 (by rfl) ⟨3782537, by rfl⟩ : syracuseStep 5043383 = 7565075) B7565075
theorem B980623 : Blo 570811 980623 := bstep (se 1 (by rfl) ⟨735467, by rfl⟩ : syracuseStep 980623 = 1470935) B1470935
theorem B5502629 : Blo 570811 5502629 := bstep (se 4 (by rfl) ⟨515871, by rfl⟩ : syracuseStep 5502629 = 1031743) B1031743
theorem B10975733 : Blo 570811 10975733 := bstep (se 5 (by rfl) ⟨514487, by rfl⟩ : syracuseStep 10975733 = 1028975) B1028975
theorem B1374727 : Blo 570811 1374727 := bstep (se 1 (by rfl) ⟨1031045, by rfl⟩ : syracuseStep 1374727 = 2062091) B2062091
theorem B817705 : Blo 570811 817705 := bstep (se 2 (by rfl) ⟨306639, by rfl⟩ : syracuseStep 817705 = 613279) B613279
theorem B1932011 : Blo 570811 1932011 := bstep (se 1 (by rfl) ⟨1449008, by rfl⟩ : syracuseStep 1932011 = 2898017) B2898017
theorem B1374985 : Blo 570811 1374985 := bstep (se 2 (by rfl) ⟨515619, by rfl⟩ : syracuseStep 1374985 = 1031239) B1031239
theorem B1932119 : Blo 570811 1932119 := bstep (se 1 (by rfl) ⟨1449089, by rfl⟩ : syracuseStep 1932119 = 2898179) B2898179
theorem B6520175 : Blo 570811 6520175 := bstep (se 1 (by rfl) ⟨4890131, by rfl⟩ : syracuseStep 6520175 = 9780263) B9780263
theorem B1179049 : Blo 570811 1179049 := bstep (se 2 (by rfl) ⟨442143, by rfl⟩ : syracuseStep 1179049 = 884287) B884287
theorem B1932929 : Blo 570811 1932929 := bstep (se 2 (by rfl) ⟨724848, by rfl⟩ : syracuseStep 1932929 = 1449697) B1449697
theorem B10714799 : Blo 570811 10714799 := bstep (se 1 (by rfl) ⟨8036099, by rfl⟩ : syracuseStep 10714799 = 16072199) B16072199
theorem B1933199 : Blo 570811 1933199 := bstep (se 1 (by rfl) ⟨1449899, by rfl⟩ : syracuseStep 1933199 = 2899799) B2899799
theorem B3670265 : Blo 570811 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B918335 : Blo 570811 918335 := bstep (se 1 (by rfl) ⟨688751, by rfl⟩ : syracuseStep 918335 = 1377503) B1377503
theorem B722459 : Blo 570811 722459 := bstep (se 1 (by rfl) ⟨541844, by rfl⟩ : syracuseStep 722459 = 1083689) B1083689
theorem B3475325 : Blo 570811 3475325 := bstep (se 3 (by rfl) ⟨651623, by rfl⟩ : syracuseStep 3475325 = 1303247) B1303247
theorem B1378187 : Blo 570811 1378187 := bstep (se 1 (by rfl) ⟨1033640, by rfl⟩ : syracuseStep 1378187 = 2067281) B2067281
theorem B4950065 : Blo 570811 4950065 := bstep (se 2 (by rfl) ⟨1856274, by rfl⟩ : syracuseStep 4950065 = 3712549) B3712549
theorem B1378387 : Blo 570811 1378387 := bstep (se 1 (by rfl) ⟨1033790, by rfl⟩ : syracuseStep 1378387 = 2067581) B2067581
theorem B6621331 : Blo 570811 6621331 := bstep (se 1 (by rfl) ⟨4965998, by rfl⟩ : syracuseStep 6621331 = 9931997) B9931997
theorem B920297 : Blo 570811 920297 := bstep (se 2 (by rfl) ⟨345111, by rfl⟩ : syracuseStep 920297 = 690223) B690223
theorem B4197203 : Blo 570811 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B4361363 : Blo 570811 4361363 := bstep (se 1 (by rfl) ⟨3271022, by rfl⟩ : syracuseStep 4361363 = 6542045) B6542045
theorem B47189789 : Blo 570811 47189789 := bstep (se 3 (by rfl) ⟨8848085, by rfl⟩ : syracuseStep 47189789 = 17696171) B17696171
theorem B1445759 : Blo 570811 1445759 := bstep (se 1 (by rfl) ⟨1084319, by rfl⟩ : syracuseStep 1445759 = 2168639) B2168639
theorem B6983729 : Blo 570811 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B3313715 : Blo 570811 3313715 := bstep (se 1 (by rfl) ⟨2485286, by rfl⟩ : syracuseStep 3313715 = 4970573) B4970573
theorem B1445971 : Blo 570811 1445971 := bstep (se 1 (by rfl) ⟨1084478, by rfl⟩ : syracuseStep 1445971 = 2168957) B2168957
theorem B2756699 : Blo 570811 2756699 := bstep (se 1 (by rfl) ⟨2067524, by rfl⟩ : syracuseStep 2756699 = 4135049) B4135049
theorem B1544417 : Blo 570811 1544417 := bstep (se 2 (by rfl) ⟨579156, by rfl⟩ : syracuseStep 1544417 = 1158313) B1158313
theorem B1446407 : Blo 570811 1446407 := bstep (se 1 (by rfl) ⟨1084805, by rfl⟩ : syracuseStep 1446407 = 2169611) B2169611
theorem B3674753 : Blo 570811 3674753 := bstep (se 2 (by rfl) ⟨1378032, by rfl⟩ : syracuseStep 3674753 = 2756065) B2756065
theorem B725755 : Blo 570811 725755 := bstep (se 1 (by rfl) ⟨544316, by rfl⟩ : syracuseStep 725755 = 1088633) B1088633
theorem B1545065 : Blo 570811 1545065 := bstep (se 2 (by rfl) ⟨579399, by rfl⟩ : syracuseStep 1545065 = 1158799) B1158799
theorem B857081 : Blo 570811 857081 := bstep (se 2 (by rfl) ⟨321405, by rfl⟩ : syracuseStep 857081 = 642811) B642811
theorem B857279 : Blo 570811 857279 := bstep (se 1 (by rfl) ⟨642959, by rfl⟩ : syracuseStep 857279 = 1285919) B1285919
theorem B857423 : Blo 570811 857423 := bstep (se 1 (by rfl) ⟨643067, by rfl⟩ : syracuseStep 857423 = 1286135) B1286135
theorem B1447247 : Blo 570811 1447247 := bstep (se 1 (by rfl) ⟨1085435, by rfl⟩ : syracuseStep 1447247 = 2170871) B2170871
theorem B857513 : Blo 570811 857513 := bstep (se 2 (by rfl) ⟨321567, by rfl⟩ : syracuseStep 857513 = 643135) B643135
theorem B1447379 : Blo 570811 1447379 := bstep (se 1 (by rfl) ⟨1085534, by rfl⟩ : syracuseStep 1447379 = 2171069) B2171069
theorem B857567 : Blo 570811 857567 := bstep (se 1 (by rfl) ⟨643175, by rfl⟩ : syracuseStep 857567 = 1286351) B1286351
theorem B857663 : Blo 570811 857663 := bstep (se 1 (by rfl) ⟨643247, by rfl⟩ : syracuseStep 857663 = 1286495) B1286495
theorem B2168441 : Blo 570811 2168441 := bstep (se 2 (by rfl) ⟨813165, by rfl⟩ : syracuseStep 2168441 = 1626331) B1626331
theorem B19896131 : Blo 570811 19896131 := bstep (se 1 (by rfl) ⟨14922098, by rfl⟩ : syracuseStep 19896131 = 29844197) B29844197
theorem B858143 : Blo 570811 858143 := bstep (se 1 (by rfl) ⟨643607, by rfl⟩ : syracuseStep 858143 = 1287215) B1287215
theorem B1448239 : Blo 570811 1448239 := bstep (se 1 (by rfl) ⟨1086179, by rfl⟩ : syracuseStep 1448239 = 2172359) B2172359
theorem B727375 : Blo 570811 727375 := bstep (se 1 (by rfl) ⟨545531, by rfl⟩ : syracuseStep 727375 = 1091063) B1091063
theorem B2890079 : Blo 570811 2890079 := bstep (se 1 (by rfl) ⟨2167559, by rfl⟩ : syracuseStep 2890079 = 4335119) B4335119
theorem B2070971 : Blo 570811 2070971 := bstep (se 1 (by rfl) ⟨1553228, by rfl⟩ : syracuseStep 2070971 = 3106457) B3106457
theorem B858575 : Blo 570811 858575 := bstep (se 1 (by rfl) ⟨643931, by rfl⟩ : syracuseStep 858575 = 1287863) B1287863
theorem B858665 : Blo 570811 858665 := bstep (se 2 (by rfl) ⟨321999, by rfl⟩ : syracuseStep 858665 = 643999) B643999
theorem B1284713 : Blo 570811 1284713 := bstep (se 2 (by rfl) ⟨481767, by rfl⟩ : syracuseStep 1284713 = 963535) B963535
theorem B10427069 : Blo 570811 10427069 := bstep (se 3 (by rfl) ⟨1955075, by rfl⟩ : syracuseStep 10427069 = 3910151) B3910151
theorem B858875 : Blo 570811 858875 := bstep (se 1 (by rfl) ⟨644156, by rfl⟩ : syracuseStep 858875 = 1288313) B1288313
theorem B859001 : Blo 570811 859001 := bstep (se 2 (by rfl) ⟨322125, by rfl⟩ : syracuseStep 859001 = 644251) B644251
theorem B1285343 : Blo 570811 1285343 := bstep (se 1 (by rfl) ⟨964007, by rfl⟩ : syracuseStep 1285343 = 1928015) B1928015
theorem B1449323 : Blo 570811 1449323 := bstep (se 1 (by rfl) ⟨1086992, by rfl⟩ : syracuseStep 1449323 = 2173985) B2173985
theorem B859751 : Blo 570811 859751 := bstep (se 1 (by rfl) ⟨644813, by rfl⟩ : syracuseStep 859751 = 1289627) B1289627
theorem B1449647 : Blo 570811 1449647 := bstep (se 1 (by rfl) ⟨1087235, by rfl⟩ : syracuseStep 1449647 = 2174471) B2174471
theorem B859913 : Blo 570811 859913 := bstep (se 2 (by rfl) ⟨322467, by rfl⟩ : syracuseStep 859913 = 644935) B644935
theorem B860135 : Blo 570811 860135 := bstep (se 1 (by rfl) ⟨645101, by rfl⟩ : syracuseStep 860135 = 1290203) B1290203
theorem B1449971 : Blo 570811 1449971 := bstep (se 1 (by rfl) ⟨1087478, by rfl⟩ : syracuseStep 1449971 = 2174957) B2174957
theorem B9281537 : Blo 570811 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B860255 : Blo 570811 860255 := bstep (se 1 (by rfl) ⟨645191, by rfl⟩ : syracuseStep 860255 = 1290383) B1290383
theorem B860315 : Blo 570811 860315 := bstep (se 1 (by rfl) ⟨645236, by rfl⟩ : syracuseStep 860315 = 1290473) B1290473
theorem B1450183 : Blo 570811 1450183 := bstep (se 1 (by rfl) ⟨1087637, by rfl⟩ : syracuseStep 1450183 = 2175275) B2175275
theorem B860399 : Blo 570811 860399 := bstep (se 1 (by rfl) ⟨645299, by rfl⟩ : syracuseStep 860399 = 1290599) B1290599
theorem B860777 : Blo 570811 860777 := bstep (se 2 (by rfl) ⟨322791, by rfl⟩ : syracuseStep 860777 = 645583) B645583
theorem B8364653 : Blo 570811 8364653 := bstep (se 3 (by rfl) ⟨1568372, by rfl⟩ : syracuseStep 8364653 = 3136745) B3136745
theorem B860783 : Blo 570811 860783 := bstep (se 1 (by rfl) ⟨645587, by rfl⟩ : syracuseStep 860783 = 1291175) B1291175
theorem B1090273 : Blo 570811 1090273 := bstep (se 2 (by rfl) ⟨408852, by rfl⟩ : syracuseStep 1090273 = 817705) B817705
theorem B1287017 : Blo 570811 1287017 := bstep (se 2 (by rfl) ⟨482631, by rfl⟩ : syracuseStep 1287017 = 965263) B965263
theorem B861407 : Blo 570811 861407 := bstep (se 1 (by rfl) ⟨646055, by rfl⟩ : syracuseStep 861407 = 1292111) B1292111
theorem B861647 : Blo 570811 861647 := bstep (se 1 (by rfl) ⟨646235, by rfl⟩ : syracuseStep 861647 = 1292471) B1292471
theorem B1451591 : Blo 570811 1451591 := bstep (se 1 (by rfl) ⟨1088693, by rfl⟩ : syracuseStep 1451591 = 2177387) B2177387
theorem B861833 : Blo 570811 861833 := bstep (se 2 (by rfl) ⟨323187, by rfl⟩ : syracuseStep 861833 = 646375) B646375
theorem B7317155 : Blo 570811 7317155 := bstep (se 1 (by rfl) ⟨5487866, by rfl⟩ : syracuseStep 7317155 = 10975733) B10975733
theorem B861887 : Blo 570811 861887 := bstep (se 1 (by rfl) ⟨646415, by rfl⟩ : syracuseStep 861887 = 1292831) B1292831
theorem B1288007 : Blo 570811 1288007 := bstep (se 1 (by rfl) ⟨966005, by rfl⟩ : syracuseStep 1288007 = 1932011) B1932011
theorem B862043 : Blo 570811 862043 := bstep (se 1 (by rfl) ⟨646532, by rfl⟩ : syracuseStep 862043 = 1293065) B1293065
theorem B1288079 : Blo 570811 1288079 := bstep (se 1 (by rfl) ⟨966059, by rfl⟩ : syracuseStep 1288079 = 1932119) B1932119
theorem B1288619 : Blo 570811 1288619 := bstep (se 1 (by rfl) ⟨966464, by rfl⟩ : syracuseStep 1288619 = 1932929) B1932929
theorem B1288799 : Blo 570811 1288799 := bstep (se 1 (by rfl) ⟨966599, by rfl⟩ : syracuseStep 1288799 = 1933199) B1933199
theorem B1289159 : Blo 570811 1289159 := bstep (se 1 (by rfl) ⟨966869, by rfl⟩ : syracuseStep 1289159 = 1933739) B1933739
theorem B16526339 : Blo 570811 16526339 := bstep (se 1 (by rfl) ⟨12394754, by rfl⟩ : syracuseStep 16526339 = 24789509) B24789509
theorem B1289519 : Blo 570811 1289519 := bstep (se 1 (by rfl) ⟨967139, by rfl⟩ : syracuseStep 1289519 = 1934279) B1934279
theorem B1289555 : Blo 570811 1289555 := bstep (se 1 (by rfl) ⟨967166, by rfl⟩ : syracuseStep 1289555 = 1934333) B1934333
theorem B1453403 : Blo 570811 1453403 := bstep (se 1 (by rfl) ⟨1090052, by rfl⟩ : syracuseStep 1453403 = 2180105) B2180105
theorem B1453423 : Blo 570811 1453423 := bstep (se 1 (by rfl) ⟨1090067, by rfl⟩ : syracuseStep 1453423 = 2180135) B2180135
theorem B2895263 : Blo 570811 2895263 := bstep (se 1 (by rfl) ⟨2171447, by rfl⟩ : syracuseStep 2895263 = 4342895) B4342895
theorem B1289807 : Blo 570811 1289807 := bstep (se 1 (by rfl) ⟨967355, by rfl⟩ : syracuseStep 1289807 = 1934711) B1934711
theorem B11185897 : Blo 570811 11185897 := bstep (se 2 (by rfl) ⟨4194711, by rfl⟩ : syracuseStep 11185897 = 8389423) B8389423
theorem B1290095 : Blo 570811 1290095 := bstep (se 1 (by rfl) ⟨967571, by rfl⟩ : syracuseStep 1290095 = 1935143) B1935143
theorem B5517391 : Blo 570811 5517391 := bstep (se 1 (by rfl) ⟨4138043, by rfl⟩ : syracuseStep 5517391 = 8276087) B8276087
theorem B1454183 : Blo 570811 1454183 := bstep (se 1 (by rfl) ⟨1090637, by rfl⟩ : syracuseStep 1454183 = 2181275) B2181275
theorem B1290347 : Blo 570811 1290347 := bstep (se 1 (by rfl) ⟨967760, by rfl⟩ : syracuseStep 1290347 = 1935521) B1935521
theorem B1290527 : Blo 570811 1290527 := bstep (se 1 (by rfl) ⟨967895, by rfl⟩ : syracuseStep 1290527 = 1935791) B1935791
theorem B1749289 : Blo 570811 1749289 := bstep (se 2 (by rfl) ⟨655983, by rfl⟩ : syracuseStep 1749289 = 1311967) B1311967
theorem B3092897 : Blo 570811 3092897 := bstep (se 2 (by rfl) ⟨1159836, by rfl⟩ : syracuseStep 3092897 = 2319673) B2319673
theorem B7811599 : Blo 570811 7811599 := bstep (se 1 (by rfl) ⟨5858699, by rfl⟩ : syracuseStep 7811599 = 11717399) B11717399
theorem B2896559 : Blo 570811 2896559 := bstep (se 1 (by rfl) ⟨2172419, by rfl⟩ : syracuseStep 2896559 = 4344839) B4344839
theorem B3257081 : Blo 570811 3257081 := bstep (se 2 (by rfl) ⟨1221405, by rfl⟩ : syracuseStep 3257081 = 2442811) B2442811
theorem B3093329 : Blo 570811 3093329 := bstep (se 2 (by rfl) ⟨1159998, by rfl⟩ : syracuseStep 3093329 = 2319997) B2319997
theorem B1291247 : Blo 570811 1291247 := bstep (se 1 (by rfl) ⟨968435, by rfl⟩ : syracuseStep 1291247 = 1936871) B1936871
theorem B963967 : Blo 570811 963967 := bstep (se 1 (by rfl) ⟨722975, by rfl⟩ : syracuseStep 963967 = 1445951) B1445951
theorem B570907 : Blo 570811 570907 := bstep (se 1 (by rfl) ⟨428180, by rfl⟩ : syracuseStep 570907 = 856361) B856361
theorem B571087 : Blo 570811 571087 := bstep (se 1 (by rfl) ⟨428315, by rfl⟩ : syracuseStep 571087 = 856631) B856631
theorem B1226515 : Blo 570811 1226515 := bstep (se 1 (by rfl) ⟨919886, by rfl⟩ : syracuseStep 1226515 = 1839773) B1839773
theorem B1029971 : Blo 570811 1029971 := bstep (se 1 (by rfl) ⟨772478, by rfl⟩ : syracuseStep 1029971 = 1544957) B1544957
theorem B571327 : Blo 570811 571327 := bstep (se 1 (by rfl) ⟨428495, by rfl⟩ : syracuseStep 571327 = 856991) B856991
theorem B735211 : Blo 570811 735211 := bstep (se 1 (by rfl) ⟨551408, by rfl⟩ : syracuseStep 735211 = 1102817) B1102817
theorem B571455 : Blo 570811 571455 := bstep (se 1 (by rfl) ⟨428591, by rfl⟩ : syracuseStep 571455 = 857183) B857183
theorem B571495 : Blo 570811 571495 := bstep (se 1 (by rfl) ⟨428621, by rfl⟩ : syracuseStep 571495 = 857243) B857243
theorem B571951 : Blo 570811 571951 := bstep (se 1 (by rfl) ⟨428963, by rfl⟩ : syracuseStep 571951 = 857927) B857927
theorem B572351 : Blo 570811 572351 := bstep (se 1 (by rfl) ⟨429263, by rfl⟩ : syracuseStep 572351 = 858527) B858527
theorem B572399 : Blo 570811 572399 := bstep (se 1 (by rfl) ⟨429299, by rfl⟩ : syracuseStep 572399 = 858599) B858599
theorem B2899151 : Blo 570811 2899151 := bstep (se 1 (by rfl) ⟨2174363, by rfl⟩ : syracuseStep 2899151 = 4348727) B4348727
theorem B2932139 : Blo 570811 2932139 := bstep (se 1 (by rfl) ⟨2199104, by rfl⟩ : syracuseStep 2932139 = 4398209) B4398209
theorem B572895 : Blo 570811 572895 := bstep (se 1 (by rfl) ⟨429671, by rfl⟩ : syracuseStep 572895 = 859343) B859343
theorem B22887947 : Blo 570811 22887947 := bstep (se 1 (by rfl) ⟨17165960, by rfl⟩ : syracuseStep 22887947 = 34331921) B34331921
theorem B2899475 : Blo 570811 2899475 := bstep (se 1 (by rfl) ⟨2174606, by rfl⟩ : syracuseStep 2899475 = 4349213) B4349213
theorem B5488175 : Blo 570811 5488175 := bstep (se 1 (by rfl) ⟨4116131, by rfl⟩ : syracuseStep 5488175 = 8232263) B8232263
theorem B572975 : Blo 570811 572975 := bstep (se 1 (by rfl) ⟨429731, by rfl⟩ : syracuseStep 572975 = 859463) B859463
theorem B573083 : Blo 570811 573083 := bstep (se 1 (by rfl) ⟨429812, by rfl⟩ : syracuseStep 573083 = 859625) B859625
theorem B4406957 : Blo 570811 4406957 := bstep (se 3 (by rfl) ⟨826304, by rfl⟩ : syracuseStep 4406957 = 1652609) B1652609
theorem B573179 : Blo 570811 573179 := bstep (se 1 (by rfl) ⟨429884, by rfl⟩ : syracuseStep 573179 = 859769) B859769
theorem B573343 : Blo 570811 573343 := bstep (se 1 (by rfl) ⟨430007, by rfl⟩ : syracuseStep 573343 = 860015) B860015
theorem B966863 : Blo 570811 966863 := bstep (se 1 (by rfl) ⟨725147, by rfl⟩ : syracuseStep 966863 = 1450295) B1450295
theorem B3260681 : Blo 570811 3260681 := bstep (se 2 (by rfl) ⟨1222755, by rfl⟩ : syracuseStep 3260681 = 2445511) B2445511
theorem B573799 : Blo 570811 573799 := bstep (se 1 (by rfl) ⟨430349, by rfl⟩ : syracuseStep 573799 = 860699) B860699
theorem B573919 : Blo 570811 573919 := bstep (se 1 (by rfl) ⟨430439, by rfl⟩ : syracuseStep 573919 = 860879) B860879
theorem B573927 : Blo 570811 573927 := bstep (se 1 (by rfl) ⟨430445, by rfl⟩ : syracuseStep 573927 = 860891) B860891
theorem B574203 : Blo 570811 574203 := bstep (se 1 (by rfl) ⟨430652, by rfl⟩ : syracuseStep 574203 = 861305) B861305
theorem B5882959 : Blo 570811 5882959 := bstep (se 1 (by rfl) ⟨4412219, by rfl⟩ : syracuseStep 5882959 = 8824439) B8824439
theorem B967801 : Blo 570811 967801 := bstep (se 2 (by rfl) ⟨362925, by rfl⟩ : syracuseStep 967801 = 725851) B725851
theorem B6505595 : Blo 570811 6505595 := bstep (se 1 (by rfl) ⟨4879196, by rfl⟩ : syracuseStep 6505595 = 9758393) B9758393
theorem B9815255 : Blo 570811 9815255 := bstep (se 1 (by rfl) ⟨7361441, by rfl⟩ : syracuseStep 9815255 = 14722883) B14722883
theorem B574783 : Blo 570811 574783 := bstep (se 1 (by rfl) ⟨431087, by rfl⟩ : syracuseStep 574783 = 862175) B862175
theorem B574791 : Blo 570811 574791 := bstep (se 1 (by rfl) ⟨431093, by rfl⟩ : syracuseStep 574791 = 862187) B862187
theorem B2443871 : Blo 570811 2443871 := bstep (se 1 (by rfl) ⟨1832903, by rfl⟩ : syracuseStep 2443871 = 3665807) B3665807
theorem B67095215 : Blo 570811 67095215 := bstep (se 1 (by rfl) ⟨50321411, by rfl⟩ : syracuseStep 67095215 = 100642823) B100642823
theorem B7359497 : Blo 570811 7359497 := bstep (se 2 (by rfl) ⟨2759811, by rfl⟩ : syracuseStep 7359497 = 5519623) B5519623
theorem B3263597 : Blo 570811 3263597 := bstep (se 3 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 3263597 = 1223849) B1223849
theorem B5229989 : Blo 570811 5229989 := bstep (se 4 (by rfl) ⟨490311, by rfl⟩ : syracuseStep 5229989 = 980623) B980623
theorem B3362255 : Blo 570811 3362255 := bstep (se 1 (by rfl) ⟨2521691, by rfl⟩ : syracuseStep 3362255 = 5043383) B5043383
theorem B643099 : Blo 570811 643099 := bstep (se 1 (by rfl) ⟨482324, by rfl⟩ : syracuseStep 643099 = 964649) B964649
theorem B4346783 : Blo 570811 4346783 := bstep (se 1 (by rfl) ⟨3260087, by rfl⟩ : syracuseStep 4346783 = 6520175) B6520175
theorem B1627265 : Blo 570811 1627265 := bstep (se 2 (by rfl) ⟨610224, by rfl⟩ : syracuseStep 1627265 = 1220449) B1220449
theorem B1627447 : Blo 570811 1627447 := bstep (se 1 (by rfl) ⟨1220585, by rfl⟩ : syracuseStep 1627447 = 2441171) B2441171
theorem B2905631 : Blo 570811 2905631 := bstep (se 1 (by rfl) ⟨2179223, by rfl⟩ : syracuseStep 2905631 = 4358447) B4358447
theorem B1628063 : Blo 570811 1628063 := bstep (se 1 (by rfl) ⟨1221047, by rfl⟩ : syracuseStep 1628063 = 2442095) B2442095
theorem B12343549 : Blo 570811 12343549 := bstep (se 3 (by rfl) ⟨2314415, by rfl⟩ : syracuseStep 12343549 = 4628831) B4628831
theorem B645403 : Blo 570811 645403 := bstep (se 1 (by rfl) ⟨484052, by rfl⟩ : syracuseStep 645403 = 968105) B968105
theorem B579995 : Blo 570811 579995 := bstep (se 1 (by rfl) ⟨434996, by rfl⟩ : syracuseStep 579995 = 869993) B869993
theorem B13425209 : Blo 570811 13425209 := bstep (se 2 (by rfl) ⟨5034453, by rfl⟩ : syracuseStep 13425209 = 10068907) B10068907
theorem B13916771 : Blo 570811 13916771 := bstep (se 1 (by rfl) ⟨10437578, by rfl⟩ : syracuseStep 13916771 = 20875157) B20875157
theorem B1628905 : Blo 570811 1628905 := bstep (se 2 (by rfl) ⟨610839, by rfl⟩ : syracuseStep 1628905 = 1221679) B1221679
theorem B1629065 : Blo 570811 1629065 := bstep (se 2 (by rfl) ⟨610899, by rfl⟩ : syracuseStep 1629065 = 1221799) B1221799
theorem B6970493 : Blo 570811 6970493 := bstep (se 3 (by rfl) ⟨1306967, by rfl⟩ : syracuseStep 6970493 = 2613935) B2613935
theorem B5496173 : Blo 570811 5496173 := bstep (se 3 (by rfl) ⟨1030532, by rfl⟩ : syracuseStep 5496173 = 2061065) B2061065
theorem B7462297 : Blo 570811 7462297 := bstep (se 2 (by rfl) ⟨2798361, by rfl⟩ : syracuseStep 7462297 = 5596723) B5596723
theorem B3104225 : Blo 570811 3104225 := bstep (se 2 (by rfl) ⟨1164084, by rfl⟩ : syracuseStep 3104225 = 2328169) B2328169
theorem B2907737 : Blo 570811 2907737 := bstep (se 2 (by rfl) ⟨1090401, by rfl⟩ : syracuseStep 2907737 = 2180803) B2180803
theorem B4350671 : Blo 570811 4350671 := bstep (se 1 (by rfl) ⟨3263003, by rfl⟩ : syracuseStep 4350671 = 6526007) B6526007
theorem B3269747 : Blo 570811 3269747 := bstep (se 1 (by rfl) ⟨2452310, by rfl⟩ : syracuseStep 3269747 = 4904621) B4904621
theorem B2909519 : Blo 570811 2909519 := bstep (se 1 (by rfl) ⟨2182139, by rfl⟩ : syracuseStep 2909519 = 4364279) B4364279
theorem B7333253 : Blo 570811 7333253 := bstep (se 4 (by rfl) ⟨687492, by rfl⟩ : syracuseStep 7333253 = 1374985) B1374985
theorem B2450843 : Blo 570811 2450843 := bstep (se 1 (by rfl) ⟨1838132, by rfl⟩ : syracuseStep 2450843 = 3676265) B3676265
theorem B1959497 : Blo 570811 1959497 := bstep (se 2 (by rfl) ⟨734811, by rfl⟩ : syracuseStep 1959497 = 1469623) B1469623
theorem B1926827 : Blo 570811 1926827 := bstep (se 1 (by rfl) ⟨1445120, by rfl⟩ : syracuseStep 1926827 = 2890241) B2890241
theorem B3106475 : Blo 570811 3106475 := bstep (se 1 (by rfl) ⟨2329856, by rfl⟩ : syracuseStep 3106475 = 4659713) B4659713
theorem B2942647 : Blo 570811 2942647 := bstep (se 1 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 2942647 = 4413971) B4413971
theorem B88991459 : Blo 570811 88991459 := bstep (se 1 (by rfl) ⟨66743594, by rfl⟩ : syracuseStep 88991459 = 133487189) B133487189
theorem B3270455 : Blo 570811 3270455 := bstep (se 1 (by rfl) ⟨2452841, by rfl⟩ : syracuseStep 3270455 = 4905683) B4905683
theorem B1927367 : Blo 570811 1927367 := bstep (se 1 (by rfl) ⟨1445525, by rfl⟩ : syracuseStep 1927367 = 2891051) B2891051
theorem B977231 : Blo 570811 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B1469191 : Blo 570811 1469191 := bstep (se 1 (by rfl) ⟨1101893, by rfl⟩ : syracuseStep 1469191 = 2203787) B2203787
theorem B1567855 : Blo 570811 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B1044535 : Blo 570811 1044535 := bstep (se 1 (by rfl) ⟨783401, by rfl⟩ : syracuseStep 1044535 = 1566803) B1566803
theorem B4714939 : Blo 570811 4714939 := bstep (se 1 (by rfl) ⟨3536204, by rfl⟩ : syracuseStep 4714939 = 7072409) B7072409
theorem B6287867 : Blo 570811 6287867 := bstep (se 1 (by rfl) ⟨4715900, by rfl⟩ : syracuseStep 6287867 = 9431801) B9431801
theorem B18641441 : Blo 570811 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B2061641 : Blo 570811 2061641 := bstep (se 2 (by rfl) ⟨773115, by rfl⟩ : syracuseStep 2061641 = 1546231) B1546231
theorem B11007413 : Blo 570811 11007413 := bstep (se 5 (by rfl) ⟨515972, by rfl⟩ : syracuseStep 11007413 = 1031945) B1031945
theorem B1832969 : Blo 570811 1832969 := bstep (se 2 (by rfl) ⟨687363, by rfl⟩ : syracuseStep 1832969 = 1374727) B1374727
theorem B3668419 : Blo 570811 3668419 := bstep (se 1 (by rfl) ⟨2751314, by rfl⟩ : syracuseStep 3668419 = 5502629) B5502629
theorem B28572797 : Blo 570811 28572797 := bstep (se 3 (by rfl) ⟨5357399, by rfl⟩ : syracuseStep 28572797 = 10714799) B10714799
theorem B1932443 : Blo 570811 1932443 := bstep (se 1 (by rfl) ⟨1449332, by rfl⟩ : syracuseStep 1932443 = 2898665) B2898665
theorem B1572065 : Blo 570811 1572065 := bstep (se 2 (by rfl) ⟨589524, by rfl⟩ : syracuseStep 1572065 = 1179049) B1179049
theorem B10452239 : Blo 570811 10452239 := bstep (se 1 (by rfl) ⟨7839179, by rfl⟩ : syracuseStep 10452239 = 15678359) B15678359
theorem B1933577 : Blo 570811 1933577 := bstep (se 2 (by rfl) ⟨725091, by rfl⟩ : syracuseStep 1933577 = 1450183) B1450183
theorem B918791 : Blo 570811 918791 := bstep (se 1 (by rfl) ⟨689093, by rfl⟩ : syracuseStep 918791 = 1378187) B1378187
theorem B44730143 : Blo 570811 44730143 := bstep (se 1 (by rfl) ⟨33547607, by rfl⟩ : syracuseStep 44730143 = 67095215) B67095215
theorem B31459859 : Blo 570811 31459859 := bstep (se 1 (by rfl) ⟨23594894, by rfl⟩ : syracuseStep 31459859 = 47189789) B47189789
theorem B4655819 : Blo 570811 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B1837799 : Blo 570811 1837799 := bstep (se 1 (by rfl) ⟨1378349, by rfl⟩ : syracuseStep 1837799 = 2756699) B2756699
theorem B1084843 : Blo 570811 1084843 := bstep (se 1 (by rfl) ⟨813632, by rfl⟩ : syracuseStep 1084843 = 1627265) B1627265
theorem B1937087 : Blo 570811 1937087 := bstep (se 1 (by rfl) ⟨1452815, by rfl⟩ : syracuseStep 1937087 = 2905631) B2905631
theorem B1445627 : Blo 570811 1445627 := bstep (se 1 (by rfl) ⟨1084220, by rfl⟩ : syracuseStep 1445627 = 2168441) B2168441
theorem B1085375 : Blo 570811 1085375 := bstep (se 1 (by rfl) ⟨814031, by rfl⟩ : syracuseStep 1085375 = 1628063) B1628063
theorem B1380647 : Blo 570811 1380647 := bstep (se 1 (by rfl) ⟨1035485, by rfl⟩ : syracuseStep 1380647 = 2070971) B2070971
theorem B8950139 : Blo 570811 8950139 := bstep (se 1 (by rfl) ⟨6712604, by rfl⟩ : syracuseStep 8950139 = 13425209) B13425209
theorem B9277847 : Blo 570811 9277847 := bstep (se 1 (by rfl) ⟨6958385, by rfl⟩ : syracuseStep 9277847 = 13916771) B13916771
theorem B856475 : Blo 570811 856475 := bstep (se 1 (by rfl) ⟨642356, by rfl⟩ : syracuseStep 856475 = 1284713) B1284713
theorem B1937897 : Blo 570811 1937897 := bstep (se 2 (by rfl) ⟨726711, by rfl⟩ : syracuseStep 1937897 = 1453423) B1453423
theorem B1086043 : Blo 570811 1086043 := bstep (se 1 (by rfl) ⟨814532, by rfl⟩ : syracuseStep 1086043 = 1629065) B1629065
theorem B856895 : Blo 570811 856895 := bstep (se 1 (by rfl) ⟨642671, by rfl⟩ : syracuseStep 856895 = 1285343) B1285343
theorem B14914529 : Blo 570811 14914529 := bstep (se 2 (by rfl) ⟨5592948, by rfl⟩ : syracuseStep 14914529 = 11185897) B11185897
theorem B2069483 : Blo 570811 2069483 := bstep (se 1 (by rfl) ⟨1552112, by rfl⟩ : syracuseStep 2069483 = 3104225) B3104225
theorem B1938491 : Blo 570811 1938491 := bstep (se 1 (by rfl) ⟨1453868, by rfl⟩ : syracuseStep 1938491 = 2907737) B2907737
theorem B857465 : Blo 570811 857465 := bstep (se 2 (by rfl) ⟨321549, by rfl⟩ : syracuseStep 857465 = 643099) B643099
theorem B2332385 : Blo 570811 2332385 := bstep (se 2 (by rfl) ⟨874644, by rfl⟩ : syracuseStep 2332385 = 1749289) B1749289
theorem B5576435 : Blo 570811 5576435 := bstep (se 1 (by rfl) ⟨4182326, by rfl⟩ : syracuseStep 5576435 = 8364653) B8364653
theorem B858011 : Blo 570811 858011 := bstep (se 1 (by rfl) ⟨643508, by rfl⟩ : syracuseStep 858011 = 1287017) B1287017
theorem B1939679 : Blo 570811 1939679 := bstep (se 1 (by rfl) ⟨1454759, by rfl⟩ : syracuseStep 1939679 = 2909519) B2909519
theorem B4888835 : Blo 570811 4888835 := bstep (se 1 (by rfl) ⟨3666626, by rfl⟩ : syracuseStep 4888835 = 7333253) B7333253
theorem B1284551 : Blo 570811 1284551 := bstep (se 1 (by rfl) ⟨963413, by rfl⟩ : syracuseStep 1284551 = 1926827) B1926827
theorem B2070983 : Blo 570811 2070983 := bstep (se 1 (by rfl) ⟨1553237, by rfl⟩ : syracuseStep 2070983 = 3106475) B3106475
theorem B858671 : Blo 570811 858671 := bstep (se 1 (by rfl) ⟨644003, by rfl⟩ : syracuseStep 858671 = 1288007) B1288007
theorem B858719 : Blo 570811 858719 := bstep (se 1 (by rfl) ⟨644039, by rfl⟩ : syracuseStep 858719 = 1288079) B1288079
theorem B1284911 : Blo 570811 1284911 := bstep (se 1 (by rfl) ⟨963683, by rfl⟩ : syracuseStep 1284911 = 1927367) B1927367
theorem B859079 : Blo 570811 859079 := bstep (se 1 (by rfl) ⟨644309, by rfl⟩ : syracuseStep 859079 = 1288619) B1288619
theorem B859199 : Blo 570811 859199 := bstep (se 1 (by rfl) ⟨644399, by rfl⟩ : syracuseStep 859199 = 1288799) B1288799
theorem B2169929 : Blo 570811 2169929 := bstep (se 2 (by rfl) ⟨813723, by rfl⟩ : syracuseStep 2169929 = 1627447) B1627447
theorem B1285289 : Blo 570811 1285289 := bstep (se 2 (by rfl) ⟨481983, by rfl⟩ : syracuseStep 1285289 = 963967) B963967
theorem B859439 : Blo 570811 859439 := bstep (se 1 (by rfl) ⟨644579, by rfl⟩ : syracuseStep 859439 = 1289159) B1289159
theorem B11017559 : Blo 570811 11017559 := bstep (se 1 (by rfl) ⟨8263169, by rfl⟩ : syracuseStep 11017559 = 16526339) B16526339
theorem B859679 : Blo 570811 859679 := bstep (se 1 (by rfl) ⟨644759, by rfl⟩ : syracuseStep 859679 = 1289519) B1289519
theorem B859703 : Blo 570811 859703 := bstep (se 1 (by rfl) ⟨644777, by rfl⟩ : syracuseStep 859703 = 1289555) B1289555
theorem B859871 : Blo 570811 859871 := bstep (se 1 (by rfl) ⟨644903, by rfl⟩ : syracuseStep 859871 = 1289807) B1289807
theorem B860063 : Blo 570811 860063 := bstep (se 1 (by rfl) ⟨645047, by rfl⟩ : syracuseStep 860063 = 1290095) B1290095
theorem B860231 : Blo 570811 860231 := bstep (se 1 (by rfl) ⟨645173, by rfl⟩ : syracuseStep 860231 = 1290347) B1290347
theorem B860351 : Blo 570811 860351 := bstep (se 1 (by rfl) ⟨645263, by rfl⟩ : syracuseStep 860351 = 1290527) B1290527
theorem B18587981 : Blo 570811 18587981 := bstep (se 3 (by rfl) ⟨3485246, by rfl⟩ : syracuseStep 18587981 = 6970493) B6970493
theorem B16458065 : Blo 570811 16458065 := bstep (se 2 (by rfl) ⟨6171774, by rfl⟩ : syracuseStep 16458065 = 12343549) B12343549
theorem B12427627 : Blo 570811 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B860537 : Blo 570811 860537 := bstep (se 2 (by rfl) ⟨322701, by rfl⟩ : syracuseStep 860537 = 645403) B645403
theorem B2171387 : Blo 570811 2171387 := bstep (se 1 (by rfl) ⟨1628540, by rfl⟩ : syracuseStep 2171387 = 3257081) B3257081
theorem B4891225 : Blo 570811 4891225 := bstep (se 2 (by rfl) ⟨1834209, by rfl⟩ : syracuseStep 4891225 = 3668419) B3668419
theorem B860831 : Blo 570811 860831 := bstep (se 1 (by rfl) ⟨645623, by rfl⟩ : syracuseStep 860831 = 1291247) B1291247
theorem B2171873 : Blo 570811 2171873 := bstep (se 2 (by rfl) ⟨814452, by rfl⟩ : syracuseStep 2171873 = 1628905) B1628905
theorem B1221979 : Blo 570811 1221979 := bstep (se 1 (by rfl) ⟨916484, by rfl⟩ : syracuseStep 1221979 = 1832969) B1832969
theorem B19048531 : Blo 570811 19048531 := bstep (se 1 (by rfl) ⟨14286398, by rfl⟩ : syracuseStep 19048531 = 28572797) B28572797
theorem B1288295 : Blo 570811 1288295 := bstep (se 1 (by rfl) ⟨966221, by rfl⟩ : syracuseStep 1288295 = 1932443) B1932443
theorem B2173787 : Blo 570811 2173787 := bstep (se 1 (by rfl) ⟨1630340, by rfl⟩ : syracuseStep 2173787 = 3260681) B3260681
theorem B7351397 : Blo 570811 7351397 := bstep (se 4 (by rfl) ⟨689193, by rfl⟩ : syracuseStep 7351397 = 1378387) B1378387
theorem B4337063 : Blo 570811 4337063 := bstep (se 1 (by rfl) ⟨3252797, by rfl⟩ : syracuseStep 4337063 = 6505595) B6505595
theorem B1453697 : Blo 570811 1453697 := bstep (se 2 (by rfl) ⟨545136, by rfl⟩ : syracuseStep 1453697 = 1090273) B1090273
theorem B1290401 : Blo 570811 1290401 := bstep (se 2 (by rfl) ⟨483900, by rfl⟩ : syracuseStep 1290401 = 967801) B967801
theorem B2798135 : Blo 570811 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B2175731 : Blo 570811 2175731 := bstep (se 1 (by rfl) ⟨1631798, by rfl⟩ : syracuseStep 2175731 = 3263597) B3263597
theorem B3486659 : Blo 570811 3486659 := bstep (se 1 (by rfl) ⟨2614994, by rfl⟩ : syracuseStep 3486659 = 5229989) B5229989
theorem B2241503 : Blo 570811 2241503 := bstep (se 1 (by rfl) ⟨1681127, by rfl⟩ : syracuseStep 2241503 = 3362255) B3362255
theorem B963839 : Blo 570811 963839 := bstep (se 1 (by rfl) ⟨722879, by rfl⟩ : syracuseStep 963839 = 1445759) B1445759
theorem B1029611 : Blo 570811 1029611 := bstep (se 1 (by rfl) ⟨772208, by rfl⟩ : syracuseStep 1029611 = 1544417) B1544417
theorem B8828441 : Blo 570811 8828441 := bstep (se 2 (by rfl) ⟨3310665, by rfl⟩ : syracuseStep 8828441 = 6621331) B6621331
theorem B964271 : Blo 570811 964271 := bstep (se 1 (by rfl) ⟨723203, by rfl⟩ : syracuseStep 964271 = 1446407) B1446407
theorem B1030043 : Blo 570811 1030043 := bstep (se 1 (by rfl) ⟨772532, by rfl⟩ : syracuseStep 1030043 = 1545065) B1545065
theorem B2897855 : Blo 570811 2897855 := bstep (se 1 (by rfl) ⟨2173391, by rfl⟩ : syracuseStep 2897855 = 4346783) B4346783
theorem B571387 : Blo 570811 571387 := bstep (se 1 (by rfl) ⟨428540, by rfl⟩ : syracuseStep 571387 = 857081) B857081
theorem B571519 : Blo 570811 571519 := bstep (se 1 (by rfl) ⟨428639, by rfl⟩ : syracuseStep 571519 = 857279) B857279
theorem B571615 : Blo 570811 571615 := bstep (se 1 (by rfl) ⟨428711, by rfl⟩ : syracuseStep 571615 = 857423) B857423
theorem B964831 : Blo 570811 964831 := bstep (se 1 (by rfl) ⟨723623, by rfl⟩ : syracuseStep 964831 = 1447247) B1447247
theorem B571675 : Blo 570811 571675 := bstep (se 1 (by rfl) ⟨428756, by rfl⟩ : syracuseStep 571675 = 857513) B857513
theorem B964919 : Blo 570811 964919 := bstep (se 1 (by rfl) ⟨723689, by rfl⟩ : syracuseStep 964919 = 1447379) B1447379
theorem B571711 : Blo 570811 571711 := bstep (se 1 (by rfl) ⟨428783, by rfl⟩ : syracuseStep 571711 = 857567) B857567
theorem B571775 : Blo 570811 571775 := bstep (se 1 (by rfl) ⟨428831, by rfl⟩ : syracuseStep 571775 = 857663) B857663
theorem B572095 : Blo 570811 572095 := bstep (se 1 (by rfl) ⟨429071, by rfl⟩ : syracuseStep 572095 = 858143) B858143
theorem B572383 : Blo 570811 572383 := bstep (se 1 (by rfl) ⟨429287, by rfl⟩ : syracuseStep 572383 = 858575) B858575
theorem B572443 : Blo 570811 572443 := bstep (se 1 (by rfl) ⟨429332, by rfl⟩ : syracuseStep 572443 = 858665) B858665
theorem B572583 : Blo 570811 572583 := bstep (se 1 (by rfl) ⟨429437, by rfl⟩ : syracuseStep 572583 = 858875) B858875
theorem B572667 : Blo 570811 572667 := bstep (se 1 (by rfl) ⟨429500, by rfl⟩ : syracuseStep 572667 = 859001) B859001
theorem B966215 : Blo 570811 966215 := bstep (se 1 (by rfl) ⟨724661, by rfl⟩ : syracuseStep 966215 = 1449323) B1449323
theorem B573167 : Blo 570811 573167 := bstep (se 1 (by rfl) ⟨429875, by rfl⟩ : syracuseStep 573167 = 859751) B859751
theorem B966431 : Blo 570811 966431 := bstep (se 1 (by rfl) ⟨724823, by rfl⟩ : syracuseStep 966431 = 1449647) B1449647
theorem B573275 : Blo 570811 573275 := bstep (se 1 (by rfl) ⟨429956, by rfl⟩ : syracuseStep 573275 = 859913) B859913
theorem B573423 : Blo 570811 573423 := bstep (se 1 (by rfl) ⟨430067, by rfl⟩ : syracuseStep 573423 = 860135) B860135
theorem B966647 : Blo 570811 966647 := bstep (se 1 (by rfl) ⟨724985, by rfl⟩ : syracuseStep 966647 = 1449971) B1449971
theorem B573503 : Blo 570811 573503 := bstep (se 1 (by rfl) ⟨430127, by rfl⟩ : syracuseStep 573503 = 860255) B860255
theorem B1392713 : Blo 570811 1392713 := bstep (se 2 (by rfl) ⟨522267, by rfl⟩ : syracuseStep 1392713 = 1044535) B1044535
theorem B573543 : Blo 570811 573543 := bstep (se 1 (by rfl) ⟨430157, by rfl⟩ : syracuseStep 573543 = 860315) B860315
theorem B7356521 : Blo 570811 7356521 := bstep (se 2 (by rfl) ⟨2758695, by rfl⟩ : syracuseStep 7356521 = 5517391) B5517391
theorem B573599 : Blo 570811 573599 := bstep (se 1 (by rfl) ⟨430199, by rfl⟩ : syracuseStep 573599 = 860399) B860399
theorem B573851 : Blo 570811 573851 := bstep (se 1 (by rfl) ⟨430388, by rfl⟩ : syracuseStep 573851 = 860777) B860777
theorem B573855 : Blo 570811 573855 := bstep (se 1 (by rfl) ⟨430391, by rfl⟩ : syracuseStep 573855 = 860783) B860783
theorem B31375781 : Blo 570811 31375781 := bstep (se 4 (by rfl) ⟨2941479, by rfl⟩ : syracuseStep 31375781 = 5882959) B5882959
theorem B2900447 : Blo 570811 2900447 := bstep (se 1 (by rfl) ⟨2175335, by rfl⟩ : syracuseStep 2900447 = 4350671) B4350671
theorem B2179831 : Blo 570811 2179831 := bstep (se 1 (by rfl) ⟨1634873, by rfl⟩ : syracuseStep 2179831 = 3269747) B3269747
theorem B574271 : Blo 570811 574271 := bstep (se 1 (by rfl) ⟨430703, by rfl⟩ : syracuseStep 574271 = 861407) B861407
theorem B574431 : Blo 570811 574431 := bstep (se 1 (by rfl) ⟨430823, by rfl⟩ : syracuseStep 574431 = 861647) B861647
theorem B967673 : Blo 570811 967673 := bstep (se 2 (by rfl) ⟨362877, by rfl⟩ : syracuseStep 967673 = 725755) B725755
theorem B967727 : Blo 570811 967727 := bstep (se 1 (by rfl) ⟨725795, by rfl⟩ : syracuseStep 967727 = 1451591) B1451591
theorem B574555 : Blo 570811 574555 := bstep (se 1 (by rfl) ⟨430916, by rfl⟩ : syracuseStep 574555 = 861833) B861833
theorem B574591 : Blo 570811 574591 := bstep (se 1 (by rfl) ⟨430943, by rfl⟩ : syracuseStep 574591 = 861887) B861887
theorem B59327639 : Blo 570811 59327639 := bstep (se 1 (by rfl) ⟨44495729, by rfl⟩ : syracuseStep 59327639 = 88991459) B88991459
theorem B2180303 : Blo 570811 2180303 := bstep (se 1 (by rfl) ⟨1635227, by rfl⟩ : syracuseStep 2180303 = 3270455) B3270455
theorem B574695 : Blo 570811 574695 := bstep (se 1 (by rfl) ⟨431021, by rfl⟩ : syracuseStep 574695 = 862043) B862043
theorem B27805517 : Blo 570811 27805517 := bstep (se 3 (by rfl) ⟨5213534, by rfl⟩ : syracuseStep 27805517 = 10427069) B10427069
theorem B968935 : Blo 570811 968935 := bstep (se 1 (by rfl) ⟨726701, by rfl⟩ : syracuseStep 968935 = 1453403) B1453403
theorem B969455 : Blo 570811 969455 := bstep (se 1 (by rfl) ⟨727091, by rfl⟩ : syracuseStep 969455 = 1454183) B1454183
theorem B969833 : Blo 570811 969833 := bstep (se 2 (by rfl) ⟨363687, by rfl⟩ : syracuseStep 969833 = 727375) B727375
theorem B9949729 : Blo 570811 9949729 := bstep (se 2 (by rfl) ⟨3731148, by rfl⟩ : syracuseStep 9949729 = 7462297) B7462297
theorem B6968159 : Blo 570811 6968159 := bstep (se 1 (by rfl) ⟨5226119, by rfl⟩ : syracuseStep 6968159 = 10452239) B10452239
theorem B1954759 : Blo 570811 1954759 := bstep (se 1 (by rfl) ⟨1466069, by rfl⟩ : syracuseStep 1954759 = 2932139) B2932139
theorem B15258631 : Blo 570811 15258631 := bstep (se 1 (by rfl) ⟨11443973, by rfl⟩ : syracuseStep 15258631 = 22887947) B22887947
theorem B3658783 : Blo 570811 3658783 := bstep (se 1 (by rfl) ⟨2744087, by rfl⟩ : syracuseStep 3658783 = 5488175) B5488175
theorem B2937971 : Blo 570811 2937971 := bstep (se 1 (by rfl) ⟨2203478, by rfl⟩ : syracuseStep 2937971 = 4406957) B4406957
theorem B644575 : Blo 570811 644575 := bstep (se 1 (by rfl) ⟨483431, by rfl⟩ : syracuseStep 644575 = 966863) B966863
theorem B2446843 : Blo 570811 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B35346293 : Blo 570811 35346293 := bstep (se 5 (by rfl) ⟨1656857, by rfl⟩ : syracuseStep 35346293 = 3313715) B3313715
theorem B6543503 : Blo 570811 6543503 := bstep (se 1 (by rfl) ⟨4907627, by rfl⟩ : syracuseStep 6543503 = 9815255) B9815255
theorem B2316883 : Blo 570811 2316883 := bstep (se 1 (by rfl) ⟨1737662, by rfl⟩ : syracuseStep 2316883 = 3475325) B3475325
theorem B3300043 : Blo 570811 3300043 := bstep (se 1 (by rfl) ⟨2475032, by rfl⟩ : syracuseStep 3300043 = 4950065) B4950065
theorem B1629247 : Blo 570811 1629247 := bstep (se 1 (by rfl) ⟨1221935, by rfl⟩ : syracuseStep 1629247 = 2443871) B2443871
theorem B613531 : Blo 570811 613531 := bstep (se 1 (by rfl) ⟨460148, by rfl⟩ : syracuseStep 613531 = 920297) B920297
theorem B4906331 : Blo 570811 4906331 := bstep (se 1 (by rfl) ⟨3679748, by rfl⟩ : syracuseStep 4906331 = 7359497) B7359497
theorem B2907575 : Blo 570811 2907575 := bstep (se 1 (by rfl) ⟨2180681, by rfl⟩ : syracuseStep 2907575 = 4361363) B4361363
theorem B2448893 : Blo 570811 2448893 := bstep (se 3 (by rfl) ⟨459167, by rfl⟩ : syracuseStep 2448893 = 918335) B918335
theorem B2449835 : Blo 570811 2449835 := bstep (se 1 (by rfl) ⟨1837376, by rfl⟩ : syracuseStep 2449835 = 3674753) B3674753
theorem B1958921 : Blo 570811 1958921 := bstep (se 2 (by rfl) ⟨734595, by rfl⟩ : syracuseStep 1958921 = 1469191) B1469191
theorem B13264087 : Blo 570811 13264087 := bstep (se 1 (by rfl) ⟨9948065, by rfl⟩ : syracuseStep 13264087 = 19896131) B19896131
theorem B1926557 : Blo 570811 1926557 := bstep (se 3 (by rfl) ⟨361229, by rfl⟩ : syracuseStep 1926557 = 722459) B722459
theorem B2090473 : Blo 570811 2090473 := bstep (se 2 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 2090473 = 1567855) B1567855
theorem B1926719 : Blo 570811 1926719 := bstep (se 1 (by rfl) ⟨1445039, by rfl⟩ : syracuseStep 1926719 = 2890079) B2890079
theorem B6186613 : Blo 570811 6186613 := bstep (se 5 (by rfl) ⟨289997, by rfl⟩ : syracuseStep 6186613 = 579995) B579995
theorem B3664115 : Blo 570811 3664115 := bstep (se 1 (by rfl) ⟨2748086, by rfl⟩ : syracuseStep 3664115 = 5496173) B5496173
theorem B6187691 : Blo 570811 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B1927961 : Blo 570811 1927961 := bstep (se 2 (by rfl) ⟨722985, by rfl⟩ : syracuseStep 1927961 = 1445971) B1445971
theorem B6286585 : Blo 570811 6286585 := bstep (se 2 (by rfl) ⟨2357469, by rfl⟩ : syracuseStep 6286585 = 4714939) B4714939
theorem B10415465 : Blo 570811 10415465 := bstep (se 2 (by rfl) ⟨3905799, by rfl⟩ : syracuseStep 10415465 = 7811599) B7811599
theorem B1633895 : Blo 570811 1633895 := bstep (se 1 (by rfl) ⟨1225421, by rfl⟩ : syracuseStep 1633895 = 2450843) B2450843
theorem B1306331 : Blo 570811 1306331 := bstep (se 1 (by rfl) ⟨979748, by rfl⟩ : syracuseStep 1306331 = 1959497) B1959497
theorem B4878103 : Blo 570811 4878103 := bstep (se 1 (by rfl) ⟨3658577, by rfl⟩ : syracuseStep 4878103 = 7317155) B7317155
theorem B651487 : Blo 570811 651487 := bstep (se 1 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 651487 = 977231) B977231
theorem B1930175 : Blo 570811 1930175 := bstep (se 1 (by rfl) ⟨1447631, by rfl⟩ : syracuseStep 1930175 = 2895263) B2895263
theorem B1635353 : Blo 570811 1635353 := bstep (se 2 (by rfl) ⟨613257, by rfl⟩ : syracuseStep 1635353 = 1226515) B1226515
theorem B980281 : Blo 570811 980281 := bstep (se 2 (by rfl) ⟨367605, by rfl⟩ : syracuseStep 980281 = 735211) B735211
theorem B2061931 : Blo 570811 2061931 := bstep (se 1 (by rfl) ⟨1546448, by rfl⟩ : syracuseStep 2061931 = 3092897) B3092897
theorem B4191911 : Blo 570811 4191911 := bstep (se 1 (by rfl) ⟨3143933, by rfl⟩ : syracuseStep 4191911 = 6287867) B6287867
theorem B1930985 : Blo 570811 1930985 := bstep (se 2 (by rfl) ⟨724119, by rfl⟩ : syracuseStep 1930985 = 1448239) B1448239
theorem B1931039 : Blo 570811 1931039 := bstep (se 1 (by rfl) ⟨1448279, by rfl⟩ : syracuseStep 1931039 = 2896559) B2896559
theorem B2062219 : Blo 570811 2062219 := bstep (se 1 (by rfl) ⟨1546664, by rfl⟩ : syracuseStep 2062219 = 3093329) B3093329
theorem B1374427 : Blo 570811 1374427 := bstep (se 1 (by rfl) ⟨1030820, by rfl⟩ : syracuseStep 1374427 = 2061641) B2061641
theorem B7338275 : Blo 570811 7338275 := bstep (se 1 (by rfl) ⟨5503706, by rfl⟩ : syracuseStep 7338275 = 11007413) B11007413
theorem B15694117 : Blo 570811 15694117 := bstep (se 4 (by rfl) ⟨1471323, by rfl⟩ : syracuseStep 15694117 = 2942647) B2942647
theorem B686647 : Blo 570811 686647 := bstep (se 1 (by rfl) ⟨514985, by rfl⟩ : syracuseStep 686647 = 1029971) B1029971
theorem B1932767 : Blo 570811 1932767 := bstep (se 1 (by rfl) ⟨1449575, by rfl⟩ : syracuseStep 1932767 = 2899151) B2899151
theorem B1048043 : Blo 570811 1048043 := bstep (se 1 (by rfl) ⟨786032, by rfl⟩ : syracuseStep 1048043 = 1572065) B1572065
theorem B1932983 : Blo 570811 1932983 := bstep (se 1 (by rfl) ⟨1449737, by rfl⟩ : syracuseStep 1932983 = 2899475) B2899475
theorem B1933631 : Blo 570811 1933631 := bstep (se 1 (by rfl) ⟨1450223, by rfl⟩ : syracuseStep 1933631 = 2900447) B2900447
theorem B39551759 : Blo 570811 39551759 := bstep (se 1 (by rfl) ⟨29663819, by rfl⟩ : syracuseStep 39551759 = 59327639) B59327639
theorem B6521633 : Blo 570811 6521633 := bstep (se 2 (by rfl) ⟨2445612, by rfl⟩ : syracuseStep 6521633 = 4891225) B4891225
theorem B29820095 : Blo 570811 29820095 := bstep (se 1 (by rfl) ⟨22365071, by rfl⟩ : syracuseStep 29820095 = 44730143) B44730143
theorem B20973239 : Blo 570811 20973239 := bstep (se 1 (by rfl) ⟨15729929, by rfl⟩ : syracuseStep 20973239 = 31459859) B31459859
theorem B723583 : Blo 570811 723583 := bstep (se 1 (by rfl) ⟨542687, by rfl⟩ : syracuseStep 723583 = 1085375) B1085375
theorem B25398041 : Blo 570811 25398041 := bstep (se 2 (by rfl) ⟨9524265, by rfl⟩ : syracuseStep 25398041 = 19048531) B19048531
theorem B920431 : Blo 570811 920431 := bstep (se 1 (by rfl) ⟨690323, by rfl⟩ : syracuseStep 920431 = 1380647) B1380647
theorem B5966759 : Blo 570811 5966759 := bstep (se 1 (by rfl) ⟨4475069, by rfl⟩ : syracuseStep 5966759 = 8950139) B8950139
theorem B23564195 : Blo 570811 23564195 := bstep (se 1 (by rfl) ⟨17673146, by rfl⟩ : syracuseStep 23564195 = 35346293) B35346293
theorem B4362335 : Blo 570811 4362335 := bstep (se 1 (by rfl) ⟨3271751, by rfl⟩ : syracuseStep 4362335 = 6543503) B6543503
theorem B856367 : Blo 570811 856367 := bstep (se 1 (by rfl) ⟨642275, by rfl⟩ : syracuseStep 856367 = 1284551) B1284551
theorem B1380655 : Blo 570811 1380655 := bstep (se 1 (by rfl) ⟨1035491, by rfl⟩ : syracuseStep 1380655 = 2070983) B2070983
theorem B856607 : Blo 570811 856607 := bstep (se 1 (by rfl) ⟨642455, by rfl⟩ : syracuseStep 856607 = 1284911) B1284911
theorem B1446457 : Blo 570811 1446457 := bstep (se 2 (by rfl) ⟨542421, by rfl⟩ : syracuseStep 1446457 = 1084843) B1084843
theorem B1446619 : Blo 570811 1446619 := bstep (se 1 (by rfl) ⟨1084964, by rfl⟩ : syracuseStep 1446619 = 2169929) B2169929
theorem B856859 : Blo 570811 856859 := bstep (se 1 (by rfl) ⟨642644, by rfl⟩ : syracuseStep 856859 = 1285289) B1285289
theorem B7345039 : Blo 570811 7345039 := bstep (se 1 (by rfl) ⟨5508779, by rfl⟩ : syracuseStep 7345039 = 11017559) B11017559
theorem B1938383 : Blo 570811 1938383 := bstep (se 1 (by rfl) ⟨1453787, by rfl⟩ : syracuseStep 1938383 = 2907575) B2907575
theorem B12391987 : Blo 570811 12391987 := bstep (se 1 (by rfl) ⟨9293990, by rfl⟩ : syracuseStep 12391987 = 18587981) B18587981
theorem B1447591 : Blo 570811 1447591 := bstep (se 1 (by rfl) ⟨1085693, by rfl⟩ : syracuseStep 1447591 = 2171387) B2171387
theorem B1447915 : Blo 570811 1447915 := bstep (se 1 (by rfl) ⟨1085936, by rfl⟩ : syracuseStep 1447915 = 2171873) B2171873
theorem B1448057 : Blo 570811 1448057 := bstep (se 2 (by rfl) ⟨543021, by rfl⟩ : syracuseStep 1448057 = 1086043) B1086043
theorem B1284371 : Blo 570811 1284371 := bstep (se 1 (by rfl) ⟨963278, by rfl⟩ : syracuseStep 1284371 = 1926557) B1926557
theorem B1284479 : Blo 570811 1284479 := bstep (se 1 (by rfl) ⟨963359, by rfl⟩ : syracuseStep 1284479 = 1926719) B1926719
theorem B858863 : Blo 570811 858863 := bstep (se 1 (by rfl) ⟨644147, by rfl⟩ : syracuseStep 858863 = 1288295) B1288295
theorem B1285307 : Blo 570811 1285307 := bstep (se 1 (by rfl) ⟨963980, by rfl⟩ : syracuseStep 1285307 = 1927961) B1927961
theorem B1449191 : Blo 570811 1449191 := bstep (se 1 (by rfl) ⟨1086893, by rfl⟩ : syracuseStep 1449191 = 2173787) B2173787
theorem B859433 : Blo 570811 859433 := bstep (se 2 (by rfl) ⟨322287, by rfl⟩ : syracuseStep 859433 = 644575) B644575
theorem B2891375 : Blo 570811 2891375 := bstep (se 1 (by rfl) ⟨2168531, by rfl⟩ : syracuseStep 2891375 = 4337063) B4337063
theorem B1089263 : Blo 570811 1089263 := bstep (se 1 (by rfl) ⟨816947, by rfl⟩ : syracuseStep 1089263 = 1633895) B1633895
theorem B860267 : Blo 570811 860267 := bstep (se 1 (by rfl) ⟨645200, by rfl⟩ : syracuseStep 860267 = 1290401) B1290401
theorem B1286441 : Blo 570811 1286441 := bstep (se 2 (by rfl) ⟨482415, by rfl⟩ : syracuseStep 1286441 = 964831) B964831
theorem B1450487 : Blo 570811 1450487 := bstep (se 1 (by rfl) ⟨1087865, by rfl⟩ : syracuseStep 1450487 = 2175731) B2175731
theorem B1286783 : Blo 570811 1286783 := bstep (se 1 (by rfl) ⟨965087, by rfl⟩ : syracuseStep 1286783 = 1930175) B1930175
theorem B1090235 : Blo 570811 1090235 := bstep (se 1 (by rfl) ⟨817676, by rfl⟩ : syracuseStep 1090235 = 1635353) B1635353
theorem B3089177 : Blo 570811 3089177 := bstep (se 2 (by rfl) ⟨1158441, by rfl⟩ : syracuseStep 3089177 = 2316883) B2316883
theorem B4400057 : Blo 570811 4400057 := bstep (se 2 (by rfl) ⟨1650021, by rfl⟩ : syracuseStep 4400057 = 3300043) B3300043
theorem B2794607 : Blo 570811 2794607 := bstep (se 1 (by rfl) ⟨2095955, by rfl⟩ : syracuseStep 2794607 = 4191911) B4191911
theorem B1287323 : Blo 570811 1287323 := bstep (se 1 (by rfl) ⟨965492, by rfl⟩ : syracuseStep 1287323 = 1930985) B1930985
theorem B1287359 : Blo 570811 1287359 := bstep (se 1 (by rfl) ⟨965519, by rfl⟩ : syracuseStep 1287359 = 1931039) B1931039
theorem B2794781 : Blo 570811 2794781 := bstep (se 3 (by rfl) ⟨524021, by rfl⟩ : syracuseStep 2794781 = 1048043) B1048043
theorem B6530381 : Blo 570811 6530381 := bstep (se 3 (by rfl) ⟨1224446, by rfl⟩ : syracuseStep 6530381 = 2448893) B2448893
theorem B2172329 : Blo 570811 2172329 := bstep (se 2 (by rfl) ⟨814623, by rfl⟩ : syracuseStep 2172329 = 1629247) B1629247
theorem B4892183 : Blo 570811 4892183 := bstep (se 1 (by rfl) ⟨3669137, by rfl⟩ : syracuseStep 4892183 = 7338275) B7338275
theorem B1288511 : Blo 570811 1288511 := bstep (se 1 (by rfl) ⟨966383, by rfl⟩ : syracuseStep 1288511 = 1932767) B1932767
theorem B1288655 : Blo 570811 1288655 := bstep (se 1 (by rfl) ⟨966491, by rfl⟩ : syracuseStep 1288655 = 1932983) B1932983
theorem B928475 : Blo 570811 928475 := bstep (se 1 (by rfl) ⟨696356, by rfl⟩ : syracuseStep 928475 = 1392713) B1392713
theorem B1289051 : Blo 570811 1289051 := bstep (se 1 (by rfl) ⟨966788, by rfl⟩ : syracuseStep 1289051 = 1933577) B1933577
theorem B20917187 : Blo 570811 20917187 := bstep (se 1 (by rfl) ⟨15687890, by rfl⟩ : syracuseStep 20917187 = 31375781) B31375781
theorem B1453535 : Blo 570811 1453535 := bstep (se 1 (by rfl) ⟨1090151, by rfl⟩ : syracuseStep 1453535 = 2180303) B2180303
theorem B83701957 : Blo 570811 83701957 := bstep (se 4 (by rfl) ⟨7847058, by rfl⟩ : syracuseStep 83701957 = 15694117) B15694117
theorem B1225199 : Blo 570811 1225199 := bstep (se 1 (by rfl) ⟨918899, by rfl⟩ : syracuseStep 1225199 = 1837799) B1837799
theorem B1291391 : Blo 570811 1291391 := bstep (se 1 (by rfl) ⟨968543, by rfl⟩ : syracuseStep 1291391 = 1937087) B1937087
theorem B963751 : Blo 570811 963751 := bstep (se 1 (by rfl) ⟨722813, by rfl⟩ : syracuseStep 963751 = 1445627) B1445627
theorem B5518621 : Blo 570811 5518621 := bstep (se 3 (by rfl) ⟨1034741, by rfl⟩ : syracuseStep 5518621 = 2069483) B2069483
theorem B570983 : Blo 570811 570983 := bstep (se 1 (by rfl) ⟨428237, by rfl⟩ : syracuseStep 570983 = 856475) B856475
theorem B1291913 : Blo 570811 1291913 := bstep (se 2 (by rfl) ⟨484467, by rfl⟩ : syracuseStep 1291913 = 968935) B968935
theorem B1291931 : Blo 570811 1291931 := bstep (se 1 (by rfl) ⟨968948, by rfl⟩ : syracuseStep 1291931 = 1937897) B1937897
theorem B571263 : Blo 570811 571263 := bstep (se 1 (by rfl) ⟨428447, by rfl⟩ : syracuseStep 571263 = 856895) B856895
theorem B9943019 : Blo 570811 9943019 := bstep (se 1 (by rfl) ⟨7457264, by rfl⟩ : syracuseStep 9943019 = 14914529) B14914529
theorem B1292327 : Blo 570811 1292327 := bstep (se 1 (by rfl) ⟨969245, by rfl⟩ : syracuseStep 1292327 = 1938491) B1938491
theorem B571643 : Blo 570811 571643 := bstep (se 1 (by rfl) ⟨428732, by rfl⟩ : syracuseStep 571643 = 857465) B857465
theorem B1554923 : Blo 570811 1554923 := bstep (se 1 (by rfl) ⟨1166192, by rfl⟩ : syracuseStep 1554923 = 2332385) B2332385
theorem B3717623 : Blo 570811 3717623 := bstep (se 1 (by rfl) ⟨2788217, by rfl⟩ : syracuseStep 3717623 = 5576435) B5576435
theorem B572007 : Blo 570811 572007 := bstep (se 1 (by rfl) ⟨429005, by rfl⟩ : syracuseStep 572007 = 858011) B858011
theorem B1293119 : Blo 570811 1293119 := bstep (se 1 (by rfl) ⟨969839, by rfl⟩ : syracuseStep 1293119 = 1939679) B1939679
theorem B3259223 : Blo 570811 3259223 := bstep (se 1 (by rfl) ⟨2444417, by rfl⟩ : syracuseStep 3259223 = 4888835) B4888835
theorem B572447 : Blo 570811 572447 := bstep (se 1 (by rfl) ⟨429335, by rfl⟩ : syracuseStep 572447 = 858671) B858671
theorem B572479 : Blo 570811 572479 := bstep (se 1 (by rfl) ⟨429359, by rfl⟩ : syracuseStep 572479 = 858719) B858719
theorem B572719 : Blo 570811 572719 := bstep (se 1 (by rfl) ⟨429539, by rfl⟩ : syracuseStep 572719 = 859079) B859079
theorem B572799 : Blo 570811 572799 := bstep (se 1 (by rfl) ⟨429599, by rfl⟩ : syracuseStep 572799 = 859199) B859199
theorem B572959 : Blo 570811 572959 := bstep (se 1 (by rfl) ⟨429719, by rfl⟩ : syracuseStep 572959 = 859439) B859439
theorem B573119 : Blo 570811 573119 := bstep (se 1 (by rfl) ⟨429839, by rfl⟩ : syracuseStep 573119 = 859679) B859679
theorem B6504137 : Blo 570811 6504137 := bstep (se 2 (by rfl) ⟨2439051, by rfl⟩ : syracuseStep 6504137 = 4878103) B4878103
theorem B573135 : Blo 570811 573135 := bstep (se 1 (by rfl) ⟨429851, by rfl⟩ : syracuseStep 573135 = 859703) B859703
theorem B573247 : Blo 570811 573247 := bstep (se 1 (by rfl) ⟨429935, by rfl⟩ : syracuseStep 573247 = 859871) B859871
theorem B573375 : Blo 570811 573375 := bstep (se 1 (by rfl) ⟨430031, by rfl⟩ : syracuseStep 573375 = 860063) B860063
theorem B573487 : Blo 570811 573487 := bstep (se 1 (by rfl) ⟨430115, by rfl⟩ : syracuseStep 573487 = 860231) B860231
theorem B573567 : Blo 570811 573567 := bstep (se 1 (by rfl) ⟨430175, by rfl⟩ : syracuseStep 573567 = 860351) B860351
theorem B573691 : Blo 570811 573691 := bstep (se 1 (by rfl) ⟨430268, by rfl⟩ : syracuseStep 573691 = 860537) B860537
theorem B868649 : Blo 570811 868649 := bstep (se 2 (by rfl) ⟨325743, by rfl⟩ : syracuseStep 868649 = 651487) B651487
theorem B573887 : Blo 570811 573887 := bstep (se 1 (by rfl) ⟨430415, by rfl⟩ : syracuseStep 573887 = 860831) B860831
theorem B2606345 : Blo 570811 2606345 := bstep (se 2 (by rfl) ⟨977379, by rfl⟩ : syracuseStep 2606345 = 1954759) B1954759
theorem B2442743 : Blo 570811 2442743 := bstep (se 1 (by rfl) ⟨1832057, by rfl⟩ : syracuseStep 2442743 = 3664115) B3664115
theorem B5228165 : Blo 570811 5228165 := bstep (se 4 (by rfl) ⟨490140, by rfl⟩ : syracuseStep 5228165 = 980281) B980281
theorem B3262457 : Blo 570811 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B4900931 : Blo 570811 4900931 := bstep (se 1 (by rfl) ⟨3675698, by rfl⟩ : syracuseStep 4900931 = 7351397) B7351397
theorem B969131 : Blo 570811 969131 := bstep (se 1 (by rfl) ⟨726848, by rfl⟩ : syracuseStep 969131 = 1453697) B1453697
theorem B870887 : Blo 570811 870887 := bstep (se 1 (by rfl) ⟨653165, by rfl⟩ : syracuseStep 870887 = 1306331) B1306331
theorem B1494335 : Blo 570811 1494335 := bstep (se 1 (by rfl) ⟨1120751, by rfl⟩ : syracuseStep 1494335 = 2241503) B2241503
theorem B642559 : Blo 570811 642559 := bstep (se 1 (by rfl) ⟨481919, by rfl⟩ : syracuseStep 642559 = 963839) B963839
theorem B5885627 : Blo 570811 5885627 := bstep (se 1 (by rfl) ⟨4414220, by rfl⟩ : syracuseStep 5885627 = 8828441) B8828441
theorem B642847 : Blo 570811 642847 := bstep (se 1 (by rfl) ⟨482135, by rfl⟩ : syracuseStep 642847 = 964271) B964271
theorem B643279 : Blo 570811 643279 := bstep (se 1 (by rfl) ⟨482459, by rfl⟩ : syracuseStep 643279 = 964919) B964919
theorem B644143 : Blo 570811 644143 := bstep (se 1 (by rfl) ⟨483107, by rfl⟩ : syracuseStep 644143 = 966215) B966215
theorem B644287 : Blo 570811 644287 := bstep (se 1 (by rfl) ⟨483215, by rfl⟩ : syracuseStep 644287 = 966431) B966431
theorem B644431 : Blo 570811 644431 := bstep (se 1 (by rfl) ⟨483323, by rfl⟩ : syracuseStep 644431 = 966647) B966647
theorem B4904347 : Blo 570811 4904347 := bstep (se 1 (by rfl) ⟨3678260, by rfl⟩ : syracuseStep 4904347 = 7356521) B7356521
theorem B16570169 : Blo 570811 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B645115 : Blo 570811 645115 := bstep (se 1 (by rfl) ⟨483836, by rfl⟩ : syracuseStep 645115 = 967673) B967673
theorem B645151 : Blo 570811 645151 := bstep (se 1 (by rfl) ⟨483863, by rfl⟩ : syracuseStep 645151 = 967727) B967727
theorem B612527 : Blo 570811 612527 := bstep (se 1 (by rfl) ⟨459395, by rfl⟩ : syracuseStep 612527 = 918791) B918791
theorem B2906441 : Blo 570811 2906441 := bstep (se 2 (by rfl) ⟨1089915, by rfl⟩ : syracuseStep 2906441 = 2179831) B2179831
theorem B7330277 : Blo 570811 7330277 := bstep (se 4 (by rfl) ⟨687213, by rfl⟩ : syracuseStep 7330277 = 1374427) B1374427
theorem B18537011 : Blo 570811 18537011 := bstep (se 1 (by rfl) ⟨13902758, by rfl⟩ : syracuseStep 18537011 = 27805517) B27805517
theorem B17685449 : Blo 570811 17685449 := bstep (se 2 (by rfl) ⟨6632043, by rfl⟩ : syracuseStep 17685449 = 13264087) B13264087
theorem B1629305 : Blo 570811 1629305 := bstep (se 2 (by rfl) ⟨610989, by rfl⟩ : syracuseStep 1629305 = 1221979) B1221979
theorem B646303 : Blo 570811 646303 := bstep (se 1 (by rfl) ⟨484727, by rfl⟩ : syracuseStep 646303 = 969455) B969455
theorem B646555 : Blo 570811 646555 := bstep (se 1 (by rfl) ⟨484916, by rfl⟩ : syracuseStep 646555 = 969833) B969833
theorem B8248817 : Blo 570811 8248817 := bstep (se 2 (by rfl) ⟨3093306, by rfl⟩ : syracuseStep 8248817 = 6186613) B6186613
theorem B9297757 : Blo 570811 9297757 := bstep (se 3 (by rfl) ⟨1743329, by rfl⟩ : syracuseStep 9297757 = 3486659) B3486659
theorem B6185231 : Blo 570811 6185231 := bstep (se 1 (by rfl) ⟨4638923, by rfl⟩ : syracuseStep 6185231 = 9277847) B9277847
theorem B3662117 : Blo 570811 3662117 := bstep (se 4 (by rfl) ⟨343323, by rfl⟩ : syracuseStep 3662117 = 686647) B686647
theorem B4645439 : Blo 570811 4645439 := bstep (se 1 (by rfl) ⟨3484079, by rfl⟩ : syracuseStep 4645439 = 6968159) B6968159
theorem B1958647 : Blo 570811 1958647 := bstep (se 1 (by rfl) ⟨1468985, by rfl⟩ : syracuseStep 1958647 = 2937971) B2937971
theorem B8382113 : Blo 570811 8382113 := bstep (se 2 (by rfl) ⟨3143292, by rfl⟩ : syracuseStep 8382113 = 6286585) B6286585
theorem B3270887 : Blo 570811 3270887 := bstep (se 1 (by rfl) ⟨2453165, by rfl⟩ : syracuseStep 3270887 = 4906331) B4906331
theorem B2746781 : Blo 570811 2746781 := bstep (se 3 (by rfl) ⟨515021, by rfl⟩ : syracuseStep 2746781 = 1030043) B1030043
theorem B10972043 : Blo 570811 10972043 := bstep (se 1 (by rfl) ⟨8229032, by rfl⟩ : syracuseStep 10972043 = 16458065) B16458065
theorem B1633223 : Blo 570811 1633223 := bstep (se 1 (by rfl) ⟨1224917, by rfl⟩ : syracuseStep 1633223 = 2449835) B2449835
theorem B1305947 : Blo 570811 1305947 := bstep (se 1 (by rfl) ⟨979460, by rfl⟩ : syracuseStep 1305947 = 1958921) B1958921
theorem B13266305 : Blo 570811 13266305 := bstep (se 2 (by rfl) ⟨4974864, by rfl⟩ : syracuseStep 13266305 = 9949729) B9949729
theorem B20344841 : Blo 570811 20344841 := bstep (se 2 (by rfl) ⟨7629315, by rfl⟩ : syracuseStep 20344841 = 15258631) B15258631
theorem B4878377 : Blo 570811 4878377 := bstep (se 2 (by rfl) ⟨1829391, by rfl⟩ : syracuseStep 4878377 = 3658783) B3658783
theorem B4125127 : Blo 570811 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B12415517 : Blo 570811 12415517 := bstep (se 3 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 12415517 = 4655819) B4655819
theorem B2749241 : Blo 570811 2749241 := bstep (se 2 (by rfl) ⟨1030965, by rfl⟩ : syracuseStep 2749241 = 2061931) B2061931
theorem B6943643 : Blo 570811 6943643 := bstep (se 1 (by rfl) ⟨5207732, by rfl⟩ : syracuseStep 6943643 = 10415465) B10415465
theorem B2749625 : Blo 570811 2749625 := bstep (se 2 (by rfl) ⟨1031109, by rfl⟩ : syracuseStep 2749625 = 2062219) B2062219
theorem B1865423 : Blo 570811 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B686407 : Blo 570811 686407 := bstep (se 1 (by rfl) ⟨514805, by rfl⟩ : syracuseStep 686407 = 1029611) B1029611
theorem B1931903 : Blo 570811 1931903 := bstep (se 1 (by rfl) ⟨1448927, by rfl⟩ : syracuseStep 1931903 = 2897855) B2897855
theorem B818041 : Blo 570811 818041 := bstep (se 2 (by rfl) ⟨306765, by rfl⟩ : syracuseStep 818041 = 613531) B613531
theorem B44596757 : Blo 570811 44596757 := bstep (se 6 (by rfl) ⟨1045236, by rfl⟩ : syracuseStep 44596757 = 2090473) B2090473
theorem B1737563 : Blo 570811 1737563 := bstep (se 1 (by rfl) ⟨1303172, by rfl⟩ : syracuseStep 1737563 = 2606345) B2606345
theorem B11046779 : Blo 570811 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B856247 : Blo 570811 856247 := bstep (se 1 (by rfl) ⟨642185, by rfl⟩ : syracuseStep 856247 = 1284371) B1284371
theorem B1937627 : Blo 570811 1937627 := bstep (se 1 (by rfl) ⟨1453220, by rfl⟩ : syracuseStep 1937627 = 2906441) B2906441
theorem B856319 : Blo 570811 856319 := bstep (se 1 (by rfl) ⟨642239, by rfl⟩ : syracuseStep 856319 = 1284479) B1284479
theorem B4886851 : Blo 570811 4886851 := bstep (se 1 (by rfl) ⟨3665138, by rfl⟩ : syracuseStep 4886851 = 7330277) B7330277
theorem B12358007 : Blo 570811 12358007 := bstep (se 1 (by rfl) ⟨9268505, by rfl⟩ : syracuseStep 12358007 = 18537011) B18537011
theorem B856745 : Blo 570811 856745 := bstep (se 2 (by rfl) ⟨321279, by rfl⟩ : syracuseStep 856745 = 642559) B642559
theorem B1086203 : Blo 570811 1086203 := bstep (se 1 (by rfl) ⟨814652, by rfl⟩ : syracuseStep 1086203 = 1629305) B1629305
theorem B856871 : Blo 570811 856871 := bstep (se 1 (by rfl) ⟨642653, by rfl⟩ : syracuseStep 856871 = 1285307) B1285307
theorem B857129 : Blo 570811 857129 := bstep (se 2 (by rfl) ⟨321423, by rfl⟩ : syracuseStep 857129 = 642847) B642847
theorem B726175 : Blo 570811 726175 := bstep (se 1 (by rfl) ⟨544631, by rfl⟩ : syracuseStep 726175 = 1089263) B1089263
theorem B857627 : Blo 570811 857627 := bstep (se 1 (by rfl) ⟨643220, by rfl⟩ : syracuseStep 857627 = 1286441) B1286441
theorem B857705 : Blo 570811 857705 := bstep (se 2 (by rfl) ⟨321639, by rfl⟩ : syracuseStep 857705 = 643279) B643279
theorem B857855 : Blo 570811 857855 := bstep (se 1 (by rfl) ⟨643391, by rfl⟩ : syracuseStep 857855 = 1286783) B1286783
theorem B726823 : Blo 570811 726823 := bstep (se 1 (by rfl) ⟨545117, by rfl⟩ : syracuseStep 726823 = 1090235) B1090235
theorem B858215 : Blo 570811 858215 := bstep (se 1 (by rfl) ⟨643661, by rfl⟩ : syracuseStep 858215 = 1287323) B1287323
theorem B858239 : Blo 570811 858239 := bstep (se 1 (by rfl) ⟨643679, by rfl⟩ : syracuseStep 858239 = 1287359) B1287359
theorem B1448219 : Blo 570811 1448219 := bstep (se 1 (by rfl) ⟨1086164, by rfl⟩ : syracuseStep 1448219 = 2172329) B2172329
theorem B858857 : Blo 570811 858857 := bstep (se 2 (by rfl) ⟨322071, by rfl⟩ : syracuseStep 858857 = 644143) B644143
theorem B859007 : Blo 570811 859007 := bstep (se 1 (by rfl) ⟨644255, by rfl⟩ : syracuseStep 859007 = 1288511) B1288511
theorem B1285001 : Blo 570811 1285001 := bstep (se 2 (by rfl) ⟨481875, by rfl⟩ : syracuseStep 1285001 = 963751) B963751
theorem B859049 : Blo 570811 859049 := bstep (se 2 (by rfl) ⟨322143, by rfl⟩ : syracuseStep 859049 = 644287) B644287
theorem B859103 : Blo 570811 859103 := bstep (se 1 (by rfl) ⟨644327, by rfl⟩ : syracuseStep 859103 = 1288655) B1288655
theorem B859241 : Blo 570811 859241 := bstep (se 2 (by rfl) ⟨322215, by rfl⟩ : syracuseStep 859241 = 644431) B644431
theorem B859367 : Blo 570811 859367 := bstep (se 1 (by rfl) ⟨644525, by rfl⟩ : syracuseStep 859367 = 1289051) B1289051
theorem B7314695 : Blo 570811 7314695 := bstep (se 1 (by rfl) ⟨5486021, by rfl⟩ : syracuseStep 7314695 = 10972043) B10972043
theorem B1088815 : Blo 570811 1088815 := bstep (se 1 (by rfl) ⟨816611, by rfl⟩ : syracuseStep 1088815 = 1633223) B1633223
theorem B16522649 : Blo 570811 16522649 := bstep (se 2 (by rfl) ⟨6195993, by rfl⟩ : syracuseStep 16522649 = 12391987) B12391987
theorem B860153 : Blo 570811 860153 := bstep (se 2 (by rfl) ⟨322557, by rfl⟩ : syracuseStep 860153 = 645115) B645115
theorem B3252251 : Blo 570811 3252251 := bstep (se 1 (by rfl) ⟨2439188, by rfl⟩ : syracuseStep 3252251 = 4878377) B4878377
theorem B860201 : Blo 570811 860201 := bstep (se 2 (by rfl) ⟨322575, by rfl⟩ : syracuseStep 860201 = 645151) B645151
theorem B4629095 : Blo 570811 4629095 := bstep (se 1 (by rfl) ⟨3471821, by rfl⟩ : syracuseStep 4629095 = 6943643) B6943643
theorem B860927 : Blo 570811 860927 := bstep (se 1 (by rfl) ⟨645695, by rfl⟩ : syracuseStep 860927 = 1291391) B1291391
theorem B861275 : Blo 570811 861275 := bstep (se 1 (by rfl) ⟨645956, by rfl⟩ : syracuseStep 861275 = 1291913) B1291913
theorem B861287 : Blo 570811 861287 := bstep (se 1 (by rfl) ⟨645965, by rfl⟩ : syracuseStep 861287 = 1291931) B1291931
theorem B1090721 : Blo 570811 1090721 := bstep (se 2 (by rfl) ⟨409020, by rfl⟩ : syracuseStep 1090721 = 818041) B818041
theorem B6628679 : Blo 570811 6628679 := bstep (se 1 (by rfl) ⟨4971509, by rfl⟩ : syracuseStep 6628679 = 9943019) B9943019
theorem B861551 : Blo 570811 861551 := bstep (se 1 (by rfl) ⟨646163, by rfl⟩ : syracuseStep 861551 = 1292327) B1292327
theorem B861737 : Blo 570811 861737 := bstep (se 2 (by rfl) ⟨323151, by rfl⟩ : syracuseStep 861737 = 646303) B646303
theorem B1287935 : Blo 570811 1287935 := bstep (se 1 (by rfl) ⟨965951, by rfl⟩ : syracuseStep 1287935 = 1931903) B1931903
theorem B862073 : Blo 570811 862073 := bstep (se 2 (by rfl) ⟨323277, by rfl⟩ : syracuseStep 862073 = 646555) B646555
theorem B862079 : Blo 570811 862079 := bstep (se 1 (by rfl) ⟨646559, by rfl⟩ : syracuseStep 862079 = 1293119) B1293119
theorem B2172815 : Blo 570811 2172815 := bstep (se 1 (by rfl) ⟨1629611, by rfl⟩ : syracuseStep 2172815 = 3259223) B3259223
theorem B29731171 : Blo 570811 29731171 := bstep (se 1 (by rfl) ⟨22298378, by rfl⟩ : syracuseStep 29731171 = 44596757) B44596757
theorem B12397009 : Blo 570811 12397009 := bstep (se 2 (by rfl) ⟨4648878, by rfl⟩ : syracuseStep 12397009 = 9297757) B9297757
theorem B4336091 : Blo 570811 4336091 := bstep (se 1 (by rfl) ⟨3252068, by rfl⟩ : syracuseStep 4336091 = 6504137) B6504137
theorem B1289087 : Blo 570811 1289087 := bstep (se 1 (by rfl) ⟨966815, by rfl⟩ : syracuseStep 1289087 = 1933631) B1933631
theorem B3485443 : Blo 570811 3485443 := bstep (se 1 (by rfl) ⟨2614082, by rfl⟩ : syracuseStep 3485443 = 5228165) B5228165
theorem B2174971 : Blo 570811 2174971 := bstep (se 1 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 2174971 = 3262457) B3262457
theorem B3977839 : Blo 570811 3977839 := bstep (se 1 (by rfl) ⟨2983379, by rfl⟩ : syracuseStep 3977839 = 5966759) B5966759
theorem B996223 : Blo 570811 996223 := bstep (se 1 (by rfl) ⟨747167, by rfl⟩ : syracuseStep 996223 = 1494335) B1494335
theorem B15709463 : Blo 570811 15709463 := bstep (se 1 (by rfl) ⟨11782097, by rfl⟩ : syracuseStep 15709463 = 23564195) B23564195
theorem B570911 : Blo 570811 570911 := bstep (se 1 (by rfl) ⟨428183, by rfl⟩ : syracuseStep 570911 = 856367) B856367
theorem B571071 : Blo 570811 571071 := bstep (se 1 (by rfl) ⟨428303, by rfl⟩ : syracuseStep 571071 = 856607) B856607
theorem B571239 : Blo 570811 571239 := bstep (se 1 (by rfl) ⟨428429, by rfl⟩ : syracuseStep 571239 = 856859) B856859
theorem B1292255 : Blo 570811 1292255 := bstep (se 1 (by rfl) ⟨969191, by rfl⟩ : syracuseStep 1292255 = 1938383) B1938383
theorem B7452749 : Blo 570811 7452749 := bstep (se 3 (by rfl) ⟨1397390, by rfl⟩ : syracuseStep 7452749 = 2794781) B2794781
theorem B964777 : Blo 570811 964777 := bstep (se 2 (by rfl) ⟨361791, by rfl⟩ : syracuseStep 964777 = 723583) B723583
theorem B1227241 : Blo 570811 1227241 := bstep (se 2 (by rfl) ⟨460215, by rfl⟩ : syracuseStep 1227241 = 920431) B920431
theorem B965371 : Blo 570811 965371 := bstep (se 1 (by rfl) ⟨724028, by rfl⟩ : syracuseStep 965371 = 1448057) B1448057
theorem B572575 : Blo 570811 572575 := bstep (se 1 (by rfl) ⟨429431, by rfl⟩ : syracuseStep 572575 = 858863) B858863
theorem B966127 : Blo 570811 966127 := bstep (se 1 (by rfl) ⟨724595, by rfl⟩ : syracuseStep 966127 = 1449191) B1449191
theorem B572955 : Blo 570811 572955 := bstep (se 1 (by rfl) ⟨429716, by rfl⟩ : syracuseStep 572955 = 859433) B859433
theorem B573511 : Blo 570811 573511 := bstep (se 1 (by rfl) ⟨430133, by rfl⟩ : syracuseStep 573511 = 860267) B860267
theorem B2441411 : Blo 570811 2441411 := bstep (se 1 (by rfl) ⟨1831058, by rfl⟩ : syracuseStep 2441411 = 3662117) B3662117
theorem B966991 : Blo 570811 966991 := bstep (se 1 (by rfl) ⟨725243, by rfl⟩ : syracuseStep 966991 = 1450487) B1450487
theorem B3096959 : Blo 570811 3096959 := bstep (se 1 (by rfl) ⟨2322719, by rfl⟩ : syracuseStep 3096959 = 4645439) B4645439
theorem B2933371 : Blo 570811 2933371 := bstep (se 1 (by rfl) ⟨2200028, by rfl⟩ : syracuseStep 2933371 = 4400057) B4400057
theorem B3261455 : Blo 570811 3261455 := bstep (se 1 (by rfl) ⟨2446091, by rfl⟩ : syracuseStep 3261455 = 4892183) B4892183
theorem B5588075 : Blo 570811 5588075 := bstep (se 1 (by rfl) ⟨4191056, by rfl⟩ : syracuseStep 5588075 = 8382113) B8382113
theorem B4146461 : Blo 570811 4146461 := bstep (se 3 (by rfl) ⟨777461, by rfl⟩ : syracuseStep 4146461 = 1554923) B1554923
theorem B9913661 : Blo 570811 9913661 := bstep (se 3 (by rfl) ⟨1858811, by rfl⟩ : syracuseStep 9913661 = 3717623) B3717623
theorem B2180591 : Blo 570811 2180591 := bstep (se 1 (by rfl) ⟨1635443, by rfl⟩ : syracuseStep 2180591 = 3270887) B3270887
theorem B7358161 : Blo 570811 7358161 := bstep (se 2 (by rfl) ⟨2759310, by rfl⟩ : syracuseStep 7358161 = 5518621) B5518621
theorem B6539129 : Blo 570811 6539129 := bstep (se 2 (by rfl) ⟨2452173, by rfl⟩ : syracuseStep 6539129 = 4904347) B4904347
theorem B13944791 : Blo 570811 13944791 := bstep (se 1 (by rfl) ⟨10458593, by rfl⟩ : syracuseStep 13944791 = 20917187) B20917187
theorem B870631 : Blo 570811 870631 := bstep (se 1 (by rfl) ⟨652973, by rfl⟩ : syracuseStep 870631 = 1305947) B1305947
theorem B969023 : Blo 570811 969023 := bstep (se 1 (by rfl) ⟨726767, by rfl⟩ : syracuseStep 969023 = 1453535) B1453535
theorem B270912437 : Blo 570811 270912437 := bstep (se 5 (by rfl) ⟨12699020, by rfl⟩ : syracuseStep 270912437 = 25398041) B25398041
theorem B8277011 : Blo 570811 8277011 := bstep (se 1 (by rfl) ⟨6207758, by rfl⟩ : syracuseStep 8277011 = 12415517) B12415517
theorem B26367839 : Blo 570811 26367839 := bstep (se 1 (by rfl) ⟨19775879, by rfl⟩ : syracuseStep 26367839 = 39551759) B39551759
theorem B4347755 : Blo 570811 4347755 := bstep (se 1 (by rfl) ⟨3260816, by rfl⟩ : syracuseStep 4347755 = 6521633) B6521633
theorem B19880063 : Blo 570811 19880063 := bstep (se 1 (by rfl) ⟨14910047, by rfl⟩ : syracuseStep 19880063 = 29820095) B29820095
theorem B2611529 : Blo 570811 2611529 := bstep (se 2 (by rfl) ⟨979323, by rfl⟩ : syracuseStep 2611529 = 1958647) B1958647
theorem B1628495 : Blo 570811 1628495 := bstep (se 1 (by rfl) ⟨1221371, by rfl⟩ : syracuseStep 1628495 = 2442743) B2442743
theorem B13982159 : Blo 570811 13982159 := bstep (se 1 (by rfl) ⟨10486619, by rfl⟩ : syracuseStep 13982159 = 20973239) B20973239
theorem B3267287 : Blo 570811 3267287 := bstep (se 1 (by rfl) ⟨2450465, by rfl⟩ : syracuseStep 3267287 = 4900931) B4900931
theorem B7363493 : Blo 570811 7363493 := bstep (se 4 (by rfl) ⟨690327, by rfl⟩ : syracuseStep 7363493 = 1380655) B1380655
theorem B646087 : Blo 570811 646087 := bstep (se 1 (by rfl) ⟨484565, by rfl⟩ : syracuseStep 646087 = 969131) B969131
theorem B580591 : Blo 570811 580591 := bstep (se 1 (by rfl) ⟨435443, by rfl⟩ : syracuseStep 580591 = 870887) B870887
theorem B2908223 : Blo 570811 2908223 := bstep (se 1 (by rfl) ⟨2181167, by rfl⟩ : syracuseStep 2908223 = 4362335) B4362335
theorem B9265589 : Blo 570811 9265589 := bstep (se 5 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 9265589 = 868649) B868649
theorem B11790299 : Blo 570811 11790299 := bstep (se 1 (by rfl) ⟨8842724, by rfl⟩ : syracuseStep 11790299 = 17685449) B17685449
theorem B5499211 : Blo 570811 5499211 := bstep (se 1 (by rfl) ⟨4124408, by rfl⟩ : syracuseStep 5499211 = 8248817) B8248817
theorem B1927583 : Blo 570811 1927583 := bstep (se 1 (by rfl) ⟨1445687, by rfl⟩ : syracuseStep 1927583 = 2891375) B2891375
theorem B4123487 : Blo 570811 4123487 := bstep (se 1 (by rfl) ⟨3092615, by rfl⟩ : syracuseStep 4123487 = 6185231) B6185231
theorem B111602609 : Blo 570811 111602609 := bstep (se 2 (by rfl) ⟨41850978, by rfl⟩ : syracuseStep 111602609 = 83701957) B83701957
theorem B1633405 : Blo 570811 1633405 := bstep (se 3 (by rfl) ⟨306263, by rfl⟩ : syracuseStep 1633405 = 612527) B612527
theorem B2059451 : Blo 570811 2059451 := bstep (se 1 (by rfl) ⟨1544588, by rfl⟩ : syracuseStep 2059451 = 3089177) B3089177
theorem B5500169 : Blo 570811 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B1863071 : Blo 570811 1863071 := bstep (se 1 (by rfl) ⟨1397303, by rfl⟩ : syracuseStep 1863071 = 2794607) B2794607
theorem B1928609 : Blo 570811 1928609 := bstep (se 2 (by rfl) ⟨723228, by rfl⟩ : syracuseStep 1928609 = 1446457) B1446457
theorem B4353587 : Blo 570811 4353587 := bstep (se 1 (by rfl) ⟨3265190, by rfl⟩ : syracuseStep 4353587 = 6530381) B6530381
theorem B1928825 : Blo 570811 1928825 := bstep (se 2 (by rfl) ⟨723309, by rfl⟩ : syracuseStep 1928825 = 1446619) B1446619
theorem B9793385 : Blo 570811 9793385 := bstep (se 2 (by rfl) ⟨3672519, by rfl⟩ : syracuseStep 9793385 = 7345039) B7345039
theorem B1831187 : Blo 570811 1831187 := bstep (se 1 (by rfl) ⟨1373390, by rfl⟩ : syracuseStep 1831187 = 2746781) B2746781
theorem B618983 : Blo 570811 618983 := bstep (se 1 (by rfl) ⟨464237, by rfl⟩ : syracuseStep 618983 = 928475) B928475
theorem B1930121 : Blo 570811 1930121 := bstep (se 2 (by rfl) ⟨723795, by rfl⟩ : syracuseStep 1930121 = 1447591) B1447591
theorem B8844203 : Blo 570811 8844203 := bstep (se 1 (by rfl) ⟨6633152, by rfl⟩ : syracuseStep 8844203 = 13266305) B13266305
theorem B1930553 : Blo 570811 1930553 := bstep (se 2 (by rfl) ⟨723957, by rfl⟩ : syracuseStep 1930553 = 1447915) B1447915
theorem B13563227 : Blo 570811 13563227 := bstep (se 1 (by rfl) ⟨10172420, by rfl⟩ : syracuseStep 13563227 = 20344841) B20344841
theorem B816799 : Blo 570811 816799 := bstep (se 1 (by rfl) ⟨612599, by rfl⟩ : syracuseStep 816799 = 1225199) B1225199
theorem B915209 : Blo 570811 915209 := bstep (se 2 (by rfl) ⟨343203, by rfl⟩ : syracuseStep 915209 = 686407) B686407
theorem B1832827 : Blo 570811 1832827 := bstep (se 1 (by rfl) ⟨1374620, by rfl⟩ : syracuseStep 1832827 = 2749241) B2749241
theorem B1833083 : Blo 570811 1833083 := bstep (se 1 (by rfl) ⟨1374812, by rfl⟩ : syracuseStep 1833083 = 2749625) B2749625
theorem B1243615 : Blo 570811 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B15695005 : Blo 570811 15695005 := bstep (se 3 (by rfl) ⟨2942813, by rfl⟩ : syracuseStep 15695005 = 5885627) B5885627
theorem B8258557 : Blo 570811 8258557 := bstep (se 3 (by rfl) ⟨1548479, by rfl⟩ : syracuseStep 8258557 = 3096959) B3096959
theorem B4359419 : Blo 570811 4359419 := bstep (se 1 (by rfl) ⟨3269564, by rfl⟩ : syracuseStep 4359419 = 6539129) B6539129
theorem B724135 : Blo 570811 724135 := bstep (se 1 (by rfl) ⟨543101, by rfl⟩ : syracuseStep 724135 = 1086203) B1086203
theorem B1741019 : Blo 570811 1741019 := bstep (se 1 (by rfl) ⟨1305764, by rfl⟩ : syracuseStep 1741019 = 2611529) B2611529
theorem B1085663 : Blo 570811 1085663 := bstep (se 1 (by rfl) ⟨814247, by rfl⟩ : syracuseStep 1085663 = 1628495) B1628495
theorem B856667 : Blo 570811 856667 := bstep (se 1 (by rfl) ⟨642500, by rfl⟩ : syracuseStep 856667 = 1285001) B1285001
theorem B11015099 : Blo 570811 11015099 := bstep (se 1 (by rfl) ⟨8261324, by rfl⟩ : syracuseStep 11015099 = 16522649) B16522649
theorem B2168167 : Blo 570811 2168167 := bstep (se 1 (by rfl) ⟨1626125, by rfl⟩ : syracuseStep 2168167 = 3252251) B3252251
theorem B1938815 : Blo 570811 1938815 := bstep (se 1 (by rfl) ⟨1454111, by rfl⟩ : syracuseStep 1938815 = 2908223) B2908223
theorem B3086063 : Blo 570811 3086063 := bstep (se 1 (by rfl) ⟨2314547, by rfl⟩ : syracuseStep 3086063 = 4629095) B4629095
theorem B727147 : Blo 570811 727147 := bstep (se 1 (by rfl) ⟨545360, by rfl⟩ : syracuseStep 727147 = 1090721) B1090721
theorem B858623 : Blo 570811 858623 := bstep (se 1 (by rfl) ⟨643967, by rfl⟩ : syracuseStep 858623 = 1287935) B1287935
theorem B1448543 : Blo 570811 1448543 := bstep (se 1 (by rfl) ⟨1086407, by rfl⟩ : syracuseStep 1448543 = 2172815) B2172815
theorem B1285055 : Blo 570811 1285055 := bstep (se 1 (by rfl) ⟨963791, by rfl⟩ : syracuseStep 1285055 = 1927583) B1927583
theorem B2890727 : Blo 570811 2890727 := bstep (se 1 (by rfl) ⟨2168045, by rfl⟩ : syracuseStep 2890727 = 4336091) B4336091
theorem B859391 : Blo 570811 859391 := bstep (se 1 (by rfl) ⟨644543, by rfl⟩ : syracuseStep 859391 = 1289087) B1289087
theorem B1089065 : Blo 570811 1089065 := bstep (se 2 (by rfl) ⟨408399, by rfl⟩ : syracuseStep 1089065 = 816799) B816799
theorem B1285739 : Blo 570811 1285739 := bstep (se 1 (by rfl) ⟨964304, by rfl⟩ : syracuseStep 1285739 = 1928609) B1928609
theorem B1285883 : Blo 570811 1285883 := bstep (se 1 (by rfl) ⟨964412, by rfl⟩ : syracuseStep 1285883 = 1928825) B1928825
theorem B6528923 : Blo 570811 6528923 := bstep (se 1 (by rfl) ⟨4896692, by rfl⟩ : syracuseStep 6528923 = 9793385) B9793385
theorem B1220791 : Blo 570811 1220791 := bstep (se 1 (by rfl) ⟨915593, by rfl⟩ : syracuseStep 1220791 = 1831187) B1831187
theorem B1286369 : Blo 570811 1286369 := bstep (se 2 (by rfl) ⟨482388, by rfl⟩ : syracuseStep 1286369 = 964777) B964777
theorem B1286747 : Blo 570811 1286747 := bstep (se 1 (by rfl) ⟨965060, by rfl⟩ : syracuseStep 1286747 = 1930121) B1930121
theorem B1287035 : Blo 570811 1287035 := bstep (se 1 (by rfl) ⟨965276, by rfl⟩ : syracuseStep 1287035 = 1930553) B1930553
theorem B1287161 : Blo 570811 1287161 := bstep (se 2 (by rfl) ⟨482685, by rfl⟩ : syracuseStep 1287161 = 965371) B965371
theorem B861449 : Blo 570811 861449 := bstep (se 2 (by rfl) ⟨323043, by rfl⟩ : syracuseStep 861449 = 646087) B646087
theorem B861503 : Blo 570811 861503 := bstep (se 1 (by rfl) ⟨646127, by rfl⟩ : syracuseStep 861503 = 1292255) B1292255
theorem B1222055 : Blo 570811 1222055 := bstep (se 1 (by rfl) ⟨916541, by rfl⟩ : syracuseStep 1222055 = 1833083) B1833083
theorem B1451753 : Blo 570811 1451753 := bstep (se 2 (by rfl) ⟨544407, by rfl⟩ : syracuseStep 1451753 = 1088815) B1088815
theorem B1288169 : Blo 570811 1288169 := bstep (se 2 (by rfl) ⟨483063, by rfl⟩ : syracuseStep 1288169 = 966127) B966127
theorem B1289321 : Blo 570811 1289321 := bstep (se 2 (by rfl) ⟨483495, by rfl⟩ : syracuseStep 1289321 = 966991) B966991
theorem B2174303 : Blo 570811 2174303 := bstep (se 1 (by rfl) ⟨1630727, by rfl⟩ : syracuseStep 2174303 = 3261455) B3261455
theorem B3911161 : Blo 570811 3911161 := bstep (se 2 (by rfl) ⟨1466685, by rfl⟩ : syracuseStep 3911161 = 2933371) B2933371
theorem B2764307 : Blo 570811 2764307 := bstep (se 1 (by rfl) ⟨2073230, by rfl⟩ : syracuseStep 2764307 = 4146461) B4146461
theorem B1453727 : Blo 570811 1453727 := bstep (se 1 (by rfl) ⟨1090295, by rfl⟩ : syracuseStep 1453727 = 2180591) B2180591
theorem B5518007 : Blo 570811 5518007 := bstep (se 1 (by rfl) ⟨4138505, by rfl⟩ : syracuseStep 5518007 = 8277011) B8277011
theorem B9810881 : Blo 570811 9810881 := bstep (se 2 (by rfl) ⟨3679080, by rfl⟩ : syracuseStep 9810881 = 7358161) B7358161
theorem B570831 : Blo 570811 570831 := bstep (se 1 (by rfl) ⟨428123, by rfl⟩ : syracuseStep 570831 = 856247) B856247
theorem B1291751 : Blo 570811 1291751 := bstep (se 1 (by rfl) ⟨968813, by rfl⟩ : syracuseStep 1291751 = 1937627) B1937627
theorem B570879 : Blo 570811 570879 := bstep (se 1 (by rfl) ⟨428159, by rfl⟩ : syracuseStep 570879 = 856319) B856319
theorem B8238671 : Blo 570811 8238671 := bstep (se 1 (by rfl) ⟨6179003, by rfl⟩ : syracuseStep 8238671 = 12358007) B12358007
theorem B571163 : Blo 570811 571163 := bstep (se 1 (by rfl) ⟨428372, by rfl⟩ : syracuseStep 571163 = 856745) B856745
theorem B571247 : Blo 570811 571247 := bstep (se 1 (by rfl) ⟨428435, by rfl⟩ : syracuseStep 571247 = 856871) B856871
theorem B21215141 : Blo 570811 21215141 := bstep (se 4 (by rfl) ⟨1988919, by rfl⟩ : syracuseStep 21215141 = 3977839) B3977839
theorem B16529345 : Blo 570811 16529345 := bstep (se 2 (by rfl) ⟨6198504, by rfl⟩ : syracuseStep 16529345 = 12397009) B12397009
theorem B571419 : Blo 570811 571419 := bstep (se 1 (by rfl) ⟨428564, by rfl⟩ : syracuseStep 571419 = 857129) B857129
theorem B571751 : Blo 570811 571751 := bstep (se 1 (by rfl) ⟨428813, by rfl⟩ : syracuseStep 571751 = 857627) B857627
theorem B571803 : Blo 570811 571803 := bstep (se 1 (by rfl) ⟨428852, by rfl⟩ : syracuseStep 571803 = 857705) B857705
theorem B571903 : Blo 570811 571903 := bstep (se 1 (by rfl) ⟨428927, by rfl⟩ : syracuseStep 571903 = 857855) B857855
theorem B17578559 : Blo 570811 17578559 := bstep (se 1 (by rfl) ⟨13183919, by rfl⟩ : syracuseStep 17578559 = 26367839) B26367839
theorem B2898503 : Blo 570811 2898503 := bstep (se 1 (by rfl) ⟨2173877, by rfl⟩ : syracuseStep 2898503 = 4347755) B4347755
theorem B572143 : Blo 570811 572143 := bstep (se 1 (by rfl) ⟨429107, by rfl⟩ : syracuseStep 572143 = 858215) B858215
theorem B572159 : Blo 570811 572159 := bstep (se 1 (by rfl) ⟨429119, by rfl⟩ : syracuseStep 572159 = 858239) B858239
theorem B13253375 : Blo 570811 13253375 := bstep (se 1 (by rfl) ⟨9940031, by rfl⟩ : syracuseStep 13253375 = 19880063) B19880063
theorem B2177873 : Blo 570811 2177873 := bstep (se 2 (by rfl) ⟨816702, by rfl⟩ : syracuseStep 2177873 = 1633405) B1633405
theorem B965479 : Blo 570811 965479 := bstep (se 1 (by rfl) ⟨724109, by rfl⟩ : syracuseStep 965479 = 1448219) B1448219
theorem B9321439 : Blo 570811 9321439 := bstep (se 1 (by rfl) ⟨6991079, by rfl⟩ : syracuseStep 9321439 = 13982159) B13982159
theorem B2178191 : Blo 570811 2178191 := bstep (se 1 (by rfl) ⟨1633643, by rfl⟩ : syracuseStep 2178191 = 3267287) B3267287
theorem B572571 : Blo 570811 572571 := bstep (se 1 (by rfl) ⟨429428, by rfl⟩ : syracuseStep 572571 = 858857) B858857
theorem B572671 : Blo 570811 572671 := bstep (se 1 (by rfl) ⟨429503, by rfl⟩ : syracuseStep 572671 = 859007) B859007
theorem B572699 : Blo 570811 572699 := bstep (se 1 (by rfl) ⟨429524, by rfl⟩ : syracuseStep 572699 = 859049) B859049
theorem B572735 : Blo 570811 572735 := bstep (se 1 (by rfl) ⟨429551, by rfl⟩ : syracuseStep 572735 = 859103) B859103
theorem B572827 : Blo 570811 572827 := bstep (se 1 (by rfl) ⟨429620, by rfl⟩ : syracuseStep 572827 = 859241) B859241
theorem B572911 : Blo 570811 572911 := bstep (se 1 (by rfl) ⟨429683, by rfl⟩ : syracuseStep 572911 = 859367) B859367
theorem B6602485 : Blo 570811 6602485 := bstep (se 5 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 6602485 = 618983) B618983
theorem B3096485 : Blo 570811 3096485 := bstep (se 4 (by rfl) ⟨290295, by rfl⟩ : syracuseStep 3096485 = 580591) B580591
theorem B2899961 : Blo 570811 2899961 := bstep (se 2 (by rfl) ⟨1087485, by rfl⟩ : syracuseStep 2899961 = 2174971) B2174971
theorem B573435 : Blo 570811 573435 := bstep (se 1 (by rfl) ⟨430076, by rfl⟩ : syracuseStep 573435 = 860153) B860153
theorem B573467 : Blo 570811 573467 := bstep (se 1 (by rfl) ⟨430100, by rfl⟩ : syracuseStep 573467 = 860201) B860201
theorem B6177059 : Blo 570811 6177059 := bstep (se 1 (by rfl) ⟨4632794, by rfl⟩ : syracuseStep 6177059 = 9265589) B9265589
theorem B573951 : Blo 570811 573951 := bstep (se 1 (by rfl) ⟨430463, by rfl⟩ : syracuseStep 573951 = 860927) B860927
theorem B574183 : Blo 570811 574183 := bstep (se 1 (by rfl) ⟨430637, by rfl⟩ : syracuseStep 574183 = 861275) B861275
theorem B574191 : Blo 570811 574191 := bstep (se 1 (by rfl) ⟨430643, by rfl⟩ : syracuseStep 574191 = 861287) B861287
theorem B574367 : Blo 570811 574367 := bstep (se 1 (by rfl) ⟨430775, by rfl⟩ : syracuseStep 574367 = 861551) B861551
theorem B574491 : Blo 570811 574491 := bstep (se 1 (by rfl) ⟨430868, by rfl⟩ : syracuseStep 574491 = 861737) B861737
theorem B1328297 : Blo 570811 1328297 := bstep (se 2 (by rfl) ⟨498111, by rfl⟩ : syracuseStep 1328297 = 996223) B996223
theorem B574715 : Blo 570811 574715 := bstep (se 1 (by rfl) ⟨431036, by rfl⟩ : syracuseStep 574715 = 862073) B862073
theorem B574719 : Blo 570811 574719 := bstep (se 1 (by rfl) ⟨431039, by rfl⟩ : syracuseStep 574719 = 862079) B862079
theorem B968233 : Blo 570811 968233 := bstep (se 2 (by rfl) ⟨363087, by rfl⟩ : syracuseStep 968233 = 726175) B726175
theorem B74401739 : Blo 570811 74401739 := bstep (se 1 (by rfl) ⟨55801304, by rfl⟩ : syracuseStep 74401739 = 111602609) B111602609
theorem B2902391 : Blo 570811 2902391 := bstep (se 1 (by rfl) ⟨2176793, by rfl⟩ : syracuseStep 2902391 = 4353587) B4353587
theorem B969097 : Blo 570811 969097 := bstep (se 2 (by rfl) ⟨363411, by rfl⟩ : syracuseStep 969097 = 726823) B726823
theorem B2443769 : Blo 570811 2443769 := bstep (se 2 (by rfl) ⟨916413, by rfl⟩ : syracuseStep 2443769 = 1832827) B1832827
theorem B1658153 : Blo 570811 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B10472975 : Blo 570811 10472975 := bstep (se 1 (by rfl) ⟨7854731, by rfl⟩ : syracuseStep 10472975 = 15709463) B15709463
theorem B18534005 : Blo 570811 18534005 := bstep (se 5 (by rfl) ⟨868781, by rfl⟩ : syracuseStep 18534005 = 1737563) B1737563
theorem B610139 : Blo 570811 610139 := bstep (se 1 (by rfl) ⟨457604, by rfl⟩ : syracuseStep 610139 = 915209) B915209
theorem B4968499 : Blo 570811 4968499 := bstep (se 1 (by rfl) ⟨3726374, by rfl⟩ : syracuseStep 4968499 = 7452749) B7452749
theorem B20926673 : Blo 570811 20926673 := bstep (se 2 (by rfl) ⟨7847502, by rfl⟩ : syracuseStep 20926673 = 15695005) B15695005
theorem B1627607 : Blo 570811 1627607 := bstep (se 1 (by rfl) ⟨1220705, by rfl⟩ : syracuseStep 1627607 = 2441411) B2441411
theorem B3725383 : Blo 570811 3725383 := bstep (se 1 (by rfl) ⟨2794037, by rfl⟩ : syracuseStep 3725383 = 5588075) B5588075
theorem B6609107 : Blo 570811 6609107 := bstep (se 1 (by rfl) ⟨4956830, by rfl⟩ : syracuseStep 6609107 = 9913661) B9913661
theorem B4643365 : Blo 570811 4643365 := bstep (se 4 (by rfl) ⟨435315, by rfl⟩ : syracuseStep 4643365 = 870631) B870631
theorem B9296527 : Blo 570811 9296527 := bstep (se 1 (by rfl) ⟨6972395, by rfl⟩ : syracuseStep 9296527 = 13944791) B13944791
theorem B646015 : Blo 570811 646015 := bstep (se 1 (by rfl) ⟨484511, by rfl⟩ : syracuseStep 646015 = 969023) B969023
theorem B180608291 : Blo 570811 180608291 := bstep (se 1 (by rfl) ⟨135456218, by rfl⟩ : syracuseStep 180608291 = 270912437) B270912437
theorem B7364519 : Blo 570811 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B7332281 : Blo 570811 7332281 := bstep (se 2 (by rfl) ⟨2749605, by rfl⟩ : syracuseStep 7332281 = 5499211) B5499211
theorem B39641561 : Blo 570811 39641561 := bstep (se 2 (by rfl) ⟨14865585, by rfl⟩ : syracuseStep 39641561 = 29731171) B29731171
theorem B4908995 : Blo 570811 4908995 := bstep (se 1 (by rfl) ⟨3681746, by rfl⟩ : syracuseStep 4908995 = 7363493) B7363493
theorem B4876463 : Blo 570811 4876463 := bstep (se 1 (by rfl) ⟨3657347, by rfl⟩ : syracuseStep 4876463 = 7314695) B7314695
theorem B4647257 : Blo 570811 4647257 := bstep (se 2 (by rfl) ⟨1742721, by rfl⟩ : syracuseStep 4647257 = 3485443) B3485443
theorem B6515801 : Blo 570811 6515801 := bstep (se 2 (by rfl) ⟨2443425, by rfl⟩ : syracuseStep 6515801 = 4886851) B4886851
theorem B4419119 : Blo 570811 4419119 := bstep (se 1 (by rfl) ⟨3314339, by rfl⟩ : syracuseStep 4419119 = 6628679) B6628679
theorem B7860199 : Blo 570811 7860199 := bstep (se 1 (by rfl) ⟨5895149, by rfl⟩ : syracuseStep 7860199 = 11790299) B11790299
theorem B2748991 : Blo 570811 2748991 := bstep (se 1 (by rfl) ⟨2061743, by rfl⟩ : syracuseStep 2748991 = 4123487) B4123487
theorem B1372967 : Blo 570811 1372967 := bstep (se 1 (by rfl) ⟨1029725, by rfl⟩ : syracuseStep 1372967 = 2059451) B2059451
theorem B3666779 : Blo 570811 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B1242047 : Blo 570811 1242047 := bstep (se 1 (by rfl) ⟨931535, by rfl⟩ : syracuseStep 1242047 = 1863071) B1863071
theorem B5896135 : Blo 570811 5896135 := bstep (se 1 (by rfl) ⟨4422101, by rfl⟩ : syracuseStep 5896135 = 8844203) B8844203
theorem B1636321 : Blo 570811 1636321 := bstep (se 2 (by rfl) ⟨613620, by rfl⟩ : syracuseStep 1636321 = 1227241) B1227241
theorem B9042151 : Blo 570811 9042151 := bstep (se 1 (by rfl) ⟨6781613, by rfl⟩ : syracuseStep 9042151 = 13563227) B13563227
theorem B11011409 : Blo 570811 11011409 := bstep (se 2 (by rfl) ⟨4129278, by rfl⟩ : syracuseStep 11011409 = 8258557) B8258557
theorem B1934927 : Blo 570811 1934927 := bstep (se 1 (by rfl) ⟨1451195, by rfl⟩ : syracuseStep 1934927 = 2902391) B2902391
theorem B6981983 : Blo 570811 6981983 := bstep (se 1 (by rfl) ⟨5236487, by rfl⟩ : syracuseStep 6981983 = 10472975) B10472975
theorem B12356003 : Blo 570811 12356003 := bstep (se 1 (by rfl) ⟨9267002, by rfl⟩ : syracuseStep 12356003 = 18534005) B18534005
theorem B3542125 : Blo 570811 3542125 := bstep (se 3 (by rfl) ⟨664148, by rfl⟩ : syracuseStep 3542125 = 1328297) B1328297
theorem B7343399 : Blo 570811 7343399 := bstep (se 1 (by rfl) ⟨5507549, by rfl⟩ : syracuseStep 7343399 = 11015099) B11015099
theorem B1085071 : Blo 570811 1085071 := bstep (se 1 (by rfl) ⟨813803, by rfl⟩ : syracuseStep 1085071 = 1627607) B1627607
theorem B856703 : Blo 570811 856703 := bstep (se 1 (by rfl) ⟨642527, by rfl⟩ : syracuseStep 856703 = 1285055) B1285055
theorem B5214881 : Blo 570811 5214881 := bstep (se 2 (by rfl) ⟨1955580, by rfl⟩ : syracuseStep 5214881 = 3911161) B3911161
theorem B857159 : Blo 570811 857159 := bstep (se 1 (by rfl) ⟨642869, by rfl⟩ : syracuseStep 857159 = 1285739) B1285739
theorem B857255 : Blo 570811 857255 := bstep (se 1 (by rfl) ⟨642941, by rfl⟩ : syracuseStep 857255 = 1285883) B1285883
theorem B6624665 : Blo 570811 6624665 := bstep (se 2 (by rfl) ⟨2484249, by rfl⟩ : syracuseStep 6624665 = 4968499) B4968499
theorem B857579 : Blo 570811 857579 := bstep (se 1 (by rfl) ⟨643184, by rfl⟩ : syracuseStep 857579 = 1286369) B1286369
theorem B4888187 : Blo 570811 4888187 := bstep (se 1 (by rfl) ⟨3666140, by rfl⟩ : syracuseStep 4888187 = 7332281) B7332281
theorem B857831 : Blo 570811 857831 := bstep (se 1 (by rfl) ⟨643373, by rfl⟩ : syracuseStep 857831 = 1286747) B1286747
theorem B858023 : Blo 570811 858023 := bstep (se 1 (by rfl) ⟨643517, by rfl⟩ : syracuseStep 858023 = 1287035) B1287035
theorem B858107 : Blo 570811 858107 := bstep (se 1 (by rfl) ⟨643580, by rfl⟩ : syracuseStep 858107 = 1287161) B1287161
theorem B858779 : Blo 570811 858779 := bstep (se 1 (by rfl) ⟨644084, by rfl⟩ : syracuseStep 858779 = 1288169) B1288169
theorem B3250975 : Blo 570811 3250975 := bstep (se 1 (by rfl) ⟨2438231, by rfl⟩ : syracuseStep 3250975 = 4876463) B4876463
theorem B2890889 : Blo 570811 2890889 := bstep (se 2 (by rfl) ⟨1084083, by rfl⟩ : syracuseStep 2890889 = 2168167) B2168167
theorem B859547 : Blo 570811 859547 := bstep (se 1 (by rfl) ⟨644660, by rfl⟩ : syracuseStep 859547 = 1289321) B1289321
theorem B1449535 : Blo 570811 1449535 := bstep (se 1 (by rfl) ⟨1087151, by rfl⟩ : syracuseStep 1449535 = 2174303) B2174303
theorem B1842871 : Blo 570811 1842871 := bstep (se 1 (by rfl) ⟨1382153, by rfl⟩ : syracuseStep 1842871 = 2764307) B2764307
theorem B3678671 : Blo 570811 3678671 := bstep (se 1 (by rfl) ⟨2759003, by rfl⟩ : syracuseStep 3678671 = 5518007) B5518007
theorem B828031 : Blo 570811 828031 := bstep (se 1 (by rfl) ⟨621023, by rfl⟩ : syracuseStep 828031 = 1242047) B1242047
theorem B12395369 : Blo 570811 12395369 := bstep (se 2 (by rfl) ⟨4648263, by rfl⟩ : syracuseStep 12395369 = 9296527) B9296527
theorem B861167 : Blo 570811 861167 := bstep (se 1 (by rfl) ⟨645875, by rfl⟩ : syracuseStep 861167 = 1291751) B1291751
theorem B1287305 : Blo 570811 1287305 := bstep (se 2 (by rfl) ⟨482739, by rfl⟩ : syracuseStep 1287305 = 965479) B965479
theorem B861353 : Blo 570811 861353 := bstep (se 2 (by rfl) ⟨323007, by rfl⟩ : syracuseStep 861353 = 646015) B646015
theorem B12428585 : Blo 570811 12428585 := bstep (se 2 (by rfl) ⟨4660719, by rfl⟩ : syracuseStep 12428585 = 9321439) B9321439
theorem B11019563 : Blo 570811 11019563 := bstep (se 1 (by rfl) ⟨8264672, by rfl⟩ : syracuseStep 11019563 = 16529345) B16529345
theorem B1451915 : Blo 570811 1451915 := bstep (se 1 (by rfl) ⟨1088936, by rfl⟩ : syracuseStep 1451915 = 2177873) B2177873
theorem B1452127 : Blo 570811 1452127 := bstep (se 1 (by rfl) ⟨1089095, by rfl⟩ : syracuseStep 1452127 = 2178191) B2178191
theorem B2895101 : Blo 570811 2895101 := bstep (se 3 (by rfl) ⟨542831, by rfl⟩ : syracuseStep 2895101 = 1085663) B1085663
theorem B1290977 : Blo 570811 1290977 := bstep (se 2 (by rfl) ⟨484116, by rfl⟩ : syracuseStep 1290977 = 968233) B968233
theorem B571111 : Blo 570811 571111 := bstep (se 1 (by rfl) ⟨428333, by rfl⟩ : syracuseStep 571111 = 856667) B856667
theorem B1292129 : Blo 570811 1292129 := bstep (se 2 (by rfl) ⟨484548, by rfl⟩ : syracuseStep 1292129 = 969097) B969097
theorem B1292543 : Blo 570811 1292543 := bstep (se 1 (by rfl) ⟨969407, by rfl⟩ : syracuseStep 1292543 = 1938815) B1938815
theorem B4406071 : Blo 570811 4406071 := bstep (se 1 (by rfl) ⟨3304553, by rfl⟩ : syracuseStep 4406071 = 6609107) B6609107
theorem B965513 : Blo 570811 965513 := bstep (se 2 (by rfl) ⟨362067, by rfl⟩ : syracuseStep 965513 = 724135) B724135
theorem B572415 : Blo 570811 572415 := bstep (se 1 (by rfl) ⟨429311, by rfl⟩ : syracuseStep 572415 = 858623) B858623
theorem B965695 : Blo 570811 965695 := bstep (se 1 (by rfl) ⟨724271, by rfl⟩ : syracuseStep 965695 = 1448543) B1448543
theorem B572927 : Blo 570811 572927 := bstep (se 1 (by rfl) ⟨429695, by rfl⟩ : syracuseStep 572927 = 859391) B859391
theorem B120405527 : Blo 570811 120405527 := bstep (se 1 (by rfl) ⟨90304145, by rfl⟩ : syracuseStep 120405527 = 180608291) B180608291
theorem B26427707 : Blo 570811 26427707 := bstep (se 1 (by rfl) ⟨19820780, by rfl⟩ : syracuseStep 26427707 = 39641561) B39641561
theorem B574299 : Blo 570811 574299 := bstep (se 1 (by rfl) ⟨430724, by rfl⟩ : syracuseStep 574299 = 861449) B861449
theorem B574335 : Blo 570811 574335 := bstep (se 1 (by rfl) ⟨430751, by rfl⟩ : syracuseStep 574335 = 861503) B861503
theorem B967835 : Blo 570811 967835 := bstep (se 1 (by rfl) ⟨725876, by rfl⟩ : syracuseStep 967835 = 1451753) B1451753
theorem B3098171 : Blo 570811 3098171 := bstep (se 1 (by rfl) ⟨2323628, by rfl⟩ : syracuseStep 3098171 = 4647257) B4647257
theorem B4343867 : Blo 570811 4343867 := bstep (se 1 (by rfl) ⟨3257900, by rfl⟩ : syracuseStep 4343867 = 6515801) B6515801
theorem B969151 : Blo 570811 969151 := bstep (se 1 (by rfl) ⟨726863, by rfl⟩ : syracuseStep 969151 = 1453727) B1453727
theorem B2181761 : Blo 570811 2181761 := bstep (se 2 (by rfl) ⟨818160, by rfl⟩ : syracuseStep 2181761 = 1636321) B1636321
theorem B4967177 : Blo 570811 4967177 := bstep (se 2 (by rfl) ⟨1862691, by rfl⟩ : syracuseStep 4967177 = 3725383) B3725383
theorem B969529 : Blo 570811 969529 := bstep (se 2 (by rfl) ⟨363573, by rfl⟩ : syracuseStep 969529 = 727147) B727147
theorem B2444519 : Blo 570811 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B6540587 : Blo 570811 6540587 := bstep (se 1 (by rfl) ⟨4905440, by rfl⟩ : syracuseStep 6540587 = 9810881) B9810881
theorem B5492447 : Blo 570811 5492447 := bstep (se 1 (by rfl) ⟨4119335, by rfl⟩ : syracuseStep 5492447 = 8238671) B8238671
theorem B14143427 : Blo 570811 14143427 := bstep (se 1 (by rfl) ⟨10607570, by rfl⟩ : syracuseStep 14143427 = 21215141) B21215141
theorem B2904173 : Blo 570811 2904173 := bstep (se 3 (by rfl) ⟨544532, by rfl⟩ : syracuseStep 2904173 = 1089065) B1089065
theorem B11719039 : Blo 570811 11719039 := bstep (se 1 (by rfl) ⟨8789279, by rfl⟩ : syracuseStep 11719039 = 17578559) B17578559
theorem B8835583 : Blo 570811 8835583 := bstep (se 1 (by rfl) ⟨6626687, by rfl⟩ : syracuseStep 8835583 = 13253375) B13253375
theorem B1627037 : Blo 570811 1627037 := bstep (se 3 (by rfl) ⟨305069, by rfl⟩ : syracuseStep 1627037 = 610139) B610139
theorem B8803313 : Blo 570811 8803313 := bstep (se 2 (by rfl) ⟨3301242, by rfl⟩ : syracuseStep 8803313 = 6602485) B6602485
theorem B31446053 : Blo 570811 31446053 := bstep (se 4 (by rfl) ⟨2948067, by rfl⟩ : syracuseStep 31446053 = 5896135) B5896135
theorem B4118039 : Blo 570811 4118039 := bstep (se 1 (by rfl) ⟨3088529, by rfl⟩ : syracuseStep 4118039 = 6177059) B6177059
theorem B1627721 : Blo 570811 1627721 := bstep (se 2 (by rfl) ⟨610395, by rfl⟩ : syracuseStep 1627721 = 1220791) B1220791
theorem B4642717 : Blo 570811 4642717 := bstep (se 3 (by rfl) ⟨870509, by rfl⟩ : syracuseStep 4642717 = 1741019) B1741019
theorem B2906279 : Blo 570811 2906279 := bstep (se 1 (by rfl) ⟨2179709, by rfl⟩ : syracuseStep 2906279 = 4359419) B4359419
theorem B49601159 : Blo 570811 49601159 := bstep (se 1 (by rfl) ⟨37200869, by rfl⟩ : syracuseStep 49601159 = 74401739) B74401739
theorem B1629179 : Blo 570811 1629179 := bstep (se 1 (by rfl) ⟨1221884, by rfl⟩ : syracuseStep 1629179 = 2443769) B2443769
theorem B1105435 : Blo 570811 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B13951115 : Blo 570811 13951115 := bstep (se 1 (by rfl) ⟨10463336, by rfl⟩ : syracuseStep 13951115 = 20926673) B20926673
theorem B2057375 : Blo 570811 2057375 := bstep (se 1 (by rfl) ⟨1543031, by rfl⟩ : syracuseStep 2057375 = 3086063) B3086063
theorem B1927151 : Blo 570811 1927151 := bstep (se 1 (by rfl) ⟨1445363, by rfl⟩ : syracuseStep 1927151 = 2890727) B2890727
theorem B4352615 : Blo 570811 4352615 := bstep (se 1 (by rfl) ⟨3264461, by rfl⟩ : syracuseStep 4352615 = 6528923) B6528923
theorem B4909679 : Blo 570811 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B10480265 : Blo 570811 10480265 := bstep (se 2 (by rfl) ⟨3930099, by rfl⟩ : syracuseStep 10480265 = 7860199) B7860199
theorem B3665321 : Blo 570811 3665321 := bstep (se 2 (by rfl) ⟨1374495, by rfl⟩ : syracuseStep 3665321 = 2748991) B2748991
theorem B814703 : Blo 570811 814703 := bstep (se 1 (by rfl) ⟨611027, by rfl⟩ : syracuseStep 814703 = 1222055) B1222055
theorem B3272663 : Blo 570811 3272663 := bstep (se 1 (by rfl) ⟨2454497, by rfl⟩ : syracuseStep 3272663 = 4908995) B4908995
theorem B2946079 : Blo 570811 2946079 := bstep (se 1 (by rfl) ⟨2209559, by rfl⟩ : syracuseStep 2946079 = 4419119) B4419119
theorem B12056201 : Blo 570811 12056201 := bstep (se 2 (by rfl) ⟨4521075, by rfl⟩ : syracuseStep 12056201 = 9042151) B9042151
theorem B915311 : Blo 570811 915311 := bstep (se 1 (by rfl) ⟨686483, by rfl⟩ : syracuseStep 915311 = 1372967) B1372967
theorem B6191153 : Blo 570811 6191153 := bstep (se 2 (by rfl) ⟨2321682, by rfl⟩ : syracuseStep 6191153 = 4643365) B4643365
theorem B1932335 : Blo 570811 1932335 := bstep (se 1 (by rfl) ⟨1449251, by rfl⟩ : syracuseStep 1932335 = 2898503) B2898503
theorem B2064323 : Blo 570811 2064323 := bstep (se 1 (by rfl) ⟨1548242, by rfl⟩ : syracuseStep 2064323 = 3096485) B3096485
theorem B1933307 : Blo 570811 1933307 := bstep (se 1 (by rfl) ⟨1449980, by rfl⟩ : syracuseStep 1933307 = 2899961) B2899961
theorem B7340939 : Blo 570811 7340939 := bstep (se 1 (by rfl) ⟨5505704, by rfl⟩ : syracuseStep 7340939 = 11011409) B11011409
theorem B2065447 : Blo 570811 2065447 := bstep (se 1 (by rfl) ⟨1549085, by rfl⟩ : syracuseStep 2065447 = 3098171) B3098171
theorem B4654655 : Blo 570811 4654655 := bstep (se 1 (by rfl) ⟨3490991, by rfl⟩ : syracuseStep 4654655 = 6981983) B6981983
theorem B4360391 : Blo 570811 4360391 := bstep (se 1 (by rfl) ⟨3270293, by rfl⟩ : syracuseStep 4360391 = 6540587) B6540587
theorem B1936115 : Blo 570811 1936115 := bstep (se 1 (by rfl) ⟨1452086, by rfl⟩ : syracuseStep 1936115 = 2904173) B2904173
theorem B1936169 : Blo 570811 1936169 := bstep (se 2 (by rfl) ⟨726063, by rfl⟩ : syracuseStep 1936169 = 1452127) B1452127
theorem B1084691 : Blo 570811 1084691 := bstep (se 1 (by rfl) ⟨813518, by rfl⟩ : syracuseStep 1084691 = 1627037) B1627037
theorem B5868875 : Blo 570811 5868875 := bstep (se 1 (by rfl) ⟨4401656, by rfl⟩ : syracuseStep 5868875 = 8803313) B8803313
theorem B1085147 : Blo 570811 1085147 := bstep (se 1 (by rfl) ⟨813860, by rfl⟩ : syracuseStep 1085147 = 1627721) B1627721
theorem B1937519 : Blo 570811 1937519 := bstep (se 1 (by rfl) ⟨1453139, by rfl⟩ : syracuseStep 1937519 = 2906279) B2906279
theorem B4722833 : Blo 570811 4722833 := bstep (se 2 (by rfl) ⟨1771062, by rfl⟩ : syracuseStep 4722833 = 3542125) B3542125
theorem B33067439 : Blo 570811 33067439 := bstep (se 1 (by rfl) ⟨24800579, by rfl⟩ : syracuseStep 33067439 = 49601159) B49601159
theorem B1086119 : Blo 570811 1086119 := bstep (se 1 (by rfl) ⟨814589, by rfl⟩ : syracuseStep 1086119 = 1629179) B1629179
theorem B1446761 : Blo 570811 1446761 := bstep (se 2 (by rfl) ⟨542535, by rfl⟩ : syracuseStep 1446761 = 1085071) B1085071
theorem B8263579 : Blo 570811 8263579 := bstep (se 1 (by rfl) ⟨6197684, by rfl⟩ : syracuseStep 8263579 = 12395369) B12395369
theorem B858203 : Blo 570811 858203 := bstep (se 1 (by rfl) ⟨643652, by rfl⟩ : syracuseStep 858203 = 1287305) B1287305
theorem B7346375 : Blo 570811 7346375 := bstep (se 1 (by rfl) ⟨5509781, by rfl⟩ : syracuseStep 7346375 = 11019563) B11019563
theorem B1284767 : Blo 570811 1284767 := bstep (se 1 (by rfl) ⟨963575, by rfl⟩ : syracuseStep 1284767 = 1927151) B1927151
theorem B6986843 : Blo 570811 6986843 := bstep (se 1 (by rfl) ⟨5240132, by rfl⟩ : syracuseStep 6986843 = 10480265) B10480265
theorem B13245805 : Blo 570811 13245805 := bstep (se 3 (by rfl) ⟨2483588, by rfl⟩ : syracuseStep 13245805 = 4967177) B4967177
theorem B860651 : Blo 570811 860651 := bstep (se 1 (by rfl) ⟨645488, by rfl⟩ : syracuseStep 860651 = 1290977) B1290977
theorem B4334633 : Blo 570811 4334633 := bstep (se 2 (by rfl) ⟨1625487, by rfl⟩ : syracuseStep 4334633 = 3250975) B3250975
theorem B5874761 : Blo 570811 5874761 := bstep (se 2 (by rfl) ⟨2203035, by rfl⟩ : syracuseStep 5874761 = 4406071) B4406071
theorem B8037467 : Blo 570811 8037467 := bstep (se 1 (by rfl) ⟨6028100, by rfl⟩ : syracuseStep 8037467 = 12056201) B12056201
theorem B861419 : Blo 570811 861419 := bstep (se 1 (by rfl) ⟨646064, by rfl⟩ : syracuseStep 861419 = 1292129) B1292129
theorem B1287593 : Blo 570811 1287593 := bstep (se 2 (by rfl) ⟨482847, by rfl⟩ : syracuseStep 1287593 = 965695) B965695
theorem B861695 : Blo 570811 861695 := bstep (se 1 (by rfl) ⟨646271, by rfl⟩ : syracuseStep 861695 = 1292543) B1292543
theorem B2172541 : Blo 570811 2172541 := bstep (se 3 (by rfl) ⟨407351, by rfl⟩ : syracuseStep 2172541 = 814703) B814703
theorem B1288223 : Blo 570811 1288223 := bstep (se 1 (by rfl) ⟨966167, by rfl⟩ : syracuseStep 1288223 = 1932335) B1932335
theorem B1288871 : Blo 570811 1288871 := bstep (se 1 (by rfl) ⟨966653, by rfl⟩ : syracuseStep 1288871 = 1933307) B1933307
theorem B1289951 : Blo 570811 1289951 := bstep (se 1 (by rfl) ⟨967463, by rfl⟩ : syracuseStep 1289951 = 1934927) B1934927
theorem B2895911 : Blo 570811 2895911 := bstep (se 1 (by rfl) ⟨2171933, by rfl⟩ : syracuseStep 2895911 = 4343867) B4343867
theorem B1454507 : Blo 570811 1454507 := bstep (se 1 (by rfl) ⟨1090880, by rfl⟩ : syracuseStep 1454507 = 2181761) B2181761
theorem B13906349 : Blo 570811 13906349 := bstep (se 3 (by rfl) ⟨2607440, by rfl⟩ : syracuseStep 13906349 = 5214881) B5214881
theorem B4895599 : Blo 570811 4895599 := bstep (se 1 (by rfl) ⟨3671699, by rfl⟩ : syracuseStep 4895599 = 7343399) B7343399
theorem B571135 : Blo 570811 571135 := bstep (se 1 (by rfl) ⟨428351, by rfl⟩ : syracuseStep 571135 = 856703) B856703
theorem B1292201 : Blo 570811 1292201 := bstep (se 2 (by rfl) ⟨484575, by rfl⟩ : syracuseStep 1292201 = 969151) B969151
theorem B571439 : Blo 570811 571439 := bstep (se 1 (by rfl) ⟨428579, by rfl⟩ : syracuseStep 571439 = 857159) B857159
theorem B571503 : Blo 570811 571503 := bstep (se 1 (by rfl) ⟨428627, by rfl⟩ : syracuseStep 571503 = 857255) B857255
theorem B571719 : Blo 570811 571719 := bstep (se 1 (by rfl) ⟨428789, by rfl⟩ : syracuseStep 571719 = 857579) B857579
theorem B1292705 : Blo 570811 1292705 := bstep (se 2 (by rfl) ⟨484764, by rfl⟩ : syracuseStep 1292705 = 969529) B969529
theorem B3258791 : Blo 570811 3258791 := bstep (se 1 (by rfl) ⟨2444093, by rfl⟩ : syracuseStep 3258791 = 4888187) B4888187
theorem B571887 : Blo 570811 571887 := bstep (se 1 (by rfl) ⟨428915, by rfl⟩ : syracuseStep 571887 = 857831) B857831
theorem B572015 : Blo 570811 572015 := bstep (se 1 (by rfl) ⟨429011, by rfl⟩ : syracuseStep 572015 = 858023) B858023
theorem B572071 : Blo 570811 572071 := bstep (se 1 (by rfl) ⟨429053, by rfl⟩ : syracuseStep 572071 = 858107) B858107
theorem B572519 : Blo 570811 572519 := bstep (se 1 (by rfl) ⟨429389, by rfl⟩ : syracuseStep 572519 = 858779) B858779
theorem B573031 : Blo 570811 573031 := bstep (se 1 (by rfl) ⟨429773, by rfl⟩ : syracuseStep 573031 = 859547) B859547
theorem B2440829 : Blo 570811 2440829 := bstep (se 3 (by rfl) ⟨457655, by rfl⟩ : syracuseStep 2440829 = 915311) B915311
theorem B574111 : Blo 570811 574111 := bstep (se 1 (by rfl) ⟨430583, by rfl⟩ : syracuseStep 574111 = 861167) B861167
theorem B11780777 : Blo 570811 11780777 := bstep (se 2 (by rfl) ⟨4417791, by rfl⟩ : syracuseStep 11780777 = 8835583) B8835583
theorem B574235 : Blo 570811 574235 := bstep (se 1 (by rfl) ⟨430676, by rfl⟩ : syracuseStep 574235 = 861353) B861353
theorem B32949341 : Blo 570811 32949341 := bstep (se 3 (by rfl) ⟨6178001, by rfl⟩ : syracuseStep 32949341 = 12356003) B12356003
theorem B967943 : Blo 570811 967943 := bstep (se 1 (by rfl) ⟨725957, by rfl⟩ : syracuseStep 967943 = 1451915) B1451915
theorem B2901743 : Blo 570811 2901743 := bstep (se 1 (by rfl) ⟨2176307, by rfl⟩ : syracuseStep 2901743 = 4352615) B4352615
theorem B2443547 : Blo 570811 2443547 := bstep (se 1 (by rfl) ⟨1832660, by rfl⟩ : syracuseStep 2443547 = 3665321) B3665321
theorem B2181775 : Blo 570811 2181775 := bstep (se 1 (by rfl) ⟨1636331, by rfl⟩ : syracuseStep 2181775 = 3272663) B3272663
theorem B643675 : Blo 570811 643675 := bstep (se 1 (by rfl) ⟨482756, by rfl⟩ : syracuseStep 643675 = 965513) B965513
theorem B80270351 : Blo 570811 80270351 := bstep (se 1 (by rfl) ⟨60202763, by rfl⟩ : syracuseStep 80270351 = 120405527) B120405527
theorem B17618471 : Blo 570811 17618471 := bstep (se 1 (by rfl) ⟨13213853, by rfl⟩ : syracuseStep 17618471 = 26427707) B26427707
theorem B645223 : Blo 570811 645223 := bstep (se 1 (by rfl) ⟨483917, by rfl⟩ : syracuseStep 645223 = 967835) B967835
theorem B1104041 : Blo 570811 1104041 := bstep (se 2 (by rfl) ⟨414015, by rfl⟩ : syracuseStep 1104041 = 828031) B828031
theorem B3661631 : Blo 570811 3661631 := bstep (se 1 (by rfl) ⟨2746223, by rfl⟩ : syracuseStep 3661631 = 5492447) B5492447
theorem B9428951 : Blo 570811 9428951 := bstep (se 1 (by rfl) ⟨7071713, by rfl⟩ : syracuseStep 9428951 = 14143427) B14143427
theorem B20964035 : Blo 570811 20964035 := bstep (se 1 (by rfl) ⟨15723026, by rfl⟩ : syracuseStep 20964035 = 31446053) B31446053
theorem B4416443 : Blo 570811 4416443 := bstep (se 1 (by rfl) ⟨3312332, by rfl⟩ : syracuseStep 4416443 = 6624665) B6624665
theorem B2745359 : Blo 570811 2745359 := bstep (se 1 (by rfl) ⟨2059019, by rfl⟩ : syracuseStep 2745359 = 4118039) B4118039
theorem B1927259 : Blo 570811 1927259 := bstep (se 1 (by rfl) ⟨1445444, by rfl⟩ : syracuseStep 1927259 = 2890889) B2890889
theorem B9300743 : Blo 570811 9300743 := bstep (se 1 (by rfl) ⟨6975557, by rfl⟩ : syracuseStep 9300743 = 13951115) B13951115
theorem B2452447 : Blo 570811 2452447 := bstep (se 1 (by rfl) ⟨1839335, by rfl⟩ : syracuseStep 2452447 = 3678671) B3678671
theorem B15625385 : Blo 570811 15625385 := bstep (se 2 (by rfl) ⟨5859519, by rfl⟩ : syracuseStep 15625385 = 11719039) B11719039
theorem B1371583 : Blo 570811 1371583 := bstep (se 1 (by rfl) ⟨1028687, by rfl⟩ : syracuseStep 1371583 = 2057375) B2057375
theorem B8285723 : Blo 570811 8285723 := bstep (se 1 (by rfl) ⟨6214292, by rfl⟩ : syracuseStep 8285723 = 12428585) B12428585
theorem B3928105 : Blo 570811 3928105 := bstep (se 2 (by rfl) ⟨1473039, by rfl⟩ : syracuseStep 3928105 = 2946079) B2946079
theorem B3273119 : Blo 570811 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B1930067 : Blo 570811 1930067 := bstep (se 1 (by rfl) ⟨1447550, by rfl⟩ : syracuseStep 1930067 = 2895101) B2895101
theorem B6190289 : Blo 570811 6190289 := bstep (se 2 (by rfl) ⟨2321358, by rfl⟩ : syracuseStep 6190289 = 4642717) B4642717
theorem B6518717 : Blo 570811 6518717 := bstep (se 3 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 6518717 = 2444519) B2444519
theorem B4127435 : Blo 570811 4127435 := bstep (se 1 (by rfl) ⟨3095576, by rfl⟩ : syracuseStep 4127435 = 6191153) B6191153
theorem B1473913 : Blo 570811 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B1932713 : Blo 570811 1932713 := bstep (se 2 (by rfl) ⟨724767, by rfl⟩ : syracuseStep 1932713 = 1449535) B1449535
theorem B2457161 : Blo 570811 2457161 := bstep (se 2 (by rfl) ⟨921435, by rfl⟩ : syracuseStep 2457161 = 1842871) B1842871
theorem B5504861 : Blo 570811 5504861 := bstep (se 3 (by rfl) ⟨1032161, by rfl⟩ : syracuseStep 5504861 = 2064323) B2064323
theorem B1934495 : Blo 570811 1934495 := bstep (se 1 (by rfl) ⟨1450871, by rfl⟩ : syracuseStep 1934495 = 2901743) B2901743
theorem B2753929 : Blo 570811 2753929 := bstep (se 2 (by rfl) ⟨1032723, by rfl⟩ : syracuseStep 2753929 = 2065447) B2065447
theorem B723431 : Blo 570811 723431 := bstep (se 1 (by rfl) ⟨542573, by rfl⟩ : syracuseStep 723431 = 1085147) B1085147
theorem B3148555 : Blo 570811 3148555 := bstep (se 1 (by rfl) ⟨2361416, by rfl⟩ : syracuseStep 3148555 = 4722833) B4722833
theorem B724079 : Blo 570811 724079 := bstep (se 1 (by rfl) ⟨543059, by rfl⟩ : syracuseStep 724079 = 1086119) B1086119
theorem B53513567 : Blo 570811 53513567 := bstep (se 1 (by rfl) ⟨40135175, by rfl⟩ : syracuseStep 53513567 = 80270351) B80270351
theorem B856511 : Blo 570811 856511 := bstep (se 1 (by rfl) ⟨642383, by rfl⟩ : syracuseStep 856511 = 1284767) B1284767
theorem B4657895 : Blo 570811 4657895 := bstep (se 1 (by rfl) ⟨3493421, by rfl⟩ : syracuseStep 4657895 = 6986843) B6986843
theorem B2889755 : Blo 570811 2889755 := bstep (se 1 (by rfl) ⟨2167316, by rfl⟩ : syracuseStep 2889755 = 4334633) B4334633
theorem B858233 : Blo 570811 858233 := bstep (se 2 (by rfl) ⟨321837, by rfl⟩ : syracuseStep 858233 = 643675) B643675
theorem B858395 : Blo 570811 858395 := bstep (se 1 (by rfl) ⟨643796, by rfl⟩ : syracuseStep 858395 = 1287593) B1287593
theorem B6527465 : Blo 570811 6527465 := bstep (se 2 (by rfl) ⟨2447799, by rfl⟩ : syracuseStep 6527465 = 4895599) B4895599
theorem B858815 : Blo 570811 858815 := bstep (se 1 (by rfl) ⟨644111, by rfl⟩ : syracuseStep 858815 = 1288223) B1288223
theorem B1284839 : Blo 570811 1284839 := bstep (se 1 (by rfl) ⟨963629, by rfl⟩ : syracuseStep 1284839 = 1927259) B1927259
theorem B859247 : Blo 570811 859247 := bstep (se 1 (by rfl) ⟨644435, by rfl⟩ : syracuseStep 859247 = 1288871) B1288871
theorem B6200495 : Blo 570811 6200495 := bstep (se 1 (by rfl) ⟨4650371, by rfl⟩ : syracuseStep 6200495 = 9300743) B9300743
theorem B859967 : Blo 570811 859967 := bstep (se 1 (by rfl) ⟨644975, by rfl⟩ : syracuseStep 859967 = 1289951) B1289951
theorem B11018105 : Blo 570811 11018105 := bstep (se 2 (by rfl) ⟨4131789, by rfl⟩ : syracuseStep 11018105 = 8263579) B8263579
theorem B860297 : Blo 570811 860297 := bstep (se 2 (by rfl) ⟨322611, by rfl⟩ : syracuseStep 860297 = 645223) B645223
theorem B1286711 : Blo 570811 1286711 := bstep (se 1 (by rfl) ⟨965033, by rfl⟩ : syracuseStep 1286711 = 1930067) B1930067
theorem B2892509 : Blo 570811 2892509 := bstep (se 3 (by rfl) ⟨542345, by rfl⟩ : syracuseStep 2892509 = 1084691) B1084691
theorem B861467 : Blo 570811 861467 := bstep (se 1 (by rfl) ⟨646100, by rfl⟩ : syracuseStep 861467 = 1292201) B1292201
theorem B861803 : Blo 570811 861803 := bstep (se 1 (by rfl) ⟨646352, by rfl⟩ : syracuseStep 861803 = 1292705) B1292705
theorem B2172527 : Blo 570811 2172527 := bstep (se 1 (by rfl) ⟨1629395, by rfl⟩ : syracuseStep 2172527 = 3258791) B3258791
theorem B1288475 : Blo 570811 1288475 := bstep (se 1 (by rfl) ⟨966356, by rfl⟩ : syracuseStep 1288475 = 1932713) B1932713
theorem B4893959 : Blo 570811 4893959 := bstep (se 1 (by rfl) ⟨3670469, by rfl⟩ : syracuseStep 4893959 = 7340939) B7340939
theorem B21966227 : Blo 570811 21966227 := bstep (se 1 (by rfl) ⟨16474670, by rfl⟩ : syracuseStep 21966227 = 32949341) B32949341
theorem B1290743 : Blo 570811 1290743 := bstep (se 1 (by rfl) ⟨968057, by rfl⟩ : syracuseStep 1290743 = 1936115) B1936115
theorem B1290779 : Blo 570811 1290779 := bstep (se 1 (by rfl) ⟨968084, by rfl⟩ : syracuseStep 1290779 = 1936169) B1936169
theorem B2896721 : Blo 570811 2896721 := bstep (se 2 (by rfl) ⟨1086270, by rfl⟩ : syracuseStep 2896721 = 2172541) B2172541
theorem B1291679 : Blo 570811 1291679 := bstep (se 1 (by rfl) ⟨968759, by rfl⟩ : syracuseStep 1291679 = 1937519) B1937519
theorem B964507 : Blo 570811 964507 := bstep (se 1 (by rfl) ⟨723380, by rfl⟩ : syracuseStep 964507 = 1446761) B1446761
theorem B11745647 : Blo 570811 11745647 := bstep (se 1 (by rfl) ⟨8809235, by rfl⟩ : syracuseStep 11745647 = 17618471) B17618471
theorem B572135 : Blo 570811 572135 := bstep (se 1 (by rfl) ⟨429101, by rfl⟩ : syracuseStep 572135 = 858203) B858203
theorem B4897583 : Blo 570811 4897583 := bstep (se 1 (by rfl) ⟨3673187, by rfl⟩ : syracuseStep 4897583 = 7346375) B7346375
theorem B2441087 : Blo 570811 2441087 := bstep (se 1 (by rfl) ⟨1830815, by rfl⟩ : syracuseStep 2441087 = 3661631) B3661631
theorem B573767 : Blo 570811 573767 := bstep (se 1 (by rfl) ⟨430325, by rfl⟩ : syracuseStep 573767 = 860651) B860651
theorem B13976023 : Blo 570811 13976023 := bstep (se 1 (by rfl) ⟨10482017, by rfl⟩ : syracuseStep 13976023 = 20964035) B20964035
theorem B3916507 : Blo 570811 3916507 := bstep (se 1 (by rfl) ⟨2937380, by rfl⟩ : syracuseStep 3916507 = 5874761) B5874761
theorem B5358311 : Blo 570811 5358311 := bstep (se 1 (by rfl) ⟨4018733, by rfl⟩ : syracuseStep 5358311 = 8037467) B8037467
theorem B574279 : Blo 570811 574279 := bstep (se 1 (by rfl) ⟨430709, by rfl⟩ : syracuseStep 574279 = 861419) B861419
theorem B574463 : Blo 570811 574463 := bstep (se 1 (by rfl) ⟨430847, by rfl⟩ : syracuseStep 574463 = 861695) B861695
theorem B5523815 : Blo 570811 5523815 := bstep (se 1 (by rfl) ⟨4142861, by rfl⟩ : syracuseStep 5523815 = 8285723) B8285723
theorem B2182079 : Blo 570811 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B969671 : Blo 570811 969671 := bstep (se 1 (by rfl) ⟨727253, by rfl⟩ : syracuseStep 969671 = 1454507) B1454507
theorem B15650333 : Blo 570811 15650333 := bstep (se 3 (by rfl) ⟨2934437, by rfl⟩ : syracuseStep 15650333 = 5868875) B5868875
theorem B4345811 : Blo 570811 4345811 := bstep (se 1 (by rfl) ⟨3259358, by rfl⟩ : syracuseStep 4345811 = 6518717) B6518717
theorem B1627219 : Blo 570811 1627219 := bstep (se 1 (by rfl) ⟨1220414, by rfl⟩ : syracuseStep 1627219 = 2440829) B2440829
theorem B7853851 : Blo 570811 7853851 := bstep (se 1 (by rfl) ⟨5890388, by rfl⟩ : syracuseStep 7853851 = 11780777) B11780777
theorem B645295 : Blo 570811 645295 := bstep (se 1 (by rfl) ⟨483971, by rfl⟩ : syracuseStep 645295 = 967943) B967943
theorem B3103103 : Blo 570811 3103103 := bstep (se 1 (by rfl) ⟨2327327, by rfl⟩ : syracuseStep 3103103 = 4654655) B4654655
theorem B2906927 : Blo 570811 2906927 := bstep (se 1 (by rfl) ⟨2180195, by rfl⟩ : syracuseStep 2906927 = 4360391) B4360391
theorem B1629031 : Blo 570811 1629031 := bstep (se 1 (by rfl) ⟨1221773, by rfl⟩ : syracuseStep 1629031 = 2443547) B2443547
theorem B22044959 : Blo 570811 22044959 := bstep (se 1 (by rfl) ⟨16533719, by rfl⟩ : syracuseStep 22044959 = 33067439) B33067439
theorem B2909033 : Blo 570811 2909033 := bstep (se 2 (by rfl) ⟨1090887, by rfl⟩ : syracuseStep 2909033 = 2181775) B2181775
theorem B3269929 : Blo 570811 3269929 := bstep (se 2 (by rfl) ⟨1226223, by rfl⟩ : syracuseStep 3269929 = 2452447) B2452447
theorem B1828777 : Blo 570811 1828777 := bstep (se 2 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 1828777 = 1371583) B1371583
theorem B6285967 : Blo 570811 6285967 := bstep (se 1 (by rfl) ⟨4714475, by rfl⟩ : syracuseStep 6285967 = 9428951) B9428951
theorem B5237473 : Blo 570811 5237473 := bstep (se 2 (by rfl) ⟨1964052, by rfl⟩ : syracuseStep 5237473 = 3928105) B3928105
theorem B2944109 : Blo 570811 2944109 := bstep (se 3 (by rfl) ⟨552020, by rfl⟩ : syracuseStep 2944109 = 1104041) B1104041
theorem B2944295 : Blo 570811 2944295 := bstep (se 1 (by rfl) ⟨2208221, by rfl⟩ : syracuseStep 2944295 = 4416443) B4416443
theorem B1830239 : Blo 570811 1830239 := bstep (se 1 (by rfl) ⟨1372679, by rfl⟩ : syracuseStep 1830239 = 2745359) B2745359
theorem B10416923 : Blo 570811 10416923 := bstep (se 1 (by rfl) ⟨7812692, by rfl⟩ : syracuseStep 10416923 = 15625385) B15625385
theorem B1930607 : Blo 570811 1930607 := bstep (se 1 (by rfl) ⟨1447955, by rfl⟩ : syracuseStep 1930607 = 2895911) B2895911
theorem B9270899 : Blo 570811 9270899 := bstep (se 1 (by rfl) ⟨6953174, by rfl⟩ : syracuseStep 9270899 = 13906349) B13906349
theorem B4126859 : Blo 570811 4126859 := bstep (se 1 (by rfl) ⟨3095144, by rfl⟩ : syracuseStep 4126859 = 6190289) B6190289
theorem B2751623 : Blo 570811 2751623 := bstep (se 1 (by rfl) ⟨2063717, by rfl⟩ : syracuseStep 2751623 = 4127435) B4127435
theorem B17661073 : Blo 570811 17661073 := bstep (se 2 (by rfl) ⟨6622902, by rfl⟩ : syracuseStep 17661073 = 13245805) B13245805
theorem B1965217 : Blo 570811 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B1638107 : Blo 570811 1638107 := bstep (se 1 (by rfl) ⟨1228580, by rfl⟩ : syracuseStep 1638107 = 2457161) B2457161
theorem B3669907 : Blo 570811 3669907 := bstep (se 1 (by rfl) ⟨2752430, by rfl⟩ : syracuseStep 3669907 = 5504861) B5504861
theorem B3572207 : Blo 570811 3572207 := bstep (se 1 (by rfl) ⟨2679155, by rfl⟩ : syracuseStep 3572207 = 5358311) B5358311
theorem B4359905 : Blo 570811 4359905 := bstep (se 2 (by rfl) ⟨1634964, by rfl⟩ : syracuseStep 4359905 = 3269929) B3269929
theorem B3671905 : Blo 570811 3671905 := bstep (se 2 (by rfl) ⟨1376964, by rfl⟩ : syracuseStep 3671905 = 2753929) B2753929
theorem B6983297 : Blo 570811 6983297 := bstep (se 2 (by rfl) ⟨2618736, by rfl⟩ : syracuseStep 6983297 = 5237473) B5237473
theorem B4198073 : Blo 570811 4198073 := bstep (se 2 (by rfl) ⟨1574277, by rfl⟩ : syracuseStep 4198073 = 3148555) B3148555
theorem B2068735 : Blo 570811 2068735 := bstep (se 1 (by rfl) ⟨1551551, by rfl⟩ : syracuseStep 2068735 = 3103103) B3103103
theorem B856559 : Blo 570811 856559 := bstep (se 1 (by rfl) ⟨642419, by rfl⟩ : syracuseStep 856559 = 1284839) B1284839
theorem B1937951 : Blo 570811 1937951 := bstep (se 1 (by rfl) ⟨1453463, by rfl⟩ : syracuseStep 1937951 = 2906927) B2906927
theorem B4133663 : Blo 570811 4133663 := bstep (se 1 (by rfl) ⟨3100247, by rfl⟩ : syracuseStep 4133663 = 6200495) B6200495
theorem B7345403 : Blo 570811 7345403 := bstep (se 1 (by rfl) ⟨5509052, by rfl⟩ : syracuseStep 7345403 = 11018105) B11018105
theorem B857807 : Blo 570811 857807 := bstep (se 1 (by rfl) ⟨643355, by rfl⟩ : syracuseStep 857807 = 1286711) B1286711
theorem B1939355 : Blo 570811 1939355 := bstep (se 1 (by rfl) ⟨1454516, by rfl⟩ : syracuseStep 1939355 = 2909033) B2909033
theorem B1448351 : Blo 570811 1448351 := bstep (se 1 (by rfl) ⟨1086263, by rfl⟩ : syracuseStep 1448351 = 2172527) B2172527
theorem B2169625 : Blo 570811 2169625 := bstep (se 2 (by rfl) ⟨813609, by rfl⟩ : syracuseStep 2169625 = 1627219) B1627219
theorem B858983 : Blo 570811 858983 := bstep (se 1 (by rfl) ⟨644237, by rfl⟩ : syracuseStep 858983 = 1288475) B1288475
theorem B1220159 : Blo 570811 1220159 := bstep (se 1 (by rfl) ⟨915119, by rfl⟩ : syracuseStep 1220159 = 1830239) B1830239
theorem B1286009 : Blo 570811 1286009 := bstep (se 2 (by rfl) ⟨482253, by rfl⟩ : syracuseStep 1286009 = 964507) B964507
theorem B860393 : Blo 570811 860393 := bstep (se 2 (by rfl) ⟨322647, by rfl⟩ : syracuseStep 860393 = 645295) B645295
theorem B860495 : Blo 570811 860495 := bstep (se 1 (by rfl) ⟨645371, by rfl⟩ : syracuseStep 860495 = 1290743) B1290743
theorem B860519 : Blo 570811 860519 := bstep (se 1 (by rfl) ⟨645389, by rfl⟩ : syracuseStep 860519 = 1290779) B1290779
theorem B1287071 : Blo 570811 1287071 := bstep (se 1 (by rfl) ⟨965303, by rfl⟩ : syracuseStep 1287071 = 1930607) B1930607
theorem B861119 : Blo 570811 861119 := bstep (se 1 (by rfl) ⟨645839, by rfl⟩ : syracuseStep 861119 = 1291679) B1291679
theorem B2172041 : Blo 570811 2172041 := bstep (se 2 (by rfl) ⟨814515, by rfl⟩ : syracuseStep 2172041 = 1629031) B1629031
theorem B1092071 : Blo 570811 1092071 := bstep (se 1 (by rfl) ⟨819053, by rfl⟩ : syracuseStep 1092071 = 1638107) B1638107
theorem B4893209 : Blo 570811 4893209 := bstep (se 2 (by rfl) ⟨1834953, by rfl⟩ : syracuseStep 4893209 = 3669907) B3669907
theorem B1289663 : Blo 570811 1289663 := bstep (se 1 (by rfl) ⟨967247, by rfl⟩ : syracuseStep 1289663 = 1934495) B1934495
theorem B5222009 : Blo 570811 5222009 := bstep (se 2 (by rfl) ⟨1958253, by rfl⟩ : syracuseStep 5222009 = 3916507) B3916507
theorem B3682543 : Blo 570811 3682543 := bstep (se 1 (by rfl) ⟨2761907, by rfl⟩ : syracuseStep 3682543 = 5523815) B5523815
theorem B1454719 : Blo 570811 1454719 := bstep (se 1 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 1454719 = 2182079) B2182079
theorem B10433555 : Blo 570811 10433555 := bstep (se 1 (by rfl) ⟨7825166, by rfl⟩ : syracuseStep 10433555 = 15650333) B15650333
theorem B2438369 : Blo 570811 2438369 := bstep (se 2 (by rfl) ⟨914388, by rfl⟩ : syracuseStep 2438369 = 1828777) B1828777
theorem B2897207 : Blo 570811 2897207 := bstep (se 1 (by rfl) ⟨2172905, by rfl⟩ : syracuseStep 2897207 = 4345811) B4345811
theorem B571007 : Blo 570811 571007 := bstep (se 1 (by rfl) ⟨428255, by rfl⟩ : syracuseStep 571007 = 856511) B856511
theorem B134100629 : Blo 570811 134100629 := bstep (se 6 (by rfl) ⟨3142983, by rfl⟩ : syracuseStep 134100629 = 6285967) B6285967
theorem B572155 : Blo 570811 572155 := bstep (se 1 (by rfl) ⟨429116, by rfl⟩ : syracuseStep 572155 = 858233) B858233
theorem B572263 : Blo 570811 572263 := bstep (se 1 (by rfl) ⟨429197, by rfl⟩ : syracuseStep 572263 = 858395) B858395
theorem B572543 : Blo 570811 572543 := bstep (se 1 (by rfl) ⟨429407, by rfl⟩ : syracuseStep 572543 = 858815) B858815
theorem B572831 : Blo 570811 572831 := bstep (se 1 (by rfl) ⟨429623, by rfl⟩ : syracuseStep 572831 = 859247) B859247
theorem B573311 : Blo 570811 573311 := bstep (se 1 (by rfl) ⟨429983, by rfl⟩ : syracuseStep 573311 = 859967) B859967
theorem B573531 : Blo 570811 573531 := bstep (se 1 (by rfl) ⟨430148, by rfl⟩ : syracuseStep 573531 = 860297) B860297
theorem B14696639 : Blo 570811 14696639 := bstep (se 1 (by rfl) ⟨11022479, by rfl⟩ : syracuseStep 14696639 = 22044959) B22044959
theorem B574311 : Blo 570811 574311 := bstep (se 1 (by rfl) ⟨430733, by rfl⟩ : syracuseStep 574311 = 861467) B861467
theorem B574535 : Blo 570811 574535 := bstep (se 1 (by rfl) ⟨430901, by rfl⟩ : syracuseStep 574535 = 861803) B861803
theorem B3262639 : Blo 570811 3262639 := bstep (se 1 (by rfl) ⟨2446979, by rfl⟩ : syracuseStep 3262639 = 4893959) B4893959
theorem B10471801 : Blo 570811 10471801 := bstep (se 2 (by rfl) ⟨3926925, by rfl⟩ : syracuseStep 10471801 = 7853851) B7853851
theorem B6180599 : Blo 570811 6180599 := bstep (se 1 (by rfl) ⟨4635449, by rfl⟩ : syracuseStep 6180599 = 9270899) B9270899
theorem B23548097 : Blo 570811 23548097 := bstep (se 2 (by rfl) ⟨8830536, by rfl⟩ : syracuseStep 23548097 = 17661073) B17661073
theorem B3265055 : Blo 570811 3265055 := bstep (se 1 (by rfl) ⟨2448791, by rfl⟩ : syracuseStep 3265055 = 4897583) B4897583
theorem B1627391 : Blo 570811 1627391 := bstep (se 1 (by rfl) ⟨1220543, by rfl⟩ : syracuseStep 1627391 = 2441087) B2441087
theorem B18634697 : Blo 570811 18634697 := bstep (se 2 (by rfl) ⟨6988011, by rfl⟩ : syracuseStep 18634697 = 13976023) B13976023
theorem B646447 : Blo 570811 646447 := bstep (se 1 (by rfl) ⟨484835, by rfl⟩ : syracuseStep 646447 = 969671) B969671
theorem B35675711 : Blo 570811 35675711 := bstep (se 1 (by rfl) ⟨26756783, by rfl⟩ : syracuseStep 35675711 = 53513567) B53513567
theorem B3105263 : Blo 570811 3105263 := bstep (se 1 (by rfl) ⟨2328947, by rfl⟩ : syracuseStep 3105263 = 4657895) B4657895
theorem B1926503 : Blo 570811 1926503 := bstep (se 1 (by rfl) ⟨1444877, by rfl⟩ : syracuseStep 1926503 = 2889755) B2889755
theorem B4351643 : Blo 570811 4351643 := bstep (se 1 (by rfl) ⟨3263732, by rfl⟩ : syracuseStep 4351643 = 6527465) B6527465
theorem B1928339 : Blo 570811 1928339 := bstep (se 1 (by rfl) ⟨1446254, by rfl⟩ : syracuseStep 1928339 = 2892509) B2892509
theorem B1929149 : Blo 570811 1929149 := bstep (se 3 (by rfl) ⟨361715, by rfl⟩ : syracuseStep 1929149 = 723431) B723431
theorem B1962739 : Blo 570811 1962739 := bstep (se 1 (by rfl) ⟨1472054, by rfl⟩ : syracuseStep 1962739 = 2944109) B2944109
theorem B1962863 : Blo 570811 1962863 := bstep (se 1 (by rfl) ⟨1472147, by rfl⟩ : syracuseStep 1962863 = 2944295) B2944295
theorem B14644151 : Blo 570811 14644151 := bstep (se 1 (by rfl) ⟨10983113, by rfl⟩ : syracuseStep 14644151 = 21966227) B21966227
theorem B1930877 : Blo 570811 1930877 := bstep (se 3 (by rfl) ⟨362039, by rfl⟩ : syracuseStep 1930877 = 724079) B724079
theorem B6944615 : Blo 570811 6944615 := bstep (se 1 (by rfl) ⟨5208461, by rfl⟩ : syracuseStep 6944615 = 10416923) B10416923
theorem B1931147 : Blo 570811 1931147 := bstep (se 1 (by rfl) ⟨1448360, by rfl⟩ : syracuseStep 1931147 = 2896721) B2896721
theorem B2751239 : Blo 570811 2751239 := bstep (se 1 (by rfl) ⟨2063429, by rfl⟩ : syracuseStep 2751239 = 4126859) B4126859
theorem B2620289 : Blo 570811 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B7830431 : Blo 570811 7830431 := bstep (se 1 (by rfl) ⟨5872823, by rfl⟩ : syracuseStep 7830431 = 11745647) B11745647
theorem B1834415 : Blo 570811 1834415 := bstep (se 1 (by rfl) ⟨1375811, by rfl⟩ : syracuseStep 1834415 = 2751623) B2751623
theorem B9797759 : Blo 570811 9797759 := bstep (se 1 (by rfl) ⟨7348319, by rfl⟩ : syracuseStep 9797759 = 14696639) B14696639
theorem B4655531 : Blo 570811 4655531 := bstep (se 1 (by rfl) ⟨3491648, by rfl⟩ : syracuseStep 4655531 = 6983297) B6983297
theorem B15698731 : Blo 570811 15698731 := bstep (se 1 (by rfl) ⟨11774048, by rfl⟩ : syracuseStep 15698731 = 23548097) B23548097
theorem B13962401 : Blo 570811 13962401 := bstep (se 2 (by rfl) ⟨5235900, by rfl⟩ : syracuseStep 13962401 = 10471801) B10471801
theorem B2755775 : Blo 570811 2755775 := bstep (se 1 (by rfl) ⟨2066831, by rfl⟩ : syracuseStep 2755775 = 4133663) B4133663
theorem B1084927 : Blo 570811 1084927 := bstep (se 1 (by rfl) ⟨813695, by rfl⟩ : syracuseStep 1084927 = 1627391) B1627391
theorem B12423131 : Blo 570811 12423131 := bstep (se 1 (by rfl) ⟨9317348, by rfl⟩ : syracuseStep 12423131 = 18634697) B18634697
theorem B857339 : Blo 570811 857339 := bstep (se 1 (by rfl) ⟨643004, by rfl⟩ : syracuseStep 857339 = 1286009) B1286009
theorem B2758313 : Blo 570811 2758313 := bstep (se 2 (by rfl) ⟨1034367, by rfl⟩ : syracuseStep 2758313 = 2068735) B2068735
theorem B858047 : Blo 570811 858047 := bstep (se 1 (by rfl) ⟨643535, by rfl⟩ : syracuseStep 858047 = 1287071) B1287071
theorem B1448027 : Blo 570811 1448027 := bstep (se 1 (by rfl) ⟨1086020, by rfl⟩ : syracuseStep 1448027 = 2172041) B2172041
theorem B1939625 : Blo 570811 1939625 := bstep (se 2 (by rfl) ⟨727359, by rfl⟩ : syracuseStep 1939625 = 1454719) B1454719
theorem B1284335 : Blo 570811 1284335 := bstep (se 1 (by rfl) ⟨963251, by rfl⟩ : syracuseStep 1284335 = 1926503) B1926503
theorem B728047 : Blo 570811 728047 := bstep (se 1 (by rfl) ⟨546035, by rfl⟩ : syracuseStep 728047 = 1092071) B1092071
theorem B1285559 : Blo 570811 1285559 := bstep (se 1 (by rfl) ⟨964169, by rfl⟩ : syracuseStep 1285559 = 1928339) B1928339
theorem B859775 : Blo 570811 859775 := bstep (se 1 (by rfl) ⟨644831, by rfl⟩ : syracuseStep 859775 = 1289663) B1289663
theorem B3481339 : Blo 570811 3481339 := bstep (se 1 (by rfl) ⟨2611004, by rfl⟩ : syracuseStep 3481339 = 5222009) B5222009
theorem B1286099 : Blo 570811 1286099 := bstep (se 1 (by rfl) ⟨964574, by rfl⟩ : syracuseStep 1286099 = 1929149) B1929149
theorem B6955703 : Blo 570811 6955703 := bstep (se 1 (by rfl) ⟨5216777, by rfl⟩ : syracuseStep 6955703 = 10433555) B10433555
theorem B2892833 : Blo 570811 2892833 := bstep (se 2 (by rfl) ⟨1084812, by rfl⟩ : syracuseStep 2892833 = 2169625) B2169625
theorem B1287251 : Blo 570811 1287251 := bstep (se 1 (by rfl) ⟨965438, by rfl⟩ : syracuseStep 1287251 = 1930877) B1930877
theorem B89400419 : Blo 570811 89400419 := bstep (se 1 (by rfl) ⟨67050314, by rfl⟩ : syracuseStep 89400419 = 134100629) B134100629
theorem B4629743 : Blo 570811 4629743 := bstep (se 1 (by rfl) ⟨3472307, by rfl⟩ : syracuseStep 4629743 = 6944615) B6944615
theorem B1287431 : Blo 570811 1287431 := bstep (se 1 (by rfl) ⟨965573, by rfl⟩ : syracuseStep 1287431 = 1931147) B1931147
theorem B861929 : Blo 570811 861929 := bstep (se 2 (by rfl) ⟨323223, by rfl⟩ : syracuseStep 861929 = 646447) B646447
theorem B1746859 : Blo 570811 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B5220287 : Blo 570811 5220287 := bstep (se 1 (by rfl) ⟨3915215, by rfl⟩ : syracuseStep 5220287 = 7830431) B7830431
theorem B1222943 : Blo 570811 1222943 := bstep (se 1 (by rfl) ⟨917207, by rfl⟩ : syracuseStep 1222943 = 1834415) B1834415
theorem B4895873 : Blo 570811 4895873 := bstep (se 2 (by rfl) ⟨1835952, by rfl⟩ : syracuseStep 4895873 = 3671905) B3671905
theorem B571039 : Blo 570811 571039 := bstep (se 1 (by rfl) ⟨428279, by rfl⟩ : syracuseStep 571039 = 856559) B856559
theorem B2176703 : Blo 570811 2176703 := bstep (se 1 (by rfl) ⟨1632527, by rfl⟩ : syracuseStep 2176703 = 3265055) B3265055
theorem B1291967 : Blo 570811 1291967 := bstep (se 1 (by rfl) ⟨968975, by rfl⟩ : syracuseStep 1291967 = 1937951) B1937951
theorem B4896935 : Blo 570811 4896935 := bstep (se 1 (by rfl) ⟨3672701, by rfl⟩ : syracuseStep 4896935 = 7345403) B7345403
theorem B571871 : Blo 570811 571871 := bstep (se 1 (by rfl) ⟨428903, by rfl⟩ : syracuseStep 571871 = 857807) B857807
theorem B1292903 : Blo 570811 1292903 := bstep (se 1 (by rfl) ⟨969677, by rfl⟩ : syracuseStep 1292903 = 1939355) B1939355
theorem B965567 : Blo 570811 965567 := bstep (se 1 (by rfl) ⟨724175, by rfl⟩ : syracuseStep 965567 = 1448351) B1448351
theorem B572655 : Blo 570811 572655 := bstep (se 1 (by rfl) ⟨429491, by rfl⟩ : syracuseStep 572655 = 858983) B858983
theorem B573595 : Blo 570811 573595 := bstep (se 1 (by rfl) ⟨430196, by rfl⟩ : syracuseStep 573595 = 860393) B860393
theorem B573663 : Blo 570811 573663 := bstep (se 1 (by rfl) ⟨430247, by rfl⟩ : syracuseStep 573663 = 860495) B860495
theorem B573679 : Blo 570811 573679 := bstep (se 1 (by rfl) ⟨430259, by rfl⟩ : syracuseStep 573679 = 860519) B860519
theorem B574079 : Blo 570811 574079 := bstep (se 1 (by rfl) ⟨430559, by rfl⟩ : syracuseStep 574079 = 861119) B861119
theorem B2901095 : Blo 570811 2901095 := bstep (se 1 (by rfl) ⟨2175821, by rfl⟩ : syracuseStep 2901095 = 4351643) B4351643
theorem B3262139 : Blo 570811 3262139 := bstep (se 1 (by rfl) ⟨2446604, by rfl⟩ : syracuseStep 3262139 = 4893209) B4893209
theorem B1625579 : Blo 570811 1625579 := bstep (se 1 (by rfl) ⟨1219184, by rfl⟩ : syracuseStep 1625579 = 2438369) B2438369
theorem B11194861 : Blo 570811 11194861 := bstep (se 3 (by rfl) ⟨2099036, by rfl⟩ : syracuseStep 11194861 = 4198073) B4198073
theorem B2381471 : Blo 570811 2381471 := bstep (se 1 (by rfl) ⟨1786103, by rfl⟩ : syracuseStep 2381471 = 3572207) B3572207
theorem B2906603 : Blo 570811 2906603 := bstep (se 1 (by rfl) ⟨2179952, by rfl⟩ : syracuseStep 2906603 = 4359905) B4359905
theorem B8280701 : Blo 570811 8280701 := bstep (se 3 (by rfl) ⟨1552631, by rfl⟩ : syracuseStep 8280701 = 3105263) B3105263
theorem B4120399 : Blo 570811 4120399 := bstep (se 1 (by rfl) ⟨3090299, by rfl⟩ : syracuseStep 4120399 = 6180599) B6180599
theorem B4350185 : Blo 570811 4350185 := bstep (se 2 (by rfl) ⟨1631319, by rfl⟩ : syracuseStep 4350185 = 3262639) B3262639
theorem B813439 : Blo 570811 813439 := bstep (se 1 (by rfl) ⟨610079, by rfl⟩ : syracuseStep 813439 = 1220159) B1220159
theorem B23783807 : Blo 570811 23783807 := bstep (se 1 (by rfl) ⟨17837855, by rfl⟩ : syracuseStep 23783807 = 35675711) B35675711
theorem B4910057 : Blo 570811 4910057 := bstep (se 2 (by rfl) ⟨1841271, by rfl⟩ : syracuseStep 4910057 = 3682543) B3682543
theorem B2616985 : Blo 570811 2616985 := bstep (se 2 (by rfl) ⟨981369, by rfl⟩ : syracuseStep 2616985 = 1962739) B1962739
theorem B1308575 : Blo 570811 1308575 := bstep (se 1 (by rfl) ⟨981431, by rfl⟩ : syracuseStep 1308575 = 1962863) B1962863
theorem B9762767 : Blo 570811 9762767 := bstep (se 1 (by rfl) ⟨7322075, by rfl⟩ : syracuseStep 9762767 = 14644151) B14644151
theorem B1931471 : Blo 570811 1931471 := bstep (se 1 (by rfl) ⟨1448603, by rfl⟩ : syracuseStep 1931471 = 2897207) B2897207
theorem B1834159 : Blo 570811 1834159 := bstep (se 1 (by rfl) ⟨1375619, by rfl⟩ : syracuseStep 1834159 = 2751239) B2751239
theorem B1934063 : Blo 570811 1934063 := bstep (se 1 (by rfl) ⟨1450547, by rfl⟩ : syracuseStep 1934063 = 2901095) B2901095
theorem B9308267 : Blo 570811 9308267 := bstep (se 1 (by rfl) ⟨6981200, by rfl⟩ : syracuseStep 9308267 = 13962401) B13962401
theorem B1837183 : Blo 570811 1837183 := bstep (se 1 (by rfl) ⟨1377887, by rfl⟩ : syracuseStep 1837183 = 2755775) B2755775
theorem B1083719 : Blo 570811 1083719 := bstep (se 1 (by rfl) ⟨812789, by rfl⟩ : syracuseStep 1083719 = 1625579) B1625579
theorem B2329145 : Blo 570811 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B1084585 : Blo 570811 1084585 := bstep (se 2 (by rfl) ⟨406719, by rfl⟩ : syracuseStep 1084585 = 813439) B813439
theorem B1838875 : Blo 570811 1838875 := bstep (se 1 (by rfl) ⟨1379156, by rfl⟩ : syracuseStep 1838875 = 2758313) B2758313
theorem B856223 : Blo 570811 856223 := bstep (se 1 (by rfl) ⟨642167, by rfl⟩ : syracuseStep 856223 = 1284335) B1284335
theorem B1937735 : Blo 570811 1937735 := bstep (se 1 (by rfl) ⟨1453301, by rfl⟩ : syracuseStep 1937735 = 2906603) B2906603
theorem B1446569 : Blo 570811 1446569 := bstep (se 2 (by rfl) ⟨542463, by rfl⟩ : syracuseStep 1446569 = 1084927) B1084927
theorem B857039 : Blo 570811 857039 := bstep (se 1 (by rfl) ⟨642779, by rfl⟩ : syracuseStep 857039 = 1285559) B1285559
theorem B857399 : Blo 570811 857399 := bstep (se 1 (by rfl) ⟨643049, by rfl⟩ : syracuseStep 857399 = 1286099) B1286099
theorem B858167 : Blo 570811 858167 := bstep (se 1 (by rfl) ⟨643625, by rfl⟩ : syracuseStep 858167 = 1287251) B1287251
theorem B3086495 : Blo 570811 3086495 := bstep (se 1 (by rfl) ⟨2314871, by rfl⟩ : syracuseStep 3086495 = 4629743) B4629743
theorem B858287 : Blo 570811 858287 := bstep (se 1 (by rfl) ⟨643715, by rfl⟩ : syracuseStep 858287 = 1287431) B1287431
theorem B3480191 : Blo 570811 3480191 := bstep (se 1 (by rfl) ⟨2610143, by rfl⟩ : syracuseStep 3480191 = 5220287) B5220287
theorem B1451135 : Blo 570811 1451135 := bstep (se 1 (by rfl) ⟨1088351, by rfl⟩ : syracuseStep 1451135 = 2176703) B2176703
theorem B861311 : Blo 570811 861311 := bstep (se 1 (by rfl) ⟨645983, by rfl⟩ : syracuseStep 861311 = 1291967) B1291967
theorem B1287647 : Blo 570811 1287647 := bstep (se 1 (by rfl) ⟨965735, by rfl⟩ : syracuseStep 1287647 = 1931471) B1931471
theorem B861935 : Blo 570811 861935 := bstep (se 1 (by rfl) ⟨646451, by rfl⟩ : syracuseStep 861935 = 1292903) B1292903
theorem B6531839 : Blo 570811 6531839 := bstep (se 1 (by rfl) ⟨4898879, by rfl⟩ : syracuseStep 6531839 = 9797759) B9797759
theorem B2174759 : Blo 570811 2174759 := bstep (se 1 (by rfl) ⟨1631069, by rfl⟩ : syracuseStep 2174759 = 3262139) B3262139
theorem B571559 : Blo 570811 571559 := bstep (se 1 (by rfl) ⟨428669, by rfl⟩ : syracuseStep 571559 = 857339) B857339
theorem B1587647 : Blo 570811 1587647 := bstep (se 1 (by rfl) ⟨1190735, by rfl⟩ : syracuseStep 1587647 = 2381471) B2381471
theorem B572031 : Blo 570811 572031 := bstep (se 1 (by rfl) ⟨429023, by rfl⟩ : syracuseStep 572031 = 858047) B858047
theorem B965351 : Blo 570811 965351 := bstep (se 1 (by rfl) ⟨724013, by rfl⟩ : syracuseStep 965351 = 1448027) B1448027
theorem B1293083 : Blo 570811 1293083 := bstep (se 1 (by rfl) ⟨969812, by rfl⟩ : syracuseStep 1293083 = 1939625) B1939625
theorem B5520467 : Blo 570811 5520467 := bstep (se 1 (by rfl) ⟨4140350, by rfl⟩ : syracuseStep 5520467 = 8280701) B8280701
theorem B3489313 : Blo 570811 3489313 := bstep (se 2 (by rfl) ⟨1308492, by rfl⟩ : syracuseStep 3489313 = 2616985) B2616985
theorem B573183 : Blo 570811 573183 := bstep (se 1 (by rfl) ⟨429887, by rfl⟩ : syracuseStep 573183 = 859775) B859775
theorem B2900123 : Blo 570811 2900123 := bstep (se 1 (by rfl) ⟨2175092, by rfl⟩ : syracuseStep 2900123 = 4350185) B4350185
theorem B4637135 : Blo 570811 4637135 := bstep (se 1 (by rfl) ⟨3477851, by rfl⟩ : syracuseStep 4637135 = 6955703) B6955703
theorem B14926481 : Blo 570811 14926481 := bstep (se 2 (by rfl) ⟨5597430, by rfl⟩ : syracuseStep 14926481 = 11194861) B11194861
theorem B3261181 : Blo 570811 3261181 := bstep (se 3 (by rfl) ⟨611471, by rfl⟩ : syracuseStep 3261181 = 1222943) B1222943
theorem B574619 : Blo 570811 574619 := bstep (se 1 (by rfl) ⟨430964, by rfl⟩ : syracuseStep 574619 = 861929) B861929
theorem B3263915 : Blo 570811 3263915 := bstep (se 1 (by rfl) ⟨2447936, by rfl⟩ : syracuseStep 3263915 = 4895873) B4895873
theorem B872383 : Blo 570811 872383 := bstep (se 1 (by rfl) ⟨654287, by rfl⟩ : syracuseStep 872383 = 1308575) B1308575
theorem B6508511 : Blo 570811 6508511 := bstep (se 1 (by rfl) ⟨4881383, by rfl⟩ : syracuseStep 6508511 = 9762767) B9762767
theorem B970729 : Blo 570811 970729 := bstep (se 2 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 970729 = 728047) B728047
theorem B3264623 : Blo 570811 3264623 := bstep (se 1 (by rfl) ⟨2448467, by rfl⟩ : syracuseStep 3264623 = 4896935) B4896935
theorem B2445545 : Blo 570811 2445545 := bstep (se 2 (by rfl) ⟨917079, by rfl⟩ : syracuseStep 2445545 = 1834159) B1834159
theorem B643711 : Blo 570811 643711 := bstep (se 1 (by rfl) ⟨482783, by rfl⟩ : syracuseStep 643711 = 965567) B965567
theorem B4641785 : Blo 570811 4641785 := bstep (se 2 (by rfl) ⟨1740669, by rfl⟩ : syracuseStep 4641785 = 3481339) B3481339
theorem B5493865 : Blo 570811 5493865 := bstep (se 2 (by rfl) ⟨2060199, by rfl⟩ : syracuseStep 5493865 = 4120399) B4120399
theorem B3103687 : Blo 570811 3103687 := bstep (se 1 (by rfl) ⟨2327765, by rfl⟩ : syracuseStep 3103687 = 4655531) B4655531
theorem B8282087 : Blo 570811 8282087 := bstep (se 1 (by rfl) ⟨6211565, by rfl⟩ : syracuseStep 8282087 = 12423131) B12423131
theorem B20931641 : Blo 570811 20931641 := bstep (se 2 (by rfl) ⟨7849365, by rfl⟩ : syracuseStep 20931641 = 15698731) B15698731
theorem B1928555 : Blo 570811 1928555 := bstep (se 1 (by rfl) ⟨1446416, by rfl⟩ : syracuseStep 1928555 = 2892833) B2892833
theorem B59600279 : Blo 570811 59600279 := bstep (se 1 (by rfl) ⟨44700209, by rfl⟩ : syracuseStep 59600279 = 89400419) B89400419
theorem B15855871 : Blo 570811 15855871 := bstep (se 1 (by rfl) ⟨11891903, by rfl⟩ : syracuseStep 15855871 = 23783807) B23783807
theorem B3273371 : Blo 570811 3273371 := bstep (se 1 (by rfl) ⟨2455028, by rfl⟩ : syracuseStep 3273371 = 4910057) B4910057
theorem B1933415 : Blo 570811 1933415 := bstep (se 1 (by rfl) ⟨1450061, by rfl⟩ : syracuseStep 1933415 = 2900123) B2900123
theorem B1446113 : Blo 570811 1446113 := bstep (se 2 (by rfl) ⟨542292, by rfl⟩ : syracuseStep 1446113 = 1084585) B1084585
theorem B21141161 : Blo 570811 21141161 := bstep (se 2 (by rfl) ⟨7927935, by rfl⟩ : syracuseStep 21141161 = 15855871) B15855871
theorem B858281 : Blo 570811 858281 := bstep (se 2 (by rfl) ⟨321855, by rfl⟩ : syracuseStep 858281 = 643711) B643711
theorem B2889917 : Blo 570811 2889917 := bstep (se 3 (by rfl) ⟨541859, by rfl⟩ : syracuseStep 2889917 = 1083719) B1083719
theorem B858431 : Blo 570811 858431 := bstep (se 1 (by rfl) ⟨643823, by rfl⟩ : syracuseStep 858431 = 1287647) B1287647
theorem B4233725 : Blo 570811 4233725 := bstep (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) B1587647
theorem B1285703 : Blo 570811 1285703 := bstep (se 1 (by rfl) ⟨964277, by rfl⟩ : syracuseStep 1285703 = 1928555) B1928555
theorem B1449839 : Blo 570811 1449839 := bstep (se 1 (by rfl) ⟨1087379, by rfl⟩ : syracuseStep 1449839 = 2174759) B2174759
theorem B4138249 : Blo 570811 4138249 := bstep (se 2 (by rfl) ⟨1551843, by rfl⟩ : syracuseStep 4138249 = 3103687) B3103687
theorem B862055 : Blo 570811 862055 := bstep (se 1 (by rfl) ⟨646541, by rfl⟩ : syracuseStep 862055 = 1293083) B1293083
theorem B3680311 : Blo 570811 3680311 := bstep (se 1 (by rfl) ⟨2760233, by rfl⟩ : syracuseStep 3680311 = 5520467) B5520467
theorem B1289375 : Blo 570811 1289375 := bstep (se 1 (by rfl) ⟨967031, by rfl⟩ : syracuseStep 1289375 = 1934063) B1934063
theorem B12365693 : Blo 570811 12365693 := bstep (se 3 (by rfl) ⟨2318567, by rfl⟩ : syracuseStep 12365693 = 4637135) B4637135
theorem B6205511 : Blo 570811 6205511 := bstep (se 1 (by rfl) ⟨4654133, by rfl⟩ : syracuseStep 6205511 = 9308267) B9308267
theorem B1552763 : Blo 570811 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B2175943 : Blo 570811 2175943 := bstep (se 1 (by rfl) ⟨1631957, by rfl⟩ : syracuseStep 2175943 = 3263915) B3263915
theorem B4339007 : Blo 570811 4339007 := bstep (se 1 (by rfl) ⟨3254255, by rfl⟩ : syracuseStep 4339007 = 6508511) B6508511
theorem B2176415 : Blo 570811 2176415 := bstep (se 1 (by rfl) ⟨1632311, by rfl⟩ : syracuseStep 2176415 = 3264623) B3264623
theorem B570815 : Blo 570811 570815 := bstep (se 1 (by rfl) ⟨428111, by rfl⟩ : syracuseStep 570815 = 856223) B856223
theorem B1291823 : Blo 570811 1291823 := bstep (se 1 (by rfl) ⟨968867, by rfl⟩ : syracuseStep 1291823 = 1937735) B1937735
theorem B964379 : Blo 570811 964379 := bstep (se 1 (by rfl) ⟨723284, by rfl⟩ : syracuseStep 964379 = 1446569) B1446569
theorem B571359 : Blo 570811 571359 := bstep (se 1 (by rfl) ⟨428519, by rfl⟩ : syracuseStep 571359 = 857039) B857039
theorem B3094523 : Blo 570811 3094523 := bstep (se 1 (by rfl) ⟨2320892, by rfl⟩ : syracuseStep 3094523 = 4641785) B4641785
theorem B571599 : Blo 570811 571599 := bstep (se 1 (by rfl) ⟨428699, by rfl⟩ : syracuseStep 571599 = 857399) B857399
theorem B572111 : Blo 570811 572111 := bstep (se 1 (by rfl) ⟨429083, by rfl⟩ : syracuseStep 572111 = 858167) B858167
theorem B572191 : Blo 570811 572191 := bstep (se 1 (by rfl) ⟨429143, by rfl⟩ : syracuseStep 572191 = 858287) B858287
theorem B1163177 : Blo 570811 1163177 := bstep (se 2 (by rfl) ⟨436191, by rfl⟩ : syracuseStep 1163177 = 872383) B872383
theorem B5521391 : Blo 570811 5521391 := bstep (se 1 (by rfl) ⟨4141043, by rfl⟩ : syracuseStep 5521391 = 8282087) B8282087
theorem B967423 : Blo 570811 967423 := bstep (se 1 (by rfl) ⟨725567, by rfl⟩ : syracuseStep 967423 = 1451135) B1451135
theorem B574207 : Blo 570811 574207 := bstep (se 1 (by rfl) ⟨430655, by rfl⟩ : syracuseStep 574207 = 861311) B861311
theorem B574623 : Blo 570811 574623 := bstep (se 1 (by rfl) ⟨430967, by rfl⟩ : syracuseStep 574623 = 861935) B861935
theorem B7325153 : Blo 570811 7325153 := bstep (se 2 (by rfl) ⟨2746932, by rfl⟩ : syracuseStep 7325153 = 5493865) B5493865
theorem B39733519 : Blo 570811 39733519 := bstep (se 1 (by rfl) ⟨29800139, by rfl⟩ : syracuseStep 39733519 = 59600279) B59600279
theorem B2182247 : Blo 570811 2182247 := bstep (se 1 (by rfl) ⟨1636685, by rfl⟩ : syracuseStep 2182247 = 3273371) B3273371
theorem B643567 : Blo 570811 643567 := bstep (se 1 (by rfl) ⟨482675, by rfl⟩ : syracuseStep 643567 = 965351) B965351
theorem B9950987 : Blo 570811 9950987 := bstep (se 1 (by rfl) ⟨7463240, by rfl⟩ : syracuseStep 9950987 = 14926481) B14926481
theorem B4348241 : Blo 570811 4348241 := bstep (se 2 (by rfl) ⟨1630590, by rfl⟩ : syracuseStep 4348241 = 3261181) B3261181
theorem B1630363 : Blo 570811 1630363 := bstep (se 1 (by rfl) ⟨1222772, by rfl⟩ : syracuseStep 1630363 = 2445545) B2445545
theorem B2449577 : Blo 570811 2449577 := bstep (se 2 (by rfl) ⟨918591, by rfl⟩ : syracuseStep 2449577 = 1837183) B1837183
theorem B2057663 : Blo 570811 2057663 := bstep (se 1 (by rfl) ⟨1543247, by rfl⟩ : syracuseStep 2057663 = 3086495) B3086495
theorem B2320127 : Blo 570811 2320127 := bstep (se 1 (by rfl) ⟨1740095, by rfl⟩ : syracuseStep 2320127 = 3480191) B3480191
theorem B2451833 : Blo 570811 2451833 := bstep (se 2 (by rfl) ⟨919437, by rfl⟩ : syracuseStep 2451833 = 1838875) B1838875
theorem B13954427 : Blo 570811 13954427 := bstep (se 1 (by rfl) ⟨10465820, by rfl⟩ : syracuseStep 13954427 = 20931641) B20931641
theorem B4354559 : Blo 570811 4354559 := bstep (se 1 (by rfl) ⟨3265919, by rfl⟩ : syracuseStep 4354559 = 6531839) B6531839
theorem B4652417 : Blo 570811 4652417 := bstep (se 2 (by rfl) ⟨1744656, by rfl⟩ : syracuseStep 4652417 = 3489313) B3489313
theorem B20708885 : Blo 570811 20708885 := bstep (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) B970729
theorem B4883435 : Blo 570811 4883435 := bstep (se 1 (by rfl) ⟨3662576, by rfl⟩ : syracuseStep 4883435 = 7325153) B7325153
theorem B14094107 : Blo 570811 14094107 := bstep (se 1 (by rfl) ⟨10570580, by rfl⟩ : syracuseStep 14094107 = 21141161) B21141161
theorem B2822483 : Blo 570811 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B857135 : Blo 570811 857135 := bstep (se 1 (by rfl) ⟨642851, by rfl⟩ : syracuseStep 857135 = 1285703) B1285703
theorem B858089 : Blo 570811 858089 := bstep (se 2 (by rfl) ⟨321783, by rfl⟩ : syracuseStep 858089 = 643567) B643567
theorem B1546751 : Blo 570811 1546751 := bstep (se 1 (by rfl) ⟨1160063, by rfl⟩ : syracuseStep 1546751 = 2320127) B2320127
theorem B859583 : Blo 570811 859583 := bstep (se 1 (by rfl) ⟨644687, by rfl⟩ : syracuseStep 859583 = 1289375) B1289375
theorem B4137007 : Blo 570811 4137007 := bstep (se 1 (by rfl) ⟨3102755, by rfl⟩ : syracuseStep 4137007 = 6205511) B6205511
theorem B2892671 : Blo 570811 2892671 := bstep (se 1 (by rfl) ⟨2169503, by rfl⟩ : syracuseStep 2892671 = 4339007) B4339007
theorem B1450943 : Blo 570811 1450943 := bstep (se 1 (by rfl) ⟨1088207, by rfl⟩ : syracuseStep 1450943 = 2176415) B2176415
theorem B861215 : Blo 570811 861215 := bstep (se 1 (by rfl) ⟨645911, by rfl⟩ : syracuseStep 861215 = 1291823) B1291823
theorem B13805923 : Blo 570811 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B3680927 : Blo 570811 3680927 := bstep (se 1 (by rfl) ⟨2760695, by rfl⟩ : syracuseStep 3680927 = 5521391) B5521391
theorem B1288943 : Blo 570811 1288943 := bstep (se 1 (by rfl) ⟨966707, by rfl⟩ : syracuseStep 1288943 = 1933415) B1933415
theorem B2173817 : Blo 570811 2173817 := bstep (se 2 (by rfl) ⟨815181, by rfl⟩ : syracuseStep 2173817 = 1630363) B1630363
theorem B1289897 : Blo 570811 1289897 := bstep (se 2 (by rfl) ⟨483711, by rfl⟩ : syracuseStep 1289897 = 967423) B967423
theorem B5517665 : Blo 570811 5517665 := bstep (se 2 (by rfl) ⟨2069124, by rfl⟩ : syracuseStep 5517665 = 4138249) B4138249
theorem B1454831 : Blo 570811 1454831 := bstep (se 1 (by rfl) ⟨1091123, by rfl⟩ : syracuseStep 1454831 = 2182247) B2182247
theorem B964075 : Blo 570811 964075 := bstep (se 1 (by rfl) ⟨723056, by rfl⟩ : syracuseStep 964075 = 1446113) B1446113
theorem B5487101 : Blo 570811 5487101 := bstep (se 3 (by rfl) ⟨1028831, by rfl⟩ : syracuseStep 5487101 = 2057663) B2057663
theorem B6633991 : Blo 570811 6633991 := bstep (se 1 (by rfl) ⟨4975493, by rfl⟩ : syracuseStep 6633991 = 9950987) B9950987
theorem B572187 : Blo 570811 572187 := bstep (se 1 (by rfl) ⟨429140, by rfl⟩ : syracuseStep 572187 = 858281) B858281
theorem B572287 : Blo 570811 572287 := bstep (se 1 (by rfl) ⟨429215, by rfl⟩ : syracuseStep 572287 = 858431) B858431
theorem B2898827 : Blo 570811 2898827 := bstep (se 1 (by rfl) ⟨2174120, by rfl⟩ : syracuseStep 2898827 = 4348241) B4348241
theorem B966559 : Blo 570811 966559 := bstep (se 1 (by rfl) ⟨724919, by rfl⟩ : syracuseStep 966559 = 1449839) B1449839
theorem B574703 : Blo 570811 574703 := bstep (se 1 (by rfl) ⟨431027, by rfl⟩ : syracuseStep 574703 = 862055) B862055
theorem B2901257 : Blo 570811 2901257 := bstep (se 2 (by rfl) ⟨1087971, by rfl⟩ : syracuseStep 2901257 = 2175943) B2175943
theorem B8243795 : Blo 570811 8243795 := bstep (se 1 (by rfl) ⟨6182846, by rfl⟩ : syracuseStep 8243795 = 12365693) B12365693
theorem B1035175 : Blo 570811 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B2903039 : Blo 570811 2903039 := bstep (se 1 (by rfl) ⟨2177279, by rfl⟩ : syracuseStep 2903039 = 4354559) B4354559
theorem B642919 : Blo 570811 642919 := bstep (se 1 (by rfl) ⟨482189, by rfl⟩ : syracuseStep 642919 = 964379) B964379
theorem B3101611 : Blo 570811 3101611 := bstep (se 1 (by rfl) ⟨2326208, by rfl⟩ : syracuseStep 3101611 = 4652417) B4652417
theorem B775451 : Blo 570811 775451 := bstep (se 1 (by rfl) ⟨581588, by rfl⟩ : syracuseStep 775451 = 1163177) B1163177
theorem B4907081 : Blo 570811 4907081 := bstep (se 2 (by rfl) ⟨1840155, by rfl⟩ : syracuseStep 4907081 = 3680311) B3680311
theorem B52978025 : Blo 570811 52978025 := bstep (se 2 (by rfl) ⟨19866759, by rfl⟩ : syracuseStep 52978025 = 39733519) B39733519
theorem B1926611 : Blo 570811 1926611 := bstep (se 1 (by rfl) ⟨1444958, by rfl⟩ : syracuseStep 1926611 = 2889917) B2889917
theorem B1633051 : Blo 570811 1633051 := bstep (se 1 (by rfl) ⟨1224788, by rfl⟩ : syracuseStep 1633051 = 2449577) B2449577
theorem B1634555 : Blo 570811 1634555 := bstep (se 1 (by rfl) ⟨1225916, by rfl⟩ : syracuseStep 1634555 = 2451833) B2451833
theorem B9302951 : Blo 570811 9302951 := bstep (se 1 (by rfl) ⟨6977213, by rfl⟩ : syracuseStep 9302951 = 13954427) B13954427
theorem B2063015 : Blo 570811 2063015 := bstep (se 1 (by rfl) ⟨1547261, by rfl⟩ : syracuseStep 2063015 = 3094523) B3094523
theorem B1934171 : Blo 570811 1934171 := bstep (se 1 (by rfl) ⟨1450628, by rfl⟩ : syracuseStep 1934171 = 2901257) B2901257
theorem B1935359 : Blo 570811 1935359 := bstep (se 1 (by rfl) ⟨1451519, by rfl⟩ : syracuseStep 1935359 = 2903039) B2903039
theorem B2067869 : Blo 570811 2067869 := bstep (se 3 (by rfl) ⟨387725, by rfl⟩ : syracuseStep 2067869 = 775451) B775451
theorem B1380233 : Blo 570811 1380233 := bstep (se 2 (by rfl) ⟨517587, by rfl⟩ : syracuseStep 1380233 = 1035175) B1035175
theorem B857225 : Blo 570811 857225 := bstep (se 2 (by rfl) ⟨321459, by rfl⟩ : syracuseStep 857225 = 642919) B642919
theorem B1284407 : Blo 570811 1284407 := bstep (se 1 (by rfl) ⟨963305, by rfl⟩ : syracuseStep 1284407 = 1926611) B1926611
theorem B4135481 : Blo 570811 4135481 := bstep (se 2 (by rfl) ⟨1550805, by rfl⟩ : syracuseStep 4135481 = 3101611) B3101611
theorem B859295 : Blo 570811 859295 := bstep (se 1 (by rfl) ⟨644471, by rfl⟩ : syracuseStep 859295 = 1288943) B1288943
theorem B1449211 : Blo 570811 1449211 := bstep (se 1 (by rfl) ⟨1086908, by rfl⟩ : syracuseStep 1449211 = 2173817) B2173817
theorem B1285433 : Blo 570811 1285433 := bstep (se 2 (by rfl) ⟨482037, by rfl⟩ : syracuseStep 1285433 = 964075) B964075
theorem B859931 : Blo 570811 859931 := bstep (se 1 (by rfl) ⟨644948, by rfl⟩ : syracuseStep 859931 = 1289897) B1289897
theorem B1089703 : Blo 570811 1089703 := bstep (se 1 (by rfl) ⟨817277, by rfl⟩ : syracuseStep 1089703 = 1634555) B1634555
theorem B3678443 : Blo 570811 3678443 := bstep (se 1 (by rfl) ⟨2758832, by rfl⟩ : syracuseStep 3678443 = 5517665) B5517665
theorem B6201967 : Blo 570811 6201967 := bstep (se 1 (by rfl) ⟨4651475, by rfl⟩ : syracuseStep 6201967 = 9302951) B9302951
theorem B1288745 : Blo 570811 1288745 := bstep (se 2 (by rfl) ⟨483279, by rfl⟩ : syracuseStep 1288745 = 966559) B966559
theorem B5516009 : Blo 570811 5516009 := bstep (se 2 (by rfl) ⟨2068503, by rfl⟩ : syracuseStep 5516009 = 4137007) B4137007
theorem B3255623 : Blo 570811 3255623 := bstep (se 1 (by rfl) ⟨2441717, by rfl⟩ : syracuseStep 3255623 = 4883435) B4883435
theorem B571423 : Blo 570811 571423 := bstep (se 1 (by rfl) ⟨428567, by rfl⟩ : syracuseStep 571423 = 857135) B857135
theorem B2177401 : Blo 570811 2177401 := bstep (se 2 (by rfl) ⟨816525, by rfl⟩ : syracuseStep 2177401 = 1633051) B1633051
theorem B572059 : Blo 570811 572059 := bstep (se 1 (by rfl) ⟨429044, by rfl⟩ : syracuseStep 572059 = 858089) B858089
theorem B1031167 : Blo 570811 1031167 := bstep (se 1 (by rfl) ⟨773375, by rfl⟩ : syracuseStep 1031167 = 1546751) B1546751
theorem B573055 : Blo 570811 573055 := bstep (se 1 (by rfl) ⟨429791, by rfl⟩ : syracuseStep 573055 = 859583) B859583
theorem B967295 : Blo 570811 967295 := bstep (se 1 (by rfl) ⟨725471, by rfl⟩ : syracuseStep 967295 = 1450943) B1450943
theorem B574143 : Blo 570811 574143 := bstep (se 1 (by rfl) ⟨430607, by rfl⟩ : syracuseStep 574143 = 861215) B861215
theorem B969887 : Blo 570811 969887 := bstep (se 1 (by rfl) ⟨727415, by rfl⟩ : syracuseStep 969887 = 1454831) B1454831
theorem B3658067 : Blo 570811 3658067 := bstep (se 1 (by rfl) ⟨2743550, by rfl⟩ : syracuseStep 3658067 = 5487101) B5487101
theorem B7526621 : Blo 570811 7526621 := bstep (se 3 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 7526621 = 2822483) B2822483
theorem B5495863 : Blo 570811 5495863 := bstep (se 1 (by rfl) ⟨4121897, by rfl⟩ : syracuseStep 5495863 = 8243795) B8243795
theorem B9396071 : Blo 570811 9396071 := bstep (se 1 (by rfl) ⟨7047053, by rfl⟩ : syracuseStep 9396071 = 14094107) B14094107
theorem B18407897 : Blo 570811 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B3271387 : Blo 570811 3271387 := bstep (se 1 (by rfl) ⟨2453540, by rfl⟩ : syracuseStep 3271387 = 4907081) B4907081
theorem B35318683 : Blo 570811 35318683 := bstep (se 1 (by rfl) ⟨26489012, by rfl⟩ : syracuseStep 35318683 = 52978025) B52978025
theorem B1928447 : Blo 570811 1928447 := bstep (se 1 (by rfl) ⟨1446335, by rfl⟩ : syracuseStep 1928447 = 2892671) B2892671
theorem B2453951 : Blo 570811 2453951 := bstep (se 1 (by rfl) ⟨1840463, by rfl⟩ : syracuseStep 2453951 = 3680927) B3680927
theorem B8845321 : Blo 570811 8845321 := bstep (se 2 (by rfl) ⟨3316995, by rfl⟩ : syracuseStep 8845321 = 6633991) B6633991
theorem B1375343 : Blo 570811 1375343 := bstep (se 1 (by rfl) ⟨1031507, by rfl⟩ : syracuseStep 1375343 = 2063015) B2063015
theorem B1932551 : Blo 570811 1932551 := bstep (se 1 (by rfl) ⟨1449413, by rfl⟩ : syracuseStep 1932551 = 2898827) B2898827
theorem B920155 : Blo 570811 920155 := bstep (se 1 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 920155 = 1380233) B1380233
theorem B4361849 : Blo 570811 4361849 := bstep (se 2 (by rfl) ⟨1635693, by rfl⟩ : syracuseStep 4361849 = 3271387) B3271387
theorem B47091577 : Blo 570811 47091577 := bstep (se 2 (by rfl) ⟨17659341, by rfl⟩ : syracuseStep 47091577 = 35318683) B35318683
theorem B856271 : Blo 570811 856271 := bstep (se 1 (by rfl) ⟨642203, by rfl⟩ : syracuseStep 856271 = 1284407) B1284407
theorem B2756987 : Blo 570811 2756987 := bstep (se 1 (by rfl) ⟨2067740, by rfl⟩ : syracuseStep 2756987 = 4135481) B4135481
theorem B856955 : Blo 570811 856955 := bstep (se 1 (by rfl) ⟨642716, by rfl⟩ : syracuseStep 856955 = 1285433) B1285433
theorem B6264047 : Blo 570811 6264047 := bstep (se 1 (by rfl) ⟨4698035, by rfl⟩ : syracuseStep 6264047 = 9396071) B9396071
theorem B859163 : Blo 570811 859163 := bstep (se 1 (by rfl) ⟨644372, by rfl⟩ : syracuseStep 859163 = 1288745) B1288745
theorem B3677339 : Blo 570811 3677339 := bstep (se 1 (by rfl) ⟨2758004, by rfl⟩ : syracuseStep 3677339 = 5516009) B5516009
theorem B1285631 : Blo 570811 1285631 := bstep (se 1 (by rfl) ⟨964223, by rfl⟩ : syracuseStep 1285631 = 1928447) B1928447
theorem B2170415 : Blo 570811 2170415 := bstep (se 1 (by rfl) ⟨1627811, by rfl⟩ : syracuseStep 2170415 = 3255623) B3255623
theorem B5514317 : Blo 570811 5514317 := bstep (se 3 (by rfl) ⟨1033934, by rfl⟩ : syracuseStep 5514317 = 2067869) B2067869
theorem B1288367 : Blo 570811 1288367 := bstep (se 1 (by rfl) ⟨966275, by rfl⟩ : syracuseStep 1288367 = 1932551) B1932551
theorem B1452937 : Blo 570811 1452937 := bstep (se 2 (by rfl) ⟨544851, by rfl⟩ : syracuseStep 1452937 = 1089703) B1089703
theorem B1289447 : Blo 570811 1289447 := bstep (se 1 (by rfl) ⟨967085, by rfl⟩ : syracuseStep 1289447 = 1934171) B1934171
theorem B8269289 : Blo 570811 8269289 := bstep (se 2 (by rfl) ⟨3100983, by rfl⟩ : syracuseStep 8269289 = 6201967) B6201967
theorem B1290239 : Blo 570811 1290239 := bstep (se 1 (by rfl) ⟨967679, by rfl⟩ : syracuseStep 1290239 = 1935359) B1935359
theorem B2438711 : Blo 570811 2438711 := bstep (se 1 (by rfl) ⟨1829033, by rfl⟩ : syracuseStep 2438711 = 3658067) B3658067
theorem B571483 : Blo 570811 571483 := bstep (se 1 (by rfl) ⟨428612, by rfl⟩ : syracuseStep 571483 = 857225) B857225
theorem B572863 : Blo 570811 572863 := bstep (se 1 (by rfl) ⟨429647, by rfl⟩ : syracuseStep 572863 = 859295) B859295
theorem B573287 : Blo 570811 573287 := bstep (se 1 (by rfl) ⟨429965, by rfl⟩ : syracuseStep 573287 = 859931) B859931
theorem B12271931 : Blo 570811 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B20070989 : Blo 570811 20070989 := bstep (se 3 (by rfl) ⟨3763310, by rfl⟩ : syracuseStep 20070989 = 7526621) B7526621
theorem B2903201 : Blo 570811 2903201 := bstep (se 2 (by rfl) ⟨1088700, by rfl⟩ : syracuseStep 2903201 = 2177401) B2177401
theorem B7327817 : Blo 570811 7327817 := bstep (se 2 (by rfl) ⟨2747931, by rfl⟩ : syracuseStep 7327817 = 5495863) B5495863
theorem B644863 : Blo 570811 644863 := bstep (se 1 (by rfl) ⟨483647, by rfl⟩ : syracuseStep 644863 = 967295) B967295
theorem B646591 : Blo 570811 646591 := bstep (se 1 (by rfl) ⟨484943, by rfl⟩ : syracuseStep 646591 = 969887) B969887
theorem B2452295 : Blo 570811 2452295 := bstep (se 1 (by rfl) ⟨1839221, by rfl⟩ : syracuseStep 2452295 = 3678443) B3678443
theorem B11793761 : Blo 570811 11793761 := bstep (se 2 (by rfl) ⟨4422660, by rfl⟩ : syracuseStep 11793761 = 8845321) B8845321
theorem B1635967 : Blo 570811 1635967 := bstep (se 1 (by rfl) ⟨1226975, by rfl⟩ : syracuseStep 1635967 = 2453951) B2453951
theorem B1374889 : Blo 570811 1374889 := bstep (se 2 (by rfl) ⟨515583, by rfl⟩ : syracuseStep 1374889 = 1031167) B1031167
theorem B1932281 : Blo 570811 1932281 := bstep (se 2 (by rfl) ⟨724605, by rfl⟩ : syracuseStep 1932281 = 1449211) B1449211
theorem B916895 : Blo 570811 916895 := bstep (se 1 (by rfl) ⟨687671, by rfl⟩ : syracuseStep 916895 = 1375343) B1375343
theorem B1935467 : Blo 570811 1935467 := bstep (se 1 (by rfl) ⟨1451600, by rfl⟩ : syracuseStep 1935467 = 2903201) B2903201
theorem B4885211 : Blo 570811 4885211 := bstep (se 1 (by rfl) ⟨3663908, by rfl⟩ : syracuseStep 4885211 = 7327817) B7327817
theorem B1837991 : Blo 570811 1837991 := bstep (se 1 (by rfl) ⟨1378493, by rfl⟩ : syracuseStep 1837991 = 2756987) B2756987
theorem B1937249 : Blo 570811 1937249 := bstep (se 2 (by rfl) ⟨726468, by rfl⟩ : syracuseStep 1937249 = 1452937) B1452937
theorem B857087 : Blo 570811 857087 := bstep (se 1 (by rfl) ⟨642815, by rfl⟩ : syracuseStep 857087 = 1285631) B1285631
theorem B1446943 : Blo 570811 1446943 := bstep (se 1 (by rfl) ⟨1085207, by rfl⟩ : syracuseStep 1446943 = 2170415) B2170415
theorem B62788769 : Blo 570811 62788769 := bstep (se 2 (by rfl) ⟨23545788, by rfl⟩ : syracuseStep 62788769 = 47091577) B47091577
theorem B3676211 : Blo 570811 3676211 := bstep (se 1 (by rfl) ⟨2757158, by rfl⟩ : syracuseStep 3676211 = 5514317) B5514317
theorem B858911 : Blo 570811 858911 := bstep (se 1 (by rfl) ⟨644183, by rfl⟩ : syracuseStep 858911 = 1288367) B1288367
theorem B859631 : Blo 570811 859631 := bstep (se 1 (by rfl) ⟨644723, by rfl⟩ : syracuseStep 859631 = 1289447) B1289447
theorem B5512859 : Blo 570811 5512859 := bstep (se 1 (by rfl) ⟨4134644, by rfl⟩ : syracuseStep 5512859 = 8269289) B8269289
theorem B859817 : Blo 570811 859817 := bstep (se 2 (by rfl) ⟨322431, by rfl⟩ : syracuseStep 859817 = 644863) B644863
theorem B860159 : Blo 570811 860159 := bstep (se 1 (by rfl) ⟨645119, by rfl⟩ : syracuseStep 860159 = 1290239) B1290239
theorem B862121 : Blo 570811 862121 := bstep (se 2 (by rfl) ⟨323295, by rfl⟩ : syracuseStep 862121 = 646591) B646591
theorem B1288187 : Blo 570811 1288187 := bstep (se 1 (by rfl) ⟨966140, by rfl⟩ : syracuseStep 1288187 = 1932281) B1932281
theorem B13380659 : Blo 570811 13380659 := bstep (se 1 (by rfl) ⟨10035494, by rfl⟩ : syracuseStep 13380659 = 20070989) B20070989
theorem B570847 : Blo 570811 570847 := bstep (se 1 (by rfl) ⟨428135, by rfl⟩ : syracuseStep 570847 = 856271) B856271
theorem B571303 : Blo 570811 571303 := bstep (se 1 (by rfl) ⟨428477, by rfl⟩ : syracuseStep 571303 = 856955) B856955
theorem B1226873 : Blo 570811 1226873 := bstep (se 2 (by rfl) ⟨460077, by rfl⟩ : syracuseStep 1226873 = 920155) B920155
theorem B4176031 : Blo 570811 4176031 := bstep (se 1 (by rfl) ⟨3132023, by rfl⟩ : syracuseStep 4176031 = 6264047) B6264047
theorem B572775 : Blo 570811 572775 := bstep (se 1 (by rfl) ⟨429581, by rfl⟩ : syracuseStep 572775 = 859163) B859163
theorem B2181289 : Blo 570811 2181289 := bstep (se 2 (by rfl) ⟨817983, by rfl⟩ : syracuseStep 2181289 = 1635967) B1635967
theorem B1625807 : Blo 570811 1625807 := bstep (se 1 (by rfl) ⟨1219355, by rfl⟩ : syracuseStep 1625807 = 2438711) B2438711
theorem B611263 : Blo 570811 611263 := bstep (se 1 (by rfl) ⟨458447, by rfl⟩ : syracuseStep 611263 = 916895) B916895
theorem B8181287 : Blo 570811 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B2907899 : Blo 570811 2907899 := bstep (se 1 (by rfl) ⟨2180924, by rfl⟩ : syracuseStep 2907899 = 4361849) B4361849
theorem B2451559 : Blo 570811 2451559 := bstep (se 1 (by rfl) ⟨1838669, by rfl⟩ : syracuseStep 2451559 = 3677339) B3677339
theorem B1634863 : Blo 570811 1634863 := bstep (se 1 (by rfl) ⟨1226147, by rfl⟩ : syracuseStep 1634863 = 2452295) B2452295
theorem B1833185 : Blo 570811 1833185 := bstep (se 2 (by rfl) ⟨687444, by rfl⟩ : syracuseStep 1833185 = 1374889) B1374889
theorem B7862507 : Blo 570811 7862507 := bstep (se 1 (by rfl) ⟨5896880, by rfl⟩ : syracuseStep 7862507 = 11793761) B11793761
theorem B1083871 : Blo 570811 1083871 := bstep (se 1 (by rfl) ⟨812903, by rfl⟩ : syracuseStep 1083871 = 1625807) B1625807
theorem B3675239 : Blo 570811 3675239 := bstep (se 1 (by rfl) ⟨2756429, by rfl⟩ : syracuseStep 3675239 = 5512859) B5512859
theorem B1938599 : Blo 570811 1938599 := bstep (se 1 (by rfl) ⟨1453949, by rfl⟩ : syracuseStep 1938599 = 2907899) B2907899
theorem B858791 : Blo 570811 858791 := bstep (se 1 (by rfl) ⟨644093, by rfl⟩ : syracuseStep 858791 = 1288187) B1288187
theorem B8920439 : Blo 570811 8920439 := bstep (se 1 (by rfl) ⟨6690329, by rfl⟩ : syracuseStep 8920439 = 13380659) B13380659
theorem B1222123 : Blo 570811 1222123 := bstep (se 1 (by rfl) ⟨916592, by rfl⟩ : syracuseStep 1222123 = 1833185) B1833185
theorem B1290311 : Blo 570811 1290311 := bstep (se 1 (by rfl) ⟨967733, by rfl⟩ : syracuseStep 1290311 = 1935467) B1935467
theorem B3256807 : Blo 570811 3256807 := bstep (se 1 (by rfl) ⟨2442605, by rfl⟩ : syracuseStep 3256807 = 4885211) B4885211
theorem B1291499 : Blo 570811 1291499 := bstep (se 1 (by rfl) ⟨968624, by rfl⟩ : syracuseStep 1291499 = 1937249) B1937249
theorem B571391 : Blo 570811 571391 := bstep (se 1 (by rfl) ⟨428543, by rfl⟩ : syracuseStep 571391 = 857087) B857087
theorem B41859179 : Blo 570811 41859179 := bstep (se 1 (by rfl) ⟨31394384, by rfl⟩ : syracuseStep 41859179 = 62788769) B62788769
theorem B5454191 : Blo 570811 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B572607 : Blo 570811 572607 := bstep (se 1 (by rfl) ⟨429455, by rfl⟩ : syracuseStep 572607 = 858911) B858911
theorem B573087 : Blo 570811 573087 := bstep (se 1 (by rfl) ⟨429815, by rfl⟩ : syracuseStep 573087 = 859631) B859631
theorem B573211 : Blo 570811 573211 := bstep (se 1 (by rfl) ⟨429908, by rfl⟩ : syracuseStep 573211 = 859817) B859817
theorem B573439 : Blo 570811 573439 := bstep (se 1 (by rfl) ⟨430079, by rfl⟩ : syracuseStep 573439 = 860159) B860159
theorem B2179817 : Blo 570811 2179817 := bstep (se 2 (by rfl) ⟨817431, by rfl⟩ : syracuseStep 2179817 = 1634863) B1634863
theorem B574747 : Blo 570811 574747 := bstep (se 1 (by rfl) ⟨431060, by rfl⟩ : syracuseStep 574747 = 862121) B862121
theorem B4901309 : Blo 570811 4901309 := bstep (se 3 (by rfl) ⟨918995, by rfl⟩ : syracuseStep 4901309 = 1837991) B1837991
theorem B3268745 : Blo 570811 3268745 := bstep (se 2 (by rfl) ⟨1225779, by rfl⟩ : syracuseStep 3268745 = 2451559) B2451559
theorem B2908385 : Blo 570811 2908385 := bstep (se 2 (by rfl) ⟨1090644, by rfl⟩ : syracuseStep 2908385 = 2181289) B2181289
theorem B2450807 : Blo 570811 2450807 := bstep (se 1 (by rfl) ⟨1838105, by rfl⟩ : syracuseStep 2450807 = 3676211) B3676211
theorem B3271661 : Blo 570811 3271661 := bstep (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) B1226873
theorem B815017 : Blo 570811 815017 := bstep (se 2 (by rfl) ⟨305631, by rfl⟩ : syracuseStep 815017 = 611263) B611263
theorem B1929257 : Blo 570811 1929257 := bstep (se 2 (by rfl) ⟨723471, by rfl⟩ : syracuseStep 1929257 = 1446943) B1446943
theorem B5568041 : Blo 570811 5568041 := bstep (se 2 (by rfl) ⟨2088015, by rfl⟩ : syracuseStep 5568041 = 4176031) B4176031
theorem B5241671 : Blo 570811 5241671 := bstep (se 1 (by rfl) ⟨3931253, by rfl⟩ : syracuseStep 5241671 = 7862507) B7862507
theorem B1445161 : Blo 570811 1445161 := bstep (se 2 (by rfl) ⟨541935, by rfl⟩ : syracuseStep 1445161 = 1083871) B1083871
theorem B14848109 : Blo 570811 14848109 := bstep (se 3 (by rfl) ⟨2784020, by rfl⟩ : syracuseStep 14848109 = 5568041) B5568041
theorem B1086689 : Blo 570811 1086689 := bstep (se 2 (by rfl) ⟨407508, by rfl⟩ : syracuseStep 1086689 = 815017) B815017
theorem B1938923 : Blo 570811 1938923 := bstep (se 1 (by rfl) ⟨1454192, by rfl⟩ : syracuseStep 1938923 = 2908385) B2908385
theorem B1286171 : Blo 570811 1286171 := bstep (se 1 (by rfl) ⟨964628, by rfl⟩ : syracuseStep 1286171 = 1929257) B1929257
theorem B860207 : Blo 570811 860207 := bstep (se 1 (by rfl) ⟨645155, by rfl⟩ : syracuseStep 860207 = 1290311) B1290311
theorem B860999 : Blo 570811 860999 := bstep (se 1 (by rfl) ⟨645749, by rfl⟩ : syracuseStep 860999 = 1291499) B1291499
theorem B1453211 : Blo 570811 1453211 := bstep (se 1 (by rfl) ⟨1089908, by rfl⟩ : syracuseStep 1453211 = 2179817) B2179817
theorem B1292399 : Blo 570811 1292399 := bstep (se 1 (by rfl) ⟨969299, by rfl⟩ : syracuseStep 1292399 = 1938599) B1938599
theorem B572527 : Blo 570811 572527 := bstep (se 1 (by rfl) ⟨429395, by rfl⟩ : syracuseStep 572527 = 858791) B858791
theorem B5946959 : Blo 570811 5946959 := bstep (se 1 (by rfl) ⟨4460219, by rfl⟩ : syracuseStep 5946959 = 8920439) B8920439
theorem B2179163 : Blo 570811 2179163 := bstep (se 1 (by rfl) ⟨1634372, by rfl⟩ : syracuseStep 2179163 = 3268745) B3268745
theorem B4342409 : Blo 570811 4342409 := bstep (se 2 (by rfl) ⟨1628403, by rfl⟩ : syracuseStep 4342409 = 3256807) B3256807
theorem B2181107 : Blo 570811 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B27906119 : Blo 570811 27906119 := bstep (se 1 (by rfl) ⟨20929589, by rfl⟩ : syracuseStep 27906119 = 41859179) B41859179
theorem B3494447 : Blo 570811 3494447 := bstep (se 1 (by rfl) ⟨2620835, by rfl⟩ : syracuseStep 3494447 = 5241671) B5241671
theorem B3267539 : Blo 570811 3267539 := bstep (se 1 (by rfl) ⟨2450654, by rfl⟩ : syracuseStep 3267539 = 4901309) B4901309
theorem B1629497 : Blo 570811 1629497 := bstep (se 2 (by rfl) ⟨611061, by rfl⟩ : syracuseStep 1629497 = 1222123) B1222123
theorem B2450159 : Blo 570811 2450159 := bstep (se 1 (by rfl) ⟨1837619, by rfl⟩ : syracuseStep 2450159 = 3675239) B3675239
theorem B1633871 : Blo 570811 1633871 := bstep (se 1 (by rfl) ⟨1225403, by rfl⟩ : syracuseStep 1633871 = 2450807) B2450807
theorem B3636127 : Blo 570811 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B9898739 : Blo 570811 9898739 := bstep (se 1 (by rfl) ⟨7424054, by rfl⟩ : syracuseStep 9898739 = 14848109) B14848109
theorem B2329631 : Blo 570811 2329631 := bstep (se 1 (by rfl) ⟨1747223, by rfl⟩ : syracuseStep 2329631 = 3494447) B3494447
theorem B724459 : Blo 570811 724459 := bstep (se 1 (by rfl) ⟨543344, by rfl⟩ : syracuseStep 724459 = 1086689) B1086689
theorem B857447 : Blo 570811 857447 := bstep (se 1 (by rfl) ⟨643085, by rfl⟩ : syracuseStep 857447 = 1286171) B1286171
theorem B861599 : Blo 570811 861599 := bstep (se 1 (by rfl) ⟨646199, by rfl⟩ : syracuseStep 861599 = 1292399) B1292399
theorem B1452775 : Blo 570811 1452775 := bstep (se 1 (by rfl) ⟨1089581, by rfl⟩ : syracuseStep 1452775 = 2179163) B2179163
theorem B2894939 : Blo 570811 2894939 := bstep (se 1 (by rfl) ⟨2171204, by rfl⟩ : syracuseStep 2894939 = 4342409) B4342409
theorem B1454071 : Blo 570811 1454071 := bstep (se 1 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 1454071 = 2181107) B2181107
theorem B1292615 : Blo 570811 1292615 := bstep (se 1 (by rfl) ⟨969461, by rfl⟩ : syracuseStep 1292615 = 1938923) B1938923
theorem B2178359 : Blo 570811 2178359 := bstep (se 1 (by rfl) ⟨1633769, by rfl⟩ : syracuseStep 2178359 = 3267539) B3267539
theorem B573471 : Blo 570811 573471 := bstep (se 1 (by rfl) ⟨430103, by rfl⟩ : syracuseStep 573471 = 860207) B860207
theorem B573999 : Blo 570811 573999 := bstep (se 1 (by rfl) ⟨430499, by rfl⟩ : syracuseStep 573999 = 860999) B860999
theorem B968807 : Blo 570811 968807 := bstep (se 1 (by rfl) ⟨726605, by rfl⟩ : syracuseStep 968807 = 1453211) B1453211
theorem B4345325 : Blo 570811 4345325 := bstep (se 3 (by rfl) ⟨814748, by rfl⟩ : syracuseStep 4345325 = 1629497) B1629497
theorem B18604079 : Blo 570811 18604079 := bstep (se 1 (by rfl) ⟨13953059, by rfl⟩ : syracuseStep 18604079 = 27906119) B27906119
theorem B1926881 : Blo 570811 1926881 := bstep (se 2 (by rfl) ⟨722580, by rfl⟩ : syracuseStep 1926881 = 1445161) B1445161
theorem B1633439 : Blo 570811 1633439 := bstep (se 1 (by rfl) ⟨1225079, by rfl⟩ : syracuseStep 1633439 = 2450159) B2450159
theorem B4848169 : Blo 570811 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B4356989 : Blo 570811 4356989 := bstep (se 3 (by rfl) ⟨816935, by rfl⟩ : syracuseStep 4356989 = 1633871) B1633871
theorem B3964639 : Blo 570811 3964639 := bstep (se 1 (by rfl) ⟨2973479, by rfl⟩ : syracuseStep 3964639 = 5946959) B5946959
theorem B1937033 : Blo 570811 1937033 := bstep (se 2 (by rfl) ⟨726387, by rfl⟩ : syracuseStep 1937033 = 1452775) B1452775
theorem B1938761 : Blo 570811 1938761 := bstep (se 2 (by rfl) ⟨727035, by rfl⟩ : syracuseStep 1938761 = 1454071) B1454071
theorem B1284587 : Blo 570811 1284587 := bstep (se 1 (by rfl) ⟨963440, by rfl⟩ : syracuseStep 1284587 = 1926881) B1926881
theorem B1088959 : Blo 570811 1088959 := bstep (se 1 (by rfl) ⟨816719, by rfl⟩ : syracuseStep 1088959 = 1633439) B1633439
theorem B6464225 : Blo 570811 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B861743 : Blo 570811 861743 := bstep (se 1 (by rfl) ⟨646307, by rfl⟩ : syracuseStep 861743 = 1292615) B1292615
theorem B1452239 : Blo 570811 1452239 := bstep (se 1 (by rfl) ⟨1089179, by rfl⟩ : syracuseStep 1452239 = 2178359) B2178359
theorem B5286185 : Blo 570811 5286185 := bstep (se 2 (by rfl) ⟨1982319, by rfl⟩ : syracuseStep 5286185 = 3964639) B3964639
theorem B6599159 : Blo 570811 6599159 := bstep (se 1 (by rfl) ⟨4949369, by rfl⟩ : syracuseStep 6599159 = 9898739) B9898739
theorem B1553087 : Blo 570811 1553087 := bstep (se 1 (by rfl) ⟨1164815, by rfl⟩ : syracuseStep 1553087 = 2329631) B2329631
theorem B2896883 : Blo 570811 2896883 := bstep (se 1 (by rfl) ⟨2172662, by rfl⟩ : syracuseStep 2896883 = 4345325) B4345325
theorem B571631 : Blo 570811 571631 := bstep (se 1 (by rfl) ⟨428723, by rfl⟩ : syracuseStep 571631 = 857447) B857447
theorem B965945 : Blo 570811 965945 := bstep (se 2 (by rfl) ⟨362229, by rfl⟩ : syracuseStep 965945 = 724459) B724459
theorem B12402719 : Blo 570811 12402719 := bstep (se 1 (by rfl) ⟨9302039, by rfl⟩ : syracuseStep 12402719 = 18604079) B18604079
theorem B574399 : Blo 570811 574399 := bstep (se 1 (by rfl) ⟨430799, by rfl⟩ : syracuseStep 574399 = 861599) B861599
theorem B2904659 : Blo 570811 2904659 := bstep (se 1 (by rfl) ⟨2178494, by rfl⟩ : syracuseStep 2904659 = 4356989) B4356989
theorem B645871 : Blo 570811 645871 := bstep (se 1 (by rfl) ⟨484403, by rfl⟩ : syracuseStep 645871 = 968807) B968807
theorem B1929959 : Blo 570811 1929959 := bstep (se 1 (by rfl) ⟨1447469, by rfl⟩ : syracuseStep 1929959 = 2894939) B2894939
theorem B17237933 : Blo 570811 17237933 := bstep (se 3 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 17237933 = 6464225) B6464225
theorem B1936439 : Blo 570811 1936439 := bstep (se 1 (by rfl) ⟨1452329, by rfl⟩ : syracuseStep 1936439 = 2904659) B2904659
theorem B856391 : Blo 570811 856391 := bstep (se 1 (by rfl) ⟨642293, by rfl⟩ : syracuseStep 856391 = 1284587) B1284587
theorem B4399439 : Blo 570811 4399439 := bstep (se 1 (by rfl) ⟨3299579, by rfl⟩ : syracuseStep 4399439 = 6599159) B6599159
theorem B1286639 : Blo 570811 1286639 := bstep (se 1 (by rfl) ⟨964979, by rfl⟩ : syracuseStep 1286639 = 1929959) B1929959
theorem B861161 : Blo 570811 861161 := bstep (se 2 (by rfl) ⟨322935, by rfl⟩ : syracuseStep 861161 = 645871) B645871
theorem B1451945 : Blo 570811 1451945 := bstep (se 2 (by rfl) ⟨544479, by rfl⟩ : syracuseStep 1451945 = 1088959) B1088959
theorem B8268479 : Blo 570811 8268479 := bstep (se 1 (by rfl) ⟨6201359, by rfl⟩ : syracuseStep 8268479 = 12402719) B12402719
theorem B1291355 : Blo 570811 1291355 := bstep (se 1 (by rfl) ⟨968516, by rfl⟩ : syracuseStep 1291355 = 1937033) B1937033
theorem B1292507 : Blo 570811 1292507 := bstep (se 1 (by rfl) ⟨969380, by rfl⟩ : syracuseStep 1292507 = 1938761) B1938761
theorem B574495 : Blo 570811 574495 := bstep (se 1 (by rfl) ⟨430871, by rfl⟩ : syracuseStep 574495 = 861743) B861743
theorem B968159 : Blo 570811 968159 := bstep (se 1 (by rfl) ⟨726119, by rfl⟩ : syracuseStep 968159 = 1452239) B1452239
theorem B3524123 : Blo 570811 3524123 := bstep (se 1 (by rfl) ⟨2643092, by rfl⟩ : syracuseStep 3524123 = 5286185) B5286185
theorem B1035391 : Blo 570811 1035391 := bstep (se 1 (by rfl) ⟨776543, by rfl⟩ : syracuseStep 1035391 = 1553087) B1553087
theorem B643963 : Blo 570811 643963 := bstep (se 1 (by rfl) ⟨482972, by rfl⟩ : syracuseStep 643963 = 965945) B965945
theorem B1931255 : Blo 570811 1931255 := bstep (se 1 (by rfl) ⟨1448441, by rfl⟩ : syracuseStep 1931255 = 2896883) B2896883
theorem B46927349 : Blo 570811 46927349 := bstep (se 5 (by rfl) ⟨2199719, by rfl⟩ : syracuseStep 46927349 = 4399439) B4399439
theorem B1380521 : Blo 570811 1380521 := bstep (se 2 (by rfl) ⟨517695, by rfl⟩ : syracuseStep 1380521 = 1035391) B1035391
theorem B857759 : Blo 570811 857759 := bstep (se 1 (by rfl) ⟨643319, by rfl⟩ : syracuseStep 857759 = 1286639) B1286639
theorem B858617 : Blo 570811 858617 := bstep (se 2 (by rfl) ⟨321981, by rfl⟩ : syracuseStep 858617 = 643963) B643963
theorem B5512319 : Blo 570811 5512319 := bstep (se 1 (by rfl) ⟨4134239, by rfl⟩ : syracuseStep 5512319 = 8268479) B8268479
theorem B860903 : Blo 570811 860903 := bstep (se 1 (by rfl) ⟨645677, by rfl⟩ : syracuseStep 860903 = 1291355) B1291355
theorem B1287503 : Blo 570811 1287503 := bstep (se 1 (by rfl) ⟨965627, by rfl⟩ : syracuseStep 1287503 = 1931255) B1931255
theorem B861671 : Blo 570811 861671 := bstep (se 1 (by rfl) ⟨646253, by rfl⟩ : syracuseStep 861671 = 1292507) B1292507
theorem B1290959 : Blo 570811 1290959 := bstep (se 1 (by rfl) ⟨968219, by rfl⟩ : syracuseStep 1290959 = 1936439) B1936439
theorem B570927 : Blo 570811 570927 := bstep (se 1 (by rfl) ⟨428195, by rfl⟩ : syracuseStep 570927 = 856391) B856391
theorem B574107 : Blo 570811 574107 := bstep (se 1 (by rfl) ⟨430580, by rfl⟩ : syracuseStep 574107 = 861161) B861161
theorem B967963 : Blo 570811 967963 := bstep (se 1 (by rfl) ⟨725972, by rfl⟩ : syracuseStep 967963 = 1451945) B1451945
theorem B645439 : Blo 570811 645439 := bstep (se 1 (by rfl) ⟨484079, by rfl⟩ : syracuseStep 645439 = 968159) B968159
theorem B2349415 : Blo 570811 2349415 := bstep (se 1 (by rfl) ⟨1762061, by rfl⟩ : syracuseStep 2349415 = 3524123) B3524123
theorem B11491955 : Blo 570811 11491955 := bstep (se 1 (by rfl) ⟨8618966, by rfl⟩ : syracuseStep 11491955 = 17237933) B17237933
theorem B3674879 : Blo 570811 3674879 := bstep (se 1 (by rfl) ⟨2756159, by rfl⟩ : syracuseStep 3674879 = 5512319) B5512319
theorem B858335 : Blo 570811 858335 := bstep (se 1 (by rfl) ⟨643751, by rfl⟩ : syracuseStep 858335 = 1287503) B1287503
theorem B860585 : Blo 570811 860585 := bstep (se 2 (by rfl) ⟨322719, by rfl⟩ : syracuseStep 860585 = 645439) B645439
theorem B860639 : Blo 570811 860639 := bstep (se 1 (by rfl) ⟨645479, by rfl⟩ : syracuseStep 860639 = 1290959) B1290959
theorem B3681389 : Blo 570811 3681389 := bstep (se 3 (by rfl) ⟨690260, by rfl⟩ : syracuseStep 3681389 = 1380521) B1380521
theorem B1290617 : Blo 570811 1290617 := bstep (se 2 (by rfl) ⟨483981, by rfl⟩ : syracuseStep 1290617 = 967963) B967963
theorem B12530213 : Blo 570811 12530213 := bstep (se 4 (by rfl) ⟨1174707, by rfl⟩ : syracuseStep 12530213 = 2349415) B2349415
theorem B571839 : Blo 570811 571839 := bstep (se 1 (by rfl) ⟨428879, by rfl⟩ : syracuseStep 571839 = 857759) B857759
theorem B572411 : Blo 570811 572411 := bstep (se 1 (by rfl) ⟨429308, by rfl⟩ : syracuseStep 572411 = 858617) B858617
theorem B573935 : Blo 570811 573935 := bstep (se 1 (by rfl) ⟨430451, by rfl⟩ : syracuseStep 573935 = 860903) B860903
theorem B574447 : Blo 570811 574447 := bstep (se 1 (by rfl) ⟨430835, by rfl⟩ : syracuseStep 574447 = 861671) B861671
theorem B31284899 : Blo 570811 31284899 := bstep (se 1 (by rfl) ⟨23463674, by rfl⟩ : syracuseStep 31284899 = 46927349) B46927349
theorem B7661303 : Blo 570811 7661303 := bstep (se 1 (by rfl) ⟨5745977, by rfl⟩ : syracuseStep 7661303 = 11491955) B11491955
theorem B860411 : Blo 570811 860411 := bstep (se 1 (by rfl) ⟨645308, by rfl⟩ : syracuseStep 860411 = 1290617) B1290617
theorem B572223 : Blo 570811 572223 := bstep (se 1 (by rfl) ⟨429167, by rfl⟩ : syracuseStep 572223 = 858335) B858335
theorem B20856599 : Blo 570811 20856599 := bstep (se 1 (by rfl) ⟨15642449, by rfl⟩ : syracuseStep 20856599 = 31284899) B31284899
theorem B573723 : Blo 570811 573723 := bstep (se 1 (by rfl) ⟨430292, by rfl⟩ : syracuseStep 573723 = 860585) B860585
theorem B573759 : Blo 570811 573759 := bstep (se 1 (by rfl) ⟨430319, by rfl⟩ : syracuseStep 573759 = 860639) B860639
theorem B2449919 : Blo 570811 2449919 := bstep (se 1 (by rfl) ⟨1837439, by rfl⟩ : syracuseStep 2449919 = 3674879) B3674879
theorem B5107535 : Blo 570811 5107535 := bstep (se 1 (by rfl) ⟨3830651, by rfl⟩ : syracuseStep 5107535 = 7661303) B7661303
theorem B2454259 : Blo 570811 2454259 := bstep (se 1 (by rfl) ⟨1840694, by rfl⟩ : syracuseStep 2454259 = 3681389) B3681389
theorem B8353475 : Blo 570811 8353475 := bstep (se 1 (by rfl) ⟨6265106, by rfl⟩ : syracuseStep 8353475 = 12530213) B12530213
theorem B13904399 : Blo 570811 13904399 := bstep (se 1 (by rfl) ⟨10428299, by rfl⟩ : syracuseStep 13904399 = 20856599) B20856599
theorem B573607 : Blo 570811 573607 := bstep (se 1 (by rfl) ⟨430205, by rfl⟩ : syracuseStep 573607 = 860411) B860411
theorem B1633279 : Blo 570811 1633279 := bstep (se 1 (by rfl) ⟨1224959, by rfl⟩ : syracuseStep 1633279 = 2449919) B2449919
theorem B3272345 : Blo 570811 3272345 := bstep (se 2 (by rfl) ⟨1227129, by rfl⟩ : syracuseStep 3272345 = 2454259) B2454259
theorem B3405023 : Blo 570811 3405023 := bstep (se 1 (by rfl) ⟨2553767, by rfl⟩ : syracuseStep 3405023 = 5107535) B5107535
theorem B5568983 : Blo 570811 5568983 := bstep (se 1 (by rfl) ⟨4176737, by rfl⟩ : syracuseStep 5568983 = 8353475) B8353475
theorem B2270015 : Blo 570811 2270015 := bstep (se 1 (by rfl) ⟨1702511, by rfl⟩ : syracuseStep 2270015 = 3405023) B3405023
theorem B3712655 : Blo 570811 3712655 := bstep (se 1 (by rfl) ⟨2784491, by rfl⟩ : syracuseStep 3712655 = 5568983) B5568983
theorem B2177705 : Blo 570811 2177705 := bstep (se 2 (by rfl) ⟨816639, by rfl⟩ : syracuseStep 2177705 = 1633279) B1633279
theorem B37078397 : Blo 570811 37078397 := bstep (se 3 (by rfl) ⟨6952199, by rfl⟩ : syracuseStep 37078397 = 13904399) B13904399
theorem B2181563 : Blo 570811 2181563 := bstep (se 1 (by rfl) ⟨1636172, by rfl⟩ : syracuseStep 2181563 = 3272345) B3272345
theorem B9900413 : Blo 570811 9900413 := bstep (se 3 (by rfl) ⟨1856327, by rfl⟩ : syracuseStep 9900413 = 3712655) B3712655
theorem B1513343 : Blo 570811 1513343 := bstep (se 1 (by rfl) ⟨1135007, by rfl⟩ : syracuseStep 1513343 = 2270015) B2270015
theorem B1451803 : Blo 570811 1451803 := bstep (se 1 (by rfl) ⟨1088852, by rfl⟩ : syracuseStep 1451803 = 2177705) B2177705
theorem B24718931 : Blo 570811 24718931 := bstep (se 1 (by rfl) ⟨18539198, by rfl⟩ : syracuseStep 24718931 = 37078397) B37078397
theorem B1454375 : Blo 570811 1454375 := bstep (se 1 (by rfl) ⟨1090781, by rfl⟩ : syracuseStep 1454375 = 2181563) B2181563
theorem B1935737 : Blo 570811 1935737 := bstep (se 2 (by rfl) ⟨725901, by rfl⟩ : syracuseStep 1935737 = 1451803) B1451803
theorem B4035581 : Blo 570811 4035581 := bstep (se 3 (by rfl) ⟨756671, by rfl⟩ : syracuseStep 4035581 = 1513343) B1513343
theorem B6600275 : Blo 570811 6600275 := bstep (se 1 (by rfl) ⟨4950206, by rfl⟩ : syracuseStep 6600275 = 9900413) B9900413
theorem B969583 : Blo 570811 969583 := bstep (se 1 (by rfl) ⟨727187, by rfl⟩ : syracuseStep 969583 = 1454375) B1454375
theorem B16479287 : Blo 570811 16479287 := bstep (se 1 (by rfl) ⟨12359465, by rfl⟩ : syracuseStep 16479287 = 24718931) B24718931
theorem B2690387 : Blo 570811 2690387 := bstep (se 1 (by rfl) ⟨2017790, by rfl⟩ : syracuseStep 2690387 = 4035581) B4035581
theorem B10986191 : Blo 570811 10986191 := bstep (se 1 (by rfl) ⟨8239643, by rfl⟩ : syracuseStep 10986191 = 16479287) B16479287
theorem B4400183 : Blo 570811 4400183 := bstep (se 1 (by rfl) ⟨3300137, by rfl⟩ : syracuseStep 4400183 = 6600275) B6600275
theorem B1290491 : Blo 570811 1290491 := bstep (se 1 (by rfl) ⟨967868, by rfl⟩ : syracuseStep 1290491 = 1935737) B1935737
theorem B1292777 : Blo 570811 1292777 := bstep (se 2 (by rfl) ⟨484791, by rfl⟩ : syracuseStep 1292777 = 969583) B969583
theorem B860327 : Blo 570811 860327 := bstep (se 1 (by rfl) ⟨645245, by rfl⟩ : syracuseStep 860327 = 1290491) B1290491
theorem B861851 : Blo 570811 861851 := bstep (se 1 (by rfl) ⟨646388, by rfl⟩ : syracuseStep 861851 = 1292777) B1292777
theorem B7324127 : Blo 570811 7324127 := bstep (se 1 (by rfl) ⟨5493095, by rfl⟩ : syracuseStep 7324127 = 10986191) B10986191
theorem B2933455 : Blo 570811 2933455 := bstep (se 1 (by rfl) ⟨2200091, by rfl⟩ : syracuseStep 2933455 = 4400183) B4400183
theorem B1793591 : Blo 570811 1793591 := bstep (se 1 (by rfl) ⟨1345193, by rfl⟩ : syracuseStep 1793591 = 2690387) B2690387
theorem B4882751 : Blo 570811 4882751 := bstep (se 1 (by rfl) ⟨3662063, by rfl⟩ : syracuseStep 4882751 = 7324127) B7324127
theorem B3911273 : Blo 570811 3911273 := bstep (se 2 (by rfl) ⟨1466727, by rfl⟩ : syracuseStep 3911273 = 2933455) B2933455
theorem B1195727 : Blo 570811 1195727 := bstep (se 1 (by rfl) ⟨896795, by rfl⟩ : syracuseStep 1195727 = 1793591) B1793591
theorem B573551 : Blo 570811 573551 := bstep (se 1 (by rfl) ⟨430163, by rfl⟩ : syracuseStep 573551 = 860327) B860327
theorem B574567 : Blo 570811 574567 := bstep (se 1 (by rfl) ⟨430925, by rfl⟩ : syracuseStep 574567 = 861851) B861851
theorem B3188605 : Blo 570811 3188605 := bstep (se 3 (by rfl) ⟨597863, by rfl⟩ : syracuseStep 3188605 = 1195727) B1195727
theorem B3255167 : Blo 570811 3255167 := bstep (se 1 (by rfl) ⟨2441375, by rfl⟩ : syracuseStep 3255167 = 4882751) B4882751
theorem B2607515 : Blo 570811 2607515 := bstep (se 1 (by rfl) ⟨1955636, by rfl⟩ : syracuseStep 2607515 = 3911273) B3911273
theorem B1738343 : Blo 570811 1738343 := bstep (se 1 (by rfl) ⟨1303757, by rfl⟩ : syracuseStep 1738343 = 2607515) B2607515
theorem B2170111 : Blo 570811 2170111 := bstep (se 1 (by rfl) ⟨1627583, by rfl⟩ : syracuseStep 2170111 = 3255167) B3255167
theorem B4251473 : Blo 570811 4251473 := bstep (se 2 (by rfl) ⟨1594302, by rfl⟩ : syracuseStep 4251473 = 3188605) B3188605
theorem B2893481 : Blo 570811 2893481 := bstep (se 2 (by rfl) ⟨1085055, by rfl⟩ : syracuseStep 2893481 = 2170111) B2170111
theorem B1158895 : Blo 570811 1158895 := bstep (se 1 (by rfl) ⟨869171, by rfl⟩ : syracuseStep 1158895 = 1738343) B1738343
theorem B2834315 : Blo 570811 2834315 := bstep (se 1 (by rfl) ⟨2125736, by rfl⟩ : syracuseStep 2834315 = 4251473) B4251473
theorem B1545193 : Blo 570811 1545193 := bstep (se 2 (by rfl) ⟨579447, by rfl⟩ : syracuseStep 1545193 = 1158895) B1158895
theorem B1889543 : Blo 570811 1889543 := bstep (se 1 (by rfl) ⟨1417157, by rfl⟩ : syracuseStep 1889543 = 2834315) B2834315
theorem B1928987 : Blo 570811 1928987 := bstep (se 1 (by rfl) ⟨1446740, by rfl⟩ : syracuseStep 1928987 = 2893481) B2893481
theorem B1285991 : Blo 570811 1285991 := bstep (se 1 (by rfl) ⟨964493, by rfl⟩ : syracuseStep 1285991 = 1928987) B1928987
theorem B1259695 : Blo 570811 1259695 := bstep (se 1 (by rfl) ⟨944771, by rfl⟩ : syracuseStep 1259695 = 1889543) B1889543
theorem B2060257 : Blo 570811 2060257 := bstep (se 2 (by rfl) ⟨772596, by rfl⟩ : syracuseStep 2060257 = 1545193) B1545193
theorem B6718373 : Blo 570811 6718373 := bstep (se 4 (by rfl) ⟨629847, by rfl⟩ : syracuseStep 6718373 = 1259695) B1259695
theorem B857327 : Blo 570811 857327 := bstep (se 1 (by rfl) ⟨642995, by rfl⟩ : syracuseStep 857327 = 1285991) B1285991
theorem B2747009 : Blo 570811 2747009 := bstep (se 2 (by rfl) ⟨1030128, by rfl⟩ : syracuseStep 2747009 = 2060257) B2060257
theorem B571551 : Blo 570811 571551 := bstep (se 1 (by rfl) ⟨428663, by rfl⟩ : syracuseStep 571551 = 857327) B857327
theorem B4478915 : Blo 570811 4478915 := bstep (se 1 (by rfl) ⟨3359186, by rfl⟩ : syracuseStep 4478915 = 6718373) B6718373
theorem B1831339 : Blo 570811 1831339 := bstep (se 1 (by rfl) ⟨1373504, by rfl⟩ : syracuseStep 1831339 = 2747009) B2747009
theorem B9767141 : Blo 570811 9767141 := bstep (se 4 (by rfl) ⟨915669, by rfl⟩ : syracuseStep 9767141 = 1831339) B1831339
theorem B11943773 : Blo 570811 11943773 := bstep (se 3 (by rfl) ⟨2239457, by rfl⟩ : syracuseStep 11943773 = 4478915) B4478915
theorem B6511427 : Blo 570811 6511427 := bstep (se 1 (by rfl) ⟨4883570, by rfl⟩ : syracuseStep 6511427 = 9767141) B9767141
theorem B7962515 : Blo 570811 7962515 := bstep (se 1 (by rfl) ⟨5971886, by rfl⟩ : syracuseStep 7962515 = 11943773) B11943773
theorem B4340951 : Blo 570811 4340951 := bstep (se 1 (by rfl) ⟨3255713, by rfl⟩ : syracuseStep 4340951 = 6511427) B6511427
theorem B5308343 : Blo 570811 5308343 := bstep (se 1 (by rfl) ⟨3981257, by rfl⟩ : syracuseStep 5308343 = 7962515) B7962515
theorem B2893967 : Blo 570811 2893967 := bstep (se 1 (by rfl) ⟨2170475, by rfl⟩ : syracuseStep 2893967 = 4340951) B4340951
theorem B3538895 : Blo 570811 3538895 := bstep (se 1 (by rfl) ⟨2654171, by rfl⟩ : syracuseStep 3538895 = 5308343) B5308343
theorem B1929311 : Blo 570811 1929311 := bstep (se 1 (by rfl) ⟨1446983, by rfl⟩ : syracuseStep 1929311 = 2893967) B2893967
theorem B37748213 : Blo 570811 37748213 := bstep (se 5 (by rfl) ⟨1769447, by rfl⟩ : syracuseStep 37748213 = 3538895) B3538895
theorem B1286207 : Blo 570811 1286207 := bstep (se 1 (by rfl) ⟨964655, by rfl⟩ : syracuseStep 1286207 = 1929311) B1929311
theorem B25165475 : Blo 570811 25165475 := bstep (se 1 (by rfl) ⟨18874106, by rfl⟩ : syracuseStep 25165475 = 37748213) B37748213
theorem B857471 : Blo 570811 857471 := bstep (se 1 (by rfl) ⟨643103, by rfl⟩ : syracuseStep 857471 = 1286207) B1286207
theorem B16776983 : Blo 570811 16776983 := bstep (se 1 (by rfl) ⟨12582737, by rfl⟩ : syracuseStep 16776983 = 25165475) B25165475
theorem B11184655 : Blo 570811 11184655 := bstep (se 1 (by rfl) ⟨8388491, by rfl⟩ : syracuseStep 11184655 = 16776983) B16776983
theorem B571647 : Blo 570811 571647 := bstep (se 1 (by rfl) ⟨428735, by rfl⟩ : syracuseStep 571647 = 857471) B857471
theorem B14912873 : Blo 570811 14912873 := bstep (se 2 (by rfl) ⟨5592327, by rfl⟩ : syracuseStep 14912873 = 11184655) B11184655
theorem B9941915 : Blo 570811 9941915 := bstep (se 1 (by rfl) ⟨7456436, by rfl⟩ : syracuseStep 9941915 = 14912873) B14912873
theorem B6627943 : Blo 570811 6627943 := bstep (se 1 (by rfl) ⟨4970957, by rfl⟩ : syracuseStep 6627943 = 9941915) B9941915
theorem B8837257 : Blo 570811 8837257 := bstep (se 2 (by rfl) ⟨3313971, by rfl⟩ : syracuseStep 8837257 = 6627943) B6627943
theorem B11783009 : Blo 570811 11783009 := bstep (se 2 (by rfl) ⟨4418628, by rfl⟩ : syracuseStep 11783009 = 8837257) B8837257
theorem B7855339 : Blo 570811 7855339 := bstep (se 1 (by rfl) ⟨5891504, by rfl⟩ : syracuseStep 7855339 = 11783009) B11783009
theorem B10473785 : Blo 570811 10473785 := bstep (se 2 (by rfl) ⟨3927669, by rfl⟩ : syracuseStep 10473785 = 7855339) B7855339
theorem B6982523 : Blo 570811 6982523 := bstep (se 1 (by rfl) ⟨5236892, by rfl⟩ : syracuseStep 6982523 = 10473785) B10473785
theorem B4655015 : Blo 570811 4655015 := bstep (se 1 (by rfl) ⟨3491261, by rfl⟩ : syracuseStep 4655015 = 6982523) B6982523
theorem B3103343 : Blo 570811 3103343 := bstep (se 1 (by rfl) ⟨2327507, by rfl⟩ : syracuseStep 3103343 = 4655015) B4655015
theorem B2068895 : Blo 570811 2068895 := bstep (se 1 (by rfl) ⟨1551671, by rfl⟩ : syracuseStep 2068895 = 3103343) B3103343
theorem B1379263 : Blo 570811 1379263 := bstep (se 1 (by rfl) ⟨1034447, by rfl⟩ : syracuseStep 1379263 = 2068895) B2068895
theorem B1839017 : Blo 570811 1839017 := bstep (se 2 (by rfl) ⟨689631, by rfl⟩ : syracuseStep 1839017 = 1379263) B1379263
theorem B1226011 : Blo 570811 1226011 := bstep (se 1 (by rfl) ⟨919508, by rfl⟩ : syracuseStep 1226011 = 1839017) B1839017
theorem B1634681 : Blo 570811 1634681 := bstep (se 2 (by rfl) ⟨613005, by rfl⟩ : syracuseStep 1634681 = 1226011) B1226011
theorem B1089787 : Blo 570811 1089787 := bstep (se 1 (by rfl) ⟨817340, by rfl⟩ : syracuseStep 1089787 = 1634681) B1634681
theorem B1453049 : Blo 570811 1453049 := bstep (se 2 (by rfl) ⟨544893, by rfl⟩ : syracuseStep 1453049 = 1089787) B1089787
theorem B968699 : Blo 570811 968699 := bstep (se 1 (by rfl) ⟨726524, by rfl⟩ : syracuseStep 968699 = 1453049) B1453049
theorem B645799 : Blo 570811 645799 := bstep (se 1 (by rfl) ⟨484349, by rfl⟩ : syracuseStep 645799 = 968699) B968699
theorem B861065 : Blo 570811 861065 := bstep (se 2 (by rfl) ⟨322899, by rfl⟩ : syracuseStep 861065 = 645799) B645799
theorem B574043 : Blo 570811 574043 := bstep (se 1 (by rfl) ⟨430532, by rfl⟩ : syracuseStep 574043 = 861065) B861065

theorem C0 (j : ℕ) (h1 : 142702 ≤ j) (h2 : j ≤ 143401) : Blo 570811 (4 * j + 3) := by
  interval_cases j
  · exact B570811
  · exact B570815
  · exact B570819
  · exact B570823
  · exact B570827
  · exact B570831
  · exact B570835
  · exact B570839
  · exact B570843
  · exact B570847
  · exact B570851
  · exact B570855
  · exact B570859
  · exact B570863
  · exact B570867
  · exact B570871
  · exact B570875
  · exact B570879
  · exact B570883
  · exact B570887
  · exact B570891
  · exact B570895
  · exact B570899
  · exact B570903
  · exact B570907
  · exact B570911
  · exact B570915
  · exact B570919
  · exact B570923
  · exact B570927
  · exact B570931
  · exact B570935
  · exact B570939
  · exact B570943
  · exact B570947
  · exact B570951
  · exact B570955
  · exact B570959
  · exact B570963
  · exact B570967
  · exact B570971
  · exact B570975
  · exact B570979
  · exact B570983
  · exact B570987
  · exact B570991
  · exact B570995
  · exact B570999
  · exact B571003
  · exact B571007
  · exact B571011
  · exact B571015
  · exact B571019
  · exact B571023
  · exact B571027
  · exact B571031
  · exact B571035
  · exact B571039
  · exact B571043
  · exact B571047
  · exact B571051
  · exact B571055
  · exact B571059
  · exact B571063
  · exact B571067
  · exact B571071
  · exact B571075
  · exact B571079
  · exact B571083
  · exact B571087
  · exact B571091
  · exact B571095
  · exact B571099
  · exact B571103
  · exact B571107
  · exact B571111
  · exact B571115
  · exact B571119
  · exact B571123
  · exact B571127
  · exact B571131
  · exact B571135
  · exact B571139
  · exact B571143
  · exact B571147
  · exact B571151
  · exact B571155
  · exact B571159
  · exact B571163
  · exact B571167
  · exact B571171
  · exact B571175
  · exact B571179
  · exact B571183
  · exact B571187
  · exact B571191
  · exact B571195
  · exact B571199
  · exact B571203
  · exact B571207
  · exact B571211
  · exact B571215
  · exact B571219
  · exact B571223
  · exact B571227
  · exact B571231
  · exact B571235
  · exact B571239
  · exact B571243
  · exact B571247
  · exact B571251
  · exact B571255
  · exact B571259
  · exact B571263
  · exact B571267
  · exact B571271
  · exact B571275
  · exact B571279
  · exact B571283
  · exact B571287
  · exact B571291
  · exact B571295
  · exact B571299
  · exact B571303
  · exact B571307
  · exact B571311
  · exact B571315
  · exact B571319
  · exact B571323
  · exact B571327
  · exact B571331
  · exact B571335
  · exact B571339
  · exact B571343
  · exact B571347
  · exact B571351
  · exact B571355
  · exact B571359
  · exact B571363
  · exact B571367
  · exact B571371
  · exact B571375
  · exact B571379
  · exact B571383
  · exact B571387
  · exact B571391
  · exact B571395
  · exact B571399
  · exact B571403
  · exact B571407
  · exact B571411
  · exact B571415
  · exact B571419
  · exact B571423
  · exact B571427
  · exact B571431
  · exact B571435
  · exact B571439
  · exact B571443
  · exact B571447
  · exact B571451
  · exact B571455
  · exact B571459
  · exact B571463
  · exact B571467
  · exact B571471
  · exact B571475
  · exact B571479
  · exact B571483
  · exact B571487
  · exact B571491
  · exact B571495
  · exact B571499
  · exact B571503
  · exact B571507
  · exact B571511
  · exact B571515
  · exact B571519
  · exact B571523
  · exact B571527
  · exact B571531
  · exact B571535
  · exact B571539
  · exact B571543
  · exact B571547
  · exact B571551
  · exact B571555
  · exact B571559
  · exact B571563
  · exact B571567
  · exact B571571
  · exact B571575
  · exact B571579
  · exact B571583
  · exact B571587
  · exact B571591
  · exact B571595
  · exact B571599
  · exact B571603
  · exact B571607
  · exact B571611
  · exact B571615
  · exact B571619
  · exact B571623
  · exact B571627
  · exact B571631
  · exact B571635
  · exact B571639
  · exact B571643
  · exact B571647
  · exact B571651
  · exact B571655
  · exact B571659
  · exact B571663
  · exact B571667
  · exact B571671
  · exact B571675
  · exact B571679
  · exact B571683
  · exact B571687
  · exact B571691
  · exact B571695
  · exact B571699
  · exact B571703
  · exact B571707
  · exact B571711
  · exact B571715
  · exact B571719
  · exact B571723
  · exact B571727
  · exact B571731
  · exact B571735
  · exact B571739
  · exact B571743
  · exact B571747
  · exact B571751
  · exact B571755
  · exact B571759
  · exact B571763
  · exact B571767
  · exact B571771
  · exact B571775
  · exact B571779
  · exact B571783
  · exact B571787
  · exact B571791
  · exact B571795
  · exact B571799
  · exact B571803
  · exact B571807
  · exact B571811
  · exact B571815
  · exact B571819
  · exact B571823
  · exact B571827
  · exact B571831
  · exact B571835
  · exact B571839
  · exact B571843
  · exact B571847
  · exact B571851
  · exact B571855
  · exact B571859
  · exact B571863
  · exact B571867
  · exact B571871
  · exact B571875
  · exact B571879
  · exact B571883
  · exact B571887
  · exact B571891
  · exact B571895
  · exact B571899
  · exact B571903
  · exact B571907
  · exact B571911
  · exact B571915
  · exact B571919
  · exact B571923
  · exact B571927
  · exact B571931
  · exact B571935
  · exact B571939
  · exact B571943
  · exact B571947
  · exact B571951
  · exact B571955
  · exact B571959
  · exact B571963
  · exact B571967
  · exact B571971
  · exact B571975
  · exact B571979
  · exact B571983
  · exact B571987
  · exact B571991
  · exact B571995
  · exact B571999
  · exact B572003
  · exact B572007
  · exact B572011
  · exact B572015
  · exact B572019
  · exact B572023
  · exact B572027
  · exact B572031
  · exact B572035
  · exact B572039
  · exact B572043
  · exact B572047
  · exact B572051
  · exact B572055
  · exact B572059
  · exact B572063
  · exact B572067
  · exact B572071
  · exact B572075
  · exact B572079
  · exact B572083
  · exact B572087
  · exact B572091
  · exact B572095
  · exact B572099
  · exact B572103
  · exact B572107
  · exact B572111
  · exact B572115
  · exact B572119
  · exact B572123
  · exact B572127
  · exact B572131
  · exact B572135
  · exact B572139
  · exact B572143
  · exact B572147
  · exact B572151
  · exact B572155
  · exact B572159
  · exact B572163
  · exact B572167
  · exact B572171
  · exact B572175
  · exact B572179
  · exact B572183
  · exact B572187
  · exact B572191
  · exact B572195
  · exact B572199
  · exact B572203
  · exact B572207
  · exact B572211
  · exact B572215
  · exact B572219
  · exact B572223
  · exact B572227
  · exact B572231
  · exact B572235
  · exact B572239
  · exact B572243
  · exact B572247
  · exact B572251
  · exact B572255
  · exact B572259
  · exact B572263
  · exact B572267
  · exact B572271
  · exact B572275
  · exact B572279
  · exact B572283
  · exact B572287
  · exact B572291
  · exact B572295
  · exact B572299
  · exact B572303
  · exact B572307
  · exact B572311
  · exact B572315
  · exact B572319
  · exact B572323
  · exact B572327
  · exact B572331
  · exact B572335
  · exact B572339
  · exact B572343
  · exact B572347
  · exact B572351
  · exact B572355
  · exact B572359
  · exact B572363
  · exact B572367
  · exact B572371
  · exact B572375
  · exact B572379
  · exact B572383
  · exact B572387
  · exact B572391
  · exact B572395
  · exact B572399
  · exact B572403
  · exact B572407
  · exact B572411
  · exact B572415
  · exact B572419
  · exact B572423
  · exact B572427
  · exact B572431
  · exact B572435
  · exact B572439
  · exact B572443
  · exact B572447
  · exact B572451
  · exact B572455
  · exact B572459
  · exact B572463
  · exact B572467
  · exact B572471
  · exact B572475
  · exact B572479
  · exact B572483
  · exact B572487
  · exact B572491
  · exact B572495
  · exact B572499
  · exact B572503
  · exact B572507
  · exact B572511
  · exact B572515
  · exact B572519
  · exact B572523
  · exact B572527
  · exact B572531
  · exact B572535
  · exact B572539
  · exact B572543
  · exact B572547
  · exact B572551
  · exact B572555
  · exact B572559
  · exact B572563
  · exact B572567
  · exact B572571
  · exact B572575
  · exact B572579
  · exact B572583
  · exact B572587
  · exact B572591
  · exact B572595
  · exact B572599
  · exact B572603
  · exact B572607
  · exact B572611
  · exact B572615
  · exact B572619
  · exact B572623
  · exact B572627
  · exact B572631
  · exact B572635
  · exact B572639
  · exact B572643
  · exact B572647
  · exact B572651
  · exact B572655
  · exact B572659
  · exact B572663
  · exact B572667
  · exact B572671
  · exact B572675
  · exact B572679
  · exact B572683
  · exact B572687
  · exact B572691
  · exact B572695
  · exact B572699
  · exact B572703
  · exact B572707
  · exact B572711
  · exact B572715
  · exact B572719
  · exact B572723
  · exact B572727
  · exact B572731
  · exact B572735
  · exact B572739
  · exact B572743
  · exact B572747
  · exact B572751
  · exact B572755
  · exact B572759
  · exact B572763
  · exact B572767
  · exact B572771
  · exact B572775
  · exact B572779
  · exact B572783
  · exact B572787
  · exact B572791
  · exact B572795
  · exact B572799
  · exact B572803
  · exact B572807
  · exact B572811
  · exact B572815
  · exact B572819
  · exact B572823
  · exact B572827
  · exact B572831
  · exact B572835
  · exact B572839
  · exact B572843
  · exact B572847
  · exact B572851
  · exact B572855
  · exact B572859
  · exact B572863
  · exact B572867
  · exact B572871
  · exact B572875
  · exact B572879
  · exact B572883
  · exact B572887
  · exact B572891
  · exact B572895
  · exact B572899
  · exact B572903
  · exact B572907
  · exact B572911
  · exact B572915
  · exact B572919
  · exact B572923
  · exact B572927
  · exact B572931
  · exact B572935
  · exact B572939
  · exact B572943
  · exact B572947
  · exact B572951
  · exact B572955
  · exact B572959
  · exact B572963
  · exact B572967
  · exact B572971
  · exact B572975
  · exact B572979
  · exact B572983
  · exact B572987
  · exact B572991
  · exact B572995
  · exact B572999
  · exact B573003
  · exact B573007
  · exact B573011
  · exact B573015
  · exact B573019
  · exact B573023
  · exact B573027
  · exact B573031
  · exact B573035
  · exact B573039
  · exact B573043
  · exact B573047
  · exact B573051
  · exact B573055
  · exact B573059
  · exact B573063
  · exact B573067
  · exact B573071
  · exact B573075
  · exact B573079
  · exact B573083
  · exact B573087
  · exact B573091
  · exact B573095
  · exact B573099
  · exact B573103
  · exact B573107
  · exact B573111
  · exact B573115
  · exact B573119
  · exact B573123
  · exact B573127
  · exact B573131
  · exact B573135
  · exact B573139
  · exact B573143
  · exact B573147
  · exact B573151
  · exact B573155
  · exact B573159
  · exact B573163
  · exact B573167
  · exact B573171
  · exact B573175
  · exact B573179
  · exact B573183
  · exact B573187
  · exact B573191
  · exact B573195
  · exact B573199
  · exact B573203
  · exact B573207
  · exact B573211
  · exact B573215
  · exact B573219
  · exact B573223
  · exact B573227
  · exact B573231
  · exact B573235
  · exact B573239
  · exact B573243
  · exact B573247
  · exact B573251
  · exact B573255
  · exact B573259
  · exact B573263
  · exact B573267
  · exact B573271
  · exact B573275
  · exact B573279
  · exact B573283
  · exact B573287
  · exact B573291
  · exact B573295
  · exact B573299
  · exact B573303
  · exact B573307
  · exact B573311
  · exact B573315
  · exact B573319
  · exact B573323
  · exact B573327
  · exact B573331
  · exact B573335
  · exact B573339
  · exact B573343
  · exact B573347
  · exact B573351
  · exact B573355
  · exact B573359
  · exact B573363
  · exact B573367
  · exact B573371
  · exact B573375
  · exact B573379
  · exact B573383
  · exact B573387
  · exact B573391
  · exact B573395
  · exact B573399
  · exact B573403
  · exact B573407
  · exact B573411
  · exact B573415
  · exact B573419
  · exact B573423
  · exact B573427
  · exact B573431
  · exact B573435
  · exact B573439
  · exact B573443
  · exact B573447
  · exact B573451
  · exact B573455
  · exact B573459
  · exact B573463
  · exact B573467
  · exact B573471
  · exact B573475
  · exact B573479
  · exact B573483
  · exact B573487
  · exact B573491
  · exact B573495
  · exact B573499
  · exact B573503
  · exact B573507
  · exact B573511
  · exact B573515
  · exact B573519
  · exact B573523
  · exact B573527
  · exact B573531
  · exact B573535
  · exact B573539
  · exact B573543
  · exact B573547
  · exact B573551
  · exact B573555
  · exact B573559
  · exact B573563
  · exact B573567
  · exact B573571
  · exact B573575
  · exact B573579
  · exact B573583
  · exact B573587
  · exact B573591
  · exact B573595
  · exact B573599
  · exact B573603
  · exact B573607

theorem C1 (j : ℕ) (h1 : 143402 ≤ j) (h2 : j ≤ 143702) : Blo 570811 (4 * j + 3) := by
  interval_cases j
  · exact B573611
  · exact B573615
  · exact B573619
  · exact B573623
  · exact B573627
  · exact B573631
  · exact B573635
  · exact B573639
  · exact B573643
  · exact B573647
  · exact B573651
  · exact B573655
  · exact B573659
  · exact B573663
  · exact B573667
  · exact B573671
  · exact B573675
  · exact B573679
  · exact B573683
  · exact B573687
  · exact B573691
  · exact B573695
  · exact B573699
  · exact B573703
  · exact B573707
  · exact B573711
  · exact B573715
  · exact B573719
  · exact B573723
  · exact B573727
  · exact B573731
  · exact B573735
  · exact B573739
  · exact B573743
  · exact B573747
  · exact B573751
  · exact B573755
  · exact B573759
  · exact B573763
  · exact B573767
  · exact B573771
  · exact B573775
  · exact B573779
  · exact B573783
  · exact B573787
  · exact B573791
  · exact B573795
  · exact B573799
  · exact B573803
  · exact B573807
  · exact B573811
  · exact B573815
  · exact B573819
  · exact B573823
  · exact B573827
  · exact B573831
  · exact B573835
  · exact B573839
  · exact B573843
  · exact B573847
  · exact B573851
  · exact B573855
  · exact B573859
  · exact B573863
  · exact B573867
  · exact B573871
  · exact B573875
  · exact B573879
  · exact B573883
  · exact B573887
  · exact B573891
  · exact B573895
  · exact B573899
  · exact B573903
  · exact B573907
  · exact B573911
  · exact B573915
  · exact B573919
  · exact B573923
  · exact B573927
  · exact B573931
  · exact B573935
  · exact B573939
  · exact B573943
  · exact B573947
  · exact B573951
  · exact B573955
  · exact B573959
  · exact B573963
  · exact B573967
  · exact B573971
  · exact B573975
  · exact B573979
  · exact B573983
  · exact B573987
  · exact B573991
  · exact B573995
  · exact B573999
  · exact B574003
  · exact B574007
  · exact B574011
  · exact B574015
  · exact B574019
  · exact B574023
  · exact B574027
  · exact B574031
  · exact B574035
  · exact B574039
  · exact B574043
  · exact B574047
  · exact B574051
  · exact B574055
  · exact B574059
  · exact B574063
  · exact B574067
  · exact B574071
  · exact B574075
  · exact B574079
  · exact B574083
  · exact B574087
  · exact B574091
  · exact B574095
  · exact B574099
  · exact B574103
  · exact B574107
  · exact B574111
  · exact B574115
  · exact B574119
  · exact B574123
  · exact B574127
  · exact B574131
  · exact B574135
  · exact B574139
  · exact B574143
  · exact B574147
  · exact B574151
  · exact B574155
  · exact B574159
  · exact B574163
  · exact B574167
  · exact B574171
  · exact B574175
  · exact B574179
  · exact B574183
  · exact B574187
  · exact B574191
  · exact B574195
  · exact B574199
  · exact B574203
  · exact B574207
  · exact B574211
  · exact B574215
  · exact B574219
  · exact B574223
  · exact B574227
  · exact B574231
  · exact B574235
  · exact B574239
  · exact B574243
  · exact B574247
  · exact B574251
  · exact B574255
  · exact B574259
  · exact B574263
  · exact B574267
  · exact B574271
  · exact B574275
  · exact B574279
  · exact B574283
  · exact B574287
  · exact B574291
  · exact B574295
  · exact B574299
  · exact B574303
  · exact B574307
  · exact B574311
  · exact B574315
  · exact B574319
  · exact B574323
  · exact B574327
  · exact B574331
  · exact B574335
  · exact B574339
  · exact B574343
  · exact B574347
  · exact B574351
  · exact B574355
  · exact B574359
  · exact B574363
  · exact B574367
  · exact B574371
  · exact B574375
  · exact B574379
  · exact B574383
  · exact B574387
  · exact B574391
  · exact B574395
  · exact B574399
  · exact B574403
  · exact B574407
  · exact B574411
  · exact B574415
  · exact B574419
  · exact B574423
  · exact B574427
  · exact B574431
  · exact B574435
  · exact B574439
  · exact B574443
  · exact B574447
  · exact B574451
  · exact B574455
  · exact B574459
  · exact B574463
  · exact B574467
  · exact B574471
  · exact B574475
  · exact B574479
  · exact B574483
  · exact B574487
  · exact B574491
  · exact B574495
  · exact B574499
  · exact B574503
  · exact B574507
  · exact B574511
  · exact B574515
  · exact B574519
  · exact B574523
  · exact B574527
  · exact B574531
  · exact B574535
  · exact B574539
  · exact B574543
  · exact B574547
  · exact B574551
  · exact B574555
  · exact B574559
  · exact B574563
  · exact B574567
  · exact B574571
  · exact B574575
  · exact B574579
  · exact B574583
  · exact B574587
  · exact B574591
  · exact B574595
  · exact B574599
  · exact B574603
  · exact B574607
  · exact B574611
  · exact B574615
  · exact B574619
  · exact B574623
  · exact B574627
  · exact B574631
  · exact B574635
  · exact B574639
  · exact B574643
  · exact B574647
  · exact B574651
  · exact B574655
  · exact B574659
  · exact B574663
  · exact B574667
  · exact B574671
  · exact B574675
  · exact B574679
  · exact B574683
  · exact B574687
  · exact B574691
  · exact B574695
  · exact B574699
  · exact B574703
  · exact B574707
  · exact B574711
  · exact B574715
  · exact B574719
  · exact B574723
  · exact B574727
  · exact B574731
  · exact B574735
  · exact B574739
  · exact B574743
  · exact B574747
  · exact B574751
  · exact B574755
  · exact B574759
  · exact B574763
  · exact B574767
  · exact B574771
  · exact B574775
  · exact B574779
  · exact B574783
  · exact B574787
  · exact B574791
  · exact B574795
  · exact B574799
  · exact B574803
  · exact B574807
  · exact B574811

theorem solution (m : ℕ) (hlo : 570811 ≤ m) (hhi : m ≤ 574811) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 142702 ≤ j := by omega
    have hj2 : j ≤ 143702 := by omega
    have hb : Blo 570811 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 143402 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
