-- Prove2me | solution 1 for syracuse_descends_range_1293965_1295965
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:24.31646+00:00
-- url     : https://prove2.me/submissions/006c0102-ad92-4d21-9ad4-0850ddfefb4e

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


theorem B1941509 : Blo 1293965 1941509 := bbase (se 4 (by rfl) ⟨182016, by rfl⟩ : syracuseStep 1941509 = 364033) (by norm_num)
theorem B14000149 : Blo 1293965 14000149 := bbase (se 6 (by rfl) ⟨328128, by rfl⟩ : syracuseStep 14000149 = 656257) (by norm_num)
theorem B1941533 : Blo 1293965 1941533 := bbase (se 3 (by rfl) ⟨364037, by rfl⟩ : syracuseStep 1941533 = 728075) (by norm_num)
theorem B3276845 : Blo 1293965 3276845 := bbase (se 3 (by rfl) ⟨614408, by rfl⟩ : syracuseStep 3276845 = 1228817) (by norm_num)
theorem B1941557 : Blo 1293965 1941557 := bbase (se 5 (by rfl) ⟨91010, by rfl⟩ : syracuseStep 1941557 = 182021) (by norm_num)
theorem B1941581 : Blo 1293965 1941581 := bbase (se 3 (by rfl) ⟨364046, by rfl⟩ : syracuseStep 1941581 = 728093) (by norm_num)
theorem B3686485 : Blo 1293965 3686485 := bbase (se 8 (by rfl) ⟨21600, by rfl⟩ : syracuseStep 3686485 = 43201) (by norm_num)
theorem B3194981 : Blo 1293965 3194981 := bbase (se 4 (by rfl) ⟨299529, by rfl⟩ : syracuseStep 3194981 = 599059) (by norm_num)
theorem B1941605 : Blo 1293965 1941605 := bbase (se 4 (by rfl) ⟨182025, by rfl⟩ : syracuseStep 1941605 = 364051) (by norm_num)
theorem B1941629 : Blo 1293965 1941629 := bbase (se 3 (by rfl) ⟨364055, by rfl⟩ : syracuseStep 1941629 = 728111) (by norm_num)
theorem B3154061 : Blo 1293965 3154061 := bbase (se 3 (by rfl) ⟨591386, by rfl⟩ : syracuseStep 3154061 = 1182773) (by norm_num)
theorem B1941653 : Blo 1293965 1941653 := bbase (se 6 (by rfl) ⟨45507, by rfl⟩ : syracuseStep 1941653 = 91015) (by norm_num)
theorem B1638569 : Blo 1293965 1638569 := bbase (se 2 (by rfl) ⟨614463, by rfl⟩ : syracuseStep 1638569 = 1228927) (by norm_num)
theorem B1941677 : Blo 1293965 1941677 := bbase (se 3 (by rfl) ⟨364064, by rfl⟩ : syracuseStep 1941677 = 728129) (by norm_num)
theorem B1941701 : Blo 1293965 1941701 := bbase (se 4 (by rfl) ⟨182034, by rfl⟩ : syracuseStep 1941701 = 364069) (by norm_num)
theorem B1941725 : Blo 1293965 1941725 := bbase (se 3 (by rfl) ⟨364073, by rfl⟩ : syracuseStep 1941725 = 728147) (by norm_num)
theorem B3367133 : Blo 1293965 3367133 := bbase (se 3 (by rfl) ⟨631337, by rfl⟩ : syracuseStep 3367133 = 1262675) (by norm_num)
theorem B1638625 : Blo 1293965 1638625 := bbase (se 2 (by rfl) ⟨614484, by rfl⟩ : syracuseStep 1638625 = 1228969) (by norm_num)
theorem B3277037 : Blo 1293965 3277037 := bbase (se 3 (by rfl) ⟨614444, by rfl⟩ : syracuseStep 3277037 = 1228889) (by norm_num)
theorem B1941749 : Blo 1293965 1941749 := bbase (se 5 (by rfl) ⟨91019, by rfl⟩ : syracuseStep 1941749 = 182039) (by norm_num)
theorem B4145413 : Blo 1293965 4145413 := bbase (se 4 (by rfl) ⟨388632, by rfl⟩ : syracuseStep 4145413 = 777265) (by norm_num)
theorem B1941773 : Blo 1293965 1941773 := bbase (se 3 (by rfl) ⟨364082, by rfl⟩ : syracuseStep 1941773 = 728165) (by norm_num)
theorem B2457877 : Blo 1293965 2457877 := bbase (se 6 (by rfl) ⟨57606, by rfl⟩ : syracuseStep 2457877 = 115213) (by norm_num)
theorem B2072861 : Blo 1293965 2072861 := bbase (se 3 (by rfl) ⟨388661, by rfl⟩ : syracuseStep 2072861 = 777323) (by norm_num)
theorem B1941797 : Blo 1293965 1941797 := bbase (se 4 (by rfl) ⟨182043, by rfl⟩ : syracuseStep 1941797 = 364087) (by norm_num)
theorem B1941821 : Blo 1293965 1941821 := bbase (se 3 (by rfl) ⟨364091, by rfl⟩ : syracuseStep 1941821 = 728183) (by norm_num)
theorem B1638721 : Blo 1293965 1638721 := bbase (se 2 (by rfl) ⟨614520, by rfl⟩ : syracuseStep 1638721 = 1229041) (by norm_num)
theorem B4915525 : Blo 1293965 4915525 := bbase (se 4 (by rfl) ⟨460830, by rfl⟩ : syracuseStep 4915525 = 921661) (by norm_num)
theorem B1941845 : Blo 1293965 1941845 := bbase (se 10 (by rfl) ⟨2844, by rfl⟩ : syracuseStep 1941845 = 5689) (by norm_num)
theorem B1941869 : Blo 1293965 1941869 := bbase (se 3 (by rfl) ⟨364100, by rfl⟩ : syracuseStep 1941869 = 728201) (by norm_num)
theorem B1843573 : Blo 1293965 1843573 := bbase (se 5 (by rfl) ⟨86417, by rfl⟩ : syracuseStep 1843573 = 172835) (by norm_num)
theorem B1941893 : Blo 1293965 1941893 := bbase (se 4 (by rfl) ⟨182052, by rfl⟩ : syracuseStep 1941893 = 364105) (by norm_num)
theorem B1941917 : Blo 1293965 1941917 := bbase (se 3 (by rfl) ⟨364109, by rfl⟩ : syracuseStep 1941917 = 728219) (by norm_num)
theorem B2458021 : Blo 1293965 2458021 := bbase (se 4 (by rfl) ⟨230439, by rfl⟩ : syracuseStep 2458021 = 460879) (by norm_num)
theorem B2490797 : Blo 1293965 2490797 := bbase (se 3 (by rfl) ⟨467024, by rfl⟩ : syracuseStep 2490797 = 934049) (by norm_num)
theorem B1941941 : Blo 1293965 1941941 := bbase (se 5 (by rfl) ⟨91028, by rfl⟩ : syracuseStep 1941941 = 182057) (by norm_num)
theorem B1941965 : Blo 1293965 1941965 := bbase (se 3 (by rfl) ⟨364118, by rfl⟩ : syracuseStep 1941965 = 728237) (by norm_num)
theorem B1941989 : Blo 1293965 1941989 := bbase (se 4 (by rfl) ⟨182061, by rfl⟩ : syracuseStep 1941989 = 364123) (by norm_num)
theorem B1638893 : Blo 1293965 1638893 := bbase (se 3 (by rfl) ⟨307292, by rfl⟩ : syracuseStep 1638893 = 614585) (by norm_num)
theorem B1942013 : Blo 1293965 1942013 := bbase (se 3 (by rfl) ⟨364127, by rfl⟩ : syracuseStep 1942013 = 728255) (by norm_num)
theorem B1942037 : Blo 1293965 1942037 := bbase (se 6 (by rfl) ⟨45516, by rfl⟩ : syracuseStep 1942037 = 91033) (by norm_num)
theorem B1638949 : Blo 1293965 1638949 := bbase (se 4 (by rfl) ⟨153651, by rfl⟩ : syracuseStep 1638949 = 307303) (by norm_num)
theorem B1942061 : Blo 1293965 1942061 := bbase (se 3 (by rfl) ⟨364136, by rfl⟩ : syracuseStep 1942061 = 728273) (by norm_num)
theorem B7979573 : Blo 1293965 7979573 := bbase (se 5 (by rfl) ⟨374042, by rfl⟩ : syracuseStep 7979573 = 748085) (by norm_num)
theorem B1942085 : Blo 1293965 1942085 := bbase (se 4 (by rfl) ⟨182070, by rfl⟩ : syracuseStep 1942085 = 364141) (by norm_num)
theorem B3277381 : Blo 1293965 3277381 := bbase (se 4 (by rfl) ⟨307254, by rfl⟩ : syracuseStep 3277381 = 614509) (by norm_num)
theorem B2458181 : Blo 1293965 2458181 := bbase (se 4 (by rfl) ⟨230454, by rfl⟩ : syracuseStep 2458181 = 460909) (by norm_num)
theorem B3113549 : Blo 1293965 3113549 := bbase (se 3 (by rfl) ⟨583790, by rfl⟩ : syracuseStep 3113549 = 1167581) (by norm_num)
theorem B1942109 : Blo 1293965 1942109 := bbase (se 3 (by rfl) ⟨364145, by rfl⟩ : syracuseStep 1942109 = 728291) (by norm_num)
theorem B4915829 : Blo 1293965 4915829 := bbase (se 5 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 4915829 = 460859) (by norm_num)
theorem B1942133 : Blo 1293965 1942133 := bbase (se 5 (by rfl) ⟨91037, by rfl⟩ : syracuseStep 1942133 = 182075) (by norm_num)
theorem B1639045 : Blo 1293965 1639045 := bbase (se 4 (by rfl) ⟨153660, by rfl⟩ : syracuseStep 1639045 = 307321) (by norm_num)
theorem B1942157 : Blo 1293965 1942157 := bbase (se 3 (by rfl) ⟨364154, by rfl⟩ : syracuseStep 1942157 = 728309) (by norm_num)
theorem B21013141 : Blo 1293965 21013141 := bbase (se 6 (by rfl) ⟨492495, by rfl⟩ : syracuseStep 21013141 = 984991) (by norm_num)
theorem B1942181 : Blo 1293965 1942181 := bbase (se 4 (by rfl) ⟨182079, by rfl⟩ : syracuseStep 1942181 = 364159) (by norm_num)
theorem B3277493 : Blo 1293965 3277493 := bbase (se 5 (by rfl) ⟨153632, by rfl⟩ : syracuseStep 3277493 = 307265) (by norm_num)
theorem B1942205 : Blo 1293965 1942205 := bbase (se 3 (by rfl) ⟨364163, by rfl⟩ : syracuseStep 1942205 = 728327) (by norm_num)
theorem B1942229 : Blo 1293965 1942229 := bbase (se 7 (by rfl) ⟨22760, by rfl⟩ : syracuseStep 1942229 = 45521) (by norm_num)
theorem B2458325 : Blo 1293965 2458325 := bbase (se 7 (by rfl) ⟨28808, by rfl⟩ : syracuseStep 2458325 = 57617) (by norm_num)
theorem B1942253 : Blo 1293965 1942253 := bbase (se 3 (by rfl) ⟨364172, by rfl⟩ : syracuseStep 1942253 = 728345) (by norm_num)
theorem B6554357 : Blo 1293965 6554357 := bbase (se 5 (by rfl) ⟨307235, by rfl⟩ : syracuseStep 6554357 = 614471) (by norm_num)
theorem B1942277 : Blo 1293965 1942277 := bbase (se 4 (by rfl) ⟨182088, by rfl⟩ : syracuseStep 1942277 = 364177) (by norm_num)
theorem B1942301 : Blo 1293965 1942301 := bbase (se 3 (by rfl) ⟨364181, by rfl⟩ : syracuseStep 1942301 = 728363) (by norm_num)
theorem B4367141 : Blo 1293965 4367141 := bbase (se 4 (by rfl) ⟨409419, by rfl⟩ : syracuseStep 4367141 = 818839) (by norm_num)
theorem B1639217 : Blo 1293965 1639217 := bbase (se 2 (by rfl) ⟨614706, by rfl⟩ : syracuseStep 1639217 = 1229413) (by norm_num)
theorem B1942325 : Blo 1293965 1942325 := bbase (se 5 (by rfl) ⟨91046, by rfl⟩ : syracuseStep 1942325 = 182093) (by norm_num)
theorem B1942349 : Blo 1293965 1942349 := bbase (se 3 (by rfl) ⟨364190, by rfl⟩ : syracuseStep 1942349 = 728381) (by norm_num)
theorem B4670293 : Blo 1293965 4670293 := bbase (se 9 (by rfl) ⟨13682, by rfl⟩ : syracuseStep 4670293 = 27365) (by norm_num)
theorem B2491229 : Blo 1293965 2491229 := bbase (se 3 (by rfl) ⟨467105, by rfl⟩ : syracuseStep 2491229 = 934211) (by norm_num)
theorem B1942373 : Blo 1293965 1942373 := bbase (se 4 (by rfl) ⟨182097, by rfl⟩ : syracuseStep 1942373 = 364195) (by norm_num)
theorem B1639273 : Blo 1293965 1639273 := bbase (se 2 (by rfl) ⟨614727, by rfl⟩ : syracuseStep 1639273 = 1229455) (by norm_num)
theorem B3277685 : Blo 1293965 3277685 := bbase (se 5 (by rfl) ⟨153641, by rfl⟩ : syracuseStep 3277685 = 307283) (by norm_num)
theorem B1942397 : Blo 1293965 1942397 := bbase (se 3 (by rfl) ⟨364199, by rfl⟩ : syracuseStep 1942397 = 728399) (by norm_num)
theorem B22119317 : Blo 1293965 22119317 := bbase (se 6 (by rfl) ⟨518421, by rfl⟩ : syracuseStep 22119317 = 1036843) (by norm_num)
theorem B1942421 : Blo 1293965 1942421 := bbase (se 6 (by rfl) ⟨45525, by rfl⟩ : syracuseStep 1942421 = 91051) (by norm_num)
theorem B1942445 : Blo 1293965 1942445 := bbase (se 3 (by rfl) ⟨364208, by rfl⟩ : syracuseStep 1942445 = 728417) (by norm_num)
theorem B1942469 : Blo 1293965 1942469 := bbase (se 4 (by rfl) ⟨182106, by rfl⟩ : syracuseStep 1942469 = 364213) (by norm_num)
theorem B1844165 : Blo 1293965 1844165 := bbase (se 4 (by rfl) ⟨172890, by rfl⟩ : syracuseStep 1844165 = 345781) (by norm_num)
theorem B1639369 : Blo 1293965 1639369 := bbase (se 2 (by rfl) ⟨614763, by rfl⟩ : syracuseStep 1639369 = 1229527) (by norm_num)
theorem B1942493 : Blo 1293965 1942493 := bbase (se 3 (by rfl) ⟨364217, by rfl⟩ : syracuseStep 1942493 = 728435) (by norm_num)
theorem B1942517 : Blo 1293965 1942517 := bbase (se 5 (by rfl) ⟨91055, by rfl⟩ : syracuseStep 1942517 = 182111) (by norm_num)
theorem B2458613 : Blo 1293965 2458613 := bbase (se 5 (by rfl) ⟨115247, by rfl⟩ : syracuseStep 2458613 = 230495) (by norm_num)
theorem B9339893 : Blo 1293965 9339893 := bbase (se 5 (by rfl) ⟨437807, by rfl⟩ : syracuseStep 9339893 = 875615) (by norm_num)
theorem B2802701 : Blo 1293965 2802701 := bbase (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) (by norm_num)
theorem B1942541 : Blo 1293965 1942541 := bbase (se 3 (by rfl) ⟨364226, by rfl⟩ : syracuseStep 1942541 = 728453) (by norm_num)
theorem B1844245 : Blo 1293965 1844245 := bbase (se 6 (by rfl) ⟨43224, by rfl⟩ : syracuseStep 1844245 = 86449) (by norm_num)
theorem B1942565 : Blo 1293965 1942565 := bbase (se 4 (by rfl) ⟨182115, by rfl⟩ : syracuseStep 1942565 = 364231) (by norm_num)
theorem B1942589 : Blo 1293965 1942589 := bbase (se 3 (by rfl) ⟨364235, by rfl⟩ : syracuseStep 1942589 = 728471) (by norm_num)
theorem B4146245 : Blo 1293965 4146245 := bbase (se 4 (by rfl) ⟨388710, by rfl⟩ : syracuseStep 4146245 = 777421) (by norm_num)
theorem B1942613 : Blo 1293965 1942613 := bbase (se 8 (by rfl) ⟨11382, by rfl⟩ : syracuseStep 1942613 = 22765) (by norm_num)
theorem B1942637 : Blo 1293965 1942637 := bbase (se 3 (by rfl) ⟨364244, by rfl⟩ : syracuseStep 1942637 = 728489) (by norm_num)
theorem B1639541 : Blo 1293965 1639541 := bbase (se 5 (by rfl) ⟨76853, by rfl⟩ : syracuseStep 1639541 = 153707) (by norm_num)
theorem B1942661 : Blo 1293965 1942661 := bbase (se 4 (by rfl) ⟨182124, by rfl⟩ : syracuseStep 1942661 = 364249) (by norm_num)
theorem B2458765 : Blo 1293965 2458765 := bbase (se 3 (by rfl) ⟨461018, by rfl⟩ : syracuseStep 2458765 = 922037) (by norm_num)
theorem B1844365 : Blo 1293965 1844365 := bbase (se 3 (by rfl) ⟨345818, by rfl⟩ : syracuseStep 1844365 = 691637) (by norm_num)
theorem B1942685 : Blo 1293965 1942685 := bbase (se 3 (by rfl) ⟨364253, by rfl⟩ : syracuseStep 1942685 = 728507) (by norm_num)
theorem B1639597 : Blo 1293965 1639597 := bbase (se 3 (by rfl) ⟨307424, by rfl⟩ : syracuseStep 1639597 = 614849) (by norm_num)
theorem B1942709 : Blo 1293965 1942709 := bbase (se 5 (by rfl) ⟨91064, by rfl⟩ : syracuseStep 1942709 = 182129) (by norm_num)
theorem B1475777 : Blo 1293965 1475777 := bbase (se 2 (by rfl) ⟨553416, by rfl⟩ : syracuseStep 1475777 = 1106833) (by norm_num)
theorem B3278029 : Blo 1293965 3278029 := bbase (se 3 (by rfl) ⟨614630, by rfl⟩ : syracuseStep 3278029 = 1229261) (by norm_num)
theorem B1942733 : Blo 1293965 1942733 := bbase (se 3 (by rfl) ⟨364262, by rfl⟩ : syracuseStep 1942733 = 728525) (by norm_num)
theorem B4367573 : Blo 1293965 4367573 := bbase (se 7 (by rfl) ⟨51182, by rfl⟩ : syracuseStep 4367573 = 102365) (by norm_num)
theorem B1942757 : Blo 1293965 1942757 := bbase (se 4 (by rfl) ⟨182133, by rfl⟩ : syracuseStep 1942757 = 364267) (by norm_num)
theorem B1844461 : Blo 1293965 1844461 := bbase (se 3 (by rfl) ⟨345836, by rfl⟩ : syracuseStep 1844461 = 691673) (by norm_num)
theorem B2073853 : Blo 1293965 2073853 := bbase (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) (by norm_num)
theorem B1942781 : Blo 1293965 1942781 := bbase (se 3 (by rfl) ⟨364271, by rfl⟩ : syracuseStep 1942781 = 728543) (by norm_num)
theorem B1639693 : Blo 1293965 1639693 := bbase (se 3 (by rfl) ⟨307442, by rfl⟩ : syracuseStep 1639693 = 614885) (by norm_num)
theorem B1942805 : Blo 1293965 1942805 := bbase (se 6 (by rfl) ⟨45534, by rfl⟩ : syracuseStep 1942805 = 91069) (by norm_num)
theorem B1942829 : Blo 1293965 1942829 := bbase (se 3 (by rfl) ⟨364280, by rfl⟩ : syracuseStep 1942829 = 728561) (by norm_num)
theorem B3278141 : Blo 1293965 3278141 := bbase (se 3 (by rfl) ⟨614651, by rfl⟩ : syracuseStep 3278141 = 1229303) (by norm_num)
theorem B1942853 : Blo 1293965 1942853 := bbase (se 4 (by rfl) ⟨182142, by rfl⟩ : syracuseStep 1942853 = 364285) (by norm_num)
theorem B1402181 : Blo 1293965 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B1942877 : Blo 1293965 1942877 := bbase (se 3 (by rfl) ⟨364289, by rfl⟩ : syracuseStep 1942877 = 728579) (by norm_num)
theorem B1942901 : Blo 1293965 1942901 := bbase (se 5 (by rfl) ⟨91073, by rfl⟩ : syracuseStep 1942901 = 182147) (by norm_num)
theorem B1942925 : Blo 1293965 1942925 := bbase (se 3 (by rfl) ⟨364298, by rfl⟩ : syracuseStep 1942925 = 728597) (by norm_num)
theorem B1942949 : Blo 1293965 1942949 := bbase (se 4 (by rfl) ⟨182151, by rfl⟩ : syracuseStep 1942949 = 364303) (by norm_num)
theorem B1639865 : Blo 1293965 1639865 := bbase (se 2 (by rfl) ⟨614949, by rfl⟩ : syracuseStep 1639865 = 1229899) (by norm_num)
theorem B2459069 : Blo 1293965 2459069 := bbase (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) (by norm_num)
theorem B1942973 : Blo 1293965 1942973 := bbase (se 3 (by rfl) ⟨364307, by rfl⟩ : syracuseStep 1942973 = 728615) (by norm_num)
theorem B1942997 : Blo 1293965 1942997 := bbase (se 7 (by rfl) ⟨22769, by rfl⟩ : syracuseStep 1942997 = 45539) (by norm_num)
theorem B1943021 : Blo 1293965 1943021 := bbase (se 3 (by rfl) ⟨364316, by rfl⟩ : syracuseStep 1943021 = 728633) (by norm_num)
theorem B1639921 : Blo 1293965 1639921 := bbase (se 2 (by rfl) ⟨614970, by rfl⟩ : syracuseStep 1639921 = 1229941) (by norm_num)
theorem B3278333 : Blo 1293965 3278333 := bbase (se 3 (by rfl) ⟨614687, by rfl⟩ : syracuseStep 3278333 = 1229375) (by norm_num)
theorem B1943045 : Blo 1293965 1943045 := bbase (se 4 (by rfl) ⟨182160, by rfl⟩ : syracuseStep 1943045 = 364321) (by norm_num)
theorem B1943069 : Blo 1293965 1943069 := bbase (se 3 (by rfl) ⟨364325, by rfl⟩ : syracuseStep 1943069 = 728651) (by norm_num)
theorem B1943093 : Blo 1293965 1943093 := bbase (se 5 (by rfl) ⟨91082, by rfl⟩ : syracuseStep 1943093 = 182165) (by norm_num)
theorem B1943117 : Blo 1293965 1943117 := bbase (se 3 (by rfl) ⟨364334, by rfl⟩ : syracuseStep 1943117 = 728669) (by norm_num)
theorem B1640017 : Blo 1293965 1640017 := bbase (se 2 (by rfl) ⟨615006, by rfl⟩ : syracuseStep 1640017 = 1230013) (by norm_num)
theorem B1943141 : Blo 1293965 1943141 := bbase (se 4 (by rfl) ⟨182169, by rfl⟩ : syracuseStep 1943141 = 364339) (by norm_num)
theorem B1943165 : Blo 1293965 1943165 := bbase (se 3 (by rfl) ⟨364343, by rfl⟩ : syracuseStep 1943165 = 728687) (by norm_num)
theorem B4368005 : Blo 1293965 4368005 := bbase (se 4 (by rfl) ⟨409500, by rfl⟩ : syracuseStep 4368005 = 819001) (by norm_num)
theorem B1943189 : Blo 1293965 1943189 := bbase (se 6 (by rfl) ⟨45543, by rfl⟩ : syracuseStep 1943189 = 91087) (by norm_num)
theorem B1943213 : Blo 1293965 1943213 := bbase (se 3 (by rfl) ⟨364352, by rfl⟩ : syracuseStep 1943213 = 728705) (by norm_num)
theorem B1943237 : Blo 1293965 1943237 := bbase (se 4 (by rfl) ⟨182178, by rfl⟩ : syracuseStep 1943237 = 364357) (by norm_num)
theorem B1943261 : Blo 1293965 1943261 := bbase (se 3 (by rfl) ⟨364361, by rfl⟩ : syracuseStep 1943261 = 728723) (by norm_num)
theorem B1844957 : Blo 1293965 1844957 := bbase (se 3 (by rfl) ⟨345929, by rfl⟩ : syracuseStep 1844957 = 691859) (by norm_num)
theorem B1402601 : Blo 1293965 1402601 := bbase (se 2 (by rfl) ⟨525975, by rfl⟩ : syracuseStep 1402601 = 1051951) (by norm_num)
theorem B1943285 : Blo 1293965 1943285 := bbase (se 5 (by rfl) ⟨91091, by rfl⟩ : syracuseStep 1943285 = 182183) (by norm_num)
theorem B1640189 : Blo 1293965 1640189 := bbase (se 3 (by rfl) ⟨307535, by rfl⟩ : syracuseStep 1640189 = 615071) (by norm_num)
theorem B1869581 : Blo 1293965 1869581 := bbase (se 3 (by rfl) ⟨350546, by rfl⟩ : syracuseStep 1869581 = 701093) (by norm_num)
theorem B1943309 : Blo 1293965 1943309 := bbase (se 3 (by rfl) ⟨364370, by rfl⟩ : syracuseStep 1943309 = 728741) (by norm_num)
theorem B5605141 : Blo 1293965 5605141 := bbase (se 6 (by rfl) ⟨131370, by rfl⟩ : syracuseStep 5605141 = 262741) (by norm_num)
theorem B1943333 : Blo 1293965 1943333 := bbase (se 4 (by rfl) ⟨182187, by rfl⟩ : syracuseStep 1943333 = 364375) (by norm_num)
theorem B2623277 : Blo 1293965 2623277 := bbase (se 3 (by rfl) ⟨491864, by rfl⟩ : syracuseStep 2623277 = 983729) (by norm_num)
theorem B1943357 : Blo 1293965 1943357 := bbase (se 3 (by rfl) ⟨364379, by rfl⟩ : syracuseStep 1943357 = 728759) (by norm_num)
theorem B1402705 : Blo 1293965 1402705 := bbase (se 2 (by rfl) ⟨526014, by rfl⟩ : syracuseStep 1402705 = 1052029) (by norm_num)
theorem B3278677 : Blo 1293965 3278677 := bbase (se 9 (by rfl) ⟨9605, by rfl⟩ : syracuseStep 3278677 = 19211) (by norm_num)
theorem B1943381 : Blo 1293965 1943381 := bbase (se 9 (by rfl) ⟨5693, by rfl⟩ : syracuseStep 1943381 = 11387) (by norm_num)
theorem B1943405 : Blo 1293965 1943405 := bbase (se 3 (by rfl) ⟨364388, by rfl⟩ : syracuseStep 1943405 = 728777) (by norm_num)
theorem B1967989 : Blo 1293965 1967989 := bbase (se 5 (by rfl) ⟨92249, by rfl⟩ : syracuseStep 1967989 = 184499) (by norm_num)
theorem B2074501 : Blo 1293965 2074501 := bbase (se 4 (by rfl) ⟨194484, by rfl⟩ : syracuseStep 2074501 = 388969) (by norm_num)
theorem B1943429 : Blo 1293965 1943429 := bbase (se 4 (by rfl) ⟨182196, by rfl⟩ : syracuseStep 1943429 = 364393) (by norm_num)
theorem B1943453 : Blo 1293965 1943453 := bbase (se 3 (by rfl) ⟨364397, by rfl⟩ : syracuseStep 1943453 = 728795) (by norm_num)
theorem B1943477 : Blo 1293965 1943477 := bbase (se 5 (by rfl) ⟨91100, by rfl⟩ : syracuseStep 1943477 = 182201) (by norm_num)
theorem B3278789 : Blo 1293965 3278789 := bbase (se 4 (by rfl) ⟨307386, by rfl⟩ : syracuseStep 3278789 = 614773) (by norm_num)
theorem B1943501 : Blo 1293965 1943501 := bbase (se 3 (by rfl) ⟨364406, by rfl⟩ : syracuseStep 1943501 = 728813) (by norm_num)
theorem B8521685 : Blo 1293965 8521685 := bbase (se 7 (by rfl) ⟨99863, by rfl⟩ : syracuseStep 8521685 = 199727) (by norm_num)
theorem B1943525 : Blo 1293965 1943525 := bbase (se 4 (by rfl) ⟨182205, by rfl⟩ : syracuseStep 1943525 = 364411) (by norm_num)
theorem B1943549 : Blo 1293965 1943549 := bbase (se 3 (by rfl) ⟨364415, by rfl⟩ : syracuseStep 1943549 = 728831) (by norm_num)
theorem B6555653 : Blo 1293965 6555653 := bbase (se 4 (by rfl) ⟨614592, by rfl⟩ : syracuseStep 6555653 = 1229185) (by norm_num)
theorem B14747669 : Blo 1293965 14747669 := bbase (se 6 (by rfl) ⟨345648, by rfl⟩ : syracuseStep 14747669 = 691297) (by norm_num)
theorem B1943573 : Blo 1293965 1943573 := bbase (se 6 (by rfl) ⟨45552, by rfl⟩ : syracuseStep 1943573 = 91105) (by norm_num)
theorem B1943597 : Blo 1293965 1943597 := bbase (se 3 (by rfl) ⟨364424, by rfl⟩ : syracuseStep 1943597 = 728849) (by norm_num)
theorem B4368437 : Blo 1293965 4368437 := bbase (se 5 (by rfl) ⟨204770, by rfl⟩ : syracuseStep 4368437 = 409541) (by norm_num)
theorem B1943621 : Blo 1293965 1943621 := bbase (se 4 (by rfl) ⟨182214, by rfl⟩ : syracuseStep 1943621 = 364429) (by norm_num)
theorem B2951261 : Blo 1293965 2951261 := bbase (se 3 (by rfl) ⟨553361, by rfl⟩ : syracuseStep 2951261 = 1106723) (by norm_num)
theorem B1943645 : Blo 1293965 1943645 := bbase (se 3 (by rfl) ⟨364433, by rfl⟩ : syracuseStep 1943645 = 728867) (by norm_num)
theorem B1943669 : Blo 1293965 1943669 := bbase (se 5 (by rfl) ⟨91109, by rfl⟩ : syracuseStep 1943669 = 182219) (by norm_num)
theorem B3278981 : Blo 1293965 3278981 := bbase (se 4 (by rfl) ⟨307404, by rfl⟩ : syracuseStep 3278981 = 614809) (by norm_num)
theorem B1943693 : Blo 1293965 1943693 := bbase (se 3 (by rfl) ⟨364442, by rfl⟩ : syracuseStep 1943693 = 728885) (by norm_num)
theorem B1476757 : Blo 1293965 1476757 := bbase (se 6 (by rfl) ⟨34611, by rfl⟩ : syracuseStep 1476757 = 69223) (by norm_num)
theorem B5531813 : Blo 1293965 5531813 := bbase (se 4 (by rfl) ⟨518607, by rfl⟩ : syracuseStep 5531813 = 1037215) (by norm_num)
theorem B1943717 : Blo 1293965 1943717 := bbase (se 4 (by rfl) ⟨182223, by rfl⟩ : syracuseStep 1943717 = 364447) (by norm_num)
theorem B2459821 : Blo 1293965 2459821 := bbase (se 3 (by rfl) ⟨461216, by rfl⟩ : syracuseStep 2459821 = 922433) (by norm_num)
theorem B1943741 : Blo 1293965 1943741 := bbase (se 3 (by rfl) ⟨364451, by rfl⟩ : syracuseStep 1943741 = 728903) (by norm_num)
theorem B1943765 : Blo 1293965 1943765 := bbase (se 7 (by rfl) ⟨22778, by rfl⟩ : syracuseStep 1943765 = 45557) (by norm_num)
theorem B1943789 : Blo 1293965 1943789 := bbase (se 3 (by rfl) ⟨364460, by rfl⟩ : syracuseStep 1943789 = 728921) (by norm_num)
theorem B1943813 : Blo 1293965 1943813 := bbase (se 4 (by rfl) ⟨182232, by rfl⟩ : syracuseStep 1943813 = 364465) (by norm_num)
theorem B1313033 : Blo 1293965 1313033 := bbase (se 2 (by rfl) ⟨492387, by rfl⟩ : syracuseStep 1313033 = 984775) (by norm_num)
theorem B1943837 : Blo 1293965 1943837 := bbase (se 3 (by rfl) ⟨364469, by rfl⟩ : syracuseStep 1943837 = 728939) (by norm_num)
theorem B7375157 : Blo 1293965 7375157 := bbase (se 5 (by rfl) ⟨345710, by rfl⟩ : syracuseStep 7375157 = 691421) (by norm_num)
theorem B1943861 : Blo 1293965 1943861 := bbase (se 5 (by rfl) ⟨91118, by rfl⟩ : syracuseStep 1943861 = 182237) (by norm_num)
theorem B2459965 : Blo 1293965 2459965 := bbase (se 3 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 2459965 = 922487) (by norm_num)
theorem B1943885 : Blo 1293965 1943885 := bbase (se 3 (by rfl) ⟨364478, by rfl⟩ : syracuseStep 1943885 = 728957) (by norm_num)
theorem B1943909 : Blo 1293965 1943909 := bbase (se 4 (by rfl) ⟨182241, by rfl⟩ : syracuseStep 1943909 = 364483) (by norm_num)
theorem B2623861 : Blo 1293965 2623861 := bbase (se 5 (by rfl) ⟨122993, by rfl⟩ : syracuseStep 2623861 = 245987) (by norm_num)
theorem B9841013 : Blo 1293965 9841013 := bbase (se 5 (by rfl) ⟨461297, by rfl⟩ : syracuseStep 9841013 = 922595) (by norm_num)
theorem B1943933 : Blo 1293965 1943933 := bbase (se 3 (by rfl) ⟨364487, by rfl⟩ : syracuseStep 1943933 = 728975) (by norm_num)
theorem B2992565 : Blo 1293965 2992565 := bbase (se 5 (by rfl) ⟨140276, by rfl⟩ : syracuseStep 2992565 = 280553) (by norm_num)
theorem B3279325 : Blo 1293965 3279325 := bbase (se 3 (by rfl) ⟨614873, by rfl⟩ : syracuseStep 3279325 = 1229747) (by norm_num)
theorem B2460125 : Blo 1293965 2460125 := bbase (se 3 (by rfl) ⟨461273, by rfl⟩ : syracuseStep 2460125 = 922547) (by norm_num)
theorem B4368869 : Blo 1293965 4368869 := bbase (se 4 (by rfl) ⟨409581, by rfl⟩ : syracuseStep 4368869 = 819163) (by norm_num)
theorem B3279437 : Blo 1293965 3279437 := bbase (se 3 (by rfl) ⟨614894, by rfl⟩ : syracuseStep 3279437 = 1229789) (by norm_num)
theorem B3320405 : Blo 1293965 3320405 := bbase (se 8 (by rfl) ⟨19455, by rfl⟩ : syracuseStep 3320405 = 38911) (by norm_num)
theorem B2460269 : Blo 1293965 2460269 := bbase (se 3 (by rfl) ⟨461300, by rfl⟩ : syracuseStep 2460269 = 922601) (by norm_num)
theorem B4917941 : Blo 1293965 4917941 := bbase (se 5 (by rfl) ⟨230528, by rfl⟩ : syracuseStep 4917941 = 461057) (by norm_num)
theorem B1968845 : Blo 1293965 1968845 := bbase (se 3 (by rfl) ⟨369158, by rfl⟩ : syracuseStep 1968845 = 738317) (by norm_num)
theorem B3279629 : Blo 1293965 3279629 := bbase (se 3 (by rfl) ⟨614930, by rfl⟩ : syracuseStep 3279629 = 1229861) (by norm_num)
theorem B9833237 : Blo 1293965 9833237 := bbase (se 6 (by rfl) ⟨230466, by rfl⟩ : syracuseStep 9833237 = 460933) (by norm_num)
theorem B2075429 : Blo 1293965 2075429 := bbase (se 4 (by rfl) ⟨194571, by rfl⟩ : syracuseStep 2075429 = 389143) (by norm_num)
theorem B2624309 : Blo 1293965 2624309 := bbase (se 5 (by rfl) ⟨123014, by rfl⟩ : syracuseStep 2624309 = 246029) (by norm_num)
theorem B5909365 : Blo 1293965 5909365 := bbase (se 5 (by rfl) ⟨277001, by rfl⟩ : syracuseStep 5909365 = 554003) (by norm_num)
theorem B3689333 : Blo 1293965 3689333 := bbase (se 5 (by rfl) ⟨172937, by rfl⟩ : syracuseStep 3689333 = 345875) (by norm_num)
theorem B5909381 : Blo 1293965 5909381 := bbase (se 4 (by rfl) ⟨554004, by rfl⟩ : syracuseStep 5909381 = 1108009) (by norm_num)
theorem B4369301 : Blo 1293965 4369301 := bbase (se 6 (by rfl) ⟨102405, by rfl⟩ : syracuseStep 4369301 = 204811) (by norm_num)
theorem B4148117 : Blo 1293965 4148117 := bbase (se 6 (by rfl) ⟨97221, by rfl⟩ : syracuseStep 4148117 = 194443) (by norm_num)
theorem B2952101 : Blo 1293965 2952101 := bbase (se 4 (by rfl) ⟨276759, by rfl⟩ : syracuseStep 2952101 = 553519) (by norm_num)
theorem B4918229 : Blo 1293965 4918229 := bbase (se 7 (by rfl) ⟨57635, by rfl⟩ : syracuseStep 4918229 = 115271) (by norm_num)
theorem B1477693 : Blo 1293965 1477693 := bbase (se 3 (by rfl) ⟨277067, by rfl⟩ : syracuseStep 1477693 = 554135) (by norm_num)
theorem B3279973 : Blo 1293965 3279973 := bbase (se 4 (by rfl) ⟨307497, by rfl⟩ : syracuseStep 3279973 = 614995) (by norm_num)
theorem B2526365 : Blo 1293965 2526365 := bbase (se 3 (by rfl) ⟨473693, by rfl⟩ : syracuseStep 2526365 = 947387) (by norm_num)
theorem B2911445 : Blo 1293965 2911445 := bbase (se 7 (by rfl) ⟨34118, by rfl⟩ : syracuseStep 2911445 = 68237) (by norm_num)
theorem B24882389 : Blo 1293965 24882389 := bbase (se 7 (by rfl) ⟨291590, by rfl⟩ : syracuseStep 24882389 = 583181) (by norm_num)
theorem B3280085 : Blo 1293965 3280085 := bbase (se 7 (by rfl) ⟨38438, by rfl⟩ : syracuseStep 3280085 = 76877) (by norm_num)
theorem B2075885 : Blo 1293965 2075885 := bbase (se 3 (by rfl) ⟨389228, by rfl⟩ : syracuseStep 2075885 = 778457) (by norm_num)
theorem B6556949 : Blo 1293965 6556949 := bbase (se 6 (by rfl) ⟨153678, by rfl⟩ : syracuseStep 6556949 = 307357) (by norm_num)
theorem B2911517 : Blo 1293965 2911517 := bbase (se 3 (by rfl) ⟨545909, by rfl⟩ : syracuseStep 2911517 = 1091819) (by norm_num)
theorem B2764061 : Blo 1293965 2764061 := bbase (se 3 (by rfl) ⟨518261, by rfl⟩ : syracuseStep 2764061 = 1036523) (by norm_num)
theorem B4369733 : Blo 1293965 4369733 := bbase (se 4 (by rfl) ⟨409662, by rfl⟩ : syracuseStep 4369733 = 819325) (by norm_num)
theorem B2911589 : Blo 1293965 2911589 := bbase (se 4 (by rfl) ⟨272961, by rfl⟩ : syracuseStep 2911589 = 545923) (by norm_num)
theorem B2764181 : Blo 1293965 2764181 := bbase (se 6 (by rfl) ⟨64785, by rfl⟩ : syracuseStep 2764181 = 129571) (by norm_num)
theorem B8301973 : Blo 1293965 8301973 := bbase (se 6 (by rfl) ⟨194577, by rfl⟩ : syracuseStep 8301973 = 389155) (by norm_num)
theorem B3280277 : Blo 1293965 3280277 := bbase (se 6 (by rfl) ⟨76881, by rfl⟩ : syracuseStep 3280277 = 153763) (by norm_num)
theorem B2911661 : Blo 1293965 2911661 := bbase (se 3 (by rfl) ⟨545936, by rfl⟩ : syracuseStep 2911661 = 1091873) (by norm_num)
theorem B2911733 : Blo 1293965 2911733 := bbase (se 5 (by rfl) ⟨136487, by rfl⟩ : syracuseStep 2911733 = 272975) (by norm_num)
theorem B2911805 : Blo 1293965 2911805 := bbase (se 3 (by rfl) ⟨545963, by rfl⟩ : syracuseStep 2911805 = 1091927) (by norm_num)
theorem B1330781 : Blo 1293965 1330781 := bbase (se 3 (by rfl) ⟨249521, by rfl⟩ : syracuseStep 1330781 = 499043) (by norm_num)
theorem B2911877 : Blo 1293965 2911877 := bbase (se 4 (by rfl) ⟨272988, by rfl⟩ : syracuseStep 2911877 = 545977) (by norm_num)
theorem B2911949 : Blo 1293965 2911949 := bbase (se 3 (by rfl) ⟨545990, by rfl⟩ : syracuseStep 2911949 = 1091981) (by norm_num)
theorem B4370165 : Blo 1293965 4370165 := bbase (se 5 (by rfl) ⟨204851, by rfl⟩ : syracuseStep 4370165 = 409703) (by norm_num)
theorem B3321605 : Blo 1293965 3321605 := bbase (se 4 (by rfl) ⟨311400, by rfl⟩ : syracuseStep 3321605 = 622801) (by norm_num)
theorem B2912021 : Blo 1293965 2912021 := bbase (se 6 (by rfl) ⟨68250, by rfl⟩ : syracuseStep 2912021 = 136501) (by norm_num)
theorem B2912093 : Blo 1293965 2912093 := bbase (se 3 (by rfl) ⟨546017, by rfl⟩ : syracuseStep 2912093 = 1092035) (by norm_num)
theorem B4665205 : Blo 1293965 4665205 := bbase (se 5 (by rfl) ⟨218681, by rfl⟩ : syracuseStep 4665205 = 437363) (by norm_num)
theorem B5533589 : Blo 1293965 5533589 := bbase (se 6 (by rfl) ⟨129693, by rfl⟩ : syracuseStep 5533589 = 259387) (by norm_num)
theorem B2912165 : Blo 1293965 2912165 := bbase (se 4 (by rfl) ⟨273015, by rfl⟩ : syracuseStep 2912165 = 546031) (by norm_num)
theorem B2912237 : Blo 1293965 2912237 := bbase (se 3 (by rfl) ⟨546044, by rfl⟩ : syracuseStep 2912237 = 1092089) (by norm_num)
theorem B2764813 : Blo 1293965 2764813 := bbase (se 3 (by rfl) ⟨518402, by rfl⟩ : syracuseStep 2764813 = 1036805) (by norm_num)
theorem B2912309 : Blo 1293965 2912309 := bbase (se 5 (by rfl) ⟨136514, by rfl⟩ : syracuseStep 2912309 = 273029) (by norm_num)
theorem B4919413 : Blo 1293965 4919413 := bbase (se 5 (by rfl) ⟨230597, by rfl⟩ : syracuseStep 4919413 = 461195) (by norm_num)
theorem B2912381 : Blo 1293965 2912381 := bbase (se 3 (by rfl) ⟨546071, by rfl⟩ : syracuseStep 2912381 = 1092143) (by norm_num)
theorem B1577089 : Blo 1293965 1577089 := bbase (se 2 (by rfl) ⟨591408, by rfl⟩ : syracuseStep 1577089 = 1182817) (by norm_num)
theorem B5533829 : Blo 1293965 5533829 := bbase (se 4 (by rfl) ⟨518796, by rfl⟩ : syracuseStep 5533829 = 1037593) (by norm_num)
theorem B4370597 : Blo 1293965 4370597 := bbase (se 4 (by rfl) ⟨409743, by rfl⟩ : syracuseStep 4370597 = 819487) (by norm_num)
theorem B2912453 : Blo 1293965 2912453 := bbase (se 4 (by rfl) ⟨273042, by rfl⟩ : syracuseStep 2912453 = 546085) (by norm_num)
theorem B2912525 : Blo 1293965 2912525 := bbase (se 3 (by rfl) ⟨546098, by rfl⟩ : syracuseStep 2912525 = 1092197) (by norm_num)
theorem B2912597 : Blo 1293965 2912597 := bbase (se 10 (by rfl) ⟨4266, by rfl⟩ : syracuseStep 2912597 = 8533) (by norm_num)
theorem B3109261 : Blo 1293965 3109261 := bbase (se 3 (by rfl) ⟨582986, by rfl⟩ : syracuseStep 3109261 = 1165973) (by norm_num)
theorem B20197781 : Blo 1293965 20197781 := bbase (se 6 (by rfl) ⟨473385, by rfl⟩ : syracuseStep 20197781 = 946771) (by norm_num)
theorem B3322261 : Blo 1293965 3322261 := bbase (se 6 (by rfl) ⟨77865, by rfl⟩ : syracuseStep 3322261 = 155731) (by norm_num)
theorem B2912669 : Blo 1293965 2912669 := bbase (se 3 (by rfl) ⟨546125, by rfl⟩ : syracuseStep 2912669 = 1092251) (by norm_num)
theorem B4919717 : Blo 1293965 4919717 := bbase (se 4 (by rfl) ⟨461223, by rfl⟩ : syracuseStep 4919717 = 922447) (by norm_num)
theorem B18682325 : Blo 1293965 18682325 := bbase (se 7 (by rfl) ⟨218933, by rfl⟩ : syracuseStep 18682325 = 437867) (by norm_num)
theorem B2183645 : Blo 1293965 2183645 := bbase (se 3 (by rfl) ⟨409433, by rfl⟩ : syracuseStep 2183645 = 818867) (by norm_num)
theorem B2912741 : Blo 1293965 2912741 := bbase (se 4 (by rfl) ⟨273069, by rfl⟩ : syracuseStep 2912741 = 546139) (by norm_num)
theorem B2953741 : Blo 1293965 2953741 := bbase (se 3 (by rfl) ⟨553826, by rfl⟩ : syracuseStep 2953741 = 1107653) (by norm_num)
theorem B6558245 : Blo 1293965 6558245 := bbase (se 4 (by rfl) ⟨614835, by rfl⟩ : syracuseStep 6558245 = 1229671) (by norm_num)
theorem B2912813 : Blo 1293965 2912813 := bbase (se 3 (by rfl) ⟨546152, by rfl⟩ : syracuseStep 2912813 = 1092305) (by norm_num)
theorem B4371029 : Blo 1293965 4371029 := bbase (se 8 (by rfl) ⟨25611, by rfl⟩ : syracuseStep 4371029 = 51223) (by norm_num)
theorem B2183773 : Blo 1293965 2183773 := bbase (se 3 (by rfl) ⟨409457, by rfl⟩ : syracuseStep 2183773 = 818915) (by norm_num)
theorem B2912885 : Blo 1293965 2912885 := bbase (se 5 (by rfl) ⟨136541, by rfl⟩ : syracuseStep 2912885 = 273083) (by norm_num)
theorem B3322541 : Blo 1293965 3322541 := bbase (se 3 (by rfl) ⟨622976, by rfl⟩ : syracuseStep 3322541 = 1245953) (by norm_num)
theorem B2183861 : Blo 1293965 2183861 := bbase (se 5 (by rfl) ⟨102368, by rfl⟩ : syracuseStep 2183861 = 204737) (by norm_num)
theorem B2912957 : Blo 1293965 2912957 := bbase (se 3 (by rfl) ⟨546179, by rfl⟩ : syracuseStep 2912957 = 1092359) (by norm_num)
theorem B1774285 : Blo 1293965 1774285 := bbase (se 3 (by rfl) ⟨332678, by rfl⟩ : syracuseStep 1774285 = 665357) (by norm_num)
theorem B11809493 : Blo 1293965 11809493 := bbase (se 7 (by rfl) ⟨138392, by rfl⟩ : syracuseStep 11809493 = 276785) (by norm_num)
theorem B2913029 : Blo 1293965 2913029 := bbase (se 4 (by rfl) ⟨273096, by rfl⟩ : syracuseStep 2913029 = 546193) (by norm_num)
theorem B2183989 : Blo 1293965 2183989 := bbase (se 5 (by rfl) ⟨102374, by rfl⟩ : syracuseStep 2183989 = 204749) (by norm_num)
theorem B2913101 : Blo 1293965 2913101 := bbase (se 3 (by rfl) ⟨546206, by rfl⟩ : syracuseStep 2913101 = 1092413) (by norm_num)
theorem B2765701 : Blo 1293965 2765701 := bbase (se 4 (by rfl) ⟨259284, by rfl⟩ : syracuseStep 2765701 = 518569) (by norm_num)
theorem B2184077 : Blo 1293965 2184077 := bbase (se 3 (by rfl) ⟨409514, by rfl⟩ : syracuseStep 2184077 = 819029) (by norm_num)
theorem B2913173 : Blo 1293965 2913173 := bbase (se 6 (by rfl) ⟨68277, by rfl⟩ : syracuseStep 2913173 = 136555) (by norm_num)
theorem B1495985 : Blo 1293965 1495985 := bbase (se 2 (by rfl) ⟨560994, by rfl⟩ : syracuseStep 1495985 = 1121989) (by norm_num)
theorem B2913245 : Blo 1293965 2913245 := bbase (se 3 (by rfl) ⟨546233, by rfl⟩ : syracuseStep 2913245 = 1092467) (by norm_num)
theorem B1577965 : Blo 1293965 1577965 := bbase (se 3 (by rfl) ⟨295868, by rfl⟩ : syracuseStep 1577965 = 591737) (by norm_num)
theorem B3109877 : Blo 1293965 3109877 := bbase (se 5 (by rfl) ⟨145775, by rfl⟩ : syracuseStep 3109877 = 291551) (by norm_num)
theorem B2765821 : Blo 1293965 2765821 := bbase (se 3 (by rfl) ⟨518591, by rfl⟩ : syracuseStep 2765821 = 1037183) (by norm_num)
theorem B4371461 : Blo 1293965 4371461 := bbase (se 4 (by rfl) ⟨409824, by rfl⟩ : syracuseStep 4371461 = 819649) (by norm_num)
theorem B2184205 : Blo 1293965 2184205 := bbase (se 3 (by rfl) ⟨409538, by rfl⟩ : syracuseStep 2184205 = 819077) (by norm_num)
theorem B2913317 : Blo 1293965 2913317 := bbase (se 4 (by rfl) ⟨273123, by rfl⟩ : syracuseStep 2913317 = 546247) (by norm_num)
theorem B3937349 : Blo 1293965 3937349 := bbase (se 4 (by rfl) ⟨369126, by rfl⟩ : syracuseStep 3937349 = 738253) (by norm_num)
theorem B2184293 : Blo 1293965 2184293 := bbase (se 4 (by rfl) ⟨204777, by rfl⟩ : syracuseStep 2184293 = 409555) (by norm_num)
theorem B2913389 : Blo 1293965 2913389 := bbase (se 3 (by rfl) ⟨546260, by rfl⟩ : syracuseStep 2913389 = 1092521) (by norm_num)
theorem B3110069 : Blo 1293965 3110069 := bbase (se 5 (by rfl) ⟨145784, by rfl⟩ : syracuseStep 3110069 = 291569) (by norm_num)
theorem B2913461 : Blo 1293965 2913461 := bbase (se 5 (by rfl) ⟨136568, by rfl⟩ : syracuseStep 2913461 = 273137) (by norm_num)
theorem B1660105 : Blo 1293965 1660105 := bbase (se 2 (by rfl) ⟨622539, by rfl⟩ : syracuseStep 1660105 = 1245079) (by norm_num)
theorem B2184421 : Blo 1293965 2184421 := bbase (se 4 (by rfl) ⟨204789, by rfl⟩ : syracuseStep 2184421 = 409579) (by norm_num)
theorem B2913533 : Blo 1293965 2913533 := bbase (se 3 (by rfl) ⟨546287, by rfl⟩ : syracuseStep 2913533 = 1092575) (by norm_num)
theorem B2766077 : Blo 1293965 2766077 := bbase (se 3 (by rfl) ⟨518639, by rfl⟩ : syracuseStep 2766077 = 1037279) (by norm_num)
theorem B5248277 : Blo 1293965 5248277 := bbase (se 6 (by rfl) ⟨123006, by rfl⟩ : syracuseStep 5248277 = 246013) (by norm_num)
theorem B3110165 : Blo 1293965 3110165 := bbase (se 6 (by rfl) ⟨72894, by rfl⟩ : syracuseStep 3110165 = 145789) (by norm_num)
theorem B2184509 : Blo 1293965 2184509 := bbase (se 3 (by rfl) ⟨409595, by rfl⟩ : syracuseStep 2184509 = 819191) (by norm_num)
theorem B1750333 : Blo 1293965 1750333 := bbase (se 3 (by rfl) ⟨328187, by rfl⟩ : syracuseStep 1750333 = 656375) (by norm_num)
theorem B2913605 : Blo 1293965 2913605 := bbase (se 4 (by rfl) ⟨273150, by rfl⟩ : syracuseStep 2913605 = 546301) (by norm_num)
theorem B2913677 : Blo 1293965 2913677 := bbase (se 3 (by rfl) ⟨546314, by rfl⟩ : syracuseStep 2913677 = 1092629) (by norm_num)
theorem B4371893 : Blo 1293965 4371893 := bbase (se 5 (by rfl) ⟨204932, by rfl⟩ : syracuseStep 4371893 = 409865) (by norm_num)
theorem B1381817 : Blo 1293965 1381817 := bbase (se 2 (by rfl) ⟨518181, by rfl⟩ : syracuseStep 1381817 = 1036363) (by norm_num)
theorem B2184637 : Blo 1293965 2184637 := bbase (se 3 (by rfl) ⟨409619, by rfl⟩ : syracuseStep 2184637 = 819239) (by norm_num)
theorem B2913749 : Blo 1293965 2913749 := bbase (se 7 (by rfl) ⟨34145, by rfl⟩ : syracuseStep 2913749 = 68291) (by norm_num)
theorem B2397701 : Blo 1293965 2397701 := bbase (se 4 (by rfl) ⟨224784, by rfl⟩ : syracuseStep 2397701 = 449569) (by norm_num)
theorem B2184725 : Blo 1293965 2184725 := bbase (se 6 (by rfl) ⟨51204, by rfl⟩ : syracuseStep 2184725 = 102409) (by norm_num)
theorem B2913821 : Blo 1293965 2913821 := bbase (se 3 (by rfl) ⟨546341, by rfl⟩ : syracuseStep 2913821 = 1092683) (by norm_num)
theorem B1381945 : Blo 1293965 1381945 := bbase (se 2 (by rfl) ⟨518229, by rfl⟩ : syracuseStep 1381945 = 1036459) (by norm_num)
theorem B2913893 : Blo 1293965 2913893 := bbase (se 4 (by rfl) ⟨273177, by rfl⟩ : syracuseStep 2913893 = 546355) (by norm_num)
theorem B4150885 : Blo 1293965 4150885 := bbase (se 4 (by rfl) ⟨389145, by rfl⟩ : syracuseStep 4150885 = 778291) (by norm_num)
theorem B1455745 : Blo 1293965 1455745 := bbase (se 2 (by rfl) ⟨545904, by rfl⟩ : syracuseStep 1455745 = 1091809) (by norm_num)
theorem B2184853 : Blo 1293965 2184853 := bbase (se 6 (by rfl) ⟨51207, by rfl⟩ : syracuseStep 2184853 = 102415) (by norm_num)
theorem B2954909 : Blo 1293965 2954909 := bbase (se 3 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 2954909 = 1108091) (by norm_num)
theorem B1455781 : Blo 1293965 1455781 := bbase (se 4 (by rfl) ⟨136479, by rfl⟩ : syracuseStep 1455781 = 272959) (by norm_num)
theorem B2913965 : Blo 1293965 2913965 := bbase (se 3 (by rfl) ⟨546368, by rfl⟩ : syracuseStep 2913965 = 1092737) (by norm_num)
theorem B1455817 : Blo 1293965 1455817 := bbase (se 2 (by rfl) ⟨545931, by rfl⟩ : syracuseStep 1455817 = 1091863) (by norm_num)
theorem B1455853 : Blo 1293965 1455853 := bbase (se 3 (by rfl) ⟨272972, by rfl⟩ : syracuseStep 1455853 = 545945) (by norm_num)
theorem B2184941 : Blo 1293965 2184941 := bbase (se 3 (by rfl) ⟨409676, by rfl⟩ : syracuseStep 2184941 = 819353) (by norm_num)
theorem B8296181 : Blo 1293965 8296181 := bbase (se 5 (by rfl) ⟨388883, by rfl⟩ : syracuseStep 8296181 = 777767) (by norm_num)
theorem B2914037 : Blo 1293965 2914037 := bbase (se 5 (by rfl) ⟨136595, by rfl⟩ : syracuseStep 2914037 = 273191) (by norm_num)
theorem B1455889 : Blo 1293965 1455889 := bbase (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) (by norm_num)
theorem B1455925 : Blo 1293965 1455925 := bbase (se 5 (by rfl) ⟨68246, by rfl⟩ : syracuseStep 1455925 = 136493) (by norm_num)
theorem B6559541 : Blo 1293965 6559541 := bbase (se 5 (by rfl) ⟨307478, by rfl⟩ : syracuseStep 6559541 = 614957) (by norm_num)
theorem B2914109 : Blo 1293965 2914109 := bbase (se 3 (by rfl) ⟨546395, by rfl⟩ : syracuseStep 2914109 = 1092791) (by norm_num)
theorem B1455961 : Blo 1293965 1455961 := bbase (se 2 (by rfl) ⟨545985, by rfl⟩ : syracuseStep 1455961 = 1091971) (by norm_num)
theorem B4372325 : Blo 1293965 4372325 := bbase (se 4 (by rfl) ⟨409905, by rfl⟩ : syracuseStep 4372325 = 819811) (by norm_num)
theorem B2185069 : Blo 1293965 2185069 := bbase (se 3 (by rfl) ⟨409700, by rfl⟩ : syracuseStep 2185069 = 819401) (by norm_num)
theorem B1455997 : Blo 1293965 1455997 := bbase (se 3 (by rfl) ⟨272999, by rfl⟩ : syracuseStep 1455997 = 545999) (by norm_num)
theorem B2914181 : Blo 1293965 2914181 := bbase (se 4 (by rfl) ⟨273204, by rfl⟩ : syracuseStep 2914181 = 546409) (by norm_num)
theorem B1456033 : Blo 1293965 1456033 := bbase (se 2 (by rfl) ⟨546012, by rfl⟩ : syracuseStep 1456033 = 1092025) (by norm_num)
theorem B1456069 : Blo 1293965 1456069 := bbase (se 4 (by rfl) ⟨136506, by rfl⟩ : syracuseStep 1456069 = 273013) (by norm_num)
theorem B2185157 : Blo 1293965 2185157 := bbase (se 4 (by rfl) ⟨204858, by rfl⟩ : syracuseStep 2185157 = 409717) (by norm_num)
theorem B2914253 : Blo 1293965 2914253 := bbase (se 3 (by rfl) ⟨546422, by rfl⟩ : syracuseStep 2914253 = 1092845) (by norm_num)
theorem B15759317 : Blo 1293965 15759317 := bbase (se 7 (by rfl) ⟨184679, by rfl⟩ : syracuseStep 15759317 = 369359) (by norm_num)
theorem B1456105 : Blo 1293965 1456105 := bbase (se 2 (by rfl) ⟨546039, by rfl⟩ : syracuseStep 1456105 = 1092079) (by norm_num)
theorem B5527541 : Blo 1293965 5527541 := bbase (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) (by norm_num)
theorem B1382389 : Blo 1293965 1382389 := bbase (se 5 (by rfl) ⟨64799, by rfl⟩ : syracuseStep 1382389 = 129599) (by norm_num)
theorem B1456141 : Blo 1293965 1456141 := bbase (se 3 (by rfl) ⟨273026, by rfl⟩ : syracuseStep 1456141 = 546053) (by norm_num)
theorem B1751053 : Blo 1293965 1751053 := bbase (se 3 (by rfl) ⟨328322, by rfl⟩ : syracuseStep 1751053 = 656645) (by norm_num)
theorem B2914325 : Blo 1293965 2914325 := bbase (se 6 (by rfl) ⟨68304, by rfl⟩ : syracuseStep 2914325 = 136609) (by norm_num)
theorem B1456177 : Blo 1293965 1456177 := bbase (se 2 (by rfl) ⟨546066, by rfl⟩ : syracuseStep 1456177 = 1092133) (by norm_num)
theorem B2185285 : Blo 1293965 2185285 := bbase (se 4 (by rfl) ⟨204870, by rfl⟩ : syracuseStep 2185285 = 409741) (by norm_num)
theorem B1456213 : Blo 1293965 1456213 := bbase (se 8 (by rfl) ⟨8532, by rfl⟩ : syracuseStep 1456213 = 17065) (by norm_num)
theorem B2914397 : Blo 1293965 2914397 := bbase (se 3 (by rfl) ⟨546449, by rfl⟩ : syracuseStep 2914397 = 1092899) (by norm_num)
theorem B1382509 : Blo 1293965 1382509 := bbase (se 3 (by rfl) ⟨259220, by rfl⟩ : syracuseStep 1382509 = 518441) (by norm_num)
theorem B2766965 : Blo 1293965 2766965 := bbase (se 5 (by rfl) ⟨129701, by rfl⟩ : syracuseStep 2766965 = 259403) (by norm_num)
theorem B1456249 : Blo 1293965 1456249 := bbase (se 2 (by rfl) ⟨546093, by rfl⟩ : syracuseStep 1456249 = 1092187) (by norm_num)
theorem B1456285 : Blo 1293965 1456285 := bbase (se 3 (by rfl) ⟨273053, by rfl⟩ : syracuseStep 1456285 = 546107) (by norm_num)
theorem B2185373 : Blo 1293965 2185373 := bbase (se 3 (by rfl) ⟨409757, by rfl⟩ : syracuseStep 2185373 = 819515) (by norm_num)
theorem B2914469 : Blo 1293965 2914469 := bbase (se 4 (by rfl) ⟨273231, by rfl⟩ : syracuseStep 2914469 = 546463) (by norm_num)
theorem B1456321 : Blo 1293965 1456321 := bbase (se 2 (by rfl) ⟨546120, by rfl⟩ : syracuseStep 1456321 = 1092241) (by norm_num)
theorem B6551765 : Blo 1293965 6551765 := bbase (se 7 (by rfl) ⟨76778, by rfl⟩ : syracuseStep 6551765 = 153557) (by norm_num)
theorem B1456357 : Blo 1293965 1456357 := bbase (se 4 (by rfl) ⟨136533, by rfl⟩ : syracuseStep 1456357 = 273067) (by norm_num)
theorem B2914541 : Blo 1293965 2914541 := bbase (se 3 (by rfl) ⟨546476, by rfl⟩ : syracuseStep 2914541 = 1092953) (by norm_num)
theorem B1456393 : Blo 1293965 1456393 := bbase (se 2 (by rfl) ⟨546147, by rfl⟩ : syracuseStep 1456393 = 1092295) (by norm_num)
theorem B4372757 : Blo 1293965 4372757 := bbase (se 6 (by rfl) ⟨102486, by rfl⟩ : syracuseStep 4372757 = 204973) (by norm_num)
theorem B2185501 : Blo 1293965 2185501 := bbase (se 3 (by rfl) ⟨409781, by rfl⟩ : syracuseStep 2185501 = 819563) (by norm_num)
theorem B1456429 : Blo 1293965 1456429 := bbase (se 3 (by rfl) ⟨273080, by rfl⟩ : syracuseStep 1456429 = 546161) (by norm_num)
theorem B2914613 : Blo 1293965 2914613 := bbase (se 5 (by rfl) ⟨136622, by rfl⟩ : syracuseStep 2914613 = 273245) (by norm_num)
theorem B1554761 : Blo 1293965 1554761 := bbase (se 2 (by rfl) ⟨583035, by rfl⟩ : syracuseStep 1554761 = 1166071) (by norm_num)
theorem B1456465 : Blo 1293965 1456465 := bbase (se 2 (by rfl) ⟨546174, by rfl⟩ : syracuseStep 1456465 = 1092349) (by norm_num)
theorem B2767205 : Blo 1293965 2767205 := bbase (se 4 (by rfl) ⟨259425, by rfl⟩ : syracuseStep 2767205 = 518851) (by norm_num)
theorem B1382761 : Blo 1293965 1382761 := bbase (se 2 (by rfl) ⟨518535, by rfl⟩ : syracuseStep 1382761 = 1037071) (by norm_num)
theorem B1382765 : Blo 1293965 1382765 := bbase (se 3 (by rfl) ⟨259268, by rfl⟩ : syracuseStep 1382765 = 518537) (by norm_num)
theorem B1456501 : Blo 1293965 1456501 := bbase (se 5 (by rfl) ⟨68273, by rfl⟩ : syracuseStep 1456501 = 136547) (by norm_num)
theorem B2185589 : Blo 1293965 2185589 := bbase (se 5 (by rfl) ⟨102449, by rfl⟩ : syracuseStep 2185589 = 204899) (by norm_num)
theorem B2914685 : Blo 1293965 2914685 := bbase (se 3 (by rfl) ⟨546503, by rfl⟩ : syracuseStep 2914685 = 1093007) (by norm_num)
theorem B1456537 : Blo 1293965 1456537 := bbase (se 2 (by rfl) ⟨546201, by rfl⟩ : syracuseStep 1456537 = 1092403) (by norm_num)
theorem B1661357 : Blo 1293965 1661357 := bbase (se 3 (by rfl) ⟨311504, by rfl⟩ : syracuseStep 1661357 = 623009) (by norm_num)
theorem B1456573 : Blo 1293965 1456573 := bbase (se 3 (by rfl) ⟨273107, by rfl⟩ : syracuseStep 1456573 = 546215) (by norm_num)
theorem B2914757 : Blo 1293965 2914757 := bbase (se 4 (by rfl) ⟨273258, by rfl⟩ : syracuseStep 2914757 = 546517) (by norm_num)
theorem B1456609 : Blo 1293965 1456609 := bbase (se 2 (by rfl) ⟨546228, by rfl⟩ : syracuseStep 1456609 = 1092457) (by norm_num)
theorem B2185717 : Blo 1293965 2185717 := bbase (se 5 (by rfl) ⟨102455, by rfl⟩ : syracuseStep 2185717 = 204911) (by norm_num)
theorem B1456645 : Blo 1293965 1456645 := bbase (se 4 (by rfl) ⟨136560, by rfl⟩ : syracuseStep 1456645 = 273121) (by norm_num)
theorem B2914829 : Blo 1293965 2914829 := bbase (se 3 (by rfl) ⟨546530, by rfl⟩ : syracuseStep 2914829 = 1093061) (by norm_num)
theorem B1456681 : Blo 1293965 1456681 := bbase (se 2 (by rfl) ⟨546255, by rfl⟩ : syracuseStep 1456681 = 1092511) (by norm_num)
theorem B1456717 : Blo 1293965 1456717 := bbase (se 3 (by rfl) ⟨273134, by rfl⟩ : syracuseStep 1456717 = 546269) (by norm_num)
theorem B2185805 : Blo 1293965 2185805 := bbase (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) (by norm_num)
theorem B2914901 : Blo 1293965 2914901 := bbase (se 8 (by rfl) ⟨17079, by rfl⟩ : syracuseStep 2914901 = 34159) (by norm_num)
theorem B1456753 : Blo 1293965 1456753 := bbase (se 2 (by rfl) ⟨546282, by rfl⟩ : syracuseStep 1456753 = 1092565) (by norm_num)
theorem B1456789 : Blo 1293965 1456789 := bbase (se 6 (by rfl) ⟨34143, by rfl⟩ : syracuseStep 1456789 = 68287) (by norm_num)
theorem B2914973 : Blo 1293965 2914973 := bbase (se 3 (by rfl) ⟨546557, by rfl⟩ : syracuseStep 2914973 = 1093115) (by norm_num)
theorem B3275437 : Blo 1293965 3275437 := bbase (se 3 (by rfl) ⟨614144, by rfl⟩ : syracuseStep 3275437 = 1228289) (by norm_num)
theorem B1456825 : Blo 1293965 1456825 := bbase (se 2 (by rfl) ⟨546309, by rfl⟩ : syracuseStep 1456825 = 1092619) (by norm_num)
theorem B4668101 : Blo 1293965 4668101 := bbase (se 4 (by rfl) ⟨437634, by rfl⟩ : syracuseStep 4668101 = 875269) (by norm_num)
theorem B4373189 : Blo 1293965 4373189 := bbase (se 4 (by rfl) ⟨409986, by rfl⟩ : syracuseStep 4373189 = 819973) (by norm_num)
theorem B2185933 : Blo 1293965 2185933 := bbase (se 3 (by rfl) ⟨409862, by rfl⟩ : syracuseStep 2185933 = 819725) (by norm_num)
theorem B6224597 : Blo 1293965 6224597 := bbase (se 7 (by rfl) ⟨72944, by rfl⟩ : syracuseStep 6224597 = 145889) (by norm_num)
theorem B1456861 : Blo 1293965 1456861 := bbase (se 3 (by rfl) ⟨273161, by rfl⟩ : syracuseStep 1456861 = 546323) (by norm_num)
theorem B2915045 : Blo 1293965 2915045 := bbase (se 4 (by rfl) ⟨273285, by rfl⟩ : syracuseStep 2915045 = 546571) (by norm_num)
theorem B1456897 : Blo 1293965 1456897 := bbase (se 2 (by rfl) ⟨546336, by rfl⟩ : syracuseStep 1456897 = 1092673) (by norm_num)
theorem B3275549 : Blo 1293965 3275549 := bbase (se 3 (by rfl) ⟨614165, by rfl⟩ : syracuseStep 3275549 = 1228331) (by norm_num)
theorem B1456933 : Blo 1293965 1456933 := bbase (se 4 (by rfl) ⟨136587, by rfl⟩ : syracuseStep 1456933 = 273175) (by norm_num)
theorem B2186021 : Blo 1293965 2186021 := bbase (se 4 (by rfl) ⟨204939, by rfl⟩ : syracuseStep 2186021 = 409879) (by norm_num)
theorem B2915117 : Blo 1293965 2915117 := bbase (se 3 (by rfl) ⟨546584, by rfl⟩ : syracuseStep 2915117 = 1093169) (by norm_num)
theorem B1456969 : Blo 1293965 1456969 := bbase (se 2 (by rfl) ⟨546363, by rfl⟩ : syracuseStep 1456969 = 1092727) (by norm_num)
theorem B2767709 : Blo 1293965 2767709 := bbase (se 3 (by rfl) ⟨518945, by rfl⟩ : syracuseStep 2767709 = 1037891) (by norm_num)
theorem B2767717 : Blo 1293965 2767717 := bbase (se 4 (by rfl) ⟨259473, by rfl⟩ : syracuseStep 2767717 = 518947) (by norm_num)
theorem B1457005 : Blo 1293965 1457005 := bbase (se 3 (by rfl) ⟨273188, by rfl⟩ : syracuseStep 1457005 = 546377) (by norm_num)
theorem B2915189 : Blo 1293965 2915189 := bbase (se 5 (by rfl) ⟨136649, by rfl⟩ : syracuseStep 2915189 = 273299) (by norm_num)
theorem B4914053 : Blo 1293965 4914053 := bbase (se 4 (by rfl) ⟨460692, by rfl⟩ : syracuseStep 4914053 = 921385) (by norm_num)
theorem B1457041 : Blo 1293965 1457041 := bbase (se 2 (by rfl) ⟨546390, by rfl⟩ : syracuseStep 1457041 = 1092781) (by norm_num)
theorem B1383329 : Blo 1293965 1383329 := bbase (se 2 (by rfl) ⟨518748, by rfl⟩ : syracuseStep 1383329 = 1037497) (by norm_num)
theorem B2186149 : Blo 1293965 2186149 := bbase (se 4 (by rfl) ⟨204951, by rfl⟩ : syracuseStep 2186149 = 409903) (by norm_num)
theorem B3685301 : Blo 1293965 3685301 := bbase (se 5 (by rfl) ⟨172748, by rfl⟩ : syracuseStep 3685301 = 345497) (by norm_num)
theorem B1457077 : Blo 1293965 1457077 := bbase (se 5 (by rfl) ⟨68300, by rfl⟩ : syracuseStep 1457077 = 136601) (by norm_num)
theorem B2915261 : Blo 1293965 2915261 := bbase (se 3 (by rfl) ⟨546611, by rfl⟩ : syracuseStep 2915261 = 1093223) (by norm_num)
theorem B1457113 : Blo 1293965 1457113 := bbase (se 2 (by rfl) ⟨546417, by rfl⟩ : syracuseStep 1457113 = 1092835) (by norm_num)
theorem B3275741 : Blo 1293965 3275741 := bbase (se 3 (by rfl) ⟨614201, by rfl⟩ : syracuseStep 3275741 = 1228403) (by norm_num)
theorem B1555453 : Blo 1293965 1555453 := bbase (se 3 (by rfl) ⟨291647, by rfl⟩ : syracuseStep 1555453 = 583295) (by norm_num)
theorem B1457149 : Blo 1293965 1457149 := bbase (se 3 (by rfl) ⟨273215, by rfl⟩ : syracuseStep 1457149 = 546431) (by norm_num)
theorem B2186237 : Blo 1293965 2186237 := bbase (se 3 (by rfl) ⟨409919, by rfl⟩ : syracuseStep 2186237 = 819839) (by norm_num)
theorem B1555457 : Blo 1293965 1555457 := bbase (se 2 (by rfl) ⟨583296, by rfl⟩ : syracuseStep 1555457 = 1166593) (by norm_num)
theorem B2915333 : Blo 1293965 2915333 := bbase (se 4 (by rfl) ⟨273312, by rfl⟩ : syracuseStep 2915333 = 546625) (by norm_num)
theorem B1457185 : Blo 1293965 1457185 := bbase (se 2 (by rfl) ⟨546444, by rfl⟩ : syracuseStep 1457185 = 1092889) (by norm_num)
theorem B5905477 : Blo 1293965 5905477 := bbase (se 4 (by rfl) ⟨553638, by rfl⟩ : syracuseStep 5905477 = 1107277) (by norm_num)
theorem B1457221 : Blo 1293965 1457221 := bbase (se 4 (by rfl) ⟨136614, by rfl⟩ : syracuseStep 1457221 = 273229) (by norm_num)
theorem B2915405 : Blo 1293965 2915405 := bbase (se 3 (by rfl) ⟨546638, by rfl⟩ : syracuseStep 2915405 = 1093277) (by norm_num)
theorem B2456669 : Blo 1293965 2456669 := bbase (se 3 (by rfl) ⟨460625, by rfl⟩ : syracuseStep 2456669 = 921251) (by norm_num)
theorem B1383517 : Blo 1293965 1383517 := bbase (se 3 (by rfl) ⟨259409, by rfl⟩ : syracuseStep 1383517 = 518819) (by norm_num)
theorem B1457257 : Blo 1293965 1457257 := bbase (se 2 (by rfl) ⟨546471, by rfl⟩ : syracuseStep 1457257 = 1092943) (by norm_num)
theorem B4373621 : Blo 1293965 4373621 := bbase (se 5 (by rfl) ⟨205013, by rfl⟩ : syracuseStep 4373621 = 410027) (by norm_num)
theorem B2186365 : Blo 1293965 2186365 := bbase (se 3 (by rfl) ⟨409943, by rfl⟩ : syracuseStep 2186365 = 819887) (by norm_num)
theorem B1457293 : Blo 1293965 1457293 := bbase (se 3 (by rfl) ⟨273242, by rfl⟩ : syracuseStep 1457293 = 546485) (by norm_num)
theorem B2915477 : Blo 1293965 2915477 := bbase (se 6 (by rfl) ⟨68331, by rfl⟩ : syracuseStep 2915477 = 136663) (by norm_num)
theorem B4914341 : Blo 1293965 4914341 := bbase (se 4 (by rfl) ⟨460719, by rfl⟩ : syracuseStep 4914341 = 921439) (by norm_num)
theorem B1457329 : Blo 1293965 1457329 := bbase (se 2 (by rfl) ⟨546498, by rfl⟩ : syracuseStep 1457329 = 1092997) (by norm_num)
theorem B1457365 : Blo 1293965 1457365 := bbase (se 7 (by rfl) ⟨17078, by rfl⟩ : syracuseStep 1457365 = 34157) (by norm_num)
theorem B2186453 : Blo 1293965 2186453 := bbase (se 7 (by rfl) ⟨25622, by rfl⟩ : syracuseStep 2186453 = 51245) (by norm_num)
theorem B2915549 : Blo 1293965 2915549 := bbase (se 3 (by rfl) ⟨546665, by rfl⟩ : syracuseStep 2915549 = 1093331) (by norm_num)
theorem B2456821 : Blo 1293965 2456821 := bbase (se 5 (by rfl) ⟨115163, by rfl⟩ : syracuseStep 2456821 = 230327) (by norm_num)
theorem B1457401 : Blo 1293965 1457401 := bbase (se 2 (by rfl) ⟨546525, by rfl⟩ : syracuseStep 1457401 = 1093051) (by norm_num)
theorem B1457437 : Blo 1293965 1457437 := bbase (se 3 (by rfl) ⟨273269, by rfl⟩ : syracuseStep 1457437 = 546539) (by norm_num)
theorem B2915621 : Blo 1293965 2915621 := bbase (se 4 (by rfl) ⟨273339, by rfl⟩ : syracuseStep 2915621 = 546679) (by norm_num)
theorem B3276085 : Blo 1293965 3276085 := bbase (se 5 (by rfl) ⟨153566, by rfl⟩ : syracuseStep 3276085 = 307133) (by norm_num)
theorem B1457473 : Blo 1293965 1457473 := bbase (se 2 (by rfl) ⟨546552, by rfl⟩ : syracuseStep 1457473 = 1093105) (by norm_num)
theorem B2186581 : Blo 1293965 2186581 := bbase (se 11 (by rfl) ⟨1601, by rfl⟩ : syracuseStep 2186581 = 3203) (by norm_num)
theorem B3685733 : Blo 1293965 3685733 := bbase (se 4 (by rfl) ⟨345537, by rfl⟩ : syracuseStep 3685733 = 691075) (by norm_num)
theorem B1457509 : Blo 1293965 1457509 := bbase (se 4 (by rfl) ⟨136641, by rfl⟩ : syracuseStep 1457509 = 273283) (by norm_num)
theorem B2915693 : Blo 1293965 2915693 := bbase (se 3 (by rfl) ⟨546692, by rfl⟩ : syracuseStep 2915693 = 1093385) (by norm_num)
theorem B1637749 : Blo 1293965 1637749 := bbase (se 5 (by rfl) ⟨76769, by rfl⟩ : syracuseStep 1637749 = 153539) (by norm_num)
theorem B1457545 : Blo 1293965 1457545 := bbase (se 2 (by rfl) ⟨546579, by rfl⟩ : syracuseStep 1457545 = 1093159) (by norm_num)
theorem B2334109 : Blo 1293965 2334109 := bbase (se 3 (by rfl) ⟨437645, by rfl⟩ : syracuseStep 2334109 = 875291) (by norm_num)
theorem B3276197 : Blo 1293965 3276197 := bbase (se 4 (by rfl) ⟨307143, by rfl⟩ : syracuseStep 3276197 = 614287) (by norm_num)
theorem B4431269 : Blo 1293965 4431269 := bbase (se 4 (by rfl) ⟨415431, by rfl⟩ : syracuseStep 4431269 = 830863) (by norm_num)
theorem B1457581 : Blo 1293965 1457581 := bbase (se 3 (by rfl) ⟨273296, by rfl⟩ : syracuseStep 1457581 = 546593) (by norm_num)
theorem B2186669 : Blo 1293965 2186669 := bbase (se 3 (by rfl) ⟨410000, by rfl⟩ : syracuseStep 2186669 = 820001) (by norm_num)
theorem B2915765 : Blo 1293965 2915765 := bbase (se 5 (by rfl) ⟨136676, by rfl⟩ : syracuseStep 2915765 = 273353) (by norm_num)
theorem B1457617 : Blo 1293965 1457617 := bbase (se 2 (by rfl) ⟨546606, by rfl⟩ : syracuseStep 1457617 = 1093213) (by norm_num)
theorem B1940957 : Blo 1293965 1940957 := bbase (se 3 (by rfl) ⟨363929, by rfl⟩ : syracuseStep 1940957 = 727859) (by norm_num)
theorem B6553061 : Blo 1293965 6553061 := bbase (se 4 (by rfl) ⟨614349, by rfl⟩ : syracuseStep 6553061 = 1228699) (by norm_num)
theorem B1662445 : Blo 1293965 1662445 := bbase (se 3 (by rfl) ⟨311708, by rfl⟩ : syracuseStep 1662445 = 623417) (by norm_num)
theorem B1940981 : Blo 1293965 1940981 := bbase (se 5 (by rfl) ⟨90983, by rfl⟩ : syracuseStep 1940981 = 181967) (by norm_num)
theorem B1555957 : Blo 1293965 1555957 := bbase (se 5 (by rfl) ⟨72935, by rfl⟩ : syracuseStep 1555957 = 145871) (by norm_num)
theorem B1457653 : Blo 1293965 1457653 := bbase (se 5 (by rfl) ⟨68327, by rfl⟩ : syracuseStep 1457653 = 136655) (by norm_num)
theorem B2915837 : Blo 1293965 2915837 := bbase (se 3 (by rfl) ⟨546719, by rfl⟩ : syracuseStep 2915837 = 1093439) (by norm_num)
theorem B1941005 : Blo 1293965 1941005 := bbase (se 3 (by rfl) ⟨363938, by rfl⟩ : syracuseStep 1941005 = 727877) (by norm_num)
theorem B1457689 : Blo 1293965 1457689 := bbase (se 2 (by rfl) ⟨546633, by rfl⟩ : syracuseStep 1457689 = 1093267) (by norm_num)
theorem B1637921 : Blo 1293965 1637921 := bbase (se 2 (by rfl) ⟨614220, by rfl⟩ : syracuseStep 1637921 = 1228441) (by norm_num)
theorem B1941029 : Blo 1293965 1941029 := bbase (se 4 (by rfl) ⟨181971, by rfl⟩ : syracuseStep 1941029 = 363943) (by norm_num)
theorem B2457125 : Blo 1293965 2457125 := bbase (se 4 (by rfl) ⟨230355, by rfl⟩ : syracuseStep 2457125 = 460711) (by norm_num)
theorem B2334253 : Blo 1293965 2334253 := bbase (se 3 (by rfl) ⟨437672, by rfl⟩ : syracuseStep 2334253 = 875345) (by norm_num)
theorem B2186797 : Blo 1293965 2186797 := bbase (se 3 (by rfl) ⟨410024, by rfl⟩ : syracuseStep 2186797 = 820049) (by norm_num)
theorem B1941053 : Blo 1293965 1941053 := bbase (se 3 (by rfl) ⟨363947, by rfl⟩ : syracuseStep 1941053 = 727895) (by norm_num)
theorem B1457725 : Blo 1293965 1457725 := bbase (se 3 (by rfl) ⟨273323, by rfl⟩ : syracuseStep 1457725 = 546647) (by norm_num)
theorem B2915909 : Blo 1293965 2915909 := bbase (se 4 (by rfl) ⟨273366, by rfl⟩ : syracuseStep 2915909 = 546733) (by norm_num)
theorem B1941077 : Blo 1293965 1941077 := bbase (se 8 (by rfl) ⟨11373, by rfl⟩ : syracuseStep 1941077 = 22747) (by norm_num)
theorem B1637977 : Blo 1293965 1637977 := bbase (se 2 (by rfl) ⟨614241, by rfl⟩ : syracuseStep 1637977 = 1228483) (by norm_num)
theorem B1457761 : Blo 1293965 1457761 := bbase (se 2 (by rfl) ⟨546660, by rfl⟩ : syracuseStep 1457761 = 1093321) (by norm_num)
theorem B3276389 : Blo 1293965 3276389 := bbase (se 4 (by rfl) ⟨307161, by rfl⟩ : syracuseStep 3276389 = 614323) (by norm_num)
theorem B1941101 : Blo 1293965 1941101 := bbase (se 3 (by rfl) ⟨363956, by rfl⟩ : syracuseStep 1941101 = 727913) (by norm_num)
theorem B2842229 : Blo 1293965 2842229 := bbase (se 5 (by rfl) ⟨133229, by rfl⟩ : syracuseStep 2842229 = 266459) (by norm_num)
theorem B1941125 : Blo 1293965 1941125 := bbase (se 4 (by rfl) ⟨181980, by rfl⟩ : syracuseStep 1941125 = 363961) (by norm_num)
theorem B1457797 : Blo 1293965 1457797 := bbase (se 4 (by rfl) ⟨136668, by rfl⟩ : syracuseStep 1457797 = 273337) (by norm_num)
theorem B2186885 : Blo 1293965 2186885 := bbase (se 4 (by rfl) ⟨205020, by rfl⟩ : syracuseStep 2186885 = 410041) (by norm_num)
theorem B3112597 : Blo 1293965 3112597 := bbase (se 6 (by rfl) ⟨72951, by rfl⟩ : syracuseStep 3112597 = 145903) (by norm_num)
theorem B1941149 : Blo 1293965 1941149 := bbase (se 3 (by rfl) ⟨363965, by rfl⟩ : syracuseStep 1941149 = 727931) (by norm_num)
theorem B1457833 : Blo 1293965 1457833 := bbase (se 2 (by rfl) ⟨546687, by rfl⟩ : syracuseStep 1457833 = 1093375) (by norm_num)
theorem B1941173 : Blo 1293965 1941173 := bbase (se 5 (by rfl) ⟨90992, by rfl⟩ : syracuseStep 1941173 = 181985) (by norm_num)
theorem B1638073 : Blo 1293965 1638073 := bbase (se 2 (by rfl) ⟨614277, by rfl⟩ : syracuseStep 1638073 = 1228555) (by norm_num)
theorem B1941197 : Blo 1293965 1941197 := bbase (se 3 (by rfl) ⟨363974, by rfl⟩ : syracuseStep 1941197 = 727949) (by norm_num)
theorem B2334413 : Blo 1293965 2334413 := bbase (se 3 (by rfl) ⟨437702, by rfl⟩ : syracuseStep 2334413 = 875405) (by norm_num)
theorem B1457869 : Blo 1293965 1457869 := bbase (se 3 (by rfl) ⟨273350, by rfl⟩ : syracuseStep 1457869 = 546701) (by norm_num)
theorem B1941221 : Blo 1293965 1941221 := bbase (se 4 (by rfl) ⟨181989, by rfl⟩ : syracuseStep 1941221 = 363979) (by norm_num)
theorem B1457905 : Blo 1293965 1457905 := bbase (se 2 (by rfl) ⟨546714, by rfl⟩ : syracuseStep 1457905 = 1093429) (by norm_num)
theorem B1941245 : Blo 1293965 1941245 := bbase (se 3 (by rfl) ⟨363983, by rfl⟩ : syracuseStep 1941245 = 727967) (by norm_num)
theorem B2334469 : Blo 1293965 2334469 := bbase (se 4 (by rfl) ⟨218856, by rfl⟩ : syracuseStep 2334469 = 437713) (by norm_num)
theorem B1941269 : Blo 1293965 1941269 := bbase (se 6 (by rfl) ⟨45498, by rfl⟩ : syracuseStep 1941269 = 90997) (by norm_num)
theorem B1457941 : Blo 1293965 1457941 := bbase (se 6 (by rfl) ⟨34170, by rfl⟩ : syracuseStep 1457941 = 68341) (by norm_num)
theorem B1941293 : Blo 1293965 1941293 := bbase (se 3 (by rfl) ⟨363992, by rfl⟩ : syracuseStep 1941293 = 727985) (by norm_num)
theorem B1941317 : Blo 1293965 1941317 := bbase (se 4 (by rfl) ⟨181998, by rfl⟩ : syracuseStep 1941317 = 363997) (by norm_num)
theorem B1941341 : Blo 1293965 1941341 := bbase (se 3 (by rfl) ⟨364001, by rfl⟩ : syracuseStep 1941341 = 728003) (by norm_num)
theorem B1638245 : Blo 1293965 1638245 := bbase (se 4 (by rfl) ⟨153585, by rfl⟩ : syracuseStep 1638245 = 307171) (by norm_num)
theorem B1941365 : Blo 1293965 1941365 := bbase (se 5 (by rfl) ⟨91001, by rfl⟩ : syracuseStep 1941365 = 182003) (by norm_num)
theorem B1556341 : Blo 1293965 1556341 := bbase (se 5 (by rfl) ⟨72953, by rfl⟩ : syracuseStep 1556341 = 145907) (by norm_num)
theorem B1941389 : Blo 1293965 1941389 := bbase (se 3 (by rfl) ⟨364010, by rfl⟩ : syracuseStep 1941389 = 728021) (by norm_num)
theorem B1638301 : Blo 1293965 1638301 := bbase (se 3 (by rfl) ⟨307181, by rfl⟩ : syracuseStep 1638301 = 614363) (by norm_num)
theorem B1941413 : Blo 1293965 1941413 := bbase (se 4 (by rfl) ⟨182007, by rfl⟩ : syracuseStep 1941413 = 364015) (by norm_num)
theorem B1400765 : Blo 1293965 1400765 := bbase (se 3 (by rfl) ⟨262643, by rfl⟩ : syracuseStep 1400765 = 525287) (by norm_num)
theorem B1941437 : Blo 1293965 1941437 := bbase (se 3 (by rfl) ⟨364019, by rfl⟩ : syracuseStep 1941437 = 728039) (by norm_num)
theorem B3276733 : Blo 1293965 3276733 := bbase (se 3 (by rfl) ⟨614387, by rfl⟩ : syracuseStep 3276733 = 1228775) (by norm_num)
theorem B1941461 : Blo 1293965 1941461 := bbase (se 7 (by rfl) ⟨22751, by rfl⟩ : syracuseStep 1941461 = 45503) (by norm_num)
theorem B3112933 : Blo 1293965 3112933 := bbase (se 4 (by rfl) ⟨291837, by rfl⟩ : syracuseStep 3112933 = 583675) (by norm_num)
theorem B1941485 : Blo 1293965 1941485 := bbase (se 3 (by rfl) ⟨364028, by rfl⟩ : syracuseStep 1941485 = 728057) (by norm_num)
theorem B1638397 : Blo 1293965 1638397 := bbase (se 3 (by rfl) ⟨307199, by rfl⟩ : syracuseStep 1638397 = 614399) (by norm_num)
theorem B1294339 : Blo 1293965 1294339 := bstep (se 1 (by rfl) ⟨970754, by rfl⟩ : syracuseStep 1294339 = 1941509) B1941509
theorem B1941521 : Blo 1293965 1941521 := bstep (se 2 (by rfl) ⟨728070, by rfl⟩ : syracuseStep 1941521 = 1456141) B1456141
theorem B3686417 : Blo 1293965 3686417 := bstep (se 2 (by rfl) ⟨1382406, by rfl⟩ : syracuseStep 3686417 = 2764813) B2764813
theorem B1294355 : Blo 1293965 1294355 := bstep (se 1 (by rfl) ⟨970766, by rfl⟩ : syracuseStep 1294355 = 1941533) B1941533
theorem B2334737 : Blo 1293965 2334737 := bstep (se 2 (by rfl) ⟨875526, by rfl⟩ : syracuseStep 2334737 = 1751053) B1751053
theorem B1941539 : Blo 1293965 1941539 := bstep (se 1 (by rfl) ⟨1456154, by rfl⟩ : syracuseStep 1941539 = 2912309) B2912309
theorem B1294371 : Blo 1293965 1294371 := bstep (se 1 (by rfl) ⟨970778, by rfl⟩ : syracuseStep 1294371 = 1941557) B1941557
theorem B1294387 : Blo 1293965 1294387 := bstep (se 1 (by rfl) ⟨970790, by rfl⟩ : syracuseStep 1294387 = 1941581) B1941581
theorem B1941569 : Blo 1293965 1941569 := bstep (se 2 (by rfl) ⟨728088, by rfl⟩ : syracuseStep 1941569 = 1456177) B1456177
theorem B2129987 : Blo 1293965 2129987 := bstep (se 1 (by rfl) ⟨1597490, by rfl⟩ : syracuseStep 2129987 = 3194981) B3194981
theorem B1294403 : Blo 1293965 1294403 := bstep (se 1 (by rfl) ⟨970802, by rfl⟩ : syracuseStep 1294403 = 1941605) B1941605
theorem B1941587 : Blo 1293965 1941587 := bstep (se 1 (by rfl) ⟨1456190, by rfl⟩ : syracuseStep 1941587 = 2912381) B2912381
theorem B1294419 : Blo 1293965 1294419 := bstep (se 1 (by rfl) ⟨970814, by rfl⟩ : syracuseStep 1294419 = 1941629) B1941629
theorem B1294435 : Blo 1293965 1294435 := bstep (se 1 (by rfl) ⟨970826, by rfl⟩ : syracuseStep 1294435 = 1941653) B1941653
theorem B1941617 : Blo 1293965 1941617 := bstep (se 2 (by rfl) ⟨728106, by rfl⟩ : syracuseStep 1941617 = 1456213) B1456213
theorem B4915313 : Blo 1293965 4915313 := bstep (se 2 (by rfl) ⟨1843242, by rfl⟩ : syracuseStep 4915313 = 3686485) B3686485
theorem B1294451 : Blo 1293965 1294451 := bstep (se 1 (by rfl) ⟨970838, by rfl⟩ : syracuseStep 1294451 = 1941677) B1941677
theorem B1941635 : Blo 1293965 1941635 := bstep (se 1 (by rfl) ⟨1456226, by rfl⟩ : syracuseStep 1941635 = 2912453) B2912453
theorem B1294467 : Blo 1293965 1294467 := bstep (se 1 (by rfl) ⟨970850, by rfl⟩ : syracuseStep 1294467 = 1941701) B1941701
theorem B1294483 : Blo 1293965 1294483 := bstep (se 1 (by rfl) ⟨970862, by rfl⟩ : syracuseStep 1294483 = 1941725) B1941725
theorem B1843345 : Blo 1293965 1843345 := bstep (se 2 (by rfl) ⟨691254, by rfl⟩ : syracuseStep 1843345 = 1382509) B1382509
theorem B2244755 : Blo 1293965 2244755 := bstep (se 1 (by rfl) ⟨1683566, by rfl⟩ : syracuseStep 2244755 = 3367133) B3367133
theorem B1941665 : Blo 1293965 1941665 := bstep (se 2 (by rfl) ⟨728124, by rfl⟩ : syracuseStep 1941665 = 1456249) B1456249
theorem B1294499 : Blo 1293965 1294499 := bstep (se 1 (by rfl) ⟨970874, by rfl⟩ : syracuseStep 1294499 = 1941749) B1941749
theorem B1941683 : Blo 1293965 1941683 := bstep (se 1 (by rfl) ⟨1456262, by rfl⟩ : syracuseStep 1941683 = 2912525) B2912525
theorem B1294515 : Blo 1293965 1294515 := bstep (se 1 (by rfl) ⟨970886, by rfl⟩ : syracuseStep 1294515 = 1941773) B1941773
theorem B1294531 : Blo 1293965 1294531 := bstep (se 1 (by rfl) ⟨970898, by rfl⟩ : syracuseStep 1294531 = 1941797) B1941797
theorem B1941713 : Blo 1293965 1941713 := bstep (se 2 (by rfl) ⟨728142, by rfl⟩ : syracuseStep 1941713 = 1456285) B1456285
theorem B1294547 : Blo 1293965 1294547 := bstep (se 1 (by rfl) ⟨970910, by rfl⟩ : syracuseStep 1294547 = 1941821) B1941821
theorem B1941731 : Blo 1293965 1941731 := bstep (se 1 (by rfl) ⟨1456298, by rfl⟩ : syracuseStep 1941731 = 2912597) B2912597
theorem B1294563 : Blo 1293965 1294563 := bstep (se 1 (by rfl) ⟨970922, by rfl⟩ : syracuseStep 1294563 = 1941845) B1941845
theorem B1294579 : Blo 1293965 1294579 := bstep (se 1 (by rfl) ⟨970934, by rfl⟩ : syracuseStep 1294579 = 1941869) B1941869
theorem B1941761 : Blo 1293965 1941761 := bstep (se 2 (by rfl) ⟨728160, by rfl⟩ : syracuseStep 1941761 = 1456321) B1456321
theorem B1294595 : Blo 1293965 1294595 := bstep (se 1 (by rfl) ⟨970946, by rfl⟩ : syracuseStep 1294595 = 1941893) B1941893
theorem B1941779 : Blo 1293965 1941779 := bstep (se 1 (by rfl) ⟨1456334, by rfl⟩ : syracuseStep 1941779 = 2912669) B2912669
theorem B1294611 : Blo 1293965 1294611 := bstep (se 1 (by rfl) ⟨970958, by rfl⟩ : syracuseStep 1294611 = 1941917) B1941917
theorem B1294627 : Blo 1293965 1294627 := bstep (se 1 (by rfl) ⟨970970, by rfl⟩ : syracuseStep 1294627 = 1941941) B1941941
theorem B1941809 : Blo 1293965 1941809 := bstep (se 2 (by rfl) ⟨728178, by rfl⟩ : syracuseStep 1941809 = 1456357) B1456357
theorem B1294643 : Blo 1293965 1294643 := bstep (se 1 (by rfl) ⟨970982, by rfl⟩ : syracuseStep 1294643 = 1941965) B1941965
theorem B1941827 : Blo 1293965 1941827 := bstep (se 1 (by rfl) ⟨1456370, by rfl⟩ : syracuseStep 1941827 = 2912741) B2912741
theorem B1294659 : Blo 1293965 1294659 := bstep (se 1 (by rfl) ⟨970994, by rfl⟩ : syracuseStep 1294659 = 1941989) B1941989
theorem B1294675 : Blo 1293965 1294675 := bstep (se 1 (by rfl) ⟨971006, by rfl⟩ : syracuseStep 1294675 = 1942013) B1942013
theorem B1941857 : Blo 1293965 1941857 := bstep (se 2 (by rfl) ⟨728196, by rfl⟩ : syracuseStep 1941857 = 1456393) B1456393
theorem B1294691 : Blo 1293965 1294691 := bstep (se 1 (by rfl) ⟨971018, by rfl⟩ : syracuseStep 1294691 = 1942037) B1942037
theorem B3277169 : Blo 1293965 3277169 := bstep (se 2 (by rfl) ⟨1228938, by rfl⟩ : syracuseStep 3277169 = 2457877) B2457877
theorem B1941875 : Blo 1293965 1941875 := bstep (se 1 (by rfl) ⟨1456406, by rfl⟩ : syracuseStep 1941875 = 2912813) B2912813
theorem B1294707 : Blo 1293965 1294707 := bstep (se 1 (by rfl) ⟨971030, by rfl⟩ : syracuseStep 1294707 = 1942061) B1942061
theorem B1294723 : Blo 1293965 1294723 := bstep (se 1 (by rfl) ⟨971042, by rfl⟩ : syracuseStep 1294723 = 1942085) B1942085
theorem B1638787 : Blo 1293965 1638787 := bstep (se 1 (by rfl) ⟨1229090, by rfl⟩ : syracuseStep 1638787 = 2458181) B2458181
theorem B1941905 : Blo 1293965 1941905 := bstep (se 2 (by rfl) ⟨728214, by rfl⟩ : syracuseStep 1941905 = 1456429) B1456429
theorem B1294739 : Blo 1293965 1294739 := bstep (se 1 (by rfl) ⟨971054, by rfl⟩ : syracuseStep 1294739 = 1942109) B1942109
theorem B1941923 : Blo 1293965 1941923 := bstep (se 1 (by rfl) ⟨1456442, by rfl⟩ : syracuseStep 1941923 = 2912885) B2912885
theorem B3277219 : Blo 1293965 3277219 := bstep (se 1 (by rfl) ⟨2457914, by rfl⟩ : syracuseStep 3277219 = 4915829) B4915829
theorem B1294755 : Blo 1293965 1294755 := bstep (se 1 (by rfl) ⟨971066, by rfl⟩ : syracuseStep 1294755 = 1942133) B1942133
theorem B6554033 : Blo 1293965 6554033 := bstep (se 2 (by rfl) ⟨2457762, by rfl⟩ : syracuseStep 6554033 = 4915525) B4915525
theorem B1294771 : Blo 1293965 1294771 := bstep (se 1 (by rfl) ⟨971078, by rfl⟩ : syracuseStep 1294771 = 1942157) B1942157
theorem B1941953 : Blo 1293965 1941953 := bstep (se 2 (by rfl) ⟨728232, by rfl⟩ : syracuseStep 1941953 = 1456465) B1456465
theorem B1294787 : Blo 1293965 1294787 := bstep (se 1 (by rfl) ⟨971090, by rfl⟩ : syracuseStep 1294787 = 1942181) B1942181
theorem B1941971 : Blo 1293965 1941971 := bstep (se 1 (by rfl) ⟨1456478, by rfl⟩ : syracuseStep 1941971 = 2912957) B2912957
theorem B1294803 : Blo 1293965 1294803 := bstep (se 1 (by rfl) ⟨971102, by rfl⟩ : syracuseStep 1294803 = 1942205) B1942205
theorem B7872995 : Blo 1293965 7872995 := bstep (se 1 (by rfl) ⟨5904746, by rfl⟩ : syracuseStep 7872995 = 11809493) B11809493
theorem B1294819 : Blo 1293965 1294819 := bstep (se 1 (by rfl) ⟨971114, by rfl⟩ : syracuseStep 1294819 = 1942229) B1942229
theorem B1638883 : Blo 1293965 1638883 := bstep (se 1 (by rfl) ⟨1229162, by rfl⟩ : syracuseStep 1638883 = 2458325) B2458325
theorem B3498481 : Blo 1293965 3498481 := bstep (se 2 (by rfl) ⟨1311930, by rfl⟩ : syracuseStep 3498481 = 2623861) B2623861
theorem B1942001 : Blo 1293965 1942001 := bstep (se 2 (by rfl) ⟨728250, by rfl⟩ : syracuseStep 1942001 = 1456501) B1456501
theorem B2458097 : Blo 1293965 2458097 := bstep (se 2 (by rfl) ⟨921786, by rfl⟩ : syracuseStep 2458097 = 1843573) B1843573
theorem B1294835 : Blo 1293965 1294835 := bstep (se 1 (by rfl) ⟨971126, by rfl⟩ : syracuseStep 1294835 = 1942253) B1942253
theorem B1942019 : Blo 1293965 1942019 := bstep (se 1 (by rfl) ⟨1456514, by rfl⟩ : syracuseStep 1942019 = 2913029) B2913029
theorem B1294851 : Blo 1293965 1294851 := bstep (se 1 (by rfl) ⟨971138, by rfl⟩ : syracuseStep 1294851 = 1942277) B1942277
theorem B4145681 : Blo 1293965 4145681 := bstep (se 2 (by rfl) ⟨1554630, by rfl⟩ : syracuseStep 4145681 = 3109261) B3109261
theorem B1294867 : Blo 1293965 1294867 := bstep (se 1 (by rfl) ⟨971150, by rfl⟩ : syracuseStep 1294867 = 1942301) B1942301
theorem B1942049 : Blo 1293965 1942049 := bstep (se 2 (by rfl) ⟨728268, by rfl⟩ : syracuseStep 1942049 = 1456537) B1456537
theorem B1294883 : Blo 1293965 1294883 := bstep (se 1 (by rfl) ⟨971162, by rfl⟩ : syracuseStep 1294883 = 1942325) B1942325
theorem B3277361 : Blo 1293965 3277361 := bstep (se 2 (by rfl) ⟨1229010, by rfl⟩ : syracuseStep 3277361 = 2458021) B2458021
theorem B1942067 : Blo 1293965 1942067 := bstep (se 1 (by rfl) ⟨1456550, by rfl⟩ : syracuseStep 1942067 = 2913101) B2913101
theorem B1294899 : Blo 1293965 1294899 := bstep (se 1 (by rfl) ⟨971174, by rfl⟩ : syracuseStep 1294899 = 1942349) B1942349
theorem B1294915 : Blo 1293965 1294915 := bstep (se 1 (by rfl) ⟨971186, by rfl⟩ : syracuseStep 1294915 = 1942373) B1942373
theorem B1942097 : Blo 1293965 1942097 := bstep (se 2 (by rfl) ⟨728286, by rfl⟩ : syracuseStep 1942097 = 1456573) B1456573
theorem B1294931 : Blo 1293965 1294931 := bstep (se 1 (by rfl) ⟨971198, by rfl⟩ : syracuseStep 1294931 = 1942397) B1942397
theorem B14746211 : Blo 1293965 14746211 := bstep (se 1 (by rfl) ⟨11059658, by rfl⟩ : syracuseStep 14746211 = 22119317) B22119317
theorem B1942115 : Blo 1293965 1942115 := bstep (se 1 (by rfl) ⟨1456586, by rfl⟩ : syracuseStep 1942115 = 2913173) B2913173
theorem B1294947 : Blo 1293965 1294947 := bstep (se 1 (by rfl) ⟨971210, by rfl⟩ : syracuseStep 1294947 = 1942421) B1942421
theorem B1294963 : Blo 1293965 1294963 := bstep (se 1 (by rfl) ⟨971222, by rfl⟩ : syracuseStep 1294963 = 1942445) B1942445
theorem B1942145 : Blo 1293965 1942145 := bstep (se 2 (by rfl) ⟨728304, by rfl⟩ : syracuseStep 1942145 = 1456609) B1456609
theorem B1294979 : Blo 1293965 1294979 := bstep (se 1 (by rfl) ⟨971234, by rfl⟩ : syracuseStep 1294979 = 1942469) B1942469
theorem B1942163 : Blo 1293965 1942163 := bstep (se 1 (by rfl) ⟨1456622, by rfl⟩ : syracuseStep 1942163 = 2913245) B2913245
theorem B1294995 : Blo 1293965 1294995 := bstep (se 1 (by rfl) ⟨971246, by rfl⟩ : syracuseStep 1294995 = 1942493) B1942493
theorem B2073251 : Blo 1293965 2073251 := bstep (se 1 (by rfl) ⟨1554938, by rfl⟩ : syracuseStep 2073251 = 3109877) B3109877
theorem B1295011 : Blo 1293965 1295011 := bstep (se 1 (by rfl) ⟨971258, by rfl⟩ : syracuseStep 1295011 = 1942517) B1942517
theorem B6226595 : Blo 1293965 6226595 := bstep (se 1 (by rfl) ⟨4669946, by rfl⟩ : syracuseStep 6226595 = 9339893) B9339893
theorem B1942193 : Blo 1293965 1942193 := bstep (se 2 (by rfl) ⟨728322, by rfl⟩ : syracuseStep 1942193 = 1456645) B1456645
theorem B1295027 : Blo 1293965 1295027 := bstep (se 1 (by rfl) ⟨971270, by rfl⟩ : syracuseStep 1295027 = 1942541) B1942541
theorem B1942211 : Blo 1293965 1942211 := bstep (se 1 (by rfl) ⟨1456658, by rfl⟩ : syracuseStep 1942211 = 2913317) B2913317
theorem B1295043 : Blo 1293965 1295043 := bstep (se 1 (by rfl) ⟨971282, by rfl⟩ : syracuseStep 1295043 = 1942565) B1942565
theorem B1295059 : Blo 1293965 1295059 := bstep (se 1 (by rfl) ⟨971294, by rfl⟩ : syracuseStep 1295059 = 1942589) B1942589
theorem B1942241 : Blo 1293965 1942241 := bstep (se 2 (by rfl) ⟨728340, by rfl⟩ : syracuseStep 1942241 = 1456681) B1456681
theorem B1295075 : Blo 1293965 1295075 := bstep (se 1 (by rfl) ⟨971306, by rfl⟩ : syracuseStep 1295075 = 1942613) B1942613
theorem B1942259 : Blo 1293965 1942259 := bstep (se 1 (by rfl) ⟨1456694, by rfl⟩ : syracuseStep 1942259 = 2913389) B2913389
theorem B1295091 : Blo 1293965 1295091 := bstep (se 1 (by rfl) ⟨971318, by rfl⟩ : syracuseStep 1295091 = 1942637) B1942637
theorem B1295107 : Blo 1293965 1295107 := bstep (se 1 (by rfl) ⟨971330, by rfl⟩ : syracuseStep 1295107 = 1942661) B1942661
theorem B1942289 : Blo 1293965 1942289 := bstep (se 2 (by rfl) ⟨728358, by rfl⟩ : syracuseStep 1942289 = 1456717) B1456717
theorem B1295123 : Blo 1293965 1295123 := bstep (se 1 (by rfl) ⟨971342, by rfl⟩ : syracuseStep 1295123 = 1942685) B1942685
theorem B2073379 : Blo 1293965 2073379 := bstep (se 1 (by rfl) ⟨1555034, by rfl⟩ : syracuseStep 2073379 = 3110069) B3110069
theorem B1942307 : Blo 1293965 1942307 := bstep (se 1 (by rfl) ⟨1456730, by rfl⟩ : syracuseStep 1942307 = 2913461) B2913461
theorem B1295139 : Blo 1293965 1295139 := bstep (se 1 (by rfl) ⟨971354, by rfl⟩ : syracuseStep 1295139 = 1942709) B1942709
theorem B1295155 : Blo 1293965 1295155 := bstep (se 1 (by rfl) ⟨971366, by rfl⟩ : syracuseStep 1295155 = 1942733) B1942733
theorem B1942337 : Blo 1293965 1942337 := bstep (se 2 (by rfl) ⟨728376, by rfl⟩ : syracuseStep 1942337 = 1456753) B1456753
theorem B1295171 : Blo 1293965 1295171 := bstep (se 1 (by rfl) ⟨971378, by rfl⟩ : syracuseStep 1295171 = 1942757) B1942757
theorem B1942355 : Blo 1293965 1942355 := bstep (se 1 (by rfl) ⟨1456766, by rfl⟩ : syracuseStep 1942355 = 2913533) B2913533
theorem B1844051 : Blo 1293965 1844051 := bstep (se 1 (by rfl) ⟨1383038, by rfl⟩ : syracuseStep 1844051 = 2766077) B2766077
theorem B1295187 : Blo 1293965 1295187 := bstep (se 1 (by rfl) ⟨971390, by rfl⟩ : syracuseStep 1295187 = 1942781) B1942781
theorem B3498851 : Blo 1293965 3498851 := bstep (se 1 (by rfl) ⟨2624138, by rfl⟩ : syracuseStep 3498851 = 5248277) B5248277
theorem B2073443 : Blo 1293965 2073443 := bstep (se 1 (by rfl) ⟨1555082, by rfl⟩ : syracuseStep 2073443 = 3110165) B3110165
theorem B1295203 : Blo 1293965 1295203 := bstep (se 1 (by rfl) ⟨971402, by rfl⟩ : syracuseStep 1295203 = 1942805) B1942805
theorem B4146029 : Blo 1293965 4146029 := bstep (se 3 (by rfl) ⟨777380, by rfl⟩ : syracuseStep 4146029 = 1554761) B1554761
theorem B1942385 : Blo 1293965 1942385 := bstep (se 2 (by rfl) ⟨728394, by rfl⟩ : syracuseStep 1942385 = 1456789) B1456789
theorem B28017521 : Blo 1293965 28017521 := bstep (se 2 (by rfl) ⟨10506570, by rfl⟩ : syracuseStep 28017521 = 21013141) B21013141
theorem B1295219 : Blo 1293965 1295219 := bstep (se 1 (by rfl) ⟨971414, by rfl⟩ : syracuseStep 1295219 = 1942829) B1942829
theorem B1942403 : Blo 1293965 1942403 := bstep (se 1 (by rfl) ⟨1456802, by rfl⟩ : syracuseStep 1942403 = 2913605) B2913605
theorem B1295235 : Blo 1293965 1295235 := bstep (se 1 (by rfl) ⟨971426, by rfl⟩ : syracuseStep 1295235 = 1942853) B1942853
theorem B4367249 : Blo 1293965 4367249 := bstep (se 2 (by rfl) ⟨1637718, by rfl⟩ : syracuseStep 4367249 = 3275437) B3275437
theorem B1295251 : Blo 1293965 1295251 := bstep (se 1 (by rfl) ⟨971438, by rfl⟩ : syracuseStep 1295251 = 1942877) B1942877
theorem B1942433 : Blo 1293965 1942433 := bstep (se 2 (by rfl) ⟨728412, by rfl⟩ : syracuseStep 1942433 = 1456825) B1456825
theorem B1295267 : Blo 1293965 1295267 := bstep (se 1 (by rfl) ⟨971450, by rfl⟩ : syracuseStep 1295267 = 1942901) B1942901
theorem B1942451 : Blo 1293965 1942451 := bstep (se 1 (by rfl) ⟨1456838, by rfl⟩ : syracuseStep 1942451 = 2913677) B2913677
theorem B1295283 : Blo 1293965 1295283 := bstep (se 1 (by rfl) ⟨971462, by rfl⟩ : syracuseStep 1295283 = 1942925) B1942925
theorem B1295299 : Blo 1293965 1295299 := bstep (se 1 (by rfl) ⟨971474, by rfl⟩ : syracuseStep 1295299 = 1942949) B1942949
theorem B3687373 : Blo 1293965 3687373 := bstep (se 3 (by rfl) ⟨691382, by rfl⟩ : syracuseStep 3687373 = 1382765) B1382765
theorem B1942481 : Blo 1293965 1942481 := bstep (se 2 (by rfl) ⟨728430, by rfl⟩ : syracuseStep 1942481 = 1456861) B1456861
theorem B1639379 : Blo 1293965 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B1295315 : Blo 1293965 1295315 := bstep (se 1 (by rfl) ⟨971486, by rfl⟩ : syracuseStep 1295315 = 1942973) B1942973
theorem B1942499 : Blo 1293965 1942499 := bstep (se 1 (by rfl) ⟨1456874, by rfl⟩ : syracuseStep 1942499 = 2913749) B2913749
theorem B1295331 : Blo 1293965 1295331 := bstep (se 1 (by rfl) ⟨971498, by rfl⟩ : syracuseStep 1295331 = 1942997) B1942997
theorem B1295347 : Blo 1293965 1295347 := bstep (se 1 (by rfl) ⟨971510, by rfl⟩ : syracuseStep 1295347 = 1943021) B1943021
theorem B1942529 : Blo 1293965 1942529 := bstep (se 2 (by rfl) ⟨728448, by rfl⟩ : syracuseStep 1942529 = 1456897) B1456897
theorem B1598467 : Blo 1293965 1598467 := bstep (se 1 (by rfl) ⟨1198850, by rfl⟩ : syracuseStep 1598467 = 2397701) B2397701
theorem B1295363 : Blo 1293965 1295363 := bstep (se 1 (by rfl) ⟨971522, by rfl⟩ : syracuseStep 1295363 = 1943045) B1943045
theorem B1942547 : Blo 1293965 1942547 := bstep (se 1 (by rfl) ⟨1456910, by rfl⟩ : syracuseStep 1942547 = 2913821) B2913821
theorem B1295379 : Blo 1293965 1295379 := bstep (se 1 (by rfl) ⟨971534, by rfl⟩ : syracuseStep 1295379 = 1943069) B1943069
theorem B1295395 : Blo 1293965 1295395 := bstep (se 1 (by rfl) ⟨971546, by rfl⟩ : syracuseStep 1295395 = 1943093) B1943093
theorem B1942577 : Blo 1293965 1942577 := bstep (se 2 (by rfl) ⟨728466, by rfl⟩ : syracuseStep 1942577 = 1456933) B1456933
theorem B1295411 : Blo 1293965 1295411 := bstep (se 1 (by rfl) ⟨971558, by rfl⟩ : syracuseStep 1295411 = 1943117) B1943117
theorem B1942595 : Blo 1293965 1942595 := bstep (se 1 (by rfl) ⟨1456946, by rfl⟩ : syracuseStep 1942595 = 2913893) B2913893
theorem B1295427 : Blo 1293965 1295427 := bstep (se 1 (by rfl) ⟨971570, by rfl⟩ : syracuseStep 1295427 = 1943141) B1943141
theorem B9462853 : Blo 1293965 9462853 := bstep (se 4 (by rfl) ⟨887142, by rfl⟩ : syracuseStep 9462853 = 1774285) B1774285
theorem B1295443 : Blo 1293965 1295443 := bstep (se 1 (by rfl) ⟨971582, by rfl⟩ : syracuseStep 1295443 = 1943165) B1943165
theorem B1942625 : Blo 1293965 1942625 := bstep (se 2 (by rfl) ⟨728484, by rfl⟩ : syracuseStep 1942625 = 1456969) B1456969
theorem B1295459 : Blo 1293965 1295459 := bstep (se 1 (by rfl) ⟨971594, by rfl⟩ : syracuseStep 1295459 = 1943189) B1943189
theorem B6227057 : Blo 1293965 6227057 := bstep (se 2 (by rfl) ⟨2335146, by rfl⟩ : syracuseStep 6227057 = 4670293) B4670293
theorem B1942643 : Blo 1293965 1942643 := bstep (se 1 (by rfl) ⟨1456982, by rfl⟩ : syracuseStep 1942643 = 2913965) B2913965
theorem B1295475 : Blo 1293965 1295475 := bstep (se 1 (by rfl) ⟨971606, by rfl⟩ : syracuseStep 1295475 = 1943213) B1943213
theorem B1295491 : Blo 1293965 1295491 := bstep (se 1 (by rfl) ⟨971618, by rfl⟩ : syracuseStep 1295491 = 1943237) B1943237
theorem B1942673 : Blo 1293965 1942673 := bstep (se 2 (by rfl) ⟨728502, by rfl⟩ : syracuseStep 1942673 = 1457005) B1457005
theorem B1295507 : Blo 1293965 1295507 := bstep (se 1 (by rfl) ⟨971630, by rfl⟩ : syracuseStep 1295507 = 1943261) B1943261
theorem B5530787 : Blo 1293965 5530787 := bstep (se 1 (by rfl) ⟨4148090, by rfl⟩ : syracuseStep 5530787 = 8296181) B8296181
theorem B1942691 : Blo 1293965 1942691 := bstep (se 1 (by rfl) ⟨1457018, by rfl⟩ : syracuseStep 1942691 = 2914037) B2914037
theorem B1295523 : Blo 1293965 1295523 := bstep (se 1 (by rfl) ⟨971642, by rfl⟩ : syracuseStep 1295523 = 1943285) B1943285
theorem B3687601 : Blo 1293965 3687601 := bstep (se 2 (by rfl) ⟨1382850, by rfl⟩ : syracuseStep 3687601 = 2765701) B2765701
theorem B1295539 : Blo 1293965 1295539 := bstep (se 1 (by rfl) ⟨971654, by rfl⟩ : syracuseStep 1295539 = 1943309) B1943309
theorem B1942721 : Blo 1293965 1942721 := bstep (se 2 (by rfl) ⟨728520, by rfl⟩ : syracuseStep 1942721 = 1457041) B1457041
theorem B1295555 : Blo 1293965 1295555 := bstep (se 1 (by rfl) ⟨971666, by rfl⟩ : syracuseStep 1295555 = 1943333) B1943333
theorem B1942739 : Blo 1293965 1942739 := bstep (se 1 (by rfl) ⟨1457054, by rfl⟩ : syracuseStep 1942739 = 2914109) B2914109
theorem B1295571 : Blo 1293965 1295571 := bstep (se 1 (by rfl) ⟨971678, by rfl⟩ : syracuseStep 1295571 = 1943357) B1943357
theorem B1295587 : Blo 1293965 1295587 := bstep (se 1 (by rfl) ⟨971690, by rfl⟩ : syracuseStep 1295587 = 1943381) B1943381
theorem B1942769 : Blo 1293965 1942769 := bstep (se 2 (by rfl) ⟨728538, by rfl⟩ : syracuseStep 1942769 = 1457077) B1457077
theorem B1295603 : Blo 1293965 1295603 := bstep (se 1 (by rfl) ⟨971702, by rfl⟩ : syracuseStep 1295603 = 1943405) B1943405
theorem B1942787 : Blo 1293965 1942787 := bstep (se 1 (by rfl) ⟨1457090, by rfl⟩ : syracuseStep 1942787 = 2914181) B2914181
theorem B1295619 : Blo 1293965 1295619 := bstep (se 1 (by rfl) ⟨971714, by rfl⟩ : syracuseStep 1295619 = 1943429) B1943429
theorem B1295635 : Blo 1293965 1295635 := bstep (se 1 (by rfl) ⟨971726, by rfl⟩ : syracuseStep 1295635 = 1943453) B1943453
theorem B1942817 : Blo 1293965 1942817 := bstep (se 2 (by rfl) ⟨728556, by rfl⟩ : syracuseStep 1942817 = 1457113) B1457113
theorem B1295651 : Blo 1293965 1295651 := bstep (se 1 (by rfl) ⟨971738, by rfl⟩ : syracuseStep 1295651 = 1943477) B1943477
theorem B1942835 : Blo 1293965 1942835 := bstep (se 1 (by rfl) ⟨1457126, by rfl⟩ : syracuseStep 1942835 = 2914253) B2914253
theorem B1295667 : Blo 1293965 1295667 := bstep (se 1 (by rfl) ⟨971750, by rfl⟩ : syracuseStep 1295667 = 1943501) B1943501
theorem B1295683 : Blo 1293965 1295683 := bstep (se 1 (by rfl) ⟨971762, by rfl⟩ : syracuseStep 1295683 = 1943525) B1943525
theorem B11060549 : Blo 1293965 11060549 := bstep (se 4 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 11060549 = 2073853) B2073853
theorem B2073937 : Blo 1293965 2073937 := bstep (se 2 (by rfl) ⟨777726, by rfl⟩ : syracuseStep 2073937 = 1555453) B1555453
theorem B3687761 : Blo 1293965 3687761 := bstep (se 2 (by rfl) ⟨1382910, by rfl⟩ : syracuseStep 3687761 = 2765821) B2765821
theorem B1942865 : Blo 1293965 1942865 := bstep (se 2 (by rfl) ⟨728574, by rfl⟩ : syracuseStep 1942865 = 1457149) B1457149
theorem B1295699 : Blo 1293965 1295699 := bstep (se 1 (by rfl) ⟨971774, by rfl⟩ : syracuseStep 1295699 = 1943549) B1943549
theorem B9831779 : Blo 1293965 9831779 := bstep (se 1 (by rfl) ⟨7373834, by rfl⟩ : syracuseStep 9831779 = 14747669) B14747669
theorem B1942883 : Blo 1293965 1942883 := bstep (se 1 (by rfl) ⟨1457162, by rfl⟩ : syracuseStep 1942883 = 2914325) B2914325
theorem B1295715 : Blo 1293965 1295715 := bstep (se 1 (by rfl) ⟨971786, by rfl⟩ : syracuseStep 1295715 = 1943573) B1943573
theorem B2458993 : Blo 1293965 2458993 := bstep (se 2 (by rfl) ⟨922122, by rfl⟩ : syracuseStep 2458993 = 1844245) B1844245
theorem B1295731 : Blo 1293965 1295731 := bstep (se 1 (by rfl) ⟨971798, by rfl⟩ : syracuseStep 1295731 = 1943597) B1943597
theorem B1942913 : Blo 1293965 1942913 := bstep (se 2 (by rfl) ⟨728592, by rfl⟩ : syracuseStep 1942913 = 1457185) B1457185
theorem B1295747 : Blo 1293965 1295747 := bstep (se 1 (by rfl) ⟨971810, by rfl⟩ : syracuseStep 1295747 = 1943621) B1943621
theorem B1967507 : Blo 1293965 1967507 := bstep (se 1 (by rfl) ⟨1475630, by rfl⟩ : syracuseStep 1967507 = 2951261) B2951261
theorem B1942931 : Blo 1293965 1942931 := bstep (se 1 (by rfl) ⟨1457198, by rfl⟩ : syracuseStep 1942931 = 2914397) B2914397
theorem B1295763 : Blo 1293965 1295763 := bstep (se 1 (by rfl) ⟨971822, by rfl⟩ : syracuseStep 1295763 = 1943645) B1943645
theorem B1295779 : Blo 1293965 1295779 := bstep (se 1 (by rfl) ⟨971834, by rfl⟩ : syracuseStep 1295779 = 1943669) B1943669
theorem B4367789 : Blo 1293965 4367789 := bstep (se 3 (by rfl) ⟨818960, by rfl⟩ : syracuseStep 4367789 = 1637921) B1637921
theorem B1942961 : Blo 1293965 1942961 := bstep (se 2 (by rfl) ⟨728610, by rfl⟩ : syracuseStep 1942961 = 1457221) B1457221
theorem B1295795 : Blo 1293965 1295795 := bstep (se 1 (by rfl) ⟨971846, by rfl⟩ : syracuseStep 1295795 = 1943693) B1943693
theorem B3687875 : Blo 1293965 3687875 := bstep (se 1 (by rfl) ⟨2765906, by rfl⟩ : syracuseStep 3687875 = 5531813) B5531813
theorem B1942979 : Blo 1293965 1942979 := bstep (se 1 (by rfl) ⟨1457234, by rfl⟩ : syracuseStep 1942979 = 2914469) B2914469
theorem B1295811 : Blo 1293965 1295811 := bstep (se 1 (by rfl) ⟨971858, by rfl⟩ : syracuseStep 1295811 = 1943717) B1943717
theorem B1844689 : Blo 1293965 1844689 := bstep (se 2 (by rfl) ⟨691758, by rfl⟩ : syracuseStep 1844689 = 1383517) B1383517
theorem B1295827 : Blo 1293965 1295827 := bstep (se 1 (by rfl) ⟨971870, by rfl⟩ : syracuseStep 1295827 = 1943741) B1943741
theorem B1943009 : Blo 1293965 1943009 := bstep (se 2 (by rfl) ⟨728628, by rfl⟩ : syracuseStep 1943009 = 1457257) B1457257
theorem B4367843 : Blo 1293965 4367843 := bstep (se 1 (by rfl) ⟨3275882, by rfl⟩ : syracuseStep 4367843 = 6551765) B6551765
theorem B1295843 : Blo 1293965 1295843 := bstep (se 1 (by rfl) ⟨971882, by rfl⟩ : syracuseStep 1295843 = 1943765) B1943765
theorem B1943027 : Blo 1293965 1943027 := bstep (se 1 (by rfl) ⟨1457270, by rfl⟩ : syracuseStep 1943027 = 2914541) B2914541
theorem B1295859 : Blo 1293965 1295859 := bstep (se 1 (by rfl) ⟨971894, by rfl⟩ : syracuseStep 1295859 = 1943789) B1943789
theorem B1295875 : Blo 1293965 1295875 := bstep (se 1 (by rfl) ⟨971906, by rfl⟩ : syracuseStep 1295875 = 1943813) B1943813
theorem B3278353 : Blo 1293965 3278353 := bstep (se 2 (by rfl) ⟨1229382, by rfl⟩ : syracuseStep 3278353 = 2458765) B2458765
theorem B2459153 : Blo 1293965 2459153 := bstep (se 2 (by rfl) ⟨922182, by rfl⟩ : syracuseStep 2459153 = 1844365) B1844365
theorem B1943057 : Blo 1293965 1943057 := bstep (se 2 (by rfl) ⟨728646, by rfl⟩ : syracuseStep 1943057 = 1457293) B1457293
theorem B1295891 : Blo 1293965 1295891 := bstep (se 1 (by rfl) ⟨971918, by rfl⟩ : syracuseStep 1295891 = 1943837) B1943837
theorem B4916771 : Blo 1293965 4916771 := bstep (se 1 (by rfl) ⟨3687578, by rfl⟩ : syracuseStep 4916771 = 7375157) B7375157
theorem B1943075 : Blo 1293965 1943075 := bstep (se 1 (by rfl) ⟨1457306, by rfl⟩ : syracuseStep 1943075 = 2914613) B2914613
theorem B1295907 : Blo 1293965 1295907 := bstep (se 1 (by rfl) ⟨971930, by rfl⟩ : syracuseStep 1295907 = 1943861) B1943861
theorem B1295923 : Blo 1293965 1295923 := bstep (se 1 (by rfl) ⟨971942, by rfl⟩ : syracuseStep 1295923 = 1943885) B1943885
theorem B1943105 : Blo 1293965 1943105 := bstep (se 2 (by rfl) ⟨728664, by rfl⟩ : syracuseStep 1943105 = 1457329) B1457329
theorem B1844803 : Blo 1293965 1844803 := bstep (se 1 (by rfl) ⟨1383602, by rfl⟩ : syracuseStep 1844803 = 2767205) B2767205
theorem B1295939 : Blo 1293965 1295939 := bstep (se 1 (by rfl) ⟨971954, by rfl⟩ : syracuseStep 1295939 = 1943909) B1943909
theorem B1943123 : Blo 1293965 1943123 := bstep (se 1 (by rfl) ⟨1457342, by rfl⟩ : syracuseStep 1943123 = 2914685) B2914685
theorem B1295955 : Blo 1293965 1295955 := bstep (se 1 (by rfl) ⟨971966, by rfl⟩ : syracuseStep 1295955 = 1943933) B1943933
theorem B1943153 : Blo 1293965 1943153 := bstep (se 2 (by rfl) ⟨728682, by rfl⟩ : syracuseStep 1943153 = 1457365) B1457365
theorem B1943171 : Blo 1293965 1943171 := bstep (se 1 (by rfl) ⟨1457378, by rfl⟩ : syracuseStep 1943171 = 2914757) B2914757
theorem B1640083 : Blo 1293965 1640083 := bstep (se 1 (by rfl) ⟨1230062, by rfl⟩ : syracuseStep 1640083 = 2460125) B2460125
theorem B1943201 : Blo 1293965 1943201 := bstep (se 2 (by rfl) ⟨728700, by rfl⟩ : syracuseStep 1943201 = 1457401) B1457401
theorem B1943219 : Blo 1293965 1943219 := bstep (se 1 (by rfl) ⟨1457414, by rfl⟩ : syracuseStep 1943219 = 2914829) B2914829
theorem B1943249 : Blo 1293965 1943249 := bstep (se 2 (by rfl) ⟨728718, by rfl⟩ : syracuseStep 1943249 = 1457437) B1457437
theorem B2213603 : Blo 1293965 2213603 := bstep (se 1 (by rfl) ⟨1660202, by rfl⟩ : syracuseStep 2213603 = 3320405) B3320405
theorem B1943267 : Blo 1293965 1943267 := bstep (se 1 (by rfl) ⟨1457450, by rfl⟩ : syracuseStep 1943267 = 2914901) B2914901
theorem B4368113 : Blo 1293965 4368113 := bstep (se 2 (by rfl) ⟨1638042, by rfl⟩ : syracuseStep 4368113 = 3276085) B3276085
theorem B1640179 : Blo 1293965 1640179 := bstep (se 1 (by rfl) ⟨1230134, by rfl⟩ : syracuseStep 1640179 = 2460269) B2460269
theorem B1943297 : Blo 1293965 1943297 := bstep (se 2 (by rfl) ⟨728736, by rfl⟩ : syracuseStep 1943297 = 1457473) B1457473
theorem B1943315 : Blo 1293965 1943315 := bstep (se 1 (by rfl) ⟨1457486, by rfl⟩ : syracuseStep 1943315 = 2914973) B2914973
theorem B3278627 : Blo 1293965 3278627 := bstep (se 1 (by rfl) ⟨2458970, by rfl⟩ : syracuseStep 3278627 = 4917941) B4917941
theorem B1943345 : Blo 1293965 1943345 := bstep (se 2 (by rfl) ⟨728754, by rfl⟩ : syracuseStep 1943345 = 1457509) B1457509
theorem B1943363 : Blo 1293965 1943363 := bstep (se 1 (by rfl) ⟨1457522, by rfl⟩ : syracuseStep 1943363 = 2915045) B2915045
theorem B1943393 : Blo 1293965 1943393 := bstep (se 2 (by rfl) ⟨728772, by rfl⟩ : syracuseStep 1943393 = 1457545) B1457545
theorem B6555491 : Blo 1293965 6555491 := bstep (se 1 (by rfl) ⟨4916618, by rfl⟩ : syracuseStep 6555491 = 9833237) B9833237
theorem B11069297 : Blo 1293965 11069297 := bstep (se 2 (by rfl) ⟨4150986, by rfl⟩ : syracuseStep 11069297 = 8301973) B8301973
theorem B1943411 : Blo 1293965 1943411 := bstep (se 1 (by rfl) ⟨1457558, by rfl⟩ : syracuseStep 1943411 = 2915117) B2915117
theorem B7374725 : Blo 1293965 7374725 := bstep (se 4 (by rfl) ⟨691380, by rfl⟩ : syracuseStep 7374725 = 1382761) B1382761
theorem B1943441 : Blo 1293965 1943441 := bstep (se 2 (by rfl) ⟨728790, by rfl⟩ : syracuseStep 1943441 = 1457581) B1457581
theorem B2459555 : Blo 1293965 2459555 := bstep (se 1 (by rfl) ⟨1844666, by rfl⟩ : syracuseStep 2459555 = 3689333) B3689333
theorem B1943459 : Blo 1293965 1943459 := bstep (se 1 (by rfl) ⟨1457594, by rfl⟩ : syracuseStep 1943459 = 2915189) B2915189
theorem B1943489 : Blo 1293965 1943489 := bstep (se 2 (by rfl) ⟨728808, by rfl⟩ : syracuseStep 1943489 = 1457617) B1457617
theorem B1968067 : Blo 1293965 1968067 := bstep (se 1 (by rfl) ⟨1476050, by rfl⟩ : syracuseStep 1968067 = 2952101) B2952101
theorem B8300485 : Blo 1293965 8300485 := bstep (se 4 (by rfl) ⟨778170, by rfl⟩ : syracuseStep 8300485 = 1556341) B1556341
theorem B1943507 : Blo 1293965 1943507 := bstep (se 1 (by rfl) ⟨1457630, by rfl⟩ : syracuseStep 1943507 = 2915261) B2915261
theorem B3278819 : Blo 1293965 3278819 := bstep (se 1 (by rfl) ⟨2459114, by rfl⟩ : syracuseStep 3278819 = 4918229) B4918229
theorem B2074609 : Blo 1293965 2074609 := bstep (se 2 (by rfl) ⟨777978, by rfl⟩ : syracuseStep 2074609 = 1555957) B1555957
theorem B1943537 : Blo 1293965 1943537 := bstep (se 2 (by rfl) ⟨728826, by rfl⟩ : syracuseStep 1943537 = 1457653) B1457653
theorem B1943555 : Blo 1293965 1943555 := bstep (se 1 (by rfl) ⟨1457666, by rfl⟩ : syracuseStep 1943555 = 2915333) B2915333
theorem B8857613 : Blo 1293965 8857613 := bstep (se 3 (by rfl) ⟨1660802, by rfl⟩ : syracuseStep 8857613 = 3321605) B3321605
theorem B1943585 : Blo 1293965 1943585 := bstep (se 2 (by rfl) ⟨728844, by rfl⟩ : syracuseStep 1943585 = 1457689) B1457689
theorem B1943603 : Blo 1293965 1943603 := bstep (se 1 (by rfl) ⟨1457702, by rfl⟩ : syracuseStep 1943603 = 2915405) B2915405
theorem B1943633 : Blo 1293965 1943633 := bstep (se 2 (by rfl) ⟨728862, by rfl⟩ : syracuseStep 1943633 = 1457725) B1457725
theorem B1943651 : Blo 1293965 1943651 := bstep (se 1 (by rfl) ⟨1457738, by rfl⟩ : syracuseStep 1943651 = 2915477) B2915477
theorem B1943681 : Blo 1293965 1943681 := bstep (se 2 (by rfl) ⟨728880, by rfl⟩ : syracuseStep 1943681 = 1457761) B1457761
theorem B1943699 : Blo 1293965 1943699 := bstep (se 1 (by rfl) ⟨1457774, by rfl⟩ : syracuseStep 1943699 = 2915549) B2915549
theorem B1943729 : Blo 1293965 1943729 := bstep (se 2 (by rfl) ⟨728898, by rfl⟩ : syracuseStep 1943729 = 1457797) B1457797
theorem B1943747 : Blo 1293965 1943747 := bstep (se 1 (by rfl) ⟨1457810, by rfl⟩ : syracuseStep 1943747 = 2915621) B2915621
theorem B1943777 : Blo 1293965 1943777 := bstep (se 2 (by rfl) ⟨728916, by rfl⟩ : syracuseStep 1943777 = 1457833) B1457833
theorem B1943795 : Blo 1293965 1943795 := bstep (se 1 (by rfl) ⟨1457846, by rfl⟩ : syracuseStep 1943795 = 2915693) B2915693
theorem B4368653 : Blo 1293965 4368653 := bstep (se 3 (by rfl) ⟨819122, by rfl⟩ : syracuseStep 4368653 = 1638245) B1638245
theorem B1943825 : Blo 1293965 1943825 := bstep (se 2 (by rfl) ⟨728934, by rfl⟩ : syracuseStep 1943825 = 1457869) B1457869
theorem B1943843 : Blo 1293965 1943843 := bstep (se 1 (by rfl) ⟨1457882, by rfl⟩ : syracuseStep 1943843 = 2915765) B2915765
theorem B1943873 : Blo 1293965 1943873 := bstep (se 2 (by rfl) ⟨728952, by rfl⟩ : syracuseStep 1943873 = 1457905) B1457905
theorem B4368707 : Blo 1293965 4368707 := bstep (se 1 (by rfl) ⟨3276530, by rfl⟩ : syracuseStep 4368707 = 6553061) B6553061
theorem B1943891 : Blo 1293965 1943891 := bstep (se 1 (by rfl) ⟨1457918, by rfl⟩ : syracuseStep 1943891 = 2915837) B2915837
theorem B7473521 : Blo 1293965 7473521 := bstep (se 2 (by rfl) ⟨2802570, by rfl⟩ : syracuseStep 7473521 = 5605141) B5605141
theorem B1943921 : Blo 1293965 1943921 := bstep (se 2 (by rfl) ⟨728970, by rfl⟩ : syracuseStep 1943921 = 1457941) B1457941
theorem B1943939 : Blo 1293965 1943939 := bstep (se 1 (by rfl) ⟨1457954, by rfl⟩ : syracuseStep 1943939 = 2915909) B2915909
theorem B1894819 : Blo 1293965 1894819 := bstep (se 1 (by rfl) ⟨1421114, by rfl⟩ : syracuseStep 1894819 = 2842229) B2842229
theorem B3688877 : Blo 1293965 3688877 := bstep (se 3 (by rfl) ⟨691664, by rfl⟩ : syracuseStep 3688877 = 1383329) B1383329
theorem B1870273 : Blo 1293965 1870273 := bstep (se 2 (by rfl) ⟨701352, by rfl⟩ : syracuseStep 1870273 = 1402705) B1402705
theorem B2623985 : Blo 1293965 2623985 := bstep (se 2 (by rfl) ⟨983994, by rfl⟩ : syracuseStep 2623985 = 1967989) B1967989
theorem B6220273 : Blo 1293965 6220273 := bstep (se 2 (by rfl) ⟨2332602, by rfl⟩ : syracuseStep 6220273 = 4665205) B4665205
theorem B4917773 : Blo 1293965 4917773 := bstep (se 3 (by rfl) ⟨922082, by rfl⟩ : syracuseStep 4917773 = 1844165) B1844165
theorem B4368977 : Blo 1293965 4368977 := bstep (se 2 (by rfl) ⟨1638366, by rfl⟩ : syracuseStep 4368977 = 3276733) B3276733
theorem B3689059 : Blo 1293965 3689059 := bstep (se 1 (by rfl) ⟨2766794, by rfl⟩ : syracuseStep 3689059 = 5533589) B5533589
theorem B6556301 : Blo 1293965 6556301 := bstep (se 3 (by rfl) ⟨1229306, by rfl⟩ : syracuseStep 6556301 = 2458613) B2458613
theorem B4147885 : Blo 1293965 4147885 := bstep (se 3 (by rfl) ⟨777728, by rfl⟩ : syracuseStep 4147885 = 1555457) B1555457
theorem B7473869 : Blo 1293965 7473869 := bstep (se 3 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 7473869 = 2802701) B2802701
theorem B3689219 : Blo 1293965 3689219 := bstep (se 1 (by rfl) ⟨2766914, by rfl⟩ : syracuseStep 3689219 = 5533829) B5533829
theorem B3279761 : Blo 1293965 3279761 := bstep (se 2 (by rfl) ⟨1229910, by rfl⟩ : syracuseStep 3279761 = 2459821) B2459821
theorem B3279811 : Blo 1293965 3279811 := bstep (se 1 (by rfl) ⟨2459858, by rfl⟩ : syracuseStep 3279811 = 4919717) B4919717
theorem B12454883 : Blo 1293965 12454883 := bstep (se 1 (by rfl) ⟨9341162, by rfl⟩ : syracuseStep 12454883 = 18682325) B18682325
theorem B5319715 : Blo 1293965 5319715 := bstep (se 1 (by rfl) ⟨3989786, by rfl⟩ : syracuseStep 5319715 = 7979573) B7979573
theorem B2075699 : Blo 1293965 2075699 := bstep (se 1 (by rfl) ⟨1556774, by rfl⟩ : syracuseStep 2075699 = 3113549) B3113549
theorem B3279953 : Blo 1293965 3279953 := bstep (se 2 (by rfl) ⟨1229982, by rfl⟩ : syracuseStep 3279953 = 2459965) B2459965
theorem B4369517 : Blo 1293965 4369517 := bstep (se 3 (by rfl) ⟨819284, by rfl⟩ : syracuseStep 4369517 = 1638569) B1638569
theorem B2215027 : Blo 1293965 2215027 := bstep (se 1 (by rfl) ⟨1661270, by rfl⟩ : syracuseStep 2215027 = 3322541) B3322541
theorem B4369571 : Blo 1293965 4369571 := bstep (se 1 (by rfl) ⟨3277178, by rfl⟩ : syracuseStep 4369571 = 6554357) B6554357
theorem B3935405 : Blo 1293965 3935405 := bstep (se 3 (by rfl) ⟨737888, by rfl⟩ : syracuseStep 3935405 = 1475777) B1475777
theorem B2911427 : Blo 1293965 2911427 := bstep (se 1 (by rfl) ⟨2183570, by rfl⟩ : syracuseStep 2911427 = 4367141) B4367141
theorem B2764163 : Blo 1293965 2764163 := bstep (se 1 (by rfl) ⟨2073122, by rfl⟩ : syracuseStep 2764163 = 4146245) B4146245
theorem B2624899 : Blo 1293965 2624899 := bstep (se 1 (by rfl) ⟨1968674, by rfl⟩ : syracuseStep 2624899 = 3937349) B3937349
theorem B4369841 : Blo 1293965 4369841 := bstep (se 2 (by rfl) ⟨1638690, by rfl⟩ : syracuseStep 4369841 = 3277381) B3277381
theorem B7876037 : Blo 1293965 7876037 := bstep (se 4 (by rfl) ⟨738378, by rfl⟩ : syracuseStep 7876037 = 1476757) B1476757
theorem B2911697 : Blo 1293965 2911697 := bstep (se 2 (by rfl) ⟨1091886, by rfl⟩ : syracuseStep 2911697 = 2183773) B2183773
theorem B2911715 : Blo 1293965 2911715 := bstep (se 1 (by rfl) ⟨2183786, by rfl⟩ : syracuseStep 2911715 = 4367573) B4367573
theorem B2911985 : Blo 1293965 2911985 := bstep (se 2 (by rfl) ⟨1091994, by rfl⟩ : syracuseStep 2911985 = 2183989) B2183989
theorem B2912003 : Blo 1293965 2912003 := bstep (se 1 (by rfl) ⟨2184002, by rfl⟩ : syracuseStep 2912003 = 4368005) B4368005
theorem B1969939 : Blo 1293965 1969939 := bstep (se 1 (by rfl) ⟨1477454, by rfl⟩ : syracuseStep 1969939 = 2954909) B2954909
theorem B3690289 : Blo 1293965 3690289 := bstep (se 2 (by rfl) ⟨1383858, by rfl⟩ : syracuseStep 3690289 = 2767717) B2767717
theorem B4370381 : Blo 1293965 4370381 := bstep (se 3 (by rfl) ⟨819446, by rfl⟩ : syracuseStep 4370381 = 1638893) B1638893
theorem B5681123 : Blo 1293965 5681123 := bstep (se 1 (by rfl) ⟨4260842, by rfl⟩ : syracuseStep 5681123 = 8521685) B8521685
theorem B4370435 : Blo 1293965 4370435 := bstep (se 1 (by rfl) ⟨3277826, by rfl⟩ : syracuseStep 4370435 = 6555653) B6555653
theorem B2912273 : Blo 1293965 2912273 := bstep (se 2 (by rfl) ⟨1092102, by rfl⟩ : syracuseStep 2912273 = 2184205) B2184205
theorem B2912291 : Blo 1293965 2912291 := bstep (se 1 (by rfl) ⟨2184218, by rfl⟩ : syracuseStep 2912291 = 4368437) B4368437
theorem B1970257 : Blo 1293965 1970257 := bstep (se 2 (by rfl) ⟨738846, by rfl⟩ : syracuseStep 1970257 = 1477693) B1477693
theorem B4370705 : Blo 1293965 4370705 := bstep (se 2 (by rfl) ⟨1639014, by rfl⟩ : syracuseStep 4370705 = 3278029) B3278029
theorem B1995043 : Blo 1293965 1995043 := bstep (se 1 (by rfl) ⟨1496282, by rfl⟩ : syracuseStep 1995043 = 2992565) B2992565
theorem B2912561 : Blo 1293965 2912561 := bstep (se 2 (by rfl) ⟨1092210, by rfl⟩ : syracuseStep 2912561 = 2184421) B2184421
theorem B2912579 : Blo 1293965 2912579 := bstep (se 1 (by rfl) ⟨2184434, by rfl⟩ : syracuseStep 2912579 = 4368869) B4368869
theorem B4149731 : Blo 1293965 4149731 := bstep (se 1 (by rfl) ⟨3112298, by rfl⟩ : syracuseStep 4149731 = 6224597) B6224597
theorem B2183665 : Blo 1293965 2183665 := bstep (se 2 (by rfl) ⟨818874, by rfl⟩ : syracuseStep 2183665 = 1637749) B1637749
theorem B2183699 : Blo 1293965 2183699 := bstep (se 1 (by rfl) ⟨1637774, by rfl⟩ : syracuseStep 2183699 = 3275549) B3275549
theorem B1749539 : Blo 1293965 1749539 := bstep (se 1 (by rfl) ⟨1312154, by rfl⟩ : syracuseStep 1749539 = 2624309) B2624309
theorem B4919885 : Blo 1293965 4919885 := bstep (se 3 (by rfl) ⟨922478, by rfl⟩ : syracuseStep 4919885 = 1844957) B1844957
theorem B2912849 : Blo 1293965 2912849 := bstep (se 2 (by rfl) ⟨1092318, by rfl⟩ : syracuseStep 2912849 = 2184637) B2184637
theorem B2912867 : Blo 1293965 2912867 := bstep (se 1 (by rfl) ⟨2184650, by rfl⟩ : syracuseStep 2912867 = 4369301) B4369301
theorem B2765411 : Blo 1293965 2765411 := bstep (se 1 (by rfl) ⟨2074058, by rfl⟩ : syracuseStep 2765411 = 4148117) B4148117
theorem B3740269 : Blo 1293965 3740269 := bstep (se 3 (by rfl) ⟨701300, by rfl⟩ : syracuseStep 3740269 = 1402601) B1402601
theorem B2216593 : Blo 1293965 2216593 := bstep (se 2 (by rfl) ⟨831222, by rfl⟩ : syracuseStep 2216593 = 1662445) B1662445
theorem B2183827 : Blo 1293965 2183827 := bstep (se 1 (by rfl) ⟨1637870, by rfl⟩ : syracuseStep 2183827 = 3275741) B3275741
theorem B4985549 : Blo 1293965 4985549 := bstep (se 3 (by rfl) ⟨934790, by rfl⟩ : syracuseStep 4985549 = 1869581) B1869581
theorem B5534477 : Blo 1293965 5534477 := bstep (se 3 (by rfl) ⟨1037714, by rfl⟩ : syracuseStep 5534477 = 2075429) B2075429
theorem B1684243 : Blo 1293965 1684243 := bstep (se 1 (by rfl) ⟨1263182, by rfl⟩ : syracuseStep 1684243 = 2526365) B2526365
theorem B2183969 : Blo 1293965 2183969 := bstep (se 2 (by rfl) ⟨818988, by rfl⟩ : syracuseStep 2183969 = 1637977) B1637977
theorem B4371245 : Blo 1293965 4371245 := bstep (se 3 (by rfl) ⟨819608, by rfl⟩ : syracuseStep 4371245 = 1639217) B1639217
theorem B5534513 : Blo 1293965 5534513 := bstep (se 2 (by rfl) ⟨2075442, by rfl⟩ : syracuseStep 5534513 = 4150885) B4150885
theorem B4371299 : Blo 1293965 4371299 := bstep (se 1 (by rfl) ⟨3278474, by rfl⟩ : syracuseStep 4371299 = 6556949) B6556949
theorem B2913137 : Blo 1293965 2913137 := bstep (se 2 (by rfl) ⟨1092426, by rfl⟩ : syracuseStep 2913137 = 2184853) B2184853
theorem B4150129 : Blo 1293965 4150129 := bstep (se 2 (by rfl) ⟨1556298, by rfl⟩ : syracuseStep 4150129 = 3112597) B3112597
theorem B2913155 : Blo 1293965 2913155 := bstep (se 1 (by rfl) ⟨2184866, by rfl⟩ : syracuseStep 2913155 = 4369733) B4369733
theorem B2184097 : Blo 1293965 2184097 := bstep (se 2 (by rfl) ⟨819036, by rfl⟩ : syracuseStep 2184097 = 1638073) B1638073
theorem B2184131 : Blo 1293965 2184131 := bstep (se 1 (by rfl) ⟨1638098, by rfl⟩ : syracuseStep 2184131 = 3276197) B3276197
theorem B2954179 : Blo 1293965 2954179 := bstep (se 1 (by rfl) ⟨2215634, by rfl⟩ : syracuseStep 2954179 = 4431269) B4431269
theorem B2184259 : Blo 1293965 2184259 := bstep (se 1 (by rfl) ⟨1638194, by rfl⟩ : syracuseStep 2184259 = 3276389) B3276389
theorem B4371569 : Blo 1293965 4371569 := bstep (se 2 (by rfl) ⟨1639338, by rfl⟩ : syracuseStep 4371569 = 3278677) B3278677
theorem B2913425 : Blo 1293965 2913425 := bstep (se 2 (by rfl) ⟨1092534, by rfl⟩ : syracuseStep 2913425 = 2185069) B2185069
theorem B2913443 : Blo 1293965 2913443 := bstep (se 1 (by rfl) ⟨2185082, by rfl⟩ : syracuseStep 2913443 = 4370165) B4370165
theorem B2766001 : Blo 1293965 2766001 := bstep (se 2 (by rfl) ⟨1037250, by rfl⟩ : syracuseStep 2766001 = 2074501) B2074501
theorem B2184401 : Blo 1293965 2184401 := bstep (se 2 (by rfl) ⟨819150, by rfl⟩ : syracuseStep 2184401 = 1638301) B1638301
theorem B4150577 : Blo 1293965 4150577 := bstep (se 2 (by rfl) ⟨1556466, by rfl⟩ : syracuseStep 4150577 = 3112933) B3112933
theorem B2184529 : Blo 1293965 2184529 := bstep (se 2 (by rfl) ⟨819198, by rfl⟩ : syracuseStep 2184529 = 1638397) B1638397
theorem B18666865 : Blo 1293965 18666865 := bstep (se 2 (by rfl) ⟨7000074, by rfl⟩ : syracuseStep 18666865 = 14000149) B14000149
theorem B2184563 : Blo 1293965 2184563 := bstep (se 1 (by rfl) ⟨1638422, by rfl⟩ : syracuseStep 2184563 = 3276845) B3276845
theorem B2913713 : Blo 1293965 2913713 := bstep (se 2 (by rfl) ⟨1092642, by rfl⟩ : syracuseStep 2913713 = 2185285) B2185285
theorem B2102707 : Blo 1293965 2102707 := bstep (se 1 (by rfl) ⟨1577030, by rfl⟩ : syracuseStep 2102707 = 3154061) B3154061
theorem B14005685 : Blo 1293965 14005685 := bstep (se 5 (by rfl) ⟨656516, by rfl⟩ : syracuseStep 14005685 = 1313033) B1313033
theorem B2913731 : Blo 1293965 2913731 := bstep (se 1 (by rfl) ⟨2185298, by rfl⟩ : syracuseStep 2913731 = 4370597) B4370597
theorem B6559217 : Blo 1293965 6559217 := bstep (se 2 (by rfl) ⟨2459706, by rfl⟩ : syracuseStep 6559217 = 4919413) B4919413
theorem B2184691 : Blo 1293965 2184691 := bstep (se 1 (by rfl) ⟨1638518, by rfl⟩ : syracuseStep 2184691 = 3277037) B3277037
theorem B1381907 : Blo 1293965 1381907 := bstep (se 1 (by rfl) ⟨1036430, by rfl⟩ : syracuseStep 1381907 = 2072861) B2072861
theorem B6551117 : Blo 1293965 6551117 := bstep (se 3 (by rfl) ⟨1228334, by rfl⟩ : syracuseStep 6551117 = 2456669) B2456669
theorem B13465187 : Blo 1293965 13465187 := bstep (se 1 (by rfl) ⟨10098890, by rfl⟩ : syracuseStep 13465187 = 20197781) B20197781
theorem B2184833 : Blo 1293965 2184833 := bstep (se 2 (by rfl) ⟨819312, by rfl⟩ : syracuseStep 2184833 = 1638625) B1638625
theorem B4372109 : Blo 1293965 4372109 := bstep (se 3 (by rfl) ⟨819770, by rfl⟩ : syracuseStep 4372109 = 1639541) B1639541
theorem B7378573 : Blo 1293965 7378573 := bstep (se 3 (by rfl) ⟨1383482, by rfl⟩ : syracuseStep 7378573 = 2766965) B2766965
theorem B1455763 : Blo 1293965 1455763 := bstep (se 1 (by rfl) ⟨1091822, by rfl⟩ : syracuseStep 1455763 = 2183645) B2183645
theorem B5527217 : Blo 1293965 5527217 := bstep (se 2 (by rfl) ⟨2072706, by rfl⟩ : syracuseStep 5527217 = 4145413) B4145413
theorem B4372163 : Blo 1293965 4372163 := bstep (se 1 (by rfl) ⟨3279122, by rfl⟩ : syracuseStep 4372163 = 6558245) B6558245
theorem B31495877 : Blo 1293965 31495877 := bstep (se 4 (by rfl) ⟨2952738, by rfl⟩ : syracuseStep 31495877 = 5905477) B5905477
theorem B2914001 : Blo 1293965 2914001 := bstep (se 2 (by rfl) ⟨1092750, by rfl⟩ : syracuseStep 2914001 = 2185501) B2185501
theorem B2914019 : Blo 1293965 2914019 := bstep (se 1 (by rfl) ⟨2185514, by rfl⟩ : syracuseStep 2914019 = 4371029) B4371029
theorem B2184961 : Blo 1293965 2184961 := bstep (se 2 (by rfl) ⟨819360, by rfl⟩ : syracuseStep 2184961 = 1638721) B1638721
theorem B1455907 : Blo 1293965 1455907 := bstep (se 1 (by rfl) ⟨1091930, by rfl⟩ : syracuseStep 1455907 = 2183861) B2183861
theorem B2184995 : Blo 1293965 2184995 := bstep (se 1 (by rfl) ⟨1638746, by rfl⟩ : syracuseStep 2184995 = 3277493) B3277493
theorem B1660819 : Blo 1293965 1660819 := bstep (se 1 (by rfl) ⟨1245614, by rfl⟩ : syracuseStep 1660819 = 2491229) B2491229
theorem B2185123 : Blo 1293965 2185123 := bstep (se 1 (by rfl) ⟨1638842, by rfl⟩ : syracuseStep 2185123 = 3277685) B3277685
theorem B1456051 : Blo 1293965 1456051 := bstep (se 1 (by rfl) ⟨1092038, by rfl⟩ : syracuseStep 1456051 = 2184077) B2184077
theorem B4372433 : Blo 1293965 4372433 := bstep (se 2 (by rfl) ⟨1639662, by rfl⟩ : syracuseStep 4372433 = 3279325) B3279325
theorem B2914289 : Blo 1293965 2914289 := bstep (se 2 (by rfl) ⟨1092858, by rfl⟩ : syracuseStep 2914289 = 2185717) B2185717
theorem B2914307 : Blo 1293965 2914307 := bstep (se 1 (by rfl) ⟨2185730, by rfl⟩ : syracuseStep 2914307 = 4371461) B4371461
theorem B8411141 : Blo 1293965 8411141 := bstep (se 4 (by rfl) ⟨788544, by rfl⟩ : syracuseStep 8411141 = 1577089) B1577089
theorem B3938321 : Blo 1293965 3938321 := bstep (se 2 (by rfl) ⟨1476870, by rfl⟩ : syracuseStep 3938321 = 2953741) B2953741
theorem B2185265 : Blo 1293965 2185265 := bstep (se 2 (by rfl) ⟨819474, by rfl⟩ : syracuseStep 2185265 = 1638949) B1638949
theorem B14956597 : Blo 1293965 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B1456195 : Blo 1293965 1456195 := bstep (se 1 (by rfl) ⟨1092146, by rfl⟩ : syracuseStep 1456195 = 2184293) B2184293
theorem B2185393 : Blo 1293965 2185393 := bstep (se 2 (by rfl) ⟨819522, by rfl⟩ : syracuseStep 2185393 = 1639045) B1639045
theorem B1456339 : Blo 1293965 1456339 := bstep (se 1 (by rfl) ⟨1092254, by rfl⟩ : syracuseStep 1456339 = 2184509) B2184509
theorem B2185427 : Blo 1293965 2185427 := bstep (se 1 (by rfl) ⟨1639070, by rfl⟩ : syracuseStep 2185427 = 3278141) B3278141
theorem B2914577 : Blo 1293965 2914577 := bstep (se 2 (by rfl) ⟨1092966, by rfl⟩ : syracuseStep 2914577 = 2185933) B2185933
theorem B2914595 : Blo 1293965 2914595 := bstep (se 1 (by rfl) ⟨2185946, by rfl⟩ : syracuseStep 2914595 = 4371893) B4371893
theorem B14194997 : Blo 1293965 14194997 := bstep (se 5 (by rfl) ⟨665390, by rfl⟩ : syracuseStep 14194997 = 1330781) B1330781
theorem B2185555 : Blo 1293965 2185555 := bstep (se 1 (by rfl) ⟨1639166, by rfl⟩ : syracuseStep 2185555 = 3278333) B3278333
theorem B1456483 : Blo 1293965 1456483 := bstep (se 1 (by rfl) ⟨1092362, by rfl⟩ : syracuseStep 1456483 = 2184725) B2184725
theorem B8853893 : Blo 1293965 8853893 := bstep (se 4 (by rfl) ⟨830052, by rfl⟩ : syracuseStep 8853893 = 1660105) B1660105
theorem B6642125 : Blo 1293965 6642125 := bstep (se 3 (by rfl) ⟨1245398, by rfl⟩ : syracuseStep 6642125 = 2490797) B2490797
theorem B4430285 : Blo 1293965 4430285 := bstep (se 3 (by rfl) ⟨830678, by rfl⟩ : syracuseStep 4430285 = 1661357) B1661357
theorem B2185697 : Blo 1293965 2185697 := bstep (se 2 (by rfl) ⟨819636, by rfl⟩ : syracuseStep 2185697 = 1639273) B1639273
theorem B3684845 : Blo 1293965 3684845 := bstep (se 3 (by rfl) ⟨690908, by rfl⟩ : syracuseStep 3684845 = 1381817) B1381817
theorem B4372973 : Blo 1293965 4372973 := bstep (se 3 (by rfl) ⟨819932, by rfl⟩ : syracuseStep 4372973 = 1639865) B1639865
theorem B7879153 : Blo 1293965 7879153 := bstep (se 2 (by rfl) ⟨2954682, by rfl⟩ : syracuseStep 7879153 = 5909365) B5909365
theorem B1456627 : Blo 1293965 1456627 := bstep (se 1 (by rfl) ⟨1092470, by rfl⟩ : syracuseStep 1456627 = 2184941) B2184941
theorem B4373027 : Blo 1293965 4373027 := bstep (se 1 (by rfl) ⟨3279770, by rfl⟩ : syracuseStep 4373027 = 6559541) B6559541
theorem B2914865 : Blo 1293965 2914865 := bstep (se 2 (by rfl) ⟨1093074, by rfl⟩ : syracuseStep 2914865 = 2186149) B2186149
theorem B2914883 : Blo 1293965 2914883 := bstep (se 1 (by rfl) ⟨2186162, by rfl⟩ : syracuseStep 2914883 = 4372325) B4372325
theorem B9837125 : Blo 1293965 9837125 := bstep (se 4 (by rfl) ⟨922230, by rfl⟩ : syracuseStep 9837125 = 1844461) B1844461
theorem B2185825 : Blo 1293965 2185825 := bstep (se 2 (by rfl) ⟨819684, by rfl⟩ : syracuseStep 2185825 = 1639369) B1639369
theorem B1456771 : Blo 1293965 1456771 := bstep (se 1 (by rfl) ⟨1092578, by rfl⟩ : syracuseStep 1456771 = 2185157) B2185157
theorem B2185859 : Blo 1293965 2185859 := bstep (se 1 (by rfl) ⟨1639394, by rfl⟩ : syracuseStep 2185859 = 3278789) B3278789
theorem B2103953 : Blo 1293965 2103953 := bstep (se 2 (by rfl) ⟨788982, by rfl⟩ : syracuseStep 2103953 = 1577965) B1577965
theorem B3685027 : Blo 1293965 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B2185987 : Blo 1293965 2185987 := bstep (se 1 (by rfl) ⟨1639490, by rfl⟩ : syracuseStep 2185987 = 3278981) B3278981
theorem B1456915 : Blo 1293965 1456915 := bstep (se 1 (by rfl) ⟨1092686, by rfl⟩ : syracuseStep 1456915 = 2185373) B2185373
theorem B4373297 : Blo 1293965 4373297 := bstep (se 2 (by rfl) ⟨1639986, by rfl⟩ : syracuseStep 4373297 = 3279973) B3279973
theorem B2915153 : Blo 1293965 2915153 := bstep (se 2 (by rfl) ⟨1093182, by rfl⟩ : syracuseStep 2915153 = 2186365) B2186365
theorem B2915171 : Blo 1293965 2915171 := bstep (se 1 (by rfl) ⟨2186378, by rfl⟩ : syracuseStep 2915171 = 4372757) B4372757
theorem B2186129 : Blo 1293965 2186129 := bstep (se 2 (by rfl) ⟨819798, by rfl⟩ : syracuseStep 2186129 = 1639597) B1639597
theorem B1457059 : Blo 1293965 1457059 := bstep (se 1 (by rfl) ⟨1092794, by rfl⟩ : syracuseStep 1457059 = 2185589) B2185589
theorem B6560675 : Blo 1293965 6560675 := bstep (se 1 (by rfl) ⟨4920506, by rfl⟩ : syracuseStep 6560675 = 9841013) B9841013
theorem B3275761 : Blo 1293965 3275761 := bstep (se 2 (by rfl) ⟨1228410, by rfl⟩ : syracuseStep 3275761 = 2456821) B2456821
theorem B2186257 : Blo 1293965 2186257 := bstep (se 2 (by rfl) ⟨819846, by rfl⟩ : syracuseStep 2186257 = 1639693) B1639693
theorem B1457203 : Blo 1293965 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B2186291 : Blo 1293965 2186291 := bstep (se 1 (by rfl) ⟨1639718, by rfl⟩ : syracuseStep 2186291 = 3279437) B3279437
theorem B2333777 : Blo 1293965 2333777 := bstep (se 2 (by rfl) ⟨875166, by rfl⟩ : syracuseStep 2333777 = 1750333) B1750333
theorem B2915441 : Blo 1293965 2915441 := bstep (se 2 (by rfl) ⟨1093290, by rfl⟩ : syracuseStep 2915441 = 2186581) B2186581
theorem B3112067 : Blo 1293965 3112067 := bstep (se 1 (by rfl) ⟨2334050, by rfl⟩ : syracuseStep 3112067 = 4668101) B4668101
theorem B2915459 : Blo 1293965 2915459 := bstep (se 1 (by rfl) ⟨2186594, by rfl⟩ : syracuseStep 2915459 = 4373189) B4373189
theorem B2186419 : Blo 1293965 2186419 := bstep (se 1 (by rfl) ⟨1639814, by rfl⟩ : syracuseStep 2186419 = 3279629) B3279629
theorem B1457347 : Blo 1293965 1457347 := bstep (se 1 (by rfl) ⟨1093010, by rfl⟩ : syracuseStep 1457347 = 2186021) B2186021
theorem B5250253 : Blo 1293965 5250253 := bstep (se 3 (by rfl) ⟨984422, by rfl⟩ : syracuseStep 5250253 = 1968845) B1968845
theorem B3112145 : Blo 1293965 3112145 := bstep (se 2 (by rfl) ⟨1167054, by rfl⟩ : syracuseStep 3112145 = 2334109) B2334109
theorem B3276035 : Blo 1293965 3276035 := bstep (se 1 (by rfl) ⟨2457026, by rfl⟩ : syracuseStep 3276035 = 4914053) B4914053
theorem B3939587 : Blo 1293965 3939587 := bstep (se 1 (by rfl) ⟨2954690, by rfl⟩ : syracuseStep 3939587 = 5909381) B5909381
theorem B2456867 : Blo 1293965 2456867 := bstep (se 1 (by rfl) ⟨1842650, by rfl⟩ : syracuseStep 2456867 = 3685301) B3685301
theorem B14941493 : Blo 1293965 14941493 := bstep (se 5 (by rfl) ⟨700382, by rfl⟩ : syracuseStep 14941493 = 1400765) B1400765
theorem B2186561 : Blo 1293965 2186561 := bstep (se 2 (by rfl) ⟨819960, by rfl⟩ : syracuseStep 2186561 = 1639921) B1639921
theorem B4373837 : Blo 1293965 4373837 := bstep (se 3 (by rfl) ⟨820094, by rfl⟩ : syracuseStep 4373837 = 1640189) B1640189
theorem B1457491 : Blo 1293965 1457491 := bstep (se 1 (by rfl) ⟨1093118, by rfl⟩ : syracuseStep 1457491 = 2186237) B2186237
theorem B3112337 : Blo 1293965 3112337 := bstep (se 2 (by rfl) ⟨1167126, by rfl⟩ : syracuseStep 3112337 = 2334253) B2334253
theorem B2915729 : Blo 1293965 2915729 := bstep (se 2 (by rfl) ⟨1093398, by rfl⟩ : syracuseStep 2915729 = 2186797) B2186797
theorem B1842593 : Blo 1293965 1842593 := bstep (se 2 (by rfl) ⟨690972, by rfl⟩ : syracuseStep 1842593 = 1381945) B1381945
theorem B2915747 : Blo 1293965 2915747 := bstep (se 1 (by rfl) ⟨2186810, by rfl⟩ : syracuseStep 2915747 = 4373621) B4373621
theorem B2186689 : Blo 1293965 2186689 := bstep (se 2 (by rfl) ⟨820008, by rfl⟩ : syracuseStep 2186689 = 1640017) B1640017
theorem B3276227 : Blo 1293965 3276227 := bstep (se 1 (by rfl) ⟨2457170, by rfl⟩ : syracuseStep 3276227 = 4914341) B4914341
theorem B17718725 : Blo 1293965 17718725 := bstep (se 4 (by rfl) ⟨1661130, by rfl⟩ : syracuseStep 17718725 = 3322261) B3322261
theorem B6995405 : Blo 1293965 6995405 := bstep (se 3 (by rfl) ⟨1311638, by rfl⟩ : syracuseStep 6995405 = 2623277) B2623277
theorem B1940963 : Blo 1293965 1940963 := bstep (se 1 (by rfl) ⟨1455722, by rfl⟩ : syracuseStep 1940963 = 2911445) B2911445
theorem B16588259 : Blo 1293965 16588259 := bstep (se 1 (by rfl) ⟨12441194, by rfl⟩ : syracuseStep 16588259 = 24882389) B24882389
theorem B1457635 : Blo 1293965 1457635 := bstep (se 1 (by rfl) ⟨1093226, by rfl⟩ : syracuseStep 1457635 = 2186453) B2186453
theorem B2186723 : Blo 1293965 2186723 := bstep (se 1 (by rfl) ⟨1640042, by rfl⟩ : syracuseStep 2186723 = 3280085) B3280085
theorem B1383923 : Blo 1293965 1383923 := bstep (se 1 (by rfl) ⟨1037942, by rfl⟩ : syracuseStep 1383923 = 2075885) B2075885
theorem B1940993 : Blo 1293965 1940993 := bstep (se 2 (by rfl) ⟨727872, by rfl⟩ : syracuseStep 1940993 = 1455745) B1455745
theorem B1941011 : Blo 1293965 1941011 := bstep (se 1 (by rfl) ⟨1455758, by rfl⟩ : syracuseStep 1941011 = 2911517) B2911517
theorem B1842707 : Blo 1293965 1842707 := bstep (se 1 (by rfl) ⟨1382030, by rfl⟩ : syracuseStep 1842707 = 2764061) B2764061
theorem B1941041 : Blo 1293965 1941041 := bstep (se 2 (by rfl) ⟨727890, by rfl⟩ : syracuseStep 1941041 = 1455781) B1455781
theorem B1941059 : Blo 1293965 1941059 := bstep (se 1 (by rfl) ⟨1455794, by rfl⟩ : syracuseStep 1941059 = 2911589) B2911589
theorem B2457155 : Blo 1293965 2457155 := bstep (se 1 (by rfl) ⟨1842866, by rfl⟩ : syracuseStep 2457155 = 3685733) B3685733
theorem B7380557 : Blo 1293965 7380557 := bstep (se 3 (by rfl) ⟨1383854, by rfl⟩ : syracuseStep 7380557 = 2767709) B2767709
theorem B1941089 : Blo 1293965 1941089 := bstep (se 2 (by rfl) ⟨727908, by rfl⟩ : syracuseStep 1941089 = 1455817) B1455817
theorem B1842787 : Blo 1293965 1842787 := bstep (se 1 (by rfl) ⟨1382090, by rfl⟩ : syracuseStep 1842787 = 2764181) B2764181
theorem B2186851 : Blo 1293965 2186851 := bstep (se 1 (by rfl) ⟨1640138, by rfl⟩ : syracuseStep 2186851 = 3280277) B3280277
theorem B1941107 : Blo 1293965 1941107 := bstep (se 1 (by rfl) ⟨1455830, by rfl⟩ : syracuseStep 1941107 = 2911661) B2911661
theorem B1457779 : Blo 1293965 1457779 := bstep (se 1 (by rfl) ⟨1093334, by rfl⟩ : syracuseStep 1457779 = 2186669) B2186669
theorem B1941137 : Blo 1293965 1941137 := bstep (se 2 (by rfl) ⟨727926, by rfl⟩ : syracuseStep 1941137 = 1455853) B1455853
theorem B1293971 : Blo 1293965 1293971 := bstep (se 1 (by rfl) ⟨970478, by rfl⟩ : syracuseStep 1293971 = 1940957) B1940957
theorem B1293987 : Blo 1293965 1293987 := bstep (se 1 (by rfl) ⟨970490, by rfl⟩ : syracuseStep 1293987 = 1940981) B1940981
theorem B1941155 : Blo 1293965 1941155 := bstep (se 1 (by rfl) ⟨1455866, by rfl⟩ : syracuseStep 1941155 = 2911733) B2911733
theorem B3112625 : Blo 1293965 3112625 := bstep (se 2 (by rfl) ⟨1167234, by rfl⟩ : syracuseStep 3112625 = 2334469) B2334469
theorem B1294003 : Blo 1293965 1294003 := bstep (se 1 (by rfl) ⟨970502, by rfl⟩ : syracuseStep 1294003 = 1941005) B1941005
theorem B1941185 : Blo 1293965 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B1294019 : Blo 1293965 1294019 := bstep (se 1 (by rfl) ⟨970514, by rfl⟩ : syracuseStep 1294019 = 1941029) B1941029
theorem B1638083 : Blo 1293965 1638083 := bstep (se 1 (by rfl) ⟨1228562, by rfl⟩ : syracuseStep 1638083 = 2457125) B2457125
theorem B1294035 : Blo 1293965 1294035 := bstep (se 1 (by rfl) ⟨970526, by rfl⟩ : syracuseStep 1294035 = 1941053) B1941053
theorem B1941203 : Blo 1293965 1941203 := bstep (se 1 (by rfl) ⟨1455902, by rfl⟩ : syracuseStep 1941203 = 2911805) B2911805
theorem B1294051 : Blo 1293965 1294051 := bstep (se 1 (by rfl) ⟨970538, by rfl⟩ : syracuseStep 1294051 = 1941077) B1941077
theorem B1941233 : Blo 1293965 1941233 := bstep (se 2 (by rfl) ⟨727962, by rfl⟩ : syracuseStep 1941233 = 1455925) B1455925
theorem B1294067 : Blo 1293965 1294067 := bstep (se 1 (by rfl) ⟨970550, by rfl⟩ : syracuseStep 1294067 = 1941101) B1941101
theorem B1294083 : Blo 1293965 1294083 := bstep (se 1 (by rfl) ⟨970562, by rfl⟩ : syracuseStep 1294083 = 1941125) B1941125
theorem B1941251 : Blo 1293965 1941251 := bstep (se 1 (by rfl) ⟨1455938, by rfl⟩ : syracuseStep 1941251 = 2911877) B2911877
theorem B1457923 : Blo 1293965 1457923 := bstep (se 1 (by rfl) ⟨1093442, by rfl⟩ : syracuseStep 1457923 = 2186885) B2186885
theorem B1294099 : Blo 1293965 1294099 := bstep (se 1 (by rfl) ⟨970574, by rfl⟩ : syracuseStep 1294099 = 1941149) B1941149
theorem B1941281 : Blo 1293965 1941281 := bstep (se 2 (by rfl) ⟨727980, by rfl⟩ : syracuseStep 1941281 = 1455961) B1455961
theorem B1294115 : Blo 1293965 1294115 := bstep (se 1 (by rfl) ⟨970586, by rfl⟩ : syracuseStep 1294115 = 1941173) B1941173
theorem B3989293 : Blo 1293965 3989293 := bstep (se 3 (by rfl) ⟨747992, by rfl⟩ : syracuseStep 3989293 = 1495985) B1495985
theorem B1294131 : Blo 1293965 1294131 := bstep (se 1 (by rfl) ⟨970598, by rfl⟩ : syracuseStep 1294131 = 1941197) B1941197
theorem B1941299 : Blo 1293965 1941299 := bstep (se 1 (by rfl) ⟨1455974, by rfl⟩ : syracuseStep 1941299 = 2911949) B2911949
theorem B1556275 : Blo 1293965 1556275 := bstep (se 1 (by rfl) ⟨1167206, by rfl⟩ : syracuseStep 1556275 = 2334413) B2334413
theorem B1294147 : Blo 1293965 1294147 := bstep (se 1 (by rfl) ⟨970610, by rfl⟩ : syracuseStep 1294147 = 1941221) B1941221
theorem B1941329 : Blo 1293965 1941329 := bstep (se 2 (by rfl) ⟨727998, by rfl⟩ : syracuseStep 1941329 = 1455997) B1455997
theorem B1294163 : Blo 1293965 1294163 := bstep (se 1 (by rfl) ⟨970622, by rfl⟩ : syracuseStep 1294163 = 1941245) B1941245
theorem B1294179 : Blo 1293965 1294179 := bstep (se 1 (by rfl) ⟨970634, by rfl⟩ : syracuseStep 1294179 = 1941269) B1941269
theorem B1941347 : Blo 1293965 1941347 := bstep (se 1 (by rfl) ⟨1456010, by rfl⟩ : syracuseStep 1941347 = 2912021) B2912021
theorem B1294195 : Blo 1293965 1294195 := bstep (se 1 (by rfl) ⟨970646, by rfl⟩ : syracuseStep 1294195 = 1941293) B1941293
theorem B1941377 : Blo 1293965 1941377 := bstep (se 2 (by rfl) ⟨728016, by rfl⟩ : syracuseStep 1941377 = 1456033) B1456033
theorem B1294211 : Blo 1293965 1294211 := bstep (se 1 (by rfl) ⟨970658, by rfl⟩ : syracuseStep 1294211 = 1941317) B1941317
theorem B42024845 : Blo 1293965 42024845 := bstep (se 3 (by rfl) ⟨7879658, by rfl⟩ : syracuseStep 42024845 = 15759317) B15759317
theorem B1294227 : Blo 1293965 1294227 := bstep (se 1 (by rfl) ⟨970670, by rfl⟩ : syracuseStep 1294227 = 1941341) B1941341
theorem B1941395 : Blo 1293965 1941395 := bstep (se 1 (by rfl) ⟨1456046, by rfl⟩ : syracuseStep 1941395 = 2912093) B2912093
theorem B1294243 : Blo 1293965 1294243 := bstep (se 1 (by rfl) ⟨970682, by rfl⟩ : syracuseStep 1294243 = 1941365) B1941365
theorem B1941425 : Blo 1293965 1941425 := bstep (se 2 (by rfl) ⟨728034, by rfl⟩ : syracuseStep 1941425 = 1456069) B1456069
theorem B1294259 : Blo 1293965 1294259 := bstep (se 1 (by rfl) ⟨970694, by rfl⟩ : syracuseStep 1294259 = 1941389) B1941389
theorem B1294275 : Blo 1293965 1294275 := bstep (se 1 (by rfl) ⟨970706, by rfl⟩ : syracuseStep 1294275 = 1941413) B1941413
theorem B1941443 : Blo 1293965 1941443 := bstep (se 1 (by rfl) ⟨1456082, by rfl⟩ : syracuseStep 1941443 = 2912165) B2912165
theorem B7372741 : Blo 1293965 7372741 := bstep (se 4 (by rfl) ⟨691194, by rfl⟩ : syracuseStep 7372741 = 1382389) B1382389
theorem B1294291 : Blo 1293965 1294291 := bstep (se 1 (by rfl) ⟨970718, by rfl⟩ : syracuseStep 1294291 = 1941437) B1941437
theorem B1941473 : Blo 1293965 1941473 := bstep (se 2 (by rfl) ⟨728052, by rfl⟩ : syracuseStep 1941473 = 1456105) B1456105
theorem B1294307 : Blo 1293965 1294307 := bstep (se 1 (by rfl) ⟨970730, by rfl⟩ : syracuseStep 1294307 = 1941461) B1941461
theorem B1294323 : Blo 1293965 1294323 := bstep (se 1 (by rfl) ⟨970742, by rfl⟩ : syracuseStep 1294323 = 1941485) B1941485
theorem B1941491 : Blo 1293965 1941491 := bstep (se 1 (by rfl) ⟨1456118, by rfl⟩ : syracuseStep 1941491 = 2912237) B2912237
theorem B1941515 : Blo 1293965 1941515 := bstep (se 1 (by rfl) ⟨1456136, by rfl⟩ : syracuseStep 1941515 = 2912273) B2912273
theorem B1294347 : Blo 1293965 1294347 := bstep (se 1 (by rfl) ⟨970760, by rfl⟩ : syracuseStep 1294347 = 1941521) B1941521
theorem B2457611 : Blo 1293965 2457611 := bstep (se 1 (by rfl) ⟨1843208, by rfl⟩ : syracuseStep 2457611 = 3686417) B3686417
theorem B1556491 : Blo 1293965 1556491 := bstep (se 1 (by rfl) ⟨1167368, by rfl⟩ : syracuseStep 1556491 = 2334737) B2334737
theorem B1941527 : Blo 1293965 1941527 := bstep (se 1 (by rfl) ⟨1456145, by rfl⟩ : syracuseStep 1941527 = 2912291) B2912291
theorem B1294359 : Blo 1293965 1294359 := bstep (se 1 (by rfl) ⟨970769, by rfl⟩ : syracuseStep 1294359 = 1941539) B1941539
theorem B1294379 : Blo 1293965 1294379 := bstep (se 1 (by rfl) ⟨970784, by rfl⟩ : syracuseStep 1294379 = 1941569) B1941569
theorem B10502189 : Blo 1293965 10502189 := bstep (se 3 (by rfl) ⟨1969160, by rfl⟩ : syracuseStep 10502189 = 3938321) B3938321
theorem B1294391 : Blo 1293965 1294391 := bstep (se 1 (by rfl) ⟨970793, by rfl⟩ : syracuseStep 1294391 = 1941587) B1941587
theorem B1294411 : Blo 1293965 1294411 := bstep (se 1 (by rfl) ⟨970808, by rfl⟩ : syracuseStep 1294411 = 1941617) B1941617
theorem B3276875 : Blo 1293965 3276875 := bstep (se 1 (by rfl) ⟨2457656, by rfl⟩ : syracuseStep 3276875 = 4915313) B4915313
theorem B1294423 : Blo 1293965 1294423 := bstep (se 1 (by rfl) ⟨970817, by rfl⟩ : syracuseStep 1294423 = 1941635) B1941635
theorem B1941593 : Blo 1293965 1941593 := bstep (se 2 (by rfl) ⟨728097, by rfl⟩ : syracuseStep 1941593 = 1456195) B1456195
theorem B1294443 : Blo 1293965 1294443 := bstep (se 1 (by rfl) ⟨970832, by rfl⟩ : syracuseStep 1294443 = 1941665) B1941665
theorem B1294455 : Blo 1293965 1294455 := bstep (se 1 (by rfl) ⟨970841, by rfl⟩ : syracuseStep 1294455 = 1941683) B1941683
theorem B1294475 : Blo 1293965 1294475 := bstep (se 1 (by rfl) ⟨970856, by rfl⟩ : syracuseStep 1294475 = 1941713) B1941713
theorem B1294487 : Blo 1293965 1294487 := bstep (se 1 (by rfl) ⟨970865, by rfl⟩ : syracuseStep 1294487 = 1941731) B1941731
theorem B1294507 : Blo 1293965 1294507 := bstep (se 1 (by rfl) ⟨970880, by rfl⟩ : syracuseStep 1294507 = 1941761) B1941761
theorem B1294519 : Blo 1293965 1294519 := bstep (se 1 (by rfl) ⟨970889, by rfl⟩ : syracuseStep 1294519 = 1941779) B1941779
theorem B2457793 : Blo 1293965 2457793 := bstep (se 2 (by rfl) ⟨921672, by rfl⟩ : syracuseStep 2457793 = 1843345) B1843345
theorem B1941707 : Blo 1293965 1941707 := bstep (se 1 (by rfl) ⟨1456280, by rfl⟩ : syracuseStep 1941707 = 2912561) B2912561
theorem B1294539 : Blo 1293965 1294539 := bstep (se 1 (by rfl) ⟨970904, by rfl⟩ : syracuseStep 1294539 = 1941809) B1941809
theorem B1941719 : Blo 1293965 1941719 := bstep (se 1 (by rfl) ⟨1456289, by rfl⟩ : syracuseStep 1941719 = 2912579) B2912579
theorem B1294551 : Blo 1293965 1294551 := bstep (se 1 (by rfl) ⟨970913, by rfl⟩ : syracuseStep 1294551 = 1941827) B1941827
theorem B1294571 : Blo 1293965 1294571 := bstep (se 1 (by rfl) ⟨970928, by rfl⟩ : syracuseStep 1294571 = 1941857) B1941857
theorem B1294583 : Blo 1293965 1294583 := bstep (se 1 (by rfl) ⟨970937, by rfl⟩ : syracuseStep 1294583 = 1941875) B1941875
theorem B1294603 : Blo 1293965 1294603 := bstep (se 1 (by rfl) ⟨970952, by rfl⟩ : syracuseStep 1294603 = 1941905) B1941905
theorem B1294615 : Blo 1293965 1294615 := bstep (se 1 (by rfl) ⟨970961, by rfl⟩ : syracuseStep 1294615 = 1941923) B1941923
theorem B1941785 : Blo 1293965 1941785 := bstep (se 2 (by rfl) ⟨728169, by rfl⟩ : syracuseStep 1941785 = 1456339) B1456339
theorem B1294635 : Blo 1293965 1294635 := bstep (se 1 (by rfl) ⟨970976, by rfl⟩ : syracuseStep 1294635 = 1941953) B1941953
theorem B1294647 : Blo 1293965 1294647 := bstep (se 1 (by rfl) ⟨970985, by rfl⟩ : syracuseStep 1294647 = 1941971) B1941971
theorem B1294667 : Blo 1293965 1294667 := bstep (se 1 (by rfl) ⟨971000, by rfl⟩ : syracuseStep 1294667 = 1942001) B1942001
theorem B1638731 : Blo 1293965 1638731 := bstep (se 1 (by rfl) ⟨1229048, by rfl⟩ : syracuseStep 1638731 = 2458097) B2458097
theorem B1294679 : Blo 1293965 1294679 := bstep (se 1 (by rfl) ⟨971009, by rfl⟩ : syracuseStep 1294679 = 1942019) B1942019
theorem B8298845 : Blo 1293965 8298845 := bstep (se 3 (by rfl) ⟨1556033, by rfl⟩ : syracuseStep 8298845 = 3112067) B3112067
theorem B1294699 : Blo 1293965 1294699 := bstep (se 1 (by rfl) ⟨971024, by rfl⟩ : syracuseStep 1294699 = 1942049) B1942049
theorem B1294711 : Blo 1293965 1294711 := bstep (se 1 (by rfl) ⟨971033, by rfl⟩ : syracuseStep 1294711 = 1942067) B1942067
theorem B1941899 : Blo 1293965 1941899 := bstep (se 1 (by rfl) ⟨1456424, by rfl⟩ : syracuseStep 1941899 = 2912849) B2912849
theorem B1294731 : Blo 1293965 1294731 := bstep (se 1 (by rfl) ⟨971048, by rfl⟩ : syracuseStep 1294731 = 1942097) B1942097
theorem B9830807 : Blo 1293965 9830807 := bstep (se 1 (by rfl) ⟨7373105, by rfl⟩ : syracuseStep 9830807 = 14746211) B14746211
theorem B1941911 : Blo 1293965 1941911 := bstep (se 1 (by rfl) ⟨1456433, by rfl⟩ : syracuseStep 1941911 = 2912867) B2912867
theorem B1294743 : Blo 1293965 1294743 := bstep (se 1 (by rfl) ⟨971057, by rfl⟩ : syracuseStep 1294743 = 1942115) B1942115
theorem B1843607 : Blo 1293965 1843607 := bstep (se 1 (by rfl) ⟨1382705, by rfl⟩ : syracuseStep 1843607 = 2765411) B2765411
theorem B1294763 : Blo 1293965 1294763 := bstep (se 1 (by rfl) ⟨971072, by rfl⟩ : syracuseStep 1294763 = 1942145) B1942145
theorem B1294775 : Blo 1293965 1294775 := bstep (se 1 (by rfl) ⟨971081, by rfl⟩ : syracuseStep 1294775 = 1942163) B1942163
theorem B1294795 : Blo 1293965 1294795 := bstep (se 1 (by rfl) ⟨971096, by rfl⟩ : syracuseStep 1294795 = 1942193) B1942193
theorem B1294807 : Blo 1293965 1294807 := bstep (se 1 (by rfl) ⟨971105, by rfl⟩ : syracuseStep 1294807 = 1942211) B1942211
theorem B1941977 : Blo 1293965 1941977 := bstep (se 2 (by rfl) ⟨728241, by rfl⟩ : syracuseStep 1941977 = 1456483) B1456483
theorem B1294827 : Blo 1293965 1294827 := bstep (se 1 (by rfl) ⟨971120, by rfl⟩ : syracuseStep 1294827 = 1942241) B1942241
theorem B1294839 : Blo 1293965 1294839 := bstep (se 1 (by rfl) ⟨971129, by rfl⟩ : syracuseStep 1294839 = 1942259) B1942259
theorem B1294859 : Blo 1293965 1294859 := bstep (se 1 (by rfl) ⟨971144, by rfl⟩ : syracuseStep 1294859 = 1942289) B1942289
theorem B1294871 : Blo 1293965 1294871 := bstep (se 1 (by rfl) ⟨971153, by rfl⟩ : syracuseStep 1294871 = 1942307) B1942307
theorem B1294891 : Blo 1293965 1294891 := bstep (se 1 (by rfl) ⟨971168, by rfl⟩ : syracuseStep 1294891 = 1942337) B1942337
theorem B1294903 : Blo 1293965 1294903 := bstep (se 1 (by rfl) ⟨971177, by rfl⟩ : syracuseStep 1294903 = 1942355) B1942355
theorem B1942091 : Blo 1293965 1942091 := bstep (se 1 (by rfl) ⟨1456568, by rfl⟩ : syracuseStep 1942091 = 2913137) B2913137
theorem B1294923 : Blo 1293965 1294923 := bstep (se 1 (by rfl) ⟨971192, by rfl⟩ : syracuseStep 1294923 = 1942385) B1942385
theorem B18678347 : Blo 1293965 18678347 := bstep (se 1 (by rfl) ⟨14008760, by rfl⟩ : syracuseStep 18678347 = 28017521) B28017521
theorem B1942103 : Blo 1293965 1942103 := bstep (se 1 (by rfl) ⟨1456577, by rfl⟩ : syracuseStep 1942103 = 2913155) B2913155
theorem B1294935 : Blo 1293965 1294935 := bstep (se 1 (by rfl) ⟨971201, by rfl⟩ : syracuseStep 1294935 = 1942403) B1942403
theorem B1294955 : Blo 1293965 1294955 := bstep (se 1 (by rfl) ⟨971216, by rfl⟩ : syracuseStep 1294955 = 1942433) B1942433
theorem B1294967 : Blo 1293965 1294967 := bstep (se 1 (by rfl) ⟨971225, by rfl⟩ : syracuseStep 1294967 = 1942451) B1942451
theorem B1294987 : Blo 1293965 1294987 := bstep (se 1 (by rfl) ⟨971240, by rfl⟩ : syracuseStep 1294987 = 1942481) B1942481
theorem B1294999 : Blo 1293965 1294999 := bstep (se 1 (by rfl) ⟨971249, by rfl⟩ : syracuseStep 1294999 = 1942499) B1942499
theorem B1942169 : Blo 1293965 1942169 := bstep (se 2 (by rfl) ⟨728313, by rfl⟩ : syracuseStep 1942169 = 1456627) B1456627
theorem B1295019 : Blo 1293965 1295019 := bstep (se 1 (by rfl) ⟨971264, by rfl⟩ : syracuseStep 1295019 = 1942529) B1942529
theorem B1295031 : Blo 1293965 1295031 := bstep (se 1 (by rfl) ⟨971273, by rfl⟩ : syracuseStep 1295031 = 1942547) B1942547
theorem B1295051 : Blo 1293965 1295051 := bstep (se 1 (by rfl) ⟨971288, by rfl⟩ : syracuseStep 1295051 = 1942577) B1942577
theorem B1295063 : Blo 1293965 1295063 := bstep (se 1 (by rfl) ⟨971297, by rfl⟩ : syracuseStep 1295063 = 1942595) B1942595
theorem B1295083 : Blo 1293965 1295083 := bstep (se 1 (by rfl) ⟨971312, by rfl⟩ : syracuseStep 1295083 = 1942625) B1942625
theorem B1295095 : Blo 1293965 1295095 := bstep (se 1 (by rfl) ⟨971321, by rfl⟩ : syracuseStep 1295095 = 1942643) B1942643
theorem B1942283 : Blo 1293965 1942283 := bstep (se 1 (by rfl) ⟨1456712, by rfl⟩ : syracuseStep 1942283 = 2913425) B2913425
theorem B1295115 : Blo 1293965 1295115 := bstep (se 1 (by rfl) ⟨971336, by rfl⟩ : syracuseStep 1295115 = 1942673) B1942673
theorem B3687191 : Blo 1293965 3687191 := bstep (se 1 (by rfl) ⟨2765393, by rfl⟩ : syracuseStep 3687191 = 5530787) B5530787
theorem B1942295 : Blo 1293965 1942295 := bstep (se 1 (by rfl) ⟨1456721, by rfl⟩ : syracuseStep 1942295 = 2913443) B2913443
theorem B1295127 : Blo 1293965 1295127 := bstep (se 1 (by rfl) ⟨971345, by rfl⟩ : syracuseStep 1295127 = 1942691) B1942691
theorem B1295147 : Blo 1293965 1295147 := bstep (se 1 (by rfl) ⟨971360, by rfl⟩ : syracuseStep 1295147 = 1942721) B1942721
theorem B1295159 : Blo 1293965 1295159 := bstep (se 1 (by rfl) ⟨971369, by rfl⟩ : syracuseStep 1295159 = 1942739) B1942739
theorem B1295179 : Blo 1293965 1295179 := bstep (se 1 (by rfl) ⟨971384, by rfl⟩ : syracuseStep 1295179 = 1942769) B1942769
theorem B1942361 : Blo 1293965 1942361 := bstep (se 2 (by rfl) ⟨728385, by rfl⟩ : syracuseStep 1942361 = 1456771) B1456771
theorem B1295191 : Blo 1293965 1295191 := bstep (se 1 (by rfl) ⟨971393, by rfl⟩ : syracuseStep 1295191 = 1942787) B1942787
theorem B1295211 : Blo 1293965 1295211 := bstep (se 1 (by rfl) ⟨971408, by rfl⟩ : syracuseStep 1295211 = 1942817) B1942817
theorem B1295223 : Blo 1293965 1295223 := bstep (se 1 (by rfl) ⟨971417, by rfl⟩ : syracuseStep 1295223 = 1942835) B1942835
theorem B7373699 : Blo 1293965 7373699 := bstep (se 1 (by rfl) ⟨5530274, by rfl⟩ : syracuseStep 7373699 = 11060549) B11060549
theorem B2458507 : Blo 1293965 2458507 := bstep (se 1 (by rfl) ⟨1843880, by rfl⟩ : syracuseStep 2458507 = 3687761) B3687761
theorem B1295243 : Blo 1293965 1295243 := bstep (se 1 (by rfl) ⟨971432, by rfl⟩ : syracuseStep 1295243 = 1942865) B1942865
theorem B5530513 : Blo 1293965 5530513 := bstep (se 2 (by rfl) ⟨2073942, by rfl⟩ : syracuseStep 5530513 = 4147885) B4147885
theorem B6554519 : Blo 1293965 6554519 := bstep (se 1 (by rfl) ⟨4915889, by rfl⟩ : syracuseStep 6554519 = 9831779) B9831779
theorem B1295255 : Blo 1293965 1295255 := bstep (se 1 (by rfl) ⟨971441, by rfl⟩ : syracuseStep 1295255 = 1942883) B1942883
theorem B1295275 : Blo 1293965 1295275 := bstep (se 1 (by rfl) ⟨971456, by rfl⟩ : syracuseStep 1295275 = 1942913) B1942913
theorem B1311671 : Blo 1293965 1311671 := bstep (se 1 (by rfl) ⟨983753, by rfl⟩ : syracuseStep 1311671 = 1967507) B1967507
theorem B1295287 : Blo 1293965 1295287 := bstep (se 1 (by rfl) ⟨971465, by rfl⟩ : syracuseStep 1295287 = 1942931) B1942931
theorem B1942475 : Blo 1293965 1942475 := bstep (se 1 (by rfl) ⟨1456856, by rfl⟩ : syracuseStep 1942475 = 2913713) B2913713
theorem B1295307 : Blo 1293965 1295307 := bstep (se 1 (by rfl) ⟨971480, by rfl⟩ : syracuseStep 1295307 = 1942961) B1942961
theorem B1942487 : Blo 1293965 1942487 := bstep (se 1 (by rfl) ⟨1456865, by rfl⟩ : syracuseStep 1942487 = 2913731) B2913731
theorem B2458583 : Blo 1293965 2458583 := bstep (se 1 (by rfl) ⟨1843937, by rfl⟩ : syracuseStep 2458583 = 3687875) B3687875
theorem B1295319 : Blo 1293965 1295319 := bstep (se 1 (by rfl) ⟨971489, by rfl⟩ : syracuseStep 1295319 = 1942979) B1942979
theorem B1295339 : Blo 1293965 1295339 := bstep (se 1 (by rfl) ⟨971504, by rfl⟩ : syracuseStep 1295339 = 1943009) B1943009
theorem B1295351 : Blo 1293965 1295351 := bstep (se 1 (by rfl) ⟨971513, by rfl⟩ : syracuseStep 1295351 = 1943027) B1943027
theorem B1639435 : Blo 1293965 1639435 := bstep (se 1 (by rfl) ⟨1229576, by rfl⟩ : syracuseStep 1639435 = 2459153) B2459153
theorem B1295371 : Blo 1293965 1295371 := bstep (se 1 (by rfl) ⟨971528, by rfl⟩ : syracuseStep 1295371 = 1943057) B1943057
theorem B3277847 : Blo 1293965 3277847 := bstep (se 1 (by rfl) ⟨2458385, by rfl⟩ : syracuseStep 3277847 = 4916771) B4916771
theorem B1942553 : Blo 1293965 1942553 := bstep (se 2 (by rfl) ⟨728457, by rfl⟩ : syracuseStep 1942553 = 1456915) B1456915
theorem B1295383 : Blo 1293965 1295383 := bstep (se 1 (by rfl) ⟨971537, by rfl⟩ : syracuseStep 1295383 = 1943075) B1943075
theorem B1295403 : Blo 1293965 1295403 := bstep (se 1 (by rfl) ⟨971552, by rfl⟩ : syracuseStep 1295403 = 1943105) B1943105
theorem B4367411 : Blo 1293965 4367411 := bstep (se 1 (by rfl) ⟨3275558, by rfl⟩ : syracuseStep 4367411 = 6551117) B6551117
theorem B1295415 : Blo 1293965 1295415 := bstep (se 1 (by rfl) ⟨971561, by rfl⟩ : syracuseStep 1295415 = 1943123) B1943123
theorem B1295435 : Blo 1293965 1295435 := bstep (se 1 (by rfl) ⟨971576, by rfl⟩ : syracuseStep 1295435 = 1943153) B1943153
theorem B1295447 : Blo 1293965 1295447 := bstep (se 1 (by rfl) ⟨971585, by rfl⟩ : syracuseStep 1295447 = 1943171) B1943171
theorem B1295467 : Blo 1293965 1295467 := bstep (se 1 (by rfl) ⟨971600, by rfl⟩ : syracuseStep 1295467 = 1943201) B1943201
theorem B1295479 : Blo 1293965 1295479 := bstep (se 1 (by rfl) ⟨971609, by rfl⟩ : syracuseStep 1295479 = 1943219) B1943219
theorem B20997251 : Blo 1293965 20997251 := bstep (se 1 (by rfl) ⟨15747938, by rfl⟩ : syracuseStep 20997251 = 31495877) B31495877
theorem B1942667 : Blo 1293965 1942667 := bstep (se 1 (by rfl) ⟨1457000, by rfl⟩ : syracuseStep 1942667 = 2914001) B2914001
theorem B1295499 : Blo 1293965 1295499 := bstep (se 1 (by rfl) ⟨971624, by rfl⟩ : syracuseStep 1295499 = 1943249) B1943249
theorem B1475735 : Blo 1293965 1475735 := bstep (se 1 (by rfl) ⟨1106801, by rfl⟩ : syracuseStep 1475735 = 2213603) B2213603
theorem B1942679 : Blo 1293965 1942679 := bstep (se 1 (by rfl) ⟨1457009, by rfl⟩ : syracuseStep 1942679 = 2914019) B2914019
theorem B1295511 : Blo 1293965 1295511 := bstep (se 1 (by rfl) ⟨971633, by rfl⟩ : syracuseStep 1295511 = 1943267) B1943267
theorem B1295531 : Blo 1293965 1295531 := bstep (se 1 (by rfl) ⟨971648, by rfl⟩ : syracuseStep 1295531 = 1943297) B1943297
theorem B1295543 : Blo 1293965 1295543 := bstep (se 1 (by rfl) ⟨971657, by rfl⟩ : syracuseStep 1295543 = 1943315) B1943315
theorem B1295563 : Blo 1293965 1295563 := bstep (se 1 (by rfl) ⟨971672, by rfl⟩ : syracuseStep 1295563 = 1943345) B1943345
theorem B1295575 : Blo 1293965 1295575 := bstep (se 1 (by rfl) ⟨971681, by rfl⟩ : syracuseStep 1295575 = 1943363) B1943363
theorem B1942745 : Blo 1293965 1942745 := bstep (se 2 (by rfl) ⟨728529, by rfl⟩ : syracuseStep 1942745 = 1457059) B1457059
theorem B1295595 : Blo 1293965 1295595 := bstep (se 1 (by rfl) ⟨971696, by rfl⟩ : syracuseStep 1295595 = 1943393) B1943393
theorem B1295607 : Blo 1293965 1295607 := bstep (se 1 (by rfl) ⟨971705, by rfl⟩ : syracuseStep 1295607 = 1943411) B1943411
theorem B4916483 : Blo 1293965 4916483 := bstep (se 1 (by rfl) ⟨3687362, by rfl⟩ : syracuseStep 4916483 = 7374725) B7374725
theorem B1295627 : Blo 1293965 1295627 := bstep (se 1 (by rfl) ⟨971720, by rfl⟩ : syracuseStep 1295627 = 1943441) B1943441
theorem B4916497 : Blo 1293965 4916497 := bstep (se 2 (by rfl) ⟨1843686, by rfl⟩ : syracuseStep 4916497 = 3687373) B3687373
theorem B1639703 : Blo 1293965 1639703 := bstep (se 1 (by rfl) ⟨1229777, by rfl⟩ : syracuseStep 1639703 = 2459555) B2459555
theorem B1295639 : Blo 1293965 1295639 := bstep (se 1 (by rfl) ⟨971729, by rfl⟩ : syracuseStep 1295639 = 1943459) B1943459
theorem B1295659 : Blo 1293965 1295659 := bstep (se 1 (by rfl) ⟨971744, by rfl⟩ : syracuseStep 1295659 = 1943489) B1943489
theorem B1295671 : Blo 1293965 1295671 := bstep (se 1 (by rfl) ⟨971753, by rfl⟩ : syracuseStep 1295671 = 1943507) B1943507
theorem B4367681 : Blo 1293965 4367681 := bstep (se 2 (by rfl) ⟨1637880, by rfl⟩ : syracuseStep 4367681 = 3275761) B3275761
theorem B1942859 : Blo 1293965 1942859 := bstep (se 1 (by rfl) ⟨1457144, by rfl⟩ : syracuseStep 1942859 = 2914289) B2914289
theorem B1295691 : Blo 1293965 1295691 := bstep (se 1 (by rfl) ⟨971768, by rfl⟩ : syracuseStep 1295691 = 1943537) B1943537
theorem B1942871 : Blo 1293965 1942871 := bstep (se 1 (by rfl) ⟨1457153, by rfl⟩ : syracuseStep 1942871 = 2914307) B2914307
theorem B1295703 : Blo 1293965 1295703 := bstep (se 1 (by rfl) ⟨971777, by rfl⟩ : syracuseStep 1295703 = 1943555) B1943555
theorem B2131289 : Blo 1293965 2131289 := bstep (se 2 (by rfl) ⟨799233, by rfl⟩ : syracuseStep 2131289 = 1598467) B1598467
theorem B1295723 : Blo 1293965 1295723 := bstep (se 1 (by rfl) ⟨971792, by rfl⟩ : syracuseStep 1295723 = 1943585) B1943585
theorem B1295735 : Blo 1293965 1295735 := bstep (se 1 (by rfl) ⟨971801, by rfl⟩ : syracuseStep 1295735 = 1943603) B1943603
theorem B1295755 : Blo 1293965 1295755 := bstep (se 1 (by rfl) ⟨971816, by rfl⟩ : syracuseStep 1295755 = 1943633) B1943633
theorem B1295767 : Blo 1293965 1295767 := bstep (se 1 (by rfl) ⟨971825, by rfl⟩ : syracuseStep 1295767 = 1943651) B1943651
theorem B1942937 : Blo 1293965 1942937 := bstep (se 2 (by rfl) ⟨728601, by rfl⟩ : syracuseStep 1942937 = 1457203) B1457203
theorem B1295787 : Blo 1293965 1295787 := bstep (se 1 (by rfl) ⟨971840, by rfl⟩ : syracuseStep 1295787 = 1943681) B1943681
theorem B12617137 : Blo 1293965 12617137 := bstep (se 2 (by rfl) ⟨4731426, by rfl⟩ : syracuseStep 12617137 = 9462853) B9462853
theorem B1295799 : Blo 1293965 1295799 := bstep (se 1 (by rfl) ⟨971849, by rfl⟩ : syracuseStep 1295799 = 1943699) B1943699
theorem B1295819 : Blo 1293965 1295819 := bstep (se 1 (by rfl) ⟨971864, by rfl⟩ : syracuseStep 1295819 = 1943729) B1943729
theorem B1295831 : Blo 1293965 1295831 := bstep (se 1 (by rfl) ⟨971873, by rfl⟩ : syracuseStep 1295831 = 1943747) B1943747
theorem B1295851 : Blo 1293965 1295851 := bstep (se 1 (by rfl) ⟨971888, by rfl⟩ : syracuseStep 1295851 = 1943777) B1943777
theorem B1295863 : Blo 1293965 1295863 := bstep (se 1 (by rfl) ⟨971897, by rfl⟩ : syracuseStep 1295863 = 1943795) B1943795
theorem B1943051 : Blo 1293965 1943051 := bstep (se 1 (by rfl) ⟨1457288, by rfl⟩ : syracuseStep 1943051 = 2914577) B2914577
theorem B1295883 : Blo 1293965 1295883 := bstep (se 1 (by rfl) ⟨971912, by rfl⟩ : syracuseStep 1295883 = 1943825) B1943825
theorem B1943063 : Blo 1293965 1943063 := bstep (se 1 (by rfl) ⟨1457297, by rfl⟩ : syracuseStep 1943063 = 2914595) B2914595
theorem B1295895 : Blo 1293965 1295895 := bstep (se 1 (by rfl) ⟨971921, by rfl⟩ : syracuseStep 1295895 = 1943843) B1943843
theorem B9463331 : Blo 1293965 9463331 := bstep (se 1 (by rfl) ⟨7097498, by rfl⟩ : syracuseStep 9463331 = 14194997) B14194997
theorem B1295915 : Blo 1293965 1295915 := bstep (se 1 (by rfl) ⟨971936, by rfl⟩ : syracuseStep 1295915 = 1943873) B1943873
theorem B1295927 : Blo 1293965 1295927 := bstep (se 1 (by rfl) ⟨971945, by rfl⟩ : syracuseStep 1295927 = 1943891) B1943891
theorem B4916801 : Blo 1293965 4916801 := bstep (se 2 (by rfl) ⟨1843800, by rfl⟩ : syracuseStep 4916801 = 3687601) B3687601
theorem B3688001 : Blo 1293965 3688001 := bstep (se 2 (by rfl) ⟨1383000, by rfl⟩ : syracuseStep 3688001 = 2766001) B2766001
theorem B4982347 : Blo 1293965 4982347 := bstep (se 1 (by rfl) ⟨3736760, by rfl⟩ : syracuseStep 4982347 = 7473521) B7473521
theorem B1295947 : Blo 1293965 1295947 := bstep (se 1 (by rfl) ⟨971960, by rfl⟩ : syracuseStep 1295947 = 1943921) B1943921
theorem B1295959 : Blo 1293965 1295959 := bstep (se 1 (by rfl) ⟨971969, by rfl⟩ : syracuseStep 1295959 = 1943939) B1943939
theorem B1943129 : Blo 1293965 1943129 := bstep (se 2 (by rfl) ⟨728673, by rfl⟩ : syracuseStep 1943129 = 1457347) B1457347
theorem B2459251 : Blo 1293965 2459251 := bstep (se 1 (by rfl) ⟨1844438, by rfl⟩ : syracuseStep 2459251 = 3688877) B3688877
theorem B3278515 : Blo 1293965 3278515 := bstep (se 1 (by rfl) ⟨2458886, by rfl⟩ : syracuseStep 3278515 = 4917773) B4917773
theorem B1943243 : Blo 1293965 1943243 := bstep (se 1 (by rfl) ⟨1457432, by rfl⟩ : syracuseStep 1943243 = 2914865) B2914865
theorem B1943255 : Blo 1293965 1943255 := bstep (se 1 (by rfl) ⟨1457441, by rfl⟩ : syracuseStep 1943255 = 2914883) B2914883
theorem B1943321 : Blo 1293965 1943321 := bstep (se 2 (by rfl) ⟨728745, by rfl⟩ : syracuseStep 1943321 = 1457491) B1457491
theorem B8300333 : Blo 1293965 8300333 := bstep (se 3 (by rfl) ⟨1556312, by rfl⟩ : syracuseStep 8300333 = 3112625) B3112625
theorem B4982579 : Blo 1293965 4982579 := bstep (se 1 (by rfl) ⟨3736934, by rfl⟩ : syracuseStep 4982579 = 7473869) B7473869
theorem B24889153 : Blo 1293965 24889153 := bstep (se 2 (by rfl) ⟨9333432, by rfl⟩ : syracuseStep 24889153 = 18666865) B18666865
theorem B3278657 : Blo 1293965 3278657 := bstep (se 2 (by rfl) ⟨1229496, by rfl⟩ : syracuseStep 3278657 = 2458993) B2458993
theorem B2459479 : Blo 1293965 2459479 := bstep (se 1 (by rfl) ⟨1844609, by rfl⟩ : syracuseStep 2459479 = 3689219) B3689219
theorem B3499865 : Blo 1293965 3499865 := bstep (se 2 (by rfl) ⟨1312449, by rfl⟩ : syracuseStep 3499865 = 2624899) B2624899
theorem B4368221 : Blo 1293965 4368221 := bstep (se 3 (by rfl) ⟨819041, by rfl⟩ : syracuseStep 4368221 = 1638083) B1638083
theorem B1943435 : Blo 1293965 1943435 := bstep (se 1 (by rfl) ⟨1457576, by rfl⟩ : syracuseStep 1943435 = 2915153) B2915153
theorem B1943447 : Blo 1293965 1943447 := bstep (se 1 (by rfl) ⟨1457585, by rfl⟩ : syracuseStep 1943447 = 2915171) B2915171
theorem B2803609 : Blo 1293965 2803609 := bstep (se 2 (by rfl) ⟨1051353, by rfl⟩ : syracuseStep 2803609 = 2102707) B2102707
theorem B2459585 : Blo 1293965 2459585 := bstep (se 2 (by rfl) ⟨922344, by rfl⟩ : syracuseStep 2459585 = 1844689) B1844689
theorem B1943513 : Blo 1293965 1943513 := bstep (se 2 (by rfl) ⟨728817, by rfl⟩ : syracuseStep 1943513 = 1457635) B1457635
theorem B1943627 : Blo 1293965 1943627 := bstep (se 1 (by rfl) ⟨1457720, by rfl⟩ : syracuseStep 1943627 = 2915441) B2915441
theorem B1943639 : Blo 1293965 1943639 := bstep (se 1 (by rfl) ⟨1457729, by rfl⟩ : syracuseStep 1943639 = 2915459) B2915459
theorem B2459737 : Blo 1293965 2459737 := bstep (se 2 (by rfl) ⟨922401, by rfl⟩ : syracuseStep 2459737 = 1844803) B1844803
theorem B2623603 : Blo 1293965 2623603 := bstep (se 1 (by rfl) ⟨1967702, by rfl⟩ : syracuseStep 2623603 = 3935405) B3935405
theorem B2074763 : Blo 1293965 2074763 := bstep (se 1 (by rfl) ⟨1556072, by rfl⟩ : syracuseStep 2074763 = 3112145) B3112145
theorem B1943705 : Blo 1293965 1943705 := bstep (se 2 (by rfl) ⟨728889, by rfl⟩ : syracuseStep 1943705 = 1457779) B1457779
theorem B4917469 : Blo 1293965 4917469 := bstep (se 3 (by rfl) ⟨922025, by rfl⟩ : syracuseStep 4917469 = 1844051) B1844051
theorem B2074891 : Blo 1293965 2074891 := bstep (se 1 (by rfl) ⟨1556168, by rfl⟩ : syracuseStep 2074891 = 3112337) B3112337
theorem B1943819 : Blo 1293965 1943819 := bstep (se 1 (by rfl) ⟨1457864, by rfl⟩ : syracuseStep 1943819 = 2915729) B2915729
theorem B1943831 : Blo 1293965 1943831 := bstep (se 1 (by rfl) ⟨1457873, by rfl⟩ : syracuseStep 1943831 = 2915747) B2915747
theorem B4663603 : Blo 1293965 4663603 := bstep (se 1 (by rfl) ⟨3497702, by rfl⟩ : syracuseStep 4663603 = 6995405) B6995405
theorem B1943897 : Blo 1293965 1943897 := bstep (se 2 (by rfl) ⟨728961, by rfl⟩ : syracuseStep 1943897 = 1457923) B1457923
theorem B2075033 : Blo 1293965 2075033 := bstep (se 2 (by rfl) ⟨778137, by rfl⟩ : syracuseStep 2075033 = 1556275) B1556275
theorem B2214425 : Blo 1293965 2214425 := bstep (se 2 (by rfl) ⟨830409, by rfl⟩ : syracuseStep 2214425 = 1660819) B1660819
theorem B2624089 : Blo 1293965 2624089 := bstep (se 2 (by rfl) ⟨984033, by rfl⟩ : syracuseStep 2624089 = 1968067) B1968067
theorem B3787415 : Blo 1293965 3787415 := bstep (se 1 (by rfl) ⟨2840561, by rfl⟩ : syracuseStep 3787415 = 5681123) B5681123
theorem B1419991 : Blo 1293965 1419991 := bstep (se 1 (by rfl) ⟨1064993, by rfl⟩ : syracuseStep 1419991 = 2129987) B2129987
theorem B19942129 : Blo 1293965 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B4369355 : Blo 1293965 4369355 := bstep (se 1 (by rfl) ⟨3277016, by rfl⟩ : syracuseStep 4369355 = 6554033) B6554033
theorem B3279923 : Blo 1293965 3279923 := bstep (se 1 (by rfl) ⟨2459942, by rfl⟩ : syracuseStep 3279923 = 4919885) B4919885
theorem B3689651 : Blo 1293965 3689651 := bstep (se 1 (by rfl) ⟨2767238, by rfl⟩ : syracuseStep 3689651 = 5534477) B5534477
theorem B3689675 : Blo 1293965 3689675 := bstep (se 1 (by rfl) ⟨2767256, by rfl⟩ : syracuseStep 3689675 = 5534513) B5534513
theorem B4369625 : Blo 1293965 4369625 := bstep (se 2 (by rfl) ⟨1638609, by rfl⟩ : syracuseStep 4369625 = 3277219) B3277219
theorem B2526425 : Blo 1293965 2526425 := bstep (se 2 (by rfl) ⟨947409, by rfl⟩ : syracuseStep 2526425 = 1894819) B1894819
theorem B2764019 : Blo 1293965 2764019 := bstep (se 1 (by rfl) ⟨2073014, by rfl⟩ : syracuseStep 2764019 = 4146029) B4146029
theorem B2911499 : Blo 1293965 2911499 := bstep (se 1 (by rfl) ⟨2183624, by rfl⟩ : syracuseStep 2911499 = 4367249) B4367249
theorem B2911553 : Blo 1293965 2911553 := bstep (se 2 (by rfl) ⟨1091832, by rfl⟩ : syracuseStep 2911553 = 2183665) B2183665
theorem B4664641 : Blo 1293965 4664641 := bstep (se 2 (by rfl) ⟨1749240, by rfl⟩ : syracuseStep 4664641 = 3498481) B3498481
theorem B8293697 : Blo 1293965 8293697 := bstep (se 2 (by rfl) ⟨3110136, by rfl⟩ : syracuseStep 8293697 = 6220273) B6220273
theorem B10505537 : Blo 1293965 10505537 := bstep (se 2 (by rfl) ⟨3939576, by rfl⟩ : syracuseStep 10505537 = 7879153) B7879153
theorem B4918745 : Blo 1293965 4918745 := bstep (se 2 (by rfl) ⟨1844529, by rfl⟩ : syracuseStep 4918745 = 3689059) B3689059
theorem B2911769 : Blo 1293965 2911769 := bstep (se 2 (by rfl) ⟨1091913, by rfl⟩ : syracuseStep 2911769 = 2183827) B2183827
theorem B2911859 : Blo 1293965 2911859 := bstep (se 1 (by rfl) ⟨2183894, by rfl⟩ : syracuseStep 2911859 = 4367789) B4367789
theorem B2911895 : Blo 1293965 2911895 := bstep (se 1 (by rfl) ⟨2183921, by rfl⟩ : syracuseStep 2911895 = 4367843) B4367843
theorem B2764505 : Blo 1293965 2764505 := bstep (se 2 (by rfl) ⟨1036689, by rfl⟩ : syracuseStep 2764505 = 2073379) B2073379
theorem B5533505 : Blo 1293965 5533505 := bstep (se 2 (by rfl) ⟨2075064, by rfl⟩ : syracuseStep 5533505 = 4150129) B4150129
theorem B2912075 : Blo 1293965 2912075 := bstep (se 1 (by rfl) ⟨2184056, by rfl⟩ : syracuseStep 2912075 = 4368113) B4368113
theorem B2912129 : Blo 1293965 2912129 := bstep (se 2 (by rfl) ⟨1092048, by rfl⟩ : syracuseStep 2912129 = 2184097) B2184097
theorem B4370327 : Blo 1293965 4370327 := bstep (se 1 (by rfl) ⟨3277745, by rfl⟩ : syracuseStep 4370327 = 6555491) B6555491
theorem B3690461 : Blo 1293965 3690461 := bstep (se 3 (by rfl) ⟨691961, by rfl⟩ : syracuseStep 3690461 = 1383923) B1383923
theorem B5607427 : Blo 1293965 5607427 := bstep (se 1 (by rfl) ⟨4205570, by rfl⟩ : syracuseStep 5607427 = 8411141) B8411141
theorem B11055149 : Blo 1293965 11055149 := bstep (se 3 (by rfl) ⟨2072840, by rfl⟩ : syracuseStep 11055149 = 4145681) B4145681
theorem B2912345 : Blo 1293965 2912345 := bstep (se 2 (by rfl) ⟨1092129, by rfl⟩ : syracuseStep 2912345 = 2184259) B2184259
theorem B4665437 : Blo 1293965 4665437 := bstep (se 3 (by rfl) ⟨874769, by rfl⟩ : syracuseStep 4665437 = 1749539) B1749539
theorem B8982629 : Blo 1293965 8982629 := bstep (se 4 (by rfl) ⟨842121, by rfl⟩ : syracuseStep 8982629 = 1684243) B1684243
theorem B10506341 : Blo 1293965 10506341 := bstep (se 4 (by rfl) ⟨984969, by rfl⟩ : syracuseStep 10506341 = 1969939) B1969939
theorem B2953369 : Blo 1293965 2953369 := bstep (se 2 (by rfl) ⟨1107513, by rfl⟩ : syracuseStep 2953369 = 2215027) B2215027
theorem B2912435 : Blo 1293965 2912435 := bstep (se 1 (by rfl) ⟨2184326, by rfl⟩ : syracuseStep 2912435 = 4368653) B4368653
theorem B2912471 : Blo 1293965 2912471 := bstep (se 1 (by rfl) ⟨2184353, by rfl⟩ : syracuseStep 2912471 = 4368707) B4368707
theorem B5902595 : Blo 1293965 5902595 := bstep (se 1 (by rfl) ⟨4426946, by rfl⟩ : syracuseStep 5902595 = 8853893) B8853893
theorem B7000337 : Blo 1293965 7000337 := bstep (se 2 (by rfl) ⟨2625126, by rfl⟩ : syracuseStep 7000337 = 5250253) B5250253
theorem B4428083 : Blo 1293965 4428083 := bstep (se 1 (by rfl) ⟨3321062, by rfl⟩ : syracuseStep 4428083 = 6642125) B6642125
theorem B2953523 : Blo 1293965 2953523 := bstep (se 1 (by rfl) ⟨2215142, by rfl⟩ : syracuseStep 2953523 = 4430285) B4430285
theorem B1749323 : Blo 1293965 1749323 := bstep (se 1 (by rfl) ⟨1311992, by rfl⟩ : syracuseStep 1749323 = 2623985) B2623985
theorem B6558083 : Blo 1293965 6558083 := bstep (se 1 (by rfl) ⟨4918562, by rfl⟩ : syracuseStep 6558083 = 9837125) B9837125
theorem B2912651 : Blo 1293965 2912651 := bstep (se 1 (by rfl) ⟨2184488, by rfl⟩ : syracuseStep 2912651 = 4368977) B4368977
theorem B4370867 : Blo 1293965 4370867 := bstep (se 1 (by rfl) ⟨3278150, by rfl⟩ : syracuseStep 4370867 = 6556301) B6556301
theorem B2912705 : Blo 1293965 2912705 := bstep (se 2 (by rfl) ⟨1092264, by rfl⟩ : syracuseStep 2912705 = 2184529) B2184529
theorem B2765249 : Blo 1293965 2765249 := bstep (se 2 (by rfl) ⟨1036968, by rfl⟩ : syracuseStep 2765249 = 2073937) B2073937
theorem B8303255 : Blo 1293965 8303255 := bstep (se 1 (by rfl) ⟨6227441, by rfl⟩ : syracuseStep 8303255 = 12454883) B12454883
theorem B2912921 : Blo 1293965 2912921 := bstep (se 2 (by rfl) ⟨1092345, by rfl⟩ : syracuseStep 2912921 = 2184691) B2184691
theorem B4371137 : Blo 1293965 4371137 := bstep (se 2 (by rfl) ⟨1639176, by rfl⟩ : syracuseStep 4371137 = 3278353) B3278353
theorem B2913011 : Blo 1293965 2913011 := bstep (se 1 (by rfl) ⟨2184758, by rfl⟩ : syracuseStep 2913011 = 4369517) B4369517
theorem B2913047 : Blo 1293965 2913047 := bstep (se 1 (by rfl) ⟨2184785, by rfl⟩ : syracuseStep 2913047 = 4369571) B4369571
theorem B2184023 : Blo 1293965 2184023 := bstep (se 1 (by rfl) ⟨1638017, by rfl⟩ : syracuseStep 2184023 = 3276035) B3276035
theorem B2626391 : Blo 1293965 2626391 := bstep (se 1 (by rfl) ⟨1969793, by rfl⟩ : syracuseStep 2626391 = 3939587) B3939587
theorem B2913227 : Blo 1293965 2913227 := bstep (se 1 (by rfl) ⟨2184920, by rfl⟩ : syracuseStep 2913227 = 4369841) B4369841
theorem B2184151 : Blo 1293965 2184151 := bstep (se 1 (by rfl) ⟨1638113, by rfl⟩ : syracuseStep 2184151 = 3276227) B3276227
theorem B2913281 : Blo 1293965 2913281 := bstep (se 2 (by rfl) ⟨1092480, by rfl⟩ : syracuseStep 2913281 = 2184961) B2184961
theorem B9974789 : Blo 1293965 9974789 := bstep (se 4 (by rfl) ⟨935136, by rfl⟩ : syracuseStep 9974789 = 1870273) B1870273
theorem B4920371 : Blo 1293965 4920371 := bstep (se 1 (by rfl) ⟨3690278, by rfl⟩ : syracuseStep 4920371 = 7380557) B7380557
theorem B4920385 : Blo 1293965 4920385 := bstep (se 2 (by rfl) ⟨1845144, by rfl⟩ : syracuseStep 4920385 = 3690289) B3690289
theorem B2913497 : Blo 1293965 2913497 := bstep (se 2 (by rfl) ⟨1092561, by rfl⟩ : syracuseStep 2913497 = 2185123) B2185123
theorem B4371677 : Blo 1293965 4371677 := bstep (se 3 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 4371677 = 1639379) B1639379
theorem B2913587 : Blo 1293965 2913587 := bstep (se 1 (by rfl) ⟨2185190, by rfl⟩ : syracuseStep 2913587 = 4370381) B4370381
theorem B2766145 : Blo 1293965 2766145 := bstep (se 2 (by rfl) ⟨1037304, by rfl⟩ : syracuseStep 2766145 = 2074609) B2074609
theorem B2913623 : Blo 1293965 2913623 := bstep (se 1 (by rfl) ⟨2185217, by rfl⟩ : syracuseStep 2913623 = 4370435) B4370435
theorem B1496503 : Blo 1293965 1496503 := bstep (se 1 (by rfl) ⟨1122377, by rfl⟩ : syracuseStep 1496503 = 2244755) B2244755
theorem B2627009 : Blo 1293965 2627009 := bstep (se 2 (by rfl) ⟨985128, by rfl⟩ : syracuseStep 2627009 = 1970257) B1970257
theorem B2913803 : Blo 1293965 2913803 := bstep (se 1 (by rfl) ⟨2185352, by rfl⟩ : syracuseStep 2913803 = 4370705) B4370705
theorem B6223405 : Blo 1293965 6223405 := bstep (se 3 (by rfl) ⟨1166888, by rfl⟩ : syracuseStep 6223405 = 2333777) B2333777
theorem B2913857 : Blo 1293965 2913857 := bstep (se 2 (by rfl) ⟨1092696, by rfl⟩ : syracuseStep 2913857 = 2185393) B2185393
theorem B2184779 : Blo 1293965 2184779 := bstep (se 1 (by rfl) ⟨1638584, by rfl⟩ : syracuseStep 2184779 = 3277169) B3277169
theorem B2766487 : Blo 1293965 2766487 := bstep (se 1 (by rfl) ⟨2074865, by rfl⟩ : syracuseStep 2766487 = 4149731) B4149731
theorem B1455799 : Blo 1293965 1455799 := bstep (se 1 (by rfl) ⟨1091849, by rfl⟩ : syracuseStep 1455799 = 2183699) B2183699
theorem B2184907 : Blo 1293965 2184907 := bstep (se 1 (by rfl) ⟨1638680, by rfl⟩ : syracuseStep 2184907 = 3277361) B3277361
theorem B2660057 : Blo 1293965 2660057 := bstep (se 2 (by rfl) ⟨997521, by rfl⟩ : syracuseStep 2660057 = 1995043) B1995043
theorem B1382167 : Blo 1293965 1382167 := bstep (se 1 (by rfl) ⟨1036625, by rfl⟩ : syracuseStep 1382167 = 2073251) B2073251
theorem B4151063 : Blo 1293965 4151063 := bstep (se 1 (by rfl) ⟨3113297, by rfl⟩ : syracuseStep 4151063 = 6226595) B6226595
theorem B2914073 : Blo 1293965 2914073 := bstep (se 2 (by rfl) ⟨1092777, by rfl⟩ : syracuseStep 2914073 = 2185555) B2185555
theorem B3323699 : Blo 1293965 3323699 := bstep (se 1 (by rfl) ⟨2492774, by rfl⟩ : syracuseStep 3323699 = 4985549) B4985549
theorem B2185049 : Blo 1293965 2185049 := bstep (se 2 (by rfl) ⟨819393, by rfl⟩ : syracuseStep 2185049 = 1638787) B1638787
theorem B1455979 : Blo 1293965 1455979 := bstep (se 1 (by rfl) ⟨1091984, by rfl⟩ : syracuseStep 1455979 = 2183969) B2183969
theorem B2914163 : Blo 1293965 2914163 := bstep (se 1 (by rfl) ⟨2185622, by rfl⟩ : syracuseStep 2914163 = 4371245) B4371245
theorem B2332567 : Blo 1293965 2332567 := bstep (se 1 (by rfl) ⟨1749425, by rfl⟩ : syracuseStep 2332567 = 3498851) B3498851
theorem B2914199 : Blo 1293965 2914199 := bstep (se 1 (by rfl) ⟨2185649, by rfl⟩ : syracuseStep 2914199 = 4371299) B4371299
theorem B1456087 : Blo 1293965 1456087 := bstep (se 1 (by rfl) ⟨1092065, by rfl⟩ : syracuseStep 1456087 = 2184131) B2184131
theorem B2185177 : Blo 1293965 2185177 := bstep (se 2 (by rfl) ⟨819441, by rfl⟩ : syracuseStep 2185177 = 1638883) B1638883
theorem B2914379 : Blo 1293965 2914379 := bstep (se 1 (by rfl) ⟨2185784, by rfl⟩ : syracuseStep 2914379 = 4371569) B4371569
theorem B4151371 : Blo 1293965 4151371 := bstep (se 1 (by rfl) ⟨3113528, by rfl⟩ : syracuseStep 4151371 = 6227057) B6227057
theorem B2914433 : Blo 1293965 2914433 := bstep (se 2 (by rfl) ⟨1092912, by rfl⟩ : syracuseStep 2914433 = 2185825) B2185825
theorem B1456267 : Blo 1293965 1456267 := bstep (se 1 (by rfl) ⟨1092200, by rfl⟩ : syracuseStep 1456267 = 2184401) B2184401
theorem B4987025 : Blo 1293965 4987025 := bstep (se 2 (by rfl) ⟨1870134, by rfl⟩ : syracuseStep 4987025 = 3740269) B3740269
theorem B2955457 : Blo 1293965 2955457 := bstep (se 2 (by rfl) ⟨1108296, by rfl⟩ : syracuseStep 2955457 = 2216593) B2216593
theorem B2767051 : Blo 1293965 2767051 := bstep (se 1 (by rfl) ⟨2075288, by rfl⟩ : syracuseStep 2767051 = 4150577) B4150577
theorem B4913369 : Blo 1293965 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B1456375 : Blo 1293965 1456375 := bstep (se 1 (by rfl) ⟨1092281, by rfl⟩ : syracuseStep 1456375 = 2184563) B2184563
theorem B85104917 : Blo 1293965 85104917 := bstep (se 6 (by rfl) ⟨1994646, by rfl⟩ : syracuseStep 85104917 = 3989293) B3989293
theorem B9337123 : Blo 1293965 9337123 := bstep (se 1 (by rfl) ⟨7002842, by rfl⟩ : syracuseStep 9337123 = 14005685) B14005685
theorem B4372811 : Blo 1293965 4372811 := bstep (se 1 (by rfl) ⟨3279608, by rfl⟩ : syracuseStep 4372811 = 6559217) B6559217
theorem B2914649 : Blo 1293965 2914649 := bstep (se 2 (by rfl) ⟨1092993, by rfl⟩ : syracuseStep 2914649 = 2185987) B2185987
theorem B7371101 : Blo 1293965 7371101 := bstep (se 3 (by rfl) ⟨1382081, by rfl⟩ : syracuseStep 7371101 = 2764163) B2764163
theorem B8976791 : Blo 1293965 8976791 := bstep (se 1 (by rfl) ⟨6732593, by rfl⟩ : syracuseStep 8976791 = 13465187) B13465187
theorem B1456555 : Blo 1293965 1456555 := bstep (se 1 (by rfl) ⟨1092416, by rfl⟩ : syracuseStep 1456555 = 2184833) B2184833
theorem B4913581 : Blo 1293965 4913581 := bstep (se 3 (by rfl) ⟨921296, by rfl⟩ : syracuseStep 4913581 = 1842593) B1842593
theorem B2914739 : Blo 1293965 2914739 := bstep (se 1 (by rfl) ⟨2186054, by rfl⟩ : syracuseStep 2914739 = 4372109) B4372109
theorem B3684811 : Blo 1293965 3684811 := bstep (se 1 (by rfl) ⟨2763608, by rfl⟩ : syracuseStep 3684811 = 5527217) B5527217
theorem B2914775 : Blo 1293965 2914775 := bstep (se 1 (by rfl) ⟨2186081, by rfl⟩ : syracuseStep 2914775 = 4372163) B4372163
theorem B1456663 : Blo 1293965 1456663 := bstep (se 1 (by rfl) ⟨1092497, by rfl⟩ : syracuseStep 1456663 = 2184995) B2184995
theorem B2185751 : Blo 1293965 2185751 := bstep (se 1 (by rfl) ⟨1639313, by rfl⟩ : syracuseStep 2185751 = 3278627) B3278627
theorem B7379531 : Blo 1293965 7379531 := bstep (se 1 (by rfl) ⟨5534648, by rfl⟩ : syracuseStep 7379531 = 11069297) B11069297
theorem B3938905 : Blo 1293965 3938905 := bstep (se 2 (by rfl) ⟨1477089, by rfl⟩ : syracuseStep 3938905 = 2954179) B2954179
theorem B4373081 : Blo 1293965 4373081 := bstep (se 2 (by rfl) ⟨1639905, by rfl⟩ : syracuseStep 4373081 = 3279811) B3279811
theorem B20994653 : Blo 1293965 20994653 := bstep (se 3 (by rfl) ⟨3936497, by rfl⟩ : syracuseStep 20994653 = 7872995) B7872995
theorem B2914955 : Blo 1293965 2914955 := bstep (se 1 (by rfl) ⟨2186216, by rfl⟩ : syracuseStep 2914955 = 4372433) B4372433
theorem B2185879 : Blo 1293965 2185879 := bstep (se 1 (by rfl) ⟨1639409, by rfl⟩ : syracuseStep 2185879 = 3278819) B3278819
theorem B5905075 : Blo 1293965 5905075 := bstep (se 1 (by rfl) ⟨4428806, by rfl⟩ : syracuseStep 5905075 = 8857613) B8857613
theorem B2915009 : Blo 1293965 2915009 := bstep (se 2 (by rfl) ⟨1093128, by rfl⟩ : syracuseStep 2915009 = 2186257) B2186257
theorem B1456843 : Blo 1293965 1456843 := bstep (se 1 (by rfl) ⟨1092632, by rfl⟩ : syracuseStep 1456843 = 2185265) B2185265
theorem B7092953 : Blo 1293965 7092953 := bstep (se 2 (by rfl) ⟨2659857, by rfl⟩ : syracuseStep 7092953 = 5319715) B5319715
theorem B3685085 : Blo 1293965 3685085 := bstep (se 3 (by rfl) ⟨690953, by rfl⟩ : syracuseStep 3685085 = 1381907) B1381907
theorem B4913885 : Blo 1293965 4913885 := bstep (se 3 (by rfl) ⟨921353, by rfl⟩ : syracuseStep 4913885 = 1842707) B1842707
theorem B1456951 : Blo 1293965 1456951 := bstep (se 1 (by rfl) ⟨1092713, by rfl⟩ : syracuseStep 1456951 = 2185427) B2185427
theorem B6552413 : Blo 1293965 6552413 := bstep (se 3 (by rfl) ⟨1228577, by rfl⟩ : syracuseStep 6552413 = 2457155) B2457155
theorem B2915225 : Blo 1293965 2915225 := bstep (se 2 (by rfl) ⟨1093209, by rfl⟩ : syracuseStep 2915225 = 2186419) B2186419
theorem B1457131 : Blo 1293965 1457131 := bstep (se 1 (by rfl) ⟨1092848, by rfl⟩ : syracuseStep 1457131 = 2185697) B2185697
theorem B2456563 : Blo 1293965 2456563 := bstep (se 1 (by rfl) ⟨1842422, by rfl⟩ : syracuseStep 2456563 = 3684845) B3684845
theorem B2915315 : Blo 1293965 2915315 := bstep (se 1 (by rfl) ⟨2186486, by rfl⟩ : syracuseStep 2915315 = 4372973) B4372973
theorem B2915351 : Blo 1293965 2915351 := bstep (se 1 (by rfl) ⟨2186513, by rfl⟩ : syracuseStep 2915351 = 4373027) B4373027
theorem B5610541 : Blo 1293965 5610541 := bstep (se 3 (by rfl) ⟨1051976, by rfl⟩ : syracuseStep 5610541 = 2103953) B2103953
theorem B1457239 : Blo 1293965 1457239 := bstep (se 1 (by rfl) ⟨1092929, by rfl⟩ : syracuseStep 1457239 = 2185859) B2185859
theorem B2915531 : Blo 1293965 2915531 := bstep (se 1 (by rfl) ⟨2186648, by rfl⟩ : syracuseStep 2915531 = 4373297) B4373297
theorem B2915585 : Blo 1293965 2915585 := bstep (se 2 (by rfl) ⟨1093344, by rfl⟩ : syracuseStep 2915585 = 2186689) B2186689
theorem B1457419 : Blo 1293965 1457419 := bstep (se 1 (by rfl) ⟨1093064, by rfl⟩ : syracuseStep 1457419 = 2186129) B2186129
theorem B2186507 : Blo 1293965 2186507 := bstep (se 1 (by rfl) ⟨1639880, by rfl⟩ : syracuseStep 2186507 = 3279761) B3279761
theorem B4373783 : Blo 1293965 4373783 := bstep (se 1 (by rfl) ⟨3280337, by rfl⟩ : syracuseStep 4373783 = 6560675) B6560675
theorem B1457527 : Blo 1293965 1457527 := bstep (se 1 (by rfl) ⟨1093145, by rfl⟩ : syracuseStep 1457527 = 2186291) B2186291
theorem B1383799 : Blo 1293965 1383799 := bstep (se 1 (by rfl) ⟨1037849, by rfl⟩ : syracuseStep 1383799 = 2075699) B2075699
theorem B2186635 : Blo 1293965 2186635 := bstep (se 1 (by rfl) ⟨1639976, by rfl⟩ : syracuseStep 2186635 = 3279953) B3279953
theorem B1940951 : Blo 1293965 1940951 := bstep (se 1 (by rfl) ⟨1455713, by rfl⟩ : syracuseStep 1940951 = 2911427) B2911427
theorem B2457049 : Blo 1293965 2457049 := bstep (se 2 (by rfl) ⟨921393, by rfl⟩ : syracuseStep 2457049 = 1842787) B1842787
theorem B2915801 : Blo 1293965 2915801 := bstep (se 2 (by rfl) ⟨1093425, by rfl⟩ : syracuseStep 2915801 = 2186851) B2186851
theorem B9838097 : Blo 1293965 9838097 := bstep (se 2 (by rfl) ⟨3689286, by rfl⟩ : syracuseStep 9838097 = 7378573) B7378573
theorem B1637911 : Blo 1293965 1637911 := bstep (se 1 (by rfl) ⟨1228433, by rfl⟩ : syracuseStep 1637911 = 2456867) B2456867
theorem B1941017 : Blo 1293965 1941017 := bstep (se 2 (by rfl) ⟨727881, by rfl⟩ : syracuseStep 1941017 = 1455763) B1455763
theorem B2186777 : Blo 1293965 2186777 := bstep (se 2 (by rfl) ⟨820041, by rfl⟩ : syracuseStep 2186777 = 1640083) B1640083
theorem B9960995 : Blo 1293965 9960995 := bstep (se 1 (by rfl) ⟨7470746, by rfl⟩ : syracuseStep 9960995 = 14941493) B14941493
theorem B1457707 : Blo 1293965 1457707 := bstep (se 1 (by rfl) ⟨1093280, by rfl⟩ : syracuseStep 1457707 = 2186561) B2186561
theorem B2915891 : Blo 1293965 2915891 := bstep (se 1 (by rfl) ⟨2186918, by rfl⟩ : syracuseStep 2915891 = 4373837) B4373837
theorem B5529181 : Blo 1293965 5529181 := bstep (se 3 (by rfl) ⟨1036721, by rfl⟩ : syracuseStep 5529181 = 2073443) B2073443
theorem B11812483 : Blo 1293965 11812483 := bstep (se 1 (by rfl) ⟨8859362, by rfl⟩ : syracuseStep 11812483 = 17718725) B17718725
theorem B5250691 : Blo 1293965 5250691 := bstep (se 1 (by rfl) ⟨3938018, by rfl⟩ : syracuseStep 5250691 = 7876037) B7876037
theorem B1941131 : Blo 1293965 1941131 := bstep (se 1 (by rfl) ⟨1455848, by rfl⟩ : syracuseStep 1941131 = 2911697) B2911697
theorem B1293975 : Blo 1293965 1293975 := bstep (se 1 (by rfl) ⟨970481, by rfl⟩ : syracuseStep 1293975 = 1940963) B1940963
theorem B1941143 : Blo 1293965 1941143 := bstep (se 1 (by rfl) ⟨1455857, by rfl⟩ : syracuseStep 1941143 = 2911715) B2911715
theorem B11058839 : Blo 1293965 11058839 := bstep (se 1 (by rfl) ⟨8294129, by rfl⟩ : syracuseStep 11058839 = 16588259) B16588259
theorem B1457815 : Blo 1293965 1457815 := bstep (se 1 (by rfl) ⟨1093361, by rfl⟩ : syracuseStep 1457815 = 2186723) B2186723
theorem B2186905 : Blo 1293965 2186905 := bstep (se 2 (by rfl) ⟨820089, by rfl⟩ : syracuseStep 2186905 = 1640179) B1640179
theorem B1293995 : Blo 1293965 1293995 := bstep (se 1 (by rfl) ⟨970496, by rfl⟩ : syracuseStep 1293995 = 1940993) B1940993
theorem B1294007 : Blo 1293965 1294007 := bstep (se 1 (by rfl) ⟨970505, by rfl⟩ : syracuseStep 1294007 = 1941011) B1941011
theorem B1294027 : Blo 1293965 1294027 := bstep (se 1 (by rfl) ⟨970520, by rfl⟩ : syracuseStep 1294027 = 1941041) B1941041
theorem B1294039 : Blo 1293965 1294039 := bstep (se 1 (by rfl) ⟨970529, by rfl⟩ : syracuseStep 1294039 = 1941059) B1941059
theorem B1941209 : Blo 1293965 1941209 := bstep (se 2 (by rfl) ⟨727953, by rfl⟩ : syracuseStep 1941209 = 1455907) B1455907
theorem B1294059 : Blo 1293965 1294059 := bstep (se 1 (by rfl) ⟨970544, by rfl⟩ : syracuseStep 1294059 = 1941089) B1941089
theorem B1294071 : Blo 1293965 1294071 := bstep (se 1 (by rfl) ⟨970553, by rfl⟩ : syracuseStep 1294071 = 1941107) B1941107
theorem B1294091 : Blo 1293965 1294091 := bstep (se 1 (by rfl) ⟨970568, by rfl⟩ : syracuseStep 1294091 = 1941137) B1941137
theorem B1294103 : Blo 1293965 1294103 := bstep (se 1 (by rfl) ⟨970577, by rfl⟩ : syracuseStep 1294103 = 1941155) B1941155
theorem B1294123 : Blo 1293965 1294123 := bstep (se 1 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 1294123 = 1941185) B1941185
theorem B1294135 : Blo 1293965 1294135 := bstep (se 1 (by rfl) ⟨970601, by rfl⟩ : syracuseStep 1294135 = 1941203) B1941203
theorem B1294155 : Blo 1293965 1294155 := bstep (se 1 (by rfl) ⟨970616, by rfl⟩ : syracuseStep 1294155 = 1941233) B1941233
theorem B1941323 : Blo 1293965 1941323 := bstep (se 1 (by rfl) ⟨1455992, by rfl⟩ : syracuseStep 1941323 = 2911985) B2911985
theorem B1294167 : Blo 1293965 1294167 := bstep (se 1 (by rfl) ⟨970625, by rfl⟩ : syracuseStep 1294167 = 1941251) B1941251
theorem B1941335 : Blo 1293965 1941335 := bstep (se 1 (by rfl) ⟨1456001, by rfl⟩ : syracuseStep 1941335 = 2912003) B2912003
theorem B1294187 : Blo 1293965 1294187 := bstep (se 1 (by rfl) ⟨970640, by rfl⟩ : syracuseStep 1294187 = 1941281) B1941281
theorem B1294199 : Blo 1293965 1294199 := bstep (se 1 (by rfl) ⟨970649, by rfl⟩ : syracuseStep 1294199 = 1941299) B1941299
theorem B1294219 : Blo 1293965 1294219 := bstep (se 1 (by rfl) ⟨970664, by rfl⟩ : syracuseStep 1294219 = 1941329) B1941329
theorem B1294231 : Blo 1293965 1294231 := bstep (se 1 (by rfl) ⟨970673, by rfl⟩ : syracuseStep 1294231 = 1941347) B1941347
theorem B1941401 : Blo 1293965 1941401 := bstep (se 2 (by rfl) ⟨728025, by rfl⟩ : syracuseStep 1941401 = 1456051) B1456051
theorem B1294251 : Blo 1293965 1294251 := bstep (se 1 (by rfl) ⟨970688, by rfl⟩ : syracuseStep 1294251 = 1941377) B1941377
theorem B9830321 : Blo 1293965 9830321 := bstep (se 2 (by rfl) ⟨3686370, by rfl⟩ : syracuseStep 9830321 = 7372741) B7372741
theorem B11067313 : Blo 1293965 11067313 := bstep (se 2 (by rfl) ⟨4150242, by rfl⟩ : syracuseStep 11067313 = 8300485) B8300485
theorem B28016563 : Blo 1293965 28016563 := bstep (se 1 (by rfl) ⟨21012422, by rfl⟩ : syracuseStep 28016563 = 42024845) B42024845
theorem B1294263 : Blo 1293965 1294263 := bstep (se 1 (by rfl) ⟨970697, by rfl⟩ : syracuseStep 1294263 = 1941395) B1941395
theorem B1294283 : Blo 1293965 1294283 := bstep (se 1 (by rfl) ⟨970712, by rfl⟩ : syracuseStep 1294283 = 1941425) B1941425
theorem B1294295 : Blo 1293965 1294295 := bstep (se 1 (by rfl) ⟨970721, by rfl⟩ : syracuseStep 1294295 = 1941443) B1941443
theorem B1294315 : Blo 1293965 1294315 := bstep (se 1 (by rfl) ⟨970736, by rfl⟩ : syracuseStep 1294315 = 1941473) B1941473
theorem B1294327 : Blo 1293965 1294327 := bstep (se 1 (by rfl) ⟨970745, by rfl⟩ : syracuseStep 1294327 = 1941491) B1941491
theorem B1294343 : Blo 1293965 1294343 := bstep (se 1 (by rfl) ⟨970757, by rfl⟩ : syracuseStep 1294343 = 1941515) B1941515
theorem B1638407 : Blo 1293965 1638407 := bstep (se 1 (by rfl) ⟨1228805, by rfl⟩ : syracuseStep 1638407 = 2457611) B2457611
theorem B1294351 : Blo 1293965 1294351 := bstep (se 1 (by rfl) ⟨970763, by rfl⟩ : syracuseStep 1294351 = 1941527) B1941527
theorem B1941563 : Blo 1293965 1941563 := bstep (se 1 (by rfl) ⟨1456172, by rfl⟩ : syracuseStep 1941563 = 2912345) B2912345
theorem B1294395 : Blo 1293965 1294395 := bstep (se 1 (by rfl) ⟨970796, by rfl⟩ : syracuseStep 1294395 = 1941593) B1941593
theorem B5988419 : Blo 1293965 5988419 := bstep (se 1 (by rfl) ⟨4491314, by rfl⟩ : syracuseStep 5988419 = 8982629) B8982629
theorem B7004227 : Blo 1293965 7004227 := bstep (se 1 (by rfl) ⟨5253170, by rfl⟩ : syracuseStep 7004227 = 10506341) B10506341
theorem B1941623 : Blo 1293965 1941623 := bstep (se 1 (by rfl) ⟨1456217, by rfl⟩ : syracuseStep 1941623 = 2912435) B2912435
theorem B1294471 : Blo 1293965 1294471 := bstep (se 1 (by rfl) ⟨970853, by rfl⟩ : syracuseStep 1294471 = 1941707) B1941707
theorem B1941647 : Blo 1293965 1941647 := bstep (se 1 (by rfl) ⟨1456235, by rfl⟩ : syracuseStep 1941647 = 2912471) B2912471
theorem B1294479 : Blo 1293965 1294479 := bstep (se 1 (by rfl) ⟨970859, by rfl⟩ : syracuseStep 1294479 = 1941719) B1941719
theorem B3498137 : Blo 1293965 3498137 := bstep (se 2 (by rfl) ⟨1311801, by rfl⟩ : syracuseStep 3498137 = 2623603) B2623603
theorem B1941689 : Blo 1293965 1941689 := bstep (se 2 (by rfl) ⟨728133, by rfl⟩ : syracuseStep 1941689 = 1456267) B1456267
theorem B1294523 : Blo 1293965 1294523 := bstep (se 1 (by rfl) ⟨970892, by rfl⟩ : syracuseStep 1294523 = 1941785) B1941785
theorem B3277057 : Blo 1293965 3277057 := bstep (se 2 (by rfl) ⟨1228896, by rfl⟩ : syracuseStep 3277057 = 2457793) B2457793
theorem B1941767 : Blo 1293965 1941767 := bstep (se 1 (by rfl) ⟨1456325, by rfl⟩ : syracuseStep 1941767 = 2912651) B2912651
theorem B1294599 : Blo 1293965 1294599 := bstep (se 1 (by rfl) ⟨970949, by rfl⟩ : syracuseStep 1294599 = 1941899) B1941899
theorem B6553871 : Blo 1293965 6553871 := bstep (se 1 (by rfl) ⟨4915403, by rfl⟩ : syracuseStep 6553871 = 9830807) B9830807
theorem B1294607 : Blo 1293965 1294607 := bstep (se 1 (by rfl) ⟨970955, by rfl⟩ : syracuseStep 1294607 = 1941911) B1941911
theorem B1941803 : Blo 1293965 1941803 := bstep (se 1 (by rfl) ⟨1456352, by rfl⟩ : syracuseStep 1941803 = 2912705) B2912705
theorem B1843499 : Blo 1293965 1843499 := bstep (se 1 (by rfl) ⟨1382624, by rfl⟩ : syracuseStep 1843499 = 2765249) B2765249
theorem B1294651 : Blo 1293965 1294651 := bstep (se 1 (by rfl) ⟨970988, by rfl⟩ : syracuseStep 1294651 = 1941977) B1941977
theorem B1941833 : Blo 1293965 1941833 := bstep (se 2 (by rfl) ⟨728187, by rfl⟩ : syracuseStep 1941833 = 1456375) B1456375
theorem B1294727 : Blo 1293965 1294727 := bstep (se 1 (by rfl) ⟨971045, by rfl⟩ : syracuseStep 1294727 = 1942091) B1942091
theorem B12452231 : Blo 1293965 12452231 := bstep (se 1 (by rfl) ⟨9339173, by rfl⟩ : syracuseStep 12452231 = 18678347) B18678347
theorem B1294735 : Blo 1293965 1294735 := bstep (se 1 (by rfl) ⟨971051, by rfl⟩ : syracuseStep 1294735 = 1942103) B1942103
theorem B6218137 : Blo 1293965 6218137 := bstep (se 2 (by rfl) ⟨2331801, by rfl⟩ : syracuseStep 6218137 = 4663603) B4663603
theorem B1941947 : Blo 1293965 1941947 := bstep (se 1 (by rfl) ⟨1456460, by rfl⟩ : syracuseStep 1941947 = 2912921) B2912921
theorem B1294779 : Blo 1293965 1294779 := bstep (se 1 (by rfl) ⟨971084, by rfl⟩ : syracuseStep 1294779 = 1942169) B1942169
theorem B9839069 : Blo 1293965 9839069 := bstep (se 3 (by rfl) ⟨1844825, by rfl⟩ : syracuseStep 9839069 = 3689651) B3689651
theorem B1942007 : Blo 1293965 1942007 := bstep (se 1 (by rfl) ⟨1456505, by rfl⟩ : syracuseStep 1942007 = 2913011) B2913011
theorem B1294855 : Blo 1293965 1294855 := bstep (se 1 (by rfl) ⟨971141, by rfl⟩ : syracuseStep 1294855 = 1942283) B1942283
theorem B1942031 : Blo 1293965 1942031 := bstep (se 1 (by rfl) ⟨1456523, by rfl⟩ : syracuseStep 1942031 = 2913047) B2913047
theorem B2458127 : Blo 1293965 2458127 := bstep (se 1 (by rfl) ⟨1843595, by rfl⟩ : syracuseStep 2458127 = 3687191) B3687191
theorem B1294863 : Blo 1293965 1294863 := bstep (se 1 (by rfl) ⟨971147, by rfl⟩ : syracuseStep 1294863 = 1942295) B1942295
theorem B1942073 : Blo 1293965 1942073 := bstep (se 2 (by rfl) ⟨728277, by rfl⟩ : syracuseStep 1942073 = 1456555) B1456555
theorem B1294907 : Blo 1293965 1294907 := bstep (se 1 (by rfl) ⟨971180, by rfl⟩ : syracuseStep 1294907 = 1942361) B1942361
theorem B4915799 : Blo 1293965 4915799 := bstep (se 1 (by rfl) ⟨3686849, by rfl⟩ : syracuseStep 4915799 = 7373699) B7373699
theorem B1942151 : Blo 1293965 1942151 := bstep (se 1 (by rfl) ⟨1456613, by rfl⟩ : syracuseStep 1942151 = 2913227) B2913227
theorem B1294983 : Blo 1293965 1294983 := bstep (se 1 (by rfl) ⟨971237, by rfl⟩ : syracuseStep 1294983 = 1942475) B1942475
theorem B1294991 : Blo 1293965 1294991 := bstep (se 1 (by rfl) ⟨971243, by rfl⟩ : syracuseStep 1294991 = 1942487) B1942487
theorem B1639055 : Blo 1293965 1639055 := bstep (se 1 (by rfl) ⟨1229291, by rfl⟩ : syracuseStep 1639055 = 2458583) B2458583
theorem B1942187 : Blo 1293965 1942187 := bstep (se 1 (by rfl) ⟨1456640, by rfl⟩ : syracuseStep 1942187 = 2913281) B2913281
theorem B1295035 : Blo 1293965 1295035 := bstep (se 1 (by rfl) ⟨971276, by rfl⟩ : syracuseStep 1295035 = 1942553) B1942553
theorem B1942217 : Blo 1293965 1942217 := bstep (se 2 (by rfl) ⟨728331, by rfl⟩ : syracuseStep 1942217 = 1456663) B1456663
theorem B1295111 : Blo 1293965 1295111 := bstep (se 1 (by rfl) ⟨971333, by rfl⟩ : syracuseStep 1295111 = 1942667) B1942667
theorem B1295119 : Blo 1293965 1295119 := bstep (se 1 (by rfl) ⟨971339, by rfl⟩ : syracuseStep 1295119 = 1942679) B1942679
theorem B3498785 : Blo 1293965 3498785 := bstep (se 2 (by rfl) ⟨1312044, by rfl⟩ : syracuseStep 3498785 = 2624089) B2624089
theorem B5251873 : Blo 1293965 5251873 := bstep (se 2 (by rfl) ⟨1969452, by rfl⟩ : syracuseStep 5251873 = 3938905) B3938905
theorem B1942331 : Blo 1293965 1942331 := bstep (se 1 (by rfl) ⟨1456748, by rfl⟩ : syracuseStep 1942331 = 2913497) B2913497
theorem B1295163 : Blo 1293965 1295163 := bstep (se 1 (by rfl) ⟨971372, by rfl⟩ : syracuseStep 1295163 = 1942745) B1942745
theorem B3277655 : Blo 1293965 3277655 := bstep (se 1 (by rfl) ⟨2458241, by rfl⟩ : syracuseStep 3277655 = 4916483) B4916483
theorem B1942391 : Blo 1293965 1942391 := bstep (se 1 (by rfl) ⟨1456793, by rfl⟩ : syracuseStep 1942391 = 2913587) B2913587
theorem B1295239 : Blo 1293965 1295239 := bstep (se 1 (by rfl) ⟨971429, by rfl⟩ : syracuseStep 1295239 = 1942859) B1942859
theorem B1942415 : Blo 1293965 1942415 := bstep (se 1 (by rfl) ⟨1456811, by rfl⟩ : syracuseStep 1942415 = 2913623) B2913623
theorem B1295247 : Blo 1293965 1295247 := bstep (se 1 (by rfl) ⟨971435, by rfl⟩ : syracuseStep 1295247 = 1942871) B1942871
theorem B7873433 : Blo 1293965 7873433 := bstep (se 2 (by rfl) ⟨2952537, by rfl⟩ : syracuseStep 7873433 = 5905075) B5905075
theorem B1942457 : Blo 1293965 1942457 := bstep (se 2 (by rfl) ⟨728421, by rfl⟩ : syracuseStep 1942457 = 1456843) B1456843
theorem B1295291 : Blo 1293965 1295291 := bstep (se 1 (by rfl) ⟨971468, by rfl⟩ : syracuseStep 1295291 = 1942937) B1942937
theorem B15762437 : Blo 1293965 15762437 := bstep (se 4 (by rfl) ⟨1477728, by rfl⟩ : syracuseStep 15762437 = 2955457) B2955457
theorem B1942535 : Blo 1293965 1942535 := bstep (se 1 (by rfl) ⟨1456901, by rfl⟩ : syracuseStep 1942535 = 2913803) B2913803
theorem B1295367 : Blo 1293965 1295367 := bstep (se 1 (by rfl) ⟨971525, by rfl⟩ : syracuseStep 1295367 = 1943051) B1943051
theorem B1295375 : Blo 1293965 1295375 := bstep (se 1 (by rfl) ⟨971531, by rfl⟩ : syracuseStep 1295375 = 1943063) B1943063
theorem B6308887 : Blo 1293965 6308887 := bstep (se 1 (by rfl) ⟨4731665, by rfl⟩ : syracuseStep 6308887 = 9463331) B9463331
theorem B3277867 : Blo 1293965 3277867 := bstep (se 1 (by rfl) ⟨2458400, by rfl⟩ : syracuseStep 3277867 = 4916801) B4916801
theorem B1942571 : Blo 1293965 1942571 := bstep (se 1 (by rfl) ⟨1456928, by rfl⟩ : syracuseStep 1942571 = 2913857) B2913857
theorem B2458667 : Blo 1293965 2458667 := bstep (se 1 (by rfl) ⟨1844000, by rfl⟩ : syracuseStep 2458667 = 3688001) B3688001
theorem B1295419 : Blo 1293965 1295419 := bstep (se 1 (by rfl) ⟨971564, by rfl⟩ : syracuseStep 1295419 = 1943129) B1943129
theorem B23938109 : Blo 1293965 23938109 := bstep (se 3 (by rfl) ⟨4488395, by rfl⟩ : syracuseStep 23938109 = 8976791) B8976791
theorem B4916285 : Blo 1293965 4916285 := bstep (se 3 (by rfl) ⟨921803, by rfl⟩ : syracuseStep 4916285 = 1843607) B1843607
theorem B1942601 : Blo 1293965 1942601 := bstep (se 2 (by rfl) ⟨728475, by rfl⟩ : syracuseStep 1942601 = 1456951) B1456951
theorem B1295495 : Blo 1293965 1295495 := bstep (se 1 (by rfl) ⟨971621, by rfl⟩ : syracuseStep 1295495 = 1943243) B1943243
theorem B1295503 : Blo 1293965 1295503 := bstep (se 1 (by rfl) ⟨971627, by rfl⟩ : syracuseStep 1295503 = 1943255) B1943255
theorem B3278009 : Blo 1293965 3278009 := bstep (se 2 (by rfl) ⟨1229253, by rfl⟩ : syracuseStep 3278009 = 2458507) B2458507
theorem B1942715 : Blo 1293965 1942715 := bstep (se 1 (by rfl) ⟨1457036, by rfl⟩ : syracuseStep 1942715 = 2914073) B2914073
theorem B1295547 : Blo 1293965 1295547 := bstep (se 1 (by rfl) ⟨971660, by rfl⟩ : syracuseStep 1295547 = 1943321) B1943321
theorem B7374017 : Blo 1293965 7374017 := bstep (se 2 (by rfl) ⟨2765256, by rfl⟩ : syracuseStep 7374017 = 5530513) B5530513
theorem B1942775 : Blo 1293965 1942775 := bstep (se 1 (by rfl) ⟨1457081, by rfl⟩ : syracuseStep 1942775 = 2914163) B2914163
theorem B1295623 : Blo 1293965 1295623 := bstep (se 1 (by rfl) ⟨971717, by rfl⟩ : syracuseStep 1295623 = 1943435) B1943435
theorem B1942799 : Blo 1293965 1942799 := bstep (se 1 (by rfl) ⟨1457099, by rfl⟩ : syracuseStep 1942799 = 2914199) B2914199
theorem B1295631 : Blo 1293965 1295631 := bstep (se 1 (by rfl) ⟨971723, by rfl⟩ : syracuseStep 1295631 = 1943447) B1943447
theorem B1942841 : Blo 1293965 1942841 := bstep (se 2 (by rfl) ⟨728565, by rfl⟩ : syracuseStep 1942841 = 1457131) B1457131
theorem B1295675 : Blo 1293965 1295675 := bstep (se 1 (by rfl) ⟨971756, by rfl⟩ : syracuseStep 1295675 = 1943513) B1943513
theorem B1942919 : Blo 1293965 1942919 := bstep (se 1 (by rfl) ⟨1457189, by rfl⟩ : syracuseStep 1942919 = 2914379) B2914379
theorem B1295751 : Blo 1293965 1295751 := bstep (se 1 (by rfl) ⟨971813, by rfl⟩ : syracuseStep 1295751 = 1943627) B1943627
theorem B1295759 : Blo 1293965 1295759 := bstep (se 1 (by rfl) ⟨971819, by rfl⟩ : syracuseStep 1295759 = 1943639) B1943639
theorem B7480721 : Blo 1293965 7480721 := bstep (se 2 (by rfl) ⟨2805270, by rfl⟩ : syracuseStep 7480721 = 5610541) B5610541
theorem B1942955 : Blo 1293965 1942955 := bstep (se 1 (by rfl) ⟨1457216, by rfl⟩ : syracuseStep 1942955 = 2914433) B2914433
theorem B1295803 : Blo 1293965 1295803 := bstep (se 1 (by rfl) ⟨971852, by rfl⟩ : syracuseStep 1295803 = 1943705) B1943705
theorem B1942985 : Blo 1293965 1942985 := bstep (se 2 (by rfl) ⟨728619, by rfl⟩ : syracuseStep 1942985 = 1457239) B1457239
theorem B1295879 : Blo 1293965 1295879 := bstep (se 1 (by rfl) ⟨971909, by rfl⟩ : syracuseStep 1295879 = 1943819) B1943819
theorem B1295887 : Blo 1293965 1295887 := bstep (se 1 (by rfl) ⟨971915, by rfl⟩ : syracuseStep 1295887 = 1943831) B1943831
theorem B1943099 : Blo 1293965 1943099 := bstep (se 1 (by rfl) ⟨1457324, by rfl⟩ : syracuseStep 1943099 = 2914649) B2914649
theorem B1295931 : Blo 1293965 1295931 := bstep (se 1 (by rfl) ⟨971948, by rfl⟩ : syracuseStep 1295931 = 1943897) B1943897
theorem B1943159 : Blo 1293965 1943159 := bstep (se 1 (by rfl) ⟨1457369, by rfl⟩ : syracuseStep 1943159 = 2914739) B2914739
theorem B1943183 : Blo 1293965 1943183 := bstep (se 1 (by rfl) ⟨1457387, by rfl⟩ : syracuseStep 1943183 = 2914775) B2914775
theorem B1943225 : Blo 1293965 1943225 := bstep (se 2 (by rfl) ⟨728709, by rfl⟩ : syracuseStep 1943225 = 1457419) B1457419
theorem B6555329 : Blo 1293965 6555329 := bstep (se 2 (by rfl) ⟨2458248, by rfl⟩ : syracuseStep 6555329 = 4916497) B4916497
theorem B6219521 : Blo 1293965 6219521 := bstep (se 2 (by rfl) ⟨2332320, by rfl⟩ : syracuseStep 6219521 = 4664641) B4664641
theorem B3688193 : Blo 1293965 3688193 := bstep (se 2 (by rfl) ⟨1383072, by rfl⟩ : syracuseStep 3688193 = 2766145) B2766145
theorem B1943303 : Blo 1293965 1943303 := bstep (se 1 (by rfl) ⟨1457477, by rfl⟩ : syracuseStep 1943303 = 2914955) B2914955
theorem B2524943 : Blo 1293965 2524943 := bstep (se 1 (by rfl) ⟨1893707, by rfl⟩ : syracuseStep 2524943 = 3787415) B3787415
theorem B1943339 : Blo 1293965 1943339 := bstep (se 1 (by rfl) ⟨1457504, by rfl⟩ : syracuseStep 1943339 = 2915009) B2915009
theorem B4728635 : Blo 1293965 4728635 := bstep (se 1 (by rfl) ⟨3546476, by rfl⟩ : syracuseStep 4728635 = 7092953) B7092953
theorem B1943369 : Blo 1293965 1943369 := bstep (se 2 (by rfl) ⟨728763, by rfl⟩ : syracuseStep 1943369 = 1457527) B1457527
theorem B1845065 : Blo 1293965 1845065 := bstep (se 2 (by rfl) ⟨691899, by rfl⟩ : syracuseStep 1845065 = 1383799) B1383799
theorem B4368275 : Blo 1293965 4368275 := bstep (se 1 (by rfl) ⟨3276206, by rfl⟩ : syracuseStep 4368275 = 6552413) B6552413
theorem B1943483 : Blo 1293965 1943483 := bstep (se 1 (by rfl) ⟨1457612, by rfl⟩ : syracuseStep 1943483 = 2915225) B2915225
theorem B1943543 : Blo 1293965 1943543 := bstep (se 1 (by rfl) ⟨1457657, by rfl⟩ : syracuseStep 1943543 = 2915315) B2915315
theorem B1943567 : Blo 1293965 1943567 := bstep (se 1 (by rfl) ⟨1457675, by rfl⟩ : syracuseStep 1943567 = 2915351) B2915351
theorem B1943609 : Blo 1293965 1943609 := bstep (se 2 (by rfl) ⟨728853, by rfl⟩ : syracuseStep 1943609 = 1457707) B1457707
theorem B2459783 : Blo 1293965 2459783 := bstep (se 1 (by rfl) ⟨1844837, by rfl⟩ : syracuseStep 2459783 = 3689675) B3689675
theorem B1943687 : Blo 1293965 1943687 := bstep (se 1 (by rfl) ⟨1457765, by rfl⟩ : syracuseStep 1943687 = 2915531) B2915531
theorem B3279001 : Blo 1293965 3279001 := bstep (se 2 (by rfl) ⟨1229625, by rfl⟩ : syracuseStep 3279001 = 2459251) B2459251
theorem B1943723 : Blo 1293965 1943723 := bstep (se 1 (by rfl) ⟨1457792, by rfl⟩ : syracuseStep 1943723 = 2915585) B2915585
theorem B3688649 : Blo 1293965 3688649 := bstep (se 2 (by rfl) ⟨1383243, by rfl⟩ : syracuseStep 3688649 = 2766487) B2766487
theorem B1943753 : Blo 1293965 1943753 := bstep (se 2 (by rfl) ⟨728907, by rfl⟩ : syracuseStep 1943753 = 1457815) B1457815
theorem B3279163 : Blo 1293965 3279163 := bstep (se 1 (by rfl) ⟨2459372, by rfl⟩ : syracuseStep 3279163 = 4918745) B4918745
theorem B1943867 : Blo 1293965 1943867 := bstep (se 1 (by rfl) ⟨1457900, by rfl⟩ : syracuseStep 1943867 = 2915801) B2915801
theorem B1943927 : Blo 1293965 1943927 := bstep (se 1 (by rfl) ⟨1457945, by rfl⟩ : syracuseStep 1943927 = 2915891) B2915891
theorem B3279305 : Blo 1293965 3279305 := bstep (se 2 (by rfl) ⟨1229739, by rfl⟩ : syracuseStep 3279305 = 2459479) B2459479
theorem B3738145 : Blo 1293965 3738145 := bstep (se 2 (by rfl) ⟨1401804, by rfl⟩ : syracuseStep 3738145 = 2803609) B2803609
theorem B3689003 : Blo 1293965 3689003 := bstep (se 1 (by rfl) ⟨2766752, by rfl⟩ : syracuseStep 3689003 = 5533505) B5533505
theorem B14756417 : Blo 1293965 14756417 := bstep (se 2 (by rfl) ⟨5533656, by rfl⟩ : syracuseStep 14756417 = 11067313) B11067313
theorem B2460307 : Blo 1293965 2460307 := bstep (se 1 (by rfl) ⟨1845230, by rfl⟩ : syracuseStep 2460307 = 3690461) B3690461
theorem B2075321 : Blo 1293965 2075321 := bstep (se 2 (by rfl) ⟨778245, by rfl⟩ : syracuseStep 2075321 = 1556491) B1556491
theorem B3279649 : Blo 1293965 3279649 := bstep (se 2 (by rfl) ⟨1229868, by rfl⟩ : syracuseStep 3279649 = 2459737) B2459737
theorem B3935063 : Blo 1293965 3935063 := bstep (se 1 (by rfl) ⟨2951297, by rfl⟩ : syracuseStep 3935063 = 5902595) B5902595
theorem B2952055 : Blo 1293965 2952055 := bstep (se 1 (by rfl) ⟨2214041, by rfl⟩ : syracuseStep 2952055 = 4428083) B4428083
theorem B5532563 : Blo 1293965 5532563 := bstep (se 1 (by rfl) ⟨4149422, by rfl⟩ : syracuseStep 5532563 = 8298845) B8298845
theorem B3689401 : Blo 1293965 3689401 := bstep (se 2 (by rfl) ⟨1383525, by rfl⟩ : syracuseStep 3689401 = 2767051) B2767051
theorem B6556625 : Blo 1293965 6556625 := bstep (se 2 (by rfl) ⟨2458734, by rfl⟩ : syracuseStep 6556625 = 4917469) B4917469
theorem B3935293 : Blo 1293965 3935293 := bstep (se 3 (by rfl) ⟨737867, by rfl⟩ : syracuseStep 3935293 = 1475735) B1475735
theorem B4369679 : Blo 1293965 4369679 := bstep (se 1 (by rfl) ⟨3277259, by rfl⟩ : syracuseStep 4369679 = 6554519) B6554519
theorem B2911607 : Blo 1293965 2911607 := bstep (se 1 (by rfl) ⟨2183705, by rfl⟩ : syracuseStep 2911607 = 4367411) B4367411
theorem B3280247 : Blo 1293965 3280247 := bstep (se 1 (by rfl) ⟨2460185, by rfl⟩ : syracuseStep 3280247 = 4920371) B4920371
theorem B7876061 : Blo 1293965 7876061 := bstep (se 3 (by rfl) ⟨1476761, by rfl⟩ : syracuseStep 7876061 = 2953523) B2953523
theorem B4664861 : Blo 1293965 4664861 := bstep (se 3 (by rfl) ⟨874661, by rfl⟩ : syracuseStep 4664861 = 1749323) B1749323
theorem B4369949 : Blo 1293965 4369949 := bstep (se 3 (by rfl) ⟨819365, by rfl⟩ : syracuseStep 4369949 = 1638731) B1638731
theorem B2911787 : Blo 1293965 2911787 := bstep (se 1 (by rfl) ⟨2183840, by rfl⟩ : syracuseStep 2911787 = 4367681) B4367681
theorem B1420859 : Blo 1293965 1420859 := bstep (se 1 (by rfl) ⟨1065644, by rfl⟩ : syracuseStep 1420859 = 2131289) B2131289
theorem B7573285 : Blo 1293965 7573285 := bstep (se 4 (by rfl) ⟨709995, by rfl⟩ : syracuseStep 7573285 = 1419991) B1419991
theorem B1773371 : Blo 1293965 1773371 := bstep (se 1 (by rfl) ⟨1330028, by rfl⟩ : syracuseStep 1773371 = 2660057) B2660057
theorem B5533555 : Blo 1293965 5533555 := bstep (se 1 (by rfl) ⟨4150166, by rfl⟩ : syracuseStep 5533555 = 8300333) B8300333
theorem B3321719 : Blo 1293965 3321719 := bstep (se 1 (by rfl) ⟨2491289, by rfl⟩ : syracuseStep 3321719 = 4982579) B4982579
theorem B2215799 : Blo 1293965 2215799 := bstep (se 1 (by rfl) ⟨1661849, by rfl⟩ : syracuseStep 2215799 = 3323699) B3323699
theorem B2912147 : Blo 1293965 2912147 := bstep (se 1 (by rfl) ⟨2184110, by rfl⟩ : syracuseStep 2912147 = 4368221) B4368221
theorem B2912201 : Blo 1293965 2912201 := bstep (se 2 (by rfl) ⟨1092075, by rfl⟩ : syracuseStep 2912201 = 2184151) B2184151
theorem B4919687 : Blo 1293965 4919687 := bstep (se 1 (by rfl) ⟨3689765, by rfl⟩ : syracuseStep 4919687 = 7379531) B7379531
theorem B13996435 : Blo 1293965 13996435 := bstep (se 1 (by rfl) ⟨10497326, by rfl⟩ : syracuseStep 13996435 = 20994653) B20994653
theorem B16822849 : Blo 1293965 16822849 := bstep (se 2 (by rfl) ⟨6308568, by rfl⟩ : syracuseStep 16822849 = 12617137) B12617137
theorem B1995337 : Blo 1293965 1995337 := bstep (se 2 (by rfl) ⟨748251, by rfl⟩ : syracuseStep 1995337 = 1496503) B1496503
theorem B2912903 : Blo 1293965 2912903 := bstep (se 1 (by rfl) ⟨2184677, by rfl⟩ : syracuseStep 2912903 = 4369355) B4369355
theorem B2183881 : Blo 1293965 2183881 := bstep (se 2 (by rfl) ⟨818955, by rfl⟩ : syracuseStep 2183881 = 1637911) B1637911
theorem B2913083 : Blo 1293965 2913083 := bstep (se 1 (by rfl) ⟨2184812, by rfl⟩ : syracuseStep 2913083 = 4369625) B4369625
theorem B1684283 : Blo 1293965 1684283 := bstep (se 1 (by rfl) ⟨1263212, by rfl⟩ : syracuseStep 1684283 = 2526425) B2526425
theorem B15749977 : Blo 1293965 15749977 := bstep (se 2 (by rfl) ⟨5906241, by rfl⟩ : syracuseStep 15749977 = 11812483) B11812483
theorem B7000921 : Blo 1293965 7000921 := bstep (se 2 (by rfl) ⟨2625345, by rfl⟩ : syracuseStep 7000921 = 5250691) B5250691
theorem B4371353 : Blo 1293965 4371353 := bstep (se 2 (by rfl) ⟨1639257, by rfl⟩ : syracuseStep 4371353 = 3278515) B3278515
theorem B2913209 : Blo 1293965 2913209 := bstep (se 2 (by rfl) ⟨1092453, by rfl⟩ : syracuseStep 2913209 = 2184907) B2184907
theorem B6558731 : Blo 1293965 6558731 := bstep (se 1 (by rfl) ⟨4919048, by rfl⟩ : syracuseStep 6558731 = 9838097) B9838097
theorem B6640663 : Blo 1293965 6640663 := bstep (se 1 (by rfl) ⟨4980497, by rfl⟩ : syracuseStep 6640663 = 9960995) B9960995
theorem B6558893 : Blo 1293965 6558893 := bstep (se 3 (by rfl) ⟨1229792, by rfl⟩ : syracuseStep 6558893 = 2459585) B2459585
theorem B3110089 : Blo 1293965 3110089 := bstep (se 2 (by rfl) ⟨1166283, by rfl⟩ : syracuseStep 3110089 = 2332567) B2332567
theorem B2913551 : Blo 1293965 2913551 := bstep (se 1 (by rfl) ⟨2185163, by rfl⟩ : syracuseStep 2913551 = 4370327) B4370327
theorem B2913569 : Blo 1293965 2913569 := bstep (se 2 (by rfl) ⟨1092588, by rfl⟩ : syracuseStep 2913569 = 2185177) B2185177
theorem B7476569 : Blo 1293965 7476569 := bstep (se 2 (by rfl) ⟨2803713, by rfl⟩ : syracuseStep 7476569 = 5607427) B5607427
theorem B7370099 : Blo 1293965 7370099 := bstep (se 1 (by rfl) ⟨5527574, by rfl⟩ : syracuseStep 7370099 = 11055149) B11055149
theorem B7001459 : Blo 1293965 7001459 := bstep (se 1 (by rfl) ⟨5251094, by rfl⟩ : syracuseStep 7001459 = 10502189) B10502189
theorem B2184583 : Blo 1293965 2184583 := bstep (se 1 (by rfl) ⟨1638437, by rfl⟩ : syracuseStep 2184583 = 3276875) B3276875
theorem B3110291 : Blo 1293965 3110291 := bstep (se 1 (by rfl) ⟨2332718, by rfl⟩ : syracuseStep 3110291 = 4665437) B4665437
theorem B5535161 : Blo 1293965 5535161 := bstep (se 2 (by rfl) ⟨2075685, by rfl⟩ : syracuseStep 5535161 = 4151371) B4151371
theorem B4666891 : Blo 1293965 4666891 := bstep (se 1 (by rfl) ⟨3500168, by rfl⟩ : syracuseStep 4666891 = 7000337) B7000337
theorem B3937825 : Blo 1293965 3937825 := bstep (se 2 (by rfl) ⟨1476684, by rfl⟩ : syracuseStep 3937825 = 2953369) B2953369
theorem B4372055 : Blo 1293965 4372055 := bstep (se 1 (by rfl) ⟨3279041, by rfl⟩ : syracuseStep 4372055 = 6558083) B6558083
theorem B2913911 : Blo 1293965 2913911 := bstep (se 1 (by rfl) ⟨2185433, by rfl⟩ : syracuseStep 2913911 = 4370867) B4370867
theorem B2766521 : Blo 1293965 2766521 := bstep (se 2 (by rfl) ⟨1037445, by rfl⟩ : syracuseStep 2766521 = 2074891) B2074891
theorem B5535503 : Blo 1293965 5535503 := bstep (se 1 (by rfl) ⟨4151627, by rfl⟩ : syracuseStep 5535503 = 8303255) B8303255
theorem B2914091 : Blo 1293965 2914091 := bstep (se 1 (by rfl) ⟨2185568, by rfl⟩ : syracuseStep 2914091 = 4371137) B4371137
theorem B1456015 : Blo 1293965 1456015 := bstep (se 1 (by rfl) ⟨1092011, by rfl⟩ : syracuseStep 1456015 = 2184023) B2184023
theorem B6551441 : Blo 1293965 6551441 := bstep (se 2 (by rfl) ⟨2456790, by rfl⟩ : syracuseStep 6551441 = 4913581) B4913581
theorem B4913081 : Blo 1293965 4913081 := bstep (se 2 (by rfl) ⟨1842405, by rfl⟩ : syracuseStep 4913081 = 3684811) B3684811
theorem B6649859 : Blo 1293965 6649859 := bstep (se 1 (by rfl) ⟨4987394, by rfl⟩ : syracuseStep 6649859 = 9974789) B9974789
theorem B2185231 : Blo 1293965 2185231 := bstep (se 1 (by rfl) ⟨1638923, by rfl⟩ : syracuseStep 2185231 = 3277847) B3277847
theorem B4372541 : Blo 1293965 4372541 := bstep (se 3 (by rfl) ⟨819851, by rfl⟩ : syracuseStep 4372541 = 1639703) B1639703
theorem B13998167 : Blo 1293965 13998167 := bstep (se 1 (by rfl) ⟨10498625, by rfl⟩ : syracuseStep 13998167 = 20997251) B20997251
theorem B2914451 : Blo 1293965 2914451 := bstep (se 1 (by rfl) ⟨2185838, by rfl⟩ : syracuseStep 2914451 = 4371677) B4371677
theorem B2914505 : Blo 1293965 2914505 := bstep (se 2 (by rfl) ⟨1092939, by rfl⟩ : syracuseStep 2914505 = 2185879) B2185879
theorem B1751339 : Blo 1293965 1751339 := bstep (se 1 (by rfl) ⟨1313504, by rfl⟩ : syracuseStep 1751339 = 2627009) B2627009
theorem B26589505 : Blo 1293965 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B1456519 : Blo 1293965 1456519 := bstep (se 1 (by rfl) ⟨1092389, by rfl⟩ : syracuseStep 1456519 = 2184779) B2184779
theorem B2767375 : Blo 1293965 2767375 := bstep (se 1 (by rfl) ⟨2075531, by rfl⟩ : syracuseStep 2767375 = 4151063) B4151063
theorem B2185771 : Blo 1293965 2185771 := bstep (se 1 (by rfl) ⟨1639328, by rfl⟩ : syracuseStep 2185771 = 3278657) B3278657
theorem B2333243 : Blo 1293965 2333243 := bstep (se 1 (by rfl) ⟨1749932, by rfl⟩ : syracuseStep 2333243 = 3499865) B3499865
theorem B1456699 : Blo 1293965 1456699 := bstep (se 1 (by rfl) ⟨1092524, by rfl⟩ : syracuseStep 1456699 = 2185049) B2185049
theorem B3275417 : Blo 1293965 3275417 := bstep (se 2 (by rfl) ⟨1228281, by rfl⟩ : syracuseStep 3275417 = 2456563) B2456563
theorem B2185913 : Blo 1293965 2185913 := bstep (se 2 (by rfl) ⟨819717, by rfl⟩ : syracuseStep 2185913 = 1639435) B1639435
theorem B5905133 : Blo 1293965 5905133 := bstep (se 3 (by rfl) ⟨1107212, by rfl⟩ : syracuseStep 5905133 = 2214425) B2214425
theorem B6560513 : Blo 1293965 6560513 := bstep (se 2 (by rfl) ⟨2460192, by rfl⟩ : syracuseStep 6560513 = 4920385) B4920385
theorem B1383175 : Blo 1293965 1383175 := bstep (se 1 (by rfl) ⟨1037381, by rfl⟩ : syracuseStep 1383175 = 2074763) B2074763
theorem B3324683 : Blo 1293965 3324683 := bstep (se 1 (by rfl) ⟨2493512, by rfl⟩ : syracuseStep 3324683 = 4987025) B4987025
theorem B7371557 : Blo 1293965 7371557 := bstep (se 4 (by rfl) ⟨691083, by rfl⟩ : syracuseStep 7371557 = 1382167) B1382167
theorem B3275579 : Blo 1293965 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B56736611 : Blo 1293965 56736611 := bstep (se 1 (by rfl) ⟨42552458, by rfl⟩ : syracuseStep 56736611 = 85104917) B85104917
theorem B49797989 : Blo 1293965 49797989 := bstep (se 4 (by rfl) ⟨4668561, by rfl⟩ : syracuseStep 49797989 = 9337123) B9337123
theorem B2915207 : Blo 1293965 2915207 := bstep (se 1 (by rfl) ⟨2186405, by rfl⟩ : syracuseStep 2915207 = 4372811) B4372811
theorem B4914067 : Blo 1293965 4914067 := bstep (se 1 (by rfl) ⟨3685550, by rfl⟩ : syracuseStep 4914067 = 7371101) B7371101
theorem B1383355 : Blo 1293965 1383355 := bstep (se 1 (by rfl) ⟨1037516, by rfl⟩ : syracuseStep 1383355 = 2075033) B2075033
theorem B1457167 : Blo 1293965 1457167 := bstep (se 1 (by rfl) ⟨1092875, by rfl⟩ : syracuseStep 1457167 = 2185751) B2185751
theorem B2915387 : Blo 1293965 2915387 := bstep (se 1 (by rfl) ⟨2186540, by rfl⟩ : syracuseStep 2915387 = 4373081) B4373081
theorem B2456723 : Blo 1293965 2456723 := bstep (se 1 (by rfl) ⟨1842542, by rfl⟩ : syracuseStep 2456723 = 3685085) B3685085
theorem B3275923 : Blo 1293965 3275923 := bstep (se 1 (by rfl) ⟨2456942, by rfl⟩ : syracuseStep 3275923 = 4913885) B4913885
theorem B2915513 : Blo 1293965 2915513 := bstep (se 2 (by rfl) ⟨1093317, by rfl⟩ : syracuseStep 2915513 = 2186635) B2186635
theorem B3276065 : Blo 1293965 3276065 := bstep (se 2 (by rfl) ⟨1228524, by rfl⟩ : syracuseStep 3276065 = 2457049) B2457049
theorem B2186615 : Blo 1293965 2186615 := bstep (se 1 (by rfl) ⟨1639961, by rfl⟩ : syracuseStep 2186615 = 3279923) B3279923
theorem B8297873 : Blo 1293965 8297873 := bstep (se 2 (by rfl) ⟨3111702, by rfl⟩ : syracuseStep 8297873 = 6223405) B6223405
theorem B6643129 : Blo 1293965 6643129 := bstep (se 2 (by rfl) ⟨2491173, by rfl⟩ : syracuseStep 6643129 = 4982347) B4982347
theorem B7372241 : Blo 1293965 7372241 := bstep (se 2 (by rfl) ⟨2764590, by rfl⟩ : syracuseStep 7372241 = 5529181) B5529181
theorem B1842679 : Blo 1293965 1842679 := bstep (se 1 (by rfl) ⟨1382009, by rfl⟩ : syracuseStep 1842679 = 2764019) B2764019
theorem B1940999 : Blo 1293965 1940999 := bstep (se 1 (by rfl) ⟨1455749, by rfl⟩ : syracuseStep 1940999 = 2911499) B2911499
theorem B1457671 : Blo 1293965 1457671 := bstep (se 1 (by rfl) ⟨1093253, by rfl⟩ : syracuseStep 1457671 = 2186507) B2186507
theorem B2915855 : Blo 1293965 2915855 := bstep (se 1 (by rfl) ⟨2186891, by rfl⟩ : syracuseStep 2915855 = 4373783) B4373783
theorem B2915873 : Blo 1293965 2915873 := bstep (se 2 (by rfl) ⟨1093452, by rfl⟩ : syracuseStep 2915873 = 2186905) B2186905
theorem B1941035 : Blo 1293965 1941035 := bstep (se 1 (by rfl) ⟨1455776, by rfl⟩ : syracuseStep 1941035 = 2911553) B2911553
theorem B5529131 : Blo 1293965 5529131 := bstep (se 1 (by rfl) ⟨4146848, by rfl⟩ : syracuseStep 5529131 = 8293697) B8293697
theorem B7003691 : Blo 1293965 7003691 := bstep (se 1 (by rfl) ⟨5252768, by rfl⟩ : syracuseStep 7003691 = 10505537) B10505537
theorem B7003709 : Blo 1293965 7003709 := bstep (se 3 (by rfl) ⟨1313195, by rfl⟩ : syracuseStep 7003709 = 2626391) B2626391
theorem B1941065 : Blo 1293965 1941065 := bstep (se 2 (by rfl) ⟨727899, by rfl⟩ : syracuseStep 1941065 = 1455799) B1455799
theorem B1293967 : Blo 1293965 1293967 := bstep (se 1 (by rfl) ⟨970475, by rfl⟩ : syracuseStep 1293967 = 1940951) B1940951
theorem B1294011 : Blo 1293965 1294011 := bstep (se 1 (by rfl) ⟨970508, by rfl⟩ : syracuseStep 1294011 = 1941017) B1941017
theorem B1941179 : Blo 1293965 1941179 := bstep (se 1 (by rfl) ⟨1455884, by rfl⟩ : syracuseStep 1941179 = 2911769) B2911769
theorem B1457851 : Blo 1293965 1457851 := bstep (se 1 (by rfl) ⟨1093388, by rfl⟩ : syracuseStep 1457851 = 2186777) B2186777
theorem B1941239 : Blo 1293965 1941239 := bstep (se 1 (by rfl) ⟨1455929, by rfl⟩ : syracuseStep 1941239 = 2911859) B2911859
theorem B33185537 : Blo 1293965 33185537 := bstep (se 2 (by rfl) ⟨12444576, by rfl⟩ : syracuseStep 33185537 = 24889153) B24889153
theorem B1294087 : Blo 1293965 1294087 := bstep (se 1 (by rfl) ⟨970565, by rfl⟩ : syracuseStep 1294087 = 1941131) B1941131
theorem B1294095 : Blo 1293965 1294095 := bstep (se 1 (by rfl) ⟨970571, by rfl⟩ : syracuseStep 1294095 = 1941143) B1941143
theorem B1941263 : Blo 1293965 1941263 := bstep (se 1 (by rfl) ⟨1455947, by rfl⟩ : syracuseStep 1941263 = 2911895) B2911895
theorem B7372559 : Blo 1293965 7372559 := bstep (se 1 (by rfl) ⟨5529419, by rfl⟩ : syracuseStep 7372559 = 11058839) B11058839
theorem B1941305 : Blo 1293965 1941305 := bstep (se 2 (by rfl) ⟨727989, by rfl⟩ : syracuseStep 1941305 = 1455979) B1455979
theorem B1294139 : Blo 1293965 1294139 := bstep (se 1 (by rfl) ⟨970604, by rfl⟩ : syracuseStep 1294139 = 1941209) B1941209
theorem B1843003 : Blo 1293965 1843003 := bstep (se 1 (by rfl) ⟨1382252, by rfl⟩ : syracuseStep 1843003 = 2764505) B2764505
theorem B3497789 : Blo 1293965 3497789 := bstep (se 3 (by rfl) ⟨655835, by rfl⟩ : syracuseStep 3497789 = 1311671) B1311671
theorem B1294215 : Blo 1293965 1294215 := bstep (se 1 (by rfl) ⟨970661, by rfl⟩ : syracuseStep 1294215 = 1941323) B1941323
theorem B1941383 : Blo 1293965 1941383 := bstep (se 1 (by rfl) ⟨1456037, by rfl⟩ : syracuseStep 1941383 = 2912075) B2912075
theorem B1294223 : Blo 1293965 1294223 := bstep (se 1 (by rfl) ⟨970667, by rfl⟩ : syracuseStep 1294223 = 1941335) B1941335
theorem B37355417 : Blo 1293965 37355417 := bstep (se 2 (by rfl) ⟨14008281, by rfl⟩ : syracuseStep 37355417 = 28016563) B28016563
theorem B1941419 : Blo 1293965 1941419 := bstep (se 1 (by rfl) ⟨1456064, by rfl⟩ : syracuseStep 1941419 = 2912129) B2912129
theorem B1294267 : Blo 1293965 1294267 := bstep (se 1 (by rfl) ⟨970700, by rfl⟩ : syracuseStep 1294267 = 1941401) B1941401
theorem B1941449 : Blo 1293965 1941449 := bstep (se 2 (by rfl) ⟨728043, by rfl⟩ : syracuseStep 1941449 = 1456087) B1456087
theorem B6553547 : Blo 1293965 6553547 := bstep (se 1 (by rfl) ⟨4915160, by rfl⟩ : syracuseStep 6553547 = 9830321) B9830321
theorem B1294375 : Blo 1293965 1294375 := bstep (se 1 (by rfl) ⟨970781, by rfl⟩ : syracuseStep 1294375 = 1941563) B1941563
theorem B1294415 : Blo 1293965 1294415 := bstep (se 1 (by rfl) ⟨970811, by rfl⟩ : syracuseStep 1294415 = 1941623) B1941623
theorem B9338969 : Blo 1293965 9338969 := bstep (se 2 (by rfl) ⟨3502113, by rfl⟩ : syracuseStep 9338969 = 7004227) B7004227
theorem B1294431 : Blo 1293965 1294431 := bstep (se 1 (by rfl) ⟨970823, by rfl⟩ : syracuseStep 1294431 = 1941647) B1941647
theorem B1294459 : Blo 1293965 1294459 := bstep (se 1 (by rfl) ⟨970844, by rfl⟩ : syracuseStep 1294459 = 1941689) B1941689
theorem B1294511 : Blo 1293965 1294511 := bstep (se 1 (by rfl) ⟨970883, by rfl⟩ : syracuseStep 1294511 = 1941767) B1941767
theorem B1294535 : Blo 1293965 1294535 := bstep (se 1 (by rfl) ⟨970901, by rfl⟩ : syracuseStep 1294535 = 1941803) B1941803
theorem B1294555 : Blo 1293965 1294555 := bstep (se 1 (by rfl) ⟨970916, by rfl⟩ : syracuseStep 1294555 = 1941833) B1941833
theorem B1294631 : Blo 1293965 1294631 := bstep (se 1 (by rfl) ⟨970973, by rfl⟩ : syracuseStep 1294631 = 1941947) B1941947
theorem B20988229 : Blo 1293965 20988229 := bstep (se 4 (by rfl) ⟨1967646, by rfl⟩ : syracuseStep 20988229 = 3935293) B3935293
theorem B1294671 : Blo 1293965 1294671 := bstep (se 1 (by rfl) ⟨971003, by rfl⟩ : syracuseStep 1294671 = 1942007) B1942007
theorem B1294687 : Blo 1293965 1294687 := bstep (se 1 (by rfl) ⟨971015, by rfl⟩ : syracuseStep 1294687 = 1942031) B1942031
theorem B1294715 : Blo 1293965 1294715 := bstep (se 1 (by rfl) ⟨971036, by rfl⟩ : syracuseStep 1294715 = 1942073) B1942073
theorem B3277199 : Blo 1293965 3277199 := bstep (se 1 (by rfl) ⟨2457899, by rfl⟩ : syracuseStep 3277199 = 4915799) B4915799
theorem B1941935 : Blo 1293965 1941935 := bstep (se 1 (by rfl) ⟨1456451, by rfl⟩ : syracuseStep 1941935 = 2912903) B2912903
theorem B1294767 : Blo 1293965 1294767 := bstep (se 1 (by rfl) ⟨971075, by rfl⟩ : syracuseStep 1294767 = 1942151) B1942151
theorem B1294791 : Blo 1293965 1294791 := bstep (se 1 (by rfl) ⟨971093, by rfl⟩ : syracuseStep 1294791 = 1942187) B1942187
theorem B1294811 : Blo 1293965 1294811 := bstep (se 1 (by rfl) ⟨971108, by rfl⟩ : syracuseStep 1294811 = 1942217) B1942217
theorem B1942025 : Blo 1293965 1942025 := bstep (se 2 (by rfl) ⟨728259, by rfl⟩ : syracuseStep 1942025 = 1456519) B1456519
theorem B18661913 : Blo 1293965 18661913 := bstep (se 2 (by rfl) ⟨6998217, by rfl⟩ : syracuseStep 18661913 = 13996435) B13996435
theorem B8290849 : Blo 1293965 8290849 := bstep (se 2 (by rfl) ⟨3109068, by rfl⟩ : syracuseStep 8290849 = 6218137) B6218137
theorem B1942055 : Blo 1293965 1942055 := bstep (se 1 (by rfl) ⟨1456541, by rfl⟩ : syracuseStep 1942055 = 2913083) B2913083
theorem B1294887 : Blo 1293965 1294887 := bstep (se 1 (by rfl) ⟨971165, by rfl⟩ : syracuseStep 1294887 = 1942331) B1942331
theorem B1294927 : Blo 1293965 1294927 := bstep (se 1 (by rfl) ⟨971195, by rfl⟩ : syracuseStep 1294927 = 1942391) B1942391
theorem B1294943 : Blo 1293965 1294943 := bstep (se 1 (by rfl) ⟨971207, by rfl⟩ : syracuseStep 1294943 = 1942415) B1942415
theorem B1942139 : Blo 1293965 1942139 := bstep (se 1 (by rfl) ⟨1456604, by rfl⟩ : syracuseStep 1942139 = 2913209) B2913209
theorem B1294971 : Blo 1293965 1294971 := bstep (se 1 (by rfl) ⟨971228, by rfl⟩ : syracuseStep 1294971 = 1942457) B1942457
theorem B1295023 : Blo 1293965 1295023 := bstep (se 1 (by rfl) ⟨971267, by rfl⟩ : syracuseStep 1295023 = 1942535) B1942535
theorem B1295047 : Blo 1293965 1295047 := bstep (se 1 (by rfl) ⟨971285, by rfl⟩ : syracuseStep 1295047 = 1942571) B1942571
theorem B1639111 : Blo 1293965 1639111 := bstep (se 1 (by rfl) ⟨1229333, by rfl⟩ : syracuseStep 1639111 = 2458667) B2458667
theorem B15958739 : Blo 1293965 15958739 := bstep (se 1 (by rfl) ⟨11969054, by rfl⟩ : syracuseStep 15958739 = 23938109) B23938109
theorem B3277523 : Blo 1293965 3277523 := bstep (se 1 (by rfl) ⟨2458142, by rfl⟩ : syracuseStep 3277523 = 4916285) B4916285
theorem B1295067 : Blo 1293965 1295067 := bstep (se 1 (by rfl) ⟨971300, by rfl⟩ : syracuseStep 1295067 = 1942601) B1942601
theorem B1942265 : Blo 1293965 1942265 := bstep (se 2 (by rfl) ⟨728349, by rfl⟩ : syracuseStep 1942265 = 1456699) B1456699
theorem B22430465 : Blo 1293965 22430465 := bstep (se 2 (by rfl) ⟨8411424, by rfl⟩ : syracuseStep 22430465 = 16822849) B16822849
theorem B4915997 : Blo 1293965 4915997 := bstep (se 3 (by rfl) ⟨921749, by rfl⟩ : syracuseStep 4915997 = 1843499) B1843499
theorem B4670237 : Blo 1293965 4670237 := bstep (se 3 (by rfl) ⟨875669, by rfl⟩ : syracuseStep 4670237 = 1751339) B1751339
theorem B1295143 : Blo 1293965 1295143 := bstep (se 1 (by rfl) ⟨971357, by rfl⟩ : syracuseStep 1295143 = 1942715) B1942715
theorem B4916011 : Blo 1293965 4916011 := bstep (se 1 (by rfl) ⟨3687008, by rfl⟩ : syracuseStep 4916011 = 7374017) B7374017
theorem B1295183 : Blo 1293965 1295183 := bstep (se 1 (by rfl) ⟨971387, by rfl⟩ : syracuseStep 1295183 = 1942775) B1942775
theorem B1942367 : Blo 1293965 1942367 := bstep (se 1 (by rfl) ⟨1456775, by rfl⟩ : syracuseStep 1942367 = 2913551) B2913551
theorem B1295199 : Blo 1293965 1295199 := bstep (se 1 (by rfl) ⟨971399, by rfl⟩ : syracuseStep 1295199 = 1942799) B1942799
theorem B1942379 : Blo 1293965 1942379 := bstep (se 1 (by rfl) ⟨1456784, by rfl⟩ : syracuseStep 1942379 = 2913569) B2913569
theorem B1295227 : Blo 1293965 1295227 := bstep (se 1 (by rfl) ⟨971420, by rfl⟩ : syracuseStep 1295227 = 1942841) B1942841
theorem B1295279 : Blo 1293965 1295279 := bstep (se 1 (by rfl) ⟨971459, by rfl⟩ : syracuseStep 1295279 = 1942919) B1942919
theorem B2073527 : Blo 1293965 2073527 := bstep (se 1 (by rfl) ⟨1555145, by rfl⟩ : syracuseStep 2073527 = 3110291) B3110291
theorem B1295303 : Blo 1293965 1295303 := bstep (se 1 (by rfl) ⟨971477, by rfl⟩ : syracuseStep 1295303 = 1942955) B1942955
theorem B1295323 : Blo 1293965 1295323 := bstep (se 1 (by rfl) ⟨971492, by rfl⟩ : syracuseStep 1295323 = 1942985) B1942985
theorem B1295399 : Blo 1293965 1295399 := bstep (se 1 (by rfl) ⟨971549, by rfl⟩ : syracuseStep 1295399 = 1943099) B1943099
theorem B19948589 : Blo 1293965 19948589 := bstep (se 3 (by rfl) ⟨3740360, by rfl⟩ : syracuseStep 19948589 = 7480721) B7480721
theorem B1942607 : Blo 1293965 1942607 := bstep (se 1 (by rfl) ⟨1456955, by rfl⟩ : syracuseStep 1942607 = 2913911) B2913911
theorem B1295439 : Blo 1293965 1295439 := bstep (se 1 (by rfl) ⟨971579, by rfl⟩ : syracuseStep 1295439 = 1943159) B1943159
theorem B1295455 : Blo 1293965 1295455 := bstep (se 1 (by rfl) ⟨971591, by rfl⟩ : syracuseStep 1295455 = 1943183) B1943183
theorem B1295483 : Blo 1293965 1295483 := bstep (se 1 (by rfl) ⟨971612, by rfl⟩ : syracuseStep 1295483 = 1943225) B1943225
theorem B4146347 : Blo 1293965 4146347 := bstep (se 1 (by rfl) ⟨3109760, by rfl⟩ : syracuseStep 4146347 = 6219521) B6219521
theorem B1295535 : Blo 1293965 1295535 := bstep (se 1 (by rfl) ⟨971651, by rfl⟩ : syracuseStep 1295535 = 1943303) B1943303
theorem B1942727 : Blo 1293965 1942727 := bstep (se 1 (by rfl) ⟨1457045, by rfl⟩ : syracuseStep 1942727 = 2914091) B2914091
theorem B1295559 : Blo 1293965 1295559 := bstep (se 1 (by rfl) ⟨971669, by rfl⟩ : syracuseStep 1295559 = 1943339) B1943339
theorem B1295579 : Blo 1293965 1295579 := bstep (se 1 (by rfl) ⟨971684, by rfl⟩ : syracuseStep 1295579 = 1943369) B1943369
theorem B1844473 : Blo 1293965 1844473 := bstep (se 2 (by rfl) ⟨691677, by rfl⟩ : syracuseStep 1844473 = 1383355) B1383355
theorem B4367627 : Blo 1293965 4367627 := bstep (se 1 (by rfl) ⟨3275720, by rfl⟩ : syracuseStep 4367627 = 6551441) B6551441
theorem B1295655 : Blo 1293965 1295655 := bstep (se 1 (by rfl) ⟨971741, by rfl⟩ : syracuseStep 1295655 = 1943483) B1943483
theorem B1295695 : Blo 1293965 1295695 := bstep (se 1 (by rfl) ⟨971771, by rfl⟩ : syracuseStep 1295695 = 1943543) B1943543
theorem B4433239 : Blo 1293965 4433239 := bstep (se 1 (by rfl) ⟨3324929, by rfl⟩ : syracuseStep 4433239 = 6649859) B6649859
theorem B1295711 : Blo 1293965 1295711 := bstep (se 1 (by rfl) ⟨971783, by rfl⟩ : syracuseStep 1295711 = 1943567) B1943567
theorem B1942889 : Blo 1293965 1942889 := bstep (se 2 (by rfl) ⟨728583, by rfl⟩ : syracuseStep 1942889 = 1457167) B1457167
theorem B1295739 : Blo 1293965 1295739 := bstep (se 1 (by rfl) ⟨971804, by rfl⟩ : syracuseStep 1295739 = 1943609) B1943609
theorem B6555005 : Blo 1293965 6555005 := bstep (se 3 (by rfl) ⟨1229063, by rfl⟩ : syracuseStep 6555005 = 2458127) B2458127
theorem B9332111 : Blo 1293965 9332111 := bstep (se 1 (by rfl) ⟨6999083, by rfl⟩ : syracuseStep 9332111 = 13998167) B13998167
theorem B1639855 : Blo 1293965 1639855 := bstep (se 1 (by rfl) ⟨1229891, by rfl⟩ : syracuseStep 1639855 = 2459783) B2459783
theorem B1295791 : Blo 1293965 1295791 := bstep (se 1 (by rfl) ⟨971843, by rfl⟩ : syracuseStep 1295791 = 1943687) B1943687
theorem B1942967 : Blo 1293965 1942967 := bstep (se 1 (by rfl) ⟨1457225, by rfl⟩ : syracuseStep 1942967 = 2914451) B2914451
theorem B1295815 : Blo 1293965 1295815 := bstep (se 1 (by rfl) ⟨971861, by rfl⟩ : syracuseStep 1295815 = 1943723) B1943723
theorem B2459099 : Blo 1293965 2459099 := bstep (se 1 (by rfl) ⟨1844324, by rfl⟩ : syracuseStep 2459099 = 3688649) B3688649
theorem B1943003 : Blo 1293965 1943003 := bstep (se 1 (by rfl) ⟨1457252, by rfl⟩ : syracuseStep 1943003 = 2914505) B2914505
theorem B1295835 : Blo 1293965 1295835 := bstep (se 1 (by rfl) ⟨971876, by rfl⟩ : syracuseStep 1295835 = 1943753) B1943753
theorem B4367897 : Blo 1293965 4367897 := bstep (se 2 (by rfl) ⟨1637961, by rfl⟩ : syracuseStep 4367897 = 3275923) B3275923
theorem B1295911 : Blo 1293965 1295911 := bstep (se 1 (by rfl) ⟨971933, by rfl⟩ : syracuseStep 1295911 = 1943867) B1943867
theorem B1295951 : Blo 1293965 1295951 := bstep (se 1 (by rfl) ⟨971963, by rfl⟩ : syracuseStep 1295951 = 1943927) B1943927
theorem B4146785 : Blo 1293965 4146785 := bstep (se 2 (by rfl) ⟨1555044, by rfl⟩ : syracuseStep 4146785 = 3110089) B3110089
theorem B2459335 : Blo 1293965 2459335 := bstep (se 1 (by rfl) ⟨1844501, by rfl⟩ : syracuseStep 2459335 = 3689003) B3689003
theorem B2623375 : Blo 1293965 2623375 := bstep (se 1 (by rfl) ⟨1967531, by rfl⟩ : syracuseStep 2623375 = 3935063) B3935063
theorem B37824407 : Blo 1293965 37824407 := bstep (se 1 (by rfl) ⟨28368305, by rfl⟩ : syracuseStep 37824407 = 56736611) B56736611
theorem B8857505 : Blo 1293965 8857505 := bstep (se 2 (by rfl) ⟨3321564, by rfl⟩ : syracuseStep 8857505 = 6643129) B6643129
theorem B1943471 : Blo 1293965 1943471 := bstep (se 1 (by rfl) ⟨1457603, by rfl⟩ : syracuseStep 1943471 = 2915207) B2915207
theorem B1943561 : Blo 1293965 1943561 := bstep (se 2 (by rfl) ⟨728835, by rfl⟩ : syracuseStep 1943561 = 1457671) B1457671
theorem B8865821 : Blo 1293965 8865821 := bstep (se 3 (by rfl) ⟨1662341, by rfl⟩ : syracuseStep 8865821 = 3324683) B3324683
theorem B1943591 : Blo 1293965 1943591 := bstep (se 1 (by rfl) ⟨1457693, by rfl⟩ : syracuseStep 1943591 = 2915387) B2915387
theorem B1943675 : Blo 1293965 1943675 := bstep (se 1 (by rfl) ⟨1457756, by rfl⟩ : syracuseStep 1943675 = 2915513) B2915513
theorem B4728989 : Blo 1293965 4728989 := bstep (se 3 (by rfl) ⟨886685, by rfl⟩ : syracuseStep 4728989 = 1773371) B1773371
theorem B4491421 : Blo 1293965 4491421 := bstep (se 3 (by rfl) ⟨842141, by rfl⟩ : syracuseStep 4491421 = 1684283) B1684283
theorem B1943801 : Blo 1293965 1943801 := bstep (se 2 (by rfl) ⟨728925, by rfl⟩ : syracuseStep 1943801 = 1457851) B1457851
theorem B5531915 : Blo 1293965 5531915 := bstep (se 1 (by rfl) ⟨4148936, by rfl⟩ : syracuseStep 5531915 = 8297873) B8297873
theorem B1943903 : Blo 1293965 1943903 := bstep (se 1 (by rfl) ⟨1457927, by rfl⟩ : syracuseStep 1943903 = 2915855) B2915855
theorem B1943915 : Blo 1293965 1943915 := bstep (se 1 (by rfl) ⟨1457936, by rfl⟩ : syracuseStep 1943915 = 2915873) B2915873
theorem B2214479 : Blo 1293965 2214479 := bstep (se 1 (by rfl) ⟨1660859, by rfl⟩ : syracuseStep 2214479 = 3321719) B3321719
theorem B1477199 : Blo 1293965 1477199 := bstep (se 1 (by rfl) ⟨1107899, by rfl⟩ : syracuseStep 1477199 = 2215799) B2215799
theorem B4369031 : Blo 1293965 4369031 := bstep (se 1 (by rfl) ⟨3276773, by rfl⟩ : syracuseStep 4369031 = 6553547) B6553547
theorem B4369085 : Blo 1293965 4369085 := bstep (se 3 (by rfl) ⟨819203, by rfl⟩ : syracuseStep 4369085 = 1638407) B1638407
theorem B3992279 : Blo 1293965 3992279 := bstep (se 1 (by rfl) ⟨2994209, by rfl⟩ : syracuseStep 3992279 = 5988419) B5988419
theorem B4369247 : Blo 1293965 4369247 := bstep (se 1 (by rfl) ⟨3276935, by rfl⟩ : syracuseStep 4369247 = 6553871) B6553871
theorem B8301487 : Blo 1293965 8301487 := bstep (se 1 (by rfl) ⟨6226115, by rfl⟩ : syracuseStep 8301487 = 12452231) B12452231
theorem B3279791 : Blo 1293965 3279791 := bstep (se 1 (by rfl) ⟨2459843, by rfl⟩ : syracuseStep 3279791 = 4919687) B4919687
theorem B4369409 : Blo 1293965 4369409 := bstep (se 2 (by rfl) ⟨1638528, by rfl⟩ : syracuseStep 4369409 = 3277057) B3277057
theorem B4984193 : Blo 1293965 4984193 := bstep (se 2 (by rfl) ⟨1869072, by rfl⟩ : syracuseStep 4984193 = 3738145) B3738145
theorem B3280409 : Blo 1293965 3280409 := bstep (se 2 (by rfl) ⟨1230153, by rfl⟩ : syracuseStep 3280409 = 2460307) B2460307
theorem B4984379 : Blo 1293965 4984379 := bstep (se 1 (by rfl) ⟨3738284, by rfl⟩ : syracuseStep 4984379 = 7476569) B7476569
theorem B2911841 : Blo 1293965 2911841 := bstep (se 2 (by rfl) ⟨1091940, by rfl⟩ : syracuseStep 2911841 = 2183881) B2183881
theorem B3690107 : Blo 1293965 3690107 := bstep (se 1 (by rfl) ⟨2767580, by rfl⟩ : syracuseStep 3690107 = 5535161) B5535161
theorem B20999969 : Blo 1293965 20999969 := bstep (se 2 (by rfl) ⟨7874988, by rfl⟩ : syracuseStep 20999969 = 15749977) B15749977
theorem B9334561 : Blo 1293965 9334561 := bstep (se 2 (by rfl) ⟨3500460, by rfl⟩ : syracuseStep 9334561 = 7000921) B7000921
theorem B4370219 : Blo 1293965 4370219 := bstep (se 1 (by rfl) ⟨3277664, by rfl⟩ : syracuseStep 4370219 = 6555329) B6555329
theorem B3936073 : Blo 1293965 3936073 := bstep (se 2 (by rfl) ⟨1476027, by rfl⟩ : syracuseStep 3936073 = 2952055) B2952055
theorem B3690335 : Blo 1293965 3690335 := bstep (se 1 (by rfl) ⟨2767751, by rfl⟩ : syracuseStep 3690335 = 5535503) B5535503
theorem B4919201 : Blo 1293965 4919201 := bstep (se 2 (by rfl) ⟨1844700, by rfl⟩ : syracuseStep 4919201 = 3689401) B3689401
theorem B2912183 : Blo 1293965 2912183 := bstep (se 1 (by rfl) ⟨2184137, by rfl⟩ : syracuseStep 2912183 = 4368275) B4368275
theorem B7376933 : Blo 1293965 7376933 := bstep (se 4 (by rfl) ⟨691587, by rfl⟩ : syracuseStep 7376933 = 1383175) B1383175
theorem B4370489 : Blo 1293965 4370489 := bstep (se 2 (by rfl) ⟨1638933, by rfl⟩ : syracuseStep 4370489 = 3277867) B3277867
theorem B6221981 : Blo 1293965 6221981 := bstep (se 3 (by rfl) ⟨1166621, by rfl⟩ : syracuseStep 6221981 = 2333243) B2333243
theorem B3788957 : Blo 1293965 3788957 := bstep (se 3 (by rfl) ⟨710429, by rfl⟩ : syracuseStep 3788957 = 1420859) B1420859
theorem B4370813 : Blo 1293965 4370813 := bstep (se 3 (by rfl) ⟨819527, by rfl⟩ : syracuseStep 4370813 = 1639055) B1639055
theorem B2183611 : Blo 1293965 2183611 := bstep (se 1 (by rfl) ⟨1637708, by rfl⟩ : syracuseStep 2183611 = 3275417) B3275417
theorem B7377389 : Blo 1293965 7377389 := bstep (se 3 (by rfl) ⟨1383260, by rfl⟩ : syracuseStep 7377389 = 2766521) B2766521
theorem B5534189 : Blo 1293965 5534189 := bstep (se 3 (by rfl) ⟨1037660, by rfl⟩ : syracuseStep 5534189 = 2075321) B2075321
theorem B3936755 : Blo 1293965 3936755 := bstep (se 1 (by rfl) ⟨2952566, by rfl⟩ : syracuseStep 3936755 = 5905133) B5905133
theorem B2912777 : Blo 1293965 2912777 := bstep (se 2 (by rfl) ⟨1092291, by rfl⟩ : syracuseStep 2912777 = 2184583) B2184583
theorem B2183719 : Blo 1293965 2183719 := bstep (se 1 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 2183719 = 3275579) B3275579
theorem B33198659 : Blo 1293965 33198659 := bstep (se 1 (by rfl) ⟨24898994, by rfl⟩ : syracuseStep 33198659 = 49797989) B49797989
theorem B4371083 : Blo 1293965 4371083 := bstep (se 1 (by rfl) ⟨3278312, by rfl⟩ : syracuseStep 4371083 = 6556625) B6556625
theorem B9835181 : Blo 1293965 9835181 := bstep (se 3 (by rfl) ⟨1844096, by rfl⟩ : syracuseStep 9835181 = 3688193) B3688193
theorem B6222521 : Blo 1293965 6222521 := bstep (se 2 (by rfl) ⟨2333445, by rfl⟩ : syracuseStep 6222521 = 4666891) B4666891
theorem B9327437 : Blo 1293965 9327437 := bstep (se 3 (by rfl) ⟨1748894, by rfl⟩ : syracuseStep 9327437 = 3497789) B3497789
theorem B2913119 : Blo 1293965 2913119 := bstep (se 1 (by rfl) ⟨2184839, by rfl⟩ : syracuseStep 2913119 = 4369679) B4369679
theorem B2184043 : Blo 1293965 2184043 := bstep (se 1 (by rfl) ⟨1638032, by rfl⟩ : syracuseStep 2184043 = 3276065) B3276065
theorem B4920173 : Blo 1293965 4920173 := bstep (se 3 (by rfl) ⟨922532, by rfl⟩ : syracuseStep 4920173 = 1845065) B1845065
theorem B3109907 : Blo 1293965 3109907 := bstep (se 1 (by rfl) ⟨2332430, by rfl⟩ : syracuseStep 3109907 = 4664861) B4664861
theorem B2913299 : Blo 1293965 2913299 := bstep (se 1 (by rfl) ⟨2184974, by rfl⟩ : syracuseStep 2913299 = 4369949) B4369949
theorem B10097713 : Blo 1293965 10097713 := bstep (se 2 (by rfl) ⟨3786642, by rfl⟩ : syracuseStep 10097713 = 7573285) B7573285
theorem B7378073 : Blo 1293965 7378073 := bstep (se 2 (by rfl) ⟨2766777, by rfl⟩ : syracuseStep 7378073 = 5533555) B5533555
theorem B22123691 : Blo 1293965 22123691 := bstep (se 1 (by rfl) ⟨16592768, by rfl⟩ : syracuseStep 22123691 = 33185537) B33185537
theorem B2913641 : Blo 1293965 2913641 := bstep (se 2 (by rfl) ⟨1092615, by rfl⟩ : syracuseStep 2913641 = 2185231) B2185231
theorem B14759333 : Blo 1293965 14759333 := bstep (se 4 (by rfl) ⟨1383687, by rfl⟩ : syracuseStep 14759333 = 2767375) B2767375
theorem B2332091 : Blo 1293965 2332091 := bstep (se 1 (by rfl) ⟨1749068, by rfl⟩ : syracuseStep 2332091 = 3498137) B3498137
theorem B4372001 : Blo 1293965 4372001 := bstep (se 2 (by rfl) ⟨1639500, by rfl⟩ : syracuseStep 4372001 = 3279001) B3279001
theorem B6559379 : Blo 1293965 6559379 := bstep (se 1 (by rfl) ⟨4919534, by rfl⟩ : syracuseStep 6559379 = 9839069) B9839069
theorem B4372217 : Blo 1293965 4372217 := bstep (se 2 (by rfl) ⟨1639581, by rfl⟩ : syracuseStep 4372217 = 3279163) B3279163
theorem B35452673 : Blo 1293965 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B2332523 : Blo 1293965 2332523 := bstep (se 1 (by rfl) ⟨1749392, by rfl⟩ : syracuseStep 2332523 = 3498785) B3498785
theorem B2185103 : Blo 1293965 2185103 := bstep (se 1 (by rfl) ⟨1638827, by rfl⟩ : syracuseStep 2185103 = 3277655) B3277655
theorem B5248955 : Blo 1293965 5248955 := bstep (se 1 (by rfl) ⟨3936716, by rfl⟩ : syracuseStep 5248955 = 7873433) B7873433
theorem B2914235 : Blo 1293965 2914235 := bstep (se 1 (by rfl) ⟨2185676, by rfl⟩ : syracuseStep 2914235 = 4371353) B4371353
theorem B10508291 : Blo 1293965 10508291 := bstep (se 1 (by rfl) ⟨7881218, by rfl⟩ : syracuseStep 10508291 = 15762437) B15762437
theorem B4372487 : Blo 1293965 4372487 := bstep (se 1 (by rfl) ⟨3279365, by rfl⟩ : syracuseStep 4372487 = 6558731) B6558731
theorem B2914361 : Blo 1293965 2914361 := bstep (se 2 (by rfl) ⟨1092885, by rfl⟩ : syracuseStep 2914361 = 2185771) B2185771
theorem B2660449 : Blo 1293965 2660449 := bstep (se 2 (by rfl) ⟨997668, by rfl⟩ : syracuseStep 2660449 = 1995337) B1995337
theorem B4372595 : Blo 1293965 4372595 := bstep (se 1 (by rfl) ⟨3279446, by rfl⟩ : syracuseStep 4372595 = 6558893) B6558893
theorem B2185339 : Blo 1293965 2185339 := bstep (se 1 (by rfl) ⟨1639004, by rfl⟩ : syracuseStep 2185339 = 3278009) B3278009
theorem B4913399 : Blo 1293965 4913399 := bstep (se 1 (by rfl) ⟨3685049, by rfl⟩ : syracuseStep 4913399 = 7370099) B7370099
theorem B4667639 : Blo 1293965 4667639 := bstep (se 1 (by rfl) ⟨3500729, by rfl⟩ : syracuseStep 4667639 = 7001459) B7001459
theorem B7002497 : Blo 1293965 7002497 := bstep (se 2 (by rfl) ⟨2625936, by rfl⟩ : syracuseStep 7002497 = 5251873) B5251873
theorem B4372865 : Blo 1293965 4372865 := bstep (se 2 (by rfl) ⟨1639824, by rfl⟩ : syracuseStep 4372865 = 3279649) B3279649
theorem B2914703 : Blo 1293965 2914703 := bstep (se 1 (by rfl) ⟨2186027, by rfl⟩ : syracuseStep 2914703 = 4372055) B4372055
theorem B6552089 : Blo 1293965 6552089 := bstep (se 2 (by rfl) ⟨2457033, by rfl⟩ : syracuseStep 6552089 = 4914067) B4914067
theorem B3152423 : Blo 1293965 3152423 := bstep (se 1 (by rfl) ⟨2364317, by rfl⟩ : syracuseStep 3152423 = 4728635) B4728635
theorem B3275387 : Blo 1293965 3275387 := bstep (se 1 (by rfl) ⟨2456540, by rfl⟩ : syracuseStep 3275387 = 4913081) B4913081
theorem B8854217 : Blo 1293965 8854217 := bstep (se 2 (by rfl) ⟨3320331, by rfl⟩ : syracuseStep 8854217 = 6640663) B6640663
theorem B8411849 : Blo 1293965 8411849 := bstep (se 2 (by rfl) ⟨3154443, by rfl⟩ : syracuseStep 8411849 = 6308887) B6308887
theorem B2915027 : Blo 1293965 2915027 := bstep (se 1 (by rfl) ⟨2186270, by rfl⟩ : syracuseStep 2915027 = 4372541) B4372541
theorem B2186203 : Blo 1293965 2186203 := bstep (se 1 (by rfl) ⟨1639652, by rfl⟩ : syracuseStep 2186203 = 3279305) B3279305
theorem B9829349 : Blo 1293965 9829349 := bstep (se 4 (by rfl) ⟨921501, by rfl⟩ : syracuseStep 9829349 = 1843003) B1843003
theorem B9837611 : Blo 1293965 9837611 := bstep (se 1 (by rfl) ⟨7378208, by rfl⟩ : syracuseStep 9837611 = 14756417) B14756417
theorem B1457275 : Blo 1293965 1457275 := bstep (se 1 (by rfl) ⟨1092956, by rfl⟩ : syracuseStep 1457275 = 2185913) B2185913
theorem B4373675 : Blo 1293965 4373675 := bstep (se 1 (by rfl) ⟨3280256, by rfl⟩ : syracuseStep 4373675 = 6560513) B6560513
theorem B4914371 : Blo 1293965 4914371 := bstep (se 1 (by rfl) ⟨3685778, by rfl⟩ : syracuseStep 4914371 = 7371557) B7371557
theorem B2456905 : Blo 1293965 2456905 := bstep (se 2 (by rfl) ⟨921339, by rfl⟩ : syracuseStep 2456905 = 1842679) B1842679
theorem B6733181 : Blo 1293965 6733181 := bstep (se 3 (by rfl) ⟨1262471, by rfl⟩ : syracuseStep 6733181 = 2524943) B2524943
theorem B5250433 : Blo 1293965 5250433 := bstep (se 2 (by rfl) ⟨1968912, by rfl⟩ : syracuseStep 5250433 = 3937825) B3937825
theorem B1637815 : Blo 1293965 1637815 := bstep (se 1 (by rfl) ⟨1228361, by rfl⟩ : syracuseStep 1637815 = 2456723) B2456723
theorem B1941071 : Blo 1293965 1941071 := bstep (se 1 (by rfl) ⟨1455803, by rfl⟩ : syracuseStep 1941071 = 2911607) B2911607
theorem B1457743 : Blo 1293965 1457743 := bstep (se 1 (by rfl) ⟨1093307, by rfl⟩ : syracuseStep 1457743 = 2186615) B2186615
theorem B2186831 : Blo 1293965 2186831 := bstep (se 1 (by rfl) ⟨1640123, by rfl⟩ : syracuseStep 2186831 = 3280247) B3280247
theorem B4914827 : Blo 1293965 4914827 := bstep (se 1 (by rfl) ⟨3686120, by rfl⟩ : syracuseStep 4914827 = 7372241) B7372241
theorem B5250707 : Blo 1293965 5250707 := bstep (se 1 (by rfl) ⟨3938030, by rfl⟩ : syracuseStep 5250707 = 7876061) B7876061
theorem B1293999 : Blo 1293965 1293999 := bstep (se 1 (by rfl) ⟨970499, by rfl⟩ : syracuseStep 1293999 = 1940999) B1940999
theorem B1294023 : Blo 1293965 1294023 := bstep (se 1 (by rfl) ⟨970517, by rfl⟩ : syracuseStep 1294023 = 1941035) B1941035
theorem B1941191 : Blo 1293965 1941191 := bstep (se 1 (by rfl) ⟨1455893, by rfl⟩ : syracuseStep 1941191 = 2911787) B2911787
theorem B3686087 : Blo 1293965 3686087 := bstep (se 1 (by rfl) ⟨2764565, by rfl⟩ : syracuseStep 3686087 = 5529131) B5529131
theorem B4669127 : Blo 1293965 4669127 := bstep (se 1 (by rfl) ⟨3501845, by rfl⟩ : syracuseStep 4669127 = 7003691) B7003691
theorem B4669139 : Blo 1293965 4669139 := bstep (se 1 (by rfl) ⟨3501854, by rfl⟩ : syracuseStep 4669139 = 7003709) B7003709
theorem B1294043 : Blo 1293965 1294043 := bstep (se 1 (by rfl) ⟨970532, by rfl⟩ : syracuseStep 1294043 = 1941065) B1941065
theorem B14753501 : Blo 1293965 14753501 := bstep (se 3 (by rfl) ⟨2766281, by rfl⟩ : syracuseStep 14753501 = 5532563) B5532563
theorem B1294119 : Blo 1293965 1294119 := bstep (se 1 (by rfl) ⟨970589, by rfl⟩ : syracuseStep 1294119 = 1941179) B1941179
theorem B1294159 : Blo 1293965 1294159 := bstep (se 1 (by rfl) ⟨970619, by rfl⟩ : syracuseStep 1294159 = 1941239) B1941239
theorem B1294175 : Blo 1293965 1294175 := bstep (se 1 (by rfl) ⟨970631, by rfl⟩ : syracuseStep 1294175 = 1941263) B1941263
theorem B4915039 : Blo 1293965 4915039 := bstep (se 1 (by rfl) ⟨3686279, by rfl⟩ : syracuseStep 4915039 = 7372559) B7372559
theorem B1941353 : Blo 1293965 1941353 := bstep (se 2 (by rfl) ⟨728007, by rfl⟩ : syracuseStep 1941353 = 1456015) B1456015
theorem B1294203 : Blo 1293965 1294203 := bstep (se 1 (by rfl) ⟨970652, by rfl⟩ : syracuseStep 1294203 = 1941305) B1941305
theorem B1294255 : Blo 1293965 1294255 := bstep (se 1 (by rfl) ⟨970691, by rfl⟩ : syracuseStep 1294255 = 1941383) B1941383
theorem B1941431 : Blo 1293965 1941431 := bstep (se 1 (by rfl) ⟨1456073, by rfl⟩ : syracuseStep 1941431 = 2912147) B2912147
theorem B24903611 : Blo 1293965 24903611 := bstep (se 1 (by rfl) ⟨18677708, by rfl⟩ : syracuseStep 24903611 = 37355417) B37355417
theorem B1294279 : Blo 1293965 1294279 := bstep (se 1 (by rfl) ⟨970709, by rfl⟩ : syracuseStep 1294279 = 1941419) B1941419
theorem B1294299 : Blo 1293965 1294299 := bstep (se 1 (by rfl) ⟨970724, by rfl⟩ : syracuseStep 1294299 = 1941449) B1941449
theorem B1941467 : Blo 1293965 1941467 := bstep (se 1 (by rfl) ⟨1456100, by rfl⟩ : syracuseStep 1941467 = 2912201) B2912201
theorem B6225979 : Blo 1293965 6225979 := bstep (se 1 (by rfl) ⟨4669484, by rfl⟩ : syracuseStep 6225979 = 9338969) B9338969
theorem B23642189 : Blo 1293965 23642189 := bstep (se 3 (by rfl) ⟨4432910, by rfl⟩ : syracuseStep 23642189 = 8865821) B8865821
theorem B3547265 : Blo 1293965 3547265 := bstep (se 2 (by rfl) ⟨1330224, by rfl⟩ : syracuseStep 3547265 = 2660449) B2660449
theorem B1294623 : Blo 1293965 1294623 := bstep (se 1 (by rfl) ⟨970967, by rfl⟩ : syracuseStep 1294623 = 1941935) B1941935
theorem B1941851 : Blo 1293965 1941851 := bstep (se 1 (by rfl) ⟨1456388, by rfl⟩ : syracuseStep 1941851 = 2912777) B2912777
theorem B1294683 : Blo 1293965 1294683 := bstep (se 1 (by rfl) ⟨971012, by rfl⟩ : syracuseStep 1294683 = 1942025) B1942025
theorem B1294703 : Blo 1293965 1294703 := bstep (se 1 (by rfl) ⟨971027, by rfl⟩ : syracuseStep 1294703 = 1942055) B1942055
theorem B1294759 : Blo 1293965 1294759 := bstep (se 1 (by rfl) ⟨971069, by rfl⟩ : syracuseStep 1294759 = 1942139) B1942139
theorem B27984305 : Blo 1293965 27984305 := bstep (se 2 (by rfl) ⟨10494114, by rfl⟩ : syracuseStep 27984305 = 20988229) B20988229
theorem B1294843 : Blo 1293965 1294843 := bstep (se 1 (by rfl) ⟨971132, by rfl⟩ : syracuseStep 1294843 = 1942265) B1942265
theorem B3277331 : Blo 1293965 3277331 := bstep (se 1 (by rfl) ⟨2457998, by rfl⟩ : syracuseStep 3277331 = 4915997) B4915997
theorem B3113491 : Blo 1293965 3113491 := bstep (se 1 (by rfl) ⟨2335118, by rfl⟩ : syracuseStep 3113491 = 4670237) B4670237
theorem B6218291 : Blo 1293965 6218291 := bstep (se 1 (by rfl) ⟨4663718, by rfl⟩ : syracuseStep 6218291 = 9327437) B9327437
theorem B1942079 : Blo 1293965 1942079 := bstep (se 1 (by rfl) ⟨1456559, by rfl⟩ : syracuseStep 1942079 = 2913119) B2913119
theorem B1294911 : Blo 1293965 1294911 := bstep (se 1 (by rfl) ⟨971183, by rfl⟩ : syracuseStep 1294911 = 1942367) B1942367
theorem B1294919 : Blo 1293965 1294919 := bstep (se 1 (by rfl) ⟨971189, by rfl⟩ : syracuseStep 1294919 = 1942379) B1942379
theorem B2073271 : Blo 1293965 2073271 := bstep (se 1 (by rfl) ⟨1554953, by rfl⟩ : syracuseStep 2073271 = 3109907) B3109907
theorem B1942199 : Blo 1293965 1942199 := bstep (se 1 (by rfl) ⟨1456649, by rfl⟩ : syracuseStep 1942199 = 2913299) B2913299
theorem B1295071 : Blo 1293965 1295071 := bstep (se 1 (by rfl) ⟨971303, by rfl⟩ : syracuseStep 1295071 = 1942607) B1942607
theorem B1295151 : Blo 1293965 1295151 := bstep (se 1 (by rfl) ⟨971363, by rfl⟩ : syracuseStep 1295151 = 1942727) B1942727
theorem B1942427 : Blo 1293965 1942427 := bstep (se 1 (by rfl) ⟨1456820, by rfl⟩ : syracuseStep 1942427 = 2913641) B2913641
theorem B1295259 : Blo 1293965 1295259 := bstep (se 1 (by rfl) ⟨971444, by rfl⟩ : syracuseStep 1295259 = 1942889) B1942889
theorem B9839555 : Blo 1293965 9839555 := bstep (se 1 (by rfl) ⟨7379666, by rfl⟩ : syracuseStep 9839555 = 14759333) B14759333
theorem B1295311 : Blo 1293965 1295311 := bstep (se 1 (by rfl) ⟨971483, by rfl⟩ : syracuseStep 1295311 = 1942967) B1942967
theorem B1295335 : Blo 1293965 1295335 := bstep (se 1 (by rfl) ⟨971501, by rfl⟩ : syracuseStep 1295335 = 1943003) B1943003
theorem B6554681 : Blo 1293965 6554681 := bstep (se 2 (by rfl) ⟨2458005, by rfl⟩ : syracuseStep 6554681 = 4916011) B4916011
theorem B23635115 : Blo 1293965 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B11068649 : Blo 1293965 11068649 := bstep (se 2 (by rfl) ⟨4150743, by rfl⟩ : syracuseStep 11068649 = 8301487) B8301487
theorem B25216271 : Blo 1293965 25216271 := bstep (se 1 (by rfl) ⟨18912203, by rfl⟩ : syracuseStep 25216271 = 37824407) B37824407
theorem B1295647 : Blo 1293965 1295647 := bstep (se 1 (by rfl) ⟨971735, by rfl⟩ : syracuseStep 1295647 = 1943471) B1943471
theorem B3499303 : Blo 1293965 3499303 := bstep (se 1 (by rfl) ⟨2624477, by rfl⟩ : syracuseStep 3499303 = 5248955) B5248955
theorem B1942823 : Blo 1293965 1942823 := bstep (se 1 (by rfl) ⟨1457117, by rfl⟩ : syracuseStep 1942823 = 2914235) B2914235
theorem B7005527 : Blo 1293965 7005527 := bstep (se 1 (by rfl) ⟨5254145, by rfl⟩ : syracuseStep 7005527 = 10508291) B10508291
theorem B1295707 : Blo 1293965 1295707 := bstep (se 1 (by rfl) ⟨971780, by rfl⟩ : syracuseStep 1295707 = 1943561) B1943561
theorem B1295727 : Blo 1293965 1295727 := bstep (se 1 (by rfl) ⟨971795, by rfl⟩ : syracuseStep 1295727 = 1943591) B1943591
theorem B1942907 : Blo 1293965 1942907 := bstep (se 1 (by rfl) ⟨1457180, by rfl⟩ : syracuseStep 1942907 = 2914361) B2914361
theorem B1295783 : Blo 1293965 1295783 := bstep (se 1 (by rfl) ⟨971837, by rfl⟩ : syracuseStep 1295783 = 1943675) B1943675
theorem B8406461 : Blo 1293965 8406461 := bstep (se 3 (by rfl) ⟨1576211, by rfl⟩ : syracuseStep 8406461 = 3152423) B3152423
theorem B1943033 : Blo 1293965 1943033 := bstep (se 2 (by rfl) ⟨728637, by rfl⟩ : syracuseStep 1943033 = 1457275) B1457275
theorem B1295867 : Blo 1293965 1295867 := bstep (se 1 (by rfl) ⟨971900, by rfl⟩ : syracuseStep 1295867 = 1943801) B1943801
theorem B3687943 : Blo 1293965 3687943 := bstep (se 1 (by rfl) ⟨2765957, by rfl⟩ : syracuseStep 3687943 = 5531915) B5531915
theorem B1295935 : Blo 1293965 1295935 := bstep (se 1 (by rfl) ⟨971951, by rfl⟩ : syracuseStep 1295935 = 1943903) B1943903
theorem B1295943 : Blo 1293965 1295943 := bstep (se 1 (by rfl) ⟨971957, by rfl⟩ : syracuseStep 1295943 = 1943915) B1943915
theorem B1943135 : Blo 1293965 1943135 := bstep (se 1 (by rfl) ⟨1457351, by rfl⟩ : syracuseStep 1943135 = 2914703) B2914703
theorem B2459297 : Blo 1293965 2459297 := bstep (se 2 (by rfl) ⟨922236, by rfl⟩ : syracuseStep 2459297 = 1844473) B1844473
theorem B4368059 : Blo 1293965 4368059 := bstep (se 1 (by rfl) ⟨3276044, by rfl⟩ : syracuseStep 4368059 = 6552089) B6552089
theorem B1943351 : Blo 1293965 1943351 := bstep (se 1 (by rfl) ⟨1457513, by rfl⟩ : syracuseStep 1943351 = 2915027) B2915027
theorem B1943657 : Blo 1293965 1943657 := bstep (se 2 (by rfl) ⟨728871, by rfl⟩ : syracuseStep 1943657 = 1457743) B1457743
theorem B3279113 : Blo 1293965 3279113 := bstep (se 2 (by rfl) ⟨1229667, by rfl⟩ : syracuseStep 3279113 = 2459335) B2459335
theorem B6220061 : Blo 1293965 6220061 := bstep (se 3 (by rfl) ⟨1166261, by rfl⟩ : syracuseStep 6220061 = 2332523) B2332523
theorem B12446081 : Blo 1293965 12446081 := bstep (se 2 (by rfl) ⟨4667280, by rfl⟩ : syracuseStep 12446081 = 9334561) B9334561
theorem B2460071 : Blo 1293965 2460071 := bstep (se 1 (by rfl) ⟨1845053, by rfl⟩ : syracuseStep 2460071 = 3690107) B3690107
theorem B3500471 : Blo 1293965 3500471 := bstep (se 1 (by rfl) ⟨2625353, by rfl⟩ : syracuseStep 3500471 = 5250707) B5250707
theorem B2460223 : Blo 1293965 2460223 := bstep (se 1 (by rfl) ⟨1845167, by rfl⟩ : syracuseStep 2460223 = 3690335) B3690335
theorem B3279467 : Blo 1293965 3279467 := bstep (se 1 (by rfl) ⟨2459600, by rfl⟩ : syracuseStep 3279467 = 4919201) B4919201
theorem B4917955 : Blo 1293965 4917955 := bstep (se 1 (by rfl) ⟨3688466, by rfl⟩ : syracuseStep 4917955 = 7376933) B7376933
theorem B2525971 : Blo 1293965 2525971 := bstep (se 1 (by rfl) ⟨1894478, by rfl⟩ : syracuseStep 2525971 = 3788957) B3788957
theorem B4918259 : Blo 1293965 4918259 := bstep (se 1 (by rfl) ⟨3688694, by rfl⟩ : syracuseStep 4918259 = 7377389) B7377389
theorem B3689459 : Blo 1293965 3689459 := bstep (se 1 (by rfl) ⟨2767094, by rfl⟩ : syracuseStep 3689459 = 5534189) B5534189
theorem B2624503 : Blo 1293965 2624503 := bstep (se 1 (by rfl) ⟨1968377, by rfl⟩ : syracuseStep 2624503 = 3936755) B3936755
theorem B12610637 : Blo 1293965 12610637 := bstep (se 3 (by rfl) ⟨2364494, by rfl⟩ : syracuseStep 12610637 = 4728989) B4728989
theorem B16591949 : Blo 1293965 16591949 := bstep (se 3 (by rfl) ⟨3110990, by rfl⟩ : syracuseStep 16591949 = 6221981) B6221981
theorem B6556787 : Blo 1293965 6556787 := bstep (se 1 (by rfl) ⟨4917590, by rfl⟩ : syracuseStep 6556787 = 9835181) B9835181
theorem B4148347 : Blo 1293965 4148347 := bstep (se 1 (by rfl) ⟨3111260, by rfl⟩ : syracuseStep 4148347 = 6222521) B6222521
theorem B14953643 : Blo 1293965 14953643 := bstep (se 1 (by rfl) ⟨11215232, by rfl⟩ : syracuseStep 14953643 = 22430465) B22430465
theorem B3280115 : Blo 1293965 3280115 := bstep (se 1 (by rfl) ⟨2460086, by rfl⟩ : syracuseStep 3280115 = 4920173) B4920173
theorem B2911481 : Blo 1293965 2911481 := bstep (se 2 (by rfl) ⟨1091805, by rfl⟩ : syracuseStep 2911481 = 2183611) B2183611
theorem B95816981 : Blo 1293965 95816981 := bstep (se 6 (by rfl) ⟨2245710, by rfl⟩ : syracuseStep 95816981 = 4491421) B4491421
theorem B12447037 : Blo 1293965 12447037 := bstep (se 3 (by rfl) ⟨2333819, by rfl⟩ : syracuseStep 12447037 = 4667639) B4667639
theorem B13299059 : Blo 1293965 13299059 := bstep (se 1 (by rfl) ⟨9974294, by rfl⟩ : syracuseStep 13299059 = 19948589) B19948589
theorem B11054465 : Blo 1293965 11054465 := bstep (se 2 (by rfl) ⟨4145424, by rfl⟩ : syracuseStep 11054465 = 8290849) B8290849
theorem B2911625 : Blo 1293965 2911625 := bstep (se 2 (by rfl) ⟨1091859, by rfl⟩ : syracuseStep 2911625 = 2183719) B2183719
theorem B4918715 : Blo 1293965 4918715 := bstep (se 1 (by rfl) ⟨3689036, by rfl⟩ : syracuseStep 4918715 = 7378073) B7378073
theorem B14749127 : Blo 1293965 14749127 := bstep (se 1 (by rfl) ⟨11061845, by rfl⟩ : syracuseStep 14749127 = 22123691) B22123691
theorem B2911751 : Blo 1293965 2911751 := bstep (se 1 (by rfl) ⟨2183813, by rfl⟩ : syracuseStep 2911751 = 4367627) B4367627
theorem B4370003 : Blo 1293965 4370003 := bstep (se 1 (by rfl) ⟨3277502, by rfl⟩ : syracuseStep 4370003 = 6555005) B6555005
theorem B6221407 : Blo 1293965 6221407 := bstep (se 1 (by rfl) ⟨4666055, by rfl⟩ : syracuseStep 6221407 = 9332111) B9332111
theorem B18673325 : Blo 1293965 18673325 := bstep (se 3 (by rfl) ⟨3501248, by rfl⟩ : syracuseStep 18673325 = 7002497) B7002497
theorem B2911931 : Blo 1293965 2911931 := bstep (se 1 (by rfl) ⟨2183948, by rfl⟩ : syracuseStep 2911931 = 4367897) B4367897
theorem B2764523 : Blo 1293965 2764523 := bstep (se 1 (by rfl) ⟨2073392, by rfl⟩ : syracuseStep 2764523 = 4146785) B4146785
theorem B2912057 : Blo 1293965 2912057 := bstep (se 2 (by rfl) ⟨1092021, by rfl⟩ : syracuseStep 2912057 = 2184043) B2184043
theorem B6557597 : Blo 1293965 6557597 := bstep (se 3 (by rfl) ⟨1229549, by rfl⟩ : syracuseStep 6557597 = 2459099) B2459099
theorem B13463617 : Blo 1293965 13463617 := bstep (se 2 (by rfl) ⟨5048856, by rfl⟩ : syracuseStep 13463617 = 10097713) B10097713
theorem B2183591 : Blo 1293965 2183591 := bstep (se 1 (by rfl) ⟨1637693, by rfl⟩ : syracuseStep 2183591 = 3275387) B3275387
theorem B2912687 : Blo 1293965 2912687 := bstep (se 1 (by rfl) ⟨2184515, by rfl⟩ : syracuseStep 2912687 = 4369031) B4369031
theorem B5910985 : Blo 1293965 5910985 := bstep (se 2 (by rfl) ⟨2216619, by rfl⟩ : syracuseStep 5910985 = 4433239) B4433239
theorem B2912723 : Blo 1293965 2912723 := bstep (se 1 (by rfl) ⟨2184542, by rfl⟩ : syracuseStep 2912723 = 4369085) B4369085
theorem B5902811 : Blo 1293965 5902811 := bstep (se 1 (by rfl) ⟨4427108, by rfl⟩ : syracuseStep 5902811 = 8854217) B8854217
theorem B5607899 : Blo 1293965 5607899 := bstep (se 1 (by rfl) ⟨4205924, by rfl⟩ : syracuseStep 5607899 = 8411849) B8411849
theorem B7000577 : Blo 1293965 7000577 := bstep (se 2 (by rfl) ⟨2625216, by rfl⟩ : syracuseStep 7000577 = 5250433) B5250433
theorem B10646077 : Blo 1293965 10646077 := bstep (se 3 (by rfl) ⟨1996139, by rfl⟩ : syracuseStep 10646077 = 3992279) B3992279
theorem B2912831 : Blo 1293965 2912831 := bstep (se 1 (by rfl) ⟨2184623, by rfl⟩ : syracuseStep 2912831 = 4369247) B4369247
theorem B2183753 : Blo 1293965 2183753 := bstep (se 2 (by rfl) ⟨818907, by rfl⟩ : syracuseStep 2183753 = 1637815) B1637815
theorem B2912939 : Blo 1293965 2912939 := bstep (se 1 (by rfl) ⟨2184704, by rfl⟩ : syracuseStep 2912939 = 4369409) B4369409
theorem B6558407 : Blo 1293965 6558407 := bstep (se 1 (by rfl) ⟨4918805, by rfl⟩ : syracuseStep 6558407 = 9837611) B9837611
theorem B3322795 : Blo 1293965 3322795 := bstep (se 1 (by rfl) ⟨2492096, by rfl⟩ : syracuseStep 3322795 = 4984193) B4984193
theorem B3322919 : Blo 1293965 3322919 := bstep (se 1 (by rfl) ⟨2492189, by rfl⟩ : syracuseStep 3322919 = 4984379) B4984379
theorem B5248097 : Blo 1293965 5248097 := bstep (se 2 (by rfl) ⟨1968036, by rfl⟩ : syracuseStep 5248097 = 3936073) B3936073
theorem B9835667 : Blo 1293965 9835667 := bstep (se 1 (by rfl) ⟨7376750, by rfl⟩ : syracuseStep 9835667 = 14753501) B14753501
theorem B2913479 : Blo 1293965 2913479 := bstep (se 1 (by rfl) ⟨2185109, by rfl⟩ : syracuseStep 2913479 = 4370219) B4370219
theorem B16602407 : Blo 1293965 16602407 := bstep (se 1 (by rfl) ⟨12451805, by rfl⟩ : syracuseStep 16602407 = 24903611) B24903611
theorem B2913659 : Blo 1293965 2913659 := bstep (se 1 (by rfl) ⟨2185244, by rfl⟩ : syracuseStep 2913659 = 4370489) B4370489
theorem B2913785 : Blo 1293965 2913785 := bstep (se 2 (by rfl) ⟨1092669, by rfl⟩ : syracuseStep 2913785 = 2185339) B2185339
theorem B2913875 : Blo 1293965 2913875 := bstep (se 1 (by rfl) ⟨2185406, by rfl⟩ : syracuseStep 2913875 = 4370813) B4370813
theorem B2184799 : Blo 1293965 2184799 := bstep (se 1 (by rfl) ⟨1638599, by rfl⟩ : syracuseStep 2184799 = 3277199) B3277199
theorem B12441275 : Blo 1293965 12441275 := bstep (se 1 (by rfl) ⟨9330956, by rfl⟩ : syracuseStep 12441275 = 18661913) B18661913
theorem B22132439 : Blo 1293965 22132439 := bstep (se 1 (by rfl) ⟨16599329, by rfl⟩ : syracuseStep 22132439 = 33198659) B33198659
theorem B2914055 : Blo 1293965 2914055 := bstep (se 1 (by rfl) ⟨2185541, by rfl⟩ : syracuseStep 2914055 = 4371083) B4371083
theorem B11056925 : Blo 1293965 11056925 := bstep (se 3 (by rfl) ⟨2073173, by rfl⟩ : syracuseStep 11056925 = 4146347) B4146347
theorem B2185015 : Blo 1293965 2185015 := bstep (se 1 (by rfl) ⟨1638761, by rfl⟩ : syracuseStep 2185015 = 3277523) B3277523
theorem B1382351 : Blo 1293965 1382351 := bstep (se 1 (by rfl) ⟨1036763, by rfl⟩ : syracuseStep 1382351 = 2073527) B2073527
theorem B2185481 : Blo 1293965 2185481 := bstep (se 2 (by rfl) ⟨819555, by rfl⟩ : syracuseStep 2185481 = 1639111) B1639111
theorem B1554727 : Blo 1293965 1554727 := bstep (se 1 (by rfl) ⟨1166045, by rfl⟩ : syracuseStep 1554727 = 2332091) B2332091
theorem B2914667 : Blo 1293965 2914667 := bstep (se 1 (by rfl) ⟨2186000, by rfl⟩ : syracuseStep 2914667 = 4372001) B4372001
theorem B4372919 : Blo 1293965 4372919 := bstep (se 1 (by rfl) ⟨3279689, by rfl⟩ : syracuseStep 4372919 = 6559379) B6559379
theorem B2914811 : Blo 1293965 2914811 := bstep (se 1 (by rfl) ⟨2186108, by rfl⟩ : syracuseStep 2914811 = 4372217) B4372217
theorem B1456735 : Blo 1293965 1456735 := bstep (se 1 (by rfl) ⟨1092551, by rfl⟩ : syracuseStep 1456735 = 2185103) B2185103
theorem B5905003 : Blo 1293965 5905003 := bstep (se 1 (by rfl) ⟨4428752, by rfl⟩ : syracuseStep 5905003 = 8857505) B8857505
theorem B2914937 : Blo 1293965 2914937 := bstep (se 2 (by rfl) ⟨1093101, by rfl⟩ : syracuseStep 2914937 = 2186203) B2186203
theorem B2914991 : Blo 1293965 2914991 := bstep (se 1 (by rfl) ⟨2186243, by rfl⟩ : syracuseStep 2914991 = 4372487) B4372487
theorem B2915063 : Blo 1293965 2915063 := bstep (se 1 (by rfl) ⟨2186297, by rfl⟩ : syracuseStep 2915063 = 4372595) B4372595
theorem B3275599 : Blo 1293965 3275599 := bstep (se 1 (by rfl) ⟨2456699, by rfl⟩ : syracuseStep 3275599 = 4913399) B4913399
theorem B5905277 : Blo 1293965 5905277 := bstep (se 3 (by rfl) ⟨1107239, by rfl⟩ : syracuseStep 5905277 = 2214479) B2214479
theorem B3939197 : Blo 1293965 3939197 := bstep (se 3 (by rfl) ⟨738599, by rfl⟩ : syracuseStep 3939197 = 1477199) B1477199
theorem B2915243 : Blo 1293965 2915243 := bstep (se 1 (by rfl) ⟨2186432, by rfl⟩ : syracuseStep 2915243 = 4372865) B4372865
theorem B3275873 : Blo 1293965 3275873 := bstep (se 2 (by rfl) ⟨1228452, by rfl⟩ : syracuseStep 3275873 = 2456905) B2456905
theorem B42556637 : Blo 1293965 42556637 := bstep (se 3 (by rfl) ⟨7979369, by rfl⟩ : syracuseStep 42556637 = 15958739) B15958739
theorem B2186473 : Blo 1293965 2186473 := bstep (se 2 (by rfl) ⟨819927, by rfl⟩ : syracuseStep 2186473 = 1639855) B1639855
theorem B2186527 : Blo 1293965 2186527 := bstep (se 1 (by rfl) ⟨1639895, by rfl⟩ : syracuseStep 2186527 = 3279791) B3279791
theorem B6552899 : Blo 1293965 6552899 := bstep (se 1 (by rfl) ⟨4914674, by rfl⟩ : syracuseStep 6552899 = 9829349) B9829349
theorem B2915783 : Blo 1293965 2915783 := bstep (se 1 (by rfl) ⟨2186837, by rfl⟩ : syracuseStep 2915783 = 4373675) B4373675
theorem B3276247 : Blo 1293965 3276247 := bstep (se 1 (by rfl) ⟨2457185, by rfl⟩ : syracuseStep 3276247 = 4914371) B4914371
theorem B4488787 : Blo 1293965 4488787 := bstep (se 1 (by rfl) ⟨3366590, by rfl⟩ : syracuseStep 4488787 = 6733181) B6733181
theorem B2186939 : Blo 1293965 2186939 := bstep (se 1 (by rfl) ⟨1640204, by rfl⟩ : syracuseStep 2186939 = 3280409) B3280409
theorem B1294047 : Blo 1293965 1294047 := bstep (se 1 (by rfl) ⟨970535, by rfl⟩ : syracuseStep 1294047 = 1941071) B1941071
theorem B1457887 : Blo 1293965 1457887 := bstep (se 1 (by rfl) ⟨1093415, by rfl⟩ : syracuseStep 1457887 = 2186831) B2186831
theorem B1941227 : Blo 1293965 1941227 := bstep (se 1 (by rfl) ⟨1455920, by rfl⟩ : syracuseStep 1941227 = 2911841) B2911841
theorem B3276551 : Blo 1293965 3276551 := bstep (se 1 (by rfl) ⟨2457413, by rfl⟩ : syracuseStep 3276551 = 4914827) B4914827
theorem B6553385 : Blo 1293965 6553385 := bstep (se 2 (by rfl) ⟨2457519, by rfl⟩ : syracuseStep 6553385 = 4915039) B4915039
theorem B1294127 : Blo 1293965 1294127 := bstep (se 1 (by rfl) ⟨970595, by rfl⟩ : syracuseStep 1294127 = 1941191) B1941191
theorem B2457391 : Blo 1293965 2457391 := bstep (se 1 (by rfl) ⟨1843043, by rfl⟩ : syracuseStep 2457391 = 3686087) B3686087
theorem B3112751 : Blo 1293965 3112751 := bstep (se 1 (by rfl) ⟨2334563, by rfl⟩ : syracuseStep 3112751 = 4669127) B4669127
theorem B3112759 : Blo 1293965 3112759 := bstep (se 1 (by rfl) ⟨2334569, by rfl⟩ : syracuseStep 3112759 = 4669139) B4669139
theorem B3497833 : Blo 1293965 3497833 := bstep (se 2 (by rfl) ⟨1311687, by rfl⟩ : syracuseStep 3497833 = 2623375) B2623375
theorem B13999979 : Blo 1293965 13999979 := bstep (se 1 (by rfl) ⟨10499984, by rfl⟩ : syracuseStep 13999979 = 20999969) B20999969
theorem B1294235 : Blo 1293965 1294235 := bstep (se 1 (by rfl) ⟨970676, by rfl⟩ : syracuseStep 1294235 = 1941353) B1941353
theorem B1294287 : Blo 1293965 1294287 := bstep (se 1 (by rfl) ⟨970715, by rfl⟩ : syracuseStep 1294287 = 1941431) B1941431
theorem B1941455 : Blo 1293965 1941455 := bstep (se 1 (by rfl) ⟨1456091, by rfl⟩ : syracuseStep 1941455 = 2912183) B2912183
theorem B1294311 : Blo 1293965 1294311 := bstep (se 1 (by rfl) ⟨970733, by rfl⟩ : syracuseStep 1294311 = 1941467) B1941467
theorem B15761459 : Blo 1293965 15761459 := bstep (se 1 (by rfl) ⟨11821094, by rfl⟩ : syracuseStep 15761459 = 23642189) B23642189
theorem B1294567 : Blo 1293965 1294567 := bstep (se 1 (by rfl) ⟨970925, by rfl⟩ : syracuseStep 1294567 = 1941851) B1941851
theorem B1941791 : Blo 1293965 1941791 := bstep (se 1 (by rfl) ⟨1456343, by rfl⟩ : syracuseStep 1941791 = 2912687) B2912687
theorem B1941815 : Blo 1293965 1941815 := bstep (se 1 (by rfl) ⟨1456361, by rfl⟩ : syracuseStep 1941815 = 2912723) B2912723
theorem B4145527 : Blo 1293965 4145527 := bstep (se 1 (by rfl) ⟨3109145, by rfl⟩ : syracuseStep 4145527 = 6218291) B6218291
theorem B1941887 : Blo 1293965 1941887 := bstep (se 1 (by rfl) ⟨1456415, by rfl⟩ : syracuseStep 1941887 = 2912831) B2912831
theorem B1294719 : Blo 1293965 1294719 := bstep (se 1 (by rfl) ⟨971039, by rfl⟩ : syracuseStep 1294719 = 1942079) B1942079
theorem B2072969 : Blo 1293965 2072969 := bstep (se 2 (by rfl) ⟨777363, by rfl⟩ : syracuseStep 2072969 = 1554727) B1554727
theorem B1941959 : Blo 1293965 1941959 := bstep (se 1 (by rfl) ⟨1456469, by rfl⟩ : syracuseStep 1941959 = 2912939) B2912939
theorem B1294799 : Blo 1293965 1294799 := bstep (se 1 (by rfl) ⟨971099, by rfl⟩ : syracuseStep 1294799 = 1942199) B1942199
theorem B113484365 : Blo 1293965 113484365 := bstep (se 3 (by rfl) ⟨21278318, by rfl⟩ : syracuseStep 113484365 = 42556637) B42556637
theorem B7881313 : Blo 1293965 7881313 := bstep (se 2 (by rfl) ⟨2955492, by rfl⟩ : syracuseStep 7881313 = 5910985) B5910985
theorem B1294951 : Blo 1293965 1294951 := bstep (se 1 (by rfl) ⟨971213, by rfl⟩ : syracuseStep 1294951 = 1942427) B1942427
theorem B3498731 : Blo 1293965 3498731 := bstep (se 1 (by rfl) ⟨2624048, by rfl⟩ : syracuseStep 3498731 = 5248097) B5248097
theorem B1942313 : Blo 1293965 1942313 := bstep (se 2 (by rfl) ⟨728367, by rfl⟩ : syracuseStep 1942313 = 1456735) B1456735
theorem B1942319 : Blo 1293965 1942319 := bstep (se 1 (by rfl) ⟨1456739, by rfl⟩ : syracuseStep 1942319 = 2913479) B2913479
theorem B7873337 : Blo 1293965 7873337 := bstep (se 2 (by rfl) ⟨2952501, by rfl⟩ : syracuseStep 7873337 = 5905003) B5905003
theorem B16810847 : Blo 1293965 16810847 := bstep (se 1 (by rfl) ⟨12608135, by rfl⟩ : syracuseStep 16810847 = 25216271) B25216271
theorem B1295215 : Blo 1293965 1295215 := bstep (se 1 (by rfl) ⟨971411, by rfl⟩ : syracuseStep 1295215 = 1942823) B1942823
theorem B11068271 : Blo 1293965 11068271 := bstep (se 1 (by rfl) ⟨8301203, by rfl⟩ : syracuseStep 11068271 = 16602407) B16602407
theorem B4670351 : Blo 1293965 4670351 := bstep (se 1 (by rfl) ⟨3502763, by rfl⟩ : syracuseStep 4670351 = 7005527) B7005527
theorem B1942439 : Blo 1293965 1942439 := bstep (se 1 (by rfl) ⟨1456829, by rfl⟩ : syracuseStep 1942439 = 2913659) B2913659
theorem B1295271 : Blo 1293965 1295271 := bstep (se 1 (by rfl) ⟨971453, by rfl⟩ : syracuseStep 1295271 = 1942907) B1942907
theorem B1942523 : Blo 1293965 1942523 := bstep (se 1 (by rfl) ⟨1456892, by rfl⟩ : syracuseStep 1942523 = 2913785) B2913785
theorem B1295355 : Blo 1293965 1295355 := bstep (se 1 (by rfl) ⟨971516, by rfl⟩ : syracuseStep 1295355 = 1943033) B1943033
theorem B1942583 : Blo 1293965 1942583 := bstep (se 1 (by rfl) ⟨1456937, by rfl⟩ : syracuseStep 1942583 = 2913875) B2913875
theorem B1295423 : Blo 1293965 1295423 := bstep (se 1 (by rfl) ⟨971567, by rfl⟩ : syracuseStep 1295423 = 1943135) B1943135
theorem B4367465 : Blo 1293965 4367465 := bstep (se 2 (by rfl) ⟨1637799, by rfl⟩ : syracuseStep 4367465 = 3275599) B3275599
theorem B1639531 : Blo 1293965 1639531 := bstep (se 1 (by rfl) ⟨1229648, by rfl⟩ : syracuseStep 1639531 = 2459297) B2459297
theorem B14754959 : Blo 1293965 14754959 := bstep (se 1 (by rfl) ⟨11066219, by rfl⟩ : syracuseStep 14754959 = 22132439) B22132439
theorem B1942703 : Blo 1293965 1942703 := bstep (se 1 (by rfl) ⟨1457027, by rfl⟩ : syracuseStep 1942703 = 2914055) B2914055
theorem B1295567 : Blo 1293965 1295567 := bstep (se 1 (by rfl) ⟨971675, by rfl⟩ : syracuseStep 1295567 = 1943351) B1943351
theorem B42018101 : Blo 1293965 42018101 := bstep (se 5 (by rfl) ⟨1969598, by rfl⟩ : syracuseStep 42018101 = 3939197) B3939197
theorem B3499337 : Blo 1293965 3499337 := bstep (se 2 (by rfl) ⟨1312251, by rfl⟩ : syracuseStep 3499337 = 2624503) B2624503
theorem B1295771 : Blo 1293965 1295771 := bstep (se 1 (by rfl) ⟨971828, by rfl⟩ : syracuseStep 1295771 = 1943657) B1943657
theorem B5531129 : Blo 1293965 5531129 := bstep (se 2 (by rfl) ⟨2074173, by rfl⟩ : syracuseStep 5531129 = 4148347) B4148347
theorem B4146707 : Blo 1293965 4146707 := bstep (se 1 (by rfl) ⟨3110030, by rfl⟩ : syracuseStep 4146707 = 6220061) B6220061
theorem B1943111 : Blo 1293965 1943111 := bstep (se 1 (by rfl) ⟨1457333, by rfl⟩ : syracuseStep 1943111 = 2914667) B2914667
theorem B215549525 : Blo 1293965 215549525 := bstep (se 8 (by rfl) ⟨1262985, by rfl⟩ : syracuseStep 215549525 = 2525971) B2525971
theorem B1943207 : Blo 1293965 1943207 := bstep (se 1 (by rfl) ⟨1457405, by rfl⟩ : syracuseStep 1943207 = 2914811) B2914811
theorem B1943291 : Blo 1293965 1943291 := bstep (se 1 (by rfl) ⟨1457468, by rfl⟩ : syracuseStep 1943291 = 2914937) B2914937
theorem B1943327 : Blo 1293965 1943327 := bstep (se 1 (by rfl) ⟨1457495, by rfl⟩ : syracuseStep 1943327 = 2914991) B2914991
theorem B1943375 : Blo 1293965 1943375 := bstep (se 1 (by rfl) ⟨1457531, by rfl⟩ : syracuseStep 1943375 = 2915063) B2915063
theorem B18655109 : Blo 1293965 18655109 := bstep (se 4 (by rfl) ⟨1748916, by rfl⟩ : syracuseStep 18655109 = 3497833) B3497833
theorem B1943495 : Blo 1293965 1943495 := bstep (se 1 (by rfl) ⟨1457621, by rfl⟩ : syracuseStep 1943495 = 2915243) B2915243
theorem B4368329 : Blo 1293965 4368329 := bstep (se 2 (by rfl) ⟨1638123, by rfl⟩ : syracuseStep 4368329 = 3276247) B3276247
theorem B3278839 : Blo 1293965 3278839 := bstep (se 1 (by rfl) ⟨2459129, by rfl⟩ : syracuseStep 3278839 = 4918259) B4918259
theorem B2459639 : Blo 1293965 2459639 := bstep (se 1 (by rfl) ⟨1844729, by rfl⟩ : syracuseStep 2459639 = 3689459) B3689459
theorem B4917257 : Blo 1293965 4917257 := bstep (se 2 (by rfl) ⟨1843971, by rfl⟩ : syracuseStep 4917257 = 3687943) B3687943
theorem B8407091 : Blo 1293965 8407091 := bstep (se 1 (by rfl) ⟨6305318, by rfl⟩ : syracuseStep 8407091 = 12610637) B12610637
theorem B11061299 : Blo 1293965 11061299 := bstep (se 1 (by rfl) ⟨8295974, by rfl⟩ : syracuseStep 11061299 = 16591949) B16591949
theorem B4368599 : Blo 1293965 4368599 := bstep (se 1 (by rfl) ⟨3276449, by rfl⟩ : syracuseStep 4368599 = 6552899) B6552899
theorem B8866039 : Blo 1293965 8866039 := bstep (se 1 (by rfl) ⟨6649529, by rfl⟩ : syracuseStep 8866039 = 13299059) B13299059
theorem B3279143 : Blo 1293965 3279143 := bstep (se 1 (by rfl) ⟨2459357, by rfl⟩ : syracuseStep 3279143 = 4918715) B4918715
theorem B1943849 : Blo 1293965 1943849 := bstep (se 2 (by rfl) ⟨728943, by rfl⟩ : syracuseStep 1943849 = 1457887) B1457887
theorem B9832751 : Blo 1293965 9832751 := bstep (se 1 (by rfl) ⟨7374563, by rfl⟩ : syracuseStep 9832751 = 14749127) B14749127
theorem B1943855 : Blo 1293965 1943855 := bstep (se 1 (by rfl) ⟨1457891, by rfl⟩ : syracuseStep 1943855 = 2915783) B2915783
theorem B4368923 : Blo 1293965 4368923 := bstep (se 1 (by rfl) ⟨3276692, by rfl⟩ : syracuseStep 4368923 = 6553385) B6553385
theorem B2075167 : Blo 1293965 2075167 := bstep (se 1 (by rfl) ⟨1556375, by rfl⟩ : syracuseStep 2075167 = 3112751) B3112751
theorem B9333319 : Blo 1293965 9333319 := bstep (se 1 (by rfl) ⟨6999989, by rfl⟩ : syracuseStep 9333319 = 13999979) B13999979
theorem B8301305 : Blo 1293965 8301305 := bstep (se 2 (by rfl) ⟨3112989, by rfl⟩ : syracuseStep 8301305 = 6225979) B6225979
theorem B17951489 : Blo 1293965 17951489 := bstep (se 2 (by rfl) ⟨6731808, by rfl⟩ : syracuseStep 17951489 = 13463617) B13463617
theorem B18656203 : Blo 1293965 18656203 := bstep (se 1 (by rfl) ⟨13992152, by rfl⟩ : syracuseStep 18656203 = 27984305) B27984305
theorem B3935207 : Blo 1293965 3935207 := bstep (se 1 (by rfl) ⟨2951405, by rfl⟩ : syracuseStep 3935207 = 5902811) B5902811
theorem B3738599 : Blo 1293965 3738599 := bstep (se 1 (by rfl) ⟨2803949, by rfl⟩ : syracuseStep 3738599 = 5607899) B5607899
theorem B2215279 : Blo 1293965 2215279 := bstep (se 1 (by rfl) ⟨1661459, by rfl⟩ : syracuseStep 2215279 = 3322919) B3322919
theorem B4369787 : Blo 1293965 4369787 := bstep (se 1 (by rfl) ⟨3277340, by rfl⟩ : syracuseStep 4369787 = 6554681) B6554681
theorem B3280297 : Blo 1293965 3280297 := bstep (se 2 (by rfl) ⟨1230111, by rfl⟩ : syracuseStep 3280297 = 2460223) B2460223
theorem B6557111 : Blo 1293965 6557111 := bstep (se 1 (by rfl) ⟨4917833, by rfl⟩ : syracuseStep 6557111 = 9835667) B9835667
theorem B15756743 : Blo 1293965 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B2764361 : Blo 1293965 2764361 := bstep (se 2 (by rfl) ⟨1036635, by rfl⟩ : syracuseStep 2764361 = 2073271) B2073271
theorem B6557273 : Blo 1293965 6557273 := bstep (se 2 (by rfl) ⟨2458977, by rfl⟩ : syracuseStep 6557273 = 4917955) B4917955
theorem B8294183 : Blo 1293965 8294183 := bstep (se 1 (by rfl) ⟨6220637, by rfl⟩ : syracuseStep 8294183 = 12441275) B12441275
theorem B2912039 : Blo 1293965 2912039 := bstep (se 1 (by rfl) ⟨2184029, by rfl⟩ : syracuseStep 2912039 = 4368059) B4368059
theorem B22417229 : Blo 1293965 22417229 := bstep (se 3 (by rfl) ⟨4203230, by rfl⟩ : syracuseStep 22417229 = 8406461) B8406461
theorem B16601381 : Blo 1293965 16601381 := bstep (se 4 (by rfl) ⟨1556379, by rfl⟩ : syracuseStep 16601381 = 3112759) B3112759
theorem B4665737 : Blo 1293965 4665737 := bstep (se 2 (by rfl) ⟨1749651, by rfl⟩ : syracuseStep 4665737 = 3499303) B3499303
theorem B3936851 : Blo 1293965 3936851 := bstep (se 1 (by rfl) ⟨2952638, by rfl⟩ : syracuseStep 3936851 = 5905277) B5905277
theorem B2183915 : Blo 1293965 2183915 := bstep (se 1 (by rfl) ⟨1637936, by rfl⟩ : syracuseStep 2183915 = 3275873) B3275873
theorem B4371191 : Blo 1293965 4371191 := bstep (se 1 (by rfl) ⟨3278393, by rfl⟩ : syracuseStep 4371191 = 6556787) B6556787
theorem B5985049 : Blo 1293965 5985049 := bstep (se 2 (by rfl) ⟨2244393, by rfl⟩ : syracuseStep 5985049 = 4488787) B4488787
theorem B8295209 : Blo 1293965 8295209 := bstep (se 2 (by rfl) ⟨3110703, by rfl⟩ : syracuseStep 8295209 = 6221407) B6221407
theorem B2913065 : Blo 1293965 2913065 := bstep (se 2 (by rfl) ⟨1092399, by rfl⟩ : syracuseStep 2913065 = 2184799) B2184799
theorem B63877987 : Blo 1293965 63877987 := bstep (se 1 (by rfl) ⟨47908490, by rfl⟩ : syracuseStep 63877987 = 95816981) B95816981
theorem B7369643 : Blo 1293965 7369643 := bstep (se 1 (by rfl) ⟨5527232, by rfl⟩ : syracuseStep 7369643 = 11054465) B11054465
theorem B2913335 : Blo 1293965 2913335 := bstep (se 1 (by rfl) ⟨2185001, by rfl⟩ : syracuseStep 2913335 = 4370003) B4370003
theorem B2913353 : Blo 1293965 2913353 := bstep (se 2 (by rfl) ⟨1092507, by rfl⟩ : syracuseStep 2913353 = 2185015) B2185015
theorem B12448883 : Blo 1293965 12448883 := bstep (se 1 (by rfl) ⟨9336662, by rfl⟩ : syracuseStep 12448883 = 18673325) B18673325
theorem B2184367 : Blo 1293965 2184367 := bstep (se 1 (by rfl) ⟨1638275, by rfl⟩ : syracuseStep 2184367 = 3276551) B3276551
theorem B4371731 : Blo 1293965 4371731 := bstep (se 1 (by rfl) ⟨3278798, by rfl⟩ : syracuseStep 4371731 = 6557597) B6557597
theorem B1455727 : Blo 1293965 1455727 := bstep (se 1 (by rfl) ⟨1091795, by rfl⟩ : syracuseStep 1455727 = 2183591) B2183591
theorem B4667051 : Blo 1293965 4667051 := bstep (se 1 (by rfl) ⟨3500288, by rfl⟩ : syracuseStep 4667051 = 7000577) B7000577
theorem B2184887 : Blo 1293965 2184887 := bstep (se 1 (by rfl) ⟨1638665, by rfl⟩ : syracuseStep 2184887 = 3277331) B3277331
theorem B1455835 : Blo 1293965 1455835 := bstep (se 1 (by rfl) ⟨1091876, by rfl⟩ : syracuseStep 1455835 = 2183753) B2183753
theorem B4372271 : Blo 1293965 4372271 := bstep (se 1 (by rfl) ⟨3279203, by rfl⟩ : syracuseStep 4372271 = 6558407) B6558407
theorem B6559703 : Blo 1293965 6559703 := bstep (se 1 (by rfl) ⟨4919777, by rfl⟩ : syracuseStep 6559703 = 9839555) B9839555
theorem B4151321 : Blo 1293965 4151321 := bstep (se 2 (by rfl) ⟨1556745, by rfl⟩ : syracuseStep 4151321 = 3113491) B3113491
theorem B14194769 : Blo 1293965 14194769 := bstep (se 2 (by rfl) ⟨5323038, by rfl⟩ : syracuseStep 14194769 = 10646077) B10646077
theorem B7379099 : Blo 1293965 7379099 := bstep (se 1 (by rfl) ⟨5534324, by rfl⟩ : syracuseStep 7379099 = 11068649) B11068649
theorem B6560189 : Blo 1293965 6560189 := bstep (se 3 (by rfl) ⟨1230035, by rfl⟩ : syracuseStep 6560189 = 2460071) B2460071
theorem B7371283 : Blo 1293965 7371283 := bstep (se 1 (by rfl) ⟨5528462, by rfl⟩ : syracuseStep 7371283 = 11056925) B11056925
theorem B4430393 : Blo 1293965 4430393 := bstep (se 2 (by rfl) ⟨1661397, by rfl⟩ : syracuseStep 4430393 = 3322795) B3322795
theorem B37837493 : Blo 1293965 37837493 := bstep (se 5 (by rfl) ⟨1773632, by rfl⟩ : syracuseStep 37837493 = 3547265) B3547265
theorem B1456987 : Blo 1293965 1456987 := bstep (se 1 (by rfl) ⟨1092740, by rfl⟩ : syracuseStep 1456987 = 2185481) B2185481
theorem B2186075 : Blo 1293965 2186075 := bstep (se 1 (by rfl) ⟨1639556, by rfl⟩ : syracuseStep 2186075 = 3279113) B3279113
theorem B8297387 : Blo 1293965 8297387 := bstep (se 1 (by rfl) ⟨6223040, by rfl⟩ : syracuseStep 8297387 = 12446081) B12446081
theorem B2333647 : Blo 1293965 2333647 := bstep (se 1 (by rfl) ⟨1750235, by rfl⟩ : syracuseStep 2333647 = 3500471) B3500471
theorem B2915279 : Blo 1293965 2915279 := bstep (se 1 (by rfl) ⟨2186459, by rfl⟩ : syracuseStep 2915279 = 4372919) B4372919
theorem B2915297 : Blo 1293965 2915297 := bstep (se 2 (by rfl) ⟨1093236, by rfl⟩ : syracuseStep 2915297 = 2186473) B2186473
theorem B2915369 : Blo 1293965 2915369 := bstep (se 2 (by rfl) ⟨1093263, by rfl⟩ : syracuseStep 2915369 = 2186527) B2186527
theorem B2186311 : Blo 1293965 2186311 := bstep (se 1 (by rfl) ⟨1639733, by rfl⟩ : syracuseStep 2186311 = 3279467) B3279467
theorem B16596049 : Blo 1293965 16596049 := bstep (se 2 (by rfl) ⟨6223518, by rfl⟩ : syracuseStep 16596049 = 12447037) B12447037
theorem B9969095 : Blo 1293965 9969095 := bstep (se 1 (by rfl) ⟨7476821, by rfl⟩ : syracuseStep 9969095 = 14953643) B14953643
theorem B2186743 : Blo 1293965 2186743 := bstep (se 1 (by rfl) ⟨1640057, by rfl⟩ : syracuseStep 2186743 = 3280115) B3280115
theorem B1940987 : Blo 1293965 1940987 := bstep (se 1 (by rfl) ⟨1455740, by rfl⟩ : syracuseStep 1940987 = 2911481) B2911481
theorem B1941083 : Blo 1293965 1941083 := bstep (se 1 (by rfl) ⟨1455812, by rfl⟩ : syracuseStep 1941083 = 2911625) B2911625
theorem B1941167 : Blo 1293965 1941167 := bstep (se 1 (by rfl) ⟨1455875, by rfl⟩ : syracuseStep 1941167 = 2911751) B2911751
theorem B3276521 : Blo 1293965 3276521 := bstep (se 2 (by rfl) ⟨1228695, by rfl⟩ : syracuseStep 3276521 = 2457391) B2457391
theorem B1941287 : Blo 1293965 1941287 := bstep (se 1 (by rfl) ⟨1455965, by rfl⟩ : syracuseStep 1941287 = 2911931) B2911931
theorem B1457959 : Blo 1293965 1457959 := bstep (se 1 (by rfl) ⟨1093469, by rfl⟩ : syracuseStep 1457959 = 2186939) B2186939
theorem B1843015 : Blo 1293965 1843015 := bstep (se 1 (by rfl) ⟨1382261, by rfl⟩ : syracuseStep 1843015 = 2764523) B2764523
theorem B1294151 : Blo 1293965 1294151 := bstep (se 1 (by rfl) ⟨970613, by rfl⟩ : syracuseStep 1294151 = 1941227) B1941227
theorem B1941371 : Blo 1293965 1941371 := bstep (se 1 (by rfl) ⟨1456028, by rfl⟩ : syracuseStep 1941371 = 2912057) B2912057
theorem B3686269 : Blo 1293965 3686269 := bstep (se 3 (by rfl) ⟨691175, by rfl⟩ : syracuseStep 3686269 = 1382351) B1382351
theorem B1294303 : Blo 1293965 1294303 := bstep (se 1 (by rfl) ⟨970727, by rfl⟩ : syracuseStep 1294303 = 1941455) B1941455
theorem B1294527 : Blo 1293965 1294527 := bstep (se 1 (by rfl) ⟨970895, by rfl⟩ : syracuseStep 1294527 = 1941791) B1941791
theorem B11067587 : Blo 1293965 11067587 := bstep (se 1 (by rfl) ⟨8300690, by rfl⟩ : syracuseStep 11067587 = 16601381) B16601381
theorem B1294543 : Blo 1293965 1294543 := bstep (se 1 (by rfl) ⟨970907, by rfl⟩ : syracuseStep 1294543 = 1941815) B1941815
theorem B1294591 : Blo 1293965 1294591 := bstep (se 1 (by rfl) ⟨970943, by rfl⟩ : syracuseStep 1294591 = 1941887) B1941887
theorem B1294639 : Blo 1293965 1294639 := bstep (se 1 (by rfl) ⟨970979, by rfl⟩ : syracuseStep 1294639 = 1941959) B1941959
theorem B11821385 : Blo 1293965 11821385 := bstep (se 2 (by rfl) ⟨4433019, by rfl⟩ : syracuseStep 11821385 = 8866039) B8866039
theorem B5530139 : Blo 1293965 5530139 := bstep (se 1 (by rfl) ⟨4147604, by rfl⟩ : syracuseStep 5530139 = 8295209) B8295209
theorem B1942043 : Blo 1293965 1942043 := bstep (se 1 (by rfl) ⟨1456532, by rfl⟩ : syracuseStep 1942043 = 2913065) B2913065
theorem B1294875 : Blo 1293965 1294875 := bstep (se 1 (by rfl) ⟨971156, by rfl⟩ : syracuseStep 1294875 = 1942313) B1942313
theorem B1294879 : Blo 1293965 1294879 := bstep (se 1 (by rfl) ⟨971159, by rfl⟩ : syracuseStep 1294879 = 1942319) B1942319
theorem B11207231 : Blo 1293965 11207231 := bstep (se 1 (by rfl) ⟨8405423, by rfl⟩ : syracuseStep 11207231 = 16810847) B16810847
theorem B3113567 : Blo 1293965 3113567 := bstep (se 1 (by rfl) ⟨2335175, by rfl⟩ : syracuseStep 3113567 = 4670351) B4670351
theorem B1294959 : Blo 1293965 1294959 := bstep (se 1 (by rfl) ⟨971219, by rfl⟩ : syracuseStep 1294959 = 1942439) B1942439
theorem B1295015 : Blo 1293965 1295015 := bstep (se 1 (by rfl) ⟨971261, by rfl⟩ : syracuseStep 1295015 = 1942523) B1942523
theorem B1942223 : Blo 1293965 1942223 := bstep (se 1 (by rfl) ⟨1456667, by rfl⟩ : syracuseStep 1942223 = 2913335) B2913335
theorem B1295055 : Blo 1293965 1295055 := bstep (se 1 (by rfl) ⟨971291, by rfl⟩ : syracuseStep 1295055 = 1942583) B1942583
theorem B1942235 : Blo 1293965 1942235 := bstep (se 1 (by rfl) ⟨1456676, by rfl⟩ : syracuseStep 1942235 = 2913353) B2913353
theorem B8299255 : Blo 1293965 8299255 := bstep (se 1 (by rfl) ⟨6224441, by rfl⟩ : syracuseStep 8299255 = 12448883) B12448883
theorem B12444425 : Blo 1293965 12444425 := bstep (se 2 (by rfl) ⟨4666659, by rfl⟩ : syracuseStep 12444425 = 9333319) B9333319
theorem B1295135 : Blo 1293965 1295135 := bstep (se 1 (by rfl) ⟨971351, by rfl⟩ : syracuseStep 1295135 = 1942703) B1942703
theorem B3687419 : Blo 1293965 3687419 := bstep (se 1 (by rfl) ⟨2765564, by rfl⟩ : syracuseStep 3687419 = 5531129) B5531129
theorem B7980065 : Blo 1293965 7980065 := bstep (se 2 (by rfl) ⟨2992524, by rfl⟩ : syracuseStep 7980065 = 5985049) B5985049
theorem B1295407 : Blo 1293965 1295407 := bstep (se 1 (by rfl) ⟨971555, by rfl⟩ : syracuseStep 1295407 = 1943111) B1943111
theorem B1295471 : Blo 1293965 1295471 := bstep (se 1 (by rfl) ⟨971603, by rfl⟩ : syracuseStep 1295471 = 1943207) B1943207
theorem B1942649 : Blo 1293965 1942649 := bstep (se 2 (by rfl) ⟨728493, by rfl⟩ : syracuseStep 1942649 = 1456987) B1456987
theorem B1295527 : Blo 1293965 1295527 := bstep (se 1 (by rfl) ⟨971645, by rfl⟩ : syracuseStep 1295527 = 1943291) B1943291
theorem B1295551 : Blo 1293965 1295551 := bstep (se 1 (by rfl) ⟨971663, by rfl⟩ : syracuseStep 1295551 = 1943327) B1943327
theorem B1295583 : Blo 1293965 1295583 := bstep (se 1 (by rfl) ⟨971687, by rfl⟩ : syracuseStep 1295583 = 1943375) B1943375
theorem B12436739 : Blo 1293965 12436739 := bstep (se 1 (by rfl) ⟨9327554, by rfl⟩ : syracuseStep 12436739 = 18655109) B18655109
theorem B1295663 : Blo 1293965 1295663 := bstep (se 1 (by rfl) ⟨971747, by rfl⟩ : syracuseStep 1295663 = 1943495) B1943495
theorem B1639759 : Blo 1293965 1639759 := bstep (se 1 (by rfl) ⟨1229819, by rfl⟩ : syracuseStep 1639759 = 2459639) B2459639
theorem B3278171 : Blo 1293965 3278171 := bstep (se 1 (by rfl) ⟨2458628, by rfl⟩ : syracuseStep 3278171 = 4917257) B4917257
theorem B5604727 : Blo 1293965 5604727 := bstep (se 1 (by rfl) ⟨4203545, by rfl⟩ : syracuseStep 5604727 = 8407091) B8407091
theorem B7374199 : Blo 1293965 7374199 := bstep (se 1 (by rfl) ⟨5530649, by rfl⟩ : syracuseStep 7374199 = 11061299) B11061299
theorem B22128065 : Blo 1293965 22128065 := bstep (se 2 (by rfl) ⟨8298024, by rfl⟩ : syracuseStep 22128065 = 16596049) B16596049
theorem B1295899 : Blo 1293965 1295899 := bstep (se 1 (by rfl) ⟨971924, by rfl⟩ : syracuseStep 1295899 = 1943849) B1943849
theorem B6555167 : Blo 1293965 6555167 := bstep (se 1 (by rfl) ⟨4916375, by rfl⟩ : syracuseStep 6555167 = 9832751) B9832751
theorem B1295903 : Blo 1293965 1295903 := bstep (se 1 (by rfl) ⟨971927, by rfl⟩ : syracuseStep 1295903 = 1943855) B1943855
theorem B25224995 : Blo 1293965 25224995 := bstep (se 1 (by rfl) ⟨18918746, by rfl⟩ : syracuseStep 25224995 = 37837493) B37837493
theorem B11814821 : Blo 1293965 11814821 := bstep (se 4 (by rfl) ⟨1107639, by rfl⟩ : syracuseStep 11814821 = 2215279) B2215279
theorem B5531591 : Blo 1293965 5531591 := bstep (se 1 (by rfl) ⟨4148693, by rfl⟩ : syracuseStep 5531591 = 8297387) B8297387
theorem B1943519 : Blo 1293965 1943519 := bstep (se 1 (by rfl) ⟨1457639, by rfl⟩ : syracuseStep 1943519 = 2915279) B2915279
theorem B1943531 : Blo 1293965 1943531 := bstep (se 1 (by rfl) ⟨1457648, by rfl⟩ : syracuseStep 1943531 = 2915297) B2915297
theorem B22136813 : Blo 1293965 22136813 := bstep (se 3 (by rfl) ⟨4150652, by rfl⟩ : syracuseStep 22136813 = 8301305) B8301305
theorem B2623471 : Blo 1293965 2623471 := bstep (se 1 (by rfl) ⟨1967603, by rfl⟩ : syracuseStep 2623471 = 3935207) B3935207
theorem B2492399 : Blo 1293965 2492399 := bstep (se 1 (by rfl) ⟨1869299, by rfl⟩ : syracuseStep 2492399 = 3738599) B3738599
theorem B1943579 : Blo 1293965 1943579 := bstep (se 1 (by rfl) ⟨1457684, by rfl⟩ : syracuseStep 1943579 = 2915369) B2915369
theorem B6646063 : Blo 1293965 6646063 := bstep (se 1 (by rfl) ⟨4984547, by rfl⟩ : syracuseStep 6646063 = 9969095) B9969095
theorem B10504495 : Blo 1293965 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B1943945 : Blo 1293965 1943945 := bstep (se 2 (by rfl) ⟨728979, by rfl⟩ : syracuseStep 1943945 = 1457959) B1457959
theorem B14944819 : Blo 1293965 14944819 := bstep (se 1 (by rfl) ⟨11208614, by rfl⟩ : syracuseStep 14944819 = 22417229) B22417229
theorem B75656243 : Blo 1293965 75656243 := bstep (se 1 (by rfl) ⟨56742182, by rfl⟩ : syracuseStep 75656243 = 113484365) B113484365
theorem B2624567 : Blo 1293965 2624567 := bstep (se 1 (by rfl) ⟨1968425, by rfl⟩ : syracuseStep 2624567 = 3936851) B3936851
theorem B2911643 : Blo 1293965 2911643 := bstep (se 1 (by rfl) ⟨2183732, by rfl⟩ : syracuseStep 2911643 = 4367465) B4367465
theorem B28012067 : Blo 1293965 28012067 := bstep (se 1 (by rfl) ⟨21009050, by rfl⟩ : syracuseStep 28012067 = 42018101) B42018101
theorem B2764471 : Blo 1293965 2764471 := bstep (se 1 (by rfl) ⟨2073353, by rfl⟩ : syracuseStep 2764471 = 4146707) B4146707
theorem B143699683 : Blo 1293965 143699683 := bstep (se 1 (by rfl) ⟨107774762, by rfl⟩ : syracuseStep 143699683 = 215549525) B215549525
theorem B24874937 : Blo 1293965 24874937 := bstep (se 2 (by rfl) ⟨9328101, by rfl⟩ : syracuseStep 24874937 = 18656203) B18656203
theorem B2912219 : Blo 1293965 2912219 := bstep (se 1 (by rfl) ⟨2184164, by rfl⟩ : syracuseStep 2912219 = 4368329) B4368329
theorem B4919399 : Blo 1293965 4919399 := bstep (se 1 (by rfl) ⟨3689549, by rfl⟩ : syracuseStep 4919399 = 7379099) B7379099
theorem B2912399 : Blo 1293965 2912399 := bstep (se 1 (by rfl) ⟨2184299, by rfl⟩ : syracuseStep 2912399 = 4368599) B4368599
theorem B2912489 : Blo 1293965 2912489 := bstep (se 2 (by rfl) ⟨1092183, by rfl⟩ : syracuseStep 2912489 = 2184367) B2184367
theorem B2912615 : Blo 1293965 2912615 := bstep (se 1 (by rfl) ⟨2184461, by rfl⟩ : syracuseStep 2912615 = 4368923) B4368923
theorem B2953595 : Blo 1293965 2953595 := bstep (se 1 (by rfl) ⟨2215196, by rfl⟩ : syracuseStep 2953595 = 4430393) B4430393
theorem B2913191 : Blo 1293965 2913191 := bstep (se 1 (by rfl) ⟨2184893, by rfl⟩ : syracuseStep 2913191 = 4369787) B4369787
theorem B4371407 : Blo 1293965 4371407 := bstep (se 1 (by rfl) ⟨3278555, by rfl⟩ : syracuseStep 4371407 = 6557111) B6557111
theorem B4371515 : Blo 1293965 4371515 := bstep (se 1 (by rfl) ⟨3278636, by rfl⟩ : syracuseStep 4371515 = 6557273) B6557273
theorem B2184347 : Blo 1293965 2184347 := bstep (se 1 (by rfl) ⟨1638260, by rfl⟩ : syracuseStep 2184347 = 3276521) B3276521
theorem B4371785 : Blo 1293965 4371785 := bstep (se 2 (by rfl) ⟨1639419, by rfl⟩ : syracuseStep 4371785 = 3278839) B3278839
theorem B10507639 : Blo 1293965 10507639 := bstep (se 1 (by rfl) ⟨7880729, by rfl⟩ : syracuseStep 10507639 = 15761459) B15761459
theorem B37852717 : Blo 1293965 37852717 := bstep (se 3 (by rfl) ⟨7097384, by rfl⟩ : syracuseStep 37852717 = 14194769) B14194769
theorem B1381979 : Blo 1293965 1381979 := bstep (se 1 (by rfl) ⟨1036484, by rfl⟩ : syracuseStep 1381979 = 2072969) B2072969
theorem B3110491 : Blo 1293965 3110491 := bstep (se 1 (by rfl) ⟨2332868, by rfl⟩ : syracuseStep 3110491 = 4665737) B4665737
theorem B1455943 : Blo 1293965 1455943 := bstep (se 1 (by rfl) ⟨1091957, by rfl⟩ : syracuseStep 1455943 = 2183915) B2183915
theorem B2332487 : Blo 1293965 2332487 := bstep (se 1 (by rfl) ⟨1749365, by rfl⟩ : syracuseStep 2332487 = 3498731) B3498731
theorem B5527369 : Blo 1293965 5527369 := bstep (se 2 (by rfl) ⟨2072763, by rfl⟩ : syracuseStep 5527369 = 4145527) B4145527
theorem B2914127 : Blo 1293965 2914127 := bstep (se 1 (by rfl) ⟨2185595, by rfl⟩ : syracuseStep 2914127 = 4371191) B4371191
theorem B5248891 : Blo 1293965 5248891 := bstep (se 1 (by rfl) ⟨3936668, by rfl⟩ : syracuseStep 5248891 = 7873337) B7873337
theorem B7378847 : Blo 1293965 7378847 := bstep (se 1 (by rfl) ⟨5534135, by rfl⟩ : syracuseStep 7378847 = 11068271) B11068271
theorem B4913095 : Blo 1293965 4913095 := bstep (se 1 (by rfl) ⟨3684821, by rfl⟩ : syracuseStep 4913095 = 7369643) B7369643
theorem B9828377 : Blo 1293965 9828377 := bstep (se 2 (by rfl) ⟨3685641, by rfl⟩ : syracuseStep 9828377 = 7371283) B7371283
theorem B2766889 : Blo 1293965 2766889 := bstep (se 2 (by rfl) ⟨1037583, by rfl⟩ : syracuseStep 2766889 = 2075167) B2075167
theorem B9836639 : Blo 1293965 9836639 := bstep (se 1 (by rfl) ⟨7377479, by rfl⟩ : syracuseStep 9836639 = 14754959) B14754959
theorem B10508417 : Blo 1293965 10508417 := bstep (se 2 (by rfl) ⟨3940656, by rfl⟩ : syracuseStep 10508417 = 7881313) B7881313
theorem B2914487 : Blo 1293965 2914487 := bstep (se 1 (by rfl) ⟨2185865, by rfl⟩ : syracuseStep 2914487 = 4371731) B4371731
theorem B2332891 : Blo 1293965 2332891 := bstep (se 1 (by rfl) ⟨1749668, by rfl⟩ : syracuseStep 2332891 = 3499337) B3499337
theorem B3111367 : Blo 1293965 3111367 := bstep (se 1 (by rfl) ⟨2333525, by rfl⟩ : syracuseStep 3111367 = 4667051) B4667051
theorem B1456591 : Blo 1293965 1456591 := bstep (se 1 (by rfl) ⟨1092443, by rfl⟩ : syracuseStep 1456591 = 2184887) B2184887
theorem B85170649 : Blo 1293965 85170649 := bstep (se 2 (by rfl) ⟨31938993, by rfl⟩ : syracuseStep 85170649 = 63877987) B63877987
theorem B2914847 : Blo 1293965 2914847 := bstep (se 1 (by rfl) ⟨2186135, by rfl⟩ : syracuseStep 2914847 = 4372271) B4372271
theorem B3111529 : Blo 1293965 3111529 := bstep (se 2 (by rfl) ⟨1166823, by rfl⟩ : syracuseStep 3111529 = 2333647) B2333647
theorem B4373135 : Blo 1293965 4373135 := bstep (se 1 (by rfl) ⟨3279851, by rfl⟩ : syracuseStep 4373135 = 6559703) B6559703
theorem B2767547 : Blo 1293965 2767547 := bstep (se 1 (by rfl) ⟨2075660, by rfl⟩ : syracuseStep 2767547 = 4151321) B4151321
theorem B2915081 : Blo 1293965 2915081 := bstep (se 2 (by rfl) ⟨1093155, by rfl⟩ : syracuseStep 2915081 = 2186311) B2186311
theorem B2186041 : Blo 1293965 2186041 := bstep (se 2 (by rfl) ⟨819765, by rfl⟩ : syracuseStep 2186041 = 1639531) B1639531
theorem B2186095 : Blo 1293965 2186095 := bstep (se 1 (by rfl) ⟨1639571, by rfl⟩ : syracuseStep 2186095 = 3279143) B3279143
theorem B4373459 : Blo 1293965 4373459 := bstep (se 1 (by rfl) ⟨3280094, by rfl⟩ : syracuseStep 4373459 = 6560189) B6560189
theorem B11967659 : Blo 1293965 11967659 := bstep (se 1 (by rfl) ⟨8975744, by rfl⟩ : syracuseStep 11967659 = 17951489) B17951489
theorem B4373729 : Blo 1293965 4373729 := bstep (se 2 (by rfl) ⟨1640148, by rfl⟩ : syracuseStep 4373729 = 3280297) B3280297
theorem B1457383 : Blo 1293965 1457383 := bstep (se 1 (by rfl) ⟨1093037, by rfl⟩ : syracuseStep 1457383 = 2186075) B2186075
theorem B2915657 : Blo 1293965 2915657 := bstep (se 2 (by rfl) ⟨1093371, by rfl⟩ : syracuseStep 2915657 = 2186743) B2186743
theorem B1940969 : Blo 1293965 1940969 := bstep (se 2 (by rfl) ⟨727863, by rfl⟩ : syracuseStep 1940969 = 1455727) B1455727
theorem B1941113 : Blo 1293965 1941113 := bstep (se 2 (by rfl) ⟨727917, by rfl⟩ : syracuseStep 1941113 = 1455835) B1455835
theorem B1293991 : Blo 1293965 1293991 := bstep (se 1 (by rfl) ⟨970493, by rfl⟩ : syracuseStep 1293991 = 1940987) B1940987
theorem B1842907 : Blo 1293965 1842907 := bstep (se 1 (by rfl) ⟨1382180, by rfl⟩ : syracuseStep 1842907 = 2764361) B2764361
theorem B1294055 : Blo 1293965 1294055 := bstep (se 1 (by rfl) ⟨970541, by rfl⟩ : syracuseStep 1294055 = 1941083) B1941083
theorem B2457353 : Blo 1293965 2457353 := bstep (se 2 (by rfl) ⟨921507, by rfl⟩ : syracuseStep 2457353 = 1843015) B1843015
theorem B1294111 : Blo 1293965 1294111 := bstep (se 1 (by rfl) ⟨970583, by rfl⟩ : syracuseStep 1294111 = 1941167) B1941167
theorem B4915025 : Blo 1293965 4915025 := bstep (se 2 (by rfl) ⟨1843134, by rfl⟩ : syracuseStep 4915025 = 3686269) B3686269
theorem B1294191 : Blo 1293965 1294191 := bstep (se 1 (by rfl) ⟨970643, by rfl⟩ : syracuseStep 1294191 = 1941287) B1941287
theorem B1941359 : Blo 1293965 1941359 := bstep (se 1 (by rfl) ⟨1456019, by rfl⟩ : syracuseStep 1941359 = 2912039) B2912039
theorem B5529455 : Blo 1293965 5529455 := bstep (se 1 (by rfl) ⟨4147091, by rfl⟩ : syracuseStep 5529455 = 8294183) B8294183
theorem B1294247 : Blo 1293965 1294247 := bstep (se 1 (by rfl) ⟨970685, by rfl⟩ : syracuseStep 1294247 = 1941371) B1941371
theorem B1941599 : Blo 1293965 1941599 := bstep (se 1 (by rfl) ⟨1456199, by rfl⟩ : syracuseStep 1941599 = 2912399) B2912399
theorem B1941659 : Blo 1293965 1941659 := bstep (se 1 (by rfl) ⟨1456244, by rfl⟩ : syracuseStep 1941659 = 2912489) B2912489
theorem B7880923 : Blo 1293965 7880923 := bstep (se 1 (by rfl) ⟨5910692, by rfl⟩ : syracuseStep 7880923 = 11821385) B11821385
theorem B1941743 : Blo 1293965 1941743 := bstep (se 1 (by rfl) ⟨1456307, by rfl⟩ : syracuseStep 1941743 = 2912615) B2912615
theorem B3686759 : Blo 1293965 3686759 := bstep (se 1 (by rfl) ⟨2765069, by rfl⟩ : syracuseStep 3686759 = 5530139) B5530139
theorem B1294695 : Blo 1293965 1294695 := bstep (se 1 (by rfl) ⟨971021, by rfl⟩ : syracuseStep 1294695 = 1942043) B1942043
theorem B7471487 : Blo 1293965 7471487 := bstep (se 1 (by rfl) ⟨5603615, by rfl⟩ : syracuseStep 7471487 = 11207231) B11207231
theorem B1294815 : Blo 1293965 1294815 := bstep (se 1 (by rfl) ⟨971111, by rfl⟩ : syracuseStep 1294815 = 1942223) B1942223
theorem B16589285 : Blo 1293965 16589285 := bstep (se 4 (by rfl) ⟨1555245, by rfl⟩ : syracuseStep 16589285 = 3110491) B3110491
theorem B1294823 : Blo 1293965 1294823 := bstep (se 1 (by rfl) ⟨971117, by rfl⟩ : syracuseStep 1294823 = 1942235) B1942235
theorem B1942121 : Blo 1293965 1942121 := bstep (se 2 (by rfl) ⟨728295, by rfl⟩ : syracuseStep 1942121 = 1456591) B1456591
theorem B1942127 : Blo 1293965 1942127 := bstep (se 1 (by rfl) ⟨1456595, by rfl⟩ : syracuseStep 1942127 = 2913191) B2913191
theorem B2458279 : Blo 1293965 2458279 := bstep (se 1 (by rfl) ⟨1843709, by rfl⟩ : syracuseStep 2458279 = 3687419) B3687419
theorem B1295099 : Blo 1293965 1295099 := bstep (se 1 (by rfl) ⟨971324, by rfl⟩ : syracuseStep 1295099 = 1942649) B1942649
theorem B8291159 : Blo 1293965 8291159 := bstep (se 1 (by rfl) ⟨6218369, by rfl⟩ : syracuseStep 8291159 = 12436739) B12436739
theorem B1942751 : Blo 1293965 1942751 := bstep (se 1 (by rfl) ⟨1457063, by rfl⟩ : syracuseStep 1942751 = 2914127) B2914127
theorem B3687727 : Blo 1293965 3687727 := bstep (se 1 (by rfl) ⟨2765795, by rfl⟩ : syracuseStep 3687727 = 5531591) B5531591
theorem B1295679 : Blo 1293965 1295679 := bstep (se 1 (by rfl) ⟨971759, by rfl⟩ : syracuseStep 1295679 = 1943519) B1943519
theorem B1295687 : Blo 1293965 1295687 := bstep (se 1 (by rfl) ⟨971765, by rfl⟩ : syracuseStep 1295687 = 1943531) B1943531
theorem B1295719 : Blo 1293965 1295719 := bstep (se 1 (by rfl) ⟨971789, by rfl⟩ : syracuseStep 1295719 = 1943579) B1943579
theorem B7005611 : Blo 1293965 7005611 := bstep (se 1 (by rfl) ⟨5254208, by rfl⟩ : syracuseStep 7005611 = 10508417) B10508417
theorem B1942991 : Blo 1293965 1942991 := bstep (se 1 (by rfl) ⟨1457243, by rfl⟩ : syracuseStep 1942991 = 2914487) B2914487
theorem B1295963 : Blo 1293965 1295963 := bstep (se 1 (by rfl) ⟨971972, by rfl⟩ : syracuseStep 1295963 = 1943945) B1943945
theorem B1943177 : Blo 1293965 1943177 := bstep (se 2 (by rfl) ⟨728691, by rfl⟩ : syracuseStep 1943177 = 1457383) B1457383
theorem B1943231 : Blo 1293965 1943231 := bstep (se 1 (by rfl) ⟨1457423, by rfl⟩ : syracuseStep 1943231 = 2914847) B2914847
theorem B1845031 : Blo 1293965 1845031 := bstep (se 1 (by rfl) ⟨1383773, by rfl⟩ : syracuseStep 1845031 = 2767547) B2767547
theorem B7472969 : Blo 1293965 7472969 := bstep (se 2 (by rfl) ⟨2802363, by rfl⟩ : syracuseStep 7472969 = 5604727) B5604727
theorem B9832265 : Blo 1293965 9832265 := bstep (se 2 (by rfl) ⟨3687099, by rfl⟩ : syracuseStep 9832265 = 7374199) B7374199
theorem B14010185 : Blo 1293965 14010185 := bstep (se 2 (by rfl) ⟨5253819, by rfl⟩ : syracuseStep 14010185 = 10507639) B10507639
theorem B1943387 : Blo 1293965 1943387 := bstep (se 1 (by rfl) ⟨1457540, by rfl⟩ : syracuseStep 1943387 = 2915081) B2915081
theorem B6219965 : Blo 1293965 6219965 := bstep (se 3 (by rfl) ⟨1166243, by rfl⟩ : syracuseStep 6219965 = 2332487) B2332487
theorem B1943771 : Blo 1293965 1943771 := bstep (se 1 (by rfl) ⟨1457828, by rfl⟩ : syracuseStep 1943771 = 2915657) B2915657
theorem B6998521 : Blo 1293965 6998521 := bstep (se 2 (by rfl) ⟨2624445, by rfl⟩ : syracuseStep 6998521 = 5248891) B5248891
theorem B16583291 : Blo 1293965 16583291 := bstep (se 1 (by rfl) ⟨12437468, by rfl⟩ : syracuseStep 16583291 = 24874937) B24874937
theorem B3689185 : Blo 1293965 3689185 := bstep (se 2 (by rfl) ⟨1383444, by rfl⟩ : syracuseStep 3689185 = 2766889) B2766889
theorem B3279599 : Blo 1293965 3279599 := bstep (se 1 (by rfl) ⟨2459699, by rfl⟩ : syracuseStep 3279599 = 4919399) B4919399
theorem B6998845 : Blo 1293965 6998845 := bstep (se 3 (by rfl) ⟨1312283, by rfl⟩ : syracuseStep 6998845 = 2624567) B2624567
theorem B2075711 : Blo 1293965 2075711 := bstep (se 1 (by rfl) ⟨1556783, by rfl⟩ : syracuseStep 2075711 = 3113567) B3113567
theorem B4148489 : Blo 1293965 4148489 := bstep (se 2 (by rfl) ⟨1555683, by rfl⟩ : syracuseStep 4148489 = 3111367) B3111367
theorem B113560865 : Blo 1293965 113560865 := bstep (se 2 (by rfl) ⟨42585324, by rfl⟩ : syracuseStep 113560865 = 85170649) B85170649
theorem B5320043 : Blo 1293965 5320043 := bstep (se 1 (by rfl) ⟨3990032, by rfl⟩ : syracuseStep 5320043 = 7980065) B7980065
theorem B19926425 : Blo 1293965 19926425 := bstep (se 2 (by rfl) ⟨7472409, by rfl⟩ : syracuseStep 19926425 = 14944819) B14944819
theorem B4148705 : Blo 1293965 4148705 := bstep (se 2 (by rfl) ⟨1555764, by rfl⟩ : syracuseStep 4148705 = 3111529) B3111529
theorem B7876253 : Blo 1293965 7876253 := bstep (se 3 (by rfl) ⟨1476797, by rfl⟩ : syracuseStep 7876253 = 2953595) B2953595
theorem B4370111 : Blo 1293965 4370111 := bstep (se 1 (by rfl) ⟨3277583, by rfl⟩ : syracuseStep 4370111 = 6555167) B6555167
theorem B4919231 : Blo 1293965 4919231 := bstep (se 1 (by rfl) ⟨3689423, by rfl⟩ : syracuseStep 4919231 = 7378847) B7378847
theorem B7876547 : Blo 1293965 7876547 := bstep (se 1 (by rfl) ⟨5907410, by rfl⟩ : syracuseStep 7876547 = 11814821) B11814821
theorem B14757875 : Blo 1293965 14757875 := bstep (se 1 (by rfl) ⟨11068406, by rfl⟩ : syracuseStep 14757875 = 22136813) B22136813
theorem B6557759 : Blo 1293965 6557759 := bstep (se 1 (by rfl) ⟨4918319, by rfl⟩ : syracuseStep 6557759 = 9836639) B9836639
theorem B191599577 : Blo 1293965 191599577 := bstep (se 2 (by rfl) ⟨71849841, by rfl⟩ : syracuseStep 191599577 = 143699683) B143699683
theorem B18674711 : Blo 1293965 18674711 := bstep (se 1 (by rfl) ⟨14006033, by rfl⟩ : syracuseStep 18674711 = 28012067) B28012067
theorem B7369825 : Blo 1293965 7369825 := bstep (se 2 (by rfl) ⟨2763684, by rfl⟩ : syracuseStep 7369825 = 5527369) B5527369
theorem B6550793 : Blo 1293965 6550793 := bstep (se 2 (by rfl) ⟨2456547, by rfl⟩ : syracuseStep 6550793 = 4913095) B4913095
theorem B7378391 : Blo 1293965 7378391 := bstep (se 1 (by rfl) ⟨5533793, by rfl⟩ : syracuseStep 7378391 = 11067587) B11067587
theorem B8861417 : Blo 1293965 8861417 := bstep (se 2 (by rfl) ⟨3323031, by rfl⟩ : syracuseStep 8861417 = 6646063) B6646063
theorem B14005993 : Blo 1293965 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B8296283 : Blo 1293965 8296283 := bstep (se 1 (by rfl) ⟨6222212, by rfl⟩ : syracuseStep 8296283 = 12444425) B12444425
theorem B2914271 : Blo 1293965 2914271 := bstep (se 1 (by rfl) ⟨2185703, by rfl⟩ : syracuseStep 2914271 = 4371407) B4371407
theorem B2914343 : Blo 1293965 2914343 := bstep (se 1 (by rfl) ⟨2185757, by rfl⟩ : syracuseStep 2914343 = 4371515) B4371515
theorem B1456231 : Blo 1293965 1456231 := bstep (se 1 (by rfl) ⟨1092173, by rfl⟩ : syracuseStep 1456231 = 2184347) B2184347
theorem B2914523 : Blo 1293965 2914523 := bstep (se 1 (by rfl) ⟨2185892, by rfl⟩ : syracuseStep 2914523 = 4371785) B4371785
theorem B2185447 : Blo 1293965 2185447 := bstep (se 1 (by rfl) ⟨1639085, by rfl⟩ : syracuseStep 2185447 = 3278171) B3278171
theorem B14752043 : Blo 1293965 14752043 := bstep (se 1 (by rfl) ⟨11064032, by rfl⟩ : syracuseStep 14752043 = 22128065) B22128065
theorem B11065673 : Blo 1293965 11065673 := bstep (se 2 (by rfl) ⟨4149627, by rfl⟩ : syracuseStep 11065673 = 8299255) B8299255
theorem B2914721 : Blo 1293965 2914721 := bstep (se 2 (by rfl) ⟨1093020, by rfl⟩ : syracuseStep 2914721 = 2186041) B2186041
theorem B12442085 : Blo 1293965 12442085 := bstep (se 4 (by rfl) ⟨1166445, by rfl⟩ : syracuseStep 12442085 = 2332891) B2332891
theorem B2914793 : Blo 1293965 2914793 := bstep (se 2 (by rfl) ⟨1093047, by rfl⟩ : syracuseStep 2914793 = 2186095) B2186095
theorem B16816663 : Blo 1293965 16816663 := bstep (se 1 (by rfl) ⟨12612497, by rfl⟩ : syracuseStep 16816663 = 25224995) B25224995
theorem B1661599 : Blo 1293965 1661599 := bstep (se 1 (by rfl) ⟨1246199, by rfl⟩ : syracuseStep 1661599 = 2492399) B2492399
theorem B6552251 : Blo 1293965 6552251 := bstep (se 1 (by rfl) ⟨4914188, by rfl⟩ : syracuseStep 6552251 = 9828377) B9828377
theorem B3685277 : Blo 1293965 3685277 := bstep (se 3 (by rfl) ⟨690989, by rfl⟩ : syracuseStep 3685277 = 1381979) B1381979
theorem B2915423 : Blo 1293965 2915423 := bstep (se 1 (by rfl) ⟨2186567, by rfl⟩ : syracuseStep 2915423 = 4373135) B4373135
theorem B2186345 : Blo 1293965 2186345 := bstep (se 2 (by rfl) ⟨819879, by rfl⟩ : syracuseStep 2186345 = 1639759) B1639759
theorem B2915639 : Blo 1293965 2915639 := bstep (se 1 (by rfl) ⟨2186729, by rfl⟩ : syracuseStep 2915639 = 4373459) B4373459
theorem B50437495 : Blo 1293965 50437495 := bstep (se 1 (by rfl) ⟨37828121, by rfl⟩ : syracuseStep 50437495 = 75656243) B75656243
theorem B50470289 : Blo 1293965 50470289 := bstep (se 2 (by rfl) ⟨18926358, by rfl⟩ : syracuseStep 50470289 = 37852717) B37852717
theorem B7978439 : Blo 1293965 7978439 := bstep (se 1 (by rfl) ⟨5983829, by rfl⟩ : syracuseStep 7978439 = 11967659) B11967659
theorem B2915819 : Blo 1293965 2915819 := bstep (se 1 (by rfl) ⟨2186864, by rfl⟩ : syracuseStep 2915819 = 4373729) B4373729
theorem B3685961 : Blo 1293965 3685961 := bstep (se 2 (by rfl) ⟨1382235, by rfl⟩ : syracuseStep 3685961 = 2764471) B2764471
theorem B1941095 : Blo 1293965 1941095 := bstep (se 1 (by rfl) ⟨1455821, by rfl⟩ : syracuseStep 1941095 = 2911643) B2911643
theorem B2457209 : Blo 1293965 2457209 := bstep (se 2 (by rfl) ⟨921453, by rfl⟩ : syracuseStep 2457209 = 1842907) B1842907
theorem B55967381 : Blo 1293965 55967381 := bstep (se 6 (by rfl) ⟨1311735, by rfl⟩ : syracuseStep 55967381 = 2623471) B2623471
theorem B1293979 : Blo 1293965 1293979 := bstep (se 1 (by rfl) ⟨970484, by rfl⟩ : syracuseStep 1293979 = 1940969) B1940969
theorem B1294075 : Blo 1293965 1294075 := bstep (se 1 (by rfl) ⟨970556, by rfl⟩ : syracuseStep 1294075 = 1941113) B1941113
theorem B1941257 : Blo 1293965 1941257 := bstep (se 2 (by rfl) ⟨727971, by rfl⟩ : syracuseStep 1941257 = 1455943) B1455943
theorem B1638235 : Blo 1293965 1638235 := bstep (se 1 (by rfl) ⟨1228676, by rfl⟩ : syracuseStep 1638235 = 2457353) B2457353
theorem B3276683 : Blo 1293965 3276683 := bstep (se 1 (by rfl) ⟨2457512, by rfl⟩ : syracuseStep 3276683 = 4915025) B4915025
theorem B1294239 : Blo 1293965 1294239 := bstep (se 1 (by rfl) ⟨970679, by rfl⟩ : syracuseStep 1294239 = 1941359) B1941359
theorem B3686303 : Blo 1293965 3686303 := bstep (se 1 (by rfl) ⟨2764727, by rfl⟩ : syracuseStep 3686303 = 5529455) B5529455
theorem B1941479 : Blo 1293965 1941479 := bstep (se 1 (by rfl) ⟨1456109, by rfl⟩ : syracuseStep 1941479 = 2912219) B2912219
theorem B1294399 : Blo 1293965 1294399 := bstep (se 1 (by rfl) ⟨970799, by rfl⟩ : syracuseStep 1294399 = 1941599) B1941599
theorem B1294439 : Blo 1293965 1294439 := bstep (se 1 (by rfl) ⟨970829, by rfl⟩ : syracuseStep 1294439 = 1941659) B1941659
theorem B1941641 : Blo 1293965 1941641 := bstep (se 2 (by rfl) ⟨728115, by rfl⟩ : syracuseStep 1941641 = 1456231) B1456231
theorem B1294495 : Blo 1293965 1294495 := bstep (se 1 (by rfl) ⟨970871, by rfl⟩ : syracuseStep 1294495 = 1941743) B1941743
theorem B2457839 : Blo 1293965 2457839 := bstep (se 1 (by rfl) ⟨1843379, by rfl⟩ : syracuseStep 2457839 = 3686759) B3686759
theorem B11059523 : Blo 1293965 11059523 := bstep (se 1 (by rfl) ⟨8294642, by rfl⟩ : syracuseStep 11059523 = 16589285) B16589285
theorem B1294747 : Blo 1293965 1294747 := bstep (se 1 (by rfl) ⟨971060, by rfl⟩ : syracuseStep 1294747 = 1942121) B1942121
theorem B1294751 : Blo 1293965 1294751 := bstep (se 1 (by rfl) ⟨971063, by rfl⟩ : syracuseStep 1294751 = 1942127) B1942127
theorem B9331361 : Blo 1293965 9331361 := bstep (se 2 (by rfl) ⟨3499260, by rfl⟩ : syracuseStep 9331361 = 6998521) B6998521
theorem B1295167 : Blo 1293965 1295167 := bstep (se 1 (by rfl) ⟨971375, by rfl⟩ : syracuseStep 1295167 = 1942751) B1942751
theorem B4367195 : Blo 1293965 4367195 := bstep (se 1 (by rfl) ⟨3275396, by rfl⟩ : syracuseStep 4367195 = 6550793) B6550793
theorem B3277705 : Blo 1293965 3277705 := bstep (se 2 (by rfl) ⟨1229139, by rfl⟩ : syracuseStep 3277705 = 2458279) B2458279
theorem B4670407 : Blo 1293965 4670407 := bstep (se 1 (by rfl) ⟨3502805, by rfl⟩ : syracuseStep 4670407 = 7005611) B7005611
theorem B1295327 : Blo 1293965 1295327 := bstep (se 1 (by rfl) ⟨971495, by rfl⟩ : syracuseStep 1295327 = 1942991) B1942991
theorem B19923965 : Blo 1293965 19923965 := bstep (se 3 (by rfl) ⟨3735743, by rfl⟩ : syracuseStep 19923965 = 7471487) B7471487
theorem B9331793 : Blo 1293965 9331793 := bstep (se 2 (by rfl) ⟨3499422, by rfl⟩ : syracuseStep 9331793 = 6998845) B6998845
theorem B1295451 : Blo 1293965 1295451 := bstep (se 1 (by rfl) ⟨971588, by rfl⟩ : syracuseStep 1295451 = 1943177) B1943177
theorem B1295487 : Blo 1293965 1295487 := bstep (se 1 (by rfl) ⟨971615, by rfl⟩ : syracuseStep 1295487 = 1943231) B1943231
theorem B5907611 : Blo 1293965 5907611 := bstep (se 1 (by rfl) ⟨4430708, by rfl⟩ : syracuseStep 5907611 = 8861417) B8861417
theorem B4981979 : Blo 1293965 4981979 := bstep (se 1 (by rfl) ⟨3736484, by rfl⟩ : syracuseStep 4981979 = 7472969) B7472969
theorem B6554843 : Blo 1293965 6554843 := bstep (se 1 (by rfl) ⟨4916132, by rfl⟩ : syracuseStep 6554843 = 9832265) B9832265
theorem B9340123 : Blo 1293965 9340123 := bstep (se 1 (by rfl) ⟨7005092, by rfl⟩ : syracuseStep 9340123 = 14010185) B14010185
theorem B5530855 : Blo 1293965 5530855 := bstep (se 1 (by rfl) ⟨4148141, by rfl⟩ : syracuseStep 5530855 = 8296283) B8296283
theorem B1295591 : Blo 1293965 1295591 := bstep (se 1 (by rfl) ⟨971693, by rfl⟩ : syracuseStep 1295591 = 1943387) B1943387
theorem B1942847 : Blo 1293965 1942847 := bstep (se 1 (by rfl) ⟨1457135, by rfl⟩ : syracuseStep 1942847 = 2914271) B2914271
theorem B1942895 : Blo 1293965 1942895 := bstep (se 1 (by rfl) ⟨1457171, by rfl⟩ : syracuseStep 1942895 = 2914343) B2914343
theorem B4146643 : Blo 1293965 4146643 := bstep (se 1 (by rfl) ⟨3109982, by rfl⟩ : syracuseStep 4146643 = 6219965) B6219965
theorem B1943015 : Blo 1293965 1943015 := bstep (se 1 (by rfl) ⟨1457261, by rfl⟩ : syracuseStep 1943015 = 2914523) B2914523
theorem B1295847 : Blo 1293965 1295847 := bstep (se 1 (by rfl) ⟨971885, by rfl⟩ : syracuseStep 1295847 = 1943771) B1943771
theorem B1943147 : Blo 1293965 1943147 := bstep (se 1 (by rfl) ⟨1457360, by rfl⟩ : syracuseStep 1943147 = 2914721) B2914721
theorem B1943195 : Blo 1293965 1943195 := bstep (se 1 (by rfl) ⟨1457396, by rfl⟩ : syracuseStep 1943195 = 2914793) B2914793
theorem B4916969 : Blo 1293965 4916969 := bstep (se 2 (by rfl) ⟨1843863, by rfl⟩ : syracuseStep 4916969 = 3687727) B3687727
theorem B4368167 : Blo 1293965 4368167 := bstep (se 1 (by rfl) ⟨3276125, by rfl⟩ : syracuseStep 4368167 = 6552251) B6552251
theorem B67249993 : Blo 1293965 67249993 := bstep (se 2 (by rfl) ⟨25218747, by rfl⟩ : syracuseStep 67249993 = 50437495) B50437495
theorem B1943615 : Blo 1293965 1943615 := bstep (se 1 (by rfl) ⟨1457711, by rfl⟩ : syracuseStep 1943615 = 2915423) B2915423
theorem B1943759 : Blo 1293965 1943759 := bstep (se 1 (by rfl) ⟨1457819, by rfl⟩ : syracuseStep 1943759 = 2915639) B2915639
theorem B33646859 : Blo 1293965 33646859 := bstep (se 1 (by rfl) ⟨25235144, by rfl⟩ : syracuseStep 33646859 = 50470289) B50470289
theorem B5318959 : Blo 1293965 5318959 := bstep (se 1 (by rfl) ⟨3989219, by rfl⟩ : syracuseStep 5318959 = 7978439) B7978439
theorem B1943879 : Blo 1293965 1943879 := bstep (se 1 (by rfl) ⟨1457909, by rfl⟩ : syracuseStep 1943879 = 2915819) B2915819
theorem B2460041 : Blo 1293965 2460041 := bstep (se 2 (by rfl) ⟨922515, by rfl⟩ : syracuseStep 2460041 = 1845031) B1845031
theorem B3279487 : Blo 1293965 3279487 := bstep (se 1 (by rfl) ⟨2459615, by rfl⟩ : syracuseStep 3279487 = 4919231) B4919231
theorem B89688869 : Blo 1293965 89688869 := bstep (se 4 (by rfl) ⟨8408331, by rfl⟩ : syracuseStep 89688869 = 16816663) B16816663
theorem B127733051 : Blo 1293965 127733051 := bstep (se 1 (by rfl) ⟨95799788, by rfl⟩ : syracuseStep 127733051 = 191599577) B191599577
theorem B4918913 : Blo 1293965 4918913 := bstep (se 2 (by rfl) ⟨1844592, by rfl⟩ : syracuseStep 4918913 = 3689185) B3689185
theorem B4918927 : Blo 1293965 4918927 := bstep (se 1 (by rfl) ⟨3689195, by rfl⟩ : syracuseStep 4918927 = 7378391) B7378391
theorem B11063213 : Blo 1293965 11063213 := bstep (se 3 (by rfl) ⟨2074352, by rfl⟩ : syracuseStep 11063213 = 4148705) B4148705
theorem B9826433 : Blo 1293965 9826433 := bstep (se 2 (by rfl) ⟨3684912, by rfl⟩ : syracuseStep 9826433 = 7369825) B7369825
theorem B9834695 : Blo 1293965 9834695 := bstep (se 1 (by rfl) ⟨7376021, by rfl⟩ : syracuseStep 9834695 = 14752043) B14752043
theorem B9838583 : Blo 1293965 9838583 := bstep (se 1 (by rfl) ⟨7378937, by rfl⟩ : syracuseStep 9838583 = 14757875) B14757875
theorem B7377115 : Blo 1293965 7377115 := bstep (se 1 (by rfl) ⟨5532836, by rfl⟩ : syracuseStep 7377115 = 11065673) B11065673
theorem B8294723 : Blo 1293965 8294723 := bstep (se 1 (by rfl) ⟨6221042, by rfl⟩ : syracuseStep 8294723 = 12442085) B12442085
theorem B11055527 : Blo 1293965 11055527 := bstep (se 1 (by rfl) ⟨8291645, by rfl⟩ : syracuseStep 11055527 = 16583291) B16583291
theorem B2765659 : Blo 1293965 2765659 := bstep (se 1 (by rfl) ⟨2074244, by rfl⟩ : syracuseStep 2765659 = 4148489) B4148489
theorem B75707243 : Blo 1293965 75707243 := bstep (se 1 (by rfl) ⟨56780432, by rfl⟩ : syracuseStep 75707243 = 113560865) B113560865
theorem B13284283 : Blo 1293965 13284283 := bstep (se 1 (by rfl) ⟨9963212, by rfl⟩ : syracuseStep 13284283 = 19926425) B19926425
theorem B18674657 : Blo 1293965 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B9827405 : Blo 1293965 9827405 := bstep (se 3 (by rfl) ⟨1842638, by rfl⟩ : syracuseStep 9827405 = 3685277) B3685277
theorem B37311587 : Blo 1293965 37311587 := bstep (se 1 (by rfl) ⟨27983690, by rfl⟩ : syracuseStep 37311587 = 55967381) B55967381
theorem B2184313 : Blo 1293965 2184313 := bstep (se 2 (by rfl) ⟨819117, by rfl⟩ : syracuseStep 2184313 = 1638235) B1638235
theorem B2913407 : Blo 1293965 2913407 := bstep (se 1 (by rfl) ⟨2185055, by rfl⟩ : syracuseStep 2913407 = 4370111) B4370111
theorem B2184455 : Blo 1293965 2184455 := bstep (se 1 (by rfl) ⟨1638341, by rfl⟩ : syracuseStep 2184455 = 3276683) B3276683
theorem B4371839 : Blo 1293965 4371839 := bstep (se 1 (by rfl) ⟨3278879, by rfl⟩ : syracuseStep 4371839 = 6557759) B6557759
theorem B5535229 : Blo 1293965 5535229 := bstep (se 3 (by rfl) ⟨1037855, by rfl⟩ : syracuseStep 5535229 = 2075711) B2075711
theorem B10507897 : Blo 1293965 10507897 := bstep (se 2 (by rfl) ⟨3940461, by rfl⟩ : syracuseStep 10507897 = 7880923) B7880923
theorem B2913929 : Blo 1293965 2913929 := bstep (se 2 (by rfl) ⟨1092723, by rfl⟩ : syracuseStep 2913929 = 2185447) B2185447
theorem B5527439 : Blo 1293965 5527439 := bstep (se 1 (by rfl) ⟨4145579, by rfl⟩ : syracuseStep 5527439 = 8291159) B8291159
theorem B12449807 : Blo 1293965 12449807 := bstep (se 1 (by rfl) ⟨9337355, by rfl⟩ : syracuseStep 12449807 = 18674711) B18674711
theorem B8861861 : Blo 1293965 8861861 := bstep (se 4 (by rfl) ⟨830799, by rfl⟩ : syracuseStep 8861861 = 1661599) B1661599
theorem B2186399 : Blo 1293965 2186399 := bstep (se 1 (by rfl) ⟨1639799, by rfl⟩ : syracuseStep 2186399 = 3279599) B3279599
theorem B1457563 : Blo 1293965 1457563 := bstep (se 1 (by rfl) ⟨1093172, by rfl⟩ : syracuseStep 1457563 = 2186345) B2186345
theorem B3546695 : Blo 1293965 3546695 := bstep (se 1 (by rfl) ⟨2660021, by rfl⟩ : syracuseStep 3546695 = 5320043) B5320043
theorem B2457307 : Blo 1293965 2457307 := bstep (se 1 (by rfl) ⟨1842980, by rfl⟩ : syracuseStep 2457307 = 3685961) B3685961
theorem B1294063 : Blo 1293965 1294063 := bstep (se 1 (by rfl) ⟨970547, by rfl⟩ : syracuseStep 1294063 = 1941095) B1941095
theorem B1638139 : Blo 1293965 1638139 := bstep (se 1 (by rfl) ⟨1228604, by rfl⟩ : syracuseStep 1638139 = 2457209) B2457209
theorem B5250835 : Blo 1293965 5250835 := bstep (se 1 (by rfl) ⟨3938126, by rfl⟩ : syracuseStep 5250835 = 7876253) B7876253
theorem B1294171 : Blo 1293965 1294171 := bstep (se 1 (by rfl) ⟨970628, by rfl⟩ : syracuseStep 1294171 = 1941257) B1941257
theorem B2457535 : Blo 1293965 2457535 := bstep (se 1 (by rfl) ⟨1843151, by rfl⟩ : syracuseStep 2457535 = 3686303) B3686303
theorem B5251031 : Blo 1293965 5251031 := bstep (se 1 (by rfl) ⟨3938273, by rfl⟩ : syracuseStep 5251031 = 7876547) B7876547
theorem B1294319 : Blo 1293965 1294319 := bstep (se 1 (by rfl) ⟨970739, by rfl⟩ : syracuseStep 1294319 = 1941479) B1941479
theorem B1294427 : Blo 1293965 1294427 := bstep (se 1 (by rfl) ⟨970820, by rfl⟩ : syracuseStep 1294427 = 1941641) B1941641
theorem B1638559 : Blo 1293965 1638559 := bstep (se 1 (by rfl) ⟨1228919, by rfl⟩ : syracuseStep 1638559 = 2457839) B2457839
theorem B7373015 : Blo 1293965 7373015 := bstep (se 1 (by rfl) ⟨5529761, by rfl⟩ : syracuseStep 7373015 = 11059523) B11059523
theorem B5529815 : Blo 1293965 5529815 := bstep (se 1 (by rfl) ⟨4147361, by rfl⟩ : syracuseStep 5529815 = 8294723) B8294723
theorem B15753629 : Blo 1293965 15753629 := bstep (se 3 (by rfl) ⟨2953805, by rfl⟩ : syracuseStep 15753629 = 5907611) B5907611
theorem B50471495 : Blo 1293965 50471495 := bstep (se 1 (by rfl) ⟨37853621, by rfl⟩ : syracuseStep 50471495 = 75707243) B75707243
theorem B56042117 : Blo 1293965 56042117 := bstep (se 4 (by rfl) ⟨5253948, by rfl⟩ : syracuseStep 56042117 = 10507897) B10507897
theorem B1942271 : Blo 1293965 1942271 := bstep (se 1 (by rfl) ⟨1456703, by rfl⟩ : syracuseStep 1942271 = 2913407) B2913407
theorem B1295231 : Blo 1293965 1295231 := bstep (se 1 (by rfl) ⟨971423, by rfl⟩ : syracuseStep 1295231 = 1942847) B1942847
theorem B1295263 : Blo 1293965 1295263 := bstep (se 1 (by rfl) ⟨971447, by rfl⟩ : syracuseStep 1295263 = 1942895) B1942895
theorem B1295343 : Blo 1293965 1295343 := bstep (se 1 (by rfl) ⟨971507, by rfl⟩ : syracuseStep 1295343 = 1943015) B1943015
theorem B1295431 : Blo 1293965 1295431 := bstep (se 1 (by rfl) ⟨971573, by rfl⟩ : syracuseStep 1295431 = 1943147) B1943147
theorem B1942619 : Blo 1293965 1942619 := bstep (se 1 (by rfl) ⟨1456964, by rfl⟩ : syracuseStep 1942619 = 2913929) B2913929
theorem B1295463 : Blo 1293965 1295463 := bstep (se 1 (by rfl) ⟨971597, by rfl⟩ : syracuseStep 1295463 = 1943195) B1943195
theorem B3687545 : Blo 1293965 3687545 := bstep (se 2 (by rfl) ⟨1382829, by rfl⟩ : syracuseStep 3687545 = 2765659) B2765659
theorem B3277979 : Blo 1293965 3277979 := bstep (se 1 (by rfl) ⟨2458484, by rfl⟩ : syracuseStep 3277979 = 4916969) B4916969
theorem B17712377 : Blo 1293965 17712377 := bstep (se 2 (by rfl) ⟨6642141, by rfl⟩ : syracuseStep 17712377 = 13284283) B13284283
theorem B6227209 : Blo 1293965 6227209 := bstep (se 2 (by rfl) ⟨2335203, by rfl⟩ : syracuseStep 6227209 = 4670407) B4670407
theorem B8299871 : Blo 1293965 8299871 := bstep (se 1 (by rfl) ⟨6224903, by rfl⟩ : syracuseStep 8299871 = 12449807) B12449807
theorem B1295743 : Blo 1293965 1295743 := bstep (se 1 (by rfl) ⟨971807, by rfl⟩ : syracuseStep 1295743 = 1943615) B1943615
theorem B5907907 : Blo 1293965 5907907 := bstep (se 1 (by rfl) ⟨4430930, by rfl⟩ : syracuseStep 5907907 = 8861861) B8861861
theorem B1295839 : Blo 1293965 1295839 := bstep (se 1 (by rfl) ⟨971879, by rfl⟩ : syracuseStep 1295839 = 1943759) B1943759
theorem B22431239 : Blo 1293965 22431239 := bstep (se 1 (by rfl) ⟨16823429, by rfl⟩ : syracuseStep 22431239 = 33646859) B33646859
theorem B1295919 : Blo 1293965 1295919 := bstep (se 1 (by rfl) ⟨971939, by rfl⟩ : syracuseStep 1295919 = 1943879) B1943879
theorem B1640027 : Blo 1293965 1640027 := bstep (se 1 (by rfl) ⟨1230020, by rfl⟩ : syracuseStep 1640027 = 2460041) B2460041
theorem B12453497 : Blo 1293965 12453497 := bstep (se 2 (by rfl) ⟨4670061, by rfl⟩ : syracuseStep 12453497 = 9340123) B9340123
theorem B7374473 : Blo 1293965 7374473 := bstep (se 2 (by rfl) ⟨2765427, by rfl⟩ : syracuseStep 7374473 = 5530855) B5530855
theorem B1943417 : Blo 1293965 1943417 := bstep (se 2 (by rfl) ⟨728781, by rfl⟩ : syracuseStep 1943417 = 1457563) B1457563
theorem B3279275 : Blo 1293965 3279275 := bstep (se 1 (by rfl) ⟨2459456, by rfl⟩ : syracuseStep 3279275 = 4918913) B4918913
theorem B7375475 : Blo 1293965 7375475 := bstep (se 1 (by rfl) ⟨5531606, by rfl⟩ : syracuseStep 7375475 = 11063213) B11063213
theorem B3500687 : Blo 1293965 3500687 := bstep (se 1 (by rfl) ⟨2625515, by rfl⟩ : syracuseStep 3500687 = 5251031) B5251031
theorem B6556463 : Blo 1293965 6556463 := bstep (se 1 (by rfl) ⟨4917347, by rfl⟩ : syracuseStep 6556463 = 9834695) B9834695
theorem B6220907 : Blo 1293965 6220907 := bstep (se 1 (by rfl) ⟨4665680, by rfl⟩ : syracuseStep 6220907 = 9331361) B9331361
theorem B2911463 : Blo 1293965 2911463 := bstep (se 1 (by rfl) ⟨2183597, by rfl⟩ : syracuseStep 2911463 = 4367195) B4367195
theorem B13282643 : Blo 1293965 13282643 := bstep (se 1 (by rfl) ⟨9961982, by rfl⟩ : syracuseStep 13282643 = 19923965) B19923965
theorem B6221195 : Blo 1293965 6221195 := bstep (se 1 (by rfl) ⟨4665896, by rfl⟩ : syracuseStep 6221195 = 9331793) B9331793
theorem B24874391 : Blo 1293965 24874391 := bstep (se 1 (by rfl) ⟨18655793, by rfl⟩ : syracuseStep 24874391 = 37311587) B37311587
theorem B3321319 : Blo 1293965 3321319 := bstep (se 1 (by rfl) ⟨2490989, by rfl⟩ : syracuseStep 3321319 = 4981979) B4981979
theorem B4369895 : Blo 1293965 4369895 := bstep (se 1 (by rfl) ⟨3277421, by rfl⟩ : syracuseStep 4369895 = 6554843) B6554843
theorem B4370273 : Blo 1293965 4370273 := bstep (se 2 (by rfl) ⟨1638852, by rfl⟩ : syracuseStep 4370273 = 3277705) B3277705
theorem B2912111 : Blo 1293965 2912111 := bstep (se 1 (by rfl) ⟨2184083, by rfl⟩ : syracuseStep 2912111 = 4368167) B4368167
theorem B28004453 : Blo 1293965 28004453 := bstep (se 4 (by rfl) ⟨2625417, by rfl⟩ : syracuseStep 28004453 = 5250835) B5250835
theorem B2912417 : Blo 1293965 2912417 := bstep (se 2 (by rfl) ⟨1092156, by rfl⟩ : syracuseStep 2912417 = 2184313) B2184313
theorem B6558569 : Blo 1293965 6558569 := bstep (se 2 (by rfl) ⟨2459463, by rfl⟩ : syracuseStep 6558569 = 4918927) B4918927
theorem B2184185 : Blo 1293965 2184185 := bstep (se 2 (by rfl) ⟨819069, by rfl⟩ : syracuseStep 2184185 = 1638139) B1638139
theorem B2364463 : Blo 1293965 2364463 := bstep (se 1 (by rfl) ⟨1773347, by rfl⟩ : syracuseStep 2364463 = 3546695) B3546695
theorem B89666657 : Blo 1293965 89666657 := bstep (se 2 (by rfl) ⟨33624996, by rfl⟩ : syracuseStep 89666657 = 67249993) B67249993
theorem B6559055 : Blo 1293965 6559055 := bstep (se 1 (by rfl) ⟨4919291, by rfl⟩ : syracuseStep 6559055 = 9838583) B9838583
theorem B6550955 : Blo 1293965 6550955 := bstep (se 1 (by rfl) ⟨4913216, by rfl⟩ : syracuseStep 6550955 = 9826433) B9826433
theorem B7370351 : Blo 1293965 7370351 := bstep (se 1 (by rfl) ⟨5527763, by rfl⟩ : syracuseStep 7370351 = 11055527) B11055527
theorem B9836153 : Blo 1293965 9836153 := bstep (se 2 (by rfl) ⟨3688557, by rfl⟩ : syracuseStep 9836153 = 7377115) B7377115
theorem B7091945 : Blo 1293965 7091945 := bstep (se 2 (by rfl) ⟨2659479, by rfl⟩ : syracuseStep 7091945 = 5318959) B5318959
theorem B12449771 : Blo 1293965 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B6551603 : Blo 1293965 6551603 := bstep (se 1 (by rfl) ⟨4913702, by rfl⟩ : syracuseStep 6551603 = 9827405) B9827405
theorem B340621469 : Blo 1293965 340621469 := bstep (se 3 (by rfl) ⟨63866525, by rfl⟩ : syracuseStep 340621469 = 127733051) B127733051
theorem B4372649 : Blo 1293965 4372649 := bstep (se 2 (by rfl) ⟨1639743, by rfl⟩ : syracuseStep 4372649 = 3279487) B3279487
theorem B1456303 : Blo 1293965 1456303 := bstep (se 1 (by rfl) ⟨1092227, by rfl⟩ : syracuseStep 1456303 = 2184455) B2184455
theorem B2914559 : Blo 1293965 2914559 := bstep (se 1 (by rfl) ⟨2185919, by rfl⟩ : syracuseStep 2914559 = 4371839) B4371839
theorem B3684959 : Blo 1293965 3684959 := bstep (se 1 (by rfl) ⟨2763719, by rfl⟩ : syracuseStep 3684959 = 5527439) B5527439
theorem B59792579 : Blo 1293965 59792579 := bstep (se 1 (by rfl) ⟨44844434, by rfl⟩ : syracuseStep 59792579 = 89688869) B89688869
theorem B5528857 : Blo 1293965 5528857 := bstep (se 2 (by rfl) ⟨2073321, by rfl⟩ : syracuseStep 5528857 = 4146643) B4146643
theorem B7380305 : Blo 1293965 7380305 := bstep (se 2 (by rfl) ⟨2767614, by rfl⟩ : syracuseStep 7380305 = 5535229) B5535229
theorem B1457599 : Blo 1293965 1457599 := bstep (se 1 (by rfl) ⟨1093199, by rfl⟩ : syracuseStep 1457599 = 2186399) B2186399
theorem B3276409 : Blo 1293965 3276409 := bstep (se 2 (by rfl) ⟨1228653, by rfl⟩ : syracuseStep 3276409 = 2457307) B2457307
theorem B3276713 : Blo 1293965 3276713 := bstep (se 2 (by rfl) ⟨1228767, by rfl⟩ : syracuseStep 3276713 = 2457535) B2457535
theorem B18669635 : Blo 1293965 18669635 := bstep (se 1 (by rfl) ⟨14002226, by rfl⟩ : syracuseStep 18669635 = 28004453) B28004453
theorem B1941611 : Blo 1293965 1941611 := bstep (se 1 (by rfl) ⟨1456208, by rfl⟩ : syracuseStep 1941611 = 2912417) B2912417
theorem B4915343 : Blo 1293965 4915343 := bstep (se 1 (by rfl) ⟨3686507, by rfl⟩ : syracuseStep 4915343 = 7373015) B7373015
theorem B3686543 : Blo 1293965 3686543 := bstep (se 1 (by rfl) ⟨2764907, by rfl⟩ : syracuseStep 3686543 = 5529815) B5529815
theorem B1941737 : Blo 1293965 1941737 := bstep (se 2 (by rfl) ⟨728151, by rfl⟩ : syracuseStep 1941737 = 1456303) B1456303
theorem B10502419 : Blo 1293965 10502419 := bstep (se 1 (by rfl) ⟨7876814, by rfl⟩ : syracuseStep 10502419 = 15753629) B15753629
theorem B1294847 : Blo 1293965 1294847 := bstep (se 1 (by rfl) ⟨971135, by rfl⟩ : syracuseStep 1294847 = 1942271) B1942271
theorem B1295079 : Blo 1293965 1295079 := bstep (se 1 (by rfl) ⟨971309, by rfl⟩ : syracuseStep 1295079 = 1942619) B1942619
theorem B59777771 : Blo 1293965 59777771 := bstep (se 1 (by rfl) ⟨44833328, by rfl⟩ : syracuseStep 59777771 = 89666657) B89666657
theorem B2458363 : Blo 1293965 2458363 := bstep (se 1 (by rfl) ⟨1843772, by rfl⟩ : syracuseStep 2458363 = 3687545) B3687545
theorem B4367303 : Blo 1293965 4367303 := bstep (se 1 (by rfl) ⟨3275477, by rfl⟩ : syracuseStep 4367303 = 6550955) B6550955
theorem B4916315 : Blo 1293965 4916315 := bstep (se 1 (by rfl) ⟨3687236, by rfl⟩ : syracuseStep 4916315 = 7374473) B7374473
theorem B4727963 : Blo 1293965 4727963 := bstep (se 1 (by rfl) ⟨3545972, by rfl⟩ : syracuseStep 4727963 = 7091945) B7091945
theorem B1295611 : Blo 1293965 1295611 := bstep (se 1 (by rfl) ⟨971708, by rfl⟩ : syracuseStep 1295611 = 1943417) B1943417
theorem B8299847 : Blo 1293965 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B4367735 : Blo 1293965 4367735 := bstep (se 1 (by rfl) ⟨3275801, by rfl⟩ : syracuseStep 4367735 = 6551603) B6551603
theorem B33211781 : Blo 1293965 33211781 := bstep (se 4 (by rfl) ⟨3113604, by rfl⟩ : syracuseStep 33211781 = 6227209) B6227209
theorem B1943039 : Blo 1293965 1943039 := bstep (se 1 (by rfl) ⟨1457279, by rfl⟩ : syracuseStep 1943039 = 2914559) B2914559
theorem B4916983 : Blo 1293965 4916983 := bstep (se 1 (by rfl) ⟨3687737, by rfl⟩ : syracuseStep 4916983 = 7375475) B7375475
theorem B1943465 : Blo 1293965 1943465 := bstep (se 2 (by rfl) ⟨728799, by rfl⟩ : syracuseStep 1943465 = 1457599) B1457599
theorem B4147271 : Blo 1293965 4147271 := bstep (se 1 (by rfl) ⟨3110453, by rfl⟩ : syracuseStep 4147271 = 6220907) B6220907
theorem B4368545 : Blo 1293965 4368545 := bstep (se 2 (by rfl) ⟨1638204, by rfl⟩ : syracuseStep 4368545 = 3276409) B3276409
theorem B4147463 : Blo 1293965 4147463 := bstep (se 1 (by rfl) ⟨3110597, by rfl⟩ : syracuseStep 4147463 = 6221195) B6221195
theorem B16582927 : Blo 1293965 16582927 := bstep (se 1 (by rfl) ⟨12437195, by rfl⟩ : syracuseStep 16582927 = 24874391) B24874391
theorem B12610469 : Blo 1293965 12610469 := bstep (se 4 (by rfl) ⟨1182231, by rfl⟩ : syracuseStep 12610469 = 2364463) B2364463
theorem B33647663 : Blo 1293965 33647663 := bstep (se 1 (by rfl) ⟨25235747, by rfl⟩ : syracuseStep 33647663 = 50471495) B50471495
theorem B11808251 : Blo 1293965 11808251 := bstep (se 1 (by rfl) ⟨8856188, by rfl⟩ : syracuseStep 11808251 = 17712377) B17712377
theorem B5533247 : Blo 1293965 5533247 := bstep (se 1 (by rfl) ⟨4149935, by rfl⟩ : syracuseStep 5533247 = 8299871) B8299871
theorem B14954159 : Blo 1293965 14954159 := bstep (se 1 (by rfl) ⟨11215619, by rfl⟩ : syracuseStep 14954159 = 22431239) B22431239
theorem B6557435 : Blo 1293965 6557435 := bstep (se 1 (by rfl) ⟨4918076, by rfl⟩ : syracuseStep 6557435 = 9836153) B9836153
theorem B8302331 : Blo 1293965 8302331 := bstep (se 1 (by rfl) ⟨6226748, by rfl⟩ : syracuseStep 8302331 = 12453497) B12453497
theorem B4370975 : Blo 1293965 4370975 := bstep (se 1 (by rfl) ⟨3278231, by rfl⟩ : syracuseStep 4370975 = 6556463) B6556463
theorem B7877209 : Blo 1293965 7877209 := bstep (se 2 (by rfl) ⟨2953953, by rfl⟩ : syracuseStep 7877209 = 5907907) B5907907
theorem B4428425 : Blo 1293965 4428425 := bstep (se 2 (by rfl) ⟨1660659, by rfl⟩ : syracuseStep 4428425 = 3321319) B3321319
theorem B4920203 : Blo 1293965 4920203 := bstep (se 1 (by rfl) ⟨3690152, by rfl⟩ : syracuseStep 4920203 = 7380305) B7380305
theorem B2913263 : Blo 1293965 2913263 := bstep (se 1 (by rfl) ⟨2184947, by rfl⟩ : syracuseStep 2913263 = 4369895) B4369895
theorem B2913515 : Blo 1293965 2913515 := bstep (se 1 (by rfl) ⟨2185136, by rfl⟩ : syracuseStep 2913515 = 4370273) B4370273
theorem B2184475 : Blo 1293965 2184475 := bstep (se 1 (by rfl) ⟨1638356, by rfl⟩ : syracuseStep 2184475 = 3276713) B3276713
theorem B2184745 : Blo 1293965 2184745 := bstep (se 2 (by rfl) ⟨819279, by rfl⟩ : syracuseStep 2184745 = 1638559) B1638559
theorem B37361411 : Blo 1293965 37361411 := bstep (se 1 (by rfl) ⟨28021058, by rfl⟩ : syracuseStep 37361411 = 56042117) B56042117
theorem B4372379 : Blo 1293965 4372379 := bstep (se 1 (by rfl) ⟨3279284, by rfl⟩ : syracuseStep 4372379 = 6558569) B6558569
theorem B1456123 : Blo 1293965 1456123 := bstep (se 1 (by rfl) ⟨1092092, by rfl⟩ : syracuseStep 1456123 = 2184185) B2184185
theorem B2185319 : Blo 1293965 2185319 := bstep (se 1 (by rfl) ⟨1638989, by rfl⟩ : syracuseStep 2185319 = 3277979) B3277979
theorem B4372703 : Blo 1293965 4372703 := bstep (se 1 (by rfl) ⟨3279527, by rfl⟩ : syracuseStep 4372703 = 6559055) B6559055
theorem B4913567 : Blo 1293965 4913567 := bstep (se 1 (by rfl) ⟨3685175, by rfl⟩ : syracuseStep 4913567 = 7370351) B7370351
theorem B227080979 : Blo 1293965 227080979 := bstep (se 1 (by rfl) ⟨170310734, by rfl⟩ : syracuseStep 227080979 = 340621469) B340621469
theorem B2915099 : Blo 1293965 2915099 := bstep (se 1 (by rfl) ⟨2186324, by rfl⟩ : syracuseStep 2915099 = 4372649) B4372649
theorem B4373405 : Blo 1293965 4373405 := bstep (se 3 (by rfl) ⟨820013, by rfl⟩ : syracuseStep 4373405 = 1640027) B1640027
theorem B2186183 : Blo 1293965 2186183 := bstep (se 1 (by rfl) ⟨1639637, by rfl⟩ : syracuseStep 2186183 = 3279275) B3279275
theorem B7371809 : Blo 1293965 7371809 := bstep (se 2 (by rfl) ⟨2764428, by rfl⟩ : syracuseStep 7371809 = 5528857) B5528857
theorem B2456639 : Blo 1293965 2456639 := bstep (se 1 (by rfl) ⟨1842479, by rfl⟩ : syracuseStep 2456639 = 3684959) B3684959
theorem B2333791 : Blo 1293965 2333791 := bstep (se 1 (by rfl) ⟨1750343, by rfl⟩ : syracuseStep 2333791 = 3500687) B3500687
theorem B39861719 : Blo 1293965 39861719 := bstep (se 1 (by rfl) ⟨29896289, by rfl⟩ : syracuseStep 39861719 = 59792579) B59792579
theorem B1940975 : Blo 1293965 1940975 := bstep (se 1 (by rfl) ⟨1455731, by rfl⟩ : syracuseStep 1940975 = 2911463) B2911463
theorem B8855095 : Blo 1293965 8855095 := bstep (se 1 (by rfl) ⟨6641321, by rfl⟩ : syracuseStep 8855095 = 13282643) B13282643
theorem B1941407 : Blo 1293965 1941407 := bstep (se 1 (by rfl) ⟨1456055, by rfl⟩ : syracuseStep 1941407 = 2912111) B2912111
theorem B1294407 : Blo 1293965 1294407 := bstep (se 1 (by rfl) ⟨970805, by rfl⟩ : syracuseStep 1294407 = 1941611) B1941611
theorem B3276895 : Blo 1293965 3276895 := bstep (se 1 (by rfl) ⟨2457671, by rfl⟩ : syracuseStep 3276895 = 4915343) B4915343
theorem B2457695 : Blo 1293965 2457695 := bstep (se 1 (by rfl) ⟨1843271, by rfl⟩ : syracuseStep 2457695 = 3686543) B3686543
theorem B1294491 : Blo 1293965 1294491 := bstep (se 1 (by rfl) ⟨970868, by rfl⟩ : syracuseStep 1294491 = 1941737) B1941737
theorem B22110569 : Blo 1293965 22110569 := bstep (se 2 (by rfl) ⟨8291463, by rfl⟩ : syracuseStep 22110569 = 16582927) B16582927
theorem B1942175 : Blo 1293965 1942175 := bstep (se 1 (by rfl) ⟨1456631, by rfl⟩ : syracuseStep 1942175 = 2913263) B2913263
theorem B11059901 : Blo 1293965 11059901 := bstep (se 3 (by rfl) ⟨2073731, by rfl⟩ : syracuseStep 11059901 = 4147463) B4147463
theorem B3277543 : Blo 1293965 3277543 := bstep (se 1 (by rfl) ⟨2458157, by rfl⟩ : syracuseStep 3277543 = 4916315) B4916315
theorem B10502945 : Blo 1293965 10502945 := bstep (se 2 (by rfl) ⟨3938604, by rfl⟩ : syracuseStep 10502945 = 7877209) B7877209
theorem B1942343 : Blo 1293965 1942343 := bstep (se 1 (by rfl) ⟨1456757, by rfl⟩ : syracuseStep 1942343 = 2913515) B2913515
theorem B3277817 : Blo 1293965 3277817 := bstep (se 2 (by rfl) ⟨1229181, by rfl⟩ : syracuseStep 3277817 = 2458363) B2458363
theorem B1295359 : Blo 1293965 1295359 := bstep (se 1 (by rfl) ⟨971519, by rfl⟩ : syracuseStep 1295359 = 1943039) B1943039
theorem B1295643 : Blo 1293965 1295643 := bstep (se 1 (by rfl) ⟨971732, by rfl⟩ : syracuseStep 1295643 = 1943465) B1943465
theorem B1943399 : Blo 1293965 1943399 := bstep (se 1 (by rfl) ⟨1457549, by rfl⟩ : syracuseStep 1943399 = 2915099) B2915099
theorem B8406979 : Blo 1293965 8406979 := bstep (se 1 (by rfl) ⟨6305234, by rfl⟩ : syracuseStep 8406979 = 12610469) B12610469
theorem B22431775 : Blo 1293965 22431775 := bstep (se 1 (by rfl) ⟨16823831, by rfl⟩ : syracuseStep 22431775 = 33647663) B33647663
theorem B11806793 : Blo 1293965 11806793 := bstep (se 2 (by rfl) ⟨4427547, by rfl⟩ : syracuseStep 11806793 = 8855095) B8855095
theorem B6555977 : Blo 1293965 6555977 := bstep (se 2 (by rfl) ⟨2458491, by rfl⟩ : syracuseStep 6555977 = 4916983) B4916983
theorem B3688831 : Blo 1293965 3688831 := bstep (se 1 (by rfl) ⟨2766623, by rfl⟩ : syracuseStep 3688831 = 5533247) B5533247
theorem B12446423 : Blo 1293965 12446423 := bstep (se 1 (by rfl) ⟨9334817, by rfl⟩ : syracuseStep 12446423 = 18669635) B18669635
theorem B14003225 : Blo 1293965 14003225 := bstep (se 2 (by rfl) ⟨5251209, by rfl⟩ : syracuseStep 14003225 = 10502419) B10502419
theorem B2952283 : Blo 1293965 2952283 := bstep (se 1 (by rfl) ⟨2214212, by rfl⟩ : syracuseStep 2952283 = 4428425) B4428425
theorem B12446885 : Blo 1293965 12446885 := bstep (se 4 (by rfl) ⟨1166895, by rfl⟩ : syracuseStep 12446885 = 2333791) B2333791
theorem B3280135 : Blo 1293965 3280135 := bstep (se 1 (by rfl) ⟨2460101, by rfl⟩ : syracuseStep 3280135 = 4920203) B4920203
theorem B2911535 : Blo 1293965 2911535 := bstep (se 1 (by rfl) ⟨2183651, by rfl⟩ : syracuseStep 2911535 = 4367303) B4367303
theorem B5533231 : Blo 1293965 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B2911823 : Blo 1293965 2911823 := bstep (se 1 (by rfl) ⟨2183867, by rfl⟩ : syracuseStep 2911823 = 4367735) B4367735
theorem B24907607 : Blo 1293965 24907607 := bstep (se 1 (by rfl) ⟨18680705, by rfl⟩ : syracuseStep 24907607 = 37361411) B37361411
theorem B2764847 : Blo 1293965 2764847 := bstep (se 1 (by rfl) ⟨2073635, by rfl⟩ : syracuseStep 2764847 = 4147271) B4147271
theorem B2912363 : Blo 1293965 2912363 := bstep (se 1 (by rfl) ⟨2184272, by rfl⟩ : syracuseStep 2912363 = 4368545) B4368545
theorem B2912633 : Blo 1293965 2912633 := bstep (se 2 (by rfl) ⟨1092237, by rfl⟩ : syracuseStep 2912633 = 2184475) B2184475
theorem B2912993 : Blo 1293965 2912993 := bstep (se 2 (by rfl) ⟨1092372, by rfl⟩ : syracuseStep 2912993 = 2184745) B2184745
theorem B4371623 : Blo 1293965 4371623 := bstep (se 1 (by rfl) ⟨3278717, by rfl⟩ : syracuseStep 4371623 = 6557435) B6557435
theorem B5534887 : Blo 1293965 5534887 := bstep (se 1 (by rfl) ⟨4151165, by rfl⟩ : syracuseStep 5534887 = 8302331) B8302331
theorem B2913983 : Blo 1293965 2913983 := bstep (se 1 (by rfl) ⟨2185487, by rfl⟩ : syracuseStep 2913983 = 4370975) B4370975
theorem B3151975 : Blo 1293965 3151975 := bstep (se 1 (by rfl) ⟨2363981, by rfl⟩ : syracuseStep 3151975 = 4727963) B4727963
theorem B22141187 : Blo 1293965 22141187 := bstep (se 1 (by rfl) ⟨16605890, by rfl⟩ : syracuseStep 22141187 = 33211781) B33211781
theorem B2914919 : Blo 1293965 2914919 := bstep (se 1 (by rfl) ⟨2186189, by rfl⟩ : syracuseStep 2914919 = 4372379) B4372379
theorem B1456879 : Blo 1293965 1456879 := bstep (se 1 (by rfl) ⟨1092659, by rfl⟩ : syracuseStep 1456879 = 2185319) B2185319
theorem B2915135 : Blo 1293965 2915135 := bstep (se 1 (by rfl) ⟨2186351, by rfl⟩ : syracuseStep 2915135 = 4372703) B4372703
theorem B3275711 : Blo 1293965 3275711 := bstep (se 1 (by rfl) ⟨2456783, by rfl⟩ : syracuseStep 3275711 = 4913567) B4913567
theorem B39877757 : Blo 1293965 39877757 := bstep (se 3 (by rfl) ⟨7477079, by rfl⟩ : syracuseStep 39877757 = 14954159) B14954159
theorem B151387319 : Blo 1293965 151387319 := bstep (se 1 (by rfl) ⟨113540489, by rfl⟩ : syracuseStep 151387319 = 227080979) B227080979
theorem B2915603 : Blo 1293965 2915603 := bstep (se 1 (by rfl) ⟨2186702, by rfl⟩ : syracuseStep 2915603 = 4373405) B4373405
theorem B159407389 : Blo 1293965 159407389 := bstep (se 3 (by rfl) ⟨29888885, by rfl⟩ : syracuseStep 159407389 = 59777771) B59777771
theorem B1457455 : Blo 1293965 1457455 := bstep (se 1 (by rfl) ⟨1093091, by rfl⟩ : syracuseStep 1457455 = 2186183) B2186183
theorem B4914539 : Blo 1293965 4914539 := bstep (se 1 (by rfl) ⟨3685904, by rfl⟩ : syracuseStep 4914539 = 7371809) B7371809
theorem B1637759 : Blo 1293965 1637759 := bstep (se 1 (by rfl) ⟨1228319, by rfl⟩ : syracuseStep 1637759 = 2456639) B2456639
theorem B26574479 : Blo 1293965 26574479 := bstep (se 1 (by rfl) ⟨19930859, by rfl⟩ : syracuseStep 26574479 = 39861719) B39861719
theorem B1293983 : Blo 1293965 1293983 := bstep (se 1 (by rfl) ⟨970487, by rfl⟩ : syracuseStep 1293983 = 1940975) B1940975
theorem B7872167 : Blo 1293965 7872167 := bstep (se 1 (by rfl) ⟨5904125, by rfl⟩ : syracuseStep 7872167 = 11808251) B11808251
theorem B1294271 : Blo 1293965 1294271 := bstep (se 1 (by rfl) ⟨970703, by rfl⟩ : syracuseStep 1294271 = 1941407) B1941407
theorem B1941497 : Blo 1293965 1941497 := bstep (se 2 (by rfl) ⟨728061, by rfl⟩ : syracuseStep 1941497 = 1456123) B1456123
theorem B1843231 : Blo 1293965 1843231 := bstep (se 1 (by rfl) ⟨1382423, by rfl⟩ : syracuseStep 1843231 = 2764847) B2764847
theorem B29909033 : Blo 1293965 29909033 := bstep (se 2 (by rfl) ⟨11215887, by rfl⟩ : syracuseStep 29909033 = 22431775) B22431775
theorem B1638463 : Blo 1293965 1638463 := bstep (se 1 (by rfl) ⟨1228847, by rfl⟩ : syracuseStep 1638463 = 2457695) B2457695
theorem B1941575 : Blo 1293965 1941575 := bstep (se 1 (by rfl) ⟨1456181, by rfl⟩ : syracuseStep 1941575 = 2912363) B2912363
theorem B4202633 : Blo 1293965 4202633 := bstep (se 2 (by rfl) ⟨1575987, by rfl⟩ : syracuseStep 4202633 = 3151975) B3151975
theorem B1941755 : Blo 1293965 1941755 := bstep (se 1 (by rfl) ⟨1456316, by rfl⟩ : syracuseStep 1941755 = 2912633) B2912633
theorem B1294783 : Blo 1293965 1294783 := bstep (se 1 (by rfl) ⟨971087, by rfl⟩ : syracuseStep 1294783 = 1942175) B1942175
theorem B7373267 : Blo 1293965 7373267 := bstep (se 1 (by rfl) ⟨5529950, by rfl⟩ : syracuseStep 7373267 = 11059901) B11059901
theorem B1941995 : Blo 1293965 1941995 := bstep (se 1 (by rfl) ⟨1456496, by rfl⟩ : syracuseStep 1941995 = 2912993) B2912993
theorem B1294895 : Blo 1293965 1294895 := bstep (se 1 (by rfl) ⟨971171, by rfl⟩ : syracuseStep 1294895 = 1942343) B1942343
theorem B1942505 : Blo 1293965 1942505 := bstep (se 2 (by rfl) ⟨728439, by rfl⟩ : syracuseStep 1942505 = 1456879) B1456879
theorem B4367357 : Blo 1293965 4367357 := bstep (se 3 (by rfl) ⟨818879, by rfl⟩ : syracuseStep 4367357 = 1637759) B1637759
theorem B1942655 : Blo 1293965 1942655 := bstep (se 1 (by rfl) ⟨1456991, by rfl⟩ : syracuseStep 1942655 = 2913983) B2913983
theorem B1295599 : Blo 1293965 1295599 := bstep (se 1 (by rfl) ⟨971699, by rfl⟩ : syracuseStep 1295599 = 1943399) B1943399
theorem B212543185 : Blo 1293965 212543185 := bstep (se 2 (by rfl) ⟨79703694, by rfl⟩ : syracuseStep 212543185 = 159407389) B159407389
theorem B1943273 : Blo 1293965 1943273 := bstep (se 2 (by rfl) ⟨728727, by rfl⟩ : syracuseStep 1943273 = 1457455) B1457455
theorem B1943279 : Blo 1293965 1943279 := bstep (se 1 (by rfl) ⟨1457459, by rfl⟩ : syracuseStep 1943279 = 2914919) B2914919
theorem B1943423 : Blo 1293965 1943423 := bstep (se 1 (by rfl) ⟨1457567, by rfl⟩ : syracuseStep 1943423 = 2915135) B2915135
theorem B26585171 : Blo 1293965 26585171 := bstep (se 1 (by rfl) ⟨19938878, by rfl⟩ : syracuseStep 26585171 = 39877757) B39877757
theorem B1943735 : Blo 1293965 1943735 := bstep (se 1 (by rfl) ⟨1457801, by rfl⟩ : syracuseStep 1943735 = 2915603) B2915603
theorem B44837221 : Blo 1293965 44837221 := bstep (se 4 (by rfl) ⟨4203489, by rfl⟩ : syracuseStep 44837221 = 8406979) B8406979
theorem B4369193 : Blo 1293965 4369193 := bstep (se 2 (by rfl) ⟨1638447, by rfl⟩ : syracuseStep 4369193 = 3276895) B3276895
theorem B14740379 : Blo 1293965 14740379 := bstep (se 1 (by rfl) ⟨11055284, by rfl⟩ : syracuseStep 14740379 = 22110569) B22110569
theorem B4918441 : Blo 1293965 4918441 := bstep (se 2 (by rfl) ⟨1844415, by rfl⟩ : syracuseStep 4918441 = 3688831) B3688831
theorem B4370057 : Blo 1293965 4370057 := bstep (se 2 (by rfl) ⟨1638771, by rfl⟩ : syracuseStep 4370057 = 3277543) B3277543
theorem B3936377 : Blo 1293965 3936377 := bstep (se 2 (by rfl) ⟨1476141, by rfl⟩ : syracuseStep 3936377 = 2952283) B2952283
theorem B4370651 : Blo 1293965 4370651 := bstep (se 1 (by rfl) ⟨3277988, by rfl⟩ : syracuseStep 4370651 = 6555977) B6555977
theorem B20992445 : Blo 1293965 20992445 := bstep (se 3 (by rfl) ⟨3936083, by rfl⟩ : syracuseStep 20992445 = 7872167) B7872167
theorem B2183807 : Blo 1293965 2183807 := bstep (se 1 (by rfl) ⟨1637855, by rfl⟩ : syracuseStep 2183807 = 3275711) B3275711
theorem B9335483 : Blo 1293965 9335483 := bstep (se 1 (by rfl) ⟨7001612, by rfl⟩ : syracuseStep 9335483 = 14003225) B14003225
theorem B7377641 : Blo 1293965 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B17716319 : Blo 1293965 17716319 := bstep (se 1 (by rfl) ⟨13287239, by rfl⟩ : syracuseStep 17716319 = 26574479) B26574479
theorem B7001963 : Blo 1293965 7001963 := bstep (se 1 (by rfl) ⟨5251472, by rfl⟩ : syracuseStep 7001963 = 10502945) B10502945
theorem B2185211 : Blo 1293965 2185211 := bstep (se 1 (by rfl) ⟨1638908, by rfl⟩ : syracuseStep 2185211 = 3277817) B3277817
theorem B2914415 : Blo 1293965 2914415 := bstep (se 1 (by rfl) ⟨2185811, by rfl⟩ : syracuseStep 2914415 = 4371623) B4371623
theorem B7871195 : Blo 1293965 7871195 := bstep (se 1 (by rfl) ⟨5903396, by rfl⟩ : syracuseStep 7871195 = 11806793) B11806793
theorem B14760791 : Blo 1293965 14760791 := bstep (se 1 (by rfl) ⟨11070593, by rfl⟩ : syracuseStep 14760791 = 22141187) B22141187
theorem B7379849 : Blo 1293965 7379849 := bstep (se 2 (by rfl) ⟨2767443, by rfl⟩ : syracuseStep 7379849 = 5534887) B5534887
theorem B4373513 : Blo 1293965 4373513 := bstep (se 2 (by rfl) ⟨1640067, by rfl⟩ : syracuseStep 4373513 = 3280135) B3280135
theorem B8297615 : Blo 1293965 8297615 := bstep (se 1 (by rfl) ⟨6223211, by rfl⟩ : syracuseStep 8297615 = 12446423) B12446423
theorem B8297923 : Blo 1293965 8297923 := bstep (se 1 (by rfl) ⟨6223442, by rfl⟩ : syracuseStep 8297923 = 12446885) B12446885
theorem B100924879 : Blo 1293965 100924879 := bstep (se 1 (by rfl) ⟨75693659, by rfl⟩ : syracuseStep 100924879 = 151387319) B151387319
theorem B1941023 : Blo 1293965 1941023 := bstep (se 1 (by rfl) ⟨1455767, by rfl⟩ : syracuseStep 1941023 = 2911535) B2911535
theorem B3276359 : Blo 1293965 3276359 := bstep (se 1 (by rfl) ⟨2457269, by rfl⟩ : syracuseStep 3276359 = 4914539) B4914539
theorem B1941215 : Blo 1293965 1941215 := bstep (se 1 (by rfl) ⟨1455911, by rfl⟩ : syracuseStep 1941215 = 2911823) B2911823
theorem B16605071 : Blo 1293965 16605071 := bstep (se 1 (by rfl) ⟨12453803, by rfl⟩ : syracuseStep 16605071 = 24907607) B24907607
theorem B1294331 : Blo 1293965 1294331 := bstep (se 1 (by rfl) ⟨970748, by rfl⟩ : syracuseStep 1294331 = 1941497) B1941497
theorem B19939355 : Blo 1293965 19939355 := bstep (se 1 (by rfl) ⟨14954516, by rfl⟩ : syracuseStep 19939355 = 29909033) B29909033
theorem B2457641 : Blo 1293965 2457641 := bstep (se 2 (by rfl) ⟨921615, by rfl⟩ : syracuseStep 2457641 = 1843231) B1843231
theorem B1294383 : Blo 1293965 1294383 := bstep (se 1 (by rfl) ⟨970787, by rfl⟩ : syracuseStep 1294383 = 1941575) B1941575
theorem B2801755 : Blo 1293965 2801755 := bstep (se 1 (by rfl) ⟨2101316, by rfl⟩ : syracuseStep 2801755 = 4202633) B4202633
theorem B1294503 : Blo 1293965 1294503 := bstep (se 1 (by rfl) ⟨970877, by rfl⟩ : syracuseStep 1294503 = 1941755) B1941755
theorem B4915511 : Blo 1293965 4915511 := bstep (se 1 (by rfl) ⟨3686633, by rfl⟩ : syracuseStep 4915511 = 7373267) B7373267
theorem B1294663 : Blo 1293965 1294663 := bstep (se 1 (by rfl) ⟨970997, by rfl⟩ : syracuseStep 1294663 = 1941995) B1941995
theorem B1295003 : Blo 1293965 1295003 := bstep (se 1 (by rfl) ⟨971252, by rfl⟩ : syracuseStep 1295003 = 1942505) B1942505
theorem B1295103 : Blo 1293965 1295103 := bstep (se 1 (by rfl) ⟨971327, by rfl⟩ : syracuseStep 1295103 = 1942655) B1942655
theorem B1295515 : Blo 1293965 1295515 := bstep (se 1 (by rfl) ⟨971636, by rfl⟩ : syracuseStep 1295515 = 1943273) B1943273
theorem B1295519 : Blo 1293965 1295519 := bstep (se 1 (by rfl) ⟨971639, by rfl⟩ : syracuseStep 1295519 = 1943279) B1943279
theorem B1295615 : Blo 1293965 1295615 := bstep (se 1 (by rfl) ⟨971711, by rfl⟩ : syracuseStep 1295615 = 1943423) B1943423
theorem B1942943 : Blo 1293965 1942943 := bstep (se 1 (by rfl) ⟨1457207, by rfl⟩ : syracuseStep 1942943 = 2914415) B2914415
theorem B1295823 : Blo 1293965 1295823 := bstep (se 1 (by rfl) ⟨971867, by rfl⟩ : syracuseStep 1295823 = 1943735) B1943735
theorem B9840527 : Blo 1293965 9840527 := bstep (se 1 (by rfl) ⟨7380395, by rfl⟩ : syracuseStep 9840527 = 14760791) B14760791
theorem B5531743 : Blo 1293965 5531743 := bstep (se 1 (by rfl) ⟨4148807, by rfl⟩ : syracuseStep 5531743 = 8297615) B8297615
theorem B11070047 : Blo 1293965 11070047 := bstep (se 1 (by rfl) ⟨8302535, by rfl⟩ : syracuseStep 11070047 = 16605071) B16605071
theorem B2624251 : Blo 1293965 2624251 := bstep (se 1 (by rfl) ⟨1968188, by rfl⟩ : syracuseStep 2624251 = 3936377) B3936377
theorem B13994963 : Blo 1293965 13994963 := bstep (se 1 (by rfl) ⟨10496222, by rfl⟩ : syracuseStep 13994963 = 20992445) B20992445
theorem B4918427 : Blo 1293965 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B2911571 : Blo 1293965 2911571 := bstep (se 1 (by rfl) ⟨2183678, by rfl⟩ : syracuseStep 2911571 = 4367357) B4367357
theorem B17723447 : Blo 1293965 17723447 := bstep (se 1 (by rfl) ⟨13292585, by rfl⟩ : syracuseStep 17723447 = 26585171) B26585171
theorem B6557921 : Blo 1293965 6557921 := bstep (se 2 (by rfl) ⟨2459220, by rfl⟩ : syracuseStep 6557921 = 4918441) B4918441
theorem B5247463 : Blo 1293965 5247463 := bstep (se 1 (by rfl) ⟨3935597, by rfl⟩ : syracuseStep 5247463 = 7871195) B7871195
theorem B2912795 : Blo 1293965 2912795 := bstep (se 1 (by rfl) ⟨2184596, by rfl⟩ : syracuseStep 2912795 = 4369193) B4369193
theorem B11063897 : Blo 1293965 11063897 := bstep (se 2 (by rfl) ⟨4148961, by rfl⟩ : syracuseStep 11063897 = 8297923) B8297923
theorem B4919899 : Blo 1293965 4919899 := bstep (se 1 (by rfl) ⟨3689924, by rfl⟩ : syracuseStep 4919899 = 7379849) B7379849
theorem B9826919 : Blo 1293965 9826919 := bstep (se 1 (by rfl) ⟨7370189, by rfl⟩ : syracuseStep 9826919 = 14740379) B14740379
theorem B134566505 : Blo 1293965 134566505 := bstep (se 2 (by rfl) ⟨50462439, by rfl⟩ : syracuseStep 134566505 = 100924879) B100924879
theorem B283390913 : Blo 1293965 283390913 := bstep (se 2 (by rfl) ⟨106271592, by rfl⟩ : syracuseStep 283390913 = 212543185) B212543185
theorem B2184239 : Blo 1293965 2184239 := bstep (se 1 (by rfl) ⟨1638179, by rfl⟩ : syracuseStep 2184239 = 3276359) B3276359
theorem B2913371 : Blo 1293965 2913371 := bstep (se 1 (by rfl) ⟨2185028, by rfl⟩ : syracuseStep 2913371 = 4370057) B4370057
theorem B2184617 : Blo 1293965 2184617 := bstep (se 2 (by rfl) ⟨819231, by rfl⟩ : syracuseStep 2184617 = 1638463) B1638463
theorem B2913767 : Blo 1293965 2913767 := bstep (se 1 (by rfl) ⟨2185325, by rfl⟩ : syracuseStep 2913767 = 4370651) B4370651
theorem B1455871 : Blo 1293965 1455871 := bstep (se 1 (by rfl) ⟨1091903, by rfl⟩ : syracuseStep 1455871 = 2183807) B2183807
theorem B6223655 : Blo 1293965 6223655 := bstep (se 1 (by rfl) ⟨4667741, by rfl⟩ : syracuseStep 6223655 = 9335483) B9335483
theorem B59782961 : Blo 1293965 59782961 := bstep (se 2 (by rfl) ⟨22418610, by rfl⟩ : syracuseStep 59782961 = 44837221) B44837221
theorem B11810879 : Blo 1293965 11810879 := bstep (se 1 (by rfl) ⟨8858159, by rfl⟩ : syracuseStep 11810879 = 17716319) B17716319
theorem B4667975 : Blo 1293965 4667975 := bstep (se 1 (by rfl) ⟨3500981, by rfl⟩ : syracuseStep 4667975 = 7001963) B7001963
theorem B1456807 : Blo 1293965 1456807 := bstep (se 1 (by rfl) ⟨1092605, by rfl⟩ : syracuseStep 1456807 = 2185211) B2185211
theorem B2915675 : Blo 1293965 2915675 := bstep (se 1 (by rfl) ⟨2186756, by rfl⟩ : syracuseStep 2915675 = 4373513) B4373513
theorem B1294015 : Blo 1293965 1294015 := bstep (se 1 (by rfl) ⟨970511, by rfl⟩ : syracuseStep 1294015 = 1941023) B1941023
theorem B1294143 : Blo 1293965 1294143 := bstep (se 1 (by rfl) ⟨970607, by rfl⟩ : syracuseStep 1294143 = 1941215) B1941215
theorem B6553709 : Blo 1293965 6553709 := bstep (se 3 (by rfl) ⟨1228820, by rfl⟩ : syracuseStep 6553709 = 2457641) B2457641
theorem B3277007 : Blo 1293965 3277007 := bstep (se 1 (by rfl) ⟨2457755, by rfl⟩ : syracuseStep 3277007 = 4915511) B4915511
theorem B1941863 : Blo 1293965 1941863 := bstep (se 1 (by rfl) ⟨1456397, by rfl⟩ : syracuseStep 1941863 = 2912795) B2912795
theorem B89711003 : Blo 1293965 89711003 := bstep (se 1 (by rfl) ⟨67283252, by rfl⟩ : syracuseStep 89711003 = 134566505) B134566505
theorem B14942693 : Blo 1293965 14942693 := bstep (se 4 (by rfl) ⟨1400877, by rfl⟩ : syracuseStep 14942693 = 2801755) B2801755
theorem B6996617 : Blo 1293965 6996617 := bstep (se 2 (by rfl) ⟨2623731, by rfl⟩ : syracuseStep 6996617 = 5247463) B5247463
theorem B1942247 : Blo 1293965 1942247 := bstep (se 1 (by rfl) ⟨1456685, by rfl⟩ : syracuseStep 1942247 = 2913371) B2913371
theorem B1942409 : Blo 1293965 1942409 := bstep (se 2 (by rfl) ⟨728403, by rfl⟩ : syracuseStep 1942409 = 1456807) B1456807
theorem B1295295 : Blo 1293965 1295295 := bstep (se 1 (by rfl) ⟨971471, by rfl⟩ : syracuseStep 1295295 = 1942943) B1942943
theorem B1942511 : Blo 1293965 1942511 := bstep (se 1 (by rfl) ⟨1456883, by rfl⟩ : syracuseStep 1942511 = 2913767) B2913767
theorem B3499001 : Blo 1293965 3499001 := bstep (se 2 (by rfl) ⟨1312125, by rfl⟩ : syracuseStep 3499001 = 2624251) B2624251
theorem B7873919 : Blo 1293965 7873919 := bstep (se 1 (by rfl) ⟨5905439, by rfl⟩ : syracuseStep 7873919 = 11810879) B11810879
theorem B3278951 : Blo 1293965 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B1943783 : Blo 1293965 1943783 := bstep (se 1 (by rfl) ⟨1457837, by rfl⟩ : syracuseStep 1943783 = 2915675) B2915675
theorem B11815631 : Blo 1293965 11815631 := bstep (se 1 (by rfl) ⟨8861723, by rfl⟩ : syracuseStep 11815631 = 17723447) B17723447
theorem B7375657 : Blo 1293965 7375657 := bstep (se 2 (by rfl) ⟨2765871, by rfl⟩ : syracuseStep 7375657 = 5531743) B5531743
theorem B7375931 : Blo 1293965 7375931 := bstep (se 1 (by rfl) ⟨5531948, by rfl⟩ : syracuseStep 7375931 = 11063897) B11063897
theorem B188927275 : Blo 1293965 188927275 := bstep (se 1 (by rfl) ⟨141695456, by rfl⟩ : syracuseStep 188927275 = 283390913) B283390913
theorem B159421229 : Blo 1293965 159421229 := bstep (se 3 (by rfl) ⟨29891480, by rfl⟩ : syracuseStep 159421229 = 59782961) B59782961
theorem B13292903 : Blo 1293965 13292903 := bstep (se 1 (by rfl) ⟨9969677, by rfl⟩ : syracuseStep 13292903 = 19939355) B19939355
theorem B4371947 : Blo 1293965 4371947 := bstep (se 1 (by rfl) ⟨3278960, by rfl⟩ : syracuseStep 4371947 = 6557921) B6557921
theorem B6551279 : Blo 1293965 6551279 := bstep (se 1 (by rfl) ⟨4913459, by rfl⟩ : syracuseStep 6551279 = 9826919) B9826919
theorem B1456159 : Blo 1293965 1456159 := bstep (se 1 (by rfl) ⟨1092119, by rfl⟩ : syracuseStep 1456159 = 2184239) B2184239
theorem B6559865 : Blo 1293965 6559865 := bstep (se 2 (by rfl) ⟨2459949, by rfl⟩ : syracuseStep 6559865 = 4919899) B4919899
theorem B1456411 : Blo 1293965 1456411 := bstep (se 1 (by rfl) ⟨1092308, by rfl⟩ : syracuseStep 1456411 = 2184617) B2184617
theorem B6560351 : Blo 1293965 6560351 := bstep (se 1 (by rfl) ⟨4920263, by rfl⟩ : syracuseStep 6560351 = 9840527) B9840527
theorem B3111983 : Blo 1293965 3111983 := bstep (se 1 (by rfl) ⟨2333987, by rfl⟩ : syracuseStep 3111983 = 4667975) B4667975
theorem B7380031 : Blo 1293965 7380031 := bstep (se 1 (by rfl) ⟨5535023, by rfl⟩ : syracuseStep 7380031 = 11070047) B11070047
theorem B9329975 : Blo 1293965 9329975 := bstep (se 1 (by rfl) ⟨6997481, by rfl⟩ : syracuseStep 9329975 = 13994963) B13994963
theorem B16596413 : Blo 1293965 16596413 := bstep (se 3 (by rfl) ⟨3111827, by rfl⟩ : syracuseStep 16596413 = 6223655) B6223655
theorem B1941047 : Blo 1293965 1941047 := bstep (se 1 (by rfl) ⟨1455785, by rfl⟩ : syracuseStep 1941047 = 2911571) B2911571
theorem B1941161 : Blo 1293965 1941161 := bstep (se 2 (by rfl) ⟨727935, by rfl⟩ : syracuseStep 1941161 = 1455871) B1455871
theorem B1941545 : Blo 1293965 1941545 := bstep (se 2 (by rfl) ⟨728079, by rfl⟩ : syracuseStep 1941545 = 1456159) B1456159
theorem B1294575 : Blo 1293965 1294575 := bstep (se 1 (by rfl) ⟨970931, by rfl⟩ : syracuseStep 1294575 = 1941863) B1941863
theorem B9961795 : Blo 1293965 9961795 := bstep (se 1 (by rfl) ⟨7471346, by rfl⟩ : syracuseStep 9961795 = 14942693) B14942693
theorem B1941881 : Blo 1293965 1941881 := bstep (se 2 (by rfl) ⟨728205, by rfl⟩ : syracuseStep 1941881 = 1456411) B1456411
theorem B1294831 : Blo 1293965 1294831 := bstep (se 1 (by rfl) ⟨971123, by rfl⟩ : syracuseStep 1294831 = 1942247) B1942247
theorem B1294939 : Blo 1293965 1294939 := bstep (se 1 (by rfl) ⟨971204, by rfl⟩ : syracuseStep 1294939 = 1942409) B1942409
theorem B1295007 : Blo 1293965 1295007 := bstep (se 1 (by rfl) ⟨971255, by rfl⟩ : syracuseStep 1295007 = 1942511) B1942511
theorem B4367519 : Blo 1293965 4367519 := bstep (se 1 (by rfl) ⟨3275639, by rfl⟩ : syracuseStep 4367519 = 6551279) B6551279
theorem B9840041 : Blo 1293965 9840041 := bstep (se 2 (by rfl) ⟨3690015, by rfl⟩ : syracuseStep 9840041 = 7380031) B7380031
theorem B1295855 : Blo 1293965 1295855 := bstep (se 1 (by rfl) ⟨971891, by rfl⟩ : syracuseStep 1295855 = 1943783) B1943783
theorem B2074655 : Blo 1293965 2074655 := bstep (se 1 (by rfl) ⟨1555991, by rfl⟩ : syracuseStep 2074655 = 3111983) B3111983
theorem B4917287 : Blo 1293965 4917287 := bstep (se 1 (by rfl) ⟨3687965, by rfl⟩ : syracuseStep 4917287 = 7375931) B7375931
theorem B6219983 : Blo 1293965 6219983 := bstep (se 1 (by rfl) ⟨4664987, by rfl⟩ : syracuseStep 6219983 = 9329975) B9329975
theorem B4369139 : Blo 1293965 4369139 := bstep (se 1 (by rfl) ⟨3276854, by rfl⟩ : syracuseStep 4369139 = 6553709) B6553709
theorem B4664411 : Blo 1293965 4664411 := bstep (se 1 (by rfl) ⟨3498308, by rfl⟩ : syracuseStep 4664411 = 6996617) B6996617
theorem B9834209 : Blo 1293965 9834209 := bstep (se 2 (by rfl) ⟨3687828, by rfl⟩ : syracuseStep 9834209 = 7375657) B7375657
theorem B7877087 : Blo 1293965 7877087 := bstep (se 1 (by rfl) ⟨5907815, by rfl⟩ : syracuseStep 7877087 = 11815631) B11815631
theorem B11064275 : Blo 1293965 11064275 := bstep (se 1 (by rfl) ⟨8298206, by rfl⟩ : syracuseStep 11064275 = 16596413) B16596413
theorem B2184671 : Blo 1293965 2184671 := bstep (se 1 (by rfl) ⟨1638503, by rfl⟩ : syracuseStep 2184671 = 3277007) B3277007
theorem B59807335 : Blo 1293965 59807335 := bstep (se 1 (by rfl) ⟨44855501, by rfl⟩ : syracuseStep 59807335 = 89711003) B89711003
theorem B106280819 : Blo 1293965 106280819 := bstep (se 1 (by rfl) ⟨79710614, by rfl⟩ : syracuseStep 106280819 = 159421229) B159421229
theorem B2332667 : Blo 1293965 2332667 := bstep (se 1 (by rfl) ⟨1749500, by rfl⟩ : syracuseStep 2332667 = 3499001) B3499001
theorem B8861935 : Blo 1293965 8861935 := bstep (se 1 (by rfl) ⟨6646451, by rfl⟩ : syracuseStep 8861935 = 13292903) B13292903
theorem B5249279 : Blo 1293965 5249279 := bstep (se 1 (by rfl) ⟨3936959, by rfl⟩ : syracuseStep 5249279 = 7873919) B7873919
theorem B2914631 : Blo 1293965 2914631 := bstep (se 1 (by rfl) ⟨2185973, by rfl⟩ : syracuseStep 2914631 = 4371947) B4371947
theorem B2185967 : Blo 1293965 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B4373243 : Blo 1293965 4373243 := bstep (se 1 (by rfl) ⟨3279932, by rfl⟩ : syracuseStep 4373243 = 6559865) B6559865
theorem B251903033 : Blo 1293965 251903033 := bstep (se 2 (by rfl) ⟨94463637, by rfl⟩ : syracuseStep 251903033 = 188927275) B188927275
theorem B4373567 : Blo 1293965 4373567 := bstep (se 1 (by rfl) ⟨3280175, by rfl⟩ : syracuseStep 4373567 = 6560351) B6560351
theorem B1294031 : Blo 1293965 1294031 := bstep (se 1 (by rfl) ⟨970523, by rfl⟩ : syracuseStep 1294031 = 1941047) B1941047
theorem B1294107 : Blo 1293965 1294107 := bstep (se 1 (by rfl) ⟨970580, by rfl⟩ : syracuseStep 1294107 = 1941161) B1941161
theorem B1294363 : Blo 1293965 1294363 := bstep (se 1 (by rfl) ⟨970772, by rfl⟩ : syracuseStep 1294363 = 1941545) B1941545
theorem B1294587 : Blo 1293965 1294587 := bstep (se 1 (by rfl) ⟨970940, by rfl⟩ : syracuseStep 1294587 = 1941881) B1941881
theorem B5251391 : Blo 1293965 5251391 := bstep (se 1 (by rfl) ⟨3938543, by rfl⟩ : syracuseStep 5251391 = 7877087) B7877087
theorem B70853879 : Blo 1293965 70853879 := bstep (se 1 (by rfl) ⟨53140409, by rfl⟩ : syracuseStep 70853879 = 106280819) B106280819
theorem B3278191 : Blo 1293965 3278191 := bstep (se 1 (by rfl) ⟨2458643, by rfl⟩ : syracuseStep 3278191 = 4917287) B4917287
theorem B4146655 : Blo 1293965 4146655 := bstep (se 1 (by rfl) ⟨3109991, by rfl⟩ : syracuseStep 4146655 = 6219983) B6219983
theorem B3499519 : Blo 1293965 3499519 := bstep (se 1 (by rfl) ⟨2624639, by rfl⟩ : syracuseStep 3499519 = 5249279) B5249279
theorem B1943087 : Blo 1293965 1943087 := bstep (se 1 (by rfl) ⟨1457315, by rfl⟩ : syracuseStep 1943087 = 2914631) B2914631
theorem B79743113 : Blo 1293965 79743113 := bstep (se 2 (by rfl) ⟨29903667, by rfl⟩ : syracuseStep 79743113 = 59807335) B59807335
theorem B6556139 : Blo 1293965 6556139 := bstep (se 1 (by rfl) ⟨4917104, by rfl⟩ : syracuseStep 6556139 = 9834209) B9834209
theorem B11815913 : Blo 1293965 11815913 := bstep (se 2 (by rfl) ⟨4430967, by rfl⟩ : syracuseStep 11815913 = 8861935) B8861935
theorem B13282393 : Blo 1293965 13282393 := bstep (se 2 (by rfl) ⟨4980897, by rfl⟩ : syracuseStep 13282393 = 9961795) B9961795
theorem B7376183 : Blo 1293965 7376183 := bstep (se 1 (by rfl) ⟨5532137, by rfl⟩ : syracuseStep 7376183 = 11064275) B11064275
theorem B2911679 : Blo 1293965 2911679 := bstep (se 1 (by rfl) ⟨2183759, by rfl⟩ : syracuseStep 2911679 = 4367519) B4367519
theorem B2912759 : Blo 1293965 2912759 := bstep (se 1 (by rfl) ⟨2184569, by rfl⟩ : syracuseStep 2912759 = 4369139) B4369139
theorem B3109607 : Blo 1293965 3109607 := bstep (se 1 (by rfl) ⟨2332205, by rfl⟩ : syracuseStep 3109607 = 4664411) B4664411
theorem B6560027 : Blo 1293965 6560027 := bstep (se 1 (by rfl) ⟨4920020, by rfl⟩ : syracuseStep 6560027 = 9840041) B9840041
theorem B1456447 : Blo 1293965 1456447 := bstep (se 1 (by rfl) ⟨1092335, by rfl⟩ : syracuseStep 1456447 = 2184671) B2184671
theorem B1555111 : Blo 1293965 1555111 := bstep (se 1 (by rfl) ⟨1166333, by rfl⟩ : syracuseStep 1555111 = 2332667) B2332667
theorem B1383103 : Blo 1293965 1383103 := bstep (se 1 (by rfl) ⟨1037327, by rfl⟩ : syracuseStep 1383103 = 2074655) B2074655
theorem B1457311 : Blo 1293965 1457311 := bstep (se 1 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 1457311 = 2185967) B2185967
theorem B2915495 : Blo 1293965 2915495 := bstep (se 1 (by rfl) ⟨2186621, by rfl⟩ : syracuseStep 2915495 = 4373243) B4373243
theorem B167935355 : Blo 1293965 167935355 := bstep (se 1 (by rfl) ⟨125951516, by rfl⟩ : syracuseStep 167935355 = 251903033) B251903033
theorem B2915711 : Blo 1293965 2915711 := bstep (se 1 (by rfl) ⟨2186783, by rfl⟩ : syracuseStep 2915711 = 4373567) B4373567
theorem B1941839 : Blo 1293965 1941839 := bstep (se 1 (by rfl) ⟨1456379, by rfl⟩ : syracuseStep 1941839 = 2912759) B2912759
theorem B1941929 : Blo 1293965 1941929 := bstep (se 2 (by rfl) ⟨728223, by rfl⟩ : syracuseStep 1941929 = 1456447) B1456447
theorem B2073071 : Blo 1293965 2073071 := bstep (se 1 (by rfl) ⟨1554803, by rfl⟩ : syracuseStep 2073071 = 3109607) B3109607
theorem B47235919 : Blo 1293965 47235919 := bstep (se 1 (by rfl) ⟨35426939, by rfl⟩ : syracuseStep 47235919 = 70853879) B70853879
theorem B2073481 : Blo 1293965 2073481 := bstep (se 2 (by rfl) ⟨777555, by rfl⟩ : syracuseStep 2073481 = 1555111) B1555111
theorem B1844137 : Blo 1293965 1844137 := bstep (se 2 (by rfl) ⟨691551, by rfl⟩ : syracuseStep 1844137 = 1383103) B1383103
theorem B1295391 : Blo 1293965 1295391 := bstep (se 1 (by rfl) ⟨971543, by rfl⟩ : syracuseStep 1295391 = 1943087) B1943087
theorem B1943081 : Blo 1293965 1943081 := bstep (se 2 (by rfl) ⟨728655, by rfl⟩ : syracuseStep 1943081 = 1457311) B1457311
theorem B1943663 : Blo 1293965 1943663 := bstep (se 1 (by rfl) ⟨1457747, by rfl⟩ : syracuseStep 1943663 = 2915495) B2915495
theorem B4917455 : Blo 1293965 4917455 := bstep (se 1 (by rfl) ⟨3688091, by rfl⟩ : syracuseStep 4917455 = 7376183) B7376183
theorem B1943807 : Blo 1293965 1943807 := bstep (se 1 (by rfl) ⟨1457855, by rfl⟩ : syracuseStep 1943807 = 2915711) B2915711
theorem B31509101 : Blo 1293965 31509101 := bstep (se 3 (by rfl) ⟨5907956, by rfl⟩ : syracuseStep 31509101 = 11815913) B11815913
theorem B3500927 : Blo 1293965 3500927 := bstep (se 1 (by rfl) ⟨2625695, by rfl⟩ : syracuseStep 3500927 = 5251391) B5251391
theorem B53162075 : Blo 1293965 53162075 := bstep (se 1 (by rfl) ⟨39871556, by rfl⟩ : syracuseStep 53162075 = 79743113) B79743113
theorem B4370759 : Blo 1293965 4370759 := bstep (se 1 (by rfl) ⟨3278069, by rfl⟩ : syracuseStep 4370759 = 6556139) B6556139
theorem B4370921 : Blo 1293965 4370921 := bstep (se 2 (by rfl) ⟨1639095, by rfl⟩ : syracuseStep 4370921 = 3278191) B3278191
theorem B4666025 : Blo 1293965 4666025 := bstep (se 2 (by rfl) ⟨1749759, by rfl⟩ : syracuseStep 4666025 = 3499519) B3499519
theorem B111956903 : Blo 1293965 111956903 := bstep (se 1 (by rfl) ⟨83967677, by rfl⟩ : syracuseStep 111956903 = 167935355) B167935355
theorem B17709857 : Blo 1293965 17709857 := bstep (se 2 (by rfl) ⟨6641196, by rfl⟩ : syracuseStep 17709857 = 13282393) B13282393
theorem B4373351 : Blo 1293965 4373351 := bstep (se 1 (by rfl) ⟨3280013, by rfl⟩ : syracuseStep 4373351 = 6560027) B6560027
theorem B5528873 : Blo 1293965 5528873 := bstep (se 2 (by rfl) ⟨2073327, by rfl⟩ : syracuseStep 5528873 = 4146655) B4146655
theorem B1941119 : Blo 1293965 1941119 := bstep (se 1 (by rfl) ⟨1455839, by rfl⟩ : syracuseStep 1941119 = 2911679) B2911679
theorem B1294559 : Blo 1293965 1294559 := bstep (se 1 (by rfl) ⟨970919, by rfl⟩ : syracuseStep 1294559 = 1941839) B1941839
theorem B1294619 : Blo 1293965 1294619 := bstep (se 1 (by rfl) ⟨970964, by rfl⟩ : syracuseStep 1294619 = 1941929) B1941929
theorem B74637935 : Blo 1293965 74637935 := bstep (se 1 (by rfl) ⟨55978451, by rfl⟩ : syracuseStep 74637935 = 111956903) B111956903
theorem B1295387 : Blo 1293965 1295387 := bstep (se 1 (by rfl) ⟨971540, by rfl⟩ : syracuseStep 1295387 = 1943081) B1943081
theorem B62981225 : Blo 1293965 62981225 := bstep (se 2 (by rfl) ⟨23617959, by rfl⟩ : syracuseStep 62981225 = 47235919) B47235919
theorem B2458849 : Blo 1293965 2458849 := bstep (se 2 (by rfl) ⟨922068, by rfl⟩ : syracuseStep 2458849 = 1844137) B1844137
theorem B1295775 : Blo 1293965 1295775 := bstep (se 1 (by rfl) ⟨971831, by rfl⟩ : syracuseStep 1295775 = 1943663) B1943663
theorem B3278303 : Blo 1293965 3278303 := bstep (se 1 (by rfl) ⟨2458727, by rfl⟩ : syracuseStep 3278303 = 4917455) B4917455
theorem B1295871 : Blo 1293965 1295871 := bstep (se 1 (by rfl) ⟨971903, by rfl⟩ : syracuseStep 1295871 = 1943807) B1943807
theorem B21006067 : Blo 1293965 21006067 := bstep (se 1 (by rfl) ⟨15754550, by rfl⟩ : syracuseStep 21006067 = 31509101) B31509101
theorem B11806571 : Blo 1293965 11806571 := bstep (se 1 (by rfl) ⟨8854928, by rfl⟩ : syracuseStep 11806571 = 17709857) B17709857
theorem B35441383 : Blo 1293965 35441383 := bstep (se 1 (by rfl) ⟨26581037, by rfl⟩ : syracuseStep 35441383 = 53162075) B53162075
theorem B2913839 : Blo 1293965 2913839 := bstep (se 1 (by rfl) ⟨2185379, by rfl⟩ : syracuseStep 2913839 = 4370759) B4370759
theorem B2913947 : Blo 1293965 2913947 := bstep (se 1 (by rfl) ⟨2185460, by rfl⟩ : syracuseStep 2913947 = 4370921) B4370921
theorem B5528189 : Blo 1293965 5528189 := bstep (se 3 (by rfl) ⟨1036535, by rfl⟩ : syracuseStep 5528189 = 2073071) B2073071
theorem B12442733 : Blo 1293965 12442733 := bstep (se 3 (by rfl) ⟨2333012, by rfl⟩ : syracuseStep 12442733 = 4666025) B4666025
theorem B2915567 : Blo 1293965 2915567 := bstep (se 1 (by rfl) ⟨2186675, by rfl⟩ : syracuseStep 2915567 = 4373351) B4373351
theorem B2333951 : Blo 1293965 2333951 := bstep (se 1 (by rfl) ⟨1750463, by rfl⟩ : syracuseStep 2333951 = 3500927) B3500927
theorem B11058565 : Blo 1293965 11058565 := bstep (se 4 (by rfl) ⟨1036740, by rfl⟩ : syracuseStep 11058565 = 2073481) B2073481
theorem B3685915 : Blo 1293965 3685915 := bstep (se 1 (by rfl) ⟨2764436, by rfl⟩ : syracuseStep 3685915 = 5528873) B5528873
theorem B1294079 : Blo 1293965 1294079 := bstep (se 1 (by rfl) ⟨970559, by rfl⟩ : syracuseStep 1294079 = 1941119) B1941119
theorem B49758623 : Blo 1293965 49758623 := bstep (se 1 (by rfl) ⟨37318967, by rfl⟩ : syracuseStep 49758623 = 74637935) B74637935
theorem B1942559 : Blo 1293965 1942559 := bstep (se 1 (by rfl) ⟨1456919, by rfl⟩ : syracuseStep 1942559 = 2913839) B2913839
theorem B1942631 : Blo 1293965 1942631 := bstep (se 1 (by rfl) ⟨1456973, by rfl⟩ : syracuseStep 1942631 = 2913947) B2913947
theorem B3278465 : Blo 1293965 3278465 := bstep (se 2 (by rfl) ⟨1229424, by rfl⟩ : syracuseStep 3278465 = 2458849) B2458849
theorem B1943711 : Blo 1293965 1943711 := bstep (se 1 (by rfl) ⟨1457783, by rfl⟩ : syracuseStep 1943711 = 2915567) B2915567
theorem B31484189 : Blo 1293965 31484189 := bstep (se 3 (by rfl) ⟨5903285, by rfl⟩ : syracuseStep 31484189 = 11806571) B11806571
theorem B41987483 : Blo 1293965 41987483 := bstep (se 1 (by rfl) ⟨31490612, by rfl⟩ : syracuseStep 41987483 = 62981225) B62981225
theorem B47255177 : Blo 1293965 47255177 := bstep (se 2 (by rfl) ⟨17720691, by rfl⟩ : syracuseStep 47255177 = 35441383) B35441383
theorem B14741837 : Blo 1293965 14741837 := bstep (se 3 (by rfl) ⟨2764094, by rfl⟩ : syracuseStep 14741837 = 5528189) B5528189
theorem B8295155 : Blo 1293965 8295155 := bstep (se 1 (by rfl) ⟨6221366, by rfl⟩ : syracuseStep 8295155 = 12442733) B12442733
theorem B2185535 : Blo 1293965 2185535 := bstep (se 1 (by rfl) ⟨1639151, by rfl⟩ : syracuseStep 2185535 = 3278303) B3278303
theorem B14744753 : Blo 1293965 14744753 := bstep (se 2 (by rfl) ⟨5529282, by rfl⟩ : syracuseStep 14744753 = 11058565) B11058565
theorem B4914553 : Blo 1293965 4914553 := bstep (se 2 (by rfl) ⟨1842957, by rfl⟩ : syracuseStep 4914553 = 3685915) B3685915
theorem B1555967 : Blo 1293965 1555967 := bstep (se 1 (by rfl) ⟨1166975, by rfl⟩ : syracuseStep 1555967 = 2333951) B2333951
theorem B28008089 : Blo 1293965 28008089 := bstep (se 2 (by rfl) ⟨10503033, by rfl⟩ : syracuseStep 28008089 = 21006067) B21006067
theorem B5530103 : Blo 1293965 5530103 := bstep (se 1 (by rfl) ⟨4147577, by rfl⟩ : syracuseStep 5530103 = 8295155) B8295155
theorem B1295039 : Blo 1293965 1295039 := bstep (se 1 (by rfl) ⟨971279, by rfl⟩ : syracuseStep 1295039 = 1942559) B1942559
theorem B1295087 : Blo 1293965 1295087 := bstep (se 1 (by rfl) ⟨971315, by rfl⟩ : syracuseStep 1295087 = 1942631) B1942631
theorem B1295807 : Blo 1293965 1295807 := bstep (se 1 (by rfl) ⟨971855, by rfl⟩ : syracuseStep 1295807 = 1943711) B1943711
theorem B20989459 : Blo 1293965 20989459 := bstep (se 1 (by rfl) ⟨15742094, by rfl⟩ : syracuseStep 20989459 = 31484189) B31484189
theorem B18672059 : Blo 1293965 18672059 := bstep (se 1 (by rfl) ⟨14004044, by rfl⟩ : syracuseStep 18672059 = 28008089) B28008089
theorem B33172415 : Blo 1293965 33172415 := bstep (se 1 (by rfl) ⟨24879311, by rfl⟩ : syracuseStep 33172415 = 49758623) B49758623
theorem B4149245 : Blo 1293965 4149245 := bstep (se 3 (by rfl) ⟨777983, by rfl⟩ : syracuseStep 4149245 = 1555967) B1555967
theorem B31503451 : Blo 1293965 31503451 := bstep (se 1 (by rfl) ⟨23627588, by rfl⟩ : syracuseStep 31503451 = 47255177) B47255177
theorem B9827891 : Blo 1293965 9827891 := bstep (se 1 (by rfl) ⟨7370918, by rfl⟩ : syracuseStep 9827891 = 14741837) B14741837
theorem B2185643 : Blo 1293965 2185643 := bstep (se 1 (by rfl) ⟨1639232, by rfl⟩ : syracuseStep 2185643 = 3278465) B3278465
theorem B1457023 : Blo 1293965 1457023 := bstep (se 1 (by rfl) ⟨1092767, by rfl⟩ : syracuseStep 1457023 = 2185535) B2185535
theorem B6552737 : Blo 1293965 6552737 := bstep (se 2 (by rfl) ⟨2457276, by rfl⟩ : syracuseStep 6552737 = 4914553) B4914553
theorem B9829835 : Blo 1293965 9829835 := bstep (se 1 (by rfl) ⟨7372376, by rfl⟩ : syracuseStep 9829835 = 14744753) B14744753
theorem B27991655 : Blo 1293965 27991655 := bstep (se 1 (by rfl) ⟨20993741, by rfl⟩ : syracuseStep 27991655 = 41987483) B41987483
theorem B3686735 : Blo 1293965 3686735 := bstep (se 1 (by rfl) ⟨2765051, by rfl⟩ : syracuseStep 3686735 = 5530103) B5530103
theorem B1942697 : Blo 1293965 1942697 := bstep (se 2 (by rfl) ⟨728511, by rfl⟩ : syracuseStep 1942697 = 1457023) B1457023
theorem B27985945 : Blo 1293965 27985945 := bstep (se 2 (by rfl) ⟨10494729, by rfl⟩ : syracuseStep 27985945 = 20989459) B20989459
theorem B4368491 : Blo 1293965 4368491 := bstep (se 1 (by rfl) ⟨3276368, by rfl⟩ : syracuseStep 4368491 = 6552737) B6552737
theorem B42004601 : Blo 1293965 42004601 := bstep (se 2 (by rfl) ⟨15751725, by rfl⟩ : syracuseStep 42004601 = 31503451) B31503451
theorem B12448039 : Blo 1293965 12448039 := bstep (se 1 (by rfl) ⟨9336029, by rfl⟩ : syracuseStep 12448039 = 18672059) B18672059
theorem B22114943 : Blo 1293965 22114943 := bstep (se 1 (by rfl) ⟨16586207, by rfl⟩ : syracuseStep 22114943 = 33172415) B33172415
theorem B2766163 : Blo 1293965 2766163 := bstep (se 1 (by rfl) ⟨2074622, by rfl⟩ : syracuseStep 2766163 = 4149245) B4149245
theorem B6551927 : Blo 1293965 6551927 := bstep (se 1 (by rfl) ⟨4913945, by rfl⟩ : syracuseStep 6551927 = 9827891) B9827891
theorem B1457095 : Blo 1293965 1457095 := bstep (se 1 (by rfl) ⟨1092821, by rfl⟩ : syracuseStep 1457095 = 2185643) B2185643
theorem B6553223 : Blo 1293965 6553223 := bstep (se 1 (by rfl) ⟨4914917, by rfl⟩ : syracuseStep 6553223 = 9829835) B9829835
theorem B18661103 : Blo 1293965 18661103 := bstep (se 1 (by rfl) ⟨13995827, by rfl⟩ : syracuseStep 18661103 = 27991655) B27991655
theorem B37314593 : Blo 1293965 37314593 := bstep (se 2 (by rfl) ⟨13992972, by rfl⟩ : syracuseStep 37314593 = 27985945) B27985945
theorem B16597385 : Blo 1293965 16597385 := bstep (se 2 (by rfl) ⟨6224019, by rfl⟩ : syracuseStep 16597385 = 12448039) B12448039
theorem B1295131 : Blo 1293965 1295131 := bstep (se 1 (by rfl) ⟨971348, by rfl⟩ : syracuseStep 1295131 = 1942697) B1942697
theorem B9831293 : Blo 1293965 9831293 := bstep (se 3 (by rfl) ⟨1843367, by rfl⟩ : syracuseStep 9831293 = 3686735) B3686735
theorem B1942793 : Blo 1293965 1942793 := bstep (se 2 (by rfl) ⟨728547, by rfl⟩ : syracuseStep 1942793 = 1457095) B1457095
theorem B4367951 : Blo 1293965 4367951 := bstep (se 1 (by rfl) ⟨3275963, by rfl⟩ : syracuseStep 4367951 = 6551927) B6551927
theorem B3688217 : Blo 1293965 3688217 := bstep (se 2 (by rfl) ⟨1383081, by rfl⟩ : syracuseStep 3688217 = 2766163) B2766163
theorem B4368815 : Blo 1293965 4368815 := bstep (se 1 (by rfl) ⟨3276611, by rfl⟩ : syracuseStep 4368815 = 6553223) B6553223
theorem B28003067 : Blo 1293965 28003067 := bstep (se 1 (by rfl) ⟨21002300, by rfl⟩ : syracuseStep 28003067 = 42004601) B42004601
theorem B2912327 : Blo 1293965 2912327 := bstep (se 1 (by rfl) ⟨2184245, by rfl⟩ : syracuseStep 2912327 = 4368491) B4368491
theorem B12440735 : Blo 1293965 12440735 := bstep (se 1 (by rfl) ⟨9330551, by rfl⟩ : syracuseStep 12440735 = 18661103) B18661103
theorem B14743295 : Blo 1293965 14743295 := bstep (se 1 (by rfl) ⟨11057471, by rfl⟩ : syracuseStep 14743295 = 22114943) B22114943
theorem B1941551 : Blo 1293965 1941551 := bstep (se 1 (by rfl) ⟨1456163, by rfl⟩ : syracuseStep 1941551 = 2912327) B2912327
theorem B6554195 : Blo 1293965 6554195 := bstep (se 1 (by rfl) ⟨4915646, by rfl⟩ : syracuseStep 6554195 = 9831293) B9831293
theorem B1295195 : Blo 1293965 1295195 := bstep (se 1 (by rfl) ⟨971396, by rfl⟩ : syracuseStep 1295195 = 1942793) B1942793
theorem B2458811 : Blo 1293965 2458811 := bstep (se 1 (by rfl) ⟨1844108, by rfl⟩ : syracuseStep 2458811 = 3688217) B3688217
theorem B8293823 : Blo 1293965 8293823 := bstep (se 1 (by rfl) ⟨6220367, by rfl⟩ : syracuseStep 8293823 = 12440735) B12440735
theorem B2911967 : Blo 1293965 2911967 := bstep (se 1 (by rfl) ⟨2183975, by rfl⟩ : syracuseStep 2911967 = 4367951) B4367951
theorem B2912543 : Blo 1293965 2912543 := bstep (se 1 (by rfl) ⟨2184407, by rfl⟩ : syracuseStep 2912543 = 4368815) B4368815
theorem B24876395 : Blo 1293965 24876395 := bstep (se 1 (by rfl) ⟨18657296, by rfl⟩ : syracuseStep 24876395 = 37314593) B37314593
theorem B11064923 : Blo 1293965 11064923 := bstep (se 1 (by rfl) ⟨8298692, by rfl⟩ : syracuseStep 11064923 = 16597385) B16597385
theorem B9828863 : Blo 1293965 9828863 := bstep (se 1 (by rfl) ⟨7371647, by rfl⟩ : syracuseStep 9828863 = 14743295) B14743295
theorem B18668711 : Blo 1293965 18668711 := bstep (se 1 (by rfl) ⟨14001533, by rfl⟩ : syracuseStep 18668711 = 28003067) B28003067
theorem B1294367 : Blo 1293965 1294367 := bstep (se 1 (by rfl) ⟨970775, by rfl⟩ : syracuseStep 1294367 = 1941551) B1941551
theorem B1941695 : Blo 1293965 1941695 := bstep (se 1 (by rfl) ⟨1456271, by rfl⟩ : syracuseStep 1941695 = 2912543) B2912543
theorem B1639207 : Blo 1293965 1639207 := bstep (se 1 (by rfl) ⟨1229405, by rfl⟩ : syracuseStep 1639207 = 2458811) B2458811
theorem B12445807 : Blo 1293965 12445807 := bstep (se 1 (by rfl) ⟨9334355, by rfl⟩ : syracuseStep 12445807 = 18668711) B18668711
theorem B4369463 : Blo 1293965 4369463 := bstep (se 1 (by rfl) ⟨3277097, by rfl⟩ : syracuseStep 4369463 = 6554195) B6554195
theorem B16584263 : Blo 1293965 16584263 := bstep (se 1 (by rfl) ⟨12438197, by rfl⟩ : syracuseStep 16584263 = 24876395) B24876395
theorem B7376615 : Blo 1293965 7376615 := bstep (se 1 (by rfl) ⟨5532461, by rfl⟩ : syracuseStep 7376615 = 11064923) B11064923
theorem B6552575 : Blo 1293965 6552575 := bstep (se 1 (by rfl) ⟨4914431, by rfl⟩ : syracuseStep 6552575 = 9828863) B9828863
theorem B5529215 : Blo 1293965 5529215 := bstep (se 1 (by rfl) ⟨4146911, by rfl⟩ : syracuseStep 5529215 = 8293823) B8293823
theorem B1941311 : Blo 1293965 1941311 := bstep (se 1 (by rfl) ⟨1455983, by rfl⟩ : syracuseStep 1941311 = 2911967) B2911967
theorem B1294463 : Blo 1293965 1294463 := bstep (se 1 (by rfl) ⟨970847, by rfl⟩ : syracuseStep 1294463 = 1941695) B1941695
theorem B4368383 : Blo 1293965 4368383 := bstep (se 1 (by rfl) ⟨3276287, by rfl⟩ : syracuseStep 4368383 = 6552575) B6552575
theorem B4917743 : Blo 1293965 4917743 := bstep (se 1 (by rfl) ⟨3688307, by rfl⟩ : syracuseStep 4917743 = 7376615) B7376615
theorem B2912975 : Blo 1293965 2912975 := bstep (se 1 (by rfl) ⟨2184731, by rfl⟩ : syracuseStep 2912975 = 4369463) B4369463
theorem B11056175 : Blo 1293965 11056175 := bstep (se 1 (by rfl) ⟨8292131, by rfl⟩ : syracuseStep 11056175 = 16584263) B16584263
theorem B16594409 : Blo 1293965 16594409 := bstep (se 2 (by rfl) ⟨6222903, by rfl⟩ : syracuseStep 16594409 = 12445807) B12445807
theorem B2185609 : Blo 1293965 2185609 := bstep (se 2 (by rfl) ⟨819603, by rfl⟩ : syracuseStep 2185609 = 1639207) B1639207
theorem B3686143 : Blo 1293965 3686143 := bstep (se 1 (by rfl) ⟨2764607, by rfl⟩ : syracuseStep 3686143 = 5529215) B5529215
theorem B1294207 : Blo 1293965 1294207 := bstep (se 1 (by rfl) ⟨970655, by rfl⟩ : syracuseStep 1294207 = 1941311) B1941311
theorem B1941983 : Blo 1293965 1941983 := bstep (se 1 (by rfl) ⟨1456487, by rfl⟩ : syracuseStep 1941983 = 2912975) B2912975
theorem B3278495 : Blo 1293965 3278495 := bstep (se 1 (by rfl) ⟨2458871, by rfl⟩ : syracuseStep 3278495 = 4917743) B4917743
theorem B11062939 : Blo 1293965 11062939 := bstep (se 1 (by rfl) ⟨8297204, by rfl⟩ : syracuseStep 11062939 = 16594409) B16594409
theorem B2912255 : Blo 1293965 2912255 := bstep (se 1 (by rfl) ⟨2184191, by rfl⟩ : syracuseStep 2912255 = 4368383) B4368383
theorem B2914145 : Blo 1293965 2914145 := bstep (se 2 (by rfl) ⟨1092804, by rfl⟩ : syracuseStep 2914145 = 2185609) B2185609
theorem B7370783 : Blo 1293965 7370783 := bstep (se 1 (by rfl) ⟨5528087, by rfl⟩ : syracuseStep 7370783 = 11056175) B11056175
theorem B4914857 : Blo 1293965 4914857 := bstep (se 2 (by rfl) ⟨1843071, by rfl⟩ : syracuseStep 4914857 = 3686143) B3686143
theorem B1294655 : Blo 1293965 1294655 := bstep (se 1 (by rfl) ⟨970991, by rfl⟩ : syracuseStep 1294655 = 1941983) B1941983
theorem B1942763 : Blo 1293965 1942763 := bstep (se 1 (by rfl) ⟨1457072, by rfl⟩ : syracuseStep 1942763 = 2914145) B2914145
theorem B14750585 : Blo 1293965 14750585 := bstep (se 2 (by rfl) ⟨5531469, by rfl⟩ : syracuseStep 14750585 = 11062939) B11062939
theorem B2185663 : Blo 1293965 2185663 := bstep (se 1 (by rfl) ⟨1639247, by rfl⟩ : syracuseStep 2185663 = 3278495) B3278495
theorem B4913855 : Blo 1293965 4913855 := bstep (se 1 (by rfl) ⟨3685391, by rfl⟩ : syracuseStep 4913855 = 7370783) B7370783
theorem B3276571 : Blo 1293965 3276571 := bstep (se 1 (by rfl) ⟨2457428, by rfl⟩ : syracuseStep 3276571 = 4914857) B4914857
theorem B1941503 : Blo 1293965 1941503 := bstep (se 1 (by rfl) ⟨1456127, by rfl⟩ : syracuseStep 1941503 = 2912255) B2912255
theorem B1295175 : Blo 1293965 1295175 := bstep (se 1 (by rfl) ⟨971381, by rfl⟩ : syracuseStep 1295175 = 1942763) B1942763
theorem B4368761 : Blo 1293965 4368761 := bstep (se 2 (by rfl) ⟨1638285, by rfl⟩ : syracuseStep 4368761 = 3276571) B3276571
theorem B9833723 : Blo 1293965 9833723 := bstep (se 1 (by rfl) ⟨7375292, by rfl⟩ : syracuseStep 9833723 = 14750585) B14750585
theorem B2914217 : Blo 1293965 2914217 := bstep (se 2 (by rfl) ⟨1092831, by rfl⟩ : syracuseStep 2914217 = 2185663) B2185663
theorem B3275903 : Blo 1293965 3275903 := bstep (se 1 (by rfl) ⟨2456927, by rfl⟩ : syracuseStep 3275903 = 4913855) B4913855
theorem B1294335 : Blo 1293965 1294335 := bstep (se 1 (by rfl) ⟨970751, by rfl⟩ : syracuseStep 1294335 = 1941503) B1941503
theorem B1942811 : Blo 1293965 1942811 := bstep (se 1 (by rfl) ⟨1457108, by rfl⟩ : syracuseStep 1942811 = 2914217) B2914217
theorem B6555815 : Blo 1293965 6555815 := bstep (se 1 (by rfl) ⟨4916861, by rfl⟩ : syracuseStep 6555815 = 9833723) B9833723
theorem B2912507 : Blo 1293965 2912507 := bstep (se 1 (by rfl) ⟨2184380, by rfl⟩ : syracuseStep 2912507 = 4368761) B4368761
theorem B2183935 : Blo 1293965 2183935 := bstep (se 1 (by rfl) ⟨1637951, by rfl⟩ : syracuseStep 2183935 = 3275903) B3275903
theorem B1941671 : Blo 1293965 1941671 := bstep (se 1 (by rfl) ⟨1456253, by rfl⟩ : syracuseStep 1941671 = 2912507) B2912507
theorem B1295207 : Blo 1293965 1295207 := bstep (se 1 (by rfl) ⟨971405, by rfl⟩ : syracuseStep 1295207 = 1942811) B1942811
theorem B2911913 : Blo 1293965 2911913 := bstep (se 2 (by rfl) ⟨1091967, by rfl⟩ : syracuseStep 2911913 = 2183935) B2183935
theorem B4370543 : Blo 1293965 4370543 := bstep (se 1 (by rfl) ⟨3277907, by rfl⟩ : syracuseStep 4370543 = 6555815) B6555815
theorem B1294447 : Blo 1293965 1294447 := bstep (se 1 (by rfl) ⟨970835, by rfl⟩ : syracuseStep 1294447 = 1941671) B1941671
theorem B2913695 : Blo 1293965 2913695 := bstep (se 1 (by rfl) ⟨2185271, by rfl⟩ : syracuseStep 2913695 = 4370543) B4370543
theorem B1941275 : Blo 1293965 1941275 := bstep (se 1 (by rfl) ⟨1455956, by rfl⟩ : syracuseStep 1941275 = 2911913) B2911913
theorem B1942463 : Blo 1293965 1942463 := bstep (se 1 (by rfl) ⟨1456847, by rfl⟩ : syracuseStep 1942463 = 2913695) B2913695
theorem B1294183 : Blo 1293965 1294183 := bstep (se 1 (by rfl) ⟨970637, by rfl⟩ : syracuseStep 1294183 = 1941275) B1941275
theorem B1294975 : Blo 1293965 1294975 := bstep (se 1 (by rfl) ⟨971231, by rfl⟩ : syracuseStep 1294975 = 1942463) B1942463

theorem C0 (j : ℕ) (h1 : 323491 ≤ j) (h2 : j ≤ 323990) : Blo 1293965 (4 * j + 3) := by
  interval_cases j
  · exact B1293967
  · exact B1293971
  · exact B1293975
  · exact B1293979
  · exact B1293983
  · exact B1293987
  · exact B1293991
  · exact B1293995
  · exact B1293999
  · exact B1294003
  · exact B1294007
  · exact B1294011
  · exact B1294015
  · exact B1294019
  · exact B1294023
  · exact B1294027
  · exact B1294031
  · exact B1294035
  · exact B1294039
  · exact B1294043
  · exact B1294047
  · exact B1294051
  · exact B1294055
  · exact B1294059
  · exact B1294063
  · exact B1294067
  · exact B1294071
  · exact B1294075
  · exact B1294079
  · exact B1294083
  · exact B1294087
  · exact B1294091
  · exact B1294095
  · exact B1294099
  · exact B1294103
  · exact B1294107
  · exact B1294111
  · exact B1294115
  · exact B1294119
  · exact B1294123
  · exact B1294127
  · exact B1294131
  · exact B1294135
  · exact B1294139
  · exact B1294143
  · exact B1294147
  · exact B1294151
  · exact B1294155
  · exact B1294159
  · exact B1294163
  · exact B1294167
  · exact B1294171
  · exact B1294175
  · exact B1294179
  · exact B1294183
  · exact B1294187
  · exact B1294191
  · exact B1294195
  · exact B1294199
  · exact B1294203
  · exact B1294207
  · exact B1294211
  · exact B1294215
  · exact B1294219
  · exact B1294223
  · exact B1294227
  · exact B1294231
  · exact B1294235
  · exact B1294239
  · exact B1294243
  · exact B1294247
  · exact B1294251
  · exact B1294255
  · exact B1294259
  · exact B1294263
  · exact B1294267
  · exact B1294271
  · exact B1294275
  · exact B1294279
  · exact B1294283
  · exact B1294287
  · exact B1294291
  · exact B1294295
  · exact B1294299
  · exact B1294303
  · exact B1294307
  · exact B1294311
  · exact B1294315
  · exact B1294319
  · exact B1294323
  · exact B1294327
  · exact B1294331
  · exact B1294335
  · exact B1294339
  · exact B1294343
  · exact B1294347
  · exact B1294351
  · exact B1294355
  · exact B1294359
  · exact B1294363
  · exact B1294367
  · exact B1294371
  · exact B1294375
  · exact B1294379
  · exact B1294383
  · exact B1294387
  · exact B1294391
  · exact B1294395
  · exact B1294399
  · exact B1294403
  · exact B1294407
  · exact B1294411
  · exact B1294415
  · exact B1294419
  · exact B1294423
  · exact B1294427
  · exact B1294431
  · exact B1294435
  · exact B1294439
  · exact B1294443
  · exact B1294447
  · exact B1294451
  · exact B1294455
  · exact B1294459
  · exact B1294463
  · exact B1294467
  · exact B1294471
  · exact B1294475
  · exact B1294479
  · exact B1294483
  · exact B1294487
  · exact B1294491
  · exact B1294495
  · exact B1294499
  · exact B1294503
  · exact B1294507
  · exact B1294511
  · exact B1294515
  · exact B1294519
  · exact B1294523
  · exact B1294527
  · exact B1294531
  · exact B1294535
  · exact B1294539
  · exact B1294543
  · exact B1294547
  · exact B1294551
  · exact B1294555
  · exact B1294559
  · exact B1294563
  · exact B1294567
  · exact B1294571
  · exact B1294575
  · exact B1294579
  · exact B1294583
  · exact B1294587
  · exact B1294591
  · exact B1294595
  · exact B1294599
  · exact B1294603
  · exact B1294607
  · exact B1294611
  · exact B1294615
  · exact B1294619
  · exact B1294623
  · exact B1294627
  · exact B1294631
  · exact B1294635
  · exact B1294639
  · exact B1294643
  · exact B1294647
  · exact B1294651
  · exact B1294655
  · exact B1294659
  · exact B1294663
  · exact B1294667
  · exact B1294671
  · exact B1294675
  · exact B1294679
  · exact B1294683
  · exact B1294687
  · exact B1294691
  · exact B1294695
  · exact B1294699
  · exact B1294703
  · exact B1294707
  · exact B1294711
  · exact B1294715
  · exact B1294719
  · exact B1294723
  · exact B1294727
  · exact B1294731
  · exact B1294735
  · exact B1294739
  · exact B1294743
  · exact B1294747
  · exact B1294751
  · exact B1294755
  · exact B1294759
  · exact B1294763
  · exact B1294767
  · exact B1294771
  · exact B1294775
  · exact B1294779
  · exact B1294783
  · exact B1294787
  · exact B1294791
  · exact B1294795
  · exact B1294799
  · exact B1294803
  · exact B1294807
  · exact B1294811
  · exact B1294815
  · exact B1294819
  · exact B1294823
  · exact B1294827
  · exact B1294831
  · exact B1294835
  · exact B1294839
  · exact B1294843
  · exact B1294847
  · exact B1294851
  · exact B1294855
  · exact B1294859
  · exact B1294863
  · exact B1294867
  · exact B1294871
  · exact B1294875
  · exact B1294879
  · exact B1294883
  · exact B1294887
  · exact B1294891
  · exact B1294895
  · exact B1294899
  · exact B1294903
  · exact B1294907
  · exact B1294911
  · exact B1294915
  · exact B1294919
  · exact B1294923
  · exact B1294927
  · exact B1294931
  · exact B1294935
  · exact B1294939
  · exact B1294943
  · exact B1294947
  · exact B1294951
  · exact B1294955
  · exact B1294959
  · exact B1294963
  · exact B1294967
  · exact B1294971
  · exact B1294975
  · exact B1294979
  · exact B1294983
  · exact B1294987
  · exact B1294991
  · exact B1294995
  · exact B1294999
  · exact B1295003
  · exact B1295007
  · exact B1295011
  · exact B1295015
  · exact B1295019
  · exact B1295023
  · exact B1295027
  · exact B1295031
  · exact B1295035
  · exact B1295039
  · exact B1295043
  · exact B1295047
  · exact B1295051
  · exact B1295055
  · exact B1295059
  · exact B1295063
  · exact B1295067
  · exact B1295071
  · exact B1295075
  · exact B1295079
  · exact B1295083
  · exact B1295087
  · exact B1295091
  · exact B1295095
  · exact B1295099
  · exact B1295103
  · exact B1295107
  · exact B1295111
  · exact B1295115
  · exact B1295119
  · exact B1295123
  · exact B1295127
  · exact B1295131
  · exact B1295135
  · exact B1295139
  · exact B1295143
  · exact B1295147
  · exact B1295151
  · exact B1295155
  · exact B1295159
  · exact B1295163
  · exact B1295167
  · exact B1295171
  · exact B1295175
  · exact B1295179
  · exact B1295183
  · exact B1295187
  · exact B1295191
  · exact B1295195
  · exact B1295199
  · exact B1295203
  · exact B1295207
  · exact B1295211
  · exact B1295215
  · exact B1295219
  · exact B1295223
  · exact B1295227
  · exact B1295231
  · exact B1295235
  · exact B1295239
  · exact B1295243
  · exact B1295247
  · exact B1295251
  · exact B1295255
  · exact B1295259
  · exact B1295263
  · exact B1295267
  · exact B1295271
  · exact B1295275
  · exact B1295279
  · exact B1295283
  · exact B1295287
  · exact B1295291
  · exact B1295295
  · exact B1295299
  · exact B1295303
  · exact B1295307
  · exact B1295311
  · exact B1295315
  · exact B1295319
  · exact B1295323
  · exact B1295327
  · exact B1295331
  · exact B1295335
  · exact B1295339
  · exact B1295343
  · exact B1295347
  · exact B1295351
  · exact B1295355
  · exact B1295359
  · exact B1295363
  · exact B1295367
  · exact B1295371
  · exact B1295375
  · exact B1295379
  · exact B1295383
  · exact B1295387
  · exact B1295391
  · exact B1295395
  · exact B1295399
  · exact B1295403
  · exact B1295407
  · exact B1295411
  · exact B1295415
  · exact B1295419
  · exact B1295423
  · exact B1295427
  · exact B1295431
  · exact B1295435
  · exact B1295439
  · exact B1295443
  · exact B1295447
  · exact B1295451
  · exact B1295455
  · exact B1295459
  · exact B1295463
  · exact B1295467
  · exact B1295471
  · exact B1295475
  · exact B1295479
  · exact B1295483
  · exact B1295487
  · exact B1295491
  · exact B1295495
  · exact B1295499
  · exact B1295503
  · exact B1295507
  · exact B1295511
  · exact B1295515
  · exact B1295519
  · exact B1295523
  · exact B1295527
  · exact B1295531
  · exact B1295535
  · exact B1295539
  · exact B1295543
  · exact B1295547
  · exact B1295551
  · exact B1295555
  · exact B1295559
  · exact B1295563
  · exact B1295567
  · exact B1295571
  · exact B1295575
  · exact B1295579
  · exact B1295583
  · exact B1295587
  · exact B1295591
  · exact B1295595
  · exact B1295599
  · exact B1295603
  · exact B1295607
  · exact B1295611
  · exact B1295615
  · exact B1295619
  · exact B1295623
  · exact B1295627
  · exact B1295631
  · exact B1295635
  · exact B1295639
  · exact B1295643
  · exact B1295647
  · exact B1295651
  · exact B1295655
  · exact B1295659
  · exact B1295663
  · exact B1295667
  · exact B1295671
  · exact B1295675
  · exact B1295679
  · exact B1295683
  · exact B1295687
  · exact B1295691
  · exact B1295695
  · exact B1295699
  · exact B1295703
  · exact B1295707
  · exact B1295711
  · exact B1295715
  · exact B1295719
  · exact B1295723
  · exact B1295727
  · exact B1295731
  · exact B1295735
  · exact B1295739
  · exact B1295743
  · exact B1295747
  · exact B1295751
  · exact B1295755
  · exact B1295759
  · exact B1295763
  · exact B1295767
  · exact B1295771
  · exact B1295775
  · exact B1295779
  · exact B1295783
  · exact B1295787
  · exact B1295791
  · exact B1295795
  · exact B1295799
  · exact B1295803
  · exact B1295807
  · exact B1295811
  · exact B1295815
  · exact B1295819
  · exact B1295823
  · exact B1295827
  · exact B1295831
  · exact B1295835
  · exact B1295839
  · exact B1295843
  · exact B1295847
  · exact B1295851
  · exact B1295855
  · exact B1295859
  · exact B1295863
  · exact B1295867
  · exact B1295871
  · exact B1295875
  · exact B1295879
  · exact B1295883
  · exact B1295887
  · exact B1295891
  · exact B1295895
  · exact B1295899
  · exact B1295903
  · exact B1295907
  · exact B1295911
  · exact B1295915
  · exact B1295919
  · exact B1295923
  · exact B1295927
  · exact B1295931
  · exact B1295935
  · exact B1295939
  · exact B1295943
  · exact B1295947
  · exact B1295951
  · exact B1295955
  · exact B1295959
  · exact B1295963

theorem solution (m : ℕ) (hlo : 1293965 ≤ m) (hhi : m ≤ 1295965) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 323491 ≤ j := by omega
    have hj2 : j ≤ 323990 := by omega
    have hb : Blo 1293965 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
