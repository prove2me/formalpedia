-- Prove2me | solution 1 for syracuse_descends_range_960589_964589
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:02.321767+00:00
-- url     : https://prove2.me/submissions/bdfad93b-abbf-4f41-aabb-f7e642c7225f

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


theorem B1081345 : Blo 960589 1081345 := bbase (se 2 (by rfl) ⟨405504, by rfl⟩ : syracuseStep 1081345 = 811009) (by norm_num)
theorem B1441805 : Blo 960589 1441805 := bbase (se 3 (by rfl) ⟨270338, by rfl⟩ : syracuseStep 1441805 = 540677) (by norm_num)
theorem B2162717 : Blo 960589 2162717 := bbase (se 3 (by rfl) ⟨405509, by rfl⟩ : syracuseStep 2162717 = 811019) (by norm_num)
theorem B1441829 : Blo 960589 1441829 := bbase (se 4 (by rfl) ⟨135171, by rfl⟩ : syracuseStep 1441829 = 270343) (by norm_num)
theorem B1081381 : Blo 960589 1081381 := bbase (se 4 (by rfl) ⟨101379, by rfl⟩ : syracuseStep 1081381 = 202759) (by norm_num)
theorem B1441853 : Blo 960589 1441853 := bbase (se 3 (by rfl) ⟨270347, by rfl⟩ : syracuseStep 1441853 = 540695) (by norm_num)
theorem B1081417 : Blo 960589 1081417 := bbase (se 2 (by rfl) ⟨405531, by rfl⟩ : syracuseStep 1081417 = 811063) (by norm_num)
theorem B1441877 : Blo 960589 1441877 := bbase (se 8 (by rfl) ⟨8448, by rfl⟩ : syracuseStep 1441877 = 16897) (by norm_num)
theorem B4882517 : Blo 960589 4882517 := bbase (se 8 (by rfl) ⟨28608, by rfl⟩ : syracuseStep 4882517 = 57217) (by norm_num)
theorem B2162789 : Blo 960589 2162789 := bbase (se 4 (by rfl) ⟨202761, by rfl⟩ : syracuseStep 2162789 = 405523) (by norm_num)
theorem B1441901 : Blo 960589 1441901 := bbase (se 3 (by rfl) ⟨270356, by rfl⟩ : syracuseStep 1441901 = 540713) (by norm_num)
theorem B1081453 : Blo 960589 1081453 := bbase (se 3 (by rfl) ⟨202772, by rfl⟩ : syracuseStep 1081453 = 405545) (by norm_num)
theorem B1441925 : Blo 960589 1441925 := bbase (se 4 (by rfl) ⟨135180, by rfl⟩ : syracuseStep 1441925 = 270361) (by norm_num)
theorem B1081489 : Blo 960589 1081489 := bbase (se 2 (by rfl) ⟨405558, by rfl⟩ : syracuseStep 1081489 = 811117) (by norm_num)
theorem B1441949 : Blo 960589 1441949 := bbase (se 3 (by rfl) ⟨270365, by rfl⟩ : syracuseStep 1441949 = 540731) (by norm_num)
theorem B2162861 : Blo 960589 2162861 := bbase (se 3 (by rfl) ⟨405536, by rfl⟩ : syracuseStep 2162861 = 811073) (by norm_num)
theorem B1441973 : Blo 960589 1441973 := bbase (se 5 (by rfl) ⟨67592, by rfl⟩ : syracuseStep 1441973 = 135185) (by norm_num)
theorem B1081525 : Blo 960589 1081525 := bbase (se 5 (by rfl) ⟨50696, by rfl⟩ : syracuseStep 1081525 = 101393) (by norm_num)
theorem B1441997 : Blo 960589 1441997 := bbase (se 3 (by rfl) ⟨270374, by rfl⟩ : syracuseStep 1441997 = 540749) (by norm_num)
theorem B1081561 : Blo 960589 1081561 := bbase (se 2 (by rfl) ⟨405585, by rfl⟩ : syracuseStep 1081561 = 811171) (by norm_num)
theorem B1442021 : Blo 960589 1442021 := bbase (se 4 (by rfl) ⟨135189, by rfl⟩ : syracuseStep 1442021 = 270379) (by norm_num)
theorem B2162933 : Blo 960589 2162933 := bbase (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) (by norm_num)
theorem B1442045 : Blo 960589 1442045 := bbase (se 3 (by rfl) ⟨270383, by rfl⟩ : syracuseStep 1442045 = 540767) (by norm_num)
theorem B1081597 : Blo 960589 1081597 := bbase (se 3 (by rfl) ⟨202799, by rfl⟩ : syracuseStep 1081597 = 405599) (by norm_num)
theorem B1442069 : Blo 960589 1442069 := bbase (se 6 (by rfl) ⟨33798, by rfl⟩ : syracuseStep 1442069 = 67597) (by norm_num)
theorem B1081633 : Blo 960589 1081633 := bbase (se 2 (by rfl) ⟨405612, by rfl⟩ : syracuseStep 1081633 = 811225) (by norm_num)
theorem B1442093 : Blo 960589 1442093 := bbase (se 3 (by rfl) ⟨270392, by rfl⟩ : syracuseStep 1442093 = 540785) (by norm_num)
theorem B2163005 : Blo 960589 2163005 := bbase (se 3 (by rfl) ⟨405563, by rfl⟩ : syracuseStep 2163005 = 811127) (by norm_num)
theorem B1442117 : Blo 960589 1442117 := bbase (se 4 (by rfl) ⟨135198, by rfl⟩ : syracuseStep 1442117 = 270397) (by norm_num)
theorem B1081669 : Blo 960589 1081669 := bbase (se 4 (by rfl) ⟨101406, by rfl⟩ : syracuseStep 1081669 = 202813) (by norm_num)
theorem B3244373 : Blo 960589 3244373 := bbase (se 10 (by rfl) ⟨4752, by rfl⟩ : syracuseStep 3244373 = 9505) (by norm_num)
theorem B1442141 : Blo 960589 1442141 := bbase (se 3 (by rfl) ⟨270401, by rfl⟩ : syracuseStep 1442141 = 540803) (by norm_num)
theorem B1081705 : Blo 960589 1081705 := bbase (se 2 (by rfl) ⟨405639, by rfl⟩ : syracuseStep 1081705 = 811279) (by norm_num)
theorem B1442165 : Blo 960589 1442165 := bbase (se 5 (by rfl) ⟨67601, by rfl⟩ : syracuseStep 1442165 = 135203) (by norm_num)
theorem B2163077 : Blo 960589 2163077 := bbase (se 4 (by rfl) ⟨202788, by rfl⟩ : syracuseStep 2163077 = 405577) (by norm_num)
theorem B1442189 : Blo 960589 1442189 := bbase (se 3 (by rfl) ⟨270410, by rfl⟩ : syracuseStep 1442189 = 540821) (by norm_num)
theorem B1081741 : Blo 960589 1081741 := bbase (se 3 (by rfl) ⟨202826, by rfl⟩ : syracuseStep 1081741 = 405653) (by norm_num)
theorem B1442213 : Blo 960589 1442213 := bbase (se 4 (by rfl) ⟨135207, by rfl⟩ : syracuseStep 1442213 = 270415) (by norm_num)
theorem B1081777 : Blo 960589 1081777 := bbase (se 2 (by rfl) ⟨405666, by rfl⟩ : syracuseStep 1081777 = 811333) (by norm_num)
theorem B1442237 : Blo 960589 1442237 := bbase (se 3 (by rfl) ⟨270419, by rfl⟩ : syracuseStep 1442237 = 540839) (by norm_num)
theorem B2163149 : Blo 960589 2163149 := bbase (se 3 (by rfl) ⟨405590, by rfl⟩ : syracuseStep 2163149 = 811181) (by norm_num)
theorem B1442261 : Blo 960589 1442261 := bbase (se 7 (by rfl) ⟨16901, by rfl⟩ : syracuseStep 1442261 = 33803) (by norm_num)
theorem B1081813 : Blo 960589 1081813 := bbase (se 7 (by rfl) ⟨12677, by rfl⟩ : syracuseStep 1081813 = 25355) (by norm_num)
theorem B1442285 : Blo 960589 1442285 := bbase (se 3 (by rfl) ⟨270428, by rfl⟩ : syracuseStep 1442285 = 540857) (by norm_num)
theorem B1081849 : Blo 960589 1081849 := bbase (se 2 (by rfl) ⟨405693, by rfl⟩ : syracuseStep 1081849 = 811387) (by norm_num)
theorem B1442309 : Blo 960589 1442309 := bbase (se 4 (by rfl) ⟨135216, by rfl⟩ : syracuseStep 1442309 = 270433) (by norm_num)
theorem B2163221 : Blo 960589 2163221 := bbase (se 6 (by rfl) ⟨50700, by rfl⟩ : syracuseStep 2163221 = 101401) (by norm_num)
theorem B1442333 : Blo 960589 1442333 := bbase (se 3 (by rfl) ⟨270437, by rfl⟩ : syracuseStep 1442333 = 540875) (by norm_num)
theorem B1081885 : Blo 960589 1081885 := bbase (se 3 (by rfl) ⟨202853, by rfl⟩ : syracuseStep 1081885 = 405707) (by norm_num)
theorem B1442357 : Blo 960589 1442357 := bbase (se 5 (by rfl) ⟨67610, by rfl⟩ : syracuseStep 1442357 = 135221) (by norm_num)
theorem B1081921 : Blo 960589 1081921 := bbase (se 2 (by rfl) ⟨405720, by rfl⟩ : syracuseStep 1081921 = 811441) (by norm_num)
theorem B1442381 : Blo 960589 1442381 := bbase (se 3 (by rfl) ⟨270446, by rfl⟩ : syracuseStep 1442381 = 540893) (by norm_num)
theorem B2163293 : Blo 960589 2163293 := bbase (se 3 (by rfl) ⟨405617, by rfl⟩ : syracuseStep 2163293 = 811235) (by norm_num)
theorem B1442405 : Blo 960589 1442405 := bbase (se 4 (by rfl) ⟨135225, by rfl⟩ : syracuseStep 1442405 = 270451) (by norm_num)
theorem B1081957 : Blo 960589 1081957 := bbase (se 4 (by rfl) ⟨101433, by rfl⟩ : syracuseStep 1081957 = 202867) (by norm_num)
theorem B1442429 : Blo 960589 1442429 := bbase (se 3 (by rfl) ⟨270455, by rfl⟩ : syracuseStep 1442429 = 540911) (by norm_num)
theorem B1081993 : Blo 960589 1081993 := bbase (se 2 (by rfl) ⟨405747, by rfl⟩ : syracuseStep 1081993 = 811495) (by norm_num)
theorem B1442453 : Blo 960589 1442453 := bbase (se 6 (by rfl) ⟨33807, by rfl⟩ : syracuseStep 1442453 = 67615) (by norm_num)
theorem B2163365 : Blo 960589 2163365 := bbase (se 4 (by rfl) ⟨202815, by rfl⟩ : syracuseStep 2163365 = 405631) (by norm_num)
theorem B1442477 : Blo 960589 1442477 := bbase (se 3 (by rfl) ⟨270464, by rfl⟩ : syracuseStep 1442477 = 540929) (by norm_num)
theorem B1082029 : Blo 960589 1082029 := bbase (se 3 (by rfl) ⟨202880, by rfl⟩ : syracuseStep 1082029 = 405761) (by norm_num)
theorem B1442501 : Blo 960589 1442501 := bbase (se 4 (by rfl) ⟨135234, by rfl⟩ : syracuseStep 1442501 = 270469) (by norm_num)
theorem B1082065 : Blo 960589 1082065 := bbase (se 2 (by rfl) ⟨405774, by rfl⟩ : syracuseStep 1082065 = 811549) (by norm_num)
theorem B1442525 : Blo 960589 1442525 := bbase (se 3 (by rfl) ⟨270473, by rfl⟩ : syracuseStep 1442525 = 540947) (by norm_num)
theorem B2163437 : Blo 960589 2163437 := bbase (se 3 (by rfl) ⟨405644, by rfl⟩ : syracuseStep 2163437 = 811289) (by norm_num)
theorem B1442549 : Blo 960589 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B1082101 : Blo 960589 1082101 := bbase (se 5 (by rfl) ⟨50723, by rfl⟩ : syracuseStep 1082101 = 101447) (by norm_num)
theorem B3244805 : Blo 960589 3244805 := bbase (se 4 (by rfl) ⟨304200, by rfl⟩ : syracuseStep 3244805 = 608401) (by norm_num)
theorem B1442573 : Blo 960589 1442573 := bbase (se 3 (by rfl) ⟨270482, by rfl⟩ : syracuseStep 1442573 = 540965) (by norm_num)
theorem B1082137 : Blo 960589 1082137 := bbase (se 2 (by rfl) ⟨405801, by rfl⟩ : syracuseStep 1082137 = 811603) (by norm_num)
theorem B1442597 : Blo 960589 1442597 := bbase (se 4 (by rfl) ⟨135243, by rfl⟩ : syracuseStep 1442597 = 270487) (by norm_num)
theorem B2163509 : Blo 960589 2163509 := bbase (se 5 (by rfl) ⟨101414, by rfl⟩ : syracuseStep 2163509 = 202829) (by norm_num)
theorem B1442621 : Blo 960589 1442621 := bbase (se 3 (by rfl) ⟨270491, by rfl⟩ : syracuseStep 1442621 = 540983) (by norm_num)
theorem B1082173 : Blo 960589 1082173 := bbase (se 3 (by rfl) ⟨202907, by rfl⟩ : syracuseStep 1082173 = 405815) (by norm_num)
theorem B1442645 : Blo 960589 1442645 := bbase (se 9 (by rfl) ⟨4226, by rfl⟩ : syracuseStep 1442645 = 8453) (by norm_num)
theorem B1082209 : Blo 960589 1082209 := bbase (se 2 (by rfl) ⟨405828, by rfl⟩ : syracuseStep 1082209 = 811657) (by norm_num)
theorem B1442669 : Blo 960589 1442669 := bbase (se 3 (by rfl) ⟨270500, by rfl⟩ : syracuseStep 1442669 = 541001) (by norm_num)
theorem B2163581 : Blo 960589 2163581 := bbase (se 3 (by rfl) ⟨405671, by rfl⟩ : syracuseStep 2163581 = 811343) (by norm_num)
theorem B1442693 : Blo 960589 1442693 := bbase (se 4 (by rfl) ⟨135252, by rfl⟩ : syracuseStep 1442693 = 270505) (by norm_num)
theorem B1082245 : Blo 960589 1082245 := bbase (se 4 (by rfl) ⟨101460, by rfl⟩ : syracuseStep 1082245 = 202921) (by norm_num)
theorem B1442717 : Blo 960589 1442717 := bbase (se 3 (by rfl) ⟨270509, by rfl⟩ : syracuseStep 1442717 = 541019) (by norm_num)
theorem B1082281 : Blo 960589 1082281 := bbase (se 2 (by rfl) ⟨405855, by rfl⟩ : syracuseStep 1082281 = 811711) (by norm_num)
theorem B1442741 : Blo 960589 1442741 := bbase (se 5 (by rfl) ⟨67628, by rfl⟩ : syracuseStep 1442741 = 135257) (by norm_num)
theorem B2163653 : Blo 960589 2163653 := bbase (se 4 (by rfl) ⟨202842, by rfl⟩ : syracuseStep 2163653 = 405685) (by norm_num)
theorem B1442765 : Blo 960589 1442765 := bbase (se 3 (by rfl) ⟨270518, by rfl⟩ : syracuseStep 1442765 = 541037) (by norm_num)
theorem B1082317 : Blo 960589 1082317 := bbase (se 3 (by rfl) ⟨202934, by rfl⟩ : syracuseStep 1082317 = 405869) (by norm_num)
theorem B35652565 : Blo 960589 35652565 := bbase (se 7 (by rfl) ⟨417803, by rfl⟩ : syracuseStep 35652565 = 835607) (by norm_num)
theorem B1442789 : Blo 960589 1442789 := bbase (se 4 (by rfl) ⟨135261, by rfl⟩ : syracuseStep 1442789 = 270523) (by norm_num)
theorem B1082353 : Blo 960589 1082353 := bbase (se 2 (by rfl) ⟨405882, by rfl⟩ : syracuseStep 1082353 = 811765) (by norm_num)
theorem B1442813 : Blo 960589 1442813 := bbase (se 3 (by rfl) ⟨270527, by rfl⟩ : syracuseStep 1442813 = 541055) (by norm_num)
theorem B2163725 : Blo 960589 2163725 := bbase (se 3 (by rfl) ⟨405698, by rfl⟩ : syracuseStep 2163725 = 811397) (by norm_num)
theorem B1442837 : Blo 960589 1442837 := bbase (se 6 (by rfl) ⟨33816, by rfl⟩ : syracuseStep 1442837 = 67633) (by norm_num)
theorem B1082389 : Blo 960589 1082389 := bbase (se 6 (by rfl) ⟨25368, by rfl⟩ : syracuseStep 1082389 = 50737) (by norm_num)
theorem B1442861 : Blo 960589 1442861 := bbase (se 3 (by rfl) ⟨270536, by rfl⟩ : syracuseStep 1442861 = 541073) (by norm_num)
theorem B1082425 : Blo 960589 1082425 := bbase (se 2 (by rfl) ⟨405909, by rfl⟩ : syracuseStep 1082425 = 811819) (by norm_num)
theorem B1442885 : Blo 960589 1442885 := bbase (se 4 (by rfl) ⟨135270, by rfl⟩ : syracuseStep 1442885 = 270541) (by norm_num)
theorem B2163797 : Blo 960589 2163797 := bbase (se 8 (by rfl) ⟨12678, by rfl⟩ : syracuseStep 2163797 = 25357) (by norm_num)
theorem B1442909 : Blo 960589 1442909 := bbase (se 3 (by rfl) ⟨270545, by rfl⟩ : syracuseStep 1442909 = 541091) (by norm_num)
theorem B1082461 : Blo 960589 1082461 := bbase (se 3 (by rfl) ⟨202961, by rfl⟩ : syracuseStep 1082461 = 405923) (by norm_num)
theorem B1442933 : Blo 960589 1442933 := bbase (se 5 (by rfl) ⟨67637, by rfl⟩ : syracuseStep 1442933 = 135275) (by norm_num)
theorem B1082497 : Blo 960589 1082497 := bbase (se 2 (by rfl) ⟨405936, by rfl⟩ : syracuseStep 1082497 = 811873) (by norm_num)
theorem B1442957 : Blo 960589 1442957 := bbase (se 3 (by rfl) ⟨270554, by rfl⟩ : syracuseStep 1442957 = 541109) (by norm_num)
theorem B3081365 : Blo 960589 3081365 := bbase (se 6 (by rfl) ⟨72219, by rfl⟩ : syracuseStep 3081365 = 144439) (by norm_num)
theorem B2163869 : Blo 960589 2163869 := bbase (se 3 (by rfl) ⟨405725, by rfl⟩ : syracuseStep 2163869 = 811451) (by norm_num)
theorem B1442981 : Blo 960589 1442981 := bbase (se 4 (by rfl) ⟨135279, by rfl⟩ : syracuseStep 1442981 = 270559) (by norm_num)
theorem B1541285 : Blo 960589 1541285 := bbase (se 4 (by rfl) ⟨144495, by rfl⟩ : syracuseStep 1541285 = 288991) (by norm_num)
theorem B1082533 : Blo 960589 1082533 := bbase (se 4 (by rfl) ⟨101487, by rfl⟩ : syracuseStep 1082533 = 202975) (by norm_num)
theorem B3245237 : Blo 960589 3245237 := bbase (se 5 (by rfl) ⟨152120, by rfl⟩ : syracuseStep 3245237 = 304241) (by norm_num)
theorem B1443005 : Blo 960589 1443005 := bbase (se 3 (by rfl) ⟨270563, by rfl⟩ : syracuseStep 1443005 = 541127) (by norm_num)
theorem B1082569 : Blo 960589 1082569 := bbase (se 2 (by rfl) ⟨405963, by rfl⟩ : syracuseStep 1082569 = 811927) (by norm_num)
theorem B5473493 : Blo 960589 5473493 := bbase (se 7 (by rfl) ⟨64142, by rfl⟩ : syracuseStep 5473493 = 128285) (by norm_num)
theorem B1443029 : Blo 960589 1443029 := bbase (se 7 (by rfl) ⟨16910, by rfl⟩ : syracuseStep 1443029 = 33821) (by norm_num)
theorem B2163941 : Blo 960589 2163941 := bbase (se 4 (by rfl) ⟨202869, by rfl⟩ : syracuseStep 2163941 = 405739) (by norm_num)
theorem B1443053 : Blo 960589 1443053 := bbase (se 3 (by rfl) ⟨270572, by rfl⟩ : syracuseStep 1443053 = 541145) (by norm_num)
theorem B1082605 : Blo 960589 1082605 := bbase (se 3 (by rfl) ⟨202988, by rfl⟩ : syracuseStep 1082605 = 405977) (by norm_num)
theorem B1443077 : Blo 960589 1443077 := bbase (se 4 (by rfl) ⟨135288, by rfl⟩ : syracuseStep 1443077 = 270577) (by norm_num)
theorem B1082641 : Blo 960589 1082641 := bbase (se 2 (by rfl) ⟨405990, by rfl⟩ : syracuseStep 1082641 = 811981) (by norm_num)
theorem B1443101 : Blo 960589 1443101 := bbase (se 3 (by rfl) ⟨270581, by rfl⟩ : syracuseStep 1443101 = 541163) (by norm_num)
theorem B2164013 : Blo 960589 2164013 := bbase (se 3 (by rfl) ⟨405752, by rfl⟩ : syracuseStep 2164013 = 811505) (by norm_num)
theorem B1443125 : Blo 960589 1443125 := bbase (se 5 (by rfl) ⟨67646, by rfl⟩ : syracuseStep 1443125 = 135293) (by norm_num)
theorem B1082677 : Blo 960589 1082677 := bbase (se 5 (by rfl) ⟨50750, by rfl⟩ : syracuseStep 1082677 = 101501) (by norm_num)
theorem B1443149 : Blo 960589 1443149 := bbase (se 3 (by rfl) ⟨270590, by rfl⟩ : syracuseStep 1443149 = 541181) (by norm_num)
theorem B1082713 : Blo 960589 1082713 := bbase (se 2 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 1082713 = 812035) (by norm_num)
theorem B1443173 : Blo 960589 1443173 := bbase (se 4 (by rfl) ⟨135297, by rfl⟩ : syracuseStep 1443173 = 270595) (by norm_num)
theorem B1541477 : Blo 960589 1541477 := bbase (se 4 (by rfl) ⟨144513, by rfl⟩ : syracuseStep 1541477 = 289027) (by norm_num)
theorem B2164085 : Blo 960589 2164085 := bbase (se 5 (by rfl) ⟨101441, by rfl⟩ : syracuseStep 2164085 = 202883) (by norm_num)
theorem B1443197 : Blo 960589 1443197 := bbase (se 3 (by rfl) ⟨270599, by rfl⟩ : syracuseStep 1443197 = 541199) (by norm_num)
theorem B1082749 : Blo 960589 1082749 := bbase (se 3 (by rfl) ⟨203015, by rfl⟩ : syracuseStep 1082749 = 406031) (by norm_num)
theorem B1443221 : Blo 960589 1443221 := bbase (se 6 (by rfl) ⟨33825, by rfl⟩ : syracuseStep 1443221 = 67651) (by norm_num)
theorem B8226197 : Blo 960589 8226197 := bbase (se 6 (by rfl) ⟨192801, by rfl⟩ : syracuseStep 8226197 = 385603) (by norm_num)
theorem B1082785 : Blo 960589 1082785 := bbase (se 2 (by rfl) ⟨406044, by rfl⟩ : syracuseStep 1082785 = 812089) (by norm_num)
theorem B1443245 : Blo 960589 1443245 := bbase (se 3 (by rfl) ⟨270608, by rfl⟩ : syracuseStep 1443245 = 541217) (by norm_num)
theorem B2164157 : Blo 960589 2164157 := bbase (se 3 (by rfl) ⟨405779, by rfl⟩ : syracuseStep 2164157 = 811559) (by norm_num)
theorem B1443269 : Blo 960589 1443269 := bbase (se 4 (by rfl) ⟨135306, by rfl⟩ : syracuseStep 1443269 = 270613) (by norm_num)
theorem B1082821 : Blo 960589 1082821 := bbase (se 4 (by rfl) ⟨101514, by rfl⟩ : syracuseStep 1082821 = 203029) (by norm_num)
theorem B8455637 : Blo 960589 8455637 := bbase (se 7 (by rfl) ⟨99089, by rfl⟩ : syracuseStep 8455637 = 198179) (by norm_num)
theorem B1443293 : Blo 960589 1443293 := bbase (se 3 (by rfl) ⟨270617, by rfl⟩ : syracuseStep 1443293 = 541235) (by norm_num)
theorem B1541605 : Blo 960589 1541605 := bbase (se 4 (by rfl) ⟨144525, by rfl⟩ : syracuseStep 1541605 = 289051) (by norm_num)
theorem B1082857 : Blo 960589 1082857 := bbase (se 2 (by rfl) ⟨406071, by rfl⟩ : syracuseStep 1082857 = 812143) (by norm_num)
theorem B1443317 : Blo 960589 1443317 := bbase (se 5 (by rfl) ⟨67655, by rfl⟩ : syracuseStep 1443317 = 135311) (by norm_num)
theorem B2164229 : Blo 960589 2164229 := bbase (se 4 (by rfl) ⟨202896, by rfl⟩ : syracuseStep 2164229 = 405793) (by norm_num)
theorem B1443341 : Blo 960589 1443341 := bbase (se 3 (by rfl) ⟨270626, by rfl⟩ : syracuseStep 1443341 = 541253) (by norm_num)
theorem B1082893 : Blo 960589 1082893 := bbase (se 3 (by rfl) ⟨203042, by rfl⟩ : syracuseStep 1082893 = 406085) (by norm_num)
theorem B1443365 : Blo 960589 1443365 := bbase (se 4 (by rfl) ⟨135315, by rfl⟩ : syracuseStep 1443365 = 270631) (by norm_num)
theorem B1082929 : Blo 960589 1082929 := bbase (se 2 (by rfl) ⟨406098, by rfl⟩ : syracuseStep 1082929 = 812197) (by norm_num)
theorem B1443389 : Blo 960589 1443389 := bbase (se 3 (by rfl) ⟨270635, by rfl⟩ : syracuseStep 1443389 = 541271) (by norm_num)
theorem B2197061 : Blo 960589 2197061 := bbase (se 4 (by rfl) ⟨205974, by rfl⟩ : syracuseStep 2197061 = 411949) (by norm_num)
theorem B2164301 : Blo 960589 2164301 := bbase (se 3 (by rfl) ⟨405806, by rfl⟩ : syracuseStep 2164301 = 811613) (by norm_num)
theorem B1443413 : Blo 960589 1443413 := bbase (se 8 (by rfl) ⟨8457, by rfl⟩ : syracuseStep 1443413 = 16915) (by norm_num)
theorem B1082965 : Blo 960589 1082965 := bbase (se 8 (by rfl) ⟨6345, by rfl⟩ : syracuseStep 1082965 = 12691) (by norm_num)
theorem B3245669 : Blo 960589 3245669 := bbase (se 4 (by rfl) ⟨304281, by rfl⟩ : syracuseStep 3245669 = 608563) (by norm_num)
theorem B1443437 : Blo 960589 1443437 := bbase (se 3 (by rfl) ⟨270644, by rfl⟩ : syracuseStep 1443437 = 541289) (by norm_num)
theorem B1083001 : Blo 960589 1083001 := bbase (se 2 (by rfl) ⟨406125, by rfl⟩ : syracuseStep 1083001 = 812251) (by norm_num)
theorem B1443461 : Blo 960589 1443461 := bbase (se 4 (by rfl) ⟨135324, by rfl⟩ : syracuseStep 1443461 = 270649) (by norm_num)
theorem B2164373 : Blo 960589 2164373 := bbase (se 6 (by rfl) ⟨50727, by rfl⟩ : syracuseStep 2164373 = 101455) (by norm_num)
theorem B1443485 : Blo 960589 1443485 := bbase (se 3 (by rfl) ⟨270653, by rfl⟩ : syracuseStep 1443485 = 541307) (by norm_num)
theorem B1083037 : Blo 960589 1083037 := bbase (se 3 (by rfl) ⟨203069, by rfl⟩ : syracuseStep 1083037 = 406139) (by norm_num)
theorem B1443509 : Blo 960589 1443509 := bbase (se 5 (by rfl) ⟨67664, by rfl⟩ : syracuseStep 1443509 = 135329) (by norm_num)
theorem B1083073 : Blo 960589 1083073 := bbase (se 2 (by rfl) ⟨406152, by rfl⟩ : syracuseStep 1083073 = 812305) (by norm_num)
theorem B1443533 : Blo 960589 1443533 := bbase (se 3 (by rfl) ⟨270662, by rfl⟩ : syracuseStep 1443533 = 541325) (by norm_num)
theorem B2164445 : Blo 960589 2164445 := bbase (se 3 (by rfl) ⟨405833, by rfl⟩ : syracuseStep 2164445 = 811667) (by norm_num)
theorem B1443557 : Blo 960589 1443557 := bbase (se 4 (by rfl) ⟨135333, by rfl⟩ : syracuseStep 1443557 = 270667) (by norm_num)
theorem B1083109 : Blo 960589 1083109 := bbase (se 4 (by rfl) ⟨101541, by rfl⟩ : syracuseStep 1083109 = 203083) (by norm_num)
theorem B1443581 : Blo 960589 1443581 := bbase (se 3 (by rfl) ⟨270671, by rfl⟩ : syracuseStep 1443581 = 541343) (by norm_num)
theorem B1083145 : Blo 960589 1083145 := bbase (se 2 (by rfl) ⟨406179, by rfl⟩ : syracuseStep 1083145 = 812359) (by norm_num)
theorem B1443605 : Blo 960589 1443605 := bbase (se 6 (by rfl) ⟨33834, by rfl⟩ : syracuseStep 1443605 = 67669) (by norm_num)
theorem B2164517 : Blo 960589 2164517 := bbase (se 4 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 2164517 = 405847) (by norm_num)
theorem B1443629 : Blo 960589 1443629 := bbase (se 3 (by rfl) ⟨270680, by rfl⟩ : syracuseStep 1443629 = 541361) (by norm_num)
theorem B1083181 : Blo 960589 1083181 := bbase (se 3 (by rfl) ⟨203096, by rfl⟩ : syracuseStep 1083181 = 406193) (by norm_num)
theorem B1443653 : Blo 960589 1443653 := bbase (se 4 (by rfl) ⟨135342, by rfl⟩ : syracuseStep 1443653 = 270685) (by norm_num)
theorem B1083217 : Blo 960589 1083217 := bbase (se 2 (by rfl) ⟨406206, by rfl⟩ : syracuseStep 1083217 = 812413) (by norm_num)
theorem B1443677 : Blo 960589 1443677 := bbase (se 3 (by rfl) ⟨270689, by rfl⟩ : syracuseStep 1443677 = 541379) (by norm_num)
theorem B2164589 : Blo 960589 2164589 := bbase (se 3 (by rfl) ⟨405860, by rfl⟩ : syracuseStep 2164589 = 811721) (by norm_num)
theorem B1443701 : Blo 960589 1443701 := bbase (se 5 (by rfl) ⟨67673, by rfl⟩ : syracuseStep 1443701 = 135347) (by norm_num)
theorem B1083253 : Blo 960589 1083253 := bbase (se 5 (by rfl) ⟨50777, by rfl⟩ : syracuseStep 1083253 = 101555) (by norm_num)
theorem B1443725 : Blo 960589 1443725 := bbase (se 3 (by rfl) ⟨270698, by rfl⟩ : syracuseStep 1443725 = 541397) (by norm_num)
theorem B3082133 : Blo 960589 3082133 := bbase (se 6 (by rfl) ⟨72237, by rfl⟩ : syracuseStep 3082133 = 144475) (by norm_num)
theorem B1083289 : Blo 960589 1083289 := bbase (se 2 (by rfl) ⟨406233, by rfl⟩ : syracuseStep 1083289 = 812467) (by norm_num)
theorem B1443749 : Blo 960589 1443749 := bbase (se 4 (by rfl) ⟨135351, by rfl⟩ : syracuseStep 1443749 = 270703) (by norm_num)
theorem B2164661 : Blo 960589 2164661 := bbase (se 5 (by rfl) ⟨101468, by rfl⟩ : syracuseStep 2164661 = 202937) (by norm_num)
theorem B1443773 : Blo 960589 1443773 := bbase (se 3 (by rfl) ⟨270707, by rfl⟩ : syracuseStep 1443773 = 541415) (by norm_num)
theorem B1083325 : Blo 960589 1083325 := bbase (se 3 (by rfl) ⟨203123, by rfl⟩ : syracuseStep 1083325 = 406247) (by norm_num)
theorem B1443797 : Blo 960589 1443797 := bbase (se 7 (by rfl) ⟨16919, by rfl⟩ : syracuseStep 1443797 = 33839) (by norm_num)
theorem B1083361 : Blo 960589 1083361 := bbase (se 2 (by rfl) ⟨406260, by rfl⟩ : syracuseStep 1083361 = 812521) (by norm_num)
theorem B1443821 : Blo 960589 1443821 := bbase (se 3 (by rfl) ⟨270716, by rfl⟩ : syracuseStep 1443821 = 541433) (by norm_num)
theorem B2164733 : Blo 960589 2164733 := bbase (se 3 (by rfl) ⟨405887, by rfl⟩ : syracuseStep 2164733 = 811775) (by norm_num)
theorem B1443845 : Blo 960589 1443845 := bbase (se 4 (by rfl) ⟨135360, by rfl⟩ : syracuseStep 1443845 = 270721) (by norm_num)
theorem B1083397 : Blo 960589 1083397 := bbase (se 4 (by rfl) ⟨101568, by rfl⟩ : syracuseStep 1083397 = 203137) (by norm_num)
theorem B3246101 : Blo 960589 3246101 := bbase (se 6 (by rfl) ⟨76080, by rfl⟩ : syracuseStep 3246101 = 152161) (by norm_num)
theorem B1443869 : Blo 960589 1443869 := bbase (se 3 (by rfl) ⟨270725, by rfl⟩ : syracuseStep 1443869 = 541451) (by norm_num)
theorem B1083433 : Blo 960589 1083433 := bbase (se 2 (by rfl) ⟨406287, by rfl⟩ : syracuseStep 1083433 = 812575) (by norm_num)
theorem B1443893 : Blo 960589 1443893 := bbase (se 5 (by rfl) ⟨67682, by rfl⟩ : syracuseStep 1443893 = 135365) (by norm_num)
theorem B2164805 : Blo 960589 2164805 := bbase (se 4 (by rfl) ⟨202950, by rfl⟩ : syracuseStep 2164805 = 405901) (by norm_num)
theorem B1443917 : Blo 960589 1443917 := bbase (se 3 (by rfl) ⟨270734, by rfl⟩ : syracuseStep 1443917 = 541469) (by norm_num)
theorem B1083469 : Blo 960589 1083469 := bbase (se 3 (by rfl) ⟨203150, by rfl⟩ : syracuseStep 1083469 = 406301) (by norm_num)
theorem B1443941 : Blo 960589 1443941 := bbase (se 4 (by rfl) ⟨135369, by rfl⟩ : syracuseStep 1443941 = 270739) (by norm_num)
theorem B1542245 : Blo 960589 1542245 := bbase (se 4 (by rfl) ⟨144585, by rfl⟩ : syracuseStep 1542245 = 289171) (by norm_num)
theorem B1083505 : Blo 960589 1083505 := bbase (se 2 (by rfl) ⟨406314, by rfl⟩ : syracuseStep 1083505 = 812629) (by norm_num)
theorem B1443965 : Blo 960589 1443965 := bbase (se 3 (by rfl) ⟨270743, by rfl⟩ : syracuseStep 1443965 = 541487) (by norm_num)
theorem B2164877 : Blo 960589 2164877 := bbase (se 3 (by rfl) ⟨405914, by rfl⟩ : syracuseStep 2164877 = 811829) (by norm_num)
theorem B1443989 : Blo 960589 1443989 := bbase (se 6 (by rfl) ⟨33843, by rfl⟩ : syracuseStep 1443989 = 67687) (by norm_num)
theorem B1083541 : Blo 960589 1083541 := bbase (se 6 (by rfl) ⟨25395, by rfl⟩ : syracuseStep 1083541 = 50791) (by norm_num)
theorem B1444013 : Blo 960589 1444013 := bbase (se 3 (by rfl) ⟨270752, by rfl⟩ : syracuseStep 1444013 = 541505) (by norm_num)
theorem B1083577 : Blo 960589 1083577 := bbase (se 2 (by rfl) ⟨406341, by rfl⟩ : syracuseStep 1083577 = 812683) (by norm_num)
theorem B1444037 : Blo 960589 1444037 := bbase (se 4 (by rfl) ⟨135378, by rfl⟩ : syracuseStep 1444037 = 270757) (by norm_num)
theorem B2164949 : Blo 960589 2164949 := bbase (se 7 (by rfl) ⟨25370, by rfl⟩ : syracuseStep 2164949 = 50741) (by norm_num)
theorem B1444061 : Blo 960589 1444061 := bbase (se 3 (by rfl) ⟨270761, by rfl⟩ : syracuseStep 1444061 = 541523) (by norm_num)
theorem B1083613 : Blo 960589 1083613 := bbase (se 3 (by rfl) ⟨203177, by rfl⟩ : syracuseStep 1083613 = 406355) (by norm_num)
theorem B1444085 : Blo 960589 1444085 := bbase (se 5 (by rfl) ⟨67691, by rfl⟩ : syracuseStep 1444085 = 135383) (by norm_num)
theorem B1083649 : Blo 960589 1083649 := bbase (se 2 (by rfl) ⟨406368, by rfl⟩ : syracuseStep 1083649 = 812737) (by norm_num)
theorem B1444109 : Blo 960589 1444109 := bbase (se 3 (by rfl) ⟨270770, by rfl⟩ : syracuseStep 1444109 = 541541) (by norm_num)
theorem B2165021 : Blo 960589 2165021 := bbase (se 3 (by rfl) ⟨405941, by rfl⟩ : syracuseStep 2165021 = 811883) (by norm_num)
theorem B1444133 : Blo 960589 1444133 := bbase (se 4 (by rfl) ⟨135387, by rfl⟩ : syracuseStep 1444133 = 270775) (by norm_num)
theorem B1083685 : Blo 960589 1083685 := bbase (se 4 (by rfl) ⟨101595, by rfl⟩ : syracuseStep 1083685 = 203191) (by norm_num)
theorem B1444157 : Blo 960589 1444157 := bbase (se 3 (by rfl) ⟨270779, by rfl⟩ : syracuseStep 1444157 = 541559) (by norm_num)
theorem B1083721 : Blo 960589 1083721 := bbase (se 2 (by rfl) ⟨406395, by rfl⟩ : syracuseStep 1083721 = 812791) (by norm_num)
theorem B1444181 : Blo 960589 1444181 := bbase (se 10 (by rfl) ⟨2115, by rfl⟩ : syracuseStep 1444181 = 4231) (by norm_num)
theorem B2165093 : Blo 960589 2165093 := bbase (se 4 (by rfl) ⟨202977, by rfl⟩ : syracuseStep 2165093 = 405955) (by norm_num)
theorem B1444205 : Blo 960589 1444205 := bbase (se 3 (by rfl) ⟨270788, by rfl⟩ : syracuseStep 1444205 = 541577) (by norm_num)
theorem B1083757 : Blo 960589 1083757 := bbase (se 3 (by rfl) ⟨203204, by rfl⟩ : syracuseStep 1083757 = 406409) (by norm_num)
theorem B1444229 : Blo 960589 1444229 := bbase (se 4 (by rfl) ⟨135396, by rfl⟩ : syracuseStep 1444229 = 270793) (by norm_num)
theorem B2197901 : Blo 960589 2197901 := bbase (se 3 (by rfl) ⟨412106, by rfl⟩ : syracuseStep 2197901 = 824213) (by norm_num)
theorem B1083793 : Blo 960589 1083793 := bbase (se 2 (by rfl) ⟨406422, by rfl⟩ : syracuseStep 1083793 = 812845) (by norm_num)
theorem B3082645 : Blo 960589 3082645 := bbase (se 6 (by rfl) ⟨72249, by rfl⟩ : syracuseStep 3082645 = 144499) (by norm_num)
theorem B1444253 : Blo 960589 1444253 := bbase (se 3 (by rfl) ⟨270797, by rfl⟩ : syracuseStep 1444253 = 541595) (by norm_num)
theorem B2165165 : Blo 960589 2165165 := bbase (se 3 (by rfl) ⟨405968, by rfl⟩ : syracuseStep 2165165 = 811937) (by norm_num)
theorem B1444277 : Blo 960589 1444277 := bbase (se 5 (by rfl) ⟨67700, by rfl⟩ : syracuseStep 1444277 = 135401) (by norm_num)
theorem B1083829 : Blo 960589 1083829 := bbase (se 5 (by rfl) ⟨50804, by rfl⟩ : syracuseStep 1083829 = 101609) (by norm_num)
theorem B3246533 : Blo 960589 3246533 := bbase (se 4 (by rfl) ⟨304362, by rfl⟩ : syracuseStep 3246533 = 608725) (by norm_num)
theorem B1444301 : Blo 960589 1444301 := bbase (se 3 (by rfl) ⟨270806, by rfl⟩ : syracuseStep 1444301 = 541613) (by norm_num)
theorem B1083865 : Blo 960589 1083865 := bbase (se 2 (by rfl) ⟨406449, by rfl⟩ : syracuseStep 1083865 = 812899) (by norm_num)
theorem B1444325 : Blo 960589 1444325 := bbase (se 4 (by rfl) ⟨135405, by rfl⟩ : syracuseStep 1444325 = 270811) (by norm_num)
theorem B2165237 : Blo 960589 2165237 := bbase (se 5 (by rfl) ⟨101495, by rfl⟩ : syracuseStep 2165237 = 202991) (by norm_num)
theorem B1444349 : Blo 960589 1444349 := bbase (se 3 (by rfl) ⟨270815, by rfl⟩ : syracuseStep 1444349 = 541631) (by norm_num)
theorem B1083901 : Blo 960589 1083901 := bbase (se 3 (by rfl) ⟨203231, by rfl⟩ : syracuseStep 1083901 = 406463) (by norm_num)
theorem B1444373 : Blo 960589 1444373 := bbase (se 6 (by rfl) ⟨33852, by rfl⟩ : syracuseStep 1444373 = 67705) (by norm_num)
theorem B1083937 : Blo 960589 1083937 := bbase (se 2 (by rfl) ⟨406476, by rfl⟩ : syracuseStep 1083937 = 812953) (by norm_num)
theorem B1444397 : Blo 960589 1444397 := bbase (se 3 (by rfl) ⟨270824, by rfl⟩ : syracuseStep 1444397 = 541649) (by norm_num)
theorem B1542701 : Blo 960589 1542701 := bbase (se 3 (by rfl) ⟨289256, by rfl⟩ : syracuseStep 1542701 = 578513) (by norm_num)
theorem B2165309 : Blo 960589 2165309 := bbase (se 3 (by rfl) ⟨405995, by rfl⟩ : syracuseStep 2165309 = 811991) (by norm_num)
theorem B1444421 : Blo 960589 1444421 := bbase (se 4 (by rfl) ⟨135414, by rfl⟩ : syracuseStep 1444421 = 270829) (by norm_num)
theorem B1083973 : Blo 960589 1083973 := bbase (se 4 (by rfl) ⟨101622, by rfl⟩ : syracuseStep 1083973 = 203245) (by norm_num)
theorem B1444445 : Blo 960589 1444445 := bbase (se 3 (by rfl) ⟨270833, by rfl⟩ : syracuseStep 1444445 = 541667) (by norm_num)
theorem B1084009 : Blo 960589 1084009 := bbase (se 2 (by rfl) ⟨406503, by rfl⟩ : syracuseStep 1084009 = 813007) (by norm_num)
theorem B1444469 : Blo 960589 1444469 := bbase (se 5 (by rfl) ⟨67709, by rfl⟩ : syracuseStep 1444469 = 135419) (by norm_num)
theorem B2165381 : Blo 960589 2165381 := bbase (se 4 (by rfl) ⟨203004, by rfl⟩ : syracuseStep 2165381 = 406009) (by norm_num)
theorem B1444493 : Blo 960589 1444493 := bbase (se 3 (by rfl) ⟨270842, by rfl⟩ : syracuseStep 1444493 = 541685) (by norm_num)
theorem B1084045 : Blo 960589 1084045 := bbase (se 3 (by rfl) ⟨203258, by rfl⟩ : syracuseStep 1084045 = 406517) (by norm_num)
theorem B1444517 : Blo 960589 1444517 := bbase (se 4 (by rfl) ⟨135423, by rfl⟩ : syracuseStep 1444517 = 270847) (by norm_num)
theorem B1084081 : Blo 960589 1084081 := bbase (se 2 (by rfl) ⟨406530, by rfl⟩ : syracuseStep 1084081 = 813061) (by norm_num)
theorem B1444541 : Blo 960589 1444541 := bbase (se 3 (by rfl) ⟨270851, by rfl⟩ : syracuseStep 1444541 = 541703) (by norm_num)
theorem B2165453 : Blo 960589 2165453 := bbase (se 3 (by rfl) ⟨406022, by rfl⟩ : syracuseStep 2165453 = 812045) (by norm_num)
theorem B1444565 : Blo 960589 1444565 := bbase (se 7 (by rfl) ⟨16928, by rfl⟩ : syracuseStep 1444565 = 33857) (by norm_num)
theorem B1084117 : Blo 960589 1084117 := bbase (se 7 (by rfl) ⟨12704, by rfl⟩ : syracuseStep 1084117 = 25409) (by norm_num)
theorem B1444589 : Blo 960589 1444589 := bbase (se 3 (by rfl) ⟨270860, by rfl⟩ : syracuseStep 1444589 = 541721) (by norm_num)
theorem B1084153 : Blo 960589 1084153 := bbase (se 2 (by rfl) ⟨406557, by rfl⟩ : syracuseStep 1084153 = 813115) (by norm_num)
theorem B1444613 : Blo 960589 1444613 := bbase (se 4 (by rfl) ⟨135432, by rfl⟩ : syracuseStep 1444613 = 270865) (by norm_num)
theorem B1542925 : Blo 960589 1542925 := bbase (se 3 (by rfl) ⟨289298, by rfl⟩ : syracuseStep 1542925 = 578597) (by norm_num)
theorem B2165525 : Blo 960589 2165525 := bbase (se 6 (by rfl) ⟨50754, by rfl⟩ : syracuseStep 2165525 = 101509) (by norm_num)
theorem B1444637 : Blo 960589 1444637 := bbase (se 3 (by rfl) ⟨270869, by rfl⟩ : syracuseStep 1444637 = 541739) (by norm_num)
theorem B1084189 : Blo 960589 1084189 := bbase (se 3 (by rfl) ⟨203285, by rfl⟩ : syracuseStep 1084189 = 406571) (by norm_num)
theorem B1444661 : Blo 960589 1444661 := bbase (se 5 (by rfl) ⟨67718, by rfl⟩ : syracuseStep 1444661 = 135437) (by norm_num)
theorem B1084225 : Blo 960589 1084225 := bbase (se 2 (by rfl) ⟨406584, by rfl⟩ : syracuseStep 1084225 = 813169) (by norm_num)
theorem B1444685 : Blo 960589 1444685 := bbase (se 3 (by rfl) ⟨270878, by rfl⟩ : syracuseStep 1444685 = 541757) (by norm_num)
theorem B1542989 : Blo 960589 1542989 := bbase (se 3 (by rfl) ⟨289310, by rfl⟩ : syracuseStep 1542989 = 578621) (by norm_num)
theorem B2165597 : Blo 960589 2165597 := bbase (se 3 (by rfl) ⟨406049, by rfl⟩ : syracuseStep 2165597 = 812099) (by norm_num)
theorem B1444709 : Blo 960589 1444709 := bbase (se 4 (by rfl) ⟨135441, by rfl⟩ : syracuseStep 1444709 = 270883) (by norm_num)
theorem B1084261 : Blo 960589 1084261 := bbase (se 4 (by rfl) ⟨101649, by rfl⟩ : syracuseStep 1084261 = 203299) (by norm_num)
theorem B3246965 : Blo 960589 3246965 := bbase (se 5 (by rfl) ⟨152201, by rfl⟩ : syracuseStep 3246965 = 304403) (by norm_num)
theorem B1444733 : Blo 960589 1444733 := bbase (se 3 (by rfl) ⟨270887, by rfl⟩ : syracuseStep 1444733 = 541775) (by norm_num)
theorem B1084297 : Blo 960589 1084297 := bbase (se 2 (by rfl) ⟨406611, by rfl⟩ : syracuseStep 1084297 = 813223) (by norm_num)
theorem B1444757 : Blo 960589 1444757 := bbase (se 6 (by rfl) ⟨33861, by rfl⟩ : syracuseStep 1444757 = 67723) (by norm_num)
theorem B2165669 : Blo 960589 2165669 := bbase (se 4 (by rfl) ⟨203031, by rfl⟩ : syracuseStep 2165669 = 406063) (by norm_num)
theorem B1444781 : Blo 960589 1444781 := bbase (se 3 (by rfl) ⟨270896, by rfl⟩ : syracuseStep 1444781 = 541793) (by norm_num)
theorem B1084333 : Blo 960589 1084333 := bbase (se 3 (by rfl) ⟨203312, by rfl⟩ : syracuseStep 1084333 = 406625) (by norm_num)
theorem B1444805 : Blo 960589 1444805 := bbase (se 4 (by rfl) ⟨135450, by rfl⟩ : syracuseStep 1444805 = 270901) (by norm_num)
theorem B1543117 : Blo 960589 1543117 := bbase (se 3 (by rfl) ⟨289334, by rfl⟩ : syracuseStep 1543117 = 578669) (by norm_num)
theorem B1084369 : Blo 960589 1084369 := bbase (se 2 (by rfl) ⟨406638, by rfl⟩ : syracuseStep 1084369 = 813277) (by norm_num)
theorem B1444829 : Blo 960589 1444829 := bbase (se 3 (by rfl) ⟨270905, by rfl⟩ : syracuseStep 1444829 = 541811) (by norm_num)
theorem B2165741 : Blo 960589 2165741 := bbase (se 3 (by rfl) ⟨406076, by rfl⟩ : syracuseStep 2165741 = 812153) (by norm_num)
theorem B6163445 : Blo 960589 6163445 := bbase (se 5 (by rfl) ⟨288911, by rfl⟩ : syracuseStep 6163445 = 577823) (by norm_num)
theorem B1444853 : Blo 960589 1444853 := bbase (se 5 (by rfl) ⟨67727, by rfl⟩ : syracuseStep 1444853 = 135455) (by norm_num)
theorem B1084405 : Blo 960589 1084405 := bbase (se 5 (by rfl) ⟨50831, by rfl⟩ : syracuseStep 1084405 = 101663) (by norm_num)
theorem B1444877 : Blo 960589 1444877 := bbase (se 3 (by rfl) ⟨270914, by rfl⟩ : syracuseStep 1444877 = 541829) (by norm_num)
theorem B1084441 : Blo 960589 1084441 := bbase (se 2 (by rfl) ⟨406665, by rfl⟩ : syracuseStep 1084441 = 813331) (by norm_num)
theorem B1444901 : Blo 960589 1444901 := bbase (se 4 (by rfl) ⟨135459, by rfl⟩ : syracuseStep 1444901 = 270919) (by norm_num)
theorem B2165813 : Blo 960589 2165813 := bbase (se 5 (by rfl) ⟨101522, by rfl⟩ : syracuseStep 2165813 = 203045) (by norm_num)
theorem B1444925 : Blo 960589 1444925 := bbase (se 3 (by rfl) ⟨270923, by rfl⟩ : syracuseStep 1444925 = 541847) (by norm_num)
theorem B1084477 : Blo 960589 1084477 := bbase (se 3 (by rfl) ⟨203339, by rfl⟩ : syracuseStep 1084477 = 406679) (by norm_num)
theorem B1444949 : Blo 960589 1444949 := bbase (se 8 (by rfl) ⟨8466, by rfl⟩ : syracuseStep 1444949 = 16933) (by norm_num)
theorem B1084513 : Blo 960589 1084513 := bbase (se 2 (by rfl) ⟨406692, by rfl⟩ : syracuseStep 1084513 = 813385) (by norm_num)
theorem B1444973 : Blo 960589 1444973 := bbase (se 3 (by rfl) ⟨270932, by rfl⟩ : syracuseStep 1444973 = 541865) (by norm_num)
theorem B2165885 : Blo 960589 2165885 := bbase (se 3 (by rfl) ⟨406103, by rfl⟩ : syracuseStep 2165885 = 812207) (by norm_num)
theorem B1444997 : Blo 960589 1444997 := bbase (se 4 (by rfl) ⟨135468, by rfl⟩ : syracuseStep 1444997 = 270937) (by norm_num)
theorem B1084549 : Blo 960589 1084549 := bbase (se 4 (by rfl) ⟨101676, by rfl⟩ : syracuseStep 1084549 = 203353) (by norm_num)
theorem B1445021 : Blo 960589 1445021 := bbase (se 3 (by rfl) ⟨270941, by rfl⟩ : syracuseStep 1445021 = 541883) (by norm_num)
theorem B1084585 : Blo 960589 1084585 := bbase (se 2 (by rfl) ⟨406719, by rfl⟩ : syracuseStep 1084585 = 813439) (by norm_num)
theorem B1445045 : Blo 960589 1445045 := bbase (se 5 (by rfl) ⟨67736, by rfl⟩ : syracuseStep 1445045 = 135473) (by norm_num)
theorem B2165957 : Blo 960589 2165957 := bbase (se 4 (by rfl) ⟨203058, by rfl⟩ : syracuseStep 2165957 = 406117) (by norm_num)
theorem B1445069 : Blo 960589 1445069 := bbase (se 3 (by rfl) ⟨270950, by rfl⟩ : syracuseStep 1445069 = 541901) (by norm_num)
theorem B1084621 : Blo 960589 1084621 := bbase (se 3 (by rfl) ⟨203366, by rfl⟩ : syracuseStep 1084621 = 406733) (by norm_num)
theorem B1445093 : Blo 960589 1445093 := bbase (se 4 (by rfl) ⟨135477, by rfl⟩ : syracuseStep 1445093 = 270955) (by norm_num)
theorem B1084657 : Blo 960589 1084657 := bbase (se 2 (by rfl) ⟨406746, by rfl⟩ : syracuseStep 1084657 = 813493) (by norm_num)
theorem B1445117 : Blo 960589 1445117 := bbase (se 3 (by rfl) ⟨270959, by rfl⟩ : syracuseStep 1445117 = 541919) (by norm_num)
theorem B1215749 : Blo 960589 1215749 := bbase (se 4 (by rfl) ⟨113976, by rfl⟩ : syracuseStep 1215749 = 227953) (by norm_num)
theorem B2166029 : Blo 960589 2166029 := bbase (se 3 (by rfl) ⟨406130, by rfl⟩ : syracuseStep 2166029 = 812261) (by norm_num)
theorem B1445141 : Blo 960589 1445141 := bbase (se 6 (by rfl) ⟨33870, by rfl⟩ : syracuseStep 1445141 = 67741) (by norm_num)
theorem B1084693 : Blo 960589 1084693 := bbase (se 6 (by rfl) ⟨25422, by rfl⟩ : syracuseStep 1084693 = 50845) (by norm_num)
theorem B3247397 : Blo 960589 3247397 := bbase (se 4 (by rfl) ⟨304443, by rfl⟩ : syracuseStep 3247397 = 608887) (by norm_num)
theorem B1445165 : Blo 960589 1445165 := bbase (se 3 (by rfl) ⟨270968, by rfl⟩ : syracuseStep 1445165 = 541937) (by norm_num)
theorem B1084729 : Blo 960589 1084729 := bbase (se 2 (by rfl) ⟨406773, by rfl⟩ : syracuseStep 1084729 = 813547) (by norm_num)
theorem B1215805 : Blo 960589 1215805 := bbase (se 3 (by rfl) ⟨227963, by rfl⟩ : syracuseStep 1215805 = 455927) (by norm_num)
theorem B1445189 : Blo 960589 1445189 := bbase (se 4 (by rfl) ⟨135486, by rfl⟩ : syracuseStep 1445189 = 270973) (by norm_num)
theorem B2166101 : Blo 960589 2166101 := bbase (se 11 (by rfl) ⟨1586, by rfl⟩ : syracuseStep 2166101 = 3173) (by norm_num)
theorem B1445213 : Blo 960589 1445213 := bbase (se 3 (by rfl) ⟨270977, by rfl⟩ : syracuseStep 1445213 = 541955) (by norm_num)
theorem B1084765 : Blo 960589 1084765 := bbase (se 3 (by rfl) ⟨203393, by rfl⟩ : syracuseStep 1084765 = 406787) (by norm_num)
theorem B5475701 : Blo 960589 5475701 := bbase (se 5 (by rfl) ⟨256673, by rfl⟩ : syracuseStep 5475701 = 513347) (by norm_num)
theorem B1445237 : Blo 960589 1445237 := bbase (se 5 (by rfl) ⟨67745, by rfl⟩ : syracuseStep 1445237 = 135491) (by norm_num)
theorem B1084801 : Blo 960589 1084801 := bbase (se 2 (by rfl) ⟨406800, by rfl⟩ : syracuseStep 1084801 = 813601) (by norm_num)
theorem B1445261 : Blo 960589 1445261 := bbase (se 3 (by rfl) ⟨270986, by rfl⟩ : syracuseStep 1445261 = 541973) (by norm_num)
theorem B1215901 : Blo 960589 1215901 := bbase (se 3 (by rfl) ⟨227981, by rfl⟩ : syracuseStep 1215901 = 455963) (by norm_num)
theorem B2166173 : Blo 960589 2166173 := bbase (se 3 (by rfl) ⟨406157, by rfl⟩ : syracuseStep 2166173 = 812315) (by norm_num)
theorem B1445285 : Blo 960589 1445285 := bbase (se 4 (by rfl) ⟨135495, by rfl⟩ : syracuseStep 1445285 = 270991) (by norm_num)
theorem B1084837 : Blo 960589 1084837 := bbase (se 4 (by rfl) ⟨101703, by rfl⟩ : syracuseStep 1084837 = 203407) (by norm_num)
theorem B4623797 : Blo 960589 4623797 := bbase (se 5 (by rfl) ⟨216740, by rfl⟩ : syracuseStep 4623797 = 433481) (by norm_num)
theorem B1445309 : Blo 960589 1445309 := bbase (se 3 (by rfl) ⟨270995, by rfl⟩ : syracuseStep 1445309 = 541991) (by norm_num)
theorem B1084873 : Blo 960589 1084873 := bbase (se 2 (by rfl) ⟨406827, by rfl⟩ : syracuseStep 1084873 = 813655) (by norm_num)
theorem B1445333 : Blo 960589 1445333 := bbase (se 7 (by rfl) ⟨16937, by rfl⟩ : syracuseStep 1445333 = 33875) (by norm_num)
theorem B2166245 : Blo 960589 2166245 := bbase (se 4 (by rfl) ⟨203085, by rfl⟩ : syracuseStep 2166245 = 406171) (by norm_num)
theorem B1445357 : Blo 960589 1445357 := bbase (se 3 (by rfl) ⟨271004, by rfl⟩ : syracuseStep 1445357 = 542009) (by norm_num)
theorem B1084909 : Blo 960589 1084909 := bbase (se 3 (by rfl) ⟨203420, by rfl⟩ : syracuseStep 1084909 = 406841) (by norm_num)
theorem B1445381 : Blo 960589 1445381 := bbase (se 4 (by rfl) ⟨135504, by rfl⟩ : syracuseStep 1445381 = 271009) (by norm_num)
theorem B1084945 : Blo 960589 1084945 := bbase (se 2 (by rfl) ⟨406854, by rfl⟩ : syracuseStep 1084945 = 813709) (by norm_num)
theorem B1445405 : Blo 960589 1445405 := bbase (se 3 (by rfl) ⟨271013, by rfl⟩ : syracuseStep 1445405 = 542027) (by norm_num)
theorem B2166317 : Blo 960589 2166317 := bbase (se 3 (by rfl) ⟨406184, by rfl⟩ : syracuseStep 2166317 = 812369) (by norm_num)
theorem B1445429 : Blo 960589 1445429 := bbase (se 5 (by rfl) ⟨67754, by rfl⟩ : syracuseStep 1445429 = 135509) (by norm_num)
theorem B1084981 : Blo 960589 1084981 := bbase (se 5 (by rfl) ⟨50858, by rfl⟩ : syracuseStep 1084981 = 101717) (by norm_num)
theorem B1216073 : Blo 960589 1216073 := bbase (se 2 (by rfl) ⟨456027, by rfl⟩ : syracuseStep 1216073 = 912055) (by norm_num)
theorem B1445453 : Blo 960589 1445453 := bbase (se 3 (by rfl) ⟨271022, by rfl⟩ : syracuseStep 1445453 = 542045) (by norm_num)
theorem B1085017 : Blo 960589 1085017 := bbase (se 2 (by rfl) ⟨406881, by rfl⟩ : syracuseStep 1085017 = 813763) (by norm_num)
theorem B1445477 : Blo 960589 1445477 := bbase (se 4 (by rfl) ⟨135513, by rfl⟩ : syracuseStep 1445477 = 271027) (by norm_num)
theorem B2166389 : Blo 960589 2166389 := bbase (se 5 (by rfl) ⟨101549, by rfl⟩ : syracuseStep 2166389 = 203099) (by norm_num)
theorem B1445501 : Blo 960589 1445501 := bbase (se 3 (by rfl) ⟨271031, by rfl⟩ : syracuseStep 1445501 = 542063) (by norm_num)
theorem B1085053 : Blo 960589 1085053 := bbase (se 3 (by rfl) ⟨203447, by rfl⟩ : syracuseStep 1085053 = 406895) (by norm_num)
theorem B1216129 : Blo 960589 1216129 := bbase (se 2 (by rfl) ⟨456048, by rfl⟩ : syracuseStep 1216129 = 912097) (by norm_num)
theorem B1445525 : Blo 960589 1445525 := bbase (se 6 (by rfl) ⟨33879, by rfl⟩ : syracuseStep 1445525 = 67759) (by norm_num)
theorem B1085089 : Blo 960589 1085089 := bbase (se 2 (by rfl) ⟨406908, by rfl⟩ : syracuseStep 1085089 = 813817) (by norm_num)
theorem B1445549 : Blo 960589 1445549 := bbase (se 3 (by rfl) ⟨271040, by rfl⟩ : syracuseStep 1445549 = 542081) (by norm_num)
theorem B2166461 : Blo 960589 2166461 := bbase (se 3 (by rfl) ⟨406211, by rfl⟩ : syracuseStep 2166461 = 812423) (by norm_num)
theorem B1445573 : Blo 960589 1445573 := bbase (se 4 (by rfl) ⟨135522, by rfl⟩ : syracuseStep 1445573 = 271045) (by norm_num)
theorem B1085125 : Blo 960589 1085125 := bbase (se 4 (by rfl) ⟨101730, by rfl⟩ : syracuseStep 1085125 = 203461) (by norm_num)
theorem B3247829 : Blo 960589 3247829 := bbase (se 7 (by rfl) ⟨38060, by rfl⟩ : syracuseStep 3247829 = 76121) (by norm_num)
theorem B1445597 : Blo 960589 1445597 := bbase (se 3 (by rfl) ⟨271049, by rfl⟩ : syracuseStep 1445597 = 542099) (by norm_num)
theorem B1216225 : Blo 960589 1216225 := bbase (se 2 (by rfl) ⟨456084, by rfl⟩ : syracuseStep 1216225 = 912169) (by norm_num)
theorem B1085161 : Blo 960589 1085161 := bbase (se 2 (by rfl) ⟨406935, by rfl⟩ : syracuseStep 1085161 = 813871) (by norm_num)
theorem B1445621 : Blo 960589 1445621 := bbase (se 5 (by rfl) ⟨67763, by rfl⟩ : syracuseStep 1445621 = 135527) (by norm_num)
theorem B2166533 : Blo 960589 2166533 := bbase (se 4 (by rfl) ⟨203112, by rfl⟩ : syracuseStep 2166533 = 406225) (by norm_num)
theorem B1445645 : Blo 960589 1445645 := bbase (se 3 (by rfl) ⟨271058, by rfl⟩ : syracuseStep 1445645 = 542117) (by norm_num)
theorem B1445669 : Blo 960589 1445669 := bbase (se 4 (by rfl) ⟨135531, by rfl⟩ : syracuseStep 1445669 = 271063) (by norm_num)
theorem B1445693 : Blo 960589 1445693 := bbase (se 3 (by rfl) ⟨271067, by rfl⟩ : syracuseStep 1445693 = 542135) (by norm_num)
theorem B2166605 : Blo 960589 2166605 := bbase (se 3 (by rfl) ⟨406238, by rfl⟩ : syracuseStep 2166605 = 812477) (by norm_num)
theorem B1445717 : Blo 960589 1445717 := bbase (se 9 (by rfl) ⟨4235, by rfl⟩ : syracuseStep 1445717 = 8471) (by norm_num)
theorem B1445741 : Blo 960589 1445741 := bbase (se 3 (by rfl) ⟨271076, by rfl⟩ : syracuseStep 1445741 = 542153) (by norm_num)
theorem B1445765 : Blo 960589 1445765 := bbase (se 4 (by rfl) ⟨135540, by rfl⟩ : syracuseStep 1445765 = 271081) (by norm_num)
theorem B1216397 : Blo 960589 1216397 := bbase (se 3 (by rfl) ⟨228074, by rfl⟩ : syracuseStep 1216397 = 456149) (by norm_num)
theorem B2166677 : Blo 960589 2166677 := bbase (se 6 (by rfl) ⟨50781, by rfl⟩ : syracuseStep 2166677 = 101563) (by norm_num)
theorem B1445789 : Blo 960589 1445789 := bbase (se 3 (by rfl) ⟨271085, by rfl⟩ : syracuseStep 1445789 = 542171) (by norm_num)
theorem B1445813 : Blo 960589 1445813 := bbase (se 5 (by rfl) ⟨67772, by rfl⟩ : syracuseStep 1445813 = 135545) (by norm_num)
theorem B1216453 : Blo 960589 1216453 := bbase (se 4 (by rfl) ⟨114042, by rfl⟩ : syracuseStep 1216453 = 228085) (by norm_num)
theorem B1445837 : Blo 960589 1445837 := bbase (se 3 (by rfl) ⟨271094, by rfl⟩ : syracuseStep 1445837 = 542189) (by norm_num)
theorem B2166749 : Blo 960589 2166749 := bbase (se 3 (by rfl) ⟨406265, by rfl⟩ : syracuseStep 2166749 = 812531) (by norm_num)
theorem B1445861 : Blo 960589 1445861 := bbase (se 4 (by rfl) ⟨135549, by rfl⟩ : syracuseStep 1445861 = 271099) (by norm_num)
theorem B1445885 : Blo 960589 1445885 := bbase (se 3 (by rfl) ⟨271103, by rfl⟩ : syracuseStep 1445885 = 542207) (by norm_num)
theorem B1445909 : Blo 960589 1445909 := bbase (se 6 (by rfl) ⟨33888, by rfl⟩ : syracuseStep 1445909 = 67777) (by norm_num)
theorem B1216549 : Blo 960589 1216549 := bbase (se 4 (by rfl) ⟨114051, by rfl⟩ : syracuseStep 1216549 = 228103) (by norm_num)
theorem B2166821 : Blo 960589 2166821 := bbase (se 4 (by rfl) ⟨203139, by rfl⟩ : syracuseStep 2166821 = 406279) (by norm_num)
theorem B1445933 : Blo 960589 1445933 := bbase (se 3 (by rfl) ⟨271112, by rfl⟩ : syracuseStep 1445933 = 542225) (by norm_num)
theorem B1445957 : Blo 960589 1445957 := bbase (se 4 (by rfl) ⟨135558, by rfl⟩ : syracuseStep 1445957 = 271117) (by norm_num)
theorem B1445981 : Blo 960589 1445981 := bbase (se 3 (by rfl) ⟨271121, by rfl⟩ : syracuseStep 1445981 = 542243) (by norm_num)
theorem B3084389 : Blo 960589 3084389 := bbase (se 4 (by rfl) ⟨289161, by rfl⟩ : syracuseStep 3084389 = 578323) (by norm_num)
theorem B2199653 : Blo 960589 2199653 := bbase (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) (by norm_num)
theorem B2166893 : Blo 960589 2166893 := bbase (se 3 (by rfl) ⟨406292, by rfl⟩ : syracuseStep 2166893 = 812585) (by norm_num)
theorem B1446005 : Blo 960589 1446005 := bbase (se 5 (by rfl) ⟨67781, by rfl⟩ : syracuseStep 1446005 = 135563) (by norm_num)
theorem B3248261 : Blo 960589 3248261 := bbase (se 4 (by rfl) ⟨304524, by rfl⟩ : syracuseStep 3248261 = 609049) (by norm_num)
theorem B1446029 : Blo 960589 1446029 := bbase (se 3 (by rfl) ⟨271130, by rfl⟩ : syracuseStep 1446029 = 542261) (by norm_num)
theorem B1544341 : Blo 960589 1544341 := bbase (se 6 (by rfl) ⟨36195, by rfl⟩ : syracuseStep 1544341 = 72391) (by norm_num)
theorem B1446053 : Blo 960589 1446053 := bbase (se 4 (by rfl) ⟨135567, by rfl⟩ : syracuseStep 1446053 = 271135) (by norm_num)
theorem B2166965 : Blo 960589 2166965 := bbase (se 5 (by rfl) ⟨101576, by rfl⟩ : syracuseStep 2166965 = 203153) (by norm_num)
theorem B1446077 : Blo 960589 1446077 := bbase (se 3 (by rfl) ⟨271139, by rfl⟩ : syracuseStep 1446077 = 542279) (by norm_num)
theorem B1216721 : Blo 960589 1216721 := bbase (se 2 (by rfl) ⟨456270, by rfl⟩ : syracuseStep 1216721 = 912541) (by norm_num)
theorem B1446101 : Blo 960589 1446101 := bbase (se 7 (by rfl) ⟨16946, by rfl⟩ : syracuseStep 1446101 = 33893) (by norm_num)
theorem B1446125 : Blo 960589 1446125 := bbase (se 3 (by rfl) ⟨271148, by rfl⟩ : syracuseStep 1446125 = 542297) (by norm_num)
theorem B2167037 : Blo 960589 2167037 := bbase (se 3 (by rfl) ⟨406319, by rfl⟩ : syracuseStep 2167037 = 812639) (by norm_num)
theorem B1446149 : Blo 960589 1446149 := bbase (se 4 (by rfl) ⟨135576, by rfl⟩ : syracuseStep 1446149 = 271153) (by norm_num)
theorem B1216777 : Blo 960589 1216777 := bbase (se 2 (by rfl) ⟨456291, by rfl⟩ : syracuseStep 1216777 = 912583) (by norm_num)
theorem B1446173 : Blo 960589 1446173 := bbase (se 3 (by rfl) ⟨271157, by rfl⟩ : syracuseStep 1446173 = 542315) (by norm_num)
theorem B3084581 : Blo 960589 3084581 := bbase (se 4 (by rfl) ⟨289179, by rfl⟩ : syracuseStep 3084581 = 578359) (by norm_num)
theorem B1446197 : Blo 960589 1446197 := bbase (se 5 (by rfl) ⟨67790, by rfl⟩ : syracuseStep 1446197 = 135581) (by norm_num)
theorem B2167109 : Blo 960589 2167109 := bbase (se 4 (by rfl) ⟨203166, by rfl⟩ : syracuseStep 2167109 = 406333) (by norm_num)
theorem B1446221 : Blo 960589 1446221 := bbase (se 3 (by rfl) ⟨271166, by rfl⟩ : syracuseStep 1446221 = 542333) (by norm_num)
theorem B1446245 : Blo 960589 1446245 := bbase (se 4 (by rfl) ⟨135585, by rfl⟩ : syracuseStep 1446245 = 271171) (by norm_num)
theorem B1216873 : Blo 960589 1216873 := bbase (se 2 (by rfl) ⟨456327, by rfl⟩ : syracuseStep 1216873 = 912655) (by norm_num)
theorem B1446269 : Blo 960589 1446269 := bbase (se 3 (by rfl) ⟨271175, by rfl⟩ : syracuseStep 1446269 = 542351) (by norm_num)
theorem B2167181 : Blo 960589 2167181 := bbase (se 3 (by rfl) ⟨406346, by rfl⟩ : syracuseStep 2167181 = 812693) (by norm_num)
theorem B1446293 : Blo 960589 1446293 := bbase (se 6 (by rfl) ⟨33897, by rfl⟩ : syracuseStep 1446293 = 67795) (by norm_num)
theorem B1446317 : Blo 960589 1446317 := bbase (se 3 (by rfl) ⟨271184, by rfl⟩ : syracuseStep 1446317 = 542369) (by norm_num)
theorem B1446341 : Blo 960589 1446341 := bbase (se 4 (by rfl) ⟨135594, by rfl⟩ : syracuseStep 1446341 = 271189) (by norm_num)
theorem B2167253 : Blo 960589 2167253 := bbase (se 7 (by rfl) ⟨25397, by rfl⟩ : syracuseStep 2167253 = 50795) (by norm_num)
theorem B1446365 : Blo 960589 1446365 := bbase (se 3 (by rfl) ⟨271193, by rfl⟩ : syracuseStep 1446365 = 542387) (by norm_num)
theorem B1446389 : Blo 960589 1446389 := bbase (se 5 (by rfl) ⟨67799, by rfl⟩ : syracuseStep 1446389 = 135599) (by norm_num)
theorem B2200069 : Blo 960589 2200069 := bbase (se 4 (by rfl) ⟨206256, by rfl⟩ : syracuseStep 2200069 = 412513) (by norm_num)
theorem B1446413 : Blo 960589 1446413 := bbase (se 3 (by rfl) ⟨271202, by rfl⟩ : syracuseStep 1446413 = 542405) (by norm_num)
theorem B1217045 : Blo 960589 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B2167325 : Blo 960589 2167325 := bbase (se 3 (by rfl) ⟨406373, by rfl⟩ : syracuseStep 2167325 = 812747) (by norm_num)
theorem B1446437 : Blo 960589 1446437 := bbase (se 4 (by rfl) ⟨135603, by rfl⟩ : syracuseStep 1446437 = 271207) (by norm_num)
theorem B3248693 : Blo 960589 3248693 := bbase (se 5 (by rfl) ⟨152282, by rfl⟩ : syracuseStep 3248693 = 304565) (by norm_num)
theorem B1446461 : Blo 960589 1446461 := bbase (se 3 (by rfl) ⟨271211, by rfl⟩ : syracuseStep 1446461 = 542423) (by norm_num)
theorem B1217101 : Blo 960589 1217101 := bbase (se 3 (by rfl) ⟨228206, by rfl⟩ : syracuseStep 1217101 = 456413) (by norm_num)
theorem B1446485 : Blo 960589 1446485 := bbase (se 8 (by rfl) ⟨8475, by rfl⟩ : syracuseStep 1446485 = 16951) (by norm_num)
theorem B2167397 : Blo 960589 2167397 := bbase (se 4 (by rfl) ⟨203193, by rfl⟩ : syracuseStep 2167397 = 406387) (by norm_num)
theorem B1446509 : Blo 960589 1446509 := bbase (se 3 (by rfl) ⟨271220, by rfl⟩ : syracuseStep 1446509 = 542441) (by norm_num)
theorem B1446533 : Blo 960589 1446533 := bbase (se 4 (by rfl) ⟨135612, by rfl⟩ : syracuseStep 1446533 = 271225) (by norm_num)
theorem B4625045 : Blo 960589 4625045 := bbase (se 6 (by rfl) ⟨108399, by rfl⟩ : syracuseStep 4625045 = 216799) (by norm_num)
theorem B1446557 : Blo 960589 1446557 := bbase (se 3 (by rfl) ⟨271229, by rfl⟩ : syracuseStep 1446557 = 542459) (by norm_num)
theorem B1217197 : Blo 960589 1217197 := bbase (se 3 (by rfl) ⟨228224, by rfl⟩ : syracuseStep 1217197 = 456449) (by norm_num)
theorem B2167469 : Blo 960589 2167469 := bbase (se 3 (by rfl) ⟨406400, by rfl⟩ : syracuseStep 2167469 = 812801) (by norm_num)
theorem B1446581 : Blo 960589 1446581 := bbase (se 5 (by rfl) ⟨67808, by rfl⟩ : syracuseStep 1446581 = 135617) (by norm_num)
theorem B1446605 : Blo 960589 1446605 := bbase (se 3 (by rfl) ⟨271238, by rfl⟩ : syracuseStep 1446605 = 542477) (by norm_num)
theorem B1446629 : Blo 960589 1446629 := bbase (se 4 (by rfl) ⟨135621, by rfl⟩ : syracuseStep 1446629 = 271243) (by norm_num)
theorem B2167541 : Blo 960589 2167541 := bbase (se 5 (by rfl) ⟨101603, by rfl⟩ : syracuseStep 2167541 = 203207) (by norm_num)
theorem B1446653 : Blo 960589 1446653 := bbase (se 3 (by rfl) ⟨271247, by rfl⟩ : syracuseStep 1446653 = 542495) (by norm_num)
theorem B1446677 : Blo 960589 1446677 := bbase (se 6 (by rfl) ⟨33906, by rfl⟩ : syracuseStep 1446677 = 67813) (by norm_num)
theorem B1446701 : Blo 960589 1446701 := bbase (se 3 (by rfl) ⟨271256, by rfl⟩ : syracuseStep 1446701 = 542513) (by norm_num)
theorem B1545013 : Blo 960589 1545013 := bbase (se 5 (by rfl) ⟨72422, by rfl⟩ : syracuseStep 1545013 = 144845) (by norm_num)
theorem B2167613 : Blo 960589 2167613 := bbase (se 3 (by rfl) ⟨406427, by rfl⟩ : syracuseStep 2167613 = 812855) (by norm_num)
theorem B1446725 : Blo 960589 1446725 := bbase (se 4 (by rfl) ⟨135630, by rfl⟩ : syracuseStep 1446725 = 271261) (by norm_num)
theorem B1217369 : Blo 960589 1217369 := bbase (se 2 (by rfl) ⟨456513, by rfl⟩ : syracuseStep 1217369 = 913027) (by norm_num)
theorem B1446749 : Blo 960589 1446749 := bbase (se 3 (by rfl) ⟨271265, by rfl⟩ : syracuseStep 1446749 = 542531) (by norm_num)
theorem B1446773 : Blo 960589 1446773 := bbase (se 5 (by rfl) ⟨67817, by rfl⟩ : syracuseStep 1446773 = 135635) (by norm_num)
theorem B2167685 : Blo 960589 2167685 := bbase (se 4 (by rfl) ⟨203220, by rfl⟩ : syracuseStep 2167685 = 406441) (by norm_num)
theorem B1446797 : Blo 960589 1446797 := bbase (se 3 (by rfl) ⟨271274, by rfl⟩ : syracuseStep 1446797 = 542549) (by norm_num)
theorem B1217425 : Blo 960589 1217425 := bbase (se 2 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 1217425 = 913069) (by norm_num)
theorem B1446821 : Blo 960589 1446821 := bbase (se 4 (by rfl) ⟨135639, by rfl⟩ : syracuseStep 1446821 = 271279) (by norm_num)
theorem B1446845 : Blo 960589 1446845 := bbase (se 3 (by rfl) ⟨271283, by rfl⟩ : syracuseStep 1446845 = 542567) (by norm_num)
theorem B2167757 : Blo 960589 2167757 := bbase (se 3 (by rfl) ⟨406454, by rfl⟩ : syracuseStep 2167757 = 812909) (by norm_num)
theorem B1446869 : Blo 960589 1446869 := bbase (se 7 (by rfl) ⟨16955, by rfl⟩ : syracuseStep 1446869 = 33911) (by norm_num)
theorem B3249125 : Blo 960589 3249125 := bbase (se 4 (by rfl) ⟨304605, by rfl⟩ : syracuseStep 3249125 = 609211) (by norm_num)
theorem B1217521 : Blo 960589 1217521 := bbase (se 2 (by rfl) ⟨456570, by rfl⟩ : syracuseStep 1217521 = 913141) (by norm_num)
theorem B2167829 : Blo 960589 2167829 := bbase (se 6 (by rfl) ⟨50808, by rfl⟩ : syracuseStep 2167829 = 101617) (by norm_num)
theorem B2167901 : Blo 960589 2167901 := bbase (se 3 (by rfl) ⟨406481, by rfl⟩ : syracuseStep 2167901 = 812963) (by norm_num)
theorem B1217693 : Blo 960589 1217693 := bbase (se 3 (by rfl) ⟨228317, by rfl⟩ : syracuseStep 1217693 = 456635) (by norm_num)
theorem B2167973 : Blo 960589 2167973 := bbase (se 4 (by rfl) ⟨203247, by rfl⟩ : syracuseStep 2167973 = 406495) (by norm_num)
theorem B1217749 : Blo 960589 1217749 := bbase (se 7 (by rfl) ⟨14270, by rfl⟩ : syracuseStep 1217749 = 28541) (by norm_num)
theorem B2168045 : Blo 960589 2168045 := bbase (se 3 (by rfl) ⟨406508, by rfl⟩ : syracuseStep 2168045 = 813017) (by norm_num)
theorem B1217845 : Blo 960589 1217845 := bbase (se 5 (by rfl) ⟨57086, by rfl⟩ : syracuseStep 1217845 = 114173) (by norm_num)
theorem B2168117 : Blo 960589 2168117 := bbase (se 5 (by rfl) ⟨101630, by rfl⟩ : syracuseStep 2168117 = 203261) (by norm_num)
theorem B2168189 : Blo 960589 2168189 := bbase (se 3 (by rfl) ⟨406535, by rfl⟩ : syracuseStep 2168189 = 813071) (by norm_num)
theorem B3249557 : Blo 960589 3249557 := bbase (se 6 (by rfl) ⟨76161, by rfl⟩ : syracuseStep 3249557 = 152323) (by norm_num)
theorem B2168261 : Blo 960589 2168261 := bbase (se 4 (by rfl) ⟨203274, by rfl⟩ : syracuseStep 2168261 = 406549) (by norm_num)
theorem B1218017 : Blo 960589 1218017 := bbase (se 2 (by rfl) ⟨456756, by rfl⟩ : syracuseStep 1218017 = 913513) (by norm_num)
theorem B2168333 : Blo 960589 2168333 := bbase (se 3 (by rfl) ⟨406562, by rfl⟩ : syracuseStep 2168333 = 813125) (by norm_num)
theorem B1218073 : Blo 960589 1218073 := bbase (se 2 (by rfl) ⟨456777, by rfl⟩ : syracuseStep 1218073 = 913555) (by norm_num)
theorem B2168405 : Blo 960589 2168405 := bbase (se 8 (by rfl) ⟨12705, by rfl⟩ : syracuseStep 2168405 = 25411) (by norm_num)
theorem B1218169 : Blo 960589 1218169 := bbase (se 2 (by rfl) ⟨456813, by rfl⟩ : syracuseStep 1218169 = 913627) (by norm_num)
theorem B2168477 : Blo 960589 2168477 := bbase (se 3 (by rfl) ⟨406589, by rfl⟩ : syracuseStep 2168477 = 813179) (by norm_num)
theorem B1316525 : Blo 960589 1316525 := bbase (se 3 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 1316525 = 493697) (by norm_num)
theorem B988849 : Blo 960589 988849 := bbase (se 2 (by rfl) ⟨370818, by rfl⟩ : syracuseStep 988849 = 741637) (by norm_num)
theorem B2168549 : Blo 960589 2168549 := bbase (se 4 (by rfl) ⟨203301, by rfl⟩ : syracuseStep 2168549 = 406603) (by norm_num)
theorem B1218341 : Blo 960589 1218341 := bbase (se 4 (by rfl) ⟨114219, by rfl⟩ : syracuseStep 1218341 = 228439) (by norm_num)
theorem B2168621 : Blo 960589 2168621 := bbase (se 3 (by rfl) ⟨406616, by rfl⟩ : syracuseStep 2168621 = 813233) (by norm_num)
theorem B3249989 : Blo 960589 3249989 := bbase (se 4 (by rfl) ⟨304686, by rfl⟩ : syracuseStep 3249989 = 609373) (by norm_num)
theorem B1218397 : Blo 960589 1218397 := bbase (se 3 (by rfl) ⟨228449, by rfl⟩ : syracuseStep 1218397 = 456899) (by norm_num)
theorem B2168693 : Blo 960589 2168693 := bbase (se 5 (by rfl) ⟨101657, by rfl⟩ : syracuseStep 2168693 = 203315) (by norm_num)
theorem B1218493 : Blo 960589 1218493 := bbase (se 3 (by rfl) ⟨228467, by rfl⟩ : syracuseStep 1218493 = 456935) (by norm_num)
theorem B2168765 : Blo 960589 2168765 := bbase (se 3 (by rfl) ⟨406643, by rfl⟩ : syracuseStep 2168765 = 813287) (by norm_num)
theorem B2168837 : Blo 960589 2168837 := bbase (se 4 (by rfl) ⟨203328, by rfl⟩ : syracuseStep 2168837 = 406657) (by norm_num)
theorem B2168909 : Blo 960589 2168909 := bbase (se 3 (by rfl) ⟨406670, by rfl⟩ : syracuseStep 2168909 = 813341) (by norm_num)
theorem B1218665 : Blo 960589 1218665 := bbase (se 2 (by rfl) ⟨456999, by rfl⟩ : syracuseStep 1218665 = 913999) (by norm_num)
theorem B2168981 : Blo 960589 2168981 := bbase (se 6 (by rfl) ⟨50835, by rfl⟩ : syracuseStep 2168981 = 101671) (by norm_num)
theorem B1218721 : Blo 960589 1218721 := bbase (se 2 (by rfl) ⟨457020, by rfl⟩ : syracuseStep 1218721 = 914041) (by norm_num)
theorem B2169053 : Blo 960589 2169053 := bbase (se 3 (by rfl) ⟨406697, by rfl⟩ : syracuseStep 2169053 = 813395) (by norm_num)
theorem B3250421 : Blo 960589 3250421 := bbase (se 5 (by rfl) ⟨152363, by rfl⟩ : syracuseStep 3250421 = 304727) (by norm_num)
theorem B1218817 : Blo 960589 1218817 := bbase (se 2 (by rfl) ⟨457056, by rfl⟩ : syracuseStep 1218817 = 914113) (by norm_num)
theorem B2169125 : Blo 960589 2169125 := bbase (se 4 (by rfl) ⟨203355, by rfl⟩ : syracuseStep 2169125 = 406711) (by norm_num)
theorem B2169197 : Blo 960589 2169197 := bbase (se 3 (by rfl) ⟨406724, by rfl⟩ : syracuseStep 2169197 = 813449) (by norm_num)
theorem B7313813 : Blo 960589 7313813 := bbase (se 6 (by rfl) ⟨171417, by rfl⟩ : syracuseStep 7313813 = 342835) (by norm_num)
theorem B1218989 : Blo 960589 1218989 := bbase (se 3 (by rfl) ⟨228560, by rfl⟩ : syracuseStep 1218989 = 457121) (by norm_num)
theorem B2169269 : Blo 960589 2169269 := bbase (se 5 (by rfl) ⟨101684, by rfl⟩ : syracuseStep 2169269 = 203369) (by norm_num)
theorem B1219045 : Blo 960589 1219045 := bbase (se 4 (by rfl) ⟨114285, by rfl⟩ : syracuseStep 1219045 = 228571) (by norm_num)
theorem B2169341 : Blo 960589 2169341 := bbase (se 3 (by rfl) ⟨406751, by rfl⟩ : syracuseStep 2169341 = 813503) (by norm_num)
theorem B1219141 : Blo 960589 1219141 := bbase (se 4 (by rfl) ⟨114294, by rfl⟩ : syracuseStep 1219141 = 228589) (by norm_num)
theorem B2169413 : Blo 960589 2169413 := bbase (se 4 (by rfl) ⟨203382, by rfl⟩ : syracuseStep 2169413 = 406765) (by norm_num)
theorem B2169485 : Blo 960589 2169485 := bbase (se 3 (by rfl) ⟨406778, by rfl⟩ : syracuseStep 2169485 = 813557) (by norm_num)
theorem B3250853 : Blo 960589 3250853 := bbase (se 4 (by rfl) ⟨304767, by rfl⟩ : syracuseStep 3250853 = 609535) (by norm_num)
theorem B989869 : Blo 960589 989869 := bbase (se 3 (by rfl) ⟨185600, by rfl⟩ : syracuseStep 989869 = 371201) (by norm_num)
theorem B2169557 : Blo 960589 2169557 := bbase (se 7 (by rfl) ⟨25424, by rfl⟩ : syracuseStep 2169557 = 50849) (by norm_num)
theorem B1219313 : Blo 960589 1219313 := bbase (se 2 (by rfl) ⟨457242, by rfl⟩ : syracuseStep 1219313 = 914485) (by norm_num)
theorem B2431741 : Blo 960589 2431741 := bbase (se 3 (by rfl) ⟨455951, by rfl⟩ : syracuseStep 2431741 = 911903) (by norm_num)
theorem B2923285 : Blo 960589 2923285 := bbase (se 6 (by rfl) ⟨68514, by rfl⟩ : syracuseStep 2923285 = 137029) (by norm_num)
theorem B2169629 : Blo 960589 2169629 := bbase (se 3 (by rfl) ⟨406805, by rfl⟩ : syracuseStep 2169629 = 813611) (by norm_num)
theorem B1219369 : Blo 960589 1219369 := bbase (se 2 (by rfl) ⟨457263, by rfl⟩ : syracuseStep 1219369 = 914527) (by norm_num)
theorem B2169701 : Blo 960589 2169701 := bbase (se 4 (by rfl) ⟨203409, by rfl⟩ : syracuseStep 2169701 = 406819) (by norm_num)
theorem B2431853 : Blo 960589 2431853 := bbase (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) (by norm_num)
theorem B2923381 : Blo 960589 2923381 := bbase (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) (by norm_num)
theorem B1219465 : Blo 960589 1219465 := bbase (se 2 (by rfl) ⟨457299, by rfl⟩ : syracuseStep 1219465 = 914599) (by norm_num)
theorem B2169773 : Blo 960589 2169773 := bbase (se 3 (by rfl) ⟨406832, by rfl⟩ : syracuseStep 2169773 = 813665) (by norm_num)
theorem B8231861 : Blo 960589 8231861 := bbase (se 5 (by rfl) ⟨385868, by rfl⟩ : syracuseStep 8231861 = 771737) (by norm_num)
theorem B2169845 : Blo 960589 2169845 := bbase (se 5 (by rfl) ⟨101711, by rfl⟩ : syracuseStep 2169845 = 203423) (by norm_num)
theorem B2432045 : Blo 960589 2432045 := bbase (se 3 (by rfl) ⟨456008, by rfl⟩ : syracuseStep 2432045 = 912017) (by norm_num)
theorem B1219637 : Blo 960589 1219637 := bbase (se 5 (by rfl) ⟨57170, by rfl⟩ : syracuseStep 1219637 = 114341) (by norm_num)
theorem B2169917 : Blo 960589 2169917 := bbase (se 3 (by rfl) ⟨406859, by rfl⟩ : syracuseStep 2169917 = 813719) (by norm_num)
theorem B3251285 : Blo 960589 3251285 := bbase (se 8 (by rfl) ⟨19050, by rfl⟩ : syracuseStep 3251285 = 38101) (by norm_num)
theorem B1219693 : Blo 960589 1219693 := bbase (se 3 (by rfl) ⟨228692, by rfl⟩ : syracuseStep 1219693 = 457385) (by norm_num)
theorem B2464901 : Blo 960589 2464901 := bbase (se 4 (by rfl) ⟨231084, by rfl⟩ : syracuseStep 2464901 = 462169) (by norm_num)
theorem B2169989 : Blo 960589 2169989 := bbase (se 4 (by rfl) ⟨203436, by rfl⟩ : syracuseStep 2169989 = 406873) (by norm_num)
theorem B1219789 : Blo 960589 1219789 := bbase (se 3 (by rfl) ⟨228710, by rfl⟩ : syracuseStep 1219789 = 457421) (by norm_num)
theorem B2170061 : Blo 960589 2170061 := bbase (se 3 (by rfl) ⟨406886, by rfl⟩ : syracuseStep 2170061 = 813773) (by norm_num)
theorem B2170133 : Blo 960589 2170133 := bbase (se 6 (by rfl) ⟨50862, by rfl⟩ : syracuseStep 2170133 = 101725) (by norm_num)
theorem B7806293 : Blo 960589 7806293 := bbase (se 11 (by rfl) ⟨5717, by rfl⟩ : syracuseStep 7806293 = 11435) (by norm_num)
theorem B2170205 : Blo 960589 2170205 := bbase (se 3 (by rfl) ⟨406913, by rfl⟩ : syracuseStep 2170205 = 813827) (by norm_num)
theorem B4627813 : Blo 960589 4627813 := bbase (se 4 (by rfl) ⟨433857, by rfl⟩ : syracuseStep 4627813 = 867715) (by norm_num)
theorem B1219961 : Blo 960589 1219961 := bbase (se 2 (by rfl) ⟨457485, by rfl⟩ : syracuseStep 1219961 = 914971) (by norm_num)
theorem B2432389 : Blo 960589 2432389 := bbase (se 4 (by rfl) ⟨228036, by rfl⟩ : syracuseStep 2432389 = 456073) (by norm_num)
theorem B2170277 : Blo 960589 2170277 := bbase (se 4 (by rfl) ⟨203463, by rfl⟩ : syracuseStep 2170277 = 406927) (by norm_num)
theorem B1220017 : Blo 960589 1220017 := bbase (se 2 (by rfl) ⟨457506, by rfl⟩ : syracuseStep 1220017 = 915013) (by norm_num)
theorem B2432501 : Blo 960589 2432501 := bbase (se 5 (by rfl) ⟨114023, by rfl⟩ : syracuseStep 2432501 = 228047) (by norm_num)
theorem B3251717 : Blo 960589 3251717 := bbase (se 4 (by rfl) ⟨304848, by rfl⟩ : syracuseStep 3251717 = 609697) (by norm_num)
theorem B1220113 : Blo 960589 1220113 := bbase (se 2 (by rfl) ⟨457542, by rfl⟩ : syracuseStep 1220113 = 915085) (by norm_num)
theorem B2432693 : Blo 960589 2432693 := bbase (se 5 (by rfl) ⟨114032, by rfl⟩ : syracuseStep 2432693 = 228065) (by norm_num)
theorem B1220285 : Blo 960589 1220285 := bbase (se 3 (by rfl) ⟨228803, by rfl⟩ : syracuseStep 1220285 = 457607) (by norm_num)
theorem B1220341 : Blo 960589 1220341 := bbase (se 5 (by rfl) ⟨57203, by rfl⟩ : syracuseStep 1220341 = 114407) (by norm_num)
theorem B1646333 : Blo 960589 1646333 := bbase (se 3 (by rfl) ⟨308687, by rfl⟩ : syracuseStep 1646333 = 617375) (by norm_num)
theorem B3088181 : Blo 960589 3088181 := bbase (se 5 (by rfl) ⟨144758, by rfl⟩ : syracuseStep 3088181 = 289517) (by norm_num)
theorem B1220437 : Blo 960589 1220437 := bbase (se 9 (by rfl) ⟨3575, by rfl⟩ : syracuseStep 1220437 = 7151) (by norm_num)
theorem B3252149 : Blo 960589 3252149 := bbase (se 5 (by rfl) ⟨152444, by rfl⟩ : syracuseStep 3252149 = 304889) (by norm_num)
theorem B1220609 : Blo 960589 1220609 := bbase (se 2 (by rfl) ⟨457728, by rfl⟩ : syracuseStep 1220609 = 915457) (by norm_num)
theorem B2433037 : Blo 960589 2433037 := bbase (se 3 (by rfl) ⟨456194, by rfl⟩ : syracuseStep 2433037 = 912389) (by norm_num)
theorem B1220665 : Blo 960589 1220665 := bbase (se 2 (by rfl) ⟨457749, by rfl⟩ : syracuseStep 1220665 = 915499) (by norm_num)
theorem B1876061 : Blo 960589 1876061 := bbase (se 3 (by rfl) ⟨351761, by rfl⟩ : syracuseStep 1876061 = 703523) (by norm_num)
theorem B2433149 : Blo 960589 2433149 := bbase (se 3 (by rfl) ⟨456215, by rfl⟩ : syracuseStep 2433149 = 912431) (by norm_num)
theorem B1220761 : Blo 960589 1220761 := bbase (se 2 (by rfl) ⟨457785, by rfl⟩ : syracuseStep 1220761 = 915571) (by norm_num)
theorem B1155281 : Blo 960589 1155281 := bbase (se 2 (by rfl) ⟨433230, by rfl⟩ : syracuseStep 1155281 = 866461) (by norm_num)
theorem B1155377 : Blo 960589 1155377 := bbase (se 2 (by rfl) ⟨433266, by rfl⟩ : syracuseStep 1155377 = 866533) (by norm_num)
theorem B2433341 : Blo 960589 2433341 := bbase (se 3 (by rfl) ⟨456251, by rfl⟩ : syracuseStep 2433341 = 912503) (by norm_num)
theorem B1155397 : Blo 960589 1155397 := bbase (se 4 (by rfl) ⟨108318, by rfl⟩ : syracuseStep 1155397 = 216637) (by norm_num)
theorem B3252581 : Blo 960589 3252581 := bbase (se 4 (by rfl) ⟨304929, by rfl⟩ : syracuseStep 3252581 = 609859) (by norm_num)
theorem B1483157 : Blo 960589 1483157 := bbase (se 6 (by rfl) ⟨34761, by rfl⟩ : syracuseStep 1483157 = 69523) (by norm_num)
theorem B2597285 : Blo 960589 2597285 := bbase (se 4 (by rfl) ⟨243495, by rfl⟩ : syracuseStep 2597285 = 486991) (by norm_num)
theorem B1647029 : Blo 960589 1647029 := bbase (se 5 (by rfl) ⟨77204, by rfl⟩ : syracuseStep 1647029 = 154409) (by norm_num)
theorem B1155541 : Blo 960589 1155541 := bbase (se 7 (by rfl) ⟨13541, by rfl⟩ : syracuseStep 1155541 = 27083) (by norm_num)
theorem B2433685 : Blo 960589 2433685 := bbase (se 6 (by rfl) ⟨57039, by rfl⟩ : syracuseStep 2433685 = 114079) (by norm_num)
theorem B1057429 : Blo 960589 1057429 := bbase (se 6 (by rfl) ⟨24783, by rfl⟩ : syracuseStep 1057429 = 49567) (by norm_num)
theorem B2433797 : Blo 960589 2433797 := bbase (se 4 (by rfl) ⟨228168, by rfl⟩ : syracuseStep 2433797 = 456337) (by norm_num)
theorem B3253013 : Blo 960589 3253013 := bbase (se 6 (by rfl) ⟨76242, by rfl⟩ : syracuseStep 3253013 = 152485) (by norm_num)
theorem B8790869 : Blo 960589 8790869 := bbase (se 9 (by rfl) ⟨25754, by rfl⟩ : syracuseStep 8790869 = 51509) (by norm_num)
theorem B2433989 : Blo 960589 2433989 := bbase (se 4 (by rfl) ⟨228186, by rfl⟩ : syracuseStep 2433989 = 456373) (by norm_num)
theorem B4105205 : Blo 960589 4105205 := bbase (se 5 (by rfl) ⟨192431, by rfl⟩ : syracuseStep 4105205 = 384863) (by norm_num)
theorem B3253445 : Blo 960589 3253445 := bbase (se 4 (by rfl) ⟨305010, by rfl⟩ : syracuseStep 3253445 = 610021) (by norm_num)
theorem B2434333 : Blo 960589 2434333 := bbase (se 3 (by rfl) ⟨456437, by rfl⟩ : syracuseStep 2434333 = 912875) (by norm_num)
theorem B2434445 : Blo 960589 2434445 := bbase (se 3 (by rfl) ⟨456458, by rfl⟩ : syracuseStep 2434445 = 912917) (by norm_num)
theorem B2860469 : Blo 960589 2860469 := bbase (se 5 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 2860469 = 268169) (by norm_num)
theorem B1648181 : Blo 960589 1648181 := bbase (se 5 (by rfl) ⟨77258, by rfl⟩ : syracuseStep 1648181 = 154517) (by norm_num)
theorem B2434637 : Blo 960589 2434637 := bbase (se 3 (by rfl) ⟨456494, by rfl⟩ : syracuseStep 2434637 = 912989) (by norm_num)
theorem B3253877 : Blo 960589 3253877 := bbase (se 5 (by rfl) ⟨152525, by rfl⟩ : syracuseStep 3253877 = 305051) (by norm_num)
theorem B1648453 : Blo 960589 1648453 := bbase (se 4 (by rfl) ⟨154542, by rfl⟩ : syracuseStep 1648453 = 309085) (by norm_num)
theorem B6596437 : Blo 960589 6596437 := bbase (se 9 (by rfl) ⟨19325, by rfl⟩ : syracuseStep 6596437 = 38651) (by norm_num)
theorem B2434981 : Blo 960589 2434981 := bbase (se 4 (by rfl) ⟨228279, by rfl⟩ : syracuseStep 2434981 = 456559) (by norm_num)
theorem B2435093 : Blo 960589 2435093 := bbase (se 6 (by rfl) ⟨57072, by rfl⟩ : syracuseStep 2435093 = 114145) (by norm_num)
theorem B3254309 : Blo 960589 3254309 := bbase (se 4 (by rfl) ⟨305091, by rfl⟩ : syracuseStep 3254309 = 610183) (by norm_num)
theorem B1026113 : Blo 960589 1026113 := bbase (se 2 (by rfl) ⟨384792, by rfl⟩ : syracuseStep 1026113 = 769585) (by norm_num)
theorem B2435285 : Blo 960589 2435285 := bbase (se 7 (by rfl) ⟨28538, by rfl⟩ : syracuseStep 2435285 = 57077) (by norm_num)
theorem B1157333 : Blo 960589 1157333 := bbase (se 7 (by rfl) ⟨13562, by rfl⟩ : syracuseStep 1157333 = 27125) (by norm_num)
theorem B3909941 : Blo 960589 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B1026361 : Blo 960589 1026361 := bbase (se 2 (by rfl) ⟨384885, by rfl⟩ : syracuseStep 1026361 = 769771) (by norm_num)
theorem B3254741 : Blo 960589 3254741 := bbase (se 7 (by rfl) ⟨38141, by rfl⟩ : syracuseStep 3254741 = 76283) (by norm_num)
theorem B1649165 : Blo 960589 1649165 := bbase (se 3 (by rfl) ⟨309218, by rfl⟩ : syracuseStep 1649165 = 618437) (by norm_num)
theorem B1157665 : Blo 960589 1157665 := bbase (se 2 (by rfl) ⟨434124, by rfl⟩ : syracuseStep 1157665 = 868249) (by norm_num)
theorem B3648037 : Blo 960589 3648037 := bbase (se 4 (by rfl) ⟨342003, by rfl⟩ : syracuseStep 3648037 = 684007) (by norm_num)
theorem B1878565 : Blo 960589 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B2435629 : Blo 960589 2435629 := bbase (se 3 (by rfl) ⟨456680, by rfl⟩ : syracuseStep 2435629 = 913361) (by norm_num)
theorem B2435741 : Blo 960589 2435741 := bbase (se 3 (by rfl) ⟨456701, by rfl⟩ : syracuseStep 2435741 = 913403) (by norm_num)
theorem B1157809 : Blo 960589 1157809 := bbase (se 2 (by rfl) ⟨434178, by rfl⟩ : syracuseStep 1157809 = 868357) (by norm_num)
theorem B1026793 : Blo 960589 1026793 := bbase (se 2 (by rfl) ⟨385047, by rfl⟩ : syracuseStep 1026793 = 770095) (by norm_num)
theorem B1026865 : Blo 960589 1026865 := bbase (se 2 (by rfl) ⟨385074, by rfl⟩ : syracuseStep 1026865 = 770149) (by norm_num)
theorem B3648341 : Blo 960589 3648341 := bbase (se 9 (by rfl) ⟨10688, by rfl⟩ : syracuseStep 3648341 = 21377) (by norm_num)
theorem B2435933 : Blo 960589 2435933 := bbase (se 3 (by rfl) ⟨456737, by rfl⟩ : syracuseStep 2435933 = 913475) (by norm_num)
theorem B3255173 : Blo 960589 3255173 := bbase (se 4 (by rfl) ⟨305172, by rfl⟩ : syracuseStep 3255173 = 610345) (by norm_num)
theorem B1027237 : Blo 960589 1027237 := bbase (se 4 (by rfl) ⟨96303, by rfl⟩ : syracuseStep 1027237 = 192607) (by norm_num)
theorem B2436277 : Blo 960589 2436277 := bbase (se 5 (by rfl) ⟨114200, by rfl⟩ : syracuseStep 2436277 = 228401) (by norm_num)
theorem B2436389 : Blo 960589 2436389 := bbase (se 4 (by rfl) ⟨228411, by rfl⟩ : syracuseStep 2436389 = 456823) (by norm_num)
theorem B3910949 : Blo 960589 3910949 := bbase (se 4 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 3910949 = 733303) (by norm_num)
theorem B4632005 : Blo 960589 4632005 := bbase (se 4 (by rfl) ⟨434250, by rfl⟩ : syracuseStep 4632005 = 868501) (by norm_num)
theorem B2436581 : Blo 960589 2436581 := bbase (se 4 (by rfl) ⟨228429, by rfl⟩ : syracuseStep 2436581 = 456859) (by norm_num)
theorem B1027613 : Blo 960589 1027613 := bbase (se 3 (by rfl) ⟨192677, by rfl⟩ : syracuseStep 1027613 = 385355) (by norm_num)
theorem B1027685 : Blo 960589 1027685 := bbase (se 4 (by rfl) ⟨96345, by rfl⟩ : syracuseStep 1027685 = 192691) (by norm_num)
theorem B1388261 : Blo 960589 1388261 := bbase (se 4 (by rfl) ⟨130149, by rfl⟩ : syracuseStep 1388261 = 260299) (by norm_num)
theorem B9252629 : Blo 960589 9252629 := bbase (se 6 (by rfl) ⟨216858, by rfl⟩ : syracuseStep 9252629 = 433717) (by norm_num)
theorem B1027873 : Blo 960589 1027873 := bbase (se 2 (by rfl) ⟨385452, by rfl⟩ : syracuseStep 1027873 = 770905) (by norm_num)
theorem B2436925 : Blo 960589 2436925 := bbase (se 3 (by rfl) ⟨456923, by rfl⟩ : syracuseStep 2436925 = 913847) (by norm_num)
theorem B2437037 : Blo 960589 2437037 := bbase (se 3 (by rfl) ⟨456944, by rfl⟩ : syracuseStep 2437037 = 913889) (by norm_num)
theorem B1028057 : Blo 960589 1028057 := bbase (se 2 (by rfl) ⟨385521, by rfl⟩ : syracuseStep 1028057 = 771043) (by norm_num)
theorem B2437229 : Blo 960589 2437229 := bbase (se 3 (by rfl) ⟨456980, by rfl⟩ : syracuseStep 2437229 = 913961) (by norm_num)
theorem B2470133 : Blo 960589 2470133 := bbase (se 5 (by rfl) ⟨115787, by rfl⟩ : syracuseStep 2470133 = 231575) (by norm_num)
theorem B6598901 : Blo 960589 6598901 := bbase (se 5 (by rfl) ⟨309323, by rfl⟩ : syracuseStep 6598901 = 618647) (by norm_num)
theorem B2928917 : Blo 960589 2928917 := bbase (se 6 (by rfl) ⟨68646, by rfl⟩ : syracuseStep 2928917 = 137293) (by norm_num)
theorem B2437573 : Blo 960589 2437573 := bbase (se 4 (by rfl) ⟨228522, by rfl⟩ : syracuseStep 2437573 = 457045) (by norm_num)
theorem B2437685 : Blo 960589 2437685 := bbase (se 5 (by rfl) ⟨114266, by rfl⟩ : syracuseStep 2437685 = 228533) (by norm_num)
theorem B1028809 : Blo 960589 1028809 := bbase (se 2 (by rfl) ⟨385803, by rfl⟩ : syracuseStep 1028809 = 771607) (by norm_num)
theorem B2437877 : Blo 960589 2437877 := bbase (se 5 (by rfl) ⟨114275, by rfl⟩ : syracuseStep 2437877 = 228551) (by norm_num)
theorem B1028881 : Blo 960589 1028881 := bbase (se 2 (by rfl) ⟨385830, by rfl⟩ : syracuseStep 1028881 = 771661) (by norm_num)
theorem B3650453 : Blo 960589 3650453 := bbase (se 6 (by rfl) ⟨85557, by rfl⟩ : syracuseStep 3650453 = 171115) (by norm_num)
theorem B4109237 : Blo 960589 4109237 := bbase (se 5 (by rfl) ⟨192620, by rfl⟩ : syracuseStep 4109237 = 385241) (by norm_num)
theorem B1029061 : Blo 960589 1029061 := bbase (se 4 (by rfl) ⟨96474, by rfl⟩ : syracuseStep 1029061 = 192949) (by norm_num)
theorem B5485589 : Blo 960589 5485589 := bbase (se 6 (by rfl) ⟨128568, by rfl⟩ : syracuseStep 5485589 = 257137) (by norm_num)
theorem B2438221 : Blo 960589 2438221 := bbase (se 3 (by rfl) ⟨457166, by rfl⟩ : syracuseStep 2438221 = 914333) (by norm_num)
theorem B8008789 : Blo 960589 8008789 := bbase (se 8 (by rfl) ⟨46926, by rfl⟩ : syracuseStep 8008789 = 93853) (by norm_num)
theorem B4863077 : Blo 960589 4863077 := bbase (se 4 (by rfl) ⟨455913, by rfl⟩ : syracuseStep 4863077 = 911827) (by norm_num)
theorem B3650741 : Blo 960589 3650741 := bbase (se 5 (by rfl) ⟨171128, by rfl⟩ : syracuseStep 3650741 = 342257) (by norm_num)
theorem B2438333 : Blo 960589 2438333 := bbase (se 3 (by rfl) ⟨457187, by rfl⟩ : syracuseStep 2438333 = 914375) (by norm_num)
theorem B8238293 : Blo 960589 8238293 := bbase (se 7 (by rfl) ⟨96542, by rfl⟩ : syracuseStep 8238293 = 193085) (by norm_num)
theorem B2438525 : Blo 960589 2438525 := bbase (se 3 (by rfl) ⟨457223, by rfl⟩ : syracuseStep 2438525 = 914447) (by norm_num)
theorem B1029505 : Blo 960589 1029505 := bbase (se 2 (by rfl) ⟨386064, by rfl⟩ : syracuseStep 1029505 = 772129) (by norm_num)
theorem B1029629 : Blo 960589 1029629 := bbase (se 3 (by rfl) ⟨193055, by rfl⟩ : syracuseStep 1029629 = 386111) (by norm_num)
theorem B1848845 : Blo 960589 1848845 := bbase (se 3 (by rfl) ⟨346658, by rfl⟩ : syracuseStep 1848845 = 693317) (by norm_num)
theorem B1390189 : Blo 960589 1390189 := bbase (se 3 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 1390189 = 521321) (by norm_num)
theorem B2438869 : Blo 960589 2438869 := bbase (se 7 (by rfl) ⟨28580, by rfl⟩ : syracuseStep 2438869 = 57161) (by norm_num)
theorem B1029881 : Blo 960589 1029881 := bbase (se 2 (by rfl) ⟨386205, by rfl⟩ : syracuseStep 1029881 = 772411) (by norm_num)
theorem B1947421 : Blo 960589 1947421 := bbase (se 3 (by rfl) ⟨365141, by rfl⟩ : syracuseStep 1947421 = 730283) (by norm_num)
theorem B1947461 : Blo 960589 1947461 := bbase (se 4 (by rfl) ⟨182574, by rfl⟩ : syracuseStep 1947461 = 365149) (by norm_num)
theorem B2438981 : Blo 960589 2438981 := bbase (se 4 (by rfl) ⟨228654, by rfl⟩ : syracuseStep 2438981 = 457309) (by norm_num)
theorem B1947493 : Blo 960589 1947493 := bbase (se 4 (by rfl) ⟨182577, by rfl⟩ : syracuseStep 1947493 = 365155) (by norm_num)
theorem B7321589 : Blo 960589 7321589 := bbase (se 5 (by rfl) ⟨343199, by rfl⟩ : syracuseStep 7321589 = 686399) (by norm_num)
theorem B2439173 : Blo 960589 2439173 := bbase (se 4 (by rfl) ⟨228672, by rfl⟩ : syracuseStep 2439173 = 457345) (by norm_num)
theorem B2340949 : Blo 960589 2340949 := bbase (se 8 (by rfl) ⟨13716, by rfl⟩ : syracuseStep 2340949 = 27433) (by norm_num)
theorem B1095877 : Blo 960589 1095877 := bbase (se 4 (by rfl) ⟨102738, by rfl⟩ : syracuseStep 1095877 = 205477) (by norm_num)
theorem B2308333 : Blo 960589 2308333 := bbase (se 3 (by rfl) ⟨432812, by rfl⟩ : syracuseStep 2308333 = 865625) (by norm_num)
theorem B1849645 : Blo 960589 1849645 := bbase (se 3 (by rfl) ⟨346808, by rfl⟩ : syracuseStep 1849645 = 693617) (by norm_num)
theorem B3651925 : Blo 960589 3651925 := bbase (se 10 (by rfl) ⟨5349, by rfl⟩ : syracuseStep 3651925 = 10699) (by norm_num)
theorem B2439517 : Blo 960589 2439517 := bbase (se 3 (by rfl) ⟨457409, by rfl⟩ : syracuseStep 2439517 = 914819) (by norm_num)
theorem B1096049 : Blo 960589 1096049 := bbase (se 2 (by rfl) ⟨411018, by rfl⟩ : syracuseStep 1096049 = 822037) (by norm_num)
theorem B4864373 : Blo 960589 4864373 := bbase (se 5 (by rfl) ⟨228017, by rfl⟩ : syracuseStep 4864373 = 456035) (by norm_num)
theorem B1096141 : Blo 960589 1096141 := bbase (se 3 (by rfl) ⟨205526, by rfl⟩ : syracuseStep 1096141 = 411053) (by norm_num)
theorem B2439629 : Blo 960589 2439629 := bbase (se 3 (by rfl) ⟨457430, by rfl⟩ : syracuseStep 2439629 = 914861) (by norm_num)
theorem B1096177 : Blo 960589 1096177 := bbase (se 2 (by rfl) ⟨411066, by rfl⟩ : syracuseStep 1096177 = 822133) (by norm_num)
theorem B3652229 : Blo 960589 3652229 := bbase (se 4 (by rfl) ⟨342396, by rfl⟩ : syracuseStep 3652229 = 684793) (by norm_num)
theorem B2439821 : Blo 960589 2439821 := bbase (se 3 (by rfl) ⟨457466, by rfl⟩ : syracuseStep 2439821 = 914933) (by norm_num)
theorem B4111013 : Blo 960589 4111013 := bbase (se 4 (by rfl) ⟨385407, by rfl⟩ : syracuseStep 4111013 = 770815) (by norm_num)
theorem B1784533 : Blo 960589 1784533 := bbase (se 7 (by rfl) ⟨20912, by rfl⟩ : syracuseStep 1784533 = 41825) (by norm_num)
theorem B6175541 : Blo 960589 6175541 := bbase (se 5 (by rfl) ⟨289478, by rfl⟩ : syracuseStep 6175541 = 578957) (by norm_num)
theorem B2308949 : Blo 960589 2308949 := bbase (se 9 (by rfl) ⟨6764, by rfl⟩ : syracuseStep 2308949 = 13529) (by norm_num)
theorem B1850293 : Blo 960589 1850293 := bbase (se 5 (by rfl) ⟨86732, by rfl⟩ : syracuseStep 1850293 = 173465) (by norm_num)
theorem B2931653 : Blo 960589 2931653 := bbase (se 4 (by rfl) ⟨274842, by rfl⟩ : syracuseStep 2931653 = 549685) (by norm_num)
theorem B2440165 : Blo 960589 2440165 := bbase (se 4 (by rfl) ⟨228765, by rfl⟩ : syracuseStep 2440165 = 457531) (by norm_num)
theorem B2440277 : Blo 960589 2440277 := bbase (se 8 (by rfl) ⟨14298, by rfl⟩ : syracuseStep 2440277 = 28597) (by norm_num)
theorem B1621093 : Blo 960589 1621093 := bbase (se 4 (by rfl) ⟨151977, by rfl⟩ : syracuseStep 1621093 = 303955) (by norm_num)
theorem B2309285 : Blo 960589 2309285 := bbase (se 4 (by rfl) ⟨216495, by rfl⟩ : syracuseStep 2309285 = 432991) (by norm_num)
theorem B1621181 : Blo 960589 1621181 := bbase (se 3 (by rfl) ⟨303971, by rfl⟩ : syracuseStep 1621181 = 607943) (by norm_num)
theorem B2342125 : Blo 960589 2342125 := bbase (se 3 (by rfl) ⟨439148, by rfl⟩ : syracuseStep 2342125 = 878297) (by norm_num)
theorem B2440469 : Blo 960589 2440469 := bbase (se 6 (by rfl) ⟨57198, by rfl⟩ : syracuseStep 2440469 = 114397) (by norm_num)
theorem B1621309 : Blo 960589 1621309 := bbase (se 3 (by rfl) ⟨303995, by rfl⟩ : syracuseStep 1621309 = 607991) (by norm_num)
theorem B1621397 : Blo 960589 1621397 := bbase (se 6 (by rfl) ⟨38001, by rfl⟩ : syracuseStep 1621397 = 76003) (by norm_num)
theorem B1621525 : Blo 960589 1621525 := bbase (se 6 (by rfl) ⟨38004, by rfl⟩ : syracuseStep 1621525 = 76009) (by norm_num)
theorem B2735653 : Blo 960589 2735653 := bbase (se 4 (by rfl) ⟨256467, by rfl⟩ : syracuseStep 2735653 = 512935) (by norm_num)
theorem B2309677 : Blo 960589 2309677 := bbase (se 3 (by rfl) ⟨433064, by rfl⟩ : syracuseStep 2309677 = 866129) (by norm_num)
theorem B1621613 : Blo 960589 1621613 := bbase (se 3 (by rfl) ⟨304052, by rfl⟩ : syracuseStep 1621613 = 608105) (by norm_num)
theorem B2440813 : Blo 960589 2440813 := bbase (se 3 (by rfl) ⟨457652, by rfl⟩ : syracuseStep 2440813 = 915305) (by norm_num)
theorem B1949309 : Blo 960589 1949309 := bbase (se 3 (by rfl) ⟨365495, by rfl⟩ : syracuseStep 1949309 = 730991) (by norm_num)
theorem B4865669 : Blo 960589 4865669 := bbase (se 4 (by rfl) ⟨456156, by rfl⟩ : syracuseStep 4865669 = 912313) (by norm_num)
theorem B4112005 : Blo 960589 4112005 := bbase (se 4 (by rfl) ⟨385500, by rfl⟩ : syracuseStep 4112005 = 771001) (by norm_num)
theorem B8208053 : Blo 960589 8208053 := bbase (se 5 (by rfl) ⟨384752, by rfl⟩ : syracuseStep 8208053 = 769505) (by norm_num)
theorem B2440925 : Blo 960589 2440925 := bbase (se 3 (by rfl) ⟨457673, by rfl⟩ : syracuseStep 2440925 = 915347) (by norm_num)
theorem B1621741 : Blo 960589 1621741 := bbase (se 3 (by rfl) ⟨304076, by rfl⟩ : syracuseStep 1621741 = 608153) (by norm_num)
theorem B1621829 : Blo 960589 1621829 := bbase (se 4 (by rfl) ⟨152046, by rfl⟩ : syracuseStep 1621829 = 304093) (by norm_num)
theorem B1851277 : Blo 960589 1851277 := bbase (se 3 (by rfl) ⟨347114, by rfl⟩ : syracuseStep 1851277 = 694229) (by norm_num)
theorem B2441117 : Blo 960589 2441117 := bbase (se 3 (by rfl) ⟨457709, by rfl⟩ : syracuseStep 2441117 = 915419) (by norm_num)
theorem B1621957 : Blo 960589 1621957 := bbase (se 4 (by rfl) ⟨152058, by rfl⟩ : syracuseStep 1621957 = 304117) (by norm_num)
theorem B1622045 : Blo 960589 1622045 := bbase (se 3 (by rfl) ⟨304133, by rfl⟩ : syracuseStep 1622045 = 608267) (by norm_num)
theorem B1622173 : Blo 960589 1622173 := bbase (se 3 (by rfl) ⟨304157, by rfl⟩ : syracuseStep 1622173 = 608315) (by norm_num)
theorem B1622261 : Blo 960589 1622261 := bbase (se 5 (by rfl) ⟨76043, by rfl⟩ : syracuseStep 1622261 = 152087) (by norm_num)
theorem B2441461 : Blo 960589 2441461 := bbase (se 5 (by rfl) ⟨114443, by rfl⟩ : syracuseStep 2441461 = 228887) (by norm_num)
theorem B2441573 : Blo 960589 2441573 := bbase (se 4 (by rfl) ⟨228897, by rfl⟩ : syracuseStep 2441573 = 457795) (by norm_num)
theorem B1622389 : Blo 960589 1622389 := bbase (se 5 (by rfl) ⟨76049, by rfl⟩ : syracuseStep 1622389 = 152099) (by norm_num)
theorem B1622477 : Blo 960589 1622477 := bbase (se 3 (by rfl) ⟨304214, by rfl⟩ : syracuseStep 1622477 = 608429) (by norm_num)
theorem B2605589 : Blo 960589 2605589 := bbase (se 6 (by rfl) ⟨61068, by rfl⟩ : syracuseStep 2605589 = 122137) (by norm_num)
theorem B1622605 : Blo 960589 1622605 := bbase (se 3 (by rfl) ⟨304238, by rfl⟩ : syracuseStep 1622605 = 608477) (by norm_num)
theorem B2736757 : Blo 960589 2736757 := bbase (se 5 (by rfl) ⟨128285, by rfl⟩ : syracuseStep 2736757 = 256571) (by norm_num)
theorem B1622693 : Blo 960589 1622693 := bbase (se 4 (by rfl) ⟨152127, by rfl⟩ : syracuseStep 1622693 = 304255) (by norm_num)
theorem B3654341 : Blo 960589 3654341 := bbase (se 4 (by rfl) ⟨342594, by rfl⟩ : syracuseStep 3654341 = 685189) (by norm_num)
theorem B1622821 : Blo 960589 1622821 := bbase (se 4 (by rfl) ⟨152139, by rfl⟩ : syracuseStep 1622821 = 304279) (by norm_num)
theorem B1622909 : Blo 960589 1622909 := bbase (se 3 (by rfl) ⟨304295, by rfl⟩ : syracuseStep 1622909 = 608591) (by norm_num)
theorem B4866965 : Blo 960589 4866965 := bbase (se 6 (by rfl) ⟨114069, by rfl⟩ : syracuseStep 4866965 = 228139) (by norm_num)
theorem B1098649 : Blo 960589 1098649 := bbase (se 2 (by rfl) ⟨411993, by rfl⟩ : syracuseStep 1098649 = 823987) (by norm_num)
theorem B3654629 : Blo 960589 3654629 := bbase (se 4 (by rfl) ⟨342621, by rfl⟩ : syracuseStep 3654629 = 685243) (by norm_num)
theorem B1623037 : Blo 960589 1623037 := bbase (se 3 (by rfl) ⟨304319, by rfl⟩ : syracuseStep 1623037 = 608639) (by norm_num)
theorem B1623125 : Blo 960589 1623125 := bbase (se 8 (by rfl) ⟨9510, by rfl⟩ : syracuseStep 1623125 = 19021) (by norm_num)
theorem B1098941 : Blo 960589 1098941 := bbase (se 3 (by rfl) ⟨206051, by rfl⟩ : syracuseStep 1098941 = 412103) (by norm_num)
theorem B1623253 : Blo 960589 1623253 := bbase (se 7 (by rfl) ⟨19022, by rfl⟩ : syracuseStep 1623253 = 38045) (by norm_num)
theorem B1623341 : Blo 960589 1623341 := bbase (se 3 (by rfl) ⟨304376, by rfl⟩ : syracuseStep 1623341 = 608753) (by norm_num)
theorem B1623469 : Blo 960589 1623469 := bbase (se 3 (by rfl) ⟨304400, by rfl⟩ : syracuseStep 1623469 = 608801) (by norm_num)
theorem B1623557 : Blo 960589 1623557 := bbase (se 4 (by rfl) ⟨152208, by rfl⟩ : syracuseStep 1623557 = 304417) (by norm_num)
theorem B1099333 : Blo 960589 1099333 := bbase (se 4 (by rfl) ⟨103062, by rfl⟩ : syracuseStep 1099333 = 206125) (by norm_num)
theorem B1623685 : Blo 960589 1623685 := bbase (se 4 (by rfl) ⟨152220, by rfl⟩ : syracuseStep 1623685 = 304441) (by norm_num)
theorem B6178517 : Blo 960589 6178517 := bbase (se 7 (by rfl) ⟨72404, by rfl⟩ : syracuseStep 6178517 = 144809) (by norm_num)
theorem B1623773 : Blo 960589 1623773 := bbase (se 3 (by rfl) ⟨304457, by rfl⟩ : syracuseStep 1623773 = 608915) (by norm_num)
theorem B1623901 : Blo 960589 1623901 := bbase (se 3 (by rfl) ⟨304481, by rfl⟩ : syracuseStep 1623901 = 608963) (by norm_num)
theorem B1623989 : Blo 960589 1623989 := bbase (se 5 (by rfl) ⟨76124, by rfl⟩ : syracuseStep 1623989 = 152249) (by norm_num)
theorem B1624117 : Blo 960589 1624117 := bbase (se 5 (by rfl) ⟨76130, by rfl⟩ : syracuseStep 1624117 = 152261) (by norm_num)
theorem B2738261 : Blo 960589 2738261 := bbase (se 8 (by rfl) ⟨16044, by rfl⟩ : syracuseStep 2738261 = 32089) (by norm_num)
theorem B1755245 : Blo 960589 1755245 := bbase (se 3 (by rfl) ⟨329108, by rfl⟩ : syracuseStep 1755245 = 658217) (by norm_num)
theorem B3655813 : Blo 960589 3655813 := bbase (se 4 (by rfl) ⟨342732, by rfl⟩ : syracuseStep 3655813 = 685465) (by norm_num)
theorem B1624205 : Blo 960589 1624205 := bbase (se 3 (by rfl) ⟨304538, by rfl⟩ : syracuseStep 1624205 = 609077) (by norm_num)
theorem B4868261 : Blo 960589 4868261 := bbase (se 4 (by rfl) ⟨456399, by rfl⟩ : syracuseStep 4868261 = 912799) (by norm_num)
theorem B2082997 : Blo 960589 2082997 := bbase (se 5 (by rfl) ⟨97640, by rfl⟩ : syracuseStep 2082997 = 195281) (by norm_num)
theorem B1624333 : Blo 960589 1624333 := bbase (se 3 (by rfl) ⟨304562, by rfl⟩ : syracuseStep 1624333 = 609125) (by norm_num)
theorem B1624421 : Blo 960589 1624421 := bbase (se 4 (by rfl) ⟨152289, by rfl⟩ : syracuseStep 1624421 = 304579) (by norm_num)
theorem B3656117 : Blo 960589 3656117 := bbase (se 5 (by rfl) ⟨171380, by rfl⟩ : syracuseStep 3656117 = 342761) (by norm_num)
theorem B1624549 : Blo 960589 1624549 := bbase (se 4 (by rfl) ⟨152301, by rfl⟩ : syracuseStep 1624549 = 304603) (by norm_num)
theorem B1624637 : Blo 960589 1624637 := bbase (se 3 (by rfl) ⟨304619, by rfl⟩ : syracuseStep 1624637 = 609239) (by norm_num)
theorem B2312821 : Blo 960589 2312821 := bbase (se 5 (by rfl) ⟨108413, by rfl⟩ : syracuseStep 2312821 = 216827) (by norm_num)
theorem B2083477 : Blo 960589 2083477 := bbase (se 6 (by rfl) ⟨48831, by rfl⟩ : syracuseStep 2083477 = 97663) (by norm_num)
theorem B2312869 : Blo 960589 2312869 := bbase (se 4 (by rfl) ⟨216831, by rfl⟩ : syracuseStep 2312869 = 433663) (by norm_num)
theorem B1624765 : Blo 960589 1624765 := bbase (se 3 (by rfl) ⟨304643, by rfl⟩ : syracuseStep 1624765 = 609287) (by norm_num)
theorem B1624853 : Blo 960589 1624853 := bbase (se 6 (by rfl) ⟨38082, by rfl⟩ : syracuseStep 1624853 = 76165) (by norm_num)
theorem B1624981 : Blo 960589 1624981 := bbase (se 6 (by rfl) ⟨38085, by rfl⟩ : syracuseStep 1624981 = 76171) (by norm_num)
theorem B5196757 : Blo 960589 5196757 := bbase (se 7 (by rfl) ⟨60899, by rfl⟩ : syracuseStep 5196757 = 121799) (by norm_num)
theorem B1625069 : Blo 960589 1625069 := bbase (se 3 (by rfl) ⟨304700, by rfl⟩ : syracuseStep 1625069 = 609401) (by norm_num)
theorem B1952813 : Blo 960589 1952813 := bbase (se 3 (by rfl) ⟨366152, by rfl⟩ : syracuseStep 1952813 = 732305) (by norm_num)
theorem B1625197 : Blo 960589 1625197 := bbase (se 3 (by rfl) ⟨304724, by rfl⟩ : syracuseStep 1625197 = 609449) (by norm_num)
theorem B7818389 : Blo 960589 7818389 := bbase (se 6 (by rfl) ⟨183243, by rfl⟩ : syracuseStep 7818389 = 366487) (by norm_num)
theorem B1625285 : Blo 960589 1625285 := bbase (se 4 (by rfl) ⟨152370, by rfl⟩ : syracuseStep 1625285 = 304741) (by norm_num)
theorem B2313485 : Blo 960589 2313485 := bbase (se 3 (by rfl) ⟨433778, by rfl⟩ : syracuseStep 2313485 = 867557) (by norm_num)
theorem B1461557 : Blo 960589 1461557 := bbase (se 5 (by rfl) ⟨68510, by rfl⟩ : syracuseStep 1461557 = 137021) (by norm_num)
theorem B1625413 : Blo 960589 1625413 := bbase (se 4 (by rfl) ⟨152382, by rfl⟩ : syracuseStep 1625413 = 304765) (by norm_num)
theorem B1625501 : Blo 960589 1625501 := bbase (se 3 (by rfl) ⟨304781, by rfl⟩ : syracuseStep 1625501 = 609563) (by norm_num)
theorem B4869557 : Blo 960589 4869557 := bbase (se 5 (by rfl) ⟨228260, by rfl⟩ : syracuseStep 4869557 = 456521) (by norm_num)
theorem B1756669 : Blo 960589 1756669 := bbase (se 3 (by rfl) ⟨329375, by rfl⟩ : syracuseStep 1756669 = 658751) (by norm_num)
theorem B1625629 : Blo 960589 1625629 := bbase (se 3 (by rfl) ⟨304805, by rfl⟩ : syracuseStep 1625629 = 609611) (by norm_num)
theorem B2313829 : Blo 960589 2313829 := bbase (se 4 (by rfl) ⟨216921, by rfl⟩ : syracuseStep 2313829 = 433843) (by norm_num)
theorem B1625717 : Blo 960589 1625717 := bbase (se 5 (by rfl) ⟨76205, by rfl⟩ : syracuseStep 1625717 = 152411) (by norm_num)
theorem B2739845 : Blo 960589 2739845 := bbase (se 4 (by rfl) ⟨256860, by rfl⟩ : syracuseStep 2739845 = 513721) (by norm_num)
theorem B1232533 : Blo 960589 1232533 := bbase (se 6 (by rfl) ⟨28887, by rfl⟩ : syracuseStep 1232533 = 57775) (by norm_num)
theorem B1756829 : Blo 960589 1756829 := bbase (se 3 (by rfl) ⟨329405, by rfl⟩ : syracuseStep 1756829 = 658811) (by norm_num)
theorem B1953461 : Blo 960589 1953461 := bbase (se 5 (by rfl) ⟨91568, by rfl⟩ : syracuseStep 1953461 = 183137) (by norm_num)
theorem B1855157 : Blo 960589 1855157 := bbase (se 5 (by rfl) ⟨86960, by rfl⟩ : syracuseStep 1855157 = 173921) (by norm_num)
theorem B1625845 : Blo 960589 1625845 := bbase (se 5 (by rfl) ⟨76211, by rfl⟩ : syracuseStep 1625845 = 152423) (by norm_num)
theorem B2051885 : Blo 960589 2051885 := bbase (se 3 (by rfl) ⟨384728, by rfl⟩ : syracuseStep 2051885 = 769457) (by norm_num)
theorem B2314061 : Blo 960589 2314061 := bbase (se 3 (by rfl) ⟨433886, by rfl⟩ : syracuseStep 2314061 = 867773) (by norm_num)
theorem B1625933 : Blo 960589 1625933 := bbase (se 3 (by rfl) ⟨304862, by rfl⟩ : syracuseStep 1625933 = 609725) (by norm_num)
theorem B3297125 : Blo 960589 3297125 := bbase (se 4 (by rfl) ⟨309105, by rfl⟩ : syracuseStep 3297125 = 618211) (by norm_num)
theorem B1626061 : Blo 960589 1626061 := bbase (se 3 (by rfl) ⟨304886, by rfl⟩ : syracuseStep 1626061 = 609773) (by norm_num)
theorem B2314253 : Blo 960589 2314253 := bbase (se 3 (by rfl) ⟨433922, by rfl⟩ : syracuseStep 2314253 = 867845) (by norm_num)
theorem B1626149 : Blo 960589 1626149 := bbase (se 4 (by rfl) ⟨152451, by rfl⟩ : syracuseStep 1626149 = 304903) (by norm_num)
theorem B1626277 : Blo 960589 1626277 := bbase (se 4 (by rfl) ⟨152463, by rfl⟩ : syracuseStep 1626277 = 304927) (by norm_num)
theorem B1462469 : Blo 960589 1462469 := bbase (se 4 (by rfl) ⟨137106, by rfl⟩ : syracuseStep 1462469 = 274213) (by norm_num)
theorem B1626365 : Blo 960589 1626365 := bbase (se 3 (by rfl) ⟨304943, by rfl⟩ : syracuseStep 1626365 = 609887) (by norm_num)
theorem B2740517 : Blo 960589 2740517 := bbase (se 4 (by rfl) ⟨256923, by rfl⟩ : syracuseStep 2740517 = 513847) (by norm_num)
theorem B2314541 : Blo 960589 2314541 := bbase (se 3 (by rfl) ⟨433976, by rfl⟩ : syracuseStep 2314541 = 867953) (by norm_num)
theorem B1626493 : Blo 960589 1626493 := bbase (se 3 (by rfl) ⟨304967, by rfl⟩ : syracuseStep 1626493 = 609935) (by norm_num)
theorem B2085277 : Blo 960589 2085277 := bbase (se 3 (by rfl) ⟨390989, by rfl⟩ : syracuseStep 2085277 = 781979) (by norm_num)
theorem B1233353 : Blo 960589 1233353 := bbase (se 2 (by rfl) ⟨462507, by rfl⟩ : syracuseStep 1233353 = 925015) (by norm_num)
theorem B1626581 : Blo 960589 1626581 := bbase (se 7 (by rfl) ⟨19061, by rfl⟩ : syracuseStep 1626581 = 38123) (by norm_num)
theorem B3658229 : Blo 960589 3658229 := bbase (se 5 (by rfl) ⟨171479, by rfl⟩ : syracuseStep 3658229 = 342959) (by norm_num)
theorem B4117013 : Blo 960589 4117013 := bbase (se 6 (by rfl) ⟨96492, by rfl⟩ : syracuseStep 4117013 = 192985) (by norm_num)
theorem B1626709 : Blo 960589 1626709 := bbase (se 8 (by rfl) ⟨9531, by rfl⟩ : syracuseStep 1626709 = 19063) (by norm_num)
theorem B1626797 : Blo 960589 1626797 := bbase (se 3 (by rfl) ⟨305024, by rfl⟩ : syracuseStep 1626797 = 610049) (by norm_num)
theorem B4870853 : Blo 960589 4870853 := bbase (se 4 (by rfl) ⟨456642, by rfl⟩ : syracuseStep 4870853 = 913285) (by norm_num)
theorem B2740949 : Blo 960589 2740949 := bbase (se 7 (by rfl) ⟨32120, by rfl⟩ : syracuseStep 2740949 = 64241) (by norm_num)
theorem B3658517 : Blo 960589 3658517 := bbase (se 6 (by rfl) ⟨85746, by rfl⟩ : syracuseStep 3658517 = 171493) (by norm_num)
theorem B1626925 : Blo 960589 1626925 := bbase (se 3 (by rfl) ⟨305048, by rfl⟩ : syracuseStep 1626925 = 610097) (by norm_num)
theorem B4117301 : Blo 960589 4117301 := bbase (se 5 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 4117301 = 385997) (by norm_num)
theorem B1233749 : Blo 960589 1233749 := bbase (se 9 (by rfl) ⟨3614, by rfl⟩ : syracuseStep 1233749 = 7229) (by norm_num)
theorem B1627013 : Blo 960589 1627013 := bbase (se 4 (by rfl) ⟨152532, by rfl⟩ : syracuseStep 1627013 = 305065) (by norm_num)
theorem B1627141 : Blo 960589 1627141 := bbase (se 4 (by rfl) ⟨152544, by rfl⟩ : syracuseStep 1627141 = 305089) (by norm_num)
theorem B1627229 : Blo 960589 1627229 := bbase (se 3 (by rfl) ⟨305105, by rfl⟩ : syracuseStep 1627229 = 610211) (by norm_num)
theorem B1627357 : Blo 960589 1627357 := bbase (se 3 (by rfl) ⟨305129, by rfl⟩ : syracuseStep 1627357 = 610259) (by norm_num)
theorem B1627445 : Blo 960589 1627445 := bbase (se 5 (by rfl) ⟨76286, by rfl⟩ : syracuseStep 1627445 = 152573) (by norm_num)
theorem B1824133 : Blo 960589 1824133 := bbase (se 4 (by rfl) ⟨171012, by rfl⟩ : syracuseStep 1824133 = 342025) (by norm_num)
theorem B2053525 : Blo 960589 2053525 := bbase (se 6 (by rfl) ⟨48129, by rfl⟩ : syracuseStep 2053525 = 96259) (by norm_num)
theorem B1627573 : Blo 960589 1627573 := bbase (se 5 (by rfl) ⟨76292, by rfl⟩ : syracuseStep 1627573 = 152585) (by norm_num)
theorem B2741701 : Blo 960589 2741701 := bbase (se 4 (by rfl) ⟨257034, by rfl⟩ : syracuseStep 2741701 = 514069) (by norm_num)
theorem B1627661 : Blo 960589 1627661 := bbase (se 3 (by rfl) ⟨305186, by rfl⟩ : syracuseStep 1627661 = 610373) (by norm_num)
theorem B1824277 : Blo 960589 1824277 := bbase (se 6 (by rfl) ⟨42756, by rfl⟩ : syracuseStep 1824277 = 85513) (by norm_num)
theorem B4118053 : Blo 960589 4118053 := bbase (se 4 (by rfl) ⟨386067, by rfl⟩ : syracuseStep 4118053 = 772135) (by norm_num)
theorem B1824437 : Blo 960589 1824437 := bbase (se 5 (by rfl) ⟨85520, by rfl⟩ : syracuseStep 1824437 = 171041) (by norm_num)
theorem B1824581 : Blo 960589 1824581 := bbase (se 4 (by rfl) ⟨171054, by rfl⟩ : syracuseStep 1824581 = 342109) (by norm_num)
theorem B13850453 : Blo 960589 13850453 := bbase (se 9 (by rfl) ⟨40577, by rfl⟩ : syracuseStep 13850453 = 81155) (by norm_num)
theorem B3659701 : Blo 960589 3659701 := bbase (se 5 (by rfl) ⟨171548, by rfl⟩ : syracuseStep 3659701 = 343097) (by norm_num)
theorem B4872149 : Blo 960589 4872149 := bbase (se 7 (by rfl) ⟨57095, by rfl⟩ : syracuseStep 4872149 = 114191) (by norm_num)
theorem B1824869 : Blo 960589 1824869 := bbase (se 4 (by rfl) ⟨171081, by rfl⟩ : syracuseStep 1824869 = 342163) (by norm_num)
theorem B1267813 : Blo 960589 1267813 := bbase (se 4 (by rfl) ⟨118857, by rfl⟩ : syracuseStep 1267813 = 237715) (by norm_num)
theorem B3660005 : Blo 960589 3660005 := bbase (se 4 (by rfl) ⟨343125, by rfl⟩ : syracuseStep 3660005 = 686251) (by norm_num)
theorem B1825021 : Blo 960589 1825021 := bbase (se 3 (by rfl) ⟨342191, by rfl⟩ : syracuseStep 1825021 = 684383) (by norm_num)
theorem B4118789 : Blo 960589 4118789 := bbase (se 4 (by rfl) ⟨386136, by rfl⟩ : syracuseStep 4118789 = 772273) (by norm_num)
theorem B2054413 : Blo 960589 2054413 := bbase (se 3 (by rfl) ⟨385202, by rfl⟩ : syracuseStep 2054413 = 770405) (by norm_num)
theorem B13883669 : Blo 960589 13883669 := bbase (se 6 (by rfl) ⟨325398, by rfl⟩ : syracuseStep 13883669 = 650797) (by norm_num)
theorem B1825325 : Blo 960589 1825325 := bbase (se 3 (by rfl) ⟨342248, by rfl⟩ : syracuseStep 1825325 = 684497) (by norm_num)
theorem B2054909 : Blo 960589 2054909 := bbase (se 3 (by rfl) ⟨385295, by rfl⟩ : syracuseStep 2054909 = 770591) (by norm_num)
theorem B9362261 : Blo 960589 9362261 := bbase (se 9 (by rfl) ⟨27428, by rfl⟩ : syracuseStep 9362261 = 54857) (by norm_num)
theorem B1465237 : Blo 960589 1465237 := bbase (se 6 (by rfl) ⟨34341, by rfl⟩ : syracuseStep 1465237 = 68683) (by norm_num)
theorem B973873 : Blo 960589 973873 := bbase (se 2 (by rfl) ⟨365202, by rfl⟩ : syracuseStep 973873 = 730405) (by norm_num)
theorem B7298261 : Blo 960589 7298261 := bbase (se 7 (by rfl) ⟨85526, by rfl⟩ : syracuseStep 7298261 = 171053) (by norm_num)
theorem B4873445 : Blo 960589 4873445 := bbase (se 4 (by rfl) ⟨456885, by rfl⟩ : syracuseStep 4873445 = 913771) (by norm_num)
theorem B1826077 : Blo 960589 1826077 := bbase (se 3 (by rfl) ⟨342389, by rfl⟩ : syracuseStep 1826077 = 684779) (by norm_num)
theorem B15621461 : Blo 960589 15621461 := bbase (se 11 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 15621461 = 22883) (by norm_num)
theorem B1826221 : Blo 960589 1826221 := bbase (se 3 (by rfl) ⟨342416, by rfl⟩ : syracuseStep 1826221 = 684833) (by norm_num)
theorem B10968533 : Blo 960589 10968533 := bbase (se 7 (by rfl) ⟨128537, by rfl⟩ : syracuseStep 10968533 = 257075) (by norm_num)
theorem B1826381 : Blo 960589 1826381 := bbase (se 3 (by rfl) ⟨342446, by rfl⟩ : syracuseStep 1826381 = 684893) (by norm_num)
theorem B2055773 : Blo 960589 2055773 := bbase (se 3 (by rfl) ⟨385457, by rfl⟩ : syracuseStep 2055773 = 770915) (by norm_num)
theorem B1040045 : Blo 960589 1040045 := bbase (se 3 (by rfl) ⟨195008, by rfl⟩ : syracuseStep 1040045 = 390017) (by norm_num)
theorem B974525 : Blo 960589 974525 := bbase (se 3 (by rfl) ⟨182723, by rfl⟩ : syracuseStep 974525 = 365447) (by norm_num)
theorem B1302221 : Blo 960589 1302221 := bbase (se 3 (by rfl) ⟨244166, by rfl⟩ : syracuseStep 1302221 = 488333) (by norm_num)
theorem B1826525 : Blo 960589 1826525 := bbase (se 3 (by rfl) ⟨342473, by rfl⟩ : syracuseStep 1826525 = 684947) (by norm_num)
theorem B1236709 : Blo 960589 1236709 := bbase (se 4 (by rfl) ⟨115941, by rfl⟩ : syracuseStep 1236709 = 231883) (by norm_num)
theorem B2055917 : Blo 960589 2055917 := bbase (se 3 (by rfl) ⟨385484, by rfl⟩ : syracuseStep 2055917 = 770969) (by norm_num)
theorem B974749 : Blo 960589 974749 := bbase (se 3 (by rfl) ⟨182765, by rfl⟩ : syracuseStep 974749 = 365531) (by norm_num)
theorem B3465125 : Blo 960589 3465125 := bbase (se 4 (by rfl) ⟨324855, by rfl⟩ : syracuseStep 3465125 = 649711) (by norm_num)
theorem B1368037 : Blo 960589 1368037 := bbase (se 4 (by rfl) ⟨128253, by rfl⟩ : syracuseStep 1368037 = 256507) (by norm_num)
theorem B1826813 : Blo 960589 1826813 := bbase (se 3 (by rfl) ⟨342527, by rfl⟩ : syracuseStep 1826813 = 685055) (by norm_num)
theorem B1826965 : Blo 960589 1826965 := bbase (se 6 (by rfl) ⟨42819, by rfl⟩ : syracuseStep 1826965 = 85639) (by norm_num)
theorem B2744549 : Blo 960589 2744549 := bbase (se 4 (by rfl) ⟨257301, by rfl⟩ : syracuseStep 2744549 = 514603) (by norm_num)
theorem B4940021 : Blo 960589 4940021 := bbase (se 5 (by rfl) ⟨231563, by rfl⟩ : syracuseStep 4940021 = 463127) (by norm_num)
theorem B975109 : Blo 960589 975109 := bbase (se 4 (by rfl) ⟨91416, by rfl⟩ : syracuseStep 975109 = 182833) (by norm_num)
theorem B3662117 : Blo 960589 3662117 := bbase (se 4 (by rfl) ⟨343323, by rfl⟩ : syracuseStep 3662117 = 686647) (by norm_num)
theorem B3465541 : Blo 960589 3465541 := bbase (se 4 (by rfl) ⟨324894, by rfl⟩ : syracuseStep 3465541 = 649789) (by norm_num)
theorem B1827269 : Blo 960589 1827269 := bbase (se 4 (by rfl) ⟨171306, by rfl⟩ : syracuseStep 1827269 = 342613) (by norm_num)
theorem B2056661 : Blo 960589 2056661 := bbase (se 7 (by rfl) ⟨24101, by rfl⟩ : syracuseStep 2056661 = 48203) (by norm_num)
theorem B4874741 : Blo 960589 4874741 := bbase (se 5 (by rfl) ⟨228503, by rfl⟩ : syracuseStep 4874741 = 457007) (by norm_num)
theorem B975385 : Blo 960589 975385 := bbase (se 2 (by rfl) ⟨365769, by rfl⟩ : syracuseStep 975385 = 731539) (by norm_num)
theorem B3662405 : Blo 960589 3662405 := bbase (se 4 (by rfl) ⟨343350, by rfl⟩ : syracuseStep 3662405 = 686701) (by norm_num)
theorem B975433 : Blo 960589 975433 := bbase (se 2 (by rfl) ⟨365787, by rfl⟩ : syracuseStep 975433 = 731575) (by norm_num)
theorem B1303141 : Blo 960589 1303141 := bbase (se 4 (by rfl) ⟨122169, by rfl⟩ : syracuseStep 1303141 = 244339) (by norm_num)
theorem B1270453 : Blo 960589 1270453 := bbase (se 5 (by rfl) ⟨59552, by rfl⟩ : syracuseStep 1270453 = 119105) (by norm_num)
theorem B1368829 : Blo 960589 1368829 := bbase (se 3 (by rfl) ⟨256655, by rfl⟩ : syracuseStep 1368829 = 513311) (by norm_num)
theorem B4940741 : Blo 960589 4940741 := bbase (se 4 (by rfl) ⟨463194, by rfl⟩ : syracuseStep 4940741 = 926389) (by norm_num)
theorem B4449269 : Blo 960589 4449269 := bbase (se 5 (by rfl) ⟨208559, by rfl⟩ : syracuseStep 4449269 = 417119) (by norm_num)
theorem B3466277 : Blo 960589 3466277 := bbase (se 4 (by rfl) ⟨324963, by rfl⟩ : syracuseStep 3466277 = 649927) (by norm_num)
theorem B1369165 : Blo 960589 1369165 := bbase (se 3 (by rfl) ⟨256718, by rfl⟩ : syracuseStep 1369165 = 513437) (by norm_num)
theorem B1828021 : Blo 960589 1828021 := bbase (se 5 (by rfl) ⟨85688, by rfl⟩ : syracuseStep 1828021 = 171377) (by norm_num)
theorem B2057413 : Blo 960589 2057413 := bbase (se 4 (by rfl) ⟨192882, by rfl⟩ : syracuseStep 2057413 = 385765) (by norm_num)
theorem B1369381 : Blo 960589 1369381 := bbase (se 4 (by rfl) ⟨128379, by rfl⟩ : syracuseStep 1369381 = 256759) (by norm_num)
theorem B2778437 : Blo 960589 2778437 := bbase (se 4 (by rfl) ⟨260478, by rfl⟩ : syracuseStep 2778437 = 520957) (by norm_num)
theorem B1828165 : Blo 960589 1828165 := bbase (se 4 (by rfl) ⟨171390, by rfl⟩ : syracuseStep 1828165 = 342781) (by norm_num)
theorem B6939989 : Blo 960589 6939989 := bbase (se 12 (by rfl) ⟨2541, by rfl⟩ : syracuseStep 6939989 = 5083) (by norm_num)
theorem B2057557 : Blo 960589 2057557 := bbase (se 12 (by rfl) ⟨753, by rfl⟩ : syracuseStep 2057557 = 1507) (by norm_num)
theorem B976261 : Blo 960589 976261 := bbase (se 4 (by rfl) ⟨91524, by rfl⟩ : syracuseStep 976261 = 183049) (by norm_num)
theorem B2745733 : Blo 960589 2745733 := bbase (se 4 (by rfl) ⟨257412, by rfl⟩ : syracuseStep 2745733 = 514825) (by norm_num)
theorem B5203349 : Blo 960589 5203349 := bbase (se 6 (by rfl) ⟨121953, by rfl⟩ : syracuseStep 5203349 = 243907) (by norm_num)
theorem B2778533 : Blo 960589 2778533 := bbase (se 4 (by rfl) ⟨260487, by rfl⟩ : syracuseStep 2778533 = 520975) (by norm_num)
theorem B1828325 : Blo 960589 1828325 := bbase (se 4 (by rfl) ⟨171405, by rfl⟩ : syracuseStep 1828325 = 342811) (by norm_num)
theorem B2745893 : Blo 960589 2745893 := bbase (se 4 (by rfl) ⟨257427, by rfl⟩ : syracuseStep 2745893 = 514855) (by norm_num)
theorem B1828469 : Blo 960589 1828469 := bbase (se 5 (by rfl) ⟨85709, by rfl⟩ : syracuseStep 1828469 = 171419) (by norm_num)
theorem B1369757 : Blo 960589 1369757 := bbase (se 3 (by rfl) ⟨256829, by rfl⟩ : syracuseStep 1369757 = 513659) (by norm_num)
theorem B2057933 : Blo 960589 2057933 := bbase (se 3 (by rfl) ⟨385862, by rfl⟩ : syracuseStep 2057933 = 771725) (by norm_num)
theorem B976601 : Blo 960589 976601 := bbase (se 2 (by rfl) ⟨366225, by rfl⟩ : syracuseStep 976601 = 732451) (by norm_num)
theorem B4876037 : Blo 960589 4876037 := bbase (se 4 (by rfl) ⟨457128, by rfl⟩ : syracuseStep 4876037 = 914257) (by norm_num)
theorem B2746133 : Blo 960589 2746133 := bbase (se 6 (by rfl) ⟨64362, by rfl⟩ : syracuseStep 2746133 = 128725) (by norm_num)
theorem B1828757 : Blo 960589 1828757 := bbase (se 6 (by rfl) ⟨42861, by rfl⟩ : syracuseStep 1828757 = 85723) (by norm_num)
theorem B2746325 : Blo 960589 2746325 := bbase (se 7 (by rfl) ⟨32183, by rfl⟩ : syracuseStep 2746325 = 64367) (by norm_num)
theorem B1828909 : Blo 960589 1828909 := bbase (se 3 (by rfl) ⟨342920, by rfl⟩ : syracuseStep 1828909 = 685841) (by norm_num)
theorem B9234485 : Blo 960589 9234485 := bbase (se 5 (by rfl) ⟨432866, by rfl⟩ : syracuseStep 9234485 = 865733) (by norm_num)
theorem B2058301 : Blo 960589 2058301 := bbase (se 3 (by rfl) ⟨385931, by rfl⟩ : syracuseStep 2058301 = 771863) (by norm_num)
theorem B1173685 : Blo 960589 1173685 := bbase (se 5 (by rfl) ⟨55016, by rfl⟩ : syracuseStep 1173685 = 110033) (by norm_num)
theorem B1829213 : Blo 960589 1829213 := bbase (se 3 (by rfl) ⟨342977, by rfl⟩ : syracuseStep 1829213 = 685955) (by norm_num)
theorem B17132053 : Blo 960589 17132053 := bbase (se 6 (by rfl) ⟨401532, by rfl⟩ : syracuseStep 17132053 = 803065) (by norm_num)
theorem B3467861 : Blo 960589 3467861 := bbase (se 8 (by rfl) ⟨20319, by rfl⟩ : syracuseStep 3467861 = 40639) (by norm_num)
theorem B977509 : Blo 960589 977509 := bbase (se 4 (by rfl) ⟨91641, by rfl⟩ : syracuseStep 977509 = 183283) (by norm_num)
theorem B1174181 : Blo 960589 1174181 := bbase (se 4 (by rfl) ⟨110079, by rfl⟩ : syracuseStep 1174181 = 220159) (by norm_num)
theorem B1043353 : Blo 960589 1043353 := bbase (se 2 (by rfl) ⟨391257, by rfl⟩ : syracuseStep 1043353 = 782515) (by norm_num)
theorem B4877333 : Blo 960589 4877333 := bbase (se 6 (by rfl) ⟨114312, by rfl⟩ : syracuseStep 4877333 = 228625) (by norm_num)
theorem B1371181 : Blo 960589 1371181 := bbase (se 3 (by rfl) ⟨257096, by rfl⟩ : syracuseStep 1371181 = 514193) (by norm_num)
theorem B1829965 : Blo 960589 1829965 := bbase (se 3 (by rfl) ⟨343118, by rfl⟩ : syracuseStep 1829965 = 686237) (by norm_num)
theorem B1830109 : Blo 960589 1830109 := bbase (se 3 (by rfl) ⟨343145, by rfl⟩ : syracuseStep 1830109 = 686291) (by norm_num)
theorem B1830269 : Blo 960589 1830269 := bbase (se 3 (by rfl) ⟨343175, by rfl⟩ : syracuseStep 1830269 = 686351) (by norm_num)
theorem B1043885 : Blo 960589 1043885 := bbase (se 3 (by rfl) ⟨195728, by rfl⟩ : syracuseStep 1043885 = 391457) (by norm_num)
theorem B1830413 : Blo 960589 1830413 := bbase (se 3 (by rfl) ⟨343202, by rfl⟩ : syracuseStep 1830413 = 686405) (by norm_num)
theorem B2059805 : Blo 960589 2059805 := bbase (se 3 (by rfl) ⟨386213, by rfl⟩ : syracuseStep 2059805 = 772427) (by norm_num)
theorem B1044037 : Blo 960589 1044037 := bbase (se 4 (by rfl) ⟨97878, by rfl⟩ : syracuseStep 1044037 = 195757) (by norm_num)
theorem B1371773 : Blo 960589 1371773 := bbase (se 3 (by rfl) ⟨257207, by rfl⟩ : syracuseStep 1371773 = 514415) (by norm_num)
theorem B2059949 : Blo 960589 2059949 := bbase (se 3 (by rfl) ⟨386240, by rfl⟩ : syracuseStep 2059949 = 772481) (by norm_num)
theorem B1371853 : Blo 960589 1371853 := bbase (se 3 (by rfl) ⟨257222, by rfl⟩ : syracuseStep 1371853 = 514445) (by norm_num)
theorem B1732309 : Blo 960589 1732309 := bbase (se 7 (by rfl) ⟨20300, by rfl⟩ : syracuseStep 1732309 = 40601) (by norm_num)
theorem B1830701 : Blo 960589 1830701 := bbase (se 3 (by rfl) ⟨343256, by rfl⟩ : syracuseStep 1830701 = 686513) (by norm_num)
theorem B1371973 : Blo 960589 1371973 := bbase (se 4 (by rfl) ⟨128622, by rfl⟩ : syracuseStep 1371973 = 257245) (by norm_num)
theorem B1372069 : Blo 960589 1372069 := bbase (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) (by norm_num)
theorem B1830853 : Blo 960589 1830853 := bbase (se 4 (by rfl) ⟨171642, by rfl⟩ : syracuseStep 1830853 = 343285) (by norm_num)
theorem B4616165 : Blo 960589 4616165 := bbase (se 4 (by rfl) ⟨432765, by rfl⟩ : syracuseStep 4616165 = 865531) (by norm_num)
theorem B4681957 : Blo 960589 4681957 := bbase (se 4 (by rfl) ⟨438933, by rfl⟩ : syracuseStep 4681957 = 877867) (by norm_num)
theorem B1831157 : Blo 960589 1831157 := bbase (se 5 (by rfl) ⟨85835, by rfl⟩ : syracuseStep 1831157 = 171671) (by norm_num)
theorem B4878629 : Blo 960589 4878629 := bbase (se 4 (by rfl) ⟨457371, by rfl⟩ : syracuseStep 4878629 = 914743) (by norm_num)
theorem B2191661 : Blo 960589 2191661 := bbase (se 3 (by rfl) ⟨410936, by rfl⟩ : syracuseStep 2191661 = 821873) (by norm_num)
theorem B6025589 : Blo 960589 6025589 := bbase (se 5 (by rfl) ⟨282449, by rfl⟩ : syracuseStep 6025589 = 564899) (by norm_num)
theorem B1372565 : Blo 960589 1372565 := bbase (se 6 (by rfl) ⟨32169, by rfl⟩ : syracuseStep 1372565 = 64339) (by norm_num)
theorem B1733557 : Blo 960589 1733557 := bbase (se 5 (by rfl) ⟨81260, by rfl⟩ : syracuseStep 1733557 = 162521) (by norm_num)
theorem B1373117 : Blo 960589 1373117 := bbase (se 3 (by rfl) ⟨257459, by rfl⟩ : syracuseStep 1373117 = 514919) (by norm_num)
theorem B7402517 : Blo 960589 7402517 := bbase (se 6 (by rfl) ⟨173496, by rfl⟩ : syracuseStep 7402517 = 346993) (by norm_num)
theorem B6157397 : Blo 960589 6157397 := bbase (se 8 (by rfl) ⟨36078, by rfl⟩ : syracuseStep 6157397 = 72157) (by norm_num)
theorem B17528021 : Blo 960589 17528021 := bbase (se 7 (by rfl) ⟨205406, by rfl⟩ : syracuseStep 17528021 = 410813) (by norm_num)
theorem B1733845 : Blo 960589 1733845 := bbase (se 7 (by rfl) ⟨20318, by rfl⟩ : syracuseStep 1733845 = 40637) (by norm_num)
theorem B3470629 : Blo 960589 3470629 := bbase (se 4 (by rfl) ⟨325371, by rfl⟩ : syracuseStep 3470629 = 650743) (by norm_num)
theorem B1734061 : Blo 960589 1734061 := bbase (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) (by norm_num)
theorem B4879925 : Blo 960589 4879925 := bbase (se 5 (by rfl) ⟨228746, by rfl⟩ : syracuseStep 4879925 = 457493) (by norm_num)
theorem B9369589 : Blo 960589 9369589 := bbase (se 5 (by rfl) ⟨439199, by rfl⟩ : syracuseStep 9369589 = 878399) (by norm_num)
theorem B2783429 : Blo 960589 2783429 := bbase (se 4 (by rfl) ⟨260946, by rfl⟩ : syracuseStep 2783429 = 521893) (by norm_num)
theorem B3242213 : Blo 960589 3242213 := bbase (se 4 (by rfl) ⟨303957, by rfl⟩ : syracuseStep 3242213 = 607915) (by norm_num)
theorem B1734941 : Blo 960589 1734941 := bbase (se 3 (by rfl) ⟨325301, by rfl⟩ : syracuseStep 1734941 = 650603) (by norm_num)
theorem B3701045 : Blo 960589 3701045 := bbase (se 5 (by rfl) ⟨173486, by rfl⟩ : syracuseStep 3701045 = 346973) (by norm_num)
theorem B1735157 : Blo 960589 1735157 := bbase (se 5 (by rfl) ⟨81335, by rfl⟩ : syracuseStep 1735157 = 162671) (by norm_num)
theorem B3242645 : Blo 960589 3242645 := bbase (se 6 (by rfl) ⟨75999, by rfl⟩ : syracuseStep 3242645 = 151999) (by norm_num)
theorem B2161349 : Blo 960589 2161349 := bbase (se 4 (by rfl) ⟨202626, by rfl⟩ : syracuseStep 2161349 = 405253) (by norm_num)
theorem B2161421 : Blo 960589 2161421 := bbase (se 3 (by rfl) ⟨405266, by rfl⟩ : syracuseStep 2161421 = 810533) (by norm_num)
theorem B1735445 : Blo 960589 1735445 := bbase (se 6 (by rfl) ⟨40674, by rfl⟩ : syracuseStep 1735445 = 81349) (by norm_num)
theorem B7306037 : Blo 960589 7306037 := bbase (se 5 (by rfl) ⟨342470, by rfl⟩ : syracuseStep 7306037 = 684941) (by norm_num)
theorem B4881221 : Blo 960589 4881221 := bbase (se 4 (by rfl) ⟨457614, by rfl⟩ : syracuseStep 4881221 = 915229) (by norm_num)
theorem B2194253 : Blo 960589 2194253 := bbase (se 3 (by rfl) ⟨411422, by rfl⟩ : syracuseStep 2194253 = 822845) (by norm_num)
theorem B2161493 : Blo 960589 2161493 := bbase (se 9 (by rfl) ⟨6332, by rfl⟩ : syracuseStep 2161493 = 12665) (by norm_num)
theorem B2161565 : Blo 960589 2161565 := bbase (se 3 (by rfl) ⟨405293, by rfl⟩ : syracuseStep 2161565 = 810587) (by norm_num)
theorem B3079109 : Blo 960589 3079109 := bbase (se 4 (by rfl) ⟨288666, by rfl⟩ : syracuseStep 3079109 = 577333) (by norm_num)
theorem B2161637 : Blo 960589 2161637 := bbase (se 4 (by rfl) ⟨202653, by rfl⟩ : syracuseStep 2161637 = 405307) (by norm_num)
theorem B2161709 : Blo 960589 2161709 := bbase (se 3 (by rfl) ⟨405320, by rfl⟩ : syracuseStep 2161709 = 810641) (by norm_num)
theorem B3243077 : Blo 960589 3243077 := bbase (se 4 (by rfl) ⟨304038, by rfl⟩ : syracuseStep 3243077 = 608077) (by norm_num)
theorem B2161781 : Blo 960589 2161781 := bbase (se 5 (by rfl) ⟨101333, by rfl⟩ : syracuseStep 2161781 = 202667) (by norm_num)
theorem B1440893 : Blo 960589 1440893 := bbase (se 3 (by rfl) ⟨270167, by rfl⟩ : syracuseStep 1440893 = 540335) (by norm_num)
theorem B1440917 : Blo 960589 1440917 := bbase (se 6 (by rfl) ⟨33771, by rfl⟩ : syracuseStep 1440917 = 67543) (by norm_num)
theorem B1539221 : Blo 960589 1539221 := bbase (se 6 (by rfl) ⟨36075, by rfl⟩ : syracuseStep 1539221 = 72151) (by norm_num)
theorem B1440941 : Blo 960589 1440941 := bbase (se 3 (by rfl) ⟨270176, by rfl⟩ : syracuseStep 1440941 = 540353) (by norm_num)
theorem B2161853 : Blo 960589 2161853 := bbase (se 3 (by rfl) ⟨405347, by rfl⟩ : syracuseStep 2161853 = 810695) (by norm_num)
theorem B1440965 : Blo 960589 1440965 := bbase (se 4 (by rfl) ⟨135090, by rfl⟩ : syracuseStep 1440965 = 270181) (by norm_num)
theorem B1440989 : Blo 960589 1440989 := bbase (se 3 (by rfl) ⟨270185, by rfl⟩ : syracuseStep 1440989 = 540371) (by norm_num)
theorem B1441013 : Blo 960589 1441013 := bbase (se 5 (by rfl) ⟨67547, by rfl⟩ : syracuseStep 1441013 = 135095) (by norm_num)
theorem B2161925 : Blo 960589 2161925 := bbase (se 4 (by rfl) ⟨202680, by rfl⟩ : syracuseStep 2161925 = 405361) (by norm_num)
theorem B1441037 : Blo 960589 1441037 := bbase (se 3 (by rfl) ⟨270194, by rfl⟩ : syracuseStep 1441037 = 540389) (by norm_num)
theorem B5471509 : Blo 960589 5471509 := bbase (se 6 (by rfl) ⟨128238, by rfl⟩ : syracuseStep 5471509 = 256477) (by norm_num)
theorem B1441061 : Blo 960589 1441061 := bbase (se 4 (by rfl) ⟨135099, by rfl⟩ : syracuseStep 1441061 = 270199) (by norm_num)
theorem B1441085 : Blo 960589 1441085 := bbase (se 3 (by rfl) ⟨270203, by rfl⟩ : syracuseStep 1441085 = 540407) (by norm_num)
theorem B2161997 : Blo 960589 2161997 := bbase (se 3 (by rfl) ⟨405374, by rfl⟩ : syracuseStep 2161997 = 810749) (by norm_num)
theorem B1441109 : Blo 960589 1441109 := bbase (se 11 (by rfl) ⟨1055, by rfl⟩ : syracuseStep 1441109 = 2111) (by norm_num)
theorem B1441133 : Blo 960589 1441133 := bbase (se 3 (by rfl) ⟨270212, by rfl⟩ : syracuseStep 1441133 = 540425) (by norm_num)
theorem B1080697 : Blo 960589 1080697 := bbase (se 2 (by rfl) ⟨405261, by rfl⟩ : syracuseStep 1080697 = 810523) (by norm_num)
theorem B1441157 : Blo 960589 1441157 := bbase (se 4 (by rfl) ⟨135108, by rfl⟩ : syracuseStep 1441157 = 270217) (by norm_num)
theorem B2162069 : Blo 960589 2162069 := bbase (se 6 (by rfl) ⟨50673, by rfl⟩ : syracuseStep 2162069 = 101347) (by norm_num)
theorem B1080733 : Blo 960589 1080733 := bbase (se 3 (by rfl) ⟨202637, by rfl⟩ : syracuseStep 1080733 = 405275) (by norm_num)
theorem B1441181 : Blo 960589 1441181 := bbase (se 3 (by rfl) ⟨270221, by rfl⟩ : syracuseStep 1441181 = 540443) (by norm_num)
theorem B1441205 : Blo 960589 1441205 := bbase (se 5 (by rfl) ⟨67556, by rfl⟩ : syracuseStep 1441205 = 135113) (by norm_num)
theorem B1080769 : Blo 960589 1080769 := bbase (se 2 (by rfl) ⟨405288, by rfl⟩ : syracuseStep 1080769 = 810577) (by norm_num)
theorem B1441229 : Blo 960589 1441229 := bbase (se 3 (by rfl) ⟨270230, by rfl⟩ : syracuseStep 1441229 = 540461) (by norm_num)
theorem B8224213 : Blo 960589 8224213 := bbase (se 7 (by rfl) ⟨96377, by rfl⟩ : syracuseStep 8224213 = 192755) (by norm_num)
theorem B2162141 : Blo 960589 2162141 := bbase (se 3 (by rfl) ⟨405401, by rfl⟩ : syracuseStep 2162141 = 810803) (by norm_num)
theorem B1080805 : Blo 960589 1080805 := bbase (se 4 (by rfl) ⟨101325, by rfl⟩ : syracuseStep 1080805 = 202651) (by norm_num)
theorem B1441253 : Blo 960589 1441253 := bbase (se 4 (by rfl) ⟨135117, by rfl⟩ : syracuseStep 1441253 = 270235) (by norm_num)
theorem B3243509 : Blo 960589 3243509 := bbase (se 5 (by rfl) ⟨152039, by rfl⟩ : syracuseStep 3243509 = 304079) (by norm_num)
theorem B1441277 : Blo 960589 1441277 := bbase (se 3 (by rfl) ⟨270239, by rfl⟩ : syracuseStep 1441277 = 540479) (by norm_num)
theorem B1080841 : Blo 960589 1080841 := bbase (se 2 (by rfl) ⟨405315, by rfl⟩ : syracuseStep 1080841 = 810631) (by norm_num)
theorem B1441301 : Blo 960589 1441301 := bbase (se 6 (by rfl) ⟨33780, by rfl⟩ : syracuseStep 1441301 = 67561) (by norm_num)
theorem B2162213 : Blo 960589 2162213 := bbase (se 4 (by rfl) ⟨202707, by rfl⟩ : syracuseStep 2162213 = 405415) (by norm_num)
theorem B1080877 : Blo 960589 1080877 := bbase (se 3 (by rfl) ⟨202664, by rfl⟩ : syracuseStep 1080877 = 405329) (by norm_num)
theorem B1441325 : Blo 960589 1441325 := bbase (se 3 (by rfl) ⟨270248, by rfl⟩ : syracuseStep 1441325 = 540497) (by norm_num)
theorem B1441349 : Blo 960589 1441349 := bbase (se 4 (by rfl) ⟨135126, by rfl⟩ : syracuseStep 1441349 = 270253) (by norm_num)
theorem B1080913 : Blo 960589 1080913 := bbase (se 2 (by rfl) ⟨405342, by rfl⟩ : syracuseStep 1080913 = 810685) (by norm_num)
theorem B1441373 : Blo 960589 1441373 := bbase (se 3 (by rfl) ⟨270257, by rfl⟩ : syracuseStep 1441373 = 540515) (by norm_num)
theorem B2162285 : Blo 960589 2162285 := bbase (se 3 (by rfl) ⟨405428, by rfl⟩ : syracuseStep 2162285 = 810857) (by norm_num)
theorem B1080949 : Blo 960589 1080949 := bbase (se 5 (by rfl) ⟨50669, by rfl⟩ : syracuseStep 1080949 = 101339) (by norm_num)
theorem B1441397 : Blo 960589 1441397 := bbase (se 5 (by rfl) ⟨67565, by rfl⟩ : syracuseStep 1441397 = 135131) (by norm_num)
theorem B1441421 : Blo 960589 1441421 := bbase (se 3 (by rfl) ⟨270266, by rfl⟩ : syracuseStep 1441421 = 540533) (by norm_num)
theorem B1080985 : Blo 960589 1080985 := bbase (se 2 (by rfl) ⟨405369, by rfl⟩ : syracuseStep 1080985 = 810739) (by norm_num)
theorem B1441445 : Blo 960589 1441445 := bbase (se 4 (by rfl) ⟨135135, by rfl⟩ : syracuseStep 1441445 = 270271) (by norm_num)
theorem B2162357 : Blo 960589 2162357 := bbase (se 5 (by rfl) ⟨101360, by rfl⟩ : syracuseStep 2162357 = 202721) (by norm_num)
theorem B1081021 : Blo 960589 1081021 := bbase (se 3 (by rfl) ⟨202691, by rfl⟩ : syracuseStep 1081021 = 405383) (by norm_num)
theorem B1441469 : Blo 960589 1441469 := bbase (se 3 (by rfl) ⟨270275, by rfl⟩ : syracuseStep 1441469 = 540551) (by norm_num)
theorem B1441493 : Blo 960589 1441493 := bbase (se 7 (by rfl) ⟨16892, by rfl⟩ : syracuseStep 1441493 = 33785) (by norm_num)
theorem B1081057 : Blo 960589 1081057 := bbase (se 2 (by rfl) ⟨405396, by rfl⟩ : syracuseStep 1081057 = 810793) (by norm_num)
theorem B1441517 : Blo 960589 1441517 := bbase (se 3 (by rfl) ⟨270284, by rfl⟩ : syracuseStep 1441517 = 540569) (by norm_num)
theorem B2162429 : Blo 960589 2162429 := bbase (se 3 (by rfl) ⟨405455, by rfl⟩ : syracuseStep 2162429 = 810911) (by norm_num)
theorem B1081093 : Blo 960589 1081093 := bbase (se 4 (by rfl) ⟨101352, by rfl⟩ : syracuseStep 1081093 = 202705) (by norm_num)
theorem B1441541 : Blo 960589 1441541 := bbase (se 4 (by rfl) ⟨135144, by rfl⟩ : syracuseStep 1441541 = 270289) (by norm_num)
theorem B1736461 : Blo 960589 1736461 := bbase (se 3 (by rfl) ⟨325586, by rfl⟩ : syracuseStep 1736461 = 651173) (by norm_num)
theorem B1441565 : Blo 960589 1441565 := bbase (se 3 (by rfl) ⟨270293, by rfl⟩ : syracuseStep 1441565 = 540587) (by norm_num)
theorem B1081129 : Blo 960589 1081129 := bbase (se 2 (by rfl) ⟨405423, by rfl⟩ : syracuseStep 1081129 = 810847) (by norm_num)
theorem B1441589 : Blo 960589 1441589 := bbase (se 5 (by rfl) ⟨67574, by rfl⟩ : syracuseStep 1441589 = 135149) (by norm_num)
theorem B1539901 : Blo 960589 1539901 := bbase (se 3 (by rfl) ⟨288731, by rfl⟩ : syracuseStep 1539901 = 577463) (by norm_num)
theorem B2162501 : Blo 960589 2162501 := bbase (se 4 (by rfl) ⟨202734, by rfl⟩ : syracuseStep 2162501 = 405469) (by norm_num)
theorem B1081165 : Blo 960589 1081165 := bbase (se 3 (by rfl) ⟨202718, by rfl⟩ : syracuseStep 1081165 = 405437) (by norm_num)
theorem B1441613 : Blo 960589 1441613 := bbase (se 3 (by rfl) ⟨270302, by rfl⟩ : syracuseStep 1441613 = 540605) (by norm_num)
theorem B3702613 : Blo 960589 3702613 := bbase (se 9 (by rfl) ⟨10847, by rfl⟩ : syracuseStep 3702613 = 21695) (by norm_num)
theorem B1441637 : Blo 960589 1441637 := bbase (se 4 (by rfl) ⟨135153, by rfl⟩ : syracuseStep 1441637 = 270307) (by norm_num)
theorem B1081201 : Blo 960589 1081201 := bbase (se 2 (by rfl) ⟨405450, by rfl⟩ : syracuseStep 1081201 = 810901) (by norm_num)
theorem B1441661 : Blo 960589 1441661 := bbase (se 3 (by rfl) ⟨270311, by rfl⟩ : syracuseStep 1441661 = 540623) (by norm_num)
theorem B1539965 : Blo 960589 1539965 := bbase (se 3 (by rfl) ⟨288743, by rfl⟩ : syracuseStep 1539965 = 577487) (by norm_num)
theorem B2162573 : Blo 960589 2162573 := bbase (se 3 (by rfl) ⟨405482, by rfl⟩ : syracuseStep 2162573 = 810965) (by norm_num)
theorem B1081237 : Blo 960589 1081237 := bbase (se 6 (by rfl) ⟨25341, by rfl⟩ : syracuseStep 1081237 = 50683) (by norm_num)
theorem B1441685 : Blo 960589 1441685 := bbase (se 6 (by rfl) ⟨33789, by rfl⟩ : syracuseStep 1441685 = 67579) (by norm_num)
theorem B3243941 : Blo 960589 3243941 := bbase (se 4 (by rfl) ⟨304119, by rfl⟩ : syracuseStep 3243941 = 608239) (by norm_num)
theorem B1441709 : Blo 960589 1441709 := bbase (se 3 (by rfl) ⟨270320, by rfl⟩ : syracuseStep 1441709 = 540641) (by norm_num)
theorem B1081273 : Blo 960589 1081273 := bbase (se 2 (by rfl) ⟨405477, by rfl⟩ : syracuseStep 1081273 = 810955) (by norm_num)
theorem B1441733 : Blo 960589 1441733 := bbase (se 4 (by rfl) ⟨135162, by rfl⟩ : syracuseStep 1441733 = 270325) (by norm_num)
theorem B3702725 : Blo 960589 3702725 := bbase (se 4 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 3702725 = 694261) (by norm_num)
theorem B2162645 : Blo 960589 2162645 := bbase (se 7 (by rfl) ⟨25343, by rfl⟩ : syracuseStep 2162645 = 50687) (by norm_num)
theorem B1081309 : Blo 960589 1081309 := bbase (se 3 (by rfl) ⟨202745, by rfl⟩ : syracuseStep 1081309 = 405491) (by norm_num)
theorem B1441757 : Blo 960589 1441757 := bbase (se 3 (by rfl) ⟨270329, by rfl⟩ : syracuseStep 1441757 = 540659) (by norm_num)
theorem B1441781 : Blo 960589 1441781 := bbase (se 5 (by rfl) ⟨67583, by rfl⟩ : syracuseStep 1441781 = 135167) (by norm_num)
theorem B4620277 : Blo 960589 4620277 := bbase (se 5 (by rfl) ⟨216575, by rfl⟩ : syracuseStep 4620277 = 433151) (by norm_num)
theorem B1441793 : Blo 960589 1441793 := bstep (se 2 (by rfl) ⟨540672, by rfl⟩ : syracuseStep 1441793 = 1081345) B1081345
theorem B3244049 : Blo 960589 3244049 := bstep (se 2 (by rfl) ⟨1216518, by rfl⟩ : syracuseStep 3244049 = 2433037) B2433037
theorem B1441811 : Blo 960589 1441811 := bstep (se 1 (by rfl) ⟨1081358, by rfl⟩ : syracuseStep 1441811 = 2162717) B2162717
theorem B1081363 : Blo 960589 1081363 := bstep (se 1 (by rfl) ⟨811022, by rfl⟩ : syracuseStep 1081363 = 1622045) B1622045
theorem B1441841 : Blo 960589 1441841 := bstep (se 2 (by rfl) ⟨540690, by rfl⟩ : syracuseStep 1441841 = 1081381) B1081381
theorem B1441859 : Blo 960589 1441859 := bstep (se 1 (by rfl) ⟨1081394, by rfl⟩ : syracuseStep 1441859 = 2162789) B2162789
theorem B1441889 : Blo 960589 1441889 := bstep (se 2 (by rfl) ⟨540708, by rfl⟩ : syracuseStep 1441889 = 1081417) B1081417
theorem B1441907 : Blo 960589 1441907 := bstep (se 1 (by rfl) ⟨1081430, by rfl⟩ : syracuseStep 1441907 = 2162861) B2162861
theorem B1441937 : Blo 960589 1441937 := bstep (se 2 (by rfl) ⟨540726, by rfl⟩ : syracuseStep 1441937 = 1081453) B1081453
theorem B1441955 : Blo 960589 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B1081507 : Blo 960589 1081507 := bstep (se 1 (by rfl) ⟨811130, by rfl⟩ : syracuseStep 1081507 = 1622261) B1622261
theorem B1441985 : Blo 960589 1441985 := bstep (se 2 (by rfl) ⟨540744, by rfl⟩ : syracuseStep 1441985 = 1081489) B1081489
theorem B2162897 : Blo 960589 2162897 := bstep (se 2 (by rfl) ⟨811086, by rfl⟩ : syracuseStep 2162897 = 1622173) B1622173
theorem B1442003 : Blo 960589 1442003 := bstep (se 1 (by rfl) ⟨1081502, by rfl⟩ : syracuseStep 1442003 = 2163005) B2163005
theorem B2162915 : Blo 960589 2162915 := bstep (se 1 (by rfl) ⟨1622186, by rfl⟩ : syracuseStep 2162915 = 3244373) B3244373
theorem B1442033 : Blo 960589 1442033 := bstep (se 2 (by rfl) ⟨540762, by rfl⟩ : syracuseStep 1442033 = 1081525) B1081525
theorem B1442051 : Blo 960589 1442051 := bstep (se 1 (by rfl) ⟨1081538, by rfl⟩ : syracuseStep 1442051 = 2163077) B2163077
theorem B1442081 : Blo 960589 1442081 := bstep (se 2 (by rfl) ⟨540780, by rfl⟩ : syracuseStep 1442081 = 1081561) B1081561
theorem B1442099 : Blo 960589 1442099 := bstep (se 1 (by rfl) ⟨1081574, by rfl⟩ : syracuseStep 1442099 = 2163149) B2163149
theorem B1081651 : Blo 960589 1081651 := bstep (se 1 (by rfl) ⟨811238, by rfl⟩ : syracuseStep 1081651 = 1622477) B1622477
theorem B1442129 : Blo 960589 1442129 := bstep (se 2 (by rfl) ⟨540798, by rfl⟩ : syracuseStep 1442129 = 1081597) B1081597
theorem B1442147 : Blo 960589 1442147 := bstep (se 1 (by rfl) ⟨1081610, by rfl⟩ : syracuseStep 1442147 = 2163221) B2163221
theorem B1737059 : Blo 960589 1737059 := bstep (se 1 (by rfl) ⟨1302794, by rfl⟩ : syracuseStep 1737059 = 2605589) B2605589
theorem B1442177 : Blo 960589 1442177 := bstep (se 2 (by rfl) ⟨540816, by rfl⟩ : syracuseStep 1442177 = 1081633) B1081633
theorem B1442195 : Blo 960589 1442195 := bstep (se 1 (by rfl) ⟨1081646, by rfl⟩ : syracuseStep 1442195 = 2163293) B2163293
theorem B1442225 : Blo 960589 1442225 := bstep (se 2 (by rfl) ⟨540834, by rfl⟩ : syracuseStep 1442225 = 1081669) B1081669
theorem B4620721 : Blo 960589 4620721 := bstep (se 2 (by rfl) ⟨1732770, by rfl⟩ : syracuseStep 4620721 = 3465541) B3465541
theorem B1540529 : Blo 960589 1540529 := bstep (se 2 (by rfl) ⟨577698, by rfl⟩ : syracuseStep 1540529 = 1155397) B1155397
theorem B1442243 : Blo 960589 1442243 := bstep (se 1 (by rfl) ⟨1081682, by rfl⟩ : syracuseStep 1442243 = 2163365) B2163365
theorem B1081795 : Blo 960589 1081795 := bstep (se 1 (by rfl) ⟨811346, by rfl⟩ : syracuseStep 1081795 = 1622693) B1622693
theorem B1442273 : Blo 960589 1442273 := bstep (se 2 (by rfl) ⟨540852, by rfl⟩ : syracuseStep 1442273 = 1081705) B1081705
theorem B2163185 : Blo 960589 2163185 := bstep (se 2 (by rfl) ⟨811194, by rfl⟩ : syracuseStep 2163185 = 1622389) B1622389
theorem B1442291 : Blo 960589 1442291 := bstep (se 1 (by rfl) ⟨1081718, by rfl⟩ : syracuseStep 1442291 = 2163437) B2163437
theorem B2163203 : Blo 960589 2163203 := bstep (se 1 (by rfl) ⟨1622402, by rfl⟩ : syracuseStep 2163203 = 3244805) B3244805
theorem B3899917 : Blo 960589 3899917 := bstep (se 3 (by rfl) ⟨731234, by rfl⟩ : syracuseStep 3899917 = 1462469) B1462469
theorem B1442321 : Blo 960589 1442321 := bstep (se 2 (by rfl) ⟨540870, by rfl⟩ : syracuseStep 1442321 = 1081741) B1081741
theorem B1442339 : Blo 960589 1442339 := bstep (se 1 (by rfl) ⟨1081754, by rfl⟩ : syracuseStep 1442339 = 2163509) B2163509
theorem B3244589 : Blo 960589 3244589 := bstep (se 3 (by rfl) ⟨608360, by rfl⟩ : syracuseStep 3244589 = 1216721) B1216721
theorem B3080749 : Blo 960589 3080749 := bstep (se 3 (by rfl) ⟨577640, by rfl⟩ : syracuseStep 3080749 = 1155281) B1155281
theorem B1442369 : Blo 960589 1442369 := bstep (se 2 (by rfl) ⟨540888, by rfl⟩ : syracuseStep 1442369 = 1081777) B1081777
theorem B1442387 : Blo 960589 1442387 := bstep (se 1 (by rfl) ⟨1081790, by rfl⟩ : syracuseStep 1442387 = 2163581) B2163581
theorem B1081939 : Blo 960589 1081939 := bstep (se 1 (by rfl) ⟨811454, by rfl⟩ : syracuseStep 1081939 = 1622909) B1622909
theorem B3244643 : Blo 960589 3244643 := bstep (se 1 (by rfl) ⟨2433482, by rfl⟩ : syracuseStep 3244643 = 4866965) B4866965
theorem B1442417 : Blo 960589 1442417 := bstep (se 2 (by rfl) ⟨540906, by rfl⟩ : syracuseStep 1442417 = 1081813) B1081813
theorem B1540721 : Blo 960589 1540721 := bstep (se 2 (by rfl) ⟨577770, by rfl⟩ : syracuseStep 1540721 = 1155541) B1155541
theorem B1442435 : Blo 960589 1442435 := bstep (se 1 (by rfl) ⟨1081826, by rfl⟩ : syracuseStep 1442435 = 2163653) B2163653
theorem B1442465 : Blo 960589 1442465 := bstep (se 2 (by rfl) ⟨540924, by rfl⟩ : syracuseStep 1442465 = 1081849) B1081849
theorem B1442483 : Blo 960589 1442483 := bstep (se 1 (by rfl) ⟨1081862, by rfl⟩ : syracuseStep 1442483 = 2163725) B2163725
theorem B10945205 : Blo 960589 10945205 := bstep (se 5 (by rfl) ⟨513056, by rfl⟩ : syracuseStep 10945205 = 1026113) B1026113
theorem B1442513 : Blo 960589 1442513 := bstep (se 2 (by rfl) ⟨540942, by rfl⟩ : syracuseStep 1442513 = 1081885) B1081885
theorem B1442531 : Blo 960589 1442531 := bstep (se 1 (by rfl) ⟨1081898, by rfl⟩ : syracuseStep 1442531 = 2163797) B2163797
theorem B1082083 : Blo 960589 1082083 := bstep (se 1 (by rfl) ⟨811562, by rfl⟩ : syracuseStep 1082083 = 1623125) B1623125
theorem B1442561 : Blo 960589 1442561 := bstep (se 2 (by rfl) ⟨540960, by rfl⟩ : syracuseStep 1442561 = 1081921) B1081921
theorem B8225549 : Blo 960589 8225549 := bstep (se 3 (by rfl) ⟨1542290, by rfl⟩ : syracuseStep 8225549 = 3084581) B3084581
theorem B2163473 : Blo 960589 2163473 := bstep (se 2 (by rfl) ⟨811302, by rfl⟩ : syracuseStep 2163473 = 1622605) B1622605
theorem B1442579 : Blo 960589 1442579 := bstep (se 1 (by rfl) ⟨1081934, by rfl⟩ : syracuseStep 1442579 = 2163869) B2163869
theorem B2163491 : Blo 960589 2163491 := bstep (se 1 (by rfl) ⟨1622618, by rfl⟩ : syracuseStep 2163491 = 3245237) B3245237
theorem B3081005 : Blo 960589 3081005 := bstep (se 3 (by rfl) ⟨577688, by rfl⟩ : syracuseStep 3081005 = 1155377) B1155377
theorem B1442609 : Blo 960589 1442609 := bstep (se 2 (by rfl) ⟨540978, by rfl⟩ : syracuseStep 1442609 = 1081957) B1081957
theorem B1737521 : Blo 960589 1737521 := bstep (se 2 (by rfl) ⟨651570, by rfl⟩ : syracuseStep 1737521 = 1303141) B1303141
theorem B1442627 : Blo 960589 1442627 := bstep (se 1 (by rfl) ⟨1081970, by rfl⟩ : syracuseStep 1442627 = 2163941) B2163941
theorem B1442657 : Blo 960589 1442657 := bstep (se 2 (by rfl) ⟨540996, by rfl⟩ : syracuseStep 1442657 = 1081993) B1081993
theorem B3244913 : Blo 960589 3244913 := bstep (se 2 (by rfl) ⟨1216842, by rfl⟩ : syracuseStep 3244913 = 2433685) B2433685
theorem B1409905 : Blo 960589 1409905 := bstep (se 2 (by rfl) ⟨528714, by rfl⟩ : syracuseStep 1409905 = 1057429) B1057429
theorem B1442675 : Blo 960589 1442675 := bstep (se 1 (by rfl) ⟨1082006, by rfl⟩ : syracuseStep 1442675 = 2164013) B2164013
theorem B1082227 : Blo 960589 1082227 := bstep (se 1 (by rfl) ⟨811670, by rfl⟩ : syracuseStep 1082227 = 1623341) B1623341
theorem B1442705 : Blo 960589 1442705 := bstep (se 2 (by rfl) ⟨541014, by rfl⟩ : syracuseStep 1442705 = 1082029) B1082029
theorem B1442723 : Blo 960589 1442723 := bstep (se 1 (by rfl) ⟨1082042, by rfl⟩ : syracuseStep 1442723 = 2164085) B2164085
theorem B1442753 : Blo 960589 1442753 := bstep (se 2 (by rfl) ⟨541032, by rfl⟩ : syracuseStep 1442753 = 1082065) B1082065
theorem B1442771 : Blo 960589 1442771 := bstep (se 1 (by rfl) ⟨1082078, by rfl⟩ : syracuseStep 1442771 = 2164157) B2164157
theorem B1442801 : Blo 960589 1442801 := bstep (se 2 (by rfl) ⟨541050, by rfl⟩ : syracuseStep 1442801 = 1082101) B1082101
theorem B1442819 : Blo 960589 1442819 := bstep (se 1 (by rfl) ⟨1082114, by rfl⟩ : syracuseStep 1442819 = 2164229) B2164229
theorem B1082371 : Blo 960589 1082371 := bstep (se 1 (by rfl) ⟨811778, by rfl⟩ : syracuseStep 1082371 = 1623557) B1623557
theorem B1442849 : Blo 960589 1442849 := bstep (se 2 (by rfl) ⟨541068, by rfl⟩ : syracuseStep 1442849 = 1082137) B1082137
theorem B2163761 : Blo 960589 2163761 := bstep (se 2 (by rfl) ⟨811410, by rfl⟩ : syracuseStep 2163761 = 1622821) B1622821
theorem B1442867 : Blo 960589 1442867 := bstep (se 1 (by rfl) ⟨1082150, by rfl⟩ : syracuseStep 1442867 = 2164301) B2164301
theorem B16450613 : Blo 960589 16450613 := bstep (se 5 (by rfl) ⟨771122, by rfl⟩ : syracuseStep 16450613 = 1542245) B1542245
theorem B2163779 : Blo 960589 2163779 := bstep (se 1 (by rfl) ⟨1622834, by rfl⟩ : syracuseStep 2163779 = 3245669) B3245669
theorem B1442897 : Blo 960589 1442897 := bstep (se 2 (by rfl) ⟨541086, by rfl⟩ : syracuseStep 1442897 = 1082173) B1082173
theorem B1442915 : Blo 960589 1442915 := bstep (se 1 (by rfl) ⟨1082186, by rfl⟩ : syracuseStep 1442915 = 2164373) B2164373
theorem B1442945 : Blo 960589 1442945 := bstep (se 2 (by rfl) ⟨541104, by rfl⟩ : syracuseStep 1442945 = 1082209) B1082209
theorem B4392077 : Blo 960589 4392077 := bstep (se 3 (by rfl) ⟨823514, by rfl⟩ : syracuseStep 4392077 = 1647029) B1647029
theorem B1442963 : Blo 960589 1442963 := bstep (se 1 (by rfl) ⟨1082222, by rfl⟩ : syracuseStep 1442963 = 2164445) B2164445
theorem B1082515 : Blo 960589 1082515 := bstep (se 1 (by rfl) ⟨811886, by rfl⟩ : syracuseStep 1082515 = 1623773) B1623773
theorem B1442993 : Blo 960589 1442993 := bstep (se 2 (by rfl) ⟨541122, by rfl⟩ : syracuseStep 1442993 = 1082245) B1082245
theorem B1443011 : Blo 960589 1443011 := bstep (se 1 (by rfl) ⟨1082258, by rfl⟩ : syracuseStep 1443011 = 2164517) B2164517
theorem B1443041 : Blo 960589 1443041 := bstep (se 2 (by rfl) ⟨541140, by rfl⟩ : syracuseStep 1443041 = 1082281) B1082281
theorem B1443059 : Blo 960589 1443059 := bstep (se 1 (by rfl) ⟨1082294, by rfl⟩ : syracuseStep 1443059 = 2164589) B2164589
theorem B1443089 : Blo 960589 1443089 := bstep (se 2 (by rfl) ⟨541158, by rfl⟩ : syracuseStep 1443089 = 1082317) B1082317
theorem B1443107 : Blo 960589 1443107 := bstep (se 1 (by rfl) ⟨1082330, by rfl⟩ : syracuseStep 1443107 = 2164661) B2164661
theorem B1082659 : Blo 960589 1082659 := bstep (se 1 (by rfl) ⟨811994, by rfl⟩ : syracuseStep 1082659 = 1623989) B1623989
theorem B1443137 : Blo 960589 1443137 := bstep (se 2 (by rfl) ⟨541176, by rfl⟩ : syracuseStep 1443137 = 1082353) B1082353
theorem B2164049 : Blo 960589 2164049 := bstep (se 2 (by rfl) ⟨811518, by rfl⟩ : syracuseStep 2164049 = 1623037) B1623037
theorem B1443155 : Blo 960589 1443155 := bstep (se 1 (by rfl) ⟨1082366, by rfl⟩ : syracuseStep 1443155 = 2164733) B2164733
theorem B2164067 : Blo 960589 2164067 := bstep (se 1 (by rfl) ⟨1623050, by rfl⟩ : syracuseStep 2164067 = 3246101) B3246101
theorem B1443185 : Blo 960589 1443185 := bstep (se 2 (by rfl) ⟨541194, by rfl⟩ : syracuseStep 1443185 = 1082389) B1082389
theorem B1443203 : Blo 960589 1443203 := bstep (se 1 (by rfl) ⟨1082402, by rfl⟩ : syracuseStep 1443203 = 2164805) B2164805
theorem B3245453 : Blo 960589 3245453 := bstep (se 3 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 3245453 = 1217045) B1217045
theorem B1443233 : Blo 960589 1443233 := bstep (se 2 (by rfl) ⟨541212, by rfl⟩ : syracuseStep 1443233 = 1082425) B1082425
theorem B1443251 : Blo 960589 1443251 := bstep (se 1 (by rfl) ⟨1082438, by rfl⟩ : syracuseStep 1443251 = 2164877) B2164877
theorem B1082803 : Blo 960589 1082803 := bstep (se 1 (by rfl) ⟨812102, by rfl⟩ : syracuseStep 1082803 = 1624205) B1624205
theorem B3245507 : Blo 960589 3245507 := bstep (se 1 (by rfl) ⟨2434130, by rfl⟩ : syracuseStep 3245507 = 4868261) B4868261
theorem B1443281 : Blo 960589 1443281 := bstep (se 2 (by rfl) ⟨541230, by rfl⟩ : syracuseStep 1443281 = 1082461) B1082461
theorem B1443299 : Blo 960589 1443299 := bstep (se 1 (by rfl) ⟨1082474, by rfl⟩ : syracuseStep 1443299 = 2164949) B2164949
theorem B1443329 : Blo 960589 1443329 := bstep (se 2 (by rfl) ⟨541248, by rfl⟩ : syracuseStep 1443329 = 1082497) B1082497
theorem B1443347 : Blo 960589 1443347 := bstep (se 1 (by rfl) ⟨1082510, by rfl⟩ : syracuseStep 1443347 = 2165021) B2165021
theorem B20809237 : Blo 960589 20809237 := bstep (se 6 (by rfl) ⟨487716, by rfl⟩ : syracuseStep 20809237 = 975433) B975433
theorem B1443377 : Blo 960589 1443377 := bstep (se 2 (by rfl) ⟨541266, by rfl⟩ : syracuseStep 1443377 = 1082533) B1082533
theorem B1443395 : Blo 960589 1443395 := bstep (se 1 (by rfl) ⟨1082546, by rfl⟩ : syracuseStep 1443395 = 2165093) B2165093
theorem B1082947 : Blo 960589 1082947 := bstep (se 1 (by rfl) ⟨812210, by rfl⟩ : syracuseStep 1082947 = 1624421) B1624421
theorem B9864773 : Blo 960589 9864773 := bstep (se 4 (by rfl) ⟨924822, by rfl⟩ : syracuseStep 9864773 = 1849645) B1849645
theorem B1443425 : Blo 960589 1443425 := bstep (se 2 (by rfl) ⟨541284, by rfl⟩ : syracuseStep 1443425 = 1082569) B1082569
theorem B2164337 : Blo 960589 2164337 := bstep (se 2 (by rfl) ⟨811626, by rfl⟩ : syracuseStep 2164337 = 1623253) B1623253
theorem B1443443 : Blo 960589 1443443 := bstep (se 1 (by rfl) ⟨1082582, by rfl⟩ : syracuseStep 1443443 = 2165165) B2165165
theorem B2164355 : Blo 960589 2164355 := bstep (se 1 (by rfl) ⟨1623266, by rfl⟩ : syracuseStep 2164355 = 3246533) B3246533
theorem B5473925 : Blo 960589 5473925 := bstep (se 4 (by rfl) ⟨513180, by rfl⟩ : syracuseStep 5473925 = 1026361) B1026361
theorem B1443473 : Blo 960589 1443473 := bstep (se 2 (by rfl) ⟨541302, by rfl⟩ : syracuseStep 1443473 = 1082605) B1082605
theorem B1443491 : Blo 960589 1443491 := bstep (se 1 (by rfl) ⟨1082618, by rfl⟩ : syracuseStep 1443491 = 2165237) B2165237
theorem B1443521 : Blo 960589 1443521 := bstep (se 2 (by rfl) ⟨541320, by rfl⟩ : syracuseStep 1443521 = 1082641) B1082641
theorem B3245777 : Blo 960589 3245777 := bstep (se 2 (by rfl) ⟨1217166, by rfl⟩ : syracuseStep 3245777 = 2434333) B2434333
theorem B1443539 : Blo 960589 1443539 := bstep (se 1 (by rfl) ⟨1082654, by rfl⟩ : syracuseStep 1443539 = 2165309) B2165309
theorem B1083091 : Blo 960589 1083091 := bstep (se 1 (by rfl) ⟨812318, by rfl⟩ : syracuseStep 1083091 = 1624637) B1624637
theorem B1443569 : Blo 960589 1443569 := bstep (se 2 (by rfl) ⟨541338, by rfl⟩ : syracuseStep 1443569 = 1082677) B1082677
theorem B1443587 : Blo 960589 1443587 := bstep (se 1 (by rfl) ⟨1082690, by rfl⟩ : syracuseStep 1443587 = 2165381) B2165381
theorem B1443617 : Blo 960589 1443617 := bstep (se 2 (by rfl) ⟨541356, by rfl⟩ : syracuseStep 1443617 = 1082713) B1082713
theorem B1443635 : Blo 960589 1443635 := bstep (se 1 (by rfl) ⟨1082726, by rfl⟩ : syracuseStep 1443635 = 2165453) B2165453
theorem B1443665 : Blo 960589 1443665 := bstep (se 2 (by rfl) ⟨541374, by rfl⟩ : syracuseStep 1443665 = 1082749) B1082749
theorem B1443683 : Blo 960589 1443683 := bstep (se 1 (by rfl) ⟨1082762, by rfl⟩ : syracuseStep 1443683 = 2165525) B2165525
theorem B1083235 : Blo 960589 1083235 := bstep (se 1 (by rfl) ⟨812426, by rfl⟩ : syracuseStep 1083235 = 1624853) B1624853
theorem B1443713 : Blo 960589 1443713 := bstep (se 2 (by rfl) ⟨541392, by rfl⟩ : syracuseStep 1443713 = 1082785) B1082785
theorem B2164625 : Blo 960589 2164625 := bstep (se 2 (by rfl) ⟨811734, by rfl⟩ : syracuseStep 2164625 = 1623469) B1623469
theorem B1443731 : Blo 960589 1443731 := bstep (se 1 (by rfl) ⟨1082798, by rfl⟩ : syracuseStep 1443731 = 2165597) B2165597
theorem B2164643 : Blo 960589 2164643 := bstep (se 1 (by rfl) ⟨1623482, by rfl⟩ : syracuseStep 2164643 = 3246965) B3246965
theorem B1443761 : Blo 960589 1443761 := bstep (se 2 (by rfl) ⟨541410, by rfl⟩ : syracuseStep 1443761 = 1082821) B1082821
theorem B1443779 : Blo 960589 1443779 := bstep (se 1 (by rfl) ⟨1082834, by rfl⟩ : syracuseStep 1443779 = 2165669) B2165669
theorem B1443809 : Blo 960589 1443809 := bstep (se 2 (by rfl) ⟨541428, by rfl⟩ : syracuseStep 1443809 = 1082857) B1082857
theorem B1443827 : Blo 960589 1443827 := bstep (se 1 (by rfl) ⟨1082870, by rfl⟩ : syracuseStep 1443827 = 2165741) B2165741
theorem B1083379 : Blo 960589 1083379 := bstep (se 1 (by rfl) ⟨812534, by rfl⟩ : syracuseStep 1083379 = 1625069) B1625069
theorem B1443857 : Blo 960589 1443857 := bstep (se 2 (by rfl) ⟨541446, by rfl⟩ : syracuseStep 1443857 = 1082893) B1082893
theorem B1443875 : Blo 960589 1443875 := bstep (se 1 (by rfl) ⟨1082906, by rfl⟩ : syracuseStep 1443875 = 2165813) B2165813
theorem B1443905 : Blo 960589 1443905 := bstep (se 2 (by rfl) ⟨541464, by rfl⟩ : syracuseStep 1443905 = 1082929) B1082929
theorem B1443923 : Blo 960589 1443923 := bstep (se 1 (by rfl) ⟨1082942, by rfl⟩ : syracuseStep 1443923 = 2165885) B2165885
theorem B5212259 : Blo 960589 5212259 := bstep (se 1 (by rfl) ⟨3909194, by rfl⟩ : syracuseStep 5212259 = 7818389) B7818389
theorem B1443953 : Blo 960589 1443953 := bstep (se 2 (by rfl) ⟨541482, by rfl⟩ : syracuseStep 1443953 = 1082965) B1082965
theorem B1443971 : Blo 960589 1443971 := bstep (se 1 (by rfl) ⟨1082978, by rfl⟩ : syracuseStep 1443971 = 2165957) B2165957
theorem B1083523 : Blo 960589 1083523 := bstep (se 1 (by rfl) ⟨812642, by rfl⟩ : syracuseStep 1083523 = 1625285) B1625285
theorem B1444001 : Blo 960589 1444001 := bstep (se 2 (by rfl) ⟨541500, by rfl⟩ : syracuseStep 1444001 = 1083001) B1083001
theorem B2164913 : Blo 960589 2164913 := bstep (se 2 (by rfl) ⟨811842, by rfl⟩ : syracuseStep 2164913 = 1623685) B1623685
theorem B1444019 : Blo 960589 1444019 := bstep (se 1 (by rfl) ⟨1083014, by rfl⟩ : syracuseStep 1444019 = 2166029) B2166029
theorem B1542323 : Blo 960589 1542323 := bstep (se 1 (by rfl) ⟨1156742, by rfl⟩ : syracuseStep 1542323 = 2313485) B2313485
theorem B2164931 : Blo 960589 2164931 := bstep (se 1 (by rfl) ⟨1623698, by rfl⟩ : syracuseStep 2164931 = 3247397) B3247397
theorem B1444049 : Blo 960589 1444049 := bstep (se 2 (by rfl) ⟨541518, by rfl⟩ : syracuseStep 1444049 = 1083037) B1083037
theorem B1444067 : Blo 960589 1444067 := bstep (se 1 (by rfl) ⟨1083050, by rfl⟩ : syracuseStep 1444067 = 2166101) B2166101
theorem B3246317 : Blo 960589 3246317 := bstep (se 3 (by rfl) ⟨608684, by rfl⟩ : syracuseStep 3246317 = 1217369) B1217369
theorem B1444097 : Blo 960589 1444097 := bstep (se 2 (by rfl) ⟨541536, by rfl⟩ : syracuseStep 1444097 = 1083073) B1083073
theorem B1444115 : Blo 960589 1444115 := bstep (se 1 (by rfl) ⟨1083086, by rfl⟩ : syracuseStep 1444115 = 2166173) B2166173
theorem B1083667 : Blo 960589 1083667 := bstep (se 1 (by rfl) ⟨812750, by rfl⟩ : syracuseStep 1083667 = 1625501) B1625501
theorem B3246371 : Blo 960589 3246371 := bstep (se 1 (by rfl) ⟨2434778, by rfl⟩ : syracuseStep 3246371 = 4869557) B4869557
theorem B3082531 : Blo 960589 3082531 := bstep (se 1 (by rfl) ⟨2311898, by rfl⟩ : syracuseStep 3082531 = 4623797) B4623797
theorem B1444145 : Blo 960589 1444145 := bstep (se 2 (by rfl) ⟨541554, by rfl⟩ : syracuseStep 1444145 = 1083109) B1083109
theorem B1444163 : Blo 960589 1444163 := bstep (se 1 (by rfl) ⟨1083122, by rfl⟩ : syracuseStep 1444163 = 2166245) B2166245
theorem B1444193 : Blo 960589 1444193 := bstep (se 2 (by rfl) ⟨541572, by rfl⟩ : syracuseStep 1444193 = 1083145) B1083145
theorem B1444211 : Blo 960589 1444211 := bstep (se 1 (by rfl) ⟨1083158, by rfl⟩ : syracuseStep 1444211 = 2166317) B2166317
theorem B1444241 : Blo 960589 1444241 := bstep (se 2 (by rfl) ⟨541590, by rfl⟩ : syracuseStep 1444241 = 1083181) B1083181
theorem B1444259 : Blo 960589 1444259 := bstep (se 1 (by rfl) ⟨1083194, by rfl⟩ : syracuseStep 1444259 = 2166389) B2166389
theorem B1083811 : Blo 960589 1083811 := bstep (se 1 (by rfl) ⟨812858, by rfl⟩ : syracuseStep 1083811 = 1625717) B1625717
theorem B2197937 : Blo 960589 2197937 := bstep (se 2 (by rfl) ⟨824226, by rfl⟩ : syracuseStep 2197937 = 1648453) B1648453
theorem B1444289 : Blo 960589 1444289 := bstep (se 2 (by rfl) ⟨541608, by rfl⟩ : syracuseStep 1444289 = 1083217) B1083217
theorem B2165201 : Blo 960589 2165201 := bstep (se 2 (by rfl) ⟨811950, by rfl⟩ : syracuseStep 2165201 = 1623901) B1623901
theorem B1444307 : Blo 960589 1444307 := bstep (se 1 (by rfl) ⟨1083230, by rfl⟩ : syracuseStep 1444307 = 2166461) B2166461
theorem B2165219 : Blo 960589 2165219 := bstep (se 1 (by rfl) ⟨1623914, by rfl⟩ : syracuseStep 2165219 = 3247829) B3247829
theorem B1444337 : Blo 960589 1444337 := bstep (se 2 (by rfl) ⟨541626, by rfl⟩ : syracuseStep 1444337 = 1083253) B1083253
theorem B1444355 : Blo 960589 1444355 := bstep (se 1 (by rfl) ⟨1083266, by rfl⟩ : syracuseStep 1444355 = 2166533) B2166533
theorem B1444385 : Blo 960589 1444385 := bstep (se 2 (by rfl) ⟨541644, by rfl⟩ : syracuseStep 1444385 = 1083289) B1083289
theorem B3246641 : Blo 960589 3246641 := bstep (se 2 (by rfl) ⟨1217490, by rfl⟩ : syracuseStep 3246641 = 2434981) B2434981
theorem B1444403 : Blo 960589 1444403 := bstep (se 1 (by rfl) ⟨1083302, by rfl⟩ : syracuseStep 1444403 = 2166605) B2166605
theorem B1542707 : Blo 960589 1542707 := bstep (se 1 (by rfl) ⟨1157030, by rfl⟩ : syracuseStep 1542707 = 2314061) B2314061
theorem B1083955 : Blo 960589 1083955 := bstep (se 1 (by rfl) ⟨812966, by rfl⟩ : syracuseStep 1083955 = 1625933) B1625933
theorem B1444433 : Blo 960589 1444433 := bstep (se 2 (by rfl) ⟨541662, by rfl⟩ : syracuseStep 1444433 = 1083325) B1083325
theorem B1444451 : Blo 960589 1444451 := bstep (se 1 (by rfl) ⟨1083338, by rfl⟩ : syracuseStep 1444451 = 2166677) B2166677
theorem B1444481 : Blo 960589 1444481 := bstep (se 2 (by rfl) ⟨541680, by rfl⟩ : syracuseStep 1444481 = 1083361) B1083361
theorem B11864717 : Blo 960589 11864717 := bstep (se 3 (by rfl) ⟨2224634, by rfl⟩ : syracuseStep 11864717 = 4449269) B4449269
theorem B1444499 : Blo 960589 1444499 := bstep (se 1 (by rfl) ⟨1083374, by rfl⟩ : syracuseStep 1444499 = 2166749) B2166749
theorem B1444529 : Blo 960589 1444529 := bstep (se 2 (by rfl) ⟨541698, by rfl⟩ : syracuseStep 1444529 = 1083397) B1083397
theorem B1542835 : Blo 960589 1542835 := bstep (se 1 (by rfl) ⟨1157126, by rfl⟩ : syracuseStep 1542835 = 2314253) B2314253
theorem B1444547 : Blo 960589 1444547 := bstep (se 1 (by rfl) ⟨1083410, by rfl⟩ : syracuseStep 1444547 = 2166821) B2166821
theorem B1084099 : Blo 960589 1084099 := bstep (se 1 (by rfl) ⟨813074, by rfl⟩ : syracuseStep 1084099 = 1626149) B1626149
theorem B1444577 : Blo 960589 1444577 := bstep (se 2 (by rfl) ⟨541716, by rfl⟩ : syracuseStep 1444577 = 1083433) B1083433
theorem B2165489 : Blo 960589 2165489 := bstep (se 2 (by rfl) ⟨812058, by rfl⟩ : syracuseStep 2165489 = 1624117) B1624117
theorem B1444595 : Blo 960589 1444595 := bstep (se 1 (by rfl) ⟨1083446, by rfl⟩ : syracuseStep 1444595 = 2166893) B2166893
theorem B2165507 : Blo 960589 2165507 := bstep (se 1 (by rfl) ⟨1624130, by rfl⟩ : syracuseStep 2165507 = 3248261) B3248261
theorem B1444625 : Blo 960589 1444625 := bstep (se 2 (by rfl) ⟨541734, by rfl⟩ : syracuseStep 1444625 = 1083469) B1083469
theorem B1444643 : Blo 960589 1444643 := bstep (se 1 (by rfl) ⟨1083482, by rfl⟩ : syracuseStep 1444643 = 2166965) B2166965
theorem B1444673 : Blo 960589 1444673 := bstep (se 2 (by rfl) ⟨541752, by rfl⟩ : syracuseStep 1444673 = 1083505) B1083505
theorem B1444691 : Blo 960589 1444691 := bstep (se 1 (by rfl) ⟨1083518, by rfl⟩ : syracuseStep 1444691 = 2167037) B2167037
theorem B1084243 : Blo 960589 1084243 := bstep (se 1 (by rfl) ⟨813182, by rfl⟩ : syracuseStep 1084243 = 1626365) B1626365
theorem B1444721 : Blo 960589 1444721 := bstep (se 2 (by rfl) ⟨541770, by rfl⟩ : syracuseStep 1444721 = 1083541) B1083541
theorem B1444739 : Blo 960589 1444739 := bstep (se 1 (by rfl) ⟨1083554, by rfl⟩ : syracuseStep 1444739 = 2167109) B2167109
theorem B1444769 : Blo 960589 1444769 := bstep (se 2 (by rfl) ⟨541788, by rfl⟩ : syracuseStep 1444769 = 1083577) B1083577
theorem B1444787 : Blo 960589 1444787 := bstep (se 1 (by rfl) ⟨1083590, by rfl⟩ : syracuseStep 1444787 = 2167181) B2167181
theorem B1444817 : Blo 960589 1444817 := bstep (se 2 (by rfl) ⟨541806, by rfl⟩ : syracuseStep 1444817 = 1083613) B1083613
theorem B1444835 : Blo 960589 1444835 := bstep (se 1 (by rfl) ⟨1083626, by rfl⟩ : syracuseStep 1444835 = 2167253) B2167253
theorem B1084387 : Blo 960589 1084387 := bstep (se 1 (by rfl) ⟨813290, by rfl⟩ : syracuseStep 1084387 = 1626581) B1626581
theorem B1444865 : Blo 960589 1444865 := bstep (se 2 (by rfl) ⟨541824, by rfl⟩ : syracuseStep 1444865 = 1083649) B1083649
theorem B2165777 : Blo 960589 2165777 := bstep (se 2 (by rfl) ⟨812166, by rfl⟩ : syracuseStep 2165777 = 1624333) B1624333
theorem B1444883 : Blo 960589 1444883 := bstep (se 1 (by rfl) ⟨1083662, by rfl⟩ : syracuseStep 1444883 = 2167325) B2167325
theorem B2165795 : Blo 960589 2165795 := bstep (se 1 (by rfl) ⟨1624346, by rfl⟩ : syracuseStep 2165795 = 3248693) B3248693
theorem B1444913 : Blo 960589 1444913 := bstep (se 2 (by rfl) ⟨541842, by rfl⟩ : syracuseStep 1444913 = 1083685) B1083685
theorem B1444931 : Blo 960589 1444931 := bstep (se 1 (by rfl) ⟨1083698, by rfl⟩ : syracuseStep 1444931 = 2167397) B2167397
theorem B3247181 : Blo 960589 3247181 := bstep (se 3 (by rfl) ⟨608846, by rfl⟩ : syracuseStep 3247181 = 1217693) B1217693
theorem B1444961 : Blo 960589 1444961 := bstep (se 2 (by rfl) ⟨541860, by rfl⟩ : syracuseStep 1444961 = 1083721) B1083721
theorem B3083363 : Blo 960589 3083363 := bstep (se 1 (by rfl) ⟨2312522, by rfl⟩ : syracuseStep 3083363 = 4625045) B4625045
theorem B1444979 : Blo 960589 1444979 := bstep (se 1 (by rfl) ⟨1083734, by rfl⟩ : syracuseStep 1444979 = 2167469) B2167469
theorem B1084531 : Blo 960589 1084531 := bstep (se 1 (by rfl) ⟨813398, by rfl⟩ : syracuseStep 1084531 = 1626797) B1626797
theorem B3247235 : Blo 960589 3247235 := bstep (se 1 (by rfl) ⟨2435426, by rfl⟩ : syracuseStep 3247235 = 4870853) B4870853
theorem B1445009 : Blo 960589 1445009 := bstep (se 2 (by rfl) ⟨541878, by rfl⟩ : syracuseStep 1445009 = 1083757) B1083757
theorem B1445027 : Blo 960589 1445027 := bstep (se 1 (by rfl) ⟨1083770, by rfl⟩ : syracuseStep 1445027 = 2167541) B2167541
theorem B1445057 : Blo 960589 1445057 := bstep (se 2 (by rfl) ⟨541896, by rfl⟩ : syracuseStep 1445057 = 1083793) B1083793
theorem B5213381 : Blo 960589 5213381 := bstep (se 4 (by rfl) ⟨488754, by rfl⟩ : syracuseStep 5213381 = 977509) B977509
theorem B1445075 : Blo 960589 1445075 := bstep (se 1 (by rfl) ⟨1083806, by rfl⟩ : syracuseStep 1445075 = 2167613) B2167613
theorem B1445105 : Blo 960589 1445105 := bstep (se 2 (by rfl) ⟨541914, by rfl⟩ : syracuseStep 1445105 = 1083829) B1083829
theorem B1445123 : Blo 960589 1445123 := bstep (se 1 (by rfl) ⟨1083842, by rfl⟩ : syracuseStep 1445123 = 2167685) B2167685
theorem B1084675 : Blo 960589 1084675 := bstep (se 1 (by rfl) ⟨813506, by rfl⟩ : syracuseStep 1084675 = 1627013) B1627013
theorem B1445153 : Blo 960589 1445153 := bstep (se 2 (by rfl) ⟨541932, by rfl⟩ : syracuseStep 1445153 = 1083865) B1083865
theorem B2166065 : Blo 960589 2166065 := bstep (se 2 (by rfl) ⟨812274, by rfl⟩ : syracuseStep 2166065 = 1624549) B1624549
theorem B1445171 : Blo 960589 1445171 := bstep (se 1 (by rfl) ⟨1083878, by rfl⟩ : syracuseStep 1445171 = 2167757) B2167757
theorem B2166083 : Blo 960589 2166083 := bstep (se 1 (by rfl) ⟨1624562, by rfl⟩ : syracuseStep 2166083 = 3249125) B3249125
theorem B1445201 : Blo 960589 1445201 := bstep (se 2 (by rfl) ⟨541950, by rfl⟩ : syracuseStep 1445201 = 1083901) B1083901
theorem B1445219 : Blo 960589 1445219 := bstep (se 1 (by rfl) ⟨1083914, by rfl⟩ : syracuseStep 1445219 = 2167829) B2167829
theorem B22842737 : Blo 960589 22842737 := bstep (se 2 (by rfl) ⟨8566026, by rfl⟩ : syracuseStep 22842737 = 17132053) B17132053
theorem B1445249 : Blo 960589 1445249 := bstep (se 2 (by rfl) ⟨541968, by rfl⟩ : syracuseStep 1445249 = 1083937) B1083937
theorem B1543553 : Blo 960589 1543553 := bstep (se 2 (by rfl) ⟨578832, by rfl⟩ : syracuseStep 1543553 = 1157665) B1157665
theorem B3247505 : Blo 960589 3247505 := bstep (se 2 (by rfl) ⟨1217814, by rfl⟩ : syracuseStep 3247505 = 2435629) B2435629
theorem B1445267 : Blo 960589 1445267 := bstep (se 1 (by rfl) ⟨1083950, by rfl⟩ : syracuseStep 1445267 = 2167901) B2167901
theorem B1084819 : Blo 960589 1084819 := bstep (se 1 (by rfl) ⟨813614, by rfl⟩ : syracuseStep 1084819 = 1627229) B1627229
theorem B1445297 : Blo 960589 1445297 := bstep (se 2 (by rfl) ⟨541986, by rfl⟩ : syracuseStep 1445297 = 1083973) B1083973
theorem B1445315 : Blo 960589 1445315 := bstep (se 1 (by rfl) ⟨1083986, by rfl⟩ : syracuseStep 1445315 = 2167973) B2167973
theorem B1445345 : Blo 960589 1445345 := bstep (se 2 (by rfl) ⟨542004, by rfl⟩ : syracuseStep 1445345 = 1084009) B1084009
theorem B3083761 : Blo 960589 3083761 := bstep (se 2 (by rfl) ⟨1156410, by rfl⟩ : syracuseStep 3083761 = 2312821) B2312821
theorem B1445363 : Blo 960589 1445363 := bstep (se 1 (by rfl) ⟨1084022, by rfl⟩ : syracuseStep 1445363 = 2168045) B2168045
theorem B7409165 : Blo 960589 7409165 := bstep (se 3 (by rfl) ⟨1389218, by rfl⟩ : syracuseStep 7409165 = 2778437) B2778437
theorem B1445393 : Blo 960589 1445393 := bstep (se 2 (by rfl) ⟨542022, by rfl⟩ : syracuseStep 1445393 = 1084045) B1084045
theorem B1445411 : Blo 960589 1445411 := bstep (se 1 (by rfl) ⟨1084058, by rfl⟩ : syracuseStep 1445411 = 2168117) B2168117
theorem B1084963 : Blo 960589 1084963 := bstep (se 1 (by rfl) ⟨813722, by rfl⟩ : syracuseStep 1084963 = 1627445) B1627445
theorem B3083825 : Blo 960589 3083825 := bstep (se 2 (by rfl) ⟨1156434, by rfl⟩ : syracuseStep 3083825 = 2312869) B2312869
theorem B1543745 : Blo 960589 1543745 := bstep (se 2 (by rfl) ⟨578904, by rfl⟩ : syracuseStep 1543745 = 1157809) B1157809
theorem B1445441 : Blo 960589 1445441 := bstep (se 2 (by rfl) ⟨542040, by rfl⟩ : syracuseStep 1445441 = 1084081) B1084081
theorem B2166353 : Blo 960589 2166353 := bstep (se 2 (by rfl) ⟨812382, by rfl⟩ : syracuseStep 2166353 = 1624765) B1624765
theorem B1445459 : Blo 960589 1445459 := bstep (se 1 (by rfl) ⟨1084094, by rfl⟩ : syracuseStep 1445459 = 2168189) B2168189
theorem B2166371 : Blo 960589 2166371 := bstep (se 1 (by rfl) ⟨1624778, by rfl⟩ : syracuseStep 2166371 = 3249557) B3249557
theorem B1445489 : Blo 960589 1445489 := bstep (se 2 (by rfl) ⟨542058, by rfl⟩ : syracuseStep 1445489 = 1084117) B1084117
theorem B1445507 : Blo 960589 1445507 := bstep (se 1 (by rfl) ⟨1084130, by rfl⟩ : syracuseStep 1445507 = 2168261) B2168261
theorem B1445537 : Blo 960589 1445537 := bstep (se 2 (by rfl) ⟨542076, by rfl⟩ : syracuseStep 1445537 = 1084153) B1084153
theorem B1445555 : Blo 960589 1445555 := bstep (se 1 (by rfl) ⟨1084166, by rfl⟩ : syracuseStep 1445555 = 2168333) B2168333
theorem B1085107 : Blo 960589 1085107 := bstep (se 1 (by rfl) ⟨813830, by rfl⟩ : syracuseStep 1085107 = 1627661) B1627661
theorem B1445585 : Blo 960589 1445585 := bstep (se 2 (by rfl) ⟨542094, by rfl⟩ : syracuseStep 1445585 = 1084189) B1084189
theorem B1445603 : Blo 960589 1445603 := bstep (se 1 (by rfl) ⟨1084202, by rfl⟩ : syracuseStep 1445603 = 2168405) B2168405
theorem B1445633 : Blo 960589 1445633 := bstep (se 2 (by rfl) ⟨542112, by rfl⟩ : syracuseStep 1445633 = 1084225) B1084225
theorem B1445651 : Blo 960589 1445651 := bstep (se 1 (by rfl) ⟨1084238, by rfl⟩ : syracuseStep 1445651 = 2168477) B2168477
theorem B1216291 : Blo 960589 1216291 := bstep (se 1 (by rfl) ⟨912218, by rfl⟩ : syracuseStep 1216291 = 1824437) B1824437
theorem B1445681 : Blo 960589 1445681 := bstep (se 2 (by rfl) ⟨542130, by rfl⟩ : syracuseStep 1445681 = 1084261) B1084261
theorem B1445699 : Blo 960589 1445699 := bstep (se 1 (by rfl) ⟨1084274, by rfl⟩ : syracuseStep 1445699 = 2168549) B2168549
theorem B1445729 : Blo 960589 1445729 := bstep (se 2 (by rfl) ⟨542148, by rfl⟩ : syracuseStep 1445729 = 1084297) B1084297
theorem B2166641 : Blo 960589 2166641 := bstep (se 2 (by rfl) ⟨812490, by rfl⟩ : syracuseStep 2166641 = 1624981) B1624981
theorem B1445747 : Blo 960589 1445747 := bstep (se 1 (by rfl) ⟨1084310, by rfl⟩ : syracuseStep 1445747 = 2168621) B2168621
theorem B1216387 : Blo 960589 1216387 := bstep (se 1 (by rfl) ⟨912290, by rfl⟩ : syracuseStep 1216387 = 1824581) B1824581
theorem B2166659 : Blo 960589 2166659 := bstep (se 1 (by rfl) ⟨1624994, by rfl⟩ : syracuseStep 2166659 = 3249989) B3249989
theorem B22548365 : Blo 960589 22548365 := bstep (se 3 (by rfl) ⟨4227818, by rfl⟩ : syracuseStep 22548365 = 8455637) B8455637
theorem B1445777 : Blo 960589 1445777 := bstep (se 2 (by rfl) ⟨542166, by rfl⟩ : syracuseStep 1445777 = 1084333) B1084333
theorem B1445795 : Blo 960589 1445795 := bstep (se 1 (by rfl) ⟨1084346, by rfl⟩ : syracuseStep 1445795 = 2168693) B2168693
theorem B3248045 : Blo 960589 3248045 := bstep (se 3 (by rfl) ⟨609008, by rfl⟩ : syracuseStep 3248045 = 1218017) B1218017
theorem B1445825 : Blo 960589 1445825 := bstep (se 2 (by rfl) ⟨542184, by rfl⟩ : syracuseStep 1445825 = 1084369) B1084369
theorem B1445843 : Blo 960589 1445843 := bstep (se 1 (by rfl) ⟨1084382, by rfl⟩ : syracuseStep 1445843 = 2168765) B2168765
theorem B3248099 : Blo 960589 3248099 := bstep (se 1 (by rfl) ⟨2436074, by rfl⟩ : syracuseStep 3248099 = 4872149) B4872149
theorem B1445873 : Blo 960589 1445873 := bstep (se 2 (by rfl) ⟨542202, by rfl⟩ : syracuseStep 1445873 = 1084405) B1084405
theorem B1445891 : Blo 960589 1445891 := bstep (se 1 (by rfl) ⟨1084418, by rfl⟩ : syracuseStep 1445891 = 2168837) B2168837
theorem B1445921 : Blo 960589 1445921 := bstep (se 2 (by rfl) ⟨542220, by rfl⟩ : syracuseStep 1445921 = 1084441) B1084441
theorem B1445939 : Blo 960589 1445939 := bstep (se 1 (by rfl) ⟨1084454, by rfl⟩ : syracuseStep 1445939 = 2168909) B2168909
theorem B1445969 : Blo 960589 1445969 := bstep (se 2 (by rfl) ⟨542238, by rfl⟩ : syracuseStep 1445969 = 1084477) B1084477
theorem B1445987 : Blo 960589 1445987 := bstep (se 1 (by rfl) ⟨1084490, by rfl⟩ : syracuseStep 1445987 = 2168981) B2168981
theorem B1446017 : Blo 960589 1446017 := bstep (se 2 (by rfl) ⟨542256, by rfl⟩ : syracuseStep 1446017 = 1084513) B1084513
theorem B2166929 : Blo 960589 2166929 := bstep (se 2 (by rfl) ⟨812598, by rfl⟩ : syracuseStep 2166929 = 1625197) B1625197
theorem B1446035 : Blo 960589 1446035 := bstep (se 1 (by rfl) ⟨1084526, by rfl⟩ : syracuseStep 1446035 = 2169053) B2169053
theorem B2166947 : Blo 960589 2166947 := bstep (se 1 (by rfl) ⟨1625210, by rfl⟩ : syracuseStep 2166947 = 3250421) B3250421
theorem B1446065 : Blo 960589 1446065 := bstep (se 2 (by rfl) ⟨542274, by rfl⟩ : syracuseStep 1446065 = 1084549) B1084549
theorem B1446083 : Blo 960589 1446083 := bstep (se 1 (by rfl) ⟨1084562, by rfl⟩ : syracuseStep 1446083 = 2169125) B2169125
theorem B1446113 : Blo 960589 1446113 := bstep (se 2 (by rfl) ⟨542292, by rfl⟩ : syracuseStep 1446113 = 1084585) B1084585
theorem B3248369 : Blo 960589 3248369 := bstep (se 2 (by rfl) ⟨1218138, by rfl⟩ : syracuseStep 3248369 = 2436277) B2436277
theorem B1446131 : Blo 960589 1446131 := bstep (se 1 (by rfl) ⟨1084598, by rfl⟩ : syracuseStep 1446131 = 2169197) B2169197
theorem B1446161 : Blo 960589 1446161 := bstep (se 2 (by rfl) ⟨542310, by rfl⟩ : syracuseStep 1446161 = 1084621) B1084621
theorem B1446179 : Blo 960589 1446179 := bstep (se 1 (by rfl) ⟨1084634, by rfl⟩ : syracuseStep 1446179 = 2169269) B2169269
theorem B1446209 : Blo 960589 1446209 := bstep (se 2 (by rfl) ⟨542328, by rfl⟩ : syracuseStep 1446209 = 1084657) B1084657
theorem B1446227 : Blo 960589 1446227 := bstep (se 1 (by rfl) ⟨1084670, by rfl⟩ : syracuseStep 1446227 = 2169341) B2169341
theorem B1446257 : Blo 960589 1446257 := bstep (se 2 (by rfl) ⟨542346, by rfl⟩ : syracuseStep 1446257 = 1084693) B1084693
theorem B1216883 : Blo 960589 1216883 := bstep (se 1 (by rfl) ⟨912662, by rfl⟩ : syracuseStep 1216883 = 1825325) B1825325
theorem B1446275 : Blo 960589 1446275 := bstep (se 1 (by rfl) ⟨1084706, by rfl⟩ : syracuseStep 1446275 = 2169413) B2169413
theorem B1446305 : Blo 960589 1446305 := bstep (se 2 (by rfl) ⟨542364, by rfl⟩ : syracuseStep 1446305 = 1084729) B1084729
theorem B2167217 : Blo 960589 2167217 := bstep (se 2 (by rfl) ⟨812706, by rfl⟩ : syracuseStep 2167217 = 1625413) B1625413
theorem B1446323 : Blo 960589 1446323 := bstep (se 1 (by rfl) ⟨1084742, by rfl⟩ : syracuseStep 1446323 = 2169485) B2169485
theorem B2167235 : Blo 960589 2167235 := bstep (se 1 (by rfl) ⟨1625426, by rfl⟩ : syracuseStep 2167235 = 3250853) B3250853
theorem B1446353 : Blo 960589 1446353 := bstep (se 2 (by rfl) ⟨542382, by rfl⟩ : syracuseStep 1446353 = 1084765) B1084765
theorem B1446371 : Blo 960589 1446371 := bstep (se 1 (by rfl) ⟨1084778, by rfl⟩ : syracuseStep 1446371 = 2169557) B2169557
theorem B1446401 : Blo 960589 1446401 := bstep (se 2 (by rfl) ⟨542400, by rfl⟩ : syracuseStep 1446401 = 1084801) B1084801
theorem B1446419 : Blo 960589 1446419 := bstep (se 1 (by rfl) ⟨1084814, by rfl⟩ : syracuseStep 1446419 = 2169629) B2169629
theorem B1446449 : Blo 960589 1446449 := bstep (se 2 (by rfl) ⟨542418, by rfl⟩ : syracuseStep 1446449 = 1084837) B1084837
theorem B30511669 : Blo 960589 30511669 := bstep (se 5 (by rfl) ⟨1430234, by rfl⟩ : syracuseStep 30511669 = 2860469) B2860469
theorem B1446467 : Blo 960589 1446467 := bstep (se 1 (by rfl) ⟨1084850, by rfl⟩ : syracuseStep 1446467 = 2169701) B2169701
theorem B1446497 : Blo 960589 1446497 := bstep (se 2 (by rfl) ⟨542436, by rfl⟩ : syracuseStep 1446497 = 1084873) B1084873
theorem B1446515 : Blo 960589 1446515 := bstep (se 1 (by rfl) ⟨1084886, by rfl⟩ : syracuseStep 1446515 = 2169773) B2169773
theorem B1446545 : Blo 960589 1446545 := bstep (se 2 (by rfl) ⟨542454, by rfl⟩ : syracuseStep 1446545 = 1084909) B1084909
theorem B1446563 : Blo 960589 1446563 := bstep (se 1 (by rfl) ⟨1084922, by rfl⟩ : syracuseStep 1446563 = 2169845) B2169845
theorem B1446593 : Blo 960589 1446593 := bstep (se 2 (by rfl) ⟨542472, by rfl⟩ : syracuseStep 1446593 = 1084945) B1084945
theorem B2167505 : Blo 960589 2167505 := bstep (se 2 (by rfl) ⟨812814, by rfl⟩ : syracuseStep 2167505 = 1625629) B1625629
theorem B1446611 : Blo 960589 1446611 := bstep (se 1 (by rfl) ⟨1084958, by rfl⟩ : syracuseStep 1446611 = 2169917) B2169917
theorem B2167523 : Blo 960589 2167523 := bstep (se 1 (by rfl) ⟨1625642, by rfl⟩ : syracuseStep 2167523 = 3251285) B3251285
theorem B1446641 : Blo 960589 1446641 := bstep (se 2 (by rfl) ⟨542490, by rfl⟩ : syracuseStep 1446641 = 1084981) B1084981
theorem B1643267 : Blo 960589 1643267 := bstep (se 1 (by rfl) ⟨1232450, by rfl⟩ : syracuseStep 1643267 = 2464901) B2464901
theorem B1446659 : Blo 960589 1446659 := bstep (se 1 (by rfl) ⟨1084994, by rfl⟩ : syracuseStep 1446659 = 2169989) B2169989
theorem B3248909 : Blo 960589 3248909 := bstep (se 3 (by rfl) ⟨609170, by rfl⟩ : syracuseStep 3248909 = 1218341) B1218341
theorem B1446689 : Blo 960589 1446689 := bstep (se 2 (by rfl) ⟨542508, by rfl⟩ : syracuseStep 1446689 = 1085017) B1085017
theorem B1446707 : Blo 960589 1446707 := bstep (se 1 (by rfl) ⟨1085030, by rfl⟩ : syracuseStep 1446707 = 2170061) B2170061
theorem B3248963 : Blo 960589 3248963 := bstep (se 1 (by rfl) ⟨2436722, by rfl⟩ : syracuseStep 3248963 = 4873445) B4873445
theorem B1446737 : Blo 960589 1446737 := bstep (se 2 (by rfl) ⟨542526, by rfl⟩ : syracuseStep 1446737 = 1085053) B1085053
theorem B1446755 : Blo 960589 1446755 := bstep (se 1 (by rfl) ⟨1085066, by rfl⟩ : syracuseStep 1446755 = 2170133) B2170133
theorem B1643377 : Blo 960589 1643377 := bstep (se 2 (by rfl) ⟨616266, by rfl⟩ : syracuseStep 1643377 = 1232533) B1232533
theorem B1446785 : Blo 960589 1446785 := bstep (se 2 (by rfl) ⟨542544, by rfl⟩ : syracuseStep 1446785 = 1085089) B1085089
theorem B1446803 : Blo 960589 1446803 := bstep (se 1 (by rfl) ⟨1085102, by rfl⟩ : syracuseStep 1446803 = 2170205) B2170205
theorem B1446833 : Blo 960589 1446833 := bstep (se 2 (by rfl) ⟨542562, by rfl⟩ : syracuseStep 1446833 = 1085125) B1085125
theorem B1446851 : Blo 960589 1446851 := bstep (se 1 (by rfl) ⟨1085138, by rfl⟩ : syracuseStep 1446851 = 2170277) B2170277
theorem B1446881 : Blo 960589 1446881 := bstep (se 2 (by rfl) ⟨542580, by rfl⟩ : syracuseStep 1446881 = 1085161) B1085161
theorem B7312355 : Blo 960589 7312355 := bstep (se 1 (by rfl) ⟨5484266, by rfl⟩ : syracuseStep 7312355 = 10968533) B10968533
theorem B2167793 : Blo 960589 2167793 := bstep (se 2 (by rfl) ⟨812922, by rfl⟩ : syracuseStep 2167793 = 1625845) B1625845
theorem B2167811 : Blo 960589 2167811 := bstep (se 1 (by rfl) ⟨1625858, by rfl⟩ : syracuseStep 2167811 = 3251717) B3251717
theorem B1217587 : Blo 960589 1217587 := bstep (se 1 (by rfl) ⟨913190, by rfl⟩ : syracuseStep 1217587 = 1826381) B1826381
theorem B3249233 : Blo 960589 3249233 := bstep (se 2 (by rfl) ⟨1218462, by rfl⟩ : syracuseStep 3249233 = 2436925) B2436925
theorem B1217683 : Blo 960589 1217683 := bstep (se 1 (by rfl) ⟨913262, by rfl⟩ : syracuseStep 1217683 = 1826525) B1826525
theorem B2168081 : Blo 960589 2168081 := bstep (se 2 (by rfl) ⟨813030, by rfl⟩ : syracuseStep 2168081 = 1626061) B1626061
theorem B2168099 : Blo 960589 2168099 := bstep (se 1 (by rfl) ⟨1626074, by rfl⟩ : syracuseStep 2168099 = 3252149) B3252149
theorem B1250707 : Blo 960589 1250707 := bstep (se 1 (by rfl) ⟨938030, by rfl⟩ : syracuseStep 1250707 = 1876061) B1876061
theorem B2168369 : Blo 960589 2168369 := bstep (se 2 (by rfl) ⟨813138, by rfl⟩ : syracuseStep 2168369 = 1626277) B1626277
theorem B2168387 : Blo 960589 2168387 := bstep (se 1 (by rfl) ⟨1626290, by rfl⟩ : syracuseStep 2168387 = 3252581) B3252581
theorem B988771 : Blo 960589 988771 := bstep (se 1 (by rfl) ⟨741578, by rfl⟩ : syracuseStep 988771 = 1483157) B1483157
theorem B3249773 : Blo 960589 3249773 := bstep (se 3 (by rfl) ⟨609332, by rfl⟩ : syracuseStep 3249773 = 1218665) B1218665
theorem B1218179 : Blo 960589 1218179 := bstep (se 1 (by rfl) ⟨913634, by rfl⟩ : syracuseStep 1218179 = 1827269) B1827269
theorem B3249827 : Blo 960589 3249827 := bstep (se 1 (by rfl) ⟨2437370, by rfl⟩ : syracuseStep 3249827 = 4874741) B4874741
theorem B2168657 : Blo 960589 2168657 := bstep (se 2 (by rfl) ⟨813246, by rfl⟩ : syracuseStep 2168657 = 1626493) B1626493
theorem B2168675 : Blo 960589 2168675 := bstep (se 1 (by rfl) ⟨1626506, by rfl⟩ : syracuseStep 2168675 = 3253013) B3253013
theorem B3250097 : Blo 960589 3250097 := bstep (se 2 (by rfl) ⟨1218786, by rfl⟩ : syracuseStep 3250097 = 2437573) B2437573
theorem B2168945 : Blo 960589 2168945 := bstep (se 2 (by rfl) ⟨813354, by rfl⟩ : syracuseStep 2168945 = 1626709) B1626709
theorem B2168963 : Blo 960589 2168963 := bstep (se 1 (by rfl) ⟨1626722, by rfl⟩ : syracuseStep 2168963 = 3253445) B3253445
theorem B4626659 : Blo 960589 4626659 := bstep (se 1 (by rfl) ⟨3469994, by rfl⟩ : syracuseStep 4626659 = 6939989) B6939989
theorem B2922797 : Blo 960589 2922797 := bstep (se 3 (by rfl) ⟨548024, by rfl⟩ : syracuseStep 2922797 = 1096049) B1096049
theorem B1218883 : Blo 960589 1218883 := bstep (se 1 (by rfl) ⟨914162, by rfl⟩ : syracuseStep 1218883 = 1828325) B1828325
theorem B2169233 : Blo 960589 2169233 := bstep (se 2 (by rfl) ⟨813462, by rfl⟩ : syracuseStep 2169233 = 1626925) B1626925
theorem B1218979 : Blo 960589 1218979 := bstep (se 1 (by rfl) ⟨914234, by rfl⟩ : syracuseStep 1218979 = 1828469) B1828469
theorem B2169251 : Blo 960589 2169251 := bstep (se 1 (by rfl) ⟨1626938, by rfl⟩ : syracuseStep 2169251 = 3253877) B3253877
theorem B3250637 : Blo 960589 3250637 := bstep (se 3 (by rfl) ⟨609494, by rfl⟩ : syracuseStep 3250637 = 1218989) B1218989
theorem B3250691 : Blo 960589 3250691 := bstep (se 1 (by rfl) ⟨2438018, by rfl⟩ : syracuseStep 3250691 = 4876037) B4876037
theorem B12491333 : Blo 960589 12491333 := bstep (se 4 (by rfl) ⟨1171062, by rfl⟩ : syracuseStep 12491333 = 2342125) B2342125
theorem B2169521 : Blo 960589 2169521 := bstep (se 2 (by rfl) ⟨813570, by rfl⟩ : syracuseStep 2169521 = 1627141) B1627141
theorem B2169539 : Blo 960589 2169539 := bstep (se 1 (by rfl) ⟨1627154, by rfl⟩ : syracuseStep 2169539 = 3254309) B3254309
theorem B4397773 : Blo 960589 4397773 := bstep (se 3 (by rfl) ⟨824582, by rfl⟩ : syracuseStep 4397773 = 1649165) B1649165
theorem B3250961 : Blo 960589 3250961 := bstep (se 2 (by rfl) ⟨1219110, by rfl⟩ : syracuseStep 3250961 = 2438221) B2438221
theorem B1219475 : Blo 960589 1219475 := bstep (se 1 (by rfl) ⟨914606, by rfl⟩ : syracuseStep 1219475 = 1829213) B1829213
theorem B2169809 : Blo 960589 2169809 := bstep (se 2 (by rfl) ⟨813678, by rfl⟩ : syracuseStep 2169809 = 1627357) B1627357
theorem B2169827 : Blo 960589 2169827 := bstep (se 1 (by rfl) ⟨1627370, by rfl⟩ : syracuseStep 2169827 = 3254741) B3254741
theorem B4627505 : Blo 960589 4627505 := bstep (se 2 (by rfl) ⟨1735314, by rfl⟩ : syracuseStep 4627505 = 3470629) B3470629
theorem B2432177 : Blo 960589 2432177 := bstep (se 2 (by rfl) ⟨912066, by rfl⟩ : syracuseStep 2432177 = 1824133) B1824133
theorem B2432227 : Blo 960589 2432227 := bstep (se 1 (by rfl) ⟨1824170, by rfl⟩ : syracuseStep 2432227 = 3648341) B3648341
theorem B2170097 : Blo 960589 2170097 := bstep (se 2 (by rfl) ⟨813786, by rfl⟩ : syracuseStep 2170097 = 1627573) B1627573
theorem B2170115 : Blo 960589 2170115 := bstep (se 1 (by rfl) ⟨1627586, by rfl⟩ : syracuseStep 2170115 = 3255173) B3255173
theorem B3251501 : Blo 960589 3251501 := bstep (se 3 (by rfl) ⟨609656, by rfl⟩ : syracuseStep 3251501 = 1219313) B1219313
theorem B5479757 : Blo 960589 5479757 := bstep (se 3 (by rfl) ⟨1027454, by rfl⟩ : syracuseStep 5479757 = 2054909) B2054909
theorem B3251555 : Blo 960589 3251555 := bstep (se 1 (by rfl) ⟨2438666, by rfl⟩ : syracuseStep 3251555 = 4877333) B4877333
theorem B2432369 : Blo 960589 2432369 := bstep (se 2 (by rfl) ⟨912138, by rfl⟩ : syracuseStep 2432369 = 1824277) B1824277
theorem B4627853 : Blo 960589 4627853 := bstep (se 3 (by rfl) ⟨867722, by rfl⟩ : syracuseStep 4627853 = 1735445) B1735445
theorem B1318465 : Blo 960589 1318465 := bstep (se 2 (by rfl) ⟨494424, by rfl⟩ : syracuseStep 1318465 = 988849) B988849
theorem B1220179 : Blo 960589 1220179 := bstep (se 1 (by rfl) ⟨915134, by rfl⟩ : syracuseStep 1220179 = 1830269) B1830269
theorem B3251825 : Blo 960589 3251825 := bstep (se 2 (by rfl) ⟨1219434, by rfl⟩ : syracuseStep 3251825 = 2438869) B2438869
theorem B3088003 : Blo 960589 3088003 := bstep (se 1 (by rfl) ⟨2316002, by rfl⟩ : syracuseStep 3088003 = 4632005) B4632005
theorem B1220275 : Blo 960589 1220275 := bstep (se 1 (by rfl) ⟨915206, by rfl⟩ : syracuseStep 1220275 = 1830413) B1830413
theorem B6168419 : Blo 960589 6168419 := bstep (se 1 (by rfl) ⟨4626314, by rfl⟩ : syracuseStep 6168419 = 9252629) B9252629
theorem B12492785 : Blo 960589 12492785 := bstep (se 2 (by rfl) ⟨4684794, by rfl⟩ : syracuseStep 12492785 = 9369589) B9369589
theorem B3121265 : Blo 960589 3121265 := bstep (se 2 (by rfl) ⟨1170474, by rfl⟩ : syracuseStep 3121265 = 2340949) B2340949
theorem B3252365 : Blo 960589 3252365 := bstep (se 3 (by rfl) ⟨609818, by rfl⟩ : syracuseStep 3252365 = 1219637) B1219637
theorem B1646755 : Blo 960589 1646755 := bstep (se 1 (by rfl) ⟨1235066, by rfl⟩ : syracuseStep 1646755 = 2470133) B2470133
theorem B4399267 : Blo 960589 4399267 := bstep (se 1 (by rfl) ⟨3299450, by rfl⟩ : syracuseStep 4399267 = 6598901) B6598901
theorem B1220771 : Blo 960589 1220771 := bstep (se 1 (by rfl) ⟨915578, by rfl⟩ : syracuseStep 1220771 = 1831157) B1831157
theorem B3252419 : Blo 960589 3252419 := bstep (se 1 (by rfl) ⟨2439314, by rfl⟩ : syracuseStep 3252419 = 4878629) B4878629
theorem B2433361 : Blo 960589 2433361 := bstep (se 2 (by rfl) ⟨912510, by rfl⟩ : syracuseStep 2433361 = 1825021) B1825021
theorem B4104589 : Blo 960589 4104589 := bstep (se 3 (by rfl) ⟨769610, by rfl⟩ : syracuseStep 4104589 = 1539221) B1539221
theorem B3252689 : Blo 960589 3252689 := bstep (se 2 (by rfl) ⟨1219758, by rfl⟩ : syracuseStep 3252689 = 2439517) B2439517
theorem B2433635 : Blo 960589 2433635 := bstep (se 1 (by rfl) ⟨1825226, by rfl⟩ : syracuseStep 2433635 = 3650453) B3650453
theorem B4104931 : Blo 960589 4104931 := bstep (se 1 (by rfl) ⟨3078698, by rfl⟩ : syracuseStep 4104931 = 6157397) B6157397
theorem B2433827 : Blo 960589 2433827 := bstep (se 1 (by rfl) ⟨1825370, by rfl⟩ : syracuseStep 2433827 = 3650741) B3650741
theorem B1319825 : Blo 960589 1319825 := bstep (se 2 (by rfl) ⟨494934, by rfl⟩ : syracuseStep 1319825 = 989869) B989869
theorem B3253229 : Blo 960589 3253229 := bstep (se 3 (by rfl) ⟨609980, by rfl⟩ : syracuseStep 3253229 = 1219961) B1219961
theorem B3253283 : Blo 960589 3253283 := bstep (se 1 (by rfl) ⟨2439962, by rfl⟩ : syracuseStep 3253283 = 4879925) B4879925
theorem B2467057 : Blo 960589 2467057 := bstep (se 2 (by rfl) ⟨925146, by rfl⟩ : syracuseStep 2467057 = 1850293) B1850293
theorem B3253553 : Blo 960589 3253553 := bstep (se 2 (by rfl) ⟨1220082, by rfl⟩ : syracuseStep 3253553 = 2440165) B2440165
theorem B5481989 : Blo 960589 5481989 := bstep (se 4 (by rfl) ⟨513936, by rfl⟩ : syracuseStep 5481989 = 1027873) B1027873
theorem B1156627 : Blo 960589 1156627 := bstep (se 1 (by rfl) ⟨867470, by rfl⟩ : syracuseStep 1156627 = 1734941) B1734941
theorem B2467363 : Blo 960589 2467363 := bstep (se 1 (by rfl) ⟨1850522, by rfl⟩ : syracuseStep 2467363 = 3701045) B3701045
theorem B1156771 : Blo 960589 1156771 := bstep (se 1 (by rfl) ⟨867578, by rfl⟩ : syracuseStep 1156771 = 1735157) B1735157
theorem B2434769 : Blo 960589 2434769 := bstep (se 2 (by rfl) ⟨913038, by rfl⟩ : syracuseStep 2434769 = 1826077) B1826077
theorem B2434819 : Blo 960589 2434819 := bstep (se 1 (by rfl) ⟨1826114, by rfl⟩ : syracuseStep 2434819 = 3652229) B3652229
theorem B6170417 : Blo 960589 6170417 := bstep (se 2 (by rfl) ⟨2313906, by rfl⟩ : syracuseStep 6170417 = 4627813) B4627813
theorem B2598733 : Blo 960589 2598733 := bstep (se 3 (by rfl) ⟨487262, by rfl⟩ : syracuseStep 2598733 = 974525) B974525
theorem B3254093 : Blo 960589 3254093 := bstep (se 3 (by rfl) ⟨610142, by rfl⟩ : syracuseStep 3254093 = 1220285) B1220285
theorem B3254147 : Blo 960589 3254147 := bstep (se 1 (by rfl) ⟨2440610, by rfl⟩ : syracuseStep 3254147 = 4881221) B4881221
theorem B2434961 : Blo 960589 2434961 := bstep (se 2 (by rfl) ⟨913110, by rfl⟩ : syracuseStep 2434961 = 1826221) B1826221
theorem B3647537 : Blo 960589 3647537 := bstep (se 2 (by rfl) ⟨1367826, by rfl⟩ : syracuseStep 3647537 = 2735653) B2735653
theorem B960595 : Blo 960589 960595 := bstep (se 1 (by rfl) ⟨720446, by rfl⟩ : syracuseStep 960595 = 1440893) B1440893
theorem B960611 : Blo 960589 960611 := bstep (se 1 (by rfl) ⟨720458, by rfl⟩ : syracuseStep 960611 = 1440917) B1440917
theorem B960627 : Blo 960589 960627 := bstep (se 1 (by rfl) ⟨720470, by rfl⟩ : syracuseStep 960627 = 1440941) B1440941
theorem B960643 : Blo 960589 960643 := bstep (se 1 (by rfl) ⟨720482, by rfl⟩ : syracuseStep 960643 = 1440965) B1440965
theorem B3254417 : Blo 960589 3254417 := bstep (se 2 (by rfl) ⟨1220406, by rfl⟩ : syracuseStep 3254417 = 2440813) B2440813
theorem B960659 : Blo 960589 960659 := bstep (se 1 (by rfl) ⟨720494, by rfl⟩ : syracuseStep 960659 = 1440989) B1440989
theorem B960675 : Blo 960589 960675 := bstep (se 1 (by rfl) ⟨720506, by rfl⟩ : syracuseStep 960675 = 1441013) B1441013
theorem B5482673 : Blo 960589 5482673 := bstep (se 2 (by rfl) ⟨2056002, by rfl⟩ : syracuseStep 5482673 = 4112005) B4112005
theorem B960691 : Blo 960589 960691 := bstep (se 1 (by rfl) ⟨720518, by rfl⟩ : syracuseStep 960691 = 1441037) B1441037
theorem B960707 : Blo 960589 960707 := bstep (se 1 (by rfl) ⟨720530, by rfl⟩ : syracuseStep 960707 = 1441061) B1441061
theorem B7317701 : Blo 960589 7317701 := bstep (se 4 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 7317701 = 1372069) B1372069
theorem B960723 : Blo 960589 960723 := bstep (se 1 (by rfl) ⟨720542, by rfl⟩ : syracuseStep 960723 = 1441085) B1441085
theorem B960739 : Blo 960589 960739 := bstep (se 1 (by rfl) ⟨720554, by rfl⟩ : syracuseStep 960739 = 1441109) B1441109
theorem B960755 : Blo 960589 960755 := bstep (se 1 (by rfl) ⟨720566, by rfl⟩ : syracuseStep 960755 = 1441133) B1441133
theorem B960771 : Blo 960589 960771 := bstep (se 1 (by rfl) ⟨720578, by rfl⟩ : syracuseStep 960771 = 1441157) B1441157
theorem B8792333 : Blo 960589 8792333 := bstep (se 3 (by rfl) ⟨1648562, by rfl⟩ : syracuseStep 8792333 = 3297125) B3297125
theorem B960787 : Blo 960589 960787 := bstep (se 1 (by rfl) ⟨720590, by rfl⟩ : syracuseStep 960787 = 1441181) B1441181
theorem B960803 : Blo 960589 960803 := bstep (se 1 (by rfl) ⟨720602, by rfl⟩ : syracuseStep 960803 = 1441205) B1441205
theorem B1648945 : Blo 960589 1648945 := bstep (se 2 (by rfl) ⟨618354, by rfl⟩ : syracuseStep 1648945 = 1236709) B1236709
theorem B960819 : Blo 960589 960819 := bstep (se 1 (by rfl) ⟨720614, by rfl⟩ : syracuseStep 960819 = 1441229) B1441229
theorem B960835 : Blo 960589 960835 := bstep (se 1 (by rfl) ⟨720626, by rfl⟩ : syracuseStep 960835 = 1441253) B1441253
theorem B960851 : Blo 960589 960851 := bstep (se 1 (by rfl) ⟨720638, by rfl⟩ : syracuseStep 960851 = 1441277) B1441277
theorem B960867 : Blo 960589 960867 := bstep (se 1 (by rfl) ⟨720650, by rfl⟩ : syracuseStep 960867 = 1441301) B1441301
theorem B960883 : Blo 960589 960883 := bstep (se 1 (by rfl) ⟨720662, by rfl⟩ : syracuseStep 960883 = 1441325) B1441325
theorem B960899 : Blo 960589 960899 := bstep (se 1 (by rfl) ⟨720674, by rfl⟩ : syracuseStep 960899 = 1441349) B1441349
theorem B960915 : Blo 960589 960915 := bstep (se 1 (by rfl) ⟨720686, by rfl⟩ : syracuseStep 960915 = 1441373) B1441373
theorem B960931 : Blo 960589 960931 := bstep (se 1 (by rfl) ⟨720698, by rfl⟩ : syracuseStep 960931 = 1441397) B1441397
theorem B960947 : Blo 960589 960947 := bstep (se 1 (by rfl) ⟨720710, by rfl⟩ : syracuseStep 960947 = 1441421) B1441421
theorem B960963 : Blo 960589 960963 := bstep (se 1 (by rfl) ⟨720722, by rfl⟩ : syracuseStep 960963 = 1441445) B1441445
theorem B960979 : Blo 960589 960979 := bstep (se 1 (by rfl) ⟨720734, by rfl⟩ : syracuseStep 960979 = 1441469) B1441469
theorem B960995 : Blo 960589 960995 := bstep (se 1 (by rfl) ⟨720746, by rfl⟩ : syracuseStep 960995 = 1441493) B1441493
theorem B961011 : Blo 960589 961011 := bstep (se 1 (by rfl) ⟨720758, by rfl⟩ : syracuseStep 961011 = 1441517) B1441517
theorem B961027 : Blo 960589 961027 := bstep (se 1 (by rfl) ⟨720770, by rfl⟩ : syracuseStep 961027 = 1441541) B1441541
theorem B2468369 : Blo 960589 2468369 := bstep (se 2 (by rfl) ⟨925638, by rfl⟩ : syracuseStep 2468369 = 1851277) B1851277
theorem B961043 : Blo 960589 961043 := bstep (se 1 (by rfl) ⟨720782, by rfl⟩ : syracuseStep 961043 = 1441565) B1441565
theorem B961059 : Blo 960589 961059 := bstep (se 1 (by rfl) ⟨720794, by rfl⟩ : syracuseStep 961059 = 1441589) B1441589
theorem B961075 : Blo 960589 961075 := bstep (se 1 (by rfl) ⟨720806, by rfl⟩ : syracuseStep 961075 = 1441613) B1441613
theorem B961091 : Blo 960589 961091 := bstep (se 1 (by rfl) ⟨720818, by rfl⟩ : syracuseStep 961091 = 1441637) B1441637
theorem B961107 : Blo 960589 961107 := bstep (se 1 (by rfl) ⟨720830, by rfl⟩ : syracuseStep 961107 = 1441661) B1441661
theorem B1026643 : Blo 960589 1026643 := bstep (se 1 (by rfl) ⟨769982, by rfl⟩ : syracuseStep 1026643 = 1539965) B1539965
theorem B961123 : Blo 960589 961123 := bstep (se 1 (by rfl) ⟨720842, by rfl⟩ : syracuseStep 961123 = 1441685) B1441685
theorem B961139 : Blo 960589 961139 := bstep (se 1 (by rfl) ⟨720854, by rfl⟩ : syracuseStep 961139 = 1441709) B1441709
theorem B961155 : Blo 960589 961155 := bstep (se 1 (by rfl) ⟨720866, by rfl⟩ : syracuseStep 961155 = 1441733) B1441733
theorem B2468483 : Blo 960589 2468483 := bstep (se 1 (by rfl) ⟨1851362, by rfl⟩ : syracuseStep 2468483 = 3702725) B3702725
theorem B961171 : Blo 960589 961171 := bstep (se 1 (by rfl) ⟨720878, by rfl⟩ : syracuseStep 961171 = 1441757) B1441757
theorem B961187 : Blo 960589 961187 := bstep (se 1 (by rfl) ⟨720890, by rfl⟩ : syracuseStep 961187 = 1441781) B1441781
theorem B3254957 : Blo 960589 3254957 := bstep (se 3 (by rfl) ⟨610304, by rfl⟩ : syracuseStep 3254957 = 1220609) B1220609
theorem B961203 : Blo 960589 961203 := bstep (se 1 (by rfl) ⟨720902, by rfl⟩ : syracuseStep 961203 = 1441805) B1441805
theorem B961219 : Blo 960589 961219 := bstep (se 1 (by rfl) ⟨720914, by rfl⟩ : syracuseStep 961219 = 1441829) B1441829
theorem B961235 : Blo 960589 961235 := bstep (se 1 (by rfl) ⟨720926, by rfl⟩ : syracuseStep 961235 = 1441853) B1441853
theorem B961251 : Blo 960589 961251 := bstep (se 1 (by rfl) ⟨720938, by rfl⟩ : syracuseStep 961251 = 1441877) B1441877
theorem B3255011 : Blo 960589 3255011 := bstep (se 1 (by rfl) ⟨2441258, by rfl⟩ : syracuseStep 3255011 = 4882517) B4882517
theorem B961267 : Blo 960589 961267 := bstep (se 1 (by rfl) ⟨720950, by rfl⟩ : syracuseStep 961267 = 1441901) B1441901
theorem B961283 : Blo 960589 961283 := bstep (se 1 (by rfl) ⟨720962, by rfl⟩ : syracuseStep 961283 = 1441925) B1441925
theorem B961299 : Blo 960589 961299 := bstep (se 1 (by rfl) ⟨720974, by rfl⟩ : syracuseStep 961299 = 1441949) B1441949
theorem B961315 : Blo 960589 961315 := bstep (se 1 (by rfl) ⟨720986, by rfl⟩ : syracuseStep 961315 = 1441973) B1441973
theorem B961331 : Blo 960589 961331 := bstep (se 1 (by rfl) ⟨720998, by rfl⟩ : syracuseStep 961331 = 1441997) B1441997
theorem B961347 : Blo 960589 961347 := bstep (se 1 (by rfl) ⟨721010, by rfl⟩ : syracuseStep 961347 = 1442021) B1442021
theorem B961363 : Blo 960589 961363 := bstep (se 1 (by rfl) ⟨721022, by rfl⟩ : syracuseStep 961363 = 1442045) B1442045
theorem B961379 : Blo 960589 961379 := bstep (se 1 (by rfl) ⟨721034, by rfl⟩ : syracuseStep 961379 = 1442069) B1442069
theorem B2435953 : Blo 960589 2435953 := bstep (se 2 (by rfl) ⟨913482, by rfl⟩ : syracuseStep 2435953 = 1826965) B1826965
theorem B961395 : Blo 960589 961395 := bstep (se 1 (by rfl) ⟨721046, by rfl⟩ : syracuseStep 961395 = 1442093) B1442093
theorem B961411 : Blo 960589 961411 := bstep (se 1 (by rfl) ⟨721058, by rfl⟩ : syracuseStep 961411 = 1442117) B1442117
theorem B961427 : Blo 960589 961427 := bstep (se 1 (by rfl) ⟨721070, by rfl⟩ : syracuseStep 961427 = 1442141) B1442141
theorem B961443 : Blo 960589 961443 := bstep (se 1 (by rfl) ⟨721082, by rfl⟩ : syracuseStep 961443 = 1442165) B1442165
theorem B961459 : Blo 960589 961459 := bstep (se 1 (by rfl) ⟨721094, by rfl⟩ : syracuseStep 961459 = 1442189) B1442189
theorem B961475 : Blo 960589 961475 := bstep (se 1 (by rfl) ⟨721106, by rfl⟩ : syracuseStep 961475 = 1442213) B1442213
theorem B961491 : Blo 960589 961491 := bstep (se 1 (by rfl) ⟨721118, by rfl⟩ : syracuseStep 961491 = 1442237) B1442237
theorem B961507 : Blo 960589 961507 := bstep (se 1 (by rfl) ⟨721130, by rfl⟩ : syracuseStep 961507 = 1442261) B1442261
theorem B3255281 : Blo 960589 3255281 := bstep (se 2 (by rfl) ⟨1220730, by rfl⟩ : syracuseStep 3255281 = 2441461) B2441461
theorem B961523 : Blo 960589 961523 := bstep (se 1 (by rfl) ⟨721142, by rfl⟩ : syracuseStep 961523 = 1442285) B1442285
theorem B961539 : Blo 960589 961539 := bstep (se 1 (by rfl) ⟨721154, by rfl⟩ : syracuseStep 961539 = 1442309) B1442309
theorem B961555 : Blo 960589 961555 := bstep (se 1 (by rfl) ⟨721166, by rfl⟩ : syracuseStep 961555 = 1442333) B1442333
theorem B961571 : Blo 960589 961571 := bstep (se 1 (by rfl) ⟨721178, by rfl⟩ : syracuseStep 961571 = 1442357) B1442357
theorem B961587 : Blo 960589 961587 := bstep (se 1 (by rfl) ⟨721190, by rfl⟩ : syracuseStep 961587 = 1442381) B1442381
theorem B961603 : Blo 960589 961603 := bstep (se 1 (by rfl) ⟨721202, by rfl⟩ : syracuseStep 961603 = 1442405) B1442405
theorem B961619 : Blo 960589 961619 := bstep (se 1 (by rfl) ⟨721214, by rfl⟩ : syracuseStep 961619 = 1442429) B1442429
theorem B961635 : Blo 960589 961635 := bstep (se 1 (by rfl) ⟨721226, by rfl⟩ : syracuseStep 961635 = 1442453) B1442453
theorem B961651 : Blo 960589 961651 := bstep (se 1 (by rfl) ⟨721238, by rfl⟩ : syracuseStep 961651 = 1442477) B1442477
theorem B961667 : Blo 960589 961667 := bstep (se 1 (by rfl) ⟨721250, by rfl⟩ : syracuseStep 961667 = 1442501) B1442501
theorem B2436227 : Blo 960589 2436227 := bstep (se 1 (by rfl) ⟨1827170, by rfl⟩ : syracuseStep 2436227 = 3654341) B3654341
theorem B961683 : Blo 960589 961683 := bstep (se 1 (by rfl) ⟨721262, by rfl⟩ : syracuseStep 961683 = 1442525) B1442525
theorem B961699 : Blo 960589 961699 := bstep (se 1 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 961699 = 1442549) B1442549
theorem B961715 : Blo 960589 961715 := bstep (se 1 (by rfl) ⟨721286, by rfl⟩ : syracuseStep 961715 = 1442573) B1442573
theorem B961731 : Blo 960589 961731 := bstep (se 1 (by rfl) ⟨721298, by rfl⟩ : syracuseStep 961731 = 1442597) B1442597
theorem B961747 : Blo 960589 961747 := bstep (se 1 (by rfl) ⟨721310, by rfl⟩ : syracuseStep 961747 = 1442621) B1442621
theorem B961763 : Blo 960589 961763 := bstep (se 1 (by rfl) ⟨721322, by rfl⟩ : syracuseStep 961763 = 1442645) B1442645
theorem B961779 : Blo 960589 961779 := bstep (se 1 (by rfl) ⟨721334, by rfl⟩ : syracuseStep 961779 = 1442669) B1442669
theorem B961795 : Blo 960589 961795 := bstep (se 1 (by rfl) ⟨721346, by rfl⟩ : syracuseStep 961795 = 1442693) B1442693
theorem B961811 : Blo 960589 961811 := bstep (se 1 (by rfl) ⟨721358, by rfl⟩ : syracuseStep 961811 = 1442717) B1442717
theorem B961827 : Blo 960589 961827 := bstep (se 1 (by rfl) ⟨721370, by rfl⟩ : syracuseStep 961827 = 1442741) B1442741
theorem B961843 : Blo 960589 961843 := bstep (se 1 (by rfl) ⟨721382, by rfl⟩ : syracuseStep 961843 = 1442765) B1442765
theorem B961859 : Blo 960589 961859 := bstep (se 1 (by rfl) ⟨721394, by rfl⟩ : syracuseStep 961859 = 1442789) B1442789
theorem B2436419 : Blo 960589 2436419 := bstep (se 1 (by rfl) ⟨1827314, by rfl⟩ : syracuseStep 2436419 = 3654629) B3654629
theorem B961875 : Blo 960589 961875 := bstep (se 1 (by rfl) ⟨721406, by rfl⟩ : syracuseStep 961875 = 1442813) B1442813
theorem B961891 : Blo 960589 961891 := bstep (se 1 (by rfl) ⟨721418, by rfl⟩ : syracuseStep 961891 = 1442837) B1442837
theorem B961907 : Blo 960589 961907 := bstep (se 1 (by rfl) ⟨721430, by rfl⟩ : syracuseStep 961907 = 1442861) B1442861
theorem B961923 : Blo 960589 961923 := bstep (se 1 (by rfl) ⟨721442, by rfl⟩ : syracuseStep 961923 = 1442885) B1442885
theorem B7810445 : Blo 960589 7810445 := bstep (se 3 (by rfl) ⟨1464458, by rfl⟩ : syracuseStep 7810445 = 2928917) B2928917
theorem B961939 : Blo 960589 961939 := bstep (se 1 (by rfl) ⟨721454, by rfl⟩ : syracuseStep 961939 = 1442909) B1442909
theorem B961955 : Blo 960589 961955 := bstep (se 1 (by rfl) ⟨721466, by rfl⟩ : syracuseStep 961955 = 1442933) B1442933
theorem B961971 : Blo 960589 961971 := bstep (se 1 (by rfl) ⟨721478, by rfl⟩ : syracuseStep 961971 = 1442957) B1442957
theorem B961987 : Blo 960589 961987 := bstep (se 1 (by rfl) ⟨721490, by rfl⟩ : syracuseStep 961987 = 1442981) B1442981
theorem B1027523 : Blo 960589 1027523 := bstep (se 1 (by rfl) ⟨770642, by rfl⟩ : syracuseStep 1027523 = 1541285) B1541285
theorem B6172109 : Blo 960589 6172109 := bstep (se 3 (by rfl) ⟨1157270, by rfl⟩ : syracuseStep 6172109 = 2314541) B2314541
theorem B962003 : Blo 960589 962003 := bstep (se 1 (by rfl) ⟨721502, by rfl⟩ : syracuseStep 962003 = 1443005) B1443005
theorem B3648995 : Blo 960589 3648995 := bstep (se 1 (by rfl) ⟨2736746, by rfl⟩ : syracuseStep 3648995 = 5473493) B5473493
theorem B962019 : Blo 960589 962019 := bstep (se 1 (by rfl) ⟨721514, by rfl⟩ : syracuseStep 962019 = 1443029) B1443029
theorem B3649009 : Blo 960589 3649009 := bstep (se 2 (by rfl) ⟨1368378, by rfl⟩ : syracuseStep 3649009 = 2736757) B2736757
theorem B962035 : Blo 960589 962035 := bstep (se 1 (by rfl) ⟨721526, by rfl⟩ : syracuseStep 962035 = 1443053) B1443053
theorem B962051 : Blo 960589 962051 := bstep (se 1 (by rfl) ⟨721538, by rfl⟩ : syracuseStep 962051 = 1443077) B1443077
theorem B962067 : Blo 960589 962067 := bstep (se 1 (by rfl) ⟨721550, by rfl⟩ : syracuseStep 962067 = 1443101) B1443101
theorem B962083 : Blo 960589 962083 := bstep (se 1 (by rfl) ⟨721562, by rfl⟩ : syracuseStep 962083 = 1443125) B1443125
theorem B962099 : Blo 960589 962099 := bstep (se 1 (by rfl) ⟨721574, by rfl⟩ : syracuseStep 962099 = 1443149) B1443149
theorem B962115 : Blo 960589 962115 := bstep (se 1 (by rfl) ⟨721586, by rfl⟩ : syracuseStep 962115 = 1443173) B1443173
theorem B1027651 : Blo 960589 1027651 := bstep (se 1 (by rfl) ⟨770738, by rfl⟩ : syracuseStep 1027651 = 1541477) B1541477
theorem B962131 : Blo 960589 962131 := bstep (se 1 (by rfl) ⟨721598, by rfl⟩ : syracuseStep 962131 = 1443197) B1443197
theorem B962147 : Blo 960589 962147 := bstep (se 1 (by rfl) ⟨721610, by rfl⟩ : syracuseStep 962147 = 1443221) B1443221
theorem B5484131 : Blo 960589 5484131 := bstep (se 1 (by rfl) ⟨4113098, by rfl⟩ : syracuseStep 5484131 = 8226197) B8226197
theorem B962163 : Blo 960589 962163 := bstep (se 1 (by rfl) ⟨721622, by rfl⟩ : syracuseStep 962163 = 1443245) B1443245
theorem B962179 : Blo 960589 962179 := bstep (se 1 (by rfl) ⟨721634, by rfl⟩ : syracuseStep 962179 = 1443269) B1443269
theorem B962195 : Blo 960589 962195 := bstep (se 1 (by rfl) ⟨721646, by rfl⟩ : syracuseStep 962195 = 1443293) B1443293
theorem B962211 : Blo 960589 962211 := bstep (se 1 (by rfl) ⟨721658, by rfl⟩ : syracuseStep 962211 = 1443317) B1443317
theorem B962227 : Blo 960589 962227 := bstep (se 1 (by rfl) ⟨721670, by rfl⟩ : syracuseStep 962227 = 1443341) B1443341
theorem B962243 : Blo 960589 962243 := bstep (se 1 (by rfl) ⟨721682, by rfl⟩ : syracuseStep 962243 = 1443365) B1443365
theorem B962259 : Blo 960589 962259 := bstep (se 1 (by rfl) ⟨721694, by rfl⟩ : syracuseStep 962259 = 1443389) B1443389
theorem B962275 : Blo 960589 962275 := bstep (se 1 (by rfl) ⟨721706, by rfl⟩ : syracuseStep 962275 = 1443413) B1443413
theorem B962291 : Blo 960589 962291 := bstep (se 1 (by rfl) ⟨721718, by rfl⟩ : syracuseStep 962291 = 1443437) B1443437
theorem B962307 : Blo 960589 962307 := bstep (se 1 (by rfl) ⟨721730, by rfl⟩ : syracuseStep 962307 = 1443461) B1443461
theorem B6926093 : Blo 960589 6926093 := bstep (se 3 (by rfl) ⟨1298642, by rfl⟩ : syracuseStep 6926093 = 2597285) B2597285
theorem B962323 : Blo 960589 962323 := bstep (se 1 (by rfl) ⟨721742, by rfl⟩ : syracuseStep 962323 = 1443485) B1443485
theorem B962339 : Blo 960589 962339 := bstep (se 1 (by rfl) ⟨721754, by rfl⟩ : syracuseStep 962339 = 1443509) B1443509
theorem B962355 : Blo 960589 962355 := bstep (se 1 (by rfl) ⟨721766, by rfl⟩ : syracuseStep 962355 = 1443533) B1443533
theorem B962371 : Blo 960589 962371 := bstep (se 1 (by rfl) ⟨721778, by rfl⟩ : syracuseStep 962371 = 1443557) B1443557
theorem B962387 : Blo 960589 962387 := bstep (se 1 (by rfl) ⟨721790, by rfl⟩ : syracuseStep 962387 = 1443581) B1443581
theorem B962403 : Blo 960589 962403 := bstep (se 1 (by rfl) ⟨721802, by rfl⟩ : syracuseStep 962403 = 1443605) B1443605
theorem B3288941 : Blo 960589 3288941 := bstep (se 3 (by rfl) ⟨616676, by rfl⟩ : syracuseStep 3288941 = 1233353) B1233353
theorem B962419 : Blo 960589 962419 := bstep (se 1 (by rfl) ⟨721814, by rfl⟩ : syracuseStep 962419 = 1443629) B1443629
theorem B962435 : Blo 960589 962435 := bstep (se 1 (by rfl) ⟨721826, by rfl⟩ : syracuseStep 962435 = 1443653) B1443653
theorem B962451 : Blo 960589 962451 := bstep (se 1 (by rfl) ⟨721838, by rfl⟩ : syracuseStep 962451 = 1443677) B1443677
theorem B962467 : Blo 960589 962467 := bstep (se 1 (by rfl) ⟨721850, by rfl⟩ : syracuseStep 962467 = 1443701) B1443701
theorem B962483 : Blo 960589 962483 := bstep (se 1 (by rfl) ⟨721862, by rfl⟩ : syracuseStep 962483 = 1443725) B1443725
theorem B962499 : Blo 960589 962499 := bstep (se 1 (by rfl) ⟨721874, by rfl⟩ : syracuseStep 962499 = 1443749) B1443749
theorem B962515 : Blo 960589 962515 := bstep (se 1 (by rfl) ⟨721886, by rfl⟩ : syracuseStep 962515 = 1443773) B1443773
theorem B962531 : Blo 960589 962531 := bstep (se 1 (by rfl) ⟨721898, by rfl⟩ : syracuseStep 962531 = 1443797) B1443797
theorem B962547 : Blo 960589 962547 := bstep (se 1 (by rfl) ⟨721910, by rfl⟩ : syracuseStep 962547 = 1443821) B1443821
theorem B962563 : Blo 960589 962563 := bstep (se 1 (by rfl) ⟨721922, by rfl⟩ : syracuseStep 962563 = 1443845) B1443845
theorem B962579 : Blo 960589 962579 := bstep (se 1 (by rfl) ⟨721934, by rfl⟩ : syracuseStep 962579 = 1443869) B1443869
theorem B962595 : Blo 960589 962595 := bstep (se 1 (by rfl) ⟨721946, by rfl⟩ : syracuseStep 962595 = 1443893) B1443893
theorem B962611 : Blo 960589 962611 := bstep (se 1 (by rfl) ⟨721958, by rfl⟩ : syracuseStep 962611 = 1443917) B1443917
theorem B962627 : Blo 960589 962627 := bstep (se 1 (by rfl) ⟨721970, by rfl⟩ : syracuseStep 962627 = 1443941) B1443941
theorem B10956869 : Blo 960589 10956869 := bstep (se 4 (by rfl) ⟨1027206, by rfl⟩ : syracuseStep 10956869 = 2054413) B2054413
theorem B962643 : Blo 960589 962643 := bstep (se 1 (by rfl) ⟨721982, by rfl⟩ : syracuseStep 962643 = 1443965) B1443965
theorem B962659 : Blo 960589 962659 := bstep (se 1 (by rfl) ⟨721994, by rfl⟩ : syracuseStep 962659 = 1443989) B1443989
theorem B962675 : Blo 960589 962675 := bstep (se 1 (by rfl) ⟨722006, by rfl⟩ : syracuseStep 962675 = 1444013) B1444013
theorem B962691 : Blo 960589 962691 := bstep (se 1 (by rfl) ⟨722018, by rfl⟩ : syracuseStep 962691 = 1444037) B1444037
theorem B962707 : Blo 960589 962707 := bstep (se 1 (by rfl) ⟨722030, by rfl⟩ : syracuseStep 962707 = 1444061) B1444061
theorem B962723 : Blo 960589 962723 := bstep (se 1 (by rfl) ⟨722042, by rfl⟩ : syracuseStep 962723 = 1444085) B1444085
theorem B962739 : Blo 960589 962739 := bstep (se 1 (by rfl) ⟨722054, by rfl⟩ : syracuseStep 962739 = 1444109) B1444109
theorem B962755 : Blo 960589 962755 := bstep (se 1 (by rfl) ⟨722066, by rfl⟩ : syracuseStep 962755 = 1444133) B1444133
theorem B962771 : Blo 960589 962771 := bstep (se 1 (by rfl) ⟨722078, by rfl⟩ : syracuseStep 962771 = 1444157) B1444157
theorem B962787 : Blo 960589 962787 := bstep (se 1 (by rfl) ⟨722090, by rfl⟩ : syracuseStep 962787 = 1444181) B1444181
theorem B2437361 : Blo 960589 2437361 := bstep (se 2 (by rfl) ⟨914010, by rfl⟩ : syracuseStep 2437361 = 1828021) B1828021
theorem B962803 : Blo 960589 962803 := bstep (se 1 (by rfl) ⟨722102, by rfl⟩ : syracuseStep 962803 = 1444205) B1444205
theorem B962819 : Blo 960589 962819 := bstep (se 1 (by rfl) ⟨722114, by rfl⟩ : syracuseStep 962819 = 1444229) B1444229
theorem B962835 : Blo 960589 962835 := bstep (se 1 (by rfl) ⟨722126, by rfl⟩ : syracuseStep 962835 = 1444253) B1444253
theorem B962851 : Blo 960589 962851 := bstep (se 1 (by rfl) ⟨722138, by rfl⟩ : syracuseStep 962851 = 1444277) B1444277
theorem B2437411 : Blo 960589 2437411 := bstep (se 1 (by rfl) ⟨1828058, by rfl⟩ : syracuseStep 2437411 = 3656117) B3656117
theorem B962867 : Blo 960589 962867 := bstep (se 1 (by rfl) ⟨722150, by rfl⟩ : syracuseStep 962867 = 1444301) B1444301
theorem B962883 : Blo 960589 962883 := bstep (se 1 (by rfl) ⟨722162, by rfl⟩ : syracuseStep 962883 = 1444325) B1444325
theorem B962899 : Blo 960589 962899 := bstep (se 1 (by rfl) ⟨722174, by rfl⟩ : syracuseStep 962899 = 1444349) B1444349
theorem B962915 : Blo 960589 962915 := bstep (se 1 (by rfl) ⟨722186, by rfl⟩ : syracuseStep 962915 = 1444373) B1444373
theorem B962931 : Blo 960589 962931 := bstep (se 1 (by rfl) ⟨722198, by rfl⟩ : syracuseStep 962931 = 1444397) B1444397
theorem B1028467 : Blo 960589 1028467 := bstep (se 1 (by rfl) ⟨771350, by rfl⟩ : syracuseStep 1028467 = 1542701) B1542701
theorem B962947 : Blo 960589 962947 := bstep (se 1 (by rfl) ⟨722210, by rfl⟩ : syracuseStep 962947 = 1444421) B1444421
theorem B962963 : Blo 960589 962963 := bstep (se 1 (by rfl) ⟨722222, by rfl⟩ : syracuseStep 962963 = 1444445) B1444445
theorem B962979 : Blo 960589 962979 := bstep (se 1 (by rfl) ⟨722234, by rfl⟩ : syracuseStep 962979 = 1444469) B1444469
theorem B2437553 : Blo 960589 2437553 := bstep (se 2 (by rfl) ⟨914082, by rfl⟩ : syracuseStep 2437553 = 1828165) B1828165
theorem B962995 : Blo 960589 962995 := bstep (se 1 (by rfl) ⟨722246, by rfl⟩ : syracuseStep 962995 = 1444493) B1444493
theorem B963011 : Blo 960589 963011 := bstep (se 1 (by rfl) ⟨722258, by rfl⟩ : syracuseStep 963011 = 1444517) B1444517
theorem B963027 : Blo 960589 963027 := bstep (se 1 (by rfl) ⟨722270, by rfl⟩ : syracuseStep 963027 = 1444541) B1444541
theorem B963043 : Blo 960589 963043 := bstep (se 1 (by rfl) ⟨722282, by rfl⟩ : syracuseStep 963043 = 1444565) B1444565
theorem B963059 : Blo 960589 963059 := bstep (se 1 (by rfl) ⟨722294, by rfl⟩ : syracuseStep 963059 = 1444589) B1444589
theorem B963075 : Blo 960589 963075 := bstep (se 1 (by rfl) ⟨722306, by rfl⟩ : syracuseStep 963075 = 1444613) B1444613
theorem B963091 : Blo 960589 963091 := bstep (se 1 (by rfl) ⟨722318, by rfl⟩ : syracuseStep 963091 = 1444637) B1444637
theorem B963107 : Blo 960589 963107 := bstep (se 1 (by rfl) ⟨722330, by rfl⟩ : syracuseStep 963107 = 1444661) B1444661
theorem B963123 : Blo 960589 963123 := bstep (se 1 (by rfl) ⟨722342, by rfl⟩ : syracuseStep 963123 = 1444685) B1444685
theorem B963139 : Blo 960589 963139 := bstep (se 1 (by rfl) ⟨722354, by rfl⟩ : syracuseStep 963139 = 1444709) B1444709
theorem B963155 : Blo 960589 963155 := bstep (se 1 (by rfl) ⟨722366, by rfl⟩ : syracuseStep 963155 = 1444733) B1444733
theorem B963171 : Blo 960589 963171 := bstep (se 1 (by rfl) ⟨722378, by rfl⟩ : syracuseStep 963171 = 1444757) B1444757
theorem B963187 : Blo 960589 963187 := bstep (se 1 (by rfl) ⟨722390, by rfl⟩ : syracuseStep 963187 = 1444781) B1444781
theorem B963203 : Blo 960589 963203 := bstep (se 1 (by rfl) ⟨722402, by rfl⟩ : syracuseStep 963203 = 1444805) B1444805
theorem B963219 : Blo 960589 963219 := bstep (se 1 (by rfl) ⟨722414, by rfl⟩ : syracuseStep 963219 = 1444829) B1444829
theorem B4108963 : Blo 960589 4108963 := bstep (se 1 (by rfl) ⟨3081722, by rfl⟩ : syracuseStep 4108963 = 6163445) B6163445
theorem B963235 : Blo 960589 963235 := bstep (se 1 (by rfl) ⟨722426, by rfl⟩ : syracuseStep 963235 = 1444853) B1444853
theorem B963251 : Blo 960589 963251 := bstep (se 1 (by rfl) ⟨722438, by rfl⟩ : syracuseStep 963251 = 1444877) B1444877
theorem B963267 : Blo 960589 963267 := bstep (se 1 (by rfl) ⟨722450, by rfl⟩ : syracuseStep 963267 = 1444901) B1444901
theorem B963283 : Blo 960589 963283 := bstep (se 1 (by rfl) ⟨722462, by rfl⟩ : syracuseStep 963283 = 1444925) B1444925
theorem B963299 : Blo 960589 963299 := bstep (se 1 (by rfl) ⟨722474, by rfl⟩ : syracuseStep 963299 = 1444949) B1444949
theorem B963315 : Blo 960589 963315 := bstep (se 1 (by rfl) ⟨722486, by rfl⟩ : syracuseStep 963315 = 1444973) B1444973
theorem B963331 : Blo 960589 963331 := bstep (se 1 (by rfl) ⟨722498, by rfl⟩ : syracuseStep 963331 = 1444997) B1444997
theorem B963347 : Blo 960589 963347 := bstep (se 1 (by rfl) ⟨722510, by rfl⟩ : syracuseStep 963347 = 1445021) B1445021
theorem B963363 : Blo 960589 963363 := bstep (se 1 (by rfl) ⟨722522, by rfl⟩ : syracuseStep 963363 = 1445045) B1445045
theorem B963379 : Blo 960589 963379 := bstep (se 1 (by rfl) ⟨722534, by rfl⟩ : syracuseStep 963379 = 1445069) B1445069
theorem B963395 : Blo 960589 963395 := bstep (se 1 (by rfl) ⟨722546, by rfl⟩ : syracuseStep 963395 = 1445093) B1445093
theorem B963411 : Blo 960589 963411 := bstep (se 1 (by rfl) ⟨722558, by rfl⟩ : syracuseStep 963411 = 1445117) B1445117
theorem B963427 : Blo 960589 963427 := bstep (se 1 (by rfl) ⟨722570, by rfl⟩ : syracuseStep 963427 = 1445141) B1445141
theorem B963443 : Blo 960589 963443 := bstep (se 1 (by rfl) ⟨722582, by rfl⟩ : syracuseStep 963443 = 1445165) B1445165
theorem B963459 : Blo 960589 963459 := bstep (se 1 (by rfl) ⟨722594, by rfl⟩ : syracuseStep 963459 = 1445189) B1445189
theorem B3289997 : Blo 960589 3289997 := bstep (se 3 (by rfl) ⟨616874, by rfl⟩ : syracuseStep 3289997 = 1233749) B1233749
theorem B23442317 : Blo 960589 23442317 := bstep (se 3 (by rfl) ⟨4395434, by rfl⟩ : syracuseStep 23442317 = 8790869) B8790869
theorem B963475 : Blo 960589 963475 := bstep (se 1 (by rfl) ⟨722606, by rfl⟩ : syracuseStep 963475 = 1445213) B1445213
theorem B3650467 : Blo 960589 3650467 := bstep (se 1 (by rfl) ⟨2737850, by rfl⟩ : syracuseStep 3650467 = 5475701) B5475701
theorem B963491 : Blo 960589 963491 := bstep (se 1 (by rfl) ⟨722618, by rfl⟩ : syracuseStep 963491 = 1445237) B1445237
theorem B963507 : Blo 960589 963507 := bstep (se 1 (by rfl) ⟨722630, by rfl⟩ : syracuseStep 963507 = 1445261) B1445261
theorem B963523 : Blo 960589 963523 := bstep (se 1 (by rfl) ⟨722642, by rfl⟩ : syracuseStep 963523 = 1445285) B1445285
theorem B963539 : Blo 960589 963539 := bstep (se 1 (by rfl) ⟨722654, by rfl⟩ : syracuseStep 963539 = 1445309) B1445309
theorem B963555 : Blo 960589 963555 := bstep (se 1 (by rfl) ⟨722666, by rfl⟩ : syracuseStep 963555 = 1445333) B1445333
theorem B963571 : Blo 960589 963571 := bstep (se 1 (by rfl) ⟨722678, by rfl⟩ : syracuseStep 963571 = 1445357) B1445357
theorem B963587 : Blo 960589 963587 := bstep (se 1 (by rfl) ⟨722690, by rfl⟩ : syracuseStep 963587 = 1445381) B1445381
theorem B963603 : Blo 960589 963603 := bstep (se 1 (by rfl) ⟨722702, by rfl⟩ : syracuseStep 963603 = 1445405) B1445405
theorem B963619 : Blo 960589 963619 := bstep (se 1 (by rfl) ⟨722714, by rfl⟩ : syracuseStep 963619 = 1445429) B1445429
theorem B963635 : Blo 960589 963635 := bstep (se 1 (by rfl) ⟨722726, by rfl⟩ : syracuseStep 963635 = 1445453) B1445453
theorem B963651 : Blo 960589 963651 := bstep (se 1 (by rfl) ⟨722738, by rfl⟩ : syracuseStep 963651 = 1445477) B1445477
theorem B963667 : Blo 960589 963667 := bstep (se 1 (by rfl) ⟨722750, by rfl⟩ : syracuseStep 963667 = 1445501) B1445501
theorem B963683 : Blo 960589 963683 := bstep (se 1 (by rfl) ⟨722762, by rfl⟩ : syracuseStep 963683 = 1445525) B1445525
theorem B8795249 : Blo 960589 8795249 := bstep (se 2 (by rfl) ⟨3298218, by rfl⟩ : syracuseStep 8795249 = 6596437) B6596437
theorem B963699 : Blo 960589 963699 := bstep (se 1 (by rfl) ⟨722774, by rfl⟩ : syracuseStep 963699 = 1445549) B1445549
theorem B963715 : Blo 960589 963715 := bstep (se 1 (by rfl) ⟨722786, by rfl⟩ : syracuseStep 963715 = 1445573) B1445573
theorem B963731 : Blo 960589 963731 := bstep (se 1 (by rfl) ⟨722798, by rfl⟩ : syracuseStep 963731 = 1445597) B1445597
theorem B963747 : Blo 960589 963747 := bstep (se 1 (by rfl) ⟨722810, by rfl⟩ : syracuseStep 963747 = 1445621) B1445621
theorem B963763 : Blo 960589 963763 := bstep (se 1 (by rfl) ⟨722822, by rfl⟩ : syracuseStep 963763 = 1445645) B1445645
theorem B963779 : Blo 960589 963779 := bstep (se 1 (by rfl) ⟨722834, by rfl⟩ : syracuseStep 963779 = 1445669) B1445669
theorem B963795 : Blo 960589 963795 := bstep (se 1 (by rfl) ⟨722846, by rfl⟩ : syracuseStep 963795 = 1445693) B1445693
theorem B963811 : Blo 960589 963811 := bstep (se 1 (by rfl) ⟨722858, by rfl⟩ : syracuseStep 963811 = 1445717) B1445717
theorem B963827 : Blo 960589 963827 := bstep (se 1 (by rfl) ⟨722870, by rfl⟩ : syracuseStep 963827 = 1445741) B1445741
theorem B963843 : Blo 960589 963843 := bstep (se 1 (by rfl) ⟨722882, by rfl⟩ : syracuseStep 963843 = 1445765) B1445765
theorem B963859 : Blo 960589 963859 := bstep (se 1 (by rfl) ⟨722894, by rfl⟩ : syracuseStep 963859 = 1445789) B1445789
theorem B963875 : Blo 960589 963875 := bstep (se 1 (by rfl) ⟨722906, by rfl⟩ : syracuseStep 963875 = 1445813) B1445813
theorem B963891 : Blo 960589 963891 := bstep (se 1 (by rfl) ⟨722918, by rfl⟩ : syracuseStep 963891 = 1445837) B1445837
theorem B963907 : Blo 960589 963907 := bstep (se 1 (by rfl) ⟨722930, by rfl⟩ : syracuseStep 963907 = 1445861) B1445861
theorem B963923 : Blo 960589 963923 := bstep (se 1 (by rfl) ⟨722942, by rfl⟩ : syracuseStep 963923 = 1445885) B1445885
theorem B963939 : Blo 960589 963939 := bstep (se 1 (by rfl) ⟨722954, by rfl⟩ : syracuseStep 963939 = 1445909) B1445909
theorem B963955 : Blo 960589 963955 := bstep (se 1 (by rfl) ⟨722966, by rfl⟩ : syracuseStep 963955 = 1445933) B1445933
theorem B963971 : Blo 960589 963971 := bstep (se 1 (by rfl) ⟨722978, by rfl⟩ : syracuseStep 963971 = 1445957) B1445957
theorem B2438545 : Blo 960589 2438545 := bstep (se 2 (by rfl) ⟨914454, by rfl⟩ : syracuseStep 2438545 = 1828909) B1828909
theorem B963987 : Blo 960589 963987 := bstep (se 1 (by rfl) ⟨722990, by rfl⟩ : syracuseStep 963987 = 1445981) B1445981
theorem B964003 : Blo 960589 964003 := bstep (se 1 (by rfl) ⟨723002, by rfl⟩ : syracuseStep 964003 = 1446005) B1446005
theorem B964019 : Blo 960589 964019 := bstep (se 1 (by rfl) ⟨723014, by rfl⟩ : syracuseStep 964019 = 1446029) B1446029
theorem B964035 : Blo 960589 964035 := bstep (se 1 (by rfl) ⟨723026, by rfl⟩ : syracuseStep 964035 = 1446053) B1446053
theorem B964051 : Blo 960589 964051 := bstep (se 1 (by rfl) ⟨723038, by rfl⟩ : syracuseStep 964051 = 1446077) B1446077
theorem B964067 : Blo 960589 964067 := bstep (se 1 (by rfl) ⟨723050, by rfl⟩ : syracuseStep 964067 = 1446101) B1446101
theorem B964083 : Blo 960589 964083 := bstep (se 1 (by rfl) ⟨723062, by rfl⟩ : syracuseStep 964083 = 1446125) B1446125
theorem B964099 : Blo 960589 964099 := bstep (se 1 (by rfl) ⟨723074, by rfl⟩ : syracuseStep 964099 = 1446149) B1446149
theorem B964115 : Blo 960589 964115 := bstep (se 1 (by rfl) ⟨723086, by rfl⟩ : syracuseStep 964115 = 1446173) B1446173
theorem B964131 : Blo 960589 964131 := bstep (se 1 (by rfl) ⟨723098, by rfl⟩ : syracuseStep 964131 = 1446197) B1446197
theorem B964147 : Blo 960589 964147 := bstep (se 1 (by rfl) ⟨723110, by rfl⟩ : syracuseStep 964147 = 1446221) B1446221
theorem B964163 : Blo 960589 964163 := bstep (se 1 (by rfl) ⟨723122, by rfl⟩ : syracuseStep 964163 = 1446245) B1446245
theorem B964179 : Blo 960589 964179 := bstep (se 1 (by rfl) ⟨723134, by rfl⟩ : syracuseStep 964179 = 1446269) B1446269
theorem B964195 : Blo 960589 964195 := bstep (se 1 (by rfl) ⟨723146, by rfl⟩ : syracuseStep 964195 = 1446293) B1446293
theorem B964211 : Blo 960589 964211 := bstep (se 1 (by rfl) ⟨723158, by rfl⟩ : syracuseStep 964211 = 1446317) B1446317
theorem B964227 : Blo 960589 964227 := bstep (se 1 (by rfl) ⟨723170, by rfl⟩ : syracuseStep 964227 = 1446341) B1446341
theorem B964243 : Blo 960589 964243 := bstep (se 1 (by rfl) ⟨723182, by rfl⟩ : syracuseStep 964243 = 1446365) B1446365
theorem B2438819 : Blo 960589 2438819 := bstep (se 1 (by rfl) ⟨1829114, by rfl⟩ : syracuseStep 2438819 = 3658229) B3658229
theorem B964259 : Blo 960589 964259 := bstep (se 1 (by rfl) ⟨723194, by rfl⟩ : syracuseStep 964259 = 1446389) B1446389
theorem B964275 : Blo 960589 964275 := bstep (se 1 (by rfl) ⟨723206, by rfl⟩ : syracuseStep 964275 = 1446413) B1446413
theorem B964291 : Blo 960589 964291 := bstep (se 1 (by rfl) ⟨723218, by rfl⟩ : syracuseStep 964291 = 1446437) B1446437
theorem B964307 : Blo 960589 964307 := bstep (se 1 (by rfl) ⟨723230, by rfl⟩ : syracuseStep 964307 = 1446461) B1446461
theorem B964323 : Blo 960589 964323 := bstep (se 1 (by rfl) ⟨723242, by rfl⟩ : syracuseStep 964323 = 1446485) B1446485
theorem B964339 : Blo 960589 964339 := bstep (se 1 (by rfl) ⟨723254, by rfl⟩ : syracuseStep 964339 = 1446509) B1446509
theorem B964355 : Blo 960589 964355 := bstep (se 1 (by rfl) ⟨723266, by rfl⟩ : syracuseStep 964355 = 1446533) B1446533
theorem B964371 : Blo 960589 964371 := bstep (se 1 (by rfl) ⟨723278, by rfl⟩ : syracuseStep 964371 = 1446557) B1446557
theorem B964387 : Blo 960589 964387 := bstep (se 1 (by rfl) ⟨723290, by rfl⟩ : syracuseStep 964387 = 1446581) B1446581
theorem B964403 : Blo 960589 964403 := bstep (se 1 (by rfl) ⟨723302, by rfl⟩ : syracuseStep 964403 = 1446605) B1446605
theorem B964419 : Blo 960589 964419 := bstep (se 1 (by rfl) ⟨723314, by rfl⟩ : syracuseStep 964419 = 1446629) B1446629
theorem B2930509 : Blo 960589 2930509 := bstep (se 3 (by rfl) ⟨549470, by rfl⟩ : syracuseStep 2930509 = 1098941) B1098941
theorem B964435 : Blo 960589 964435 := bstep (se 1 (by rfl) ⟨723326, by rfl⟩ : syracuseStep 964435 = 1446653) B1446653
theorem B2439011 : Blo 960589 2439011 := bstep (se 1 (by rfl) ⟨1829258, by rfl⟩ : syracuseStep 2439011 = 3658517) B3658517
theorem B964451 : Blo 960589 964451 := bstep (se 1 (by rfl) ⟨723338, by rfl⟩ : syracuseStep 964451 = 1446677) B1446677
theorem B4110193 : Blo 960589 4110193 := bstep (se 2 (by rfl) ⟨1541322, by rfl⟩ : syracuseStep 4110193 = 3082645) B3082645
theorem B964467 : Blo 960589 964467 := bstep (se 1 (by rfl) ⟨723350, by rfl⟩ : syracuseStep 964467 = 1446701) B1446701
theorem B964483 : Blo 960589 964483 := bstep (se 1 (by rfl) ⟨723362, by rfl⟩ : syracuseStep 964483 = 1446725) B1446725
theorem B964499 : Blo 960589 964499 := bstep (se 1 (by rfl) ⟨723374, by rfl⟩ : syracuseStep 964499 = 1446749) B1446749
theorem B964515 : Blo 960589 964515 := bstep (se 1 (by rfl) ⟨723386, by rfl⟩ : syracuseStep 964515 = 1446773) B1446773
theorem B964531 : Blo 960589 964531 := bstep (se 1 (by rfl) ⟨723398, by rfl⟩ : syracuseStep 964531 = 1446797) B1446797
theorem B964547 : Blo 960589 964547 := bstep (se 1 (by rfl) ⟨723410, by rfl⟩ : syracuseStep 964547 = 1446821) B1446821
theorem B964563 : Blo 960589 964563 := bstep (se 1 (by rfl) ⟨723422, by rfl⟩ : syracuseStep 964563 = 1446845) B1446845
theorem B964579 : Blo 960589 964579 := bstep (se 1 (by rfl) ⟨723434, by rfl⟩ : syracuseStep 964579 = 1446869) B1446869
theorem B4864049 : Blo 960589 4864049 := bstep (se 2 (by rfl) ⟨1824018, by rfl⟩ : syracuseStep 4864049 = 3648037) B3648037
theorem B2504753 : Blo 960589 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B1391137 : Blo 960589 1391137 := bstep (se 2 (by rfl) ⟨521676, by rfl⟩ : syracuseStep 1391137 = 1043353) B1043353
theorem B6929009 : Blo 960589 6929009 := bstep (se 2 (by rfl) ⟨2598378, by rfl⟩ : syracuseStep 6929009 = 5196757) B5196757
theorem B5487365 : Blo 960589 5487365 := bstep (se 4 (by rfl) ⟨514440, by rfl⟩ : syracuseStep 5487365 = 1028881) B1028881
theorem B2439953 : Blo 960589 2439953 := bstep (se 2 (by rfl) ⟨914982, by rfl⟩ : syracuseStep 2439953 = 1829965) B1829965
theorem B2440003 : Blo 960589 2440003 := bstep (se 1 (by rfl) ⟨1830002, by rfl⟩ : syracuseStep 2440003 = 3660005) B3660005
theorem B9255779 : Blo 960589 9255779 := bstep (se 1 (by rfl) ⟨6941834, by rfl⟩ : syracuseStep 9255779 = 13883669) B13883669
theorem B8240069 : Blo 960589 8240069 := bstep (se 4 (by rfl) ⟨772506, by rfl⟩ : syracuseStep 8240069 = 1545013) B1545013
theorem B2440145 : Blo 960589 2440145 := bstep (se 2 (by rfl) ⟨915054, by rfl⟩ : syracuseStep 2440145 = 1830109) B1830109
theorem B3652685 : Blo 960589 3652685 := bstep (se 3 (by rfl) ⟨684878, by rfl⟩ : syracuseStep 3652685 = 1369757) B1369757
theorem B1621073 : Blo 960589 1621073 := bstep (se 2 (by rfl) ⟨607902, by rfl⟩ : syracuseStep 1621073 = 1215805) B1215805
theorem B5487821 : Blo 960589 5487821 := bstep (se 3 (by rfl) ⟨1028966, by rfl⟩ : syracuseStep 5487821 = 2057933) B2057933
theorem B1621201 : Blo 960589 1621201 := bstep (se 2 (by rfl) ⟨607950, by rfl⟩ : syracuseStep 1621201 = 1215901) B1215901
theorem B2604269 : Blo 960589 2604269 := bstep (se 3 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 2604269 = 976601) B976601
theorem B1621235 : Blo 960589 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B5487907 : Blo 960589 5487907 := bstep (se 1 (by rfl) ⟨4115930, by rfl⟩ : syracuseStep 5487907 = 8231861) B8231861
theorem B2342225 : Blo 960589 2342225 := bstep (se 2 (by rfl) ⟨878334, by rfl⟩ : syracuseStep 2342225 = 1756669) B1756669
theorem B1621363 : Blo 960589 1621363 := bstep (se 1 (by rfl) ⟨1216022, by rfl⟩ : syracuseStep 1621363 = 2432045) B2432045
theorem B1392049 : Blo 960589 1392049 := bstep (se 2 (by rfl) ⟨522018, by rfl⟩ : syracuseStep 1392049 = 1044037) B1044037
theorem B4865507 : Blo 960589 4865507 := bstep (se 1 (by rfl) ⟨3649130, by rfl⟩ : syracuseStep 4865507 = 7298261) B7298261
theorem B1621505 : Blo 960589 1621505 := bstep (se 2 (by rfl) ⟨608064, by rfl⟩ : syracuseStep 1621505 = 1216129) B1216129
theorem B5193229 : Blo 960589 5193229 := bstep (se 3 (by rfl) ⟨973730, by rfl⟩ : syracuseStep 5193229 = 1947461) B1947461
theorem B1621633 : Blo 960589 1621633 := bstep (se 2 (by rfl) ⟨608112, by rfl⟩ : syracuseStep 1621633 = 1216225) B1216225
theorem B1621667 : Blo 960589 1621667 := bstep (se 1 (by rfl) ⟨1216250, by rfl⟩ : syracuseStep 1621667 = 2432501) B2432501
theorem B1621795 : Blo 960589 1621795 := bstep (se 1 (by rfl) ⟨1216346, by rfl⟩ : syracuseStep 1621795 = 2432693) B2432693
theorem B1097555 : Blo 960589 1097555 := bstep (se 1 (by rfl) ⟨823166, by rfl⟩ : syracuseStep 1097555 = 1646333) B1646333
theorem B7323533 : Blo 960589 7323533 := bstep (se 3 (by rfl) ⟨1373162, by rfl⟩ : syracuseStep 7323533 = 2746325) B2746325
theorem B1621937 : Blo 960589 1621937 := bstep (se 2 (by rfl) ⟨608226, by rfl⟩ : syracuseStep 1621937 = 1216453) B1216453
theorem B2441137 : Blo 960589 2441137 := bstep (se 2 (by rfl) ⟨915426, by rfl⟩ : syracuseStep 2441137 = 1830853) B1830853
theorem B2310083 : Blo 960589 2310083 := bstep (se 1 (by rfl) ⟨1732562, by rfl⟩ : syracuseStep 2310083 = 3465125) B3465125
theorem B1622065 : Blo 960589 1622065 := bstep (se 2 (by rfl) ⟨608274, by rfl⟩ : syracuseStep 1622065 = 1216549) B1216549
theorem B1622099 : Blo 960589 1622099 := bstep (se 1 (by rfl) ⟨1216574, by rfl⟩ : syracuseStep 1622099 = 2433149) B2433149
theorem B3293347 : Blo 960589 3293347 := bstep (se 1 (by rfl) ⟨2470010, by rfl⟩ : syracuseStep 3293347 = 4940021) B4940021
theorem B2441411 : Blo 960589 2441411 := bstep (se 1 (by rfl) ⟨1831058, by rfl⟩ : syracuseStep 2441411 = 3662117) B3662117
theorem B1622227 : Blo 960589 1622227 := bstep (se 1 (by rfl) ⟨1216670, by rfl⟩ : syracuseStep 1622227 = 2433341) B2433341
theorem B5193989 : Blo 960589 5193989 := bstep (se 4 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 5193989 = 973873) B973873
theorem B4866317 : Blo 960589 4866317 := bstep (se 3 (by rfl) ⟨912434, by rfl⟩ : syracuseStep 4866317 = 1824869) B1824869
theorem B6242609 : Blo 960589 6242609 := bstep (se 2 (by rfl) ⟨2340978, by rfl⟩ : syracuseStep 6242609 = 4681957) B4681957
theorem B1622369 : Blo 960589 1622369 := bstep (se 2 (by rfl) ⟨608388, by rfl⟩ : syracuseStep 1622369 = 1216777) B1216777
theorem B2441603 : Blo 960589 2441603 := bstep (se 1 (by rfl) ⟨1831202, by rfl⟩ : syracuseStep 2441603 = 3662405) B3662405
theorem B1622497 : Blo 960589 1622497 := bstep (se 2 (by rfl) ⟨608436, by rfl⟩ : syracuseStep 1622497 = 1216873) B1216873
theorem B1622531 : Blo 960589 1622531 := bstep (se 1 (by rfl) ⟨1216898, by rfl⟩ : syracuseStep 1622531 = 2433797) B2433797
theorem B1622659 : Blo 960589 1622659 := bstep (se 1 (by rfl) ⟨1216994, by rfl⟩ : syracuseStep 1622659 = 2433989) B2433989
theorem B3293827 : Blo 960589 3293827 := bstep (se 1 (by rfl) ⟨2470370, by rfl⟩ : syracuseStep 3293827 = 4940741) B4940741
theorem B2736803 : Blo 960589 2736803 := bstep (se 1 (by rfl) ⟨2052602, by rfl⟩ : syracuseStep 2736803 = 4105205) B4105205
theorem B2933425 : Blo 960589 2933425 := bstep (se 2 (by rfl) ⟨1100034, by rfl⟩ : syracuseStep 2933425 = 2200069) B2200069
theorem B2310851 : Blo 960589 2310851 := bstep (se 1 (by rfl) ⟨1733138, by rfl⟩ : syracuseStep 2310851 = 3466277) B3466277
theorem B1622801 : Blo 960589 1622801 := bstep (se 2 (by rfl) ⟨608550, by rfl⟩ : syracuseStep 1622801 = 1217101) B1217101
theorem B1622929 : Blo 960589 1622929 := bstep (se 2 (by rfl) ⟨608598, by rfl⟩ : syracuseStep 1622929 = 1217197) B1217197
theorem B1622963 : Blo 960589 1622963 := bstep (se 1 (by rfl) ⟨1217222, by rfl⟩ : syracuseStep 1622963 = 2434445) B2434445
theorem B1852355 : Blo 960589 1852355 := bstep (se 1 (by rfl) ⟨1389266, by rfl⟩ : syracuseStep 1852355 = 2778533) B2778533
theorem B1098787 : Blo 960589 1098787 := bstep (se 1 (by rfl) ⟨824090, by rfl⟩ : syracuseStep 1098787 = 1648181) B1648181
theorem B1623091 : Blo 960589 1623091 := bstep (se 1 (by rfl) ⟨1217318, by rfl⟩ : syracuseStep 1623091 = 2434637) B2434637
theorem B1623233 : Blo 960589 1623233 := bstep (se 2 (by rfl) ⟨608712, by rfl⟩ : syracuseStep 1623233 = 1217425) B1217425
theorem B2311409 : Blo 960589 2311409 := bstep (se 2 (by rfl) ⟨866778, by rfl⟩ : syracuseStep 2311409 = 1733557) B1733557
theorem B20792629 : Blo 960589 20792629 := bstep (se 5 (by rfl) ⟨974654, by rfl⟩ : syracuseStep 20792629 = 1949309) B1949309
theorem B1623361 : Blo 960589 1623361 := bstep (se 2 (by rfl) ⟨608760, by rfl⟩ : syracuseStep 1623361 = 1217521) B1217521
theorem B1623395 : Blo 960589 1623395 := bstep (se 1 (by rfl) ⟨1217546, by rfl⟩ : syracuseStep 1623395 = 2435093) B2435093
theorem B1623523 : Blo 960589 1623523 := bstep (se 1 (by rfl) ⟨1217642, by rfl⟩ : syracuseStep 1623523 = 2435285) B2435285
theorem B2606627 : Blo 960589 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B2311793 : Blo 960589 2311793 := bstep (se 2 (by rfl) ⟨866922, by rfl⟩ : syracuseStep 2311793 = 1733845) B1733845
theorem B1623665 : Blo 960589 1623665 := bstep (se 2 (by rfl) ⟨608874, by rfl⟩ : syracuseStep 1623665 = 1217749) B1217749
theorem B2311907 : Blo 960589 2311907 := bstep (se 1 (by rfl) ⟨1733930, by rfl⟩ : syracuseStep 2311907 = 3467861) B3467861
theorem B1623793 : Blo 960589 1623793 := bstep (se 2 (by rfl) ⟨608922, by rfl⟩ : syracuseStep 1623793 = 1217845) B1217845
theorem B10962701 : Blo 960589 10962701 := bstep (se 3 (by rfl) ⟨2055506, by rfl⟩ : syracuseStep 10962701 = 4111013) B4111013
theorem B3131149 : Blo 960589 3131149 := bstep (se 3 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 3131149 = 1174181) B1174181
theorem B1623827 : Blo 960589 1623827 := bstep (se 1 (by rfl) ⟨1217870, by rfl⟩ : syracuseStep 1623827 = 2435741) B2435741
theorem B14042933 : Blo 960589 14042933 := bstep (se 5 (by rfl) ⟨658262, by rfl⟩ : syracuseStep 14042933 = 1316525) B1316525
theorem B2738033 : Blo 960589 2738033 := bstep (se 2 (by rfl) ⟨1026762, by rfl⟩ : syracuseStep 2738033 = 2053525) B2053525
theorem B2312081 : Blo 960589 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B1623955 : Blo 960589 1623955 := bstep (se 1 (by rfl) ⟨1217966, by rfl⟩ : syracuseStep 1623955 = 2435933) B2435933
theorem B3655601 : Blo 960589 3655601 := bstep (se 2 (by rfl) ⟨1370850, by rfl⟩ : syracuseStep 3655601 = 2741701) B2741701
theorem B1624097 : Blo 960589 1624097 := bstep (se 2 (by rfl) ⟨609036, by rfl⟩ : syracuseStep 1624097 = 1218073) B1218073
theorem B5490737 : Blo 960589 5490737 := bstep (se 2 (by rfl) ⟨2059026, by rfl⟩ : syracuseStep 5490737 = 4118053) B4118053
theorem B16468109 : Blo 960589 16468109 := bstep (se 3 (by rfl) ⟨3087770, by rfl⟩ : syracuseStep 16468109 = 6175541) B6175541
theorem B1853585 : Blo 960589 1853585 := bstep (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) B1390189
theorem B1624225 : Blo 960589 1624225 := bstep (se 2 (by rfl) ⟨609084, by rfl⟩ : syracuseStep 1624225 = 1218169) B1218169
theorem B1624259 : Blo 960589 1624259 := bstep (se 1 (by rfl) ⟨1218194, by rfl⟩ : syracuseStep 1624259 = 2436389) B2436389
theorem B2607299 : Blo 960589 2607299 := bstep (se 1 (by rfl) ⟨1955474, by rfl⟩ : syracuseStep 2607299 = 3910949) B3910949
theorem B4114637 : Blo 960589 4114637 := bstep (se 3 (by rfl) ⟨771494, by rfl⟩ : syracuseStep 4114637 = 1542989) B1542989
theorem B1624387 : Blo 960589 1624387 := bstep (se 1 (by rfl) ⟨1218290, by rfl⟩ : syracuseStep 1624387 = 2436581) B2436581
theorem B1624529 : Blo 960589 1624529 := bstep (se 2 (by rfl) ⟨609198, by rfl⟩ : syracuseStep 1624529 = 1218397) B1218397
theorem B7817741 : Blo 960589 7817741 := bstep (se 3 (by rfl) ⟨1465826, by rfl⟩ : syracuseStep 7817741 = 2931653) B2931653
theorem B1624657 : Blo 960589 1624657 := bstep (se 2 (by rfl) ⟨609246, by rfl⟩ : syracuseStep 1624657 = 1218493) B1218493
theorem B1624691 : Blo 960589 1624691 := bstep (se 1 (by rfl) ⟨1218518, by rfl⟩ : syracuseStep 1624691 = 2437037) B2437037
theorem B1624819 : Blo 960589 1624819 := bstep (se 1 (by rfl) ⟨1218614, by rfl⟩ : syracuseStep 1624819 = 2437229) B2437229
theorem B1690417 : Blo 960589 1690417 := bstep (se 2 (by rfl) ⟨633906, by rfl⟩ : syracuseStep 1690417 = 1267813) B1267813
theorem B1461107 : Blo 960589 1461107 := bstep (se 1 (by rfl) ⟨1095830, by rfl⟩ : syracuseStep 1461107 = 2191661) B2191661
theorem B1624961 : Blo 960589 1624961 := bstep (se 2 (by rfl) ⟨609360, by rfl⟩ : syracuseStep 1624961 = 1218721) B1218721
theorem B4017059 : Blo 960589 4017059 := bstep (se 1 (by rfl) ⟨3012794, by rfl⟩ : syracuseStep 4017059 = 6025589) B6025589
theorem B1461169 : Blo 960589 1461169 := bstep (se 2 (by rfl) ⟨547938, by rfl⟩ : syracuseStep 1461169 = 1095877) B1095877
theorem B1625089 : Blo 960589 1625089 := bstep (se 2 (by rfl) ⟨609408, by rfl⟩ : syracuseStep 1625089 = 1218817) B1218817
theorem B1625123 : Blo 960589 1625123 := bstep (se 1 (by rfl) ⟨1218842, by rfl⟩ : syracuseStep 1625123 = 2437685) B2437685
theorem B4869233 : Blo 960589 4869233 := bstep (se 2 (by rfl) ⟨1825962, by rfl⟩ : syracuseStep 4869233 = 3651925) B3651925
theorem B1625251 : Blo 960589 1625251 := bstep (se 1 (by rfl) ⟨1218938, by rfl⟩ : syracuseStep 1625251 = 2437877) B2437877
theorem B12340421 : Blo 960589 12340421 := bstep (se 4 (by rfl) ⟨1156914, by rfl⟩ : syracuseStep 12340421 = 2313829) B2313829
theorem B1461521 : Blo 960589 1461521 := bstep (se 2 (by rfl) ⟨548070, by rfl⟩ : syracuseStep 1461521 = 1096141) B1096141
theorem B2739491 : Blo 960589 2739491 := bstep (se 1 (by rfl) ⟨2054618, by rfl⟩ : syracuseStep 2739491 = 4109237) B4109237
theorem B1625393 : Blo 960589 1625393 := bstep (se 2 (by rfl) ⟨609522, by rfl⟩ : syracuseStep 1625393 = 1219045) B1219045
theorem B1461569 : Blo 960589 1461569 := bstep (se 2 (by rfl) ⟨548088, by rfl⟩ : syracuseStep 1461569 = 1096177) B1096177
theorem B4935011 : Blo 960589 4935011 := bstep (se 1 (by rfl) ⟨3701258, by rfl⟩ : syracuseStep 4935011 = 7402517) B7402517
theorem B3657059 : Blo 960589 3657059 := bstep (se 1 (by rfl) ⟨2742794, by rfl⟩ : syracuseStep 3657059 = 5485589) B5485589
theorem B1625521 : Blo 960589 1625521 := bstep (se 2 (by rfl) ⟨609570, by rfl⟩ : syracuseStep 1625521 = 1219141) B1219141
theorem B1625555 : Blo 960589 1625555 := bstep (se 1 (by rfl) ⟨1219166, by rfl⟩ : syracuseStep 1625555 = 2438333) B2438333
theorem B11685347 : Blo 960589 11685347 := bstep (se 1 (by rfl) ⟨8764010, by rfl⟩ : syracuseStep 11685347 = 17528021) B17528021
theorem B5492195 : Blo 960589 5492195 := bstep (se 1 (by rfl) ⟨4119146, by rfl⟩ : syracuseStep 5492195 = 8238293) B8238293
theorem B1625683 : Blo 960589 1625683 := bstep (se 1 (by rfl) ⟨1219262, by rfl⟩ : syracuseStep 1625683 = 2438525) B2438525
theorem B2379377 : Blo 960589 2379377 := bstep (se 2 (by rfl) ⟨892266, by rfl⟩ : syracuseStep 2379377 = 1784533) B1784533
theorem B1232563 : Blo 960589 1232563 := bstep (se 1 (by rfl) ⟨924422, by rfl⟩ : syracuseStep 1232563 = 1848845) B1848845
theorem B1625825 : Blo 960589 1625825 := bstep (se 2 (by rfl) ⟨609684, by rfl⟩ : syracuseStep 1625825 = 1219369) B1219369
theorem B1625953 : Blo 960589 1625953 := bstep (se 2 (by rfl) ⟨609732, by rfl⟩ : syracuseStep 1625953 = 1219465) B1219465
theorem B1953649 : Blo 960589 1953649 := bstep (se 2 (by rfl) ⟨732618, by rfl⟩ : syracuseStep 1953649 = 1465237) B1465237
theorem B1625987 : Blo 960589 1625987 := bstep (se 1 (by rfl) ⟨1219490, by rfl⟩ : syracuseStep 1625987 = 2438981) B2438981
theorem B1626115 : Blo 960589 1626115 := bstep (se 1 (by rfl) ⟨1219586, by rfl⟩ : syracuseStep 1626115 = 2439173) B2439173
theorem B9261125 : Blo 960589 9261125 := bstep (se 4 (by rfl) ⟨868230, by rfl⟩ : syracuseStep 9261125 = 1736461) B1736461
theorem B2740301 : Blo 960589 2740301 := bstep (se 3 (by rfl) ⟨513806, by rfl⟩ : syracuseStep 2740301 = 1027613) B1027613
theorem B1855619 : Blo 960589 1855619 := bstep (se 1 (by rfl) ⟨1391714, by rfl⟩ : syracuseStep 1855619 = 2783429) B2783429
theorem B1626257 : Blo 960589 1626257 := bstep (se 2 (by rfl) ⟨609846, by rfl⟩ : syracuseStep 1626257 = 1219693) B1219693
theorem B2740493 : Blo 960589 2740493 := bstep (se 3 (by rfl) ⟨513842, by rfl⟩ : syracuseStep 2740493 = 1027685) B1027685
theorem B1626385 : Blo 960589 1626385 := bstep (se 2 (by rfl) ⟨609894, by rfl⟩ : syracuseStep 1626385 = 1219789) B1219789
theorem B1626419 : Blo 960589 1626419 := bstep (se 1 (by rfl) ⟨1219814, by rfl⟩ : syracuseStep 1626419 = 2439629) B2439629
theorem B3658061 : Blo 960589 3658061 := bstep (se 3 (by rfl) ⟨685886, by rfl⟩ : syracuseStep 3658061 = 1371773) B1371773
theorem B7295345 : Blo 960589 7295345 := bstep (se 2 (by rfl) ⟨2735754, by rfl⟩ : syracuseStep 7295345 = 5471509) B5471509
theorem B1626547 : Blo 960589 1626547 := bstep (se 1 (by rfl) ⟨1219910, by rfl⟩ : syracuseStep 1626547 = 2439821) B2439821
theorem B2773453 : Blo 960589 2773453 := bstep (se 3 (by rfl) ⟨520022, by rfl⟩ : syracuseStep 2773453 = 1040045) B1040045
theorem B5493197 : Blo 960589 5493197 := bstep (se 3 (by rfl) ⟨1029974, by rfl⟩ : syracuseStep 5493197 = 2059949) B2059949
theorem B4870691 : Blo 960589 4870691 := bstep (se 1 (by rfl) ⟨3653018, by rfl⟩ : syracuseStep 4870691 = 7306037) B7306037
theorem B1462835 : Blo 960589 1462835 := bstep (se 1 (by rfl) ⟨1097126, by rfl⟩ : syracuseStep 1462835 = 2194253) B2194253
theorem B1626689 : Blo 960589 1626689 := bstep (se 2 (by rfl) ⟨610008, by rfl⟩ : syracuseStep 1626689 = 1220017) B1220017
theorem B10965617 : Blo 960589 10965617 := bstep (se 2 (by rfl) ⟨4112106, by rfl⟩ : syracuseStep 10965617 = 8224213) B8224213
theorem B2052739 : Blo 960589 2052739 := bstep (se 1 (by rfl) ⟨1539554, by rfl⟩ : syracuseStep 2052739 = 3079109) B3079109
theorem B1626817 : Blo 960589 1626817 := bstep (se 2 (by rfl) ⟨610056, by rfl⟩ : syracuseStep 1626817 = 1220113) B1220113
theorem B1626851 : Blo 960589 1626851 := bstep (se 1 (by rfl) ⟨1220138, by rfl⟩ : syracuseStep 1626851 = 2440277) B2440277
theorem B1626979 : Blo 960589 1626979 := bstep (se 1 (by rfl) ⟨1220234, by rfl⟩ : syracuseStep 1626979 = 2440469) B2440469
theorem B1627121 : Blo 960589 1627121 := bstep (se 2 (by rfl) ⟨610170, by rfl⟩ : syracuseStep 1627121 = 1220341) B1220341
theorem B2053201 : Blo 960589 2053201 := bstep (se 2 (by rfl) ⟨769950, by rfl⟩ : syracuseStep 2053201 = 1539901) B1539901
theorem B4936817 : Blo 960589 4936817 := bstep (se 2 (by rfl) ⟨1851306, by rfl⟩ : syracuseStep 4936817 = 3702613) B3702613
theorem B1627249 : Blo 960589 1627249 := bstep (se 2 (by rfl) ⟨610218, by rfl⟩ : syracuseStep 1627249 = 1220437) B1220437
theorem B1627283 : Blo 960589 1627283 := bstep (se 1 (by rfl) ⟨1220462, by rfl⟩ : syracuseStep 1627283 = 2440925) B2440925
theorem B1299665 : Blo 960589 1299665 := bstep (se 2 (by rfl) ⟨487374, by rfl⟩ : syracuseStep 1299665 = 974749) B974749
theorem B2741485 : Blo 960589 2741485 := bstep (se 3 (by rfl) ⟨514028, by rfl⟩ : syracuseStep 2741485 = 1028057) B1028057
theorem B1627411 : Blo 960589 1627411 := bstep (se 1 (by rfl) ⟨1220558, by rfl⟩ : syracuseStep 1627411 = 2441117) B2441117
theorem B1824049 : Blo 960589 1824049 := bstep (se 2 (by rfl) ⟨684018, by rfl⟩ : syracuseStep 1824049 = 1368037) B1368037
theorem B4871501 : Blo 960589 4871501 := bstep (se 3 (by rfl) ⟨913406, by rfl⟩ : syracuseStep 4871501 = 1826813) B1826813
theorem B1627553 : Blo 960589 1627553 := bstep (se 2 (by rfl) ⟨610332, by rfl⟩ : syracuseStep 1627553 = 1220665) B1220665
theorem B1627681 : Blo 960589 1627681 := bstep (se 2 (by rfl) ⟨610380, by rfl⟩ : syracuseStep 1627681 = 1220761) B1220761
theorem B1627715 : Blo 960589 1627715 := bstep (se 1 (by rfl) ⟨1220786, by rfl⟩ : syracuseStep 1627715 = 2441573) B2441573
theorem B1300145 : Blo 960589 1300145 := bstep (se 2 (by rfl) ⟨487554, by rfl⟩ : syracuseStep 1300145 = 975109) B975109
theorem B2054243 : Blo 960589 2054243 := bstep (se 1 (by rfl) ⟨1540682, by rfl⟩ : syracuseStep 2054243 = 3081365) B3081365
theorem B1693937 : Blo 960589 1693937 := bstep (se 2 (by rfl) ⟨635226, by rfl⟩ : syracuseStep 1693937 = 1270453) B1270453
theorem B1825105 : Blo 960589 1825105 := bstep (se 2 (by rfl) ⟨684414, by rfl⟩ : syracuseStep 1825105 = 1368829) B1368829
theorem B1464707 : Blo 960589 1464707 := bstep (se 1 (by rfl) ⟨1098530, by rfl⟩ : syracuseStep 1464707 = 2197061) B2197061
theorem B3660173 : Blo 960589 3660173 := bstep (se 3 (by rfl) ⟨686282, by rfl⟩ : syracuseStep 3660173 = 1372565) B1372565
theorem B4119011 : Blo 960589 4119011 := bstep (se 1 (by rfl) ⟨3089258, by rfl⟩ : syracuseStep 4119011 = 6178517) B6178517
theorem B2054755 : Blo 960589 2054755 := bstep (se 1 (by rfl) ⟨1541066, by rfl⟩ : syracuseStep 2054755 = 3082133) B3082133
theorem B47536753 : Blo 960589 47536753 := bstep (se 2 (by rfl) ⟨17826282, by rfl⟩ : syracuseStep 47536753 = 35652565) B35652565
theorem B1825507 : Blo 960589 1825507 := bstep (se 1 (by rfl) ⟨1369130, by rfl⟩ : syracuseStep 1825507 = 2738261) B2738261
theorem B1170163 : Blo 960589 1170163 := bstep (se 1 (by rfl) ⟨877622, by rfl⟩ : syracuseStep 1170163 = 1755245) B1755245
theorem B1825553 : Blo 960589 1825553 := bstep (se 2 (by rfl) ⟨684582, by rfl⟩ : syracuseStep 1825553 = 1369165) B1369165
theorem B2743217 : Blo 960589 2743217 := bstep (se 2 (by rfl) ⟨1028706, by rfl⟩ : syracuseStep 2743217 = 2057413) B2057413
theorem B1825841 : Blo 960589 1825841 := bstep (se 2 (by rfl) ⟨684690, by rfl⟩ : syracuseStep 1825841 = 1369381) B1369381
theorem B2743409 : Blo 960589 2743409 := bstep (se 2 (by rfl) ⟨1028778, by rfl⟩ : syracuseStep 2743409 = 2057557) B2057557
theorem B1301681 : Blo 960589 1301681 := bstep (se 2 (by rfl) ⟨488130, by rfl⟩ : syracuseStep 1301681 = 976261) B976261
theorem B3660977 : Blo 960589 3660977 := bstep (se 2 (by rfl) ⟨1372866, by rfl⟩ : syracuseStep 3660977 = 2745733) B2745733
theorem B2055473 : Blo 960589 2055473 := bstep (se 2 (by rfl) ⟨770802, by rfl⟩ : syracuseStep 2055473 = 1541605) B1541605
theorem B1301875 : Blo 960589 1301875 := bstep (se 1 (by rfl) ⟨976406, by rfl⟩ : syracuseStep 1301875 = 1952813) B1952813
theorem B1465777 : Blo 960589 1465777 := bstep (se 2 (by rfl) ⟨549666, by rfl⟩ : syracuseStep 1465777 = 1099333) B1099333
theorem B12344885 : Blo 960589 12344885 := bstep (se 5 (by rfl) ⟨578666, by rfl⟩ : syracuseStep 12344885 = 1157333) B1157333
theorem B1826563 : Blo 960589 1826563 := bstep (se 1 (by rfl) ⟨1369922, by rfl⟩ : syracuseStep 1826563 = 2739845) B2739845
theorem B3661645 : Blo 960589 3661645 := bstep (se 3 (by rfl) ⟨686558, by rfl⟩ : syracuseStep 3661645 = 1373117) B1373117
theorem B1367923 : Blo 960589 1367923 := bstep (se 1 (by rfl) ⟨1025942, by rfl⟩ : syracuseStep 1367923 = 2051885) B2051885
theorem B2056259 : Blo 960589 2056259 := bstep (se 1 (by rfl) ⟨1542194, by rfl⟩ : syracuseStep 2056259 = 3084389) B3084389
theorem B1466435 : Blo 960589 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B2744401 : Blo 960589 2744401 := bstep (se 2 (by rfl) ⟨1029150, by rfl⟩ : syracuseStep 2744401 = 2058301) B2058301
theorem B5202053 : Blo 960589 5202053 := bstep (se 4 (by rfl) ⟨487692, by rfl⟩ : syracuseStep 5202053 = 975385) B975385
theorem B4874417 : Blo 960589 4874417 := bstep (se 2 (by rfl) ⟨1827906, by rfl⟩ : syracuseStep 4874417 = 3655813) B3655813
theorem B1827011 : Blo 960589 1827011 := bstep (se 1 (by rfl) ⟨1370258, by rfl⟩ : syracuseStep 1827011 = 2740517) B2740517
theorem B2777329 : Blo 960589 2777329 := bstep (se 2 (by rfl) ⟨1041498, by rfl⟩ : syracuseStep 2777329 = 2082997) B2082997
theorem B1564913 : Blo 960589 1564913 := bstep (se 2 (by rfl) ⟨586842, by rfl⟩ : syracuseStep 1564913 = 1173685) B1173685
theorem B2744675 : Blo 960589 2744675 := bstep (se 1 (by rfl) ⟨2058506, by rfl⟩ : syracuseStep 2744675 = 4117013) B4117013
theorem B1827299 : Blo 960589 1827299 := bstep (se 1 (by rfl) ⟨1370474, by rfl⟩ : syracuseStep 1827299 = 2740949) B2740949
theorem B2744867 : Blo 960589 2744867 := bstep (se 1 (by rfl) ⟨2058650, by rfl⟩ : syracuseStep 2744867 = 4117301) B4117301
theorem B2777969 : Blo 960589 2777969 := bstep (se 2 (by rfl) ⟨1041738, by rfl⟩ : syracuseStep 2777969 = 2083477) B2083477
theorem B1369057 : Blo 960589 1369057 := bstep (se 2 (by rfl) ⟨513396, by rfl⟩ : syracuseStep 1369057 = 1026793) B1026793
theorem B2057233 : Blo 960589 2057233 := bstep (se 2 (by rfl) ⟨771462, by rfl⟩ : syracuseStep 2057233 = 1542925) B1542925
theorem B1369153 : Blo 960589 1369153 := bstep (se 2 (by rfl) ⟨513432, by rfl⟩ : syracuseStep 1369153 = 1026865) B1026865
theorem B9233635 : Blo 960589 9233635 := bstep (se 1 (by rfl) ⟨6925226, by rfl⟩ : syracuseStep 9233635 = 13850453) B13850453
theorem B2057489 : Blo 960589 2057489 := bstep (se 2 (by rfl) ⟨771558, by rfl⟩ : syracuseStep 2057489 = 1543117) B1543117
theorem B2745677 : Blo 960589 2745677 := bstep (se 3 (by rfl) ⟨514814, by rfl⟩ : syracuseStep 2745677 = 1029629) B1029629
theorem B1828241 : Blo 960589 1828241 := bstep (se 2 (by rfl) ⟨685590, by rfl⟩ : syracuseStep 1828241 = 1371181) B1371181
theorem B2745859 : Blo 960589 2745859 := bstep (se 1 (by rfl) ⟨2059394, by rfl⟩ : syracuseStep 2745859 = 4118789) B4118789
theorem B1369649 : Blo 960589 1369649 := bstep (se 2 (by rfl) ⟨513618, by rfl⟩ : syracuseStep 1369649 = 1027237) B1027237
theorem B4875875 : Blo 960589 4875875 := bstep (se 1 (by rfl) ⟨3656906, by rfl⟩ : syracuseStep 4875875 = 7313813) B7313813
theorem B15591365 : Blo 960589 15591365 := bstep (se 4 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 15591365 = 2923381) B2923381
theorem B2746349 : Blo 960589 2746349 := bstep (se 3 (by rfl) ⟨514940, by rfl⟩ : syracuseStep 2746349 = 1029881) B1029881
theorem B5859461 : Blo 960589 5859461 := bstep (se 4 (by rfl) ⟨549324, by rfl⟩ : syracuseStep 5859461 = 1098649) B1098649
theorem B5204195 : Blo 960589 5204195 := bstep (se 1 (by rfl) ⟨3903146, by rfl⟩ : syracuseStep 5204195 = 7806293) B7806293
theorem B10414307 : Blo 960589 10414307 := bstep (se 1 (by rfl) ⟨7810730, by rfl⟩ : syracuseStep 10414307 = 15621461) B15621461
theorem B1829137 : Blo 960589 1829137 := bstep (se 2 (by rfl) ⟨685926, by rfl⟩ : syracuseStep 1829137 = 1371853) B1371853
theorem B4876685 : Blo 960589 4876685 := bstep (se 3 (by rfl) ⟨914378, by rfl⟩ : syracuseStep 4876685 = 1828757) B1828757
theorem B1370515 : Blo 960589 1370515 := bstep (se 1 (by rfl) ⟨1027886, by rfl⟩ : syracuseStep 1370515 = 2055773) B2055773
theorem B1829297 : Blo 960589 1829297 := bstep (se 2 (by rfl) ⟨685986, by rfl⟩ : syracuseStep 1829297 = 1371973) B1371973
theorem B1370611 : Blo 960589 1370611 := bstep (se 1 (by rfl) ⟨1027958, by rfl⟩ : syracuseStep 1370611 = 2055917) B2055917
theorem B2058787 : Blo 960589 2058787 := bstep (se 1 (by rfl) ⟨1544090, by rfl⟩ : syracuseStep 2058787 = 3088181) B3088181
theorem B1829699 : Blo 960589 1829699 := bstep (se 1 (by rfl) ⟨1372274, by rfl⟩ : syracuseStep 1829699 = 2744549) B2744549
theorem B2059121 : Blo 960589 2059121 := bstep (se 2 (by rfl) ⟨772170, by rfl⟩ : syracuseStep 2059121 = 1544341) B1544341
theorem B1371107 : Blo 960589 1371107 := bstep (se 1 (by rfl) ⟨1028330, by rfl⟩ : syracuseStep 1371107 = 2056661) B2056661
theorem B2780369 : Blo 960589 2780369 := bstep (se 2 (by rfl) ⟨1042638, by rfl⟩ : syracuseStep 2780369 = 2085277) B2085277
theorem B1371745 : Blo 960589 1371745 := bstep (se 2 (by rfl) ⟨514404, by rfl⟩ : syracuseStep 1371745 = 1028809) B1028809
theorem B3468899 : Blo 960589 3468899 := bstep (se 1 (by rfl) ⟨2601674, by rfl⟩ : syracuseStep 3468899 = 5203349) B5203349
theorem B1830595 : Blo 960589 1830595 := bstep (se 1 (by rfl) ⟨1372946, by rfl⟩ : syracuseStep 1830595 = 2745893) B2745893
theorem B5861069 : Blo 960589 5861069 := bstep (se 3 (by rfl) ⟨1098950, by rfl⟩ : syracuseStep 5861069 = 2197901) B2197901
theorem B1830755 : Blo 960589 1830755 := bstep (se 1 (by rfl) ⟨1373066, by rfl⟩ : syracuseStep 1830755 = 2746133) B2746133
theorem B1372081 : Blo 960589 1372081 := bstep (se 2 (by rfl) ⟨514530, by rfl⟩ : syracuseStep 1372081 = 1029061) B1029061
theorem B6156323 : Blo 960589 6156323 := bstep (se 1 (by rfl) ⟨4617242, by rfl⟩ : syracuseStep 6156323 = 9234485) B9234485
theorem B10678385 : Blo 960589 10678385 := bstep (se 2 (by rfl) ⟨4004394, by rfl⟩ : syracuseStep 10678385 = 8008789) B8008789
theorem B1372673 : Blo 960589 1372673 := bstep (se 2 (by rfl) ⟨514752, by rfl⟩ : syracuseStep 1372673 = 1029505) B1029505
theorem B24966029 : Blo 960589 24966029 := bstep (se 3 (by rfl) ⟨4681130, by rfl⟩ : syracuseStep 24966029 = 9362261) B9362261
theorem B1373203 : Blo 960589 1373203 := bstep (se 1 (by rfl) ⟨1029902, by rfl⟩ : syracuseStep 1373203 = 2059805) B2059805
theorem B4879601 : Blo 960589 4879601 := bstep (se 2 (by rfl) ⟨1829850, by rfl⟩ : syracuseStep 4879601 = 3659701) B3659701
theorem B3077443 : Blo 960589 3077443 := bstep (se 1 (by rfl) ⟨2308082, by rfl⟩ : syracuseStep 3077443 = 4616165) B4616165
theorem B12318277 : Blo 960589 12318277 := bstep (se 4 (by rfl) ⟨1154838, by rfl⟩ : syracuseStep 12318277 = 2309677) B2309677
theorem B3077777 : Blo 960589 3077777 := bstep (se 2 (by rfl) ⟨1154166, by rfl⟩ : syracuseStep 3077777 = 2308333) B2308333
theorem B3241997 : Blo 960589 3241997 := bstep (se 3 (by rfl) ⟨607874, by rfl⟩ : syracuseStep 3241997 = 1215749) B1215749
theorem B3242051 : Blo 960589 3242051 := bstep (se 1 (by rfl) ⟨2431538, by rfl⟩ : syracuseStep 3242051 = 4863077) B4863077
theorem B3897485 : Blo 960589 3897485 := bstep (se 3 (by rfl) ⟨730778, by rfl⟩ : syracuseStep 3897485 = 1461557) B1461557
theorem B3242321 : Blo 960589 3242321 := bstep (se 2 (by rfl) ⟨1215870, by rfl⟩ : syracuseStep 3242321 = 2431741) B2431741
theorem B3897713 : Blo 960589 3897713 := bstep (se 2 (by rfl) ⟨1461642, by rfl⟩ : syracuseStep 3897713 = 2923285) B2923285
theorem B9238981 : Blo 960589 9238981 := bstep (se 4 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 9238981 = 1732309) B1732309
theorem B2783693 : Blo 960589 2783693 := bstep (se 3 (by rfl) ⟨521942, by rfl⟩ : syracuseStep 2783693 = 1043885) B1043885
theorem B4881059 : Blo 960589 4881059 := bstep (se 1 (by rfl) ⟨3660794, by rfl⟩ : syracuseStep 4881059 = 7321589) B7321589
theorem B2161457 : Blo 960589 2161457 := bstep (se 2 (by rfl) ⟨810546, by rfl⟩ : syracuseStep 2161457 = 1621093) B1621093
theorem B2161475 : Blo 960589 2161475 := bstep (se 1 (by rfl) ⟨1621106, by rfl⟩ : syracuseStep 2161475 = 3242213) B3242213
theorem B10386245 : Blo 960589 10386245 := bstep (se 4 (by rfl) ⟨973710, by rfl⟩ : syracuseStep 10386245 = 1947421) B1947421
theorem B3242861 : Blo 960589 3242861 := bstep (se 3 (by rfl) ⟨608036, by rfl⟩ : syracuseStep 3242861 = 1216073) B1216073
theorem B3242915 : Blo 960589 3242915 := bstep (se 1 (by rfl) ⟨2432186, by rfl⟩ : syracuseStep 3242915 = 4864373) B4864373
theorem B4684877 : Blo 960589 4684877 := bstep (se 3 (by rfl) ⟨878414, by rfl⟩ : syracuseStep 4684877 = 1756829) B1756829
theorem B2161745 : Blo 960589 2161745 := bstep (se 2 (by rfl) ⟨810654, by rfl⟩ : syracuseStep 2161745 = 1621309) B1621309
theorem B2161763 : Blo 960589 2161763 := bstep (se 1 (by rfl) ⟨1621322, by rfl⟩ : syracuseStep 2161763 = 3242645) B3242645
theorem B1440899 : Blo 960589 1440899 := bstep (se 1 (by rfl) ⟨1080674, by rfl⟩ : syracuseStep 1440899 = 2161349) B2161349
theorem B5209229 : Blo 960589 5209229 := bstep (se 3 (by rfl) ⟨976730, by rfl⟩ : syracuseStep 5209229 = 1953461) B1953461
theorem B4947085 : Blo 960589 4947085 := bstep (se 3 (by rfl) ⟨927578, by rfl⟩ : syracuseStep 4947085 = 1855157) B1855157
theorem B1440929 : Blo 960589 1440929 := bstep (se 2 (by rfl) ⟨540348, by rfl⟩ : syracuseStep 1440929 = 1080697) B1080697
theorem B3243185 : Blo 960589 3243185 := bstep (se 2 (by rfl) ⟨1216194, by rfl⟩ : syracuseStep 3243185 = 2432389) B2432389
theorem B1440947 : Blo 960589 1440947 := bstep (se 1 (by rfl) ⟨1080710, by rfl⟩ : syracuseStep 1440947 = 2161421) B2161421
theorem B10386629 : Blo 960589 10386629 := bstep (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) B1947493
theorem B3472589 : Blo 960589 3472589 := bstep (se 3 (by rfl) ⟨651110, by rfl⟩ : syracuseStep 3472589 = 1302221) B1302221
theorem B1440977 : Blo 960589 1440977 := bstep (se 2 (by rfl) ⟨540366, by rfl⟩ : syracuseStep 1440977 = 1080733) B1080733
theorem B1440995 : Blo 960589 1440995 := bstep (se 1 (by rfl) ⟨1080746, by rfl⟩ : syracuseStep 1440995 = 2161493) B2161493
theorem B1539299 : Blo 960589 1539299 := bstep (se 1 (by rfl) ⟨1154474, by rfl⟩ : syracuseStep 1539299 = 2308949) B2308949
theorem B1441025 : Blo 960589 1441025 := bstep (se 2 (by rfl) ⟨540384, by rfl⟩ : syracuseStep 1441025 = 1080769) B1080769
theorem B3702029 : Blo 960589 3702029 := bstep (se 3 (by rfl) ⟨694130, by rfl⟩ : syracuseStep 3702029 = 1388261) B1388261
theorem B1441043 : Blo 960589 1441043 := bstep (se 1 (by rfl) ⟨1080782, by rfl⟩ : syracuseStep 1441043 = 2161565) B2161565
theorem B1441073 : Blo 960589 1441073 := bstep (se 2 (by rfl) ⟨540402, by rfl⟩ : syracuseStep 1441073 = 1080805) B1080805
theorem B1441091 : Blo 960589 1441091 := bstep (se 1 (by rfl) ⟨1080818, by rfl⟩ : syracuseStep 1441091 = 2161637) B2161637
theorem B1441121 : Blo 960589 1441121 := bstep (se 2 (by rfl) ⟨540420, by rfl⟩ : syracuseStep 1441121 = 1080841) B1080841
theorem B2162033 : Blo 960589 2162033 := bstep (se 2 (by rfl) ⟨810762, by rfl⟩ : syracuseStep 2162033 = 1621525) B1621525
theorem B1441139 : Blo 960589 1441139 := bstep (se 1 (by rfl) ⟨1080854, by rfl⟩ : syracuseStep 1441139 = 2161709) B2161709
theorem B2162051 : Blo 960589 2162051 := bstep (se 1 (by rfl) ⟨1621538, by rfl⟩ : syracuseStep 2162051 = 3243077) B3243077
theorem B1441169 : Blo 960589 1441169 := bstep (se 2 (by rfl) ⟨540438, by rfl⟩ : syracuseStep 1441169 = 1080877) B1080877
theorem B1441187 : Blo 960589 1441187 := bstep (se 1 (by rfl) ⟨1080890, by rfl⟩ : syracuseStep 1441187 = 2161781) B2161781
theorem B1441217 : Blo 960589 1441217 := bstep (se 2 (by rfl) ⟨540456, by rfl⟩ : syracuseStep 1441217 = 1080913) B1080913
theorem B1539523 : Blo 960589 1539523 := bstep (se 1 (by rfl) ⟨1154642, by rfl⟩ : syracuseStep 1539523 = 2309285) B2309285
theorem B4881869 : Blo 960589 4881869 := bstep (se 3 (by rfl) ⟨915350, by rfl⟩ : syracuseStep 4881869 = 1830701) B1830701
theorem B1080787 : Blo 960589 1080787 := bstep (se 1 (by rfl) ⟨810590, by rfl⟩ : syracuseStep 1080787 = 1621181) B1621181
theorem B1441235 : Blo 960589 1441235 := bstep (se 1 (by rfl) ⟨1080926, by rfl⟩ : syracuseStep 1441235 = 2161853) B2161853
theorem B1441265 : Blo 960589 1441265 := bstep (se 2 (by rfl) ⟨540474, by rfl⟩ : syracuseStep 1441265 = 1080949) B1080949
theorem B1441283 : Blo 960589 1441283 := bstep (se 1 (by rfl) ⟨1080962, by rfl⟩ : syracuseStep 1441283 = 2161925) B2161925
theorem B1441313 : Blo 960589 1441313 := bstep (se 2 (by rfl) ⟨540492, by rfl⟩ : syracuseStep 1441313 = 1080985) B1080985
theorem B1441331 : Blo 960589 1441331 := bstep (se 1 (by rfl) ⟨1080998, by rfl⟩ : syracuseStep 1441331 = 2161997) B2161997
theorem B1441361 : Blo 960589 1441361 := bstep (se 2 (by rfl) ⟨540510, by rfl⟩ : syracuseStep 1441361 = 1081021) B1081021
theorem B1080931 : Blo 960589 1080931 := bstep (se 1 (by rfl) ⟨810698, by rfl⟩ : syracuseStep 1080931 = 1621397) B1621397
theorem B1441379 : Blo 960589 1441379 := bstep (se 1 (by rfl) ⟨1081034, by rfl⟩ : syracuseStep 1441379 = 2162069) B2162069
theorem B1441409 : Blo 960589 1441409 := bstep (se 2 (by rfl) ⟨540528, by rfl⟩ : syracuseStep 1441409 = 1081057) B1081057
theorem B2162321 : Blo 960589 2162321 := bstep (se 2 (by rfl) ⟨810870, by rfl⟩ : syracuseStep 2162321 = 1621741) B1621741
theorem B1441427 : Blo 960589 1441427 := bstep (se 1 (by rfl) ⟨1081070, by rfl⟩ : syracuseStep 1441427 = 2162141) B2162141
theorem B2162339 : Blo 960589 2162339 := bstep (se 1 (by rfl) ⟨1621754, by rfl⟩ : syracuseStep 2162339 = 3243509) B3243509
theorem B1441457 : Blo 960589 1441457 := bstep (se 2 (by rfl) ⟨540546, by rfl⟩ : syracuseStep 1441457 = 1081093) B1081093
theorem B1441475 : Blo 960589 1441475 := bstep (se 1 (by rfl) ⟨1081106, by rfl⟩ : syracuseStep 1441475 = 2162213) B2162213
theorem B3243725 : Blo 960589 3243725 := bstep (se 3 (by rfl) ⟨608198, by rfl⟩ : syracuseStep 3243725 = 1216397) B1216397
theorem B1441505 : Blo 960589 1441505 := bstep (se 2 (by rfl) ⟨540564, by rfl⟩ : syracuseStep 1441505 = 1081129) B1081129
theorem B1081075 : Blo 960589 1081075 := bstep (se 1 (by rfl) ⟨810806, by rfl⟩ : syracuseStep 1081075 = 1621613) B1621613
theorem B1441523 : Blo 960589 1441523 := bstep (se 1 (by rfl) ⟨1081142, by rfl⟩ : syracuseStep 1441523 = 2162285) B2162285
theorem B3243779 : Blo 960589 3243779 := bstep (se 1 (by rfl) ⟨2432834, by rfl⟩ : syracuseStep 3243779 = 4865669) B4865669
theorem B1441553 : Blo 960589 1441553 := bstep (se 2 (by rfl) ⟨540582, by rfl⟩ : syracuseStep 1441553 = 1081165) B1081165
theorem B5472035 : Blo 960589 5472035 := bstep (se 1 (by rfl) ⟨4104026, by rfl⟩ : syracuseStep 5472035 = 8208053) B8208053
theorem B1441571 : Blo 960589 1441571 := bstep (se 1 (by rfl) ⟨1081178, by rfl⟩ : syracuseStep 1441571 = 2162357) B2162357
theorem B1441601 : Blo 960589 1441601 := bstep (se 2 (by rfl) ⟨540600, by rfl⟩ : syracuseStep 1441601 = 1081201) B1081201
theorem B1441619 : Blo 960589 1441619 := bstep (se 1 (by rfl) ⟨1081214, by rfl⟩ : syracuseStep 1441619 = 2162429) B2162429
theorem B1441649 : Blo 960589 1441649 := bstep (se 2 (by rfl) ⟨540618, by rfl⟩ : syracuseStep 1441649 = 1081237) B1081237
theorem B1081219 : Blo 960589 1081219 := bstep (se 1 (by rfl) ⟨810914, by rfl⟩ : syracuseStep 1081219 = 1621829) B1621829
theorem B1441667 : Blo 960589 1441667 := bstep (se 1 (by rfl) ⟨1081250, by rfl⟩ : syracuseStep 1441667 = 2162501) B2162501
theorem B1441697 : Blo 960589 1441697 := bstep (se 2 (by rfl) ⟨540636, by rfl⟩ : syracuseStep 1441697 = 1081273) B1081273
theorem B2162609 : Blo 960589 2162609 := bstep (se 2 (by rfl) ⟨810978, by rfl⟩ : syracuseStep 2162609 = 1621957) B1621957
theorem B1441715 : Blo 960589 1441715 := bstep (se 1 (by rfl) ⟨1081286, by rfl⟩ : syracuseStep 1441715 = 2162573) B2162573
theorem B2162627 : Blo 960589 2162627 := bstep (se 1 (by rfl) ⟨1621970, by rfl⟩ : syracuseStep 2162627 = 3243941) B3243941
theorem B1441745 : Blo 960589 1441745 := bstep (se 2 (by rfl) ⟨540654, by rfl⟩ : syracuseStep 1441745 = 1081309) B1081309
theorem B1441763 : Blo 960589 1441763 := bstep (se 1 (by rfl) ⟨1081322, by rfl⟩ : syracuseStep 1441763 = 2162645) B2162645
theorem B6160369 : Blo 960589 6160369 := bstep (se 2 (by rfl) ⟨2310138, by rfl⟩ : syracuseStep 6160369 = 4620277) B4620277
theorem B2162699 : Blo 960589 2162699 := bstep (se 1 (by rfl) ⟨1622024, by rfl⟩ : syracuseStep 2162699 = 3244049) B3244049
theorem B1441817 : Blo 960589 1441817 := bstep (se 2 (by rfl) ⟨540681, by rfl⟩ : syracuseStep 1441817 = 1081363) B1081363
theorem B1081399 : Blo 960589 1081399 := bstep (se 1 (by rfl) ⟨811049, by rfl⟩ : syracuseStep 1081399 = 1622099) B1622099
theorem B2162753 : Blo 960589 2162753 := bstep (se 2 (by rfl) ⟨811032, by rfl⟩ : syracuseStep 2162753 = 1622065) B1622065
theorem B1441931 : Blo 960589 1441931 := bstep (se 1 (by rfl) ⟨1081448, by rfl⟩ : syracuseStep 1441931 = 2162897) B2162897
theorem B1441943 : Blo 960589 1441943 := bstep (se 1 (by rfl) ⟨1081457, by rfl⟩ : syracuseStep 1441943 = 2162915) B2162915
theorem B3244211 : Blo 960589 3244211 := bstep (se 1 (by rfl) ⟨2433158, by rfl⟩ : syracuseStep 3244211 = 4866317) B4866317
theorem B4161739 : Blo 960589 4161739 := bstep (se 1 (by rfl) ⟨3121304, by rfl⟩ : syracuseStep 4161739 = 6242609) B6242609
theorem B1442009 : Blo 960589 1442009 := bstep (se 2 (by rfl) ⟨540753, by rfl⟩ : syracuseStep 1442009 = 1081507) B1081507
theorem B4391129 : Blo 960589 4391129 := bstep (se 2 (by rfl) ⟨1646673, by rfl⟩ : syracuseStep 4391129 = 3293347) B3293347
theorem B5865689 : Blo 960589 5865689 := bstep (se 2 (by rfl) ⟨2199633, by rfl⟩ : syracuseStep 5865689 = 4399267) B4399267
theorem B1081579 : Blo 960589 1081579 := bstep (se 1 (by rfl) ⟨811184, by rfl⟩ : syracuseStep 1081579 = 1622369) B1622369
theorem B2162969 : Blo 960589 2162969 := bstep (se 2 (by rfl) ⟨811113, by rfl⟩ : syracuseStep 2162969 = 1622227) B1622227
theorem B8323373 : Blo 960589 8323373 := bstep (se 3 (by rfl) ⟨1560632, by rfl⟩ : syracuseStep 8323373 = 3121265) B3121265
theorem B3703105 : Blo 960589 3703105 := bstep (se 2 (by rfl) ⟨1388664, by rfl⟩ : syracuseStep 3703105 = 2777329) B2777329
theorem B1442123 : Blo 960589 1442123 := bstep (se 1 (by rfl) ⟨1081592, by rfl⟩ : syracuseStep 1442123 = 2163185) B2163185
theorem B1442135 : Blo 960589 1442135 := bstep (se 1 (by rfl) ⟨1081601, by rfl⟩ : syracuseStep 1442135 = 2163203) B2163203
theorem B1081687 : Blo 960589 1081687 := bstep (se 1 (by rfl) ⟨811265, by rfl⟩ : syracuseStep 1081687 = 1622531) B1622531
theorem B2163059 : Blo 960589 2163059 := bstep (se 1 (by rfl) ⟨1622294, by rfl⟩ : syracuseStep 2163059 = 3244589) B3244589
theorem B2163095 : Blo 960589 2163095 := bstep (se 1 (by rfl) ⟨1622321, by rfl⟩ : syracuseStep 2163095 = 3244643) B3244643
theorem B1442201 : Blo 960589 1442201 := bstep (se 2 (by rfl) ⟨540825, by rfl⟩ : syracuseStep 1442201 = 1081651) B1081651
theorem B3244481 : Blo 960589 3244481 := bstep (se 2 (by rfl) ⟨1216680, by rfl⟩ : syracuseStep 3244481 = 2433361) B2433361
theorem B1540567 : Blo 960589 1540567 := bstep (se 1 (by rfl) ⟨1155425, by rfl⟩ : syracuseStep 1540567 = 2310851) B2310851
theorem B1442315 : Blo 960589 1442315 := bstep (se 1 (by rfl) ⟨1081736, by rfl⟩ : syracuseStep 1442315 = 2163473) B2163473
theorem B1081867 : Blo 960589 1081867 := bstep (se 1 (by rfl) ⟨811400, by rfl⟩ : syracuseStep 1081867 = 1622801) B1622801
theorem B5472785 : Blo 960589 5472785 := bstep (se 2 (by rfl) ⟨2052294, by rfl⟩ : syracuseStep 5472785 = 4104589) B4104589
theorem B1442327 : Blo 960589 1442327 := bstep (se 1 (by rfl) ⟨1081745, by rfl⟩ : syracuseStep 1442327 = 2163491) B2163491
theorem B6160961 : Blo 960589 6160961 := bstep (se 2 (by rfl) ⟨2310360, by rfl⟩ : syracuseStep 6160961 = 4620721) B4620721
theorem B2163275 : Blo 960589 2163275 := bstep (se 1 (by rfl) ⟨1622456, by rfl⟩ : syracuseStep 2163275 = 3244913) B3244913
theorem B1442393 : Blo 960589 1442393 := bstep (se 2 (by rfl) ⟨540897, by rfl⟩ : syracuseStep 1442393 = 1081795) B1081795
theorem B1081975 : Blo 960589 1081975 := bstep (se 1 (by rfl) ⟨811481, by rfl⟩ : syracuseStep 1081975 = 1622963) B1622963
theorem B2163329 : Blo 960589 2163329 := bstep (se 2 (by rfl) ⟨811248, by rfl⟩ : syracuseStep 2163329 = 1622497) B1622497
theorem B1442507 : Blo 960589 1442507 := bstep (se 1 (by rfl) ⟨1081880, by rfl⟩ : syracuseStep 1442507 = 2163761) B2163761
theorem B7307981 : Blo 960589 7307981 := bstep (se 3 (by rfl) ⟨1370246, by rfl⟩ : syracuseStep 7307981 = 2740493) B2740493
theorem B1442519 : Blo 960589 1442519 := bstep (se 1 (by rfl) ⟨1081889, by rfl⟩ : syracuseStep 1442519 = 2163779) B2163779
theorem B1442585 : Blo 960589 1442585 := bstep (se 2 (by rfl) ⟨540969, by rfl⟩ : syracuseStep 1442585 = 1081939) B1081939
theorem B1082155 : Blo 960589 1082155 := bstep (se 1 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 1082155 = 1623233) B1623233
theorem B1540939 : Blo 960589 1540939 := bstep (se 1 (by rfl) ⟨1155704, by rfl⟩ : syracuseStep 1540939 = 2311409) B2311409
theorem B2163545 : Blo 960589 2163545 := bstep (se 2 (by rfl) ⟨811329, by rfl⟩ : syracuseStep 2163545 = 1622659) B1622659
theorem B1442699 : Blo 960589 1442699 := bstep (se 1 (by rfl) ⟨1082024, by rfl⟩ : syracuseStep 1442699 = 2164049) B2164049
theorem B1442711 : Blo 960589 1442711 := bstep (se 1 (by rfl) ⟨1082033, by rfl⟩ : syracuseStep 1442711 = 2164067) B2164067
theorem B1082263 : Blo 960589 1082263 := bstep (se 1 (by rfl) ⟨811697, by rfl⟩ : syracuseStep 1082263 = 1623395) B1623395
theorem B2163635 : Blo 960589 2163635 := bstep (se 1 (by rfl) ⟨1622726, by rfl⟩ : syracuseStep 2163635 = 3245453) B3245453
theorem B2163671 : Blo 960589 2163671 := bstep (se 1 (by rfl) ⟨1622753, by rfl⟩ : syracuseStep 2163671 = 3245507) B3245507
theorem B5473241 : Blo 960589 5473241 := bstep (se 2 (by rfl) ⟨2052465, by rfl⟩ : syracuseStep 5473241 = 4104931) B4104931
theorem B1442777 : Blo 960589 1442777 := bstep (se 2 (by rfl) ⟨541041, by rfl⟩ : syracuseStep 1442777 = 1082083) B1082083
theorem B3245021 : Blo 960589 3245021 := bstep (se 3 (by rfl) ⟨608441, by rfl⟩ : syracuseStep 3245021 = 1216883) B1216883
theorem B1442891 : Blo 960589 1442891 := bstep (se 1 (by rfl) ⟨1082168, by rfl⟩ : syracuseStep 1442891 = 2164337) B2164337
theorem B1541195 : Blo 960589 1541195 := bstep (se 1 (by rfl) ⟨1155896, by rfl⟩ : syracuseStep 1541195 = 2311793) B2311793
theorem B1082443 : Blo 960589 1082443 := bstep (se 1 (by rfl) ⟨811832, by rfl⟩ : syracuseStep 1082443 = 1623665) B1623665
theorem B1442903 : Blo 960589 1442903 := bstep (se 1 (by rfl) ⟨1082177, by rfl⟩ : syracuseStep 1442903 = 2164355) B2164355
theorem B2163851 : Blo 960589 2163851 := bstep (se 1 (by rfl) ⟨1622888, by rfl⟩ : syracuseStep 2163851 = 3245777) B3245777
theorem B1442969 : Blo 960589 1442969 := bstep (se 2 (by rfl) ⟨541113, by rfl⟩ : syracuseStep 1442969 = 1082227) B1082227
theorem B7308467 : Blo 960589 7308467 := bstep (se 1 (by rfl) ⟨5481350, by rfl⟩ : syracuseStep 7308467 = 10962701) B10962701
theorem B1082551 : Blo 960589 1082551 := bstep (se 1 (by rfl) ⟨811913, by rfl⟩ : syracuseStep 1082551 = 1623827) B1623827
theorem B2163905 : Blo 960589 2163905 := bstep (se 2 (by rfl) ⟨811464, by rfl⟩ : syracuseStep 2163905 = 1622929) B1622929
theorem B1443083 : Blo 960589 1443083 := bstep (se 1 (by rfl) ⟨1082312, by rfl⟩ : syracuseStep 1443083 = 2164625) B2164625
theorem B1541387 : Blo 960589 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B1443095 : Blo 960589 1443095 := bstep (se 1 (by rfl) ⟨1082321, by rfl⟩ : syracuseStep 1443095 = 2164643) B2164643
theorem B1443161 : Blo 960589 1443161 := bstep (se 2 (by rfl) ⟨541185, by rfl⟩ : syracuseStep 1443161 = 1082371) B1082371
theorem B1082731 : Blo 960589 1082731 := bstep (se 1 (by rfl) ⟨812048, by rfl⟩ : syracuseStep 1082731 = 1624097) B1624097
theorem B3474839 : Blo 960589 3474839 := bstep (se 1 (by rfl) ⟨2606129, by rfl⟩ : syracuseStep 3474839 = 5212259) B5212259
theorem B2164121 : Blo 960589 2164121 := bstep (se 2 (by rfl) ⟨811545, by rfl⟩ : syracuseStep 2164121 = 1623091) B1623091
theorem B10978739 : Blo 960589 10978739 := bstep (se 1 (by rfl) ⟨8234054, by rfl⟩ : syracuseStep 10978739 = 16468109) B16468109
theorem B1443275 : Blo 960589 1443275 := bstep (se 1 (by rfl) ⟨1082456, by rfl⟩ : syracuseStep 1443275 = 2164913) B2164913
theorem B1443287 : Blo 960589 1443287 := bstep (se 1 (by rfl) ⟨1082465, by rfl⟩ : syracuseStep 1443287 = 2164931) B2164931
theorem B1082839 : Blo 960589 1082839 := bstep (se 1 (by rfl) ⟨812129, by rfl⟩ : syracuseStep 1082839 = 1624259) B1624259
theorem B1738199 : Blo 960589 1738199 := bstep (se 1 (by rfl) ⟨1303649, by rfl⟩ : syracuseStep 1738199 = 2607299) B2607299
theorem B2164211 : Blo 960589 2164211 := bstep (se 1 (by rfl) ⟨1623158, by rfl⟩ : syracuseStep 2164211 = 3246317) B3246317
theorem B2164247 : Blo 960589 2164247 := bstep (se 1 (by rfl) ⟨1623185, by rfl⟩ : syracuseStep 2164247 = 3246371) B3246371
theorem B1443353 : Blo 960589 1443353 := bstep (se 2 (by rfl) ⟨541257, by rfl⟩ : syracuseStep 1443353 = 1082515) B1082515
theorem B1443467 : Blo 960589 1443467 := bstep (se 1 (by rfl) ⟨1082600, by rfl⟩ : syracuseStep 1443467 = 2165201) B2165201
theorem B1083019 : Blo 960589 1083019 := bstep (se 1 (by rfl) ⟨812264, by rfl⟩ : syracuseStep 1083019 = 1624529) B1624529
theorem B1443479 : Blo 960589 1443479 := bstep (se 1 (by rfl) ⟨1082609, by rfl⟩ : syracuseStep 1443479 = 2165219) B2165219
theorem B5211827 : Blo 960589 5211827 := bstep (se 1 (by rfl) ⟨3908870, by rfl⟩ : syracuseStep 5211827 = 7817741) B7817741
theorem B2164427 : Blo 960589 2164427 := bstep (se 1 (by rfl) ⟨1623320, by rfl⟩ : syracuseStep 2164427 = 3246641) B3246641
theorem B1443545 : Blo 960589 1443545 := bstep (se 2 (by rfl) ⟨541329, by rfl⟩ : syracuseStep 1443545 = 1082659) B1082659
theorem B27723505 : Blo 960589 27723505 := bstep (se 2 (by rfl) ⟨10396314, by rfl⟩ : syracuseStep 27723505 = 20792629) B20792629
theorem B1083127 : Blo 960589 1083127 := bstep (se 1 (by rfl) ⟨812345, by rfl⟩ : syracuseStep 1083127 = 1624691) B1624691
theorem B2164481 : Blo 960589 2164481 := bstep (se 2 (by rfl) ⟨811680, by rfl⟩ : syracuseStep 2164481 = 1623361) B1623361
theorem B1443659 : Blo 960589 1443659 := bstep (se 1 (by rfl) ⟨1082744, by rfl⟩ : syracuseStep 1443659 = 2165489) B2165489
theorem B1443671 : Blo 960589 1443671 := bstep (se 1 (by rfl) ⟨1082753, by rfl⟩ : syracuseStep 1443671 = 2165507) B2165507
theorem B1443737 : Blo 960589 1443737 := bstep (se 2 (by rfl) ⟨541401, by rfl⟩ : syracuseStep 1443737 = 1082803) B1082803
theorem B1083307 : Blo 960589 1083307 := bstep (se 1 (by rfl) ⟨812480, by rfl⟩ : syracuseStep 1083307 = 1624961) B1624961
theorem B2164697 : Blo 960589 2164697 := bstep (se 2 (by rfl) ⟨811761, by rfl⟩ : syracuseStep 2164697 = 1623523) B1623523
theorem B1443851 : Blo 960589 1443851 := bstep (se 1 (by rfl) ⟨1082888, by rfl⟩ : syracuseStep 1443851 = 2165777) B2165777
theorem B1443863 : Blo 960589 1443863 := bstep (se 1 (by rfl) ⟨1082897, by rfl⟩ : syracuseStep 1443863 = 2165795) B2165795
theorem B1083415 : Blo 960589 1083415 := bstep (se 1 (by rfl) ⟨812561, by rfl⟩ : syracuseStep 1083415 = 1625123) B1625123
theorem B1542169 : Blo 960589 1542169 := bstep (se 2 (by rfl) ⟨578313, by rfl⟩ : syracuseStep 1542169 = 1156627) B1156627
theorem B2164787 : Blo 960589 2164787 := bstep (se 1 (by rfl) ⟨1623590, by rfl⟩ : syracuseStep 2164787 = 3247181) B3247181
theorem B3246155 : Blo 960589 3246155 := bstep (se 1 (by rfl) ⟨2434616, by rfl⟩ : syracuseStep 3246155 = 4869233) B4869233
theorem B2164823 : Blo 960589 2164823 := bstep (se 1 (by rfl) ⟨1623617, by rfl⟩ : syracuseStep 2164823 = 3247235) B3247235
theorem B1443929 : Blo 960589 1443929 := bstep (se 2 (by rfl) ⟨541473, by rfl⟩ : syracuseStep 1443929 = 1082947) B1082947
theorem B8226947 : Blo 960589 8226947 := bstep (se 1 (by rfl) ⟨6170210, by rfl⟩ : syracuseStep 8226947 = 12340421) B12340421
theorem B1444043 : Blo 960589 1444043 := bstep (se 1 (by rfl) ⟨1083032, by rfl⟩ : syracuseStep 1444043 = 2166065) B2166065
theorem B1083595 : Blo 960589 1083595 := bstep (se 1 (by rfl) ⟨812696, by rfl⟩ : syracuseStep 1083595 = 1625393) B1625393
theorem B1444055 : Blo 960589 1444055 := bstep (se 1 (by rfl) ⟨1083041, by rfl⟩ : syracuseStep 1444055 = 2166083) B2166083
theorem B2165003 : Blo 960589 2165003 := bstep (se 1 (by rfl) ⟨1623752, by rfl⟩ : syracuseStep 2165003 = 3247505) B3247505
theorem B1444121 : Blo 960589 1444121 := bstep (se 2 (by rfl) ⟨541545, by rfl⟩ : syracuseStep 1444121 = 1083091) B1083091
theorem B1083703 : Blo 960589 1083703 := bstep (se 1 (by rfl) ⟨812777, by rfl⟩ : syracuseStep 1083703 = 1625555) B1625555
theorem B2165057 : Blo 960589 2165057 := bstep (se 2 (by rfl) ⟨811896, by rfl⟩ : syracuseStep 2165057 = 1623793) B1623793
theorem B3246425 : Blo 960589 3246425 := bstep (se 2 (by rfl) ⟨1217409, by rfl⟩ : syracuseStep 3246425 = 2434819) B2434819
theorem B1444235 : Blo 960589 1444235 := bstep (se 1 (by rfl) ⟨1083176, by rfl⟩ : syracuseStep 1444235 = 2166353) B2166353
theorem B1444247 : Blo 960589 1444247 := bstep (se 1 (by rfl) ⟨1083185, by rfl⟩ : syracuseStep 1444247 = 2166371) B2166371
theorem B1444313 : Blo 960589 1444313 := bstep (se 2 (by rfl) ⟨541617, by rfl⟩ : syracuseStep 1444313 = 1083235) B1083235
theorem B1083883 : Blo 960589 1083883 := bstep (se 1 (by rfl) ⟨812912, by rfl⟩ : syracuseStep 1083883 = 1625825) B1625825
theorem B2165273 : Blo 960589 2165273 := bstep (se 2 (by rfl) ⟨811977, by rfl⟩ : syracuseStep 2165273 = 1623955) B1623955
theorem B1444427 : Blo 960589 1444427 := bstep (se 1 (by rfl) ⟨1083320, by rfl⟩ : syracuseStep 1444427 = 2166641) B2166641
theorem B1444439 : Blo 960589 1444439 := bstep (se 1 (by rfl) ⟨1083329, by rfl⟩ : syracuseStep 1444439 = 2166659) B2166659
theorem B1083991 : Blo 960589 1083991 := bstep (se 1 (by rfl) ⟨812993, by rfl⟩ : syracuseStep 1083991 = 1625987) B1625987
theorem B7309925 : Blo 960589 7309925 := bstep (se 4 (by rfl) ⟨685305, by rfl⟩ : syracuseStep 7309925 = 1370611) B1370611
theorem B2165363 : Blo 960589 2165363 := bstep (se 1 (by rfl) ⟨1624022, by rfl⟩ : syracuseStep 2165363 = 3248045) B3248045
theorem B2165399 : Blo 960589 2165399 := bstep (se 1 (by rfl) ⟨1624049, by rfl⟩ : syracuseStep 2165399 = 3248099) B3248099
theorem B1444505 : Blo 960589 1444505 := bstep (se 2 (by rfl) ⟨541689, by rfl⟩ : syracuseStep 1444505 = 1083379) B1083379
theorem B1444619 : Blo 960589 1444619 := bstep (se 1 (by rfl) ⟨1083464, by rfl⟩ : syracuseStep 1444619 = 2166929) B2166929
theorem B1084171 : Blo 960589 1084171 := bstep (se 1 (by rfl) ⟨813128, by rfl⟩ : syracuseStep 1084171 = 1626257) B1626257
theorem B1444631 : Blo 960589 1444631 := bstep (se 1 (by rfl) ⟨1083473, by rfl⟩ : syracuseStep 1444631 = 2166947) B2166947
theorem B2165579 : Blo 960589 2165579 := bstep (se 1 (by rfl) ⟨1624184, by rfl⟩ : syracuseStep 2165579 = 3248369) B3248369
theorem B1444697 : Blo 960589 1444697 := bstep (se 2 (by rfl) ⟨541761, by rfl⟩ : syracuseStep 1444697 = 1083523) B1083523
theorem B10980197 : Blo 960589 10980197 := bstep (se 4 (by rfl) ⟨1029393, by rfl⟩ : syracuseStep 10980197 = 2058787) B2058787
theorem B1084279 : Blo 960589 1084279 := bstep (se 1 (by rfl) ⟨813209, by rfl⟩ : syracuseStep 1084279 = 1626419) B1626419
theorem B2165633 : Blo 960589 2165633 := bstep (se 2 (by rfl) ⟨812112, by rfl⟩ : syracuseStep 2165633 = 1624225) B1624225
theorem B1444811 : Blo 960589 1444811 := bstep (se 1 (by rfl) ⟨1083608, by rfl⟩ : syracuseStep 1444811 = 2167217) B2167217
theorem B1444823 : Blo 960589 1444823 := bstep (se 1 (by rfl) ⟨1083617, by rfl⟩ : syracuseStep 1444823 = 2167235) B2167235
theorem B3247127 : Blo 960589 3247127 := bstep (se 1 (by rfl) ⟨2435345, by rfl⟩ : syracuseStep 3247127 = 4870691) B4870691
theorem B1444889 : Blo 960589 1444889 := bstep (se 2 (by rfl) ⟨541833, by rfl⟩ : syracuseStep 1444889 = 1083667) B1083667
theorem B1084459 : Blo 960589 1084459 := bstep (se 1 (by rfl) ⟨813344, by rfl⟩ : syracuseStep 1084459 = 1626689) B1626689
theorem B2198593 : Blo 960589 2198593 := bstep (se 2 (by rfl) ⟨824472, by rfl⟩ : syracuseStep 2198593 = 1648945) B1648945
theorem B7310411 : Blo 960589 7310411 := bstep (se 1 (by rfl) ⟨5482808, by rfl⟩ : syracuseStep 7310411 = 10965617) B10965617
theorem B2165849 : Blo 960589 2165849 := bstep (se 2 (by rfl) ⟨812193, by rfl⟩ : syracuseStep 2165849 = 1624387) B1624387
theorem B1445003 : Blo 960589 1445003 := bstep (se 1 (by rfl) ⟨1083752, by rfl⟩ : syracuseStep 1445003 = 2167505) B2167505
theorem B1445015 : Blo 960589 1445015 := bstep (se 1 (by rfl) ⟨1083761, by rfl⟩ : syracuseStep 1445015 = 2167523) B2167523
theorem B1084567 : Blo 960589 1084567 := bstep (se 1 (by rfl) ⟨813425, by rfl⟩ : syracuseStep 1084567 = 1626851) B1626851
theorem B2165939 : Blo 960589 2165939 := bstep (se 1 (by rfl) ⟨1624454, by rfl⟩ : syracuseStep 2165939 = 3248909) B3248909
theorem B2165975 : Blo 960589 2165975 := bstep (se 1 (by rfl) ⟨1624481, by rfl⟩ : syracuseStep 2165975 = 3248963) B3248963
theorem B1445081 : Blo 960589 1445081 := bstep (se 2 (by rfl) ⟨541905, by rfl⟩ : syracuseStep 1445081 = 1083811) B1083811
theorem B1445195 : Blo 960589 1445195 := bstep (se 1 (by rfl) ⟨1083896, by rfl⟩ : syracuseStep 1445195 = 2167793) B2167793
theorem B1084747 : Blo 960589 1084747 := bstep (se 1 (by rfl) ⟨813560, by rfl⟩ : syracuseStep 1084747 = 1627121) B1627121
theorem B1445207 : Blo 960589 1445207 := bstep (se 1 (by rfl) ⟨1083905, by rfl⟩ : syracuseStep 1445207 = 2167811) B2167811
theorem B2166155 : Blo 960589 2166155 := bstep (se 1 (by rfl) ⟨1624616, by rfl⟩ : syracuseStep 2166155 = 3249233) B3249233
theorem B35130773 : Blo 960589 35130773 := bstep (se 6 (by rfl) ⟨823377, by rfl⟩ : syracuseStep 35130773 = 1646755) B1646755
theorem B1445273 : Blo 960589 1445273 := bstep (se 2 (by rfl) ⟨541977, by rfl⟩ : syracuseStep 1445273 = 1083955) B1083955
theorem B1084855 : Blo 960589 1084855 := bstep (se 1 (by rfl) ⟨813641, by rfl⟩ : syracuseStep 1084855 = 1627283) B1627283
theorem B2166209 : Blo 960589 2166209 := bstep (se 2 (by rfl) ⟨812328, by rfl⟩ : syracuseStep 2166209 = 1624657) B1624657
theorem B1445387 : Blo 960589 1445387 := bstep (se 1 (by rfl) ⟨1084040, by rfl⟩ : syracuseStep 1445387 = 2168081) B2168081
theorem B1445399 : Blo 960589 1445399 := bstep (se 1 (by rfl) ⟨1084049, by rfl⟩ : syracuseStep 1445399 = 2168099) B2168099
theorem B3247667 : Blo 960589 3247667 := bstep (se 1 (by rfl) ⟨2435750, by rfl⟩ : syracuseStep 3247667 = 4871501) B4871501
theorem B1445465 : Blo 960589 1445465 := bstep (se 2 (by rfl) ⟨542049, by rfl⟩ : syracuseStep 1445465 = 1084099) B1084099
theorem B1085035 : Blo 960589 1085035 := bstep (se 1 (by rfl) ⟨813776, by rfl⟩ : syracuseStep 1085035 = 1627553) B1627553
theorem B2166425 : Blo 960589 2166425 := bstep (se 2 (by rfl) ⟨812409, by rfl⟩ : syracuseStep 2166425 = 1624819) B1624819
theorem B1445579 : Blo 960589 1445579 := bstep (se 1 (by rfl) ⟨1084184, by rfl⟩ : syracuseStep 1445579 = 2168369) B2168369
theorem B1445591 : Blo 960589 1445591 := bstep (se 1 (by rfl) ⟨1084193, by rfl⟩ : syracuseStep 1445591 = 2168387) B2168387
theorem B1085143 : Blo 960589 1085143 := bstep (se 1 (by rfl) ⟨813857, by rfl⟩ : syracuseStep 1085143 = 1627715) B1627715
theorem B2166515 : Blo 960589 2166515 := bstep (se 1 (by rfl) ⟨1624886, by rfl⟩ : syracuseStep 2166515 = 3249773) B3249773
theorem B2166551 : Blo 960589 2166551 := bstep (se 1 (by rfl) ⟨1624913, by rfl⟩ : syracuseStep 2166551 = 3249827) B3249827
theorem B1445657 : Blo 960589 1445657 := bstep (se 2 (by rfl) ⟨542121, by rfl⟩ : syracuseStep 1445657 = 1084243) B1084243
theorem B3247937 : Blo 960589 3247937 := bstep (se 2 (by rfl) ⟨1217976, by rfl⟩ : syracuseStep 3247937 = 2435953) B2435953
theorem B1445771 : Blo 960589 1445771 := bstep (se 1 (by rfl) ⟨1084328, by rfl⟩ : syracuseStep 1445771 = 2168657) B2168657
theorem B1445783 : Blo 960589 1445783 := bstep (se 1 (by rfl) ⟨1084337, by rfl⟩ : syracuseStep 1445783 = 2168675) B2168675
theorem B2166731 : Blo 960589 2166731 := bstep (se 1 (by rfl) ⟨1625048, by rfl⟩ : syracuseStep 2166731 = 3250097) B3250097
theorem B1445849 : Blo 960589 1445849 := bstep (se 2 (by rfl) ⟨542193, by rfl⟩ : syracuseStep 1445849 = 1084387) B1084387
theorem B2166785 : Blo 960589 2166785 := bstep (se 2 (by rfl) ⟨812544, by rfl⟩ : syracuseStep 2166785 = 1625089) B1625089
theorem B1445963 : Blo 960589 1445963 := bstep (se 1 (by rfl) ⟨1084472, by rfl⟩ : syracuseStep 1445963 = 2168945) B2168945
theorem B1445975 : Blo 960589 1445975 := bstep (se 1 (by rfl) ⟨1084481, by rfl⟩ : syracuseStep 1445975 = 2168963) B2168963
theorem B6951005 : Blo 960589 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B1446041 : Blo 960589 1446041 := bstep (se 2 (by rfl) ⟨542265, by rfl⟩ : syracuseStep 1446041 = 1084531) B1084531
theorem B2167001 : Blo 960589 2167001 := bstep (se 2 (by rfl) ⟨812625, by rfl⟩ : syracuseStep 2167001 = 1625251) B1625251
theorem B1446155 : Blo 960589 1446155 := bstep (se 1 (by rfl) ⟨1084616, by rfl⟩ : syracuseStep 1446155 = 2169233) B2169233
theorem B1446167 : Blo 960589 1446167 := bstep (se 1 (by rfl) ⟨1084625, by rfl⟩ : syracuseStep 1446167 = 2169251) B2169251
theorem B2167091 : Blo 960589 2167091 := bstep (se 1 (by rfl) ⟨1625318, by rfl⟩ : syracuseStep 2167091 = 3250637) B3250637
theorem B2167127 : Blo 960589 2167127 := bstep (se 1 (by rfl) ⟨1625345, by rfl⟩ : syracuseStep 2167127 = 3250691) B3250691
theorem B1446233 : Blo 960589 1446233 := bstep (se 2 (by rfl) ⟨542337, by rfl⟩ : syracuseStep 1446233 = 1084675) B1084675
theorem B3248477 : Blo 960589 3248477 := bstep (se 3 (by rfl) ⟨609089, by rfl⟩ : syracuseStep 3248477 = 1218179) B1218179
theorem B8327555 : Blo 960589 8327555 := bstep (se 1 (by rfl) ⟨6245666, by rfl⟩ : syracuseStep 8327555 = 12491333) B12491333
theorem B1446347 : Blo 960589 1446347 := bstep (se 1 (by rfl) ⟨1084760, by rfl⟩ : syracuseStep 1446347 = 2169521) B2169521
theorem B1446359 : Blo 960589 1446359 := bstep (se 1 (by rfl) ⟨1084769, by rfl⟩ : syracuseStep 1446359 = 2169539) B2169539
theorem B1217035 : Blo 960589 1217035 := bstep (se 1 (by rfl) ⟨912776, by rfl⟩ : syracuseStep 1217035 = 1825553) B1825553
theorem B2167307 : Blo 960589 2167307 := bstep (se 1 (by rfl) ⟨1625480, by rfl⟩ : syracuseStep 2167307 = 3250961) B3250961
theorem B1446425 : Blo 960589 1446425 := bstep (se 2 (by rfl) ⟨542409, by rfl⟩ : syracuseStep 1446425 = 1084819) B1084819
theorem B2167361 : Blo 960589 2167361 := bstep (se 2 (by rfl) ⟨812760, by rfl⟩ : syracuseStep 2167361 = 1625521) B1625521
theorem B6165085 : Blo 960589 6165085 := bstep (se 3 (by rfl) ⟨1155953, by rfl⟩ : syracuseStep 6165085 = 2311907) B2311907
theorem B1446539 : Blo 960589 1446539 := bstep (se 1 (by rfl) ⟨1084904, by rfl⟩ : syracuseStep 1446539 = 2169809) B2169809
theorem B1446551 : Blo 960589 1446551 := bstep (se 1 (by rfl) ⟨1084913, by rfl⟩ : syracuseStep 1446551 = 2169827) B2169827
theorem B3085003 : Blo 960589 3085003 := bstep (se 1 (by rfl) ⟨2313752, by rfl⟩ : syracuseStep 3085003 = 4627505) B4627505
theorem B1446617 : Blo 960589 1446617 := bstep (se 2 (by rfl) ⟨542481, by rfl⟩ : syracuseStep 1446617 = 1084963) B1084963
theorem B2167577 : Blo 960589 2167577 := bstep (se 2 (by rfl) ⟨812841, by rfl⟩ : syracuseStep 2167577 = 1625683) B1625683
theorem B1446731 : Blo 960589 1446731 := bstep (se 1 (by rfl) ⟨1085048, by rfl⟩ : syracuseStep 1446731 = 2170097) B2170097
theorem B1446743 : Blo 960589 1446743 := bstep (se 1 (by rfl) ⟨1085057, by rfl⟩ : syracuseStep 1446743 = 2170115) B2170115
theorem B2167667 : Blo 960589 2167667 := bstep (se 1 (by rfl) ⟨1625750, by rfl⟩ : syracuseStep 2167667 = 3251501) B3251501
theorem B2167703 : Blo 960589 2167703 := bstep (se 1 (by rfl) ⟨1625777, by rfl⟩ : syracuseStep 2167703 = 3251555) B3251555
theorem B1643417 : Blo 960589 1643417 := bstep (se 2 (by rfl) ⟨616281, by rfl⟩ : syracuseStep 1643417 = 1232563) B1232563
theorem B1446809 : Blo 960589 1446809 := bstep (se 2 (by rfl) ⟨542553, by rfl⟩ : syracuseStep 1446809 = 1085107) B1085107
theorem B3085235 : Blo 960589 3085235 := bstep (se 1 (by rfl) ⟨2313926, by rfl⟩ : syracuseStep 3085235 = 4627853) B4627853
theorem B8229923 : Blo 960589 8229923 := bstep (se 1 (by rfl) ⟨6172442, by rfl⟩ : syracuseStep 8229923 = 12344885) B12344885
theorem B2167883 : Blo 960589 2167883 := bstep (se 1 (by rfl) ⟨1625912, by rfl⟩ : syracuseStep 2167883 = 3251825) B3251825
theorem B2167937 : Blo 960589 2167937 := bstep (se 2 (by rfl) ⟨812976, by rfl⟩ : syracuseStep 2167937 = 1625953) B1625953
theorem B2168153 : Blo 960589 2168153 := bstep (se 2 (by rfl) ⟨813057, by rfl⟩ : syracuseStep 2168153 = 1626115) B1626115
theorem B2168243 : Blo 960589 2168243 := bstep (se 1 (by rfl) ⟨1626182, by rfl⟩ : syracuseStep 2168243 = 3252365) B3252365
theorem B3249611 : Blo 960589 3249611 := bstep (se 1 (by rfl) ⟨2437208, by rfl⟩ : syracuseStep 3249611 = 4874417) B4874417
theorem B1218007 : Blo 960589 1218007 := bstep (se 1 (by rfl) ⟨913505, by rfl⟩ : syracuseStep 1218007 = 1827011) B1827011
theorem B2168279 : Blo 960589 2168279 := bstep (se 1 (by rfl) ⟨1626209, by rfl⟩ : syracuseStep 2168279 = 3252419) B3252419
theorem B2168459 : Blo 960589 2168459 := bstep (se 1 (by rfl) ⟨1626344, by rfl⟩ : syracuseStep 2168459 = 3252689) B3252689
theorem B2168513 : Blo 960589 2168513 := bstep (se 2 (by rfl) ⟨813192, by rfl⟩ : syracuseStep 2168513 = 1626385) B1626385
theorem B3249881 : Blo 960589 3249881 := bstep (se 2 (by rfl) ⟨1218705, by rfl⟩ : syracuseStep 3249881 = 2437411) B2437411
theorem B2168729 : Blo 960589 2168729 := bstep (se 2 (by rfl) ⟨813273, by rfl⟩ : syracuseStep 2168729 = 1626547) B1626547
theorem B2168819 : Blo 960589 2168819 := bstep (se 1 (by rfl) ⟨1626614, by rfl⟩ : syracuseStep 2168819 = 3253229) B3253229
theorem B2168855 : Blo 960589 2168855 := bstep (se 1 (by rfl) ⟨1626641, by rfl⟩ : syracuseStep 2168855 = 3253283) B3253283
theorem B2169035 : Blo 960589 2169035 := bstep (se 1 (by rfl) ⟨1626776, by rfl⟩ : syracuseStep 2169035 = 3253553) B3253553
theorem B5478617 : Blo 960589 5478617 := bstep (se 2 (by rfl) ⟨2054481, by rfl⟩ : syracuseStep 5478617 = 4108963) B4108963
theorem B2169089 : Blo 960589 2169089 := bstep (se 2 (by rfl) ⟨813408, by rfl⟩ : syracuseStep 2169089 = 1626817) B1626817
theorem B1218827 : Blo 960589 1218827 := bstep (se 1 (by rfl) ⟨914120, by rfl⟩ : syracuseStep 1218827 = 1828241) B1828241
theorem B3250583 : Blo 960589 3250583 := bstep (se 1 (by rfl) ⟨2437937, by rfl⟩ : syracuseStep 3250583 = 4875875) B4875875
theorem B2169305 : Blo 960589 2169305 := bstep (se 2 (by rfl) ⟨813489, by rfl⟩ : syracuseStep 2169305 = 1626979) B1626979
theorem B2169395 : Blo 960589 2169395 := bstep (se 1 (by rfl) ⟨1627046, by rfl⟩ : syracuseStep 2169395 = 3254093) B3254093
theorem B2169431 : Blo 960589 2169431 := bstep (se 1 (by rfl) ⟨1627073, by rfl⟩ : syracuseStep 2169431 = 3254147) B3254147
theorem B10394243 : Blo 960589 10394243 := bstep (se 1 (by rfl) ⟨7795682, by rfl⟩ : syracuseStep 10394243 = 15591365) B15591365
theorem B2431691 : Blo 960589 2431691 := bstep (se 1 (by rfl) ⟨1823768, by rfl⟩ : syracuseStep 2431691 = 3647537) B3647537
theorem B3906307 : Blo 960589 3906307 := bstep (se 1 (by rfl) ⟨2929730, by rfl⟩ : syracuseStep 3906307 = 5859461) B5859461
theorem B2169611 : Blo 960589 2169611 := bstep (se 1 (by rfl) ⟨1627208, by rfl⟩ : syracuseStep 2169611 = 3254417) B3254417
theorem B2169665 : Blo 960589 2169665 := bstep (se 2 (by rfl) ⟨813624, by rfl⟩ : syracuseStep 2169665 = 1627249) B1627249
theorem B3251123 : Blo 960589 3251123 := bstep (se 1 (by rfl) ⟨2438342, by rfl⟩ : syracuseStep 3251123 = 4876685) B4876685
theorem B1219531 : Blo 960589 1219531 := bstep (se 1 (by rfl) ⟨914648, by rfl⟩ : syracuseStep 1219531 = 1829297) B1829297
theorem B1645579 : Blo 960589 1645579 := bstep (se 1 (by rfl) ⟨1234184, by rfl⟩ : syracuseStep 1645579 = 2468369) B2468369
theorem B2169881 : Blo 960589 2169881 := bstep (se 2 (by rfl) ⟨813705, by rfl⟩ : syracuseStep 2169881 = 1627411) B1627411
theorem B2432065 : Blo 960589 2432065 := bstep (se 2 (by rfl) ⟨912024, by rfl⟩ : syracuseStep 2432065 = 1824049) B1824049
theorem B1645655 : Blo 960589 1645655 := bstep (se 1 (by rfl) ⟨1234241, by rfl⟩ : syracuseStep 1645655 = 2468483) B2468483
theorem B4103257 : Blo 960589 4103257 := bstep (se 2 (by rfl) ⟨1538721, by rfl⟩ : syracuseStep 4103257 = 3077443) B3077443
theorem B2169971 : Blo 960589 2169971 := bstep (se 1 (by rfl) ⟨1627478, by rfl⟩ : syracuseStep 2169971 = 3254957) B3254957
theorem B2170007 : Blo 960589 2170007 := bstep (se 1 (by rfl) ⟨1627505, by rfl⟩ : syracuseStep 2170007 = 3255011) B3255011
theorem B3251393 : Blo 960589 3251393 := bstep (se 2 (by rfl) ⟨1219272, by rfl⟩ : syracuseStep 3251393 = 2438545) B2438545
theorem B1219799 : Blo 960589 1219799 := bstep (se 1 (by rfl) ⟨914849, by rfl⟩ : syracuseStep 1219799 = 1829699) B1829699
theorem B2170187 : Blo 960589 2170187 := bstep (se 1 (by rfl) ⟨1627640, by rfl⟩ : syracuseStep 2170187 = 3255281) B3255281
theorem B2170241 : Blo 960589 2170241 := bstep (se 2 (by rfl) ⟨813840, by rfl⟩ : syracuseStep 2170241 = 1627681) B1627681
theorem B16424369 : Blo 960589 16424369 := bstep (se 2 (by rfl) ⟨6159138, by rfl⟩ : syracuseStep 16424369 = 12318277) B12318277
theorem B1318361 : Blo 960589 1318361 := bstep (se 2 (by rfl) ⟨494385, by rfl⟩ : syracuseStep 1318361 = 988771) B988771
theorem B2432663 : Blo 960589 2432663 := bstep (se 1 (by rfl) ⟨1824497, by rfl⟩ : syracuseStep 2432663 = 3648995) B3648995
theorem B3251933 : Blo 960589 3251933 := bstep (se 3 (by rfl) ⟨609737, by rfl⟩ : syracuseStep 3251933 = 1219475) B1219475
theorem B3907379 : Blo 960589 3907379 := bstep (se 1 (by rfl) ⟨2930534, by rfl⟩ : syracuseStep 3907379 = 5861069) B5861069
theorem B5480257 : Blo 960589 5480257 := bstep (se 2 (by rfl) ⟨2055096, by rfl⟩ : syracuseStep 5480257 = 4110193) B4110193
theorem B1220503 : Blo 960589 1220503 := bstep (se 1 (by rfl) ⟨915377, by rfl⟩ : syracuseStep 1220503 = 1830755) B1830755
theorem B4104215 : Blo 960589 4104215 := bstep (se 1 (by rfl) ⟨3078161, by rfl⟩ : syracuseStep 4104215 = 6156323) B6156323
theorem B7118923 : Blo 960589 7118923 := bstep (se 1 (by rfl) ⟨5339192, by rfl⟩ : syracuseStep 7118923 = 10678385) B10678385
theorem B7315757 : Blo 960589 7315757 := bstep (se 3 (by rfl) ⟨1371704, by rfl⟩ : syracuseStep 7315757 = 2743409) B2743409
theorem B2433473 : Blo 960589 2433473 := bstep (se 2 (by rfl) ⟨912552, by rfl⟩ : syracuseStep 2433473 = 1825105) B1825105
theorem B13902349 : Blo 960589 13902349 := bstep (se 3 (by rfl) ⟨2606690, by rfl⟩ : syracuseStep 13902349 = 5213381) B5213381
theorem B9872077 : Blo 960589 9872077 := bstep (se 3 (by rfl) ⟨1851014, by rfl⟩ : syracuseStep 9872077 = 3702029) B3702029
theorem B63382337 : Blo 960589 63382337 := bstep (se 2 (by rfl) ⟨23768376, by rfl⟩ : syracuseStep 63382337 = 47536753) B47536753
theorem B3253067 : Blo 960589 3253067 := bstep (se 1 (by rfl) ⟨2439800, by rfl⟩ : syracuseStep 3253067 = 4879601) B4879601
theorem B6169445 : Blo 960589 6169445 := bstep (se 4 (by rfl) ⟨578385, by rfl⟩ : syracuseStep 6169445 = 1156771) B1156771
theorem B11707253 : Blo 960589 11707253 := bstep (se 5 (by rfl) ⟨548777, by rfl⟩ : syracuseStep 11707253 = 1097555) B1097555
theorem B2434009 : Blo 960589 2434009 := bstep (se 2 (by rfl) ⟨912753, by rfl⟩ : syracuseStep 2434009 = 1825507) B1825507
theorem B3253337 : Blo 960589 3253337 := bstep (se 2 (by rfl) ⟨1220001, by rfl⟩ : syracuseStep 3253337 = 2440003) B2440003
theorem B2598323 : Blo 960589 2598323 := bstep (se 1 (by rfl) ⟨1948742, by rfl⟩ : syracuseStep 2598323 = 3897485) B3897485
theorem B6596113 : Blo 960589 6596113 := bstep (se 2 (by rfl) ⟨2473542, by rfl⟩ : syracuseStep 6596113 = 4947085) B4947085
theorem B2598475 : Blo 960589 2598475 := bstep (se 1 (by rfl) ⟨1948856, by rfl⟩ : syracuseStep 2598475 = 3897713) B3897713
theorem B7317209 : Blo 960589 7317209 := bstep (se 2 (by rfl) ⟨2743953, by rfl⟩ : syracuseStep 7317209 = 5487907) B5487907
theorem B3254039 : Blo 960589 3254039 := bstep (se 1 (by rfl) ⟨2440529, by rfl⟩ : syracuseStep 3254039 = 4881059) B4881059
theorem B6924163 : Blo 960589 6924163 := bstep (se 1 (by rfl) ⟨5193122, by rfl⟩ : syracuseStep 6924163 = 10386245) B10386245
theorem B6170519 : Blo 960589 6170519 := bstep (se 1 (by rfl) ⟨4627889, by rfl⟩ : syracuseStep 6170519 = 9255779) B9255779
theorem B6924305 : Blo 960589 6924305 := bstep (se 2 (by rfl) ⟨2596614, by rfl⟩ : syracuseStep 6924305 = 5193229) B5193229
theorem B3123251 : Blo 960589 3123251 := bstep (se 1 (by rfl) ⟨2342438, by rfl⟩ : syracuseStep 3123251 = 4684877) B4684877
theorem B2435123 : Blo 960589 2435123 := bstep (se 1 (by rfl) ⟨1826342, by rfl⟩ : syracuseStep 2435123 = 3652685) B3652685
theorem B960599 : Blo 960589 960599 := bstep (se 1 (by rfl) ⟨720449, by rfl⟩ : syracuseStep 960599 = 1440899) B1440899
theorem B960619 : Blo 960589 960619 := bstep (se 1 (by rfl) ⟨720464, by rfl⟩ : syracuseStep 960619 = 1440929) B1440929
theorem B960631 : Blo 960589 960631 := bstep (se 1 (by rfl) ⟨720473, by rfl⟩ : syracuseStep 960631 = 1440947) B1440947
theorem B6924419 : Blo 960589 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B960651 : Blo 960589 960651 := bstep (se 1 (by rfl) ⟨720488, by rfl⟩ : syracuseStep 960651 = 1440977) B1440977
theorem B960663 : Blo 960589 960663 := bstep (se 1 (by rfl) ⟨720497, by rfl⟩ : syracuseStep 960663 = 1440995) B1440995
theorem B1026199 : Blo 960589 1026199 := bstep (se 1 (by rfl) ⟨769649, by rfl⟩ : syracuseStep 1026199 = 1539299) B1539299
theorem B960683 : Blo 960589 960683 := bstep (se 1 (by rfl) ⟨720512, by rfl⟩ : syracuseStep 960683 = 1441025) B1441025
theorem B960695 : Blo 960589 960695 := bstep (se 1 (by rfl) ⟨720521, by rfl⟩ : syracuseStep 960695 = 1441043) B1441043
theorem B960715 : Blo 960589 960715 := bstep (se 1 (by rfl) ⟨720536, by rfl⟩ : syracuseStep 960715 = 1441073) B1441073
theorem B960727 : Blo 960589 960727 := bstep (se 1 (by rfl) ⟨720545, by rfl⟩ : syracuseStep 960727 = 1441091) B1441091
theorem B960747 : Blo 960589 960747 := bstep (se 1 (by rfl) ⟨720560, by rfl⟩ : syracuseStep 960747 = 1441121) B1441121
theorem B960759 : Blo 960589 960759 := bstep (se 1 (by rfl) ⟨720569, by rfl⟩ : syracuseStep 960759 = 1441139) B1441139
theorem B960779 : Blo 960589 960779 := bstep (se 1 (by rfl) ⟨720584, by rfl⟩ : syracuseStep 960779 = 1441169) B1441169
theorem B960791 : Blo 960589 960791 := bstep (se 1 (by rfl) ⟨720593, by rfl⟩ : syracuseStep 960791 = 1441187) B1441187
theorem B960811 : Blo 960589 960811 := bstep (se 1 (by rfl) ⟨720608, by rfl⟩ : syracuseStep 960811 = 1441217) B1441217
theorem B3254579 : Blo 960589 3254579 := bstep (se 1 (by rfl) ⟨2440934, by rfl⟩ : syracuseStep 3254579 = 4881869) B4881869
theorem B960823 : Blo 960589 960823 := bstep (se 1 (by rfl) ⟨720617, by rfl⟩ : syracuseStep 960823 = 1441235) B1441235
theorem B960843 : Blo 960589 960843 := bstep (se 1 (by rfl) ⟨720632, by rfl⟩ : syracuseStep 960843 = 1441265) B1441265
theorem B960855 : Blo 960589 960855 := bstep (se 1 (by rfl) ⟨720641, by rfl⟩ : syracuseStep 960855 = 1441283) B1441283
theorem B2435417 : Blo 960589 2435417 := bstep (se 2 (by rfl) ⟨913281, by rfl⟩ : syracuseStep 2435417 = 1826563) B1826563
theorem B960875 : Blo 960589 960875 := bstep (se 1 (by rfl) ⟨720656, by rfl⟩ : syracuseStep 960875 = 1441313) B1441313
theorem B960887 : Blo 960589 960887 := bstep (se 1 (by rfl) ⟨720665, by rfl⟩ : syracuseStep 960887 = 1441331) B1441331
theorem B960907 : Blo 960589 960907 := bstep (se 1 (by rfl) ⟨720680, by rfl⟩ : syracuseStep 960907 = 1441361) B1441361
theorem B960919 : Blo 960589 960919 := bstep (se 1 (by rfl) ⟨720689, by rfl⟩ : syracuseStep 960919 = 1441379) B1441379
theorem B960939 : Blo 960589 960939 := bstep (se 1 (by rfl) ⟨720704, by rfl⟩ : syracuseStep 960939 = 1441409) B1441409
theorem B960951 : Blo 960589 960951 := bstep (se 1 (by rfl) ⟨720713, by rfl⟩ : syracuseStep 960951 = 1441427) B1441427
theorem B960971 : Blo 960589 960971 := bstep (se 1 (by rfl) ⟨720728, by rfl⟩ : syracuseStep 960971 = 1441457) B1441457
theorem B960983 : Blo 960589 960983 := bstep (se 1 (by rfl) ⟨720737, by rfl⟩ : syracuseStep 960983 = 1441475) B1441475
theorem B961003 : Blo 960589 961003 := bstep (se 1 (by rfl) ⟨720752, by rfl⟩ : syracuseStep 961003 = 1441505) B1441505
theorem B961015 : Blo 960589 961015 := bstep (se 1 (by rfl) ⟨720761, by rfl⟩ : syracuseStep 961015 = 1441523) B1441523
theorem B961035 : Blo 960589 961035 := bstep (se 1 (by rfl) ⟨720776, by rfl⟩ : syracuseStep 961035 = 1441553) B1441553
theorem B3648023 : Blo 960589 3648023 := bstep (se 1 (by rfl) ⟨2736017, by rfl⟩ : syracuseStep 3648023 = 5472035) B5472035
theorem B961047 : Blo 960589 961047 := bstep (se 1 (by rfl) ⟨720785, by rfl⟩ : syracuseStep 961047 = 1441571) B1441571
theorem B961067 : Blo 960589 961067 := bstep (se 1 (by rfl) ⟨720800, by rfl⟩ : syracuseStep 961067 = 1441601) B1441601
theorem B961079 : Blo 960589 961079 := bstep (se 1 (by rfl) ⟨720809, by rfl⟩ : syracuseStep 961079 = 1441619) B1441619
theorem B3254849 : Blo 960589 3254849 := bstep (se 2 (by rfl) ⟨1220568, by rfl⟩ : syracuseStep 3254849 = 2441137) B2441137
theorem B961099 : Blo 960589 961099 := bstep (se 1 (by rfl) ⟨720824, by rfl⟩ : syracuseStep 961099 = 1441649) B1441649
theorem B961111 : Blo 960589 961111 := bstep (se 1 (by rfl) ⟨720833, by rfl⟩ : syracuseStep 961111 = 1441667) B1441667
theorem B961131 : Blo 960589 961131 := bstep (se 1 (by rfl) ⟨720848, by rfl⟩ : syracuseStep 961131 = 1441697) B1441697
theorem B961143 : Blo 960589 961143 := bstep (se 1 (by rfl) ⟨720857, by rfl⟩ : syracuseStep 961143 = 1441715) B1441715
theorem B961163 : Blo 960589 961163 := bstep (se 1 (by rfl) ⟨720872, by rfl⟩ : syracuseStep 961163 = 1441745) B1441745
theorem B961175 : Blo 960589 961175 := bstep (se 1 (by rfl) ⟨720881, by rfl⟩ : syracuseStep 961175 = 1441763) B1441763
theorem B961195 : Blo 960589 961195 := bstep (se 1 (by rfl) ⟨720896, by rfl⟩ : syracuseStep 961195 = 1441793) B1441793
theorem B961207 : Blo 960589 961207 := bstep (se 1 (by rfl) ⟨720905, by rfl⟩ : syracuseStep 961207 = 1441811) B1441811
theorem B961227 : Blo 960589 961227 := bstep (se 1 (by rfl) ⟨720920, by rfl⟩ : syracuseStep 961227 = 1441841) B1441841
theorem B961239 : Blo 960589 961239 := bstep (se 1 (by rfl) ⟨720929, by rfl⟩ : syracuseStep 961239 = 1441859) B1441859
theorem B961259 : Blo 960589 961259 := bstep (se 1 (by rfl) ⟨720944, by rfl⟩ : syracuseStep 961259 = 1441889) B1441889
theorem B961271 : Blo 960589 961271 := bstep (se 1 (by rfl) ⟨720953, by rfl⟩ : syracuseStep 961271 = 1441907) B1441907
theorem B961291 : Blo 960589 961291 := bstep (se 1 (by rfl) ⟨720968, by rfl⟩ : syracuseStep 961291 = 1441937) B1441937
theorem B961303 : Blo 960589 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B961323 : Blo 960589 961323 := bstep (se 1 (by rfl) ⟨720992, by rfl⟩ : syracuseStep 961323 = 1441985) B1441985
theorem B961335 : Blo 960589 961335 := bstep (se 1 (by rfl) ⟨721001, by rfl⟩ : syracuseStep 961335 = 1442003) B1442003
theorem B961355 : Blo 960589 961355 := bstep (se 1 (by rfl) ⟨721016, by rfl⟩ : syracuseStep 961355 = 1442033) B1442033
theorem B961367 : Blo 960589 961367 := bstep (se 1 (by rfl) ⟨721025, by rfl⟩ : syracuseStep 961367 = 1442051) B1442051
theorem B3910493 : Blo 960589 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B961387 : Blo 960589 961387 := bstep (se 1 (by rfl) ⟨721040, by rfl⟩ : syracuseStep 961387 = 1442081) B1442081
theorem B961399 : Blo 960589 961399 := bstep (se 1 (by rfl) ⟨721049, by rfl⟩ : syracuseStep 961399 = 1442099) B1442099
theorem B961419 : Blo 960589 961419 := bstep (se 1 (by rfl) ⟨721064, by rfl⟩ : syracuseStep 961419 = 1442129) B1442129
theorem B961431 : Blo 960589 961431 := bstep (se 1 (by rfl) ⟨721073, by rfl⟩ : syracuseStep 961431 = 1442147) B1442147
theorem B961451 : Blo 960589 961451 := bstep (se 1 (by rfl) ⟨721088, by rfl⟩ : syracuseStep 961451 = 1442177) B1442177
theorem B961463 : Blo 960589 961463 := bstep (se 1 (by rfl) ⟨721097, by rfl⟩ : syracuseStep 961463 = 1442195) B1442195
theorem B961483 : Blo 960589 961483 := bstep (se 1 (by rfl) ⟨721112, by rfl⟩ : syracuseStep 961483 = 1442225) B1442225
theorem B1027019 : Blo 960589 1027019 := bstep (se 1 (by rfl) ⟨770264, by rfl⟩ : syracuseStep 1027019 = 1540529) B1540529
theorem B961495 : Blo 960589 961495 := bstep (se 1 (by rfl) ⟨721121, by rfl⟩ : syracuseStep 961495 = 1442243) B1442243
theorem B961515 : Blo 960589 961515 := bstep (se 1 (by rfl) ⟨721136, by rfl⟩ : syracuseStep 961515 = 1442273) B1442273
theorem B961527 : Blo 960589 961527 := bstep (se 1 (by rfl) ⟨721145, by rfl⟩ : syracuseStep 961527 = 1442291) B1442291
theorem B961547 : Blo 960589 961547 := bstep (se 1 (by rfl) ⟨721160, by rfl⟩ : syracuseStep 961547 = 1442321) B1442321
theorem B961559 : Blo 960589 961559 := bstep (se 1 (by rfl) ⟨721169, by rfl⟩ : syracuseStep 961559 = 1442339) B1442339
theorem B961579 : Blo 960589 961579 := bstep (se 1 (by rfl) ⟨721184, by rfl⟩ : syracuseStep 961579 = 1442369) B1442369
theorem B961591 : Blo 960589 961591 := bstep (se 1 (by rfl) ⟨721193, by rfl⟩ : syracuseStep 961591 = 1442387) B1442387
theorem B961611 : Blo 960589 961611 := bstep (se 1 (by rfl) ⟨721208, by rfl⟩ : syracuseStep 961611 = 1442417) B1442417
theorem B961623 : Blo 960589 961623 := bstep (se 1 (by rfl) ⟨721217, by rfl⟩ : syracuseStep 961623 = 1442435) B1442435
theorem B3255389 : Blo 960589 3255389 := bstep (se 3 (by rfl) ⟨610385, by rfl⟩ : syracuseStep 3255389 = 1220771) B1220771
theorem B961643 : Blo 960589 961643 := bstep (se 1 (by rfl) ⟨721232, by rfl⟩ : syracuseStep 961643 = 1442465) B1442465
theorem B961655 : Blo 960589 961655 := bstep (se 1 (by rfl) ⟨721241, by rfl⟩ : syracuseStep 961655 = 1442483) B1442483
theorem B961675 : Blo 960589 961675 := bstep (se 1 (by rfl) ⟨721256, by rfl⟩ : syracuseStep 961675 = 1442513) B1442513
theorem B961687 : Blo 960589 961687 := bstep (se 1 (by rfl) ⟨721265, by rfl⟩ : syracuseStep 961687 = 1442531) B1442531
theorem B961707 : Blo 960589 961707 := bstep (se 1 (by rfl) ⟨721280, by rfl⟩ : syracuseStep 961707 = 1442561) B1442561
theorem B5483699 : Blo 960589 5483699 := bstep (se 1 (by rfl) ⟨4112774, by rfl⟩ : syracuseStep 5483699 = 8225549) B8225549
theorem B961719 : Blo 960589 961719 := bstep (se 1 (by rfl) ⟨721289, by rfl⟩ : syracuseStep 961719 = 1442579) B1442579
theorem B961739 : Blo 960589 961739 := bstep (se 1 (by rfl) ⟨721304, by rfl⟩ : syracuseStep 961739 = 1442609) B1442609
theorem B1158347 : Blo 960589 1158347 := bstep (se 1 (by rfl) ⟨868760, by rfl⟩ : syracuseStep 1158347 = 1737521) B1737521
theorem B961751 : Blo 960589 961751 := bstep (se 1 (by rfl) ⟨721313, by rfl⟩ : syracuseStep 961751 = 1442627) B1442627
theorem B961771 : Blo 960589 961771 := bstep (se 1 (by rfl) ⟨721328, by rfl⟩ : syracuseStep 961771 = 1442657) B1442657
theorem B961783 : Blo 960589 961783 := bstep (se 1 (by rfl) ⟨721337, by rfl⟩ : syracuseStep 961783 = 1442675) B1442675
theorem B961803 : Blo 960589 961803 := bstep (se 1 (by rfl) ⟨721352, by rfl⟩ : syracuseStep 961803 = 1442705) B1442705
theorem B961815 : Blo 960589 961815 := bstep (se 1 (by rfl) ⟨721361, by rfl⟩ : syracuseStep 961815 = 1442723) B1442723
theorem B961835 : Blo 960589 961835 := bstep (se 1 (by rfl) ⟨721376, by rfl⟩ : syracuseStep 961835 = 1442753) B1442753
theorem B961847 : Blo 960589 961847 := bstep (se 1 (by rfl) ⟨721385, by rfl⟩ : syracuseStep 961847 = 1442771) B1442771
theorem B961867 : Blo 960589 961867 := bstep (se 1 (by rfl) ⟨721400, by rfl⟩ : syracuseStep 961867 = 1442801) B1442801
theorem B961879 : Blo 960589 961879 := bstep (se 1 (by rfl) ⟨721409, by rfl⟩ : syracuseStep 961879 = 1442819) B1442819
theorem B961899 : Blo 960589 961899 := bstep (se 1 (by rfl) ⟨721424, by rfl⟩ : syracuseStep 961899 = 1442849) B1442849
theorem B961911 : Blo 960589 961911 := bstep (se 1 (by rfl) ⟨721433, by rfl⟩ : syracuseStep 961911 = 1442867) B1442867
theorem B961931 : Blo 960589 961931 := bstep (se 1 (by rfl) ⟨721448, by rfl⟩ : syracuseStep 961931 = 1442897) B1442897
theorem B4107665 : Blo 960589 4107665 := bstep (se 2 (by rfl) ⟨1540374, by rfl⟩ : syracuseStep 4107665 = 3080749) B3080749
theorem B961943 : Blo 960589 961943 := bstep (se 1 (by rfl) ⟨721457, by rfl⟩ : syracuseStep 961943 = 1442915) B1442915
theorem B961963 : Blo 960589 961963 := bstep (se 1 (by rfl) ⟨721472, by rfl⟩ : syracuseStep 961963 = 1442945) B1442945
theorem B961975 : Blo 960589 961975 := bstep (se 1 (by rfl) ⟨721481, by rfl⟩ : syracuseStep 961975 = 1442963) B1442963
theorem B961995 : Blo 960589 961995 := bstep (se 1 (by rfl) ⟨721496, by rfl⟩ : syracuseStep 961995 = 1442993) B1442993
theorem B962007 : Blo 960589 962007 := bstep (se 1 (by rfl) ⟨721505, by rfl⟩ : syracuseStep 962007 = 1443011) B1443011
theorem B962027 : Blo 960589 962027 := bstep (se 1 (by rfl) ⟨721520, by rfl⟩ : syracuseStep 962027 = 1443041) B1443041
theorem B962039 : Blo 960589 962039 := bstep (se 1 (by rfl) ⟨721529, by rfl⟩ : syracuseStep 962039 = 1443059) B1443059
theorem B962059 : Blo 960589 962059 := bstep (se 1 (by rfl) ⟨721544, by rfl⟩ : syracuseStep 962059 = 1443089) B1443089
theorem B962071 : Blo 960589 962071 := bstep (se 1 (by rfl) ⟨721553, by rfl⟩ : syracuseStep 962071 = 1443107) B1443107
theorem B962091 : Blo 960589 962091 := bstep (se 1 (by rfl) ⟨721568, by rfl⟩ : syracuseStep 962091 = 1443137) B1443137
theorem B962103 : Blo 960589 962103 := bstep (se 1 (by rfl) ⟨721577, by rfl⟩ : syracuseStep 962103 = 1443155) B1443155
theorem B962123 : Blo 960589 962123 := bstep (se 1 (by rfl) ⟨721592, by rfl⟩ : syracuseStep 962123 = 1443185) B1443185
theorem B962135 : Blo 960589 962135 := bstep (se 1 (by rfl) ⟨721601, by rfl⟩ : syracuseStep 962135 = 1443203) B1443203
theorem B4632157 : Blo 960589 4632157 := bstep (se 3 (by rfl) ⟨868529, by rfl⟩ : syracuseStep 4632157 = 1737059) B1737059
theorem B962155 : Blo 960589 962155 := bstep (se 1 (by rfl) ⟨721616, by rfl⟩ : syracuseStep 962155 = 1443233) B1443233
theorem B962167 : Blo 960589 962167 := bstep (se 1 (by rfl) ⟨721625, by rfl⟩ : syracuseStep 962167 = 1443251) B1443251
theorem B962187 : Blo 960589 962187 := bstep (se 1 (by rfl) ⟨721640, by rfl⟩ : syracuseStep 962187 = 1443281) B1443281
theorem B962199 : Blo 960589 962199 := bstep (se 1 (by rfl) ⟨721649, by rfl⟩ : syracuseStep 962199 = 1443299) B1443299
theorem B962219 : Blo 960589 962219 := bstep (se 1 (by rfl) ⟨721664, by rfl⟩ : syracuseStep 962219 = 1443329) B1443329
theorem B962231 : Blo 960589 962231 := bstep (se 1 (by rfl) ⟨721673, by rfl⟩ : syracuseStep 962231 = 1443347) B1443347
theorem B962251 : Blo 960589 962251 := bstep (se 1 (by rfl) ⟨721688, by rfl⟩ : syracuseStep 962251 = 1443377) B1443377
theorem B962263 : Blo 960589 962263 := bstep (se 1 (by rfl) ⟨721697, by rfl⟩ : syracuseStep 962263 = 1443395) B1443395
theorem B962283 : Blo 960589 962283 := bstep (se 1 (by rfl) ⟨721712, by rfl⟩ : syracuseStep 962283 = 1443425) B1443425
theorem B962295 : Blo 960589 962295 := bstep (se 1 (by rfl) ⟨721721, by rfl⟩ : syracuseStep 962295 = 1443443) B1443443
theorem B3649283 : Blo 960589 3649283 := bstep (se 1 (by rfl) ⟨2736962, by rfl⟩ : syracuseStep 3649283 = 5473925) B5473925
theorem B962315 : Blo 960589 962315 := bstep (se 1 (by rfl) ⟨721736, by rfl⟩ : syracuseStep 962315 = 1443473) B1443473
theorem B962327 : Blo 960589 962327 := bstep (se 1 (by rfl) ⟨721745, by rfl⟩ : syracuseStep 962327 = 1443491) B1443491
theorem B962347 : Blo 960589 962347 := bstep (se 1 (by rfl) ⟨721760, by rfl⟩ : syracuseStep 962347 = 1443521) B1443521
theorem B962359 : Blo 960589 962359 := bstep (se 1 (by rfl) ⟨721769, by rfl⟩ : syracuseStep 962359 = 1443539) B1443539
theorem B962379 : Blo 960589 962379 := bstep (se 1 (by rfl) ⟨721784, by rfl⟩ : syracuseStep 962379 = 1443569) B1443569
theorem B962391 : Blo 960589 962391 := bstep (se 1 (by rfl) ⟨721793, by rfl⟩ : syracuseStep 962391 = 1443587) B1443587
theorem B962411 : Blo 960589 962411 := bstep (se 1 (by rfl) ⟨721808, by rfl⟩ : syracuseStep 962411 = 1443617) B1443617
theorem B962423 : Blo 960589 962423 := bstep (se 1 (by rfl) ⟨721817, by rfl⟩ : syracuseStep 962423 = 1443635) B1443635
theorem B962443 : Blo 960589 962443 := bstep (se 1 (by rfl) ⟨721832, by rfl⟩ : syracuseStep 962443 = 1443665) B1443665
theorem B962455 : Blo 960589 962455 := bstep (se 1 (by rfl) ⟨721841, by rfl⟩ : syracuseStep 962455 = 1443683) B1443683
theorem B962475 : Blo 960589 962475 := bstep (se 1 (by rfl) ⟨721856, by rfl⟩ : syracuseStep 962475 = 1443713) B1443713
theorem B962487 : Blo 960589 962487 := bstep (se 1 (by rfl) ⟨721865, by rfl⟩ : syracuseStep 962487 = 1443731) B1443731
theorem B962507 : Blo 960589 962507 := bstep (se 1 (by rfl) ⟨721880, by rfl⟩ : syracuseStep 962507 = 1443761) B1443761
theorem B2437067 : Blo 960589 2437067 := bstep (se 1 (by rfl) ⟨1827800, by rfl⟩ : syracuseStep 2437067 = 3655601) B3655601
theorem B962519 : Blo 960589 962519 := bstep (se 1 (by rfl) ⟨721889, by rfl⟩ : syracuseStep 962519 = 1443779) B1443779
theorem B962539 : Blo 960589 962539 := bstep (se 1 (by rfl) ⟨721904, by rfl⟩ : syracuseStep 962539 = 1443809) B1443809
theorem B962551 : Blo 960589 962551 := bstep (se 1 (by rfl) ⟨721913, by rfl⟩ : syracuseStep 962551 = 1443827) B1443827
theorem B962571 : Blo 960589 962571 := bstep (se 1 (by rfl) ⟨721928, by rfl⟩ : syracuseStep 962571 = 1443857) B1443857
theorem B962583 : Blo 960589 962583 := bstep (se 1 (by rfl) ⟨721937, by rfl⟩ : syracuseStep 962583 = 1443875) B1443875
theorem B962603 : Blo 960589 962603 := bstep (se 1 (by rfl) ⟨721952, by rfl⟩ : syracuseStep 962603 = 1443905) B1443905
theorem B962615 : Blo 960589 962615 := bstep (se 1 (by rfl) ⟨721961, by rfl⟩ : syracuseStep 962615 = 1443923) B1443923
theorem B962635 : Blo 960589 962635 := bstep (se 1 (by rfl) ⟨721976, by rfl⟩ : syracuseStep 962635 = 1443953) B1443953
theorem B962647 : Blo 960589 962647 := bstep (se 1 (by rfl) ⟨721985, by rfl⟩ : syracuseStep 962647 = 1443971) B1443971
theorem B7319645 : Blo 960589 7319645 := bstep (se 3 (by rfl) ⟨1372433, by rfl⟩ : syracuseStep 7319645 = 2744867) B2744867
theorem B962667 : Blo 960589 962667 := bstep (se 1 (by rfl) ⟨722000, by rfl⟩ : syracuseStep 962667 = 1444001) B1444001
theorem B962679 : Blo 960589 962679 := bstep (se 1 (by rfl) ⟨722009, by rfl⟩ : syracuseStep 962679 = 1444019) B1444019
theorem B1028215 : Blo 960589 1028215 := bstep (se 1 (by rfl) ⟨771161, by rfl⟩ : syracuseStep 1028215 = 1542323) B1542323
theorem B962699 : Blo 960589 962699 := bstep (se 1 (by rfl) ⟨722024, by rfl⟩ : syracuseStep 962699 = 1444049) B1444049
theorem B962711 : Blo 960589 962711 := bstep (se 1 (by rfl) ⟨722033, by rfl⟩ : syracuseStep 962711 = 1444067) B1444067
theorem B962731 : Blo 960589 962731 := bstep (se 1 (by rfl) ⟨722048, by rfl⟩ : syracuseStep 962731 = 1444097) B1444097
theorem B962743 : Blo 960589 962743 := bstep (se 1 (by rfl) ⟨722057, by rfl⟩ : syracuseStep 962743 = 1444115) B1444115
theorem B962763 : Blo 960589 962763 := bstep (se 1 (by rfl) ⟨722072, by rfl⟩ : syracuseStep 962763 = 1444145) B1444145
theorem B962775 : Blo 960589 962775 := bstep (se 1 (by rfl) ⟨722081, by rfl⟩ : syracuseStep 962775 = 1444163) B1444163
theorem B962795 : Blo 960589 962795 := bstep (se 1 (by rfl) ⟨722096, by rfl⟩ : syracuseStep 962795 = 1444193) B1444193
theorem B962807 : Blo 960589 962807 := bstep (se 1 (by rfl) ⟨722105, by rfl⟩ : syracuseStep 962807 = 1444211) B1444211
theorem B962827 : Blo 960589 962827 := bstep (se 1 (by rfl) ⟨722120, by rfl⟩ : syracuseStep 962827 = 1444241) B1444241
theorem B962839 : Blo 960589 962839 := bstep (se 1 (by rfl) ⟨722129, by rfl⟩ : syracuseStep 962839 = 1444259) B1444259
theorem B962859 : Blo 960589 962859 := bstep (se 1 (by rfl) ⟨722144, by rfl⟩ : syracuseStep 962859 = 1444289) B1444289
theorem B4108589 : Blo 960589 4108589 := bstep (se 3 (by rfl) ⟨770360, by rfl⟩ : syracuseStep 4108589 = 1540721) B1540721
theorem B962871 : Blo 960589 962871 := bstep (se 1 (by rfl) ⟨722153, by rfl⟩ : syracuseStep 962871 = 1444307) B1444307
theorem B3289409 : Blo 960589 3289409 := bstep (se 2 (by rfl) ⟨1233528, by rfl⟩ : syracuseStep 3289409 = 2467057) B2467057
theorem B962891 : Blo 960589 962891 := bstep (se 1 (by rfl) ⟨722168, by rfl⟩ : syracuseStep 962891 = 1444337) B1444337
theorem B962903 : Blo 960589 962903 := bstep (se 1 (by rfl) ⟨722177, by rfl⟩ : syracuseStep 962903 = 1444355) B1444355
theorem B962923 : Blo 960589 962923 := bstep (se 1 (by rfl) ⟨722192, by rfl⟩ : syracuseStep 962923 = 1444385) B1444385
theorem B962935 : Blo 960589 962935 := bstep (se 1 (by rfl) ⟨722201, by rfl⟩ : syracuseStep 962935 = 1444403) B1444403
theorem B1028471 : Blo 960589 1028471 := bstep (se 1 (by rfl) ⟨771353, by rfl⟩ : syracuseStep 1028471 = 1542707) B1542707
theorem B962955 : Blo 960589 962955 := bstep (se 1 (by rfl) ⟨722216, by rfl⟩ : syracuseStep 962955 = 1444433) B1444433
theorem B962967 : Blo 960589 962967 := bstep (se 1 (by rfl) ⟨722225, by rfl⟩ : syracuseStep 962967 = 1444451) B1444451
theorem B962987 : Blo 960589 962987 := bstep (se 1 (by rfl) ⟨722240, by rfl⟩ : syracuseStep 962987 = 1444481) B1444481
theorem B7909811 : Blo 960589 7909811 := bstep (se 1 (by rfl) ⟨5932358, by rfl⟩ : syracuseStep 7909811 = 11864717) B11864717
theorem B962999 : Blo 960589 962999 := bstep (se 1 (by rfl) ⟨722249, by rfl⟩ : syracuseStep 962999 = 1444499) B1444499
theorem B963019 : Blo 960589 963019 := bstep (se 1 (by rfl) ⟨722264, by rfl⟩ : syracuseStep 963019 = 1444529) B1444529
theorem B963031 : Blo 960589 963031 := bstep (se 1 (by rfl) ⟨722273, by rfl⟩ : syracuseStep 963031 = 1444547) B1444547
theorem B963051 : Blo 960589 963051 := bstep (se 1 (by rfl) ⟨722288, by rfl⟩ : syracuseStep 963051 = 1444577) B1444577
theorem B963063 : Blo 960589 963063 := bstep (se 1 (by rfl) ⟨722297, by rfl⟩ : syracuseStep 963063 = 1444595) B1444595
theorem B963083 : Blo 960589 963083 := bstep (se 1 (by rfl) ⟨722312, by rfl⟩ : syracuseStep 963083 = 1444625) B1444625
theorem B963095 : Blo 960589 963095 := bstep (se 1 (by rfl) ⟨722321, by rfl⟩ : syracuseStep 963095 = 1444643) B1444643
theorem B963115 : Blo 960589 963115 := bstep (se 1 (by rfl) ⟨722336, by rfl⟩ : syracuseStep 963115 = 1444673) B1444673
theorem B963127 : Blo 960589 963127 := bstep (se 1 (by rfl) ⟨722345, by rfl⟩ : syracuseStep 963127 = 1444691) B1444691
theorem B963147 : Blo 960589 963147 := bstep (se 1 (by rfl) ⟨722360, by rfl⟩ : syracuseStep 963147 = 1444721) B1444721
theorem B963159 : Blo 960589 963159 := bstep (se 1 (by rfl) ⟨722369, by rfl⟩ : syracuseStep 963159 = 1444739) B1444739
theorem B5485157 : Blo 960589 5485157 := bstep (se 4 (by rfl) ⟨514233, by rfl⟩ : syracuseStep 5485157 = 1028467) B1028467
theorem B963179 : Blo 960589 963179 := bstep (se 1 (by rfl) ⟨722384, by rfl⟩ : syracuseStep 963179 = 1444769) B1444769
theorem B963191 : Blo 960589 963191 := bstep (se 1 (by rfl) ⟨722393, by rfl⟩ : syracuseStep 963191 = 1444787) B1444787
theorem B963211 : Blo 960589 963211 := bstep (se 1 (by rfl) ⟨722408, by rfl⟩ : syracuseStep 963211 = 1444817) B1444817
theorem B963223 : Blo 960589 963223 := bstep (se 1 (by rfl) ⟨722417, by rfl⟩ : syracuseStep 963223 = 1444835) B1444835
theorem B963243 : Blo 960589 963243 := bstep (se 1 (by rfl) ⟨722432, by rfl⟩ : syracuseStep 963243 = 1444865) B1444865
theorem B963255 : Blo 960589 963255 := bstep (se 1 (by rfl) ⟨722441, by rfl⟩ : syracuseStep 963255 = 1444883) B1444883
theorem B963275 : Blo 960589 963275 := bstep (se 1 (by rfl) ⟨722456, by rfl⟩ : syracuseStep 963275 = 1444913) B1444913
theorem B963287 : Blo 960589 963287 := bstep (se 1 (by rfl) ⟨722465, by rfl⟩ : syracuseStep 963287 = 1444931) B1444931
theorem B3289817 : Blo 960589 3289817 := bstep (se 2 (by rfl) ⟨1233681, by rfl⟩ : syracuseStep 3289817 = 2467363) B2467363
theorem B963307 : Blo 960589 963307 := bstep (se 1 (by rfl) ⟨722480, by rfl⟩ : syracuseStep 963307 = 1444961) B1444961
theorem B963319 : Blo 960589 963319 := bstep (se 1 (by rfl) ⟨722489, by rfl⟩ : syracuseStep 963319 = 1444979) B1444979
theorem B963339 : Blo 960589 963339 := bstep (se 1 (by rfl) ⟨722504, by rfl⟩ : syracuseStep 963339 = 1445009) B1445009
theorem B963351 : Blo 960589 963351 := bstep (se 1 (by rfl) ⟨722513, by rfl⟩ : syracuseStep 963351 = 1445027) B1445027
theorem B963371 : Blo 960589 963371 := bstep (se 1 (by rfl) ⟨722528, by rfl⟩ : syracuseStep 963371 = 1445057) B1445057
theorem B963383 : Blo 960589 963383 := bstep (se 1 (by rfl) ⟨722537, by rfl⟩ : syracuseStep 963383 = 1445075) B1445075
theorem B963403 : Blo 960589 963403 := bstep (se 1 (by rfl) ⟨722552, by rfl⟩ : syracuseStep 963403 = 1445105) B1445105
theorem B963415 : Blo 960589 963415 := bstep (se 1 (by rfl) ⟨722561, by rfl⟩ : syracuseStep 963415 = 1445123) B1445123
theorem B963435 : Blo 960589 963435 := bstep (se 1 (by rfl) ⟨722576, by rfl⟩ : syracuseStep 963435 = 1445153) B1445153
theorem B963447 : Blo 960589 963447 := bstep (se 1 (by rfl) ⟨722585, by rfl⟩ : syracuseStep 963447 = 1445171) B1445171
theorem B963467 : Blo 960589 963467 := bstep (se 1 (by rfl) ⟨722600, by rfl⟩ : syracuseStep 963467 = 1445201) B1445201
theorem B2438039 : Blo 960589 2438039 := bstep (se 1 (by rfl) ⟨1828529, by rfl⟩ : syracuseStep 2438039 = 3657059) B3657059
theorem B963479 : Blo 960589 963479 := bstep (se 1 (by rfl) ⟨722609, by rfl⟩ : syracuseStep 963479 = 1445219) B1445219
theorem B963499 : Blo 960589 963499 := bstep (se 1 (by rfl) ⟨722624, by rfl⟩ : syracuseStep 963499 = 1445249) B1445249
theorem B1029035 : Blo 960589 1029035 := bstep (se 1 (by rfl) ⟨771776, by rfl⟩ : syracuseStep 1029035 = 1543553) B1543553
theorem B963511 : Blo 960589 963511 := bstep (se 1 (by rfl) ⟨722633, by rfl⟩ : syracuseStep 963511 = 1445267) B1445267
theorem B963531 : Blo 960589 963531 := bstep (se 1 (by rfl) ⟨722648, by rfl⟩ : syracuseStep 963531 = 1445297) B1445297
theorem B963543 : Blo 960589 963543 := bstep (se 1 (by rfl) ⟨722657, by rfl⟩ : syracuseStep 963543 = 1445315) B1445315
theorem B963563 : Blo 960589 963563 := bstep (se 1 (by rfl) ⟨722672, by rfl⟩ : syracuseStep 963563 = 1445345) B1445345
theorem B963575 : Blo 960589 963575 := bstep (se 1 (by rfl) ⟨722681, by rfl⟩ : syracuseStep 963575 = 1445363) B1445363
theorem B963595 : Blo 960589 963595 := bstep (se 1 (by rfl) ⟨722696, by rfl⟩ : syracuseStep 963595 = 1445393) B1445393
theorem B4174865 : Blo 960589 4174865 := bstep (se 2 (by rfl) ⟨1565574, by rfl⟩ : syracuseStep 4174865 = 3131149) B3131149
theorem B963607 : Blo 960589 963607 := bstep (se 1 (by rfl) ⟨722705, by rfl⟩ : syracuseStep 963607 = 1445411) B1445411
theorem B963627 : Blo 960589 963627 := bstep (se 1 (by rfl) ⟨722720, by rfl⟩ : syracuseStep 963627 = 1445441) B1445441
theorem B3519533 : Blo 960589 3519533 := bstep (se 3 (by rfl) ⟨659912, by rfl⟩ : syracuseStep 3519533 = 1319825) B1319825
theorem B963639 : Blo 960589 963639 := bstep (se 1 (by rfl) ⟨722729, by rfl⟩ : syracuseStep 963639 = 1445459) B1445459
theorem B963659 : Blo 960589 963659 := bstep (se 1 (by rfl) ⟨722744, by rfl⟩ : syracuseStep 963659 = 1445489) B1445489
theorem B1586251 : Blo 960589 1586251 := bstep (se 1 (by rfl) ⟨1189688, by rfl⟩ : syracuseStep 1586251 = 2379377) B2379377
theorem B963671 : Blo 960589 963671 := bstep (se 1 (by rfl) ⟨722753, by rfl⟩ : syracuseStep 963671 = 1445507) B1445507
theorem B963691 : Blo 960589 963691 := bstep (se 1 (by rfl) ⟨722768, by rfl⟩ : syracuseStep 963691 = 1445537) B1445537
theorem B963703 : Blo 960589 963703 := bstep (se 1 (by rfl) ⟨722777, by rfl⟩ : syracuseStep 963703 = 1445555) B1445555
theorem B963723 : Blo 960589 963723 := bstep (se 1 (by rfl) ⟨722792, by rfl⟩ : syracuseStep 963723 = 1445585) B1445585
theorem B963735 : Blo 960589 963735 := bstep (se 1 (by rfl) ⟨722801, by rfl⟩ : syracuseStep 963735 = 1445603) B1445603
theorem B963755 : Blo 960589 963755 := bstep (se 1 (by rfl) ⟨722816, by rfl⟩ : syracuseStep 963755 = 1445633) B1445633
theorem B963767 : Blo 960589 963767 := bstep (se 1 (by rfl) ⟨722825, by rfl⟩ : syracuseStep 963767 = 1445651) B1445651
theorem B963787 : Blo 960589 963787 := bstep (se 1 (by rfl) ⟨722840, by rfl⟩ : syracuseStep 963787 = 1445681) B1445681
theorem B963799 : Blo 960589 963799 := bstep (se 1 (by rfl) ⟨722849, by rfl⟩ : syracuseStep 963799 = 1445699) B1445699
theorem B963819 : Blo 960589 963819 := bstep (se 1 (by rfl) ⟨722864, by rfl⟩ : syracuseStep 963819 = 1445729) B1445729
theorem B963831 : Blo 960589 963831 := bstep (se 1 (by rfl) ⟨722873, by rfl⟩ : syracuseStep 963831 = 1445747) B1445747
theorem B963851 : Blo 960589 963851 := bstep (se 1 (by rfl) ⟨722888, by rfl⟩ : syracuseStep 963851 = 1445777) B1445777
theorem B963863 : Blo 960589 963863 := bstep (se 1 (by rfl) ⟨722897, by rfl⟩ : syracuseStep 963863 = 1445795) B1445795
theorem B963883 : Blo 960589 963883 := bstep (se 1 (by rfl) ⟨722912, by rfl⟩ : syracuseStep 963883 = 1445825) B1445825
theorem B963895 : Blo 960589 963895 := bstep (se 1 (by rfl) ⟨722921, by rfl⟩ : syracuseStep 963895 = 1445843) B1445843
theorem B963915 : Blo 960589 963915 := bstep (se 1 (by rfl) ⟨722936, by rfl⟩ : syracuseStep 963915 = 1445873) B1445873
theorem B963927 : Blo 960589 963927 := bstep (se 1 (by rfl) ⟨722945, by rfl⟩ : syracuseStep 963927 = 1445891) B1445891
theorem B963947 : Blo 960589 963947 := bstep (se 1 (by rfl) ⟨722960, by rfl⟩ : syracuseStep 963947 = 1445921) B1445921
theorem B963959 : Blo 960589 963959 := bstep (se 1 (by rfl) ⟨722969, by rfl⟩ : syracuseStep 963959 = 1445939) B1445939
theorem B6174083 : Blo 960589 6174083 := bstep (se 1 (by rfl) ⟨4630562, by rfl⟩ : syracuseStep 6174083 = 9261125) B9261125
theorem B963979 : Blo 960589 963979 := bstep (se 1 (by rfl) ⟨722984, by rfl⟩ : syracuseStep 963979 = 1445969) B1445969
theorem B70268309 : Blo 960589 70268309 := bstep (se 6 (by rfl) ⟨1646913, by rfl⟩ : syracuseStep 70268309 = 3293827) B3293827
theorem B963991 : Blo 960589 963991 := bstep (se 1 (by rfl) ⟨722993, by rfl⟩ : syracuseStep 963991 = 1445987) B1445987
theorem B964011 : Blo 960589 964011 := bstep (se 1 (by rfl) ⟨723008, by rfl⟩ : syracuseStep 964011 = 1446017) B1446017
theorem B964023 : Blo 960589 964023 := bstep (se 1 (by rfl) ⟨723017, by rfl⟩ : syracuseStep 964023 = 1446035) B1446035
theorem B964043 : Blo 960589 964043 := bstep (se 1 (by rfl) ⟨723032, by rfl⟩ : syracuseStep 964043 = 1446065) B1446065
theorem B964055 : Blo 960589 964055 := bstep (se 1 (by rfl) ⟨723041, by rfl⟩ : syracuseStep 964055 = 1446083) B1446083
theorem B964075 : Blo 960589 964075 := bstep (se 1 (by rfl) ⟨723056, by rfl⟩ : syracuseStep 964075 = 1446113) B1446113
theorem B964087 : Blo 960589 964087 := bstep (se 1 (by rfl) ⟨723065, by rfl⟩ : syracuseStep 964087 = 1446131) B1446131
theorem B964107 : Blo 960589 964107 := bstep (se 1 (by rfl) ⟨723080, by rfl⟩ : syracuseStep 964107 = 1446161) B1446161
theorem B964119 : Blo 960589 964119 := bstep (se 1 (by rfl) ⟨723089, by rfl⟩ : syracuseStep 964119 = 1446179) B1446179
theorem B964139 : Blo 960589 964139 := bstep (se 1 (by rfl) ⟨723104, by rfl⟩ : syracuseStep 964139 = 1446209) B1446209
theorem B2438707 : Blo 960589 2438707 := bstep (se 1 (by rfl) ⟨1829030, by rfl⟩ : syracuseStep 2438707 = 3658061) B3658061
theorem B964151 : Blo 960589 964151 := bstep (se 1 (by rfl) ⟨723113, by rfl⟩ : syracuseStep 964151 = 1446227) B1446227
theorem B4863563 : Blo 960589 4863563 := bstep (se 1 (by rfl) ⟨3647672, by rfl⟩ : syracuseStep 4863563 = 7295345) B7295345
theorem B964171 : Blo 960589 964171 := bstep (se 1 (by rfl) ⟨723128, by rfl⟩ : syracuseStep 964171 = 1446257) B1446257
theorem B964183 : Blo 960589 964183 := bstep (se 1 (by rfl) ⟨723137, by rfl⟩ : syracuseStep 964183 = 1446275) B1446275
theorem B964203 : Blo 960589 964203 := bstep (se 1 (by rfl) ⟨723152, by rfl⟩ : syracuseStep 964203 = 1446305) B1446305
theorem B964215 : Blo 960589 964215 := bstep (se 1 (by rfl) ⟨723161, by rfl⟩ : syracuseStep 964215 = 1446323) B1446323
theorem B964235 : Blo 960589 964235 := bstep (se 1 (by rfl) ⟨723176, by rfl⟩ : syracuseStep 964235 = 1446353) B1446353
theorem B964247 : Blo 960589 964247 := bstep (se 1 (by rfl) ⟨723185, by rfl⟩ : syracuseStep 964247 = 1446371) B1446371
theorem B964267 : Blo 960589 964267 := bstep (se 1 (by rfl) ⟨723200, by rfl⟩ : syracuseStep 964267 = 1446401) B1446401
theorem B964279 : Blo 960589 964279 := bstep (se 1 (by rfl) ⟨723209, by rfl⟩ : syracuseStep 964279 = 1446419) B1446419
theorem B2438849 : Blo 960589 2438849 := bstep (se 2 (by rfl) ⟨914568, by rfl⟩ : syracuseStep 2438849 = 1829137) B1829137
theorem B964299 : Blo 960589 964299 := bstep (se 1 (by rfl) ⟨723224, by rfl⟩ : syracuseStep 964299 = 1446449) B1446449
theorem B11712205 : Blo 960589 11712205 := bstep (se 3 (by rfl) ⟨2196038, by rfl⟩ : syracuseStep 11712205 = 4392077) B4392077
theorem B964311 : Blo 960589 964311 := bstep (se 1 (by rfl) ⟨723233, by rfl⟩ : syracuseStep 964311 = 1446467) B1446467
theorem B4110041 : Blo 960589 4110041 := bstep (se 2 (by rfl) ⟨1541265, by rfl⟩ : syracuseStep 4110041 = 3082531) B3082531
theorem B964331 : Blo 960589 964331 := bstep (se 1 (by rfl) ⟨723248, by rfl⟩ : syracuseStep 964331 = 1446497) B1446497
theorem B964343 : Blo 960589 964343 := bstep (se 1 (by rfl) ⟨723257, by rfl⟩ : syracuseStep 964343 = 1446515) B1446515
theorem B964363 : Blo 960589 964363 := bstep (se 1 (by rfl) ⟨723272, by rfl⟩ : syracuseStep 964363 = 1446545) B1446545
theorem B964375 : Blo 960589 964375 := bstep (se 1 (by rfl) ⟨723281, by rfl⟩ : syracuseStep 964375 = 1446563) B1446563
theorem B964395 : Blo 960589 964395 := bstep (se 1 (by rfl) ⟨723296, by rfl⟩ : syracuseStep 964395 = 1446593) B1446593
theorem B964407 : Blo 960589 964407 := bstep (se 1 (by rfl) ⟨723305, by rfl⟩ : syracuseStep 964407 = 1446611) B1446611
theorem B964427 : Blo 960589 964427 := bstep (se 1 (by rfl) ⟨723320, by rfl⟩ : syracuseStep 964427 = 1446641) B1446641
theorem B964439 : Blo 960589 964439 := bstep (se 1 (by rfl) ⟨723329, by rfl⟩ : syracuseStep 964439 = 1446659) B1446659
theorem B964459 : Blo 960589 964459 := bstep (se 1 (by rfl) ⟨723344, by rfl⟩ : syracuseStep 964459 = 1446689) B1446689
theorem B964471 : Blo 960589 964471 := bstep (se 1 (by rfl) ⟨723353, by rfl⟩ : syracuseStep 964471 = 1446707) B1446707
theorem B964491 : Blo 960589 964491 := bstep (se 1 (by rfl) ⟨723368, by rfl⟩ : syracuseStep 964491 = 1446737) B1446737
theorem B964503 : Blo 960589 964503 := bstep (se 1 (by rfl) ⟨723377, by rfl⟩ : syracuseStep 964503 = 1446755) B1446755
theorem B964523 : Blo 960589 964523 := bstep (se 1 (by rfl) ⟨723392, by rfl⟩ : syracuseStep 964523 = 1446785) B1446785
theorem B964535 : Blo 960589 964535 := bstep (se 1 (by rfl) ⟨723401, by rfl⟩ : syracuseStep 964535 = 1446803) B1446803
theorem B964555 : Blo 960589 964555 := bstep (se 1 (by rfl) ⟨723416, by rfl⟩ : syracuseStep 964555 = 1446833) B1446833
theorem B964567 : Blo 960589 964567 := bstep (se 1 (by rfl) ⟨723425, by rfl⟩ : syracuseStep 964567 = 1446851) B1446851
theorem B964587 : Blo 960589 964587 := bstep (se 1 (by rfl) ⟨723440, by rfl⟩ : syracuseStep 964587 = 1446881) B1446881
theorem B3291211 : Blo 960589 3291211 := bstep (se 1 (by rfl) ⟨2468408, by rfl⟩ : syracuseStep 3291211 = 4936817) B4936817
theorem B15644933 : Blo 960589 15644933 := bstep (se 4 (by rfl) ⟨1466712, by rfl⟩ : syracuseStep 15644933 = 2933425) B2933425
theorem B1948225 : Blo 960589 1948225 := bstep (se 2 (by rfl) ⟨730584, by rfl⟩ : syracuseStep 1948225 = 1461169) B1461169
theorem B3652397 : Blo 960589 3652397 := bstep (se 3 (by rfl) ⟨684824, by rfl⟩ : syracuseStep 3652397 = 1369649) B1369649
theorem B1129291 : Blo 960589 1129291 := bstep (se 1 (by rfl) ⟨846968, by rfl⟩ : syracuseStep 1129291 = 1693937) B1693937
theorem B1948531 : Blo 960589 1948531 := bstep (se 1 (by rfl) ⟨1461398, by rfl⟩ : syracuseStep 1948531 = 2922797) B2922797
theorem B2440115 : Blo 960589 2440115 := bstep (se 1 (by rfl) ⟨1830086, by rfl⟩ : syracuseStep 2440115 = 3660173) B3660173
theorem B7519493 : Blo 960589 7519493 := bstep (se 4 (by rfl) ⟨704952, by rfl⟩ : syracuseStep 7519493 = 1409905) B1409905
theorem B4865345 : Blo 960589 4865345 := bstep (se 2 (by rfl) ⟨1824504, by rfl⟩ : syracuseStep 4865345 = 3649009) B3649009
theorem B4111681 : Blo 960589 4111681 := bstep (se 2 (by rfl) ⟨1541880, by rfl⟩ : syracuseStep 4111681 = 3083761) B3083761
theorem B1621451 : Blo 960589 1621451 := bstep (se 1 (by rfl) ⟨1216088, by rfl⟩ : syracuseStep 1621451 = 2432177) B2432177
theorem B2440651 : Blo 960589 2440651 := bstep (se 1 (by rfl) ⟨1830488, by rfl⟩ : syracuseStep 2440651 = 3660977) B3660977
theorem B3653171 : Blo 960589 3653171 := bstep (se 1 (by rfl) ⟨2739878, by rfl⟩ : syracuseStep 3653171 = 5479757) B5479757
theorem B1621579 : Blo 960589 1621579 := bstep (se 1 (by rfl) ⟨1216184, by rfl⟩ : syracuseStep 1621579 = 2432369) B2432369
theorem B2440793 : Blo 960589 2440793 := bstep (se 2 (by rfl) ⟨915297, by rfl⟩ : syracuseStep 2440793 = 1830595) B1830595
theorem B1621721 : Blo 960589 1621721 := bstep (se 2 (by rfl) ⟨608145, by rfl⟩ : syracuseStep 1621721 = 1216291) B1216291
theorem B1621849 : Blo 960589 1621849 := bstep (se 2 (by rfl) ⟨608193, by rfl⟩ : syracuseStep 1621849 = 1216387) B1216387
theorem B4112279 : Blo 960589 4112279 := bstep (se 1 (by rfl) ⟨3084209, by rfl⟩ : syracuseStep 4112279 = 6168419) B6168419
theorem B1622423 : Blo 960589 1622423 := bstep (se 1 (by rfl) ⟨1216817, by rfl⟩ : syracuseStep 1622423 = 2433635) B2433635
theorem B1622551 : Blo 960589 1622551 := bstep (se 1 (by rfl) ⟨1216913, by rfl⟩ : syracuseStep 1622551 = 2433827) B2433827
theorem B1851979 : Blo 960589 1851979 := bstep (se 1 (by rfl) ⟨1388984, by rfl⟩ : syracuseStep 1851979 = 2777969) B2777969
theorem B12337757 : Blo 960589 12337757 := bstep (se 3 (by rfl) ⟨2313329, by rfl⟩ : syracuseStep 12337757 = 4626659) B4626659
theorem B79086293 : Blo 960589 79086293 := bstep (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) B1853585
theorem B40682225 : Blo 960589 40682225 := bstep (se 2 (by rfl) ⟨15255834, by rfl⟩ : syracuseStep 40682225 = 30511669) B30511669
theorem B2736985 : Blo 960589 2736985 := bstep (se 2 (by rfl) ⟨1026369, by rfl⟩ : syracuseStep 2736985 = 2052739) B2052739
theorem B3654659 : Blo 960589 3654659 := bstep (se 1 (by rfl) ⟨2740994, by rfl⟩ : syracuseStep 3654659 = 5481989) B5481989
theorem B1623179 : Blo 960589 1623179 := bstep (se 1 (by rfl) ⟨1217384, by rfl⟩ : syracuseStep 1623179 = 2434769) B2434769
theorem B4113611 : Blo 960589 4113611 := bstep (se 1 (by rfl) ⟨3085208, by rfl⟩ : syracuseStep 4113611 = 6170417) B6170417
theorem B4867289 : Blo 960589 4867289 := bstep (se 2 (by rfl) ⟨1825233, by rfl⟩ : syracuseStep 4867289 = 3650467) B3650467
theorem B1623307 : Blo 960589 1623307 := bstep (se 1 (by rfl) ⟨1217480, by rfl⟩ : syracuseStep 1623307 = 2434961) B2434961
theorem B1623449 : Blo 960589 1623449 := bstep (se 2 (by rfl) ⟨608793, by rfl⟩ : syracuseStep 1623449 = 1217587) B1217587
theorem B2737601 : Blo 960589 2737601 := bstep (se 2 (by rfl) ⟨1026600, by rfl⟩ : syracuseStep 2737601 = 2053201) B2053201
theorem B3655115 : Blo 960589 3655115 := bstep (se 1 (by rfl) ⟨2741336, by rfl⟩ : syracuseStep 3655115 = 5482673) B5482673
theorem B1623577 : Blo 960589 1623577 := bstep (se 2 (by rfl) ⟨608841, by rfl⟩ : syracuseStep 1623577 = 1217683) B1217683
theorem B3655313 : Blo 960589 3655313 := bstep (se 2 (by rfl) ⟨1370742, by rfl⟩ : syracuseStep 3655313 = 2741485) B2741485
theorem B1624151 : Blo 960589 1624151 := bstep (se 1 (by rfl) ⟨1218113, by rfl⟩ : syracuseStep 1624151 = 2436227) B2436227
theorem B1853579 : Blo 960589 1853579 := bstep (se 1 (by rfl) ⟨1390184, by rfl⟩ : syracuseStep 1853579 = 2780369) B2780369
theorem B1624279 : Blo 960589 1624279 := bstep (se 1 (by rfl) ⟨1218209, by rfl⟩ : syracuseStep 1624279 = 2436419) B2436419
theorem B7817477 : Blo 960589 7817477 := bstep (se 4 (by rfl) ⟨732888, by rfl⟩ : syracuseStep 7817477 = 1465777) B1465777
theorem B5490989 : Blo 960589 5490989 := bstep (se 3 (by rfl) ⟨1029560, by rfl⟩ : syracuseStep 5490989 = 2059121) B2059121
theorem B4114739 : Blo 960589 4114739 := bstep (se 1 (by rfl) ⟨3086054, by rfl⟩ : syracuseStep 4114739 = 6172109) B6172109
theorem B2312599 : Blo 960589 2312599 := bstep (se 1 (by rfl) ⟨1734449, by rfl⟩ : syracuseStep 2312599 = 3468899) B3468899
theorem B3656087 : Blo 960589 3656087 := bstep (se 1 (by rfl) ⟨2742065, by rfl⟩ : syracuseStep 3656087 = 5484131) B5484131
theorem B3656285 : Blo 960589 3656285 := bstep (se 3 (by rfl) ⟨685553, by rfl⟩ : syracuseStep 3656285 = 1371107) B1371107
theorem B4868909 : Blo 960589 4868909 := bstep (se 3 (by rfl) ⟨912920, by rfl⟩ : syracuseStep 4868909 = 1825841) B1825841
theorem B1624907 : Blo 960589 1624907 := bstep (se 1 (by rfl) ⟨1218680, by rfl⟩ : syracuseStep 1624907 = 2437361) B2437361
theorem B1625035 : Blo 960589 1625035 := bstep (se 1 (by rfl) ⟨1218776, by rfl⟩ : syracuseStep 1625035 = 2437553) B2437553
theorem B1625177 : Blo 960589 1625177 := bstep (se 2 (by rfl) ⟨609441, by rfl⟩ : syracuseStep 1625177 = 1218883) B1218883
theorem B9260237 : Blo 960589 9260237 := bstep (se 3 (by rfl) ⟨1736294, by rfl⟩ : syracuseStep 9260237 = 3472589) B3472589
theorem B1625305 : Blo 960589 1625305 := bstep (se 2 (by rfl) ⟨609489, by rfl⟩ : syracuseStep 1625305 = 1218979) B1218979
theorem B2739673 : Blo 960589 2739673 := bstep (se 2 (by rfl) ⟨1027377, by rfl⟩ : syracuseStep 2739673 = 2054755) B2054755
theorem B13160029 : Blo 960589 13160029 := bstep (se 3 (by rfl) ⟨2467505, by rfl⟩ : syracuseStep 13160029 = 4935011) B4935011
theorem B1560217 : Blo 960589 1560217 := bstep (se 2 (by rfl) ⟨585081, by rfl⟩ : syracuseStep 1560217 = 1170163) B1170163
theorem B2051851 : Blo 960589 2051851 := bstep (se 1 (by rfl) ⟨1538888, by rfl⟩ : syracuseStep 2051851 = 3077777) B3077777
theorem B1625879 : Blo 960589 1625879 := bstep (se 1 (by rfl) ⟨1219409, by rfl⟩ : syracuseStep 1625879 = 2438819) B2438819
theorem B2740061 : Blo 960589 2740061 := bstep (se 3 (by rfl) ⟨513761, by rfl⟩ : syracuseStep 2740061 = 1027523) B1027523
theorem B1626007 : Blo 960589 1626007 := bstep (se 1 (by rfl) ⟨1219505, by rfl⟩ : syracuseStep 1626007 = 2439011) B2439011
theorem B4116653 : Blo 960589 4116653 := bstep (se 3 (by rfl) ⟨771872, by rfl⟩ : syracuseStep 4116653 = 1543745) B1543745
theorem B1855795 : Blo 960589 1855795 := bstep (se 1 (by rfl) ⟨1391846, by rfl⟩ : syracuseStep 1855795 = 2783693) B2783693
theorem B3658243 : Blo 960589 3658243 := bstep (se 1 (by rfl) ⟨2743682, by rfl⟩ : syracuseStep 3658243 = 5487365) B5487365
theorem B1626635 : Blo 960589 1626635 := bstep (se 1 (by rfl) ⟨1219976, by rfl⟩ : syracuseStep 1626635 = 2439953) B2439953
theorem B1856065 : Blo 960589 1856065 := bstep (se 2 (by rfl) ⟨696024, by rfl⟩ : syracuseStep 1856065 = 1392049) B1392049
theorem B2052697 : Blo 960589 2052697 := bstep (se 2 (by rfl) ⟨769761, by rfl⟩ : syracuseStep 2052697 = 1539523) B1539523
theorem B5493379 : Blo 960589 5493379 := bstep (se 1 (by rfl) ⟨4120034, by rfl⟩ : syracuseStep 5493379 = 8240069) B8240069
theorem B1626763 : Blo 960589 1626763 := bstep (se 1 (by rfl) ⟨1220072, by rfl⟩ : syracuseStep 1626763 = 2440145) B2440145
theorem B1757953 : Blo 960589 1757953 := bstep (se 2 (by rfl) ⟨659232, by rfl⟩ : syracuseStep 1757953 = 1318465) B1318465
theorem B1626905 : Blo 960589 1626905 := bstep (se 2 (by rfl) ⟨610089, by rfl⟩ : syracuseStep 1626905 = 1220179) B1220179
theorem B3658547 : Blo 960589 3658547 := bstep (se 1 (by rfl) ⟨2743910, by rfl⟩ : syracuseStep 3658547 = 5487821) B5487821
theorem B4117337 : Blo 960589 4117337 := bstep (se 2 (by rfl) ⟨1544001, by rfl⟩ : syracuseStep 4117337 = 3088003) B3088003
theorem B1561483 : Blo 960589 1561483 := bstep (se 1 (by rfl) ⟨1171112, by rfl⟩ : syracuseStep 1561483 = 2342225) B2342225
theorem B1627033 : Blo 960589 1627033 := bstep (se 2 (by rfl) ⟨610137, by rfl⟩ : syracuseStep 1627033 = 1220275) B1220275
theorem B1823897 : Blo 960589 1823897 := bstep (se 2 (by rfl) ⟨683961, by rfl⟩ : syracuseStep 1823897 = 1367923) B1367923
theorem B33314093 : Blo 960589 33314093 := bstep (se 3 (by rfl) ⟨6246392, by rfl⟩ : syracuseStep 33314093 = 12492785) B12492785
theorem B8213825 : Blo 960589 8213825 := bstep (se 2 (by rfl) ⟨3080184, by rfl⟩ : syracuseStep 8213825 = 6160369) B6160369
theorem B3659201 : Blo 960589 3659201 := bstep (se 2 (by rfl) ⟨1372200, by rfl⟩ : syracuseStep 3659201 = 2744401) B2744401
theorem B1627607 : Blo 960589 1627607 := bstep (se 1 (by rfl) ⟨1220705, by rfl⟩ : syracuseStep 1627607 = 2441411) B2441411
theorem B3462659 : Blo 960589 3462659 := bstep (se 1 (by rfl) ⟨2596994, by rfl⟩ : syracuseStep 3462659 = 5193989) B5193989
theorem B1627735 : Blo 960589 1627735 := bstep (se 1 (by rfl) ⟨1220801, by rfl⟩ : syracuseStep 1627735 = 2441603) B2441603
theorem B1824535 : Blo 960589 1824535 := bstep (se 1 (by rfl) ⟨1368401, by rfl⟩ : syracuseStep 1824535 = 2736803) B2736803
theorem B7296803 : Blo 960589 7296803 := bstep (se 1 (by rfl) ⟨5472602, by rfl⟩ : syracuseStep 7296803 = 10945205) B10945205
theorem B2054003 : Blo 960589 2054003 := bstep (se 1 (by rfl) ⟨1540502, by rfl⟩ : syracuseStep 2054003 = 3081005) B3081005
theorem B5199889 : Blo 960589 5199889 := bstep (se 2 (by rfl) ⟨1949958, by rfl⟩ : syracuseStep 5199889 = 3899917) B3899917
theorem B29677589 : Blo 960589 29677589 := bstep (se 6 (by rfl) ⟨695568, by rfl⟩ : syracuseStep 29677589 = 1391137) B1391137
theorem B10967075 : Blo 960589 10967075 := bstep (se 1 (by rfl) ⟨8225306, by rfl⟩ : syracuseStep 10967075 = 16450613) B16450613
theorem B6576515 : Blo 960589 6576515 := bstep (se 1 (by rfl) ⟨4932386, by rfl⟩ : syracuseStep 6576515 = 9864773) B9864773
theorem B9361955 : Blo 960589 9361955 := bstep (se 1 (by rfl) ⟨7021466, by rfl⟩ : syracuseStep 9361955 = 14042933) B14042933
theorem B1825355 : Blo 960589 1825355 := bstep (se 1 (by rfl) ⟨1369016, by rfl⟩ : syracuseStep 1825355 = 2738033) B2738033
theorem B4872797 : Blo 960589 4872797 := bstep (se 3 (by rfl) ⟨913649, by rfl⟩ : syracuseStep 4872797 = 1827299) B1827299
theorem B1825409 : Blo 960589 1825409 := bstep (se 2 (by rfl) ⟨684528, by rfl⟩ : syracuseStep 1825409 = 1369057) B1369057
theorem B3660461 : Blo 960589 3660461 := bstep (se 3 (by rfl) ⟨686336, by rfl⟩ : syracuseStep 3660461 = 1372673) B1372673
theorem B2742977 : Blo 960589 2742977 := bstep (se 2 (by rfl) ⟨1028616, by rfl⟩ : syracuseStep 2742977 = 2057233) B2057233
theorem B3660491 : Blo 960589 3660491 := bstep (se 1 (by rfl) ⟨2745368, by rfl⟩ : syracuseStep 3660491 = 5490737) B5490737
theorem B1465049 : Blo 960589 1465049 := bstep (se 2 (by rfl) ⟨549393, by rfl⟩ : syracuseStep 1465049 = 1098787) B1098787
theorem B2743091 : Blo 960589 2743091 := bstep (se 1 (by rfl) ⟨2057318, by rfl⟩ : syracuseStep 2743091 = 4114637) B4114637
theorem B1465291 : Blo 960589 1465291 := bstep (se 1 (by rfl) ⟨1098968, by rfl⟩ : syracuseStep 1465291 = 2197937) B2197937
theorem B12311513 : Blo 960589 12311513 := bstep (se 2 (by rfl) ⟨4616817, by rfl⟩ : syracuseStep 12311513 = 9233635) B9233635
theorem B974071 : Blo 960589 974071 := bstep (se 1 (by rfl) ⟨730553, by rfl⟩ : syracuseStep 974071 = 1461107) B1461107
theorem B2678039 : Blo 960589 2678039 := bstep (se 1 (by rfl) ⟨2008529, by rfl⟩ : syracuseStep 2678039 = 4017059) B4017059
theorem B3661145 : Blo 960589 3661145 := bstep (se 2 (by rfl) ⟨1372929, by rfl⟩ : syracuseStep 3661145 = 2745859) B2745859
theorem B4382045 : Blo 960589 4382045 := bstep (se 3 (by rfl) ⟨821633, by rfl⟩ : syracuseStep 4382045 = 1643267) B1643267
theorem B27745649 : Blo 960589 27745649 := bstep (se 2 (by rfl) ⟨10404618, by rfl⟩ : syracuseStep 27745649 = 20809237) B20809237
theorem B2055575 : Blo 960589 2055575 := bstep (se 1 (by rfl) ⟨1541681, by rfl⟩ : syracuseStep 2055575 = 3083363) B3083363
theorem B1826327 : Blo 960589 1826327 := bstep (se 1 (by rfl) ⟨1369745, by rfl⟩ : syracuseStep 1826327 = 2739491) B2739491
theorem B15228491 : Blo 960589 15228491 := bstep (se 1 (by rfl) ⟨11421368, by rfl⟩ : syracuseStep 15228491 = 22842737) B22842737
theorem B7790231 : Blo 960589 7790231 := bstep (se 1 (by rfl) ⟨5842673, by rfl⟩ : syracuseStep 7790231 = 11685347) B11685347
theorem B3661463 : Blo 960589 3661463 := bstep (se 1 (by rfl) ⟨2746097, by rfl⟩ : syracuseStep 3661463 = 5492195) B5492195
theorem B2055883 : Blo 960589 2055883 := bstep (se 1 (by rfl) ⟨1541912, by rfl⟩ : syracuseStep 2055883 = 3083825) B3083825
theorem B66576077 : Blo 960589 66576077 := bstep (se 3 (by rfl) ⟨12483014, by rfl⟩ : syracuseStep 66576077 = 24966029) B24966029
theorem B4939613 : Blo 960589 4939613 := bstep (se 3 (by rfl) ⟨926177, by rfl⟩ : syracuseStep 4939613 = 1852355) B1852355
theorem B15032243 : Blo 960589 15032243 := bstep (se 1 (by rfl) ⟨11274182, by rfl⟩ : syracuseStep 15032243 = 22548365) B22548365
theorem B1826867 : Blo 960589 1826867 := bstep (se 1 (by rfl) ⟨1370150, by rfl⟩ : syracuseStep 1826867 = 2740301) B2740301
theorem B1237079 : Blo 960589 1237079 := bstep (se 1 (by rfl) ⟨927809, by rfl⟩ : syracuseStep 1237079 = 1855619) B1855619
theorem B3662131 : Blo 960589 3662131 := bstep (se 1 (by rfl) ⟨2746598, by rfl⟩ : syracuseStep 3662131 = 5493197) B5493197
theorem B975223 : Blo 960589 975223 := bstep (se 1 (by rfl) ⟨731417, by rfl⟩ : syracuseStep 975223 = 1462835) B1462835
theorem B1827353 : Blo 960589 1827353 := bstep (se 2 (by rfl) ⟨685257, by rfl⟩ : syracuseStep 1827353 = 1370515) B1370515
theorem B3465773 : Blo 960589 3465773 := bstep (se 3 (by rfl) ⟨649832, by rfl⟩ : syracuseStep 3465773 = 1299665) B1299665
theorem B4874903 : Blo 960589 4874903 := bstep (se 1 (by rfl) ⟨3656177, by rfl⟩ : syracuseStep 4874903 = 7312355) B7312355
theorem B1368857 : Blo 960589 1368857 := bstep (se 2 (by rfl) ⟨513321, by rfl⟩ : syracuseStep 1368857 = 1026643) B1026643
theorem B2057113 : Blo 960589 2057113 := bstep (se 2 (by rfl) ⟨771417, by rfl⟩ : syracuseStep 2057113 = 1542835) B1542835
theorem B2253889 : Blo 960589 2253889 := bstep (se 2 (by rfl) ⟨845208, by rfl⟩ : syracuseStep 2253889 = 1690417) B1690417
theorem B1369495 : Blo 960589 1369495 := bstep (se 1 (by rfl) ⟨1027121, by rfl⟩ : syracuseStep 1369495 = 2054243) B2054243
theorem B976471 : Blo 960589 976471 := bstep (se 1 (by rfl) ⟨732353, by rfl⟩ : syracuseStep 976471 = 1464707) B1464707
theorem B2746007 : Blo 960589 2746007 := bstep (se 1 (by rfl) ⟨2059505, by rfl⟩ : syracuseStep 2746007 = 4119011) B4119011
theorem B3467053 : Blo 960589 3467053 := bstep (se 3 (by rfl) ⟨650072, by rfl⟩ : syracuseStep 3467053 = 1300145) B1300145
theorem B1828811 : Blo 960589 1828811 := bstep (se 1 (by rfl) ⟨1371608, by rfl⟩ : syracuseStep 1828811 = 2743217) B2743217
theorem B1370201 : Blo 960589 1370201 := bstep (se 2 (by rfl) ⟨513825, by rfl⟩ : syracuseStep 1370201 = 1027651) B1027651
theorem B1828993 : Blo 960589 1828993 := bstep (se 2 (by rfl) ⟨685872, by rfl⟩ : syracuseStep 1828993 = 1371745) B1371745
theorem B1370315 : Blo 960589 1370315 := bstep (se 1 (by rfl) ⟨1027736, by rfl⟩ : syracuseStep 1370315 = 2055473) B2055473
theorem B1829441 : Blo 960589 1829441 := bstep (se 2 (by rfl) ⟨686040, by rfl⟩ : syracuseStep 1829441 = 1372081) B1372081
theorem B1370839 : Blo 960589 1370839 := bstep (se 1 (by rfl) ⟨1028129, by rfl⟩ : syracuseStep 1370839 = 2056259) B2056259
theorem B3468035 : Blo 960589 3468035 := bstep (se 1 (by rfl) ⟨2601026, by rfl⟩ : syracuseStep 3468035 = 5202053) B5202053
theorem B1043275 : Blo 960589 1043275 := bstep (se 1 (by rfl) ⟨782456, by rfl⟩ : syracuseStep 1043275 = 1564913) B1564913
theorem B1829783 : Blo 960589 1829783 := bstep (se 1 (by rfl) ⟨1372337, by rfl⟩ : syracuseStep 1829783 = 2744675) B2744675
theorem B7302149 : Blo 960589 7302149 := bstep (se 4 (by rfl) ⟨684576, by rfl⟩ : syracuseStep 7302149 = 1369153) B1369153
theorem B3697937 : Blo 960589 3697937 := bstep (se 2 (by rfl) ⟨1386726, by rfl⟩ : syracuseStep 3697937 = 2773453) B2773453
theorem B1371659 : Blo 960589 1371659 := bstep (se 1 (by rfl) ⟨1028744, by rfl⟩ : syracuseStep 1371659 = 2057489) B2057489
theorem B1830451 : Blo 960589 1830451 := bstep (se 1 (by rfl) ⟨1372838, by rfl⟩ : syracuseStep 1830451 = 2745677) B2745677
theorem B2191169 : Blo 960589 2191169 := bstep (se 2 (by rfl) ⟨821688, by rfl⟩ : syracuseStep 2191169 = 1643377) B1643377
theorem B1830899 : Blo 960589 1830899 := bstep (se 1 (by rfl) ⟨1373174, by rfl⟩ : syracuseStep 1830899 = 2746349) B2746349
theorem B1830937 : Blo 960589 1830937 := bstep (se 2 (by rfl) ⟨686601, by rfl⟩ : syracuseStep 1830937 = 1373203) B1373203
theorem B4878467 : Blo 960589 4878467 := bstep (se 1 (by rfl) ⟨3658850, by rfl⟩ : syracuseStep 4878467 = 7317701) B7317701
theorem B3469463 : Blo 960589 3469463 := bstep (se 1 (by rfl) ⟨2602097, by rfl⟩ : syracuseStep 3469463 = 5204195) B5204195
theorem B6942871 : Blo 960589 6942871 := bstep (se 1 (by rfl) ⟨5207153, by rfl⟩ : syracuseStep 6942871 = 10414307) B10414307
theorem B5861555 : Blo 960589 5861555 := bstep (se 1 (by rfl) ⟨4396166, by rfl⟩ : syracuseStep 5861555 = 8792333) B8792333
theorem B1667609 : Blo 960589 1667609 := bstep (se 2 (by rfl) ⟨625353, by rfl⟩ : syracuseStep 1667609 = 1250707) B1250707
theorem B6943333 : Blo 960589 6943333 := bstep (se 4 (by rfl) ⟨650937, by rfl⟩ : syracuseStep 6943333 = 1301875) B1301875
theorem B5206963 : Blo 960589 5206963 := bstep (se 1 (by rfl) ⟨3905222, by rfl⟩ : syracuseStep 5206963 = 7810445) B7810445
theorem B4617395 : Blo 960589 4617395 := bstep (se 1 (by rfl) ⟨3463046, by rfl⟩ : syracuseStep 4617395 = 6926093) B6926093
theorem B2192627 : Blo 960589 2192627 := bstep (se 1 (by rfl) ⟨1644470, by rfl⟩ : syracuseStep 2192627 = 3288941) B3288941
theorem B7304579 : Blo 960589 7304579 := bstep (se 1 (by rfl) ⟨5478434, by rfl⟩ : syracuseStep 7304579 = 10956869) B10956869
theorem B13891277 : Blo 960589 13891277 := bstep (se 3 (by rfl) ⟨2604614, by rfl⟩ : syracuseStep 13891277 = 5209229) B5209229
theorem B3471149 : Blo 960589 3471149 := bstep (se 3 (by rfl) ⟨650840, by rfl⟩ : syracuseStep 3471149 = 1301681) B1301681
theorem B12318641 : Blo 960589 12318641 := bstep (se 2 (by rfl) ⟨4619490, by rfl⟩ : syracuseStep 12318641 = 9238981) B9238981
theorem B2193331 : Blo 960589 2193331 := bstep (se 1 (by rfl) ⟨1644998, by rfl⟩ : syracuseStep 2193331 = 3289997) B3289997
theorem B15628211 : Blo 960589 15628211 := bstep (se 1 (by rfl) ⟨11721158, by rfl⟩ : syracuseStep 15628211 = 23442317) B23442317
theorem B6944717 : Blo 960589 6944717 := bstep (se 3 (by rfl) ⟨1302134, by rfl⟩ : syracuseStep 6944717 = 2604269) B2604269
theorem B3897389 : Blo 960589 3897389 := bstep (se 3 (by rfl) ⟨730760, by rfl⟩ : syracuseStep 3897389 = 1461521) B1461521
theorem B5863499 : Blo 960589 5863499 := bstep (se 1 (by rfl) ⟨4397624, by rfl⟩ : syracuseStep 5863499 = 8795249) B8795249
theorem B3897517 : Blo 960589 3897517 := bstep (se 3 (by rfl) ⟨730784, by rfl⟩ : syracuseStep 3897517 = 1461569) B1461569
theorem B5863697 : Blo 960589 5863697 := bstep (se 2 (by rfl) ⟨2198886, by rfl⟩ : syracuseStep 5863697 = 4397773) B4397773
theorem B2161331 : Blo 960589 2161331 := bstep (se 1 (by rfl) ⟨1620998, by rfl⟩ : syracuseStep 2161331 = 3241997) B3241997
theorem B3242699 : Blo 960589 3242699 := bstep (se 1 (by rfl) ⟨2432024, by rfl⟩ : syracuseStep 3242699 = 4864049) B4864049
theorem B1669835 : Blo 960589 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B19757773 : Blo 960589 19757773 := bstep (se 3 (by rfl) ⟨3704582, by rfl⟩ : syracuseStep 19757773 = 7409165) B7409165
theorem B2161367 : Blo 960589 2161367 := bstep (se 1 (by rfl) ⟨1621025, by rfl⟩ : syracuseStep 2161367 = 3242051) B3242051
theorem B2161547 : Blo 960589 2161547 := bstep (se 1 (by rfl) ⟨1621160, by rfl⟩ : syracuseStep 2161547 = 3242321) B3242321
theorem B2161601 : Blo 960589 2161601 := bstep (se 2 (by rfl) ⟨810600, by rfl⟩ : syracuseStep 2161601 = 1621201) B1621201
theorem B3242969 : Blo 960589 3242969 := bstep (se 2 (by rfl) ⟨1216113, by rfl⟩ : syracuseStep 3242969 = 2432227) B2432227
theorem B13859909 : Blo 960589 13859909 := bstep (se 4 (by rfl) ⟨1299366, by rfl⟩ : syracuseStep 13859909 = 2598733) B2598733
theorem B15629381 : Blo 960589 15629381 := bstep (se 4 (by rfl) ⟨1465254, by rfl⟩ : syracuseStep 15629381 = 2930509) B2930509
theorem B4619339 : Blo 960589 4619339 := bstep (se 1 (by rfl) ⟨3464504, by rfl⟩ : syracuseStep 4619339 = 6929009) B6929009
theorem B2161817 : Blo 960589 2161817 := bstep (se 2 (by rfl) ⟨810681, by rfl⟩ : syracuseStep 2161817 = 1621363) B1621363
theorem B1440971 : Blo 960589 1440971 := bstep (se 1 (by rfl) ⟨1080728, by rfl⟩ : syracuseStep 1440971 = 2161457) B2161457
theorem B1440983 : Blo 960589 1440983 := bstep (se 1 (by rfl) ⟨1080737, by rfl⟩ : syracuseStep 1440983 = 2161475) B2161475
theorem B2161907 : Blo 960589 2161907 := bstep (se 1 (by rfl) ⟨1621430, by rfl⟩ : syracuseStep 2161907 = 3242861) B3242861
theorem B10419461 : Blo 960589 10419461 := bstep (se 4 (by rfl) ⟨976824, by rfl⟩ : syracuseStep 10419461 = 1953649) B1953649
theorem B2161943 : Blo 960589 2161943 := bstep (se 1 (by rfl) ⟨1621457, by rfl⟩ : syracuseStep 2161943 = 3242915) B3242915
theorem B1441049 : Blo 960589 1441049 := bstep (se 2 (by rfl) ⟨540393, by rfl⟩ : syracuseStep 1441049 = 1080787) B1080787
theorem B1080715 : Blo 960589 1080715 := bstep (se 1 (by rfl) ⟨810536, by rfl⟩ : syracuseStep 1080715 = 1621073) B1621073
theorem B1441163 : Blo 960589 1441163 := bstep (se 1 (by rfl) ⟨1080872, by rfl⟩ : syracuseStep 1441163 = 2161745) B2161745
theorem B1441175 : Blo 960589 1441175 := bstep (se 1 (by rfl) ⟨1080881, by rfl⟩ : syracuseStep 1441175 = 2161763) B2161763
theorem B2162123 : Blo 960589 2162123 := bstep (se 1 (by rfl) ⟨1621592, by rfl⟩ : syracuseStep 2162123 = 3243185) B3243185
theorem B1441241 : Blo 960589 1441241 := bstep (se 2 (by rfl) ⟨540465, by rfl⟩ : syracuseStep 1441241 = 1080931) B1080931
theorem B1080823 : Blo 960589 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B2162177 : Blo 960589 2162177 := bstep (se 2 (by rfl) ⟨810816, by rfl⟩ : syracuseStep 2162177 = 1621633) B1621633
theorem B1441355 : Blo 960589 1441355 := bstep (se 1 (by rfl) ⟨1081016, by rfl⟩ : syracuseStep 1441355 = 2162033) B2162033
theorem B1441367 : Blo 960589 1441367 := bstep (se 1 (by rfl) ⟨1081025, by rfl⟩ : syracuseStep 1441367 = 2162051) B2162051
theorem B3243671 : Blo 960589 3243671 := bstep (se 1 (by rfl) ⟨2432753, by rfl⟩ : syracuseStep 3243671 = 4865507) B4865507
theorem B1441433 : Blo 960589 1441433 := bstep (se 2 (by rfl) ⟨540537, by rfl⟩ : syracuseStep 1441433 = 1081075) B1081075
theorem B1081003 : Blo 960589 1081003 := bstep (se 1 (by rfl) ⟨810752, by rfl⟩ : syracuseStep 1081003 = 1621505) B1621505
theorem B2162393 : Blo 960589 2162393 := bstep (se 2 (by rfl) ⟨810897, by rfl⟩ : syracuseStep 2162393 = 1621795) B1621795
theorem B1441547 : Blo 960589 1441547 := bstep (se 1 (by rfl) ⟨1081160, by rfl⟩ : syracuseStep 1441547 = 2162321) B2162321
theorem B4882193 : Blo 960589 4882193 := bstep (se 2 (by rfl) ⟨1830822, by rfl⟩ : syracuseStep 4882193 = 3661645) B3661645
theorem B1081111 : Blo 960589 1081111 := bstep (se 1 (by rfl) ⟨810833, by rfl⟩ : syracuseStep 1081111 = 1621667) B1621667
theorem B1441559 : Blo 960589 1441559 := bstep (se 1 (by rfl) ⟨1081169, by rfl⟩ : syracuseStep 1441559 = 2162339) B2162339
theorem B2162483 : Blo 960589 2162483 := bstep (se 1 (by rfl) ⟨1621862, by rfl⟩ : syracuseStep 2162483 = 3243725) B3243725
theorem B2162519 : Blo 960589 2162519 := bstep (se 1 (by rfl) ⟨1621889, by rfl⟩ : syracuseStep 2162519 = 3243779) B3243779
theorem B1441625 : Blo 960589 1441625 := bstep (se 2 (by rfl) ⟨540609, by rfl⟩ : syracuseStep 1441625 = 1081219) B1081219
theorem B4882355 : Blo 960589 4882355 := bstep (se 1 (by rfl) ⟨3661766, by rfl⟩ : syracuseStep 4882355 = 7323533) B7323533
theorem B1081291 : Blo 960589 1081291 := bstep (se 1 (by rfl) ⟨810968, by rfl⟩ : syracuseStep 1081291 = 1621937) B1621937
theorem B1441739 : Blo 960589 1441739 := bstep (se 1 (by rfl) ⟨1081304, by rfl⟩ : syracuseStep 1441739 = 2162609) B2162609
theorem B1441751 : Blo 960589 1441751 := bstep (se 1 (by rfl) ⟨1081313, by rfl⟩ : syracuseStep 1441751 = 2162627) B2162627
theorem B1540055 : Blo 960589 1540055 := bstep (se 1 (by rfl) ⟨1155041, by rfl⟩ : syracuseStep 1540055 = 2310083) B2310083
theorem B1441799 : Blo 960589 1441799 := bstep (se 1 (by rfl) ⟨1081349, by rfl⟩ : syracuseStep 1441799 = 2162699) B2162699
theorem B1441835 : Blo 960589 1441835 := bstep (se 1 (by rfl) ⟨1081376, by rfl⟩ : syracuseStep 1441835 = 2162753) B2162753
theorem B1441865 : Blo 960589 1441865 := bstep (se 2 (by rfl) ⟨540699, by rfl⟩ : syracuseStep 1441865 = 1081399) B1081399
theorem B2162807 : Blo 960589 2162807 := bstep (se 1 (by rfl) ⟨1622105, by rfl⟩ : syracuseStep 2162807 = 3244211) B3244211
theorem B1441979 : Blo 960589 1441979 := bstep (se 1 (by rfl) ⟨1081484, by rfl⟩ : syracuseStep 1441979 = 2162969) B2162969
theorem B1442039 : Blo 960589 1442039 := bstep (se 1 (by rfl) ⟨1081529, by rfl⟩ : syracuseStep 1442039 = 2163059) B2163059
theorem B1442063 : Blo 960589 1442063 := bstep (se 1 (by rfl) ⟨1081547, by rfl⟩ : syracuseStep 1442063 = 2163095) B2163095
theorem B1081615 : Blo 960589 1081615 := bstep (se 1 (by rfl) ⟨811211, by rfl⟩ : syracuseStep 1081615 = 1622423) B1622423
theorem B2162987 : Blo 960589 2162987 := bstep (se 1 (by rfl) ⟨1622240, by rfl⟩ : syracuseStep 2162987 = 3244481) B3244481
theorem B1442105 : Blo 960589 1442105 := bstep (se 2 (by rfl) ⟨540789, by rfl⟩ : syracuseStep 1442105 = 1081579) B1081579
theorem B1442183 : Blo 960589 1442183 := bstep (se 1 (by rfl) ⟨1081637, by rfl⟩ : syracuseStep 1442183 = 2163275) B2163275
theorem B8225171 : Blo 960589 8225171 := bstep (se 1 (by rfl) ⟨6168878, by rfl⟩ : syracuseStep 8225171 = 12337757) B12337757
theorem B4882841 : Blo 960589 4882841 := bstep (se 2 (by rfl) ⟨1831065, by rfl⟩ : syracuseStep 4882841 = 3662131) B3662131
theorem B1442219 : Blo 960589 1442219 := bstep (se 1 (by rfl) ⟨1081664, by rfl⟩ : syracuseStep 1442219 = 2163329) B2163329
theorem B1442249 : Blo 960589 1442249 := bstep (se 2 (by rfl) ⟨540843, by rfl⟩ : syracuseStep 1442249 = 1081687) B1081687
theorem B52724195 : Blo 960589 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B1442363 : Blo 960589 1442363 := bstep (se 1 (by rfl) ⟨1081772, by rfl⟩ : syracuseStep 1442363 = 2163545) B2163545
theorem B1442423 : Blo 960589 1442423 := bstep (se 1 (by rfl) ⟨1081817, by rfl⟩ : syracuseStep 1442423 = 2163635) B2163635
theorem B1442447 : Blo 960589 1442447 := bstep (se 1 (by rfl) ⟨1081835, by rfl⟩ : syracuseStep 1442447 = 2163671) B2163671
theorem B2163347 : Blo 960589 2163347 := bstep (se 1 (by rfl) ⟨1622510, by rfl⟩ : syracuseStep 2163347 = 3245021) B3245021
theorem B1442489 : Blo 960589 1442489 := bstep (se 2 (by rfl) ⟨540933, by rfl⟩ : syracuseStep 1442489 = 1081867) B1081867
theorem B2163401 : Blo 960589 2163401 := bstep (se 2 (by rfl) ⟨811275, by rfl⟩ : syracuseStep 2163401 = 1622551) B1622551
theorem B1442567 : Blo 960589 1442567 := bstep (se 1 (by rfl) ⟨1081925, by rfl⟩ : syracuseStep 1442567 = 2163851) B2163851
theorem B1082119 : Blo 960589 1082119 := bstep (se 1 (by rfl) ⟨811589, by rfl⟩ : syracuseStep 1082119 = 1623179) B1623179
theorem B1442603 : Blo 960589 1442603 := bstep (se 1 (by rfl) ⟨1081952, by rfl⟩ : syracuseStep 1442603 = 2163905) B2163905
theorem B3244859 : Blo 960589 3244859 := bstep (se 1 (by rfl) ⟨2433644, by rfl⟩ : syracuseStep 3244859 = 4867289) B4867289
theorem B1442633 : Blo 960589 1442633 := bstep (se 2 (by rfl) ⟨540987, by rfl⟩ : syracuseStep 1442633 = 1081975) B1081975
theorem B1442747 : Blo 960589 1442747 := bstep (se 1 (by rfl) ⟨1082060, by rfl⟩ : syracuseStep 1442747 = 2164121) B2164121
theorem B1082299 : Blo 960589 1082299 := bstep (se 1 (by rfl) ⟨811724, by rfl⟩ : syracuseStep 1082299 = 1623449) B1623449
theorem B1442807 : Blo 960589 1442807 := bstep (se 1 (by rfl) ⟨1082105, by rfl⟩ : syracuseStep 1442807 = 2164211) B2164211
theorem B1442831 : Blo 960589 1442831 := bstep (se 1 (by rfl) ⟨1082123, by rfl⟩ : syracuseStep 1442831 = 2164247) B2164247
theorem B1442873 : Blo 960589 1442873 := bstep (se 2 (by rfl) ⟨541077, by rfl⟩ : syracuseStep 1442873 = 1082155) B1082155
theorem B3474551 : Blo 960589 3474551 := bstep (se 1 (by rfl) ⟨2605913, by rfl⟩ : syracuseStep 3474551 = 5211827) B5211827
theorem B1442951 : Blo 960589 1442951 := bstep (se 1 (by rfl) ⟨1082213, by rfl⟩ : syracuseStep 1442951 = 2164427) B2164427
theorem B1442987 : Blo 960589 1442987 := bstep (se 1 (by rfl) ⟨1082240, by rfl⟩ : syracuseStep 1442987 = 2164481) B2164481
theorem B1443017 : Blo 960589 1443017 := bstep (se 2 (by rfl) ⟨541131, by rfl⟩ : syracuseStep 1443017 = 1082263) B1082263
theorem B3245345 : Blo 960589 3245345 := bstep (se 2 (by rfl) ⟨1217004, by rfl⟩ : syracuseStep 3245345 = 2434009) B2434009
theorem B1443131 : Blo 960589 1443131 := bstep (se 1 (by rfl) ⟨1082348, by rfl⟩ : syracuseStep 1443131 = 2164697) B2164697
theorem B1443191 : Blo 960589 1443191 := bstep (se 1 (by rfl) ⟨1082393, by rfl⟩ : syracuseStep 1443191 = 2164787) B2164787
theorem B2164103 : Blo 960589 2164103 := bstep (se 1 (by rfl) ⟨1623077, by rfl⟩ : syracuseStep 2164103 = 3246155) B3246155
theorem B1443215 : Blo 960589 1443215 := bstep (se 1 (by rfl) ⟨1082411, by rfl⟩ : syracuseStep 1443215 = 2164823) B2164823
theorem B1082767 : Blo 960589 1082767 := bstep (se 1 (by rfl) ⟨812075, by rfl⟩ : syracuseStep 1082767 = 1624151) B1624151
theorem B1443257 : Blo 960589 1443257 := bstep (se 2 (by rfl) ⟨541221, by rfl⟩ : syracuseStep 1443257 = 1082443) B1082443
theorem B1443335 : Blo 960589 1443335 := bstep (se 1 (by rfl) ⟨1082501, by rfl⟩ : syracuseStep 1443335 = 2165003) B2165003
theorem B1443371 : Blo 960589 1443371 := bstep (se 1 (by rfl) ⟨1082528, by rfl⟩ : syracuseStep 1443371 = 2165057) B2165057
theorem B2164283 : Blo 960589 2164283 := bstep (se 1 (by rfl) ⟨1623212, by rfl⟩ : syracuseStep 2164283 = 3246425) B3246425
theorem B1443401 : Blo 960589 1443401 := bstep (se 2 (by rfl) ⟨541275, by rfl⟩ : syracuseStep 1443401 = 1082551) B1082551
theorem B2164409 : Blo 960589 2164409 := bstep (se 2 (by rfl) ⟨811653, by rfl⟩ : syracuseStep 2164409 = 1623307) B1623307
theorem B1443515 : Blo 960589 1443515 := bstep (se 1 (by rfl) ⟨1082636, by rfl⟩ : syracuseStep 1443515 = 2165273) B2165273
theorem B1443575 : Blo 960589 1443575 := bstep (se 1 (by rfl) ⟨1082681, by rfl⟩ : syracuseStep 1443575 = 2165363) B2165363
theorem B1443599 : Blo 960589 1443599 := bstep (se 1 (by rfl) ⟨1082699, by rfl⟩ : syracuseStep 1443599 = 2165399) B2165399
theorem B1443641 : Blo 960589 1443641 := bstep (se 2 (by rfl) ⟨541365, by rfl⟩ : syracuseStep 1443641 = 1082731) B1082731
theorem B3245939 : Blo 960589 3245939 := bstep (se 1 (by rfl) ⟨2434454, by rfl⟩ : syracuseStep 3245939 = 4868909) B4868909
theorem B1443719 : Blo 960589 1443719 := bstep (se 1 (by rfl) ⟨1082789, by rfl⟩ : syracuseStep 1443719 = 2165579) B2165579
theorem B1083271 : Blo 960589 1083271 := bstep (se 1 (by rfl) ⟨812453, by rfl⟩ : syracuseStep 1083271 = 1624907) B1624907
theorem B1443755 : Blo 960589 1443755 := bstep (se 1 (by rfl) ⟨1082816, by rfl⟩ : syracuseStep 1443755 = 2165633) B2165633
theorem B1443785 : Blo 960589 1443785 := bstep (se 2 (by rfl) ⟨541419, by rfl⟩ : syracuseStep 1443785 = 1082839) B1082839
theorem B2164751 : Blo 960589 2164751 := bstep (se 1 (by rfl) ⟨1623563, by rfl⟩ : syracuseStep 2164751 = 3247127) B3247127
theorem B2164769 : Blo 960589 2164769 := bstep (se 2 (by rfl) ⟨811788, by rfl⟩ : syracuseStep 2164769 = 1623577) B1623577
theorem B1443899 : Blo 960589 1443899 := bstep (se 1 (by rfl) ⟨1082924, by rfl⟩ : syracuseStep 1443899 = 2165849) B2165849
theorem B1083451 : Blo 960589 1083451 := bstep (se 1 (by rfl) ⟨812588, by rfl⟩ : syracuseStep 1083451 = 1625177) B1625177
theorem B1443959 : Blo 960589 1443959 := bstep (se 1 (by rfl) ⟨1082969, by rfl⟩ : syracuseStep 1443959 = 2165939) B2165939
theorem B1443983 : Blo 960589 1443983 := bstep (se 1 (by rfl) ⟨1082987, by rfl⟩ : syracuseStep 1443983 = 2165975) B2165975
theorem B1444025 : Blo 960589 1444025 := bstep (se 2 (by rfl) ⟨541509, by rfl⟩ : syracuseStep 1444025 = 1083019) B1083019
theorem B1444103 : Blo 960589 1444103 := bstep (se 1 (by rfl) ⟨1083077, by rfl⟩ : syracuseStep 1444103 = 2166155) B2166155
theorem B1444139 : Blo 960589 1444139 := bstep (se 1 (by rfl) ⟨1083104, by rfl⟩ : syracuseStep 1444139 = 2166209) B2166209
theorem B36964673 : Blo 960589 36964673 := bstep (se 2 (by rfl) ⟨13861752, by rfl⟩ : syracuseStep 36964673 = 27723505) B27723505
theorem B1444169 : Blo 960589 1444169 := bstep (se 2 (by rfl) ⟨541563, by rfl⟩ : syracuseStep 1444169 = 1083127) B1083127
theorem B2165111 : Blo 960589 2165111 := bstep (se 1 (by rfl) ⟨1623833, by rfl⟩ : syracuseStep 2165111 = 3247667) B3247667
theorem B1444283 : Blo 960589 1444283 := bstep (se 1 (by rfl) ⟨1083212, by rfl⟩ : syracuseStep 1444283 = 2166425) B2166425
theorem B1444343 : Blo 960589 1444343 := bstep (se 1 (by rfl) ⟨1083257, by rfl⟩ : syracuseStep 1444343 = 2166515) B2166515
theorem B1444367 : Blo 960589 1444367 := bstep (se 1 (by rfl) ⟨1083275, by rfl⟩ : syracuseStep 1444367 = 2166551) B2166551
theorem B1083919 : Blo 960589 1083919 := bstep (se 1 (by rfl) ⟨812939, by rfl⟩ : syracuseStep 1083919 = 1625879) B1625879
theorem B2165291 : Blo 960589 2165291 := bstep (se 1 (by rfl) ⟨1623968, by rfl⟩ : syracuseStep 2165291 = 3247937) B3247937
theorem B1444409 : Blo 960589 1444409 := bstep (se 2 (by rfl) ⟨541653, by rfl⟩ : syracuseStep 1444409 = 1083307) B1083307
theorem B1444487 : Blo 960589 1444487 := bstep (se 1 (by rfl) ⟨1083365, by rfl⟩ : syracuseStep 1444487 = 2166731) B2166731
theorem B1444523 : Blo 960589 1444523 := bstep (se 1 (by rfl) ⟨1083392, by rfl⟩ : syracuseStep 1444523 = 2166785) B2166785
theorem B1444553 : Blo 960589 1444553 := bstep (se 2 (by rfl) ⟨541707, by rfl⟩ : syracuseStep 1444553 = 1083415) B1083415
theorem B1444667 : Blo 960589 1444667 := bstep (se 1 (by rfl) ⟨1083500, by rfl⟩ : syracuseStep 1444667 = 2167001) B2167001
theorem B1444727 : Blo 960589 1444727 := bstep (se 1 (by rfl) ⟨1083545, by rfl⟩ : syracuseStep 1444727 = 2167091) B2167091
theorem B1444751 : Blo 960589 1444751 := bstep (se 1 (by rfl) ⟨1083563, by rfl⟩ : syracuseStep 1444751 = 2167127) B2167127
theorem B2165651 : Blo 960589 2165651 := bstep (se 1 (by rfl) ⟨1624238, by rfl⟩ : syracuseStep 2165651 = 3248477) B3248477
theorem B1444793 : Blo 960589 1444793 := bstep (se 2 (by rfl) ⟨541797, by rfl⟩ : syracuseStep 1444793 = 1083595) B1083595
theorem B2165705 : Blo 960589 2165705 := bstep (se 2 (by rfl) ⟨812139, by rfl⟩ : syracuseStep 2165705 = 1624279) B1624279
theorem B1444871 : Blo 960589 1444871 := bstep (se 1 (by rfl) ⟨1083653, by rfl⟩ : syracuseStep 1444871 = 2167307) B2167307
theorem B1084423 : Blo 960589 1084423 := bstep (se 1 (by rfl) ⟨813317, by rfl⟩ : syracuseStep 1084423 = 1626635) B1626635
theorem B1444907 : Blo 960589 1444907 := bstep (se 1 (by rfl) ⟨1083680, by rfl⟩ : syracuseStep 1444907 = 2167361) B2167361
theorem B1444937 : Blo 960589 1444937 := bstep (se 2 (by rfl) ⟨541851, by rfl⟩ : syracuseStep 1444937 = 1083703) B1083703
theorem B1445051 : Blo 960589 1445051 := bstep (se 1 (by rfl) ⟨1083788, by rfl⟩ : syracuseStep 1445051 = 2167577) B2167577
theorem B1084603 : Blo 960589 1084603 := bstep (se 1 (by rfl) ⟨813452, by rfl⟩ : syracuseStep 1084603 = 1626905) B1626905
theorem B3083465 : Blo 960589 3083465 := bstep (se 2 (by rfl) ⟨1156299, by rfl⟩ : syracuseStep 3083465 = 2312599) B2312599
theorem B1445111 : Blo 960589 1445111 := bstep (se 1 (by rfl) ⟨1083833, by rfl⟩ : syracuseStep 1445111 = 2167667) B2167667
theorem B1445135 : Blo 960589 1445135 := bstep (se 1 (by rfl) ⟨1083851, by rfl⟩ : syracuseStep 1445135 = 2167703) B2167703
theorem B1445177 : Blo 960589 1445177 := bstep (se 2 (by rfl) ⟨541941, by rfl⟩ : syracuseStep 1445177 = 1083883) B1083883
theorem B1445255 : Blo 960589 1445255 := bstep (se 1 (by rfl) ⟨1083941, by rfl⟩ : syracuseStep 1445255 = 2167883) B2167883
theorem B1445291 : Blo 960589 1445291 := bstep (se 1 (by rfl) ⟨1083968, by rfl⟩ : syracuseStep 1445291 = 2167937) B2167937
theorem B1445321 : Blo 960589 1445321 := bstep (se 2 (by rfl) ⟨541995, by rfl⟩ : syracuseStep 1445321 = 1083991) B1083991
theorem B5475883 : Blo 960589 5475883 := bstep (se 1 (by rfl) ⟨4106912, by rfl⟩ : syracuseStep 5475883 = 8213825) B8213825
theorem B1445435 : Blo 960589 1445435 := bstep (se 1 (by rfl) ⟨1084076, by rfl⟩ : syracuseStep 1445435 = 2168153) B2168153
theorem B1445495 : Blo 960589 1445495 := bstep (se 1 (by rfl) ⟨1084121, by rfl⟩ : syracuseStep 1445495 = 2168243) B2168243
theorem B2166407 : Blo 960589 2166407 := bstep (se 1 (by rfl) ⟨1624805, by rfl⟩ : syracuseStep 2166407 = 3249611) B3249611
theorem B1445519 : Blo 960589 1445519 := bstep (se 1 (by rfl) ⟨1084139, by rfl⟩ : syracuseStep 1445519 = 2168279) B2168279
theorem B1085071 : Blo 960589 1085071 := bstep (se 1 (by rfl) ⟨813803, by rfl⟩ : syracuseStep 1085071 = 1627607) B1627607
theorem B1445561 : Blo 960589 1445561 := bstep (se 2 (by rfl) ⟨542085, by rfl⟩ : syracuseStep 1445561 = 1084171) B1084171
theorem B1445639 : Blo 960589 1445639 := bstep (se 1 (by rfl) ⟨1084229, by rfl⟩ : syracuseStep 1445639 = 2168459) B2168459
theorem B1445675 : Blo 960589 1445675 := bstep (se 1 (by rfl) ⟨1084256, by rfl⟩ : syracuseStep 1445675 = 2168513) B2168513
theorem B2166587 : Blo 960589 2166587 := bstep (se 1 (by rfl) ⟨1624940, by rfl⟩ : syracuseStep 2166587 = 3249881) B3249881
theorem B1445705 : Blo 960589 1445705 := bstep (se 2 (by rfl) ⟨542139, by rfl⟩ : syracuseStep 1445705 = 1084279) B1084279
theorem B2166713 : Blo 960589 2166713 := bstep (se 2 (by rfl) ⟨812517, by rfl⟩ : syracuseStep 2166713 = 1625035) B1625035
theorem B1445819 : Blo 960589 1445819 := bstep (se 1 (by rfl) ⟨1084364, by rfl⟩ : syracuseStep 1445819 = 2168729) B2168729
theorem B1445879 : Blo 960589 1445879 := bstep (se 1 (by rfl) ⟨1084409, by rfl⟩ : syracuseStep 1445879 = 2168819) B2168819
theorem B9375749 : Blo 960589 9375749 := bstep (se 4 (by rfl) ⟨878976, by rfl⟩ : syracuseStep 9375749 = 1757953) B1757953
theorem B1445903 : Blo 960589 1445903 := bstep (se 1 (by rfl) ⟨1084427, by rfl⟩ : syracuseStep 1445903 = 2168855) B2168855
theorem B7311383 : Blo 960589 7311383 := bstep (se 1 (by rfl) ⟨5483537, by rfl⟩ : syracuseStep 7311383 = 10967075) B10967075
theorem B1445945 : Blo 960589 1445945 := bstep (se 2 (by rfl) ⟨542229, by rfl⟩ : syracuseStep 1445945 = 1084459) B1084459
theorem B1446023 : Blo 960589 1446023 := bstep (se 1 (by rfl) ⟨1084517, by rfl⟩ : syracuseStep 1446023 = 2169035) B2169035
theorem B1446059 : Blo 960589 1446059 := bstep (se 1 (by rfl) ⟨1084544, by rfl⟩ : syracuseStep 1446059 = 2169089) B2169089
theorem B1446089 : Blo 960589 1446089 := bstep (se 2 (by rfl) ⟨542283, by rfl⟩ : syracuseStep 1446089 = 1084567) B1084567
theorem B2167055 : Blo 960589 2167055 := bstep (se 1 (by rfl) ⟨1625291, by rfl⟩ : syracuseStep 2167055 = 3250583) B3250583
theorem B2167073 : Blo 960589 2167073 := bstep (se 2 (by rfl) ⟨812652, by rfl⟩ : syracuseStep 2167073 = 1625305) B1625305
theorem B1446203 : Blo 960589 1446203 := bstep (se 1 (by rfl) ⟨1084652, by rfl⟩ : syracuseStep 1446203 = 2169305) B2169305
theorem B1446263 : Blo 960589 1446263 := bstep (se 1 (by rfl) ⟨1084697, by rfl⟩ : syracuseStep 1446263 = 2169395) B2169395
theorem B1446287 : Blo 960589 1446287 := bstep (se 1 (by rfl) ⟨1084715, by rfl⟩ : syracuseStep 1446287 = 2169431) B2169431
theorem B3248531 : Blo 960589 3248531 := bstep (se 1 (by rfl) ⟨2436398, by rfl⟩ : syracuseStep 3248531 = 4872797) B4872797
theorem B1216939 : Blo 960589 1216939 := bstep (se 1 (by rfl) ⟨912704, by rfl⟩ : syracuseStep 1216939 = 1825409) B1825409
theorem B1446329 : Blo 960589 1446329 := bstep (se 2 (by rfl) ⟨542373, by rfl⟩ : syracuseStep 1446329 = 1084747) B1084747
theorem B1446407 : Blo 960589 1446407 := bstep (se 1 (by rfl) ⟨1084805, by rfl⟩ : syracuseStep 1446407 = 2169611) B2169611
theorem B1446443 : Blo 960589 1446443 := bstep (se 1 (by rfl) ⟨1084832, by rfl⟩ : syracuseStep 1446443 = 2169665) B2169665
theorem B1446473 : Blo 960589 1446473 := bstep (se 2 (by rfl) ⟨542427, by rfl⟩ : syracuseStep 1446473 = 1084855) B1084855
theorem B2167415 : Blo 960589 2167415 := bstep (se 1 (by rfl) ⟨1625561, by rfl⟩ : syracuseStep 2167415 = 3251123) B3251123
theorem B1446587 : Blo 960589 1446587 := bstep (se 1 (by rfl) ⟨1084940, by rfl⟩ : syracuseStep 1446587 = 2169881) B2169881
theorem B8327909 : Blo 960589 8327909 := bstep (se 4 (by rfl) ⟨780741, by rfl⟩ : syracuseStep 8327909 = 1561483) B1561483
theorem B1446647 : Blo 960589 1446647 := bstep (se 1 (by rfl) ⟨1084985, by rfl⟩ : syracuseStep 1446647 = 2169971) B2169971
theorem B1446671 : Blo 960589 1446671 := bstep (se 1 (by rfl) ⟨1085003, by rfl⟩ : syracuseStep 1446671 = 2170007) B2170007
theorem B2167595 : Blo 960589 2167595 := bstep (se 1 (by rfl) ⟨1625696, by rfl⟩ : syracuseStep 2167595 = 3251393) B3251393
theorem B1446713 : Blo 960589 1446713 := bstep (se 2 (by rfl) ⟨542517, by rfl⟩ : syracuseStep 1446713 = 1085035) B1085035
theorem B1446791 : Blo 960589 1446791 := bstep (se 1 (by rfl) ⟨1085093, by rfl⟩ : syracuseStep 1446791 = 2170187) B2170187
theorem B2921363 : Blo 960589 2921363 := bstep (se 1 (by rfl) ⟨2191022, by rfl⟩ : syracuseStep 2921363 = 4382045) B4382045
theorem B1446827 : Blo 960589 1446827 := bstep (se 1 (by rfl) ⟨1085120, by rfl⟩ : syracuseStep 1446827 = 2170241) B2170241
theorem B14062517 : Blo 960589 14062517 := bstep (se 5 (by rfl) ⟨659180, by rfl⟩ : syracuseStep 14062517 = 1318361) B1318361
theorem B1446857 : Blo 960589 1446857 := bstep (se 2 (by rfl) ⟨542571, by rfl⟩ : syracuseStep 1446857 = 1085143) B1085143
theorem B10949579 : Blo 960589 10949579 := bstep (se 1 (by rfl) ⟨8212184, by rfl⟩ : syracuseStep 10949579 = 16424369) B16424369
theorem B5477341 : Blo 960589 5477341 := bstep (se 3 (by rfl) ⟨1027001, by rfl⟩ : syracuseStep 5477341 = 2054003) B2054003
theorem B2167955 : Blo 960589 2167955 := bstep (se 1 (by rfl) ⟨1625966, by rfl⟩ : syracuseStep 2167955 = 3251933) B3251933
theorem B2168009 : Blo 960589 2168009 := bstep (se 2 (by rfl) ⟨813003, by rfl⟩ : syracuseStep 2168009 = 1626007) B1626007
theorem B1217911 : Blo 960589 1217911 := bstep (se 1 (by rfl) ⟨913433, by rfl⟩ : syracuseStep 1217911 = 1826867) B1826867
theorem B1218235 : Blo 960589 1218235 := bstep (se 1 (by rfl) ⟨913676, by rfl⟩ : syracuseStep 1218235 = 1827353) B1827353
theorem B3249935 : Blo 960589 3249935 := bstep (se 1 (by rfl) ⟨2437451, by rfl⟩ : syracuseStep 3249935 = 4874903) B4874903
theorem B2168711 : Blo 960589 2168711 := bstep (se 1 (by rfl) ⟨1626533, by rfl⟩ : syracuseStep 2168711 = 3253067) B3253067
theorem B7804835 : Blo 960589 7804835 := bstep (se 1 (by rfl) ⟨5853626, by rfl⟩ : syracuseStep 7804835 = 11707253) B11707253
theorem B20846605 : Blo 960589 20846605 := bstep (se 3 (by rfl) ⟨3908738, by rfl⟩ : syracuseStep 20846605 = 7817477) B7817477
theorem B3250205 : Blo 960589 3250205 := bstep (se 3 (by rfl) ⟨609413, by rfl⟩ : syracuseStep 3250205 = 1218827) B1218827
theorem B2168891 : Blo 960589 2168891 := bstep (se 1 (by rfl) ⟨1626668, by rfl⟩ : syracuseStep 2168891 = 3253337) B3253337
theorem B162437237 : Blo 960589 162437237 := bstep (se 5 (by rfl) ⟨7614245, by rfl⟩ : syracuseStep 162437237 = 15228491) B15228491
theorem B2169017 : Blo 960589 2169017 := bstep (se 2 (by rfl) ⟨813381, by rfl⟩ : syracuseStep 2169017 = 1626763) B1626763
theorem B2169359 : Blo 960589 2169359 := bstep (se 1 (by rfl) ⟨1627019, by rfl⟩ : syracuseStep 2169359 = 3254039) B3254039
theorem B2169377 : Blo 960589 2169377 := bstep (se 2 (by rfl) ⟨813516, by rfl⟩ : syracuseStep 2169377 = 1627033) B1627033
theorem B1219207 : Blo 960589 1219207 := bstep (se 1 (by rfl) ⟨914405, by rfl⟩ : syracuseStep 1219207 = 1828811) B1828811
theorem B2169719 : Blo 960589 2169719 := bstep (se 1 (by rfl) ⟨1627289, by rfl⟩ : syracuseStep 2169719 = 3254579) B3254579
theorem B2432015 : Blo 960589 2432015 := bstep (se 1 (by rfl) ⟨1824011, by rfl⟩ : syracuseStep 2432015 = 3648023) B3648023
theorem B1219627 : Blo 960589 1219627 := bstep (se 1 (by rfl) ⟨914720, by rfl⟩ : syracuseStep 1219627 = 1829441) B1829441
theorem B2169899 : Blo 960589 2169899 := bstep (se 1 (by rfl) ⟨1627424, by rfl⟩ : syracuseStep 2169899 = 3254849) B3254849
theorem B1219855 : Blo 960589 1219855 := bstep (se 1 (by rfl) ⟨914891, by rfl⟩ : syracuseStep 1219855 = 1829783) B1829783
theorem B9248093 : Blo 960589 9248093 := bstep (se 3 (by rfl) ⟨1734017, by rfl⟩ : syracuseStep 9248093 = 3468035) B3468035
theorem B2170259 : Blo 960589 2170259 := bstep (se 1 (by rfl) ⟨1627694, by rfl⟩ : syracuseStep 2170259 = 3255389) B3255389
theorem B3251609 : Blo 960589 3251609 := bstep (se 2 (by rfl) ⟨1219353, by rfl⟩ : syracuseStep 3251609 = 2438707) B2438707
theorem B2170313 : Blo 960589 2170313 := bstep (se 2 (by rfl) ⟨813867, by rfl⟩ : syracuseStep 2170313 = 1627735) B1627735
theorem B2465291 : Blo 960589 2465291 := bstep (se 1 (by rfl) ⟨1848968, by rfl⟩ : syracuseStep 2465291 = 3697937) B3697937
theorem B2432713 : Blo 960589 2432713 := bstep (se 2 (by rfl) ⟨912267, by rfl⟩ : syracuseStep 2432713 = 1824535) B1824535
theorem B2432855 : Blo 960589 2432855 := bstep (se 1 (by rfl) ⟨1824641, by rfl⟩ : syracuseStep 2432855 = 3649283) B3649283
theorem B2924441 : Blo 960589 2924441 := bstep (se 2 (by rfl) ⟨1096665, by rfl⟩ : syracuseStep 2924441 = 2193331) B2193331
theorem B1220599 : Blo 960589 1220599 := bstep (se 1 (by rfl) ⟨915449, by rfl⟩ : syracuseStep 1220599 = 1830899) B1830899
theorem B3252311 : Blo 960589 3252311 := bstep (se 1 (by rfl) ⟨2439233, by rfl⟩ : syracuseStep 3252311 = 4878467) B4878467
theorem B3907703 : Blo 960589 3907703 := bstep (se 1 (by rfl) ⟨2930777, by rfl⟩ : syracuseStep 3907703 = 5861555) B5861555
theorem B3088925 : Blo 960589 3088925 := bstep (se 3 (by rfl) ⟨579173, by rfl⟩ : syracuseStep 3088925 = 1158347) B1158347
theorem B3252797 : Blo 960589 3252797 := bstep (se 3 (by rfl) ⟨609899, by rfl⟩ : syracuseStep 3252797 = 1219799) B1219799
theorem B2597633 : Blo 960589 2597633 := bstep (se 2 (by rfl) ⟨974112, by rfl⟩ : syracuseStep 2597633 = 1948225) B1948225
theorem B5481533 : Blo 960589 5481533 := bstep (se 3 (by rfl) ⟨1027787, by rfl⟩ : syracuseStep 5481533 = 2055575) B2055575
theorem B2598041 : Blo 960589 2598041 := bstep (se 2 (by rfl) ⟨974265, by rfl⟩ : syracuseStep 2598041 = 1948531) B1948531
theorem B4629811 : Blo 960589 4629811 := bstep (se 1 (by rfl) ⟨3472358, by rfl⟩ : syracuseStep 4629811 = 6944717) B6944717
theorem B2598259 : Blo 960589 2598259 := bstep (se 1 (by rfl) ⟨1948694, by rfl⟩ : syracuseStep 2598259 = 3897389) B3897389
theorem B3908999 : Blo 960589 3908999 := bstep (se 1 (by rfl) ⟨2931749, by rfl⟩ : syracuseStep 3908999 = 5863499) B5863499
theorem B10429955 : Blo 960589 10429955 := bstep (se 1 (by rfl) ⟨7822466, by rfl⟩ : syracuseStep 10429955 = 15644933) B15644933
theorem B3909131 : Blo 960589 3909131 := bstep (se 1 (by rfl) ⟨2931848, by rfl⟩ : syracuseStep 3909131 = 5863697) B5863697
theorem B18490949 : Blo 960589 18490949 := bstep (se 4 (by rfl) ⟨1733526, by rfl⟩ : syracuseStep 18490949 = 3467053) B3467053
theorem B5482241 : Blo 960589 5482241 := bstep (se 2 (by rfl) ⟨2055840, by rfl⟩ : syracuseStep 5482241 = 4111681) B4111681
theorem B2434931 : Blo 960589 2434931 := bstep (se 1 (by rfl) ⟨1826198, by rfl⟩ : syracuseStep 2434931 = 3652397) B3652397
theorem B3254201 : Blo 960589 3254201 := bstep (se 2 (by rfl) ⟨1220325, by rfl⟩ : syracuseStep 3254201 = 2440651) B2440651
theorem B960647 : Blo 960589 960647 := bstep (se 1 (by rfl) ⟨720485, by rfl⟩ : syracuseStep 960647 = 1440971) B1440971
theorem B960655 : Blo 960589 960655 := bstep (se 1 (by rfl) ⟨720491, by rfl⟩ : syracuseStep 960655 = 1440983) B1440983
theorem B5843117 : Blo 960589 5843117 := bstep (se 3 (by rfl) ⟨1095584, by rfl⟩ : syracuseStep 5843117 = 2191169) B2191169
theorem B960699 : Blo 960589 960699 := bstep (se 1 (by rfl) ⟨720524, by rfl⟩ : syracuseStep 960699 = 1441049) B1441049
theorem B960775 : Blo 960589 960775 := bstep (se 1 (by rfl) ⟨720581, by rfl⟩ : syracuseStep 960775 = 1441163) B1441163
theorem B960783 : Blo 960589 960783 := bstep (se 1 (by rfl) ⟨720587, by rfl⟩ : syracuseStep 960783 = 1441175) B1441175
theorem B960827 : Blo 960589 960827 := bstep (se 1 (by rfl) ⟨720620, by rfl⟩ : syracuseStep 960827 = 1441241) B1441241
theorem B2435447 : Blo 960589 2435447 := bstep (se 1 (by rfl) ⟨1826585, by rfl⟩ : syracuseStep 2435447 = 3653171) B3653171
theorem B960903 : Blo 960589 960903 := bstep (se 1 (by rfl) ⟨720677, by rfl⟩ : syracuseStep 960903 = 1441355) B1441355
theorem B960911 : Blo 960589 960911 := bstep (se 1 (by rfl) ⟨720683, by rfl⟩ : syracuseStep 960911 = 1441367) B1441367
theorem B960955 : Blo 960589 960955 := bstep (se 1 (by rfl) ⟨720716, by rfl⟩ : syracuseStep 960955 = 1441433) B1441433
theorem B961031 : Blo 960589 961031 := bstep (se 1 (by rfl) ⟨720773, by rfl⟩ : syracuseStep 961031 = 1441547) B1441547
theorem B3254795 : Blo 960589 3254795 := bstep (se 1 (by rfl) ⟨2441096, by rfl⟩ : syracuseStep 3254795 = 4882193) B4882193
theorem B961039 : Blo 960589 961039 := bstep (se 1 (by rfl) ⟨720779, by rfl⟩ : syracuseStep 961039 = 1441559) B1441559
theorem B961083 : Blo 960589 961083 := bstep (se 1 (by rfl) ⟨720812, by rfl⟩ : syracuseStep 961083 = 1441625) B1441625
theorem B3254903 : Blo 960589 3254903 := bstep (se 1 (by rfl) ⟨2441177, by rfl⟩ : syracuseStep 3254903 = 4882355) B4882355
theorem B961159 : Blo 960589 961159 := bstep (se 1 (by rfl) ⟨720869, by rfl⟩ : syracuseStep 961159 = 1441739) B1441739
theorem B961167 : Blo 960589 961167 := bstep (se 1 (by rfl) ⟨720875, by rfl⟩ : syracuseStep 961167 = 1441751) B1441751
theorem B1026703 : Blo 960589 1026703 := bstep (se 1 (by rfl) ⟨770027, by rfl⟩ : syracuseStep 1026703 = 1540055) B1540055
theorem B961211 : Blo 960589 961211 := bstep (se 1 (by rfl) ⟨720908, by rfl⟩ : syracuseStep 961211 = 1441817) B1441817
theorem B961287 : Blo 960589 961287 := bstep (se 1 (by rfl) ⟨720965, by rfl⟩ : syracuseStep 961287 = 1441931) B1441931
theorem B961295 : Blo 960589 961295 := bstep (se 1 (by rfl) ⟨720971, by rfl⟩ : syracuseStep 961295 = 1441943) B1441943
theorem B961339 : Blo 960589 961339 := bstep (se 1 (by rfl) ⟨721004, by rfl⟩ : syracuseStep 961339 = 1442009) B1442009
theorem B3910459 : Blo 960589 3910459 := bstep (se 1 (by rfl) ⟨2932844, by rfl⟩ : syracuseStep 3910459 = 5865689) B5865689
theorem B5548915 : Blo 960589 5548915 := bstep (se 1 (by rfl) ⟨4161686, by rfl⟩ : syracuseStep 5548915 = 8323373) B8323373
theorem B961415 : Blo 960589 961415 := bstep (se 1 (by rfl) ⟨721061, by rfl⟩ : syracuseStep 961415 = 1442123) B1442123
theorem B961423 : Blo 960589 961423 := bstep (se 1 (by rfl) ⟨721067, by rfl⟩ : syracuseStep 961423 = 1442135) B1442135
theorem B5548985 : Blo 960589 5548985 := bstep (se 2 (by rfl) ⟨2080869, by rfl⟩ : syracuseStep 5548985 = 4161739) B4161739
theorem B961467 : Blo 960589 961467 := bstep (se 1 (by rfl) ⟨721100, by rfl⟩ : syracuseStep 961467 = 1442201) B1442201
theorem B961543 : Blo 960589 961543 := bstep (se 1 (by rfl) ⟨721157, by rfl⟩ : syracuseStep 961543 = 1442315) B1442315
theorem B3648523 : Blo 960589 3648523 := bstep (se 1 (by rfl) ⟨2736392, by rfl⟩ : syracuseStep 3648523 = 5472785) B5472785
theorem B961551 : Blo 960589 961551 := bstep (se 1 (by rfl) ⟨721163, by rfl⟩ : syracuseStep 961551 = 1442327) B1442327
theorem B4107307 : Blo 960589 4107307 := bstep (se 1 (by rfl) ⟨3080480, by rfl⟩ : syracuseStep 4107307 = 6160961) B6160961
theorem B961595 : Blo 960589 961595 := bstep (se 1 (by rfl) ⟨721196, by rfl⟩ : syracuseStep 961595 = 1442393) B1442393
theorem B961671 : Blo 960589 961671 := bstep (se 1 (by rfl) ⟨721253, by rfl⟩ : syracuseStep 961671 = 1442507) B1442507
theorem B961679 : Blo 960589 961679 := bstep (se 1 (by rfl) ⟨721259, by rfl⟩ : syracuseStep 961679 = 1442519) B1442519
theorem B961723 : Blo 960589 961723 := bstep (se 1 (by rfl) ⟨721292, by rfl⟩ : syracuseStep 961723 = 1442585) B1442585
theorem B11709677 : Blo 960589 11709677 := bstep (se 3 (by rfl) ⟨2195564, by rfl⟩ : syracuseStep 11709677 = 4391129) B4391129
theorem B961799 : Blo 960589 961799 := bstep (se 1 (by rfl) ⟨721349, by rfl⟩ : syracuseStep 961799 = 1442699) B1442699
theorem B961807 : Blo 960589 961807 := bstep (se 1 (by rfl) ⟨721355, by rfl⟩ : syracuseStep 961807 = 1442711) B1442711
theorem B3648827 : Blo 960589 3648827 := bstep (se 1 (by rfl) ⟨2736620, by rfl⟩ : syracuseStep 3648827 = 5473241) B5473241
theorem B961851 : Blo 960589 961851 := bstep (se 1 (by rfl) ⟨721388, by rfl⟩ : syracuseStep 961851 = 1442777) B1442777
theorem B2436439 : Blo 960589 2436439 := bstep (se 1 (by rfl) ⟨1827329, by rfl⟩ : syracuseStep 2436439 = 3654659) B3654659
theorem B961927 : Blo 960589 961927 := bstep (se 1 (by rfl) ⟨721445, by rfl⟩ : syracuseStep 961927 = 1442891) B1442891
theorem B1027463 : Blo 960589 1027463 := bstep (se 1 (by rfl) ⟨770597, by rfl⟩ : syracuseStep 1027463 = 1541195) B1541195
theorem B961935 : Blo 960589 961935 := bstep (se 1 (by rfl) ⟨721451, by rfl⟩ : syracuseStep 961935 = 1442903) B1442903
theorem B2469305 : Blo 960589 2469305 := bstep (se 2 (by rfl) ⟨925989, by rfl⟩ : syracuseStep 2469305 = 1851979) B1851979
theorem B961979 : Blo 960589 961979 := bstep (se 1 (by rfl) ⟨721484, by rfl⟩ : syracuseStep 961979 = 1442969) B1442969
theorem B962055 : Blo 960589 962055 := bstep (se 1 (by rfl) ⟨721541, by rfl⟩ : syracuseStep 962055 = 1443083) B1443083
theorem B962063 : Blo 960589 962063 := bstep (se 1 (by rfl) ⟨721547, by rfl⟩ : syracuseStep 962063 = 1443095) B1443095
theorem B962107 : Blo 960589 962107 := bstep (se 1 (by rfl) ⟨721580, by rfl⟩ : syracuseStep 962107 = 1443161) B1443161
theorem B7319159 : Blo 960589 7319159 := bstep (se 1 (by rfl) ⟨5489369, by rfl⟩ : syracuseStep 7319159 = 10978739) B10978739
theorem B962183 : Blo 960589 962183 := bstep (se 1 (by rfl) ⟨721637, by rfl⟩ : syracuseStep 962183 = 1443275) B1443275
theorem B2436743 : Blo 960589 2436743 := bstep (se 1 (by rfl) ⟨1827557, by rfl⟩ : syracuseStep 2436743 = 3655115) B3655115
theorem B962191 : Blo 960589 962191 := bstep (se 1 (by rfl) ⟨721643, by rfl⟩ : syracuseStep 962191 = 1443287) B1443287
theorem B1158799 : Blo 960589 1158799 := bstep (se 1 (by rfl) ⟨869099, by rfl⟩ : syracuseStep 1158799 = 1738199) B1738199
theorem B962235 : Blo 960589 962235 := bstep (se 1 (by rfl) ⟨721676, by rfl⟩ : syracuseStep 962235 = 1443353) B1443353
theorem B962311 : Blo 960589 962311 := bstep (se 1 (by rfl) ⟨721733, by rfl⟩ : syracuseStep 962311 = 1443467) B1443467
theorem B2436875 : Blo 960589 2436875 := bstep (se 1 (by rfl) ⟨1827656, by rfl⟩ : syracuseStep 2436875 = 3655313) B3655313
theorem B962319 : Blo 960589 962319 := bstep (se 1 (by rfl) ⟨721739, by rfl⟩ : syracuseStep 962319 = 1443479) B1443479
theorem B3649313 : Blo 960589 3649313 := bstep (se 2 (by rfl) ⟨1368492, by rfl⟩ : syracuseStep 3649313 = 2736985) B2736985
theorem B962363 : Blo 960589 962363 := bstep (se 1 (by rfl) ⟨721772, by rfl⟩ : syracuseStep 962363 = 1443545) B1443545
theorem B962439 : Blo 960589 962439 := bstep (se 1 (by rfl) ⟨721829, by rfl⟩ : syracuseStep 962439 = 1443659) B1443659
theorem B962447 : Blo 960589 962447 := bstep (se 1 (by rfl) ⟨721835, by rfl⟩ : syracuseStep 962447 = 1443671) B1443671
theorem B962491 : Blo 960589 962491 := bstep (se 1 (by rfl) ⟨721868, by rfl⟩ : syracuseStep 962491 = 1443737) B1443737
theorem B962567 : Blo 960589 962567 := bstep (se 1 (by rfl) ⟨721925, by rfl⟩ : syracuseStep 962567 = 1443851) B1443851
theorem B962575 : Blo 960589 962575 := bstep (se 1 (by rfl) ⟨721931, by rfl⟩ : syracuseStep 962575 = 1443863) B1443863
theorem B962619 : Blo 960589 962619 := bstep (se 1 (by rfl) ⟨721964, by rfl⟩ : syracuseStep 962619 = 1443929) B1443929
theorem B5484631 : Blo 960589 5484631 := bstep (se 1 (by rfl) ⟨4113473, by rfl⟩ : syracuseStep 5484631 = 8226947) B8226947
theorem B962695 : Blo 960589 962695 := bstep (se 1 (by rfl) ⟨722021, by rfl⟩ : syracuseStep 962695 = 1444043) B1444043
theorem B962703 : Blo 960589 962703 := bstep (se 1 (by rfl) ⟨722027, by rfl⟩ : syracuseStep 962703 = 1444055) B1444055
theorem B962747 : Blo 960589 962747 := bstep (se 1 (by rfl) ⟨722060, by rfl⟩ : syracuseStep 962747 = 1444121) B1444121
theorem B962823 : Blo 960589 962823 := bstep (se 1 (by rfl) ⟨722117, by rfl⟩ : syracuseStep 962823 = 1444235) B1444235
theorem B962831 : Blo 960589 962831 := bstep (se 1 (by rfl) ⟨722123, by rfl⟩ : syracuseStep 962831 = 1444247) B1444247
theorem B2437391 : Blo 960589 2437391 := bstep (se 1 (by rfl) ⟨1828043, by rfl⟩ : syracuseStep 2437391 = 3656087) B3656087
theorem B962875 : Blo 960589 962875 := bstep (se 1 (by rfl) ⟨722156, by rfl⟩ : syracuseStep 962875 = 1444313) B1444313
theorem B962951 : Blo 960589 962951 := bstep (se 1 (by rfl) ⟨722213, by rfl⟩ : syracuseStep 962951 = 1444427) B1444427
theorem B962959 : Blo 960589 962959 := bstep (se 1 (by rfl) ⟨722219, by rfl⟩ : syracuseStep 962959 = 1444439) B1444439
theorem B2437523 : Blo 960589 2437523 := bstep (se 1 (by rfl) ⟨1828142, by rfl⟩ : syracuseStep 2437523 = 3656285) B3656285
theorem B963003 : Blo 960589 963003 := bstep (se 1 (by rfl) ⟨722252, by rfl⟩ : syracuseStep 963003 = 1444505) B1444505
theorem B963079 : Blo 960589 963079 := bstep (se 1 (by rfl) ⟨722309, by rfl⟩ : syracuseStep 963079 = 1444619) B1444619
theorem B963087 : Blo 960589 963087 := bstep (se 1 (by rfl) ⟨722315, by rfl⟩ : syracuseStep 963087 = 1444631) B1444631
theorem B963131 : Blo 960589 963131 := bstep (se 1 (by rfl) ⟨722348, by rfl⟩ : syracuseStep 963131 = 1444697) B1444697
theorem B7320131 : Blo 960589 7320131 := bstep (se 1 (by rfl) ⟨5490098, by rfl⟩ : syracuseStep 7320131 = 10980197) B10980197
theorem B963207 : Blo 960589 963207 := bstep (se 1 (by rfl) ⟨722405, by rfl⟩ : syracuseStep 963207 = 1444811) B1444811
theorem B963215 : Blo 960589 963215 := bstep (se 1 (by rfl) ⟨722411, by rfl⟩ : syracuseStep 963215 = 1444823) B1444823
theorem B963259 : Blo 960589 963259 := bstep (se 1 (by rfl) ⟨722444, by rfl⟩ : syracuseStep 963259 = 1444889) B1444889
theorem B8794817 : Blo 960589 8794817 := bstep (se 2 (by rfl) ⟨3298056, by rfl⟩ : syracuseStep 8794817 = 6596113) B6596113
theorem B3650285 : Blo 960589 3650285 := bstep (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) B1368857
theorem B963335 : Blo 960589 963335 := bstep (se 1 (by rfl) ⟨722501, by rfl⟩ : syracuseStep 963335 = 1445003) B1445003
theorem B963343 : Blo 960589 963343 := bstep (se 1 (by rfl) ⟨722507, by rfl⟩ : syracuseStep 963343 = 1445015) B1445015
theorem B6173491 : Blo 960589 6173491 := bstep (se 1 (by rfl) ⟨4630118, by rfl⟩ : syracuseStep 6173491 = 9260237) B9260237
theorem B963387 : Blo 960589 963387 := bstep (se 1 (by rfl) ⟨722540, by rfl⟩ : syracuseStep 963387 = 1445081) B1445081
theorem B963463 : Blo 960589 963463 := bstep (se 1 (by rfl) ⟨722597, by rfl⟩ : syracuseStep 963463 = 1445195) B1445195
theorem B963471 : Blo 960589 963471 := bstep (se 1 (by rfl) ⟨722603, by rfl⟩ : syracuseStep 963471 = 1445207) B1445207
theorem B963515 : Blo 960589 963515 := bstep (se 1 (by rfl) ⟨722636, by rfl⟩ : syracuseStep 963515 = 1445273) B1445273
theorem B963591 : Blo 960589 963591 := bstep (se 1 (by rfl) ⟨722693, by rfl⟩ : syracuseStep 963591 = 1445387) B1445387
theorem B963599 : Blo 960589 963599 := bstep (se 1 (by rfl) ⟨722699, by rfl⟩ : syracuseStep 963599 = 1445399) B1445399
theorem B963643 : Blo 960589 963643 := bstep (se 1 (by rfl) ⟨722732, by rfl⟩ : syracuseStep 963643 = 1445465) B1445465
theorem B963719 : Blo 960589 963719 := bstep (se 1 (by rfl) ⟨722789, by rfl⟩ : syracuseStep 963719 = 1445579) B1445579
theorem B963727 : Blo 960589 963727 := bstep (se 1 (by rfl) ⟨722795, by rfl⟩ : syracuseStep 963727 = 1445591) B1445591
theorem B963771 : Blo 960589 963771 := bstep (se 1 (by rfl) ⟨722828, by rfl⟩ : syracuseStep 963771 = 1445657) B1445657
theorem B963847 : Blo 960589 963847 := bstep (se 1 (by rfl) ⟨722885, by rfl⟩ : syracuseStep 963847 = 1445771) B1445771
theorem B963855 : Blo 960589 963855 := bstep (se 1 (by rfl) ⟨722891, by rfl⟩ : syracuseStep 963855 = 1445783) B1445783
theorem B963899 : Blo 960589 963899 := bstep (se 1 (by rfl) ⟨722924, by rfl⟩ : syracuseStep 963899 = 1445849) B1445849
theorem B963975 : Blo 960589 963975 := bstep (se 1 (by rfl) ⟨722981, by rfl⟩ : syracuseStep 963975 = 1445963) B1445963
theorem B963983 : Blo 960589 963983 := bstep (se 1 (by rfl) ⟨722987, by rfl⟩ : syracuseStep 963983 = 1445975) B1445975
theorem B4634003 : Blo 960589 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B964027 : Blo 960589 964027 := bstep (se 1 (by rfl) ⟨723020, by rfl⟩ : syracuseStep 964027 = 1446041) B1446041
theorem B2438657 : Blo 960589 2438657 := bstep (se 2 (by rfl) ⟨914496, by rfl⟩ : syracuseStep 2438657 = 1828993) B1828993
theorem B964103 : Blo 960589 964103 := bstep (se 1 (by rfl) ⟨723077, by rfl⟩ : syracuseStep 964103 = 1446155) B1446155
theorem B964111 : Blo 960589 964111 := bstep (se 1 (by rfl) ⟨723083, by rfl⟩ : syracuseStep 964111 = 1446167) B1446167
theorem B964155 : Blo 960589 964155 := bstep (se 1 (by rfl) ⟨723116, by rfl⟩ : syracuseStep 964155 = 1446233) B1446233
theorem B5551703 : Blo 960589 5551703 := bstep (se 1 (by rfl) ⟨4163777, by rfl⟩ : syracuseStep 5551703 = 8327555) B8327555
theorem B964231 : Blo 960589 964231 := bstep (se 1 (by rfl) ⟨723173, by rfl⟩ : syracuseStep 964231 = 1446347) B1446347
theorem B964239 : Blo 960589 964239 := bstep (se 1 (by rfl) ⟨723179, by rfl⟩ : syracuseStep 964239 = 1446359) B1446359
theorem B964283 : Blo 960589 964283 := bstep (se 1 (by rfl) ⟨723212, by rfl⟩ : syracuseStep 964283 = 1446425) B1446425
theorem B4863725 : Blo 960589 4863725 := bstep (se 3 (by rfl) ⟨911948, by rfl⟩ : syracuseStep 4863725 = 1823897) B1823897
theorem B964359 : Blo 960589 964359 := bstep (se 1 (by rfl) ⟨723269, by rfl⟩ : syracuseStep 964359 = 1446539) B1446539
theorem B964367 : Blo 960589 964367 := bstep (se 1 (by rfl) ⟨723275, by rfl⟩ : syracuseStep 964367 = 1446551) B1446551
theorem B964411 : Blo 960589 964411 := bstep (se 1 (by rfl) ⟨723308, by rfl⟩ : syracuseStep 964411 = 1446617) B1446617
theorem B2439031 : Blo 960589 2439031 := bstep (se 1 (by rfl) ⟨1829273, by rfl⟩ : syracuseStep 2439031 = 3658547) B3658547
theorem B964487 : Blo 960589 964487 := bstep (se 1 (by rfl) ⟨723365, by rfl⟩ : syracuseStep 964487 = 1446731) B1446731
theorem B964495 : Blo 960589 964495 := bstep (se 1 (by rfl) ⟨723371, by rfl⟩ : syracuseStep 964495 = 1446743) B1446743
theorem B1095611 : Blo 960589 1095611 := bstep (se 1 (by rfl) ⟨821708, by rfl⟩ : syracuseStep 1095611 = 1643417) B1643417
theorem B964539 : Blo 960589 964539 := bstep (se 1 (by rfl) ⟨723404, by rfl⟩ : syracuseStep 964539 = 1446809) B1446809
theorem B5847005 : Blo 960589 5847005 := bstep (se 3 (by rfl) ⟨1096313, by rfl⟩ : syracuseStep 5847005 = 2192627) B2192627
theorem B5486615 : Blo 960589 5486615 := bstep (se 1 (by rfl) ⟨4114961, by rfl⟩ : syracuseStep 5486615 = 8229923) B8229923
theorem B4110365 : Blo 960589 4110365 := bstep (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) B1541387
theorem B2439467 : Blo 960589 2439467 := bstep (se 1 (by rfl) ⟨1829600, by rfl⟩ : syracuseStep 2439467 = 3659201) B3659201
theorem B2308439 : Blo 960589 2308439 := bstep (se 1 (by rfl) ⟨1731329, by rfl⟩ : syracuseStep 2308439 = 3462659) B3462659
theorem B1391033 : Blo 960589 1391033 := bstep (se 2 (by rfl) ⟨521637, by rfl⟩ : syracuseStep 1391033 = 1043275) B1043275
theorem B6928861 : Blo 960589 6928861 := bstep (se 3 (by rfl) ⟨1299161, by rfl⟩ : syracuseStep 6928861 = 2598323) B2598323
theorem B4864535 : Blo 960589 4864535 := bstep (se 1 (by rfl) ⟨3648401, by rfl⟩ : syracuseStep 4864535 = 7296803) B7296803
theorem B3652411 : Blo 960589 3652411 := bstep (se 1 (by rfl) ⟨2739308, by rfl⟩ : syracuseStep 3652411 = 5478617) B5478617
theorem B6241303 : Blo 960589 6241303 := bstep (se 1 (by rfl) ⟨4680977, by rfl⟩ : syracuseStep 6241303 = 9361955) B9361955
theorem B6929495 : Blo 960589 6929495 := bstep (se 1 (by rfl) ⟨5197121, by rfl⟩ : syracuseStep 6929495 = 10394243) B10394243
theorem B2440307 : Blo 960589 2440307 := bstep (se 1 (by rfl) ⟨1830230, by rfl⟩ : syracuseStep 2440307 = 3660461) B3660461
theorem B1621127 : Blo 960589 1621127 := bstep (se 1 (by rfl) ⟨1215845, by rfl⟩ : syracuseStep 1621127 = 2431691) B2431691
theorem B2440327 : Blo 960589 2440327 := bstep (se 1 (by rfl) ⟨1830245, by rfl⟩ : syracuseStep 2440327 = 3660491) B3660491
theorem B37043405 : Blo 960589 37043405 := bstep (se 3 (by rfl) ⟨6945638, by rfl⟩ : syracuseStep 37043405 = 13891277) B13891277
theorem B3652897 : Blo 960589 3652897 := bstep (se 2 (by rfl) ⟨1369836, by rfl⟩ : syracuseStep 3652897 = 2739673) B2739673
theorem B8207675 : Blo 960589 8207675 := bstep (se 1 (by rfl) ⟨6155756, by rfl⟩ : syracuseStep 8207675 = 12311513) B12311513
theorem B2440601 : Blo 960589 2440601 := bstep (se 2 (by rfl) ⟨915225, by rfl⟩ : syracuseStep 2440601 = 1830451) B1830451
theorem B17546705 : Blo 960589 17546705 := bstep (se 2 (by rfl) ⟨6580014, by rfl⟩ : syracuseStep 17546705 = 13160029) B13160029
theorem B6176209 : Blo 960589 6176209 := bstep (se 2 (by rfl) ⟨2316078, by rfl⟩ : syracuseStep 6176209 = 4632157) B4632157
theorem B1785359 : Blo 960589 1785359 := bstep (se 1 (by rfl) ⟨1339019, by rfl⟩ : syracuseStep 1785359 = 2678039) B2678039
theorem B2080289 : Blo 960589 2080289 := bstep (se 2 (by rfl) ⟨780108, by rfl⟩ : syracuseStep 2080289 = 1560217) B1560217
theorem B2440763 : Blo 960589 2440763 := bstep (se 1 (by rfl) ⟨1830572, by rfl⟩ : syracuseStep 2440763 = 3661145) B3661145
theorem B18497099 : Blo 960589 18497099 := bstep (se 1 (by rfl) ⟨13872824, by rfl⟩ : syracuseStep 18497099 = 27745649) B27745649
theorem B2735801 : Blo 960589 2735801 := bstep (se 2 (by rfl) ⟨1025925, by rfl⟩ : syracuseStep 2735801 = 2051851) B2051851
theorem B5193487 : Blo 960589 5193487 := bstep (se 1 (by rfl) ⟨3895115, by rfl⟩ : syracuseStep 5193487 = 7790231) B7790231
theorem B1621775 : Blo 960589 1621775 := bstep (se 1 (by rfl) ⟨1216331, by rfl⟩ : syracuseStep 1621775 = 2432663) B2432663
theorem B2440975 : Blo 960589 2440975 := bstep (se 1 (by rfl) ⟨1830731, by rfl⟩ : syracuseStep 2440975 = 3661463) B3661463
theorem B44384051 : Blo 960589 44384051 := bstep (se 1 (by rfl) ⟨33288038, by rfl⟩ : syracuseStep 44384051 = 66576077) B66576077
theorem B2604919 : Blo 960589 2604919 := bstep (se 1 (by rfl) ⟨1953689, by rfl⟩ : syracuseStep 2604919 = 3907379) B3907379
theorem B3293075 : Blo 960589 3293075 := bstep (se 1 (by rfl) ⟨2469806, by rfl⟩ : syracuseStep 3293075 = 4939613) B4939613
theorem B2736143 : Blo 960589 2736143 := bstep (se 1 (by rfl) ⟨2052107, by rfl⟩ : syracuseStep 2736143 = 4104215) B4104215
theorem B2441249 : Blo 960589 2441249 := bstep (se 2 (by rfl) ⟨915468, by rfl⟩ : syracuseStep 2441249 = 1830937) B1830937
theorem B9257161 : Blo 960589 9257161 := bstep (se 2 (by rfl) ⟨3471435, by rfl⟩ : syracuseStep 9257161 = 6942871) B6942871
theorem B3653869 : Blo 960589 3653869 := bstep (se 3 (by rfl) ⟨685100, by rfl⟩ : syracuseStep 3653869 = 1370201) B1370201
theorem B1622315 : Blo 960589 1622315 := bstep (se 1 (by rfl) ⟨1216736, by rfl⟩ : syracuseStep 1622315 = 2433473) B2433473
theorem B2310515 : Blo 960589 2310515 := bstep (se 1 (by rfl) ⟨1732886, by rfl⟩ : syracuseStep 2310515 = 3465773) B3465773
theorem B2474393 : Blo 960589 2474393 := bstep (se 2 (by rfl) ⟨927897, by rfl⟩ : syracuseStep 2474393 = 1855795) B1855795
theorem B3654173 : Blo 960589 3654173 := bstep (se 3 (by rfl) ⟨685157, by rfl⟩ : syracuseStep 3654173 = 1370315) B1370315
theorem B42254891 : Blo 960589 42254891 := bstep (se 1 (by rfl) ⟨31691168, by rfl⟩ : syracuseStep 42254891 = 63382337) B63382337
theorem B4112963 : Blo 960589 4112963 := bstep (se 1 (by rfl) ⟨3084722, by rfl⟩ : syracuseStep 4112963 = 6169445) B6169445
theorem B1622713 : Blo 960589 1622713 := bstep (se 2 (by rfl) ⟨608517, by rfl⟩ : syracuseStep 1622713 = 1217035) B1217035
theorem B2474753 : Blo 960589 2474753 := bstep (se 2 (by rfl) ⟨928032, by rfl⟩ : syracuseStep 2474753 = 1856065) B1856065
theorem B2736929 : Blo 960589 2736929 := bstep (se 2 (by rfl) ⟨1026348, by rfl⟩ : syracuseStep 2736929 = 2052697) B2052697
theorem B9257777 : Blo 960589 9257777 := bstep (se 2 (by rfl) ⟨3471666, by rfl⟩ : syracuseStep 9257777 = 6943333) B6943333
theorem B7324505 : Blo 960589 7324505 := bstep (se 2 (by rfl) ⟨2746689, by rfl⟩ : syracuseStep 7324505 = 5493379) B5493379
theorem B4113337 : Blo 960589 4113337 := bstep (se 2 (by rfl) ⟨1542501, by rfl⟩ : syracuseStep 4113337 = 3085003) B3085003
theorem B4113679 : Blo 960589 4113679 := bstep (se 1 (by rfl) ⟨3085259, by rfl⟩ : syracuseStep 4113679 = 6170519) B6170519
theorem B2082167 : Blo 960589 2082167 := bstep (se 1 (by rfl) ⟨1561625, by rfl⟩ : syracuseStep 2082167 = 3123251) B3123251
theorem B1623415 : Blo 960589 1623415 := bstep (se 1 (by rfl) ⟨1217561, by rfl⟩ : syracuseStep 1623415 = 2435123) B2435123
theorem B2115001 : Blo 960589 2115001 := bstep (se 2 (by rfl) ⟨793125, by rfl⟩ : syracuseStep 2115001 = 1586251) B1586251
theorem B4867613 : Blo 960589 4867613 := bstep (se 3 (by rfl) ⟨912677, by rfl⟩ : syracuseStep 4867613 = 1825355) B1825355
theorem B1623611 : Blo 960589 1623611 := bstep (se 1 (by rfl) ⟨1217708, by rfl⟩ : syracuseStep 1623611 = 2435417) B2435417
theorem B2606995 : Blo 960589 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B1624009 : Blo 960589 1624009 := bstep (se 2 (by rfl) ⟨609003, by rfl⟩ : syracuseStep 1624009 = 1218007) B1218007
theorem B4868099 : Blo 960589 4868099 := bstep (se 1 (by rfl) ⟨3651074, by rfl⟩ : syracuseStep 4868099 = 7302149) B7302149
theorem B3655799 : Blo 960589 3655799 := bstep (se 1 (by rfl) ⟨2741849, by rfl⟩ : syracuseStep 3655799 = 5483699) B5483699
theorem B2738443 : Blo 960589 2738443 := bstep (se 1 (by rfl) ⟨2053832, by rfl⟩ : syracuseStep 2738443 = 4107665) B4107665
theorem B15616273 : Blo 960589 15616273 := bstep (se 2 (by rfl) ⟨5856102, by rfl⟩ : syracuseStep 15616273 = 11712205) B11712205
theorem B2738717 : Blo 960589 2738717 := bstep (se 3 (by rfl) ⟨513509, by rfl⟩ : syracuseStep 2738717 = 1027019) B1027019
theorem B1624711 : Blo 960589 1624711 := bstep (se 1 (by rfl) ⟨1218533, by rfl⟩ : syracuseStep 1624711 = 2437067) B2437067
theorem B6933185 : Blo 960589 6933185 := bstep (se 2 (by rfl) ⟨2599944, by rfl⟩ : syracuseStep 6933185 = 5199889) B5199889
theorem B2312975 : Blo 960589 2312975 := bstep (se 1 (by rfl) ⟨1734731, by rfl⟩ : syracuseStep 2312975 = 3469463) B3469463
theorem B2739059 : Blo 960589 2739059 := bstep (se 1 (by rfl) ⟨2054294, by rfl⟩ : syracuseStep 2739059 = 4108589) B4108589
theorem B5196689 : Blo 960589 5196689 := bstep (se 2 (by rfl) ⟨1948758, by rfl⟩ : syracuseStep 5196689 = 3897517) B3897517
theorem B3656771 : Blo 960589 3656771 := bstep (se 1 (by rfl) ⟨2742578, by rfl⟩ : syracuseStep 3656771 = 5485157) B5485157
theorem B1625359 : Blo 960589 1625359 := bstep (se 1 (by rfl) ⟨1219019, by rfl⟩ : syracuseStep 1625359 = 2438039) B2438039
theorem B2346355 : Blo 960589 2346355 := bstep (se 1 (by rfl) ⟨1759766, by rfl⟩ : syracuseStep 2346355 = 3519533) B3519533
theorem B4869719 : Blo 960589 4869719 := bstep (se 1 (by rfl) ⟨3652289, by rfl⟩ : syracuseStep 4869719 = 7304579) B7304579
theorem B4116055 : Blo 960589 4116055 := bstep (se 1 (by rfl) ⟨3087041, by rfl⟩ : syracuseStep 4116055 = 6174083) B6174083
theorem B46845539 : Blo 960589 46845539 := bstep (se 1 (by rfl) ⟨35134154, by rfl⟩ : syracuseStep 46845539 = 70268309) B70268309
theorem B1625899 : Blo 960589 1625899 := bstep (se 1 (by rfl) ⟨1219424, by rfl⟩ : syracuseStep 1625899 = 2438849) B2438849
theorem B2740027 : Blo 960589 2740027 := bstep (se 1 (by rfl) ⟨2055020, by rfl⟩ : syracuseStep 2740027 = 4110041) B4110041
theorem B2314099 : Blo 960589 2314099 := bstep (se 1 (by rfl) ⟨1735574, by rfl⟩ : syracuseStep 2314099 = 3471149) B3471149
theorem B1626041 : Blo 960589 1626041 := bstep (se 2 (by rfl) ⟨609765, by rfl⟩ : syracuseStep 1626041 = 1219531) B1219531
theorem B1953721 : Blo 960589 1953721 := bstep (se 2 (by rfl) ⟨732645, by rfl⟩ : syracuseStep 1953721 = 1465291) B1465291
theorem B8212427 : Blo 960589 8212427 := bstep (se 1 (by rfl) ⟨6159320, by rfl⟩ : syracuseStep 8212427 = 12318641) B12318641
theorem B3657757 : Blo 960589 3657757 := bstep (se 3 (by rfl) ⟨685829, by rfl⟩ : syracuseStep 3657757 = 1371659) B1371659
theorem B4870205 : Blo 960589 4870205 := bstep (se 3 (by rfl) ⟨913163, by rfl⟩ : syracuseStep 4870205 = 1826327) B1826327
theorem B1298761 : Blo 960589 1298761 := bstep (se 2 (by rfl) ⟨487035, by rfl⟩ : syracuseStep 1298761 = 974071) B974071
theorem B1626743 : Blo 960589 1626743 := bstep (se 1 (by rfl) ⟨1220057, by rfl⟩ : syracuseStep 1626743 = 2440115) B2440115
theorem B2741177 : Blo 960589 2741177 := bstep (se 2 (by rfl) ⟨1027941, by rfl⟩ : syracuseStep 2741177 = 2055883) B2055883
theorem B1627195 : Blo 960589 1627195 := bstep (se 1 (by rfl) ⟨1220396, by rfl⟩ : syracuseStep 1627195 = 2440793) B2440793
theorem B1627337 : Blo 960589 1627337 := bstep (se 2 (by rfl) ⟨610251, by rfl⟩ : syracuseStep 1627337 = 1220503) B1220503
theorem B2741519 : Blo 960589 2741519 := bstep (se 1 (by rfl) ⟨2056139, by rfl⟩ : syracuseStep 2741519 = 4112279) B4112279
theorem B9491897 : Blo 960589 9491897 := bstep (se 2 (by rfl) ⟨3559461, by rfl⟩ : syracuseStep 9491897 = 7118923) B7118923
theorem B3298877 : Blo 960589 3298877 := bstep (se 3 (by rfl) ⟨618539, by rfl⟩ : syracuseStep 3298877 = 1237079) B1237079
theorem B17553125 : Blo 960589 17553125 := bstep (se 4 (by rfl) ⟨1645605, by rfl⟩ : syracuseStep 17553125 = 3291211) B3291211
theorem B4937473 : Blo 960589 4937473 := bstep (se 2 (by rfl) ⟨1851552, by rfl⟩ : syracuseStep 4937473 = 3703105) B3703105
theorem B4871987 : Blo 960589 4871987 := bstep (se 1 (by rfl) ⟨3653990, by rfl⟩ : syracuseStep 4871987 = 7307981) B7307981
theorem B1300297 : Blo 960589 1300297 := bstep (se 2 (by rfl) ⟨487611, by rfl⟩ : syracuseStep 1300297 = 975223) B975223
theorem B27121483 : Blo 960589 27121483 := bstep (se 1 (by rfl) ⟨20341112, by rfl⟩ : syracuseStep 27121483 = 40682225) B40682225
theorem B2054089 : Blo 960589 2054089 := bstep (se 2 (by rfl) ⟨770283, by rfl⟩ : syracuseStep 2054089 = 1540567) B1540567
theorem B18536465 : Blo 960589 18536465 := bstep (se 2 (by rfl) ⟨6951174, by rfl⟩ : syracuseStep 18536465 = 13902349) B13902349
theorem B4872311 : Blo 960589 4872311 := bstep (se 1 (by rfl) ⟨3654233, by rfl⟩ : syracuseStep 4872311 = 7308467) B7308467
theorem B2742407 : Blo 960589 2742407 := bstep (se 1 (by rfl) ⟨2056805, by rfl⟩ : syracuseStep 2742407 = 4113611) B4113611
theorem B13162769 : Blo 960589 13162769 := bstep (se 2 (by rfl) ⟨4936038, by rfl⟩ : syracuseStep 13162769 = 9872077) B9872077
theorem B1825067 : Blo 960589 1825067 := bstep (se 1 (by rfl) ⟨1368800, by rfl⟩ : syracuseStep 1825067 = 2737601) B2737601
theorem B2742589 : Blo 960589 2742589 := bstep (se 3 (by rfl) ⟨514235, by rfl⟩ : syracuseStep 2742589 = 1028471) B1028471
theorem B2054585 : Blo 960589 2054585 := bstep (se 2 (by rfl) ⟨770469, by rfl⟩ : syracuseStep 2054585 = 1540939) B1540939
theorem B2742817 : Blo 960589 2742817 := bstep (se 2 (by rfl) ⟨1028556, by rfl⟩ : syracuseStep 2742817 = 2057113) B2057113
theorem B3005185 : Blo 960589 3005185 := bstep (se 2 (by rfl) ⟨1126944, by rfl⟩ : syracuseStep 3005185 = 2253889) B2253889
theorem B1235719 : Blo 960589 1235719 := bstep (se 1 (by rfl) ⟨926789, by rfl⟩ : syracuseStep 1235719 = 1853579) B1853579
theorem B3660659 : Blo 960589 3660659 := bstep (se 1 (by rfl) ⟨2745494, by rfl⟩ : syracuseStep 3660659 = 5490989) B5490989
theorem B2743159 : Blo 960589 2743159 := bstep (se 1 (by rfl) ⟨2057369, by rfl⟩ : syracuseStep 2743159 = 4114739) B4114739
theorem B4873283 : Blo 960589 4873283 := bstep (se 1 (by rfl) ⟨3654962, by rfl⟩ : syracuseStep 4873283 = 7309925) B7309925
theorem B20831381 : Blo 960589 20831381 := bstep (se 6 (by rfl) ⟨488235, by rfl⟩ : syracuseStep 20831381 = 976471) B976471
theorem B1825993 : Blo 960589 1825993 := bstep (se 2 (by rfl) ⟨684747, by rfl⟩ : syracuseStep 1825993 = 1369495) B1369495
theorem B4873607 : Blo 960589 4873607 := bstep (se 1 (by rfl) ⟨3655205, by rfl⟩ : syracuseStep 4873607 = 7310411) B7310411
theorem B3464633 : Blo 960589 3464633 := bstep (se 2 (by rfl) ⟨1299237, by rfl⟩ : syracuseStep 3464633 = 2598475) B2598475
theorem B23420515 : Blo 960589 23420515 := bstep (se 1 (by rfl) ⟨17565386, by rfl⟩ : syracuseStep 23420515 = 35130773) B35130773
theorem B2744093 : Blo 960589 2744093 := bstep (se 3 (by rfl) ⟨514517, by rfl⟩ : syracuseStep 2744093 = 1029035) B1029035
theorem B9232217 : Blo 960589 9232217 := bstep (se 2 (by rfl) ⟨3462081, by rfl⟩ : syracuseStep 9232217 = 6924163) B6924163
theorem B1826707 : Blo 960589 1826707 := bstep (se 1 (by rfl) ⟨1370030, by rfl⟩ : syracuseStep 1826707 = 2740061) B2740061
theorem B2056225 : Blo 960589 2056225 := bstep (se 2 (by rfl) ⟨771084, by rfl⟩ : syracuseStep 2056225 = 1542169) B1542169
theorem B2744435 : Blo 960589 2744435 := bstep (se 1 (by rfl) ⟨2058326, by rfl⟩ : syracuseStep 2744435 = 4116653) B4116653
theorem B1368265 : Blo 960589 1368265 := bstep (se 2 (by rfl) ⟨513099, by rfl⟩ : syracuseStep 1368265 = 1026199) B1026199
theorem B2744891 : Blo 960589 2744891 := bstep (se 1 (by rfl) ⟨2058668, by rfl⟩ : syracuseStep 2744891 = 4117337) B4117337
theorem B2056823 : Blo 960589 2056823 := bstep (se 1 (by rfl) ⟨1542617, by rfl⟩ : syracuseStep 2056823 = 3085235) B3085235
theorem B22209395 : Blo 960589 22209395 := bstep (se 1 (by rfl) ⟨16657046, by rfl⟩ : syracuseStep 22209395 = 33314093) B33314093
theorem B1827785 : Blo 960589 1827785 := bstep (se 2 (by rfl) ⟨685419, by rfl⟩ : syracuseStep 1827785 = 1370839) B1370839
theorem B9266237 : Blo 960589 9266237 := bstep (se 3 (by rfl) ⟨1737419, by rfl⟩ : syracuseStep 9266237 = 3474839) B3474839
theorem B19785059 : Blo 960589 19785059 := bstep (se 1 (by rfl) ⟨14838794, by rfl⟩ : syracuseStep 19785059 = 29677589) B29677589
theorem B4384343 : Blo 960589 4384343 := bstep (se 1 (by rfl) ⟨3288257, by rfl⟩ : syracuseStep 4384343 = 6576515) B6576515
theorem B6022885 : Blo 960589 6022885 := bstep (se 4 (by rfl) ⟨564645, by rfl⟩ : syracuseStep 6022885 = 1129291) B1129291
theorem B1828651 : Blo 960589 1828651 := bstep (se 1 (by rfl) ⟨1371488, by rfl⟩ : syracuseStep 1828651 = 2742977) B2742977
theorem B976699 : Blo 960589 976699 := bstep (se 1 (by rfl) ⟨732524, by rfl⟩ : syracuseStep 976699 = 1465049) B1465049
theorem B1828727 : Blo 960589 1828727 := bstep (se 1 (by rfl) ⟨1371545, by rfl⟩ : syracuseStep 1828727 = 2743091) B2743091
theorem B10021495 : Blo 960589 10021495 := bstep (se 1 (by rfl) ⟨7516121, by rfl⟩ : syracuseStep 10021495 = 15032243) B15032243
theorem B8776421 : Blo 960589 8776421 := bstep (se 4 (by rfl) ⟨822789, by rfl⟩ : syracuseStep 8776421 = 1645579) B1645579
theorem B1370953 : Blo 960589 1370953 := bstep (se 2 (by rfl) ⟨514107, by rfl⟩ : syracuseStep 1370953 = 1028215) B1028215
theorem B4877171 : Blo 960589 4877171 := bstep (se 1 (by rfl) ⟨3657878, by rfl⟩ : syracuseStep 4877171 = 7315757) B7315757
theorem B11725829 : Blo 960589 11725829 := bstep (se 4 (by rfl) ⟨1099296, by rfl⟩ : syracuseStep 11725829 = 2198593) B2198593
theorem B4877657 : Blo 960589 4877657 := bstep (se 2 (by rfl) ⟨1829121, by rfl⟩ : syracuseStep 4877657 = 3658243) B3658243
theorem B8220113 : Blo 960589 8220113 := bstep (se 2 (by rfl) ⟨3082542, by rfl⟩ : syracuseStep 8220113 = 6165085) B6165085
theorem B1830671 : Blo 960589 1830671 := bstep (se 1 (by rfl) ⟨1373003, by rfl⟩ : syracuseStep 1830671 = 2746007) B2746007
theorem B4878139 : Blo 960589 4878139 := bstep (se 1 (by rfl) ⟨3658604, by rfl⟩ : syracuseStep 4878139 = 7317209) B7317209
theorem B6942617 : Blo 960589 6942617 := bstep (se 2 (by rfl) ⟨2603481, by rfl⟩ : syracuseStep 6942617 = 5206963) B5206963
theorem B4616203 : Blo 960589 4616203 := bstep (se 1 (by rfl) ⟨3462152, by rfl⟩ : syracuseStep 4616203 = 6924305) B6924305
theorem B4616279 : Blo 960589 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B4452893 : Blo 960589 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B4879763 : Blo 960589 4879763 := bstep (se 1 (by rfl) ⟨3659822, by rfl⟩ : syracuseStep 4879763 = 7319645) B7319645
theorem B2192939 : Blo 960589 2192939 := bstep (se 1 (by rfl) ⟨1644704, by rfl⟩ : syracuseStep 2192939 = 3289409) B3289409
theorem B4388413 : Blo 960589 4388413 := bstep (se 3 (by rfl) ⟨822827, by rfl⟩ : syracuseStep 4388413 = 1645655) B1645655
theorem B5273207 : Blo 960589 5273207 := bstep (se 1 (by rfl) ⟨3954905, by rfl⟩ : syracuseStep 5273207 = 7909811) B7909811
theorem B1111739 : Blo 960589 1111739 := bstep (se 1 (by rfl) ⟨833804, by rfl⟩ : syracuseStep 1111739 = 1667609) B1667609
theorem B2193211 : Blo 960589 2193211 := bstep (se 1 (by rfl) ⟨1644908, by rfl⟩ : syracuseStep 2193211 = 3289817) B3289817
theorem B2783243 : Blo 960589 2783243 := bstep (se 1 (by rfl) ⟨2087432, by rfl⟩ : syracuseStep 2783243 = 4174865) B4174865
theorem B20051981 : Blo 960589 20051981 := bstep (se 3 (by rfl) ⟨3759746, by rfl⟩ : syracuseStep 20051981 = 7519493) B7519493
theorem B3078263 : Blo 960589 3078263 := bstep (se 1 (by rfl) ⟨2308697, by rfl⟩ : syracuseStep 3078263 = 4617395) B4617395
theorem B26343697 : Blo 960589 26343697 := bstep (se 2 (by rfl) ⟨9878886, by rfl⟩ : syracuseStep 26343697 = 19757773) B19757773
theorem B5208409 : Blo 960589 5208409 := bstep (se 2 (by rfl) ⟨1953153, by rfl⟩ : syracuseStep 5208409 = 3906307) B3906307
theorem B3242375 : Blo 960589 3242375 := bstep (se 1 (by rfl) ⟨2431781, by rfl⟩ : syracuseStep 3242375 = 4863563) B4863563
theorem B10418807 : Blo 960589 10418807 := bstep (se 1 (by rfl) ⟨7814105, by rfl⟩ : syracuseStep 10418807 = 15628211) B15628211
theorem B3242753 : Blo 960589 3242753 := bstep (se 2 (by rfl) ⟨1216032, by rfl⟩ : syracuseStep 3242753 = 2432065) B2432065
theorem B5471009 : Blo 960589 5471009 := bstep (se 2 (by rfl) ⟨2051628, by rfl⟩ : syracuseStep 5471009 = 4103257) B4103257
theorem B1440887 : Blo 960589 1440887 := bstep (se 1 (by rfl) ⟨1080665, by rfl⟩ : syracuseStep 1440887 = 2161331) B2161331
theorem B2161799 : Blo 960589 2161799 := bstep (se 1 (by rfl) ⟨1621349, by rfl⟩ : syracuseStep 2161799 = 3242699) B3242699
theorem B1440911 : Blo 960589 1440911 := bstep (se 1 (by rfl) ⟨1080683, by rfl⟩ : syracuseStep 1440911 = 2161367) B2161367
theorem B1440953 : Blo 960589 1440953 := bstep (se 2 (by rfl) ⟨540357, by rfl⟩ : syracuseStep 1440953 = 1080715) B1080715
theorem B1441031 : Blo 960589 1441031 := bstep (se 1 (by rfl) ⟨1080773, by rfl⟩ : syracuseStep 1441031 = 2161547) B2161547
theorem B1441067 : Blo 960589 1441067 := bstep (se 1 (by rfl) ⟨1080800, by rfl⟩ : syracuseStep 1441067 = 2161601) B2161601
theorem B2161979 : Blo 960589 2161979 := bstep (se 1 (by rfl) ⟨1621484, by rfl⟩ : syracuseStep 2161979 = 3242969) B3242969
theorem B1441097 : Blo 960589 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B10419587 : Blo 960589 10419587 := bstep (se 1 (by rfl) ⟨7814690, by rfl⟩ : syracuseStep 10419587 = 15629381) B15629381
theorem B9239939 : Blo 960589 9239939 := bstep (se 1 (by rfl) ⟨6929954, by rfl⟩ : syracuseStep 9239939 = 13859909) B13859909
theorem B3079559 : Blo 960589 3079559 := bstep (se 1 (by rfl) ⟨2309669, by rfl⟩ : syracuseStep 3079559 = 4619339) B4619339
theorem B2162105 : Blo 960589 2162105 := bstep (se 2 (by rfl) ⟨810789, by rfl⟩ : syracuseStep 2162105 = 1621579) B1621579
theorem B1441211 : Blo 960589 1441211 := bstep (se 1 (by rfl) ⟨1080908, by rfl⟩ : syracuseStep 1441211 = 2161817) B2161817
theorem B1441271 : Blo 960589 1441271 := bstep (se 1 (by rfl) ⟨1080953, by rfl⟩ : syracuseStep 1441271 = 2161907) B2161907
theorem B6946307 : Blo 960589 6946307 := bstep (se 1 (by rfl) ⟨5209730, by rfl⟩ : syracuseStep 6946307 = 10419461) B10419461
theorem B1441295 : Blo 960589 1441295 := bstep (se 1 (by rfl) ⟨1080971, by rfl⟩ : syracuseStep 1441295 = 2161943) B2161943
theorem B3243563 : Blo 960589 3243563 := bstep (se 1 (by rfl) ⟨2432672, by rfl⟩ : syracuseStep 3243563 = 4865345) B4865345
theorem B1441337 : Blo 960589 1441337 := bstep (se 2 (by rfl) ⟨540501, by rfl⟩ : syracuseStep 1441337 = 1081003) B1081003
theorem B1080967 : Blo 960589 1080967 := bstep (se 1 (by rfl) ⟨810725, by rfl⟩ : syracuseStep 1080967 = 1621451) B1621451
theorem B1441415 : Blo 960589 1441415 := bstep (se 1 (by rfl) ⟨1081061, by rfl⟩ : syracuseStep 1441415 = 2162123) B2162123
theorem B1441451 : Blo 960589 1441451 := bstep (se 1 (by rfl) ⟨1081088, by rfl⟩ : syracuseStep 1441451 = 2162177) B2162177
theorem B1441481 : Blo 960589 1441481 := bstep (se 2 (by rfl) ⟨540555, by rfl⟩ : syracuseStep 1441481 = 1081111) B1081111
theorem B7307009 : Blo 960589 7307009 := bstep (se 2 (by rfl) ⟨2740128, by rfl⟩ : syracuseStep 7307009 = 5480257) B5480257
theorem B2162447 : Blo 960589 2162447 := bstep (se 1 (by rfl) ⟨1621835, by rfl⟩ : syracuseStep 2162447 = 3243671) B3243671
theorem B2162465 : Blo 960589 2162465 := bstep (se 2 (by rfl) ⟨810924, by rfl⟩ : syracuseStep 2162465 = 1621849) B1621849
theorem B1081147 : Blo 960589 1081147 := bstep (se 1 (by rfl) ⟨810860, by rfl⟩ : syracuseStep 1081147 = 1621721) B1621721
theorem B1441595 : Blo 960589 1441595 := bstep (se 1 (by rfl) ⟨1081196, by rfl⟩ : syracuseStep 1441595 = 2162393) B2162393
theorem B1441655 : Blo 960589 1441655 := bstep (se 1 (by rfl) ⟨1081241, by rfl⟩ : syracuseStep 1441655 = 2162483) B2162483
theorem B1441679 : Blo 960589 1441679 := bstep (se 1 (by rfl) ⟨1081259, by rfl⟩ : syracuseStep 1441679 = 2162519) B2162519
theorem B1441721 : Blo 960589 1441721 := bstep (se 2 (by rfl) ⟨540645, by rfl⟩ : syracuseStep 1441721 = 1081291) B1081291
theorem B1441871 : Blo 960589 1441871 := bstep (se 1 (by rfl) ⟨1081403, by rfl⟩ : syracuseStep 1441871 = 2162807) B2162807
theorem B1441991 : Blo 960589 1441991 := bstep (se 1 (by rfl) ⟨1081493, by rfl⟩ : syracuseStep 1441991 = 2162987) B2162987
theorem B1081543 : Blo 960589 1081543 := bstep (se 1 (by rfl) ⟨811157, by rfl⟩ : syracuseStep 1081543 = 1622315) B1622315
theorem B1540343 : Blo 960589 1540343 := bstep (se 1 (by rfl) ⟨1155257, by rfl⟩ : syracuseStep 1540343 = 2310515) B2310515
theorem B1442153 : Blo 960589 1442153 := bstep (se 2 (by rfl) ⟨540807, by rfl⟩ : syracuseStep 1442153 = 1081615) B1081615
theorem B1442231 : Blo 960589 1442231 := bstep (se 1 (by rfl) ⟨1081673, by rfl⟩ : syracuseStep 1442231 = 2163347) B2163347
theorem B1442267 : Blo 960589 1442267 := bstep (se 1 (by rfl) ⟨1081700, by rfl⟩ : syracuseStep 1442267 = 2163401) B2163401
theorem B2163239 : Blo 960589 2163239 := bstep (se 1 (by rfl) ⟨1622429, by rfl⟩ : syracuseStep 2163239 = 3244859) B3244859
theorem B4883003 : Blo 960589 4883003 := bstep (se 1 (by rfl) ⟨3662252, by rfl⟩ : syracuseStep 4883003 = 7324505) B7324505
theorem B2163563 : Blo 960589 2163563 := bstep (se 1 (by rfl) ⟨1622672, by rfl⟩ : syracuseStep 2163563 = 3245345) B3245345
theorem B2163617 : Blo 960589 2163617 := bstep (se 2 (by rfl) ⟨811356, by rfl⟩ : syracuseStep 2163617 = 1622713) B1622713
theorem B1442735 : Blo 960589 1442735 := bstep (se 1 (by rfl) ⟨1082051, by rfl⟩ : syracuseStep 1442735 = 2164103) B2164103
theorem B1442825 : Blo 960589 1442825 := bstep (se 2 (by rfl) ⟨541059, by rfl⟩ : syracuseStep 1442825 = 1082119) B1082119
theorem B3245075 : Blo 960589 3245075 := bstep (se 1 (by rfl) ⟨2433806, by rfl⟩ : syracuseStep 3245075 = 4867613) B4867613
theorem B1442855 : Blo 960589 1442855 := bstep (se 1 (by rfl) ⟨1082141, by rfl⟩ : syracuseStep 1442855 = 2164283) B2164283
theorem B1082407 : Blo 960589 1082407 := bstep (se 1 (by rfl) ⟨811805, by rfl⟩ : syracuseStep 1082407 = 1623611) B1623611
theorem B1442939 : Blo 960589 1442939 := bstep (se 1 (by rfl) ⟨1082204, by rfl⟩ : syracuseStep 1442939 = 2164409) B2164409
theorem B2163959 : Blo 960589 2163959 := bstep (se 1 (by rfl) ⟨1622969, by rfl⟩ : syracuseStep 2163959 = 3245939) B3245939
theorem B1443065 : Blo 960589 1443065 := bstep (se 2 (by rfl) ⟨541149, by rfl⟩ : syracuseStep 1443065 = 1082299) B1082299
theorem B3245399 : Blo 960589 3245399 := bstep (se 1 (by rfl) ⟨2434049, by rfl⟩ : syracuseStep 3245399 = 4868099) B4868099
theorem B1443167 : Blo 960589 1443167 := bstep (se 1 (by rfl) ⟨1082375, by rfl⟩ : syracuseStep 1443167 = 2164751) B2164751
theorem B1443179 : Blo 960589 1443179 := bstep (se 1 (by rfl) ⟨1082384, by rfl⟩ : syracuseStep 1443179 = 2164769) B2164769
theorem B24643115 : Blo 960589 24643115 := bstep (se 1 (by rfl) ⟨18482336, by rfl⟩ : syracuseStep 24643115 = 36964673) B36964673
theorem B1443407 : Blo 960589 1443407 := bstep (se 1 (by rfl) ⟨1082555, by rfl⟩ : syracuseStep 1443407 = 2165111) B2165111
theorem B1443527 : Blo 960589 1443527 := bstep (se 1 (by rfl) ⟨1082645, by rfl⟩ : syracuseStep 1443527 = 2165291) B2165291
theorem B4622123 : Blo 960589 4622123 := bstep (se 1 (by rfl) ⟨3466592, by rfl⟩ : syracuseStep 4622123 = 6933185) B6933185
theorem B2164553 : Blo 960589 2164553 := bstep (se 2 (by rfl) ⟨811707, by rfl⟩ : syracuseStep 2164553 = 1623415) B1623415
theorem B1443689 : Blo 960589 1443689 := bstep (se 2 (by rfl) ⟨541383, by rfl⟩ : syracuseStep 1443689 = 1082767) B1082767
theorem B1443767 : Blo 960589 1443767 := bstep (se 1 (by rfl) ⟨1082825, by rfl⟩ : syracuseStep 1443767 = 2165651) B2165651
theorem B1443803 : Blo 960589 1443803 := bstep (se 1 (by rfl) ⟨1082852, by rfl⟩ : syracuseStep 1443803 = 2165705) B2165705
theorem B8030513 : Blo 960589 8030513 := bstep (se 2 (by rfl) ⟨3011442, by rfl⟩ : syracuseStep 8030513 = 6022885) B6022885
theorem B3246479 : Blo 960589 3246479 := bstep (se 1 (by rfl) ⟨2434859, by rfl⟩ : syracuseStep 3246479 = 4869719) B4869719
theorem B31230359 : Blo 960589 31230359 := bstep (se 1 (by rfl) ⟨23422769, by rfl⟩ : syracuseStep 31230359 = 46845539) B46845539
theorem B1444271 : Blo 960589 1444271 := bstep (se 1 (by rfl) ⟨1083203, by rfl⟩ : syracuseStep 1444271 = 2166407) B2166407
theorem B1444361 : Blo 960589 1444361 := bstep (se 2 (by rfl) ⟨541635, by rfl⟩ : syracuseStep 1444361 = 1083271) B1083271
theorem B3475993 : Blo 960589 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B1444391 : Blo 960589 1444391 := bstep (se 1 (by rfl) ⟨1083293, by rfl⟩ : syracuseStep 1444391 = 2166587) B2166587
theorem B2165345 : Blo 960589 2165345 := bstep (se 2 (by rfl) ⟨812004, by rfl⟩ : syracuseStep 2165345 = 1624009) B1624009
theorem B1444475 : Blo 960589 1444475 := bstep (se 1 (by rfl) ⟨1083356, by rfl⟩ : syracuseStep 1444475 = 2166713) B2166713
theorem B1084027 : Blo 960589 1084027 := bstep (se 1 (by rfl) ⟨813020, by rfl⟩ : syracuseStep 1084027 = 1626041) B1626041
theorem B5474951 : Blo 960589 5474951 := bstep (se 1 (by rfl) ⟨4106213, by rfl⟩ : syracuseStep 5474951 = 8212427) B8212427
theorem B3246803 : Blo 960589 3246803 := bstep (se 1 (by rfl) ⟨2435102, by rfl⟩ : syracuseStep 3246803 = 4870205) B4870205
theorem B1444601 : Blo 960589 1444601 := bstep (se 2 (by rfl) ⟨541725, by rfl⟩ : syracuseStep 1444601 = 1083451) B1083451
theorem B1444703 : Blo 960589 1444703 := bstep (se 1 (by rfl) ⟨1083527, by rfl⟩ : syracuseStep 1444703 = 2167055) B2167055
theorem B1444715 : Blo 960589 1444715 := bstep (se 1 (by rfl) ⟨1083536, by rfl⟩ : syracuseStep 1444715 = 2167073) B2167073
theorem B2165687 : Blo 960589 2165687 := bstep (se 1 (by rfl) ⟨1624265, by rfl⟩ : syracuseStep 2165687 = 3248531) B3248531
theorem B1444943 : Blo 960589 1444943 := bstep (se 1 (by rfl) ⟨1083707, by rfl⟩ : syracuseStep 1444943 = 2167415) B2167415
theorem B1084495 : Blo 960589 1084495 := bstep (se 1 (by rfl) ⟨813371, by rfl⟩ : syracuseStep 1084495 = 1626743) B1626743
theorem B1445063 : Blo 960589 1445063 := bstep (se 1 (by rfl) ⟨1083797, by rfl⟩ : syracuseStep 1445063 = 2167595) B2167595
theorem B9375011 : Blo 960589 9375011 := bstep (se 1 (by rfl) ⟨7031258, by rfl⟩ : syracuseStep 9375011 = 14062517) B14062517
theorem B1445225 : Blo 960589 1445225 := bstep (se 2 (by rfl) ⟨541959, by rfl⟩ : syracuseStep 1445225 = 1083919) B1083919
theorem B1445303 : Blo 960589 1445303 := bstep (se 1 (by rfl) ⟨1083977, by rfl⟩ : syracuseStep 1445303 = 2167955) B2167955
theorem B1445339 : Blo 960589 1445339 := bstep (se 1 (by rfl) ⟨1084004, by rfl⟩ : syracuseStep 1445339 = 2168009) B2168009
theorem B1084891 : Blo 960589 1084891 := bstep (se 1 (by rfl) ⟨813668, by rfl⟩ : syracuseStep 1084891 = 1627337) B1627337
theorem B2166281 : Blo 960589 2166281 := bstep (se 2 (by rfl) ⟨812355, by rfl⟩ : syracuseStep 2166281 = 1624711) B1624711
theorem B6327931 : Blo 960589 6327931 := bstep (se 1 (by rfl) ⟨4745948, by rfl⟩ : syracuseStep 6327931 = 9491897) B9491897
theorem B2199251 : Blo 960589 2199251 := bstep (se 1 (by rfl) ⟨1649438, by rfl⟩ : syracuseStep 2199251 = 3298877) B3298877
theorem B5213945 : Blo 960589 5213945 := bstep (se 2 (by rfl) ⟨1955229, by rfl⟩ : syracuseStep 5213945 = 3910459) B3910459
theorem B11702083 : Blo 960589 11702083 := bstep (se 1 (by rfl) ⟨8776562, by rfl⟩ : syracuseStep 11702083 = 17553125) B17553125
theorem B2166623 : Blo 960589 2166623 := bstep (se 1 (by rfl) ⟨1624967, by rfl⟩ : syracuseStep 2166623 = 3249935) B3249935
theorem B3247991 : Blo 960589 3247991 := bstep (se 1 (by rfl) ⟨2435993, by rfl⟩ : syracuseStep 3247991 = 4871987) B4871987
theorem B1445807 : Blo 960589 1445807 := bstep (se 1 (by rfl) ⟨1084355, by rfl⟩ : syracuseStep 1445807 = 2168711) B2168711
theorem B1445897 : Blo 960589 1445897 := bstep (se 2 (by rfl) ⟨542211, by rfl⟩ : syracuseStep 1445897 = 1084423) B1084423
theorem B12357643 : Blo 960589 12357643 := bstep (se 1 (by rfl) ⟨9268232, by rfl⟩ : syracuseStep 12357643 = 18536465) B18536465
theorem B2166803 : Blo 960589 2166803 := bstep (se 1 (by rfl) ⟨1625102, by rfl⟩ : syracuseStep 2166803 = 3250205) B3250205
theorem B1445927 : Blo 960589 1445927 := bstep (se 1 (by rfl) ⟨1084445, by rfl⟩ : syracuseStep 1445927 = 2168891) B2168891
theorem B5476409 : Blo 960589 5476409 := bstep (se 2 (by rfl) ⟨2053653, by rfl⟩ : syracuseStep 5476409 = 4107307) B4107307
theorem B3248207 : Blo 960589 3248207 := bstep (se 1 (by rfl) ⟨2436155, by rfl⟩ : syracuseStep 3248207 = 4872311) B4872311
theorem B1446011 : Blo 960589 1446011 := bstep (se 1 (by rfl) ⟨1084508, by rfl⟩ : syracuseStep 1446011 = 2169017) B2169017
theorem B1216711 : Blo 960589 1216711 := bstep (se 1 (by rfl) ⟨912533, by rfl⟩ : syracuseStep 1216711 = 1825067) B1825067
theorem B1446137 : Blo 960589 1446137 := bstep (se 2 (by rfl) ⟨542301, by rfl⟩ : syracuseStep 1446137 = 1084603) B1084603
theorem B1446239 : Blo 960589 1446239 := bstep (se 1 (by rfl) ⟨1084679, by rfl⟩ : syracuseStep 1446239 = 2169359) B2169359
theorem B2167145 : Blo 960589 2167145 := bstep (se 2 (by rfl) ⟨812679, by rfl⟩ : syracuseStep 2167145 = 1625359) B1625359
theorem B1446251 : Blo 960589 1446251 := bstep (se 1 (by rfl) ⟨1084688, by rfl⟩ : syracuseStep 1446251 = 2169377) B2169377
theorem B3248585 : Blo 960589 3248585 := bstep (se 2 (by rfl) ⟨1218219, by rfl⟩ : syracuseStep 3248585 = 2436439) B2436439
theorem B1446479 : Blo 960589 1446479 := bstep (se 1 (by rfl) ⟨1084859, by rfl⟩ : syracuseStep 1446479 = 2169719) B2169719
theorem B1446599 : Blo 960589 1446599 := bstep (se 1 (by rfl) ⟨1084949, by rfl⟩ : syracuseStep 1446599 = 2169899) B2169899
theorem B3248855 : Blo 960589 3248855 := bstep (se 1 (by rfl) ⟨2436641, by rfl⟩ : syracuseStep 3248855 = 4873283) B4873283
theorem B1446761 : Blo 960589 1446761 := bstep (se 2 (by rfl) ⟨542535, by rfl⟩ : syracuseStep 1446761 = 1085071) B1085071
theorem B1545065 : Blo 960589 1545065 := bstep (se 2 (by rfl) ⟨579399, by rfl⟩ : syracuseStep 1545065 = 1158799) B1158799
theorem B6165395 : Blo 960589 6165395 := bstep (se 1 (by rfl) ⟨4624046, by rfl⟩ : syracuseStep 6165395 = 9248093) B9248093
theorem B3249071 : Blo 960589 3249071 := bstep (se 1 (by rfl) ⟨2436803, by rfl⟩ : syracuseStep 3249071 = 4873607) B4873607
theorem B1446839 : Blo 960589 1446839 := bstep (se 1 (by rfl) ⟨1085129, by rfl⟩ : syracuseStep 1446839 = 2170259) B2170259
theorem B2167739 : Blo 960589 2167739 := bstep (se 1 (by rfl) ⟨1625804, by rfl⟩ : syracuseStep 2167739 = 3251609) B3251609
theorem B1446875 : Blo 960589 1446875 := bstep (se 1 (by rfl) ⟨1085156, by rfl⟩ : syracuseStep 1446875 = 2170313) B2170313
theorem B1643527 : Blo 960589 1643527 := bstep (se 1 (by rfl) ⟨1232645, by rfl⟩ : syracuseStep 1643527 = 2465291) B2465291
theorem B2167865 : Blo 960589 2167865 := bstep (se 2 (by rfl) ⟨812949, by rfl⟩ : syracuseStep 2167865 = 1625899) B1625899
theorem B3085465 : Blo 960589 3085465 := bstep (se 2 (by rfl) ⟨1157049, by rfl⟩ : syracuseStep 3085465 = 2314099) B2314099
theorem B2168207 : Blo 960589 2168207 := bstep (se 1 (by rfl) ⟨1626155, by rfl⟩ : syracuseStep 2168207 = 3252311) B3252311
theorem B7312841 : Blo 960589 7312841 := bstep (se 2 (by rfl) ⟨2742315, by rfl⟩ : syracuseStep 7312841 = 5484631) B5484631
theorem B2168531 : Blo 960589 2168531 := bstep (se 1 (by rfl) ⟨1626398, by rfl⟩ : syracuseStep 2168531 = 3252797) B3252797
theorem B6953303 : Blo 960589 6953303 := bstep (se 1 (by rfl) ⟨5214977, by rfl⟩ : syracuseStep 6953303 = 10429955) B10429955
theorem B12327299 : Blo 960589 12327299 := bstep (se 1 (by rfl) ⟨9245474, by rfl⟩ : syracuseStep 12327299 = 18490949) B18490949
theorem B2922895 : Blo 960589 2922895 := bstep (se 1 (by rfl) ⟨2192171, by rfl⟩ : syracuseStep 2922895 = 4384343) B4384343
theorem B8231321 : Blo 960589 8231321 := bstep (se 2 (by rfl) ⟨3086745, by rfl⟩ : syracuseStep 8231321 = 6173491) B6173491
theorem B3709421 : Blo 960589 3709421 := bstep (se 3 (by rfl) ⟨695516, by rfl⟩ : syracuseStep 3709421 = 1391033) B1391033
theorem B1219151 : Blo 960589 1219151 := bstep (se 1 (by rfl) ⟨914363, by rfl⟩ : syracuseStep 1219151 = 1828727) B1828727
theorem B2169467 : Blo 960589 2169467 := bstep (se 1 (by rfl) ⟨1627100, by rfl⟩ : syracuseStep 2169467 = 3254201) B3254201
theorem B2169593 : Blo 960589 2169593 := bstep (se 2 (by rfl) ⟨813597, by rfl⟩ : syracuseStep 2169593 = 1627195) B1627195
theorem B2169863 : Blo 960589 2169863 := bstep (se 1 (by rfl) ⟨1627397, by rfl⟩ : syracuseStep 2169863 = 3254795) B3254795
theorem B2169935 : Blo 960589 2169935 := bstep (se 1 (by rfl) ⟨1627451, by rfl⟩ : syracuseStep 2169935 = 3254903) B3254903
theorem B3251447 : Blo 960589 3251447 := bstep (se 1 (by rfl) ⟨2438585, by rfl⟩ : syracuseStep 3251447 = 4877171) B4877171
theorem B6167933 : Blo 960589 6167933 := bstep (se 3 (by rfl) ⟨1156487, by rfl⟩ : syracuseStep 6167933 = 2312975) B2312975
theorem B7806451 : Blo 960589 7806451 := bstep (se 1 (by rfl) ⟨5854838, by rfl⟩ : syracuseStep 7806451 = 11709677) B11709677
theorem B2432551 : Blo 960589 2432551 := bstep (se 1 (by rfl) ⟨1824413, by rfl⟩ : syracuseStep 2432551 = 3648827) B3648827
theorem B3251771 : Blo 960589 3251771 := bstep (se 1 (by rfl) ⟨2438828, by rfl⟩ : syracuseStep 3251771 = 4877657) B4877657
theorem B11280005 : Blo 960589 11280005 := bstep (se 4 (by rfl) ⟨1057500, by rfl⟩ : syracuseStep 11280005 = 2115001) B2115001
theorem B5480075 : Blo 960589 5480075 := bstep (se 1 (by rfl) ⟨4110056, by rfl⟩ : syracuseStep 5480075 = 8220113) B8220113
theorem B2924281 : Blo 960589 2924281 := bstep (se 2 (by rfl) ⟨1096605, by rfl⟩ : syracuseStep 2924281 = 2193211) B2193211
theorem B3252041 : Blo 960589 3252041 := bstep (se 2 (by rfl) ⟨1219515, by rfl⟩ : syracuseStep 3252041 = 2439031) B2439031
theorem B1220447 : Blo 960589 1220447 := bstep (se 1 (by rfl) ⟨915335, by rfl⟩ : syracuseStep 1220447 = 1830671) B1830671
theorem B2432875 : Blo 960589 2432875 := bstep (se 1 (by rfl) ⟨1824656, by rfl⟩ : syracuseStep 2432875 = 3649313) B3649313
theorem B4628411 : Blo 960589 4628411 := bstep (se 1 (by rfl) ⟨3471308, by rfl⟩ : syracuseStep 4628411 = 6942617) B6942617
theorem B27795473 : Blo 960589 27795473 := bstep (se 2 (by rfl) ⟨10423302, by rfl⟩ : syracuseStep 27795473 = 20846605) B20846605
theorem B2433523 : Blo 960589 2433523 := bstep (se 1 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 2433523 = 3650285) B3650285
theorem B3253175 : Blo 960589 3253175 := bstep (se 1 (by rfl) ⟨2439881, by rfl⟩ : syracuseStep 3253175 = 4879763) B4879763
theorem B3089335 : Blo 960589 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B4006913 : Blo 960589 4006913 := bstep (se 2 (by rfl) ⟨1502592, by rfl⟩ : syracuseStep 4006913 = 3005185) B3005185
theorem B1647625 : Blo 960589 1647625 := bstep (se 2 (by rfl) ⟨617859, by rfl⟩ : syracuseStep 1647625 = 1235719) B1235719
theorem B3515471 : Blo 960589 3515471 := bstep (se 1 (by rfl) ⟨2636603, by rfl⟩ : syracuseStep 3515471 = 5273207) B5273207
theorem B4760957 : Blo 960589 4760957 := bstep (se 3 (by rfl) ⟨892679, by rfl⟩ : syracuseStep 4760957 = 1785359) B1785359
theorem B27698597 : Blo 960589 27698597 := bstep (se 4 (by rfl) ⟨2596743, by rfl⟩ : syracuseStep 27698597 = 5193487) B5193487
theorem B5547437 : Blo 960589 5547437 := bstep (se 3 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 5547437 = 2080289) B2080289
theorem B3253769 : Blo 960589 3253769 := bstep (se 2 (by rfl) ⟨1220163, by rfl⟩ : syracuseStep 3253769 = 2440327) B2440327
theorem B2434657 : Blo 960589 2434657 := bstep (se 2 (by rfl) ⟨912996, by rfl⟩ : syracuseStep 2434657 = 1825993) B1825993
theorem B3647339 : Blo 960589 3647339 := bstep (se 1 (by rfl) ⟨2735504, by rfl⟩ : syracuseStep 3647339 = 5471009) B5471009
theorem B8234945 : Blo 960589 8234945 := bstep (se 2 (by rfl) ⟨3088104, by rfl⟩ : syracuseStep 8234945 = 6176209) B6176209
theorem B960591 : Blo 960589 960591 := bstep (se 1 (by rfl) ⟨720443, by rfl⟩ : syracuseStep 960591 = 1440887) B1440887
theorem B960607 : Blo 960589 960607 := bstep (se 1 (by rfl) ⟨720455, by rfl⟩ : syracuseStep 960607 = 1440911) B1440911
theorem B960635 : Blo 960589 960635 := bstep (se 1 (by rfl) ⟨720476, by rfl⟩ : syracuseStep 960635 = 1440953) B1440953
theorem B960687 : Blo 960589 960687 := bstep (se 1 (by rfl) ⟨720515, by rfl⟩ : syracuseStep 960687 = 1441031) B1441031
theorem B960711 : Blo 960589 960711 := bstep (se 1 (by rfl) ⟨720533, by rfl⟩ : syracuseStep 960711 = 1441067) B1441067
theorem B960731 : Blo 960589 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B960807 : Blo 960589 960807 := bstep (se 1 (by rfl) ⟨720605, by rfl⟩ : syracuseStep 960807 = 1441211) B1441211
theorem B960847 : Blo 960589 960847 := bstep (se 1 (by rfl) ⟨720635, by rfl⟩ : syracuseStep 960847 = 1441271) B1441271
theorem B4630871 : Blo 960589 4630871 := bstep (se 1 (by rfl) ⟨3473153, by rfl⟩ : syracuseStep 4630871 = 6946307) B6946307
theorem B960863 : Blo 960589 960863 := bstep (se 1 (by rfl) ⟨720647, by rfl⟩ : syracuseStep 960863 = 1441295) B1441295
theorem B3254633 : Blo 960589 3254633 := bstep (se 2 (by rfl) ⟨1220487, by rfl⟩ : syracuseStep 3254633 = 2440975) B2440975
theorem B960891 : Blo 960589 960891 := bstep (se 1 (by rfl) ⟨720668, by rfl⟩ : syracuseStep 960891 = 1441337) B1441337
theorem B12331399 : Blo 960589 12331399 := bstep (se 1 (by rfl) ⟨9248549, by rfl⟩ : syracuseStep 12331399 = 18497099) B18497099
theorem B960943 : Blo 960589 960943 := bstep (se 1 (by rfl) ⟨720707, by rfl⟩ : syracuseStep 960943 = 1441415) B1441415
theorem B960967 : Blo 960589 960967 := bstep (se 1 (by rfl) ⟨720725, by rfl⟩ : syracuseStep 960967 = 1441451) B1441451
theorem B960987 : Blo 960589 960987 := bstep (se 1 (by rfl) ⟨720740, by rfl⟩ : syracuseStep 960987 = 1441481) B1441481
theorem B2435609 : Blo 960589 2435609 := bstep (se 2 (by rfl) ⟨913353, by rfl⟩ : syracuseStep 2435609 = 1826707) B1826707
theorem B961063 : Blo 960589 961063 := bstep (se 1 (by rfl) ⟨720797, by rfl⟩ : syracuseStep 961063 = 1441595) B1441595
theorem B961103 : Blo 960589 961103 := bstep (se 1 (by rfl) ⟨720827, by rfl⟩ : syracuseStep 961103 = 1441655) B1441655
theorem B961119 : Blo 960589 961119 := bstep (se 1 (by rfl) ⟨720839, by rfl⟩ : syracuseStep 961119 = 1441679) B1441679
theorem B961147 : Blo 960589 961147 := bstep (se 1 (by rfl) ⟨720860, by rfl⟩ : syracuseStep 961147 = 1441721) B1441721
theorem B961199 : Blo 960589 961199 := bstep (se 1 (by rfl) ⟨720899, by rfl⟩ : syracuseStep 961199 = 1441799) B1441799
theorem B961223 : Blo 960589 961223 := bstep (se 1 (by rfl) ⟨720917, by rfl⟩ : syracuseStep 961223 = 1441835) B1441835
theorem B961243 : Blo 960589 961243 := bstep (se 1 (by rfl) ⟨720932, by rfl⟩ : syracuseStep 961243 = 1441865) B1441865
theorem B961319 : Blo 960589 961319 := bstep (se 1 (by rfl) ⟨720989, by rfl⟩ : syracuseStep 961319 = 1441979) B1441979
theorem B961359 : Blo 960589 961359 := bstep (se 1 (by rfl) ⟨721019, by rfl⟩ : syracuseStep 961359 = 1442039) B1442039
theorem B961375 : Blo 960589 961375 := bstep (se 1 (by rfl) ⟨721031, by rfl⟩ : syracuseStep 961375 = 1442063) B1442063
theorem B961403 : Blo 960589 961403 := bstep (se 1 (by rfl) ⟨721052, by rfl⟩ : syracuseStep 961403 = 1442105) B1442105
theorem B961455 : Blo 960589 961455 := bstep (se 1 (by rfl) ⟨721091, by rfl⟩ : syracuseStep 961455 = 1442183) B1442183
theorem B5483447 : Blo 960589 5483447 := bstep (se 1 (by rfl) ⟨4112585, by rfl⟩ : syracuseStep 5483447 = 8225171) B8225171
theorem B3255227 : Blo 960589 3255227 := bstep (se 1 (by rfl) ⟨2441420, by rfl⟩ : syracuseStep 3255227 = 4882841) B4882841
theorem B961479 : Blo 960589 961479 := bstep (se 1 (by rfl) ⟨721109, by rfl⟩ : syracuseStep 961479 = 1442219) B1442219
theorem B961499 : Blo 960589 961499 := bstep (se 1 (by rfl) ⟨721124, by rfl⟩ : syracuseStep 961499 = 1442249) B1442249
theorem B2436115 : Blo 960589 2436115 := bstep (se 1 (by rfl) ⟨1827086, by rfl⟩ : syracuseStep 2436115 = 3654173) B3654173
theorem B961575 : Blo 960589 961575 := bstep (se 1 (by rfl) ⟨721181, by rfl⟩ : syracuseStep 961575 = 1442363) B1442363
theorem B961615 : Blo 960589 961615 := bstep (se 1 (by rfl) ⟨721211, by rfl⟩ : syracuseStep 961615 = 1442423) B1442423
theorem B961631 : Blo 960589 961631 := bstep (se 1 (by rfl) ⟨721223, by rfl⟩ : syracuseStep 961631 = 1442447) B1442447
theorem B961659 : Blo 960589 961659 := bstep (se 1 (by rfl) ⟨721244, by rfl⟩ : syracuseStep 961659 = 1442489) B1442489
theorem B961711 : Blo 960589 961711 := bstep (se 1 (by rfl) ⟨721283, by rfl⟩ : syracuseStep 961711 = 1442567) B1442567
theorem B961735 : Blo 960589 961735 := bstep (se 1 (by rfl) ⟨721301, by rfl⟩ : syracuseStep 961735 = 1442603) B1442603
theorem B6171851 : Blo 960589 6171851 := bstep (se 1 (by rfl) ⟨4628888, by rfl⟩ : syracuseStep 6171851 = 9257777) B9257777
theorem B961755 : Blo 960589 961755 := bstep (se 1 (by rfl) ⟨721316, by rfl⟩ : syracuseStep 961755 = 1442633) B1442633
theorem B961831 : Blo 960589 961831 := bstep (se 1 (by rfl) ⟨721373, by rfl⟩ : syracuseStep 961831 = 1442747) B1442747
theorem B961871 : Blo 960589 961871 := bstep (se 1 (by rfl) ⟨721403, by rfl⟩ : syracuseStep 961871 = 1442807) B1442807
theorem B961887 : Blo 960589 961887 := bstep (se 1 (by rfl) ⟨721415, by rfl⟩ : syracuseStep 961887 = 1442831) B1442831
theorem B961915 : Blo 960589 961915 := bstep (se 1 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 961915 = 1442873) B1442873
theorem B961967 : Blo 960589 961967 := bstep (se 1 (by rfl) ⟨721475, by rfl⟩ : syracuseStep 961967 = 1442951) B1442951
theorem B961991 : Blo 960589 961991 := bstep (se 1 (by rfl) ⟨721493, by rfl⟩ : syracuseStep 961991 = 1442987) B1442987
theorem B962011 : Blo 960589 962011 := bstep (se 1 (by rfl) ⟨721508, by rfl⟩ : syracuseStep 962011 = 1443017) B1443017
theorem B962087 : Blo 960589 962087 := bstep (se 1 (by rfl) ⟨721565, by rfl⟩ : syracuseStep 962087 = 1443131) B1443131
theorem B1388111 : Blo 960589 1388111 := bstep (se 1 (by rfl) ⟨1041083, by rfl⟩ : syracuseStep 1388111 = 2082167) B2082167
theorem B962127 : Blo 960589 962127 := bstep (se 1 (by rfl) ⟨721595, by rfl⟩ : syracuseStep 962127 = 1443191) B1443191
theorem B962143 : Blo 960589 962143 := bstep (se 1 (by rfl) ⟨721607, by rfl⟩ : syracuseStep 962143 = 1443215) B1443215
theorem B962171 : Blo 960589 962171 := bstep (se 1 (by rfl) ⟨721628, by rfl⟩ : syracuseStep 962171 = 1443257) B1443257
theorem B962223 : Blo 960589 962223 := bstep (se 1 (by rfl) ⟨721667, by rfl⟩ : syracuseStep 962223 = 1443335) B1443335
theorem B962247 : Blo 960589 962247 := bstep (se 1 (by rfl) ⟨721685, by rfl⟩ : syracuseStep 962247 = 1443371) B1443371
theorem B962267 : Blo 960589 962267 := bstep (se 1 (by rfl) ⟨721700, by rfl⟩ : syracuseStep 962267 = 1443401) B1443401
theorem B6598381 : Blo 960589 6598381 := bstep (se 3 (by rfl) ⟨1237196, by rfl⟩ : syracuseStep 6598381 = 2474393) B2474393
theorem B962343 : Blo 960589 962343 := bstep (se 1 (by rfl) ⟨721757, by rfl⟩ : syracuseStep 962343 = 1443515) B1443515
theorem B962383 : Blo 960589 962383 := bstep (se 1 (by rfl) ⟨721787, by rfl⟩ : syracuseStep 962383 = 1443575) B1443575
theorem B962399 : Blo 960589 962399 := bstep (se 1 (by rfl) ⟨721799, by rfl⟩ : syracuseStep 962399 = 1443599) B1443599
theorem B962427 : Blo 960589 962427 := bstep (se 1 (by rfl) ⟨721820, by rfl⟩ : syracuseStep 962427 = 1443641) B1443641
theorem B5484449 : Blo 960589 5484449 := bstep (se 2 (by rfl) ⟨2056668, by rfl⟩ : syracuseStep 5484449 = 4113337) B4113337
theorem B962479 : Blo 960589 962479 := bstep (se 1 (by rfl) ⟨721859, by rfl⟩ : syracuseStep 962479 = 1443719) B1443719
theorem B962503 : Blo 960589 962503 := bstep (se 1 (by rfl) ⟨721877, by rfl⟩ : syracuseStep 962503 = 1443755) B1443755
theorem B962523 : Blo 960589 962523 := bstep (se 1 (by rfl) ⟨721892, by rfl⟩ : syracuseStep 962523 = 1443785) B1443785
theorem B962599 : Blo 960589 962599 := bstep (se 1 (by rfl) ⟨721949, by rfl⟩ : syracuseStep 962599 = 1443899) B1443899
theorem B962639 : Blo 960589 962639 := bstep (se 1 (by rfl) ⟨721979, by rfl⟩ : syracuseStep 962639 = 1443959) B1443959
theorem B2437199 : Blo 960589 2437199 := bstep (se 1 (by rfl) ⟨1827899, by rfl⟩ : syracuseStep 2437199 = 3655799) B3655799
theorem B962655 : Blo 960589 962655 := bstep (se 1 (by rfl) ⟨721991, by rfl⟩ : syracuseStep 962655 = 1443983) B1443983
theorem B962683 : Blo 960589 962683 := bstep (se 1 (by rfl) ⟨722012, by rfl⟩ : syracuseStep 962683 = 1444025) B1444025
theorem B962735 : Blo 960589 962735 := bstep (se 1 (by rfl) ⟨722051, by rfl⟩ : syracuseStep 962735 = 1444103) B1444103
theorem B962759 : Blo 960589 962759 := bstep (se 1 (by rfl) ⟨722069, by rfl⟩ : syracuseStep 962759 = 1444139) B1444139
theorem B962779 : Blo 960589 962779 := bstep (se 1 (by rfl) ⟨722084, by rfl⟩ : syracuseStep 962779 = 1444169) B1444169
theorem B962855 : Blo 960589 962855 := bstep (se 1 (by rfl) ⟨722141, by rfl⟩ : syracuseStep 962855 = 1444283) B1444283
theorem B962895 : Blo 960589 962895 := bstep (se 1 (by rfl) ⟨722171, by rfl⟩ : syracuseStep 962895 = 1444343) B1444343
theorem B962911 : Blo 960589 962911 := bstep (se 1 (by rfl) ⟨722183, by rfl⟩ : syracuseStep 962911 = 1444367) B1444367
theorem B5484905 : Blo 960589 5484905 := bstep (se 2 (by rfl) ⟨2056839, by rfl⟩ : syracuseStep 5484905 = 4113679) B4113679
theorem B962939 : Blo 960589 962939 := bstep (se 1 (by rfl) ⟨722204, by rfl⟩ : syracuseStep 962939 = 1444409) B1444409
theorem B6926725 : Blo 960589 6926725 := bstep (se 4 (by rfl) ⟨649380, by rfl⟩ : syracuseStep 6926725 = 1298761) B1298761
theorem B6173081 : Blo 960589 6173081 := bstep (se 2 (by rfl) ⟨2314905, by rfl⟩ : syracuseStep 6173081 = 4629811) B4629811
theorem B962991 : Blo 960589 962991 := bstep (se 1 (by rfl) ⟨722243, by rfl⟩ : syracuseStep 962991 = 1444487) B1444487
theorem B963015 : Blo 960589 963015 := bstep (se 1 (by rfl) ⟨722261, by rfl⟩ : syracuseStep 963015 = 1444523) B1444523
theorem B963035 : Blo 960589 963035 := bstep (se 1 (by rfl) ⟨722276, by rfl⟩ : syracuseStep 963035 = 1444553) B1444553
theorem B963111 : Blo 960589 963111 := bstep (se 1 (by rfl) ⟨722333, by rfl⟩ : syracuseStep 963111 = 1444667) B1444667
theorem B963151 : Blo 960589 963151 := bstep (se 1 (by rfl) ⟨722363, by rfl⟩ : syracuseStep 963151 = 1444727) B1444727
theorem B963167 : Blo 960589 963167 := bstep (se 1 (by rfl) ⟨722375, by rfl⟩ : syracuseStep 963167 = 1444751) B1444751
theorem B963195 : Blo 960589 963195 := bstep (se 1 (by rfl) ⟨722396, by rfl⟩ : syracuseStep 963195 = 1444793) B1444793
theorem B6599341 : Blo 960589 6599341 := bstep (se 3 (by rfl) ⟨1237376, by rfl⟩ : syracuseStep 6599341 = 2474753) B2474753
theorem B963247 : Blo 960589 963247 := bstep (se 1 (by rfl) ⟨722435, by rfl⟩ : syracuseStep 963247 = 1444871) B1444871
theorem B963271 : Blo 960589 963271 := bstep (se 1 (by rfl) ⟨722453, by rfl⟩ : syracuseStep 963271 = 1444907) B1444907
theorem B2437847 : Blo 960589 2437847 := bstep (se 1 (by rfl) ⟨1828385, by rfl⟩ : syracuseStep 2437847 = 3656771) B3656771
theorem B963291 : Blo 960589 963291 := bstep (se 1 (by rfl) ⟨722468, by rfl⟩ : syracuseStep 963291 = 1444937) B1444937
theorem B963367 : Blo 960589 963367 := bstep (se 1 (by rfl) ⟨722525, by rfl⟩ : syracuseStep 963367 = 1445051) B1445051
theorem B963407 : Blo 960589 963407 := bstep (se 1 (by rfl) ⟨722555, by rfl⟩ : syracuseStep 963407 = 1445111) B1445111
theorem B963423 : Blo 960589 963423 := bstep (se 1 (by rfl) ⟨722567, by rfl⟩ : syracuseStep 963423 = 1445135) B1445135
theorem B963451 : Blo 960589 963451 := bstep (se 1 (by rfl) ⟨722588, by rfl⟩ : syracuseStep 963451 = 1445177) B1445177
theorem B963503 : Blo 960589 963503 := bstep (se 1 (by rfl) ⟨722627, by rfl⟩ : syracuseStep 963503 = 1445255) B1445255
theorem B963527 : Blo 960589 963527 := bstep (se 1 (by rfl) ⟨722645, by rfl⟩ : syracuseStep 963527 = 1445291) B1445291
theorem B963547 : Blo 960589 963547 := bstep (se 1 (by rfl) ⟨722660, by rfl⟩ : syracuseStep 963547 = 1445321) B1445321
theorem B963623 : Blo 960589 963623 := bstep (se 1 (by rfl) ⟨722717, by rfl⟩ : syracuseStep 963623 = 1445435) B1445435
theorem B2438201 : Blo 960589 2438201 := bstep (se 2 (by rfl) ⟨914325, by rfl⟩ : syracuseStep 2438201 = 1828651) B1828651
theorem B963663 : Blo 960589 963663 := bstep (se 1 (by rfl) ⟨722747, by rfl⟩ : syracuseStep 963663 = 1445495) B1445495
theorem B963679 : Blo 960589 963679 := bstep (se 1 (by rfl) ⟨722759, by rfl⟩ : syracuseStep 963679 = 1445519) B1445519
theorem B963707 : Blo 960589 963707 := bstep (se 1 (by rfl) ⟨722780, by rfl⟩ : syracuseStep 963707 = 1445561) B1445561
theorem B963759 : Blo 960589 963759 := bstep (se 1 (by rfl) ⟨722819, by rfl⟩ : syracuseStep 963759 = 1445639) B1445639
theorem B963783 : Blo 960589 963783 := bstep (se 1 (by rfl) ⟨722837, by rfl⟩ : syracuseStep 963783 = 1445675) B1445675
theorem B963803 : Blo 960589 963803 := bstep (se 1 (by rfl) ⟨722852, by rfl⟩ : syracuseStep 963803 = 1445705) B1445705
theorem B963879 : Blo 960589 963879 := bstep (se 1 (by rfl) ⟨722909, by rfl⟩ : syracuseStep 963879 = 1445819) B1445819
theorem B963919 : Blo 960589 963919 := bstep (se 1 (by rfl) ⟨722939, by rfl⟩ : syracuseStep 963919 = 1445879) B1445879
theorem B963935 : Blo 960589 963935 := bstep (se 1 (by rfl) ⟨722951, by rfl⟩ : syracuseStep 963935 = 1445903) B1445903
theorem B963963 : Blo 960589 963963 := bstep (se 1 (by rfl) ⟨722972, by rfl⟩ : syracuseStep 963963 = 1445945) B1445945
theorem B964015 : Blo 960589 964015 := bstep (se 1 (by rfl) ⟨723011, by rfl⟩ : syracuseStep 964015 = 1446023) B1446023
theorem B964039 : Blo 960589 964039 := bstep (se 1 (by rfl) ⟨723029, by rfl⟩ : syracuseStep 964039 = 1446059) B1446059
theorem B964059 : Blo 960589 964059 := bstep (se 1 (by rfl) ⟨723044, by rfl⟩ : syracuseStep 964059 = 1446089) B1446089
theorem B964135 : Blo 960589 964135 := bstep (se 1 (by rfl) ⟨723101, by rfl⟩ : syracuseStep 964135 = 1446203) B1446203
theorem B964175 : Blo 960589 964175 := bstep (se 1 (by rfl) ⟨723131, by rfl⟩ : syracuseStep 964175 = 1446263) B1446263
theorem B964191 : Blo 960589 964191 := bstep (se 1 (by rfl) ⟨723143, by rfl⟩ : syracuseStep 964191 = 1446287) B1446287
theorem B964219 : Blo 960589 964219 := bstep (se 1 (by rfl) ⟨723164, by rfl⟩ : syracuseStep 964219 = 1446329) B1446329
theorem B964271 : Blo 960589 964271 := bstep (se 1 (by rfl) ⟨723203, by rfl⟩ : syracuseStep 964271 = 1446407) B1446407
theorem B3651257 : Blo 960589 3651257 := bstep (se 2 (by rfl) ⟨1369221, by rfl⟩ : syracuseStep 3651257 = 2738443) B2738443
theorem B20821697 : Blo 960589 20821697 := bstep (se 2 (by rfl) ⟨7808136, by rfl⟩ : syracuseStep 20821697 = 15616273) B15616273
theorem B964295 : Blo 960589 964295 := bstep (se 1 (by rfl) ⟨723221, by rfl⟩ : syracuseStep 964295 = 1446443) B1446443
theorem B964315 : Blo 960589 964315 := bstep (se 1 (by rfl) ⟨723236, by rfl⟩ : syracuseStep 964315 = 1446473) B1446473
theorem B6928109 : Blo 960589 6928109 := bstep (se 3 (by rfl) ⟨1299020, by rfl⟩ : syracuseStep 6928109 = 2598041) B2598041
theorem B964391 : Blo 960589 964391 := bstep (se 1 (by rfl) ⟨723293, by rfl⟩ : syracuseStep 964391 = 1446587) B1446587
theorem B5551939 : Blo 960589 5551939 := bstep (se 1 (by rfl) ⟨4163954, by rfl⟩ : syracuseStep 5551939 = 8327909) B8327909
theorem B964431 : Blo 960589 964431 := bstep (se 1 (by rfl) ⟨723323, by rfl⟩ : syracuseStep 964431 = 1446647) B1446647
theorem B964447 : Blo 960589 964447 := bstep (se 1 (by rfl) ⟨723335, by rfl⟩ : syracuseStep 964447 = 1446671) B1446671
theorem B964475 : Blo 960589 964475 := bstep (se 1 (by rfl) ⟨723356, by rfl⟩ : syracuseStep 964475 = 1446713) B1446713
theorem B964527 : Blo 960589 964527 := bstep (se 1 (by rfl) ⟨723395, by rfl⟩ : syracuseStep 964527 = 1446791) B1446791
theorem B1947575 : Blo 960589 1947575 := bstep (se 1 (by rfl) ⟨1460681, by rfl⟩ : syracuseStep 1947575 = 2921363) B2921363
theorem B964551 : Blo 960589 964551 := bstep (se 1 (by rfl) ⟨723413, by rfl⟩ : syracuseStep 964551 = 1446827) B1446827
theorem B964571 : Blo 960589 964571 := bstep (se 1 (by rfl) ⟨723428, by rfl⟩ : syracuseStep 964571 = 1446857) B1446857
theorem B4864697 : Blo 960589 4864697 := bstep (se 2 (by rfl) ⟨1824261, by rfl⟩ : syracuseStep 4864697 = 3648523) B3648523
theorem B3128473 : Blo 960589 3128473 := bstep (se 2 (by rfl) ⟨1173177, by rfl⟩ : syracuseStep 3128473 = 2346355) B2346355
theorem B2964637 : Blo 960589 2964637 := bstep (se 3 (by rfl) ⟨555869, by rfl⟩ : syracuseStep 2964637 = 1111739) B1111739
theorem B2440439 : Blo 960589 2440439 := bstep (se 1 (by rfl) ⟨1830329, by rfl⟩ : syracuseStep 2440439 = 3660659) B3660659
theorem B1621343 : Blo 960589 1621343 := bstep (se 1 (by rfl) ⟨1216007, by rfl⟩ : syracuseStep 1621343 = 2432015) B2432015
theorem B5488073 : Blo 960589 5488073 := bstep (se 2 (by rfl) ⟨2058027, by rfl⟩ : syracuseStep 5488073 = 4116055) B4116055
theorem B2309755 : Blo 960589 2309755 := bstep (se 1 (by rfl) ⟨1732316, by rfl⟩ : syracuseStep 2309755 = 3464633) B3464633
theorem B6504185 : Blo 960589 6504185 := bstep (se 2 (by rfl) ⟨2439069, by rfl⟩ : syracuseStep 6504185 = 4878139) B4878139
theorem B3653369 : Blo 960589 3653369 := bstep (se 2 (by rfl) ⟨1370013, by rfl⟩ : syracuseStep 3653369 = 2740027) B2740027
theorem B1621903 : Blo 960589 1621903 := bstep (se 1 (by rfl) ⟨1216427, by rfl⟩ : syracuseStep 1621903 = 2432855) B2432855
theorem B2604961 : Blo 960589 2604961 := bstep (se 2 (by rfl) ⟨976860, by rfl⟩ : syracuseStep 2604961 = 1953721) B1953721
theorem B1949627 : Blo 960589 1949627 := bstep (se 1 (by rfl) ⟨1462220, by rfl⟩ : syracuseStep 1949627 = 2924441) B2924441
theorem B2605135 : Blo 960589 2605135 := bstep (se 1 (by rfl) ⟨1953851, by rfl⟩ : syracuseStep 2605135 = 3907703) B3907703
theorem B8208701 : Blo 960589 8208701 := bstep (se 3 (by rfl) ⟨1539131, by rfl⟩ : syracuseStep 8208701 = 3078263) B3078263
theorem B1622585 : Blo 960589 1622585 := bstep (se 2 (by rfl) ⟨608469, by rfl⟩ : syracuseStep 1622585 = 1216939) B1216939
theorem B3654355 : Blo 960589 3654355 := bstep (se 1 (by rfl) ⟨2740766, by rfl⟩ : syracuseStep 3654355 = 5481533) B5481533
theorem B6177491 : Blo 960589 6177491 := bstep (se 1 (by rfl) ⟨4633118, by rfl⟩ : syracuseStep 6177491 = 9266237) B9266237
theorem B13190039 : Blo 960589 13190039 := bstep (se 1 (by rfl) ⟨9892529, by rfl⟩ : syracuseStep 13190039 = 19785059) B19785059
theorem B2605999 : Blo 960589 2605999 := bstep (se 1 (by rfl) ⟨1954499, by rfl⟩ : syracuseStep 2605999 = 3908999) B3908999
theorem B2606087 : Blo 960589 2606087 := bstep (se 1 (by rfl) ⟨1954565, by rfl⟩ : syracuseStep 2606087 = 3909131) B3909131
theorem B3654827 : Blo 960589 3654827 := bstep (se 1 (by rfl) ⟨2741120, by rfl⟩ : syracuseStep 3654827 = 5482241) B5482241
theorem B1623287 : Blo 960589 1623287 := bstep (se 1 (by rfl) ⟨1217465, by rfl⟩ : syracuseStep 1623287 = 2434931) B2434931
theorem B1623631 : Blo 960589 1623631 := bstep (se 1 (by rfl) ⟨1217723, by rfl⟩ : syracuseStep 1623631 = 2435447) B2435447
theorem B5850947 : Blo 960589 5850947 := bstep (se 1 (by rfl) ⟨4388210, by rfl⟩ : syracuseStep 5850947 = 8776421) B8776421
theorem B1623881 : Blo 960589 1623881 := bstep (se 2 (by rfl) ⟨608955, by rfl⟩ : syracuseStep 1623881 = 1217911) B1217911
theorem B7817219 : Blo 960589 7817219 := bstep (se 1 (by rfl) ⟨5862914, by rfl⟩ : syracuseStep 7817219 = 11725829) B11725829
theorem B5851217 : Blo 960589 5851217 := bstep (se 2 (by rfl) ⟨2194206, by rfl⟩ : syracuseStep 5851217 = 4388413) B4388413
theorem B1624313 : Blo 960589 1624313 := bstep (se 2 (by rfl) ⟨609117, by rfl⟩ : syracuseStep 1624313 = 1218235) B1218235
theorem B1624495 : Blo 960589 1624495 := bstep (se 1 (by rfl) ⟨1218371, by rfl⟩ : syracuseStep 1624495 = 2436743) B2436743
theorem B36161977 : Blo 960589 36161977 := bstep (se 2 (by rfl) ⟨13560741, by rfl⟩ : syracuseStep 36161977 = 27121483) B27121483
theorem B1624583 : Blo 960589 1624583 := bstep (se 1 (by rfl) ⟨1218437, by rfl⟩ : syracuseStep 1624583 = 2436875) B2436875
theorem B2738785 : Blo 960589 2738785 := bstep (se 2 (by rfl) ⟨1027044, by rfl⟩ : syracuseStep 2738785 = 2054089) B2054089
theorem B1624927 : Blo 960589 1624927 := bstep (se 1 (by rfl) ⟨1218695, by rfl⟩ : syracuseStep 1624927 = 2437391) B2437391
theorem B1625015 : Blo 960589 1625015 := bstep (se 1 (by rfl) ⟨1218761, by rfl⟩ : syracuseStep 1625015 = 2437523) B2437523
theorem B2968595 : Blo 960589 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B3656785 : Blo 960589 3656785 := bstep (se 2 (by rfl) ⟨1371294, by rfl⟩ : syracuseStep 3656785 = 2742589) B2742589
theorem B3657089 : Blo 960589 3657089 := bstep (se 2 (by rfl) ⟨1371408, by rfl⟩ : syracuseStep 3657089 = 2742817) B2742817
theorem B1625609 : Blo 960589 1625609 := bstep (se 2 (by rfl) ⟨609603, by rfl⟩ : syracuseStep 1625609 = 1219207) B1219207
theorem B1625771 : Blo 960589 1625771 := bstep (se 1 (by rfl) ⟨1219328, by rfl⟩ : syracuseStep 1625771 = 2438657) B2438657
theorem B2739901 : Blo 960589 2739901 := bstep (se 3 (by rfl) ⟨513731, by rfl⟩ : syracuseStep 2739901 = 1027463) B1027463
theorem B1461959 : Blo 960589 1461959 := bstep (se 1 (by rfl) ⟨1096469, by rfl⟩ : syracuseStep 1461959 = 2192939) B2192939
theorem B4869881 : Blo 960589 4869881 := bstep (se 2 (by rfl) ⟨1826205, by rfl⟩ : syracuseStep 4869881 = 3652411) B3652411
theorem B3657545 : Blo 960589 3657545 := bstep (se 2 (by rfl) ⟨1371579, by rfl⟩ : syracuseStep 3657545 = 2743159) B2743159
theorem B236900213 : Blo 960589 236900213 := bstep (se 5 (by rfl) ⟨11104697, by rfl⟩ : syracuseStep 236900213 = 22209395) B22209395
theorem B26333189 : Blo 960589 26333189 := bstep (se 4 (by rfl) ⟨2468736, by rfl⟩ : syracuseStep 26333189 = 4937473) B4937473
theorem B1855495 : Blo 960589 1855495 := bstep (se 1 (by rfl) ⟨1391621, by rfl⟩ : syracuseStep 1855495 = 2783243) B2783243
theorem B3657743 : Blo 960589 3657743 := bstep (se 1 (by rfl) ⟨2743307, by rfl⟩ : syracuseStep 3657743 = 5486615) B5486615
theorem B2740243 : Blo 960589 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B1626169 : Blo 960589 1626169 := bstep (se 2 (by rfl) ⟨609813, by rfl⟩ : syracuseStep 1626169 = 1219627) B1219627
theorem B1626311 : Blo 960589 1626311 := bstep (se 1 (by rfl) ⟨1219733, by rfl⟩ : syracuseStep 1626311 = 2439467) B2439467
theorem B1626473 : Blo 960589 1626473 := bstep (se 2 (by rfl) ⟨609927, by rfl⟩ : syracuseStep 1626473 = 1219855) B1219855
theorem B4870529 : Blo 960589 4870529 := bstep (se 2 (by rfl) ⟨1826448, by rfl⟩ : syracuseStep 4870529 = 3652897) B3652897
theorem B11686517 : Blo 960589 11686517 := bstep (se 5 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 11686517 = 1095611) B1095611
theorem B1626871 : Blo 960589 1626871 := bstep (se 1 (by rfl) ⟨1220153, by rfl⟩ : syracuseStep 1626871 = 2440307) B2440307
theorem B24695603 : Blo 960589 24695603 := bstep (se 1 (by rfl) ⟨18521702, by rfl⟩ : syracuseStep 24695603 = 37043405) B37043405
theorem B2053039 : Blo 960589 2053039 := bstep (se 1 (by rfl) ⟨1539779, by rfl⟩ : syracuseStep 2053039 = 3079559) B3079559
theorem B1627067 : Blo 960589 1627067 := bstep (se 1 (by rfl) ⟨1220300, by rfl⟩ : syracuseStep 1627067 = 2440601) B2440601
theorem B1627175 : Blo 960589 1627175 := bstep (se 1 (by rfl) ⟨1220381, by rfl⟩ : syracuseStep 1627175 = 2440763) B2440763
theorem B1823867 : Blo 960589 1823867 := bstep (se 1 (by rfl) ⟨1367900, by rfl⟩ : syracuseStep 1823867 = 2735801) B2735801
theorem B4871339 : Blo 960589 4871339 := bstep (se 1 (by rfl) ⟨3653504, by rfl⟩ : syracuseStep 4871339 = 7307009) B7307009
theorem B1627465 : Blo 960589 1627465 := bstep (se 2 (by rfl) ⟨610299, by rfl⟩ : syracuseStep 1627465 = 1220599) B1220599
theorem B1824095 : Blo 960589 1824095 := bstep (se 1 (by rfl) ⟨1368071, by rfl⟩ : syracuseStep 1824095 = 2736143) B2736143
theorem B1627499 : Blo 960589 1627499 := bstep (se 1 (by rfl) ⟨1220624, by rfl⟩ : syracuseStep 1627499 = 2441249) B2441249
theorem B2741633 : Blo 960589 2741633 := bstep (se 2 (by rfl) ⟨1028112, by rfl⟩ : syracuseStep 2741633 = 2056225) B2056225
theorem B1824353 : Blo 960589 1824353 := bstep (se 2 (by rfl) ⟨684132, by rfl⟩ : syracuseStep 1824353 = 1368265) B1368265
theorem B12342881 : Blo 960589 12342881 := bstep (se 2 (by rfl) ⟨4628580, by rfl⟩ : syracuseStep 12342881 = 9257161) B9257161
theorem B4871825 : Blo 960589 4871825 := bstep (se 2 (by rfl) ⟨1826934, by rfl⟩ : syracuseStep 4871825 = 3653869) B3653869
theorem B35149463 : Blo 960589 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B28169927 : Blo 960589 28169927 := bstep (se 1 (by rfl) ⟨21127445, by rfl⟩ : syracuseStep 28169927 = 42254891) B42254891
theorem B2741975 : Blo 960589 2741975 := bstep (se 1 (by rfl) ⟨2056481, by rfl⟩ : syracuseStep 2741975 = 4112963) B4112963
theorem B1824619 : Blo 960589 1824619 := bstep (se 1 (by rfl) ⟨1368464, by rfl⟩ : syracuseStep 1824619 = 2736929) B2736929
theorem B2316367 : Blo 960589 2316367 := bstep (se 1 (by rfl) ⟨1737275, by rfl⟩ : syracuseStep 2316367 = 3474551) B3474551
theorem B1825811 : Blo 960589 1825811 := bstep (se 1 (by rfl) ⟨1369358, by rfl⟩ : syracuseStep 1825811 = 2738717) B2738717
theorem B3464345 : Blo 960589 3464345 := bstep (se 2 (by rfl) ⟨1299129, by rfl⟩ : syracuseStep 3464345 = 2598259) B2598259
theorem B1826039 : Blo 960589 1826039 := bstep (se 1 (by rfl) ⟨1369529, by rfl⟩ : syracuseStep 1826039 = 2739059) B2739059
theorem B3464459 : Blo 960589 3464459 := bstep (se 1 (by rfl) ⟨2598344, by rfl⟩ : syracuseStep 3464459 = 5196689) B5196689
theorem B1302265 : Blo 960589 1302265 := bstep (se 2 (by rfl) ⟨488349, by rfl⟩ : syracuseStep 1302265 = 976699) B976699
theorem B4874093 : Blo 960589 4874093 := bstep (se 3 (by rfl) ⟨913892, by rfl⟩ : syracuseStep 4874093 = 1827785) B1827785
theorem B6250499 : Blo 960589 6250499 := bstep (se 1 (by rfl) ⟨4687874, by rfl⟩ : syracuseStep 6250499 = 9375749) B9375749
theorem B4874255 : Blo 960589 4874255 := bstep (se 1 (by rfl) ⟨3655691, by rfl⟩ : syracuseStep 4874255 = 7311383) B7311383
theorem B1827451 : Blo 960589 1827451 := bstep (se 1 (by rfl) ⟨1370588, by rfl⟩ : syracuseStep 1827451 = 2741177) B2741177
theorem B7299719 : Blo 960589 7299719 := bstep (se 1 (by rfl) ⟨5474789, by rfl⟩ : syracuseStep 7299719 = 10949579) B10949579
theorem B13361993 : Blo 960589 13361993 := bstep (se 2 (by rfl) ⟨5010747, by rfl⟩ : syracuseStep 13361993 = 10021495) B10021495
theorem B1827679 : Blo 960589 1827679 := bstep (se 1 (by rfl) ⟨1370759, by rfl⟩ : syracuseStep 1827679 = 2741519) B2741519
theorem B1368937 : Blo 960589 1368937 := bstep (se 2 (by rfl) ⟨513351, by rfl⟩ : syracuseStep 1368937 = 1026703) B1026703
theorem B1827937 : Blo 960589 1827937 := bstep (se 2 (by rfl) ⟨685476, by rfl⟩ : syracuseStep 1827937 = 1370953) B1370953
theorem B7398553 : Blo 960589 7398553 := bstep (se 2 (by rfl) ⟨2774457, by rfl⟩ : syracuseStep 7398553 = 5548915) B5548915
theorem B5203223 : Blo 960589 5203223 := bstep (se 1 (by rfl) ⟨3902417, by rfl⟩ : syracuseStep 5203223 = 7804835) B7804835
theorem B108291491 : Blo 960589 108291491 := bstep (se 1 (by rfl) ⟨81218618, by rfl⟩ : syracuseStep 108291491 = 162437237) B162437237
theorem B1828271 : Blo 960589 1828271 := bstep (se 1 (by rfl) ⟨1371203, by rfl⟩ : syracuseStep 1828271 = 2742407) B2742407
theorem B8775179 : Blo 960589 8775179 := bstep (se 1 (by rfl) ⟨6581384, by rfl⟩ : syracuseStep 8775179 = 13162769) B13162769
theorem B1369723 : Blo 960589 1369723 := bstep (se 1 (by rfl) ⟨1027292, by rfl⟩ : syracuseStep 1369723 = 2054585) B2054585
theorem B7301177 : Blo 960589 7301177 := bstep (se 2 (by rfl) ⟨2737941, by rfl⟩ : syracuseStep 7301177 = 5475883) B5475883
theorem B13887587 : Blo 960589 13887587 := bstep (se 1 (by rfl) ⟨10415690, by rfl⟩ : syracuseStep 13887587 = 20831381) B20831381
theorem B1829395 : Blo 960589 1829395 := bstep (se 1 (by rfl) ⟨1372046, by rfl⟩ : syracuseStep 1829395 = 2744093) B2744093
theorem B6154811 : Blo 960589 6154811 := bstep (se 1 (by rfl) ⟨4616108, by rfl⟩ : syracuseStep 6154811 = 9232217) B9232217
theorem B15592013 : Blo 960589 15592013 := bstep (se 3 (by rfl) ⟨2923502, by rfl⟩ : syracuseStep 15592013 = 5847005) B5847005
theorem B6154937 : Blo 960589 6154937 := bstep (se 2 (by rfl) ⟨2308101, by rfl⟩ : syracuseStep 6154937 = 4616203) B4616203
theorem B4877009 : Blo 960589 4877009 := bstep (se 2 (by rfl) ⟨1828878, by rfl⟩ : syracuseStep 4877009 = 3657757) B3657757
theorem B1829623 : Blo 960589 1829623 := bstep (se 1 (by rfl) ⟨1372217, by rfl⟩ : syracuseStep 1829623 = 2744435) B2744435
theorem B2059283 : Blo 960589 2059283 := bstep (se 1 (by rfl) ⟨1544462, by rfl⟩ : syracuseStep 2059283 = 3088925) B3088925
theorem B1829927 : Blo 960589 1829927 := bstep (se 1 (by rfl) ⟨1372445, by rfl⟩ : syracuseStep 1829927 = 2744891) B2744891
theorem B1371215 : Blo 960589 1371215 := bstep (se 1 (by rfl) ⟨1028411, by rfl⟩ : syracuseStep 1371215 = 2056823) B2056823
theorem B1731755 : Blo 960589 1731755 := bstep (se 1 (by rfl) ⟨1298816, by rfl⟩ : syracuseStep 1731755 = 2597633) B2597633
theorem B6155837 : Blo 960589 6155837 := bstep (se 3 (by rfl) ⟨1154219, by rfl⟩ : syracuseStep 6155837 = 2308439) B2308439
theorem B7303121 : Blo 960589 7303121 := bstep (se 2 (by rfl) ⟨2738670, by rfl⟩ : syracuseStep 7303121 = 5477341) B5477341
theorem B3895411 : Blo 960589 3895411 := bstep (se 1 (by rfl) ⟨2921558, by rfl⟩ : syracuseStep 3895411 = 5843117) B5843117
theorem B3699323 : Blo 960589 3699323 := bstep (se 1 (by rfl) ⟨2774492, by rfl⟩ : syracuseStep 3699323 = 5548985) B5548985
theorem B4879439 : Blo 960589 4879439 := bstep (se 1 (by rfl) ⟨3659579, by rfl⟩ : syracuseStep 4879439 = 7319159) B7319159
theorem B1733729 : Blo 960589 1733729 := bstep (se 2 (by rfl) ⟨650148, by rfl⟩ : syracuseStep 1733729 = 1300297) B1300297
theorem B3077519 : Blo 960589 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B35124929 : Blo 960589 35124929 := bstep (se 2 (by rfl) ⟨13171848, by rfl⟩ : syracuseStep 35124929 = 26343697) B26343697
theorem B4880087 : Blo 960589 4880087 := bstep (se 1 (by rfl) ⟨3660065, by rfl⟩ : syracuseStep 4880087 = 7320131) B7320131
theorem B6944545 : Blo 960589 6944545 := bstep (se 2 (by rfl) ⟨2604204, by rfl⟩ : syracuseStep 6944545 = 5208409) B5208409
theorem B5863211 : Blo 960589 5863211 := bstep (se 1 (by rfl) ⟨4397408, by rfl⟩ : syracuseStep 5863211 = 8794817) B8794817
theorem B8222573 : Blo 960589 8222573 := bstep (se 3 (by rfl) ⟨1541732, by rfl⟩ : syracuseStep 8222573 = 3083465) B3083465
theorem B9238481 : Blo 960589 9238481 := bstep (se 2 (by rfl) ⟨3464430, by rfl⟩ : syracuseStep 9238481 = 6928861) B6928861
theorem B3701135 : Blo 960589 3701135 := bstep (se 1 (by rfl) ⟨2775851, by rfl⟩ : syracuseStep 3701135 = 5551703) B5551703
theorem B6584813 : Blo 960589 6584813 := bstep (se 3 (by rfl) ⟨1234652, by rfl⟩ : syracuseStep 6584813 = 2469305) B2469305
theorem B3242483 : Blo 960589 3242483 := bstep (se 1 (by rfl) ⟨2431862, by rfl⟩ : syracuseStep 3242483 = 4863725) B4863725
theorem B13367987 : Blo 960589 13367987 := bstep (se 1 (by rfl) ⟨10025990, by rfl⟩ : syracuseStep 13367987 = 20051981) B20051981
theorem B8321737 : Blo 960589 8321737 := bstep (se 2 (by rfl) ⟨3120651, by rfl⟩ : syracuseStep 8321737 = 6241303) B6241303
theorem B2161583 : Blo 960589 2161583 := bstep (se 1 (by rfl) ⟨1621187, by rfl⟩ : syracuseStep 2161583 = 3242375) B3242375
theorem B3243023 : Blo 960589 3243023 := bstep (se 1 (by rfl) ⟨2432267, by rfl⟩ : syracuseStep 3243023 = 4864535) B4864535
theorem B6945871 : Blo 960589 6945871 := bstep (se 1 (by rfl) ⟨5209403, by rfl⟩ : syracuseStep 6945871 = 10418807) B10418807
theorem B2161835 : Blo 960589 2161835 := bstep (se 1 (by rfl) ⟨1621376, by rfl⟩ : syracuseStep 2161835 = 3242753) B3242753
theorem B4619663 : Blo 960589 4619663 := bstep (se 1 (by rfl) ⟨3464747, by rfl⟩ : syracuseStep 4619663 = 6929495) B6929495
theorem B1080751 : Blo 960589 1080751 := bstep (se 1 (by rfl) ⟨810563, by rfl⟩ : syracuseStep 1080751 = 1621127) B1621127
theorem B1441199 : Blo 960589 1441199 := bstep (se 1 (by rfl) ⟨1080899, by rfl⟩ : syracuseStep 1441199 = 2161799) B2161799
theorem B31227353 : Blo 960589 31227353 := bstep (se 2 (by rfl) ⟨11710257, by rfl⟩ : syracuseStep 31227353 = 23420515) B23420515
theorem B118357469 : Blo 960589 118357469 := bstep (se 3 (by rfl) ⟨22192025, by rfl⟩ : syracuseStep 118357469 = 44384051) B44384051
theorem B1441289 : Blo 960589 1441289 := bstep (se 2 (by rfl) ⟨540483, by rfl⟩ : syracuseStep 1441289 = 1080967) B1080967
theorem B5471783 : Blo 960589 5471783 := bstep (se 1 (by rfl) ⟨4103837, by rfl⟩ : syracuseStep 5471783 = 8207675) B8207675
theorem B1441319 : Blo 960589 1441319 := bstep (se 1 (by rfl) ⟨1080989, by rfl⟩ : syracuseStep 1441319 = 2161979) B2161979
theorem B6159959 : Blo 960589 6159959 := bstep (se 1 (by rfl) ⟨4619969, by rfl⟩ : syracuseStep 6159959 = 9239939) B9239939
theorem B6946391 : Blo 960589 6946391 := bstep (se 1 (by rfl) ⟨5209793, by rfl⟩ : syracuseStep 6946391 = 10419587) B10419587
theorem B3243617 : Blo 960589 3243617 := bstep (se 2 (by rfl) ⟨1216356, by rfl⟩ : syracuseStep 3243617 = 2432713) B2432713
theorem B1441403 : Blo 960589 1441403 := bstep (se 1 (by rfl) ⟨1081052, by rfl⟩ : syracuseStep 1441403 = 2162105) B2162105
theorem B11697803 : Blo 960589 11697803 := bstep (se 1 (by rfl) ⟨8773352, by rfl⟩ : syracuseStep 11697803 = 17546705) B17546705
theorem B2162375 : Blo 960589 2162375 := bstep (se 1 (by rfl) ⟨1621781, by rfl⟩ : syracuseStep 2162375 = 3243563) B3243563
theorem B8781533 : Blo 960589 8781533 := bstep (se 3 (by rfl) ⟨1646537, by rfl⟩ : syracuseStep 8781533 = 3293075) B3293075
theorem B1441529 : Blo 960589 1441529 := bstep (se 2 (by rfl) ⟨540573, by rfl⟩ : syracuseStep 1441529 = 1081147) B1081147
theorem B3473225 : Blo 960589 3473225 := bstep (se 2 (by rfl) ⟨1302459, by rfl⟩ : syracuseStep 3473225 = 2604919) B2604919
theorem B1081183 : Blo 960589 1081183 := bstep (se 1 (by rfl) ⟨810887, by rfl⟩ : syracuseStep 1081183 = 1621775) B1621775
theorem B1441631 : Blo 960589 1441631 := bstep (se 1 (by rfl) ⟨1081223, by rfl⟩ : syracuseStep 1441631 = 2162447) B2162447
theorem B1441643 : Blo 960589 1441643 := bstep (se 1 (by rfl) ⟨1081232, by rfl⟩ : syracuseStep 1441643 = 2162465) B2162465
theorem B3473513 : Blo 960589 3473513 := bstep (se 2 (by rfl) ⟨1302567, by rfl⟩ : syracuseStep 3473513 = 2605135) B2605135
theorem B5472467 : Blo 960589 5472467 := bstep (se 1 (by rfl) ⟨4104350, by rfl⟩ : syracuseStep 5472467 = 8208701) B8208701
theorem B1442057 : Blo 960589 1442057 := bstep (se 2 (by rfl) ⟨540771, by rfl⟩ : syracuseStep 1442057 = 1081543) B1081543
theorem B1442159 : Blo 960589 1442159 := bstep (se 1 (by rfl) ⟨1081619, by rfl⟩ : syracuseStep 1442159 = 2163239) B2163239
theorem B1081723 : Blo 960589 1081723 := bstep (se 1 (by rfl) ⟨811292, by rfl⟩ : syracuseStep 1081723 = 1622585) B1622585
theorem B1442375 : Blo 960589 1442375 := bstep (se 1 (by rfl) ⟨1081781, by rfl⟩ : syracuseStep 1442375 = 2163563) B2163563
theorem B1442411 : Blo 960589 1442411 := bstep (se 1 (by rfl) ⟨1081808, by rfl⟩ : syracuseStep 1442411 = 2163617) B2163617
theorem B3244697 : Blo 960589 3244697 := bstep (se 2 (by rfl) ⟨1216761, by rfl⟩ : syracuseStep 3244697 = 2433523) B2433523
theorem B1737391 : Blo 960589 1737391 := bstep (se 1 (by rfl) ⟨1303043, by rfl⟩ : syracuseStep 1737391 = 2606087) B2606087
theorem B2163383 : Blo 960589 2163383 := bstep (se 1 (by rfl) ⟨1622537, by rfl⟩ : syracuseStep 2163383 = 3245075) B3245075
theorem B1442639 : Blo 960589 1442639 := bstep (se 1 (by rfl) ⟨1081979, by rfl⟩ : syracuseStep 1442639 = 2163959) B2163959
theorem B1082191 : Blo 960589 1082191 := bstep (se 1 (by rfl) ⟨811643, by rfl⟩ : syracuseStep 1082191 = 1623287) B1623287
theorem B2163599 : Blo 960589 2163599 := bstep (se 1 (by rfl) ⟨1622699, by rfl⟩ : syracuseStep 2163599 = 3245399) B3245399
theorem B3081415 : Blo 960589 3081415 := bstep (se 1 (by rfl) ⟨2311061, by rfl⟩ : syracuseStep 3081415 = 4622123) B4622123
theorem B3900631 : Blo 960589 3900631 := bstep (se 1 (by rfl) ⟨2925473, by rfl⟩ : syracuseStep 3900631 = 5850947) B5850947
theorem B1443035 : Blo 960589 1443035 := bstep (se 1 (by rfl) ⟨1082276, by rfl⟩ : syracuseStep 1443035 = 2164553) B2164553
theorem B1082587 : Blo 960589 1082587 := bstep (se 1 (by rfl) ⟨811940, by rfl⟩ : syracuseStep 1082587 = 1623881) B1623881
theorem B3474665 : Blo 960589 3474665 := bstep (se 2 (by rfl) ⟨1302999, by rfl⟩ : syracuseStep 3474665 = 2605999) B2605999
theorem B5211479 : Blo 960589 5211479 := bstep (se 1 (by rfl) ⟨3908609, by rfl⟩ : syracuseStep 5211479 = 7817219) B7817219
theorem B2196833 : Blo 960589 2196833 := bstep (se 2 (by rfl) ⟨823812, by rfl⟩ : syracuseStep 2196833 = 1647625) B1647625
theorem B1443209 : Blo 960589 1443209 := bstep (se 2 (by rfl) ⟨541203, by rfl⟩ : syracuseStep 1443209 = 1082407) B1082407
theorem B3900811 : Blo 960589 3900811 := bstep (se 1 (by rfl) ⟨2925608, by rfl⟩ : syracuseStep 3900811 = 5851217) B5851217
theorem B1082875 : Blo 960589 1082875 := bstep (se 1 (by rfl) ⟨812156, by rfl⟩ : syracuseStep 1082875 = 1624313) B1624313
theorem B9864737 : Blo 960589 9864737 := bstep (se 2 (by rfl) ⟨3699276, by rfl⟩ : syracuseStep 9864737 = 7398553) B7398553
theorem B2164319 : Blo 960589 2164319 := bstep (se 1 (by rfl) ⟨1623239, by rfl⟩ : syracuseStep 2164319 = 3246479) B3246479
theorem B1083055 : Blo 960589 1083055 := bstep (se 1 (by rfl) ⟨812291, by rfl⟩ : syracuseStep 1083055 = 1624583) B1624583
theorem B1443563 : Blo 960589 1443563 := bstep (se 1 (by rfl) ⟨1082672, by rfl⟩ : syracuseStep 1443563 = 2165345) B2165345
theorem B2164535 : Blo 960589 2164535 := bstep (se 1 (by rfl) ⟨1623401, by rfl⟩ : syracuseStep 2164535 = 3246803) B3246803
theorem B1443791 : Blo 960589 1443791 := bstep (se 1 (by rfl) ⟨1082843, by rfl⟩ : syracuseStep 1443791 = 2165687) B2165687
theorem B1083343 : Blo 960589 1083343 := bstep (se 1 (by rfl) ⟨812507, by rfl⟩ : syracuseStep 1083343 = 1625015) B1625015
theorem B2164841 : Blo 960589 2164841 := bstep (se 2 (by rfl) ⟨811815, by rfl⟩ : syracuseStep 2164841 = 1623631) B1623631
theorem B3246209 : Blo 960589 3246209 := bstep (se 2 (by rfl) ⟨1217328, by rfl⟩ : syracuseStep 3246209 = 2434657) B2434657
theorem B1444187 : Blo 960589 1444187 := bstep (se 1 (by rfl) ⟨1083140, by rfl⟩ : syracuseStep 1444187 = 2166281) B2166281
theorem B1083739 : Blo 960589 1083739 := bstep (se 1 (by rfl) ⟨812804, by rfl⟩ : syracuseStep 1083739 = 1625609) B1625609
theorem B1083847 : Blo 960589 1083847 := bstep (se 1 (by rfl) ⟨812885, by rfl⟩ : syracuseStep 1083847 = 1625771) B1625771
theorem B3246587 : Blo 960589 3246587 := bstep (se 1 (by rfl) ⟨2434940, by rfl⟩ : syracuseStep 3246587 = 4869881) B4869881
theorem B3475963 : Blo 960589 3475963 := bstep (se 1 (by rfl) ⟨2606972, by rfl⟩ : syracuseStep 3475963 = 5213945) B5213945
theorem B1444415 : Blo 960589 1444415 := bstep (se 1 (by rfl) ⟨1083311, by rfl⟩ : syracuseStep 1444415 = 2166623) B2166623
theorem B2165327 : Blo 960589 2165327 := bstep (se 1 (by rfl) ⟨1623995, by rfl⟩ : syracuseStep 2165327 = 3247991) B3247991
theorem B1444535 : Blo 960589 1444535 := bstep (se 1 (by rfl) ⟨1083401, by rfl⟩ : syracuseStep 1444535 = 2166803) B2166803
theorem B2165471 : Blo 960589 2165471 := bstep (se 1 (by rfl) ⟨1624103, by rfl⟩ : syracuseStep 2165471 = 3248207) B3248207
theorem B1084207 : Blo 960589 1084207 := bstep (se 1 (by rfl) ⟨813155, by rfl⟩ : syracuseStep 1084207 = 1626311) B1626311
theorem B1444763 : Blo 960589 1444763 := bstep (se 1 (by rfl) ⟨1083572, by rfl⟩ : syracuseStep 1444763 = 2167145) B2167145
theorem B1084315 : Blo 960589 1084315 := bstep (se 1 (by rfl) ⟨813236, by rfl⟩ : syracuseStep 1084315 = 1626473) B1626473
theorem B3247019 : Blo 960589 3247019 := bstep (se 1 (by rfl) ⟨2435264, by rfl⟩ : syracuseStep 3247019 = 4870529) B4870529
theorem B4623277 : Blo 960589 4623277 := bstep (se 3 (by rfl) ⟨866864, by rfl⟩ : syracuseStep 4623277 = 1733729) B1733729
theorem B2165723 : Blo 960589 2165723 := bstep (se 1 (by rfl) ⟨1624292, by rfl⟩ : syracuseStep 2165723 = 3248585) B3248585
theorem B2165903 : Blo 960589 2165903 := bstep (se 1 (by rfl) ⟨1624427, by rfl⟩ : syracuseStep 2165903 = 3248855) B3248855
theorem B2165993 : Blo 960589 2165993 := bstep (se 2 (by rfl) ⟨812247, by rfl⟩ : syracuseStep 2165993 = 1624495) B1624495
theorem B2166047 : Blo 960589 2166047 := bstep (se 1 (by rfl) ⟨1624535, by rfl⟩ : syracuseStep 2166047 = 3249071) B3249071
theorem B1445159 : Blo 960589 1445159 := bstep (se 1 (by rfl) ⟨1083869, by rfl⟩ : syracuseStep 1445159 = 2167739) B2167739
theorem B1084711 : Blo 960589 1084711 := bstep (se 1 (by rfl) ⟨813533, by rfl⟩ : syracuseStep 1084711 = 1627067) B1627067
theorem B1084783 : Blo 960589 1084783 := bstep (se 1 (by rfl) ⟨813587, by rfl⟩ : syracuseStep 1084783 = 1627175) B1627175
theorem B1445243 : Blo 960589 1445243 := bstep (se 1 (by rfl) ⟨1083932, by rfl⟩ : syracuseStep 1445243 = 2167865) B2167865
theorem B1215911 : Blo 960589 1215911 := bstep (se 1 (by rfl) ⟨911933, by rfl⟩ : syracuseStep 1215911 = 1823867) B1823867
theorem B3247559 : Blo 960589 3247559 := bstep (se 1 (by rfl) ⟨2435669, by rfl⟩ : syracuseStep 3247559 = 4871339) B4871339
theorem B1445369 : Blo 960589 1445369 := bstep (se 2 (by rfl) ⟨542013, by rfl⟩ : syracuseStep 1445369 = 1084027) B1084027
theorem B1216063 : Blo 960589 1216063 := bstep (se 1 (by rfl) ⟨912047, by rfl⟩ : syracuseStep 1216063 = 1824095) B1824095
theorem B1084999 : Blo 960589 1084999 := bstep (se 1 (by rfl) ⟨813749, by rfl⟩ : syracuseStep 1084999 = 1627499) B1627499
theorem B1445471 : Blo 960589 1445471 := bstep (se 1 (by rfl) ⟨1084103, by rfl⟩ : syracuseStep 1445471 = 2168207) B2168207
theorem B1216235 : Blo 960589 1216235 := bstep (se 1 (by rfl) ⟨912176, by rfl⟩ : syracuseStep 1216235 = 1824353) B1824353
theorem B8228587 : Blo 960589 8228587 := bstep (se 1 (by rfl) ⟨6171440, by rfl⟩ : syracuseStep 8228587 = 12342881) B12342881
theorem B3247883 : Blo 960589 3247883 := bstep (se 1 (by rfl) ⟨2435912, by rfl⟩ : syracuseStep 3247883 = 4871825) B4871825
theorem B23432975 : Blo 960589 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B2166569 : Blo 960589 2166569 := bstep (se 2 (by rfl) ⟨812463, by rfl⟩ : syracuseStep 2166569 = 1624927) B1624927
theorem B18779951 : Blo 960589 18779951 := bstep (se 1 (by rfl) ⟨14084963, by rfl⟩ : syracuseStep 18779951 = 28169927) B28169927
theorem B1445687 : Blo 960589 1445687 := bstep (se 1 (by rfl) ⟨1084265, by rfl⟩ : syracuseStep 1445687 = 2168531) B2168531
theorem B3248153 : Blo 960589 3248153 := bstep (se 2 (by rfl) ⟨1218057, by rfl⟩ : syracuseStep 3248153 = 2436115) B2436115
theorem B1445993 : Blo 960589 1445993 := bstep (se 2 (by rfl) ⟨542247, by rfl⟩ : syracuseStep 1445993 = 1084495) B1084495
theorem B1446311 : Blo 960589 1446311 := bstep (se 1 (by rfl) ⟨1084733, by rfl⟩ : syracuseStep 1446311 = 2169467) B2169467
theorem B1446395 : Blo 960589 1446395 := bstep (se 1 (by rfl) ⟨1084796, by rfl⟩ : syracuseStep 1446395 = 2169593) B2169593
theorem B1446521 : Blo 960589 1446521 := bstep (se 2 (by rfl) ⟨542445, by rfl⟩ : syracuseStep 1446521 = 1084891) B1084891
theorem B1446575 : Blo 960589 1446575 := bstep (se 1 (by rfl) ⟨1084931, by rfl⟩ : syracuseStep 1446575 = 2169863) B2169863
theorem B1217207 : Blo 960589 1217207 := bstep (se 1 (by rfl) ⟨912905, by rfl⟩ : syracuseStep 1217207 = 1825811) B1825811
theorem B1446623 : Blo 960589 1446623 := bstep (se 1 (by rfl) ⟨1084967, by rfl⟩ : syracuseStep 1446623 = 2169935) B2169935
theorem B1217359 : Blo 960589 1217359 := bstep (se 1 (by rfl) ⟨913019, by rfl⟩ : syracuseStep 1217359 = 1826039) B1826039
theorem B2167631 : Blo 960589 2167631 := bstep (se 1 (by rfl) ⟨1625723, by rfl⟩ : syracuseStep 2167631 = 3251447) B3251447
theorem B2167847 : Blo 960589 2167847 := bstep (se 1 (by rfl) ⟨1625885, by rfl⟩ : syracuseStep 2167847 = 3251771) B3251771
theorem B15602777 : Blo 960589 15602777 := bstep (se 2 (by rfl) ⟨5851041, by rfl⟩ : syracuseStep 15602777 = 11702083) B11702083
theorem B2168027 : Blo 960589 2168027 := bstep (se 1 (by rfl) ⟨1626020, by rfl⟩ : syracuseStep 2168027 = 3252041) B3252041
theorem B3249395 : Blo 960589 3249395 := bstep (se 1 (by rfl) ⟨2437046, by rfl⟩ : syracuseStep 3249395 = 4874093) B4874093
theorem B3085607 : Blo 960589 3085607 := bstep (se 1 (by rfl) ⟨2314205, by rfl⟩ : syracuseStep 3085607 = 4628411) B4628411
theorem B4166999 : Blo 960589 4166999 := bstep (se 1 (by rfl) ⟨3125249, by rfl⟩ : syracuseStep 4166999 = 6250499) B6250499
theorem B3249503 : Blo 960589 3249503 := bstep (se 1 (by rfl) ⟨2437127, by rfl⟩ : syracuseStep 3249503 = 4874255) B4874255
theorem B2168225 : Blo 960589 2168225 := bstep (se 2 (by rfl) ⟨813084, by rfl⟩ : syracuseStep 2168225 = 1626169) B1626169
theorem B2168783 : Blo 960589 2168783 := bstep (se 1 (by rfl) ⟨1626587, by rfl⟩ : syracuseStep 2168783 = 3253175) B3253175
theorem B16685189 : Blo 960589 16685189 := bstep (se 4 (by rfl) ⟨1564236, by rfl⟩ : syracuseStep 16685189 = 3128473) B3128473
theorem B72194327 : Blo 960589 72194327 := bstep (se 1 (by rfl) ⟨54145745, by rfl⟩ : syracuseStep 72194327 = 108291491) B108291491
theorem B2169161 : Blo 960589 2169161 := bstep (se 2 (by rfl) ⟨813435, by rfl⟩ : syracuseStep 2169161 = 1626871) B1626871
theorem B2169179 : Blo 960589 2169179 := bstep (se 1 (by rfl) ⟨1626884, by rfl⟩ : syracuseStep 2169179 = 3253769) B3253769
theorem B2431559 : Blo 960589 2431559 := bstep (se 1 (by rfl) ⟨1823669, by rfl⟩ : syracuseStep 2431559 = 3647339) B3647339
theorem B3251069 : Blo 960589 3251069 := bstep (se 3 (by rfl) ⟨609575, by rfl⟩ : syracuseStep 3251069 = 1219151) B1219151
theorem B3087247 : Blo 960589 3087247 := bstep (se 1 (by rfl) ⟨2315435, by rfl⟩ : syracuseStep 3087247 = 4630871) B4630871
theorem B2169755 : Blo 960589 2169755 := bstep (se 1 (by rfl) ⟨1627316, by rfl⟩ : syracuseStep 2169755 = 3254633) B3254633
theorem B4103207 : Blo 960589 4103207 := bstep (se 1 (by rfl) ⟨3077405, by rfl⟩ : syracuseStep 4103207 = 6154811) B6154811
theorem B10394675 : Blo 960589 10394675 := bstep (se 1 (by rfl) ⟨7796006, by rfl⟩ : syracuseStep 10394675 = 15592013) B15592013
theorem B2169953 : Blo 960589 2169953 := bstep (se 2 (by rfl) ⟨813732, by rfl⟩ : syracuseStep 2169953 = 1627465) B1627465
theorem B4103291 : Blo 960589 4103291 := bstep (se 1 (by rfl) ⟨3077468, by rfl⟩ : syracuseStep 4103291 = 6154937) B6154937
theorem B3251339 : Blo 960589 3251339 := bstep (se 1 (by rfl) ⟨2438504, by rfl⟩ : syracuseStep 3251339 = 4877009) B4877009
theorem B2170151 : Blo 960589 2170151 := bstep (se 1 (by rfl) ⟨1627613, by rfl⟩ : syracuseStep 2170151 = 3255227) B3255227
theorem B1219951 : Blo 960589 1219951 := bstep (se 1 (by rfl) ⟨914963, by rfl⟩ : syracuseStep 1219951 = 1829927) B1829927
theorem B1154503 : Blo 960589 1154503 := bstep (se 1 (by rfl) ⟨865877, by rfl⟩ : syracuseStep 1154503 = 1731755) B1731755
theorem B4103891 : Blo 960589 4103891 := bstep (se 1 (by rfl) ⟨3077918, by rfl⟩ : syracuseStep 4103891 = 6155837) B6155837
theorem B2432825 : Blo 960589 2432825 := bstep (se 2 (by rfl) ⟨912309, by rfl⟩ : syracuseStep 2432825 = 1824619) B1824619
theorem B3088489 : Blo 960589 3088489 := bstep (se 2 (by rfl) ⟨1158183, by rfl⟩ : syracuseStep 3088489 = 2316367) B2316367
theorem B2466215 : Blo 960589 2466215 := bstep (se 1 (by rfl) ⟨1849661, by rfl⟩ : syracuseStep 2466215 = 3699323) B3699323
theorem B3252959 : Blo 960589 3252959 := bstep (se 1 (by rfl) ⟨2439719, by rfl⟩ : syracuseStep 3252959 = 4879439) B4879439
theorem B2434171 : Blo 960589 2434171 := bstep (se 1 (by rfl) ⟨1825628, by rfl⟩ : syracuseStep 2434171 = 3651257) B3651257
theorem B3253391 : Blo 960589 3253391 := bstep (se 1 (by rfl) ⟨2440043, by rfl⟩ : syracuseStep 3253391 = 4880087) B4880087
theorem B3908807 : Blo 960589 3908807 := bstep (se 1 (by rfl) ⟨2931605, by rfl⟩ : syracuseStep 3908807 = 5863211) B5863211
theorem B5481715 : Blo 960589 5481715 := bstep (se 1 (by rfl) ⟨4111286, by rfl⟩ : syracuseStep 5481715 = 8222573) B8222573
theorem B2467423 : Blo 960589 2467423 := bstep (se 1 (by rfl) ⟨1850567, by rfl⟩ : syracuseStep 2467423 = 3701135) B3701135
theorem B3254525 : Blo 960589 3254525 := bstep (se 3 (by rfl) ⟨610223, by rfl⟩ : syracuseStep 3254525 = 1220447) B1220447
theorem B960799 : Blo 960589 960799 := bstep (se 1 (by rfl) ⟨720599, by rfl⟩ : syracuseStep 960799 = 1441199) B1441199
theorem B20818235 : Blo 960589 20818235 := bstep (se 1 (by rfl) ⟨15613676, by rfl⟩ : syracuseStep 20818235 = 31227353) B31227353
theorem B960859 : Blo 960589 960859 := bstep (se 1 (by rfl) ⟨720644, by rfl⟩ : syracuseStep 960859 = 1441289) B1441289
theorem B3647855 : Blo 960589 3647855 := bstep (se 1 (by rfl) ⟨2735891, by rfl⟩ : syracuseStep 3647855 = 5471783) B5471783
theorem B960879 : Blo 960589 960879 := bstep (se 1 (by rfl) ⟨720659, by rfl⟩ : syracuseStep 960879 = 1441319) B1441319
theorem B4630927 : Blo 960589 4630927 := bstep (se 1 (by rfl) ⟨3473195, by rfl⟩ : syracuseStep 4630927 = 6946391) B6946391
theorem B4106639 : Blo 960589 4106639 := bstep (se 1 (by rfl) ⟨3079979, by rfl⟩ : syracuseStep 4106639 = 6159959) B6159959
theorem B960935 : Blo 960589 960935 := bstep (se 1 (by rfl) ⟨720701, by rfl⟩ : syracuseStep 960935 = 1441403) B1441403
theorem B961019 : Blo 960589 961019 := bstep (se 1 (by rfl) ⟨720764, by rfl⟩ : syracuseStep 961019 = 1441529) B1441529
theorem B4336123 : Blo 960589 4336123 := bstep (se 1 (by rfl) ⟨3252092, by rfl⟩ : syracuseStep 4336123 = 6504185) B6504185
theorem B2435579 : Blo 960589 2435579 := bstep (se 1 (by rfl) ⟨1826684, by rfl⟩ : syracuseStep 2435579 = 3653369) B3653369
theorem B961087 : Blo 960589 961087 := bstep (se 1 (by rfl) ⟨720815, by rfl⟩ : syracuseStep 961087 = 1441631) B1441631
theorem B961095 : Blo 960589 961095 := bstep (se 1 (by rfl) ⟨720821, by rfl⟩ : syracuseStep 961095 = 1441643) B1441643
theorem B42740405 : Blo 960589 42740405 := bstep (se 5 (by rfl) ⟨2003456, by rfl⟩ : syracuseStep 42740405 = 4006913) B4006913
theorem B961247 : Blo 960589 961247 := bstep (se 1 (by rfl) ⟨720935, by rfl⟩ : syracuseStep 961247 = 1441871) B1441871
theorem B961327 : Blo 960589 961327 := bstep (se 1 (by rfl) ⟨720995, by rfl⟩ : syracuseStep 961327 = 1441991) B1441991
theorem B961435 : Blo 960589 961435 := bstep (se 1 (by rfl) ⟨721076, by rfl⟩ : syracuseStep 961435 = 1442153) B1442153
theorem B961487 : Blo 960589 961487 := bstep (se 1 (by rfl) ⟨721115, by rfl⟩ : syracuseStep 961487 = 1442231) B1442231
theorem B961511 : Blo 960589 961511 := bstep (se 1 (by rfl) ⟨721133, by rfl⟩ : syracuseStep 961511 = 1442267) B1442267
theorem B3255335 : Blo 960589 3255335 := bstep (se 1 (by rfl) ⟨2441501, by rfl⟩ : syracuseStep 3255335 = 4883003) B4883003
theorem B8793359 : Blo 960589 8793359 := bstep (se 1 (by rfl) ⟨6595019, by rfl⟩ : syracuseStep 8793359 = 13190039) B13190039
theorem B961823 : Blo 960589 961823 := bstep (se 1 (by rfl) ⟨721367, by rfl⟩ : syracuseStep 961823 = 1442735) B1442735
theorem B4107581 : Blo 960589 4107581 := bstep (se 3 (by rfl) ⟨770171, by rfl⟩ : syracuseStep 4107581 = 1540343) B1540343
theorem B961883 : Blo 960589 961883 := bstep (se 1 (by rfl) ⟨721412, by rfl⟩ : syracuseStep 961883 = 1442825) B1442825
theorem B961903 : Blo 960589 961903 := bstep (se 1 (by rfl) ⟨721427, by rfl⟩ : syracuseStep 961903 = 1442855) B1442855
theorem B961959 : Blo 960589 961959 := bstep (se 1 (by rfl) ⟨721469, by rfl⟩ : syracuseStep 961959 = 1442939) B1442939
theorem B2436551 : Blo 960589 2436551 := bstep (se 1 (by rfl) ⟨1827413, by rfl⟩ : syracuseStep 2436551 = 3654827) B3654827
theorem B2436601 : Blo 960589 2436601 := bstep (se 2 (by rfl) ⟨913725, by rfl⟩ : syracuseStep 2436601 = 1827451) B1827451
theorem B962043 : Blo 960589 962043 := bstep (se 1 (by rfl) ⟨721532, by rfl⟩ : syracuseStep 962043 = 1443065) B1443065
theorem B962111 : Blo 960589 962111 := bstep (se 1 (by rfl) ⟨721583, by rfl⟩ : syracuseStep 962111 = 1443167) B1443167
theorem B962119 : Blo 960589 962119 := bstep (se 1 (by rfl) ⟨721589, by rfl⟩ : syracuseStep 962119 = 1443179) B1443179
theorem B16428743 : Blo 960589 16428743 := bstep (se 1 (by rfl) ⟨12321557, by rfl⟩ : syracuseStep 16428743 = 24643115) B24643115
theorem B962271 : Blo 960589 962271 := bstep (se 1 (by rfl) ⟨721703, by rfl⟩ : syracuseStep 962271 = 1443407) B1443407
theorem B2436905 : Blo 960589 2436905 := bstep (se 2 (by rfl) ⟨913839, by rfl⟩ : syracuseStep 2436905 = 1827679) B1827679
theorem B962351 : Blo 960589 962351 := bstep (se 1 (by rfl) ⟨721763, by rfl⟩ : syracuseStep 962351 = 1443527) B1443527
theorem B962459 : Blo 960589 962459 := bstep (se 1 (by rfl) ⟨721844, by rfl⟩ : syracuseStep 962459 = 1443689) B1443689
theorem B962511 : Blo 960589 962511 := bstep (se 1 (by rfl) ⟨721883, by rfl⟩ : syracuseStep 962511 = 1443767) B1443767
theorem B962535 : Blo 960589 962535 := bstep (se 1 (by rfl) ⟨721901, by rfl⟩ : syracuseStep 962535 = 1443803) B1443803
theorem B2437249 : Blo 960589 2437249 := bstep (se 2 (by rfl) ⟨913968, by rfl⟩ : syracuseStep 2437249 = 1827937) B1827937
theorem B5353675 : Blo 960589 5353675 := bstep (se 1 (by rfl) ⟨4015256, by rfl⟩ : syracuseStep 5353675 = 8030513) B8030513
theorem B20820239 : Blo 960589 20820239 := bstep (se 1 (by rfl) ⟨15615179, by rfl⟩ : syracuseStep 20820239 = 31230359) B31230359
theorem B962847 : Blo 960589 962847 := bstep (se 1 (by rfl) ⟨722135, by rfl⟩ : syracuseStep 962847 = 1444271) B1444271
theorem B962907 : Blo 960589 962907 := bstep (se 1 (by rfl) ⟨722180, by rfl⟩ : syracuseStep 962907 = 1444361) B1444361
theorem B962927 : Blo 960589 962927 := bstep (se 1 (by rfl) ⟨722195, by rfl⟩ : syracuseStep 962927 = 1444391) B1444391
theorem B962983 : Blo 960589 962983 := bstep (se 1 (by rfl) ⟨722237, by rfl⟩ : syracuseStep 962983 = 1444475) B1444475
theorem B3649967 : Blo 960589 3649967 := bstep (se 1 (by rfl) ⟨2737475, by rfl⟩ : syracuseStep 3649967 = 5474951) B5474951
theorem B963067 : Blo 960589 963067 := bstep (se 1 (by rfl) ⟨722300, by rfl⟩ : syracuseStep 963067 = 1444601) B1444601
theorem B963135 : Blo 960589 963135 := bstep (se 1 (by rfl) ⟨722351, by rfl⟩ : syracuseStep 963135 = 1444703) B1444703
theorem B963143 : Blo 960589 963143 := bstep (se 1 (by rfl) ⟨722357, by rfl⟩ : syracuseStep 963143 = 1444715) B1444715
theorem B1979063 : Blo 960589 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B963295 : Blo 960589 963295 := bstep (se 1 (by rfl) ⟨722471, by rfl⟩ : syracuseStep 963295 = 1444943) B1444943
theorem B963375 : Blo 960589 963375 := bstep (se 1 (by rfl) ⟨722531, by rfl⟩ : syracuseStep 963375 = 1445063) B1445063
theorem B963483 : Blo 960589 963483 := bstep (se 1 (by rfl) ⟨722612, by rfl⟩ : syracuseStep 963483 = 1445225) B1445225
theorem B2438059 : Blo 960589 2438059 := bstep (se 1 (by rfl) ⟨1828544, by rfl⟩ : syracuseStep 2438059 = 3657089) B3657089
theorem B963535 : Blo 960589 963535 := bstep (se 1 (by rfl) ⟨722651, by rfl⟩ : syracuseStep 963535 = 1445303) B1445303
theorem B963559 : Blo 960589 963559 := bstep (se 1 (by rfl) ⟨722669, by rfl⟩ : syracuseStep 963559 = 1445339) B1445339
theorem B2438363 : Blo 960589 2438363 := bstep (se 1 (by rfl) ⟨1828772, by rfl⟩ : syracuseStep 2438363 = 3657545) B3657545
theorem B963871 : Blo 960589 963871 := bstep (se 1 (by rfl) ⟨722903, by rfl⟩ : syracuseStep 963871 = 1445807) B1445807
theorem B963931 : Blo 960589 963931 := bstep (se 1 (by rfl) ⟨722948, by rfl⟩ : syracuseStep 963931 = 1445897) B1445897
theorem B2438495 : Blo 960589 2438495 := bstep (se 1 (by rfl) ⟨1828871, by rfl⟩ : syracuseStep 2438495 = 3657743) B3657743
theorem B963951 : Blo 960589 963951 := bstep (se 1 (by rfl) ⟨722963, by rfl⟩ : syracuseStep 963951 = 1445927) B1445927
theorem B3650939 : Blo 960589 3650939 := bstep (se 1 (by rfl) ⟨2738204, by rfl⟩ : syracuseStep 3650939 = 5476409) B5476409
theorem B964007 : Blo 960589 964007 := bstep (se 1 (by rfl) ⟨723005, by rfl⟩ : syracuseStep 964007 = 1446011) B1446011
theorem B964091 : Blo 960589 964091 := bstep (se 1 (by rfl) ⟨723068, by rfl⟩ : syracuseStep 964091 = 1446137) B1446137
theorem B964159 : Blo 960589 964159 := bstep (se 1 (by rfl) ⟨723119, by rfl⟩ : syracuseStep 964159 = 1446239) B1446239
theorem B964167 : Blo 960589 964167 := bstep (se 1 (by rfl) ⟨723125, by rfl⟩ : syracuseStep 964167 = 1446251) B1446251
theorem B964319 : Blo 960589 964319 := bstep (se 1 (by rfl) ⟨723239, by rfl⟩ : syracuseStep 964319 = 1446479) B1446479
theorem B964399 : Blo 960589 964399 := bstep (se 1 (by rfl) ⟨723299, by rfl⟩ : syracuseStep 964399 = 1446599) B1446599
theorem B16463735 : Blo 960589 16463735 := bstep (se 1 (by rfl) ⟨12347801, by rfl⟩ : syracuseStep 16463735 = 24695603) B24695603
theorem B964507 : Blo 960589 964507 := bstep (se 1 (by rfl) ⟨723380, by rfl⟩ : syracuseStep 964507 = 1446761) B1446761
theorem B1030043 : Blo 960589 1030043 := bstep (se 1 (by rfl) ⟨772532, by rfl⟩ : syracuseStep 1030043 = 1545065) B1545065
theorem B48215969 : Blo 960589 48215969 := bstep (se 2 (by rfl) ⟨18080988, by rfl⟩ : syracuseStep 48215969 = 36161977) B36161977
theorem B4110263 : Blo 960589 4110263 := bstep (se 1 (by rfl) ⟨3082697, by rfl⟩ : syracuseStep 4110263 = 6165395) B6165395
theorem B964559 : Blo 960589 964559 := bstep (se 1 (by rfl) ⟨723419, by rfl⟩ : syracuseStep 964559 = 1446839) B1446839
theorem B964583 : Blo 960589 964583 := bstep (se 1 (by rfl) ⟨723437, by rfl⟩ : syracuseStep 964583 = 1446875) B1446875
theorem B2439193 : Blo 960589 2439193 := bstep (se 2 (by rfl) ⟨914697, by rfl⟩ : syracuseStep 2439193 = 1829395) B1829395
theorem B4634657 : Blo 960589 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B3651713 : Blo 960589 3651713 := bstep (se 2 (by rfl) ⟨1369392, by rfl⟩ : syracuseStep 3651713 = 2738785) B2738785
theorem B2439497 : Blo 960589 2439497 := bstep (se 2 (by rfl) ⟨914811, by rfl⟩ : syracuseStep 2439497 = 1829623) B1829623
theorem B8206717 : Blo 960589 8206717 := bstep (se 3 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 8206717 = 3077519) B3077519
theorem B4635535 : Blo 960589 4635535 := bstep (se 1 (by rfl) ⟨3476651, by rfl⟩ : syracuseStep 4635535 = 6953303) B6953303
theorem B5487547 : Blo 960589 5487547 := bstep (se 1 (by rfl) ⟨4115660, by rfl⟩ : syracuseStep 5487547 = 8231321) B8231321
theorem B2472947 : Blo 960589 2472947 := bstep (se 1 (by rfl) ⟨1854710, by rfl⟩ : syracuseStep 2472947 = 3709421) B3709421
theorem B2309563 : Blo 960589 2309563 := bstep (se 1 (by rfl) ⟨1732172, by rfl⟩ : syracuseStep 2309563 = 3464345) B3464345
theorem B8437241 : Blo 960589 8437241 := bstep (se 2 (by rfl) ⟨3163965, by rfl⟩ : syracuseStep 8437241 = 6327931) B6327931
theorem B2309639 : Blo 960589 2309639 := bstep (se 1 (by rfl) ⟨1732229, by rfl⟩ : syracuseStep 2309639 = 3464459) B3464459
theorem B3653201 : Blo 960589 3653201 := bstep (se 2 (by rfl) ⟨1369950, by rfl⟩ : syracuseStep 3653201 = 2739901) B2739901
theorem B4111955 : Blo 960589 4111955 := bstep (se 1 (by rfl) ⟨3083966, by rfl⟩ : syracuseStep 4111955 = 6167933) B6167933
theorem B8797841 : Blo 960589 8797841 := bstep (se 2 (by rfl) ⟨3299190, by rfl⟩ : syracuseStep 8797841 = 6598381) B6598381
theorem B7520003 : Blo 960589 7520003 := bstep (se 1 (by rfl) ⟨5640002, by rfl⟩ : syracuseStep 7520003 = 11280005) B11280005
theorem B3653383 : Blo 960589 3653383 := bstep (se 1 (by rfl) ⟨2740037, by rfl⟩ : syracuseStep 3653383 = 5480075) B5480075
theorem B5193533 : Blo 960589 5193533 := bstep (se 3 (by rfl) ⟨973787, by rfl⟩ : syracuseStep 5193533 = 1947575) B1947575
theorem B2473993 : Blo 960589 2473993 := bstep (se 2 (by rfl) ⟨927747, by rfl⟩ : syracuseStep 2473993 = 1855495) B1855495
theorem B18530315 : Blo 960589 18530315 := bstep (se 1 (by rfl) ⟨13897736, by rfl⟩ : syracuseStep 18530315 = 27795473) B27795473
theorem B3653657 : Blo 960589 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B5193881 : Blo 960589 5193881 := bstep (se 2 (by rfl) ⟨1947705, by rfl⟩ : syracuseStep 5193881 = 3895411) B3895411
theorem B1622281 : Blo 960589 1622281 := bstep (se 2 (by rfl) ⟨608355, by rfl⟩ : syracuseStep 1622281 = 1216711) B1216711
theorem B4866479 : Blo 960589 4866479 := bstep (se 1 (by rfl) ⟨3649859, by rfl⟩ : syracuseStep 4866479 = 7299719) B7299719
theorem B2343647 : Blo 960589 2343647 := bstep (se 1 (by rfl) ⟨1757735, by rfl⟩ : syracuseStep 2343647 = 3515471) B3515471
theorem B8799121 : Blo 960589 8799121 := bstep (se 2 (by rfl) ⟨3299670, by rfl⟩ : syracuseStep 8799121 = 6599341) B6599341
theorem B18465731 : Blo 960589 18465731 := bstep (se 1 (by rfl) ⟨13849298, by rfl⟩ : syracuseStep 18465731 = 27698597) B27698597
theorem B5850119 : Blo 960589 5850119 := bstep (se 1 (by rfl) ⟨4387589, by rfl⟩ : syracuseStep 5850119 = 8775179) B8775179
theorem B2737385 : Blo 960589 2737385 := bstep (se 2 (by rfl) ⟨1026519, by rfl⟩ : syracuseStep 2737385 = 2053039) B2053039
theorem B5489963 : Blo 960589 5489963 := bstep (se 1 (by rfl) ⟨4117472, by rfl⟩ : syracuseStep 5489963 = 8234945) B8234945
theorem B4867451 : Blo 960589 4867451 := bstep (se 1 (by rfl) ⟨3650588, by rfl⟩ : syracuseStep 4867451 = 7301177) B7301177
theorem B9258391 : Blo 960589 9258391 := bstep (se 1 (by rfl) ⟨6943793, by rfl⟩ : syracuseStep 9258391 = 13887587) B13887587
theorem B4113953 : Blo 960589 4113953 := bstep (se 2 (by rfl) ⟨1542732, by rfl⟩ : syracuseStep 4113953 = 3085465) B3085465
theorem B1623739 : Blo 960589 1623739 := bstep (se 1 (by rfl) ⟨1217804, by rfl⟩ : syracuseStep 1623739 = 2435609) B2435609
theorem B3655631 : Blo 960589 3655631 := bstep (se 1 (by rfl) ⟨2741723, by rfl⟩ : syracuseStep 3655631 = 5483447) B5483447
theorem B4114567 : Blo 960589 4114567 := bstep (se 1 (by rfl) ⟨3085925, by rfl⟩ : syracuseStep 4114567 = 6171851) B6171851
theorem B9259393 : Blo 960589 9259393 := bstep (se 2 (by rfl) ⟨3472272, by rfl⟩ : syracuseStep 9259393 = 6944545) B6944545
theorem B3656299 : Blo 960589 3656299 := bstep (se 1 (by rfl) ⟨2742224, by rfl⟩ : syracuseStep 3656299 = 5484449) B5484449
theorem B4868747 : Blo 960589 4868747 := bstep (se 1 (by rfl) ⟨3651560, by rfl⟩ : syracuseStep 4868747 = 7303121) B7303121
theorem B5491421 : Blo 960589 5491421 := bstep (se 3 (by rfl) ⟨1029641, by rfl⟩ : syracuseStep 5491421 = 2059283) B2059283
theorem B1624799 : Blo 960589 1624799 := bstep (se 1 (by rfl) ⟨1218599, by rfl⟩ : syracuseStep 1624799 = 2437199) B2437199
theorem B3656573 : Blo 960589 3656573 := bstep (se 3 (by rfl) ⟨685607, by rfl⟩ : syracuseStep 3656573 = 1371215) B1371215
theorem B3656603 : Blo 960589 3656603 := bstep (se 1 (by rfl) ⟨2742452, by rfl⟩ : syracuseStep 3656603 = 5484905) B5484905
theorem B4115387 : Blo 960589 4115387 := bstep (se 1 (by rfl) ⟨3086540, by rfl⟩ : syracuseStep 4115387 = 6173081) B6173081
theorem B1625231 : Blo 960589 1625231 := bstep (se 1 (by rfl) ⟨1218923, by rfl⟩ : syracuseStep 1625231 = 2437847) B2437847
theorem B1625467 : Blo 960589 1625467 := bstep (se 1 (by rfl) ⟨1219100, by rfl⟩ : syracuseStep 1625467 = 2438201) B2438201
theorem B11095649 : Blo 960589 11095649 := bstep (se 2 (by rfl) ⟨4160868, by rfl⟩ : syracuseStep 11095649 = 8321737) B8321737
theorem B23416619 : Blo 960589 23416619 := bstep (se 1 (by rfl) ⟨17562464, by rfl⟩ : syracuseStep 23416619 = 35124929) B35124929
theorem B13881131 : Blo 960589 13881131 := bstep (se 1 (by rfl) ⟨10410848, by rfl⟩ : syracuseStep 13881131 = 20821697) B20821697
theorem B9261161 : Blo 960589 9261161 := bstep (se 2 (by rfl) ⟨3472935, by rfl⟩ : syracuseStep 9261161 = 6945871) B6945871
theorem B3952849 : Blo 960589 3952849 := bstep (se 2 (by rfl) ⟨1482318, by rfl⟩ : syracuseStep 3952849 = 2964637) B2964637
theorem B10408601 : Blo 960589 10408601 := bstep (se 2 (by rfl) ⟨3903225, by rfl⟩ : syracuseStep 10408601 = 7806451) B7806451
theorem B1626959 : Blo 960589 1626959 := bstep (se 1 (by rfl) ⟨1220219, by rfl⟩ : syracuseStep 1626959 = 2440439) B2440439
theorem B3658715 : Blo 960589 3658715 := bstep (se 1 (by rfl) ⟨2744036, by rfl⟩ : syracuseStep 3658715 = 5488073) B5488073
theorem B5854355 : Blo 960589 5854355 := bstep (se 1 (by rfl) ⟨4390766, by rfl⟩ : syracuseStep 5854355 = 8781533) B8781533
theorem B5199005 : Blo 960589 5199005 := bstep (se 3 (by rfl) ⟨974813, by rfl⟩ : syracuseStep 5199005 = 1949627) B1949627
theorem B2315483 : Blo 960589 2315483 := bstep (se 1 (by rfl) ⟨1736612, by rfl⟩ : syracuseStep 2315483 = 3473225) B3473225
theorem B4118327 : Blo 960589 4118327 := bstep (se 1 (by rfl) ⟨3088745, by rfl⟩ : syracuseStep 4118327 = 6177491) B6177491
theorem B4872473 : Blo 960589 4872473 := bstep (se 2 (by rfl) ⟨1827177, by rfl⟩ : syracuseStep 4872473 = 3654355) B3654355
theorem B1825249 : Blo 960589 1825249 := bstep (se 2 (by rfl) ⟨684468, by rfl⟩ : syracuseStep 1825249 = 1368937) B1368937
theorem B4119113 : Blo 960589 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B1826297 : Blo 960589 1826297 := bstep (se 2 (by rfl) ⟨684861, by rfl⟩ : syracuseStep 1826297 = 1369723) B1369723
theorem B6250007 : Blo 960589 6250007 := bstep (se 1 (by rfl) ⟨4687505, by rfl⟩ : syracuseStep 6250007 = 9375011) B9375011
theorem B974639 : Blo 960589 974639 := bstep (se 1 (by rfl) ⟨730979, by rfl⟩ : syracuseStep 974639 = 1461959) B1461959
theorem B157933475 : Blo 960589 157933475 := bstep (se 1 (by rfl) ⟨118450106, by rfl⟩ : syracuseStep 157933475 = 236900213) B236900213
theorem B17555459 : Blo 960589 17555459 := bstep (se 1 (by rfl) ⟨13166594, by rfl⟩ : syracuseStep 17555459 = 26333189) B26333189
theorem B7791011 : Blo 960589 7791011 := bstep (se 1 (by rfl) ⟨5843258, by rfl⟩ : syracuseStep 7791011 = 11686517) B11686517
theorem B16441865 : Blo 960589 16441865 := bstep (se 2 (by rfl) ⟨6165699, by rfl⟩ : syracuseStep 16441865 = 12331399) B12331399
theorem B1827755 : Blo 960589 1827755 := bstep (se 1 (by rfl) ⟨1370816, by rfl⟩ : syracuseStep 1827755 = 2741633) B2741633
theorem B4875227 : Blo 960589 4875227 := bstep (se 1 (by rfl) ⟨3656420, by rfl⟩ : syracuseStep 4875227 = 7312841) B7312841
theorem B4875389 : Blo 960589 4875389 := bstep (se 3 (by rfl) ⟨914135, by rfl⟩ : syracuseStep 4875389 = 1828271) B1828271
theorem B1827983 : Blo 960589 1827983 := bstep (se 1 (by rfl) ⟨1370987, by rfl⟩ : syracuseStep 1827983 = 2741975) B2741975
theorem B4875713 : Blo 960589 4875713 := bstep (se 2 (by rfl) ⟨1828392, by rfl⟩ : syracuseStep 4875713 = 3656785) B3656785
theorem B8218199 : Blo 960589 8218199 := bstep (se 1 (by rfl) ⟨6163649, by rfl⟩ : syracuseStep 8218199 = 12327299) B12327299
theorem B16476857 : Blo 960589 16476857 := bstep (se 2 (by rfl) ⟨6178821, by rfl⟩ : syracuseStep 16476857 = 12357643) B12357643
theorem B9235633 : Blo 960589 9235633 := bstep (se 2 (by rfl) ⟨3463362, by rfl⟩ : syracuseStep 9235633 = 6926725) B6926725
theorem B8907995 : Blo 960589 8907995 := bstep (se 1 (by rfl) ⟨6680996, by rfl⟩ : syracuseStep 8907995 = 13361993) B13361993
theorem B3468815 : Blo 960589 3468815 := bstep (se 1 (by rfl) ⟨2601611, by rfl⟩ : syracuseStep 3468815 = 5203223) B5203223
theorem B3173971 : Blo 960589 3173971 := bstep (se 1 (by rfl) ⟨2380478, by rfl⟩ : syracuseStep 3173971 = 4760957) B4760957
theorem B3698291 : Blo 960589 3698291 := bstep (se 1 (by rfl) ⟨2773718, by rfl⟩ : syracuseStep 3698291 = 5547437) B5547437
theorem B2191369 : Blo 960589 2191369 := bstep (se 2 (by rfl) ⟨821763, by rfl⟩ : syracuseStep 2191369 = 1643527) B1643527
theorem B7402585 : Blo 960589 7402585 := bstep (se 2 (by rfl) ⟨2775969, by rfl⟩ : syracuseStep 7402585 = 5551939) B5551939
theorem B3897193 : Blo 960589 3897193 := bstep (se 2 (by rfl) ⟨1461447, by rfl⟩ : syracuseStep 3897193 = 2922895) B2922895
theorem B4618739 : Blo 960589 4618739 := bstep (se 1 (by rfl) ⟨3464054, by rfl⟩ : syracuseStep 4618739 = 6928109) B6928109
theorem B15596165 : Blo 960589 15596165 := bstep (se 4 (by rfl) ⟨1462140, by rfl⟩ : syracuseStep 15596165 = 2924281) B2924281
theorem B6158987 : Blo 960589 6158987 := bstep (se 1 (by rfl) ⟨4619240, by rfl⟩ : syracuseStep 6158987 = 9238481) B9238481
theorem B3701629 : Blo 960589 3701629 := bstep (se 3 (by rfl) ⟨694055, by rfl⟩ : syracuseStep 3701629 = 1388111) B1388111
theorem B4389875 : Blo 960589 4389875 := bstep (se 1 (by rfl) ⟨3292406, by rfl⟩ : syracuseStep 4389875 = 6584813) B6584813
theorem B2161655 : Blo 960589 2161655 := bstep (se 1 (by rfl) ⟨1621241, by rfl⟩ : syracuseStep 2161655 = 3242483) B3242483
theorem B8911991 : Blo 960589 8911991 := bstep (se 1 (by rfl) ⟨6683993, by rfl⟩ : syracuseStep 8911991 = 13367987) B13367987
theorem B3243131 : Blo 960589 3243131 := bstep (se 1 (by rfl) ⟨2432348, by rfl⟩ : syracuseStep 3243131 = 4864697) B4864697
theorem B5864669 : Blo 960589 5864669 := bstep (se 3 (by rfl) ⟨1099625, by rfl⟩ : syracuseStep 5864669 = 2199251) B2199251
theorem B1441001 : Blo 960589 1441001 := bstep (se 2 (by rfl) ⟨540375, by rfl⟩ : syracuseStep 1441001 = 1080751) B1080751
theorem B1441055 : Blo 960589 1441055 := bstep (se 1 (by rfl) ⟨1080791, by rfl⟩ : syracuseStep 1441055 = 2161583) B2161583
theorem B2162015 : Blo 960589 2162015 := bstep (se 1 (by rfl) ⟨1621511, by rfl⟩ : syracuseStep 2162015 = 3243023) B3243023
theorem B3243401 : Blo 960589 3243401 := bstep (se 2 (by rfl) ⟨1216275, by rfl⟩ : syracuseStep 3243401 = 2432551) B2432551
theorem B1441223 : Blo 960589 1441223 := bstep (se 1 (by rfl) ⟨1080917, by rfl⟩ : syracuseStep 1441223 = 2161835) B2161835
theorem B3079673 : Blo 960589 3079673 := bstep (se 2 (by rfl) ⟨1154877, by rfl⟩ : syracuseStep 3079673 = 2309755) B2309755
theorem B1080895 : Blo 960589 1080895 := bstep (se 1 (by rfl) ⟨810671, by rfl⟩ : syracuseStep 1080895 = 1621343) B1621343
theorem B3079775 : Blo 960589 3079775 := bstep (se 1 (by rfl) ⟨2309831, by rfl⟩ : syracuseStep 3079775 = 4619663) B4619663
theorem B78904979 : Blo 960589 78904979 := bstep (se 1 (by rfl) ⟨59178734, by rfl⟩ : syracuseStep 78904979 = 118357469) B118357469
theorem B1736353 : Blo 960589 1736353 := bstep (se 2 (by rfl) ⟨651132, by rfl⟩ : syracuseStep 1736353 = 1302265) B1302265
theorem B2162411 : Blo 960589 2162411 := bstep (se 1 (by rfl) ⟨1621808, by rfl⟩ : syracuseStep 2162411 = 3243617) B3243617
theorem B7798535 : Blo 960589 7798535 := bstep (se 1 (by rfl) ⟨5848901, by rfl⟩ : syracuseStep 7798535 = 11697803) B11697803
theorem B1441577 : Blo 960589 1441577 := bstep (se 2 (by rfl) ⟨540591, by rfl⟩ : syracuseStep 1441577 = 1081183) B1081183
theorem B1441583 : Blo 960589 1441583 := bstep (se 1 (by rfl) ⟨1081187, by rfl⟩ : syracuseStep 1441583 = 2162375) B2162375
theorem B3243833 : Blo 960589 3243833 := bstep (se 2 (by rfl) ⟨1216437, by rfl⟩ : syracuseStep 3243833 = 2432875) B2432875
theorem B2162537 : Blo 960589 2162537 := bstep (se 2 (by rfl) ⟨810951, by rfl⟩ : syracuseStep 2162537 = 1621903) B1621903
theorem B3473281 : Blo 960589 3473281 := bstep (se 2 (by rfl) ⟨1302480, by rfl⟩ : syracuseStep 3473281 = 2604961) B2604961
theorem B12353543 : Blo 960589 12353543 := bstep (se 1 (by rfl) ⟨9265157, by rfl⟩ : syracuseStep 12353543 = 18530315) B18530315
theorem B3244319 : Blo 960589 3244319 := bstep (se 1 (by rfl) ⟨2433239, by rfl⟩ : syracuseStep 3244319 = 4866479) B4866479
theorem B2163041 : Blo 960589 2163041 := bstep (se 2 (by rfl) ⟨811140, by rfl⟩ : syracuseStep 2163041 = 1622281) B1622281
theorem B2163131 : Blo 960589 2163131 := bstep (se 1 (by rfl) ⟨1622348, by rfl⟩ : syracuseStep 2163131 = 3244697) B3244697
theorem B1442255 : Blo 960589 1442255 := bstep (se 1 (by rfl) ⟨1081691, by rfl⟩ : syracuseStep 1442255 = 2163383) B2163383
theorem B1442297 : Blo 960589 1442297 := bstep (se 2 (by rfl) ⟨540861, by rfl⟩ : syracuseStep 1442297 = 1081723) B1081723
theorem B1442399 : Blo 960589 1442399 := bstep (se 1 (by rfl) ⟨1081799, by rfl⟩ : syracuseStep 1442399 = 2163599) B2163599
theorem B3900079 : Blo 960589 3900079 := bstep (se 1 (by rfl) ⟨2925059, by rfl⟩ : syracuseStep 3900079 = 5850119) B5850119
theorem B3244967 : Blo 960589 3244967 := bstep (se 1 (by rfl) ⟨2433725, by rfl⟩ : syracuseStep 3244967 = 4867451) B4867451
theorem B1442879 : Blo 960589 1442879 := bstep (se 1 (by rfl) ⟨1082159, by rfl⟩ : syracuseStep 1442879 = 2164319) B2164319
theorem B1442921 : Blo 960589 1442921 := bstep (se 2 (by rfl) ⟨541095, by rfl⟩ : syracuseStep 1442921 = 1082191) B1082191
theorem B11732161 : Blo 960589 11732161 := bstep (se 2 (by rfl) ⟨4399560, by rfl⟩ : syracuseStep 11732161 = 8799121) B8799121
theorem B1443023 : Blo 960589 1443023 := bstep (se 1 (by rfl) ⟨1082267, by rfl⟩ : syracuseStep 1443023 = 2164535) B2164535
theorem B1443227 : Blo 960589 1443227 := bstep (se 1 (by rfl) ⟨1082420, by rfl⟩ : syracuseStep 1443227 = 2164841) B2164841
theorem B2164139 : Blo 960589 2164139 := bstep (se 1 (by rfl) ⟨1623104, by rfl⟩ : syracuseStep 2164139 = 3246209) B3246209
theorem B3245561 : Blo 960589 3245561 := bstep (se 2 (by rfl) ⟨1217085, by rfl⟩ : syracuseStep 3245561 = 2434171) B2434171
theorem B1443449 : Blo 960589 1443449 := bstep (se 2 (by rfl) ⟨541293, by rfl⟩ : syracuseStep 1443449 = 1082587) B1082587
theorem B7308953 : Blo 960589 7308953 := bstep (se 2 (by rfl) ⟨2740857, by rfl⟩ : syracuseStep 7308953 = 5481715) B5481715
theorem B2164391 : Blo 960589 2164391 := bstep (se 1 (by rfl) ⟨1623293, by rfl⟩ : syracuseStep 2164391 = 3246587) B3246587
theorem B1443551 : Blo 960589 1443551 := bstep (se 1 (by rfl) ⟨1082663, by rfl⟩ : syracuseStep 1443551 = 2165327) B2165327
theorem B3245831 : Blo 960589 3245831 := bstep (se 1 (by rfl) ⟨2434373, by rfl⟩ : syracuseStep 3245831 = 4868747) B4868747
theorem B3245885 : Blo 960589 3245885 := bstep (se 3 (by rfl) ⟨608603, by rfl⟩ : syracuseStep 3245885 = 1217207) B1217207
theorem B1443647 : Blo 960589 1443647 := bstep (se 1 (by rfl) ⟨1082735, by rfl⟩ : syracuseStep 1443647 = 2165471) B2165471
theorem B1083199 : Blo 960589 1083199 := bstep (se 1 (by rfl) ⟨812399, by rfl⟩ : syracuseStep 1083199 = 1624799) B1624799
theorem B2164679 : Blo 960589 2164679 := bstep (se 1 (by rfl) ⟨1623509, by rfl⟩ : syracuseStep 2164679 = 3247019) B3247019
theorem B1443815 : Blo 960589 1443815 := bstep (se 1 (by rfl) ⟨1082861, by rfl⟩ : syracuseStep 1443815 = 2165723) B2165723
theorem B1443833 : Blo 960589 1443833 := bstep (se 2 (by rfl) ⟨541437, by rfl⟩ : syracuseStep 1443833 = 1082875) B1082875
theorem B1443935 : Blo 960589 1443935 := bstep (se 1 (by rfl) ⟨1082951, by rfl⟩ : syracuseStep 1443935 = 2165903) B2165903
theorem B1083487 : Blo 960589 1083487 := bstep (se 1 (by rfl) ⟨812615, by rfl⟩ : syracuseStep 1083487 = 1625231) B1625231
theorem B1443995 : Blo 960589 1443995 := bstep (se 1 (by rfl) ⟨1082996, by rfl⟩ : syracuseStep 1443995 = 2165993) B2165993
theorem B1444031 : Blo 960589 1444031 := bstep (se 1 (by rfl) ⟨1083023, by rfl⟩ : syracuseStep 1444031 = 2166047) B2166047
theorem B1444073 : Blo 960589 1444073 := bstep (se 2 (by rfl) ⟨541527, by rfl⟩ : syracuseStep 1444073 = 1083055) B1083055
theorem B2164985 : Blo 960589 2164985 := bstep (se 2 (by rfl) ⟨811869, by rfl⟩ : syracuseStep 2164985 = 1623739) B1623739
theorem B2165039 : Blo 960589 2165039 := bstep (se 1 (by rfl) ⟨1623779, by rfl⟩ : syracuseStep 2165039 = 3247559) B3247559
theorem B2165255 : Blo 960589 2165255 := bstep (se 1 (by rfl) ⟨1623941, by rfl⟩ : syracuseStep 2165255 = 3247883) B3247883
theorem B1444379 : Blo 960589 1444379 := bstep (se 1 (by rfl) ⟨1083284, by rfl⟩ : syracuseStep 1444379 = 2166569) B2166569
theorem B12519967 : Blo 960589 12519967 := bstep (se 1 (by rfl) ⟨9389975, by rfl⟩ : syracuseStep 12519967 = 18779951) B18779951
theorem B1444457 : Blo 960589 1444457 := bstep (se 2 (by rfl) ⟨541671, by rfl⟩ : syracuseStep 1444457 = 1083343) B1083343
theorem B2165435 : Blo 960589 2165435 := bstep (se 1 (by rfl) ⟨1624076, by rfl⟩ : syracuseStep 2165435 = 3248153) B3248153
theorem B1444985 : Blo 960589 1444985 := bstep (se 2 (by rfl) ⟨541869, by rfl⟩ : syracuseStep 1444985 = 1083739) B1083739
theorem B1445087 : Blo 960589 1445087 := bstep (se 1 (by rfl) ⟨1083815, by rfl⟩ : syracuseStep 1445087 = 2167631) B2167631
theorem B1084639 : Blo 960589 1084639 := bstep (se 1 (by rfl) ⟨813479, by rfl⟩ : syracuseStep 1084639 = 1626959) B1626959
theorem B1445129 : Blo 960589 1445129 := bstep (se 2 (by rfl) ⟨541923, by rfl⟩ : syracuseStep 1445129 = 1083847) B1083847
theorem B1445231 : Blo 960589 1445231 := bstep (se 1 (by rfl) ⟨1083923, by rfl⟩ : syracuseStep 1445231 = 2167847) B2167847
theorem B3902903 : Blo 960589 3902903 := bstep (se 1 (by rfl) ⟨2927177, by rfl⟩ : syracuseStep 3902903 = 5854355) B5854355
theorem B1543655 : Blo 960589 1543655 := bstep (se 1 (by rfl) ⟨1157741, by rfl⟩ : syracuseStep 1543655 = 2315483) B2315483
theorem B1445351 : Blo 960589 1445351 := bstep (se 1 (by rfl) ⟨1084013, by rfl⟩ : syracuseStep 1445351 = 2168027) B2168027
theorem B2166263 : Blo 960589 2166263 := bstep (se 1 (by rfl) ⟨1624697, by rfl⟩ : syracuseStep 2166263 = 3249395) B3249395
theorem B13897277 : Blo 960589 13897277 := bstep (se 3 (by rfl) ⟨2605739, by rfl⟩ : syracuseStep 13897277 = 5211479) B5211479
theorem B2166335 : Blo 960589 2166335 := bstep (se 1 (by rfl) ⟨1624751, by rfl⟩ : syracuseStep 2166335 = 3249503) B3249503
theorem B1445483 : Blo 960589 1445483 := bstep (se 1 (by rfl) ⟨1084112, by rfl⟩ : syracuseStep 1445483 = 2168225) B2168225
theorem B23432885 : Blo 960589 23432885 := bstep (se 5 (by rfl) ⟨1098416, by rfl⟩ : syracuseStep 23432885 = 2196833) B2196833
theorem B1445609 : Blo 960589 1445609 := bstep (se 2 (by rfl) ⟨542103, by rfl⟩ : syracuseStep 1445609 = 1084207) B1084207
theorem B1445753 : Blo 960589 1445753 := bstep (se 2 (by rfl) ⟨542157, by rfl⟩ : syracuseStep 1445753 = 1084315) B1084315
theorem B6164369 : Blo 960589 6164369 := bstep (se 2 (by rfl) ⟨2311638, by rfl⟩ : syracuseStep 6164369 = 4623277) B4623277
theorem B1445855 : Blo 960589 1445855 := bstep (se 1 (by rfl) ⟨1084391, by rfl⟩ : syracuseStep 1445855 = 2168783) B2168783
theorem B3248315 : Blo 960589 3248315 := bstep (se 1 (by rfl) ⟨2436236, by rfl⟩ : syracuseStep 3248315 = 4872473) B4872473
theorem B1446107 : Blo 960589 1446107 := bstep (se 1 (by rfl) ⟨1084580, by rfl⟩ : syracuseStep 1446107 = 2169161) B2169161
theorem B1446119 : Blo 960589 1446119 := bstep (se 1 (by rfl) ⟨1084589, by rfl⟩ : syracuseStep 1446119 = 2169179) B2169179
theorem B1446281 : Blo 960589 1446281 := bstep (se 2 (by rfl) ⟨542355, by rfl⟩ : syracuseStep 1446281 = 1084711) B1084711
theorem B1446377 : Blo 960589 1446377 := bstep (se 2 (by rfl) ⟨542391, by rfl⟩ : syracuseStep 1446377 = 1084783) B1084783
theorem B2167289 : Blo 960589 2167289 := bstep (se 2 (by rfl) ⟨812733, by rfl⟩ : syracuseStep 2167289 = 1625467) B1625467
theorem B2167379 : Blo 960589 2167379 := bstep (se 1 (by rfl) ⟨1625534, by rfl⟩ : syracuseStep 2167379 = 3251069) B3251069
theorem B1446503 : Blo 960589 1446503 := bstep (se 1 (by rfl) ⟨1084877, by rfl⟩ : syracuseStep 1446503 = 2169755) B2169755
theorem B3248801 : Blo 960589 3248801 := bstep (se 2 (by rfl) ⟨1218300, by rfl⟩ : syracuseStep 3248801 = 2436601) B2436601
theorem B1446635 : Blo 960589 1446635 := bstep (se 1 (by rfl) ⟨1084976, by rfl⟩ : syracuseStep 1446635 = 2169953) B2169953
theorem B2167559 : Blo 960589 2167559 := bstep (se 1 (by rfl) ⟨1625669, by rfl⟩ : syracuseStep 2167559 = 3251339) B3251339
theorem B1446665 : Blo 960589 1446665 := bstep (se 2 (by rfl) ⟨542499, by rfl⟩ : syracuseStep 1446665 = 1084999) B1084999
theorem B4231961 : Blo 960589 4231961 := bstep (se 2 (by rfl) ⟨1586985, by rfl⟩ : syracuseStep 4231961 = 3173971) B3173971
theorem B1446767 : Blo 960589 1446767 := bstep (se 1 (by rfl) ⟨1085075, by rfl⟩ : syracuseStep 1446767 = 2170151) B2170151
theorem B1217531 : Blo 960589 1217531 := bstep (se 1 (by rfl) ⟨913148, by rfl⟩ : syracuseStep 1217531 = 1826297) B1826297
theorem B4166671 : Blo 960589 4166671 := bstep (se 1 (by rfl) ⟨3125003, by rfl⟩ : syracuseStep 4166671 = 6250007) B6250007
theorem B105288983 : Blo 960589 105288983 := bstep (se 1 (by rfl) ⟨78966737, by rfl⟩ : syracuseStep 105288983 = 157933475) B157933475
theorem B2921825 : Blo 960589 2921825 := bstep (se 2 (by rfl) ⟨1095684, by rfl⟩ : syracuseStep 2921825 = 2191369) B2191369
theorem B3249665 : Blo 960589 3249665 := bstep (se 2 (by rfl) ⟨1218624, by rfl⟩ : syracuseStep 3249665 = 2437249) B2437249
theorem B1644143 : Blo 960589 1644143 := bstep (se 1 (by rfl) ⟨1233107, by rfl⟩ : syracuseStep 1644143 = 2466215) B2466215
theorem B2168639 : Blo 960589 2168639 := bstep (se 1 (by rfl) ⟨1626479, by rfl⟩ : syracuseStep 2168639 = 3252959) B3252959
theorem B1218503 : Blo 960589 1218503 := bstep (se 1 (by rfl) ⟨913877, by rfl⟩ : syracuseStep 1218503 = 1827755) B1827755
theorem B3250151 : Blo 960589 3250151 := bstep (se 1 (by rfl) ⟨2437613, by rfl⟩ : syracuseStep 3250151 = 4875227) B4875227
theorem B3250259 : Blo 960589 3250259 := bstep (se 1 (by rfl) ⟨2437694, by rfl⟩ : syracuseStep 3250259 = 4875389) B4875389
theorem B1218655 : Blo 960589 1218655 := bstep (se 1 (by rfl) ⟨913991, by rfl⟩ : syracuseStep 1218655 = 1827983) B1827983
theorem B2168927 : Blo 960589 2168927 := bstep (se 1 (by rfl) ⟨1626695, by rfl⟩ : syracuseStep 2168927 = 3253391) B3253391
theorem B3250475 : Blo 960589 3250475 := bstep (se 1 (by rfl) ⟨2437856, by rfl⟩ : syracuseStep 3250475 = 4875713) B4875713
theorem B10951037 : Blo 960589 10951037 := bstep (se 3 (by rfl) ⟨2053319, by rfl⟩ : syracuseStep 10951037 = 4106639) B4106639
theorem B5478799 : Blo 960589 5478799 := bstep (se 1 (by rfl) ⟨4109099, by rfl⟩ : syracuseStep 5478799 = 8218199) B8218199
theorem B3250745 : Blo 960589 3250745 := bstep (se 2 (by rfl) ⟨1219029, by rfl⟩ : syracuseStep 3250745 = 2438059) B2438059
theorem B9870113 : Blo 960589 9870113 := bstep (se 2 (by rfl) ⟨3701292, by rfl⟩ : syracuseStep 9870113 = 7402585) B7402585
theorem B2169683 : Blo 960589 2169683 := bstep (se 1 (by rfl) ⟨1627262, by rfl⟩ : syracuseStep 2169683 = 3254525) B3254525
theorem B2431903 : Blo 960589 2431903 := bstep (se 1 (by rfl) ⟨1823927, by rfl⟩ : syracuseStep 2431903 = 3647855) B3647855
theorem B10984571 : Blo 960589 10984571 := bstep (se 1 (by rfl) ⟨8238428, by rfl⟩ : syracuseStep 10984571 = 16476857) B16476857
theorem B2170223 : Blo 960589 2170223 := bstep (se 1 (by rfl) ⟨1627667, by rfl⟩ : syracuseStep 2170223 = 3255335) B3255335
theorem B2465527 : Blo 960589 2465527 := bstep (se 1 (by rfl) ⟨1849145, by rfl⟩ : syracuseStep 2465527 = 3698291) B3698291
theorem B10952495 : Blo 960589 10952495 := bstep (se 1 (by rfl) ⟨8214371, by rfl⟩ : syracuseStep 10952495 = 16428743) B16428743
theorem B3252257 : Blo 960589 3252257 := bstep (se 2 (by rfl) ⟨1219596, by rfl⟩ : syracuseStep 3252257 = 2439193) B2439193
theorem B2433311 : Blo 960589 2433311 := bstep (se 1 (by rfl) ⟨1824983, by rfl⟩ : syracuseStep 2433311 = 3649967) B3649967
theorem B23765309 : Blo 960589 23765309 := bstep (se 3 (by rfl) ⟨4455995, by rfl⟩ : syracuseStep 23765309 = 8911991) B8911991
theorem B1319375 : Blo 960589 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B2433665 : Blo 960589 2433665 := bstep (se 2 (by rfl) ⟨912624, by rfl⟩ : syracuseStep 2433665 = 1825249) B1825249
theorem B2433959 : Blo 960589 2433959 := bstep (se 1 (by rfl) ⟨1825469, by rfl⟩ : syracuseStep 2433959 = 3650939) B3650939
theorem B7316729 : Blo 960589 7316729 := bstep (se 2 (by rfl) ⟨2743773, by rfl⟩ : syracuseStep 7316729 = 5487547) B5487547
theorem B3089771 : Blo 960589 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B2434475 : Blo 960589 2434475 := bstep (se 1 (by rfl) ⟨1825856, by rfl⟩ : syracuseStep 2434475 = 3651713) B3651713
theorem B10397443 : Blo 960589 10397443 := bstep (se 1 (by rfl) ⟨7798082, by rfl⟩ : syracuseStep 10397443 = 15596165) B15596165
theorem B4105991 : Blo 960589 4105991 := bstep (se 1 (by rfl) ⟨3079493, by rfl⟩ : syracuseStep 4105991 = 6158987) B6158987
theorem B2926583 : Blo 960589 2926583 := bstep (se 1 (by rfl) ⟨2194937, by rfl⟩ : syracuseStep 2926583 = 4389875) B4389875
theorem B1648631 : Blo 960589 1648631 := bstep (se 1 (by rfl) ⟨1236473, by rfl⟩ : syracuseStep 1648631 = 2472947) B2472947
theorem B2599037 : Blo 960589 2599037 := bstep (se 3 (by rfl) ⟨487319, by rfl⟩ : syracuseStep 2599037 = 974639) B974639
theorem B3909779 : Blo 960589 3909779 := bstep (se 1 (by rfl) ⟨2932334, by rfl⟩ : syracuseStep 3909779 = 5864669) B5864669
theorem B960667 : Blo 960589 960667 := bstep (se 1 (by rfl) ⟨720500, by rfl⟩ : syracuseStep 960667 = 1441001) B1441001
theorem B960703 : Blo 960589 960703 := bstep (se 1 (by rfl) ⟨720527, by rfl⟩ : syracuseStep 960703 = 1441055) B1441055
theorem B960815 : Blo 960589 960815 := bstep (se 1 (by rfl) ⟨720611, by rfl⟩ : syracuseStep 960815 = 1441223) B1441223
theorem B2435467 : Blo 960589 2435467 := bstep (se 1 (by rfl) ⟨1826600, by rfl⟩ : syracuseStep 2435467 = 3653201) B3653201
theorem B52603319 : Blo 960589 52603319 := bstep (se 1 (by rfl) ⟨39452489, by rfl⟩ : syracuseStep 52603319 = 78904979) B78904979
theorem B4631041 : Blo 960589 4631041 := bstep (se 2 (by rfl) ⟨1736640, by rfl⟩ : syracuseStep 4631041 = 3473281) B3473281
theorem B961051 : Blo 960589 961051 := bstep (se 1 (by rfl) ⟨720788, by rfl⟩ : syracuseStep 961051 = 1441577) B1441577
theorem B961055 : Blo 960589 961055 := bstep (se 1 (by rfl) ⟨720791, by rfl⟩ : syracuseStep 961055 = 1441583) B1441583
theorem B2435771 : Blo 960589 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B3648311 : Blo 960589 3648311 := bstep (se 1 (by rfl) ⟨2736233, by rfl⟩ : syracuseStep 3648311 = 5472467) B5472467
theorem B961371 : Blo 960589 961371 := bstep (se 1 (by rfl) ⟨721028, by rfl⟩ : syracuseStep 961371 = 1442057) B1442057
theorem B961439 : Blo 960589 961439 := bstep (se 1 (by rfl) ⟨721079, by rfl⟩ : syracuseStep 961439 = 1442159) B1442159
theorem B961583 : Blo 960589 961583 := bstep (se 1 (by rfl) ⟨721187, by rfl⟩ : syracuseStep 961583 = 1442375) B1442375
theorem B961607 : Blo 960589 961607 := bstep (se 1 (by rfl) ⟨721205, by rfl⟩ : syracuseStep 961607 = 1442411) B1442411
theorem B961759 : Blo 960589 961759 := bstep (se 1 (by rfl) ⟨721319, by rfl⟩ : syracuseStep 961759 = 1442639) B1442639
theorem B962023 : Blo 960589 962023 := bstep (se 1 (by rfl) ⟨721517, by rfl⟩ : syracuseStep 962023 = 1443035) B1443035
theorem B962139 : Blo 960589 962139 := bstep (se 1 (by rfl) ⟨721604, by rfl⟩ : syracuseStep 962139 = 1443209) B1443209
theorem B28552933 : Blo 960589 28552933 := bstep (se 4 (by rfl) ⟨2676837, by rfl⟩ : syracuseStep 28552933 = 5353675) B5353675
theorem B962375 : Blo 960589 962375 := bstep (se 1 (by rfl) ⟨721781, by rfl⟩ : syracuseStep 962375 = 1443563) B1443563
theorem B962527 : Blo 960589 962527 := bstep (se 1 (by rfl) ⟨721895, by rfl⟩ : syracuseStep 962527 = 1443791) B1443791
theorem B2437087 : Blo 960589 2437087 := bstep (se 1 (by rfl) ⟨1827815, by rfl⟩ : syracuseStep 2437087 = 3655631) B3655631
theorem B962791 : Blo 960589 962791 := bstep (se 1 (by rfl) ⟨722093, by rfl⟩ : syracuseStep 962791 = 1444187) B1444187
theorem B4108553 : Blo 960589 4108553 := bstep (se 2 (by rfl) ⟨1540707, by rfl⟩ : syracuseStep 4108553 = 3081415) B3081415
theorem B962943 : Blo 960589 962943 := bstep (se 1 (by rfl) ⟨722207, by rfl⟩ : syracuseStep 962943 = 1444415) B1444415
theorem B963023 : Blo 960589 963023 := bstep (se 1 (by rfl) ⟨722267, by rfl⟩ : syracuseStep 963023 = 1444535) B1444535
theorem B2437715 : Blo 960589 2437715 := bstep (se 1 (by rfl) ⟨1828286, by rfl⟩ : syracuseStep 2437715 = 3656573) B3656573
theorem B2437735 : Blo 960589 2437735 := bstep (se 1 (by rfl) ⟨1828301, by rfl⟩ : syracuseStep 2437735 = 3656603) B3656603
theorem B963175 : Blo 960589 963175 := bstep (se 1 (by rfl) ⟨722381, by rfl⟩ : syracuseStep 963175 = 1444763) B1444763
theorem B963439 : Blo 960589 963439 := bstep (se 1 (by rfl) ⟨722579, by rfl⟩ : syracuseStep 963439 = 1445159) B1445159
theorem B963495 : Blo 960589 963495 := bstep (se 1 (by rfl) ⟨722621, by rfl⟩ : syracuseStep 963495 = 1445243) B1445243
theorem B963579 : Blo 960589 963579 := bstep (se 1 (by rfl) ⟨722684, by rfl⟩ : syracuseStep 963579 = 1445369) B1445369
theorem B963647 : Blo 960589 963647 := bstep (se 1 (by rfl) ⟨722735, by rfl⟩ : syracuseStep 963647 = 1445471) B1445471
theorem B9254087 : Blo 960589 9254087 := bstep (se 1 (by rfl) ⟨6940565, by rfl⟩ : syracuseStep 9254087 = 13881131) B13881131
theorem B963791 : Blo 960589 963791 := bstep (se 1 (by rfl) ⟨722843, by rfl⟩ : syracuseStep 963791 = 1445687) B1445687
theorem B6174107 : Blo 960589 6174107 := bstep (se 1 (by rfl) ⟨4630580, by rfl⟩ : syracuseStep 6174107 = 9261161) B9261161
theorem B963995 : Blo 960589 963995 := bstep (se 1 (by rfl) ⟨722996, by rfl⟩ : syracuseStep 963995 = 1445993) B1445993
theorem B5486089 : Blo 960589 5486089 := bstep (se 2 (by rfl) ⟨2057283, by rfl⟩ : syracuseStep 5486089 = 4114567) B4114567
theorem B964207 : Blo 960589 964207 := bstep (se 1 (by rfl) ⟨723155, by rfl⟩ : syracuseStep 964207 = 1446311) B1446311
theorem B964263 : Blo 960589 964263 := bstep (se 1 (by rfl) ⟨723197, by rfl⟩ : syracuseStep 964263 = 1446395) B1446395
theorem B964347 : Blo 960589 964347 := bstep (se 1 (by rfl) ⟨723260, by rfl⟩ : syracuseStep 964347 = 1446521) B1446521
theorem B964383 : Blo 960589 964383 := bstep (se 1 (by rfl) ⟨723287, by rfl⟩ : syracuseStep 964383 = 1446575) B1446575
theorem B964415 : Blo 960589 964415 := bstep (se 1 (by rfl) ⟨723311, by rfl⟩ : syracuseStep 964415 = 1446623) B1446623
theorem B6174569 : Blo 960589 6174569 := bstep (se 2 (by rfl) ⟨2315463, by rfl⟩ : syracuseStep 6174569 = 4630927) B4630927
theorem B2439143 : Blo 960589 2439143 := bstep (se 1 (by rfl) ⟨1829357, by rfl⟩ : syracuseStep 2439143 = 3658715) B3658715
theorem B5781497 : Blo 960589 5781497 := bstep (se 2 (by rfl) ⟨2168061, by rfl⟩ : syracuseStep 5781497 = 4336123) B4336123
theorem B10401851 : Blo 960589 10401851 := bstep (se 1 (by rfl) ⟨7801388, by rfl⟩ : syracuseStep 10401851 = 15602777) B15602777
theorem B11123459 : Blo 960589 11123459 := bstep (se 1 (by rfl) ⟨8342594, by rfl⟩ : syracuseStep 11123459 = 16685189) B16685189
theorem B1621039 : Blo 960589 1621039 := bstep (se 1 (by rfl) ⟨1215779, by rfl⟩ : syracuseStep 1621039 = 2431559) B2431559
theorem B2735471 : Blo 960589 2735471 := bstep (se 1 (by rfl) ⟨2051603, by rfl⟩ : syracuseStep 2735471 = 4103207) B4103207
theorem B6929783 : Blo 960589 6929783 := bstep (se 1 (by rfl) ⟨5197337, by rfl⟩ : syracuseStep 6929783 = 10394675) B10394675
theorem B2735527 : Blo 960589 2735527 := bstep (se 1 (by rfl) ⟨2051645, by rfl⟩ : syracuseStep 2735527 = 4103291) B4103291
theorem B1621417 : Blo 960589 1621417 := bstep (se 2 (by rfl) ⟨608031, by rfl⟩ : syracuseStep 1621417 = 1216063) B1216063
theorem B2735927 : Blo 960589 2735927 := bstep (se 1 (by rfl) ⟨2051945, by rfl⟩ : syracuseStep 2735927 = 4103891) B4103891
theorem B1621883 : Blo 960589 1621883 := bstep (se 1 (by rfl) ⟨1216412, by rfl⟩ : syracuseStep 1621883 = 2432825) B2432825
theorem B5194007 : Blo 960589 5194007 := bstep (se 1 (by rfl) ⟨3895505, by rfl⟩ : syracuseStep 5194007 = 7791011) B7791011
theorem B10961243 : Blo 960589 10961243 := bstep (se 1 (by rfl) ⟨8220932, by rfl⟩ : syracuseStep 10961243 = 16441865) B16441865
theorem B2605871 : Blo 960589 2605871 := bstep (se 1 (by rfl) ⟨1954403, by rfl⟩ : syracuseStep 2605871 = 3908807) B3908807
theorem B1623145 : Blo 960589 1623145 := bstep (se 2 (by rfl) ⟨608679, by rfl⟩ : syracuseStep 1623145 = 1217359) B1217359
theorem B13878823 : Blo 960589 13878823 := bstep (se 1 (by rfl) ⟨10409117, by rfl⟩ : syracuseStep 13878823 = 20818235) B20818235
theorem B1623719 : Blo 960589 1623719 := bstep (se 1 (by rfl) ⟨1217789, by rfl⟩ : syracuseStep 1623719 = 2435579) B2435579
theorem B28493603 : Blo 960589 28493603 := bstep (se 1 (by rfl) ⟨21370202, by rfl⟩ : syracuseStep 28493603 = 42740405) B42740405
theorem B2738387 : Blo 960589 2738387 := bstep (se 1 (by rfl) ⟨2053790, by rfl⟩ : syracuseStep 2738387 = 4107581) B4107581
theorem B1624367 : Blo 960589 1624367 := bstep (se 1 (by rfl) ⟨1218275, by rfl⟩ : syracuseStep 1624367 = 2436551) B2436551
theorem B2312543 : Blo 960589 2312543 := bstep (se 1 (by rfl) ⟨1734407, by rfl⟩ : syracuseStep 2312543 = 3468815) B3468815
theorem B5196257 : Blo 960589 5196257 := bstep (se 2 (by rfl) ⟨1948596, by rfl⟩ : syracuseStep 5196257 = 3897193) B3897193
theorem B1624603 : Blo 960589 1624603 := bstep (se 1 (by rfl) ⟨1218452, by rfl⟩ : syracuseStep 1624603 = 2436905) B2436905
theorem B13880159 : Blo 960589 13880159 := bstep (se 1 (by rfl) ⟨10410119, by rfl⟩ : syracuseStep 13880159 = 20820239) B20820239
theorem B13159589 : Blo 960589 13159589 := bstep (se 4 (by rfl) ⟨1233711, by rfl⟩ : syracuseStep 13159589 = 2467423) B2467423
theorem B1625575 : Blo 960589 1625575 := bstep (se 1 (by rfl) ⟨1219181, by rfl⟩ : syracuseStep 1625575 = 2438363) B2438363
theorem B1625663 : Blo 960589 1625663 := bstep (se 1 (by rfl) ⟨1219247, by rfl⟩ : syracuseStep 1625663 = 2438495) B2438495
theorem B4935505 : Blo 960589 4935505 := bstep (se 2 (by rfl) ⟨1850814, by rfl⟩ : syracuseStep 4935505 = 3701629) B3701629
theorem B6180713 : Blo 960589 6180713 := bstep (se 2 (by rfl) ⟨2317767, by rfl⟩ : syracuseStep 6180713 = 4635535) B4635535
theorem B4116329 : Blo 960589 4116329 := bstep (se 2 (by rfl) ⟨1543623, by rfl⟩ : syracuseStep 4116329 = 3087247) B3087247
theorem B2740175 : Blo 960589 2740175 := bstep (se 1 (by rfl) ⟨2055131, by rfl⟩ : syracuseStep 2740175 = 4110263) B4110263
theorem B22499309 : Blo 960589 22499309 := bstep (se 3 (by rfl) ⟨4218620, by rfl⟩ : syracuseStep 22499309 = 8437241) B8437241
theorem B1626331 : Blo 960589 1626331 := bstep (se 1 (by rfl) ⟨1219748, by rfl⟩ : syracuseStep 1626331 = 2439497) B2439497
theorem B1626601 : Blo 960589 1626601 := bstep (se 2 (by rfl) ⟨609975, by rfl⟩ : syracuseStep 1626601 = 1219951) B1219951
theorem B62444317 : Blo 960589 62444317 := bstep (se 3 (by rfl) ⟨11708309, by rfl⟩ : syracuseStep 62444317 = 23416619) B23416619
theorem B2315137 : Blo 960589 2315137 := bstep (se 2 (by rfl) ⟨868176, by rfl⟩ : syracuseStep 2315137 = 1736353) B1736353
theorem B2053115 : Blo 960589 2053115 := bstep (se 1 (by rfl) ⟨1539836, by rfl⟩ : syracuseStep 2053115 = 3079673) B3079673
theorem B4871177 : Blo 960589 4871177 := bstep (se 2 (by rfl) ⟨1826691, by rfl⟩ : syracuseStep 4871177 = 3653383) B3653383
theorem B2741303 : Blo 960589 2741303 := bstep (se 1 (by rfl) ⟨2055977, by rfl⟩ : syracuseStep 2741303 = 4111955) B4111955
theorem B2053183 : Blo 960589 2053183 := bstep (se 1 (by rfl) ⟨1539887, by rfl⟩ : syracuseStep 2053183 = 3079775) B3079775
theorem B5199023 : Blo 960589 5199023 := bstep (se 1 (by rfl) ⟨3899267, by rfl⟩ : syracuseStep 5199023 = 7798535) B7798535
theorem B3462355 : Blo 960589 3462355 := bstep (se 1 (by rfl) ⟨2596766, by rfl⟩ : syracuseStep 3462355 = 5193533) B5193533
theorem B46814557 : Blo 960589 46814557 := bstep (se 3 (by rfl) ⟨8777729, by rfl⟩ : syracuseStep 46814557 = 17555459) B17555459
theorem B3298657 : Blo 960589 3298657 := bstep (se 2 (by rfl) ⟨1236996, by rfl⟩ : syracuseStep 3298657 = 2473993) B2473993
theorem B2315675 : Blo 960589 2315675 := bstep (se 1 (by rfl) ⟨1736756, by rfl⟩ : syracuseStep 2315675 = 3473513) B3473513
theorem B3462587 : Blo 960589 3462587 := bstep (se 1 (by rfl) ⟨2596940, by rfl⟩ : syracuseStep 3462587 = 5193881) B5193881
theorem B4117985 : Blo 960589 4117985 := bstep (se 2 (by rfl) ⟨1544244, by rfl⟩ : syracuseStep 4117985 = 3088489) B3088489
theorem B1562431 : Blo 960589 1562431 := bstep (se 1 (by rfl) ⟨1171823, by rfl⟩ : syracuseStep 1562431 = 2343647) B2343647
theorem B12310487 : Blo 960589 12310487 := bstep (se 1 (by rfl) ⟨9232865, by rfl⟩ : syracuseStep 12310487 = 18465731) B18465731
theorem B1824923 : Blo 960589 1824923 := bstep (se 1 (by rfl) ⟨1368692, by rfl⟩ : syracuseStep 1824923 = 2737385) B2737385
theorem B2316443 : Blo 960589 2316443 := bstep (se 1 (by rfl) ⟨1737332, by rfl⟩ : syracuseStep 2316443 = 3474665) B3474665
theorem B3659975 : Blo 960589 3659975 := bstep (se 1 (by rfl) ⟨2744981, by rfl⟩ : syracuseStep 3659975 = 5489963) B5489963
theorem B2316521 : Blo 960589 2316521 := bstep (se 2 (by rfl) ⟨868695, by rfl⟩ : syracuseStep 2316521 = 1737391) B1737391
theorem B6576491 : Blo 960589 6576491 := bstep (se 1 (by rfl) ⟨4932368, by rfl⟩ : syracuseStep 6576491 = 9864737) B9864737
theorem B2742635 : Blo 960589 2742635 := bstep (se 1 (by rfl) ⟨2056976, by rfl⟩ : syracuseStep 2742635 = 4113953) B4113953
theorem B5200841 : Blo 960589 5200841 := bstep (se 2 (by rfl) ⟨1950315, by rfl⟩ : syracuseStep 5200841 = 3900631) B3900631
theorem B3660947 : Blo 960589 3660947 := bstep (se 1 (by rfl) ⟨2745710, by rfl⟩ : syracuseStep 3660947 = 5491421) B5491421
theorem B5201081 : Blo 960589 5201081 := bstep (se 2 (by rfl) ⟨1950405, by rfl⟩ : syracuseStep 5201081 = 3900811) B3900811
theorem B12344521 : Blo 960589 12344521 := bstep (se 2 (by rfl) ⟨4629195, by rfl⟩ : syracuseStep 12344521 = 9258391) B9258391
theorem B7397099 : Blo 960589 7397099 := bstep (se 1 (by rfl) ⟨5547824, by rfl⟩ : syracuseStep 7397099 = 11095649) B11095649
theorem B15621983 : Blo 960589 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B18538469 : Blo 960589 18538469 := bstep (se 4 (by rfl) ⟨1737981, by rfl⟩ : syracuseStep 18538469 = 3475963) B3475963
theorem B6939067 : Blo 960589 6939067 := bstep (se 1 (by rfl) ⟨5204300, by rfl⟩ : syracuseStep 6939067 = 10408601) B10408601
theorem B12345857 : Blo 960589 12345857 := bstep (se 2 (by rfl) ⟨4629696, by rfl⟩ : syracuseStep 12345857 = 9259393) B9259393
theorem B3466003 : Blo 960589 3466003 := bstep (se 1 (by rfl) ⟨2599502, by rfl⟩ : syracuseStep 3466003 = 5199005) B5199005
theorem B4875065 : Blo 960589 4875065 := bstep (se 2 (by rfl) ⟨1828149, by rfl⟩ : syracuseStep 4875065 = 3656299) B3656299
theorem B2057071 : Blo 960589 2057071 := bstep (se 1 (by rfl) ⟨1542803, by rfl⟩ : syracuseStep 2057071 = 3085607) B3085607
theorem B2777999 : Blo 960589 2777999 := bstep (se 1 (by rfl) ⟨2083499, by rfl⟩ : syracuseStep 2777999 = 4166999) B4166999
theorem B2745551 : Blo 960589 2745551 := bstep (se 1 (by rfl) ⟨2059163, by rfl⟩ : syracuseStep 2745551 = 4118327) B4118327
theorem B48129551 : Blo 960589 48129551 := bstep (se 1 (by rfl) ⟨36097163, by rfl⟩ : syracuseStep 48129551 = 72194327) B72194327
theorem B12314177 : Blo 960589 12314177 := bstep (se 2 (by rfl) ⟨4617816, by rfl⟩ : syracuseStep 12314177 = 9235633) B9235633
theorem B2746075 : Blo 960589 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B10971449 : Blo 960589 10971449 := bstep (se 2 (by rfl) ⟨4114293, by rfl⟩ : syracuseStep 10971449 = 8228587) B8228587
theorem B2746781 : Blo 960589 2746781 := bstep (se 3 (by rfl) ⟨515021, by rfl⟩ : syracuseStep 2746781 = 1030043) B1030043
theorem B5270465 : Blo 960589 5270465 := bstep (se 2 (by rfl) ⟨1976424, by rfl⟩ : syracuseStep 5270465 = 3952849) B3952849
theorem B12316637 : Blo 960589 12316637 := bstep (se 3 (by rfl) ⟨2309369, by rfl⟩ : syracuseStep 12316637 = 4618739) B4618739
theorem B5862239 : Blo 960589 5862239 := bstep (se 1 (by rfl) ⟨4396679, by rfl⟩ : syracuseStep 5862239 = 8793359) B8793359
theorem B10974365 : Blo 960589 10974365 := bstep (se 3 (by rfl) ⟨2057693, by rfl⟩ : syracuseStep 10974365 = 4115387) B4115387
theorem B10942289 : Blo 960589 10942289 := bstep (se 2 (by rfl) ⟨4103358, by rfl⟩ : syracuseStep 10942289 = 8206717) B8206717
theorem B23754653 : Blo 960589 23754653 := bstep (se 3 (by rfl) ⟨4453997, by rfl⟩ : syracuseStep 23754653 = 8907995) B8907995
theorem B3242429 : Blo 960589 3242429 := bstep (se 3 (by rfl) ⟨607955, by rfl⟩ : syracuseStep 3242429 = 1215911) B1215911
theorem B10975823 : Blo 960589 10975823 := bstep (se 1 (by rfl) ⟨8231867, by rfl⟩ : syracuseStep 10975823 = 16463735) B16463735
theorem B32143979 : Blo 960589 32143979 := bstep (se 1 (by rfl) ⟨24107984, by rfl⟩ : syracuseStep 32143979 = 48215969) B48215969
theorem B6159037 : Blo 960589 6159037 := bstep (se 3 (by rfl) ⟨1154819, by rfl⟩ : syracuseStep 6159037 = 2309639) B2309639
theorem B3079417 : Blo 960589 3079417 := bstep (se 2 (by rfl) ⟨1154781, by rfl⟩ : syracuseStep 3079417 = 2309563) B2309563
theorem B1539337 : Blo 960589 1539337 := bstep (se 2 (by rfl) ⟨577251, by rfl⟩ : syracuseStep 1539337 = 1154503) B1154503
theorem B3243293 : Blo 960589 3243293 := bstep (se 3 (by rfl) ⟨608117, by rfl⟩ : syracuseStep 3243293 = 1216235) B1216235
theorem B1441103 : Blo 960589 1441103 := bstep (se 1 (by rfl) ⟨1080827, by rfl⟩ : syracuseStep 1441103 = 2161655) B2161655
theorem B2162087 : Blo 960589 2162087 := bstep (se 1 (by rfl) ⟨1621565, by rfl⟩ : syracuseStep 2162087 = 3243131) B3243131
theorem B1441193 : Blo 960589 1441193 := bstep (se 2 (by rfl) ⟨540447, by rfl⟩ : syracuseStep 1441193 = 1080895) B1080895
theorem B1441343 : Blo 960589 1441343 := bstep (se 1 (by rfl) ⟨1081007, by rfl⟩ : syracuseStep 1441343 = 2162015) B2162015
theorem B2162267 : Blo 960589 2162267 := bstep (se 1 (by rfl) ⟨1621700, by rfl⟩ : syracuseStep 2162267 = 3243401) B3243401
theorem B5865227 : Blo 960589 5865227 := bstep (se 1 (by rfl) ⟨4398920, by rfl⟩ : syracuseStep 5865227 = 8797841) B8797841
theorem B1441607 : Blo 960589 1441607 := bstep (se 1 (by rfl) ⟨1081205, by rfl⟩ : syracuseStep 1441607 = 2162411) B2162411
theorem B5013335 : Blo 960589 5013335 := bstep (se 1 (by rfl) ⟨3760001, by rfl⟩ : syracuseStep 5013335 = 7520003) B7520003
theorem B2162555 : Blo 960589 2162555 := bstep (se 1 (by rfl) ⟨1621916, by rfl⟩ : syracuseStep 2162555 = 3243833) B3243833
theorem B1441691 : Blo 960589 1441691 := bstep (se 1 (by rfl) ⟨1081268, by rfl⟩ : syracuseStep 1441691 = 2162537) B2162537
theorem B2162879 : Blo 960589 2162879 := bstep (se 1 (by rfl) ⟨1622159, by rfl⟩ : syracuseStep 2162879 = 3244319) B3244319
theorem B7307495 : Blo 960589 7307495 := bstep (se 1 (by rfl) ⟨5480621, by rfl⟩ : syracuseStep 7307495 = 10961243) B10961243
theorem B1442027 : Blo 960589 1442027 := bstep (se 1 (by rfl) ⟨1081520, by rfl⟩ : syracuseStep 1442027 = 2163041) B2163041
theorem B1442087 : Blo 960589 1442087 := bstep (se 1 (by rfl) ⟨1081565, by rfl⟩ : syracuseStep 1442087 = 2163131) B2163131
theorem B2163311 : Blo 960589 2163311 := bstep (se 1 (by rfl) ⟨1622483, by rfl⟩ : syracuseStep 2163311 = 3244967) B3244967
theorem B1442759 : Blo 960589 1442759 := bstep (se 1 (by rfl) ⟨1082069, by rfl⟩ : syracuseStep 1442759 = 2164139) B2164139
theorem B2163707 : Blo 960589 2163707 := bstep (se 1 (by rfl) ⟨1622780, by rfl⟩ : syracuseStep 2163707 = 3245561) B3245561
theorem B4621337 : Blo 960589 4621337 := bstep (se 2 (by rfl) ⟨1733001, by rfl⟩ : syracuseStep 4621337 = 3466003) B3466003
theorem B1442927 : Blo 960589 1442927 := bstep (se 1 (by rfl) ⟨1082195, by rfl⟩ : syracuseStep 1442927 = 2164391) B2164391
theorem B1082479 : Blo 960589 1082479 := bstep (se 1 (by rfl) ⟨811859, by rfl⟩ : syracuseStep 1082479 = 1623719) B1623719
theorem B2163887 : Blo 960589 2163887 := bstep (se 1 (by rfl) ⟨1622915, by rfl⟩ : syracuseStep 2163887 = 3245831) B3245831
theorem B2163923 : Blo 960589 2163923 := bstep (se 1 (by rfl) ⟨1622942, by rfl⟩ : syracuseStep 2163923 = 3245885) B3245885
theorem B1443119 : Blo 960589 1443119 := bstep (se 1 (by rfl) ⟨1082339, by rfl⟩ : syracuseStep 1443119 = 2164679) B2164679
theorem B2164193 : Blo 960589 2164193 := bstep (se 2 (by rfl) ⟨811572, by rfl⟩ : syracuseStep 2164193 = 1623145) B1623145
theorem B1443323 : Blo 960589 1443323 := bstep (se 1 (by rfl) ⟨1082492, by rfl⟩ : syracuseStep 1443323 = 2164985) B2164985
theorem B1443359 : Blo 960589 1443359 := bstep (se 1 (by rfl) ⟨1082519, by rfl⟩ : syracuseStep 1443359 = 2165039) B2165039
theorem B1082911 : Blo 960589 1082911 := bstep (se 1 (by rfl) ⟨812183, by rfl⟩ : syracuseStep 1082911 = 1624367) B1624367
theorem B1541695 : Blo 960589 1541695 := bstep (se 1 (by rfl) ⟨1156271, by rfl⟩ : syracuseStep 1541695 = 2312543) B2312543
theorem B24708725 : Blo 960589 24708725 := bstep (se 5 (by rfl) ⟨1158221, by rfl⟩ : syracuseStep 24708725 = 2316443) B2316443
theorem B1443503 : Blo 960589 1443503 := bstep (se 1 (by rfl) ⟨1082627, by rfl⟩ : syracuseStep 1443503 = 2165255) B2165255
theorem B1443623 : Blo 960589 1443623 := bstep (se 1 (by rfl) ⟨1082717, by rfl⟩ : syracuseStep 1443623 = 2165435) B2165435
theorem B6948989 : Blo 960589 6948989 := bstep (se 3 (by rfl) ⟨1302935, by rfl⟩ : syracuseStep 6948989 = 2605871) B2605871
theorem B1444175 : Blo 960589 1444175 := bstep (se 1 (by rfl) ⟨1083131, by rfl⟩ : syracuseStep 1444175 = 2166263) B2166263
theorem B13863257 : Blo 960589 13863257 := bstep (se 2 (by rfl) ⟨5198721, by rfl⟩ : syracuseStep 13863257 = 10397443) B10397443
theorem B7407997 : Blo 960589 7407997 := bstep (se 3 (by rfl) ⟨1388999, by rfl⟩ : syracuseStep 7407997 = 2777999) B2777999
theorem B1444223 : Blo 960589 1444223 := bstep (se 1 (by rfl) ⟨1083167, by rfl⟩ : syracuseStep 1444223 = 2166335) B2166335
theorem B1083775 : Blo 960589 1083775 := bstep (se 1 (by rfl) ⟨812831, by rfl⟩ : syracuseStep 1083775 = 1625663) B1625663
theorem B1444265 : Blo 960589 1444265 := bstep (se 2 (by rfl) ⟨541599, by rfl⟩ : syracuseStep 1444265 = 1083199) B1083199
theorem B3246749 : Blo 960589 3246749 := bstep (se 3 (by rfl) ⟨608765, by rfl⟩ : syracuseStep 3246749 = 1217531) B1217531
theorem B2165543 : Blo 960589 2165543 := bstep (se 1 (by rfl) ⟨1624157, by rfl⟩ : syracuseStep 2165543 = 3248315) B3248315
theorem B1444649 : Blo 960589 1444649 := bstep (se 2 (by rfl) ⟨541743, by rfl⟩ : syracuseStep 1444649 = 1083487) B1083487
theorem B1444859 : Blo 960589 1444859 := bstep (se 1 (by rfl) ⟨1083644, by rfl⟩ : syracuseStep 1444859 = 2167289) B2167289
theorem B1444919 : Blo 960589 1444919 := bstep (se 1 (by rfl) ⟨1083689, by rfl⟩ : syracuseStep 1444919 = 2167379) B2167379
theorem B2165867 : Blo 960589 2165867 := bstep (se 1 (by rfl) ⟨1624400, by rfl⟩ : syracuseStep 2165867 = 3248801) B3248801
theorem B13864061 : Blo 960589 13864061 := bstep (se 3 (by rfl) ⟨2599511, by rfl⟩ : syracuseStep 13864061 = 5199023) B5199023
theorem B1445039 : Blo 960589 1445039 := bstep (se 1 (by rfl) ⟨1083779, by rfl⟩ : syracuseStep 1445039 = 2167559) B2167559
theorem B3247289 : Blo 960589 3247289 := bstep (se 2 (by rfl) ⟨1217733, by rfl⟩ : syracuseStep 3247289 = 2435467) B2435467
theorem B2821307 : Blo 960589 2821307 := bstep (se 1 (by rfl) ⟨2115980, by rfl⟩ : syracuseStep 2821307 = 4231961) B4231961
theorem B3247451 : Blo 960589 3247451 := bstep (se 1 (by rfl) ⟨2435588, by rfl⟩ : syracuseStep 3247451 = 4871177) B4871177
theorem B2166137 : Blo 960589 2166137 := bstep (se 2 (by rfl) ⟨812301, by rfl⟩ : syracuseStep 2166137 = 1624603) B1624603
theorem B70192655 : Blo 960589 70192655 := bstep (se 1 (by rfl) ⟨52644491, by rfl⟩ : syracuseStep 70192655 = 105288983) B105288983
theorem B1543783 : Blo 960589 1543783 := bstep (se 1 (by rfl) ⟨1157837, by rfl⟩ : syracuseStep 1543783 = 2315675) B2315675
theorem B2166443 : Blo 960589 2166443 := bstep (se 1 (by rfl) ⟨1624832, by rfl⟩ : syracuseStep 2166443 = 3249665) B3249665
theorem B1445759 : Blo 960589 1445759 := bstep (se 1 (by rfl) ⟨1084319, by rfl⟩ : syracuseStep 1445759 = 2168639) B2168639
theorem B2166767 : Blo 960589 2166767 := bstep (se 1 (by rfl) ⟨1625075, by rfl⟩ : syracuseStep 2166767 = 3250151) B3250151
theorem B2166839 : Blo 960589 2166839 := bstep (se 1 (by rfl) ⟨1625129, by rfl⟩ : syracuseStep 2166839 = 3250259) B3250259
theorem B1445951 : Blo 960589 1445951 := bstep (se 1 (by rfl) ⟨1084463, by rfl⟩ : syracuseStep 1445951 = 2168927) B2168927
theorem B1216615 : Blo 960589 1216615 := bstep (se 1 (by rfl) ⟨912461, by rfl⟩ : syracuseStep 1216615 = 1824923) B1824923
theorem B1544347 : Blo 960589 1544347 := bstep (se 1 (by rfl) ⟨1158260, by rfl⟩ : syracuseStep 1544347 = 2316521) B2316521
theorem B2166983 : Blo 960589 2166983 := bstep (se 1 (by rfl) ⟨1625237, by rfl⟩ : syracuseStep 2166983 = 3250475) B3250475
theorem B1446185 : Blo 960589 1446185 := bstep (se 2 (by rfl) ⟨542319, by rfl⟩ : syracuseStep 1446185 = 1084639) B1084639
theorem B2167163 : Blo 960589 2167163 := bstep (se 1 (by rfl) ⟨1625372, by rfl⟩ : syracuseStep 2167163 = 3250745) B3250745
theorem B1446455 : Blo 960589 1446455 := bstep (se 1 (by rfl) ⟨1084841, by rfl⟩ : syracuseStep 1446455 = 2169683) B2169683
theorem B2167433 : Blo 960589 2167433 := bstep (se 2 (by rfl) ⟨812787, by rfl⟩ : syracuseStep 2167433 = 1625575) B1625575
theorem B1446815 : Blo 960589 1446815 := bstep (se 1 (by rfl) ⟨1085111, by rfl⟩ : syracuseStep 1446815 = 2170223) B2170223
theorem B3249341 : Blo 960589 3249341 := bstep (se 3 (by rfl) ⟨609251, by rfl⟩ : syracuseStep 3249341 = 1218503) B1218503
theorem B3249449 : Blo 960589 3249449 := bstep (se 2 (by rfl) ⟨1218543, by rfl⟩ : syracuseStep 3249449 = 2437087) B2437087
theorem B4396349 : Blo 960589 4396349 := bstep (se 3 (by rfl) ⟨824315, by rfl⟩ : syracuseStep 4396349 = 1648631) B1648631
theorem B12358979 : Blo 960589 12358979 := bstep (se 1 (by rfl) ⟨9269234, by rfl⟩ : syracuseStep 12358979 = 18538469) B18538469
theorem B2168171 : Blo 960589 2168171 := bstep (se 1 (by rfl) ⟨1626128, by rfl⟩ : syracuseStep 2168171 = 3252257) B3252257
theorem B2168441 : Blo 960589 2168441 := bstep (se 2 (by rfl) ⟨813165, by rfl⟩ : syracuseStep 2168441 = 1626331) B1626331
theorem B8230571 : Blo 960589 8230571 := bstep (se 1 (by rfl) ⟨6172928, by rfl⟩ : syracuseStep 8230571 = 12345857) B12345857
theorem B3250043 : Blo 960589 3250043 := bstep (se 1 (by rfl) ⟨2437532, by rfl⟩ : syracuseStep 3250043 = 4875065) B4875065
theorem B2168801 : Blo 960589 2168801 := bstep (se 2 (by rfl) ⟨813300, by rfl⟩ : syracuseStep 2168801 = 1626601) B1626601
theorem B3250313 : Blo 960589 3250313 := bstep (se 2 (by rfl) ⟨1218867, by rfl⟩ : syracuseStep 3250313 = 2437735) B2437735
theorem B32086367 : Blo 960589 32086367 := bstep (se 1 (by rfl) ⟨24064775, by rfl⟩ : syracuseStep 32086367 = 48129551) B48129551
theorem B3086849 : Blo 960589 3086849 := bstep (se 2 (by rfl) ⟨1157568, by rfl⟩ : syracuseStep 3086849 = 2315137) B2315137
theorem B7314299 : Blo 960589 7314299 := bstep (se 1 (by rfl) ⟨5485724, by rfl⟩ : syracuseStep 7314299 = 10971449) B10971449
theorem B35068879 : Blo 960589 35068879 := bstep (se 1 (by rfl) ⟨26301659, by rfl⟩ : syracuseStep 35068879 = 52603319) B52603319
theorem B4398209 : Blo 960589 4398209 := bstep (se 2 (by rfl) ⟨1649328, by rfl⟩ : syracuseStep 4398209 = 3298657) B3298657
theorem B2432207 : Blo 960589 2432207 := bstep (se 1 (by rfl) ⟨1824155, by rfl⟩ : syracuseStep 2432207 = 3648311) B3648311
theorem B7314785 : Blo 960589 7314785 := bstep (se 2 (by rfl) ⟨2743044, by rfl⟩ : syracuseStep 7314785 = 5486089) B5486089
theorem B3908159 : Blo 960589 3908159 := bstep (se 1 (by rfl) ⟨2931119, by rfl⟩ : syracuseStep 3908159 = 5862239) B5862239
theorem B7316243 : Blo 960589 7316243 := bstep (se 1 (by rfl) ⟨5487182, by rfl⟩ : syracuseStep 7316243 = 10974365) B10974365
theorem B6169391 : Blo 960589 6169391 := bstep (se 1 (by rfl) ⟨4627043, by rfl⟩ : syracuseStep 6169391 = 9254087) B9254087
theorem B15836435 : Blo 960589 15836435 := bstep (se 1 (by rfl) ⟨11877326, by rfl⟩ : syracuseStep 15836435 = 23754653) B23754653
theorem B16459361 : Blo 960589 16459361 := bstep (se 2 (by rfl) ⟨6172260, by rfl⟩ : syracuseStep 16459361 = 12344521) B12344521
theorem B4105889 : Blo 960589 4105889 := bstep (se 2 (by rfl) ⟨1539708, by rfl⟩ : syracuseStep 4105889 = 3079417) B3079417
theorem B7317215 : Blo 960589 7317215 := bstep (se 1 (by rfl) ⟨5487911, by rfl⟩ : syracuseStep 7317215 = 10975823) B10975823
theorem B7415639 : Blo 960589 7415639 := bstep (se 1 (by rfl) ⟨5561729, by rfl⟩ : syracuseStep 7415639 = 11123459) B11123459
theorem B3647369 : Blo 960589 3647369 := bstep (se 2 (by rfl) ⟨1367763, by rfl⟩ : syracuseStep 3647369 = 2735527) B2735527
theorem B960735 : Blo 960589 960735 := bstep (se 1 (by rfl) ⟨720551, by rfl⟩ : syracuseStep 960735 = 1441103) B1441103
theorem B960795 : Blo 960589 960795 := bstep (se 1 (by rfl) ⟨720596, by rfl⟩ : syracuseStep 960795 = 1441193) B1441193
theorem B3287369 : Blo 960589 3287369 := bstep (se 2 (by rfl) ⟨1232763, by rfl⟩ : syracuseStep 3287369 = 2465527) B2465527
theorem B960895 : Blo 960589 960895 := bstep (se 1 (by rfl) ⟨720671, by rfl⟩ : syracuseStep 960895 = 1441343) B1441343
theorem B3910151 : Blo 960589 3910151 := bstep (se 1 (by rfl) ⟨2932613, by rfl⟩ : syracuseStep 3910151 = 5865227) B5865227
theorem B961071 : Blo 960589 961071 := bstep (se 1 (by rfl) ⟨720803, by rfl⟩ : syracuseStep 961071 = 1441607) B1441607
theorem B961127 : Blo 960589 961127 := bstep (se 1 (by rfl) ⟨720845, by rfl⟩ : syracuseStep 961127 = 1441691) B1441691
theorem B8235695 : Blo 960589 8235695 := bstep (se 1 (by rfl) ⟨6176771, by rfl⟩ : syracuseStep 8235695 = 12353543) B12353543
theorem B961503 : Blo 960589 961503 := bstep (se 1 (by rfl) ⟨721127, by rfl⟩ : syracuseStep 961503 = 1442255) B1442255
theorem B961531 : Blo 960589 961531 := bstep (se 1 (by rfl) ⟨721148, by rfl⟩ : syracuseStep 961531 = 1442297) B1442297
theorem B961599 : Blo 960589 961599 := bstep (se 1 (by rfl) ⟨721199, by rfl⟩ : syracuseStep 961599 = 1442399) B1442399
theorem B9252089 : Blo 960589 9252089 := bstep (se 2 (by rfl) ⟨3469533, by rfl⟩ : syracuseStep 9252089 = 6939067) B6939067
theorem B961919 : Blo 960589 961919 := bstep (se 1 (by rfl) ⟨721439, by rfl⟩ : syracuseStep 961919 = 1442879) B1442879
theorem B961947 : Blo 960589 961947 := bstep (se 1 (by rfl) ⟨721460, by rfl⟩ : syracuseStep 961947 = 1442921) B1442921
theorem B962015 : Blo 960589 962015 := bstep (se 1 (by rfl) ⟨721511, by rfl⟩ : syracuseStep 962015 = 1443023) B1443023
theorem B962151 : Blo 960589 962151 := bstep (se 1 (by rfl) ⟨721613, by rfl⟩ : syracuseStep 962151 = 1443227) B1443227
theorem B962299 : Blo 960589 962299 := bstep (se 1 (by rfl) ⟨721724, by rfl⟩ : syracuseStep 962299 = 1443449) B1443449
theorem B962367 : Blo 960589 962367 := bstep (se 1 (by rfl) ⟨721775, by rfl⟩ : syracuseStep 962367 = 1443551) B1443551
theorem B3518333 : Blo 960589 3518333 := bstep (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) B1319375
theorem B962431 : Blo 960589 962431 := bstep (se 1 (by rfl) ⟨721823, by rfl⟩ : syracuseStep 962431 = 1443647) B1443647
theorem B962543 : Blo 960589 962543 := bstep (se 1 (by rfl) ⟨721907, by rfl⟩ : syracuseStep 962543 = 1443815) B1443815
theorem B962555 : Blo 960589 962555 := bstep (se 1 (by rfl) ⟨721916, by rfl⟩ : syracuseStep 962555 = 1443833) B1443833
theorem B962623 : Blo 960589 962623 := bstep (se 1 (by rfl) ⟨721967, by rfl⟩ : syracuseStep 962623 = 1443935) B1443935
theorem B962663 : Blo 960589 962663 := bstep (se 1 (by rfl) ⟨721997, by rfl⟩ : syracuseStep 962663 = 1443995) B1443995
theorem B962687 : Blo 960589 962687 := bstep (se 1 (by rfl) ⟨722015, by rfl⟩ : syracuseStep 962687 = 1444031) B1444031
theorem B962715 : Blo 960589 962715 := bstep (se 1 (by rfl) ⟨722036, by rfl⟩ : syracuseStep 962715 = 1444073) B1444073
theorem B15642881 : Blo 960589 15642881 := bstep (se 2 (by rfl) ⟨5866080, by rfl⟩ : syracuseStep 15642881 = 11732161) B11732161
theorem B962919 : Blo 960589 962919 := bstep (se 1 (by rfl) ⟨722189, by rfl⟩ : syracuseStep 962919 = 1444379) B1444379
theorem B962971 : Blo 960589 962971 := bstep (se 1 (by rfl) ⟨722228, by rfl⟩ : syracuseStep 962971 = 1444457) B1444457
theorem B9253439 : Blo 960589 9253439 := bstep (se 1 (by rfl) ⟨6940079, by rfl⟩ : syracuseStep 9253439 = 13880159) B13880159
theorem B963323 : Blo 960589 963323 := bstep (se 1 (by rfl) ⟨722492, by rfl⟩ : syracuseStep 963323 = 1444985) B1444985
theorem B963391 : Blo 960589 963391 := bstep (se 1 (by rfl) ⟨722543, by rfl⟩ : syracuseStep 963391 = 1445087) B1445087
theorem B963419 : Blo 960589 963419 := bstep (se 1 (by rfl) ⟨722564, by rfl⟩ : syracuseStep 963419 = 1445129) B1445129
theorem B963487 : Blo 960589 963487 := bstep (se 1 (by rfl) ⟨722615, by rfl⟩ : syracuseStep 963487 = 1445231) B1445231
theorem B2601935 : Blo 960589 2601935 := bstep (se 1 (by rfl) ⟨1951451, by rfl⟩ : syracuseStep 2601935 = 3902903) B3902903
theorem B963567 : Blo 960589 963567 := bstep (se 1 (by rfl) ⟨722675, by rfl⟩ : syracuseStep 963567 = 1445351) B1445351
theorem B963655 : Blo 960589 963655 := bstep (se 1 (by rfl) ⟨722741, by rfl⟩ : syracuseStep 963655 = 1445483) B1445483
theorem B963739 : Blo 960589 963739 := bstep (se 1 (by rfl) ⟨722804, by rfl⟩ : syracuseStep 963739 = 1445609) B1445609
theorem B963835 : Blo 960589 963835 := bstep (se 1 (by rfl) ⟨722876, by rfl⟩ : syracuseStep 963835 = 1445753) B1445753
theorem B4109579 : Blo 960589 4109579 := bstep (se 1 (by rfl) ⟨3082184, by rfl⟩ : syracuseStep 4109579 = 6164369) B6164369
theorem B963903 : Blo 960589 963903 := bstep (se 1 (by rfl) ⟨722927, by rfl⟩ : syracuseStep 963903 = 1445855) B1445855
theorem B964071 : Blo 960589 964071 := bstep (se 1 (by rfl) ⟨723053, by rfl⟩ : syracuseStep 964071 = 1446107) B1446107
theorem B964079 : Blo 960589 964079 := bstep (se 1 (by rfl) ⟨723059, by rfl⟩ : syracuseStep 964079 = 1446119) B1446119
theorem B964187 : Blo 960589 964187 := bstep (se 1 (by rfl) ⟨723140, by rfl⟩ : syracuseStep 964187 = 1446281) B1446281
theorem B964251 : Blo 960589 964251 := bstep (se 1 (by rfl) ⟨723188, by rfl⟩ : syracuseStep 964251 = 1446377) B1446377
theorem B964335 : Blo 960589 964335 := bstep (se 1 (by rfl) ⟨723251, by rfl⟩ : syracuseStep 964335 = 1446503) B1446503
theorem B964423 : Blo 960589 964423 := bstep (se 1 (by rfl) ⟨723317, by rfl⟩ : syracuseStep 964423 = 1446635) B1446635
theorem B964443 : Blo 960589 964443 := bstep (se 1 (by rfl) ⟨723332, by rfl⟩ : syracuseStep 964443 = 1446665) B1446665
theorem B964511 : Blo 960589 964511 := bstep (se 1 (by rfl) ⟨723383, by rfl⟩ : syracuseStep 964511 = 1446767) B1446767
theorem B6174721 : Blo 960589 6174721 := bstep (se 2 (by rfl) ⟨2315520, by rfl⟩ : syracuseStep 6174721 = 4631041) B4631041
theorem B16693289 : Blo 960589 16693289 := bstep (se 2 (by rfl) ⟨6259983, by rfl⟩ : syracuseStep 16693289 = 12519967) B12519967
theorem B1947883 : Blo 960589 1947883 := bstep (se 1 (by rfl) ⟨1460912, by rfl⟩ : syracuseStep 1947883 = 2921825) B2921825
theorem B2308391 : Blo 960589 2308391 := bstep (se 1 (by rfl) ⟨1731293, by rfl⟩ : syracuseStep 2308391 = 3462587) B3462587
theorem B8206991 : Blo 960589 8206991 := bstep (se 1 (by rfl) ⟨6155243, by rfl⟩ : syracuseStep 8206991 = 12310487) B12310487
theorem B2439983 : Blo 960589 2439983 := bstep (se 1 (by rfl) ⟨1829987, by rfl⟩ : syracuseStep 2439983 = 3659975) B3659975
theorem B7323047 : Blo 960589 7323047 := bstep (se 1 (by rfl) ⟨5492285, by rfl⟩ : syracuseStep 7323047 = 10984571) B10984571
theorem B2440631 : Blo 960589 2440631 := bstep (se 1 (by rfl) ⟨1830473, by rfl⟩ : syracuseStep 2440631 = 3660947) B3660947
theorem B4931399 : Blo 960589 4931399 := bstep (se 1 (by rfl) ⟨3698549, by rfl⟩ : syracuseStep 4931399 = 7397099) B7397099
theorem B15417325 : Blo 960589 15417325 := bstep (se 3 (by rfl) ⟨2890748, by rfl⟩ : syracuseStep 15417325 = 5781497) B5781497
theorem B1622207 : Blo 960589 1622207 := bstep (se 1 (by rfl) ⟨1216655, by rfl⟩ : syracuseStep 1622207 = 2433311) B2433311
theorem B15843539 : Blo 960589 15843539 := bstep (se 1 (by rfl) ⟨11882654, by rfl⟩ : syracuseStep 15843539 = 23765309) B23765309
theorem B1622443 : Blo 960589 1622443 := bstep (se 1 (by rfl) ⟨1216832, by rfl⟩ : syracuseStep 1622443 = 2433665) B2433665
theorem B1622639 : Blo 960589 1622639 := bstep (se 1 (by rfl) ⟨1216979, by rfl⟩ : syracuseStep 1622639 = 2433959) B2433959
theorem B1622983 : Blo 960589 1622983 := bstep (se 1 (by rfl) ⟨1217237, by rfl⟩ : syracuseStep 1622983 = 2434475) B2434475
theorem B8209451 : Blo 960589 8209451 := bstep (se 1 (by rfl) ⟨6157088, by rfl⟩ : syracuseStep 8209451 = 12314177) B12314177
theorem B2737327 : Blo 960589 2737327 := bstep (se 1 (by rfl) ⟨2052995, by rfl⟩ : syracuseStep 2737327 = 4105991) B4105991
theorem B1951055 : Blo 960589 1951055 := bstep (se 1 (by rfl) ⟨1463291, by rfl⟩ : syracuseStep 1951055 = 2926583) B2926583
theorem B5555561 : Blo 960589 5555561 := bstep (se 2 (by rfl) ⟨2083335, by rfl⟩ : syracuseStep 5555561 = 4166671) B4166671
theorem B2737577 : Blo 960589 2737577 := bstep (se 2 (by rfl) ⟨1026591, by rfl⟩ : syracuseStep 2737577 = 2053183) B2053183
theorem B2606519 : Blo 960589 2606519 := bstep (se 1 (by rfl) ⟨1954889, by rfl⟩ : syracuseStep 2606519 = 3909779) B3909779
theorem B1623847 : Blo 960589 1623847 := bstep (se 1 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 1623847 = 2435771) B2435771
theorem B2083241 : Blo 960589 2083241 := bstep (se 2 (by rfl) ⟨781215, by rfl⟩ : syracuseStep 2083241 = 1562431) B1562431
theorem B8211091 : Blo 960589 8211091 := bstep (se 1 (by rfl) ⟨6158318, by rfl⟩ : syracuseStep 8211091 = 12316637) B12316637
theorem B1624873 : Blo 960589 1624873 := bstep (se 2 (by rfl) ⟨609327, by rfl⟩ : syracuseStep 1624873 = 1218655) B1218655
theorem B2739035 : Blo 960589 2739035 := bstep (se 1 (by rfl) ⟨2054276, by rfl⟩ : syracuseStep 2739035 = 4108553) B4108553
theorem B1625143 : Blo 960589 1625143 := bstep (se 1 (by rfl) ⟨1218857, by rfl⟩ : syracuseStep 1625143 = 2437715) B2437715
theorem B8212049 : Blo 960589 8212049 := bstep (se 2 (by rfl) ⟨3079518, by rfl⟩ : syracuseStep 8212049 = 6159037) B6159037
theorem B4116071 : Blo 960589 4116071 := bstep (se 1 (by rfl) ⟨3087053, by rfl⟩ : syracuseStep 4116071 = 6174107) B6174107
theorem B7294859 : Blo 960589 7294859 := bstep (se 1 (by rfl) ⟨5471144, by rfl⟩ : syracuseStep 7294859 = 10942289) B10942289
theorem B4116379 : Blo 960589 4116379 := bstep (se 1 (by rfl) ⟨3087284, by rfl⟩ : syracuseStep 4116379 = 6174569) B6174569
theorem B4116413 : Blo 960589 4116413 := bstep (se 3 (by rfl) ⟨771827, by rfl⟩ : syracuseStep 4116413 = 1543655) B1543655
theorem B1626095 : Blo 960589 1626095 := bstep (se 1 (by rfl) ⟨1219571, by rfl⟩ : syracuseStep 1626095 = 2439143) B2439143
theorem B6934567 : Blo 960589 6934567 := bstep (se 1 (by rfl) ⟨5200925, by rfl⟩ : syracuseStep 6934567 = 10401851) B10401851
theorem B2052449 : Blo 960589 2052449 := bstep (se 2 (by rfl) ⟨769668, by rfl⟩ : syracuseStep 2052449 = 1539337) B1539337
theorem B1823647 : Blo 960589 1823647 := bstep (se 1 (by rfl) ⟨1367735, by rfl⟩ : syracuseStep 1823647 = 2735471) B2735471
theorem B1823951 : Blo 960589 1823951 := bstep (se 1 (by rfl) ⟨1367963, by rfl⟩ : syracuseStep 1823951 = 2735927) B2735927
theorem B3462671 : Blo 960589 3462671 := bstep (se 1 (by rfl) ⟨2597003, by rfl⟩ : syracuseStep 3462671 = 5194007) B5194007
theorem B4872635 : Blo 960589 4872635 := bstep (se 1 (by rfl) ⟨3654476, by rfl⟩ : syracuseStep 4872635 = 7308953) B7308953
theorem B2742761 : Blo 960589 2742761 := bstep (se 2 (by rfl) ⟨1028535, by rfl⟩ : syracuseStep 2742761 = 2057071) B2057071
theorem B18995735 : Blo 960589 18995735 := bstep (se 1 (by rfl) ⟨14246801, by rfl⟩ : syracuseStep 18995735 = 28493603) B28493603
theorem B1825591 : Blo 960589 1825591 := bstep (se 1 (by rfl) ⟨1369193, by rfl⟩ : syracuseStep 1825591 = 2738387) B2738387
theorem B3464171 : Blo 960589 3464171 := bstep (se 1 (by rfl) ⟨2598128, by rfl⟩ : syracuseStep 3464171 = 5196257) B5196257
theorem B18505097 : Blo 960589 18505097 := bstep (se 2 (by rfl) ⟨6939411, by rfl⟩ : syracuseStep 18505097 = 13878823) B13878823
theorem B3661433 : Blo 960589 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B9264851 : Blo 960589 9264851 := bstep (se 1 (by rfl) ⟨6948638, by rfl⟩ : syracuseStep 9264851 = 13897277) B13897277
theorem B15621923 : Blo 960589 15621923 := bstep (se 1 (by rfl) ⟨11716442, by rfl⟩ : syracuseStep 15621923 = 23432885) B23432885
theorem B4120475 : Blo 960589 4120475 := bstep (se 1 (by rfl) ⟨3090356, by rfl⟩ : syracuseStep 4120475 = 6180713) B6180713
theorem B2744219 : Blo 960589 2744219 := bstep (se 1 (by rfl) ⟨2058164, by rfl⟩ : syracuseStep 2744219 = 4116329) B4116329
theorem B1826783 : Blo 960589 1826783 := bstep (se 1 (by rfl) ⟨1370087, by rfl⟩ : syracuseStep 1826783 = 2740175) B2740175
theorem B1368743 : Blo 960589 1368743 := bstep (se 1 (by rfl) ⟨1026557, by rfl⟩ : syracuseStep 1368743 = 2053115) B2053115
theorem B1827535 : Blo 960589 1827535 := bstep (se 1 (by rfl) ⟨1370651, by rfl⟩ : syracuseStep 1827535 = 2741303) B2741303
theorem B20800421 : Blo 960589 20800421 := bstep (se 4 (by rfl) ⟨1950039, by rfl⟩ : syracuseStep 20800421 = 3900079) B3900079
theorem B2745323 : Blo 960589 2745323 := bstep (se 1 (by rfl) ⟨2058992, by rfl⟩ : syracuseStep 2745323 = 4117985) B4117985
theorem B4384327 : Blo 960589 4384327 := bstep (se 1 (by rfl) ⟨3288245, by rfl⟩ : syracuseStep 4384327 = 6576491) B6576491
theorem B1828423 : Blo 960589 1828423 := bstep (se 1 (by rfl) ⟨1371317, by rfl⟩ : syracuseStep 1828423 = 2742635) B2742635
theorem B7300691 : Blo 960589 7300691 := bstep (se 1 (by rfl) ⟨5475518, by rfl⟩ : syracuseStep 7300691 = 10951037) B10951037
theorem B4384381 : Blo 960589 4384381 := bstep (se 3 (by rfl) ⟨822071, by rfl⟩ : syracuseStep 4384381 = 1644143) B1644143
theorem B6580075 : Blo 960589 6580075 := bstep (se 1 (by rfl) ⟨4935056, by rfl⟩ : syracuseStep 6580075 = 9870113) B9870113
theorem B3467227 : Blo 960589 3467227 := bstep (se 1 (by rfl) ⟨2600420, by rfl⟩ : syracuseStep 3467227 = 5200841) B5200841
theorem B3467387 : Blo 960589 3467387 := bstep (se 1 (by rfl) ⟨2600540, by rfl⟩ : syracuseStep 3467387 = 5201081) B5201081
theorem B38070577 : Blo 960589 38070577 := bstep (se 2 (by rfl) ⟨14276466, by rfl⟩ : syracuseStep 38070577 = 28552933) B28552933
theorem B6580673 : Blo 960589 6580673 := bstep (se 2 (by rfl) ⟨2467752, by rfl⟩ : syracuseStep 6580673 = 4935505) B4935505
theorem B7301663 : Blo 960589 7301663 := bstep (se 1 (by rfl) ⟨5476247, by rfl⟩ : syracuseStep 7301663 = 10952495) B10952495
theorem B10414655 : Blo 960589 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B1830367 : Blo 960589 1830367 := bstep (se 1 (by rfl) ⟨1372775, by rfl⟩ : syracuseStep 1830367 = 2745551) B2745551
theorem B4877819 : Blo 960589 4877819 := bstep (se 1 (by rfl) ⟨3658364, by rfl⟩ : syracuseStep 4877819 = 7316729) B7316729
theorem B2059847 : Blo 960589 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B83259089 : Blo 960589 83259089 := bstep (se 2 (by rfl) ⟨31222158, by rfl⟩ : syracuseStep 83259089 = 62444317) B62444317
theorem B1732691 : Blo 960589 1732691 := bstep (se 1 (by rfl) ⟨1299518, by rfl⟩ : syracuseStep 1732691 = 2599037) B2599037
theorem B1831187 : Blo 960589 1831187 := bstep (se 1 (by rfl) ⟨1373390, by rfl⟩ : syracuseStep 1831187 = 2746781) B2746781
theorem B4616473 : Blo 960589 4616473 := bstep (se 2 (by rfl) ⟨1731177, by rfl⟩ : syracuseStep 4616473 = 3462355) B3462355
theorem B62419409 : Blo 960589 62419409 := bstep (se 2 (by rfl) ⟨23407278, by rfl⟩ : syracuseStep 62419409 = 46814557) B46814557
theorem B14054573 : Blo 960589 14054573 := bstep (se 3 (by rfl) ⟨2635232, by rfl⟩ : syracuseStep 14054573 = 5270465) B5270465
theorem B35092237 : Blo 960589 35092237 := bstep (se 3 (by rfl) ⟨6579794, by rfl⟩ : syracuseStep 35092237 = 13159589) B13159589
theorem B7305065 : Blo 960589 7305065 := bstep (se 2 (by rfl) ⟨2739399, by rfl⟩ : syracuseStep 7305065 = 5478799) B5478799
theorem B3242537 : Blo 960589 3242537 := bstep (se 2 (by rfl) ⟨1215951, by rfl⟩ : syracuseStep 3242537 = 2431903) B2431903
theorem B2161385 : Blo 960589 2161385 := bstep (se 2 (by rfl) ⟨810519, by rfl⟩ : syracuseStep 2161385 = 1621039) B1621039
theorem B2161619 : Blo 960589 2161619 := bstep (se 1 (by rfl) ⟨1621214, by rfl⟩ : syracuseStep 2161619 = 3242429) B3242429
theorem B21429319 : Blo 960589 21429319 := bstep (se 1 (by rfl) ⟨16071989, by rfl⟩ : syracuseStep 21429319 = 32143979) B32143979
theorem B2161889 : Blo 960589 2161889 := bstep (se 2 (by rfl) ⟨810708, by rfl⟩ : syracuseStep 2161889 = 1621417) B1621417
theorem B2162195 : Blo 960589 2162195 := bstep (se 1 (by rfl) ⟨1621646, by rfl⟩ : syracuseStep 2162195 = 3243293) B3243293
theorem B4619855 : Blo 960589 4619855 := bstep (se 1 (by rfl) ⟨3464891, by rfl⟩ : syracuseStep 4619855 = 6929783) B6929783
theorem B1441391 : Blo 960589 1441391 := bstep (se 1 (by rfl) ⟨1081043, by rfl⟩ : syracuseStep 1441391 = 2162087) B2162087
theorem B1441511 : Blo 960589 1441511 := bstep (se 1 (by rfl) ⟨1081133, by rfl⟩ : syracuseStep 1441511 = 2162267) B2162267
theorem B3342223 : Blo 960589 3342223 := bstep (se 1 (by rfl) ⟨2506667, by rfl⟩ : syracuseStep 3342223 = 5013335) B5013335
theorem B1081255 : Blo 960589 1081255 := bstep (se 1 (by rfl) ⟨810941, by rfl⟩ : syracuseStep 1081255 = 1621883) B1621883
theorem B1441703 : Blo 960589 1441703 := bstep (se 1 (by rfl) ⟨1081277, by rfl⟩ : syracuseStep 1441703 = 2162555) B2162555
theorem B59998157 : Blo 960589 59998157 := bstep (se 3 (by rfl) ⟨11249654, by rfl⟩ : syracuseStep 59998157 = 22499309) B22499309
theorem B1441919 : Blo 960589 1441919 := bstep (se 1 (by rfl) ⟨1081439, by rfl⟩ : syracuseStep 1441919 = 2162879) B2162879
theorem B1081471 : Blo 960589 1081471 := bstep (se 1 (by rfl) ⟨811103, by rfl⟩ : syracuseStep 1081471 = 1622207) B1622207
theorem B4620509 : Blo 960589 4620509 := bstep (se 3 (by rfl) ⟨866345, by rfl⟩ : syracuseStep 4620509 = 1732691) B1732691
theorem B1442207 : Blo 960589 1442207 := bstep (se 1 (by rfl) ⟨1081655, by rfl⟩ : syracuseStep 1442207 = 2163311) B2163311
theorem B1081759 : Blo 960589 1081759 := bstep (se 1 (by rfl) ⟨811319, by rfl⟩ : syracuseStep 1081759 = 1622639) B1622639
theorem B2163257 : Blo 960589 2163257 := bstep (se 2 (by rfl) ⟨811221, by rfl⟩ : syracuseStep 2163257 = 1622443) B1622443
theorem B1442471 : Blo 960589 1442471 := bstep (se 1 (by rfl) ⟨1081853, by rfl⟩ : syracuseStep 1442471 = 2163707) B2163707
theorem B3080891 : Blo 960589 3080891 := bstep (se 1 (by rfl) ⟨2310668, by rfl⟩ : syracuseStep 3080891 = 4621337) B4621337
theorem B5472967 : Blo 960589 5472967 := bstep (se 1 (by rfl) ⟨4104725, by rfl⟩ : syracuseStep 5472967 = 8209451) B8209451
theorem B4883165 : Blo 960589 4883165 := bstep (se 3 (by rfl) ⟨915593, by rfl⟩ : syracuseStep 4883165 = 1831187) B1831187
theorem B1442591 : Blo 960589 1442591 := bstep (se 1 (by rfl) ⟨1081943, by rfl⟩ : syracuseStep 1442591 = 2163887) B2163887
theorem B1442615 : Blo 960589 1442615 := bstep (se 1 (by rfl) ⟨1081961, by rfl⟩ : syracuseStep 1442615 = 2163923) B2163923
theorem B1737679 : Blo 960589 1737679 := bstep (se 1 (by rfl) ⟨1303259, by rfl⟩ : syracuseStep 1737679 = 2606519) B2606519
theorem B1442795 : Blo 960589 1442795 := bstep (se 1 (by rfl) ⟨1082096, by rfl⟩ : syracuseStep 1442795 = 2164193) B2164193
theorem B2163977 : Blo 960589 2163977 := bstep (se 2 (by rfl) ⟨811491, by rfl⟩ : syracuseStep 2163977 = 1622983) B1622983
theorem B1443305 : Blo 960589 1443305 := bstep (se 2 (by rfl) ⟨541239, by rfl⟩ : syracuseStep 1443305 = 1082479) B1082479
theorem B9242171 : Blo 960589 9242171 := bstep (se 1 (by rfl) ⟨6931628, by rfl⟩ : syracuseStep 9242171 = 13863257) B13863257
theorem B2164499 : Blo 960589 2164499 := bstep (se 1 (by rfl) ⟨1623374, by rfl⟩ : syracuseStep 2164499 = 3246749) B3246749
theorem B1443695 : Blo 960589 1443695 := bstep (se 1 (by rfl) ⟨1082771, by rfl⟩ : syracuseStep 1443695 = 2165543) B2165543
theorem B1443881 : Blo 960589 1443881 := bstep (se 2 (by rfl) ⟨541455, by rfl⟩ : syracuseStep 1443881 = 1082911) B1082911
theorem B1443911 : Blo 960589 1443911 := bstep (se 1 (by rfl) ⟨1082933, by rfl⟩ : syracuseStep 1443911 = 2165867) B2165867
theorem B9242707 : Blo 960589 9242707 := bstep (se 1 (by rfl) ⟨6932030, by rfl⟩ : syracuseStep 9242707 = 13864061) B13864061
theorem B2164859 : Blo 960589 2164859 := bstep (se 1 (by rfl) ⟨1623644, by rfl⟩ : syracuseStep 2164859 = 3247289) B3247289
theorem B2164967 : Blo 960589 2164967 := bstep (se 1 (by rfl) ⟨1623725, by rfl⟩ : syracuseStep 2164967 = 3247451) B3247451
theorem B1444091 : Blo 960589 1444091 := bstep (se 1 (by rfl) ⟨1083068, by rfl⟩ : syracuseStep 1444091 = 2166137) B2166137
theorem B46795103 : Blo 960589 46795103 := bstep (se 1 (by rfl) ⟨35096327, by rfl⟩ : syracuseStep 46795103 = 70192655) B70192655
theorem B2165129 : Blo 960589 2165129 := bstep (se 2 (by rfl) ⟨811923, by rfl⟩ : syracuseStep 2165129 = 1623847) B1623847
theorem B5474699 : Blo 960589 5474699 := bstep (se 1 (by rfl) ⟨4106024, by rfl⟩ : syracuseStep 5474699 = 8212049) B8212049
theorem B1444295 : Blo 960589 1444295 := bstep (se 1 (by rfl) ⟨1083221, by rfl⟩ : syracuseStep 1444295 = 2166443) B2166443
theorem B4622969 : Blo 960589 4622969 := bstep (se 2 (by rfl) ⟨1733613, by rfl⟩ : syracuseStep 4622969 = 3467227) B3467227
theorem B1444511 : Blo 960589 1444511 := bstep (se 1 (by rfl) ⟨1083383, by rfl⟩ : syracuseStep 1444511 = 2166767) B2166767
theorem B1084063 : Blo 960589 1084063 := bstep (se 1 (by rfl) ⟨813047, by rfl⟩ : syracuseStep 1084063 = 1626095) B1626095
theorem B1444559 : Blo 960589 1444559 := bstep (se 1 (by rfl) ⟨1083419, by rfl⟩ : syracuseStep 1444559 = 2166839) B2166839
theorem B1444655 : Blo 960589 1444655 := bstep (se 1 (by rfl) ⟨1083491, by rfl⟩ : syracuseStep 1444655 = 2166983) B2166983
theorem B1444775 : Blo 960589 1444775 := bstep (se 1 (by rfl) ⟨1083581, by rfl⟩ : syracuseStep 1444775 = 2167163) B2167163
theorem B50760769 : Blo 960589 50760769 := bstep (se 2 (by rfl) ⟨19035288, by rfl⟩ : syracuseStep 50760769 = 38070577) B38070577
theorem B1444955 : Blo 960589 1444955 := bstep (se 1 (by rfl) ⟨1083716, by rfl⟩ : syracuseStep 1444955 = 2167433) B2167433
theorem B1445033 : Blo 960589 1445033 := bstep (se 2 (by rfl) ⟨541887, by rfl⟩ : syracuseStep 1445033 = 1083775) B1083775
theorem B2166227 : Blo 960589 2166227 := bstep (se 1 (by rfl) ⟨1624670, by rfl⟩ : syracuseStep 2166227 = 3249341) B3249341
theorem B1215967 : Blo 960589 1215967 := bstep (se 1 (by rfl) ⟨911975, by rfl⟩ : syracuseStep 1215967 = 1823951) B1823951
theorem B10948121 : Blo 960589 10948121 := bstep (se 2 (by rfl) ⟨4105545, by rfl⟩ : syracuseStep 10948121 = 8211091) B8211091
theorem B2166299 : Blo 960589 2166299 := bstep (se 1 (by rfl) ⟨1624724, by rfl⟩ : syracuseStep 2166299 = 3249449) B3249449
theorem B1445447 : Blo 960589 1445447 := bstep (se 1 (by rfl) ⟨1084085, by rfl⟩ : syracuseStep 1445447 = 2168171) B2168171
theorem B14814829 : Blo 960589 14814829 := bstep (se 3 (by rfl) ⟨2777780, by rfl⟩ : syracuseStep 14814829 = 5555561) B5555561
theorem B2166497 : Blo 960589 2166497 := bstep (se 2 (by rfl) ⟨812436, by rfl⟩ : syracuseStep 2166497 = 1624873) B1624873
theorem B1445627 : Blo 960589 1445627 := bstep (se 1 (by rfl) ⟨1084220, by rfl⟩ : syracuseStep 1445627 = 2168441) B2168441
theorem B2166695 : Blo 960589 2166695 := bstep (se 1 (by rfl) ⟨1625021, by rfl⟩ : syracuseStep 2166695 = 3250043) B3250043
theorem B1445867 : Blo 960589 1445867 := bstep (se 1 (by rfl) ⟨1084400, by rfl⟩ : syracuseStep 1445867 = 2168801) B2168801
theorem B2166857 : Blo 960589 2166857 := bstep (se 2 (by rfl) ⟨812571, by rfl⟩ : syracuseStep 2166857 = 1625143) B1625143
theorem B2166875 : Blo 960589 2166875 := bstep (se 1 (by rfl) ⟨1625156, by rfl⟩ : syracuseStep 2166875 = 3250313) B3250313
theorem B3248423 : Blo 960589 3248423 := bstep (se 1 (by rfl) ⟨2436317, by rfl⟩ : syracuseStep 3248423 = 4872635) B4872635
theorem B1217855 : Blo 960589 1217855 := bstep (se 1 (by rfl) ⟨913391, by rfl⟩ : syracuseStep 1217855 = 1826783) B1826783
theorem B9246089 : Blo 960589 9246089 := bstep (se 2 (by rfl) ⟨3467283, by rfl⟩ : syracuseStep 9246089 = 6934567) B6934567
theorem B13866947 : Blo 960589 13866947 := bstep (se 1 (by rfl) ⟨10400210, by rfl⟩ : syracuseStep 13866947 = 20800421) B20800421
theorem B10557623 : Blo 960589 10557623 := bstep (se 1 (by rfl) ⟨7918217, by rfl⟩ : syracuseStep 10557623 = 15836435) B15836435
theorem B2431529 : Blo 960589 2431529 := bstep (se 2 (by rfl) ⟨911823, by rfl⟩ : syracuseStep 2431529 = 1823647) B1823647
theorem B2431579 : Blo 960589 2431579 := bstep (se 1 (by rfl) ⟨1823684, by rfl⟩ : syracuseStep 2431579 = 3647369) B3647369
theorem B10427069 : Blo 960589 10427069 := bstep (se 3 (by rfl) ⟨1955075, by rfl⟩ : syracuseStep 10427069 = 3910151) B3910151
theorem B6168059 : Blo 960589 6168059 := bstep (se 1 (by rfl) ⟨4626044, by rfl⟩ : syracuseStep 6168059 = 9252089) B9252089
theorem B3251879 : Blo 960589 3251879 := bstep (se 1 (by rfl) ⟨2438909, by rfl⟩ : syracuseStep 3251879 = 4877819) B4877819
theorem B8232961 : Blo 960589 8232961 := bstep (se 2 (by rfl) ⟨3087360, by rfl⟩ : syracuseStep 8232961 = 6174721) B6174721
theorem B10428587 : Blo 960589 10428587 := bstep (se 1 (by rfl) ⟨7821440, by rfl⟩ : syracuseStep 10428587 = 15642881) B15642881
theorem B2597177 : Blo 960589 2597177 := bstep (se 2 (by rfl) ⟨973941, by rfl⟩ : syracuseStep 2597177 = 1947883) B1947883
theorem B6168959 : Blo 960589 6168959 := bstep (se 1 (by rfl) ⟨4626719, by rfl⟩ : syracuseStep 6168959 = 9253439) B9253439
theorem B2434121 : Blo 960589 2434121 := bstep (se 2 (by rfl) ⟨912795, by rfl⟩ : syracuseStep 2434121 = 1825591) B1825591
theorem B13150397 : Blo 960589 13150397 := bstep (se 3 (by rfl) ⟨2465699, by rfl⟩ : syracuseStep 13150397 = 4931399) B4931399
theorem B10987933 : Blo 960589 10987933 := bstep (se 3 (by rfl) ⟨2060237, by rfl⟩ : syracuseStep 10987933 = 4120475) B4120475
theorem B960927 : Blo 960589 960927 := bstep (se 1 (by rfl) ⟨720695, by rfl⟩ : syracuseStep 960927 = 1441391) B1441391
theorem B961007 : Blo 960589 961007 := bstep (se 1 (by rfl) ⟨720755, by rfl⟩ : syracuseStep 961007 = 1441511) B1441511
theorem B961135 : Blo 960589 961135 := bstep (se 1 (by rfl) ⟨720851, by rfl⟩ : syracuseStep 961135 = 1441703) B1441703
theorem B20556433 : Blo 960589 20556433 := bstep (se 2 (by rfl) ⟨7708662, by rfl⟩ : syracuseStep 20556433 = 15417325) B15417325
theorem B961351 : Blo 960589 961351 := bstep (se 1 (by rfl) ⟨721013, by rfl⟩ : syracuseStep 961351 = 1442027) B1442027
theorem B961391 : Blo 960589 961391 := bstep (se 1 (by rfl) ⟨721043, by rfl⟩ : syracuseStep 961391 = 1442087) B1442087
theorem B42249437 : Blo 960589 42249437 := bstep (se 3 (by rfl) ⟨7921769, by rfl⟩ : syracuseStep 42249437 = 15843539) B15843539
theorem B961839 : Blo 960589 961839 := bstep (se 1 (by rfl) ⟨721379, by rfl⟩ : syracuseStep 961839 = 1442759) B1442759
theorem B961951 : Blo 960589 961951 := bstep (se 1 (by rfl) ⟨721463, by rfl⟩ : syracuseStep 961951 = 1442927) B1442927
theorem B962079 : Blo 960589 962079 := bstep (se 1 (by rfl) ⟨721559, by rfl⟩ : syracuseStep 962079 = 1443119) B1443119
theorem B2436713 : Blo 960589 2436713 := bstep (se 2 (by rfl) ⟨913767, by rfl⟩ : syracuseStep 2436713 = 1827535) B1827535
theorem B962215 : Blo 960589 962215 := bstep (se 1 (by rfl) ⟨721661, by rfl⟩ : syracuseStep 962215 = 1443323) B1443323
theorem B962239 : Blo 960589 962239 := bstep (se 1 (by rfl) ⟨721679, by rfl⟩ : syracuseStep 962239 = 1443359) B1443359
theorem B962335 : Blo 960589 962335 := bstep (se 1 (by rfl) ⟨721751, by rfl⟩ : syracuseStep 962335 = 1443503) B1443503
theorem B962415 : Blo 960589 962415 := bstep (se 1 (by rfl) ⟨721811, by rfl⟩ : syracuseStep 962415 = 1443623) B1443623
theorem B4632659 : Blo 960589 4632659 := bstep (se 1 (by rfl) ⟨3474494, by rfl⟩ : syracuseStep 4632659 = 6948989) B6948989
theorem B962783 : Blo 960589 962783 := bstep (se 1 (by rfl) ⟨722087, by rfl⟩ : syracuseStep 962783 = 1444175) B1444175
theorem B3649769 : Blo 960589 3649769 := bstep (se 2 (by rfl) ⟨1368663, by rfl⟩ : syracuseStep 3649769 = 2737327) B2737327
theorem B962815 : Blo 960589 962815 := bstep (se 1 (by rfl) ⟨722111, by rfl⟩ : syracuseStep 962815 = 1444223) B1444223
theorem B1388827 : Blo 960589 1388827 := bstep (se 1 (by rfl) ⟨1041620, by rfl⟩ : syracuseStep 1388827 = 2083241) B2083241
theorem B962843 : Blo 960589 962843 := bstep (se 1 (by rfl) ⟨722132, by rfl⟩ : syracuseStep 962843 = 1444265) B1444265
theorem B3649981 : Blo 960589 3649981 := bstep (se 3 (by rfl) ⟨684371, by rfl⟩ : syracuseStep 3649981 = 1368743) B1368743
theorem B963099 : Blo 960589 963099 := bstep (se 1 (by rfl) ⟨722324, by rfl⟩ : syracuseStep 963099 = 1444649) B1444649
theorem B963239 : Blo 960589 963239 := bstep (se 1 (by rfl) ⟨722429, by rfl⟩ : syracuseStep 963239 = 1444859) B1444859
theorem B963279 : Blo 960589 963279 := bstep (se 1 (by rfl) ⟨722459, by rfl⟩ : syracuseStep 963279 = 1444919) B1444919
theorem B5845769 : Blo 960589 5845769 := bstep (se 2 (by rfl) ⟨2192163, by rfl⟩ : syracuseStep 5845769 = 4384327) B4384327
theorem B2437897 : Blo 960589 2437897 := bstep (se 2 (by rfl) ⟨914211, by rfl⟩ : syracuseStep 2437897 = 1828423) B1828423
theorem B963359 : Blo 960589 963359 := bstep (se 1 (by rfl) ⟨722519, by rfl⟩ : syracuseStep 963359 = 1445039) B1445039
theorem B5845841 : Blo 960589 5845841 := bstep (se 2 (by rfl) ⟨2192190, by rfl⟩ : syracuseStep 5845841 = 4384381) B4384381
theorem B963839 : Blo 960589 963839 := bstep (se 1 (by rfl) ⟨722879, by rfl⟩ : syracuseStep 963839 = 1445759) B1445759
theorem B4863239 : Blo 960589 4863239 := bstep (se 1 (by rfl) ⟨3647429, by rfl⟩ : syracuseStep 4863239 = 7294859) B7294859
theorem B963967 : Blo 960589 963967 := bstep (se 1 (by rfl) ⟨722975, by rfl⟩ : syracuseStep 963967 = 1445951) B1445951
theorem B964123 : Blo 960589 964123 := bstep (se 1 (by rfl) ⟨723092, by rfl⟩ : syracuseStep 964123 = 1446185) B1446185
theorem B964303 : Blo 960589 964303 := bstep (se 1 (by rfl) ⟨723227, by rfl⟩ : syracuseStep 964303 = 1446455) B1446455
theorem B964543 : Blo 960589 964543 := bstep (se 1 (by rfl) ⟨723407, by rfl⟩ : syracuseStep 964543 = 1446815) B1446815
theorem B2930899 : Blo 960589 2930899 := bstep (se 1 (by rfl) ⟨2198174, by rfl⟩ : syracuseStep 2930899 = 4396349) B4396349
theorem B8239319 : Blo 960589 8239319 := bstep (se 1 (by rfl) ⟨6179489, by rfl⟩ : syracuseStep 8239319 = 12358979) B12358979
theorem B2308447 : Blo 960589 2308447 := bstep (se 1 (by rfl) ⟨1731335, by rfl⟩ : syracuseStep 2308447 = 3462671) B3462671
theorem B5487047 : Blo 960589 5487047 := bstep (se 1 (by rfl) ⟨4115285, by rfl⟩ : syracuseStep 5487047 = 8230571) B8230571
theorem B12663823 : Blo 960589 12663823 := bstep (se 1 (by rfl) ⟨9497867, by rfl⟩ : syracuseStep 12663823 = 18995735) B18995735
theorem B2440489 : Blo 960589 2440489 := bstep (se 2 (by rfl) ⟨915183, by rfl⟩ : syracuseStep 2440489 = 1830367) B1830367
theorem B2309447 : Blo 960589 2309447 := bstep (se 1 (by rfl) ⟨1732085, by rfl⟩ : syracuseStep 2309447 = 3464171) B3464171
theorem B2932139 : Blo 960589 2932139 := bstep (se 1 (by rfl) ⟨2199104, by rfl⟩ : syracuseStep 2932139 = 4398209) B4398209
theorem B1621471 : Blo 960589 1621471 := bstep (se 1 (by rfl) ⟨1216103, by rfl⟩ : syracuseStep 1621471 = 2432207) B2432207
theorem B12336731 : Blo 960589 12336731 := bstep (se 1 (by rfl) ⟨9252548, by rfl⟩ : syracuseStep 12336731 = 18505097) B18505097
theorem B2440955 : Blo 960589 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B6176567 : Blo 960589 6176567 := bstep (se 1 (by rfl) ⟨4632425, by rfl⟩ : syracuseStep 6176567 = 9264851) B9264851
theorem B5488505 : Blo 960589 5488505 := bstep (se 2 (by rfl) ⟨2058189, by rfl⟩ : syracuseStep 5488505 = 4116379) B4116379
theorem B1622153 : Blo 960589 1622153 := bstep (se 2 (by rfl) ⟨608307, by rfl⟩ : syracuseStep 1622153 = 1216615) B1216615
theorem B2605439 : Blo 960589 2605439 := bstep (se 1 (by rfl) ⟨1954079, by rfl⟩ : syracuseStep 2605439 = 3908159) B3908159
theorem B4112927 : Blo 960589 4112927 := bstep (se 1 (by rfl) ⟨3084695, by rfl⟩ : syracuseStep 4112927 = 6169391) B6169391
theorem B4867127 : Blo 960589 4867127 := bstep (se 1 (by rfl) ⟨3650345, by rfl⟩ : syracuseStep 4867127 = 7300691) B7300691
theorem B2737259 : Blo 960589 2737259 := bstep (se 1 (by rfl) ⟨2052944, by rfl⟩ : syracuseStep 2737259 = 4105889) B4105889
theorem B2311591 : Blo 960589 2311591 := bstep (se 1 (by rfl) ⟨1733693, by rfl⟩ : syracuseStep 2311591 = 3467387) B3467387
theorem B4867775 : Blo 960589 4867775 := bstep (se 1 (by rfl) ⟨3650831, by rfl⟩ : syracuseStep 4867775 = 7301663) B7301663
theorem B5490463 : Blo 960589 5490463 := bstep (se 1 (by rfl) ⟨4117847, by rfl⟩ : syracuseStep 5490463 = 8235695) B8235695
theorem B2345555 : Blo 960589 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B7523485 : Blo 960589 7523485 := bstep (se 3 (by rfl) ⟨1410653, by rfl⟩ : syracuseStep 7523485 = 2821307) B2821307
theorem B2739719 : Blo 960589 2739719 := bstep (se 1 (by rfl) ⟨2054789, by rfl⟩ : syracuseStep 2739719 = 4109579) B4109579
theorem B4870043 : Blo 960589 4870043 := bstep (se 1 (by rfl) ⟨3652532, by rfl⟩ : syracuseStep 4870043 = 7305065) B7305065
theorem B11128859 : Blo 960589 11128859 := bstep (se 1 (by rfl) ⟨8346644, by rfl⟩ : syracuseStep 11128859 = 16693289) B16693289
theorem B1626655 : Blo 960589 1626655 := bstep (se 1 (by rfl) ⟨1219991, by rfl⟩ : syracuseStep 1626655 = 2439983) B2439983
theorem B1627087 : Blo 960589 1627087 := bstep (se 1 (by rfl) ⟨1220315, by rfl⟩ : syracuseStep 1627087 = 2440631) B2440631
theorem B39998771 : Blo 960589 39998771 := bstep (se 1 (by rfl) ⟨29999078, by rfl⟩ : syracuseStep 39998771 = 59998157) B59998157
theorem B4871663 : Blo 960589 4871663 := bstep (se 1 (by rfl) ⟨3653747, by rfl⟩ : syracuseStep 4871663 = 7307495) B7307495
theorem B1300703 : Blo 960589 1300703 := bstep (se 1 (by rfl) ⟨975527, by rfl⟩ : syracuseStep 1300703 = 1951055) B1951055
theorem B16472483 : Blo 960589 16472483 := bstep (se 1 (by rfl) ⟨12354362, by rfl⟩ : syracuseStep 16472483 = 24708725) B24708725
theorem B39509317 : Blo 960589 39509317 := bstep (se 4 (by rfl) ⟨3703998, by rfl⟩ : syracuseStep 39509317 = 7407997) B7407997
theorem B2055593 : Blo 960589 2055593 := bstep (se 2 (by rfl) ⟨770847, by rfl⟩ : syracuseStep 2055593 = 1541695) B1541695
theorem B2744047 : Blo 960589 2744047 := bstep (se 1 (by rfl) ⟨2058035, by rfl⟩ : syracuseStep 2744047 = 4116071) B4116071
theorem B8773433 : Blo 960589 8773433 := bstep (se 2 (by rfl) ⟨3290037, by rfl⟩ : syracuseStep 8773433 = 6580075) B6580075
theorem B2744275 : Blo 960589 2744275 := bstep (se 1 (by rfl) ⟨2058206, by rfl⟩ : syracuseStep 2744275 = 4116413) B4116413
theorem B1368299 : Blo 960589 1368299 := bstep (se 1 (by rfl) ⟨1026224, by rfl⟩ : syracuseStep 1368299 = 2052449) B2052449
theorem B37478861 : Blo 960589 37478861 := bstep (se 3 (by rfl) ⟨7027286, by rfl⟩ : syracuseStep 37478861 = 14054573) B14054573
theorem B7300205 : Blo 960589 7300205 := bstep (se 3 (by rfl) ⟨1368788, by rfl⟩ : syracuseStep 7300205 = 2737577) B2737577
theorem B21390911 : Blo 960589 21390911 := bstep (se 1 (by rfl) ⟨16043183, by rfl⟩ : syracuseStep 21390911 = 32086367) B32086367
theorem B1828507 : Blo 960589 1828507 := bstep (se 1 (by rfl) ⟨1371380, by rfl⟩ : syracuseStep 1828507 = 2742761) B2742761
theorem B2057899 : Blo 960589 2057899 := bstep (se 1 (by rfl) ⟨1543424, by rfl⟩ : syracuseStep 2057899 = 3086849) B3086849
theorem B4876199 : Blo 960589 4876199 := bstep (se 1 (by rfl) ⟨3657149, by rfl⟩ : syracuseStep 4876199 = 7314299) B7314299
theorem B2058377 : Blo 960589 2058377 := bstep (se 2 (by rfl) ⟨771891, by rfl⟩ : syracuseStep 2058377 = 1543783) B1543783
theorem B4876523 : Blo 960589 4876523 := bstep (se 1 (by rfl) ⟨3657392, by rfl⟩ : syracuseStep 4876523 = 7314785) B7314785
theorem B10414615 : Blo 960589 10414615 := bstep (se 1 (by rfl) ⟨7810961, by rfl⟩ : syracuseStep 10414615 = 15621923) B15621923
theorem B1829479 : Blo 960589 1829479 := bstep (se 1 (by rfl) ⟨1372109, by rfl⟩ : syracuseStep 1829479 = 2744219) B2744219
theorem B2059129 : Blo 960589 2059129 := bstep (se 2 (by rfl) ⟨772173, by rfl⟩ : syracuseStep 2059129 = 1544347) B1544347
theorem B6155297 : Blo 960589 6155297 := bstep (se 2 (by rfl) ⟨2308236, by rfl⟩ : syracuseStep 6155297 = 4616473) B4616473
theorem B4877495 : Blo 960589 4877495 := bstep (se 1 (by rfl) ⟨3658121, by rfl⟩ : syracuseStep 4877495 = 7316243) B7316243
theorem B1830215 : Blo 960589 1830215 := bstep (se 1 (by rfl) ⟨1372661, by rfl⟩ : syracuseStep 1830215 = 2745323) B2745323
theorem B10972907 : Blo 960589 10972907 := bstep (se 1 (by rfl) ⟨8229680, by rfl⟩ : syracuseStep 10972907 = 16459361) B16459361
theorem B4878143 : Blo 960589 4878143 := bstep (se 1 (by rfl) ⟨3658607, by rfl⟩ : syracuseStep 4878143 = 7317215) B7317215
theorem B4943759 : Blo 960589 4943759 := bstep (se 1 (by rfl) ⟨3707819, by rfl⟩ : syracuseStep 4943759 = 7415639) B7415639
theorem B2191579 : Blo 960589 2191579 := bstep (se 1 (by rfl) ⟨1643684, by rfl⟩ : syracuseStep 2191579 = 3287369) B3287369
theorem B4387115 : Blo 960589 4387115 := bstep (se 1 (by rfl) ⟨3290336, by rfl⟩ : syracuseStep 4387115 = 6580673) B6580673
theorem B6943103 : Blo 960589 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B7304093 : Blo 960589 7304093 := bstep (se 3 (by rfl) ⟨1369517, by rfl⟩ : syracuseStep 7304093 = 2739035) B2739035
theorem B46789649 : Blo 960589 46789649 := bstep (se 2 (by rfl) ⟨17546118, by rfl⟩ : syracuseStep 46789649 = 35092237) B35092237
theorem B1373231 : Blo 960589 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B55506059 : Blo 960589 55506059 := bstep (se 1 (by rfl) ⟨41629544, by rfl⟩ : syracuseStep 55506059 = 83259089) B83259089
theorem B41612939 : Blo 960589 41612939 := bstep (se 1 (by rfl) ⟨31209704, by rfl⟩ : syracuseStep 41612939 = 62419409) B62419409
theorem B1734623 : Blo 960589 1734623 := bstep (se 1 (by rfl) ⟨1300967, by rfl⟩ : syracuseStep 1734623 = 2601935) B2601935
theorem B46758505 : Blo 960589 46758505 := bstep (se 2 (by rfl) ⟨17534439, by rfl⟩ : syracuseStep 46758505 = 35068879) B35068879
theorem B28572425 : Blo 960589 28572425 := bstep (se 2 (by rfl) ⟨10714659, by rfl⟩ : syracuseStep 28572425 = 21429319) B21429319
theorem B1538927 : Blo 960589 1538927 := bstep (se 1 (by rfl) ⟨1154195, by rfl⟩ : syracuseStep 1538927 = 2308391) B2308391
theorem B12319613 : Blo 960589 12319613 := bstep (se 3 (by rfl) ⟨2309927, by rfl⟩ : syracuseStep 12319613 = 4619855) B4619855
theorem B2161691 : Blo 960589 2161691 := bstep (se 1 (by rfl) ⟨1621268, by rfl⟩ : syracuseStep 2161691 = 3242537) B3242537
theorem B5471327 : Blo 960589 5471327 := bstep (se 1 (by rfl) ⟨4103495, by rfl⟩ : syracuseStep 5471327 = 8206991) B8206991
theorem B1440923 : Blo 960589 1440923 := bstep (se 1 (by rfl) ⟨1080692, by rfl⟩ : syracuseStep 1440923 = 2161385) B2161385
theorem B1441079 : Blo 960589 1441079 := bstep (se 1 (by rfl) ⟨1080809, by rfl⟩ : syracuseStep 1441079 = 2161619) B2161619
theorem B1441259 : Blo 960589 1441259 := bstep (se 1 (by rfl) ⟨1080944, by rfl⟩ : syracuseStep 1441259 = 2161889) B2161889
theorem B4882031 : Blo 960589 4882031 := bstep (se 1 (by rfl) ⟨3661523, by rfl⟩ : syracuseStep 4882031 = 7323047) B7323047
theorem B1441463 : Blo 960589 1441463 := bstep (se 1 (by rfl) ⟨1081097, by rfl⟩ : syracuseStep 1441463 = 2162195) B2162195
theorem B4456297 : Blo 960589 4456297 := bstep (se 2 (by rfl) ⟨1671111, by rfl⟩ : syracuseStep 4456297 = 3342223) B3342223
theorem B1441673 : Blo 960589 1441673 := bstep (se 2 (by rfl) ⟨540627, by rfl⟩ : syracuseStep 1441673 = 1081255) B1081255
theorem B10977281 : Blo 960589 10977281 := bstep (se 2 (by rfl) ⟨4116480, by rfl⟩ : syracuseStep 10977281 = 8232961) B8232961
theorem B1081435 : Blo 960589 1081435 := bstep (se 1 (by rfl) ⟨811076, by rfl⟩ : syracuseStep 1081435 = 1622153) B1622153
theorem B3080339 : Blo 960589 3080339 := bstep (se 1 (by rfl) ⟨2310254, by rfl⟩ : syracuseStep 3080339 = 4620509) B4620509
theorem B1441961 : Blo 960589 1441961 := bstep (se 2 (by rfl) ⟨540735, by rfl⟩ : syracuseStep 1441961 = 1081471) B1081471
theorem B1736959 : Blo 960589 1736959 := bstep (se 1 (by rfl) ⟨1302719, by rfl⟩ : syracuseStep 1736959 = 2605439) B2605439
theorem B1442171 : Blo 960589 1442171 := bstep (se 1 (by rfl) ⟨1081628, by rfl⟩ : syracuseStep 1442171 = 2163257) B2163257
theorem B1442345 : Blo 960589 1442345 := bstep (se 2 (by rfl) ⟨540879, by rfl⟩ : syracuseStep 1442345 = 1081759) B1081759
theorem B3244751 : Blo 960589 3244751 := bstep (se 1 (by rfl) ⟨2433563, by rfl⟩ : syracuseStep 3244751 = 4867127) B4867127
theorem B1442651 : Blo 960589 1442651 := bstep (se 1 (by rfl) ⟨1081988, by rfl⟩ : syracuseStep 1442651 = 2163977) B2163977
theorem B6161447 : Blo 960589 6161447 := bstep (se 1 (by rfl) ⟨4621085, by rfl⟩ : syracuseStep 6161447 = 9242171) B9242171
theorem B3245183 : Blo 960589 3245183 := bstep (se 1 (by rfl) ⟨2433887, by rfl⟩ : syracuseStep 3245183 = 4867775) B4867775
theorem B1442999 : Blo 960589 1442999 := bstep (se 1 (by rfl) ⟨1082249, by rfl⟩ : syracuseStep 1442999 = 2164499) B2164499
theorem B1443239 : Blo 960589 1443239 := bstep (se 1 (by rfl) ⟨1082429, by rfl⟩ : syracuseStep 1443239 = 2164859) B2164859
theorem B1443311 : Blo 960589 1443311 := bstep (se 1 (by rfl) ⟨1082483, by rfl⟩ : syracuseStep 1443311 = 2164967) B2164967
theorem B31196735 : Blo 960589 31196735 := bstep (se 1 (by rfl) ⟨23397551, by rfl⟩ : syracuseStep 31196735 = 46795103) B46795103
theorem B1443419 : Blo 960589 1443419 := bstep (se 1 (by rfl) ⟨1082564, by rfl⟩ : syracuseStep 1443419 = 2165129) B2165129
theorem B3081979 : Blo 960589 3081979 := bstep (se 1 (by rfl) ⟨2311484, by rfl⟩ : syracuseStep 3081979 = 4622969) B4622969
theorem B3082121 : Blo 960589 3082121 := bstep (se 2 (by rfl) ⟨1155795, by rfl⟩ : syracuseStep 3082121 = 2311591) B2311591
theorem B1444151 : Blo 960589 1444151 := bstep (se 1 (by rfl) ⟨1083113, by rfl⟩ : syracuseStep 1444151 = 2166227) B2166227
theorem B1444199 : Blo 960589 1444199 := bstep (se 1 (by rfl) ⟨1083149, by rfl⟩ : syracuseStep 1444199 = 2166299) B2166299
theorem B1444331 : Blo 960589 1444331 := bstep (se 1 (by rfl) ⟨1083248, by rfl⟩ : syracuseStep 1444331 = 2166497) B2166497
theorem B3246695 : Blo 960589 3246695 := bstep (se 1 (by rfl) ⟨2435021, by rfl⟩ : syracuseStep 3246695 = 4870043) B4870043
theorem B1444463 : Blo 960589 1444463 := bstep (se 1 (by rfl) ⟨1083347, by rfl⟩ : syracuseStep 1444463 = 2166695) B2166695
theorem B1444571 : Blo 960589 1444571 := bstep (se 1 (by rfl) ⟨1083428, by rfl⟩ : syracuseStep 1444571 = 2166857) B2166857
theorem B1444583 : Blo 960589 1444583 := bstep (se 1 (by rfl) ⟨1083437, by rfl⟩ : syracuseStep 1444583 = 2166875) B2166875
theorem B12323609 : Blo 960589 12323609 := bstep (se 2 (by rfl) ⟨4621353, by rfl⟩ : syracuseStep 12323609 = 9242707) B9242707
theorem B2165615 : Blo 960589 2165615 := bstep (se 1 (by rfl) ⟨1624211, by rfl⟩ : syracuseStep 2165615 = 3248423) B3248423
theorem B14650577 : Blo 960589 14650577 := bstep (se 2 (by rfl) ⟨5493966, by rfl⟩ : syracuseStep 14650577 = 10987933) B10987933
theorem B160501013 : Blo 960589 160501013 := bstep (se 6 (by rfl) ⟨3761742, by rfl⟩ : syracuseStep 160501013 = 7523485) B7523485
theorem B3247613 : Blo 960589 3247613 := bstep (se 3 (by rfl) ⟨608927, by rfl⟩ : syracuseStep 3247613 = 1217855) B1217855
theorem B1445417 : Blo 960589 1445417 := bstep (se 2 (by rfl) ⟨542031, by rfl⟩ : syracuseStep 1445417 = 1084063) B1084063
theorem B3247775 : Blo 960589 3247775 := bstep (se 1 (by rfl) ⟨2435831, by rfl⟩ : syracuseStep 3247775 = 4871663) B4871663
theorem B9244631 : Blo 960589 9244631 := bstep (se 1 (by rfl) ⟨6933473, by rfl⟩ : syracuseStep 9244631 = 13866947) B13866947
theorem B10981655 : Blo 960589 10981655 := bstep (se 1 (by rfl) ⟨8236241, by rfl⟩ : syracuseStep 10981655 = 16472483) B16472483
theorem B2167919 : Blo 960589 2167919 := bstep (se 1 (by rfl) ⟨1625939, by rfl⟩ : syracuseStep 2167919 = 3251879) B3251879
theorem B6952391 : Blo 960589 6952391 := bstep (se 1 (by rfl) ⟨5214293, by rfl⟩ : syracuseStep 6952391 = 10428587) B10428587
theorem B35067725 : Blo 960589 35067725 := bstep (se 3 (by rfl) ⟨6575198, by rfl⟩ : syracuseStep 35067725 = 13150397) B13150397
theorem B2168873 : Blo 960589 2168873 := bstep (se 2 (by rfl) ⟨813327, by rfl⟩ : syracuseStep 2168873 = 1626655) B1626655
theorem B3250529 : Blo 960589 3250529 := bstep (se 2 (by rfl) ⟨1218948, by rfl⟩ : syracuseStep 3250529 = 2437897) B2437897
theorem B14260607 : Blo 960589 14260607 := bstep (se 1 (by rfl) ⟨10695455, by rfl⟩ : syracuseStep 14260607 = 21390911) B21390911
theorem B2169449 : Blo 960589 2169449 := bstep (se 2 (by rfl) ⟨813543, by rfl⟩ : syracuseStep 2169449 = 1627087) B1627087
theorem B3250799 : Blo 960589 3250799 := bstep (se 1 (by rfl) ⟨2438099, by rfl⟩ : syracuseStep 3250799 = 4876199) B4876199
theorem B3251015 : Blo 960589 3251015 := bstep (se 1 (by rfl) ⟨2438261, by rfl⟩ : syracuseStep 3251015 = 4876523) B4876523
theorem B4103531 : Blo 960589 4103531 := bstep (se 1 (by rfl) ⟨3077648, by rfl⟩ : syracuseStep 4103531 = 6155297) B6155297
theorem B3251663 : Blo 960589 3251663 := bstep (se 1 (by rfl) ⟨2438747, by rfl⟩ : syracuseStep 3251663 = 4877495) B4877495
theorem B7315271 : Blo 960589 7315271 := bstep (se 1 (by rfl) ⟨5486453, by rfl⟩ : syracuseStep 7315271 = 10972907) B10972907
theorem B3252095 : Blo 960589 3252095 := bstep (se 1 (by rfl) ⟨2439071, by rfl⟩ : syracuseStep 3252095 = 4878143) B4878143
theorem B3088439 : Blo 960589 3088439 := bstep (se 1 (by rfl) ⟨2316329, by rfl⟩ : syracuseStep 3088439 = 4632659) B4632659
theorem B2433179 : Blo 960589 2433179 := bstep (se 1 (by rfl) ⟨1824884, by rfl⟩ : syracuseStep 2433179 = 3649769) B3649769
theorem B2924743 : Blo 960589 2924743 := bstep (se 1 (by rfl) ⟨2193557, by rfl⟩ : syracuseStep 2924743 = 4387115) B4387115
theorem B4628735 : Blo 960589 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B3907865 : Blo 960589 3907865 := bstep (se 2 (by rfl) ⟨1465449, by rfl⟩ : syracuseStep 3907865 = 2930899) B2930899
theorem B37004039 : Blo 960589 37004039 := bstep (se 1 (by rfl) ⟨27753029, by rfl⟩ : syracuseStep 37004039 = 55506059) B55506059
theorem B1156415 : Blo 960589 1156415 := bstep (se 1 (by rfl) ⟨867311, by rfl⟩ : syracuseStep 1156415 = 1734623) B1734623
theorem B16885097 : Blo 960589 16885097 := bstep (se 2 (by rfl) ⟨6331911, by rfl⟩ : syracuseStep 16885097 = 12663823) B12663823
theorem B3253985 : Blo 960589 3253985 := bstep (se 2 (by rfl) ⟨1220244, by rfl⟩ : syracuseStep 3253985 = 2440489) B2440489
theorem B19048283 : Blo 960589 19048283 := bstep (se 1 (by rfl) ⟨14286212, by rfl⟩ : syracuseStep 19048283 = 28572425) B28572425
theorem B1025951 : Blo 960589 1025951 := bstep (se 1 (by rfl) ⟨769463, by rfl⟩ : syracuseStep 1025951 = 1538927) B1538927
theorem B3647551 : Blo 960589 3647551 := bstep (se 1 (by rfl) ⟨2735663, by rfl⟩ : syracuseStep 3647551 = 5471327) B5471327
theorem B960615 : Blo 960589 960615 := bstep (se 1 (by rfl) ⟨720461, by rfl⟩ : syracuseStep 960615 = 1440923) B1440923
theorem B960719 : Blo 960589 960719 := bstep (se 1 (by rfl) ⟨720539, by rfl⟩ : syracuseStep 960719 = 1441079) B1441079
theorem B960839 : Blo 960589 960839 := bstep (se 1 (by rfl) ⟨720629, by rfl⟩ : syracuseStep 960839 = 1441259) B1441259
theorem B13183357 : Blo 960589 13183357 := bstep (se 3 (by rfl) ⟨2471879, by rfl⟩ : syracuseStep 13183357 = 4943759) B4943759
theorem B3254687 : Blo 960589 3254687 := bstep (se 1 (by rfl) ⟨2441015, by rfl⟩ : syracuseStep 3254687 = 4882031) B4882031
theorem B960975 : Blo 960589 960975 := bstep (se 1 (by rfl) ⟨720731, by rfl⟩ : syracuseStep 960975 = 1441463) B1441463
theorem B5941729 : Blo 960589 5941729 := bstep (se 2 (by rfl) ⟨2228148, by rfl⟩ : syracuseStep 5941729 = 4456297) B4456297
theorem B961115 : Blo 960589 961115 := bstep (se 1 (by rfl) ⟨720836, by rfl⟩ : syracuseStep 961115 = 1441673) B1441673
theorem B961279 : Blo 960589 961279 := bstep (se 1 (by rfl) ⟨720959, by rfl⟩ : syracuseStep 961279 = 1441919) B1441919
theorem B961471 : Blo 960589 961471 := bstep (se 1 (by rfl) ⟨721103, by rfl⟩ : syracuseStep 961471 = 1442207) B1442207
theorem B961647 : Blo 960589 961647 := bstep (se 1 (by rfl) ⟨721235, by rfl⟩ : syracuseStep 961647 = 1442471) B1442471
theorem B3255443 : Blo 960589 3255443 := bstep (se 1 (by rfl) ⟨2441582, by rfl⟩ : syracuseStep 3255443 = 4883165) B4883165
theorem B961727 : Blo 960589 961727 := bstep (se 1 (by rfl) ⟨721295, by rfl⟩ : syracuseStep 961727 = 1442591) B1442591
theorem B961743 : Blo 960589 961743 := bstep (se 1 (by rfl) ⟨721307, by rfl⟩ : syracuseStep 961743 = 1442615) B1442615
theorem B3648797 : Blo 960589 3648797 := bstep (se 3 (by rfl) ⟨684149, by rfl⟩ : syracuseStep 3648797 = 1368299) B1368299
theorem B961863 : Blo 960589 961863 := bstep (se 1 (by rfl) ⟨721397, by rfl⟩ : syracuseStep 961863 = 1442795) B1442795
theorem B962203 : Blo 960589 962203 := bstep (se 1 (by rfl) ⟨721652, by rfl⟩ : syracuseStep 962203 = 1443305) B1443305
theorem B962463 : Blo 960589 962463 := bstep (se 1 (by rfl) ⟨721847, by rfl⟩ : syracuseStep 962463 = 1443695) B1443695
theorem B962587 : Blo 960589 962587 := bstep (se 1 (by rfl) ⟨721940, by rfl⟩ : syracuseStep 962587 = 1443881) B1443881
theorem B962607 : Blo 960589 962607 := bstep (se 1 (by rfl) ⟨721955, by rfl⟩ : syracuseStep 962607 = 1443911) B1443911
theorem B962727 : Blo 960589 962727 := bstep (se 1 (by rfl) ⟨722045, by rfl⟩ : syracuseStep 962727 = 1444091) B1444091
theorem B3649799 : Blo 960589 3649799 := bstep (se 1 (by rfl) ⟨2737349, by rfl⟩ : syracuseStep 3649799 = 5474699) B5474699
theorem B962863 : Blo 960589 962863 := bstep (se 1 (by rfl) ⟨722147, by rfl⟩ : syracuseStep 962863 = 1444295) B1444295
theorem B963007 : Blo 960589 963007 := bstep (se 1 (by rfl) ⟨722255, by rfl⟩ : syracuseStep 963007 = 1444511) B1444511
theorem B963039 : Blo 960589 963039 := bstep (se 1 (by rfl) ⟨722279, by rfl⟩ : syracuseStep 963039 = 1444559) B1444559
theorem B963103 : Blo 960589 963103 := bstep (se 1 (by rfl) ⟨722327, by rfl⟩ : syracuseStep 963103 = 1444655) B1444655
theorem B963183 : Blo 960589 963183 := bstep (se 1 (by rfl) ⟨722387, by rfl⟩ : syracuseStep 963183 = 1444775) B1444775
theorem B963303 : Blo 960589 963303 := bstep (se 1 (by rfl) ⟨722477, by rfl⟩ : syracuseStep 963303 = 1444955) B1444955
theorem B963355 : Blo 960589 963355 := bstep (se 1 (by rfl) ⟨722516, by rfl⟩ : syracuseStep 963355 = 1445033) B1445033
theorem B2438009 : Blo 960589 2438009 := bstep (se 2 (by rfl) ⟨914253, by rfl⟩ : syracuseStep 2438009 = 1828507) B1828507
theorem B7320617 : Blo 960589 7320617 := bstep (se 2 (by rfl) ⟨2745231, by rfl⟩ : syracuseStep 7320617 = 5490463) B5490463
theorem B963631 : Blo 960589 963631 := bstep (se 1 (by rfl) ⟨722723, by rfl⟩ : syracuseStep 963631 = 1445447) B1445447
theorem B963751 : Blo 960589 963751 := bstep (se 1 (by rfl) ⟨722813, by rfl⟩ : syracuseStep 963751 = 1445627) B1445627
theorem B963911 : Blo 960589 963911 := bstep (se 1 (by rfl) ⟨722933, by rfl⟩ : syracuseStep 963911 = 1445867) B1445867
theorem B7419239 : Blo 960589 7419239 := bstep (se 1 (by rfl) ⟨5564429, by rfl⟩ : syracuseStep 7419239 = 11128859) B11128859
theorem B2439305 : Blo 960589 2439305 := bstep (se 2 (by rfl) ⟨914739, by rfl⟩ : syracuseStep 2439305 = 1829479) B1829479
theorem B27408577 : Blo 960589 27408577 := bstep (se 2 (by rfl) ⟨10278216, by rfl⟩ : syracuseStep 27408577 = 20556433) B20556433
theorem B24656237 : Blo 960589 24656237 := bstep (se 3 (by rfl) ⟨4623044, by rfl⟩ : syracuseStep 24656237 = 9246089) B9246089
theorem B67681025 : Blo 960589 67681025 := bstep (se 2 (by rfl) ⟨25380384, by rfl⟩ : syracuseStep 67681025 = 50760769) B50760769
theorem B1621019 : Blo 960589 1621019 := bstep (se 1 (by rfl) ⟨1215764, by rfl⟩ : syracuseStep 1621019 = 2431529) B2431529
theorem B1621289 : Blo 960589 1621289 := bstep (se 2 (by rfl) ⟨607983, by rfl⟩ : syracuseStep 1621289 = 1215967) B1215967
theorem B4112039 : Blo 960589 4112039 := bstep (se 1 (by rfl) ⟨3084029, by rfl⟩ : syracuseStep 4112039 = 6168059) B6168059
theorem B5848955 : Blo 960589 5848955 := bstep (se 1 (by rfl) ⟨4386716, by rfl⟩ : syracuseStep 5848955 = 8773433) B8773433
theorem B4112639 : Blo 960589 4112639 := bstep (se 1 (by rfl) ⟨3084479, by rfl⟩ : syracuseStep 4112639 = 6168959) B6168959
theorem B24985907 : Blo 960589 24985907 := bstep (se 1 (by rfl) ⟨18739430, by rfl⟩ : syracuseStep 24985907 = 37478861) B37478861
theorem B5489005 : Blo 960589 5489005 := bstep (se 3 (by rfl) ⟨1029188, by rfl⟩ : syracuseStep 5489005 = 2058377) B2058377
theorem B1851769 : Blo 960589 1851769 := bstep (se 2 (by rfl) ⟨694413, by rfl⟩ : syracuseStep 1851769 = 1388827) B1388827
theorem B4866641 : Blo 960589 4866641 := bstep (se 2 (by rfl) ⟨1824990, by rfl⟩ : syracuseStep 4866641 = 3649981) B3649981
theorem B1622747 : Blo 960589 1622747 := bstep (se 1 (by rfl) ⟨1217060, by rfl⟩ : syracuseStep 1622747 = 2434121) B2434121
theorem B4866803 : Blo 960589 4866803 := bstep (se 1 (by rfl) ⟨3650102, by rfl⟩ : syracuseStep 4866803 = 7300205) B7300205
theorem B27805517 : Blo 960589 27805517 := bstep (se 3 (by rfl) ⟨5213534, by rfl⟩ : syracuseStep 27805517 = 10427069) B10427069
theorem B28166291 : Blo 960589 28166291 := bstep (se 1 (by rfl) ⟨21124718, by rfl⟩ : syracuseStep 28166291 = 42249437) B42249437
theorem B1624475 : Blo 960589 1624475 := bstep (se 1 (by rfl) ⟨1218356, by rfl⟩ : syracuseStep 1624475 = 2436713) B2436713
theorem B4869395 : Blo 960589 4869395 := bstep (se 1 (by rfl) ⟨3652046, by rfl⟩ : syracuseStep 4869395 = 7304093) B7304093
theorem B62344673 : Blo 960589 62344673 := bstep (se 2 (by rfl) ⟨23379252, by rfl⟩ : syracuseStep 62344673 = 46758505) B46758505
theorem B27741959 : Blo 960589 27741959 := bstep (se 1 (by rfl) ⟨20806469, by rfl⟩ : syracuseStep 27741959 = 41612939) B41612939
theorem B5492879 : Blo 960589 5492879 := bstep (se 1 (by rfl) ⟨4119659, by rfl⟩ : syracuseStep 5492879 = 8239319) B8239319
theorem B3658031 : Blo 960589 3658031 := bstep (se 1 (by rfl) ⟨2743523, by rfl⟩ : syracuseStep 3658031 = 5487047) B5487047
theorem B52679089 : Blo 960589 52679089 := bstep (se 2 (by rfl) ⟨19754658, by rfl⟩ : syracuseStep 52679089 = 39509317) B39509317
theorem B8213075 : Blo 960589 8213075 := bstep (se 1 (by rfl) ⟨6159806, by rfl⟩ : syracuseStep 8213075 = 12319613) B12319613
theorem B1954759 : Blo 960589 1954759 := bstep (se 1 (by rfl) ⟨1466069, by rfl⟩ : syracuseStep 1954759 = 2932139) B2932139
theorem B3658729 : Blo 960589 3658729 := bstep (se 2 (by rfl) ⟨1372023, by rfl⟩ : syracuseStep 3658729 = 2744047) B2744047
theorem B1627303 : Blo 960589 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B4117711 : Blo 960589 4117711 := bstep (se 1 (by rfl) ⟨3088283, by rfl⟩ : syracuseStep 4117711 = 6176567) B6176567
theorem B3659003 : Blo 960589 3659003 := bstep (se 1 (by rfl) ⟨2744252, by rfl⟩ : syracuseStep 3659003 = 5488505) B5488505
theorem B3659033 : Blo 960589 3659033 := bstep (se 2 (by rfl) ⟨1372137, by rfl⟩ : syracuseStep 3659033 = 2744275) B2744275
theorem B2741951 : Blo 960589 2741951 := bstep (se 1 (by rfl) ⟨2056463, by rfl⟩ : syracuseStep 2741951 = 4112927) B4112927
theorem B2053927 : Blo 960589 2053927 := bstep (se 1 (by rfl) ⟨1540445, by rfl⟩ : syracuseStep 2053927 = 3080891) B3080891
theorem B1824839 : Blo 960589 1824839 := bstep (se 1 (by rfl) ⟨1368629, by rfl⟩ : syracuseStep 1824839 = 2737259) B2737259
theorem B7297289 : Blo 960589 7297289 := bstep (se 2 (by rfl) ⟨2736483, by rfl⟩ : syracuseStep 7297289 = 5472967) B5472967
theorem B11688421 : Blo 960589 11688421 := bstep (se 4 (by rfl) ⟨1095789, by rfl⟩ : syracuseStep 11688421 = 2191579) B2191579
theorem B2316905 : Blo 960589 2316905 := bstep (se 2 (by rfl) ⟨868839, by rfl⟩ : syracuseStep 2316905 = 1737679) B1737679
theorem B2743865 : Blo 960589 2743865 := bstep (se 2 (by rfl) ⟨1028949, by rfl⟩ : syracuseStep 2743865 = 2057899) B2057899
theorem B1826479 : Blo 960589 1826479 := bstep (se 1 (by rfl) ⟨1369859, by rfl⟩ : syracuseStep 1826479 = 2739719) B2739719
theorem B7298747 : Blo 960589 7298747 := bstep (se 1 (by rfl) ⟨5474060, by rfl⟩ : syracuseStep 7298747 = 10948121) B10948121
theorem B3661949 : Blo 960589 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B13886153 : Blo 960589 13886153 := bstep (se 2 (by rfl) ⟨5207307, by rfl⟩ : syracuseStep 13886153 = 10414615) B10414615
theorem B26665847 : Blo 960589 26665847 := bstep (se 1 (by rfl) ⟨19999385, by rfl⟩ : syracuseStep 26665847 = 39998771) B39998771
theorem B2745505 : Blo 960589 2745505 := bstep (se 2 (by rfl) ⟨1029564, by rfl⟩ : syracuseStep 2745505 = 2059129) B2059129
theorem B7038415 : Blo 960589 7038415 := bstep (se 1 (by rfl) ⟨5278811, by rfl⟩ : syracuseStep 7038415 = 10557623) B10557623
theorem B19753105 : Blo 960589 19753105 := bstep (se 2 (by rfl) ⟨7407414, by rfl⟩ : syracuseStep 19753105 = 14814829) B14814829
theorem B1370395 : Blo 960589 1370395 := bstep (se 1 (by rfl) ⟨1027796, by rfl⟩ : syracuseStep 1370395 = 2055593) B2055593
theorem B1731451 : Blo 960589 1731451 := bstep (se 1 (by rfl) ⟨1298588, by rfl⟩ : syracuseStep 1731451 = 2597177) B2597177
theorem B3468541 : Blo 960589 3468541 := bstep (se 3 (by rfl) ⟨650351, by rfl⟩ : syracuseStep 3468541 = 1300703) B1300703
theorem B6254813 : Blo 960589 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B3077929 : Blo 960589 3077929 := bstep (se 2 (by rfl) ⟨1154223, by rfl⟩ : syracuseStep 3077929 = 2308447) B2308447
theorem B3897179 : Blo 960589 3897179 := bstep (se 1 (by rfl) ⟨2922884, by rfl⟩ : syracuseStep 3897179 = 5845769) B5845769
theorem B3897227 : Blo 960589 3897227 := bstep (se 1 (by rfl) ⟨2922920, by rfl⟩ : syracuseStep 3897227 = 5845841) B5845841
theorem B31193099 : Blo 960589 31193099 := bstep (se 1 (by rfl) ⟨23394824, by rfl⟩ : syracuseStep 31193099 = 46789649) B46789649
theorem B3242105 : Blo 960589 3242105 := bstep (se 2 (by rfl) ⟨1215789, by rfl⟩ : syracuseStep 3242105 = 2431579) B2431579
theorem B3242159 : Blo 960589 3242159 := bstep (se 1 (by rfl) ⟨2431619, by rfl⟩ : syracuseStep 3242159 = 4863239) B4863239
theorem B4880573 : Blo 960589 4880573 := bstep (se 3 (by rfl) ⟨915107, by rfl⟩ : syracuseStep 4880573 = 1830215) B1830215
theorem B2161961 : Blo 960589 2161961 := bstep (se 2 (by rfl) ⟨810735, by rfl⟩ : syracuseStep 2161961 = 1621471) B1621471
theorem B1441127 : Blo 960589 1441127 := bstep (se 1 (by rfl) ⟨1080845, by rfl⟩ : syracuseStep 1441127 = 2161691) B2161691
theorem B1539631 : Blo 960589 1539631 := bstep (se 1 (by rfl) ⟨1154723, by rfl⟩ : syracuseStep 1539631 = 2309447) B2309447
theorem B8224487 : Blo 960589 8224487 := bstep (se 1 (by rfl) ⟨6168365, by rfl⟩ : syracuseStep 8224487 = 12336731) B12336731
theorem B1441913 : Blo 960589 1441913 := bstep (se 2 (by rfl) ⟨540717, by rfl⟩ : syracuseStep 1441913 = 1081435) B1081435
theorem B3899657 : Blo 960589 3899657 := bstep (se 2 (by rfl) ⟨1462371, by rfl⟩ : syracuseStep 3899657 = 2924743) B2924743
theorem B3244427 : Blo 960589 3244427 := bstep (se 1 (by rfl) ⟨2433320, by rfl⟩ : syracuseStep 3244427 = 4866641) B4866641
theorem B2163167 : Blo 960589 2163167 := bstep (se 1 (by rfl) ⟨1622375, by rfl⟩ : syracuseStep 2163167 = 3244751) B3244751
theorem B1081831 : Blo 960589 1081831 := bstep (se 1 (by rfl) ⟨811373, by rfl⟩ : syracuseStep 1081831 = 1622747) B1622747
theorem B3244535 : Blo 960589 3244535 := bstep (se 1 (by rfl) ⟨2433401, by rfl⟩ : syracuseStep 3244535 = 4866803) B4866803
theorem B10420973 : Blo 960589 10420973 := bstep (se 3 (by rfl) ⟨1953932, by rfl⟩ : syracuseStep 10420973 = 3907865) B3907865
theorem B2163455 : Blo 960589 2163455 := bstep (se 1 (by rfl) ⟨1622591, by rfl⟩ : syracuseStep 2163455 = 3245183) B3245183
theorem B18777527 : Blo 960589 18777527 := bstep (se 1 (by rfl) ⟨14083145, by rfl⟩ : syracuseStep 18777527 = 28166291) B28166291
theorem B1082983 : Blo 960589 1082983 := bstep (se 1 (by rfl) ⟨812237, by rfl⟩ : syracuseStep 1082983 = 1624475) B1624475
theorem B2164463 : Blo 960589 2164463 := bstep (se 1 (by rfl) ⟨1623347, by rfl⟩ : syracuseStep 2164463 = 3246695) B3246695
theorem B1443743 : Blo 960589 1443743 := bstep (se 1 (by rfl) ⟨1082807, by rfl⟩ : syracuseStep 1443743 = 2165615) B2165615
theorem B9767051 : Blo 960589 9767051 := bstep (se 1 (by rfl) ⟨7325288, by rfl⟩ : syracuseStep 9767051 = 14650577) B14650577
theorem B3246263 : Blo 960589 3246263 := bstep (se 1 (by rfl) ⟨2434697, by rfl⟩ : syracuseStep 3246263 = 4869395) B4869395
theorem B2165075 : Blo 960589 2165075 := bstep (se 1 (by rfl) ⟨1623806, by rfl⟩ : syracuseStep 2165075 = 3247613) B3247613
theorem B2165183 : Blo 960589 2165183 := bstep (se 1 (by rfl) ⟨1623887, by rfl⟩ : syracuseStep 2165183 = 3247775) B3247775
theorem B6163087 : Blo 960589 6163087 := bstep (se 1 (by rfl) ⟨4622315, by rfl⟩ : syracuseStep 6163087 = 9244631) B9244631
theorem B5475383 : Blo 960589 5475383 := bstep (se 1 (by rfl) ⟨4106537, by rfl⟩ : syracuseStep 5475383 = 8213075) B8213075
theorem B1445279 : Blo 960589 1445279 := bstep (se 1 (by rfl) ⟨1083959, by rfl⟩ : syracuseStep 1445279 = 2167919) B2167919
theorem B3083773 : Blo 960589 3083773 := bstep (se 3 (by rfl) ⟨578207, by rfl⟩ : syracuseStep 3083773 = 1156415) B1156415
theorem B1445915 : Blo 960589 1445915 := bstep (se 1 (by rfl) ⟨1084436, by rfl⟩ : syracuseStep 1445915 = 2168873) B2168873
theorem B1216559 : Blo 960589 1216559 := bstep (se 1 (by rfl) ⟨912419, by rfl⟩ : syracuseStep 1216559 = 1824839) B1824839
theorem B2167019 : Blo 960589 2167019 := bstep (se 1 (by rfl) ⟨1625264, by rfl⟩ : syracuseStep 2167019 = 3250529) B3250529
theorem B9507071 : Blo 960589 9507071 := bstep (se 1 (by rfl) ⟨7130303, by rfl⟩ : syracuseStep 9507071 = 14260607) B14260607
theorem B4624721 : Blo 960589 4624721 := bstep (se 2 (by rfl) ⟨1734270, by rfl⟩ : syracuseStep 4624721 = 3468541) B3468541
theorem B1446299 : Blo 960589 1446299 := bstep (se 1 (by rfl) ⟨1084724, by rfl⟩ : syracuseStep 1446299 = 2169449) B2169449
theorem B1544603 : Blo 960589 1544603 := bstep (se 1 (by rfl) ⟨1158452, by rfl⟩ : syracuseStep 1544603 = 2316905) B2316905
theorem B2167199 : Blo 960589 2167199 := bstep (se 1 (by rfl) ⟨1625399, by rfl⟩ : syracuseStep 2167199 = 3250799) B3250799
theorem B7311869 : Blo 960589 7311869 := bstep (se 3 (by rfl) ⟨1370975, by rfl⟩ : syracuseStep 7311869 = 2741951) B2741951
theorem B2167343 : Blo 960589 2167343 := bstep (se 1 (by rfl) ⟨1625507, by rfl⟩ : syracuseStep 2167343 = 3251015) B3251015
theorem B2167775 : Blo 960589 2167775 := bstep (se 1 (by rfl) ⟨1625831, by rfl⟩ : syracuseStep 2167775 = 3251663) B3251663
theorem B2168063 : Blo 960589 2168063 := bstep (se 1 (by rfl) ⟨1626047, by rfl⟩ : syracuseStep 2168063 = 3252095) B3252095
theorem B3085823 : Blo 960589 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B2169323 : Blo 960589 2169323 := bstep (se 1 (by rfl) ⟨1626992, by rfl⟩ : syracuseStep 2169323 = 3253985) B3253985
theorem B2169737 : Blo 960589 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B2169791 : Blo 960589 2169791 := bstep (se 1 (by rfl) ⟨1627343, by rfl⟩ : syracuseStep 2169791 = 3254687) B3254687
theorem B2170295 : Blo 960589 2170295 := bstep (se 1 (by rfl) ⟨1627721, by rfl⟩ : syracuseStep 2170295 = 3255443) B3255443
theorem B2432531 : Blo 960589 2432531 := bstep (se 1 (by rfl) ⟨1824398, by rfl⟩ : syracuseStep 2432531 = 3648797) B3648797
theorem B4169875 : Blo 960589 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B2433199 : Blo 960589 2433199 := bstep (se 1 (by rfl) ⟨1824899, by rfl⟩ : syracuseStep 2433199 = 3649799) B3649799
theorem B36544769 : Blo 960589 36544769 := bstep (se 2 (by rfl) ⟨13704288, by rfl⟩ : syracuseStep 36544769 = 27408577) B27408577
theorem B2598119 : Blo 960589 2598119 := bstep (se 1 (by rfl) ⟨1948589, by rfl⟩ : syracuseStep 2598119 = 3897179) B3897179
theorem B2598151 : Blo 960589 2598151 := bstep (se 1 (by rfl) ⟨1948613, by rfl⟩ : syracuseStep 2598151 = 3897227) B3897227
theorem B3253715 : Blo 960589 3253715 := bstep (se 1 (by rfl) ⟨2440286, by rfl⟩ : syracuseStep 3253715 = 4880573) B4880573
theorem B2435305 : Blo 960589 2435305 := bstep (se 2 (by rfl) ⟨913239, by rfl⟩ : syracuseStep 2435305 = 1826479) B1826479
theorem B960751 : Blo 960589 960751 := bstep (se 1 (by rfl) ⟨720563, by rfl⟩ : syracuseStep 960751 = 1441127) B1441127
theorem B5482991 : Blo 960589 5482991 := bstep (se 1 (by rfl) ⟨4112243, by rfl⟩ : syracuseStep 5482991 = 8224487) B8224487
theorem B7318187 : Blo 960589 7318187 := bstep (se 1 (by rfl) ⟨5488640, by rfl⟩ : syracuseStep 7318187 = 10977281) B10977281
theorem B961307 : Blo 960589 961307 := bstep (se 1 (by rfl) ⟨720980, by rfl⟩ : syracuseStep 961307 = 1441961) B1441961
theorem B16657271 : Blo 960589 16657271 := bstep (se 1 (by rfl) ⟨12492953, by rfl⟩ : syracuseStep 16657271 = 24985907) B24985907
theorem B961447 : Blo 960589 961447 := bstep (se 1 (by rfl) ⟨721085, by rfl⟩ : syracuseStep 961447 = 1442171) B1442171
theorem B961563 : Blo 960589 961563 := bstep (se 1 (by rfl) ⟨721172, by rfl⟩ : syracuseStep 961563 = 1442345) B1442345
theorem B7318673 : Blo 960589 7318673 := bstep (se 2 (by rfl) ⟨2744502, by rfl⟩ : syracuseStep 7318673 = 5489005) B5489005
theorem B2469025 : Blo 960589 2469025 := bstep (se 2 (by rfl) ⟨925884, by rfl⟩ : syracuseStep 2469025 = 1851769) B1851769
theorem B961767 : Blo 960589 961767 := bstep (se 1 (by rfl) ⟨721325, by rfl⟩ : syracuseStep 961767 = 1442651) B1442651
theorem B4107631 : Blo 960589 4107631 := bstep (se 1 (by rfl) ⟨3080723, by rfl⟩ : syracuseStep 4107631 = 6161447) B6161447
theorem B961999 : Blo 960589 961999 := bstep (se 1 (by rfl) ⟨721499, by rfl⟩ : syracuseStep 961999 = 1442999) B1442999
theorem B962159 : Blo 960589 962159 := bstep (se 1 (by rfl) ⟨721619, by rfl⟩ : syracuseStep 962159 = 1443239) B1443239
theorem B962207 : Blo 960589 962207 := bstep (se 1 (by rfl) ⟨721655, by rfl⟩ : syracuseStep 962207 = 1443311) B1443311
theorem B962279 : Blo 960589 962279 := bstep (se 1 (by rfl) ⟨721709, by rfl⟩ : syracuseStep 962279 = 1443419) B1443419
theorem B962767 : Blo 960589 962767 := bstep (se 1 (by rfl) ⟨722075, by rfl⟩ : syracuseStep 962767 = 1444151) B1444151
theorem B962799 : Blo 960589 962799 := bstep (se 1 (by rfl) ⟨722099, by rfl⟩ : syracuseStep 962799 = 1444199) B1444199
theorem B962887 : Blo 960589 962887 := bstep (se 1 (by rfl) ⟨722165, by rfl⟩ : syracuseStep 962887 = 1444331) B1444331
theorem B962975 : Blo 960589 962975 := bstep (se 1 (by rfl) ⟨722231, by rfl⟩ : syracuseStep 962975 = 1444463) B1444463
theorem B963047 : Blo 960589 963047 := bstep (se 1 (by rfl) ⟨722285, by rfl⟩ : syracuseStep 963047 = 1444571) B1444571
theorem B963055 : Blo 960589 963055 := bstep (se 1 (by rfl) ⟨722291, by rfl⟩ : syracuseStep 963055 = 1444583) B1444583
theorem B9384553 : Blo 960589 9384553 := bstep (se 2 (by rfl) ⟨3519207, by rfl⟩ : syracuseStep 9384553 = 7038415) B7038415
theorem B107000675 : Blo 960589 107000675 := bstep (se 1 (by rfl) ⟨80250506, by rfl⟩ : syracuseStep 107000675 = 160501013) B160501013
theorem B41563115 : Blo 960589 41563115 := bstep (se 1 (by rfl) ⟨31172336, by rfl⟩ : syracuseStep 41563115 = 62344673) B62344673
theorem B4109305 : Blo 960589 4109305 := bstep (se 2 (by rfl) ⟨1540989, by rfl⟩ : syracuseStep 4109305 = 3081979) B3081979
theorem B963611 : Blo 960589 963611 := bstep (se 1 (by rfl) ⟨722708, by rfl⟩ : syracuseStep 963611 = 1445417) B1445417
theorem B18494639 : Blo 960589 18494639 := bstep (se 1 (by rfl) ⟨13870979, by rfl⟩ : syracuseStep 18494639 = 27741959) B27741959
theorem B4863401 : Blo 960589 4863401 := bstep (se 2 (by rfl) ⟨1823775, by rfl⟩ : syracuseStep 4863401 = 3647551) B3647551
theorem B7321103 : Blo 960589 7321103 := bstep (se 1 (by rfl) ⟨5490827, by rfl⟩ : syracuseStep 7321103 = 10981655) B10981655
theorem B2438687 : Blo 960589 2438687 := bstep (se 1 (by rfl) ⟨1829015, by rfl⟩ : syracuseStep 2438687 = 3658031) B3658031
theorem B17577809 : Blo 960589 17577809 := bstep (se 2 (by rfl) ⟨6591678, by rfl⟩ : syracuseStep 17577809 = 13183357) B13183357
theorem B2439335 : Blo 960589 2439335 := bstep (se 1 (by rfl) ⟨1829501, by rfl⟩ : syracuseStep 2439335 = 3659003) B3659003
theorem B2439355 : Blo 960589 2439355 := bstep (se 1 (by rfl) ⟨1829516, by rfl⟩ : syracuseStep 2439355 = 3659033) B3659033
theorem B4634927 : Blo 960589 4634927 := bstep (se 1 (by rfl) ⟨3476195, by rfl⟩ : syracuseStep 4634927 = 6952391) B6952391
theorem B2308601 : Blo 960589 2308601 := bstep (se 2 (by rfl) ⟨865725, by rfl⟩ : syracuseStep 2308601 = 1731451) B1731451
theorem B23378483 : Blo 960589 23378483 := bstep (se 1 (by rfl) ⟨17533862, by rfl⟩ : syracuseStep 23378483 = 35067725) B35067725
theorem B4864859 : Blo 960589 4864859 := bstep (se 1 (by rfl) ⟨3648644, by rfl⟩ : syracuseStep 4864859 = 7297289) B7297289
theorem B2735687 : Blo 960589 2735687 := bstep (se 1 (by rfl) ⟨2051765, by rfl⟩ : syracuseStep 2735687 = 4103531) B4103531
theorem B2735869 : Blo 960589 2735869 := bstep (se 3 (by rfl) ⟨512975, by rfl⟩ : syracuseStep 2735869 = 1025951) B1025951
theorem B4865831 : Blo 960589 4865831 := bstep (se 1 (by rfl) ⟨3649373, by rfl⟩ : syracuseStep 4865831 = 7298747) B7298747
theorem B2441299 : Blo 960589 2441299 := bstep (se 1 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 2441299 = 3661949) B3661949
theorem B1622119 : Blo 960589 1622119 := bstep (se 1 (by rfl) ⟨1216589, by rfl⟩ : syracuseStep 1622119 = 2433179) B2433179
theorem B9257435 : Blo 960589 9257435 := bstep (se 1 (by rfl) ⟨6943076, by rfl⟩ : syracuseStep 9257435 = 13886153) B13886153
theorem B70238785 : Blo 960589 70238785 := bstep (se 2 (by rfl) ⟨26339544, by rfl⟩ : syracuseStep 70238785 = 52679089) B52679089
theorem B17777231 : Blo 960589 17777231 := bstep (se 1 (by rfl) ⟨13332923, by rfl⟩ : syracuseStep 17777231 = 26665847) B26665847
theorem B11256731 : Blo 960589 11256731 := bstep (se 1 (by rfl) ⟨8442548, by rfl⟩ : syracuseStep 11256731 = 16885097) B16885097
theorem B12698855 : Blo 960589 12698855 := bstep (se 1 (by rfl) ⟨9524141, by rfl⟩ : syracuseStep 12698855 = 19048283) B19048283
theorem B2606345 : Blo 960589 2606345 := bstep (se 2 (by rfl) ⟨977379, by rfl⟩ : syracuseStep 2606345 = 1954759) B1954759
theorem B5490281 : Blo 960589 5490281 := bstep (se 2 (by rfl) ⟨2058855, by rfl⟩ : syracuseStep 5490281 = 4117711) B4117711
theorem B2738569 : Blo 960589 2738569 := bstep (se 2 (by rfl) ⟨1026963, by rfl⟩ : syracuseStep 2738569 = 2053927) B2053927
theorem B8211365 : Blo 960589 8211365 := bstep (se 4 (by rfl) ⟨769815, by rfl⟩ : syracuseStep 8211365 = 1539631) B1539631
theorem B1625339 : Blo 960589 1625339 := bstep (se 1 (by rfl) ⟨1219004, by rfl⟩ : syracuseStep 1625339 = 2438009) B2438009
theorem B15584561 : Blo 960589 15584561 := bstep (se 2 (by rfl) ⟨5844210, by rfl⟩ : syracuseStep 15584561 = 11688421) B11688421
theorem B20795399 : Blo 960589 20795399 := bstep (se 1 (by rfl) ⟨15596549, by rfl⟩ : syracuseStep 20795399 = 31193099) B31193099
theorem B1626203 : Blo 960589 1626203 := bstep (se 1 (by rfl) ⟨1219652, by rfl⟩ : syracuseStep 1626203 = 2439305) B2439305
theorem B16437491 : Blo 960589 16437491 := bstep (se 1 (by rfl) ⟨12328118, by rfl⟩ : syracuseStep 16437491 = 24656237) B24656237
theorem B2741359 : Blo 960589 2741359 := bstep (se 1 (by rfl) ⟨2056019, by rfl⟩ : syracuseStep 2741359 = 4112039) B4112039
theorem B2053559 : Blo 960589 2053559 := bstep (se 1 (by rfl) ⟨1540169, by rfl⟩ : syracuseStep 2053559 = 3080339) B3080339
theorem B2741759 : Blo 960589 2741759 := bstep (se 1 (by rfl) ⟨2056319, by rfl⟩ : syracuseStep 2741759 = 4112639) B4112639
theorem B2315945 : Blo 960589 2315945 := bstep (se 2 (by rfl) ⟨868479, by rfl⟩ : syracuseStep 2315945 = 1736959) B1736959
theorem B20797823 : Blo 960589 20797823 := bstep (se 1 (by rfl) ⟨15598367, by rfl⟩ : syracuseStep 20797823 = 31196735) B31196735
theorem B18537011 : Blo 960589 18537011 := bstep (se 1 (by rfl) ⟨13902758, by rfl⟩ : syracuseStep 18537011 = 27805517) B27805517
theorem B2054747 : Blo 960589 2054747 := bstep (se 1 (by rfl) ⟨1541060, by rfl⟩ : syracuseStep 2054747 = 3082121) B3082121
theorem B3660673 : Blo 960589 3660673 := bstep (se 2 (by rfl) ⟨1372752, by rfl⟩ : syracuseStep 3660673 = 2745505) B2745505
theorem B8215739 : Blo 960589 8215739 := bstep (se 1 (by rfl) ⟨6161804, by rfl⟩ : syracuseStep 8215739 = 12323609) B12323609
theorem B3661919 : Blo 960589 3661919 := bstep (se 1 (by rfl) ⟨2746439, by rfl⟩ : syracuseStep 3661919 = 5492879) B5492879
theorem B26337473 : Blo 960589 26337473 := bstep (se 2 (by rfl) ⟨9876552, by rfl⟩ : syracuseStep 26337473 = 19753105) B19753105
theorem B1827193 : Blo 960589 1827193 := bstep (se 2 (by rfl) ⟨685197, by rfl⟩ : syracuseStep 1827193 = 1370395) B1370395
theorem B7922305 : Blo 960589 7922305 := bstep (se 2 (by rfl) ⟨2970864, by rfl⟩ : syracuseStep 7922305 = 5941729) B5941729
theorem B1829243 : Blo 960589 1829243 := bstep (se 1 (by rfl) ⟨1371932, by rfl⟩ : syracuseStep 1829243 = 2743865) B2743865
theorem B4876847 : Blo 960589 4876847 := bstep (se 1 (by rfl) ⟨3657635, by rfl⟩ : syracuseStep 4876847 = 7315271) B7315271
theorem B2058959 : Blo 960589 2058959 := bstep (se 1 (by rfl) ⟨1544219, by rfl⟩ : syracuseStep 2058959 = 3088439) B3088439
theorem B24669359 : Blo 960589 24669359 := bstep (se 1 (by rfl) ⟨18502019, by rfl⟩ : syracuseStep 24669359 = 37004039) B37004039
theorem B4878305 : Blo 960589 4878305 := bstep (se 2 (by rfl) ⟨1829364, by rfl⟩ : syracuseStep 4878305 = 3658729) B3658729
theorem B4880411 : Blo 960589 4880411 := bstep (se 1 (by rfl) ⟨3660308, by rfl⟩ : syracuseStep 4880411 = 7320617) B7320617
theorem B4946159 : Blo 960589 4946159 := bstep (se 1 (by rfl) ⟨3709619, by rfl⟩ : syracuseStep 4946159 = 7419239) B7419239
theorem B2161403 : Blo 960589 2161403 := bstep (se 1 (by rfl) ⟨1621052, by rfl⟩ : syracuseStep 2161403 = 3242105) B3242105
theorem B2161439 : Blo 960589 2161439 := bstep (se 1 (by rfl) ⟨1621079, by rfl⟩ : syracuseStep 2161439 = 3242159) B3242159
theorem B16415621 : Blo 960589 16415621 := bstep (se 4 (by rfl) ⟨1538964, by rfl⟩ : syracuseStep 16415621 = 3077929) B3077929
theorem B45120683 : Blo 960589 45120683 := bstep (se 1 (by rfl) ⟨33840512, by rfl⟩ : syracuseStep 45120683 = 67681025) B67681025
theorem B1080679 : Blo 960589 1080679 := bstep (se 1 (by rfl) ⟨810509, by rfl⟩ : syracuseStep 1080679 = 1621019) B1621019
theorem B1080859 : Blo 960589 1080859 := bstep (se 1 (by rfl) ⟨810644, by rfl⟩ : syracuseStep 1080859 = 1621289) B1621289
theorem B1441307 : Blo 960589 1441307 := bstep (se 1 (by rfl) ⟨1080980, by rfl⟩ : syracuseStep 1441307 = 2161961) B2161961
theorem B3899303 : Blo 960589 3899303 := bstep (se 1 (by rfl) ⟨2924477, by rfl⟩ : syracuseStep 3899303 = 5848955) B5848955
theorem B3244157 : Blo 960589 3244157 := bstep (se 3 (by rfl) ⟨608279, by rfl⟩ : syracuseStep 3244157 = 1216559) B1216559
theorem B2162825 : Blo 960589 2162825 := bstep (se 2 (by rfl) ⟨811059, by rfl⟩ : syracuseStep 2162825 = 1622119) B1622119
theorem B3244265 : Blo 960589 3244265 := bstep (se 2 (by rfl) ⟨1216599, by rfl⟩ : syracuseStep 3244265 = 2433199) B2433199
theorem B2162951 : Blo 960589 2162951 := bstep (se 1 (by rfl) ⟨1622213, by rfl⟩ : syracuseStep 2162951 = 3244427) B3244427
theorem B1442111 : Blo 960589 1442111 := bstep (se 1 (by rfl) ⟨1081583, by rfl⟩ : syracuseStep 1442111 = 2163167) B2163167
theorem B2163023 : Blo 960589 2163023 := bstep (se 1 (by rfl) ⟨1622267, by rfl⟩ : syracuseStep 2163023 = 3244535) B3244535
theorem B6947315 : Blo 960589 6947315 := bstep (se 1 (by rfl) ⟨5210486, by rfl⟩ : syracuseStep 6947315 = 10420973) B10420973
theorem B1442303 : Blo 960589 1442303 := bstep (se 1 (by rfl) ⟨1081727, by rfl⟩ : syracuseStep 1442303 = 2163455) B2163455
theorem B7504487 : Blo 960589 7504487 := bstep (se 1 (by rfl) ⟨5628365, by rfl⟩ : syracuseStep 7504487 = 11256731) B11256731
theorem B1442441 : Blo 960589 1442441 := bstep (se 2 (by rfl) ⟨540915, by rfl⟩ : syracuseStep 1442441 = 1081831) B1081831
theorem B93651713 : Blo 960589 93651713 := bstep (se 2 (by rfl) ⟨35119392, by rfl⟩ : syracuseStep 93651713 = 70238785) B70238785
theorem B1737563 : Blo 960589 1737563 := bstep (se 1 (by rfl) ⟨1303172, by rfl⟩ : syracuseStep 1737563 = 2606345) B2606345
theorem B12518351 : Blo 960589 12518351 := bstep (se 1 (by rfl) ⟨9388763, by rfl⟩ : syracuseStep 12518351 = 18777527) B18777527
theorem B1442975 : Blo 960589 1442975 := bstep (se 1 (by rfl) ⟨1082231, by rfl⟩ : syracuseStep 1442975 = 2164463) B2164463
theorem B2164175 : Blo 960589 2164175 := bstep (se 1 (by rfl) ⟨1623131, by rfl⟩ : syracuseStep 2164175 = 3246263) B3246263
theorem B1443383 : Blo 960589 1443383 := bstep (se 1 (by rfl) ⟨1082537, by rfl⟩ : syracuseStep 1443383 = 2165075) B2165075
theorem B1443455 : Blo 960589 1443455 := bstep (se 1 (by rfl) ⟨1082591, by rfl⟩ : syracuseStep 1443455 = 2165183) B2165183
theorem B5474243 : Blo 960589 5474243 := bstep (se 1 (by rfl) ⟨4105682, by rfl⟩ : syracuseStep 5474243 = 8211365) B8211365
theorem B1443977 : Blo 960589 1443977 := bstep (se 2 (by rfl) ⟨541491, by rfl⟩ : syracuseStep 1443977 = 1082983) B1082983
theorem B1083559 : Blo 960589 1083559 := bstep (se 1 (by rfl) ⟨812669, by rfl⟩ : syracuseStep 1083559 = 1625339) B1625339
theorem B10389707 : Blo 960589 10389707 := bstep (se 1 (by rfl) ⟨7792280, by rfl⟩ : syracuseStep 10389707 = 15584561) B15584561
theorem B13863599 : Blo 960589 13863599 := bstep (se 1 (by rfl) ⟨10397699, by rfl⟩ : syracuseStep 13863599 = 20795399) B20795399
theorem B1084135 : Blo 960589 1084135 := bstep (se 1 (by rfl) ⟨813101, by rfl⟩ : syracuseStep 1084135 = 1626203) B1626203
theorem B1444679 : Blo 960589 1444679 := bstep (se 1 (by rfl) ⟨1083509, by rfl⟩ : syracuseStep 1444679 = 2167019) B2167019
theorem B3083147 : Blo 960589 3083147 := bstep (se 1 (by rfl) ⟨2312360, by rfl⟩ : syracuseStep 3083147 = 4624721) B4624721
theorem B1444799 : Blo 960589 1444799 := bstep (se 1 (by rfl) ⟨1083599, by rfl⟩ : syracuseStep 1444799 = 2167199) B2167199
theorem B3247073 : Blo 960589 3247073 := bstep (se 2 (by rfl) ⟨1217652, by rfl⟩ : syracuseStep 3247073 = 2435305) B2435305
theorem B1444895 : Blo 960589 1444895 := bstep (se 1 (by rfl) ⟨1083671, by rfl⟩ : syracuseStep 1444895 = 2167343) B2167343
theorem B1445183 : Blo 960589 1445183 := bstep (se 1 (by rfl) ⟨1083887, by rfl⟩ : syracuseStep 1445183 = 2167775) B2167775
theorem B1445375 : Blo 960589 1445375 := bstep (se 1 (by rfl) ⟨1084031, by rfl⟩ : syracuseStep 1445375 = 2168063) B2168063
theorem B1543963 : Blo 960589 1543963 := bstep (se 1 (by rfl) ⟨1157972, by rfl⟩ : syracuseStep 1543963 = 2315945) B2315945
theorem B5476157 : Blo 960589 5476157 := bstep (se 3 (by rfl) ⟨1026779, by rfl⟩ : syracuseStep 5476157 = 2053559) B2053559
theorem B8228861 : Blo 960589 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B13865215 : Blo 960589 13865215 := bstep (se 1 (by rfl) ⟨10398911, by rfl⟩ : syracuseStep 13865215 = 20797823) B20797823
theorem B1446215 : Blo 960589 1446215 := bstep (se 1 (by rfl) ⟨1084661, by rfl⟩ : syracuseStep 1446215 = 2169323) B2169323
theorem B12358007 : Blo 960589 12358007 := bstep (se 1 (by rfl) ⟨9268505, by rfl⟩ : syracuseStep 12358007 = 18537011) B18537011
theorem B5476841 : Blo 960589 5476841 := bstep (se 2 (by rfl) ⟨2053815, by rfl⟩ : syracuseStep 5476841 = 4107631) B4107631
theorem B1446491 : Blo 960589 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B1446527 : Blo 960589 1446527 := bstep (se 1 (by rfl) ⟨1084895, by rfl⟩ : syracuseStep 1446527 = 2169791) B2169791
theorem B5477159 : Blo 960589 5477159 := bstep (se 1 (by rfl) ⟨4107869, by rfl⟩ : syracuseStep 5477159 = 8215739) B8215739
theorem B1446863 : Blo 960589 1446863 := bstep (se 1 (by rfl) ⟨1085147, by rfl⟩ : syracuseStep 1446863 = 2170295) B2170295
theorem B2169143 : Blo 960589 2169143 := bstep (se 1 (by rfl) ⟨1626857, by rfl⟩ : syracuseStep 2169143 = 3253715) B3253715
theorem B5479073 : Blo 960589 5479073 := bstep (se 2 (by rfl) ⟨2054652, by rfl⟩ : syracuseStep 5479073 = 4109305) B4109305
theorem B5479325 : Blo 960589 5479325 := bstep (se 3 (by rfl) ⟨1027373, by rfl⟩ : syracuseStep 5479325 = 2054747) B2054747
theorem B3251231 : Blo 960589 3251231 := bstep (se 1 (by rfl) ⟨2438423, by rfl⟩ : syracuseStep 3251231 = 4876847) B4876847
theorem B3252203 : Blo 960589 3252203 := bstep (se 1 (by rfl) ⟨2439152, by rfl⟩ : syracuseStep 3252203 = 4878305) B4878305
theorem B3252473 : Blo 960589 3252473 := bstep (se 2 (by rfl) ⟨1219677, by rfl⟩ : syracuseStep 3252473 = 2439355) B2439355
theorem B12329759 : Blo 960589 12329759 := bstep (se 1 (by rfl) ⟨9247319, by rfl⟩ : syracuseStep 12329759 = 18494639) B18494639
theorem B3253607 : Blo 960589 3253607 := bstep (se 1 (by rfl) ⟨2440205, by rfl⟩ : syracuseStep 3253607 = 4880411) B4880411
theorem B3089951 : Blo 960589 3089951 := bstep (se 1 (by rfl) ⟨2317463, by rfl⟩ : syracuseStep 3089951 = 4634927) B4634927
theorem B3647825 : Blo 960589 3647825 := bstep (se 2 (by rfl) ⟨1367934, by rfl⟩ : syracuseStep 3647825 = 2735869) B2735869
theorem B960871 : Blo 960589 960871 := bstep (se 1 (by rfl) ⟨720653, by rfl⟩ : syracuseStep 960871 = 1441307) B1441307
theorem B2599535 : Blo 960589 2599535 := bstep (se 1 (by rfl) ⟨1949651, by rfl⟩ : syracuseStep 2599535 = 3899303) B3899303
theorem B961275 : Blo 960589 961275 := bstep (se 1 (by rfl) ⟨720956, by rfl⟩ : syracuseStep 961275 = 1441913) B1441913
theorem B3255065 : Blo 960589 3255065 := bstep (se 2 (by rfl) ⟨1220649, by rfl⟩ : syracuseStep 3255065 = 2441299) B2441299
theorem B2599771 : Blo 960589 2599771 := bstep (se 1 (by rfl) ⟨1949828, by rfl⟩ : syracuseStep 2599771 = 3899657) B3899657
theorem B6171623 : Blo 960589 6171623 := bstep (se 1 (by rfl) ⟨4628717, by rfl⟩ : syracuseStep 6171623 = 9257435) B9257435
theorem B2436257 : Blo 960589 2436257 := bstep (se 2 (by rfl) ⟨913596, by rfl⟩ : syracuseStep 2436257 = 1827193) B1827193
theorem B8465903 : Blo 960589 8465903 := bstep (se 1 (by rfl) ⟨6349427, by rfl⟩ : syracuseStep 8465903 = 12698855) B12698855
theorem B962495 : Blo 960589 962495 := bstep (se 1 (by rfl) ⟨721871, by rfl⟩ : syracuseStep 962495 = 1443743) B1443743
theorem B3650255 : Blo 960589 3650255 := bstep (se 1 (by rfl) ⟨2737691, by rfl⟩ : syracuseStep 3650255 = 5475383) B5475383
theorem B963519 : Blo 960589 963519 := bstep (se 1 (by rfl) ⟨722639, by rfl⟩ : syracuseStep 963519 = 1445279) B1445279
theorem B963943 : Blo 960589 963943 := bstep (se 1 (by rfl) ⟨722957, by rfl⟩ : syracuseStep 963943 = 1445915) B1445915
theorem B10958327 : Blo 960589 10958327 := bstep (se 1 (by rfl) ⟨8218745, by rfl⟩ : syracuseStep 10958327 = 16437491) B16437491
theorem B6338047 : Blo 960589 6338047 := bstep (se 1 (by rfl) ⟨4753535, by rfl⟩ : syracuseStep 6338047 = 9507071) B9507071
theorem B964199 : Blo 960589 964199 := bstep (se 1 (by rfl) ⟨723149, by rfl⟩ : syracuseStep 964199 = 1446299) B1446299
theorem B3651425 : Blo 960589 3651425 := bstep (se 2 (by rfl) ⟨1369284, by rfl⟩ : syracuseStep 3651425 = 2738569) B2738569
theorem B42252293 : Blo 960589 42252293 := bstep (se 4 (by rfl) ⟨3961152, by rfl⟩ : syracuseStep 42252293 = 7922305) B7922305
theorem B4111697 : Blo 960589 4111697 := bstep (se 2 (by rfl) ⟨1541886, by rfl⟩ : syracuseStep 4111697 = 3083773) B3083773
theorem B1621687 : Blo 960589 1621687 := bstep (se 1 (by rfl) ⟨1216265, by rfl⟩ : syracuseStep 1621687 = 2432531) B2432531
theorem B2441279 : Blo 960589 2441279 := bstep (se 1 (by rfl) ⟨1830959, by rfl⟩ : syracuseStep 2441279 = 3661919) B3661919
theorem B24363179 : Blo 960589 24363179 := bstep (se 1 (by rfl) ⟨18272384, by rfl⟩ : syracuseStep 24363179 = 36544769) B36544769
theorem B3655145 : Blo 960589 3655145 := bstep (se 2 (by rfl) ⟨1370679, by rfl⟩ : syracuseStep 3655145 = 2741359) B2741359
theorem B3655327 : Blo 960589 3655327 := bstep (se 1 (by rfl) ⟨2741495, by rfl⟩ : syracuseStep 3655327 = 5482991) B5482991
theorem B27708743 : Blo 960589 27708743 := bstep (se 1 (by rfl) ⟨20781557, by rfl⟩ : syracuseStep 27708743 = 41563115) B41563115
theorem B1625791 : Blo 960589 1625791 := bstep (se 1 (by rfl) ⟨1219343, by rfl⟩ : syracuseStep 1625791 = 2438687) B2438687
theorem B11718539 : Blo 960589 11718539 := bstep (se 1 (by rfl) ⟨8788904, by rfl⟩ : syracuseStep 11718539 = 17577809) B17577809
theorem B1626223 : Blo 960589 1626223 := bstep (se 1 (by rfl) ⟨1219667, by rfl⟩ : syracuseStep 1626223 = 2439335) B2439335
theorem B3297439 : Blo 960589 3297439 := bstep (se 1 (by rfl) ⟨2473079, by rfl⟩ : syracuseStep 3297439 = 4946159) B4946159
theorem B15585655 : Blo 960589 15585655 := bstep (se 1 (by rfl) ⟨11689241, by rfl⟩ : syracuseStep 15585655 = 23378483) B23378483
theorem B1823791 : Blo 960589 1823791 := bstep (se 1 (by rfl) ⟨1367843, by rfl⟩ : syracuseStep 1823791 = 2735687) B2735687
theorem B5559833 : Blo 960589 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B11851487 : Blo 960589 11851487 := bstep (se 1 (by rfl) ⟨8888615, by rfl⟩ : syracuseStep 11851487 = 17777231) B17777231
theorem B3660187 : Blo 960589 3660187 := bstep (se 1 (by rfl) ⟨2745140, by rfl⟩ : syracuseStep 3660187 = 5490281) B5490281
theorem B4118941 : Blo 960589 4118941 := bstep (se 3 (by rfl) ⟨772301, by rfl⟩ : syracuseStep 4118941 = 1544603) B1544603
theorem B6511367 : Blo 960589 6511367 := bstep (se 1 (by rfl) ⟨4883525, by rfl⟩ : syracuseStep 6511367 = 9767051) B9767051
theorem B3464201 : Blo 960589 3464201 := bstep (se 2 (by rfl) ⟨1299075, by rfl⟩ : syracuseStep 3464201 = 2598151) B2598151
theorem B4874579 : Blo 960589 4874579 := bstep (se 1 (by rfl) ⟨3655934, by rfl⟩ : syracuseStep 4874579 = 7311869) B7311869
theorem B8217449 : Blo 960589 8217449 := bstep (se 2 (by rfl) ⟨3081543, by rfl⟩ : syracuseStep 8217449 = 6163087) B6163087
theorem B1827839 : Blo 960589 1827839 := bstep (se 1 (by rfl) ⟨1370879, by rfl⟩ : syracuseStep 1827839 = 2741759) B2741759
theorem B17558315 : Blo 960589 17558315 := bstep (se 1 (by rfl) ⟨13168736, by rfl⟩ : syracuseStep 17558315 = 26337473) B26337473
theorem B12512737 : Blo 960589 12512737 := bstep (se 2 (by rfl) ⟨4692276, by rfl⟩ : syracuseStep 12512737 = 9384553) B9384553
theorem B1732079 : Blo 960589 1732079 := bstep (se 1 (by rfl) ⟨1299059, by rfl⟩ : syracuseStep 1732079 = 2598119) B2598119
theorem B13168133 : Blo 960589 13168133 := bstep (se 4 (by rfl) ⟨1234512, by rfl⟩ : syracuseStep 13168133 = 2469025) B2469025
theorem B4877981 : Blo 960589 4877981 := bstep (se 3 (by rfl) ⟨914621, by rfl⟩ : syracuseStep 4877981 = 1829243) B1829243
theorem B6156269 : Blo 960589 6156269 := bstep (se 3 (by rfl) ⟨1154300, by rfl⟩ : syracuseStep 6156269 = 2308601) B2308601
theorem B4878791 : Blo 960589 4878791 := bstep (se 1 (by rfl) ⟨3659093, by rfl⟩ : syracuseStep 4878791 = 7318187) B7318187
theorem B1372639 : Blo 960589 1372639 := bstep (se 1 (by rfl) ⟨1029479, by rfl⟩ : syracuseStep 1372639 = 2058959) B2058959
theorem B11104847 : Blo 960589 11104847 := bstep (se 1 (by rfl) ⟨8328635, by rfl⟩ : syracuseStep 11104847 = 16657271) B16657271
theorem B4879115 : Blo 960589 4879115 := bstep (se 1 (by rfl) ⟨3659336, by rfl⟩ : syracuseStep 4879115 = 7318673) B7318673
theorem B16446239 : Blo 960589 16446239 := bstep (se 1 (by rfl) ⟨12334679, by rfl⟩ : syracuseStep 16446239 = 24669359) B24669359
theorem B120321821 : Blo 960589 120321821 := bstep (se 3 (by rfl) ⟨22560341, by rfl⟩ : syracuseStep 120321821 = 45120683) B45120683
theorem B71333783 : Blo 960589 71333783 := bstep (se 1 (by rfl) ⟨53500337, by rfl⟩ : syracuseStep 71333783 = 107000675) B107000675
theorem B3242267 : Blo 960589 3242267 := bstep (se 1 (by rfl) ⟨2431700, by rfl⟩ : syracuseStep 3242267 = 4863401) B4863401
theorem B4880735 : Blo 960589 4880735 := bstep (se 1 (by rfl) ⟨3660551, by rfl⟩ : syracuseStep 4880735 = 7321103) B7321103
theorem B4880897 : Blo 960589 4880897 := bstep (se 2 (by rfl) ⟨1830336, by rfl⟩ : syracuseStep 4880897 = 3660673) B3660673
theorem B1440905 : Blo 960589 1440905 := bstep (se 2 (by rfl) ⟨540339, by rfl⟩ : syracuseStep 1440905 = 1080679) B1080679
theorem B1440935 : Blo 960589 1440935 := bstep (se 1 (by rfl) ⟨1080701, by rfl⟩ : syracuseStep 1440935 = 2161403) B2161403
theorem B1440959 : Blo 960589 1440959 := bstep (se 1 (by rfl) ⟨1080719, by rfl⟩ : syracuseStep 1440959 = 2161439) B2161439
theorem B3243239 : Blo 960589 3243239 := bstep (se 1 (by rfl) ⟨2432429, by rfl⟩ : syracuseStep 3243239 = 4864859) B4864859
theorem B10943747 : Blo 960589 10943747 := bstep (se 1 (by rfl) ⟨8207810, by rfl⟩ : syracuseStep 10943747 = 16415621) B16415621
theorem B1441145 : Blo 960589 1441145 := bstep (se 2 (by rfl) ⟨540429, by rfl⟩ : syracuseStep 1441145 = 1080859) B1080859
theorem B3243887 : Blo 960589 3243887 := bstep (se 1 (by rfl) ⟨2432915, by rfl⟩ : syracuseStep 3243887 = 4865831) B4865831
theorem B2162771 : Blo 960589 2162771 := bstep (se 1 (by rfl) ⟨1622078, by rfl⟩ : syracuseStep 2162771 = 3244157) B3244157
theorem B1441883 : Blo 960589 1441883 := bstep (se 1 (by rfl) ⟨1081412, by rfl⟩ : syracuseStep 1441883 = 2162825) B2162825
theorem B2162843 : Blo 960589 2162843 := bstep (se 1 (by rfl) ⟨1622132, by rfl⟩ : syracuseStep 2162843 = 3244265) B3244265
theorem B1441967 : Blo 960589 1441967 := bstep (se 1 (by rfl) ⟨1081475, by rfl⟩ : syracuseStep 1441967 = 2162951) B2162951
theorem B1442015 : Blo 960589 1442015 := bstep (se 1 (by rfl) ⟨1081511, by rfl⟩ : syracuseStep 1442015 = 2163023) B2163023
theorem B1442783 : Blo 960589 1442783 := bstep (se 1 (by rfl) ⟨1082087, by rfl⟩ : syracuseStep 1442783 = 2164175) B2164175
theorem B9242399 : Blo 960589 9242399 := bstep (se 1 (by rfl) ⟨6931799, by rfl⟩ : syracuseStep 9242399 = 13863599) B13863599
theorem B2164715 : Blo 960589 2164715 := bstep (se 1 (by rfl) ⟨1623536, by rfl⟩ : syracuseStep 2164715 = 3247073) B3247073
theorem B1444745 : Blo 960589 1444745 := bstep (se 2 (by rfl) ⟨541779, by rfl⟩ : syracuseStep 1444745 = 1083559) B1083559
theorem B1445513 : Blo 960589 1445513 := bstep (se 2 (by rfl) ⟨542067, by rfl⟩ : syracuseStep 1445513 = 1084135) B1084135
theorem B3706555 : Blo 960589 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B7900991 : Blo 960589 7900991 := bstep (se 1 (by rfl) ⟨5925743, by rfl⟩ : syracuseStep 7900991 = 11851487) B11851487
theorem B1446095 : Blo 960589 1446095 := bstep (se 1 (by rfl) ⟨1084571, by rfl⟩ : syracuseStep 1446095 = 2169143) B2169143
theorem B2167487 : Blo 960589 2167487 := bstep (se 1 (by rfl) ⟨1625615, by rfl⟩ : syracuseStep 2167487 = 3251231) B3251231
theorem B2167721 : Blo 960589 2167721 := bstep (se 2 (by rfl) ⟨812895, by rfl⟩ : syracuseStep 2167721 = 1625791) B1625791
theorem B2168135 : Blo 960589 2168135 := bstep (se 1 (by rfl) ⟨1626101, by rfl⟩ : syracuseStep 2168135 = 3252203) B3252203
theorem B2168297 : Blo 960589 2168297 := bstep (se 2 (by rfl) ⟨813111, by rfl⟩ : syracuseStep 2168297 = 1626223) B1626223
theorem B2168315 : Blo 960589 2168315 := bstep (se 1 (by rfl) ⟨1626236, by rfl⟩ : syracuseStep 2168315 = 3252473) B3252473
theorem B3249719 : Blo 960589 3249719 := bstep (se 1 (by rfl) ⟨2437289, by rfl⟩ : syracuseStep 3249719 = 4874579) B4874579
theorem B18486953 : Blo 960589 18486953 := bstep (se 2 (by rfl) ⟨6932607, by rfl⟩ : syracuseStep 18486953 = 13865215) B13865215
theorem B20780873 : Blo 960589 20780873 := bstep (se 2 (by rfl) ⟨7792827, by rfl⟩ : syracuseStep 20780873 = 15585655) B15585655
theorem B5478299 : Blo 960589 5478299 := bstep (se 1 (by rfl) ⟨4108724, by rfl⟩ : syracuseStep 5478299 = 8217449) B8217449
theorem B1218559 : Blo 960589 1218559 := bstep (se 1 (by rfl) ⟨913919, by rfl⟩ : syracuseStep 1218559 = 1827839) B1827839
theorem B2169071 : Blo 960589 2169071 := bstep (se 1 (by rfl) ⟨1626803, by rfl⟩ : syracuseStep 2169071 = 3253607) B3253607
theorem B2431721 : Blo 960589 2431721 := bstep (se 2 (by rfl) ⟨911895, by rfl⟩ : syracuseStep 2431721 = 1823791) B1823791
theorem B2431883 : Blo 960589 2431883 := bstep (se 1 (by rfl) ⟨1823912, by rfl⟩ : syracuseStep 2431883 = 3647825) B3647825
theorem B2170043 : Blo 960589 2170043 := bstep (se 1 (by rfl) ⟨1627532, by rfl⟩ : syracuseStep 2170043 = 3255065) B3255065
theorem B11705543 : Blo 960589 11705543 := bstep (se 1 (by rfl) ⟨8779157, by rfl⟩ : syracuseStep 11705543 = 17558315) B17558315
theorem B1154719 : Blo 960589 1154719 := bstep (se 1 (by rfl) ⟨866039, by rfl⟩ : syracuseStep 1154719 = 1732079) B1732079
theorem B5643935 : Blo 960589 5643935 := bstep (se 1 (by rfl) ⟨4232951, by rfl⟩ : syracuseStep 5643935 = 8465903) B8465903
theorem B3251987 : Blo 960589 3251987 := bstep (se 1 (by rfl) ⟨2438990, by rfl⟩ : syracuseStep 3251987 = 4877981) B4877981
theorem B4104179 : Blo 960589 4104179 := bstep (se 1 (by rfl) ⟨3078134, by rfl⟩ : syracuseStep 4104179 = 6156269) B6156269
theorem B3252527 : Blo 960589 3252527 := bstep (se 1 (by rfl) ⟨2439395, by rfl⟩ : syracuseStep 3252527 = 4878791) B4878791
theorem B2433503 : Blo 960589 2433503 := bstep (se 1 (by rfl) ⟨1825127, by rfl⟩ : syracuseStep 2433503 = 3650255) B3650255
theorem B3252743 : Blo 960589 3252743 := bstep (se 1 (by rfl) ⟨2439557, by rfl⟩ : syracuseStep 3252743 = 4879115) B4879115
theorem B2434283 : Blo 960589 2434283 := bstep (se 1 (by rfl) ⟨1825712, by rfl⟩ : syracuseStep 2434283 = 3651425) B3651425
theorem B47555855 : Blo 960589 47555855 := bstep (se 1 (by rfl) ⟨35666891, by rfl⟩ : syracuseStep 47555855 = 71333783) B71333783
theorem B3253823 : Blo 960589 3253823 := bstep (se 1 (by rfl) ⟨2440367, by rfl⟩ : syracuseStep 3253823 = 4880735) B4880735
theorem B3253931 : Blo 960589 3253931 := bstep (se 1 (by rfl) ⟨2440448, by rfl⟩ : syracuseStep 3253931 = 4880897) B4880897
theorem B960603 : Blo 960589 960603 := bstep (se 1 (by rfl) ⟨720452, by rfl⟩ : syracuseStep 960603 = 1440905) B1440905
theorem B960623 : Blo 960589 960623 := bstep (se 1 (by rfl) ⟨720467, by rfl⟩ : syracuseStep 960623 = 1440935) B1440935
theorem B960639 : Blo 960589 960639 := bstep (se 1 (by rfl) ⟨720479, by rfl⟩ : syracuseStep 960639 = 1440959) B1440959
theorem B960763 : Blo 960589 960763 := bstep (se 1 (by rfl) ⟨720572, by rfl⟩ : syracuseStep 960763 = 1441145) B1441145
theorem B961407 : Blo 960589 961407 := bstep (se 1 (by rfl) ⟨721055, by rfl⟩ : syracuseStep 961407 = 1442111) B1442111
theorem B4631543 : Blo 960589 4631543 := bstep (se 1 (by rfl) ⟨3473657, by rfl⟩ : syracuseStep 4631543 = 6947315) B6947315
theorem B961535 : Blo 960589 961535 := bstep (se 1 (by rfl) ⟨721151, by rfl⟩ : syracuseStep 961535 = 1442303) B1442303
theorem B961627 : Blo 960589 961627 := bstep (se 1 (by rfl) ⟨721220, by rfl⟩ : syracuseStep 961627 = 1442441) B1442441
theorem B62434475 : Blo 960589 62434475 := bstep (se 1 (by rfl) ⟨46825856, by rfl⟩ : syracuseStep 62434475 = 93651713) B93651713
theorem B961983 : Blo 960589 961983 := bstep (se 1 (by rfl) ⟨721487, by rfl⟩ : syracuseStep 961983 = 1442975) B1442975
theorem B2436763 : Blo 960589 2436763 := bstep (se 1 (by rfl) ⟨1827572, by rfl⟩ : syracuseStep 2436763 = 3655145) B3655145
theorem B962255 : Blo 960589 962255 := bstep (se 1 (by rfl) ⟨721691, by rfl⟩ : syracuseStep 962255 = 1443383) B1443383
theorem B962303 : Blo 960589 962303 := bstep (se 1 (by rfl) ⟨721727, by rfl⟩ : syracuseStep 962303 = 1443455) B1443455
theorem B3649495 : Blo 960589 3649495 := bstep (se 1 (by rfl) ⟨2737121, by rfl⟩ : syracuseStep 3649495 = 5474243) B5474243
theorem B962651 : Blo 960589 962651 := bstep (se 1 (by rfl) ⟨721988, by rfl⟩ : syracuseStep 962651 = 1443977) B1443977
theorem B6926471 : Blo 960589 6926471 := bstep (se 1 (by rfl) ⟨5194853, by rfl⟩ : syracuseStep 6926471 = 10389707) B10389707
theorem B963119 : Blo 960589 963119 := bstep (se 1 (by rfl) ⟨722339, by rfl⟩ : syracuseStep 963119 = 1444679) B1444679
theorem B963199 : Blo 960589 963199 := bstep (se 1 (by rfl) ⟨722399, by rfl⟩ : syracuseStep 963199 = 1444799) B1444799
theorem B963263 : Blo 960589 963263 := bstep (se 1 (by rfl) ⟨722447, by rfl⟩ : syracuseStep 963263 = 1444895) B1444895
theorem B963455 : Blo 960589 963455 := bstep (se 1 (by rfl) ⟨722591, by rfl⟩ : syracuseStep 963455 = 1445183) B1445183
theorem B963583 : Blo 960589 963583 := bstep (se 1 (by rfl) ⟨722687, by rfl⟩ : syracuseStep 963583 = 1445375) B1445375
theorem B3650771 : Blo 960589 3650771 := bstep (se 1 (by rfl) ⟨2738078, by rfl⟩ : syracuseStep 3650771 = 5476157) B5476157
theorem B7812359 : Blo 960589 7812359 := bstep (se 1 (by rfl) ⟨5859269, by rfl⟩ : syracuseStep 7812359 = 11718539) B11718539
theorem B5485907 : Blo 960589 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B964143 : Blo 960589 964143 := bstep (se 1 (by rfl) ⟨723107, by rfl⟩ : syracuseStep 964143 = 1446215) B1446215
theorem B8238671 : Blo 960589 8238671 := bstep (se 1 (by rfl) ⟨6179003, by rfl⟩ : syracuseStep 8238671 = 12358007) B12358007
theorem B3651227 : Blo 960589 3651227 := bstep (se 1 (by rfl) ⟨2738420, by rfl⟩ : syracuseStep 3651227 = 5476841) B5476841
theorem B964327 : Blo 960589 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B964351 : Blo 960589 964351 := bstep (se 1 (by rfl) ⟨723263, by rfl⟩ : syracuseStep 964351 = 1446527) B1446527
theorem B3651439 : Blo 960589 3651439 := bstep (se 1 (by rfl) ⟨2738579, by rfl⟩ : syracuseStep 3651439 = 5477159) B5477159
theorem B964575 : Blo 960589 964575 := bstep (se 1 (by rfl) ⟨723431, by rfl⟩ : syracuseStep 964575 = 1446863) B1446863
theorem B3652715 : Blo 960589 3652715 := bstep (se 1 (by rfl) ⟨2739536, by rfl⟩ : syracuseStep 3652715 = 5479073) B5479073
theorem B4340911 : Blo 960589 4340911 := bstep (se 1 (by rfl) ⟨3255683, by rfl⟩ : syracuseStep 4340911 = 6511367) B6511367
theorem B3652883 : Blo 960589 3652883 := bstep (se 1 (by rfl) ⟨2739662, by rfl⟩ : syracuseStep 3652883 = 5479325) B5479325
theorem B2309467 : Blo 960589 2309467 := bstep (se 1 (by rfl) ⟨1732100, by rfl⟩ : syracuseStep 2309467 = 3464201) B3464201
theorem B4114415 : Blo 960589 4114415 := bstep (se 1 (by rfl) ⟨3085811, by rfl⟩ : syracuseStep 4114415 = 6171623) B6171623
theorem B1624171 : Blo 960589 1624171 := bstep (se 1 (by rfl) ⟨1218128, by rfl⟩ : syracuseStep 1624171 = 2436257) B2436257
theorem B66734597 : Blo 960589 66734597 := bstep (se 4 (by rfl) ⟨6256368, by rfl⟩ : syracuseStep 66734597 = 12512737) B12512737
theorem B10964159 : Blo 960589 10964159 := bstep (se 1 (by rfl) ⟨8223119, by rfl⟩ : syracuseStep 10964159 = 16446239) B16446239
theorem B5491921 : Blo 960589 5491921 := bstep (se 2 (by rfl) ⟨2059470, by rfl⟩ : syracuseStep 5491921 = 4118941) B4118941
theorem B18534005 : Blo 960589 18534005 := bstep (se 5 (by rfl) ⟨868781, by rfl⟩ : syracuseStep 18534005 = 1737563) B1737563
theorem B28168195 : Blo 960589 28168195 := bstep (se 1 (by rfl) ⟨21126146, by rfl⟩ : syracuseStep 28168195 = 42252293) B42252293
theorem B7295831 : Blo 960589 7295831 := bstep (se 1 (by rfl) ⟨5471873, by rfl⟩ : syracuseStep 7295831 = 10943747) B10943747
theorem B2741131 : Blo 960589 2741131 := bstep (se 1 (by rfl) ⟨2055848, by rfl⟩ : syracuseStep 2741131 = 4111697) B4111697
theorem B1627519 : Blo 960589 1627519 := bstep (se 1 (by rfl) ⟨1220639, by rfl⟩ : syracuseStep 1627519 = 2441279) B2441279
theorem B16242119 : Blo 960589 16242119 := bstep (se 1 (by rfl) ⟨12181589, by rfl⟩ : syracuseStep 16242119 = 24363179) B24363179
theorem B5002991 : Blo 960589 5002991 := bstep (se 1 (by rfl) ⟨3752243, by rfl⟩ : syracuseStep 5002991 = 7504487) B7504487
theorem B8345567 : Blo 960589 8345567 := bstep (se 1 (by rfl) ⟨6259175, by rfl⟩ : syracuseStep 8345567 = 12518351) B12518351
theorem B17586341 : Blo 960589 17586341 := bstep (se 4 (by rfl) ⟨1648719, by rfl⟩ : syracuseStep 17586341 = 3297439) B3297439
theorem B2055431 : Blo 960589 2055431 := bstep (se 1 (by rfl) ⟨1541573, by rfl⟩ : syracuseStep 2055431 = 3083147) B3083147
theorem B4873769 : Blo 960589 4873769 := bstep (se 2 (by rfl) ⟨1827663, by rfl⟩ : syracuseStep 4873769 = 3655327) B3655327
theorem B18472495 : Blo 960589 18472495 := bstep (se 1 (by rfl) ⟨13854371, by rfl⟩ : syracuseStep 18472495 = 27708743) B27708743
theorem B3466361 : Blo 960589 3466361 := bstep (se 2 (by rfl) ⟨1299885, by rfl⟩ : syracuseStep 3466361 = 2599771) B2599771
theorem B2058617 : Blo 960589 2058617 := bstep (se 2 (by rfl) ⟨771981, by rfl⟩ : syracuseStep 2058617 = 1543963) B1543963
theorem B8219839 : Blo 960589 8219839 := bstep (se 1 (by rfl) ⟨6164879, by rfl⟩ : syracuseStep 8219839 = 12329759) B12329759
theorem B1830185 : Blo 960589 1830185 := bstep (se 2 (by rfl) ⟨686319, by rfl⟩ : syracuseStep 1830185 = 1372639) B1372639
theorem B2059967 : Blo 960589 2059967 := bstep (se 1 (by rfl) ⟨1544975, by rfl⟩ : syracuseStep 2059967 = 3089951) B3089951
theorem B1733023 : Blo 960589 1733023 := bstep (se 1 (by rfl) ⟨1299767, by rfl⟩ : syracuseStep 1733023 = 2599535) B2599535
theorem B8450729 : Blo 960589 8450729 := bstep (se 2 (by rfl) ⟨3169023, by rfl⟩ : syracuseStep 8450729 = 6338047) B6338047
theorem B8778755 : Blo 960589 8778755 := bstep (se 1 (by rfl) ⟨6584066, by rfl⟩ : syracuseStep 8778755 = 13168133) B13168133
theorem B7403231 : Blo 960589 7403231 := bstep (se 1 (by rfl) ⟨5552423, by rfl⟩ : syracuseStep 7403231 = 11104847) B11104847
theorem B4880249 : Blo 960589 4880249 := bstep (se 2 (by rfl) ⟨1830093, by rfl⟩ : syracuseStep 4880249 = 3660187) B3660187
theorem B7305551 : Blo 960589 7305551 := bstep (se 1 (by rfl) ⟨5479163, by rfl⟩ : syracuseStep 7305551 = 10958327) B10958327
theorem B80214547 : Blo 960589 80214547 := bstep (se 1 (by rfl) ⟨60160910, by rfl⟩ : syracuseStep 80214547 = 120321821) B120321821
theorem B2161511 : Blo 960589 2161511 := bstep (se 1 (by rfl) ⟨1621133, by rfl⟩ : syracuseStep 2161511 = 3242267) B3242267
theorem B2162159 : Blo 960589 2162159 := bstep (se 1 (by rfl) ⟨1621619, by rfl⟩ : syracuseStep 2162159 = 3243239) B3243239
theorem B2162249 : Blo 960589 2162249 := bstep (se 2 (by rfl) ⟨810843, by rfl⟩ : syracuseStep 2162249 = 1621687) B1621687
theorem B2162591 : Blo 960589 2162591 := bstep (se 1 (by rfl) ⟨1621943, by rfl⟩ : syracuseStep 2162591 = 3243887) B3243887
theorem B1441847 : Blo 960589 1441847 := bstep (se 1 (by rfl) ⟨1081385, by rfl⟩ : syracuseStep 1441847 = 2162771) B2162771
theorem B1441895 : Blo 960589 1441895 := bstep (se 1 (by rfl) ⟨1081421, by rfl⟩ : syracuseStep 1441895 = 2162843) B2162843
theorem B6161599 : Blo 960589 6161599 := bstep (se 1 (by rfl) ⟨4621199, by rfl⟩ : syracuseStep 6161599 = 9242399) B9242399
theorem B1443143 : Blo 960589 1443143 := bstep (se 1 (by rfl) ⟨1082357, by rfl⟩ : syracuseStep 1443143 = 2164715) B2164715
theorem B7309439 : Blo 960589 7309439 := bstep (se 1 (by rfl) ⟨5482079, by rfl⟩ : syracuseStep 7309439 = 10964159) B10964159
theorem B12356003 : Blo 960589 12356003 := bstep (se 1 (by rfl) ⟨9267002, by rfl⟩ : syracuseStep 12356003 = 18534005) B18534005
theorem B2165561 : Blo 960589 2165561 := bstep (se 2 (by rfl) ⟨812085, by rfl⟩ : syracuseStep 2165561 = 1624171) B1624171
theorem B9243629 : Blo 960589 9243629 := bstep (se 3 (by rfl) ⟨1733180, by rfl⟩ : syracuseStep 9243629 = 3466361) B3466361
theorem B1444991 : Blo 960589 1444991 := bstep (se 1 (by rfl) ⟨1083743, by rfl⟩ : syracuseStep 1444991 = 2167487) B2167487
theorem B1445147 : Blo 960589 1445147 := bstep (se 1 (by rfl) ⟨1083860, by rfl⟩ : syracuseStep 1445147 = 2167721) B2167721
theorem B1445423 : Blo 960589 1445423 := bstep (se 1 (by rfl) ⟨1084067, by rfl⟩ : syracuseStep 1445423 = 2168135) B2168135
theorem B1445531 : Blo 960589 1445531 := bstep (se 1 (by rfl) ⟨1084148, by rfl⟩ : syracuseStep 1445531 = 2168297) B2168297
theorem B1445543 : Blo 960589 1445543 := bstep (se 1 (by rfl) ⟨1084157, by rfl⟩ : syracuseStep 1445543 = 2168315) B2168315
theorem B2166479 : Blo 960589 2166479 := bstep (se 1 (by rfl) ⟨1624859, by rfl⟩ : syracuseStep 2166479 = 3249719) B3249719
theorem B12324635 : Blo 960589 12324635 := bstep (se 1 (by rfl) ⟨9243476, by rfl⟩ : syracuseStep 12324635 = 18486953) B18486953
theorem B1446047 : Blo 960589 1446047 := bstep (se 1 (by rfl) ⟨1084535, by rfl⟩ : syracuseStep 1446047 = 2169071) B2169071
theorem B1446695 : Blo 960589 1446695 := bstep (se 1 (by rfl) ⟨1085021, by rfl⟩ : syracuseStep 1446695 = 2170043) B2170043
theorem B7803695 : Blo 960589 7803695 := bstep (se 1 (by rfl) ⟨5852771, by rfl⟩ : syracuseStep 7803695 = 11705543) B11705543
theorem B3249017 : Blo 960589 3249017 := bstep (se 2 (by rfl) ⟨1218381, by rfl⟩ : syracuseStep 3249017 = 2436763) B2436763
theorem B3249179 : Blo 960589 3249179 := bstep (se 1 (by rfl) ⟨2436884, by rfl⟩ : syracuseStep 3249179 = 4873769) B4873769
theorem B2167991 : Blo 960589 2167991 := bstep (se 1 (by rfl) ⟨1625993, by rfl⟩ : syracuseStep 2167991 = 3251987) B3251987
theorem B37557593 : Blo 960589 37557593 := bstep (se 2 (by rfl) ⟨14084097, by rfl⟩ : syracuseStep 37557593 = 28168195) B28168195
theorem B2168351 : Blo 960589 2168351 := bstep (se 1 (by rfl) ⟨1626263, by rfl⟩ : syracuseStep 2168351 = 3252527) B3252527
theorem B2168495 : Blo 960589 2168495 := bstep (se 1 (by rfl) ⟨1626371, by rfl⟩ : syracuseStep 2168495 = 3252743) B3252743
theorem B2169215 : Blo 960589 2169215 := bstep (se 1 (by rfl) ⟨1626911, by rfl⟩ : syracuseStep 2169215 = 3253823) B3253823
theorem B2169287 : Blo 960589 2169287 := bstep (se 1 (by rfl) ⟨1626965, by rfl⟩ : syracuseStep 2169287 = 3253931) B3253931
theorem B2170025 : Blo 960589 2170025 := bstep (se 2 (by rfl) ⟨813759, by rfl⟩ : syracuseStep 2170025 = 1627519) B1627519
theorem B3087695 : Blo 960589 3087695 := bstep (se 1 (by rfl) ⟨2315771, by rfl⟩ : syracuseStep 3087695 = 4631543) B4631543
theorem B41622983 : Blo 960589 41622983 := bstep (se 1 (by rfl) ⟨31217237, by rfl⟩ : syracuseStep 41622983 = 62434475) B62434475
theorem B1220123 : Blo 960589 1220123 := bstep (se 1 (by rfl) ⟨915092, by rfl⟩ : syracuseStep 1220123 = 1830185) B1830185
theorem B2433847 : Blo 960589 2433847 := bstep (se 1 (by rfl) ⟨1825385, by rfl⟩ : syracuseStep 2433847 = 3650771) B3650771
theorem B2434151 : Blo 960589 2434151 := bstep (se 1 (by rfl) ⟨1825613, by rfl⟩ : syracuseStep 2434151 = 3651227) B3651227
theorem B3253499 : Blo 960589 3253499 := bstep (se 1 (by rfl) ⟨2440124, by rfl⟩ : syracuseStep 3253499 = 4880249) B4880249
theorem B2435143 : Blo 960589 2435143 := bstep (se 1 (by rfl) ⟨1826357, by rfl⟩ : syracuseStep 2435143 = 3652715) B3652715
theorem B2435255 : Blo 960589 2435255 := bstep (se 1 (by rfl) ⟨1826441, by rfl⟩ : syracuseStep 2435255 = 3652883) B3652883
theorem B961255 : Blo 960589 961255 := bstep (se 1 (by rfl) ⟨720941, by rfl⟩ : syracuseStep 961255 = 1441883) B1441883
theorem B961311 : Blo 960589 961311 := bstep (se 1 (by rfl) ⟨720983, by rfl⟩ : syracuseStep 961311 = 1441967) B1441967
theorem B961343 : Blo 960589 961343 := bstep (se 1 (by rfl) ⟨721007, by rfl⟩ : syracuseStep 961343 = 1442015) B1442015
theorem B961855 : Blo 960589 961855 := bstep (se 1 (by rfl) ⟨721391, by rfl⟩ : syracuseStep 961855 = 1442783) B1442783
theorem B963163 : Blo 960589 963163 := bstep (se 1 (by rfl) ⟨722372, by rfl⟩ : syracuseStep 963163 = 1444745) B1444745
theorem B963675 : Blo 960589 963675 := bstep (se 1 (by rfl) ⟨722756, by rfl⟩ : syracuseStep 963675 = 1445513) B1445513
theorem B964063 : Blo 960589 964063 := bstep (se 1 (by rfl) ⟨723047, by rfl⟩ : syracuseStep 964063 = 1446095) B1446095
theorem B4863887 : Blo 960589 4863887 := bstep (se 1 (by rfl) ⟨3647915, by rfl⟩ : syracuseStep 4863887 = 7295831) B7295831
theorem B10828079 : Blo 960589 10828079 := bstep (se 1 (by rfl) ⟨8121059, by rfl⟩ : syracuseStep 10828079 = 16242119) B16242119
theorem B3652199 : Blo 960589 3652199 := bstep (se 1 (by rfl) ⟨2739149, by rfl⟩ : syracuseStep 3652199 = 5478299) B5478299
theorem B10959785 : Blo 960589 10959785 := bstep (se 2 (by rfl) ⟨4109919, by rfl⟩ : syracuseStep 10959785 = 8219839) B8219839
theorem B7322561 : Blo 960589 7322561 := bstep (se 2 (by rfl) ⟨2745960, by rfl⟩ : syracuseStep 7322561 = 5491921) B5491921
theorem B1621147 : Blo 960589 1621147 := bstep (se 1 (by rfl) ⟨1215860, by rfl⟩ : syracuseStep 1621147 = 2431721) B2431721
theorem B1621255 : Blo 960589 1621255 := bstep (se 1 (by rfl) ⟨1215941, by rfl⟩ : syracuseStep 1621255 = 2431883) B2431883
theorem B4865993 : Blo 960589 4865993 := bstep (se 2 (by rfl) ⟨1824747, by rfl⟩ : syracuseStep 4865993 = 3649495) B3649495
theorem B2736119 : Blo 960589 2736119 := bstep (se 1 (by rfl) ⟨2052089, by rfl⟩ : syracuseStep 2736119 = 4104179) B4104179
theorem B1622335 : Blo 960589 1622335 := bstep (se 1 (by rfl) ⟨1216751, by rfl⟩ : syracuseStep 1622335 = 2433503) B2433503
theorem B2310697 : Blo 960589 2310697 := bstep (se 2 (by rfl) ⟨866511, by rfl⟩ : syracuseStep 2310697 = 1733023) B1733023
theorem B1622855 : Blo 960589 1622855 := bstep (se 1 (by rfl) ⟨1217141, by rfl⟩ : syracuseStep 1622855 = 2434283) B2434283
theorem B31703903 : Blo 960589 31703903 := bstep (se 1 (by rfl) ⟨23777927, by rfl⟩ : syracuseStep 31703903 = 47555855) B47555855
theorem B3654841 : Blo 960589 3654841 := bstep (se 2 (by rfl) ⟨1370565, by rfl⟩ : syracuseStep 3654841 = 2741131) B2741131
theorem B4868585 : Blo 960589 4868585 := bstep (se 2 (by rfl) ⟨1825719, by rfl⟩ : syracuseStep 4868585 = 3651439) B3651439
theorem B1624745 : Blo 960589 1624745 := bstep (se 2 (by rfl) ⟨609279, by rfl⟩ : syracuseStep 1624745 = 1218559) B1218559
theorem B5852503 : Blo 960589 5852503 := bstep (se 1 (by rfl) ⟨4389377, by rfl⟩ : syracuseStep 5852503 = 8778755) B8778755
theorem B3657271 : Blo 960589 3657271 := bstep (se 1 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 3657271 = 5485907) B5485907
theorem B5492447 : Blo 960589 5492447 := bstep (se 1 (by rfl) ⟨4119335, by rfl⟩ : syracuseStep 5492447 = 8238671) B8238671
theorem B4935487 : Blo 960589 4935487 := bstep (se 1 (by rfl) ⟨3701615, by rfl⟩ : syracuseStep 4935487 = 7403231) B7403231
theorem B4870367 : Blo 960589 4870367 := bstep (se 1 (by rfl) ⟨3652775, by rfl⟩ : syracuseStep 4870367 = 7305551) B7305551
theorem B5787881 : Blo 960589 5787881 := bstep (se 2 (by rfl) ⟨2170455, by rfl⟩ : syracuseStep 5787881 = 4340911) B4340911
theorem B24629993 : Blo 960589 24629993 := bstep (se 2 (by rfl) ⟨9236247, by rfl⟩ : syracuseStep 24629993 = 18472495) B18472495
theorem B2742943 : Blo 960589 2742943 := bstep (se 1 (by rfl) ⟨2057207, by rfl⟩ : syracuseStep 2742943 = 4114415) B4114415
theorem B44489731 : Blo 960589 44489731 := bstep (se 1 (by rfl) ⟨33367298, by rfl⟩ : syracuseStep 44489731 = 66734597) B66734597
theorem B5267327 : Blo 960589 5267327 := bstep (se 1 (by rfl) ⟨3950495, by rfl⟩ : syracuseStep 5267327 = 7900991) B7900991
theorem B3335327 : Blo 960589 3335327 := bstep (se 1 (by rfl) ⟨2501495, by rfl⟩ : syracuseStep 3335327 = 5002991) B5002991
theorem B13853915 : Blo 960589 13853915 := bstep (se 1 (by rfl) ⟨10390436, by rfl⟩ : syracuseStep 13853915 = 20780873) B20780873
theorem B5563711 : Blo 960589 5563711 := bstep (se 1 (by rfl) ⟨4172783, by rfl⟩ : syracuseStep 5563711 = 8345567) B8345567
theorem B11724227 : Blo 960589 11724227 := bstep (se 1 (by rfl) ⟨8793170, by rfl⟩ : syracuseStep 11724227 = 17586341) B17586341
theorem B1370287 : Blo 960589 1370287 := bstep (se 1 (by rfl) ⟨1027715, by rfl⟩ : syracuseStep 1370287 = 2055431) B2055431
theorem B4942073 : Blo 960589 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B3762623 : Blo 960589 3762623 := bstep (se 1 (by rfl) ⟨2821967, by rfl⟩ : syracuseStep 3762623 = 5643935) B5643935
theorem B1372411 : Blo 960589 1372411 := bstep (se 1 (by rfl) ⟨1029308, by rfl⟩ : syracuseStep 1372411 = 2058617) B2058617
theorem B1373311 : Blo 960589 1373311 := bstep (se 1 (by rfl) ⟨1029983, by rfl⟩ : syracuseStep 1373311 = 2059967) B2059967
theorem B4617647 : Blo 960589 4617647 := bstep (se 1 (by rfl) ⟨3463235, by rfl⟩ : syracuseStep 4617647 = 6926471) B6926471
theorem B5633819 : Blo 960589 5633819 := bstep (se 1 (by rfl) ⟨4225364, by rfl⟩ : syracuseStep 5633819 = 8450729) B8450729
theorem B106952729 : Blo 960589 106952729 := bstep (se 2 (by rfl) ⟨40107273, by rfl⟩ : syracuseStep 106952729 = 80214547) B80214547
theorem B6158501 : Blo 960589 6158501 := bstep (se 4 (by rfl) ⟨577359, by rfl⟩ : syracuseStep 6158501 = 1154719) B1154719
theorem B5208239 : Blo 960589 5208239 := bstep (se 1 (by rfl) ⟨3906179, by rfl⟩ : syracuseStep 5208239 = 7812359) B7812359
theorem B3079289 : Blo 960589 3079289 := bstep (se 2 (by rfl) ⟨1154733, by rfl⟩ : syracuseStep 3079289 = 2309467) B2309467
theorem B1441007 : Blo 960589 1441007 := bstep (se 1 (by rfl) ⟨1080755, by rfl⟩ : syracuseStep 1441007 = 2161511) B2161511
theorem B1441439 : Blo 960589 1441439 := bstep (se 1 (by rfl) ⟨1081079, by rfl⟩ : syracuseStep 1441439 = 2162159) B2162159
theorem B1441499 : Blo 960589 1441499 := bstep (se 1 (by rfl) ⟨1081124, by rfl⟩ : syracuseStep 1441499 = 2162249) B2162249
theorem B1441727 : Blo 960589 1441727 := bstep (se 1 (by rfl) ⟨1081295, by rfl⟩ : syracuseStep 1441727 = 2162591) B2162591
theorem B2163113 : Blo 960589 2163113 := bstep (se 2 (by rfl) ⟨811167, by rfl⟩ : syracuseStep 2163113 = 1622335) B1622335
theorem B1081903 : Blo 960589 1081903 := bstep (se 1 (by rfl) ⟨811427, by rfl⟩ : syracuseStep 1081903 = 1622855) B1622855
theorem B21135935 : Blo 960589 21135935 := bstep (se 1 (by rfl) ⟨15851951, by rfl⟩ : syracuseStep 21135935 = 31703903) B31703903
theorem B3080929 : Blo 960589 3080929 := bstep (se 2 (by rfl) ⟨1155348, by rfl⟩ : syracuseStep 3080929 = 2310697) B2310697
theorem B3245129 : Blo 960589 3245129 := bstep (se 2 (by rfl) ⟨1216923, by rfl⟩ : syracuseStep 3245129 = 2433847) B2433847
theorem B3245723 : Blo 960589 3245723 := bstep (se 1 (by rfl) ⟨2434292, by rfl⟩ : syracuseStep 3245723 = 4868585) B4868585
theorem B1083163 : Blo 960589 1083163 := bstep (se 1 (by rfl) ⟨812372, by rfl⟩ : syracuseStep 1083163 = 1624745) B1624745
theorem B1443707 : Blo 960589 1443707 := bstep (se 1 (by rfl) ⟨1082780, by rfl⟩ : syracuseStep 1443707 = 2165561) B2165561
theorem B6162419 : Blo 960589 6162419 := bstep (se 1 (by rfl) ⟨4621814, by rfl⟩ : syracuseStep 6162419 = 9243629) B9243629
theorem B1444319 : Blo 960589 1444319 := bstep (se 1 (by rfl) ⟨1083239, by rfl⟩ : syracuseStep 1444319 = 2166479) B2166479
theorem B3246857 : Blo 960589 3246857 := bstep (se 2 (by rfl) ⟨1217571, by rfl⟩ : syracuseStep 3246857 = 2435143) B2435143
theorem B3246911 : Blo 960589 3246911 := bstep (se 1 (by rfl) ⟨2435183, by rfl⟩ : syracuseStep 3246911 = 4870367) B4870367
theorem B16419995 : Blo 960589 16419995 := bstep (se 1 (by rfl) ⟨12314996, by rfl⟩ : syracuseStep 16419995 = 24629993) B24629993
theorem B2166011 : Blo 960589 2166011 := bstep (se 1 (by rfl) ⟨1624508, by rfl⟩ : syracuseStep 2166011 = 3249017) B3249017
theorem B2166119 : Blo 960589 2166119 := bstep (se 1 (by rfl) ⟨1624589, by rfl⟩ : syracuseStep 2166119 = 3249179) B3249179
theorem B1445327 : Blo 960589 1445327 := bstep (se 1 (by rfl) ⟨1083995, by rfl⟩ : syracuseStep 1445327 = 2167991) B2167991
theorem B25038395 : Blo 960589 25038395 := bstep (se 1 (by rfl) ⟨18778796, by rfl⟩ : syracuseStep 25038395 = 37557593) B37557593
theorem B1445567 : Blo 960589 1445567 := bstep (se 1 (by rfl) ⟨1084175, by rfl⟩ : syracuseStep 1445567 = 2168351) B2168351
theorem B1445663 : Blo 960589 1445663 := bstep (se 1 (by rfl) ⟨1084247, by rfl⟩ : syracuseStep 1445663 = 2168495) B2168495
theorem B1446143 : Blo 960589 1446143 := bstep (se 1 (by rfl) ⟨1084607, by rfl⟩ : syracuseStep 1446143 = 2169215) B2169215
theorem B1446191 : Blo 960589 1446191 := bstep (se 1 (by rfl) ⟨1084643, by rfl⟩ : syracuseStep 1446191 = 2169287) B2169287
theorem B7803337 : Blo 960589 7803337 := bstep (se 2 (by rfl) ⟨2926251, by rfl⟩ : syracuseStep 7803337 = 5852503) B5852503
theorem B1446683 : Blo 960589 1446683 := bstep (se 1 (by rfl) ⟨1085012, by rfl⟩ : syracuseStep 1446683 = 2170025) B2170025
theorem B13178861 : Blo 960589 13178861 := bstep (se 3 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 13178861 = 4942073) B4942073
theorem B2168999 : Blo 960589 2168999 := bstep (se 1 (by rfl) ⟨1626749, by rfl⟩ : syracuseStep 2168999 = 3253499) B3253499
theorem B59319641 : Blo 960589 59319641 := bstep (se 2 (by rfl) ⟨22244865, by rfl⟩ : syracuseStep 59319641 = 44489731) B44489731
theorem B3253661 : Blo 960589 3253661 := bstep (se 3 (by rfl) ⟨610061, by rfl⟩ : syracuseStep 3253661 = 1220123) B1220123
theorem B4105667 : Blo 960589 4105667 := bstep (se 1 (by rfl) ⟨3079250, by rfl⟩ : syracuseStep 4105667 = 6158501) B6158501
theorem B7218719 : Blo 960589 7218719 := bstep (se 1 (by rfl) ⟨5414039, by rfl⟩ : syracuseStep 7218719 = 10828079) B10828079
theorem B2434799 : Blo 960589 2434799 := bstep (se 1 (by rfl) ⟨1826099, by rfl⟩ : syracuseStep 2434799 = 3652199) B3652199
theorem B960671 : Blo 960589 960671 := bstep (se 1 (by rfl) ⟨720503, by rfl⟩ : syracuseStep 960671 = 1441007) B1441007
theorem B960959 : Blo 960589 960959 := bstep (se 1 (by rfl) ⟨720719, by rfl⟩ : syracuseStep 960959 = 1441439) B1441439
theorem B960999 : Blo 960589 960999 := bstep (se 1 (by rfl) ⟨720749, by rfl⟩ : syracuseStep 960999 = 1441499) B1441499
theorem B961151 : Blo 960589 961151 := bstep (se 1 (by rfl) ⟨720863, by rfl⟩ : syracuseStep 961151 = 1441727) B1441727
theorem B961231 : Blo 960589 961231 := bstep (se 1 (by rfl) ⟨720923, by rfl⟩ : syracuseStep 961231 = 1441847) B1441847
theorem B961263 : Blo 960589 961263 := bstep (se 1 (by rfl) ⟨720947, by rfl⟩ : syracuseStep 961263 = 1441895) B1441895
theorem B1140829109 : Blo 960589 1140829109 := bstep (se 5 (by rfl) ⟨53476364, by rfl⟩ : syracuseStep 1140829109 = 106952729) B106952729
theorem B962095 : Blo 960589 962095 := bstep (se 1 (by rfl) ⟨721571, by rfl⟩ : syracuseStep 962095 = 1443143) B1443143
theorem B8237335 : Blo 960589 8237335 := bstep (se 1 (by rfl) ⟨6178001, by rfl⟩ : syracuseStep 8237335 = 12356003) B12356003
theorem B963327 : Blo 960589 963327 := bstep (se 1 (by rfl) ⟨722495, by rfl⟩ : syracuseStep 963327 = 1444991) B1444991
theorem B963431 : Blo 960589 963431 := bstep (se 1 (by rfl) ⟨722573, by rfl⟩ : syracuseStep 963431 = 1445147) B1445147
theorem B963615 : Blo 960589 963615 := bstep (se 1 (by rfl) ⟨722711, by rfl⟩ : syracuseStep 963615 = 1445423) B1445423
theorem B963687 : Blo 960589 963687 := bstep (se 1 (by rfl) ⟨722765, by rfl⟩ : syracuseStep 963687 = 1445531) B1445531
theorem B963695 : Blo 960589 963695 := bstep (se 1 (by rfl) ⟨722771, by rfl⟩ : syracuseStep 963695 = 1445543) B1445543
theorem B964031 : Blo 960589 964031 := bstep (se 1 (by rfl) ⟨723023, by rfl⟩ : syracuseStep 964031 = 1446047) B1446047
theorem B964463 : Blo 960589 964463 := bstep (se 1 (by rfl) ⟨723347, by rfl⟩ : syracuseStep 964463 = 1446695) B1446695
theorem B1622767 : Blo 960589 1622767 := bstep (se 1 (by rfl) ⟨1217075, by rfl⟩ : syracuseStep 1622767 = 2434151) B2434151
theorem B7816151 : Blo 960589 7816151 := bstep (se 1 (by rfl) ⟨5862113, by rfl⟩ : syracuseStep 7816151 = 11724227) B11724227
theorem B1623503 : Blo 960589 1623503 := bstep (se 1 (by rfl) ⟨1217627, by rfl⟩ : syracuseStep 1623503 = 2435255) B2435255
theorem B2508415 : Blo 960589 2508415 := bstep (se 1 (by rfl) ⟨1881311, by rfl⟩ : syracuseStep 2508415 = 3762623) B3762623
theorem B29673125 : Blo 960589 29673125 := bstep (se 4 (by rfl) ⟨2781855, by rfl⟩ : syracuseStep 29673125 = 5563711) B5563711
theorem B3657257 : Blo 960589 3657257 := bstep (se 2 (by rfl) ⟨1371471, by rfl⟩ : syracuseStep 3657257 = 2742943) B2742943
theorem B3755879 : Blo 960589 3755879 := bstep (se 1 (by rfl) ⟨2816909, by rfl⟩ : syracuseStep 3755879 = 5633819) B5633819
theorem B2052859 : Blo 960589 2052859 := bstep (se 1 (by rfl) ⟨1539644, by rfl⟩ : syracuseStep 2052859 = 3079289) B3079289
theorem B14046205 : Blo 960589 14046205 := bstep (se 3 (by rfl) ⟨2633663, by rfl⟩ : syracuseStep 14046205 = 5267327) B5267327
theorem B7296317 : Blo 960589 7296317 := bstep (se 3 (by rfl) ⟨1368059, by rfl⟩ : syracuseStep 7296317 = 2736119) B2736119
theorem B4872959 : Blo 960589 4872959 := bstep (se 1 (by rfl) ⟨3654719, by rfl⟩ : syracuseStep 4872959 = 7309439) B7309439
theorem B4873121 : Blo 960589 4873121 := bstep (se 2 (by rfl) ⟨1827420, by rfl⟩ : syracuseStep 4873121 = 3654841) B3654841
theorem B8215465 : Blo 960589 8215465 := bstep (se 2 (by rfl) ⟨3080799, by rfl⟩ : syracuseStep 8215465 = 6161599) B6161599
theorem B3661631 : Blo 960589 3661631 := bstep (se 1 (by rfl) ⟨2746223, by rfl⟩ : syracuseStep 3661631 = 5492447) B5492447
theorem B8216423 : Blo 960589 8216423 := bstep (se 1 (by rfl) ⟨6162317, by rfl⟩ : syracuseStep 8216423 = 12324635) B12324635
theorem B3858587 : Blo 960589 3858587 := bstep (se 1 (by rfl) ⟨2893940, by rfl⟩ : syracuseStep 3858587 = 5787881) B5787881
theorem B1827049 : Blo 960589 1827049 := bstep (se 2 (by rfl) ⟨685143, by rfl⟩ : syracuseStep 1827049 = 1370287) B1370287
theorem B5202463 : Blo 960589 5202463 := bstep (se 1 (by rfl) ⟨3901847, by rfl⟩ : syracuseStep 5202463 = 7803695) B7803695
theorem B4876361 : Blo 960589 4876361 := bstep (se 2 (by rfl) ⟨1828635, by rfl⟩ : syracuseStep 4876361 = 3657271) B3657271
theorem B2058463 : Blo 960589 2058463 := bstep (se 1 (by rfl) ⟨1543847, by rfl⟩ : syracuseStep 2058463 = 3087695) B3087695
theorem B27748655 : Blo 960589 27748655 := bstep (se 1 (by rfl) ⟨20811491, by rfl⟩ : syracuseStep 27748655 = 41622983) B41622983
theorem B6580649 : Blo 960589 6580649 := bstep (se 2 (by rfl) ⟨2467743, by rfl⟩ : syracuseStep 6580649 = 4935487) B4935487
theorem B1829881 : Blo 960589 1829881 := bstep (se 2 (by rfl) ⟨686205, by rfl⟩ : syracuseStep 1829881 = 1372411) B1372411
theorem B2223551 : Blo 960589 2223551 := bstep (se 1 (by rfl) ⟨1667663, by rfl⟩ : syracuseStep 2223551 = 3335327) B3335327
theorem B9235943 : Blo 960589 9235943 := bstep (se 1 (by rfl) ⟨6926957, by rfl⟩ : syracuseStep 9235943 = 13853915) B13853915
theorem B1831081 : Blo 960589 1831081 := bstep (se 2 (by rfl) ⟨686655, by rfl⟩ : syracuseStep 1831081 = 1373311) B1373311
theorem B3078431 : Blo 960589 3078431 := bstep (se 1 (by rfl) ⟨2308823, by rfl⟩ : syracuseStep 3078431 = 4617647) B4617647
theorem B3242591 : Blo 960589 3242591 := bstep (se 1 (by rfl) ⟨2431943, by rfl⟩ : syracuseStep 3242591 = 4863887) B4863887
theorem B3472159 : Blo 960589 3472159 := bstep (se 1 (by rfl) ⟨2604119, by rfl⟩ : syracuseStep 3472159 = 5208239) B5208239
theorem B2161529 : Blo 960589 2161529 := bstep (se 2 (by rfl) ⟨810573, by rfl⟩ : syracuseStep 2161529 = 1621147) B1621147
theorem B2161673 : Blo 960589 2161673 := bstep (se 2 (by rfl) ⟨810627, by rfl⟩ : syracuseStep 2161673 = 1621255) B1621255
theorem B7306523 : Blo 960589 7306523 := bstep (se 1 (by rfl) ⟨5479892, by rfl⟩ : syracuseStep 7306523 = 10959785) B10959785
theorem B4881707 : Blo 960589 4881707 := bstep (se 1 (by rfl) ⟨3661280, by rfl⟩ : syracuseStep 4881707 = 7322561) B7322561
theorem B3243995 : Blo 960589 3243995 := bstep (se 1 (by rfl) ⟨2432996, by rfl⟩ : syracuseStep 3243995 = 4865993) B4865993
theorem B1442075 : Blo 960589 1442075 := bstep (se 1 (by rfl) ⟨1081556, by rfl⟩ : syracuseStep 1442075 = 2163113) B2163113
theorem B5210767 : Blo 960589 5210767 := bstep (se 1 (by rfl) ⟨3908075, by rfl⟩ : syracuseStep 5210767 = 7816151) B7816151
theorem B2163419 : Blo 960589 2163419 := bstep (se 1 (by rfl) ⟨1622564, by rfl⟩ : syracuseStep 2163419 = 3245129) B3245129
theorem B1442537 : Blo 960589 1442537 := bstep (se 2 (by rfl) ⟨540951, by rfl⟩ : syracuseStep 1442537 = 1081903) B1081903
theorem B1082335 : Blo 960589 1082335 := bstep (se 1 (by rfl) ⟨811751, by rfl⟩ : syracuseStep 1082335 = 1623503) B1623503
theorem B2163689 : Blo 960589 2163689 := bstep (se 2 (by rfl) ⟨811383, by rfl⟩ : syracuseStep 2163689 = 1622767) B1622767
theorem B2163815 : Blo 960589 2163815 := bstep (se 1 (by rfl) ⟨1622861, by rfl⟩ : syracuseStep 2163815 = 3245723) B3245723
theorem B56362493 : Blo 960589 56362493 := bstep (se 3 (by rfl) ⟨10567967, by rfl⟩ : syracuseStep 56362493 = 21135935) B21135935
theorem B2164571 : Blo 960589 2164571 := bstep (se 1 (by rfl) ⟨1623428, by rfl⟩ : syracuseStep 2164571 = 3246857) B3246857
theorem B2164607 : Blo 960589 2164607 := bstep (se 1 (by rfl) ⟨1623455, by rfl⟩ : syracuseStep 2164607 = 3246911) B3246911
theorem B10946663 : Blo 960589 10946663 := bstep (se 1 (by rfl) ⟨8209997, by rfl⟩ : syracuseStep 10946663 = 16419995) B16419995
theorem B1444007 : Blo 960589 1444007 := bstep (se 1 (by rfl) ⟨1083005, by rfl⟩ : syracuseStep 1444007 = 2166011) B2166011
theorem B1444079 : Blo 960589 1444079 := bstep (se 1 (by rfl) ⟨1083059, by rfl⟩ : syracuseStep 1444079 = 2166119) B2166119
theorem B1444217 : Blo 960589 1444217 := bstep (se 2 (by rfl) ⟨541581, by rfl⟩ : syracuseStep 1444217 = 1083163) B1083163
theorem B8785907 : Blo 960589 8785907 := bstep (se 1 (by rfl) ⟨6589430, by rfl⟩ : syracuseStep 8785907 = 13178861) B13178861
theorem B1445999 : Blo 960589 1445999 := bstep (se 1 (by rfl) ⟨1084499, by rfl⟩ : syracuseStep 1445999 = 2168999) B2168999
theorem B3248639 : Blo 960589 3248639 := bstep (se 1 (by rfl) ⟨2436479, by rfl⟩ : syracuseStep 3248639 = 4872959) B4872959
theorem B3248747 : Blo 960589 3248747 := bstep (se 1 (by rfl) ⟨2436560, by rfl⟩ : syracuseStep 3248747 = 4873121) B4873121
theorem B5477615 : Blo 960589 5477615 := bstep (se 1 (by rfl) ⟨4108211, by rfl⟩ : syracuseStep 5477615 = 8216423) B8216423
theorem B10983113 : Blo 960589 10983113 := bstep (se 2 (by rfl) ⟨4118667, by rfl⟩ : syracuseStep 10983113 = 8237335) B8237335
theorem B2169107 : Blo 960589 2169107 := bstep (se 1 (by rfl) ⟨1626830, by rfl⟩ : syracuseStep 2169107 = 3253661) B3253661
theorem B3250907 : Blo 960589 3250907 := bstep (se 1 (by rfl) ⟨2438180, by rfl⟩ : syracuseStep 3250907 = 4876361) B4876361
theorem B760552739 : Blo 960589 760552739 := bstep (se 1 (by rfl) ⟨570414554, by rfl⟩ : syracuseStep 760552739 = 1140829109) B1140829109
theorem B13378213 : Blo 960589 13378213 := bstep (se 4 (by rfl) ⟨1254207, by rfl⟩ : syracuseStep 13378213 = 2508415) B2508415
theorem B4629545 : Blo 960589 4629545 := bstep (se 2 (by rfl) ⟨1736079, by rfl⟩ : syracuseStep 4629545 = 3472159) B3472159
theorem B10953953 : Blo 960589 10953953 := bstep (se 2 (by rfl) ⟨4107732, by rfl⟩ : syracuseStep 10953953 = 8215465) B8215465
theorem B3254471 : Blo 960589 3254471 := bstep (se 1 (by rfl) ⟨2440853, by rfl⟩ : syracuseStep 3254471 = 4881707) B4881707
theorem B2436065 : Blo 960589 2436065 := bstep (se 2 (by rfl) ⟨913524, by rfl⟩ : syracuseStep 2436065 = 1827049) B1827049
theorem B4107905 : Blo 960589 4107905 := bstep (se 2 (by rfl) ⟨1540464, by rfl⟩ : syracuseStep 4107905 = 3080929) B3080929
theorem B962471 : Blo 960589 962471 := bstep (se 1 (by rfl) ⟨721853, by rfl⟩ : syracuseStep 962471 = 1443707) B1443707
theorem B962879 : Blo 960589 962879 := bstep (se 1 (by rfl) ⟨722159, by rfl⟩ : syracuseStep 962879 = 1444319) B1444319
theorem B963551 : Blo 960589 963551 := bstep (se 1 (by rfl) ⟨722663, by rfl⟩ : syracuseStep 963551 = 1445327) B1445327
theorem B2438171 : Blo 960589 2438171 := bstep (se 1 (by rfl) ⟨1828628, by rfl⟩ : syracuseStep 2438171 = 3657257) B3657257
theorem B16692263 : Blo 960589 16692263 := bstep (se 1 (by rfl) ⟨12519197, by rfl⟩ : syracuseStep 16692263 = 25038395) B25038395
theorem B963711 : Blo 960589 963711 := bstep (se 1 (by rfl) ⟨722783, by rfl⟩ : syracuseStep 963711 = 1445567) B1445567
theorem B963775 : Blo 960589 963775 := bstep (se 1 (by rfl) ⟨722831, by rfl⟩ : syracuseStep 963775 = 1445663) B1445663
theorem B2503919 : Blo 960589 2503919 := bstep (se 1 (by rfl) ⟨1877939, by rfl⟩ : syracuseStep 2503919 = 3755879) B3755879
theorem B964095 : Blo 960589 964095 := bstep (se 1 (by rfl) ⟨723071, by rfl⟩ : syracuseStep 964095 = 1446143) B1446143
theorem B964127 : Blo 960589 964127 := bstep (se 1 (by rfl) ⟨723095, by rfl⟩ : syracuseStep 964127 = 1446191) B1446191
theorem B964455 : Blo 960589 964455 := bstep (se 1 (by rfl) ⟨723341, by rfl⟩ : syracuseStep 964455 = 1446683) B1446683
theorem B4864211 : Blo 960589 4864211 := bstep (se 1 (by rfl) ⟨3648158, by rfl⟩ : syracuseStep 4864211 = 7296317) B7296317
theorem B158185709 : Blo 960589 158185709 := bstep (se 3 (by rfl) ⟨29659820, by rfl⟩ : syracuseStep 158185709 = 59319641) B59319641
theorem B2439841 : Blo 960589 2439841 := bstep (se 2 (by rfl) ⟨914940, by rfl⟩ : syracuseStep 2439841 = 1829881) B1829881
theorem B2441087 : Blo 960589 2441087 := bstep (se 1 (by rfl) ⟨1830815, by rfl⟩ : syracuseStep 2441087 = 3661631) B3661631
theorem B16433117 : Blo 960589 16433117 := bstep (se 3 (by rfl) ⟨3081209, by rfl⟩ : syracuseStep 16433117 = 6162419) B6162419
theorem B2572391 : Blo 960589 2572391 := bstep (se 1 (by rfl) ⟨1929293, by rfl⟩ : syracuseStep 2572391 = 3858587) B3858587
theorem B2441441 : Blo 960589 2441441 := bstep (se 2 (by rfl) ⟨915540, by rfl⟩ : syracuseStep 2441441 = 1831081) B1831081
theorem B10404449 : Blo 960589 10404449 := bstep (se 2 (by rfl) ⟨3901668, by rfl⟩ : syracuseStep 10404449 = 7803337) B7803337
theorem B2737111 : Blo 960589 2737111 := bstep (se 1 (by rfl) ⟨2052833, by rfl⟩ : syracuseStep 2737111 = 4105667) B4105667
theorem B2737145 : Blo 960589 2737145 := bstep (se 2 (by rfl) ⟨1026429, by rfl⟩ : syracuseStep 2737145 = 2052859) B2052859
theorem B17548397 : Blo 960589 17548397 := bstep (se 3 (by rfl) ⟨3290324, by rfl⟩ : syracuseStep 17548397 = 6580649) B6580649
theorem B1623199 : Blo 960589 1623199 := bstep (se 1 (by rfl) ⟨1217399, by rfl⟩ : syracuseStep 1623199 = 2434799) B2434799
theorem B18728273 : Blo 960589 18728273 := bstep (se 2 (by rfl) ⟨7023102, by rfl⟩ : syracuseStep 18728273 = 14046205) B14046205
theorem B18499103 : Blo 960589 18499103 := bstep (se 1 (by rfl) ⟨13874327, by rfl⟩ : syracuseStep 18499103 = 27748655) B27748655
theorem B2052287 : Blo 960589 2052287 := bstep (se 1 (by rfl) ⟨1539215, by rfl⟩ : syracuseStep 2052287 = 3078431) B3078431
theorem B4871015 : Blo 960589 4871015 := bstep (se 1 (by rfl) ⟨3653261, by rfl⟩ : syracuseStep 4871015 = 7306523) B7306523
theorem B6936617 : Blo 960589 6936617 := bstep (se 2 (by rfl) ⟨2601231, by rfl⟩ : syracuseStep 6936617 = 5202463) B5202463
theorem B19782083 : Blo 960589 19782083 := bstep (se 1 (by rfl) ⟨14836562, by rfl⟩ : syracuseStep 19782083 = 29673125) B29673125
theorem B2744617 : Blo 960589 2744617 := bstep (se 2 (by rfl) ⟨1029231, by rfl⟩ : syracuseStep 2744617 = 2058463) B2058463
theorem B4812479 : Blo 960589 4812479 := bstep (se 1 (by rfl) ⟨3609359, by rfl⟩ : syracuseStep 4812479 = 7218719) B7218719
theorem B6157295 : Blo 960589 6157295 := bstep (se 1 (by rfl) ⟨4617971, by rfl⟩ : syracuseStep 6157295 = 9235943) B9235943
theorem B5929469 : Blo 960589 5929469 := bstep (se 3 (by rfl) ⟨1111775, by rfl⟩ : syracuseStep 5929469 = 2223551) B2223551
theorem B2161727 : Blo 960589 2161727 := bstep (se 1 (by rfl) ⟨1621295, by rfl⟩ : syracuseStep 2161727 = 3242591) B3242591
theorem B1441019 : Blo 960589 1441019 := bstep (se 1 (by rfl) ⟨1080764, by rfl⟩ : syracuseStep 1441019 = 2161529) B2161529
theorem B1441115 : Blo 960589 1441115 := bstep (se 1 (by rfl) ⟨1080836, by rfl⟩ : syracuseStep 1441115 = 2161673) B2161673
theorem B2162663 : Blo 960589 2162663 := bstep (se 1 (by rfl) ⟨1621997, by rfl⟩ : syracuseStep 2162663 = 3243995) B3243995
theorem B1442279 : Blo 960589 1442279 := bstep (se 1 (by rfl) ⟨1081709, by rfl⟩ : syracuseStep 1442279 = 2163419) B2163419
theorem B1442459 : Blo 960589 1442459 := bstep (se 1 (by rfl) ⟨1081844, by rfl⟩ : syracuseStep 1442459 = 2163689) B2163689
theorem B1442543 : Blo 960589 1442543 := bstep (se 1 (by rfl) ⟨1081907, by rfl⟩ : syracuseStep 1442543 = 2163815) B2163815
theorem B11698931 : Blo 960589 11698931 := bstep (se 1 (by rfl) ⟨8774198, by rfl⟩ : syracuseStep 11698931 = 17548397) B17548397
theorem B6947689 : Blo 960589 6947689 := bstep (se 2 (by rfl) ⟨2605383, by rfl⟩ : syracuseStep 6947689 = 5210767) B5210767
theorem B12485515 : Blo 960589 12485515 := bstep (se 1 (by rfl) ⟨9364136, by rfl⟩ : syracuseStep 12485515 = 18728273) B18728273
theorem B1443047 : Blo 960589 1443047 := bstep (se 1 (by rfl) ⟨1082285, by rfl⟩ : syracuseStep 1443047 = 2164571) B2164571
theorem B1443071 : Blo 960589 1443071 := bstep (se 1 (by rfl) ⟨1082303, by rfl⟩ : syracuseStep 1443071 = 2164607) B2164607
theorem B1443113 : Blo 960589 1443113 := bstep (se 2 (by rfl) ⟨541167, by rfl⟩ : syracuseStep 1443113 = 1082335) B1082335
theorem B2164265 : Blo 960589 2164265 := bstep (se 2 (by rfl) ⟨811599, by rfl⟩ : syracuseStep 2164265 = 1623199) B1623199
theorem B2165759 : Blo 960589 2165759 := bstep (se 1 (by rfl) ⟨1624319, by rfl⟩ : syracuseStep 2165759 = 3248639) B3248639
theorem B2165831 : Blo 960589 2165831 := bstep (se 1 (by rfl) ⟨1624373, by rfl⟩ : syracuseStep 2165831 = 3248747) B3248747
theorem B3247343 : Blo 960589 3247343 := bstep (se 1 (by rfl) ⟨2435507, by rfl⟩ : syracuseStep 3247343 = 4871015) B4871015
theorem B1446071 : Blo 960589 1446071 := bstep (se 1 (by rfl) ⟨1084553, by rfl⟩ : syracuseStep 1446071 = 2169107) B2169107
theorem B2167271 : Blo 960589 2167271 := bstep (se 1 (by rfl) ⟨1625453, by rfl⟩ : syracuseStep 2167271 = 3250907) B3250907
theorem B3086363 : Blo 960589 3086363 := bstep (se 1 (by rfl) ⟨2314772, by rfl⟩ : syracuseStep 3086363 = 4629545) B4629545
theorem B2169647 : Blo 960589 2169647 := bstep (se 1 (by rfl) ⟨1627235, by rfl⟩ : syracuseStep 2169647 = 3254471) B3254471
theorem B4104863 : Blo 960589 4104863 := bstep (se 1 (by rfl) ⟨3078647, by rfl⟩ : syracuseStep 4104863 = 6157295) B6157295
theorem B3253121 : Blo 960589 3253121 := bstep (se 2 (by rfl) ⟨1219920, by rfl⟩ : syracuseStep 3253121 = 2439841) B2439841
theorem B105457139 : Blo 960589 105457139 := bstep (se 1 (by rfl) ⟨79092854, by rfl⟩ : syracuseStep 105457139 = 158185709) B158185709
theorem B960679 : Blo 960589 960679 := bstep (se 1 (by rfl) ⟨720509, by rfl⟩ : syracuseStep 960679 = 1441019) B1441019
theorem B960743 : Blo 960589 960743 := bstep (se 1 (by rfl) ⟨720557, by rfl⟩ : syracuseStep 960743 = 1441115) B1441115
theorem B10955411 : Blo 960589 10955411 := bstep (se 1 (by rfl) ⟨8216558, by rfl⟩ : syracuseStep 10955411 = 16433117) B16433117
theorem B1714927 : Blo 960589 1714927 := bstep (se 1 (by rfl) ⟨1286195, by rfl⟩ : syracuseStep 1714927 = 2572391) B2572391
theorem B961383 : Blo 960589 961383 := bstep (se 1 (by rfl) ⟨721037, by rfl⟩ : syracuseStep 961383 = 1442075) B1442075
theorem B961691 : Blo 960589 961691 := bstep (se 1 (by rfl) ⟨721268, by rfl⟩ : syracuseStep 961691 = 1442537) B1442537
theorem B17837617 : Blo 960589 17837617 := bstep (se 2 (by rfl) ⟨6689106, by rfl⟩ : syracuseStep 17837617 = 13378213) B13378213
theorem B12332735 : Blo 960589 12332735 := bstep (se 1 (by rfl) ⟨9249551, by rfl⟩ : syracuseStep 12332735 = 18499103) B18499103
theorem B3649481 : Blo 960589 3649481 := bstep (se 2 (by rfl) ⟨1368555, by rfl⟩ : syracuseStep 3649481 = 2737111) B2737111
theorem B962671 : Blo 960589 962671 := bstep (se 1 (by rfl) ⟨722003, by rfl⟩ : syracuseStep 962671 = 1444007) B1444007
theorem B962719 : Blo 960589 962719 := bstep (se 1 (by rfl) ⟨722039, by rfl⟩ : syracuseStep 962719 = 1444079) B1444079
theorem B962811 : Blo 960589 962811 := bstep (se 1 (by rfl) ⟨722108, by rfl⟩ : syracuseStep 962811 = 1444217) B1444217
theorem B963999 : Blo 960589 963999 := bstep (se 1 (by rfl) ⟨722999, by rfl⟩ : syracuseStep 963999 = 1445999) B1445999
theorem B3651743 : Blo 960589 3651743 := bstep (se 1 (by rfl) ⟨2738807, by rfl⟩ : syracuseStep 3651743 = 5477615) B5477615
theorem B7322075 : Blo 960589 7322075 := bstep (se 1 (by rfl) ⟨5491556, by rfl⟩ : syracuseStep 7322075 = 10983113) B10983113
theorem B13188055 : Blo 960589 13188055 := bstep (se 1 (by rfl) ⟨9891041, by rfl⟩ : syracuseStep 13188055 = 19782083) B19782083
theorem B507035159 : Blo 960589 507035159 := bstep (se 1 (by rfl) ⟨380276369, by rfl⟩ : syracuseStep 507035159 = 760552739) B760552739
theorem B18497645 : Blo 960589 18497645 := bstep (se 3 (by rfl) ⟨3468308, by rfl⟩ : syracuseStep 18497645 = 6936617) B6936617
theorem B1624043 : Blo 960589 1624043 := bstep (se 1 (by rfl) ⟨1218032, by rfl⟩ : syracuseStep 1624043 = 2436065) B2436065
theorem B2738603 : Blo 960589 2738603 := bstep (se 1 (by rfl) ⟨2053952, by rfl⟩ : syracuseStep 2738603 = 4107905) B4107905
theorem B1625447 : Blo 960589 1625447 := bstep (se 1 (by rfl) ⟨1219085, by rfl⟩ : syracuseStep 1625447 = 2438171) B2438171
theorem B11128175 : Blo 960589 11128175 := bstep (se 1 (by rfl) ⟨8346131, by rfl⟩ : syracuseStep 11128175 = 16692263) B16692263
theorem B3952979 : Blo 960589 3952979 := bstep (se 1 (by rfl) ⟨2964734, by rfl⟩ : syracuseStep 3952979 = 5929469) B5929469
theorem B1627391 : Blo 960589 1627391 := bstep (se 1 (by rfl) ⟨1220543, by rfl⟩ : syracuseStep 1627391 = 2441087) B2441087
theorem B1627627 : Blo 960589 1627627 := bstep (se 1 (by rfl) ⟨1220720, by rfl⟩ : syracuseStep 1627627 = 2441441) B2441441
theorem B3659489 : Blo 960589 3659489 := bstep (se 2 (by rfl) ⟨1372308, by rfl⟩ : syracuseStep 3659489 = 2744617) B2744617
theorem B6936299 : Blo 960589 6936299 := bstep (se 1 (by rfl) ⟨5202224, by rfl⟩ : syracuseStep 6936299 = 10404449) B10404449
theorem B1824763 : Blo 960589 1824763 := bstep (se 1 (by rfl) ⟨1368572, by rfl⟩ : syracuseStep 1824763 = 2737145) B2737145
theorem B7297775 : Blo 960589 7297775 := bstep (se 1 (by rfl) ⟨5473331, by rfl⟩ : syracuseStep 7297775 = 10946663) B10946663
theorem B5857271 : Blo 960589 5857271 := bstep (se 1 (by rfl) ⟨4392953, by rfl⟩ : syracuseStep 5857271 = 8785907) B8785907
theorem B1368191 : Blo 960589 1368191 := bstep (se 1 (by rfl) ⟨1026143, by rfl⟩ : syracuseStep 1368191 = 2052287) B2052287
theorem B150299981 : Blo 960589 150299981 := bstep (se 3 (by rfl) ⟨28181246, by rfl⟩ : syracuseStep 150299981 = 56362493) B56362493
theorem B7302635 : Blo 960589 7302635 := bstep (se 1 (by rfl) ⟨5476976, by rfl⟩ : syracuseStep 7302635 = 10953953) B10953953
theorem B3208319 : Blo 960589 3208319 := bstep (se 1 (by rfl) ⟨2406239, by rfl⟩ : syracuseStep 3208319 = 4812479) B4812479
theorem B1669279 : Blo 960589 1669279 := bstep (se 1 (by rfl) ⟨1251959, by rfl⟩ : syracuseStep 1669279 = 2503919) B2503919
theorem B3242807 : Blo 960589 3242807 := bstep (se 1 (by rfl) ⟨2432105, by rfl⟩ : syracuseStep 3242807 = 4864211) B4864211
theorem B1441151 : Blo 960589 1441151 := bstep (se 1 (by rfl) ⟨1080863, by rfl⟩ : syracuseStep 1441151 = 2161727) B2161727
theorem B1441775 : Blo 960589 1441775 := bstep (se 1 (by rfl) ⟨1081331, by rfl⟩ : syracuseStep 1441775 = 2162663) B2162663
theorem B7799287 : Blo 960589 7799287 := bstep (se 1 (by rfl) ⟨5849465, by rfl⟩ : syracuseStep 7799287 = 11698931) B11698931
theorem B1442843 : Blo 960589 1442843 := bstep (se 1 (by rfl) ⟨1082132, by rfl⟩ : syracuseStep 1442843 = 2164265) B2164265
theorem B16647353 : Blo 960589 16647353 := bstep (se 2 (by rfl) ⟨6242757, by rfl⟩ : syracuseStep 16647353 = 12485515) B12485515
theorem B1082695 : Blo 960589 1082695 := bstep (se 1 (by rfl) ⟨812021, by rfl⟩ : syracuseStep 1082695 = 1624043) B1624043
theorem B1443839 : Blo 960589 1443839 := bstep (se 1 (by rfl) ⟨1082879, by rfl⟩ : syracuseStep 1443839 = 2165759) B2165759
theorem B1443887 : Blo 960589 1443887 := bstep (se 1 (by rfl) ⟨1082915, by rfl⟩ : syracuseStep 1443887 = 2165831) B2165831
theorem B2164895 : Blo 960589 2164895 := bstep (se 1 (by rfl) ⟨1623671, by rfl⟩ : syracuseStep 2164895 = 3247343) B3247343
theorem B1083631 : Blo 960589 1083631 := bstep (se 1 (by rfl) ⟨812723, by rfl⟩ : syracuseStep 1083631 = 1625447) B1625447
theorem B142445141 : Blo 960589 142445141 := bstep (se 8 (by rfl) ⟨834639, by rfl⟩ : syracuseStep 142445141 = 1669279) B1669279
theorem B1444847 : Blo 960589 1444847 := bstep (se 1 (by rfl) ⟨1083635, by rfl⟩ : syracuseStep 1444847 = 2167271) B2167271
theorem B1084927 : Blo 960589 1084927 := bstep (se 1 (by rfl) ⟨813695, by rfl⟩ : syracuseStep 1084927 = 1627391) B1627391
theorem B4624199 : Blo 960589 4624199 := bstep (se 1 (by rfl) ⟨3468149, by rfl⟩ : syracuseStep 4624199 = 6936299) B6936299
theorem B1446431 : Blo 960589 1446431 := bstep (se 1 (by rfl) ⟨1084823, by rfl⟩ : syracuseStep 1446431 = 2169647) B2169647
theorem B3904847 : Blo 960589 3904847 := bstep (se 1 (by rfl) ⟨2928635, by rfl⟩ : syracuseStep 3904847 = 5857271) B5857271
theorem B2168747 : Blo 960589 2168747 := bstep (se 1 (by rfl) ⟨1626560, by rfl⟩ : syracuseStep 2168747 = 3253121) B3253121
theorem B2170169 : Blo 960589 2170169 := bstep (se 2 (by rfl) ⟨813813, by rfl⟩ : syracuseStep 2170169 = 1627627) B1627627
theorem B2432987 : Blo 960589 2432987 := bstep (se 1 (by rfl) ⟨1824740, by rfl⟩ : syracuseStep 2432987 = 3649481) B3649481
theorem B2433017 : Blo 960589 2433017 := bstep (se 2 (by rfl) ⟨912381, by rfl⟩ : syracuseStep 2433017 = 1824763) B1824763
theorem B2138879 : Blo 960589 2138879 := bstep (se 1 (by rfl) ⟨1604159, by rfl⟩ : syracuseStep 2138879 = 3208319) B3208319
theorem B2434495 : Blo 960589 2434495 := bstep (se 1 (by rfl) ⟨1825871, by rfl⟩ : syracuseStep 2434495 = 3651743) B3651743
theorem B960767 : Blo 960589 960767 := bstep (se 1 (by rfl) ⟨720575, by rfl⟩ : syracuseStep 960767 = 1441151) B1441151
theorem B961183 : Blo 960589 961183 := bstep (se 1 (by rfl) ⟨720887, by rfl⟩ : syracuseStep 961183 = 1441775) B1441775
theorem B12331763 : Blo 960589 12331763 := bstep (se 1 (by rfl) ⟨9248822, by rfl⟩ : syracuseStep 12331763 = 18497645) B18497645
theorem B961519 : Blo 960589 961519 := bstep (se 1 (by rfl) ⟨721139, by rfl⟩ : syracuseStep 961519 = 1442279) B1442279
theorem B3648509 : Blo 960589 3648509 := bstep (se 3 (by rfl) ⟨684095, by rfl⟩ : syracuseStep 3648509 = 1368191) B1368191
theorem B961639 : Blo 960589 961639 := bstep (se 1 (by rfl) ⟨721229, by rfl⟩ : syracuseStep 961639 = 1442459) B1442459
theorem B961695 : Blo 960589 961695 := bstep (se 1 (by rfl) ⟨721271, by rfl⟩ : syracuseStep 961695 = 1442543) B1442543
theorem B962031 : Blo 960589 962031 := bstep (se 1 (by rfl) ⟨721523, by rfl⟩ : syracuseStep 962031 = 1443047) B1443047
theorem B962047 : Blo 960589 962047 := bstep (se 1 (by rfl) ⟨721535, by rfl⟩ : syracuseStep 962047 = 1443071) B1443071
theorem B962075 : Blo 960589 962075 := bstep (se 1 (by rfl) ⟨721556, by rfl⟩ : syracuseStep 962075 = 1443113) B1443113
theorem B7418783 : Blo 960589 7418783 := bstep (se 1 (by rfl) ⟨5564087, by rfl⟩ : syracuseStep 7418783 = 11128175) B11128175
theorem B964047 : Blo 960589 964047 := bstep (se 1 (by rfl) ⟨723035, by rfl⟩ : syracuseStep 964047 = 1446071) B1446071
theorem B2635319 : Blo 960589 2635319 := bstep (se 1 (by rfl) ⟨1976489, by rfl⟩ : syracuseStep 2635319 = 3952979) B3952979
theorem B2439659 : Blo 960589 2439659 := bstep (se 1 (by rfl) ⟨1829744, by rfl⟩ : syracuseStep 2439659 = 3659489) B3659489
theorem B4865183 : Blo 960589 4865183 := bstep (se 1 (by rfl) ⟨3648887, by rfl⟩ : syracuseStep 4865183 = 7297775) B7297775
theorem B2736575 : Blo 960589 2736575 := bstep (se 1 (by rfl) ⟨2052431, by rfl⟩ : syracuseStep 2736575 = 4104863) B4104863
theorem B70304759 : Blo 960589 70304759 := bstep (se 1 (by rfl) ⟨52728569, by rfl⟩ : syracuseStep 70304759 = 105457139) B105457139
theorem B4868423 : Blo 960589 4868423 := bstep (se 1 (by rfl) ⟨3651317, by rfl⟩ : syracuseStep 4868423 = 7302635) B7302635
theorem B17584073 : Blo 960589 17584073 := bstep (se 2 (by rfl) ⟨6594027, by rfl⟩ : syracuseStep 17584073 = 13188055) B13188055
theorem B338023439 : Blo 960589 338023439 := bstep (se 1 (by rfl) ⟨253517579, by rfl⟩ : syracuseStep 338023439 = 507035159) B507035159
theorem B9263585 : Blo 960589 9263585 := bstep (se 2 (by rfl) ⟨3473844, by rfl⟩ : syracuseStep 9263585 = 6947689) B6947689
theorem B1825735 : Blo 960589 1825735 := bstep (se 1 (by rfl) ⟨1369301, by rfl⟩ : syracuseStep 1825735 = 2738603) B2738603
theorem B2286569 : Blo 960589 2286569 := bstep (se 2 (by rfl) ⟨857463, by rfl⟩ : syracuseStep 2286569 = 1714927) B1714927
theorem B2057575 : Blo 960589 2057575 := bstep (se 1 (by rfl) ⟨1543181, by rfl⟩ : syracuseStep 2057575 = 3086363) B3086363
theorem B23783489 : Blo 960589 23783489 := bstep (se 2 (by rfl) ⟨8918808, by rfl⟩ : syracuseStep 23783489 = 17837617) B17837617
theorem B100199987 : Blo 960589 100199987 := bstep (se 1 (by rfl) ⟨75149990, by rfl⟩ : syracuseStep 100199987 = 150299981) B150299981
theorem B7303607 : Blo 960589 7303607 := bstep (se 1 (by rfl) ⟨5477705, by rfl⟩ : syracuseStep 7303607 = 10955411) B10955411
theorem B8221823 : Blo 960589 8221823 := bstep (se 1 (by rfl) ⟨6166367, by rfl⟩ : syracuseStep 8221823 = 12332735) B12332735
theorem B4881383 : Blo 960589 4881383 := bstep (se 1 (by rfl) ⟨3661037, by rfl⟩ : syracuseStep 4881383 = 7322075) B7322075
theorem B2161871 : Blo 960589 2161871 := bstep (se 1 (by rfl) ⟨1621403, by rfl⟩ : syracuseStep 2161871 = 3242807) B3242807
theorem B1443263 : Blo 960589 1443263 := bstep (se 1 (by rfl) ⟨1082447, by rfl⟩ : syracuseStep 1443263 = 2164895) B2164895
theorem B3245615 : Blo 960589 3245615 := bstep (se 1 (by rfl) ⟨2434211, by rfl⟩ : syracuseStep 3245615 = 4868423) B4868423
theorem B94963427 : Blo 960589 94963427 := bstep (se 1 (by rfl) ⟨71222570, by rfl⟩ : syracuseStep 94963427 = 142445141) B142445141
theorem B1443593 : Blo 960589 1443593 := bstep (se 2 (by rfl) ⟨541347, by rfl⟩ : syracuseStep 1443593 = 1082695) B1082695
theorem B3245993 : Blo 960589 3245993 := bstep (se 2 (by rfl) ⟨1217247, by rfl⟩ : syracuseStep 3245993 = 2434495) B2434495
theorem B3082799 : Blo 960589 3082799 := bstep (se 1 (by rfl) ⟨2312099, by rfl⟩ : syracuseStep 3082799 = 4624199) B4624199
theorem B6097517 : Blo 960589 6097517 := bstep (se 3 (by rfl) ⟨1143284, by rfl⟩ : syracuseStep 6097517 = 2286569) B2286569
theorem B1444841 : Blo 960589 1444841 := bstep (se 2 (by rfl) ⟨541815, by rfl⟩ : syracuseStep 1444841 = 1083631) B1083631
theorem B225348959 : Blo 960589 225348959 := bstep (se 1 (by rfl) ⟨169011719, by rfl⟩ : syracuseStep 225348959 = 338023439) B338023439
theorem B1445831 : Blo 960589 1445831 := bstep (se 1 (by rfl) ⟨1084373, by rfl⟩ : syracuseStep 1445831 = 2168747) B2168747
theorem B1446569 : Blo 960589 1446569 := bstep (se 2 (by rfl) ⟨542463, by rfl⟩ : syracuseStep 1446569 = 1084927) B1084927
theorem B1446779 : Blo 960589 1446779 := bstep (se 1 (by rfl) ⟨1085084, by rfl⟩ : syracuseStep 1446779 = 2170169) B2170169
theorem B2432339 : Blo 960589 2432339 := bstep (se 1 (by rfl) ⟨1824254, by rfl⟩ : syracuseStep 2432339 = 3648509) B3648509
theorem B5481215 : Blo 960589 5481215 := bstep (se 1 (by rfl) ⟨4110911, by rfl⟩ : syracuseStep 5481215 = 8221823) B8221823
theorem B2434313 : Blo 960589 2434313 := bstep (se 2 (by rfl) ⟨912867, by rfl⟩ : syracuseStep 2434313 = 1825735) B1825735
theorem B3254255 : Blo 960589 3254255 := bstep (se 1 (by rfl) ⟨2440691, by rfl⟩ : syracuseStep 3254255 = 4881383) B4881383
theorem B10399049 : Blo 960589 10399049 := bstep (se 2 (by rfl) ⟨3899643, by rfl⟩ : syracuseStep 10399049 = 7799287) B7799287
theorem B46869839 : Blo 960589 46869839 := bstep (se 1 (by rfl) ⟨35152379, by rfl⟩ : syracuseStep 46869839 = 70304759) B70304759
theorem B961895 : Blo 960589 961895 := bstep (se 1 (by rfl) ⟨721421, by rfl⟩ : syracuseStep 961895 = 1442843) B1442843
theorem B962559 : Blo 960589 962559 := bstep (se 1 (by rfl) ⟨721919, by rfl⟩ : syracuseStep 962559 = 1443839) B1443839
theorem B962591 : Blo 960589 962591 := bstep (se 1 (by rfl) ⟨721943, by rfl⟩ : syracuseStep 962591 = 1443887) B1443887
theorem B963231 : Blo 960589 963231 := bstep (se 1 (by rfl) ⟨722423, by rfl⟩ : syracuseStep 963231 = 1444847) B1444847
theorem B964287 : Blo 960589 964287 := bstep (se 1 (by rfl) ⟨723215, by rfl⟩ : syracuseStep 964287 = 1446431) B1446431
theorem B2603231 : Blo 960589 2603231 := bstep (se 1 (by rfl) ⟨1952423, by rfl⟩ : syracuseStep 2603231 = 3904847) B3904847
theorem B6175723 : Blo 960589 6175723 := bstep (se 1 (by rfl) ⟨4631792, by rfl⟩ : syracuseStep 6175723 = 9263585) B9263585
theorem B1621991 : Blo 960589 1621991 := bstep (se 1 (by rfl) ⟨1216493, by rfl⟩ : syracuseStep 1621991 = 2432987) B2432987
theorem B1622011 : Blo 960589 1622011 := bstep (se 1 (by rfl) ⟨1216508, by rfl⟩ : syracuseStep 1622011 = 2433017) B2433017
theorem B1425919 : Blo 960589 1425919 := bstep (se 1 (by rfl) ⟨1069439, by rfl⟩ : syracuseStep 1425919 = 2138879) B2138879
theorem B66799991 : Blo 960589 66799991 := bstep (se 1 (by rfl) ⟨50099993, by rfl⟩ : syracuseStep 66799991 = 100199987) B100199987
theorem B4869071 : Blo 960589 4869071 := bstep (se 1 (by rfl) ⟨3651803, by rfl⟩ : syracuseStep 4869071 = 7303607) B7303607
theorem B1756879 : Blo 960589 1756879 := bstep (se 1 (by rfl) ⟨1317659, by rfl⟩ : syracuseStep 1756879 = 2635319) B2635319
theorem B1626439 : Blo 960589 1626439 := bstep (se 1 (by rfl) ⟨1219829, by rfl⟩ : syracuseStep 1626439 = 2439659) B2439659
theorem B1824383 : Blo 960589 1824383 := bstep (se 1 (by rfl) ⟨1368287, by rfl⟩ : syracuseStep 1824383 = 2736575) B2736575
theorem B11098235 : Blo 960589 11098235 := bstep (se 1 (by rfl) ⟨8323676, by rfl⟩ : syracuseStep 11098235 = 16647353) B16647353
theorem B2743433 : Blo 960589 2743433 := bstep (se 2 (by rfl) ⟨1028787, by rfl⟩ : syracuseStep 2743433 = 2057575) B2057575
theorem B11722715 : Blo 960589 11722715 := bstep (se 1 (by rfl) ⟨8792036, by rfl⟩ : syracuseStep 11722715 = 17584073) B17584073
theorem B15855659 : Blo 960589 15855659 := bstep (se 1 (by rfl) ⟨11891744, by rfl⟩ : syracuseStep 15855659 = 23783489) B23783489
theorem B8221175 : Blo 960589 8221175 := bstep (se 1 (by rfl) ⟨6165881, by rfl⟩ : syracuseStep 8221175 = 12331763) B12331763
theorem B4945855 : Blo 960589 4945855 := bstep (se 1 (by rfl) ⟨3709391, by rfl⟩ : syracuseStep 4945855 = 7418783) B7418783
theorem B3243455 : Blo 960589 3243455 := bstep (se 1 (by rfl) ⟨2432591, by rfl⟩ : syracuseStep 3243455 = 4865183) B4865183
theorem B1441247 : Blo 960589 1441247 := bstep (se 1 (by rfl) ⟨1080935, by rfl⟩ : syracuseStep 1441247 = 2161871) B2161871
theorem B1901225 : Blo 960589 1901225 := bstep (se 2 (by rfl) ⟨712959, by rfl⟩ : syracuseStep 1901225 = 1425919) B1425919
theorem B2163743 : Blo 960589 2163743 := bstep (se 1 (by rfl) ⟨1622807, by rfl⟩ : syracuseStep 2163743 = 3245615) B3245615
theorem B63308951 : Blo 960589 63308951 := bstep (se 1 (by rfl) ⟨47481713, by rfl⟩ : syracuseStep 63308951 = 94963427) B94963427
theorem B2163995 : Blo 960589 2163995 := bstep (se 1 (by rfl) ⟨1622996, by rfl⟩ : syracuseStep 2163995 = 3245993) B3245993
theorem B44533327 : Blo 960589 44533327 := bstep (se 1 (by rfl) ⟨33399995, by rfl⟩ : syracuseStep 44533327 = 66799991) B66799991
theorem B4065011 : Blo 960589 4065011 := bstep (se 1 (by rfl) ⟨3048758, by rfl⟩ : syracuseStep 4065011 = 6097517) B6097517
theorem B3246047 : Blo 960589 3246047 := bstep (se 1 (by rfl) ⟨2434535, by rfl⟩ : syracuseStep 3246047 = 4869071) B4869071
theorem B2168585 : Blo 960589 2168585 := bstep (se 2 (by rfl) ⟨813219, by rfl⟩ : syracuseStep 2168585 = 1626439) B1626439
theorem B2169503 : Blo 960589 2169503 := bstep (se 1 (by rfl) ⟨1627127, by rfl⟩ : syracuseStep 2169503 = 3254255) B3254255
theorem B6594473 : Blo 960589 6594473 := bstep (se 2 (by rfl) ⟨2472927, by rfl⟩ : syracuseStep 6594473 = 4945855) B4945855
theorem B5480783 : Blo 960589 5480783 := bstep (se 1 (by rfl) ⟨4110587, by rfl⟩ : syracuseStep 5480783 = 8221175) B8221175
theorem B8234297 : Blo 960589 8234297 := bstep (se 2 (by rfl) ⟨3087861, by rfl⟩ : syracuseStep 8234297 = 6175723) B6175723
theorem B960831 : Blo 960589 960831 := bstep (se 1 (by rfl) ⟨720623, by rfl⟩ : syracuseStep 960831 = 1441247) B1441247
theorem B962175 : Blo 960589 962175 := bstep (se 1 (by rfl) ⟨721631, by rfl⟩ : syracuseStep 962175 = 1443263) B1443263
theorem B962395 : Blo 960589 962395 := bstep (se 1 (by rfl) ⟨721796, by rfl⟩ : syracuseStep 962395 = 1443593) B1443593
theorem B963227 : Blo 960589 963227 := bstep (se 1 (by rfl) ⟨722420, by rfl⟩ : syracuseStep 963227 = 1444841) B1444841
theorem B963887 : Blo 960589 963887 := bstep (se 1 (by rfl) ⟨722915, by rfl⟩ : syracuseStep 963887 = 1445831) B1445831
theorem B964379 : Blo 960589 964379 := bstep (se 1 (by rfl) ⟨723284, by rfl⟩ : syracuseStep 964379 = 1446569) B1446569
theorem B964519 : Blo 960589 964519 := bstep (se 1 (by rfl) ⟨723389, by rfl⟩ : syracuseStep 964519 = 1446779) B1446779
theorem B4865021 : Blo 960589 4865021 := bstep (se 3 (by rfl) ⟨912191, by rfl⟩ : syracuseStep 4865021 = 1824383) B1824383
theorem B1621559 : Blo 960589 1621559 := bstep (se 1 (by rfl) ⟨1216169, by rfl⟩ : syracuseStep 1621559 = 2432339) B2432339
theorem B7815143 : Blo 960589 7815143 := bstep (se 1 (by rfl) ⟨5861357, by rfl⟩ : syracuseStep 7815143 = 11722715) B11722715
theorem B3654143 : Blo 960589 3654143 := bstep (se 1 (by rfl) ⟨2740607, by rfl⟩ : syracuseStep 3654143 = 5481215) B5481215
theorem B1622875 : Blo 960589 1622875 := bstep (se 1 (by rfl) ⟨1217156, by rfl⟩ : syracuseStep 1622875 = 2434313) B2434313
theorem B6932699 : Blo 960589 6932699 := bstep (se 1 (by rfl) ⟨5199524, by rfl⟩ : syracuseStep 6932699 = 10399049) B10399049
theorem B31246559 : Blo 960589 31246559 := bstep (se 1 (by rfl) ⟨23434919, by rfl⟩ : syracuseStep 31246559 = 46869839) B46869839
theorem B10570439 : Blo 960589 10570439 := bstep (se 1 (by rfl) ⟨7927829, by rfl⟩ : syracuseStep 10570439 = 15855659) B15855659
theorem B150232639 : Blo 960589 150232639 := bstep (se 1 (by rfl) ⟨112674479, by rfl⟩ : syracuseStep 150232639 = 225348959) B225348959
theorem B7398823 : Blo 960589 7398823 := bstep (se 1 (by rfl) ⟨5549117, by rfl⟩ : syracuseStep 7398823 = 11098235) B11098235
theorem B37480085 : Blo 960589 37480085 := bstep (se 6 (by rfl) ⟨878439, by rfl⟩ : syracuseStep 37480085 = 1756879) B1756879
theorem B1828955 : Blo 960589 1828955 := bstep (se 1 (by rfl) ⟨1371716, by rfl⟩ : syracuseStep 1828955 = 2743433) B2743433
theorem B8220797 : Blo 960589 8220797 := bstep (se 3 (by rfl) ⟨1541399, by rfl⟩ : syracuseStep 8220797 = 3082799) B3082799
theorem B1735487 : Blo 960589 1735487 := bstep (se 1 (by rfl) ⟨1301615, by rfl⟩ : syracuseStep 1735487 = 2603231) B2603231
theorem B2162303 : Blo 960589 2162303 := bstep (se 1 (by rfl) ⟨1621727, by rfl⟩ : syracuseStep 2162303 = 3243455) B3243455
theorem B1081327 : Blo 960589 1081327 := bstep (se 1 (by rfl) ⟨810995, by rfl⟩ : syracuseStep 1081327 = 1621991) B1621991
theorem B2162681 : Blo 960589 2162681 := bstep (se 2 (by rfl) ⟨811005, by rfl⟩ : syracuseStep 2162681 = 1622011) B1622011
theorem B1442495 : Blo 960589 1442495 := bstep (se 1 (by rfl) ⟨1081871, by rfl⟩ : syracuseStep 1442495 = 2163743) B2163743
theorem B42205967 : Blo 960589 42205967 := bstep (se 1 (by rfl) ⟨31654475, by rfl⟩ : syracuseStep 42205967 = 63308951) B63308951
theorem B1442663 : Blo 960589 1442663 := bstep (se 1 (by rfl) ⟨1081997, by rfl⟩ : syracuseStep 1442663 = 2163995) B2163995
theorem B2163833 : Blo 960589 2163833 := bstep (se 2 (by rfl) ⟨811437, by rfl⟩ : syracuseStep 2163833 = 1622875) B1622875
theorem B2164031 : Blo 960589 2164031 := bstep (se 1 (by rfl) ⟨1623023, by rfl⟩ : syracuseStep 2164031 = 3246047) B3246047
theorem B4621799 : Blo 960589 4621799 := bstep (se 1 (by rfl) ⟨3466349, by rfl⟩ : syracuseStep 4621799 = 6932699) B6932699
theorem B7046959 : Blo 960589 7046959 := bstep (se 1 (by rfl) ⟨5285219, by rfl⟩ : syracuseStep 7046959 = 10570439) B10570439
theorem B9865097 : Blo 960589 9865097 := bstep (se 2 (by rfl) ⟨3699411, by rfl⟩ : syracuseStep 9865097 = 7398823) B7398823
theorem B59377769 : Blo 960589 59377769 := bstep (se 2 (by rfl) ⟨22266663, by rfl⟩ : syracuseStep 59377769 = 44533327) B44533327
theorem B1445723 : Blo 960589 1445723 := bstep (se 1 (by rfl) ⟨1084292, by rfl⟩ : syracuseStep 1445723 = 2168585) B2168585
theorem B1446335 : Blo 960589 1446335 := bstep (se 1 (by rfl) ⟨1084751, by rfl⟩ : syracuseStep 1446335 = 2169503) B2169503
theorem B4396315 : Blo 960589 4396315 := bstep (se 1 (by rfl) ⟨3297236, by rfl⟩ : syracuseStep 4396315 = 6594473) B6594473
theorem B1219303 : Blo 960589 1219303 := bstep (se 1 (by rfl) ⟨914477, by rfl⟩ : syracuseStep 1219303 = 1828955) B1828955
theorem B5480531 : Blo 960589 5480531 := bstep (se 1 (by rfl) ⟨4110398, by rfl⟩ : syracuseStep 5480531 = 8220797) B8220797
theorem B2436095 : Blo 960589 2436095 := bstep (se 1 (by rfl) ⟨1827071, by rfl⟩ : syracuseStep 2436095 = 3654143) B3654143
theorem B3653855 : Blo 960589 3653855 := bstep (se 1 (by rfl) ⟨2740391, by rfl⟩ : syracuseStep 3653855 = 5480783) B5480783
theorem B5489531 : Blo 960589 5489531 := bstep (se 1 (by rfl) ⟨4117148, by rfl⟩ : syracuseStep 5489531 = 8234297) B8234297
theorem B24986723 : Blo 960589 24986723 := bstep (se 1 (by rfl) ⟨18740042, by rfl⟩ : syracuseStep 24986723 = 37480085) B37480085
theorem B1267483 : Blo 960589 1267483 := bstep (se 1 (by rfl) ⟨950612, by rfl⟩ : syracuseStep 1267483 = 1901225) B1901225
theorem B2710007 : Blo 960589 2710007 := bstep (se 1 (by rfl) ⟨2032505, by rfl⟩ : syracuseStep 2710007 = 4065011) B4065011
theorem B20831039 : Blo 960589 20831039 := bstep (se 1 (by rfl) ⟨15623279, by rfl⟩ : syracuseStep 20831039 = 31246559) B31246559
theorem B18511861 : Blo 960589 18511861 := bstep (se 5 (by rfl) ⟨867743, by rfl⟩ : syracuseStep 18511861 = 1735487) B1735487
theorem B3243347 : Blo 960589 3243347 := bstep (se 1 (by rfl) ⟨2432510, by rfl⟩ : syracuseStep 3243347 = 4865021) B4865021
theorem B200310185 : Blo 960589 200310185 := bstep (se 2 (by rfl) ⟨75116319, by rfl⟩ : syracuseStep 200310185 = 150232639) B150232639
theorem B1081039 : Blo 960589 1081039 := bstep (se 1 (by rfl) ⟨810779, by rfl⟩ : syracuseStep 1081039 = 1621559) B1621559
theorem B1441535 : Blo 960589 1441535 := bstep (se 1 (by rfl) ⟨1081151, by rfl⟩ : syracuseStep 1441535 = 2162303) B2162303
theorem B1441769 : Blo 960589 1441769 := bstep (se 2 (by rfl) ⟨540663, by rfl⟩ : syracuseStep 1441769 = 1081327) B1081327
theorem B5210095 : Blo 960589 5210095 := bstep (se 1 (by rfl) ⟨3907571, by rfl⟩ : syracuseStep 5210095 = 7815143) B7815143
theorem B1441787 : Blo 960589 1441787 := bstep (se 1 (by rfl) ⟨1081340, by rfl⟩ : syracuseStep 1441787 = 2162681) B2162681
theorem B1442555 : Blo 960589 1442555 := bstep (se 1 (by rfl) ⟨1081916, by rfl⟩ : syracuseStep 1442555 = 2163833) B2163833
theorem B1442687 : Blo 960589 1442687 := bstep (se 1 (by rfl) ⟨1082015, by rfl⟩ : syracuseStep 1442687 = 2164031) B2164031
theorem B3081199 : Blo 960589 3081199 := bstep (se 1 (by rfl) ⟨2310899, by rfl⟩ : syracuseStep 3081199 = 4621799) B4621799
theorem B39585179 : Blo 960589 39585179 := bstep (se 1 (by rfl) ⟨29688884, by rfl⟩ : syracuseStep 39585179 = 59377769) B59377769
theorem B1806671 : Blo 960589 1806671 := bstep (se 1 (by rfl) ⟨1355003, by rfl⟩ : syracuseStep 1806671 = 2710007) B2710007
theorem B24682481 : Blo 960589 24682481 := bstep (se 2 (by rfl) ⟨9255930, by rfl⟩ : syracuseStep 24682481 = 18511861) B18511861
theorem B133540123 : Blo 960589 133540123 := bstep (se 1 (by rfl) ⟨100155092, by rfl⟩ : syracuseStep 133540123 = 200310185) B200310185
theorem B961023 : Blo 960589 961023 := bstep (se 1 (by rfl) ⟨720767, by rfl⟩ : syracuseStep 961023 = 1441535) B1441535
theorem B961179 : Blo 960589 961179 := bstep (se 1 (by rfl) ⟨720884, by rfl⟩ : syracuseStep 961179 = 1441769) B1441769
theorem B961191 : Blo 960589 961191 := bstep (se 1 (by rfl) ⟨720893, by rfl⟩ : syracuseStep 961191 = 1441787) B1441787
theorem B2435903 : Blo 960589 2435903 := bstep (se 1 (by rfl) ⟨1826927, by rfl⟩ : syracuseStep 2435903 = 3653855) B3653855
theorem B961663 : Blo 960589 961663 := bstep (se 1 (by rfl) ⟨721247, by rfl⟩ : syracuseStep 961663 = 1442495) B1442495
theorem B961775 : Blo 960589 961775 := bstep (se 1 (by rfl) ⟨721331, by rfl⟩ : syracuseStep 961775 = 1442663) B1442663
theorem B963815 : Blo 960589 963815 := bstep (se 1 (by rfl) ⟨722861, by rfl⟩ : syracuseStep 963815 = 1445723) B1445723
theorem B66631261 : Blo 960589 66631261 := bstep (se 3 (by rfl) ⟨12493361, by rfl⟩ : syracuseStep 66631261 = 24986723) B24986723
theorem B964223 : Blo 960589 964223 := bstep (se 1 (by rfl) ⟨723167, by rfl⟩ : syracuseStep 964223 = 1446335) B1446335
theorem B3653687 : Blo 960589 3653687 := bstep (se 1 (by rfl) ⟨2740265, by rfl⟩ : syracuseStep 3653687 = 5480531) B5480531
theorem B1624063 : Blo 960589 1624063 := bstep (se 1 (by rfl) ⟨1218047, by rfl⟩ : syracuseStep 1624063 = 2436095) B2436095
theorem B1689977 : Blo 960589 1689977 := bstep (se 2 (by rfl) ⟨633741, by rfl⟩ : syracuseStep 1689977 = 1267483) B1267483
theorem B1625737 : Blo 960589 1625737 := bstep (se 2 (by rfl) ⟨609651, by rfl⟩ : syracuseStep 1625737 = 1219303) B1219303
theorem B28137311 : Blo 960589 28137311 := bstep (se 1 (by rfl) ⟨21102983, by rfl⟩ : syracuseStep 28137311 = 42205967) B42205967
theorem B3659687 : Blo 960589 3659687 := bstep (se 1 (by rfl) ⟨2744765, by rfl⟩ : syracuseStep 3659687 = 5489531) B5489531
theorem B6576731 : Blo 960589 6576731 := bstep (se 1 (by rfl) ⟨4932548, by rfl⟩ : syracuseStep 6576731 = 9865097) B9865097
theorem B9395945 : Blo 960589 9395945 := bstep (se 2 (by rfl) ⟨3523479, by rfl⟩ : syracuseStep 9395945 = 7046959) B7046959
theorem B13887359 : Blo 960589 13887359 := bstep (se 1 (by rfl) ⟨10415519, by rfl⟩ : syracuseStep 13887359 = 20831039) B20831039
theorem B5861753 : Blo 960589 5861753 := bstep (se 2 (by rfl) ⟨2198157, by rfl⟩ : syracuseStep 5861753 = 4396315) B4396315
theorem B2162231 : Blo 960589 2162231 := bstep (se 1 (by rfl) ⟨1621673, by rfl⟩ : syracuseStep 2162231 = 3243347) B3243347
theorem B1441385 : Blo 960589 1441385 := bstep (se 2 (by rfl) ⟨540519, by rfl⟩ : syracuseStep 1441385 = 1081039) B1081039
theorem B6946793 : Blo 960589 6946793 := bstep (se 2 (by rfl) ⟨2605047, by rfl⟩ : syracuseStep 6946793 = 5210095) B5210095
theorem B4817789 : Blo 960589 4817789 := bstep (se 3 (by rfl) ⟨903335, by rfl⟩ : syracuseStep 4817789 = 1806671) B1806671
theorem B2165417 : Blo 960589 2165417 := bstep (se 2 (by rfl) ⟨812031, by rfl⟩ : syracuseStep 2165417 = 1624063) B1624063
theorem B2167649 : Blo 960589 2167649 := bstep (se 2 (by rfl) ⟨812868, by rfl⟩ : syracuseStep 2167649 = 1625737) B1625737
theorem B6263963 : Blo 960589 6263963 := bstep (se 1 (by rfl) ⟨4697972, by rfl⟩ : syracuseStep 6263963 = 9395945) B9395945
theorem B16454987 : Blo 960589 16454987 := bstep (se 1 (by rfl) ⟨12341240, by rfl⟩ : syracuseStep 16454987 = 24682481) B24682481
theorem B88841681 : Blo 960589 88841681 := bstep (se 2 (by rfl) ⟨33315630, by rfl⟩ : syracuseStep 88841681 = 66631261) B66631261
theorem B3907835 : Blo 960589 3907835 := bstep (se 1 (by rfl) ⟨2930876, by rfl⟩ : syracuseStep 3907835 = 5861753) B5861753
theorem B960923 : Blo 960589 960923 := bstep (se 1 (by rfl) ⟨720692, by rfl⟩ : syracuseStep 960923 = 1441385) B1441385
theorem B4631195 : Blo 960589 4631195 := bstep (se 1 (by rfl) ⟨3473396, by rfl⟩ : syracuseStep 4631195 = 6946793) B6946793
theorem B2435791 : Blo 960589 2435791 := bstep (se 1 (by rfl) ⟨1826843, by rfl⟩ : syracuseStep 2435791 = 3653687) B3653687
theorem B961703 : Blo 960589 961703 := bstep (se 1 (by rfl) ⟨721277, by rfl⟩ : syracuseStep 961703 = 1442555) B1442555
theorem B961791 : Blo 960589 961791 := bstep (se 1 (by rfl) ⟨721343, by rfl⟩ : syracuseStep 961791 = 1442687) B1442687
theorem B26390119 : Blo 960589 26390119 := bstep (se 1 (by rfl) ⟨19792589, by rfl⟩ : syracuseStep 26390119 = 39585179) B39585179
theorem B4108265 : Blo 960589 4108265 := bstep (se 2 (by rfl) ⟨1540599, by rfl⟩ : syracuseStep 4108265 = 3081199) B3081199
theorem B1126651 : Blo 960589 1126651 := bstep (se 1 (by rfl) ⟨844988, by rfl⟩ : syracuseStep 1126651 = 1689977) B1689977
theorem B18758207 : Blo 960589 18758207 := bstep (se 1 (by rfl) ⟨14068655, by rfl⟩ : syracuseStep 18758207 = 28137311) B28137311
theorem B2439791 : Blo 960589 2439791 := bstep (se 1 (by rfl) ⟨1829843, by rfl⟩ : syracuseStep 2439791 = 3659687) B3659687
theorem B9258239 : Blo 960589 9258239 := bstep (se 1 (by rfl) ⟨6943679, by rfl⟩ : syracuseStep 9258239 = 13887359) B13887359
theorem B1623935 : Blo 960589 1623935 := bstep (se 1 (by rfl) ⟨1217951, by rfl⟩ : syracuseStep 1623935 = 2435903) B2435903
theorem B178053497 : Blo 960589 178053497 := bstep (se 2 (by rfl) ⟨66770061, by rfl⟩ : syracuseStep 178053497 = 133540123) B133540123
theorem B4384487 : Blo 960589 4384487 := bstep (se 1 (by rfl) ⟨3288365, by rfl⟩ : syracuseStep 4384487 = 6576731) B6576731
theorem B1441487 : Blo 960589 1441487 := bstep (se 1 (by rfl) ⟨1081115, by rfl⟩ : syracuseStep 1441487 = 2162231) B2162231
theorem B3211859 : Blo 960589 3211859 := bstep (se 1 (by rfl) ⟨2408894, by rfl⟩ : syracuseStep 3211859 = 4817789) B4817789
theorem B1082623 : Blo 960589 1082623 := bstep (se 1 (by rfl) ⟨811967, by rfl⟩ : syracuseStep 1082623 = 1623935) B1623935
theorem B1443611 : Blo 960589 1443611 := bstep (se 1 (by rfl) ⟨1082708, by rfl⟩ : syracuseStep 1443611 = 2165417) B2165417
theorem B1445099 : Blo 960589 1445099 := bstep (se 1 (by rfl) ⟨1083824, by rfl⟩ : syracuseStep 1445099 = 2167649) B2167649
theorem B3247721 : Blo 960589 3247721 := bstep (se 2 (by rfl) ⟨1217895, by rfl⟩ : syracuseStep 3247721 = 2435791) B2435791
theorem B960991 : Blo 960589 960991 := bstep (se 1 (by rfl) ⟨720743, by rfl⟩ : syracuseStep 960991 = 1441487) B1441487
theorem B6172159 : Blo 960589 6172159 := bstep (se 1 (by rfl) ⟨4629119, by rfl⟩ : syracuseStep 6172159 = 9258239) B9258239
theorem B4175975 : Blo 960589 4175975 := bstep (se 1 (by rfl) ⟨3131981, by rfl⟩ : syracuseStep 4175975 = 6263963) B6263963
theorem B59227787 : Blo 960589 59227787 := bstep (se 1 (by rfl) ⟨44420840, by rfl⟩ : syracuseStep 59227787 = 88841681) B88841681
theorem B2605223 : Blo 960589 2605223 := bstep (se 1 (by rfl) ⟨1953917, by rfl⟩ : syracuseStep 2605223 = 3907835) B3907835
theorem B118702331 : Blo 960589 118702331 := bstep (se 1 (by rfl) ⟨89026748, by rfl⟩ : syracuseStep 118702331 = 178053497) B178053497
theorem B2738843 : Blo 960589 2738843 := bstep (se 1 (by rfl) ⟨2054132, by rfl⟩ : syracuseStep 2738843 = 4108265) B4108265
theorem B12505471 : Blo 960589 12505471 := bstep (se 1 (by rfl) ⟨9379103, by rfl⟩ : syracuseStep 12505471 = 18758207) B18758207
theorem B1626527 : Blo 960589 1626527 := bstep (se 1 (by rfl) ⟨1219895, by rfl⟩ : syracuseStep 1626527 = 2439791) B2439791
theorem B10969991 : Blo 960589 10969991 := bstep (se 1 (by rfl) ⟨8227493, by rfl⟩ : syracuseStep 10969991 = 16454987) B16454987
theorem B11691965 : Blo 960589 11691965 := bstep (se 3 (by rfl) ⟨2192243, by rfl⟩ : syracuseStep 11691965 = 4384487) B4384487
theorem B35186825 : Blo 960589 35186825 := bstep (se 2 (by rfl) ⟨13195059, by rfl⟩ : syracuseStep 35186825 = 26390119) B26390119
theorem B1502201 : Blo 960589 1502201 := bstep (se 2 (by rfl) ⟨563325, by rfl⟩ : syracuseStep 1502201 = 1126651) B1126651
theorem B12349853 : Blo 960589 12349853 := bstep (se 3 (by rfl) ⟨2315597, by rfl⟩ : syracuseStep 12349853 = 4631195) B4631195
theorem B1736815 : Blo 960589 1736815 := bstep (se 1 (by rfl) ⟨1302611, by rfl⟩ : syracuseStep 1736815 = 2605223) B2605223
theorem B79134887 : Blo 960589 79134887 := bstep (se 1 (by rfl) ⟨59351165, by rfl⟩ : syracuseStep 79134887 = 118702331) B118702331
theorem B1443497 : Blo 960589 1443497 := bstep (se 2 (by rfl) ⟨541311, by rfl⟩ : syracuseStep 1443497 = 1082623) B1082623
theorem B2165147 : Blo 960589 2165147 := bstep (se 1 (by rfl) ⟨1623860, by rfl⟩ : syracuseStep 2165147 = 3247721) B3247721
theorem B1084351 : Blo 960589 1084351 := bstep (se 1 (by rfl) ⟨813263, by rfl⟩ : syracuseStep 1084351 = 1626527) B1626527
theorem B8229545 : Blo 960589 8229545 := bstep (se 2 (by rfl) ⟨3086079, by rfl⟩ : syracuseStep 8229545 = 6172159) B6172159
theorem B7313327 : Blo 960589 7313327 := bstep (se 1 (by rfl) ⟨5484995, by rfl⟩ : syracuseStep 7313327 = 10969991) B10969991
theorem B8233235 : Blo 960589 8233235 := bstep (se 1 (by rfl) ⟨6174926, by rfl⟩ : syracuseStep 8233235 = 12349853) B12349853
theorem B962407 : Blo 960589 962407 := bstep (se 1 (by rfl) ⟨721805, by rfl⟩ : syracuseStep 962407 = 1443611) B1443611
theorem B8564957 : Blo 960589 8564957 := bstep (se 3 (by rfl) ⟨1605929, by rfl⟩ : syracuseStep 8564957 = 3211859) B3211859
theorem B66695845 : Blo 960589 66695845 := bstep (se 4 (by rfl) ⟨6252735, by rfl⟩ : syracuseStep 66695845 = 12505471) B12505471
theorem B963399 : Blo 960589 963399 := bstep (se 1 (by rfl) ⟨722549, by rfl⟩ : syracuseStep 963399 = 1445099) B1445099
theorem B1001467 : Blo 960589 1001467 := bstep (se 1 (by rfl) ⟨751100, by rfl⟩ : syracuseStep 1001467 = 1502201) B1502201
theorem B1825895 : Blo 960589 1825895 := bstep (se 1 (by rfl) ⟨1369421, by rfl⟩ : syracuseStep 1825895 = 2738843) B2738843
theorem B7794643 : Blo 960589 7794643 := bstep (se 1 (by rfl) ⟨5845982, by rfl⟩ : syracuseStep 7794643 = 11691965) B11691965
theorem B23457883 : Blo 960589 23457883 := bstep (se 1 (by rfl) ⟨17593412, by rfl⟩ : syracuseStep 23457883 = 35186825) B35186825
theorem B2783983 : Blo 960589 2783983 := bstep (se 1 (by rfl) ⟨2087987, by rfl⟩ : syracuseStep 2783983 = 4175975) B4175975
theorem B39485191 : Blo 960589 39485191 := bstep (se 1 (by rfl) ⟨29613893, by rfl⟩ : syracuseStep 39485191 = 59227787) B59227787
theorem B52756591 : Blo 960589 52756591 := bstep (se 1 (by rfl) ⟨39567443, by rfl⟩ : syracuseStep 52756591 = 79134887) B79134887
theorem B1443431 : Blo 960589 1443431 := bstep (se 1 (by rfl) ⟨1082573, by rfl⟩ : syracuseStep 1443431 = 2165147) B2165147
theorem B1445801 : Blo 960589 1445801 := bstep (se 2 (by rfl) ⟨542175, by rfl⟩ : syracuseStep 1445801 = 1084351) B1084351
theorem B1217263 : Blo 960589 1217263 := bstep (se 1 (by rfl) ⟨912947, by rfl⟩ : syracuseStep 1217263 = 1825895) B1825895
theorem B10392857 : Blo 960589 10392857 := bstep (se 2 (by rfl) ⟨3897321, by rfl⟩ : syracuseStep 10392857 = 7794643) B7794643
theorem B5709971 : Blo 960589 5709971 := bstep (se 1 (by rfl) ⟨4282478, by rfl⟩ : syracuseStep 5709971 = 8564957) B8564957
theorem B3711977 : Blo 960589 3711977 := bstep (se 2 (by rfl) ⟨1391991, by rfl⟩ : syracuseStep 3711977 = 2783983) B2783983
theorem B962331 : Blo 960589 962331 := bstep (se 1 (by rfl) ⟨721748, by rfl⟩ : syracuseStep 962331 = 1443497) B1443497
theorem B5486363 : Blo 960589 5486363 := bstep (se 1 (by rfl) ⟨4114772, by rfl⟩ : syracuseStep 5486363 = 8229545) B8229545
theorem B31277177 : Blo 960589 31277177 := bstep (se 2 (by rfl) ⟨11728941, by rfl⟩ : syracuseStep 31277177 = 23457883) B23457883
theorem B5488823 : Blo 960589 5488823 := bstep (se 1 (by rfl) ⟨4116617, by rfl⟩ : syracuseStep 5488823 = 8233235) B8233235
theorem B52646921 : Blo 960589 52646921 := bstep (se 2 (by rfl) ⟨19742595, by rfl⟩ : syracuseStep 52646921 = 39485191) B39485191
theorem B2315753 : Blo 960589 2315753 := bstep (se 2 (by rfl) ⟨868407, by rfl⟩ : syracuseStep 2315753 = 1736815) B1736815
theorem B1335289 : Blo 960589 1335289 := bstep (se 2 (by rfl) ⟨500733, by rfl⟩ : syracuseStep 1335289 = 1001467) B1001467
theorem B4875551 : Blo 960589 4875551 := bstep (se 1 (by rfl) ⟨3656663, by rfl⟩ : syracuseStep 4875551 = 7313327) B7313327
theorem B88927793 : Blo 960589 88927793 := bstep (se 2 (by rfl) ⟨33347922, by rfl⟩ : syracuseStep 88927793 = 66695845) B66695845
theorem B35097947 : Blo 960589 35097947 := bstep (se 1 (by rfl) ⟨26323460, by rfl⟩ : syracuseStep 35097947 = 52646921) B52646921
theorem B1543835 : Blo 960589 1543835 := bstep (se 1 (by rfl) ⟨1157876, by rfl⟩ : syracuseStep 1543835 = 2315753) B2315753
theorem B3250367 : Blo 960589 3250367 := bstep (se 1 (by rfl) ⟨2437775, by rfl⟩ : syracuseStep 3250367 = 4875551) B4875551
theorem B59285195 : Blo 960589 59285195 := bstep (se 1 (by rfl) ⟨44463896, by rfl⟩ : syracuseStep 59285195 = 88927793) B88927793
theorem B1780385 : Blo 960589 1780385 := bstep (se 2 (by rfl) ⟨667644, by rfl⟩ : syracuseStep 1780385 = 1335289) B1335289
theorem B20851451 : Blo 960589 20851451 := bstep (se 1 (by rfl) ⟨15638588, by rfl⟩ : syracuseStep 20851451 = 31277177) B31277177
theorem B962287 : Blo 960589 962287 := bstep (se 1 (by rfl) ⟨721715, by rfl⟩ : syracuseStep 962287 = 1443431) B1443431
theorem B963867 : Blo 960589 963867 := bstep (se 1 (by rfl) ⟨722900, by rfl⟩ : syracuseStep 963867 = 1445801) B1445801
theorem B6928571 : Blo 960589 6928571 := bstep (se 1 (by rfl) ⟨5196428, by rfl⟩ : syracuseStep 6928571 = 10392857) B10392857
theorem B2474651 : Blo 960589 2474651 := bstep (se 1 (by rfl) ⟨1855988, by rfl⟩ : syracuseStep 2474651 = 3711977) B3711977
theorem B1623017 : Blo 960589 1623017 := bstep (se 2 (by rfl) ⟨608631, by rfl⟩ : syracuseStep 1623017 = 1217263) B1217263
theorem B3657575 : Blo 960589 3657575 := bstep (se 1 (by rfl) ⟨2743181, by rfl⟩ : syracuseStep 3657575 = 5486363) B5486363
theorem B3659215 : Blo 960589 3659215 := bstep (se 1 (by rfl) ⟨2744411, by rfl⟩ : syracuseStep 3659215 = 5488823) B5488823
theorem B70342121 : Blo 960589 70342121 := bstep (se 2 (by rfl) ⟨26378295, by rfl⟩ : syracuseStep 70342121 = 52756591) B52756591
theorem B15226589 : Blo 960589 15226589 := bstep (se 3 (by rfl) ⟨2854985, by rfl⟩ : syracuseStep 15226589 = 5709971) B5709971
theorem B1082011 : Blo 960589 1082011 := bstep (se 1 (by rfl) ⟨811508, by rfl⟩ : syracuseStep 1082011 = 1623017) B1623017
theorem B23398631 : Blo 960589 23398631 := bstep (se 1 (by rfl) ⟨17548973, by rfl⟩ : syracuseStep 23398631 = 35097947) B35097947
theorem B46894747 : Blo 960589 46894747 := bstep (se 1 (by rfl) ⟨35171060, by rfl⟩ : syracuseStep 46894747 = 70342121) B70342121
theorem B2166911 : Blo 960589 2166911 := bstep (se 1 (by rfl) ⟨1625183, by rfl⟩ : syracuseStep 2166911 = 3250367) B3250367
theorem B40604237 : Blo 960589 40604237 := bstep (se 3 (by rfl) ⟨7613294, by rfl⟩ : syracuseStep 40604237 = 15226589) B15226589
theorem B39523463 : Blo 960589 39523463 := bstep (se 1 (by rfl) ⟨29642597, by rfl⟩ : syracuseStep 39523463 = 59285195) B59285195
theorem B13900967 : Blo 960589 13900967 := bstep (se 1 (by rfl) ⟨10425725, by rfl⟩ : syracuseStep 13900967 = 20851451) B20851451
theorem B6599069 : Blo 960589 6599069 := bstep (se 3 (by rfl) ⟨1237325, by rfl⟩ : syracuseStep 6599069 = 2474651) B2474651
theorem B1029223 : Blo 960589 1029223 := bstep (se 1 (by rfl) ⟨771917, by rfl⟩ : syracuseStep 1029223 = 1543835) B1543835
theorem B2438383 : Blo 960589 2438383 := bstep (se 1 (by rfl) ⟨1828787, by rfl⟩ : syracuseStep 2438383 = 3657575) B3657575
theorem B4747693 : Blo 960589 4747693 := bstep (se 3 (by rfl) ⟨890192, by rfl⟩ : syracuseStep 4747693 = 1780385) B1780385
theorem B4878953 : Blo 960589 4878953 := bstep (se 2 (by rfl) ⟨1829607, by rfl⟩ : syracuseStep 4878953 = 3659215) B3659215
theorem B4619047 : Blo 960589 4619047 := bstep (se 1 (by rfl) ⟨3464285, by rfl⟩ : syracuseStep 4619047 = 6928571) B6928571
theorem B1442681 : Blo 960589 1442681 := bstep (se 2 (by rfl) ⟨541005, by rfl⟩ : syracuseStep 1442681 = 1082011) B1082011
theorem B15599087 : Blo 960589 15599087 := bstep (se 1 (by rfl) ⟨11699315, by rfl⟩ : syracuseStep 15599087 = 23398631) B23398631
theorem B1444607 : Blo 960589 1444607 := bstep (se 1 (by rfl) ⟨1083455, by rfl⟩ : syracuseStep 1444607 = 2166911) B2166911
theorem B27069491 : Blo 960589 27069491 := bstep (se 1 (by rfl) ⟨20302118, by rfl⟩ : syracuseStep 27069491 = 40604237) B40604237
theorem B26348975 : Blo 960589 26348975 := bstep (se 1 (by rfl) ⟨19761731, by rfl⟩ : syracuseStep 26348975 = 39523463) B39523463
theorem B62526329 : Blo 960589 62526329 := bstep (se 2 (by rfl) ⟨23447373, by rfl⟩ : syracuseStep 62526329 = 46894747) B46894747
theorem B6330257 : Blo 960589 6330257 := bstep (se 2 (by rfl) ⟨2373846, by rfl⟩ : syracuseStep 6330257 = 4747693) B4747693
theorem B3251177 : Blo 960589 3251177 := bstep (se 2 (by rfl) ⟨1219191, by rfl⟩ : syracuseStep 3251177 = 2438383) B2438383
theorem B4399379 : Blo 960589 4399379 := bstep (se 1 (by rfl) ⟨3299534, by rfl⟩ : syracuseStep 4399379 = 6599069) B6599069
theorem B3252635 : Blo 960589 3252635 := bstep (se 1 (by rfl) ⟨2439476, by rfl⟩ : syracuseStep 3252635 = 4878953) B4878953
theorem B9267311 : Blo 960589 9267311 := bstep (se 1 (by rfl) ⟨6950483, by rfl⟩ : syracuseStep 9267311 = 13900967) B13900967
theorem B1372297 : Blo 960589 1372297 := bstep (se 2 (by rfl) ⟨514611, by rfl⟩ : syracuseStep 1372297 = 1029223) B1029223
theorem B6158729 : Blo 960589 6158729 := bstep (se 2 (by rfl) ⟨2309523, by rfl⟩ : syracuseStep 6158729 = 4619047) B4619047
theorem B17565983 : Blo 960589 17565983 := bstep (se 1 (by rfl) ⟨13174487, by rfl⟩ : syracuseStep 17565983 = 26348975) B26348975
theorem B41684219 : Blo 960589 41684219 := bstep (se 1 (by rfl) ⟨31263164, by rfl⟩ : syracuseStep 41684219 = 62526329) B62526329
theorem B2167451 : Blo 960589 2167451 := bstep (se 1 (by rfl) ⟨1625588, by rfl⟩ : syracuseStep 2167451 = 3251177) B3251177
theorem B2168423 : Blo 960589 2168423 := bstep (se 1 (by rfl) ⟨1626317, by rfl⟩ : syracuseStep 2168423 = 3252635) B3252635
theorem B4105819 : Blo 960589 4105819 := bstep (se 1 (by rfl) ⟨3079364, by rfl⟩ : syracuseStep 4105819 = 6158729) B6158729
theorem B961787 : Blo 960589 961787 := bstep (se 1 (by rfl) ⟨721340, by rfl⟩ : syracuseStep 961787 = 1442681) B1442681
theorem B10399391 : Blo 960589 10399391 := bstep (se 1 (by rfl) ⟨7799543, by rfl⟩ : syracuseStep 10399391 = 15599087) B15599087
theorem B963071 : Blo 960589 963071 := bstep (se 1 (by rfl) ⟨722303, by rfl⟩ : syracuseStep 963071 = 1444607) B1444607
theorem B2932919 : Blo 960589 2932919 := bstep (se 1 (by rfl) ⟨2199689, by rfl⟩ : syracuseStep 2932919 = 4399379) B4399379
theorem B6178207 : Blo 960589 6178207 := bstep (se 1 (by rfl) ⟨4633655, by rfl⟩ : syracuseStep 6178207 = 9267311) B9267311
theorem B18046327 : Blo 960589 18046327 := bstep (se 1 (by rfl) ⟨13534745, by rfl⟩ : syracuseStep 18046327 = 27069491) B27069491
theorem B4220171 : Blo 960589 4220171 := bstep (se 1 (by rfl) ⟨3165128, by rfl⟩ : syracuseStep 4220171 = 6330257) B6330257
theorem B1829729 : Blo 960589 1829729 := bstep (se 2 (by rfl) ⟨686148, by rfl⟩ : syracuseStep 1829729 = 1372297) B1372297
theorem B5474425 : Blo 960589 5474425 := bstep (se 2 (by rfl) ⟨2052909, by rfl⟩ : syracuseStep 5474425 = 4105819) B4105819
theorem B27789479 : Blo 960589 27789479 := bstep (se 1 (by rfl) ⟨20842109, by rfl⟩ : syracuseStep 27789479 = 41684219) B41684219
theorem B1444967 : Blo 960589 1444967 := bstep (se 1 (by rfl) ⟨1083725, by rfl⟩ : syracuseStep 1444967 = 2167451) B2167451
theorem B1445615 : Blo 960589 1445615 := bstep (se 1 (by rfl) ⟨1084211, by rfl⟩ : syracuseStep 1445615 = 2168423) B2168423
theorem B24061769 : Blo 960589 24061769 := bstep (se 2 (by rfl) ⟨9023163, by rfl⟩ : syracuseStep 24061769 = 18046327) B18046327
theorem B11710655 : Blo 960589 11710655 := bstep (se 1 (by rfl) ⟨8782991, by rfl⟩ : syracuseStep 11710655 = 17565983) B17565983
theorem B8237609 : Blo 960589 8237609 := bstep (se 2 (by rfl) ⟨3089103, by rfl⟩ : syracuseStep 8237609 = 6178207) B6178207
theorem B6932927 : Blo 960589 6932927 := bstep (se 1 (by rfl) ⟨5199695, by rfl⟩ : syracuseStep 6932927 = 10399391) B10399391
theorem B1955279 : Blo 960589 1955279 := bstep (se 1 (by rfl) ⟨1466459, by rfl⟩ : syracuseStep 1955279 = 2932919) B2932919
theorem B2813447 : Blo 960589 2813447 := bstep (se 1 (by rfl) ⟨2110085, by rfl⟩ : syracuseStep 2813447 = 4220171) B4220171
theorem B4879277 : Blo 960589 4879277 := bstep (se 3 (by rfl) ⟨914864, by rfl⟩ : syracuseStep 4879277 = 1829729) B1829729
theorem B4621951 : Blo 960589 4621951 := bstep (se 1 (by rfl) ⟨3466463, by rfl⟩ : syracuseStep 4621951 = 6932927) B6932927
theorem B1875631 : Blo 960589 1875631 := bstep (se 1 (by rfl) ⟨1406723, by rfl⟩ : syracuseStep 1875631 = 2813447) B2813447
theorem B7807103 : Blo 960589 7807103 := bstep (se 1 (by rfl) ⟨5855327, by rfl⟩ : syracuseStep 7807103 = 11710655) B11710655
theorem B3252851 : Blo 960589 3252851 := bstep (se 1 (by rfl) ⟨2439638, by rfl⟩ : syracuseStep 3252851 = 4879277) B4879277
theorem B18526319 : Blo 960589 18526319 := bstep (se 1 (by rfl) ⟨13894739, by rfl⟩ : syracuseStep 18526319 = 27789479) B27789479
theorem B963311 : Blo 960589 963311 := bstep (se 1 (by rfl) ⟨722483, by rfl⟩ : syracuseStep 963311 = 1444967) B1444967
theorem B963743 : Blo 960589 963743 := bstep (se 1 (by rfl) ⟨722807, by rfl⟩ : syracuseStep 963743 = 1445615) B1445615
theorem B16041179 : Blo 960589 16041179 := bstep (se 1 (by rfl) ⟨12030884, by rfl⟩ : syracuseStep 16041179 = 24061769) B24061769
theorem B5491739 : Blo 960589 5491739 := bstep (se 1 (by rfl) ⟨4118804, by rfl⟩ : syracuseStep 5491739 = 8237609) B8237609
theorem B7299233 : Blo 960589 7299233 := bstep (se 2 (by rfl) ⟨2737212, by rfl⟩ : syracuseStep 7299233 = 5474425) B5474425
theorem B1303519 : Blo 960589 1303519 := bstep (se 1 (by rfl) ⟨977639, by rfl⟩ : syracuseStep 1303519 = 1955279) B1955279
theorem B1738025 : Blo 960589 1738025 := bstep (se 2 (by rfl) ⟨651759, by rfl⟩ : syracuseStep 1738025 = 1303519) B1303519
theorem B6162601 : Blo 960589 6162601 := bstep (se 2 (by rfl) ⟨2310975, by rfl⟩ : syracuseStep 6162601 = 4621951) B4621951
theorem B2168567 : Blo 960589 2168567 := bstep (se 1 (by rfl) ⟨1626425, by rfl⟩ : syracuseStep 2168567 = 3252851) B3252851
theorem B2500841 : Blo 960589 2500841 := bstep (se 2 (by rfl) ⟨937815, by rfl⟩ : syracuseStep 2500841 = 1875631) B1875631
theorem B10694119 : Blo 960589 10694119 := bstep (se 1 (by rfl) ⟨8020589, by rfl⟩ : syracuseStep 10694119 = 16041179) B16041179
theorem B4866155 : Blo 960589 4866155 := bstep (se 1 (by rfl) ⟨3649616, by rfl⟩ : syracuseStep 4866155 = 7299233) B7299233
theorem B3661159 : Blo 960589 3661159 := bstep (se 1 (by rfl) ⟨2745869, by rfl⟩ : syracuseStep 3661159 = 5491739) B5491739
theorem B5204735 : Blo 960589 5204735 := bstep (se 1 (by rfl) ⟨3903551, by rfl⟩ : syracuseStep 5204735 = 7807103) B7807103
theorem B12350879 : Blo 960589 12350879 := bstep (se 1 (by rfl) ⟨9263159, by rfl⟩ : syracuseStep 12350879 = 18526319) B18526319
theorem B3244103 : Blo 960589 3244103 := bstep (se 1 (by rfl) ⟨2433077, by rfl⟩ : syracuseStep 3244103 = 4866155) B4866155
theorem B1445711 : Blo 960589 1445711 := bstep (se 1 (by rfl) ⟨1084283, by rfl⟩ : syracuseStep 1445711 = 2168567) B2168567
theorem B14258825 : Blo 960589 14258825 := bstep (se 2 (by rfl) ⟨5347059, by rfl⟩ : syracuseStep 14258825 = 10694119) B10694119
theorem B8233919 : Blo 960589 8233919 := bstep (se 1 (by rfl) ⟨6175439, by rfl⟩ : syracuseStep 8233919 = 12350879) B12350879
theorem B1158683 : Blo 960589 1158683 := bstep (se 1 (by rfl) ⟨869012, by rfl⟩ : syracuseStep 1158683 = 1738025) B1738025
theorem B8216801 : Blo 960589 8216801 := bstep (se 2 (by rfl) ⟨3081300, by rfl⟩ : syracuseStep 8216801 = 6162601) B6162601
theorem B1667227 : Blo 960589 1667227 := bstep (se 1 (by rfl) ⟨1250420, by rfl⟩ : syracuseStep 1667227 = 2500841) B2500841
theorem B3469823 : Blo 960589 3469823 := bstep (se 1 (by rfl) ⟨2602367, by rfl⟩ : syracuseStep 3469823 = 5204735) B5204735
theorem B4881545 : Blo 960589 4881545 := bstep (se 2 (by rfl) ⟨1830579, by rfl⟩ : syracuseStep 4881545 = 3661159) B3661159
theorem B2162735 : Blo 960589 2162735 := bstep (se 1 (by rfl) ⟨1622051, by rfl⟩ : syracuseStep 2162735 = 3244103) B3244103
theorem B9505883 : Blo 960589 9505883 := bstep (se 1 (by rfl) ⟨7129412, by rfl⟩ : syracuseStep 9505883 = 14258825) B14258825
theorem B5477867 : Blo 960589 5477867 := bstep (se 1 (by rfl) ⟨4108400, by rfl⟩ : syracuseStep 5477867 = 8216801) B8216801
theorem B3089821 : Blo 960589 3089821 := bstep (se 3 (by rfl) ⟨579341, by rfl⟩ : syracuseStep 3089821 = 1158683) B1158683
theorem B3254363 : Blo 960589 3254363 := bstep (se 1 (by rfl) ⟨2440772, by rfl⟩ : syracuseStep 3254363 = 4881545) B4881545
theorem B963807 : Blo 960589 963807 := bstep (se 1 (by rfl) ⟨722855, by rfl⟩ : syracuseStep 963807 = 1445711) B1445711
theorem B5489279 : Blo 960589 5489279 := bstep (se 1 (by rfl) ⟨4116959, by rfl⟩ : syracuseStep 5489279 = 8233919) B8233919
theorem B2313215 : Blo 960589 2313215 := bstep (se 1 (by rfl) ⟨1734911, by rfl⟩ : syracuseStep 2313215 = 3469823) B3469823
theorem B2222969 : Blo 960589 2222969 := bstep (se 2 (by rfl) ⟨833613, by rfl⟩ : syracuseStep 2222969 = 1667227) B1667227
theorem B1441823 : Blo 960589 1441823 := bstep (se 1 (by rfl) ⟨1081367, by rfl⟩ : syracuseStep 1441823 = 2162735) B2162735
theorem B1542143 : Blo 960589 1542143 := bstep (se 1 (by rfl) ⟨1156607, by rfl⟩ : syracuseStep 1542143 = 2313215) B2313215
theorem B2169575 : Blo 960589 2169575 := bstep (se 1 (by rfl) ⟨1627181, by rfl⟩ : syracuseStep 2169575 = 3254363) B3254363
theorem B3651911 : Blo 960589 3651911 := bstep (se 1 (by rfl) ⟨2738933, by rfl⟩ : syracuseStep 3651911 = 5477867) B5477867
theorem B25349021 : Blo 960589 25349021 := bstep (se 3 (by rfl) ⟨4752941, by rfl⟩ : syracuseStep 25349021 = 9505883) B9505883
theorem B3659519 : Blo 960589 3659519 := bstep (se 1 (by rfl) ⟨2744639, by rfl⟩ : syracuseStep 3659519 = 5489279) B5489279
theorem B4119761 : Blo 960589 4119761 := bstep (se 2 (by rfl) ⟨1544910, by rfl⟩ : syracuseStep 4119761 = 3089821) B3089821
theorem B5927917 : Blo 960589 5927917 := bstep (se 3 (by rfl) ⟨1111484, by rfl⟩ : syracuseStep 5927917 = 2222969) B2222969
theorem B1446383 : Blo 960589 1446383 := bstep (se 1 (by rfl) ⟨1084787, by rfl⟩ : syracuseStep 1446383 = 2169575) B2169575
theorem B7903889 : Blo 960589 7903889 := bstep (se 2 (by rfl) ⟨2963958, by rfl⟩ : syracuseStep 7903889 = 5927917) B5927917
theorem B10986029 : Blo 960589 10986029 := bstep (se 3 (by rfl) ⟨2059880, by rfl⟩ : syracuseStep 10986029 = 4119761) B4119761
theorem B2434607 : Blo 960589 2434607 := bstep (se 1 (by rfl) ⟨1825955, by rfl⟩ : syracuseStep 2434607 = 3651911) B3651911
theorem B961215 : Blo 960589 961215 := bstep (se 1 (by rfl) ⟨720911, by rfl⟩ : syracuseStep 961215 = 1441823) B1441823
theorem B1028095 : Blo 960589 1028095 := bstep (se 1 (by rfl) ⟨771071, by rfl⟩ : syracuseStep 1028095 = 1542143) B1542143
theorem B2439679 : Blo 960589 2439679 := bstep (se 1 (by rfl) ⟨1829759, by rfl⟩ : syracuseStep 2439679 = 3659519) B3659519
theorem B16899347 : Blo 960589 16899347 := bstep (se 1 (by rfl) ⟨12674510, by rfl⟩ : syracuseStep 16899347 = 25349021) B25349021
theorem B3252905 : Blo 960589 3252905 := bstep (se 2 (by rfl) ⟨1219839, by rfl⟩ : syracuseStep 3252905 = 2439679) B2439679
theorem B5483173 : Blo 960589 5483173 := bstep (se 4 (by rfl) ⟨514047, by rfl⟩ : syracuseStep 5483173 = 1028095) B1028095
theorem B964255 : Blo 960589 964255 := bstep (se 1 (by rfl) ⟨723191, by rfl⟩ : syracuseStep 964255 = 1446383) B1446383
theorem B7324019 : Blo 960589 7324019 := bstep (se 1 (by rfl) ⟨5493014, by rfl⟩ : syracuseStep 7324019 = 10986029) B10986029
theorem B1623071 : Blo 960589 1623071 := bstep (se 1 (by rfl) ⟨1217303, by rfl⟩ : syracuseStep 1623071 = 2434607) B2434607
theorem B5269259 : Blo 960589 5269259 := bstep (se 1 (by rfl) ⟨3951944, by rfl⟩ : syracuseStep 5269259 = 7903889) B7903889
theorem B11266231 : Blo 960589 11266231 := bstep (se 1 (by rfl) ⟨8449673, by rfl⟩ : syracuseStep 11266231 = 16899347) B16899347
theorem B4882679 : Blo 960589 4882679 := bstep (se 1 (by rfl) ⟨3662009, by rfl⟩ : syracuseStep 4882679 = 7324019) B7324019
theorem B1082047 : Blo 960589 1082047 := bstep (se 1 (by rfl) ⟨811535, by rfl⟩ : syracuseStep 1082047 = 1623071) B1623071
theorem B7310897 : Blo 960589 7310897 := bstep (se 2 (by rfl) ⟨2741586, by rfl⟩ : syracuseStep 7310897 = 5483173) B5483173
theorem B2168603 : Blo 960589 2168603 := bstep (se 1 (by rfl) ⟨1626452, by rfl⟩ : syracuseStep 2168603 = 3252905) B3252905
theorem B15021641 : Blo 960589 15021641 := bstep (se 2 (by rfl) ⟨5633115, by rfl⟩ : syracuseStep 15021641 = 11266231) B11266231
theorem B14051357 : Blo 960589 14051357 := bstep (se 3 (by rfl) ⟨2634629, by rfl⟩ : syracuseStep 14051357 = 5269259) B5269259
theorem B1442729 : Blo 960589 1442729 := bstep (se 2 (by rfl) ⟨541023, by rfl⟩ : syracuseStep 1442729 = 1082047) B1082047
theorem B1445735 : Blo 960589 1445735 := bstep (se 1 (by rfl) ⟨1084301, by rfl⟩ : syracuseStep 1445735 = 2168603) B2168603
theorem B3255119 : Blo 960589 3255119 := bstep (se 1 (by rfl) ⟨2441339, by rfl⟩ : syracuseStep 3255119 = 4882679) B4882679
theorem B10014427 : Blo 960589 10014427 := bstep (se 1 (by rfl) ⟨7510820, by rfl⟩ : syracuseStep 10014427 = 15021641) B15021641
theorem B4873931 : Blo 960589 4873931 := bstep (se 1 (by rfl) ⟨3655448, by rfl⟩ : syracuseStep 4873931 = 7310897) B7310897
theorem B9367571 : Blo 960589 9367571 := bstep (se 1 (by rfl) ⟨7025678, by rfl⟩ : syracuseStep 9367571 = 14051357) B14051357
theorem B3249287 : Blo 960589 3249287 := bstep (se 1 (by rfl) ⟨2436965, by rfl⟩ : syracuseStep 3249287 = 4873931) B4873931
theorem B2170079 : Blo 960589 2170079 := bstep (se 1 (by rfl) ⟨1627559, by rfl⟩ : syracuseStep 2170079 = 3255119) B3255119
theorem B961819 : Blo 960589 961819 := bstep (se 1 (by rfl) ⟨721364, by rfl⟩ : syracuseStep 961819 = 1442729) B1442729
theorem B963823 : Blo 960589 963823 := bstep (se 1 (by rfl) ⟨722867, by rfl⟩ : syracuseStep 963823 = 1445735) B1445735
theorem B13352569 : Blo 960589 13352569 := bstep (se 2 (by rfl) ⟨5007213, by rfl⟩ : syracuseStep 13352569 = 10014427) B10014427
theorem B6245047 : Blo 960589 6245047 := bstep (se 1 (by rfl) ⟨4683785, by rfl⟩ : syracuseStep 6245047 = 9367571) B9367571
theorem B284854805 : Blo 960589 284854805 := bstep (se 6 (by rfl) ⟨6676284, by rfl⟩ : syracuseStep 284854805 = 13352569) B13352569
theorem B2166191 : Blo 960589 2166191 := bstep (se 1 (by rfl) ⟨1624643, by rfl⟩ : syracuseStep 2166191 = 3249287) B3249287
theorem B8326729 : Blo 960589 8326729 := bstep (se 2 (by rfl) ⟨3122523, by rfl⟩ : syracuseStep 8326729 = 6245047) B6245047
theorem B1446719 : Blo 960589 1446719 := bstep (se 1 (by rfl) ⟨1085039, by rfl⟩ : syracuseStep 1446719 = 2170079) B2170079
theorem B1444127 : Blo 960589 1444127 := bstep (se 1 (by rfl) ⟨1083095, by rfl⟩ : syracuseStep 1444127 = 2166191) B2166191
theorem B189903203 : Blo 960589 189903203 := bstep (se 1 (by rfl) ⟨142427402, by rfl⟩ : syracuseStep 189903203 = 284854805) B284854805
theorem B964479 : Blo 960589 964479 := bstep (se 1 (by rfl) ⟨723359, by rfl⟩ : syracuseStep 964479 = 1446719) B1446719
theorem B11102305 : Blo 960589 11102305 := bstep (se 2 (by rfl) ⟨4163364, by rfl⟩ : syracuseStep 11102305 = 8326729) B8326729
theorem B962751 : Blo 960589 962751 := bstep (se 1 (by rfl) ⟨722063, by rfl⟩ : syracuseStep 962751 = 1444127) B1444127
theorem B126602135 : Blo 960589 126602135 := bstep (se 1 (by rfl) ⟨94951601, by rfl⟩ : syracuseStep 126602135 = 189903203) B189903203
theorem B14803073 : Blo 960589 14803073 := bstep (se 2 (by rfl) ⟨5551152, by rfl⟩ : syracuseStep 14803073 = 11102305) B11102305
theorem B9868715 : Blo 960589 9868715 := bstep (se 1 (by rfl) ⟨7401536, by rfl⟩ : syracuseStep 9868715 = 14803073) B14803073
theorem B84401423 : Blo 960589 84401423 := bstep (se 1 (by rfl) ⟨63301067, by rfl⟩ : syracuseStep 84401423 = 126602135) B126602135
theorem B56267615 : Blo 960589 56267615 := bstep (se 1 (by rfl) ⟨42200711, by rfl⟩ : syracuseStep 56267615 = 84401423) B84401423
theorem B6579143 : Blo 960589 6579143 := bstep (se 1 (by rfl) ⟨4934357, by rfl⟩ : syracuseStep 6579143 = 9868715) B9868715
theorem B37511743 : Blo 960589 37511743 := bstep (se 1 (by rfl) ⟨28133807, by rfl⟩ : syracuseStep 37511743 = 56267615) B56267615
theorem B4386095 : Blo 960589 4386095 := bstep (se 1 (by rfl) ⟨3289571, by rfl⟩ : syracuseStep 4386095 = 6579143) B6579143
theorem B2924063 : Blo 960589 2924063 := bstep (se 1 (by rfl) ⟨2193047, by rfl⟩ : syracuseStep 2924063 = 4386095) B4386095
theorem B50015657 : Blo 960589 50015657 := bstep (se 2 (by rfl) ⟨18755871, by rfl⟩ : syracuseStep 50015657 = 37511743) B37511743
theorem B133375085 : Blo 960589 133375085 := bstep (se 3 (by rfl) ⟨25007828, by rfl⟩ : syracuseStep 133375085 = 50015657) B50015657
theorem B1949375 : Blo 960589 1949375 := bstep (se 1 (by rfl) ⟨1462031, by rfl⟩ : syracuseStep 1949375 = 2924063) B2924063
theorem B88916723 : Blo 960589 88916723 := bstep (se 1 (by rfl) ⟨66687542, by rfl⟩ : syracuseStep 88916723 = 133375085) B133375085
theorem B1299583 : Blo 960589 1299583 := bstep (se 1 (by rfl) ⟨974687, by rfl⟩ : syracuseStep 1299583 = 1949375) B1949375
theorem B59277815 : Blo 960589 59277815 := bstep (se 1 (by rfl) ⟨44458361, by rfl⟩ : syracuseStep 59277815 = 88916723) B88916723
theorem B6931109 : Blo 960589 6931109 := bstep (se 4 (by rfl) ⟨649791, by rfl⟩ : syracuseStep 6931109 = 1299583) B1299583
theorem B39518543 : Blo 960589 39518543 := bstep (se 1 (by rfl) ⟨29638907, by rfl⟩ : syracuseStep 39518543 = 59277815) B59277815
theorem B4620739 : Blo 960589 4620739 := bstep (se 1 (by rfl) ⟨3465554, by rfl⟩ : syracuseStep 4620739 = 6931109) B6931109
theorem B26345695 : Blo 960589 26345695 := bstep (se 1 (by rfl) ⟨19759271, by rfl⟩ : syracuseStep 26345695 = 39518543) B39518543
theorem B6160985 : Blo 960589 6160985 := bstep (se 2 (by rfl) ⟨2310369, by rfl⟩ : syracuseStep 6160985 = 4620739) B4620739
theorem B35127593 : Blo 960589 35127593 := bstep (se 2 (by rfl) ⟨13172847, by rfl⟩ : syracuseStep 35127593 = 26345695) B26345695
theorem B4107323 : Blo 960589 4107323 := bstep (se 1 (by rfl) ⟨3080492, by rfl⟩ : syracuseStep 4107323 = 6160985) B6160985
theorem B2738215 : Blo 960589 2738215 := bstep (se 1 (by rfl) ⟨2053661, by rfl⟩ : syracuseStep 2738215 = 4107323) B4107323
theorem B23418395 : Blo 960589 23418395 := bstep (se 1 (by rfl) ⟨17563796, by rfl⟩ : syracuseStep 23418395 = 35127593) B35127593
theorem B3650953 : Blo 960589 3650953 := bstep (se 2 (by rfl) ⟨1369107, by rfl⟩ : syracuseStep 3650953 = 2738215) B2738215
theorem B15612263 : Blo 960589 15612263 := bstep (se 1 (by rfl) ⟨11709197, by rfl⟩ : syracuseStep 15612263 = 23418395) B23418395
theorem B4867937 : Blo 960589 4867937 := bstep (se 2 (by rfl) ⟨1825476, by rfl⟩ : syracuseStep 4867937 = 3650953) B3650953
theorem B10408175 : Blo 960589 10408175 := bstep (se 1 (by rfl) ⟨7806131, by rfl⟩ : syracuseStep 10408175 = 15612263) B15612263
theorem B3245291 : Blo 960589 3245291 := bstep (se 1 (by rfl) ⟨2433968, by rfl⟩ : syracuseStep 3245291 = 4867937) B4867937
theorem B6938783 : Blo 960589 6938783 := bstep (se 1 (by rfl) ⟨5204087, by rfl⟩ : syracuseStep 6938783 = 10408175) B10408175
theorem B2163527 : Blo 960589 2163527 := bstep (se 1 (by rfl) ⟨1622645, by rfl⟩ : syracuseStep 2163527 = 3245291) B3245291
theorem B4625855 : Blo 960589 4625855 := bstep (se 1 (by rfl) ⟨3469391, by rfl⟩ : syracuseStep 4625855 = 6938783) B6938783
theorem B1442351 : Blo 960589 1442351 := bstep (se 1 (by rfl) ⟨1081763, by rfl⟩ : syracuseStep 1442351 = 2163527) B2163527
theorem B3083903 : Blo 960589 3083903 := bstep (se 1 (by rfl) ⟨2312927, by rfl⟩ : syracuseStep 3083903 = 4625855) B4625855
theorem B961567 : Blo 960589 961567 := bstep (se 1 (by rfl) ⟨721175, by rfl⟩ : syracuseStep 961567 = 1442351) B1442351
theorem B2055935 : Blo 960589 2055935 := bstep (se 1 (by rfl) ⟨1541951, by rfl⟩ : syracuseStep 2055935 = 3083903) B3083903
theorem B1370623 : Blo 960589 1370623 := bstep (se 1 (by rfl) ⟨1027967, by rfl⟩ : syracuseStep 1370623 = 2055935) B2055935
theorem B1827497 : Blo 960589 1827497 := bstep (se 2 (by rfl) ⟨685311, by rfl⟩ : syracuseStep 1827497 = 1370623) B1370623
theorem B1218331 : Blo 960589 1218331 := bstep (se 1 (by rfl) ⟨913748, by rfl⟩ : syracuseStep 1218331 = 1827497) B1827497
theorem B1624441 : Blo 960589 1624441 := bstep (se 2 (by rfl) ⟨609165, by rfl⟩ : syracuseStep 1624441 = 1218331) B1218331
theorem B2165921 : Blo 960589 2165921 := bstep (se 2 (by rfl) ⟨812220, by rfl⟩ : syracuseStep 2165921 = 1624441) B1624441
theorem B1443947 : Blo 960589 1443947 := bstep (se 1 (by rfl) ⟨1082960, by rfl⟩ : syracuseStep 1443947 = 2165921) B2165921
theorem B962631 : Blo 960589 962631 := bstep (se 1 (by rfl) ⟨721973, by rfl⟩ : syracuseStep 962631 = 1443947) B1443947

theorem C0 (j : ℕ) (h1 : 240147 ≤ j) (h2 : j ≤ 240846) : Blo 960589 (4 * j + 3) := by
  interval_cases j
  · exact B960591
  · exact B960595
  · exact B960599
  · exact B960603
  · exact B960607
  · exact B960611
  · exact B960615
  · exact B960619
  · exact B960623
  · exact B960627
  · exact B960631
  · exact B960635
  · exact B960639
  · exact B960643
  · exact B960647
  · exact B960651
  · exact B960655
  · exact B960659
  · exact B960663
  · exact B960667
  · exact B960671
  · exact B960675
  · exact B960679
  · exact B960683
  · exact B960687
  · exact B960691
  · exact B960695
  · exact B960699
  · exact B960703
  · exact B960707
  · exact B960711
  · exact B960715
  · exact B960719
  · exact B960723
  · exact B960727
  · exact B960731
  · exact B960735
  · exact B960739
  · exact B960743
  · exact B960747
  · exact B960751
  · exact B960755
  · exact B960759
  · exact B960763
  · exact B960767
  · exact B960771
  · exact B960775
  · exact B960779
  · exact B960783
  · exact B960787
  · exact B960791
  · exact B960795
  · exact B960799
  · exact B960803
  · exact B960807
  · exact B960811
  · exact B960815
  · exact B960819
  · exact B960823
  · exact B960827
  · exact B960831
  · exact B960835
  · exact B960839
  · exact B960843
  · exact B960847
  · exact B960851
  · exact B960855
  · exact B960859
  · exact B960863
  · exact B960867
  · exact B960871
  · exact B960875
  · exact B960879
  · exact B960883
  · exact B960887
  · exact B960891
  · exact B960895
  · exact B960899
  · exact B960903
  · exact B960907
  · exact B960911
  · exact B960915
  · exact B960919
  · exact B960923
  · exact B960927
  · exact B960931
  · exact B960935
  · exact B960939
  · exact B960943
  · exact B960947
  · exact B960951
  · exact B960955
  · exact B960959
  · exact B960963
  · exact B960967
  · exact B960971
  · exact B960975
  · exact B960979
  · exact B960983
  · exact B960987
  · exact B960991
  · exact B960995
  · exact B960999
  · exact B961003
  · exact B961007
  · exact B961011
  · exact B961015
  · exact B961019
  · exact B961023
  · exact B961027
  · exact B961031
  · exact B961035
  · exact B961039
  · exact B961043
  · exact B961047
  · exact B961051
  · exact B961055
  · exact B961059
  · exact B961063
  · exact B961067
  · exact B961071
  · exact B961075
  · exact B961079
  · exact B961083
  · exact B961087
  · exact B961091
  · exact B961095
  · exact B961099
  · exact B961103
  · exact B961107
  · exact B961111
  · exact B961115
  · exact B961119
  · exact B961123
  · exact B961127
  · exact B961131
  · exact B961135
  · exact B961139
  · exact B961143
  · exact B961147
  · exact B961151
  · exact B961155
  · exact B961159
  · exact B961163
  · exact B961167
  · exact B961171
  · exact B961175
  · exact B961179
  · exact B961183
  · exact B961187
  · exact B961191
  · exact B961195
  · exact B961199
  · exact B961203
  · exact B961207
  · exact B961211
  · exact B961215
  · exact B961219
  · exact B961223
  · exact B961227
  · exact B961231
  · exact B961235
  · exact B961239
  · exact B961243
  · exact B961247
  · exact B961251
  · exact B961255
  · exact B961259
  · exact B961263
  · exact B961267
  · exact B961271
  · exact B961275
  · exact B961279
  · exact B961283
  · exact B961287
  · exact B961291
  · exact B961295
  · exact B961299
  · exact B961303
  · exact B961307
  · exact B961311
  · exact B961315
  · exact B961319
  · exact B961323
  · exact B961327
  · exact B961331
  · exact B961335
  · exact B961339
  · exact B961343
  · exact B961347
  · exact B961351
  · exact B961355
  · exact B961359
  · exact B961363
  · exact B961367
  · exact B961371
  · exact B961375
  · exact B961379
  · exact B961383
  · exact B961387
  · exact B961391
  · exact B961395
  · exact B961399
  · exact B961403
  · exact B961407
  · exact B961411
  · exact B961415
  · exact B961419
  · exact B961423
  · exact B961427
  · exact B961431
  · exact B961435
  · exact B961439
  · exact B961443
  · exact B961447
  · exact B961451
  · exact B961455
  · exact B961459
  · exact B961463
  · exact B961467
  · exact B961471
  · exact B961475
  · exact B961479
  · exact B961483
  · exact B961487
  · exact B961491
  · exact B961495
  · exact B961499
  · exact B961503
  · exact B961507
  · exact B961511
  · exact B961515
  · exact B961519
  · exact B961523
  · exact B961527
  · exact B961531
  · exact B961535
  · exact B961539
  · exact B961543
  · exact B961547
  · exact B961551
  · exact B961555
  · exact B961559
  · exact B961563
  · exact B961567
  · exact B961571
  · exact B961575
  · exact B961579
  · exact B961583
  · exact B961587
  · exact B961591
  · exact B961595
  · exact B961599
  · exact B961603
  · exact B961607
  · exact B961611
  · exact B961615
  · exact B961619
  · exact B961623
  · exact B961627
  · exact B961631
  · exact B961635
  · exact B961639
  · exact B961643
  · exact B961647
  · exact B961651
  · exact B961655
  · exact B961659
  · exact B961663
  · exact B961667
  · exact B961671
  · exact B961675
  · exact B961679
  · exact B961683
  · exact B961687
  · exact B961691
  · exact B961695
  · exact B961699
  · exact B961703
  · exact B961707
  · exact B961711
  · exact B961715
  · exact B961719
  · exact B961723
  · exact B961727
  · exact B961731
  · exact B961735
  · exact B961739
  · exact B961743
  · exact B961747
  · exact B961751
  · exact B961755
  · exact B961759
  · exact B961763
  · exact B961767
  · exact B961771
  · exact B961775
  · exact B961779
  · exact B961783
  · exact B961787
  · exact B961791
  · exact B961795
  · exact B961799
  · exact B961803
  · exact B961807
  · exact B961811
  · exact B961815
  · exact B961819
  · exact B961823
  · exact B961827
  · exact B961831
  · exact B961835
  · exact B961839
  · exact B961843
  · exact B961847
  · exact B961851
  · exact B961855
  · exact B961859
  · exact B961863
  · exact B961867
  · exact B961871
  · exact B961875
  · exact B961879
  · exact B961883
  · exact B961887
  · exact B961891
  · exact B961895
  · exact B961899
  · exact B961903
  · exact B961907
  · exact B961911
  · exact B961915
  · exact B961919
  · exact B961923
  · exact B961927
  · exact B961931
  · exact B961935
  · exact B961939
  · exact B961943
  · exact B961947
  · exact B961951
  · exact B961955
  · exact B961959
  · exact B961963
  · exact B961967
  · exact B961971
  · exact B961975
  · exact B961979
  · exact B961983
  · exact B961987
  · exact B961991
  · exact B961995
  · exact B961999
  · exact B962003
  · exact B962007
  · exact B962011
  · exact B962015
  · exact B962019
  · exact B962023
  · exact B962027
  · exact B962031
  · exact B962035
  · exact B962039
  · exact B962043
  · exact B962047
  · exact B962051
  · exact B962055
  · exact B962059
  · exact B962063
  · exact B962067
  · exact B962071
  · exact B962075
  · exact B962079
  · exact B962083
  · exact B962087
  · exact B962091
  · exact B962095
  · exact B962099
  · exact B962103
  · exact B962107
  · exact B962111
  · exact B962115
  · exact B962119
  · exact B962123
  · exact B962127
  · exact B962131
  · exact B962135
  · exact B962139
  · exact B962143
  · exact B962147
  · exact B962151
  · exact B962155
  · exact B962159
  · exact B962163
  · exact B962167
  · exact B962171
  · exact B962175
  · exact B962179
  · exact B962183
  · exact B962187
  · exact B962191
  · exact B962195
  · exact B962199
  · exact B962203
  · exact B962207
  · exact B962211
  · exact B962215
  · exact B962219
  · exact B962223
  · exact B962227
  · exact B962231
  · exact B962235
  · exact B962239
  · exact B962243
  · exact B962247
  · exact B962251
  · exact B962255
  · exact B962259
  · exact B962263
  · exact B962267
  · exact B962271
  · exact B962275
  · exact B962279
  · exact B962283
  · exact B962287
  · exact B962291
  · exact B962295
  · exact B962299
  · exact B962303
  · exact B962307
  · exact B962311
  · exact B962315
  · exact B962319
  · exact B962323
  · exact B962327
  · exact B962331
  · exact B962335
  · exact B962339
  · exact B962343
  · exact B962347
  · exact B962351
  · exact B962355
  · exact B962359
  · exact B962363
  · exact B962367
  · exact B962371
  · exact B962375
  · exact B962379
  · exact B962383
  · exact B962387
  · exact B962391
  · exact B962395
  · exact B962399
  · exact B962403
  · exact B962407
  · exact B962411
  · exact B962415
  · exact B962419
  · exact B962423
  · exact B962427
  · exact B962431
  · exact B962435
  · exact B962439
  · exact B962443
  · exact B962447
  · exact B962451
  · exact B962455
  · exact B962459
  · exact B962463
  · exact B962467
  · exact B962471
  · exact B962475
  · exact B962479
  · exact B962483
  · exact B962487
  · exact B962491
  · exact B962495
  · exact B962499
  · exact B962503
  · exact B962507
  · exact B962511
  · exact B962515
  · exact B962519
  · exact B962523
  · exact B962527
  · exact B962531
  · exact B962535
  · exact B962539
  · exact B962543
  · exact B962547
  · exact B962551
  · exact B962555
  · exact B962559
  · exact B962563
  · exact B962567
  · exact B962571
  · exact B962575
  · exact B962579
  · exact B962583
  · exact B962587
  · exact B962591
  · exact B962595
  · exact B962599
  · exact B962603
  · exact B962607
  · exact B962611
  · exact B962615
  · exact B962619
  · exact B962623
  · exact B962627
  · exact B962631
  · exact B962635
  · exact B962639
  · exact B962643
  · exact B962647
  · exact B962651
  · exact B962655
  · exact B962659
  · exact B962663
  · exact B962667
  · exact B962671
  · exact B962675
  · exact B962679
  · exact B962683
  · exact B962687
  · exact B962691
  · exact B962695
  · exact B962699
  · exact B962703
  · exact B962707
  · exact B962711
  · exact B962715
  · exact B962719
  · exact B962723
  · exact B962727
  · exact B962731
  · exact B962735
  · exact B962739
  · exact B962743
  · exact B962747
  · exact B962751
  · exact B962755
  · exact B962759
  · exact B962763
  · exact B962767
  · exact B962771
  · exact B962775
  · exact B962779
  · exact B962783
  · exact B962787
  · exact B962791
  · exact B962795
  · exact B962799
  · exact B962803
  · exact B962807
  · exact B962811
  · exact B962815
  · exact B962819
  · exact B962823
  · exact B962827
  · exact B962831
  · exact B962835
  · exact B962839
  · exact B962843
  · exact B962847
  · exact B962851
  · exact B962855
  · exact B962859
  · exact B962863
  · exact B962867
  · exact B962871
  · exact B962875
  · exact B962879
  · exact B962883
  · exact B962887
  · exact B962891
  · exact B962895
  · exact B962899
  · exact B962903
  · exact B962907
  · exact B962911
  · exact B962915
  · exact B962919
  · exact B962923
  · exact B962927
  · exact B962931
  · exact B962935
  · exact B962939
  · exact B962943
  · exact B962947
  · exact B962951
  · exact B962955
  · exact B962959
  · exact B962963
  · exact B962967
  · exact B962971
  · exact B962975
  · exact B962979
  · exact B962983
  · exact B962987
  · exact B962991
  · exact B962995
  · exact B962999
  · exact B963003
  · exact B963007
  · exact B963011
  · exact B963015
  · exact B963019
  · exact B963023
  · exact B963027
  · exact B963031
  · exact B963035
  · exact B963039
  · exact B963043
  · exact B963047
  · exact B963051
  · exact B963055
  · exact B963059
  · exact B963063
  · exact B963067
  · exact B963071
  · exact B963075
  · exact B963079
  · exact B963083
  · exact B963087
  · exact B963091
  · exact B963095
  · exact B963099
  · exact B963103
  · exact B963107
  · exact B963111
  · exact B963115
  · exact B963119
  · exact B963123
  · exact B963127
  · exact B963131
  · exact B963135
  · exact B963139
  · exact B963143
  · exact B963147
  · exact B963151
  · exact B963155
  · exact B963159
  · exact B963163
  · exact B963167
  · exact B963171
  · exact B963175
  · exact B963179
  · exact B963183
  · exact B963187
  · exact B963191
  · exact B963195
  · exact B963199
  · exact B963203
  · exact B963207
  · exact B963211
  · exact B963215
  · exact B963219
  · exact B963223
  · exact B963227
  · exact B963231
  · exact B963235
  · exact B963239
  · exact B963243
  · exact B963247
  · exact B963251
  · exact B963255
  · exact B963259
  · exact B963263
  · exact B963267
  · exact B963271
  · exact B963275
  · exact B963279
  · exact B963283
  · exact B963287
  · exact B963291
  · exact B963295
  · exact B963299
  · exact B963303
  · exact B963307
  · exact B963311
  · exact B963315
  · exact B963319
  · exact B963323
  · exact B963327
  · exact B963331
  · exact B963335
  · exact B963339
  · exact B963343
  · exact B963347
  · exact B963351
  · exact B963355
  · exact B963359
  · exact B963363
  · exact B963367
  · exact B963371
  · exact B963375
  · exact B963379
  · exact B963383
  · exact B963387

theorem C1 (j : ℕ) (h1 : 240847 ≤ j) (h2 : j ≤ 241146) : Blo 960589 (4 * j + 3) := by
  interval_cases j
  · exact B963391
  · exact B963395
  · exact B963399
  · exact B963403
  · exact B963407
  · exact B963411
  · exact B963415
  · exact B963419
  · exact B963423
  · exact B963427
  · exact B963431
  · exact B963435
  · exact B963439
  · exact B963443
  · exact B963447
  · exact B963451
  · exact B963455
  · exact B963459
  · exact B963463
  · exact B963467
  · exact B963471
  · exact B963475
  · exact B963479
  · exact B963483
  · exact B963487
  · exact B963491
  · exact B963495
  · exact B963499
  · exact B963503
  · exact B963507
  · exact B963511
  · exact B963515
  · exact B963519
  · exact B963523
  · exact B963527
  · exact B963531
  · exact B963535
  · exact B963539
  · exact B963543
  · exact B963547
  · exact B963551
  · exact B963555
  · exact B963559
  · exact B963563
  · exact B963567
  · exact B963571
  · exact B963575
  · exact B963579
  · exact B963583
  · exact B963587
  · exact B963591
  · exact B963595
  · exact B963599
  · exact B963603
  · exact B963607
  · exact B963611
  · exact B963615
  · exact B963619
  · exact B963623
  · exact B963627
  · exact B963631
  · exact B963635
  · exact B963639
  · exact B963643
  · exact B963647
  · exact B963651
  · exact B963655
  · exact B963659
  · exact B963663
  · exact B963667
  · exact B963671
  · exact B963675
  · exact B963679
  · exact B963683
  · exact B963687
  · exact B963691
  · exact B963695
  · exact B963699
  · exact B963703
  · exact B963707
  · exact B963711
  · exact B963715
  · exact B963719
  · exact B963723
  · exact B963727
  · exact B963731
  · exact B963735
  · exact B963739
  · exact B963743
  · exact B963747
  · exact B963751
  · exact B963755
  · exact B963759
  · exact B963763
  · exact B963767
  · exact B963771
  · exact B963775
  · exact B963779
  · exact B963783
  · exact B963787
  · exact B963791
  · exact B963795
  · exact B963799
  · exact B963803
  · exact B963807
  · exact B963811
  · exact B963815
  · exact B963819
  · exact B963823
  · exact B963827
  · exact B963831
  · exact B963835
  · exact B963839
  · exact B963843
  · exact B963847
  · exact B963851
  · exact B963855
  · exact B963859
  · exact B963863
  · exact B963867
  · exact B963871
  · exact B963875
  · exact B963879
  · exact B963883
  · exact B963887
  · exact B963891
  · exact B963895
  · exact B963899
  · exact B963903
  · exact B963907
  · exact B963911
  · exact B963915
  · exact B963919
  · exact B963923
  · exact B963927
  · exact B963931
  · exact B963935
  · exact B963939
  · exact B963943
  · exact B963947
  · exact B963951
  · exact B963955
  · exact B963959
  · exact B963963
  · exact B963967
  · exact B963971
  · exact B963975
  · exact B963979
  · exact B963983
  · exact B963987
  · exact B963991
  · exact B963995
  · exact B963999
  · exact B964003
  · exact B964007
  · exact B964011
  · exact B964015
  · exact B964019
  · exact B964023
  · exact B964027
  · exact B964031
  · exact B964035
  · exact B964039
  · exact B964043
  · exact B964047
  · exact B964051
  · exact B964055
  · exact B964059
  · exact B964063
  · exact B964067
  · exact B964071
  · exact B964075
  · exact B964079
  · exact B964083
  · exact B964087
  · exact B964091
  · exact B964095
  · exact B964099
  · exact B964103
  · exact B964107
  · exact B964111
  · exact B964115
  · exact B964119
  · exact B964123
  · exact B964127
  · exact B964131
  · exact B964135
  · exact B964139
  · exact B964143
  · exact B964147
  · exact B964151
  · exact B964155
  · exact B964159
  · exact B964163
  · exact B964167
  · exact B964171
  · exact B964175
  · exact B964179
  · exact B964183
  · exact B964187
  · exact B964191
  · exact B964195
  · exact B964199
  · exact B964203
  · exact B964207
  · exact B964211
  · exact B964215
  · exact B964219
  · exact B964223
  · exact B964227
  · exact B964231
  · exact B964235
  · exact B964239
  · exact B964243
  · exact B964247
  · exact B964251
  · exact B964255
  · exact B964259
  · exact B964263
  · exact B964267
  · exact B964271
  · exact B964275
  · exact B964279
  · exact B964283
  · exact B964287
  · exact B964291
  · exact B964295
  · exact B964299
  · exact B964303
  · exact B964307
  · exact B964311
  · exact B964315
  · exact B964319
  · exact B964323
  · exact B964327
  · exact B964331
  · exact B964335
  · exact B964339
  · exact B964343
  · exact B964347
  · exact B964351
  · exact B964355
  · exact B964359
  · exact B964363
  · exact B964367
  · exact B964371
  · exact B964375
  · exact B964379
  · exact B964383
  · exact B964387
  · exact B964391
  · exact B964395
  · exact B964399
  · exact B964403
  · exact B964407
  · exact B964411
  · exact B964415
  · exact B964419
  · exact B964423
  · exact B964427
  · exact B964431
  · exact B964435
  · exact B964439
  · exact B964443
  · exact B964447
  · exact B964451
  · exact B964455
  · exact B964459
  · exact B964463
  · exact B964467
  · exact B964471
  · exact B964475
  · exact B964479
  · exact B964483
  · exact B964487
  · exact B964491
  · exact B964495
  · exact B964499
  · exact B964503
  · exact B964507
  · exact B964511
  · exact B964515
  · exact B964519
  · exact B964523
  · exact B964527
  · exact B964531
  · exact B964535
  · exact B964539
  · exact B964543
  · exact B964547
  · exact B964551
  · exact B964555
  · exact B964559
  · exact B964563
  · exact B964567
  · exact B964571
  · exact B964575
  · exact B964579
  · exact B964583
  · exact B964587

theorem solution (m : ℕ) (hlo : 960589 ≤ m) (hhi : m ≤ 964589) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 240147 ≤ j := by omega
    have hj2 : j ≤ 241146 := by omega
    have hb : Blo 960589 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 240847 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
