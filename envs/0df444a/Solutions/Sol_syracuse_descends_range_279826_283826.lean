-- Prove2me | solution 1 for syracuse_descends_range_279826_283826
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:12.464332+00:00
-- url     : https://prove2.me/submissions/5fba4af7-4b8e-4b8f-81fd-11a8b65dd6e0

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


theorem B852133 : Blo 279826 852133 := bbase (se 4 (by rfl) ⟨79887, by rfl⟩ : syracuseStep 852133 = 159775) (by norm_num)
theorem B950453 : Blo 279826 950453 := bbase (se 5 (by rfl) ⟨44552, by rfl⟩ : syracuseStep 950453 = 89105) (by norm_num)
theorem B721133 : Blo 279826 721133 := bbase (se 3 (by rfl) ⟨135212, by rfl⟩ : syracuseStep 721133 = 270425) (by norm_num)
theorem B1016405 : Blo 279826 1016405 := bbase (se 8 (by rfl) ⟨5955, by rfl⟩ : syracuseStep 1016405 = 11911) (by norm_num)
theorem B950885 : Blo 279826 950885 := bbase (se 4 (by rfl) ⟨89145, by rfl⟩ : syracuseStep 950885 = 178291) (by norm_num)
theorem B3605269 : Blo 279826 3605269 := bbase (se 6 (by rfl) ⟨84498, by rfl⟩ : syracuseStep 3605269 = 168997) (by norm_num)
theorem B951317 : Blo 279826 951317 := bbase (se 6 (by rfl) ⟨22296, by rfl⟩ : syracuseStep 951317 = 44593) (by norm_num)
theorem B328745 : Blo 279826 328745 := bbase (se 2 (by rfl) ⟨123279, by rfl⟩ : syracuseStep 328745 = 246559) (by norm_num)
theorem B722197 : Blo 279826 722197 := bbase (se 6 (by rfl) ⟨16926, by rfl⟩ : syracuseStep 722197 = 33853) (by norm_num)
theorem B951749 : Blo 279826 951749 := bbase (se 4 (by rfl) ⟨89226, by rfl⟩ : syracuseStep 951749 = 178453) (by norm_num)
theorem B1934837 : Blo 279826 1934837 := bbase (se 5 (by rfl) ⟨90695, by rfl⟩ : syracuseStep 1934837 = 181391) (by norm_num)
theorem B362137 : Blo 279826 362137 := bbase (se 2 (by rfl) ⟨135801, by rfl⟩ : syracuseStep 362137 = 271603) (by norm_num)
theorem B952181 : Blo 279826 952181 := bbase (se 5 (by rfl) ⟨44633, by rfl⟩ : syracuseStep 952181 = 89267) (by norm_num)
theorem B427933 : Blo 279826 427933 := bbase (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) (by norm_num)
theorem B493541 : Blo 279826 493541 := bbase (se 4 (by rfl) ⟨46269, by rfl⟩ : syracuseStep 493541 = 92539) (by norm_num)
theorem B428213 : Blo 279826 428213 := bbase (se 5 (by rfl) ⟨20072, by rfl⟩ : syracuseStep 428213 = 40145) (by norm_num)
theorem B854309 : Blo 279826 854309 := bbase (se 4 (by rfl) ⟨80091, by rfl⟩ : syracuseStep 854309 = 160183) (by norm_num)
theorem B952613 : Blo 279826 952613 := bbase (se 4 (by rfl) ⟨89307, by rfl⟩ : syracuseStep 952613 = 178615) (by norm_num)
theorem B297317 : Blo 279826 297317 := bbase (se 4 (by rfl) ⟨27873, by rfl⟩ : syracuseStep 297317 = 55747) (by norm_num)
theorem B953045 : Blo 279826 953045 := bbase (se 7 (by rfl) ⟨11168, by rfl⟩ : syracuseStep 953045 = 22337) (by norm_num)
theorem B953477 : Blo 279826 953477 := bbase (se 4 (by rfl) ⟨89388, by rfl⟩ : syracuseStep 953477 = 178777) (by norm_num)
theorem B756965 : Blo 279826 756965 := bbase (se 4 (by rfl) ⟨70965, by rfl⟩ : syracuseStep 756965 = 141931) (by norm_num)
theorem B953909 : Blo 279826 953909 := bbase (se 5 (by rfl) ⟨44714, by rfl⟩ : syracuseStep 953909 = 89429) (by norm_num)
theorem B1019461 : Blo 279826 1019461 := bbase (se 4 (by rfl) ⟨95574, by rfl⟩ : syracuseStep 1019461 = 191149) (by norm_num)
theorem B1019621 : Blo 279826 1019621 := bbase (se 4 (by rfl) ⟨95589, by rfl⟩ : syracuseStep 1019621 = 191179) (by norm_num)
theorem B1150757 : Blo 279826 1150757 := bbase (se 4 (by rfl) ⟨107883, by rfl⟩ : syracuseStep 1150757 = 215767) (by norm_num)
theorem B954341 : Blo 279826 954341 := bbase (se 4 (by rfl) ⟨89469, by rfl⟩ : syracuseStep 954341 = 178939) (by norm_num)
theorem B856133 : Blo 279826 856133 := bbase (se 4 (by rfl) ⟨80262, by rfl⟩ : syracuseStep 856133 = 160525) (by norm_num)
theorem B2396405 : Blo 279826 2396405 := bbase (se 5 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 2396405 = 224663) (by norm_num)
theorem B954773 : Blo 279826 954773 := bbase (se 6 (by rfl) ⟨22377, by rfl⟩ : syracuseStep 954773 = 44755) (by norm_num)
theorem B1217045 : Blo 279826 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B299585 : Blo 279826 299585 := bbase (se 2 (by rfl) ⟨112344, by rfl⟩ : syracuseStep 299585 = 224689) (by norm_num)
theorem B2036501 : Blo 279826 2036501 := bbase (se 6 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 2036501 = 95461) (by norm_num)
theorem B955205 : Blo 279826 955205 := bbase (se 4 (by rfl) ⟨89550, by rfl⟩ : syracuseStep 955205 = 179101) (by norm_num)
theorem B758693 : Blo 279826 758693 := bbase (se 4 (by rfl) ⟨71127, by rfl⟩ : syracuseStep 758693 = 142255) (by norm_num)
theorem B2134997 : Blo 279826 2134997 := bbase (se 7 (by rfl) ⟨25019, by rfl⟩ : syracuseStep 2134997 = 50039) (by norm_num)
theorem B300029 : Blo 279826 300029 := bbase (se 3 (by rfl) ⟨56255, by rfl⟩ : syracuseStep 300029 = 112511) (by norm_num)
theorem B300277 : Blo 279826 300277 := bbase (se 5 (by rfl) ⟨14075, by rfl⟩ : syracuseStep 300277 = 28151) (by norm_num)
theorem B955637 : Blo 279826 955637 := bbase (se 5 (by rfl) ⟨44795, by rfl⟩ : syracuseStep 955637 = 89591) (by norm_num)
theorem B398621 : Blo 279826 398621 := bbase (se 3 (by rfl) ⟨74741, by rfl⟩ : syracuseStep 398621 = 149483) (by norm_num)
theorem B1348901 : Blo 279826 1348901 := bbase (se 4 (by rfl) ⟨126459, by rfl⟩ : syracuseStep 1348901 = 252919) (by norm_num)
theorem B1218053 : Blo 279826 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B300709 : Blo 279826 300709 := bbase (se 4 (by rfl) ⟨28191, by rfl⟩ : syracuseStep 300709 = 56383) (by norm_num)
theorem B956069 : Blo 279826 956069 := bbase (se 4 (by rfl) ⟨89631, by rfl⟩ : syracuseStep 956069 = 179263) (by norm_num)
theorem B1218277 : Blo 279826 1218277 := bbase (se 4 (by rfl) ⟨114213, by rfl⟩ : syracuseStep 1218277 = 228427) (by norm_num)
theorem B300781 : Blo 279826 300781 := bbase (se 3 (by rfl) ⟨56396, by rfl⟩ : syracuseStep 300781 = 112793) (by norm_num)
theorem B399173 : Blo 279826 399173 := bbase (se 4 (by rfl) ⟨37422, by rfl⟩ : syracuseStep 399173 = 74845) (by norm_num)
theorem B726869 : Blo 279826 726869 := bbase (se 9 (by rfl) ⟨2129, by rfl⟩ : syracuseStep 726869 = 4259) (by norm_num)
theorem B956501 : Blo 279826 956501 := bbase (se 8 (by rfl) ⟨5604, by rfl⟩ : syracuseStep 956501 = 11209) (by norm_num)
theorem B301153 : Blo 279826 301153 := bbase (se 2 (by rfl) ⟨112932, by rfl⟩ : syracuseStep 301153 = 225865) (by norm_num)
theorem B760229 : Blo 279826 760229 := bbase (se 4 (by rfl) ⟨71271, by rfl⟩ : syracuseStep 760229 = 142543) (by norm_num)
theorem B301529 : Blo 279826 301529 := bbase (se 2 (by rfl) ⟨113073, by rfl⟩ : syracuseStep 301529 = 226147) (by norm_num)
theorem B956933 : Blo 279826 956933 := bbase (se 4 (by rfl) ⟨89712, by rfl⟩ : syracuseStep 956933 = 179425) (by norm_num)
theorem B301601 : Blo 279826 301601 := bbase (se 2 (by rfl) ⟨113100, by rfl⟩ : syracuseStep 301601 = 226201) (by norm_num)
theorem B399925 : Blo 279826 399925 := bbase (se 5 (by rfl) ⟨18746, by rfl⟩ : syracuseStep 399925 = 37493) (by norm_num)
theorem B301789 : Blo 279826 301789 := bbase (se 3 (by rfl) ⟨56585, by rfl⟩ : syracuseStep 301789 = 113171) (by norm_num)
theorem B760661 : Blo 279826 760661 := bbase (se 9 (by rfl) ⟨2228, by rfl⟩ : syracuseStep 760661 = 4457) (by norm_num)
theorem B629621 : Blo 279826 629621 := bbase (se 5 (by rfl) ⟨29513, by rfl⟩ : syracuseStep 629621 = 59027) (by norm_num)
theorem B301973 : Blo 279826 301973 := bbase (se 6 (by rfl) ⟨7077, by rfl⟩ : syracuseStep 301973 = 14155) (by norm_num)
theorem B531373 : Blo 279826 531373 := bbase (se 3 (by rfl) ⟨99632, by rfl⟩ : syracuseStep 531373 = 199265) (by norm_num)
theorem B957365 : Blo 279826 957365 := bbase (se 5 (by rfl) ⟨44876, by rfl⟩ : syracuseStep 957365 = 89753) (by norm_num)
theorem B629693 : Blo 279826 629693 := bbase (se 3 (by rfl) ⟨118067, by rfl⟩ : syracuseStep 629693 = 236135) (by norm_num)
theorem B629765 : Blo 279826 629765 := bbase (se 4 (by rfl) ⟨59040, by rfl⟩ : syracuseStep 629765 = 118081) (by norm_num)
theorem B531517 : Blo 279826 531517 := bbase (se 3 (by rfl) ⟨99659, by rfl⟩ : syracuseStep 531517 = 199319) (by norm_num)
theorem B629837 : Blo 279826 629837 := bbase (se 3 (by rfl) ⟨118094, by rfl⟩ : syracuseStep 629837 = 236189) (by norm_num)
theorem B629909 : Blo 279826 629909 := bbase (se 6 (by rfl) ⟨14763, by rfl⟩ : syracuseStep 629909 = 29527) (by norm_num)
theorem B2399381 : Blo 279826 2399381 := bbase (se 6 (by rfl) ⟨56235, by rfl⟩ : syracuseStep 2399381 = 112471) (by norm_num)
theorem B629981 : Blo 279826 629981 := bbase (se 3 (by rfl) ⟨118121, by rfl⟩ : syracuseStep 629981 = 236243) (by norm_num)
theorem B531677 : Blo 279826 531677 := bbase (se 3 (by rfl) ⟨99689, by rfl⟩ : syracuseStep 531677 = 199379) (by norm_num)
theorem B630053 : Blo 279826 630053 := bbase (se 4 (by rfl) ⟨59067, by rfl⟩ : syracuseStep 630053 = 118135) (by norm_num)
theorem B400717 : Blo 279826 400717 := bbase (se 3 (by rfl) ⟨75134, by rfl⟩ : syracuseStep 400717 = 150269) (by norm_num)
theorem B1613141 : Blo 279826 1613141 := bbase (se 11 (by rfl) ⟨1181, by rfl⟩ : syracuseStep 1613141 = 2363) (by norm_num)
theorem B957797 : Blo 279826 957797 := bbase (se 4 (by rfl) ⟨89793, by rfl⟩ : syracuseStep 957797 = 179587) (by norm_num)
theorem B630125 : Blo 279826 630125 := bbase (se 3 (by rfl) ⟨118148, by rfl⟩ : syracuseStep 630125 = 236297) (by norm_num)
theorem B531821 : Blo 279826 531821 := bbase (se 3 (by rfl) ⟨99716, by rfl⟩ : syracuseStep 531821 = 199433) (by norm_num)
theorem B630197 : Blo 279826 630197 := bbase (se 5 (by rfl) ⟨29540, by rfl⟩ : syracuseStep 630197 = 59081) (by norm_num)
theorem B630269 : Blo 279826 630269 := bbase (se 3 (by rfl) ⟨118175, by rfl⟩ : syracuseStep 630269 = 236351) (by norm_num)
theorem B630341 : Blo 279826 630341 := bbase (se 4 (by rfl) ⟨59094, by rfl⟩ : syracuseStep 630341 = 118189) (by norm_num)
theorem B1121861 : Blo 279826 1121861 := bbase (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) (by norm_num)
theorem B302725 : Blo 279826 302725 := bbase (se 4 (by rfl) ⟨28380, by rfl⟩ : syracuseStep 302725 = 56761) (by norm_num)
theorem B630413 : Blo 279826 630413 := bbase (se 3 (by rfl) ⟨118202, by rfl⟩ : syracuseStep 630413 = 236405) (by norm_num)
theorem B532109 : Blo 279826 532109 := bbase (se 3 (by rfl) ⟨99770, by rfl⟩ : syracuseStep 532109 = 199541) (by norm_num)
theorem B401053 : Blo 279826 401053 := bbase (se 3 (by rfl) ⟨75197, by rfl⟩ : syracuseStep 401053 = 150395) (by norm_num)
theorem B597701 : Blo 279826 597701 := bbase (se 4 (by rfl) ⟨56034, by rfl⟩ : syracuseStep 597701 = 112069) (by norm_num)
theorem B302797 : Blo 279826 302797 := bbase (se 3 (by rfl) ⟨56774, by rfl⟩ : syracuseStep 302797 = 113549) (by norm_num)
theorem B630485 : Blo 279826 630485 := bbase (se 7 (by rfl) ⟨7388, by rfl⟩ : syracuseStep 630485 = 14777) (by norm_num)
theorem B2989781 : Blo 279826 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B1154837 : Blo 279826 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B630557 : Blo 279826 630557 := bbase (se 3 (by rfl) ⟨118229, by rfl⟩ : syracuseStep 630557 = 236459) (by norm_num)
theorem B532261 : Blo 279826 532261 := bbase (se 4 (by rfl) ⟨49899, by rfl⟩ : syracuseStep 532261 = 99799) (by norm_num)
theorem B1417013 : Blo 279826 1417013 := bbase (se 5 (by rfl) ⟨66422, by rfl⟩ : syracuseStep 1417013 = 132845) (by norm_num)
theorem B630629 : Blo 279826 630629 := bbase (se 4 (by rfl) ⟨59121, by rfl⟩ : syracuseStep 630629 = 118243) (by norm_num)
theorem B401269 : Blo 279826 401269 := bbase (se 5 (by rfl) ⟨18809, by rfl⟩ : syracuseStep 401269 = 37619) (by norm_num)
theorem B302977 : Blo 279826 302977 := bbase (se 2 (by rfl) ⟨113616, by rfl⟩ : syracuseStep 302977 = 227233) (by norm_num)
theorem B630701 : Blo 279826 630701 := bbase (se 3 (by rfl) ⟨118256, by rfl⟩ : syracuseStep 630701 = 236513) (by norm_num)
theorem B303049 : Blo 279826 303049 := bbase (se 2 (by rfl) ⟨113643, by rfl⟩ : syracuseStep 303049 = 227287) (by norm_num)
theorem B630773 : Blo 279826 630773 := bbase (se 5 (by rfl) ⟨29567, by rfl⟩ : syracuseStep 630773 = 59135) (by norm_num)
theorem B1351669 : Blo 279826 1351669 := bbase (se 5 (by rfl) ⟨63359, by rfl⟩ : syracuseStep 1351669 = 126719) (by norm_num)
theorem B630845 : Blo 279826 630845 := bbase (se 3 (by rfl) ⟨118283, by rfl⟩ : syracuseStep 630845 = 236567) (by norm_num)
theorem B532565 : Blo 279826 532565 := bbase (se 8 (by rfl) ⟨3120, by rfl⟩ : syracuseStep 532565 = 6241) (by norm_num)
theorem B630917 : Blo 279826 630917 := bbase (se 4 (by rfl) ⟨59148, by rfl⟩ : syracuseStep 630917 = 118297) (by norm_num)
theorem B598205 : Blo 279826 598205 := bbase (se 3 (by rfl) ⟨112163, by rfl⟩ : syracuseStep 598205 = 224327) (by norm_num)
theorem B598213 : Blo 279826 598213 := bbase (se 4 (by rfl) ⟨56082, by rfl⟩ : syracuseStep 598213 = 112165) (by norm_num)
theorem B630989 : Blo 279826 630989 := bbase (se 3 (by rfl) ⟨118310, by rfl⟩ : syracuseStep 630989 = 236621) (by norm_num)
theorem B401645 : Blo 279826 401645 := bbase (se 3 (by rfl) ⟨75308, by rfl⟩ : syracuseStep 401645 = 150617) (by norm_num)
theorem B631061 : Blo 279826 631061 := bbase (se 6 (by rfl) ⟨14790, by rfl⟩ : syracuseStep 631061 = 29581) (by norm_num)
theorem B631133 : Blo 279826 631133 := bbase (se 3 (by rfl) ⟨118337, by rfl⟩ : syracuseStep 631133 = 236675) (by norm_num)
theorem B1286533 : Blo 279826 1286533 := bbase (se 4 (by rfl) ⟨120612, by rfl⟩ : syracuseStep 1286533 = 241225) (by norm_num)
theorem B631205 : Blo 279826 631205 := bbase (se 4 (by rfl) ⟨59175, by rfl⟩ : syracuseStep 631205 = 118351) (by norm_num)
theorem B631277 : Blo 279826 631277 := bbase (se 3 (by rfl) ⟨118364, by rfl⟩ : syracuseStep 631277 = 236729) (by norm_num)
theorem B631349 : Blo 279826 631349 := bbase (se 5 (by rfl) ⟨29594, by rfl⟩ : syracuseStep 631349 = 59189) (by norm_num)
theorem B631421 : Blo 279826 631421 := bbase (se 3 (by rfl) ⟨118391, by rfl⟩ : syracuseStep 631421 = 236783) (by norm_num)
theorem B631493 : Blo 279826 631493 := bbase (se 4 (by rfl) ⟨59202, by rfl⟩ : syracuseStep 631493 = 118405) (by norm_num)
theorem B631565 : Blo 279826 631565 := bbase (se 3 (by rfl) ⟨118418, by rfl⟩ : syracuseStep 631565 = 236837) (by norm_num)
theorem B533317 : Blo 279826 533317 := bbase (se 4 (by rfl) ⟨49998, by rfl⟩ : syracuseStep 533317 = 99997) (by norm_num)
theorem B631637 : Blo 279826 631637 := bbase (se 9 (by rfl) ⟨1850, by rfl⟩ : syracuseStep 631637 = 3701) (by norm_num)
theorem B336745 : Blo 279826 336745 := bbase (se 2 (by rfl) ⟨126279, by rfl⟩ : syracuseStep 336745 = 252559) (by norm_num)
theorem B631709 : Blo 279826 631709 := bbase (se 3 (by rfl) ⟨118445, by rfl⟩ : syracuseStep 631709 = 236891) (by norm_num)
theorem B533461 : Blo 279826 533461 := bbase (se 7 (by rfl) ⟨6251, by rfl⟩ : syracuseStep 533461 = 12503) (by norm_num)
theorem B631781 : Blo 279826 631781 := bbase (se 4 (by rfl) ⟨59229, by rfl⟩ : syracuseStep 631781 = 118459) (by norm_num)
theorem B631853 : Blo 279826 631853 := bbase (se 3 (by rfl) ⟨118472, by rfl⟩ : syracuseStep 631853 = 236945) (by norm_num)
theorem B1418309 : Blo 279826 1418309 := bbase (se 4 (by rfl) ⟨132966, by rfl⟩ : syracuseStep 1418309 = 265933) (by norm_num)
theorem B631925 : Blo 279826 631925 := bbase (se 5 (by rfl) ⟨29621, by rfl⟩ : syracuseStep 631925 = 59243) (by norm_num)
theorem B533621 : Blo 279826 533621 := bbase (se 5 (by rfl) ⟨25013, by rfl⟩ : syracuseStep 533621 = 50027) (by norm_num)
theorem B631997 : Blo 279826 631997 := bbase (se 3 (by rfl) ⟨118499, by rfl⟩ : syracuseStep 631997 = 236999) (by norm_num)
theorem B632069 : Blo 279826 632069 := bbase (se 4 (by rfl) ⟨59256, by rfl⟩ : syracuseStep 632069 = 118513) (by norm_num)
theorem B533765 : Blo 279826 533765 := bbase (se 4 (by rfl) ⟨50040, by rfl⟩ : syracuseStep 533765 = 100081) (by norm_num)
theorem B599341 : Blo 279826 599341 := bbase (se 3 (by rfl) ⟨112376, by rfl⟩ : syracuseStep 599341 = 224753) (by norm_num)
theorem B632141 : Blo 279826 632141 := bbase (se 3 (by rfl) ⟨118526, by rfl⟩ : syracuseStep 632141 = 237053) (by norm_num)
theorem B632213 : Blo 279826 632213 := bbase (se 6 (by rfl) ⟨14817, by rfl⟩ : syracuseStep 632213 = 29635) (by norm_num)
theorem B632285 : Blo 279826 632285 := bbase (se 3 (by rfl) ⟨118553, by rfl⟩ : syracuseStep 632285 = 237107) (by norm_num)
theorem B632357 : Blo 279826 632357 := bbase (se 4 (by rfl) ⟨59283, by rfl⟩ : syracuseStep 632357 = 118567) (by norm_num)
theorem B534053 : Blo 279826 534053 := bbase (se 4 (by rfl) ⟨50067, by rfl⟩ : syracuseStep 534053 = 100135) (by norm_num)
theorem B632429 : Blo 279826 632429 := bbase (se 3 (by rfl) ⟨118580, by rfl⟩ : syracuseStep 632429 = 237161) (by norm_num)
theorem B403069 : Blo 279826 403069 := bbase (se 3 (by rfl) ⟨75575, by rfl⟩ : syracuseStep 403069 = 151151) (by norm_num)
theorem B599717 : Blo 279826 599717 := bbase (se 4 (by rfl) ⟨56223, by rfl⟩ : syracuseStep 599717 = 112447) (by norm_num)
theorem B632501 : Blo 279826 632501 := bbase (se 5 (by rfl) ⟨29648, by rfl⟩ : syracuseStep 632501 = 59297) (by norm_num)
theorem B534205 : Blo 279826 534205 := bbase (se 3 (by rfl) ⟨100163, by rfl⟩ : syracuseStep 534205 = 200327) (by norm_num)
theorem B632573 : Blo 279826 632573 := bbase (se 3 (by rfl) ⟨118607, by rfl⟩ : syracuseStep 632573 = 237215) (by norm_num)
theorem B632645 : Blo 279826 632645 := bbase (se 4 (by rfl) ⟨59310, by rfl⟩ : syracuseStep 632645 = 118621) (by norm_num)
theorem B1517429 : Blo 279826 1517429 := bbase (se 5 (by rfl) ⟨71129, by rfl⟩ : syracuseStep 1517429 = 142259) (by norm_num)
theorem B632717 : Blo 279826 632717 := bbase (se 3 (by rfl) ⟨118634, by rfl⟩ : syracuseStep 632717 = 237269) (by norm_num)
theorem B305093 : Blo 279826 305093 := bbase (se 4 (by rfl) ⟨28602, by rfl⟩ : syracuseStep 305093 = 57205) (by norm_num)
theorem B632789 : Blo 279826 632789 := bbase (se 7 (by rfl) ⟨7415, by rfl⟩ : syracuseStep 632789 = 14831) (by norm_num)
theorem B337889 : Blo 279826 337889 := bbase (se 2 (by rfl) ⟨126708, by rfl⟩ : syracuseStep 337889 = 253417) (by norm_num)
theorem B534509 : Blo 279826 534509 := bbase (se 3 (by rfl) ⟨100220, by rfl⟩ : syracuseStep 534509 = 200441) (by norm_num)
theorem B337937 : Blo 279826 337937 := bbase (se 2 (by rfl) ⟨126726, by rfl⟩ : syracuseStep 337937 = 253453) (by norm_num)
theorem B632861 : Blo 279826 632861 := bbase (se 3 (by rfl) ⟨118661, by rfl⟩ : syracuseStep 632861 = 237323) (by norm_num)
theorem B632933 : Blo 279826 632933 := bbase (se 4 (by rfl) ⟨59337, by rfl⟩ : syracuseStep 632933 = 118675) (by norm_num)
theorem B338033 : Blo 279826 338033 := bbase (se 2 (by rfl) ⟨126762, by rfl⟩ : syracuseStep 338033 = 253525) (by norm_num)
theorem B633005 : Blo 279826 633005 := bbase (se 3 (by rfl) ⟨118688, by rfl⟩ : syracuseStep 633005 = 237377) (by norm_num)
theorem B305353 : Blo 279826 305353 := bbase (se 2 (by rfl) ⟨114507, by rfl⟩ : syracuseStep 305353 = 229015) (by norm_num)
theorem B403661 : Blo 279826 403661 := bbase (se 3 (by rfl) ⟨75686, by rfl⟩ : syracuseStep 403661 = 151373) (by norm_num)
theorem B2697461 : Blo 279826 2697461 := bbase (se 5 (by rfl) ⟨126443, by rfl⟩ : syracuseStep 2697461 = 252887) (by norm_num)
theorem B633077 : Blo 279826 633077 := bbase (se 5 (by rfl) ⟨29675, by rfl⟩ : syracuseStep 633077 = 59351) (by norm_num)
theorem B338197 : Blo 279826 338197 := bbase (se 6 (by rfl) ⟨7926, by rfl⟩ : syracuseStep 338197 = 15853) (by norm_num)
theorem B3352853 : Blo 279826 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B403741 : Blo 279826 403741 := bbase (se 3 (by rfl) ⟨75701, by rfl⟩ : syracuseStep 403741 = 151403) (by norm_num)
theorem B633149 : Blo 279826 633149 := bbase (se 3 (by rfl) ⟨118715, by rfl⟩ : syracuseStep 633149 = 237431) (by norm_num)
theorem B1419605 : Blo 279826 1419605 := bbase (se 10 (by rfl) ⟨2079, by rfl⟩ : syracuseStep 1419605 = 4159) (by norm_num)
theorem B633221 : Blo 279826 633221 := bbase (se 4 (by rfl) ⟨59364, by rfl⟩ : syracuseStep 633221 = 118729) (by norm_num)
theorem B403861 : Blo 279826 403861 := bbase (se 6 (by rfl) ⟨9465, by rfl⟩ : syracuseStep 403861 = 18931) (by norm_num)
theorem B633293 : Blo 279826 633293 := bbase (se 3 (by rfl) ⟨118742, by rfl⟩ : syracuseStep 633293 = 237485) (by norm_num)
theorem B338413 : Blo 279826 338413 := bbase (se 3 (by rfl) ⟨63452, by rfl⟩ : syracuseStep 338413 = 126905) (by norm_num)
theorem B403957 : Blo 279826 403957 := bbase (se 5 (by rfl) ⟨18935, by rfl⟩ : syracuseStep 403957 = 37871) (by norm_num)
theorem B633365 : Blo 279826 633365 := bbase (se 6 (by rfl) ⟨14844, by rfl⟩ : syracuseStep 633365 = 29689) (by norm_num)
theorem B633437 : Blo 279826 633437 := bbase (se 3 (by rfl) ⟨118769, by rfl⟩ : syracuseStep 633437 = 237539) (by norm_num)
theorem B338581 : Blo 279826 338581 := bbase (se 6 (by rfl) ⟨7935, by rfl⟩ : syracuseStep 338581 = 15871) (by norm_num)
theorem B633509 : Blo 279826 633509 := bbase (se 4 (by rfl) ⟨59391, by rfl⟩ : syracuseStep 633509 = 118783) (by norm_num)
theorem B1354421 : Blo 279826 1354421 := bbase (se 5 (by rfl) ⟨63488, by rfl⟩ : syracuseStep 1354421 = 126977) (by norm_num)
theorem B535261 : Blo 279826 535261 := bbase (se 3 (by rfl) ⟨100361, by rfl⟩ : syracuseStep 535261 = 200723) (by norm_num)
theorem B633581 : Blo 279826 633581 := bbase (se 3 (by rfl) ⟨118796, by rfl⟩ : syracuseStep 633581 = 237593) (by norm_num)
theorem B633653 : Blo 279826 633653 := bbase (se 5 (by rfl) ⟨29702, by rfl⟩ : syracuseStep 633653 = 59405) (by norm_num)
theorem B535405 : Blo 279826 535405 := bbase (se 3 (by rfl) ⟨100388, by rfl⟩ : syracuseStep 535405 = 200777) (by norm_num)
theorem B633725 : Blo 279826 633725 := bbase (se 3 (by rfl) ⟨118823, by rfl⟩ : syracuseStep 633725 = 237647) (by norm_num)
theorem B404389 : Blo 279826 404389 := bbase (se 4 (by rfl) ⟨37911, by rfl⟩ : syracuseStep 404389 = 75823) (by norm_num)
theorem B633797 : Blo 279826 633797 := bbase (se 4 (by rfl) ⟨59418, by rfl⟩ : syracuseStep 633797 = 118837) (by norm_num)
theorem B633869 : Blo 279826 633869 := bbase (se 3 (by rfl) ⟨118850, by rfl⟩ : syracuseStep 633869 = 237701) (by norm_num)
theorem B535565 : Blo 279826 535565 := bbase (se 3 (by rfl) ⟨100418, by rfl⟩ : syracuseStep 535565 = 200837) (by norm_num)
theorem B633941 : Blo 279826 633941 := bbase (se 8 (by rfl) ⟨3714, by rfl⟩ : syracuseStep 633941 = 7429) (by norm_num)
theorem B797845 : Blo 279826 797845 := bbase (se 6 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 797845 = 37399) (by norm_num)
theorem B634013 : Blo 279826 634013 := bbase (se 3 (by rfl) ⟨118877, by rfl⟩ : syracuseStep 634013 = 237755) (by norm_num)
theorem B535709 : Blo 279826 535709 := bbase (se 3 (by rfl) ⟨100445, by rfl⟩ : syracuseStep 535709 = 200891) (by norm_num)
theorem B339109 : Blo 279826 339109 := bbase (se 4 (by rfl) ⟨31791, by rfl⟩ : syracuseStep 339109 = 63583) (by norm_num)
theorem B568549 : Blo 279826 568549 := bbase (se 4 (by rfl) ⟨53301, by rfl⟩ : syracuseStep 568549 = 106603) (by norm_num)
theorem B634085 : Blo 279826 634085 := bbase (se 4 (by rfl) ⟨59445, by rfl⟩ : syracuseStep 634085 = 118891) (by norm_num)
theorem B601357 : Blo 279826 601357 := bbase (se 3 (by rfl) ⟨112754, by rfl⟩ : syracuseStep 601357 = 225509) (by norm_num)
theorem B634157 : Blo 279826 634157 := bbase (se 3 (by rfl) ⟨118904, by rfl⟩ : syracuseStep 634157 = 237809) (by norm_num)
theorem B798005 : Blo 279826 798005 := bbase (se 5 (by rfl) ⟨37406, by rfl⟩ : syracuseStep 798005 = 74813) (by norm_num)
theorem B634229 : Blo 279826 634229 := bbase (se 5 (by rfl) ⟨29729, by rfl⟩ : syracuseStep 634229 = 59459) (by norm_num)
theorem B2174357 : Blo 279826 2174357 := bbase (se 6 (by rfl) ⟨50961, by rfl⟩ : syracuseStep 2174357 = 101923) (by norm_num)
theorem B634301 : Blo 279826 634301 := bbase (se 3 (by rfl) ⟨118931, by rfl⟩ : syracuseStep 634301 = 237863) (by norm_num)
theorem B535997 : Blo 279826 535997 := bbase (se 3 (by rfl) ⟨100499, by rfl⟩ : syracuseStep 535997 = 200999) (by norm_num)
theorem B634373 : Blo 279826 634373 := bbase (se 4 (by rfl) ⟨59472, by rfl⟩ : syracuseStep 634373 = 118945) (by norm_num)
theorem B798245 : Blo 279826 798245 := bbase (se 4 (by rfl) ⟨74835, by rfl⟩ : syracuseStep 798245 = 149671) (by norm_num)
theorem B405037 : Blo 279826 405037 := bbase (se 3 (by rfl) ⟨75944, by rfl⟩ : syracuseStep 405037 = 151889) (by norm_num)
theorem B634445 : Blo 279826 634445 := bbase (se 3 (by rfl) ⟨118958, by rfl⟩ : syracuseStep 634445 = 237917) (by norm_num)
theorem B536149 : Blo 279826 536149 := bbase (se 8 (by rfl) ⟨3141, by rfl⟩ : syracuseStep 536149 = 6283) (by norm_num)
theorem B1420901 : Blo 279826 1420901 := bbase (se 4 (by rfl) ⟨133209, by rfl⟩ : syracuseStep 1420901 = 266419) (by norm_num)
theorem B896629 : Blo 279826 896629 := bbase (se 5 (by rfl) ⟨42029, by rfl⟩ : syracuseStep 896629 = 84059) (by norm_num)
theorem B568957 : Blo 279826 568957 := bbase (se 3 (by rfl) ⟨106679, by rfl⟩ : syracuseStep 568957 = 213359) (by norm_num)
theorem B634517 : Blo 279826 634517 := bbase (se 6 (by rfl) ⟨14871, by rfl⟩ : syracuseStep 634517 = 29743) (by norm_num)
theorem B1027765 : Blo 279826 1027765 := bbase (se 5 (by rfl) ⟨48176, by rfl⟩ : syracuseStep 1027765 = 96353) (by norm_num)
theorem B700093 : Blo 279826 700093 := bbase (se 3 (by rfl) ⟨131267, by rfl⟩ : syracuseStep 700093 = 262535) (by norm_num)
theorem B634589 : Blo 279826 634589 := bbase (se 3 (by rfl) ⟨118985, by rfl⟩ : syracuseStep 634589 = 237971) (by norm_num)
theorem B798437 : Blo 279826 798437 := bbase (se 4 (by rfl) ⟨74853, by rfl⟩ : syracuseStep 798437 = 149707) (by norm_num)
theorem B634661 : Blo 279826 634661 := bbase (se 4 (by rfl) ⟨59499, by rfl⟩ : syracuseStep 634661 = 118999) (by norm_num)
theorem B634733 : Blo 279826 634733 := bbase (se 3 (by rfl) ⟨119012, by rfl⟩ : syracuseStep 634733 = 238025) (by norm_num)
theorem B536453 : Blo 279826 536453 := bbase (se 4 (by rfl) ⟨50292, by rfl⟩ : syracuseStep 536453 = 100585) (by norm_num)
theorem B634805 : Blo 279826 634805 := bbase (se 5 (by rfl) ⟨29756, by rfl⟩ : syracuseStep 634805 = 59513) (by norm_num)
theorem B634877 : Blo 279826 634877 := bbase (se 3 (by rfl) ⟨119039, by rfl⟩ : syracuseStep 634877 = 238079) (by norm_num)
theorem B634949 : Blo 279826 634949 := bbase (se 4 (by rfl) ⟨59526, by rfl⟩ : syracuseStep 634949 = 119053) (by norm_num)
theorem B3223637 : Blo 279826 3223637 := bbase (se 8 (by rfl) ⟨18888, by rfl⟩ : syracuseStep 3223637 = 37777) (by norm_num)
theorem B602245 : Blo 279826 602245 := bbase (se 4 (by rfl) ⟨56460, by rfl⟩ : syracuseStep 602245 = 112921) (by norm_num)
theorem B635021 : Blo 279826 635021 := bbase (se 3 (by rfl) ⟨119066, by rfl⟩ : syracuseStep 635021 = 238133) (by norm_num)
theorem B635093 : Blo 279826 635093 := bbase (se 7 (by rfl) ⟨7442, by rfl⟩ : syracuseStep 635093 = 14885) (by norm_num)
theorem B340205 : Blo 279826 340205 := bbase (se 3 (by rfl) ⟨63788, by rfl⟩ : syracuseStep 340205 = 127577) (by norm_num)
theorem B635165 : Blo 279826 635165 := bbase (se 3 (by rfl) ⟨119093, by rfl⟩ : syracuseStep 635165 = 238187) (by norm_num)
theorem B635237 : Blo 279826 635237 := bbase (se 4 (by rfl) ⟨59553, by rfl⟩ : syracuseStep 635237 = 119107) (by norm_num)
theorem B569717 : Blo 279826 569717 := bbase (se 5 (by rfl) ⟨26705, by rfl⟩ : syracuseStep 569717 = 53411) (by norm_num)
theorem B635309 : Blo 279826 635309 := bbase (se 3 (by rfl) ⟨119120, by rfl⟩ : syracuseStep 635309 = 238241) (by norm_num)
theorem B635381 : Blo 279826 635381 := bbase (se 5 (by rfl) ⟨29783, by rfl⟩ : syracuseStep 635381 = 59567) (by norm_num)
theorem B2142773 : Blo 279826 2142773 := bbase (se 5 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 2142773 = 200885) (by norm_num)
theorem B635453 : Blo 279826 635453 := bbase (se 3 (by rfl) ⟨119147, by rfl⟩ : syracuseStep 635453 = 238295) (by norm_num)
theorem B9810517 : Blo 279826 9810517 := bbase (se 8 (by rfl) ⟨57483, by rfl⟩ : syracuseStep 9810517 = 114967) (by norm_num)
theorem B602741 : Blo 279826 602741 := bbase (se 5 (by rfl) ⟨28253, by rfl⟩ : syracuseStep 602741 = 56507) (by norm_num)
theorem B537205 : Blo 279826 537205 := bbase (se 5 (by rfl) ⟨25181, by rfl⟩ : syracuseStep 537205 = 50363) (by norm_num)
theorem B635525 : Blo 279826 635525 := bbase (se 4 (by rfl) ⟨59580, by rfl⟩ : syracuseStep 635525 = 119161) (by norm_num)
theorem B799429 : Blo 279826 799429 := bbase (se 4 (by rfl) ⟨74946, by rfl⟩ : syracuseStep 799429 = 149893) (by norm_num)
theorem B635597 : Blo 279826 635597 := bbase (se 3 (by rfl) ⟨119174, by rfl⟩ : syracuseStep 635597 = 238349) (by norm_num)
theorem B537349 : Blo 279826 537349 := bbase (se 4 (by rfl) ⟨50376, by rfl⟩ : syracuseStep 537349 = 100753) (by norm_num)
theorem B635669 : Blo 279826 635669 := bbase (se 6 (by rfl) ⟨14898, by rfl⟩ : syracuseStep 635669 = 29797) (by norm_num)
theorem B635741 : Blo 279826 635741 := bbase (se 3 (by rfl) ⟨119201, by rfl⟩ : syracuseStep 635741 = 238403) (by norm_num)
theorem B1422197 : Blo 279826 1422197 := bbase (se 5 (by rfl) ⟨66665, by rfl⟩ : syracuseStep 1422197 = 133331) (by norm_num)
theorem B340897 : Blo 279826 340897 := bbase (se 2 (by rfl) ⟨127836, by rfl⟩ : syracuseStep 340897 = 255673) (by norm_num)
theorem B635813 : Blo 279826 635813 := bbase (se 4 (by rfl) ⟨59607, by rfl⟩ : syracuseStep 635813 = 119215) (by norm_num)
theorem B537509 : Blo 279826 537509 := bbase (se 4 (by rfl) ⟨50391, by rfl⟩ : syracuseStep 537509 = 100783) (by norm_num)
theorem B635885 : Blo 279826 635885 := bbase (se 3 (by rfl) ⟨119228, by rfl⟩ : syracuseStep 635885 = 238457) (by norm_num)
theorem B1356821 : Blo 279826 1356821 := bbase (se 6 (by rfl) ⟨31800, by rfl⟩ : syracuseStep 1356821 = 63601) (by norm_num)
theorem B766997 : Blo 279826 766997 := bbase (se 6 (by rfl) ⟨17976, by rfl⟩ : syracuseStep 766997 = 35953) (by norm_num)
theorem B635957 : Blo 279826 635957 := bbase (se 5 (by rfl) ⟨29810, by rfl⟩ : syracuseStep 635957 = 59621) (by norm_num)
theorem B537653 : Blo 279826 537653 := bbase (se 5 (by rfl) ⟨25202, by rfl⟩ : syracuseStep 537653 = 50405) (by norm_num)
theorem B1815605 : Blo 279826 1815605 := bbase (se 5 (by rfl) ⟨85106, by rfl⟩ : syracuseStep 1815605 = 170213) (by norm_num)
theorem B865349 : Blo 279826 865349 := bbase (se 4 (by rfl) ⟨81126, by rfl⟩ : syracuseStep 865349 = 162253) (by norm_num)
theorem B636029 : Blo 279826 636029 := bbase (se 3 (by rfl) ⟨119255, by rfl⟩ : syracuseStep 636029 = 238511) (by norm_num)
theorem B504973 : Blo 279826 504973 := bbase (se 3 (by rfl) ⟨94682, by rfl⟩ : syracuseStep 504973 = 189365) (by norm_num)
theorem B636101 : Blo 279826 636101 := bbase (se 4 (by rfl) ⟨59634, by rfl⟩ : syracuseStep 636101 = 119269) (by norm_num)
theorem B472277 : Blo 279826 472277 := bbase (se 7 (by rfl) ⟨5534, by rfl⟩ : syracuseStep 472277 = 11069) (by norm_num)
theorem B636173 : Blo 279826 636173 := bbase (se 3 (by rfl) ⟨119282, by rfl⟩ : syracuseStep 636173 = 238565) (by norm_num)
theorem B472405 : Blo 279826 472405 := bbase (se 13 (by rfl) ⟨86, by rfl⟩ : syracuseStep 472405 = 173) (by norm_num)
theorem B636245 : Blo 279826 636245 := bbase (se 13 (by rfl) ⟨116, by rfl⟩ : syracuseStep 636245 = 233) (by norm_num)
theorem B537941 : Blo 279826 537941 := bbase (se 13 (by rfl) ⟨98, by rfl⟩ : syracuseStep 537941 = 197) (by norm_num)
theorem B865637 : Blo 279826 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B636317 : Blo 279826 636317 := bbase (se 3 (by rfl) ⟨119309, by rfl⟩ : syracuseStep 636317 = 238619) (by norm_num)
theorem B472493 : Blo 279826 472493 := bbase (se 3 (by rfl) ⟨88592, by rfl⟩ : syracuseStep 472493 = 177185) (by norm_num)
theorem B603605 : Blo 279826 603605 := bbase (se 7 (by rfl) ⟨7073, by rfl⟩ : syracuseStep 603605 = 14147) (by norm_num)
theorem B636389 : Blo 279826 636389 := bbase (se 4 (by rfl) ⟨59661, by rfl⟩ : syracuseStep 636389 = 119323) (by norm_num)
theorem B538093 : Blo 279826 538093 := bbase (se 3 (by rfl) ⟨100892, by rfl⟩ : syracuseStep 538093 = 201785) (by norm_num)
theorem B505349 : Blo 279826 505349 := bbase (se 4 (by rfl) ⟨47376, by rfl⟩ : syracuseStep 505349 = 94753) (by norm_num)
theorem B472621 : Blo 279826 472621 := bbase (se 3 (by rfl) ⟨88616, by rfl⟩ : syracuseStep 472621 = 177233) (by norm_num)
theorem B636461 : Blo 279826 636461 := bbase (se 3 (by rfl) ⟨119336, by rfl⟩ : syracuseStep 636461 = 238673) (by norm_num)
theorem B603749 : Blo 279826 603749 := bbase (se 4 (by rfl) ⟨56601, by rfl⟩ : syracuseStep 603749 = 113203) (by norm_num)
theorem B1062517 : Blo 279826 1062517 := bbase (se 5 (by rfl) ⟨49805, by rfl⟩ : syracuseStep 1062517 = 99611) (by norm_num)
theorem B636533 : Blo 279826 636533 := bbase (se 5 (by rfl) ⟨29837, by rfl⟩ : syracuseStep 636533 = 59675) (by norm_num)
theorem B472709 : Blo 279826 472709 := bbase (se 4 (by rfl) ⟨44316, by rfl⟩ : syracuseStep 472709 = 88633) (by norm_num)
theorem B636605 : Blo 279826 636605 := bbase (se 3 (by rfl) ⟨119363, by rfl⟩ : syracuseStep 636605 = 238727) (by norm_num)
theorem B472837 : Blo 279826 472837 := bbase (se 4 (by rfl) ⟨44328, by rfl⟩ : syracuseStep 472837 = 88657) (by norm_num)
theorem B636677 : Blo 279826 636677 := bbase (se 4 (by rfl) ⟨59688, by rfl⟩ : syracuseStep 636677 = 119377) (by norm_num)
theorem B800533 : Blo 279826 800533 := bbase (se 6 (by rfl) ⟨18762, by rfl⟩ : syracuseStep 800533 = 37525) (by norm_num)
theorem B538397 : Blo 279826 538397 := bbase (se 3 (by rfl) ⟨100949, by rfl⟩ : syracuseStep 538397 = 201899) (by norm_num)
theorem B636749 : Blo 279826 636749 := bbase (se 3 (by rfl) ⟨119390, by rfl⟩ : syracuseStep 636749 = 238781) (by norm_num)
theorem B472925 : Blo 279826 472925 := bbase (se 3 (by rfl) ⟨88673, by rfl⟩ : syracuseStep 472925 = 177347) (by norm_num)
theorem B538501 : Blo 279826 538501 := bbase (se 4 (by rfl) ⟨50484, by rfl⟩ : syracuseStep 538501 = 100969) (by norm_num)
theorem B636821 : Blo 279826 636821 := bbase (se 6 (by rfl) ⟨14925, by rfl⟩ : syracuseStep 636821 = 29851) (by norm_num)
theorem B1062821 : Blo 279826 1062821 := bbase (se 4 (by rfl) ⟨99639, by rfl⟩ : syracuseStep 1062821 = 199279) (by norm_num)
theorem B473053 : Blo 279826 473053 := bbase (se 3 (by rfl) ⟨88697, by rfl⟩ : syracuseStep 473053 = 177395) (by norm_num)
theorem B636893 : Blo 279826 636893 := bbase (se 3 (by rfl) ⟨119417, by rfl⟩ : syracuseStep 636893 = 238835) (by norm_num)
theorem B636965 : Blo 279826 636965 := bbase (se 4 (by rfl) ⟨59715, by rfl⟩ : syracuseStep 636965 = 119431) (by norm_num)
theorem B473141 : Blo 279826 473141 := bbase (se 5 (by rfl) ⟨22178, by rfl⟩ : syracuseStep 473141 = 44357) (by norm_num)
theorem B637037 : Blo 279826 637037 := bbase (se 3 (by rfl) ⟨119444, by rfl⟩ : syracuseStep 637037 = 238889) (by norm_num)
theorem B1423493 : Blo 279826 1423493 := bbase (se 4 (by rfl) ⟨133452, by rfl⟩ : syracuseStep 1423493 = 266905) (by norm_num)
theorem B473269 : Blo 279826 473269 := bbase (se 5 (by rfl) ⟨22184, by rfl⟩ : syracuseStep 473269 = 44369) (by norm_num)
theorem B637109 : Blo 279826 637109 := bbase (se 5 (by rfl) ⟨29864, by rfl⟩ : syracuseStep 637109 = 59729) (by norm_num)
theorem B506069 : Blo 279826 506069 := bbase (se 7 (by rfl) ⟨5930, by rfl⟩ : syracuseStep 506069 = 11861) (by norm_num)
theorem B637181 : Blo 279826 637181 := bbase (se 3 (by rfl) ⟨119471, by rfl⟩ : syracuseStep 637181 = 238943) (by norm_num)
theorem B473357 : Blo 279826 473357 := bbase (se 3 (by rfl) ⟨88754, by rfl⟩ : syracuseStep 473357 = 177509) (by norm_num)
theorem B637253 : Blo 279826 637253 := bbase (se 4 (by rfl) ⟨59742, by rfl⟩ : syracuseStep 637253 = 119485) (by norm_num)
theorem B604493 : Blo 279826 604493 := bbase (se 3 (by rfl) ⟨113342, by rfl⟩ : syracuseStep 604493 = 226685) (by norm_num)
theorem B473485 : Blo 279826 473485 := bbase (se 3 (by rfl) ⟨88778, by rfl⟩ : syracuseStep 473485 = 177557) (by norm_num)
theorem B637325 : Blo 279826 637325 := bbase (se 3 (by rfl) ⟨119498, by rfl⟩ : syracuseStep 637325 = 238997) (by norm_num)
theorem B899525 : Blo 279826 899525 := bbase (se 4 (by rfl) ⟨84330, by rfl⟩ : syracuseStep 899525 = 168661) (by norm_num)
theorem B637397 : Blo 279826 637397 := bbase (se 7 (by rfl) ⟨7469, by rfl⟩ : syracuseStep 637397 = 14939) (by norm_num)
theorem B473573 : Blo 279826 473573 := bbase (se 4 (by rfl) ⟨44397, by rfl⟩ : syracuseStep 473573 = 88795) (by norm_num)
theorem B637469 : Blo 279826 637469 := bbase (se 3 (by rfl) ⟨119525, by rfl⟩ : syracuseStep 637469 = 239051) (by norm_num)
theorem B571981 : Blo 279826 571981 := bbase (se 3 (by rfl) ⟨107246, by rfl⟩ : syracuseStep 571981 = 214493) (by norm_num)
theorem B473701 : Blo 279826 473701 := bbase (se 4 (by rfl) ⟨44409, by rfl⟩ : syracuseStep 473701 = 88819) (by norm_num)
theorem B637541 : Blo 279826 637541 := bbase (se 4 (by rfl) ⟨59769, by rfl⟩ : syracuseStep 637541 = 119539) (by norm_num)
theorem B965285 : Blo 279826 965285 := bbase (se 4 (by rfl) ⟨90495, by rfl⟩ : syracuseStep 965285 = 180991) (by norm_num)
theorem B637613 : Blo 279826 637613 := bbase (se 3 (by rfl) ⟨119552, by rfl⟩ : syracuseStep 637613 = 239105) (by norm_num)
theorem B1522357 : Blo 279826 1522357 := bbase (se 5 (by rfl) ⟨71360, by rfl⟩ : syracuseStep 1522357 = 142721) (by norm_num)
theorem B473789 : Blo 279826 473789 := bbase (se 3 (by rfl) ⟨88835, by rfl⟩ : syracuseStep 473789 = 177671) (by norm_num)
theorem B637685 : Blo 279826 637685 := bbase (se 5 (by rfl) ⟨29891, by rfl⟩ : syracuseStep 637685 = 59783) (by norm_num)
theorem B473917 : Blo 279826 473917 := bbase (se 3 (by rfl) ⟨88859, by rfl⟩ : syracuseStep 473917 = 177719) (by norm_num)
theorem B637757 : Blo 279826 637757 := bbase (se 3 (by rfl) ⟨119579, by rfl⟩ : syracuseStep 637757 = 239159) (by norm_num)
theorem B637829 : Blo 279826 637829 := bbase (se 4 (by rfl) ⟨59796, by rfl⟩ : syracuseStep 637829 = 119593) (by norm_num)
theorem B474005 : Blo 279826 474005 := bbase (se 6 (by rfl) ⟨11109, by rfl⟩ : syracuseStep 474005 = 22219) (by norm_num)
theorem B637901 : Blo 279826 637901 := bbase (se 3 (by rfl) ⟨119606, by rfl⟩ : syracuseStep 637901 = 239213) (by norm_num)
theorem B1391573 : Blo 279826 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B343045 : Blo 279826 343045 := bbase (se 4 (by rfl) ⟨32160, by rfl⟩ : syracuseStep 343045 = 64321) (by norm_num)
theorem B474133 : Blo 279826 474133 := bbase (se 6 (by rfl) ⟨11112, by rfl⟩ : syracuseStep 474133 = 22225) (by norm_num)
theorem B637973 : Blo 279826 637973 := bbase (se 6 (by rfl) ⟨14952, by rfl⟩ : syracuseStep 637973 = 29905) (by norm_num)
theorem B605245 : Blo 279826 605245 := bbase (se 3 (by rfl) ⟨113483, by rfl⟩ : syracuseStep 605245 = 226967) (by norm_num)
theorem B539741 : Blo 279826 539741 := bbase (se 3 (by rfl) ⟨101201, by rfl⟩ : syracuseStep 539741 = 202403) (by norm_num)
theorem B638045 : Blo 279826 638045 := bbase (se 3 (by rfl) ⟨119633, by rfl⟩ : syracuseStep 638045 = 239267) (by norm_num)
theorem B474221 : Blo 279826 474221 := bbase (se 3 (by rfl) ⟨88916, by rfl⟩ : syracuseStep 474221 = 177833) (by norm_num)
theorem B638117 : Blo 279826 638117 := bbase (se 4 (by rfl) ⟨59823, by rfl⟩ : syracuseStep 638117 = 119647) (by norm_num)
theorem B605389 : Blo 279826 605389 := bbase (se 3 (by rfl) ⟨113510, by rfl⟩ : syracuseStep 605389 = 227021) (by norm_num)
theorem B474349 : Blo 279826 474349 := bbase (se 3 (by rfl) ⟨88940, by rfl⟩ : syracuseStep 474349 = 177881) (by norm_num)
theorem B638189 : Blo 279826 638189 := bbase (se 3 (by rfl) ⟨119660, by rfl⟩ : syracuseStep 638189 = 239321) (by norm_num)
theorem B802037 : Blo 279826 802037 := bbase (se 5 (by rfl) ⟨37595, by rfl⟩ : syracuseStep 802037 = 75191) (by norm_num)
theorem B638261 : Blo 279826 638261 := bbase (se 5 (by rfl) ⟨29918, by rfl⟩ : syracuseStep 638261 = 59837) (by norm_num)
theorem B474437 : Blo 279826 474437 := bbase (se 4 (by rfl) ⟨44478, by rfl⟩ : syracuseStep 474437 = 88957) (by norm_num)
theorem B638333 : Blo 279826 638333 := bbase (se 3 (by rfl) ⟨119687, by rfl⟩ : syracuseStep 638333 = 239375) (by norm_num)
theorem B1424789 : Blo 279826 1424789 := bbase (se 6 (by rfl) ⟨33393, by rfl⟩ : syracuseStep 1424789 = 66787) (by norm_num)
theorem B4078997 : Blo 279826 4078997 := bbase (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) (by norm_num)
theorem B474565 : Blo 279826 474565 := bbase (se 4 (by rfl) ⟨44490, by rfl⟩ : syracuseStep 474565 = 88981) (by norm_num)
theorem B638405 : Blo 279826 638405 := bbase (se 4 (by rfl) ⟨59850, by rfl⟩ : syracuseStep 638405 = 119701) (by norm_num)
theorem B638477 : Blo 279826 638477 := bbase (se 3 (by rfl) ⟨119714, by rfl⟩ : syracuseStep 638477 = 239429) (by norm_num)
theorem B474653 : Blo 279826 474653 := bbase (se 3 (by rfl) ⟨88997, by rfl⟩ : syracuseStep 474653 = 177995) (by norm_num)
theorem B605765 : Blo 279826 605765 := bbase (se 4 (by rfl) ⟨56790, by rfl⟩ : syracuseStep 605765 = 113581) (by norm_num)
theorem B638549 : Blo 279826 638549 := bbase (se 8 (by rfl) ⟨3741, by rfl⟩ : syracuseStep 638549 = 7483) (by norm_num)
theorem B343697 : Blo 279826 343697 := bbase (se 2 (by rfl) ⟨128886, by rfl⟩ : syracuseStep 343697 = 257773) (by norm_num)
theorem B474781 : Blo 279826 474781 := bbase (se 3 (by rfl) ⟨89021, by rfl⟩ : syracuseStep 474781 = 178043) (by norm_num)
theorem B573149 : Blo 279826 573149 := bbase (se 3 (by rfl) ⟨107465, by rfl⟩ : syracuseStep 573149 = 214931) (by norm_num)
theorem B474869 : Blo 279826 474869 := bbase (se 5 (by rfl) ⟨22259, by rfl⟩ : syracuseStep 474869 = 44519) (by norm_num)
theorem B2244341 : Blo 279826 2244341 := bbase (se 5 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 2244341 = 210407) (by norm_num)
theorem B474997 : Blo 279826 474997 := bbase (se 5 (by rfl) ⟨22265, by rfl⟩ : syracuseStep 474997 = 44531) (by norm_num)
theorem B507829 : Blo 279826 507829 := bbase (se 5 (by rfl) ⟨23804, by rfl⟩ : syracuseStep 507829 = 47609) (by norm_num)
theorem B606133 : Blo 279826 606133 := bbase (se 5 (by rfl) ⟨28412, by rfl⟩ : syracuseStep 606133 = 56825) (by norm_num)
theorem B475085 : Blo 279826 475085 := bbase (se 3 (by rfl) ⟨89078, by rfl⟩ : syracuseStep 475085 = 178157) (by norm_num)
theorem B1064933 : Blo 279826 1064933 := bbase (se 4 (by rfl) ⟨99837, by rfl⟩ : syracuseStep 1064933 = 199675) (by norm_num)
theorem B638981 : Blo 279826 638981 := bbase (se 4 (by rfl) ⟨59904, by rfl⟩ : syracuseStep 638981 = 119809) (by norm_num)
theorem B507965 : Blo 279826 507965 := bbase (se 3 (by rfl) ⟨95243, by rfl⟩ : syracuseStep 507965 = 190487) (by norm_num)
theorem B475213 : Blo 279826 475213 := bbase (se 3 (by rfl) ⟨89102, by rfl⟩ : syracuseStep 475213 = 178205) (by norm_num)
theorem B508045 : Blo 279826 508045 := bbase (se 3 (by rfl) ⟨95258, by rfl⟩ : syracuseStep 508045 = 190517) (by norm_num)
theorem B475301 : Blo 279826 475301 := bbase (se 4 (by rfl) ⟨44559, by rfl⟩ : syracuseStep 475301 = 89119) (by norm_num)
theorem B1065221 : Blo 279826 1065221 := bbase (se 4 (by rfl) ⟨99864, by rfl⟩ : syracuseStep 1065221 = 199729) (by norm_num)
theorem B475429 : Blo 279826 475429 := bbase (se 4 (by rfl) ⟨44571, by rfl⟩ : syracuseStep 475429 = 89143) (by norm_num)
theorem B475517 : Blo 279826 475517 := bbase (se 3 (by rfl) ⟨89159, by rfl⟩ : syracuseStep 475517 = 178319) (by norm_num)
theorem B475645 : Blo 279826 475645 := bbase (se 3 (by rfl) ⟨89183, by rfl⟩ : syracuseStep 475645 = 178367) (by norm_num)
theorem B475733 : Blo 279826 475733 := bbase (se 8 (by rfl) ⟨2787, by rfl⟩ : syracuseStep 475733 = 5575) (by norm_num)
theorem B1426085 : Blo 279826 1426085 := bbase (se 4 (by rfl) ⟨133695, by rfl⟩ : syracuseStep 1426085 = 267391) (by norm_num)
theorem B541397 : Blo 279826 541397 := bbase (se 7 (by rfl) ⟨6344, by rfl⟩ : syracuseStep 541397 = 12689) (by norm_num)
theorem B475861 : Blo 279826 475861 := bbase (se 7 (by rfl) ⟨5576, by rfl⟩ : syracuseStep 475861 = 11153) (by norm_num)
theorem B803621 : Blo 279826 803621 := bbase (se 4 (by rfl) ⟨75339, by rfl⟩ : syracuseStep 803621 = 150679) (by norm_num)
theorem B475949 : Blo 279826 475949 := bbase (se 3 (by rfl) ⟨89240, by rfl⟩ : syracuseStep 475949 = 178481) (by norm_num)
theorem B476077 : Blo 279826 476077 := bbase (se 3 (by rfl) ⟨89264, by rfl⟩ : syracuseStep 476077 = 178529) (by norm_num)
theorem B476165 : Blo 279826 476165 := bbase (se 4 (by rfl) ⟨44640, by rfl⟩ : syracuseStep 476165 = 89281) (by norm_num)
theorem B1197109 : Blo 279826 1197109 := bbase (se 5 (by rfl) ⟨56114, by rfl⟩ : syracuseStep 1197109 = 112229) (by norm_num)
theorem B574517 : Blo 279826 574517 := bbase (se 5 (by rfl) ⟨26930, by rfl⟩ : syracuseStep 574517 = 53861) (by norm_num)
theorem B476293 : Blo 279826 476293 := bbase (se 4 (by rfl) ⟨44652, by rfl⟩ : syracuseStep 476293 = 89305) (by norm_num)
theorem B2802869 : Blo 279826 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B509141 : Blo 279826 509141 := bbase (se 7 (by rfl) ⟨5966, by rfl⟩ : syracuseStep 509141 = 11933) (by norm_num)
theorem B476381 : Blo 279826 476381 := bbase (se 3 (by rfl) ⟨89321, by rfl⟩ : syracuseStep 476381 = 178643) (by norm_num)
theorem B476509 : Blo 279826 476509 := bbase (se 3 (by rfl) ⟨89345, by rfl⟩ : syracuseStep 476509 = 178691) (by norm_num)
theorem B1066405 : Blo 279826 1066405 := bbase (se 4 (by rfl) ⟨99975, by rfl⟩ : syracuseStep 1066405 = 199951) (by norm_num)
theorem B476597 : Blo 279826 476597 := bbase (se 5 (by rfl) ⟨22340, by rfl⟩ : syracuseStep 476597 = 44681) (by norm_num)
theorem B542141 : Blo 279826 542141 := bbase (se 3 (by rfl) ⟨101651, by rfl⟩ : syracuseStep 542141 = 203303) (by norm_num)
theorem B804293 : Blo 279826 804293 := bbase (se 4 (by rfl) ⟨75402, by rfl⟩ : syracuseStep 804293 = 150805) (by norm_num)
theorem B509429 : Blo 279826 509429 := bbase (se 5 (by rfl) ⟨23879, by rfl⟩ : syracuseStep 509429 = 47759) (by norm_num)
theorem B902677 : Blo 279826 902677 := bbase (se 6 (by rfl) ⟨21156, by rfl⟩ : syracuseStep 902677 = 42313) (by norm_num)
theorem B1525301 : Blo 279826 1525301 := bbase (se 5 (by rfl) ⟨71498, by rfl⟩ : syracuseStep 1525301 = 142997) (by norm_num)
theorem B476725 : Blo 279826 476725 := bbase (se 5 (by rfl) ⟨22346, by rfl⟩ : syracuseStep 476725 = 44693) (by norm_num)
theorem B476813 : Blo 279826 476813 := bbase (se 3 (by rfl) ⟨89402, by rfl⟩ : syracuseStep 476813 = 178805) (by norm_num)
theorem B509645 : Blo 279826 509645 := bbase (se 3 (by rfl) ⟨95558, by rfl⟩ : syracuseStep 509645 = 191117) (by norm_num)
theorem B1066709 : Blo 279826 1066709 := bbase (se 7 (by rfl) ⟨12500, by rfl⟩ : syracuseStep 1066709 = 25001) (by norm_num)
theorem B476941 : Blo 279826 476941 := bbase (se 3 (by rfl) ⟨89426, by rfl⟩ : syracuseStep 476941 = 178853) (by norm_num)
theorem B477029 : Blo 279826 477029 := bbase (se 4 (by rfl) ⟨44721, by rfl⟩ : syracuseStep 477029 = 89443) (by norm_num)
theorem B804725 : Blo 279826 804725 := bbase (se 5 (by rfl) ⟨37721, by rfl⟩ : syracuseStep 804725 = 75443) (by norm_num)
theorem B1427381 : Blo 279826 1427381 := bbase (se 5 (by rfl) ⟨66908, by rfl⟩ : syracuseStep 1427381 = 133817) (by norm_num)
theorem B575453 : Blo 279826 575453 := bbase (se 3 (by rfl) ⟨107897, by rfl⟩ : syracuseStep 575453 = 215795) (by norm_num)
theorem B477157 : Blo 279826 477157 := bbase (se 4 (by rfl) ⟨44733, by rfl⟩ : syracuseStep 477157 = 89467) (by norm_num)
theorem B477245 : Blo 279826 477245 := bbase (se 3 (by rfl) ⟨89483, by rfl⟩ : syracuseStep 477245 = 178967) (by norm_num)
theorem B673933 : Blo 279826 673933 := bbase (se 3 (by rfl) ⟨126362, by rfl⟩ : syracuseStep 673933 = 252725) (by norm_num)
theorem B477373 : Blo 279826 477373 := bbase (se 3 (by rfl) ⟨89507, by rfl⟩ : syracuseStep 477373 = 179015) (by norm_num)
theorem B477461 : Blo 279826 477461 := bbase (se 6 (by rfl) ⟨11190, by rfl⟩ : syracuseStep 477461 = 22381) (by norm_num)
theorem B1526165 : Blo 279826 1526165 := bbase (se 6 (by rfl) ⟨35769, by rfl⟩ : syracuseStep 1526165 = 71539) (by norm_num)
theorem B477589 : Blo 279826 477589 := bbase (se 6 (by rfl) ⟨11193, by rfl⟩ : syracuseStep 477589 = 22387) (by norm_num)
theorem B477677 : Blo 279826 477677 := bbase (se 3 (by rfl) ⟨89564, by rfl⟩ : syracuseStep 477677 = 179129) (by norm_num)
theorem B1198597 : Blo 279826 1198597 := bbase (se 4 (by rfl) ⟨112368, by rfl⟩ : syracuseStep 1198597 = 224737) (by norm_num)
theorem B1198613 : Blo 279826 1198613 := bbase (se 6 (by rfl) ⟨28092, by rfl⟩ : syracuseStep 1198613 = 56185) (by norm_num)
theorem B510509 : Blo 279826 510509 := bbase (se 3 (by rfl) ⟨95720, by rfl⟩ : syracuseStep 510509 = 191441) (by norm_num)
theorem B805477 : Blo 279826 805477 := bbase (se 4 (by rfl) ⟨75513, by rfl⟩ : syracuseStep 805477 = 151027) (by norm_num)
theorem B477805 : Blo 279826 477805 := bbase (se 3 (by rfl) ⟨89588, by rfl⟩ : syracuseStep 477805 = 179177) (by norm_num)
theorem B477893 : Blo 279826 477893 := bbase (se 4 (by rfl) ⟨44802, by rfl⟩ : syracuseStep 477893 = 89605) (by norm_num)
theorem B510733 : Blo 279826 510733 := bbase (se 3 (by rfl) ⟨95762, by rfl⟩ : syracuseStep 510733 = 191525) (by norm_num)
theorem B478021 : Blo 279826 478021 := bbase (se 4 (by rfl) ⟨44814, by rfl⟩ : syracuseStep 478021 = 89629) (by norm_num)
theorem B478109 : Blo 279826 478109 := bbase (se 3 (by rfl) ⟨89645, by rfl⟩ : syracuseStep 478109 = 179291) (by norm_num)
theorem B478237 : Blo 279826 478237 := bbase (se 3 (by rfl) ⟨89669, by rfl⟩ : syracuseStep 478237 = 179339) (by norm_num)
theorem B478325 : Blo 279826 478325 := bbase (se 5 (by rfl) ⟨22421, by rfl⟩ : syracuseStep 478325 = 44843) (by norm_num)
theorem B1428677 : Blo 279826 1428677 := bbase (se 4 (by rfl) ⟨133938, by rfl⟩ : syracuseStep 1428677 = 267877) (by norm_num)
theorem B478453 : Blo 279826 478453 := bbase (se 5 (by rfl) ⟨22427, by rfl⟩ : syracuseStep 478453 = 44855) (by norm_num)
theorem B478541 : Blo 279826 478541 := bbase (se 3 (by rfl) ⟨89726, by rfl⟩ : syracuseStep 478541 = 179453) (by norm_num)
theorem B478669 : Blo 279826 478669 := bbase (se 3 (by rfl) ⟨89750, by rfl⟩ : syracuseStep 478669 = 179501) (by norm_num)
theorem B314833 : Blo 279826 314833 := bbase (se 2 (by rfl) ⟨118062, by rfl⟩ : syracuseStep 314833 = 236125) (by norm_num)
theorem B314869 : Blo 279826 314869 := bbase (se 5 (by rfl) ⟨14759, by rfl⟩ : syracuseStep 314869 = 29519) (by norm_num)
theorem B675317 : Blo 279826 675317 := bbase (se 5 (by rfl) ⟨31655, by rfl⟩ : syracuseStep 675317 = 63311) (by norm_num)
theorem B314905 : Blo 279826 314905 := bbase (se 2 (by rfl) ⟨118089, by rfl⟩ : syracuseStep 314905 = 236179) (by norm_num)
theorem B478757 : Blo 279826 478757 := bbase (se 4 (by rfl) ⟨44883, by rfl⟩ : syracuseStep 478757 = 89767) (by norm_num)
theorem B1363493 : Blo 279826 1363493 := bbase (se 4 (by rfl) ⟨127827, by rfl⟩ : syracuseStep 1363493 = 255655) (by norm_num)
theorem B314941 : Blo 279826 314941 := bbase (se 3 (by rfl) ⟨59051, by rfl⟩ : syracuseStep 314941 = 118103) (by norm_num)
theorem B314977 : Blo 279826 314977 := bbase (se 2 (by rfl) ⟨118116, by rfl⟩ : syracuseStep 314977 = 236233) (by norm_num)
theorem B315013 : Blo 279826 315013 := bbase (se 4 (by rfl) ⟨29532, by rfl⟩ : syracuseStep 315013 = 59065) (by norm_num)
theorem B478885 : Blo 279826 478885 := bbase (se 4 (by rfl) ⟨44895, by rfl⟩ : syracuseStep 478885 = 89791) (by norm_num)
theorem B315049 : Blo 279826 315049 := bbase (se 2 (by rfl) ⟨118143, by rfl⟩ : syracuseStep 315049 = 236287) (by norm_num)
theorem B315085 : Blo 279826 315085 := bbase (se 3 (by rfl) ⟨59078, by rfl⟩ : syracuseStep 315085 = 118157) (by norm_num)
theorem B315121 : Blo 279826 315121 := bbase (se 2 (by rfl) ⟨118170, by rfl⟩ : syracuseStep 315121 = 236341) (by norm_num)
theorem B708365 : Blo 279826 708365 := bbase (se 3 (by rfl) ⟨132818, by rfl⟩ : syracuseStep 708365 = 265637) (by norm_num)
theorem B315157 : Blo 279826 315157 := bbase (se 6 (by rfl) ⟨7386, by rfl⟩ : syracuseStep 315157 = 14773) (by norm_num)
theorem B1068821 : Blo 279826 1068821 := bbase (se 6 (by rfl) ⟨25050, by rfl⟩ : syracuseStep 1068821 = 50101) (by norm_num)
theorem B315193 : Blo 279826 315193 := bbase (se 2 (by rfl) ⟨118197, by rfl⟩ : syracuseStep 315193 = 236395) (by norm_num)
theorem B315229 : Blo 279826 315229 := bbase (se 3 (by rfl) ⟨59105, by rfl⟩ : syracuseStep 315229 = 118211) (by norm_num)
theorem B2576245 : Blo 279826 2576245 := bbase (se 5 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 2576245 = 241523) (by norm_num)
theorem B642941 : Blo 279826 642941 := bbase (se 3 (by rfl) ⟨120551, by rfl⟩ : syracuseStep 642941 = 241103) (by norm_num)
theorem B315265 : Blo 279826 315265 := bbase (se 2 (by rfl) ⟨118224, by rfl⟩ : syracuseStep 315265 = 236449) (by norm_num)
theorem B315301 : Blo 279826 315301 := bbase (se 4 (by rfl) ⟨29559, by rfl⟩ : syracuseStep 315301 = 59119) (by norm_num)
theorem B675749 : Blo 279826 675749 := bbase (se 4 (by rfl) ⟨63351, by rfl⟩ : syracuseStep 675749 = 126703) (by norm_num)
theorem B315337 : Blo 279826 315337 := bbase (se 2 (by rfl) ⟨118251, by rfl⟩ : syracuseStep 315337 = 236503) (by norm_num)
theorem B315373 : Blo 279826 315373 := bbase (se 3 (by rfl) ⟨59132, by rfl⟩ : syracuseStep 315373 = 118265) (by norm_num)
theorem B315409 : Blo 279826 315409 := bbase (se 2 (by rfl) ⟨118278, by rfl⟩ : syracuseStep 315409 = 236557) (by norm_num)
theorem B315445 : Blo 279826 315445 := bbase (se 5 (by rfl) ⟨14786, by rfl⟩ : syracuseStep 315445 = 29573) (by norm_num)
theorem B1069109 : Blo 279826 1069109 := bbase (se 5 (by rfl) ⟨50114, by rfl⟩ : syracuseStep 1069109 = 100229) (by norm_num)
theorem B315481 : Blo 279826 315481 := bbase (se 2 (by rfl) ⟨118305, by rfl⟩ : syracuseStep 315481 = 236611) (by norm_num)
theorem B708709 : Blo 279826 708709 := bbase (se 4 (by rfl) ⟨66441, by rfl⟩ : syracuseStep 708709 = 132883) (by norm_num)
theorem B315517 : Blo 279826 315517 := bbase (se 3 (by rfl) ⟨59159, by rfl⟩ : syracuseStep 315517 = 118319) (by norm_num)
theorem B2150549 : Blo 279826 2150549 := bbase (se 6 (by rfl) ⟨50403, by rfl⟩ : syracuseStep 2150549 = 100807) (by norm_num)
theorem B315553 : Blo 279826 315553 := bbase (se 2 (by rfl) ⟨118332, by rfl⟩ : syracuseStep 315553 = 236665) (by norm_num)
theorem B512173 : Blo 279826 512173 := bbase (se 3 (by rfl) ⟨96032, by rfl⟩ : syracuseStep 512173 = 192065) (by norm_num)
theorem B315589 : Blo 279826 315589 := bbase (se 4 (by rfl) ⟨29586, by rfl⟩ : syracuseStep 315589 = 59173) (by norm_num)
theorem B708821 : Blo 279826 708821 := bbase (se 7 (by rfl) ⟨8306, by rfl⟩ : syracuseStep 708821 = 16613) (by norm_num)
theorem B315625 : Blo 279826 315625 := bbase (se 2 (by rfl) ⟨118359, by rfl⟩ : syracuseStep 315625 = 236719) (by norm_num)
theorem B315661 : Blo 279826 315661 := bbase (se 3 (by rfl) ⟨59186, by rfl⟩ : syracuseStep 315661 = 118373) (by norm_num)
theorem B905509 : Blo 279826 905509 := bbase (se 4 (by rfl) ⟨84891, by rfl⟩ : syracuseStep 905509 = 169783) (by norm_num)
theorem B315697 : Blo 279826 315697 := bbase (se 2 (by rfl) ⟨118386, by rfl⟩ : syracuseStep 315697 = 236773) (by norm_num)
theorem B315733 : Blo 279826 315733 := bbase (se 10 (by rfl) ⟨462, by rfl⟩ : syracuseStep 315733 = 925) (by norm_num)
theorem B905573 : Blo 279826 905573 := bbase (se 4 (by rfl) ⟨84897, by rfl⟩ : syracuseStep 905573 = 169795) (by norm_num)
theorem B315769 : Blo 279826 315769 := bbase (se 2 (by rfl) ⟨118413, by rfl⟩ : syracuseStep 315769 = 236827) (by norm_num)
theorem B709013 : Blo 279826 709013 := bbase (se 6 (by rfl) ⟨16617, by rfl⟩ : syracuseStep 709013 = 33235) (by norm_num)
theorem B315805 : Blo 279826 315805 := bbase (se 3 (by rfl) ⟨59213, by rfl⟩ : syracuseStep 315805 = 118427) (by norm_num)
theorem B315841 : Blo 279826 315841 := bbase (se 2 (by rfl) ⟨118440, by rfl⟩ : syracuseStep 315841 = 236881) (by norm_num)
theorem B1429973 : Blo 279826 1429973 := bbase (se 7 (by rfl) ⟨16757, by rfl⟩ : syracuseStep 1429973 = 33515) (by norm_num)
theorem B315877 : Blo 279826 315877 := bbase (se 4 (by rfl) ⟨29613, by rfl⟩ : syracuseStep 315877 = 59227) (by norm_num)
theorem B315913 : Blo 279826 315913 := bbase (se 2 (by rfl) ⟨118467, by rfl⟩ : syracuseStep 315913 = 236935) (by norm_num)
theorem B315949 : Blo 279826 315949 := bbase (se 3 (by rfl) ⟨59240, by rfl⟩ : syracuseStep 315949 = 118481) (by norm_num)
theorem B381493 : Blo 279826 381493 := bbase (se 5 (by rfl) ⟨17882, by rfl⟩ : syracuseStep 381493 = 35765) (by norm_num)
theorem B315985 : Blo 279826 315985 := bbase (se 2 (by rfl) ⟨118494, by rfl⟩ : syracuseStep 315985 = 236989) (by norm_num)
theorem B316021 : Blo 279826 316021 := bbase (se 5 (by rfl) ⟨14813, by rfl⟩ : syracuseStep 316021 = 29627) (by norm_num)
theorem B316057 : Blo 279826 316057 := bbase (se 2 (by rfl) ⟨118521, by rfl⟩ : syracuseStep 316057 = 237043) (by norm_num)
theorem B316093 : Blo 279826 316093 := bbase (se 3 (by rfl) ⟨59267, by rfl⟩ : syracuseStep 316093 = 118535) (by norm_num)
theorem B316129 : Blo 279826 316129 := bbase (se 2 (by rfl) ⟨118548, by rfl⟩ : syracuseStep 316129 = 237097) (by norm_num)
theorem B1200869 : Blo 279826 1200869 := bbase (se 4 (by rfl) ⟨112581, by rfl⟩ : syracuseStep 1200869 = 225163) (by norm_num)
theorem B709357 : Blo 279826 709357 := bbase (se 3 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 709357 = 266009) (by norm_num)
theorem B316165 : Blo 279826 316165 := bbase (se 4 (by rfl) ⟨29640, by rfl⟩ : syracuseStep 316165 = 59281) (by norm_num)
theorem B316201 : Blo 279826 316201 := bbase (se 2 (by rfl) ⟨118575, by rfl⟩ : syracuseStep 316201 = 237151) (by norm_num)
theorem B447293 : Blo 279826 447293 := bbase (se 3 (by rfl) ⟨83867, by rfl⟩ : syracuseStep 447293 = 167735) (by norm_num)
theorem B316237 : Blo 279826 316237 := bbase (se 3 (by rfl) ⟨59294, by rfl⟩ : syracuseStep 316237 = 118589) (by norm_num)
theorem B709469 : Blo 279826 709469 := bbase (se 3 (by rfl) ⟨133025, by rfl⟩ : syracuseStep 709469 = 266051) (by norm_num)
theorem B316273 : Blo 279826 316273 := bbase (se 2 (by rfl) ⟨118602, by rfl⟩ : syracuseStep 316273 = 237205) (by norm_num)
theorem B316309 : Blo 279826 316309 := bbase (se 6 (by rfl) ⟨7413, by rfl⟩ : syracuseStep 316309 = 14827) (by norm_num)
theorem B643997 : Blo 279826 643997 := bbase (se 3 (by rfl) ⟨120749, by rfl⟩ : syracuseStep 643997 = 241499) (by norm_num)
theorem B1135541 : Blo 279826 1135541 := bbase (se 5 (by rfl) ⟨53228, by rfl⟩ : syracuseStep 1135541 = 106457) (by norm_num)
theorem B316345 : Blo 279826 316345 := bbase (se 2 (by rfl) ⟨118629, by rfl⟩ : syracuseStep 316345 = 237259) (by norm_num)
theorem B316381 : Blo 279826 316381 := bbase (se 3 (by rfl) ⟨59321, by rfl⟩ : syracuseStep 316381 = 118643) (by norm_num)
theorem B349177 : Blo 279826 349177 := bbase (se 2 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 349177 = 261883) (by norm_num)
theorem B316417 : Blo 279826 316417 := bbase (se 2 (by rfl) ⟨118656, by rfl⟩ : syracuseStep 316417 = 237313) (by norm_num)
theorem B709661 : Blo 279826 709661 := bbase (se 3 (by rfl) ⟨133061, by rfl⟩ : syracuseStep 709661 = 266123) (by norm_num)
theorem B316453 : Blo 279826 316453 := bbase (se 4 (by rfl) ⟨29667, by rfl⟩ : syracuseStep 316453 = 59335) (by norm_num)
theorem B611365 : Blo 279826 611365 := bbase (se 4 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 611365 = 114631) (by norm_num)
theorem B316489 : Blo 279826 316489 := bbase (se 2 (by rfl) ⟨118683, by rfl⟩ : syracuseStep 316489 = 237367) (by norm_num)
theorem B316525 : Blo 279826 316525 := bbase (se 3 (by rfl) ⟨59348, by rfl⟩ : syracuseStep 316525 = 118697) (by norm_num)
theorem B316561 : Blo 279826 316561 := bbase (se 2 (by rfl) ⟨118710, by rfl⟩ : syracuseStep 316561 = 237421) (by norm_num)
theorem B316597 : Blo 279826 316597 := bbase (se 5 (by rfl) ⟨14840, by rfl⟩ : syracuseStep 316597 = 29681) (by norm_num)
theorem B1070293 : Blo 279826 1070293 := bbase (se 7 (by rfl) ⟨12542, by rfl⟩ : syracuseStep 1070293 = 25085) (by norm_num)
theorem B316633 : Blo 279826 316633 := bbase (se 2 (by rfl) ⟨118737, by rfl⟩ : syracuseStep 316633 = 237475) (by norm_num)
theorem B316669 : Blo 279826 316669 := bbase (se 3 (by rfl) ⟨59375, by rfl⟩ : syracuseStep 316669 = 118751) (by norm_num)
theorem B316705 : Blo 279826 316705 := bbase (se 2 (by rfl) ⟨118764, by rfl⟩ : syracuseStep 316705 = 237529) (by norm_num)
theorem B283969 : Blo 279826 283969 := bbase (se 2 (by rfl) ⟨106488, by rfl⟩ : syracuseStep 283969 = 212977) (by norm_num)
theorem B316741 : Blo 279826 316741 := bbase (se 4 (by rfl) ⟨29694, by rfl⟩ : syracuseStep 316741 = 59389) (by norm_num)
theorem B382277 : Blo 279826 382277 := bbase (se 4 (by rfl) ⟨35838, by rfl⟩ : syracuseStep 382277 = 71677) (by norm_num)
theorem B316777 : Blo 279826 316777 := bbase (se 2 (by rfl) ⟨118791, by rfl⟩ : syracuseStep 316777 = 237583) (by norm_num)
theorem B710005 : Blo 279826 710005 := bbase (se 5 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 710005 = 66563) (by norm_num)
theorem B316813 : Blo 279826 316813 := bbase (se 3 (by rfl) ⟨59402, by rfl⟩ : syracuseStep 316813 = 118805) (by norm_num)
theorem B316849 : Blo 279826 316849 := bbase (se 2 (by rfl) ⟨118818, by rfl⟩ : syracuseStep 316849 = 237637) (by norm_num)
theorem B316885 : Blo 279826 316885 := bbase (se 7 (by rfl) ⟨3713, by rfl⟩ : syracuseStep 316885 = 7427) (by norm_num)
theorem B710117 : Blo 279826 710117 := bbase (se 4 (by rfl) ⟨66573, by rfl⟩ : syracuseStep 710117 = 133147) (by norm_num)
theorem B316921 : Blo 279826 316921 := bbase (se 2 (by rfl) ⟨118845, by rfl⟩ : syracuseStep 316921 = 237691) (by norm_num)
theorem B1070597 : Blo 279826 1070597 := bbase (se 4 (by rfl) ⟨100368, by rfl⟩ : syracuseStep 1070597 = 200737) (by norm_num)
theorem B316957 : Blo 279826 316957 := bbase (se 3 (by rfl) ⟨59429, by rfl⟩ : syracuseStep 316957 = 118859) (by norm_num)
theorem B316993 : Blo 279826 316993 := bbase (se 2 (by rfl) ⟨118872, by rfl⟩ : syracuseStep 316993 = 237745) (by norm_num)
theorem B317029 : Blo 279826 317029 := bbase (se 4 (by rfl) ⟨29721, by rfl⟩ : syracuseStep 317029 = 59443) (by norm_num)
theorem B317065 : Blo 279826 317065 := bbase (se 2 (by rfl) ⟨118899, by rfl⟩ : syracuseStep 317065 = 237799) (by norm_num)
theorem B710309 : Blo 279826 710309 := bbase (se 4 (by rfl) ⟨66591, by rfl⟩ : syracuseStep 710309 = 133183) (by norm_num)
theorem B317101 : Blo 279826 317101 := bbase (se 3 (by rfl) ⟨59456, by rfl⟩ : syracuseStep 317101 = 118913) (by norm_num)
theorem B317137 : Blo 279826 317137 := bbase (se 2 (by rfl) ⟨118926, by rfl⟩ : syracuseStep 317137 = 237853) (by norm_num)
theorem B1431269 : Blo 279826 1431269 := bbase (se 4 (by rfl) ⟨134181, by rfl⟩ : syracuseStep 1431269 = 268363) (by norm_num)
theorem B317173 : Blo 279826 317173 := bbase (se 5 (by rfl) ⟨14867, by rfl⟩ : syracuseStep 317173 = 29735) (by norm_num)
theorem B317209 : Blo 279826 317209 := bbase (se 2 (by rfl) ⟨118953, by rfl⟩ : syracuseStep 317209 = 237907) (by norm_num)
theorem B448301 : Blo 279826 448301 := bbase (se 3 (by rfl) ⟨84056, by rfl⟩ : syracuseStep 448301 = 168113) (by norm_num)
theorem B317245 : Blo 279826 317245 := bbase (se 3 (by rfl) ⟨59483, by rfl⟩ : syracuseStep 317245 = 118967) (by norm_num)
theorem B317281 : Blo 279826 317281 := bbase (se 2 (by rfl) ⟨118980, by rfl⟩ : syracuseStep 317281 = 237961) (by norm_num)
theorem B317317 : Blo 279826 317317 := bbase (se 4 (by rfl) ⟨29748, by rfl⟩ : syracuseStep 317317 = 59497) (by norm_num)
theorem B317353 : Blo 279826 317353 := bbase (se 2 (by rfl) ⟨119007, by rfl⟩ : syracuseStep 317353 = 238015) (by norm_num)
theorem B350125 : Blo 279826 350125 := bbase (se 3 (by rfl) ⟨65648, by rfl⟩ : syracuseStep 350125 = 131297) (by norm_num)
theorem B317389 : Blo 279826 317389 := bbase (se 3 (by rfl) ⟨59510, by rfl⟩ : syracuseStep 317389 = 119021) (by norm_num)
theorem B382925 : Blo 279826 382925 := bbase (se 3 (by rfl) ⟨71798, by rfl⟩ : syracuseStep 382925 = 143597) (by norm_num)
theorem B317425 : Blo 279826 317425 := bbase (se 2 (by rfl) ⟨119034, by rfl⟩ : syracuseStep 317425 = 238069) (by norm_num)
theorem B710653 : Blo 279826 710653 := bbase (se 3 (by rfl) ⟨133247, by rfl⟩ : syracuseStep 710653 = 266495) (by norm_num)
theorem B317461 : Blo 279826 317461 := bbase (se 6 (by rfl) ⟨7440, by rfl⟩ : syracuseStep 317461 = 14881) (by norm_num)
theorem B317497 : Blo 279826 317497 := bbase (se 2 (by rfl) ⟨119061, by rfl⟩ : syracuseStep 317497 = 238123) (by norm_num)
theorem B317533 : Blo 279826 317533 := bbase (se 3 (by rfl) ⟨59537, by rfl⟩ : syracuseStep 317533 = 119075) (by norm_num)
theorem B710765 : Blo 279826 710765 := bbase (se 3 (by rfl) ⟨133268, by rfl⟩ : syracuseStep 710765 = 266537) (by norm_num)
theorem B317569 : Blo 279826 317569 := bbase (se 2 (by rfl) ⟨119088, by rfl⟩ : syracuseStep 317569 = 238177) (by norm_num)
theorem B317605 : Blo 279826 317605 := bbase (se 4 (by rfl) ⟨29775, by rfl⟩ : syracuseStep 317605 = 59551) (by norm_num)
theorem B317641 : Blo 279826 317641 := bbase (se 2 (by rfl) ⟨119115, by rfl⟩ : syracuseStep 317641 = 238231) (by norm_num)
theorem B317677 : Blo 279826 317677 := bbase (se 3 (by rfl) ⟨59564, by rfl⟩ : syracuseStep 317677 = 119129) (by norm_num)
theorem B448757 : Blo 279826 448757 := bbase (se 5 (by rfl) ⟨21035, by rfl⟩ : syracuseStep 448757 = 42071) (by norm_num)
theorem B317713 : Blo 279826 317713 := bbase (se 2 (by rfl) ⟨119142, by rfl⟩ : syracuseStep 317713 = 238285) (by norm_num)
theorem B710957 : Blo 279826 710957 := bbase (se 3 (by rfl) ⟨133304, by rfl⟩ : syracuseStep 710957 = 266609) (by norm_num)
theorem B317749 : Blo 279826 317749 := bbase (se 5 (by rfl) ⟨14894, by rfl⟩ : syracuseStep 317749 = 29789) (by norm_num)
theorem B317785 : Blo 279826 317785 := bbase (se 2 (by rfl) ⟨119169, by rfl⟩ : syracuseStep 317785 = 238339) (by norm_num)
theorem B285053 : Blo 279826 285053 := bbase (se 3 (by rfl) ⟨53447, by rfl⟩ : syracuseStep 285053 = 106895) (by norm_num)
theorem B317821 : Blo 279826 317821 := bbase (se 3 (by rfl) ⟨59591, by rfl⟩ : syracuseStep 317821 = 119183) (by norm_num)
theorem B612749 : Blo 279826 612749 := bbase (se 3 (by rfl) ⟨114890, by rfl⟩ : syracuseStep 612749 = 229781) (by norm_num)
theorem B3627413 : Blo 279826 3627413 := bbase (se 6 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 3627413 = 170035) (by norm_num)
theorem B317857 : Blo 279826 317857 := bbase (se 2 (by rfl) ⟨119196, by rfl⟩ : syracuseStep 317857 = 238393) (by norm_num)
theorem B317893 : Blo 279826 317893 := bbase (se 4 (by rfl) ⟨29802, by rfl⟩ : syracuseStep 317893 = 59605) (by norm_num)
theorem B317929 : Blo 279826 317929 := bbase (se 2 (by rfl) ⟨119223, by rfl⟩ : syracuseStep 317929 = 238447) (by norm_num)
theorem B317965 : Blo 279826 317965 := bbase (se 3 (by rfl) ⟨59618, by rfl⟩ : syracuseStep 317965 = 119237) (by norm_num)
theorem B645677 : Blo 279826 645677 := bbase (se 3 (by rfl) ⟨121064, by rfl⟩ : syracuseStep 645677 = 242129) (by norm_num)
theorem B318001 : Blo 279826 318001 := bbase (se 2 (by rfl) ⟨119250, by rfl⟩ : syracuseStep 318001 = 238501) (by norm_num)
theorem B481877 : Blo 279826 481877 := bbase (se 8 (by rfl) ⟨2823, by rfl⟩ : syracuseStep 481877 = 5647) (by norm_num)
theorem B318037 : Blo 279826 318037 := bbase (se 8 (by rfl) ⟨1863, by rfl⟩ : syracuseStep 318037 = 3727) (by norm_num)
theorem B645749 : Blo 279826 645749 := bbase (se 5 (by rfl) ⟨30269, by rfl⟩ : syracuseStep 645749 = 60539) (by norm_num)
theorem B318073 : Blo 279826 318073 := bbase (se 2 (by rfl) ⟨119277, by rfl⟩ : syracuseStep 318073 = 238555) (by norm_num)
theorem B711301 : Blo 279826 711301 := bbase (se 4 (by rfl) ⟨66684, by rfl⟩ : syracuseStep 711301 = 133369) (by norm_num)
theorem B318109 : Blo 279826 318109 := bbase (se 3 (by rfl) ⟨59645, by rfl⟩ : syracuseStep 318109 = 119291) (by norm_num)
theorem B613021 : Blo 279826 613021 := bbase (se 3 (by rfl) ⟨114941, by rfl⟩ : syracuseStep 613021 = 229883) (by norm_num)
theorem B318145 : Blo 279826 318145 := bbase (se 2 (by rfl) ⟨119304, by rfl⟩ : syracuseStep 318145 = 238609) (by norm_num)
theorem B318181 : Blo 279826 318181 := bbase (se 4 (by rfl) ⟨29829, by rfl⟩ : syracuseStep 318181 = 59659) (by norm_num)
theorem B711413 : Blo 279826 711413 := bbase (se 5 (by rfl) ⟨33347, by rfl⟩ : syracuseStep 711413 = 66695) (by norm_num)
theorem B318217 : Blo 279826 318217 := bbase (se 2 (by rfl) ⟨119331, by rfl⟩ : syracuseStep 318217 = 238663) (by norm_num)
theorem B318253 : Blo 279826 318253 := bbase (se 3 (by rfl) ⟨59672, by rfl⟩ : syracuseStep 318253 = 119345) (by norm_num)
theorem B318289 : Blo 279826 318289 := bbase (se 2 (by rfl) ⟨119358, by rfl⟩ : syracuseStep 318289 = 238717) (by norm_num)
theorem B318325 : Blo 279826 318325 := bbase (se 5 (by rfl) ⟨14921, by rfl⟩ : syracuseStep 318325 = 29843) (by norm_num)
theorem B318361 : Blo 279826 318361 := bbase (se 2 (by rfl) ⟨119385, by rfl⟩ : syracuseStep 318361 = 238771) (by norm_num)
theorem B711605 : Blo 279826 711605 := bbase (se 5 (by rfl) ⟨33356, by rfl⟩ : syracuseStep 711605 = 66713) (by norm_num)
theorem B2415541 : Blo 279826 2415541 := bbase (se 5 (by rfl) ⟨113228, by rfl⟩ : syracuseStep 2415541 = 226457) (by norm_num)
theorem B318397 : Blo 279826 318397 := bbase (se 3 (by rfl) ⟨59699, by rfl⟩ : syracuseStep 318397 = 119399) (by norm_num)
theorem B318433 : Blo 279826 318433 := bbase (se 2 (by rfl) ⟨119412, by rfl⟩ : syracuseStep 318433 = 238825) (by norm_num)
theorem B1432565 : Blo 279826 1432565 := bbase (se 5 (by rfl) ⟨67151, by rfl⟩ : syracuseStep 1432565 = 134303) (by norm_num)
theorem B318469 : Blo 279826 318469 := bbase (se 4 (by rfl) ⟨29856, by rfl⟩ : syracuseStep 318469 = 59713) (by norm_num)
theorem B318505 : Blo 279826 318505 := bbase (se 2 (by rfl) ⟨119439, by rfl⟩ : syracuseStep 318505 = 238879) (by norm_num)
theorem B777269 : Blo 279826 777269 := bbase (se 5 (by rfl) ⟨36434, by rfl⟩ : syracuseStep 777269 = 72869) (by norm_num)
theorem B318541 : Blo 279826 318541 := bbase (se 3 (by rfl) ⟨59726, by rfl⟩ : syracuseStep 318541 = 119453) (by norm_num)
theorem B318577 : Blo 279826 318577 := bbase (se 2 (by rfl) ⟨119466, by rfl⟩ : syracuseStep 318577 = 238933) (by norm_num)
theorem B318613 : Blo 279826 318613 := bbase (se 6 (by rfl) ⟨7467, by rfl⟩ : syracuseStep 318613 = 14935) (by norm_num)
theorem B318649 : Blo 279826 318649 := bbase (se 2 (by rfl) ⟨119493, by rfl⟩ : syracuseStep 318649 = 238987) (by norm_num)
theorem B318685 : Blo 279826 318685 := bbase (se 3 (by rfl) ⟨59753, by rfl⟩ : syracuseStep 318685 = 119507) (by norm_num)
theorem B679141 : Blo 279826 679141 := bbase (se 4 (by rfl) ⟨63669, by rfl⟩ : syracuseStep 679141 = 127339) (by norm_num)
theorem B318721 : Blo 279826 318721 := bbase (se 2 (by rfl) ⟨119520, by rfl⟩ : syracuseStep 318721 = 239041) (by norm_num)
theorem B711949 : Blo 279826 711949 := bbase (se 3 (by rfl) ⟨133490, by rfl⟩ : syracuseStep 711949 = 266981) (by norm_num)
theorem B318757 : Blo 279826 318757 := bbase (se 4 (by rfl) ⟨29883, by rfl⟩ : syracuseStep 318757 = 59767) (by norm_num)
theorem B908597 : Blo 279826 908597 := bbase (se 5 (by rfl) ⟨42590, by rfl⟩ : syracuseStep 908597 = 85181) (by norm_num)
theorem B318793 : Blo 279826 318793 := bbase (se 2 (by rfl) ⟨119547, by rfl⟩ : syracuseStep 318793 = 239095) (by norm_num)
theorem B318829 : Blo 279826 318829 := bbase (se 3 (by rfl) ⟨59780, by rfl⟩ : syracuseStep 318829 = 119561) (by norm_num)
theorem B712061 : Blo 279826 712061 := bbase (se 3 (by rfl) ⟨133511, by rfl⟩ : syracuseStep 712061 = 267023) (by norm_num)
theorem B318865 : Blo 279826 318865 := bbase (se 2 (by rfl) ⟨119574, by rfl⟩ : syracuseStep 318865 = 239149) (by norm_num)
theorem B1793461 : Blo 279826 1793461 := bbase (se 5 (by rfl) ⟨84068, by rfl⟩ : syracuseStep 1793461 = 168137) (by norm_num)
theorem B318901 : Blo 279826 318901 := bbase (se 5 (by rfl) ⟨14948, by rfl⟩ : syracuseStep 318901 = 29897) (by norm_num)
theorem B318937 : Blo 279826 318937 := bbase (se 2 (by rfl) ⟨119601, by rfl⟩ : syracuseStep 318937 = 239203) (by norm_num)
theorem B318973 : Blo 279826 318973 := bbase (se 3 (by rfl) ⟨59807, by rfl⟩ : syracuseStep 318973 = 119615) (by norm_num)
theorem B319009 : Blo 279826 319009 := bbase (se 2 (by rfl) ⟨119628, by rfl⟩ : syracuseStep 319009 = 239257) (by norm_num)
theorem B712253 : Blo 279826 712253 := bbase (se 3 (by rfl) ⟨133547, by rfl⟩ : syracuseStep 712253 = 267095) (by norm_num)
theorem B1072709 : Blo 279826 1072709 := bbase (se 4 (by rfl) ⟨100566, by rfl⟩ : syracuseStep 1072709 = 201133) (by norm_num)
theorem B319045 : Blo 279826 319045 := bbase (se 4 (by rfl) ⟨29910, by rfl⟩ : syracuseStep 319045 = 59821) (by norm_num)
theorem B319081 : Blo 279826 319081 := bbase (se 2 (by rfl) ⟨119655, by rfl⟩ : syracuseStep 319081 = 239311) (by norm_num)
theorem B450173 : Blo 279826 450173 := bbase (se 3 (by rfl) ⟨84407, by rfl⟩ : syracuseStep 450173 = 168815) (by norm_num)
theorem B679565 : Blo 279826 679565 := bbase (se 3 (by rfl) ⟨127418, by rfl⟩ : syracuseStep 679565 = 254837) (by norm_num)
theorem B319117 : Blo 279826 319117 := bbase (se 3 (by rfl) ⟨59834, by rfl⟩ : syracuseStep 319117 = 119669) (by norm_num)
theorem B319153 : Blo 279826 319153 := bbase (se 2 (by rfl) ⟨119682, by rfl⟩ : syracuseStep 319153 = 239365) (by norm_num)
theorem B319189 : Blo 279826 319189 := bbase (se 7 (by rfl) ⟨3740, by rfl⟩ : syracuseStep 319189 = 7481) (by norm_num)
theorem B319225 : Blo 279826 319225 := bbase (se 2 (by rfl) ⟨119709, by rfl⟩ : syracuseStep 319225 = 239419) (by norm_num)
theorem B319261 : Blo 279826 319261 := bbase (se 3 (by rfl) ⟨59861, by rfl⟩ : syracuseStep 319261 = 119723) (by norm_num)
theorem B319297 : Blo 279826 319297 := bbase (se 2 (by rfl) ⟨119736, by rfl⟩ : syracuseStep 319297 = 239473) (by norm_num)
theorem B450397 : Blo 279826 450397 := bbase (se 3 (by rfl) ⟨84449, by rfl⟩ : syracuseStep 450397 = 168899) (by norm_num)
theorem B1072997 : Blo 279826 1072997 := bbase (se 4 (by rfl) ⟨100593, by rfl⟩ : syracuseStep 1072997 = 201187) (by norm_num)
theorem B712597 : Blo 279826 712597 := bbase (se 6 (by rfl) ⟨16701, by rfl⟩ : syracuseStep 712597 = 33403) (by norm_num)
theorem B679853 : Blo 279826 679853 := bbase (se 3 (by rfl) ⟨127472, by rfl⟩ : syracuseStep 679853 = 254945) (by norm_num)
theorem B712709 : Blo 279826 712709 := bbase (se 4 (by rfl) ⟨66816, by rfl⟩ : syracuseStep 712709 = 133633) (by norm_num)
theorem B319609 : Blo 279826 319609 := bbase (se 2 (by rfl) ⟨119853, by rfl⟩ : syracuseStep 319609 = 239707) (by norm_num)
theorem B712901 : Blo 279826 712901 := bbase (se 4 (by rfl) ⟨66834, by rfl⟩ : syracuseStep 712901 = 133669) (by norm_num)
theorem B1138949 : Blo 279826 1138949 := bbase (se 4 (by rfl) ⟨106776, by rfl⟩ : syracuseStep 1138949 = 213553) (by norm_num)
theorem B1433861 : Blo 279826 1433861 := bbase (se 4 (by rfl) ⟨134424, by rfl⟩ : syracuseStep 1433861 = 268849) (by norm_num)
theorem B483725 : Blo 279826 483725 := bbase (se 3 (by rfl) ⟨90698, by rfl⟩ : syracuseStep 483725 = 181397) (by norm_num)
theorem B287129 : Blo 279826 287129 := bbase (se 2 (by rfl) ⟨107673, by rfl⟩ : syracuseStep 287129 = 215347) (by norm_num)
theorem B1597877 : Blo 279826 1597877 := bbase (se 5 (by rfl) ⟨74900, by rfl⟩ : syracuseStep 1597877 = 149801) (by norm_num)
theorem B713245 : Blo 279826 713245 := bbase (se 3 (by rfl) ⟨133733, by rfl⟩ : syracuseStep 713245 = 267467) (by norm_num)
theorem B516709 : Blo 279826 516709 := bbase (se 4 (by rfl) ⟨48441, by rfl⟩ : syracuseStep 516709 = 96883) (by norm_num)
theorem B713357 : Blo 279826 713357 := bbase (se 3 (by rfl) ⟨133754, by rfl⟩ : syracuseStep 713357 = 267509) (by norm_num)
theorem B1204901 : Blo 279826 1204901 := bbase (se 4 (by rfl) ⟨112959, by rfl⟩ : syracuseStep 1204901 = 225919) (by norm_num)
theorem B320221 : Blo 279826 320221 := bbase (se 3 (by rfl) ⟨60041, by rfl⟩ : syracuseStep 320221 = 120083) (by norm_num)
theorem B713549 : Blo 279826 713549 := bbase (se 3 (by rfl) ⟨133790, by rfl⟩ : syracuseStep 713549 = 267581) (by norm_num)
theorem B2417525 : Blo 279826 2417525 := bbase (se 5 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 2417525 = 226643) (by norm_num)
theorem B287693 : Blo 279826 287693 := bbase (se 3 (by rfl) ⟨53942, by rfl⟩ : syracuseStep 287693 = 107885) (by norm_num)
theorem B385997 : Blo 279826 385997 := bbase (se 3 (by rfl) ⟨72374, by rfl⟩ : syracuseStep 385997 = 144749) (by norm_num)
theorem B1074181 : Blo 279826 1074181 := bbase (se 4 (by rfl) ⟨100704, by rfl⟩ : syracuseStep 1074181 = 201409) (by norm_num)
theorem B320521 : Blo 279826 320521 := bbase (se 2 (by rfl) ⟨120195, by rfl⟩ : syracuseStep 320521 = 240391) (by norm_num)
theorem B713893 : Blo 279826 713893 := bbase (se 4 (by rfl) ⟨66927, by rfl⟩ : syracuseStep 713893 = 133855) (by norm_num)
theorem B451813 : Blo 279826 451813 := bbase (se 4 (by rfl) ⟨42357, by rfl⟩ : syracuseStep 451813 = 84715) (by norm_num)
theorem B714005 : Blo 279826 714005 := bbase (se 6 (by rfl) ⟨16734, by rfl⟩ : syracuseStep 714005 = 33469) (by norm_num)
theorem B582941 : Blo 279826 582941 := bbase (se 3 (by rfl) ⟨109301, by rfl⟩ : syracuseStep 582941 = 218603) (by norm_num)
theorem B2876725 : Blo 279826 2876725 := bbase (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) (by norm_num)
theorem B1074485 : Blo 279826 1074485 := bbase (se 5 (by rfl) ⟨50366, by rfl⟩ : syracuseStep 1074485 = 100733) (by norm_num)
theorem B1140149 : Blo 279826 1140149 := bbase (se 5 (by rfl) ⟨53444, by rfl⟩ : syracuseStep 1140149 = 106889) (by norm_num)
theorem B517565 : Blo 279826 517565 := bbase (se 3 (by rfl) ⟨97043, by rfl⟩ : syracuseStep 517565 = 194087) (by norm_num)
theorem B714197 : Blo 279826 714197 := bbase (se 7 (by rfl) ⟨8369, by rfl⟩ : syracuseStep 714197 = 16739) (by norm_num)
theorem B452069 : Blo 279826 452069 := bbase (se 4 (by rfl) ⟨42381, by rfl⟩ : syracuseStep 452069 = 84763) (by norm_num)
theorem B1435157 : Blo 279826 1435157 := bbase (se 6 (by rfl) ⟨33636, by rfl⟩ : syracuseStep 1435157 = 67273) (by norm_num)
theorem B1599061 : Blo 279826 1599061 := bbase (se 8 (by rfl) ⟨9369, by rfl⟩ : syracuseStep 1599061 = 18739) (by norm_num)
theorem B3434069 : Blo 279826 3434069 := bbase (se 8 (by rfl) ⟨20121, by rfl⟩ : syracuseStep 3434069 = 40243) (by norm_num)
theorem B452261 : Blo 279826 452261 := bbase (se 4 (by rfl) ⟨42399, by rfl⟩ : syracuseStep 452261 = 84799) (by norm_num)
theorem B714541 : Blo 279826 714541 := bbase (se 3 (by rfl) ⟨133976, by rfl⟩ : syracuseStep 714541 = 267953) (by norm_num)
theorem B419741 : Blo 279826 419741 := bbase (se 3 (by rfl) ⟨78701, by rfl⟩ : syracuseStep 419741 = 157403) (by norm_num)
theorem B714653 : Blo 279826 714653 := bbase (se 3 (by rfl) ⟨133997, by rfl⟩ : syracuseStep 714653 = 267995) (by norm_num)
theorem B419765 : Blo 279826 419765 := bbase (se 5 (by rfl) ⟨19676, by rfl⟩ : syracuseStep 419765 = 39353) (by norm_num)
theorem B354233 : Blo 279826 354233 := bbase (se 2 (by rfl) ⟨132837, by rfl⟩ : syracuseStep 354233 = 265675) (by norm_num)
theorem B419789 : Blo 279826 419789 := bbase (se 3 (by rfl) ⟨78710, by rfl⟩ : syracuseStep 419789 = 157421) (by norm_num)
theorem B419813 : Blo 279826 419813 := bbase (se 4 (by rfl) ⟨39357, by rfl⟩ : syracuseStep 419813 = 78715) (by norm_num)
theorem B354289 : Blo 279826 354289 := bbase (se 2 (by rfl) ⟨132858, by rfl⟩ : syracuseStep 354289 = 265717) (by norm_num)
theorem B419837 : Blo 279826 419837 := bbase (se 3 (by rfl) ⟨78719, by rfl⟩ : syracuseStep 419837 = 157439) (by norm_num)
theorem B419861 : Blo 279826 419861 := bbase (se 6 (by rfl) ⟨9840, by rfl⟩ : syracuseStep 419861 = 19681) (by norm_num)
theorem B419885 : Blo 279826 419885 := bbase (se 3 (by rfl) ⟨78728, by rfl⟩ : syracuseStep 419885 = 157457) (by norm_num)
theorem B419909 : Blo 279826 419909 := bbase (se 4 (by rfl) ⟨39366, by rfl⟩ : syracuseStep 419909 = 78733) (by norm_num)
theorem B354385 : Blo 279826 354385 := bbase (se 2 (by rfl) ⟨132894, by rfl⟩ : syracuseStep 354385 = 265789) (by norm_num)
theorem B485461 : Blo 279826 485461 := bbase (se 8 (by rfl) ⟨2844, by rfl⟩ : syracuseStep 485461 = 5689) (by norm_num)
theorem B419933 : Blo 279826 419933 := bbase (se 3 (by rfl) ⟨78737, by rfl⟩ : syracuseStep 419933 = 157475) (by norm_num)
theorem B714845 : Blo 279826 714845 := bbase (se 3 (by rfl) ⟨134033, by rfl⟩ : syracuseStep 714845 = 268067) (by norm_num)
theorem B419957 : Blo 279826 419957 := bbase (se 5 (by rfl) ⟨19685, by rfl⟩ : syracuseStep 419957 = 39371) (by norm_num)
theorem B419981 : Blo 279826 419981 := bbase (se 3 (by rfl) ⟨78746, by rfl⟩ : syracuseStep 419981 = 157493) (by norm_num)
theorem B420005 : Blo 279826 420005 := bbase (se 4 (by rfl) ⟨39375, by rfl⟩ : syracuseStep 420005 = 78751) (by norm_num)
theorem B420029 : Blo 279826 420029 := bbase (se 3 (by rfl) ⟨78755, by rfl⟩ : syracuseStep 420029 = 157511) (by norm_num)
theorem B420053 : Blo 279826 420053 := bbase (se 7 (by rfl) ⟨4922, by rfl⟩ : syracuseStep 420053 = 9845) (by norm_num)
theorem B420077 : Blo 279826 420077 := bbase (se 3 (by rfl) ⟨78764, by rfl⟩ : syracuseStep 420077 = 157529) (by norm_num)
theorem B354557 : Blo 279826 354557 := bbase (se 3 (by rfl) ⟨66479, by rfl⟩ : syracuseStep 354557 = 132959) (by norm_num)
theorem B420101 : Blo 279826 420101 := bbase (se 4 (by rfl) ⟨39384, by rfl⟩ : syracuseStep 420101 = 78769) (by norm_num)
theorem B420125 : Blo 279826 420125 := bbase (se 3 (by rfl) ⟨78773, by rfl⟩ : syracuseStep 420125 = 157547) (by norm_num)
theorem B420149 : Blo 279826 420149 := bbase (se 5 (by rfl) ⟨19694, by rfl⟩ : syracuseStep 420149 = 39389) (by norm_num)
theorem B354613 : Blo 279826 354613 := bbase (se 5 (by rfl) ⟨16622, by rfl⟩ : syracuseStep 354613 = 33245) (by norm_num)
theorem B420173 : Blo 279826 420173 := bbase (se 3 (by rfl) ⟨78782, by rfl⟩ : syracuseStep 420173 = 157565) (by norm_num)
theorem B4811093 : Blo 279826 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B420197 : Blo 279826 420197 := bbase (se 4 (by rfl) ⟨39393, by rfl⟩ : syracuseStep 420197 = 78787) (by norm_num)
theorem B420221 : Blo 279826 420221 := bbase (se 3 (by rfl) ⟨78791, by rfl⟩ : syracuseStep 420221 = 157583) (by norm_num)
theorem B420245 : Blo 279826 420245 := bbase (se 6 (by rfl) ⟨9849, by rfl⟩ : syracuseStep 420245 = 19699) (by norm_num)
theorem B354709 : Blo 279826 354709 := bbase (se 6 (by rfl) ⟨8313, by rfl⟩ : syracuseStep 354709 = 16627) (by norm_num)
theorem B1206677 : Blo 279826 1206677 := bbase (se 6 (by rfl) ⟨28281, by rfl⟩ : syracuseStep 1206677 = 56563) (by norm_num)
theorem B420269 : Blo 279826 420269 := bbase (se 3 (by rfl) ⟨78800, by rfl⟩ : syracuseStep 420269 = 157601) (by norm_num)
theorem B715189 : Blo 279826 715189 := bbase (se 5 (by rfl) ⟨33524, by rfl⟩ : syracuseStep 715189 = 67049) (by norm_num)
theorem B420293 : Blo 279826 420293 := bbase (se 4 (by rfl) ⟨39402, by rfl⟩ : syracuseStep 420293 = 78805) (by norm_num)
theorem B420317 : Blo 279826 420317 := bbase (se 3 (by rfl) ⟨78809, by rfl⟩ : syracuseStep 420317 = 157619) (by norm_num)
theorem B420341 : Blo 279826 420341 := bbase (se 5 (by rfl) ⟨19703, by rfl⟩ : syracuseStep 420341 = 39407) (by norm_num)
theorem B420365 : Blo 279826 420365 := bbase (se 3 (by rfl) ⟨78818, by rfl⟩ : syracuseStep 420365 = 157637) (by norm_num)
theorem B420389 : Blo 279826 420389 := bbase (se 4 (by rfl) ⟨39411, by rfl⟩ : syracuseStep 420389 = 78823) (by norm_num)
theorem B715301 : Blo 279826 715301 := bbase (se 4 (by rfl) ⟨67059, by rfl⟩ : syracuseStep 715301 = 134119) (by norm_num)
theorem B420413 : Blo 279826 420413 := bbase (se 3 (by rfl) ⟨78827, by rfl⟩ : syracuseStep 420413 = 157655) (by norm_num)
theorem B354881 : Blo 279826 354881 := bbase (se 2 (by rfl) ⟨133080, by rfl⟩ : syracuseStep 354881 = 266161) (by norm_num)
theorem B322117 : Blo 279826 322117 := bbase (se 4 (by rfl) ⟨30198, by rfl⟩ : syracuseStep 322117 = 60397) (by norm_num)
theorem B453197 : Blo 279826 453197 := bbase (se 3 (by rfl) ⟨84974, by rfl⟩ : syracuseStep 453197 = 169949) (by norm_num)
theorem B420437 : Blo 279826 420437 := bbase (se 8 (by rfl) ⟨2463, by rfl⟩ : syracuseStep 420437 = 4927) (by norm_num)
theorem B2878037 : Blo 279826 2878037 := bbase (se 8 (by rfl) ⟨16863, by rfl⟩ : syracuseStep 2878037 = 33727) (by norm_num)
theorem B420461 : Blo 279826 420461 := bbase (se 3 (by rfl) ⟨78836, by rfl⟩ : syracuseStep 420461 = 157673) (by norm_num)
theorem B354937 : Blo 279826 354937 := bbase (se 2 (by rfl) ⟨133101, by rfl⟩ : syracuseStep 354937 = 266203) (by norm_num)
theorem B420485 : Blo 279826 420485 := bbase (se 4 (by rfl) ⟨39420, by rfl⟩ : syracuseStep 420485 = 78841) (by norm_num)
theorem B420509 : Blo 279826 420509 := bbase (se 3 (by rfl) ⟨78845, by rfl⟩ : syracuseStep 420509 = 157691) (by norm_num)
theorem B420533 : Blo 279826 420533 := bbase (se 5 (by rfl) ⟨19712, by rfl⟩ : syracuseStep 420533 = 39425) (by norm_num)
theorem B944837 : Blo 279826 944837 := bbase (se 4 (by rfl) ⟨88578, by rfl⟩ : syracuseStep 944837 = 177157) (by norm_num)
theorem B420557 : Blo 279826 420557 := bbase (se 3 (by rfl) ⟨78854, by rfl⟩ : syracuseStep 420557 = 157709) (by norm_num)
theorem B355033 : Blo 279826 355033 := bbase (se 2 (by rfl) ⟨133137, by rfl⟩ : syracuseStep 355033 = 266275) (by norm_num)
theorem B420581 : Blo 279826 420581 := bbase (se 4 (by rfl) ⟨39429, by rfl⟩ : syracuseStep 420581 = 78859) (by norm_num)
theorem B715493 : Blo 279826 715493 := bbase (se 4 (by rfl) ⟨67077, by rfl⟩ : syracuseStep 715493 = 134155) (by norm_num)
theorem B420605 : Blo 279826 420605 := bbase (se 3 (by rfl) ⟨78863, by rfl⟩ : syracuseStep 420605 = 157727) (by norm_num)
theorem B420629 : Blo 279826 420629 := bbase (se 6 (by rfl) ⟨9858, by rfl⟩ : syracuseStep 420629 = 19717) (by norm_num)
theorem B1436453 : Blo 279826 1436453 := bbase (se 4 (by rfl) ⟨134667, by rfl⟩ : syracuseStep 1436453 = 269335) (by norm_num)
theorem B420653 : Blo 279826 420653 := bbase (se 3 (by rfl) ⟨78872, by rfl⟩ : syracuseStep 420653 = 157745) (by norm_num)
theorem B420677 : Blo 279826 420677 := bbase (se 4 (by rfl) ⟨39438, by rfl⟩ : syracuseStep 420677 = 78877) (by norm_num)
theorem B420701 : Blo 279826 420701 := bbase (se 3 (by rfl) ⟨78881, by rfl⟩ : syracuseStep 420701 = 157763) (by norm_num)
theorem B420725 : Blo 279826 420725 := bbase (se 5 (by rfl) ⟨19721, by rfl⟩ : syracuseStep 420725 = 39443) (by norm_num)
theorem B355205 : Blo 279826 355205 := bbase (se 4 (by rfl) ⟨33300, by rfl⟩ : syracuseStep 355205 = 66601) (by norm_num)
theorem B420749 : Blo 279826 420749 := bbase (se 3 (by rfl) ⟨78890, by rfl⟩ : syracuseStep 420749 = 157781) (by norm_num)
theorem B519077 : Blo 279826 519077 := bbase (se 4 (by rfl) ⟨48663, by rfl⟩ : syracuseStep 519077 = 97327) (by norm_num)
theorem B420773 : Blo 279826 420773 := bbase (se 4 (by rfl) ⟨39447, by rfl⟩ : syracuseStep 420773 = 78895) (by norm_num)
theorem B420797 : Blo 279826 420797 := bbase (se 3 (by rfl) ⟨78899, by rfl⟩ : syracuseStep 420797 = 157799) (by norm_num)
theorem B355261 : Blo 279826 355261 := bbase (se 3 (by rfl) ⟨66611, by rfl⟩ : syracuseStep 355261 = 133223) (by norm_num)
theorem B453581 : Blo 279826 453581 := bbase (se 3 (by rfl) ⟨85046, by rfl⟩ : syracuseStep 453581 = 170093) (by norm_num)
theorem B420821 : Blo 279826 420821 := bbase (se 7 (by rfl) ⟨4931, by rfl⟩ : syracuseStep 420821 = 9863) (by norm_num)
theorem B420845 : Blo 279826 420845 := bbase (se 3 (by rfl) ⟨78908, by rfl⟩ : syracuseStep 420845 = 157817) (by norm_num)
theorem B420869 : Blo 279826 420869 := bbase (se 4 (by rfl) ⟨39456, by rfl⟩ : syracuseStep 420869 = 78913) (by norm_num)
theorem B420893 : Blo 279826 420893 := bbase (se 3 (by rfl) ⟨78917, by rfl⟩ : syracuseStep 420893 = 157835) (by norm_num)
theorem B355357 : Blo 279826 355357 := bbase (se 3 (by rfl) ⟨66629, by rfl⟩ : syracuseStep 355357 = 133259) (by norm_num)
theorem B420917 : Blo 279826 420917 := bbase (se 5 (by rfl) ⟨19730, by rfl⟩ : syracuseStep 420917 = 39461) (by norm_num)
theorem B715837 : Blo 279826 715837 := bbase (se 3 (by rfl) ⟨134219, by rfl⟩ : syracuseStep 715837 = 268439) (by norm_num)
theorem B420941 : Blo 279826 420941 := bbase (se 3 (by rfl) ⟨78926, by rfl⟩ : syracuseStep 420941 = 157853) (by norm_num)
theorem B453709 : Blo 279826 453709 := bbase (se 3 (by rfl) ⟨85070, by rfl⟩ : syracuseStep 453709 = 170141) (by norm_num)
theorem B420965 : Blo 279826 420965 := bbase (se 4 (by rfl) ⟨39465, by rfl⟩ : syracuseStep 420965 = 78931) (by norm_num)
theorem B945269 : Blo 279826 945269 := bbase (se 5 (by rfl) ⟨44309, by rfl⟩ : syracuseStep 945269 = 88619) (by norm_num)
theorem B420989 : Blo 279826 420989 := bbase (se 3 (by rfl) ⟨78935, by rfl⟩ : syracuseStep 420989 = 157871) (by norm_num)
theorem B421013 : Blo 279826 421013 := bbase (se 6 (by rfl) ⟨9867, by rfl⟩ : syracuseStep 421013 = 19735) (by norm_num)
theorem B421037 : Blo 279826 421037 := bbase (se 3 (by rfl) ⟨78944, by rfl⟩ : syracuseStep 421037 = 157889) (by norm_num)
theorem B715949 : Blo 279826 715949 := bbase (se 3 (by rfl) ⟨134240, by rfl⟩ : syracuseStep 715949 = 268481) (by norm_num)
theorem B421061 : Blo 279826 421061 := bbase (se 4 (by rfl) ⟨39474, by rfl⟩ : syracuseStep 421061 = 78949) (by norm_num)
theorem B355529 : Blo 279826 355529 := bbase (se 2 (by rfl) ⟨133323, by rfl⟩ : syracuseStep 355529 = 266647) (by norm_num)
theorem B421085 : Blo 279826 421085 := bbase (se 3 (by rfl) ⟨78953, by rfl⟩ : syracuseStep 421085 = 157907) (by norm_num)
theorem B421109 : Blo 279826 421109 := bbase (se 5 (by rfl) ⟨19739, by rfl⟩ : syracuseStep 421109 = 39479) (by norm_num)
theorem B355585 : Blo 279826 355585 := bbase (se 2 (by rfl) ⟨133344, by rfl⟩ : syracuseStep 355585 = 266689) (by norm_num)
theorem B421133 : Blo 279826 421133 := bbase (se 3 (by rfl) ⟨78962, by rfl⟩ : syracuseStep 421133 = 157925) (by norm_num)
theorem B421157 : Blo 279826 421157 := bbase (se 4 (by rfl) ⟨39483, by rfl⟩ : syracuseStep 421157 = 78967) (by norm_num)
theorem B421181 : Blo 279826 421181 := bbase (se 3 (by rfl) ⟨78971, by rfl⟩ : syracuseStep 421181 = 157943) (by norm_num)
theorem B552253 : Blo 279826 552253 := bbase (se 3 (by rfl) ⟨103547, by rfl⟩ : syracuseStep 552253 = 207095) (by norm_num)
theorem B1469765 : Blo 279826 1469765 := bbase (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) (by norm_num)
theorem B421205 : Blo 279826 421205 := bbase (se 11 (by rfl) ⟨308, by rfl⟩ : syracuseStep 421205 = 617) (by norm_num)
theorem B355681 : Blo 279826 355681 := bbase (se 2 (by rfl) ⟨133380, by rfl⟩ : syracuseStep 355681 = 266761) (by norm_num)
theorem B421229 : Blo 279826 421229 := bbase (se 3 (by rfl) ⟨78980, by rfl⟩ : syracuseStep 421229 = 157961) (by norm_num)
theorem B716141 : Blo 279826 716141 := bbase (se 3 (by rfl) ⟨134276, by rfl⟩ : syracuseStep 716141 = 268553) (by norm_num)
theorem B1207669 : Blo 279826 1207669 := bbase (se 5 (by rfl) ⟨56609, by rfl⟩ : syracuseStep 1207669 = 113219) (by norm_num)
theorem B1076597 : Blo 279826 1076597 := bbase (se 5 (by rfl) ⟨50465, by rfl⟩ : syracuseStep 1076597 = 100931) (by norm_num)
theorem B421253 : Blo 279826 421253 := bbase (se 4 (by rfl) ⟨39492, by rfl⟩ : syracuseStep 421253 = 78985) (by norm_num)
theorem B421277 : Blo 279826 421277 := bbase (se 3 (by rfl) ⟨78989, by rfl⟩ : syracuseStep 421277 = 157979) (by norm_num)
theorem B421301 : Blo 279826 421301 := bbase (se 5 (by rfl) ⟨19748, by rfl⟩ : syracuseStep 421301 = 39497) (by norm_num)
theorem B421325 : Blo 279826 421325 := bbase (se 3 (by rfl) ⟨78998, by rfl⟩ : syracuseStep 421325 = 157997) (by norm_num)
theorem B421349 : Blo 279826 421349 := bbase (se 4 (by rfl) ⟨39501, by rfl⟩ : syracuseStep 421349 = 79003) (by norm_num)
theorem B421373 : Blo 279826 421373 := bbase (se 3 (by rfl) ⟨79007, by rfl⟩ : syracuseStep 421373 = 158015) (by norm_num)
theorem B355853 : Blo 279826 355853 := bbase (se 3 (by rfl) ⟨66722, by rfl⟩ : syracuseStep 355853 = 133445) (by norm_num)
theorem B421397 : Blo 279826 421397 := bbase (se 6 (by rfl) ⟨9876, by rfl⟩ : syracuseStep 421397 = 19753) (by norm_num)
theorem B1601045 : Blo 279826 1601045 := bbase (se 6 (by rfl) ⟨37524, by rfl⟩ : syracuseStep 1601045 = 75049) (by norm_num)
theorem B945701 : Blo 279826 945701 := bbase (se 4 (by rfl) ⟨88659, by rfl⟩ : syracuseStep 945701 = 177319) (by norm_num)
theorem B421421 : Blo 279826 421421 := bbase (se 3 (by rfl) ⟨79016, by rfl⟩ : syracuseStep 421421 = 158033) (by norm_num)
theorem B421445 : Blo 279826 421445 := bbase (se 4 (by rfl) ⟨39510, by rfl⟩ : syracuseStep 421445 = 79021) (by norm_num)
theorem B355909 : Blo 279826 355909 := bbase (se 4 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 355909 = 66733) (by norm_num)
theorem B421469 : Blo 279826 421469 := bbase (se 3 (by rfl) ⟨79025, by rfl⟩ : syracuseStep 421469 = 158051) (by norm_num)
theorem B421493 : Blo 279826 421493 := bbase (se 5 (by rfl) ⟨19757, by rfl⟩ : syracuseStep 421493 = 39515) (by norm_num)
theorem B421517 : Blo 279826 421517 := bbase (se 3 (by rfl) ⟨79034, by rfl⟩ : syracuseStep 421517 = 158069) (by norm_num)
theorem B1076885 : Blo 279826 1076885 := bbase (se 6 (by rfl) ⟨25239, by rfl⟩ : syracuseStep 1076885 = 50479) (by norm_num)
theorem B421541 : Blo 279826 421541 := bbase (se 4 (by rfl) ⟨39519, by rfl⟩ : syracuseStep 421541 = 79039) (by norm_num)
theorem B356005 : Blo 279826 356005 := bbase (se 4 (by rfl) ⟨33375, by rfl⟩ : syracuseStep 356005 = 66751) (by norm_num)
theorem B323249 : Blo 279826 323249 := bbase (se 2 (by rfl) ⟨121218, by rfl⟩ : syracuseStep 323249 = 242437) (by norm_num)
theorem B421565 : Blo 279826 421565 := bbase (se 3 (by rfl) ⟨79043, by rfl⟩ : syracuseStep 421565 = 158087) (by norm_num)
theorem B716485 : Blo 279826 716485 := bbase (se 4 (by rfl) ⟨67170, by rfl⟩ : syracuseStep 716485 = 134341) (by norm_num)
theorem B421589 : Blo 279826 421589 := bbase (se 7 (by rfl) ⟨4940, by rfl⟩ : syracuseStep 421589 = 9881) (by norm_num)
theorem B323285 : Blo 279826 323285 := bbase (se 7 (by rfl) ⟨3788, by rfl⟩ : syracuseStep 323285 = 7577) (by norm_num)
theorem B421613 : Blo 279826 421613 := bbase (se 3 (by rfl) ⟨79052, by rfl⟩ : syracuseStep 421613 = 158105) (by norm_num)
theorem B421637 : Blo 279826 421637 := bbase (se 4 (by rfl) ⟨39528, by rfl⟩ : syracuseStep 421637 = 79057) (by norm_num)
theorem B1142549 : Blo 279826 1142549 := bbase (se 6 (by rfl) ⟨26778, by rfl⟩ : syracuseStep 1142549 = 53557) (by norm_num)
theorem B421661 : Blo 279826 421661 := bbase (se 3 (by rfl) ⟨79061, by rfl⟩ : syracuseStep 421661 = 158123) (by norm_num)
theorem B421685 : Blo 279826 421685 := bbase (se 5 (by rfl) ⟨19766, by rfl⟩ : syracuseStep 421685 = 39533) (by norm_num)
theorem B716597 : Blo 279826 716597 := bbase (se 5 (by rfl) ⟨33590, by rfl⟩ : syracuseStep 716597 = 67181) (by norm_num)
theorem B421709 : Blo 279826 421709 := bbase (se 3 (by rfl) ⟨79070, by rfl⟩ : syracuseStep 421709 = 158141) (by norm_num)
theorem B356177 : Blo 279826 356177 := bbase (se 2 (by rfl) ⟨133566, by rfl⟩ : syracuseStep 356177 = 267133) (by norm_num)
theorem B421733 : Blo 279826 421733 := bbase (se 4 (by rfl) ⟨39537, by rfl⟩ : syracuseStep 421733 = 79075) (by norm_num)
theorem B421757 : Blo 279826 421757 := bbase (se 3 (by rfl) ⟨79079, by rfl⟩ : syracuseStep 421757 = 158159) (by norm_num)
theorem B356233 : Blo 279826 356233 := bbase (se 2 (by rfl) ⟨133587, by rfl⟩ : syracuseStep 356233 = 267175) (by norm_num)
theorem B421781 : Blo 279826 421781 := bbase (se 6 (by rfl) ⟨9885, by rfl⟩ : syracuseStep 421781 = 19771) (by norm_num)
theorem B421805 : Blo 279826 421805 := bbase (se 3 (by rfl) ⟨79088, by rfl⟩ : syracuseStep 421805 = 158177) (by norm_num)
theorem B421829 : Blo 279826 421829 := bbase (se 4 (by rfl) ⟨39546, by rfl⟩ : syracuseStep 421829 = 79093) (by norm_num)
theorem B946133 : Blo 279826 946133 := bbase (se 7 (by rfl) ⟨11087, by rfl⟩ : syracuseStep 946133 = 22175) (by norm_num)
theorem B421853 : Blo 279826 421853 := bbase (se 3 (by rfl) ⟨79097, by rfl⟩ : syracuseStep 421853 = 158195) (by norm_num)
theorem B356329 : Blo 279826 356329 := bbase (se 2 (by rfl) ⟨133623, by rfl⟩ : syracuseStep 356329 = 267247) (by norm_num)
theorem B421877 : Blo 279826 421877 := bbase (se 5 (by rfl) ⟨19775, by rfl⟩ : syracuseStep 421877 = 39551) (by norm_num)
theorem B716789 : Blo 279826 716789 := bbase (se 5 (by rfl) ⟨33599, by rfl⟩ : syracuseStep 716789 = 67199) (by norm_num)
theorem B421901 : Blo 279826 421901 := bbase (se 3 (by rfl) ⟨79106, by rfl⟩ : syracuseStep 421901 = 158213) (by norm_num)
theorem B421925 : Blo 279826 421925 := bbase (se 4 (by rfl) ⟨39555, by rfl⟩ : syracuseStep 421925 = 79111) (by norm_num)
theorem B421949 : Blo 279826 421949 := bbase (se 3 (by rfl) ⟨79115, by rfl⟩ : syracuseStep 421949 = 158231) (by norm_num)
theorem B421973 : Blo 279826 421973 := bbase (se 8 (by rfl) ⟨2472, by rfl⟩ : syracuseStep 421973 = 4945) (by norm_num)
theorem B421997 : Blo 279826 421997 := bbase (se 3 (by rfl) ⟨79124, by rfl⟩ : syracuseStep 421997 = 158249) (by norm_num)
theorem B422021 : Blo 279826 422021 := bbase (se 4 (by rfl) ⟨39564, by rfl⟩ : syracuseStep 422021 = 79129) (by norm_num)
theorem B389269 : Blo 279826 389269 := bbase (se 6 (by rfl) ⟨9123, by rfl⟩ : syracuseStep 389269 = 18247) (by norm_num)
theorem B356501 : Blo 279826 356501 := bbase (se 6 (by rfl) ⟨8355, by rfl⟩ : syracuseStep 356501 = 16711) (by norm_num)
theorem B422045 : Blo 279826 422045 := bbase (se 3 (by rfl) ⟨79133, by rfl⟩ : syracuseStep 422045 = 158267) (by norm_num)
theorem B618653 : Blo 279826 618653 := bbase (se 3 (by rfl) ⟨115997, by rfl⟩ : syracuseStep 618653 = 231995) (by norm_num)
theorem B422069 : Blo 279826 422069 := bbase (se 5 (by rfl) ⟨19784, by rfl⟩ : syracuseStep 422069 = 39569) (by norm_num)
theorem B422093 : Blo 279826 422093 := bbase (se 3 (by rfl) ⟨79142, by rfl⟩ : syracuseStep 422093 = 158285) (by norm_num)
theorem B356557 : Blo 279826 356557 := bbase (se 3 (by rfl) ⟨66854, by rfl⟩ : syracuseStep 356557 = 133709) (by norm_num)
theorem B422117 : Blo 279826 422117 := bbase (se 4 (by rfl) ⟨39573, by rfl⟩ : syracuseStep 422117 = 79147) (by norm_num)
theorem B422141 : Blo 279826 422141 := bbase (se 3 (by rfl) ⟨79151, by rfl⟩ : syracuseStep 422141 = 158303) (by norm_num)
theorem B291089 : Blo 279826 291089 := bbase (se 2 (by rfl) ⟨109158, by rfl⟩ : syracuseStep 291089 = 218317) (by norm_num)
theorem B422165 : Blo 279826 422165 := bbase (se 6 (by rfl) ⟨9894, by rfl⟩ : syracuseStep 422165 = 19789) (by norm_num)
theorem B422189 : Blo 279826 422189 := bbase (se 3 (by rfl) ⟨79160, by rfl⟩ : syracuseStep 422189 = 158321) (by norm_num)
theorem B356653 : Blo 279826 356653 := bbase (se 3 (by rfl) ⟨66872, by rfl⟩ : syracuseStep 356653 = 133745) (by norm_num)
theorem B422213 : Blo 279826 422213 := bbase (se 4 (by rfl) ⟨39582, by rfl⟩ : syracuseStep 422213 = 79165) (by norm_num)
theorem B717133 : Blo 279826 717133 := bbase (se 3 (by rfl) ⟨134462, by rfl⟩ : syracuseStep 717133 = 268925) (by norm_num)
theorem B422237 : Blo 279826 422237 := bbase (se 3 (by rfl) ⟨79169, by rfl⟩ : syracuseStep 422237 = 158339) (by norm_num)
theorem B422261 : Blo 279826 422261 := bbase (se 5 (by rfl) ⟨19793, by rfl⟩ : syracuseStep 422261 = 39587) (by norm_num)
theorem B946565 : Blo 279826 946565 := bbase (se 4 (by rfl) ⟨88740, by rfl⟩ : syracuseStep 946565 = 177481) (by norm_num)
theorem B422285 : Blo 279826 422285 := bbase (se 3 (by rfl) ⟨79178, by rfl⟩ : syracuseStep 422285 = 158357) (by norm_num)
theorem B422309 : Blo 279826 422309 := bbase (se 4 (by rfl) ⟨39591, by rfl⟩ : syracuseStep 422309 = 79183) (by norm_num)
theorem B422333 : Blo 279826 422333 := bbase (se 3 (by rfl) ⟨79187, by rfl⟩ : syracuseStep 422333 = 158375) (by norm_num)
theorem B717245 : Blo 279826 717245 := bbase (se 3 (by rfl) ⟨134483, by rfl⟩ : syracuseStep 717245 = 268967) (by norm_num)
theorem B422357 : Blo 279826 422357 := bbase (se 7 (by rfl) ⟨4949, by rfl⟩ : syracuseStep 422357 = 9899) (by norm_num)
theorem B356825 : Blo 279826 356825 := bbase (se 2 (by rfl) ⟨133809, by rfl⟩ : syracuseStep 356825 = 267619) (by norm_num)
theorem B422381 : Blo 279826 422381 := bbase (se 3 (by rfl) ⟨79196, by rfl⟩ : syracuseStep 422381 = 158393) (by norm_num)
theorem B422405 : Blo 279826 422405 := bbase (se 4 (by rfl) ⟨39600, by rfl⟩ : syracuseStep 422405 = 79201) (by norm_num)
theorem B356881 : Blo 279826 356881 := bbase (se 2 (by rfl) ⟨133830, by rfl⟩ : syracuseStep 356881 = 267661) (by norm_num)
theorem B422429 : Blo 279826 422429 := bbase (se 3 (by rfl) ⟨79205, by rfl⟩ : syracuseStep 422429 = 158411) (by norm_num)
theorem B422453 : Blo 279826 422453 := bbase (se 5 (by rfl) ⟨19802, by rfl⟩ : syracuseStep 422453 = 39605) (by norm_num)
theorem B422477 : Blo 279826 422477 := bbase (se 3 (by rfl) ⟨79214, by rfl⟩ : syracuseStep 422477 = 158429) (by norm_num)
theorem B422501 : Blo 279826 422501 := bbase (se 4 (by rfl) ⟨39609, by rfl⟩ : syracuseStep 422501 = 79219) (by norm_num)
theorem B356977 : Blo 279826 356977 := bbase (se 2 (by rfl) ⟨133866, by rfl⟩ : syracuseStep 356977 = 267733) (by norm_num)
theorem B422525 : Blo 279826 422525 := bbase (se 3 (by rfl) ⟨79223, by rfl⟩ : syracuseStep 422525 = 158447) (by norm_num)
theorem B717437 : Blo 279826 717437 := bbase (se 3 (by rfl) ⟨134519, by rfl⟩ : syracuseStep 717437 = 269039) (by norm_num)
theorem B422549 : Blo 279826 422549 := bbase (se 6 (by rfl) ⟨9903, by rfl⟩ : syracuseStep 422549 = 19807) (by norm_num)
theorem B422573 : Blo 279826 422573 := bbase (se 3 (by rfl) ⟨79232, by rfl⟩ : syracuseStep 422573 = 158465) (by norm_num)
theorem B422597 : Blo 279826 422597 := bbase (se 4 (by rfl) ⟨39618, by rfl⟩ : syracuseStep 422597 = 79237) (by norm_num)
theorem B422621 : Blo 279826 422621 := bbase (se 3 (by rfl) ⟨79241, by rfl⟩ : syracuseStep 422621 = 158483) (by norm_num)
theorem B422645 : Blo 279826 422645 := bbase (se 5 (by rfl) ⟨19811, by rfl⟩ : syracuseStep 422645 = 39623) (by norm_num)
theorem B422669 : Blo 279826 422669 := bbase (se 3 (by rfl) ⟨79250, by rfl⟩ : syracuseStep 422669 = 158501) (by norm_num)
theorem B357149 : Blo 279826 357149 := bbase (se 3 (by rfl) ⟨66965, by rfl⟩ : syracuseStep 357149 = 133931) (by norm_num)
theorem B422693 : Blo 279826 422693 := bbase (se 4 (by rfl) ⟨39627, by rfl⟩ : syracuseStep 422693 = 79255) (by norm_num)
theorem B946997 : Blo 279826 946997 := bbase (se 5 (by rfl) ⟨44390, by rfl⟩ : syracuseStep 946997 = 88781) (by norm_num)
theorem B422717 : Blo 279826 422717 := bbase (se 3 (by rfl) ⟨79259, by rfl⟩ : syracuseStep 422717 = 158519) (by norm_num)
theorem B422741 : Blo 279826 422741 := bbase (se 9 (by rfl) ⟨1238, by rfl⟩ : syracuseStep 422741 = 2477) (by norm_num)
theorem B357205 : Blo 279826 357205 := bbase (se 9 (by rfl) ⟨1046, by rfl⟩ : syracuseStep 357205 = 2093) (by norm_num)
theorem B422765 : Blo 279826 422765 := bbase (se 3 (by rfl) ⟨79268, by rfl⟩ : syracuseStep 422765 = 158537) (by norm_num)
theorem B455557 : Blo 279826 455557 := bbase (se 4 (by rfl) ⟨42708, by rfl⟩ : syracuseStep 455557 = 85417) (by norm_num)
theorem B422789 : Blo 279826 422789 := bbase (se 4 (by rfl) ⟨39636, by rfl⟩ : syracuseStep 422789 = 79273) (by norm_num)
theorem B422813 : Blo 279826 422813 := bbase (se 3 (by rfl) ⟨79277, by rfl⟩ : syracuseStep 422813 = 158555) (by norm_num)
theorem B422837 : Blo 279826 422837 := bbase (se 5 (by rfl) ⟨19820, by rfl⟩ : syracuseStep 422837 = 39641) (by norm_num)
theorem B357301 : Blo 279826 357301 := bbase (se 5 (by rfl) ⟨16748, by rfl⟩ : syracuseStep 357301 = 33497) (by norm_num)
theorem B422861 : Blo 279826 422861 := bbase (se 3 (by rfl) ⟨79286, by rfl⟩ : syracuseStep 422861 = 158573) (by norm_num)
theorem B717781 : Blo 279826 717781 := bbase (se 7 (by rfl) ⟨8411, by rfl⟩ : syracuseStep 717781 = 16823) (by norm_num)
theorem B422885 : Blo 279826 422885 := bbase (se 4 (by rfl) ⟨39645, by rfl⟩ : syracuseStep 422885 = 79291) (by norm_num)
theorem B422909 : Blo 279826 422909 := bbase (se 3 (by rfl) ⟨79295, by rfl⟩ : syracuseStep 422909 = 158591) (by norm_num)
theorem B422933 : Blo 279826 422933 := bbase (se 6 (by rfl) ⟨9912, by rfl⟩ : syracuseStep 422933 = 19825) (by norm_num)
theorem B1143845 : Blo 279826 1143845 := bbase (se 4 (by rfl) ⟨107235, by rfl⟩ : syracuseStep 1143845 = 214471) (by norm_num)
theorem B422957 : Blo 279826 422957 := bbase (se 3 (by rfl) ⟨79304, by rfl⟩ : syracuseStep 422957 = 158609) (by norm_num)
theorem B422981 : Blo 279826 422981 := bbase (se 4 (by rfl) ⟨39654, by rfl⟩ : syracuseStep 422981 = 79309) (by norm_num)
theorem B717893 : Blo 279826 717893 := bbase (se 4 (by rfl) ⟨67302, by rfl⟩ : syracuseStep 717893 = 134605) (by norm_num)
theorem B423005 : Blo 279826 423005 := bbase (se 3 (by rfl) ⟨79313, by rfl⟩ : syracuseStep 423005 = 158627) (by norm_num)
theorem B357473 : Blo 279826 357473 := bbase (se 2 (by rfl) ⟨134052, by rfl⟩ : syracuseStep 357473 = 268105) (by norm_num)
theorem B423029 : Blo 279826 423029 := bbase (se 5 (by rfl) ⟨19829, by rfl⟩ : syracuseStep 423029 = 39659) (by norm_num)
theorem B423053 : Blo 279826 423053 := bbase (se 3 (by rfl) ⟨79322, by rfl⟩ : syracuseStep 423053 = 158645) (by norm_num)
theorem B357529 : Blo 279826 357529 := bbase (se 2 (by rfl) ⟨134073, by rfl⟩ : syracuseStep 357529 = 268147) (by norm_num)
theorem B423077 : Blo 279826 423077 := bbase (se 4 (by rfl) ⟨39663, by rfl⟩ : syracuseStep 423077 = 79327) (by norm_num)
theorem B423101 : Blo 279826 423101 := bbase (se 3 (by rfl) ⟨79331, by rfl⟩ : syracuseStep 423101 = 158663) (by norm_num)
theorem B423125 : Blo 279826 423125 := bbase (se 7 (by rfl) ⟨4958, by rfl⟩ : syracuseStep 423125 = 9917) (by norm_num)
theorem B947429 : Blo 279826 947429 := bbase (se 4 (by rfl) ⟨88821, by rfl⟩ : syracuseStep 947429 = 177643) (by norm_num)
theorem B423149 : Blo 279826 423149 := bbase (se 3 (by rfl) ⟨79340, by rfl⟩ : syracuseStep 423149 = 158681) (by norm_num)
theorem B1373429 : Blo 279826 1373429 := bbase (se 5 (by rfl) ⟨64379, by rfl⟩ : syracuseStep 1373429 = 128759) (by norm_num)
theorem B357625 : Blo 279826 357625 := bbase (se 2 (by rfl) ⟨134109, by rfl⟩ : syracuseStep 357625 = 268219) (by norm_num)
theorem B423173 : Blo 279826 423173 := bbase (se 4 (by rfl) ⟨39672, by rfl⟩ : syracuseStep 423173 = 79345) (by norm_num)
theorem B718085 : Blo 279826 718085 := bbase (se 4 (by rfl) ⟨67320, by rfl⟩ : syracuseStep 718085 = 134641) (by norm_num)
theorem B423197 : Blo 279826 423197 := bbase (se 3 (by rfl) ⟨79349, by rfl⟩ : syracuseStep 423197 = 158699) (by norm_num)
theorem B423221 : Blo 279826 423221 := bbase (se 5 (by rfl) ⟨19838, by rfl⟩ : syracuseStep 423221 = 39677) (by norm_num)
theorem B423245 : Blo 279826 423245 := bbase (se 3 (by rfl) ⟨79358, by rfl⟩ : syracuseStep 423245 = 158717) (by norm_num)
theorem B423269 : Blo 279826 423269 := bbase (se 4 (by rfl) ⟨39681, by rfl⟩ : syracuseStep 423269 = 79363) (by norm_num)
theorem B2127221 : Blo 279826 2127221 := bbase (se 5 (by rfl) ⟨99713, by rfl⟩ : syracuseStep 2127221 = 199427) (by norm_num)
theorem B423293 : Blo 279826 423293 := bbase (se 3 (by rfl) ⟨79367, by rfl⟩ : syracuseStep 423293 = 158735) (by norm_num)
theorem B423317 : Blo 279826 423317 := bbase (se 6 (by rfl) ⟨9921, by rfl⟩ : syracuseStep 423317 = 19843) (by norm_num)
theorem B357797 : Blo 279826 357797 := bbase (se 4 (by rfl) ⟨33543, by rfl⟩ : syracuseStep 357797 = 67087) (by norm_num)
theorem B423341 : Blo 279826 423341 := bbase (se 3 (by rfl) ⟨79376, by rfl⟩ : syracuseStep 423341 = 158753) (by norm_num)
theorem B423365 : Blo 279826 423365 := bbase (se 4 (by rfl) ⟨39690, by rfl⟩ : syracuseStep 423365 = 79381) (by norm_num)
theorem B423389 : Blo 279826 423389 := bbase (se 3 (by rfl) ⟨79385, by rfl⟩ : syracuseStep 423389 = 158771) (by norm_num)
theorem B357853 : Blo 279826 357853 := bbase (se 3 (by rfl) ⟨67097, by rfl⟩ : syracuseStep 357853 = 134195) (by norm_num)
theorem B423413 : Blo 279826 423413 := bbase (se 5 (by rfl) ⟨19847, by rfl⟩ : syracuseStep 423413 = 39695) (by norm_num)
theorem B423437 : Blo 279826 423437 := bbase (se 3 (by rfl) ⟨79394, by rfl⟩ : syracuseStep 423437 = 158789) (by norm_num)
theorem B423461 : Blo 279826 423461 := bbase (se 4 (by rfl) ⟨39699, by rfl⟩ : syracuseStep 423461 = 79399) (by norm_num)
theorem B423485 : Blo 279826 423485 := bbase (se 3 (by rfl) ⟨79403, by rfl⟩ : syracuseStep 423485 = 158807) (by norm_num)
theorem B357949 : Blo 279826 357949 := bbase (se 3 (by rfl) ⟨67115, by rfl⟩ : syracuseStep 357949 = 134231) (by norm_num)
theorem B1799765 : Blo 279826 1799765 := bbase (se 8 (by rfl) ⟨10545, by rfl⟩ : syracuseStep 1799765 = 21091) (by norm_num)
theorem B423509 : Blo 279826 423509 := bbase (se 8 (by rfl) ⟨2481, by rfl⟩ : syracuseStep 423509 = 4963) (by norm_num)
theorem B718429 : Blo 279826 718429 := bbase (se 3 (by rfl) ⟨134705, by rfl⟩ : syracuseStep 718429 = 269411) (by norm_num)
theorem B423533 : Blo 279826 423533 := bbase (se 3 (by rfl) ⟨79412, by rfl⟩ : syracuseStep 423533 = 158825) (by norm_num)
theorem B423557 : Blo 279826 423557 := bbase (se 4 (by rfl) ⟨39708, by rfl⟩ : syracuseStep 423557 = 79417) (by norm_num)
theorem B947861 : Blo 279826 947861 := bbase (se 6 (by rfl) ⟨22215, by rfl⟩ : syracuseStep 947861 = 44431) (by norm_num)
theorem B2717333 : Blo 279826 2717333 := bbase (se 6 (by rfl) ⟨63687, by rfl⟩ : syracuseStep 2717333 = 127375) (by norm_num)
theorem B423581 : Blo 279826 423581 := bbase (se 3 (by rfl) ⟨79421, by rfl⟩ : syracuseStep 423581 = 158843) (by norm_num)
theorem B1603253 : Blo 279826 1603253 := bbase (se 5 (by rfl) ⟨75152, by rfl⟩ : syracuseStep 1603253 = 150305) (by norm_num)
theorem B423605 : Blo 279826 423605 := bbase (se 5 (by rfl) ⟨19856, by rfl⟩ : syracuseStep 423605 = 39713) (by norm_num)
theorem B423629 : Blo 279826 423629 := bbase (se 3 (by rfl) ⟨79430, by rfl⟩ : syracuseStep 423629 = 158861) (by norm_num)
theorem B423653 : Blo 279826 423653 := bbase (se 4 (by rfl) ⟨39717, by rfl⟩ : syracuseStep 423653 = 79435) (by norm_num)
theorem B358121 : Blo 279826 358121 := bbase (se 2 (by rfl) ⟨134295, by rfl⟩ : syracuseStep 358121 = 268591) (by norm_num)
theorem B423677 : Blo 279826 423677 := bbase (se 3 (by rfl) ⟨79439, by rfl⟩ : syracuseStep 423677 = 158879) (by norm_num)
theorem B423701 : Blo 279826 423701 := bbase (se 6 (by rfl) ⟨9930, by rfl⟩ : syracuseStep 423701 = 19861) (by norm_num)
theorem B358177 : Blo 279826 358177 := bbase (se 2 (by rfl) ⟨134316, by rfl⟩ : syracuseStep 358177 = 268633) (by norm_num)
theorem B423725 : Blo 279826 423725 := bbase (se 3 (by rfl) ⟨79448, by rfl⟩ : syracuseStep 423725 = 158897) (by norm_num)
theorem B423749 : Blo 279826 423749 := bbase (se 4 (by rfl) ⟨39726, by rfl⟩ : syracuseStep 423749 = 79453) (by norm_num)
theorem B423773 : Blo 279826 423773 := bbase (se 3 (by rfl) ⟨79457, by rfl⟩ : syracuseStep 423773 = 158915) (by norm_num)
theorem B423797 : Blo 279826 423797 := bbase (se 5 (by rfl) ⟨19865, by rfl⟩ : syracuseStep 423797 = 39731) (by norm_num)
theorem B358273 : Blo 279826 358273 := bbase (se 2 (by rfl) ⟨134352, by rfl⟩ : syracuseStep 358273 = 268705) (by norm_num)
theorem B423821 : Blo 279826 423821 := bbase (se 3 (by rfl) ⟨79466, by rfl⟩ : syracuseStep 423821 = 158933) (by norm_num)
theorem B423845 : Blo 279826 423845 := bbase (se 4 (by rfl) ⟨39735, by rfl⟩ : syracuseStep 423845 = 79471) (by norm_num)
theorem B423869 : Blo 279826 423869 := bbase (se 3 (by rfl) ⟨79475, by rfl⟩ : syracuseStep 423869 = 158951) (by norm_num)
theorem B423893 : Blo 279826 423893 := bbase (se 7 (by rfl) ⟨4967, by rfl⟩ : syracuseStep 423893 = 9935) (by norm_num)
theorem B423917 : Blo 279826 423917 := bbase (se 3 (by rfl) ⟨79484, by rfl⟩ : syracuseStep 423917 = 158969) (by norm_num)
theorem B423941 : Blo 279826 423941 := bbase (se 4 (by rfl) ⟨39744, by rfl⟩ : syracuseStep 423941 = 79489) (by norm_num)
theorem B423965 : Blo 279826 423965 := bbase (se 3 (by rfl) ⟨79493, by rfl⟩ : syracuseStep 423965 = 158987) (by norm_num)
theorem B358445 : Blo 279826 358445 := bbase (se 3 (by rfl) ⟨67208, by rfl⟩ : syracuseStep 358445 = 134417) (by norm_num)
theorem B423989 : Blo 279826 423989 := bbase (se 5 (by rfl) ⟨19874, by rfl⟩ : syracuseStep 423989 = 39749) (by norm_num)
theorem B948293 : Blo 279826 948293 := bbase (se 4 (by rfl) ⟨88902, by rfl⟩ : syracuseStep 948293 = 177805) (by norm_num)
theorem B424013 : Blo 279826 424013 := bbase (se 3 (by rfl) ⟨79502, by rfl⟩ : syracuseStep 424013 = 159005) (by norm_num)
theorem B424037 : Blo 279826 424037 := bbase (se 4 (by rfl) ⟨39753, by rfl⟩ : syracuseStep 424037 = 79507) (by norm_num)
theorem B358501 : Blo 279826 358501 := bbase (se 4 (by rfl) ⟨33609, by rfl⟩ : syracuseStep 358501 = 67219) (by norm_num)
theorem B424061 : Blo 279826 424061 := bbase (se 3 (by rfl) ⟨79511, by rfl⟩ : syracuseStep 424061 = 159023) (by norm_num)
theorem B424085 : Blo 279826 424085 := bbase (se 6 (by rfl) ⟨9939, by rfl⟩ : syracuseStep 424085 = 19879) (by norm_num)
theorem B424109 : Blo 279826 424109 := bbase (se 3 (by rfl) ⟨79520, by rfl⟩ : syracuseStep 424109 = 159041) (by norm_num)
theorem B424133 : Blo 279826 424133 := bbase (se 4 (by rfl) ⟨39762, by rfl⟩ : syracuseStep 424133 = 79525) (by norm_num)
theorem B358597 : Blo 279826 358597 := bbase (se 4 (by rfl) ⟨33618, by rfl⟩ : syracuseStep 358597 = 67237) (by norm_num)
theorem B424157 : Blo 279826 424157 := bbase (se 3 (by rfl) ⟨79529, by rfl⟩ : syracuseStep 424157 = 159059) (by norm_num)
theorem B424181 : Blo 279826 424181 := bbase (se 5 (by rfl) ⟨19883, by rfl⟩ : syracuseStep 424181 = 39767) (by norm_num)
theorem B424205 : Blo 279826 424205 := bbase (se 3 (by rfl) ⟨79538, by rfl⟩ : syracuseStep 424205 = 159077) (by norm_num)
theorem B424229 : Blo 279826 424229 := bbase (se 4 (by rfl) ⟨39771, by rfl⟩ : syracuseStep 424229 = 79543) (by norm_num)
theorem B424253 : Blo 279826 424253 := bbase (se 3 (by rfl) ⟨79547, by rfl⟩ : syracuseStep 424253 = 159095) (by norm_num)
theorem B424277 : Blo 279826 424277 := bbase (se 10 (by rfl) ⟨621, by rfl⟩ : syracuseStep 424277 = 1243) (by norm_num)
theorem B424301 : Blo 279826 424301 := bbase (se 3 (by rfl) ⟨79556, by rfl⟩ : syracuseStep 424301 = 159113) (by norm_num)
theorem B358769 : Blo 279826 358769 := bbase (se 2 (by rfl) ⟨134538, by rfl⟩ : syracuseStep 358769 = 269077) (by norm_num)
theorem B424325 : Blo 279826 424325 := bbase (se 4 (by rfl) ⟨39780, by rfl⟩ : syracuseStep 424325 = 79561) (by norm_num)
theorem B424349 : Blo 279826 424349 := bbase (se 3 (by rfl) ⟨79565, by rfl⟩ : syracuseStep 424349 = 159131) (by norm_num)
theorem B358825 : Blo 279826 358825 := bbase (se 2 (by rfl) ⟨134559, by rfl⟩ : syracuseStep 358825 = 269119) (by norm_num)
theorem B424373 : Blo 279826 424373 := bbase (se 5 (by rfl) ⟨19892, by rfl⟩ : syracuseStep 424373 = 39785) (by norm_num)
theorem B424397 : Blo 279826 424397 := bbase (se 3 (by rfl) ⟨79574, by rfl⟩ : syracuseStep 424397 = 159149) (by norm_num)
theorem B1014245 : Blo 279826 1014245 := bbase (se 4 (by rfl) ⟨95085, by rfl⟩ : syracuseStep 1014245 = 190171) (by norm_num)
theorem B424421 : Blo 279826 424421 := bbase (se 4 (by rfl) ⟨39789, by rfl⟩ : syracuseStep 424421 = 79579) (by norm_num)
theorem B948725 : Blo 279826 948725 := bbase (se 5 (by rfl) ⟨44471, by rfl⟩ : syracuseStep 948725 = 88943) (by norm_num)
theorem B424445 : Blo 279826 424445 := bbase (se 3 (by rfl) ⟨79583, by rfl⟩ : syracuseStep 424445 = 159167) (by norm_num)
theorem B358921 : Blo 279826 358921 := bbase (se 2 (by rfl) ⟨134595, by rfl⟩ : syracuseStep 358921 = 269191) (by norm_num)
theorem B424469 : Blo 279826 424469 := bbase (se 6 (by rfl) ⟨9948, by rfl⟩ : syracuseStep 424469 = 19897) (by norm_num)
theorem B424493 : Blo 279826 424493 := bbase (se 3 (by rfl) ⟨79592, by rfl⟩ : syracuseStep 424493 = 159185) (by norm_num)
theorem B424517 : Blo 279826 424517 := bbase (se 4 (by rfl) ⟨39798, by rfl⟩ : syracuseStep 424517 = 79597) (by norm_num)
theorem B424541 : Blo 279826 424541 := bbase (se 3 (by rfl) ⟨79601, by rfl⟩ : syracuseStep 424541 = 159203) (by norm_num)
theorem B1014389 : Blo 279826 1014389 := bbase (se 5 (by rfl) ⟨47549, by rfl⟩ : syracuseStep 1014389 = 95099) (by norm_num)
theorem B424565 : Blo 279826 424565 := bbase (se 5 (by rfl) ⟨19901, by rfl⟩ : syracuseStep 424565 = 39803) (by norm_num)
theorem B424589 : Blo 279826 424589 := bbase (se 3 (by rfl) ⟨79610, by rfl⟩ : syracuseStep 424589 = 159221) (by norm_num)
theorem B424613 : Blo 279826 424613 := bbase (se 4 (by rfl) ⟨39807, by rfl⟩ : syracuseStep 424613 = 79615) (by norm_num)
theorem B359093 : Blo 279826 359093 := bbase (se 5 (by rfl) ⟨16832, by rfl⟩ : syracuseStep 359093 = 33665) (by norm_num)
theorem B424637 : Blo 279826 424637 := bbase (se 3 (by rfl) ⟨79619, by rfl⟩ : syracuseStep 424637 = 159239) (by norm_num)
theorem B424661 : Blo 279826 424661 := bbase (se 7 (by rfl) ⟨4976, by rfl⟩ : syracuseStep 424661 = 9953) (by norm_num)
theorem B424685 : Blo 279826 424685 := bbase (se 3 (by rfl) ⟨79628, by rfl⟩ : syracuseStep 424685 = 159257) (by norm_num)
theorem B359149 : Blo 279826 359149 := bbase (se 3 (by rfl) ⟨67340, by rfl⟩ : syracuseStep 359149 = 134681) (by norm_num)
theorem B424709 : Blo 279826 424709 := bbase (se 4 (by rfl) ⟨39816, by rfl⟩ : syracuseStep 424709 = 79633) (by norm_num)
theorem B424733 : Blo 279826 424733 := bbase (se 3 (by rfl) ⟨79637, by rfl⟩ : syracuseStep 424733 = 159275) (by norm_num)
theorem B424757 : Blo 279826 424757 := bbase (se 5 (by rfl) ⟨19910, by rfl⟩ : syracuseStep 424757 = 39821) (by norm_num)
theorem B424781 : Blo 279826 424781 := bbase (se 3 (by rfl) ⟨79646, by rfl⟩ : syracuseStep 424781 = 159293) (by norm_num)
theorem B424805 : Blo 279826 424805 := bbase (se 4 (by rfl) ⟨39825, by rfl⟩ : syracuseStep 424805 = 79651) (by norm_num)
theorem B359273 : Blo 279826 359273 := bbase (se 2 (by rfl) ⟨134727, by rfl⟩ : syracuseStep 359273 = 269455) (by norm_num)
theorem B424829 : Blo 279826 424829 := bbase (se 3 (by rfl) ⟨79655, by rfl⟩ : syracuseStep 424829 = 159311) (by norm_num)
theorem B1440661 : Blo 279826 1440661 := bbase (se 6 (by rfl) ⟨33765, by rfl⟩ : syracuseStep 1440661 = 67531) (by norm_num)
theorem B424853 : Blo 279826 424853 := bbase (se 6 (by rfl) ⟨9957, by rfl⟩ : syracuseStep 424853 = 19915) (by norm_num)
theorem B949157 : Blo 279826 949157 := bbase (se 4 (by rfl) ⟨88983, by rfl⟩ : syracuseStep 949157 = 177967) (by norm_num)
theorem B424877 : Blo 279826 424877 := bbase (se 3 (by rfl) ⟨79664, by rfl⟩ : syracuseStep 424877 = 159329) (by norm_num)
theorem B424901 : Blo 279826 424901 := bbase (se 4 (by rfl) ⟨39834, by rfl⟩ : syracuseStep 424901 = 79669) (by norm_num)
theorem B424925 : Blo 279826 424925 := bbase (se 3 (by rfl) ⟨79673, by rfl⟩ : syracuseStep 424925 = 159347) (by norm_num)
theorem B1276901 : Blo 279826 1276901 := bbase (se 4 (by rfl) ⟨119709, by rfl⟩ : syracuseStep 1276901 = 239419) (by norm_num)
theorem B424949 : Blo 279826 424949 := bbase (se 5 (by rfl) ⟨19919, by rfl⟩ : syracuseStep 424949 = 39839) (by norm_num)
theorem B424973 : Blo 279826 424973 := bbase (se 3 (by rfl) ⟨79682, by rfl⟩ : syracuseStep 424973 = 159365) (by norm_num)
theorem B424997 : Blo 279826 424997 := bbase (se 4 (by rfl) ⟨39843, by rfl⟩ : syracuseStep 424997 = 79687) (by norm_num)
theorem B425021 : Blo 279826 425021 := bbase (se 3 (by rfl) ⟨79691, by rfl⟩ : syracuseStep 425021 = 159383) (by norm_num)
theorem B425045 : Blo 279826 425045 := bbase (se 8 (by rfl) ⟨2490, by rfl⟩ : syracuseStep 425045 = 4981) (by norm_num)
theorem B425069 : Blo 279826 425069 := bbase (se 3 (by rfl) ⟨79700, by rfl⟩ : syracuseStep 425069 = 159401) (by norm_num)
theorem B425093 : Blo 279826 425093 := bbase (se 4 (by rfl) ⟨39852, by rfl⟩ : syracuseStep 425093 = 79705) (by norm_num)
theorem B425117 : Blo 279826 425117 := bbase (se 3 (by rfl) ⟨79709, by rfl⟩ : syracuseStep 425117 = 159419) (by norm_num)
theorem B425141 : Blo 279826 425141 := bbase (se 5 (by rfl) ⟨19928, by rfl⟩ : syracuseStep 425141 = 39857) (by norm_num)
theorem B425165 : Blo 279826 425165 := bbase (se 3 (by rfl) ⟨79718, by rfl⟩ : syracuseStep 425165 = 159437) (by norm_num)
theorem B425189 : Blo 279826 425189 := bbase (se 4 (by rfl) ⟨39861, by rfl⟩ : syracuseStep 425189 = 79723) (by norm_num)
theorem B425213 : Blo 279826 425213 := bbase (se 3 (by rfl) ⟨79727, by rfl⟩ : syracuseStep 425213 = 159455) (by norm_num)
theorem B425237 : Blo 279826 425237 := bbase (se 6 (by rfl) ⟨9966, by rfl⟩ : syracuseStep 425237 = 19933) (by norm_num)
theorem B752933 : Blo 279826 752933 := bbase (se 4 (by rfl) ⟨70587, by rfl⟩ : syracuseStep 752933 = 141175) (by norm_num)
theorem B425261 : Blo 279826 425261 := bbase (se 3 (by rfl) ⟨79736, by rfl⟩ : syracuseStep 425261 = 159473) (by norm_num)
theorem B359741 : Blo 279826 359741 := bbase (se 3 (by rfl) ⟨67451, by rfl⟩ : syracuseStep 359741 = 134903) (by norm_num)
theorem B425285 : Blo 279826 425285 := bbase (se 4 (by rfl) ⟨39870, by rfl⟩ : syracuseStep 425285 = 79741) (by norm_num)
theorem B949589 : Blo 279826 949589 := bbase (se 11 (by rfl) ⟨695, by rfl⟩ : syracuseStep 949589 = 1391) (by norm_num)
theorem B425309 : Blo 279826 425309 := bbase (se 3 (by rfl) ⟨79745, by rfl⟩ : syracuseStep 425309 = 159491) (by norm_num)
theorem B425333 : Blo 279826 425333 := bbase (se 5 (by rfl) ⟨19937, by rfl⟩ : syracuseStep 425333 = 39875) (by norm_num)
theorem B425357 : Blo 279826 425357 := bbase (se 3 (by rfl) ⟨79754, by rfl⟩ : syracuseStep 425357 = 159509) (by norm_num)
theorem B425381 : Blo 279826 425381 := bbase (se 4 (by rfl) ⟨39879, by rfl⟩ : syracuseStep 425381 = 79759) (by norm_num)
theorem B425405 : Blo 279826 425405 := bbase (se 3 (by rfl) ⟨79763, by rfl⟩ : syracuseStep 425405 = 159527) (by norm_num)
theorem B425429 : Blo 279826 425429 := bbase (se 7 (by rfl) ⟨4985, by rfl⟩ : syracuseStep 425429 = 9971) (by norm_num)
theorem B425453 : Blo 279826 425453 := bbase (se 3 (by rfl) ⟨79772, by rfl⟩ : syracuseStep 425453 = 159545) (by norm_num)
theorem B425477 : Blo 279826 425477 := bbase (se 4 (by rfl) ⟨39888, by rfl⟩ : syracuseStep 425477 = 79777) (by norm_num)
theorem B425501 : Blo 279826 425501 := bbase (se 3 (by rfl) ⟨79781, by rfl⟩ : syracuseStep 425501 = 159563) (by norm_num)
theorem B425525 : Blo 279826 425525 := bbase (se 5 (by rfl) ⟨19946, by rfl⟩ : syracuseStep 425525 = 39893) (by norm_num)
theorem B425549 : Blo 279826 425549 := bbase (se 3 (by rfl) ⟨79790, by rfl⟩ : syracuseStep 425549 = 159581) (by norm_num)
theorem B425573 : Blo 279826 425573 := bbase (se 4 (by rfl) ⟨39897, by rfl⟩ : syracuseStep 425573 = 79795) (by norm_num)
theorem B425597 : Blo 279826 425597 := bbase (se 3 (by rfl) ⟨79799, by rfl⟩ : syracuseStep 425597 = 159599) (by norm_num)
theorem B425621 : Blo 279826 425621 := bbase (se 6 (by rfl) ⟨9975, by rfl⟩ : syracuseStep 425621 = 19951) (by norm_num)
theorem B425645 : Blo 279826 425645 := bbase (se 3 (by rfl) ⟨79808, by rfl⟩ : syracuseStep 425645 = 159617) (by norm_num)
theorem B1703605 : Blo 279826 1703605 := bbase (se 5 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 1703605 = 159713) (by norm_num)
theorem B425669 : Blo 279826 425669 := bbase (se 4 (by rfl) ⟨39906, by rfl⟩ : syracuseStep 425669 = 79813) (by norm_num)
theorem B425693 : Blo 279826 425693 := bbase (se 3 (by rfl) ⟨79817, by rfl⟩ : syracuseStep 425693 = 159635) (by norm_num)
theorem B1310453 : Blo 279826 1310453 := bbase (se 5 (by rfl) ⟨61427, by rfl⟩ : syracuseStep 1310453 = 122855) (by norm_num)
theorem B425717 : Blo 279826 425717 := bbase (se 5 (by rfl) ⟨19955, by rfl⟩ : syracuseStep 425717 = 39911) (by norm_num)
theorem B950021 : Blo 279826 950021 := bbase (se 4 (by rfl) ⟨89064, by rfl⟩ : syracuseStep 950021 = 178129) (by norm_num)
theorem B425987 : Blo 279826 425987 := bstep (se 1 (by rfl) ⟨319490, by rfl⟩ : syracuseStep 425987 = 638981) B638981
theorem B426145 : Blo 279826 426145 := bstep (se 2 (by rfl) ⟨159804, by rfl⟩ : syracuseStep 426145 = 319609) B319609
theorem B950669 : Blo 279826 950669 := bstep (se 3 (by rfl) ⟨178250, by rfl⟩ : syracuseStep 950669 = 356501) B356501
theorem B950723 : Blo 279826 950723 := bstep (se 1 (by rfl) ⟨713042, by rfl⟩ : syracuseStep 950723 = 1426085) B1426085
theorem B360931 : Blo 279826 360931 := bstep (se 1 (by rfl) ⟨270698, by rfl⟩ : syracuseStep 360931 = 541397) B541397
theorem B3211973 : Blo 279826 3211973 := bstep (se 4 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 3211973 = 602245) B602245
theorem B950993 : Blo 279826 950993 := bstep (se 2 (by rfl) ⟨356622, by rfl⟩ : syracuseStep 950993 = 713245) B713245
theorem B1868579 : Blo 279826 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B426961 : Blo 279826 426961 := bstep (se 2 (by rfl) ⟨160110, by rfl⟩ : syracuseStep 426961 = 320221) B320221
theorem B361427 : Blo 279826 361427 := bstep (se 1 (by rfl) ⟨271070, by rfl⟩ : syracuseStep 361427 = 542141) B542141
theorem B1016867 : Blo 279826 1016867 := bstep (se 1 (by rfl) ⟨762650, by rfl⟩ : syracuseStep 1016867 = 1525301) B1525301
theorem B951533 : Blo 279826 951533 := bstep (se 3 (by rfl) ⟨178412, by rfl⟩ : syracuseStep 951533 = 356825) B356825
theorem B951587 : Blo 279826 951587 := bstep (se 1 (by rfl) ⟨713690, by rfl⟩ : syracuseStep 951587 = 1427381) B1427381
theorem B329027 : Blo 279826 329027 := bstep (se 1 (by rfl) ⟨246770, by rfl⟩ : syracuseStep 329027 = 493541) B493541
theorem B427361 : Blo 279826 427361 := bstep (se 2 (by rfl) ⟨160260, by rfl⟩ : syracuseStep 427361 = 320521) B320521
theorem B951857 : Blo 279826 951857 := bstep (se 2 (by rfl) ⟨356946, by rfl⟩ : syracuseStep 951857 = 713893) B713893
theorem B1017443 : Blo 279826 1017443 := bstep (se 1 (by rfl) ⟨763082, by rfl⟩ : syracuseStep 1017443 = 1526165) B1526165
theorem B1607309 : Blo 279826 1607309 := bstep (se 3 (by rfl) ⟨301370, by rfl⟩ : syracuseStep 1607309 = 602741) B602741
theorem B3835633 : Blo 279826 3835633 := bstep (se 2 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 3835633 = 2876725) B2876725
theorem B952397 : Blo 279826 952397 := bstep (se 3 (by rfl) ⟨178574, by rfl⟩ : syracuseStep 952397 = 357149) B357149
theorem B2132081 : Blo 279826 2132081 := bstep (se 2 (by rfl) ⟨799530, by rfl⟩ : syracuseStep 2132081 = 1599061) B1599061
theorem B952451 : Blo 279826 952451 := bstep (se 1 (by rfl) ⟨714338, by rfl⟩ : syracuseStep 952451 = 1428677) B1428677
theorem B952721 : Blo 279826 952721 := bstep (se 2 (by rfl) ⟨357270, by rfl⟩ : syracuseStep 952721 = 714541) B714541
theorem B428627 : Blo 279826 428627 := bstep (se 1 (by rfl) ⟨321470, by rfl⟩ : syracuseStep 428627 = 642941) B642941
theorem B953261 : Blo 279826 953261 := bstep (se 3 (by rfl) ⟨178736, by rfl⟩ : syracuseStep 953261 = 357473) B357473
theorem B2034629 : Blo 279826 2034629 := bstep (se 4 (by rfl) ⟨190746, by rfl⟩ : syracuseStep 2034629 = 381493) B381493
theorem B953315 : Blo 279826 953315 := bstep (se 1 (by rfl) ⟨714986, by rfl⟩ : syracuseStep 953315 = 1429973) B1429973
theorem B2755781 : Blo 279826 2755781 := bstep (se 4 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 2755781 = 516709) B516709
theorem B953585 : Blo 279826 953585 := bstep (se 2 (by rfl) ⟨357594, by rfl⟩ : syracuseStep 953585 = 715189) B715189
theorem B429331 : Blo 279826 429331 := bstep (se 1 (by rfl) ⟨321998, by rfl⟩ : syracuseStep 429331 = 643997) B643997
theorem B757027 : Blo 279826 757027 := bstep (se 1 (by rfl) ⟨567770, by rfl⟩ : syracuseStep 757027 = 1135541) B1135541
theorem B1019405 : Blo 279826 1019405 := bstep (se 3 (by rfl) ⟨191138, by rfl⟩ : syracuseStep 1019405 = 382277) B382277
theorem B954125 : Blo 279826 954125 := bstep (se 3 (by rfl) ⟨178898, by rfl⟩ : syracuseStep 954125 = 357797) B357797
theorem B954179 : Blo 279826 954179 := bstep (se 1 (by rfl) ⟨715634, by rfl⟩ : syracuseStep 954179 = 1431269) B1431269
theorem B1609541 : Blo 279826 1609541 := bstep (se 4 (by rfl) ⟨150894, by rfl⟩ : syracuseStep 1609541 = 301789) B301789
theorem B954449 : Blo 279826 954449 := bstep (se 2 (by rfl) ⟨357918, by rfl⟩ : syracuseStep 954449 = 715837) B715837
theorem B299171 : Blo 279826 299171 := bstep (se 1 (by rfl) ⟨224378, by rfl⟩ : syracuseStep 299171 = 448757) B448757
theorem B430451 : Blo 279826 430451 := bstep (se 1 (by rfl) ⟨322838, by rfl⟩ : syracuseStep 430451 = 645677) B645677
theorem B430499 : Blo 279826 430499 := bstep (se 1 (by rfl) ⟨322874, by rfl⟩ : syracuseStep 430499 = 645749) B645749
theorem B1610225 : Blo 279826 1610225 := bstep (se 2 (by rfl) ⟨603834, by rfl⟩ : syracuseStep 1610225 = 1207669) B1207669
theorem B954989 : Blo 279826 954989 := bstep (se 3 (by rfl) ⟨179060, by rfl⟩ : syracuseStep 954989 = 358121) B358121
theorem B955043 : Blo 279826 955043 := bstep (se 1 (by rfl) ⟨716282, by rfl⟩ : syracuseStep 955043 = 1432565) B1432565
theorem B758609 : Blo 279826 758609 := bstep (se 2 (by rfl) ⟨284478, by rfl⟩ : syracuseStep 758609 = 568957) B568957
theorem B955313 : Blo 279826 955313 := bstep (se 2 (by rfl) ⟨358242, by rfl⟩ : syracuseStep 955313 = 716485) B716485
theorem B300115 : Blo 279826 300115 := bstep (se 1 (by rfl) ⟨225086, by rfl⟩ : syracuseStep 300115 = 450173) B450173
theorem B398467 : Blo 279826 398467 := bstep (se 1 (by rfl) ⟨298850, by rfl⟩ : syracuseStep 398467 = 597701) B597701
theorem B1021133 : Blo 279826 1021133 := bstep (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) B382925
theorem B955853 : Blo 279826 955853 := bstep (se 3 (by rfl) ⟨179222, by rfl⟩ : syracuseStep 955853 = 358445) B358445
theorem B759299 : Blo 279826 759299 := bstep (se 1 (by rfl) ⟨569474, by rfl⟩ : syracuseStep 759299 = 1138949) B1138949
theorem B955907 : Blo 279826 955907 := bstep (se 1 (by rfl) ⟨716930, by rfl⟩ : syracuseStep 955907 = 1433861) B1433861
theorem B956177 : Blo 279826 956177 := bstep (se 2 (by rfl) ⟨358566, by rfl⟩ : syracuseStep 956177 = 717133) B717133
theorem B1611683 : Blo 279826 1611683 := bstep (se 1 (by rfl) ⟨1208762, by rfl⟩ : syracuseStep 1611683 = 2417525) B2417525
theorem B2693189 : Blo 279826 2693189 := bstep (se 4 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 2693189 = 504973) B504973
theorem B25860181 : Blo 279826 25860181 := bstep (se 8 (by rfl) ⟨151524, by rfl⟩ : syracuseStep 25860181 = 303049) B303049
theorem B13080689 : Blo 279826 13080689 := bstep (se 2 (by rfl) ⟨4905258, by rfl⟩ : syracuseStep 13080689 = 9810517) B9810517
theorem B1808581 : Blo 279826 1808581 := bstep (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) B339109
theorem B792845 : Blo 279826 792845 := bstep (se 3 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 792845 = 297317) B297317
theorem B760099 : Blo 279826 760099 := bstep (se 1 (by rfl) ⟨570074, by rfl⟩ : syracuseStep 760099 = 1140149) B1140149
theorem B956717 : Blo 279826 956717 := bstep (se 3 (by rfl) ⟨179384, by rfl⟩ : syracuseStep 956717 = 358769) B358769
theorem B301379 : Blo 279826 301379 := bstep (se 1 (by rfl) ⟨226034, by rfl⟩ : syracuseStep 301379 = 452069) B452069
theorem B760141 : Blo 279826 760141 := bstep (se 3 (by rfl) ⟨142526, by rfl⟩ : syracuseStep 760141 = 285053) B285053
theorem B956771 : Blo 279826 956771 := bstep (se 1 (by rfl) ⟨717578, by rfl⟩ : syracuseStep 956771 = 1435157) B1435157
theorem B3217805 : Blo 279826 3217805 := bstep (se 3 (by rfl) ⟨603338, by rfl⟩ : syracuseStep 3217805 = 1206677) B1206677
theorem B399811 : Blo 279826 399811 := bstep (se 1 (by rfl) ⟨299858, by rfl⟩ : syracuseStep 399811 = 599717) B599717
theorem B957041 : Blo 279826 957041 := bstep (se 2 (by rfl) ⟨358890, by rfl⟩ : syracuseStep 957041 = 717781) B717781
theorem B465569 : Blo 279826 465569 := bstep (se 2 (by rfl) ⟨174588, by rfl⟩ : syracuseStep 465569 = 349177) B349177
theorem B2235235 : Blo 279826 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B1514501 : Blo 279826 1514501 := bstep (se 4 (by rfl) ⟨141984, by rfl⟩ : syracuseStep 1514501 = 283969) B283969
theorem B302131 : Blo 279826 302131 := bstep (se 1 (by rfl) ⟨226598, by rfl⟩ : syracuseStep 302131 = 453197) B453197
theorem B629873 : Blo 279826 629873 := bstep (se 2 (by rfl) ⟨236202, by rfl⟩ : syracuseStep 629873 = 472405) B472405
theorem B629891 : Blo 279826 629891 := bstep (se 1 (by rfl) ⟨472418, by rfl⟩ : syracuseStep 629891 = 944837) B944837
theorem B957581 : Blo 279826 957581 := bstep (se 3 (by rfl) ⟨179546, by rfl⟩ : syracuseStep 957581 = 359093) B359093
theorem B957635 : Blo 279826 957635 := bstep (se 1 (by rfl) ⟨718226, by rfl⟩ : syracuseStep 957635 = 1436453) B1436453
theorem B302387 : Blo 279826 302387 := bstep (se 1 (by rfl) ⟨226790, by rfl⟩ : syracuseStep 302387 = 453581) B453581
theorem B630161 : Blo 279826 630161 := bstep (se 2 (by rfl) ⟨236310, by rfl⟩ : syracuseStep 630161 = 472621) B472621
theorem B630179 : Blo 279826 630179 := bstep (se 1 (by rfl) ⟨472634, by rfl⟩ : syracuseStep 630179 = 945269) B945269
theorem B957905 : Blo 279826 957905 := bstep (se 2 (by rfl) ⟨359214, by rfl⟩ : syracuseStep 957905 = 718429) B718429
theorem B1416689 : Blo 279826 1416689 := bstep (se 2 (by rfl) ⟨531258, by rfl⟩ : syracuseStep 1416689 = 1062517) B1062517
theorem B532003 : Blo 279826 532003 := bstep (se 1 (by rfl) ⟨399002, by rfl⟩ : syracuseStep 532003 = 798005) B798005
theorem B400945 : Blo 279826 400945 := bstep (se 2 (by rfl) ⟨150354, by rfl⟩ : syracuseStep 400945 = 300709) B300709
theorem B1449571 : Blo 279826 1449571 := bstep (se 1 (by rfl) ⟨1087178, by rfl⟩ : syracuseStep 1449571 = 2174357) B2174357
theorem B958061 : Blo 279826 958061 := bstep (se 3 (by rfl) ⟨179636, by rfl⟩ : syracuseStep 958061 = 359273) B359273
theorem B401041 : Blo 279826 401041 := bstep (se 2 (by rfl) ⟨150390, by rfl⟩ : syracuseStep 401041 = 300781) B300781
theorem B630449 : Blo 279826 630449 := bstep (se 2 (by rfl) ⟨236418, by rfl⟩ : syracuseStep 630449 = 472837) B472837
theorem B630467 : Blo 279826 630467 := bstep (se 1 (by rfl) ⟨472850, by rfl⟩ : syracuseStep 630467 = 945701) B945701
theorem B532163 : Blo 279826 532163 := bstep (se 1 (by rfl) ⟨399122, by rfl⟩ : syracuseStep 532163 = 798245) B798245
theorem B761699 : Blo 279826 761699 := bstep (se 1 (by rfl) ⟨571274, by rfl⟩ : syracuseStep 761699 = 1142549) B1142549
theorem B3710861 : Blo 279826 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B630737 : Blo 279826 630737 := bstep (se 2 (by rfl) ⟨236526, by rfl⟩ : syracuseStep 630737 = 473053) B473053
theorem B630755 : Blo 279826 630755 := bstep (se 1 (by rfl) ⟨473066, by rfl⟩ : syracuseStep 630755 = 946133) B946133
theorem B401537 : Blo 279826 401537 := bstep (se 2 (by rfl) ⟨150576, by rfl⟩ : syracuseStep 401537 = 301153) B301153
theorem B631025 : Blo 279826 631025 := bstep (se 2 (by rfl) ⟨236634, by rfl⟩ : syracuseStep 631025 = 473269) B473269
theorem B631043 : Blo 279826 631043 := bstep (se 1 (by rfl) ⟨473282, by rfl⟩ : syracuseStep 631043 = 946565) B946565
theorem B631313 : Blo 279826 631313 := bstep (se 2 (by rfl) ⟨236742, by rfl⟩ : syracuseStep 631313 = 473485) B473485
theorem B631331 : Blo 279826 631331 := bstep (se 1 (by rfl) ⟨473498, by rfl⟩ : syracuseStep 631331 = 946997) B946997
theorem B762563 : Blo 279826 762563 := bstep (se 1 (by rfl) ⟨571922, by rfl⟩ : syracuseStep 762563 = 1143845) B1143845
theorem B533233 : Blo 279826 533233 := bstep (se 2 (by rfl) ⟨199962, by rfl⟩ : syracuseStep 533233 = 399925) B399925
theorem B762641 : Blo 279826 762641 := bstep (se 2 (by rfl) ⟨285990, by rfl⟩ : syracuseStep 762641 = 571981) B571981
theorem B631601 : Blo 279826 631601 := bstep (se 2 (by rfl) ⟨236850, by rfl⟩ : syracuseStep 631601 = 473701) B473701
theorem B631619 : Blo 279826 631619 := bstep (se 1 (by rfl) ⟨473714, by rfl⟩ : syracuseStep 631619 = 947429) B947429
theorem B959309 : Blo 279826 959309 := bstep (se 3 (by rfl) ⟨179870, by rfl⟩ : syracuseStep 959309 = 359741) B359741
theorem B1418147 : Blo 279826 1418147 := bstep (se 1 (by rfl) ⟨1063610, by rfl⟩ : syracuseStep 1418147 = 2127221) B2127221
theorem B402403 : Blo 279826 402403 := bstep (se 1 (by rfl) ⟨301802, by rfl⟩ : syracuseStep 402403 = 603605) B603605
theorem B336899 : Blo 279826 336899 := bstep (se 1 (by rfl) ⟨252674, by rfl⟩ : syracuseStep 336899 = 505349) B505349
theorem B402499 : Blo 279826 402499 := bstep (se 1 (by rfl) ⟨301874, by rfl⟩ : syracuseStep 402499 = 603749) B603749
theorem B1614917 : Blo 279826 1614917 := bstep (se 4 (by rfl) ⟨151398, by rfl⟩ : syracuseStep 1614917 = 302797) B302797
theorem B631889 : Blo 279826 631889 := bstep (se 2 (by rfl) ⟨236958, by rfl⟩ : syracuseStep 631889 = 473917) B473917
theorem B631907 : Blo 279826 631907 := bstep (se 1 (by rfl) ⟨473930, by rfl⟩ : syracuseStep 631907 = 947861) B947861
theorem B1811555 : Blo 279826 1811555 := bstep (se 1 (by rfl) ⟨1358666, by rfl⟩ : syracuseStep 1811555 = 2717333) B2717333
theorem B3220721 : Blo 279826 3220721 := bstep (se 2 (by rfl) ⟨1207770, by rfl⟩ : syracuseStep 3220721 = 2415541) B2415541
theorem B632177 : Blo 279826 632177 := bstep (se 2 (by rfl) ⟨237066, by rfl⟩ : syracuseStep 632177 = 474133) B474133
theorem B632195 : Blo 279826 632195 := bstep (se 1 (by rfl) ⟨474146, by rfl⟩ : syracuseStep 632195 = 948293) B948293
theorem B337379 : Blo 279826 337379 := bstep (se 1 (by rfl) ⟨253034, by rfl⟩ : syracuseStep 337379 = 506069) B506069
theorem B1615373 : Blo 279826 1615373 := bstep (se 3 (by rfl) ⟨302882, by rfl⟩ : syracuseStep 1615373 = 605765) B605765
theorem B2991629 : Blo 279826 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B402995 : Blo 279826 402995 := bstep (se 1 (by rfl) ⟨302246, by rfl⟩ : syracuseStep 402995 = 604493) B604493
theorem B599683 : Blo 279826 599683 := bstep (se 1 (by rfl) ⟨449762, by rfl⟩ : syracuseStep 599683 = 899525) B899525
theorem B632465 : Blo 279826 632465 := bstep (se 2 (by rfl) ⟨237174, by rfl⟩ : syracuseStep 632465 = 474349) B474349
theorem B632483 : Blo 279826 632483 := bstep (se 1 (by rfl) ⟨474362, by rfl⟩ : syracuseStep 632483 = 948725) B948725
theorem B1418957 : Blo 279826 1418957 := bstep (se 3 (by rfl) ⟨266054, by rfl⟩ : syracuseStep 1418957 = 532109) B532109
theorem B534289 : Blo 279826 534289 := bstep (se 2 (by rfl) ⟨200358, by rfl⟩ : syracuseStep 534289 = 400717) B400717
theorem B861997 : Blo 279826 861997 := bstep (se 3 (by rfl) ⟨161624, by rfl⟩ : syracuseStep 861997 = 323249) B323249
theorem B862093 : Blo 279826 862093 := bstep (se 3 (by rfl) ⟨161642, by rfl⟩ : syracuseStep 862093 = 323285) B323285
theorem B632753 : Blo 279826 632753 := bstep (se 2 (by rfl) ⟨237282, by rfl⟩ : syracuseStep 632753 = 474565) B474565
theorem B632771 : Blo 279826 632771 := bstep (se 1 (by rfl) ⟨474578, by rfl⟩ : syracuseStep 632771 = 949157) B949157
theorem B534691 : Blo 279826 534691 := bstep (se 1 (by rfl) ⟨401018, by rfl⟩ : syracuseStep 534691 = 802037) B802037
theorem B403633 : Blo 279826 403633 := bstep (se 2 (by rfl) ⟨151362, by rfl⟩ : syracuseStep 403633 = 302725) B302725
theorem B501955 : Blo 279826 501955 := bstep (se 1 (by rfl) ⟨376466, by rfl⟩ : syracuseStep 501955 = 752933) B752933
theorem B633041 : Blo 279826 633041 := bstep (se 2 (by rfl) ⟨237390, by rfl⟩ : syracuseStep 633041 = 474781) B474781
theorem B534737 : Blo 279826 534737 := bstep (se 2 (by rfl) ⟨200526, by rfl⟩ : syracuseStep 534737 = 401053) B401053
theorem B633059 : Blo 279826 633059 := bstep (se 1 (by rfl) ⟨474794, by rfl⟩ : syracuseStep 633059 = 949589) B949589
theorem B2271473 : Blo 279826 2271473 := bstep (se 2 (by rfl) ⟨851802, by rfl⟩ : syracuseStep 2271473 = 1703605) B1703605
theorem B1812941 : Blo 279826 1812941 := bstep (se 3 (by rfl) ⟨339926, by rfl⟩ : syracuseStep 1812941 = 679853) B679853
theorem B600529 : Blo 279826 600529 := bstep (se 2 (by rfl) ⟨225198, by rfl⟩ : syracuseStep 600529 = 450397) B450397
theorem B633329 : Blo 279826 633329 := bstep (se 2 (by rfl) ⟨237498, by rfl⟩ : syracuseStep 633329 = 474997) B474997
theorem B535025 : Blo 279826 535025 := bstep (se 2 (by rfl) ⟨200634, by rfl⟩ : syracuseStep 535025 = 401269) B401269
theorem B403969 : Blo 279826 403969 := bstep (se 2 (by rfl) ⟨151488, by rfl⟩ : syracuseStep 403969 = 302977) B302977
theorem B633347 : Blo 279826 633347 := bstep (se 1 (by rfl) ⟨475010, by rfl⟩ : syracuseStep 633347 = 950021) B950021
theorem B633617 : Blo 279826 633617 := bstep (se 2 (by rfl) ⟨237606, by rfl⟩ : syracuseStep 633617 = 475213) B475213
theorem B633635 : Blo 279826 633635 := bstep (se 1 (by rfl) ⟨475226, by rfl⟩ : syracuseStep 633635 = 950453) B950453
theorem B1354573 : Blo 279826 1354573 := bstep (se 3 (by rfl) ⟨253982, by rfl⟩ : syracuseStep 1354573 = 507965) B507965
theorem B797617 : Blo 279826 797617 := bstep (se 2 (by rfl) ⟨299106, by rfl⟩ : syracuseStep 797617 = 598213) B598213
theorem B633905 : Blo 279826 633905 := bstep (se 2 (by rfl) ⟨237714, by rfl⟩ : syracuseStep 633905 = 475429) B475429
theorem B633923 : Blo 279826 633923 := bstep (se 1 (by rfl) ⟨475442, by rfl⟩ : syracuseStep 633923 = 950885) B950885
theorem B535747 : Blo 279826 535747 := bstep (se 1 (by rfl) ⟨401810, by rfl⟩ : syracuseStep 535747 = 803621) B803621
theorem B634193 : Blo 279826 634193 := bstep (se 2 (by rfl) ⟨237822, by rfl⟩ : syracuseStep 634193 = 475645) B475645
theorem B634211 : Blo 279826 634211 := bstep (se 1 (by rfl) ⟨475658, by rfl⟩ : syracuseStep 634211 = 951317) B951317
theorem B2076101 : Blo 279826 2076101 := bstep (se 4 (by rfl) ⟨194634, by rfl⟩ : syracuseStep 2076101 = 389269) B389269
theorem B339427 : Blo 279826 339427 := bstep (se 1 (by rfl) ⟨254570, by rfl⟩ : syracuseStep 339427 = 509141) B509141
theorem B634481 : Blo 279826 634481 := bstep (se 2 (by rfl) ⟨237930, by rfl⟩ : syracuseStep 634481 = 475861) B475861
theorem B634499 : Blo 279826 634499 := bstep (se 1 (by rfl) ⟨475874, by rfl⟩ : syracuseStep 634499 = 951749) B951749
theorem B536195 : Blo 279826 536195 := bstep (se 1 (by rfl) ⟨402146, by rfl⟩ : syracuseStep 536195 = 804293) B804293
theorem B1289891 : Blo 279826 1289891 := bstep (se 1 (by rfl) ⟨967418, by rfl⟩ : syracuseStep 1289891 = 1934837) B1934837
theorem B765677 : Blo 279826 765677 := bstep (se 3 (by rfl) ⟨143564, by rfl⟩ : syracuseStep 765677 = 287129) B287129
theorem B339763 : Blo 279826 339763 := bstep (se 1 (by rfl) ⟨254822, by rfl⟩ : syracuseStep 339763 = 509645) B509645
theorem B634769 : Blo 279826 634769 := bstep (se 2 (by rfl) ⟨238038, by rfl⟩ : syracuseStep 634769 = 476077) B476077
theorem B634787 : Blo 279826 634787 := bstep (se 1 (by rfl) ⟨476090, by rfl⟩ : syracuseStep 634787 = 952181) B952181
theorem B536483 : Blo 279826 536483 := bstep (se 1 (by rfl) ⟨402362, by rfl⟩ : syracuseStep 536483 = 804725) B804725
theorem B798893 : Blo 279826 798893 := bstep (se 3 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 798893 = 299585) B299585
theorem B635057 : Blo 279826 635057 := bstep (se 2 (by rfl) ⟨238146, by rfl⟩ : syracuseStep 635057 = 476293) B476293
theorem B569539 : Blo 279826 569539 := bstep (se 1 (by rfl) ⟨427154, by rfl⟩ : syracuseStep 569539 = 854309) B854309
theorem B635075 : Blo 279826 635075 := bstep (se 1 (by rfl) ⟨476306, by rfl⟩ : syracuseStep 635075 = 952613) B952613
theorem B602417 : Blo 279826 602417 := bstep (se 2 (by rfl) ⟨225906, by rfl⟩ : syracuseStep 602417 = 451813) B451813
theorem B799075 : Blo 279826 799075 := bstep (se 1 (by rfl) ⟨599306, by rfl⟩ : syracuseStep 799075 = 1198613) B1198613
theorem B799121 : Blo 279826 799121 := bstep (se 2 (by rfl) ⟨299670, by rfl⟩ : syracuseStep 799121 = 599341) B599341
theorem B635345 : Blo 279826 635345 := bstep (se 2 (by rfl) ⟨238254, by rfl⟩ : syracuseStep 635345 = 476509) B476509
theorem B635363 : Blo 279826 635363 := bstep (se 1 (by rfl) ⟨476522, by rfl⟩ : syracuseStep 635363 = 953045) B953045
theorem B1421873 : Blo 279826 1421873 := bstep (se 2 (by rfl) ⟨533202, by rfl⟩ : syracuseStep 1421873 = 1066405) B1066405
theorem B6861509 : Blo 279826 6861509 := bstep (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) B1286533
theorem B635633 : Blo 279826 635633 := bstep (se 2 (by rfl) ⟨238362, by rfl⟩ : syracuseStep 635633 = 476725) B476725
theorem B635651 : Blo 279826 635651 := bstep (se 1 (by rfl) ⟨476738, by rfl⟩ : syracuseStep 635651 = 953477) B953477
theorem B504643 : Blo 279826 504643 := bstep (se 1 (by rfl) ⟨378482, by rfl⟩ : syracuseStep 504643 = 756965) B756965
theorem B1192781 : Blo 279826 1192781 := bstep (se 3 (by rfl) ⟨223646, by rfl⟩ : syracuseStep 1192781 = 447293) B447293
theorem B537425 : Blo 279826 537425 := bstep (se 2 (by rfl) ⟨201534, by rfl⟩ : syracuseStep 537425 = 403069) B403069
theorem B635921 : Blo 279826 635921 := bstep (se 2 (by rfl) ⟨238470, by rfl⟩ : syracuseStep 635921 = 476941) B476941
theorem B635939 : Blo 279826 635939 := bstep (se 1 (by rfl) ⟨476954, by rfl⟩ : syracuseStep 635939 = 953909) B953909
theorem B472243 : Blo 279826 472243 := bstep (se 1 (by rfl) ⟨354182, by rfl⟩ : syracuseStep 472243 = 708365) B708365
theorem B767171 : Blo 279826 767171 := bstep (se 1 (by rfl) ⟨575378, by rfl⟩ : syracuseStep 767171 = 1150757) B1150757
theorem B570577 : Blo 279826 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B636209 : Blo 279826 636209 := bstep (se 2 (by rfl) ⟨238578, by rfl⟩ : syracuseStep 636209 = 477157) B477157
theorem B472385 : Blo 279826 472385 := bstep (se 2 (by rfl) ⟨177144, by rfl⟩ : syracuseStep 472385 = 354289) B354289
theorem B636227 : Blo 279826 636227 := bstep (se 1 (by rfl) ⟨477170, by rfl⟩ : syracuseStep 636227 = 954341) B954341
theorem B570755 : Blo 279826 570755 := bstep (se 1 (by rfl) ⟨428066, by rfl⟩ : syracuseStep 570755 = 856133) B856133
theorem B472513 : Blo 279826 472513 := bstep (se 2 (by rfl) ⟨177192, by rfl⟩ : syracuseStep 472513 = 354385) B354385
theorem B472547 : Blo 279826 472547 := bstep (se 1 (by rfl) ⟨354410, by rfl⟩ : syracuseStep 472547 = 708821) B708821
theorem B898577 : Blo 279826 898577 := bstep (se 2 (by rfl) ⟨336966, by rfl⟩ : syracuseStep 898577 = 673933) B673933
theorem B603715 : Blo 279826 603715 := bstep (se 1 (by rfl) ⟨452786, by rfl⟩ : syracuseStep 603715 = 905573) B905573
theorem B636497 : Blo 279826 636497 := bstep (se 2 (by rfl) ⟨238686, by rfl⟩ : syracuseStep 636497 = 477373) B477373
theorem B472675 : Blo 279826 472675 := bstep (se 1 (by rfl) ⟨354506, by rfl⟩ : syracuseStep 472675 = 709013) B709013
theorem B636515 : Blo 279826 636515 := bstep (se 1 (by rfl) ⟨477386, by rfl⟩ : syracuseStep 636515 = 954773) B954773
theorem B1717957 : Blo 279826 1717957 := bstep (se 4 (by rfl) ⟨161058, by rfl⟩ : syracuseStep 1717957 = 322117) B322117
theorem B538321 : Blo 279826 538321 := bstep (se 2 (by rfl) ⟨201870, by rfl⟩ : syracuseStep 538321 = 403741) B403741
theorem B472817 : Blo 279826 472817 := bstep (se 2 (by rfl) ⟨177306, by rfl⟩ : syracuseStep 472817 = 354613) B354613
theorem B800579 : Blo 279826 800579 := bstep (se 1 (by rfl) ⟨600434, by rfl⟩ : syracuseStep 800579 = 1200869) B1200869
theorem B1357667 : Blo 279826 1357667 := bstep (se 1 (by rfl) ⟨1018250, by rfl⟩ : syracuseStep 1357667 = 2036501) B2036501
theorem B472945 : Blo 279826 472945 := bstep (se 2 (by rfl) ⟨177354, by rfl⟩ : syracuseStep 472945 = 354709) B354709
theorem B636785 : Blo 279826 636785 := bstep (se 2 (by rfl) ⟨238794, by rfl⟩ : syracuseStep 636785 = 477589) B477589
theorem B538481 : Blo 279826 538481 := bstep (se 2 (by rfl) ⟨201930, by rfl⟩ : syracuseStep 538481 = 403861) B403861
theorem B636803 : Blo 279826 636803 := bstep (se 1 (by rfl) ⟨477602, by rfl⟩ : syracuseStep 636803 = 955205) B955205
theorem B472979 : Blo 279826 472979 := bstep (se 1 (by rfl) ⟨354734, by rfl⟩ : syracuseStep 472979 = 709469) B709469
theorem B1423331 : Blo 279826 1423331 := bstep (se 1 (by rfl) ⟨1067498, by rfl⟩ : syracuseStep 1423331 = 2134997) B2134997
theorem B473107 : Blo 279826 473107 := bstep (se 1 (by rfl) ⟨354830, by rfl⟩ : syracuseStep 473107 = 709661) B709661
theorem B1062989 : Blo 279826 1062989 := bstep (se 3 (by rfl) ⟨199310, by rfl⟩ : syracuseStep 1062989 = 398621) B398621
theorem B1554509 : Blo 279826 1554509 := bstep (se 3 (by rfl) ⟨291470, by rfl⟩ : syracuseStep 1554509 = 582941) B582941
theorem B637073 : Blo 279826 637073 := bstep (se 2 (by rfl) ⟨238902, by rfl⟩ : syracuseStep 637073 = 477805) B477805
theorem B473249 : Blo 279826 473249 := bstep (se 2 (by rfl) ⟨177468, by rfl⟩ : syracuseStep 473249 = 354937) B354937
theorem B637091 : Blo 279826 637091 := bstep (se 1 (by rfl) ⟨477818, by rfl⟩ : syracuseStep 637091 = 955637) B955637
theorem B899267 : Blo 279826 899267 := bstep (se 1 (by rfl) ⟨674450, by rfl⟩ : syracuseStep 899267 = 1348901) B1348901
theorem B473377 : Blo 279826 473377 := bstep (se 2 (by rfl) ⟨177516, by rfl⟩ : syracuseStep 473377 = 355033) B355033
theorem B473411 : Blo 279826 473411 := bstep (se 1 (by rfl) ⟨355058, by rfl⟩ : syracuseStep 473411 = 710117) B710117
theorem B637361 : Blo 279826 637361 := bstep (se 2 (by rfl) ⟨239010, by rfl⟩ : syracuseStep 637361 = 478021) B478021
theorem B473539 : Blo 279826 473539 := bstep (se 1 (by rfl) ⟨355154, by rfl⟩ : syracuseStep 473539 = 710309) B710309
theorem B637379 : Blo 279826 637379 := bstep (se 1 (by rfl) ⟨478034, by rfl⟩ : syracuseStep 637379 = 956069) B956069
theorem B539185 : Blo 279826 539185 := bstep (se 2 (by rfl) ⟨202194, by rfl⟩ : syracuseStep 539185 = 404389) B404389
theorem B473681 : Blo 279826 473681 := bstep (se 2 (by rfl) ⟨177630, by rfl⟩ : syracuseStep 473681 = 355261) B355261
theorem B1358477 : Blo 279826 1358477 := bstep (se 3 (by rfl) ⟨254714, by rfl⟩ : syracuseStep 1358477 = 509429) B509429
theorem B473809 : Blo 279826 473809 := bstep (se 2 (by rfl) ⟨177678, by rfl⟩ : syracuseStep 473809 = 355357) B355357
theorem B637649 : Blo 279826 637649 := bstep (se 2 (by rfl) ⟨239118, by rfl⟩ : syracuseStep 637649 = 478237) B478237
theorem B637667 : Blo 279826 637667 := bstep (se 1 (by rfl) ⟨478250, by rfl⟩ : syracuseStep 637667 = 956501) B956501
theorem B473843 : Blo 279826 473843 := bstep (se 1 (by rfl) ⟨355382, by rfl⟩ : syracuseStep 473843 = 710765) B710765
theorem B1424141 : Blo 279826 1424141 := bstep (se 3 (by rfl) ⟨267026, by rfl⟩ : syracuseStep 1424141 = 534053) B534053
theorem B604945 : Blo 279826 604945 := bstep (se 2 (by rfl) ⟨226854, by rfl⟩ : syracuseStep 604945 = 453709) B453709
theorem B1063793 : Blo 279826 1063793 := bstep (se 2 (by rfl) ⟨398922, by rfl⟩ : syracuseStep 1063793 = 797845) B797845
theorem B473971 : Blo 279826 473971 := bstep (se 1 (by rfl) ⟨355478, by rfl⟩ : syracuseStep 473971 = 710957) B710957
theorem B506819 : Blo 279826 506819 := bstep (se 1 (by rfl) ⟨380114, by rfl⟩ : syracuseStep 506819 = 760229) B760229
theorem B637937 : Blo 279826 637937 := bstep (se 2 (by rfl) ⟨239226, by rfl⟩ : syracuseStep 637937 = 478453) B478453
theorem B474113 : Blo 279826 474113 := bstep (se 2 (by rfl) ⟨177792, by rfl⟩ : syracuseStep 474113 = 355585) B355585
theorem B637955 : Blo 279826 637955 := bstep (se 1 (by rfl) ⟨478466, by rfl⟩ : syracuseStep 637955 = 956933) B956933
theorem B801809 : Blo 279826 801809 := bstep (se 2 (by rfl) ⟨300678, by rfl⟩ : syracuseStep 801809 = 601357) B601357
theorem B736337 : Blo 279826 736337 := bstep (se 2 (by rfl) ⟨276126, by rfl⟩ : syracuseStep 736337 = 552253) B552253
theorem B474241 : Blo 279826 474241 := bstep (se 2 (by rfl) ⟨177840, by rfl⟩ : syracuseStep 474241 = 355681) B355681
theorem B474275 : Blo 279826 474275 := bstep (se 1 (by rfl) ⟨355706, by rfl⟩ : syracuseStep 474275 = 711413) B711413
theorem B507107 : Blo 279826 507107 := bstep (se 1 (by rfl) ⟨380330, by rfl⟩ : syracuseStep 507107 = 760661) B760661
theorem B638225 : Blo 279826 638225 := bstep (se 2 (by rfl) ⟨239334, by rfl⟩ : syracuseStep 638225 = 478669) B478669
theorem B474403 : Blo 279826 474403 := bstep (se 1 (by rfl) ⟨355802, by rfl⟩ : syracuseStep 474403 = 711605) B711605
theorem B638243 : Blo 279826 638243 := bstep (se 1 (by rfl) ⟨478682, by rfl⟩ : syracuseStep 638243 = 957365) B957365
theorem B540049 : Blo 279826 540049 := bstep (se 2 (by rfl) ⟨202518, by rfl⟩ : syracuseStep 540049 = 405037) B405037
theorem B474545 : Blo 279826 474545 := bstep (se 2 (by rfl) ⟨177954, by rfl⟩ : syracuseStep 474545 = 355909) B355909
theorem B1359281 : Blo 279826 1359281 := bstep (se 2 (by rfl) ⟨509730, by rfl⟩ : syracuseStep 1359281 = 1019461) B1019461
theorem B1195469 : Blo 279826 1195469 := bstep (se 3 (by rfl) ⟨224150, by rfl⟩ : syracuseStep 1195469 = 448301) B448301
theorem B1195505 : Blo 279826 1195505 := bstep (se 2 (by rfl) ⟨448314, by rfl⟩ : syracuseStep 1195505 = 896629) B896629
theorem B1064461 : Blo 279826 1064461 := bstep (se 3 (by rfl) ⟨199586, by rfl⟩ : syracuseStep 1064461 = 399173) B399173
theorem B605731 : Blo 279826 605731 := bstep (se 1 (by rfl) ⟨454298, by rfl⟩ : syracuseStep 605731 = 908597) B908597
theorem B474673 : Blo 279826 474673 := bstep (se 2 (by rfl) ⟨178002, by rfl⟩ : syracuseStep 474673 = 356005) B356005
theorem B638513 : Blo 279826 638513 := bstep (se 2 (by rfl) ⟨239442, by rfl⟩ : syracuseStep 638513 = 478885) B478885
theorem B638531 : Blo 279826 638531 := bstep (se 1 (by rfl) ⟨478898, by rfl⟩ : syracuseStep 638531 = 957797) B957797
theorem B933457 : Blo 279826 933457 := bstep (se 2 (by rfl) ⟨350046, by rfl⟩ : syracuseStep 933457 = 700093) B700093
theorem B474707 : Blo 279826 474707 := bstep (se 1 (by rfl) ⟨356030, by rfl⟩ : syracuseStep 474707 = 712061) B712061
theorem B474835 : Blo 279826 474835 := bstep (se 1 (by rfl) ⟨356126, by rfl⟩ : syracuseStep 474835 = 712253) B712253
theorem B474977 : Blo 279826 474977 := bstep (se 2 (by rfl) ⟨178116, by rfl⟩ : syracuseStep 474977 = 356233) B356233
theorem B901037 : Blo 279826 901037 := bstep (se 3 (by rfl) ⟨168944, by rfl⟩ : syracuseStep 901037 = 337889) B337889
theorem B475105 : Blo 279826 475105 := bstep (se 2 (by rfl) ⟨178164, by rfl⟩ : syracuseStep 475105 = 356329) B356329
theorem B475139 : Blo 279826 475139 := bstep (se 1 (by rfl) ⟨356354, by rfl⟩ : syracuseStep 475139 = 712709) B712709
theorem B901165 : Blo 279826 901165 := bstep (se 3 (by rfl) ⟨168968, by rfl⟩ : syracuseStep 901165 = 337937) B337937
theorem B475267 : Blo 279826 475267 := bstep (se 1 (by rfl) ⟨356450, by rfl⟩ : syracuseStep 475267 = 712901) B712901
theorem B475409 : Blo 279826 475409 := bstep (se 2 (by rfl) ⟨178278, by rfl⟩ : syracuseStep 475409 = 356557) B356557
theorem B1065251 : Blo 279826 1065251 := bstep (se 1 (by rfl) ⟨798938, by rfl⟩ : syracuseStep 1065251 = 1597877) B1597877
theorem B901421 : Blo 279826 901421 := bstep (se 3 (by rfl) ⟨169016, by rfl⟩ : syracuseStep 901421 = 338033) B338033
theorem B475537 : Blo 279826 475537 := bstep (se 2 (by rfl) ⟨178326, by rfl⟩ : syracuseStep 475537 = 356653) B356653
theorem B475571 : Blo 279826 475571 := bstep (se 1 (by rfl) ⟨356678, by rfl⟩ : syracuseStep 475571 = 713357) B713357
theorem B803267 : Blo 279826 803267 := bstep (se 1 (by rfl) ⟨602450, by rfl⟩ : syracuseStep 803267 = 1204901) B1204901
theorem B475699 : Blo 279826 475699 := bstep (se 1 (by rfl) ⟨356774, by rfl⟩ : syracuseStep 475699 = 713549) B713549
theorem B475841 : Blo 279826 475841 := bstep (se 2 (by rfl) ⟨178440, by rfl⟩ : syracuseStep 475841 = 356881) B356881
theorem B475969 : Blo 279826 475969 := bstep (se 2 (by rfl) ⟨178488, by rfl⟩ : syracuseStep 475969 = 356977) B356977
theorem B476003 : Blo 279826 476003 := bstep (se 1 (by rfl) ⟨357002, by rfl⟩ : syracuseStep 476003 = 714005) B714005
theorem B1065905 : Blo 279826 1065905 := bstep (se 2 (by rfl) ⟨399714, by rfl⟩ : syracuseStep 1065905 = 799429) B799429
theorem B345043 : Blo 279826 345043 := bstep (se 1 (by rfl) ⟨258782, by rfl⟩ : syracuseStep 345043 = 517565) B517565
theorem B476131 : Blo 279826 476131 := bstep (se 1 (by rfl) ⟨357098, by rfl⟩ : syracuseStep 476131 = 714197) B714197
theorem B476273 : Blo 279826 476273 := bstep (se 2 (by rfl) ⟨178602, by rfl⟩ : syracuseStep 476273 = 357205) B357205
theorem B607409 : Blo 279826 607409 := bstep (se 2 (by rfl) ⟨227778, by rfl⟩ : syracuseStep 607409 = 455557) B455557
theorem B3032261 : Blo 279826 3032261 := bstep (se 4 (by rfl) ⟨284274, by rfl⟩ : syracuseStep 3032261 = 568549) B568549
theorem B804077 : Blo 279826 804077 := bstep (se 3 (by rfl) ⟨150764, by rfl⟩ : syracuseStep 804077 = 301529) B301529
theorem B476401 : Blo 279826 476401 := bstep (se 2 (by rfl) ⟨178650, by rfl⟩ : syracuseStep 476401 = 357301) B357301
theorem B279827 : Blo 279826 279827 := bstep (se 1 (by rfl) ⟨209870, by rfl⟩ : syracuseStep 279827 = 419741) B419741
theorem B476435 : Blo 279826 476435 := bstep (se 1 (by rfl) ⟨357326, by rfl⟩ : syracuseStep 476435 = 714653) B714653
theorem B279843 : Blo 279826 279843 := bstep (se 1 (by rfl) ⟨209882, by rfl⟩ : syracuseStep 279843 = 419765) B419765
theorem B279859 : Blo 279826 279859 := bstep (se 1 (by rfl) ⟨209894, by rfl⟩ : syracuseStep 279859 = 419789) B419789
theorem B279875 : Blo 279826 279875 := bstep (se 1 (by rfl) ⟨209906, by rfl⟩ : syracuseStep 279875 = 419813) B419813
theorem B279891 : Blo 279826 279891 := bstep (se 1 (by rfl) ⟨209918, by rfl⟩ : syracuseStep 279891 = 419837) B419837
theorem B279907 : Blo 279826 279907 := bstep (se 1 (by rfl) ⟨209930, by rfl⟩ : syracuseStep 279907 = 419861) B419861
theorem B279923 : Blo 279826 279923 := bstep (se 1 (by rfl) ⟨209942, by rfl⟩ : syracuseStep 279923 = 419885) B419885
theorem B279939 : Blo 279826 279939 := bstep (se 1 (by rfl) ⟨209954, by rfl⟩ : syracuseStep 279939 = 419909) B419909
theorem B279955 : Blo 279826 279955 := bstep (se 1 (by rfl) ⟨209966, by rfl⟩ : syracuseStep 279955 = 419933) B419933
theorem B476563 : Blo 279826 476563 := bstep (se 1 (by rfl) ⟨357422, by rfl⟩ : syracuseStep 476563 = 714845) B714845
theorem B279971 : Blo 279826 279971 := bstep (se 1 (by rfl) ⟨209978, by rfl⟩ : syracuseStep 279971 = 419957) B419957
theorem B804269 : Blo 279826 804269 := bstep (se 3 (by rfl) ⟨150800, by rfl⟩ : syracuseStep 804269 = 301601) B301601
theorem B279987 : Blo 279826 279987 := bstep (se 1 (by rfl) ⟨209990, by rfl⟩ : syracuseStep 279987 = 419981) B419981
theorem B280003 : Blo 279826 280003 := bstep (se 1 (by rfl) ⟨210002, by rfl⟩ : syracuseStep 280003 = 420005) B420005
theorem B3851717 : Blo 279826 3851717 := bstep (se 4 (by rfl) ⟨361098, by rfl⟩ : syracuseStep 3851717 = 722197) B722197
theorem B1361357 : Blo 279826 1361357 := bstep (se 3 (by rfl) ⟨255254, by rfl⟩ : syracuseStep 1361357 = 510509) B510509
theorem B280019 : Blo 279826 280019 := bstep (se 1 (by rfl) ⟨210014, by rfl⟩ : syracuseStep 280019 = 420029) B420029
theorem B280035 : Blo 279826 280035 := bstep (se 1 (by rfl) ⟨210026, by rfl⟩ : syracuseStep 280035 = 420053) B420053
theorem B280051 : Blo 279826 280051 := bstep (se 1 (by rfl) ⟨210038, by rfl⟩ : syracuseStep 280051 = 420077) B420077
theorem B280067 : Blo 279826 280067 := bstep (se 1 (by rfl) ⟨210050, by rfl⟩ : syracuseStep 280067 = 420101) B420101
theorem B280083 : Blo 279826 280083 := bstep (se 1 (by rfl) ⟨210062, by rfl⟩ : syracuseStep 280083 = 420125) B420125
theorem B476705 : Blo 279826 476705 := bstep (se 2 (by rfl) ⟨178764, by rfl⟩ : syracuseStep 476705 = 357529) B357529
theorem B280099 : Blo 279826 280099 := bstep (se 1 (by rfl) ⟨210074, by rfl⟩ : syracuseStep 280099 = 420149) B420149
theorem B280115 : Blo 279826 280115 := bstep (se 1 (by rfl) ⟨210086, by rfl⟩ : syracuseStep 280115 = 420173) B420173
theorem B280131 : Blo 279826 280131 := bstep (se 1 (by rfl) ⟨210098, by rfl⟩ : syracuseStep 280131 = 420197) B420197
theorem B280147 : Blo 279826 280147 := bstep (se 1 (by rfl) ⟨210110, by rfl⟩ : syracuseStep 280147 = 420221) B420221
theorem B280163 : Blo 279826 280163 := bstep (se 1 (by rfl) ⟨210122, by rfl⟩ : syracuseStep 280163 = 420245) B420245
theorem B1427057 : Blo 279826 1427057 := bstep (se 2 (by rfl) ⟨535146, by rfl⟩ : syracuseStep 1427057 = 1070293) B1070293
theorem B280179 : Blo 279826 280179 := bstep (se 1 (by rfl) ⟨210134, by rfl⟩ : syracuseStep 280179 = 420269) B420269
theorem B280195 : Blo 279826 280195 := bstep (se 1 (by rfl) ⟨210146, by rfl⟩ : syracuseStep 280195 = 420293) B420293
theorem B280211 : Blo 279826 280211 := bstep (se 1 (by rfl) ⟨210158, by rfl⟩ : syracuseStep 280211 = 420317) B420317
theorem B476833 : Blo 279826 476833 := bstep (se 2 (by rfl) ⟨178812, by rfl⟩ : syracuseStep 476833 = 357625) B357625
theorem B280227 : Blo 279826 280227 := bstep (se 1 (by rfl) ⟨210170, by rfl⟩ : syracuseStep 280227 = 420341) B420341
theorem B280243 : Blo 279826 280243 := bstep (se 1 (by rfl) ⟨210182, by rfl⟩ : syracuseStep 280243 = 420365) B420365
theorem B280259 : Blo 279826 280259 := bstep (se 1 (by rfl) ⟨210194, by rfl⟩ : syracuseStep 280259 = 420389) B420389
theorem B476867 : Blo 279826 476867 := bstep (se 1 (by rfl) ⟨357650, by rfl⟩ : syracuseStep 476867 = 715301) B715301
theorem B280275 : Blo 279826 280275 := bstep (se 1 (by rfl) ⟨210206, by rfl⟩ : syracuseStep 280275 = 420413) B420413
theorem B280291 : Blo 279826 280291 := bstep (se 1 (by rfl) ⟨210218, by rfl⟩ : syracuseStep 280291 = 420437) B420437
theorem B1918691 : Blo 279826 1918691 := bstep (se 1 (by rfl) ⟨1439018, by rfl⟩ : syracuseStep 1918691 = 2878037) B2878037
theorem B280307 : Blo 279826 280307 := bstep (se 1 (by rfl) ⟨210230, by rfl⟩ : syracuseStep 280307 = 420461) B420461
theorem B280323 : Blo 279826 280323 := bstep (se 1 (by rfl) ⟨210242, by rfl⟩ : syracuseStep 280323 = 420485) B420485
theorem B280339 : Blo 279826 280339 := bstep (se 1 (by rfl) ⟨210254, by rfl⟩ : syracuseStep 280339 = 420509) B420509
theorem B280355 : Blo 279826 280355 := bstep (se 1 (by rfl) ⟨210266, by rfl⟩ : syracuseStep 280355 = 420533) B420533
theorem B902947 : Blo 279826 902947 := bstep (se 1 (by rfl) ⟨677210, by rfl⟩ : syracuseStep 902947 = 1354421) B1354421
theorem B280371 : Blo 279826 280371 := bstep (se 1 (by rfl) ⟨210278, by rfl⟩ : syracuseStep 280371 = 420557) B420557
theorem B280387 : Blo 279826 280387 := bstep (se 1 (by rfl) ⟨210290, by rfl⟩ : syracuseStep 280387 = 420581) B420581
theorem B476995 : Blo 279826 476995 := bstep (se 1 (by rfl) ⟨357746, by rfl⟩ : syracuseStep 476995 = 715493) B715493
theorem B280403 : Blo 279826 280403 := bstep (se 1 (by rfl) ⟨210302, by rfl⟩ : syracuseStep 280403 = 420605) B420605
theorem B280419 : Blo 279826 280419 := bstep (se 1 (by rfl) ⟨210314, by rfl⟩ : syracuseStep 280419 = 420629) B420629
theorem B280435 : Blo 279826 280435 := bstep (se 1 (by rfl) ⟨210326, by rfl⟩ : syracuseStep 280435 = 420653) B420653
theorem B280451 : Blo 279826 280451 := bstep (se 1 (by rfl) ⟨210338, by rfl⟩ : syracuseStep 280451 = 420677) B420677
theorem B280467 : Blo 279826 280467 := bstep (se 1 (by rfl) ⟨210350, by rfl⟩ : syracuseStep 280467 = 420701) B420701
theorem B280483 : Blo 279826 280483 := bstep (se 1 (by rfl) ⟨210362, by rfl⟩ : syracuseStep 280483 = 420725) B420725
theorem B280499 : Blo 279826 280499 := bstep (se 1 (by rfl) ⟨210374, by rfl⟩ : syracuseStep 280499 = 420749) B420749
theorem B346051 : Blo 279826 346051 := bstep (se 1 (by rfl) ⟨259538, by rfl⟩ : syracuseStep 346051 = 519077) B519077
theorem B280515 : Blo 279826 280515 := bstep (se 1 (by rfl) ⟨210386, by rfl⟩ : syracuseStep 280515 = 420773) B420773
theorem B477137 : Blo 279826 477137 := bstep (se 2 (by rfl) ⟨178926, by rfl⟩ : syracuseStep 477137 = 357853) B357853
theorem B280531 : Blo 279826 280531 := bstep (se 1 (by rfl) ⟨210398, by rfl⟩ : syracuseStep 280531 = 420797) B420797
theorem B280547 : Blo 279826 280547 := bstep (se 1 (by rfl) ⟨210410, by rfl⟩ : syracuseStep 280547 = 420821) B420821
theorem B280563 : Blo 279826 280563 := bstep (se 1 (by rfl) ⟨210422, by rfl⟩ : syracuseStep 280563 = 420845) B420845
theorem B280579 : Blo 279826 280579 := bstep (se 1 (by rfl) ⟨210434, by rfl⟩ : syracuseStep 280579 = 420869) B420869
theorem B280595 : Blo 279826 280595 := bstep (se 1 (by rfl) ⟨210446, by rfl⟩ : syracuseStep 280595 = 420893) B420893
theorem B280611 : Blo 279826 280611 := bstep (se 1 (by rfl) ⟨210458, by rfl⟩ : syracuseStep 280611 = 420917) B420917
theorem B280627 : Blo 279826 280627 := bstep (se 1 (by rfl) ⟨210470, by rfl⟩ : syracuseStep 280627 = 420941) B420941
theorem B280643 : Blo 279826 280643 := bstep (se 1 (by rfl) ⟨210482, by rfl⟩ : syracuseStep 280643 = 420965) B420965
theorem B477265 : Blo 279826 477265 := bstep (se 2 (by rfl) ⟨178974, by rfl⟩ : syracuseStep 477265 = 357949) B357949
theorem B280659 : Blo 279826 280659 := bstep (se 1 (by rfl) ⟨210494, by rfl⟩ : syracuseStep 280659 = 420989) B420989
theorem B280675 : Blo 279826 280675 := bstep (se 1 (by rfl) ⟨210506, by rfl⟩ : syracuseStep 280675 = 421013) B421013
theorem B477299 : Blo 279826 477299 := bstep (se 1 (by rfl) ⟨357974, by rfl⟩ : syracuseStep 477299 = 715949) B715949
theorem B280691 : Blo 279826 280691 := bstep (se 1 (by rfl) ⟨210518, by rfl⟩ : syracuseStep 280691 = 421037) B421037
theorem B280707 : Blo 279826 280707 := bstep (se 1 (by rfl) ⟨210530, by rfl⟩ : syracuseStep 280707 = 421061) B421061
theorem B280723 : Blo 279826 280723 := bstep (se 1 (by rfl) ⟨210542, by rfl⟩ : syracuseStep 280723 = 421085) B421085
theorem B280739 : Blo 279826 280739 := bstep (se 1 (by rfl) ⟨210554, by rfl⟩ : syracuseStep 280739 = 421109) B421109
theorem B280755 : Blo 279826 280755 := bstep (se 1 (by rfl) ⟨210566, by rfl⟩ : syracuseStep 280755 = 421133) B421133
theorem B280771 : Blo 279826 280771 := bstep (se 1 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 280771 = 421157) B421157
theorem B280787 : Blo 279826 280787 := bstep (se 1 (by rfl) ⟨210590, by rfl⟩ : syracuseStep 280787 = 421181) B421181
theorem B280803 : Blo 279826 280803 := bstep (se 1 (by rfl) ⟨210602, by rfl⟩ : syracuseStep 280803 = 421205) B421205
theorem B477427 : Blo 279826 477427 := bstep (se 1 (by rfl) ⟨358070, by rfl⟩ : syracuseStep 477427 = 716141) B716141
theorem B280819 : Blo 279826 280819 := bstep (se 1 (by rfl) ⟨210614, by rfl⟩ : syracuseStep 280819 = 421229) B421229
theorem B280835 : Blo 279826 280835 := bstep (se 1 (by rfl) ⟨210626, by rfl⟩ : syracuseStep 280835 = 421253) B421253
theorem B280851 : Blo 279826 280851 := bstep (se 1 (by rfl) ⟨210638, by rfl⟩ : syracuseStep 280851 = 421277) B421277
theorem B280867 : Blo 279826 280867 := bstep (se 1 (by rfl) ⟨210650, by rfl⟩ : syracuseStep 280867 = 421301) B421301
theorem B1624369 : Blo 279826 1624369 := bstep (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) B1218277
theorem B280883 : Blo 279826 280883 := bstep (se 1 (by rfl) ⟨210662, by rfl⟩ : syracuseStep 280883 = 421325) B421325
theorem B280899 : Blo 279826 280899 := bstep (se 1 (by rfl) ⟨210674, by rfl⟩ : syracuseStep 280899 = 421349) B421349
theorem B280915 : Blo 279826 280915 := bstep (se 1 (by rfl) ⟨210686, by rfl⟩ : syracuseStep 280915 = 421373) B421373
theorem B280931 : Blo 279826 280931 := bstep (se 1 (by rfl) ⟨210698, by rfl⟩ : syracuseStep 280931 = 421397) B421397
theorem B1067363 : Blo 279826 1067363 := bstep (se 1 (by rfl) ⟨800522, by rfl⟩ : syracuseStep 1067363 = 1601045) B1601045
theorem B1067377 : Blo 279826 1067377 := bstep (se 2 (by rfl) ⟨400266, by rfl⟩ : syracuseStep 1067377 = 800533) B800533
theorem B280947 : Blo 279826 280947 := bstep (se 1 (by rfl) ⟨210710, by rfl⟩ : syracuseStep 280947 = 421421) B421421
theorem B477569 : Blo 279826 477569 := bstep (se 2 (by rfl) ⟨179088, by rfl⟩ : syracuseStep 477569 = 358177) B358177
theorem B280963 : Blo 279826 280963 := bstep (se 1 (by rfl) ⟨210722, by rfl⟩ : syracuseStep 280963 = 421445) B421445
theorem B805261 : Blo 279826 805261 := bstep (se 3 (by rfl) ⟨150986, by rfl⟩ : syracuseStep 805261 = 301973) B301973
theorem B280979 : Blo 279826 280979 := bstep (se 1 (by rfl) ⟨210734, by rfl⟩ : syracuseStep 280979 = 421469) B421469
theorem B280995 : Blo 279826 280995 := bstep (se 1 (by rfl) ⟨210746, by rfl⟩ : syracuseStep 280995 = 421493) B421493
theorem B281011 : Blo 279826 281011 := bstep (se 1 (by rfl) ⟨210758, by rfl⟩ : syracuseStep 281011 = 421517) B421517
theorem B281027 : Blo 279826 281027 := bstep (se 1 (by rfl) ⟨210770, by rfl⟩ : syracuseStep 281027 = 421541) B421541
theorem B281043 : Blo 279826 281043 := bstep (se 1 (by rfl) ⟨210782, by rfl⟩ : syracuseStep 281043 = 421565) B421565
theorem B281059 : Blo 279826 281059 := bstep (se 1 (by rfl) ⟨210794, by rfl⟩ : syracuseStep 281059 = 421589) B421589
theorem B281075 : Blo 279826 281075 := bstep (se 1 (by rfl) ⟨210806, by rfl⟩ : syracuseStep 281075 = 421613) B421613
theorem B477697 : Blo 279826 477697 := bstep (se 2 (by rfl) ⟨179136, by rfl⟩ : syracuseStep 477697 = 358273) B358273
theorem B281091 : Blo 279826 281091 := bstep (se 1 (by rfl) ⟨210818, by rfl⟩ : syracuseStep 281091 = 421637) B421637
theorem B281107 : Blo 279826 281107 := bstep (se 1 (by rfl) ⟨210830, by rfl⟩ : syracuseStep 281107 = 421661) B421661
theorem B281123 : Blo 279826 281123 := bstep (se 1 (by rfl) ⟨210842, by rfl⟩ : syracuseStep 281123 = 421685) B421685
theorem B477731 : Blo 279826 477731 := bstep (se 1 (by rfl) ⟨358298, by rfl⟩ : syracuseStep 477731 = 716597) B716597
theorem B281139 : Blo 279826 281139 := bstep (se 1 (by rfl) ⟨210854, by rfl⟩ : syracuseStep 281139 = 421709) B421709
theorem B281155 : Blo 279826 281155 := bstep (se 1 (by rfl) ⟨210866, by rfl⟩ : syracuseStep 281155 = 421733) B421733
theorem B281171 : Blo 279826 281171 := bstep (se 1 (by rfl) ⟨210878, by rfl⟩ : syracuseStep 281171 = 421757) B421757
theorem B281187 : Blo 279826 281187 := bstep (se 1 (by rfl) ⟨210890, by rfl⟩ : syracuseStep 281187 = 421781) B421781
theorem B281203 : Blo 279826 281203 := bstep (se 1 (by rfl) ⟨210902, by rfl⟩ : syracuseStep 281203 = 421805) B421805
theorem B281219 : Blo 279826 281219 := bstep (se 1 (by rfl) ⟨210914, by rfl⟩ : syracuseStep 281219 = 421829) B421829
theorem B281235 : Blo 279826 281235 := bstep (se 1 (by rfl) ⟨210926, by rfl⟩ : syracuseStep 281235 = 421853) B421853
theorem B281251 : Blo 279826 281251 := bstep (se 1 (by rfl) ⟨210938, by rfl⟩ : syracuseStep 281251 = 421877) B421877
theorem B477859 : Blo 279826 477859 := bstep (se 1 (by rfl) ⟨358394, by rfl⟩ : syracuseStep 477859 = 716789) B716789
theorem B281267 : Blo 279826 281267 := bstep (se 1 (by rfl) ⟨210950, by rfl⟩ : syracuseStep 281267 = 421901) B421901
theorem B281283 : Blo 279826 281283 := bstep (se 1 (by rfl) ⟨210962, by rfl⟩ : syracuseStep 281283 = 421925) B421925
theorem B281299 : Blo 279826 281299 := bstep (se 1 (by rfl) ⟨210974, by rfl⟩ : syracuseStep 281299 = 421949) B421949
theorem B281315 : Blo 279826 281315 := bstep (se 1 (by rfl) ⟨210986, by rfl⟩ : syracuseStep 281315 = 421973) B421973
theorem B2149091 : Blo 279826 2149091 := bstep (se 1 (by rfl) ⟨1611818, by rfl⟩ : syracuseStep 2149091 = 3223637) B3223637
theorem B281331 : Blo 279826 281331 := bstep (se 1 (by rfl) ⟨210998, by rfl⟩ : syracuseStep 281331 = 421997) B421997
theorem B281347 : Blo 279826 281347 := bstep (se 1 (by rfl) ⟨211010, by rfl⟩ : syracuseStep 281347 = 422021) B422021
theorem B281363 : Blo 279826 281363 := bstep (se 1 (by rfl) ⟨211022, by rfl⟩ : syracuseStep 281363 = 422045) B422045
theorem B412435 : Blo 279826 412435 := bstep (se 1 (by rfl) ⟨309326, by rfl⟩ : syracuseStep 412435 = 618653) B618653
theorem B281379 : Blo 279826 281379 := bstep (se 1 (by rfl) ⟨211034, by rfl⟩ : syracuseStep 281379 = 422069) B422069
theorem B478001 : Blo 279826 478001 := bstep (se 2 (by rfl) ⟨179250, by rfl⟩ : syracuseStep 478001 = 358501) B358501
theorem B281395 : Blo 279826 281395 := bstep (se 1 (by rfl) ⟨211046, by rfl⟩ : syracuseStep 281395 = 422093) B422093
theorem B281411 : Blo 279826 281411 := bstep (se 1 (by rfl) ⟨211058, by rfl⟩ : syracuseStep 281411 = 422117) B422117
theorem B281427 : Blo 279826 281427 := bstep (se 1 (by rfl) ⟨211070, by rfl⟩ : syracuseStep 281427 = 422141) B422141
theorem B281443 : Blo 279826 281443 := bstep (se 1 (by rfl) ⟨211082, by rfl⟩ : syracuseStep 281443 = 422165) B422165
theorem B281459 : Blo 279826 281459 := bstep (se 1 (by rfl) ⟨211094, by rfl⟩ : syracuseStep 281459 = 422189) B422189
theorem B281475 : Blo 279826 281475 := bstep (se 1 (by rfl) ⟨211106, by rfl⟩ : syracuseStep 281475 = 422213) B422213
theorem B281491 : Blo 279826 281491 := bstep (se 1 (by rfl) ⟨211118, by rfl⟩ : syracuseStep 281491 = 422237) B422237
theorem B379811 : Blo 279826 379811 := bstep (se 1 (by rfl) ⟨284858, by rfl⟩ : syracuseStep 379811 = 569717) B569717
theorem B281507 : Blo 279826 281507 := bstep (se 1 (by rfl) ⟨211130, by rfl⟩ : syracuseStep 281507 = 422261) B422261
theorem B478129 : Blo 279826 478129 := bstep (se 2 (by rfl) ⟨179298, by rfl⟩ : syracuseStep 478129 = 358597) B358597
theorem B281523 : Blo 279826 281523 := bstep (se 1 (by rfl) ⟨211142, by rfl⟩ : syracuseStep 281523 = 422285) B422285
theorem B281539 : Blo 279826 281539 := bstep (se 1 (by rfl) ⟨211154, by rfl⟩ : syracuseStep 281539 = 422309) B422309
theorem B281555 : Blo 279826 281555 := bstep (se 1 (by rfl) ⟨211166, by rfl⟩ : syracuseStep 281555 = 422333) B422333
theorem B478163 : Blo 279826 478163 := bstep (se 1 (by rfl) ⟨358622, by rfl⟩ : syracuseStep 478163 = 717245) B717245
theorem B281571 : Blo 279826 281571 := bstep (se 1 (by rfl) ⟨211178, by rfl⟩ : syracuseStep 281571 = 422357) B422357
theorem B281587 : Blo 279826 281587 := bstep (se 1 (by rfl) ⟨211190, by rfl⟩ : syracuseStep 281587 = 422381) B422381
theorem B281603 : Blo 279826 281603 := bstep (se 1 (by rfl) ⟨211202, by rfl⟩ : syracuseStep 281603 = 422405) B422405
theorem B281619 : Blo 279826 281619 := bstep (se 1 (by rfl) ⟨211214, by rfl⟩ : syracuseStep 281619 = 422429) B422429
theorem B1428515 : Blo 279826 1428515 := bstep (se 1 (by rfl) ⟨1071386, by rfl⟩ : syracuseStep 1428515 = 2142773) B2142773
theorem B281635 : Blo 279826 281635 := bstep (se 1 (by rfl) ⟨211226, by rfl⟩ : syracuseStep 281635 = 422453) B422453
theorem B281651 : Blo 279826 281651 := bstep (se 1 (by rfl) ⟨211238, by rfl⟩ : syracuseStep 281651 = 422477) B422477
theorem B281667 : Blo 279826 281667 := bstep (se 1 (by rfl) ⟨211250, by rfl⟩ : syracuseStep 281667 = 422501) B422501
theorem B281683 : Blo 279826 281683 := bstep (se 1 (by rfl) ⟨211262, by rfl⟩ : syracuseStep 281683 = 422525) B422525
theorem B478291 : Blo 279826 478291 := bstep (se 1 (by rfl) ⟨358718, by rfl⟩ : syracuseStep 478291 = 717437) B717437
theorem B281699 : Blo 279826 281699 := bstep (se 1 (by rfl) ⟨211274, by rfl⟩ : syracuseStep 281699 = 422549) B422549
theorem B281715 : Blo 279826 281715 := bstep (se 1 (by rfl) ⟨211286, by rfl⟩ : syracuseStep 281715 = 422573) B422573
theorem B281731 : Blo 279826 281731 := bstep (se 1 (by rfl) ⟨211298, by rfl⟩ : syracuseStep 281731 = 422597) B422597
theorem B281747 : Blo 279826 281747 := bstep (se 1 (by rfl) ⟨211310, by rfl⟩ : syracuseStep 281747 = 422621) B422621
theorem B281763 : Blo 279826 281763 := bstep (se 1 (by rfl) ⟨211322, by rfl⟩ : syracuseStep 281763 = 422645) B422645
theorem B281779 : Blo 279826 281779 := bstep (se 1 (by rfl) ⟨211334, by rfl⟩ : syracuseStep 281779 = 422669) B422669
theorem B281795 : Blo 279826 281795 := bstep (se 1 (by rfl) ⟨211346, by rfl⟩ : syracuseStep 281795 = 422693) B422693
theorem B281811 : Blo 279826 281811 := bstep (se 1 (by rfl) ⟨211358, by rfl⟩ : syracuseStep 281811 = 422717) B422717
theorem B478433 : Blo 279826 478433 := bstep (se 2 (by rfl) ⟨179412, by rfl⟩ : syracuseStep 478433 = 358825) B358825
theorem B281827 : Blo 279826 281827 := bstep (se 1 (by rfl) ⟨211370, by rfl⟩ : syracuseStep 281827 = 422741) B422741
theorem B281843 : Blo 279826 281843 := bstep (se 1 (by rfl) ⟨211382, by rfl⟩ : syracuseStep 281843 = 422765) B422765
theorem B281859 : Blo 279826 281859 := bstep (se 1 (by rfl) ⟨211394, by rfl⟩ : syracuseStep 281859 = 422789) B422789
theorem B281875 : Blo 279826 281875 := bstep (se 1 (by rfl) ⟨211406, by rfl⟩ : syracuseStep 281875 = 422813) B422813
theorem B281891 : Blo 279826 281891 := bstep (se 1 (by rfl) ⟨211418, by rfl⟩ : syracuseStep 281891 = 422837) B422837
theorem B281907 : Blo 279826 281907 := bstep (se 1 (by rfl) ⟨211430, by rfl⟩ : syracuseStep 281907 = 422861) B422861
theorem B281923 : Blo 279826 281923 := bstep (se 1 (by rfl) ⟨211442, by rfl⟩ : syracuseStep 281923 = 422885) B422885
theorem B281939 : Blo 279826 281939 := bstep (se 1 (by rfl) ⟨211454, by rfl⟩ : syracuseStep 281939 = 422909) B422909
theorem B478561 : Blo 279826 478561 := bstep (se 2 (by rfl) ⟨179460, by rfl⟩ : syracuseStep 478561 = 358921) B358921
theorem B281955 : Blo 279826 281955 := bstep (se 1 (by rfl) ⟨211466, by rfl⟩ : syracuseStep 281955 = 422933) B422933
theorem B904547 : Blo 279826 904547 := bstep (se 1 (by rfl) ⟨678410, by rfl⟩ : syracuseStep 904547 = 1356821) B1356821
theorem B511331 : Blo 279826 511331 := bstep (se 1 (by rfl) ⟨383498, by rfl⟩ : syracuseStep 511331 = 766997) B766997
theorem B281971 : Blo 279826 281971 := bstep (se 1 (by rfl) ⟨211478, by rfl⟩ : syracuseStep 281971 = 422957) B422957
theorem B576899 : Blo 279826 576899 := bstep (se 1 (by rfl) ⟨432674, by rfl⟩ : syracuseStep 576899 = 865349) B865349
theorem B281987 : Blo 279826 281987 := bstep (se 1 (by rfl) ⟨211490, by rfl⟩ : syracuseStep 281987 = 422981) B422981
theorem B478595 : Blo 279826 478595 := bstep (se 1 (by rfl) ⟨358946, by rfl⟩ : syracuseStep 478595 = 717893) B717893
theorem B282003 : Blo 279826 282003 := bstep (se 1 (by rfl) ⟨211502, by rfl⟩ : syracuseStep 282003 = 423005) B423005
theorem B282019 : Blo 279826 282019 := bstep (se 1 (by rfl) ⟨211514, by rfl⟩ : syracuseStep 282019 = 423029) B423029
theorem B282035 : Blo 279826 282035 := bstep (se 1 (by rfl) ⟨211526, by rfl⟩ : syracuseStep 282035 = 423053) B423053
theorem B282051 : Blo 279826 282051 := bstep (se 1 (by rfl) ⟨211538, by rfl⟩ : syracuseStep 282051 = 423077) B423077
theorem B282067 : Blo 279826 282067 := bstep (se 1 (by rfl) ⟨211550, by rfl⟩ : syracuseStep 282067 = 423101) B423101
theorem B314851 : Blo 279826 314851 := bstep (se 1 (by rfl) ⟨236138, by rfl⟩ : syracuseStep 314851 = 472277) B472277
theorem B282083 : Blo 279826 282083 := bstep (se 1 (by rfl) ⟨211562, by rfl⟩ : syracuseStep 282083 = 423125) B423125
theorem B282099 : Blo 279826 282099 := bstep (se 1 (by rfl) ⟨211574, by rfl⟩ : syracuseStep 282099 = 423149) B423149
theorem B282115 : Blo 279826 282115 := bstep (se 1 (by rfl) ⟨211586, by rfl⟩ : syracuseStep 282115 = 423173) B423173
theorem B478723 : Blo 279826 478723 := bstep (se 1 (by rfl) ⟨359042, by rfl⟩ : syracuseStep 478723 = 718085) B718085
theorem B3919373 : Blo 279826 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B282131 : Blo 279826 282131 := bstep (se 1 (by rfl) ⟨211598, by rfl⟩ : syracuseStep 282131 = 423197) B423197
theorem B282147 : Blo 279826 282147 := bstep (se 1 (by rfl) ⟨211610, by rfl⟩ : syracuseStep 282147 = 423221) B423221
theorem B282163 : Blo 279826 282163 := bstep (se 1 (by rfl) ⟨211622, by rfl⟩ : syracuseStep 282163 = 423245) B423245
theorem B577091 : Blo 279826 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B282179 : Blo 279826 282179 := bstep (se 1 (by rfl) ⟨211634, by rfl⟩ : syracuseStep 282179 = 423269) B423269
theorem B282195 : Blo 279826 282195 := bstep (se 1 (by rfl) ⟨211646, by rfl⟩ : syracuseStep 282195 = 423293) B423293
theorem B282211 : Blo 279826 282211 := bstep (se 1 (by rfl) ⟨211658, by rfl⟩ : syracuseStep 282211 = 423317) B423317
theorem B314995 : Blo 279826 314995 := bstep (se 1 (by rfl) ⟨236246, by rfl⟩ : syracuseStep 314995 = 472493) B472493
theorem B282227 : Blo 279826 282227 := bstep (se 1 (by rfl) ⟨211670, by rfl⟩ : syracuseStep 282227 = 423341) B423341
theorem B282243 : Blo 279826 282243 := bstep (se 1 (by rfl) ⟨211682, by rfl⟩ : syracuseStep 282243 = 423365) B423365
theorem B478865 : Blo 279826 478865 := bstep (se 2 (by rfl) ⟨179574, by rfl⟩ : syracuseStep 478865 = 359149) B359149
theorem B282259 : Blo 279826 282259 := bstep (se 1 (by rfl) ⟨211694, by rfl⟩ : syracuseStep 282259 = 423389) B423389
theorem B282275 : Blo 279826 282275 := bstep (se 1 (by rfl) ⟨211706, by rfl⟩ : syracuseStep 282275 = 423413) B423413
theorem B282291 : Blo 279826 282291 := bstep (se 1 (by rfl) ⟨211718, by rfl⟩ : syracuseStep 282291 = 423437) B423437
theorem B282307 : Blo 279826 282307 := bstep (se 1 (by rfl) ⟨211730, by rfl⟩ : syracuseStep 282307 = 423461) B423461
theorem B282323 : Blo 279826 282323 := bstep (se 1 (by rfl) ⟨211742, by rfl⟩ : syracuseStep 282323 = 423485) B423485
theorem B1199843 : Blo 279826 1199843 := bstep (se 1 (by rfl) ⟨899882, by rfl⟩ : syracuseStep 1199843 = 1799765) B1799765
theorem B282339 : Blo 279826 282339 := bstep (se 1 (by rfl) ⟨211754, by rfl⟩ : syracuseStep 282339 = 423509) B423509
theorem B282355 : Blo 279826 282355 := bstep (se 1 (by rfl) ⟨211766, by rfl⟩ : syracuseStep 282355 = 423533) B423533
theorem B315139 : Blo 279826 315139 := bstep (se 1 (by rfl) ⟨236354, by rfl⟩ : syracuseStep 315139 = 472709) B472709
theorem B282371 : Blo 279826 282371 := bstep (se 1 (by rfl) ⟨211778, by rfl⟩ : syracuseStep 282371 = 423557) B423557
theorem B282387 : Blo 279826 282387 := bstep (se 1 (by rfl) ⟨211790, by rfl⟩ : syracuseStep 282387 = 423581) B423581
theorem B1068835 : Blo 279826 1068835 := bstep (se 1 (by rfl) ⟨801626, by rfl⟩ : syracuseStep 1068835 = 1603253) B1603253
theorem B282403 : Blo 279826 282403 := bstep (se 1 (by rfl) ⟨211802, by rfl⟩ : syracuseStep 282403 = 423605) B423605
theorem B282419 : Blo 279826 282419 := bstep (se 1 (by rfl) ⟨211814, by rfl⟩ : syracuseStep 282419 = 423629) B423629
theorem B282435 : Blo 279826 282435 := bstep (se 1 (by rfl) ⟨211826, by rfl⟩ : syracuseStep 282435 = 423653) B423653
theorem B1429325 : Blo 279826 1429325 := bstep (se 3 (by rfl) ⟨267998, by rfl⟩ : syracuseStep 1429325 = 535997) B535997
theorem B282451 : Blo 279826 282451 := bstep (se 1 (by rfl) ⟨211838, by rfl⟩ : syracuseStep 282451 = 423677) B423677
theorem B282467 : Blo 279826 282467 := bstep (se 1 (by rfl) ⟨211850, by rfl⟩ : syracuseStep 282467 = 423701) B423701
theorem B1920881 : Blo 279826 1920881 := bstep (se 2 (by rfl) ⟨720330, by rfl⟩ : syracuseStep 1920881 = 1440661) B1440661
theorem B282483 : Blo 279826 282483 := bstep (se 1 (by rfl) ⟨211862, by rfl⟩ : syracuseStep 282483 = 423725) B423725
theorem B282499 : Blo 279826 282499 := bstep (se 1 (by rfl) ⟨211874, by rfl⟩ : syracuseStep 282499 = 423749) B423749
theorem B708497 : Blo 279826 708497 := bstep (se 2 (by rfl) ⟨265686, by rfl⟩ : syracuseStep 708497 = 531373) B531373
theorem B315283 : Blo 279826 315283 := bstep (se 1 (by rfl) ⟨236462, by rfl⟩ : syracuseStep 315283 = 472925) B472925
theorem B282515 : Blo 279826 282515 := bstep (se 1 (by rfl) ⟨211886, by rfl⟩ : syracuseStep 282515 = 423773) B423773
theorem B282531 : Blo 279826 282531 := bstep (se 1 (by rfl) ⟨211898, by rfl⟩ : syracuseStep 282531 = 423797) B423797
theorem B282547 : Blo 279826 282547 := bstep (se 1 (by rfl) ⟨211910, by rfl⟩ : syracuseStep 282547 = 423821) B423821
theorem B708547 : Blo 279826 708547 := bstep (se 1 (by rfl) ⟨531410, by rfl⟩ : syracuseStep 708547 = 1062821) B1062821
theorem B282563 : Blo 279826 282563 := bstep (se 1 (by rfl) ⟨211922, by rfl⟩ : syracuseStep 282563 = 423845) B423845
theorem B282579 : Blo 279826 282579 := bstep (se 1 (by rfl) ⟨211934, by rfl⟩ : syracuseStep 282579 = 423869) B423869
theorem B282595 : Blo 279826 282595 := bstep (se 1 (by rfl) ⟨211946, by rfl⟩ : syracuseStep 282595 = 423893) B423893
theorem B282611 : Blo 279826 282611 := bstep (se 1 (by rfl) ⟨211958, by rfl⟩ : syracuseStep 282611 = 423917) B423917
theorem B282627 : Blo 279826 282627 := bstep (se 1 (by rfl) ⟨211970, by rfl⟩ : syracuseStep 282627 = 423941) B423941
theorem B282643 : Blo 279826 282643 := bstep (se 1 (by rfl) ⟨211982, by rfl⟩ : syracuseStep 282643 = 423965) B423965
theorem B315427 : Blo 279826 315427 := bstep (se 1 (by rfl) ⟨236570, by rfl⟩ : syracuseStep 315427 = 473141) B473141
theorem B282659 : Blo 279826 282659 := bstep (se 1 (by rfl) ⟨211994, by rfl⟩ : syracuseStep 282659 = 423989) B423989
theorem B282675 : Blo 279826 282675 := bstep (se 1 (by rfl) ⟨212006, by rfl⟩ : syracuseStep 282675 = 424013) B424013
theorem B282691 : Blo 279826 282691 := bstep (se 1 (by rfl) ⟨212018, by rfl⟩ : syracuseStep 282691 = 424037) B424037
theorem B708689 : Blo 279826 708689 := bstep (se 2 (by rfl) ⟨265758, by rfl⟩ : syracuseStep 708689 = 531517) B531517
theorem B806993 : Blo 279826 806993 := bstep (se 2 (by rfl) ⟨302622, by rfl⟩ : syracuseStep 806993 = 605245) B605245
theorem B282707 : Blo 279826 282707 := bstep (se 1 (by rfl) ⟨212030, by rfl⟩ : syracuseStep 282707 = 424061) B424061
theorem B282723 : Blo 279826 282723 := bstep (se 1 (by rfl) ⟨212042, by rfl⟩ : syracuseStep 282723 = 424085) B424085
theorem B282739 : Blo 279826 282739 := bstep (se 1 (by rfl) ⟨212054, by rfl⟩ : syracuseStep 282739 = 424109) B424109
theorem B282755 : Blo 279826 282755 := bstep (se 1 (by rfl) ⟨212066, by rfl⟩ : syracuseStep 282755 = 424133) B424133
theorem B282771 : Blo 279826 282771 := bstep (se 1 (by rfl) ⟨212078, by rfl⟩ : syracuseStep 282771 = 424157) B424157
theorem B282787 : Blo 279826 282787 := bstep (se 1 (by rfl) ⟨212090, by rfl⟩ : syracuseStep 282787 = 424181) B424181
theorem B315571 : Blo 279826 315571 := bstep (se 1 (by rfl) ⟨236678, by rfl⟩ : syracuseStep 315571 = 473357) B473357
theorem B282803 : Blo 279826 282803 := bstep (se 1 (by rfl) ⟨212102, by rfl⟩ : syracuseStep 282803 = 424205) B424205
theorem B282819 : Blo 279826 282819 := bstep (se 1 (by rfl) ⟨212114, by rfl⟩ : syracuseStep 282819 = 424229) B424229
theorem B282835 : Blo 279826 282835 := bstep (se 1 (by rfl) ⟨212126, by rfl⟩ : syracuseStep 282835 = 424253) B424253
theorem B282851 : Blo 279826 282851 := bstep (se 1 (by rfl) ⟨212138, by rfl⟩ : syracuseStep 282851 = 424277) B424277
theorem B282867 : Blo 279826 282867 := bstep (se 1 (by rfl) ⟨212150, by rfl⟩ : syracuseStep 282867 = 424301) B424301
theorem B282883 : Blo 279826 282883 := bstep (se 1 (by rfl) ⟨212162, by rfl⟩ : syracuseStep 282883 = 424325) B424325
theorem B807185 : Blo 279826 807185 := bstep (se 2 (by rfl) ⟨302694, by rfl⟩ : syracuseStep 807185 = 605389) B605389
theorem B282899 : Blo 279826 282899 := bstep (se 1 (by rfl) ⟨212174, by rfl⟩ : syracuseStep 282899 = 424349) B424349
theorem B282915 : Blo 279826 282915 := bstep (se 1 (by rfl) ⟨212186, by rfl⟩ : syracuseStep 282915 = 424373) B424373
theorem B905521 : Blo 279826 905521 := bstep (se 2 (by rfl) ⟨339570, by rfl⟩ : syracuseStep 905521 = 679141) B679141
theorem B282931 : Blo 279826 282931 := bstep (se 1 (by rfl) ⟨212198, by rfl⟩ : syracuseStep 282931 = 424397) B424397
theorem B315715 : Blo 279826 315715 := bstep (se 1 (by rfl) ⟨236786, by rfl⟩ : syracuseStep 315715 = 473573) B473573
theorem B676163 : Blo 279826 676163 := bstep (se 1 (by rfl) ⟨507122, by rfl⟩ : syracuseStep 676163 = 1014245) B1014245
theorem B282947 : Blo 279826 282947 := bstep (se 1 (by rfl) ⟨212210, by rfl⟩ : syracuseStep 282947 = 424421) B424421
theorem B282963 : Blo 279826 282963 := bstep (se 1 (by rfl) ⟨212222, by rfl⟩ : syracuseStep 282963 = 424445) B424445
theorem B282979 : Blo 279826 282979 := bstep (se 1 (by rfl) ⟨212234, by rfl⟩ : syracuseStep 282979 = 424469) B424469
theorem B282995 : Blo 279826 282995 := bstep (se 1 (by rfl) ⟨212246, by rfl⟩ : syracuseStep 282995 = 424493) B424493
theorem B283011 : Blo 279826 283011 := bstep (se 1 (by rfl) ⟨212258, by rfl⟩ : syracuseStep 283011 = 424517) B424517
theorem B283027 : Blo 279826 283027 := bstep (se 1 (by rfl) ⟨212270, by rfl⟩ : syracuseStep 283027 = 424541) B424541
theorem B676259 : Blo 279826 676259 := bstep (se 1 (by rfl) ⟨507194, by rfl⟩ : syracuseStep 676259 = 1014389) B1014389
theorem B283043 : Blo 279826 283043 := bstep (se 1 (by rfl) ⟨212282, by rfl⟩ : syracuseStep 283043 = 424565) B424565
theorem B283059 : Blo 279826 283059 := bstep (se 1 (by rfl) ⟨212294, by rfl⟩ : syracuseStep 283059 = 424589) B424589
theorem B643523 : Blo 279826 643523 := bstep (se 1 (by rfl) ⟨482642, by rfl⟩ : syracuseStep 643523 = 965285) B965285
theorem B283075 : Blo 279826 283075 := bstep (se 1 (by rfl) ⟨212306, by rfl⟩ : syracuseStep 283075 = 424613) B424613
theorem B315859 : Blo 279826 315859 := bstep (se 1 (by rfl) ⟨236894, by rfl⟩ : syracuseStep 315859 = 473789) B473789
theorem B283091 : Blo 279826 283091 := bstep (se 1 (by rfl) ⟨212318, by rfl⟩ : syracuseStep 283091 = 424637) B424637
theorem B283107 : Blo 279826 283107 := bstep (se 1 (by rfl) ⟨212330, by rfl⟩ : syracuseStep 283107 = 424661) B424661
theorem B283123 : Blo 279826 283123 := bstep (se 1 (by rfl) ⟨212342, by rfl⟩ : syracuseStep 283123 = 424685) B424685
theorem B283139 : Blo 279826 283139 := bstep (se 1 (by rfl) ⟨212354, by rfl⟩ : syracuseStep 283139 = 424709) B424709
theorem B283155 : Blo 279826 283155 := bstep (se 1 (by rfl) ⟨212366, by rfl⟩ : syracuseStep 283155 = 424733) B424733
theorem B283171 : Blo 279826 283171 := bstep (se 1 (by rfl) ⟨212378, by rfl⟩ : syracuseStep 283171 = 424757) B424757
theorem B283187 : Blo 279826 283187 := bstep (se 1 (by rfl) ⟨212390, by rfl⟩ : syracuseStep 283187 = 424781) B424781
theorem B283203 : Blo 279826 283203 := bstep (se 1 (by rfl) ⟨212402, by rfl⟩ : syracuseStep 283203 = 424805) B424805
theorem B283219 : Blo 279826 283219 := bstep (se 1 (by rfl) ⟨212414, by rfl⟩ : syracuseStep 283219 = 424829) B424829
theorem B316003 : Blo 279826 316003 := bstep (se 1 (by rfl) ⟨237002, by rfl⟩ : syracuseStep 316003 = 474005) B474005
theorem B283235 : Blo 279826 283235 := bstep (se 1 (by rfl) ⟨212426, by rfl⟩ : syracuseStep 283235 = 424853) B424853
theorem B283251 : Blo 279826 283251 := bstep (se 1 (by rfl) ⟨212438, by rfl⟩ : syracuseStep 283251 = 424877) B424877
theorem B283267 : Blo 279826 283267 := bstep (se 1 (by rfl) ⟨212450, by rfl⟩ : syracuseStep 283267 = 424901) B424901
theorem B283283 : Blo 279826 283283 := bstep (se 1 (by rfl) ⟨212462, by rfl⟩ : syracuseStep 283283 = 424925) B424925
theorem B283299 : Blo 279826 283299 := bstep (se 1 (by rfl) ⟨212474, by rfl⟩ : syracuseStep 283299 = 424949) B424949
theorem B283315 : Blo 279826 283315 := bstep (se 1 (by rfl) ⟨212486, by rfl⟩ : syracuseStep 283315 = 424973) B424973
theorem B283331 : Blo 279826 283331 := bstep (se 1 (by rfl) ⟨212498, by rfl⟩ : syracuseStep 283331 = 424997) B424997
theorem B283347 : Blo 279826 283347 := bstep (se 1 (by rfl) ⟨212510, by rfl⟩ : syracuseStep 283347 = 425021) B425021
theorem B283363 : Blo 279826 283363 := bstep (se 1 (by rfl) ⟨212522, by rfl⟩ : syracuseStep 283363 = 425045) B425045
theorem B316147 : Blo 279826 316147 := bstep (se 1 (by rfl) ⟨237110, by rfl⟩ : syracuseStep 316147 = 474221) B474221
theorem B283379 : Blo 279826 283379 := bstep (se 1 (by rfl) ⟨212534, by rfl⟩ : syracuseStep 283379 = 425069) B425069
theorem B283395 : Blo 279826 283395 := bstep (se 1 (by rfl) ⟨212546, by rfl⟩ : syracuseStep 283395 = 425093) B425093
theorem B283411 : Blo 279826 283411 := bstep (se 1 (by rfl) ⟨212558, by rfl⟩ : syracuseStep 283411 = 425117) B425117
theorem B283427 : Blo 279826 283427 := bstep (se 1 (by rfl) ⟨212570, by rfl⟩ : syracuseStep 283427 = 425141) B425141
theorem B283443 : Blo 279826 283443 := bstep (se 1 (by rfl) ⟨212582, by rfl⟩ : syracuseStep 283443 = 425165) B425165
theorem B3068725 : Blo 279826 3068725 := bstep (se 5 (by rfl) ⟨143846, by rfl⟩ : syracuseStep 3068725 = 287693) B287693
theorem B4117301 : Blo 279826 4117301 := bstep (se 5 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 4117301 = 385997) B385997
theorem B283459 : Blo 279826 283459 := bstep (se 1 (by rfl) ⟨212594, by rfl⟩ : syracuseStep 283459 = 425189) B425189
theorem B283475 : Blo 279826 283475 := bstep (se 1 (by rfl) ⟨212606, by rfl⟩ : syracuseStep 283475 = 425213) B425213
theorem B283491 : Blo 279826 283491 := bstep (se 1 (by rfl) ⟨212618, by rfl⟩ : syracuseStep 283491 = 425237) B425237
theorem B283507 : Blo 279826 283507 := bstep (se 1 (by rfl) ⟨212630, by rfl⟩ : syracuseStep 283507 = 425261) B425261
theorem B316291 : Blo 279826 316291 := bstep (se 1 (by rfl) ⟨237218, by rfl⟩ : syracuseStep 316291 = 474437) B474437
theorem B283523 : Blo 279826 283523 := bstep (se 1 (by rfl) ⟨212642, by rfl⟩ : syracuseStep 283523 = 425285) B425285
theorem B283539 : Blo 279826 283539 := bstep (se 1 (by rfl) ⟨212654, by rfl⟩ : syracuseStep 283539 = 425309) B425309
theorem B283555 : Blo 279826 283555 := bstep (se 1 (by rfl) ⟨212666, by rfl⟩ : syracuseStep 283555 = 425333) B425333
theorem B283571 : Blo 279826 283571 := bstep (se 1 (by rfl) ⟨212678, by rfl⟩ : syracuseStep 283571 = 425357) B425357
theorem B283587 : Blo 279826 283587 := bstep (se 1 (by rfl) ⟨212690, by rfl⟩ : syracuseStep 283587 = 425381) B425381
theorem B283603 : Blo 279826 283603 := bstep (se 1 (by rfl) ⟨212702, by rfl⟩ : syracuseStep 283603 = 425405) B425405
theorem B283619 : Blo 279826 283619 := bstep (se 1 (by rfl) ⟨212714, by rfl⟩ : syracuseStep 283619 = 425429) B425429
theorem B283635 : Blo 279826 283635 := bstep (se 1 (by rfl) ⟨212726, by rfl⟩ : syracuseStep 283635 = 425453) B425453
theorem B283651 : Blo 279826 283651 := bstep (se 1 (by rfl) ⟨212738, by rfl⟩ : syracuseStep 283651 = 425477) B425477
theorem B316435 : Blo 279826 316435 := bstep (se 1 (by rfl) ⟨237326, by rfl⟩ : syracuseStep 316435 = 474653) B474653
theorem B283667 : Blo 279826 283667 := bstep (se 1 (by rfl) ⟨212750, by rfl⟩ : syracuseStep 283667 = 425501) B425501
theorem B283683 : Blo 279826 283683 := bstep (se 1 (by rfl) ⟨212762, by rfl⟩ : syracuseStep 283683 = 425525) B425525
theorem B709681 : Blo 279826 709681 := bstep (se 2 (by rfl) ⟨266130, by rfl⟩ : syracuseStep 709681 = 532261) B532261
theorem B283699 : Blo 279826 283699 := bstep (se 1 (by rfl) ⟨212774, by rfl⟩ : syracuseStep 283699 = 425549) B425549
theorem B283715 : Blo 279826 283715 := bstep (se 1 (by rfl) ⟨212786, by rfl⟩ : syracuseStep 283715 = 425573) B425573
theorem B283731 : Blo 279826 283731 := bstep (se 1 (by rfl) ⟨212798, by rfl⟩ : syracuseStep 283731 = 425597) B425597
theorem B283747 : Blo 279826 283747 := bstep (se 1 (by rfl) ⟨212810, by rfl⟩ : syracuseStep 283747 = 425621) B425621
theorem B283763 : Blo 279826 283763 := bstep (se 1 (by rfl) ⟨212822, by rfl⟩ : syracuseStep 283763 = 425645) B425645
theorem B283779 : Blo 279826 283779 := bstep (se 1 (by rfl) ⟨212834, by rfl⟩ : syracuseStep 283779 = 425669) B425669
theorem B382099 : Blo 279826 382099 := bstep (se 1 (by rfl) ⟨286574, by rfl⟩ : syracuseStep 382099 = 573149) B573149
theorem B283795 : Blo 279826 283795 := bstep (se 1 (by rfl) ⟨212846, by rfl⟩ : syracuseStep 283795 = 425693) B425693
theorem B316579 : Blo 279826 316579 := bstep (se 1 (by rfl) ⟨237434, by rfl⟩ : syracuseStep 316579 = 474869) B474869
theorem B873635 : Blo 279826 873635 := bstep (se 1 (by rfl) ⟨655226, by rfl⟩ : syracuseStep 873635 = 1310453) B1310453
theorem B1496227 : Blo 279826 1496227 := bstep (se 1 (by rfl) ⟨1122170, by rfl⟩ : syracuseStep 1496227 = 2244341) B2244341
theorem B283811 : Blo 279826 283811 := bstep (se 1 (by rfl) ⟨212858, by rfl⟩ : syracuseStep 283811 = 425717) B425717
theorem B677105 : Blo 279826 677105 := bstep (se 2 (by rfl) ⟨253914, by rfl⟩ : syracuseStep 677105 = 507829) B507829
theorem B808177 : Blo 279826 808177 := bstep (se 2 (by rfl) ⟨303066, by rfl⟩ : syracuseStep 808177 = 606133) B606133
theorem B316723 : Blo 279826 316723 := bstep (se 1 (by rfl) ⟨237542, by rfl⟩ : syracuseStep 316723 = 475085) B475085
theorem B3200309 : Blo 279826 3200309 := bstep (se 5 (by rfl) ⟨150014, by rfl⟩ : syracuseStep 3200309 = 300029) B300029
theorem B709955 : Blo 279826 709955 := bstep (se 1 (by rfl) ⟨532466, by rfl⟩ : syracuseStep 709955 = 1064933) B1064933
theorem B316867 : Blo 279826 316867 := bstep (se 1 (by rfl) ⟨237650, by rfl⟩ : syracuseStep 316867 = 475301) B475301
theorem B480755 : Blo 279826 480755 := bstep (se 1 (by rfl) ⟨360566, by rfl⟩ : syracuseStep 480755 = 721133) B721133
theorem B710147 : Blo 279826 710147 := bstep (se 1 (by rfl) ⟨532610, by rfl⟩ : syracuseStep 710147 = 1065221) B1065221
theorem B677393 : Blo 279826 677393 := bstep (se 2 (by rfl) ⟨254022, by rfl⟩ : syracuseStep 677393 = 508045) B508045
theorem B1136177 : Blo 279826 1136177 := bstep (se 2 (by rfl) ⟨426066, by rfl⟩ : syracuseStep 1136177 = 852133) B852133
theorem B317011 : Blo 279826 317011 := bstep (se 1 (by rfl) ⟨237758, by rfl⟩ : syracuseStep 317011 = 475517) B475517
theorem B317155 : Blo 279826 317155 := bstep (se 1 (by rfl) ⟨237866, by rfl⟩ : syracuseStep 317155 = 475733) B475733
theorem B677603 : Blo 279826 677603 := bstep (se 1 (by rfl) ⟨508202, by rfl⟩ : syracuseStep 677603 = 1016405) B1016405
theorem B1595213 : Blo 279826 1595213 := bstep (se 3 (by rfl) ⟨299102, by rfl⟩ : syracuseStep 1595213 = 598205) B598205
theorem B317299 : Blo 279826 317299 := bstep (se 1 (by rfl) ⟨237974, by rfl⟩ : syracuseStep 317299 = 475949) B475949
theorem B1071053 : Blo 279826 1071053 := bstep (se 3 (by rfl) ⟨200822, by rfl⟩ : syracuseStep 1071053 = 401645) B401645
theorem B907213 : Blo 279826 907213 := bstep (se 3 (by rfl) ⟨170102, by rfl⟩ : syracuseStep 907213 = 340205) B340205
theorem B317443 : Blo 279826 317443 := bstep (se 1 (by rfl) ⟨238082, by rfl⟩ : syracuseStep 317443 = 476165) B476165
theorem B776237 : Blo 279826 776237 := bstep (se 3 (by rfl) ⟨145544, by rfl⟩ : syracuseStep 776237 = 291089) B291089
theorem B317587 : Blo 279826 317587 := bstep (se 1 (by rfl) ⟨238190, by rfl⟩ : syracuseStep 317587 = 476381) B476381
theorem B317731 : Blo 279826 317731 := bstep (se 1 (by rfl) ⟨238298, by rfl⟩ : syracuseStep 317731 = 476597) B476597
theorem B4807025 : Blo 279826 4807025 := bstep (se 2 (by rfl) ⟨1802634, by rfl⟩ : syracuseStep 4807025 = 3605269) B3605269
theorem B1628549 : Blo 279826 1628549 := bstep (se 4 (by rfl) ⟨152676, by rfl⟩ : syracuseStep 1628549 = 305353) B305353
theorem B711089 : Blo 279826 711089 := bstep (se 2 (by rfl) ⟨266658, by rfl⟩ : syracuseStep 711089 = 533317) B533317
theorem B317875 : Blo 279826 317875 := bstep (se 1 (by rfl) ⟨238406, by rfl⟩ : syracuseStep 317875 = 476813) B476813
theorem B448993 : Blo 279826 448993 := bstep (se 2 (by rfl) ⟨168372, by rfl⟩ : syracuseStep 448993 = 336745) B336745
theorem B711139 : Blo 279826 711139 := bstep (se 1 (by rfl) ⟨533354, by rfl⟩ : syracuseStep 711139 = 1066709) B1066709
theorem B318019 : Blo 279826 318019 := bstep (se 1 (by rfl) ⟨238514, by rfl⟩ : syracuseStep 318019 = 477029) B477029
theorem B711281 : Blo 279826 711281 := bstep (se 2 (by rfl) ⟨266730, by rfl⟩ : syracuseStep 711281 = 533461) B533461
theorem B383635 : Blo 279826 383635 := bstep (se 1 (by rfl) ⟨287726, by rfl⟩ : syracuseStep 383635 = 575453) B575453
theorem B1432241 : Blo 279826 1432241 := bstep (se 2 (by rfl) ⟨537090, by rfl⟩ : syracuseStep 1432241 = 1074181) B1074181
theorem B318163 : Blo 279826 318163 := bstep (se 1 (by rfl) ⟨238622, by rfl⟩ : syracuseStep 318163 = 477245) B477245
theorem B1596145 : Blo 279826 1596145 := bstep (se 2 (by rfl) ⟨598554, by rfl⟩ : syracuseStep 1596145 = 1197109) B1197109
theorem B285475 : Blo 279826 285475 := bstep (se 1 (by rfl) ⟨214106, by rfl⟩ : syracuseStep 285475 = 428213) B428213
theorem B318307 : Blo 279826 318307 := bstep (se 1 (by rfl) ⟨238730, by rfl⟩ : syracuseStep 318307 = 477461) B477461
theorem B318451 : Blo 279826 318451 := bstep (se 1 (by rfl) ⟨238838, by rfl⟩ : syracuseStep 318451 = 477677) B477677
theorem B318595 : Blo 279826 318595 := bstep (se 1 (by rfl) ⟨238946, by rfl⟩ : syracuseStep 318595 = 477893) B477893
theorem B318739 : Blo 279826 318739 := bstep (se 1 (by rfl) ⟨239054, by rfl⟩ : syracuseStep 318739 = 478109) B478109
theorem B1203569 : Blo 279826 1203569 := bstep (se 2 (by rfl) ⟨451338, by rfl⟩ : syracuseStep 1203569 = 902677) B902677
theorem B318883 : Blo 279826 318883 := bstep (se 1 (by rfl) ⟨239162, by rfl⟩ : syracuseStep 318883 = 478325) B478325
theorem B482849 : Blo 279826 482849 := bstep (se 2 (by rfl) ⟨181068, by rfl⟩ : syracuseStep 482849 = 362137) B362137
theorem B319027 : Blo 279826 319027 := bstep (se 1 (by rfl) ⟨239270, by rfl⟩ : syracuseStep 319027 = 478541) B478541
theorem B712273 : Blo 279826 712273 := bstep (se 2 (by rfl) ⟨267102, by rfl⟩ : syracuseStep 712273 = 534205) B534205
theorem B450211 : Blo 279826 450211 := bstep (se 1 (by rfl) ⟨337658, by rfl⟩ : syracuseStep 450211 = 675317) B675317
theorem B319171 : Blo 279826 319171 := bstep (se 1 (by rfl) ⟨239378, by rfl⟩ : syracuseStep 319171 = 478757) B478757
theorem B908995 : Blo 279826 908995 := bstep (se 1 (by rfl) ⟨681746, by rfl⟩ : syracuseStep 908995 = 1363493) B1363493
theorem B2023181 : Blo 279826 2023181 := bstep (se 3 (by rfl) ⟨379346, by rfl⟩ : syracuseStep 2023181 = 758693) B758693
theorem B679747 : Blo 279826 679747 := bstep (se 1 (by rfl) ⟨509810, by rfl⟩ : syracuseStep 679747 = 1019621) B1019621
theorem B712547 : Blo 279826 712547 := bstep (se 1 (by rfl) ⟨534410, by rfl⟩ : syracuseStep 712547 = 1068821) B1068821
theorem B2154437 : Blo 279826 2154437 := bstep (se 4 (by rfl) ⟨201978, by rfl⟩ : syracuseStep 2154437 = 403957) B403957
theorem B712739 : Blo 279826 712739 := bstep (se 1 (by rfl) ⟨534554, by rfl⟩ : syracuseStep 712739 = 1069109) B1069109
theorem B1433699 : Blo 279826 1433699 := bstep (se 1 (by rfl) ⟨1075274, by rfl⟩ : syracuseStep 1433699 = 2150549) B2150549
theorem B876653 : Blo 279826 876653 := bstep (se 3 (by rfl) ⟨164372, by rfl⟩ : syracuseStep 876653 = 328745) B328745
theorem B647281 : Blo 279826 647281 := bstep (se 2 (by rfl) ⟨242730, by rfl⟩ : syracuseStep 647281 = 485461) B485461
theorem B1532045 : Blo 279826 1532045 := bstep (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) B574517
theorem B1597603 : Blo 279826 1597603 := bstep (se 1 (by rfl) ⟨1198202, by rfl⟩ : syracuseStep 1597603 = 2396405) B2396405
theorem B811363 : Blo 279826 811363 := bstep (se 1 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 811363 = 1217045) B1217045
theorem B450929 : Blo 279826 450929 := bstep (se 2 (by rfl) ⟨169098, by rfl⟩ : syracuseStep 450929 = 338197) B338197
theorem B451217 : Blo 279826 451217 := bstep (se 2 (by rfl) ⟨169206, by rfl⟩ : syracuseStep 451217 = 338413) B338413
theorem B1598129 : Blo 279826 1598129 := bstep (se 2 (by rfl) ⟨599298, by rfl⟩ : syracuseStep 1598129 = 1198597) B1198597
theorem B1073969 : Blo 279826 1073969 := bstep (se 2 (by rfl) ⟨402738, by rfl⟩ : syracuseStep 1073969 = 805477) B805477
theorem B451441 : Blo 279826 451441 := bstep (se 2 (by rfl) ⟨169290, by rfl⟩ : syracuseStep 451441 = 338581) B338581
theorem B1434509 : Blo 279826 1434509 := bstep (se 3 (by rfl) ⟨268970, by rfl⟩ : syracuseStep 1434509 = 537941) B537941
theorem B8119237 : Blo 279826 8119237 := bstep (se 4 (by rfl) ⟨761178, by rfl⟩ : syracuseStep 8119237 = 1522357) B1522357
theorem B713681 : Blo 279826 713681 := bstep (se 2 (by rfl) ⟨267630, by rfl⟩ : syracuseStep 713681 = 535261) B535261
theorem B812035 : Blo 279826 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B713731 : Blo 279826 713731 := bstep (se 1 (by rfl) ⟨535298, by rfl⟩ : syracuseStep 713731 = 1070597) B1070597
theorem B680977 : Blo 279826 680977 := bstep (se 2 (by rfl) ⟨255366, by rfl⟩ : syracuseStep 680977 = 510733) B510733
theorem B713873 : Blo 279826 713873 := bstep (se 2 (by rfl) ⟨267702, by rfl⟩ : syracuseStep 713873 = 535405) B535405
theorem B484579 : Blo 279826 484579 := bstep (se 1 (by rfl) ⟨363434, by rfl⟩ : syracuseStep 484579 = 726869) B726869
theorem B2418275 : Blo 279826 2418275 := bstep (se 1 (by rfl) ⟨1813706, by rfl⟩ : syracuseStep 2418275 = 3627413) B3627413
theorem B321251 : Blo 279826 321251 := bstep (se 1 (by rfl) ⟨240938, by rfl⟩ : syracuseStep 321251 = 481877) B481877
theorem B1206029 : Blo 279826 1206029 := bstep (se 3 (by rfl) ⟨226130, by rfl⟩ : syracuseStep 1206029 = 452261) B452261
theorem B419747 : Blo 279826 419747 := bstep (se 1 (by rfl) ⟨314810, by rfl⟩ : syracuseStep 419747 = 629621) B629621
theorem B419777 : Blo 279826 419777 := bstep (se 2 (by rfl) ⟨157416, by rfl⟩ : syracuseStep 419777 = 314833) B314833
theorem B419795 : Blo 279826 419795 := bstep (se 1 (by rfl) ⟨314846, by rfl⟩ : syracuseStep 419795 = 629693) B629693
theorem B419825 : Blo 279826 419825 := bstep (se 2 (by rfl) ⟨157434, by rfl⟩ : syracuseStep 419825 = 314869) B314869
theorem B419843 : Blo 279826 419843 := bstep (se 1 (by rfl) ⟨314882, by rfl⟩ : syracuseStep 419843 = 629765) B629765
theorem B419873 : Blo 279826 419873 := bstep (se 2 (by rfl) ⟨157452, by rfl⟩ : syracuseStep 419873 = 314905) B314905
theorem B518179 : Blo 279826 518179 := bstep (se 1 (by rfl) ⟨388634, by rfl⟩ : syracuseStep 518179 = 777269) B777269
theorem B419891 : Blo 279826 419891 := bstep (se 1 (by rfl) ⟨314918, by rfl⟩ : syracuseStep 419891 = 629837) B629837
theorem B419921 : Blo 279826 419921 := bstep (se 2 (by rfl) ⟨157470, by rfl⟩ : syracuseStep 419921 = 314941) B314941
theorem B419939 : Blo 279826 419939 := bstep (se 1 (by rfl) ⟨314954, by rfl⟩ : syracuseStep 419939 = 629909) B629909
theorem B1599587 : Blo 279826 1599587 := bstep (se 1 (by rfl) ⟨1199690, by rfl⟩ : syracuseStep 1599587 = 2399381) B2399381
theorem B714865 : Blo 279826 714865 := bstep (se 2 (by rfl) ⟨268074, by rfl⟩ : syracuseStep 714865 = 536149) B536149
theorem B419969 : Blo 279826 419969 := bstep (se 2 (by rfl) ⟨157488, by rfl⟩ : syracuseStep 419969 = 314977) B314977
theorem B419987 : Blo 279826 419987 := bstep (se 1 (by rfl) ⟨314990, by rfl⟩ : syracuseStep 419987 = 629981) B629981
theorem B354451 : Blo 279826 354451 := bstep (se 1 (by rfl) ⟨265838, by rfl⟩ : syracuseStep 354451 = 531677) B531677
theorem B420017 : Blo 279826 420017 := bstep (se 2 (by rfl) ⟨157506, by rfl⟩ : syracuseStep 420017 = 315013) B315013
theorem B420035 : Blo 279826 420035 := bstep (se 1 (by rfl) ⟨315026, by rfl⟩ : syracuseStep 420035 = 630053) B630053
theorem B420065 : Blo 279826 420065 := bstep (se 2 (by rfl) ⟨157524, by rfl⟩ : syracuseStep 420065 = 315049) B315049
theorem B1075427 : Blo 279826 1075427 := bstep (se 1 (by rfl) ⟨806570, by rfl⟩ : syracuseStep 1075427 = 1613141) B1613141
theorem B1370353 : Blo 279826 1370353 := bstep (se 2 (by rfl) ⟨513882, by rfl⟩ : syracuseStep 1370353 = 1027765) B1027765
theorem B420083 : Blo 279826 420083 := bstep (se 1 (by rfl) ⟨315062, by rfl⟩ : syracuseStep 420083 = 630125) B630125
theorem B354547 : Blo 279826 354547 := bstep (se 1 (by rfl) ⟨265910, by rfl⟩ : syracuseStep 354547 = 531821) B531821
theorem B420113 : Blo 279826 420113 := bstep (se 2 (by rfl) ⟨157542, by rfl⟩ : syracuseStep 420113 = 315085) B315085
theorem B420131 : Blo 279826 420131 := bstep (se 1 (by rfl) ⟨315098, by rfl⟩ : syracuseStep 420131 = 630197) B630197
theorem B420161 : Blo 279826 420161 := bstep (se 2 (by rfl) ⟨157560, by rfl⟩ : syracuseStep 420161 = 315121) B315121
theorem B420179 : Blo 279826 420179 := bstep (se 1 (by rfl) ⟨315134, by rfl⟩ : syracuseStep 420179 = 630269) B630269
theorem B420209 : Blo 279826 420209 := bstep (se 2 (by rfl) ⟨157578, by rfl⟩ : syracuseStep 420209 = 315157) B315157
theorem B420227 : Blo 279826 420227 := bstep (se 1 (by rfl) ⟨315170, by rfl⟩ : syracuseStep 420227 = 630341) B630341
theorem B715139 : Blo 279826 715139 := bstep (se 1 (by rfl) ⟨536354, by rfl⟩ : syracuseStep 715139 = 1072709) B1072709
theorem B420257 : Blo 279826 420257 := bstep (se 2 (by rfl) ⟨157596, by rfl⟩ : syracuseStep 420257 = 315193) B315193
theorem B420275 : Blo 279826 420275 := bstep (se 1 (by rfl) ⟨315206, by rfl⟩ : syracuseStep 420275 = 630413) B630413
theorem B453043 : Blo 279826 453043 := bstep (se 1 (by rfl) ⟨339782, by rfl⟩ : syracuseStep 453043 = 679565) B679565
theorem B420305 : Blo 279826 420305 := bstep (se 2 (by rfl) ⟨157614, by rfl⟩ : syracuseStep 420305 = 315229) B315229
theorem B420323 : Blo 279826 420323 := bstep (se 1 (by rfl) ⟨315242, by rfl⟩ : syracuseStep 420323 = 630485) B630485
theorem B1993187 : Blo 279826 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B944621 : Blo 279826 944621 := bstep (se 3 (by rfl) ⟨177116, by rfl⟩ : syracuseStep 944621 = 354233) B354233
theorem B3434993 : Blo 279826 3434993 := bstep (se 2 (by rfl) ⟨1288122, by rfl⟩ : syracuseStep 3434993 = 2576245) B2576245
theorem B420353 : Blo 279826 420353 := bstep (se 2 (by rfl) ⟨157632, by rfl⟩ : syracuseStep 420353 = 315265) B315265
theorem B813581 : Blo 279826 813581 := bstep (se 3 (by rfl) ⟨152546, by rfl⟩ : syracuseStep 813581 = 305093) B305093
theorem B420371 : Blo 279826 420371 := bstep (se 1 (by rfl) ⟨315278, by rfl⟩ : syracuseStep 420371 = 630557) B630557
theorem B944675 : Blo 279826 944675 := bstep (se 1 (by rfl) ⟨708506, by rfl⟩ : syracuseStep 944675 = 1417013) B1417013
theorem B420401 : Blo 279826 420401 := bstep (se 2 (by rfl) ⟨157650, by rfl⟩ : syracuseStep 420401 = 315301) B315301
theorem B420419 : Blo 279826 420419 := bstep (se 1 (by rfl) ⟨315314, by rfl⟩ : syracuseStep 420419 = 630629) B630629
theorem B715331 : Blo 279826 715331 := bstep (se 1 (by rfl) ⟨536498, by rfl⟩ : syracuseStep 715331 = 1072997) B1072997
theorem B420449 : Blo 279826 420449 := bstep (se 2 (by rfl) ⟨157668, by rfl⟩ : syracuseStep 420449 = 315337) B315337
theorem B420467 : Blo 279826 420467 := bstep (se 1 (by rfl) ⟨315350, by rfl⟩ : syracuseStep 420467 = 630701) B630701
theorem B420497 : Blo 279826 420497 := bstep (se 2 (by rfl) ⟨157686, by rfl⟩ : syracuseStep 420497 = 315373) B315373
theorem B420515 : Blo 279826 420515 := bstep (se 1 (by rfl) ⟨315386, by rfl⟩ : syracuseStep 420515 = 630773) B630773
theorem B420545 : Blo 279826 420545 := bstep (se 2 (by rfl) ⟨157704, by rfl⟩ : syracuseStep 420545 = 315409) B315409
theorem B1829573 : Blo 279826 1829573 := bstep (se 4 (by rfl) ⟨171522, by rfl⟩ : syracuseStep 1829573 = 343045) B343045
theorem B420563 : Blo 279826 420563 := bstep (se 1 (by rfl) ⟨315422, by rfl⟩ : syracuseStep 420563 = 630845) B630845
theorem B355043 : Blo 279826 355043 := bstep (se 1 (by rfl) ⟨266282, by rfl⟩ : syracuseStep 355043 = 532565) B532565
theorem B420593 : Blo 279826 420593 := bstep (se 2 (by rfl) ⟨157722, by rfl⟩ : syracuseStep 420593 = 315445) B315445
theorem B420611 : Blo 279826 420611 := bstep (se 1 (by rfl) ⟨315458, by rfl⟩ : syracuseStep 420611 = 630917) B630917
theorem B420641 : Blo 279826 420641 := bstep (se 2 (by rfl) ⟨157740, by rfl⟩ : syracuseStep 420641 = 315481) B315481
theorem B944945 : Blo 279826 944945 := bstep (se 2 (by rfl) ⟨354354, by rfl⟩ : syracuseStep 944945 = 708709) B708709
theorem B420659 : Blo 279826 420659 := bstep (se 1 (by rfl) ⟨315494, by rfl⟩ : syracuseStep 420659 = 630989) B630989
theorem B420689 : Blo 279826 420689 := bstep (se 2 (by rfl) ⟨157758, by rfl⟩ : syracuseStep 420689 = 315517) B315517
theorem B420707 : Blo 279826 420707 := bstep (se 1 (by rfl) ⟨315530, by rfl⟩ : syracuseStep 420707 = 631061) B631061
theorem B420737 : Blo 279826 420737 := bstep (se 2 (by rfl) ⟨157776, by rfl⟩ : syracuseStep 420737 = 315553) B315553
theorem B682897 : Blo 279826 682897 := bstep (se 2 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 682897 = 512173) B512173
theorem B420755 : Blo 279826 420755 := bstep (se 1 (by rfl) ⟨315566, by rfl⟩ : syracuseStep 420755 = 631133) B631133
theorem B420785 : Blo 279826 420785 := bstep (se 2 (by rfl) ⟨157794, by rfl⟩ : syracuseStep 420785 = 315589) B315589
theorem B322483 : Blo 279826 322483 := bstep (se 1 (by rfl) ⟨241862, by rfl⟩ : syracuseStep 322483 = 483725) B483725
theorem B420803 : Blo 279826 420803 := bstep (se 1 (by rfl) ⟨315602, by rfl⟩ : syracuseStep 420803 = 631205) B631205
theorem B420833 : Blo 279826 420833 := bstep (se 2 (by rfl) ⟨157812, by rfl⟩ : syracuseStep 420833 = 315625) B315625
theorem B420851 : Blo 279826 420851 := bstep (se 1 (by rfl) ⟨315638, by rfl⟩ : syracuseStep 420851 = 631277) B631277
theorem B420881 : Blo 279826 420881 := bstep (se 2 (by rfl) ⟨157830, by rfl⟩ : syracuseStep 420881 = 315661) B315661
theorem B420899 : Blo 279826 420899 := bstep (se 1 (by rfl) ⟨315674, by rfl⟩ : syracuseStep 420899 = 631349) B631349
theorem B1207345 : Blo 279826 1207345 := bstep (se 2 (by rfl) ⟨452754, by rfl⟩ : syracuseStep 1207345 = 905509) B905509
theorem B420929 : Blo 279826 420929 := bstep (se 2 (by rfl) ⟨157848, by rfl⟩ : syracuseStep 420929 = 315697) B315697
theorem B420947 : Blo 279826 420947 := bstep (se 1 (by rfl) ⟨315710, by rfl⟩ : syracuseStep 420947 = 631421) B631421
theorem B420977 : Blo 279826 420977 := bstep (se 2 (by rfl) ⟨157866, by rfl⟩ : syracuseStep 420977 = 315733) B315733
theorem B420995 : Blo 279826 420995 := bstep (se 1 (by rfl) ⟨315746, by rfl⟩ : syracuseStep 420995 = 631493) B631493
theorem B421025 : Blo 279826 421025 := bstep (se 2 (by rfl) ⟨157884, by rfl⟩ : syracuseStep 421025 = 315769) B315769
theorem B421043 : Blo 279826 421043 := bstep (se 1 (by rfl) ⟨315782, by rfl⟩ : syracuseStep 421043 = 631565) B631565
theorem B1076429 : Blo 279826 1076429 := bstep (se 3 (by rfl) ⟨201830, by rfl⟩ : syracuseStep 1076429 = 403661) B403661
theorem B421073 : Blo 279826 421073 := bstep (se 2 (by rfl) ⟨157902, by rfl⟩ : syracuseStep 421073 = 315805) B315805
theorem B421091 : Blo 279826 421091 := bstep (se 1 (by rfl) ⟨315818, by rfl⟩ : syracuseStep 421091 = 631637) B631637
theorem B421121 : Blo 279826 421121 := bstep (se 2 (by rfl) ⟨157920, by rfl⟩ : syracuseStep 421121 = 315841) B315841
theorem B421139 : Blo 279826 421139 := bstep (se 1 (by rfl) ⟨315854, by rfl⟩ : syracuseStep 421139 = 631709) B631709
theorem B421169 : Blo 279826 421169 := bstep (se 2 (by rfl) ⟨157938, by rfl⟩ : syracuseStep 421169 = 315877) B315877
theorem B421187 : Blo 279826 421187 := bstep (se 1 (by rfl) ⟨315890, by rfl⟩ : syracuseStep 421187 = 631781) B631781
theorem B945485 : Blo 279826 945485 := bstep (se 3 (by rfl) ⟨177278, by rfl⟩ : syracuseStep 945485 = 354557) B354557
theorem B421217 : Blo 279826 421217 := bstep (se 2 (by rfl) ⟨157956, by rfl⟩ : syracuseStep 421217 = 315913) B315913
theorem B421235 : Blo 279826 421235 := bstep (se 1 (by rfl) ⟨315926, by rfl⟩ : syracuseStep 421235 = 631853) B631853
theorem B945539 : Blo 279826 945539 := bstep (se 1 (by rfl) ⟨709154, by rfl⟩ : syracuseStep 945539 = 1418309) B1418309
theorem B421265 : Blo 279826 421265 := bstep (se 2 (by rfl) ⟨157974, by rfl⟩ : syracuseStep 421265 = 315949) B315949
theorem B421283 : Blo 279826 421283 := bstep (se 1 (by rfl) ⟨315962, by rfl⟩ : syracuseStep 421283 = 631925) B631925
theorem B355747 : Blo 279826 355747 := bstep (se 1 (by rfl) ⟨266810, by rfl⟩ : syracuseStep 355747 = 533621) B533621
theorem B421313 : Blo 279826 421313 := bstep (se 2 (by rfl) ⟨157992, by rfl⟩ : syracuseStep 421313 = 315985) B315985
theorem B421331 : Blo 279826 421331 := bstep (se 1 (by rfl) ⟨315998, by rfl⟩ : syracuseStep 421331 = 631997) B631997
theorem B421361 : Blo 279826 421361 := bstep (se 2 (by rfl) ⟨158010, by rfl⟩ : syracuseStep 421361 = 316021) B316021
theorem B716273 : Blo 279826 716273 := bstep (se 2 (by rfl) ⟨268602, by rfl⟩ : syracuseStep 716273 = 537205) B537205
theorem B421379 : Blo 279826 421379 := bstep (se 1 (by rfl) ⟨316034, by rfl⟩ : syracuseStep 421379 = 632069) B632069
theorem B355843 : Blo 279826 355843 := bstep (se 1 (by rfl) ⟨266882, by rfl⟩ : syracuseStep 355843 = 533765) B533765
theorem B421409 : Blo 279826 421409 := bstep (se 2 (by rfl) ⟨158028, by rfl⟩ : syracuseStep 421409 = 316057) B316057
theorem B716323 : Blo 279826 716323 := bstep (se 1 (by rfl) ⟨537242, by rfl⟩ : syracuseStep 716323 = 1074485) B1074485
theorem B421427 : Blo 279826 421427 := bstep (se 1 (by rfl) ⟨316070, by rfl⟩ : syracuseStep 421427 = 632141) B632141
theorem B421457 : Blo 279826 421457 := bstep (se 2 (by rfl) ⟨158046, by rfl⟩ : syracuseStep 421457 = 316093) B316093
theorem B421475 : Blo 279826 421475 := bstep (se 1 (by rfl) ⟨316106, by rfl⟩ : syracuseStep 421475 = 632213) B632213
theorem B421505 : Blo 279826 421505 := bstep (se 2 (by rfl) ⟨158064, by rfl⟩ : syracuseStep 421505 = 316129) B316129
theorem B945809 : Blo 279826 945809 := bstep (se 2 (by rfl) ⟨354678, by rfl⟩ : syracuseStep 945809 = 709357) B709357
theorem B421523 : Blo 279826 421523 := bstep (se 1 (by rfl) ⟨316142, by rfl⟩ : syracuseStep 421523 = 632285) B632285
theorem B421553 : Blo 279826 421553 := bstep (se 2 (by rfl) ⟨158082, by rfl⟩ : syracuseStep 421553 = 316165) B316165
theorem B716465 : Blo 279826 716465 := bstep (se 2 (by rfl) ⟨268674, by rfl⟩ : syracuseStep 716465 = 537349) B537349
theorem B421571 : Blo 279826 421571 := bstep (se 1 (by rfl) ⟨316178, by rfl⟩ : syracuseStep 421571 = 632357) B632357
theorem B1633997 : Blo 279826 1633997 := bstep (se 3 (by rfl) ⟨306374, by rfl⟩ : syracuseStep 1633997 = 612749) B612749
theorem B421601 : Blo 279826 421601 := bstep (se 2 (by rfl) ⟨158100, by rfl⟩ : syracuseStep 421601 = 316201) B316201
theorem B2289379 : Blo 279826 2289379 := bstep (se 1 (by rfl) ⟨1717034, by rfl⟩ : syracuseStep 2289379 = 3434069) B3434069
theorem B421619 : Blo 279826 421619 := bstep (se 1 (by rfl) ⟨316214, by rfl⟩ : syracuseStep 421619 = 632429) B632429
theorem B421649 : Blo 279826 421649 := bstep (se 2 (by rfl) ⟨158118, by rfl⟩ : syracuseStep 421649 = 316237) B316237
theorem B421667 : Blo 279826 421667 := bstep (se 1 (by rfl) ⟨316250, by rfl⟩ : syracuseStep 421667 = 632501) B632501
theorem B421697 : Blo 279826 421697 := bstep (se 2 (by rfl) ⟨158136, by rfl⟩ : syracuseStep 421697 = 316273) B316273
theorem B421715 : Blo 279826 421715 := bstep (se 1 (by rfl) ⟨316286, by rfl⟩ : syracuseStep 421715 = 632573) B632573
theorem B421745 : Blo 279826 421745 := bstep (se 2 (by rfl) ⟨158154, by rfl⟩ : syracuseStep 421745 = 316309) B316309
theorem B454529 : Blo 279826 454529 := bstep (se 2 (by rfl) ⟨170448, by rfl⟩ : syracuseStep 454529 = 340897) B340897
theorem B421763 : Blo 279826 421763 := bstep (se 1 (by rfl) ⟨316322, by rfl⟩ : syracuseStep 421763 = 632645) B632645
theorem B421793 : Blo 279826 421793 := bstep (se 2 (by rfl) ⟨158172, by rfl⟩ : syracuseStep 421793 = 316345) B316345
theorem B1011619 : Blo 279826 1011619 := bstep (se 1 (by rfl) ⟨758714, by rfl⟩ : syracuseStep 1011619 = 1517429) B1517429
theorem B421811 : Blo 279826 421811 := bstep (se 1 (by rfl) ⟨316358, by rfl⟩ : syracuseStep 421811 = 632717) B632717
theorem B1601477 : Blo 279826 1601477 := bstep (se 4 (by rfl) ⟨150138, by rfl⟩ : syracuseStep 1601477 = 300277) B300277
theorem B421841 : Blo 279826 421841 := bstep (se 2 (by rfl) ⟨158190, by rfl⟩ : syracuseStep 421841 = 316381) B316381
theorem B421859 : Blo 279826 421859 := bstep (se 1 (by rfl) ⟨316394, by rfl⟩ : syracuseStep 421859 = 632789) B632789
theorem B356339 : Blo 279826 356339 := bstep (se 1 (by rfl) ⟨267254, by rfl⟩ : syracuseStep 356339 = 534509) B534509
theorem B421889 : Blo 279826 421889 := bstep (se 2 (by rfl) ⟨158208, by rfl⟩ : syracuseStep 421889 = 316417) B316417
theorem B421907 : Blo 279826 421907 := bstep (se 1 (by rfl) ⟨316430, by rfl⟩ : syracuseStep 421907 = 632861) B632861
theorem B421937 : Blo 279826 421937 := bstep (se 2 (by rfl) ⟨158226, by rfl⟩ : syracuseStep 421937 = 316453) B316453
theorem B815153 : Blo 279826 815153 := bstep (se 2 (by rfl) ⟨305682, by rfl⟩ : syracuseStep 815153 = 611365) B611365
theorem B421955 : Blo 279826 421955 := bstep (se 1 (by rfl) ⟨316466, by rfl⟩ : syracuseStep 421955 = 632933) B632933
theorem B421985 : Blo 279826 421985 := bstep (se 2 (by rfl) ⟨158244, by rfl⟩ : syracuseStep 421985 = 316489) B316489
theorem B422003 : Blo 279826 422003 := bstep (se 1 (by rfl) ⟨316502, by rfl⟩ : syracuseStep 422003 = 633005) B633005
theorem B422033 : Blo 279826 422033 := bstep (se 2 (by rfl) ⟨158262, by rfl⟩ : syracuseStep 422033 = 316525) B316525
theorem B1798307 : Blo 279826 1798307 := bstep (se 1 (by rfl) ⟨1348730, by rfl⟩ : syracuseStep 1798307 = 2697461) B2697461
theorem B422051 : Blo 279826 422051 := bstep (se 1 (by rfl) ⟨316538, by rfl⟩ : syracuseStep 422051 = 633077) B633077
theorem B946349 : Blo 279826 946349 := bstep (se 3 (by rfl) ⟨177440, by rfl⟩ : syracuseStep 946349 = 354881) B354881
theorem B422081 : Blo 279826 422081 := bstep (se 2 (by rfl) ⟨158280, by rfl⟩ : syracuseStep 422081 = 316561) B316561
theorem B422099 : Blo 279826 422099 := bstep (se 1 (by rfl) ⟨316574, by rfl⟩ : syracuseStep 422099 = 633149) B633149
theorem B946403 : Blo 279826 946403 := bstep (se 1 (by rfl) ⟨709802, by rfl⟩ : syracuseStep 946403 = 1419605) B1419605
theorem B3207395 : Blo 279826 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B422129 : Blo 279826 422129 := bstep (se 2 (by rfl) ⟨158298, by rfl⟩ : syracuseStep 422129 = 316597) B316597
theorem B422147 : Blo 279826 422147 := bstep (se 1 (by rfl) ⟨316610, by rfl⟩ : syracuseStep 422147 = 633221) B633221
theorem B422177 : Blo 279826 422177 := bstep (se 2 (by rfl) ⟨158316, by rfl⟩ : syracuseStep 422177 = 316633) B316633
theorem B422195 : Blo 279826 422195 := bstep (se 1 (by rfl) ⟨316646, by rfl⟩ : syracuseStep 422195 = 633293) B633293
theorem B422225 : Blo 279826 422225 := bstep (se 2 (by rfl) ⟨158334, by rfl⟩ : syracuseStep 422225 = 316669) B316669
theorem B422243 : Blo 279826 422243 := bstep (se 1 (by rfl) ⟨316682, by rfl⟩ : syracuseStep 422243 = 633365) B633365
theorem B422273 : Blo 279826 422273 := bstep (se 2 (by rfl) ⟨158352, by rfl⟩ : syracuseStep 422273 = 316705) B316705
theorem B422291 : Blo 279826 422291 := bstep (se 1 (by rfl) ⟨316718, by rfl⟩ : syracuseStep 422291 = 633437) B633437
theorem B422321 : Blo 279826 422321 := bstep (se 2 (by rfl) ⟨158370, by rfl⟩ : syracuseStep 422321 = 316741) B316741
theorem B422339 : Blo 279826 422339 := bstep (se 1 (by rfl) ⟨316754, by rfl⟩ : syracuseStep 422339 = 633509) B633509
theorem B422369 : Blo 279826 422369 := bstep (se 2 (by rfl) ⟨158388, by rfl⟩ : syracuseStep 422369 = 316777) B316777
theorem B946673 : Blo 279826 946673 := bstep (se 2 (by rfl) ⟨355002, by rfl⟩ : syracuseStep 946673 = 710005) B710005
theorem B422387 : Blo 279826 422387 := bstep (se 1 (by rfl) ⟨316790, by rfl⟩ : syracuseStep 422387 = 633581) B633581
theorem B422417 : Blo 279826 422417 := bstep (se 2 (by rfl) ⟨158406, by rfl⟩ : syracuseStep 422417 = 316813) B316813
theorem B422435 : Blo 279826 422435 := bstep (se 1 (by rfl) ⟨316826, by rfl⟩ : syracuseStep 422435 = 633653) B633653
theorem B422465 : Blo 279826 422465 := bstep (se 2 (by rfl) ⟨158424, by rfl⟩ : syracuseStep 422465 = 316849) B316849
theorem B422483 : Blo 279826 422483 := bstep (se 1 (by rfl) ⟨316862, by rfl⟩ : syracuseStep 422483 = 633725) B633725
theorem B422513 : Blo 279826 422513 := bstep (se 2 (by rfl) ⟨158442, by rfl⟩ : syracuseStep 422513 = 316885) B316885
theorem B422531 : Blo 279826 422531 := bstep (se 1 (by rfl) ⟨316898, by rfl⟩ : syracuseStep 422531 = 633797) B633797
theorem B717457 : Blo 279826 717457 := bstep (se 2 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 717457 = 538093) B538093
theorem B422561 : Blo 279826 422561 := bstep (se 2 (by rfl) ⟨158460, by rfl⟩ : syracuseStep 422561 = 316921) B316921
theorem B422579 : Blo 279826 422579 := bstep (se 1 (by rfl) ⟨316934, by rfl⟩ : syracuseStep 422579 = 633869) B633869
theorem B357043 : Blo 279826 357043 := bstep (se 1 (by rfl) ⟨267782, by rfl⟩ : syracuseStep 357043 = 535565) B535565
theorem B422609 : Blo 279826 422609 := bstep (se 2 (by rfl) ⟨158478, by rfl⟩ : syracuseStep 422609 = 316957) B316957
theorem B422627 : Blo 279826 422627 := bstep (se 1 (by rfl) ⟨316970, by rfl⟩ : syracuseStep 422627 = 633941) B633941
theorem B422657 : Blo 279826 422657 := bstep (se 2 (by rfl) ⟨158496, by rfl⟩ : syracuseStep 422657 = 316993) B316993
theorem B422675 : Blo 279826 422675 := bstep (se 1 (by rfl) ⟨317006, by rfl⟩ : syracuseStep 422675 = 634013) B634013
theorem B357139 : Blo 279826 357139 := bstep (se 1 (by rfl) ⟨267854, by rfl⟩ : syracuseStep 357139 = 535709) B535709
theorem B422705 : Blo 279826 422705 := bstep (se 2 (by rfl) ⟨158514, by rfl⟩ : syracuseStep 422705 = 317029) B317029
theorem B422723 : Blo 279826 422723 := bstep (se 1 (by rfl) ⟨317042, by rfl⟩ : syracuseStep 422723 = 634085) B634085
theorem B422753 : Blo 279826 422753 := bstep (se 2 (by rfl) ⟨158532, by rfl⟩ : syracuseStep 422753 = 317065) B317065
theorem B422771 : Blo 279826 422771 := bstep (se 1 (by rfl) ⟨317078, by rfl⟩ : syracuseStep 422771 = 634157) B634157
theorem B422801 : Blo 279826 422801 := bstep (se 2 (by rfl) ⟨158550, by rfl⟩ : syracuseStep 422801 = 317101) B317101
theorem B422819 : Blo 279826 422819 := bstep (se 1 (by rfl) ⟨317114, by rfl⟩ : syracuseStep 422819 = 634229) B634229
theorem B717731 : Blo 279826 717731 := bstep (se 1 (by rfl) ⟨538298, by rfl⟩ : syracuseStep 717731 = 1076597) B1076597
theorem B422849 : Blo 279826 422849 := bstep (se 2 (by rfl) ⟨158568, by rfl⟩ : syracuseStep 422849 = 317137) B317137
theorem B422867 : Blo 279826 422867 := bstep (se 1 (by rfl) ⟨317150, by rfl⟩ : syracuseStep 422867 = 634301) B634301
theorem B422897 : Blo 279826 422897 := bstep (se 2 (by rfl) ⟨158586, by rfl⟩ : syracuseStep 422897 = 317173) B317173
theorem B422915 : Blo 279826 422915 := bstep (se 1 (by rfl) ⟨317186, by rfl⟩ : syracuseStep 422915 = 634373) B634373
theorem B947213 : Blo 279826 947213 := bstep (se 3 (by rfl) ⟨177602, by rfl⟩ : syracuseStep 947213 = 355205) B355205
theorem B422945 : Blo 279826 422945 := bstep (se 2 (by rfl) ⟨158604, by rfl⟩ : syracuseStep 422945 = 317209) B317209
theorem B422963 : Blo 279826 422963 := bstep (se 1 (by rfl) ⟨317222, by rfl⟩ : syracuseStep 422963 = 634445) B634445
theorem B947267 : Blo 279826 947267 := bstep (se 1 (by rfl) ⟨710450, by rfl⟩ : syracuseStep 947267 = 1420901) B1420901
theorem B422993 : Blo 279826 422993 := bstep (se 2 (by rfl) ⟨158622, by rfl⟩ : syracuseStep 422993 = 317245) B317245
theorem B423011 : Blo 279826 423011 := bstep (se 1 (by rfl) ⟨317258, by rfl⟩ : syracuseStep 423011 = 634517) B634517
theorem B717923 : Blo 279826 717923 := bstep (se 1 (by rfl) ⟨538442, by rfl⟩ : syracuseStep 717923 = 1076885) B1076885
theorem B423041 : Blo 279826 423041 := bstep (se 2 (by rfl) ⟨158640, by rfl⟩ : syracuseStep 423041 = 317281) B317281
theorem B423059 : Blo 279826 423059 := bstep (se 1 (by rfl) ⟨317294, by rfl⟩ : syracuseStep 423059 = 634589) B634589
theorem B718001 : Blo 279826 718001 := bstep (se 2 (by rfl) ⟨269250, by rfl⟩ : syracuseStep 718001 = 538501) B538501
theorem B423089 : Blo 279826 423089 := bstep (se 2 (by rfl) ⟨158658, by rfl⟩ : syracuseStep 423089 = 317317) B317317
theorem B423107 : Blo 279826 423107 := bstep (se 1 (by rfl) ⟨317330, by rfl⟩ : syracuseStep 423107 = 634661) B634661
theorem B423137 : Blo 279826 423137 := bstep (se 2 (by rfl) ⟨158676, by rfl⟩ : syracuseStep 423137 = 317353) B317353
theorem B423155 : Blo 279826 423155 := bstep (se 1 (by rfl) ⟨317366, by rfl⟩ : syracuseStep 423155 = 634733) B634733
theorem B357635 : Blo 279826 357635 := bstep (se 1 (by rfl) ⟨268226, by rfl⟩ : syracuseStep 357635 = 536453) B536453
theorem B423185 : Blo 279826 423185 := bstep (se 2 (by rfl) ⟨158694, by rfl⟩ : syracuseStep 423185 = 317389) B317389
theorem B423203 : Blo 279826 423203 := bstep (se 1 (by rfl) ⟨317402, by rfl⟩ : syracuseStep 423203 = 634805) B634805
theorem B423233 : Blo 279826 423233 := bstep (se 2 (by rfl) ⟨158712, by rfl⟩ : syracuseStep 423233 = 317425) B317425
theorem B947537 : Blo 279826 947537 := bstep (se 2 (by rfl) ⟨355326, by rfl⟩ : syracuseStep 947537 = 710653) B710653
theorem B423251 : Blo 279826 423251 := bstep (se 1 (by rfl) ⟨317438, by rfl⟩ : syracuseStep 423251 = 634877) B634877
theorem B423281 : Blo 279826 423281 := bstep (se 2 (by rfl) ⟨158730, by rfl⟩ : syracuseStep 423281 = 317461) B317461
theorem B423299 : Blo 279826 423299 := bstep (se 1 (by rfl) ⟨317474, by rfl⟩ : syracuseStep 423299 = 634949) B634949
theorem B423329 : Blo 279826 423329 := bstep (se 2 (by rfl) ⟨158748, by rfl⟩ : syracuseStep 423329 = 317497) B317497
theorem B423347 : Blo 279826 423347 := bstep (se 1 (by rfl) ⟨317510, by rfl⟩ : syracuseStep 423347 = 635021) B635021
theorem B423377 : Blo 279826 423377 := bstep (se 2 (by rfl) ⟨158766, by rfl⟩ : syracuseStep 423377 = 317533) B317533
theorem B423395 : Blo 279826 423395 := bstep (se 1 (by rfl) ⟨317546, by rfl⟩ : syracuseStep 423395 = 635093) B635093
theorem B423425 : Blo 279826 423425 := bstep (se 2 (by rfl) ⟨158784, by rfl⟩ : syracuseStep 423425 = 317569) B317569
theorem B423443 : Blo 279826 423443 := bstep (se 1 (by rfl) ⟨317582, by rfl⟩ : syracuseStep 423443 = 635165) B635165
theorem B423473 : Blo 279826 423473 := bstep (se 2 (by rfl) ⟨158802, by rfl⟩ : syracuseStep 423473 = 317605) B317605
theorem B423491 : Blo 279826 423491 := bstep (se 1 (by rfl) ⟨317618, by rfl⟩ : syracuseStep 423491 = 635237) B635237
theorem B1439309 : Blo 279826 1439309 := bstep (se 3 (by rfl) ⟨269870, by rfl⟩ : syracuseStep 1439309 = 539741) B539741
theorem B423521 : Blo 279826 423521 := bstep (se 2 (by rfl) ⟨158820, by rfl⟩ : syracuseStep 423521 = 317641) B317641
theorem B423539 : Blo 279826 423539 := bstep (se 1 (by rfl) ⟨317654, by rfl⟩ : syracuseStep 423539 = 635309) B635309
theorem B423569 : Blo 279826 423569 := bstep (se 2 (by rfl) ⟨158838, by rfl⟩ : syracuseStep 423569 = 317677) B317677
theorem B423587 : Blo 279826 423587 := bstep (se 1 (by rfl) ⟨317690, by rfl⟩ : syracuseStep 423587 = 635381) B635381
theorem B423617 : Blo 279826 423617 := bstep (se 2 (by rfl) ⟨158856, by rfl⟩ : syracuseStep 423617 = 317713) B317713
theorem B423635 : Blo 279826 423635 := bstep (se 1 (by rfl) ⟨317726, by rfl⟩ : syracuseStep 423635 = 635453) B635453
theorem B423665 : Blo 279826 423665 := bstep (se 2 (by rfl) ⟨158874, by rfl⟩ : syracuseStep 423665 = 317749) B317749
theorem B423683 : Blo 279826 423683 := bstep (se 1 (by rfl) ⟨317762, by rfl⟩ : syracuseStep 423683 = 635525) B635525
theorem B423713 : Blo 279826 423713 := bstep (se 2 (by rfl) ⟨158892, by rfl⟩ : syracuseStep 423713 = 317785) B317785
theorem B423731 : Blo 279826 423731 := bstep (se 1 (by rfl) ⟨317798, by rfl⟩ : syracuseStep 423731 = 635597) B635597
theorem B423761 : Blo 279826 423761 := bstep (se 2 (by rfl) ⟨158910, by rfl⟩ : syracuseStep 423761 = 317821) B317821
theorem B423779 : Blo 279826 423779 := bstep (se 1 (by rfl) ⟨317834, by rfl⟩ : syracuseStep 423779 = 635669) B635669
theorem B948077 : Blo 279826 948077 := bstep (se 3 (by rfl) ⟨177764, by rfl⟩ : syracuseStep 948077 = 355529) B355529
theorem B423809 : Blo 279826 423809 := bstep (se 2 (by rfl) ⟨158928, by rfl⟩ : syracuseStep 423809 = 317857) B317857
theorem B423827 : Blo 279826 423827 := bstep (se 1 (by rfl) ⟨317870, by rfl⟩ : syracuseStep 423827 = 635741) B635741
theorem B948131 : Blo 279826 948131 := bstep (se 1 (by rfl) ⟨711098, by rfl⟩ : syracuseStep 948131 = 1422197) B1422197
theorem B423857 : Blo 279826 423857 := bstep (se 2 (by rfl) ⟨158946, by rfl⟩ : syracuseStep 423857 = 317893) B317893
theorem B423875 : Blo 279826 423875 := bstep (se 1 (by rfl) ⟨317906, by rfl⟩ : syracuseStep 423875 = 635813) B635813
theorem B358339 : Blo 279826 358339 := bstep (se 1 (by rfl) ⟨268754, by rfl⟩ : syracuseStep 358339 = 537509) B537509
theorem B423905 : Blo 279826 423905 := bstep (se 2 (by rfl) ⟨158964, by rfl⟩ : syracuseStep 423905 = 317929) B317929
theorem B423923 : Blo 279826 423923 := bstep (se 1 (by rfl) ⟨317942, by rfl⟩ : syracuseStep 423923 = 635885) B635885
theorem B423953 : Blo 279826 423953 := bstep (se 2 (by rfl) ⟨158982, by rfl⟩ : syracuseStep 423953 = 317965) B317965
theorem B423971 : Blo 279826 423971 := bstep (se 1 (by rfl) ⟨317978, by rfl⟩ : syracuseStep 423971 = 635957) B635957
theorem B358435 : Blo 279826 358435 := bstep (se 1 (by rfl) ⟨268826, by rfl⟩ : syracuseStep 358435 = 537653) B537653
theorem B1210403 : Blo 279826 1210403 := bstep (se 1 (by rfl) ⟨907802, by rfl⟩ : syracuseStep 1210403 = 1815605) B1815605
theorem B424001 : Blo 279826 424001 := bstep (se 2 (by rfl) ⟨159000, by rfl⟩ : syracuseStep 424001 = 318001) B318001
theorem B424019 : Blo 279826 424019 := bstep (se 1 (by rfl) ⟨318014, by rfl⟩ : syracuseStep 424019 = 636029) B636029
theorem B424049 : Blo 279826 424049 := bstep (se 2 (by rfl) ⟨159018, by rfl⟩ : syracuseStep 424049 = 318037) B318037
theorem B424067 : Blo 279826 424067 := bstep (se 1 (by rfl) ⟨318050, by rfl⟩ : syracuseStep 424067 = 636101) B636101
theorem B424097 : Blo 279826 424097 := bstep (se 2 (by rfl) ⟨159036, by rfl⟩ : syracuseStep 424097 = 318073) B318073
theorem B915619 : Blo 279826 915619 := bstep (se 1 (by rfl) ⟨686714, by rfl⟩ : syracuseStep 915619 = 1373429) B1373429
theorem B948401 : Blo 279826 948401 := bstep (se 2 (by rfl) ⟨355650, by rfl⟩ : syracuseStep 948401 = 711301) B711301
theorem B424115 : Blo 279826 424115 := bstep (se 1 (by rfl) ⟨318086, by rfl⟩ : syracuseStep 424115 = 636173) B636173
theorem B424145 : Blo 279826 424145 := bstep (se 2 (by rfl) ⟨159054, by rfl⟩ : syracuseStep 424145 = 318109) B318109
theorem B817361 : Blo 279826 817361 := bstep (se 2 (by rfl) ⟨306510, by rfl⟩ : syracuseStep 817361 = 613021) B613021
theorem B424163 : Blo 279826 424163 := bstep (se 1 (by rfl) ⟨318122, by rfl⟩ : syracuseStep 424163 = 636245) B636245
theorem B424193 : Blo 279826 424193 := bstep (se 2 (by rfl) ⟨159072, by rfl⟩ : syracuseStep 424193 = 318145) B318145
theorem B424211 : Blo 279826 424211 := bstep (se 1 (by rfl) ⟨318158, by rfl⟩ : syracuseStep 424211 = 636317) B636317
theorem B424241 : Blo 279826 424241 := bstep (se 2 (by rfl) ⟨159090, by rfl⟩ : syracuseStep 424241 = 318181) B318181
theorem B424259 : Blo 279826 424259 := bstep (se 1 (by rfl) ⟨318194, by rfl⟩ : syracuseStep 424259 = 636389) B636389
theorem B424289 : Blo 279826 424289 := bstep (se 2 (by rfl) ⟨159108, by rfl⟩ : syracuseStep 424289 = 318217) B318217
theorem B424307 : Blo 279826 424307 := bstep (se 1 (by rfl) ⟨318230, by rfl⟩ : syracuseStep 424307 = 636461) B636461
theorem B424337 : Blo 279826 424337 := bstep (se 2 (by rfl) ⟨159126, by rfl⟩ : syracuseStep 424337 = 318253) B318253
theorem B424355 : Blo 279826 424355 := bstep (se 1 (by rfl) ⟨318266, by rfl⟩ : syracuseStep 424355 = 636533) B636533
theorem B424385 : Blo 279826 424385 := bstep (se 2 (by rfl) ⟨159144, by rfl⟩ : syracuseStep 424385 = 318289) B318289
theorem B424403 : Blo 279826 424403 := bstep (se 1 (by rfl) ⟨318302, by rfl⟩ : syracuseStep 424403 = 636605) B636605
theorem B424433 : Blo 279826 424433 := bstep (se 2 (by rfl) ⟨159162, by rfl⟩ : syracuseStep 424433 = 318325) B318325
theorem B424451 : Blo 279826 424451 := bstep (se 1 (by rfl) ⟨318338, by rfl⟩ : syracuseStep 424451 = 636677) B636677
theorem B358931 : Blo 279826 358931 := bstep (se 1 (by rfl) ⟨269198, by rfl⟩ : syracuseStep 358931 = 538397) B538397
theorem B424481 : Blo 279826 424481 := bstep (se 2 (by rfl) ⟨159180, by rfl⟩ : syracuseStep 424481 = 318361) B318361
theorem B424499 : Blo 279826 424499 := bstep (se 1 (by rfl) ⟨318374, by rfl⟩ : syracuseStep 424499 = 636749) B636749
theorem B424529 : Blo 279826 424529 := bstep (se 2 (by rfl) ⟨159198, by rfl⟩ : syracuseStep 424529 = 318397) B318397
theorem B424547 : Blo 279826 424547 := bstep (se 1 (by rfl) ⟨318410, by rfl⟩ : syracuseStep 424547 = 636821) B636821
theorem B424577 : Blo 279826 424577 := bstep (se 2 (by rfl) ⟨159216, by rfl⟩ : syracuseStep 424577 = 318433) B318433
theorem B424595 : Blo 279826 424595 := bstep (se 1 (by rfl) ⟨318446, by rfl⟩ : syracuseStep 424595 = 636893) B636893
theorem B424625 : Blo 279826 424625 := bstep (se 2 (by rfl) ⟨159234, by rfl⟩ : syracuseStep 424625 = 318469) B318469
theorem B424643 : Blo 279826 424643 := bstep (se 1 (by rfl) ⟨318482, by rfl⟩ : syracuseStep 424643 = 636965) B636965
theorem B948941 : Blo 279826 948941 := bstep (se 3 (by rfl) ⟨177926, by rfl⟩ : syracuseStep 948941 = 355853) B355853
theorem B424673 : Blo 279826 424673 := bstep (se 2 (by rfl) ⟨159252, by rfl⟩ : syracuseStep 424673 = 318505) B318505
theorem B424691 : Blo 279826 424691 := bstep (se 1 (by rfl) ⟨318518, by rfl⟩ : syracuseStep 424691 = 637037) B637037
theorem B948995 : Blo 279826 948995 := bstep (se 1 (by rfl) ⟨711746, by rfl⟩ : syracuseStep 948995 = 1423493) B1423493
theorem B424721 : Blo 279826 424721 := bstep (se 2 (by rfl) ⟨159270, by rfl⟩ : syracuseStep 424721 = 318541) B318541
theorem B424739 : Blo 279826 424739 := bstep (se 1 (by rfl) ⟨318554, by rfl⟩ : syracuseStep 424739 = 637109) B637109
theorem B424769 : Blo 279826 424769 := bstep (se 2 (by rfl) ⟨159288, by rfl⟩ : syracuseStep 424769 = 318577) B318577
theorem B424787 : Blo 279826 424787 := bstep (se 1 (by rfl) ⟨318590, by rfl⟩ : syracuseStep 424787 = 637181) B637181
theorem B424817 : Blo 279826 424817 := bstep (se 2 (by rfl) ⟨159306, by rfl⟩ : syracuseStep 424817 = 318613) B318613
theorem B424835 : Blo 279826 424835 := bstep (se 1 (by rfl) ⟨318626, by rfl⟩ : syracuseStep 424835 = 637253) B637253
theorem B424865 : Blo 279826 424865 := bstep (se 2 (by rfl) ⟨159324, by rfl⟩ : syracuseStep 424865 = 318649) B318649
theorem B424883 : Blo 279826 424883 := bstep (se 1 (by rfl) ⟨318662, by rfl⟩ : syracuseStep 424883 = 637325) B637325
theorem B424913 : Blo 279826 424913 := bstep (se 2 (by rfl) ⟨159342, by rfl⟩ : syracuseStep 424913 = 318685) B318685
theorem B424931 : Blo 279826 424931 := bstep (se 1 (by rfl) ⟨318698, by rfl⟩ : syracuseStep 424931 = 637397) B637397
theorem B424961 : Blo 279826 424961 := bstep (se 2 (by rfl) ⟨159360, by rfl⟩ : syracuseStep 424961 = 318721) B318721
theorem B949265 : Blo 279826 949265 := bstep (se 2 (by rfl) ⟨355974, by rfl⟩ : syracuseStep 949265 = 711949) B711949
theorem B424979 : Blo 279826 424979 := bstep (se 1 (by rfl) ⟨318734, by rfl⟩ : syracuseStep 424979 = 637469) B637469
theorem B916525 : Blo 279826 916525 := bstep (se 3 (by rfl) ⟨171848, by rfl⟩ : syracuseStep 916525 = 343697) B343697
theorem B425009 : Blo 279826 425009 := bstep (se 2 (by rfl) ⟨159378, by rfl⟩ : syracuseStep 425009 = 318757) B318757
theorem B425027 : Blo 279826 425027 := bstep (se 1 (by rfl) ⟨318770, by rfl⟩ : syracuseStep 425027 = 637541) B637541
theorem B425057 : Blo 279826 425057 := bstep (se 2 (by rfl) ⟨159396, by rfl⟩ : syracuseStep 425057 = 318793) B318793
theorem B425075 : Blo 279826 425075 := bstep (se 1 (by rfl) ⟨318806, by rfl⟩ : syracuseStep 425075 = 637613) B637613
theorem B425105 : Blo 279826 425105 := bstep (se 2 (by rfl) ⟨159414, by rfl⟩ : syracuseStep 425105 = 318829) B318829
theorem B425123 : Blo 279826 425123 := bstep (se 1 (by rfl) ⟨318842, by rfl⟩ : syracuseStep 425123 = 637685) B637685
theorem B425153 : Blo 279826 425153 := bstep (se 2 (by rfl) ⟨159432, by rfl⟩ : syracuseStep 425153 = 318865) B318865
theorem B425171 : Blo 279826 425171 := bstep (se 1 (by rfl) ⟨318878, by rfl⟩ : syracuseStep 425171 = 637757) B637757
theorem B2391281 : Blo 279826 2391281 := bstep (se 2 (by rfl) ⟨896730, by rfl⟩ : syracuseStep 2391281 = 1793461) B1793461
theorem B425201 : Blo 279826 425201 := bstep (se 2 (by rfl) ⟨159450, by rfl⟩ : syracuseStep 425201 = 318901) B318901
theorem B425219 : Blo 279826 425219 := bstep (se 1 (by rfl) ⟨318914, by rfl⟩ : syracuseStep 425219 = 637829) B637829
theorem B2129165 : Blo 279826 2129165 := bstep (se 3 (by rfl) ⟨399218, by rfl⟩ : syracuseStep 2129165 = 798437) B798437
theorem B425249 : Blo 279826 425249 := bstep (se 2 (by rfl) ⟨159468, by rfl⟩ : syracuseStep 425249 = 318937) B318937
theorem B425267 : Blo 279826 425267 := bstep (se 1 (by rfl) ⟨318950, by rfl⟩ : syracuseStep 425267 = 637901) B637901
theorem B851267 : Blo 279826 851267 := bstep (se 1 (by rfl) ⟨638450, by rfl⟩ : syracuseStep 851267 = 1276901) B1276901
theorem B425297 : Blo 279826 425297 := bstep (se 2 (by rfl) ⟨159486, by rfl⟩ : syracuseStep 425297 = 318973) B318973
theorem B425315 : Blo 279826 425315 := bstep (se 1 (by rfl) ⟨318986, by rfl⟩ : syracuseStep 425315 = 637973) B637973
theorem B425345 : Blo 279826 425345 := bstep (se 2 (by rfl) ⟨159504, by rfl⟩ : syracuseStep 425345 = 319009) B319009
theorem B3079565 : Blo 279826 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B425363 : Blo 279826 425363 := bstep (se 1 (by rfl) ⟨319022, by rfl⟩ : syracuseStep 425363 = 638045) B638045
theorem B425393 : Blo 279826 425393 := bstep (se 2 (by rfl) ⟨159522, by rfl⟩ : syracuseStep 425393 = 319045) B319045
theorem B425411 : Blo 279826 425411 := bstep (se 1 (by rfl) ⟨319058, by rfl⟩ : syracuseStep 425411 = 638117) B638117
theorem B425441 : Blo 279826 425441 := bstep (se 2 (by rfl) ⟨159540, by rfl⟩ : syracuseStep 425441 = 319081) B319081
theorem B425459 : Blo 279826 425459 := bstep (se 1 (by rfl) ⟨319094, by rfl⟩ : syracuseStep 425459 = 638189) B638189
theorem B425489 : Blo 279826 425489 := bstep (se 2 (by rfl) ⟨159558, by rfl⟩ : syracuseStep 425489 = 319117) B319117
theorem B425507 : Blo 279826 425507 := bstep (se 1 (by rfl) ⟨319130, by rfl⟩ : syracuseStep 425507 = 638261) B638261
theorem B949805 : Blo 279826 949805 := bstep (se 3 (by rfl) ⟨178088, by rfl⟩ : syracuseStep 949805 = 356177) B356177
theorem B425537 : Blo 279826 425537 := bstep (se 2 (by rfl) ⟨159576, by rfl⟩ : syracuseStep 425537 = 319153) B319153
theorem B1867333 : Blo 279826 1867333 := bstep (se 4 (by rfl) ⟨175062, by rfl⟩ : syracuseStep 1867333 = 350125) B350125
theorem B425555 : Blo 279826 425555 := bstep (se 1 (by rfl) ⟨319166, by rfl⟩ : syracuseStep 425555 = 638333) B638333
theorem B949859 : Blo 279826 949859 := bstep (se 1 (by rfl) ⟨712394, by rfl⟩ : syracuseStep 949859 = 1424789) B1424789
theorem B2719331 : Blo 279826 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B425585 : Blo 279826 425585 := bstep (se 2 (by rfl) ⟨159594, by rfl⟩ : syracuseStep 425585 = 319189) B319189
theorem B425603 : Blo 279826 425603 := bstep (se 1 (by rfl) ⟨319202, by rfl⟩ : syracuseStep 425603 = 638405) B638405
theorem B425633 : Blo 279826 425633 := bstep (se 2 (by rfl) ⟨159612, by rfl⟩ : syracuseStep 425633 = 319225) B319225
theorem B425651 : Blo 279826 425651 := bstep (se 1 (by rfl) ⟨319238, by rfl⟩ : syracuseStep 425651 = 638477) B638477
theorem B425681 : Blo 279826 425681 := bstep (se 2 (by rfl) ⟨159630, by rfl⟩ : syracuseStep 425681 = 319261) B319261
theorem B425699 : Blo 279826 425699 := bstep (se 1 (by rfl) ⟨319274, by rfl⟩ : syracuseStep 425699 = 638549) B638549
theorem B425729 : Blo 279826 425729 := bstep (se 2 (by rfl) ⟨159648, by rfl⟩ : syracuseStep 425729 = 319297) B319297
theorem B1801997 : Blo 279826 1801997 := bstep (se 3 (by rfl) ⟨337874, by rfl⟩ : syracuseStep 1801997 = 675749) B675749
theorem B950129 : Blo 279826 950129 := bstep (se 2 (by rfl) ⟨356298, by rfl⟩ : syracuseStep 950129 = 712597) B712597
theorem B1802225 : Blo 279826 1802225 := bstep (se 2 (by rfl) ⟨675834, by rfl⟩ : syracuseStep 1802225 = 1351669) B1351669
theorem B2130137 : Blo 279826 2130137 := bstep (se 2 (by rfl) ⟨798801, by rfl⟩ : syracuseStep 2130137 = 1597603) B1597603
theorem B1081817 : Blo 279826 1081817 := bstep (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) B811363
theorem B1245719 : Blo 279826 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B8553053 : Blo 279826 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B951371 : Blo 279826 951371 := bstep (se 1 (by rfl) ⟨713528, by rfl⟩ : syracuseStep 951371 = 1427057) B1427057
theorem B1279127 : Blo 279826 1279127 := bstep (se 1 (by rfl) ⟨959345, by rfl⟩ : syracuseStep 1279127 = 1918691) B1918691
theorem B951641 : Blo 279826 951641 := bstep (se 2 (by rfl) ⟨356865, by rfl⟩ : syracuseStep 951641 = 713731) B713731
theorem B952343 : Blo 279826 952343 := bstep (se 1 (by rfl) ⟨714257, by rfl⟩ : syracuseStep 952343 = 1428515) B1428515
theorem B1837187 : Blo 279826 1837187 := bstep (se 1 (by rfl) ⟨1377890, by rfl⟩ : syracuseStep 1837187 = 2755781) B2755781
theorem B5114177 : Blo 279826 5114177 := bstep (se 2 (by rfl) ⟨1917816, by rfl⟩ : syracuseStep 5114177 = 3835633) B3835633
theorem B1149329 : Blo 279826 1149329 := bstep (se 2 (by rfl) ⟨430998, by rfl⟩ : syracuseStep 1149329 = 861997) B861997
theorem B2394629 : Blo 279826 2394629 := bstep (se 4 (by rfl) ⟨224496, by rfl⟩ : syracuseStep 2394629 = 448993) B448993
theorem B1149457 : Blo 279826 1149457 := bstep (se 2 (by rfl) ⟨431046, by rfl⟩ : syracuseStep 1149457 = 862093) B862093
theorem B952883 : Blo 279826 952883 := bstep (se 1 (by rfl) ⟨714662, by rfl⟩ : syracuseStep 952883 = 1429325) B1429325
theorem B690905 : Blo 279826 690905 := bstep (se 2 (by rfl) ⟨259089, by rfl⟩ : syracuseStep 690905 = 518179) B518179
theorem B953153 : Blo 279826 953153 := bstep (se 2 (by rfl) ⟨357432, by rfl⟩ : syracuseStep 953153 = 714865) B714865
theorem B2165825 : Blo 279826 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B2723021 : Blo 279826 2723021 := bstep (se 3 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 2723021 = 1021133) B1021133
theorem B953693 : Blo 279826 953693 := bstep (se 3 (by rfl) ⟨178817, by rfl⟩ : syracuseStep 953693 = 357635) B357635
theorem B2133539 : Blo 279826 2133539 := bstep (se 1 (by rfl) ⟨1600154, by rfl⟩ : syracuseStep 2133539 = 3200309) B3200309
theorem B757451 : Blo 279826 757451 := bstep (se 1 (by rfl) ⟨568088, by rfl⟩ : syracuseStep 757451 = 1136177) B1136177
theorem B1806097 : Blo 279826 1806097 := bstep (se 2 (by rfl) ⟨677286, by rfl⟩ : syracuseStep 1806097 = 1354573) B1354573
theorem B429977 : Blo 279826 429977 := bstep (se 2 (by rfl) ⟨161241, by rfl⟩ : syracuseStep 429977 = 322483) B322483
theorem B1609793 : Blo 279826 1609793 := bstep (se 2 (by rfl) ⟨603672, by rfl⟩ : syracuseStep 1609793 = 1207345) B1207345
theorem B8720459 : Blo 279826 8720459 := bstep (se 1 (by rfl) ⟨6540344, by rfl⟩ : syracuseStep 8720459 = 13080689) B13080689
theorem B2199653 : Blo 279826 2199653 := bstep (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) B412435
theorem B528563 : Blo 279826 528563 := bstep (se 1 (by rfl) ⟨396422, by rfl⟩ : syracuseStep 528563 = 792845) B792845
theorem B1085699 : Blo 279826 1085699 := bstep (se 1 (by rfl) ⟨814274, by rfl⟩ : syracuseStep 1085699 = 1628549) B1628549
theorem B954827 : Blo 279826 954827 := bstep (se 1 (by rfl) ⟨716120, by rfl⟩ : syracuseStep 954827 = 1432241) B1432241
theorem B856669 : Blo 279826 856669 := bstep (se 3 (by rfl) ⟨160625, by rfl⟩ : syracuseStep 856669 = 321251) B321251
theorem B1806941 : Blo 279826 1806941 := bstep (se 3 (by rfl) ⟨338801, by rfl⟩ : syracuseStep 1806941 = 677603) B677603
theorem B955097 : Blo 279826 955097 := bstep (se 2 (by rfl) ⟨358161, by rfl⟩ : syracuseStep 955097 = 716323) B716323
theorem B3052505 : Blo 279826 3052505 := bstep (se 2 (by rfl) ⟨1144689, by rfl⟩ : syracuseStep 3052505 = 2289379) B2289379
theorem B1840229 : Blo 279826 1840229 := bstep (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) B345043
theorem B1348787 : Blo 279826 1348787 := bstep (se 1 (by rfl) ⟨1011590, by rfl⟩ : syracuseStep 1348787 = 2023181) B2023181
theorem B1348825 : Blo 279826 1348825 := bstep (se 2 (by rfl) ⟨505809, by rfl⟩ : syracuseStep 1348825 = 1011619) B1011619
theorem B4330853 : Blo 279826 4330853 := bstep (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) B812035
theorem B955799 : Blo 279826 955799 := bstep (se 1 (by rfl) ⟨716849, by rfl⟩ : syracuseStep 955799 = 1433699) B1433699
theorem B2069965 : Blo 279826 2069965 := bstep (se 3 (by rfl) ⟨388118, by rfl⟩ : syracuseStep 2069965 = 776237) B776237
theorem B300619 : Blo 279826 300619 := bstep (se 1 (by rfl) ⟨225464, by rfl⟩ : syracuseStep 300619 = 450929) B450929
theorem B759385 : Blo 279826 759385 := bstep (se 2 (by rfl) ⟨284769, by rfl⟩ : syracuseStep 759385 = 569539) B569539
theorem B2398045 : Blo 279826 2398045 := bstep (se 3 (by rfl) ⟨449633, by rfl⟩ : syracuseStep 2398045 = 899267) B899267
theorem B956339 : Blo 279826 956339 := bstep (se 1 (by rfl) ⟨717254, by rfl⟩ : syracuseStep 956339 = 1434509) B1434509
theorem B956609 : Blo 279826 956609 := bstep (se 2 (by rfl) ⟨358728, by rfl⟩ : syracuseStep 956609 = 717457) B717457
theorem B1612183 : Blo 279826 1612183 := bstep (se 1 (by rfl) ⟨1209137, by rfl⟩ : syracuseStep 1612183 = 2418275) B2418275
theorem B957149 : Blo 279826 957149 := bstep (se 3 (by rfl) ⟨179465, by rfl⟩ : syracuseStep 957149 = 358931) B358931
theorem B400153 : Blo 279826 400153 := bstep (se 2 (by rfl) ⟨150057, by rfl⟩ : syracuseStep 400153 = 300115) B300115
theorem B1514315 : Blo 279826 1514315 := bstep (se 1 (by rfl) ⟨1135736, by rfl⟩ : syracuseStep 1514315 = 2271473) B2271473
theorem B531289 : Blo 279826 531289 := bstep (se 2 (by rfl) ⟨199233, by rfl⟩ : syracuseStep 531289 = 398467) B398467
theorem B629657 : Blo 279826 629657 := bstep (se 2 (by rfl) ⟨236121, by rfl⟩ : syracuseStep 629657 = 472243) B472243
theorem B760769 : Blo 279826 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B629747 : Blo 279826 629747 := bstep (se 1 (by rfl) ⟨472310, by rfl⟩ : syracuseStep 629747 = 944621) B944621
theorem B629783 : Blo 279826 629783 := bstep (se 1 (by rfl) ⟨472337, by rfl⟩ : syracuseStep 629783 = 944675) B944675
theorem B1219715 : Blo 279826 1219715 := bstep (se 1 (by rfl) ⟨914786, by rfl⟩ : syracuseStep 1219715 = 1829573) B1829573
theorem B629963 : Blo 279826 629963 := bstep (se 1 (by rfl) ⟨472472, by rfl⟩ : syracuseStep 629963 = 944945) B944945
theorem B630017 : Blo 279826 630017 := bstep (se 2 (by rfl) ⟨236256, by rfl⟩ : syracuseStep 630017 = 472513) B472513
theorem B630233 : Blo 279826 630233 := bstep (se 2 (by rfl) ⟨236337, by rfl⟩ : syracuseStep 630233 = 472675) B472675
theorem B630323 : Blo 279826 630323 := bstep (se 1 (by rfl) ⟨472742, by rfl⟩ : syracuseStep 630323 = 945485) B945485
theorem B630359 : Blo 279826 630359 := bstep (se 1 (by rfl) ⟨472769, by rfl⟩ : syracuseStep 630359 = 945539) B945539
theorem B1384067 : Blo 279826 1384067 := bstep (se 1 (by rfl) ⟨1038050, by rfl⟩ : syracuseStep 1384067 = 2076101) B2076101
theorem B630539 : Blo 279826 630539 := bstep (se 1 (by rfl) ⟨472904, by rfl⟩ : syracuseStep 630539 = 945809) B945809
theorem B859927 : Blo 279826 859927 := bstep (se 1 (by rfl) ⟨644945, by rfl⟩ : syracuseStep 859927 = 1289891) B1289891
theorem B1089331 : Blo 279826 1089331 := bstep (se 1 (by rfl) ⟨816998, by rfl⟩ : syracuseStep 1089331 = 1633997) B1633997
theorem B630593 : Blo 279826 630593 := bstep (se 2 (by rfl) ⟨236472, by rfl⟩ : syracuseStep 630593 = 472945) B472945
theorem B630809 : Blo 279826 630809 := bstep (se 2 (by rfl) ⟨236553, by rfl⟩ : syracuseStep 630809 = 473107) B473107
theorem B34480241 : Blo 279826 34480241 := bstep (se 2 (by rfl) ⟨12930090, by rfl⟩ : syracuseStep 34480241 = 25860181) B25860181
theorem B630899 : Blo 279826 630899 := bstep (se 1 (by rfl) ⟨473174, by rfl⟩ : syracuseStep 630899 = 946349) B946349
theorem B532595 : Blo 279826 532595 := bstep (se 1 (by rfl) ⟨399446, by rfl⟩ : syracuseStep 532595 = 798893) B798893
theorem B630935 : Blo 279826 630935 := bstep (se 1 (by rfl) ⟨473201, by rfl⟩ : syracuseStep 630935 = 946403) B946403
theorem B401611 : Blo 279826 401611 := bstep (se 1 (by rfl) ⟨301208, by rfl⟩ : syracuseStep 401611 = 602417) B602417
theorem B1220825 : Blo 279826 1220825 := bstep (se 2 (by rfl) ⟨457809, by rfl⟩ : syracuseStep 1220825 = 915619) B915619
theorem B532747 : Blo 279826 532747 := bstep (se 1 (by rfl) ⟨399560, by rfl⟩ : syracuseStep 532747 = 799121) B799121
theorem B631115 : Blo 279826 631115 := bstep (se 1 (by rfl) ⟨473336, by rfl⟩ : syracuseStep 631115 = 946673) B946673
theorem B631169 : Blo 279826 631169 := bstep (se 2 (by rfl) ⟨236688, by rfl⟩ : syracuseStep 631169 = 473377) B473377
theorem B795187 : Blo 279826 795187 := bstep (se 1 (by rfl) ⟨596390, by rfl⟩ : syracuseStep 795187 = 1192781) B1192781
theorem B631385 : Blo 279826 631385 := bstep (se 2 (by rfl) ⟨236769, by rfl⟩ : syracuseStep 631385 = 473539) B473539
theorem B533081 : Blo 279826 533081 := bstep (se 2 (by rfl) ⟨199905, by rfl⟩ : syracuseStep 533081 = 399811) B399811
theorem B1352285 : Blo 279826 1352285 := bstep (se 3 (by rfl) ⟨253553, by rfl⟩ : syracuseStep 1352285 = 507107) B507107
theorem B631475 : Blo 279826 631475 := bstep (se 1 (by rfl) ⟨473606, by rfl⟩ : syracuseStep 631475 = 947213) B947213
theorem B631511 : Blo 279826 631511 := bstep (se 1 (by rfl) ⟨473633, by rfl⟩ : syracuseStep 631511 = 947267) B947267
theorem B2138885 : Blo 279826 2138885 := bstep (se 4 (by rfl) ⟨200520, by rfl⟩ : syracuseStep 2138885 = 401041) B401041
theorem B2270045 : Blo 279826 2270045 := bstep (se 3 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 2270045 = 851267) B851267
theorem B631691 : Blo 279826 631691 := bstep (se 1 (by rfl) ⟨473768, by rfl⟩ : syracuseStep 631691 = 947537) B947537
theorem B631745 : Blo 279826 631745 := bstep (se 2 (by rfl) ⟨236904, by rfl⟩ : syracuseStep 631745 = 473809) B473809
theorem B599051 : Blo 279826 599051 := bstep (se 1 (by rfl) ⟨449288, by rfl⟩ : syracuseStep 599051 = 898577) B898577
theorem B959539 : Blo 279826 959539 := bstep (se 1 (by rfl) ⟨719654, by rfl⟩ : syracuseStep 959539 = 1439309) B1439309
theorem B631961 : Blo 279826 631961 := bstep (se 2 (by rfl) ⟨236985, by rfl⟩ : syracuseStep 631961 = 473971) B473971
theorem B533719 : Blo 279826 533719 := bstep (se 1 (by rfl) ⟨400289, by rfl⟩ : syracuseStep 533719 = 800579) B800579
theorem B632051 : Blo 279826 632051 := bstep (se 1 (by rfl) ⟨474038, by rfl⟩ : syracuseStep 632051 = 948077) B948077
theorem B632087 : Blo 279826 632087 := bstep (se 1 (by rfl) ⟨474065, by rfl⟩ : syracuseStep 632087 = 948131) B948131
theorem B1222033 : Blo 279826 1222033 := bstep (se 2 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 1222033 = 916525) B916525
theorem B402841 : Blo 279826 402841 := bstep (se 2 (by rfl) ⟨151065, by rfl⟩ : syracuseStep 402841 = 302131) B302131
theorem B632267 : Blo 279826 632267 := bstep (se 1 (by rfl) ⟨474200, by rfl⟩ : syracuseStep 632267 = 948401) B948401
theorem B632321 : Blo 279826 632321 := bstep (se 2 (by rfl) ⟨237120, by rfl⟩ : syracuseStep 632321 = 474241) B474241
theorem B632537 : Blo 279826 632537 := bstep (se 2 (by rfl) ⟨237201, by rfl⟩ : syracuseStep 632537 = 474403) B474403
theorem B632627 : Blo 279826 632627 := bstep (se 1 (by rfl) ⟨474470, by rfl⟩ : syracuseStep 632627 = 948941) B948941
theorem B632663 : Blo 279826 632663 := bstep (se 1 (by rfl) ⟨474497, by rfl⟩ : syracuseStep 632663 = 948995) B948995
theorem B337879 : Blo 279826 337879 := bstep (se 1 (by rfl) ⟨253409, by rfl⟩ : syracuseStep 337879 = 506819) B506819
theorem B632843 : Blo 279826 632843 := bstep (se 1 (by rfl) ⟨474632, by rfl⟩ : syracuseStep 632843 = 949265) B949265
theorem B534539 : Blo 279826 534539 := bstep (se 1 (by rfl) ⟨400904, by rfl⟩ : syracuseStep 534539 = 801809) B801809
theorem B1419281 : Blo 279826 1419281 := bstep (se 2 (by rfl) ⟨532230, by rfl⟩ : syracuseStep 1419281 = 1064461) B1064461
theorem B632897 : Blo 279826 632897 := bstep (se 2 (by rfl) ⟨237336, by rfl⟩ : syracuseStep 632897 = 474673) B474673
theorem B534593 : Blo 279826 534593 := bstep (se 2 (by rfl) ⟨200472, by rfl⟩ : syracuseStep 534593 = 400945) B400945
theorem B1419443 : Blo 279826 1419443 := bstep (se 1 (by rfl) ⟨1064582, by rfl⟩ : syracuseStep 1419443 = 2129165) B2129165
theorem B600281 : Blo 279826 600281 := bstep (se 2 (by rfl) ⟨225105, by rfl⟩ : syracuseStep 600281 = 450211) B450211
theorem B633113 : Blo 279826 633113 := bstep (se 2 (by rfl) ⟨237417, by rfl⟩ : syracuseStep 633113 = 474835) B474835
theorem B5122349 : Blo 279826 5122349 := bstep (se 3 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 5122349 = 1920881) B1920881
theorem B796979 : Blo 279826 796979 := bstep (se 1 (by rfl) ⟨597734, by rfl⟩ : syracuseStep 796979 = 1195469) B1195469
theorem B797003 : Blo 279826 797003 := bstep (se 1 (by rfl) ⟨597752, by rfl⟩ : syracuseStep 797003 = 1195505) B1195505
theorem B1845605 : Blo 279826 1845605 := bstep (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) B346051
theorem B633203 : Blo 279826 633203 := bstep (se 1 (by rfl) ⟨474902, by rfl⟩ : syracuseStep 633203 = 949805) B949805
theorem B633239 : Blo 279826 633239 := bstep (se 1 (by rfl) ⟨474929, by rfl⟩ : syracuseStep 633239 = 949859) B949859
theorem B1812887 : Blo 279826 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B633419 : Blo 279826 633419 := bstep (se 1 (by rfl) ⟨475064, by rfl⟩ : syracuseStep 633419 = 950129) B950129
theorem B600691 : Blo 279826 600691 := bstep (se 1 (by rfl) ⟨450518, by rfl⟩ : syracuseStep 600691 = 901037) B901037
theorem B633473 : Blo 279826 633473 := bstep (se 2 (by rfl) ⟨237552, by rfl⟩ : syracuseStep 633473 = 475105) B475105
theorem B633689 : Blo 279826 633689 := bstep (se 2 (by rfl) ⟨237633, by rfl⟩ : syracuseStep 633689 = 475267) B475267
theorem B600947 : Blo 279826 600947 := bstep (se 1 (by rfl) ⟨450710, by rfl⟩ : syracuseStep 600947 = 901421) B901421
theorem B568193 : Blo 279826 568193 := bstep (se 2 (by rfl) ⟨213072, by rfl⟩ : syracuseStep 568193 = 426145) B426145
theorem B633779 : Blo 279826 633779 := bstep (se 1 (by rfl) ⟨475334, by rfl⟩ : syracuseStep 633779 = 950669) B950669
theorem B633815 : Blo 279826 633815 := bstep (se 1 (by rfl) ⟨475361, by rfl⟩ : syracuseStep 633815 = 950723) B950723
theorem B535511 : Blo 279826 535511 := bstep (se 1 (by rfl) ⟨401633, by rfl⟩ : syracuseStep 535511 = 803267) B803267
theorem B797789 : Blo 279826 797789 := bstep (se 3 (by rfl) ⟨149585, by rfl⟩ : syracuseStep 797789 = 299171) B299171
theorem B2141315 : Blo 279826 2141315 := bstep (se 1 (by rfl) ⟨1605986, by rfl⟩ : syracuseStep 2141315 = 3211973) B3211973
theorem B633995 : Blo 279826 633995 := bstep (se 1 (by rfl) ⟨475496, by rfl⟩ : syracuseStep 633995 = 950993) B950993
theorem B8694965 : Blo 279826 8694965 := bstep (se 5 (by rfl) ⟨407576, by rfl⟩ : syracuseStep 8694965 = 815153) B815153
theorem B634049 : Blo 279826 634049 := bstep (se 2 (by rfl) ⟨237768, by rfl⟩ : syracuseStep 634049 = 475537) B475537
theorem B3452165 : Blo 279826 3452165 := bstep (se 4 (by rfl) ⟨323640, by rfl⟩ : syracuseStep 3452165 = 647281) B647281
theorem B634265 : Blo 279826 634265 := bstep (se 2 (by rfl) ⟨237849, by rfl⟩ : syracuseStep 634265 = 475699) B475699
theorem B404939 : Blo 279826 404939 := bstep (se 1 (by rfl) ⟨303704, by rfl⟩ : syracuseStep 404939 = 607409) B607409
theorem B634355 : Blo 279826 634355 := bstep (se 1 (by rfl) ⟨475766, by rfl⟩ : syracuseStep 634355 = 951533) B951533
theorem B536051 : Blo 279826 536051 := bstep (se 1 (by rfl) ⟨402038, by rfl⟩ : syracuseStep 536051 = 804077) B804077
theorem B634391 : Blo 279826 634391 := bstep (se 1 (by rfl) ⟨475793, by rfl⟩ : syracuseStep 634391 = 951587) B951587
theorem B634571 : Blo 279826 634571 := bstep (se 1 (by rfl) ⟨475928, by rfl⟩ : syracuseStep 634571 = 951857) B951857
theorem B634625 : Blo 279826 634625 := bstep (se 2 (by rfl) ⟨237984, by rfl⟩ : syracuseStep 634625 = 475969) B475969
theorem B601921 : Blo 279826 601921 := bstep (se 2 (by rfl) ⟨225720, by rfl⟩ : syracuseStep 601921 = 451441) B451441
theorem B1716061 : Blo 279826 1716061 := bstep (se 3 (by rfl) ⟨321761, by rfl⟩ : syracuseStep 1716061 = 643523) B643523
theorem B10825649 : Blo 279826 10825649 := bstep (se 2 (by rfl) ⟨4059618, by rfl⟩ : syracuseStep 10825649 = 8119237) B8119237
theorem B569281 : Blo 279826 569281 := bstep (se 2 (by rfl) ⟨213480, by rfl⟩ : syracuseStep 569281 = 426961) B426961
theorem B634841 : Blo 279826 634841 := bstep (se 2 (by rfl) ⟨238065, by rfl⟩ : syracuseStep 634841 = 476131) B476131
theorem B536537 : Blo 279826 536537 := bstep (se 2 (by rfl) ⟨201201, by rfl⟩ : syracuseStep 536537 = 402403) B402403
theorem B634931 : Blo 279826 634931 := bstep (se 1 (by rfl) ⟨476198, by rfl⟩ : syracuseStep 634931 = 952397) B952397
theorem B1421387 : Blo 279826 1421387 := bstep (se 1 (by rfl) ⟨1066040, by rfl⟩ : syracuseStep 1421387 = 2132081) B2132081
theorem B634967 : Blo 279826 634967 := bstep (se 1 (by rfl) ⟨476225, by rfl⟩ : syracuseStep 634967 = 952451) B952451
theorem B635147 : Blo 279826 635147 := bstep (se 1 (by rfl) ⟨476360, by rfl⟩ : syracuseStep 635147 = 952721) B952721
theorem B635201 : Blo 279826 635201 := bstep (se 2 (by rfl) ⟨238200, by rfl⟩ : syracuseStep 635201 = 476401) B476401
theorem B9318773 : Blo 279826 9318773 := bstep (se 5 (by rfl) ⟨436817, by rfl⟩ : syracuseStep 9318773 = 873635) B873635
theorem B635417 : Blo 279826 635417 := bstep (se 2 (by rfl) ⟨238281, by rfl⟩ : syracuseStep 635417 = 476563) B476563
theorem B635507 : Blo 279826 635507 := bstep (se 1 (by rfl) ⟨476630, by rfl⟩ : syracuseStep 635507 = 953261) B953261
theorem B1356419 : Blo 279826 1356419 := bstep (se 1 (by rfl) ⟨1017314, by rfl⟩ : syracuseStep 1356419 = 2034629) B2034629
theorem B635543 : Blo 279826 635543 := bstep (se 1 (by rfl) ⟨476657, by rfl⟩ : syracuseStep 635543 = 953315) B953315
theorem B635723 : Blo 279826 635723 := bstep (se 1 (by rfl) ⟨476792, by rfl⟩ : syracuseStep 635723 = 953585) B953585
theorem B799577 : Blo 279826 799577 := bstep (se 2 (by rfl) ⟨299841, by rfl⟩ : syracuseStep 799577 = 599683) B599683
theorem B635777 : Blo 279826 635777 := bstep (se 2 (by rfl) ⟨238416, by rfl⟩ : syracuseStep 635777 = 476833) B476833
theorem B635993 : Blo 279826 635993 := bstep (se 2 (by rfl) ⟨238497, by rfl⟩ : syracuseStep 635993 = 476995) B476995
theorem B799895 : Blo 279826 799895 := bstep (se 1 (by rfl) ⟨599921, by rfl⟩ : syracuseStep 799895 = 1199843) B1199843
theorem B636083 : Blo 279826 636083 := bstep (se 1 (by rfl) ⟨477062, by rfl⟩ : syracuseStep 636083 = 954125) B954125
theorem B636119 : Blo 279826 636119 := bstep (se 1 (by rfl) ⟨477089, by rfl⟩ : syracuseStep 636119 = 954179) B954179
theorem B472331 : Blo 279826 472331 := bstep (se 1 (by rfl) ⟨354248, by rfl⟩ : syracuseStep 472331 = 708497) B708497
theorem B898397 : Blo 279826 898397 := bstep (se 3 (by rfl) ⟨168449, by rfl⟩ : syracuseStep 898397 = 336899) B336899
theorem B472459 : Blo 279826 472459 := bstep (se 1 (by rfl) ⟨354344, by rfl⟩ : syracuseStep 472459 = 708689) B708689
theorem B636299 : Blo 279826 636299 := bstep (se 1 (by rfl) ⟨477224, by rfl⟩ : syracuseStep 636299 = 954449) B954449
theorem B537995 : Blo 279826 537995 := bstep (se 1 (by rfl) ⟨403496, by rfl⟩ : syracuseStep 537995 = 806993) B806993
theorem B636353 : Blo 279826 636353 := bstep (se 2 (by rfl) ⟨238632, by rfl⟩ : syracuseStep 636353 = 477265) B477265
theorem B472601 : Blo 279826 472601 := bstep (se 2 (by rfl) ⟨177225, by rfl⟩ : syracuseStep 472601 = 354451) B354451
theorem B538177 : Blo 279826 538177 := bstep (se 2 (by rfl) ⟨201816, by rfl⟩ : syracuseStep 538177 = 403633) B403633
theorem B472729 : Blo 279826 472729 := bstep (se 2 (by rfl) ⟨177273, by rfl⟩ : syracuseStep 472729 = 354547) B354547
theorem B636569 : Blo 279826 636569 := bstep (se 2 (by rfl) ⟨238713, by rfl⟩ : syracuseStep 636569 = 477427) B477427
theorem B636659 : Blo 279826 636659 := bstep (se 1 (by rfl) ⟨477494, by rfl⟩ : syracuseStep 636659 = 954989) B954989
theorem B636695 : Blo 279826 636695 := bstep (se 1 (by rfl) ⟨477521, by rfl⟩ : syracuseStep 636695 = 955043) B955043
theorem B1423169 : Blo 279826 1423169 := bstep (se 2 (by rfl) ⟨533688, by rfl⟩ : syracuseStep 1423169 = 1067377) B1067377
theorem B505739 : Blo 279826 505739 := bstep (se 1 (by rfl) ⟨379304, by rfl⟩ : syracuseStep 505739 = 758609) B758609
theorem B604057 : Blo 279826 604057 := bstep (se 2 (by rfl) ⟨226521, by rfl⟩ : syracuseStep 604057 = 453043) B453043
theorem B800705 : Blo 279826 800705 := bstep (se 2 (by rfl) ⟨300264, by rfl⟩ : syracuseStep 800705 = 600529) B600529
theorem B636875 : Blo 279826 636875 := bstep (se 1 (by rfl) ⟨477656, by rfl⟩ : syracuseStep 636875 = 955313) B955313
theorem B636929 : Blo 279826 636929 := bstep (se 2 (by rfl) ⟨238848, by rfl⟩ : syracuseStep 636929 = 477697) B477697
theorem B538625 : Blo 279826 538625 := bstep (se 2 (by rfl) ⟨201984, by rfl⟩ : syracuseStep 538625 = 403969) B403969
theorem B2046053 : Blo 279826 2046053 := bstep (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) B383635
theorem B473303 : Blo 279826 473303 := bstep (se 1 (by rfl) ⟨354977, by rfl⟩ : syracuseStep 473303 = 709955) B709955
theorem B637145 : Blo 279826 637145 := bstep (se 2 (by rfl) ⟨238929, by rfl⟩ : syracuseStep 637145 = 477859) B477859
theorem B637235 : Blo 279826 637235 := bstep (se 1 (by rfl) ⟨477926, by rfl⟩ : syracuseStep 637235 = 955853) B955853
theorem B473431 : Blo 279826 473431 := bstep (se 1 (by rfl) ⟨355073, by rfl⟩ : syracuseStep 473431 = 710147) B710147
theorem B637271 : Blo 279826 637271 := bstep (se 1 (by rfl) ⟨477953, by rfl⟩ : syracuseStep 637271 = 955907) B955907
theorem B2144717 : Blo 279826 2144717 := bstep (se 3 (by rfl) ⟨402134, by rfl⟩ : syracuseStep 2144717 = 804269) B804269
theorem B637451 : Blo 279826 637451 := bstep (se 1 (by rfl) ⟨478088, by rfl⟩ : syracuseStep 637451 = 956177) B956177
theorem B10271245 : Blo 279826 10271245 := bstep (se 3 (by rfl) ⟨1925858, by rfl⟩ : syracuseStep 10271245 = 3851717) B3851717
theorem B1063475 : Blo 279826 1063475 := bstep (se 1 (by rfl) ⟨797606, by rfl⟩ : syracuseStep 1063475 = 1595213) B1595213
theorem B1063489 : Blo 279826 1063489 := bstep (se 2 (by rfl) ⟨398808, by rfl⟩ : syracuseStep 1063489 = 797617) B797617
theorem B637505 : Blo 279826 637505 := bstep (se 2 (by rfl) ⟨239064, by rfl⟩ : syracuseStep 637505 = 478129) B478129
theorem B899677 : Blo 279826 899677 := bstep (se 3 (by rfl) ⟨168689, by rfl⟩ : syracuseStep 899677 = 337379) B337379
theorem B637721 : Blo 279826 637721 := bstep (se 2 (by rfl) ⟨239145, by rfl⟩ : syracuseStep 637721 = 478291) B478291
theorem B637811 : Blo 279826 637811 := bstep (se 1 (by rfl) ⟨478358, by rfl⟩ : syracuseStep 637811 = 956717) B956717
theorem B637847 : Blo 279826 637847 := bstep (se 1 (by rfl) ⟨478385, by rfl⟩ : syracuseStep 637847 = 956771) B956771
theorem B2145203 : Blo 279826 2145203 := bstep (se 1 (by rfl) ⟨1608902, by rfl⟩ : syracuseStep 2145203 = 3217805) B3217805
theorem B474059 : Blo 279826 474059 := bstep (se 1 (by rfl) ⟨355544, by rfl⟩ : syracuseStep 474059 = 711089) B711089
theorem B572441 : Blo 279826 572441 := bstep (se 2 (by rfl) ⟨214665, by rfl⟩ : syracuseStep 572441 = 429331) B429331
theorem B474187 : Blo 279826 474187 := bstep (se 1 (by rfl) ⟨355640, by rfl⟩ : syracuseStep 474187 = 711281) B711281
theorem B638027 : Blo 279826 638027 := bstep (se 1 (by rfl) ⟨478520, by rfl⟩ : syracuseStep 638027 = 957041) B957041
theorem B638081 : Blo 279826 638081 := bstep (se 2 (by rfl) ⟨239280, by rfl⟩ : syracuseStep 638081 = 478561) B478561
theorem B474329 : Blo 279826 474329 := bstep (se 2 (by rfl) ⟨177873, by rfl⟩ : syracuseStep 474329 = 355747) B355747
theorem B474457 : Blo 279826 474457 := bstep (se 2 (by rfl) ⟨177921, by rfl⟩ : syracuseStep 474457 = 355843) B355843
theorem B638297 : Blo 279826 638297 := bstep (se 2 (by rfl) ⟨239361, by rfl⟩ : syracuseStep 638297 = 478723) B478723
theorem B638387 : Blo 279826 638387 := bstep (se 1 (by rfl) ⟨478790, by rfl⟩ : syracuseStep 638387 = 957581) B957581
theorem B638423 : Blo 279826 638423 := bstep (se 1 (by rfl) ⟨478817, by rfl⟩ : syracuseStep 638423 = 957635) B957635
theorem B802379 : Blo 279826 802379 := bstep (se 1 (by rfl) ⟨601784, by rfl⟩ : syracuseStep 802379 = 1203569) B1203569
theorem B638603 : Blo 279826 638603 := bstep (se 1 (by rfl) ⟨478952, by rfl⟩ : syracuseStep 638603 = 957905) B957905
theorem B1425113 : Blo 279826 1425113 := bstep (se 2 (by rfl) ⟨534417, by rfl⟩ : syracuseStep 1425113 = 1068835) B1068835
theorem B638707 : Blo 279826 638707 := bstep (se 1 (by rfl) ⟨479030, by rfl⟩ : syracuseStep 638707 = 958061) B958061
theorem B475031 : Blo 279826 475031 := bstep (se 1 (by rfl) ⟨356273, by rfl⟩ : syracuseStep 475031 = 712547) B712547
theorem B507799 : Blo 279826 507799 := bstep (se 1 (by rfl) ⟨380849, by rfl⟩ : syracuseStep 507799 = 761699) B761699
theorem B2473907 : Blo 279826 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B475159 : Blo 279826 475159 := bstep (se 1 (by rfl) ⟨356369, by rfl⟩ : syracuseStep 475159 = 712739) B712739
theorem B4145357 : Blo 279826 4145357 := bstep (se 3 (by rfl) ⟨777254, by rfl⟩ : syracuseStep 4145357 = 1554509) B1554509
theorem B2146661 : Blo 279826 2146661 := bstep (se 4 (by rfl) ⟨201249, by rfl⟩ : syracuseStep 2146661 = 402499) B402499
theorem B1065419 : Blo 279826 1065419 := bstep (se 1 (by rfl) ⟨799064, by rfl⟩ : syracuseStep 1065419 = 1598129) B1598129
theorem B508375 : Blo 279826 508375 := bstep (se 1 (by rfl) ⟨381281, by rfl⟩ : syracuseStep 508375 = 762563) B762563
theorem B1065433 : Blo 279826 1065433 := bstep (se 2 (by rfl) ⟨399537, by rfl⟩ : syracuseStep 1065433 = 799075) B799075
theorem B508427 : Blo 279826 508427 := bstep (se 1 (by rfl) ⟨381320, by rfl⟩ : syracuseStep 508427 = 762641) B762641
theorem B639539 : Blo 279826 639539 := bstep (se 1 (by rfl) ⟨479654, by rfl⟩ : syracuseStep 639539 = 959309) B959309
theorem B475787 : Blo 279826 475787 := bstep (se 1 (by rfl) ⟨356840, by rfl⟩ : syracuseStep 475787 = 713681) B713681
theorem B475915 : Blo 279826 475915 := bstep (se 1 (by rfl) ⟨356936, by rfl⟩ : syracuseStep 475915 = 713873) B713873
theorem B2147147 : Blo 279826 2147147 := bstep (se 1 (by rfl) ⟨1610360, by rfl⟩ : syracuseStep 2147147 = 3220721) B3220721
theorem B803677 : Blo 279826 803677 := bstep (se 3 (by rfl) ⟨150689, by rfl⟩ : syracuseStep 803677 = 301379) B301379
theorem B476057 : Blo 279826 476057 := bstep (se 2 (by rfl) ⟨178521, by rfl⟩ : syracuseStep 476057 = 357043) B357043
theorem B476185 : Blo 279826 476185 := bstep (se 2 (by rfl) ⟨178569, by rfl⟩ : syracuseStep 476185 = 357139) B357139
theorem B672857 : Blo 279826 672857 := bstep (se 2 (by rfl) ⟨252321, by rfl⟩ : syracuseStep 672857 = 504643) B504643
theorem B804019 : Blo 279826 804019 := bstep (se 1 (by rfl) ⟨603014, by rfl⟩ : syracuseStep 804019 = 1206029) B1206029
theorem B279831 : Blo 279826 279831 := bstep (se 1 (by rfl) ⟨209873, by rfl⟩ : syracuseStep 279831 = 419747) B419747
theorem B279851 : Blo 279826 279851 := bstep (se 1 (by rfl) ⟨209888, by rfl⟩ : syracuseStep 279851 = 419777) B419777
theorem B1426733 : Blo 279826 1426733 := bstep (se 3 (by rfl) ⟨267512, by rfl⟩ : syracuseStep 1426733 = 535025) B535025
theorem B279863 : Blo 279826 279863 := bstep (se 1 (by rfl) ⟨209897, by rfl⟩ : syracuseStep 279863 = 419795) B419795
theorem B279883 : Blo 279826 279883 := bstep (se 1 (by rfl) ⟨209912, by rfl⟩ : syracuseStep 279883 = 419825) B419825
theorem B279895 : Blo 279826 279895 := bstep (se 1 (by rfl) ⟨209921, by rfl⟩ : syracuseStep 279895 = 419843) B419843
theorem B279915 : Blo 279826 279915 := bstep (se 1 (by rfl) ⟨209936, by rfl⟩ : syracuseStep 279915 = 419873) B419873
theorem B279927 : Blo 279826 279927 := bstep (se 1 (by rfl) ⟨209945, by rfl⟩ : syracuseStep 279927 = 419891) B419891
theorem B279947 : Blo 279826 279947 := bstep (se 1 (by rfl) ⟨209960, by rfl⟩ : syracuseStep 279947 = 419921) B419921
theorem B279959 : Blo 279826 279959 := bstep (se 1 (by rfl) ⟨209969, by rfl⟩ : syracuseStep 279959 = 419939) B419939
theorem B1066391 : Blo 279826 1066391 := bstep (se 1 (by rfl) ⟨799793, by rfl⟩ : syracuseStep 1066391 = 1599587) B1599587
theorem B279979 : Blo 279826 279979 := bstep (se 1 (by rfl) ⟨209984, by rfl⟩ : syracuseStep 279979 = 419969) B419969
theorem B279991 : Blo 279826 279991 := bstep (se 1 (by rfl) ⟨209993, by rfl⟩ : syracuseStep 279991 = 419987) B419987
theorem B280011 : Blo 279826 280011 := bstep (se 1 (by rfl) ⟨210008, by rfl⟩ : syracuseStep 280011 = 420017) B420017
theorem B280023 : Blo 279826 280023 := bstep (se 1 (by rfl) ⟨210017, by rfl⟩ : syracuseStep 280023 = 420035) B420035
theorem B280043 : Blo 279826 280043 := bstep (se 1 (by rfl) ⟨210032, by rfl⟩ : syracuseStep 280043 = 420065) B420065
theorem B280055 : Blo 279826 280055 := bstep (se 1 (by rfl) ⟨210041, by rfl⟩ : syracuseStep 280055 = 420083) B420083
theorem B280075 : Blo 279826 280075 := bstep (se 1 (by rfl) ⟨210056, by rfl⟩ : syracuseStep 280075 = 420113) B420113
theorem B280087 : Blo 279826 280087 := bstep (se 1 (by rfl) ⟨210065, by rfl⟩ : syracuseStep 280087 = 420131) B420131
theorem B509465 : Blo 279826 509465 := bstep (se 2 (by rfl) ⟨191049, by rfl⟩ : syracuseStep 509465 = 382099) B382099
theorem B280107 : Blo 279826 280107 := bstep (se 1 (by rfl) ⟨210080, by rfl⟩ : syracuseStep 280107 = 420161) B420161
theorem B280119 : Blo 279826 280119 := bstep (se 1 (by rfl) ⟨210089, by rfl⟩ : syracuseStep 280119 = 420179) B420179
theorem B280139 : Blo 279826 280139 := bstep (se 1 (by rfl) ⟨210104, by rfl⟩ : syracuseStep 280139 = 420209) B420209
theorem B280151 : Blo 279826 280151 := bstep (se 1 (by rfl) ⟨210113, by rfl⟩ : syracuseStep 280151 = 420227) B420227
theorem B476759 : Blo 279826 476759 := bstep (se 1 (by rfl) ⟨357569, by rfl⟩ : syracuseStep 476759 = 715139) B715139
theorem B280171 : Blo 279826 280171 := bstep (se 1 (by rfl) ⟨210128, by rfl⟩ : syracuseStep 280171 = 420257) B420257
theorem B280183 : Blo 279826 280183 := bstep (se 1 (by rfl) ⟨210137, by rfl⟩ : syracuseStep 280183 = 420275) B420275
theorem B280203 : Blo 279826 280203 := bstep (se 1 (by rfl) ⟨210152, by rfl⟩ : syracuseStep 280203 = 420305) B420305
theorem B280215 : Blo 279826 280215 := bstep (se 1 (by rfl) ⟨210161, by rfl⟩ : syracuseStep 280215 = 420323) B420323
theorem B1328791 : Blo 279826 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B280235 : Blo 279826 280235 := bstep (se 1 (by rfl) ⟨210176, by rfl⟩ : syracuseStep 280235 = 420353) B420353
theorem B542387 : Blo 279826 542387 := bstep (se 1 (by rfl) ⟨406790, by rfl⟩ : syracuseStep 542387 = 813581) B813581
theorem B4966069 : Blo 279826 4966069 := bstep (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) B465569
theorem B280247 : Blo 279826 280247 := bstep (se 1 (by rfl) ⟨210185, by rfl⟩ : syracuseStep 280247 = 420371) B420371
theorem B280267 : Blo 279826 280267 := bstep (se 1 (by rfl) ⟨210200, by rfl⟩ : syracuseStep 280267 = 420401) B420401
theorem B280279 : Blo 279826 280279 := bstep (se 1 (by rfl) ⟨210209, by rfl⟩ : syracuseStep 280279 = 420419) B420419
theorem B476887 : Blo 279826 476887 := bstep (se 1 (by rfl) ⟨357665, by rfl⟩ : syracuseStep 476887 = 715331) B715331
theorem B280299 : Blo 279826 280299 := bstep (se 1 (by rfl) ⟨210224, by rfl⟩ : syracuseStep 280299 = 420449) B420449
theorem B280311 : Blo 279826 280311 := bstep (se 1 (by rfl) ⟨210233, by rfl⟩ : syracuseStep 280311 = 420467) B420467
theorem B280331 : Blo 279826 280331 := bstep (se 1 (by rfl) ⟨210248, by rfl⟩ : syracuseStep 280331 = 420497) B420497
theorem B280343 : Blo 279826 280343 := bstep (se 1 (by rfl) ⟨210257, by rfl⟩ : syracuseStep 280343 = 420515) B420515
theorem B280363 : Blo 279826 280363 := bstep (se 1 (by rfl) ⟨210272, by rfl⟩ : syracuseStep 280363 = 420545) B420545
theorem B280375 : Blo 279826 280375 := bstep (se 1 (by rfl) ⟨210281, by rfl⟩ : syracuseStep 280375 = 420563) B420563
theorem B280395 : Blo 279826 280395 := bstep (se 1 (by rfl) ⟨210296, by rfl⟩ : syracuseStep 280395 = 420593) B420593
theorem B280407 : Blo 279826 280407 := bstep (se 1 (by rfl) ⟨210305, by rfl⟩ : syracuseStep 280407 = 420611) B420611
theorem B280427 : Blo 279826 280427 := bstep (se 1 (by rfl) ⟨210320, by rfl⟩ : syracuseStep 280427 = 420641) B420641
theorem B280439 : Blo 279826 280439 := bstep (se 1 (by rfl) ⟨210329, by rfl⟩ : syracuseStep 280439 = 420659) B420659
theorem B280459 : Blo 279826 280459 := bstep (se 1 (by rfl) ⟨210344, by rfl⟩ : syracuseStep 280459 = 420689) B420689
theorem B280471 : Blo 279826 280471 := bstep (se 1 (by rfl) ⟨210353, by rfl⟩ : syracuseStep 280471 = 420707) B420707
theorem B280491 : Blo 279826 280491 := bstep (se 1 (by rfl) ⟨210368, by rfl⟩ : syracuseStep 280491 = 420737) B420737
theorem B280503 : Blo 279826 280503 := bstep (se 1 (by rfl) ⟨210377, by rfl⟩ : syracuseStep 280503 = 420755) B420755
theorem B280523 : Blo 279826 280523 := bstep (se 1 (by rfl) ⟨210392, by rfl⟩ : syracuseStep 280523 = 420785) B420785
theorem B280535 : Blo 279826 280535 := bstep (se 1 (by rfl) ⟨210401, by rfl⟩ : syracuseStep 280535 = 420803) B420803
theorem B280555 : Blo 279826 280555 := bstep (se 1 (by rfl) ⟨210416, by rfl⟩ : syracuseStep 280555 = 420833) B420833
theorem B280567 : Blo 279826 280567 := bstep (se 1 (by rfl) ⟨210425, by rfl⟩ : syracuseStep 280567 = 420851) B420851
theorem B280587 : Blo 279826 280587 := bstep (se 1 (by rfl) ⟨210440, by rfl⟩ : syracuseStep 280587 = 420881) B420881
theorem B280599 : Blo 279826 280599 := bstep (se 1 (by rfl) ⟨210449, by rfl⟩ : syracuseStep 280599 = 420899) B420899
theorem B280619 : Blo 279826 280619 := bstep (se 1 (by rfl) ⟨210464, by rfl⟩ : syracuseStep 280619 = 420929) B420929
theorem B280631 : Blo 279826 280631 := bstep (se 1 (by rfl) ⟨210473, by rfl⟩ : syracuseStep 280631 = 420947) B420947
theorem B280651 : Blo 279826 280651 := bstep (se 1 (by rfl) ⟨210488, by rfl⟩ : syracuseStep 280651 = 420977) B420977
theorem B280663 : Blo 279826 280663 := bstep (se 1 (by rfl) ⟨210497, by rfl⟩ : syracuseStep 280663 = 420995) B420995
theorem B804953 : Blo 279826 804953 := bstep (se 2 (by rfl) ⟨301857, by rfl⟩ : syracuseStep 804953 = 603715) B603715
theorem B280683 : Blo 279826 280683 := bstep (se 1 (by rfl) ⟨210512, by rfl⟩ : syracuseStep 280683 = 421025) B421025
theorem B280695 : Blo 279826 280695 := bstep (se 1 (by rfl) ⟨210521, by rfl⟩ : syracuseStep 280695 = 421043) B421043
theorem B280715 : Blo 279826 280715 := bstep (se 1 (by rfl) ⟨210536, by rfl⟩ : syracuseStep 280715 = 421073) B421073
theorem B280727 : Blo 279826 280727 := bstep (se 1 (by rfl) ⟨210545, by rfl⟩ : syracuseStep 280727 = 421091) B421091
theorem B280747 : Blo 279826 280747 := bstep (se 1 (by rfl) ⟨210560, by rfl⟩ : syracuseStep 280747 = 421121) B421121
theorem B280759 : Blo 279826 280759 := bstep (se 1 (by rfl) ⟨210569, by rfl⟩ : syracuseStep 280759 = 421139) B421139
theorem B280779 : Blo 279826 280779 := bstep (se 1 (by rfl) ⟨210584, by rfl⟩ : syracuseStep 280779 = 421169) B421169
theorem B280791 : Blo 279826 280791 := bstep (se 1 (by rfl) ⟨210593, by rfl⟩ : syracuseStep 280791 = 421187) B421187
theorem B280811 : Blo 279826 280811 := bstep (se 1 (by rfl) ⟨210608, by rfl⟩ : syracuseStep 280811 = 421217) B421217
theorem B280823 : Blo 279826 280823 := bstep (se 1 (by rfl) ⟨210617, by rfl⟩ : syracuseStep 280823 = 421235) B421235
theorem B280843 : Blo 279826 280843 := bstep (se 1 (by rfl) ⟨210632, by rfl⟩ : syracuseStep 280843 = 421265) B421265
theorem B280855 : Blo 279826 280855 := bstep (se 1 (by rfl) ⟨210641, by rfl⟩ : syracuseStep 280855 = 421283) B421283
theorem B280875 : Blo 279826 280875 := bstep (se 1 (by rfl) ⟨210656, by rfl⟩ : syracuseStep 280875 = 421313) B421313
theorem B280887 : Blo 279826 280887 := bstep (se 1 (by rfl) ⟨210665, by rfl⟩ : syracuseStep 280887 = 421331) B421331
theorem B280907 : Blo 279826 280907 := bstep (se 1 (by rfl) ⟨210680, by rfl⟩ : syracuseStep 280907 = 421361) B421361
theorem B477515 : Blo 279826 477515 := bstep (se 1 (by rfl) ⟨358136, by rfl⟩ : syracuseStep 477515 = 716273) B716273
theorem B280919 : Blo 279826 280919 := bstep (se 1 (by rfl) ⟨210689, by rfl⟩ : syracuseStep 280919 = 421379) B421379
theorem B280939 : Blo 279826 280939 := bstep (se 1 (by rfl) ⟨210704, by rfl⟩ : syracuseStep 280939 = 421409) B421409
theorem B280951 : Blo 279826 280951 := bstep (se 1 (by rfl) ⟨210713, by rfl⟩ : syracuseStep 280951 = 421427) B421427
theorem B280971 : Blo 279826 280971 := bstep (se 1 (by rfl) ⟨210728, by rfl⟩ : syracuseStep 280971 = 421457) B421457
theorem B280983 : Blo 279826 280983 := bstep (se 1 (by rfl) ⟨210737, by rfl⟩ : syracuseStep 280983 = 421475) B421475
theorem B281003 : Blo 279826 281003 := bstep (se 1 (by rfl) ⟨210752, by rfl⟩ : syracuseStep 281003 = 421505) B421505
theorem B281015 : Blo 279826 281015 := bstep (se 1 (by rfl) ⟨210761, by rfl⟩ : syracuseStep 281015 = 421523) B421523
theorem B281035 : Blo 279826 281035 := bstep (se 1 (by rfl) ⟨210776, by rfl⟩ : syracuseStep 281035 = 421553) B421553
theorem B477643 : Blo 279826 477643 := bstep (se 1 (by rfl) ⟨358232, by rfl⟩ : syracuseStep 477643 = 716465) B716465
theorem B281047 : Blo 279826 281047 := bstep (se 1 (by rfl) ⟨210785, by rfl⟩ : syracuseStep 281047 = 421571) B421571
theorem B281067 : Blo 279826 281067 := bstep (se 1 (by rfl) ⟨210800, by rfl⟩ : syracuseStep 281067 = 421601) B421601
theorem B510451 : Blo 279826 510451 := bstep (se 1 (by rfl) ⟨382838, by rfl⟩ : syracuseStep 510451 = 765677) B765677
theorem B281079 : Blo 279826 281079 := bstep (se 1 (by rfl) ⟨210809, by rfl⟩ : syracuseStep 281079 = 421619) B421619
theorem B281099 : Blo 279826 281099 := bstep (se 1 (by rfl) ⟨210824, by rfl⟩ : syracuseStep 281099 = 421649) B421649
theorem B281111 : Blo 279826 281111 := bstep (se 1 (by rfl) ⟨210833, by rfl⟩ : syracuseStep 281111 = 421667) B421667
theorem B281131 : Blo 279826 281131 := bstep (se 1 (by rfl) ⟨210848, by rfl⟩ : syracuseStep 281131 = 421697) B421697
theorem B281143 : Blo 279826 281143 := bstep (se 1 (by rfl) ⟨210857, by rfl⟩ : syracuseStep 281143 = 421715) B421715
theorem B281163 : Blo 279826 281163 := bstep (se 1 (by rfl) ⟨210872, by rfl⟩ : syracuseStep 281163 = 421745) B421745
theorem B281175 : Blo 279826 281175 := bstep (se 1 (by rfl) ⟨210881, by rfl⟩ : syracuseStep 281175 = 421763) B421763
theorem B477785 : Blo 279826 477785 := bstep (se 2 (by rfl) ⟨179169, by rfl⟩ : syracuseStep 477785 = 358339) B358339
theorem B281195 : Blo 279826 281195 := bstep (se 1 (by rfl) ⟨210896, by rfl⟩ : syracuseStep 281195 = 421793) B421793
theorem B281207 : Blo 279826 281207 := bstep (se 1 (by rfl) ⟨210905, by rfl⟩ : syracuseStep 281207 = 421811) B421811
theorem B1067651 : Blo 279826 1067651 := bstep (se 1 (by rfl) ⟨800738, by rfl⟩ : syracuseStep 1067651 = 1601477) B1601477
theorem B281227 : Blo 279826 281227 := bstep (se 1 (by rfl) ⟨210920, by rfl⟩ : syracuseStep 281227 = 421841) B421841
theorem B281239 : Blo 279826 281239 := bstep (se 1 (by rfl) ⟨210929, by rfl⟩ : syracuseStep 281239 = 421859) B421859
theorem B281259 : Blo 279826 281259 := bstep (se 1 (by rfl) ⟨210944, by rfl⟩ : syracuseStep 281259 = 421889) B421889
theorem B281271 : Blo 279826 281271 := bstep (se 1 (by rfl) ⟨210953, by rfl⟩ : syracuseStep 281271 = 421907) B421907
theorem B281291 : Blo 279826 281291 := bstep (se 1 (by rfl) ⟨210968, by rfl⟩ : syracuseStep 281291 = 421937) B421937
theorem B281303 : Blo 279826 281303 := bstep (se 1 (by rfl) ⟨210977, by rfl⟩ : syracuseStep 281303 = 421955) B421955
theorem B477913 : Blo 279826 477913 := bstep (se 2 (by rfl) ⟨179217, by rfl⟩ : syracuseStep 477913 = 358435) B358435
theorem B281323 : Blo 279826 281323 := bstep (se 1 (by rfl) ⟨210992, by rfl⟩ : syracuseStep 281323 = 421985) B421985
theorem B281335 : Blo 279826 281335 := bstep (se 1 (by rfl) ⟨211001, by rfl⟩ : syracuseStep 281335 = 422003) B422003
theorem B281355 : Blo 279826 281355 := bstep (se 1 (by rfl) ⟨211016, by rfl⟩ : syracuseStep 281355 = 422033) B422033
theorem B1198871 : Blo 279826 1198871 := bstep (se 1 (by rfl) ⟨899153, by rfl⟩ : syracuseStep 1198871 = 1798307) B1798307
theorem B281367 : Blo 279826 281367 := bstep (se 1 (by rfl) ⟨211025, by rfl⟩ : syracuseStep 281367 = 422051) B422051
theorem B281387 : Blo 279826 281387 := bstep (se 1 (by rfl) ⟨211040, by rfl⟩ : syracuseStep 281387 = 422081) B422081
theorem B281399 : Blo 279826 281399 := bstep (se 1 (by rfl) ⟨211049, by rfl⟩ : syracuseStep 281399 = 422099) B422099
theorem B281419 : Blo 279826 281419 := bstep (se 1 (by rfl) ⟨211064, by rfl⟩ : syracuseStep 281419 = 422129) B422129
theorem B281431 : Blo 279826 281431 := bstep (se 1 (by rfl) ⟨211073, by rfl⟩ : syracuseStep 281431 = 422147) B422147
theorem B281451 : Blo 279826 281451 := bstep (se 1 (by rfl) ⟨211088, by rfl⟩ : syracuseStep 281451 = 422177) B422177
theorem B281463 : Blo 279826 281463 := bstep (se 1 (by rfl) ⟨211097, by rfl⟩ : syracuseStep 281463 = 422195) B422195
theorem B281483 : Blo 279826 281483 := bstep (se 1 (by rfl) ⟨211112, by rfl⟩ : syracuseStep 281483 = 422225) B422225
theorem B281495 : Blo 279826 281495 := bstep (se 1 (by rfl) ⟨211121, by rfl⟩ : syracuseStep 281495 = 422243) B422243
theorem B281515 : Blo 279826 281515 := bstep (se 1 (by rfl) ⟨211136, by rfl⟩ : syracuseStep 281515 = 422273) B422273
theorem B2411441 : Blo 279826 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B281527 : Blo 279826 281527 := bstep (se 1 (by rfl) ⟨211145, by rfl⟩ : syracuseStep 281527 = 422291) B422291
theorem B281547 : Blo 279826 281547 := bstep (se 1 (by rfl) ⟨211160, by rfl⟩ : syracuseStep 281547 = 422321) B422321
theorem B281559 : Blo 279826 281559 := bstep (se 1 (by rfl) ⟨211169, by rfl⟩ : syracuseStep 281559 = 422339) B422339
theorem B281579 : Blo 279826 281579 := bstep (se 1 (by rfl) ⟨211184, by rfl⟩ : syracuseStep 281579 = 422369) B422369
theorem B281591 : Blo 279826 281591 := bstep (se 1 (by rfl) ⟨211193, by rfl⟩ : syracuseStep 281591 = 422387) B422387
theorem B281611 : Blo 279826 281611 := bstep (se 1 (by rfl) ⟨211208, by rfl⟩ : syracuseStep 281611 = 422417) B422417
theorem B281623 : Blo 279826 281623 := bstep (se 1 (by rfl) ⟨211217, by rfl⟩ : syracuseStep 281623 = 422435) B422435
theorem B281643 : Blo 279826 281643 := bstep (se 1 (by rfl) ⟨211232, by rfl⟩ : syracuseStep 281643 = 422465) B422465
theorem B281655 : Blo 279826 281655 := bstep (se 1 (by rfl) ⟨211241, by rfl⟩ : syracuseStep 281655 = 422483) B422483
theorem B281675 : Blo 279826 281675 := bstep (se 1 (by rfl) ⟨211256, by rfl⟩ : syracuseStep 281675 = 422513) B422513
theorem B281687 : Blo 279826 281687 := bstep (se 1 (by rfl) ⟨211265, by rfl⟩ : syracuseStep 281687 = 422531) B422531
theorem B281707 : Blo 279826 281707 := bstep (se 1 (by rfl) ⟨211280, by rfl⟩ : syracuseStep 281707 = 422561) B422561
theorem B281719 : Blo 279826 281719 := bstep (se 1 (by rfl) ⟨211289, by rfl⟩ : syracuseStep 281719 = 422579) B422579
theorem B4574339 : Blo 279826 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B281739 : Blo 279826 281739 := bstep (se 1 (by rfl) ⟨211304, by rfl⟩ : syracuseStep 281739 = 422609) B422609
theorem B281751 : Blo 279826 281751 := bstep (se 1 (by rfl) ⟨211313, by rfl⟩ : syracuseStep 281751 = 422627) B422627
theorem B281771 : Blo 279826 281771 := bstep (se 1 (by rfl) ⟨211328, by rfl⟩ : syracuseStep 281771 = 422657) B422657
theorem B281783 : Blo 279826 281783 := bstep (se 1 (by rfl) ⟨211337, by rfl⟩ : syracuseStep 281783 = 422675) B422675
theorem B281803 : Blo 279826 281803 := bstep (se 1 (by rfl) ⟨211352, by rfl⟩ : syracuseStep 281803 = 422705) B422705
theorem B281815 : Blo 279826 281815 := bstep (se 1 (by rfl) ⟨211361, by rfl⟩ : syracuseStep 281815 = 422723) B422723
theorem B281835 : Blo 279826 281835 := bstep (se 1 (by rfl) ⟨211376, by rfl⟩ : syracuseStep 281835 = 422753) B422753
theorem B281847 : Blo 279826 281847 := bstep (se 1 (by rfl) ⟨211385, by rfl⟩ : syracuseStep 281847 = 422771) B422771
theorem B281867 : Blo 279826 281867 := bstep (se 1 (by rfl) ⟨211400, by rfl⟩ : syracuseStep 281867 = 422801) B422801
theorem B281879 : Blo 279826 281879 := bstep (se 1 (by rfl) ⟨211409, by rfl⟩ : syracuseStep 281879 = 422819) B422819
theorem B478487 : Blo 279826 478487 := bstep (se 1 (by rfl) ⟨358865, by rfl⟩ : syracuseStep 478487 = 717731) B717731
theorem B281899 : Blo 279826 281899 := bstep (se 1 (by rfl) ⟨211424, by rfl⟩ : syracuseStep 281899 = 422849) B422849
theorem B281911 : Blo 279826 281911 := bstep (se 1 (by rfl) ⟨211433, by rfl⟩ : syracuseStep 281911 = 422867) B422867
theorem B281931 : Blo 279826 281931 := bstep (se 1 (by rfl) ⟨211448, by rfl⟩ : syracuseStep 281931 = 422897) B422897
theorem B281943 : Blo 279826 281943 := bstep (se 1 (by rfl) ⟨211457, by rfl⟩ : syracuseStep 281943 = 422915) B422915
theorem B281963 : Blo 279826 281963 := bstep (se 1 (by rfl) ⟨211472, by rfl⟩ : syracuseStep 281963 = 422945) B422945
theorem B281975 : Blo 279826 281975 := bstep (se 1 (by rfl) ⟨211481, by rfl⟩ : syracuseStep 281975 = 422963) B422963
theorem B281995 : Blo 279826 281995 := bstep (se 1 (by rfl) ⟨211496, by rfl⟩ : syracuseStep 281995 = 422993) B422993
theorem B282007 : Blo 279826 282007 := bstep (se 1 (by rfl) ⟨211505, by rfl⟩ : syracuseStep 282007 = 423011) B423011
theorem B478615 : Blo 279826 478615 := bstep (se 1 (by rfl) ⟨358961, by rfl⟩ : syracuseStep 478615 = 717923) B717923
theorem B282027 : Blo 279826 282027 := bstep (se 1 (by rfl) ⟨211520, by rfl⟩ : syracuseStep 282027 = 423041) B423041
theorem B282039 : Blo 279826 282039 := bstep (se 1 (by rfl) ⟨211529, by rfl⟩ : syracuseStep 282039 = 423059) B423059
theorem B478667 : Blo 279826 478667 := bstep (se 1 (by rfl) ⟨359000, by rfl⟩ : syracuseStep 478667 = 718001) B718001
theorem B282059 : Blo 279826 282059 := bstep (se 1 (by rfl) ⟨211544, by rfl⟩ : syracuseStep 282059 = 423089) B423089
theorem B282071 : Blo 279826 282071 := bstep (se 1 (by rfl) ⟨211553, by rfl⟩ : syracuseStep 282071 = 423107) B423107
theorem B511447 : Blo 279826 511447 := bstep (se 1 (by rfl) ⟨383585, by rfl⟩ : syracuseStep 511447 = 767171) B767171
theorem B806365 : Blo 279826 806365 := bstep (se 3 (by rfl) ⟨151193, by rfl⟩ : syracuseStep 806365 = 302387) B302387
theorem B282091 : Blo 279826 282091 := bstep (se 1 (by rfl) ⟨211568, by rfl⟩ : syracuseStep 282091 = 423137) B423137
theorem B282103 : Blo 279826 282103 := bstep (se 1 (by rfl) ⟨211577, by rfl⟩ : syracuseStep 282103 = 423155) B423155
theorem B282123 : Blo 279826 282123 := bstep (se 1 (by rfl) ⟨211592, by rfl⟩ : syracuseStep 282123 = 423185) B423185
theorem B282135 : Blo 279826 282135 := bstep (se 1 (by rfl) ⟨211601, by rfl⟩ : syracuseStep 282135 = 423203) B423203
theorem B314923 : Blo 279826 314923 := bstep (se 1 (by rfl) ⟨236192, by rfl⟩ : syracuseStep 314923 = 472385) B472385
theorem B282155 : Blo 279826 282155 := bstep (se 1 (by rfl) ⟨211616, by rfl⟩ : syracuseStep 282155 = 423233) B423233
theorem B282167 : Blo 279826 282167 := bstep (se 1 (by rfl) ⟨211625, by rfl⟩ : syracuseStep 282167 = 423251) B423251
theorem B282187 : Blo 279826 282187 := bstep (se 1 (by rfl) ⟨211640, by rfl⟩ : syracuseStep 282187 = 423281) B423281
theorem B380503 : Blo 279826 380503 := bstep (se 1 (by rfl) ⟨285377, by rfl⟩ : syracuseStep 380503 = 570755) B570755
theorem B282199 : Blo 279826 282199 := bstep (se 1 (by rfl) ⟨211649, by rfl⟩ : syracuseStep 282199 = 423299) B423299
theorem B2412125 : Blo 279826 2412125 := bstep (se 3 (by rfl) ⟨452273, by rfl⟩ : syracuseStep 2412125 = 904547) B904547
theorem B1363549 : Blo 279826 1363549 := bstep (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) B511331
theorem B282219 : Blo 279826 282219 := bstep (se 1 (by rfl) ⟨211664, by rfl⟩ : syracuseStep 282219 = 423329) B423329
theorem B282231 : Blo 279826 282231 := bstep (se 1 (by rfl) ⟨211673, by rfl⟩ : syracuseStep 282231 = 423347) B423347
theorem B282251 : Blo 279826 282251 := bstep (se 1 (by rfl) ⟨211688, by rfl⟩ : syracuseStep 282251 = 423377) B423377
theorem B315031 : Blo 279826 315031 := bstep (se 1 (by rfl) ⟨236273, by rfl⟩ : syracuseStep 315031 = 472547) B472547
theorem B282263 : Blo 279826 282263 := bstep (se 1 (by rfl) ⟨211697, by rfl⟩ : syracuseStep 282263 = 423395) B423395
theorem B282283 : Blo 279826 282283 := bstep (se 1 (by rfl) ⟨211712, by rfl⟩ : syracuseStep 282283 = 423425) B423425
theorem B282295 : Blo 279826 282295 := bstep (se 1 (by rfl) ⟨211721, by rfl⟩ : syracuseStep 282295 = 423443) B423443
theorem B806593 : Blo 279826 806593 := bstep (se 2 (by rfl) ⟨302472, by rfl⟩ : syracuseStep 806593 = 604945) B604945
theorem B282315 : Blo 279826 282315 := bstep (se 1 (by rfl) ⟨211736, by rfl⟩ : syracuseStep 282315 = 423473) B423473
theorem B282327 : Blo 279826 282327 := bstep (se 1 (by rfl) ⟨211745, by rfl⟩ : syracuseStep 282327 = 423491) B423491
theorem B380633 : Blo 279826 380633 := bstep (se 2 (by rfl) ⟨142737, by rfl⟩ : syracuseStep 380633 = 285475) B285475
theorem B282347 : Blo 279826 282347 := bstep (se 1 (by rfl) ⟨211760, by rfl⟩ : syracuseStep 282347 = 423521) B423521
theorem B282359 : Blo 279826 282359 := bstep (se 1 (by rfl) ⟨211769, by rfl⟩ : syracuseStep 282359 = 423539) B423539
theorem B282379 : Blo 279826 282379 := bstep (se 1 (by rfl) ⟨211784, by rfl⟩ : syracuseStep 282379 = 423569) B423569
theorem B282391 : Blo 279826 282391 := bstep (se 1 (by rfl) ⟨211793, by rfl⟩ : syracuseStep 282391 = 423587) B423587
theorem B282411 : Blo 279826 282411 := bstep (se 1 (by rfl) ⟨211808, by rfl⟩ : syracuseStep 282411 = 423617) B423617
theorem B3624749 : Blo 279826 3624749 := bstep (se 3 (by rfl) ⟨679640, by rfl⟩ : syracuseStep 3624749 = 1359281) B1359281
theorem B282423 : Blo 279826 282423 := bstep (se 1 (by rfl) ⟨211817, by rfl⟩ : syracuseStep 282423 = 423635) B423635
theorem B315211 : Blo 279826 315211 := bstep (se 1 (by rfl) ⟨236408, by rfl⟩ : syracuseStep 315211 = 472817) B472817
theorem B282443 : Blo 279826 282443 := bstep (se 1 (by rfl) ⟨211832, by rfl⟩ : syracuseStep 282443 = 423665) B423665
theorem B282455 : Blo 279826 282455 := bstep (se 1 (by rfl) ⟨211841, by rfl⟩ : syracuseStep 282455 = 423683) B423683
theorem B282475 : Blo 279826 282475 := bstep (se 1 (by rfl) ⟨211856, by rfl⟩ : syracuseStep 282475 = 423713) B423713
theorem B282487 : Blo 279826 282487 := bstep (se 1 (by rfl) ⟨211865, by rfl⟩ : syracuseStep 282487 = 423731) B423731
theorem B282507 : Blo 279826 282507 := bstep (se 1 (by rfl) ⟨211880, by rfl⟩ : syracuseStep 282507 = 423761) B423761
theorem B282519 : Blo 279826 282519 := bstep (se 1 (by rfl) ⟨211889, by rfl⟩ : syracuseStep 282519 = 423779) B423779
theorem B905111 : Blo 279826 905111 := bstep (se 1 (by rfl) ⟨678833, by rfl⟩ : syracuseStep 905111 = 1357667) B1357667
theorem B282539 : Blo 279826 282539 := bstep (se 1 (by rfl) ⟨211904, by rfl⟩ : syracuseStep 282539 = 423809) B423809
theorem B315319 : Blo 279826 315319 := bstep (se 1 (by rfl) ⟨236489, by rfl⟩ : syracuseStep 315319 = 472979) B472979
theorem B282551 : Blo 279826 282551 := bstep (se 1 (by rfl) ⟨211913, by rfl⟩ : syracuseStep 282551 = 423827) B423827
theorem B282571 : Blo 279826 282571 := bstep (se 1 (by rfl) ⟨211928, by rfl⟩ : syracuseStep 282571 = 423857) B423857
theorem B282583 : Blo 279826 282583 := bstep (se 1 (by rfl) ⟨211937, by rfl⟩ : syracuseStep 282583 = 423875) B423875
theorem B282603 : Blo 279826 282603 := bstep (se 1 (by rfl) ⟨211952, by rfl⟩ : syracuseStep 282603 = 423905) B423905
theorem B282615 : Blo 279826 282615 := bstep (se 1 (by rfl) ⟨211961, by rfl⟩ : syracuseStep 282615 = 423923) B423923
theorem B282635 : Blo 279826 282635 := bstep (se 1 (by rfl) ⟨211976, by rfl⟩ : syracuseStep 282635 = 423953) B423953
theorem B282647 : Blo 279826 282647 := bstep (se 1 (by rfl) ⟨211985, by rfl⟩ : syracuseStep 282647 = 423971) B423971
theorem B806935 : Blo 279826 806935 := bstep (se 1 (by rfl) ⟨605201, by rfl⟩ : syracuseStep 806935 = 1210403) B1210403
theorem B282667 : Blo 279826 282667 := bstep (se 1 (by rfl) ⟨212000, by rfl⟩ : syracuseStep 282667 = 424001) B424001
theorem B708659 : Blo 279826 708659 := bstep (se 1 (by rfl) ⟨531494, by rfl⟩ : syracuseStep 708659 = 1062989) B1062989
theorem B282679 : Blo 279826 282679 := bstep (se 1 (by rfl) ⟨212009, by rfl⟩ : syracuseStep 282679 = 424019) B424019
theorem B282699 : Blo 279826 282699 := bstep (se 1 (by rfl) ⟨212024, by rfl⟩ : syracuseStep 282699 = 424049) B424049
theorem B282711 : Blo 279826 282711 := bstep (se 1 (by rfl) ⟨212033, by rfl⟩ : syracuseStep 282711 = 424067) B424067
theorem B315499 : Blo 279826 315499 := bstep (se 1 (by rfl) ⟨236624, by rfl⟩ : syracuseStep 315499 = 473249) B473249
theorem B282731 : Blo 279826 282731 := bstep (se 1 (by rfl) ⟨212048, by rfl⟩ : syracuseStep 282731 = 424097) B424097
theorem B282743 : Blo 279826 282743 := bstep (se 1 (by rfl) ⟨212057, by rfl⟩ : syracuseStep 282743 = 424115) B424115
theorem B282763 : Blo 279826 282763 := bstep (se 1 (by rfl) ⟨212072, by rfl⟩ : syracuseStep 282763 = 424145) B424145
theorem B544907 : Blo 279826 544907 := bstep (se 1 (by rfl) ⟨408680, by rfl⟩ : syracuseStep 544907 = 817361) B817361
theorem B282775 : Blo 279826 282775 := bstep (se 1 (by rfl) ⟨212081, by rfl⟩ : syracuseStep 282775 = 424163) B424163
theorem B282795 : Blo 279826 282795 := bstep (se 1 (by rfl) ⟨212096, by rfl⟩ : syracuseStep 282795 = 424193) B424193
theorem B282807 : Blo 279826 282807 := bstep (se 1 (by rfl) ⟨212105, by rfl⟩ : syracuseStep 282807 = 424211) B424211
theorem B282827 : Blo 279826 282827 := bstep (se 1 (by rfl) ⟨212120, by rfl⟩ : syracuseStep 282827 = 424241) B424241
theorem B315607 : Blo 279826 315607 := bstep (se 1 (by rfl) ⟨236705, by rfl⟩ : syracuseStep 315607 = 473411) B473411
theorem B282839 : Blo 279826 282839 := bstep (se 1 (by rfl) ⟨212129, by rfl⟩ : syracuseStep 282839 = 424259) B424259
theorem B282859 : Blo 279826 282859 := bstep (se 1 (by rfl) ⟨212144, by rfl⟩ : syracuseStep 282859 = 424289) B424289
theorem B282871 : Blo 279826 282871 := bstep (se 1 (by rfl) ⟨212153, by rfl⟩ : syracuseStep 282871 = 424307) B424307
theorem B282891 : Blo 279826 282891 := bstep (se 1 (by rfl) ⟨212168, by rfl⟩ : syracuseStep 282891 = 424337) B424337
theorem B282903 : Blo 279826 282903 := bstep (se 1 (by rfl) ⟨212177, by rfl⟩ : syracuseStep 282903 = 424355) B424355
theorem B282923 : Blo 279826 282923 := bstep (se 1 (by rfl) ⟨212192, by rfl⟩ : syracuseStep 282923 = 424385) B424385
theorem B282935 : Blo 279826 282935 := bstep (se 1 (by rfl) ⟨212201, by rfl⟩ : syracuseStep 282935 = 424403) B424403
theorem B282955 : Blo 279826 282955 := bstep (se 1 (by rfl) ⟨212216, by rfl⟩ : syracuseStep 282955 = 424433) B424433
theorem B282967 : Blo 279826 282967 := bstep (se 1 (by rfl) ⟨212225, by rfl⟩ : syracuseStep 282967 = 424451) B424451
theorem B282987 : Blo 279826 282987 := bstep (se 1 (by rfl) ⟨212240, by rfl⟩ : syracuseStep 282987 = 424481) B424481
theorem B282999 : Blo 279826 282999 := bstep (se 1 (by rfl) ⟨212249, by rfl⟩ : syracuseStep 282999 = 424499) B424499
theorem B315787 : Blo 279826 315787 := bstep (se 1 (by rfl) ⟨236840, by rfl⟩ : syracuseStep 315787 = 473681) B473681
theorem B283019 : Blo 279826 283019 := bstep (se 1 (by rfl) ⟨212264, by rfl⟩ : syracuseStep 283019 = 424529) B424529
theorem B283031 : Blo 279826 283031 := bstep (se 1 (by rfl) ⟨212273, by rfl⟩ : syracuseStep 283031 = 424547) B424547
theorem B283051 : Blo 279826 283051 := bstep (se 1 (by rfl) ⟨212288, by rfl⟩ : syracuseStep 283051 = 424577) B424577
theorem B905651 : Blo 279826 905651 := bstep (se 1 (by rfl) ⟨679238, by rfl⟩ : syracuseStep 905651 = 1358477) B1358477
theorem B283063 : Blo 279826 283063 := bstep (se 1 (by rfl) ⟨212297, by rfl⟩ : syracuseStep 283063 = 424595) B424595
theorem B283083 : Blo 279826 283083 := bstep (se 1 (by rfl) ⟨212312, by rfl⟩ : syracuseStep 283083 = 424625) B424625
theorem B283095 : Blo 279826 283095 := bstep (se 1 (by rfl) ⟨212321, by rfl⟩ : syracuseStep 283095 = 424643) B424643
theorem B283115 : Blo 279826 283115 := bstep (se 1 (by rfl) ⟨212336, by rfl⟩ : syracuseStep 283115 = 424673) B424673
theorem B315895 : Blo 279826 315895 := bstep (se 1 (by rfl) ⟨236921, by rfl⟩ : syracuseStep 315895 = 473843) B473843
theorem B283127 : Blo 279826 283127 := bstep (se 1 (by rfl) ⟨212345, by rfl⟩ : syracuseStep 283127 = 424691) B424691
theorem B283147 : Blo 279826 283147 := bstep (se 1 (by rfl) ⟨212360, by rfl⟩ : syracuseStep 283147 = 424721) B424721
theorem B283159 : Blo 279826 283159 := bstep (se 1 (by rfl) ⟨212369, by rfl⟩ : syracuseStep 283159 = 424739) B424739
theorem B283179 : Blo 279826 283179 := bstep (se 1 (by rfl) ⟨212384, by rfl⟩ : syracuseStep 283179 = 424769) B424769
theorem B283191 : Blo 279826 283191 := bstep (se 1 (by rfl) ⟨212393, by rfl⟩ : syracuseStep 283191 = 424787) B424787
theorem B709195 : Blo 279826 709195 := bstep (se 1 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 709195 = 1063793) B1063793
theorem B283211 : Blo 279826 283211 := bstep (se 1 (by rfl) ⟨212408, by rfl⟩ : syracuseStep 283211 = 424817) B424817
theorem B283223 : Blo 279826 283223 := bstep (se 1 (by rfl) ⟨212417, by rfl⟩ : syracuseStep 283223 = 424835) B424835
theorem B283243 : Blo 279826 283243 := bstep (se 1 (by rfl) ⟨212432, by rfl⟩ : syracuseStep 283243 = 424865) B424865
theorem B283255 : Blo 279826 283255 := bstep (se 1 (by rfl) ⟨212441, by rfl⟩ : syracuseStep 283255 = 424883) B424883
theorem B283275 : Blo 279826 283275 := bstep (se 1 (by rfl) ⟨212456, by rfl⟩ : syracuseStep 283275 = 424913) B424913
theorem B283287 : Blo 279826 283287 := bstep (se 1 (by rfl) ⟨212465, by rfl⟩ : syracuseStep 283287 = 424931) B424931
theorem B316075 : Blo 279826 316075 := bstep (se 1 (by rfl) ⟨237056, by rfl⟩ : syracuseStep 316075 = 474113) B474113
theorem B283307 : Blo 279826 283307 := bstep (se 1 (by rfl) ⟨212480, by rfl⟩ : syracuseStep 283307 = 424961) B424961
theorem B283319 : Blo 279826 283319 := bstep (se 1 (by rfl) ⟨212489, by rfl⟩ : syracuseStep 283319 = 424979) B424979
theorem B283339 : Blo 279826 283339 := bstep (se 1 (by rfl) ⟨212504, by rfl⟩ : syracuseStep 283339 = 425009) B425009
theorem B283351 : Blo 279826 283351 := bstep (se 1 (by rfl) ⟨212513, by rfl⟩ : syracuseStep 283351 = 425027) B425027
theorem B709337 : Blo 279826 709337 := bstep (se 2 (by rfl) ⟨266001, by rfl⟩ : syracuseStep 709337 = 532003) B532003
theorem B807641 : Blo 279826 807641 := bstep (se 2 (by rfl) ⟨302865, by rfl⟩ : syracuseStep 807641 = 605731) B605731
theorem B283371 : Blo 279826 283371 := bstep (se 1 (by rfl) ⟨212528, by rfl⟩ : syracuseStep 283371 = 425057) B425057
theorem B283383 : Blo 279826 283383 := bstep (se 1 (by rfl) ⟨212537, by rfl⟩ : syracuseStep 283383 = 425075) B425075
theorem B283403 : Blo 279826 283403 := bstep (se 1 (by rfl) ⟨212552, by rfl⟩ : syracuseStep 283403 = 425105) B425105
theorem B316183 : Blo 279826 316183 := bstep (se 1 (by rfl) ⟨237137, by rfl⟩ : syracuseStep 316183 = 474275) B474275
theorem B283415 : Blo 279826 283415 := bstep (se 1 (by rfl) ⟨212561, by rfl⟩ : syracuseStep 283415 = 425123) B425123
theorem B283435 : Blo 279826 283435 := bstep (se 1 (by rfl) ⟨212576, by rfl⟩ : syracuseStep 283435 = 425153) B425153
theorem B283447 : Blo 279826 283447 := bstep (se 1 (by rfl) ⟨212585, by rfl⟩ : syracuseStep 283447 = 425171) B425171
theorem B1594187 : Blo 279826 1594187 := bstep (se 1 (by rfl) ⟨1195640, by rfl⟩ : syracuseStep 1594187 = 2391281) B2391281
theorem B283467 : Blo 279826 283467 := bstep (se 1 (by rfl) ⟨212600, by rfl⟩ : syracuseStep 283467 = 425201) B425201
theorem B283479 : Blo 279826 283479 := bstep (se 1 (by rfl) ⟨212609, by rfl⟩ : syracuseStep 283479 = 425219) B425219
theorem B283499 : Blo 279826 283499 := bstep (se 1 (by rfl) ⟨212624, by rfl⟩ : syracuseStep 283499 = 425249) B425249
theorem B3855221 : Blo 279826 3855221 := bstep (se 5 (by rfl) ⟨180713, by rfl⟩ : syracuseStep 3855221 = 361427) B361427
theorem B283511 : Blo 279826 283511 := bstep (se 1 (by rfl) ⟨212633, by rfl⟩ : syracuseStep 283511 = 425267) B425267
theorem B283531 : Blo 279826 283531 := bstep (se 1 (by rfl) ⟨212648, by rfl⟩ : syracuseStep 283531 = 425297) B425297
theorem B283543 : Blo 279826 283543 := bstep (se 1 (by rfl) ⟨212657, by rfl⟩ : syracuseStep 283543 = 425315) B425315
theorem B283563 : Blo 279826 283563 := bstep (se 1 (by rfl) ⟨212672, by rfl⟩ : syracuseStep 283563 = 425345) B425345
theorem B2053043 : Blo 279826 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B283575 : Blo 279826 283575 := bstep (se 1 (by rfl) ⟨212681, by rfl⟩ : syracuseStep 283575 = 425363) B425363
theorem B316363 : Blo 279826 316363 := bstep (se 1 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 316363 = 474545) B474545
theorem B283595 : Blo 279826 283595 := bstep (se 1 (by rfl) ⟨212696, by rfl⟩ : syracuseStep 283595 = 425393) B425393
theorem B283607 : Blo 279826 283607 := bstep (se 1 (by rfl) ⟨212705, by rfl⟩ : syracuseStep 283607 = 425411) B425411
theorem B283627 : Blo 279826 283627 := bstep (se 1 (by rfl) ⟨212720, by rfl⟩ : syracuseStep 283627 = 425441) B425441
theorem B283639 : Blo 279826 283639 := bstep (se 1 (by rfl) ⟨212729, by rfl⟩ : syracuseStep 283639 = 425459) B425459
theorem B283659 : Blo 279826 283659 := bstep (se 1 (by rfl) ⟨212744, by rfl⟩ : syracuseStep 283659 = 425489) B425489
theorem B283671 : Blo 279826 283671 := bstep (se 1 (by rfl) ⟨212753, by rfl⟩ : syracuseStep 283671 = 425507) B425507
theorem B283691 : Blo 279826 283691 := bstep (se 1 (by rfl) ⟨212768, by rfl⟩ : syracuseStep 283691 = 425537) B425537
theorem B316471 : Blo 279826 316471 := bstep (se 1 (by rfl) ⟨237353, by rfl⟩ : syracuseStep 316471 = 474707) B474707
theorem B283703 : Blo 279826 283703 := bstep (se 1 (by rfl) ⟨212777, by rfl⟩ : syracuseStep 283703 = 425555) B425555
theorem B283723 : Blo 279826 283723 := bstep (se 1 (by rfl) ⟨212792, by rfl⟩ : syracuseStep 283723 = 425585) B425585
theorem B283735 : Blo 279826 283735 := bstep (se 1 (by rfl) ⟨212801, by rfl⟩ : syracuseStep 283735 = 425603) B425603
theorem B906329 : Blo 279826 906329 := bstep (se 2 (by rfl) ⟨339873, by rfl⟩ : syracuseStep 906329 = 679747) B679747
theorem B1430621 : Blo 279826 1430621 := bstep (se 3 (by rfl) ⟨268241, by rfl⟩ : syracuseStep 1430621 = 536483) B536483
theorem B283755 : Blo 279826 283755 := bstep (se 1 (by rfl) ⟨212816, by rfl⟩ : syracuseStep 283755 = 425633) B425633
theorem B283767 : Blo 279826 283767 := bstep (se 1 (by rfl) ⟨212825, by rfl⟩ : syracuseStep 283767 = 425651) B425651
theorem B283787 : Blo 279826 283787 := bstep (se 1 (by rfl) ⟨212840, by rfl⟩ : syracuseStep 283787 = 425681) B425681
theorem B283799 : Blo 279826 283799 := bstep (se 1 (by rfl) ⟨212849, by rfl⟩ : syracuseStep 283799 = 425699) B425699
theorem B283819 : Blo 279826 283819 := bstep (se 1 (by rfl) ⟨212864, by rfl⟩ : syracuseStep 283819 = 425729) B425729
theorem B1201331 : Blo 279826 1201331 := bstep (se 1 (by rfl) ⟨900998, by rfl⟩ : syracuseStep 1201331 = 1801997) B1801997
theorem B316651 : Blo 279826 316651 := bstep (se 1 (by rfl) ⟨237488, by rfl⟩ : syracuseStep 316651 = 474977) B474977
theorem B1201483 : Blo 279826 1201483 := bstep (se 1 (by rfl) ⟨901112, by rfl⟩ : syracuseStep 1201483 = 1802225) B1802225
theorem B283991 : Blo 279826 283991 := bstep (se 1 (by rfl) ⟨212993, by rfl⟩ : syracuseStep 283991 = 425987) B425987
theorem B316759 : Blo 279826 316759 := bstep (se 1 (by rfl) ⟨237569, by rfl⟩ : syracuseStep 316759 = 475139) B475139
theorem B1201553 : Blo 279826 1201553 := bstep (se 2 (by rfl) ⟨450582, by rfl⟩ : syracuseStep 1201553 = 901165) B901165
theorem B316939 : Blo 279826 316939 := bstep (se 1 (by rfl) ⟨237704, by rfl⟩ : syracuseStep 316939 = 475409) B475409
theorem B710167 : Blo 279826 710167 := bstep (se 1 (by rfl) ⟨532625, by rfl⟩ : syracuseStep 710167 = 1065251) B1065251
theorem B317047 : Blo 279826 317047 := bstep (se 1 (by rfl) ⟨237785, by rfl⟩ : syracuseStep 317047 = 475571) B475571
theorem B1070765 : Blo 279826 1070765 := bstep (se 3 (by rfl) ⟨200768, by rfl⟩ : syracuseStep 1070765 = 401537) B401537
theorem B4085453 : Blo 279826 4085453 := bstep (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) B1532045
theorem B317227 : Blo 279826 317227 := bstep (se 1 (by rfl) ⟨237920, by rfl⟩ : syracuseStep 317227 = 475841) B475841
theorem B317335 : Blo 279826 317335 := bstep (se 1 (by rfl) ⟨238001, by rfl⟩ : syracuseStep 317335 = 476003) B476003
theorem B710603 : Blo 279826 710603 := bstep (se 1 (by rfl) ⟨532952, by rfl⟩ : syracuseStep 710603 = 1065905) B1065905
theorem B481241 : Blo 279826 481241 := bstep (se 2 (by rfl) ⟨180465, by rfl⟩ : syracuseStep 481241 = 360931) B360931
theorem B677911 : Blo 279826 677911 := bstep (se 1 (by rfl) ⟨508433, by rfl⟩ : syracuseStep 677911 = 1016867) B1016867
theorem B2152493 : Blo 279826 2152493 := bstep (se 3 (by rfl) ⟨403592, by rfl⟩ : syracuseStep 2152493 = 807185) B807185
theorem B317515 : Blo 279826 317515 := bstep (se 1 (by rfl) ⟨238136, by rfl⟩ : syracuseStep 317515 = 476273) B476273
theorem B2021507 : Blo 279826 2021507 := bstep (se 1 (by rfl) ⟨1516130, by rfl⟩ : syracuseStep 2021507 = 3032261) B3032261
theorem B317623 : Blo 279826 317623 := bstep (se 1 (by rfl) ⟨238217, by rfl⟩ : syracuseStep 317623 = 476435) B476435
theorem B907571 : Blo 279826 907571 := bstep (se 1 (by rfl) ⟨680678, by rfl⟩ : syracuseStep 907571 = 1361357) B1361357
theorem B710977 : Blo 279826 710977 := bstep (se 2 (by rfl) ⟨266616, by rfl⟩ : syracuseStep 710977 = 533233) B533233
theorem B2677093 : Blo 279826 2677093 := bstep (se 4 (by rfl) ⟨250977, by rfl⟩ : syracuseStep 2677093 = 501955) B501955
theorem B317803 : Blo 279826 317803 := bstep (se 1 (by rfl) ⟨238352, by rfl⟩ : syracuseStep 317803 = 476705) B476705
theorem B678295 : Blo 279826 678295 := bstep (se 1 (by rfl) ⟨508721, by rfl⟩ : syracuseStep 678295 = 1017443) B1017443
theorem B1071539 : Blo 279826 1071539 := bstep (se 1 (by rfl) ⟨803654, by rfl⟩ : syracuseStep 1071539 = 1607309) B1607309
theorem B317911 : Blo 279826 317911 := bstep (se 1 (by rfl) ⟨238433, by rfl⟩ : syracuseStep 317911 = 476867) B476867
theorem B318091 : Blo 279826 318091 := bstep (se 1 (by rfl) ⟨238568, by rfl⟩ : syracuseStep 318091 = 477137) B477137
theorem B318199 : Blo 279826 318199 := bstep (se 1 (by rfl) ⟨238649, by rfl⟩ : syracuseStep 318199 = 477299) B477299
theorem B711575 : Blo 279826 711575 := bstep (se 1 (by rfl) ⟨533681, by rfl⟩ : syracuseStep 711575 = 1067363) B1067363
theorem B318379 : Blo 279826 318379 := bstep (se 1 (by rfl) ⟨238784, by rfl⟩ : syracuseStep 318379 = 477569) B477569
theorem B646105 : Blo 279826 646105 := bstep (se 2 (by rfl) ⟨242289, by rfl⟩ : syracuseStep 646105 = 484579) B484579
theorem B318487 : Blo 279826 318487 := bstep (se 1 (by rfl) ⟨238865, by rfl⟩ : syracuseStep 318487 = 477731) B477731
theorem B1203245 : Blo 279826 1203245 := bstep (se 3 (by rfl) ⟨225608, by rfl⟩ : syracuseStep 1203245 = 451217) B451217
theorem B285751 : Blo 279826 285751 := bstep (se 1 (by rfl) ⟨214313, by rfl⟩ : syracuseStep 285751 = 428627) B428627
theorem B1432727 : Blo 279826 1432727 := bstep (se 1 (by rfl) ⟨1074545, by rfl⟩ : syracuseStep 1432727 = 2149091) B2149091
theorem B318667 : Blo 279826 318667 := bstep (se 1 (by rfl) ⟨239000, by rfl⟩ : syracuseStep 318667 = 478001) B478001
theorem B318775 : Blo 279826 318775 := bstep (se 1 (by rfl) ⟨239081, by rfl⟩ : syracuseStep 318775 = 478163) B478163
theorem B318955 : Blo 279826 318955 := bstep (se 1 (by rfl) ⟨239216, by rfl⟩ : syracuseStep 318955 = 478433) B478433
theorem B384599 : Blo 279826 384599 := bstep (se 1 (by rfl) ⟨288449, by rfl⟩ : syracuseStep 384599 = 576899) B576899
theorem B319063 : Blo 279826 319063 := bstep (se 1 (by rfl) ⟨239297, by rfl⟩ : syracuseStep 319063 = 478595) B478595
theorem B2612915 : Blo 279826 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B679603 : Blo 279826 679603 := bstep (se 1 (by rfl) ⟨509702, by rfl⟩ : syracuseStep 679603 = 1019405) B1019405
theorem B712385 : Blo 279826 712385 := bstep (se 2 (by rfl) ⟨267144, by rfl⟩ : syracuseStep 712385 = 534289) B534289
theorem B1203929 : Blo 279826 1203929 := bstep (se 2 (by rfl) ⟨451473, by rfl⟩ : syracuseStep 1203929 = 902947) B902947
theorem B319243 : Blo 279826 319243 := bstep (se 1 (by rfl) ⟨239432, by rfl⟩ : syracuseStep 319243 = 478865) B478865
theorem B1073027 : Blo 279826 1073027 := bstep (se 1 (by rfl) ⟨804770, by rfl⟩ : syracuseStep 1073027 = 1609541) B1609541
theorem B450775 : Blo 279826 450775 := bstep (se 1 (by rfl) ⟨338081, by rfl⟩ : syracuseStep 450775 = 676163) B676163
theorem B712921 : Blo 279826 712921 := bstep (se 2 (by rfl) ⟨267345, by rfl⟩ : syracuseStep 712921 = 534691) B534691
theorem B286967 : Blo 279826 286967 := bstep (se 1 (by rfl) ⟨215225, by rfl⟩ : syracuseStep 286967 = 430451) B430451
theorem B450839 : Blo 279826 450839 := bstep (se 1 (by rfl) ⟨338129, by rfl⟩ : syracuseStep 450839 = 676259) B676259
theorem B286999 : Blo 279826 286999 := bstep (se 1 (by rfl) ⟨215249, by rfl⟩ : syracuseStep 286999 = 430499) B430499
theorem B1827137 : Blo 279826 1827137 := bstep (se 2 (by rfl) ⟨685176, by rfl⟩ : syracuseStep 1827137 = 1370353) B1370353
theorem B1073483 : Blo 279826 1073483 := bstep (se 1 (by rfl) ⟨805112, by rfl⟩ : syracuseStep 1073483 = 1610225) B1610225
theorem B1073681 : Blo 279826 1073681 := bstep (se 2 (by rfl) ⟨402630, by rfl⟩ : syracuseStep 1073681 = 805261) B805261
theorem B2744867 : Blo 279826 2744867 := bstep (se 1 (by rfl) ⟨2058650, by rfl⟩ : syracuseStep 2744867 = 4117301) B4117301
theorem B451403 : Blo 279826 451403 := bstep (se 1 (by rfl) ⟨338552, by rfl⟩ : syracuseStep 451403 = 677105) B677105
theorem B877405 : Blo 279826 877405 := bstep (se 3 (by rfl) ⟨164513, by rfl⟩ : syracuseStep 877405 = 329027) B329027
theorem B1139629 : Blo 279826 1139629 := bstep (se 3 (by rfl) ⟨213680, by rfl⟩ : syracuseStep 1139629 = 427361) B427361
theorem B320503 : Blo 279826 320503 := bstep (se 1 (by rfl) ⟨240377, by rfl⟩ : syracuseStep 320503 = 480755) B480755
theorem B451595 : Blo 279826 451595 := bstep (se 1 (by rfl) ⟨338696, by rfl⟩ : syracuseStep 451595 = 677393) B677393
theorem B910529 : Blo 279826 910529 := bstep (se 2 (by rfl) ⟨341448, by rfl⟩ : syracuseStep 910529 = 682897) B682897
theorem B1074455 : Blo 279826 1074455 := bstep (se 1 (by rfl) ⟨805841, by rfl⟩ : syracuseStep 1074455 = 1611683) B1611683
theorem B714035 : Blo 279826 714035 := bstep (se 1 (by rfl) ⟨535526, by rfl⟩ : syracuseStep 714035 = 1071053) B1071053
theorem B2024797 : Blo 279826 2024797 := bstep (se 3 (by rfl) ⟨379649, by rfl⟩ : syracuseStep 2024797 = 759299) B759299
theorem B1795459 : Blo 279826 1795459 := bstep (se 1 (by rfl) ⟨1346594, by rfl⟩ : syracuseStep 1795459 = 2693189) B2693189
theorem B1074653 : Blo 279826 1074653 := bstep (se 3 (by rfl) ⟨201497, by rfl⟩ : syracuseStep 1074653 = 402995) B402995
theorem B3204683 : Blo 279826 3204683 := bstep (se 1 (by rfl) ⟨2403512, by rfl⟩ : syracuseStep 3204683 = 4807025) B4807025
theorem B714329 : Blo 279826 714329 := bstep (se 2 (by rfl) ⟨267873, by rfl⟩ : syracuseStep 714329 = 535747) B535747
theorem B1009369 : Blo 279826 1009369 := bstep (se 2 (by rfl) ⟨378513, by rfl⟩ : syracuseStep 1009369 = 757027) B757027
theorem B419801 : Blo 279826 419801 := bstep (se 2 (by rfl) ⟨157425, by rfl⟩ : syracuseStep 419801 = 314851) B314851
theorem B452569 : Blo 279826 452569 := bstep (se 2 (by rfl) ⟨169713, by rfl⟩ : syracuseStep 452569 = 339427) B339427
theorem B1009667 : Blo 279826 1009667 := bstep (se 1 (by rfl) ⟨757250, by rfl⟩ : syracuseStep 1009667 = 1514501) B1514501
theorem B419915 : Blo 279826 419915 := bstep (se 1 (by rfl) ⟨314936, by rfl⟩ : syracuseStep 419915 = 629873) B629873
theorem B419927 : Blo 279826 419927 := bstep (se 1 (by rfl) ⟨314945, by rfl⟩ : syracuseStep 419927 = 629891) B629891
theorem B419993 : Blo 279826 419993 := bstep (se 2 (by rfl) ⟨157497, by rfl⟩ : syracuseStep 419993 = 314995) B314995
theorem B420107 : Blo 279826 420107 := bstep (se 1 (by rfl) ⟨315080, by rfl⟩ : syracuseStep 420107 = 630161) B630161
theorem B420119 : Blo 279826 420119 := bstep (se 1 (by rfl) ⟨315089, by rfl⟩ : syracuseStep 420119 = 630179) B630179
theorem B944459 : Blo 279826 944459 := bstep (se 1 (by rfl) ⟨708344, by rfl⟩ : syracuseStep 944459 = 1416689) B1416689
theorem B420185 : Blo 279826 420185 := bstep (se 2 (by rfl) ⟨157569, by rfl⟩ : syracuseStep 420185 = 315139) B315139
theorem B321899 : Blo 279826 321899 := bstep (se 1 (by rfl) ⟨241424, by rfl⟩ : syracuseStep 321899 = 482849) B482849
theorem B453017 : Blo 279826 453017 := bstep (se 2 (by rfl) ⟨169881, by rfl⟩ : syracuseStep 453017 = 339763) B339763
theorem B420299 : Blo 279826 420299 := bstep (se 1 (by rfl) ⟨315224, by rfl⟩ : syracuseStep 420299 = 630449) B630449
theorem B420311 : Blo 279826 420311 := bstep (se 1 (by rfl) ⟨315233, by rfl⟩ : syracuseStep 420311 = 630467) B630467
theorem B354775 : Blo 279826 354775 := bstep (se 1 (by rfl) ⟨266081, by rfl⟩ : syracuseStep 354775 = 532163) B532163
theorem B420377 : Blo 279826 420377 := bstep (se 2 (by rfl) ⟨157641, by rfl⟩ : syracuseStep 420377 = 315283) B315283
theorem B944729 : Blo 279826 944729 := bstep (se 2 (by rfl) ⟨354273, by rfl⟩ : syracuseStep 944729 = 708547) B708547
theorem B1436291 : Blo 279826 1436291 := bstep (se 1 (by rfl) ⟨1077218, by rfl⟩ : syracuseStep 1436291 = 2154437) B2154437
theorem B420491 : Blo 279826 420491 := bstep (se 1 (by rfl) ⟨315368, by rfl⟩ : syracuseStep 420491 = 630737) B630737
theorem B420503 : Blo 279826 420503 := bstep (se 1 (by rfl) ⟨315377, by rfl⟩ : syracuseStep 420503 = 630755) B630755
theorem B420569 : Blo 279826 420569 := bstep (se 2 (by rfl) ⟨157713, by rfl⟩ : syracuseStep 420569 = 315427) B315427
theorem B584435 : Blo 279826 584435 := bstep (se 1 (by rfl) ⟨438326, by rfl⟩ : syracuseStep 584435 = 876653) B876653
theorem B3631877 : Blo 279826 3631877 := bstep (se 4 (by rfl) ⟨340488, by rfl⟩ : syracuseStep 3631877 = 680977) B680977
theorem B420683 : Blo 279826 420683 := bstep (se 1 (by rfl) ⟨315512, by rfl⟩ : syracuseStep 420683 = 631025) B631025
theorem B420695 : Blo 279826 420695 := bstep (se 1 (by rfl) ⟨315521, by rfl⟩ : syracuseStep 420695 = 631043) B631043
theorem B420761 : Blo 279826 420761 := bstep (se 2 (by rfl) ⟨157785, by rfl⟩ : syracuseStep 420761 = 315571) B315571
theorem B420875 : Blo 279826 420875 := bstep (se 1 (by rfl) ⟨315656, by rfl⟩ : syracuseStep 420875 = 631313) B631313
theorem B420887 : Blo 279826 420887 := bstep (se 1 (by rfl) ⟨315665, by rfl⟩ : syracuseStep 420887 = 631331) B631331
theorem B1207361 : Blo 279826 1207361 := bstep (se 2 (by rfl) ⟨452760, by rfl⟩ : syracuseStep 1207361 = 905521) B905521
theorem B420953 : Blo 279826 420953 := bstep (se 2 (by rfl) ⟨157857, by rfl⟩ : syracuseStep 420953 = 315715) B315715
theorem B421067 : Blo 279826 421067 := bstep (se 1 (by rfl) ⟨315800, by rfl⟩ : syracuseStep 421067 = 631601) B631601
theorem B715979 : Blo 279826 715979 := bstep (se 1 (by rfl) ⟨536984, by rfl⟩ : syracuseStep 715979 = 1073969) B1073969
theorem B421079 : Blo 279826 421079 := bstep (se 1 (by rfl) ⟨315809, by rfl⟩ : syracuseStep 421079 = 631619) B631619
theorem B945431 : Blo 279826 945431 := bstep (se 1 (by rfl) ⟨709073, by rfl⟩ : syracuseStep 945431 = 1418147) B1418147
theorem B421145 : Blo 279826 421145 := bstep (se 2 (by rfl) ⟨157929, by rfl⟩ : syracuseStep 421145 = 315859) B315859
theorem B1076611 : Blo 279826 1076611 := bstep (se 1 (by rfl) ⟨807458, by rfl⟩ : syracuseStep 1076611 = 1614917) B1614917
theorem B421259 : Blo 279826 421259 := bstep (se 1 (by rfl) ⟨315944, by rfl⟩ : syracuseStep 421259 = 631889) B631889
theorem B421271 : Blo 279826 421271 := bstep (se 1 (by rfl) ⟨315953, by rfl⟩ : syracuseStep 421271 = 631907) B631907
theorem B1207703 : Blo 279826 1207703 := bstep (se 1 (by rfl) ⟨905777, by rfl⟩ : syracuseStep 1207703 = 1811555) B1811555
theorem B421337 : Blo 279826 421337 := bstep (se 2 (by rfl) ⟨158001, by rfl⟩ : syracuseStep 421337 = 316003) B316003
theorem B421451 : Blo 279826 421451 := bstep (se 1 (by rfl) ⟨316088, by rfl⟩ : syracuseStep 421451 = 632177) B632177
theorem B421463 : Blo 279826 421463 := bstep (se 1 (by rfl) ⟨316097, by rfl⟩ : syracuseStep 421463 = 632195) B632195
theorem B421529 : Blo 279826 421529 := bstep (se 2 (by rfl) ⟨158073, by rfl⟩ : syracuseStep 421529 = 316147) B316147
theorem B1076915 : Blo 279826 1076915 := bstep (se 1 (by rfl) ⟨807686, by rfl⟩ : syracuseStep 1076915 = 1615373) B1615373
theorem B1994419 : Blo 279826 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B4091633 : Blo 279826 4091633 := bstep (se 2 (by rfl) ⟨1534362, by rfl⟩ : syracuseStep 4091633 = 3068725) B3068725
theorem B421643 : Blo 279826 421643 := bstep (se 1 (by rfl) ⟨316232, by rfl⟩ : syracuseStep 421643 = 632465) B632465
theorem B421655 : Blo 279826 421655 := bstep (se 1 (by rfl) ⟨316241, by rfl⟩ : syracuseStep 421655 = 632483) B632483
theorem B945971 : Blo 279826 945971 := bstep (se 1 (by rfl) ⟨709478, by rfl⟩ : syracuseStep 945971 = 1418957) B1418957
theorem B421721 : Blo 279826 421721 := bstep (se 2 (by rfl) ⟨158145, by rfl⟩ : syracuseStep 421721 = 316291) B316291
theorem B421835 : Blo 279826 421835 := bstep (se 1 (by rfl) ⟨316376, by rfl⟩ : syracuseStep 421835 = 632753) B632753
theorem B421847 : Blo 279826 421847 := bstep (se 1 (by rfl) ⟨316385, by rfl⟩ : syracuseStep 421847 = 632771) B632771
theorem B421913 : Blo 279826 421913 := bstep (se 2 (by rfl) ⟨158217, by rfl⟩ : syracuseStep 421913 = 316435) B316435
theorem B946241 : Blo 279826 946241 := bstep (se 2 (by rfl) ⟨354840, by rfl⟩ : syracuseStep 946241 = 709681) B709681
theorem B422027 : Blo 279826 422027 := bstep (se 1 (by rfl) ⟨316520, by rfl⟩ : syracuseStep 422027 = 633041) B633041
theorem B356491 : Blo 279826 356491 := bstep (se 1 (by rfl) ⟨267368, by rfl⟩ : syracuseStep 356491 = 534737) B534737
theorem B422039 : Blo 279826 422039 := bstep (se 1 (by rfl) ⟨316529, by rfl⟩ : syracuseStep 422039 = 633059) B633059
theorem B716951 : Blo 279826 716951 := bstep (se 1 (by rfl) ⟨537713, by rfl⟩ : syracuseStep 716951 = 1075427) B1075427
theorem B422105 : Blo 279826 422105 := bstep (se 2 (by rfl) ⟨158289, by rfl⟩ : syracuseStep 422105 = 316579) B316579
theorem B1994969 : Blo 279826 1994969 := bstep (se 2 (by rfl) ⟨748113, by rfl⟩ : syracuseStep 1994969 = 1496227) B1496227
theorem B1208627 : Blo 279826 1208627 := bstep (se 1 (by rfl) ⟨906470, by rfl⟩ : syracuseStep 1208627 = 1812941) B1812941
theorem B1077569 : Blo 279826 1077569 := bstep (se 2 (by rfl) ⟨404088, by rfl⟩ : syracuseStep 1077569 = 808177) B808177
theorem B422219 : Blo 279826 422219 := bstep (se 1 (by rfl) ⟨316664, by rfl⟩ : syracuseStep 422219 = 633329) B633329
theorem B2289995 : Blo 279826 2289995 := bstep (se 1 (by rfl) ⟨1717496, by rfl⟩ : syracuseStep 2289995 = 3434993) B3434993
theorem B422231 : Blo 279826 422231 := bstep (se 1 (by rfl) ⟨316673, by rfl⟩ : syracuseStep 422231 = 633347) B633347
theorem B422297 : Blo 279826 422297 := bstep (se 2 (by rfl) ⟨158361, by rfl⟩ : syracuseStep 422297 = 316723) B316723
theorem B422411 : Blo 279826 422411 := bstep (se 1 (by rfl) ⟨316808, by rfl⟩ : syracuseStep 422411 = 633617) B633617
theorem B422423 : Blo 279826 422423 := bstep (se 1 (by rfl) ⟨316817, by rfl⟩ : syracuseStep 422423 = 633635) B633635
theorem B422489 : Blo 279826 422489 := bstep (se 2 (by rfl) ⟨158433, by rfl⟩ : syracuseStep 422489 = 316867) B316867
theorem B946781 : Blo 279826 946781 := bstep (se 3 (by rfl) ⟨177521, by rfl⟩ : syracuseStep 946781 = 355043) B355043
theorem B422603 : Blo 279826 422603 := bstep (se 1 (by rfl) ⟨316952, by rfl⟩ : syracuseStep 422603 = 633905) B633905
theorem B422615 : Blo 279826 422615 := bstep (se 1 (by rfl) ⟨316961, by rfl⟩ : syracuseStep 422615 = 633923) B633923
theorem B422681 : Blo 279826 422681 := bstep (se 2 (by rfl) ⟨158505, by rfl⟩ : syracuseStep 422681 = 317011) B317011
theorem B717619 : Blo 279826 717619 := bstep (se 1 (by rfl) ⟨538214, by rfl⟩ : syracuseStep 717619 = 1076429) B1076429
theorem B422795 : Blo 279826 422795 := bstep (se 1 (by rfl) ⟨317096, by rfl⟩ : syracuseStep 422795 = 634193) B634193
theorem B422807 : Blo 279826 422807 := bstep (se 1 (by rfl) ⟨317105, by rfl⟩ : syracuseStep 422807 = 634211) B634211
theorem B2290609 : Blo 279826 2290609 := bstep (se 2 (by rfl) ⟨858978, by rfl⟩ : syracuseStep 2290609 = 1717957) B1717957
theorem B717761 : Blo 279826 717761 := bstep (se 2 (by rfl) ⟨269160, by rfl⟩ : syracuseStep 717761 = 538321) B538321
theorem B422873 : Blo 279826 422873 := bstep (se 2 (by rfl) ⟨158577, by rfl⟩ : syracuseStep 422873 = 317155) B317155
theorem B422987 : Blo 279826 422987 := bstep (se 1 (by rfl) ⟨317240, by rfl⟩ : syracuseStep 422987 = 634481) B634481
theorem B422999 : Blo 279826 422999 := bstep (se 1 (by rfl) ⟨317249, by rfl⟩ : syracuseStep 422999 = 634499) B634499
theorem B357463 : Blo 279826 357463 := bstep (se 1 (by rfl) ⟨268097, by rfl⟩ : syracuseStep 357463 = 536195) B536195
theorem B1012829 : Blo 279826 1012829 := bstep (se 3 (by rfl) ⟨189905, by rfl⟩ : syracuseStep 1012829 = 379811) B379811
theorem B423065 : Blo 279826 423065 := bstep (se 2 (by rfl) ⟨158649, by rfl⟩ : syracuseStep 423065 = 317299) B317299
theorem B423179 : Blo 279826 423179 := bstep (se 1 (by rfl) ⟨317384, by rfl⟩ : syracuseStep 423179 = 634769) B634769
theorem B1209617 : Blo 279826 1209617 := bstep (se 2 (by rfl) ⟨453606, by rfl⟩ : syracuseStep 1209617 = 907213) B907213
theorem B423191 : Blo 279826 423191 := bstep (se 1 (by rfl) ⟨317393, by rfl⟩ : syracuseStep 423191 = 634787) B634787
theorem B423257 : Blo 279826 423257 := bstep (se 2 (by rfl) ⟨158721, by rfl⟩ : syracuseStep 423257 = 317443) B317443
theorem B423371 : Blo 279826 423371 := bstep (se 1 (by rfl) ⟨317528, by rfl⟩ : syracuseStep 423371 = 635057) B635057
theorem B423383 : Blo 279826 423383 := bstep (se 1 (by rfl) ⟨317537, by rfl⟩ : syracuseStep 423383 = 635075) B635075
theorem B423449 : Blo 279826 423449 := bstep (se 2 (by rfl) ⟨158793, by rfl⟩ : syracuseStep 423449 = 317587) B317587
theorem B1963565 : Blo 279826 1963565 := bstep (se 3 (by rfl) ⟨368168, by rfl⟩ : syracuseStep 1963565 = 736337) B736337
theorem B423563 : Blo 279826 423563 := bstep (se 1 (by rfl) ⟨317672, by rfl⟩ : syracuseStep 423563 = 635345) B635345
theorem B423575 : Blo 279826 423575 := bstep (se 1 (by rfl) ⟨317681, by rfl⟩ : syracuseStep 423575 = 635363) B635363
theorem B947915 : Blo 279826 947915 := bstep (se 1 (by rfl) ⟨710936, by rfl⟩ : syracuseStep 947915 = 1421873) B1421873
theorem B1013465 : Blo 279826 1013465 := bstep (se 2 (by rfl) ⟨380049, by rfl⟩ : syracuseStep 1013465 = 760099) B760099
theorem B423641 : Blo 279826 423641 := bstep (se 2 (by rfl) ⟨158865, by rfl⟩ : syracuseStep 423641 = 317731) B317731
theorem B1013521 : Blo 279826 1013521 := bstep (se 2 (by rfl) ⟨380070, by rfl⟩ : syracuseStep 1013521 = 760141) B760141
theorem B423755 : Blo 279826 423755 := bstep (se 1 (by rfl) ⟨317816, by rfl⟩ : syracuseStep 423755 = 635633) B635633
theorem B423767 : Blo 279826 423767 := bstep (se 1 (by rfl) ⟨317825, by rfl⟩ : syracuseStep 423767 = 635651) B635651
theorem B358283 : Blo 279826 358283 := bstep (se 1 (by rfl) ⟨268712, by rfl⟩ : syracuseStep 358283 = 537425) B537425
theorem B423833 : Blo 279826 423833 := bstep (se 2 (by rfl) ⟨158937, by rfl⟩ : syracuseStep 423833 = 317875) B317875
theorem B948185 : Blo 279826 948185 := bstep (se 2 (by rfl) ⟨355569, by rfl⟩ : syracuseStep 948185 = 711139) B711139
theorem B423947 : Blo 279826 423947 := bstep (se 1 (by rfl) ⟨317960, by rfl⟩ : syracuseStep 423947 = 635921) B635921
theorem B423959 : Blo 279826 423959 := bstep (se 1 (by rfl) ⟨317969, by rfl⟩ : syracuseStep 423959 = 635939) B635939
theorem B718913 : Blo 279826 718913 := bstep (se 2 (by rfl) ⟨269592, by rfl⟩ : syracuseStep 718913 = 539185) B539185
theorem B424025 : Blo 279826 424025 := bstep (se 2 (by rfl) ⟨159009, by rfl⟩ : syracuseStep 424025 = 318019) B318019
theorem B424139 : Blo 279826 424139 := bstep (se 1 (by rfl) ⟨318104, by rfl⟩ : syracuseStep 424139 = 636209) B636209
theorem B424151 : Blo 279826 424151 := bstep (se 1 (by rfl) ⟨318113, by rfl⟩ : syracuseStep 424151 = 636227) B636227
theorem B424217 : Blo 279826 424217 := bstep (se 2 (by rfl) ⟨159081, by rfl⟩ : syracuseStep 424217 = 318163) B318163
theorem B2128193 : Blo 279826 2128193 := bstep (se 2 (by rfl) ⟨798072, by rfl⟩ : syracuseStep 2128193 = 1596145) B1596145
theorem B424331 : Blo 279826 424331 := bstep (se 1 (by rfl) ⟨318248, by rfl⟩ : syracuseStep 424331 = 636497) B636497
theorem B424343 : Blo 279826 424343 := bstep (se 1 (by rfl) ⟨318257, by rfl⟩ : syracuseStep 424343 = 636515) B636515
theorem B2980313 : Blo 279826 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B424409 : Blo 279826 424409 := bstep (se 2 (by rfl) ⟨159153, by rfl⟩ : syracuseStep 424409 = 318307) B318307
theorem B424523 : Blo 279826 424523 := bstep (se 1 (by rfl) ⟨318392, by rfl⟩ : syracuseStep 424523 = 636785) B636785
theorem B358987 : Blo 279826 358987 := bstep (se 1 (by rfl) ⟨269240, by rfl⟩ : syracuseStep 358987 = 538481) B538481
theorem B424535 : Blo 279826 424535 := bstep (se 1 (by rfl) ⟨318401, by rfl⟩ : syracuseStep 424535 = 636803) B636803
theorem B948887 : Blo 279826 948887 := bstep (se 1 (by rfl) ⟨711665, by rfl⟩ : syracuseStep 948887 = 1423331) B1423331
theorem B424601 : Blo 279826 424601 := bstep (se 2 (by rfl) ⟨159225, by rfl⟩ : syracuseStep 424601 = 318451) B318451
theorem B424715 : Blo 279826 424715 := bstep (se 1 (by rfl) ⟨318536, by rfl⟩ : syracuseStep 424715 = 637073) B637073
theorem B424727 : Blo 279826 424727 := bstep (se 1 (by rfl) ⟨318545, by rfl⟩ : syracuseStep 424727 = 637091) B637091
theorem B424793 : Blo 279826 424793 := bstep (se 2 (by rfl) ⟨159297, by rfl⟩ : syracuseStep 424793 = 318595) B318595
theorem B1538909 : Blo 279826 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B424907 : Blo 279826 424907 := bstep (se 1 (by rfl) ⟨318680, by rfl⟩ : syracuseStep 424907 = 637361) B637361
theorem B424919 : Blo 279826 424919 := bstep (se 1 (by rfl) ⟨318689, by rfl⟩ : syracuseStep 424919 = 637379) B637379
theorem B424985 : Blo 279826 424985 := bstep (se 2 (by rfl) ⟨159369, by rfl⟩ : syracuseStep 424985 = 318739) B318739
theorem B425099 : Blo 279826 425099 := bstep (se 1 (by rfl) ⟨318824, by rfl⟩ : syracuseStep 425099 = 637649) B637649
theorem B425111 : Blo 279826 425111 := bstep (se 1 (by rfl) ⟨318833, by rfl⟩ : syracuseStep 425111 = 637667) B637667
theorem B949427 : Blo 279826 949427 := bstep (se 1 (by rfl) ⟨712070, by rfl⟩ : syracuseStep 949427 = 1424141) B1424141
theorem B720065 : Blo 279826 720065 := bstep (se 2 (by rfl) ⟨270024, by rfl⟩ : syracuseStep 720065 = 540049) B540049
theorem B425177 : Blo 279826 425177 := bstep (se 2 (by rfl) ⟨159441, by rfl⟩ : syracuseStep 425177 = 318883) B318883
theorem B425291 : Blo 279826 425291 := bstep (se 1 (by rfl) ⟨318968, by rfl⟩ : syracuseStep 425291 = 637937) B637937
theorem B425303 : Blo 279826 425303 := bstep (se 1 (by rfl) ⟨318977, by rfl⟩ : syracuseStep 425303 = 637955) B637955
theorem B425369 : Blo 279826 425369 := bstep (se 2 (by rfl) ⟨159513, by rfl⟩ : syracuseStep 425369 = 319027) B319027
theorem B2489777 : Blo 279826 2489777 := bstep (se 2 (by rfl) ⟨933666, by rfl⟩ : syracuseStep 2489777 = 1867333) B1867333
theorem B949697 : Blo 279826 949697 := bstep (se 2 (by rfl) ⟨356136, by rfl⟩ : syracuseStep 949697 = 712273) B712273
theorem B1244609 : Blo 279826 1244609 := bstep (se 2 (by rfl) ⟨466728, by rfl⟩ : syracuseStep 1244609 = 933457) B933457
theorem B1932761 : Blo 279826 1932761 := bstep (se 2 (by rfl) ⟨724785, by rfl⟩ : syracuseStep 1932761 = 1449571) B1449571
theorem B425483 : Blo 279826 425483 := bstep (se 1 (by rfl) ⟨319112, by rfl⟩ : syracuseStep 425483 = 638225) B638225
theorem B425495 : Blo 279826 425495 := bstep (se 1 (by rfl) ⟨319121, by rfl⟩ : syracuseStep 425495 = 638243) B638243
theorem B425561 : Blo 279826 425561 := bstep (se 2 (by rfl) ⟨159585, by rfl⟩ : syracuseStep 425561 = 319171) B319171
theorem B1211993 : Blo 279826 1211993 := bstep (se 2 (by rfl) ⟨454497, by rfl⟩ : syracuseStep 1211993 = 908995) B908995
theorem B1212077 : Blo 279826 1212077 := bstep (se 3 (by rfl) ⟨227264, by rfl⟩ : syracuseStep 1212077 = 454529) B454529
theorem B425675 : Blo 279826 425675 := bstep (se 1 (by rfl) ⟨319256, by rfl⟩ : syracuseStep 425675 = 638513) B638513
theorem B425687 : Blo 279826 425687 := bstep (se 1 (by rfl) ⟨319265, by rfl⟩ : syracuseStep 425687 = 638531) B638531
theorem B950237 : Blo 279826 950237 := bstep (se 3 (by rfl) ⟨178169, by rfl⟩ : syracuseStep 950237 = 356339) B356339
theorem B950561 : Blo 279826 950561 := bstep (se 2 (by rfl) ⟨356460, by rfl⟩ : syracuseStep 950561 = 712921) B712921
theorem B426359 : Blo 279826 426359 := bstep (se 1 (by rfl) ⟨319769, by rfl⟩ : syracuseStep 426359 = 639539) B639539
theorem B1409501 : Blo 279826 1409501 := bstep (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) B528563
theorem B852751 : Blo 279826 852751 := bstep (se 1 (by rfl) ⟨639563, by rfl⟩ : syracuseStep 852751 = 1279127) B1279127
theorem B951155 : Blo 279826 951155 := bstep (se 1 (by rfl) ⟨713366, by rfl⟩ : syracuseStep 951155 = 1426733) B1426733
theorem B427337 : Blo 279826 427337 := bstep (se 2 (by rfl) ⟨160251, by rfl⟩ : syracuseStep 427337 = 320503) B320503
theorem B1279385 : Blo 279826 1279385 := bstep (se 2 (by rfl) ⟨479769, by rfl⟩ : syracuseStep 1279385 = 959539) B959539
theorem B3409451 : Blo 279826 3409451 := bstep (se 1 (by rfl) ⟨2557088, by rfl⟩ : syracuseStep 3409451 = 5114177) B5114177
theorem B22808141 : Blo 279826 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B460603 : Blo 279826 460603 := bstep (se 1 (by rfl) ⟨345452, by rfl⟩ : syracuseStep 460603 = 690905) B690905
theorem B2393945 : Blo 279826 2393945 := bstep (se 2 (by rfl) ⟨897729, by rfl⟩ : syracuseStep 2393945 = 1795459) B1795459
theorem B1607627 : Blo 279826 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B3049559 : Blo 279826 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B1771721 : Blo 279826 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B6621425 : Blo 279826 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B1345825 : Blo 279826 1345825 := bstep (se 2 (by rfl) ⟨504684, by rfl⟩ : syracuseStep 1345825 = 1009369) B1009369
theorem B1608083 : Blo 279826 1608083 := bstep (se 1 (by rfl) ⟨1206062, by rfl⟩ : syracuseStep 1608083 = 2412125) B2412125
theorem B2722405 : Blo 279826 2722405 := bstep (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) B510451
theorem B723799 : Blo 279826 723799 := bstep (se 1 (by rfl) ⟨542849, by rfl⟩ : syracuseStep 723799 = 1085699) B1085699
theorem B2133053 : Blo 279826 2133053 := bstep (se 3 (by rfl) ⟨399947, by rfl⟩ : syracuseStep 2133053 = 799895) B799895
theorem B2035003 : Blo 279826 2035003 := bstep (se 1 (by rfl) ⟨1526252, by rfl⟩ : syracuseStep 2035003 = 3052505) B3052505
theorem B953747 : Blo 279826 953747 := bstep (se 1 (by rfl) ⟨715310, by rfl⟩ : syracuseStep 953747 = 1430621) B1430621
theorem B2887235 : Blo 279826 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B2723635 : Blo 279826 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B1347671 : Blo 279826 1347671 := bstep (se 1 (by rfl) ⟨1010753, by rfl⟩ : syracuseStep 1347671 = 2021507) B2021507
theorem B1446365 : Blo 279826 1446365 := bstep (se 3 (by rfl) ⟨271193, by rfl⟩ : syracuseStep 1446365 = 542387) B542387
theorem B955151 : Blo 279826 955151 := bstep (se 1 (by rfl) ⟨716363, by rfl⟩ : syracuseStep 955151 = 1432727) B1432727
theorem B2659225 : Blo 279826 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B955421 : Blo 279826 955421 := bstep (se 3 (by rfl) ⟨179141, by rfl⟩ : syracuseStep 955421 = 358283) B358283
theorem B922711 : Blo 279826 922711 := bstep (se 1 (by rfl) ⟨692033, by rfl⟩ : syracuseStep 922711 = 1384067) B1384067
theorem B1741943 : Blo 279826 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B1283309 : Blo 279826 1283309 := bstep (se 3 (by rfl) ⟨240620, by rfl⟩ : syracuseStep 1283309 = 481241) B481241
theorem B759041 : Blo 279826 759041 := bstep (se 2 (by rfl) ⟨284640, by rfl⟩ : syracuseStep 759041 = 569281) B569281
theorem B2692445 : Blo 279826 2692445 := bstep (se 3 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 2692445 = 1009667) B1009667
theorem B300559 : Blo 279826 300559 := bstep (se 1 (by rfl) ⟨225419, by rfl⟩ : syracuseStep 300559 = 450839) B450839
theorem B1218091 : Blo 279826 1218091 := bstep (se 1 (by rfl) ⟨913568, by rfl⟩ : syracuseStep 1218091 = 1827137) B1827137
theorem B300935 : Blo 279826 300935 := bstep (se 1 (by rfl) ⟨225701, by rfl⟩ : syracuseStep 300935 = 451403) B451403
theorem B1513363 : Blo 279826 1513363 := bstep (se 1 (by rfl) ⟨1135022, by rfl⟩ : syracuseStep 1513363 = 2270045) B2270045
theorem B399367 : Blo 279826 399367 := bstep (se 1 (by rfl) ⟨299525, by rfl⟩ : syracuseStep 399367 = 599051) B599051
theorem B4921613 : Blo 279826 4921613 := bstep (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) B1845605
theorem B2136455 : Blo 279826 2136455 := bstep (se 1 (by rfl) ⟨1602341, by rfl⟩ : syracuseStep 2136455 = 3204683) B3204683
theorem B23239061 : Blo 279826 23239061 := bstep (se 6 (by rfl) ⟨544665, by rfl⟩ : syracuseStep 23239061 = 1089331) B1089331
theorem B956825 : Blo 279826 956825 := bstep (se 2 (by rfl) ⟨358809, by rfl⟩ : syracuseStep 956825 = 717619) B717619
theorem B400187 : Blo 279826 400187 := bstep (se 1 (by rfl) ⟨300140, by rfl⟩ : syracuseStep 400187 = 600281) B600281
theorem B3414899 : Blo 279826 3414899 := bstep (se 1 (by rfl) ⟨2561174, by rfl⟩ : syracuseStep 3414899 = 5122349) B5122349
theorem B629639 : Blo 279826 629639 := bstep (se 1 (by rfl) ⟨472229, by rfl⟩ : syracuseStep 629639 = 944459) B944459
theorem B531335 : Blo 279826 531335 := bstep (se 1 (by rfl) ⟨398501, by rfl⟩ : syracuseStep 531335 = 797003) B797003
theorem B302011 : Blo 279826 302011 := bstep (se 1 (by rfl) ⟨226508, by rfl⟩ : syracuseStep 302011 = 453017) B453017
theorem B629819 : Blo 279826 629819 := bstep (se 1 (by rfl) ⟨472364, by rfl⟩ : syracuseStep 629819 = 944729) B944729
theorem B957527 : Blo 279826 957527 := bstep (se 1 (by rfl) ⟨718145, by rfl⟩ : syracuseStep 957527 = 1436291) B1436291
theorem B629945 : Blo 279826 629945 := bstep (se 2 (by rfl) ⟨236229, by rfl⟩ : syracuseStep 629945 = 472459) B472459
theorem B400631 : Blo 279826 400631 := bstep (se 1 (by rfl) ⟨300473, by rfl⟩ : syracuseStep 400631 = 600947) B600947
theorem B2759953 : Blo 279826 2759953 := bstep (se 2 (by rfl) ⟨1034982, by rfl⟩ : syracuseStep 2759953 = 2069965) B2069965
theorem B531859 : Blo 279826 531859 := bstep (se 1 (by rfl) ⟨398894, by rfl⟩ : syracuseStep 531859 = 797789) B797789
theorem B400825 : Blo 279826 400825 := bstep (se 2 (by rfl) ⟨150309, by rfl⟩ : syracuseStep 400825 = 300619) B300619
theorem B2301443 : Blo 279826 2301443 := bstep (se 1 (by rfl) ⟨1726082, by rfl⟩ : syracuseStep 2301443 = 3452165) B3452165
theorem B630287 : Blo 279826 630287 := bstep (se 1 (by rfl) ⟨472715, by rfl⟩ : syracuseStep 630287 = 945431) B945431
theorem B4038173 : Blo 279826 4038173 := bstep (se 3 (by rfl) ⟨757157, by rfl⟩ : syracuseStep 4038173 = 1514315) B1514315
theorem B630305 : Blo 279826 630305 := bstep (se 2 (by rfl) ⟨236364, by rfl⟩ : syracuseStep 630305 = 472729) B472729
theorem B1515181 : Blo 279826 1515181 := bstep (se 3 (by rfl) ⟨284096, by rfl⟩ : syracuseStep 1515181 = 568193) B568193
theorem B1351361 : Blo 279826 1351361 := bstep (se 2 (by rfl) ⟨506760, by rfl⟩ : syracuseStep 1351361 = 1013521) B1013521
theorem B2727755 : Blo 279826 2727755 := bstep (se 1 (by rfl) ⟨2045816, by rfl⟩ : syracuseStep 2727755 = 4091633) B4091633
theorem B630647 : Blo 279826 630647 := bstep (se 1 (by rfl) ⟨472985, by rfl⟩ : syracuseStep 630647 = 945971) B945971
theorem B7217099 : Blo 279826 7217099 := bstep (se 1 (by rfl) ⟨5412824, by rfl⟩ : syracuseStep 7217099 = 10825649) B10825649
theorem B630827 : Blo 279826 630827 := bstep (se 1 (by rfl) ⟨473120, by rfl⟩ : syracuseStep 630827 = 946241) B946241
theorem B5775533 : Blo 279826 5775533 := bstep (se 3 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 5775533 = 2165825) B2165825
theorem B631187 : Blo 279826 631187 := bstep (se 1 (by rfl) ⟨473390, by rfl⟩ : syracuseStep 631187 = 946781) B946781
theorem B631241 : Blo 279826 631241 := bstep (se 2 (by rfl) ⟨236715, by rfl⟩ : syracuseStep 631241 = 473431) B473431
theorem B533051 : Blo 279826 533051 := bstep (se 1 (by rfl) ⟨399788, by rfl⟩ : syracuseStep 533051 = 799577) B799577
theorem B1417985 : Blo 279826 1417985 := bstep (se 2 (by rfl) ⟨531744, by rfl⟩ : syracuseStep 1417985 = 1063489) B1063489
theorem B598931 : Blo 279826 598931 := bstep (se 1 (by rfl) ⟨449198, by rfl⟩ : syracuseStep 598931 = 898397) B898397
theorem B533537 : Blo 279826 533537 := bstep (se 2 (by rfl) ⟨200076, by rfl⟩ : syracuseStep 533537 = 400153) B400153
theorem B631943 : Blo 279826 631943 := bstep (se 1 (by rfl) ⟨473957, by rfl⟩ : syracuseStep 631943 = 947915) B947915
theorem B5154029 : Blo 279826 5154029 := bstep (se 3 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 5154029 = 1932761) B1932761
theorem B337159 : Blo 279826 337159 := bstep (se 1 (by rfl) ⟨252869, by rfl⟩ : syracuseStep 337159 = 505739) B505739
theorem B861473 : Blo 279826 861473 := bstep (se 2 (by rfl) ⟨323052, by rfl⟩ : syracuseStep 861473 = 646105) B646105
theorem B533803 : Blo 279826 533803 := bstep (se 1 (by rfl) ⟨400352, by rfl⟩ : syracuseStep 533803 = 800705) B800705
theorem B632123 : Blo 279826 632123 := bstep (se 1 (by rfl) ⟨474092, by rfl⟩ : syracuseStep 632123 = 948185) B948185
theorem B632249 : Blo 279826 632249 := bstep (se 2 (by rfl) ⟨237093, by rfl⟩ : syracuseStep 632249 = 474187) B474187
theorem B1418795 : Blo 279826 1418795 := bstep (se 1 (by rfl) ⟨1064096, by rfl⟩ : syracuseStep 1418795 = 2128193) B2128193
theorem B1025597 : Blo 279826 1025597 := bstep (se 3 (by rfl) ⟨192299, by rfl⟩ : syracuseStep 1025597 = 384599) B384599
theorem B632591 : Blo 279826 632591 := bstep (se 1 (by rfl) ⟨474443, by rfl⟩ : syracuseStep 632591 = 948887) B948887
theorem B632609 : Blo 279826 632609 := bstep (se 2 (by rfl) ⟨237228, by rfl⟩ : syracuseStep 632609 = 474457) B474457
theorem B26388341 : Blo 279826 26388341 := bstep (se 5 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 26388341 = 2473907) B2473907
theorem B1025939 : Blo 279826 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B632951 : Blo 279826 632951 := bstep (se 1 (by rfl) ⟨474713, by rfl⟩ : syracuseStep 632951 = 949427) B949427
theorem B633131 : Blo 279826 633131 := bstep (se 1 (by rfl) ⟨474848, by rfl⟩ : syracuseStep 633131 = 949697) B949697
theorem B829739 : Blo 279826 829739 := bstep (se 1 (by rfl) ⟨622304, by rfl⟩ : syracuseStep 829739 = 1244609) B1244609
theorem B534919 : Blo 279826 534919 := bstep (se 1 (by rfl) ⟨401189, by rfl⟩ : syracuseStep 534919 = 802379) B802379
theorem B633491 : Blo 279826 633491 := bstep (se 1 (by rfl) ⟨475118, by rfl⟩ : syracuseStep 633491 = 950237) B950237
theorem B633545 : Blo 279826 633545 := bstep (se 2 (by rfl) ⟨237579, by rfl⟩ : syracuseStep 633545 = 475159) B475159
theorem B2763571 : Blo 279826 2763571 := bstep (se 1 (by rfl) ⟨2072678, by rfl⟩ : syracuseStep 2763571 = 4145357) B4145357
theorem B1420091 : Blo 279826 1420091 := bstep (se 1 (by rfl) ⟨1065068, by rfl⟩ : syracuseStep 1420091 = 2130137) B2130137
theorem B535481 : Blo 279826 535481 := bstep (se 2 (by rfl) ⟨200805, by rfl⟩ : syracuseStep 535481 = 401611) B401611
theorem B601033 : Blo 279826 601033 := bstep (se 2 (by rfl) ⟨225387, by rfl⟩ : syracuseStep 601033 = 450775) B450775
theorem B1420253 : Blo 279826 1420253 := bstep (se 3 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 1420253 = 532595) B532595
theorem B338951 : Blo 279826 338951 := bstep (se 1 (by rfl) ⟨254213, by rfl⟩ : syracuseStep 338951 = 508427) B508427
theorem B1453085 : Blo 279826 1453085 := bstep (se 3 (by rfl) ⟨272453, by rfl⟩ : syracuseStep 1453085 = 544907) B544907
theorem B1420577 : Blo 279826 1420577 := bstep (se 2 (by rfl) ⟨532716, by rfl⟩ : syracuseStep 1420577 = 1065433) B1065433
theorem B765245 : Blo 279826 765245 := bstep (se 3 (by rfl) ⟨143483, by rfl⟩ : syracuseStep 765245 = 286967) B286967
theorem B634247 : Blo 279826 634247 := bstep (se 1 (by rfl) ⟨475685, by rfl⟩ : syracuseStep 634247 = 951371) B951371
theorem B1060249 : Blo 279826 1060249 := bstep (se 2 (by rfl) ⟨397593, by rfl⟩ : syracuseStep 1060249 = 795187) B795187
theorem B634427 : Blo 279826 634427 := bstep (se 1 (by rfl) ⟨475820, by rfl⟩ : syracuseStep 634427 = 951641) B951641
theorem B24850061 : Blo 279826 24850061 := bstep (se 3 (by rfl) ⟨4659386, by rfl⟩ : syracuseStep 24850061 = 9318773) B9318773
theorem B634553 : Blo 279826 634553 := bstep (se 2 (by rfl) ⟨237957, by rfl⟩ : syracuseStep 634553 = 475915) B475915
theorem B339643 : Blo 279826 339643 := bstep (se 1 (by rfl) ⟨254732, by rfl⟩ : syracuseStep 339643 = 509465) B509465
theorem B1519505 : Blo 279826 1519505 := bstep (se 2 (by rfl) ⟨569814, by rfl⟩ : syracuseStep 1519505 = 1139629) B1139629
theorem B634895 : Blo 279826 634895 := bstep (se 1 (by rfl) ⟨476171, by rfl⟩ : syracuseStep 634895 = 952343) B952343
theorem B634913 : Blo 279826 634913 := bstep (se 2 (by rfl) ⟨238092, by rfl⟩ : syracuseStep 634913 = 476185) B476185
theorem B536635 : Blo 279826 536635 := bstep (se 1 (by rfl) ⟨402476, by rfl⟩ : syracuseStep 536635 = 804953) B804953
theorem B3321917 : Blo 279826 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B1224791 : Blo 279826 1224791 := bstep (se 1 (by rfl) ⟨918593, by rfl⟩ : syracuseStep 1224791 = 1837187) B1837187
theorem B7319645 : Blo 279826 7319645 := bstep (se 3 (by rfl) ⟨1372433, by rfl⟩ : syracuseStep 7319645 = 2744867) B2744867
theorem B1421549 : Blo 279826 1421549 := bstep (se 3 (by rfl) ⟨266540, by rfl⟩ : syracuseStep 1421549 = 533081) B533081
theorem B635255 : Blo 279826 635255 := bstep (se 1 (by rfl) ⟨476441, by rfl⟩ : syracuseStep 635255 = 952883) B952883
theorem B2699729 : Blo 279826 2699729 := bstep (se 2 (by rfl) ⟨1012398, by rfl⟩ : syracuseStep 2699729 = 2024797) B2024797
theorem B799247 : Blo 279826 799247 := bstep (se 1 (by rfl) ⟨599435, by rfl⟩ : syracuseStep 799247 = 1198871) B1198871
theorem B537121 : Blo 279826 537121 := bstep (se 2 (by rfl) ⟨201420, by rfl⟩ : syracuseStep 537121 = 402841) B402841
theorem B635435 : Blo 279826 635435 := bstep (se 1 (by rfl) ⟨476576, by rfl⟩ : syracuseStep 635435 = 953153) B953153
theorem B1815347 : Blo 279826 1815347 := bstep (se 1 (by rfl) ⟨1361510, by rfl⟩ : syracuseStep 1815347 = 2723021) B2723021
theorem B635795 : Blo 279826 635795 := bstep (se 1 (by rfl) ⟨476846, by rfl⟩ : syracuseStep 635795 = 953693) B953693
theorem B635849 : Blo 279826 635849 := bstep (se 2 (by rfl) ⟨238443, by rfl⟩ : syracuseStep 635849 = 476887) B476887
theorem B1422359 : Blo 279826 1422359 := bstep (se 1 (by rfl) ⟨1066769, by rfl⟩ : syracuseStep 1422359 = 2133539) B2133539
theorem B504967 : Blo 279826 504967 := bstep (se 1 (by rfl) ⟨378725, by rfl⟩ : syracuseStep 504967 = 757451) B757451
theorem B603407 : Blo 279826 603407 := bstep (se 1 (by rfl) ⟨452555, by rfl⟩ : syracuseStep 603407 = 905111) B905111
theorem B603425 : Blo 279826 603425 := bstep (se 2 (by rfl) ⟨226284, by rfl⟩ : syracuseStep 603425 = 452569) B452569
theorem B472439 : Blo 279826 472439 := bstep (se 1 (by rfl) ⟨354329, by rfl⟩ : syracuseStep 472439 = 708659) B708659
theorem B5813639 : Blo 279826 5813639 := bstep (se 1 (by rfl) ⟨4360229, by rfl⟩ : syracuseStep 5813639 = 8720459) B8720459
theorem B2700877 : Blo 279826 2700877 := bstep (se 3 (by rfl) ⟨506414, by rfl⟩ : syracuseStep 2700877 = 1012829) B1012829
theorem B603767 : Blo 279826 603767 := bstep (se 1 (by rfl) ⟨452825, by rfl⟩ : syracuseStep 603767 = 905651) B905651
theorem B636551 : Blo 279826 636551 := bstep (se 1 (by rfl) ⟨477413, by rfl⟩ : syracuseStep 636551 = 954827) B954827
theorem B472891 : Blo 279826 472891 := bstep (se 1 (by rfl) ⟨354668, by rfl⟩ : syracuseStep 472891 = 709337) B709337
theorem B636731 : Blo 279826 636731 := bstep (se 1 (by rfl) ⟨477548, by rfl⟩ : syracuseStep 636731 = 955097) B955097
theorem B538427 : Blo 279826 538427 := bstep (se 1 (by rfl) ⟨403820, by rfl⟩ : syracuseStep 538427 = 807641) B807641
theorem B4798277 : Blo 279826 4798277 := bstep (se 4 (by rfl) ⟨449838, by rfl⟩ : syracuseStep 4798277 = 899677) B899677
theorem B1062791 : Blo 279826 1062791 := bstep (se 1 (by rfl) ⟨797093, by rfl⟩ : syracuseStep 1062791 = 1594187) B1594187
theorem B2570147 : Blo 279826 2570147 := bstep (se 1 (by rfl) ⟨1927610, by rfl⟩ : syracuseStep 2570147 = 3855221) B3855221
theorem B636857 : Blo 279826 636857 := bstep (se 2 (by rfl) ⟨238821, by rfl⟩ : syracuseStep 636857 = 477643) B477643
theorem B473033 : Blo 279826 473033 := bstep (se 2 (by rfl) ⟨177387, by rfl⟩ : syracuseStep 473033 = 354775) B354775
theorem B1226819 : Blo 279826 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B899191 : Blo 279826 899191 := bstep (se 1 (by rfl) ⟨674393, by rfl⟩ : syracuseStep 899191 = 1348787) B1348787
theorem B800887 : Blo 279826 800887 := bstep (se 1 (by rfl) ⟨600665, by rfl⟩ : syracuseStep 800887 = 1201331) B1201331
theorem B800921 : Blo 279826 800921 := bstep (se 2 (by rfl) ⟨300345, by rfl⟩ : syracuseStep 800921 = 600691) B600691
theorem B3029237 : Blo 279826 3029237 := bstep (se 5 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 3029237 = 283991) B283991
theorem B801035 : Blo 279826 801035 := bstep (se 1 (by rfl) ⟨600776, by rfl⟩ : syracuseStep 801035 = 1201553) B1201553
theorem B637199 : Blo 279826 637199 := bstep (se 1 (by rfl) ⟨477899, by rfl⟩ : syracuseStep 637199 = 955799) B955799
theorem B637217 : Blo 279826 637217 := bstep (se 2 (by rfl) ⟨238956, by rfl⟩ : syracuseStep 637217 = 477913) B477913
theorem B637559 : Blo 279826 637559 := bstep (se 1 (by rfl) ⟨478169, by rfl⟩ : syracuseStep 637559 = 956339) B956339
theorem B473735 : Blo 279826 473735 := bstep (se 1 (by rfl) ⟨355301, by rfl⟩ : syracuseStep 473735 = 710603) B710603
theorem B637739 : Blo 279826 637739 := bstep (se 1 (by rfl) ⟨478304, by rfl⟩ : syracuseStep 637739 = 956609) B956609
theorem B638099 : Blo 279826 638099 := bstep (se 1 (by rfl) ⟨478574, by rfl⟩ : syracuseStep 638099 = 957149) B957149
theorem B638153 : Blo 279826 638153 := bstep (se 2 (by rfl) ⟨239307, by rfl⟩ : syracuseStep 638153 = 478615) B478615
theorem B474383 : Blo 279826 474383 := bstep (se 1 (by rfl) ⟨355787, by rfl⟩ : syracuseStep 474383 = 711575) B711575
theorem B507179 : Blo 279826 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B802163 : Blo 279826 802163 := bstep (se 1 (by rfl) ⟨601622, by rfl⟩ : syracuseStep 802163 = 1203245) B1203245
theorem B1818065 : Blo 279826 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B2408129 : Blo 279826 2408129 := bstep (se 2 (by rfl) ⟨903048, by rfl⟩ : syracuseStep 2408129 = 1806097) B1806097
theorem B802561 : Blo 279826 802561 := bstep (se 2 (by rfl) ⟨300960, by rfl⟩ : syracuseStep 802561 = 601921) B601921
theorem B474923 : Blo 279826 474923 := bstep (se 1 (by rfl) ⟨356192, by rfl⟩ : syracuseStep 474923 = 712385) B712385
theorem B802619 : Blo 279826 802619 := bstep (se 1 (by rfl) ⟨601964, by rfl⟩ : syracuseStep 802619 = 1203929) B1203929
theorem B1425437 : Blo 279826 1425437 := bstep (se 3 (by rfl) ⟨267269, by rfl⟩ : syracuseStep 1425437 = 534539) B534539
theorem B22986827 : Blo 279826 22986827 := bstep (se 1 (by rfl) ⟨17240120, by rfl⟩ : syracuseStep 22986827 = 34480241) B34480241
theorem B1917101 : Blo 279826 1917101 := bstep (se 3 (by rfl) ⟨359456, by rfl⟩ : syracuseStep 1917101 = 718913) B718913
theorem B475321 : Blo 279826 475321 := bstep (se 2 (by rfl) ⟨178245, by rfl⟩ : syracuseStep 475321 = 356491) B356491
theorem B1524005 : Blo 279826 1524005 := bstep (se 4 (by rfl) ⟨142875, by rfl⟩ : syracuseStep 1524005 = 285751) B285751
theorem B901523 : Blo 279826 901523 := bstep (se 1 (by rfl) ⟨676142, by rfl⟩ : syracuseStep 901523 = 1352285) B1352285
theorem B1425923 : Blo 279826 1425923 := bstep (se 1 (by rfl) ⟨1069442, by rfl⟩ : syracuseStep 1425923 = 2138885) B2138885
theorem B607019 : Blo 279826 607019 := bstep (se 1 (by rfl) ⟨455264, by rfl⟩ : syracuseStep 607019 = 910529) B910529
theorem B476023 : Blo 279826 476023 := bstep (se 1 (by rfl) ⟨357017, by rfl⟩ : syracuseStep 476023 = 714035) B714035
theorem B3064877 : Blo 279826 3064877 := bstep (se 3 (by rfl) ⟨574664, by rfl⟩ : syracuseStep 3064877 = 1149329) B1149329
theorem B476219 : Blo 279826 476219 := bstep (se 1 (by rfl) ⟨357164, by rfl⟩ : syracuseStep 476219 = 714329) B714329
theorem B279867 : Blo 279826 279867 := bstep (se 1 (by rfl) ⟨209900, by rfl⟩ : syracuseStep 279867 = 419801) B419801
theorem B279943 : Blo 279826 279943 := bstep (se 1 (by rfl) ⟨209957, by rfl⟩ : syracuseStep 279943 = 419915) B419915
theorem B279951 : Blo 279826 279951 := bstep (se 1 (by rfl) ⟨209963, by rfl⟩ : syracuseStep 279951 = 419927) B419927
theorem B279995 : Blo 279826 279995 := bstep (se 1 (by rfl) ⟨209996, by rfl⟩ : syracuseStep 279995 = 419993) B419993
theorem B476617 : Blo 279826 476617 := bstep (se 2 (by rfl) ⟨178731, by rfl⟩ : syracuseStep 476617 = 357463) B357463
theorem B280071 : Blo 279826 280071 := bstep (se 1 (by rfl) ⟨210053, by rfl⟩ : syracuseStep 280071 = 420107) B420107
theorem B280079 : Blo 279826 280079 := bstep (se 1 (by rfl) ⟨210059, by rfl⟩ : syracuseStep 280079 = 420119) B420119
theorem B280123 : Blo 279826 280123 := bstep (se 1 (by rfl) ⟨210092, by rfl⟩ : syracuseStep 280123 = 420185) B420185
theorem B280199 : Blo 279826 280199 := bstep (se 1 (by rfl) ⟨210149, by rfl⟩ : syracuseStep 280199 = 420299) B420299
theorem B280207 : Blo 279826 280207 := bstep (se 1 (by rfl) ⟨210155, by rfl⟩ : syracuseStep 280207 = 420311) B420311
theorem B280251 : Blo 279826 280251 := bstep (se 1 (by rfl) ⟨210188, by rfl⟩ : syracuseStep 280251 = 420377) B420377
theorem B280327 : Blo 279826 280327 := bstep (se 1 (by rfl) ⟨210245, by rfl⟩ : syracuseStep 280327 = 420491) B420491
theorem B280335 : Blo 279826 280335 := bstep (se 1 (by rfl) ⟨210251, by rfl⟩ : syracuseStep 280335 = 420503) B420503
theorem B280379 : Blo 279826 280379 := bstep (se 1 (by rfl) ⟨210284, by rfl⟩ : syracuseStep 280379 = 420569) B420569
theorem B280455 : Blo 279826 280455 := bstep (se 1 (by rfl) ⟨210341, by rfl⟩ : syracuseStep 280455 = 420683) B420683
theorem B280463 : Blo 279826 280463 := bstep (se 1 (by rfl) ⟨210347, by rfl⟩ : syracuseStep 280463 = 420695) B420695
theorem B280507 : Blo 279826 280507 := bstep (se 1 (by rfl) ⟨210380, by rfl⟩ : syracuseStep 280507 = 420761) B420761
theorem B1558493 : Blo 279826 1558493 := bstep (se 3 (by rfl) ⟨292217, by rfl⟩ : syracuseStep 1558493 = 584435) B584435
theorem B280583 : Blo 279826 280583 := bstep (se 1 (by rfl) ⟨210437, by rfl⟩ : syracuseStep 280583 = 420875) B420875
theorem B280591 : Blo 279826 280591 := bstep (se 1 (by rfl) ⟨210443, by rfl⟩ : syracuseStep 280591 = 420887) B420887
theorem B804907 : Blo 279826 804907 := bstep (se 1 (by rfl) ⟨603680, by rfl⟩ : syracuseStep 804907 = 1207361) B1207361
theorem B280635 : Blo 279826 280635 := bstep (se 1 (by rfl) ⟨210476, by rfl⟩ : syracuseStep 280635 = 420953) B420953
theorem B1427543 : Blo 279826 1427543 := bstep (se 1 (by rfl) ⟨1070657, by rfl⟩ : syracuseStep 1427543 = 2141315) B2141315
theorem B280711 : Blo 279826 280711 := bstep (se 1 (by rfl) ⟨210533, by rfl⟩ : syracuseStep 280711 = 421067) B421067
theorem B477319 : Blo 279826 477319 := bstep (se 1 (by rfl) ⟨357989, by rfl⟩ : syracuseStep 477319 = 715979) B715979
theorem B280719 : Blo 279826 280719 := bstep (se 1 (by rfl) ⟨210539, by rfl⟩ : syracuseStep 280719 = 421079) B421079
theorem B280763 : Blo 279826 280763 := bstep (se 1 (by rfl) ⟨210572, by rfl⟩ : syracuseStep 280763 = 421145) B421145
theorem B280839 : Blo 279826 280839 := bstep (se 1 (by rfl) ⟨210629, by rfl⟩ : syracuseStep 280839 = 421259) B421259
theorem B280847 : Blo 279826 280847 := bstep (se 1 (by rfl) ⟨210635, by rfl⟩ : syracuseStep 280847 = 421271) B421271
theorem B805135 : Blo 279826 805135 := bstep (se 1 (by rfl) ⟨603851, by rfl⟩ : syracuseStep 805135 = 1207703) B1207703
theorem B280891 : Blo 279826 280891 := bstep (se 1 (by rfl) ⟨210668, by rfl⟩ : syracuseStep 280891 = 421337) B421337
theorem B280967 : Blo 279826 280967 := bstep (se 1 (by rfl) ⟨210725, by rfl⟩ : syracuseStep 280967 = 421451) B421451
theorem B280975 : Blo 279826 280975 := bstep (se 1 (by rfl) ⟨210731, by rfl⟩ : syracuseStep 280975 = 421463) B421463
theorem B281019 : Blo 279826 281019 := bstep (se 1 (by rfl) ⟨210764, by rfl⟩ : syracuseStep 281019 = 421529) B421529
theorem B3197393 : Blo 279826 3197393 := bstep (se 2 (by rfl) ⟨1199022, by rfl⟩ : syracuseStep 3197393 = 2398045) B2398045
theorem B281095 : Blo 279826 281095 := bstep (se 1 (by rfl) ⟨210821, by rfl⟩ : syracuseStep 281095 = 421643) B421643
theorem B281103 : Blo 279826 281103 := bstep (se 1 (by rfl) ⟨210827, by rfl⟩ : syracuseStep 281103 = 421655) B421655
theorem B805409 : Blo 279826 805409 := bstep (se 2 (by rfl) ⟨302028, by rfl⟩ : syracuseStep 805409 = 604057) B604057
theorem B281147 : Blo 279826 281147 := bstep (se 1 (by rfl) ⟨210860, by rfl⟩ : syracuseStep 281147 = 421721) B421721
theorem B1428029 : Blo 279826 1428029 := bstep (se 3 (by rfl) ⟨267755, by rfl⟩ : syracuseStep 1428029 = 535511) B535511
theorem B281223 : Blo 279826 281223 := bstep (se 1 (by rfl) ⟨210917, by rfl⟩ : syracuseStep 281223 = 421835) B421835
theorem B281231 : Blo 279826 281231 := bstep (se 1 (by rfl) ⟨210923, by rfl⟩ : syracuseStep 281231 = 421847) B421847
theorem B281275 : Blo 279826 281275 := bstep (se 1 (by rfl) ⟨210956, by rfl⟩ : syracuseStep 281275 = 421913) B421913
theorem B903881 : Blo 279826 903881 := bstep (se 2 (by rfl) ⟨338955, by rfl⟩ : syracuseStep 903881 = 677911) B677911
theorem B1526509 : Blo 279826 1526509 := bstep (se 3 (by rfl) ⟨286220, by rfl⟩ : syracuseStep 1526509 = 572441) B572441
theorem B281351 : Blo 279826 281351 := bstep (se 1 (by rfl) ⟨211013, by rfl⟩ : syracuseStep 281351 = 422027) B422027
theorem B281359 : Blo 279826 281359 := bstep (se 1 (by rfl) ⟨211019, by rfl⟩ : syracuseStep 281359 = 422039) B422039
theorem B477967 : Blo 279826 477967 := bstep (se 1 (by rfl) ⟨358475, by rfl⟩ : syracuseStep 477967 = 716951) B716951
theorem B281403 : Blo 279826 281403 := bstep (se 1 (by rfl) ⟨211052, by rfl⟩ : syracuseStep 281403 = 422105) B422105
theorem B1329979 : Blo 279826 1329979 := bstep (se 1 (by rfl) ⟨997484, by rfl⟩ : syracuseStep 1329979 = 1994969) B1994969
theorem B805751 : Blo 279826 805751 := bstep (se 1 (by rfl) ⟨604313, by rfl⟩ : syracuseStep 805751 = 1208627) B1208627
theorem B281479 : Blo 279826 281479 := bstep (se 1 (by rfl) ⟨211109, by rfl⟩ : syracuseStep 281479 = 422219) B422219
theorem B1526663 : Blo 279826 1526663 := bstep (se 1 (by rfl) ⟨1144997, by rfl⟩ : syracuseStep 1526663 = 2289995) B2289995
theorem B281487 : Blo 279826 281487 := bstep (se 1 (by rfl) ⟨211115, by rfl⟩ : syracuseStep 281487 = 422231) B422231
theorem B281531 : Blo 279826 281531 := bstep (se 1 (by rfl) ⟨211148, by rfl⟩ : syracuseStep 281531 = 422297) B422297
theorem B281607 : Blo 279826 281607 := bstep (se 1 (by rfl) ⟨211205, by rfl⟩ : syracuseStep 281607 = 422411) B422411
theorem B281615 : Blo 279826 281615 := bstep (se 1 (by rfl) ⟨211211, by rfl⟩ : syracuseStep 281615 = 422423) B422423
theorem B281659 : Blo 279826 281659 := bstep (se 1 (by rfl) ⟨211244, by rfl⟩ : syracuseStep 281659 = 422489) B422489
theorem B904279 : Blo 279826 904279 := bstep (se 1 (by rfl) ⟨678209, by rfl⟩ : syracuseStep 904279 = 1356419) B1356419
theorem B281735 : Blo 279826 281735 := bstep (se 1 (by rfl) ⟨211301, by rfl⟩ : syracuseStep 281735 = 422603) B422603
theorem B281743 : Blo 279826 281743 := bstep (se 1 (by rfl) ⟨211307, by rfl⟩ : syracuseStep 281743 = 422615) B422615
theorem B281787 : Blo 279826 281787 := bstep (se 1 (by rfl) ⟨211340, by rfl⟩ : syracuseStep 281787 = 422681) B422681
theorem B904393 : Blo 279826 904393 := bstep (se 2 (by rfl) ⟨339147, by rfl⟩ : syracuseStep 904393 = 678295) B678295
theorem B2149577 : Blo 279826 2149577 := bstep (se 2 (by rfl) ⟨806091, by rfl⟩ : syracuseStep 2149577 = 1612183) B1612183
theorem B281863 : Blo 279826 281863 := bstep (se 1 (by rfl) ⟨211397, by rfl⟩ : syracuseStep 281863 = 422795) B422795
theorem B281871 : Blo 279826 281871 := bstep (se 1 (by rfl) ⟨211403, by rfl⟩ : syracuseStep 281871 = 422807) B422807
theorem B478507 : Blo 279826 478507 := bstep (se 1 (by rfl) ⟨358880, by rfl⟩ : syracuseStep 478507 = 717761) B717761
theorem B281915 : Blo 279826 281915 := bstep (se 1 (by rfl) ⟨211436, by rfl⟩ : syracuseStep 281915 = 422873) B422873
theorem B281991 : Blo 279826 281991 := bstep (se 1 (by rfl) ⟨211493, by rfl⟩ : syracuseStep 281991 = 422987) B422987
theorem B281999 : Blo 279826 281999 := bstep (se 1 (by rfl) ⟨211499, by rfl⟩ : syracuseStep 281999 = 422999) B422999
theorem B478649 : Blo 279826 478649 := bstep (se 2 (by rfl) ⟨179493, by rfl⟩ : syracuseStep 478649 = 358987) B358987
theorem B282043 : Blo 279826 282043 := bstep (se 1 (by rfl) ⟨211532, by rfl⟩ : syracuseStep 282043 = 423065) B423065
theorem B314887 : Blo 279826 314887 := bstep (se 1 (by rfl) ⟨236165, by rfl⟩ : syracuseStep 314887 = 472331) B472331
theorem B282119 : Blo 279826 282119 := bstep (se 1 (by rfl) ⟨211589, by rfl⟩ : syracuseStep 282119 = 423179) B423179
theorem B806411 : Blo 279826 806411 := bstep (se 1 (by rfl) ⟨604808, by rfl⟩ : syracuseStep 806411 = 1209617) B1209617
theorem B282127 : Blo 279826 282127 := bstep (se 1 (by rfl) ⟨211595, by rfl⟩ : syracuseStep 282127 = 423191) B423191
theorem B282171 : Blo 279826 282171 := bstep (se 1 (by rfl) ⟨211628, by rfl⟩ : syracuseStep 282171 = 423257) B423257
theorem B282247 : Blo 279826 282247 := bstep (se 1 (by rfl) ⟨211685, by rfl⟩ : syracuseStep 282247 = 423371) B423371
theorem B282255 : Blo 279826 282255 := bstep (se 1 (by rfl) ⟨211691, by rfl⟩ : syracuseStep 282255 = 423383) B423383
theorem B315067 : Blo 279826 315067 := bstep (se 1 (by rfl) ⟨236300, by rfl⟩ : syracuseStep 315067 = 472601) B472601
theorem B282299 : Blo 279826 282299 := bstep (se 1 (by rfl) ⟨211724, by rfl⟩ : syracuseStep 282299 = 423449) B423449
theorem B46157525 : Blo 279826 46157525 := bstep (se 7 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 46157525 = 1081817) B1081817
theorem B282375 : Blo 279826 282375 := bstep (se 1 (by rfl) ⟨211781, by rfl⟩ : syracuseStep 282375 = 423563) B423563
theorem B282383 : Blo 279826 282383 := bstep (se 1 (by rfl) ⟨211787, by rfl⟩ : syracuseStep 282383 = 423575) B423575
theorem B708385 : Blo 279826 708385 := bstep (se 2 (by rfl) ⟨265644, by rfl⟩ : syracuseStep 708385 = 531289) B531289
theorem B675643 : Blo 279826 675643 := bstep (se 1 (by rfl) ⟨506732, by rfl⟩ : syracuseStep 675643 = 1013465) B1013465
theorem B282427 : Blo 279826 282427 := bstep (se 1 (by rfl) ⟨211820, by rfl⟩ : syracuseStep 282427 = 423641) B423641
theorem B282503 : Blo 279826 282503 := bstep (se 1 (by rfl) ⟨211877, by rfl⟩ : syracuseStep 282503 = 423755) B423755
theorem B282511 : Blo 279826 282511 := bstep (se 1 (by rfl) ⟨211883, by rfl⟩ : syracuseStep 282511 = 423767) B423767
theorem B282555 : Blo 279826 282555 := bstep (se 1 (by rfl) ⟨211916, by rfl⟩ : syracuseStep 282555 = 423833) B423833
theorem B282631 : Blo 279826 282631 := bstep (se 1 (by rfl) ⟨211973, by rfl⟩ : syracuseStep 282631 = 423947) B423947
theorem B282639 : Blo 279826 282639 := bstep (se 1 (by rfl) ⟨211979, by rfl⟩ : syracuseStep 282639 = 423959) B423959
theorem B282683 : Blo 279826 282683 := bstep (se 1 (by rfl) ⟨212012, by rfl⟩ : syracuseStep 282683 = 424025) B424025
theorem B1364035 : Blo 279826 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B282759 : Blo 279826 282759 := bstep (se 1 (by rfl) ⟨212069, by rfl⟩ : syracuseStep 282759 = 424139) B424139
theorem B315535 : Blo 279826 315535 := bstep (se 1 (by rfl) ⟨236651, by rfl⟩ : syracuseStep 315535 = 473303) B473303
theorem B282767 : Blo 279826 282767 := bstep (se 1 (by rfl) ⟨212075, by rfl⟩ : syracuseStep 282767 = 424151) B424151
theorem B282811 : Blo 279826 282811 := bstep (se 1 (by rfl) ⟨212108, by rfl⟩ : syracuseStep 282811 = 424217) B424217
theorem B282887 : Blo 279826 282887 := bstep (se 1 (by rfl) ⟨212165, by rfl⟩ : syracuseStep 282887 = 424331) B424331
theorem B282895 : Blo 279826 282895 := bstep (se 1 (by rfl) ⟨212171, by rfl⟩ : syracuseStep 282895 = 424343) B424343
theorem B1429811 : Blo 279826 1429811 := bstep (se 1 (by rfl) ⟨1072358, by rfl⟩ : syracuseStep 1429811 = 2144717) B2144717
theorem B1986875 : Blo 279826 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B282939 : Blo 279826 282939 := bstep (se 1 (by rfl) ⟨212204, by rfl⟩ : syracuseStep 282939 = 424409) B424409
theorem B708983 : Blo 279826 708983 := bstep (se 1 (by rfl) ⟨531737, by rfl⟩ : syracuseStep 708983 = 1063475) B1063475
theorem B283015 : Blo 279826 283015 := bstep (se 1 (by rfl) ⟨212261, by rfl⟩ : syracuseStep 283015 = 424523) B424523
theorem B283023 : Blo 279826 283023 := bstep (se 1 (by rfl) ⟨212267, by rfl⟩ : syracuseStep 283023 = 424535) B424535
theorem B283067 : Blo 279826 283067 := bstep (se 1 (by rfl) ⟨212300, by rfl⟩ : syracuseStep 283067 = 424601) B424601
theorem B283143 : Blo 279826 283143 := bstep (se 1 (by rfl) ⟨212357, by rfl⟩ : syracuseStep 283143 = 424715) B424715
theorem B283151 : Blo 279826 283151 := bstep (se 1 (by rfl) ⟨212363, by rfl⟩ : syracuseStep 283151 = 424727) B424727
theorem B283195 : Blo 279826 283195 := bstep (se 1 (by rfl) ⟨212396, by rfl⟩ : syracuseStep 283195 = 424793) B424793
theorem B1430135 : Blo 279826 1430135 := bstep (se 1 (by rfl) ⟨1072601, by rfl⟩ : syracuseStep 1430135 = 2145203) B2145203
theorem B316039 : Blo 279826 316039 := bstep (se 1 (by rfl) ⟨237029, by rfl⟩ : syracuseStep 316039 = 474059) B474059
theorem B283271 : Blo 279826 283271 := bstep (se 1 (by rfl) ⟨212453, by rfl⟩ : syracuseStep 283271 = 424907) B424907
theorem B283279 : Blo 279826 283279 := bstep (se 1 (by rfl) ⟨212459, by rfl⟩ : syracuseStep 283279 = 424919) B424919
theorem B283323 : Blo 279826 283323 := bstep (se 1 (by rfl) ⟨212492, by rfl⟩ : syracuseStep 283323 = 424985) B424985
theorem B283399 : Blo 279826 283399 := bstep (se 1 (by rfl) ⟨212549, by rfl⟩ : syracuseStep 283399 = 425099) B425099
theorem B283407 : Blo 279826 283407 := bstep (se 1 (by rfl) ⟨212555, by rfl⟩ : syracuseStep 283407 = 425111) B425111
theorem B480043 : Blo 279826 480043 := bstep (se 1 (by rfl) ⟨360032, by rfl⟩ : syracuseStep 480043 = 720065) B720065
theorem B316219 : Blo 279826 316219 := bstep (se 1 (by rfl) ⟨237164, by rfl⟩ : syracuseStep 316219 = 474329) B474329
theorem B283451 : Blo 279826 283451 := bstep (se 1 (by rfl) ⟨212588, by rfl⟩ : syracuseStep 283451 = 425177) B425177
theorem B283527 : Blo 279826 283527 := bstep (se 1 (by rfl) ⟨212645, by rfl⟩ : syracuseStep 283527 = 425291) B425291
theorem B283535 : Blo 279826 283535 := bstep (se 1 (by rfl) ⟨212651, by rfl⟩ : syracuseStep 283535 = 425303) B425303
theorem B906137 : Blo 279826 906137 := bstep (se 2 (by rfl) ⟨339801, by rfl⟩ : syracuseStep 906137 = 679603) B679603
theorem B283579 : Blo 279826 283579 := bstep (se 1 (by rfl) ⟨212684, by rfl⟩ : syracuseStep 283579 = 425369) B425369
theorem B1659851 : Blo 279826 1659851 := bstep (se 1 (by rfl) ⟨1244888, by rfl⟩ : syracuseStep 1659851 = 2489777) B2489777
theorem B283655 : Blo 279826 283655 := bstep (se 1 (by rfl) ⟨212741, by rfl⟩ : syracuseStep 283655 = 425483) B425483
theorem B283663 : Blo 279826 283663 := bstep (se 1 (by rfl) ⟨212747, by rfl⟩ : syracuseStep 283663 = 425495) B425495
theorem B283707 : Blo 279826 283707 := bstep (se 1 (by rfl) ⟨212780, by rfl⟩ : syracuseStep 283707 = 425561) B425561
theorem B807995 : Blo 279826 807995 := bstep (se 1 (by rfl) ⟨605996, by rfl⟩ : syracuseStep 807995 = 1211993) B1211993
theorem B808051 : Blo 279826 808051 := bstep (se 1 (by rfl) ⟨606038, by rfl⟩ : syracuseStep 808051 = 1212077) B1212077
theorem B283783 : Blo 279826 283783 := bstep (se 1 (by rfl) ⟨212837, by rfl⟩ : syracuseStep 283783 = 425675) B425675
theorem B283791 : Blo 279826 283791 := bstep (se 1 (by rfl) ⟨212843, by rfl⟩ : syracuseStep 283791 = 425687) B425687
theorem B677065 : Blo 279826 677065 := bstep (se 2 (by rfl) ⟨253899, by rfl⟩ : syracuseStep 677065 = 507799) B507799
theorem B316687 : Blo 279826 316687 := bstep (se 1 (by rfl) ⟨237515, by rfl⟩ : syracuseStep 316687 = 475031) B475031
theorem B1431107 : Blo 279826 1431107 := bstep (se 1 (by rfl) ⟨1073330, by rfl⟩ : syracuseStep 1431107 = 2146661) B2146661
theorem B710279 : Blo 279826 710279 := bstep (se 1 (by rfl) ⟨532709, by rfl⟩ : syracuseStep 710279 = 1065419) B1065419
theorem B710329 : Blo 279826 710329 := bstep (se 2 (by rfl) ⟨266373, by rfl⟩ : syracuseStep 710329 = 532747) B532747
theorem B317191 : Blo 279826 317191 := bstep (se 1 (by rfl) ⟨237893, by rfl⟩ : syracuseStep 317191 = 475787) B475787
theorem B1431431 : Blo 279826 1431431 := bstep (se 1 (by rfl) ⟨1073573, by rfl⟩ : syracuseStep 1431431 = 2147147) B2147147
theorem B317371 : Blo 279826 317371 := bstep (se 1 (by rfl) ⟨238028, by rfl⟩ : syracuseStep 317371 = 476057) B476057
theorem B448571 : Blo 279826 448571 := bstep (se 1 (by rfl) ⟨336428, by rfl⟩ : syracuseStep 448571 = 672857) B672857
theorem B710927 : Blo 279826 710927 := bstep (se 1 (by rfl) ⟨533195, by rfl⟩ : syracuseStep 710927 = 1066391) B1066391
theorem B317839 : Blo 279826 317839 := bstep (se 1 (by rfl) ⟨238379, by rfl⟩ : syracuseStep 317839 = 476759) B476759
theorem B1169873 : Blo 279826 1169873 := bstep (se 2 (by rfl) ⟨438702, by rfl⟩ : syracuseStep 1169873 = 877405) B877405
theorem B1071569 : Blo 279826 1071569 := bstep (se 2 (by rfl) ⟨401838, by rfl⟩ : syracuseStep 1071569 = 803677) B803677
theorem B1530661 : Blo 279826 1530661 := bstep (se 4 (by rfl) ⟨143499, by rfl⟩ : syracuseStep 1530661 = 286999) B286999
theorem B318343 : Blo 279826 318343 := bstep (se 1 (by rfl) ⟨238757, by rfl⟩ : syracuseStep 318343 = 477515) B477515
theorem B1072025 : Blo 279826 1072025 := bstep (se 2 (by rfl) ⟨402009, by rfl⟩ : syracuseStep 1072025 = 804019) B804019
theorem B711625 : Blo 279826 711625 := bstep (se 2 (by rfl) ⟨266859, by rfl⟩ : syracuseStep 711625 = 533719) B533719
theorem B1596419 : Blo 279826 1596419 := bstep (se 1 (by rfl) ⟨1197314, by rfl⟩ : syracuseStep 1596419 = 2394629) B2394629
theorem B318523 : Blo 279826 318523 := bstep (se 1 (by rfl) ⟨238892, by rfl⟩ : syracuseStep 318523 = 477785) B477785
theorem B711767 : Blo 279826 711767 := bstep (se 1 (by rfl) ⟨533825, by rfl⟩ : syracuseStep 711767 = 1067651) B1067651
theorem B1629377 : Blo 279826 1629377 := bstep (se 2 (by rfl) ⟨611016, by rfl⟩ : syracuseStep 1629377 = 1222033) B1222033
theorem B14277829 : Blo 279826 14277829 := bstep (se 4 (by rfl) ⟨1338546, by rfl⟩ : syracuseStep 14277829 = 2677093) B2677093
theorem B318991 : Blo 279826 318991 := bstep (se 1 (by rfl) ⟨239243, by rfl⟩ : syracuseStep 318991 = 478487) B478487
theorem B2711333 : Blo 279826 2711333 := bstep (se 4 (by rfl) ⟨254187, by rfl⟩ : syracuseStep 2711333 = 508375) B508375
theorem B2416499 : Blo 279826 2416499 := bstep (se 1 (by rfl) ⟨1812374, by rfl⟩ : syracuseStep 2416499 = 3624749) B3624749
theorem B286651 : Blo 279826 286651 := bstep (se 1 (by rfl) ⟨214988, by rfl⟩ : syracuseStep 286651 = 429977) B429977
theorem B450505 : Blo 279826 450505 := bstep (se 2 (by rfl) ⟨168939, by rfl⟩ : syracuseStep 450505 = 337879) B337879
theorem B1204253 : Blo 279826 1204253 := bstep (se 3 (by rfl) ⟨225797, by rfl⟩ : syracuseStep 1204253 = 451595) B451595
theorem B1073195 : Blo 279826 1073195 := bstep (se 1 (by rfl) ⟨804896, by rfl⟩ : syracuseStep 1073195 = 1609793) B1609793
theorem B1466435 : Blo 279826 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B2416877 : Blo 279826 2416877 := bstep (se 3 (by rfl) ⟨453164, by rfl⟩ : syracuseStep 2416877 = 906329) B906329
theorem B1204627 : Blo 279826 1204627 := bstep (se 1 (by rfl) ⟨903470, by rfl⟩ : syracuseStep 1204627 = 1806941) B1806941
theorem B1368695 : Blo 279826 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B1532609 : Blo 279826 1532609 := bstep (se 2 (by rfl) ⟨574728, by rfl⟩ : syracuseStep 1532609 = 1149457) B1149457
theorem B713843 : Blo 279826 713843 := bstep (se 1 (by rfl) ⟨535382, by rfl⟩ : syracuseStep 713843 = 1070765) B1070765
theorem B3433589 : Blo 279826 3433589 := bstep (se 5 (by rfl) ⟨160949, by rfl⟩ : syracuseStep 3433589 = 321899) B321899
theorem B1434995 : Blo 279826 1434995 := bstep (se 1 (by rfl) ⟨1076246, by rfl⟩ : syracuseStep 1434995 = 2152493) B2152493
theorem B714359 : Blo 279826 714359 := bstep (se 1 (by rfl) ⟨535769, by rfl⟩ : syracuseStep 714359 = 1071539) B1071539
theorem B1435481 : Blo 279826 1435481 := bstep (se 2 (by rfl) ⟨538305, by rfl⟩ : syracuseStep 1435481 = 1076611) B1076611
theorem B419771 : Blo 279826 419771 := bstep (se 1 (by rfl) ⟨314828, by rfl⟩ : syracuseStep 419771 = 629657) B629657
theorem B681929 : Blo 279826 681929 := bstep (se 2 (by rfl) ⟨255723, by rfl⟩ : syracuseStep 681929 = 511447) B511447
theorem B1075153 : Blo 279826 1075153 := bstep (se 2 (by rfl) ⟨403182, by rfl⟩ : syracuseStep 1075153 = 806365) B806365
theorem B419831 : Blo 279826 419831 := bstep (se 1 (by rfl) ⟨314873, by rfl⟩ : syracuseStep 419831 = 629747) B629747
theorem B419855 : Blo 279826 419855 := bstep (se 1 (by rfl) ⟨314891, by rfl⟩ : syracuseStep 419855 = 629783) B629783
theorem B419897 : Blo 279826 419897 := bstep (se 2 (by rfl) ⟨157461, by rfl⟩ : syracuseStep 419897 = 314923) B314923
theorem B813143 : Blo 279826 813143 := bstep (se 1 (by rfl) ⟨609857, by rfl⟩ : syracuseStep 813143 = 1219715) B1219715
theorem B419975 : Blo 279826 419975 := bstep (se 1 (by rfl) ⟨314981, by rfl⟩ : syracuseStep 419975 = 629963) B629963
theorem B420011 : Blo 279826 420011 := bstep (se 1 (by rfl) ⟨315008, by rfl⟩ : syracuseStep 420011 = 630017) B630017
theorem B420041 : Blo 279826 420041 := bstep (se 2 (by rfl) ⟨157515, by rfl⟩ : syracuseStep 420041 = 315031) B315031
theorem B1075457 : Blo 279826 1075457 := bstep (se 2 (by rfl) ⟨403296, by rfl⟩ : syracuseStep 1075457 = 806593) B806593
theorem B12216581 : Blo 279826 12216581 := bstep (se 4 (by rfl) ⟨1145304, by rfl⟩ : syracuseStep 12216581 = 2290609) B2290609
theorem B420155 : Blo 279826 420155 := bstep (se 1 (by rfl) ⟨315116, by rfl⟩ : syracuseStep 420155 = 630233) B630233
theorem B420215 : Blo 279826 420215 := bstep (se 1 (by rfl) ⟨315161, by rfl⟩ : syracuseStep 420215 = 630323) B630323
theorem B420239 : Blo 279826 420239 := bstep (se 1 (by rfl) ⟨315179, by rfl⟩ : syracuseStep 420239 = 630359) B630359
theorem B420281 : Blo 279826 420281 := bstep (se 2 (by rfl) ⟨157605, by rfl⟩ : syracuseStep 420281 = 315211) B315211
theorem B2288081 : Blo 279826 2288081 := bstep (se 2 (by rfl) ⟨858030, by rfl⟩ : syracuseStep 2288081 = 1716061) B1716061
theorem B420359 : Blo 279826 420359 := bstep (se 1 (by rfl) ⟨315269, by rfl⟩ : syracuseStep 420359 = 630539) B630539
theorem B420395 : Blo 279826 420395 := bstep (se 1 (by rfl) ⟨315296, by rfl⟩ : syracuseStep 420395 = 630593) B630593
theorem B420425 : Blo 279826 420425 := bstep (se 2 (by rfl) ⟨157659, by rfl⟩ : syracuseStep 420425 = 315319) B315319
theorem B715351 : Blo 279826 715351 := bstep (se 1 (by rfl) ⟨536513, by rfl⟩ : syracuseStep 715351 = 1073027) B1073027
theorem B420539 : Blo 279826 420539 := bstep (se 1 (by rfl) ⟨315404, by rfl⟩ : syracuseStep 420539 = 630809) B630809
theorem B1075913 : Blo 279826 1075913 := bstep (se 2 (by rfl) ⟨403467, by rfl⟩ : syracuseStep 1075913 = 806935) B806935
theorem B420599 : Blo 279826 420599 := bstep (se 1 (by rfl) ⟨315449, by rfl⟩ : syracuseStep 420599 = 630899) B630899
theorem B420623 : Blo 279826 420623 := bstep (se 1 (by rfl) ⟨315467, by rfl⟩ : syracuseStep 420623 = 630935) B630935
theorem B420665 : Blo 279826 420665 := bstep (se 2 (by rfl) ⟨157749, by rfl⟩ : syracuseStep 420665 = 315499) B315499
theorem B813883 : Blo 279826 813883 := bstep (se 1 (by rfl) ⟨610412, by rfl⟩ : syracuseStep 813883 = 1220825) B1220825
theorem B420743 : Blo 279826 420743 := bstep (se 1 (by rfl) ⟨315557, by rfl⟩ : syracuseStep 420743 = 631115) B631115
theorem B715655 : Blo 279826 715655 := bstep (se 1 (by rfl) ⟨536741, by rfl⟩ : syracuseStep 715655 = 1073483) B1073483
theorem B420779 : Blo 279826 420779 := bstep (se 1 (by rfl) ⟨315584, by rfl⟩ : syracuseStep 420779 = 631169) B631169
theorem B420809 : Blo 279826 420809 := bstep (se 2 (by rfl) ⟨157803, by rfl⟩ : syracuseStep 420809 = 315607) B315607
theorem B715787 : Blo 279826 715787 := bstep (se 1 (by rfl) ⟨536840, by rfl⟩ : syracuseStep 715787 = 1073681) B1073681
theorem B420923 : Blo 279826 420923 := bstep (se 1 (by rfl) ⟨315692, by rfl⟩ : syracuseStep 420923 = 631385) B631385
theorem B420983 : Blo 279826 420983 := bstep (se 1 (by rfl) ⟨315737, by rfl⟩ : syracuseStep 420983 = 631475) B631475
theorem B421007 : Blo 279826 421007 := bstep (se 1 (by rfl) ⟨315755, by rfl⟩ : syracuseStep 421007 = 631511) B631511
theorem B421049 : Blo 279826 421049 := bstep (se 2 (by rfl) ⟨157893, by rfl⟩ : syracuseStep 421049 = 315787) B315787
theorem B421127 : Blo 279826 421127 := bstep (se 1 (by rfl) ⟨315845, by rfl⟩ : syracuseStep 421127 = 631691) B631691
theorem B421163 : Blo 279826 421163 := bstep (se 1 (by rfl) ⟨315872, by rfl⟩ : syracuseStep 421163 = 631745) B631745
theorem B421193 : Blo 279826 421193 := bstep (se 2 (by rfl) ⟨157947, by rfl⟩ : syracuseStep 421193 = 315895) B315895
theorem B945593 : Blo 279826 945593 := bstep (se 2 (by rfl) ⟨354597, by rfl⟩ : syracuseStep 945593 = 709195) B709195
theorem B421307 : Blo 279826 421307 := bstep (se 1 (by rfl) ⟨315980, by rfl⟩ : syracuseStep 421307 = 631961) B631961
theorem B1142225 : Blo 279826 1142225 := bstep (se 2 (by rfl) ⟨428334, by rfl⟩ : syracuseStep 1142225 = 856669) B856669
theorem B2125277 : Blo 279826 2125277 := bstep (se 3 (by rfl) ⟨398489, by rfl⟩ : syracuseStep 2125277 = 796979) B796979
theorem B2420189 : Blo 279826 2420189 := bstep (se 3 (by rfl) ⟨453785, by rfl⟩ : syracuseStep 2420189 = 907571) B907571
theorem B421367 : Blo 279826 421367 := bstep (se 1 (by rfl) ⟨316025, by rfl⟩ : syracuseStep 421367 = 632051) B632051
theorem B421391 : Blo 279826 421391 := bstep (se 1 (by rfl) ⟨316043, by rfl⟩ : syracuseStep 421391 = 632087) B632087
theorem B716303 : Blo 279826 716303 := bstep (se 1 (by rfl) ⟨537227, by rfl⟩ : syracuseStep 716303 = 1074455) B1074455
theorem B421433 : Blo 279826 421433 := bstep (se 2 (by rfl) ⟨158037, by rfl⟩ : syracuseStep 421433 = 316075) B316075
theorem B421511 : Blo 279826 421511 := bstep (se 1 (by rfl) ⟨316133, by rfl⟩ : syracuseStep 421511 = 632267) B632267
theorem B716435 : Blo 279826 716435 := bstep (se 1 (by rfl) ⟨537326, by rfl⟩ : syracuseStep 716435 = 1074653) B1074653
theorem B421547 : Blo 279826 421547 := bstep (se 1 (by rfl) ⟨316160, by rfl⟩ : syracuseStep 421547 = 632321) B632321
theorem B421577 : Blo 279826 421577 := bstep (se 2 (by rfl) ⟨158091, by rfl⟩ : syracuseStep 421577 = 316183) B316183
theorem B421691 : Blo 279826 421691 := bstep (se 1 (by rfl) ⟨316268, by rfl⟩ : syracuseStep 421691 = 632537) B632537
theorem B421751 : Blo 279826 421751 := bstep (se 1 (by rfl) ⟨316313, by rfl⟩ : syracuseStep 421751 = 632627) B632627
theorem B421775 : Blo 279826 421775 := bstep (se 1 (by rfl) ⟨316331, by rfl⟩ : syracuseStep 421775 = 632663) B632663
theorem B421817 : Blo 279826 421817 := bstep (se 2 (by rfl) ⟨158181, by rfl⟩ : syracuseStep 421817 = 316363) B316363
theorem B421895 : Blo 279826 421895 := bstep (se 1 (by rfl) ⟨316421, by rfl⟩ : syracuseStep 421895 = 632843) B632843
theorem B946187 : Blo 279826 946187 := bstep (se 1 (by rfl) ⟨709640, by rfl⟩ : syracuseStep 946187 = 1419281) B1419281
theorem B421931 : Blo 279826 421931 := bstep (se 1 (by rfl) ⟨316448, by rfl⟩ : syracuseStep 421931 = 632897) B632897
theorem B356395 : Blo 279826 356395 := bstep (se 1 (by rfl) ⟨267296, by rfl⟩ : syracuseStep 356395 = 534593) B534593
theorem B421961 : Blo 279826 421961 := bstep (se 2 (by rfl) ⟨158235, by rfl⟩ : syracuseStep 421961 = 316471) B316471
theorem B946295 : Blo 279826 946295 := bstep (se 1 (by rfl) ⟨709721, by rfl⟩ : syracuseStep 946295 = 1419443) B1419443
theorem B422075 : Blo 279826 422075 := bstep (se 1 (by rfl) ⟨316556, by rfl⟩ : syracuseStep 422075 = 633113) B633113
theorem B422135 : Blo 279826 422135 := bstep (se 1 (by rfl) ⟨316601, by rfl⟩ : syracuseStep 422135 = 633203) B633203
theorem B422159 : Blo 279826 422159 := bstep (se 1 (by rfl) ⟨316619, by rfl⟩ : syracuseStep 422159 = 633239) B633239
theorem B1208591 : Blo 279826 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B1798433 : Blo 279826 1798433 := bstep (se 2 (by rfl) ⟨674412, by rfl⟩ : syracuseStep 1798433 = 1348825) B1348825
theorem B422201 : Blo 279826 422201 := bstep (se 2 (by rfl) ⟨158325, by rfl⟩ : syracuseStep 422201 = 316651) B316651
theorem B422279 : Blo 279826 422279 := bstep (se 1 (by rfl) ⟨316709, by rfl⟩ : syracuseStep 422279 = 633419) B633419
theorem B422315 : Blo 279826 422315 := bstep (se 1 (by rfl) ⟨316736, by rfl⟩ : syracuseStep 422315 = 633473) B633473
theorem B1601977 : Blo 279826 1601977 := bstep (se 2 (by rfl) ⟨600741, by rfl⟩ : syracuseStep 1601977 = 1201483) B1201483
theorem B422345 : Blo 279826 422345 := bstep (se 2 (by rfl) ⟨158379, by rfl⟩ : syracuseStep 422345 = 316759) B316759
theorem B2421251 : Blo 279826 2421251 := bstep (se 1 (by rfl) ⟨1815938, by rfl⟩ : syracuseStep 2421251 = 3631877) B3631877
theorem B422459 : Blo 279826 422459 := bstep (se 1 (by rfl) ⟨316844, by rfl⟩ : syracuseStep 422459 = 633689) B633689
theorem B422519 : Blo 279826 422519 := bstep (se 1 (by rfl) ⟨316889, by rfl⟩ : syracuseStep 422519 = 633779) B633779
theorem B422543 : Blo 279826 422543 := bstep (se 1 (by rfl) ⟨316907, by rfl⟩ : syracuseStep 422543 = 633815) B633815
theorem B422585 : Blo 279826 422585 := bstep (se 2 (by rfl) ⟨158469, by rfl⟩ : syracuseStep 422585 = 316939) B316939
theorem B946889 : Blo 279826 946889 := bstep (se 2 (by rfl) ⟨355083, by rfl⟩ : syracuseStep 946889 = 710167) B710167
theorem B717569 : Blo 279826 717569 := bstep (se 2 (by rfl) ⟨269088, by rfl⟩ : syracuseStep 717569 = 538177) B538177
theorem B422663 : Blo 279826 422663 := bstep (se 1 (by rfl) ⟨316997, by rfl⟩ : syracuseStep 422663 = 633995) B633995
theorem B1012513 : Blo 279826 1012513 := bstep (se 2 (by rfl) ⟨379692, by rfl⟩ : syracuseStep 1012513 = 759385) B759385
theorem B5796643 : Blo 279826 5796643 := bstep (se 1 (by rfl) ⟨4347482, by rfl⟩ : syracuseStep 5796643 = 8694965) B8694965
theorem B422699 : Blo 279826 422699 := bstep (se 1 (by rfl) ⟨317024, by rfl⟩ : syracuseStep 422699 = 634049) B634049
theorem B422729 : Blo 279826 422729 := bstep (se 2 (by rfl) ⟨158523, by rfl⟩ : syracuseStep 422729 = 317047) B317047
theorem B422843 : Blo 279826 422843 := bstep (se 1 (by rfl) ⟨317132, by rfl⟩ : syracuseStep 422843 = 634265) B634265
theorem B422903 : Blo 279826 422903 := bstep (se 1 (by rfl) ⟨317177, by rfl⟩ : syracuseStep 422903 = 634355) B634355
theorem B357367 : Blo 279826 357367 := bstep (se 1 (by rfl) ⟨268025, by rfl⟩ : syracuseStep 357367 = 536051) B536051
theorem B422927 : Blo 279826 422927 := bstep (se 1 (by rfl) ⟨317195, by rfl⟩ : syracuseStep 422927 = 634391) B634391
theorem B422969 : Blo 279826 422969 := bstep (se 2 (by rfl) ⟨158613, by rfl⟩ : syracuseStep 422969 = 317227) B317227
theorem B717943 : Blo 279826 717943 := bstep (se 1 (by rfl) ⟨538457, by rfl⟩ : syracuseStep 717943 = 1076915) B1076915
theorem B423047 : Blo 279826 423047 := bstep (se 1 (by rfl) ⟨317285, by rfl⟩ : syracuseStep 423047 = 634571) B634571
theorem B423083 : Blo 279826 423083 := bstep (se 1 (by rfl) ⟨317312, by rfl⟩ : syracuseStep 423083 = 634625) B634625
theorem B423113 : Blo 279826 423113 := bstep (se 2 (by rfl) ⟨158667, by rfl⟩ : syracuseStep 423113 = 317335) B317335
theorem B423227 : Blo 279826 423227 := bstep (se 1 (by rfl) ⟨317420, by rfl⟩ : syracuseStep 423227 = 634841) B634841
theorem B357691 : Blo 279826 357691 := bstep (se 1 (by rfl) ⟨268268, by rfl⟩ : syracuseStep 357691 = 536537) B536537
theorem B423287 : Blo 279826 423287 := bstep (se 1 (by rfl) ⟨317465, by rfl⟩ : syracuseStep 423287 = 634931) B634931
theorem B947591 : Blo 279826 947591 := bstep (se 1 (by rfl) ⟨710693, by rfl⟩ : syracuseStep 947591 = 1421387) B1421387
theorem B423311 : Blo 279826 423311 := bstep (se 1 (by rfl) ⟨317483, by rfl⟩ : syracuseStep 423311 = 634967) B634967
theorem B423353 : Blo 279826 423353 := bstep (se 2 (by rfl) ⟨158757, by rfl⟩ : syracuseStep 423353 = 317515) B317515
theorem B423431 : Blo 279826 423431 := bstep (se 1 (by rfl) ⟨317573, by rfl⟩ : syracuseStep 423431 = 635147) B635147
theorem B423467 : Blo 279826 423467 := bstep (se 1 (by rfl) ⟨317600, by rfl⟩ : syracuseStep 423467 = 635201) B635201
theorem B718379 : Blo 279826 718379 := bstep (se 1 (by rfl) ⟨538784, by rfl⟩ : syracuseStep 718379 = 1077569) B1077569
theorem B423497 : Blo 279826 423497 := bstep (se 2 (by rfl) ⟨158811, by rfl⟩ : syracuseStep 423497 = 317623) B317623
theorem B423611 : Blo 279826 423611 := bstep (se 1 (by rfl) ⟨317708, by rfl⟩ : syracuseStep 423611 = 635417) B635417
theorem B423671 : Blo 279826 423671 := bstep (se 1 (by rfl) ⟨317753, by rfl⟩ : syracuseStep 423671 = 635507) B635507
theorem B947969 : Blo 279826 947969 := bstep (se 2 (by rfl) ⟨355488, by rfl⟩ : syracuseStep 947969 = 710977) B710977
theorem B423695 : Blo 279826 423695 := bstep (se 1 (by rfl) ⟨317771, by rfl⟩ : syracuseStep 423695 = 635543) B635543
theorem B2029349 : Blo 279826 2029349 := bstep (se 4 (by rfl) ⟨190251, by rfl⟩ : syracuseStep 2029349 = 380503) B380503
theorem B423737 : Blo 279826 423737 := bstep (se 2 (by rfl) ⟨158901, by rfl⟩ : syracuseStep 423737 = 317803) B317803
theorem B423815 : Blo 279826 423815 := bstep (se 1 (by rfl) ⟨317861, by rfl⟩ : syracuseStep 423815 = 635723) B635723
theorem B423851 : Blo 279826 423851 := bstep (se 1 (by rfl) ⟨317888, by rfl⟩ : syracuseStep 423851 = 635777) B635777
theorem B423881 : Blo 279826 423881 := bstep (se 2 (by rfl) ⟨158955, by rfl⟩ : syracuseStep 423881 = 317911) B317911
theorem B13694993 : Blo 279826 13694993 := bstep (se 2 (by rfl) ⟨5135622, by rfl⟩ : syracuseStep 13694993 = 10271245) B10271245
theorem B423995 : Blo 279826 423995 := bstep (se 1 (by rfl) ⟨317996, by rfl⟩ : syracuseStep 423995 = 635993) B635993
theorem B424055 : Blo 279826 424055 := bstep (se 1 (by rfl) ⟨318041, by rfl⟩ : syracuseStep 424055 = 636083) B636083
theorem B424079 : Blo 279826 424079 := bstep (se 1 (by rfl) ⟨318059, by rfl⟩ : syracuseStep 424079 = 636119) B636119
theorem B424121 : Blo 279826 424121 := bstep (se 2 (by rfl) ⟨159045, by rfl⟩ : syracuseStep 424121 = 318091) B318091
theorem B424199 : Blo 279826 424199 := bstep (se 1 (by rfl) ⟨318149, by rfl⟩ : syracuseStep 424199 = 636299) B636299
theorem B358663 : Blo 279826 358663 := bstep (se 1 (by rfl) ⟨268997, by rfl⟩ : syracuseStep 358663 = 537995) B537995
theorem B424235 : Blo 279826 424235 := bstep (se 1 (by rfl) ⟨318176, by rfl⟩ : syracuseStep 424235 = 636353) B636353
theorem B424265 : Blo 279826 424265 := bstep (se 2 (by rfl) ⟨159099, by rfl⟩ : syracuseStep 424265 = 318199) B318199
theorem B1309043 : Blo 279826 1309043 := bstep (se 1 (by rfl) ⟨981782, by rfl⟩ : syracuseStep 1309043 = 1963565) B1963565
theorem B424379 : Blo 279826 424379 := bstep (se 1 (by rfl) ⟨318284, by rfl⟩ : syracuseStep 424379 = 636569) B636569
theorem B424439 : Blo 279826 424439 := bstep (se 1 (by rfl) ⟨318329, by rfl⟩ : syracuseStep 424439 = 636659) B636659
theorem B424463 : Blo 279826 424463 := bstep (se 1 (by rfl) ⟨318347, by rfl⟩ : syracuseStep 424463 = 636695) B636695
theorem B1276445 : Blo 279826 1276445 := bstep (se 3 (by rfl) ⟨239333, by rfl⟩ : syracuseStep 1276445 = 478667) B478667
theorem B1079837 : Blo 279826 1079837 := bstep (se 3 (by rfl) ⟨202469, by rfl⟩ : syracuseStep 1079837 = 404939) B404939
theorem B948779 : Blo 279826 948779 := bstep (se 1 (by rfl) ⟨711584, by rfl⟩ : syracuseStep 948779 = 1423169) B1423169
theorem B424505 : Blo 279826 424505 := bstep (se 2 (by rfl) ⟨159189, by rfl⟩ : syracuseStep 424505 = 318379) B318379
theorem B424583 : Blo 279826 424583 := bstep (se 1 (by rfl) ⟨318437, by rfl⟩ : syracuseStep 424583 = 636875) B636875
theorem B424619 : Blo 279826 424619 := bstep (se 1 (by rfl) ⟨318464, by rfl⟩ : syracuseStep 424619 = 636929) B636929
theorem B359083 : Blo 279826 359083 := bstep (se 1 (by rfl) ⟨269312, by rfl⟩ : syracuseStep 359083 = 538625) B538625
theorem B424649 : Blo 279826 424649 := bstep (se 2 (by rfl) ⟨159243, by rfl⟩ : syracuseStep 424649 = 318487) B318487
theorem B424763 : Blo 279826 424763 := bstep (se 1 (by rfl) ⟨318572, by rfl⟩ : syracuseStep 424763 = 637145) B637145
theorem B424823 : Blo 279826 424823 := bstep (se 1 (by rfl) ⟨318617, by rfl⟩ : syracuseStep 424823 = 637235) B637235
theorem B424847 : Blo 279826 424847 := bstep (se 1 (by rfl) ⟨318635, by rfl⟩ : syracuseStep 424847 = 637271) B637271
theorem B424889 : Blo 279826 424889 := bstep (se 2 (by rfl) ⟨159333, by rfl⟩ : syracuseStep 424889 = 318667) B318667
theorem B424967 : Blo 279826 424967 := bstep (se 1 (by rfl) ⟨318725, by rfl⟩ : syracuseStep 424967 = 637451) B637451
theorem B425003 : Blo 279826 425003 := bstep (se 1 (by rfl) ⟨318752, by rfl⟩ : syracuseStep 425003 = 637505) B637505
theorem B425033 : Blo 279826 425033 := bstep (se 2 (by rfl) ⟨159387, by rfl⟩ : syracuseStep 425033 = 318775) B318775
theorem B425147 : Blo 279826 425147 := bstep (se 1 (by rfl) ⟨318860, by rfl⟩ : syracuseStep 425147 = 637721) B637721
theorem B1015021 : Blo 279826 1015021 := bstep (se 3 (by rfl) ⟨190316, by rfl⟩ : syracuseStep 1015021 = 380633) B380633
theorem B425207 : Blo 279826 425207 := bstep (se 1 (by rfl) ⟨318905, by rfl⟩ : syracuseStep 425207 = 637811) B637811
theorem B425231 : Blo 279826 425231 := bstep (se 1 (by rfl) ⟨318923, by rfl⟩ : syracuseStep 425231 = 637847) B637847
theorem B425273 : Blo 279826 425273 := bstep (se 2 (by rfl) ⟨159477, by rfl⟩ : syracuseStep 425273 = 318955) B318955
theorem B425351 : Blo 279826 425351 := bstep (se 1 (by rfl) ⟨319013, by rfl⟩ : syracuseStep 425351 = 638027) B638027
theorem B425387 : Blo 279826 425387 := bstep (se 1 (by rfl) ⟨319040, by rfl⟩ : syracuseStep 425387 = 638081) B638081
theorem B425417 : Blo 279826 425417 := bstep (se 2 (by rfl) ⟨159531, by rfl⟩ : syracuseStep 425417 = 319063) B319063
theorem B425531 : Blo 279826 425531 := bstep (se 1 (by rfl) ⟨319148, by rfl⟩ : syracuseStep 425531 = 638297) B638297
theorem B425591 : Blo 279826 425591 := bstep (se 1 (by rfl) ⟨319193, by rfl⟩ : syracuseStep 425591 = 638387) B638387
theorem B425615 : Blo 279826 425615 := bstep (se 1 (by rfl) ⟨319211, by rfl⟩ : syracuseStep 425615 = 638423) B638423
theorem B851609 : Blo 279826 851609 := bstep (se 2 (by rfl) ⟨319353, by rfl⟩ : syracuseStep 851609 = 638707) B638707
theorem B425657 : Blo 279826 425657 := bstep (se 2 (by rfl) ⟨159621, by rfl⟩ : syracuseStep 425657 = 319243) B319243
theorem B1146569 : Blo 279826 1146569 := bstep (se 2 (by rfl) ⟨429963, by rfl⟩ : syracuseStep 1146569 = 859927) B859927
theorem B425735 : Blo 279826 425735 := bstep (se 1 (by rfl) ⟨319301, by rfl⟩ : syracuseStep 425735 = 638603) B638603
theorem B950075 : Blo 279826 950075 := bstep (se 1 (by rfl) ⟨712556, by rfl⟩ : syracuseStep 950075 = 1425113) B1425113
theorem B950291 : Blo 279826 950291 := bstep (se 1 (by rfl) ⟨712718, by rfl⟩ : syracuseStep 950291 = 1425437) B1425437
theorem B1278067 : Blo 279826 1278067 := bstep (se 1 (by rfl) ⟨958550, by rfl⟩ : syracuseStep 1278067 = 1917101) B1917101
theorem B1016003 : Blo 279826 1016003 := bstep (se 1 (by rfl) ⟨762002, by rfl⟩ : syracuseStep 1016003 = 1524005) B1524005
theorem B950615 : Blo 279826 950615 := bstep (se 1 (by rfl) ⟨712961, by rfl⟩ : syracuseStep 950615 = 1425923) B1425923
theorem B1606169 : Blo 279826 1606169 := bstep (se 2 (by rfl) ⟨602313, by rfl⟩ : syracuseStep 1606169 = 1204627) B1204627
theorem B852923 : Blo 279826 852923 := bstep (se 1 (by rfl) ⟨639692, by rfl⟩ : syracuseStep 852923 = 1279385) B1279385
theorem B15205427 : Blo 279826 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B951695 : Blo 279826 951695 := bstep (se 1 (by rfl) ⟨713771, by rfl⟩ : syracuseStep 951695 = 1427543) B1427543
theorem B2033039 : Blo 279826 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B1181147 : Blo 279826 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B7177733 : Blo 279826 7177733 := bstep (se 4 (by rfl) ⟨672912, by rfl⟩ : syracuseStep 7177733 = 1345825) B1345825
theorem B2131595 : Blo 279826 2131595 := bstep (se 1 (by rfl) ⟨1598696, by rfl⟩ : syracuseStep 2131595 = 3197393) B3197393
theorem B952019 : Blo 279826 952019 := bstep (se 1 (by rfl) ⟨714014, by rfl⟩ : syracuseStep 952019 = 1428029) B1428029
theorem B1017775 : Blo 279826 1017775 := bstep (se 1 (by rfl) ⟨763331, by rfl⟩ : syracuseStep 1017775 = 1526663) B1526663
theorem B30771683 : Blo 279826 30771683 := bstep (se 1 (by rfl) ⟨23078762, by rfl⟩ : syracuseStep 30771683 = 46157525) B46157525
theorem B953207 : Blo 279826 953207 := bstep (se 1 (by rfl) ⟨714905, by rfl⟩ : syracuseStep 953207 = 1429811) B1429811
theorem B953423 : Blo 279826 953423 := bstep (se 1 (by rfl) ⟨715067, by rfl⟩ : syracuseStep 953423 = 1430135) B1430135
theorem B1609085 : Blo 279826 1609085 := bstep (se 3 (by rfl) ⟨301703, by rfl⟩ : syracuseStep 1609085 = 603407) B603407
theorem B2297261 : Blo 279826 2297261 := bstep (se 3 (by rfl) ⟨430736, by rfl⟩ : syracuseStep 2297261 = 861473) B861473
theorem B953801 : Blo 279826 953801 := bstep (se 2 (by rfl) ⟨357675, by rfl⟩ : syracuseStep 953801 = 715351) B715351
theorem B855539 : Blo 279826 855539 := bstep (se 1 (by rfl) ⟨641654, by rfl⟩ : syracuseStep 855539 = 1283309) B1283309
theorem B7179853 : Blo 279826 7179853 := bstep (se 3 (by rfl) ⟨1346222, by rfl⟩ : syracuseStep 7179853 = 2692445) B2692445
theorem B954071 : Blo 279826 954071 := bstep (se 1 (by rfl) ⟨715553, by rfl⟩ : syracuseStep 954071 = 1431107) B1431107
theorem B1085177 : Blo 279826 1085177 := bstep (se 2 (by rfl) ⟨406941, by rfl⟩ : syracuseStep 1085177 = 813883) B813883
theorem B1773305 : Blo 279826 1773305 := bstep (se 2 (by rfl) ⟨664989, by rfl⟩ : syracuseStep 1773305 = 1329979) B1329979
theorem B954287 : Blo 279826 954287 := bstep (se 1 (by rfl) ⟨715715, by rfl⟩ : syracuseStep 954287 = 1431431) B1431431
theorem B299047 : Blo 279826 299047 := bstep (se 1 (by rfl) ⟨224285, by rfl⟩ : syracuseStep 299047 = 448571) B448571
theorem B3281075 : Blo 279826 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B1413665 : Blo 279826 1413665 := bstep (se 2 (by rfl) ⟨530124, by rfl⟩ : syracuseStep 1413665 = 1060249) B1060249
theorem B1086251 : Blo 279826 1086251 := bstep (se 1 (by rfl) ⟨814688, by rfl⟩ : syracuseStep 1086251 = 1629377) B1629377
theorem B1610725 : Blo 279826 1610725 := bstep (se 4 (by rfl) ⟨151005, by rfl⟩ : syracuseStep 1610725 = 302011) B302011
theorem B2692115 : Blo 279826 2692115 := bstep (se 1 (by rfl) ⟨2019086, by rfl⟩ : syracuseStep 2692115 = 4038173) B4038173
theorem B1610999 : Blo 279826 1610999 := bstep (se 1 (by rfl) ⟨1208249, by rfl⟩ : syracuseStep 1610999 = 2416499) B2416499
theorem B1611251 : Blo 279826 1611251 := bstep (se 1 (by rfl) ⟨1208438, by rfl⟩ : syracuseStep 1611251 = 2416877) B2416877
theorem B1021739 : Blo 279826 1021739 := bstep (se 1 (by rfl) ⟨766304, by rfl⟩ : syracuseStep 1021739 = 1532609) B1532609
theorem B2135969 : Blo 279826 2135969 := bstep (se 2 (by rfl) ⟨800988, by rfl⟩ : syracuseStep 2135969 = 1601977) B1601977
theorem B399287 : Blo 279826 399287 := bstep (se 1 (by rfl) ⟨299465, by rfl⟩ : syracuseStep 399287 = 598931) B598931
theorem B956663 : Blo 279826 956663 := bstep (se 1 (by rfl) ⟨717497, by rfl⟩ : syracuseStep 956663 = 1434995) B1434995
theorem B1350017 : Blo 279826 1350017 := bstep (se 2 (by rfl) ⟨506256, by rfl⟩ : syracuseStep 1350017 = 1012513) B1012513
theorem B3545633 : Blo 279826 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B956987 : Blo 279826 956987 := bstep (se 1 (by rfl) ⟨717740, by rfl⟩ : syracuseStep 956987 = 1435481) B1435481
theorem B957257 : Blo 279826 957257 := bstep (se 2 (by rfl) ⟨358971, by rfl⟩ : syracuseStep 957257 = 717943) B717943
theorem B400745 : Blo 279826 400745 := bstep (se 2 (by rfl) ⟨150279, by rfl⟩ : syracuseStep 400745 = 300559) B300559
theorem B630395 : Blo 279826 630395 := bstep (se 1 (by rfl) ⟨472796, by rfl⟩ : syracuseStep 630395 = 945593) B945593
theorem B761483 : Blo 279826 761483 := bstep (se 1 (by rfl) ⟨571112, by rfl⟩ : syracuseStep 761483 = 1142225) B1142225
theorem B1416851 : Blo 279826 1416851 := bstep (se 1 (by rfl) ⟨1062638, by rfl⟩ : syracuseStep 1416851 = 2125277) B2125277
theorem B1613459 : Blo 279826 1613459 := bstep (se 1 (by rfl) ⟨1210094, by rfl⟩ : syracuseStep 1613459 = 2420189) B2420189
theorem B630521 : Blo 279826 630521 := bstep (se 2 (by rfl) ⟨236445, by rfl⟩ : syracuseStep 630521 = 472891) B472891
theorem B630791 : Blo 279826 630791 := bstep (se 1 (by rfl) ⟨473093, by rfl⟩ : syracuseStep 630791 = 946187) B946187
theorem B532489 : Blo 279826 532489 := bstep (se 2 (by rfl) ⟨199683, by rfl⟩ : syracuseStep 532489 = 399367) B399367
theorem B630863 : Blo 279826 630863 := bstep (se 1 (by rfl) ⟨473147, by rfl⟩ : syracuseStep 630863 = 946295) B946295
theorem B1614167 : Blo 279826 1614167 := bstep (se 1 (by rfl) ⟨1210625, by rfl⟩ : syracuseStep 1614167 = 2421251) B2421251
theorem B532831 : Blo 279826 532831 := bstep (se 1 (by rfl) ⟨399623, by rfl⟩ : syracuseStep 532831 = 799247) B799247
theorem B631259 : Blo 279826 631259 := bstep (se 1 (by rfl) ⟨473444, by rfl⟩ : syracuseStep 631259 = 946889) B946889
theorem B1352477 : Blo 279826 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B2040653 : Blo 279826 2040653 := bstep (se 3 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 2040653 = 765245) B765245
theorem B402283 : Blo 279826 402283 := bstep (se 1 (by rfl) ⟨301712, by rfl⟩ : syracuseStep 402283 = 603425) B603425
theorem B631727 : Blo 279826 631727 := bstep (se 1 (by rfl) ⟨473795, by rfl⟩ : syracuseStep 631727 = 947591) B947591
theorem B3875759 : Blo 279826 3875759 := bstep (se 1 (by rfl) ⟨2906819, by rfl⟩ : syracuseStep 3875759 = 5813639) B5813639
theorem B1811429 : Blo 279826 1811429 := bstep (se 4 (by rfl) ⟨169821, by rfl⟩ : syracuseStep 1811429 = 339643) B339643
theorem B2040881 : Blo 279826 2040881 := bstep (se 2 (by rfl) ⟨765330, by rfl⟩ : syracuseStep 2040881 = 1530661) B1530661
theorem B402511 : Blo 279826 402511 := bstep (se 1 (by rfl) ⟨301883, by rfl⟩ : syracuseStep 402511 = 603767) B603767
theorem B631979 : Blo 279826 631979 := bstep (se 1 (by rfl) ⟨473984, by rfl⟩ : syracuseStep 631979 = 947969) B947969
theorem B1352899 : Blo 279826 1352899 := bstep (se 1 (by rfl) ⟨1014674, by rfl⟩ : syracuseStep 1352899 = 2029349) B2029349
theorem B1713431 : Blo 279826 1713431 := bstep (se 1 (by rfl) ⟨1285073, by rfl⟩ : syracuseStep 1713431 = 2570147) B2570147
theorem B533947 : Blo 279826 533947 := bstep (se 1 (by rfl) ⟨400460, by rfl⟩ : syracuseStep 533947 = 800921) B800921
theorem B534023 : Blo 279826 534023 := bstep (se 1 (by rfl) ⟨400517, by rfl⟩ : syracuseStep 534023 = 801035) B801035
theorem B1353361 : Blo 279826 1353361 := bstep (se 2 (by rfl) ⟨507510, by rfl⟩ : syracuseStep 1353361 = 1015021) B1015021
theorem B3679937 : Blo 279826 3679937 := bstep (se 2 (by rfl) ⟨1379976, by rfl⟩ : syracuseStep 3679937 = 2759953) B2759953
theorem B632519 : Blo 279826 632519 := bstep (se 1 (by rfl) ⟨474389, by rfl⟩ : syracuseStep 632519 = 948779) B948779
theorem B3057517 : Blo 279826 3057517 := bstep (se 3 (by rfl) ⟨573284, by rfl⟩ : syracuseStep 3057517 = 1146569) B1146569
theorem B534433 : Blo 279826 534433 := bstep (se 2 (by rfl) ⟨200412, by rfl⟩ : syracuseStep 534433 = 400825) B400825
theorem B534775 : Blo 279826 534775 := bstep (se 1 (by rfl) ⟨401081, by rfl⟩ : syracuseStep 534775 = 802163) B802163
theorem B2402693 : Blo 279826 2402693 := bstep (se 4 (by rfl) ⟨225252, by rfl⟩ : syracuseStep 2402693 = 450505) B450505
theorem B567739 : Blo 279826 567739 := bstep (se 1 (by rfl) ⟨425804, by rfl⟩ : syracuseStep 567739 = 851609) B851609
theorem B633383 : Blo 279826 633383 := bstep (se 1 (by rfl) ⟨475037, by rfl⟩ : syracuseStep 633383 = 950075) B950075
theorem B535079 : Blo 279826 535079 := bstep (se 1 (by rfl) ⟨401309, by rfl⟩ : syracuseStep 535079 = 802619) B802619
theorem B3910493 : Blo 279826 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B633707 : Blo 279826 633707 := bstep (se 1 (by rfl) ⟨475280, by rfl⟩ : syracuseStep 633707 = 950561) B950561
theorem B633761 : Blo 279826 633761 := bstep (se 2 (by rfl) ⟨237660, by rfl⟩ : syracuseStep 633761 = 475321) B475321
theorem B601015 : Blo 279826 601015 := bstep (se 1 (by rfl) ⟨450761, by rfl⟩ : syracuseStep 601015 = 901523) B901523
theorem B634103 : Blo 279826 634103 := bstep (se 1 (by rfl) ⟨475577, by rfl⟩ : syracuseStep 634103 = 951155) B951155
theorem B2043251 : Blo 279826 2043251 := bstep (se 1 (by rfl) ⟨1532438, by rfl⟩ : syracuseStep 2043251 = 3064877) B3064877
theorem B2272967 : Blo 279826 2272967 := bstep (se 1 (by rfl) ⟨1704725, by rfl⟩ : syracuseStep 2272967 = 3409451) B3409451
theorem B634697 : Blo 279826 634697 := bstep (se 2 (by rfl) ⟨238011, by rfl⟩ : syracuseStep 634697 = 476023) B476023
theorem B3649853 : Blo 279826 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B536939 : Blo 279826 536939 := bstep (se 1 (by rfl) ⟨402704, by rfl⟩ : syracuseStep 536939 = 805409) B805409
theorem B602587 : Blo 279826 602587 := bstep (se 1 (by rfl) ⟨451940, by rfl⟩ : syracuseStep 602587 = 903881) B903881
theorem B537167 : Blo 279826 537167 := bstep (se 1 (by rfl) ⟨402875, by rfl⟩ : syracuseStep 537167 = 805751) B805751
theorem B635489 : Blo 279826 635489 := bstep (se 2 (by rfl) ⟨238308, by rfl⟩ : syracuseStep 635489 = 476617) B476617
theorem B1422035 : Blo 279826 1422035 := bstep (se 1 (by rfl) ⟨1066526, by rfl⟩ : syracuseStep 1422035 = 2133053) B2133053
theorem B1618717 : Blo 279826 1618717 := bstep (se 3 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 1618717 = 607019) B607019
theorem B635831 : Blo 279826 635831 := bstep (se 1 (by rfl) ⟨476873, by rfl⟩ : syracuseStep 635831 = 953747) B953747
theorem B537607 : Blo 279826 537607 := bstep (se 1 (by rfl) ⟨403205, by rfl⟩ : syracuseStep 537607 = 806411) B806411
theorem B898447 : Blo 279826 898447 := bstep (se 1 (by rfl) ⟨673835, by rfl⟩ : syracuseStep 898447 = 1347671) B1347671
theorem B636425 : Blo 279826 636425 := bstep (se 2 (by rfl) ⟨238659, by rfl⟩ : syracuseStep 636425 = 477319) B477319
theorem B1324583 : Blo 279826 1324583 := bstep (se 1 (by rfl) ⟨993437, by rfl⟩ : syracuseStep 1324583 = 1986875) B1986875
theorem B472655 : Blo 279826 472655 := bstep (se 1 (by rfl) ⟨354491, by rfl⟩ : syracuseStep 472655 = 708983) B708983
theorem B964243 : Blo 279826 964243 := bstep (se 1 (by rfl) ⟨723182, by rfl⟩ : syracuseStep 964243 = 1446365) B1446365
theorem B636767 : Blo 279826 636767 := bstep (se 1 (by rfl) ⟨477575, by rfl⟩ : syracuseStep 636767 = 955151) B955151
theorem B604091 : Blo 279826 604091 := bstep (se 1 (by rfl) ⟨453068, by rfl⟩ : syracuseStep 604091 = 906137) B906137
theorem B636947 : Blo 279826 636947 := bstep (se 1 (by rfl) ⟨477710, by rfl⟩ : syracuseStep 636947 = 955421) B955421
theorem B538663 : Blo 279826 538663 := bstep (se 1 (by rfl) ⟨403997, by rfl⟩ : syracuseStep 538663 = 807995) B807995
theorem B506027 : Blo 279826 506027 := bstep (se 1 (by rfl) ⟨379520, by rfl⟩ : syracuseStep 506027 = 759041) B759041
theorem B637289 : Blo 279826 637289 := bstep (se 2 (by rfl) ⟨238983, by rfl⟩ : syracuseStep 637289 = 477967) B477967
theorem B3684761 : Blo 279826 3684761 := bstep (se 2 (by rfl) ⟨1381785, by rfl⟩ : syracuseStep 3684761 = 2763571) B2763571
theorem B473519 : Blo 279826 473519 := bstep (se 1 (by rfl) ⟨355139, by rfl⟩ : syracuseStep 473519 = 710279) B710279
theorem B8141381 : Blo 279826 8141381 := bstep (se 4 (by rfl) ⟨763254, by rfl⟩ : syracuseStep 8141381 = 1526509) B1526509
theorem B801377 : Blo 279826 801377 := bstep (se 2 (by rfl) ⟨300516, by rfl⟩ : syracuseStep 801377 = 601033) B601033
theorem B473951 : Blo 279826 473951 := bstep (se 1 (by rfl) ⟨355463, by rfl⟩ : syracuseStep 473951 = 710927) B710927
theorem B1424303 : Blo 279826 1424303 := bstep (se 1 (by rfl) ⟨1068227, by rfl⟩ : syracuseStep 1424303 = 2136455) B2136455
theorem B637883 : Blo 279826 637883 := bstep (se 1 (by rfl) ⟨478412, by rfl⟩ : syracuseStep 637883 = 956825) B956825
theorem B638009 : Blo 279826 638009 := bstep (se 2 (by rfl) ⟨239253, by rfl⟩ : syracuseStep 638009 = 478507) B478507
theorem B2276599 : Blo 279826 2276599 := bstep (se 1 (by rfl) ⟨1707449, by rfl⟩ : syracuseStep 2276599 = 3414899) B3414899
theorem B1064279 : Blo 279826 1064279 := bstep (se 1 (by rfl) ⟨798209, by rfl⟩ : syracuseStep 1064279 = 1596419) B1596419
theorem B474511 : Blo 279826 474511 := bstep (se 1 (by rfl) ⟨355883, by rfl⟩ : syracuseStep 474511 = 711767) B711767
theorem B638351 : Blo 279826 638351 := bstep (se 1 (by rfl) ⟨478763, by rfl⟩ : syracuseStep 638351 = 957527) B957527
theorem B802493 : Blo 279826 802493 := bstep (se 3 (by rfl) ⟨150467, by rfl⟩ : syracuseStep 802493 = 300935) B300935
theorem B900857 : Blo 279826 900857 := bstep (se 2 (by rfl) ⟨337821, by rfl⟩ : syracuseStep 900857 = 675643) B675643
theorem B1818503 : Blo 279826 1818503 := bstep (se 1 (by rfl) ⟨1363877, by rfl⟩ : syracuseStep 1818503 = 2727755) B2727755
theorem B802835 : Blo 279826 802835 := bstep (se 1 (by rfl) ⟨602126, by rfl⟩ : syracuseStep 802835 = 1204253) B1204253
theorem B475193 : Blo 279826 475193 := bstep (se 2 (by rfl) ⟨178197, by rfl⟩ : syracuseStep 475193 = 356395) B356395
theorem B1818713 : Blo 279826 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B3850355 : Blo 279826 3850355 := bstep (se 1 (by rfl) ⟨2887766, by rfl⟩ : syracuseStep 3850355 = 5775533) B5775533
theorem B475895 : Blo 279826 475895 := bstep (se 1 (by rfl) ⟨356921, by rfl⟩ : syracuseStep 475895 = 713843) B713843
theorem B3490781 : Blo 279826 3490781 := bstep (se 3 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 3490781 = 1309043) B1309043
theorem B640057 : Blo 279826 640057 := bstep (se 2 (by rfl) ⟨240021, by rfl⟩ : syracuseStep 640057 = 480043) B480043
theorem B476239 : Blo 279826 476239 := bstep (se 1 (by rfl) ⟨357179, by rfl⟩ : syracuseStep 476239 = 714359) B714359
theorem B279847 : Blo 279826 279847 := bstep (se 1 (by rfl) ⟨209885, by rfl⟩ : syracuseStep 279847 = 419771) B419771
theorem B476489 : Blo 279826 476489 := bstep (se 2 (by rfl) ⟨178683, by rfl⟩ : syracuseStep 476489 = 357367) B357367
theorem B279887 : Blo 279826 279887 := bstep (se 1 (by rfl) ⟨209915, by rfl⟩ : syracuseStep 279887 = 419831) B419831
theorem B279903 : Blo 279826 279903 := bstep (se 1 (by rfl) ⟨209927, by rfl⟩ : syracuseStep 279903 = 419855) B419855
theorem B279931 : Blo 279826 279931 := bstep (se 1 (by rfl) ⟨209948, by rfl⟩ : syracuseStep 279931 = 419897) B419897
theorem B542095 : Blo 279826 542095 := bstep (se 1 (by rfl) ⟨406571, by rfl⟩ : syracuseStep 542095 = 813143) B813143
theorem B279983 : Blo 279826 279983 := bstep (se 1 (by rfl) ⟨209987, by rfl⟩ : syracuseStep 279983 = 419975) B419975
theorem B280007 : Blo 279826 280007 := bstep (se 1 (by rfl) ⟨210005, by rfl⟩ : syracuseStep 280007 = 420011) B420011
theorem B1230281 : Blo 279826 1230281 := bstep (se 2 (by rfl) ⟨461355, by rfl⟩ : syracuseStep 1230281 = 922711) B922711
theorem B280027 : Blo 279826 280027 := bstep (se 1 (by rfl) ⟨210020, by rfl⟩ : syracuseStep 280027 = 420041) B420041
theorem B8144387 : Blo 279826 8144387 := bstep (se 1 (by rfl) ⟨6108290, by rfl⟩ : syracuseStep 8144387 = 12216581) B12216581
theorem B673289 : Blo 279826 673289 := bstep (se 2 (by rfl) ⟨252483, by rfl⟩ : syracuseStep 673289 = 504967) B504967
theorem B280103 : Blo 279826 280103 := bstep (se 1 (by rfl) ⟨210077, by rfl⟩ : syracuseStep 280103 = 420155) B420155
theorem B280143 : Blo 279826 280143 := bstep (se 1 (by rfl) ⟨210107, by rfl⟩ : syracuseStep 280143 = 420215) B420215
theorem B280159 : Blo 279826 280159 := bstep (se 1 (by rfl) ⟨210119, by rfl⟩ : syracuseStep 280159 = 420239) B420239
theorem B902753 : Blo 279826 902753 := bstep (se 2 (by rfl) ⟨338532, by rfl⟩ : syracuseStep 902753 = 677065) B677065
theorem B280187 : Blo 279826 280187 := bstep (se 1 (by rfl) ⟨210140, by rfl⟩ : syracuseStep 280187 = 420281) B420281
theorem B1525387 : Blo 279826 1525387 := bstep (se 1 (by rfl) ⟨1144040, by rfl⟩ : syracuseStep 1525387 = 2288081) B2288081
theorem B280239 : Blo 279826 280239 := bstep (se 1 (by rfl) ⟨210179, by rfl⟩ : syracuseStep 280239 = 420359) B420359
theorem B280263 : Blo 279826 280263 := bstep (se 1 (by rfl) ⟨210197, by rfl⟩ : syracuseStep 280263 = 420395) B420395
theorem B280283 : Blo 279826 280283 := bstep (se 1 (by rfl) ⟨210212, by rfl⟩ : syracuseStep 280283 = 420425) B420425
theorem B476921 : Blo 279826 476921 := bstep (se 2 (by rfl) ⟨178845, by rfl⟩ : syracuseStep 476921 = 357691) B357691
theorem B280359 : Blo 279826 280359 := bstep (se 1 (by rfl) ⟨210269, by rfl⟩ : syracuseStep 280359 = 420539) B420539
theorem B280399 : Blo 279826 280399 := bstep (se 1 (by rfl) ⟨210299, by rfl⟩ : syracuseStep 280399 = 420599) B420599
theorem B280415 : Blo 279826 280415 := bstep (se 1 (by rfl) ⟨210311, by rfl⟩ : syracuseStep 280415 = 420623) B420623
theorem B280443 : Blo 279826 280443 := bstep (se 1 (by rfl) ⟨210332, by rfl⟩ : syracuseStep 280443 = 420665) B420665
theorem B280495 : Blo 279826 280495 := bstep (se 1 (by rfl) ⟨210371, by rfl⟩ : syracuseStep 280495 = 420743) B420743
theorem B477103 : Blo 279826 477103 := bstep (se 1 (by rfl) ⟨357827, by rfl⟩ : syracuseStep 477103 = 715655) B715655
theorem B280519 : Blo 279826 280519 := bstep (se 1 (by rfl) ⟨210389, by rfl⟩ : syracuseStep 280519 = 420779) B420779
theorem B280539 : Blo 279826 280539 := bstep (se 1 (by rfl) ⟨210404, by rfl⟩ : syracuseStep 280539 = 420809) B420809
theorem B477191 : Blo 279826 477191 := bstep (se 1 (by rfl) ⟨357893, by rfl⟩ : syracuseStep 477191 = 715787) B715787
theorem B968723 : Blo 279826 968723 := bstep (se 1 (by rfl) ⟨726542, by rfl⟩ : syracuseStep 968723 = 1453085) B1453085
theorem B280615 : Blo 279826 280615 := bstep (se 1 (by rfl) ⟨210461, by rfl⟩ : syracuseStep 280615 = 420923) B420923
theorem B1624121 : Blo 279826 1624121 := bstep (se 2 (by rfl) ⟨609045, by rfl⟩ : syracuseStep 1624121 = 1218091) B1218091
theorem B280655 : Blo 279826 280655 := bstep (se 1 (by rfl) ⟨210491, by rfl⟩ : syracuseStep 280655 = 420983) B420983
theorem B280671 : Blo 279826 280671 := bstep (se 1 (by rfl) ⟨210503, by rfl⟩ : syracuseStep 280671 = 421007) B421007
theorem B280699 : Blo 279826 280699 := bstep (se 1 (by rfl) ⟨210524, by rfl⟩ : syracuseStep 280699 = 421049) B421049
theorem B1067165 : Blo 279826 1067165 := bstep (se 3 (by rfl) ⟨200093, by rfl⟩ : syracuseStep 1067165 = 400187) B400187
theorem B280751 : Blo 279826 280751 := bstep (se 1 (by rfl) ⟨210563, by rfl⟩ : syracuseStep 280751 = 421127) B421127
theorem B280775 : Blo 279826 280775 := bstep (se 1 (by rfl) ⟨210581, by rfl⟩ : syracuseStep 280775 = 421163) B421163
theorem B280795 : Blo 279826 280795 := bstep (se 1 (by rfl) ⟨210596, by rfl⟩ : syracuseStep 280795 = 421193) B421193
theorem B280871 : Blo 279826 280871 := bstep (se 1 (by rfl) ⟨210653, by rfl⟩ : syracuseStep 280871 = 421307) B421307
theorem B280911 : Blo 279826 280911 := bstep (se 1 (by rfl) ⟨210683, by rfl⟩ : syracuseStep 280911 = 421367) B421367
theorem B477535 : Blo 279826 477535 := bstep (se 1 (by rfl) ⟨358151, by rfl⟩ : syracuseStep 477535 = 716303) B716303
theorem B280927 : Blo 279826 280927 := bstep (se 1 (by rfl) ⟨210695, by rfl⟩ : syracuseStep 280927 = 421391) B421391
theorem B280955 : Blo 279826 280955 := bstep (se 1 (by rfl) ⟨210716, by rfl⟩ : syracuseStep 280955 = 421433) B421433
theorem B281007 : Blo 279826 281007 := bstep (se 1 (by rfl) ⟨210755, by rfl⟩ : syracuseStep 281007 = 421511) B421511
theorem B16566707 : Blo 279826 16566707 := bstep (se 1 (by rfl) ⟨12425030, by rfl⟩ : syracuseStep 16566707 = 24850061) B24850061
theorem B477623 : Blo 279826 477623 := bstep (se 1 (by rfl) ⟨358217, by rfl⟩ : syracuseStep 477623 = 716435) B716435
theorem B281031 : Blo 279826 281031 := bstep (se 1 (by rfl) ⟨210773, by rfl⟩ : syracuseStep 281031 = 421547) B421547
theorem B281051 : Blo 279826 281051 := bstep (se 1 (by rfl) ⟨210788, by rfl⟩ : syracuseStep 281051 = 421577) B421577
theorem B2017817 : Blo 279826 2017817 := bstep (se 2 (by rfl) ⟨756681, by rfl⟩ : syracuseStep 2017817 = 1513363) B1513363
theorem B281127 : Blo 279826 281127 := bstep (se 1 (by rfl) ⟨210845, by rfl⟩ : syracuseStep 281127 = 421691) B421691
theorem B281167 : Blo 279826 281167 := bstep (se 1 (by rfl) ⟨210875, by rfl⟩ : syracuseStep 281167 = 421751) B421751
theorem B281183 : Blo 279826 281183 := bstep (se 1 (by rfl) ⟨210887, by rfl⟩ : syracuseStep 281183 = 421775) B421775
theorem B281211 : Blo 279826 281211 := bstep (se 1 (by rfl) ⟨210908, by rfl⟩ : syracuseStep 281211 = 421817) B421817
theorem B281263 : Blo 279826 281263 := bstep (se 1 (by rfl) ⟨210947, by rfl⟩ : syracuseStep 281263 = 421895) B421895
theorem B903869 : Blo 279826 903869 := bstep (se 3 (by rfl) ⟨169475, by rfl⟩ : syracuseStep 903869 = 338951) B338951
theorem B281287 : Blo 279826 281287 := bstep (se 1 (by rfl) ⟨210965, by rfl⟩ : syracuseStep 281287 = 421931) B421931
theorem B2214611 : Blo 279826 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B281307 : Blo 279826 281307 := bstep (se 1 (by rfl) ⟨210980, by rfl⟩ : syracuseStep 281307 = 421961) B421961
theorem B281383 : Blo 279826 281383 := bstep (se 1 (by rfl) ⟨211037, by rfl⟩ : syracuseStep 281383 = 422075) B422075
theorem B1198921 : Blo 279826 1198921 := bstep (se 2 (by rfl) ⟨449595, by rfl⟩ : syracuseStep 1198921 = 899191) B899191
theorem B1067849 : Blo 279826 1067849 := bstep (se 2 (by rfl) ⟨400443, by rfl⟩ : syracuseStep 1067849 = 800887) B800887
theorem B281423 : Blo 279826 281423 := bstep (se 1 (by rfl) ⟨211067, by rfl⟩ : syracuseStep 281423 = 422135) B422135
theorem B281439 : Blo 279826 281439 := bstep (se 1 (by rfl) ⟨211079, by rfl⟩ : syracuseStep 281439 = 422159) B422159
theorem B805727 : Blo 279826 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B1198955 : Blo 279826 1198955 := bstep (se 1 (by rfl) ⟨899216, by rfl⟩ : syracuseStep 1198955 = 1798433) B1798433
theorem B281467 : Blo 279826 281467 := bstep (se 1 (by rfl) ⟨211100, by rfl⟩ : syracuseStep 281467 = 422201) B422201
theorem B281519 : Blo 279826 281519 := bstep (se 1 (by rfl) ⟨211139, by rfl⟩ : syracuseStep 281519 = 422279) B422279
theorem B281543 : Blo 279826 281543 := bstep (se 1 (by rfl) ⟨211157, by rfl⟩ : syracuseStep 281543 = 422315) B422315
theorem B281563 : Blo 279826 281563 := bstep (se 1 (by rfl) ⟨211172, by rfl⟩ : syracuseStep 281563 = 422345) B422345
theorem B478217 : Blo 279826 478217 := bstep (se 2 (by rfl) ⟨179331, by rfl⟩ : syracuseStep 478217 = 358663) B358663
theorem B281639 : Blo 279826 281639 := bstep (se 1 (by rfl) ⟨211229, by rfl⟩ : syracuseStep 281639 = 422459) B422459
theorem B281679 : Blo 279826 281679 := bstep (se 1 (by rfl) ⟨211259, by rfl⟩ : syracuseStep 281679 = 422519) B422519
theorem B281695 : Blo 279826 281695 := bstep (se 1 (by rfl) ⟨211271, by rfl⟩ : syracuseStep 281695 = 422543) B422543
theorem B281723 : Blo 279826 281723 := bstep (se 1 (by rfl) ⟨211292, by rfl⟩ : syracuseStep 281723 = 422585) B422585
theorem B478379 : Blo 279826 478379 := bstep (se 1 (by rfl) ⟨358784, by rfl⟩ : syracuseStep 478379 = 717569) B717569
theorem B281775 : Blo 279826 281775 := bstep (se 1 (by rfl) ⟨211331, by rfl⟩ : syracuseStep 281775 = 422663) B422663
theorem B281799 : Blo 279826 281799 := bstep (se 1 (by rfl) ⟨211349, by rfl⟩ : syracuseStep 281799 = 422699) B422699
theorem B281819 : Blo 279826 281819 := bstep (se 1 (by rfl) ⟨211364, by rfl⟩ : syracuseStep 281819 = 422729) B422729
theorem B281895 : Blo 279826 281895 := bstep (se 1 (by rfl) ⟨211421, by rfl⟩ : syracuseStep 281895 = 422843) B422843
theorem B1068349 : Blo 279826 1068349 := bstep (se 3 (by rfl) ⟨200315, by rfl⟩ : syracuseStep 1068349 = 400631) B400631
theorem B281935 : Blo 279826 281935 := bstep (se 1 (by rfl) ⟨211451, by rfl⟩ : syracuseStep 281935 = 422903) B422903
theorem B281951 : Blo 279826 281951 := bstep (se 1 (by rfl) ⟨211463, by rfl⟩ : syracuseStep 281951 = 422927) B422927
theorem B281979 : Blo 279826 281979 := bstep (se 1 (by rfl) ⟨211484, by rfl⟩ : syracuseStep 281979 = 422969) B422969
theorem B282031 : Blo 279826 282031 := bstep (se 1 (by rfl) ⟨211523, by rfl⟩ : syracuseStep 282031 = 423047) B423047
theorem B282055 : Blo 279826 282055 := bstep (se 1 (by rfl) ⟨211541, by rfl⟩ : syracuseStep 282055 = 423083) B423083
theorem B282075 : Blo 279826 282075 := bstep (se 1 (by rfl) ⟨211556, by rfl⟩ : syracuseStep 282075 = 423113) B423113
theorem B282151 : Blo 279826 282151 := bstep (se 1 (by rfl) ⟨211613, by rfl⟩ : syracuseStep 282151 = 423227) B423227
theorem B478777 : Blo 279826 478777 := bstep (se 2 (by rfl) ⟨179541, by rfl⟩ : syracuseStep 478777 = 359083) B359083
theorem B314959 : Blo 279826 314959 := bstep (se 1 (by rfl) ⟨236219, by rfl⟩ : syracuseStep 314959 = 472439) B472439
theorem B282191 : Blo 279826 282191 := bstep (se 1 (by rfl) ⟨211643, by rfl⟩ : syracuseStep 282191 = 423287) B423287
theorem B282207 : Blo 279826 282207 := bstep (se 1 (by rfl) ⟨211655, by rfl⟩ : syracuseStep 282207 = 423311) B423311
theorem B282235 : Blo 279826 282235 := bstep (se 1 (by rfl) ⟨211676, by rfl⟩ : syracuseStep 282235 = 423353) B423353
theorem B282287 : Blo 279826 282287 := bstep (se 1 (by rfl) ⟨211715, by rfl⟩ : syracuseStep 282287 = 423431) B423431
theorem B282311 : Blo 279826 282311 := bstep (se 1 (by rfl) ⟨211733, by rfl⟩ : syracuseStep 282311 = 423467) B423467
theorem B478919 : Blo 279826 478919 := bstep (se 1 (by rfl) ⟨359189, by rfl⟩ : syracuseStep 478919 = 718379) B718379
theorem B282331 : Blo 279826 282331 := bstep (se 1 (by rfl) ⟨211748, by rfl⟩ : syracuseStep 282331 = 423497) B423497
theorem B282407 : Blo 279826 282407 := bstep (se 1 (by rfl) ⟨211805, by rfl⟩ : syracuseStep 282407 = 423611) B423611
theorem B282447 : Blo 279826 282447 := bstep (se 1 (by rfl) ⟨211835, by rfl⟩ : syracuseStep 282447 = 423671) B423671
theorem B282463 : Blo 279826 282463 := bstep (se 1 (by rfl) ⟨211847, by rfl⟩ : syracuseStep 282463 = 423695) B423695
theorem B282491 : Blo 279826 282491 := bstep (se 1 (by rfl) ⟨211868, by rfl⟩ : syracuseStep 282491 = 423737) B423737
theorem B3198851 : Blo 279826 3198851 := bstep (se 1 (by rfl) ⟨2399138, by rfl⟩ : syracuseStep 3198851 = 4798277) B4798277
theorem B708527 : Blo 279826 708527 := bstep (se 1 (by rfl) ⟨531395, by rfl⟩ : syracuseStep 708527 = 1062791) B1062791
theorem B282543 : Blo 279826 282543 := bstep (se 1 (by rfl) ⟨211907, by rfl⟩ : syracuseStep 282543 = 423815) B423815
theorem B282567 : Blo 279826 282567 := bstep (se 1 (by rfl) ⟨211925, by rfl⟩ : syracuseStep 282567 = 423851) B423851
theorem B315355 : Blo 279826 315355 := bstep (se 1 (by rfl) ⟨236516, by rfl⟩ : syracuseStep 315355 = 473033) B473033
theorem B282587 : Blo 279826 282587 := bstep (se 1 (by rfl) ⟨211940, by rfl⟩ : syracuseStep 282587 = 423881) B423881
theorem B9129995 : Blo 279826 9129995 := bstep (se 1 (by rfl) ⟨6847496, by rfl⟩ : syracuseStep 9129995 = 13694993) B13694993
theorem B282663 : Blo 279826 282663 := bstep (se 1 (by rfl) ⟨211997, by rfl⟩ : syracuseStep 282663 = 423995) B423995
theorem B282703 : Blo 279826 282703 := bstep (se 1 (by rfl) ⟨212027, by rfl⟩ : syracuseStep 282703 = 424055) B424055
theorem B282719 : Blo 279826 282719 := bstep (se 1 (by rfl) ⟨212039, by rfl⟩ : syracuseStep 282719 = 424079) B424079
theorem B282747 : Blo 279826 282747 := bstep (se 1 (by rfl) ⟨212060, by rfl⟩ : syracuseStep 282747 = 424121) B424121
theorem B2019491 : Blo 279826 2019491 := bstep (se 1 (by rfl) ⟨1514618, by rfl⟩ : syracuseStep 2019491 = 3029237) B3029237
theorem B282799 : Blo 279826 282799 := bstep (se 1 (by rfl) ⟨212099, by rfl⟩ : syracuseStep 282799 = 424199) B424199
theorem B282823 : Blo 279826 282823 := bstep (se 1 (by rfl) ⟨212117, by rfl⟩ : syracuseStep 282823 = 424235) B424235
theorem B282843 : Blo 279826 282843 := bstep (se 1 (by rfl) ⟨212132, by rfl⟩ : syracuseStep 282843 = 424265) B424265
theorem B282919 : Blo 279826 282919 := bstep (se 1 (by rfl) ⟨212189, by rfl⟩ : syracuseStep 282919 = 424379) B424379
theorem B282959 : Blo 279826 282959 := bstep (se 1 (by rfl) ⟨212219, by rfl⟩ : syracuseStep 282959 = 424439) B424439
theorem B282975 : Blo 279826 282975 := bstep (se 1 (by rfl) ⟨212231, by rfl⟩ : syracuseStep 282975 = 424463) B424463
theorem B283003 : Blo 279826 283003 := bstep (se 1 (by rfl) ⟨212252, by rfl⟩ : syracuseStep 283003 = 424505) B424505
theorem B315823 : Blo 279826 315823 := bstep (se 1 (by rfl) ⟨236867, by rfl⟩ : syracuseStep 315823 = 473735) B473735
theorem B283055 : Blo 279826 283055 := bstep (se 1 (by rfl) ⟨212291, by rfl⟩ : syracuseStep 283055 = 424583) B424583
theorem B283079 : Blo 279826 283079 := bstep (se 1 (by rfl) ⟨212309, by rfl⟩ : syracuseStep 283079 = 424619) B424619
theorem B283099 : Blo 279826 283099 := bstep (se 1 (by rfl) ⟨212324, by rfl⟩ : syracuseStep 283099 = 424649) B424649
theorem B709145 : Blo 279826 709145 := bstep (se 2 (by rfl) ⟨265929, by rfl⟩ : syracuseStep 709145 = 531859) B531859
theorem B283175 : Blo 279826 283175 := bstep (se 1 (by rfl) ⟨212381, by rfl⟩ : syracuseStep 283175 = 424763) B424763
theorem B283215 : Blo 279826 283215 := bstep (se 1 (by rfl) ⟨212411, by rfl⟩ : syracuseStep 283215 = 424823) B424823
theorem B283231 : Blo 279826 283231 := bstep (se 1 (by rfl) ⟨212423, by rfl⟩ : syracuseStep 283231 = 424847) B424847
theorem B283259 : Blo 279826 283259 := bstep (se 1 (by rfl) ⟨212444, by rfl⟩ : syracuseStep 283259 = 424889) B424889
theorem B283311 : Blo 279826 283311 := bstep (se 1 (by rfl) ⟨212483, by rfl⟩ : syracuseStep 283311 = 424967) B424967
theorem B283335 : Blo 279826 283335 := bstep (se 1 (by rfl) ⟨212501, by rfl⟩ : syracuseStep 283335 = 425003) B425003
theorem B283355 : Blo 279826 283355 := bstep (se 1 (by rfl) ⟨212516, by rfl⟩ : syracuseStep 283355 = 425033) B425033
theorem B7230221 : Blo 279826 7230221 := bstep (se 3 (by rfl) ⟨1355666, by rfl⟩ : syracuseStep 7230221 = 2711333) B2711333
theorem B283431 : Blo 279826 283431 := bstep (se 1 (by rfl) ⟨212573, by rfl⟩ : syracuseStep 283431 = 425147) B425147
theorem B283471 : Blo 279826 283471 := bstep (se 1 (by rfl) ⟨212603, by rfl⟩ : syracuseStep 283471 = 425207) B425207
theorem B316255 : Blo 279826 316255 := bstep (se 1 (by rfl) ⟨237191, by rfl⟩ : syracuseStep 316255 = 474383) B474383
theorem B283487 : Blo 279826 283487 := bstep (se 1 (by rfl) ⟨212615, by rfl⟩ : syracuseStep 283487 = 425231) B425231
theorem B283515 : Blo 279826 283515 := bstep (se 1 (by rfl) ⟨212636, by rfl⟩ : syracuseStep 283515 = 425273) B425273
theorem B2020241 : Blo 279826 2020241 := bstep (se 2 (by rfl) ⟨757590, by rfl⟩ : syracuseStep 2020241 = 1515181) B1515181
theorem B283567 : Blo 279826 283567 := bstep (se 1 (by rfl) ⟨212675, by rfl⟩ : syracuseStep 283567 = 425351) B425351
theorem B283591 : Blo 279826 283591 := bstep (se 1 (by rfl) ⟨212693, by rfl⟩ : syracuseStep 283591 = 425387) B425387
theorem B283611 : Blo 279826 283611 := bstep (se 1 (by rfl) ⟨212708, by rfl⟩ : syracuseStep 283611 = 425417) B425417
theorem B1070081 : Blo 279826 1070081 := bstep (se 2 (by rfl) ⟨401280, by rfl⟩ : syracuseStep 1070081 = 802561) B802561
theorem B283687 : Blo 279826 283687 := bstep (se 1 (by rfl) ⟨212765, by rfl⟩ : syracuseStep 283687 = 425531) B425531
theorem B283727 : Blo 279826 283727 := bstep (se 1 (by rfl) ⟨212795, by rfl⟩ : syracuseStep 283727 = 425591) B425591
theorem B283743 : Blo 279826 283743 := bstep (se 1 (by rfl) ⟨212807, by rfl⟩ : syracuseStep 283743 = 425615) B425615
theorem B283771 : Blo 279826 283771 := bstep (se 1 (by rfl) ⟨212828, by rfl⟩ : syracuseStep 283771 = 425657) B425657
theorem B283823 : Blo 279826 283823 := bstep (se 1 (by rfl) ⟨212867, by rfl⟩ : syracuseStep 283823 = 425735) B425735
theorem B316615 : Blo 279826 316615 := bstep (se 1 (by rfl) ⟨237461, by rfl⟩ : syracuseStep 316615 = 474923) B474923
theorem B382201 : Blo 279826 382201 := bstep (se 2 (by rfl) ⟨143325, by rfl⟩ : syracuseStep 382201 = 286651) B286651
theorem B15324551 : Blo 279826 15324551 := bstep (se 1 (by rfl) ⟨11493413, by rfl⟩ : syracuseStep 15324551 = 22986827) B22986827
theorem B284239 : Blo 279826 284239 := bstep (se 1 (by rfl) ⟨213179, by rfl⟩ : syracuseStep 284239 = 426359) B426359
theorem B317479 : Blo 279826 317479 := bstep (se 1 (by rfl) ⟨238109, by rfl⟩ : syracuseStep 317479 = 476219) B476219
theorem B284891 : Blo 279826 284891 := bstep (se 1 (by rfl) ⟨213668, by rfl⟩ : syracuseStep 284891 = 427337) B427337
theorem B1137001 : Blo 279826 1137001 := bstep (se 2 (by rfl) ⟨426375, by rfl⟩ : syracuseStep 1137001 = 852751) B852751
theorem B1595963 : Blo 279826 1595963 := bstep (se 1 (by rfl) ⟨1196972, by rfl⟩ : syracuseStep 1595963 = 2393945) B2393945
theorem B3758669 : Blo 279826 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B1071751 : Blo 279826 1071751 := bstep (se 1 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 1071751 = 1607627) B1607627
theorem B1038995 : Blo 279826 1038995 := bstep (se 1 (by rfl) ⟨779246, by rfl⟩ : syracuseStep 1038995 = 1558493) B1558493
theorem B4414283 : Blo 279826 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B1072055 : Blo 279826 1072055 := bstep (se 1 (by rfl) ⟨804041, by rfl⟩ : syracuseStep 1072055 = 1608083) B1608083
theorem B449545 : Blo 279826 449545 := bstep (se 2 (by rfl) ⟨168579, by rfl⟩ : syracuseStep 449545 = 337159) B337159
theorem B711737 : Blo 279826 711737 := bstep (se 2 (by rfl) ⟨266901, by rfl⟩ : syracuseStep 711737 = 533803) B533803
theorem B1433051 : Blo 279826 1433051 := bstep (se 1 (by rfl) ⟨1074788, by rfl⟩ : syracuseStep 1433051 = 2149577) B2149577
theorem B319099 : Blo 279826 319099 := bstep (se 1 (by rfl) ⟨239324, by rfl⟩ : syracuseStep 319099 = 478649) B478649
theorem B1924823 : Blo 279826 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B614137 : Blo 279826 614137 := bstep (se 2 (by rfl) ⟨230301, by rfl⟩ : syracuseStep 614137 = 460603) B460603
theorem B1433537 : Blo 279826 1433537 := bstep (se 2 (by rfl) ⟨537576, by rfl⟩ : syracuseStep 1433537 = 1075153) B1075153
theorem B1073209 : Blo 279826 1073209 := bstep (se 2 (by rfl) ⟨402453, by rfl⟩ : syracuseStep 1073209 = 804907) B804907
theorem B4645181 : Blo 279826 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B1073513 : Blo 279826 1073513 := bstep (se 2 (by rfl) ⟨402567, by rfl⟩ : syracuseStep 1073513 = 805135) B805135
theorem B713225 : Blo 279826 713225 := bstep (se 2 (by rfl) ⟨267459, by rfl⟩ : syracuseStep 713225 = 534919) B534919
theorem B1106567 : Blo 279826 1106567 := bstep (se 1 (by rfl) ⟨829925, by rfl⟩ : syracuseStep 1106567 = 1659851) B1659851
theorem B3629873 : Blo 279826 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B1205705 : Blo 279826 1205705 := bstep (se 2 (by rfl) ⟨452139, by rfl⟩ : syracuseStep 1205705 = 904279) B904279
theorem B1205857 : Blo 279826 1205857 := bstep (se 2 (by rfl) ⟨452196, by rfl⟩ : syracuseStep 1205857 = 904393) B904393
theorem B15492707 : Blo 279826 15492707 := bstep (se 1 (by rfl) ⟨11619530, by rfl⟩ : syracuseStep 15492707 = 23239061) B23239061
theorem B779915 : Blo 279826 779915 := bstep (se 1 (by rfl) ⟨584936, by rfl⟩ : syracuseStep 779915 = 1169873) B1169873
theorem B714379 : Blo 279826 714379 := bstep (se 1 (by rfl) ⟨535784, by rfl⟩ : syracuseStep 714379 = 1071569) B1071569
theorem B2713337 : Blo 279826 2713337 := bstep (se 2 (by rfl) ⟨1017501, by rfl⟩ : syracuseStep 2713337 = 2035003) B2035003
theorem B3860261 : Blo 279826 3860261 := bstep (se 4 (by rfl) ⟨361899, by rfl⟩ : syracuseStep 3860261 = 723799) B723799
theorem B419759 : Blo 279826 419759 := bstep (se 1 (by rfl) ⟨314819, by rfl⟩ : syracuseStep 419759 = 629639) B629639
theorem B354223 : Blo 279826 354223 := bstep (se 1 (by rfl) ⟨265667, by rfl⟩ : syracuseStep 354223 = 531335) B531335
theorem B714683 : Blo 279826 714683 := bstep (se 1 (by rfl) ⟨536012, by rfl⟩ : syracuseStep 714683 = 1072025) B1072025
theorem B419849 : Blo 279826 419849 := bstep (se 2 (by rfl) ⟨157443, by rfl⟩ : syracuseStep 419849 = 314887) B314887
theorem B419879 : Blo 279826 419879 := bstep (se 1 (by rfl) ⟨314909, by rfl⟩ : syracuseStep 419879 = 629819) B629819
theorem B419963 : Blo 279826 419963 := bstep (se 1 (by rfl) ⟨314972, by rfl⟩ : syracuseStep 419963 = 629945) B629945
theorem B1435805 : Blo 279826 1435805 := bstep (se 3 (by rfl) ⟨269213, by rfl⟩ : syracuseStep 1435805 = 538427) B538427
theorem B420089 : Blo 279826 420089 := bstep (se 2 (by rfl) ⟨157533, by rfl⟩ : syracuseStep 420089 = 315067) B315067
theorem B1534295 : Blo 279826 1534295 := bstep (se 1 (by rfl) ⟨1150721, by rfl⟩ : syracuseStep 1534295 = 2301443) B2301443
theorem B420191 : Blo 279826 420191 := bstep (se 1 (by rfl) ⟨315143, by rfl⟩ : syracuseStep 420191 = 630287) B630287
theorem B420203 : Blo 279826 420203 := bstep (se 1 (by rfl) ⟨315152, by rfl⟩ : syracuseStep 420203 = 630305) B630305
theorem B944513 : Blo 279826 944513 := bstep (se 2 (by rfl) ⟨354192, by rfl⟩ : syracuseStep 944513 = 708385) B708385
theorem B3631513 : Blo 279826 3631513 := bstep (se 2 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 3631513 = 2723635) B2723635
theorem B420431 : Blo 279826 420431 := bstep (se 1 (by rfl) ⟨315323, by rfl⟩ : syracuseStep 420431 = 630647) B630647
theorem B4811399 : Blo 279826 4811399 := bstep (se 1 (by rfl) ⟨3608549, by rfl⟩ : syracuseStep 4811399 = 7217099) B7217099
theorem B420551 : Blo 279826 420551 := bstep (se 1 (by rfl) ⟨315413, by rfl⟩ : syracuseStep 420551 = 630827) B630827
theorem B715463 : Blo 279826 715463 := bstep (se 1 (by rfl) ⟨536597, by rfl⟩ : syracuseStep 715463 = 1073195) B1073195
theorem B715513 : Blo 279826 715513 := bstep (se 2 (by rfl) ⟨268317, by rfl⟩ : syracuseStep 715513 = 536635) B536635
theorem B420713 : Blo 279826 420713 := bstep (se 2 (by rfl) ⟨157767, by rfl⟩ : syracuseStep 420713 = 315535) B315535
theorem B420791 : Blo 279826 420791 := bstep (se 1 (by rfl) ⟨315593, by rfl⟩ : syracuseStep 420791 = 631187) B631187
theorem B420827 : Blo 279826 420827 := bstep (se 1 (by rfl) ⟨315620, by rfl⟩ : syracuseStep 420827 = 631241) B631241
theorem B355367 : Blo 279826 355367 := bstep (se 1 (by rfl) ⟨266525, by rfl⟩ : syracuseStep 355367 = 533051) B533051
theorem B945323 : Blo 279826 945323 := bstep (se 1 (by rfl) ⟨708992, by rfl⟩ : syracuseStep 945323 = 1417985) B1417985
theorem B355691 : Blo 279826 355691 := bstep (se 1 (by rfl) ⟨266768, by rfl⟩ : syracuseStep 355691 = 533537) B533537
theorem B716161 : Blo 279826 716161 := bstep (se 2 (by rfl) ⟨268560, by rfl⟩ : syracuseStep 716161 = 537121) B537121
theorem B2289059 : Blo 279826 2289059 := bstep (se 1 (by rfl) ⟨1716794, by rfl⟩ : syracuseStep 2289059 = 3433589) B3433589
theorem B421295 : Blo 279826 421295 := bstep (se 1 (by rfl) ⟨315971, by rfl⟩ : syracuseStep 421295 = 631943) B631943
theorem B3436019 : Blo 279826 3436019 := bstep (se 1 (by rfl) ⟨2577014, by rfl⟩ : syracuseStep 3436019 = 5154029) B5154029
theorem B421385 : Blo 279826 421385 := bstep (se 2 (by rfl) ⟨158019, by rfl⟩ : syracuseStep 421385 = 316039) B316039
theorem B421415 : Blo 279826 421415 := bstep (se 1 (by rfl) ⟨316061, by rfl⟩ : syracuseStep 421415 = 632123) B632123
theorem B421499 : Blo 279826 421499 := bstep (se 1 (by rfl) ⟨316124, by rfl⟩ : syracuseStep 421499 = 632249) B632249
theorem B945863 : Blo 279826 945863 := bstep (se 1 (by rfl) ⟨709397, by rfl⟩ : syracuseStep 945863 = 1418795) B1418795
theorem B683731 : Blo 279826 683731 := bstep (se 1 (by rfl) ⟨512798, by rfl⟩ : syracuseStep 683731 = 1025597) B1025597
theorem B7728857 : Blo 279826 7728857 := bstep (se 2 (by rfl) ⟨2898321, by rfl⟩ : syracuseStep 7728857 = 5796643) B5796643
theorem B421625 : Blo 279826 421625 := bstep (se 2 (by rfl) ⟨158109, by rfl⟩ : syracuseStep 421625 = 316219) B316219
theorem B421727 : Blo 279826 421727 := bstep (se 1 (by rfl) ⟨316295, by rfl⟩ : syracuseStep 421727 = 632591) B632591
theorem B421739 : Blo 279826 421739 := bstep (se 1 (by rfl) ⟨316304, by rfl⟩ : syracuseStep 421739 = 632609) B632609
theorem B17592227 : Blo 279826 17592227 := bstep (se 1 (by rfl) ⟨13194170, by rfl⟩ : syracuseStep 17592227 = 26388341) B26388341
theorem B683959 : Blo 279826 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B454619 : Blo 279826 454619 := bstep (se 1 (by rfl) ⟨340964, by rfl⟩ : syracuseStep 454619 = 681929) B681929
theorem B3403853 : Blo 279826 3403853 := bstep (se 3 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 3403853 = 1276445) B1276445
theorem B421967 : Blo 279826 421967 := bstep (se 1 (by rfl) ⟨316475, by rfl⟩ : syracuseStep 421967 = 632951) B632951
theorem B1077401 : Blo 279826 1077401 := bstep (se 2 (by rfl) ⟨404025, by rfl⟩ : syracuseStep 1077401 = 808051) B808051
theorem B716971 : Blo 279826 716971 := bstep (se 1 (by rfl) ⟨537728, by rfl⟩ : syracuseStep 716971 = 1075457) B1075457
theorem B422087 : Blo 279826 422087 := bstep (se 1 (by rfl) ⟨316565, by rfl⟩ : syracuseStep 422087 = 633131) B633131
theorem B553159 : Blo 279826 553159 := bstep (se 1 (by rfl) ⟨414869, by rfl⟩ : syracuseStep 553159 = 829739) B829739
theorem B422249 : Blo 279826 422249 := bstep (se 2 (by rfl) ⟨158343, by rfl⟩ : syracuseStep 422249 = 316687) B316687
theorem B422327 : Blo 279826 422327 := bstep (se 1 (by rfl) ⟨316745, by rfl⟩ : syracuseStep 422327 = 633491) B633491
theorem B422363 : Blo 279826 422363 := bstep (se 1 (by rfl) ⟨316772, by rfl⟩ : syracuseStep 422363 = 633545) B633545
theorem B717275 : Blo 279826 717275 := bstep (se 1 (by rfl) ⟨537956, by rfl⟩ : syracuseStep 717275 = 1075913) B1075913
theorem B946727 : Blo 279826 946727 := bstep (se 1 (by rfl) ⟨710045, by rfl⟩ : syracuseStep 946727 = 1420091) B1420091
theorem B356987 : Blo 279826 356987 := bstep (se 1 (by rfl) ⟨267740, by rfl⟩ : syracuseStep 356987 = 535481) B535481
theorem B946835 : Blo 279826 946835 := bstep (se 1 (by rfl) ⟨710126, by rfl⟩ : syracuseStep 946835 = 1420253) B1420253
theorem B3601169 : Blo 279826 3601169 := bstep (se 2 (by rfl) ⟨1350438, by rfl⟩ : syracuseStep 3601169 = 2700877) B2700877
theorem B947051 : Blo 279826 947051 := bstep (se 1 (by rfl) ⟨710288, by rfl⟩ : syracuseStep 947051 = 1420577) B1420577
theorem B947105 : Blo 279826 947105 := bstep (se 2 (by rfl) ⟨355164, by rfl⟩ : syracuseStep 947105 = 710329) B710329
theorem B422831 : Blo 279826 422831 := bstep (se 1 (by rfl) ⟨317123, by rfl⟩ : syracuseStep 422831 = 634247) B634247
theorem B422921 : Blo 279826 422921 := bstep (se 2 (by rfl) ⟨158595, by rfl⟩ : syracuseStep 422921 = 317191) B317191
theorem B422951 : Blo 279826 422951 := bstep (se 1 (by rfl) ⟨317213, by rfl⟩ : syracuseStep 422951 = 634427) B634427
theorem B423035 : Blo 279826 423035 := bstep (se 1 (by rfl) ⟨317276, by rfl⟩ : syracuseStep 423035 = 634553) B634553
theorem B423161 : Blo 279826 423161 := bstep (se 2 (by rfl) ⟨158685, by rfl⟩ : syracuseStep 423161 = 317371) B317371
theorem B1013003 : Blo 279826 1013003 := bstep (se 1 (by rfl) ⟨759752, by rfl⟩ : syracuseStep 1013003 = 1519505) B1519505
theorem B423263 : Blo 279826 423263 := bstep (se 1 (by rfl) ⟨317447, by rfl⟩ : syracuseStep 423263 = 634895) B634895
theorem B423275 : Blo 279826 423275 := bstep (se 1 (by rfl) ⟨317456, by rfl⟩ : syracuseStep 423275 = 634913) B634913
theorem B816527 : Blo 279826 816527 := bstep (se 1 (by rfl) ⟨612395, by rfl⟩ : syracuseStep 816527 = 1224791) B1224791
theorem B4879763 : Blo 279826 4879763 := bstep (se 1 (by rfl) ⟨3659822, by rfl⟩ : syracuseStep 4879763 = 7319645) B7319645
theorem B947699 : Blo 279826 947699 := bstep (se 1 (by rfl) ⟨710774, by rfl⟩ : syracuseStep 947699 = 1421549) B1421549
theorem B423503 : Blo 279826 423503 := bstep (se 1 (by rfl) ⟨317627, by rfl⟩ : syracuseStep 423503 = 635255) B635255
theorem B1799819 : Blo 279826 1799819 := bstep (se 1 (by rfl) ⟨1349864, by rfl⟩ : syracuseStep 1799819 = 2699729) B2699729
theorem B423623 : Blo 279826 423623 := bstep (se 1 (by rfl) ⟨317717, by rfl⟩ : syracuseStep 423623 = 635435) B635435
theorem B423785 : Blo 279826 423785 := bstep (se 2 (by rfl) ⟨158919, by rfl⟩ : syracuseStep 423785 = 317839) B317839
theorem B1210231 : Blo 279826 1210231 := bstep (se 1 (by rfl) ⟨907673, by rfl⟩ : syracuseStep 1210231 = 1815347) B1815347
theorem B423863 : Blo 279826 423863 := bstep (se 1 (by rfl) ⟨317897, by rfl⟩ : syracuseStep 423863 = 635795) B635795
theorem B423899 : Blo 279826 423899 := bstep (se 1 (by rfl) ⟨317924, by rfl⟩ : syracuseStep 423899 = 635849) B635849
theorem B948239 : Blo 279826 948239 := bstep (se 1 (by rfl) ⟨711179, by rfl⟩ : syracuseStep 948239 = 1422359) B1422359
theorem B424367 : Blo 279826 424367 := bstep (se 1 (by rfl) ⟨318275, by rfl⟩ : syracuseStep 424367 = 636551) B636551
theorem B424457 : Blo 279826 424457 := bstep (se 2 (by rfl) ⟨159171, by rfl⟩ : syracuseStep 424457 = 318343) B318343
theorem B424487 : Blo 279826 424487 := bstep (se 1 (by rfl) ⟨318365, by rfl⟩ : syracuseStep 424487 = 636731) B636731
theorem B948833 : Blo 279826 948833 := bstep (se 2 (by rfl) ⟨355812, by rfl⟩ : syracuseStep 948833 = 711625) B711625
theorem B424571 : Blo 279826 424571 := bstep (se 1 (by rfl) ⟨318428, by rfl⟩ : syracuseStep 424571 = 636857) B636857
theorem B817879 : Blo 279826 817879 := bstep (se 1 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 817879 = 1226819) B1226819
theorem B424697 : Blo 279826 424697 := bstep (se 2 (by rfl) ⟨159261, by rfl⟩ : syracuseStep 424697 = 318523) B318523
theorem B424799 : Blo 279826 424799 := bstep (se 1 (by rfl) ⟨318599, by rfl⟩ : syracuseStep 424799 = 637199) B637199
theorem B424811 : Blo 279826 424811 := bstep (se 1 (by rfl) ⟨318608, by rfl⟩ : syracuseStep 424811 = 637217) B637217
theorem B19037105 : Blo 279826 19037105 := bstep (se 2 (by rfl) ⟨7138914, by rfl⟩ : syracuseStep 19037105 = 14277829) B14277829
theorem B719891 : Blo 279826 719891 := bstep (se 1 (by rfl) ⟨539918, by rfl⟩ : syracuseStep 719891 = 1079837) B1079837
theorem B425039 : Blo 279826 425039 := bstep (se 1 (by rfl) ⟨318779, by rfl⟩ : syracuseStep 425039 = 637559) B637559
theorem B3603629 : Blo 279826 3603629 := bstep (se 3 (by rfl) ⟨675680, by rfl⟩ : syracuseStep 3603629 = 1351361) B1351361
theorem B425159 : Blo 279826 425159 := bstep (se 1 (by rfl) ⟨318869, by rfl⟩ : syracuseStep 425159 = 637739) B637739
theorem B425321 : Blo 279826 425321 := bstep (se 2 (by rfl) ⟨159495, by rfl⟩ : syracuseStep 425321 = 318991) B318991
theorem B425399 : Blo 279826 425399 := bstep (se 1 (by rfl) ⟨319049, by rfl⟩ : syracuseStep 425399 = 638099) B638099
theorem B425435 : Blo 279826 425435 := bstep (se 1 (by rfl) ⟨319076, by rfl⟩ : syracuseStep 425435 = 638153) B638153
theorem B1212043 : Blo 279826 1212043 := bstep (se 1 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 1212043 = 1818065) B1818065
theorem B1605419 : Blo 279826 1605419 := bstep (se 1 (by rfl) ⟨1204064, by rfl⟩ : syracuseStep 1605419 = 2408129) B2408129
theorem B1704089 : Blo 279826 1704089 := bstep (se 2 (by rfl) ⟨639033, by rfl⟩ : syracuseStep 1704089 = 1278067) B1278067
theorem B4849901 : Blo 279826 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B820187 : Blo 279826 820187 := bstep (se 1 (by rfl) ⟨615140, by rfl⟩ : syracuseStep 820187 = 1230281) B1230281
theorem B4785155 : Blo 279826 4785155 := bstep (se 1 (by rfl) ⟨3588866, by rfl⟩ : syracuseStep 4785155 = 7177733) B7177733
theorem B2950181 : Blo 279826 2950181 := bstep (se 4 (by rfl) ⟨276579, by rfl⟩ : syracuseStep 2950181 = 553159) B553159
theorem B1082747 : Blo 279826 1082747 := bstep (se 1 (by rfl) ⟨812060, by rfl⟩ : syracuseStep 1082747 = 1624121) B1624121
theorem B853409 : Blo 279826 853409 := bstep (se 2 (by rfl) ⟨320028, by rfl⟩ : syracuseStep 853409 = 640057) B640057
theorem B1803865 : Blo 279826 1803865 := bstep (se 2 (by rfl) ⟨676449, by rfl⟩ : syracuseStep 1803865 = 1352899) B1352899
theorem B11044471 : Blo 279826 11044471 := bstep (se 1 (by rfl) ⟨8283353, by rfl⟩ : syracuseStep 11044471 = 16566707) B16566707
theorem B20514455 : Blo 279826 20514455 := bstep (se 1 (by rfl) ⟨15385841, by rfl⟩ : syracuseStep 20514455 = 30771683) B30771683
theorem B951965 : Blo 279826 951965 := bstep (se 3 (by rfl) ⟨178493, by rfl⟩ : syracuseStep 951965 = 356987) B356987
theorem B1345211 : Blo 279826 1345211 := bstep (se 1 (by rfl) ⟨1008908, by rfl⟩ : syracuseStep 1345211 = 2017817) B2017817
theorem B1476407 : Blo 279826 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B3606605 : Blo 279826 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B1607809 : Blo 279826 1607809 := bstep (se 2 (by rfl) ⟨602928, by rfl⟩ : syracuseStep 1607809 = 1205857) B1205857
theorem B2033849 : Blo 279826 2033849 := bstep (se 2 (by rfl) ⟨762693, by rfl⟩ : syracuseStep 2033849 = 1525387) B1525387
theorem B952505 : Blo 279826 952505 := bstep (se 2 (by rfl) ⟨357189, by rfl⟩ : syracuseStep 952505 = 714379) B714379
theorem B1804481 : Blo 279826 1804481 := bstep (se 2 (by rfl) ⟨676680, by rfl⟩ : syracuseStep 1804481 = 1353361) B1353361
theorem B723451 : Blo 279826 723451 := bstep (se 1 (by rfl) ⟨542588, by rfl⟩ : syracuseStep 723451 = 1085177) B1085177
theorem B1182203 : Blo 279826 1182203 := bstep (se 1 (by rfl) ⟨886652, by rfl⟩ : syracuseStep 1182203 = 1773305) B1773305
theorem B2132567 : Blo 279826 2132567 := bstep (se 1 (by rfl) ⟨1599425, by rfl⟩ : syracuseStep 2132567 = 3198851) B3198851
theorem B1346327 : Blo 279826 1346327 := bstep (se 1 (by rfl) ⟨1009745, by rfl⟩ : syracuseStep 1346327 = 2019491) B2019491
theorem B5442349 : Blo 279826 5442349 := bstep (se 3 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 5442349 = 2040881) B2040881
theorem B4820147 : Blo 279826 4820147 := bstep (se 1 (by rfl) ⟨3615110, by rfl⟩ : syracuseStep 4820147 = 7230221) B7230221
theorem B756985 : Blo 279826 756985 := bstep (se 2 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 756985 = 567739) B567739
theorem B1346827 : Blo 279826 1346827 := bstep (se 1 (by rfl) ⟨1010120, by rfl⟩ : syracuseStep 1346827 = 2020241) B2020241
theorem B2985461 : Blo 279826 2985461 := bstep (se 5 (by rfl) ⟨139943, by rfl⟩ : syracuseStep 2985461 = 279887) B279887
theorem B954017 : Blo 279826 954017 := bstep (se 2 (by rfl) ⟨357756, by rfl⟩ : syracuseStep 954017 = 715513) B715513
theorem B3149725 : Blo 279826 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B2363755 : Blo 279826 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B954881 : Blo 279826 954881 := bstep (se 2 (by rfl) ⟨358080, by rfl⟩ : syracuseStep 954881 = 716161) B716161
theorem B9573137 : Blo 279826 9573137 := bstep (se 2 (by rfl) ⟨3589926, by rfl⟩ : syracuseStep 9573137 = 7179853) B7179853
theorem B2724637 : Blo 279826 2724637 := bstep (se 3 (by rfl) ⟨510869, by rfl⟩ : syracuseStep 2724637 = 1021739) B1021739
theorem B955367 : Blo 279826 955367 := bstep (se 1 (by rfl) ⟨716525, by rfl⟩ : syracuseStep 955367 = 1433051) B1433051
theorem B1283215 : Blo 279826 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B955691 : Blo 279826 955691 := bstep (se 1 (by rfl) ⟨716768, by rfl⟩ : syracuseStep 955691 = 1433537) B1433537
theorem B398729 : Blo 279826 398729 := bstep (se 2 (by rfl) ⟨149523, by rfl⟩ : syracuseStep 398729 = 299047) B299047
theorem B955961 : Blo 279826 955961 := bstep (se 2 (by rfl) ⟨358485, by rfl⟩ : syracuseStep 955961 = 716971) B716971
theorem B759709 : Blo 279826 759709 := bstep (se 3 (by rfl) ⟨142445, by rfl⟩ : syracuseStep 759709 = 284891) B284891
theorem B10328471 : Blo 279826 10328471 := bstep (se 1 (by rfl) ⟨7746353, by rfl⟩ : syracuseStep 10328471 = 15492707) B15492707
theorem B1808891 : Blo 279826 1808891 := bstep (se 1 (by rfl) ⟨1356668, by rfl⟩ : syracuseStep 1808891 = 2713337) B2713337
theorem B2038405 : Blo 279826 2038405 := bstep (se 4 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 2038405 = 382201) B382201
theorem B957203 : Blo 279826 957203 := bstep (se 1 (by rfl) ⟨717902, by rfl⟩ : syracuseStep 957203 = 1435805) B1435805
theorem B1022863 : Blo 279826 1022863 := bstep (se 1 (by rfl) ⟨767147, by rfl⟩ : syracuseStep 1022863 = 1534295) B1534295
theorem B629675 : Blo 279826 629675 := bstep (se 1 (by rfl) ⟨472256, by rfl⟩ : syracuseStep 629675 = 944513) B944513
theorem B2891173 : Blo 279826 2891173 := bstep (se 4 (by rfl) ⟨271047, by rfl⟩ : syracuseStep 2891173 = 542095) B542095
theorem B630215 : Blo 279826 630215 := bstep (se 1 (by rfl) ⟨472661, by rfl⟩ : syracuseStep 630215 = 945323) B945323
theorem B630575 : Blo 279826 630575 := bstep (se 1 (by rfl) ⟨472931, by rfl⟩ : syracuseStep 630575 = 945863) B945863
theorem B1515311 : Blo 279826 1515311 := bstep (se 1 (by rfl) ⟨1136483, by rfl⟩ : syracuseStep 1515311 = 2272967) B2272967
theorem B5152571 : Blo 279826 5152571 := bstep (se 1 (by rfl) ⟨3864428, by rfl⟩ : syracuseStep 5152571 = 7728857) B7728857
theorem B1613641 : Blo 279826 1613641 := bstep (se 2 (by rfl) ⟨605115, by rfl⟩ : syracuseStep 1613641 = 1210231) B1210231
theorem B2269235 : Blo 279826 2269235 := bstep (se 1 (by rfl) ⟨1701926, by rfl⟩ : syracuseStep 2269235 = 3403853) B3403853
theorem B2433235 : Blo 279826 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B631151 : Blo 279826 631151 := bstep (se 1 (by rfl) ⟨473363, by rfl⟩ : syracuseStep 631151 = 946727) B946727
theorem B1515941 : Blo 279826 1515941 := bstep (se 4 (by rfl) ⟨142119, by rfl⟩ : syracuseStep 1515941 = 284239) B284239
theorem B631223 : Blo 279826 631223 := bstep (se 1 (by rfl) ⟨473417, by rfl⟩ : syracuseStep 631223 = 946835) B946835
theorem B1516001 : Blo 279826 1516001 := bstep (se 2 (by rfl) ⟨568500, by rfl⟩ : syracuseStep 1516001 = 1137001) B1137001
theorem B2400779 : Blo 279826 2400779 := bstep (se 1 (by rfl) ⟨1800584, by rfl⟩ : syracuseStep 2400779 = 3601169) B3601169
theorem B631367 : Blo 279826 631367 := bstep (se 1 (by rfl) ⟨473525, by rfl⟩ : syracuseStep 631367 = 947051) B947051
theorem B631403 : Blo 279826 631403 := bstep (se 1 (by rfl) ⟨473552, by rfl⟩ : syracuseStep 631403 = 947105) B947105
theorem B3253175 : Blo 279826 3253175 := bstep (se 1 (by rfl) ⟨2439881, by rfl⟩ : syracuseStep 3253175 = 4879763) B4879763
theorem B1090505 : Blo 279826 1090505 := bstep (se 2 (by rfl) ⟨408939, by rfl⟩ : syracuseStep 1090505 = 817879) B817879
theorem B631799 : Blo 279826 631799 := bstep (se 1 (by rfl) ⟨473849, by rfl⟩ : syracuseStep 631799 = 947699) B947699
theorem B3646565 : Blo 279826 3646565 := bstep (se 4 (by rfl) ⟨341865, by rfl⟩ : syracuseStep 3646565 = 683731) B683731
theorem B402727 : Blo 279826 402727 := bstep (se 1 (by rfl) ⟨302045, by rfl⟩ : syracuseStep 402727 = 604091) B604091
theorem B632159 : Blo 279826 632159 := bstep (se 1 (by rfl) ⟨474119, by rfl⟩ : syracuseStep 632159 = 948239) B948239
theorem B599393 : Blo 279826 599393 := bstep (se 2 (by rfl) ⟨224772, by rfl⟩ : syracuseStep 599393 = 449545) B449545
theorem B337351 : Blo 279826 337351 := bstep (se 1 (by rfl) ⟨253013, by rfl⟩ : syracuseStep 337351 = 506027) B506027
theorem B632555 : Blo 279826 632555 := bstep (se 1 (by rfl) ⟨474416, by rfl⟩ : syracuseStep 632555 = 948833) B948833
theorem B534251 : Blo 279826 534251 := bstep (se 1 (by rfl) ⟨400688, by rfl⟩ : syracuseStep 534251 = 801377) B801377
theorem B632681 : Blo 279826 632681 := bstep (se 2 (by rfl) ⟨237255, by rfl⟩ : syracuseStep 632681 = 474511) B474511
theorem B12691403 : Blo 279826 12691403 := bstep (se 1 (by rfl) ⟨9518552, by rfl⟩ : syracuseStep 12691403 = 19037105) B19037105
theorem B2402419 : Blo 279826 2402419 := bstep (se 1 (by rfl) ⟨1801814, by rfl⟩ : syracuseStep 2402419 = 3603629) B3603629
theorem B1616057 : Blo 279826 1616057 := bstep (se 2 (by rfl) ⟨606021, by rfl⟩ : syracuseStep 1616057 = 1212043) B1212043
theorem B37234997 : Blo 279826 37234997 := bstep (se 5 (by rfl) ⟨1745390, by rfl⟩ : syracuseStep 37234997 = 3490781) B3490781
theorem B534995 : Blo 279826 534995 := bstep (se 1 (by rfl) ⟨401246, by rfl⟩ : syracuseStep 534995 = 802493) B802493
theorem B600571 : Blo 279826 600571 := bstep (se 1 (by rfl) ⟨450428, by rfl⟩ : syracuseStep 600571 = 900857) B900857
theorem B633527 : Blo 279826 633527 := bstep (se 1 (by rfl) ⟨475145, by rfl⟩ : syracuseStep 633527 = 950291) B950291
theorem B535223 : Blo 279826 535223 := bstep (se 1 (by rfl) ⟨401417, by rfl⟩ : syracuseStep 535223 = 802835) B802835
theorem B2566903 : Blo 279826 2566903 := bstep (se 1 (by rfl) ⟨1925177, by rfl⟩ : syracuseStep 2566903 = 3850355) B3850355
theorem B633743 : Blo 279826 633743 := bstep (se 1 (by rfl) ⟨475307, by rfl⟩ : syracuseStep 633743 = 950615) B950615
theorem B568615 : Blo 279826 568615 := bstep (se 1 (by rfl) ⟨426461, by rfl⟩ : syracuseStep 568615 = 852923) B852923
theorem B10136951 : Blo 279826 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B634463 : Blo 279826 634463 := bstep (se 1 (by rfl) ⟨475847, by rfl⟩ : syracuseStep 634463 = 951695) B951695
theorem B601835 : Blo 279826 601835 := bstep (se 1 (by rfl) ⟨451376, by rfl⟩ : syracuseStep 601835 = 902753) B902753
theorem B1421063 : Blo 279826 1421063 := bstep (se 1 (by rfl) ⟨1065797, by rfl⟩ : syracuseStep 1421063 = 2131595) B2131595
theorem B634679 : Blo 279826 634679 := bstep (se 1 (by rfl) ⟨476009, by rfl⟩ : syracuseStep 634679 = 952019) B952019
theorem B536377 : Blo 279826 536377 := bstep (se 2 (by rfl) ⟨201141, by rfl⟩ : syracuseStep 536377 = 402283) B402283
theorem B634985 : Blo 279826 634985 := bstep (se 2 (by rfl) ⟨238119, by rfl⟩ : syracuseStep 634985 = 476239) B476239
theorem B536681 : Blo 279826 536681 := bstep (se 2 (by rfl) ⟨201255, by rfl⟩ : syracuseStep 536681 = 402511) B402511
theorem B602579 : Blo 279826 602579 := bstep (se 1 (by rfl) ⟨451934, by rfl⟩ : syracuseStep 602579 = 903869) B903869
theorem B799303 : Blo 279826 799303 := bstep (se 1 (by rfl) ⟨599477, by rfl⟩ : syracuseStep 799303 = 1198955) B1198955
theorem B635471 : Blo 279826 635471 := bstep (se 1 (by rfl) ⟨476603, by rfl⟩ : syracuseStep 635471 = 953207) B953207
theorem B635615 : Blo 279826 635615 := bstep (se 1 (by rfl) ⟨476711, by rfl⟩ : syracuseStep 635615 = 953423) B953423
theorem B2896669 : Blo 279826 2896669 := bstep (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) B1086251
theorem B635867 : Blo 279826 635867 := bstep (se 1 (by rfl) ⟨476900, by rfl⟩ : syracuseStep 635867 = 953801) B953801
theorem B570359 : Blo 279826 570359 := bstep (se 1 (by rfl) ⟨427769, by rfl⟩ : syracuseStep 570359 = 855539) B855539
theorem B636047 : Blo 279826 636047 := bstep (se 1 (by rfl) ⟨477035, by rfl⟩ : syracuseStep 636047 = 954071) B954071
theorem B4076689 : Blo 279826 4076689 := bstep (se 2 (by rfl) ⟨1528758, by rfl⟩ : syracuseStep 4076689 = 3057517) B3057517
theorem B472297 : Blo 279826 472297 := bstep (se 2 (by rfl) ⟨177111, by rfl⟩ : syracuseStep 472297 = 354223) B354223
theorem B636137 : Blo 279826 636137 := bstep (se 2 (by rfl) ⟨238551, by rfl⟩ : syracuseStep 636137 = 477103) B477103
theorem B472351 : Blo 279826 472351 := bstep (se 1 (by rfl) ⟨354263, by rfl⟩ : syracuseStep 472351 = 708527) B708527
theorem B636191 : Blo 279826 636191 := bstep (se 1 (by rfl) ⟨477143, by rfl⟩ : syracuseStep 636191 = 954287) B954287
theorem B472763 : Blo 279826 472763 := bstep (se 1 (by rfl) ⟨354572, by rfl⟩ : syracuseStep 472763 = 709145) B709145
theorem B636713 : Blo 279826 636713 := bstep (se 2 (by rfl) ⟨238767, by rfl⟩ : syracuseStep 636713 = 477535) B477535
theorem B4569149 : Blo 279826 4569149 := bstep (se 3 (by rfl) ⟨856715, by rfl⟩ : syracuseStep 4569149 = 1713431) B1713431
theorem B1128701 : Blo 279826 1128701 := bstep (se 3 (by rfl) ⟨211631, by rfl⟩ : syracuseStep 1128701 = 423263) B423263
theorem B5421437 : Blo 279826 5421437 := bstep (se 3 (by rfl) ⟨1016519, by rfl⟩ : syracuseStep 5421437 = 2033039) B2033039
theorem B2177405 : Blo 279826 2177405 := bstep (se 3 (by rfl) ⟨408263, by rfl⟩ : syracuseStep 2177405 = 816527) B816527
theorem B801353 : Blo 279826 801353 := bstep (se 2 (by rfl) ⟨300507, by rfl⟩ : syracuseStep 801353 = 601015) B601015
theorem B1423979 : Blo 279826 1423979 := bstep (se 1 (by rfl) ⟨1067984, by rfl⟩ : syracuseStep 1423979 = 2135969) B2135969
theorem B637775 : Blo 279826 637775 := bstep (se 1 (by rfl) ⟨478331, by rfl⟩ : syracuseStep 637775 = 956663) B956663
theorem B900011 : Blo 279826 900011 := bstep (se 1 (by rfl) ⟨675008, by rfl⟩ : syracuseStep 900011 = 1350017) B1350017
theorem B1063975 : Blo 279826 1063975 := bstep (se 1 (by rfl) ⟨797981, by rfl⟩ : syracuseStep 1063975 = 1595963) B1595963
theorem B637991 : Blo 279826 637991 := bstep (se 1 (by rfl) ⟨478493, by rfl⟩ : syracuseStep 637991 = 956987) B956987
theorem B2505779 : Blo 279826 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B1424465 : Blo 279826 1424465 := bstep (se 2 (by rfl) ⟨534174, by rfl⟩ : syracuseStep 1424465 = 1068349) B1068349
theorem B638171 : Blo 279826 638171 := bstep (se 1 (by rfl) ⟨478628, by rfl⟩ : syracuseStep 638171 = 957257) B957257
theorem B474491 : Blo 279826 474491 := bstep (se 1 (by rfl) ⟨355868, by rfl⟩ : syracuseStep 474491 = 711737) B711737
theorem B638369 : Blo 279826 638369 := bstep (se 2 (by rfl) ⟨239388, by rfl⟩ : syracuseStep 638369 = 478777) B478777
theorem B507655 : Blo 279826 507655 := bstep (se 1 (by rfl) ⟨380741, by rfl⟩ : syracuseStep 507655 = 761483) B761483
theorem B1064765 : Blo 279826 1064765 := bstep (se 3 (by rfl) ⟨199643, by rfl⟩ : syracuseStep 1064765 = 399287) B399287
theorem B3096787 : Blo 279826 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B475483 : Blo 279826 475483 := bstep (se 1 (by rfl) ⟨356612, by rfl⟩ : syracuseStep 475483 = 713225) B713225
theorem B737711 : Blo 279826 737711 := bstep (se 1 (by rfl) ⟨553283, by rfl⟩ : syracuseStep 737711 = 1106567) B1106567
theorem B1360435 : Blo 279826 1360435 := bstep (se 1 (by rfl) ⟨1020326, by rfl⟩ : syracuseStep 1360435 = 2040653) B2040653
theorem B803449 : Blo 279826 803449 := bstep (se 2 (by rfl) ⟨301293, by rfl⟩ : syracuseStep 803449 = 602587) B602587
theorem B803803 : Blo 279826 803803 := bstep (se 1 (by rfl) ⟨602852, by rfl⟩ : syracuseStep 803803 = 1205705) B1205705
theorem B2573507 : Blo 279826 2573507 := bstep (se 1 (by rfl) ⟨1930130, by rfl⟩ : syracuseStep 2573507 = 3860261) B3860261
theorem B279839 : Blo 279826 279839 := bstep (se 1 (by rfl) ⟨209879, by rfl⟩ : syracuseStep 279839 = 419759) B419759
theorem B476455 : Blo 279826 476455 := bstep (se 1 (by rfl) ⟨357341, by rfl⟩ : syracuseStep 476455 = 714683) B714683
theorem B2147633 : Blo 279826 2147633 := bstep (se 2 (by rfl) ⟨805362, by rfl⟩ : syracuseStep 2147633 = 1610725) B1610725
theorem B279899 : Blo 279826 279899 := bstep (se 1 (by rfl) ⟨209924, by rfl⟩ : syracuseStep 279899 = 419849) B419849
theorem B279919 : Blo 279826 279919 := bstep (se 1 (by rfl) ⟨209939, by rfl⟩ : syracuseStep 279919 = 419879) B419879
theorem B279975 : Blo 279826 279975 := bstep (se 1 (by rfl) ⟨209981, by rfl⟩ : syracuseStep 279975 = 419963) B419963
theorem B280059 : Blo 279826 280059 := bstep (se 1 (by rfl) ⟨210044, by rfl⟩ : syracuseStep 280059 = 420089) B420089
theorem B280127 : Blo 279826 280127 := bstep (se 1 (by rfl) ⟨210095, by rfl⟩ : syracuseStep 280127 = 420191) B420191
theorem B280135 : Blo 279826 280135 := bstep (se 1 (by rfl) ⟨210101, by rfl⟩ : syracuseStep 280135 = 420203) B420203
theorem B280287 : Blo 279826 280287 := bstep (se 1 (by rfl) ⟨210215, by rfl⟩ : syracuseStep 280287 = 420431) B420431
theorem B280367 : Blo 279826 280367 := bstep (se 1 (by rfl) ⟨210275, by rfl⟩ : syracuseStep 280367 = 420551) B420551
theorem B476975 : Blo 279826 476975 := bstep (se 1 (by rfl) ⟨357731, by rfl⟩ : syracuseStep 476975 = 715463) B715463
theorem B1197929 : Blo 279826 1197929 := bstep (se 2 (by rfl) ⟨449223, by rfl⟩ : syracuseStep 1197929 = 898447) B898447
theorem B2606995 : Blo 279826 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B280475 : Blo 279826 280475 := bstep (se 1 (by rfl) ⟨210356, by rfl⟩ : syracuseStep 280475 = 420713) B420713
theorem B280527 : Blo 279826 280527 := bstep (se 1 (by rfl) ⟨210395, by rfl⟩ : syracuseStep 280527 = 420791) B420791
theorem B280551 : Blo 279826 280551 := bstep (se 1 (by rfl) ⟨210413, by rfl⟩ : syracuseStep 280551 = 420827) B420827
theorem B1362167 : Blo 279826 1362167 := bstep (se 1 (by rfl) ⟨1021625, by rfl⟩ : syracuseStep 1362167 = 2043251) B2043251
theorem B2148605 : Blo 279826 2148605 := bstep (se 3 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 2148605 = 805727) B805727
theorem B1526039 : Blo 279826 1526039 := bstep (se 1 (by rfl) ⟨1144529, by rfl⟩ : syracuseStep 1526039 = 2289059) B2289059
theorem B280863 : Blo 279826 280863 := bstep (se 1 (by rfl) ⟨210647, by rfl⟩ : syracuseStep 280863 = 421295) B421295
theorem B280923 : Blo 279826 280923 := bstep (se 1 (by rfl) ⟨210692, by rfl⟩ : syracuseStep 280923 = 421385) B421385
theorem B280943 : Blo 279826 280943 := bstep (se 1 (by rfl) ⟨210707, by rfl⟩ : syracuseStep 280943 = 421415) B421415
theorem B280999 : Blo 279826 280999 := bstep (se 1 (by rfl) ⟨210749, by rfl⟩ : syracuseStep 280999 = 421499) B421499
theorem B281083 : Blo 279826 281083 := bstep (se 1 (by rfl) ⟨210812, by rfl⟩ : syracuseStep 281083 = 421625) B421625
theorem B281151 : Blo 279826 281151 := bstep (se 1 (by rfl) ⟨210863, by rfl⟩ : syracuseStep 281151 = 421727) B421727
theorem B281159 : Blo 279826 281159 := bstep (se 1 (by rfl) ⟨210869, by rfl⟩ : syracuseStep 281159 = 421739) B421739
theorem B281311 : Blo 279826 281311 := bstep (se 1 (by rfl) ⟨210983, by rfl⟩ : syracuseStep 281311 = 421967) B421967
theorem B281391 : Blo 279826 281391 := bstep (se 1 (by rfl) ⟨211043, by rfl⟩ : syracuseStep 281391 = 422087) B422087
theorem B281499 : Blo 279826 281499 := bstep (se 1 (by rfl) ⟨211124, by rfl⟩ : syracuseStep 281499 = 422249) B422249
theorem B281551 : Blo 279826 281551 := bstep (se 1 (by rfl) ⟨211163, by rfl⟩ : syracuseStep 281551 = 422327) B422327
theorem B281575 : Blo 279826 281575 := bstep (se 1 (by rfl) ⟨211181, by rfl⟩ : syracuseStep 281575 = 422363) B422363
theorem B478183 : Blo 279826 478183 := bstep (se 1 (by rfl) ⟨358637, by rfl⟩ : syracuseStep 478183 = 717275) B717275
theorem B281887 : Blo 279826 281887 := bstep (se 1 (by rfl) ⟨211415, by rfl⟩ : syracuseStep 281887 = 422831) B422831
theorem B281947 : Blo 279826 281947 := bstep (se 1 (by rfl) ⟨211460, by rfl⟩ : syracuseStep 281947 = 422921) B422921
theorem B281967 : Blo 279826 281967 := bstep (se 1 (by rfl) ⟨211475, by rfl⟩ : syracuseStep 281967 = 422951) B422951
theorem B282023 : Blo 279826 282023 := bstep (se 1 (by rfl) ⟨211517, by rfl⟩ : syracuseStep 282023 = 423035) B423035
theorem B282107 : Blo 279826 282107 := bstep (se 1 (by rfl) ⟨211580, by rfl⟩ : syracuseStep 282107 = 423161) B423161
theorem B675335 : Blo 279826 675335 := bstep (se 1 (by rfl) ⟨506501, by rfl⟩ : syracuseStep 675335 = 1013003) B1013003
theorem B1429001 : Blo 279826 1429001 := bstep (se 2 (by rfl) ⟨535875, by rfl⟩ : syracuseStep 1429001 = 1071751) B1071751
theorem B282175 : Blo 279826 282175 := bstep (se 1 (by rfl) ⟨211631, by rfl⟩ : syracuseStep 282175 = 423263) B423263
theorem B282183 : Blo 279826 282183 := bstep (se 1 (by rfl) ⟨211637, by rfl⟩ : syracuseStep 282183 = 423275) B423275
theorem B1068653 : Blo 279826 1068653 := bstep (se 3 (by rfl) ⟨200372, by rfl⟩ : syracuseStep 1068653 = 400745) B400745
theorem B315103 : Blo 279826 315103 := bstep (se 1 (by rfl) ⟨236327, by rfl⟩ : syracuseStep 315103 = 472655) B472655
theorem B282335 : Blo 279826 282335 := bstep (se 1 (by rfl) ⟨211751, by rfl⟩ : syracuseStep 282335 = 423503) B423503
theorem B1199879 : Blo 279826 1199879 := bstep (se 1 (by rfl) ⟨899909, by rfl⟩ : syracuseStep 1199879 = 1799819) B1799819
theorem B282415 : Blo 279826 282415 := bstep (se 1 (by rfl) ⟨211811, by rfl⟩ : syracuseStep 282415 = 423623) B423623
theorem B282523 : Blo 279826 282523 := bstep (se 1 (by rfl) ⟨211892, by rfl⟩ : syracuseStep 282523 = 423785) B423785
theorem B282575 : Blo 279826 282575 := bstep (se 1 (by rfl) ⟨211931, by rfl⟩ : syracuseStep 282575 = 423863) B423863
theorem B282599 : Blo 279826 282599 := bstep (se 1 (by rfl) ⟨211949, by rfl⟩ : syracuseStep 282599 = 423899) B423899
theorem B315679 : Blo 279826 315679 := bstep (se 1 (by rfl) ⟨236759, by rfl⟩ : syracuseStep 315679 = 473519) B473519
theorem B282911 : Blo 279826 282911 := bstep (se 1 (by rfl) ⟨212183, by rfl⟩ : syracuseStep 282911 = 424367) B424367
theorem B3035465 : Blo 279826 3035465 := bstep (se 2 (by rfl) ⟨1138299, by rfl⟩ : syracuseStep 3035465 = 2276599) B2276599
theorem B282971 : Blo 279826 282971 := bstep (se 1 (by rfl) ⟨212228, by rfl⟩ : syracuseStep 282971 = 424457) B424457
theorem B282991 : Blo 279826 282991 := bstep (se 1 (by rfl) ⟨212243, by rfl⟩ : syracuseStep 282991 = 424487) B424487
theorem B5427587 : Blo 279826 5427587 := bstep (se 1 (by rfl) ⟨4070690, by rfl⟩ : syracuseStep 5427587 = 8141381) B8141381
theorem B283047 : Blo 279826 283047 := bstep (se 1 (by rfl) ⟨212285, by rfl⟩ : syracuseStep 283047 = 424571) B424571
theorem B283131 : Blo 279826 283131 := bstep (se 1 (by rfl) ⟨212348, by rfl⟩ : syracuseStep 283131 = 424697) B424697
theorem B315967 : Blo 279826 315967 := bstep (se 1 (by rfl) ⟨236975, by rfl⟩ : syracuseStep 315967 = 473951) B473951
theorem B283199 : Blo 279826 283199 := bstep (se 1 (by rfl) ⟨212399, by rfl⟩ : syracuseStep 283199 = 424799) B424799
theorem B283207 : Blo 279826 283207 := bstep (se 1 (by rfl) ⟨212405, by rfl⟩ : syracuseStep 283207 = 424811) B424811
theorem B479927 : Blo 279826 479927 := bstep (se 1 (by rfl) ⟨359945, by rfl⟩ : syracuseStep 479927 = 719891) B719891
theorem B283359 : Blo 279826 283359 := bstep (se 1 (by rfl) ⟨212519, by rfl⟩ : syracuseStep 283359 = 425039) B425039
theorem B283439 : Blo 279826 283439 := bstep (se 1 (by rfl) ⟨212579, by rfl⟩ : syracuseStep 283439 = 425159) B425159
theorem B709519 : Blo 279826 709519 := bstep (se 1 (by rfl) ⟨532139, by rfl⟩ : syracuseStep 709519 = 1064279) B1064279
theorem B283547 : Blo 279826 283547 := bstep (se 1 (by rfl) ⟨212660, by rfl⟩ : syracuseStep 283547 = 425321) B425321
theorem B5428133 : Blo 279826 5428133 := bstep (se 4 (by rfl) ⟨508887, by rfl⟩ : syracuseStep 5428133 = 1017775) B1017775
theorem B283599 : Blo 279826 283599 := bstep (se 1 (by rfl) ⟨212699, by rfl⟩ : syracuseStep 283599 = 425399) B425399
theorem B283623 : Blo 279826 283623 := bstep (se 1 (by rfl) ⟨212717, by rfl⟩ : syracuseStep 283623 = 425435) B425435
theorem B1070279 : Blo 279826 1070279 := bstep (se 1 (by rfl) ⟨802709, by rfl⟩ : syracuseStep 1070279 = 1605419) B1605419
theorem B709985 : Blo 279826 709985 := bstep (se 2 (by rfl) ⟨266244, by rfl⟩ : syracuseStep 709985 = 532489) B532489
theorem B316795 : Blo 279826 316795 := bstep (se 1 (by rfl) ⟨237596, by rfl⟩ : syracuseStep 316795 = 475193) B475193
theorem B1430945 : Blo 279826 1430945 := bstep (se 2 (by rfl) ⟨536604, by rfl⟩ : syracuseStep 1430945 = 1073209) B1073209
theorem B677335 : Blo 279826 677335 := bstep (se 1 (by rfl) ⟨508001, by rfl⟩ : syracuseStep 677335 = 1016003) B1016003
theorem B1070779 : Blo 279826 1070779 := bstep (se 1 (by rfl) ⟨803084, by rfl⟩ : syracuseStep 1070779 = 1606169) B1606169
theorem B710441 : Blo 279826 710441 := bstep (se 2 (by rfl) ⟨266415, by rfl⟩ : syracuseStep 710441 = 532831) B532831
theorem B317263 : Blo 279826 317263 := bstep (se 1 (by rfl) ⟨237947, by rfl⟩ : syracuseStep 317263 = 475895) B475895
theorem B317659 : Blo 279826 317659 := bstep (se 1 (by rfl) ⟨238244, by rfl⟩ : syracuseStep 317659 = 476489) B476489
theorem B5429591 : Blo 279826 5429591 := bstep (se 1 (by rfl) ⟨4072193, by rfl⟩ : syracuseStep 5429591 = 8144387) B8144387
theorem B448859 : Blo 279826 448859 := bstep (se 1 (by rfl) ⟨336644, by rfl⟩ : syracuseStep 448859 = 673289) B673289
theorem B317947 : Blo 279826 317947 := bstep (se 1 (by rfl) ⟨238460, by rfl⟩ : syracuseStep 317947 = 476921) B476921
theorem B318127 : Blo 279826 318127 := bstep (se 1 (by rfl) ⟨238595, by rfl⟩ : syracuseStep 318127 = 477191) B477191
theorem B645815 : Blo 279826 645815 := bstep (se 1 (by rfl) ⟨484361, by rfl⟩ : syracuseStep 645815 = 968723) B968723
theorem B711443 : Blo 279826 711443 := bstep (se 1 (by rfl) ⟨533582, by rfl⟩ : syracuseStep 711443 = 1067165) B1067165
theorem B318415 : Blo 279826 318415 := bstep (se 1 (by rfl) ⟨238811, by rfl⟩ : syracuseStep 318415 = 477623) B477623
theorem B711899 : Blo 279826 711899 := bstep (se 1 (by rfl) ⟨533924, by rfl⟩ : syracuseStep 711899 = 1067849) B1067849
theorem B711929 : Blo 279826 711929 := bstep (se 2 (by rfl) ⟨266973, by rfl⟩ : syracuseStep 711929 = 533947) B533947
theorem B318811 : Blo 279826 318811 := bstep (se 1 (by rfl) ⟨239108, by rfl⟩ : syracuseStep 318811 = 478217) B478217
theorem B318919 : Blo 279826 318919 := bstep (se 1 (by rfl) ⟨239189, by rfl⟩ : syracuseStep 318919 = 478379) B478379
theorem B1072723 : Blo 279826 1072723 := bstep (se 1 (by rfl) ⟨804542, by rfl⟩ : syracuseStep 1072723 = 1609085) B1609085
theorem B319279 : Blo 279826 319279 := bstep (se 1 (by rfl) ⟨239459, by rfl⟩ : syracuseStep 319279 = 478919) B478919
theorem B712577 : Blo 279826 712577 := bstep (se 2 (by rfl) ⟨267216, by rfl⟩ : syracuseStep 712577 = 534433) B534433
theorem B6086663 : Blo 279826 6086663 := bstep (se 1 (by rfl) ⟨4564997, by rfl⟩ : syracuseStep 6086663 = 9129995) B9129995
theorem B2187383 : Blo 279826 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B713033 : Blo 279826 713033 := bstep (se 2 (by rfl) ⟨267387, by rfl⟩ : syracuseStep 713033 = 534775) B534775
theorem B942443 : Blo 279826 942443 := bstep (se 1 (by rfl) ⟨706832, by rfl⟩ : syracuseStep 942443 = 1413665) B1413665
theorem B4842017 : Blo 279826 4842017 := bstep (se 2 (by rfl) ⟨1815756, by rfl⟩ : syracuseStep 4842017 = 3631513) B3631513
theorem B713387 : Blo 279826 713387 := bstep (se 1 (by rfl) ⟨535040, by rfl⟩ : syracuseStep 713387 = 1070081) B1070081
theorem B1794743 : Blo 279826 1794743 := bstep (se 1 (by rfl) ⟨1346057, by rfl⟩ : syracuseStep 1794743 = 2692115) B2692115
theorem B1073999 : Blo 279826 1073999 := bstep (se 1 (by rfl) ⟨805499, by rfl⟩ : syracuseStep 1073999 = 1610999) B1610999
theorem B10216367 : Blo 279826 10216367 := bstep (se 1 (by rfl) ⟨7662275, by rfl⟩ : syracuseStep 10216367 = 15324551) B15324551
theorem B1074167 : Blo 279826 1074167 := bstep (se 1 (by rfl) ⟨805625, by rfl⟩ : syracuseStep 1074167 = 1611251) B1611251
theorem B1598561 : Blo 279826 1598561 := bstep (se 2 (by rfl) ⟨599460, by rfl⟩ : syracuseStep 1598561 = 1198921) B1198921
theorem B2942855 : Blo 279826 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B714703 : Blo 279826 714703 := bstep (se 1 (by rfl) ⟨536027, by rfl⟩ : syracuseStep 714703 = 1072055) B1072055
theorem B419945 : Blo 279826 419945 := bstep (se 2 (by rfl) ⟨157479, by rfl⟩ : syracuseStep 419945 = 314959) B314959
theorem B420263 : Blo 279826 420263 := bstep (se 1 (by rfl) ⟨315197, by rfl⟩ : syracuseStep 420263 = 630395) B630395
theorem B944567 : Blo 279826 944567 := bstep (se 1 (by rfl) ⟨708425, by rfl⟩ : syracuseStep 944567 = 1416851) B1416851
theorem B1075639 : Blo 279826 1075639 := bstep (se 1 (by rfl) ⟨806729, by rfl⟩ : syracuseStep 1075639 = 1613459) B1613459
theorem B420347 : Blo 279826 420347 := bstep (se 1 (by rfl) ⟨315260, by rfl⟩ : syracuseStep 420347 = 630521) B630521
theorem B911945 : Blo 279826 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B420473 : Blo 279826 420473 := bstep (se 2 (by rfl) ⟨157677, by rfl⟩ : syracuseStep 420473 = 315355) B315355
theorem B420527 : Blo 279826 420527 := bstep (se 1 (by rfl) ⟨315395, by rfl⟩ : syracuseStep 420527 = 630791) B630791
theorem B420575 : Blo 279826 420575 := bstep (se 1 (by rfl) ⟨315431, by rfl⟩ : syracuseStep 420575 = 630863) B630863
theorem B1076111 : Blo 279826 1076111 := bstep (se 1 (by rfl) ⟨807083, by rfl⟩ : syracuseStep 1076111 = 1614167) B1614167
theorem B715675 : Blo 279826 715675 := bstep (se 1 (by rfl) ⟨536756, by rfl⟩ : syracuseStep 715675 = 1073513) B1073513
theorem B420839 : Blo 279826 420839 := bstep (se 1 (by rfl) ⟨315629, by rfl⟩ : syracuseStep 420839 = 631259) B631259
theorem B2419915 : Blo 279826 2419915 := bstep (se 1 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 2419915 = 3629873) B3629873
theorem B421097 : Blo 279826 421097 := bstep (se 2 (by rfl) ⟨157911, by rfl⟩ : syracuseStep 421097 = 315823) B315823
theorem B421151 : Blo 279826 421151 := bstep (se 1 (by rfl) ⟨315863, by rfl⟩ : syracuseStep 421151 = 631727) B631727
theorem B2583839 : Blo 279826 2583839 := bstep (se 1 (by rfl) ⟨1937879, by rfl⟩ : syracuseStep 2583839 = 3875759) B3875759
theorem B1207619 : Blo 279826 1207619 := bstep (se 1 (by rfl) ⟨905714, by rfl⟩ : syracuseStep 1207619 = 1811429) B1811429
theorem B421319 : Blo 279826 421319 := bstep (se 1 (by rfl) ⟨315989, by rfl⟩ : syracuseStep 421319 = 631979) B631979
theorem B44330453 : Blo 279826 44330453 := bstep (se 7 (by rfl) ⟨519497, by rfl⟩ : syracuseStep 44330453 = 1038995) B1038995
theorem B356015 : Blo 279826 356015 := bstep (se 1 (by rfl) ⟨267011, by rfl⟩ : syracuseStep 356015 = 534023) B534023
theorem B2158289 : Blo 279826 2158289 := bstep (se 2 (by rfl) ⟨809358, by rfl⟩ : syracuseStep 2158289 = 1618717) B1618717
theorem B519943 : Blo 279826 519943 := bstep (se 1 (by rfl) ⟨389957, by rfl⟩ : syracuseStep 519943 = 779915) B779915
theorem B421673 : Blo 279826 421673 := bstep (se 2 (by rfl) ⟨158127, by rfl⟩ : syracuseStep 421673 = 316255) B316255
theorem B2453291 : Blo 279826 2453291 := bstep (se 1 (by rfl) ⟨1839968, by rfl⟩ : syracuseStep 2453291 = 3679937) B3679937
theorem B421679 : Blo 279826 421679 := bstep (se 1 (by rfl) ⟨316259, by rfl⟩ : syracuseStep 421679 = 632519) B632519
theorem B716809 : Blo 279826 716809 := bstep (se 2 (by rfl) ⟨268803, by rfl⟩ : syracuseStep 716809 = 537607) B537607
theorem B1601795 : Blo 279826 1601795 := bstep (se 1 (by rfl) ⟨1201346, by rfl⟩ : syracuseStep 1601795 = 2402693) B2402693
theorem B422153 : Blo 279826 422153 := bstep (se 2 (by rfl) ⟨158307, by rfl⟩ : syracuseStep 422153 = 316615) B316615
theorem B422255 : Blo 279826 422255 := bstep (se 1 (by rfl) ⟨316691, by rfl⟩ : syracuseStep 422255 = 633383) B633383
theorem B356719 : Blo 279826 356719 := bstep (se 1 (by rfl) ⟨267539, by rfl⟩ : syracuseStep 356719 = 535079) B535079
theorem B3207599 : Blo 279826 3207599 := bstep (se 1 (by rfl) ⟨2405699, by rfl⟩ : syracuseStep 3207599 = 4811399) B4811399
theorem B422471 : Blo 279826 422471 := bstep (se 1 (by rfl) ⟨316853, by rfl⟩ : syracuseStep 422471 = 633707) B633707
theorem B422507 : Blo 279826 422507 := bstep (se 1 (by rfl) ⟨316880, by rfl⟩ : syracuseStep 422507 = 633761) B633761
theorem B422735 : Blo 279826 422735 := bstep (se 1 (by rfl) ⟨317051, by rfl⟩ : syracuseStep 422735 = 634103) B634103
theorem B2290679 : Blo 279826 2290679 := bstep (se 1 (by rfl) ⟨1718009, by rfl⟩ : syracuseStep 2290679 = 3436019) B3436019
theorem B423131 : Blo 279826 423131 := bstep (se 1 (by rfl) ⟨317348, by rfl⟩ : syracuseStep 423131 = 634697) B634697
theorem B11728151 : Blo 279826 11728151 := bstep (se 1 (by rfl) ⟨8796113, by rfl⟩ : syracuseStep 11728151 = 17592227) B17592227
theorem B423305 : Blo 279826 423305 := bstep (se 2 (by rfl) ⟨158739, by rfl⟩ : syracuseStep 423305 = 317479) B317479
theorem B718217 : Blo 279826 718217 := bstep (se 2 (by rfl) ⟨269331, by rfl⟩ : syracuseStep 718217 = 538663) B538663
theorem B718267 : Blo 279826 718267 := bstep (se 1 (by rfl) ⟨538700, by rfl⟩ : syracuseStep 718267 = 1077401) B1077401
theorem B947645 : Blo 279826 947645 := bstep (se 3 (by rfl) ⟨177683, by rfl⟩ : syracuseStep 947645 = 355367) B355367
theorem B357959 : Blo 279826 357959 := bstep (se 1 (by rfl) ⟨268469, by rfl⟩ : syracuseStep 357959 = 536939) B536939
theorem B358111 : Blo 279826 358111 := bstep (se 1 (by rfl) ⟨268583, by rfl⟩ : syracuseStep 358111 = 537167) B537167
theorem B423659 : Blo 279826 423659 := bstep (se 1 (by rfl) ⟨317744, by rfl⟩ : syracuseStep 423659 = 635489) B635489
theorem B948023 : Blo 279826 948023 := bstep (se 1 (by rfl) ⟨711017, by rfl⟩ : syracuseStep 948023 = 1422035) B1422035
theorem B423887 : Blo 279826 423887 := bstep (se 1 (by rfl) ⟨317915, by rfl⟩ : syracuseStep 423887 = 635831) B635831
theorem B5142629 : Blo 279826 5142629 := bstep (se 4 (by rfl) ⟨482121, by rfl⟩ : syracuseStep 5142629 = 964243) B964243
theorem B948509 : Blo 279826 948509 := bstep (se 3 (by rfl) ⟨177845, by rfl⟩ : syracuseStep 948509 = 355691) B355691
theorem B424283 : Blo 279826 424283 := bstep (se 1 (by rfl) ⟨318212, by rfl⟩ : syracuseStep 424283 = 636425) B636425
theorem B883055 : Blo 279826 883055 := bstep (se 1 (by rfl) ⟨662291, by rfl⟩ : syracuseStep 883055 = 1324583) B1324583
theorem B6126029 : Blo 279826 6126029 := bstep (se 3 (by rfl) ⟨1148630, by rfl⟩ : syracuseStep 6126029 = 2297261) B2297261
theorem B424511 : Blo 279826 424511 := bstep (se 1 (by rfl) ⟨318383, by rfl⟩ : syracuseStep 424511 = 636767) B636767
theorem B424631 : Blo 279826 424631 := bstep (se 1 (by rfl) ⟨318473, by rfl⟩ : syracuseStep 424631 = 636947) B636947
theorem B424859 : Blo 279826 424859 := bstep (se 1 (by rfl) ⟨318644, by rfl⟩ : syracuseStep 424859 = 637289) B637289
theorem B2456507 : Blo 279826 2456507 := bstep (se 1 (by rfl) ⟨1842380, by rfl⟩ : syracuseStep 2456507 = 3684761) B3684761
theorem B949535 : Blo 279826 949535 := bstep (se 1 (by rfl) ⟨712151, by rfl⟩ : syracuseStep 949535 = 1424303) B1424303
theorem B425255 : Blo 279826 425255 := bstep (se 1 (by rfl) ⟨318941, by rfl⟩ : syracuseStep 425255 = 637883) B637883
theorem B425339 : Blo 279826 425339 := bstep (se 1 (by rfl) ⟨319004, by rfl⟩ : syracuseStep 425339 = 638009) B638009
theorem B425465 : Blo 279826 425465 := bstep (se 2 (by rfl) ⟨159549, by rfl⟩ : syracuseStep 425465 = 319099) B319099
theorem B425567 : Blo 279826 425567 := bstep (se 1 (by rfl) ⟨319175, by rfl⟩ : syracuseStep 425567 = 638351) B638351
theorem B818849 : Blo 279826 818849 := bstep (se 2 (by rfl) ⟨307068, by rfl⟩ : syracuseStep 818849 = 614137) B614137
theorem B1212317 : Blo 279826 1212317 := bstep (se 3 (by rfl) ⟨227309, by rfl⟩ : syracuseStep 1212317 = 454619) B454619
theorem B1212335 : Blo 279826 1212335 := bstep (se 1 (by rfl) ⟨909251, by rfl⟩ : syracuseStep 1212335 = 1818503) B1818503
theorem B3244313 : Blo 279826 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B4129049 : Blo 279826 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B491807 : Blo 279826 491807 := bstep (se 1 (by rfl) ⟨368855, by rfl⟩ : syracuseStep 491807 = 737711) B737711
theorem B5833021 : Blo 279826 5833021 := bstep (se 3 (by rfl) ⟨1093691, by rfl⟩ : syracuseStep 5833021 = 2187383) B2187383
theorem B1966787 : Blo 279826 1966787 := bstep (se 1 (by rfl) ⟨1475090, by rfl⟩ : syracuseStep 1966787 = 2950181) B2950181
theorem B721831 : Blo 279826 721831 := bstep (se 1 (by rfl) ⟨541373, by rfl⟩ : syracuseStep 721831 = 1082747) B1082747
theorem B1606877 : Blo 279826 1606877 := bstep (se 3 (by rfl) ⟨301289, by rfl⟩ : syracuseStep 1606877 = 602579) B602579
theorem B1017359 : Blo 279826 1017359 := bstep (se 1 (by rfl) ⟨763019, by rfl⟩ : syracuseStep 1017359 = 1526039) B1526039
theorem B788135 : Blo 279826 788135 := bstep (se 1 (by rfl) ⟨591101, by rfl⟩ : syracuseStep 788135 = 1182203) B1182203
theorem B1279805 : Blo 279826 1279805 := bstep (se 3 (by rfl) ⟨239963, by rfl⟩ : syracuseStep 1279805 = 479927) B479927
theorem B3213431 : Blo 279826 3213431 := bstep (se 1 (by rfl) ⟨2410073, by rfl⟩ : syracuseStep 3213431 = 4820147) B4820147
theorem B952667 : Blo 279826 952667 := bstep (se 1 (by rfl) ⟨714500, by rfl⟩ : syracuseStep 952667 = 1429001) B1429001
theorem B3475993 : Blo 279826 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B952937 : Blo 279826 952937 := bstep (se 2 (by rfl) ⟨357351, by rfl⟩ : syracuseStep 952937 = 714703) B714703
theorem B953963 : Blo 279826 953963 := bstep (se 1 (by rfl) ⟨715472, by rfl⟩ : syracuseStep 953963 = 1430945) B1430945
theorem B954233 : Blo 279826 954233 := bstep (se 2 (by rfl) ⟨357837, by rfl⟩ : syracuseStep 954233 = 715675) B715675
theorem B954557 : Blo 279826 954557 := bstep (se 3 (by rfl) ⟨178979, by rfl⟩ : syracuseStep 954557 = 357959) B357959
theorem B6885647 : Blo 279826 6885647 := bstep (se 1 (by rfl) ⟨5164235, by rfl⟩ : syracuseStep 6885647 = 10328471) B10328471
theorem B758153 : Blo 279826 758153 := bstep (se 2 (by rfl) ⟨284307, by rfl⟩ : syracuseStep 758153 = 568615) B568615
theorem B430543 : Blo 279826 430543 := bstep (se 1 (by rfl) ⟨322907, by rfl⟩ : syracuseStep 430543 = 645815) B645815
theorem B3937085 : Blo 279826 3937085 := bstep (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) B1476407
theorem B693257 : Blo 279826 693257 := bstep (se 2 (by rfl) ⟨259971, by rfl⟩ : syracuseStep 693257 = 519943) B519943
theorem B4199633 : Blo 279826 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B955745 : Blo 279826 955745 := bstep (se 2 (by rfl) ⟨358404, by rfl⟩ : syracuseStep 955745 = 716809) B716809
theorem B628295 : Blo 279826 628295 := bstep (se 1 (by rfl) ⟨471221, by rfl⟩ : syracuseStep 628295 = 942443) B942443
theorem B3151673 : Blo 279826 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B2168783 : Blo 279826 2168783 := bstep (se 1 (by rfl) ⟨1626587, by rfl⟩ : syracuseStep 2168783 = 3253175) B3253175
theorem B727003 : Blo 279826 727003 := bstep (se 1 (by rfl) ⟨545252, by rfl⟩ : syracuseStep 727003 = 1090505) B1090505
theorem B2431043 : Blo 279826 2431043 := bstep (se 1 (by rfl) ⟨1823282, by rfl⟩ : syracuseStep 2431043 = 3646565) B3646565
theorem B399595 : Blo 279826 399595 := bstep (se 1 (by rfl) ⟨299696, by rfl⟩ : syracuseStep 399595 = 599393) B599393
theorem B8460935 : Blo 279826 8460935 := bstep (se 1 (by rfl) ⟨6345701, by rfl⟩ : syracuseStep 8460935 = 12691403) B12691403
theorem B1710953 : Blo 279826 1710953 := bstep (se 2 (by rfl) ⟨641607, by rfl⟩ : syracuseStep 1710953 = 1283215) B1283215
theorem B2431853 : Blo 279826 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B2136941 : Blo 279826 2136941 := bstep (se 3 (by rfl) ⟨400676, by rfl⟩ : syracuseStep 2136941 = 801353) B801353
theorem B629711 : Blo 279826 629711 := bstep (se 1 (by rfl) ⟨472283, by rfl⟩ : syracuseStep 629711 = 944567) B944567
theorem B629729 : Blo 279826 629729 := bstep (se 2 (by rfl) ⟨236148, by rfl⟩ : syracuseStep 629729 = 472297) B472297
theorem B629801 : Blo 279826 629801 := bstep (se 2 (by rfl) ⟨236175, by rfl⟩ : syracuseStep 629801 = 472351) B472351
theorem B957689 : Blo 279826 957689 := bstep (se 2 (by rfl) ⟨359133, by rfl⟩ : syracuseStep 957689 = 718267) B718267
theorem B6757967 : Blo 279826 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B2400029 : Blo 279826 2400029 := bstep (se 3 (by rfl) ⟨450005, by rfl⟩ : syracuseStep 2400029 = 900011) B900011
theorem B2138399 : Blo 279826 2138399 := bstep (se 1 (by rfl) ⟨1603799, by rfl⟩ : syracuseStep 2138399 = 3207599) B3207599
theorem B631763 : Blo 279826 631763 := bstep (se 1 (by rfl) ⟨473822, by rfl⟩ : syracuseStep 631763 = 947645) B947645
theorem B632015 : Blo 279826 632015 := bstep (se 1 (by rfl) ⟨474011, by rfl⟩ : syracuseStep 632015 = 948023) B948023
theorem B1418633 : Blo 279826 1418633 := bstep (se 2 (by rfl) ⟨531987, by rfl⟩ : syracuseStep 1418633 = 1063975) B1063975
theorem B632339 : Blo 279826 632339 := bstep (se 1 (by rfl) ⟨474254, by rfl⟩ : syracuseStep 632339 = 948509) B948509
theorem B3614291 : Blo 279826 3614291 := bstep (se 1 (by rfl) ⟨2710718, by rfl⟩ : syracuseStep 3614291 = 5421437) B5421437
theorem B1451603 : Blo 279826 1451603 := bstep (se 1 (by rfl) ⟨1088702, by rfl⟩ : syracuseStep 1451603 = 2177405) B2177405
theorem B633023 : Blo 279826 633023 := bstep (se 1 (by rfl) ⟨474767, by rfl⟩ : syracuseStep 633023 = 949535) B949535
theorem B633977 : Blo 279826 633977 := bstep (se 2 (by rfl) ⟨237741, by rfl⟩ : syracuseStep 633977 = 475483) B475483
theorem B3190103 : Blo 279826 3190103 := bstep (se 1 (by rfl) ⟨2392577, by rfl⟩ : syracuseStep 3190103 = 4785155) B4785155
theorem B1813913 : Blo 279826 1813913 := bstep (se 2 (by rfl) ⟨680217, by rfl⟩ : syracuseStep 1813913 = 1360435) B1360435
theorem B1715671 : Blo 279826 1715671 := bstep (se 1 (by rfl) ⟨1286753, by rfl⟩ : syracuseStep 1715671 = 2573507) B2573507
theorem B568939 : Blo 279826 568939 := bstep (se 1 (by rfl) ⟨426704, by rfl⟩ : syracuseStep 568939 = 853409) B853409
theorem B13676303 : Blo 279826 13676303 := bstep (se 1 (by rfl) ⟨10257227, by rfl⟩ : syracuseStep 13676303 = 20514455) B20514455
theorem B634643 : Blo 279826 634643 := bstep (se 1 (by rfl) ⟨475982, by rfl⟩ : syracuseStep 634643 = 951965) B951965
theorem B896807 : Blo 279826 896807 := bstep (se 1 (by rfl) ⟨672605, by rfl⟩ : syracuseStep 896807 = 1345211) B1345211
theorem B4042669 : Blo 279826 4042669 := bstep (se 3 (by rfl) ⟨758000, by rfl⟩ : syracuseStep 4042669 = 1516001) B1516001
theorem B2404403 : Blo 279826 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B1355899 : Blo 279826 1355899 := bstep (se 1 (by rfl) ⟨1016924, by rfl⟩ : syracuseStep 1355899 = 2033849) B2033849
theorem B635003 : Blo 279826 635003 := bstep (se 1 (by rfl) ⟨476252, by rfl⟩ : syracuseStep 635003 = 952505) B952505
theorem B635273 : Blo 279826 635273 := bstep (se 2 (by rfl) ⟨238227, by rfl⟩ : syracuseStep 635273 = 476455) B476455
theorem B536969 : Blo 279826 536969 := bstep (se 2 (by rfl) ⟨201363, by rfl⟩ : syracuseStep 536969 = 402727) B402727
theorem B1421711 : Blo 279826 1421711 := bstep (se 1 (by rfl) ⟨1066283, by rfl⟩ : syracuseStep 1421711 = 2132567) B2132567
theorem B897551 : Blo 279826 897551 := bstep (se 1 (by rfl) ⟨673163, by rfl⟩ : syracuseStep 897551 = 1346327) B1346327
theorem B2405153 : Blo 279826 2405153 := bstep (se 2 (by rfl) ⟨901932, by rfl⟩ : syracuseStep 2405153 = 1803865) B1803865
theorem B14725961 : Blo 279826 14725961 := bstep (se 2 (by rfl) ⟨5522235, by rfl⟩ : syracuseStep 14725961 = 11044471) B11044471
theorem B636011 : Blo 279826 636011 := bstep (se 1 (by rfl) ⟨477008, by rfl⟩ : syracuseStep 636011 = 954017) B954017
theorem B799919 : Blo 279826 799919 := bstep (se 1 (by rfl) ⟨599939, by rfl⟩ : syracuseStep 799919 = 1199879) B1199879
theorem B1520957 : Blo 279826 1520957 := bstep (se 3 (by rfl) ⟨285179, by rfl⟩ : syracuseStep 1520957 = 570359) B570359
theorem B2143745 : Blo 279826 2143745 := bstep (se 2 (by rfl) ⟨803904, by rfl⟩ : syracuseStep 2143745 = 1607809) B1607809
theorem B3618391 : Blo 279826 3618391 := bstep (se 1 (by rfl) ⟨2713793, by rfl⟩ : syracuseStep 3618391 = 5427587) B5427587
theorem B636587 : Blo 279826 636587 := bstep (se 1 (by rfl) ⟨477440, by rfl⟩ : syracuseStep 636587 = 954881) B954881
theorem B3618755 : Blo 279826 3618755 := bstep (se 1 (by rfl) ⟨2714066, by rfl⟩ : syracuseStep 3618755 = 5428133) B5428133
theorem B636911 : Blo 279826 636911 := bstep (se 1 (by rfl) ⟨477683, by rfl⟩ : syracuseStep 636911 = 955367) B955367
theorem B800761 : Blo 279826 800761 := bstep (se 2 (by rfl) ⟨300285, by rfl⟩ : syracuseStep 800761 = 600571) B600571
theorem B964601 : Blo 279826 964601 := bstep (se 2 (by rfl) ⟨361725, by rfl⟩ : syracuseStep 964601 = 723451) B723451
theorem B637127 : Blo 279826 637127 := bstep (se 1 (by rfl) ⟨477845, by rfl⟩ : syracuseStep 637127 = 955691) B955691
theorem B473323 : Blo 279826 473323 := bstep (se 1 (by rfl) ⟨354992, by rfl⟩ : syracuseStep 473323 = 709985) B709985
theorem B3422537 : Blo 279826 3422537 := bstep (se 2 (by rfl) ⟨1283451, by rfl⟩ : syracuseStep 3422537 = 2566903) B2566903
theorem B1063277 : Blo 279826 1063277 := bstep (se 3 (by rfl) ⟨199364, by rfl⟩ : syracuseStep 1063277 = 398729) B398729
theorem B637307 : Blo 279826 637307 := bstep (se 1 (by rfl) ⟨477980, by rfl⟩ : syracuseStep 637307 = 955961) B955961
theorem B7256465 : Blo 279826 7256465 := bstep (se 2 (by rfl) ⟨2721174, by rfl⟩ : syracuseStep 7256465 = 5442349) B5442349
theorem B473627 : Blo 279826 473627 := bstep (se 1 (by rfl) ⟨355220, by rfl⟩ : syracuseStep 473627 = 710441) B710441
theorem B637577 : Blo 279826 637577 := bstep (se 2 (by rfl) ⟨239091, by rfl⟩ : syracuseStep 637577 = 478183) B478183
theorem B3619727 : Blo 279826 3619727 := bstep (se 1 (by rfl) ⟨2714795, by rfl⟩ : syracuseStep 3619727 = 5429591) B5429591
theorem B3226553 : Blo 279826 3226553 := bstep (se 2 (by rfl) ⟨1209957, by rfl⟩ : syracuseStep 3226553 = 2419915) B2419915
theorem B474295 : Blo 279826 474295 := bstep (se 1 (by rfl) ⟨355721, by rfl⟩ : syracuseStep 474295 = 711443) B711443
theorem B638135 : Blo 279826 638135 := bstep (se 1 (by rfl) ⟨478601, by rfl⟩ : syracuseStep 638135 = 957203) B957203
theorem B474599 : Blo 279826 474599 := bstep (se 1 (by rfl) ⟨355949, by rfl⟩ : syracuseStep 474599 = 711899) B711899
theorem B474619 : Blo 279826 474619 := bstep (se 1 (by rfl) ⟨355964, by rfl⟩ : syracuseStep 474619 = 711929) B711929
theorem B472858165 : Blo 279826 472858165 := bstep (se 5 (by rfl) ⟨22165226, by rfl⟩ : syracuseStep 472858165 = 44330453) B44330453
theorem B3194477 : Blo 279826 3194477 := bstep (se 3 (by rfl) ⟨598964, by rfl⟩ : syracuseStep 3194477 = 1197929) B1197929
theorem B475051 : Blo 279826 475051 := bstep (se 1 (by rfl) ⟨356288, by rfl⟩ : syracuseStep 475051 = 712577) B712577
theorem B475355 : Blo 279826 475355 := bstep (se 1 (by rfl) ⟨356516, by rfl⟩ : syracuseStep 475355 = 713033) B713033
theorem B3228011 : Blo 279826 3228011 := bstep (se 1 (by rfl) ⟨2421008, by rfl⟩ : syracuseStep 3228011 = 4842017) B4842017
theorem B475591 : Blo 279826 475591 := bstep (se 1 (by rfl) ⟨356693, by rfl⟩ : syracuseStep 475591 = 713387) B713387
theorem B1196495 : Blo 279826 1196495 := bstep (se 1 (by rfl) ⟨897371, by rfl⟩ : syracuseStep 1196495 = 1794743) B1794743
theorem B475625 : Blo 279826 475625 := bstep (se 2 (by rfl) ⟨178359, by rfl⟩ : syracuseStep 475625 = 356719) B356719
theorem B1065707 : Blo 279826 1065707 := bstep (se 1 (by rfl) ⟨799280, by rfl⟩ : syracuseStep 1065707 = 1598561) B1598561
theorem B1065737 : Blo 279826 1065737 := bstep (se 2 (by rfl) ⟨399651, by rfl⟩ : syracuseStep 1065737 = 799303) B799303
theorem B1196957 : Blo 279826 1196957 := bstep (se 3 (by rfl) ⟨224429, by rfl⟩ : syracuseStep 1196957 = 448859) B448859
theorem B279963 : Blo 279826 279963 := bstep (se 1 (by rfl) ⟨209972, by rfl⟩ : syracuseStep 279963 = 419945) B419945
theorem B24823331 : Blo 279826 24823331 := bstep (se 1 (by rfl) ⟨18617498, by rfl⟩ : syracuseStep 24823331 = 37234997) B37234997
theorem B280175 : Blo 279826 280175 := bstep (se 1 (by rfl) ⟨210131, by rfl⟩ : syracuseStep 280175 = 420263) B420263
theorem B280231 : Blo 279826 280231 := bstep (se 1 (by rfl) ⟨210173, by rfl⟩ : syracuseStep 280231 = 420347) B420347
theorem B280315 : Blo 279826 280315 := bstep (se 1 (by rfl) ⟨210236, by rfl⟩ : syracuseStep 280315 = 420473) B420473
theorem B280351 : Blo 279826 280351 := bstep (se 1 (by rfl) ⟨210263, by rfl⟩ : syracuseStep 280351 = 420527) B420527
theorem B280383 : Blo 279826 280383 := bstep (se 1 (by rfl) ⟨210287, by rfl⟩ : syracuseStep 280383 = 420575) B420575
theorem B903113 : Blo 279826 903113 := bstep (se 2 (by rfl) ⟨338667, by rfl⟩ : syracuseStep 903113 = 677335) B677335
theorem B280559 : Blo 279826 280559 := bstep (se 1 (by rfl) ⟨210419, by rfl⟩ : syracuseStep 280559 = 420839) B420839
theorem B280731 : Blo 279826 280731 := bstep (se 1 (by rfl) ⟨210548, by rfl⟩ : syracuseStep 280731 = 421097) B421097
theorem B280767 : Blo 279826 280767 := bstep (se 1 (by rfl) ⟨210575, by rfl⟩ : syracuseStep 280767 = 421151) B421151
theorem B1722559 : Blo 279826 1722559 := bstep (se 1 (by rfl) ⟨1291919, by rfl⟩ : syracuseStep 1722559 = 2583839) B2583839
theorem B805079 : Blo 279826 805079 := bstep (se 1 (by rfl) ⟨603809, by rfl⟩ : syracuseStep 805079 = 1207619) B1207619
theorem B1427705 : Blo 279826 1427705 := bstep (se 2 (by rfl) ⟨535389, by rfl⟩ : syracuseStep 1427705 = 1070779) B1070779
theorem B477481 : Blo 279826 477481 := bstep (se 2 (by rfl) ⟨179055, by rfl⟩ : syracuseStep 477481 = 358111) B358111
theorem B280879 : Blo 279826 280879 := bstep (se 1 (by rfl) ⟨210659, by rfl⟩ : syracuseStep 280879 = 421319) B421319
theorem B281115 : Blo 279826 281115 := bstep (se 1 (by rfl) ⟨210836, by rfl⟩ : syracuseStep 281115 = 421673) B421673
theorem B281119 : Blo 279826 281119 := bstep (se 1 (by rfl) ⟨210839, by rfl⟩ : syracuseStep 281119 = 421679) B421679
theorem B1067863 : Blo 279826 1067863 := bstep (se 1 (by rfl) ⟨800897, by rfl⟩ : syracuseStep 1067863 = 1601795) B1601795
theorem B281435 : Blo 279826 281435 := bstep (se 1 (by rfl) ⟨211076, by rfl⟩ : syracuseStep 281435 = 422153) B422153
theorem B281503 : Blo 279826 281503 := bstep (se 1 (by rfl) ⟨211127, by rfl⟩ : syracuseStep 281503 = 422255) B422255
theorem B281647 : Blo 279826 281647 := bstep (se 1 (by rfl) ⟨211235, by rfl⟩ : syracuseStep 281647 = 422471) B422471
theorem B281671 : Blo 279826 281671 := bstep (se 1 (by rfl) ⟨211253, by rfl⟩ : syracuseStep 281671 = 422507) B422507
theorem B281823 : Blo 279826 281823 := bstep (se 1 (by rfl) ⟨211367, by rfl⟩ : syracuseStep 281823 = 422735) B422735
theorem B1527119 : Blo 279826 1527119 := bstep (se 1 (by rfl) ⟨1145339, by rfl⟩ : syracuseStep 1527119 = 2290679) B2290679
theorem B282087 : Blo 279826 282087 := bstep (se 1 (by rfl) ⟨211565, by rfl⟩ : syracuseStep 282087 = 423131) B423131
theorem B7818767 : Blo 279826 7818767 := bstep (se 1 (by rfl) ⟨5864075, by rfl⟩ : syracuseStep 7818767 = 11728151) B11728151
theorem B282203 : Blo 279826 282203 := bstep (se 1 (by rfl) ⟨211652, by rfl⟩ : syracuseStep 282203 = 423305) B423305
theorem B478811 : Blo 279826 478811 := bstep (se 1 (by rfl) ⟨359108, by rfl⟩ : syracuseStep 478811 = 718217) B718217
theorem B315175 : Blo 279826 315175 := bstep (se 1 (by rfl) ⟨236381, by rfl⟩ : syracuseStep 315175 = 472763) B472763
theorem B282439 : Blo 279826 282439 := bstep (se 1 (by rfl) ⟨211829, by rfl⟩ : syracuseStep 282439 = 423659) B423659
theorem B1363817 : Blo 279826 1363817 := bstep (se 2 (by rfl) ⟨511431, by rfl⟩ : syracuseStep 1363817 = 1022863) B1022863
theorem B282591 : Blo 279826 282591 := bstep (se 1 (by rfl) ⟨211943, by rfl⟩ : syracuseStep 282591 = 423887) B423887
theorem B3428419 : Blo 279826 3428419 := bstep (se 1 (by rfl) ⟨2571314, by rfl⟩ : syracuseStep 3428419 = 5142629) B5142629
theorem B282855 : Blo 279826 282855 := bstep (se 1 (by rfl) ⟨212141, by rfl⟩ : syracuseStep 282855 = 424283) B424283
theorem B4084019 : Blo 279826 4084019 := bstep (se 1 (by rfl) ⟨3063014, by rfl⟩ : syracuseStep 4084019 = 6126029) B6126029
theorem B283007 : Blo 279826 283007 := bstep (se 1 (by rfl) ⟨212255, by rfl⟩ : syracuseStep 283007 = 424511) B424511
theorem B2183597 : Blo 279826 2183597 := bstep (se 3 (by rfl) ⟨409424, by rfl⟩ : syracuseStep 2183597 = 818849) B818849
theorem B283087 : Blo 279826 283087 := bstep (se 1 (by rfl) ⟨212315, by rfl⟩ : syracuseStep 283087 = 424631) B424631
theorem B3854897 : Blo 279826 3854897 := bstep (se 2 (by rfl) ⟨1445586, by rfl⟩ : syracuseStep 3854897 = 2891173) B2891173
theorem B283239 : Blo 279826 283239 := bstep (se 1 (by rfl) ⟨212429, by rfl⟩ : syracuseStep 283239 = 424859) B424859
theorem B1430297 : Blo 279826 1430297 := bstep (se 2 (by rfl) ⟨536361, by rfl⟩ : syracuseStep 1430297 = 1072723) B1072723
theorem B4051781 : Blo 279826 4051781 := bstep (se 4 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 4051781 = 759709) B759709
theorem B283503 : Blo 279826 283503 := bstep (se 1 (by rfl) ⟨212627, by rfl⟩ : syracuseStep 283503 = 425255) B425255
theorem B316327 : Blo 279826 316327 := bstep (se 1 (by rfl) ⟨237245, by rfl⟩ : syracuseStep 316327 = 474491) B474491
theorem B283559 : Blo 279826 283559 := bstep (se 1 (by rfl) ⟨212669, by rfl⟩ : syracuseStep 283559 = 425339) B425339
theorem B283643 : Blo 279826 283643 := bstep (se 1 (by rfl) ⟨212732, by rfl⟩ : syracuseStep 283643 = 425465) B425465
theorem B676873 : Blo 279826 676873 := bstep (se 2 (by rfl) ⟨253827, by rfl⟩ : syracuseStep 676873 = 507655) B507655
theorem B283711 : Blo 279826 283711 := bstep (se 1 (by rfl) ⟨212783, by rfl⟩ : syracuseStep 283711 = 425567) B425567
theorem B2151521 : Blo 279826 2151521 := bstep (se 2 (by rfl) ⟨806820, by rfl⟩ : syracuseStep 2151521 = 1613641) B1613641
theorem B709843 : Blo 279826 709843 := bstep (se 1 (by rfl) ⟨532382, by rfl⟩ : syracuseStep 709843 = 1064765) B1064765
theorem B808211 : Blo 279826 808211 := bstep (se 1 (by rfl) ⟨606158, by rfl⟩ : syracuseStep 808211 = 1212317) B1212317
theorem B808223 : Blo 279826 808223 := bstep (se 1 (by rfl) ⟨606167, by rfl⟩ : syracuseStep 808223 = 1212335) B1212335
theorem B6051293 : Blo 279826 6051293 := bstep (se 3 (by rfl) ⟨1134617, by rfl⟩ : syracuseStep 6051293 = 2269235) B2269235
theorem B3233267 : Blo 279826 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B4544237 : Blo 279826 4544237 := bstep (se 3 (by rfl) ⟨852044, by rfl⟩ : syracuseStep 4544237 = 1704089) B1704089
theorem B546791 : Blo 279826 546791 := bstep (se 1 (by rfl) ⟨410093, by rfl⟩ : syracuseStep 546791 = 820187) B820187
theorem B1071265 : Blo 279826 1071265 := bstep (se 2 (by rfl) ⟨401724, by rfl⟩ : syracuseStep 1071265 = 803449) B803449
theorem B1431755 : Blo 279826 1431755 := bstep (se 1 (by rfl) ⟨1073816, by rfl⟩ : syracuseStep 1431755 = 2147633) B2147633
theorem B317983 : Blo 279826 317983 := bstep (se 1 (by rfl) ⟨238487, by rfl⟩ : syracuseStep 317983 = 476975) B476975
theorem B1071737 : Blo 279826 1071737 := bstep (se 2 (by rfl) ⟨401901, by rfl⟩ : syracuseStep 1071737 = 803803) B803803
theorem B1202987 : Blo 279826 1202987 := bstep (se 1 (by rfl) ⟨902240, by rfl⟩ : syracuseStep 1202987 = 1804481) B1804481
theorem B908111 : Blo 279826 908111 := bstep (se 1 (by rfl) ⟨681083, by rfl⟩ : syracuseStep 908111 = 1362167) B1362167
theorem B1432403 : Blo 279826 1432403 := bstep (se 1 (by rfl) ⟨1074302, by rfl⟩ : syracuseStep 1432403 = 2148605) B2148605
theorem B449801 : Blo 279826 449801 := bstep (se 2 (by rfl) ⟨168675, by rfl⟩ : syracuseStep 449801 = 337351) B337351
theorem B1990307 : Blo 279826 1990307 := bstep (se 1 (by rfl) ⟨1492730, by rfl⟩ : syracuseStep 1990307 = 2985461) B2985461
theorem B712435 : Blo 279826 712435 := bstep (se 1 (by rfl) ⟨534326, by rfl⟩ : syracuseStep 712435 = 1068653) B1068653
theorem B3203225 : Blo 279826 3203225 := bstep (se 2 (by rfl) ⟨1201209, by rfl⟩ : syracuseStep 3203225 = 2402419) B2402419
theorem B2023643 : Blo 279826 2023643 := bstep (se 1 (by rfl) ⟨1517732, by rfl⟩ : syracuseStep 2023643 = 3035465) B3035465
theorem B6382091 : Blo 279826 6382091 := bstep (se 1 (by rfl) ⟨4786568, by rfl⟩ : syracuseStep 6382091 = 9573137) B9573137
theorem B1434185 : Blo 279826 1434185 := bstep (se 2 (by rfl) ⟨537819, by rfl⟩ : syracuseStep 1434185 = 1075639) B1075639
theorem B713519 : Blo 279826 713519 := bstep (se 1 (by rfl) ⟨535139, by rfl⟩ : syracuseStep 713519 = 1070279) B1070279
theorem B1009313 : Blo 279826 1009313 := bstep (se 2 (by rfl) ⟨378492, by rfl⟩ : syracuseStep 1009313 = 756985) B756985
theorem B1205927 : Blo 279826 1205927 := bstep (se 1 (by rfl) ⟨904445, by rfl⟩ : syracuseStep 1205927 = 1808891) B1808891
theorem B1795769 : Blo 279826 1795769 := bstep (se 2 (by rfl) ⟨673413, by rfl⟩ : syracuseStep 1795769 = 1346827) B1346827
theorem B419783 : Blo 279826 419783 := bstep (se 1 (by rfl) ⟨314837, by rfl⟩ : syracuseStep 419783 = 629675) B629675
theorem B420137 : Blo 279826 420137 := bstep (se 2 (by rfl) ⟨157551, by rfl⟩ : syracuseStep 420137 = 315103) B315103
theorem B420143 : Blo 279826 420143 := bstep (se 1 (by rfl) ⟨315107, by rfl⟩ : syracuseStep 420143 = 630215) B630215
theorem B715169 : Blo 279826 715169 := bstep (se 2 (by rfl) ⟨268188, by rfl⟩ : syracuseStep 715169 = 536377) B536377
theorem B420383 : Blo 279826 420383 := bstep (se 1 (by rfl) ⟨315287, by rfl⟩ : syracuseStep 420383 = 630575) B630575
theorem B1010207 : Blo 279826 1010207 := bstep (se 1 (by rfl) ⟨757655, by rfl⟩ : syracuseStep 1010207 = 1515311) B1515311
theorem B3435047 : Blo 279826 3435047 := bstep (se 1 (by rfl) ⟨2576285, by rfl⟩ : syracuseStep 3435047 = 5152571) B5152571
theorem B4057775 : Blo 279826 4057775 := bstep (se 1 (by rfl) ⟨3043331, by rfl⟩ : syracuseStep 4057775 = 6086663) B6086663
theorem B420767 : Blo 279826 420767 := bstep (se 1 (by rfl) ⟨315575, by rfl⟩ : syracuseStep 420767 = 631151) B631151
theorem B1010627 : Blo 279826 1010627 := bstep (se 1 (by rfl) ⟨757970, by rfl⟩ : syracuseStep 1010627 = 1515941) B1515941
theorem B420815 : Blo 279826 420815 := bstep (se 1 (by rfl) ⟨315611, by rfl⟩ : syracuseStep 420815 = 631223) B631223
theorem B1600519 : Blo 279826 1600519 := bstep (se 1 (by rfl) ⟨1200389, by rfl⟩ : syracuseStep 1600519 = 2400779) B2400779
theorem B420905 : Blo 279826 420905 := bstep (se 2 (by rfl) ⟨157839, by rfl⟩ : syracuseStep 420905 = 315679) B315679
theorem B420911 : Blo 279826 420911 := bstep (se 1 (by rfl) ⟨315683, by rfl⟩ : syracuseStep 420911 = 631367) B631367
theorem B420935 : Blo 279826 420935 := bstep (se 1 (by rfl) ⟨315701, by rfl⟩ : syracuseStep 420935 = 631403) B631403
theorem B715999 : Blo 279826 715999 := bstep (se 1 (by rfl) ⟨536999, by rfl⟩ : syracuseStep 715999 = 1073999) B1073999
theorem B6810911 : Blo 279826 6810911 := bstep (se 1 (by rfl) ⟨5108183, by rfl⟩ : syracuseStep 6810911 = 10216367) B10216367
theorem B3009869 : Blo 279826 3009869 := bstep (se 3 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 3009869 = 1128701) B1128701
theorem B421199 : Blo 279826 421199 := bstep (se 1 (by rfl) ⟨315899, by rfl⟩ : syracuseStep 421199 = 631799) B631799
theorem B716111 : Blo 279826 716111 := bstep (se 1 (by rfl) ⟨537083, by rfl⟩ : syracuseStep 716111 = 1074167) B1074167
theorem B421289 : Blo 279826 421289 := bstep (se 2 (by rfl) ⟨157983, by rfl⟩ : syracuseStep 421289 = 315967) B315967
theorem B421439 : Blo 279826 421439 := bstep (se 1 (by rfl) ⟨316079, by rfl⟩ : syracuseStep 421439 = 632159) B632159
theorem B3862225 : Blo 279826 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B3632849 : Blo 279826 3632849 := bstep (se 2 (by rfl) ⟨1362318, by rfl⟩ : syracuseStep 3632849 = 2724637) B2724637
theorem B421703 : Blo 279826 421703 := bstep (se 1 (by rfl) ⟨316277, by rfl⟩ : syracuseStep 421703 = 632555) B632555
theorem B356167 : Blo 279826 356167 := bstep (se 1 (by rfl) ⟨267125, by rfl⟩ : syracuseStep 356167 = 534251) B534251
theorem B946025 : Blo 279826 946025 := bstep (se 2 (by rfl) ⟨354759, by rfl⟩ : syracuseStep 946025 = 709519) B709519
theorem B421787 : Blo 279826 421787 := bstep (se 1 (by rfl) ⟨316340, by rfl⟩ : syracuseStep 421787 = 632681) B632681
theorem B1961903 : Blo 279826 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B1077371 : Blo 279826 1077371 := bstep (se 1 (by rfl) ⟨808028, by rfl⟩ : syracuseStep 1077371 = 1616057) B1616057
theorem B5435585 : Blo 279826 5435585 := bstep (se 2 (by rfl) ⟨2038344, by rfl⟩ : syracuseStep 5435585 = 4076689) B4076689
theorem B356663 : Blo 279826 356663 := bstep (se 1 (by rfl) ⟨267497, by rfl⟩ : syracuseStep 356663 = 534995) B534995
theorem B422351 : Blo 279826 422351 := bstep (se 1 (by rfl) ⟨316763, by rfl⟩ : syracuseStep 422351 = 633527) B633527
theorem B356815 : Blo 279826 356815 := bstep (se 1 (by rfl) ⟨267611, by rfl⟩ : syracuseStep 356815 = 535223) B535223
theorem B422393 : Blo 279826 422393 := bstep (se 2 (by rfl) ⟨158397, by rfl⟩ : syracuseStep 422393 = 316795) B316795
theorem B422495 : Blo 279826 422495 := bstep (se 1 (by rfl) ⟨316871, by rfl⟩ : syracuseStep 422495 = 633743) B633743
theorem B717407 : Blo 279826 717407 := bstep (se 1 (by rfl) ⟨538055, by rfl⟩ : syracuseStep 717407 = 1076111) B1076111
theorem B422975 : Blo 279826 422975 := bstep (se 1 (by rfl) ⟨317231, by rfl⟩ : syracuseStep 422975 = 634463) B634463
theorem B423017 : Blo 279826 423017 := bstep (se 2 (by rfl) ⟨158631, by rfl⟩ : syracuseStep 423017 = 317263) B317263
theorem B1438859 : Blo 279826 1438859 := bstep (se 1 (by rfl) ⟨1079144, by rfl⟩ : syracuseStep 1438859 = 2158289) B2158289
theorem B947375 : Blo 279826 947375 := bstep (se 1 (by rfl) ⟨710531, by rfl⟩ : syracuseStep 947375 = 1421063) B1421063
theorem B1635527 : Blo 279826 1635527 := bstep (se 1 (by rfl) ⟨1226645, by rfl⟩ : syracuseStep 1635527 = 2453291) B2453291
theorem B423119 : Blo 279826 423119 := bstep (se 1 (by rfl) ⟨317339, by rfl⟩ : syracuseStep 423119 = 634679) B634679
theorem B423323 : Blo 279826 423323 := bstep (se 1 (by rfl) ⟨317492, by rfl⟩ : syracuseStep 423323 = 634985) B634985
theorem B357787 : Blo 279826 357787 := bstep (se 1 (by rfl) ⟨268340, by rfl⟩ : syracuseStep 357787 = 536681) B536681
theorem B423545 : Blo 279826 423545 := bstep (se 2 (by rfl) ⟨158829, by rfl⟩ : syracuseStep 423545 = 317659) B317659
theorem B423647 : Blo 279826 423647 := bstep (se 1 (by rfl) ⟨317735, by rfl⟩ : syracuseStep 423647 = 635471) B635471
theorem B423743 : Blo 279826 423743 := bstep (se 1 (by rfl) ⟨317807, by rfl⟩ : syracuseStep 423743 = 635615) B635615
theorem B423911 : Blo 279826 423911 := bstep (se 1 (by rfl) ⟨317933, by rfl⟩ : syracuseStep 423911 = 635867) B635867
theorem B423929 : Blo 279826 423929 := bstep (se 2 (by rfl) ⟨158973, by rfl⟩ : syracuseStep 423929 = 317947) B317947
theorem B424031 : Blo 279826 424031 := bstep (se 1 (by rfl) ⟨318023, by rfl⟩ : syracuseStep 424031 = 636047) B636047
theorem B424091 : Blo 279826 424091 := bstep (se 1 (by rfl) ⟨318068, by rfl⟩ : syracuseStep 424091 = 636137) B636137
theorem B2717873 : Blo 279826 2717873 := bstep (se 2 (by rfl) ⟨1019202, by rfl⟩ : syracuseStep 2717873 = 2038405) B2038405
theorem B424127 : Blo 279826 424127 := bstep (se 1 (by rfl) ⟨318095, by rfl⟩ : syracuseStep 424127 = 636191) B636191
theorem B424169 : Blo 279826 424169 := bstep (se 2 (by rfl) ⟨159063, by rfl⟩ : syracuseStep 424169 = 318127) B318127
theorem B424475 : Blo 279826 424475 := bstep (se 1 (by rfl) ⟨318356, by rfl⟩ : syracuseStep 424475 = 636713) B636713
theorem B424553 : Blo 279826 424553 := bstep (se 2 (by rfl) ⟨159207, by rfl⟩ : syracuseStep 424553 = 318415) B318415
theorem B1800893 : Blo 279826 1800893 := bstep (se 3 (by rfl) ⟨337667, by rfl⟩ : syracuseStep 1800893 = 675335) B675335
theorem B3046099 : Blo 279826 3046099 := bstep (se 1 (by rfl) ⟨2284574, by rfl⟩ : syracuseStep 3046099 = 4569149) B4569149
theorem B588703 : Blo 279826 588703 := bstep (se 1 (by rfl) ⟨441527, by rfl⟩ : syracuseStep 588703 = 883055) B883055
theorem B949319 : Blo 279826 949319 := bstep (se 1 (by rfl) ⟨711989, by rfl⟩ : syracuseStep 949319 = 1423979) B1423979
theorem B425081 : Blo 279826 425081 := bstep (se 2 (by rfl) ⟨159405, by rfl⟩ : syracuseStep 425081 = 318811) B318811
theorem B949373 : Blo 279826 949373 := bstep (se 3 (by rfl) ⟨178007, by rfl⟩ : syracuseStep 949373 = 356015) B356015
theorem B425183 : Blo 279826 425183 := bstep (se 1 (by rfl) ⟨318887, by rfl⟩ : syracuseStep 425183 = 637775) B637775
theorem B425225 : Blo 279826 425225 := bstep (se 2 (by rfl) ⟨159459, by rfl⟩ : syracuseStep 425225 = 318919) B318919
theorem B1604893 : Blo 279826 1604893 := bstep (se 3 (by rfl) ⟨300917, by rfl⟩ : syracuseStep 1604893 = 601835) B601835
theorem B1637671 : Blo 279826 1637671 := bstep (se 1 (by rfl) ⟨1228253, by rfl⟩ : syracuseStep 1637671 = 2456507) B2456507
theorem B425327 : Blo 279826 425327 := bstep (se 1 (by rfl) ⟨318995, by rfl⟩ : syracuseStep 425327 = 637991) B637991
theorem B1670519 : Blo 279826 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B949643 : Blo 279826 949643 := bstep (se 1 (by rfl) ⟨712232, by rfl⟩ : syracuseStep 949643 = 1424465) B1424465
theorem B425447 : Blo 279826 425447 := bstep (se 1 (by rfl) ⟨319085, by rfl⟩ : syracuseStep 425447 = 638171) B638171
theorem B425579 : Blo 279826 425579 := bstep (se 1 (by rfl) ⟨319184, by rfl⟩ : syracuseStep 425579 = 638369) B638369
theorem B425705 : Blo 279826 425705 := bstep (se 2 (by rfl) ⟨159639, by rfl⟩ : syracuseStep 425705 = 319279) B319279
theorem B2162875 : Blo 279826 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B2752699 : Blo 279826 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B327871 : Blo 279826 327871 := bstep (se 1 (by rfl) ⟨245903, by rfl⟩ : syracuseStep 327871 = 491807) B491807
theorem B1311191 : Blo 279826 1311191 := bstep (se 1 (by rfl) ⟨983393, by rfl⟩ : syracuseStep 1311191 = 1966787) B1966787
theorem B951101 : Blo 279826 951101 := bstep (se 3 (by rfl) ⟨178331, by rfl⟩ : syracuseStep 951101 = 356663) B356663
theorem B16548887 : Blo 279826 16548887 := bstep (se 1 (by rfl) ⟨12411665, by rfl⟩ : syracuseStep 16548887 = 24823331) B24823331
theorem B951803 : Blo 279826 951803 := bstep (se 1 (by rfl) ⟨713852, by rfl⟩ : syracuseStep 951803 = 1427705) B1427705
theorem B1018079 : Blo 279826 1018079 := bstep (se 1 (by rfl) ⟨763559, by rfl⟩ : syracuseStep 1018079 = 1527119) B1527119
theorem B5212511 : Blo 279826 5212511 := bstep (se 1 (by rfl) ⟨3909383, by rfl⟩ : syracuseStep 5212511 = 7818767) B7818767
theorem B4590431 : Blo 279826 4590431 := bstep (se 1 (by rfl) ⟨3442823, by rfl⟩ : syracuseStep 4590431 = 6885647) B6885647
theorem B2722679 : Blo 279826 2722679 := bstep (se 1 (by rfl) ⟨2042009, by rfl⟩ : syracuseStep 2722679 = 4084019) B4084019
theorem B2296745 : Blo 279826 2296745 := bstep (se 2 (by rfl) ⟨861279, by rfl⟩ : syracuseStep 2296745 = 1722559) B1722559
theorem B953531 : Blo 279826 953531 := bstep (se 1 (by rfl) ⟨715148, by rfl⟩ : syracuseStep 953531 = 1430297) B1430297
theorem B2624723 : Blo 279826 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B4034195 : Blo 279826 4034195 := bstep (se 1 (by rfl) ⟨3025646, by rfl⟩ : syracuseStep 4034195 = 6051293) B6051293
theorem B2101115 : Blo 279826 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B1445855 : Blo 279826 1445855 := bstep (se 1 (by rfl) ⟨1084391, by rfl⟩ : syracuseStep 1445855 = 2168783) B2168783
theorem B2134025 : Blo 279826 2134025 := bstep (se 2 (by rfl) ⟨800259, by rfl⟩ : syracuseStep 2134025 = 1600519) B1600519
theorem B954503 : Blo 279826 954503 := bstep (se 1 (by rfl) ⟨715877, by rfl⟩ : syracuseStep 954503 = 1431755) B1431755
theorem B1675453 : Blo 279826 1675453 := bstep (se 3 (by rfl) ⟨314147, by rfl⟩ : syracuseStep 1675453 = 628295) B628295
theorem B954665 : Blo 279826 954665 := bstep (se 2 (by rfl) ⟨357999, by rfl⟩ : syracuseStep 954665 = 715999) B715999
theorem B5640623 : Blo 279826 5640623 := bstep (se 1 (by rfl) ⟨4230467, by rfl⟩ : syracuseStep 5640623 = 8460935) B8460935
theorem B954935 : Blo 279826 954935 := bstep (se 1 (by rfl) ⟨716201, by rfl⟩ : syracuseStep 954935 = 1432403) B1432403
theorem B758585 : Blo 279826 758585 := bstep (se 2 (by rfl) ⟨284469, by rfl⟩ : syracuseStep 758585 = 568939) B568939
theorem B3412813 : Blo 279826 3412813 := bstep (se 3 (by rfl) ⟨639902, by rfl⟩ : syracuseStep 3412813 = 1279805) B1279805
theorem B299867 : Blo 279826 299867 := bstep (se 1 (by rfl) ⟨224900, by rfl⟩ : syracuseStep 299867 = 449801) B449801
theorem B2135483 : Blo 279826 2135483 := bstep (se 1 (by rfl) ⟨1601612, by rfl⟩ : syracuseStep 2135483 = 3203225) B3203225
theorem B1349095 : Blo 279826 1349095 := bstep (se 1 (by rfl) ⟨1011821, by rfl⟩ : syracuseStep 1349095 = 2023643) B2023643
theorem B1807865 : Blo 279826 1807865 := bstep (se 2 (by rfl) ⟨677949, by rfl⟩ : syracuseStep 1807865 = 1355899) B1355899
theorem B956123 : Blo 279826 956123 := bstep (se 1 (by rfl) ⟨717092, by rfl⟩ : syracuseStep 956123 = 1434185) B1434185
theorem B4824521 : Blo 279826 4824521 := bstep (se 2 (by rfl) ⟨1809195, by rfl⟩ : syracuseStep 4824521 = 3618391) B3618391
theorem B2006579 : Blo 279826 2006579 := bstep (se 1 (by rfl) ⟨1504934, by rfl⟩ : syracuseStep 2006579 = 3009869) B3009869
theorem B9117535 : Blo 279826 9117535 := bstep (se 1 (by rfl) ⟨6838151, by rfl⟩ : syracuseStep 9117535 = 13676303) B13676303
theorem B597871 : Blo 279826 597871 := bstep (se 1 (by rfl) ⟨448403, by rfl⟩ : syracuseStep 597871 = 896807) B896807
theorem B630683 : Blo 279826 630683 := bstep (se 1 (by rfl) ⟨473012, by rfl⟩ : syracuseStep 630683 = 946025) B946025
theorem B631097 : Blo 279826 631097 := bstep (se 2 (by rfl) ⟨236661, by rfl⟩ : syracuseStep 631097 = 473323) B473323
theorem B532793 : Blo 279826 532793 := bstep (se 2 (by rfl) ⟨199797, by rfl⟩ : syracuseStep 532793 = 399595) B399595
theorem B598367 : Blo 279826 598367 := bstep (se 1 (by rfl) ⟨448775, by rfl⟩ : syracuseStep 598367 = 897551) B897551
theorem B959239 : Blo 279826 959239 := bstep (se 1 (by rfl) ⟨719429, by rfl⟩ : syracuseStep 959239 = 1438859) B1438859
theorem B631583 : Blo 279826 631583 := bstep (se 1 (by rfl) ⟨473687, by rfl⟩ : syracuseStep 631583 = 947375) B947375
theorem B533279 : Blo 279826 533279 := bstep (se 1 (by rfl) ⟨399959, by rfl⟩ : syracuseStep 533279 = 799919) B799919
theorem B1090351 : Blo 279826 1090351 := bstep (se 1 (by rfl) ⟨817763, by rfl⟩ : syracuseStep 1090351 = 1635527) B1635527
theorem B1811915 : Blo 279826 1811915 := bstep (se 1 (by rfl) ⟨1358936, by rfl⟩ : syracuseStep 1811915 = 2717873) B2717873
theorem B632393 : Blo 279826 632393 := bstep (se 2 (by rfl) ⟨237147, by rfl⟩ : syracuseStep 632393 = 474295) B474295
theorem B2139857 : Blo 279826 2139857 := bstep (se 2 (by rfl) ⟨802446, by rfl⟩ : syracuseStep 2139857 = 1604893) B1604893
theorem B632825 : Blo 279826 632825 := bstep (se 2 (by rfl) ⟨237309, by rfl⟩ : syracuseStep 632825 = 474619) B474619
theorem B632879 : Blo 279826 632879 := bstep (se 1 (by rfl) ⟨474659, by rfl⟩ : syracuseStep 632879 = 949319) B949319
theorem B632915 : Blo 279826 632915 := bstep (se 1 (by rfl) ⟨474686, by rfl⟩ : syracuseStep 632915 = 949373) B949373
theorem B633095 : Blo 279826 633095 := bstep (se 1 (by rfl) ⟨474821, by rfl⟩ : syracuseStep 633095 = 949643) B949643
theorem B633401 : Blo 279826 633401 := bstep (se 2 (by rfl) ⟨237525, by rfl⟩ : syracuseStep 633401 = 475051) B475051
theorem B797663 : Blo 279826 797663 := bstep (se 1 (by rfl) ⟨598247, by rfl⟩ : syracuseStep 797663 = 1196495) B1196495
theorem B7777361 : Blo 279826 7777361 := bstep (se 2 (by rfl) ⟨2916510, by rfl⟩ : syracuseStep 7777361 = 5833021) B5833021
theorem B634121 : Blo 279826 634121 := bstep (se 2 (by rfl) ⟨237795, by rfl⟩ : syracuseStep 634121 = 475591) B475591
theorem B797971 : Blo 279826 797971 := bstep (se 1 (by rfl) ⟨598478, by rfl⟩ : syracuseStep 797971 = 1196957) B1196957
theorem B962441 : Blo 279826 962441 := bstep (se 2 (by rfl) ⟨360915, by rfl⟩ : syracuseStep 962441 = 721831) B721831
theorem B602075 : Blo 279826 602075 := bstep (se 1 (by rfl) ⟨451556, by rfl⟩ : syracuseStep 602075 = 903113) B903113
theorem B17018909 : Blo 279826 17018909 := bstep (se 3 (by rfl) ⟨3191045, by rfl⟩ : syracuseStep 17018909 = 6382091) B6382091
theorem B2142287 : Blo 279826 2142287 := bstep (se 1 (by rfl) ⟨1606715, by rfl⟩ : syracuseStep 2142287 = 3213431) B3213431
theorem B536719 : Blo 279826 536719 := bstep (se 1 (by rfl) ⟨402539, by rfl⟩ : syracuseStep 536719 = 805079) B805079
theorem B635111 : Blo 279826 635111 := bstep (se 1 (by rfl) ⟨476333, by rfl⟩ : syracuseStep 635111 = 952667) B952667
theorem B635291 : Blo 279826 635291 := bstep (se 1 (by rfl) ⟨476468, by rfl⟩ : syracuseStep 635291 = 952937) B952937
theorem B635975 : Blo 279826 635975 := bstep (se 1 (by rfl) ⟨476981, by rfl⟩ : syracuseStep 635975 = 953963) B953963
theorem B636155 : Blo 279826 636155 := bstep (se 1 (by rfl) ⟨477116, by rfl⟩ : syracuseStep 636155 = 954233) B954233
theorem B1848685 : Blo 279826 1848685 := bstep (se 3 (by rfl) ⟨346628, by rfl⟩ : syracuseStep 1848685 = 693257) B693257
theorem B636371 : Blo 279826 636371 := bstep (se 1 (by rfl) ⟨477278, by rfl⟩ : syracuseStep 636371 = 954557) B954557
theorem B505435 : Blo 279826 505435 := bstep (se 1 (by rfl) ⟨379076, by rfl⟩ : syracuseStep 505435 = 758153) B758153
theorem B1455731 : Blo 279826 1455731 := bstep (se 1 (by rfl) ⟨1091798, by rfl⟩ : syracuseStep 1455731 = 2183597) B2183597
theorem B2569931 : Blo 279826 2569931 := bstep (se 1 (by rfl) ⟨1927448, by rfl⟩ : syracuseStep 2569931 = 3854897) B3854897
theorem B636641 : Blo 279826 636641 := bstep (se 2 (by rfl) ⟨238740, by rfl⟩ : syracuseStep 636641 = 477481) B477481
theorem B2701187 : Blo 279826 2701187 := bstep (se 1 (by rfl) ⟨2025890, by rfl⟩ : syracuseStep 2701187 = 4051781) B4051781
theorem B4634657 : Blo 279826 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B2799755 : Blo 279826 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B538807 : Blo 279826 538807 := bstep (se 1 (by rfl) ⟨404105, by rfl⟩ : syracuseStep 538807 = 808211) B808211
theorem B637163 : Blo 279826 637163 := bstep (se 1 (by rfl) ⟨477872, by rfl⟩ : syracuseStep 637163 = 955745) B955745
theorem B1423817 : Blo 279826 1423817 := bstep (se 2 (by rfl) ⟨533931, by rfl⟩ : syracuseStep 1423817 = 1067863) B1067863
theorem B3029491 : Blo 279826 3029491 := bstep (se 1 (by rfl) ⟨2272118, by rfl⟩ : syracuseStep 3029491 = 4544237) B4544237
theorem B1620695 : Blo 279826 1620695 := bstep (se 1 (by rfl) ⟨1215521, by rfl⟩ : syracuseStep 1620695 = 2431043) B2431043
theorem B801991 : Blo 279826 801991 := bstep (se 1 (by rfl) ⟨601493, by rfl⟩ : syracuseStep 801991 = 1202987) B1202987
theorem B605407 : Blo 279826 605407 := bstep (se 1 (by rfl) ⟨454055, by rfl⟩ : syracuseStep 605407 = 908111) B908111
theorem B1621235 : Blo 279826 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B1424627 : Blo 279826 1424627 := bstep (se 1 (by rfl) ⟨1068470, by rfl⟩ : syracuseStep 1424627 = 2136941) B2136941
theorem B638459 : Blo 279826 638459 := bstep (se 1 (by rfl) ⟨478844, by rfl⟩ : syracuseStep 638459 = 957689) B957689
theorem B4505311 : Blo 279826 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B474889 : Blo 279826 474889 := bstep (se 2 (by rfl) ⟨178083, by rfl⟩ : syracuseStep 474889 = 356167) B356167
theorem B1326871 : Blo 279826 1326871 := bstep (se 1 (by rfl) ⟨995153, by rfl⟩ : syracuseStep 1326871 = 1990307) B1990307
theorem B5390225 : Blo 279826 5390225 := bstep (se 2 (by rfl) ⟨2021334, by rfl⟩ : syracuseStep 5390225 = 4042669) B4042669
theorem B1458109 : Blo 279826 1458109 := bstep (se 3 (by rfl) ⟨273395, by rfl⟩ : syracuseStep 1458109 = 546791) B546791
theorem B4571225 : Blo 279826 4571225 := bstep (se 2 (by rfl) ⟨1714209, by rfl⟩ : syracuseStep 4571225 = 3428419) B3428419
theorem B1425599 : Blo 279826 1425599 := bstep (se 1 (by rfl) ⟨1069199, by rfl⟩ : syracuseStep 1425599 = 2138399) B2138399
theorem B475679 : Blo 279826 475679 := bstep (se 1 (by rfl) ⟨356759, by rfl⟩ : syracuseStep 475679 = 713519) B713519
theorem B475753 : Blo 279826 475753 := bstep (se 2 (by rfl) ⟨178407, by rfl⟩ : syracuseStep 475753 = 356815) B356815
theorem B574057 : Blo 279826 574057 := bstep (se 2 (by rfl) ⟨215271, by rfl⟩ : syracuseStep 574057 = 430543) B430543
theorem B2409527 : Blo 279826 2409527 := bstep (se 1 (by rfl) ⟨1807145, by rfl⟩ : syracuseStep 2409527 = 3614291) B3614291
theorem B967735 : Blo 279826 967735 := bstep (se 1 (by rfl) ⟨725801, by rfl⟩ : syracuseStep 967735 = 1451603) B1451603
theorem B672875 : Blo 279826 672875 := bstep (se 1 (by rfl) ⟨504656, by rfl⟩ : syracuseStep 672875 = 1009313) B1009313
theorem B803951 : Blo 279826 803951 := bstep (se 1 (by rfl) ⟨602963, by rfl⟩ : syracuseStep 803951 = 1205927) B1205927
theorem B1197179 : Blo 279826 1197179 := bstep (se 1 (by rfl) ⟨897884, by rfl⟩ : syracuseStep 1197179 = 1795769) B1795769
theorem B279855 : Blo 279826 279855 := bstep (se 1 (by rfl) ⟨209891, by rfl⟩ : syracuseStep 279855 = 419783) B419783
theorem B902497 : Blo 279826 902497 := bstep (se 2 (by rfl) ⟨338436, by rfl⟩ : syracuseStep 902497 = 676873) B676873
theorem B280091 : Blo 279826 280091 := bstep (se 1 (by rfl) ⟨210068, by rfl⟩ : syracuseStep 280091 = 420137) B420137
theorem B280095 : Blo 279826 280095 := bstep (se 1 (by rfl) ⟨210071, by rfl⟩ : syracuseStep 280095 = 420143) B420143
theorem B476779 : Blo 279826 476779 := bstep (se 1 (by rfl) ⟨357584, by rfl⟩ : syracuseStep 476779 = 715169) B715169
theorem B280255 : Blo 279826 280255 := bstep (se 1 (by rfl) ⟨210191, by rfl⟩ : syracuseStep 280255 = 420383) B420383
theorem B673471 : Blo 279826 673471 := bstep (se 1 (by rfl) ⟨505103, by rfl⟩ : syracuseStep 673471 = 1010207) B1010207
theorem B8406773 : Blo 279826 8406773 := bstep (se 5 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 8406773 = 788135) B788135
theorem B2705183 : Blo 279826 2705183 := bstep (se 1 (by rfl) ⟨2028887, by rfl⟩ : syracuseStep 2705183 = 4057775) B4057775
theorem B477049 : Blo 279826 477049 := bstep (se 2 (by rfl) ⟨178893, by rfl⟩ : syracuseStep 477049 = 357787) B357787
theorem B280511 : Blo 279826 280511 := bstep (se 1 (by rfl) ⟨210383, by rfl⟩ : syracuseStep 280511 = 420767) B420767
theorem B673751 : Blo 279826 673751 := bstep (se 1 (by rfl) ⟨505313, by rfl⟩ : syracuseStep 673751 = 1010627) B1010627
theorem B280543 : Blo 279826 280543 := bstep (se 1 (by rfl) ⟨210407, by rfl⟩ : syracuseStep 280543 = 420815) B420815
theorem B280603 : Blo 279826 280603 := bstep (se 1 (by rfl) ⟨210452, by rfl⟩ : syracuseStep 280603 = 420905) B420905
theorem B280607 : Blo 279826 280607 := bstep (se 1 (by rfl) ⟨210455, by rfl⟩ : syracuseStep 280607 = 420911) B420911
theorem B280623 : Blo 279826 280623 := bstep (se 1 (by rfl) ⟨210467, by rfl⟩ : syracuseStep 280623 = 420935) B420935
theorem B4540607 : Blo 279826 4540607 := bstep (se 1 (by rfl) ⟨3405455, by rfl⟩ : syracuseStep 4540607 = 6810911) B6810911
theorem B280799 : Blo 279826 280799 := bstep (se 1 (by rfl) ⟨210599, by rfl⟩ : syracuseStep 280799 = 421199) B421199
theorem B477407 : Blo 279826 477407 := bstep (se 1 (by rfl) ⟨358055, by rfl⟩ : syracuseStep 477407 = 716111) B716111
theorem B280859 : Blo 279826 280859 := bstep (se 1 (by rfl) ⟨210644, by rfl⟩ : syracuseStep 280859 = 421289) B421289
theorem B280959 : Blo 279826 280959 := bstep (se 1 (by rfl) ⟨210719, by rfl⟩ : syracuseStep 280959 = 421439) B421439
theorem B281135 : Blo 279826 281135 := bstep (se 1 (by rfl) ⟨210851, by rfl⟩ : syracuseStep 281135 = 421703) B421703
theorem B281191 : Blo 279826 281191 := bstep (se 1 (by rfl) ⟨210893, by rfl⟩ : syracuseStep 281191 = 421787) B421787
theorem B969337 : Blo 279826 969337 := bstep (se 2 (by rfl) ⟨363501, by rfl⟩ : syracuseStep 969337 = 727003) B727003
theorem B1067681 : Blo 279826 1067681 := bstep (se 2 (by rfl) ⟨400380, by rfl⟩ : syracuseStep 1067681 = 800761) B800761
theorem B3623723 : Blo 279826 3623723 := bstep (se 1 (by rfl) ⟨2717792, by rfl⟩ : syracuseStep 3623723 = 5435585) B5435585
theorem B1428353 : Blo 279826 1428353 := bstep (se 2 (by rfl) ⟨535632, by rfl⟩ : syracuseStep 1428353 = 1071265) B1071265
theorem B281567 : Blo 279826 281567 := bstep (se 1 (by rfl) ⟨211175, by rfl⟩ : syracuseStep 281567 = 422351) B422351
theorem B281595 : Blo 279826 281595 := bstep (se 1 (by rfl) ⟨211196, by rfl⟩ : syracuseStep 281595 = 422393) B422393
theorem B281663 : Blo 279826 281663 := bstep (se 1 (by rfl) ⟨211247, by rfl⟩ : syracuseStep 281663 = 422495) B422495
theorem B478271 : Blo 279826 478271 := bstep (se 1 (by rfl) ⟨358703, by rfl⟩ : syracuseStep 478271 = 717407) B717407
theorem B9817307 : Blo 279826 9817307 := bstep (se 1 (by rfl) ⟨7362980, by rfl⟩ : syracuseStep 9817307 = 14725961) B14725961
theorem B281983 : Blo 279826 281983 := bstep (se 1 (by rfl) ⟨211487, by rfl⟩ : syracuseStep 281983 = 422975) B422975
theorem B282011 : Blo 279826 282011 := bstep (se 1 (by rfl) ⟨211508, by rfl⟩ : syracuseStep 282011 = 423017) B423017
theorem B282079 : Blo 279826 282079 := bstep (se 1 (by rfl) ⟨211559, by rfl⟩ : syracuseStep 282079 = 423119) B423119
theorem B282215 : Blo 279826 282215 := bstep (se 1 (by rfl) ⟨211661, by rfl⟩ : syracuseStep 282215 = 423323) B423323
theorem B1429163 : Blo 279826 1429163 := bstep (se 1 (by rfl) ⟨1071872, by rfl⟩ : syracuseStep 1429163 = 2143745) B2143745
theorem B282363 : Blo 279826 282363 := bstep (se 1 (by rfl) ⟨211772, by rfl⟩ : syracuseStep 282363 = 423545) B423545
theorem B20598533 : Blo 279826 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B282431 : Blo 279826 282431 := bstep (se 1 (by rfl) ⟨211823, by rfl⟩ : syracuseStep 282431 = 423647) B423647
theorem B282495 : Blo 279826 282495 := bstep (se 1 (by rfl) ⟨211871, by rfl⟩ : syracuseStep 282495 = 423743) B423743
theorem B2412503 : Blo 279826 2412503 := bstep (se 1 (by rfl) ⟨1809377, by rfl⟩ : syracuseStep 2412503 = 3618755) B3618755
theorem B282607 : Blo 279826 282607 := bstep (se 1 (by rfl) ⟨211955, by rfl⟩ : syracuseStep 282607 = 423911) B423911
theorem B643067 : Blo 279826 643067 := bstep (se 1 (by rfl) ⟨482300, by rfl⟩ : syracuseStep 643067 = 964601) B964601
theorem B282619 : Blo 279826 282619 := bstep (se 1 (by rfl) ⟨211964, by rfl⟩ : syracuseStep 282619 = 423929) B423929
theorem B282687 : Blo 279826 282687 := bstep (se 1 (by rfl) ⟨212015, by rfl⟩ : syracuseStep 282687 = 424031) B424031
theorem B282727 : Blo 279826 282727 := bstep (se 1 (by rfl) ⟨212045, by rfl⟩ : syracuseStep 282727 = 424091) B424091
theorem B282751 : Blo 279826 282751 := bstep (se 1 (by rfl) ⟨212063, by rfl⟩ : syracuseStep 282751 = 424127) B424127
theorem B282779 : Blo 279826 282779 := bstep (se 1 (by rfl) ⟨212084, by rfl⟩ : syracuseStep 282779 = 424169) B424169
theorem B2281691 : Blo 279826 2281691 := bstep (se 1 (by rfl) ⟨1711268, by rfl⟩ : syracuseStep 2281691 = 3422537) B3422537
theorem B708851 : Blo 279826 708851 := bstep (se 1 (by rfl) ⟨531638, by rfl⟩ : syracuseStep 708851 = 1063277) B1063277
theorem B4837643 : Blo 279826 4837643 := bstep (se 1 (by rfl) ⟨3628232, by rfl⟩ : syracuseStep 4837643 = 7256465) B7256465
theorem B315751 : Blo 279826 315751 := bstep (se 1 (by rfl) ⟨236813, by rfl⟩ : syracuseStep 315751 = 473627) B473627
theorem B282983 : Blo 279826 282983 := bstep (se 1 (by rfl) ⟨212237, by rfl⟩ : syracuseStep 282983 = 424475) B424475
theorem B2183561 : Blo 279826 2183561 := bstep (se 2 (by rfl) ⟨818835, by rfl⟩ : syracuseStep 2183561 = 1637671) B1637671
theorem B283035 : Blo 279826 283035 := bstep (se 1 (by rfl) ⟨212276, by rfl⟩ : syracuseStep 283035 = 424553) B424553
theorem B1200595 : Blo 279826 1200595 := bstep (se 1 (by rfl) ⟨900446, by rfl⟩ : syracuseStep 1200595 = 1800893) B1800893
theorem B2413151 : Blo 279826 2413151 := bstep (se 1 (by rfl) ⟨1809863, by rfl⟩ : syracuseStep 2413151 = 3619727) B3619727
theorem B2151035 : Blo 279826 2151035 := bstep (se 1 (by rfl) ⟨1613276, by rfl⟩ : syracuseStep 2151035 = 3226553) B3226553
theorem B630477553 : Blo 279826 630477553 := bstep (se 2 (by rfl) ⟨236429082, by rfl⟩ : syracuseStep 630477553 = 472858165) B472858165
theorem B283387 : Blo 279826 283387 := bstep (se 1 (by rfl) ⟨212540, by rfl⟩ : syracuseStep 283387 = 425081) B425081
theorem B283455 : Blo 279826 283455 := bstep (se 1 (by rfl) ⟨212591, by rfl⟩ : syracuseStep 283455 = 425183) B425183
theorem B283483 : Blo 279826 283483 := bstep (se 1 (by rfl) ⟨212612, by rfl⟩ : syracuseStep 283483 = 425225) B425225
theorem B283551 : Blo 279826 283551 := bstep (se 1 (by rfl) ⟨212663, by rfl⟩ : syracuseStep 283551 = 425327) B425327
theorem B316399 : Blo 279826 316399 := bstep (se 1 (by rfl) ⟨237299, by rfl⟩ : syracuseStep 316399 = 474599) B474599
theorem B283631 : Blo 279826 283631 := bstep (se 1 (by rfl) ⟨212723, by rfl⟩ : syracuseStep 283631 = 425447) B425447
theorem B283719 : Blo 279826 283719 := bstep (se 1 (by rfl) ⟨212789, by rfl⟩ : syracuseStep 283719 = 425579) B425579
theorem B283803 : Blo 279826 283803 := bstep (se 1 (by rfl) ⟨212852, by rfl⟩ : syracuseStep 283803 = 425705) B425705
theorem B316903 : Blo 279826 316903 := bstep (se 1 (by rfl) ⟨237677, by rfl⟩ : syracuseStep 316903 = 475355) B475355
theorem B2152007 : Blo 279826 2152007 := bstep (se 1 (by rfl) ⟨1614005, by rfl⟩ : syracuseStep 2152007 = 3228011) B3228011
theorem B317083 : Blo 279826 317083 := bstep (se 1 (by rfl) ⟨237812, by rfl⟩ : syracuseStep 317083 = 475625) B475625
theorem B710471 : Blo 279826 710471 := bstep (se 1 (by rfl) ⟨532853, by rfl⟩ : syracuseStep 710471 = 1065707) B1065707
theorem B710491 : Blo 279826 710491 := bstep (se 1 (by rfl) ⟨532868, by rfl⟩ : syracuseStep 710491 = 1065737) B1065737
theorem B1071251 : Blo 279826 1071251 := bstep (se 1 (by rfl) ⟨803438, by rfl⟩ : syracuseStep 1071251 = 1606877) B1606877
theorem B678239 : Blo 279826 678239 := bstep (se 1 (by rfl) ⟨508679, by rfl⟩ : syracuseStep 678239 = 1017359) B1017359
theorem B1431917 : Blo 279826 1431917 := bstep (se 3 (by rfl) ⟨268484, by rfl⟩ : syracuseStep 1431917 = 536969) B536969
theorem B319207 : Blo 279826 319207 := bstep (se 1 (by rfl) ⟨239405, by rfl⟩ : syracuseStep 319207 = 478811) B478811
theorem B1434347 : Blo 279826 1434347 := bstep (se 1 (by rfl) ⟨1075760, by rfl⟩ : syracuseStep 1434347 = 2151521) B2151521
theorem B2155261 : Blo 279826 2155261 := bstep (se 3 (by rfl) ⟨404111, by rfl⟩ : syracuseStep 2155261 = 808223) B808223
theorem B2155511 : Blo 279826 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B714491 : Blo 279826 714491 := bstep (se 1 (by rfl) ⟨535868, by rfl⟩ : syracuseStep 714491 = 1071737) B1071737
theorem B1140635 : Blo 279826 1140635 := bstep (se 1 (by rfl) ⟨855476, by rfl⟩ : syracuseStep 1140635 = 1710953) B1710953
theorem B2287561 : Blo 279826 2287561 := bstep (se 2 (by rfl) ⟨857835, by rfl⟩ : syracuseStep 2287561 = 1715671) B1715671
theorem B419807 : Blo 279826 419807 := bstep (se 1 (by rfl) ⟨314855, by rfl⟩ : syracuseStep 419807 = 629711) B629711
theorem B419819 : Blo 279826 419819 := bstep (se 1 (by rfl) ⟨314864, by rfl⟩ : syracuseStep 419819 = 629729) B629729
theorem B419867 : Blo 279826 419867 := bstep (se 1 (by rfl) ⟨314900, by rfl⟩ : syracuseStep 419867 = 629801) B629801
theorem B420233 : Blo 279826 420233 := bstep (se 2 (by rfl) ⟨157587, by rfl⟩ : syracuseStep 420233 = 315175) B315175
theorem B1600019 : Blo 279826 1600019 := bstep (se 1 (by rfl) ⟨1200014, by rfl⟩ : syracuseStep 1600019 = 2400029) B2400029
theorem B421175 : Blo 279826 421175 := bstep (se 1 (by rfl) ⟨315881, by rfl⟩ : syracuseStep 421175 = 631763) B631763
theorem B421343 : Blo 279826 421343 := bstep (se 1 (by rfl) ⟨316007, by rfl⟩ : syracuseStep 421343 = 632015) B632015
theorem B945755 : Blo 279826 945755 := bstep (se 1 (by rfl) ⟨709316, by rfl⟩ : syracuseStep 945755 = 1418633) B1418633
theorem B421559 : Blo 279826 421559 := bstep (se 1 (by rfl) ⟨316169, by rfl⟩ : syracuseStep 421559 = 632339) B632339
theorem B421769 : Blo 279826 421769 := bstep (se 2 (by rfl) ⟨158163, by rfl⟩ : syracuseStep 421769 = 316327) B316327
theorem B422015 : Blo 279826 422015 := bstep (se 1 (by rfl) ⟨316511, by rfl⟩ : syracuseStep 422015 = 633023) B633023
theorem B946457 : Blo 279826 946457 := bstep (se 2 (by rfl) ⟨354921, by rfl⟩ : syracuseStep 946457 = 709843) B709843
theorem B2290031 : Blo 279826 2290031 := bstep (se 1 (by rfl) ⟨1717523, by rfl⟩ : syracuseStep 2290031 = 3435047) B3435047
theorem B422651 : Blo 279826 422651 := bstep (se 1 (by rfl) ⟨316988, by rfl⟩ : syracuseStep 422651 = 633977) B633977
theorem B2126735 : Blo 279826 2126735 := bstep (se 1 (by rfl) ⟨1595051, by rfl⟩ : syracuseStep 2126735 = 3190103) B3190103
theorem B1209275 : Blo 279826 1209275 := bstep (se 1 (by rfl) ⟨906956, by rfl⟩ : syracuseStep 1209275 = 1813913) B1813913
theorem B2421899 : Blo 279826 2421899 := bstep (se 1 (by rfl) ⟨1816424, by rfl⟩ : syracuseStep 2421899 = 3632849) B3632849
theorem B423095 : Blo 279826 423095 := bstep (se 1 (by rfl) ⟨317321, by rfl⟩ : syracuseStep 423095 = 634643) B634643
theorem B1307935 : Blo 279826 1307935 := bstep (se 1 (by rfl) ⟨980951, by rfl⟩ : syracuseStep 1307935 = 1961903) B1961903
theorem B1602935 : Blo 279826 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B423335 : Blo 279826 423335 := bstep (se 1 (by rfl) ⟨317501, by rfl⟩ : syracuseStep 423335 = 635003) B635003
theorem B718247 : Blo 279826 718247 := bstep (se 1 (by rfl) ⟨538685, by rfl⟩ : syracuseStep 718247 = 1077371) B1077371
theorem B423515 : Blo 279826 423515 := bstep (se 1 (by rfl) ⟨317636, by rfl⟩ : syracuseStep 423515 = 635273) B635273
theorem B947807 : Blo 279826 947807 := bstep (se 1 (by rfl) ⟨710855, by rfl⟩ : syracuseStep 947807 = 1421711) B1421711
theorem B1603435 : Blo 279826 1603435 := bstep (se 1 (by rfl) ⟨1202576, by rfl⟩ : syracuseStep 1603435 = 2405153) B2405153
theorem B423977 : Blo 279826 423977 := bstep (se 2 (by rfl) ⟨158991, by rfl⟩ : syracuseStep 423977 = 317983) B317983
theorem B424007 : Blo 279826 424007 := bstep (se 1 (by rfl) ⟨318005, by rfl⟩ : syracuseStep 424007 = 636011) B636011
theorem B1013971 : Blo 279826 1013971 := bstep (se 1 (by rfl) ⟨760478, by rfl⟩ : syracuseStep 1013971 = 1520957) B1520957
theorem B4061465 : Blo 279826 4061465 := bstep (se 2 (by rfl) ⟨1523049, by rfl⟩ : syracuseStep 4061465 = 3046099) B3046099
theorem B424391 : Blo 279826 424391 := bstep (se 1 (by rfl) ⟨318293, by rfl⟩ : syracuseStep 424391 = 636587) B636587
theorem B784937 : Blo 279826 784937 := bstep (se 2 (by rfl) ⟨294351, by rfl⟩ : syracuseStep 784937 = 588703) B588703
theorem B424607 : Blo 279826 424607 := bstep (se 1 (by rfl) ⟨318455, by rfl⟩ : syracuseStep 424607 = 636911) B636911
theorem B424751 : Blo 279826 424751 := bstep (se 1 (by rfl) ⟨318563, by rfl⟩ : syracuseStep 424751 = 637127) B637127
theorem B424871 : Blo 279826 424871 := bstep (se 1 (by rfl) ⟨318653, by rfl⟩ : syracuseStep 424871 = 637307) B637307
theorem B425051 : Blo 279826 425051 := bstep (se 1 (by rfl) ⟨318788, by rfl⟩ : syracuseStep 425051 = 637577) B637577
theorem B425423 : Blo 279826 425423 := bstep (se 1 (by rfl) ⟨319067, by rfl⟩ : syracuseStep 425423 = 638135) B638135
theorem B1113679 : Blo 279826 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B3636845 : Blo 279826 3636845 := bstep (se 3 (by rfl) ⟨681908, by rfl⟩ : syracuseStep 3636845 = 1363817) B1363817
theorem B949913 : Blo 279826 949913 := bstep (se 2 (by rfl) ⟨356217, by rfl⟩ : syracuseStep 949913 = 712435) B712435
theorem B2129651 : Blo 279826 2129651 := bstep (se 1 (by rfl) ⟨1597238, by rfl⟩ : syracuseStep 2129651 = 3194477) B3194477
theorem B3047483 : Blo 279826 3047483 := bstep (se 1 (by rfl) ⟨2285612, by rfl⟩ : syracuseStep 3047483 = 4571225) B4571225
theorem B950399 : Blo 279826 950399 := bstep (se 1 (by rfl) ⟨712799, by rfl⟩ : syracuseStep 950399 = 1425599) B1425599
theorem B2883833 : Blo 279826 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B3670265 : Blo 279826 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B1606351 : Blo 279826 1606351 := bstep (se 1 (by rfl) ⟨1204763, by rfl⟩ : syracuseStep 1606351 = 2409527) B2409527
theorem B1278985 : Blo 279826 1278985 := bstep (se 2 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 1278985 = 959239) B959239
theorem B5604515 : Blo 279826 5604515 := bstep (se 1 (by rfl) ⟨4203386, by rfl⟩ : syracuseStep 5604515 = 8406773) B8406773
theorem B1803455 : Blo 279826 1803455 := bstep (se 1 (by rfl) ⟨1352591, by rfl⟩ : syracuseStep 1803455 = 2705183) B2705183
theorem B3475007 : Blo 279826 3475007 := bstep (se 1 (by rfl) ⟨2606255, by rfl⟩ : syracuseStep 3475007 = 5212511) B5212511
theorem B952235 : Blo 279826 952235 := bstep (se 1 (by rfl) ⟨714176, by rfl⟩ : syracuseStep 952235 = 1428353) B1428353
theorem B2689463 : Blo 279826 2689463 := bstep (se 1 (by rfl) ⟨2017097, by rfl⟩ : syracuseStep 2689463 = 4034195) B4034195
theorem B952775 : Blo 279826 952775 := bstep (se 1 (by rfl) ⟨714581, by rfl⟩ : syracuseStep 952775 = 1429163) B1429163
theorem B13732355 : Blo 279826 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B3050081 : Blo 279826 3050081 := bstep (se 2 (by rfl) ⟨1143780, by rfl⟩ : syracuseStep 3050081 = 2287561) B2287561
theorem B1608335 : Blo 279826 1608335 := bstep (se 1 (by rfl) ⟨1206251, by rfl⟩ : syracuseStep 1608335 = 2412503) B2412503
theorem B428711 : Blo 279826 428711 := bstep (se 1 (by rfl) ⟨321533, by rfl⟩ : syracuseStep 428711 = 643067) B643067
theorem B1608767 : Blo 279826 1608767 := bstep (se 1 (by rfl) ⟨1206575, by rfl⟩ : syracuseStep 1608767 = 2413151) B2413151
theorem B954611 : Blo 279826 954611 := bstep (se 1 (by rfl) ⟨715958, by rfl⟩ : syracuseStep 954611 = 1431917) B1431917
theorem B3216347 : Blo 279826 3216347 := bstep (se 1 (by rfl) ⟨2412260, by rfl⟩ : syracuseStep 3216347 = 4824521) B4824521
theorem B2233937 : Blo 279826 2233937 := bstep (se 2 (by rfl) ⟨837726, by rfl⟩ : syracuseStep 2233937 = 1675453) B1675453
theorem B956231 : Blo 279826 956231 := bstep (se 1 (by rfl) ⟨717173, by rfl⟩ : syracuseStep 956231 = 1434347) B1434347
theorem B840636737 : Blo 279826 840636737 := bstep (se 2 (by rfl) ⟨315238776, by rfl⟩ : syracuseStep 840636737 = 630477553) B630477553
theorem B760423 : Blo 279826 760423 := bstep (se 1 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 760423 = 1140635) B1140635
theorem B1743913 : Blo 279826 1743913 := bstep (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) B1307935
theorem B2464913 : Blo 279826 2464913 := bstep (se 2 (by rfl) ⟨924342, by rfl⟩ : syracuseStep 2464913 = 1848685) B1848685
theorem B531775 : Blo 279826 531775 := bstep (se 1 (by rfl) ⟨398831, by rfl⟩ : syracuseStep 531775 = 797663) B797663
theorem B630503 : Blo 279826 630503 := bstep (se 1 (by rfl) ⟨472877, by rfl⟩ : syracuseStep 630503 = 945755) B945755
theorem B2137913 : Blo 279826 2137913 := bstep (se 2 (by rfl) ⟨801717, by rfl⟩ : syracuseStep 2137913 = 1603435) B1603435
theorem B401383 : Blo 279826 401383 := bstep (se 1 (by rfl) ⟨301037, by rfl⟩ : syracuseStep 401383 = 602075) B602075
theorem B11345939 : Blo 279826 11345939 := bstep (se 1 (by rfl) ⟨8509454, by rfl⟩ : syracuseStep 11345939 = 17018909) B17018909
theorem B630971 : Blo 279826 630971 := bstep (se 1 (by rfl) ⟨473228, by rfl⟩ : syracuseStep 630971 = 946457) B946457
theorem B1351961 : Blo 279826 1351961 := bstep (se 2 (by rfl) ⟨506985, by rfl⟩ : syracuseStep 1351961 = 1013971) B1013971
theorem B1417823 : Blo 279826 1417823 := bstep (se 1 (by rfl) ⟨1063367, by rfl⟩ : syracuseStep 1417823 = 2126735) B2126735
theorem B4039321 : Blo 279826 4039321 := bstep (se 2 (by rfl) ⟨1514745, by rfl⟩ : syracuseStep 4039321 = 3029491) B3029491
theorem B1614599 : Blo 279826 1614599 := bstep (se 1 (by rfl) ⟨1210949, by rfl⟩ : syracuseStep 1614599 = 2421899) B2421899
theorem B631871 : Blo 279826 631871 := bstep (se 1 (by rfl) ⟨473903, by rfl⟩ : syracuseStep 631871 = 947807) B947807
theorem B1713287 : Blo 279826 1713287 := bstep (se 1 (by rfl) ⟨1284965, by rfl⟩ : syracuseStep 1713287 = 2569931) B2569931
theorem B3089771 : Blo 279826 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B3188645 : Blo 279826 3188645 := bstep (se 4 (by rfl) ⟨298935, by rfl⟩ : syracuseStep 3188645 = 597871) B597871
theorem B1484905 : Blo 279826 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B6007081 : Blo 279826 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B633185 : Blo 279826 633185 := bstep (se 2 (by rfl) ⟨237444, by rfl⟩ : syracuseStep 633185 = 474889) B474889
theorem B633275 : Blo 279826 633275 := bstep (se 1 (by rfl) ⟨474956, by rfl⟩ : syracuseStep 633275 = 949913) B949913
theorem B1419767 : Blo 279826 1419767 := bstep (se 1 (by rfl) ⟨1064825, by rfl⟩ : syracuseStep 1419767 = 2129651) B2129651
theorem B1944145 : Blo 279826 1944145 := bstep (se 2 (by rfl) ⟨729054, by rfl⟩ : syracuseStep 1944145 = 1458109) B1458109
theorem B634067 : Blo 279826 634067 := bstep (se 1 (by rfl) ⟨475550, by rfl⟩ : syracuseStep 634067 = 951101) B951101
theorem B535967 : Blo 279826 535967 := bstep (se 1 (by rfl) ⟨401975, by rfl⟩ : syracuseStep 535967 = 803951) B803951
theorem B798119 : Blo 279826 798119 := bstep (se 1 (by rfl) ⟨598589, by rfl⟩ : syracuseStep 798119 = 1197179) B1197179
theorem B634337 : Blo 279826 634337 := bstep (se 2 (by rfl) ⟨237876, by rfl⟩ : syracuseStep 634337 = 475753) B475753
theorem B765409 : Blo 279826 765409 := bstep (se 2 (by rfl) ⟨287028, by rfl⟩ : syracuseStep 765409 = 574057) B574057
theorem B1748645 : Blo 279826 1748645 := bstep (se 4 (by rfl) ⟨163935, by rfl⟩ : syracuseStep 1748645 = 327871) B327871
theorem B634535 : Blo 279826 634535 := bstep (se 1 (by rfl) ⟨475901, by rfl⟩ : syracuseStep 634535 = 951803) B951803
theorem B1453801 : Blo 279826 1453801 := bstep (se 2 (by rfl) ⟨545175, by rfl⟩ : syracuseStep 1453801 = 1090351) B1090351
theorem B1290313 : Blo 279826 1290313 := bstep (se 2 (by rfl) ⟨483867, by rfl⟩ : syracuseStep 1290313 = 967735) B967735
theorem B3027071 : Blo 279826 3027071 := bstep (se 1 (by rfl) ⟨2270303, by rfl⟩ : syracuseStep 3027071 = 4540607) B4540607
theorem B3060287 : Blo 279826 3060287 := bstep (se 1 (by rfl) ⟨2295215, by rfl⟩ : syracuseStep 3060287 = 4590431) B4590431
theorem B1815119 : Blo 279826 1815119 := bstep (se 1 (by rfl) ⟨1361339, by rfl⟩ : syracuseStep 1815119 = 2722679) B2722679
theorem B635687 : Blo 279826 635687 := bstep (se 1 (by rfl) ⟨476765, by rfl⟩ : syracuseStep 635687 = 953531) B953531
theorem B1749815 : Blo 279826 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B635705 : Blo 279826 635705 := bstep (se 2 (by rfl) ⟨238389, by rfl⟩ : syracuseStep 635705 = 476779) B476779
theorem B799645 : Blo 279826 799645 := bstep (se 3 (by rfl) ⟨149933, by rfl⟩ : syracuseStep 799645 = 299867) B299867
theorem B897961 : Blo 279826 897961 := bstep (se 2 (by rfl) ⟨336735, by rfl⟩ : syracuseStep 897961 = 673471) B673471
theorem B636065 : Blo 279826 636065 := bstep (se 2 (by rfl) ⟨238524, by rfl⟩ : syracuseStep 636065 = 477049) B477049
theorem B5748029 : Blo 279826 5748029 := bstep (se 3 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 5748029 = 2155511) B2155511
theorem B1422683 : Blo 279826 1422683 := bstep (se 1 (by rfl) ⟨1067012, by rfl⟩ : syracuseStep 1422683 = 2134025) B2134025
theorem B636335 : Blo 279826 636335 := bstep (se 1 (by rfl) ⟨477251, by rfl⟩ : syracuseStep 636335 = 954503) B954503
theorem B1521127 : Blo 279826 1521127 := bstep (se 1 (by rfl) ⟨1140845, by rfl⟩ : syracuseStep 1521127 = 2281691) B2281691
theorem B472567 : Blo 279826 472567 := bstep (se 1 (by rfl) ⟨354425, by rfl⟩ : syracuseStep 472567 = 708851) B708851
theorem B3225095 : Blo 279826 3225095 := bstep (se 1 (by rfl) ⟨2418821, by rfl⟩ : syracuseStep 3225095 = 4837643) B4837643
theorem B636443 : Blo 279826 636443 := bstep (se 1 (by rfl) ⟨477332, by rfl⟩ : syracuseStep 636443 = 954665) B954665
theorem B1455707 : Blo 279826 1455707 := bstep (se 1 (by rfl) ⟨1091780, by rfl⟩ : syracuseStep 1455707 = 2183561) B2183561
theorem B636623 : Blo 279826 636623 := bstep (se 1 (by rfl) ⟨477467, by rfl⟩ : syracuseStep 636623 = 954935) B954935
theorem B1292449 : Blo 279826 1292449 := bstep (se 2 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 1292449 = 969337) B969337
theorem B1423655 : Blo 279826 1423655 := bstep (se 1 (by rfl) ⟨1067741, by rfl⟩ : syracuseStep 1423655 = 2135483) B2135483
theorem B637415 : Blo 279826 637415 := bstep (se 1 (by rfl) ⟨478061, by rfl⟩ : syracuseStep 637415 = 956123) B956123
theorem B473647 : Blo 279826 473647 := bstep (se 1 (by rfl) ⟨355235, by rfl⟩ : syracuseStep 473647 = 710471) B710471
theorem B1063961 : Blo 279826 1063961 := bstep (se 2 (by rfl) ⟨398985, by rfl⟩ : syracuseStep 1063961 = 797971) B797971
theorem B1426571 : Blo 279826 1426571 := bstep (se 1 (by rfl) ⟨1069928, by rfl⟩ : syracuseStep 1426571 = 2139857) B2139857
theorem B476327 : Blo 279826 476327 := bstep (se 1 (by rfl) ⟨357245, by rfl⟩ : syracuseStep 476327 = 714491) B714491
theorem B279871 : Blo 279826 279871 := bstep (se 1 (by rfl) ⟨209903, by rfl⟩ : syracuseStep 279871 = 419807) B419807
theorem B279879 : Blo 279826 279879 := bstep (se 1 (by rfl) ⟨209909, by rfl⟩ : syracuseStep 279879 = 419819) B419819
theorem B279911 : Blo 279826 279911 := bstep (se 1 (by rfl) ⟨209933, by rfl⟩ : syracuseStep 279911 = 419867) B419867
theorem B280155 : Blo 279826 280155 := bstep (se 1 (by rfl) ⟨210116, by rfl⟩ : syracuseStep 280155 = 420233) B420233
theorem B1066679 : Blo 279826 1066679 := bstep (se 1 (by rfl) ⟨800009, by rfl⟩ : syracuseStep 1066679 = 1600019) B1600019
theorem B673913 : Blo 279826 673913 := bstep (se 2 (by rfl) ⟨252717, by rfl⟩ : syracuseStep 673913 = 505435) B505435
theorem B280783 : Blo 279826 280783 := bstep (se 1 (by rfl) ⟨210587, by rfl⟩ : syracuseStep 280783 = 421175) B421175
theorem B280895 : Blo 279826 280895 := bstep (se 1 (by rfl) ⟨210671, by rfl⟩ : syracuseStep 280895 = 421343) B421343
theorem B281039 : Blo 279826 281039 := bstep (se 1 (by rfl) ⟨210779, by rfl⟩ : syracuseStep 281039 = 421559) B421559
theorem B281179 : Blo 279826 281179 := bstep (se 1 (by rfl) ⟨210884, by rfl⟩ : syracuseStep 281179 = 421769) B421769
theorem B641627 : Blo 279826 641627 := bstep (se 1 (by rfl) ⟨481220, by rfl⟩ : syracuseStep 641627 = 962441) B962441
theorem B1428191 : Blo 279826 1428191 := bstep (se 1 (by rfl) ⟨1071143, by rfl⟩ : syracuseStep 1428191 = 2142287) B2142287
theorem B281343 : Blo 279826 281343 := bstep (se 1 (by rfl) ⟨211007, by rfl⟩ : syracuseStep 281343 = 422015) B422015
theorem B1526687 : Blo 279826 1526687 := bstep (se 1 (by rfl) ⟨1145015, by rfl⟩ : syracuseStep 1526687 = 2290031) B2290031
theorem B281767 : Blo 279826 281767 := bstep (se 1 (by rfl) ⟨211325, by rfl⟩ : syracuseStep 281767 = 422651) B422651
theorem B806183 : Blo 279826 806183 := bstep (se 1 (by rfl) ⟨604637, by rfl⟩ : syracuseStep 806183 = 1209275) B1209275
theorem B282063 : Blo 279826 282063 := bstep (se 1 (by rfl) ⟨211547, by rfl⟩ : syracuseStep 282063 = 423095) B423095
theorem B1068623 : Blo 279826 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B282223 : Blo 279826 282223 := bstep (se 1 (by rfl) ⟨211667, by rfl⟩ : syracuseStep 282223 = 423335) B423335
theorem B478831 : Blo 279826 478831 := bstep (se 1 (by rfl) ⟨359123, by rfl⟩ : syracuseStep 478831 = 718247) B718247
theorem B282343 : Blo 279826 282343 := bstep (se 1 (by rfl) ⟨211757, by rfl⟩ : syracuseStep 282343 = 423515) B423515
theorem B970487 : Blo 279826 970487 := bstep (se 1 (by rfl) ⟨727865, by rfl⟩ : syracuseStep 970487 = 1455731) B1455731
theorem B282651 : Blo 279826 282651 := bstep (se 1 (by rfl) ⟨211988, by rfl⟩ : syracuseStep 282651 = 423977) B423977
theorem B282671 : Blo 279826 282671 := bstep (se 1 (by rfl) ⟨212003, by rfl⟩ : syracuseStep 282671 = 424007) B424007
theorem B2707643 : Blo 279826 2707643 := bstep (se 1 (by rfl) ⟨2030732, by rfl⟩ : syracuseStep 2707643 = 4061465) B4061465
theorem B1069321 : Blo 279826 1069321 := bstep (se 2 (by rfl) ⟨400995, by rfl⟩ : syracuseStep 1069321 = 801991) B801991
theorem B807209 : Blo 279826 807209 := bstep (se 2 (by rfl) ⟨302703, by rfl⟩ : syracuseStep 807209 = 605407) B605407
theorem B282927 : Blo 279826 282927 := bstep (se 1 (by rfl) ⟨212195, by rfl⟩ : syracuseStep 282927 = 424391) B424391
theorem B283071 : Blo 279826 283071 := bstep (se 1 (by rfl) ⟨212303, by rfl⟩ : syracuseStep 283071 = 424607) B424607
theorem B283167 : Blo 279826 283167 := bstep (se 1 (by rfl) ⟨212375, by rfl⟩ : syracuseStep 283167 = 424751) B424751
theorem B283247 : Blo 279826 283247 := bstep (se 1 (by rfl) ⟨212435, by rfl⟩ : syracuseStep 283247 = 424871) B424871
theorem B283367 : Blo 279826 283367 := bstep (se 1 (by rfl) ⟨212525, by rfl⟩ : syracuseStep 283367 = 425051) B425051
theorem B283615 : Blo 279826 283615 := bstep (se 1 (by rfl) ⟨212711, by rfl⟩ : syracuseStep 283615 = 425423) B425423
theorem B3855613 : Blo 279826 3855613 := bstep (se 3 (by rfl) ⟨722927, by rfl⟩ : syracuseStep 3855613 = 1445855) B1445855
theorem B3593483 : Blo 279826 3593483 := bstep (se 1 (by rfl) ⟨2695112, by rfl⟩ : syracuseStep 3593483 = 5390225) B5390225
theorem B874127 : Blo 279826 874127 := bstep (se 1 (by rfl) ⟨655595, by rfl⟩ : syracuseStep 874127 = 1311191) B1311191
theorem B317119 : Blo 279826 317119 := bstep (se 1 (by rfl) ⟨237839, by rfl⟩ : syracuseStep 317119 = 475679) B475679
theorem B448583 : Blo 279826 448583 := bstep (se 1 (by rfl) ⟨336437, by rfl⟩ : syracuseStep 448583 = 672875) B672875
theorem B1595645 : Blo 279826 1595645 := bstep (se 3 (by rfl) ⟨299183, by rfl⟩ : syracuseStep 1595645 = 598367) B598367
theorem B2873681 : Blo 279826 2873681 := bstep (se 2 (by rfl) ⟨1077630, by rfl⟩ : syracuseStep 2873681 = 2155261) B2155261
theorem B449167 : Blo 279826 449167 := bstep (se 1 (by rfl) ⟨336875, by rfl⟩ : syracuseStep 449167 = 673751) B673751
theorem B678719 : Blo 279826 678719 := bstep (se 1 (by rfl) ⟨509039, by rfl⟩ : syracuseStep 678719 = 1018079) B1018079
theorem B318271 : Blo 279826 318271 := bstep (se 1 (by rfl) ⟨238703, by rfl⟩ : syracuseStep 318271 = 477407) B477407
theorem B711787 : Blo 279826 711787 := bstep (se 1 (by rfl) ⟨533840, by rfl⟩ : syracuseStep 711787 = 1067681) B1067681
theorem B1203329 : Blo 279826 1203329 := bstep (se 2 (by rfl) ⟨451248, by rfl⟩ : syracuseStep 1203329 = 902497) B902497
theorem B2415815 : Blo 279826 2415815 := bstep (se 1 (by rfl) ⟨1811861, by rfl⟩ : syracuseStep 2415815 = 3623723) B3623723
theorem B1531163 : Blo 279826 1531163 := bstep (se 1 (by rfl) ⟨1148372, by rfl⟩ : syracuseStep 1531163 = 2296745) B2296745
theorem B318847 : Blo 279826 318847 := bstep (se 1 (by rfl) ⟨239135, by rfl⟩ : syracuseStep 318847 = 478271) B478271
theorem B6544871 : Blo 279826 6544871 := bstep (se 1 (by rfl) ⟨4908653, by rfl⟩ : syracuseStep 6544871 = 9817307) B9817307
theorem B2022893 : Blo 279826 2022893 := bstep (se 3 (by rfl) ⟨379292, by rfl⟩ : syracuseStep 2022893 = 758585) B758585
theorem B1400743 : Blo 279826 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B44130365 : Blo 279826 44130365 := bstep (se 3 (by rfl) ⟨8274443, by rfl⟩ : syracuseStep 44130365 = 16548887) B16548887
theorem B3760415 : Blo 279826 3760415 := bstep (se 1 (by rfl) ⟨2820311, by rfl⟩ : syracuseStep 3760415 = 5640623) B5640623
theorem B1434023 : Blo 279826 1434023 := bstep (se 1 (by rfl) ⟨1075517, by rfl⟩ : syracuseStep 1434023 = 2151035) B2151035
theorem B1205243 : Blo 279826 1205243 := bstep (se 1 (by rfl) ⟨903932, by rfl⟩ : syracuseStep 1205243 = 1807865) B1807865
theorem B1434671 : Blo 279826 1434671 := bstep (se 1 (by rfl) ⟨1076003, by rfl⟩ : syracuseStep 1434671 = 2152007) B2152007
theorem B714167 : Blo 279826 714167 := bstep (se 1 (by rfl) ⟨535625, by rfl⟩ : syracuseStep 714167 = 1071251) B1071251
theorem B452159 : Blo 279826 452159 := bstep (se 1 (by rfl) ⟨339119, by rfl⟩ : syracuseStep 452159 = 678239) B678239
theorem B1337719 : Blo 279826 1337719 := bstep (se 1 (by rfl) ⟨1003289, by rfl⟩ : syracuseStep 1337719 = 2006579) B2006579
theorem B420455 : Blo 279826 420455 := bstep (se 1 (by rfl) ⟨315341, by rfl⟩ : syracuseStep 420455 = 630683) B630683
theorem B715625 : Blo 279826 715625 := bstep (se 2 (by rfl) ⟨268359, by rfl⟩ : syracuseStep 715625 = 536719) B536719
theorem B420731 : Blo 279826 420731 := bstep (se 1 (by rfl) ⟨315548, by rfl⟩ : syracuseStep 420731 = 631097) B631097
theorem B355195 : Blo 279826 355195 := bstep (se 1 (by rfl) ⟨266396, by rfl⟩ : syracuseStep 355195 = 532793) B532793
theorem B421001 : Blo 279826 421001 := bstep (se 2 (by rfl) ⟨157875, by rfl⟩ : syracuseStep 421001 = 315751) B315751
theorem B421055 : Blo 279826 421055 := bstep (se 1 (by rfl) ⟨315791, by rfl⟩ : syracuseStep 421055 = 631583) B631583
theorem B355519 : Blo 279826 355519 := bstep (se 1 (by rfl) ⟨266639, by rfl⟩ : syracuseStep 355519 = 533279) B533279
theorem B1600793 : Blo 279826 1600793 := bstep (se 2 (by rfl) ⟨600297, by rfl⟩ : syracuseStep 1600793 = 1200595) B1200595
theorem B1207943 : Blo 279826 1207943 := bstep (se 1 (by rfl) ⟨905957, by rfl⟩ : syracuseStep 1207943 = 1811915) B1811915
theorem B421595 : Blo 279826 421595 := bstep (se 1 (by rfl) ⟨316196, by rfl⟩ : syracuseStep 421595 = 632393) B632393
theorem B4550417 : Blo 279826 4550417 := bstep (se 2 (by rfl) ⟨1706406, by rfl⟩ : syracuseStep 4550417 = 3412813) B3412813
theorem B421865 : Blo 279826 421865 := bstep (se 2 (by rfl) ⟨158199, by rfl⟩ : syracuseStep 421865 = 316399) B316399
theorem B421883 : Blo 279826 421883 := bstep (se 1 (by rfl) ⟨316412, by rfl⟩ : syracuseStep 421883 = 632825) B632825
theorem B421919 : Blo 279826 421919 := bstep (se 1 (by rfl) ⟨316439, by rfl⟩ : syracuseStep 421919 = 632879) B632879
theorem B421943 : Blo 279826 421943 := bstep (se 1 (by rfl) ⟨316457, by rfl⟩ : syracuseStep 421943 = 632915) B632915
theorem B2093165 : Blo 279826 2093165 := bstep (se 3 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 2093165 = 784937) B784937
theorem B422063 : Blo 279826 422063 := bstep (se 1 (by rfl) ⟨316547, by rfl⟩ : syracuseStep 422063 = 633095) B633095
theorem B422267 : Blo 279826 422267 := bstep (se 1 (by rfl) ⟨316700, by rfl⟩ : syracuseStep 422267 = 633401) B633401
theorem B1798793 : Blo 279826 1798793 := bstep (se 2 (by rfl) ⟨674547, by rfl⟩ : syracuseStep 1798793 = 1349095) B1349095
theorem B422537 : Blo 279826 422537 := bstep (se 2 (by rfl) ⟨158451, by rfl⟩ : syracuseStep 422537 = 316903) B316903
theorem B422747 : Blo 279826 422747 := bstep (se 1 (by rfl) ⟨317060, by rfl⟩ : syracuseStep 422747 = 634121) B634121
theorem B422777 : Blo 279826 422777 := bstep (se 2 (by rfl) ⟨158541, by rfl⟩ : syracuseStep 422777 = 317083) B317083
theorem B947321 : Blo 279826 947321 := bstep (se 2 (by rfl) ⟨355245, by rfl⟩ : syracuseStep 947321 = 710491) B710491
theorem B423407 : Blo 279826 423407 := bstep (se 1 (by rfl) ⟨317555, by rfl⟩ : syracuseStep 423407 = 635111) B635111
theorem B20739629 : Blo 279826 20739629 := bstep (se 3 (by rfl) ⟨3888680, by rfl⟩ : syracuseStep 20739629 = 7777361) B7777361
theorem B718409 : Blo 279826 718409 := bstep (se 2 (by rfl) ⟨269403, by rfl⟩ : syracuseStep 718409 = 538807) B538807
theorem B423527 : Blo 279826 423527 := bstep (se 1 (by rfl) ⟨317645, by rfl⟩ : syracuseStep 423527 = 635291) B635291
theorem B423983 : Blo 279826 423983 := bstep (se 1 (by rfl) ⟨317987, by rfl⟩ : syracuseStep 423983 = 635975) B635975
theorem B424103 : Blo 279826 424103 := bstep (se 1 (by rfl) ⟨318077, by rfl⟩ : syracuseStep 424103 = 636155) B636155
theorem B424247 : Blo 279826 424247 := bstep (se 1 (by rfl) ⟨318185, by rfl⟩ : syracuseStep 424247 = 636371) B636371
theorem B424427 : Blo 279826 424427 := bstep (se 1 (by rfl) ⟨318320, by rfl⟩ : syracuseStep 424427 = 636641) B636641
theorem B1800791 : Blo 279826 1800791 := bstep (se 1 (by rfl) ⟨1350593, by rfl⟩ : syracuseStep 1800791 = 2701187) B2701187
theorem B1866503 : Blo 279826 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B424775 : Blo 279826 424775 := bstep (se 1 (by rfl) ⟨318581, by rfl⟩ : syracuseStep 424775 = 637163) B637163
theorem B949211 : Blo 279826 949211 := bstep (se 1 (by rfl) ⟨711908, by rfl⟩ : syracuseStep 949211 = 1423817) B1423817
theorem B1080463 : Blo 279826 1080463 := bstep (se 1 (by rfl) ⟨810347, by rfl⟩ : syracuseStep 1080463 = 1620695) B1620695
theorem B1080823 : Blo 279826 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B949751 : Blo 279826 949751 := bstep (se 1 (by rfl) ⟨712313, by rfl⟩ : syracuseStep 949751 = 1424627) B1424627
theorem B425609 : Blo 279826 425609 := bstep (se 2 (by rfl) ⟨159603, by rfl⟩ : syracuseStep 425609 = 319207) B319207
theorem B425639 : Blo 279826 425639 := bstep (se 1 (by rfl) ⟨319229, by rfl⟩ : syracuseStep 425639 = 638459) B638459
theorem B1769161 : Blo 279826 1769161 := bstep (se 2 (by rfl) ⟨663435, by rfl⟩ : syracuseStep 1769161 = 1326871) B1326871
theorem B2424563 : Blo 279826 2424563 := bstep (se 1 (by rfl) ⟨1818422, by rfl⟩ : syracuseStep 2424563 = 3636845) B3636845
theorem B12156713 : Blo 279826 12156713 := bstep (se 2 (by rfl) ⟨4558767, by rfl⟩ : syracuseStep 12156713 = 9117535) B9117535
theorem B2031655 : Blo 279826 2031655 := bstep (se 1 (by rfl) ⟨1523741, by rfl⟩ : syracuseStep 2031655 = 3047483) B3047483
theorem B6881669 : Blo 279826 6881669 := bstep (se 4 (by rfl) ⟨645156, by rfl⟩ : syracuseStep 6881669 = 1290313) B1290313
theorem B951047 : Blo 279826 951047 := bstep (se 1 (by rfl) ⟨713285, by rfl⟩ : syracuseStep 951047 = 1426571) B1426571
theorem B3736343 : Blo 279826 3736343 := bstep (se 1 (by rfl) ⟨2802257, by rfl⟩ : syracuseStep 3736343 = 5604515) B5604515
theorem B1705313 : Blo 279826 1705313 := bstep (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) B1278985
theorem B427751 : Blo 279826 427751 := bstep (se 1 (by rfl) ⟨320813, by rfl⟩ : syracuseStep 427751 = 641627) B641627
theorem B2033387 : Blo 279826 2033387 := bstep (se 1 (by rfl) ⟨1525040, by rfl⟩ : syracuseStep 2033387 = 3050081) B3050081
theorem B952127 : Blo 279826 952127 := bstep (se 1 (by rfl) ⟨714095, by rfl⟩ : syracuseStep 952127 = 1428191) B1428191
theorem B1017791 : Blo 279826 1017791 := bstep (se 1 (by rfl) ⟨763343, by rfl⟩ : syracuseStep 1017791 = 1526687) B1526687
theorem B1805095 : Blo 279826 1805095 := bstep (se 1 (by rfl) ⟨1353821, by rfl⟩ : syracuseStep 1805095 = 2707643) B2707643
theorem B2395655 : Blo 279826 2395655 := bstep (se 1 (by rfl) ⟨1796741, by rfl⟩ : syracuseStep 2395655 = 3593483) B3593483
theorem B1020545 : Blo 279826 1020545 := bstep (se 2 (by rfl) ⟨382704, by rfl⟩ : syracuseStep 1020545 = 765409) B765409
theorem B1643275 : Blo 279826 1643275 := bstep (se 1 (by rfl) ⟨1232456, by rfl⟩ : syracuseStep 1643275 = 2464913) B2464913
theorem B1610543 : Blo 279826 1610543 := bstep (se 1 (by rfl) ⟨1207907, by rfl⟩ : syracuseStep 1610543 = 2415815) B2415815
theorem B1020775 : Blo 279826 1020775 := bstep (se 1 (by rfl) ⟨765581, by rfl⟩ : syracuseStep 1020775 = 1531163) B1531163
theorem B1938401 : Blo 279826 1938401 := bstep (se 2 (by rfl) ⟨726900, by rfl⟩ : syracuseStep 1938401 = 1453801) B1453801
theorem B4363247 : Blo 279826 4363247 := bstep (se 1 (by rfl) ⟨3272435, by rfl⟩ : syracuseStep 4363247 = 6544871) B6544871
theorem B1348595 : Blo 279826 1348595 := bstep (se 1 (by rfl) ⟨1011446, by rfl⟩ : syracuseStep 1348595 = 2022893) B2022893
theorem B956015 : Blo 279826 956015 := bstep (se 1 (by rfl) ⟨717011, by rfl⟩ : syracuseStep 956015 = 1434023) B1434023
theorem B956447 : Blo 279826 956447 := bstep (se 1 (by rfl) ⟨717335, by rfl⟩ : syracuseStep 956447 = 1434671) B1434671
theorem B301439 : Blo 279826 301439 := bstep (se 1 (by rfl) ⟨226079, by rfl⟩ : syracuseStep 301439 = 452159) B452159
theorem B630089 : Blo 279826 630089 := bstep (se 2 (by rfl) ⟨236283, by rfl⟩ : syracuseStep 630089 = 472567) B472567
theorem B532079 : Blo 279826 532079 := bstep (se 1 (by rfl) ⟨399059, by rfl⟩ : syracuseStep 532079 = 798119) B798119
theorem B2040191 : Blo 279826 2040191 := bstep (se 1 (by rfl) ⟨1530143, by rfl⟩ : syracuseStep 2040191 = 3060287) B3060287
theorem B631529 : Blo 279826 631529 := bstep (se 2 (by rfl) ⟨236823, by rfl⟩ : syracuseStep 631529 = 473647) B473647
theorem B631547 : Blo 279826 631547 := bstep (se 1 (by rfl) ⟨473660, by rfl⟩ : syracuseStep 631547 = 947321) B947321
theorem B598889 : Blo 279826 598889 := bstep (se 2 (by rfl) ⟨224583, by rfl⟩ : syracuseStep 598889 = 449167) B449167
theorem B632807 : Blo 279826 632807 := bstep (se 1 (by rfl) ⟨474605, by rfl⟩ : syracuseStep 632807 = 949211) B949211
theorem B633167 : Blo 279826 633167 := bstep (se 1 (by rfl) ⟨474875, by rfl⟩ : syracuseStep 633167 = 949751) B949751
theorem B1616375 : Blo 279826 1616375 := bstep (se 1 (by rfl) ⟨1212281, by rfl⟩ : syracuseStep 1616375 = 2424563) B2424563
theorem B8104475 : Blo 279826 8104475 := bstep (se 1 (by rfl) ⟨6078356, by rfl⟩ : syracuseStep 8104475 = 12156713) B12156713
theorem B535177 : Blo 279826 535177 := bstep (se 2 (by rfl) ⟨200691, by rfl⟩ : syracuseStep 535177 = 401383) B401383
theorem B633599 : Blo 279826 633599 := bstep (se 1 (by rfl) ⟨475199, by rfl⟩ : syracuseStep 633599 = 950399) B950399
theorem B5385761 : Blo 279826 5385761 := bstep (se 2 (by rfl) ⟨2019660, by rfl⟩ : syracuseStep 5385761 = 4039321) B4039321
theorem B2141801 : Blo 279826 2141801 := bstep (se 2 (by rfl) ⟨803175, by rfl⟩ : syracuseStep 2141801 = 1606351) B1606351
theorem B634823 : Blo 279826 634823 := bstep (se 1 (by rfl) ⟨476117, by rfl⟩ : syracuseStep 634823 = 952235) B952235
theorem B635183 : Blo 279826 635183 := bstep (se 1 (by rfl) ⟨476387, by rfl⟩ : syracuseStep 635183 = 952775) B952775
theorem B9154903 : Blo 279826 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B537455 : Blo 279826 537455 := bstep (se 1 (by rfl) ⟨403091, by rfl⟩ : syracuseStep 537455 = 806183) B806183
theorem B1979873 : Blo 279826 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B636407 : Blo 279826 636407 := bstep (se 1 (by rfl) ⟨477305, by rfl⟩ : syracuseStep 636407 = 954611) B954611
theorem B538139 : Blo 279826 538139 := bstep (se 1 (by rfl) ⟨403604, by rfl⟩ : syracuseStep 538139 = 807209) B807209
theorem B8009441 : Blo 279826 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B10368773 : Blo 279826 10368773 := bstep (se 4 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 10368773 = 1944145) B1944145
theorem B1783625 : Blo 279826 1783625 := bstep (se 2 (by rfl) ⟨668859, by rfl⟩ : syracuseStep 1783625 = 1337719) B1337719
theorem B2144231 : Blo 279826 2144231 := bstep (se 1 (by rfl) ⟨1608173, by rfl⟩ : syracuseStep 2144231 = 3216347) B3216347
theorem B1489291 : Blo 279826 1489291 := bstep (se 1 (by rfl) ⟨1116968, by rfl⟩ : syracuseStep 1489291 = 2233937) B2233937
theorem B473593 : Blo 279826 473593 := bstep (se 2 (by rfl) ⟨177597, by rfl⟩ : syracuseStep 473593 = 355195) B355195
theorem B637487 : Blo 279826 637487 := bstep (se 1 (by rfl) ⟨478115, by rfl⟩ : syracuseStep 637487 = 956231) B956231
theorem B1063763 : Blo 279826 1063763 := bstep (se 1 (by rfl) ⟨797822, by rfl⟩ : syracuseStep 1063763 = 1595645) B1595645
theorem B1915787 : Blo 279826 1915787 := bstep (se 1 (by rfl) ⟨1436840, by rfl⟩ : syracuseStep 1915787 = 2873681) B2873681
theorem B474025 : Blo 279826 474025 := bstep (se 2 (by rfl) ⟨177759, by rfl⟩ : syracuseStep 474025 = 355519) B355519
theorem B802219 : Blo 279826 802219 := bstep (se 1 (by rfl) ⟨601664, by rfl⟩ : syracuseStep 802219 = 1203329) B1203329
theorem B638441 : Blo 279826 638441 := bstep (se 2 (by rfl) ⟨239415, by rfl⟩ : syracuseStep 638441 = 478831) B478831
theorem B1425275 : Blo 279826 1425275 := bstep (se 1 (by rfl) ⟨1068956, by rfl⟩ : syracuseStep 1425275 = 2137913) B2137913
theorem B901307 : Blo 279826 901307 := bstep (se 1 (by rfl) ⟨675980, by rfl⟩ : syracuseStep 901307 = 1351961) B1351961
theorem B1196221 : Blo 279826 1196221 := bstep (se 3 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 1196221 = 448583) B448583
theorem B2506943 : Blo 279826 2506943 := bstep (se 1 (by rfl) ⟨1880207, by rfl⟩ : syracuseStep 2506943 = 3760415) B3760415
theorem B1425761 : Blo 279826 1425761 := bstep (se 2 (by rfl) ⟨534660, by rfl⟩ : syracuseStep 1425761 = 1069321) B1069321
theorem B803495 : Blo 279826 803495 := bstep (se 1 (by rfl) ⟨602621, by rfl⟩ : syracuseStep 803495 = 1205243) B1205243
theorem B476111 : Blo 279826 476111 := bstep (se 1 (by rfl) ⟨357083, by rfl⟩ : syracuseStep 476111 = 714167) B714167
theorem B1066193 : Blo 279826 1066193 := bstep (se 2 (by rfl) ⟨399822, by rfl⟩ : syracuseStep 1066193 = 799645) B799645
theorem B1197281 : Blo 279826 1197281 := bstep (se 2 (by rfl) ⟨448980, by rfl⟩ : syracuseStep 1197281 = 897961) B897961
theorem B280303 : Blo 279826 280303 := bstep (se 1 (by rfl) ⟨210227, by rfl⟩ : syracuseStep 280303 = 420455) B420455
theorem B477083 : Blo 279826 477083 := bstep (se 1 (by rfl) ⟨357812, by rfl⟩ : syracuseStep 477083 = 715625) B715625
theorem B280487 : Blo 279826 280487 := bstep (se 1 (by rfl) ⟨210365, by rfl⟩ : syracuseStep 280487 = 420731) B420731
theorem B280667 : Blo 279826 280667 := bstep (se 1 (by rfl) ⟨210500, by rfl⟩ : syracuseStep 280667 = 421001) B421001
theorem B280703 : Blo 279826 280703 := bstep (se 1 (by rfl) ⟨210527, by rfl⟩ : syracuseStep 280703 = 421055) B421055
theorem B1067195 : Blo 279826 1067195 := bstep (se 1 (by rfl) ⟨800396, by rfl⟩ : syracuseStep 1067195 = 1600793) B1600793
theorem B805295 : Blo 279826 805295 := bstep (se 1 (by rfl) ⟨603971, by rfl⟩ : syracuseStep 805295 = 1207943) B1207943
theorem B1165763 : Blo 279826 1165763 := bstep (se 1 (by rfl) ⟨874322, by rfl⟩ : syracuseStep 1165763 = 1748645) B1748645
theorem B281063 : Blo 279826 281063 := bstep (se 1 (by rfl) ⟨210797, by rfl⟩ : syracuseStep 281063 = 421595) B421595
theorem B3033611 : Blo 279826 3033611 := bstep (se 1 (by rfl) ⟨2275208, by rfl⟩ : syracuseStep 3033611 = 4550417) B4550417
theorem B281243 : Blo 279826 281243 := bstep (se 1 (by rfl) ⟨210932, by rfl⟩ : syracuseStep 281243 = 421865) B421865
theorem B281255 : Blo 279826 281255 := bstep (se 1 (by rfl) ⟨210941, by rfl⟩ : syracuseStep 281255 = 421883) B421883
theorem B281279 : Blo 279826 281279 := bstep (se 1 (by rfl) ⟨210959, by rfl⟩ : syracuseStep 281279 = 421919) B421919
theorem B281295 : Blo 279826 281295 := bstep (se 1 (by rfl) ⟨210971, by rfl⟩ : syracuseStep 281295 = 421943) B421943
theorem B1395443 : Blo 279826 1395443 := bstep (se 1 (by rfl) ⟨1046582, by rfl⟩ : syracuseStep 1395443 = 2093165) B2093165
theorem B2018047 : Blo 279826 2018047 := bstep (se 1 (by rfl) ⟨1513535, by rfl⟩ : syracuseStep 2018047 = 3027071) B3027071
theorem B281375 : Blo 279826 281375 := bstep (se 1 (by rfl) ⟨211031, by rfl⟩ : syracuseStep 281375 = 422063) B422063
theorem B1723265 : Blo 279826 1723265 := bstep (se 2 (by rfl) ⟨646224, by rfl⟩ : syracuseStep 1723265 = 1292449) B1292449
theorem B281511 : Blo 279826 281511 := bstep (se 1 (by rfl) ⟨211133, by rfl⟩ : syracuseStep 281511 = 422267) B422267
theorem B1199195 : Blo 279826 1199195 := bstep (se 1 (by rfl) ⟨899396, by rfl⟩ : syracuseStep 1199195 = 1798793) B1798793
theorem B281691 : Blo 279826 281691 := bstep (se 1 (by rfl) ⟨211268, by rfl⟩ : syracuseStep 281691 = 422537) B422537
theorem B1166543 : Blo 279826 1166543 := bstep (se 1 (by rfl) ⟨874907, by rfl⟩ : syracuseStep 1166543 = 1749815) B1749815
theorem B281831 : Blo 279826 281831 := bstep (se 1 (by rfl) ⟨211373, by rfl⟩ : syracuseStep 281831 = 422747) B422747
theorem B281851 : Blo 279826 281851 := bstep (se 1 (by rfl) ⟨211388, by rfl⟩ : syracuseStep 281851 = 422777) B422777
theorem B282271 : Blo 279826 282271 := bstep (se 1 (by rfl) ⟨211703, by rfl⟩ : syracuseStep 282271 = 423407) B423407
theorem B2150063 : Blo 279826 2150063 := bstep (se 1 (by rfl) ⟨1612547, by rfl⟩ : syracuseStep 2150063 = 3225095) B3225095
theorem B478939 : Blo 279826 478939 := bstep (se 1 (by rfl) ⟨359204, by rfl⟩ : syracuseStep 478939 = 718409) B718409
theorem B970471 : Blo 279826 970471 := bstep (se 1 (by rfl) ⟨727853, by rfl⟩ : syracuseStep 970471 = 1455707) B1455707
theorem B282351 : Blo 279826 282351 := bstep (se 1 (by rfl) ⟨211763, by rfl⟩ : syracuseStep 282351 = 423527) B423527
theorem B282655 : Blo 279826 282655 := bstep (se 1 (by rfl) ⟨211991, by rfl⟩ : syracuseStep 282655 = 423983) B423983
theorem B282735 : Blo 279826 282735 := bstep (se 1 (by rfl) ⟨212051, by rfl⟩ : syracuseStep 282735 = 424103) B424103
theorem B282831 : Blo 279826 282831 := bstep (se 1 (by rfl) ⟨212123, by rfl⟩ : syracuseStep 282831 = 424247) B424247
theorem B282951 : Blo 279826 282951 := bstep (se 1 (by rfl) ⟨212213, by rfl⟩ : syracuseStep 282951 = 424427) B424427
theorem B1200527 : Blo 279826 1200527 := bstep (se 1 (by rfl) ⟨900395, by rfl⟩ : syracuseStep 1200527 = 1800791) B1800791
theorem B709033 : Blo 279826 709033 := bstep (se 2 (by rfl) ⟨265887, by rfl⟩ : syracuseStep 709033 = 531775) B531775
theorem B283183 : Blo 279826 283183 := bstep (se 1 (by rfl) ⟨212387, by rfl⟩ : syracuseStep 283183 = 424775) B424775
theorem B709307 : Blo 279826 709307 := bstep (se 1 (by rfl) ⟨531980, by rfl⟩ : syracuseStep 709307 = 1063961) B1063961
theorem B283739 : Blo 279826 283739 := bstep (se 1 (by rfl) ⟨212804, by rfl⟩ : syracuseStep 283739 = 425609) B425609
theorem B283759 : Blo 279826 283759 := bstep (se 1 (by rfl) ⟨212819, by rfl⟩ : syracuseStep 283759 = 425639) B425639
theorem B1922555 : Blo 279826 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B2446843 : Blo 279826 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B317551 : Blo 279826 317551 := bstep (se 1 (by rfl) ⟨238163, by rfl⟩ : syracuseStep 317551 = 476327) B476327
theorem B1202303 : Blo 279826 1202303 := bstep (se 1 (by rfl) ⟨901727, by rfl⟩ : syracuseStep 1202303 = 1803455) B1803455
theorem B2316671 : Blo 279826 2316671 := bstep (se 1 (by rfl) ⟨1737503, by rfl⟩ : syracuseStep 2316671 = 3475007) B3475007
theorem B711119 : Blo 279826 711119 := bstep (se 1 (by rfl) ⟨533339, by rfl⟩ : syracuseStep 711119 = 1066679) B1066679
theorem B449275 : Blo 279826 449275 := bstep (se 1 (by rfl) ⟨336956, by rfl⟩ : syracuseStep 449275 = 673913) B673913
theorem B1792975 : Blo 279826 1792975 := bstep (se 1 (by rfl) ⟨1344731, by rfl⟩ : syracuseStep 1792975 = 2689463) B2689463
theorem B1072223 : Blo 279826 1072223 := bstep (se 1 (by rfl) ⟨804167, by rfl⟩ : syracuseStep 1072223 = 1608335) B1608335
theorem B1072511 : Blo 279826 1072511 := bstep (se 1 (by rfl) ⟨804383, by rfl⟩ : syracuseStep 1072511 = 1608767) B1608767
theorem B712415 : Blo 279826 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B646991 : Blo 279826 646991 := bstep (se 1 (by rfl) ⟨485243, by rfl⟩ : syracuseStep 646991 = 970487) B970487
theorem B582751 : Blo 279826 582751 := bstep (se 1 (by rfl) ⟨437063, by rfl⟩ : syracuseStep 582751 = 874127) B874127
theorem B560424491 : Blo 279826 560424491 := bstep (se 1 (by rfl) ⟨420318368, by rfl⟩ : syracuseStep 560424491 = 840636737) B840636737
theorem B452479 : Blo 279826 452479 := bstep (se 1 (by rfl) ⟨339359, by rfl⟩ : syracuseStep 452479 = 678719) B678719
theorem B420335 : Blo 279826 420335 := bstep (se 1 (by rfl) ⟨315251, by rfl⟩ : syracuseStep 420335 = 630503) B630503
theorem B7563959 : Blo 279826 7563959 := bstep (se 1 (by rfl) ⟨5672969, by rfl⟩ : syracuseStep 7563959 = 11345939) B11345939
theorem B29420243 : Blo 279826 29420243 := bstep (se 1 (by rfl) ⟨22065182, by rfl⟩ : syracuseStep 29420243 = 44130365) B44130365
theorem B420647 : Blo 279826 420647 := bstep (se 1 (by rfl) ⟨315485, by rfl⟩ : syracuseStep 420647 = 630971) B630971
theorem B945215 : Blo 279826 945215 := bstep (se 1 (by rfl) ⟨708911, by rfl⟩ : syracuseStep 945215 = 1417823) B1417823
theorem B1076399 : Blo 279826 1076399 := bstep (se 1 (by rfl) ⟨807299, by rfl⟩ : syracuseStep 1076399 = 1614599) B1614599
theorem B421247 : Blo 279826 421247 := bstep (se 1 (by rfl) ⟨315935, by rfl⟩ : syracuseStep 421247 = 631871) B631871
theorem B1142191 : Blo 279826 1142191 := bstep (se 1 (by rfl) ⟨856643, by rfl⟩ : syracuseStep 1142191 = 1713287) B1713287
theorem B2059847 : Blo 279826 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B2125763 : Blo 279826 2125763 := bstep (se 1 (by rfl) ⟨1594322, by rfl⟩ : syracuseStep 2125763 = 3188645) B3188645
theorem B422123 : Blo 279826 422123 := bstep (se 1 (by rfl) ⟨316592, by rfl⟩ : syracuseStep 422123 = 633185) B633185
theorem B422183 : Blo 279826 422183 := bstep (se 1 (by rfl) ⟨316637, by rfl⟩ : syracuseStep 422183 = 633275) B633275
theorem B946511 : Blo 279826 946511 := bstep (se 1 (by rfl) ⟨709883, by rfl⟩ : syracuseStep 946511 = 1419767) B1419767
theorem B5140817 : Blo 279826 5140817 := bstep (se 2 (by rfl) ⟨1927806, by rfl⟩ : syracuseStep 5140817 = 3855613) B3855613
theorem B1143229 : Blo 279826 1143229 := bstep (se 3 (by rfl) ⟨214355, by rfl⟩ : syracuseStep 1143229 = 428711) B428711
theorem B2028169 : Blo 279826 2028169 := bstep (se 2 (by rfl) ⟨760563, by rfl⟩ : syracuseStep 2028169 = 1521127) B1521127
theorem B422711 : Blo 279826 422711 := bstep (se 1 (by rfl) ⟨317033, by rfl⟩ : syracuseStep 422711 = 634067) B634067
theorem B422825 : Blo 279826 422825 := bstep (se 2 (by rfl) ⟨158559, by rfl⟩ : syracuseStep 422825 = 317119) B317119
theorem B357311 : Blo 279826 357311 := bstep (se 1 (by rfl) ⟨267983, by rfl⟩ : syracuseStep 357311 = 535967) B535967
theorem B422891 : Blo 279826 422891 := bstep (se 1 (by rfl) ⟨317168, by rfl⟩ : syracuseStep 422891 = 634337) B634337
theorem B423023 : Blo 279826 423023 := bstep (se 1 (by rfl) ⟨317267, by rfl⟩ : syracuseStep 423023 = 634535) B634535
theorem B1210079 : Blo 279826 1210079 := bstep (se 1 (by rfl) ⟨907559, by rfl⟩ : syracuseStep 1210079 = 1815119) B1815119
theorem B423791 : Blo 279826 423791 := bstep (se 1 (by rfl) ⟨317843, by rfl⟩ : syracuseStep 423791 = 635687) B635687
theorem B423803 : Blo 279826 423803 := bstep (se 1 (by rfl) ⟨317852, by rfl⟩ : syracuseStep 423803 = 635705) B635705
theorem B424043 : Blo 279826 424043 := bstep (se 1 (by rfl) ⟨318032, by rfl⟩ : syracuseStep 424043 = 636065) B636065
theorem B1013897 : Blo 279826 1013897 := bstep (se 2 (by rfl) ⟨380211, by rfl⟩ : syracuseStep 1013897 = 760423) B760423
theorem B3832019 : Blo 279826 3832019 := bstep (se 1 (by rfl) ⟨2874014, by rfl⟩ : syracuseStep 3832019 = 5748029) B5748029
theorem B948455 : Blo 279826 948455 := bstep (se 1 (by rfl) ⟨711341, by rfl⟩ : syracuseStep 948455 = 1422683) B1422683
theorem B424223 : Blo 279826 424223 := bstep (se 1 (by rfl) ⟨318167, by rfl⟩ : syracuseStep 424223 = 636335) B636335
theorem B424295 : Blo 279826 424295 := bstep (se 1 (by rfl) ⟨318221, by rfl⟩ : syracuseStep 424295 = 636443) B636443
theorem B13826419 : Blo 279826 13826419 := bstep (se 1 (by rfl) ⟨10369814, by rfl⟩ : syracuseStep 13826419 = 20739629) B20739629
theorem B424361 : Blo 279826 424361 := bstep (se 2 (by rfl) ⟨159135, by rfl⟩ : syracuseStep 424361 = 318271) B318271
theorem B424415 : Blo 279826 424415 := bstep (se 1 (by rfl) ⟨318311, by rfl⟩ : syracuseStep 424415 = 636623) B636623
theorem B2325217 : Blo 279826 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B949049 : Blo 279826 949049 := bstep (se 2 (by rfl) ⟨355893, by rfl⟩ : syracuseStep 949049 = 711787) B711787
theorem B1440617 : Blo 279826 1440617 := bstep (se 2 (by rfl) ⟨540231, by rfl⟩ : syracuseStep 1440617 = 1080463) B1080463
theorem B949103 : Blo 279826 949103 := bstep (se 1 (by rfl) ⟨711827, by rfl⟩ : syracuseStep 949103 = 1423655) B1423655
theorem B424943 : Blo 279826 424943 := bstep (se 1 (by rfl) ⟨318707, by rfl⟩ : syracuseStep 424943 = 637415) B637415
theorem B425129 : Blo 279826 425129 := bstep (se 2 (by rfl) ⟨159423, by rfl⟩ : syracuseStep 425129 = 318847) B318847
theorem B1244335 : Blo 279826 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B1441097 : Blo 279826 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B2358881 : Blo 279826 2358881 := bstep (se 2 (by rfl) ⟨884580, by rfl⟩ : syracuseStep 2358881 = 1769161) B1769161
theorem B1867657 : Blo 279826 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B950507 : Blo 279826 950507 := bstep (se 1 (by rfl) ⟨712880, by rfl⟩ : syracuseStep 950507 = 1425761) B1425761
theorem B4587779 : Blo 279826 4587779 := bstep (se 1 (by rfl) ⟨3440834, by rfl⟩ : syracuseStep 4587779 = 6881669) B6881669
theorem B6685181 : Blo 279826 6685181 := bstep (se 3 (by rfl) ⟨1253471, by rfl⟩ : syracuseStep 6685181 = 2506943) B2506943
theorem B2490895 : Blo 279826 2490895 := bstep (se 1 (by rfl) ⟨1868171, by rfl⟩ : syracuseStep 2490895 = 3736343) B3736343
theorem B1148843 : Blo 279826 1148843 := bstep (se 1 (by rfl) ⟨861632, by rfl⟩ : syracuseStep 1148843 = 1723265) B1723265
theorem B952829 : Blo 279826 952829 := bstep (se 3 (by rfl) ⟨178655, by rfl⟩ : syracuseStep 952829 = 357311) B357311
theorem B1281703 : Blo 279826 1281703 := bstep (se 1 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 1281703 = 1922555) B1922555
theorem B2690729 : Blo 279826 2690729 := bstep (se 2 (by rfl) ⟨1009023, by rfl⟩ : syracuseStep 2690729 = 2018047) B2018047
theorem B1544447 : Blo 279826 1544447 := bstep (se 1 (by rfl) ⟨1158335, by rfl⟩ : syracuseStep 1544447 = 2316671) B2316671
theorem B4756333 : Blo 279826 4756333 := bstep (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) B1783625
theorem B431327 : Blo 279826 431327 := bstep (se 1 (by rfl) ⟨323495, by rfl⟩ : syracuseStep 431327 = 646991) B646991
theorem B399259 : Blo 279826 399259 := bstep (se 1 (by rfl) ⟨299444, by rfl⟩ : syracuseStep 399259 = 598889) B598889
theorem B630143 : Blo 279826 630143 := bstep (se 1 (by rfl) ⟨472607, by rfl⟩ : syracuseStep 630143 = 945215) B945215
theorem B1417175 : Blo 279826 1417175 := bstep (se 1 (by rfl) ⟨1062881, by rfl⟩ : syracuseStep 1417175 = 2125763) B2125763
theorem B631007 : Blo 279826 631007 := bstep (se 1 (by rfl) ⟨473255, by rfl⟩ : syracuseStep 631007 = 946511) B946511
theorem B631457 : Blo 279826 631457 := bstep (se 2 (by rfl) ⟨236796, by rfl⟩ : syracuseStep 631457 = 473593) B473593
theorem B1319915 : Blo 279826 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B599033 : Blo 279826 599033 := bstep (se 2 (by rfl) ⟨224637, by rfl⟩ : syracuseStep 599033 = 449275) B449275
theorem B632033 : Blo 279826 632033 := bstep (se 2 (by rfl) ⟨237012, by rfl⟩ : syracuseStep 632033 = 474025) B474025
theorem B632303 : Blo 279826 632303 := bstep (se 1 (by rfl) ⟨474227, by rfl⟩ : syracuseStep 632303 = 948455) B948455
theorem B632699 : Blo 279826 632699 := bstep (se 1 (by rfl) ⟨474524, by rfl⟩ : syracuseStep 632699 = 949049) B949049
theorem B632735 : Blo 279826 632735 := bstep (se 1 (by rfl) ⟨474551, by rfl⟩ : syracuseStep 632735 = 949103) B949103
theorem B960731 : Blo 279826 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B600871 : Blo 279826 600871 := bstep (se 1 (by rfl) ⟨450653, by rfl⟩ : syracuseStep 600871 = 901307) B901307
theorem B535663 : Blo 279826 535663 := bstep (se 1 (by rfl) ⟨401747, by rfl⟩ : syracuseStep 535663 = 803495) B803495
theorem B634031 : Blo 279826 634031 := bstep (se 1 (by rfl) ⟨475523, by rfl⟩ : syracuseStep 634031 = 951047) B951047
theorem B798187 : Blo 279826 798187 := bstep (se 1 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 798187 = 1197281) B1197281
theorem B1355591 : Blo 279826 1355591 := bstep (se 1 (by rfl) ⟨1016693, by rfl⟩ : syracuseStep 1355591 = 2033387) B2033387
theorem B634751 : Blo 279826 634751 := bstep (se 1 (by rfl) ⟨476063, by rfl⟩ : syracuseStep 634751 = 952127) B952127
theorem B536863 : Blo 279826 536863 := bstep (se 1 (by rfl) ⟨402647, by rfl⟩ : syracuseStep 536863 = 805295) B805295
theorem B930295 : Blo 279826 930295 := bstep (se 1 (by rfl) ⟨697721, by rfl⟩ : syracuseStep 930295 = 1395443) B1395443
theorem B73740901 : Blo 279826 73740901 := bstep (se 4 (by rfl) ⟨6913209, by rfl⟩ : syracuseStep 73740901 = 13826419) B13826419
theorem B799463 : Blo 279826 799463 := bstep (se 1 (by rfl) ⟨599597, by rfl⟩ : syracuseStep 799463 = 1199195) B1199195
theorem B603305 : Blo 279826 603305 := bstep (se 2 (by rfl) ⟨226239, by rfl⟩ : syracuseStep 603305 = 452479) B452479
theorem B800351 : Blo 279826 800351 := bstep (se 1 (by rfl) ⟨600263, by rfl⟩ : syracuseStep 800351 = 1200527) B1200527
theorem B472871 : Blo 279826 472871 := bstep (se 1 (by rfl) ⟨354653, by rfl⟩ : syracuseStep 472871 = 709307) B709307
theorem B1292267 : Blo 279826 1292267 := bstep (se 1 (by rfl) ⟨969200, by rfl⟩ : syracuseStep 1292267 = 1938401) B1938401
theorem B899063 : Blo 279826 899063 := bstep (se 1 (by rfl) ⟨674297, by rfl⟩ : syracuseStep 899063 = 1348595) B1348595
theorem B2406793 : Blo 279826 2406793 := bstep (se 2 (by rfl) ⟨902547, by rfl⟩ : syracuseStep 2406793 = 1805095) B1805095
theorem B637343 : Blo 279826 637343 := bstep (se 1 (by rfl) ⟨478007, by rfl⟩ : syracuseStep 637343 = 956015) B956015
theorem B637631 : Blo 279826 637631 := bstep (se 1 (by rfl) ⟨478223, by rfl⟩ : syracuseStep 637631 = 956447) B956447
theorem B474079 : Blo 279826 474079 := bstep (se 1 (by rfl) ⟨355559, by rfl⟩ : syracuseStep 474079 = 711119) B711119
theorem B638585 : Blo 279826 638585 := bstep (se 2 (by rfl) ⟨239469, by rfl⟩ : syracuseStep 638585 = 478939) B478939
theorem B474943 : Blo 279826 474943 := bstep (se 1 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 474943 = 712415) B712415
theorem B1360127 : Blo 279826 1360127 := bstep (se 1 (by rfl) ⟨1020095, by rfl⟩ : syracuseStep 1360127 = 2040191) B2040191
theorem B2703725 : Blo 279826 2703725 := bstep (se 3 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 2703725 = 1013897) B1013897
theorem B12206537 : Blo 279826 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B1524305 : Blo 279826 1524305 := bstep (se 2 (by rfl) ⟨571614, by rfl⟩ : syracuseStep 1524305 = 1143229) B1143229
theorem B2704225 : Blo 279826 2704225 := bstep (se 2 (by rfl) ⟨1014084, by rfl⟩ : syracuseStep 2704225 = 2028169) B2028169
theorem B803837 : Blo 279826 803837 := bstep (se 3 (by rfl) ⟨150719, by rfl⟩ : syracuseStep 803837 = 301439) B301439
theorem B1361033 : Blo 279826 1361033 := bstep (se 2 (by rfl) ⟨510387, by rfl⟩ : syracuseStep 1361033 = 1020775) B1020775
theorem B280223 : Blo 279826 280223 := bstep (se 1 (by rfl) ⟨210167, by rfl⟩ : syracuseStep 280223 = 420335) B420335
theorem B19613495 : Blo 279826 19613495 := bstep (se 1 (by rfl) ⟨14710121, by rfl⟩ : syracuseStep 19613495 = 29420243) B29420243
theorem B280431 : Blo 279826 280431 := bstep (se 1 (by rfl) ⟨210323, by rfl⟩ : syracuseStep 280431 = 420647) B420647
theorem B3262457 : Blo 279826 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B280831 : Blo 279826 280831 := bstep (se 1 (by rfl) ⟨210623, by rfl⟩ : syracuseStep 280831 = 421247) B421247
theorem B3590507 : Blo 279826 3590507 := bstep (se 1 (by rfl) ⟨2692880, by rfl⟩ : syracuseStep 3590507 = 5385761) B5385761
theorem B1427867 : Blo 279826 1427867 := bstep (se 1 (by rfl) ⟨1070900, by rfl⟩ : syracuseStep 1427867 = 2141801) B2141801
theorem B281415 : Blo 279826 281415 := bstep (se 1 (by rfl) ⟨211061, by rfl⟩ : syracuseStep 281415 = 422123) B422123
theorem B281455 : Blo 279826 281455 := bstep (se 1 (by rfl) ⟨211091, by rfl⟩ : syracuseStep 281455 = 422183) B422183
theorem B3427211 : Blo 279826 3427211 := bstep (se 1 (by rfl) ⟨2570408, by rfl⟩ : syracuseStep 3427211 = 5140817) B5140817
theorem B31771541 : Blo 279826 31771541 := bstep (se 6 (by rfl) ⟨744645, by rfl⟩ : syracuseStep 31771541 = 1489291) B1489291
theorem B281807 : Blo 279826 281807 := bstep (se 1 (by rfl) ⟨211355, by rfl⟩ : syracuseStep 281807 = 422711) B422711
theorem B281883 : Blo 279826 281883 := bstep (se 1 (by rfl) ⟨211412, by rfl⟩ : syracuseStep 281883 = 422825) B422825
theorem B281927 : Blo 279826 281927 := bstep (se 1 (by rfl) ⟨211445, by rfl⟩ : syracuseStep 281927 = 422891) B422891
theorem B282015 : Blo 279826 282015 := bstep (se 1 (by rfl) ⟨211511, by rfl⟩ : syracuseStep 282015 = 423023) B423023
theorem B3100289 : Blo 279826 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B806719 : Blo 279826 806719 := bstep (se 1 (by rfl) ⟨605039, by rfl⟩ : syracuseStep 806719 = 1210079) B1210079
theorem B282527 : Blo 279826 282527 := bstep (se 1 (by rfl) ⟨211895, by rfl⟩ : syracuseStep 282527 = 423791) B423791
theorem B282535 : Blo 279826 282535 := bstep (se 1 (by rfl) ⟨211901, by rfl⟩ : syracuseStep 282535 = 423803) B423803
theorem B1429487 : Blo 279826 1429487 := bstep (se 1 (by rfl) ⟨1072115, by rfl⟩ : syracuseStep 1429487 = 2144231) B2144231
theorem B282695 : Blo 279826 282695 := bstep (se 1 (by rfl) ⟨212021, by rfl⟩ : syracuseStep 282695 = 424043) B424043
theorem B282815 : Blo 279826 282815 := bstep (se 1 (by rfl) ⟨212111, by rfl⟩ : syracuseStep 282815 = 424223) B424223
theorem B1659113 : Blo 279826 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B282863 : Blo 279826 282863 := bstep (se 1 (by rfl) ⟨212147, by rfl⟩ : syracuseStep 282863 = 424295) B424295
theorem B282907 : Blo 279826 282907 := bstep (se 1 (by rfl) ⟨212180, by rfl⟩ : syracuseStep 282907 = 424361) B424361
theorem B282943 : Blo 279826 282943 := bstep (se 1 (by rfl) ⟨212207, by rfl⟩ : syracuseStep 282943 = 424415) B424415
theorem B709175 : Blo 279826 709175 := bstep (se 1 (by rfl) ⟨531881, by rfl⟩ : syracuseStep 709175 = 1063763) B1063763
theorem B1069625 : Blo 279826 1069625 := bstep (se 2 (by rfl) ⟨401109, by rfl⟩ : syracuseStep 1069625 = 802219) B802219
theorem B283295 : Blo 279826 283295 := bstep (se 1 (by rfl) ⟨212471, by rfl⟩ : syracuseStep 283295 = 424943) B424943
theorem B283419 : Blo 279826 283419 := bstep (se 1 (by rfl) ⟨212564, by rfl⟩ : syracuseStep 283419 = 425129) B425129
theorem B2708873 : Blo 279826 2708873 := bstep (se 2 (by rfl) ⟨1015827, by rfl⟩ : syracuseStep 2708873 = 2031655) B2031655
theorem B1594961 : Blo 279826 1594961 := bstep (se 2 (by rfl) ⟨598110, by rfl⟩ : syracuseStep 1594961 = 1196221) B1196221
theorem B317407 : Blo 279826 317407 := bstep (se 1 (by rfl) ⟨238055, by rfl⟩ : syracuseStep 317407 = 476111) B476111
theorem B710795 : Blo 279826 710795 := bstep (se 1 (by rfl) ⟨533096, by rfl⟩ : syracuseStep 710795 = 1066193) B1066193
theorem B1136875 : Blo 279826 1136875 := bstep (se 1 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 1136875 = 1705313) B1705313
theorem B285167 : Blo 279826 285167 := bstep (se 1 (by rfl) ⟨213875, by rfl⟩ : syracuseStep 285167 = 427751) B427751
theorem B318055 : Blo 279826 318055 := bstep (se 1 (by rfl) ⟨238541, by rfl⟩ : syracuseStep 318055 = 477083) B477083
theorem B678527 : Blo 279826 678527 := bstep (se 1 (by rfl) ⟨508895, by rfl⟩ : syracuseStep 678527 = 1017791) B1017791
theorem B711463 : Blo 279826 711463 := bstep (se 1 (by rfl) ⟨533597, by rfl⟩ : syracuseStep 711463 = 1067195) B1067195
theorem B777001 : Blo 279826 777001 := bstep (se 2 (by rfl) ⟨291375, by rfl⟩ : syracuseStep 777001 = 582751) B582751
theorem B2022407 : Blo 279826 2022407 := bstep (se 1 (by rfl) ⟨1516805, by rfl⟩ : syracuseStep 2022407 = 3033611) B3033611
theorem B777695 : Blo 279826 777695 := bstep (se 1 (by rfl) ⟨583271, by rfl⟩ : syracuseStep 777695 = 1166543) B1166543
theorem B1433213 : Blo 279826 1433213 := bstep (se 3 (by rfl) ⟨268727, by rfl⟩ : syracuseStep 1433213 = 537455) B537455
theorem B1597103 : Blo 279826 1597103 := bstep (se 1 (by rfl) ⟨1197827, by rfl⟩ : syracuseStep 1597103 = 2395655) B2395655
theorem B1433375 : Blo 279826 1433375 := bstep (se 1 (by rfl) ⟨1075031, by rfl⟩ : syracuseStep 1433375 = 2150063) B2150063
theorem B680363 : Blo 279826 680363 := bstep (se 1 (by rfl) ⟨510272, by rfl⟩ : syracuseStep 680363 = 1020545) B1020545
theorem B1073695 : Blo 279826 1073695 := bstep (se 1 (by rfl) ⟨805271, by rfl⟩ : syracuseStep 1073695 = 1610543) B1610543
theorem B2908831 : Blo 279826 2908831 := bstep (se 1 (by rfl) ⟨2181623, by rfl⟩ : syracuseStep 2908831 = 4363247) B4363247
theorem B713569 : Blo 279826 713569 := bstep (se 2 (by rfl) ⟨267588, by rfl⟩ : syracuseStep 713569 = 535177) B535177
theorem B714815 : Blo 279826 714815 := bstep (se 1 (by rfl) ⟨536111, by rfl⟩ : syracuseStep 714815 = 1072223) B1072223
theorem B420059 : Blo 279826 420059 := bstep (se 1 (by rfl) ⟨315044, by rfl⟩ : syracuseStep 420059 = 630089) B630089
theorem B715007 : Blo 279826 715007 := bstep (se 1 (by rfl) ⟨536255, by rfl⟩ : syracuseStep 715007 = 1072511) B1072511
theorem B354719 : Blo 279826 354719 := bstep (se 1 (by rfl) ⟨266039, by rfl⟩ : syracuseStep 354719 = 532079) B532079
theorem B3206141 : Blo 279826 3206141 := bstep (se 3 (by rfl) ⟨601151, by rfl⟩ : syracuseStep 3206141 = 1202303) B1202303
theorem B421019 : Blo 279826 421019 := bstep (se 1 (by rfl) ⟨315764, by rfl⟩ : syracuseStep 421019 = 631529) B631529
theorem B421031 : Blo 279826 421031 := bstep (se 1 (by rfl) ⟨315773, by rfl⟩ : syracuseStep 421031 = 631547) B631547
theorem B945377 : Blo 279826 945377 := bstep (se 2 (by rfl) ⟨354516, by rfl⟩ : syracuseStep 945377 = 709033) B709033
theorem B2191033 : Blo 279826 2191033 := bstep (se 2 (by rfl) ⟨821637, by rfl⟩ : syracuseStep 2191033 = 1643275) B1643275
theorem B373616327 : Blo 279826 373616327 := bstep (se 1 (by rfl) ⟨280212245, by rfl⟩ : syracuseStep 373616327 = 560424491) B560424491
theorem B3108701 : Blo 279826 3108701 := bstep (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) B1165763
theorem B421871 : Blo 279826 421871 := bstep (se 1 (by rfl) ⟨316403, by rfl⟩ : syracuseStep 421871 = 632807) B632807
theorem B422111 : Blo 279826 422111 := bstep (se 1 (by rfl) ⟨316583, by rfl⟩ : syracuseStep 422111 = 633167) B633167
theorem B1077583 : Blo 279826 1077583 := bstep (se 1 (by rfl) ⟨808187, by rfl⟩ : syracuseStep 1077583 = 1616375) B1616375
theorem B5402983 : Blo 279826 5402983 := bstep (se 1 (by rfl) ⟨4052237, by rfl⟩ : syracuseStep 5402983 = 8104475) B8104475
theorem B5042639 : Blo 279826 5042639 := bstep (se 1 (by rfl) ⟨3781979, by rfl⟩ : syracuseStep 5042639 = 7563959) B7563959
theorem B422399 : Blo 279826 422399 := bstep (se 1 (by rfl) ⟨316799, by rfl⟩ : syracuseStep 422399 = 633599) B633599
theorem B717599 : Blo 279826 717599 := bstep (se 1 (by rfl) ⟨538199, by rfl⟩ : syracuseStep 717599 = 1076399) B1076399
theorem B6091685 : Blo 279826 6091685 := bstep (se 4 (by rfl) ⟨571095, by rfl⟩ : syracuseStep 6091685 = 1142191) B1142191
theorem B1373231 : Blo 279826 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B423215 : Blo 279826 423215 := bstep (se 1 (by rfl) ⟨317411, by rfl⟩ : syracuseStep 423215 = 634823) B634823
theorem B423401 : Blo 279826 423401 := bstep (se 2 (by rfl) ⟨158775, by rfl⟩ : syracuseStep 423401 = 317551) B317551
theorem B423455 : Blo 279826 423455 := bstep (se 1 (by rfl) ⟨317591, by rfl⟩ : syracuseStep 423455 = 635183) B635183
theorem B424271 : Blo 279826 424271 := bstep (se 1 (by rfl) ⟨318203, by rfl⟩ : syracuseStep 424271 = 636407) B636407
theorem B358759 : Blo 279826 358759 := bstep (se 1 (by rfl) ⟨269069, by rfl⟩ : syracuseStep 358759 = 538139) B538139
theorem B15366581 : Blo 279826 15366581 := bstep (se 5 (by rfl) ⟨720308, by rfl⟩ : syracuseStep 15366581 = 1440617) B1440617
theorem B5339627 : Blo 279826 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B6912515 : Blo 279826 6912515 := bstep (se 1 (by rfl) ⟨5184386, by rfl⟩ : syracuseStep 6912515 = 10368773) B10368773
theorem B5175845 : Blo 279826 5175845 := bstep (se 4 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 5175845 = 970471) B970471
theorem B2390633 : Blo 279826 2390633 := bstep (se 2 (by rfl) ⟨896487, by rfl⟩ : syracuseStep 2390633 = 1792975) B1792975
theorem B2554679 : Blo 279826 2554679 := bstep (se 1 (by rfl) ⟨1916009, by rfl⟩ : syracuseStep 2554679 = 3832019) B3832019
theorem B424991 : Blo 279826 424991 := bstep (se 1 (by rfl) ⟨318743, by rfl⟩ : syracuseStep 424991 = 637487) B637487
theorem B1277191 : Blo 279826 1277191 := bstep (se 1 (by rfl) ⟨957893, by rfl⟩ : syracuseStep 1277191 = 1915787) B1915787
theorem B425627 : Blo 279826 425627 := bstep (se 1 (by rfl) ⟨319220, by rfl⟩ : syracuseStep 425627 = 638441) B638441
theorem B1572587 : Blo 279826 1572587 := bstep (se 1 (by rfl) ⟨1179440, by rfl⟩ : syracuseStep 1572587 = 2358881) B2358881
theorem B2490209 : Blo 279826 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B950183 : Blo 279826 950183 := bstep (se 1 (by rfl) ⟨712637, by rfl⟩ : syracuseStep 950183 = 1425275) B1425275
theorem B1802483 : Blo 279826 1802483 := bstep (se 1 (by rfl) ⟨1351862, by rfl⟩ : syracuseStep 1802483 = 2703725) B2703725
theorem B4456787 : Blo 279826 4456787 := bstep (se 1 (by rfl) ⟨3342590, by rfl⟩ : syracuseStep 4456787 = 6685181) B6685181
theorem B3605633 : Blo 279826 3605633 := bstep (se 2 (by rfl) ⟨1352112, by rfl⟩ : syracuseStep 3605633 = 2704225) B2704225
theorem B951425 : Blo 279826 951425 := bstep (se 2 (by rfl) ⟨356784, by rfl⟩ : syracuseStep 951425 = 713569) B713569
theorem B13075663 : Blo 279826 13075663 := bstep (se 1 (by rfl) ⟨9806747, by rfl⟩ : syracuseStep 13075663 = 19613495) B19613495
theorem B4064813 : Blo 279826 4064813 := bstep (se 3 (by rfl) ⟨762152, by rfl⟩ : syracuseStep 4064813 = 1524305) B1524305
theorem B2393671 : Blo 279826 2393671 := bstep (se 1 (by rfl) ⟨1795253, by rfl⟩ : syracuseStep 2393671 = 3590507) B3590507
theorem B951911 : Blo 279826 951911 := bstep (se 1 (by rfl) ⟨713933, by rfl⟩ : syracuseStep 951911 = 1427867) B1427867
theorem B952991 : Blo 279826 952991 := bstep (se 1 (by rfl) ⟨714743, by rfl⟩ : syracuseStep 952991 = 1429487) B1429487
theorem B1805915 : Blo 279826 1805915 := bstep (se 1 (by rfl) ⟨1354436, by rfl⟩ : syracuseStep 1805915 = 2708873) B2708873
theorem B1348271 : Blo 279826 1348271 := bstep (se 1 (by rfl) ⟨1011203, by rfl⟩ : syracuseStep 1348271 = 2022407) B2022407
theorem B1708937 : Blo 279826 1708937 := bstep (se 2 (by rfl) ⟨640851, by rfl⟩ : syracuseStep 1708937 = 1281703) B1281703
theorem B955475 : Blo 279826 955475 := bstep (se 1 (by rfl) ⟨716606, by rfl⟩ : syracuseStep 955475 = 1433213) B1433213
theorem B955583 : Blo 279826 955583 := bstep (se 1 (by rfl) ⟨716687, by rfl⟩ : syracuseStep 955583 = 1433375) B1433375
theorem B760445 : Blo 279826 760445 := bstep (se 3 (by rfl) ⟨142583, by rfl⟩ : syracuseStep 760445 = 285167) B285167
theorem B2137427 : Blo 279826 2137427 := bstep (se 1 (by rfl) ⟨1603070, by rfl⟩ : syracuseStep 2137427 = 3206141) B3206141
theorem B630251 : Blo 279826 630251 := bstep (se 1 (by rfl) ⟨472688, by rfl⟩ : syracuseStep 630251 = 945377) B945377
theorem B249077551 : Blo 279826 249077551 := bstep (se 1 (by rfl) ⟨186808163, by rfl⟩ : syracuseStep 249077551 = 373616327) B373616327
theorem B532345 : Blo 279826 532345 := bstep (se 2 (by rfl) ⟨199629, by rfl⟩ : syracuseStep 532345 = 399259) B399259
theorem B1515833 : Blo 279826 1515833 := bstep (se 2 (by rfl) ⟨568437, by rfl⟩ : syracuseStep 1515833 = 1136875) B1136875
theorem B532975 : Blo 279826 532975 := bstep (se 1 (by rfl) ⟨399731, by rfl⟩ : syracuseStep 532975 = 799463) B799463
theorem B402203 : Blo 279826 402203 := bstep (se 1 (by rfl) ⟨301652, by rfl⟩ : syracuseStep 402203 = 603305) B603305
theorem B533567 : Blo 279826 533567 := bstep (se 1 (by rfl) ⟨400175, by rfl⟩ : syracuseStep 533567 = 800351) B800351
theorem B2073853 : Blo 279826 2073853 := bstep (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) B777695
theorem B632105 : Blo 279826 632105 := bstep (se 2 (by rfl) ⟨237039, by rfl⟩ : syracuseStep 632105 = 474079) B474079
theorem B861511 : Blo 279826 861511 := bstep (se 1 (by rfl) ⟨646133, by rfl⟩ : syracuseStep 861511 = 1292267) B1292267
theorem B599375 : Blo 279826 599375 := bstep (se 1 (by rfl) ⟨449531, by rfl⟩ : syracuseStep 599375 = 899063) B899063
theorem B8267437 : Blo 279826 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B3450563 : Blo 279826 3450563 := bstep (se 1 (by rfl) ⟨2587922, by rfl⟩ : syracuseStep 3450563 = 5175845) B5175845
theorem B633257 : Blo 279826 633257 := bstep (se 2 (by rfl) ⟨237471, by rfl⟩ : syracuseStep 633257 = 474943) B474943
theorem B633455 : Blo 279826 633455 := bstep (se 1 (by rfl) ⟨475091, by rfl⟩ : syracuseStep 633455 = 950183) B950183
theorem B633671 : Blo 279826 633671 := bstep (se 1 (by rfl) ⟨475253, by rfl⟩ : syracuseStep 633671 = 950507) B950507
theorem B3058519 : Blo 279826 3058519 := bstep (se 1 (by rfl) ⟨2293889, by rfl⟩ : syracuseStep 3058519 = 4587779) B4587779
theorem B8137691 : Blo 279826 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B535891 : Blo 279826 535891 := bstep (se 1 (by rfl) ⟨401918, by rfl⟩ : syracuseStep 535891 = 803837) B803837
theorem B3878441 : Blo 279826 3878441 := bstep (se 2 (by rfl) ⟨1454415, by rfl⟩ : syracuseStep 3878441 = 2908831) B2908831
theorem B13447037 : Blo 279826 13447037 := bstep (se 3 (by rfl) ⟨2521319, by rfl⟩ : syracuseStep 13447037 = 5042639) B5042639
theorem B765895 : Blo 279826 765895 := bstep (se 1 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 765895 = 1148843) B1148843
theorem B635219 : Blo 279826 635219 := bstep (se 1 (by rfl) ⟨476414, by rfl⟩ : syracuseStep 635219 = 952829) B952829
theorem B21181027 : Blo 279826 21181027 := bstep (se 1 (by rfl) ⟨15885770, by rfl⟩ : syracuseStep 21181027 = 31771541) B31771541
theorem B3519773 : Blo 279826 3519773 := bstep (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) B1319915
theorem B4961573 : Blo 279826 4961573 := bstep (se 4 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 4961573 = 930295) B930295
theorem B13284773 : Blo 279826 13284773 := bstep (se 4 (by rfl) ⟨1245447, by rfl⟩ : syracuseStep 13284773 = 2490895) B2490895
theorem B1029631 : Blo 279826 1029631 := bstep (se 1 (by rfl) ⟨772223, by rfl⟩ : syracuseStep 1029631 = 1544447) B1544447
theorem B472783 : Blo 279826 472783 := bstep (se 1 (by rfl) ⟨354587, by rfl⟩ : syracuseStep 472783 = 709175) B709175
theorem B801161 : Blo 279826 801161 := bstep (se 2 (by rfl) ⟨300435, by rfl⟩ : syracuseStep 801161 = 600871) B600871
theorem B1063307 : Blo 279826 1063307 := bstep (se 1 (by rfl) ⟨797480, by rfl⟩ : syracuseStep 1063307 = 1594961) B1594961
theorem B473863 : Blo 279826 473863 := bstep (se 1 (by rfl) ⟨355397, by rfl⟩ : syracuseStep 473863 = 710795) B710795
theorem B1064249 : Blo 279826 1064249 := bstep (se 2 (by rfl) ⟨399093, by rfl⟩ : syracuseStep 1064249 = 798187) B798187
theorem B1064735 : Blo 279826 1064735 := bstep (se 1 (by rfl) ⟨798551, by rfl⟩ : syracuseStep 1064735 = 1597103) B1597103
theorem B8699885 : Blo 279826 8699885 := bstep (se 3 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 8699885 = 3262457) B3262457
theorem B98321201 : Blo 279826 98321201 := bstep (se 2 (by rfl) ⟨36870450, by rfl⟩ : syracuseStep 98321201 = 73740901) B73740901
theorem B6341777 : Blo 279826 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B476543 : Blo 279826 476543 := bstep (se 1 (by rfl) ⟨357407, by rfl⟩ : syracuseStep 476543 = 714815) B714815
theorem B280039 : Blo 279826 280039 := bstep (se 1 (by rfl) ⟨210029, by rfl⟩ : syracuseStep 280039 = 420059) B420059
theorem B640487 : Blo 279826 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B476671 : Blo 279826 476671 := bstep (se 1 (by rfl) ⟨357503, by rfl⟩ : syracuseStep 476671 = 715007) B715007
theorem B280679 : Blo 279826 280679 := bstep (se 1 (by rfl) ⟨210509, by rfl⟩ : syracuseStep 280679 = 421019) B421019
theorem B280687 : Blo 279826 280687 := bstep (se 1 (by rfl) ⟨210515, by rfl⟩ : syracuseStep 280687 = 421031) B421031
theorem B903727 : Blo 279826 903727 := bstep (se 1 (by rfl) ⟨677795, by rfl⟩ : syracuseStep 903727 = 1355591) B1355591
theorem B281247 : Blo 279826 281247 := bstep (se 1 (by rfl) ⟨210935, by rfl⟩ : syracuseStep 281247 = 421871) B421871
theorem B281407 : Blo 279826 281407 := bstep (se 1 (by rfl) ⟨211055, by rfl⟩ : syracuseStep 281407 = 422111) B422111
theorem B281599 : Blo 279826 281599 := bstep (se 1 (by rfl) ⟨211199, by rfl⟩ : syracuseStep 281599 = 422399) B422399
theorem B478345 : Blo 279826 478345 := bstep (se 2 (by rfl) ⟨179379, by rfl⟩ : syracuseStep 478345 = 358759) B358759
theorem B478399 : Blo 279826 478399 := bstep (se 1 (by rfl) ⟨358799, by rfl⟩ : syracuseStep 478399 = 717599) B717599
theorem B282143 : Blo 279826 282143 := bstep (se 1 (by rfl) ⟨211607, by rfl⟩ : syracuseStep 282143 = 423215) B423215
theorem B11685509 : Blo 279826 11685509 := bstep (se 4 (by rfl) ⟨1095516, by rfl⟩ : syracuseStep 11685509 = 2191033) B2191033
theorem B282267 : Blo 279826 282267 := bstep (se 1 (by rfl) ⟨211700, by rfl⟩ : syracuseStep 282267 = 423401) B423401
theorem B282303 : Blo 279826 282303 := bstep (se 1 (by rfl) ⟨211727, by rfl⟩ : syracuseStep 282303 = 423455) B423455
theorem B1036001 : Blo 279826 1036001 := bstep (se 2 (by rfl) ⟨388500, by rfl⟩ : syracuseStep 1036001 = 777001) B777001
theorem B315247 : Blo 279826 315247 := bstep (se 1 (by rfl) ⟨236435, by rfl⟩ : syracuseStep 315247 = 472871) B472871
theorem B282847 : Blo 279826 282847 := bstep (se 1 (by rfl) ⟨212135, by rfl⟩ : syracuseStep 282847 = 424271) B424271
theorem B10244387 : Blo 279826 10244387 := bstep (se 1 (by rfl) ⟨7683290, by rfl⟩ : syracuseStep 10244387 = 15366581) B15366581
theorem B3559751 : Blo 279826 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B4608343 : Blo 279826 4608343 := bstep (se 1 (by rfl) ⟨3456257, by rfl⟩ : syracuseStep 4608343 = 6912515) B6912515
theorem B1593755 : Blo 279826 1593755 := bstep (se 1 (by rfl) ⟨1195316, by rfl⟩ : syracuseStep 1593755 = 2390633) B2390633
theorem B283327 : Blo 279826 283327 := bstep (se 1 (by rfl) ⟨212495, by rfl⟩ : syracuseStep 283327 = 424991) B424991
theorem B283751 : Blo 279826 283751 := bstep (se 1 (by rfl) ⟨212813, by rfl⟩ : syracuseStep 283751 = 425627) B425627
theorem B1660139 : Blo 279826 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B906751 : Blo 279826 906751 := bstep (se 1 (by rfl) ⟨680063, by rfl⟩ : syracuseStep 906751 = 1360127) B1360127
theorem B1431593 : Blo 279826 1431593 := bstep (se 2 (by rfl) ⟨536847, by rfl⟩ : syracuseStep 1431593 = 1073695) B1073695
theorem B907355 : Blo 279826 907355 := bstep (se 1 (by rfl) ⟨680516, by rfl⟩ : syracuseStep 907355 = 1361033) B1361033
theorem B2284807 : Blo 279826 2284807 := bstep (se 1 (by rfl) ⟨1713605, by rfl⟩ : syracuseStep 2284807 = 3427211) B3427211
theorem B1793819 : Blo 279826 1793819 := bstep (se 1 (by rfl) ⟨1345364, by rfl⟩ : syracuseStep 1793819 = 2690729) B2690729
theorem B1597421 : Blo 279826 1597421 := bstep (se 3 (by rfl) ⟨299516, by rfl⟩ : syracuseStep 1597421 = 599033) B599033
theorem B3661949 : Blo 279826 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B1106075 : Blo 279826 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B713083 : Blo 279826 713083 := bstep (se 1 (by rfl) ⟨534812, by rfl⟩ : syracuseStep 713083 = 1069625) B1069625
theorem B287551 : Blo 279826 287551 := bstep (se 1 (by rfl) ⟨215663, by rfl⟩ : syracuseStep 287551 = 431327) B431327
theorem B714217 : Blo 279826 714217 := bstep (se 2 (by rfl) ⟨267831, by rfl⟩ : syracuseStep 714217 = 535663) B535663
theorem B452351 : Blo 279826 452351 := bstep (se 1 (by rfl) ⟨339263, by rfl⟩ : syracuseStep 452351 = 678527) B678527
theorem B420095 : Blo 279826 420095 := bstep (se 1 (by rfl) ⟨315071, by rfl⟩ : syracuseStep 420095 = 630143) B630143
theorem B1075625 : Blo 279826 1075625 := bstep (se 2 (by rfl) ⟨403359, by rfl⟩ : syracuseStep 1075625 = 806719) B806719
theorem B944783 : Blo 279826 944783 := bstep (se 1 (by rfl) ⟨708587, by rfl⟩ : syracuseStep 944783 = 1417175) B1417175
theorem B420671 : Blo 279826 420671 := bstep (se 1 (by rfl) ⟨315503, by rfl⟩ : syracuseStep 420671 = 631007) B631007
theorem B453575 : Blo 279826 453575 := bstep (se 1 (by rfl) ⟨340181, by rfl⟩ : syracuseStep 453575 = 680363) B680363
theorem B715817 : Blo 279826 715817 := bstep (se 2 (by rfl) ⟨268431, by rfl⟩ : syracuseStep 715817 = 536863) B536863
theorem B1436777 : Blo 279826 1436777 := bstep (se 2 (by rfl) ⟨538791, by rfl⟩ : syracuseStep 1436777 = 1077583) B1077583
theorem B420971 : Blo 279826 420971 := bstep (se 1 (by rfl) ⟨315728, by rfl⟩ : syracuseStep 420971 = 631457) B631457
theorem B7203977 : Blo 279826 7203977 := bstep (se 2 (by rfl) ⟨2701491, by rfl⟩ : syracuseStep 7203977 = 5402983) B5402983
theorem B421355 : Blo 279826 421355 := bstep (se 1 (by rfl) ⟨316016, by rfl⟩ : syracuseStep 421355 = 632033) B632033
theorem B421535 : Blo 279826 421535 := bstep (se 1 (by rfl) ⟨316151, by rfl⟩ : syracuseStep 421535 = 632303) B632303
theorem B945917 : Blo 279826 945917 := bstep (se 3 (by rfl) ⟨177359, by rfl⟩ : syracuseStep 945917 = 354719) B354719
theorem B421799 : Blo 279826 421799 := bstep (se 1 (by rfl) ⟨316349, by rfl⟩ : syracuseStep 421799 = 632699) B632699
theorem B421823 : Blo 279826 421823 := bstep (se 1 (by rfl) ⟨316367, by rfl⟩ : syracuseStep 421823 = 632735) B632735
theorem B6811685 : Blo 279826 6811685 := bstep (se 4 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 6811685 = 1277191) B1277191
theorem B422687 : Blo 279826 422687 := bstep (se 1 (by rfl) ⟨317015, by rfl⟩ : syracuseStep 422687 = 634031) B634031
theorem B423167 : Blo 279826 423167 := bstep (se 1 (by rfl) ⟨317375, by rfl⟩ : syracuseStep 423167 = 634751) B634751
theorem B423209 : Blo 279826 423209 := bstep (se 2 (by rfl) ⟨158703, by rfl⟩ : syracuseStep 423209 = 317407) B317407
theorem B3209057 : Blo 279826 3209057 := bstep (se 2 (by rfl) ⟨1203396, by rfl⟩ : syracuseStep 3209057 = 2406793) B2406793
theorem B4061123 : Blo 279826 4061123 := bstep (se 1 (by rfl) ⟨3045842, by rfl⟩ : syracuseStep 4061123 = 6091685) B6091685
theorem B424073 : Blo 279826 424073 := bstep (se 2 (by rfl) ⟨159027, by rfl⟩ : syracuseStep 424073 = 318055) B318055
theorem B948617 : Blo 279826 948617 := bstep (se 2 (by rfl) ⟨355731, by rfl⟩ : syracuseStep 948617 = 711463) B711463
theorem B424895 : Blo 279826 424895 := bstep (se 1 (by rfl) ⟨318671, by rfl⟩ : syracuseStep 424895 = 637343) B637343
theorem B425087 : Blo 279826 425087 := bstep (se 1 (by rfl) ⟨318815, by rfl⟩ : syracuseStep 425087 = 637631) B637631
theorem B1703119 : Blo 279826 1703119 := bstep (se 1 (by rfl) ⟨1277339, by rfl⟩ : syracuseStep 1703119 = 2554679) B2554679
theorem B8289869 : Blo 279826 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B425723 : Blo 279826 425723 := bstep (se 1 (by rfl) ⟨319292, by rfl⟩ : syracuseStep 425723 = 638585) B638585
theorem B1048391 : Blo 279826 1048391 := bstep (se 1 (by rfl) ⟨786293, by rfl⟩ : syracuseStep 1048391 = 1572587) B1572587
theorem B9765197 : Blo 279826 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B2949533 : Blo 279826 2949533 := bstep (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) B1106075
theorem B950777 : Blo 279826 950777 := bstep (se 2 (by rfl) ⟨356541, by rfl⟩ : syracuseStep 950777 = 713083) B713083
theorem B4227851 : Blo 279826 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B17434217 : Blo 279826 17434217 := bstep (se 2 (by rfl) ⟨6537831, by rfl⟩ : syracuseStep 17434217 = 13075663) B13075663
theorem B1148681 : Blo 279826 1148681 := bstep (se 2 (by rfl) ⟨430755, by rfl⟩ : syracuseStep 1148681 = 861511) B861511
theorem B952289 : Blo 279826 952289 := bstep (se 2 (by rfl) ⟨357108, by rfl⟩ : syracuseStep 952289 = 714217) B714217
theorem B1707965 : Blo 279826 1707965 := bstep (se 3 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 1707965 = 640487) B640487
theorem B954395 : Blo 279826 954395 := bstep (se 1 (by rfl) ⟨715796, by rfl⟩ : syracuseStep 954395 = 1431593) B1431593
theorem B1021193 : Blo 279826 1021193 := bstep (se 2 (by rfl) ⟨382947, by rfl⟩ : syracuseStep 1021193 = 765895) B765895
theorem B399583 : Blo 279826 399583 := bstep (se 1 (by rfl) ⟨299687, by rfl⟩ : syracuseStep 399583 = 599375) B599375
theorem B2300375 : Blo 279826 2300375 := bstep (se 1 (by rfl) ⟨1725281, by rfl⟩ : syracuseStep 2300375 = 3450563) B3450563
theorem B301567 : Blo 279826 301567 := bstep (se 1 (by rfl) ⟨226175, by rfl⟩ : syracuseStep 301567 = 452351) B452351
theorem B629855 : Blo 279826 629855 := bstep (se 1 (by rfl) ⟨472391, by rfl⟩ : syracuseStep 629855 = 944783) B944783
theorem B302383 : Blo 279826 302383 := bstep (se 1 (by rfl) ⟨226787, by rfl⟩ : syracuseStep 302383 = 453575) B453575
theorem B957851 : Blo 279826 957851 := bstep (se 1 (by rfl) ⟨718388, by rfl⟩ : syracuseStep 957851 = 1436777) B1436777
theorem B630377 : Blo 279826 630377 := bstep (se 2 (by rfl) ⟨236391, by rfl⟩ : syracuseStep 630377 = 472783) B472783
theorem B630611 : Blo 279826 630611 := bstep (se 1 (by rfl) ⟨472958, by rfl⟩ : syracuseStep 630611 = 945917) B945917
theorem B8856515 : Blo 279826 8856515 := bstep (se 1 (by rfl) ⟨6642386, by rfl⟩ : syracuseStep 8856515 = 13284773) B13284773
theorem B631817 : Blo 279826 631817 := bstep (se 2 (by rfl) ⟨236931, by rfl⟩ : syracuseStep 631817 = 473863) B473863
theorem B2139371 : Blo 279826 2139371 := bstep (se 1 (by rfl) ⟨1604528, by rfl⟩ : syracuseStep 2139371 = 3209057) B3209057
theorem B632411 : Blo 279826 632411 := bstep (se 1 (by rfl) ⟨474308, by rfl⟩ : syracuseStep 632411 = 948617) B948617
theorem B534107 : Blo 279826 534107 := bstep (se 1 (by rfl) ⟨400580, by rfl⟩ : syracuseStep 534107 = 801161) B801161
theorem B2270825 : Blo 279826 2270825 := bstep (se 2 (by rfl) ⟨851559, by rfl⟩ : syracuseStep 2270825 = 1703119) B1703119
theorem B2762669 : Blo 279826 2762669 := bstep (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) B1036001
theorem B35858765 : Blo 279826 35858765 := bstep (se 3 (by rfl) ⟨6723518, by rfl⟩ : syracuseStep 35858765 = 13447037) B13447037
theorem B698927 : Blo 279826 698927 := bstep (se 1 (by rfl) ⟨524195, by rfl⟩ : syracuseStep 698927 = 1048391) B1048391
theorem B65547467 : Blo 279826 65547467 := bstep (se 1 (by rfl) ⟨49160600, by rfl⟩ : syracuseStep 65547467 = 98321201) B98321201
theorem B2403755 : Blo 279826 2403755 := bstep (se 1 (by rfl) ⟨1802816, by rfl⟩ : syracuseStep 2403755 = 3605633) B3605633
theorem B634283 : Blo 279826 634283 := bstep (se 1 (by rfl) ⟨475712, by rfl⟩ : syracuseStep 634283 = 951425) B951425
theorem B634607 : Blo 279826 634607 := bstep (se 1 (by rfl) ⟨475955, by rfl⟩ : syracuseStep 634607 = 951911) B951911
theorem B2765137 : Blo 279826 2765137 := bstep (se 2 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 2765137 = 2073853) B2073853
theorem B635327 : Blo 279826 635327 := bstep (se 1 (by rfl) ⟨476495, by rfl⟩ : syracuseStep 635327 = 952991) B952991
theorem B635561 : Blo 279826 635561 := bstep (se 2 (by rfl) ⟨238335, by rfl⟩ : syracuseStep 635561 = 476671) B476671
theorem B3191561 : Blo 279826 3191561 := bstep (se 2 (by rfl) ⟨1196835, by rfl⟩ : syracuseStep 3191561 = 2393671) B2393671
theorem B1422845 : Blo 279826 1422845 := bstep (se 3 (by rfl) ⟨266783, by rfl⟩ : syracuseStep 1422845 = 533567) B533567
theorem B6829591 : Blo 279826 6829591 := bstep (se 1 (by rfl) ⟨5122193, by rfl⟩ : syracuseStep 6829591 = 10244387) B10244387
theorem B2373167 : Blo 279826 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B1062503 : Blo 279826 1062503 := bstep (se 1 (by rfl) ⟨796877, by rfl⟩ : syracuseStep 1062503 = 1593755) B1593755
theorem B898847 : Blo 279826 898847 := bstep (se 1 (by rfl) ⟨674135, by rfl⟩ : syracuseStep 898847 = 1348271) B1348271
theorem B636983 : Blo 279826 636983 := bstep (se 1 (by rfl) ⟨477737, by rfl⟩ : syracuseStep 636983 = 955475) B955475
theorem B637055 : Blo 279826 637055 := bstep (se 1 (by rfl) ⟨477791, by rfl⟩ : syracuseStep 637055 = 955583) B955583
theorem B4078025 : Blo 279826 4078025 := bstep (se 2 (by rfl) ⟨1529259, by rfl⟩ : syracuseStep 4078025 = 3058519) B3058519
theorem B604903 : Blo 279826 604903 := bstep (se 1 (by rfl) ⟨453677, by rfl⟩ : syracuseStep 604903 = 907355) B907355
theorem B637793 : Blo 279826 637793 := bstep (se 2 (by rfl) ⟨239172, by rfl⟩ : syracuseStep 637793 = 478345) B478345
theorem B637865 : Blo 279826 637865 := bstep (se 2 (by rfl) ⟨239199, by rfl⟩ : syracuseStep 637865 = 478399) B478399
theorem B506963 : Blo 279826 506963 := bstep (se 1 (by rfl) ⟨380222, by rfl⟩ : syracuseStep 506963 = 760445) B760445
theorem B1424951 : Blo 279826 1424951 := bstep (se 1 (by rfl) ⟨1068713, by rfl⟩ : syracuseStep 1424951 = 2137427) B2137427
theorem B1195879 : Blo 279826 1195879 := bstep (se 1 (by rfl) ⟨896909, by rfl⟩ : syracuseStep 1195879 = 1793819) B1793819
theorem B1064947 : Blo 279826 1064947 := bstep (se 1 (by rfl) ⟨798710, by rfl⟩ : syracuseStep 1064947 = 1597421) B1597421
theorem B6144457 : Blo 279826 6144457 := bstep (se 2 (by rfl) ⟨2304171, by rfl⟩ : syracuseStep 6144457 = 4608343) B4608343
theorem B280063 : Blo 279826 280063 := bstep (se 1 (by rfl) ⟨210047, by rfl⟩ : syracuseStep 280063 = 420095) B420095
theorem B280447 : Blo 279826 280447 := bstep (se 1 (by rfl) ⟨210335, by rfl⟩ : syracuseStep 280447 = 420671) B420671
theorem B5425127 : Blo 279826 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B477211 : Blo 279826 477211 := bstep (se 1 (by rfl) ⟨357908, by rfl⟩ : syracuseStep 477211 = 715817) B715817
theorem B280647 : Blo 279826 280647 := bstep (se 1 (by rfl) ⟨210485, by rfl⟩ : syracuseStep 280647 = 420971) B420971
theorem B4802651 : Blo 279826 4802651 := bstep (se 1 (by rfl) ⟨3601988, by rfl⟩ : syracuseStep 4802651 = 7203977) B7203977
theorem B280903 : Blo 279826 280903 := bstep (se 1 (by rfl) ⟨210677, by rfl⟩ : syracuseStep 280903 = 421355) B421355
theorem B281023 : Blo 279826 281023 := bstep (se 1 (by rfl) ⟨210767, by rfl⟩ : syracuseStep 281023 = 421535) B421535
theorem B281199 : Blo 279826 281199 := bstep (se 1 (by rfl) ⟨210899, by rfl⟩ : syracuseStep 281199 = 421799) B421799
theorem B281215 : Blo 279826 281215 := bstep (se 1 (by rfl) ⟨210911, by rfl⟩ : syracuseStep 281215 = 421823) B421823
theorem B4541123 : Blo 279826 4541123 := bstep (se 1 (by rfl) ⟨3405842, by rfl⟩ : syracuseStep 4541123 = 6811685) B6811685
theorem B281791 : Blo 279826 281791 := bstep (se 1 (by rfl) ⟨211343, by rfl⟩ : syracuseStep 281791 = 422687) B422687
theorem B282111 : Blo 279826 282111 := bstep (se 1 (by rfl) ⟨211583, by rfl⟩ : syracuseStep 282111 = 423167) B423167
theorem B2346515 : Blo 279826 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B282139 : Blo 279826 282139 := bstep (se 1 (by rfl) ⟨211604, by rfl⟩ : syracuseStep 282139 = 423209) B423209
theorem B44092997 : Blo 279826 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B2707415 : Blo 279826 2707415 := bstep (se 1 (by rfl) ⟨2030561, by rfl⟩ : syracuseStep 2707415 = 4061123) B4061123
theorem B282715 : Blo 279826 282715 := bstep (se 1 (by rfl) ⟨212036, by rfl⟩ : syracuseStep 282715 = 424073) B424073
theorem B22106317 : Blo 279826 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B708871 : Blo 279826 708871 := bstep (se 1 (by rfl) ⟨531653, by rfl⟩ : syracuseStep 708871 = 1063307) B1063307
theorem B283263 : Blo 279826 283263 := bstep (se 1 (by rfl) ⟨212447, by rfl⟩ : syracuseStep 283263 = 424895) B424895
theorem B283391 : Blo 279826 283391 := bstep (se 1 (by rfl) ⟨212543, by rfl⟩ : syracuseStep 283391 = 425087) B425087
theorem B709499 : Blo 279826 709499 := bstep (se 1 (by rfl) ⟨532124, by rfl⟩ : syracuseStep 709499 = 1064249) B1064249
theorem B709793 : Blo 279826 709793 := bstep (se 2 (by rfl) ⟨266172, by rfl⟩ : syracuseStep 709793 = 532345) B532345
theorem B283815 : Blo 279826 283815 := bstep (se 1 (by rfl) ⟨212861, by rfl⟩ : syracuseStep 283815 = 425723) B425723
theorem B709823 : Blo 279826 709823 := bstep (se 1 (by rfl) ⟨532367, by rfl⟩ : syracuseStep 709823 = 1064735) B1064735
theorem B1201655 : Blo 279826 1201655 := bstep (se 1 (by rfl) ⟨901241, by rfl⟩ : syracuseStep 1201655 = 1802483) B1802483
theorem B710633 : Blo 279826 710633 := bstep (se 2 (by rfl) ⟨266487, by rfl⟩ : syracuseStep 710633 = 532975) B532975
theorem B317695 : Blo 279826 317695 := bstep (se 1 (by rfl) ⟨238271, by rfl⟩ : syracuseStep 317695 = 476543) B476543
theorem B2709875 : Blo 279826 2709875 := bstep (se 1 (by rfl) ⟨2032406, by rfl⟩ : syracuseStep 2709875 = 4064813) B4064813
theorem B383401 : Blo 279826 383401 := bstep (se 2 (by rfl) ⟨143775, by rfl⟩ : syracuseStep 383401 = 287551) B287551
theorem B1072541 : Blo 279826 1072541 := bstep (se 3 (by rfl) ⟨201101, by rfl⟩ : syracuseStep 1072541 = 402203) B402203
theorem B7790339 : Blo 279826 7790339 := bstep (se 1 (by rfl) ⟨5842754, by rfl⟩ : syracuseStep 7790339 = 11685509) B11685509
theorem B1139291 : Blo 279826 1139291 := bstep (se 1 (by rfl) ⟨854468, by rfl⟩ : syracuseStep 1139291 = 1708937) B1708937
theorem B1204969 : Blo 279826 1204969 := bstep (se 2 (by rfl) ⟨451863, by rfl⟩ : syracuseStep 1204969 = 903727) B903727
theorem B1106759 : Blo 279826 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B47539061 : Blo 279826 47539061 := bstep (se 5 (by rfl) ⟨2228393, by rfl⟩ : syracuseStep 47539061 = 4456787) B4456787
theorem B714521 : Blo 279826 714521 := bstep (se 2 (by rfl) ⟨267945, by rfl⟩ : syracuseStep 714521 = 535891) B535891
theorem B420167 : Blo 279826 420167 := bstep (se 1 (by rfl) ⟨315125, by rfl⟩ : syracuseStep 420167 = 630251) B630251
theorem B420329 : Blo 279826 420329 := bstep (se 2 (by rfl) ⟨157623, by rfl⟩ : syracuseStep 420329 = 315247) B315247
theorem B1010555 : Blo 279826 1010555 := bstep (se 1 (by rfl) ⟨757916, by rfl⟩ : syracuseStep 1010555 = 1515833) B1515833
theorem B28241369 : Blo 279826 28241369 := bstep (se 2 (by rfl) ⟨10590513, by rfl⟩ : syracuseStep 28241369 = 21181027) B21181027
theorem B421403 : Blo 279826 421403 := bstep (se 1 (by rfl) ⟨316052, by rfl⟩ : syracuseStep 421403 = 632105) B632105
theorem B422171 : Blo 279826 422171 := bstep (se 1 (by rfl) ⟨316628, by rfl⟩ : syracuseStep 422171 = 633257) B633257
theorem B717083 : Blo 279826 717083 := bstep (se 1 (by rfl) ⟨537812, by rfl⟩ : syracuseStep 717083 = 1075625) B1075625
theorem B422303 : Blo 279826 422303 := bstep (se 1 (by rfl) ⟨316727, by rfl⟩ : syracuseStep 422303 = 633455) B633455
theorem B422447 : Blo 279826 422447 := bstep (se 1 (by rfl) ⟨316835, by rfl⟩ : syracuseStep 422447 = 633671) B633671
theorem B1372841 : Blo 279826 1372841 := bstep (se 2 (by rfl) ⟨514815, by rfl⟩ : syracuseStep 1372841 = 1029631) B1029631
theorem B1209001 : Blo 279826 1209001 := bstep (se 2 (by rfl) ⟨453375, by rfl⟩ : syracuseStep 1209001 = 906751) B906751
theorem B2585627 : Blo 279826 2585627 := bstep (se 1 (by rfl) ⟨1939220, by rfl⟩ : syracuseStep 2585627 = 3878441) B3878441
theorem B423479 : Blo 279826 423479 := bstep (se 1 (by rfl) ⟨317609, by rfl⟩ : syracuseStep 423479 = 635219) B635219
theorem B3307715 : Blo 279826 3307715 := bstep (se 1 (by rfl) ⟨2480786, by rfl⟩ : syracuseStep 3307715 = 4961573) B4961573
theorem B4815773 : Blo 279826 4815773 := bstep (se 3 (by rfl) ⟨902957, by rfl⟩ : syracuseStep 4815773 = 1805915) B1805915
theorem B3046409 : Blo 279826 3046409 := bstep (se 2 (by rfl) ⟨1142403, by rfl⟩ : syracuseStep 3046409 = 2284807) B2284807
theorem B332103401 : Blo 279826 332103401 := bstep (se 2 (by rfl) ⟨124538775, by rfl⟩ : syracuseStep 332103401 = 249077551) B249077551
theorem B5799923 : Blo 279826 5799923 := bstep (se 1 (by rfl) ⟨4349942, by rfl⟩ : syracuseStep 5799923 = 8699885) B8699885
theorem B1966355 : Blo 279826 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B2818567 : Blo 279826 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B8192609 : Blo 279826 8192609 := bstep (se 2 (by rfl) ⟨3072228, by rfl⟩ : syracuseStep 8192609 = 6144457) B6144457
theorem B1606625 : Blo 279826 1606625 := bstep (se 2 (by rfl) ⟨602484, by rfl⟩ : syracuseStep 1606625 = 1204969) B1204969
theorem B2131109 : Blo 279826 2131109 := bstep (se 4 (by rfl) ⟨199791, by rfl⟩ : syracuseStep 2131109 = 399583) B399583
theorem B29395331 : Blo 279826 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B1804943 : Blo 279826 1804943 := bstep (se 1 (by rfl) ⟨1353707, by rfl⟩ : syracuseStep 1804943 = 2707415) B2707415
theorem B1806583 : Blo 279826 1806583 := bstep (se 1 (by rfl) ⟨1354937, by rfl⟩ : syracuseStep 1806583 = 2709875) B2709875
theorem B759527 : Blo 279826 759527 := bstep (se 1 (by rfl) ⟨569645, by rfl⟩ : syracuseStep 759527 = 1139291) B1139291
theorem B31692707 : Blo 279826 31692707 := bstep (se 1 (by rfl) ⟨23769530, by rfl⟩ : syracuseStep 31692707 = 47539061) B47539061
theorem B5904343 : Blo 279826 5904343 := bstep (se 1 (by rfl) ⟨4428257, by rfl⟩ : syracuseStep 5904343 = 8856515) B8856515
theorem B1612001 : Blo 279826 1612001 := bstep (se 2 (by rfl) ⟨604500, by rfl⟩ : syracuseStep 1612001 = 1209001) B1209001
theorem B1513883 : Blo 279826 1513883 := bstep (se 1 (by rfl) ⟨1135412, by rfl⟩ : syracuseStep 1513883 = 2270825) B2270825
theorem B1841779 : Blo 279826 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B1612709 : Blo 279826 1612709 := bstep (se 4 (by rfl) ⟨151191, by rfl⟩ : syracuseStep 1612709 = 302383) B302383
theorem B402089 : Blo 279826 402089 := bstep (se 2 (by rfl) ⟨150783, by rfl⟩ : syracuseStep 402089 = 301567) B301567
theorem B1582111 : Blo 279826 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B599231 : Blo 279826 599231 := bstep (se 1 (by rfl) ⟨449423, by rfl⟩ : syracuseStep 599231 = 898847) B898847
theorem B2205143 : Blo 279826 2205143 := bstep (se 1 (by rfl) ⟨1653857, by rfl⟩ : syracuseStep 2205143 = 3307715) B3307715
theorem B337975 : Blo 279826 337975 := bstep (se 1 (by rfl) ⟨253481, by rfl⟩ : syracuseStep 337975 = 506963) B506963
theorem B1419929 : Blo 279826 1419929 := bstep (se 2 (by rfl) ⟨532473, by rfl⟩ : syracuseStep 1419929 = 1064947) B1064947
theorem B633851 : Blo 279826 633851 := bstep (se 1 (by rfl) ⟨475388, by rfl⟩ : syracuseStep 633851 = 950777) B950777
theorem B765787 : Blo 279826 765787 := bstep (se 1 (by rfl) ⟨574340, by rfl⟩ : syracuseStep 765787 = 1148681) B1148681
theorem B634859 : Blo 279826 634859 := bstep (se 1 (by rfl) ⟨476144, by rfl⟩ : syracuseStep 634859 = 952289) B952289
theorem B3616751 : Blo 279826 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B636263 : Blo 279826 636263 := bstep (se 1 (by rfl) ⟨477197, by rfl⟩ : syracuseStep 636263 = 954395) B954395
theorem B636281 : Blo 279826 636281 := bstep (se 2 (by rfl) ⟨238605, by rfl⟩ : syracuseStep 636281 = 477211) B477211
theorem B472999 : Blo 279826 472999 := bstep (se 1 (by rfl) ⟨354749, by rfl⟩ : syracuseStep 472999 = 709499) B709499
theorem B473195 : Blo 279826 473195 := bstep (se 1 (by rfl) ⟨354896, by rfl⟩ : syracuseStep 473195 = 709793) B709793
theorem B473215 : Blo 279826 473215 := bstep (se 1 (by rfl) ⟨354911, by rfl⟩ : syracuseStep 473215 = 709823) B709823
theorem B801103 : Blo 279826 801103 := bstep (se 1 (by rfl) ⟨600827, by rfl⟩ : syracuseStep 801103 = 1201655) B1201655
theorem B473755 : Blo 279826 473755 := bstep (se 1 (by rfl) ⟨355316, by rfl⟩ : syracuseStep 473755 = 710633) B710633
theorem B638567 : Blo 279826 638567 := bstep (se 1 (by rfl) ⟨478925, by rfl⟩ : syracuseStep 638567 = 957851) B957851
theorem B5193559 : Blo 279826 5193559 := bstep (se 1 (by rfl) ⟨3895169, by rfl⟩ : syracuseStep 5193559 = 7790339) B7790339
theorem B29475089 : Blo 279826 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B3686849 : Blo 279826 3686849 := bstep (se 2 (by rfl) ⟨1382568, by rfl⟩ : syracuseStep 3686849 = 2765137) B2765137
theorem B737839 : Blo 279826 737839 := bstep (se 1 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 737839 = 1106759) B1106759
theorem B1426247 : Blo 279826 1426247 := bstep (se 1 (by rfl) ⟨1069685, by rfl⟩ : syracuseStep 1426247 = 2139371) B2139371
theorem B476347 : Blo 279826 476347 := bstep (se 1 (by rfl) ⟨357260, by rfl⟩ : syracuseStep 476347 = 714521) B714521
theorem B280111 : Blo 279826 280111 := bstep (se 1 (by rfl) ⟨210083, by rfl⟩ : syracuseStep 280111 = 420167) B420167
theorem B23905843 : Blo 279826 23905843 := bstep (se 1 (by rfl) ⟨17929382, by rfl⟩ : syracuseStep 23905843 = 35858765) B35858765
theorem B280219 : Blo 279826 280219 := bstep (se 1 (by rfl) ⟨210164, by rfl⟩ : syracuseStep 280219 = 420329) B420329
theorem B12109661 : Blo 279826 12109661 := bstep (se 3 (by rfl) ⟨2270561, by rfl⟩ : syracuseStep 12109661 = 4541123) B4541123
theorem B673703 : Blo 279826 673703 := bstep (se 1 (by rfl) ⟨505277, by rfl⟩ : syracuseStep 673703 = 1010555) B1010555
theorem B43698311 : Blo 279826 43698311 := bstep (se 1 (by rfl) ⟨32773733, by rfl⟩ : syracuseStep 43698311 = 65547467) B65547467
theorem B18827579 : Blo 279826 18827579 := bstep (se 1 (by rfl) ⟨14120684, by rfl⟩ : syracuseStep 18827579 = 28241369) B28241369
theorem B280935 : Blo 279826 280935 := bstep (se 1 (by rfl) ⟨210701, by rfl⟩ : syracuseStep 280935 = 421403) B421403
theorem B281447 : Blo 279826 281447 := bstep (se 1 (by rfl) ⟨211085, by rfl⟩ : syracuseStep 281447 = 422171) B422171
theorem B478055 : Blo 279826 478055 := bstep (se 1 (by rfl) ⟨358541, by rfl⟩ : syracuseStep 478055 = 717083) B717083
theorem B281535 : Blo 279826 281535 := bstep (se 1 (by rfl) ⟨211151, by rfl⟩ : syracuseStep 281535 = 422303) B422303
theorem B281631 : Blo 279826 281631 := bstep (se 1 (by rfl) ⟨211223, by rfl⟩ : syracuseStep 281631 = 422447) B422447
theorem B511201 : Blo 279826 511201 := bstep (se 2 (by rfl) ⟨191700, by rfl⟩ : syracuseStep 511201 = 383401) B383401
theorem B1723751 : Blo 279826 1723751 := bstep (se 1 (by rfl) ⟨1292813, by rfl⟩ : syracuseStep 1723751 = 2585627) B2585627
theorem B806537 : Blo 279826 806537 := bstep (se 2 (by rfl) ⟨302451, by rfl⟩ : syracuseStep 806537 = 604903) B604903
theorem B282319 : Blo 279826 282319 := bstep (se 1 (by rfl) ⟨211739, by rfl⟩ : syracuseStep 282319 = 423479) B423479
theorem B708335 : Blo 279826 708335 := bstep (se 1 (by rfl) ⟨531251, by rfl⟩ : syracuseStep 708335 = 1062503) B1062503
theorem B1594505 : Blo 279826 1594505 := bstep (se 2 (by rfl) ⟨597939, by rfl⟩ : syracuseStep 1594505 = 1195879) B1195879
theorem B221402267 : Blo 279826 221402267 := bstep (se 1 (by rfl) ⟨166051700, by rfl⟩ : syracuseStep 221402267 = 332103401) B332103401
theorem B6510131 : Blo 279826 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B3201767 : Blo 279826 3201767 := bstep (se 1 (by rfl) ⟨2401325, by rfl⟩ : syracuseStep 3201767 = 4802651) B4802651
theorem B1564343 : Blo 279826 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B1138643 : Blo 279826 1138643 := bstep (se 1 (by rfl) ⟨853982, by rfl⟩ : syracuseStep 1138643 = 1707965) B1707965
theorem B680795 : Blo 279826 680795 := bstep (se 1 (by rfl) ⟨510596, by rfl⟩ : syracuseStep 680795 = 1021193) B1021193
theorem B46491245 : Blo 279826 46491245 := bstep (se 3 (by rfl) ⟨8717108, by rfl⟩ : syracuseStep 46491245 = 17434217) B17434217
theorem B1533583 : Blo 279826 1533583 := bstep (se 1 (by rfl) ⟨1150187, by rfl⟩ : syracuseStep 1533583 = 2300375) B2300375
theorem B419903 : Blo 279826 419903 := bstep (se 1 (by rfl) ⟨314927, by rfl⟩ : syracuseStep 419903 = 629855) B629855
theorem B715027 : Blo 279826 715027 := bstep (se 1 (by rfl) ⟨536270, by rfl⟩ : syracuseStep 715027 = 1072541) B1072541
theorem B420251 : Blo 279826 420251 := bstep (se 1 (by rfl) ⟨315188, by rfl⟩ : syracuseStep 420251 = 630377) B630377
theorem B420407 : Blo 279826 420407 := bstep (se 1 (by rfl) ⟨315305, by rfl⟩ : syracuseStep 420407 = 630611) B630611
theorem B945161 : Blo 279826 945161 := bstep (se 2 (by rfl) ⟨354435, by rfl⟩ : syracuseStep 945161 = 708871) B708871
theorem B421211 : Blo 279826 421211 := bstep (se 1 (by rfl) ⟨315908, by rfl⟩ : syracuseStep 421211 = 631817) B631817
theorem B421607 : Blo 279826 421607 := bstep (se 1 (by rfl) ⟨316205, by rfl⟩ : syracuseStep 421607 = 632411) B632411
theorem B356071 : Blo 279826 356071 := bstep (se 1 (by rfl) ⟨267053, by rfl⟩ : syracuseStep 356071 = 534107) B534107
theorem B1863805 : Blo 279826 1863805 := bstep (se 3 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 1863805 = 698927) B698927
theorem B9106121 : Blo 279826 9106121 := bstep (se 2 (by rfl) ⟨3414795, by rfl⟩ : syracuseStep 9106121 = 6829591) B6829591
theorem B1602503 : Blo 279826 1602503 := bstep (se 1 (by rfl) ⟨1201877, by rfl⟩ : syracuseStep 1602503 = 2403755) B2403755
theorem B422855 : Blo 279826 422855 := bstep (se 1 (by rfl) ⟨317141, by rfl⟩ : syracuseStep 422855 = 634283) B634283
theorem B423071 : Blo 279826 423071 := bstep (se 1 (by rfl) ⟨317303, by rfl⟩ : syracuseStep 423071 = 634607) B634607
theorem B423551 : Blo 279826 423551 := bstep (se 1 (by rfl) ⟨317663, by rfl⟩ : syracuseStep 423551 = 635327) B635327
theorem B423593 : Blo 279826 423593 := bstep (se 2 (by rfl) ⟨158847, by rfl⟩ : syracuseStep 423593 = 317695) B317695
theorem B915227 : Blo 279826 915227 := bstep (se 1 (by rfl) ⟨686420, by rfl⟩ : syracuseStep 915227 = 1372841) B1372841
theorem B423707 : Blo 279826 423707 := bstep (se 1 (by rfl) ⟨317780, by rfl⟩ : syracuseStep 423707 = 635561) B635561
theorem B2127707 : Blo 279826 2127707 := bstep (se 1 (by rfl) ⟨1595780, by rfl⟩ : syracuseStep 2127707 = 3191561) B3191561
theorem B948563 : Blo 279826 948563 := bstep (se 1 (by rfl) ⟨711422, by rfl⟩ : syracuseStep 948563 = 1422845) B1422845
theorem B424655 : Blo 279826 424655 := bstep (se 1 (by rfl) ⟨318491, by rfl⟩ : syracuseStep 424655 = 636983) B636983
theorem B424703 : Blo 279826 424703 := bstep (se 1 (by rfl) ⟨318527, by rfl⟩ : syracuseStep 424703 = 637055) B637055
theorem B2718683 : Blo 279826 2718683 := bstep (se 1 (by rfl) ⟨2039012, by rfl⟩ : syracuseStep 2718683 = 4078025) B4078025
theorem B425195 : Blo 279826 425195 := bstep (se 1 (by rfl) ⟨318896, by rfl⟩ : syracuseStep 425195 = 637793) B637793
theorem B3210515 : Blo 279826 3210515 := bstep (se 1 (by rfl) ⟨2407886, by rfl⟩ : syracuseStep 3210515 = 4815773) B4815773
theorem B425243 : Blo 279826 425243 := bstep (se 1 (by rfl) ⟨318932, by rfl⟩ : syracuseStep 425243 = 637865) B637865
theorem B2030939 : Blo 279826 2030939 := bstep (se 1 (by rfl) ⟨1523204, by rfl⟩ : syracuseStep 2030939 = 3046409) B3046409
theorem B949967 : Blo 279826 949967 := bstep (se 1 (by rfl) ⟨712475, by rfl⟩ : syracuseStep 949967 = 1424951) B1424951
theorem B3866615 : Blo 279826 3866615 := bstep (se 1 (by rfl) ⟨2899961, by rfl⟩ : syracuseStep 3866615 = 5799923) B5799923
theorem B1310903 : Blo 279826 1310903 := bstep (se 1 (by rfl) ⟨983177, by rfl⟩ : syracuseStep 1310903 = 1966355) B1966355
theorem B1802533 : Blo 279826 1802533 := bstep (se 4 (by rfl) ⟨168987, by rfl⟩ : syracuseStep 1802533 = 337975) B337975
theorem B2457899 : Blo 279826 2457899 := bstep (se 1 (by rfl) ⟨1843424, by rfl⟩ : syracuseStep 2457899 = 3686849) B3686849
theorem B950831 : Blo 279826 950831 := bstep (se 1 (by rfl) ⟨713123, by rfl⟩ : syracuseStep 950831 = 1426247) B1426247
theorem B29132207 : Blo 279826 29132207 := bstep (se 1 (by rfl) ⟨21849155, by rfl⟩ : syracuseStep 29132207 = 43698311) B43698311
theorem B19596887 : Blo 279826 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B1149167 : Blo 279826 1149167 := bstep (se 1 (by rfl) ⟨861875, by rfl⟩ : syracuseStep 1149167 = 1723751) B1723751
theorem B3935141 : Blo 279826 3935141 := bstep (se 4 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 3935141 = 737839) B737839
theorem B953369 : Blo 279826 953369 := bstep (se 2 (by rfl) ⟨357513, by rfl⟩ : syracuseStep 953369 = 715027) B715027
theorem B2134511 : Blo 279826 2134511 := bstep (se 1 (by rfl) ⟨1600883, by rfl⟩ : syracuseStep 2134511 = 3201767) B3201767
theorem B1021049 : Blo 279826 1021049 := bstep (se 2 (by rfl) ⟨382893, by rfl⟩ : syracuseStep 1021049 = 765787) B765787
theorem B759095 : Blo 279826 759095 := bstep (se 1 (by rfl) ⟨569321, by rfl⟩ : syracuseStep 759095 = 1138643) B1138643
theorem B399487 : Blo 279826 399487 := bstep (se 1 (by rfl) ⟨299615, by rfl⟩ : syracuseStep 399487 = 599231) B599231
theorem B50206877 : Blo 279826 50206877 := bstep (se 3 (by rfl) ⟨9413789, by rfl⟩ : syracuseStep 50206877 = 18827579) B18827579
theorem B2726405 : Blo 279826 2726405 := bstep (se 4 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 2726405 = 511201) B511201
theorem B630107 : Blo 279826 630107 := bstep (se 1 (by rfl) ⟨472580, by rfl⟩ : syracuseStep 630107 = 945161) B945161
theorem B630665 : Blo 279826 630665 := bstep (se 2 (by rfl) ⟨236499, by rfl⟩ : syracuseStep 630665 = 472999) B472999
theorem B630953 : Blo 279826 630953 := bstep (se 2 (by rfl) ⟨236607, by rfl⟩ : syracuseStep 630953 = 473215) B473215
theorem B6070747 : Blo 279826 6070747 := bstep (se 1 (by rfl) ⟨4553060, by rfl⟩ : syracuseStep 6070747 = 9106121) B9106121
theorem B631673 : Blo 279826 631673 := bstep (se 2 (by rfl) ⟨236877, by rfl⟩ : syracuseStep 631673 = 473755) B473755
theorem B1418471 : Blo 279826 1418471 := bstep (se 1 (by rfl) ⟨1063853, by rfl⟩ : syracuseStep 1418471 = 2127707) B2127707
theorem B632375 : Blo 279826 632375 := bstep (se 1 (by rfl) ⟨474281, by rfl⟩ : syracuseStep 632375 = 948563) B948563
theorem B1812455 : Blo 279826 1812455 := bstep (se 1 (by rfl) ⟨1359341, by rfl⟩ : syracuseStep 1812455 = 2718683) B2718683
theorem B2140343 : Blo 279826 2140343 := bstep (se 1 (by rfl) ⟨1605257, by rfl⟩ : syracuseStep 2140343 = 3210515) B3210515
theorem B1353959 : Blo 279826 1353959 := bstep (se 1 (by rfl) ⟨1015469, by rfl⟩ : syracuseStep 1353959 = 2030939) B2030939
theorem B6924745 : Blo 279826 6924745 := bstep (se 2 (by rfl) ⟨2596779, by rfl⟩ : syracuseStep 6924745 = 5193559) B5193559
theorem B633311 : Blo 279826 633311 := bstep (se 1 (by rfl) ⟨474983, by rfl⟩ : syracuseStep 633311 = 949967) B949967
theorem B1420739 : Blo 279826 1420739 := bstep (se 1 (by rfl) ⟨1065554, by rfl⟩ : syracuseStep 1420739 = 2131109) B2131109
theorem B8073107 : Blo 279826 8073107 := bstep (se 1 (by rfl) ⟨6054830, by rfl⟩ : syracuseStep 8073107 = 12109661) B12109661
theorem B635129 : Blo 279826 635129 := bstep (se 2 (by rfl) ⟨238173, by rfl⟩ : syracuseStep 635129 = 476347) B476347
theorem B2044777 : Blo 279826 2044777 := bstep (se 2 (by rfl) ⟨766791, by rfl⟩ : syracuseStep 2044777 = 1533583) B1533583
theorem B537691 : Blo 279826 537691 := bstep (se 1 (by rfl) ⟨403268, by rfl⟩ : syracuseStep 537691 = 806537) B806537
theorem B472223 : Blo 279826 472223 := bstep (se 1 (by rfl) ⟨354167, by rfl⟩ : syracuseStep 472223 = 708335) B708335
theorem B1063003 : Blo 279826 1063003 := bstep (se 1 (by rfl) ⟨797252, by rfl⟩ : syracuseStep 1063003 = 1594505) B1594505
theorem B147601511 : Blo 279826 147601511 := bstep (se 1 (by rfl) ⟨110701133, by rfl⟩ : syracuseStep 147601511 = 221402267) B221402267
theorem B4340087 : Blo 279826 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B506351 : Blo 279826 506351 := bstep (se 1 (by rfl) ⟨379763, by rfl⟩ : syracuseStep 506351 = 759527) B759527
theorem B474761 : Blo 279826 474761 := bstep (se 2 (by rfl) ⟨178035, by rfl⟩ : syracuseStep 474761 = 356071) B356071
theorem B8437925 : Blo 279826 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B2408777 : Blo 279826 2408777 := bstep (se 2 (by rfl) ⟨903291, by rfl⟩ : syracuseStep 2408777 = 1806583) B1806583
theorem B279935 : Blo 279826 279935 := bstep (se 1 (by rfl) ⟨209951, by rfl⟩ : syracuseStep 279935 = 419903) B419903
theorem B280167 : Blo 279826 280167 := bstep (se 1 (by rfl) ⟨210125, by rfl⟩ : syracuseStep 280167 = 420251) B420251
theorem B280271 : Blo 279826 280271 := bstep (se 1 (by rfl) ⟨210203, by rfl⟩ : syracuseStep 280271 = 420407) B420407
theorem B280807 : Blo 279826 280807 := bstep (se 1 (by rfl) ⟨210605, by rfl⟩ : syracuseStep 280807 = 421211) B421211
theorem B281071 : Blo 279826 281071 := bstep (se 1 (by rfl) ⟨210803, by rfl⟩ : syracuseStep 281071 = 421607) B421607
theorem B2411167 : Blo 279826 2411167 := bstep (se 1 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 2411167 = 3616751) B3616751
theorem B1068137 : Blo 279826 1068137 := bstep (se 2 (by rfl) ⟨400551, by rfl⟩ : syracuseStep 1068137 = 801103) B801103
theorem B1068335 : Blo 279826 1068335 := bstep (se 1 (by rfl) ⟨801251, by rfl⟩ : syracuseStep 1068335 = 1602503) B1602503
theorem B281903 : Blo 279826 281903 := bstep (se 1 (by rfl) ⟨211427, by rfl⟩ : syracuseStep 281903 = 422855) B422855
theorem B282047 : Blo 279826 282047 := bstep (se 1 (by rfl) ⟨211535, by rfl⟩ : syracuseStep 282047 = 423071) B423071
theorem B282367 : Blo 279826 282367 := bstep (se 1 (by rfl) ⟨211775, by rfl⟩ : syracuseStep 282367 = 423551) B423551
theorem B282395 : Blo 279826 282395 := bstep (se 1 (by rfl) ⟨211796, by rfl⟩ : syracuseStep 282395 = 423593) B423593
theorem B610151 : Blo 279826 610151 := bstep (se 1 (by rfl) ⟨457613, by rfl⟩ : syracuseStep 610151 = 915227) B915227
theorem B282471 : Blo 279826 282471 := bstep (se 1 (by rfl) ⟨211853, by rfl⟩ : syracuseStep 282471 = 423707) B423707
theorem B315463 : Blo 279826 315463 := bstep (se 1 (by rfl) ⟨236597, by rfl⟩ : syracuseStep 315463 = 473195) B473195
theorem B283103 : Blo 279826 283103 := bstep (se 1 (by rfl) ⟨212327, by rfl⟩ : syracuseStep 283103 = 424655) B424655
theorem B283135 : Blo 279826 283135 := bstep (se 1 (by rfl) ⟨212351, by rfl⟩ : syracuseStep 283135 = 424703) B424703
theorem B283463 : Blo 279826 283463 := bstep (se 1 (by rfl) ⟨212597, by rfl⟩ : syracuseStep 283463 = 425195) B425195
theorem B283495 : Blo 279826 283495 := bstep (se 1 (by rfl) ⟨212621, by rfl⟩ : syracuseStep 283495 = 425243) B425243
theorem B2577743 : Blo 279826 2577743 := bstep (se 1 (by rfl) ⟨1933307, by rfl⟩ : syracuseStep 2577743 = 3866615) B3866615
theorem B19650059 : Blo 279826 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B5461739 : Blo 279826 5461739 := bstep (se 1 (by rfl) ⟨4096304, by rfl⟩ : syracuseStep 5461739 = 8192609) B8192609
theorem B1071083 : Blo 279826 1071083 := bstep (se 1 (by rfl) ⟨803312, by rfl⟩ : syracuseStep 1071083 = 1606625) B1606625
theorem B3758089 : Blo 279826 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B449135 : Blo 279826 449135 := bstep (se 1 (by rfl) ⟨336851, by rfl⟩ : syracuseStep 449135 = 673703) B673703
theorem B1203295 : Blo 279826 1203295 := bstep (se 1 (by rfl) ⟨902471, by rfl⟩ : syracuseStep 1203295 = 1804943) B1804943
theorem B1072237 : Blo 279826 1072237 := bstep (se 3 (by rfl) ⟨201044, by rfl⟩ : syracuseStep 1072237 = 402089) B402089
theorem B318703 : Blo 279826 318703 := bstep (se 1 (by rfl) ⟨239027, by rfl⟩ : syracuseStep 318703 = 478055) B478055
theorem B21128471 : Blo 279826 21128471 := bstep (se 1 (by rfl) ⟨15846353, by rfl⟩ : syracuseStep 21128471 = 31692707) B31692707
theorem B1074667 : Blo 279826 1074667 := bstep (se 1 (by rfl) ⟨806000, by rfl⟩ : syracuseStep 1074667 = 1612001) B1612001
theorem B1009255 : Blo 279826 1009255 := bstep (se 1 (by rfl) ⟨756941, by rfl⟩ : syracuseStep 1009255 = 1513883) B1513883
theorem B1075139 : Blo 279826 1075139 := bstep (se 1 (by rfl) ⟨806354, by rfl⟩ : syracuseStep 1075139 = 1612709) B1612709
theorem B1042895 : Blo 279826 1042895 := bstep (se 1 (by rfl) ⟨782171, by rfl⟩ : syracuseStep 1042895 = 1564343) B1564343
theorem B2485073 : Blo 279826 2485073 := bstep (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) B1863805
theorem B453863 : Blo 279826 453863 := bstep (se 1 (by rfl) ⟨340397, by rfl⟩ : syracuseStep 453863 = 680795) B680795
theorem B1470095 : Blo 279826 1470095 := bstep (se 1 (by rfl) ⟨1102571, by rfl⟩ : syracuseStep 1470095 = 2205143) B2205143
theorem B30994163 : Blo 279826 30994163 := bstep (se 1 (by rfl) ⟨23245622, by rfl⟩ : syracuseStep 30994163 = 46491245) B46491245
theorem B946619 : Blo 279826 946619 := bstep (se 1 (by rfl) ⟨709964, by rfl⟩ : syracuseStep 946619 = 1419929) B1419929
theorem B422567 : Blo 279826 422567 := bstep (se 1 (by rfl) ⟨316925, by rfl⟩ : syracuseStep 422567 = 633851) B633851
theorem B423239 : Blo 279826 423239 := bstep (se 1 (by rfl) ⟨317429, by rfl⟩ : syracuseStep 423239 = 634859) B634859
theorem B127497829 : Blo 279826 127497829 := bstep (se 4 (by rfl) ⟨11952921, by rfl⟩ : syracuseStep 127497829 = 23905843) B23905843
theorem B2455705 : Blo 279826 2455705 := bstep (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) B1841779
theorem B424175 : Blo 279826 424175 := bstep (se 1 (by rfl) ⟨318131, by rfl⟩ : syracuseStep 424175 = 636263) B636263
theorem B424187 : Blo 279826 424187 := bstep (se 1 (by rfl) ⟨318140, by rfl⟩ : syracuseStep 424187 = 636281) B636281
theorem B425711 : Blo 279826 425711 := bstep (se 1 (by rfl) ⟨319283, by rfl⟩ : syracuseStep 425711 = 638567) B638567
theorem B31489829 : Blo 279826 31489829 := bstep (se 4 (by rfl) ⟨2952171, by rfl⟩ : syracuseStep 31489829 = 5904343) B5904343
theorem B1638599 : Blo 279826 1638599 := bstep (se 1 (by rfl) ⟨1228949, by rfl⟩ : syracuseStep 1638599 = 2457899) B2457899
theorem B1605851 : Blo 279826 1605851 := bstep (se 1 (by rfl) ⟨1204388, by rfl⟩ : syracuseStep 1605851 = 2408777) B2408777
theorem B8094329 : Blo 279826 8094329 := bstep (se 2 (by rfl) ⟨3035373, by rfl⟩ : syracuseStep 8094329 = 6070747) B6070747
theorem B2623427 : Blo 279826 2623427 := bstep (se 1 (by rfl) ⟨1967570, by rfl⟩ : syracuseStep 2623427 = 3935141) B3935141
theorem B1345673 : Blo 279826 1345673 := bstep (se 2 (by rfl) ⟨504627, by rfl⟩ : syracuseStep 1345673 = 1009255) B1009255
theorem B3214889 : Blo 279826 3214889 := bstep (se 2 (by rfl) ⟨1205583, by rfl⟩ : syracuseStep 3214889 = 2411167) B2411167
theorem B3641159 : Blo 279826 3641159 := bstep (se 1 (by rfl) ⟨2730869, by rfl⟩ : syracuseStep 3641159 = 5461739) B5461739
theorem B299423 : Blo 279826 299423 := bstep (se 1 (by rfl) ⟨224567, by rfl⟩ : syracuseStep 299423 = 449135) B449135
theorem B2726369 : Blo 279826 2726369 := bstep (se 2 (by rfl) ⟨1022388, by rfl⟩ : syracuseStep 2726369 = 2044777) B2044777
theorem B1350269 : Blo 279826 1350269 := bstep (se 3 (by rfl) ⟨253175, by rfl⟩ : syracuseStep 1350269 = 506351) B506351
theorem B6626861 : Blo 279826 6626861 := bstep (se 3 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 6626861 = 2485073) B2485073
theorem B5382071 : Blo 279826 5382071 := bstep (se 1 (by rfl) ⟨4036553, by rfl⟩ : syracuseStep 5382071 = 8073107) B8073107
theorem B1417337 : Blo 279826 1417337 := bstep (se 2 (by rfl) ⟨531501, by rfl⟩ : syracuseStep 1417337 = 1063003) B1063003
theorem B532649 : Blo 279826 532649 := bstep (se 2 (by rfl) ⟨199743, by rfl⟩ : syracuseStep 532649 = 399487) B399487
theorem B631079 : Blo 279826 631079 := bstep (se 1 (by rfl) ⟨473309, by rfl⟩ : syracuseStep 631079 = 946619) B946619
theorem B2893391 : Blo 279826 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B633887 : Blo 279826 633887 := bstep (se 1 (by rfl) ⟨475415, by rfl⟩ : syracuseStep 633887 = 950831) B950831
theorem B2403377 : Blo 279826 2403377 := bstep (se 2 (by rfl) ⟨901266, by rfl⟩ : syracuseStep 2403377 = 1802533) B1802533
theorem B766111 : Blo 279826 766111 := bstep (se 1 (by rfl) ⟨574583, by rfl⟩ : syracuseStep 766111 = 1149167) B1149167
theorem B635579 : Blo 279826 635579 := bstep (se 1 (by rfl) ⟨476684, by rfl⟩ : syracuseStep 635579 = 953369) B953369
theorem B1423007 : Blo 279826 1423007 := bstep (se 1 (by rfl) ⟨1067255, by rfl⟩ : syracuseStep 1423007 = 2134511) B2134511
theorem B506063 : Blo 279826 506063 := bstep (se 1 (by rfl) ⟨379547, by rfl⟩ : syracuseStep 506063 = 759095) B759095
theorem B1718495 : Blo 279826 1718495 := bstep (se 1 (by rfl) ⟨1288871, by rfl⟩ : syracuseStep 1718495 = 2577743) B2577743
theorem B33471251 : Blo 279826 33471251 := bstep (se 1 (by rfl) ⟨25103438, by rfl⟩ : syracuseStep 33471251 = 50206877) B50206877
theorem B1817603 : Blo 279826 1817603 := bstep (se 1 (by rfl) ⟨1363202, by rfl⟩ : syracuseStep 1817603 = 2726405) B2726405
theorem B1426895 : Blo 279826 1426895 := bstep (se 1 (by rfl) ⟨1070171, by rfl⟩ : syracuseStep 1426895 = 2140343) B2140343
theorem B902639 : Blo 279826 902639 := bstep (se 1 (by rfl) ⟨676979, by rfl⟩ : syracuseStep 902639 = 1353959) B1353959
theorem B20662775 : Blo 279826 20662775 := bstep (se 1 (by rfl) ⟨15497081, by rfl⟩ : syracuseStep 20662775 = 30994163) B30994163
theorem B281711 : Blo 279826 281711 := bstep (se 1 (by rfl) ⟨211283, by rfl⟩ : syracuseStep 281711 = 422567) B422567
theorem B314815 : Blo 279826 314815 := bstep (se 1 (by rfl) ⟨236111, by rfl⟩ : syracuseStep 314815 = 472223) B472223
theorem B282159 : Blo 279826 282159 := bstep (se 1 (by rfl) ⟨211619, by rfl⟩ : syracuseStep 282159 = 423239) B423239
theorem B1429649 : Blo 279826 1429649 := bstep (se 2 (by rfl) ⟨536118, by rfl⟩ : syracuseStep 1429649 = 1072237) B1072237
theorem B282783 : Blo 279826 282783 := bstep (se 1 (by rfl) ⟨212087, by rfl⟩ : syracuseStep 282783 = 424175) B424175
theorem B282791 : Blo 279826 282791 := bstep (se 1 (by rfl) ⟨212093, by rfl⟩ : syracuseStep 282791 = 424187) B424187
theorem B1627069 : Blo 279826 1627069 := bstep (se 3 (by rfl) ⟨305075, by rfl⟩ : syracuseStep 1627069 = 610151) B610151
theorem B316507 : Blo 279826 316507 := bstep (se 1 (by rfl) ⟨237380, by rfl⟩ : syracuseStep 316507 = 474761) B474761
theorem B283807 : Blo 279826 283807 := bstep (se 1 (by rfl) ⟨212855, by rfl⟩ : syracuseStep 283807 = 425711) B425711
theorem B20993219 : Blo 279826 20993219 := bstep (se 1 (by rfl) ⟨15744914, by rfl⟩ : syracuseStep 20993219 = 31489829) B31489829
theorem B5625283 : Blo 279826 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B873935 : Blo 279826 873935 := bstep (se 1 (by rfl) ⟨655451, by rfl⟩ : syracuseStep 873935 = 1310903) B1310903
theorem B19421471 : Blo 279826 19421471 := bstep (se 1 (by rfl) ⟨14566103, by rfl⟩ : syracuseStep 19421471 = 29132207) B29132207
theorem B13064591 : Blo 279826 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B1432889 : Blo 279826 1432889 := bstep (se 2 (by rfl) ⟨537333, by rfl⟩ : syracuseStep 1432889 = 1074667) B1074667
theorem B712091 : Blo 279826 712091 := bstep (se 1 (by rfl) ⟨534068, by rfl⟩ : syracuseStep 712091 = 1068137) B1068137
theorem B712223 : Blo 279826 712223 := bstep (se 1 (by rfl) ⟨534167, by rfl⟩ : syracuseStep 712223 = 1068335) B1068335
theorem B9232993 : Blo 279826 9232993 := bstep (se 2 (by rfl) ⟨3462372, by rfl⟩ : syracuseStep 9232993 = 6924745) B6924745
theorem B680699 : Blo 279826 680699 := bstep (se 1 (by rfl) ⟨510524, by rfl⟩ : syracuseStep 680699 = 1021049) B1021049
theorem B13100039 : Blo 279826 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B714055 : Blo 279826 714055 := bstep (se 1 (by rfl) ⟨535541, by rfl⟩ : syracuseStep 714055 = 1071083) B1071083
theorem B420071 : Blo 279826 420071 := bstep (se 1 (by rfl) ⟨315053, by rfl⟩ : syracuseStep 420071 = 630107) B630107
theorem B420443 : Blo 279826 420443 := bstep (se 1 (by rfl) ⟨315332, by rfl⟩ : syracuseStep 420443 = 630665) B630665
theorem B420617 : Blo 279826 420617 := bstep (se 2 (by rfl) ⟨157731, by rfl⟩ : syracuseStep 420617 = 315463) B315463
theorem B420635 : Blo 279826 420635 := bstep (se 1 (by rfl) ⟨315476, by rfl⟩ : syracuseStep 420635 = 630953) B630953
theorem B421115 : Blo 279826 421115 := bstep (se 1 (by rfl) ⟨315836, by rfl⟩ : syracuseStep 421115 = 631673) B631673
theorem B945647 : Blo 279826 945647 := bstep (se 1 (by rfl) ⟨709235, by rfl⟩ : syracuseStep 945647 = 1418471) B1418471
theorem B14085647 : Blo 279826 14085647 := bstep (se 1 (by rfl) ⟨10564235, by rfl⟩ : syracuseStep 14085647 = 21128471) B21128471
theorem B421583 : Blo 279826 421583 := bstep (se 1 (by rfl) ⟨316187, by rfl⟩ : syracuseStep 421583 = 632375) B632375
theorem B2781053 : Blo 279826 2781053 := bstep (se 3 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 2781053 = 1042895) B1042895
theorem B716759 : Blo 279826 716759 := bstep (se 1 (by rfl) ⟨537569, by rfl⟩ : syracuseStep 716759 = 1075139) B1075139
theorem B1208303 : Blo 279826 1208303 := bstep (se 1 (by rfl) ⟨906227, by rfl⟩ : syracuseStep 1208303 = 1812455) B1812455
theorem B716921 : Blo 279826 716921 := bstep (se 2 (by rfl) ⟨268845, by rfl⟩ : syracuseStep 716921 = 537691) B537691
theorem B422207 : Blo 279826 422207 := bstep (se 1 (by rfl) ⟨316655, by rfl⟩ : syracuseStep 422207 = 633311) B633311
theorem B169997105 : Blo 279826 169997105 := bstep (se 2 (by rfl) ⟨63748914, by rfl⟩ : syracuseStep 169997105 = 127497829) B127497829
theorem B947159 : Blo 279826 947159 := bstep (se 1 (by rfl) ⟨710369, by rfl⟩ : syracuseStep 947159 = 1420739) B1420739
theorem B980063 : Blo 279826 980063 := bstep (se 1 (by rfl) ⟨735047, by rfl⟩ : syracuseStep 980063 = 1470095) B1470095
theorem B5010785 : Blo 279826 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B423419 : Blo 279826 423419 := bstep (se 1 (by rfl) ⟨317564, by rfl⟩ : syracuseStep 423419 = 635129) B635129
theorem B3274273 : Blo 279826 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B1210301 : Blo 279826 1210301 := bstep (se 3 (by rfl) ⟨226931, by rfl⟩ : syracuseStep 1210301 = 453863) B453863
theorem B98401007 : Blo 279826 98401007 := bstep (se 1 (by rfl) ⟨73800755, by rfl⟩ : syracuseStep 98401007 = 147601511) B147601511
theorem B1604393 : Blo 279826 1604393 := bstep (se 2 (by rfl) ⟨601647, by rfl⟩ : syracuseStep 1604393 = 1203295) B1203295
theorem B424937 : Blo 279826 424937 := bstep (se 2 (by rfl) ⟨159351, by rfl⟩ : syracuseStep 424937 = 318703) B318703
theorem B951263 : Blo 279826 951263 := bstep (se 1 (by rfl) ⟨713447, by rfl⟩ : syracuseStep 951263 = 1426895) B1426895
theorem B952073 : Blo 279826 952073 := bstep (se 2 (by rfl) ⟨357027, by rfl⟩ : syracuseStep 952073 = 714055) B714055
theorem B953099 : Blo 279826 953099 := bstep (se 1 (by rfl) ⟨714824, by rfl⟩ : syracuseStep 953099 = 1429649) B1429649
theorem B13995479 : Blo 279826 13995479 := bstep (se 1 (by rfl) ⟨10496609, by rfl⟩ : syracuseStep 13995479 = 20993219) B20993219
theorem B955259 : Blo 279826 955259 := bstep (se 1 (by rfl) ⟨716444, by rfl⟩ : syracuseStep 955259 = 1432889) B1432889
theorem B1021481 : Blo 279826 1021481 := bstep (se 2 (by rfl) ⟨383055, by rfl⟩ : syracuseStep 1021481 = 766111) B766111
theorem B2169425 : Blo 279826 2169425 := bstep (se 2 (by rfl) ⟨813534, by rfl⟩ : syracuseStep 2169425 = 1627069) B1627069
theorem B4365697 : Blo 279826 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B630431 : Blo 279826 630431 := bstep (se 1 (by rfl) ⟨472823, by rfl⟩ : syracuseStep 630431 = 945647) B945647
theorem B631439 : Blo 279826 631439 := bstep (se 1 (by rfl) ⟨473579, by rfl⟩ : syracuseStep 631439 = 947159) B947159
theorem B337375 : Blo 279826 337375 := bstep (se 1 (by rfl) ⟨253031, by rfl⟩ : syracuseStep 337375 = 506063) B506063
theorem B9709757 : Blo 279826 9709757 := bstep (se 3 (by rfl) ⟨1820579, by rfl⟩ : syracuseStep 9709757 = 3641159) B3641159
theorem B601759 : Blo 279826 601759 := bstep (se 1 (by rfl) ⟨451319, by rfl⟩ : syracuseStep 601759 = 902639) B902639
theorem B798461 : Blo 279826 798461 := bstep (se 3 (by rfl) ⟨149711, by rfl⟩ : syracuseStep 798461 = 299423) B299423
theorem B1748951 : Blo 279826 1748951 := bstep (se 1 (by rfl) ⟨1311713, by rfl⟩ : syracuseStep 1748951 = 2623427) B2623427
theorem B897115 : Blo 279826 897115 := bstep (se 1 (by rfl) ⟨672836, by rfl⟩ : syracuseStep 897115 = 1345673) B1345673
theorem B13775183 : Blo 279826 13775183 := bstep (se 1 (by rfl) ⟨10331387, by rfl⟩ : syracuseStep 13775183 = 20662775) B20662775
theorem B17478389 : Blo 279826 17478389 := bstep (se 5 (by rfl) ⟨819299, by rfl⟩ : syracuseStep 17478389 = 1638599) B1638599
theorem B2143259 : Blo 279826 2143259 := bstep (se 1 (by rfl) ⟨1607444, by rfl⟩ : syracuseStep 2143259 = 3214889) B3214889
theorem B1817579 : Blo 279826 1817579 := bstep (se 1 (by rfl) ⟨1363184, by rfl⟩ : syracuseStep 1817579 = 2726369) B2726369
theorem B900179 : Blo 279826 900179 := bstep (se 1 (by rfl) ⟨675134, by rfl⟩ : syracuseStep 900179 = 1350269) B1350269
theorem B474727 : Blo 279826 474727 := bstep (se 1 (by rfl) ⟨356045, by rfl⟩ : syracuseStep 474727 = 712091) B712091
theorem B474815 : Blo 279826 474815 := bstep (se 1 (by rfl) ⟨356111, by rfl⟩ : syracuseStep 474815 = 712223) B712223
theorem B3588047 : Blo 279826 3588047 := bstep (se 1 (by rfl) ⟨2691035, by rfl⟩ : syracuseStep 3588047 = 5382071) B5382071
theorem B8733359 : Blo 279826 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B51790589 : Blo 279826 51790589 := bstep (se 3 (by rfl) ⟨9710735, by rfl⟩ : syracuseStep 51790589 = 19421471) B19421471
theorem B280047 : Blo 279826 280047 := bstep (se 1 (by rfl) ⟨210035, by rfl⟩ : syracuseStep 280047 = 420071) B420071
theorem B280295 : Blo 279826 280295 := bstep (se 1 (by rfl) ⟨210221, by rfl⟩ : syracuseStep 280295 = 420443) B420443
theorem B280411 : Blo 279826 280411 := bstep (se 1 (by rfl) ⟨210308, by rfl⟩ : syracuseStep 280411 = 420617) B420617
theorem B280423 : Blo 279826 280423 := bstep (se 1 (by rfl) ⟨210317, by rfl⟩ : syracuseStep 280423 = 420635) B420635
theorem B280743 : Blo 279826 280743 := bstep (se 1 (by rfl) ⟨210557, by rfl⟩ : syracuseStep 280743 = 421115) B421115
theorem B9390431 : Blo 279826 9390431 := bstep (se 1 (by rfl) ⟨7042823, by rfl⟩ : syracuseStep 9390431 = 14085647) B14085647
theorem B281055 : Blo 279826 281055 := bstep (se 1 (by rfl) ⟨210791, by rfl⟩ : syracuseStep 281055 = 421583) B421583
theorem B1854035 : Blo 279826 1854035 := bstep (se 1 (by rfl) ⟨1390526, by rfl⟩ : syracuseStep 1854035 = 2781053) B2781053
theorem B477839 : Blo 279826 477839 := bstep (se 1 (by rfl) ⟨358379, by rfl⟩ : syracuseStep 477839 = 716759) B716759
theorem B805535 : Blo 279826 805535 := bstep (se 1 (by rfl) ⟨604151, by rfl⟩ : syracuseStep 805535 = 1208303) B1208303
theorem B477947 : Blo 279826 477947 := bstep (se 1 (by rfl) ⟨358460, by rfl⟩ : syracuseStep 477947 = 716921) B716921
theorem B281471 : Blo 279826 281471 := bstep (se 1 (by rfl) ⟨211103, by rfl⟩ : syracuseStep 281471 = 422207) B422207
theorem B113331403 : Blo 279826 113331403 := bstep (se 1 (by rfl) ⟨84998552, by rfl⟩ : syracuseStep 113331403 = 169997105) B169997105
theorem B282279 : Blo 279826 282279 := bstep (se 1 (by rfl) ⟨211709, by rfl⟩ : syracuseStep 282279 = 423419) B423419
theorem B806867 : Blo 279826 806867 := bstep (se 1 (by rfl) ⟨605150, by rfl⟩ : syracuseStep 806867 = 1210301) B1210301
theorem B1069595 : Blo 279826 1069595 := bstep (se 1 (by rfl) ⟨802196, by rfl⟩ : syracuseStep 1069595 = 1604393) B1604393
theorem B283291 : Blo 279826 283291 := bstep (se 1 (by rfl) ⟨212468, by rfl⟩ : syracuseStep 283291 = 424937) B424937
theorem B1070567 : Blo 279826 1070567 := bstep (se 1 (by rfl) ⟨802925, by rfl⟩ : syracuseStep 1070567 = 1605851) B1605851
theorem B5396219 : Blo 279826 5396219 := bstep (se 1 (by rfl) ⟨4047164, by rfl⟩ : syracuseStep 5396219 = 8094329) B8094329
theorem B49242629 : Blo 279826 49242629 := bstep (se 4 (by rfl) ⟨4616496, by rfl⟩ : syracuseStep 49242629 = 9232993) B9232993
theorem B582623 : Blo 279826 582623 := bstep (se 1 (by rfl) ⟨436967, by rfl⟩ : syracuseStep 582623 = 873935) B873935
theorem B8709727 : Blo 279826 8709727 := bstep (se 1 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 8709727 = 13064591) B13064591
theorem B419753 : Blo 279826 419753 := bstep (se 2 (by rfl) ⟨157407, by rfl⟩ : syracuseStep 419753 = 314815) B314815
theorem B4417907 : Blo 279826 4417907 := bstep (se 1 (by rfl) ⟨3313430, by rfl⟩ : syracuseStep 4417907 = 6626861) B6626861
theorem B944891 : Blo 279826 944891 := bstep (se 1 (by rfl) ⟨708668, by rfl⟩ : syracuseStep 944891 = 1417337) B1417337
theorem B355099 : Blo 279826 355099 := bstep (se 1 (by rfl) ⟨266324, by rfl⟩ : syracuseStep 355099 = 532649) B532649
theorem B420719 : Blo 279826 420719 := bstep (se 1 (by rfl) ⟨315539, by rfl⟩ : syracuseStep 420719 = 631079) B631079
theorem B453799 : Blo 279826 453799 := bstep (se 1 (by rfl) ⟨340349, by rfl⟩ : syracuseStep 453799 = 680699) B680699
theorem B1928927 : Blo 279826 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B422009 : Blo 279826 422009 := bstep (se 2 (by rfl) ⟨158253, by rfl⟩ : syracuseStep 422009 = 316507) B316507
theorem B7500377 : Blo 279826 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B262402685 : Blo 279826 262402685 := bstep (se 3 (by rfl) ⟨49200503, by rfl⟩ : syracuseStep 262402685 = 98401007) B98401007
theorem B422591 : Blo 279826 422591 := bstep (se 1 (by rfl) ⟨316943, by rfl⟩ : syracuseStep 422591 = 633887) B633887
theorem B1602251 : Blo 279826 1602251 := bstep (se 1 (by rfl) ⟨1201688, by rfl⟩ : syracuseStep 1602251 = 2403377) B2403377
theorem B423719 : Blo 279826 423719 := bstep (se 1 (by rfl) ⟨317789, by rfl⟩ : syracuseStep 423719 = 635579) B635579
theorem B653375 : Blo 279826 653375 := bstep (se 1 (by rfl) ⟨490031, by rfl⟩ : syracuseStep 653375 = 980063) B980063
theorem B3340523 : Blo 279826 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B948671 : Blo 279826 948671 := bstep (se 1 (by rfl) ⟨711503, by rfl⟩ : syracuseStep 948671 = 1423007) B1423007
theorem B1145663 : Blo 279826 1145663 := bstep (se 1 (by rfl) ⟨859247, by rfl⟩ : syracuseStep 1145663 = 1718495) B1718495
theorem B22314167 : Blo 279826 22314167 := bstep (se 1 (by rfl) ⟨16735625, by rfl⟩ : syracuseStep 22314167 = 33471251) B33471251
theorem B1211735 : Blo 279826 1211735 := bstep (se 1 (by rfl) ⟨908801, by rfl⟩ : syracuseStep 1211735 = 1817603) B1817603
theorem B6260287 : Blo 279826 6260287 := bstep (se 1 (by rfl) ⟨4695215, by rfl⟩ : syracuseStep 6260287 = 9390431) B9390431
theorem B1446283 : Blo 279826 1446283 := bstep (se 1 (by rfl) ⟨1084712, by rfl⟩ : syracuseStep 1446283 = 2169425) B2169425
theorem B629927 : Blo 279826 629927 := bstep (se 1 (by rfl) ⟨472445, by rfl⟩ : syracuseStep 629927 = 944891) B944891
theorem B1285951 : Blo 279826 1285951 := bstep (se 1 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 1285951 = 1928927) B1928927
theorem B532307 : Blo 279826 532307 := bstep (se 1 (by rfl) ⟨399230, by rfl⟩ : syracuseStep 532307 = 798461) B798461
theorem B9183455 : Blo 279826 9183455 := bstep (se 1 (by rfl) ⟨6887591, by rfl⟩ : syracuseStep 9183455 = 13775183) B13775183
theorem B435583 : Blo 279826 435583 := bstep (se 1 (by rfl) ⟨326687, by rfl⟩ : syracuseStep 435583 = 653375) B653375
theorem B632447 : Blo 279826 632447 := bstep (se 1 (by rfl) ⟨474335, by rfl⟩ : syracuseStep 632447 = 948671) B948671
theorem B763775 : Blo 279826 763775 := bstep (se 1 (by rfl) ⟨572831, by rfl⟩ : syracuseStep 763775 = 1145663) B1145663
theorem B600119 : Blo 279826 600119 := bstep (se 1 (by rfl) ⟨450089, by rfl⟩ : syracuseStep 600119 = 900179) B900179
theorem B632969 : Blo 279826 632969 := bstep (se 2 (by rfl) ⟨237363, by rfl⟩ : syracuseStep 632969 = 474727) B474727
theorem B634175 : Blo 279826 634175 := bstep (se 1 (by rfl) ⟨475631, by rfl⟩ : syracuseStep 634175 = 951263) B951263
theorem B634715 : Blo 279826 634715 := bstep (se 1 (by rfl) ⟨476036, by rfl⟩ : syracuseStep 634715 = 952073) B952073
theorem B20001005 : Blo 279826 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B537023 : Blo 279826 537023 := bstep (se 1 (by rfl) ⟨402767, by rfl⟩ : syracuseStep 537023 = 805535) B805535
theorem B635399 : Blo 279826 635399 := bstep (se 1 (by rfl) ⟨476549, by rfl⟩ : syracuseStep 635399 = 953099) B953099
theorem B46609037 : Blo 279826 46609037 := bstep (se 3 (by rfl) ⟨8739194, by rfl⟩ : syracuseStep 46609037 = 17478389) B17478389
theorem B11612969 : Blo 279826 11612969 := bstep (se 2 (by rfl) ⟨4354863, by rfl⟩ : syracuseStep 11612969 = 8709727) B8709727
theorem B537911 : Blo 279826 537911 := bstep (se 1 (by rfl) ⟨403433, by rfl⟩ : syracuseStep 537911 = 806867) B806867
theorem B636839 : Blo 279826 636839 := bstep (se 1 (by rfl) ⟨477629, by rfl⟩ : syracuseStep 636839 = 955259) B955259
theorem B473465 : Blo 279826 473465 := bstep (se 2 (by rfl) ⟨177549, by rfl⟩ : syracuseStep 473465 = 355099) B355099
theorem B605065 : Blo 279826 605065 := bstep (se 2 (by rfl) ⟨226899, by rfl⟩ : syracuseStep 605065 = 453799) B453799
theorem B151108537 : Blo 279826 151108537 := bstep (se 2 (by rfl) ⟨56665701, by rfl⟩ : syracuseStep 151108537 = 113331403) B113331403
theorem B802345 : Blo 279826 802345 := bstep (se 2 (by rfl) ⟨300879, by rfl⟩ : syracuseStep 802345 = 601759) B601759
theorem B1196153 : Blo 279826 1196153 := bstep (se 2 (by rfl) ⟨448557, by rfl⟩ : syracuseStep 1196153 = 897115) B897115
theorem B11781085 : Blo 279826 11781085 := bstep (se 3 (by rfl) ⟨2208953, by rfl⟩ : syracuseStep 11781085 = 4417907) B4417907
theorem B279835 : Blo 279826 279835 := bstep (se 1 (by rfl) ⟨209876, by rfl⟩ : syracuseStep 279835 = 419753) B419753
theorem B6473171 : Blo 279826 6473171 := bstep (se 1 (by rfl) ⟨4854878, by rfl⟩ : syracuseStep 6473171 = 9709757) B9709757
theorem B280479 : Blo 279826 280479 := bstep (se 1 (by rfl) ⟨210359, by rfl⟩ : syracuseStep 280479 = 420719) B420719
theorem B1165967 : Blo 279826 1165967 := bstep (se 1 (by rfl) ⟨874475, by rfl⟩ : syracuseStep 1165967 = 1748951) B1748951
theorem B281339 : Blo 279826 281339 := bstep (se 1 (by rfl) ⟨211004, by rfl⟩ : syracuseStep 281339 = 422009) B422009
theorem B174935123 : Blo 279826 174935123 := bstep (se 1 (by rfl) ⟨131201342, by rfl⟩ : syracuseStep 174935123 = 262402685) B262402685
theorem B281727 : Blo 279826 281727 := bstep (se 1 (by rfl) ⟨211295, by rfl⟩ : syracuseStep 281727 = 422591) B422591
theorem B1068167 : Blo 279826 1068167 := bstep (se 1 (by rfl) ⟨801125, by rfl⟩ : syracuseStep 1068167 = 1602251) B1602251
theorem B1428839 : Blo 279826 1428839 := bstep (se 1 (by rfl) ⟨1071629, by rfl⟩ : syracuseStep 1428839 = 2143259) B2143259
theorem B282479 : Blo 279826 282479 := bstep (se 1 (by rfl) ⟨211859, by rfl⟩ : syracuseStep 282479 = 423719) B423719
theorem B5820929 : Blo 279826 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B807823 : Blo 279826 807823 := bstep (se 1 (by rfl) ⟨605867, by rfl⟩ : syracuseStep 807823 = 1211735) B1211735
theorem B316543 : Blo 279826 316543 := bstep (se 1 (by rfl) ⟨237407, by rfl⟩ : syracuseStep 316543 = 474815) B474815
theorem B5822239 : Blo 279826 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B34527059 : Blo 279826 34527059 := bstep (se 1 (by rfl) ⟨25895294, by rfl⟩ : syracuseStep 34527059 = 51790589) B51790589
theorem B1236023 : Blo 279826 1236023 := bstep (se 1 (by rfl) ⟨927017, by rfl⟩ : syracuseStep 1236023 = 1854035) B1854035
theorem B318559 : Blo 279826 318559 := bstep (se 1 (by rfl) ⟨238919, by rfl⟩ : syracuseStep 318559 = 477839) B477839
theorem B318631 : Blo 279826 318631 := bstep (se 1 (by rfl) ⟨238973, by rfl⟩ : syracuseStep 318631 = 477947) B477947
theorem B9330319 : Blo 279826 9330319 := bstep (se 1 (by rfl) ⟨6997739, by rfl⟩ : syracuseStep 9330319 = 13995479) B13995479
theorem B713063 : Blo 279826 713063 := bstep (se 1 (by rfl) ⟨534797, by rfl⟩ : syracuseStep 713063 = 1069595) B1069595
theorem B713711 : Blo 279826 713711 := bstep (se 1 (by rfl) ⟨535283, by rfl⟩ : syracuseStep 713711 = 1070567) B1070567
theorem B680987 : Blo 279826 680987 := bstep (se 1 (by rfl) ⟨510740, by rfl⟩ : syracuseStep 680987 = 1021481) B1021481
theorem B3597479 : Blo 279826 3597479 := bstep (se 1 (by rfl) ⟨2698109, by rfl⟩ : syracuseStep 3597479 = 5396219) B5396219
theorem B420287 : Blo 279826 420287 := bstep (se 1 (by rfl) ⟨315215, by rfl⟩ : syracuseStep 420287 = 630431) B630431
theorem B32828419 : Blo 279826 32828419 := bstep (se 1 (by rfl) ⟨24621314, by rfl⟩ : syracuseStep 32828419 = 49242629) B49242629
theorem B420959 : Blo 279826 420959 := bstep (se 1 (by rfl) ⟨315719, by rfl⟩ : syracuseStep 420959 = 631439) B631439
theorem B8908061 : Blo 279826 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B388415 : Blo 279826 388415 := bstep (se 1 (by rfl) ⟨291311, by rfl⟩ : syracuseStep 388415 = 582623) B582623
theorem B1799333 : Blo 279826 1799333 := bstep (se 4 (by rfl) ⟨168687, by rfl⟩ : syracuseStep 1799333 = 337375) B337375
theorem B1211719 : Blo 279826 1211719 := bstep (se 1 (by rfl) ⟨908789, by rfl⟩ : syracuseStep 1211719 = 1817579) B1817579
theorem B14876111 : Blo 279826 14876111 := bstep (se 1 (by rfl) ⟨11157083, by rfl⟩ : syracuseStep 14876111 = 22314167) B22314167
theorem B2392031 : Blo 279826 2392031 := bstep (se 1 (by rfl) ⟨1794023, by rfl⟩ : syracuseStep 2392031 = 3588047) B3588047
theorem B116623415 : Blo 279826 116623415 := bstep (se 1 (by rfl) ⟨87467561, by rfl⟩ : syracuseStep 116623415 = 174935123) B174935123
theorem B952559 : Blo 279826 952559 := bstep (se 1 (by rfl) ⟨714419, by rfl⟩ : syracuseStep 952559 = 1428839) B1428839
theorem B824015 : Blo 279826 824015 := bstep (se 1 (by rfl) ⟨618011, by rfl⟩ : syracuseStep 824015 = 1236023) B1236023
theorem B175084901 : Blo 279826 175084901 := bstep (se 4 (by rfl) ⟨16414209, by rfl⟩ : syracuseStep 175084901 = 32828419) B32828419
theorem B2398319 : Blo 279826 2398319 := bstep (se 1 (by rfl) ⟨1798739, by rfl⟩ : syracuseStep 2398319 = 3597479) B3597479
theorem B400079 : Blo 279826 400079 := bstep (se 1 (by rfl) ⟨300059, by rfl⟩ : syracuseStep 400079 = 600119) B600119
theorem B31072691 : Blo 279826 31072691 := bstep (se 1 (by rfl) ⟨23304518, by rfl⟩ : syracuseStep 31072691 = 46609037) B46609037
theorem B7741979 : Blo 279826 7741979 := bstep (se 1 (by rfl) ⟨5806484, by rfl⟩ : syracuseStep 7741979 = 11612969) B11612969
theorem B1615625 : Blo 279826 1615625 := bstep (se 2 (by rfl) ⟨605859, by rfl⟩ : syracuseStep 1615625 = 1211719) B1211719
theorem B1714601 : Blo 279826 1714601 := bstep (se 2 (by rfl) ⟨642975, by rfl⟩ : syracuseStep 1714601 = 1285951) B1285951
theorem B797435 : Blo 279826 797435 := bstep (se 1 (by rfl) ⟨598076, by rfl⟩ : syracuseStep 797435 = 1196153) B1196153
theorem B15708113 : Blo 279826 15708113 := bstep (se 2 (by rfl) ⟨5890542, by rfl⟩ : syracuseStep 15708113 = 11781085) B11781085
theorem B3880619 : Blo 279826 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B23018039 : Blo 279826 23018039 := bstep (se 1 (by rfl) ⟨17263529, by rfl⟩ : syracuseStep 23018039 = 34527059) B34527059
theorem B475375 : Blo 279826 475375 := bstep (se 1 (by rfl) ⟨356531, by rfl⟩ : syracuseStep 475375 = 713063) B713063
theorem B475807 : Blo 279826 475807 := bstep (se 1 (by rfl) ⟨356855, by rfl⟩ : syracuseStep 475807 = 713711) B713711
theorem B509183 : Blo 279826 509183 := bstep (se 1 (by rfl) ⟨381887, by rfl⟩ : syracuseStep 509183 = 763775) B763775
theorem B280191 : Blo 279826 280191 := bstep (se 1 (by rfl) ⟨210143, by rfl⟩ : syracuseStep 280191 = 420287) B420287
theorem B280639 : Blo 279826 280639 := bstep (se 1 (by rfl) ⟨210479, by rfl⟩ : syracuseStep 280639 = 420959) B420959
theorem B49761701 : Blo 279826 49761701 := bstep (se 4 (by rfl) ⟨4665159, by rfl⟩ : syracuseStep 49761701 = 9330319) B9330319
theorem B1199555 : Blo 279826 1199555 := bstep (se 1 (by rfl) ⟨899666, by rfl⟩ : syracuseStep 1199555 = 1799333) B1799333
theorem B1035773 : Blo 279826 1035773 := bstep (se 3 (by rfl) ⟨194207, by rfl⟩ : syracuseStep 1035773 = 388415) B388415
theorem B806753 : Blo 279826 806753 := bstep (se 2 (by rfl) ⟨302532, by rfl⟩ : syracuseStep 806753 = 605065) B605065
theorem B201478049 : Blo 279826 201478049 := bstep (se 2 (by rfl) ⟨75554268, by rfl⟩ : syracuseStep 201478049 = 151108537) B151108537
theorem B315643 : Blo 279826 315643 := bstep (se 1 (by rfl) ⟨236732, by rfl⟩ : syracuseStep 315643 = 473465) B473465
theorem B1069793 : Blo 279826 1069793 := bstep (se 2 (by rfl) ⟨401172, by rfl⟩ : syracuseStep 1069793 = 802345) B802345
theorem B9917407 : Blo 279826 9917407 := bstep (se 1 (by rfl) ⟨7438055, by rfl⟩ : syracuseStep 9917407 = 14876111) B14876111
theorem B1594687 : Blo 279826 1594687 := bstep (se 1 (by rfl) ⟨1196015, by rfl⟩ : syracuseStep 1594687 = 2392031) B2392031
theorem B4315447 : Blo 279826 4315447 := bstep (se 1 (by rfl) ⟨3236585, by rfl⟩ : syracuseStep 4315447 = 6473171) B6473171
theorem B777311 : Blo 279826 777311 := bstep (se 1 (by rfl) ⟨582983, by rfl⟩ : syracuseStep 777311 = 1165967) B1165967
theorem B8347049 : Blo 279826 8347049 := bstep (se 2 (by rfl) ⟨3130143, by rfl⟩ : syracuseStep 8347049 = 6260287) B6260287
theorem B712111 : Blo 279826 712111 := bstep (se 1 (by rfl) ⟨534083, by rfl⟩ : syracuseStep 712111 = 1068167) B1068167
theorem B419951 : Blo 279826 419951 := bstep (se 1 (by rfl) ⟨314963, by rfl⟩ : syracuseStep 419951 = 629927) B629927
theorem B354871 : Blo 279826 354871 := bstep (se 1 (by rfl) ⟨266153, by rfl⟩ : syracuseStep 354871 = 532307) B532307
theorem B6122303 : Blo 279826 6122303 := bstep (se 1 (by rfl) ⟨4591727, by rfl⟩ : syracuseStep 6122303 = 9183455) B9183455
theorem B1928377 : Blo 279826 1928377 := bstep (se 2 (by rfl) ⟨723141, by rfl⟩ : syracuseStep 1928377 = 1446283) B1446283
theorem B453991 : Blo 279826 453991 := bstep (se 1 (by rfl) ⟨340493, by rfl⟩ : syracuseStep 453991 = 680987) B680987
theorem B421631 : Blo 279826 421631 := bstep (se 1 (by rfl) ⟨316223, by rfl⟩ : syracuseStep 421631 = 632447) B632447
theorem B1077097 : Blo 279826 1077097 := bstep (se 2 (by rfl) ⟨403911, by rfl⟩ : syracuseStep 1077097 = 807823) B807823
theorem B421979 : Blo 279826 421979 := bstep (se 1 (by rfl) ⟨316484, by rfl⟩ : syracuseStep 421979 = 632969) B632969
theorem B422057 : Blo 279826 422057 := bstep (se 2 (by rfl) ⟨158271, by rfl⟩ : syracuseStep 422057 = 316543) B316543
theorem B2323109 : Blo 279826 2323109 := bstep (se 4 (by rfl) ⟨217791, by rfl⟩ : syracuseStep 2323109 = 435583) B435583
theorem B422783 : Blo 279826 422783 := bstep (se 1 (by rfl) ⟨317087, by rfl⟩ : syracuseStep 422783 = 634175) B634175
theorem B7762985 : Blo 279826 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B423143 : Blo 279826 423143 := bstep (se 1 (by rfl) ⟨317357, by rfl⟩ : syracuseStep 423143 = 634715) B634715
theorem B13334003 : Blo 279826 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B358015 : Blo 279826 358015 := bstep (se 1 (by rfl) ⟨268511, by rfl⟩ : syracuseStep 358015 = 537023) B537023
theorem B423599 : Blo 279826 423599 := bstep (se 1 (by rfl) ⟨317699, by rfl⟩ : syracuseStep 423599 = 635399) B635399
theorem B23754829 : Blo 279826 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B358607 : Blo 279826 358607 := bstep (se 1 (by rfl) ⟨268955, by rfl⟩ : syracuseStep 358607 = 537911) B537911
theorem B424559 : Blo 279826 424559 := bstep (se 1 (by rfl) ⟨318419, by rfl⟩ : syracuseStep 424559 = 636839) B636839
theorem B424745 : Blo 279826 424745 := bstep (se 2 (by rfl) ⟨159279, by rfl⟩ : syracuseStep 424745 = 318559) B318559
theorem B424841 : Blo 279826 424841 := bstep (se 2 (by rfl) ⟨159315, by rfl⟩ : syracuseStep 424841 = 318631) B318631
theorem B690515 : Blo 279826 690515 := bstep (se 1 (by rfl) ⟨517886, by rfl⟩ : syracuseStep 690515 = 1035773) B1035773
theorem B134318699 : Blo 279826 134318699 := bstep (se 1 (by rfl) ⟨100739024, by rfl⟩ : syracuseStep 134318699 = 201478049) B201478049
theorem B116723267 : Blo 279826 116723267 := bstep (se 1 (by rfl) ⟨87542450, by rfl⟩ : syracuseStep 116723267 = 175084901) B175084901
theorem B52892837 : Blo 279826 52892837 := bstep (se 4 (by rfl) ⟨4958703, by rfl⟩ : syracuseStep 52892837 = 9917407) B9917407
theorem B956285 : Blo 279826 956285 := bstep (se 3 (by rfl) ⟨179303, by rfl⟩ : syracuseStep 956285 = 358607) B358607
theorem B531623 : Blo 279826 531623 := bstep (se 1 (by rfl) ⟨398717, by rfl⟩ : syracuseStep 531623 = 797435) B797435
theorem B1548739 : Blo 279826 1548739 := bstep (se 1 (by rfl) ⟨1161554, by rfl⟩ : syracuseStep 1548739 = 2323109) B2323109
theorem B8889335 : Blo 279826 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B15345359 : Blo 279826 15345359 := bstep (se 1 (by rfl) ⟨11509019, by rfl⟩ : syracuseStep 15345359 = 23018039) B23018039
theorem B633833 : Blo 279826 633833 := bstep (se 2 (by rfl) ⟨237687, by rfl⟩ : syracuseStep 633833 = 475375) B475375
theorem B339455 : Blo 279826 339455 := bstep (se 1 (by rfl) ⟨254591, by rfl⟩ : syracuseStep 339455 = 509183) B509183
theorem B634409 : Blo 279826 634409 := bstep (se 2 (by rfl) ⟨237903, by rfl⟩ : syracuseStep 634409 = 475807) B475807
theorem B635039 : Blo 279826 635039 := bstep (se 1 (by rfl) ⟨476279, by rfl⟩ : syracuseStep 635039 = 952559) B952559
theorem B33174467 : Blo 279826 33174467 := bstep (se 1 (by rfl) ⟨24880850, by rfl⟩ : syracuseStep 33174467 = 49761701) B49761701
theorem B799703 : Blo 279826 799703 := bstep (se 1 (by rfl) ⟨599777, by rfl⟩ : syracuseStep 799703 = 1199555) B1199555
theorem B537835 : Blo 279826 537835 := bstep (se 1 (by rfl) ⟨403376, by rfl⟩ : syracuseStep 537835 = 806753) B806753
theorem B473161 : Blo 279826 473161 := bstep (se 2 (by rfl) ⟨177435, by rfl⟩ : syracuseStep 473161 = 354871) B354871
theorem B605321 : Blo 279826 605321 := bstep (se 2 (by rfl) ⟨226995, by rfl⟩ : syracuseStep 605321 = 453991) B453991
theorem B5161319 : Blo 279826 5161319 := bstep (se 1 (by rfl) ⟨3870989, by rfl⟩ : syracuseStep 5161319 = 7741979) B7741979
theorem B279967 : Blo 279826 279967 := bstep (se 1 (by rfl) ⟨209975, by rfl⟩ : syracuseStep 279967 = 419951) B419951
theorem B1066877 : Blo 279826 1066877 := bstep (se 3 (by rfl) ⟨200039, by rfl⟩ : syracuseStep 1066877 = 400079) B400079
theorem B4081535 : Blo 279826 4081535 := bstep (se 1 (by rfl) ⟨3061151, by rfl⟩ : syracuseStep 4081535 = 6122303) B6122303
theorem B477353 : Blo 279826 477353 := bstep (se 2 (by rfl) ⟨179007, by rfl⟩ : syracuseStep 477353 = 358015) B358015
theorem B281087 : Blo 279826 281087 := bstep (se 1 (by rfl) ⟨210815, by rfl⟩ : syracuseStep 281087 = 421631) B421631
theorem B10472075 : Blo 279826 10472075 := bstep (se 1 (by rfl) ⟨7854056, by rfl⟩ : syracuseStep 10472075 = 15708113) B15708113
theorem B281319 : Blo 279826 281319 := bstep (se 1 (by rfl) ⟨210989, by rfl⟩ : syracuseStep 281319 = 421979) B421979
theorem B31673105 : Blo 279826 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B281371 : Blo 279826 281371 := bstep (se 1 (by rfl) ⟨211028, by rfl⟩ : syracuseStep 281371 = 422057) B422057
theorem B5753929 : Blo 279826 5753929 := bstep (se 2 (by rfl) ⟨2157723, by rfl⟩ : syracuseStep 5753929 = 4315447) B4315447
theorem B281855 : Blo 279826 281855 := bstep (se 1 (by rfl) ⟨211391, by rfl⟩ : syracuseStep 281855 = 422783) B422783
theorem B282095 : Blo 279826 282095 := bstep (se 1 (by rfl) ⟨211571, by rfl⟩ : syracuseStep 282095 = 423143) B423143
theorem B282399 : Blo 279826 282399 := bstep (se 1 (by rfl) ⟨211799, by rfl⟩ : syracuseStep 282399 = 423599) B423599
theorem B283039 : Blo 279826 283039 := bstep (se 1 (by rfl) ⟨212279, by rfl⟩ : syracuseStep 283039 = 424559) B424559
theorem B283163 : Blo 279826 283163 := bstep (se 1 (by rfl) ⟨212372, by rfl⟩ : syracuseStep 283163 = 424745) B424745
theorem B283227 : Blo 279826 283227 := bstep (se 1 (by rfl) ⟨212420, by rfl⟩ : syracuseStep 283227 = 424841) B424841
theorem B82860509 : Blo 279826 82860509 := bstep (se 3 (by rfl) ⟨15536345, by rfl⟩ : syracuseStep 82860509 = 31072691) B31072691
theorem B77748943 : Blo 279826 77748943 := bstep (se 1 (by rfl) ⟨58311707, by rfl⟩ : syracuseStep 77748943 = 116623415) B116623415
theorem B549343 : Blo 279826 549343 := bstep (se 1 (by rfl) ⟨412007, by rfl⟩ : syracuseStep 549343 = 824015) B824015
theorem B713195 : Blo 279826 713195 := bstep (se 1 (by rfl) ⟨534896, by rfl⟩ : syracuseStep 713195 = 1069793) B1069793
theorem B1598879 : Blo 279826 1598879 := bstep (se 1 (by rfl) ⟨1199159, by rfl⟩ : syracuseStep 1598879 = 2398319) B2398319
theorem B518207 : Blo 279826 518207 := bstep (se 1 (by rfl) ⟨388655, by rfl⟩ : syracuseStep 518207 = 777311) B777311
theorem B5564699 : Blo 279826 5564699 := bstep (se 1 (by rfl) ⟨4173524, by rfl⟩ : syracuseStep 5564699 = 8347049) B8347049
theorem B1436129 : Blo 279826 1436129 := bstep (se 2 (by rfl) ⟨538548, by rfl⟩ : syracuseStep 1436129 = 1077097) B1077097
theorem B420857 : Blo 279826 420857 := bstep (se 2 (by rfl) ⟨157821, by rfl⟩ : syracuseStep 420857 = 315643) B315643
theorem B10284677 : Blo 279826 10284677 := bstep (se 4 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 10284677 = 1928377) B1928377
theorem B1077083 : Blo 279826 1077083 := bstep (se 1 (by rfl) ⟨807812, by rfl⟩ : syracuseStep 1077083 = 1615625) B1615625
theorem B1143067 : Blo 279826 1143067 := bstep (se 1 (by rfl) ⟨857300, by rfl⟩ : syracuseStep 1143067 = 1714601) B1714601
theorem B2126249 : Blo 279826 2126249 := bstep (se 2 (by rfl) ⟨797343, by rfl⟩ : syracuseStep 2126249 = 1594687) B1594687
theorem B5175323 : Blo 279826 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B2587079 : Blo 279826 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B949481 : Blo 279826 949481 := bstep (se 2 (by rfl) ⟨356055, by rfl⟩ : syracuseStep 949481 = 712111) B712111
theorem B3440879 : Blo 279826 3440879 := bstep (se 1 (by rfl) ⟨2580659, by rfl⟩ : syracuseStep 3440879 = 5161319) B5161319
theorem B2721023 : Blo 279826 2721023 := bstep (se 1 (by rfl) ⟨2040767, by rfl⟩ : syracuseStep 2721023 = 4081535) B4081535
theorem B460343 : Blo 279826 460343 := bstep (se 1 (by rfl) ⟨345257, by rfl⟩ : syracuseStep 460343 = 690515) B690515
theorem B6981383 : Blo 279826 6981383 := bstep (se 1 (by rfl) ⟨5236037, by rfl⟩ : syracuseStep 6981383 = 10472075) B10472075
theorem B8259941 : Blo 279826 8259941 := bstep (se 4 (by rfl) ⟨774369, by rfl⟩ : syracuseStep 8259941 = 1548739) B1548739
theorem B35261891 : Blo 279826 35261891 := bstep (se 1 (by rfl) ⟨26446418, by rfl⟩ : syracuseStep 35261891 = 52892837) B52892837
theorem B7671905 : Blo 279826 7671905 := bstep (se 2 (by rfl) ⟨2876964, by rfl⟩ : syracuseStep 7671905 = 5753929) B5753929
theorem B10230239 : Blo 279826 10230239 := bstep (se 1 (by rfl) ⟨7672679, by rfl⟩ : syracuseStep 10230239 = 15345359) B15345359
theorem B3709799 : Blo 279826 3709799 := bstep (se 1 (by rfl) ⟨2782349, by rfl⟩ : syracuseStep 3709799 = 5564699) B5564699
theorem B957419 : Blo 279826 957419 := bstep (se 1 (by rfl) ⟨718064, by rfl⟩ : syracuseStep 957419 = 1436129) B1436129
theorem B6856451 : Blo 279826 6856451 := bstep (se 1 (by rfl) ⟨5142338, by rfl⟩ : syracuseStep 6856451 = 10284677) B10284677
theorem B630881 : Blo 279826 630881 := bstep (se 2 (by rfl) ⟨236580, by rfl⟩ : syracuseStep 630881 = 473161) B473161
theorem B1417499 : Blo 279826 1417499 := bstep (se 1 (by rfl) ⟨1063124, by rfl⟩ : syracuseStep 1417499 = 2126249) B2126249
theorem B1417661 : Blo 279826 1417661 := bstep (se 3 (by rfl) ⟨265811, by rfl⟩ : syracuseStep 1417661 = 531623) B531623
theorem B533135 : Blo 279826 533135 := bstep (se 1 (by rfl) ⟨399851, by rfl⟩ : syracuseStep 533135 = 799703) B799703
theorem B3450215 : Blo 279826 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B403547 : Blo 279826 403547 := bstep (se 1 (by rfl) ⟨302660, by rfl⟩ : syracuseStep 403547 = 605321) B605321
theorem B632987 : Blo 279826 632987 := bstep (se 1 (by rfl) ⟨474740, by rfl⟩ : syracuseStep 632987 = 949481) B949481
theorem B21115403 : Blo 279826 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B2929829 : Blo 279826 2929829 := bstep (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) B549343
theorem B637523 : Blo 279826 637523 := bstep (se 1 (by rfl) ⟨478142, by rfl⟩ : syracuseStep 637523 = 956285) B956285
theorem B475463 : Blo 279826 475463 := bstep (se 1 (by rfl) ⟨356597, by rfl⟩ : syracuseStep 475463 = 713195) B713195
theorem B1524089 : Blo 279826 1524089 := bstep (se 2 (by rfl) ⟨571533, by rfl⟩ : syracuseStep 1524089 = 1143067) B1143067
theorem B1065919 : Blo 279826 1065919 := bstep (se 1 (by rfl) ⟨799439, by rfl⟩ : syracuseStep 1065919 = 1598879) B1598879
theorem B6898877 : Blo 279826 6898877 := bstep (se 3 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 6898877 = 2587079) B2587079
theorem B280571 : Blo 279826 280571 := bstep (se 1 (by rfl) ⟨210428, by rfl⟩ : syracuseStep 280571 = 420857) B420857
theorem B103665257 : Blo 279826 103665257 := bstep (se 2 (by rfl) ⟨38874471, by rfl⟩ : syracuseStep 103665257 = 77748943) B77748943
theorem B905213 : Blo 279826 905213 := bstep (se 3 (by rfl) ⟨169727, by rfl⟩ : syracuseStep 905213 = 339455) B339455
theorem B5527541 : Blo 279826 5527541 := bstep (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) B518207
theorem B711251 : Blo 279826 711251 := bstep (se 1 (by rfl) ⟨533438, by rfl⟩ : syracuseStep 711251 = 1066877) B1066877
theorem B318235 : Blo 279826 318235 := bstep (se 1 (by rfl) ⟨238676, by rfl⟩ : syracuseStep 318235 = 477353) B477353
theorem B89545799 : Blo 279826 89545799 := bstep (se 1 (by rfl) ⟨67159349, by rfl⟩ : syracuseStep 89545799 = 134318699) B134318699
theorem B77815511 : Blo 279826 77815511 := bstep (se 1 (by rfl) ⟨58361633, by rfl⟩ : syracuseStep 77815511 = 116723267) B116723267
theorem B55240339 : Blo 279826 55240339 := bstep (se 1 (by rfl) ⟨41430254, by rfl⟩ : syracuseStep 55240339 = 82860509) B82860509
theorem B5926223 : Blo 279826 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B717113 : Blo 279826 717113 := bstep (se 2 (by rfl) ⟨268917, by rfl⟩ : syracuseStep 717113 = 537835) B537835
theorem B422555 : Blo 279826 422555 := bstep (se 1 (by rfl) ⟨316916, by rfl⟩ : syracuseStep 422555 = 633833) B633833
theorem B422939 : Blo 279826 422939 := bstep (se 1 (by rfl) ⟨317204, by rfl⟩ : syracuseStep 422939 = 634409) B634409
theorem B718055 : Blo 279826 718055 := bstep (se 1 (by rfl) ⟨538541, by rfl⟩ : syracuseStep 718055 = 1077083) B1077083
theorem B423359 : Blo 279826 423359 := bstep (se 1 (by rfl) ⟨317519, by rfl⟩ : syracuseStep 423359 = 635039) B635039
theorem B22116311 : Blo 279826 22116311 := bstep (se 1 (by rfl) ⟨16587233, by rfl⟩ : syracuseStep 22116311 = 33174467) B33174467
theorem B2293919 : Blo 279826 2293919 := bstep (se 1 (by rfl) ⟨1720439, by rfl⟩ : syracuseStep 2293919 = 3440879) B3440879
theorem B1016059 : Blo 279826 1016059 := bstep (se 1 (by rfl) ⟨762044, by rfl⟩ : syracuseStep 1016059 = 1524089) B1524089
theorem B4654255 : Blo 279826 4654255 := bstep (se 1 (by rfl) ⟨3490691, by rfl⟩ : syracuseStep 4654255 = 6981383) B6981383
theorem B5506627 : Blo 279826 5506627 := bstep (se 1 (by rfl) ⟨4129970, by rfl⟩ : syracuseStep 5506627 = 8259941) B8259941
theorem B69110171 : Blo 279826 69110171 := bstep (se 1 (by rfl) ⟨51832628, by rfl⟩ : syracuseStep 69110171 = 103665257) B103665257
theorem B5114603 : Blo 279826 5114603 := bstep (se 1 (by rfl) ⟨3835952, by rfl⟩ : syracuseStep 5114603 = 7671905) B7671905
theorem B51877007 : Blo 279826 51877007 := bstep (se 1 (by rfl) ⟨38907755, by rfl⟩ : syracuseStep 51877007 = 77815511) B77815511
theorem B4599251 : Blo 279826 4599251 := bstep (se 1 (by rfl) ⟨3449438, by rfl⟩ : syracuseStep 4599251 = 6898877) B6898877
theorem B1814015 : Blo 279826 1814015 := bstep (se 1 (by rfl) ⟨1360511, by rfl⟩ : syracuseStep 1814015 = 2721023) B2721023
theorem B1421225 : Blo 279826 1421225 := bstep (se 2 (by rfl) ⟨532959, by rfl⟩ : syracuseStep 1421225 = 1065919) B1065919
theorem B23507927 : Blo 279826 23507927 := bstep (se 1 (by rfl) ⟨17630945, by rfl⟩ : syracuseStep 23507927 = 35261891) B35261891
theorem B7812877 : Blo 279826 7812877 := bstep (se 3 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 7812877 = 2929829) B2929829
theorem B3685027 : Blo 279826 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B1227581 : Blo 279826 1227581 := bstep (se 3 (by rfl) ⟨230171, by rfl⟩ : syracuseStep 1227581 = 460343) B460343
theorem B474167 : Blo 279826 474167 := bstep (se 1 (by rfl) ⟨355625, by rfl⟩ : syracuseStep 474167 = 711251) B711251
theorem B2473199 : Blo 279826 2473199 := bstep (se 1 (by rfl) ⟨1854899, by rfl⟩ : syracuseStep 2473199 = 3709799) B3709799
theorem B638279 : Blo 279826 638279 := bstep (se 1 (by rfl) ⟨478709, by rfl⟩ : syracuseStep 638279 = 957419) B957419
theorem B4570967 : Blo 279826 4570967 := bstep (se 1 (by rfl) ⟨3428225, by rfl⟩ : syracuseStep 4570967 = 6856451) B6856451
theorem B27280637 : Blo 279826 27280637 := bstep (se 3 (by rfl) ⟨5115119, by rfl⟩ : syracuseStep 27280637 = 10230239) B10230239
theorem B3950815 : Blo 279826 3950815 := bstep (se 1 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 3950815 = 5926223) B5926223
theorem B478075 : Blo 279826 478075 := bstep (se 1 (by rfl) ⟨358556, by rfl⟩ : syracuseStep 478075 = 717113) B717113
theorem B14076935 : Blo 279826 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B281703 : Blo 279826 281703 := bstep (se 1 (by rfl) ⟨211277, by rfl⟩ : syracuseStep 281703 = 422555) B422555
theorem B281959 : Blo 279826 281959 := bstep (se 1 (by rfl) ⟨211469, by rfl⟩ : syracuseStep 281959 = 422939) B422939
theorem B478703 : Blo 279826 478703 := bstep (se 1 (by rfl) ⟨359027, by rfl⟩ : syracuseStep 478703 = 718055) B718055
theorem B282239 : Blo 279826 282239 := bstep (se 1 (by rfl) ⟨211679, by rfl⟩ : syracuseStep 282239 = 423359) B423359
theorem B2413901 : Blo 279826 2413901 := bstep (se 3 (by rfl) ⟨452606, by rfl⟩ : syracuseStep 2413901 = 905213) B905213
theorem B316975 : Blo 279826 316975 := bstep (se 1 (by rfl) ⟨237731, by rfl⟩ : syracuseStep 316975 = 475463) B475463
theorem B73653785 : Blo 279826 73653785 := bstep (se 2 (by rfl) ⟨27620169, by rfl⟩ : syracuseStep 73653785 = 55240339) B55240339
theorem B9200573 : Blo 279826 9200573 := bstep (se 3 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 9200573 = 3450215) B3450215
theorem B59697199 : Blo 279826 59697199 := bstep (se 1 (by rfl) ⟨44772899, by rfl⟩ : syracuseStep 59697199 = 89545799) B89545799
theorem B420587 : Blo 279826 420587 := bstep (se 1 (by rfl) ⟨315440, by rfl⟩ : syracuseStep 420587 = 630881) B630881
theorem B944999 : Blo 279826 944999 := bstep (se 1 (by rfl) ⟨708749, by rfl⟩ : syracuseStep 944999 = 1417499) B1417499
theorem B1076125 : Blo 279826 1076125 := bstep (se 3 (by rfl) ⟨201773, by rfl⟩ : syracuseStep 1076125 = 403547) B403547
theorem B945107 : Blo 279826 945107 := bstep (se 1 (by rfl) ⟨708830, by rfl⟩ : syracuseStep 945107 = 1417661) B1417661
theorem B355423 : Blo 279826 355423 := bstep (se 1 (by rfl) ⟨266567, by rfl⟩ : syracuseStep 355423 = 533135) B533135
theorem B421991 : Blo 279826 421991 := bstep (se 1 (by rfl) ⟨316493, by rfl⟩ : syracuseStep 421991 = 632987) B632987
theorem B424313 : Blo 279826 424313 := bstep (se 2 (by rfl) ⟨159117, by rfl⟩ : syracuseStep 424313 = 318235) B318235
theorem B14744207 : Blo 279826 14744207 := bstep (se 1 (by rfl) ⟨11058155, by rfl⟩ : syracuseStep 14744207 = 22116311) B22116311
theorem B425015 : Blo 279826 425015 := bstep (se 1 (by rfl) ⟨318761, by rfl⟩ : syracuseStep 425015 = 637523) B637523
theorem B18187091 : Blo 279826 18187091 := bstep (se 1 (by rfl) ⟨13640318, by rfl⟩ : syracuseStep 18187091 = 27280637) B27280637
theorem B46073447 : Blo 279826 46073447 := bstep (se 1 (by rfl) ⟨34555085, by rfl⟩ : syracuseStep 46073447 = 69110171) B69110171
theorem B3409735 : Blo 279826 3409735 := bstep (se 1 (by rfl) ⟨2557301, by rfl⟩ : syracuseStep 3409735 = 5114603) B5114603
theorem B7342169 : Blo 279826 7342169 := bstep (se 2 (by rfl) ⟨2753313, by rfl⟩ : syracuseStep 7342169 = 5506627) B5506627
theorem B79596265 : Blo 279826 79596265 := bstep (se 2 (by rfl) ⟨29848599, by rfl⟩ : syracuseStep 79596265 = 59697199) B59697199
theorem B1609267 : Blo 279826 1609267 := bstep (se 1 (by rfl) ⟨1206950, by rfl⟩ : syracuseStep 1609267 = 2413901) B2413901
theorem B6133715 : Blo 279826 6133715 := bstep (se 1 (by rfl) ⟨4600286, by rfl⟩ : syracuseStep 6133715 = 9200573) B9200573
theorem B629999 : Blo 279826 629999 := bstep (se 1 (by rfl) ⟨472499, by rfl⟩ : syracuseStep 629999 = 944999) B944999
theorem B630071 : Blo 279826 630071 := bstep (se 1 (by rfl) ⟨472553, by rfl⟩ : syracuseStep 630071 = 945107) B945107
theorem B15671951 : Blo 279826 15671951 := bstep (se 1 (by rfl) ⟨11753963, by rfl⟩ : syracuseStep 15671951 = 23507927) B23507927
theorem B1648799 : Blo 279826 1648799 := bstep (se 1 (by rfl) ⟨1236599, by rfl⟩ : syracuseStep 1648799 = 2473199) B2473199
theorem B1354745 : Blo 279826 1354745 := bstep (se 2 (by rfl) ⟨508029, by rfl⟩ : syracuseStep 1354745 = 1016059) B1016059
theorem B6205673 : Blo 279826 6205673 := bstep (se 2 (by rfl) ⟨2327127, by rfl⟩ : syracuseStep 6205673 = 4654255) B4654255
theorem B9384623 : Blo 279826 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B34584671 : Blo 279826 34584671 := bstep (se 1 (by rfl) ⟨25938503, by rfl⟩ : syracuseStep 34584671 = 51877007) B51877007
theorem B637433 : Blo 279826 637433 := bstep (se 2 (by rfl) ⟨239037, by rfl⟩ : syracuseStep 637433 = 478075) B478075
theorem B473897 : Blo 279826 473897 := bstep (se 2 (by rfl) ⟨177711, by rfl⟩ : syracuseStep 473897 = 355423) B355423
theorem B49102523 : Blo 279826 49102523 := bstep (se 1 (by rfl) ⟨36826892, by rfl⟩ : syracuseStep 49102523 = 73653785) B73653785
theorem B280391 : Blo 279826 280391 := bstep (se 1 (by rfl) ⟨210293, by rfl⟩ : syracuseStep 280391 = 420587) B420587
theorem B3066167 : Blo 279826 3066167 := bstep (se 1 (by rfl) ⟨2299625, by rfl⟩ : syracuseStep 3066167 = 4599251) B4599251
theorem B281327 : Blo 279826 281327 := bstep (se 1 (by rfl) ⟨210995, by rfl⟩ : syracuseStep 281327 = 421991) B421991
theorem B282875 : Blo 279826 282875 := bstep (se 1 (by rfl) ⟨212156, by rfl⟩ : syracuseStep 282875 = 424313) B424313
theorem B316111 : Blo 279826 316111 := bstep (se 1 (by rfl) ⟨237083, by rfl⟩ : syracuseStep 316111 = 474167) B474167
theorem B283343 : Blo 279826 283343 := bstep (se 1 (by rfl) ⟨212507, by rfl⟩ : syracuseStep 283343 = 425015) B425015
theorem B1529279 : Blo 279826 1529279 := bstep (se 1 (by rfl) ⟨1146959, by rfl⟩ : syracuseStep 1529279 = 2293919) B2293919
theorem B319135 : Blo 279826 319135 := bstep (se 1 (by rfl) ⟨239351, by rfl⟩ : syracuseStep 319135 = 478703) B478703
theorem B5267753 : Blo 279826 5267753 := bstep (se 2 (by rfl) ⟨1975407, by rfl⟩ : syracuseStep 5267753 = 3950815) B3950815
theorem B1434833 : Blo 279826 1434833 := bstep (se 2 (by rfl) ⟨538062, by rfl⟩ : syracuseStep 1434833 = 1076125) B1076125
theorem B422633 : Blo 279826 422633 := bstep (se 2 (by rfl) ⟨158487, by rfl⟩ : syracuseStep 422633 = 316975) B316975
theorem B1209343 : Blo 279826 1209343 := bstep (se 1 (by rfl) ⟨907007, by rfl⟩ : syracuseStep 1209343 = 1814015) B1814015
theorem B10417169 : Blo 279826 10417169 := bstep (se 2 (by rfl) ⟨3906438, by rfl⟩ : syracuseStep 10417169 = 7812877) B7812877
theorem B947483 : Blo 279826 947483 := bstep (se 1 (by rfl) ⟨710612, by rfl⟩ : syracuseStep 947483 = 1421225) B1421225
theorem B4913369 : Blo 279826 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B9829471 : Blo 279826 9829471 := bstep (se 1 (by rfl) ⟨7372103, by rfl⟩ : syracuseStep 9829471 = 14744207) B14744207
theorem B818387 : Blo 279826 818387 := bstep (se 1 (by rfl) ⟨613790, by rfl⟩ : syracuseStep 818387 = 1227581) B1227581
theorem B425519 : Blo 279826 425519 := bstep (se 1 (by rfl) ⟨319139, by rfl⟩ : syracuseStep 425519 = 638279) B638279
theorem B3047311 : Blo 279826 3047311 := bstep (se 1 (by rfl) ⟨2285483, by rfl⟩ : syracuseStep 3047311 = 4570967) B4570967
theorem B12124727 : Blo 279826 12124727 := bstep (se 1 (by rfl) ⟨9093545, by rfl⟩ : syracuseStep 12124727 = 18187091) B18187091
theorem B16548461 : Blo 279826 16548461 := bstep (se 3 (by rfl) ⟨3102836, by rfl⟩ : syracuseStep 16548461 = 6205673) B6205673
theorem B1019519 : Blo 279826 1019519 := bstep (se 1 (by rfl) ⟨764639, by rfl⟩ : syracuseStep 1019519 = 1529279) B1529279
theorem B3511835 : Blo 279826 3511835 := bstep (se 1 (by rfl) ⟨2633876, by rfl⟩ : syracuseStep 3511835 = 5267753) B5267753
theorem B956555 : Blo 279826 956555 := bstep (se 1 (by rfl) ⟨717416, by rfl⟩ : syracuseStep 956555 = 1434833) B1434833
theorem B1612457 : Blo 279826 1612457 := bstep (se 2 (by rfl) ⟨604671, by rfl⟩ : syracuseStep 1612457 = 1209343) B1209343
theorem B631655 : Blo 279826 631655 := bstep (se 1 (by rfl) ⟨473741, by rfl⟩ : syracuseStep 631655 = 947483) B947483
theorem B30715631 : Blo 279826 30715631 := bstep (se 1 (by rfl) ⟨23036723, by rfl⟩ : syracuseStep 30715631 = 46073447) B46073447
theorem B2044111 : Blo 279826 2044111 := bstep (se 1 (by rfl) ⟨1533083, by rfl⟩ : syracuseStep 2044111 = 3066167) B3066167
theorem B2145689 : Blo 279826 2145689 := bstep (se 2 (by rfl) ⟨804633, by rfl⟩ : syracuseStep 2145689 = 1609267) B1609267
theorem B19579117 : Blo 279826 19579117 := bstep (se 3 (by rfl) ⟨3671084, by rfl⟩ : syracuseStep 19579117 = 7342169) B7342169
theorem B1099199 : Blo 279826 1099199 := bstep (se 1 (by rfl) ⟨824399, by rfl⟩ : syracuseStep 1099199 = 1648799) B1648799
theorem B903163 : Blo 279826 903163 := bstep (se 1 (by rfl) ⟨677372, by rfl⟩ : syracuseStep 903163 = 1354745) B1354745
theorem B281755 : Blo 279826 281755 := bstep (se 1 (by rfl) ⟨211316, by rfl⟩ : syracuseStep 281755 = 422633) B422633
theorem B23056447 : Blo 279826 23056447 := bstep (se 1 (by rfl) ⟨17292335, by rfl⟩ : syracuseStep 23056447 = 34584671) B34584671
theorem B315931 : Blo 279826 315931 := bstep (se 1 (by rfl) ⟨236948, by rfl⟩ : syracuseStep 315931 = 473897) B473897
theorem B545591 : Blo 279826 545591 := bstep (se 1 (by rfl) ⟨409193, by rfl⟩ : syracuseStep 545591 = 818387) B818387
theorem B283679 : Blo 279826 283679 := bstep (se 1 (by rfl) ⟨212759, by rfl⟩ : syracuseStep 283679 = 425519) B425519
theorem B4546313 : Blo 279826 4546313 := bstep (se 2 (by rfl) ⟨1704867, by rfl⟩ : syracuseStep 4546313 = 3409735) B3409735
theorem B106128353 : Blo 279826 106128353 := bstep (se 2 (by rfl) ⟨39798132, by rfl⟩ : syracuseStep 106128353 = 79596265) B79596265
theorem B4089143 : Blo 279826 4089143 := bstep (se 1 (by rfl) ⟨3066857, by rfl⟩ : syracuseStep 4089143 = 6133715) B6133715
theorem B419999 : Blo 279826 419999 := bstep (se 1 (by rfl) ⟨314999, by rfl⟩ : syracuseStep 419999 = 629999) B629999
theorem B420047 : Blo 279826 420047 := bstep (se 1 (by rfl) ⟨315035, by rfl⟩ : syracuseStep 420047 = 630071) B630071
theorem B10447967 : Blo 279826 10447967 := bstep (se 1 (by rfl) ⟨7835975, by rfl⟩ : syracuseStep 10447967 = 15671951) B15671951
theorem B421481 : Blo 279826 421481 := bstep (se 2 (by rfl) ⟨158055, by rfl⟩ : syracuseStep 421481 = 316111) B316111
theorem B6256415 : Blo 279826 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B6944779 : Blo 279826 6944779 := bstep (se 1 (by rfl) ⟨5208584, by rfl⟩ : syracuseStep 6944779 = 10417169) B10417169
theorem B13105961 : Blo 279826 13105961 := bstep (se 2 (by rfl) ⟨4914735, by rfl⟩ : syracuseStep 13105961 = 9829471) B9829471
theorem B3275579 : Blo 279826 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B424955 : Blo 279826 424955 := bstep (se 1 (by rfl) ⟨318716, by rfl⟩ : syracuseStep 424955 = 637433) B637433
theorem B425513 : Blo 279826 425513 := bstep (se 2 (by rfl) ⟨159567, by rfl⟩ : syracuseStep 425513 = 319135) B319135
theorem B32735015 : Blo 279826 32735015 := bstep (se 1 (by rfl) ⟨24551261, by rfl⟩ : syracuseStep 32735015 = 49102523) B49102523
theorem B4063081 : Blo 279826 4063081 := bstep (se 2 (by rfl) ⟨1523655, by rfl⟩ : syracuseStep 4063081 = 3047311) B3047311
theorem B363727 : Blo 279826 363727 := bstep (se 1 (by rfl) ⟨272795, by rfl⟩ : syracuseStep 363727 = 545591) B545591
theorem B30741929 : Blo 279826 30741929 := bstep (se 2 (by rfl) ⟨11528223, by rfl⟩ : syracuseStep 30741929 = 23056447) B23056447
theorem B2725481 : Blo 279826 2725481 := bstep (se 2 (by rfl) ⟨1022055, by rfl⟩ : syracuseStep 2725481 = 2044111) B2044111
theorem B4170943 : Blo 279826 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B5417441 : Blo 279826 5417441 := bstep (se 2 (by rfl) ⟨2031540, by rfl⟩ : syracuseStep 5417441 = 4063081) B4063081
theorem B2341223 : Blo 279826 2341223 := bstep (se 1 (by rfl) ⟨1755917, by rfl⟩ : syracuseStep 2341223 = 3511835) B3511835
theorem B2931197 : Blo 279826 2931197 := bstep (se 3 (by rfl) ⟨549599, by rfl⟩ : syracuseStep 2931197 = 1099199) B1099199
theorem B637703 : Blo 279826 637703 := bstep (se 1 (by rfl) ⟨478277, by rfl⟩ : syracuseStep 637703 = 956555) B956555
theorem B3030875 : Blo 279826 3030875 := bstep (se 1 (by rfl) ⟨2273156, by rfl⟩ : syracuseStep 3030875 = 4546313) B4546313
theorem B279999 : Blo 279826 279999 := bstep (se 1 (by rfl) ⟨209999, by rfl⟩ : syracuseStep 279999 = 419999) B419999
theorem B280031 : Blo 279826 280031 := bstep (se 1 (by rfl) ⟨210023, by rfl⟩ : syracuseStep 280031 = 420047) B420047
theorem B6965311 : Blo 279826 6965311 := bstep (se 1 (by rfl) ⟨5223983, by rfl⟩ : syracuseStep 6965311 = 10447967) B10447967
theorem B8734877 : Blo 279826 8734877 := bstep (se 3 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 8734877 = 3275579) B3275579
theorem B280987 : Blo 279826 280987 := bstep (se 1 (by rfl) ⟨210740, by rfl⟩ : syracuseStep 280987 = 421481) B421481
theorem B9259705 : Blo 279826 9259705 := bstep (se 2 (by rfl) ⟨3472389, by rfl⟩ : syracuseStep 9259705 = 6944779) B6944779
theorem B8737307 : Blo 279826 8737307 := bstep (se 1 (by rfl) ⟨6552980, by rfl⟩ : syracuseStep 8737307 = 13105961) B13105961
theorem B283303 : Blo 279826 283303 := bstep (se 1 (by rfl) ⟨212477, by rfl⟩ : syracuseStep 283303 = 424955) B424955
theorem B1430459 : Blo 279826 1430459 := bstep (se 1 (by rfl) ⟨1072844, by rfl⟩ : syracuseStep 1430459 = 2145689) B2145689
theorem B283675 : Blo 279826 283675 := bstep (se 1 (by rfl) ⟨212756, by rfl⟩ : syracuseStep 283675 = 425513) B425513
theorem B26105489 : Blo 279826 26105489 := bstep (se 2 (by rfl) ⟨9789558, by rfl⟩ : syracuseStep 26105489 = 19579117) B19579117
theorem B8083151 : Blo 279826 8083151 := bstep (se 1 (by rfl) ⟨6062363, by rfl⟩ : syracuseStep 8083151 = 12124727) B12124727
theorem B11032307 : Blo 279826 11032307 := bstep (se 1 (by rfl) ⟨8274230, by rfl⟩ : syracuseStep 11032307 = 16548461) B16548461
theorem B679679 : Blo 279826 679679 := bstep (se 1 (by rfl) ⟨509759, by rfl⟩ : syracuseStep 679679 = 1019519) B1019519
theorem B283008941 : Blo 279826 283008941 := bstep (se 3 (by rfl) ⟨53064176, by rfl⟩ : syracuseStep 283008941 = 106128353) B106128353
theorem B1204217 : Blo 279826 1204217 := bstep (se 2 (by rfl) ⟨451581, by rfl⟩ : syracuseStep 1204217 = 903163) B903163
theorem B10904381 : Blo 279826 10904381 := bstep (se 3 (by rfl) ⟨2044571, by rfl⟩ : syracuseStep 10904381 = 4089143) B4089143
theorem B1074971 : Blo 279826 1074971 := bstep (se 1 (by rfl) ⟨806228, by rfl⟩ : syracuseStep 1074971 = 1612457) B1612457
theorem B421103 : Blo 279826 421103 := bstep (se 1 (by rfl) ⟨315827, by rfl⟩ : syracuseStep 421103 = 631655) B631655
theorem B421241 : Blo 279826 421241 := bstep (se 2 (by rfl) ⟨157965, by rfl⟩ : syracuseStep 421241 = 315931) B315931
theorem B20477087 : Blo 279826 20477087 := bstep (se 1 (by rfl) ⟨15357815, by rfl⟩ : syracuseStep 20477087 = 30715631) B30715631
theorem B21823343 : Blo 279826 21823343 := bstep (se 1 (by rfl) ⟨16367507, by rfl⟩ : syracuseStep 21823343 = 32735015) B32735015
theorem B953639 : Blo 279826 953639 := bstep (se 1 (by rfl) ⟨715229, by rfl⟩ : syracuseStep 953639 = 1430459) B1430459
theorem B17403659 : Blo 279826 17403659 := bstep (se 1 (by rfl) ⟨13052744, by rfl⟩ : syracuseStep 17403659 = 26105489) B26105489
theorem B31266101 : Blo 279826 31266101 := bstep (se 5 (by rfl) ⟨1465598, by rfl⟩ : syracuseStep 31266101 = 2931197) B2931197
theorem B3611627 : Blo 279826 3611627 := bstep (se 1 (by rfl) ⟨2708720, by rfl⟩ : syracuseStep 3611627 = 5417441) B5417441
theorem B9287081 : Blo 279826 9287081 := bstep (se 2 (by rfl) ⟨3482655, by rfl⟩ : syracuseStep 9287081 = 6965311) B6965311
theorem B20494619 : Blo 279826 20494619 := bstep (se 1 (by rfl) ⟨15370964, by rfl⟩ : syracuseStep 20494619 = 30741929) B30741929
theorem B1816987 : Blo 279826 1816987 := bstep (se 1 (by rfl) ⟨1362740, by rfl⟩ : syracuseStep 1816987 = 2725481) B2725481
theorem B5388767 : Blo 279826 5388767 := bstep (se 1 (by rfl) ⟨4041575, by rfl⟩ : syracuseStep 5388767 = 8083151) B8083151
theorem B7354871 : Blo 279826 7354871 := bstep (se 1 (by rfl) ⟨5516153, by rfl⟩ : syracuseStep 7354871 = 11032307) B11032307
theorem B802811 : Blo 279826 802811 := bstep (se 1 (by rfl) ⟨602108, by rfl⟩ : syracuseStep 802811 = 1204217) B1204217
theorem B280735 : Blo 279826 280735 := bstep (se 1 (by rfl) ⟨210551, by rfl⟩ : syracuseStep 280735 = 421103) B421103
theorem B280827 : Blo 279826 280827 := bstep (se 1 (by rfl) ⟨210620, by rfl⟩ : syracuseStep 280827 = 421241) B421241
theorem B13651391 : Blo 279826 13651391 := bstep (se 1 (by rfl) ⟨10238543, by rfl⟩ : syracuseStep 13651391 = 20477087) B20477087
theorem B1560815 : Blo 279826 1560815 := bstep (se 1 (by rfl) ⟨1170611, by rfl⟩ : syracuseStep 1560815 = 2341223) B2341223
theorem B2020583 : Blo 279826 2020583 := bstep (se 1 (by rfl) ⟨1515437, by rfl⟩ : syracuseStep 2020583 = 3030875) B3030875
theorem B5823251 : Blo 279826 5823251 := bstep (se 1 (by rfl) ⟨4367438, by rfl⟩ : syracuseStep 5823251 = 8734877) B8734877
theorem B5561257 : Blo 279826 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B5824871 : Blo 279826 5824871 := bstep (se 1 (by rfl) ⟨4368653, by rfl⟩ : syracuseStep 5824871 = 8737307) B8737307
theorem B12346273 : Blo 279826 12346273 := bstep (se 2 (by rfl) ⟨4629852, by rfl⟩ : syracuseStep 12346273 = 9259705) B9259705
theorem B484969 : Blo 279826 484969 := bstep (se 2 (by rfl) ⟨181863, by rfl⟩ : syracuseStep 484969 = 363727) B363727
theorem B453119 : Blo 279826 453119 := bstep (se 1 (by rfl) ⟨339839, by rfl⟩ : syracuseStep 453119 = 679679) B679679
theorem B188672627 : Blo 279826 188672627 := bstep (se 1 (by rfl) ⟨141504470, by rfl⟩ : syracuseStep 188672627 = 283008941) B283008941
theorem B7269587 : Blo 279826 7269587 := bstep (se 1 (by rfl) ⟨5452190, by rfl⟩ : syracuseStep 7269587 = 10904381) B10904381
theorem B716647 : Blo 279826 716647 := bstep (se 1 (by rfl) ⟨537485, by rfl⟩ : syracuseStep 716647 = 1074971) B1074971
theorem B425135 : Blo 279826 425135 := bstep (se 1 (by rfl) ⟨318851, by rfl⟩ : syracuseStep 425135 = 637703) B637703
theorem B14548895 : Blo 279826 14548895 := bstep (se 1 (by rfl) ⟨10911671, by rfl⟩ : syracuseStep 14548895 = 21823343) B21823343
theorem B11602439 : Blo 279826 11602439 := bstep (se 1 (by rfl) ⟨8701829, by rfl⟩ : syracuseStep 11602439 = 17403659) B17403659
theorem B20844067 : Blo 279826 20844067 := bstep (se 1 (by rfl) ⟨15633050, by rfl⟩ : syracuseStep 20844067 = 31266101) B31266101
theorem B955529 : Blo 279826 955529 := bstep (se 2 (by rfl) ⟨358323, by rfl⟩ : syracuseStep 955529 = 716647) B716647
theorem B7415009 : Blo 279826 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B2140829 : Blo 279826 2140829 := bstep (se 3 (by rfl) ⟨401405, by rfl⟩ : syracuseStep 2140829 = 802811) B802811
theorem B635759 : Blo 279826 635759 := bstep (se 1 (by rfl) ⟨476819, by rfl⟩ : syracuseStep 635759 = 953639) B953639
theorem B5388221 : Blo 279826 5388221 := bstep (se 3 (by rfl) ⟨1010291, by rfl⟩ : syracuseStep 5388221 = 2020583) B2020583
theorem B3882167 : Blo 279826 3882167 := bstep (se 1 (by rfl) ⟨2911625, by rfl⟩ : syracuseStep 3882167 = 5823251) B5823251
theorem B2407751 : Blo 279826 2407751 := bstep (se 1 (by rfl) ⟨1805813, by rfl⟩ : syracuseStep 2407751 = 3611627) B3611627
theorem B65846789 : Blo 279826 65846789 := bstep (se 4 (by rfl) ⟨6173136, by rfl⟩ : syracuseStep 65846789 = 12346273) B12346273
theorem B4833269 : Blo 279826 4833269 := bstep (se 5 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 4833269 = 453119) B453119
theorem B3883247 : Blo 279826 3883247 := bstep (se 1 (by rfl) ⟨2912435, by rfl⟩ : syracuseStep 3883247 = 5824871) B5824871
theorem B125781751 : Blo 279826 125781751 := bstep (se 1 (by rfl) ⟨94336313, by rfl⟩ : syracuseStep 125781751 = 188672627) B188672627
theorem B3592511 : Blo 279826 3592511 := bstep (se 1 (by rfl) ⟨2694383, by rfl⟩ : syracuseStep 3592511 = 5388767) B5388767
theorem B4903247 : Blo 279826 4903247 := bstep (se 1 (by rfl) ⟨3677435, by rfl⟩ : syracuseStep 4903247 = 7354871) B7354871
theorem B283423 : Blo 279826 283423 := bstep (se 1 (by rfl) ⟨212567, by rfl⟩ : syracuseStep 283423 = 425135) B425135
theorem B646625 : Blo 279826 646625 := bstep (se 2 (by rfl) ⟨242484, by rfl⟩ : syracuseStep 646625 = 484969) B484969
theorem B9100927 : Blo 279826 9100927 := bstep (se 1 (by rfl) ⟨6825695, by rfl⟩ : syracuseStep 9100927 = 13651391) B13651391
theorem B1040543 : Blo 279826 1040543 := bstep (se 1 (by rfl) ⟨780407, by rfl⟩ : syracuseStep 1040543 = 1560815) B1560815
theorem B4846391 : Blo 279826 4846391 := bstep (se 1 (by rfl) ⟨3634793, by rfl⟩ : syracuseStep 4846391 = 7269587) B7269587
theorem B2422649 : Blo 279826 2422649 := bstep (se 2 (by rfl) ⟨908493, by rfl⟩ : syracuseStep 2422649 = 1816987) B1816987
theorem B6191387 : Blo 279826 6191387 := bstep (se 1 (by rfl) ⟨4643540, by rfl⟩ : syracuseStep 6191387 = 9287081) B9287081
theorem B13663079 : Blo 279826 13663079 := bstep (se 1 (by rfl) ⟨10247309, by rfl⟩ : syracuseStep 13663079 = 20494619) B20494619
theorem B9699263 : Blo 279826 9699263 := bstep (se 1 (by rfl) ⟨7274447, by rfl⟩ : syracuseStep 9699263 = 14548895) B14548895
theorem B2588831 : Blo 279826 2588831 := bstep (se 1 (by rfl) ⟨1941623, by rfl⟩ : syracuseStep 2588831 = 3883247) B3883247
theorem B7734959 : Blo 279826 7734959 := bstep (se 1 (by rfl) ⟨5801219, by rfl⟩ : syracuseStep 7734959 = 11602439) B11602439
theorem B167709001 : Blo 279826 167709001 := bstep (se 2 (by rfl) ⟨62890875, by rfl⟩ : syracuseStep 167709001 = 125781751) B125781751
theorem B2395007 : Blo 279826 2395007 := bstep (se 1 (by rfl) ⟨1796255, by rfl⟩ : syracuseStep 2395007 = 3592511) B3592511
theorem B27792089 : Blo 279826 27792089 := bstep (se 2 (by rfl) ⟨10422033, by rfl⟩ : syracuseStep 27792089 = 20844067) B20844067
theorem B431083 : Blo 279826 431083 := bstep (se 1 (by rfl) ⟨323312, by rfl⟩ : syracuseStep 431083 = 646625) B646625
theorem B693695 : Blo 279826 693695 := bstep (se 1 (by rfl) ⟨520271, by rfl⟩ : syracuseStep 693695 = 1040543) B1040543
theorem B1615099 : Blo 279826 1615099 := bstep (se 1 (by rfl) ⟨1211324, by rfl⟩ : syracuseStep 1615099 = 2422649) B2422649
theorem B12134569 : Blo 279826 12134569 := bstep (se 2 (by rfl) ⟨4550463, by rfl⟩ : syracuseStep 12134569 = 9100927) B9100927
theorem B6466175 : Blo 279826 6466175 := bstep (se 1 (by rfl) ⟨4849631, by rfl⟩ : syracuseStep 6466175 = 9699263) B9699263
theorem B3222179 : Blo 279826 3222179 := bstep (se 1 (by rfl) ⟨2416634, by rfl⟩ : syracuseStep 3222179 = 4833269) B4833269
theorem B637019 : Blo 279826 637019 := bstep (se 1 (by rfl) ⟨477764, by rfl⟩ : syracuseStep 637019 = 955529) B955529
theorem B1427219 : Blo 279826 1427219 := bstep (se 1 (by rfl) ⟨1070414, by rfl⟩ : syracuseStep 1427219 = 2140829) B2140829
theorem B3230927 : Blo 279826 3230927 := bstep (se 1 (by rfl) ⟨2423195, by rfl⟩ : syracuseStep 3230927 = 4846391) B4846391
theorem B3592147 : Blo 279826 3592147 := bstep (se 1 (by rfl) ⟨2694110, by rfl⟩ : syracuseStep 3592147 = 5388221) B5388221
theorem B43897859 : Blo 279826 43897859 := bstep (se 1 (by rfl) ⟨32923394, by rfl⟩ : syracuseStep 43897859 = 65846789) B65846789
theorem B3268831 : Blo 279826 3268831 := bstep (se 1 (by rfl) ⟨2451623, by rfl⟩ : syracuseStep 3268831 = 4903247) B4903247
theorem B4943339 : Blo 279826 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B423839 : Blo 279826 423839 := bstep (se 1 (by rfl) ⟨317879, by rfl⟩ : syracuseStep 423839 = 635759) B635759
theorem B4127591 : Blo 279826 4127591 := bstep (se 1 (by rfl) ⟨3095693, by rfl⟩ : syracuseStep 4127591 = 6191387) B6191387
theorem B9108719 : Blo 279826 9108719 := bstep (se 1 (by rfl) ⟨6831539, by rfl⟩ : syracuseStep 9108719 = 13663079) B13663079
theorem B2588111 : Blo 279826 2588111 := bstep (se 1 (by rfl) ⟨1941083, by rfl⟩ : syracuseStep 2588111 = 3882167) B3882167
theorem B1605167 : Blo 279826 1605167 := bstep (se 1 (by rfl) ⟨1203875, by rfl⟩ : syracuseStep 1605167 = 2407751) B2407751
theorem B4358441 : Blo 279826 4358441 := bstep (se 2 (by rfl) ⟨1634415, by rfl⟩ : syracuseStep 4358441 = 3268831) B3268831
theorem B951479 : Blo 279826 951479 := bstep (se 1 (by rfl) ⟨713609, by rfl⟩ : syracuseStep 951479 = 1427219) B1427219
theorem B223612001 : Blo 279826 223612001 := bstep (se 2 (by rfl) ⟨83854500, by rfl⟩ : syracuseStep 223612001 = 167709001) B167709001
theorem B29265239 : Blo 279826 29265239 := bstep (se 1 (by rfl) ⟨21948929, by rfl⟩ : syracuseStep 29265239 = 43897859) B43897859
theorem B4789529 : Blo 279826 4789529 := bstep (se 2 (by rfl) ⟨1796073, by rfl⟩ : syracuseStep 4789529 = 3592147) B3592147
theorem B6072479 : Blo 279826 6072479 := bstep (se 1 (by rfl) ⟨4554359, by rfl⟩ : syracuseStep 6072479 = 9108719) B9108719
theorem B5156639 : Blo 279826 5156639 := bstep (se 1 (by rfl) ⟨3867479, by rfl⟩ : syracuseStep 5156639 = 7734959) B7734959
theorem B18528059 : Blo 279826 18528059 := bstep (se 1 (by rfl) ⟨13896044, by rfl⟩ : syracuseStep 18528059 = 27792089) B27792089
theorem B1849853 : Blo 279826 1849853 := bstep (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) B693695
theorem B574777 : Blo 279826 574777 := bstep (se 2 (by rfl) ⟨215541, by rfl⟩ : syracuseStep 574777 = 431083) B431083
theorem B4310783 : Blo 279826 4310783 := bstep (se 1 (by rfl) ⟨3233087, by rfl⟩ : syracuseStep 4310783 = 6466175) B6466175
theorem B2148119 : Blo 279826 2148119 := bstep (se 1 (by rfl) ⟨1611089, by rfl⟩ : syracuseStep 2148119 = 3222179) B3222179
theorem B3295559 : Blo 279826 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B282559 : Blo 279826 282559 := bstep (se 1 (by rfl) ⟨211919, by rfl⟩ : syracuseStep 282559 = 423839) B423839
theorem B1725407 : Blo 279826 1725407 := bstep (se 1 (by rfl) ⟨1294055, by rfl⟩ : syracuseStep 1725407 = 2588111) B2588111
theorem B1070111 : Blo 279826 1070111 := bstep (se 1 (by rfl) ⟨802583, by rfl⟩ : syracuseStep 1070111 = 1605167) B1605167
theorem B1725887 : Blo 279826 1725887 := bstep (se 1 (by rfl) ⟨1294415, by rfl⟩ : syracuseStep 1725887 = 2588831) B2588831
theorem B2153465 : Blo 279826 2153465 := bstep (se 2 (by rfl) ⟨807549, by rfl⟩ : syracuseStep 2153465 = 1615099) B1615099
theorem B1596671 : Blo 279826 1596671 := bstep (se 1 (by rfl) ⟨1197503, by rfl⟩ : syracuseStep 1596671 = 2395007) B2395007
theorem B2153951 : Blo 279826 2153951 := bstep (se 1 (by rfl) ⟨1615463, by rfl⟩ : syracuseStep 2153951 = 3230927) B3230927
theorem B16179425 : Blo 279826 16179425 := bstep (se 2 (by rfl) ⟨6067284, by rfl⟩ : syracuseStep 16179425 = 12134569) B12134569
theorem B424679 : Blo 279826 424679 := bstep (se 1 (by rfl) ⟨318509, by rfl⟩ : syracuseStep 424679 = 637019) B637019
theorem B2751727 : Blo 279826 2751727 := bstep (se 1 (by rfl) ⟨2063795, by rfl⟩ : syracuseStep 2751727 = 4127591) B4127591
theorem B2197039 : Blo 279826 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B1150271 : Blo 279826 1150271 := bstep (se 1 (by rfl) ⟨862703, by rfl⟩ : syracuseStep 1150271 = 1725407) B1725407
theorem B10786283 : Blo 279826 10786283 := bstep (se 1 (by rfl) ⟨8089712, by rfl⟩ : syracuseStep 10786283 = 16179425) B16179425
theorem B634319 : Blo 279826 634319 := bstep (se 1 (by rfl) ⟨475739, by rfl⟩ : syracuseStep 634319 = 951479) B951479
theorem B766369 : Blo 279826 766369 := bstep (se 2 (by rfl) ⟨287388, by rfl⟩ : syracuseStep 766369 = 574777) B574777
theorem B149074667 : Blo 279826 149074667 := bstep (se 1 (by rfl) ⟨111806000, by rfl⟩ : syracuseStep 149074667 = 223612001) B223612001
theorem B19510159 : Blo 279826 19510159 := bstep (se 1 (by rfl) ⟨14632619, by rfl⟩ : syracuseStep 19510159 = 29265239) B29265239
theorem B3193019 : Blo 279826 3193019 := bstep (se 1 (by rfl) ⟨2394764, by rfl⟩ : syracuseStep 3193019 = 4789529) B4789529
theorem B4602365 : Blo 279826 4602365 := bstep (se 3 (by rfl) ⟨862943, by rfl⟩ : syracuseStep 4602365 = 1725887) B1725887
theorem B1064447 : Blo 279826 1064447 := bstep (se 1 (by rfl) ⟨798335, by rfl⟩ : syracuseStep 1064447 = 1596671) B1596671
theorem B4048319 : Blo 279826 4048319 := bstep (se 1 (by rfl) ⟨3036239, by rfl⟩ : syracuseStep 4048319 = 6072479) B6072479
theorem B1233235 : Blo 279826 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B283119 : Blo 279826 283119 := bstep (se 1 (by rfl) ⟨212339, by rfl⟩ : syracuseStep 283119 = 424679) B424679
theorem B2905627 : Blo 279826 2905627 := bstep (se 1 (by rfl) ⟨2179220, by rfl⟩ : syracuseStep 2905627 = 4358441) B4358441
theorem B2873855 : Blo 279826 2873855 := bstep (se 1 (by rfl) ⟨2155391, by rfl⟩ : syracuseStep 2873855 = 4310783) B4310783
theorem B1432079 : Blo 279826 1432079 := bstep (se 1 (by rfl) ⟨1074059, by rfl⟩ : syracuseStep 1432079 = 2148119) B2148119
theorem B713407 : Blo 279826 713407 := bstep (se 1 (by rfl) ⟨535055, by rfl⟩ : syracuseStep 713407 = 1070111) B1070111
theorem B1435643 : Blo 279826 1435643 := bstep (se 1 (by rfl) ⟨1076732, by rfl⟩ : syracuseStep 1435643 = 2153465) B2153465
theorem B49408157 : Blo 279826 49408157 := bstep (se 3 (by rfl) ⟨9264029, by rfl⟩ : syracuseStep 49408157 = 18528059) B18528059
theorem B1435967 : Blo 279826 1435967 := bstep (se 1 (by rfl) ⟨1076975, by rfl⟩ : syracuseStep 1435967 = 2153951) B2153951
theorem B3437759 : Blo 279826 3437759 := bstep (se 1 (by rfl) ⟨2578319, by rfl⟩ : syracuseStep 3437759 = 5156639) B5156639
theorem B3668969 : Blo 279826 3668969 := bstep (se 2 (by rfl) ⟨1375863, by rfl⟩ : syracuseStep 3668969 = 2751727) B2751727
theorem B951209 : Blo 279826 951209 := bstep (se 2 (by rfl) ⟨356703, by rfl⟩ : syracuseStep 951209 = 713407) B713407
theorem B954719 : Blo 279826 954719 := bstep (se 1 (by rfl) ⟨716039, by rfl⟩ : syracuseStep 954719 = 1432079) B1432079
theorem B1644313 : Blo 279826 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B1021825 : Blo 279826 1021825 := bstep (se 2 (by rfl) ⟨383184, by rfl⟩ : syracuseStep 1021825 = 766369) B766369
theorem B957095 : Blo 279826 957095 := bstep (se 1 (by rfl) ⟨717821, by rfl⟩ : syracuseStep 957095 = 1435643) B1435643
theorem B957311 : Blo 279826 957311 := bstep (se 1 (by rfl) ⟨717983, by rfl⟩ : syracuseStep 957311 = 1435967) B1435967
theorem B3874169 : Blo 279826 3874169 := bstep (se 2 (by rfl) ⟨1452813, by rfl⟩ : syracuseStep 3874169 = 2905627) B2905627
theorem B2698879 : Blo 279826 2698879 := bstep (se 1 (by rfl) ⟨2024159, by rfl⟩ : syracuseStep 2698879 = 4048319) B4048319
theorem B2929385 : Blo 279826 2929385 := bstep (se 2 (by rfl) ⟨1098519, by rfl⟩ : syracuseStep 2929385 = 2197039) B2197039
theorem B766847 : Blo 279826 766847 := bstep (se 1 (by rfl) ⟨575135, by rfl⟩ : syracuseStep 766847 = 1150271) B1150271
theorem B7190855 : Blo 279826 7190855 := bstep (se 1 (by rfl) ⟨5393141, by rfl⟩ : syracuseStep 7190855 = 10786283) B10786283
theorem B1915903 : Blo 279826 1915903 := bstep (se 1 (by rfl) ⟨1436927, by rfl⟩ : syracuseStep 1915903 = 2873855) B2873855
theorem B3068243 : Blo 279826 3068243 := bstep (se 1 (by rfl) ⟨2301182, by rfl⟩ : syracuseStep 3068243 = 4602365) B4602365
theorem B2445979 : Blo 279826 2445979 := bstep (se 1 (by rfl) ⟨1834484, by rfl⟩ : syracuseStep 2445979 = 3668969) B3668969
theorem B709631 : Blo 279826 709631 := bstep (se 1 (by rfl) ⟨532223, by rfl⟩ : syracuseStep 709631 = 1064447) B1064447
theorem B9167357 : Blo 279826 9167357 := bstep (se 3 (by rfl) ⟨1718879, by rfl⟩ : syracuseStep 9167357 = 3437759) B3437759
theorem B131755085 : Blo 279826 131755085 := bstep (se 3 (by rfl) ⟨24704078, by rfl⟩ : syracuseStep 131755085 = 49408157) B49408157
theorem B26013545 : Blo 279826 26013545 := bstep (se 2 (by rfl) ⟨9755079, by rfl⟩ : syracuseStep 26013545 = 19510159) B19510159
theorem B422879 : Blo 279826 422879 := bstep (se 1 (by rfl) ⟨317159, by rfl⟩ : syracuseStep 422879 = 634319) B634319
theorem B99383111 : Blo 279826 99383111 := bstep (se 1 (by rfl) ⟨74537333, by rfl⟩ : syracuseStep 99383111 = 149074667) B149074667
theorem B2128679 : Blo 279826 2128679 := bstep (se 1 (by rfl) ⟨1596509, by rfl⟩ : syracuseStep 2128679 = 3193019) B3193019
theorem B24446285 : Blo 279826 24446285 := bstep (se 3 (by rfl) ⟨4583678, by rfl⟩ : syracuseStep 24446285 = 9167357) B9167357
theorem B17342363 : Blo 279826 17342363 := bstep (se 1 (by rfl) ⟨13006772, by rfl⟩ : syracuseStep 17342363 = 26013545) B26013545
theorem B4793903 : Blo 279826 4793903 := bstep (se 1 (by rfl) ⟨3595427, by rfl⟩ : syracuseStep 4793903 = 7190855) B7190855
theorem B1419119 : Blo 279826 1419119 := bstep (se 1 (by rfl) ⟨1064339, by rfl⟩ : syracuseStep 1419119 = 2128679) B2128679
theorem B634139 : Blo 279826 634139 := bstep (se 1 (by rfl) ⟨475604, by rfl⟩ : syracuseStep 634139 = 951209) B951209
theorem B2045495 : Blo 279826 2045495 := bstep (se 1 (by rfl) ⟨1534121, by rfl⟩ : syracuseStep 2045495 = 3068243) B3068243
theorem B636479 : Blo 279826 636479 := bstep (se 1 (by rfl) ⟨477359, by rfl⟩ : syracuseStep 636479 = 954719) B954719
theorem B473087 : Blo 279826 473087 := bstep (se 1 (by rfl) ⟨354815, by rfl⟩ : syracuseStep 473087 = 709631) B709631
theorem B638063 : Blo 279826 638063 := bstep (se 1 (by rfl) ⟨478547, by rfl⟩ : syracuseStep 638063 = 957095) B957095
theorem B638207 : Blo 279826 638207 := bstep (se 1 (by rfl) ⟨478655, by rfl⟩ : syracuseStep 638207 = 957311) B957311
theorem B3261305 : Blo 279826 3261305 := bstep (se 2 (by rfl) ⟨1222989, by rfl⟩ : syracuseStep 3261305 = 2445979) B2445979
theorem B87836723 : Blo 279826 87836723 := bstep (se 1 (by rfl) ⟨65877542, by rfl⟩ : syracuseStep 87836723 = 131755085) B131755085
theorem B1362433 : Blo 279826 1362433 := bstep (se 2 (by rfl) ⟨510912, by rfl⟩ : syracuseStep 1362433 = 1021825) B1021825
theorem B1952923 : Blo 279826 1952923 := bstep (se 1 (by rfl) ⟨1464692, by rfl⟩ : syracuseStep 1952923 = 2929385) B2929385
theorem B511231 : Blo 279826 511231 := bstep (se 1 (by rfl) ⟨383423, by rfl⟩ : syracuseStep 511231 = 766847) B766847
theorem B281919 : Blo 279826 281919 := bstep (se 1 (by rfl) ⟨211439, by rfl⟩ : syracuseStep 281919 = 422879) B422879
theorem B3598505 : Blo 279826 3598505 := bstep (se 2 (by rfl) ⟨1349439, by rfl⟩ : syracuseStep 3598505 = 2698879) B2698879
theorem B2582779 : Blo 279826 2582779 := bstep (se 1 (by rfl) ⟨1937084, by rfl⟩ : syracuseStep 2582779 = 3874169) B3874169
theorem B2192417 : Blo 279826 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B66255407 : Blo 279826 66255407 := bstep (se 1 (by rfl) ⟨49691555, by rfl⟩ : syracuseStep 66255407 = 99383111) B99383111
theorem B2554537 : Blo 279826 2554537 := bstep (se 2 (by rfl) ⟨957951, by rfl⟩ : syracuseStep 2554537 = 1915903) B1915903
theorem B58557815 : Blo 279826 58557815 := bstep (se 1 (by rfl) ⟨43918361, by rfl⟩ : syracuseStep 58557815 = 87836723) B87836723
theorem B3443705 : Blo 279826 3443705 := bstep (se 2 (by rfl) ⟨1291389, by rfl⟩ : syracuseStep 3443705 = 2582779) B2582779
theorem B2399003 : Blo 279826 2399003 := bstep (se 1 (by rfl) ⟨1799252, by rfl⟩ : syracuseStep 2399003 = 3598505) B3598505
theorem B2174203 : Blo 279826 2174203 := bstep (se 1 (by rfl) ⟨1630652, by rfl⟩ : syracuseStep 2174203 = 3261305) B3261305
theorem B16297523 : Blo 279826 16297523 := bstep (se 1 (by rfl) ⟨12223142, by rfl⟩ : syracuseStep 16297523 = 24446285) B24446285
theorem B1816577 : Blo 279826 1816577 := bstep (se 2 (by rfl) ⟨681216, by rfl⟩ : syracuseStep 1816577 = 1362433) B1362433
theorem B2603897 : Blo 279826 2603897 := bstep (se 2 (by rfl) ⟨976461, by rfl⟩ : syracuseStep 2603897 = 1952923) B1952923
theorem B3195935 : Blo 279826 3195935 := bstep (se 1 (by rfl) ⟨2396951, by rfl⟩ : syracuseStep 3195935 = 4793903) B4793903
theorem B1461611 : Blo 279826 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B1363663 : Blo 279826 1363663 := bstep (se 1 (by rfl) ⟨1022747, by rfl⟩ : syracuseStep 1363663 = 2045495) B2045495
theorem B315391 : Blo 279826 315391 := bstep (se 1 (by rfl) ⟨236543, by rfl⟩ : syracuseStep 315391 = 473087) B473087
theorem B681641 : Blo 279826 681641 := bstep (se 2 (by rfl) ⟨255615, by rfl⟩ : syracuseStep 681641 = 511231) B511231
theorem B11561575 : Blo 279826 11561575 := bstep (se 1 (by rfl) ⟨8671181, by rfl⟩ : syracuseStep 11561575 = 17342363) B17342363
theorem B946079 : Blo 279826 946079 := bstep (se 1 (by rfl) ⟨709559, by rfl⟩ : syracuseStep 946079 = 1419119) B1419119
theorem B422759 : Blo 279826 422759 := bstep (se 1 (by rfl) ⟨317069, by rfl⟩ : syracuseStep 422759 = 634139) B634139
theorem B3406049 : Blo 279826 3406049 := bstep (se 2 (by rfl) ⟨1277268, by rfl⟩ : syracuseStep 3406049 = 2554537) B2554537
theorem B424319 : Blo 279826 424319 := bstep (se 1 (by rfl) ⟨318239, by rfl⟩ : syracuseStep 424319 = 636479) B636479
theorem B44170271 : Blo 279826 44170271 := bstep (se 1 (by rfl) ⟨33127703, by rfl⟩ : syracuseStep 44170271 = 66255407) B66255407
theorem B425375 : Blo 279826 425375 := bstep (se 1 (by rfl) ⟨319031, by rfl⟩ : syracuseStep 425375 = 638063) B638063
theorem B425471 : Blo 279826 425471 := bstep (se 1 (by rfl) ⟨319103, by rfl⟩ : syracuseStep 425471 = 638207) B638207
theorem B2130623 : Blo 279826 2130623 := bstep (se 1 (by rfl) ⟨1597967, by rfl⟩ : syracuseStep 2130623 = 3195935) B3195935
theorem B2295803 : Blo 279826 2295803 := bstep (se 1 (by rfl) ⟨1721852, by rfl⟩ : syracuseStep 2295803 = 3443705) B3443705
theorem B630719 : Blo 279826 630719 := bstep (se 1 (by rfl) ⟨473039, by rfl⟩ : syracuseStep 630719 = 946079) B946079
theorem B2270699 : Blo 279826 2270699 := bstep (se 1 (by rfl) ⟨1703024, by rfl⟩ : syracuseStep 2270699 = 3406049) B3406049
theorem B39038543 : Blo 279826 39038543 := bstep (se 1 (by rfl) ⟨29278907, by rfl⟩ : syracuseStep 39038543 = 58557815) B58557815
theorem B15415433 : Blo 279826 15415433 := bstep (se 2 (by rfl) ⟨5780787, by rfl⟩ : syracuseStep 15415433 = 11561575) B11561575
theorem B2898937 : Blo 279826 2898937 := bstep (se 2 (by rfl) ⟨1087101, by rfl⟩ : syracuseStep 2898937 = 2174203) B2174203
theorem B1818217 : Blo 279826 1818217 := bstep (se 2 (by rfl) ⟨681831, by rfl⟩ : syracuseStep 1818217 = 1363663) B1363663
theorem B10865015 : Blo 279826 10865015 := bstep (se 1 (by rfl) ⟨8148761, by rfl⟩ : syracuseStep 10865015 = 16297523) B16297523
theorem B281839 : Blo 279826 281839 := bstep (se 1 (by rfl) ⟨211379, by rfl⟩ : syracuseStep 281839 = 422759) B422759
theorem B282879 : Blo 279826 282879 := bstep (se 1 (by rfl) ⟨212159, by rfl⟩ : syracuseStep 282879 = 424319) B424319
theorem B29446847 : Blo 279826 29446847 := bstep (se 1 (by rfl) ⟨22085135, by rfl⟩ : syracuseStep 29446847 = 44170271) B44170271
theorem B283583 : Blo 279826 283583 := bstep (se 1 (by rfl) ⟨212687, by rfl⟩ : syracuseStep 283583 = 425375) B425375
theorem B283647 : Blo 279826 283647 := bstep (se 1 (by rfl) ⟨212735, by rfl⟩ : syracuseStep 283647 = 425471) B425471
theorem B1599335 : Blo 279826 1599335 := bstep (se 1 (by rfl) ⟨1199501, by rfl⟩ : syracuseStep 1599335 = 2399003) B2399003
theorem B420521 : Blo 279826 420521 := bstep (se 2 (by rfl) ⟨157695, by rfl⟩ : syracuseStep 420521 = 315391) B315391
theorem B454427 : Blo 279826 454427 := bstep (se 1 (by rfl) ⟨340820, by rfl⟩ : syracuseStep 454427 = 681641) B681641
theorem B3897629 : Blo 279826 3897629 := bstep (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) B1461611
theorem B1211051 : Blo 279826 1211051 := bstep (se 1 (by rfl) ⟨908288, by rfl⟩ : syracuseStep 1211051 = 1816577) B1816577
theorem B1735931 : Blo 279826 1735931 := bstep (se 1 (by rfl) ⟨1301948, by rfl⟩ : syracuseStep 1735931 = 2603897) B2603897
theorem B7243343 : Blo 279826 7243343 := bstep (se 1 (by rfl) ⟨5432507, by rfl⟩ : syracuseStep 7243343 = 10865015) B10865015
theorem B19631231 : Blo 279826 19631231 := bstep (se 1 (by rfl) ⟨14723423, by rfl⟩ : syracuseStep 19631231 = 29446847) B29446847
theorem B1513799 : Blo 279826 1513799 := bstep (se 1 (by rfl) ⟨1135349, by rfl⟩ : syracuseStep 1513799 = 2270699) B2270699
theorem B26025695 : Blo 279826 26025695 := bstep (se 1 (by rfl) ⟨19519271, by rfl⟩ : syracuseStep 26025695 = 39038543) B39038543
theorem B302951 : Blo 279826 302951 := bstep (se 1 (by rfl) ⟨227213, by rfl⟩ : syracuseStep 302951 = 454427) B454427
theorem B4629149 : Blo 279826 4629149 := bstep (se 3 (by rfl) ⟨867965, by rfl⟩ : syracuseStep 4629149 = 1735931) B1735931
theorem B2598419 : Blo 279826 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B1420415 : Blo 279826 1420415 := bstep (se 1 (by rfl) ⟨1065311, by rfl⟩ : syracuseStep 1420415 = 2130623) B2130623
theorem B1066223 : Blo 279826 1066223 := bstep (se 1 (by rfl) ⟨799667, by rfl⟩ : syracuseStep 1066223 = 1599335) B1599335
theorem B280347 : Blo 279826 280347 := bstep (se 1 (by rfl) ⟨210260, by rfl⟩ : syracuseStep 280347 = 420521) B420521
theorem B3229469 : Blo 279826 3229469 := bstep (se 3 (by rfl) ⟨605525, by rfl⟩ : syracuseStep 3229469 = 1211051) B1211051
theorem B10276955 : Blo 279826 10276955 := bstep (se 1 (by rfl) ⟨7707716, by rfl⟩ : syracuseStep 10276955 = 15415433) B15415433
theorem B1530535 : Blo 279826 1530535 := bstep (se 1 (by rfl) ⟨1147901, by rfl⟩ : syracuseStep 1530535 = 2295803) B2295803
theorem B420479 : Blo 279826 420479 := bstep (se 1 (by rfl) ⟨315359, by rfl⟩ : syracuseStep 420479 = 630719) B630719
theorem B3865249 : Blo 279826 3865249 := bstep (se 2 (by rfl) ⟨1449468, by rfl⟩ : syracuseStep 3865249 = 2898937) B2898937
theorem B2424289 : Blo 279826 2424289 := bstep (se 2 (by rfl) ⟨909108, by rfl⟩ : syracuseStep 2424289 = 1818217) B1818217
theorem B6851303 : Blo 279826 6851303 := bstep (se 1 (by rfl) ⟨5138477, by rfl⟩ : syracuseStep 6851303 = 10276955) B10276955
theorem B3086099 : Blo 279826 3086099 := bstep (se 1 (by rfl) ⟨2314574, by rfl⟩ : syracuseStep 3086099 = 4629149) B4629149
theorem B5153665 : Blo 279826 5153665 := bstep (se 2 (by rfl) ⟨1932624, by rfl⟩ : syracuseStep 5153665 = 3865249) B3865249
theorem B2040713 : Blo 279826 2040713 := bstep (se 2 (by rfl) ⟨765267, by rfl⟩ : syracuseStep 2040713 = 1530535) B1530535
theorem B4828895 : Blo 279826 4828895 := bstep (se 1 (by rfl) ⟨3621671, by rfl⟩ : syracuseStep 4828895 = 7243343) B7243343
theorem B13087487 : Blo 279826 13087487 := bstep (se 1 (by rfl) ⟨9815615, by rfl⟩ : syracuseStep 13087487 = 19631231) B19631231
theorem B17350463 : Blo 279826 17350463 := bstep (se 1 (by rfl) ⟨13012847, by rfl⟩ : syracuseStep 17350463 = 26025695) B26025695
theorem B280319 : Blo 279826 280319 := bstep (se 1 (by rfl) ⟨210239, by rfl⟩ : syracuseStep 280319 = 420479) B420479
theorem B3232385 : Blo 279826 3232385 := bstep (se 2 (by rfl) ⟨1212144, by rfl⟩ : syracuseStep 3232385 = 2424289) B2424289
theorem B807869 : Blo 279826 807869 := bstep (se 3 (by rfl) ⟨151475, by rfl⟩ : syracuseStep 807869 = 302951) B302951
theorem B710815 : Blo 279826 710815 := bstep (se 1 (by rfl) ⟨533111, by rfl⟩ : syracuseStep 710815 = 1066223) B1066223
theorem B2152979 : Blo 279826 2152979 := bstep (se 1 (by rfl) ⟨1614734, by rfl⟩ : syracuseStep 2152979 = 3229469) B3229469
theorem B1009199 : Blo 279826 1009199 := bstep (se 1 (by rfl) ⟨756899, by rfl⟩ : syracuseStep 1009199 = 1513799) B1513799
theorem B1732279 : Blo 279826 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B946943 : Blo 279826 946943 := bstep (se 1 (by rfl) ⟨710207, by rfl⟩ : syracuseStep 946943 = 1420415) B1420415
theorem B3219263 : Blo 279826 3219263 := bstep (se 1 (by rfl) ⟨2414447, by rfl⟩ : syracuseStep 3219263 = 4828895) B4828895
theorem B631295 : Blo 279826 631295 := bstep (se 1 (by rfl) ⟨473471, by rfl⟩ : syracuseStep 631295 = 946943) B946943
theorem B8724991 : Blo 279826 8724991 := bstep (se 1 (by rfl) ⟨6543743, by rfl⟩ : syracuseStep 8724991 = 13087487) B13087487
theorem B4567535 : Blo 279826 4567535 := bstep (se 1 (by rfl) ⟨3425651, by rfl⟩ : syracuseStep 4567535 = 6851303) B6851303
theorem B538579 : Blo 279826 538579 := bstep (se 1 (by rfl) ⟨403934, by rfl⟩ : syracuseStep 538579 = 807869) B807869
theorem B2309705 : Blo 279826 2309705 := bstep (se 2 (by rfl) ⟨866139, by rfl⟩ : syracuseStep 2309705 = 1732279) B1732279
theorem B1360475 : Blo 279826 1360475 := bstep (se 1 (by rfl) ⟨1020356, by rfl⟩ : syracuseStep 1360475 = 2040713) B2040713
theorem B672799 : Blo 279826 672799 := bstep (se 1 (by rfl) ⟨504599, by rfl⟩ : syracuseStep 672799 = 1009199) B1009199
theorem B6871553 : Blo 279826 6871553 := bstep (se 2 (by rfl) ⟨2576832, by rfl⟩ : syracuseStep 6871553 = 5153665) B5153665
theorem B2154923 : Blo 279826 2154923 := bstep (se 1 (by rfl) ⟨1616192, by rfl⟩ : syracuseStep 2154923 = 3232385) B3232385
theorem B2057399 : Blo 279826 2057399 := bstep (se 1 (by rfl) ⟨1543049, by rfl⟩ : syracuseStep 2057399 = 3086099) B3086099
theorem B1435319 : Blo 279826 1435319 := bstep (se 1 (by rfl) ⟨1076489, by rfl⟩ : syracuseStep 1435319 = 2152979) B2152979
theorem B947753 : Blo 279826 947753 := bstep (se 2 (by rfl) ⟨355407, by rfl⟩ : syracuseStep 947753 = 710815) B710815
theorem B11566975 : Blo 279826 11566975 := bstep (se 1 (by rfl) ⟨8675231, by rfl⟩ : syracuseStep 11566975 = 17350463) B17350463
theorem B11633321 : Blo 279826 11633321 := bstep (se 2 (by rfl) ⟨4362495, by rfl⟩ : syracuseStep 11633321 = 8724991) B8724991
theorem B956879 : Blo 279826 956879 := bstep (se 1 (by rfl) ⟨717659, by rfl⟩ : syracuseStep 956879 = 1435319) B1435319
theorem B631835 : Blo 279826 631835 := bstep (se 1 (by rfl) ⟨473876, by rfl⟩ : syracuseStep 631835 = 947753) B947753
theorem B897065 : Blo 279826 897065 := bstep (se 2 (by rfl) ⟨336399, by rfl⟩ : syracuseStep 897065 = 672799) B672799
theorem B2146175 : Blo 279826 2146175 := bstep (se 1 (by rfl) ⟨1609631, by rfl⟩ : syracuseStep 2146175 = 3219263) B3219263
theorem B15422633 : Blo 279826 15422633 := bstep (se 2 (by rfl) ⟨5783487, by rfl⟩ : syracuseStep 15422633 = 11566975) B11566975
theorem B906983 : Blo 279826 906983 := bstep (se 1 (by rfl) ⟨680237, by rfl⟩ : syracuseStep 906983 = 1360475) B1360475
theorem B4581035 : Blo 279826 4581035 := bstep (se 1 (by rfl) ⟨3435776, by rfl⟩ : syracuseStep 4581035 = 6871553) B6871553
theorem B1436615 : Blo 279826 1436615 := bstep (se 1 (by rfl) ⟨1077461, by rfl⟩ : syracuseStep 1436615 = 2154923) B2154923
theorem B420863 : Blo 279826 420863 := bstep (se 1 (by rfl) ⟨315647, by rfl⟩ : syracuseStep 420863 = 631295) B631295
theorem B1371599 : Blo 279826 1371599 := bstep (se 1 (by rfl) ⟨1028699, by rfl⟩ : syracuseStep 1371599 = 2057399) B2057399
theorem B718105 : Blo 279826 718105 := bstep (se 2 (by rfl) ⟨269289, by rfl⟩ : syracuseStep 718105 = 538579) B538579
theorem B3045023 : Blo 279826 3045023 := bstep (se 1 (by rfl) ⟨2283767, by rfl⟩ : syracuseStep 3045023 = 4567535) B4567535
theorem B1539803 : Blo 279826 1539803 := bstep (se 1 (by rfl) ⟨1154852, by rfl⟩ : syracuseStep 1539803 = 2309705) B2309705
theorem B3054023 : Blo 279826 3054023 := bstep (se 1 (by rfl) ⟨2290517, by rfl⟩ : syracuseStep 3054023 = 4581035) B4581035
theorem B957473 : Blo 279826 957473 := bstep (se 2 (by rfl) ⟨359052, by rfl⟩ : syracuseStep 957473 = 718105) B718105
theorem B957743 : Blo 279826 957743 := bstep (se 1 (by rfl) ⟨718307, by rfl⟩ : syracuseStep 957743 = 1436615) B1436615
theorem B598043 : Blo 279826 598043 := bstep (se 1 (by rfl) ⟨448532, by rfl⟩ : syracuseStep 598043 = 897065) B897065
theorem B1026535 : Blo 279826 1026535 := bstep (se 1 (by rfl) ⟨769901, by rfl⟩ : syracuseStep 1026535 = 1539803) B1539803
theorem B604655 : Blo 279826 604655 := bstep (se 1 (by rfl) ⟨453491, by rfl⟩ : syracuseStep 604655 = 906983) B906983
theorem B637919 : Blo 279826 637919 := bstep (se 1 (by rfl) ⟨478439, by rfl⟩ : syracuseStep 637919 = 956879) B956879
theorem B280575 : Blo 279826 280575 := bstep (se 1 (by rfl) ⟨210431, by rfl⟩ : syracuseStep 280575 = 420863) B420863
theorem B1430783 : Blo 279826 1430783 := bstep (se 1 (by rfl) ⟨1073087, by rfl⟩ : syracuseStep 1430783 = 2146175) B2146175
theorem B7755547 : Blo 279826 7755547 := bstep (se 1 (by rfl) ⟨5816660, by rfl⟩ : syracuseStep 7755547 = 11633321) B11633321
theorem B10281755 : Blo 279826 10281755 := bstep (se 1 (by rfl) ⟨7711316, by rfl⟩ : syracuseStep 10281755 = 15422633) B15422633
theorem B421223 : Blo 279826 421223 := bstep (se 1 (by rfl) ⟨315917, by rfl⟩ : syracuseStep 421223 = 631835) B631835
theorem B914399 : Blo 279826 914399 := bstep (se 1 (by rfl) ⟨685799, by rfl⟩ : syracuseStep 914399 = 1371599) B1371599
theorem B2030015 : Blo 279826 2030015 := bstep (se 1 (by rfl) ⟨1522511, by rfl⟩ : syracuseStep 2030015 = 3045023) B3045023
theorem B953855 : Blo 279826 953855 := bstep (se 1 (by rfl) ⟨715391, by rfl⟩ : syracuseStep 953855 = 1430783) B1430783
theorem B2036015 : Blo 279826 2036015 := bstep (se 1 (by rfl) ⟨1527011, by rfl⟩ : syracuseStep 2036015 = 3054023) B3054023
theorem B398695 : Blo 279826 398695 := bstep (se 1 (by rfl) ⟨299021, by rfl⟩ : syracuseStep 398695 = 598043) B598043
theorem B6854503 : Blo 279826 6854503 := bstep (se 1 (by rfl) ⟨5140877, by rfl⟩ : syracuseStep 6854503 = 10281755) B10281755
theorem B1353343 : Blo 279826 1353343 := bstep (se 1 (by rfl) ⟨1015007, by rfl⟩ : syracuseStep 1353343 = 2030015) B2030015
theorem B403103 : Blo 279826 403103 := bstep (se 1 (by rfl) ⟨302327, by rfl⟩ : syracuseStep 403103 = 604655) B604655
theorem B638315 : Blo 279826 638315 := bstep (se 1 (by rfl) ⟨478736, by rfl⟩ : syracuseStep 638315 = 957473) B957473
theorem B638495 : Blo 279826 638495 := bstep (se 1 (by rfl) ⟨478871, by rfl⟩ : syracuseStep 638495 = 957743) B957743
theorem B280815 : Blo 279826 280815 := bstep (se 1 (by rfl) ⟨210611, by rfl⟩ : syracuseStep 280815 = 421223) B421223
theorem B10340729 : Blo 279826 10340729 := bstep (se 2 (by rfl) ⟨3877773, by rfl⟩ : syracuseStep 10340729 = 7755547) B7755547
theorem B609599 : Blo 279826 609599 := bstep (se 1 (by rfl) ⟨457199, by rfl⟩ : syracuseStep 609599 = 914399) B914399
theorem B1368713 : Blo 279826 1368713 := bstep (se 2 (by rfl) ⟨513267, by rfl⟩ : syracuseStep 1368713 = 1026535) B1026535
theorem B425279 : Blo 279826 425279 := bstep (se 1 (by rfl) ⟨318959, by rfl⟩ : syracuseStep 425279 = 637919) B637919
theorem B1804457 : Blo 279826 1804457 := bstep (se 2 (by rfl) ⟨676671, by rfl⟩ : syracuseStep 1804457 = 1353343) B1353343
theorem B531593 : Blo 279826 531593 := bstep (se 2 (by rfl) ⟨199347, by rfl⟩ : syracuseStep 531593 = 398695) B398695
theorem B6893819 : Blo 279826 6893819 := bstep (se 1 (by rfl) ⟨5170364, by rfl⟩ : syracuseStep 6893819 = 10340729) B10340729
theorem B406399 : Blo 279826 406399 := bstep (se 1 (by rfl) ⟨304799, by rfl⟩ : syracuseStep 406399 = 609599) B609599
theorem B635903 : Blo 279826 635903 := bstep (se 1 (by rfl) ⟨476927, by rfl⟩ : syracuseStep 635903 = 953855) B953855
theorem B1357343 : Blo 279826 1357343 := bstep (se 1 (by rfl) ⟨1018007, by rfl⟩ : syracuseStep 1357343 = 2036015) B2036015
theorem B283519 : Blo 279826 283519 := bstep (se 1 (by rfl) ⟨212639, by rfl⟩ : syracuseStep 283519 = 425279) B425279
theorem B1074941 : Blo 279826 1074941 := bstep (se 3 (by rfl) ⟨201551, by rfl⟩ : syracuseStep 1074941 = 403103) B403103
theorem B912475 : Blo 279826 912475 := bstep (se 1 (by rfl) ⟨684356, by rfl⟩ : syracuseStep 912475 = 1368713) B1368713
theorem B9139337 : Blo 279826 9139337 := bstep (se 2 (by rfl) ⟨3427251, by rfl⟩ : syracuseStep 9139337 = 6854503) B6854503
theorem B425543 : Blo 279826 425543 := bstep (se 1 (by rfl) ⟨319157, by rfl⟩ : syracuseStep 425543 = 638315) B638315
theorem B425663 : Blo 279826 425663 := bstep (se 1 (by rfl) ⟨319247, by rfl⟩ : syracuseStep 425663 = 638495) B638495
theorem B1216633 : Blo 279826 1216633 := bstep (se 2 (by rfl) ⟨456237, by rfl⟩ : syracuseStep 1216633 = 912475) B912475
theorem B4595879 : Blo 279826 4595879 := bstep (se 1 (by rfl) ⟨3446909, by rfl⟩ : syracuseStep 4595879 = 6893819) B6893819
theorem B541865 : Blo 279826 541865 := bstep (se 2 (by rfl) ⟨203199, by rfl⟩ : syracuseStep 541865 = 406399) B406399
theorem B904895 : Blo 279826 904895 := bstep (se 1 (by rfl) ⟨678671, by rfl⟩ : syracuseStep 904895 = 1357343) B1357343
theorem B283695 : Blo 279826 283695 := bstep (se 1 (by rfl) ⟨212771, by rfl⟩ : syracuseStep 283695 = 425543) B425543
theorem B283775 : Blo 279826 283775 := bstep (se 1 (by rfl) ⟨212831, by rfl⟩ : syracuseStep 283775 = 425663) B425663
theorem B1202971 : Blo 279826 1202971 := bstep (se 1 (by rfl) ⟨902228, by rfl⟩ : syracuseStep 1202971 = 1804457) B1804457
theorem B354395 : Blo 279826 354395 := bstep (se 1 (by rfl) ⟨265796, by rfl⟩ : syracuseStep 354395 = 531593) B531593
theorem B716627 : Blo 279826 716627 := bstep (se 1 (by rfl) ⟨537470, by rfl⟩ : syracuseStep 716627 = 1074941) B1074941
theorem B423935 : Blo 279826 423935 := bstep (se 1 (by rfl) ⟨317951, by rfl⟩ : syracuseStep 423935 = 635903) B635903
theorem B6092891 : Blo 279826 6092891 := bstep (se 1 (by rfl) ⟨4569668, by rfl⟩ : syracuseStep 6092891 = 9139337) B9139337
theorem B361243 : Blo 279826 361243 := bstep (se 1 (by rfl) ⟨270932, by rfl⟩ : syracuseStep 361243 = 541865) B541865
theorem B603263 : Blo 279826 603263 := bstep (se 1 (by rfl) ⟨452447, by rfl⟩ : syracuseStep 603263 = 904895) B904895
theorem B3063919 : Blo 279826 3063919 := bstep (se 1 (by rfl) ⟨2297939, by rfl⟩ : syracuseStep 3063919 = 4595879) B4595879
theorem B1622177 : Blo 279826 1622177 := bstep (se 2 (by rfl) ⟨608316, by rfl⟩ : syracuseStep 1622177 = 1216633) B1216633
theorem B477751 : Blo 279826 477751 := bstep (se 1 (by rfl) ⟨358313, by rfl⟩ : syracuseStep 477751 = 716627) B716627
theorem B282623 : Blo 279826 282623 := bstep (se 1 (by rfl) ⟨211967, by rfl⟩ : syracuseStep 282623 = 423935) B423935
theorem B945053 : Blo 279826 945053 := bstep (se 3 (by rfl) ⟨177197, by rfl⟩ : syracuseStep 945053 = 354395) B354395
theorem B1603961 : Blo 279826 1603961 := bstep (se 2 (by rfl) ⟨601485, by rfl⟩ : syracuseStep 1603961 = 1202971) B1202971
theorem B4061927 : Blo 279826 4061927 := bstep (se 1 (by rfl) ⟨3046445, by rfl⟩ : syracuseStep 4061927 = 6092891) B6092891
theorem B1081451 : Blo 279826 1081451 := bstep (se 1 (by rfl) ⟨811088, by rfl⟩ : syracuseStep 1081451 = 1622177) B1622177
theorem B630035 : Blo 279826 630035 := bstep (se 1 (by rfl) ⟨472526, by rfl⟩ : syracuseStep 630035 = 945053) B945053
theorem B402175 : Blo 279826 402175 := bstep (se 1 (by rfl) ⟨301631, by rfl⟩ : syracuseStep 402175 = 603263) B603263
theorem B637001 : Blo 279826 637001 := bstep (se 2 (by rfl) ⟨238875, by rfl⟩ : syracuseStep 637001 = 477751) B477751
theorem B1069307 : Blo 279826 1069307 := bstep (se 1 (by rfl) ⟨801980, by rfl⟩ : syracuseStep 1069307 = 1603961) B1603961
theorem B2707951 : Blo 279826 2707951 := bstep (se 1 (by rfl) ⟨2030963, by rfl⟩ : syracuseStep 2707951 = 4061927) B4061927
theorem B4085225 : Blo 279826 4085225 := bstep (se 2 (by rfl) ⟨1531959, by rfl⟩ : syracuseStep 4085225 = 3063919) B3063919
theorem B1926629 : Blo 279826 1926629 := bstep (se 4 (by rfl) ⟨180621, by rfl⟩ : syracuseStep 1926629 = 361243) B361243
theorem B2883869 : Blo 279826 2883869 := bstep (se 3 (by rfl) ⟨540725, by rfl⟩ : syracuseStep 2883869 = 1081451) B1081451
theorem B2723483 : Blo 279826 2723483 := bstep (se 1 (by rfl) ⟨2042612, by rfl⟩ : syracuseStep 2723483 = 4085225) B4085225
theorem B3610601 : Blo 279826 3610601 := bstep (se 2 (by rfl) ⟨1353975, by rfl⟩ : syracuseStep 3610601 = 2707951) B2707951
theorem B1284419 : Blo 279826 1284419 := bstep (se 1 (by rfl) ⟨963314, by rfl⟩ : syracuseStep 1284419 = 1926629) B1926629
theorem B536233 : Blo 279826 536233 := bstep (se 2 (by rfl) ⟨201087, by rfl⟩ : syracuseStep 536233 = 402175) B402175
theorem B712871 : Blo 279826 712871 := bstep (se 1 (by rfl) ⟨534653, by rfl⟩ : syracuseStep 712871 = 1069307) B1069307
theorem B420023 : Blo 279826 420023 := bstep (se 1 (by rfl) ⟨315017, by rfl⟩ : syracuseStep 420023 = 630035) B630035
theorem B424667 : Blo 279826 424667 := bstep (se 1 (by rfl) ⟨318500, by rfl⟩ : syracuseStep 424667 = 637001) B637001
theorem B856279 : Blo 279826 856279 := bstep (se 1 (by rfl) ⟨642209, by rfl⟩ : syracuseStep 856279 = 1284419) B1284419
theorem B1815655 : Blo 279826 1815655 := bstep (se 1 (by rfl) ⟨1361741, by rfl⟩ : syracuseStep 1815655 = 2723483) B2723483
theorem B2407067 : Blo 279826 2407067 := bstep (se 1 (by rfl) ⟨1805300, by rfl⟩ : syracuseStep 2407067 = 3610601) B3610601
theorem B475247 : Blo 279826 475247 := bstep (se 1 (by rfl) ⟨356435, by rfl⟩ : syracuseStep 475247 = 712871) B712871
theorem B280015 : Blo 279826 280015 := bstep (se 1 (by rfl) ⟨210011, by rfl⟩ : syracuseStep 280015 = 420023) B420023
theorem B283111 : Blo 279826 283111 := bstep (se 1 (by rfl) ⟨212333, by rfl⟩ : syracuseStep 283111 = 424667) B424667
theorem B1922579 : Blo 279826 1922579 := bstep (se 1 (by rfl) ⟨1441934, by rfl⟩ : syracuseStep 1922579 = 2883869) B2883869
theorem B714977 : Blo 279826 714977 := bstep (se 2 (by rfl) ⟨268116, by rfl⟩ : syracuseStep 714977 = 536233) B536233
theorem B1281719 : Blo 279826 1281719 := bstep (se 1 (by rfl) ⟨961289, by rfl⟩ : syracuseStep 1281719 = 1922579) B1922579
theorem B476651 : Blo 279826 476651 := bstep (se 1 (by rfl) ⟨357488, by rfl⟩ : syracuseStep 476651 = 714977) B714977
theorem B316831 : Blo 279826 316831 := bstep (se 1 (by rfl) ⟨237623, by rfl⟩ : syracuseStep 316831 = 475247) B475247
theorem B1141705 : Blo 279826 1141705 := bstep (se 2 (by rfl) ⟨428139, by rfl⟩ : syracuseStep 1141705 = 856279) B856279
theorem B2420873 : Blo 279826 2420873 := bstep (se 2 (by rfl) ⟨907827, by rfl⟩ : syracuseStep 2420873 = 1815655) B1815655
theorem B1604711 : Blo 279826 1604711 := bstep (se 1 (by rfl) ⟨1203533, by rfl⟩ : syracuseStep 1604711 = 2407067) B2407067
theorem B854479 : Blo 279826 854479 := bstep (se 1 (by rfl) ⟨640859, by rfl⟩ : syracuseStep 854479 = 1281719) B1281719
theorem B1613915 : Blo 279826 1613915 := bstep (se 1 (by rfl) ⟨1210436, by rfl⟩ : syracuseStep 1613915 = 2420873) B2420873
theorem B1522273 : Blo 279826 1522273 := bstep (se 2 (by rfl) ⟨570852, by rfl⟩ : syracuseStep 1522273 = 1141705) B1141705
theorem B1069807 : Blo 279826 1069807 := bstep (se 1 (by rfl) ⟨802355, by rfl⟩ : syracuseStep 1069807 = 1604711) B1604711
theorem B317767 : Blo 279826 317767 := bstep (se 1 (by rfl) ⟨238325, by rfl⟩ : syracuseStep 317767 = 476651) B476651
theorem B422441 : Blo 279826 422441 := bstep (se 2 (by rfl) ⟨158415, by rfl⟩ : syracuseStep 422441 = 316831) B316831
theorem B1426409 : Blo 279826 1426409 := bstep (se 2 (by rfl) ⟨534903, by rfl⟩ : syracuseStep 1426409 = 1069807) B1069807
theorem B281627 : Blo 279826 281627 := bstep (se 1 (by rfl) ⟨211220, by rfl⟩ : syracuseStep 281627 = 422441) B422441
theorem B1139305 : Blo 279826 1139305 := bstep (se 2 (by rfl) ⟨427239, by rfl⟩ : syracuseStep 1139305 = 854479) B854479
theorem B1075943 : Blo 279826 1075943 := bstep (se 1 (by rfl) ⟨806957, by rfl⟩ : syracuseStep 1075943 = 1613915) B1613915
theorem B423689 : Blo 279826 423689 := bstep (se 2 (by rfl) ⟨158883, by rfl⟩ : syracuseStep 423689 = 317767) B317767
theorem B2029697 : Blo 279826 2029697 := bstep (se 2 (by rfl) ⟨761136, by rfl⟩ : syracuseStep 2029697 = 1522273) B1522273
theorem B950939 : Blo 279826 950939 := bstep (se 1 (by rfl) ⟨713204, by rfl⟩ : syracuseStep 950939 = 1426409) B1426409
theorem B1353131 : Blo 279826 1353131 := bstep (se 1 (by rfl) ⟨1014848, by rfl⟩ : syracuseStep 1353131 = 2029697) B2029697
theorem B1519073 : Blo 279826 1519073 := bstep (se 2 (by rfl) ⟨569652, by rfl⟩ : syracuseStep 1519073 = 1139305) B1139305
theorem B282459 : Blo 279826 282459 := bstep (se 1 (by rfl) ⟨211844, by rfl⟩ : syracuseStep 282459 = 423689) B423689
theorem B717295 : Blo 279826 717295 := bstep (se 1 (by rfl) ⟨537971, by rfl⟩ : syracuseStep 717295 = 1075943) B1075943
theorem B956393 : Blo 279826 956393 := bstep (se 2 (by rfl) ⟨358647, by rfl⟩ : syracuseStep 956393 = 717295) B717295
theorem B633959 : Blo 279826 633959 := bstep (se 1 (by rfl) ⟨475469, by rfl⟩ : syracuseStep 633959 = 950939) B950939
theorem B902087 : Blo 279826 902087 := bstep (se 1 (by rfl) ⟨676565, by rfl⟩ : syracuseStep 902087 = 1353131) B1353131
theorem B1012715 : Blo 279826 1012715 := bstep (se 1 (by rfl) ⟨759536, by rfl⟩ : syracuseStep 1012715 = 1519073) B1519073
theorem B601391 : Blo 279826 601391 := bstep (se 1 (by rfl) ⟨451043, by rfl⟩ : syracuseStep 601391 = 902087) B902087
theorem B637595 : Blo 279826 637595 := bstep (se 1 (by rfl) ⟨478196, by rfl⟩ : syracuseStep 637595 = 956393) B956393
theorem B675143 : Blo 279826 675143 := bstep (se 1 (by rfl) ⟨506357, by rfl⟩ : syracuseStep 675143 = 1012715) B1012715
theorem B422639 : Blo 279826 422639 := bstep (se 1 (by rfl) ⟨316979, by rfl⟩ : syracuseStep 422639 = 633959) B633959
theorem B281759 : Blo 279826 281759 := bstep (se 1 (by rfl) ⟨211319, by rfl⟩ : syracuseStep 281759 = 422639) B422639
theorem B450095 : Blo 279826 450095 := bstep (se 1 (by rfl) ⟨337571, by rfl⟩ : syracuseStep 450095 = 675143) B675143
theorem B1603709 : Blo 279826 1603709 := bstep (se 3 (by rfl) ⟨300695, by rfl⟩ : syracuseStep 1603709 = 601391) B601391
theorem B425063 : Blo 279826 425063 := bstep (se 1 (by rfl) ⟨318797, by rfl⟩ : syracuseStep 425063 = 637595) B637595
theorem B1069139 : Blo 279826 1069139 := bstep (se 1 (by rfl) ⟨801854, by rfl⟩ : syracuseStep 1069139 = 1603709) B1603709
theorem B1200253 : Blo 279826 1200253 := bstep (se 3 (by rfl) ⟨225047, by rfl⟩ : syracuseStep 1200253 = 450095) B450095
theorem B283375 : Blo 279826 283375 := bstep (se 1 (by rfl) ⟨212531, by rfl⟩ : syracuseStep 283375 = 425063) B425063
theorem B712759 : Blo 279826 712759 := bstep (se 1 (by rfl) ⟨534569, by rfl⟩ : syracuseStep 712759 = 1069139) B1069139
theorem B1600337 : Blo 279826 1600337 := bstep (se 2 (by rfl) ⟨600126, by rfl⟩ : syracuseStep 1600337 = 1200253) B1200253
theorem B950345 : Blo 279826 950345 := bstep (se 2 (by rfl) ⟨356379, by rfl⟩ : syracuseStep 950345 = 712759) B712759
theorem B1066891 : Blo 279826 1066891 := bstep (se 1 (by rfl) ⟨800168, by rfl⟩ : syracuseStep 1066891 = 1600337) B1600337
theorem B633563 : Blo 279826 633563 := bstep (se 1 (by rfl) ⟨475172, by rfl⟩ : syracuseStep 633563 = 950345) B950345
theorem B1422521 : Blo 279826 1422521 := bstep (se 2 (by rfl) ⟨533445, by rfl⟩ : syracuseStep 1422521 = 1066891) B1066891
theorem B422375 : Blo 279826 422375 := bstep (se 1 (by rfl) ⟨316781, by rfl⟩ : syracuseStep 422375 = 633563) B633563
theorem B948347 : Blo 279826 948347 := bstep (se 1 (by rfl) ⟨711260, by rfl⟩ : syracuseStep 948347 = 1422521) B1422521
theorem B632231 : Blo 279826 632231 := bstep (se 1 (by rfl) ⟨474173, by rfl⟩ : syracuseStep 632231 = 948347) B948347
theorem B281583 : Blo 279826 281583 := bstep (se 1 (by rfl) ⟨211187, by rfl⟩ : syracuseStep 281583 = 422375) B422375
theorem B421487 : Blo 279826 421487 := bstep (se 1 (by rfl) ⟨316115, by rfl⟩ : syracuseStep 421487 = 632231) B632231
theorem B280991 : Blo 279826 280991 := bstep (se 1 (by rfl) ⟨210743, by rfl⟩ : syracuseStep 280991 = 421487) B421487

theorem C0 (j : ℕ) (h1 : 69956 ≤ j) (h2 : j ≤ 70655) : Blo 279826 (4 * j + 3) := by
  interval_cases j
  · exact B279827
  · exact B279831
  · exact B279835
  · exact B279839
  · exact B279843
  · exact B279847
  · exact B279851
  · exact B279855
  · exact B279859
  · exact B279863
  · exact B279867
  · exact B279871
  · exact B279875
  · exact B279879
  · exact B279883
  · exact B279887
  · exact B279891
  · exact B279895
  · exact B279899
  · exact B279903
  · exact B279907
  · exact B279911
  · exact B279915
  · exact B279919
  · exact B279923
  · exact B279927
  · exact B279931
  · exact B279935
  · exact B279939
  · exact B279943
  · exact B279947
  · exact B279951
  · exact B279955
  · exact B279959
  · exact B279963
  · exact B279967
  · exact B279971
  · exact B279975
  · exact B279979
  · exact B279983
  · exact B279987
  · exact B279991
  · exact B279995
  · exact B279999
  · exact B280003
  · exact B280007
  · exact B280011
  · exact B280015
  · exact B280019
  · exact B280023
  · exact B280027
  · exact B280031
  · exact B280035
  · exact B280039
  · exact B280043
  · exact B280047
  · exact B280051
  · exact B280055
  · exact B280059
  · exact B280063
  · exact B280067
  · exact B280071
  · exact B280075
  · exact B280079
  · exact B280083
  · exact B280087
  · exact B280091
  · exact B280095
  · exact B280099
  · exact B280103
  · exact B280107
  · exact B280111
  · exact B280115
  · exact B280119
  · exact B280123
  · exact B280127
  · exact B280131
  · exact B280135
  · exact B280139
  · exact B280143
  · exact B280147
  · exact B280151
  · exact B280155
  · exact B280159
  · exact B280163
  · exact B280167
  · exact B280171
  · exact B280175
  · exact B280179
  · exact B280183
  · exact B280187
  · exact B280191
  · exact B280195
  · exact B280199
  · exact B280203
  · exact B280207
  · exact B280211
  · exact B280215
  · exact B280219
  · exact B280223
  · exact B280227
  · exact B280231
  · exact B280235
  · exact B280239
  · exact B280243
  · exact B280247
  · exact B280251
  · exact B280255
  · exact B280259
  · exact B280263
  · exact B280267
  · exact B280271
  · exact B280275
  · exact B280279
  · exact B280283
  · exact B280287
  · exact B280291
  · exact B280295
  · exact B280299
  · exact B280303
  · exact B280307
  · exact B280311
  · exact B280315
  · exact B280319
  · exact B280323
  · exact B280327
  · exact B280331
  · exact B280335
  · exact B280339
  · exact B280343
  · exact B280347
  · exact B280351
  · exact B280355
  · exact B280359
  · exact B280363
  · exact B280367
  · exact B280371
  · exact B280375
  · exact B280379
  · exact B280383
  · exact B280387
  · exact B280391
  · exact B280395
  · exact B280399
  · exact B280403
  · exact B280407
  · exact B280411
  · exact B280415
  · exact B280419
  · exact B280423
  · exact B280427
  · exact B280431
  · exact B280435
  · exact B280439
  · exact B280443
  · exact B280447
  · exact B280451
  · exact B280455
  · exact B280459
  · exact B280463
  · exact B280467
  · exact B280471
  · exact B280475
  · exact B280479
  · exact B280483
  · exact B280487
  · exact B280491
  · exact B280495
  · exact B280499
  · exact B280503
  · exact B280507
  · exact B280511
  · exact B280515
  · exact B280519
  · exact B280523
  · exact B280527
  · exact B280531
  · exact B280535
  · exact B280539
  · exact B280543
  · exact B280547
  · exact B280551
  · exact B280555
  · exact B280559
  · exact B280563
  · exact B280567
  · exact B280571
  · exact B280575
  · exact B280579
  · exact B280583
  · exact B280587
  · exact B280591
  · exact B280595
  · exact B280599
  · exact B280603
  · exact B280607
  · exact B280611
  · exact B280615
  · exact B280619
  · exact B280623
  · exact B280627
  · exact B280631
  · exact B280635
  · exact B280639
  · exact B280643
  · exact B280647
  · exact B280651
  · exact B280655
  · exact B280659
  · exact B280663
  · exact B280667
  · exact B280671
  · exact B280675
  · exact B280679
  · exact B280683
  · exact B280687
  · exact B280691
  · exact B280695
  · exact B280699
  · exact B280703
  · exact B280707
  · exact B280711
  · exact B280715
  · exact B280719
  · exact B280723
  · exact B280727
  · exact B280731
  · exact B280735
  · exact B280739
  · exact B280743
  · exact B280747
  · exact B280751
  · exact B280755
  · exact B280759
  · exact B280763
  · exact B280767
  · exact B280771
  · exact B280775
  · exact B280779
  · exact B280783
  · exact B280787
  · exact B280791
  · exact B280795
  · exact B280799
  · exact B280803
  · exact B280807
  · exact B280811
  · exact B280815
  · exact B280819
  · exact B280823
  · exact B280827
  · exact B280831
  · exact B280835
  · exact B280839
  · exact B280843
  · exact B280847
  · exact B280851
  · exact B280855
  · exact B280859
  · exact B280863
  · exact B280867
  · exact B280871
  · exact B280875
  · exact B280879
  · exact B280883
  · exact B280887
  · exact B280891
  · exact B280895
  · exact B280899
  · exact B280903
  · exact B280907
  · exact B280911
  · exact B280915
  · exact B280919
  · exact B280923
  · exact B280927
  · exact B280931
  · exact B280935
  · exact B280939
  · exact B280943
  · exact B280947
  · exact B280951
  · exact B280955
  · exact B280959
  · exact B280963
  · exact B280967
  · exact B280971
  · exact B280975
  · exact B280979
  · exact B280983
  · exact B280987
  · exact B280991
  · exact B280995
  · exact B280999
  · exact B281003
  · exact B281007
  · exact B281011
  · exact B281015
  · exact B281019
  · exact B281023
  · exact B281027
  · exact B281031
  · exact B281035
  · exact B281039
  · exact B281043
  · exact B281047
  · exact B281051
  · exact B281055
  · exact B281059
  · exact B281063
  · exact B281067
  · exact B281071
  · exact B281075
  · exact B281079
  · exact B281083
  · exact B281087
  · exact B281091
  · exact B281095
  · exact B281099
  · exact B281103
  · exact B281107
  · exact B281111
  · exact B281115
  · exact B281119
  · exact B281123
  · exact B281127
  · exact B281131
  · exact B281135
  · exact B281139
  · exact B281143
  · exact B281147
  · exact B281151
  · exact B281155
  · exact B281159
  · exact B281163
  · exact B281167
  · exact B281171
  · exact B281175
  · exact B281179
  · exact B281183
  · exact B281187
  · exact B281191
  · exact B281195
  · exact B281199
  · exact B281203
  · exact B281207
  · exact B281211
  · exact B281215
  · exact B281219
  · exact B281223
  · exact B281227
  · exact B281231
  · exact B281235
  · exact B281239
  · exact B281243
  · exact B281247
  · exact B281251
  · exact B281255
  · exact B281259
  · exact B281263
  · exact B281267
  · exact B281271
  · exact B281275
  · exact B281279
  · exact B281283
  · exact B281287
  · exact B281291
  · exact B281295
  · exact B281299
  · exact B281303
  · exact B281307
  · exact B281311
  · exact B281315
  · exact B281319
  · exact B281323
  · exact B281327
  · exact B281331
  · exact B281335
  · exact B281339
  · exact B281343
  · exact B281347
  · exact B281351
  · exact B281355
  · exact B281359
  · exact B281363
  · exact B281367
  · exact B281371
  · exact B281375
  · exact B281379
  · exact B281383
  · exact B281387
  · exact B281391
  · exact B281395
  · exact B281399
  · exact B281403
  · exact B281407
  · exact B281411
  · exact B281415
  · exact B281419
  · exact B281423
  · exact B281427
  · exact B281431
  · exact B281435
  · exact B281439
  · exact B281443
  · exact B281447
  · exact B281451
  · exact B281455
  · exact B281459
  · exact B281463
  · exact B281467
  · exact B281471
  · exact B281475
  · exact B281479
  · exact B281483
  · exact B281487
  · exact B281491
  · exact B281495
  · exact B281499
  · exact B281503
  · exact B281507
  · exact B281511
  · exact B281515
  · exact B281519
  · exact B281523
  · exact B281527
  · exact B281531
  · exact B281535
  · exact B281539
  · exact B281543
  · exact B281547
  · exact B281551
  · exact B281555
  · exact B281559
  · exact B281563
  · exact B281567
  · exact B281571
  · exact B281575
  · exact B281579
  · exact B281583
  · exact B281587
  · exact B281591
  · exact B281595
  · exact B281599
  · exact B281603
  · exact B281607
  · exact B281611
  · exact B281615
  · exact B281619
  · exact B281623
  · exact B281627
  · exact B281631
  · exact B281635
  · exact B281639
  · exact B281643
  · exact B281647
  · exact B281651
  · exact B281655
  · exact B281659
  · exact B281663
  · exact B281667
  · exact B281671
  · exact B281675
  · exact B281679
  · exact B281683
  · exact B281687
  · exact B281691
  · exact B281695
  · exact B281699
  · exact B281703
  · exact B281707
  · exact B281711
  · exact B281715
  · exact B281719
  · exact B281723
  · exact B281727
  · exact B281731
  · exact B281735
  · exact B281739
  · exact B281743
  · exact B281747
  · exact B281751
  · exact B281755
  · exact B281759
  · exact B281763
  · exact B281767
  · exact B281771
  · exact B281775
  · exact B281779
  · exact B281783
  · exact B281787
  · exact B281791
  · exact B281795
  · exact B281799
  · exact B281803
  · exact B281807
  · exact B281811
  · exact B281815
  · exact B281819
  · exact B281823
  · exact B281827
  · exact B281831
  · exact B281835
  · exact B281839
  · exact B281843
  · exact B281847
  · exact B281851
  · exact B281855
  · exact B281859
  · exact B281863
  · exact B281867
  · exact B281871
  · exact B281875
  · exact B281879
  · exact B281883
  · exact B281887
  · exact B281891
  · exact B281895
  · exact B281899
  · exact B281903
  · exact B281907
  · exact B281911
  · exact B281915
  · exact B281919
  · exact B281923
  · exact B281927
  · exact B281931
  · exact B281935
  · exact B281939
  · exact B281943
  · exact B281947
  · exact B281951
  · exact B281955
  · exact B281959
  · exact B281963
  · exact B281967
  · exact B281971
  · exact B281975
  · exact B281979
  · exact B281983
  · exact B281987
  · exact B281991
  · exact B281995
  · exact B281999
  · exact B282003
  · exact B282007
  · exact B282011
  · exact B282015
  · exact B282019
  · exact B282023
  · exact B282027
  · exact B282031
  · exact B282035
  · exact B282039
  · exact B282043
  · exact B282047
  · exact B282051
  · exact B282055
  · exact B282059
  · exact B282063
  · exact B282067
  · exact B282071
  · exact B282075
  · exact B282079
  · exact B282083
  · exact B282087
  · exact B282091
  · exact B282095
  · exact B282099
  · exact B282103
  · exact B282107
  · exact B282111
  · exact B282115
  · exact B282119
  · exact B282123
  · exact B282127
  · exact B282131
  · exact B282135
  · exact B282139
  · exact B282143
  · exact B282147
  · exact B282151
  · exact B282155
  · exact B282159
  · exact B282163
  · exact B282167
  · exact B282171
  · exact B282175
  · exact B282179
  · exact B282183
  · exact B282187
  · exact B282191
  · exact B282195
  · exact B282199
  · exact B282203
  · exact B282207
  · exact B282211
  · exact B282215
  · exact B282219
  · exact B282223
  · exact B282227
  · exact B282231
  · exact B282235
  · exact B282239
  · exact B282243
  · exact B282247
  · exact B282251
  · exact B282255
  · exact B282259
  · exact B282263
  · exact B282267
  · exact B282271
  · exact B282275
  · exact B282279
  · exact B282283
  · exact B282287
  · exact B282291
  · exact B282295
  · exact B282299
  · exact B282303
  · exact B282307
  · exact B282311
  · exact B282315
  · exact B282319
  · exact B282323
  · exact B282327
  · exact B282331
  · exact B282335
  · exact B282339
  · exact B282343
  · exact B282347
  · exact B282351
  · exact B282355
  · exact B282359
  · exact B282363
  · exact B282367
  · exact B282371
  · exact B282375
  · exact B282379
  · exact B282383
  · exact B282387
  · exact B282391
  · exact B282395
  · exact B282399
  · exact B282403
  · exact B282407
  · exact B282411
  · exact B282415
  · exact B282419
  · exact B282423
  · exact B282427
  · exact B282431
  · exact B282435
  · exact B282439
  · exact B282443
  · exact B282447
  · exact B282451
  · exact B282455
  · exact B282459
  · exact B282463
  · exact B282467
  · exact B282471
  · exact B282475
  · exact B282479
  · exact B282483
  · exact B282487
  · exact B282491
  · exact B282495
  · exact B282499
  · exact B282503
  · exact B282507
  · exact B282511
  · exact B282515
  · exact B282519
  · exact B282523
  · exact B282527
  · exact B282531
  · exact B282535
  · exact B282539
  · exact B282543
  · exact B282547
  · exact B282551
  · exact B282555
  · exact B282559
  · exact B282563
  · exact B282567
  · exact B282571
  · exact B282575
  · exact B282579
  · exact B282583
  · exact B282587
  · exact B282591
  · exact B282595
  · exact B282599
  · exact B282603
  · exact B282607
  · exact B282611
  · exact B282615
  · exact B282619
  · exact B282623

theorem C1 (j : ℕ) (h1 : 70656 ≤ j) (h2 : j ≤ 70955) : Blo 279826 (4 * j + 3) := by
  interval_cases j
  · exact B282627
  · exact B282631
  · exact B282635
  · exact B282639
  · exact B282643
  · exact B282647
  · exact B282651
  · exact B282655
  · exact B282659
  · exact B282663
  · exact B282667
  · exact B282671
  · exact B282675
  · exact B282679
  · exact B282683
  · exact B282687
  · exact B282691
  · exact B282695
  · exact B282699
  · exact B282703
  · exact B282707
  · exact B282711
  · exact B282715
  · exact B282719
  · exact B282723
  · exact B282727
  · exact B282731
  · exact B282735
  · exact B282739
  · exact B282743
  · exact B282747
  · exact B282751
  · exact B282755
  · exact B282759
  · exact B282763
  · exact B282767
  · exact B282771
  · exact B282775
  · exact B282779
  · exact B282783
  · exact B282787
  · exact B282791
  · exact B282795
  · exact B282799
  · exact B282803
  · exact B282807
  · exact B282811
  · exact B282815
  · exact B282819
  · exact B282823
  · exact B282827
  · exact B282831
  · exact B282835
  · exact B282839
  · exact B282843
  · exact B282847
  · exact B282851
  · exact B282855
  · exact B282859
  · exact B282863
  · exact B282867
  · exact B282871
  · exact B282875
  · exact B282879
  · exact B282883
  · exact B282887
  · exact B282891
  · exact B282895
  · exact B282899
  · exact B282903
  · exact B282907
  · exact B282911
  · exact B282915
  · exact B282919
  · exact B282923
  · exact B282927
  · exact B282931
  · exact B282935
  · exact B282939
  · exact B282943
  · exact B282947
  · exact B282951
  · exact B282955
  · exact B282959
  · exact B282963
  · exact B282967
  · exact B282971
  · exact B282975
  · exact B282979
  · exact B282983
  · exact B282987
  · exact B282991
  · exact B282995
  · exact B282999
  · exact B283003
  · exact B283007
  · exact B283011
  · exact B283015
  · exact B283019
  · exact B283023
  · exact B283027
  · exact B283031
  · exact B283035
  · exact B283039
  · exact B283043
  · exact B283047
  · exact B283051
  · exact B283055
  · exact B283059
  · exact B283063
  · exact B283067
  · exact B283071
  · exact B283075
  · exact B283079
  · exact B283083
  · exact B283087
  · exact B283091
  · exact B283095
  · exact B283099
  · exact B283103
  · exact B283107
  · exact B283111
  · exact B283115
  · exact B283119
  · exact B283123
  · exact B283127
  · exact B283131
  · exact B283135
  · exact B283139
  · exact B283143
  · exact B283147
  · exact B283151
  · exact B283155
  · exact B283159
  · exact B283163
  · exact B283167
  · exact B283171
  · exact B283175
  · exact B283179
  · exact B283183
  · exact B283187
  · exact B283191
  · exact B283195
  · exact B283199
  · exact B283203
  · exact B283207
  · exact B283211
  · exact B283215
  · exact B283219
  · exact B283223
  · exact B283227
  · exact B283231
  · exact B283235
  · exact B283239
  · exact B283243
  · exact B283247
  · exact B283251
  · exact B283255
  · exact B283259
  · exact B283263
  · exact B283267
  · exact B283271
  · exact B283275
  · exact B283279
  · exact B283283
  · exact B283287
  · exact B283291
  · exact B283295
  · exact B283299
  · exact B283303
  · exact B283307
  · exact B283311
  · exact B283315
  · exact B283319
  · exact B283323
  · exact B283327
  · exact B283331
  · exact B283335
  · exact B283339
  · exact B283343
  · exact B283347
  · exact B283351
  · exact B283355
  · exact B283359
  · exact B283363
  · exact B283367
  · exact B283371
  · exact B283375
  · exact B283379
  · exact B283383
  · exact B283387
  · exact B283391
  · exact B283395
  · exact B283399
  · exact B283403
  · exact B283407
  · exact B283411
  · exact B283415
  · exact B283419
  · exact B283423
  · exact B283427
  · exact B283431
  · exact B283435
  · exact B283439
  · exact B283443
  · exact B283447
  · exact B283451
  · exact B283455
  · exact B283459
  · exact B283463
  · exact B283467
  · exact B283471
  · exact B283475
  · exact B283479
  · exact B283483
  · exact B283487
  · exact B283491
  · exact B283495
  · exact B283499
  · exact B283503
  · exact B283507
  · exact B283511
  · exact B283515
  · exact B283519
  · exact B283523
  · exact B283527
  · exact B283531
  · exact B283535
  · exact B283539
  · exact B283543
  · exact B283547
  · exact B283551
  · exact B283555
  · exact B283559
  · exact B283563
  · exact B283567
  · exact B283571
  · exact B283575
  · exact B283579
  · exact B283583
  · exact B283587
  · exact B283591
  · exact B283595
  · exact B283599
  · exact B283603
  · exact B283607
  · exact B283611
  · exact B283615
  · exact B283619
  · exact B283623
  · exact B283627
  · exact B283631
  · exact B283635
  · exact B283639
  · exact B283643
  · exact B283647
  · exact B283651
  · exact B283655
  · exact B283659
  · exact B283663
  · exact B283667
  · exact B283671
  · exact B283675
  · exact B283679
  · exact B283683
  · exact B283687
  · exact B283691
  · exact B283695
  · exact B283699
  · exact B283703
  · exact B283707
  · exact B283711
  · exact B283715
  · exact B283719
  · exact B283723
  · exact B283727
  · exact B283731
  · exact B283735
  · exact B283739
  · exact B283743
  · exact B283747
  · exact B283751
  · exact B283755
  · exact B283759
  · exact B283763
  · exact B283767
  · exact B283771
  · exact B283775
  · exact B283779
  · exact B283783
  · exact B283787
  · exact B283791
  · exact B283795
  · exact B283799
  · exact B283803
  · exact B283807
  · exact B283811
  · exact B283815
  · exact B283819
  · exact B283823

theorem solution (m : ℕ) (hlo : 279826 ≤ m) (hhi : m ≤ 283826) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 69956 ≤ j := by omega
    have hj2 : j ≤ 70955 := by omega
    have hb : Blo 279826 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 70656 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
