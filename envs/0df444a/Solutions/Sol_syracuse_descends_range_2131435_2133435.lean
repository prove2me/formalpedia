-- Prove2me | solution 1 for syracuse_descends_range_2131435_2133435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:07.993758+00:00
-- url     : https://prove2.me/submissions/852564e7-ec54-4f60-85ac-837c13b38ffb

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

theorem B2397865 : Blo 2131435 2397865 := bbase (se 2 (by rfl) ⟨899199, by rfl⟩ : syracuseStep 2397865 = 1798399) (by norm_num)
theorem B3197153 : Blo 2131435 3197153 := bstep (se 2 (by rfl) ⟨1198932, by rfl⟩ : syracuseStep 3197153 = 2397865) B2397865
theorem B2131435 : Blo 2131435 2131435 := bstep (se 1 (by rfl) ⟨1598576, by rfl⟩ : syracuseStep 2131435 = 3197153) B3197153
theorem B3840925 : Blo 2131435 3840925 := bbase (se 3 (by rfl) ⟨720173, by rfl⟩ : syracuseStep 3840925 = 1440347) (by norm_num)
theorem B5121233 : Blo 2131435 5121233 := bstep (se 2 (by rfl) ⟨1920462, by rfl⟩ : syracuseStep 5121233 = 3840925) B3840925
theorem B3414155 : Blo 2131435 3414155 := bstep (se 1 (by rfl) ⟨2560616, by rfl⟩ : syracuseStep 3414155 = 5121233) B5121233
theorem B9104413 : Blo 2131435 9104413 := bstep (se 3 (by rfl) ⟨1707077, by rfl⟩ : syracuseStep 9104413 = 3414155) B3414155
theorem B12139217 : Blo 2131435 12139217 := bstep (se 2 (by rfl) ⟨4552206, by rfl⟩ : syracuseStep 12139217 = 9104413) B9104413
theorem B8092811 : Blo 2131435 8092811 := bstep (se 1 (by rfl) ⟨6069608, by rfl⟩ : syracuseStep 8092811 = 12139217) B12139217
theorem B5395207 : Blo 2131435 5395207 := bstep (se 1 (by rfl) ⟨4046405, by rfl⟩ : syracuseStep 5395207 = 8092811) B8092811
theorem B7193609 : Blo 2131435 7193609 := bstep (se 2 (by rfl) ⟨2697603, by rfl⟩ : syracuseStep 7193609 = 5395207) B5395207
theorem B4795739 : Blo 2131435 4795739 := bstep (se 1 (by rfl) ⟨3596804, by rfl⟩ : syracuseStep 4795739 = 7193609) B7193609
theorem B3197159 : Blo 2131435 3197159 := bstep (se 1 (by rfl) ⟨2397869, by rfl⟩ : syracuseStep 3197159 = 4795739) B4795739
theorem B2131439 : Blo 2131435 2131439 := bstep (se 1 (by rfl) ⟨1598579, by rfl⟩ : syracuseStep 2131439 = 3197159) B3197159
theorem B3197165 : Blo 2131435 3197165 := bbase (se 3 (by rfl) ⟨599468, by rfl⟩ : syracuseStep 3197165 = 1198937) (by norm_num)
theorem B2131443 : Blo 2131435 2131443 := bstep (se 1 (by rfl) ⟨1598582, by rfl⟩ : syracuseStep 2131443 = 3197165) B3197165
theorem B4795757 : Blo 2131435 4795757 := bbase (se 3 (by rfl) ⟨899204, by rfl⟩ : syracuseStep 4795757 = 1798409) (by norm_num)
theorem B3197171 : Blo 2131435 3197171 := bstep (se 1 (by rfl) ⟨2397878, by rfl⟩ : syracuseStep 3197171 = 4795757) B4795757
theorem B2131447 : Blo 2131435 2131447 := bstep (se 1 (by rfl) ⟨1598585, by rfl⟩ : syracuseStep 2131447 = 3197171) B3197171
theorem B4046429 : Blo 2131435 4046429 := bbase (se 3 (by rfl) ⟨758705, by rfl⟩ : syracuseStep 4046429 = 1517411) (by norm_num)
theorem B2697619 : Blo 2131435 2697619 := bstep (se 1 (by rfl) ⟨2023214, by rfl⟩ : syracuseStep 2697619 = 4046429) B4046429
theorem B3596825 : Blo 2131435 3596825 := bstep (se 2 (by rfl) ⟨1348809, by rfl⟩ : syracuseStep 3596825 = 2697619) B2697619
theorem B2397883 : Blo 2131435 2397883 := bstep (se 1 (by rfl) ⟨1798412, by rfl⟩ : syracuseStep 2397883 = 3596825) B3596825
theorem B3197177 : Blo 2131435 3197177 := bstep (se 2 (by rfl) ⟨1198941, by rfl⟩ : syracuseStep 3197177 = 2397883) B2397883
theorem B2131451 : Blo 2131435 2131451 := bstep (se 1 (by rfl) ⟨1598588, by rfl⟩ : syracuseStep 2131451 = 3197177) B3197177
theorem B3240805 : Blo 2131435 3240805 := bbase (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) (by norm_num)
theorem B4321073 : Blo 2131435 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B2880715 : Blo 2131435 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B3840953 : Blo 2131435 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B10242541 : Blo 2131435 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B54626885 : Blo 2131435 54626885 := bstep (se 4 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 54626885 = 10242541) B10242541
theorem B36417923 : Blo 2131435 36417923 := bstep (se 1 (by rfl) ⟨27313442, by rfl⟩ : syracuseStep 36417923 = 54626885) B54626885
theorem B24278615 : Blo 2131435 24278615 := bstep (se 1 (by rfl) ⟨18208961, by rfl⟩ : syracuseStep 24278615 = 36417923) B36417923
theorem B16185743 : Blo 2131435 16185743 := bstep (se 1 (by rfl) ⟨12139307, by rfl⟩ : syracuseStep 16185743 = 24278615) B24278615
theorem B10790495 : Blo 2131435 10790495 := bstep (se 1 (by rfl) ⟨8092871, by rfl⟩ : syracuseStep 10790495 = 16185743) B16185743
theorem B7193663 : Blo 2131435 7193663 := bstep (se 1 (by rfl) ⟨5395247, by rfl⟩ : syracuseStep 7193663 = 10790495) B10790495
theorem B4795775 : Blo 2131435 4795775 := bstep (se 1 (by rfl) ⟨3596831, by rfl⟩ : syracuseStep 4795775 = 7193663) B7193663
theorem B3197183 : Blo 2131435 3197183 := bstep (se 1 (by rfl) ⟨2397887, by rfl⟩ : syracuseStep 3197183 = 4795775) B4795775
theorem B2131455 : Blo 2131435 2131455 := bstep (se 1 (by rfl) ⟨1598591, by rfl⟩ : syracuseStep 2131455 = 3197183) B3197183
theorem B3197189 : Blo 2131435 3197189 := bbase (se 4 (by rfl) ⟨299736, by rfl⟩ : syracuseStep 3197189 = 599473) (by norm_num)
theorem B2131459 : Blo 2131435 2131459 := bstep (se 1 (by rfl) ⟨1598594, by rfl⟩ : syracuseStep 2131459 = 3197189) B3197189
theorem B3596845 : Blo 2131435 3596845 := bbase (se 3 (by rfl) ⟨674408, by rfl⟩ : syracuseStep 3596845 = 1348817) (by norm_num)
theorem B4795793 : Blo 2131435 4795793 := bstep (se 2 (by rfl) ⟨1798422, by rfl⟩ : syracuseStep 4795793 = 3596845) B3596845
theorem B3197195 : Blo 2131435 3197195 := bstep (se 1 (by rfl) ⟨2397896, by rfl⟩ : syracuseStep 3197195 = 4795793) B4795793
theorem B2131463 : Blo 2131435 2131463 := bstep (se 1 (by rfl) ⟨1598597, by rfl⟩ : syracuseStep 2131463 = 3197195) B3197195
theorem B2397901 : Blo 2131435 2397901 := bbase (se 3 (by rfl) ⟨449606, by rfl⟩ : syracuseStep 2397901 = 899213) (by norm_num)
theorem B3197201 : Blo 2131435 3197201 := bstep (se 2 (by rfl) ⟨1198950, by rfl⟩ : syracuseStep 3197201 = 2397901) B2397901
theorem B2131467 : Blo 2131435 2131467 := bstep (se 1 (by rfl) ⟨1598600, by rfl⟩ : syracuseStep 2131467 = 3197201) B3197201
theorem B7193717 : Blo 2131435 7193717 := bbase (se 5 (by rfl) ⟨337205, by rfl⟩ : syracuseStep 7193717 = 674411) (by norm_num)
theorem B4795811 : Blo 2131435 4795811 := bstep (se 1 (by rfl) ⟨3596858, by rfl⟩ : syracuseStep 4795811 = 7193717) B7193717
theorem B3197207 : Blo 2131435 3197207 := bstep (se 1 (by rfl) ⟨2397905, by rfl⟩ : syracuseStep 3197207 = 4795811) B4795811
theorem B2131471 : Blo 2131435 2131471 := bstep (se 1 (by rfl) ⟨1598603, by rfl⟩ : syracuseStep 2131471 = 3197207) B3197207
theorem B3197213 : Blo 2131435 3197213 := bbase (se 3 (by rfl) ⟨599477, by rfl⟩ : syracuseStep 3197213 = 1198955) (by norm_num)
theorem B2131475 : Blo 2131435 2131475 := bstep (se 1 (by rfl) ⟨1598606, by rfl⟩ : syracuseStep 2131475 = 3197213) B3197213
theorem B4795829 : Blo 2131435 4795829 := bbase (se 5 (by rfl) ⟨224804, by rfl⟩ : syracuseStep 4795829 = 449609) (by norm_num)
theorem B3197219 : Blo 2131435 3197219 := bstep (se 1 (by rfl) ⟨2397914, by rfl⟩ : syracuseStep 3197219 = 4795829) B4795829
theorem B2131479 : Blo 2131435 2131479 := bstep (se 1 (by rfl) ⟨1598609, by rfl⟩ : syracuseStep 2131479 = 3197219) B3197219
theorem B4552301 : Blo 2131435 4552301 := bbase (se 3 (by rfl) ⟨853556, by rfl⟩ : syracuseStep 4552301 = 1707113) (by norm_num)
theorem B12139469 : Blo 2131435 12139469 := bstep (se 3 (by rfl) ⟨2276150, by rfl⟩ : syracuseStep 12139469 = 4552301) B4552301
theorem B8092979 : Blo 2131435 8092979 := bstep (se 1 (by rfl) ⟨6069734, by rfl⟩ : syracuseStep 8092979 = 12139469) B12139469
theorem B5395319 : Blo 2131435 5395319 := bstep (se 1 (by rfl) ⟨4046489, by rfl⟩ : syracuseStep 5395319 = 8092979) B8092979
theorem B3596879 : Blo 2131435 3596879 := bstep (se 1 (by rfl) ⟨2697659, by rfl⟩ : syracuseStep 3596879 = 5395319) B5395319
theorem B2397919 : Blo 2131435 2397919 := bstep (se 1 (by rfl) ⟨1798439, by rfl⟩ : syracuseStep 2397919 = 3596879) B3596879
theorem B3197225 : Blo 2131435 3197225 := bstep (se 2 (by rfl) ⟨1198959, by rfl⟩ : syracuseStep 3197225 = 2397919) B2397919
theorem B2131483 : Blo 2131435 2131483 := bstep (se 1 (by rfl) ⟨1598612, by rfl⟩ : syracuseStep 2131483 = 3197225) B3197225
theorem B4552309 : Blo 2131435 4552309 := bbase (se 5 (by rfl) ⟨213389, by rfl⟩ : syracuseStep 4552309 = 426779) (by norm_num)
theorem B6069745 : Blo 2131435 6069745 := bstep (se 2 (by rfl) ⟨2276154, by rfl⟩ : syracuseStep 6069745 = 4552309) B4552309
theorem B8092993 : Blo 2131435 8092993 := bstep (se 2 (by rfl) ⟨3034872, by rfl⟩ : syracuseStep 8092993 = 6069745) B6069745
theorem B10790657 : Blo 2131435 10790657 := bstep (se 2 (by rfl) ⟨4046496, by rfl⟩ : syracuseStep 10790657 = 8092993) B8092993
theorem B7193771 : Blo 2131435 7193771 := bstep (se 1 (by rfl) ⟨5395328, by rfl⟩ : syracuseStep 7193771 = 10790657) B10790657
theorem B4795847 : Blo 2131435 4795847 := bstep (se 1 (by rfl) ⟨3596885, by rfl⟩ : syracuseStep 4795847 = 7193771) B7193771
theorem B3197231 : Blo 2131435 3197231 := bstep (se 1 (by rfl) ⟨2397923, by rfl⟩ : syracuseStep 3197231 = 4795847) B4795847
theorem B2131487 : Blo 2131435 2131487 := bstep (se 1 (by rfl) ⟨1598615, by rfl⟩ : syracuseStep 2131487 = 3197231) B3197231
theorem B3197237 : Blo 2131435 3197237 := bbase (se 5 (by rfl) ⟨149870, by rfl⟩ : syracuseStep 3197237 = 299741) (by norm_num)
theorem B2131491 : Blo 2131435 2131491 := bstep (se 1 (by rfl) ⟨1598618, by rfl⟩ : syracuseStep 2131491 = 3197237) B3197237
theorem B5395349 : Blo 2131435 5395349 := bbase (se 6 (by rfl) ⟨126453, by rfl⟩ : syracuseStep 5395349 = 252907) (by norm_num)
theorem B3596899 : Blo 2131435 3596899 := bstep (se 1 (by rfl) ⟨2697674, by rfl⟩ : syracuseStep 3596899 = 5395349) B5395349
theorem B4795865 : Blo 2131435 4795865 := bstep (se 2 (by rfl) ⟨1798449, by rfl⟩ : syracuseStep 4795865 = 3596899) B3596899
theorem B3197243 : Blo 2131435 3197243 := bstep (se 1 (by rfl) ⟨2397932, by rfl⟩ : syracuseStep 3197243 = 4795865) B4795865
theorem B2131495 : Blo 2131435 2131495 := bstep (se 1 (by rfl) ⟨1598621, by rfl⟩ : syracuseStep 2131495 = 3197243) B3197243
theorem B2397937 : Blo 2131435 2397937 := bbase (se 2 (by rfl) ⟨899226, by rfl⟩ : syracuseStep 2397937 = 1798453) (by norm_num)
theorem B3197249 : Blo 2131435 3197249 := bstep (se 2 (by rfl) ⟨1198968, by rfl⟩ : syracuseStep 3197249 = 2397937) B2397937
theorem B2131499 : Blo 2131435 2131499 := bstep (se 1 (by rfl) ⟨1598624, by rfl⟩ : syracuseStep 2131499 = 3197249) B3197249
theorem B8428853 : Blo 2131435 8428853 := bbase (se 5 (by rfl) ⟨395102, by rfl⟩ : syracuseStep 8428853 = 790205) (by norm_num)
theorem B5619235 : Blo 2131435 5619235 := bstep (se 1 (by rfl) ⟨4214426, by rfl⟩ : syracuseStep 5619235 = 8428853) B8428853
theorem B7492313 : Blo 2131435 7492313 := bstep (se 2 (by rfl) ⟨2809617, by rfl⟩ : syracuseStep 7492313 = 5619235) B5619235
theorem B4994875 : Blo 2131435 4994875 := bstep (se 1 (by rfl) ⟨3746156, by rfl⟩ : syracuseStep 4994875 = 7492313) B7492313
theorem B6659833 : Blo 2131435 6659833 := bstep (se 2 (by rfl) ⟨2497437, by rfl⟩ : syracuseStep 6659833 = 4994875) B4994875
theorem B8879777 : Blo 2131435 8879777 := bstep (se 2 (by rfl) ⟨3329916, by rfl⟩ : syracuseStep 8879777 = 6659833) B6659833
theorem B5919851 : Blo 2131435 5919851 := bstep (se 1 (by rfl) ⟨4439888, by rfl⟩ : syracuseStep 5919851 = 8879777) B8879777
theorem B3946567 : Blo 2131435 3946567 := bstep (se 1 (by rfl) ⟨2959925, by rfl⟩ : syracuseStep 3946567 = 5919851) B5919851
theorem B5262089 : Blo 2131435 5262089 := bstep (se 2 (by rfl) ⟨1973283, by rfl⟩ : syracuseStep 5262089 = 3946567) B3946567
theorem B14032237 : Blo 2131435 14032237 := bstep (se 3 (by rfl) ⟨2631044, by rfl⟩ : syracuseStep 14032237 = 5262089) B5262089
theorem B18709649 : Blo 2131435 18709649 := bstep (se 2 (by rfl) ⟨7016118, by rfl⟩ : syracuseStep 18709649 = 14032237) B14032237
theorem B12473099 : Blo 2131435 12473099 := bstep (se 1 (by rfl) ⟨9354824, by rfl⟩ : syracuseStep 12473099 = 18709649) B18709649
theorem B8315399 : Blo 2131435 8315399 := bstep (se 1 (by rfl) ⟨6236549, by rfl⟩ : syracuseStep 8315399 = 12473099) B12473099
theorem B5543599 : Blo 2131435 5543599 := bstep (se 1 (by rfl) ⟨4157699, by rfl⟩ : syracuseStep 5543599 = 8315399) B8315399
theorem B7391465 : Blo 2131435 7391465 := bstep (se 2 (by rfl) ⟨2771799, by rfl⟩ : syracuseStep 7391465 = 5543599) B5543599
theorem B4927643 : Blo 2131435 4927643 := bstep (se 1 (by rfl) ⟨3695732, by rfl⟩ : syracuseStep 4927643 = 7391465) B7391465
theorem B3285095 : Blo 2131435 3285095 := bstep (se 1 (by rfl) ⟨2463821, by rfl⟩ : syracuseStep 3285095 = 4927643) B4927643
theorem B8760253 : Blo 2131435 8760253 := bstep (se 3 (by rfl) ⟨1642547, by rfl⟩ : syracuseStep 8760253 = 3285095) B3285095
theorem B11680337 : Blo 2131435 11680337 := bstep (se 2 (by rfl) ⟨4380126, by rfl⟩ : syracuseStep 11680337 = 8760253) B8760253
theorem B7786891 : Blo 2131435 7786891 := bstep (se 1 (by rfl) ⟨5840168, by rfl⟩ : syracuseStep 7786891 = 11680337) B11680337
theorem B10382521 : Blo 2131435 10382521 := bstep (se 2 (by rfl) ⟨3893445, by rfl⟩ : syracuseStep 10382521 = 7786891) B7786891
theorem B13843361 : Blo 2131435 13843361 := bstep (se 2 (by rfl) ⟨5191260, by rfl⟩ : syracuseStep 13843361 = 10382521) B10382521
theorem B9228907 : Blo 2131435 9228907 := bstep (se 1 (by rfl) ⟨6921680, by rfl⟩ : syracuseStep 9228907 = 13843361) B13843361
theorem B12305209 : Blo 2131435 12305209 := bstep (se 2 (by rfl) ⟨4614453, by rfl⟩ : syracuseStep 12305209 = 9228907) B9228907
theorem B16406945 : Blo 2131435 16406945 := bstep (se 2 (by rfl) ⟨6152604, by rfl⟩ : syracuseStep 16406945 = 12305209) B12305209
theorem B10937963 : Blo 2131435 10937963 := bstep (se 1 (by rfl) ⟨8203472, by rfl⟩ : syracuseStep 10937963 = 16406945) B16406945
theorem B29167901 : Blo 2131435 29167901 := bstep (se 3 (by rfl) ⟨5468981, by rfl⟩ : syracuseStep 29167901 = 10937963) B10937963
theorem B19445267 : Blo 2131435 19445267 := bstep (se 1 (by rfl) ⟨14583950, by rfl⟩ : syracuseStep 19445267 = 29167901) B29167901
theorem B12963511 : Blo 2131435 12963511 := bstep (se 1 (by rfl) ⟨9722633, by rfl⟩ : syracuseStep 12963511 = 19445267) B19445267
theorem B17284681 : Blo 2131435 17284681 := bstep (se 2 (by rfl) ⟨6481755, by rfl⟩ : syracuseStep 17284681 = 12963511) B12963511
theorem B23046241 : Blo 2131435 23046241 := bstep (se 2 (by rfl) ⟨8642340, by rfl⟩ : syracuseStep 23046241 = 17284681) B17284681
theorem B30728321 : Blo 2131435 30728321 := bstep (se 2 (by rfl) ⟨11523120, by rfl⟩ : syracuseStep 30728321 = 23046241) B23046241
theorem B20485547 : Blo 2131435 20485547 := bstep (se 1 (by rfl) ⟨15364160, by rfl⟩ : syracuseStep 20485547 = 30728321) B30728321
theorem B13657031 : Blo 2131435 13657031 := bstep (se 1 (by rfl) ⟨10242773, by rfl⟩ : syracuseStep 13657031 = 20485547) B20485547
theorem B9104687 : Blo 2131435 9104687 := bstep (se 1 (by rfl) ⟨6828515, by rfl⟩ : syracuseStep 9104687 = 13657031) B13657031
theorem B6069791 : Blo 2131435 6069791 := bstep (se 1 (by rfl) ⟨4552343, by rfl⟩ : syracuseStep 6069791 = 9104687) B9104687
theorem B4046527 : Blo 2131435 4046527 := bstep (se 1 (by rfl) ⟨3034895, by rfl⟩ : syracuseStep 4046527 = 6069791) B6069791
theorem B5395369 : Blo 2131435 5395369 := bstep (se 2 (by rfl) ⟨2023263, by rfl⟩ : syracuseStep 5395369 = 4046527) B4046527
theorem B7193825 : Blo 2131435 7193825 := bstep (se 2 (by rfl) ⟨2697684, by rfl⟩ : syracuseStep 7193825 = 5395369) B5395369
theorem B4795883 : Blo 2131435 4795883 := bstep (se 1 (by rfl) ⟨3596912, by rfl⟩ : syracuseStep 4795883 = 7193825) B7193825
theorem B3197255 : Blo 2131435 3197255 := bstep (se 1 (by rfl) ⟨2397941, by rfl⟩ : syracuseStep 3197255 = 4795883) B4795883
theorem B2131503 : Blo 2131435 2131503 := bstep (se 1 (by rfl) ⟨1598627, by rfl⟩ : syracuseStep 2131503 = 3197255) B3197255
theorem B3197261 : Blo 2131435 3197261 := bbase (se 3 (by rfl) ⟨599486, by rfl⟩ : syracuseStep 3197261 = 1198973) (by norm_num)
theorem B2131507 : Blo 2131435 2131507 := bstep (se 1 (by rfl) ⟨1598630, by rfl⟩ : syracuseStep 2131507 = 3197261) B3197261
theorem B4795901 : Blo 2131435 4795901 := bbase (se 3 (by rfl) ⟨899231, by rfl⟩ : syracuseStep 4795901 = 1798463) (by norm_num)
theorem B3197267 : Blo 2131435 3197267 := bstep (se 1 (by rfl) ⟨2397950, by rfl⟩ : syracuseStep 3197267 = 4795901) B4795901
theorem B2131511 : Blo 2131435 2131511 := bstep (se 1 (by rfl) ⟨1598633, by rfl⟩ : syracuseStep 2131511 = 3197267) B3197267
theorem B3596933 : Blo 2131435 3596933 := bbase (se 4 (by rfl) ⟨337212, by rfl⟩ : syracuseStep 3596933 = 674425) (by norm_num)
theorem B2397955 : Blo 2131435 2397955 := bstep (se 1 (by rfl) ⟨1798466, by rfl⟩ : syracuseStep 2397955 = 3596933) B3596933
theorem B3197273 : Blo 2131435 3197273 := bstep (se 2 (by rfl) ⟨1198977, by rfl⟩ : syracuseStep 3197273 = 2397955) B2397955
theorem B2131515 : Blo 2131435 2131515 := bstep (se 1 (by rfl) ⟨1598636, by rfl⟩ : syracuseStep 2131515 = 3197273) B3197273
theorem B16186229 : Blo 2131435 16186229 := bbase (se 5 (by rfl) ⟨758729, by rfl⟩ : syracuseStep 16186229 = 1517459) (by norm_num)
theorem B10790819 : Blo 2131435 10790819 := bstep (se 1 (by rfl) ⟨8093114, by rfl⟩ : syracuseStep 10790819 = 16186229) B16186229
theorem B7193879 : Blo 2131435 7193879 := bstep (se 1 (by rfl) ⟨5395409, by rfl⟩ : syracuseStep 7193879 = 10790819) B10790819
theorem B4795919 : Blo 2131435 4795919 := bstep (se 1 (by rfl) ⟨3596939, by rfl⟩ : syracuseStep 4795919 = 7193879) B7193879
theorem B3197279 : Blo 2131435 3197279 := bstep (se 1 (by rfl) ⟨2397959, by rfl⟩ : syracuseStep 3197279 = 4795919) B4795919
theorem B2131519 : Blo 2131435 2131519 := bstep (se 1 (by rfl) ⟨1598639, by rfl⟩ : syracuseStep 2131519 = 3197279) B3197279
theorem B3197285 : Blo 2131435 3197285 := bbase (se 4 (by rfl) ⟨299745, by rfl⟩ : syracuseStep 3197285 = 599491) (by norm_num)
theorem B2131523 : Blo 2131435 2131523 := bstep (se 1 (by rfl) ⟨1598642, by rfl⟩ : syracuseStep 2131523 = 3197285) B3197285
theorem B4046573 : Blo 2131435 4046573 := bbase (se 3 (by rfl) ⟨758732, by rfl⟩ : syracuseStep 4046573 = 1517465) (by norm_num)
theorem B2697715 : Blo 2131435 2697715 := bstep (se 1 (by rfl) ⟨2023286, by rfl⟩ : syracuseStep 2697715 = 4046573) B4046573
theorem B3596953 : Blo 2131435 3596953 := bstep (se 2 (by rfl) ⟨1348857, by rfl⟩ : syracuseStep 3596953 = 2697715) B2697715
theorem B4795937 : Blo 2131435 4795937 := bstep (se 2 (by rfl) ⟨1798476, by rfl⟩ : syracuseStep 4795937 = 3596953) B3596953
theorem B3197291 : Blo 2131435 3197291 := bstep (se 1 (by rfl) ⟨2397968, by rfl⟩ : syracuseStep 3197291 = 4795937) B4795937
theorem B2131527 : Blo 2131435 2131527 := bstep (se 1 (by rfl) ⟨1598645, by rfl⟩ : syracuseStep 2131527 = 3197291) B3197291
theorem B2397973 : Blo 2131435 2397973 := bbase (se 6 (by rfl) ⟨56202, by rfl⟩ : syracuseStep 2397973 = 112405) (by norm_num)
theorem B3197297 : Blo 2131435 3197297 := bstep (se 2 (by rfl) ⟨1198986, by rfl⟩ : syracuseStep 3197297 = 2397973) B2397973
theorem B2131531 : Blo 2131435 2131531 := bstep (se 1 (by rfl) ⟨1598648, by rfl⟩ : syracuseStep 2131531 = 3197297) B3197297
theorem B2697725 : Blo 2131435 2697725 := bbase (se 3 (by rfl) ⟨505823, by rfl⟩ : syracuseStep 2697725 = 1011647) (by norm_num)
theorem B7193933 : Blo 2131435 7193933 := bstep (se 3 (by rfl) ⟨1348862, by rfl⟩ : syracuseStep 7193933 = 2697725) B2697725
theorem B4795955 : Blo 2131435 4795955 := bstep (se 1 (by rfl) ⟨3596966, by rfl⟩ : syracuseStep 4795955 = 7193933) B7193933
theorem B3197303 : Blo 2131435 3197303 := bstep (se 1 (by rfl) ⟨2397977, by rfl⟩ : syracuseStep 3197303 = 4795955) B4795955
theorem B2131535 : Blo 2131435 2131535 := bstep (se 1 (by rfl) ⟨1598651, by rfl⟩ : syracuseStep 2131535 = 3197303) B3197303
theorem B3197309 : Blo 2131435 3197309 := bbase (se 3 (by rfl) ⟨599495, by rfl⟩ : syracuseStep 3197309 = 1198991) (by norm_num)
theorem B2131539 : Blo 2131435 2131539 := bstep (se 1 (by rfl) ⟨1598654, by rfl⟩ : syracuseStep 2131539 = 3197309) B3197309
theorem B4795973 : Blo 2131435 4795973 := bbase (se 4 (by rfl) ⟨449622, by rfl⟩ : syracuseStep 4795973 = 899245) (by norm_num)
theorem B3197315 : Blo 2131435 3197315 := bstep (se 1 (by rfl) ⟨2397986, by rfl⟩ : syracuseStep 3197315 = 4795973) B4795973
theorem B2131543 : Blo 2131435 2131543 := bstep (se 1 (by rfl) ⟨1598657, by rfl⟩ : syracuseStep 2131543 = 3197315) B3197315
theorem B4861421 : Blo 2131435 4861421 := bbase (se 3 (by rfl) ⟨911516, by rfl⟩ : syracuseStep 4861421 = 1823033) (by norm_num)
theorem B3240947 : Blo 2131435 3240947 := bstep (se 1 (by rfl) ⟨2430710, by rfl⟩ : syracuseStep 3240947 = 4861421) B4861421
theorem B2160631 : Blo 2131435 2160631 := bstep (se 1 (by rfl) ⟨1620473, by rfl⟩ : syracuseStep 2160631 = 3240947) B3240947
theorem B2880841 : Blo 2131435 2880841 := bstep (se 2 (by rfl) ⟨1080315, by rfl⟩ : syracuseStep 2880841 = 2160631) B2160631
theorem B3841121 : Blo 2131435 3841121 := bstep (se 2 (by rfl) ⟨1440420, by rfl⟩ : syracuseStep 3841121 = 2880841) B2880841
theorem B2560747 : Blo 2131435 2560747 := bstep (se 1 (by rfl) ⟨1920560, by rfl⟩ : syracuseStep 2560747 = 3841121) B3841121
theorem B3414329 : Blo 2131435 3414329 := bstep (se 2 (by rfl) ⟨1280373, by rfl⟩ : syracuseStep 3414329 = 2560747) B2560747
theorem B2276219 : Blo 2131435 2276219 := bstep (se 1 (by rfl) ⟨1707164, by rfl⟩ : syracuseStep 2276219 = 3414329) B3414329
theorem B6069917 : Blo 2131435 6069917 := bstep (se 3 (by rfl) ⟨1138109, by rfl⟩ : syracuseStep 6069917 = 2276219) B2276219
theorem B4046611 : Blo 2131435 4046611 := bstep (se 1 (by rfl) ⟨3034958, by rfl⟩ : syracuseStep 4046611 = 6069917) B6069917
theorem B5395481 : Blo 2131435 5395481 := bstep (se 2 (by rfl) ⟨2023305, by rfl⟩ : syracuseStep 5395481 = 4046611) B4046611
theorem B3596987 : Blo 2131435 3596987 := bstep (se 1 (by rfl) ⟨2697740, by rfl⟩ : syracuseStep 3596987 = 5395481) B5395481
theorem B2397991 : Blo 2131435 2397991 := bstep (se 1 (by rfl) ⟨1798493, by rfl⟩ : syracuseStep 2397991 = 3596987) B3596987
theorem B3197321 : Blo 2131435 3197321 := bstep (se 2 (by rfl) ⟨1198995, by rfl⟩ : syracuseStep 3197321 = 2397991) B2397991
theorem B2131547 : Blo 2131435 2131547 := bstep (se 1 (by rfl) ⟨1598660, by rfl⟩ : syracuseStep 2131547 = 3197321) B3197321
theorem B10790981 : Blo 2131435 10790981 := bbase (se 4 (by rfl) ⟨1011654, by rfl⟩ : syracuseStep 10790981 = 2023309) (by norm_num)
theorem B7193987 : Blo 2131435 7193987 := bstep (se 1 (by rfl) ⟨5395490, by rfl⟩ : syracuseStep 7193987 = 10790981) B10790981
theorem B4795991 : Blo 2131435 4795991 := bstep (se 1 (by rfl) ⟨3596993, by rfl⟩ : syracuseStep 4795991 = 7193987) B7193987
theorem B3197327 : Blo 2131435 3197327 := bstep (se 1 (by rfl) ⟨2397995, by rfl⟩ : syracuseStep 3197327 = 4795991) B4795991
theorem B2131551 : Blo 2131435 2131551 := bstep (se 1 (by rfl) ⟨1598663, by rfl⟩ : syracuseStep 2131551 = 3197327) B3197327
theorem B3197333 : Blo 2131435 3197333 := bbase (se 6 (by rfl) ⟨74937, by rfl⟩ : syracuseStep 3197333 = 149875) (by norm_num)
theorem B2131555 : Blo 2131435 2131555 := bstep (se 1 (by rfl) ⟨1598666, by rfl⟩ : syracuseStep 2131555 = 3197333) B3197333
theorem B15364565 : Blo 2131435 15364565 := bbase (se 7 (by rfl) ⟨180053, by rfl⟩ : syracuseStep 15364565 = 360107) (by norm_num)
theorem B10243043 : Blo 2131435 10243043 := bstep (se 1 (by rfl) ⟨7682282, by rfl⟩ : syracuseStep 10243043 = 15364565) B15364565
theorem B6828695 : Blo 2131435 6828695 := bstep (se 1 (by rfl) ⟨5121521, by rfl⟩ : syracuseStep 6828695 = 10243043) B10243043
theorem B4552463 : Blo 2131435 4552463 := bstep (se 1 (by rfl) ⟨3414347, by rfl⟩ : syracuseStep 4552463 = 6828695) B6828695
theorem B12139901 : Blo 2131435 12139901 := bstep (se 3 (by rfl) ⟨2276231, by rfl⟩ : syracuseStep 12139901 = 4552463) B4552463
theorem B8093267 : Blo 2131435 8093267 := bstep (se 1 (by rfl) ⟨6069950, by rfl⟩ : syracuseStep 8093267 = 12139901) B12139901
theorem B5395511 : Blo 2131435 5395511 := bstep (se 1 (by rfl) ⟨4046633, by rfl⟩ : syracuseStep 5395511 = 8093267) B8093267
theorem B3597007 : Blo 2131435 3597007 := bstep (se 1 (by rfl) ⟨2697755, by rfl⟩ : syracuseStep 3597007 = 5395511) B5395511
theorem B4796009 : Blo 2131435 4796009 := bstep (se 2 (by rfl) ⟨1798503, by rfl⟩ : syracuseStep 4796009 = 3597007) B3597007
theorem B3197339 : Blo 2131435 3197339 := bstep (se 1 (by rfl) ⟨2398004, by rfl⟩ : syracuseStep 3197339 = 4796009) B4796009
theorem B2131559 : Blo 2131435 2131559 := bstep (se 1 (by rfl) ⟨1598669, by rfl⟩ : syracuseStep 2131559 = 3197339) B3197339
theorem B2398009 : Blo 2131435 2398009 := bbase (se 2 (by rfl) ⟨899253, by rfl⟩ : syracuseStep 2398009 = 1798507) (by norm_num)
theorem B3197345 : Blo 2131435 3197345 := bstep (se 2 (by rfl) ⟨1199004, by rfl⟩ : syracuseStep 3197345 = 2398009) B2398009
theorem B2131563 : Blo 2131435 2131563 := bstep (se 1 (by rfl) ⟨1598672, by rfl⟩ : syracuseStep 2131563 = 3197345) B3197345
theorem B6069973 : Blo 2131435 6069973 := bbase (se 7 (by rfl) ⟨71132, by rfl⟩ : syracuseStep 6069973 = 142265) (by norm_num)
theorem B8093297 : Blo 2131435 8093297 := bstep (se 2 (by rfl) ⟨3034986, by rfl⟩ : syracuseStep 8093297 = 6069973) B6069973
theorem B5395531 : Blo 2131435 5395531 := bstep (se 1 (by rfl) ⟨4046648, by rfl⟩ : syracuseStep 5395531 = 8093297) B8093297
theorem B7194041 : Blo 2131435 7194041 := bstep (se 2 (by rfl) ⟨2697765, by rfl⟩ : syracuseStep 7194041 = 5395531) B5395531
theorem B4796027 : Blo 2131435 4796027 := bstep (se 1 (by rfl) ⟨3597020, by rfl⟩ : syracuseStep 4796027 = 7194041) B7194041
theorem B3197351 : Blo 2131435 3197351 := bstep (se 1 (by rfl) ⟨2398013, by rfl⟩ : syracuseStep 3197351 = 4796027) B4796027
theorem B2131567 : Blo 2131435 2131567 := bstep (se 1 (by rfl) ⟨1598675, by rfl⟩ : syracuseStep 2131567 = 3197351) B3197351
theorem B3197357 : Blo 2131435 3197357 := bbase (se 3 (by rfl) ⟨599504, by rfl⟩ : syracuseStep 3197357 = 1199009) (by norm_num)
theorem B2131571 : Blo 2131435 2131571 := bstep (se 1 (by rfl) ⟨1598678, by rfl⟩ : syracuseStep 2131571 = 3197357) B3197357
theorem B4796045 : Blo 2131435 4796045 := bbase (se 3 (by rfl) ⟨899258, by rfl⟩ : syracuseStep 4796045 = 1798517) (by norm_num)
theorem B3197363 : Blo 2131435 3197363 := bstep (se 1 (by rfl) ⟨2398022, by rfl⟩ : syracuseStep 3197363 = 4796045) B4796045
theorem B2131575 : Blo 2131435 2131575 := bstep (se 1 (by rfl) ⟨1598681, by rfl⟩ : syracuseStep 2131575 = 3197363) B3197363
theorem B2697781 : Blo 2131435 2697781 := bbase (se 5 (by rfl) ⟨126458, by rfl⟩ : syracuseStep 2697781 = 252917) (by norm_num)
theorem B3597041 : Blo 2131435 3597041 := bstep (se 2 (by rfl) ⟨1348890, by rfl⟩ : syracuseStep 3597041 = 2697781) B2697781
theorem B2398027 : Blo 2131435 2398027 := bstep (se 1 (by rfl) ⟨1798520, by rfl⟩ : syracuseStep 2398027 = 3597041) B3597041
theorem B3197369 : Blo 2131435 3197369 := bstep (se 2 (by rfl) ⟨1199013, by rfl⟩ : syracuseStep 3197369 = 2398027) B2398027
theorem B2131579 : Blo 2131435 2131579 := bstep (se 1 (by rfl) ⟨1598684, by rfl⟩ : syracuseStep 2131579 = 3197369) B3197369
theorem B8760581 : Blo 2131435 8760581 := bbase (se 4 (by rfl) ⟨821304, by rfl⟩ : syracuseStep 8760581 = 1642609) (by norm_num)
theorem B5840387 : Blo 2131435 5840387 := bstep (se 1 (by rfl) ⟨4380290, by rfl⟩ : syracuseStep 5840387 = 8760581) B8760581
theorem B3893591 : Blo 2131435 3893591 := bstep (se 1 (by rfl) ⟨2920193, by rfl⟩ : syracuseStep 3893591 = 5840387) B5840387
theorem B2595727 : Blo 2131435 2595727 := bstep (se 1 (by rfl) ⟨1946795, by rfl⟩ : syracuseStep 2595727 = 3893591) B3893591
theorem B13843877 : Blo 2131435 13843877 := bstep (se 4 (by rfl) ⟨1297863, by rfl⟩ : syracuseStep 13843877 = 2595727) B2595727
theorem B36917005 : Blo 2131435 36917005 := bstep (se 3 (by rfl) ⟨6921938, by rfl⟩ : syracuseStep 36917005 = 13843877) B13843877
theorem B49222673 : Blo 2131435 49222673 := bstep (se 2 (by rfl) ⟨18458502, by rfl⟩ : syracuseStep 49222673 = 36917005) B36917005
theorem B32815115 : Blo 2131435 32815115 := bstep (se 1 (by rfl) ⟨24611336, by rfl⟩ : syracuseStep 32815115 = 49222673) B49222673
theorem B21876743 : Blo 2131435 21876743 := bstep (se 1 (by rfl) ⟨16407557, by rfl⟩ : syracuseStep 21876743 = 32815115) B32815115
theorem B58337981 : Blo 2131435 58337981 := bstep (se 3 (by rfl) ⟨10938371, by rfl⟩ : syracuseStep 58337981 = 21876743) B21876743
theorem B38891987 : Blo 2131435 38891987 := bstep (se 1 (by rfl) ⟨29168990, by rfl⟩ : syracuseStep 38891987 = 58337981) B58337981
theorem B25927991 : Blo 2131435 25927991 := bstep (se 1 (by rfl) ⟨19445993, by rfl⟩ : syracuseStep 25927991 = 38891987) B38891987
theorem B17285327 : Blo 2131435 17285327 := bstep (se 1 (by rfl) ⟨12963995, by rfl⟩ : syracuseStep 17285327 = 25927991) B25927991
theorem B11523551 : Blo 2131435 11523551 := bstep (se 1 (by rfl) ⟨8642663, by rfl⟩ : syracuseStep 11523551 = 17285327) B17285327
theorem B30729469 : Blo 2131435 30729469 := bstep (se 3 (by rfl) ⟨5761775, by rfl⟩ : syracuseStep 30729469 = 11523551) B11523551
theorem B40972625 : Blo 2131435 40972625 := bstep (se 2 (by rfl) ⟨15364734, by rfl⟩ : syracuseStep 40972625 = 30729469) B30729469
theorem B27315083 : Blo 2131435 27315083 := bstep (se 1 (by rfl) ⟨20486312, by rfl⟩ : syracuseStep 27315083 = 40972625) B40972625
theorem B18210055 : Blo 2131435 18210055 := bstep (se 1 (by rfl) ⟨13657541, by rfl⟩ : syracuseStep 18210055 = 27315083) B27315083
theorem B24280073 : Blo 2131435 24280073 := bstep (se 2 (by rfl) ⟨9105027, by rfl⟩ : syracuseStep 24280073 = 18210055) B18210055
theorem B16186715 : Blo 2131435 16186715 := bstep (se 1 (by rfl) ⟨12140036, by rfl⟩ : syracuseStep 16186715 = 24280073) B24280073
theorem B10791143 : Blo 2131435 10791143 := bstep (se 1 (by rfl) ⟨8093357, by rfl⟩ : syracuseStep 10791143 = 16186715) B16186715
theorem B7194095 : Blo 2131435 7194095 := bstep (se 1 (by rfl) ⟨5395571, by rfl⟩ : syracuseStep 7194095 = 10791143) B10791143
theorem B4796063 : Blo 2131435 4796063 := bstep (se 1 (by rfl) ⟨3597047, by rfl⟩ : syracuseStep 4796063 = 7194095) B7194095
theorem B3197375 : Blo 2131435 3197375 := bstep (se 1 (by rfl) ⟨2398031, by rfl⟩ : syracuseStep 3197375 = 4796063) B4796063
theorem B2131583 : Blo 2131435 2131583 := bstep (se 1 (by rfl) ⟨1598687, by rfl⟩ : syracuseStep 2131583 = 3197375) B3197375
theorem B3197381 : Blo 2131435 3197381 := bbase (se 4 (by rfl) ⟨299754, by rfl⟩ : syracuseStep 3197381 = 599509) (by norm_num)
theorem B2131587 : Blo 2131435 2131587 := bstep (se 1 (by rfl) ⟨1598690, by rfl⟩ : syracuseStep 2131587 = 3197381) B3197381
theorem B3597061 : Blo 2131435 3597061 := bbase (se 4 (by rfl) ⟨337224, by rfl⟩ : syracuseStep 3597061 = 674449) (by norm_num)
theorem B4796081 : Blo 2131435 4796081 := bstep (se 2 (by rfl) ⟨1798530, by rfl⟩ : syracuseStep 4796081 = 3597061) B3597061
theorem B3197387 : Blo 2131435 3197387 := bstep (se 1 (by rfl) ⟨2398040, by rfl⟩ : syracuseStep 3197387 = 4796081) B4796081
theorem B2131591 : Blo 2131435 2131591 := bstep (se 1 (by rfl) ⟨1598693, by rfl⟩ : syracuseStep 2131591 = 3197387) B3197387
theorem B2398045 : Blo 2131435 2398045 := bbase (se 3 (by rfl) ⟨449633, by rfl⟩ : syracuseStep 2398045 = 899267) (by norm_num)
theorem B3197393 : Blo 2131435 3197393 := bstep (se 2 (by rfl) ⟨1199022, by rfl⟩ : syracuseStep 3197393 = 2398045) B2398045
theorem B2131595 : Blo 2131435 2131595 := bstep (se 1 (by rfl) ⟨1598696, by rfl⟩ : syracuseStep 2131595 = 3197393) B3197393
theorem B7194149 : Blo 2131435 7194149 := bbase (se 4 (by rfl) ⟨674451, by rfl⟩ : syracuseStep 7194149 = 1348903) (by norm_num)
theorem B4796099 : Blo 2131435 4796099 := bstep (se 1 (by rfl) ⟨3597074, by rfl⟩ : syracuseStep 4796099 = 7194149) B7194149
theorem B3197399 : Blo 2131435 3197399 := bstep (se 1 (by rfl) ⟨2398049, by rfl⟩ : syracuseStep 3197399 = 4796099) B4796099
theorem B2131599 : Blo 2131435 2131599 := bstep (se 1 (by rfl) ⟨1598699, by rfl⟩ : syracuseStep 2131599 = 3197399) B3197399
theorem B3197405 : Blo 2131435 3197405 := bbase (se 3 (by rfl) ⟨599513, by rfl⟩ : syracuseStep 3197405 = 1199027) (by norm_num)
theorem B2131603 : Blo 2131435 2131603 := bstep (se 1 (by rfl) ⟨1598702, by rfl⟩ : syracuseStep 2131603 = 3197405) B3197405
theorem B4796117 : Blo 2131435 4796117 := bbase (se 7 (by rfl) ⟨56204, by rfl⟩ : syracuseStep 4796117 = 112409) (by norm_num)
theorem B3197411 : Blo 2131435 3197411 := bstep (se 1 (by rfl) ⟨2398058, by rfl⟩ : syracuseStep 3197411 = 4796117) B4796117
theorem B2131607 : Blo 2131435 2131607 := bstep (se 1 (by rfl) ⟨1598705, by rfl⟩ : syracuseStep 2131607 = 3197411) B3197411
theorem B14584693 : Blo 2131435 14584693 := bbase (se 5 (by rfl) ⟨683657, by rfl⟩ : syracuseStep 14584693 = 1367315) (by norm_num)
theorem B19446257 : Blo 2131435 19446257 := bstep (se 2 (by rfl) ⟨7292346, by rfl⟩ : syracuseStep 19446257 = 14584693) B14584693
theorem B12964171 : Blo 2131435 12964171 := bstep (se 1 (by rfl) ⟨9723128, by rfl⟩ : syracuseStep 12964171 = 19446257) B19446257
theorem B17285561 : Blo 2131435 17285561 := bstep (se 2 (by rfl) ⟨6482085, by rfl⟩ : syracuseStep 17285561 = 12964171) B12964171
theorem B11523707 : Blo 2131435 11523707 := bstep (se 1 (by rfl) ⟨8642780, by rfl⟩ : syracuseStep 11523707 = 17285561) B17285561
theorem B7682471 : Blo 2131435 7682471 := bstep (se 1 (by rfl) ⟨5761853, by rfl⟩ : syracuseStep 7682471 = 11523707) B11523707
theorem B5121647 : Blo 2131435 5121647 := bstep (se 1 (by rfl) ⟨3841235, by rfl⟩ : syracuseStep 5121647 = 7682471) B7682471
theorem B3414431 : Blo 2131435 3414431 := bstep (se 1 (by rfl) ⟨2560823, by rfl⟩ : syracuseStep 3414431 = 5121647) B5121647
theorem B9105149 : Blo 2131435 9105149 := bstep (se 3 (by rfl) ⟨1707215, by rfl⟩ : syracuseStep 9105149 = 3414431) B3414431
theorem B6070099 : Blo 2131435 6070099 := bstep (se 1 (by rfl) ⟨4552574, by rfl⟩ : syracuseStep 6070099 = 9105149) B9105149
theorem B8093465 : Blo 2131435 8093465 := bstep (se 2 (by rfl) ⟨3035049, by rfl⟩ : syracuseStep 8093465 = 6070099) B6070099
theorem B5395643 : Blo 2131435 5395643 := bstep (se 1 (by rfl) ⟨4046732, by rfl⟩ : syracuseStep 5395643 = 8093465) B8093465
theorem B3597095 : Blo 2131435 3597095 := bstep (se 1 (by rfl) ⟨2697821, by rfl⟩ : syracuseStep 3597095 = 5395643) B5395643
theorem B2398063 : Blo 2131435 2398063 := bstep (se 1 (by rfl) ⟨1798547, by rfl⟩ : syracuseStep 2398063 = 3597095) B3597095
theorem B3197417 : Blo 2131435 3197417 := bstep (se 2 (by rfl) ⟨1199031, by rfl⟩ : syracuseStep 3197417 = 2398063) B2398063
theorem B2131611 : Blo 2131435 2131611 := bstep (se 1 (by rfl) ⟨1598708, by rfl⟩ : syracuseStep 2131611 = 3197417) B3197417
theorem B4321397 : Blo 2131435 4321397 := bbase (se 5 (by rfl) ⟨202565, by rfl⟩ : syracuseStep 4321397 = 405131) (by norm_num)
theorem B11523725 : Blo 2131435 11523725 := bstep (se 3 (by rfl) ⟨2160698, by rfl⟩ : syracuseStep 11523725 = 4321397) B4321397
theorem B7682483 : Blo 2131435 7682483 := bstep (se 1 (by rfl) ⟨5761862, by rfl⟩ : syracuseStep 7682483 = 11523725) B11523725
theorem B20486621 : Blo 2131435 20486621 := bstep (se 3 (by rfl) ⟨3841241, by rfl⟩ : syracuseStep 20486621 = 7682483) B7682483
theorem B13657747 : Blo 2131435 13657747 := bstep (se 1 (by rfl) ⟨10243310, by rfl⟩ : syracuseStep 13657747 = 20486621) B20486621
theorem B18210329 : Blo 2131435 18210329 := bstep (se 2 (by rfl) ⟨6828873, by rfl⟩ : syracuseStep 18210329 = 13657747) B13657747
theorem B12140219 : Blo 2131435 12140219 := bstep (se 1 (by rfl) ⟨9105164, by rfl⟩ : syracuseStep 12140219 = 18210329) B18210329
theorem B8093479 : Blo 2131435 8093479 := bstep (se 1 (by rfl) ⟨6070109, by rfl⟩ : syracuseStep 8093479 = 12140219) B12140219
theorem B10791305 : Blo 2131435 10791305 := bstep (se 2 (by rfl) ⟨4046739, by rfl⟩ : syracuseStep 10791305 = 8093479) B8093479
theorem B7194203 : Blo 2131435 7194203 := bstep (se 1 (by rfl) ⟨5395652, by rfl⟩ : syracuseStep 7194203 = 10791305) B10791305
theorem B4796135 : Blo 2131435 4796135 := bstep (se 1 (by rfl) ⟨3597101, by rfl⟩ : syracuseStep 4796135 = 7194203) B7194203
theorem B3197423 : Blo 2131435 3197423 := bstep (se 1 (by rfl) ⟨2398067, by rfl⟩ : syracuseStep 3197423 = 4796135) B4796135
theorem B2131615 : Blo 2131435 2131615 := bstep (se 1 (by rfl) ⟨1598711, by rfl⟩ : syracuseStep 2131615 = 3197423) B3197423
theorem B3197429 : Blo 2131435 3197429 := bbase (se 5 (by rfl) ⟨149879, by rfl⟩ : syracuseStep 3197429 = 299759) (by norm_num)
theorem B2131619 : Blo 2131435 2131619 := bstep (se 1 (by rfl) ⟨1598714, by rfl⟩ : syracuseStep 2131619 = 3197429) B3197429
theorem B6070133 : Blo 2131435 6070133 := bbase (se 5 (by rfl) ⟨284537, by rfl⟩ : syracuseStep 6070133 = 569075) (by norm_num)
theorem B4046755 : Blo 2131435 4046755 := bstep (se 1 (by rfl) ⟨3035066, by rfl⟩ : syracuseStep 4046755 = 6070133) B6070133
theorem B5395673 : Blo 2131435 5395673 := bstep (se 2 (by rfl) ⟨2023377, by rfl⟩ : syracuseStep 5395673 = 4046755) B4046755
theorem B3597115 : Blo 2131435 3597115 := bstep (se 1 (by rfl) ⟨2697836, by rfl⟩ : syracuseStep 3597115 = 5395673) B5395673
theorem B4796153 : Blo 2131435 4796153 := bstep (se 2 (by rfl) ⟨1798557, by rfl⟩ : syracuseStep 4796153 = 3597115) B3597115
theorem B3197435 : Blo 2131435 3197435 := bstep (se 1 (by rfl) ⟨2398076, by rfl⟩ : syracuseStep 3197435 = 4796153) B4796153
theorem B2131623 : Blo 2131435 2131623 := bstep (se 1 (by rfl) ⟨1598717, by rfl⟩ : syracuseStep 2131623 = 3197435) B3197435
theorem B2398081 : Blo 2131435 2398081 := bbase (se 2 (by rfl) ⟨899280, by rfl⟩ : syracuseStep 2398081 = 1798561) (by norm_num)
theorem B3197441 : Blo 2131435 3197441 := bstep (se 2 (by rfl) ⟨1199040, by rfl⟩ : syracuseStep 3197441 = 2398081) B2398081
theorem B2131627 : Blo 2131435 2131627 := bstep (se 1 (by rfl) ⟨1598720, by rfl⟩ : syracuseStep 2131627 = 3197441) B3197441
theorem B5395693 : Blo 2131435 5395693 := bbase (se 3 (by rfl) ⟨1011692, by rfl⟩ : syracuseStep 5395693 = 2023385) (by norm_num)
theorem B7194257 : Blo 2131435 7194257 := bstep (se 2 (by rfl) ⟨2697846, by rfl⟩ : syracuseStep 7194257 = 5395693) B5395693
theorem B4796171 : Blo 2131435 4796171 := bstep (se 1 (by rfl) ⟨3597128, by rfl⟩ : syracuseStep 4796171 = 7194257) B7194257
theorem B3197447 : Blo 2131435 3197447 := bstep (se 1 (by rfl) ⟨2398085, by rfl⟩ : syracuseStep 3197447 = 4796171) B4796171
theorem B2131631 : Blo 2131435 2131631 := bstep (se 1 (by rfl) ⟨1598723, by rfl⟩ : syracuseStep 2131631 = 3197447) B3197447
theorem B3197453 : Blo 2131435 3197453 := bbase (se 3 (by rfl) ⟨599522, by rfl⟩ : syracuseStep 3197453 = 1199045) (by norm_num)
theorem B2131635 : Blo 2131435 2131635 := bstep (se 1 (by rfl) ⟨1598726, by rfl⟩ : syracuseStep 2131635 = 3197453) B3197453
theorem B4796189 : Blo 2131435 4796189 := bbase (se 3 (by rfl) ⟨899285, by rfl⟩ : syracuseStep 4796189 = 1798571) (by norm_num)
theorem B3197459 : Blo 2131435 3197459 := bstep (se 1 (by rfl) ⟨2398094, by rfl⟩ : syracuseStep 3197459 = 4796189) B4796189
theorem B2131639 : Blo 2131435 2131639 := bstep (se 1 (by rfl) ⟨1598729, by rfl⟩ : syracuseStep 2131639 = 3197459) B3197459
theorem B3597149 : Blo 2131435 3597149 := bbase (se 3 (by rfl) ⟨674465, by rfl⟩ : syracuseStep 3597149 = 1348931) (by norm_num)
theorem B2398099 : Blo 2131435 2398099 := bstep (se 1 (by rfl) ⟨1798574, by rfl⟩ : syracuseStep 2398099 = 3597149) B3597149
theorem B3197465 : Blo 2131435 3197465 := bstep (se 2 (by rfl) ⟨1199049, by rfl⟩ : syracuseStep 3197465 = 2398099) B2398099
theorem B2131643 : Blo 2131435 2131643 := bstep (se 1 (by rfl) ⟨1598732, by rfl⟩ : syracuseStep 2131643 = 3197465) B3197465
theorem B9105301 : Blo 2131435 9105301 := bbase (se 6 (by rfl) ⟨213405, by rfl⟩ : syracuseStep 9105301 = 426811) (by norm_num)
theorem B12140401 : Blo 2131435 12140401 := bstep (se 2 (by rfl) ⟨4552650, by rfl⟩ : syracuseStep 12140401 = 9105301) B9105301
theorem B16187201 : Blo 2131435 16187201 := bstep (se 2 (by rfl) ⟨6070200, by rfl⟩ : syracuseStep 16187201 = 12140401) B12140401
theorem B10791467 : Blo 2131435 10791467 := bstep (se 1 (by rfl) ⟨8093600, by rfl⟩ : syracuseStep 10791467 = 16187201) B16187201
theorem B7194311 : Blo 2131435 7194311 := bstep (se 1 (by rfl) ⟨5395733, by rfl⟩ : syracuseStep 7194311 = 10791467) B10791467
theorem B4796207 : Blo 2131435 4796207 := bstep (se 1 (by rfl) ⟨3597155, by rfl⟩ : syracuseStep 4796207 = 7194311) B7194311
theorem B3197471 : Blo 2131435 3197471 := bstep (se 1 (by rfl) ⟨2398103, by rfl⟩ : syracuseStep 3197471 = 4796207) B4796207
theorem B2131647 : Blo 2131435 2131647 := bstep (se 1 (by rfl) ⟨1598735, by rfl⟩ : syracuseStep 2131647 = 3197471) B3197471
theorem B3197477 : Blo 2131435 3197477 := bbase (se 4 (by rfl) ⟨299763, by rfl⟩ : syracuseStep 3197477 = 599527) (by norm_num)
theorem B2131651 : Blo 2131435 2131651 := bstep (se 1 (by rfl) ⟨1598738, by rfl⟩ : syracuseStep 2131651 = 3197477) B3197477
theorem B2697877 : Blo 2131435 2697877 := bbase (se 6 (by rfl) ⟨63231, by rfl⟩ : syracuseStep 2697877 = 126463) (by norm_num)
theorem B3597169 : Blo 2131435 3597169 := bstep (se 2 (by rfl) ⟨1348938, by rfl⟩ : syracuseStep 3597169 = 2697877) B2697877
theorem B4796225 : Blo 2131435 4796225 := bstep (se 2 (by rfl) ⟨1798584, by rfl⟩ : syracuseStep 4796225 = 3597169) B3597169
theorem B3197483 : Blo 2131435 3197483 := bstep (se 1 (by rfl) ⟨2398112, by rfl⟩ : syracuseStep 3197483 = 4796225) B4796225
theorem B2131655 : Blo 2131435 2131655 := bstep (se 1 (by rfl) ⟨1598741, by rfl⟩ : syracuseStep 2131655 = 3197483) B3197483
theorem B2398117 : Blo 2131435 2398117 := bbase (se 4 (by rfl) ⟨224823, by rfl⟩ : syracuseStep 2398117 = 449647) (by norm_num)
theorem B3197489 : Blo 2131435 3197489 := bstep (se 2 (by rfl) ⟨1199058, by rfl⟩ : syracuseStep 3197489 = 2398117) B2398117
theorem B2131659 : Blo 2131435 2131659 := bstep (se 1 (by rfl) ⟨1598744, by rfl⟩ : syracuseStep 2131659 = 3197489) B3197489
theorem B9723365 : Blo 2131435 9723365 := bbase (se 4 (by rfl) ⟨911565, by rfl⟩ : syracuseStep 9723365 = 1823131) (by norm_num)
theorem B6482243 : Blo 2131435 6482243 := bstep (se 1 (by rfl) ⟨4861682, by rfl⟩ : syracuseStep 6482243 = 9723365) B9723365
theorem B4321495 : Blo 2131435 4321495 := bstep (se 1 (by rfl) ⟨3241121, by rfl⟩ : syracuseStep 4321495 = 6482243) B6482243
theorem B23047973 : Blo 2131435 23047973 := bstep (se 4 (by rfl) ⟨2160747, by rfl⟩ : syracuseStep 23047973 = 4321495) B4321495
theorem B15365315 : Blo 2131435 15365315 := bstep (se 1 (by rfl) ⟨11523986, by rfl⟩ : syracuseStep 15365315 = 23047973) B23047973
theorem B10243543 : Blo 2131435 10243543 := bstep (se 1 (by rfl) ⟨7682657, by rfl⟩ : syracuseStep 10243543 = 15365315) B15365315
theorem B13658057 : Blo 2131435 13658057 := bstep (se 2 (by rfl) ⟨5121771, by rfl⟩ : syracuseStep 13658057 = 10243543) B10243543
theorem B9105371 : Blo 2131435 9105371 := bstep (se 1 (by rfl) ⟨6829028, by rfl⟩ : syracuseStep 9105371 = 13658057) B13658057
theorem B6070247 : Blo 2131435 6070247 := bstep (se 1 (by rfl) ⟨4552685, by rfl⟩ : syracuseStep 6070247 = 9105371) B9105371
theorem B4046831 : Blo 2131435 4046831 := bstep (se 1 (by rfl) ⟨3035123, by rfl⟩ : syracuseStep 4046831 = 6070247) B6070247
theorem B2697887 : Blo 2131435 2697887 := bstep (se 1 (by rfl) ⟨2023415, by rfl⟩ : syracuseStep 2697887 = 4046831) B4046831
theorem B7194365 : Blo 2131435 7194365 := bstep (se 3 (by rfl) ⟨1348943, by rfl⟩ : syracuseStep 7194365 = 2697887) B2697887
theorem B4796243 : Blo 2131435 4796243 := bstep (se 1 (by rfl) ⟨3597182, by rfl⟩ : syracuseStep 4796243 = 7194365) B7194365
theorem B3197495 : Blo 2131435 3197495 := bstep (se 1 (by rfl) ⟨2398121, by rfl⟩ : syracuseStep 3197495 = 4796243) B4796243
theorem B2131663 : Blo 2131435 2131663 := bstep (se 1 (by rfl) ⟨1598747, by rfl⟩ : syracuseStep 2131663 = 3197495) B3197495
theorem B3197501 : Blo 2131435 3197501 := bbase (se 3 (by rfl) ⟨599531, by rfl⟩ : syracuseStep 3197501 = 1199063) (by norm_num)
theorem B2131667 : Blo 2131435 2131667 := bstep (se 1 (by rfl) ⟨1598750, by rfl⟩ : syracuseStep 2131667 = 3197501) B3197501
theorem B4796261 : Blo 2131435 4796261 := bbase (se 4 (by rfl) ⟨449649, by rfl⟩ : syracuseStep 4796261 = 899299) (by norm_num)
theorem B3197507 : Blo 2131435 3197507 := bstep (se 1 (by rfl) ⟨2398130, by rfl⟩ : syracuseStep 3197507 = 4796261) B4796261
theorem B2131671 : Blo 2131435 2131671 := bstep (se 1 (by rfl) ⟨1598753, by rfl⟩ : syracuseStep 2131671 = 3197507) B3197507
theorem B5395805 : Blo 2131435 5395805 := bbase (se 3 (by rfl) ⟨1011713, by rfl⟩ : syracuseStep 5395805 = 2023427) (by norm_num)
theorem B3597203 : Blo 2131435 3597203 := bstep (se 1 (by rfl) ⟨2697902, by rfl⟩ : syracuseStep 3597203 = 5395805) B5395805
theorem B2398135 : Blo 2131435 2398135 := bstep (se 1 (by rfl) ⟨1798601, by rfl⟩ : syracuseStep 2398135 = 3597203) B3597203
theorem B3197513 : Blo 2131435 3197513 := bstep (se 2 (by rfl) ⟨1199067, by rfl⟩ : syracuseStep 3197513 = 2398135) B2398135
theorem B2131675 : Blo 2131435 2131675 := bstep (se 1 (by rfl) ⟨1598756, by rfl⟩ : syracuseStep 2131675 = 3197513) B3197513
theorem B4046861 : Blo 2131435 4046861 := bbase (se 3 (by rfl) ⟨758786, by rfl⟩ : syracuseStep 4046861 = 1517573) (by norm_num)
theorem B10791629 : Blo 2131435 10791629 := bstep (se 3 (by rfl) ⟨2023430, by rfl⟩ : syracuseStep 10791629 = 4046861) B4046861
theorem B7194419 : Blo 2131435 7194419 := bstep (se 1 (by rfl) ⟨5395814, by rfl⟩ : syracuseStep 7194419 = 10791629) B10791629
theorem B4796279 : Blo 2131435 4796279 := bstep (se 1 (by rfl) ⟨3597209, by rfl⟩ : syracuseStep 4796279 = 7194419) B7194419
theorem B3197519 : Blo 2131435 3197519 := bstep (se 1 (by rfl) ⟨2398139, by rfl⟩ : syracuseStep 3197519 = 4796279) B4796279
theorem B2131679 : Blo 2131435 2131679 := bstep (se 1 (by rfl) ⟨1598759, by rfl⟩ : syracuseStep 2131679 = 3197519) B3197519
theorem B3197525 : Blo 2131435 3197525 := bbase (se 8 (by rfl) ⟨18735, by rfl⟩ : syracuseStep 3197525 = 37471) (by norm_num)
theorem B2131683 : Blo 2131435 2131683 := bstep (se 1 (by rfl) ⟨1598762, by rfl⟩ : syracuseStep 2131683 = 3197525) B3197525
theorem B5121829 : Blo 2131435 5121829 := bbase (se 4 (by rfl) ⟨480171, by rfl⟩ : syracuseStep 5121829 = 960343) (by norm_num)
theorem B6829105 : Blo 2131435 6829105 := bstep (se 2 (by rfl) ⟨2560914, by rfl⟩ : syracuseStep 6829105 = 5121829) B5121829
theorem B9105473 : Blo 2131435 9105473 := bstep (se 2 (by rfl) ⟨3414552, by rfl⟩ : syracuseStep 9105473 = 6829105) B6829105
theorem B6070315 : Blo 2131435 6070315 := bstep (se 1 (by rfl) ⟨4552736, by rfl⟩ : syracuseStep 6070315 = 9105473) B9105473
theorem B8093753 : Blo 2131435 8093753 := bstep (se 2 (by rfl) ⟨3035157, by rfl⟩ : syracuseStep 8093753 = 6070315) B6070315
theorem B5395835 : Blo 2131435 5395835 := bstep (se 1 (by rfl) ⟨4046876, by rfl⟩ : syracuseStep 5395835 = 8093753) B8093753
theorem B3597223 : Blo 2131435 3597223 := bstep (se 1 (by rfl) ⟨2697917, by rfl⟩ : syracuseStep 3597223 = 5395835) B5395835
theorem B4796297 : Blo 2131435 4796297 := bstep (se 2 (by rfl) ⟨1798611, by rfl⟩ : syracuseStep 4796297 = 3597223) B3597223
theorem B3197531 : Blo 2131435 3197531 := bstep (se 1 (by rfl) ⟨2398148, by rfl⟩ : syracuseStep 3197531 = 4796297) B4796297
theorem B2131687 : Blo 2131435 2131687 := bstep (se 1 (by rfl) ⟨1598765, by rfl⟩ : syracuseStep 2131687 = 3197531) B3197531
theorem B2398153 : Blo 2131435 2398153 := bbase (se 2 (by rfl) ⟨899307, by rfl⟩ : syracuseStep 2398153 = 1798615) (by norm_num)
theorem B3197537 : Blo 2131435 3197537 := bstep (se 2 (by rfl) ⟨1199076, by rfl⟩ : syracuseStep 3197537 = 2398153) B2398153
theorem B2131691 : Blo 2131435 2131691 := bstep (se 1 (by rfl) ⟨1598768, by rfl⟩ : syracuseStep 2131691 = 3197537) B3197537
theorem B3414565 : Blo 2131435 3414565 := bbase (se 4 (by rfl) ⟨320115, by rfl⟩ : syracuseStep 3414565 = 640231) (by norm_num)
theorem B18211013 : Blo 2131435 18211013 := bstep (se 4 (by rfl) ⟨1707282, by rfl⟩ : syracuseStep 18211013 = 3414565) B3414565
theorem B12140675 : Blo 2131435 12140675 := bstep (se 1 (by rfl) ⟨9105506, by rfl⟩ : syracuseStep 12140675 = 18211013) B18211013
theorem B8093783 : Blo 2131435 8093783 := bstep (se 1 (by rfl) ⟨6070337, by rfl⟩ : syracuseStep 8093783 = 12140675) B12140675
theorem B5395855 : Blo 2131435 5395855 := bstep (se 1 (by rfl) ⟨4046891, by rfl⟩ : syracuseStep 5395855 = 8093783) B8093783
theorem B7194473 : Blo 2131435 7194473 := bstep (se 2 (by rfl) ⟨2697927, by rfl⟩ : syracuseStep 7194473 = 5395855) B5395855
theorem B4796315 : Blo 2131435 4796315 := bstep (se 1 (by rfl) ⟨3597236, by rfl⟩ : syracuseStep 4796315 = 7194473) B7194473
theorem B3197543 : Blo 2131435 3197543 := bstep (se 1 (by rfl) ⟨2398157, by rfl⟩ : syracuseStep 3197543 = 4796315) B4796315
theorem B2131695 : Blo 2131435 2131695 := bstep (se 1 (by rfl) ⟨1598771, by rfl⟩ : syracuseStep 2131695 = 3197543) B3197543
theorem B3197549 : Blo 2131435 3197549 := bbase (se 3 (by rfl) ⟨599540, by rfl⟩ : syracuseStep 3197549 = 1199081) (by norm_num)
theorem B2131699 : Blo 2131435 2131699 := bstep (se 1 (by rfl) ⟨1598774, by rfl⟩ : syracuseStep 2131699 = 3197549) B3197549
theorem B4796333 : Blo 2131435 4796333 := bbase (se 3 (by rfl) ⟨899312, by rfl⟩ : syracuseStep 4796333 = 1798625) (by norm_num)
theorem B3197555 : Blo 2131435 3197555 := bstep (se 1 (by rfl) ⟨2398166, by rfl⟩ : syracuseStep 3197555 = 4796333) B4796333
theorem B2131703 : Blo 2131435 2131703 := bstep (se 1 (by rfl) ⟨1598777, by rfl⟩ : syracuseStep 2131703 = 3197555) B3197555
theorem B6070373 : Blo 2131435 6070373 := bbase (se 4 (by rfl) ⟨569097, by rfl⟩ : syracuseStep 6070373 = 1138195) (by norm_num)
theorem B4046915 : Blo 2131435 4046915 := bstep (se 1 (by rfl) ⟨3035186, by rfl⟩ : syracuseStep 4046915 = 6070373) B6070373
theorem B2697943 : Blo 2131435 2697943 := bstep (se 1 (by rfl) ⟨2023457, by rfl⟩ : syracuseStep 2697943 = 4046915) B4046915
theorem B3597257 : Blo 2131435 3597257 := bstep (se 2 (by rfl) ⟨1348971, by rfl⟩ : syracuseStep 3597257 = 2697943) B2697943
theorem B2398171 : Blo 2131435 2398171 := bstep (se 1 (by rfl) ⟨1798628, by rfl⟩ : syracuseStep 2398171 = 3597257) B3597257
theorem B3197561 : Blo 2131435 3197561 := bstep (se 2 (by rfl) ⟨1199085, by rfl⟩ : syracuseStep 3197561 = 2398171) B2398171
theorem B2131707 : Blo 2131435 2131707 := bstep (se 1 (by rfl) ⟨1598780, by rfl⟩ : syracuseStep 2131707 = 3197561) B3197561
theorem B6153205 : Blo 2131435 6153205 := bbase (se 5 (by rfl) ⟨288431, by rfl⟩ : syracuseStep 6153205 = 576863) (by norm_num)
theorem B8204273 : Blo 2131435 8204273 := bstep (se 2 (by rfl) ⟨3076602, by rfl⟩ : syracuseStep 8204273 = 6153205) B6153205
theorem B5469515 : Blo 2131435 5469515 := bstep (se 1 (by rfl) ⟨4102136, by rfl⟩ : syracuseStep 5469515 = 8204273) B8204273
theorem B3646343 : Blo 2131435 3646343 := bstep (se 1 (by rfl) ⟨2734757, by rfl⟩ : syracuseStep 3646343 = 5469515) B5469515
theorem B9723581 : Blo 2131435 9723581 := bstep (se 3 (by rfl) ⟨1823171, by rfl⟩ : syracuseStep 9723581 = 3646343) B3646343
theorem B6482387 : Blo 2131435 6482387 := bstep (se 1 (by rfl) ⟨4861790, by rfl⟩ : syracuseStep 6482387 = 9723581) B9723581
theorem B17286365 : Blo 2131435 17286365 := bstep (se 3 (by rfl) ⟨3241193, by rfl⟩ : syracuseStep 17286365 = 6482387) B6482387
theorem B11524243 : Blo 2131435 11524243 := bstep (se 1 (by rfl) ⟨8643182, by rfl⟩ : syracuseStep 11524243 = 17286365) B17286365
theorem B15365657 : Blo 2131435 15365657 := bstep (se 2 (by rfl) ⟨5762121, by rfl⟩ : syracuseStep 15365657 = 11524243) B11524243
theorem B40975085 : Blo 2131435 40975085 := bstep (se 3 (by rfl) ⟨7682828, by rfl⟩ : syracuseStep 40975085 = 15365657) B15365657
theorem B27316723 : Blo 2131435 27316723 := bstep (se 1 (by rfl) ⟨20487542, by rfl⟩ : syracuseStep 27316723 = 40975085) B40975085
theorem B36422297 : Blo 2131435 36422297 := bstep (se 2 (by rfl) ⟨13658361, by rfl⟩ : syracuseStep 36422297 = 27316723) B27316723
theorem B24281531 : Blo 2131435 24281531 := bstep (se 1 (by rfl) ⟨18211148, by rfl⟩ : syracuseStep 24281531 = 36422297) B36422297
theorem B16187687 : Blo 2131435 16187687 := bstep (se 1 (by rfl) ⟨12140765, by rfl⟩ : syracuseStep 16187687 = 24281531) B24281531
theorem B10791791 : Blo 2131435 10791791 := bstep (se 1 (by rfl) ⟨8093843, by rfl⟩ : syracuseStep 10791791 = 16187687) B16187687
theorem B7194527 : Blo 2131435 7194527 := bstep (se 1 (by rfl) ⟨5395895, by rfl⟩ : syracuseStep 7194527 = 10791791) B10791791
theorem B4796351 : Blo 2131435 4796351 := bstep (se 1 (by rfl) ⟨3597263, by rfl⟩ : syracuseStep 4796351 = 7194527) B7194527
theorem B3197567 : Blo 2131435 3197567 := bstep (se 1 (by rfl) ⟨2398175, by rfl⟩ : syracuseStep 3197567 = 4796351) B4796351
theorem B2131711 : Blo 2131435 2131711 := bstep (se 1 (by rfl) ⟨1598783, by rfl⟩ : syracuseStep 2131711 = 3197567) B3197567
theorem B3197573 : Blo 2131435 3197573 := bbase (se 4 (by rfl) ⟨299772, by rfl⟩ : syracuseStep 3197573 = 599545) (by norm_num)
theorem B2131715 : Blo 2131435 2131715 := bstep (se 1 (by rfl) ⟨1598786, by rfl⟩ : syracuseStep 2131715 = 3197573) B3197573
theorem B3597277 : Blo 2131435 3597277 := bbase (se 3 (by rfl) ⟨674489, by rfl⟩ : syracuseStep 3597277 = 1348979) (by norm_num)
theorem B4796369 : Blo 2131435 4796369 := bstep (se 2 (by rfl) ⟨1798638, by rfl⟩ : syracuseStep 4796369 = 3597277) B3597277
theorem B3197579 : Blo 2131435 3197579 := bstep (se 1 (by rfl) ⟨2398184, by rfl⟩ : syracuseStep 3197579 = 4796369) B4796369
theorem B2131719 : Blo 2131435 2131719 := bstep (se 1 (by rfl) ⟨1598789, by rfl⟩ : syracuseStep 2131719 = 3197579) B3197579
theorem B2398189 : Blo 2131435 2398189 := bbase (se 3 (by rfl) ⟨449660, by rfl⟩ : syracuseStep 2398189 = 899321) (by norm_num)
theorem B3197585 : Blo 2131435 3197585 := bstep (se 2 (by rfl) ⟨1199094, by rfl⟩ : syracuseStep 3197585 = 2398189) B2398189
theorem B2131723 : Blo 2131435 2131723 := bstep (se 1 (by rfl) ⟨1598792, by rfl⟩ : syracuseStep 2131723 = 3197585) B3197585
theorem B7194581 : Blo 2131435 7194581 := bbase (se 7 (by rfl) ⟨84311, by rfl⟩ : syracuseStep 7194581 = 168623) (by norm_num)
theorem B4796387 : Blo 2131435 4796387 := bstep (se 1 (by rfl) ⟨3597290, by rfl⟩ : syracuseStep 4796387 = 7194581) B7194581
theorem B3197591 : Blo 2131435 3197591 := bstep (se 1 (by rfl) ⟨2398193, by rfl⟩ : syracuseStep 3197591 = 4796387) B4796387
theorem B2131727 : Blo 2131435 2131727 := bstep (se 1 (by rfl) ⟨1598795, by rfl⟩ : syracuseStep 2131727 = 3197591) B3197591
theorem B3197597 : Blo 2131435 3197597 := bbase (se 3 (by rfl) ⟨599549, by rfl⟩ : syracuseStep 3197597 = 1199099) (by norm_num)
theorem B2131731 : Blo 2131435 2131731 := bstep (se 1 (by rfl) ⟨1598798, by rfl⟩ : syracuseStep 2131731 = 3197597) B3197597
theorem B4796405 : Blo 2131435 4796405 := bbase (se 5 (by rfl) ⟨224831, by rfl⟩ : syracuseStep 4796405 = 449663) (by norm_num)
theorem B3197603 : Blo 2131435 3197603 := bstep (se 1 (by rfl) ⟨2398202, by rfl⟩ : syracuseStep 3197603 = 4796405) B4796405
theorem B2131735 : Blo 2131435 2131735 := bstep (se 1 (by rfl) ⟨1598801, by rfl⟩ : syracuseStep 2131735 = 3197603) B3197603
theorem B14784565 : Blo 2131435 14784565 := bbase (se 5 (by rfl) ⟨693026, by rfl⟩ : syracuseStep 14784565 = 1386053) (by norm_num)
theorem B19712753 : Blo 2131435 19712753 := bstep (se 2 (by rfl) ⟨7392282, by rfl⟩ : syracuseStep 19712753 = 14784565) B14784565
theorem B13141835 : Blo 2131435 13141835 := bstep (se 1 (by rfl) ⟨9856376, by rfl⟩ : syracuseStep 13141835 = 19712753) B19712753
theorem B8761223 : Blo 2131435 8761223 := bstep (se 1 (by rfl) ⟨6570917, by rfl⟩ : syracuseStep 8761223 = 13141835) B13141835
theorem B23363261 : Blo 2131435 23363261 := bstep (se 3 (by rfl) ⟨4380611, by rfl⟩ : syracuseStep 23363261 = 8761223) B8761223
theorem B15575507 : Blo 2131435 15575507 := bstep (se 1 (by rfl) ⟨11681630, by rfl⟩ : syracuseStep 15575507 = 23363261) B23363261
theorem B10383671 : Blo 2131435 10383671 := bstep (se 1 (by rfl) ⟨7787753, by rfl⟩ : syracuseStep 10383671 = 15575507) B15575507
theorem B27689789 : Blo 2131435 27689789 := bstep (se 3 (by rfl) ⟨5191835, by rfl⟩ : syracuseStep 27689789 = 10383671) B10383671
theorem B18459859 : Blo 2131435 18459859 := bstep (se 1 (by rfl) ⟨13844894, by rfl⟩ : syracuseStep 18459859 = 27689789) B27689789
theorem B24613145 : Blo 2131435 24613145 := bstep (se 2 (by rfl) ⟨9229929, by rfl⟩ : syracuseStep 24613145 = 18459859) B18459859
theorem B16408763 : Blo 2131435 16408763 := bstep (se 1 (by rfl) ⟨12306572, by rfl⟩ : syracuseStep 16408763 = 24613145) B24613145
theorem B10939175 : Blo 2131435 10939175 := bstep (se 1 (by rfl) ⟨8204381, by rfl⟩ : syracuseStep 10939175 = 16408763) B16408763
theorem B7292783 : Blo 2131435 7292783 := bstep (se 1 (by rfl) ⟨5469587, by rfl⟩ : syracuseStep 7292783 = 10939175) B10939175
theorem B4861855 : Blo 2131435 4861855 := bstep (se 1 (by rfl) ⟨3646391, by rfl⟩ : syracuseStep 4861855 = 7292783) B7292783
theorem B6482473 : Blo 2131435 6482473 := bstep (se 2 (by rfl) ⟨2430927, by rfl⟩ : syracuseStep 6482473 = 4861855) B4861855
theorem B138292757 : Blo 2131435 138292757 := bstep (se 6 (by rfl) ⟨3241236, by rfl⟩ : syracuseStep 138292757 = 6482473) B6482473
theorem B92195171 : Blo 2131435 92195171 := bstep (se 1 (by rfl) ⟨69146378, by rfl⟩ : syracuseStep 92195171 = 138292757) B138292757
theorem B61463447 : Blo 2131435 61463447 := bstep (se 1 (by rfl) ⟨46097585, by rfl⟩ : syracuseStep 61463447 = 92195171) B92195171
theorem B40975631 : Blo 2131435 40975631 := bstep (se 1 (by rfl) ⟨30731723, by rfl⟩ : syracuseStep 40975631 = 61463447) B61463447
theorem B27317087 : Blo 2131435 27317087 := bstep (se 1 (by rfl) ⟨20487815, by rfl⟩ : syracuseStep 27317087 = 40975631) B40975631
theorem B18211391 : Blo 2131435 18211391 := bstep (se 1 (by rfl) ⟨13658543, by rfl⟩ : syracuseStep 18211391 = 27317087) B27317087
theorem B12140927 : Blo 2131435 12140927 := bstep (se 1 (by rfl) ⟨9105695, by rfl⟩ : syracuseStep 12140927 = 18211391) B18211391
theorem B8093951 : Blo 2131435 8093951 := bstep (se 1 (by rfl) ⟨6070463, by rfl⟩ : syracuseStep 8093951 = 12140927) B12140927
theorem B5395967 : Blo 2131435 5395967 := bstep (se 1 (by rfl) ⟨4046975, by rfl⟩ : syracuseStep 5395967 = 8093951) B8093951
theorem B3597311 : Blo 2131435 3597311 := bstep (se 1 (by rfl) ⟨2697983, by rfl⟩ : syracuseStep 3597311 = 5395967) B5395967
theorem B2398207 : Blo 2131435 2398207 := bstep (se 1 (by rfl) ⟨1798655, by rfl⟩ : syracuseStep 2398207 = 3597311) B3597311
theorem B3197609 : Blo 2131435 3197609 := bstep (se 2 (by rfl) ⟨1199103, by rfl⟩ : syracuseStep 3197609 = 2398207) B2398207
theorem B2131739 : Blo 2131435 2131739 := bstep (se 1 (by rfl) ⟨1598804, by rfl⟩ : syracuseStep 2131739 = 3197609) B3197609
theorem B3035237 : Blo 2131435 3035237 := bbase (se 4 (by rfl) ⟨284553, by rfl⟩ : syracuseStep 3035237 = 569107) (by norm_num)
theorem B8093965 : Blo 2131435 8093965 := bstep (se 3 (by rfl) ⟨1517618, by rfl⟩ : syracuseStep 8093965 = 3035237) B3035237
theorem B10791953 : Blo 2131435 10791953 := bstep (se 2 (by rfl) ⟨4046982, by rfl⟩ : syracuseStep 10791953 = 8093965) B8093965
theorem B7194635 : Blo 2131435 7194635 := bstep (se 1 (by rfl) ⟨5395976, by rfl⟩ : syracuseStep 7194635 = 10791953) B10791953
theorem B4796423 : Blo 2131435 4796423 := bstep (se 1 (by rfl) ⟨3597317, by rfl⟩ : syracuseStep 4796423 = 7194635) B7194635
theorem B3197615 : Blo 2131435 3197615 := bstep (se 1 (by rfl) ⟨2398211, by rfl⟩ : syracuseStep 3197615 = 4796423) B4796423
theorem B2131743 : Blo 2131435 2131743 := bstep (se 1 (by rfl) ⟨1598807, by rfl⟩ : syracuseStep 2131743 = 3197615) B3197615
theorem B3197621 : Blo 2131435 3197621 := bbase (se 5 (by rfl) ⟨149888, by rfl⟩ : syracuseStep 3197621 = 299777) (by norm_num)
theorem B2131747 : Blo 2131435 2131747 := bstep (se 1 (by rfl) ⟨1598810, by rfl⟩ : syracuseStep 2131747 = 3197621) B3197621
theorem B5395997 : Blo 2131435 5395997 := bbase (se 3 (by rfl) ⟨1011749, by rfl⟩ : syracuseStep 5395997 = 2023499) (by norm_num)
theorem B3597331 : Blo 2131435 3597331 := bstep (se 1 (by rfl) ⟨2697998, by rfl⟩ : syracuseStep 3597331 = 5395997) B5395997
theorem B4796441 : Blo 2131435 4796441 := bstep (se 2 (by rfl) ⟨1798665, by rfl⟩ : syracuseStep 4796441 = 3597331) B3597331
theorem B3197627 : Blo 2131435 3197627 := bstep (se 1 (by rfl) ⟨2398220, by rfl⟩ : syracuseStep 3197627 = 4796441) B4796441
theorem B2131751 : Blo 2131435 2131751 := bstep (se 1 (by rfl) ⟨1598813, by rfl⟩ : syracuseStep 2131751 = 3197627) B3197627
theorem B2398225 : Blo 2131435 2398225 := bbase (se 2 (by rfl) ⟨899334, by rfl⟩ : syracuseStep 2398225 = 1798669) (by norm_num)
theorem B3197633 : Blo 2131435 3197633 := bstep (se 2 (by rfl) ⟨1199112, by rfl⟩ : syracuseStep 3197633 = 2398225) B2398225
theorem B2131755 : Blo 2131435 2131755 := bstep (se 1 (by rfl) ⟨1598816, by rfl⟩ : syracuseStep 2131755 = 3197633) B3197633
theorem B4047013 : Blo 2131435 4047013 := bbase (se 4 (by rfl) ⟨379407, by rfl⟩ : syracuseStep 4047013 = 758815) (by norm_num)
theorem B5396017 : Blo 2131435 5396017 := bstep (se 2 (by rfl) ⟨2023506, by rfl⟩ : syracuseStep 5396017 = 4047013) B4047013
theorem B7194689 : Blo 2131435 7194689 := bstep (se 2 (by rfl) ⟨2698008, by rfl⟩ : syracuseStep 7194689 = 5396017) B5396017
theorem B4796459 : Blo 2131435 4796459 := bstep (se 1 (by rfl) ⟨3597344, by rfl⟩ : syracuseStep 4796459 = 7194689) B7194689
theorem B3197639 : Blo 2131435 3197639 := bstep (se 1 (by rfl) ⟨2398229, by rfl⟩ : syracuseStep 3197639 = 4796459) B4796459
theorem B2131759 : Blo 2131435 2131759 := bstep (se 1 (by rfl) ⟨1598819, by rfl⟩ : syracuseStep 2131759 = 3197639) B3197639
theorem B3197645 : Blo 2131435 3197645 := bbase (se 3 (by rfl) ⟨599558, by rfl⟩ : syracuseStep 3197645 = 1199117) (by norm_num)
theorem B2131763 : Blo 2131435 2131763 := bstep (se 1 (by rfl) ⟨1598822, by rfl⟩ : syracuseStep 2131763 = 3197645) B3197645
theorem B4796477 : Blo 2131435 4796477 := bbase (se 3 (by rfl) ⟨899339, by rfl⟩ : syracuseStep 4796477 = 1798679) (by norm_num)
theorem B3197651 : Blo 2131435 3197651 := bstep (se 1 (by rfl) ⟨2398238, by rfl⟩ : syracuseStep 3197651 = 4796477) B4796477
theorem B2131767 : Blo 2131435 2131767 := bstep (se 1 (by rfl) ⟨1598825, by rfl⟩ : syracuseStep 2131767 = 3197651) B3197651
theorem B3597365 : Blo 2131435 3597365 := bbase (se 5 (by rfl) ⟨168626, by rfl⟩ : syracuseStep 3597365 = 337253) (by norm_num)
theorem B2398243 : Blo 2131435 2398243 := bstep (se 1 (by rfl) ⟨1798682, by rfl⟩ : syracuseStep 2398243 = 3597365) B3597365
theorem B3197657 : Blo 2131435 3197657 := bstep (se 2 (by rfl) ⟨1199121, by rfl⟩ : syracuseStep 3197657 = 2398243) B2398243
theorem B2131771 : Blo 2131435 2131771 := bstep (se 1 (by rfl) ⟨1598828, by rfl⟩ : syracuseStep 2131771 = 3197657) B3197657
theorem B6070565 : Blo 2131435 6070565 := bbase (se 4 (by rfl) ⟨569115, by rfl⟩ : syracuseStep 6070565 = 1138231) (by norm_num)
theorem B16188173 : Blo 2131435 16188173 := bstep (se 3 (by rfl) ⟨3035282, by rfl⟩ : syracuseStep 16188173 = 6070565) B6070565
theorem B10792115 : Blo 2131435 10792115 := bstep (se 1 (by rfl) ⟨8094086, by rfl⟩ : syracuseStep 10792115 = 16188173) B16188173
theorem B7194743 : Blo 2131435 7194743 := bstep (se 1 (by rfl) ⟨5396057, by rfl⟩ : syracuseStep 7194743 = 10792115) B10792115
theorem B4796495 : Blo 2131435 4796495 := bstep (se 1 (by rfl) ⟨3597371, by rfl⟩ : syracuseStep 4796495 = 7194743) B7194743
theorem B3197663 : Blo 2131435 3197663 := bstep (se 1 (by rfl) ⟨2398247, by rfl⟩ : syracuseStep 3197663 = 4796495) B4796495
theorem B2131775 : Blo 2131435 2131775 := bstep (se 1 (by rfl) ⟨1598831, by rfl⟩ : syracuseStep 2131775 = 3197663) B3197663
theorem B3197669 : Blo 2131435 3197669 := bbase (se 4 (by rfl) ⟨299781, by rfl⟩ : syracuseStep 3197669 = 599563) (by norm_num)
theorem B2131779 : Blo 2131435 2131779 := bstep (se 1 (by rfl) ⟨1598834, by rfl⟩ : syracuseStep 2131779 = 3197669) B3197669
theorem B5122061 : Blo 2131435 5122061 := bbase (se 3 (by rfl) ⟨960386, by rfl⟩ : syracuseStep 5122061 = 1920773) (by norm_num)
theorem B3414707 : Blo 2131435 3414707 := bstep (se 1 (by rfl) ⟨2561030, by rfl⟩ : syracuseStep 3414707 = 5122061) B5122061
theorem B2276471 : Blo 2131435 2276471 := bstep (se 1 (by rfl) ⟨1707353, by rfl⟩ : syracuseStep 2276471 = 3414707) B3414707
theorem B6070589 : Blo 2131435 6070589 := bstep (se 3 (by rfl) ⟨1138235, by rfl⟩ : syracuseStep 6070589 = 2276471) B2276471
theorem B4047059 : Blo 2131435 4047059 := bstep (se 1 (by rfl) ⟨3035294, by rfl⟩ : syracuseStep 4047059 = 6070589) B6070589
theorem B2698039 : Blo 2131435 2698039 := bstep (se 1 (by rfl) ⟨2023529, by rfl⟩ : syracuseStep 2698039 = 4047059) B4047059
theorem B3597385 : Blo 2131435 3597385 := bstep (se 2 (by rfl) ⟨1349019, by rfl⟩ : syracuseStep 3597385 = 2698039) B2698039
theorem B4796513 : Blo 2131435 4796513 := bstep (se 2 (by rfl) ⟨1798692, by rfl⟩ : syracuseStep 4796513 = 3597385) B3597385
theorem B3197675 : Blo 2131435 3197675 := bstep (se 1 (by rfl) ⟨2398256, by rfl⟩ : syracuseStep 3197675 = 4796513) B4796513
theorem B2131783 : Blo 2131435 2131783 := bstep (se 1 (by rfl) ⟨1598837, by rfl⟩ : syracuseStep 2131783 = 3197675) B3197675
theorem B2398261 : Blo 2131435 2398261 := bbase (se 5 (by rfl) ⟨112418, by rfl⟩ : syracuseStep 2398261 = 224837) (by norm_num)
theorem B3197681 : Blo 2131435 3197681 := bstep (se 2 (by rfl) ⟨1199130, by rfl⟩ : syracuseStep 3197681 = 2398261) B2398261
theorem B2131787 : Blo 2131435 2131787 := bstep (se 1 (by rfl) ⟨1598840, by rfl⟩ : syracuseStep 2131787 = 3197681) B3197681
theorem B2698049 : Blo 2131435 2698049 := bbase (se 2 (by rfl) ⟨1011768, by rfl⟩ : syracuseStep 2698049 = 2023537) (by norm_num)
theorem B7194797 : Blo 2131435 7194797 := bstep (se 3 (by rfl) ⟨1349024, by rfl⟩ : syracuseStep 7194797 = 2698049) B2698049
theorem B4796531 : Blo 2131435 4796531 := bstep (se 1 (by rfl) ⟨3597398, by rfl⟩ : syracuseStep 4796531 = 7194797) B7194797
theorem B3197687 : Blo 2131435 3197687 := bstep (se 1 (by rfl) ⟨2398265, by rfl⟩ : syracuseStep 3197687 = 4796531) B4796531
theorem B2131791 : Blo 2131435 2131791 := bstep (se 1 (by rfl) ⟨1598843, by rfl⟩ : syracuseStep 2131791 = 3197687) B3197687
theorem B3197693 : Blo 2131435 3197693 := bbase (se 3 (by rfl) ⟨599567, by rfl⟩ : syracuseStep 3197693 = 1199135) (by norm_num)
theorem B2131795 : Blo 2131435 2131795 := bstep (se 1 (by rfl) ⟨1598846, by rfl⟩ : syracuseStep 2131795 = 3197693) B3197693
theorem B4796549 : Blo 2131435 4796549 := bbase (se 4 (by rfl) ⟨449676, by rfl⟩ : syracuseStep 4796549 = 899353) (by norm_num)
theorem B3197699 : Blo 2131435 3197699 := bstep (se 1 (by rfl) ⟨2398274, by rfl⟩ : syracuseStep 3197699 = 4796549) B4796549
theorem B2131799 : Blo 2131435 2131799 := bstep (se 1 (by rfl) ⟨1598849, by rfl⟩ : syracuseStep 2131799 = 3197699) B3197699
theorem B5122109 : Blo 2131435 5122109 := bbase (se 3 (by rfl) ⟨960395, by rfl⟩ : syracuseStep 5122109 = 1920791) (by norm_num)
theorem B3414739 : Blo 2131435 3414739 := bstep (se 1 (by rfl) ⟨2561054, by rfl⟩ : syracuseStep 3414739 = 5122109) B5122109
theorem B4552985 : Blo 2131435 4552985 := bstep (se 2 (by rfl) ⟨1707369, by rfl⟩ : syracuseStep 4552985 = 3414739) B3414739
theorem B3035323 : Blo 2131435 3035323 := bstep (se 1 (by rfl) ⟨2276492, by rfl⟩ : syracuseStep 3035323 = 4552985) B4552985
theorem B4047097 : Blo 2131435 4047097 := bstep (se 2 (by rfl) ⟨1517661, by rfl⟩ : syracuseStep 4047097 = 3035323) B3035323
theorem B5396129 : Blo 2131435 5396129 := bstep (se 2 (by rfl) ⟨2023548, by rfl⟩ : syracuseStep 5396129 = 4047097) B4047097
theorem B3597419 : Blo 2131435 3597419 := bstep (se 1 (by rfl) ⟨2698064, by rfl⟩ : syracuseStep 3597419 = 5396129) B5396129
theorem B2398279 : Blo 2131435 2398279 := bstep (se 1 (by rfl) ⟨1798709, by rfl⟩ : syracuseStep 2398279 = 3597419) B3597419
theorem B3197705 : Blo 2131435 3197705 := bstep (se 2 (by rfl) ⟨1199139, by rfl⟩ : syracuseStep 3197705 = 2398279) B2398279
theorem B2131803 : Blo 2131435 2131803 := bstep (se 1 (by rfl) ⟨1598852, by rfl⟩ : syracuseStep 2131803 = 3197705) B3197705
theorem B10792277 : Blo 2131435 10792277 := bbase (se 11 (by rfl) ⟨7904, by rfl⟩ : syracuseStep 10792277 = 15809) (by norm_num)
theorem B7194851 : Blo 2131435 7194851 := bstep (se 1 (by rfl) ⟨5396138, by rfl⟩ : syracuseStep 7194851 = 10792277) B10792277
theorem B4796567 : Blo 2131435 4796567 := bstep (se 1 (by rfl) ⟨3597425, by rfl⟩ : syracuseStep 4796567 = 7194851) B7194851
theorem B3197711 : Blo 2131435 3197711 := bstep (se 1 (by rfl) ⟨2398283, by rfl⟩ : syracuseStep 3197711 = 4796567) B4796567
theorem B2131807 : Blo 2131435 2131807 := bstep (se 1 (by rfl) ⟨1598855, by rfl⟩ : syracuseStep 2131807 = 3197711) B3197711
theorem B3197717 : Blo 2131435 3197717 := bbase (se 6 (by rfl) ⟨74946, by rfl⟩ : syracuseStep 3197717 = 149893) (by norm_num)
theorem B2131811 : Blo 2131435 2131811 := bstep (se 1 (by rfl) ⟨1598858, by rfl⟩ : syracuseStep 2131811 = 3197717) B3197717
theorem B8643605 : Blo 2131435 8643605 := bbase (se 6 (by rfl) ⟨202584, by rfl⟩ : syracuseStep 8643605 = 405169) (by norm_num)
theorem B23049613 : Blo 2131435 23049613 := bstep (se 3 (by rfl) ⟨4321802, by rfl⟩ : syracuseStep 23049613 = 8643605) B8643605
theorem B30732817 : Blo 2131435 30732817 := bstep (se 2 (by rfl) ⟨11524806, by rfl⟩ : syracuseStep 30732817 = 23049613) B23049613
theorem B40977089 : Blo 2131435 40977089 := bstep (se 2 (by rfl) ⟨15366408, by rfl⟩ : syracuseStep 40977089 = 30732817) B30732817
theorem B27318059 : Blo 2131435 27318059 := bstep (se 1 (by rfl) ⟨20488544, by rfl⟩ : syracuseStep 27318059 = 40977089) B40977089
theorem B18212039 : Blo 2131435 18212039 := bstep (se 1 (by rfl) ⟨13659029, by rfl⟩ : syracuseStep 18212039 = 27318059) B27318059
theorem B12141359 : Blo 2131435 12141359 := bstep (se 1 (by rfl) ⟨9106019, by rfl⟩ : syracuseStep 12141359 = 18212039) B18212039
theorem B8094239 : Blo 2131435 8094239 := bstep (se 1 (by rfl) ⟨6070679, by rfl⟩ : syracuseStep 8094239 = 12141359) B12141359
theorem B5396159 : Blo 2131435 5396159 := bstep (se 1 (by rfl) ⟨4047119, by rfl⟩ : syracuseStep 5396159 = 8094239) B8094239
theorem B3597439 : Blo 2131435 3597439 := bstep (se 1 (by rfl) ⟨2698079, by rfl⟩ : syracuseStep 3597439 = 5396159) B5396159
theorem B4796585 : Blo 2131435 4796585 := bstep (se 2 (by rfl) ⟨1798719, by rfl⟩ : syracuseStep 4796585 = 3597439) B3597439
theorem B3197723 : Blo 2131435 3197723 := bstep (se 1 (by rfl) ⟨2398292, by rfl⟩ : syracuseStep 3197723 = 4796585) B4796585
theorem B2131815 : Blo 2131435 2131815 := bstep (se 1 (by rfl) ⟨1598861, by rfl⟩ : syracuseStep 2131815 = 3197723) B3197723
theorem B2398297 : Blo 2131435 2398297 := bbase (se 2 (by rfl) ⟨899361, by rfl⟩ : syracuseStep 2398297 = 1798723) (by norm_num)
theorem B3197729 : Blo 2131435 3197729 := bstep (se 2 (by rfl) ⟨1199148, by rfl⟩ : syracuseStep 3197729 = 2398297) B2398297
theorem B2131819 : Blo 2131435 2131819 := bstep (se 1 (by rfl) ⟨1598864, by rfl⟩ : syracuseStep 2131819 = 3197729) B3197729
theorem B6829541 : Blo 2131435 6829541 := bbase (se 4 (by rfl) ⟨640269, by rfl⟩ : syracuseStep 6829541 = 1280539) (by norm_num)
theorem B4553027 : Blo 2131435 4553027 := bstep (se 1 (by rfl) ⟨3414770, by rfl⟩ : syracuseStep 4553027 = 6829541) B6829541
theorem B3035351 : Blo 2131435 3035351 := bstep (se 1 (by rfl) ⟨2276513, by rfl⟩ : syracuseStep 3035351 = 4553027) B4553027
theorem B8094269 : Blo 2131435 8094269 := bstep (se 3 (by rfl) ⟨1517675, by rfl⟩ : syracuseStep 8094269 = 3035351) B3035351
theorem B5396179 : Blo 2131435 5396179 := bstep (se 1 (by rfl) ⟨4047134, by rfl⟩ : syracuseStep 5396179 = 8094269) B8094269
theorem B7194905 : Blo 2131435 7194905 := bstep (se 2 (by rfl) ⟨2698089, by rfl⟩ : syracuseStep 7194905 = 5396179) B5396179
theorem B4796603 : Blo 2131435 4796603 := bstep (se 1 (by rfl) ⟨3597452, by rfl⟩ : syracuseStep 4796603 = 7194905) B7194905
theorem B3197735 : Blo 2131435 3197735 := bstep (se 1 (by rfl) ⟨2398301, by rfl⟩ : syracuseStep 3197735 = 4796603) B4796603
theorem B2131823 : Blo 2131435 2131823 := bstep (se 1 (by rfl) ⟨1598867, by rfl⟩ : syracuseStep 2131823 = 3197735) B3197735
theorem B3197741 : Blo 2131435 3197741 := bbase (se 3 (by rfl) ⟨599576, by rfl⟩ : syracuseStep 3197741 = 1199153) (by norm_num)
theorem B2131827 : Blo 2131435 2131827 := bstep (se 1 (by rfl) ⟨1598870, by rfl⟩ : syracuseStep 2131827 = 3197741) B3197741
theorem B4796621 : Blo 2131435 4796621 := bbase (se 3 (by rfl) ⟨899366, by rfl⟩ : syracuseStep 4796621 = 1798733) (by norm_num)
theorem B3197747 : Blo 2131435 3197747 := bstep (se 1 (by rfl) ⟨2398310, by rfl⟩ : syracuseStep 3197747 = 4796621) B4796621
theorem B2131831 : Blo 2131435 2131831 := bstep (se 1 (by rfl) ⟨1598873, by rfl⟩ : syracuseStep 2131831 = 3197747) B3197747
theorem B2698105 : Blo 2131435 2698105 := bbase (se 2 (by rfl) ⟨1011789, by rfl⟩ : syracuseStep 2698105 = 2023579) (by norm_num)
theorem B3597473 : Blo 2131435 3597473 := bstep (se 2 (by rfl) ⟨1349052, by rfl⟩ : syracuseStep 3597473 = 2698105) B2698105
theorem B2398315 : Blo 2131435 2398315 := bstep (se 1 (by rfl) ⟨1798736, by rfl⟩ : syracuseStep 2398315 = 3597473) B3597473
theorem B3197753 : Blo 2131435 3197753 := bstep (se 2 (by rfl) ⟨1199157, by rfl⟩ : syracuseStep 3197753 = 2398315) B2398315
theorem B2131835 : Blo 2131435 2131835 := bstep (se 1 (by rfl) ⟨1598876, by rfl⟩ : syracuseStep 2131835 = 3197753) B3197753
theorem B15366581 : Blo 2131435 15366581 := bbase (se 5 (by rfl) ⟨720308, by rfl⟩ : syracuseStep 15366581 = 1440617) (by norm_num)
theorem B10244387 : Blo 2131435 10244387 := bstep (se 1 (by rfl) ⟨7683290, by rfl⟩ : syracuseStep 10244387 = 15366581) B15366581
theorem B6829591 : Blo 2131435 6829591 := bstep (se 1 (by rfl) ⟨5122193, by rfl⟩ : syracuseStep 6829591 = 10244387) B10244387
theorem B9106121 : Blo 2131435 9106121 := bstep (se 2 (by rfl) ⟨3414795, by rfl⟩ : syracuseStep 9106121 = 6829591) B6829591
theorem B24282989 : Blo 2131435 24282989 := bstep (se 3 (by rfl) ⟨4553060, by rfl⟩ : syracuseStep 24282989 = 9106121) B9106121
theorem B16188659 : Blo 2131435 16188659 := bstep (se 1 (by rfl) ⟨12141494, by rfl⟩ : syracuseStep 16188659 = 24282989) B24282989
theorem B10792439 : Blo 2131435 10792439 := bstep (se 1 (by rfl) ⟨8094329, by rfl⟩ : syracuseStep 10792439 = 16188659) B16188659
theorem B7194959 : Blo 2131435 7194959 := bstep (se 1 (by rfl) ⟨5396219, by rfl⟩ : syracuseStep 7194959 = 10792439) B10792439
theorem B4796639 : Blo 2131435 4796639 := bstep (se 1 (by rfl) ⟨3597479, by rfl⟩ : syracuseStep 4796639 = 7194959) B7194959
theorem B3197759 : Blo 2131435 3197759 := bstep (se 1 (by rfl) ⟨2398319, by rfl⟩ : syracuseStep 3197759 = 4796639) B4796639
theorem B2131839 : Blo 2131435 2131839 := bstep (se 1 (by rfl) ⟨1598879, by rfl⟩ : syracuseStep 2131839 = 3197759) B3197759
theorem B3197765 : Blo 2131435 3197765 := bbase (se 4 (by rfl) ⟨299790, by rfl⟩ : syracuseStep 3197765 = 599581) (by norm_num)
theorem B2131843 : Blo 2131435 2131843 := bstep (se 1 (by rfl) ⟨1598882, by rfl⟩ : syracuseStep 2131843 = 3197765) B3197765
theorem B3597493 : Blo 2131435 3597493 := bbase (se 5 (by rfl) ⟨168632, by rfl⟩ : syracuseStep 3597493 = 337265) (by norm_num)
theorem B4796657 : Blo 2131435 4796657 := bstep (se 2 (by rfl) ⟨1798746, by rfl⟩ : syracuseStep 4796657 = 3597493) B3597493
theorem B3197771 : Blo 2131435 3197771 := bstep (se 1 (by rfl) ⟨2398328, by rfl⟩ : syracuseStep 3197771 = 4796657) B4796657
theorem B2131847 : Blo 2131435 2131847 := bstep (se 1 (by rfl) ⟨1598885, by rfl⟩ : syracuseStep 2131847 = 3197771) B3197771
theorem B2398333 : Blo 2131435 2398333 := bbase (se 3 (by rfl) ⟨449687, by rfl⟩ : syracuseStep 2398333 = 899375) (by norm_num)
theorem B3197777 : Blo 2131435 3197777 := bstep (se 2 (by rfl) ⟨1199166, by rfl⟩ : syracuseStep 3197777 = 2398333) B2398333
theorem B2131851 : Blo 2131435 2131851 := bstep (se 1 (by rfl) ⟨1598888, by rfl⟩ : syracuseStep 2131851 = 3197777) B3197777
theorem B7195013 : Blo 2131435 7195013 := bbase (se 4 (by rfl) ⟨674532, by rfl⟩ : syracuseStep 7195013 = 1349065) (by norm_num)
theorem B4796675 : Blo 2131435 4796675 := bstep (se 1 (by rfl) ⟨3597506, by rfl⟩ : syracuseStep 4796675 = 7195013) B7195013
theorem B3197783 : Blo 2131435 3197783 := bstep (se 1 (by rfl) ⟨2398337, by rfl⟩ : syracuseStep 3197783 = 4796675) B4796675
theorem B2131855 : Blo 2131435 2131855 := bstep (se 1 (by rfl) ⟨1598891, by rfl⟩ : syracuseStep 2131855 = 3197783) B3197783
theorem B3197789 : Blo 2131435 3197789 := bbase (se 3 (by rfl) ⟨599585, by rfl⟩ : syracuseStep 3197789 = 1199171) (by norm_num)
theorem B2131859 : Blo 2131435 2131859 := bstep (se 1 (by rfl) ⟨1598894, by rfl⟩ : syracuseStep 2131859 = 3197789) B3197789
theorem B4796693 : Blo 2131435 4796693 := bbase (se 6 (by rfl) ⟨112422, by rfl⟩ : syracuseStep 4796693 = 224845) (by norm_num)
theorem B3197795 : Blo 2131435 3197795 := bstep (se 1 (by rfl) ⟨2398346, by rfl⟩ : syracuseStep 3197795 = 4796693) B4796693
theorem B2131863 : Blo 2131435 2131863 := bstep (se 1 (by rfl) ⟨1598897, by rfl⟩ : syracuseStep 2131863 = 3197795) B3197795
theorem B8094437 : Blo 2131435 8094437 := bbase (se 4 (by rfl) ⟨758853, by rfl⟩ : syracuseStep 8094437 = 1517707) (by norm_num)
theorem B5396291 : Blo 2131435 5396291 := bstep (se 1 (by rfl) ⟨4047218, by rfl⟩ : syracuseStep 5396291 = 8094437) B8094437
theorem B3597527 : Blo 2131435 3597527 := bstep (se 1 (by rfl) ⟨2698145, by rfl⟩ : syracuseStep 3597527 = 5396291) B5396291
theorem B2398351 : Blo 2131435 2398351 := bstep (se 1 (by rfl) ⟨1798763, by rfl⟩ : syracuseStep 2398351 = 3597527) B3597527
theorem B3197801 : Blo 2131435 3197801 := bstep (se 2 (by rfl) ⟨1199175, by rfl⟩ : syracuseStep 3197801 = 2398351) B2398351
theorem B2131867 : Blo 2131435 2131867 := bstep (se 1 (by rfl) ⟨1598900, by rfl⟩ : syracuseStep 2131867 = 3197801) B3197801
theorem B4102445 : Blo 2131435 4102445 := bbase (se 3 (by rfl) ⟨769208, by rfl⟩ : syracuseStep 4102445 = 1538417) (by norm_num)
theorem B10939853 : Blo 2131435 10939853 := bstep (se 3 (by rfl) ⟨2051222, by rfl⟩ : syracuseStep 10939853 = 4102445) B4102445
theorem B7293235 : Blo 2131435 7293235 := bstep (se 1 (by rfl) ⟨5469926, by rfl⟩ : syracuseStep 7293235 = 10939853) B10939853
theorem B9724313 : Blo 2131435 9724313 := bstep (se 2 (by rfl) ⟨3646617, by rfl⟩ : syracuseStep 9724313 = 7293235) B7293235
theorem B25931501 : Blo 2131435 25931501 := bstep (se 3 (by rfl) ⟨4862156, by rfl⟩ : syracuseStep 25931501 = 9724313) B9724313
theorem B17287667 : Blo 2131435 17287667 := bstep (se 1 (by rfl) ⟨12965750, by rfl⟩ : syracuseStep 17287667 = 25931501) B25931501
theorem B11525111 : Blo 2131435 11525111 := bstep (se 1 (by rfl) ⟨8643833, by rfl⟩ : syracuseStep 11525111 = 17287667) B17287667
theorem B7683407 : Blo 2131435 7683407 := bstep (se 1 (by rfl) ⟨5762555, by rfl⟩ : syracuseStep 7683407 = 11525111) B11525111
theorem B5122271 : Blo 2131435 5122271 := bstep (se 1 (by rfl) ⟨3841703, by rfl⟩ : syracuseStep 5122271 = 7683407) B7683407
theorem B3414847 : Blo 2131435 3414847 := bstep (se 1 (by rfl) ⟨2561135, by rfl⟩ : syracuseStep 3414847 = 5122271) B5122271
theorem B4553129 : Blo 2131435 4553129 := bstep (se 2 (by rfl) ⟨1707423, by rfl⟩ : syracuseStep 4553129 = 3414847) B3414847
theorem B12141677 : Blo 2131435 12141677 := bstep (se 3 (by rfl) ⟨2276564, by rfl⟩ : syracuseStep 12141677 = 4553129) B4553129
theorem B8094451 : Blo 2131435 8094451 := bstep (se 1 (by rfl) ⟨6070838, by rfl⟩ : syracuseStep 8094451 = 12141677) B12141677
theorem B10792601 : Blo 2131435 10792601 := bstep (se 2 (by rfl) ⟨4047225, by rfl⟩ : syracuseStep 10792601 = 8094451) B8094451
theorem B7195067 : Blo 2131435 7195067 := bstep (se 1 (by rfl) ⟨5396300, by rfl⟩ : syracuseStep 7195067 = 10792601) B10792601
theorem B4796711 : Blo 2131435 4796711 := bstep (se 1 (by rfl) ⟨3597533, by rfl⟩ : syracuseStep 4796711 = 7195067) B7195067
theorem B3197807 : Blo 2131435 3197807 := bstep (se 1 (by rfl) ⟨2398355, by rfl⟩ : syracuseStep 3197807 = 4796711) B4796711
theorem B2131871 : Blo 2131435 2131871 := bstep (se 1 (by rfl) ⟨1598903, by rfl⟩ : syracuseStep 2131871 = 3197807) B3197807
theorem B3197813 : Blo 2131435 3197813 := bbase (se 5 (by rfl) ⟨149897, by rfl⟩ : syracuseStep 3197813 = 299795) (by norm_num)
theorem B2131875 : Blo 2131435 2131875 := bstep (se 1 (by rfl) ⟨1598906, by rfl⟩ : syracuseStep 2131875 = 3197813) B3197813
theorem B6237653 : Blo 2131435 6237653 := bbase (se 7 (by rfl) ⟨73097, by rfl⟩ : syracuseStep 6237653 = 146195) (by norm_num)
theorem B66534965 : Blo 2131435 66534965 := bstep (se 5 (by rfl) ⟨3118826, by rfl⟩ : syracuseStep 66534965 = 6237653) B6237653
theorem B44356643 : Blo 2131435 44356643 := bstep (se 1 (by rfl) ⟨33267482, by rfl⟩ : syracuseStep 44356643 = 66534965) B66534965
theorem B29571095 : Blo 2131435 29571095 := bstep (se 1 (by rfl) ⟨22178321, by rfl⟩ : syracuseStep 29571095 = 44356643) B44356643
theorem B19714063 : Blo 2131435 19714063 := bstep (se 1 (by rfl) ⟨14785547, by rfl⟩ : syracuseStep 19714063 = 29571095) B29571095
theorem B26285417 : Blo 2131435 26285417 := bstep (se 2 (by rfl) ⟨9857031, by rfl⟩ : syracuseStep 26285417 = 19714063) B19714063
theorem B17523611 : Blo 2131435 17523611 := bstep (se 1 (by rfl) ⟨13142708, by rfl⟩ : syracuseStep 17523611 = 26285417) B26285417
theorem B11682407 : Blo 2131435 11682407 := bstep (se 1 (by rfl) ⟨8761805, by rfl⟩ : syracuseStep 11682407 = 17523611) B17523611
theorem B31153085 : Blo 2131435 31153085 := bstep (se 3 (by rfl) ⟨5841203, by rfl⟩ : syracuseStep 31153085 = 11682407) B11682407
theorem B20768723 : Blo 2131435 20768723 := bstep (se 1 (by rfl) ⟨15576542, by rfl⟩ : syracuseStep 20768723 = 31153085) B31153085
theorem B13845815 : Blo 2131435 13845815 := bstep (se 1 (by rfl) ⟨10384361, by rfl⟩ : syracuseStep 13845815 = 20768723) B20768723
theorem B9230543 : Blo 2131435 9230543 := bstep (se 1 (by rfl) ⟨6922907, by rfl⟩ : syracuseStep 9230543 = 13845815) B13845815
theorem B6153695 : Blo 2131435 6153695 := bstep (se 1 (by rfl) ⟨4615271, by rfl⟩ : syracuseStep 6153695 = 9230543) B9230543
theorem B4102463 : Blo 2131435 4102463 := bstep (se 1 (by rfl) ⟨3076847, by rfl⟩ : syracuseStep 4102463 = 6153695) B6153695
theorem B2734975 : Blo 2131435 2734975 := bstep (se 1 (by rfl) ⟨2051231, by rfl⟩ : syracuseStep 2734975 = 4102463) B4102463
theorem B3646633 : Blo 2131435 3646633 := bstep (se 2 (by rfl) ⟨1367487, by rfl⟩ : syracuseStep 3646633 = 2734975) B2734975
theorem B4862177 : Blo 2131435 4862177 := bstep (se 2 (by rfl) ⟨1823316, by rfl⟩ : syracuseStep 4862177 = 3646633) B3646633
theorem B3241451 : Blo 2131435 3241451 := bstep (se 1 (by rfl) ⟨2431088, by rfl⟩ : syracuseStep 3241451 = 4862177) B4862177
theorem B2160967 : Blo 2131435 2160967 := bstep (se 1 (by rfl) ⟨1620725, by rfl⟩ : syracuseStep 2160967 = 3241451) B3241451
theorem B2881289 : Blo 2131435 2881289 := bstep (se 2 (by rfl) ⟨1080483, by rfl⟩ : syracuseStep 2881289 = 2160967) B2160967
theorem B7683437 : Blo 2131435 7683437 := bstep (se 3 (by rfl) ⟨1440644, by rfl⟩ : syracuseStep 7683437 = 2881289) B2881289
theorem B5122291 : Blo 2131435 5122291 := bstep (se 1 (by rfl) ⟨3841718, by rfl⟩ : syracuseStep 5122291 = 7683437) B7683437
theorem B6829721 : Blo 2131435 6829721 := bstep (se 2 (by rfl) ⟨2561145, by rfl⟩ : syracuseStep 6829721 = 5122291) B5122291
theorem B4553147 : Blo 2131435 4553147 := bstep (se 1 (by rfl) ⟨3414860, by rfl⟩ : syracuseStep 4553147 = 6829721) B6829721
theorem B3035431 : Blo 2131435 3035431 := bstep (se 1 (by rfl) ⟨2276573, by rfl⟩ : syracuseStep 3035431 = 4553147) B4553147
theorem B4047241 : Blo 2131435 4047241 := bstep (se 2 (by rfl) ⟨1517715, by rfl⟩ : syracuseStep 4047241 = 3035431) B3035431
theorem B5396321 : Blo 2131435 5396321 := bstep (se 2 (by rfl) ⟨2023620, by rfl⟩ : syracuseStep 5396321 = 4047241) B4047241
theorem B3597547 : Blo 2131435 3597547 := bstep (se 1 (by rfl) ⟨2698160, by rfl⟩ : syracuseStep 3597547 = 5396321) B5396321
theorem B4796729 : Blo 2131435 4796729 := bstep (se 2 (by rfl) ⟨1798773, by rfl⟩ : syracuseStep 4796729 = 3597547) B3597547
theorem B3197819 : Blo 2131435 3197819 := bstep (se 1 (by rfl) ⟨2398364, by rfl⟩ : syracuseStep 3197819 = 4796729) B4796729
theorem B2131879 : Blo 2131435 2131879 := bstep (se 1 (by rfl) ⟨1598909, by rfl⟩ : syracuseStep 2131879 = 3197819) B3197819
theorem B2398369 : Blo 2131435 2398369 := bbase (se 2 (by rfl) ⟨899388, by rfl⟩ : syracuseStep 2398369 = 1798777) (by norm_num)
theorem B3197825 : Blo 2131435 3197825 := bstep (se 2 (by rfl) ⟨1199184, by rfl⟩ : syracuseStep 3197825 = 2398369) B2398369
theorem B2131883 : Blo 2131435 2131883 := bstep (se 1 (by rfl) ⟨1598912, by rfl⟩ : syracuseStep 2131883 = 3197825) B3197825
theorem B5396341 : Blo 2131435 5396341 := bbase (se 5 (by rfl) ⟨252953, by rfl⟩ : syracuseStep 5396341 = 505907) (by norm_num)
theorem B7195121 : Blo 2131435 7195121 := bstep (se 2 (by rfl) ⟨2698170, by rfl⟩ : syracuseStep 7195121 = 5396341) B5396341
theorem B4796747 : Blo 2131435 4796747 := bstep (se 1 (by rfl) ⟨3597560, by rfl⟩ : syracuseStep 4796747 = 7195121) B7195121
theorem B3197831 : Blo 2131435 3197831 := bstep (se 1 (by rfl) ⟨2398373, by rfl⟩ : syracuseStep 3197831 = 4796747) B4796747
theorem B2131887 : Blo 2131435 2131887 := bstep (se 1 (by rfl) ⟨1598915, by rfl⟩ : syracuseStep 2131887 = 3197831) B3197831
theorem B3197837 : Blo 2131435 3197837 := bbase (se 3 (by rfl) ⟨599594, by rfl⟩ : syracuseStep 3197837 = 1199189) (by norm_num)
theorem B2131891 : Blo 2131435 2131891 := bstep (se 1 (by rfl) ⟨1598918, by rfl⟩ : syracuseStep 2131891 = 3197837) B3197837
theorem B4796765 : Blo 2131435 4796765 := bbase (se 3 (by rfl) ⟨899393, by rfl⟩ : syracuseStep 4796765 = 1798787) (by norm_num)
theorem B3197843 : Blo 2131435 3197843 := bstep (se 1 (by rfl) ⟨2398382, by rfl⟩ : syracuseStep 3197843 = 4796765) B4796765
theorem B2131895 : Blo 2131435 2131895 := bstep (se 1 (by rfl) ⟨1598921, by rfl⟩ : syracuseStep 2131895 = 3197843) B3197843
theorem B3597581 : Blo 2131435 3597581 := bbase (se 3 (by rfl) ⟨674546, by rfl⟩ : syracuseStep 3597581 = 1349093) (by norm_num)
theorem B2398387 : Blo 2131435 2398387 := bstep (se 1 (by rfl) ⟨1798790, by rfl⟩ : syracuseStep 2398387 = 3597581) B3597581
theorem B3197849 : Blo 2131435 3197849 := bstep (se 2 (by rfl) ⟨1199193, by rfl⟩ : syracuseStep 3197849 = 2398387) B2398387
theorem B2131899 : Blo 2131435 2131899 := bstep (se 1 (by rfl) ⟨1598924, by rfl⟩ : syracuseStep 2131899 = 3197849) B3197849
theorem B18212789 : Blo 2131435 18212789 := bbase (se 5 (by rfl) ⟨853724, by rfl⟩ : syracuseStep 18212789 = 1707449) (by norm_num)
theorem B12141859 : Blo 2131435 12141859 := bstep (se 1 (by rfl) ⟨9106394, by rfl⟩ : syracuseStep 12141859 = 18212789) B18212789
theorem B16189145 : Blo 2131435 16189145 := bstep (se 2 (by rfl) ⟨6070929, by rfl⟩ : syracuseStep 16189145 = 12141859) B12141859
theorem B10792763 : Blo 2131435 10792763 := bstep (se 1 (by rfl) ⟨8094572, by rfl⟩ : syracuseStep 10792763 = 16189145) B16189145
theorem B7195175 : Blo 2131435 7195175 := bstep (se 1 (by rfl) ⟨5396381, by rfl⟩ : syracuseStep 7195175 = 10792763) B10792763
theorem B4796783 : Blo 2131435 4796783 := bstep (se 1 (by rfl) ⟨3597587, by rfl⟩ : syracuseStep 4796783 = 7195175) B7195175
theorem B3197855 : Blo 2131435 3197855 := bstep (se 1 (by rfl) ⟨2398391, by rfl⟩ : syracuseStep 3197855 = 4796783) B4796783
theorem B2131903 : Blo 2131435 2131903 := bstep (se 1 (by rfl) ⟨1598927, by rfl⟩ : syracuseStep 2131903 = 3197855) B3197855
theorem B3197861 : Blo 2131435 3197861 := bbase (se 4 (by rfl) ⟨299799, by rfl⟩ : syracuseStep 3197861 = 599599) (by norm_num)
theorem B2131907 : Blo 2131435 2131907 := bstep (se 1 (by rfl) ⟨1598930, by rfl⟩ : syracuseStep 2131907 = 3197861) B3197861
theorem B2698201 : Blo 2131435 2698201 := bbase (se 2 (by rfl) ⟨1011825, by rfl⟩ : syracuseStep 2698201 = 2023651) (by norm_num)
theorem B3597601 : Blo 2131435 3597601 := bstep (se 2 (by rfl) ⟨1349100, by rfl⟩ : syracuseStep 3597601 = 2698201) B2698201
theorem B4796801 : Blo 2131435 4796801 := bstep (se 2 (by rfl) ⟨1798800, by rfl⟩ : syracuseStep 4796801 = 3597601) B3597601
theorem B3197867 : Blo 2131435 3197867 := bstep (se 1 (by rfl) ⟨2398400, by rfl⟩ : syracuseStep 3197867 = 4796801) B4796801
theorem B2131911 : Blo 2131435 2131911 := bstep (se 1 (by rfl) ⟨1598933, by rfl⟩ : syracuseStep 2131911 = 3197867) B3197867
theorem B2398405 : Blo 2131435 2398405 := bbase (se 4 (by rfl) ⟨224850, by rfl⟩ : syracuseStep 2398405 = 449701) (by norm_num)
theorem B3197873 : Blo 2131435 3197873 := bstep (se 2 (by rfl) ⟨1199202, by rfl⟩ : syracuseStep 3197873 = 2398405) B2398405
theorem B2131915 : Blo 2131435 2131915 := bstep (se 1 (by rfl) ⟨1598936, by rfl⟩ : syracuseStep 2131915 = 3197873) B3197873
theorem B4047317 : Blo 2131435 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B2698211 : Blo 2131435 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B7195229 : Blo 2131435 7195229 := bstep (se 3 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 7195229 = 2698211) B2698211
theorem B4796819 : Blo 2131435 4796819 := bstep (se 1 (by rfl) ⟨3597614, by rfl⟩ : syracuseStep 4796819 = 7195229) B7195229
theorem B3197879 : Blo 2131435 3197879 := bstep (se 1 (by rfl) ⟨2398409, by rfl⟩ : syracuseStep 3197879 = 4796819) B4796819
theorem B2131919 : Blo 2131435 2131919 := bstep (se 1 (by rfl) ⟨1598939, by rfl⟩ : syracuseStep 2131919 = 3197879) B3197879
theorem B3197885 : Blo 2131435 3197885 := bbase (se 3 (by rfl) ⟨599603, by rfl⟩ : syracuseStep 3197885 = 1199207) (by norm_num)
theorem B2131923 : Blo 2131435 2131923 := bstep (se 1 (by rfl) ⟨1598942, by rfl⟩ : syracuseStep 2131923 = 3197885) B3197885
theorem B4796837 : Blo 2131435 4796837 := bbase (se 4 (by rfl) ⟨449703, by rfl⟩ : syracuseStep 4796837 = 899407) (by norm_num)
theorem B3197891 : Blo 2131435 3197891 := bstep (se 1 (by rfl) ⟨2398418, by rfl⟩ : syracuseStep 3197891 = 4796837) B4796837
theorem B2131927 : Blo 2131435 2131927 := bstep (se 1 (by rfl) ⟨1598945, by rfl⟩ : syracuseStep 2131927 = 3197891) B3197891
theorem B5396453 : Blo 2131435 5396453 := bbase (se 4 (by rfl) ⟨505917, by rfl⟩ : syracuseStep 5396453 = 1011835) (by norm_num)
theorem B3597635 : Blo 2131435 3597635 := bstep (se 1 (by rfl) ⟨2698226, by rfl⟩ : syracuseStep 3597635 = 5396453) B5396453
theorem B2398423 : Blo 2131435 2398423 := bstep (se 1 (by rfl) ⟨1798817, by rfl⟩ : syracuseStep 2398423 = 3597635) B3597635
theorem B3197897 : Blo 2131435 3197897 := bstep (se 2 (by rfl) ⟨1199211, by rfl⟩ : syracuseStep 3197897 = 2398423) B2398423
theorem B2131931 : Blo 2131435 2131931 := bstep (se 1 (by rfl) ⟨1598948, by rfl⟩ : syracuseStep 2131931 = 3197897) B3197897
theorem B2276633 : Blo 2131435 2276633 := bbase (se 2 (by rfl) ⟨853737, by rfl⟩ : syracuseStep 2276633 = 1707475) (by norm_num)
theorem B6071021 : Blo 2131435 6071021 := bstep (se 3 (by rfl) ⟨1138316, by rfl⟩ : syracuseStep 6071021 = 2276633) B2276633
theorem B4047347 : Blo 2131435 4047347 := bstep (se 1 (by rfl) ⟨3035510, by rfl⟩ : syracuseStep 4047347 = 6071021) B6071021
theorem B10792925 : Blo 2131435 10792925 := bstep (se 3 (by rfl) ⟨2023673, by rfl⟩ : syracuseStep 10792925 = 4047347) B4047347
theorem B7195283 : Blo 2131435 7195283 := bstep (se 1 (by rfl) ⟨5396462, by rfl⟩ : syracuseStep 7195283 = 10792925) B10792925
theorem B4796855 : Blo 2131435 4796855 := bstep (se 1 (by rfl) ⟨3597641, by rfl⟩ : syracuseStep 4796855 = 7195283) B7195283
theorem B3197903 : Blo 2131435 3197903 := bstep (se 1 (by rfl) ⟨2398427, by rfl⟩ : syracuseStep 3197903 = 4796855) B4796855
theorem B2131935 : Blo 2131435 2131935 := bstep (se 1 (by rfl) ⟨1598951, by rfl⟩ : syracuseStep 2131935 = 3197903) B3197903
theorem B3197909 : Blo 2131435 3197909 := bbase (se 7 (by rfl) ⟨37475, by rfl⟩ : syracuseStep 3197909 = 74951) (by norm_num)
theorem B2131939 : Blo 2131435 2131939 := bstep (se 1 (by rfl) ⟨1598954, by rfl⟩ : syracuseStep 2131939 = 3197909) B3197909
theorem B8094725 : Blo 2131435 8094725 := bbase (se 4 (by rfl) ⟨758880, by rfl⟩ : syracuseStep 8094725 = 1517761) (by norm_num)
theorem B5396483 : Blo 2131435 5396483 := bstep (se 1 (by rfl) ⟨4047362, by rfl⟩ : syracuseStep 5396483 = 8094725) B8094725
theorem B3597655 : Blo 2131435 3597655 := bstep (se 1 (by rfl) ⟨2698241, by rfl⟩ : syracuseStep 3597655 = 5396483) B5396483
theorem B4796873 : Blo 2131435 4796873 := bstep (se 2 (by rfl) ⟨1798827, by rfl⟩ : syracuseStep 4796873 = 3597655) B3597655
theorem B3197915 : Blo 2131435 3197915 := bstep (se 1 (by rfl) ⟨2398436, by rfl⟩ : syracuseStep 3197915 = 4796873) B4796873
theorem B2131943 : Blo 2131435 2131943 := bstep (se 1 (by rfl) ⟨1598957, by rfl⟩ : syracuseStep 2131943 = 3197915) B3197915
theorem B2398441 : Blo 2131435 2398441 := bbase (se 2 (by rfl) ⟨899415, by rfl⟩ : syracuseStep 2398441 = 1798831) (by norm_num)
theorem B3197921 : Blo 2131435 3197921 := bstep (se 2 (by rfl) ⟨1199220, by rfl⟩ : syracuseStep 3197921 = 2398441) B2398441
theorem B2131947 : Blo 2131435 2131947 := bstep (se 1 (by rfl) ⟨1598960, by rfl⟩ : syracuseStep 2131947 = 3197921) B3197921
theorem B12142133 : Blo 2131435 12142133 := bbase (se 5 (by rfl) ⟨569162, by rfl⟩ : syracuseStep 12142133 = 1138325) (by norm_num)
theorem B8094755 : Blo 2131435 8094755 := bstep (se 1 (by rfl) ⟨6071066, by rfl⟩ : syracuseStep 8094755 = 12142133) B12142133
theorem B5396503 : Blo 2131435 5396503 := bstep (se 1 (by rfl) ⟨4047377, by rfl⟩ : syracuseStep 5396503 = 8094755) B8094755
theorem B7195337 : Blo 2131435 7195337 := bstep (se 2 (by rfl) ⟨2698251, by rfl⟩ : syracuseStep 7195337 = 5396503) B5396503
theorem B4796891 : Blo 2131435 4796891 := bstep (se 1 (by rfl) ⟨3597668, by rfl⟩ : syracuseStep 4796891 = 7195337) B7195337
theorem B3197927 : Blo 2131435 3197927 := bstep (se 1 (by rfl) ⟨2398445, by rfl⟩ : syracuseStep 3197927 = 4796891) B4796891
theorem B2131951 : Blo 2131435 2131951 := bstep (se 1 (by rfl) ⟨1598963, by rfl⟩ : syracuseStep 2131951 = 3197927) B3197927
theorem B3197933 : Blo 2131435 3197933 := bbase (se 3 (by rfl) ⟨599612, by rfl⟩ : syracuseStep 3197933 = 1199225) (by norm_num)
theorem B2131955 : Blo 2131435 2131955 := bstep (se 1 (by rfl) ⟨1598966, by rfl⟩ : syracuseStep 2131955 = 3197933) B3197933
theorem B4796909 : Blo 2131435 4796909 := bbase (se 3 (by rfl) ⟨899420, by rfl⟩ : syracuseStep 4796909 = 1798841) (by norm_num)
theorem B3197939 : Blo 2131435 3197939 := bstep (se 1 (by rfl) ⟨2398454, by rfl⟩ : syracuseStep 3197939 = 4796909) B4796909
theorem B2131959 : Blo 2131435 2131959 := bstep (se 1 (by rfl) ⟨1598969, by rfl⟩ : syracuseStep 2131959 = 3197939) B3197939
theorem B7393061 : Blo 2131435 7393061 := bbase (se 4 (by rfl) ⟨693099, by rfl⟩ : syracuseStep 7393061 = 1386199) (by norm_num)
theorem B4928707 : Blo 2131435 4928707 := bstep (se 1 (by rfl) ⟨3696530, by rfl⟩ : syracuseStep 4928707 = 7393061) B7393061
theorem B26286437 : Blo 2131435 26286437 := bstep (se 4 (by rfl) ⟨2464353, by rfl⟩ : syracuseStep 26286437 = 4928707) B4928707
theorem B17524291 : Blo 2131435 17524291 := bstep (se 1 (by rfl) ⟨13143218, by rfl⟩ : syracuseStep 17524291 = 26286437) B26286437
theorem B23365721 : Blo 2131435 23365721 := bstep (se 2 (by rfl) ⟨8762145, by rfl⟩ : syracuseStep 23365721 = 17524291) B17524291
theorem B15577147 : Blo 2131435 15577147 := bstep (se 1 (by rfl) ⟨11682860, by rfl⟩ : syracuseStep 15577147 = 23365721) B23365721
theorem B20769529 : Blo 2131435 20769529 := bstep (se 2 (by rfl) ⟨7788573, by rfl⟩ : syracuseStep 20769529 = 15577147) B15577147
theorem B27692705 : Blo 2131435 27692705 := bstep (se 2 (by rfl) ⟨10384764, by rfl⟩ : syracuseStep 27692705 = 20769529) B20769529
theorem B73847213 : Blo 2131435 73847213 := bstep (se 3 (by rfl) ⟨13846352, by rfl⟩ : syracuseStep 73847213 = 27692705) B27692705
theorem B49231475 : Blo 2131435 49231475 := bstep (se 1 (by rfl) ⟨36923606, by rfl⟩ : syracuseStep 49231475 = 73847213) B73847213
theorem B32820983 : Blo 2131435 32820983 := bstep (se 1 (by rfl) ⟨24615737, by rfl⟩ : syracuseStep 32820983 = 49231475) B49231475
theorem B21880655 : Blo 2131435 21880655 := bstep (se 1 (by rfl) ⟨16410491, by rfl⟩ : syracuseStep 21880655 = 32820983) B32820983
theorem B14587103 : Blo 2131435 14587103 := bstep (se 1 (by rfl) ⟨10940327, by rfl⟩ : syracuseStep 14587103 = 21880655) B21880655
theorem B9724735 : Blo 2131435 9724735 := bstep (se 1 (by rfl) ⟨7293551, by rfl⟩ : syracuseStep 9724735 = 14587103) B14587103
theorem B12966313 : Blo 2131435 12966313 := bstep (se 2 (by rfl) ⟨4862367, by rfl⟩ : syracuseStep 12966313 = 9724735) B9724735
theorem B17288417 : Blo 2131435 17288417 := bstep (se 2 (by rfl) ⟨6483156, by rfl⟩ : syracuseStep 17288417 = 12966313) B12966313
theorem B11525611 : Blo 2131435 11525611 := bstep (se 1 (by rfl) ⟨8644208, by rfl⟩ : syracuseStep 11525611 = 17288417) B17288417
theorem B15367481 : Blo 2131435 15367481 := bstep (se 2 (by rfl) ⟨5762805, by rfl⟩ : syracuseStep 15367481 = 11525611) B11525611
theorem B10244987 : Blo 2131435 10244987 := bstep (se 1 (by rfl) ⟨7683740, by rfl⟩ : syracuseStep 10244987 = 15367481) B15367481
theorem B6829991 : Blo 2131435 6829991 := bstep (se 1 (by rfl) ⟨5122493, by rfl⟩ : syracuseStep 6829991 = 10244987) B10244987
theorem B4553327 : Blo 2131435 4553327 := bstep (se 1 (by rfl) ⟨3414995, by rfl⟩ : syracuseStep 4553327 = 6829991) B6829991
theorem B3035551 : Blo 2131435 3035551 := bstep (se 1 (by rfl) ⟨2276663, by rfl⟩ : syracuseStep 3035551 = 4553327) B4553327
theorem B4047401 : Blo 2131435 4047401 := bstep (se 2 (by rfl) ⟨1517775, by rfl⟩ : syracuseStep 4047401 = 3035551) B3035551
theorem B2698267 : Blo 2131435 2698267 := bstep (se 1 (by rfl) ⟨2023700, by rfl⟩ : syracuseStep 2698267 = 4047401) B4047401
theorem B3597689 : Blo 2131435 3597689 := bstep (se 2 (by rfl) ⟨1349133, by rfl⟩ : syracuseStep 3597689 = 2698267) B2698267
theorem B2398459 : Blo 2131435 2398459 := bstep (se 1 (by rfl) ⟨1798844, by rfl⟩ : syracuseStep 2398459 = 3597689) B3597689
theorem B3197945 : Blo 2131435 3197945 := bstep (se 2 (by rfl) ⟨1199229, by rfl⟩ : syracuseStep 3197945 = 2398459) B2398459
theorem B2131963 : Blo 2131435 2131963 := bstep (se 1 (by rfl) ⟨1598972, by rfl⟩ : syracuseStep 2131963 = 3197945) B3197945
theorem B9230917 : Blo 2131435 9230917 := bbase (se 4 (by rfl) ⟨865398, by rfl⟩ : syracuseStep 9230917 = 1730797) (by norm_num)
theorem B12307889 : Blo 2131435 12307889 := bstep (se 2 (by rfl) ⟨4615458, by rfl⟩ : syracuseStep 12307889 = 9230917) B9230917
theorem B8205259 : Blo 2131435 8205259 := bstep (se 1 (by rfl) ⟨6153944, by rfl⟩ : syracuseStep 8205259 = 12307889) B12307889
theorem B10940345 : Blo 2131435 10940345 := bstep (se 2 (by rfl) ⟨4102629, by rfl⟩ : syracuseStep 10940345 = 8205259) B8205259
theorem B7293563 : Blo 2131435 7293563 := bstep (se 1 (by rfl) ⟨5470172, by rfl⟩ : syracuseStep 7293563 = 10940345) B10940345
theorem B4862375 : Blo 2131435 4862375 := bstep (se 1 (by rfl) ⟨3646781, by rfl⟩ : syracuseStep 4862375 = 7293563) B7293563
theorem B3241583 : Blo 2131435 3241583 := bstep (se 1 (by rfl) ⟨2431187, by rfl⟩ : syracuseStep 3241583 = 4862375) B4862375
theorem B2161055 : Blo 2131435 2161055 := bstep (se 1 (by rfl) ⟨1620791, by rfl⟩ : syracuseStep 2161055 = 3241583) B3241583
theorem B92205013 : Blo 2131435 92205013 := bstep (se 7 (by rfl) ⟨1080527, by rfl⟩ : syracuseStep 92205013 = 2161055) B2161055
theorem B122940017 : Blo 2131435 122940017 := bstep (se 2 (by rfl) ⟨46102506, by rfl⟩ : syracuseStep 122940017 = 92205013) B92205013
theorem B81960011 : Blo 2131435 81960011 := bstep (se 1 (by rfl) ⟨61470008, by rfl⟩ : syracuseStep 81960011 = 122940017) B122940017
theorem B54640007 : Blo 2131435 54640007 := bstep (se 1 (by rfl) ⟨40980005, by rfl⟩ : syracuseStep 54640007 = 81960011) B81960011
theorem B36426671 : Blo 2131435 36426671 := bstep (se 1 (by rfl) ⟨27320003, by rfl⟩ : syracuseStep 36426671 = 54640007) B54640007
theorem B24284447 : Blo 2131435 24284447 := bstep (se 1 (by rfl) ⟨18213335, by rfl⟩ : syracuseStep 24284447 = 36426671) B36426671
theorem B16189631 : Blo 2131435 16189631 := bstep (se 1 (by rfl) ⟨12142223, by rfl⟩ : syracuseStep 16189631 = 24284447) B24284447
theorem B10793087 : Blo 2131435 10793087 := bstep (se 1 (by rfl) ⟨8094815, by rfl⟩ : syracuseStep 10793087 = 16189631) B16189631
theorem B7195391 : Blo 2131435 7195391 := bstep (se 1 (by rfl) ⟨5396543, by rfl⟩ : syracuseStep 7195391 = 10793087) B10793087
theorem B4796927 : Blo 2131435 4796927 := bstep (se 1 (by rfl) ⟨3597695, by rfl⟩ : syracuseStep 4796927 = 7195391) B7195391
theorem B3197951 : Blo 2131435 3197951 := bstep (se 1 (by rfl) ⟨2398463, by rfl⟩ : syracuseStep 3197951 = 4796927) B4796927
theorem B2131967 : Blo 2131435 2131967 := bstep (se 1 (by rfl) ⟨1598975, by rfl⟩ : syracuseStep 2131967 = 3197951) B3197951
theorem B3197957 : Blo 2131435 3197957 := bbase (se 4 (by rfl) ⟨299808, by rfl⟩ : syracuseStep 3197957 = 599617) (by norm_num)
theorem B2131971 : Blo 2131435 2131971 := bstep (se 1 (by rfl) ⟨1598978, by rfl⟩ : syracuseStep 2131971 = 3197957) B3197957
theorem B3597709 : Blo 2131435 3597709 := bbase (se 3 (by rfl) ⟨674570, by rfl⟩ : syracuseStep 3597709 = 1349141) (by norm_num)
theorem B4796945 : Blo 2131435 4796945 := bstep (se 2 (by rfl) ⟨1798854, by rfl⟩ : syracuseStep 4796945 = 3597709) B3597709
theorem B3197963 : Blo 2131435 3197963 := bstep (se 1 (by rfl) ⟨2398472, by rfl⟩ : syracuseStep 3197963 = 4796945) B4796945
theorem B2131975 : Blo 2131435 2131975 := bstep (se 1 (by rfl) ⟨1598981, by rfl⟩ : syracuseStep 2131975 = 3197963) B3197963
theorem B2398477 : Blo 2131435 2398477 := bbase (se 3 (by rfl) ⟨449714, by rfl⟩ : syracuseStep 2398477 = 899429) (by norm_num)
theorem B3197969 : Blo 2131435 3197969 := bstep (se 2 (by rfl) ⟨1199238, by rfl⟩ : syracuseStep 3197969 = 2398477) B2398477
theorem B2131979 : Blo 2131435 2131979 := bstep (se 1 (by rfl) ⟨1598984, by rfl⟩ : syracuseStep 2131979 = 3197969) B3197969
theorem B7195445 : Blo 2131435 7195445 := bbase (se 5 (by rfl) ⟨337286, by rfl⟩ : syracuseStep 7195445 = 674573) (by norm_num)
theorem B4796963 : Blo 2131435 4796963 := bstep (se 1 (by rfl) ⟨3597722, by rfl⟩ : syracuseStep 4796963 = 7195445) B7195445
theorem B3197975 : Blo 2131435 3197975 := bstep (se 1 (by rfl) ⟨2398481, by rfl⟩ : syracuseStep 3197975 = 4796963) B4796963
theorem B2131983 : Blo 2131435 2131983 := bstep (se 1 (by rfl) ⟨1598987, by rfl⟩ : syracuseStep 2131983 = 3197975) B3197975
theorem B3197981 : Blo 2131435 3197981 := bbase (se 3 (by rfl) ⟨599621, by rfl⟩ : syracuseStep 3197981 = 1199243) (by norm_num)
theorem B2131987 : Blo 2131435 2131987 := bstep (se 1 (by rfl) ⟨1598990, by rfl⟩ : syracuseStep 2131987 = 3197981) B3197981
theorem B4796981 : Blo 2131435 4796981 := bbase (se 5 (by rfl) ⟨224858, by rfl⟩ : syracuseStep 4796981 = 449717) (by norm_num)
theorem B3197987 : Blo 2131435 3197987 := bstep (se 1 (by rfl) ⟨2398490, by rfl⟩ : syracuseStep 3197987 = 4796981) B4796981
theorem B2131991 : Blo 2131435 2131991 := bstep (se 1 (by rfl) ⟨1598993, by rfl⟩ : syracuseStep 2131991 = 3197987) B3197987
theorem B9106789 : Blo 2131435 9106789 := bbase (se 4 (by rfl) ⟨853761, by rfl⟩ : syracuseStep 9106789 = 1707523) (by norm_num)
theorem B12142385 : Blo 2131435 12142385 := bstep (se 2 (by rfl) ⟨4553394, by rfl⟩ : syracuseStep 12142385 = 9106789) B9106789
theorem B8094923 : Blo 2131435 8094923 := bstep (se 1 (by rfl) ⟨6071192, by rfl⟩ : syracuseStep 8094923 = 12142385) B12142385
theorem B5396615 : Blo 2131435 5396615 := bstep (se 1 (by rfl) ⟨4047461, by rfl⟩ : syracuseStep 5396615 = 8094923) B8094923
theorem B3597743 : Blo 2131435 3597743 := bstep (se 1 (by rfl) ⟨2698307, by rfl⟩ : syracuseStep 3597743 = 5396615) B5396615
theorem B2398495 : Blo 2131435 2398495 := bstep (se 1 (by rfl) ⟨1798871, by rfl⟩ : syracuseStep 2398495 = 3597743) B3597743
theorem B3197993 : Blo 2131435 3197993 := bstep (se 2 (by rfl) ⟨1199247, by rfl⟩ : syracuseStep 3197993 = 2398495) B2398495
theorem B2131995 : Blo 2131435 2131995 := bstep (se 1 (by rfl) ⟨1598996, by rfl⟩ : syracuseStep 2131995 = 3197993) B3197993
theorem B9106805 : Blo 2131435 9106805 := bbase (se 5 (by rfl) ⟨426881, by rfl⟩ : syracuseStep 9106805 = 853763) (by norm_num)
theorem B6071203 : Blo 2131435 6071203 := bstep (se 1 (by rfl) ⟨4553402, by rfl⟩ : syracuseStep 6071203 = 9106805) B9106805
theorem B8094937 : Blo 2131435 8094937 := bstep (se 2 (by rfl) ⟨3035601, by rfl⟩ : syracuseStep 8094937 = 6071203) B6071203
theorem B10793249 : Blo 2131435 10793249 := bstep (se 2 (by rfl) ⟨4047468, by rfl⟩ : syracuseStep 10793249 = 8094937) B8094937
theorem B7195499 : Blo 2131435 7195499 := bstep (se 1 (by rfl) ⟨5396624, by rfl⟩ : syracuseStep 7195499 = 10793249) B10793249
theorem B4796999 : Blo 2131435 4796999 := bstep (se 1 (by rfl) ⟨3597749, by rfl⟩ : syracuseStep 4796999 = 7195499) B7195499
theorem B3197999 : Blo 2131435 3197999 := bstep (se 1 (by rfl) ⟨2398499, by rfl⟩ : syracuseStep 3197999 = 4796999) B4796999
theorem B2131999 : Blo 2131435 2131999 := bstep (se 1 (by rfl) ⟨1598999, by rfl⟩ : syracuseStep 2131999 = 3197999) B3197999
theorem B3198005 : Blo 2131435 3198005 := bbase (se 5 (by rfl) ⟨149906, by rfl⟩ : syracuseStep 3198005 = 299813) (by norm_num)
theorem B2132003 : Blo 2131435 2132003 := bstep (se 1 (by rfl) ⟨1599002, by rfl⟩ : syracuseStep 2132003 = 3198005) B3198005
theorem B5396645 : Blo 2131435 5396645 := bbase (se 4 (by rfl) ⟨505935, by rfl⟩ : syracuseStep 5396645 = 1011871) (by norm_num)
theorem B3597763 : Blo 2131435 3597763 := bstep (se 1 (by rfl) ⟨2698322, by rfl⟩ : syracuseStep 3597763 = 5396645) B5396645
theorem B4797017 : Blo 2131435 4797017 := bstep (se 2 (by rfl) ⟨1798881, by rfl⟩ : syracuseStep 4797017 = 3597763) B3597763
theorem B3198011 : Blo 2131435 3198011 := bstep (se 1 (by rfl) ⟨2398508, by rfl⟩ : syracuseStep 3198011 = 4797017) B4797017
theorem B2132007 : Blo 2131435 2132007 := bstep (se 1 (by rfl) ⟨1599005, by rfl⟩ : syracuseStep 2132007 = 3198011) B3198011
theorem B2398513 : Blo 2131435 2398513 := bbase (se 2 (by rfl) ⟨899442, by rfl⟩ : syracuseStep 2398513 = 1798885) (by norm_num)
theorem B3198017 : Blo 2131435 3198017 := bstep (se 2 (by rfl) ⟨1199256, by rfl⟩ : syracuseStep 3198017 = 2398513) B2398513
theorem B2132011 : Blo 2131435 2132011 := bstep (se 1 (by rfl) ⟨1599008, by rfl⟩ : syracuseStep 2132011 = 3198017) B3198017
theorem B4553437 : Blo 2131435 4553437 := bbase (se 3 (by rfl) ⟨853769, by rfl⟩ : syracuseStep 4553437 = 1707539) (by norm_num)
theorem B6071249 : Blo 2131435 6071249 := bstep (se 2 (by rfl) ⟨2276718, by rfl⟩ : syracuseStep 6071249 = 4553437) B4553437
theorem B4047499 : Blo 2131435 4047499 := bstep (se 1 (by rfl) ⟨3035624, by rfl⟩ : syracuseStep 4047499 = 6071249) B6071249
theorem B5396665 : Blo 2131435 5396665 := bstep (se 2 (by rfl) ⟨2023749, by rfl⟩ : syracuseStep 5396665 = 4047499) B4047499
theorem B7195553 : Blo 2131435 7195553 := bstep (se 2 (by rfl) ⟨2698332, by rfl⟩ : syracuseStep 7195553 = 5396665) B5396665
theorem B4797035 : Blo 2131435 4797035 := bstep (se 1 (by rfl) ⟨3597776, by rfl⟩ : syracuseStep 4797035 = 7195553) B7195553
theorem B3198023 : Blo 2131435 3198023 := bstep (se 1 (by rfl) ⟨2398517, by rfl⟩ : syracuseStep 3198023 = 4797035) B4797035
theorem B2132015 : Blo 2131435 2132015 := bstep (se 1 (by rfl) ⟨1599011, by rfl⟩ : syracuseStep 2132015 = 3198023) B3198023
theorem B3198029 : Blo 2131435 3198029 := bbase (se 3 (by rfl) ⟨599630, by rfl⟩ : syracuseStep 3198029 = 1199261) (by norm_num)
theorem B2132019 : Blo 2131435 2132019 := bstep (se 1 (by rfl) ⟨1599014, by rfl⟩ : syracuseStep 2132019 = 3198029) B3198029
theorem B4797053 : Blo 2131435 4797053 := bbase (se 3 (by rfl) ⟨899447, by rfl⟩ : syracuseStep 4797053 = 1798895) (by norm_num)
theorem B3198035 : Blo 2131435 3198035 := bstep (se 1 (by rfl) ⟨2398526, by rfl⟩ : syracuseStep 3198035 = 4797053) B4797053
theorem B2132023 : Blo 2131435 2132023 := bstep (se 1 (by rfl) ⟨1599017, by rfl⟩ : syracuseStep 2132023 = 3198035) B3198035
theorem B3597797 : Blo 2131435 3597797 := bbase (se 4 (by rfl) ⟨337293, by rfl⟩ : syracuseStep 3597797 = 674587) (by norm_num)
theorem B2398531 : Blo 2131435 2398531 := bstep (se 1 (by rfl) ⟨1798898, by rfl⟩ : syracuseStep 2398531 = 3597797) B3597797
theorem B3198041 : Blo 2131435 3198041 := bstep (se 2 (by rfl) ⟨1199265, by rfl⟩ : syracuseStep 3198041 = 2398531) B2398531
theorem B2132027 : Blo 2131435 2132027 := bstep (se 1 (by rfl) ⟨1599020, by rfl⟩ : syracuseStep 2132027 = 3198041) B3198041
theorem B10385093 : Blo 2131435 10385093 := bbase (se 4 (by rfl) ⟨973602, by rfl⟩ : syracuseStep 10385093 = 1947205) (by norm_num)
theorem B6923395 : Blo 2131435 6923395 := bstep (se 1 (by rfl) ⟨5192546, by rfl⟩ : syracuseStep 6923395 = 10385093) B10385093
theorem B9231193 : Blo 2131435 9231193 := bstep (se 2 (by rfl) ⟨3461697, by rfl⟩ : syracuseStep 9231193 = 6923395) B6923395
theorem B12308257 : Blo 2131435 12308257 := bstep (se 2 (by rfl) ⟨4615596, by rfl⟩ : syracuseStep 12308257 = 9231193) B9231193
theorem B16411009 : Blo 2131435 16411009 := bstep (se 2 (by rfl) ⟨6154128, by rfl⟩ : syracuseStep 16411009 = 12308257) B12308257
theorem B21881345 : Blo 2131435 21881345 := bstep (se 2 (by rfl) ⟨8205504, by rfl⟩ : syracuseStep 21881345 = 16411009) B16411009
theorem B58350253 : Blo 2131435 58350253 := bstep (se 3 (by rfl) ⟨10940672, by rfl⟩ : syracuseStep 58350253 = 21881345) B21881345
theorem B77800337 : Blo 2131435 77800337 := bstep (se 2 (by rfl) ⟨29175126, by rfl⟩ : syracuseStep 77800337 = 58350253) B58350253
theorem B51866891 : Blo 2131435 51866891 := bstep (se 1 (by rfl) ⟨38900168, by rfl⟩ : syracuseStep 51866891 = 77800337) B77800337
theorem B34577927 : Blo 2131435 34577927 := bstep (se 1 (by rfl) ⟨25933445, by rfl⟩ : syracuseStep 34577927 = 51866891) B51866891
theorem B23051951 : Blo 2131435 23051951 := bstep (se 1 (by rfl) ⟨17288963, by rfl⟩ : syracuseStep 23051951 = 34577927) B34577927
theorem B15367967 : Blo 2131435 15367967 := bstep (se 1 (by rfl) ⟨11525975, by rfl⟩ : syracuseStep 15367967 = 23051951) B23051951
theorem B10245311 : Blo 2131435 10245311 := bstep (se 1 (by rfl) ⟨7683983, by rfl⟩ : syracuseStep 10245311 = 15367967) B15367967
theorem B6830207 : Blo 2131435 6830207 := bstep (se 1 (by rfl) ⟨5122655, by rfl⟩ : syracuseStep 6830207 = 10245311) B10245311
theorem B4553471 : Blo 2131435 4553471 := bstep (se 1 (by rfl) ⟨3415103, by rfl⟩ : syracuseStep 4553471 = 6830207) B6830207
theorem B3035647 : Blo 2131435 3035647 := bstep (se 1 (by rfl) ⟨2276735, by rfl⟩ : syracuseStep 3035647 = 4553471) B4553471
theorem B16190117 : Blo 2131435 16190117 := bstep (se 4 (by rfl) ⟨1517823, by rfl⟩ : syracuseStep 16190117 = 3035647) B3035647
theorem B10793411 : Blo 2131435 10793411 := bstep (se 1 (by rfl) ⟨8095058, by rfl⟩ : syracuseStep 10793411 = 16190117) B16190117
theorem B7195607 : Blo 2131435 7195607 := bstep (se 1 (by rfl) ⟨5396705, by rfl⟩ : syracuseStep 7195607 = 10793411) B10793411
theorem B4797071 : Blo 2131435 4797071 := bstep (se 1 (by rfl) ⟨3597803, by rfl⟩ : syracuseStep 4797071 = 7195607) B7195607
theorem B3198047 : Blo 2131435 3198047 := bstep (se 1 (by rfl) ⟨2398535, by rfl⟩ : syracuseStep 3198047 = 4797071) B4797071
theorem B2132031 : Blo 2131435 2132031 := bstep (se 1 (by rfl) ⟨1599023, by rfl⟩ : syracuseStep 2132031 = 3198047) B3198047
theorem B3198053 : Blo 2131435 3198053 := bbase (se 4 (by rfl) ⟨299817, by rfl⟩ : syracuseStep 3198053 = 599635) (by norm_num)
theorem B2132035 : Blo 2131435 2132035 := bstep (se 1 (by rfl) ⟨1599026, by rfl⟩ : syracuseStep 2132035 = 3198053) B3198053
theorem B3415117 : Blo 2131435 3415117 := bbase (se 3 (by rfl) ⟨640334, by rfl⟩ : syracuseStep 3415117 = 1280669) (by norm_num)
theorem B4553489 : Blo 2131435 4553489 := bstep (se 2 (by rfl) ⟨1707558, by rfl⟩ : syracuseStep 4553489 = 3415117) B3415117
theorem B3035659 : Blo 2131435 3035659 := bstep (se 1 (by rfl) ⟨2276744, by rfl⟩ : syracuseStep 3035659 = 4553489) B4553489
theorem B4047545 : Blo 2131435 4047545 := bstep (se 2 (by rfl) ⟨1517829, by rfl⟩ : syracuseStep 4047545 = 3035659) B3035659
theorem B2698363 : Blo 2131435 2698363 := bstep (se 1 (by rfl) ⟨2023772, by rfl⟩ : syracuseStep 2698363 = 4047545) B4047545
theorem B3597817 : Blo 2131435 3597817 := bstep (se 2 (by rfl) ⟨1349181, by rfl⟩ : syracuseStep 3597817 = 2698363) B2698363
theorem B4797089 : Blo 2131435 4797089 := bstep (se 2 (by rfl) ⟨1798908, by rfl⟩ : syracuseStep 4797089 = 3597817) B3597817
theorem B3198059 : Blo 2131435 3198059 := bstep (se 1 (by rfl) ⟨2398544, by rfl⟩ : syracuseStep 3198059 = 4797089) B4797089
theorem B2132039 : Blo 2131435 2132039 := bstep (se 1 (by rfl) ⟨1599029, by rfl⟩ : syracuseStep 2132039 = 3198059) B3198059
theorem B2398549 : Blo 2131435 2398549 := bbase (se 10 (by rfl) ⟨3513, by rfl⟩ : syracuseStep 2398549 = 7027) (by norm_num)
theorem B3198065 : Blo 2131435 3198065 := bstep (se 2 (by rfl) ⟨1199274, by rfl⟩ : syracuseStep 3198065 = 2398549) B2398549
theorem B2132043 : Blo 2131435 2132043 := bstep (se 1 (by rfl) ⟨1599032, by rfl⟩ : syracuseStep 2132043 = 3198065) B3198065
theorem B2698373 : Blo 2131435 2698373 := bbase (se 4 (by rfl) ⟨252972, by rfl⟩ : syracuseStep 2698373 = 505945) (by norm_num)
theorem B7195661 : Blo 2131435 7195661 := bstep (se 3 (by rfl) ⟨1349186, by rfl⟩ : syracuseStep 7195661 = 2698373) B2698373
theorem B4797107 : Blo 2131435 4797107 := bstep (se 1 (by rfl) ⟨3597830, by rfl⟩ : syracuseStep 4797107 = 7195661) B7195661
theorem B3198071 : Blo 2131435 3198071 := bstep (se 1 (by rfl) ⟨2398553, by rfl⟩ : syracuseStep 3198071 = 4797107) B4797107
theorem B2132047 : Blo 2131435 2132047 := bstep (se 1 (by rfl) ⟨1599035, by rfl⟩ : syracuseStep 2132047 = 3198071) B3198071
theorem B3198077 : Blo 2131435 3198077 := bbase (se 3 (by rfl) ⟨599639, by rfl⟩ : syracuseStep 3198077 = 1199279) (by norm_num)
theorem B2132051 : Blo 2131435 2132051 := bstep (se 1 (by rfl) ⟨1599038, by rfl⟩ : syracuseStep 2132051 = 3198077) B3198077
theorem B4797125 : Blo 2131435 4797125 := bbase (se 4 (by rfl) ⟨449730, by rfl⟩ : syracuseStep 4797125 = 899461) (by norm_num)
theorem B3198083 : Blo 2131435 3198083 := bstep (se 1 (by rfl) ⟨2398562, by rfl⟩ : syracuseStep 3198083 = 4797125) B4797125
theorem B2132055 : Blo 2131435 2132055 := bstep (se 1 (by rfl) ⟨1599041, by rfl⟩ : syracuseStep 2132055 = 3198083) B3198083
theorem B7684085 : Blo 2131435 7684085 := bbase (se 5 (by rfl) ⟨360191, by rfl⟩ : syracuseStep 7684085 = 720383) (by norm_num)
theorem B20490893 : Blo 2131435 20490893 := bstep (se 3 (by rfl) ⟨3842042, by rfl⟩ : syracuseStep 20490893 = 7684085) B7684085
theorem B13660595 : Blo 2131435 13660595 := bstep (se 1 (by rfl) ⟨10245446, by rfl⟩ : syracuseStep 13660595 = 20490893) B20490893
theorem B9107063 : Blo 2131435 9107063 := bstep (se 1 (by rfl) ⟨6830297, by rfl⟩ : syracuseStep 9107063 = 13660595) B13660595
theorem B6071375 : Blo 2131435 6071375 := bstep (se 1 (by rfl) ⟨4553531, by rfl⟩ : syracuseStep 6071375 = 9107063) B9107063
theorem B4047583 : Blo 2131435 4047583 := bstep (se 1 (by rfl) ⟨3035687, by rfl⟩ : syracuseStep 4047583 = 6071375) B6071375
theorem B5396777 : Blo 2131435 5396777 := bstep (se 2 (by rfl) ⟨2023791, by rfl⟩ : syracuseStep 5396777 = 4047583) B4047583
theorem B3597851 : Blo 2131435 3597851 := bstep (se 1 (by rfl) ⟨2698388, by rfl⟩ : syracuseStep 3597851 = 5396777) B5396777
theorem B2398567 : Blo 2131435 2398567 := bstep (se 1 (by rfl) ⟨1798925, by rfl⟩ : syracuseStep 2398567 = 3597851) B3597851
theorem B3198089 : Blo 2131435 3198089 := bstep (se 2 (by rfl) ⟨1199283, by rfl⟩ : syracuseStep 3198089 = 2398567) B2398567
theorem B2132059 : Blo 2131435 2132059 := bstep (se 1 (by rfl) ⟨1599044, by rfl⟩ : syracuseStep 2132059 = 3198089) B3198089
theorem B10793573 : Blo 2131435 10793573 := bbase (se 4 (by rfl) ⟨1011897, by rfl⟩ : syracuseStep 10793573 = 2023795) (by norm_num)
theorem B7195715 : Blo 2131435 7195715 := bstep (se 1 (by rfl) ⟨5396786, by rfl⟩ : syracuseStep 7195715 = 10793573) B10793573
theorem B4797143 : Blo 2131435 4797143 := bstep (se 1 (by rfl) ⟨3597857, by rfl⟩ : syracuseStep 4797143 = 7195715) B7195715
theorem B3198095 : Blo 2131435 3198095 := bstep (se 1 (by rfl) ⟨2398571, by rfl⟩ : syracuseStep 3198095 = 4797143) B4797143
theorem B2132063 : Blo 2131435 2132063 := bstep (se 1 (by rfl) ⟨1599047, by rfl⟩ : syracuseStep 2132063 = 3198095) B3198095
theorem B3198101 : Blo 2131435 3198101 := bbase (se 6 (by rfl) ⟨74955, by rfl⟩ : syracuseStep 3198101 = 149911) (by norm_num)
theorem B2132067 : Blo 2131435 2132067 := bstep (se 1 (by rfl) ⟨1599050, by rfl⟩ : syracuseStep 2132067 = 3198101) B3198101
theorem B7788965 : Blo 2131435 7788965 := bbase (se 4 (by rfl) ⟨730215, by rfl⟩ : syracuseStep 7788965 = 1460431) (by norm_num)
theorem B83082293 : Blo 2131435 83082293 := bstep (se 5 (by rfl) ⟨3894482, by rfl⟩ : syracuseStep 83082293 = 7788965) B7788965
theorem B55388195 : Blo 2131435 55388195 := bstep (se 1 (by rfl) ⟨41541146, by rfl⟩ : syracuseStep 55388195 = 83082293) B83082293
theorem B36925463 : Blo 2131435 36925463 := bstep (se 1 (by rfl) ⟨27694097, by rfl⟩ : syracuseStep 36925463 = 55388195) B55388195
theorem B24616975 : Blo 2131435 24616975 := bstep (se 1 (by rfl) ⟨18462731, by rfl⟩ : syracuseStep 24616975 = 36925463) B36925463
theorem B32822633 : Blo 2131435 32822633 := bstep (se 2 (by rfl) ⟨12308487, by rfl⟩ : syracuseStep 32822633 = 24616975) B24616975
theorem B21881755 : Blo 2131435 21881755 := bstep (se 1 (by rfl) ⟨16411316, by rfl⟩ : syracuseStep 21881755 = 32822633) B32822633
theorem B116702693 : Blo 2131435 116702693 := bstep (se 4 (by rfl) ⟨10940877, by rfl⟩ : syracuseStep 116702693 = 21881755) B21881755
theorem B77801795 : Blo 2131435 77801795 := bstep (se 1 (by rfl) ⟨58351346, by rfl⟩ : syracuseStep 77801795 = 116702693) B116702693
theorem B51867863 : Blo 2131435 51867863 := bstep (se 1 (by rfl) ⟨38900897, by rfl⟩ : syracuseStep 51867863 = 77801795) B77801795
theorem B34578575 : Blo 2131435 34578575 := bstep (se 1 (by rfl) ⟨25933931, by rfl⟩ : syracuseStep 34578575 = 51867863) B51867863
theorem B23052383 : Blo 2131435 23052383 := bstep (se 1 (by rfl) ⟨17289287, by rfl⟩ : syracuseStep 23052383 = 34578575) B34578575
theorem B15368255 : Blo 2131435 15368255 := bstep (se 1 (by rfl) ⟨11526191, by rfl⟩ : syracuseStep 15368255 = 23052383) B23052383
theorem B10245503 : Blo 2131435 10245503 := bstep (se 1 (by rfl) ⟨7684127, by rfl⟩ : syracuseStep 10245503 = 15368255) B15368255
theorem B6830335 : Blo 2131435 6830335 := bstep (se 1 (by rfl) ⟨5122751, by rfl⟩ : syracuseStep 6830335 = 10245503) B10245503
theorem B9107113 : Blo 2131435 9107113 := bstep (se 2 (by rfl) ⟨3415167, by rfl⟩ : syracuseStep 9107113 = 6830335) B6830335
theorem B12142817 : Blo 2131435 12142817 := bstep (se 2 (by rfl) ⟨4553556, by rfl⟩ : syracuseStep 12142817 = 9107113) B9107113
theorem B8095211 : Blo 2131435 8095211 := bstep (se 1 (by rfl) ⟨6071408, by rfl⟩ : syracuseStep 8095211 = 12142817) B12142817
theorem B5396807 : Blo 2131435 5396807 := bstep (se 1 (by rfl) ⟨4047605, by rfl⟩ : syracuseStep 5396807 = 8095211) B8095211
theorem B3597871 : Blo 2131435 3597871 := bstep (se 1 (by rfl) ⟨2698403, by rfl⟩ : syracuseStep 3597871 = 5396807) B5396807
theorem B4797161 : Blo 2131435 4797161 := bstep (se 2 (by rfl) ⟨1798935, by rfl⟩ : syracuseStep 4797161 = 3597871) B3597871
theorem B3198107 : Blo 2131435 3198107 := bstep (se 1 (by rfl) ⟨2398580, by rfl⟩ : syracuseStep 3198107 = 4797161) B4797161
theorem B2132071 : Blo 2131435 2132071 := bstep (se 1 (by rfl) ⟨1599053, by rfl⟩ : syracuseStep 2132071 = 3198107) B3198107
theorem B2398585 : Blo 2131435 2398585 := bbase (se 2 (by rfl) ⟨899469, by rfl⟩ : syracuseStep 2398585 = 1798939) (by norm_num)
theorem B3198113 : Blo 2131435 3198113 := bstep (se 2 (by rfl) ⟨1199292, by rfl⟩ : syracuseStep 3198113 = 2398585) B2398585
theorem B2132075 : Blo 2131435 2132075 := bstep (se 1 (by rfl) ⟨1599056, by rfl⟩ : syracuseStep 2132075 = 3198113) B3198113
theorem B10245541 : Blo 2131435 10245541 := bbase (se 4 (by rfl) ⟨960519, by rfl⟩ : syracuseStep 10245541 = 1921039) (by norm_num)
theorem B13660721 : Blo 2131435 13660721 := bstep (se 2 (by rfl) ⟨5122770, by rfl⟩ : syracuseStep 13660721 = 10245541) B10245541
theorem B9107147 : Blo 2131435 9107147 := bstep (se 1 (by rfl) ⟨6830360, by rfl⟩ : syracuseStep 9107147 = 13660721) B13660721
theorem B6071431 : Blo 2131435 6071431 := bstep (se 1 (by rfl) ⟨4553573, by rfl⟩ : syracuseStep 6071431 = 9107147) B9107147
theorem B8095241 : Blo 2131435 8095241 := bstep (se 2 (by rfl) ⟨3035715, by rfl⟩ : syracuseStep 8095241 = 6071431) B6071431
theorem B5396827 : Blo 2131435 5396827 := bstep (se 1 (by rfl) ⟨4047620, by rfl⟩ : syracuseStep 5396827 = 8095241) B8095241
theorem B7195769 : Blo 2131435 7195769 := bstep (se 2 (by rfl) ⟨2698413, by rfl⟩ : syracuseStep 7195769 = 5396827) B5396827
theorem B4797179 : Blo 2131435 4797179 := bstep (se 1 (by rfl) ⟨3597884, by rfl⟩ : syracuseStep 4797179 = 7195769) B7195769
theorem B3198119 : Blo 2131435 3198119 := bstep (se 1 (by rfl) ⟨2398589, by rfl⟩ : syracuseStep 3198119 = 4797179) B4797179
theorem B2132079 : Blo 2131435 2132079 := bstep (se 1 (by rfl) ⟨1599059, by rfl⟩ : syracuseStep 2132079 = 3198119) B3198119
theorem B3198125 : Blo 2131435 3198125 := bbase (se 3 (by rfl) ⟨599648, by rfl⟩ : syracuseStep 3198125 = 1199297) (by norm_num)
theorem B2132083 : Blo 2131435 2132083 := bstep (se 1 (by rfl) ⟨1599062, by rfl⟩ : syracuseStep 2132083 = 3198125) B3198125
theorem B4797197 : Blo 2131435 4797197 := bbase (se 3 (by rfl) ⟨899474, by rfl⟩ : syracuseStep 4797197 = 1798949) (by norm_num)
theorem B3198131 : Blo 2131435 3198131 := bstep (se 1 (by rfl) ⟨2398598, by rfl⟩ : syracuseStep 3198131 = 4797197) B4797197
theorem B2132087 : Blo 2131435 2132087 := bstep (se 1 (by rfl) ⟨1599065, by rfl⟩ : syracuseStep 2132087 = 3198131) B3198131
theorem B2698429 : Blo 2131435 2698429 := bbase (se 3 (by rfl) ⟨505955, by rfl⟩ : syracuseStep 2698429 = 1011911) (by norm_num)
theorem B3597905 : Blo 2131435 3597905 := bstep (se 2 (by rfl) ⟨1349214, by rfl⟩ : syracuseStep 3597905 = 2698429) B2698429
theorem B2398603 : Blo 2131435 2398603 := bstep (se 1 (by rfl) ⟨1798952, by rfl⟩ : syracuseStep 2398603 = 3597905) B3597905
theorem B3198137 : Blo 2131435 3198137 := bstep (se 2 (by rfl) ⟨1199301, by rfl⟩ : syracuseStep 3198137 = 2398603) B2398603
theorem B2132091 : Blo 2131435 2132091 := bstep (se 1 (by rfl) ⟨1599068, by rfl⟩ : syracuseStep 2132091 = 3198137) B3198137
theorem B7684213 : Blo 2131435 7684213 := bbase (se 5 (by rfl) ⟨360197, by rfl⟩ : syracuseStep 7684213 = 720395) (by norm_num)
theorem B10245617 : Blo 2131435 10245617 := bstep (se 2 (by rfl) ⟨3842106, by rfl⟩ : syracuseStep 10245617 = 7684213) B7684213
theorem B6830411 : Blo 2131435 6830411 := bstep (se 1 (by rfl) ⟨5122808, by rfl⟩ : syracuseStep 6830411 = 10245617) B10245617
theorem B18214429 : Blo 2131435 18214429 := bstep (se 3 (by rfl) ⟨3415205, by rfl⟩ : syracuseStep 18214429 = 6830411) B6830411
theorem B24285905 : Blo 2131435 24285905 := bstep (se 2 (by rfl) ⟨9107214, by rfl⟩ : syracuseStep 24285905 = 18214429) B18214429
theorem B16190603 : Blo 2131435 16190603 := bstep (se 1 (by rfl) ⟨12142952, by rfl⟩ : syracuseStep 16190603 = 24285905) B24285905
theorem B10793735 : Blo 2131435 10793735 := bstep (se 1 (by rfl) ⟨8095301, by rfl⟩ : syracuseStep 10793735 = 16190603) B16190603
theorem B7195823 : Blo 2131435 7195823 := bstep (se 1 (by rfl) ⟨5396867, by rfl⟩ : syracuseStep 7195823 = 10793735) B10793735
theorem B4797215 : Blo 2131435 4797215 := bstep (se 1 (by rfl) ⟨3597911, by rfl⟩ : syracuseStep 4797215 = 7195823) B7195823
theorem B3198143 : Blo 2131435 3198143 := bstep (se 1 (by rfl) ⟨2398607, by rfl⟩ : syracuseStep 3198143 = 4797215) B4797215
theorem B2132095 : Blo 2131435 2132095 := bstep (se 1 (by rfl) ⟨1599071, by rfl⟩ : syracuseStep 2132095 = 3198143) B3198143
theorem B3198149 : Blo 2131435 3198149 := bbase (se 4 (by rfl) ⟨299826, by rfl⟩ : syracuseStep 3198149 = 599653) (by norm_num)
theorem B2132099 : Blo 2131435 2132099 := bstep (se 1 (by rfl) ⟨1599074, by rfl⟩ : syracuseStep 2132099 = 3198149) B3198149
theorem B3597925 : Blo 2131435 3597925 := bbase (se 4 (by rfl) ⟨337305, by rfl⟩ : syracuseStep 3597925 = 674611) (by norm_num)
theorem B4797233 : Blo 2131435 4797233 := bstep (se 2 (by rfl) ⟨1798962, by rfl⟩ : syracuseStep 4797233 = 3597925) B3597925
theorem B3198155 : Blo 2131435 3198155 := bstep (se 1 (by rfl) ⟨2398616, by rfl⟩ : syracuseStep 3198155 = 4797233) B4797233
theorem B2132103 : Blo 2131435 2132103 := bstep (se 1 (by rfl) ⟨1599077, by rfl⟩ : syracuseStep 2132103 = 3198155) B3198155
theorem B2398621 : Blo 2131435 2398621 := bbase (se 3 (by rfl) ⟨449741, by rfl⟩ : syracuseStep 2398621 = 899483) (by norm_num)
theorem B3198161 : Blo 2131435 3198161 := bstep (se 2 (by rfl) ⟨1199310, by rfl⟩ : syracuseStep 3198161 = 2398621) B2398621
theorem B2132107 : Blo 2131435 2132107 := bstep (se 1 (by rfl) ⟨1599080, by rfl⟩ : syracuseStep 2132107 = 3198161) B3198161
theorem B7195877 : Blo 2131435 7195877 := bbase (se 4 (by rfl) ⟨674613, by rfl⟩ : syracuseStep 7195877 = 1349227) (by norm_num)
theorem B4797251 : Blo 2131435 4797251 := bstep (se 1 (by rfl) ⟨3597938, by rfl⟩ : syracuseStep 4797251 = 7195877) B7195877
theorem B3198167 : Blo 2131435 3198167 := bstep (se 1 (by rfl) ⟨2398625, by rfl⟩ : syracuseStep 3198167 = 4797251) B4797251
theorem B2132111 : Blo 2131435 2132111 := bstep (se 1 (by rfl) ⟨1599083, by rfl⟩ : syracuseStep 2132111 = 3198167) B3198167
theorem B3198173 : Blo 2131435 3198173 := bbase (se 3 (by rfl) ⟨599657, by rfl⟩ : syracuseStep 3198173 = 1199315) (by norm_num)
theorem B2132115 : Blo 2131435 2132115 := bstep (se 1 (by rfl) ⟨1599086, by rfl⟩ : syracuseStep 2132115 = 3198173) B3198173
theorem B4797269 : Blo 2131435 4797269 := bbase (se 9 (by rfl) ⟨14054, by rfl⟩ : syracuseStep 4797269 = 28109) (by norm_num)
theorem B3198179 : Blo 2131435 3198179 := bstep (se 1 (by rfl) ⟨2398634, by rfl⟩ : syracuseStep 3198179 = 4797269) B4797269
theorem B2132119 : Blo 2131435 2132119 := bstep (se 1 (by rfl) ⟨1599089, by rfl⟩ : syracuseStep 2132119 = 3198179) B3198179
theorem B6071557 : Blo 2131435 6071557 := bbase (se 4 (by rfl) ⟨569208, by rfl⟩ : syracuseStep 6071557 = 1138417) (by norm_num)
theorem B8095409 : Blo 2131435 8095409 := bstep (se 2 (by rfl) ⟨3035778, by rfl⟩ : syracuseStep 8095409 = 6071557) B6071557
theorem B5396939 : Blo 2131435 5396939 := bstep (se 1 (by rfl) ⟨4047704, by rfl⟩ : syracuseStep 5396939 = 8095409) B8095409
theorem B3597959 : Blo 2131435 3597959 := bstep (se 1 (by rfl) ⟨2698469, by rfl⟩ : syracuseStep 3597959 = 5396939) B5396939
theorem B2398639 : Blo 2131435 2398639 := bstep (se 1 (by rfl) ⟨1798979, by rfl⟩ : syracuseStep 2398639 = 3597959) B3597959
theorem B3198185 : Blo 2131435 3198185 := bstep (se 2 (by rfl) ⟨1199319, by rfl⟩ : syracuseStep 3198185 = 2398639) B2398639
theorem B2132123 : Blo 2131435 2132123 := bstep (se 1 (by rfl) ⟨1599092, by rfl⟩ : syracuseStep 2132123 = 3198185) B3198185
theorem B34579477 : Blo 2131435 34579477 := bbase (se 6 (by rfl) ⟨810456, by rfl⟩ : syracuseStep 34579477 = 1620913) (by norm_num)
theorem B46105969 : Blo 2131435 46105969 := bstep (se 2 (by rfl) ⟨17289738, by rfl⟩ : syracuseStep 46105969 = 34579477) B34579477
theorem B61474625 : Blo 2131435 61474625 := bstep (se 2 (by rfl) ⟨23052984, by rfl⟩ : syracuseStep 61474625 = 46105969) B46105969
theorem B40983083 : Blo 2131435 40983083 := bstep (se 1 (by rfl) ⟨30737312, by rfl⟩ : syracuseStep 40983083 = 61474625) B61474625
theorem B27322055 : Blo 2131435 27322055 := bstep (se 1 (by rfl) ⟨20491541, by rfl⟩ : syracuseStep 27322055 = 40983083) B40983083
theorem B18214703 : Blo 2131435 18214703 := bstep (se 1 (by rfl) ⟨13661027, by rfl⟩ : syracuseStep 18214703 = 27322055) B27322055
theorem B12143135 : Blo 2131435 12143135 := bstep (se 1 (by rfl) ⟨9107351, by rfl⟩ : syracuseStep 12143135 = 18214703) B18214703
theorem B8095423 : Blo 2131435 8095423 := bstep (se 1 (by rfl) ⟨6071567, by rfl⟩ : syracuseStep 8095423 = 12143135) B12143135
theorem B10793897 : Blo 2131435 10793897 := bstep (se 2 (by rfl) ⟨4047711, by rfl⟩ : syracuseStep 10793897 = 8095423) B8095423
theorem B7195931 : Blo 2131435 7195931 := bstep (se 1 (by rfl) ⟨5396948, by rfl⟩ : syracuseStep 7195931 = 10793897) B10793897
theorem B4797287 : Blo 2131435 4797287 := bstep (se 1 (by rfl) ⟨3597965, by rfl⟩ : syracuseStep 4797287 = 7195931) B7195931
theorem B3198191 : Blo 2131435 3198191 := bstep (se 1 (by rfl) ⟨2398643, by rfl⟩ : syracuseStep 3198191 = 4797287) B4797287
theorem B2132127 : Blo 2131435 2132127 := bstep (se 1 (by rfl) ⟨1599095, by rfl⟩ : syracuseStep 2132127 = 3198191) B3198191
theorem B3198197 : Blo 2131435 3198197 := bbase (se 5 (by rfl) ⟨149915, by rfl⟩ : syracuseStep 3198197 = 299831) (by norm_num)
theorem B2132131 : Blo 2131435 2132131 := bstep (se 1 (by rfl) ⟨1599098, by rfl⟩ : syracuseStep 2132131 = 3198197) B3198197
theorem B5763269 : Blo 2131435 5763269 := bbase (se 4 (by rfl) ⟨540306, by rfl⟩ : syracuseStep 5763269 = 1080613) (by norm_num)
theorem B15368717 : Blo 2131435 15368717 := bstep (se 3 (by rfl) ⟨2881634, by rfl⟩ : syracuseStep 15368717 = 5763269) B5763269
theorem B10245811 : Blo 2131435 10245811 := bstep (se 1 (by rfl) ⟨7684358, by rfl⟩ : syracuseStep 10245811 = 15368717) B15368717
theorem B13661081 : Blo 2131435 13661081 := bstep (se 2 (by rfl) ⟨5122905, by rfl⟩ : syracuseStep 13661081 = 10245811) B10245811
theorem B9107387 : Blo 2131435 9107387 := bstep (se 1 (by rfl) ⟨6830540, by rfl⟩ : syracuseStep 9107387 = 13661081) B13661081
theorem B6071591 : Blo 2131435 6071591 := bstep (se 1 (by rfl) ⟨4553693, by rfl⟩ : syracuseStep 6071591 = 9107387) B9107387
theorem B4047727 : Blo 2131435 4047727 := bstep (se 1 (by rfl) ⟨3035795, by rfl⟩ : syracuseStep 4047727 = 6071591) B6071591
theorem B5396969 : Blo 2131435 5396969 := bstep (se 2 (by rfl) ⟨2023863, by rfl⟩ : syracuseStep 5396969 = 4047727) B4047727
theorem B3597979 : Blo 2131435 3597979 := bstep (se 1 (by rfl) ⟨2698484, by rfl⟩ : syracuseStep 3597979 = 5396969) B5396969
theorem B4797305 : Blo 2131435 4797305 := bstep (se 2 (by rfl) ⟨1798989, by rfl⟩ : syracuseStep 4797305 = 3597979) B3597979
theorem B3198203 : Blo 2131435 3198203 := bstep (se 1 (by rfl) ⟨2398652, by rfl⟩ : syracuseStep 3198203 = 4797305) B4797305
theorem B2132135 : Blo 2131435 2132135 := bstep (se 1 (by rfl) ⟨1599101, by rfl⟩ : syracuseStep 2132135 = 3198203) B3198203
theorem B2398657 : Blo 2131435 2398657 := bbase (se 2 (by rfl) ⟨899496, by rfl⟩ : syracuseStep 2398657 = 1798993) (by norm_num)
theorem B3198209 : Blo 2131435 3198209 := bstep (se 2 (by rfl) ⟨1199328, by rfl⟩ : syracuseStep 3198209 = 2398657) B2398657
theorem B2132139 : Blo 2131435 2132139 := bstep (se 1 (by rfl) ⟨1599104, by rfl⟩ : syracuseStep 2132139 = 3198209) B3198209
theorem B5396989 : Blo 2131435 5396989 := bbase (se 3 (by rfl) ⟨1011935, by rfl⟩ : syracuseStep 5396989 = 2023871) (by norm_num)
theorem B7195985 : Blo 2131435 7195985 := bstep (se 2 (by rfl) ⟨2698494, by rfl⟩ : syracuseStep 7195985 = 5396989) B5396989
theorem B4797323 : Blo 2131435 4797323 := bstep (se 1 (by rfl) ⟨3597992, by rfl⟩ : syracuseStep 4797323 = 7195985) B7195985
theorem B3198215 : Blo 2131435 3198215 := bstep (se 1 (by rfl) ⟨2398661, by rfl⟩ : syracuseStep 3198215 = 4797323) B4797323
theorem B2132143 : Blo 2131435 2132143 := bstep (se 1 (by rfl) ⟨1599107, by rfl⟩ : syracuseStep 2132143 = 3198215) B3198215
theorem B3198221 : Blo 2131435 3198221 := bbase (se 3 (by rfl) ⟨599666, by rfl⟩ : syracuseStep 3198221 = 1199333) (by norm_num)
theorem B2132147 : Blo 2131435 2132147 := bstep (se 1 (by rfl) ⟨1599110, by rfl⟩ : syracuseStep 2132147 = 3198221) B3198221
theorem B4797341 : Blo 2131435 4797341 := bbase (se 3 (by rfl) ⟨899501, by rfl⟩ : syracuseStep 4797341 = 1799003) (by norm_num)
theorem B3198227 : Blo 2131435 3198227 := bstep (se 1 (by rfl) ⟨2398670, by rfl⟩ : syracuseStep 3198227 = 4797341) B4797341
theorem B2132151 : Blo 2131435 2132151 := bstep (se 1 (by rfl) ⟨1599113, by rfl⟩ : syracuseStep 2132151 = 3198227) B3198227
theorem B3598013 : Blo 2131435 3598013 := bbase (se 3 (by rfl) ⟨674627, by rfl⟩ : syracuseStep 3598013 = 1349255) (by norm_num)
theorem B2398675 : Blo 2131435 2398675 := bstep (se 1 (by rfl) ⟨1799006, by rfl⟩ : syracuseStep 2398675 = 3598013) B3598013
theorem B3198233 : Blo 2131435 3198233 := bstep (se 2 (by rfl) ⟨1199337, by rfl⟩ : syracuseStep 3198233 = 2398675) B2398675
theorem B2132155 : Blo 2131435 2132155 := bstep (se 1 (by rfl) ⟨1599116, by rfl⟩ : syracuseStep 2132155 = 3198233) B3198233
theorem B12143317 : Blo 2131435 12143317 := bbase (se 7 (by rfl) ⟨142304, by rfl⟩ : syracuseStep 12143317 = 284609) (by norm_num)
theorem B16191089 : Blo 2131435 16191089 := bstep (se 2 (by rfl) ⟨6071658, by rfl⟩ : syracuseStep 16191089 = 12143317) B12143317
theorem B10794059 : Blo 2131435 10794059 := bstep (se 1 (by rfl) ⟨8095544, by rfl⟩ : syracuseStep 10794059 = 16191089) B16191089
theorem B7196039 : Blo 2131435 7196039 := bstep (se 1 (by rfl) ⟨5397029, by rfl⟩ : syracuseStep 7196039 = 10794059) B10794059
theorem B4797359 : Blo 2131435 4797359 := bstep (se 1 (by rfl) ⟨3598019, by rfl⟩ : syracuseStep 4797359 = 7196039) B7196039
theorem B3198239 : Blo 2131435 3198239 := bstep (se 1 (by rfl) ⟨2398679, by rfl⟩ : syracuseStep 3198239 = 4797359) B4797359
theorem B2132159 : Blo 2131435 2132159 := bstep (se 1 (by rfl) ⟨1599119, by rfl⟩ : syracuseStep 2132159 = 3198239) B3198239
theorem B3198245 : Blo 2131435 3198245 := bbase (se 4 (by rfl) ⟨299835, by rfl⟩ : syracuseStep 3198245 = 599671) (by norm_num)
theorem B2132163 : Blo 2131435 2132163 := bstep (se 1 (by rfl) ⟨1599122, by rfl⟩ : syracuseStep 2132163 = 3198245) B3198245
theorem B2698525 : Blo 2131435 2698525 := bbase (se 3 (by rfl) ⟨505973, by rfl⟩ : syracuseStep 2698525 = 1011947) (by norm_num)
theorem B3598033 : Blo 2131435 3598033 := bstep (se 2 (by rfl) ⟨1349262, by rfl⟩ : syracuseStep 3598033 = 2698525) B2698525
theorem B4797377 : Blo 2131435 4797377 := bstep (se 2 (by rfl) ⟨1799016, by rfl⟩ : syracuseStep 4797377 = 3598033) B3598033
theorem B3198251 : Blo 2131435 3198251 := bstep (se 1 (by rfl) ⟨2398688, by rfl⟩ : syracuseStep 3198251 = 4797377) B4797377
theorem B2132167 : Blo 2131435 2132167 := bstep (se 1 (by rfl) ⟨1599125, by rfl⟩ : syracuseStep 2132167 = 3198251) B3198251
theorem B2398693 : Blo 2131435 2398693 := bbase (se 4 (by rfl) ⟨224877, by rfl⟩ : syracuseStep 2398693 = 449755) (by norm_num)
theorem B3198257 : Blo 2131435 3198257 := bstep (se 2 (by rfl) ⟨1199346, by rfl⟩ : syracuseStep 3198257 = 2398693) B2398693
theorem B2132171 : Blo 2131435 2132171 := bstep (se 1 (by rfl) ⟨1599128, by rfl⟩ : syracuseStep 2132171 = 3198257) B3198257
theorem B2561501 : Blo 2131435 2561501 := bbase (se 3 (by rfl) ⟨480281, by rfl⟩ : syracuseStep 2561501 = 960563) (by norm_num)
theorem B6830669 : Blo 2131435 6830669 := bstep (se 3 (by rfl) ⟨1280750, by rfl⟩ : syracuseStep 6830669 = 2561501) B2561501
theorem B4553779 : Blo 2131435 4553779 := bstep (se 1 (by rfl) ⟨3415334, by rfl⟩ : syracuseStep 4553779 = 6830669) B6830669
theorem B6071705 : Blo 2131435 6071705 := bstep (se 2 (by rfl) ⟨2276889, by rfl⟩ : syracuseStep 6071705 = 4553779) B4553779
theorem B4047803 : Blo 2131435 4047803 := bstep (se 1 (by rfl) ⟨3035852, by rfl⟩ : syracuseStep 4047803 = 6071705) B6071705
theorem B2698535 : Blo 2131435 2698535 := bstep (se 1 (by rfl) ⟨2023901, by rfl⟩ : syracuseStep 2698535 = 4047803) B4047803
theorem B7196093 : Blo 2131435 7196093 := bstep (se 3 (by rfl) ⟨1349267, by rfl⟩ : syracuseStep 7196093 = 2698535) B2698535
theorem B4797395 : Blo 2131435 4797395 := bstep (se 1 (by rfl) ⟨3598046, by rfl⟩ : syracuseStep 4797395 = 7196093) B7196093
theorem B3198263 : Blo 2131435 3198263 := bstep (se 1 (by rfl) ⟨2398697, by rfl⟩ : syracuseStep 3198263 = 4797395) B4797395
theorem B2132175 : Blo 2131435 2132175 := bstep (se 1 (by rfl) ⟨1599131, by rfl⟩ : syracuseStep 2132175 = 3198263) B3198263
theorem B3198269 : Blo 2131435 3198269 := bbase (se 3 (by rfl) ⟨599675, by rfl⟩ : syracuseStep 3198269 = 1199351) (by norm_num)
theorem B2132179 : Blo 2131435 2132179 := bstep (se 1 (by rfl) ⟨1599134, by rfl⟩ : syracuseStep 2132179 = 3198269) B3198269
theorem B4797413 : Blo 2131435 4797413 := bbase (se 4 (by rfl) ⟨449757, by rfl⟩ : syracuseStep 4797413 = 899515) (by norm_num)
theorem B3198275 : Blo 2131435 3198275 := bstep (se 1 (by rfl) ⟨2398706, by rfl⟩ : syracuseStep 3198275 = 4797413) B4797413
theorem B2132183 : Blo 2131435 2132183 := bstep (se 1 (by rfl) ⟨1599137, by rfl⟩ : syracuseStep 2132183 = 3198275) B3198275
theorem B5397101 : Blo 2131435 5397101 := bbase (se 3 (by rfl) ⟨1011956, by rfl⟩ : syracuseStep 5397101 = 2023913) (by norm_num)
theorem B3598067 : Blo 2131435 3598067 := bstep (se 1 (by rfl) ⟨2698550, by rfl⟩ : syracuseStep 3598067 = 5397101) B5397101
theorem B2398711 : Blo 2131435 2398711 := bstep (se 1 (by rfl) ⟨1799033, by rfl⟩ : syracuseStep 2398711 = 3598067) B3598067
theorem B3198281 : Blo 2131435 3198281 := bstep (se 2 (by rfl) ⟨1199355, by rfl⟩ : syracuseStep 3198281 = 2398711) B2398711
theorem B2132187 : Blo 2131435 2132187 := bstep (se 1 (by rfl) ⟨1599140, by rfl⟩ : syracuseStep 2132187 = 3198281) B3198281
theorem B4553813 : Blo 2131435 4553813 := bbase (se 8 (by rfl) ⟨26682, by rfl⟩ : syracuseStep 4553813 = 53365) (by norm_num)
theorem B3035875 : Blo 2131435 3035875 := bstep (se 1 (by rfl) ⟨2276906, by rfl⟩ : syracuseStep 3035875 = 4553813) B4553813
theorem B4047833 : Blo 2131435 4047833 := bstep (se 2 (by rfl) ⟨1517937, by rfl⟩ : syracuseStep 4047833 = 3035875) B3035875
theorem B10794221 : Blo 2131435 10794221 := bstep (se 3 (by rfl) ⟨2023916, by rfl⟩ : syracuseStep 10794221 = 4047833) B4047833
theorem B7196147 : Blo 2131435 7196147 := bstep (se 1 (by rfl) ⟨5397110, by rfl⟩ : syracuseStep 7196147 = 10794221) B10794221
theorem B4797431 : Blo 2131435 4797431 := bstep (se 1 (by rfl) ⟨3598073, by rfl⟩ : syracuseStep 4797431 = 7196147) B7196147
theorem B3198287 : Blo 2131435 3198287 := bstep (se 1 (by rfl) ⟨2398715, by rfl⟩ : syracuseStep 3198287 = 4797431) B4797431
theorem B2132191 : Blo 2131435 2132191 := bstep (se 1 (by rfl) ⟨1599143, by rfl⟩ : syracuseStep 2132191 = 3198287) B3198287
theorem B3198293 : Blo 2131435 3198293 := bbase (se 11 (by rfl) ⟨2342, by rfl⟩ : syracuseStep 3198293 = 4685) (by norm_num)
theorem B2132195 : Blo 2131435 2132195 := bstep (se 1 (by rfl) ⟨1599146, by rfl⟩ : syracuseStep 2132195 = 3198293) B3198293
theorem B3415373 : Blo 2131435 3415373 := bbase (se 3 (by rfl) ⟨640382, by rfl⟩ : syracuseStep 3415373 = 1280765) (by norm_num)
theorem B2276915 : Blo 2131435 2276915 := bstep (se 1 (by rfl) ⟨1707686, by rfl⟩ : syracuseStep 2276915 = 3415373) B3415373
theorem B6071773 : Blo 2131435 6071773 := bstep (se 3 (by rfl) ⟨1138457, by rfl⟩ : syracuseStep 6071773 = 2276915) B2276915
theorem B8095697 : Blo 2131435 8095697 := bstep (se 2 (by rfl) ⟨3035886, by rfl⟩ : syracuseStep 8095697 = 6071773) B6071773
theorem B5397131 : Blo 2131435 5397131 := bstep (se 1 (by rfl) ⟨4047848, by rfl⟩ : syracuseStep 5397131 = 8095697) B8095697
theorem B3598087 : Blo 2131435 3598087 := bstep (se 1 (by rfl) ⟨2698565, by rfl⟩ : syracuseStep 3598087 = 5397131) B5397131
theorem B4797449 : Blo 2131435 4797449 := bstep (se 2 (by rfl) ⟨1799043, by rfl⟩ : syracuseStep 4797449 = 3598087) B3598087
theorem B3198299 : Blo 2131435 3198299 := bstep (se 1 (by rfl) ⟨2398724, by rfl⟩ : syracuseStep 3198299 = 4797449) B4797449
theorem B2132199 : Blo 2131435 2132199 := bstep (se 1 (by rfl) ⟨1599149, by rfl⟩ : syracuseStep 2132199 = 3198299) B3198299
theorem B2398729 : Blo 2131435 2398729 := bbase (se 2 (by rfl) ⟨899523, by rfl⟩ : syracuseStep 2398729 = 1799047) (by norm_num)
theorem B3198305 : Blo 2131435 3198305 := bstep (se 2 (by rfl) ⟨1199364, by rfl⟩ : syracuseStep 3198305 = 2398729) B2398729
theorem B2132203 : Blo 2131435 2132203 := bstep (se 1 (by rfl) ⟨1599152, by rfl⟩ : syracuseStep 2132203 = 3198305) B3198305
theorem B4322597 : Blo 2131435 4322597 := bbase (se 4 (by rfl) ⟨405243, by rfl⟩ : syracuseStep 4322597 = 810487) (by norm_num)
theorem B46107701 : Blo 2131435 46107701 := bstep (se 5 (by rfl) ⟨2161298, by rfl⟩ : syracuseStep 46107701 = 4322597) B4322597
theorem B30738467 : Blo 2131435 30738467 := bstep (se 1 (by rfl) ⟨23053850, by rfl⟩ : syracuseStep 30738467 = 46107701) B46107701
theorem B20492311 : Blo 2131435 20492311 := bstep (se 1 (by rfl) ⟨15369233, by rfl⟩ : syracuseStep 20492311 = 30738467) B30738467
theorem B27323081 : Blo 2131435 27323081 := bstep (se 2 (by rfl) ⟨10246155, by rfl⟩ : syracuseStep 27323081 = 20492311) B20492311
theorem B18215387 : Blo 2131435 18215387 := bstep (se 1 (by rfl) ⟨13661540, by rfl⟩ : syracuseStep 18215387 = 27323081) B27323081
theorem B12143591 : Blo 2131435 12143591 := bstep (se 1 (by rfl) ⟨9107693, by rfl⟩ : syracuseStep 12143591 = 18215387) B18215387
theorem B8095727 : Blo 2131435 8095727 := bstep (se 1 (by rfl) ⟨6071795, by rfl⟩ : syracuseStep 8095727 = 12143591) B12143591
theorem B5397151 : Blo 2131435 5397151 := bstep (se 1 (by rfl) ⟨4047863, by rfl⟩ : syracuseStep 5397151 = 8095727) B8095727
theorem B7196201 : Blo 2131435 7196201 := bstep (se 2 (by rfl) ⟨2698575, by rfl⟩ : syracuseStep 7196201 = 5397151) B5397151
theorem B4797467 : Blo 2131435 4797467 := bstep (se 1 (by rfl) ⟨3598100, by rfl⟩ : syracuseStep 4797467 = 7196201) B7196201
theorem B3198311 : Blo 2131435 3198311 := bstep (se 1 (by rfl) ⟨2398733, by rfl⟩ : syracuseStep 3198311 = 4797467) B4797467
theorem B2132207 : Blo 2131435 2132207 := bstep (se 1 (by rfl) ⟨1599155, by rfl⟩ : syracuseStep 2132207 = 3198311) B3198311
theorem B3198317 : Blo 2131435 3198317 := bbase (se 3 (by rfl) ⟨599684, by rfl⟩ : syracuseStep 3198317 = 1199369) (by norm_num)
theorem B2132211 : Blo 2131435 2132211 := bstep (se 1 (by rfl) ⟨1599158, by rfl⟩ : syracuseStep 2132211 = 3198317) B3198317
theorem B4797485 : Blo 2131435 4797485 := bbase (se 3 (by rfl) ⟨899528, by rfl⟩ : syracuseStep 4797485 = 1799057) (by norm_num)
theorem B3198323 : Blo 2131435 3198323 := bstep (se 1 (by rfl) ⟨2398742, by rfl⟩ : syracuseStep 3198323 = 4797485) B4797485
theorem B2132215 : Blo 2131435 2132215 := bstep (se 1 (by rfl) ⟨1599161, by rfl⟩ : syracuseStep 2132215 = 3198323) B3198323
theorem B13661621 : Blo 2131435 13661621 := bbase (se 5 (by rfl) ⟨640388, by rfl⟩ : syracuseStep 13661621 = 1280777) (by norm_num)
theorem B9107747 : Blo 2131435 9107747 := bstep (se 1 (by rfl) ⟨6830810, by rfl⟩ : syracuseStep 9107747 = 13661621) B13661621
theorem B6071831 : Blo 2131435 6071831 := bstep (se 1 (by rfl) ⟨4553873, by rfl⟩ : syracuseStep 6071831 = 9107747) B9107747
theorem B4047887 : Blo 2131435 4047887 := bstep (se 1 (by rfl) ⟨3035915, by rfl⟩ : syracuseStep 4047887 = 6071831) B6071831
theorem B2698591 : Blo 2131435 2698591 := bstep (se 1 (by rfl) ⟨2023943, by rfl⟩ : syracuseStep 2698591 = 4047887) B4047887
theorem B3598121 : Blo 2131435 3598121 := bstep (se 2 (by rfl) ⟨1349295, by rfl⟩ : syracuseStep 3598121 = 2698591) B2698591
theorem B2398747 : Blo 2131435 2398747 := bstep (se 1 (by rfl) ⟨1799060, by rfl⟩ : syracuseStep 2398747 = 3598121) B3598121
theorem B3198329 : Blo 2131435 3198329 := bstep (se 2 (by rfl) ⟨1199373, by rfl⟩ : syracuseStep 3198329 = 2398747) B2398747
theorem B2132219 : Blo 2131435 2132219 := bstep (se 1 (by rfl) ⟨1599164, by rfl⟩ : syracuseStep 2132219 = 3198329) B3198329
theorem B6830821 : Blo 2131435 6830821 := bbase (se 4 (by rfl) ⟨640389, by rfl⟩ : syracuseStep 6830821 = 1280779) (by norm_num)
theorem B36431045 : Blo 2131435 36431045 := bstep (se 4 (by rfl) ⟨3415410, by rfl⟩ : syracuseStep 36431045 = 6830821) B6830821
theorem B24287363 : Blo 2131435 24287363 := bstep (se 1 (by rfl) ⟨18215522, by rfl⟩ : syracuseStep 24287363 = 36431045) B36431045
theorem B16191575 : Blo 2131435 16191575 := bstep (se 1 (by rfl) ⟨12143681, by rfl⟩ : syracuseStep 16191575 = 24287363) B24287363
theorem B10794383 : Blo 2131435 10794383 := bstep (se 1 (by rfl) ⟨8095787, by rfl⟩ : syracuseStep 10794383 = 16191575) B16191575
theorem B7196255 : Blo 2131435 7196255 := bstep (se 1 (by rfl) ⟨5397191, by rfl⟩ : syracuseStep 7196255 = 10794383) B10794383
theorem B4797503 : Blo 2131435 4797503 := bstep (se 1 (by rfl) ⟨3598127, by rfl⟩ : syracuseStep 4797503 = 7196255) B7196255
theorem B3198335 : Blo 2131435 3198335 := bstep (se 1 (by rfl) ⟨2398751, by rfl⟩ : syracuseStep 3198335 = 4797503) B4797503
theorem B2132223 : Blo 2131435 2132223 := bstep (se 1 (by rfl) ⟨1599167, by rfl⟩ : syracuseStep 2132223 = 3198335) B3198335
theorem B3198341 : Blo 2131435 3198341 := bbase (se 4 (by rfl) ⟨299844, by rfl⟩ : syracuseStep 3198341 = 599689) (by norm_num)
theorem B2132227 : Blo 2131435 2132227 := bstep (se 1 (by rfl) ⟨1599170, by rfl⟩ : syracuseStep 2132227 = 3198341) B3198341
theorem B3598141 : Blo 2131435 3598141 := bbase (se 3 (by rfl) ⟨674651, by rfl⟩ : syracuseStep 3598141 = 1349303) (by norm_num)
theorem B4797521 : Blo 2131435 4797521 := bstep (se 2 (by rfl) ⟨1799070, by rfl⟩ : syracuseStep 4797521 = 3598141) B3598141
theorem B3198347 : Blo 2131435 3198347 := bstep (se 1 (by rfl) ⟨2398760, by rfl⟩ : syracuseStep 3198347 = 4797521) B4797521
theorem B2132231 : Blo 2131435 2132231 := bstep (se 1 (by rfl) ⟨1599173, by rfl⟩ : syracuseStep 2132231 = 3198347) B3198347
theorem B2398765 : Blo 2131435 2398765 := bbase (se 3 (by rfl) ⟨449768, by rfl⟩ : syracuseStep 2398765 = 899537) (by norm_num)
theorem B3198353 : Blo 2131435 3198353 := bstep (se 2 (by rfl) ⟨1199382, by rfl⟩ : syracuseStep 3198353 = 2398765) B2398765
theorem B2132235 : Blo 2131435 2132235 := bstep (se 1 (by rfl) ⟨1599176, by rfl⟩ : syracuseStep 2132235 = 3198353) B3198353
theorem B7196309 : Blo 2131435 7196309 := bbase (se 6 (by rfl) ⟨168663, by rfl⟩ : syracuseStep 7196309 = 337327) (by norm_num)
theorem B4797539 : Blo 2131435 4797539 := bstep (se 1 (by rfl) ⟨3598154, by rfl⟩ : syracuseStep 4797539 = 7196309) B7196309
theorem B3198359 : Blo 2131435 3198359 := bstep (se 1 (by rfl) ⟨2398769, by rfl⟩ : syracuseStep 3198359 = 4797539) B4797539
theorem B2132239 : Blo 2131435 2132239 := bstep (se 1 (by rfl) ⟨1599179, by rfl⟩ : syracuseStep 2132239 = 3198359) B3198359
theorem B3198365 : Blo 2131435 3198365 := bbase (se 3 (by rfl) ⟨599693, by rfl⟩ : syracuseStep 3198365 = 1199387) (by norm_num)
theorem B2132243 : Blo 2131435 2132243 := bstep (se 1 (by rfl) ⟨1599182, by rfl⟩ : syracuseStep 2132243 = 3198365) B3198365
theorem B4797557 : Blo 2131435 4797557 := bbase (se 5 (by rfl) ⟨224885, by rfl⟩ : syracuseStep 4797557 = 449771) (by norm_num)
theorem B3198371 : Blo 2131435 3198371 := bstep (se 1 (by rfl) ⟨2398778, by rfl⟩ : syracuseStep 3198371 = 4797557) B4797557
theorem B2132247 : Blo 2131435 2132247 := bstep (se 1 (by rfl) ⟨1599185, by rfl⟩ : syracuseStep 2132247 = 3198371) B3198371
theorem B18215765 : Blo 2131435 18215765 := bbase (se 9 (by rfl) ⟨53366, by rfl⟩ : syracuseStep 18215765 = 106733) (by norm_num)
theorem B12143843 : Blo 2131435 12143843 := bstep (se 1 (by rfl) ⟨9107882, by rfl⟩ : syracuseStep 12143843 = 18215765) B18215765
theorem B8095895 : Blo 2131435 8095895 := bstep (se 1 (by rfl) ⟨6071921, by rfl⟩ : syracuseStep 8095895 = 12143843) B12143843
theorem B5397263 : Blo 2131435 5397263 := bstep (se 1 (by rfl) ⟨4047947, by rfl⟩ : syracuseStep 5397263 = 8095895) B8095895
theorem B3598175 : Blo 2131435 3598175 := bstep (se 1 (by rfl) ⟨2698631, by rfl⟩ : syracuseStep 3598175 = 5397263) B5397263
theorem B2398783 : Blo 2131435 2398783 := bstep (se 1 (by rfl) ⟨1799087, by rfl⟩ : syracuseStep 2398783 = 3598175) B3598175
theorem B3198377 : Blo 2131435 3198377 := bstep (se 2 (by rfl) ⟨1199391, by rfl⟩ : syracuseStep 3198377 = 2398783) B2398783
theorem B2132251 : Blo 2131435 2132251 := bstep (se 1 (by rfl) ⟨1599188, by rfl⟩ : syracuseStep 2132251 = 3198377) B3198377
theorem B8095909 : Blo 2131435 8095909 := bbase (se 4 (by rfl) ⟨758991, by rfl⟩ : syracuseStep 8095909 = 1517983) (by norm_num)
theorem B10794545 : Blo 2131435 10794545 := bstep (se 2 (by rfl) ⟨4047954, by rfl⟩ : syracuseStep 10794545 = 8095909) B8095909
theorem B7196363 : Blo 2131435 7196363 := bstep (se 1 (by rfl) ⟨5397272, by rfl⟩ : syracuseStep 7196363 = 10794545) B10794545
theorem B4797575 : Blo 2131435 4797575 := bstep (se 1 (by rfl) ⟨3598181, by rfl⟩ : syracuseStep 4797575 = 7196363) B7196363
theorem B3198383 : Blo 2131435 3198383 := bstep (se 1 (by rfl) ⟨2398787, by rfl⟩ : syracuseStep 3198383 = 4797575) B4797575
theorem B2132255 : Blo 2131435 2132255 := bstep (se 1 (by rfl) ⟨1599191, by rfl⟩ : syracuseStep 2132255 = 3198383) B3198383
theorem B3198389 : Blo 2131435 3198389 := bbase (se 5 (by rfl) ⟨149924, by rfl⟩ : syracuseStep 3198389 = 299849) (by norm_num)
theorem B2132259 : Blo 2131435 2132259 := bstep (se 1 (by rfl) ⟨1599194, by rfl⟩ : syracuseStep 2132259 = 3198389) B3198389
theorem B5397293 : Blo 2131435 5397293 := bbase (se 3 (by rfl) ⟨1011992, by rfl⟩ : syracuseStep 5397293 = 2023985) (by norm_num)
theorem B3598195 : Blo 2131435 3598195 := bstep (se 1 (by rfl) ⟨2698646, by rfl⟩ : syracuseStep 3598195 = 5397293) B5397293
theorem B4797593 : Blo 2131435 4797593 := bstep (se 2 (by rfl) ⟨1799097, by rfl⟩ : syracuseStep 4797593 = 3598195) B3598195
theorem B3198395 : Blo 2131435 3198395 := bstep (se 1 (by rfl) ⟨2398796, by rfl⟩ : syracuseStep 3198395 = 4797593) B4797593
theorem B2132263 : Blo 2131435 2132263 := bstep (se 1 (by rfl) ⟨1599197, by rfl⟩ : syracuseStep 2132263 = 3198395) B3198395
theorem B2398801 : Blo 2131435 2398801 := bbase (se 2 (by rfl) ⟨899550, by rfl⟩ : syracuseStep 2398801 = 1799101) (by norm_num)
theorem B3198401 : Blo 2131435 3198401 := bstep (se 2 (by rfl) ⟨1199400, by rfl⟩ : syracuseStep 3198401 = 2398801) B2398801
theorem B2132267 : Blo 2131435 2132267 := bstep (se 1 (by rfl) ⟨1599200, by rfl⟩ : syracuseStep 2132267 = 3198401) B3198401
theorem B3035989 : Blo 2131435 3035989 := bbase (se 9 (by rfl) ⟨8894, by rfl⟩ : syracuseStep 3035989 = 17789) (by norm_num)
theorem B4047985 : Blo 2131435 4047985 := bstep (se 2 (by rfl) ⟨1517994, by rfl⟩ : syracuseStep 4047985 = 3035989) B3035989
theorem B5397313 : Blo 2131435 5397313 := bstep (se 2 (by rfl) ⟨2023992, by rfl⟩ : syracuseStep 5397313 = 4047985) B4047985
theorem B7196417 : Blo 2131435 7196417 := bstep (se 2 (by rfl) ⟨2698656, by rfl⟩ : syracuseStep 7196417 = 5397313) B5397313
theorem B4797611 : Blo 2131435 4797611 := bstep (se 1 (by rfl) ⟨3598208, by rfl⟩ : syracuseStep 4797611 = 7196417) B7196417
theorem B3198407 : Blo 2131435 3198407 := bstep (se 1 (by rfl) ⟨2398805, by rfl⟩ : syracuseStep 3198407 = 4797611) B4797611
theorem B2132271 : Blo 2131435 2132271 := bstep (se 1 (by rfl) ⟨1599203, by rfl⟩ : syracuseStep 2132271 = 3198407) B3198407
theorem B3198413 : Blo 2131435 3198413 := bbase (se 3 (by rfl) ⟨599702, by rfl⟩ : syracuseStep 3198413 = 1199405) (by norm_num)
theorem B2132275 : Blo 2131435 2132275 := bstep (se 1 (by rfl) ⟨1599206, by rfl⟩ : syracuseStep 2132275 = 3198413) B3198413
theorem B4797629 : Blo 2131435 4797629 := bbase (se 3 (by rfl) ⟨899555, by rfl⟩ : syracuseStep 4797629 = 1799111) (by norm_num)
theorem B3198419 : Blo 2131435 3198419 := bstep (se 1 (by rfl) ⟨2398814, by rfl⟩ : syracuseStep 3198419 = 4797629) B4797629
theorem B2132279 : Blo 2131435 2132279 := bstep (se 1 (by rfl) ⟨1599209, by rfl⟩ : syracuseStep 2132279 = 3198419) B3198419
theorem B3598229 : Blo 2131435 3598229 := bbase (se 6 (by rfl) ⟨84333, by rfl⟩ : syracuseStep 3598229 = 168667) (by norm_num)
theorem B2398819 : Blo 2131435 2398819 := bstep (se 1 (by rfl) ⟨1799114, by rfl⟩ : syracuseStep 2398819 = 3598229) B3598229
theorem B3198425 : Blo 2131435 3198425 := bstep (se 2 (by rfl) ⟨1199409, by rfl⟩ : syracuseStep 3198425 = 2398819) B2398819
theorem B2132283 : Blo 2131435 2132283 := bstep (se 1 (by rfl) ⟨1599212, by rfl⟩ : syracuseStep 2132283 = 3198425) B3198425
theorem B3842453 : Blo 2131435 3842453 := bbase (se 6 (by rfl) ⟨90057, by rfl⟩ : syracuseStep 3842453 = 180115) (by norm_num)
theorem B2561635 : Blo 2131435 2561635 := bstep (se 1 (by rfl) ⟨1921226, by rfl⟩ : syracuseStep 2561635 = 3842453) B3842453
theorem B13662053 : Blo 2131435 13662053 := bstep (se 4 (by rfl) ⟨1280817, by rfl⟩ : syracuseStep 13662053 = 2561635) B2561635
theorem B9108035 : Blo 2131435 9108035 := bstep (se 1 (by rfl) ⟨6831026, by rfl⟩ : syracuseStep 9108035 = 13662053) B13662053
theorem B6072023 : Blo 2131435 6072023 := bstep (se 1 (by rfl) ⟨4554017, by rfl⟩ : syracuseStep 6072023 = 9108035) B9108035
theorem B16192061 : Blo 2131435 16192061 := bstep (se 3 (by rfl) ⟨3036011, by rfl⟩ : syracuseStep 16192061 = 6072023) B6072023
theorem B10794707 : Blo 2131435 10794707 := bstep (se 1 (by rfl) ⟨8096030, by rfl⟩ : syracuseStep 10794707 = 16192061) B16192061
theorem B7196471 : Blo 2131435 7196471 := bstep (se 1 (by rfl) ⟨5397353, by rfl⟩ : syracuseStep 7196471 = 10794707) B10794707
theorem B4797647 : Blo 2131435 4797647 := bstep (se 1 (by rfl) ⟨3598235, by rfl⟩ : syracuseStep 4797647 = 7196471) B7196471
theorem B3198431 : Blo 2131435 3198431 := bstep (se 1 (by rfl) ⟨2398823, by rfl⟩ : syracuseStep 3198431 = 4797647) B4797647
theorem B2132287 : Blo 2131435 2132287 := bstep (se 1 (by rfl) ⟨1599215, by rfl⟩ : syracuseStep 2132287 = 3198431) B3198431
theorem B3198437 : Blo 2131435 3198437 := bbase (se 4 (by rfl) ⟨299853, by rfl⟩ : syracuseStep 3198437 = 599707) (by norm_num)
theorem B2132291 : Blo 2131435 2132291 := bstep (se 1 (by rfl) ⟨1599218, by rfl⟩ : syracuseStep 2132291 = 3198437) B3198437
theorem B3894893 : Blo 2131435 3894893 := bbase (se 3 (by rfl) ⟨730292, by rfl⟩ : syracuseStep 3894893 = 1460585) (by norm_num)
theorem B2596595 : Blo 2131435 2596595 := bstep (se 1 (by rfl) ⟨1947446, by rfl⟩ : syracuseStep 2596595 = 3894893) B3894893
theorem B6924253 : Blo 2131435 6924253 := bstep (se 3 (by rfl) ⟨1298297, by rfl⟩ : syracuseStep 6924253 = 2596595) B2596595
theorem B9232337 : Blo 2131435 9232337 := bstep (se 2 (by rfl) ⟨3462126, by rfl⟩ : syracuseStep 9232337 = 6924253) B6924253
theorem B24619565 : Blo 2131435 24619565 := bstep (se 3 (by rfl) ⟨4616168, by rfl⟩ : syracuseStep 24619565 = 9232337) B9232337
theorem B16413043 : Blo 2131435 16413043 := bstep (se 1 (by rfl) ⟨12309782, by rfl⟩ : syracuseStep 16413043 = 24619565) B24619565
theorem B21884057 : Blo 2131435 21884057 := bstep (se 2 (by rfl) ⟨8206521, by rfl⟩ : syracuseStep 21884057 = 16413043) B16413043
theorem B14589371 : Blo 2131435 14589371 := bstep (se 1 (by rfl) ⟨10942028, by rfl⟩ : syracuseStep 14589371 = 21884057) B21884057
theorem B9726247 : Blo 2131435 9726247 := bstep (se 1 (by rfl) ⟨7294685, by rfl⟩ : syracuseStep 9726247 = 14589371) B14589371
theorem B51873317 : Blo 2131435 51873317 := bstep (se 4 (by rfl) ⟨4863123, by rfl⟩ : syracuseStep 51873317 = 9726247) B9726247
theorem B34582211 : Blo 2131435 34582211 := bstep (se 1 (by rfl) ⟨25936658, by rfl⟩ : syracuseStep 34582211 = 51873317) B51873317
theorem B23054807 : Blo 2131435 23054807 := bstep (se 1 (by rfl) ⟨17291105, by rfl⟩ : syracuseStep 23054807 = 34582211) B34582211
theorem B15369871 : Blo 2131435 15369871 := bstep (se 1 (by rfl) ⟨11527403, by rfl⟩ : syracuseStep 15369871 = 23054807) B23054807
theorem B20493161 : Blo 2131435 20493161 := bstep (se 2 (by rfl) ⟨7684935, by rfl⟩ : syracuseStep 20493161 = 15369871) B15369871
theorem B13662107 : Blo 2131435 13662107 := bstep (se 1 (by rfl) ⟨10246580, by rfl⟩ : syracuseStep 13662107 = 20493161) B20493161
theorem B9108071 : Blo 2131435 9108071 := bstep (se 1 (by rfl) ⟨6831053, by rfl⟩ : syracuseStep 9108071 = 13662107) B13662107
theorem B6072047 : Blo 2131435 6072047 := bstep (se 1 (by rfl) ⟨4554035, by rfl⟩ : syracuseStep 6072047 = 9108071) B9108071
theorem B4048031 : Blo 2131435 4048031 := bstep (se 1 (by rfl) ⟨3036023, by rfl⟩ : syracuseStep 4048031 = 6072047) B6072047
theorem B2698687 : Blo 2131435 2698687 := bstep (se 1 (by rfl) ⟨2024015, by rfl⟩ : syracuseStep 2698687 = 4048031) B4048031
theorem B3598249 : Blo 2131435 3598249 := bstep (se 2 (by rfl) ⟨1349343, by rfl⟩ : syracuseStep 3598249 = 2698687) B2698687
theorem B4797665 : Blo 2131435 4797665 := bstep (se 2 (by rfl) ⟨1799124, by rfl⟩ : syracuseStep 4797665 = 3598249) B3598249
theorem B3198443 : Blo 2131435 3198443 := bstep (se 1 (by rfl) ⟨2398832, by rfl⟩ : syracuseStep 3198443 = 4797665) B4797665
theorem B2132295 : Blo 2131435 2132295 := bstep (se 1 (by rfl) ⟨1599221, by rfl⟩ : syracuseStep 2132295 = 3198443) B3198443
theorem B2398837 : Blo 2131435 2398837 := bbase (se 5 (by rfl) ⟨112445, by rfl⟩ : syracuseStep 2398837 = 224891) (by norm_num)
theorem B3198449 : Blo 2131435 3198449 := bstep (se 2 (by rfl) ⟨1199418, by rfl⟩ : syracuseStep 3198449 = 2398837) B2398837
theorem B2132299 : Blo 2131435 2132299 := bstep (se 1 (by rfl) ⟨1599224, by rfl⟩ : syracuseStep 2132299 = 3198449) B3198449
theorem B2698697 : Blo 2131435 2698697 := bbase (se 2 (by rfl) ⟨1012011, by rfl⟩ : syracuseStep 2698697 = 2024023) (by norm_num)
theorem B7196525 : Blo 2131435 7196525 := bstep (se 3 (by rfl) ⟨1349348, by rfl⟩ : syracuseStep 7196525 = 2698697) B2698697
theorem B4797683 : Blo 2131435 4797683 := bstep (se 1 (by rfl) ⟨3598262, by rfl⟩ : syracuseStep 4797683 = 7196525) B7196525
theorem B3198455 : Blo 2131435 3198455 := bstep (se 1 (by rfl) ⟨2398841, by rfl⟩ : syracuseStep 3198455 = 4797683) B4797683
theorem B2132303 : Blo 2131435 2132303 := bstep (se 1 (by rfl) ⟨1599227, by rfl⟩ : syracuseStep 2132303 = 3198455) B3198455
theorem B3198461 : Blo 2131435 3198461 := bbase (se 3 (by rfl) ⟨599711, by rfl⟩ : syracuseStep 3198461 = 1199423) (by norm_num)
theorem B2132307 : Blo 2131435 2132307 := bstep (se 1 (by rfl) ⟨1599230, by rfl⟩ : syracuseStep 2132307 = 3198461) B3198461
theorem B4797701 : Blo 2131435 4797701 := bbase (se 4 (by rfl) ⟨449784, by rfl⟩ : syracuseStep 4797701 = 899569) (by norm_num)
theorem B3198467 : Blo 2131435 3198467 := bstep (se 1 (by rfl) ⟨2398850, by rfl⟩ : syracuseStep 3198467 = 4797701) B4797701
theorem B2132311 : Blo 2131435 2132311 := bstep (se 1 (by rfl) ⟨1599233, by rfl⟩ : syracuseStep 2132311 = 3198467) B3198467
theorem B4048069 : Blo 2131435 4048069 := bbase (se 4 (by rfl) ⟨379506, by rfl⟩ : syracuseStep 4048069 = 759013) (by norm_num)
theorem B5397425 : Blo 2131435 5397425 := bstep (se 2 (by rfl) ⟨2024034, by rfl⟩ : syracuseStep 5397425 = 4048069) B4048069
theorem B3598283 : Blo 2131435 3598283 := bstep (se 1 (by rfl) ⟨2698712, by rfl⟩ : syracuseStep 3598283 = 5397425) B5397425
theorem B2398855 : Blo 2131435 2398855 := bstep (se 1 (by rfl) ⟨1799141, by rfl⟩ : syracuseStep 2398855 = 3598283) B3598283
theorem B3198473 : Blo 2131435 3198473 := bstep (se 2 (by rfl) ⟨1199427, by rfl⟩ : syracuseStep 3198473 = 2398855) B2398855
theorem B2132315 : Blo 2131435 2132315 := bstep (se 1 (by rfl) ⟨1599236, by rfl⟩ : syracuseStep 2132315 = 3198473) B3198473
theorem B10794869 : Blo 2131435 10794869 := bbase (se 5 (by rfl) ⟨506009, by rfl⟩ : syracuseStep 10794869 = 1012019) (by norm_num)
theorem B7196579 : Blo 2131435 7196579 := bstep (se 1 (by rfl) ⟨5397434, by rfl⟩ : syracuseStep 7196579 = 10794869) B10794869
theorem B4797719 : Blo 2131435 4797719 := bstep (se 1 (by rfl) ⟨3598289, by rfl⟩ : syracuseStep 4797719 = 7196579) B7196579
theorem B3198479 : Blo 2131435 3198479 := bstep (se 1 (by rfl) ⟨2398859, by rfl⟩ : syracuseStep 3198479 = 4797719) B4797719
theorem B2132319 : Blo 2131435 2132319 := bstep (se 1 (by rfl) ⟨1599239, by rfl⟩ : syracuseStep 2132319 = 3198479) B3198479
theorem B3198485 : Blo 2131435 3198485 := bbase (se 6 (by rfl) ⟨74964, by rfl⟩ : syracuseStep 3198485 = 149929) (by norm_num)
theorem B2132323 : Blo 2131435 2132323 := bstep (se 1 (by rfl) ⟨1599242, by rfl⟩ : syracuseStep 2132323 = 3198485) B3198485
theorem B3842525 : Blo 2131435 3842525 := bbase (se 3 (by rfl) ⟨720473, by rfl⟩ : syracuseStep 3842525 = 1440947) (by norm_num)
theorem B10246733 : Blo 2131435 10246733 := bstep (se 3 (by rfl) ⟨1921262, by rfl⟩ : syracuseStep 10246733 = 3842525) B3842525
theorem B6831155 : Blo 2131435 6831155 := bstep (se 1 (by rfl) ⟨5123366, by rfl⟩ : syracuseStep 6831155 = 10246733) B10246733
theorem B18216413 : Blo 2131435 18216413 := bstep (se 3 (by rfl) ⟨3415577, by rfl⟩ : syracuseStep 18216413 = 6831155) B6831155
theorem B12144275 : Blo 2131435 12144275 := bstep (se 1 (by rfl) ⟨9108206, by rfl⟩ : syracuseStep 12144275 = 18216413) B18216413
theorem B8096183 : Blo 2131435 8096183 := bstep (se 1 (by rfl) ⟨6072137, by rfl⟩ : syracuseStep 8096183 = 12144275) B12144275
theorem B5397455 : Blo 2131435 5397455 := bstep (se 1 (by rfl) ⟨4048091, by rfl⟩ : syracuseStep 5397455 = 8096183) B8096183
theorem B3598303 : Blo 2131435 3598303 := bstep (se 1 (by rfl) ⟨2698727, by rfl⟩ : syracuseStep 3598303 = 5397455) B5397455
theorem B4797737 : Blo 2131435 4797737 := bstep (se 2 (by rfl) ⟨1799151, by rfl⟩ : syracuseStep 4797737 = 3598303) B3598303
theorem B3198491 : Blo 2131435 3198491 := bstep (se 1 (by rfl) ⟨2398868, by rfl⟩ : syracuseStep 3198491 = 4797737) B4797737
theorem B2132327 : Blo 2131435 2132327 := bstep (se 1 (by rfl) ⟨1599245, by rfl⟩ : syracuseStep 2132327 = 3198491) B3198491
theorem B2398873 : Blo 2131435 2398873 := bbase (se 2 (by rfl) ⟨899577, by rfl⟩ : syracuseStep 2398873 = 1799155) (by norm_num)
theorem B3198497 : Blo 2131435 3198497 := bstep (se 2 (by rfl) ⟨1199436, by rfl⟩ : syracuseStep 3198497 = 2398873) B2398873
theorem B2132331 : Blo 2131435 2132331 := bstep (se 1 (by rfl) ⟨1599248, by rfl⟩ : syracuseStep 2132331 = 3198497) B3198497
theorem B8096213 : Blo 2131435 8096213 := bbase (se 7 (by rfl) ⟨94877, by rfl⟩ : syracuseStep 8096213 = 189755) (by norm_num)
theorem B5397475 : Blo 2131435 5397475 := bstep (se 1 (by rfl) ⟨4048106, by rfl⟩ : syracuseStep 5397475 = 8096213) B8096213
theorem B7196633 : Blo 2131435 7196633 := bstep (se 2 (by rfl) ⟨2698737, by rfl⟩ : syracuseStep 7196633 = 5397475) B5397475
theorem B4797755 : Blo 2131435 4797755 := bstep (se 1 (by rfl) ⟨3598316, by rfl⟩ : syracuseStep 4797755 = 7196633) B7196633
theorem B3198503 : Blo 2131435 3198503 := bstep (se 1 (by rfl) ⟨2398877, by rfl⟩ : syracuseStep 3198503 = 4797755) B4797755
theorem B2132335 : Blo 2131435 2132335 := bstep (se 1 (by rfl) ⟨1599251, by rfl⟩ : syracuseStep 2132335 = 3198503) B3198503
theorem B3198509 : Blo 2131435 3198509 := bbase (se 3 (by rfl) ⟨599720, by rfl⟩ : syracuseStep 3198509 = 1199441) (by norm_num)
theorem B2132339 : Blo 2131435 2132339 := bstep (se 1 (by rfl) ⟨1599254, by rfl⟩ : syracuseStep 2132339 = 3198509) B3198509
theorem B4797773 : Blo 2131435 4797773 := bbase (se 3 (by rfl) ⟨899582, by rfl⟩ : syracuseStep 4797773 = 1799165) (by norm_num)
theorem B3198515 : Blo 2131435 3198515 := bstep (se 1 (by rfl) ⟨2398886, by rfl⟩ : syracuseStep 3198515 = 4797773) B4797773
theorem B2132343 : Blo 2131435 2132343 := bstep (se 1 (by rfl) ⟨1599257, by rfl⟩ : syracuseStep 2132343 = 3198515) B3198515
theorem B2698753 : Blo 2131435 2698753 := bbase (se 2 (by rfl) ⟨1012032, by rfl⟩ : syracuseStep 2698753 = 2024065) (by norm_num)
theorem B3598337 : Blo 2131435 3598337 := bstep (se 2 (by rfl) ⟨1349376, by rfl⟩ : syracuseStep 3598337 = 2698753) B2698753
theorem B2398891 : Blo 2131435 2398891 := bstep (se 1 (by rfl) ⟨1799168, by rfl⟩ : syracuseStep 2398891 = 3598337) B3598337
theorem B3198521 : Blo 2131435 3198521 := bstep (se 2 (by rfl) ⟨1199445, by rfl⟩ : syracuseStep 3198521 = 2398891) B2398891
theorem B2132347 : Blo 2131435 2132347 := bstep (se 1 (by rfl) ⟨1599260, by rfl⟩ : syracuseStep 2132347 = 3198521) B3198521
theorem B2277077 : Blo 2131435 2277077 := bbase (se 7 (by rfl) ⟨26684, by rfl⟩ : syracuseStep 2277077 = 53369) (by norm_num)
theorem B24288821 : Blo 2131435 24288821 := bstep (se 5 (by rfl) ⟨1138538, by rfl⟩ : syracuseStep 24288821 = 2277077) B2277077
theorem B16192547 : Blo 2131435 16192547 := bstep (se 1 (by rfl) ⟨12144410, by rfl⟩ : syracuseStep 16192547 = 24288821) B24288821
theorem B10795031 : Blo 2131435 10795031 := bstep (se 1 (by rfl) ⟨8096273, by rfl⟩ : syracuseStep 10795031 = 16192547) B16192547
theorem B7196687 : Blo 2131435 7196687 := bstep (se 1 (by rfl) ⟨5397515, by rfl⟩ : syracuseStep 7196687 = 10795031) B10795031
theorem B4797791 : Blo 2131435 4797791 := bstep (se 1 (by rfl) ⟨3598343, by rfl⟩ : syracuseStep 4797791 = 7196687) B7196687
theorem B3198527 : Blo 2131435 3198527 := bstep (se 1 (by rfl) ⟨2398895, by rfl⟩ : syracuseStep 3198527 = 4797791) B4797791
theorem B2132351 : Blo 2131435 2132351 := bstep (se 1 (by rfl) ⟨1599263, by rfl⟩ : syracuseStep 2132351 = 3198527) B3198527
theorem B3198533 : Blo 2131435 3198533 := bbase (se 4 (by rfl) ⟨299862, by rfl⟩ : syracuseStep 3198533 = 599725) (by norm_num)
theorem B2132355 : Blo 2131435 2132355 := bstep (se 1 (by rfl) ⟨1599266, by rfl⟩ : syracuseStep 2132355 = 3198533) B3198533
theorem B3598357 : Blo 2131435 3598357 := bbase (se 6 (by rfl) ⟨84336, by rfl⟩ : syracuseStep 3598357 = 168673) (by norm_num)
theorem B4797809 : Blo 2131435 4797809 := bstep (se 2 (by rfl) ⟨1799178, by rfl⟩ : syracuseStep 4797809 = 3598357) B3598357
theorem B3198539 : Blo 2131435 3198539 := bstep (se 1 (by rfl) ⟨2398904, by rfl⟩ : syracuseStep 3198539 = 4797809) B4797809
theorem B2132359 : Blo 2131435 2132359 := bstep (se 1 (by rfl) ⟨1599269, by rfl⟩ : syracuseStep 2132359 = 3198539) B3198539
theorem B2398909 : Blo 2131435 2398909 := bbase (se 3 (by rfl) ⟨449795, by rfl⟩ : syracuseStep 2398909 = 899591) (by norm_num)
theorem B3198545 : Blo 2131435 3198545 := bstep (se 2 (by rfl) ⟨1199454, by rfl⟩ : syracuseStep 3198545 = 2398909) B2398909
theorem B2132363 : Blo 2131435 2132363 := bstep (se 1 (by rfl) ⟨1599272, by rfl⟩ : syracuseStep 2132363 = 3198545) B3198545
theorem B7196741 : Blo 2131435 7196741 := bbase (se 4 (by rfl) ⟨674694, by rfl⟩ : syracuseStep 7196741 = 1349389) (by norm_num)
theorem B4797827 : Blo 2131435 4797827 := bstep (se 1 (by rfl) ⟨3598370, by rfl⟩ : syracuseStep 4797827 = 7196741) B7196741
theorem B3198551 : Blo 2131435 3198551 := bstep (se 1 (by rfl) ⟨2398913, by rfl⟩ : syracuseStep 3198551 = 4797827) B4797827
theorem B2132367 : Blo 2131435 2132367 := bstep (se 1 (by rfl) ⟨1599275, by rfl⟩ : syracuseStep 2132367 = 3198551) B3198551
theorem B3198557 : Blo 2131435 3198557 := bbase (se 3 (by rfl) ⟨599729, by rfl⟩ : syracuseStep 3198557 = 1199459) (by norm_num)
theorem B2132371 : Blo 2131435 2132371 := bstep (se 1 (by rfl) ⟨1599278, by rfl⟩ : syracuseStep 2132371 = 3198557) B3198557
theorem B4797845 : Blo 2131435 4797845 := bbase (se 6 (by rfl) ⟨112449, by rfl⟩ : syracuseStep 4797845 = 224899) (by norm_num)
theorem B3198563 : Blo 2131435 3198563 := bstep (se 1 (by rfl) ⟨2398922, by rfl⟩ : syracuseStep 3198563 = 4797845) B4797845
theorem B2132375 : Blo 2131435 2132375 := bstep (se 1 (by rfl) ⟨1599281, by rfl⟩ : syracuseStep 2132375 = 3198563) B3198563
theorem B6484421 : Blo 2131435 6484421 := bbase (se 4 (by rfl) ⟨607914, by rfl⟩ : syracuseStep 6484421 = 1215829) (by norm_num)
theorem B17291789 : Blo 2131435 17291789 := bstep (se 3 (by rfl) ⟨3242210, by rfl⟩ : syracuseStep 17291789 = 6484421) B6484421
theorem B11527859 : Blo 2131435 11527859 := bstep (se 1 (by rfl) ⟨8645894, by rfl⟩ : syracuseStep 11527859 = 17291789) B17291789
theorem B7685239 : Blo 2131435 7685239 := bstep (se 1 (by rfl) ⟨5763929, by rfl⟩ : syracuseStep 7685239 = 11527859) B11527859
theorem B10246985 : Blo 2131435 10246985 := bstep (se 2 (by rfl) ⟨3842619, by rfl⟩ : syracuseStep 10246985 = 7685239) B7685239
theorem B6831323 : Blo 2131435 6831323 := bstep (se 1 (by rfl) ⟨5123492, by rfl⟩ : syracuseStep 6831323 = 10246985) B10246985
theorem B4554215 : Blo 2131435 4554215 := bstep (se 1 (by rfl) ⟨3415661, by rfl⟩ : syracuseStep 4554215 = 6831323) B6831323
theorem B3036143 : Blo 2131435 3036143 := bstep (se 1 (by rfl) ⟨2277107, by rfl⟩ : syracuseStep 3036143 = 4554215) B4554215
theorem B8096381 : Blo 2131435 8096381 := bstep (se 3 (by rfl) ⟨1518071, by rfl⟩ : syracuseStep 8096381 = 3036143) B3036143
theorem B5397587 : Blo 2131435 5397587 := bstep (se 1 (by rfl) ⟨4048190, by rfl⟩ : syracuseStep 5397587 = 8096381) B8096381
theorem B3598391 : Blo 2131435 3598391 := bstep (se 1 (by rfl) ⟨2698793, by rfl⟩ : syracuseStep 3598391 = 5397587) B5397587
theorem B2398927 : Blo 2131435 2398927 := bstep (se 1 (by rfl) ⟨1799195, by rfl⟩ : syracuseStep 2398927 = 3598391) B3598391
theorem B3198569 : Blo 2131435 3198569 := bstep (se 2 (by rfl) ⟨1199463, by rfl⟩ : syracuseStep 3198569 = 2398927) B2398927
theorem B2132379 : Blo 2131435 2132379 := bstep (se 1 (by rfl) ⟨1599284, by rfl⟩ : syracuseStep 2132379 = 3198569) B3198569
theorem B5123501 : Blo 2131435 5123501 := bbase (se 3 (by rfl) ⟨960656, by rfl⟩ : syracuseStep 5123501 = 1921313) (by norm_num)
theorem B3415667 : Blo 2131435 3415667 := bstep (se 1 (by rfl) ⟨2561750, by rfl⟩ : syracuseStep 3415667 = 5123501) B5123501
theorem B9108445 : Blo 2131435 9108445 := bstep (se 3 (by rfl) ⟨1707833, by rfl⟩ : syracuseStep 9108445 = 3415667) B3415667
theorem B12144593 : Blo 2131435 12144593 := bstep (se 2 (by rfl) ⟨4554222, by rfl⟩ : syracuseStep 12144593 = 9108445) B9108445
theorem B8096395 : Blo 2131435 8096395 := bstep (se 1 (by rfl) ⟨6072296, by rfl⟩ : syracuseStep 8096395 = 12144593) B12144593
theorem B10795193 : Blo 2131435 10795193 := bstep (se 2 (by rfl) ⟨4048197, by rfl⟩ : syracuseStep 10795193 = 8096395) B8096395
theorem B7196795 : Blo 2131435 7196795 := bstep (se 1 (by rfl) ⟨5397596, by rfl⟩ : syracuseStep 7196795 = 10795193) B10795193
theorem B4797863 : Blo 2131435 4797863 := bstep (se 1 (by rfl) ⟨3598397, by rfl⟩ : syracuseStep 4797863 = 7196795) B7196795
theorem B3198575 : Blo 2131435 3198575 := bstep (se 1 (by rfl) ⟨2398931, by rfl⟩ : syracuseStep 3198575 = 4797863) B4797863
theorem B2132383 : Blo 2131435 2132383 := bstep (se 1 (by rfl) ⟨1599287, by rfl⟩ : syracuseStep 2132383 = 3198575) B3198575
theorem B3198581 : Blo 2131435 3198581 := bbase (se 5 (by rfl) ⟨149933, by rfl⟩ : syracuseStep 3198581 = 299867) (by norm_num)
theorem B2132387 : Blo 2131435 2132387 := bstep (se 1 (by rfl) ⟨1599290, by rfl⟩ : syracuseStep 2132387 = 3198581) B3198581
theorem B4048213 : Blo 2131435 4048213 := bbase (se 12 (by rfl) ⟨1482, by rfl⟩ : syracuseStep 4048213 = 2965) (by norm_num)
theorem B5397617 : Blo 2131435 5397617 := bstep (se 2 (by rfl) ⟨2024106, by rfl⟩ : syracuseStep 5397617 = 4048213) B4048213
theorem B3598411 : Blo 2131435 3598411 := bstep (se 1 (by rfl) ⟨2698808, by rfl⟩ : syracuseStep 3598411 = 5397617) B5397617
theorem B4797881 : Blo 2131435 4797881 := bstep (se 2 (by rfl) ⟨1799205, by rfl⟩ : syracuseStep 4797881 = 3598411) B3598411
theorem B3198587 : Blo 2131435 3198587 := bstep (se 1 (by rfl) ⟨2398940, by rfl⟩ : syracuseStep 3198587 = 4797881) B4797881
theorem B2132391 : Blo 2131435 2132391 := bstep (se 1 (by rfl) ⟨1599293, by rfl⟩ : syracuseStep 2132391 = 3198587) B3198587
theorem B2398945 : Blo 2131435 2398945 := bbase (se 2 (by rfl) ⟨899604, by rfl⟩ : syracuseStep 2398945 = 1799209) (by norm_num)
theorem B3198593 : Blo 2131435 3198593 := bstep (se 2 (by rfl) ⟨1199472, by rfl⟩ : syracuseStep 3198593 = 2398945) B2398945
theorem B2132395 : Blo 2131435 2132395 := bstep (se 1 (by rfl) ⟨1599296, by rfl⟩ : syracuseStep 2132395 = 3198593) B3198593
theorem B5397637 : Blo 2131435 5397637 := bbase (se 4 (by rfl) ⟨506028, by rfl⟩ : syracuseStep 5397637 = 1012057) (by norm_num)
theorem B7196849 : Blo 2131435 7196849 := bstep (se 2 (by rfl) ⟨2698818, by rfl⟩ : syracuseStep 7196849 = 5397637) B5397637
theorem B4797899 : Blo 2131435 4797899 := bstep (se 1 (by rfl) ⟨3598424, by rfl⟩ : syracuseStep 4797899 = 7196849) B7196849
theorem B3198599 : Blo 2131435 3198599 := bstep (se 1 (by rfl) ⟨2398949, by rfl⟩ : syracuseStep 3198599 = 4797899) B4797899
theorem B2132399 : Blo 2131435 2132399 := bstep (se 1 (by rfl) ⟨1599299, by rfl⟩ : syracuseStep 2132399 = 3198599) B3198599
theorem B3198605 : Blo 2131435 3198605 := bbase (se 3 (by rfl) ⟨599738, by rfl⟩ : syracuseStep 3198605 = 1199477) (by norm_num)
theorem B2132403 : Blo 2131435 2132403 := bstep (se 1 (by rfl) ⟨1599302, by rfl⟩ : syracuseStep 2132403 = 3198605) B3198605
theorem B4797917 : Blo 2131435 4797917 := bbase (se 3 (by rfl) ⟨899609, by rfl⟩ : syracuseStep 4797917 = 1799219) (by norm_num)
theorem B3198611 : Blo 2131435 3198611 := bstep (se 1 (by rfl) ⟨2398958, by rfl⟩ : syracuseStep 3198611 = 4797917) B4797917
theorem B2132407 : Blo 2131435 2132407 := bstep (se 1 (by rfl) ⟨1599305, by rfl⟩ : syracuseStep 2132407 = 3198611) B3198611
theorem B3598445 : Blo 2131435 3598445 := bbase (se 3 (by rfl) ⟨674708, by rfl⟩ : syracuseStep 3598445 = 1349417) (by norm_num)
theorem B2398963 : Blo 2131435 2398963 := bstep (se 1 (by rfl) ⟨1799222, by rfl⟩ : syracuseStep 2398963 = 3598445) B3598445
theorem B3198617 : Blo 2131435 3198617 := bstep (se 2 (by rfl) ⟨1199481, by rfl⟩ : syracuseStep 3198617 = 2398963) B2398963
theorem B2132411 : Blo 2131435 2132411 := bstep (se 1 (by rfl) ⟨1599308, by rfl⟩ : syracuseStep 2132411 = 3198617) B3198617
theorem B4863397 : Blo 2131435 4863397 := bbase (se 4 (by rfl) ⟨455943, by rfl⟩ : syracuseStep 4863397 = 911887) (by norm_num)
theorem B6484529 : Blo 2131435 6484529 := bstep (se 2 (by rfl) ⟨2431698, by rfl⟩ : syracuseStep 6484529 = 4863397) B4863397
theorem B4323019 : Blo 2131435 4323019 := bstep (se 1 (by rfl) ⟨3242264, by rfl⟩ : syracuseStep 4323019 = 6484529) B6484529
theorem B5764025 : Blo 2131435 5764025 := bstep (se 2 (by rfl) ⟨2161509, by rfl⟩ : syracuseStep 5764025 = 4323019) B4323019
theorem B3842683 : Blo 2131435 3842683 := bstep (se 1 (by rfl) ⟨2882012, by rfl⟩ : syracuseStep 3842683 = 5764025) B5764025
theorem B20494309 : Blo 2131435 20494309 := bstep (se 4 (by rfl) ⟨1921341, by rfl⟩ : syracuseStep 20494309 = 3842683) B3842683
theorem B27325745 : Blo 2131435 27325745 := bstep (se 2 (by rfl) ⟨10247154, by rfl⟩ : syracuseStep 27325745 = 20494309) B20494309
theorem B18217163 : Blo 2131435 18217163 := bstep (se 1 (by rfl) ⟨13662872, by rfl⟩ : syracuseStep 18217163 = 27325745) B27325745
theorem B12144775 : Blo 2131435 12144775 := bstep (se 1 (by rfl) ⟨9108581, by rfl⟩ : syracuseStep 12144775 = 18217163) B18217163
theorem B16193033 : Blo 2131435 16193033 := bstep (se 2 (by rfl) ⟨6072387, by rfl⟩ : syracuseStep 16193033 = 12144775) B12144775
theorem B10795355 : Blo 2131435 10795355 := bstep (se 1 (by rfl) ⟨8096516, by rfl⟩ : syracuseStep 10795355 = 16193033) B16193033
theorem B7196903 : Blo 2131435 7196903 := bstep (se 1 (by rfl) ⟨5397677, by rfl⟩ : syracuseStep 7196903 = 10795355) B10795355
theorem B4797935 : Blo 2131435 4797935 := bstep (se 1 (by rfl) ⟨3598451, by rfl⟩ : syracuseStep 4797935 = 7196903) B7196903
theorem B3198623 : Blo 2131435 3198623 := bstep (se 1 (by rfl) ⟨2398967, by rfl⟩ : syracuseStep 3198623 = 4797935) B4797935
theorem B2132415 : Blo 2131435 2132415 := bstep (se 1 (by rfl) ⟨1599311, by rfl⟩ : syracuseStep 2132415 = 3198623) B3198623
theorem B3198629 : Blo 2131435 3198629 := bbase (se 4 (by rfl) ⟨299871, by rfl⟩ : syracuseStep 3198629 = 599743) (by norm_num)
theorem B2132419 : Blo 2131435 2132419 := bstep (se 1 (by rfl) ⟨1599314, by rfl⟩ : syracuseStep 2132419 = 3198629) B3198629
theorem B2698849 : Blo 2131435 2698849 := bbase (se 2 (by rfl) ⟨1012068, by rfl⟩ : syracuseStep 2698849 = 2024137) (by norm_num)
theorem B3598465 : Blo 2131435 3598465 := bstep (se 2 (by rfl) ⟨1349424, by rfl⟩ : syracuseStep 3598465 = 2698849) B2698849
theorem B4797953 : Blo 2131435 4797953 := bstep (se 2 (by rfl) ⟨1799232, by rfl⟩ : syracuseStep 4797953 = 3598465) B3598465
theorem B3198635 : Blo 2131435 3198635 := bstep (se 1 (by rfl) ⟨2398976, by rfl⟩ : syracuseStep 3198635 = 4797953) B4797953
theorem B2132423 : Blo 2131435 2132423 := bstep (se 1 (by rfl) ⟨1599317, by rfl⟩ : syracuseStep 2132423 = 3198635) B3198635
theorem B2398981 : Blo 2131435 2398981 := bbase (se 4 (by rfl) ⟨224904, by rfl⟩ : syracuseStep 2398981 = 449809) (by norm_num)
theorem B3198641 : Blo 2131435 3198641 := bstep (se 2 (by rfl) ⟨1199490, by rfl⟩ : syracuseStep 3198641 = 2398981) B2398981
theorem B2132427 : Blo 2131435 2132427 := bstep (se 1 (by rfl) ⟨1599320, by rfl⟩ : syracuseStep 2132427 = 3198641) B3198641
theorem B2561809 : Blo 2131435 2561809 := bbase (se 2 (by rfl) ⟨960678, by rfl⟩ : syracuseStep 2561809 = 1921357) (by norm_num)
theorem B3415745 : Blo 2131435 3415745 := bstep (se 2 (by rfl) ⟨1280904, by rfl⟩ : syracuseStep 3415745 = 2561809) B2561809
theorem B2277163 : Blo 2131435 2277163 := bstep (se 1 (by rfl) ⟨1707872, by rfl⟩ : syracuseStep 2277163 = 3415745) B3415745
theorem B3036217 : Blo 2131435 3036217 := bstep (se 2 (by rfl) ⟨1138581, by rfl⟩ : syracuseStep 3036217 = 2277163) B2277163
theorem B4048289 : Blo 2131435 4048289 := bstep (se 2 (by rfl) ⟨1518108, by rfl⟩ : syracuseStep 4048289 = 3036217) B3036217
theorem B2698859 : Blo 2131435 2698859 := bstep (se 1 (by rfl) ⟨2024144, by rfl⟩ : syracuseStep 2698859 = 4048289) B4048289
theorem B7196957 : Blo 2131435 7196957 := bstep (se 3 (by rfl) ⟨1349429, by rfl⟩ : syracuseStep 7196957 = 2698859) B2698859
theorem B4797971 : Blo 2131435 4797971 := bstep (se 1 (by rfl) ⟨3598478, by rfl⟩ : syracuseStep 4797971 = 7196957) B7196957
theorem B3198647 : Blo 2131435 3198647 := bstep (se 1 (by rfl) ⟨2398985, by rfl⟩ : syracuseStep 3198647 = 4797971) B4797971
theorem B2132431 : Blo 2131435 2132431 := bstep (se 1 (by rfl) ⟨1599323, by rfl⟩ : syracuseStep 2132431 = 3198647) B3198647
theorem B3198653 : Blo 2131435 3198653 := bbase (se 3 (by rfl) ⟨599747, by rfl⟩ : syracuseStep 3198653 = 1199495) (by norm_num)
theorem B2132435 : Blo 2131435 2132435 := bstep (se 1 (by rfl) ⟨1599326, by rfl⟩ : syracuseStep 2132435 = 3198653) B3198653
theorem B4797989 : Blo 2131435 4797989 := bbase (se 4 (by rfl) ⟨449811, by rfl⟩ : syracuseStep 4797989 = 899623) (by norm_num)
theorem B3198659 : Blo 2131435 3198659 := bstep (se 1 (by rfl) ⟨2398994, by rfl⟩ : syracuseStep 3198659 = 4797989) B4797989
theorem B2132439 : Blo 2131435 2132439 := bstep (se 1 (by rfl) ⟨1599329, by rfl⟩ : syracuseStep 2132439 = 3198659) B3198659
theorem B5397749 : Blo 2131435 5397749 := bbase (se 5 (by rfl) ⟨253019, by rfl⟩ : syracuseStep 5397749 = 506039) (by norm_num)
theorem B3598499 : Blo 2131435 3598499 := bstep (se 1 (by rfl) ⟨2698874, by rfl⟩ : syracuseStep 3598499 = 5397749) B5397749
theorem B2398999 : Blo 2131435 2398999 := bstep (se 1 (by rfl) ⟨1799249, by rfl⟩ : syracuseStep 2398999 = 3598499) B3598499
theorem B3198665 : Blo 2131435 3198665 := bstep (se 2 (by rfl) ⟨1199499, by rfl⟩ : syracuseStep 3198665 = 2398999) B2398999
theorem B2132443 : Blo 2131435 2132443 := bstep (se 1 (by rfl) ⟨1599332, by rfl⟩ : syracuseStep 2132443 = 3198665) B3198665
theorem B2191033 : Blo 2131435 2191033 := bbase (se 2 (by rfl) ⟨821637, by rfl⟩ : syracuseStep 2191033 = 1643275) (by norm_num)
theorem B11685509 : Blo 2131435 11685509 := bstep (se 4 (by rfl) ⟨1095516, by rfl⟩ : syracuseStep 11685509 = 2191033) B2191033
theorem B7790339 : Blo 2131435 7790339 := bstep (se 1 (by rfl) ⟨5842754, by rfl⟩ : syracuseStep 7790339 = 11685509) B11685509
theorem B5193559 : Blo 2131435 5193559 := bstep (se 1 (by rfl) ⟨3895169, by rfl⟩ : syracuseStep 5193559 = 7790339) B7790339
theorem B6924745 : Blo 2131435 6924745 := bstep (se 2 (by rfl) ⟨2596779, by rfl⟩ : syracuseStep 6924745 = 5193559) B5193559
theorem B9232993 : Blo 2131435 9232993 := bstep (se 2 (by rfl) ⟨3462372, by rfl⟩ : syracuseStep 9232993 = 6924745) B6924745
theorem B49242629 : Blo 2131435 49242629 := bstep (se 4 (by rfl) ⟨4616496, by rfl⟩ : syracuseStep 49242629 = 9232993) B9232993
theorem B32828419 : Blo 2131435 32828419 := bstep (se 1 (by rfl) ⟨24621314, by rfl⟩ : syracuseStep 32828419 = 49242629) B49242629
theorem B175084901 : Blo 2131435 175084901 := bstep (se 4 (by rfl) ⟨16414209, by rfl⟩ : syracuseStep 175084901 = 32828419) B32828419
theorem B116723267 : Blo 2131435 116723267 := bstep (se 1 (by rfl) ⟨87542450, by rfl⟩ : syracuseStep 116723267 = 175084901) B175084901
theorem B77815511 : Blo 2131435 77815511 := bstep (se 1 (by rfl) ⟨58361633, by rfl⟩ : syracuseStep 77815511 = 116723267) B116723267
theorem B51877007 : Blo 2131435 51877007 := bstep (se 1 (by rfl) ⟨38907755, by rfl⟩ : syracuseStep 51877007 = 77815511) B77815511
theorem B34584671 : Blo 2131435 34584671 := bstep (se 1 (by rfl) ⟨25938503, by rfl⟩ : syracuseStep 34584671 = 51877007) B51877007
theorem B23056447 : Blo 2131435 23056447 := bstep (se 1 (by rfl) ⟨17292335, by rfl⟩ : syracuseStep 23056447 = 34584671) B34584671
theorem B30741929 : Blo 2131435 30741929 := bstep (se 2 (by rfl) ⟨11528223, by rfl⟩ : syracuseStep 30741929 = 23056447) B23056447
theorem B20494619 : Blo 2131435 20494619 := bstep (se 1 (by rfl) ⟨15370964, by rfl⟩ : syracuseStep 20494619 = 30741929) B30741929
theorem B13663079 : Blo 2131435 13663079 := bstep (se 1 (by rfl) ⟨10247309, by rfl⟩ : syracuseStep 13663079 = 20494619) B20494619
theorem B9108719 : Blo 2131435 9108719 := bstep (se 1 (by rfl) ⟨6831539, by rfl⟩ : syracuseStep 9108719 = 13663079) B13663079
theorem B6072479 : Blo 2131435 6072479 := bstep (se 1 (by rfl) ⟨4554359, by rfl⟩ : syracuseStep 6072479 = 9108719) B9108719
theorem B4048319 : Blo 2131435 4048319 := bstep (se 1 (by rfl) ⟨3036239, by rfl⟩ : syracuseStep 4048319 = 6072479) B6072479
theorem B10795517 : Blo 2131435 10795517 := bstep (se 3 (by rfl) ⟨2024159, by rfl⟩ : syracuseStep 10795517 = 4048319) B4048319
theorem B7197011 : Blo 2131435 7197011 := bstep (se 1 (by rfl) ⟨5397758, by rfl⟩ : syracuseStep 7197011 = 10795517) B10795517
theorem B4798007 : Blo 2131435 4798007 := bstep (se 1 (by rfl) ⟨3598505, by rfl⟩ : syracuseStep 4798007 = 7197011) B7197011
theorem B3198671 : Blo 2131435 3198671 := bstep (se 1 (by rfl) ⟨2399003, by rfl⟩ : syracuseStep 3198671 = 4798007) B4798007
theorem B2132447 : Blo 2131435 2132447 := bstep (se 1 (by rfl) ⟨1599335, by rfl⟩ : syracuseStep 2132447 = 3198671) B3198671
theorem B3198677 : Blo 2131435 3198677 := bbase (se 7 (by rfl) ⟨37484, by rfl⟩ : syracuseStep 3198677 = 74969) (by norm_num)
theorem B2132451 : Blo 2131435 2132451 := bstep (se 1 (by rfl) ⟨1599338, by rfl⟩ : syracuseStep 2132451 = 3198677) B3198677
theorem B2735713 : Blo 2131435 2735713 := bbase (se 2 (by rfl) ⟨1025892, by rfl⟩ : syracuseStep 2735713 = 2051785) (by norm_num)
theorem B14590469 : Blo 2131435 14590469 := bstep (se 4 (by rfl) ⟨1367856, by rfl⟩ : syracuseStep 14590469 = 2735713) B2735713
theorem B9726979 : Blo 2131435 9726979 := bstep (se 1 (by rfl) ⟨7295234, by rfl⟩ : syracuseStep 9726979 = 14590469) B14590469
theorem B12969305 : Blo 2131435 12969305 := bstep (se 2 (by rfl) ⟨4863489, by rfl⟩ : syracuseStep 12969305 = 9726979) B9726979
theorem B8646203 : Blo 2131435 8646203 := bstep (se 1 (by rfl) ⟨6484652, by rfl⟩ : syracuseStep 8646203 = 12969305) B12969305
theorem B5764135 : Blo 2131435 5764135 := bstep (se 1 (by rfl) ⟨4323101, by rfl⟩ : syracuseStep 5764135 = 8646203) B8646203
theorem B7685513 : Blo 2131435 7685513 := bstep (se 2 (by rfl) ⟨2882067, by rfl⟩ : syracuseStep 7685513 = 5764135) B5764135
theorem B5123675 : Blo 2131435 5123675 := bstep (se 1 (by rfl) ⟨3842756, by rfl⟩ : syracuseStep 5123675 = 7685513) B7685513
theorem B3415783 : Blo 2131435 3415783 := bstep (se 1 (by rfl) ⟨2561837, by rfl⟩ : syracuseStep 3415783 = 5123675) B5123675
theorem B4554377 : Blo 2131435 4554377 := bstep (se 2 (by rfl) ⟨1707891, by rfl⟩ : syracuseStep 4554377 = 3415783) B3415783
theorem B3036251 : Blo 2131435 3036251 := bstep (se 1 (by rfl) ⟨2277188, by rfl⟩ : syracuseStep 3036251 = 4554377) B4554377
theorem B8096669 : Blo 2131435 8096669 := bstep (se 3 (by rfl) ⟨1518125, by rfl⟩ : syracuseStep 8096669 = 3036251) B3036251
theorem B5397779 : Blo 2131435 5397779 := bstep (se 1 (by rfl) ⟨4048334, by rfl⟩ : syracuseStep 5397779 = 8096669) B8096669
theorem B3598519 : Blo 2131435 3598519 := bstep (se 1 (by rfl) ⟨2698889, by rfl⟩ : syracuseStep 3598519 = 5397779) B5397779
theorem B4798025 : Blo 2131435 4798025 := bstep (se 2 (by rfl) ⟨1799259, by rfl⟩ : syracuseStep 4798025 = 3598519) B3598519
theorem B3198683 : Blo 2131435 3198683 := bstep (se 1 (by rfl) ⟨2399012, by rfl⟩ : syracuseStep 3198683 = 4798025) B4798025
theorem B2132455 : Blo 2131435 2132455 := bstep (se 1 (by rfl) ⟨1599341, by rfl⟩ : syracuseStep 2132455 = 3198683) B3198683
theorem B2399017 : Blo 2131435 2399017 := bbase (se 2 (by rfl) ⟨899631, by rfl⟩ : syracuseStep 2399017 = 1799263) (by norm_num)
theorem B3198689 : Blo 2131435 3198689 := bstep (se 2 (by rfl) ⟨1199508, by rfl⟩ : syracuseStep 3198689 = 2399017) B2399017
theorem B2132459 : Blo 2131435 2132459 := bstep (se 1 (by rfl) ⟨1599344, by rfl⟩ : syracuseStep 2132459 = 3198689) B3198689
theorem B5123693 : Blo 2131435 5123693 := bbase (se 3 (by rfl) ⟨960692, by rfl⟩ : syracuseStep 5123693 = 1921385) (by norm_num)
theorem B13663181 : Blo 2131435 13663181 := bstep (se 3 (by rfl) ⟨2561846, by rfl⟩ : syracuseStep 13663181 = 5123693) B5123693
theorem B9108787 : Blo 2131435 9108787 := bstep (se 1 (by rfl) ⟨6831590, by rfl⟩ : syracuseStep 9108787 = 13663181) B13663181
theorem B12145049 : Blo 2131435 12145049 := bstep (se 2 (by rfl) ⟨4554393, by rfl⟩ : syracuseStep 12145049 = 9108787) B9108787
theorem B8096699 : Blo 2131435 8096699 := bstep (se 1 (by rfl) ⟨6072524, by rfl⟩ : syracuseStep 8096699 = 12145049) B12145049
theorem B5397799 : Blo 2131435 5397799 := bstep (se 1 (by rfl) ⟨4048349, by rfl⟩ : syracuseStep 5397799 = 8096699) B8096699
theorem B7197065 : Blo 2131435 7197065 := bstep (se 2 (by rfl) ⟨2698899, by rfl⟩ : syracuseStep 7197065 = 5397799) B5397799
theorem B4798043 : Blo 2131435 4798043 := bstep (se 1 (by rfl) ⟨3598532, by rfl⟩ : syracuseStep 4798043 = 7197065) B7197065
theorem B3198695 : Blo 2131435 3198695 := bstep (se 1 (by rfl) ⟨2399021, by rfl⟩ : syracuseStep 3198695 = 4798043) B4798043
theorem B2132463 : Blo 2131435 2132463 := bstep (se 1 (by rfl) ⟨1599347, by rfl⟩ : syracuseStep 2132463 = 3198695) B3198695
theorem B3198701 : Blo 2131435 3198701 := bbase (se 3 (by rfl) ⟨599756, by rfl⟩ : syracuseStep 3198701 = 1199513) (by norm_num)
theorem B2132467 : Blo 2131435 2132467 := bstep (se 1 (by rfl) ⟨1599350, by rfl⟩ : syracuseStep 2132467 = 3198701) B3198701
theorem B4798061 : Blo 2131435 4798061 := bbase (se 3 (by rfl) ⟨899636, by rfl⟩ : syracuseStep 4798061 = 1799273) (by norm_num)
theorem B3198707 : Blo 2131435 3198707 := bstep (se 1 (by rfl) ⟨2399030, by rfl⟩ : syracuseStep 3198707 = 4798061) B4798061
theorem B2132471 : Blo 2131435 2132471 := bstep (se 1 (by rfl) ⟨1599353, by rfl⟩ : syracuseStep 2132471 = 3198707) B3198707
theorem B4048373 : Blo 2131435 4048373 := bbase (se 5 (by rfl) ⟨189767, by rfl⟩ : syracuseStep 4048373 = 379535) (by norm_num)
theorem B2698915 : Blo 2131435 2698915 := bstep (se 1 (by rfl) ⟨2024186, by rfl⟩ : syracuseStep 2698915 = 4048373) B4048373
theorem B3598553 : Blo 2131435 3598553 := bstep (se 2 (by rfl) ⟨1349457, by rfl⟩ : syracuseStep 3598553 = 2698915) B2698915
theorem B2399035 : Blo 2131435 2399035 := bstep (se 1 (by rfl) ⟨1799276, by rfl⟩ : syracuseStep 2399035 = 3598553) B3598553
theorem B3198713 : Blo 2131435 3198713 := bstep (se 2 (by rfl) ⟨1199517, by rfl⟩ : syracuseStep 3198713 = 2399035) B2399035
theorem B2132475 : Blo 2131435 2132475 := bstep (se 1 (by rfl) ⟨1599356, by rfl⟩ : syracuseStep 2132475 = 3198713) B3198713
theorem B92227157 : Blo 2131435 92227157 := bbase (se 8 (by rfl) ⟨540393, by rfl⟩ : syracuseStep 92227157 = 1080787) (by norm_num)
theorem B61484771 : Blo 2131435 61484771 := bstep (se 1 (by rfl) ⟨46113578, by rfl⟩ : syracuseStep 61484771 = 92227157) B92227157
theorem B40989847 : Blo 2131435 40989847 := bstep (se 1 (by rfl) ⟨30742385, by rfl⟩ : syracuseStep 40989847 = 61484771) B61484771
theorem B54653129 : Blo 2131435 54653129 := bstep (se 2 (by rfl) ⟨20494923, by rfl⟩ : syracuseStep 54653129 = 40989847) B40989847
theorem B36435419 : Blo 2131435 36435419 := bstep (se 1 (by rfl) ⟨27326564, by rfl⟩ : syracuseStep 36435419 = 54653129) B54653129
theorem B24290279 : Blo 2131435 24290279 := bstep (se 1 (by rfl) ⟨18217709, by rfl⟩ : syracuseStep 24290279 = 36435419) B36435419
theorem B16193519 : Blo 2131435 16193519 := bstep (se 1 (by rfl) ⟨12145139, by rfl⟩ : syracuseStep 16193519 = 24290279) B24290279
theorem B10795679 : Blo 2131435 10795679 := bstep (se 1 (by rfl) ⟨8096759, by rfl⟩ : syracuseStep 10795679 = 16193519) B16193519
theorem B7197119 : Blo 2131435 7197119 := bstep (se 1 (by rfl) ⟨5397839, by rfl⟩ : syracuseStep 7197119 = 10795679) B10795679
theorem B4798079 : Blo 2131435 4798079 := bstep (se 1 (by rfl) ⟨3598559, by rfl⟩ : syracuseStep 4798079 = 7197119) B7197119
theorem B3198719 : Blo 2131435 3198719 := bstep (se 1 (by rfl) ⟨2399039, by rfl⟩ : syracuseStep 3198719 = 4798079) B4798079
theorem B2132479 : Blo 2131435 2132479 := bstep (se 1 (by rfl) ⟨1599359, by rfl⟩ : syracuseStep 2132479 = 3198719) B3198719
theorem B3198725 : Blo 2131435 3198725 := bbase (se 4 (by rfl) ⟨299880, by rfl⟩ : syracuseStep 3198725 = 599761) (by norm_num)
theorem B2132483 : Blo 2131435 2132483 := bstep (se 1 (by rfl) ⟨1599362, by rfl⟩ : syracuseStep 2132483 = 3198725) B3198725
theorem B3598573 : Blo 2131435 3598573 := bbase (se 3 (by rfl) ⟨674732, by rfl⟩ : syracuseStep 3598573 = 1349465) (by norm_num)
theorem B4798097 : Blo 2131435 4798097 := bstep (se 2 (by rfl) ⟨1799286, by rfl⟩ : syracuseStep 4798097 = 3598573) B3598573
theorem B3198731 : Blo 2131435 3198731 := bstep (se 1 (by rfl) ⟨2399048, by rfl⟩ : syracuseStep 3198731 = 4798097) B4798097
theorem B2132487 : Blo 2131435 2132487 := bstep (se 1 (by rfl) ⟨1599365, by rfl⟩ : syracuseStep 2132487 = 3198731) B3198731
theorem B2399053 : Blo 2131435 2399053 := bbase (se 3 (by rfl) ⟨449822, by rfl⟩ : syracuseStep 2399053 = 899645) (by norm_num)
theorem B3198737 : Blo 2131435 3198737 := bstep (se 2 (by rfl) ⟨1199526, by rfl⟩ : syracuseStep 3198737 = 2399053) B2399053
theorem B2132491 : Blo 2131435 2132491 := bstep (se 1 (by rfl) ⟨1599368, by rfl⟩ : syracuseStep 2132491 = 3198737) B3198737
theorem B7197173 : Blo 2131435 7197173 := bbase (se 5 (by rfl) ⟨337367, by rfl⟩ : syracuseStep 7197173 = 674735) (by norm_num)
theorem B4798115 : Blo 2131435 4798115 := bstep (se 1 (by rfl) ⟨3598586, by rfl⟩ : syracuseStep 4798115 = 7197173) B7197173
theorem B3198743 : Blo 2131435 3198743 := bstep (se 1 (by rfl) ⟨2399057, by rfl⟩ : syracuseStep 3198743 = 4798115) B4798115
theorem B2132495 : Blo 2131435 2132495 := bstep (se 1 (by rfl) ⟨1599371, by rfl⟩ : syracuseStep 2132495 = 3198743) B3198743
theorem B3198749 : Blo 2131435 3198749 := bbase (se 3 (by rfl) ⟨599765, by rfl⟩ : syracuseStep 3198749 = 1199531) (by norm_num)
theorem B2132499 : Blo 2131435 2132499 := bstep (se 1 (by rfl) ⟨1599374, by rfl⟩ : syracuseStep 2132499 = 3198749) B3198749
theorem B4798133 : Blo 2131435 4798133 := bbase (se 5 (by rfl) ⟨224912, by rfl⟩ : syracuseStep 4798133 = 449825) (by norm_num)
theorem B3198755 : Blo 2131435 3198755 := bstep (se 1 (by rfl) ⟨2399066, by rfl⟩ : syracuseStep 3198755 = 4798133) B4798133
theorem B2132503 : Blo 2131435 2132503 := bstep (se 1 (by rfl) ⟨1599377, by rfl⟩ : syracuseStep 2132503 = 3198755) B3198755
theorem B12145301 : Blo 2131435 12145301 := bbase (se 6 (by rfl) ⟨284655, by rfl⟩ : syracuseStep 12145301 = 569311) (by norm_num)
theorem B8096867 : Blo 2131435 8096867 := bstep (se 1 (by rfl) ⟨6072650, by rfl⟩ : syracuseStep 8096867 = 12145301) B12145301
theorem B5397911 : Blo 2131435 5397911 := bstep (se 1 (by rfl) ⟨4048433, by rfl⟩ : syracuseStep 5397911 = 8096867) B8096867
theorem B3598607 : Blo 2131435 3598607 := bstep (se 1 (by rfl) ⟨2698955, by rfl⟩ : syracuseStep 3598607 = 5397911) B5397911
theorem B2399071 : Blo 2131435 2399071 := bstep (se 1 (by rfl) ⟨1799303, by rfl⟩ : syracuseStep 2399071 = 3598607) B3598607
theorem B3198761 : Blo 2131435 3198761 := bstep (se 2 (by rfl) ⟨1199535, by rfl⟩ : syracuseStep 3198761 = 2399071) B2399071
theorem B2132507 : Blo 2131435 2132507 := bstep (se 1 (by rfl) ⟨1599380, by rfl⟩ : syracuseStep 2132507 = 3198761) B3198761
theorem B6072661 : Blo 2131435 6072661 := bbase (se 10 (by rfl) ⟨8895, by rfl⟩ : syracuseStep 6072661 = 17791) (by norm_num)
theorem B8096881 : Blo 2131435 8096881 := bstep (se 2 (by rfl) ⟨3036330, by rfl⟩ : syracuseStep 8096881 = 6072661) B6072661
theorem B10795841 : Blo 2131435 10795841 := bstep (se 2 (by rfl) ⟨4048440, by rfl⟩ : syracuseStep 10795841 = 8096881) B8096881
theorem B7197227 : Blo 2131435 7197227 := bstep (se 1 (by rfl) ⟨5397920, by rfl⟩ : syracuseStep 7197227 = 10795841) B10795841
theorem B4798151 : Blo 2131435 4798151 := bstep (se 1 (by rfl) ⟨3598613, by rfl⟩ : syracuseStep 4798151 = 7197227) B7197227
theorem B3198767 : Blo 2131435 3198767 := bstep (se 1 (by rfl) ⟨2399075, by rfl⟩ : syracuseStep 3198767 = 4798151) B4798151
theorem B2132511 : Blo 2131435 2132511 := bstep (se 1 (by rfl) ⟨1599383, by rfl⟩ : syracuseStep 2132511 = 3198767) B3198767
theorem B3198773 : Blo 2131435 3198773 := bbase (se 5 (by rfl) ⟨149942, by rfl⟩ : syracuseStep 3198773 = 299885) (by norm_num)
theorem B2132515 : Blo 2131435 2132515 := bstep (se 1 (by rfl) ⟨1599386, by rfl⟩ : syracuseStep 2132515 = 3198773) B3198773
theorem B5397941 : Blo 2131435 5397941 := bbase (se 5 (by rfl) ⟨253028, by rfl⟩ : syracuseStep 5397941 = 506057) (by norm_num)
theorem B3598627 : Blo 2131435 3598627 := bstep (se 1 (by rfl) ⟨2698970, by rfl⟩ : syracuseStep 3598627 = 5397941) B5397941
theorem B4798169 : Blo 2131435 4798169 := bstep (se 2 (by rfl) ⟨1799313, by rfl⟩ : syracuseStep 4798169 = 3598627) B3598627
theorem B3198779 : Blo 2131435 3198779 := bstep (se 1 (by rfl) ⟨2399084, by rfl⟩ : syracuseStep 3198779 = 4798169) B4798169
theorem B2132519 : Blo 2131435 2132519 := bstep (se 1 (by rfl) ⟨1599389, by rfl⟩ : syracuseStep 2132519 = 3198779) B3198779
theorem B2399089 : Blo 2131435 2399089 := bbase (se 2 (by rfl) ⟨899658, by rfl⟩ : syracuseStep 2399089 = 1799317) (by norm_num)
theorem B3198785 : Blo 2131435 3198785 := bstep (se 2 (by rfl) ⟨1199544, by rfl⟩ : syracuseStep 3198785 = 2399089) B2399089
theorem B2132523 : Blo 2131435 2132523 := bstep (se 1 (by rfl) ⟨1599392, by rfl⟩ : syracuseStep 2132523 = 3198785) B3198785
theorem B9109061 : Blo 2131435 9109061 := bbase (se 4 (by rfl) ⟨853974, by rfl⟩ : syracuseStep 9109061 = 1707949) (by norm_num)
theorem B6072707 : Blo 2131435 6072707 := bstep (se 1 (by rfl) ⟨4554530, by rfl⟩ : syracuseStep 6072707 = 9109061) B9109061
theorem B4048471 : Blo 2131435 4048471 := bstep (se 1 (by rfl) ⟨3036353, by rfl⟩ : syracuseStep 4048471 = 6072707) B6072707
theorem B5397961 : Blo 2131435 5397961 := bstep (se 2 (by rfl) ⟨2024235, by rfl⟩ : syracuseStep 5397961 = 4048471) B4048471
theorem B7197281 : Blo 2131435 7197281 := bstep (se 2 (by rfl) ⟨2698980, by rfl⟩ : syracuseStep 7197281 = 5397961) B5397961
theorem B4798187 : Blo 2131435 4798187 := bstep (se 1 (by rfl) ⟨3598640, by rfl⟩ : syracuseStep 4798187 = 7197281) B7197281
theorem B3198791 : Blo 2131435 3198791 := bstep (se 1 (by rfl) ⟨2399093, by rfl⟩ : syracuseStep 3198791 = 4798187) B4798187
theorem B2132527 : Blo 2131435 2132527 := bstep (se 1 (by rfl) ⟨1599395, by rfl⟩ : syracuseStep 2132527 = 3198791) B3198791
theorem B3198797 : Blo 2131435 3198797 := bbase (se 3 (by rfl) ⟨599774, by rfl⟩ : syracuseStep 3198797 = 1199549) (by norm_num)
theorem B2132531 : Blo 2131435 2132531 := bstep (se 1 (by rfl) ⟨1599398, by rfl⟩ : syracuseStep 2132531 = 3198797) B3198797
theorem B4798205 : Blo 2131435 4798205 := bbase (se 3 (by rfl) ⟨899663, by rfl⟩ : syracuseStep 4798205 = 1799327) (by norm_num)
theorem B3198803 : Blo 2131435 3198803 := bstep (se 1 (by rfl) ⟨2399102, by rfl⟩ : syracuseStep 3198803 = 4798205) B4798205
theorem B2132535 : Blo 2131435 2132535 := bstep (se 1 (by rfl) ⟨1599401, by rfl⟩ : syracuseStep 2132535 = 3198803) B3198803
theorem B3598661 : Blo 2131435 3598661 := bbase (se 4 (by rfl) ⟨337374, by rfl⟩ : syracuseStep 3598661 = 674749) (by norm_num)
theorem B2399107 : Blo 2131435 2399107 := bstep (se 1 (by rfl) ⟨1799330, by rfl⟩ : syracuseStep 2399107 = 3598661) B3598661
theorem B3198809 : Blo 2131435 3198809 := bstep (se 2 (by rfl) ⟨1199553, by rfl⟩ : syracuseStep 3198809 = 2399107) B2399107
theorem B2132539 : Blo 2131435 2132539 := bstep (se 1 (by rfl) ⟨1599404, by rfl⟩ : syracuseStep 2132539 = 3198809) B3198809
theorem B16194005 : Blo 2131435 16194005 := bbase (se 7 (by rfl) ⟨189773, by rfl⟩ : syracuseStep 16194005 = 379547) (by norm_num)
theorem B10796003 : Blo 2131435 10796003 := bstep (se 1 (by rfl) ⟨8097002, by rfl⟩ : syracuseStep 10796003 = 16194005) B16194005
theorem B7197335 : Blo 2131435 7197335 := bstep (se 1 (by rfl) ⟨5398001, by rfl⟩ : syracuseStep 7197335 = 10796003) B10796003
theorem B4798223 : Blo 2131435 4798223 := bstep (se 1 (by rfl) ⟨3598667, by rfl⟩ : syracuseStep 4798223 = 7197335) B7197335
theorem B3198815 : Blo 2131435 3198815 := bstep (se 1 (by rfl) ⟨2399111, by rfl⟩ : syracuseStep 3198815 = 4798223) B4798223
theorem B2132543 : Blo 2131435 2132543 := bstep (se 1 (by rfl) ⟨1599407, by rfl⟩ : syracuseStep 2132543 = 3198815) B3198815
theorem B3198821 : Blo 2131435 3198821 := bbase (se 4 (by rfl) ⟨299889, by rfl⟩ : syracuseStep 3198821 = 599779) (by norm_num)
theorem B2132547 : Blo 2131435 2132547 := bstep (se 1 (by rfl) ⟨1599410, by rfl⟩ : syracuseStep 2132547 = 3198821) B3198821
theorem B4048517 : Blo 2131435 4048517 := bbase (se 4 (by rfl) ⟨379548, by rfl⟩ : syracuseStep 4048517 = 759097) (by norm_num)
theorem B2699011 : Blo 2131435 2699011 := bstep (se 1 (by rfl) ⟨2024258, by rfl⟩ : syracuseStep 2699011 = 4048517) B4048517
theorem B3598681 : Blo 2131435 3598681 := bstep (se 2 (by rfl) ⟨1349505, by rfl⟩ : syracuseStep 3598681 = 2699011) B2699011
theorem B4798241 : Blo 2131435 4798241 := bstep (se 2 (by rfl) ⟨1799340, by rfl⟩ : syracuseStep 4798241 = 3598681) B3598681
theorem B3198827 : Blo 2131435 3198827 := bstep (se 1 (by rfl) ⟨2399120, by rfl⟩ : syracuseStep 3198827 = 4798241) B4798241
theorem B2132551 : Blo 2131435 2132551 := bstep (se 1 (by rfl) ⟨1599413, by rfl⟩ : syracuseStep 2132551 = 3198827) B3198827
theorem B2399125 : Blo 2131435 2399125 := bbase (se 6 (by rfl) ⟨56229, by rfl⟩ : syracuseStep 2399125 = 112459) (by norm_num)
theorem B3198833 : Blo 2131435 3198833 := bstep (se 2 (by rfl) ⟨1199562, by rfl⟩ : syracuseStep 3198833 = 2399125) B2399125
theorem B2132555 : Blo 2131435 2132555 := bstep (se 1 (by rfl) ⟨1599416, by rfl⟩ : syracuseStep 2132555 = 3198833) B3198833
theorem B2699021 : Blo 2131435 2699021 := bbase (se 3 (by rfl) ⟨506066, by rfl⟩ : syracuseStep 2699021 = 1012133) (by norm_num)
theorem B7197389 : Blo 2131435 7197389 := bstep (se 3 (by rfl) ⟨1349510, by rfl⟩ : syracuseStep 7197389 = 2699021) B2699021
theorem B4798259 : Blo 2131435 4798259 := bstep (se 1 (by rfl) ⟨3598694, by rfl⟩ : syracuseStep 4798259 = 7197389) B7197389
theorem B3198839 : Blo 2131435 3198839 := bstep (se 1 (by rfl) ⟨2399129, by rfl⟩ : syracuseStep 3198839 = 4798259) B4798259
theorem B2132559 : Blo 2131435 2132559 := bstep (se 1 (by rfl) ⟨1599419, by rfl⟩ : syracuseStep 2132559 = 3198839) B3198839
theorem B3198845 : Blo 2131435 3198845 := bbase (se 3 (by rfl) ⟨599783, by rfl⟩ : syracuseStep 3198845 = 1199567) (by norm_num)
theorem B2132563 : Blo 2131435 2132563 := bstep (se 1 (by rfl) ⟨1599422, by rfl⟩ : syracuseStep 2132563 = 3198845) B3198845
theorem B4798277 : Blo 2131435 4798277 := bbase (se 4 (by rfl) ⟨449838, by rfl⟩ : syracuseStep 4798277 = 899677) (by norm_num)
theorem B3198851 : Blo 2131435 3198851 := bstep (se 1 (by rfl) ⟨2399138, by rfl⟩ : syracuseStep 3198851 = 4798277) B4798277
theorem B2132567 : Blo 2131435 2132567 := bstep (se 1 (by rfl) ⟨1599425, by rfl⟩ : syracuseStep 2132567 = 3198851) B3198851
theorem B2561977 : Blo 2131435 2561977 := bbase (se 2 (by rfl) ⟨960741, by rfl⟩ : syracuseStep 2561977 = 1921483) (by norm_num)
theorem B3415969 : Blo 2131435 3415969 := bstep (se 2 (by rfl) ⟨1280988, by rfl⟩ : syracuseStep 3415969 = 2561977) B2561977
theorem B4554625 : Blo 2131435 4554625 := bstep (se 2 (by rfl) ⟨1707984, by rfl⟩ : syracuseStep 4554625 = 3415969) B3415969
theorem B6072833 : Blo 2131435 6072833 := bstep (se 2 (by rfl) ⟨2277312, by rfl⟩ : syracuseStep 6072833 = 4554625) B4554625
theorem B4048555 : Blo 2131435 4048555 := bstep (se 1 (by rfl) ⟨3036416, by rfl⟩ : syracuseStep 4048555 = 6072833) B6072833
theorem B5398073 : Blo 2131435 5398073 := bstep (se 2 (by rfl) ⟨2024277, by rfl⟩ : syracuseStep 5398073 = 4048555) B4048555
theorem B3598715 : Blo 2131435 3598715 := bstep (se 1 (by rfl) ⟨2699036, by rfl⟩ : syracuseStep 3598715 = 5398073) B5398073
theorem B2399143 : Blo 2131435 2399143 := bstep (se 1 (by rfl) ⟨1799357, by rfl⟩ : syracuseStep 2399143 = 3598715) B3598715
theorem B3198857 : Blo 2131435 3198857 := bstep (se 2 (by rfl) ⟨1199571, by rfl⟩ : syracuseStep 3198857 = 2399143) B2399143
theorem B2132571 : Blo 2131435 2132571 := bstep (se 1 (by rfl) ⟨1599428, by rfl⟩ : syracuseStep 2132571 = 3198857) B3198857
theorem B10796165 : Blo 2131435 10796165 := bbase (se 4 (by rfl) ⟨1012140, by rfl⟩ : syracuseStep 10796165 = 2024281) (by norm_num)
theorem B7197443 : Blo 2131435 7197443 := bstep (se 1 (by rfl) ⟨5398082, by rfl⟩ : syracuseStep 7197443 = 10796165) B10796165
theorem B4798295 : Blo 2131435 4798295 := bstep (se 1 (by rfl) ⟨3598721, by rfl⟩ : syracuseStep 4798295 = 7197443) B7197443
theorem B3198863 : Blo 2131435 3198863 := bstep (se 1 (by rfl) ⟨2399147, by rfl⟩ : syracuseStep 3198863 = 4798295) B4798295
theorem B2132575 : Blo 2131435 2132575 := bstep (se 1 (by rfl) ⟨1599431, by rfl⟩ : syracuseStep 2132575 = 3198863) B3198863
theorem B3198869 : Blo 2131435 3198869 := bbase (se 6 (by rfl) ⟨74973, by rfl⟩ : syracuseStep 3198869 = 149947) (by norm_num)
theorem B2132579 : Blo 2131435 2132579 := bstep (se 1 (by rfl) ⟨1599434, by rfl⟩ : syracuseStep 2132579 = 3198869) B3198869
theorem B2277325 : Blo 2131435 2277325 := bbase (se 3 (by rfl) ⟨426998, by rfl⟩ : syracuseStep 2277325 = 853997) (by norm_num)
theorem B12145733 : Blo 2131435 12145733 := bstep (se 4 (by rfl) ⟨1138662, by rfl⟩ : syracuseStep 12145733 = 2277325) B2277325
theorem B8097155 : Blo 2131435 8097155 := bstep (se 1 (by rfl) ⟨6072866, by rfl⟩ : syracuseStep 8097155 = 12145733) B12145733
theorem B5398103 : Blo 2131435 5398103 := bstep (se 1 (by rfl) ⟨4048577, by rfl⟩ : syracuseStep 5398103 = 8097155) B8097155
theorem B3598735 : Blo 2131435 3598735 := bstep (se 1 (by rfl) ⟨2699051, by rfl⟩ : syracuseStep 3598735 = 5398103) B5398103
theorem B4798313 : Blo 2131435 4798313 := bstep (se 2 (by rfl) ⟨1799367, by rfl⟩ : syracuseStep 4798313 = 3598735) B3598735
theorem B3198875 : Blo 2131435 3198875 := bstep (se 1 (by rfl) ⟨2399156, by rfl⟩ : syracuseStep 3198875 = 4798313) B4798313
theorem B2132583 : Blo 2131435 2132583 := bstep (se 1 (by rfl) ⟨1599437, by rfl⟩ : syracuseStep 2132583 = 3198875) B3198875
theorem B2399161 : Blo 2131435 2399161 := bbase (se 2 (by rfl) ⟨899685, by rfl⟩ : syracuseStep 2399161 = 1799371) (by norm_num)
theorem B3198881 : Blo 2131435 3198881 := bstep (se 2 (by rfl) ⟨1199580, by rfl⟩ : syracuseStep 3198881 = 2399161) B2399161
theorem B2132587 : Blo 2131435 2132587 := bstep (se 1 (by rfl) ⟨1599440, by rfl⟩ : syracuseStep 2132587 = 3198881) B3198881
theorem B3242533 : Blo 2131435 3242533 := bbase (se 4 (by rfl) ⟨303987, by rfl⟩ : syracuseStep 3242533 = 607975) (by norm_num)
theorem B4323377 : Blo 2131435 4323377 := bstep (se 2 (by rfl) ⟨1621266, by rfl⟩ : syracuseStep 4323377 = 3242533) B3242533
theorem B2882251 : Blo 2131435 2882251 := bstep (se 1 (by rfl) ⟨2161688, by rfl⟩ : syracuseStep 2882251 = 4323377) B4323377
theorem B3843001 : Blo 2131435 3843001 := bstep (se 2 (by rfl) ⟨1441125, by rfl⟩ : syracuseStep 3843001 = 2882251) B2882251
theorem B5124001 : Blo 2131435 5124001 := bstep (se 2 (by rfl) ⟨1921500, by rfl⟩ : syracuseStep 5124001 = 3843001) B3843001
theorem B6832001 : Blo 2131435 6832001 := bstep (se 2 (by rfl) ⟨2562000, by rfl⟩ : syracuseStep 6832001 = 5124001) B5124001
theorem B4554667 : Blo 2131435 4554667 := bstep (se 1 (by rfl) ⟨3416000, by rfl⟩ : syracuseStep 4554667 = 6832001) B6832001
theorem B6072889 : Blo 2131435 6072889 := bstep (se 2 (by rfl) ⟨2277333, by rfl⟩ : syracuseStep 6072889 = 4554667) B4554667
theorem B8097185 : Blo 2131435 8097185 := bstep (se 2 (by rfl) ⟨3036444, by rfl⟩ : syracuseStep 8097185 = 6072889) B6072889
theorem B5398123 : Blo 2131435 5398123 := bstep (se 1 (by rfl) ⟨4048592, by rfl⟩ : syracuseStep 5398123 = 8097185) B8097185
theorem B7197497 : Blo 2131435 7197497 := bstep (se 2 (by rfl) ⟨2699061, by rfl⟩ : syracuseStep 7197497 = 5398123) B5398123
theorem B4798331 : Blo 2131435 4798331 := bstep (se 1 (by rfl) ⟨3598748, by rfl⟩ : syracuseStep 4798331 = 7197497) B7197497
theorem B3198887 : Blo 2131435 3198887 := bstep (se 1 (by rfl) ⟨2399165, by rfl⟩ : syracuseStep 3198887 = 4798331) B4798331
theorem B2132591 : Blo 2131435 2132591 := bstep (se 1 (by rfl) ⟨1599443, by rfl⟩ : syracuseStep 2132591 = 3198887) B3198887
theorem B3198893 : Blo 2131435 3198893 := bbase (se 3 (by rfl) ⟨599792, by rfl⟩ : syracuseStep 3198893 = 1199585) (by norm_num)
theorem B2132595 : Blo 2131435 2132595 := bstep (se 1 (by rfl) ⟨1599446, by rfl⟩ : syracuseStep 2132595 = 3198893) B3198893
theorem B4798349 : Blo 2131435 4798349 := bbase (se 3 (by rfl) ⟨899690, by rfl⟩ : syracuseStep 4798349 = 1799381) (by norm_num)
theorem B3198899 : Blo 2131435 3198899 := bstep (se 1 (by rfl) ⟨2399174, by rfl⟩ : syracuseStep 3198899 = 4798349) B4798349
theorem B2132599 : Blo 2131435 2132599 := bstep (se 1 (by rfl) ⟨1599449, by rfl⟩ : syracuseStep 2132599 = 3198899) B3198899
theorem B2699077 : Blo 2131435 2699077 := bbase (se 4 (by rfl) ⟨253038, by rfl⟩ : syracuseStep 2699077 = 506077) (by norm_num)
theorem B3598769 : Blo 2131435 3598769 := bstep (se 2 (by rfl) ⟨1349538, by rfl⟩ : syracuseStep 3598769 = 2699077) B2699077
theorem B2399179 : Blo 2131435 2399179 := bstep (se 1 (by rfl) ⟨1799384, by rfl⟩ : syracuseStep 2399179 = 3598769) B3598769
theorem B3198905 : Blo 2131435 3198905 := bstep (se 2 (by rfl) ⟨1199589, by rfl⟩ : syracuseStep 3198905 = 2399179) B2399179
theorem B2132603 : Blo 2131435 2132603 := bstep (se 1 (by rfl) ⟨1599452, by rfl⟩ : syracuseStep 2132603 = 3198905) B3198905
theorem B3843029 : Blo 2131435 3843029 := bbase (se 7 (by rfl) ⟨45035, by rfl⟩ : syracuseStep 3843029 = 90071) (by norm_num)
theorem B10248077 : Blo 2131435 10248077 := bstep (se 3 (by rfl) ⟨1921514, by rfl⟩ : syracuseStep 10248077 = 3843029) B3843029
theorem B27328205 : Blo 2131435 27328205 := bstep (se 3 (by rfl) ⟨5124038, by rfl⟩ : syracuseStep 27328205 = 10248077) B10248077
theorem B18218803 : Blo 2131435 18218803 := bstep (se 1 (by rfl) ⟨13664102, by rfl⟩ : syracuseStep 18218803 = 27328205) B27328205
theorem B24291737 : Blo 2131435 24291737 := bstep (se 2 (by rfl) ⟨9109401, by rfl⟩ : syracuseStep 24291737 = 18218803) B18218803
theorem B16194491 : Blo 2131435 16194491 := bstep (se 1 (by rfl) ⟨12145868, by rfl⟩ : syracuseStep 16194491 = 24291737) B24291737
theorem B10796327 : Blo 2131435 10796327 := bstep (se 1 (by rfl) ⟨8097245, by rfl⟩ : syracuseStep 10796327 = 16194491) B16194491
theorem B7197551 : Blo 2131435 7197551 := bstep (se 1 (by rfl) ⟨5398163, by rfl⟩ : syracuseStep 7197551 = 10796327) B10796327
theorem B4798367 : Blo 2131435 4798367 := bstep (se 1 (by rfl) ⟨3598775, by rfl⟩ : syracuseStep 4798367 = 7197551) B7197551
theorem B3198911 : Blo 2131435 3198911 := bstep (se 1 (by rfl) ⟨2399183, by rfl⟩ : syracuseStep 3198911 = 4798367) B4798367
theorem B2132607 : Blo 2131435 2132607 := bstep (se 1 (by rfl) ⟨1599455, by rfl⟩ : syracuseStep 2132607 = 3198911) B3198911
theorem B3198917 : Blo 2131435 3198917 := bbase (se 4 (by rfl) ⟨299898, by rfl⟩ : syracuseStep 3198917 = 599797) (by norm_num)
theorem B2132611 : Blo 2131435 2132611 := bstep (se 1 (by rfl) ⟨1599458, by rfl⟩ : syracuseStep 2132611 = 3198917) B3198917
theorem B3598789 : Blo 2131435 3598789 := bbase (se 4 (by rfl) ⟨337386, by rfl⟩ : syracuseStep 3598789 = 674773) (by norm_num)
theorem B4798385 : Blo 2131435 4798385 := bstep (se 2 (by rfl) ⟨1799394, by rfl⟩ : syracuseStep 4798385 = 3598789) B3598789
theorem B3198923 : Blo 2131435 3198923 := bstep (se 1 (by rfl) ⟨2399192, by rfl⟩ : syracuseStep 3198923 = 4798385) B4798385
theorem B2132615 : Blo 2131435 2132615 := bstep (se 1 (by rfl) ⟨1599461, by rfl⟩ : syracuseStep 2132615 = 3198923) B3198923
theorem B2399197 : Blo 2131435 2399197 := bbase (se 3 (by rfl) ⟨449849, by rfl⟩ : syracuseStep 2399197 = 899699) (by norm_num)
theorem B3198929 : Blo 2131435 3198929 := bstep (se 2 (by rfl) ⟨1199598, by rfl⟩ : syracuseStep 3198929 = 2399197) B2399197
theorem B2132619 : Blo 2131435 2132619 := bstep (se 1 (by rfl) ⟨1599464, by rfl⟩ : syracuseStep 2132619 = 3198929) B3198929
theorem B7197605 : Blo 2131435 7197605 := bbase (se 4 (by rfl) ⟨674775, by rfl⟩ : syracuseStep 7197605 = 1349551) (by norm_num)
theorem B4798403 : Blo 2131435 4798403 := bstep (se 1 (by rfl) ⟨3598802, by rfl⟩ : syracuseStep 4798403 = 7197605) B7197605
theorem B3198935 : Blo 2131435 3198935 := bstep (se 1 (by rfl) ⟨2399201, by rfl⟩ : syracuseStep 3198935 = 4798403) B4798403
theorem B2132623 : Blo 2131435 2132623 := bstep (se 1 (by rfl) ⟨1599467, by rfl⟩ : syracuseStep 2132623 = 3198935) B3198935
theorem B3198941 : Blo 2131435 3198941 := bbase (se 3 (by rfl) ⟨599801, by rfl⟩ : syracuseStep 3198941 = 1199603) (by norm_num)
theorem B2132627 : Blo 2131435 2132627 := bstep (se 1 (by rfl) ⟨1599470, by rfl⟩ : syracuseStep 2132627 = 3198941) B3198941
theorem B4798421 : Blo 2131435 4798421 := bbase (se 7 (by rfl) ⟨56231, by rfl⟩ : syracuseStep 4798421 = 112463) (by norm_num)
theorem B3198947 : Blo 2131435 3198947 := bstep (se 1 (by rfl) ⟨2399210, by rfl⟩ : syracuseStep 3198947 = 4798421) B4798421
theorem B2132631 : Blo 2131435 2132631 := bstep (se 1 (by rfl) ⟨1599473, by rfl⟩ : syracuseStep 2132631 = 3198947) B3198947
theorem B2161733 : Blo 2131435 2161733 := bbase (se 4 (by rfl) ⟨202662, by rfl⟩ : syracuseStep 2161733 = 405325) (by norm_num)
theorem B5764621 : Blo 2131435 5764621 := bstep (se 3 (by rfl) ⟨1080866, by rfl⟩ : syracuseStep 5764621 = 2161733) B2161733
theorem B7686161 : Blo 2131435 7686161 := bstep (se 2 (by rfl) ⟨2882310, by rfl⟩ : syracuseStep 7686161 = 5764621) B5764621
theorem B5124107 : Blo 2131435 5124107 := bstep (se 1 (by rfl) ⟨3843080, by rfl⟩ : syracuseStep 5124107 = 7686161) B7686161
theorem B13664285 : Blo 2131435 13664285 := bstep (se 3 (by rfl) ⟨2562053, by rfl⟩ : syracuseStep 13664285 = 5124107) B5124107
theorem B9109523 : Blo 2131435 9109523 := bstep (se 1 (by rfl) ⟨6832142, by rfl⟩ : syracuseStep 9109523 = 13664285) B13664285
theorem B6073015 : Blo 2131435 6073015 := bstep (se 1 (by rfl) ⟨4554761, by rfl⟩ : syracuseStep 6073015 = 9109523) B9109523
theorem B8097353 : Blo 2131435 8097353 := bstep (se 2 (by rfl) ⟨3036507, by rfl⟩ : syracuseStep 8097353 = 6073015) B6073015
theorem B5398235 : Blo 2131435 5398235 := bstep (se 1 (by rfl) ⟨4048676, by rfl⟩ : syracuseStep 5398235 = 8097353) B8097353
theorem B3598823 : Blo 2131435 3598823 := bstep (se 1 (by rfl) ⟨2699117, by rfl⟩ : syracuseStep 3598823 = 5398235) B5398235
theorem B2399215 : Blo 2131435 2399215 := bstep (se 1 (by rfl) ⟨1799411, by rfl⟩ : syracuseStep 2399215 = 3598823) B3598823
theorem B3198953 : Blo 2131435 3198953 := bstep (se 2 (by rfl) ⟨1199607, by rfl⟩ : syracuseStep 3198953 = 2399215) B2399215
theorem B2132635 : Blo 2131435 2132635 := bstep (se 1 (by rfl) ⟨1599476, by rfl⟩ : syracuseStep 2132635 = 3198953) B3198953
theorem B3416077 : Blo 2131435 3416077 := bbase (se 3 (by rfl) ⟨640514, by rfl⟩ : syracuseStep 3416077 = 1281029) (by norm_num)
theorem B18219077 : Blo 2131435 18219077 := bstep (se 4 (by rfl) ⟨1708038, by rfl⟩ : syracuseStep 18219077 = 3416077) B3416077
theorem B12146051 : Blo 2131435 12146051 := bstep (se 1 (by rfl) ⟨9109538, by rfl⟩ : syracuseStep 12146051 = 18219077) B18219077
theorem B8097367 : Blo 2131435 8097367 := bstep (se 1 (by rfl) ⟨6073025, by rfl⟩ : syracuseStep 8097367 = 12146051) B12146051
theorem B10796489 : Blo 2131435 10796489 := bstep (se 2 (by rfl) ⟨4048683, by rfl⟩ : syracuseStep 10796489 = 8097367) B8097367
theorem B7197659 : Blo 2131435 7197659 := bstep (se 1 (by rfl) ⟨5398244, by rfl⟩ : syracuseStep 7197659 = 10796489) B10796489
theorem B4798439 : Blo 2131435 4798439 := bstep (se 1 (by rfl) ⟨3598829, by rfl⟩ : syracuseStep 4798439 = 7197659) B7197659
theorem B3198959 : Blo 2131435 3198959 := bstep (se 1 (by rfl) ⟨2399219, by rfl⟩ : syracuseStep 3198959 = 4798439) B4798439
theorem B2132639 : Blo 2131435 2132639 := bstep (se 1 (by rfl) ⟨1599479, by rfl⟩ : syracuseStep 2132639 = 3198959) B3198959
theorem B3198965 : Blo 2131435 3198965 := bbase (se 5 (by rfl) ⟨149951, by rfl⟩ : syracuseStep 3198965 = 299903) (by norm_num)
theorem B2132643 : Blo 2131435 2132643 := bstep (se 1 (by rfl) ⟨1599482, by rfl⟩ : syracuseStep 2132643 = 3198965) B3198965
theorem B6832181 : Blo 2131435 6832181 := bbase (se 5 (by rfl) ⟨320258, by rfl⟩ : syracuseStep 6832181 = 640517) (by norm_num)
theorem B4554787 : Blo 2131435 4554787 := bstep (se 1 (by rfl) ⟨3416090, by rfl⟩ : syracuseStep 4554787 = 6832181) B6832181
theorem B6073049 : Blo 2131435 6073049 := bstep (se 2 (by rfl) ⟨2277393, by rfl⟩ : syracuseStep 6073049 = 4554787) B4554787
theorem B4048699 : Blo 2131435 4048699 := bstep (se 1 (by rfl) ⟨3036524, by rfl⟩ : syracuseStep 4048699 = 6073049) B6073049
theorem B5398265 : Blo 2131435 5398265 := bstep (se 2 (by rfl) ⟨2024349, by rfl⟩ : syracuseStep 5398265 = 4048699) B4048699
theorem B3598843 : Blo 2131435 3598843 := bstep (se 1 (by rfl) ⟨2699132, by rfl⟩ : syracuseStep 3598843 = 5398265) B5398265
theorem B4798457 : Blo 2131435 4798457 := bstep (se 2 (by rfl) ⟨1799421, by rfl⟩ : syracuseStep 4798457 = 3598843) B3598843
theorem B3198971 : Blo 2131435 3198971 := bstep (se 1 (by rfl) ⟨2399228, by rfl⟩ : syracuseStep 3198971 = 4798457) B4798457
theorem B2132647 : Blo 2131435 2132647 := bstep (se 1 (by rfl) ⟨1599485, by rfl⟩ : syracuseStep 2132647 = 3198971) B3198971
theorem B2399233 : Blo 2131435 2399233 := bbase (se 2 (by rfl) ⟨899712, by rfl⟩ : syracuseStep 2399233 = 1799425) (by norm_num)
theorem B3198977 : Blo 2131435 3198977 := bstep (se 2 (by rfl) ⟨1199616, by rfl⟩ : syracuseStep 3198977 = 2399233) B2399233
theorem B2132651 : Blo 2131435 2132651 := bstep (se 1 (by rfl) ⟨1599488, by rfl⟩ : syracuseStep 2132651 = 3198977) B3198977
theorem B5398285 : Blo 2131435 5398285 := bbase (se 3 (by rfl) ⟨1012178, by rfl⟩ : syracuseStep 5398285 = 2024357) (by norm_num)
theorem B7197713 : Blo 2131435 7197713 := bstep (se 2 (by rfl) ⟨2699142, by rfl⟩ : syracuseStep 7197713 = 5398285) B5398285
theorem B4798475 : Blo 2131435 4798475 := bstep (se 1 (by rfl) ⟨3598856, by rfl⟩ : syracuseStep 4798475 = 7197713) B7197713
theorem B3198983 : Blo 2131435 3198983 := bstep (se 1 (by rfl) ⟨2399237, by rfl⟩ : syracuseStep 3198983 = 4798475) B4798475
theorem B2132655 : Blo 2131435 2132655 := bstep (se 1 (by rfl) ⟨1599491, by rfl⟩ : syracuseStep 2132655 = 3198983) B3198983
theorem B3198989 : Blo 2131435 3198989 := bbase (se 3 (by rfl) ⟨599810, by rfl⟩ : syracuseStep 3198989 = 1199621) (by norm_num)
theorem B2132659 : Blo 2131435 2132659 := bstep (se 1 (by rfl) ⟨1599494, by rfl⟩ : syracuseStep 2132659 = 3198989) B3198989
theorem B4798493 : Blo 2131435 4798493 := bbase (se 3 (by rfl) ⟨899717, by rfl⟩ : syracuseStep 4798493 = 1799435) (by norm_num)
theorem B3198995 : Blo 2131435 3198995 := bstep (se 1 (by rfl) ⟨2399246, by rfl⟩ : syracuseStep 3198995 = 4798493) B4798493
theorem B2132663 : Blo 2131435 2132663 := bstep (se 1 (by rfl) ⟨1599497, by rfl⟩ : syracuseStep 2132663 = 3198995) B3198995
theorem B3598877 : Blo 2131435 3598877 := bbase (se 3 (by rfl) ⟨674789, by rfl⟩ : syracuseStep 3598877 = 1349579) (by norm_num)
theorem B2399251 : Blo 2131435 2399251 := bstep (se 1 (by rfl) ⟨1799438, by rfl⟩ : syracuseStep 2399251 = 3598877) B3598877
theorem B3199001 : Blo 2131435 3199001 := bstep (se 2 (by rfl) ⟨1199625, by rfl⟩ : syracuseStep 3199001 = 2399251) B2399251
theorem B2132667 : Blo 2131435 2132667 := bstep (se 1 (by rfl) ⟨1599500, by rfl⟩ : syracuseStep 2132667 = 3199001) B3199001
theorem B2161769 : Blo 2131435 2161769 := bbase (se 2 (by rfl) ⟨810663, by rfl⟩ : syracuseStep 2161769 = 1621327) (by norm_num)
theorem B5764717 : Blo 2131435 5764717 := bstep (se 3 (by rfl) ⟨1080884, by rfl⟩ : syracuseStep 5764717 = 2161769) B2161769
theorem B7686289 : Blo 2131435 7686289 := bstep (se 2 (by rfl) ⟨2882358, by rfl⟩ : syracuseStep 7686289 = 5764717) B5764717
theorem B10248385 : Blo 2131435 10248385 := bstep (se 2 (by rfl) ⟨3843144, by rfl⟩ : syracuseStep 10248385 = 7686289) B7686289
theorem B13664513 : Blo 2131435 13664513 := bstep (se 2 (by rfl) ⟨5124192, by rfl⟩ : syracuseStep 13664513 = 10248385) B10248385
theorem B9109675 : Blo 2131435 9109675 := bstep (se 1 (by rfl) ⟨6832256, by rfl⟩ : syracuseStep 9109675 = 13664513) B13664513
theorem B12146233 : Blo 2131435 12146233 := bstep (se 2 (by rfl) ⟨4554837, by rfl⟩ : syracuseStep 12146233 = 9109675) B9109675
theorem B16194977 : Blo 2131435 16194977 := bstep (se 2 (by rfl) ⟨6073116, by rfl⟩ : syracuseStep 16194977 = 12146233) B12146233
theorem B10796651 : Blo 2131435 10796651 := bstep (se 1 (by rfl) ⟨8097488, by rfl⟩ : syracuseStep 10796651 = 16194977) B16194977
theorem B7197767 : Blo 2131435 7197767 := bstep (se 1 (by rfl) ⟨5398325, by rfl⟩ : syracuseStep 7197767 = 10796651) B10796651
theorem B4798511 : Blo 2131435 4798511 := bstep (se 1 (by rfl) ⟨3598883, by rfl⟩ : syracuseStep 4798511 = 7197767) B7197767
theorem B3199007 : Blo 2131435 3199007 := bstep (se 1 (by rfl) ⟨2399255, by rfl⟩ : syracuseStep 3199007 = 4798511) B4798511
theorem B2132671 : Blo 2131435 2132671 := bstep (se 1 (by rfl) ⟨1599503, by rfl⟩ : syracuseStep 2132671 = 3199007) B3199007
theorem B3199013 : Blo 2131435 3199013 := bbase (se 4 (by rfl) ⟨299907, by rfl⟩ : syracuseStep 3199013 = 599815) (by norm_num)
theorem B2132675 : Blo 2131435 2132675 := bstep (se 1 (by rfl) ⟨1599506, by rfl⟩ : syracuseStep 2132675 = 3199013) B3199013
theorem B2699173 : Blo 2131435 2699173 := bbase (se 4 (by rfl) ⟨253047, by rfl⟩ : syracuseStep 2699173 = 506095) (by norm_num)
theorem B3598897 : Blo 2131435 3598897 := bstep (se 2 (by rfl) ⟨1349586, by rfl⟩ : syracuseStep 3598897 = 2699173) B2699173
theorem B4798529 : Blo 2131435 4798529 := bstep (se 2 (by rfl) ⟨1799448, by rfl⟩ : syracuseStep 4798529 = 3598897) B3598897
theorem B3199019 : Blo 2131435 3199019 := bstep (se 1 (by rfl) ⟨2399264, by rfl⟩ : syracuseStep 3199019 = 4798529) B4798529
theorem B2132679 : Blo 2131435 2132679 := bstep (se 1 (by rfl) ⟨1599509, by rfl⟩ : syracuseStep 2132679 = 3199019) B3199019
theorem B2399269 : Blo 2131435 2399269 := bbase (se 4 (by rfl) ⟨224931, by rfl⟩ : syracuseStep 2399269 = 449863) (by norm_num)
theorem B3199025 : Blo 2131435 3199025 := bstep (se 2 (by rfl) ⟨1199634, by rfl⟩ : syracuseStep 3199025 = 2399269) B2399269
theorem B2132683 : Blo 2131435 2132683 := bstep (se 1 (by rfl) ⟨1599512, by rfl⟩ : syracuseStep 2132683 = 3199025) B3199025
theorem B6832309 : Blo 2131435 6832309 := bbase (se 5 (by rfl) ⟨320264, by rfl⟩ : syracuseStep 6832309 = 640529) (by norm_num)
theorem B9109745 : Blo 2131435 9109745 := bstep (se 2 (by rfl) ⟨3416154, by rfl⟩ : syracuseStep 9109745 = 6832309) B6832309
theorem B6073163 : Blo 2131435 6073163 := bstep (se 1 (by rfl) ⟨4554872, by rfl⟩ : syracuseStep 6073163 = 9109745) B9109745
theorem B4048775 : Blo 2131435 4048775 := bstep (se 1 (by rfl) ⟨3036581, by rfl⟩ : syracuseStep 4048775 = 6073163) B6073163
theorem B2699183 : Blo 2131435 2699183 := bstep (se 1 (by rfl) ⟨2024387, by rfl⟩ : syracuseStep 2699183 = 4048775) B4048775
theorem B7197821 : Blo 2131435 7197821 := bstep (se 3 (by rfl) ⟨1349591, by rfl⟩ : syracuseStep 7197821 = 2699183) B2699183
theorem B4798547 : Blo 2131435 4798547 := bstep (se 1 (by rfl) ⟨3598910, by rfl⟩ : syracuseStep 4798547 = 7197821) B7197821
theorem B3199031 : Blo 2131435 3199031 := bstep (se 1 (by rfl) ⟨2399273, by rfl⟩ : syracuseStep 3199031 = 4798547) B4798547
theorem B2132687 : Blo 2131435 2132687 := bstep (se 1 (by rfl) ⟨1599515, by rfl⟩ : syracuseStep 2132687 = 3199031) B3199031
theorem B3199037 : Blo 2131435 3199037 := bbase (se 3 (by rfl) ⟨599819, by rfl⟩ : syracuseStep 3199037 = 1199639) (by norm_num)
theorem B2132691 : Blo 2131435 2132691 := bstep (se 1 (by rfl) ⟨1599518, by rfl⟩ : syracuseStep 2132691 = 3199037) B3199037
theorem B4798565 : Blo 2131435 4798565 := bbase (se 4 (by rfl) ⟨449865, by rfl⟩ : syracuseStep 4798565 = 899731) (by norm_num)
theorem B3199043 : Blo 2131435 3199043 := bstep (se 1 (by rfl) ⟨2399282, by rfl⟩ : syracuseStep 3199043 = 4798565) B4798565
theorem B2132695 : Blo 2131435 2132695 := bstep (se 1 (by rfl) ⟨1599521, by rfl⟩ : syracuseStep 2132695 = 3199043) B3199043
theorem B5398397 : Blo 2131435 5398397 := bbase (se 3 (by rfl) ⟨1012199, by rfl⟩ : syracuseStep 5398397 = 2024399) (by norm_num)
theorem B3598931 : Blo 2131435 3598931 := bstep (se 1 (by rfl) ⟨2699198, by rfl⟩ : syracuseStep 3598931 = 5398397) B5398397
theorem B2399287 : Blo 2131435 2399287 := bstep (se 1 (by rfl) ⟨1799465, by rfl⟩ : syracuseStep 2399287 = 3598931) B3598931
theorem B3199049 : Blo 2131435 3199049 := bstep (se 2 (by rfl) ⟨1199643, by rfl⟩ : syracuseStep 3199049 = 2399287) B2399287
theorem B2132699 : Blo 2131435 2132699 := bstep (se 1 (by rfl) ⟨1599524, by rfl⟩ : syracuseStep 2132699 = 3199049) B3199049
theorem B4048805 : Blo 2131435 4048805 := bbase (se 4 (by rfl) ⟨379575, by rfl⟩ : syracuseStep 4048805 = 759151) (by norm_num)
theorem B10796813 : Blo 2131435 10796813 := bstep (se 3 (by rfl) ⟨2024402, by rfl⟩ : syracuseStep 10796813 = 4048805) B4048805
theorem B7197875 : Blo 2131435 7197875 := bstep (se 1 (by rfl) ⟨5398406, by rfl⟩ : syracuseStep 7197875 = 10796813) B10796813
theorem B4798583 : Blo 2131435 4798583 := bstep (se 1 (by rfl) ⟨3598937, by rfl⟩ : syracuseStep 4798583 = 7197875) B7197875
theorem B3199055 : Blo 2131435 3199055 := bstep (se 1 (by rfl) ⟨2399291, by rfl⟩ : syracuseStep 3199055 = 4798583) B4798583
theorem B2132703 : Blo 2131435 2132703 := bstep (se 1 (by rfl) ⟨1599527, by rfl⟩ : syracuseStep 2132703 = 3199055) B3199055
theorem B3199061 : Blo 2131435 3199061 := bbase (se 8 (by rfl) ⟨18744, by rfl⟩ : syracuseStep 3199061 = 37489) (by norm_num)
theorem B2132707 : Blo 2131435 2132707 := bstep (se 1 (by rfl) ⟨1599530, by rfl⟩ : syracuseStep 2132707 = 3199061) B3199061
theorem B2882413 : Blo 2131435 2882413 := bbase (se 3 (by rfl) ⟨540452, by rfl⟩ : syracuseStep 2882413 = 1080905) (by norm_num)
theorem B3843217 : Blo 2131435 3843217 := bstep (se 2 (by rfl) ⟨1441206, by rfl⟩ : syracuseStep 3843217 = 2882413) B2882413
theorem B20497157 : Blo 2131435 20497157 := bstep (se 4 (by rfl) ⟨1921608, by rfl⟩ : syracuseStep 20497157 = 3843217) B3843217
theorem B13664771 : Blo 2131435 13664771 := bstep (se 1 (by rfl) ⟨10248578, by rfl⟩ : syracuseStep 13664771 = 20497157) B20497157
theorem B9109847 : Blo 2131435 9109847 := bstep (se 1 (by rfl) ⟨6832385, by rfl⟩ : syracuseStep 9109847 = 13664771) B13664771
theorem B6073231 : Blo 2131435 6073231 := bstep (se 1 (by rfl) ⟨4554923, by rfl⟩ : syracuseStep 6073231 = 9109847) B9109847
theorem B8097641 : Blo 2131435 8097641 := bstep (se 2 (by rfl) ⟨3036615, by rfl⟩ : syracuseStep 8097641 = 6073231) B6073231
theorem B5398427 : Blo 2131435 5398427 := bstep (se 1 (by rfl) ⟨4048820, by rfl⟩ : syracuseStep 5398427 = 8097641) B8097641
theorem B3598951 : Blo 2131435 3598951 := bstep (se 1 (by rfl) ⟨2699213, by rfl⟩ : syracuseStep 3598951 = 5398427) B5398427
theorem B4798601 : Blo 2131435 4798601 := bstep (se 2 (by rfl) ⟨1799475, by rfl⟩ : syracuseStep 4798601 = 3598951) B3598951
theorem B3199067 : Blo 2131435 3199067 := bstep (se 1 (by rfl) ⟨2399300, by rfl⟩ : syracuseStep 3199067 = 4798601) B4798601
theorem B2132711 : Blo 2131435 2132711 := bstep (se 1 (by rfl) ⟨1599533, by rfl⟩ : syracuseStep 2132711 = 3199067) B3199067
theorem B2399305 : Blo 2131435 2399305 := bbase (se 2 (by rfl) ⟨899739, by rfl⟩ : syracuseStep 2399305 = 1799479) (by norm_num)
theorem B3199073 : Blo 2131435 3199073 := bstep (se 2 (by rfl) ⟨1199652, by rfl⟩ : syracuseStep 3199073 = 2399305) B2399305
theorem B2132715 : Blo 2131435 2132715 := bstep (se 1 (by rfl) ⟨1599536, by rfl⟩ : syracuseStep 2132715 = 3199073) B3199073
theorem B13664821 : Blo 2131435 13664821 := bbase (se 5 (by rfl) ⟨640538, by rfl⟩ : syracuseStep 13664821 = 1281077) (by norm_num)
theorem B18219761 : Blo 2131435 18219761 := bstep (se 2 (by rfl) ⟨6832410, by rfl⟩ : syracuseStep 18219761 = 13664821) B13664821
theorem B12146507 : Blo 2131435 12146507 := bstep (se 1 (by rfl) ⟨9109880, by rfl⟩ : syracuseStep 12146507 = 18219761) B18219761
theorem B8097671 : Blo 2131435 8097671 := bstep (se 1 (by rfl) ⟨6073253, by rfl⟩ : syracuseStep 8097671 = 12146507) B12146507
theorem B5398447 : Blo 2131435 5398447 := bstep (se 1 (by rfl) ⟨4048835, by rfl⟩ : syracuseStep 5398447 = 8097671) B8097671
theorem B7197929 : Blo 2131435 7197929 := bstep (se 2 (by rfl) ⟨2699223, by rfl⟩ : syracuseStep 7197929 = 5398447) B5398447
theorem B4798619 : Blo 2131435 4798619 := bstep (se 1 (by rfl) ⟨3598964, by rfl⟩ : syracuseStep 4798619 = 7197929) B7197929
theorem B3199079 : Blo 2131435 3199079 := bstep (se 1 (by rfl) ⟨2399309, by rfl⟩ : syracuseStep 3199079 = 4798619) B4798619
theorem B2132719 : Blo 2131435 2132719 := bstep (se 1 (by rfl) ⟨1599539, by rfl⟩ : syracuseStep 2132719 = 3199079) B3199079
theorem B3199085 : Blo 2131435 3199085 := bbase (se 3 (by rfl) ⟨599828, by rfl⟩ : syracuseStep 3199085 = 1199657) (by norm_num)
theorem B2132723 : Blo 2131435 2132723 := bstep (se 1 (by rfl) ⟨1599542, by rfl⟩ : syracuseStep 2132723 = 3199085) B3199085
theorem B4798637 : Blo 2131435 4798637 := bbase (se 3 (by rfl) ⟨899744, by rfl⟩ : syracuseStep 4798637 = 1799489) (by norm_num)
theorem B3199091 : Blo 2131435 3199091 := bstep (se 1 (by rfl) ⟨2399318, by rfl⟩ : syracuseStep 3199091 = 4798637) B4798637
theorem B2132727 : Blo 2131435 2132727 := bstep (se 1 (by rfl) ⟨1599545, by rfl⟩ : syracuseStep 2132727 = 3199091) B3199091
theorem B10248677 : Blo 2131435 10248677 := bbase (se 4 (by rfl) ⟨960813, by rfl⟩ : syracuseStep 10248677 = 1921627) (by norm_num)
theorem B6832451 : Blo 2131435 6832451 := bstep (se 1 (by rfl) ⟨5124338, by rfl⟩ : syracuseStep 6832451 = 10248677) B10248677
theorem B4554967 : Blo 2131435 4554967 := bstep (se 1 (by rfl) ⟨3416225, by rfl⟩ : syracuseStep 4554967 = 6832451) B6832451
theorem B6073289 : Blo 2131435 6073289 := bstep (se 2 (by rfl) ⟨2277483, by rfl⟩ : syracuseStep 6073289 = 4554967) B4554967
theorem B4048859 : Blo 2131435 4048859 := bstep (se 1 (by rfl) ⟨3036644, by rfl⟩ : syracuseStep 4048859 = 6073289) B6073289
theorem B2699239 : Blo 2131435 2699239 := bstep (se 1 (by rfl) ⟨2024429, by rfl⟩ : syracuseStep 2699239 = 4048859) B4048859
theorem B3598985 : Blo 2131435 3598985 := bstep (se 2 (by rfl) ⟨1349619, by rfl⟩ : syracuseStep 3598985 = 2699239) B2699239
theorem B2399323 : Blo 2131435 2399323 := bstep (se 1 (by rfl) ⟨1799492, by rfl⟩ : syracuseStep 2399323 = 3598985) B3598985
theorem B3199097 : Blo 2131435 3199097 := bstep (se 2 (by rfl) ⟨1199661, by rfl⟩ : syracuseStep 3199097 = 2399323) B2399323
theorem B2132731 : Blo 2131435 2132731 := bstep (se 1 (by rfl) ⟨1599548, by rfl⟩ : syracuseStep 2132731 = 3199097) B3199097
theorem B2562173 : Blo 2131435 2562173 := bbase (se 3 (by rfl) ⟨480407, by rfl⟩ : syracuseStep 2562173 = 960815) (by norm_num)
theorem B27329845 : Blo 2131435 27329845 := bstep (se 5 (by rfl) ⟨1281086, by rfl⟩ : syracuseStep 27329845 = 2562173) B2562173
theorem B36439793 : Blo 2131435 36439793 := bstep (se 2 (by rfl) ⟨13664922, by rfl⟩ : syracuseStep 36439793 = 27329845) B27329845
theorem B24293195 : Blo 2131435 24293195 := bstep (se 1 (by rfl) ⟨18219896, by rfl⟩ : syracuseStep 24293195 = 36439793) B36439793
theorem B16195463 : Blo 2131435 16195463 := bstep (se 1 (by rfl) ⟨12146597, by rfl⟩ : syracuseStep 16195463 = 24293195) B24293195
theorem B10796975 : Blo 2131435 10796975 := bstep (se 1 (by rfl) ⟨8097731, by rfl⟩ : syracuseStep 10796975 = 16195463) B16195463
theorem B7197983 : Blo 2131435 7197983 := bstep (se 1 (by rfl) ⟨5398487, by rfl⟩ : syracuseStep 7197983 = 10796975) B10796975
theorem B4798655 : Blo 2131435 4798655 := bstep (se 1 (by rfl) ⟨3598991, by rfl⟩ : syracuseStep 4798655 = 7197983) B7197983
theorem B3199103 : Blo 2131435 3199103 := bstep (se 1 (by rfl) ⟨2399327, by rfl⟩ : syracuseStep 3199103 = 4798655) B4798655
theorem B2132735 : Blo 2131435 2132735 := bstep (se 1 (by rfl) ⟨1599551, by rfl⟩ : syracuseStep 2132735 = 3199103) B3199103
theorem B3199109 : Blo 2131435 3199109 := bbase (se 4 (by rfl) ⟨299916, by rfl⟩ : syracuseStep 3199109 = 599833) (by norm_num)
theorem B2132739 : Blo 2131435 2132739 := bstep (se 1 (by rfl) ⟨1599554, by rfl⟩ : syracuseStep 2132739 = 3199109) B3199109
theorem B3599005 : Blo 2131435 3599005 := bbase (se 3 (by rfl) ⟨674813, by rfl⟩ : syracuseStep 3599005 = 1349627) (by norm_num)
theorem B4798673 : Blo 2131435 4798673 := bstep (se 2 (by rfl) ⟨1799502, by rfl⟩ : syracuseStep 4798673 = 3599005) B3599005
theorem B3199115 : Blo 2131435 3199115 := bstep (se 1 (by rfl) ⟨2399336, by rfl⟩ : syracuseStep 3199115 = 4798673) B4798673
theorem B2132743 : Blo 2131435 2132743 := bstep (se 1 (by rfl) ⟨1599557, by rfl⟩ : syracuseStep 2132743 = 3199115) B3199115
theorem B2399341 : Blo 2131435 2399341 := bbase (se 3 (by rfl) ⟨449876, by rfl⟩ : syracuseStep 2399341 = 899753) (by norm_num)
theorem B3199121 : Blo 2131435 3199121 := bstep (se 2 (by rfl) ⟨1199670, by rfl⟩ : syracuseStep 3199121 = 2399341) B2399341
theorem B2132747 : Blo 2131435 2132747 := bstep (se 1 (by rfl) ⟨1599560, by rfl⟩ : syracuseStep 2132747 = 3199121) B3199121
theorem B7198037 : Blo 2131435 7198037 := bbase (se 15 (by rfl) ⟨329, by rfl⟩ : syracuseStep 7198037 = 659) (by norm_num)
theorem B4798691 : Blo 2131435 4798691 := bstep (se 1 (by rfl) ⟨3599018, by rfl⟩ : syracuseStep 4798691 = 7198037) B7198037
theorem B3199127 : Blo 2131435 3199127 := bstep (se 1 (by rfl) ⟨2399345, by rfl⟩ : syracuseStep 3199127 = 4798691) B4798691
theorem B2132751 : Blo 2131435 2132751 := bstep (se 1 (by rfl) ⟨1599563, by rfl⟩ : syracuseStep 2132751 = 3199127) B3199127
theorem B3199133 : Blo 2131435 3199133 := bbase (se 3 (by rfl) ⟨599837, by rfl⟩ : syracuseStep 3199133 = 1199675) (by norm_num)
theorem B2132755 : Blo 2131435 2132755 := bstep (se 1 (by rfl) ⟨1599566, by rfl⟩ : syracuseStep 2132755 = 3199133) B3199133
theorem B4798709 : Blo 2131435 4798709 := bbase (se 5 (by rfl) ⟨224939, by rfl⟩ : syracuseStep 4798709 = 449879) (by norm_num)
theorem B3199139 : Blo 2131435 3199139 := bstep (se 1 (by rfl) ⟨2399354, by rfl⟩ : syracuseStep 3199139 = 4798709) B4798709
theorem B2132759 : Blo 2131435 2132759 := bstep (se 1 (by rfl) ⟨1599569, by rfl⟩ : syracuseStep 2132759 = 3199139) B3199139
theorem B13327541 : Blo 2131435 13327541 := bbase (se 5 (by rfl) ⟨624728, by rfl⟩ : syracuseStep 13327541 = 1249457) (by norm_num)
theorem B8885027 : Blo 2131435 8885027 := bstep (se 1 (by rfl) ⟨6663770, by rfl⟩ : syracuseStep 8885027 = 13327541) B13327541
theorem B5923351 : Blo 2131435 5923351 := bstep (se 1 (by rfl) ⟨4442513, by rfl⟩ : syracuseStep 5923351 = 8885027) B8885027
theorem B31591205 : Blo 2131435 31591205 := bstep (se 4 (by rfl) ⟨2961675, by rfl⟩ : syracuseStep 31591205 = 5923351) B5923351
theorem B21060803 : Blo 2131435 21060803 := bstep (se 1 (by rfl) ⟨15795602, by rfl⟩ : syracuseStep 21060803 = 31591205) B31591205
theorem B14040535 : Blo 2131435 14040535 := bstep (se 1 (by rfl) ⟨10530401, by rfl⟩ : syracuseStep 14040535 = 21060803) B21060803
theorem B18720713 : Blo 2131435 18720713 := bstep (se 2 (by rfl) ⟨7020267, by rfl⟩ : syracuseStep 18720713 = 14040535) B14040535
theorem B12480475 : Blo 2131435 12480475 := bstep (se 1 (by rfl) ⟨9360356, by rfl⟩ : syracuseStep 12480475 = 18720713) B18720713
theorem B16640633 : Blo 2131435 16640633 := bstep (se 2 (by rfl) ⟨6240237, by rfl⟩ : syracuseStep 16640633 = 12480475) B12480475
theorem B11093755 : Blo 2131435 11093755 := bstep (se 1 (by rfl) ⟨8320316, by rfl⟩ : syracuseStep 11093755 = 16640633) B16640633
theorem B14791673 : Blo 2131435 14791673 := bstep (se 2 (by rfl) ⟨5546877, by rfl⟩ : syracuseStep 14791673 = 11093755) B11093755
theorem B9861115 : Blo 2131435 9861115 := bstep (se 1 (by rfl) ⟨7395836, by rfl⟩ : syracuseStep 9861115 = 14791673) B14791673
theorem B13148153 : Blo 2131435 13148153 := bstep (se 2 (by rfl) ⟨4930557, by rfl⟩ : syracuseStep 13148153 = 9861115) B9861115
theorem B8765435 : Blo 2131435 8765435 := bstep (se 1 (by rfl) ⟨6574076, by rfl⟩ : syracuseStep 8765435 = 13148153) B13148153
theorem B5843623 : Blo 2131435 5843623 := bstep (se 1 (by rfl) ⟨4382717, by rfl⟩ : syracuseStep 5843623 = 8765435) B8765435
theorem B7791497 : Blo 2131435 7791497 := bstep (se 2 (by rfl) ⟨2921811, by rfl⟩ : syracuseStep 7791497 = 5843623) B5843623
theorem B5194331 : Blo 2131435 5194331 := bstep (se 1 (by rfl) ⟨3895748, by rfl⟩ : syracuseStep 5194331 = 7791497) B7791497
theorem B3462887 : Blo 2131435 3462887 := bstep (se 1 (by rfl) ⟨2597165, by rfl⟩ : syracuseStep 3462887 = 5194331) B5194331
theorem B2308591 : Blo 2131435 2308591 := bstep (se 1 (by rfl) ⟨1731443, by rfl⟩ : syracuseStep 2308591 = 3462887) B3462887
theorem B12312485 : Blo 2131435 12312485 := bstep (se 4 (by rfl) ⟨1154295, by rfl⟩ : syracuseStep 12312485 = 2308591) B2308591
theorem B8208323 : Blo 2131435 8208323 := bstep (se 1 (by rfl) ⟨6156242, by rfl⟩ : syracuseStep 8208323 = 12312485) B12312485
theorem B5472215 : Blo 2131435 5472215 := bstep (se 1 (by rfl) ⟨4104161, by rfl⟩ : syracuseStep 5472215 = 8208323) B8208323
theorem B3648143 : Blo 2131435 3648143 := bstep (se 1 (by rfl) ⟨2736107, by rfl⟩ : syracuseStep 3648143 = 5472215) B5472215
theorem B9728381 : Blo 2131435 9728381 := bstep (se 3 (by rfl) ⟨1824071, by rfl⟩ : syracuseStep 9728381 = 3648143) B3648143
theorem B25942349 : Blo 2131435 25942349 := bstep (se 3 (by rfl) ⟨4864190, by rfl⟩ : syracuseStep 25942349 = 9728381) B9728381
theorem B17294899 : Blo 2131435 17294899 := bstep (se 1 (by rfl) ⟨12971174, by rfl⟩ : syracuseStep 17294899 = 25942349) B25942349
theorem B23059865 : Blo 2131435 23059865 := bstep (se 2 (by rfl) ⟨8647449, by rfl⟩ : syracuseStep 23059865 = 17294899) B17294899
theorem B15373243 : Blo 2131435 15373243 := bstep (se 1 (by rfl) ⟨11529932, by rfl⟩ : syracuseStep 15373243 = 23059865) B23059865
theorem B20497657 : Blo 2131435 20497657 := bstep (se 2 (by rfl) ⟨7686621, by rfl⟩ : syracuseStep 20497657 = 15373243) B15373243
theorem B27330209 : Blo 2131435 27330209 := bstep (se 2 (by rfl) ⟨10248828, by rfl⟩ : syracuseStep 27330209 = 20497657) B20497657
theorem B18220139 : Blo 2131435 18220139 := bstep (se 1 (by rfl) ⟨13665104, by rfl⟩ : syracuseStep 18220139 = 27330209) B27330209
theorem B12146759 : Blo 2131435 12146759 := bstep (se 1 (by rfl) ⟨9110069, by rfl⟩ : syracuseStep 12146759 = 18220139) B18220139
theorem B8097839 : Blo 2131435 8097839 := bstep (se 1 (by rfl) ⟨6073379, by rfl⟩ : syracuseStep 8097839 = 12146759) B12146759
theorem B5398559 : Blo 2131435 5398559 := bstep (se 1 (by rfl) ⟨4048919, by rfl⟩ : syracuseStep 5398559 = 8097839) B8097839
theorem B3599039 : Blo 2131435 3599039 := bstep (se 1 (by rfl) ⟨2699279, by rfl⟩ : syracuseStep 3599039 = 5398559) B5398559
theorem B2399359 : Blo 2131435 2399359 := bstep (se 1 (by rfl) ⟨1799519, by rfl⟩ : syracuseStep 2399359 = 3599039) B3599039
theorem B3199145 : Blo 2131435 3199145 := bstep (se 2 (by rfl) ⟨1199679, by rfl⟩ : syracuseStep 3199145 = 2399359) B2399359
theorem B2132763 : Blo 2131435 2132763 := bstep (se 1 (by rfl) ⟨1599572, by rfl⟩ : syracuseStep 2132763 = 3199145) B3199145
theorem B6832565 : Blo 2131435 6832565 := bbase (se 5 (by rfl) ⟨320276, by rfl⟩ : syracuseStep 6832565 = 640553) (by norm_num)
theorem B4555043 : Blo 2131435 4555043 := bstep (se 1 (by rfl) ⟨3416282, by rfl⟩ : syracuseStep 4555043 = 6832565) B6832565
theorem B3036695 : Blo 2131435 3036695 := bstep (se 1 (by rfl) ⟨2277521, by rfl⟩ : syracuseStep 3036695 = 4555043) B4555043
theorem B8097853 : Blo 2131435 8097853 := bstep (se 3 (by rfl) ⟨1518347, by rfl⟩ : syracuseStep 8097853 = 3036695) B3036695
theorem B10797137 : Blo 2131435 10797137 := bstep (se 2 (by rfl) ⟨4048926, by rfl⟩ : syracuseStep 10797137 = 8097853) B8097853
theorem B7198091 : Blo 2131435 7198091 := bstep (se 1 (by rfl) ⟨5398568, by rfl⟩ : syracuseStep 7198091 = 10797137) B10797137
theorem B4798727 : Blo 2131435 4798727 := bstep (se 1 (by rfl) ⟨3599045, by rfl⟩ : syracuseStep 4798727 = 7198091) B7198091
theorem B3199151 : Blo 2131435 3199151 := bstep (se 1 (by rfl) ⟨2399363, by rfl⟩ : syracuseStep 3199151 = 4798727) B4798727
theorem B2132767 : Blo 2131435 2132767 := bstep (se 1 (by rfl) ⟨1599575, by rfl⟩ : syracuseStep 2132767 = 3199151) B3199151
theorem B3199157 : Blo 2131435 3199157 := bbase (se 5 (by rfl) ⟨149960, by rfl⟩ : syracuseStep 3199157 = 299921) (by norm_num)
theorem B2132771 : Blo 2131435 2132771 := bstep (se 1 (by rfl) ⟨1599578, by rfl⟩ : syracuseStep 2132771 = 3199157) B3199157
theorem B5398589 : Blo 2131435 5398589 := bbase (se 3 (by rfl) ⟨1012235, by rfl⟩ : syracuseStep 5398589 = 2024471) (by norm_num)
theorem B3599059 : Blo 2131435 3599059 := bstep (se 1 (by rfl) ⟨2699294, by rfl⟩ : syracuseStep 3599059 = 5398589) B5398589
theorem B4798745 : Blo 2131435 4798745 := bstep (se 2 (by rfl) ⟨1799529, by rfl⟩ : syracuseStep 4798745 = 3599059) B3599059
theorem B3199163 : Blo 2131435 3199163 := bstep (se 1 (by rfl) ⟨2399372, by rfl⟩ : syracuseStep 3199163 = 4798745) B4798745
theorem B2132775 : Blo 2131435 2132775 := bstep (se 1 (by rfl) ⟨1599581, by rfl⟩ : syracuseStep 2132775 = 3199163) B3199163
theorem B2399377 : Blo 2131435 2399377 := bbase (se 2 (by rfl) ⟨899766, by rfl⟩ : syracuseStep 2399377 = 1799533) (by norm_num)
theorem B3199169 : Blo 2131435 3199169 := bstep (se 2 (by rfl) ⟨1199688, by rfl⟩ : syracuseStep 3199169 = 2399377) B2399377
theorem B2132779 : Blo 2131435 2132779 := bstep (se 1 (by rfl) ⟨1599584, by rfl⟩ : syracuseStep 2132779 = 3199169) B3199169
theorem B4048957 : Blo 2131435 4048957 := bbase (se 3 (by rfl) ⟨759179, by rfl⟩ : syracuseStep 4048957 = 1518359) (by norm_num)
theorem B5398609 : Blo 2131435 5398609 := bstep (se 2 (by rfl) ⟨2024478, by rfl⟩ : syracuseStep 5398609 = 4048957) B4048957
theorem B7198145 : Blo 2131435 7198145 := bstep (se 2 (by rfl) ⟨2699304, by rfl⟩ : syracuseStep 7198145 = 5398609) B5398609
theorem B4798763 : Blo 2131435 4798763 := bstep (se 1 (by rfl) ⟨3599072, by rfl⟩ : syracuseStep 4798763 = 7198145) B7198145
theorem B3199175 : Blo 2131435 3199175 := bstep (se 1 (by rfl) ⟨2399381, by rfl⟩ : syracuseStep 3199175 = 4798763) B4798763
theorem B2132783 : Blo 2131435 2132783 := bstep (se 1 (by rfl) ⟨1599587, by rfl⟩ : syracuseStep 2132783 = 3199175) B3199175
theorem B3199181 : Blo 2131435 3199181 := bbase (se 3 (by rfl) ⟨599846, by rfl⟩ : syracuseStep 3199181 = 1199693) (by norm_num)
theorem B2132787 : Blo 2131435 2132787 := bstep (se 1 (by rfl) ⟨1599590, by rfl⟩ : syracuseStep 2132787 = 3199181) B3199181
theorem B4798781 : Blo 2131435 4798781 := bbase (se 3 (by rfl) ⟨899771, by rfl⟩ : syracuseStep 4798781 = 1799543) (by norm_num)
theorem B3199187 : Blo 2131435 3199187 := bstep (se 1 (by rfl) ⟨2399390, by rfl⟩ : syracuseStep 3199187 = 4798781) B4798781
theorem B2132791 : Blo 2131435 2132791 := bstep (se 1 (by rfl) ⟨1599593, by rfl⟩ : syracuseStep 2132791 = 3199187) B3199187
theorem B3599093 : Blo 2131435 3599093 := bbase (se 5 (by rfl) ⟨168707, by rfl⟩ : syracuseStep 3599093 = 337415) (by norm_num)
theorem B2399395 : Blo 2131435 2399395 := bstep (se 1 (by rfl) ⟨1799546, by rfl⟩ : syracuseStep 2399395 = 3599093) B3599093
theorem B3199193 : Blo 2131435 3199193 := bstep (se 2 (by rfl) ⟨1199697, by rfl⟩ : syracuseStep 3199193 = 2399395) B2399395
theorem B2132795 : Blo 2131435 2132795 := bstep (se 1 (by rfl) ⟨1599596, by rfl⟩ : syracuseStep 2132795 = 3199193) B3199193
theorem B3078173 : Blo 2131435 3078173 := bbase (se 3 (by rfl) ⟨577157, by rfl⟩ : syracuseStep 3078173 = 1154315) (by norm_num)
theorem B8208461 : Blo 2131435 8208461 := bstep (se 3 (by rfl) ⟨1539086, by rfl⟩ : syracuseStep 8208461 = 3078173) B3078173
theorem B5472307 : Blo 2131435 5472307 := bstep (se 1 (by rfl) ⟨4104230, by rfl⟩ : syracuseStep 5472307 = 8208461) B8208461
theorem B7296409 : Blo 2131435 7296409 := bstep (se 2 (by rfl) ⟨2736153, by rfl⟩ : syracuseStep 7296409 = 5472307) B5472307
theorem B38914181 : Blo 2131435 38914181 := bstep (se 4 (by rfl) ⟨3648204, by rfl⟩ : syracuseStep 38914181 = 7296409) B7296409
theorem B25942787 : Blo 2131435 25942787 := bstep (se 1 (by rfl) ⟨19457090, by rfl⟩ : syracuseStep 25942787 = 38914181) B38914181
theorem B17295191 : Blo 2131435 17295191 := bstep (se 1 (by rfl) ⟨12971393, by rfl⟩ : syracuseStep 17295191 = 25942787) B25942787
theorem B11530127 : Blo 2131435 11530127 := bstep (se 1 (by rfl) ⟨8647595, by rfl⟩ : syracuseStep 11530127 = 17295191) B17295191
theorem B7686751 : Blo 2131435 7686751 := bstep (se 1 (by rfl) ⟨5765063, by rfl⟩ : syracuseStep 7686751 = 11530127) B11530127
theorem B10249001 : Blo 2131435 10249001 := bstep (se 2 (by rfl) ⟨3843375, by rfl⟩ : syracuseStep 10249001 = 7686751) B7686751
theorem B6832667 : Blo 2131435 6832667 := bstep (se 1 (by rfl) ⟨5124500, by rfl⟩ : syracuseStep 6832667 = 10249001) B10249001
theorem B4555111 : Blo 2131435 4555111 := bstep (se 1 (by rfl) ⟨3416333, by rfl⟩ : syracuseStep 4555111 = 6832667) B6832667
theorem B6073481 : Blo 2131435 6073481 := bstep (se 2 (by rfl) ⟨2277555, by rfl⟩ : syracuseStep 6073481 = 4555111) B4555111
theorem B16195949 : Blo 2131435 16195949 := bstep (se 3 (by rfl) ⟨3036740, by rfl⟩ : syracuseStep 16195949 = 6073481) B6073481
theorem B10797299 : Blo 2131435 10797299 := bstep (se 1 (by rfl) ⟨8097974, by rfl⟩ : syracuseStep 10797299 = 16195949) B16195949
theorem B7198199 : Blo 2131435 7198199 := bstep (se 1 (by rfl) ⟨5398649, by rfl⟩ : syracuseStep 7198199 = 10797299) B10797299
theorem B4798799 : Blo 2131435 4798799 := bstep (se 1 (by rfl) ⟨3599099, by rfl⟩ : syracuseStep 4798799 = 7198199) B7198199
theorem B3199199 : Blo 2131435 3199199 := bstep (se 1 (by rfl) ⟨2399399, by rfl⟩ : syracuseStep 3199199 = 4798799) B4798799
theorem B2132799 : Blo 2131435 2132799 := bstep (se 1 (by rfl) ⟨1599599, by rfl⟩ : syracuseStep 2132799 = 3199199) B3199199
theorem B3199205 : Blo 2131435 3199205 := bbase (se 4 (by rfl) ⟨299925, by rfl⟩ : syracuseStep 3199205 = 599851) (by norm_num)
theorem B2132803 : Blo 2131435 2132803 := bstep (se 1 (by rfl) ⟨1599602, by rfl⟩ : syracuseStep 2132803 = 3199205) B3199205
theorem B6574213 : Blo 2131435 6574213 := bbase (se 4 (by rfl) ⟨616332, by rfl⟩ : syracuseStep 6574213 = 1232665) (by norm_num)
theorem B8765617 : Blo 2131435 8765617 := bstep (se 2 (by rfl) ⟨3287106, by rfl⟩ : syracuseStep 8765617 = 6574213) B6574213
theorem B11687489 : Blo 2131435 11687489 := bstep (se 2 (by rfl) ⟨4382808, by rfl⟩ : syracuseStep 11687489 = 8765617) B8765617
theorem B7791659 : Blo 2131435 7791659 := bstep (se 1 (by rfl) ⟨5843744, by rfl⟩ : syracuseStep 7791659 = 11687489) B11687489
theorem B5194439 : Blo 2131435 5194439 := bstep (se 1 (by rfl) ⟨3895829, by rfl⟩ : syracuseStep 5194439 = 7791659) B7791659
theorem B3462959 : Blo 2131435 3462959 := bstep (se 1 (by rfl) ⟨2597219, by rfl⟩ : syracuseStep 3462959 = 5194439) B5194439
theorem B9234557 : Blo 2131435 9234557 := bstep (se 3 (by rfl) ⟨1731479, by rfl⟩ : syracuseStep 9234557 = 3462959) B3462959
theorem B6156371 : Blo 2131435 6156371 := bstep (se 1 (by rfl) ⟨4617278, by rfl⟩ : syracuseStep 6156371 = 9234557) B9234557
theorem B16416989 : Blo 2131435 16416989 := bstep (se 3 (by rfl) ⟨3078185, by rfl⟩ : syracuseStep 16416989 = 6156371) B6156371
theorem B10944659 : Blo 2131435 10944659 := bstep (se 1 (by rfl) ⟨8208494, by rfl⟩ : syracuseStep 10944659 = 16416989) B16416989
theorem B29185757 : Blo 2131435 29185757 := bstep (se 3 (by rfl) ⟨5472329, by rfl⟩ : syracuseStep 29185757 = 10944659) B10944659
theorem B19457171 : Blo 2131435 19457171 := bstep (se 1 (by rfl) ⟨14592878, by rfl⟩ : syracuseStep 19457171 = 29185757) B29185757
theorem B12971447 : Blo 2131435 12971447 := bstep (se 1 (by rfl) ⟨9728585, by rfl⟩ : syracuseStep 12971447 = 19457171) B19457171
theorem B8647631 : Blo 2131435 8647631 := bstep (se 1 (by rfl) ⟨6485723, by rfl⟩ : syracuseStep 8647631 = 12971447) B12971447
theorem B5765087 : Blo 2131435 5765087 := bstep (se 1 (by rfl) ⟨4323815, by rfl⟩ : syracuseStep 5765087 = 8647631) B8647631
theorem B3843391 : Blo 2131435 3843391 := bstep (se 1 (by rfl) ⟨2882543, by rfl⟩ : syracuseStep 3843391 = 5765087) B5765087
theorem B5124521 : Blo 2131435 5124521 := bstep (se 2 (by rfl) ⟨1921695, by rfl⟩ : syracuseStep 5124521 = 3843391) B3843391
theorem B3416347 : Blo 2131435 3416347 := bstep (se 1 (by rfl) ⟨2562260, by rfl⟩ : syracuseStep 3416347 = 5124521) B5124521
theorem B4555129 : Blo 2131435 4555129 := bstep (se 2 (by rfl) ⟨1708173, by rfl⟩ : syracuseStep 4555129 = 3416347) B3416347
theorem B6073505 : Blo 2131435 6073505 := bstep (se 2 (by rfl) ⟨2277564, by rfl⟩ : syracuseStep 6073505 = 4555129) B4555129
theorem B4049003 : Blo 2131435 4049003 := bstep (se 1 (by rfl) ⟨3036752, by rfl⟩ : syracuseStep 4049003 = 6073505) B6073505
theorem B2699335 : Blo 2131435 2699335 := bstep (se 1 (by rfl) ⟨2024501, by rfl⟩ : syracuseStep 2699335 = 4049003) B4049003
theorem B3599113 : Blo 2131435 3599113 := bstep (se 2 (by rfl) ⟨1349667, by rfl⟩ : syracuseStep 3599113 = 2699335) B2699335
theorem B4798817 : Blo 2131435 4798817 := bstep (se 2 (by rfl) ⟨1799556, by rfl⟩ : syracuseStep 4798817 = 3599113) B3599113
theorem B3199211 : Blo 2131435 3199211 := bstep (se 1 (by rfl) ⟨2399408, by rfl⟩ : syracuseStep 3199211 = 4798817) B4798817
theorem B2132807 : Blo 2131435 2132807 := bstep (se 1 (by rfl) ⟨1599605, by rfl⟩ : syracuseStep 2132807 = 3199211) B3199211
theorem B2399413 : Blo 2131435 2399413 := bbase (se 5 (by rfl) ⟨112472, by rfl⟩ : syracuseStep 2399413 = 224945) (by norm_num)
theorem B3199217 : Blo 2131435 3199217 := bstep (se 2 (by rfl) ⟨1199706, by rfl⟩ : syracuseStep 3199217 = 2399413) B2399413
theorem B2132811 : Blo 2131435 2132811 := bstep (se 1 (by rfl) ⟨1599608, by rfl⟩ : syracuseStep 2132811 = 3199217) B3199217
theorem B2699345 : Blo 2131435 2699345 := bbase (se 2 (by rfl) ⟨1012254, by rfl⟩ : syracuseStep 2699345 = 2024509) (by norm_num)
theorem B7198253 : Blo 2131435 7198253 := bstep (se 3 (by rfl) ⟨1349672, by rfl⟩ : syracuseStep 7198253 = 2699345) B2699345
theorem B4798835 : Blo 2131435 4798835 := bstep (se 1 (by rfl) ⟨3599126, by rfl⟩ : syracuseStep 4798835 = 7198253) B7198253
theorem B3199223 : Blo 2131435 3199223 := bstep (se 1 (by rfl) ⟨2399417, by rfl⟩ : syracuseStep 3199223 = 4798835) B4798835
theorem B2132815 : Blo 2131435 2132815 := bstep (se 1 (by rfl) ⟨1599611, by rfl⟩ : syracuseStep 2132815 = 3199223) B3199223
theorem B3199229 : Blo 2131435 3199229 := bbase (se 3 (by rfl) ⟨599855, by rfl⟩ : syracuseStep 3199229 = 1199711) (by norm_num)
theorem B2132819 : Blo 2131435 2132819 := bstep (se 1 (by rfl) ⟨1599614, by rfl⟩ : syracuseStep 2132819 = 3199229) B3199229
theorem B4798853 : Blo 2131435 4798853 := bbase (se 4 (by rfl) ⟨449892, by rfl⟩ : syracuseStep 4798853 = 899785) (by norm_num)
theorem B3199235 : Blo 2131435 3199235 := bstep (se 1 (by rfl) ⟨2399426, by rfl⟩ : syracuseStep 3199235 = 4798853) B4798853
theorem B2132823 : Blo 2131435 2132823 := bstep (se 1 (by rfl) ⟨1599617, by rfl⟩ : syracuseStep 2132823 = 3199235) B3199235
theorem B3036781 : Blo 2131435 3036781 := bbase (se 3 (by rfl) ⟨569396, by rfl⟩ : syracuseStep 3036781 = 1138793) (by norm_num)
theorem B4049041 : Blo 2131435 4049041 := bstep (se 2 (by rfl) ⟨1518390, by rfl⟩ : syracuseStep 4049041 = 3036781) B3036781
theorem B5398721 : Blo 2131435 5398721 := bstep (se 2 (by rfl) ⟨2024520, by rfl⟩ : syracuseStep 5398721 = 4049041) B4049041
theorem B3599147 : Blo 2131435 3599147 := bstep (se 1 (by rfl) ⟨2699360, by rfl⟩ : syracuseStep 3599147 = 5398721) B5398721
theorem B2399431 : Blo 2131435 2399431 := bstep (se 1 (by rfl) ⟨1799573, by rfl⟩ : syracuseStep 2399431 = 3599147) B3599147
theorem B3199241 : Blo 2131435 3199241 := bstep (se 2 (by rfl) ⟨1199715, by rfl⟩ : syracuseStep 3199241 = 2399431) B2399431
theorem B2132827 : Blo 2131435 2132827 := bstep (se 1 (by rfl) ⟨1599620, by rfl⟩ : syracuseStep 2132827 = 3199241) B3199241
theorem B10797461 : Blo 2131435 10797461 := bbase (se 6 (by rfl) ⟨253065, by rfl⟩ : syracuseStep 10797461 = 506131) (by norm_num)
theorem B7198307 : Blo 2131435 7198307 := bstep (se 1 (by rfl) ⟨5398730, by rfl⟩ : syracuseStep 7198307 = 10797461) B10797461
theorem B4798871 : Blo 2131435 4798871 := bstep (se 1 (by rfl) ⟨3599153, by rfl⟩ : syracuseStep 4798871 = 7198307) B7198307
theorem B3199247 : Blo 2131435 3199247 := bstep (se 1 (by rfl) ⟨2399435, by rfl⟩ : syracuseStep 3199247 = 4798871) B4798871
theorem B2132831 : Blo 2131435 2132831 := bstep (se 1 (by rfl) ⟨1599623, by rfl⟩ : syracuseStep 2132831 = 3199247) B3199247
theorem B3199253 : Blo 2131435 3199253 := bbase (se 6 (by rfl) ⟨74982, by rfl⟩ : syracuseStep 3199253 = 149965) (by norm_num)
theorem B2132835 : Blo 2131435 2132835 := bstep (se 1 (by rfl) ⟨1599626, by rfl⟩ : syracuseStep 2132835 = 3199253) B3199253
theorem B2597257 : Blo 2131435 2597257 := bbase (se 2 (by rfl) ⟨973971, by rfl⟩ : syracuseStep 2597257 = 1947943) (by norm_num)
theorem B13852037 : Blo 2131435 13852037 := bstep (se 4 (by rfl) ⟨1298628, by rfl⟩ : syracuseStep 13852037 = 2597257) B2597257
theorem B9234691 : Blo 2131435 9234691 := bstep (se 1 (by rfl) ⟨6926018, by rfl⟩ : syracuseStep 9234691 = 13852037) B13852037
theorem B49251685 : Blo 2131435 49251685 := bstep (se 4 (by rfl) ⟨4617345, by rfl⟩ : syracuseStep 49251685 = 9234691) B9234691
theorem B65668913 : Blo 2131435 65668913 := bstep (se 2 (by rfl) ⟨24625842, by rfl⟩ : syracuseStep 65668913 = 49251685) B49251685
theorem B43779275 : Blo 2131435 43779275 := bstep (se 1 (by rfl) ⟨32834456, by rfl⟩ : syracuseStep 43779275 = 65668913) B65668913
theorem B29186183 : Blo 2131435 29186183 := bstep (se 1 (by rfl) ⟨21889637, by rfl⟩ : syracuseStep 29186183 = 43779275) B43779275
theorem B19457455 : Blo 2131435 19457455 := bstep (se 1 (by rfl) ⟨14593091, by rfl⟩ : syracuseStep 19457455 = 29186183) B29186183
theorem B25943273 : Blo 2131435 25943273 := bstep (se 2 (by rfl) ⟨9728727, by rfl⟩ : syracuseStep 25943273 = 19457455) B19457455
theorem B17295515 : Blo 2131435 17295515 := bstep (se 1 (by rfl) ⟨12971636, by rfl⟩ : syracuseStep 17295515 = 25943273) B25943273
theorem B11530343 : Blo 2131435 11530343 := bstep (se 1 (by rfl) ⟨8647757, by rfl⟩ : syracuseStep 11530343 = 17295515) B17295515
theorem B7686895 : Blo 2131435 7686895 := bstep (se 1 (by rfl) ⟨5765171, by rfl⟩ : syracuseStep 7686895 = 11530343) B11530343
theorem B10249193 : Blo 2131435 10249193 := bstep (se 2 (by rfl) ⟨3843447, by rfl⟩ : syracuseStep 10249193 = 7686895) B7686895
theorem B27331181 : Blo 2131435 27331181 := bstep (se 3 (by rfl) ⟨5124596, by rfl⟩ : syracuseStep 27331181 = 10249193) B10249193
theorem B18220787 : Blo 2131435 18220787 := bstep (se 1 (by rfl) ⟨13665590, by rfl⟩ : syracuseStep 18220787 = 27331181) B27331181
theorem B12147191 : Blo 2131435 12147191 := bstep (se 1 (by rfl) ⟨9110393, by rfl⟩ : syracuseStep 12147191 = 18220787) B18220787
theorem B8098127 : Blo 2131435 8098127 := bstep (se 1 (by rfl) ⟨6073595, by rfl⟩ : syracuseStep 8098127 = 12147191) B12147191
theorem B5398751 : Blo 2131435 5398751 := bstep (se 1 (by rfl) ⟨4049063, by rfl⟩ : syracuseStep 5398751 = 8098127) B8098127
theorem B3599167 : Blo 2131435 3599167 := bstep (se 1 (by rfl) ⟨2699375, by rfl⟩ : syracuseStep 3599167 = 5398751) B5398751
theorem B4798889 : Blo 2131435 4798889 := bstep (se 2 (by rfl) ⟨1799583, by rfl⟩ : syracuseStep 4798889 = 3599167) B3599167
theorem B3199259 : Blo 2131435 3199259 := bstep (se 1 (by rfl) ⟨2399444, by rfl⟩ : syracuseStep 3199259 = 4798889) B4798889
theorem B2132839 : Blo 2131435 2132839 := bstep (se 1 (by rfl) ⟨1599629, by rfl⟩ : syracuseStep 2132839 = 3199259) B3199259
theorem B2399449 : Blo 2131435 2399449 := bbase (se 2 (by rfl) ⟨899793, by rfl⟩ : syracuseStep 2399449 = 1799587) (by norm_num)
theorem B3199265 : Blo 2131435 3199265 := bstep (se 2 (by rfl) ⟨1199724, by rfl⟩ : syracuseStep 3199265 = 2399449) B2399449
theorem B2132843 : Blo 2131435 2132843 := bstep (se 1 (by rfl) ⟨1599632, by rfl⟩ : syracuseStep 2132843 = 3199265) B3199265
theorem B6485845 : Blo 2131435 6485845 := bbase (se 9 (by rfl) ⟨19001, by rfl⟩ : syracuseStep 6485845 = 38003) (by norm_num)
theorem B8647793 : Blo 2131435 8647793 := bstep (se 2 (by rfl) ⟨3242922, by rfl⟩ : syracuseStep 8647793 = 6485845) B6485845
theorem B5765195 : Blo 2131435 5765195 := bstep (se 1 (by rfl) ⟨4323896, by rfl⟩ : syracuseStep 5765195 = 8647793) B8647793
theorem B3843463 : Blo 2131435 3843463 := bstep (se 1 (by rfl) ⟨2882597, by rfl⟩ : syracuseStep 3843463 = 5765195) B5765195
theorem B5124617 : Blo 2131435 5124617 := bstep (se 2 (by rfl) ⟨1921731, by rfl⟩ : syracuseStep 5124617 = 3843463) B3843463
theorem B3416411 : Blo 2131435 3416411 := bstep (se 1 (by rfl) ⟨2562308, by rfl⟩ : syracuseStep 3416411 = 5124617) B5124617
theorem B2277607 : Blo 2131435 2277607 := bstep (se 1 (by rfl) ⟨1708205, by rfl⟩ : syracuseStep 2277607 = 3416411) B3416411
theorem B3036809 : Blo 2131435 3036809 := bstep (se 2 (by rfl) ⟨1138803, by rfl⟩ : syracuseStep 3036809 = 2277607) B2277607
theorem B8098157 : Blo 2131435 8098157 := bstep (se 3 (by rfl) ⟨1518404, by rfl⟩ : syracuseStep 8098157 = 3036809) B3036809
theorem B5398771 : Blo 2131435 5398771 := bstep (se 1 (by rfl) ⟨4049078, by rfl⟩ : syracuseStep 5398771 = 8098157) B8098157
theorem B7198361 : Blo 2131435 7198361 := bstep (se 2 (by rfl) ⟨2699385, by rfl⟩ : syracuseStep 7198361 = 5398771) B5398771
theorem B4798907 : Blo 2131435 4798907 := bstep (se 1 (by rfl) ⟨3599180, by rfl⟩ : syracuseStep 4798907 = 7198361) B7198361
theorem B3199271 : Blo 2131435 3199271 := bstep (se 1 (by rfl) ⟨2399453, by rfl⟩ : syracuseStep 3199271 = 4798907) B4798907
theorem B2132847 : Blo 2131435 2132847 := bstep (se 1 (by rfl) ⟨1599635, by rfl⟩ : syracuseStep 2132847 = 3199271) B3199271
theorem B3199277 : Blo 2131435 3199277 := bbase (se 3 (by rfl) ⟨599864, by rfl⟩ : syracuseStep 3199277 = 1199729) (by norm_num)
theorem B2132851 : Blo 2131435 2132851 := bstep (se 1 (by rfl) ⟨1599638, by rfl⟩ : syracuseStep 2132851 = 3199277) B3199277
theorem B4798925 : Blo 2131435 4798925 := bbase (se 3 (by rfl) ⟨899798, by rfl⟩ : syracuseStep 4798925 = 1799597) (by norm_num)
theorem B3199283 : Blo 2131435 3199283 := bstep (se 1 (by rfl) ⟨2399462, by rfl⟩ : syracuseStep 3199283 = 4798925) B4798925
theorem B2132855 : Blo 2131435 2132855 := bstep (se 1 (by rfl) ⟨1599641, by rfl⟩ : syracuseStep 2132855 = 3199283) B3199283
theorem B2699401 : Blo 2131435 2699401 := bbase (se 2 (by rfl) ⟨1012275, by rfl⟩ : syracuseStep 2699401 = 2024551) (by norm_num)
theorem B3599201 : Blo 2131435 3599201 := bstep (se 2 (by rfl) ⟨1349700, by rfl⟩ : syracuseStep 3599201 = 2699401) B2699401
theorem B2399467 : Blo 2131435 2399467 := bstep (se 1 (by rfl) ⟨1799600, by rfl⟩ : syracuseStep 2399467 = 3599201) B3599201
theorem B3199289 : Blo 2131435 3199289 := bstep (se 2 (by rfl) ⟨1199733, by rfl⟩ : syracuseStep 3199289 = 2399467) B2399467
theorem B2132859 : Blo 2131435 2132859 := bstep (se 1 (by rfl) ⟨1599644, by rfl⟩ : syracuseStep 2132859 = 3199289) B3199289
theorem B4617397 : Blo 2131435 4617397 := bbase (se 5 (by rfl) ⟨216440, by rfl⟩ : syracuseStep 4617397 = 432881) (by norm_num)
theorem B6156529 : Blo 2131435 6156529 := bstep (se 2 (by rfl) ⟨2308698, by rfl⟩ : syracuseStep 6156529 = 4617397) B4617397
theorem B32834821 : Blo 2131435 32834821 := bstep (se 4 (by rfl) ⟨3078264, by rfl⟩ : syracuseStep 32834821 = 6156529) B6156529
theorem B43779761 : Blo 2131435 43779761 := bstep (se 2 (by rfl) ⟨16417410, by rfl⟩ : syracuseStep 43779761 = 32834821) B32834821
theorem B29186507 : Blo 2131435 29186507 := bstep (se 1 (by rfl) ⟨21889880, by rfl⟩ : syracuseStep 29186507 = 43779761) B43779761
theorem B19457671 : Blo 2131435 19457671 := bstep (se 1 (by rfl) ⟨14593253, by rfl⟩ : syracuseStep 19457671 = 29186507) B29186507
theorem B25943561 : Blo 2131435 25943561 := bstep (se 2 (by rfl) ⟨9728835, by rfl⟩ : syracuseStep 25943561 = 19457671) B19457671
theorem B17295707 : Blo 2131435 17295707 := bstep (se 1 (by rfl) ⟨12971780, by rfl⟩ : syracuseStep 17295707 = 25943561) B25943561
theorem B46121885 : Blo 2131435 46121885 := bstep (se 3 (by rfl) ⟨8647853, by rfl⟩ : syracuseStep 46121885 = 17295707) B17295707
theorem B30747923 : Blo 2131435 30747923 := bstep (se 1 (by rfl) ⟨23060942, by rfl⟩ : syracuseStep 30747923 = 46121885) B46121885
theorem B20498615 : Blo 2131435 20498615 := bstep (se 1 (by rfl) ⟨15373961, by rfl⟩ : syracuseStep 20498615 = 30747923) B30747923
theorem B13665743 : Blo 2131435 13665743 := bstep (se 1 (by rfl) ⟨10249307, by rfl⟩ : syracuseStep 13665743 = 20498615) B20498615
theorem B9110495 : Blo 2131435 9110495 := bstep (se 1 (by rfl) ⟨6832871, by rfl⟩ : syracuseStep 9110495 = 13665743) B13665743
theorem B24294653 : Blo 2131435 24294653 := bstep (se 3 (by rfl) ⟨4555247, by rfl⟩ : syracuseStep 24294653 = 9110495) B9110495
theorem B16196435 : Blo 2131435 16196435 := bstep (se 1 (by rfl) ⟨12147326, by rfl⟩ : syracuseStep 16196435 = 24294653) B24294653
theorem B10797623 : Blo 2131435 10797623 := bstep (se 1 (by rfl) ⟨8098217, by rfl⟩ : syracuseStep 10797623 = 16196435) B16196435
theorem B7198415 : Blo 2131435 7198415 := bstep (se 1 (by rfl) ⟨5398811, by rfl⟩ : syracuseStep 7198415 = 10797623) B10797623
theorem B4798943 : Blo 2131435 4798943 := bstep (se 1 (by rfl) ⟨3599207, by rfl⟩ : syracuseStep 4798943 = 7198415) B7198415
theorem B3199295 : Blo 2131435 3199295 := bstep (se 1 (by rfl) ⟨2399471, by rfl⟩ : syracuseStep 3199295 = 4798943) B4798943
theorem B2132863 : Blo 2131435 2132863 := bstep (se 1 (by rfl) ⟨1599647, by rfl⟩ : syracuseStep 2132863 = 3199295) B3199295
theorem B3199301 : Blo 2131435 3199301 := bbase (se 4 (by rfl) ⟨299934, by rfl⟩ : syracuseStep 3199301 = 599869) (by norm_num)
theorem B2132867 : Blo 2131435 2132867 := bstep (se 1 (by rfl) ⟨1599650, by rfl⟩ : syracuseStep 2132867 = 3199301) B3199301
theorem B3599221 : Blo 2131435 3599221 := bbase (se 5 (by rfl) ⟨168713, by rfl⟩ : syracuseStep 3599221 = 337427) (by norm_num)
theorem B4798961 : Blo 2131435 4798961 := bstep (se 2 (by rfl) ⟨1799610, by rfl⟩ : syracuseStep 4798961 = 3599221) B3599221
theorem B3199307 : Blo 2131435 3199307 := bstep (se 1 (by rfl) ⟨2399480, by rfl⟩ : syracuseStep 3199307 = 4798961) B4798961
theorem B2132871 : Blo 2131435 2132871 := bstep (se 1 (by rfl) ⟨1599653, by rfl⟩ : syracuseStep 2132871 = 3199307) B3199307
theorem B2399485 : Blo 2131435 2399485 := bbase (se 3 (by rfl) ⟨449903, by rfl⟩ : syracuseStep 2399485 = 899807) (by norm_num)
theorem B3199313 : Blo 2131435 3199313 := bstep (se 2 (by rfl) ⟨1199742, by rfl⟩ : syracuseStep 3199313 = 2399485) B2399485
theorem B2132875 : Blo 2131435 2132875 := bstep (se 1 (by rfl) ⟨1599656, by rfl⟩ : syracuseStep 2132875 = 3199313) B3199313
theorem B7198469 : Blo 2131435 7198469 := bbase (se 4 (by rfl) ⟨674856, by rfl⟩ : syracuseStep 7198469 = 1349713) (by norm_num)
theorem B4798979 : Blo 2131435 4798979 := bstep (se 1 (by rfl) ⟨3599234, by rfl⟩ : syracuseStep 4798979 = 7198469) B7198469
theorem B3199319 : Blo 2131435 3199319 := bstep (se 1 (by rfl) ⟨2399489, by rfl⟩ : syracuseStep 3199319 = 4798979) B4798979
theorem B2132879 : Blo 2131435 2132879 := bstep (se 1 (by rfl) ⟨1599659, by rfl⟩ : syracuseStep 2132879 = 3199319) B3199319
theorem B3199325 : Blo 2131435 3199325 := bbase (se 3 (by rfl) ⟨599873, by rfl⟩ : syracuseStep 3199325 = 1199747) (by norm_num)
theorem B2132883 : Blo 2131435 2132883 := bstep (se 1 (by rfl) ⟨1599662, by rfl⟩ : syracuseStep 2132883 = 3199325) B3199325
theorem B4798997 : Blo 2131435 4798997 := bbase (se 6 (by rfl) ⟨112476, by rfl⟩ : syracuseStep 4798997 = 224953) (by norm_num)
theorem B3199331 : Blo 2131435 3199331 := bstep (se 1 (by rfl) ⟨2399498, by rfl⟩ : syracuseStep 3199331 = 4798997) B4798997
theorem B2132887 : Blo 2131435 2132887 := bstep (se 1 (by rfl) ⟨1599665, by rfl⟩ : syracuseStep 2132887 = 3199331) B3199331
theorem B8098325 : Blo 2131435 8098325 := bbase (se 6 (by rfl) ⟨189804, by rfl⟩ : syracuseStep 8098325 = 379609) (by norm_num)
theorem B5398883 : Blo 2131435 5398883 := bstep (se 1 (by rfl) ⟨4049162, by rfl⟩ : syracuseStep 5398883 = 8098325) B8098325
theorem B3599255 : Blo 2131435 3599255 := bstep (se 1 (by rfl) ⟨2699441, by rfl⟩ : syracuseStep 3599255 = 5398883) B5398883
theorem B2399503 : Blo 2131435 2399503 := bstep (se 1 (by rfl) ⟨1799627, by rfl⟩ : syracuseStep 2399503 = 3599255) B3599255
theorem B3199337 : Blo 2131435 3199337 := bstep (se 2 (by rfl) ⟨1199751, by rfl⟩ : syracuseStep 3199337 = 2399503) B2399503
theorem B2132891 : Blo 2131435 2132891 := bstep (se 1 (by rfl) ⟨1599668, by rfl⟩ : syracuseStep 2132891 = 3199337) B3199337
theorem B12147509 : Blo 2131435 12147509 := bbase (se 5 (by rfl) ⟨569414, by rfl⟩ : syracuseStep 12147509 = 1138829) (by norm_num)
theorem B8098339 : Blo 2131435 8098339 := bstep (se 1 (by rfl) ⟨6073754, by rfl⟩ : syracuseStep 8098339 = 12147509) B12147509
theorem B10797785 : Blo 2131435 10797785 := bstep (se 2 (by rfl) ⟨4049169, by rfl⟩ : syracuseStep 10797785 = 8098339) B8098339
theorem B7198523 : Blo 2131435 7198523 := bstep (se 1 (by rfl) ⟨5398892, by rfl⟩ : syracuseStep 7198523 = 10797785) B10797785
theorem B4799015 : Blo 2131435 4799015 := bstep (se 1 (by rfl) ⟨3599261, by rfl⟩ : syracuseStep 4799015 = 7198523) B7198523
theorem B3199343 : Blo 2131435 3199343 := bstep (se 1 (by rfl) ⟨2399507, by rfl⟩ : syracuseStep 3199343 = 4799015) B4799015
theorem B2132895 : Blo 2131435 2132895 := bstep (se 1 (by rfl) ⟨1599671, by rfl⟩ : syracuseStep 2132895 = 3199343) B3199343
theorem B3199349 : Blo 2131435 3199349 := bbase (se 5 (by rfl) ⟨149969, by rfl⟩ : syracuseStep 3199349 = 299939) (by norm_num)
theorem B2132899 : Blo 2131435 2132899 := bstep (se 1 (by rfl) ⟨1599674, by rfl⟩ : syracuseStep 2132899 = 3199349) B3199349
theorem B3416501 : Blo 2131435 3416501 := bbase (se 5 (by rfl) ⟨160148, by rfl⟩ : syracuseStep 3416501 = 320297) (by norm_num)
theorem B2277667 : Blo 2131435 2277667 := bstep (se 1 (by rfl) ⟨1708250, by rfl⟩ : syracuseStep 2277667 = 3416501) B3416501
theorem B3036889 : Blo 2131435 3036889 := bstep (se 2 (by rfl) ⟨1138833, by rfl⟩ : syracuseStep 3036889 = 2277667) B2277667
theorem B4049185 : Blo 2131435 4049185 := bstep (se 2 (by rfl) ⟨1518444, by rfl⟩ : syracuseStep 4049185 = 3036889) B3036889
theorem B5398913 : Blo 2131435 5398913 := bstep (se 2 (by rfl) ⟨2024592, by rfl⟩ : syracuseStep 5398913 = 4049185) B4049185
theorem B3599275 : Blo 2131435 3599275 := bstep (se 1 (by rfl) ⟨2699456, by rfl⟩ : syracuseStep 3599275 = 5398913) B5398913
theorem B4799033 : Blo 2131435 4799033 := bstep (se 2 (by rfl) ⟨1799637, by rfl⟩ : syracuseStep 4799033 = 3599275) B3599275
theorem B3199355 : Blo 2131435 3199355 := bstep (se 1 (by rfl) ⟨2399516, by rfl⟩ : syracuseStep 3199355 = 4799033) B4799033
theorem B2132903 : Blo 2131435 2132903 := bstep (se 1 (by rfl) ⟨1599677, by rfl⟩ : syracuseStep 2132903 = 3199355) B3199355
theorem B2399521 : Blo 2131435 2399521 := bbase (se 2 (by rfl) ⟨899820, by rfl⟩ : syracuseStep 2399521 = 1799641) (by norm_num)
theorem B3199361 : Blo 2131435 3199361 := bstep (se 2 (by rfl) ⟨1199760, by rfl⟩ : syracuseStep 3199361 = 2399521) B2399521
theorem B2132907 : Blo 2131435 2132907 := bstep (se 1 (by rfl) ⟨1599680, by rfl⟩ : syracuseStep 2132907 = 3199361) B3199361
theorem B5398933 : Blo 2131435 5398933 := bbase (se 6 (by rfl) ⟨126537, by rfl⟩ : syracuseStep 5398933 = 253075) (by norm_num)
theorem B7198577 : Blo 2131435 7198577 := bstep (se 2 (by rfl) ⟨2699466, by rfl⟩ : syracuseStep 7198577 = 5398933) B5398933
theorem B4799051 : Blo 2131435 4799051 := bstep (se 1 (by rfl) ⟨3599288, by rfl⟩ : syracuseStep 4799051 = 7198577) B7198577
theorem B3199367 : Blo 2131435 3199367 := bstep (se 1 (by rfl) ⟨2399525, by rfl⟩ : syracuseStep 3199367 = 4799051) B4799051
theorem B2132911 : Blo 2131435 2132911 := bstep (se 1 (by rfl) ⟨1599683, by rfl⟩ : syracuseStep 2132911 = 3199367) B3199367
theorem B3199373 : Blo 2131435 3199373 := bbase (se 3 (by rfl) ⟨599882, by rfl⟩ : syracuseStep 3199373 = 1199765) (by norm_num)
theorem B2132915 : Blo 2131435 2132915 := bstep (se 1 (by rfl) ⟨1599686, by rfl⟩ : syracuseStep 2132915 = 3199373) B3199373
theorem B4799069 : Blo 2131435 4799069 := bbase (se 3 (by rfl) ⟨899825, by rfl⟩ : syracuseStep 4799069 = 1799651) (by norm_num)
theorem B3199379 : Blo 2131435 3199379 := bstep (se 1 (by rfl) ⟨2399534, by rfl⟩ : syracuseStep 3199379 = 4799069) B4799069
theorem B2132919 : Blo 2131435 2132919 := bstep (se 1 (by rfl) ⟨1599689, by rfl⟩ : syracuseStep 2132919 = 3199379) B3199379
theorem B3599309 : Blo 2131435 3599309 := bbase (se 3 (by rfl) ⟨674870, by rfl⟩ : syracuseStep 3599309 = 1349741) (by norm_num)
theorem B2399539 : Blo 2131435 2399539 := bstep (se 1 (by rfl) ⟨1799654, by rfl⟩ : syracuseStep 2399539 = 3599309) B3599309
theorem B3199385 : Blo 2131435 3199385 := bstep (se 2 (by rfl) ⟨1199769, by rfl⟩ : syracuseStep 3199385 = 2399539) B2399539
theorem B2132923 : Blo 2131435 2132923 := bstep (se 1 (by rfl) ⟨1599692, by rfl⟩ : syracuseStep 2132923 = 3199385) B3199385
theorem B6486085 : Blo 2131435 6486085 := bbase (se 4 (by rfl) ⟨608070, by rfl⟩ : syracuseStep 6486085 = 1216141) (by norm_num)
theorem B34592453 : Blo 2131435 34592453 := bstep (se 4 (by rfl) ⟨3243042, by rfl⟩ : syracuseStep 34592453 = 6486085) B6486085
theorem B23061635 : Blo 2131435 23061635 := bstep (se 1 (by rfl) ⟨17296226, by rfl⟩ : syracuseStep 23061635 = 34592453) B34592453
theorem B15374423 : Blo 2131435 15374423 := bstep (se 1 (by rfl) ⟨11530817, by rfl⟩ : syracuseStep 15374423 = 23061635) B23061635
theorem B10249615 : Blo 2131435 10249615 := bstep (se 1 (by rfl) ⟨7687211, by rfl⟩ : syracuseStep 10249615 = 15374423) B15374423
theorem B13666153 : Blo 2131435 13666153 := bstep (se 2 (by rfl) ⟨5124807, by rfl⟩ : syracuseStep 13666153 = 10249615) B10249615
theorem B18221537 : Blo 2131435 18221537 := bstep (se 2 (by rfl) ⟨6833076, by rfl⟩ : syracuseStep 18221537 = 13666153) B13666153
theorem B12147691 : Blo 2131435 12147691 := bstep (se 1 (by rfl) ⟨9110768, by rfl⟩ : syracuseStep 12147691 = 18221537) B18221537
theorem B16196921 : Blo 2131435 16196921 := bstep (se 2 (by rfl) ⟨6073845, by rfl⟩ : syracuseStep 16196921 = 12147691) B12147691
theorem B10797947 : Blo 2131435 10797947 := bstep (se 1 (by rfl) ⟨8098460, by rfl⟩ : syracuseStep 10797947 = 16196921) B16196921
theorem B7198631 : Blo 2131435 7198631 := bstep (se 1 (by rfl) ⟨5398973, by rfl⟩ : syracuseStep 7198631 = 10797947) B10797947
theorem B4799087 : Blo 2131435 4799087 := bstep (se 1 (by rfl) ⟨3599315, by rfl⟩ : syracuseStep 4799087 = 7198631) B7198631
theorem B3199391 : Blo 2131435 3199391 := bstep (se 1 (by rfl) ⟨2399543, by rfl⟩ : syracuseStep 3199391 = 4799087) B4799087
theorem B2132927 : Blo 2131435 2132927 := bstep (se 1 (by rfl) ⟨1599695, by rfl⟩ : syracuseStep 2132927 = 3199391) B3199391
theorem B3199397 : Blo 2131435 3199397 := bbase (se 4 (by rfl) ⟨299943, by rfl⟩ : syracuseStep 3199397 = 599887) (by norm_num)
theorem B2132931 : Blo 2131435 2132931 := bstep (se 1 (by rfl) ⟨1599698, by rfl⟩ : syracuseStep 2132931 = 3199397) B3199397
theorem B2699497 : Blo 2131435 2699497 := bbase (se 2 (by rfl) ⟨1012311, by rfl⟩ : syracuseStep 2699497 = 2024623) (by norm_num)
theorem B3599329 : Blo 2131435 3599329 := bstep (se 2 (by rfl) ⟨1349748, by rfl⟩ : syracuseStep 3599329 = 2699497) B2699497
theorem B4799105 : Blo 2131435 4799105 := bstep (se 2 (by rfl) ⟨1799664, by rfl⟩ : syracuseStep 4799105 = 3599329) B3599329
theorem B3199403 : Blo 2131435 3199403 := bstep (se 1 (by rfl) ⟨2399552, by rfl⟩ : syracuseStep 3199403 = 4799105) B4799105
theorem B2132935 : Blo 2131435 2132935 := bstep (se 1 (by rfl) ⟨1599701, by rfl⟩ : syracuseStep 2132935 = 3199403) B3199403
theorem B2399557 : Blo 2131435 2399557 := bbase (se 4 (by rfl) ⟨224958, by rfl⟩ : syracuseStep 2399557 = 449917) (by norm_num)
theorem B3199409 : Blo 2131435 3199409 := bstep (se 2 (by rfl) ⟨1199778, by rfl⟩ : syracuseStep 3199409 = 2399557) B2399557
theorem B2132939 : Blo 2131435 2132939 := bstep (se 1 (by rfl) ⟨1599704, by rfl⟩ : syracuseStep 2132939 = 3199409) B3199409
theorem B4049261 : Blo 2131435 4049261 := bbase (se 3 (by rfl) ⟨759236, by rfl⟩ : syracuseStep 4049261 = 1518473) (by norm_num)
theorem B2699507 : Blo 2131435 2699507 := bstep (se 1 (by rfl) ⟨2024630, by rfl⟩ : syracuseStep 2699507 = 4049261) B4049261
theorem B7198685 : Blo 2131435 7198685 := bstep (se 3 (by rfl) ⟨1349753, by rfl⟩ : syracuseStep 7198685 = 2699507) B2699507
theorem B4799123 : Blo 2131435 4799123 := bstep (se 1 (by rfl) ⟨3599342, by rfl⟩ : syracuseStep 4799123 = 7198685) B7198685
theorem B3199415 : Blo 2131435 3199415 := bstep (se 1 (by rfl) ⟨2399561, by rfl⟩ : syracuseStep 3199415 = 4799123) B4799123
theorem B2132943 : Blo 2131435 2132943 := bstep (se 1 (by rfl) ⟨1599707, by rfl⟩ : syracuseStep 2132943 = 3199415) B3199415
theorem B3199421 : Blo 2131435 3199421 := bbase (se 3 (by rfl) ⟨599891, by rfl⟩ : syracuseStep 3199421 = 1199783) (by norm_num)
theorem B2132947 : Blo 2131435 2132947 := bstep (se 1 (by rfl) ⟨1599710, by rfl⟩ : syracuseStep 2132947 = 3199421) B3199421
theorem B4799141 : Blo 2131435 4799141 := bbase (se 4 (by rfl) ⟨449919, by rfl⟩ : syracuseStep 4799141 = 899839) (by norm_num)
theorem B3199427 : Blo 2131435 3199427 := bstep (se 1 (by rfl) ⟨2399570, by rfl⟩ : syracuseStep 3199427 = 4799141) B4799141
theorem B2132951 : Blo 2131435 2132951 := bstep (se 1 (by rfl) ⟨1599713, by rfl⟩ : syracuseStep 2132951 = 3199427) B3199427
theorem B5399045 : Blo 2131435 5399045 := bbase (se 4 (by rfl) ⟨506160, by rfl⟩ : syracuseStep 5399045 = 1012321) (by norm_num)
theorem B3599363 : Blo 2131435 3599363 := bstep (se 1 (by rfl) ⟨2699522, by rfl⟩ : syracuseStep 3599363 = 5399045) B5399045
theorem B2399575 : Blo 2131435 2399575 := bstep (se 1 (by rfl) ⟨1799681, by rfl⟩ : syracuseStep 2399575 = 3599363) B3599363
theorem B3199433 : Blo 2131435 3199433 := bstep (se 2 (by rfl) ⟨1199787, by rfl⟩ : syracuseStep 3199433 = 2399575) B2399575
theorem B2132955 : Blo 2131435 2132955 := bstep (se 1 (by rfl) ⟨1599716, by rfl⟩ : syracuseStep 2132955 = 3199433) B3199433
theorem B4555453 : Blo 2131435 4555453 := bbase (se 3 (by rfl) ⟨854147, by rfl⟩ : syracuseStep 4555453 = 1708295) (by norm_num)
theorem B6073937 : Blo 2131435 6073937 := bstep (se 2 (by rfl) ⟨2277726, by rfl⟩ : syracuseStep 6073937 = 4555453) B4555453
theorem B4049291 : Blo 2131435 4049291 := bstep (se 1 (by rfl) ⟨3036968, by rfl⟩ : syracuseStep 4049291 = 6073937) B6073937
theorem B10798109 : Blo 2131435 10798109 := bstep (se 3 (by rfl) ⟨2024645, by rfl⟩ : syracuseStep 10798109 = 4049291) B4049291
theorem B7198739 : Blo 2131435 7198739 := bstep (se 1 (by rfl) ⟨5399054, by rfl⟩ : syracuseStep 7198739 = 10798109) B10798109
theorem B4799159 : Blo 2131435 4799159 := bstep (se 1 (by rfl) ⟨3599369, by rfl⟩ : syracuseStep 4799159 = 7198739) B7198739
theorem B3199439 : Blo 2131435 3199439 := bstep (se 1 (by rfl) ⟨2399579, by rfl⟩ : syracuseStep 3199439 = 4799159) B4799159
theorem B2132959 : Blo 2131435 2132959 := bstep (se 1 (by rfl) ⟨1599719, by rfl⟩ : syracuseStep 2132959 = 3199439) B3199439
theorem B3199445 : Blo 2131435 3199445 := bbase (se 7 (by rfl) ⟨37493, by rfl⟩ : syracuseStep 3199445 = 74987) (by norm_num)
theorem B2132963 : Blo 2131435 2132963 := bstep (se 1 (by rfl) ⟨1599722, by rfl⟩ : syracuseStep 2132963 = 3199445) B3199445
theorem B8098613 : Blo 2131435 8098613 := bbase (se 5 (by rfl) ⟨379622, by rfl⟩ : syracuseStep 8098613 = 759245) (by norm_num)
theorem B5399075 : Blo 2131435 5399075 := bstep (se 1 (by rfl) ⟨4049306, by rfl⟩ : syracuseStep 5399075 = 8098613) B8098613
theorem B3599383 : Blo 2131435 3599383 := bstep (se 1 (by rfl) ⟨2699537, by rfl⟩ : syracuseStep 3599383 = 5399075) B5399075
theorem B4799177 : Blo 2131435 4799177 := bstep (se 2 (by rfl) ⟨1799691, by rfl⟩ : syracuseStep 4799177 = 3599383) B3599383
theorem B3199451 : Blo 2131435 3199451 := bstep (se 1 (by rfl) ⟨2399588, by rfl⟩ : syracuseStep 3199451 = 4799177) B4799177
theorem B2132967 : Blo 2131435 2132967 := bstep (se 1 (by rfl) ⟨1599725, by rfl⟩ : syracuseStep 2132967 = 3199451) B3199451
theorem B2399593 : Blo 2131435 2399593 := bbase (se 2 (by rfl) ⟨899847, by rfl⟩ : syracuseStep 2399593 = 1799695) (by norm_num)
theorem B3199457 : Blo 2131435 3199457 := bstep (se 2 (by rfl) ⟨1199796, by rfl⟩ : syracuseStep 3199457 = 2399593) B2399593
theorem B2132971 : Blo 2131435 2132971 := bstep (se 1 (by rfl) ⟨1599728, by rfl⟩ : syracuseStep 2132971 = 3199457) B3199457
theorem B8648309 : Blo 2131435 8648309 := bbase (se 5 (by rfl) ⟨405389, by rfl⟩ : syracuseStep 8648309 = 810779) (by norm_num)
theorem B23062157 : Blo 2131435 23062157 := bstep (se 3 (by rfl) ⟨4324154, by rfl⟩ : syracuseStep 23062157 = 8648309) B8648309
theorem B15374771 : Blo 2131435 15374771 := bstep (se 1 (by rfl) ⟨11531078, by rfl⟩ : syracuseStep 15374771 = 23062157) B23062157
theorem B10249847 : Blo 2131435 10249847 := bstep (se 1 (by rfl) ⟨7687385, by rfl⟩ : syracuseStep 10249847 = 15374771) B15374771
theorem B6833231 : Blo 2131435 6833231 := bstep (se 1 (by rfl) ⟨5124923, by rfl⟩ : syracuseStep 6833231 = 10249847) B10249847
theorem B4555487 : Blo 2131435 4555487 := bstep (se 1 (by rfl) ⟨3416615, by rfl⟩ : syracuseStep 4555487 = 6833231) B6833231
theorem B12147965 : Blo 2131435 12147965 := bstep (se 3 (by rfl) ⟨2277743, by rfl⟩ : syracuseStep 12147965 = 4555487) B4555487
theorem B8098643 : Blo 2131435 8098643 := bstep (se 1 (by rfl) ⟨6073982, by rfl⟩ : syracuseStep 8098643 = 12147965) B12147965
theorem B5399095 : Blo 2131435 5399095 := bstep (se 1 (by rfl) ⟨4049321, by rfl⟩ : syracuseStep 5399095 = 8098643) B8098643
theorem B7198793 : Blo 2131435 7198793 := bstep (se 2 (by rfl) ⟨2699547, by rfl⟩ : syracuseStep 7198793 = 5399095) B5399095
theorem B4799195 : Blo 2131435 4799195 := bstep (se 1 (by rfl) ⟨3599396, by rfl⟩ : syracuseStep 4799195 = 7198793) B7198793
theorem B3199463 : Blo 2131435 3199463 := bstep (se 1 (by rfl) ⟨2399597, by rfl⟩ : syracuseStep 3199463 = 4799195) B4799195
theorem B2132975 : Blo 2131435 2132975 := bstep (se 1 (by rfl) ⟨1599731, by rfl⟩ : syracuseStep 2132975 = 3199463) B3199463
theorem B3199469 : Blo 2131435 3199469 := bbase (se 3 (by rfl) ⟨599900, by rfl⟩ : syracuseStep 3199469 = 1199801) (by norm_num)
theorem B2132979 : Blo 2131435 2132979 := bstep (se 1 (by rfl) ⟨1599734, by rfl⟩ : syracuseStep 2132979 = 3199469) B3199469
theorem B4799213 : Blo 2131435 4799213 := bbase (se 3 (by rfl) ⟨899852, by rfl⟩ : syracuseStep 4799213 = 1799705) (by norm_num)
theorem B3199475 : Blo 2131435 3199475 := bstep (se 1 (by rfl) ⟨2399606, by rfl⟩ : syracuseStep 3199475 = 4799213) B4799213
theorem B2132983 : Blo 2131435 2132983 := bstep (se 1 (by rfl) ⟨1599737, by rfl⟩ : syracuseStep 2132983 = 3199475) B3199475
theorem B2277757 : Blo 2131435 2277757 := bbase (se 3 (by rfl) ⟨427079, by rfl⟩ : syracuseStep 2277757 = 854159) (by norm_num)
theorem B3037009 : Blo 2131435 3037009 := bstep (se 2 (by rfl) ⟨1138878, by rfl⟩ : syracuseStep 3037009 = 2277757) B2277757
theorem B4049345 : Blo 2131435 4049345 := bstep (se 2 (by rfl) ⟨1518504, by rfl⟩ : syracuseStep 4049345 = 3037009) B3037009
theorem B2699563 : Blo 2131435 2699563 := bstep (se 1 (by rfl) ⟨2024672, by rfl⟩ : syracuseStep 2699563 = 4049345) B4049345
theorem B3599417 : Blo 2131435 3599417 := bstep (se 2 (by rfl) ⟨1349781, by rfl⟩ : syracuseStep 3599417 = 2699563) B2699563
theorem B2399611 : Blo 2131435 2399611 := bstep (se 1 (by rfl) ⟨1799708, by rfl⟩ : syracuseStep 2399611 = 3599417) B3599417
theorem B3199481 : Blo 2131435 3199481 := bstep (se 2 (by rfl) ⟨1199805, by rfl⟩ : syracuseStep 3199481 = 2399611) B2399611
theorem B2132987 : Blo 2131435 2132987 := bstep (se 1 (by rfl) ⟨1599740, by rfl⟩ : syracuseStep 2132987 = 3199481) B3199481
theorem B2162093 : Blo 2131435 2162093 := bbase (se 3 (by rfl) ⟨405392, by rfl⟩ : syracuseStep 2162093 = 810785) (by norm_num)
theorem B23062325 : Blo 2131435 23062325 := bstep (se 5 (by rfl) ⟨1081046, by rfl⟩ : syracuseStep 23062325 = 2162093) B2162093
theorem B61499533 : Blo 2131435 61499533 := bstep (se 3 (by rfl) ⟨11531162, by rfl⟩ : syracuseStep 61499533 = 23062325) B23062325
theorem B81999377 : Blo 2131435 81999377 := bstep (se 2 (by rfl) ⟨30749766, by rfl⟩ : syracuseStep 81999377 = 61499533) B61499533
theorem B54666251 : Blo 2131435 54666251 := bstep (se 1 (by rfl) ⟨40999688, by rfl⟩ : syracuseStep 54666251 = 81999377) B81999377
theorem B36444167 : Blo 2131435 36444167 := bstep (se 1 (by rfl) ⟨27333125, by rfl⟩ : syracuseStep 36444167 = 54666251) B54666251
theorem B24296111 : Blo 2131435 24296111 := bstep (se 1 (by rfl) ⟨18222083, by rfl⟩ : syracuseStep 24296111 = 36444167) B36444167
theorem B16197407 : Blo 2131435 16197407 := bstep (se 1 (by rfl) ⟨12148055, by rfl⟩ : syracuseStep 16197407 = 24296111) B24296111
theorem B10798271 : Blo 2131435 10798271 := bstep (se 1 (by rfl) ⟨8098703, by rfl⟩ : syracuseStep 10798271 = 16197407) B16197407
theorem B7198847 : Blo 2131435 7198847 := bstep (se 1 (by rfl) ⟨5399135, by rfl⟩ : syracuseStep 7198847 = 10798271) B10798271
theorem B4799231 : Blo 2131435 4799231 := bstep (se 1 (by rfl) ⟨3599423, by rfl⟩ : syracuseStep 4799231 = 7198847) B7198847
theorem B3199487 : Blo 2131435 3199487 := bstep (se 1 (by rfl) ⟨2399615, by rfl⟩ : syracuseStep 3199487 = 4799231) B4799231
theorem B2132991 : Blo 2131435 2132991 := bstep (se 1 (by rfl) ⟨1599743, by rfl⟩ : syracuseStep 2132991 = 3199487) B3199487
theorem B3199493 : Blo 2131435 3199493 := bbase (se 4 (by rfl) ⟨299952, by rfl⟩ : syracuseStep 3199493 = 599905) (by norm_num)
theorem B2132995 : Blo 2131435 2132995 := bstep (se 1 (by rfl) ⟨1599746, by rfl⟩ : syracuseStep 2132995 = 3199493) B3199493
theorem B3599437 : Blo 2131435 3599437 := bbase (se 3 (by rfl) ⟨674894, by rfl⟩ : syracuseStep 3599437 = 1349789) (by norm_num)
theorem B4799249 : Blo 2131435 4799249 := bstep (se 2 (by rfl) ⟨1799718, by rfl⟩ : syracuseStep 4799249 = 3599437) B3599437
theorem B3199499 : Blo 2131435 3199499 := bstep (se 1 (by rfl) ⟨2399624, by rfl⟩ : syracuseStep 3199499 = 4799249) B4799249
theorem B2132999 : Blo 2131435 2132999 := bstep (se 1 (by rfl) ⟨1599749, by rfl⟩ : syracuseStep 2132999 = 3199499) B3199499
theorem B2399629 : Blo 2131435 2399629 := bbase (se 3 (by rfl) ⟨449930, by rfl⟩ : syracuseStep 2399629 = 899861) (by norm_num)
theorem B3199505 : Blo 2131435 3199505 := bstep (se 2 (by rfl) ⟨1199814, by rfl⟩ : syracuseStep 3199505 = 2399629) B2399629
theorem B2133003 : Blo 2131435 2133003 := bstep (se 1 (by rfl) ⟨1599752, by rfl⟩ : syracuseStep 2133003 = 3199505) B3199505
theorem B7198901 : Blo 2131435 7198901 := bbase (se 5 (by rfl) ⟨337448, by rfl⟩ : syracuseStep 7198901 = 674897) (by norm_num)
theorem B4799267 : Blo 2131435 4799267 := bstep (se 1 (by rfl) ⟨3599450, by rfl⟩ : syracuseStep 4799267 = 7198901) B7198901
theorem B3199511 : Blo 2131435 3199511 := bstep (se 1 (by rfl) ⟨2399633, by rfl⟩ : syracuseStep 3199511 = 4799267) B4799267
theorem B2133007 : Blo 2131435 2133007 := bstep (se 1 (by rfl) ⟨1599755, by rfl⟩ : syracuseStep 2133007 = 3199511) B3199511
theorem B3199517 : Blo 2131435 3199517 := bbase (se 3 (by rfl) ⟨599909, by rfl⟩ : syracuseStep 3199517 = 1199819) (by norm_num)
theorem B2133011 : Blo 2131435 2133011 := bstep (se 1 (by rfl) ⟨1599758, by rfl⟩ : syracuseStep 2133011 = 3199517) B3199517
theorem B4799285 : Blo 2131435 4799285 := bbase (se 5 (by rfl) ⟨224966, by rfl⟩ : syracuseStep 4799285 = 449933) (by norm_num)
theorem B3199523 : Blo 2131435 3199523 := bstep (se 1 (by rfl) ⟨2399642, by rfl⟩ : syracuseStep 3199523 = 4799285) B4799285
theorem B2133015 : Blo 2131435 2133015 := bstep (se 1 (by rfl) ⟨1599761, by rfl⟩ : syracuseStep 2133015 = 3199523) B3199523
theorem B11531317 : Blo 2131435 11531317 := bbase (se 5 (by rfl) ⟨540530, by rfl⟩ : syracuseStep 11531317 = 1081061) (by norm_num)
theorem B15375089 : Blo 2131435 15375089 := bstep (se 2 (by rfl) ⟨5765658, by rfl⟩ : syracuseStep 15375089 = 11531317) B11531317
theorem B10250059 : Blo 2131435 10250059 := bstep (se 1 (by rfl) ⟨7687544, by rfl⟩ : syracuseStep 10250059 = 15375089) B15375089
theorem B13666745 : Blo 2131435 13666745 := bstep (se 2 (by rfl) ⟨5125029, by rfl⟩ : syracuseStep 13666745 = 10250059) B10250059
theorem B9111163 : Blo 2131435 9111163 := bstep (se 1 (by rfl) ⟨6833372, by rfl⟩ : syracuseStep 9111163 = 13666745) B13666745
theorem B12148217 : Blo 2131435 12148217 := bstep (se 2 (by rfl) ⟨4555581, by rfl⟩ : syracuseStep 12148217 = 9111163) B9111163
theorem B8098811 : Blo 2131435 8098811 := bstep (se 1 (by rfl) ⟨6074108, by rfl⟩ : syracuseStep 8098811 = 12148217) B12148217
theorem B5399207 : Blo 2131435 5399207 := bstep (se 1 (by rfl) ⟨4049405, by rfl⟩ : syracuseStep 5399207 = 8098811) B8098811
theorem B3599471 : Blo 2131435 3599471 := bstep (se 1 (by rfl) ⟨2699603, by rfl⟩ : syracuseStep 3599471 = 5399207) B5399207
theorem B2399647 : Blo 2131435 2399647 := bstep (se 1 (by rfl) ⟨1799735, by rfl⟩ : syracuseStep 2399647 = 3599471) B3599471
theorem B3199529 : Blo 2131435 3199529 := bstep (se 2 (by rfl) ⟨1199823, by rfl⟩ : syracuseStep 3199529 = 2399647) B2399647
theorem B2133019 : Blo 2131435 2133019 := bstep (se 1 (by rfl) ⟨1599764, by rfl⟩ : syracuseStep 2133019 = 3199529) B3199529
theorem B5765669 : Blo 2131435 5765669 := bbase (se 4 (by rfl) ⟨540531, by rfl⟩ : syracuseStep 5765669 = 1081063) (by norm_num)
theorem B3843779 : Blo 2131435 3843779 := bstep (se 1 (by rfl) ⟨2882834, by rfl⟩ : syracuseStep 3843779 = 5765669) B5765669
theorem B10250077 : Blo 2131435 10250077 := bstep (se 3 (by rfl) ⟨1921889, by rfl⟩ : syracuseStep 10250077 = 3843779) B3843779
theorem B13666769 : Blo 2131435 13666769 := bstep (se 2 (by rfl) ⟨5125038, by rfl⟩ : syracuseStep 13666769 = 10250077) B10250077
theorem B9111179 : Blo 2131435 9111179 := bstep (se 1 (by rfl) ⟨6833384, by rfl⟩ : syracuseStep 9111179 = 13666769) B13666769
theorem B6074119 : Blo 2131435 6074119 := bstep (se 1 (by rfl) ⟨4555589, by rfl⟩ : syracuseStep 6074119 = 9111179) B9111179
theorem B8098825 : Blo 2131435 8098825 := bstep (se 2 (by rfl) ⟨3037059, by rfl⟩ : syracuseStep 8098825 = 6074119) B6074119
theorem B10798433 : Blo 2131435 10798433 := bstep (se 2 (by rfl) ⟨4049412, by rfl⟩ : syracuseStep 10798433 = 8098825) B8098825
theorem B7198955 : Blo 2131435 7198955 := bstep (se 1 (by rfl) ⟨5399216, by rfl⟩ : syracuseStep 7198955 = 10798433) B10798433
theorem B4799303 : Blo 2131435 4799303 := bstep (se 1 (by rfl) ⟨3599477, by rfl⟩ : syracuseStep 4799303 = 7198955) B7198955
theorem B3199535 : Blo 2131435 3199535 := bstep (se 1 (by rfl) ⟨2399651, by rfl⟩ : syracuseStep 3199535 = 4799303) B4799303
theorem B2133023 : Blo 2131435 2133023 := bstep (se 1 (by rfl) ⟨1599767, by rfl⟩ : syracuseStep 2133023 = 3199535) B3199535
theorem B3199541 : Blo 2131435 3199541 := bbase (se 5 (by rfl) ⟨149978, by rfl⟩ : syracuseStep 3199541 = 299957) (by norm_num)
theorem B2133027 : Blo 2131435 2133027 := bstep (se 1 (by rfl) ⟨1599770, by rfl⟩ : syracuseStep 2133027 = 3199541) B3199541
theorem B5399237 : Blo 2131435 5399237 := bbase (se 4 (by rfl) ⟨506178, by rfl⟩ : syracuseStep 5399237 = 1012357) (by norm_num)
theorem B3599491 : Blo 2131435 3599491 := bstep (se 1 (by rfl) ⟨2699618, by rfl⟩ : syracuseStep 3599491 = 5399237) B5399237
theorem B4799321 : Blo 2131435 4799321 := bstep (se 2 (by rfl) ⟨1799745, by rfl⟩ : syracuseStep 4799321 = 3599491) B3599491
theorem B3199547 : Blo 2131435 3199547 := bstep (se 1 (by rfl) ⟨2399660, by rfl⟩ : syracuseStep 3199547 = 4799321) B4799321
theorem B2133031 : Blo 2131435 2133031 := bstep (se 1 (by rfl) ⟨1599773, by rfl⟩ : syracuseStep 2133031 = 3199547) B3199547
theorem B2399665 : Blo 2131435 2399665 := bbase (se 2 (by rfl) ⟨899874, by rfl⟩ : syracuseStep 2399665 = 1799749) (by norm_num)
theorem B3199553 : Blo 2131435 3199553 := bstep (se 2 (by rfl) ⟨1199832, by rfl⟩ : syracuseStep 3199553 = 2399665) B2399665
theorem B2133035 : Blo 2131435 2133035 := bstep (se 1 (by rfl) ⟨1599776, by rfl⟩ : syracuseStep 2133035 = 3199553) B3199553
theorem B6074165 : Blo 2131435 6074165 := bbase (se 5 (by rfl) ⟨284726, by rfl⟩ : syracuseStep 6074165 = 569453) (by norm_num)
theorem B4049443 : Blo 2131435 4049443 := bstep (se 1 (by rfl) ⟨3037082, by rfl⟩ : syracuseStep 4049443 = 6074165) B6074165
theorem B5399257 : Blo 2131435 5399257 := bstep (se 2 (by rfl) ⟨2024721, by rfl⟩ : syracuseStep 5399257 = 4049443) B4049443
theorem B7199009 : Blo 2131435 7199009 := bstep (se 2 (by rfl) ⟨2699628, by rfl⟩ : syracuseStep 7199009 = 5399257) B5399257
theorem B4799339 : Blo 2131435 4799339 := bstep (se 1 (by rfl) ⟨3599504, by rfl⟩ : syracuseStep 4799339 = 7199009) B7199009
theorem B3199559 : Blo 2131435 3199559 := bstep (se 1 (by rfl) ⟨2399669, by rfl⟩ : syracuseStep 3199559 = 4799339) B4799339
theorem B2133039 : Blo 2131435 2133039 := bstep (se 1 (by rfl) ⟨1599779, by rfl⟩ : syracuseStep 2133039 = 3199559) B3199559
theorem B3199565 : Blo 2131435 3199565 := bbase (se 3 (by rfl) ⟨599918, by rfl⟩ : syracuseStep 3199565 = 1199837) (by norm_num)
theorem B2133043 : Blo 2131435 2133043 := bstep (se 1 (by rfl) ⟨1599782, by rfl⟩ : syracuseStep 2133043 = 3199565) B3199565
theorem B4799357 : Blo 2131435 4799357 := bbase (se 3 (by rfl) ⟨899879, by rfl⟩ : syracuseStep 4799357 = 1799759) (by norm_num)
theorem B3199571 : Blo 2131435 3199571 := bstep (se 1 (by rfl) ⟨2399678, by rfl⟩ : syracuseStep 3199571 = 4799357) B4799357
theorem B2133047 : Blo 2131435 2133047 := bstep (se 1 (by rfl) ⟨1599785, by rfl⟩ : syracuseStep 2133047 = 3199571) B3199571
theorem B3599525 : Blo 2131435 3599525 := bbase (se 4 (by rfl) ⟨337455, by rfl⟩ : syracuseStep 3599525 = 674911) (by norm_num)
theorem B2399683 : Blo 2131435 2399683 := bstep (se 1 (by rfl) ⟨1799762, by rfl⟩ : syracuseStep 2399683 = 3599525) B3599525
theorem B3199577 : Blo 2131435 3199577 := bstep (se 2 (by rfl) ⟨1199841, by rfl⟩ : syracuseStep 3199577 = 2399683) B2399683
theorem B2133051 : Blo 2131435 2133051 := bstep (se 1 (by rfl) ⟨1599788, by rfl⟩ : syracuseStep 2133051 = 3199577) B3199577
theorem B2277829 : Blo 2131435 2277829 := bbase (se 4 (by rfl) ⟨213546, by rfl⟩ : syracuseStep 2277829 = 427093) (by norm_num)
theorem B3037105 : Blo 2131435 3037105 := bstep (se 2 (by rfl) ⟨1138914, by rfl⟩ : syracuseStep 3037105 = 2277829) B2277829
theorem B16197893 : Blo 2131435 16197893 := bstep (se 4 (by rfl) ⟨1518552, by rfl⟩ : syracuseStep 16197893 = 3037105) B3037105
theorem B10798595 : Blo 2131435 10798595 := bstep (se 1 (by rfl) ⟨8098946, by rfl⟩ : syracuseStep 10798595 = 16197893) B16197893
theorem B7199063 : Blo 2131435 7199063 := bstep (se 1 (by rfl) ⟨5399297, by rfl⟩ : syracuseStep 7199063 = 10798595) B10798595
theorem B4799375 : Blo 2131435 4799375 := bstep (se 1 (by rfl) ⟨3599531, by rfl⟩ : syracuseStep 4799375 = 7199063) B7199063
theorem B3199583 : Blo 2131435 3199583 := bstep (se 1 (by rfl) ⟨2399687, by rfl⟩ : syracuseStep 3199583 = 4799375) B4799375
theorem B2133055 : Blo 2131435 2133055 := bstep (se 1 (by rfl) ⟨1599791, by rfl⟩ : syracuseStep 2133055 = 3199583) B3199583
theorem B3199589 : Blo 2131435 3199589 := bbase (se 4 (by rfl) ⟨299961, by rfl⟩ : syracuseStep 3199589 = 599923) (by norm_num)
theorem B2133059 : Blo 2131435 2133059 := bstep (se 1 (by rfl) ⟨1599794, by rfl⟩ : syracuseStep 2133059 = 3199589) B3199589
theorem B3037117 : Blo 2131435 3037117 := bbase (se 3 (by rfl) ⟨569459, by rfl⟩ : syracuseStep 3037117 = 1138919) (by norm_num)
theorem B4049489 : Blo 2131435 4049489 := bstep (se 2 (by rfl) ⟨1518558, by rfl⟩ : syracuseStep 4049489 = 3037117) B3037117
theorem B2699659 : Blo 2131435 2699659 := bstep (se 1 (by rfl) ⟨2024744, by rfl⟩ : syracuseStep 2699659 = 4049489) B4049489
theorem B3599545 : Blo 2131435 3599545 := bstep (se 2 (by rfl) ⟨1349829, by rfl⟩ : syracuseStep 3599545 = 2699659) B2699659
theorem B4799393 : Blo 2131435 4799393 := bstep (se 2 (by rfl) ⟨1799772, by rfl⟩ : syracuseStep 4799393 = 3599545) B3599545
theorem B3199595 : Blo 2131435 3199595 := bstep (se 1 (by rfl) ⟨2399696, by rfl⟩ : syracuseStep 3199595 = 4799393) B4799393
theorem B2133063 : Blo 2131435 2133063 := bstep (se 1 (by rfl) ⟨1599797, by rfl⟩ : syracuseStep 2133063 = 3199595) B3199595
theorem B2399701 : Blo 2131435 2399701 := bbase (se 7 (by rfl) ⟨28121, by rfl⟩ : syracuseStep 2399701 = 56243) (by norm_num)
theorem B3199601 : Blo 2131435 3199601 := bstep (se 2 (by rfl) ⟨1199850, by rfl⟩ : syracuseStep 3199601 = 2399701) B2399701
theorem B2133067 : Blo 2131435 2133067 := bstep (se 1 (by rfl) ⟨1599800, by rfl⟩ : syracuseStep 2133067 = 3199601) B3199601
theorem B2699669 : Blo 2131435 2699669 := bbase (se 6 (by rfl) ⟨63273, by rfl⟩ : syracuseStep 2699669 = 126547) (by norm_num)
theorem B7199117 : Blo 2131435 7199117 := bstep (se 3 (by rfl) ⟨1349834, by rfl⟩ : syracuseStep 7199117 = 2699669) B2699669
theorem B4799411 : Blo 2131435 4799411 := bstep (se 1 (by rfl) ⟨3599558, by rfl⟩ : syracuseStep 4799411 = 7199117) B7199117
theorem B3199607 : Blo 2131435 3199607 := bstep (se 1 (by rfl) ⟨2399705, by rfl⟩ : syracuseStep 3199607 = 4799411) B4799411
theorem B2133071 : Blo 2131435 2133071 := bstep (se 1 (by rfl) ⟨1599803, by rfl⟩ : syracuseStep 2133071 = 3199607) B3199607
theorem B3199613 : Blo 2131435 3199613 := bbase (se 3 (by rfl) ⟨599927, by rfl⟩ : syracuseStep 3199613 = 1199855) (by norm_num)
theorem B2133075 : Blo 2131435 2133075 := bstep (se 1 (by rfl) ⟨1599806, by rfl⟩ : syracuseStep 2133075 = 3199613) B3199613
theorem B4799429 : Blo 2131435 4799429 := bbase (se 4 (by rfl) ⟨449946, by rfl⟩ : syracuseStep 4799429 = 899893) (by norm_num)
theorem B3199619 : Blo 2131435 3199619 := bstep (se 1 (by rfl) ⟨2399714, by rfl⟩ : syracuseStep 3199619 = 4799429) B4799429
theorem B2133079 : Blo 2131435 2133079 := bstep (se 1 (by rfl) ⟨1599809, by rfl⟩ : syracuseStep 2133079 = 3199619) B3199619
theorem B3416789 : Blo 2131435 3416789 := bbase (se 7 (by rfl) ⟨40040, by rfl⟩ : syracuseStep 3416789 = 80081) (by norm_num)
theorem B9111437 : Blo 2131435 9111437 := bstep (se 3 (by rfl) ⟨1708394, by rfl⟩ : syracuseStep 9111437 = 3416789) B3416789
theorem B6074291 : Blo 2131435 6074291 := bstep (se 1 (by rfl) ⟨4555718, by rfl⟩ : syracuseStep 6074291 = 9111437) B9111437
theorem B4049527 : Blo 2131435 4049527 := bstep (se 1 (by rfl) ⟨3037145, by rfl⟩ : syracuseStep 4049527 = 6074291) B6074291
theorem B5399369 : Blo 2131435 5399369 := bstep (se 2 (by rfl) ⟨2024763, by rfl⟩ : syracuseStep 5399369 = 4049527) B4049527
theorem B3599579 : Blo 2131435 3599579 := bstep (se 1 (by rfl) ⟨2699684, by rfl⟩ : syracuseStep 3599579 = 5399369) B5399369
theorem B2399719 : Blo 2131435 2399719 := bstep (se 1 (by rfl) ⟨1799789, by rfl⟩ : syracuseStep 2399719 = 3599579) B3599579
theorem B3199625 : Blo 2131435 3199625 := bstep (se 2 (by rfl) ⟨1199859, by rfl⟩ : syracuseStep 3199625 = 2399719) B2399719
theorem B2133083 : Blo 2131435 2133083 := bstep (se 1 (by rfl) ⟨1599812, by rfl⟩ : syracuseStep 2133083 = 3199625) B3199625
theorem B10798757 : Blo 2131435 10798757 := bbase (se 4 (by rfl) ⟨1012383, by rfl⟩ : syracuseStep 10798757 = 2024767) (by norm_num)
theorem B7199171 : Blo 2131435 7199171 := bstep (se 1 (by rfl) ⟨5399378, by rfl⟩ : syracuseStep 7199171 = 10798757) B10798757
theorem B4799447 : Blo 2131435 4799447 := bstep (se 1 (by rfl) ⟨3599585, by rfl⟩ : syracuseStep 4799447 = 7199171) B7199171
theorem B3199631 : Blo 2131435 3199631 := bstep (se 1 (by rfl) ⟨2399723, by rfl⟩ : syracuseStep 3199631 = 4799447) B4799447
theorem B2133087 : Blo 2131435 2133087 := bstep (se 1 (by rfl) ⟨1599815, by rfl⟩ : syracuseStep 2133087 = 3199631) B3199631
theorem B3199637 : Blo 2131435 3199637 := bbase (se 6 (by rfl) ⟨74991, by rfl⟩ : syracuseStep 3199637 = 149983) (by norm_num)
theorem B2133091 : Blo 2131435 2133091 := bstep (se 1 (by rfl) ⟨1599818, by rfl⟩ : syracuseStep 2133091 = 3199637) B3199637
theorem B2736533 : Blo 2131435 2736533 := bbase (se 6 (by rfl) ⟨64137, by rfl⟩ : syracuseStep 2736533 = 128275) (by norm_num)
theorem B7297421 : Blo 2131435 7297421 := bstep (se 3 (by rfl) ⟨1368266, by rfl⟩ : syracuseStep 7297421 = 2736533) B2736533
theorem B77839157 : Blo 2131435 77839157 := bstep (se 5 (by rfl) ⟨3648710, by rfl⟩ : syracuseStep 77839157 = 7297421) B7297421
theorem B51892771 : Blo 2131435 51892771 := bstep (se 1 (by rfl) ⟨38919578, by rfl⟩ : syracuseStep 51892771 = 77839157) B77839157
theorem B69190361 : Blo 2131435 69190361 := bstep (se 2 (by rfl) ⟨25946385, by rfl⟩ : syracuseStep 69190361 = 51892771) B51892771
theorem B46126907 : Blo 2131435 46126907 := bstep (se 1 (by rfl) ⟨34595180, by rfl⟩ : syracuseStep 46126907 = 69190361) B69190361
theorem B30751271 : Blo 2131435 30751271 := bstep (se 1 (by rfl) ⟨23063453, by rfl⟩ : syracuseStep 30751271 = 46126907) B46126907
theorem B20500847 : Blo 2131435 20500847 := bstep (se 1 (by rfl) ⟨15375635, by rfl⟩ : syracuseStep 20500847 = 30751271) B30751271
theorem B13667231 : Blo 2131435 13667231 := bstep (se 1 (by rfl) ⟨10250423, by rfl⟩ : syracuseStep 13667231 = 20500847) B20500847
theorem B9111487 : Blo 2131435 9111487 := bstep (se 1 (by rfl) ⟨6833615, by rfl⟩ : syracuseStep 9111487 = 13667231) B13667231
theorem B12148649 : Blo 2131435 12148649 := bstep (se 2 (by rfl) ⟨4555743, by rfl⟩ : syracuseStep 12148649 = 9111487) B9111487
theorem B8099099 : Blo 2131435 8099099 := bstep (se 1 (by rfl) ⟨6074324, by rfl⟩ : syracuseStep 8099099 = 12148649) B12148649
theorem B5399399 : Blo 2131435 5399399 := bstep (se 1 (by rfl) ⟨4049549, by rfl⟩ : syracuseStep 5399399 = 8099099) B8099099
theorem B3599599 : Blo 2131435 3599599 := bstep (se 1 (by rfl) ⟨2699699, by rfl⟩ : syracuseStep 3599599 = 5399399) B5399399
theorem B4799465 : Blo 2131435 4799465 := bstep (se 2 (by rfl) ⟨1799799, by rfl⟩ : syracuseStep 4799465 = 3599599) B3599599
theorem B3199643 : Blo 2131435 3199643 := bstep (se 1 (by rfl) ⟨2399732, by rfl⟩ : syracuseStep 3199643 = 4799465) B4799465
theorem B2133095 : Blo 2131435 2133095 := bstep (se 1 (by rfl) ⟨1599821, by rfl⟩ : syracuseStep 2133095 = 3199643) B3199643
theorem B2399737 : Blo 2131435 2399737 := bbase (se 2 (by rfl) ⟨899901, by rfl⟩ : syracuseStep 2399737 = 1799803) (by norm_num)
theorem B3199649 : Blo 2131435 3199649 := bstep (se 2 (by rfl) ⟨1199868, by rfl⟩ : syracuseStep 3199649 = 2399737) B2399737
theorem B2133099 : Blo 2131435 2133099 := bstep (se 1 (by rfl) ⟨1599824, by rfl⟩ : syracuseStep 2133099 = 3199649) B3199649
theorem B4160821 : Blo 2131435 4160821 := bbase (se 5 (by rfl) ⟨195038, by rfl⟩ : syracuseStep 4160821 = 390077) (by norm_num)
theorem B5547761 : Blo 2131435 5547761 := bstep (se 2 (by rfl) ⟨2080410, by rfl⟩ : syracuseStep 5547761 = 4160821) B4160821
theorem B3698507 : Blo 2131435 3698507 := bstep (se 1 (by rfl) ⟨2773880, by rfl⟩ : syracuseStep 3698507 = 5547761) B5547761
theorem B2465671 : Blo 2131435 2465671 := bstep (se 1 (by rfl) ⟨1849253, by rfl⟩ : syracuseStep 2465671 = 3698507) B3698507
theorem B3287561 : Blo 2131435 3287561 := bstep (se 2 (by rfl) ⟨1232835, by rfl⟩ : syracuseStep 3287561 = 2465671) B2465671
theorem B8766829 : Blo 2131435 8766829 := bstep (se 3 (by rfl) ⟨1643780, by rfl⟩ : syracuseStep 8766829 = 3287561) B3287561
theorem B11689105 : Blo 2131435 11689105 := bstep (se 2 (by rfl) ⟨4383414, by rfl⟩ : syracuseStep 11689105 = 8766829) B8766829
theorem B15585473 : Blo 2131435 15585473 := bstep (se 2 (by rfl) ⟨5844552, by rfl⟩ : syracuseStep 15585473 = 11689105) B11689105
theorem B41561261 : Blo 2131435 41561261 := bstep (se 3 (by rfl) ⟨7792736, by rfl⟩ : syracuseStep 41561261 = 15585473) B15585473
theorem B27707507 : Blo 2131435 27707507 := bstep (se 1 (by rfl) ⟨20780630, by rfl⟩ : syracuseStep 27707507 = 41561261) B41561261
theorem B18471671 : Blo 2131435 18471671 := bstep (se 1 (by rfl) ⟨13853753, by rfl⟩ : syracuseStep 18471671 = 27707507) B27707507
theorem B12314447 : Blo 2131435 12314447 := bstep (se 1 (by rfl) ⟨9235835, by rfl⟩ : syracuseStep 12314447 = 18471671) B18471671
theorem B8209631 : Blo 2131435 8209631 := bstep (se 1 (by rfl) ⟨6157223, by rfl⟩ : syracuseStep 8209631 = 12314447) B12314447
theorem B21892349 : Blo 2131435 21892349 := bstep (se 3 (by rfl) ⟨4104815, by rfl⟩ : syracuseStep 21892349 = 8209631) B8209631
theorem B14594899 : Blo 2131435 14594899 := bstep (se 1 (by rfl) ⟨10946174, by rfl⟩ : syracuseStep 14594899 = 21892349) B21892349
theorem B19459865 : Blo 2131435 19459865 := bstep (se 2 (by rfl) ⟨7297449, by rfl⟩ : syracuseStep 19459865 = 14594899) B14594899
theorem B12973243 : Blo 2131435 12973243 := bstep (se 1 (by rfl) ⟨9729932, by rfl⟩ : syracuseStep 12973243 = 19459865) B19459865
theorem B17297657 : Blo 2131435 17297657 := bstep (se 2 (by rfl) ⟨6486621, by rfl⟩ : syracuseStep 17297657 = 12973243) B12973243
theorem B11531771 : Blo 2131435 11531771 := bstep (se 1 (by rfl) ⟨8648828, by rfl⟩ : syracuseStep 11531771 = 17297657) B17297657
theorem B7687847 : Blo 2131435 7687847 := bstep (se 1 (by rfl) ⟨5765885, by rfl⟩ : syracuseStep 7687847 = 11531771) B11531771
theorem B5125231 : Blo 2131435 5125231 := bstep (se 1 (by rfl) ⟨3843923, by rfl⟩ : syracuseStep 5125231 = 7687847) B7687847
theorem B6833641 : Blo 2131435 6833641 := bstep (se 2 (by rfl) ⟨2562615, by rfl⟩ : syracuseStep 6833641 = 5125231) B5125231
theorem B9111521 : Blo 2131435 9111521 := bstep (se 2 (by rfl) ⟨3416820, by rfl⟩ : syracuseStep 9111521 = 6833641) B6833641
theorem B6074347 : Blo 2131435 6074347 := bstep (se 1 (by rfl) ⟨4555760, by rfl⟩ : syracuseStep 6074347 = 9111521) B9111521
theorem B8099129 : Blo 2131435 8099129 := bstep (se 2 (by rfl) ⟨3037173, by rfl⟩ : syracuseStep 8099129 = 6074347) B6074347
theorem B5399419 : Blo 2131435 5399419 := bstep (se 1 (by rfl) ⟨4049564, by rfl⟩ : syracuseStep 5399419 = 8099129) B8099129
theorem B7199225 : Blo 2131435 7199225 := bstep (se 2 (by rfl) ⟨2699709, by rfl⟩ : syracuseStep 7199225 = 5399419) B5399419
theorem B4799483 : Blo 2131435 4799483 := bstep (se 1 (by rfl) ⟨3599612, by rfl⟩ : syracuseStep 4799483 = 7199225) B7199225
theorem B3199655 : Blo 2131435 3199655 := bstep (se 1 (by rfl) ⟨2399741, by rfl⟩ : syracuseStep 3199655 = 4799483) B4799483
theorem B2133103 : Blo 2131435 2133103 := bstep (se 1 (by rfl) ⟨1599827, by rfl⟩ : syracuseStep 2133103 = 3199655) B3199655
theorem B3199661 : Blo 2131435 3199661 := bbase (se 3 (by rfl) ⟨599936, by rfl⟩ : syracuseStep 3199661 = 1199873) (by norm_num)
theorem B2133107 : Blo 2131435 2133107 := bstep (se 1 (by rfl) ⟨1599830, by rfl⟩ : syracuseStep 2133107 = 3199661) B3199661
theorem B4799501 : Blo 2131435 4799501 := bbase (se 3 (by rfl) ⟨899906, by rfl⟩ : syracuseStep 4799501 = 1799813) (by norm_num)
theorem B3199667 : Blo 2131435 3199667 := bstep (se 1 (by rfl) ⟨2399750, by rfl⟩ : syracuseStep 3199667 = 4799501) B4799501
theorem B2133111 : Blo 2131435 2133111 := bstep (se 1 (by rfl) ⟨1599833, by rfl⟩ : syracuseStep 2133111 = 3199667) B3199667
theorem B2699725 : Blo 2131435 2699725 := bbase (se 3 (by rfl) ⟨506198, by rfl⟩ : syracuseStep 2699725 = 1012397) (by norm_num)
theorem B3599633 : Blo 2131435 3599633 := bstep (se 2 (by rfl) ⟨1349862, by rfl⟩ : syracuseStep 3599633 = 2699725) B2699725
theorem B2399755 : Blo 2131435 2399755 := bstep (se 1 (by rfl) ⟨1799816, by rfl⟩ : syracuseStep 2399755 = 3599633) B3599633
theorem B3199673 : Blo 2131435 3199673 := bstep (se 2 (by rfl) ⟨1199877, by rfl⟩ : syracuseStep 3199673 = 2399755) B2399755
theorem B2133115 : Blo 2131435 2133115 := bstep (se 1 (by rfl) ⟨1599836, by rfl⟩ : syracuseStep 2133115 = 3199673) B3199673
theorem B4809557 : Blo 2131435 4809557 := bbase (se 9 (by rfl) ⟨14090, by rfl⟩ : syracuseStep 4809557 = 28181) (by norm_num)
theorem B12825485 : Blo 2131435 12825485 := bstep (se 3 (by rfl) ⟨2404778, by rfl⟩ : syracuseStep 12825485 = 4809557) B4809557
theorem B8550323 : Blo 2131435 8550323 := bstep (se 1 (by rfl) ⟨6412742, by rfl⟩ : syracuseStep 8550323 = 12825485) B12825485
theorem B5700215 : Blo 2131435 5700215 := bstep (se 1 (by rfl) ⟨4275161, by rfl⟩ : syracuseStep 5700215 = 8550323) B8550323
theorem B3800143 : Blo 2131435 3800143 := bstep (se 1 (by rfl) ⟨2850107, by rfl⟩ : syracuseStep 3800143 = 5700215) B5700215
theorem B5066857 : Blo 2131435 5066857 := bstep (se 2 (by rfl) ⟨1900071, by rfl⟩ : syracuseStep 5066857 = 3800143) B3800143
theorem B6755809 : Blo 2131435 6755809 := bstep (se 2 (by rfl) ⟨2533428, by rfl⟩ : syracuseStep 6755809 = 5066857) B5066857
theorem B9007745 : Blo 2131435 9007745 := bstep (se 2 (by rfl) ⟨3377904, by rfl⟩ : syracuseStep 9007745 = 6755809) B6755809
theorem B24020653 : Blo 2131435 24020653 := bstep (se 3 (by rfl) ⟨4503872, by rfl⟩ : syracuseStep 24020653 = 9007745) B9007745
theorem B32027537 : Blo 2131435 32027537 := bstep (se 2 (by rfl) ⟨12010326, by rfl⟩ : syracuseStep 32027537 = 24020653) B24020653
theorem B21351691 : Blo 2131435 21351691 := bstep (se 1 (by rfl) ⟨16013768, by rfl⟩ : syracuseStep 21351691 = 32027537) B32027537
theorem B28468921 : Blo 2131435 28468921 := bstep (se 2 (by rfl) ⟨10675845, by rfl⟩ : syracuseStep 28468921 = 21351691) B21351691
theorem B37958561 : Blo 2131435 37958561 := bstep (se 2 (by rfl) ⟨14234460, by rfl⟩ : syracuseStep 37958561 = 28468921) B28468921
theorem B25305707 : Blo 2131435 25305707 := bstep (se 1 (by rfl) ⟨18979280, by rfl⟩ : syracuseStep 25305707 = 37958561) B37958561
theorem B67481885 : Blo 2131435 67481885 := bstep (se 3 (by rfl) ⟨12652853, by rfl⟩ : syracuseStep 67481885 = 25305707) B25305707
theorem B44987923 : Blo 2131435 44987923 := bstep (se 1 (by rfl) ⟨33740942, by rfl⟩ : syracuseStep 44987923 = 67481885) B67481885
theorem B59983897 : Blo 2131435 59983897 := bstep (se 2 (by rfl) ⟨22493961, by rfl⟩ : syracuseStep 59983897 = 44987923) B44987923
theorem B79978529 : Blo 2131435 79978529 := bstep (se 2 (by rfl) ⟨29991948, by rfl⟩ : syracuseStep 79978529 = 59983897) B59983897
theorem B53319019 : Blo 2131435 53319019 := bstep (se 1 (by rfl) ⟨39989264, by rfl⟩ : syracuseStep 53319019 = 79978529) B79978529
theorem B71092025 : Blo 2131435 71092025 := bstep (se 2 (by rfl) ⟨26659509, by rfl⟩ : syracuseStep 71092025 = 53319019) B53319019
theorem B47394683 : Blo 2131435 47394683 := bstep (se 1 (by rfl) ⟨35546012, by rfl⟩ : syracuseStep 47394683 = 71092025) B71092025
theorem B31596455 : Blo 2131435 31596455 := bstep (se 1 (by rfl) ⟨23697341, by rfl⟩ : syracuseStep 31596455 = 47394683) B47394683
theorem B21064303 : Blo 2131435 21064303 := bstep (se 1 (by rfl) ⟨15798227, by rfl⟩ : syracuseStep 21064303 = 31596455) B31596455
theorem B28085737 : Blo 2131435 28085737 := bstep (se 2 (by rfl) ⟨10532151, by rfl⟩ : syracuseStep 28085737 = 21064303) B21064303
theorem B37447649 : Blo 2131435 37447649 := bstep (se 2 (by rfl) ⟨14042868, by rfl⟩ : syracuseStep 37447649 = 28085737) B28085737
theorem B24965099 : Blo 2131435 24965099 := bstep (se 1 (by rfl) ⟨18723824, by rfl⟩ : syracuseStep 24965099 = 37447649) B37447649
theorem B16643399 : Blo 2131435 16643399 := bstep (se 1 (by rfl) ⟨12482549, by rfl⟩ : syracuseStep 16643399 = 24965099) B24965099
theorem B177529589 : Blo 2131435 177529589 := bstep (se 5 (by rfl) ⟨8321699, by rfl⟩ : syracuseStep 177529589 = 16643399) B16643399
theorem B118353059 : Blo 2131435 118353059 := bstep (se 1 (by rfl) ⟨88764794, by rfl⟩ : syracuseStep 118353059 = 177529589) B177529589
theorem B78902039 : Blo 2131435 78902039 := bstep (se 1 (by rfl) ⟨59176529, by rfl⟩ : syracuseStep 78902039 = 118353059) B118353059
theorem B52601359 : Blo 2131435 52601359 := bstep (se 1 (by rfl) ⟨39451019, by rfl⟩ : syracuseStep 52601359 = 78902039) B78902039
theorem B70135145 : Blo 2131435 70135145 := bstep (se 2 (by rfl) ⟨26300679, by rfl⟩ : syracuseStep 70135145 = 52601359) B52601359
theorem B46756763 : Blo 2131435 46756763 := bstep (se 1 (by rfl) ⟨35067572, by rfl⟩ : syracuseStep 46756763 = 70135145) B70135145
theorem B31171175 : Blo 2131435 31171175 := bstep (se 1 (by rfl) ⟨23378381, by rfl⟩ : syracuseStep 31171175 = 46756763) B46756763
theorem B20780783 : Blo 2131435 20780783 := bstep (se 1 (by rfl) ⟨15585587, by rfl⟩ : syracuseStep 20780783 = 31171175) B31171175
theorem B13853855 : Blo 2131435 13853855 := bstep (se 1 (by rfl) ⟨10390391, by rfl⟩ : syracuseStep 13853855 = 20780783) B20780783
theorem B9235903 : Blo 2131435 9235903 := bstep (se 1 (by rfl) ⟨6926927, by rfl⟩ : syracuseStep 9235903 = 13853855) B13853855
theorem B12314537 : Blo 2131435 12314537 := bstep (se 2 (by rfl) ⟨4617951, by rfl⟩ : syracuseStep 12314537 = 9235903) B9235903
theorem B8209691 : Blo 2131435 8209691 := bstep (se 1 (by rfl) ⟨6157268, by rfl⟩ : syracuseStep 8209691 = 12314537) B12314537
theorem B5473127 : Blo 2131435 5473127 := bstep (se 1 (by rfl) ⟨4104845, by rfl⟩ : syracuseStep 5473127 = 8209691) B8209691
theorem B14595005 : Blo 2131435 14595005 := bstep (se 3 (by rfl) ⟨2736563, by rfl⟩ : syracuseStep 14595005 = 5473127) B5473127
theorem B38920013 : Blo 2131435 38920013 := bstep (se 3 (by rfl) ⟨7297502, by rfl⟩ : syracuseStep 38920013 = 14595005) B14595005
theorem B25946675 : Blo 2131435 25946675 := bstep (se 1 (by rfl) ⟨19460006, by rfl⟩ : syracuseStep 25946675 = 38920013) B38920013
theorem B17297783 : Blo 2131435 17297783 := bstep (se 1 (by rfl) ⟨12973337, by rfl⟩ : syracuseStep 17297783 = 25946675) B25946675
theorem B11531855 : Blo 2131435 11531855 := bstep (se 1 (by rfl) ⟨8648891, by rfl⟩ : syracuseStep 11531855 = 17297783) B17297783
theorem B30751613 : Blo 2131435 30751613 := bstep (se 3 (by rfl) ⟨5765927, by rfl⟩ : syracuseStep 30751613 = 11531855) B11531855
theorem B20501075 : Blo 2131435 20501075 := bstep (se 1 (by rfl) ⟨15375806, by rfl⟩ : syracuseStep 20501075 = 30751613) B30751613
theorem B13667383 : Blo 2131435 13667383 := bstep (se 1 (by rfl) ⟨10250537, by rfl⟩ : syracuseStep 13667383 = 20501075) B20501075
theorem B18223177 : Blo 2131435 18223177 := bstep (se 2 (by rfl) ⟨6833691, by rfl⟩ : syracuseStep 18223177 = 13667383) B13667383
theorem B24297569 : Blo 2131435 24297569 := bstep (se 2 (by rfl) ⟨9111588, by rfl⟩ : syracuseStep 24297569 = 18223177) B18223177
theorem B16198379 : Blo 2131435 16198379 := bstep (se 1 (by rfl) ⟨12148784, by rfl⟩ : syracuseStep 16198379 = 24297569) B24297569
theorem B10798919 : Blo 2131435 10798919 := bstep (se 1 (by rfl) ⟨8099189, by rfl⟩ : syracuseStep 10798919 = 16198379) B16198379
theorem B7199279 : Blo 2131435 7199279 := bstep (se 1 (by rfl) ⟨5399459, by rfl⟩ : syracuseStep 7199279 = 10798919) B10798919
theorem B4799519 : Blo 2131435 4799519 := bstep (se 1 (by rfl) ⟨3599639, by rfl⟩ : syracuseStep 4799519 = 7199279) B7199279
theorem B3199679 : Blo 2131435 3199679 := bstep (se 1 (by rfl) ⟨2399759, by rfl⟩ : syracuseStep 3199679 = 4799519) B4799519
theorem B2133119 : Blo 2131435 2133119 := bstep (se 1 (by rfl) ⟨1599839, by rfl⟩ : syracuseStep 2133119 = 3199679) B3199679
theorem B3199685 : Blo 2131435 3199685 := bbase (se 4 (by rfl) ⟨299970, by rfl⟩ : syracuseStep 3199685 = 599941) (by norm_num)
theorem B2133123 : Blo 2131435 2133123 := bstep (se 1 (by rfl) ⟨1599842, by rfl⟩ : syracuseStep 2133123 = 3199685) B3199685
theorem B3599653 : Blo 2131435 3599653 := bbase (se 4 (by rfl) ⟨337467, by rfl⟩ : syracuseStep 3599653 = 674935) (by norm_num)
theorem B4799537 : Blo 2131435 4799537 := bstep (se 2 (by rfl) ⟨1799826, by rfl⟩ : syracuseStep 4799537 = 3599653) B3599653
theorem B3199691 : Blo 2131435 3199691 := bstep (se 1 (by rfl) ⟨2399768, by rfl⟩ : syracuseStep 3199691 = 4799537) B4799537
theorem B2133127 : Blo 2131435 2133127 := bstep (se 1 (by rfl) ⟨1599845, by rfl⟩ : syracuseStep 2133127 = 3199691) B3199691
theorem B2399773 : Blo 2131435 2399773 := bbase (se 3 (by rfl) ⟨449957, by rfl⟩ : syracuseStep 2399773 = 899915) (by norm_num)
theorem B3199697 : Blo 2131435 3199697 := bstep (se 2 (by rfl) ⟨1199886, by rfl⟩ : syracuseStep 3199697 = 2399773) B2399773
theorem B2133131 : Blo 2131435 2133131 := bstep (se 1 (by rfl) ⟨1599848, by rfl⟩ : syracuseStep 2133131 = 3199697) B3199697
theorem B7199333 : Blo 2131435 7199333 := bbase (se 4 (by rfl) ⟨674937, by rfl⟩ : syracuseStep 7199333 = 1349875) (by norm_num)
theorem B4799555 : Blo 2131435 4799555 := bstep (se 1 (by rfl) ⟨3599666, by rfl⟩ : syracuseStep 4799555 = 7199333) B7199333
theorem B3199703 : Blo 2131435 3199703 := bstep (se 1 (by rfl) ⟨2399777, by rfl⟩ : syracuseStep 3199703 = 4799555) B4799555
theorem B2133135 : Blo 2131435 2133135 := bstep (se 1 (by rfl) ⟨1599851, by rfl⟩ : syracuseStep 2133135 = 3199703) B3199703
theorem B3199709 : Blo 2131435 3199709 := bbase (se 3 (by rfl) ⟨599945, by rfl⟩ : syracuseStep 3199709 = 1199891) (by norm_num)
theorem B2133139 : Blo 2131435 2133139 := bstep (se 1 (by rfl) ⟨1599854, by rfl⟩ : syracuseStep 2133139 = 3199709) B3199709
theorem B4799573 : Blo 2131435 4799573 := bbase (se 8 (by rfl) ⟨28122, by rfl⟩ : syracuseStep 4799573 = 56245) (by norm_num)
theorem B3199715 : Blo 2131435 3199715 := bstep (se 1 (by rfl) ⟨2399786, by rfl⟩ : syracuseStep 3199715 = 4799573) B4799573
theorem B2133143 : Blo 2131435 2133143 := bstep (se 1 (by rfl) ⟨1599857, by rfl⟩ : syracuseStep 2133143 = 3199715) B3199715
theorem B5766005 : Blo 2131435 5766005 := bbase (se 5 (by rfl) ⟨270281, by rfl⟩ : syracuseStep 5766005 = 540563) (by norm_num)
theorem B15376013 : Blo 2131435 15376013 := bstep (se 3 (by rfl) ⟨2883002, by rfl⟩ : syracuseStep 15376013 = 5766005) B5766005
theorem B10250675 : Blo 2131435 10250675 := bstep (se 1 (by rfl) ⟨7688006, by rfl⟩ : syracuseStep 10250675 = 15376013) B15376013
theorem B6833783 : Blo 2131435 6833783 := bstep (se 1 (by rfl) ⟨5125337, by rfl⟩ : syracuseStep 6833783 = 10250675) B10250675
theorem B4555855 : Blo 2131435 4555855 := bstep (se 1 (by rfl) ⟨3416891, by rfl⟩ : syracuseStep 4555855 = 6833783) B6833783
theorem B6074473 : Blo 2131435 6074473 := bstep (se 2 (by rfl) ⟨2277927, by rfl⟩ : syracuseStep 6074473 = 4555855) B4555855
theorem B8099297 : Blo 2131435 8099297 := bstep (se 2 (by rfl) ⟨3037236, by rfl⟩ : syracuseStep 8099297 = 6074473) B6074473
theorem B5399531 : Blo 2131435 5399531 := bstep (se 1 (by rfl) ⟨4049648, by rfl⟩ : syracuseStep 5399531 = 8099297) B8099297
theorem B3599687 : Blo 2131435 3599687 := bstep (se 1 (by rfl) ⟨2699765, by rfl⟩ : syracuseStep 3599687 = 5399531) B5399531
theorem B2399791 : Blo 2131435 2399791 := bstep (se 1 (by rfl) ⟨1799843, by rfl⟩ : syracuseStep 2399791 = 3599687) B3599687
theorem B3199721 : Blo 2131435 3199721 := bstep (se 2 (by rfl) ⟨1199895, by rfl⟩ : syracuseStep 3199721 = 2399791) B2399791
theorem B2133147 : Blo 2131435 2133147 := bstep (se 1 (by rfl) ⟨1599860, by rfl⟩ : syracuseStep 2133147 = 3199721) B3199721
theorem B2736605 : Blo 2131435 2736605 := bbase (se 3 (by rfl) ⟨513113, by rfl⟩ : syracuseStep 2736605 = 1026227) (by norm_num)
theorem B7297613 : Blo 2131435 7297613 := bstep (se 3 (by rfl) ⟨1368302, by rfl⟩ : syracuseStep 7297613 = 2736605) B2736605
theorem B4865075 : Blo 2131435 4865075 := bstep (se 1 (by rfl) ⟨3648806, by rfl⟩ : syracuseStep 4865075 = 7297613) B7297613
theorem B3243383 : Blo 2131435 3243383 := bstep (se 1 (by rfl) ⟨2432537, by rfl⟩ : syracuseStep 3243383 = 4865075) B4865075
theorem B34596085 : Blo 2131435 34596085 := bstep (se 5 (by rfl) ⟨1621691, by rfl⟩ : syracuseStep 34596085 = 3243383) B3243383
theorem B46128113 : Blo 2131435 46128113 := bstep (se 2 (by rfl) ⟨17298042, by rfl⟩ : syracuseStep 46128113 = 34596085) B34596085
theorem B30752075 : Blo 2131435 30752075 := bstep (se 1 (by rfl) ⟨23064056, by rfl⟩ : syracuseStep 30752075 = 46128113) B46128113
theorem B20501383 : Blo 2131435 20501383 := bstep (se 1 (by rfl) ⟨15376037, by rfl⟩ : syracuseStep 20501383 = 30752075) B30752075
theorem B27335177 : Blo 2131435 27335177 := bstep (se 2 (by rfl) ⟨10250691, by rfl⟩ : syracuseStep 27335177 = 20501383) B20501383
theorem B18223451 : Blo 2131435 18223451 := bstep (se 1 (by rfl) ⟨13667588, by rfl⟩ : syracuseStep 18223451 = 27335177) B27335177
theorem B12148967 : Blo 2131435 12148967 := bstep (se 1 (by rfl) ⟨9111725, by rfl⟩ : syracuseStep 12148967 = 18223451) B18223451
theorem B8099311 : Blo 2131435 8099311 := bstep (se 1 (by rfl) ⟨6074483, by rfl⟩ : syracuseStep 8099311 = 12148967) B12148967
theorem B10799081 : Blo 2131435 10799081 := bstep (se 2 (by rfl) ⟨4049655, by rfl⟩ : syracuseStep 10799081 = 8099311) B8099311
theorem B7199387 : Blo 2131435 7199387 := bstep (se 1 (by rfl) ⟨5399540, by rfl⟩ : syracuseStep 7199387 = 10799081) B10799081
theorem B4799591 : Blo 2131435 4799591 := bstep (se 1 (by rfl) ⟨3599693, by rfl⟩ : syracuseStep 4799591 = 7199387) B7199387
theorem B3199727 : Blo 2131435 3199727 := bstep (se 1 (by rfl) ⟨2399795, by rfl⟩ : syracuseStep 3199727 = 4799591) B4799591
theorem B2133151 : Blo 2131435 2133151 := bstep (se 1 (by rfl) ⟨1599863, by rfl⟩ : syracuseStep 2133151 = 3199727) B3199727
theorem B3199733 : Blo 2131435 3199733 := bbase (se 5 (by rfl) ⟨149987, by rfl⟩ : syracuseStep 3199733 = 299975) (by norm_num)
theorem B2133155 : Blo 2131435 2133155 := bstep (se 1 (by rfl) ⟨1599866, by rfl⟩ : syracuseStep 2133155 = 3199733) B3199733
theorem B3243397 : Blo 2131435 3243397 := bbase (se 4 (by rfl) ⟨304068, by rfl⟩ : syracuseStep 3243397 = 608137) (by norm_num)
theorem B4324529 : Blo 2131435 4324529 := bstep (se 2 (by rfl) ⟨1621698, by rfl⟩ : syracuseStep 4324529 = 3243397) B3243397
theorem B2883019 : Blo 2131435 2883019 := bstep (se 1 (by rfl) ⟨2162264, by rfl⟩ : syracuseStep 2883019 = 4324529) B4324529
theorem B3844025 : Blo 2131435 3844025 := bstep (se 2 (by rfl) ⟨1441509, by rfl⟩ : syracuseStep 3844025 = 2883019) B2883019
theorem B2562683 : Blo 2131435 2562683 := bstep (se 1 (by rfl) ⟨1922012, by rfl⟩ : syracuseStep 2562683 = 3844025) B3844025
theorem B6833821 : Blo 2131435 6833821 := bstep (se 3 (by rfl) ⟨1281341, by rfl⟩ : syracuseStep 6833821 = 2562683) B2562683
theorem B9111761 : Blo 2131435 9111761 := bstep (se 2 (by rfl) ⟨3416910, by rfl⟩ : syracuseStep 9111761 = 6833821) B6833821
theorem B6074507 : Blo 2131435 6074507 := bstep (se 1 (by rfl) ⟨4555880, by rfl⟩ : syracuseStep 6074507 = 9111761) B9111761
theorem B4049671 : Blo 2131435 4049671 := bstep (se 1 (by rfl) ⟨3037253, by rfl⟩ : syracuseStep 4049671 = 6074507) B6074507
theorem B5399561 : Blo 2131435 5399561 := bstep (se 2 (by rfl) ⟨2024835, by rfl⟩ : syracuseStep 5399561 = 4049671) B4049671
theorem B3599707 : Blo 2131435 3599707 := bstep (se 1 (by rfl) ⟨2699780, by rfl⟩ : syracuseStep 3599707 = 5399561) B5399561
theorem B4799609 : Blo 2131435 4799609 := bstep (se 2 (by rfl) ⟨1799853, by rfl⟩ : syracuseStep 4799609 = 3599707) B3599707
theorem B3199739 : Blo 2131435 3199739 := bstep (se 1 (by rfl) ⟨2399804, by rfl⟩ : syracuseStep 3199739 = 4799609) B4799609
theorem B2133159 : Blo 2131435 2133159 := bstep (se 1 (by rfl) ⟨1599869, by rfl⟩ : syracuseStep 2133159 = 3199739) B3199739
theorem B2399809 : Blo 2131435 2399809 := bbase (se 2 (by rfl) ⟨899928, by rfl⟩ : syracuseStep 2399809 = 1799857) (by norm_num)
theorem B3199745 : Blo 2131435 3199745 := bstep (se 2 (by rfl) ⟨1199904, by rfl⟩ : syracuseStep 3199745 = 2399809) B2399809
theorem B2133163 : Blo 2131435 2133163 := bstep (se 1 (by rfl) ⟨1599872, by rfl⟩ : syracuseStep 2133163 = 3199745) B3199745
theorem B5399581 : Blo 2131435 5399581 := bbase (se 3 (by rfl) ⟨1012421, by rfl⟩ : syracuseStep 5399581 = 2024843) (by norm_num)
theorem B7199441 : Blo 2131435 7199441 := bstep (se 2 (by rfl) ⟨2699790, by rfl⟩ : syracuseStep 7199441 = 5399581) B5399581
theorem B4799627 : Blo 2131435 4799627 := bstep (se 1 (by rfl) ⟨3599720, by rfl⟩ : syracuseStep 4799627 = 7199441) B7199441
theorem B3199751 : Blo 2131435 3199751 := bstep (se 1 (by rfl) ⟨2399813, by rfl⟩ : syracuseStep 3199751 = 4799627) B4799627
theorem B2133167 : Blo 2131435 2133167 := bstep (se 1 (by rfl) ⟨1599875, by rfl⟩ : syracuseStep 2133167 = 3199751) B3199751
theorem B3199757 : Blo 2131435 3199757 := bbase (se 3 (by rfl) ⟨599954, by rfl⟩ : syracuseStep 3199757 = 1199909) (by norm_num)
theorem B2133171 : Blo 2131435 2133171 := bstep (se 1 (by rfl) ⟨1599878, by rfl⟩ : syracuseStep 2133171 = 3199757) B3199757
theorem B4799645 : Blo 2131435 4799645 := bbase (se 3 (by rfl) ⟨899933, by rfl⟩ : syracuseStep 4799645 = 1799867) (by norm_num)
theorem B3199763 : Blo 2131435 3199763 := bstep (se 1 (by rfl) ⟨2399822, by rfl⟩ : syracuseStep 3199763 = 4799645) B4799645
theorem B2133175 : Blo 2131435 2133175 := bstep (se 1 (by rfl) ⟨1599881, by rfl⟩ : syracuseStep 2133175 = 3199763) B3199763
theorem B3599741 : Blo 2131435 3599741 := bbase (se 3 (by rfl) ⟨674951, by rfl⟩ : syracuseStep 3599741 = 1349903) (by norm_num)
theorem B2399827 : Blo 2131435 2399827 := bstep (se 1 (by rfl) ⟨1799870, by rfl⟩ : syracuseStep 2399827 = 3599741) B3599741
theorem B3199769 : Blo 2131435 3199769 := bstep (se 2 (by rfl) ⟨1199913, by rfl⟩ : syracuseStep 3199769 = 2399827) B2399827
theorem B2133179 : Blo 2131435 2133179 := bstep (se 1 (by rfl) ⟨1599884, by rfl⟩ : syracuseStep 2133179 = 3199769) B3199769
theorem B5844773 : Blo 2131435 5844773 := bbase (se 4 (by rfl) ⟨547947, by rfl⟩ : syracuseStep 5844773 = 1095895) (by norm_num)
theorem B3896515 : Blo 2131435 3896515 := bstep (se 1 (by rfl) ⟨2922386, by rfl⟩ : syracuseStep 3896515 = 5844773) B5844773
theorem B5195353 : Blo 2131435 5195353 := bstep (se 2 (by rfl) ⟨1948257, by rfl⟩ : syracuseStep 5195353 = 3896515) B3896515
theorem B6927137 : Blo 2131435 6927137 := bstep (se 2 (by rfl) ⟨2597676, by rfl⟩ : syracuseStep 6927137 = 5195353) B5195353
theorem B4618091 : Blo 2131435 4618091 := bstep (se 1 (by rfl) ⟨3463568, by rfl⟩ : syracuseStep 4618091 = 6927137) B6927137
theorem B12314909 : Blo 2131435 12314909 := bstep (se 3 (by rfl) ⟨2309045, by rfl⟩ : syracuseStep 12314909 = 4618091) B4618091
theorem B8209939 : Blo 2131435 8209939 := bstep (se 1 (by rfl) ⟨6157454, by rfl⟩ : syracuseStep 8209939 = 12314909) B12314909
theorem B10946585 : Blo 2131435 10946585 := bstep (se 2 (by rfl) ⟨4104969, by rfl⟩ : syracuseStep 10946585 = 8209939) B8209939
theorem B7297723 : Blo 2131435 7297723 := bstep (se 1 (by rfl) ⟨5473292, by rfl⟩ : syracuseStep 7297723 = 10946585) B10946585
theorem B9730297 : Blo 2131435 9730297 := bstep (se 2 (by rfl) ⟨3648861, by rfl⟩ : syracuseStep 9730297 = 7297723) B7297723
theorem B12973729 : Blo 2131435 12973729 := bstep (se 2 (by rfl) ⟨4865148, by rfl⟩ : syracuseStep 12973729 = 9730297) B9730297
theorem B17298305 : Blo 2131435 17298305 := bstep (se 2 (by rfl) ⟨6486864, by rfl⟩ : syracuseStep 17298305 = 12973729) B12973729
theorem B11532203 : Blo 2131435 11532203 := bstep (se 1 (by rfl) ⟨8649152, by rfl⟩ : syracuseStep 11532203 = 17298305) B17298305
theorem B7688135 : Blo 2131435 7688135 := bstep (se 1 (by rfl) ⟨5766101, by rfl⟩ : syracuseStep 7688135 = 11532203) B11532203
theorem B5125423 : Blo 2131435 5125423 := bstep (se 1 (by rfl) ⟨3844067, by rfl⟩ : syracuseStep 5125423 = 7688135) B7688135
theorem B6833897 : Blo 2131435 6833897 := bstep (se 2 (by rfl) ⟨2562711, by rfl⟩ : syracuseStep 6833897 = 5125423) B5125423
theorem B4555931 : Blo 2131435 4555931 := bstep (se 1 (by rfl) ⟨3416948, by rfl⟩ : syracuseStep 4555931 = 6833897) B6833897
theorem B12149149 : Blo 2131435 12149149 := bstep (se 3 (by rfl) ⟨2277965, by rfl⟩ : syracuseStep 12149149 = 4555931) B4555931
theorem B16198865 : Blo 2131435 16198865 := bstep (se 2 (by rfl) ⟨6074574, by rfl⟩ : syracuseStep 16198865 = 12149149) B12149149
theorem B10799243 : Blo 2131435 10799243 := bstep (se 1 (by rfl) ⟨8099432, by rfl⟩ : syracuseStep 10799243 = 16198865) B16198865
theorem B7199495 : Blo 2131435 7199495 := bstep (se 1 (by rfl) ⟨5399621, by rfl⟩ : syracuseStep 7199495 = 10799243) B10799243
theorem B4799663 : Blo 2131435 4799663 := bstep (se 1 (by rfl) ⟨3599747, by rfl⟩ : syracuseStep 4799663 = 7199495) B7199495
theorem B3199775 : Blo 2131435 3199775 := bstep (se 1 (by rfl) ⟨2399831, by rfl⟩ : syracuseStep 3199775 = 4799663) B4799663
theorem B2133183 : Blo 2131435 2133183 := bstep (se 1 (by rfl) ⟨1599887, by rfl⟩ : syracuseStep 2133183 = 3199775) B3199775
theorem B3199781 : Blo 2131435 3199781 := bbase (se 4 (by rfl) ⟨299979, by rfl⟩ : syracuseStep 3199781 = 599959) (by norm_num)
theorem B2133187 : Blo 2131435 2133187 := bstep (se 1 (by rfl) ⟨1599890, by rfl⟩ : syracuseStep 2133187 = 3199781) B3199781
theorem B2699821 : Blo 2131435 2699821 := bbase (se 3 (by rfl) ⟨506216, by rfl⟩ : syracuseStep 2699821 = 1012433) (by norm_num)
theorem B3599761 : Blo 2131435 3599761 := bstep (se 2 (by rfl) ⟨1349910, by rfl⟩ : syracuseStep 3599761 = 2699821) B2699821
theorem B4799681 : Blo 2131435 4799681 := bstep (se 2 (by rfl) ⟨1799880, by rfl⟩ : syracuseStep 4799681 = 3599761) B3599761
theorem B3199787 : Blo 2131435 3199787 := bstep (se 1 (by rfl) ⟨2399840, by rfl⟩ : syracuseStep 3199787 = 4799681) B4799681
theorem B2133191 : Blo 2131435 2133191 := bstep (se 1 (by rfl) ⟨1599893, by rfl⟩ : syracuseStep 2133191 = 3199787) B3199787
theorem B2399845 : Blo 2131435 2399845 := bbase (se 4 (by rfl) ⟨224985, by rfl⟩ : syracuseStep 2399845 = 449971) (by norm_num)
theorem B3199793 : Blo 2131435 3199793 := bstep (se 2 (by rfl) ⟨1199922, by rfl⟩ : syracuseStep 3199793 = 2399845) B2399845
theorem B2133195 : Blo 2131435 2133195 := bstep (se 1 (by rfl) ⟨1599896, by rfl⟩ : syracuseStep 2133195 = 3199793) B3199793
theorem B2162305 : Blo 2131435 2162305 := bbase (se 2 (by rfl) ⟨810864, by rfl⟩ : syracuseStep 2162305 = 1621729) (by norm_num)
theorem B11532293 : Blo 2131435 11532293 := bstep (se 4 (by rfl) ⟨1081152, by rfl⟩ : syracuseStep 11532293 = 2162305) B2162305
theorem B7688195 : Blo 2131435 7688195 := bstep (se 1 (by rfl) ⟨5766146, by rfl⟩ : syracuseStep 7688195 = 11532293) B11532293
theorem B5125463 : Blo 2131435 5125463 := bstep (se 1 (by rfl) ⟨3844097, by rfl⟩ : syracuseStep 5125463 = 7688195) B7688195
theorem B3416975 : Blo 2131435 3416975 := bstep (se 1 (by rfl) ⟨2562731, by rfl⟩ : syracuseStep 3416975 = 5125463) B5125463
theorem B2277983 : Blo 2131435 2277983 := bstep (se 1 (by rfl) ⟨1708487, by rfl⟩ : syracuseStep 2277983 = 3416975) B3416975
theorem B6074621 : Blo 2131435 6074621 := bstep (se 3 (by rfl) ⟨1138991, by rfl⟩ : syracuseStep 6074621 = 2277983) B2277983
theorem B4049747 : Blo 2131435 4049747 := bstep (se 1 (by rfl) ⟨3037310, by rfl⟩ : syracuseStep 4049747 = 6074621) B6074621
theorem B2699831 : Blo 2131435 2699831 := bstep (se 1 (by rfl) ⟨2024873, by rfl⟩ : syracuseStep 2699831 = 4049747) B4049747
theorem B7199549 : Blo 2131435 7199549 := bstep (se 3 (by rfl) ⟨1349915, by rfl⟩ : syracuseStep 7199549 = 2699831) B2699831
theorem B4799699 : Blo 2131435 4799699 := bstep (se 1 (by rfl) ⟨3599774, by rfl⟩ : syracuseStep 4799699 = 7199549) B7199549
theorem B3199799 : Blo 2131435 3199799 := bstep (se 1 (by rfl) ⟨2399849, by rfl⟩ : syracuseStep 3199799 = 4799699) B4799699
theorem B2133199 : Blo 2131435 2133199 := bstep (se 1 (by rfl) ⟨1599899, by rfl⟩ : syracuseStep 2133199 = 3199799) B3199799
theorem B3199805 : Blo 2131435 3199805 := bbase (se 3 (by rfl) ⟨599963, by rfl⟩ : syracuseStep 3199805 = 1199927) (by norm_num)
theorem B2133203 : Blo 2131435 2133203 := bstep (se 1 (by rfl) ⟨1599902, by rfl⟩ : syracuseStep 2133203 = 3199805) B3199805
theorem B4799717 : Blo 2131435 4799717 := bbase (se 4 (by rfl) ⟨449973, by rfl⟩ : syracuseStep 4799717 = 899947) (by norm_num)
theorem B3199811 : Blo 2131435 3199811 := bstep (se 1 (by rfl) ⟨2399858, by rfl⟩ : syracuseStep 3199811 = 4799717) B4799717
theorem B2133207 : Blo 2131435 2133207 := bstep (se 1 (by rfl) ⟨1599905, by rfl⟩ : syracuseStep 2133207 = 3199811) B3199811
theorem B5399693 : Blo 2131435 5399693 := bbase (se 3 (by rfl) ⟨1012442, by rfl⟩ : syracuseStep 5399693 = 2024885) (by norm_num)
theorem B3599795 : Blo 2131435 3599795 := bstep (se 1 (by rfl) ⟨2699846, by rfl⟩ : syracuseStep 3599795 = 5399693) B5399693
theorem B2399863 : Blo 2131435 2399863 := bstep (se 1 (by rfl) ⟨1799897, by rfl⟩ : syracuseStep 2399863 = 3599795) B3599795
theorem B3199817 : Blo 2131435 3199817 := bstep (se 2 (by rfl) ⟨1199931, by rfl⟩ : syracuseStep 3199817 = 2399863) B2399863
theorem B2133211 : Blo 2131435 2133211 := bstep (se 1 (by rfl) ⟨1599908, by rfl⟩ : syracuseStep 2133211 = 3199817) B3199817
theorem B3037333 : Blo 2131435 3037333 := bbase (se 6 (by rfl) ⟨71187, by rfl⟩ : syracuseStep 3037333 = 142375) (by norm_num)
theorem B4049777 : Blo 2131435 4049777 := bstep (se 2 (by rfl) ⟨1518666, by rfl⟩ : syracuseStep 4049777 = 3037333) B3037333
theorem B10799405 : Blo 2131435 10799405 := bstep (se 3 (by rfl) ⟨2024888, by rfl⟩ : syracuseStep 10799405 = 4049777) B4049777
theorem B7199603 : Blo 2131435 7199603 := bstep (se 1 (by rfl) ⟨5399702, by rfl⟩ : syracuseStep 7199603 = 10799405) B10799405
theorem B4799735 : Blo 2131435 4799735 := bstep (se 1 (by rfl) ⟨3599801, by rfl⟩ : syracuseStep 4799735 = 7199603) B7199603
theorem B3199823 : Blo 2131435 3199823 := bstep (se 1 (by rfl) ⟨2399867, by rfl⟩ : syracuseStep 3199823 = 4799735) B4799735
theorem B2133215 : Blo 2131435 2133215 := bstep (se 1 (by rfl) ⟨1599911, by rfl⟩ : syracuseStep 2133215 = 3199823) B3199823
theorem B3199829 : Blo 2131435 3199829 := bbase (se 9 (by rfl) ⟨9374, by rfl⟩ : syracuseStep 3199829 = 18749) (by norm_num)
theorem B2133219 : Blo 2131435 2133219 := bstep (se 1 (by rfl) ⟨1599914, by rfl⟩ : syracuseStep 2133219 = 3199829) B3199829
theorem B3417013 : Blo 2131435 3417013 := bbase (se 5 (by rfl) ⟨160172, by rfl⟩ : syracuseStep 3417013 = 320345) (by norm_num)
theorem B4556017 : Blo 2131435 4556017 := bstep (se 2 (by rfl) ⟨1708506, by rfl⟩ : syracuseStep 4556017 = 3417013) B3417013
theorem B6074689 : Blo 2131435 6074689 := bstep (se 2 (by rfl) ⟨2278008, by rfl⟩ : syracuseStep 6074689 = 4556017) B4556017
theorem B8099585 : Blo 2131435 8099585 := bstep (se 2 (by rfl) ⟨3037344, by rfl⟩ : syracuseStep 8099585 = 6074689) B6074689
theorem B5399723 : Blo 2131435 5399723 := bstep (se 1 (by rfl) ⟨4049792, by rfl⟩ : syracuseStep 5399723 = 8099585) B8099585
theorem B3599815 : Blo 2131435 3599815 := bstep (se 1 (by rfl) ⟨2699861, by rfl⟩ : syracuseStep 3599815 = 5399723) B5399723
theorem B4799753 : Blo 2131435 4799753 := bstep (se 2 (by rfl) ⟨1799907, by rfl⟩ : syracuseStep 4799753 = 3599815) B3599815
theorem B3199835 : Blo 2131435 3199835 := bstep (se 1 (by rfl) ⟨2399876, by rfl⟩ : syracuseStep 3199835 = 4799753) B4799753
theorem B2133223 : Blo 2131435 2133223 := bstep (se 1 (by rfl) ⟨1599917, by rfl⟩ : syracuseStep 2133223 = 3199835) B3199835
theorem B2399881 : Blo 2131435 2399881 := bbase (se 2 (by rfl) ⟨899955, by rfl⟩ : syracuseStep 2399881 = 1799911) (by norm_num)
theorem B3199841 : Blo 2131435 3199841 := bstep (se 2 (by rfl) ⟨1199940, by rfl⟩ : syracuseStep 3199841 = 2399881) B2399881
theorem B2133227 : Blo 2131435 2133227 := bstep (se 1 (by rfl) ⟨1599920, by rfl⟩ : syracuseStep 2133227 = 3199841) B3199841
theorem B2432629 : Blo 2131435 2432629 := bbase (se 5 (by rfl) ⟨114029, by rfl⟩ : syracuseStep 2432629 = 228059) (by norm_num)
theorem B3243505 : Blo 2131435 3243505 := bstep (se 2 (by rfl) ⟨1216314, by rfl⟩ : syracuseStep 3243505 = 2432629) B2432629
theorem B4324673 : Blo 2131435 4324673 := bstep (se 2 (by rfl) ⟨1621752, by rfl⟩ : syracuseStep 4324673 = 3243505) B3243505
theorem B11532461 : Blo 2131435 11532461 := bstep (se 3 (by rfl) ⟨2162336, by rfl⟩ : syracuseStep 11532461 = 4324673) B4324673
theorem B30753229 : Blo 2131435 30753229 := bstep (se 3 (by rfl) ⟨5766230, by rfl⟩ : syracuseStep 30753229 = 11532461) B11532461
theorem B41004305 : Blo 2131435 41004305 := bstep (se 2 (by rfl) ⟨15376614, by rfl⟩ : syracuseStep 41004305 = 30753229) B30753229
theorem B27336203 : Blo 2131435 27336203 := bstep (se 1 (by rfl) ⟨20502152, by rfl⟩ : syracuseStep 27336203 = 41004305) B41004305
theorem B18224135 : Blo 2131435 18224135 := bstep (se 1 (by rfl) ⟨13668101, by rfl⟩ : syracuseStep 18224135 = 27336203) B27336203
theorem B12149423 : Blo 2131435 12149423 := bstep (se 1 (by rfl) ⟨9112067, by rfl⟩ : syracuseStep 12149423 = 18224135) B18224135
theorem B8099615 : Blo 2131435 8099615 := bstep (se 1 (by rfl) ⟨6074711, by rfl⟩ : syracuseStep 8099615 = 12149423) B12149423
theorem B5399743 : Blo 2131435 5399743 := bstep (se 1 (by rfl) ⟨4049807, by rfl⟩ : syracuseStep 5399743 = 8099615) B8099615
theorem B7199657 : Blo 2131435 7199657 := bstep (se 2 (by rfl) ⟨2699871, by rfl⟩ : syracuseStep 7199657 = 5399743) B5399743
theorem B4799771 : Blo 2131435 4799771 := bstep (se 1 (by rfl) ⟨3599828, by rfl⟩ : syracuseStep 4799771 = 7199657) B7199657
theorem B3199847 : Blo 2131435 3199847 := bstep (se 1 (by rfl) ⟨2399885, by rfl⟩ : syracuseStep 3199847 = 4799771) B4799771
theorem B2133231 : Blo 2131435 2133231 := bstep (se 1 (by rfl) ⟨1599923, by rfl⟩ : syracuseStep 2133231 = 3199847) B3199847
theorem B3199853 : Blo 2131435 3199853 := bbase (se 3 (by rfl) ⟨599972, by rfl⟩ : syracuseStep 3199853 = 1199945) (by norm_num)
theorem B2133235 : Blo 2131435 2133235 := bstep (se 1 (by rfl) ⟨1599926, by rfl⟩ : syracuseStep 2133235 = 3199853) B3199853
theorem B4799789 : Blo 2131435 4799789 := bbase (se 3 (by rfl) ⟨899960, by rfl⟩ : syracuseStep 4799789 = 1799921) (by norm_num)
theorem B3199859 : Blo 2131435 3199859 := bstep (se 1 (by rfl) ⟨2399894, by rfl⟩ : syracuseStep 3199859 = 4799789) B4799789
theorem B2133239 : Blo 2131435 2133239 := bstep (se 1 (by rfl) ⟨1599929, by rfl⟩ : syracuseStep 2133239 = 3199859) B3199859
theorem B26302229 : Blo 2131435 26302229 := bbase (se 6 (by rfl) ⟨616458, by rfl⟩ : syracuseStep 26302229 = 1232917) (by norm_num)
theorem B17534819 : Blo 2131435 17534819 := bstep (se 1 (by rfl) ⟨13151114, by rfl⟩ : syracuseStep 17534819 = 26302229) B26302229
theorem B11689879 : Blo 2131435 11689879 := bstep (se 1 (by rfl) ⟨8767409, by rfl⟩ : syracuseStep 11689879 = 17534819) B17534819
theorem B15586505 : Blo 2131435 15586505 := bstep (se 2 (by rfl) ⟨5844939, by rfl⟩ : syracuseStep 15586505 = 11689879) B11689879
theorem B10391003 : Blo 2131435 10391003 := bstep (se 1 (by rfl) ⟨7793252, by rfl⟩ : syracuseStep 10391003 = 15586505) B15586505
theorem B6927335 : Blo 2131435 6927335 := bstep (se 1 (by rfl) ⟨5195501, by rfl⟩ : syracuseStep 6927335 = 10391003) B10391003
theorem B4618223 : Blo 2131435 4618223 := bstep (se 1 (by rfl) ⟨3463667, by rfl⟩ : syracuseStep 4618223 = 6927335) B6927335
theorem B3078815 : Blo 2131435 3078815 := bstep (se 1 (by rfl) ⟨2309111, by rfl⟩ : syracuseStep 3078815 = 4618223) B4618223
theorem B8210173 : Blo 2131435 8210173 := bstep (se 3 (by rfl) ⟨1539407, by rfl⟩ : syracuseStep 8210173 = 3078815) B3078815
theorem B10946897 : Blo 2131435 10946897 := bstep (se 2 (by rfl) ⟨4105086, by rfl⟩ : syracuseStep 10946897 = 8210173) B8210173
theorem B7297931 : Blo 2131435 7297931 := bstep (se 1 (by rfl) ⟨5473448, by rfl⟩ : syracuseStep 7297931 = 10946897) B10946897
theorem B4865287 : Blo 2131435 4865287 := bstep (se 1 (by rfl) ⟨3648965, by rfl⟩ : syracuseStep 4865287 = 7297931) B7297931
theorem B6487049 : Blo 2131435 6487049 := bstep (se 2 (by rfl) ⟨2432643, by rfl⟩ : syracuseStep 6487049 = 4865287) B4865287
theorem B4324699 : Blo 2131435 4324699 := bstep (se 1 (by rfl) ⟨3243524, by rfl⟩ : syracuseStep 4324699 = 6487049) B6487049
theorem B5766265 : Blo 2131435 5766265 := bstep (se 2 (by rfl) ⟨2162349, by rfl⟩ : syracuseStep 5766265 = 4324699) B4324699
theorem B7688353 : Blo 2131435 7688353 := bstep (se 2 (by rfl) ⟨2883132, by rfl⟩ : syracuseStep 7688353 = 5766265) B5766265
theorem B10251137 : Blo 2131435 10251137 := bstep (se 2 (by rfl) ⟨3844176, by rfl⟩ : syracuseStep 10251137 = 7688353) B7688353
theorem B6834091 : Blo 2131435 6834091 := bstep (se 1 (by rfl) ⟨5125568, by rfl⟩ : syracuseStep 6834091 = 10251137) B10251137
theorem B9112121 : Blo 2131435 9112121 := bstep (se 2 (by rfl) ⟨3417045, by rfl⟩ : syracuseStep 9112121 = 6834091) B6834091
theorem B6074747 : Blo 2131435 6074747 := bstep (se 1 (by rfl) ⟨4556060, by rfl⟩ : syracuseStep 6074747 = 9112121) B9112121
theorem B4049831 : Blo 2131435 4049831 := bstep (se 1 (by rfl) ⟨3037373, by rfl⟩ : syracuseStep 4049831 = 6074747) B6074747
theorem B2699887 : Blo 2131435 2699887 := bstep (se 1 (by rfl) ⟨2024915, by rfl⟩ : syracuseStep 2699887 = 4049831) B4049831
theorem B3599849 : Blo 2131435 3599849 := bstep (se 2 (by rfl) ⟨1349943, by rfl⟩ : syracuseStep 3599849 = 2699887) B2699887
theorem B2399899 : Blo 2131435 2399899 := bstep (se 1 (by rfl) ⟨1799924, by rfl⟩ : syracuseStep 2399899 = 3599849) B3599849
theorem B3199865 : Blo 2131435 3199865 := bstep (se 2 (by rfl) ⟨1199949, by rfl⟩ : syracuseStep 3199865 = 2399899) B2399899
theorem B2133243 : Blo 2131435 2133243 := bstep (se 1 (by rfl) ⟨1599932, by rfl⟩ : syracuseStep 2133243 = 3199865) B3199865
theorem B4105093 : Blo 2131435 4105093 := bbase (se 4 (by rfl) ⟨384852, by rfl⟩ : syracuseStep 4105093 = 769705) (by norm_num)
theorem B5473457 : Blo 2131435 5473457 := bstep (se 2 (by rfl) ⟨2052546, by rfl⟩ : syracuseStep 5473457 = 4105093) B4105093
theorem B3648971 : Blo 2131435 3648971 := bstep (se 1 (by rfl) ⟨2736728, by rfl⟩ : syracuseStep 3648971 = 5473457) B5473457
theorem B2432647 : Blo 2131435 2432647 := bstep (se 1 (by rfl) ⟨1824485, by rfl⟩ : syracuseStep 2432647 = 3648971) B3648971
theorem B3243529 : Blo 2131435 3243529 := bstep (se 2 (by rfl) ⟨1216323, by rfl⟩ : syracuseStep 3243529 = 2432647) B2432647
theorem B17298821 : Blo 2131435 17298821 := bstep (se 4 (by rfl) ⟨1621764, by rfl⟩ : syracuseStep 17298821 = 3243529) B3243529
theorem B11532547 : Blo 2131435 11532547 := bstep (se 1 (by rfl) ⟨8649410, by rfl⟩ : syracuseStep 11532547 = 17298821) B17298821
theorem B15376729 : Blo 2131435 15376729 := bstep (se 2 (by rfl) ⟨5766273, by rfl⟩ : syracuseStep 15376729 = 11532547) B11532547
theorem B20502305 : Blo 2131435 20502305 := bstep (se 2 (by rfl) ⟨7688364, by rfl⟩ : syracuseStep 20502305 = 15376729) B15376729
theorem B13668203 : Blo 2131435 13668203 := bstep (se 1 (by rfl) ⟨10251152, by rfl⟩ : syracuseStep 13668203 = 20502305) B20502305
theorem B36448541 : Blo 2131435 36448541 := bstep (se 3 (by rfl) ⟨6834101, by rfl⟩ : syracuseStep 36448541 = 13668203) B13668203
theorem B24299027 : Blo 2131435 24299027 := bstep (se 1 (by rfl) ⟨18224270, by rfl⟩ : syracuseStep 24299027 = 36448541) B36448541
theorem B16199351 : Blo 2131435 16199351 := bstep (se 1 (by rfl) ⟨12149513, by rfl⟩ : syracuseStep 16199351 = 24299027) B24299027
theorem B10799567 : Blo 2131435 10799567 := bstep (se 1 (by rfl) ⟨8099675, by rfl⟩ : syracuseStep 10799567 = 16199351) B16199351
theorem B7199711 : Blo 2131435 7199711 := bstep (se 1 (by rfl) ⟨5399783, by rfl⟩ : syracuseStep 7199711 = 10799567) B10799567
theorem B4799807 : Blo 2131435 4799807 := bstep (se 1 (by rfl) ⟨3599855, by rfl⟩ : syracuseStep 4799807 = 7199711) B7199711
theorem B3199871 : Blo 2131435 3199871 := bstep (se 1 (by rfl) ⟨2399903, by rfl⟩ : syracuseStep 3199871 = 4799807) B4799807
theorem B2133247 : Blo 2131435 2133247 := bstep (se 1 (by rfl) ⟨1599935, by rfl⟩ : syracuseStep 2133247 = 3199871) B3199871
theorem B3199877 : Blo 2131435 3199877 := bbase (se 4 (by rfl) ⟨299988, by rfl⟩ : syracuseStep 3199877 = 599977) (by norm_num)
theorem B2133251 : Blo 2131435 2133251 := bstep (se 1 (by rfl) ⟨1599938, by rfl⟩ : syracuseStep 2133251 = 3199877) B3199877
theorem B3599869 : Blo 2131435 3599869 := bbase (se 3 (by rfl) ⟨674975, by rfl⟩ : syracuseStep 3599869 = 1349951) (by norm_num)
theorem B4799825 : Blo 2131435 4799825 := bstep (se 2 (by rfl) ⟨1799934, by rfl⟩ : syracuseStep 4799825 = 3599869) B3599869
theorem B3199883 : Blo 2131435 3199883 := bstep (se 1 (by rfl) ⟨2399912, by rfl⟩ : syracuseStep 3199883 = 4799825) B4799825
theorem B2133255 : Blo 2131435 2133255 := bstep (se 1 (by rfl) ⟨1599941, by rfl⟩ : syracuseStep 2133255 = 3199883) B3199883
theorem B2399917 : Blo 2131435 2399917 := bbase (se 3 (by rfl) ⟨449984, by rfl⟩ : syracuseStep 2399917 = 899969) (by norm_num)
theorem B3199889 : Blo 2131435 3199889 := bstep (se 2 (by rfl) ⟨1199958, by rfl⟩ : syracuseStep 3199889 = 2399917) B2399917
theorem B2133259 : Blo 2131435 2133259 := bstep (se 1 (by rfl) ⟨1599944, by rfl⟩ : syracuseStep 2133259 = 3199889) B3199889
theorem B7199765 : Blo 2131435 7199765 := bbase (se 6 (by rfl) ⟨168744, by rfl⟩ : syracuseStep 7199765 = 337489) (by norm_num)
theorem B4799843 : Blo 2131435 4799843 := bstep (se 1 (by rfl) ⟨3599882, by rfl⟩ : syracuseStep 4799843 = 7199765) B7199765
theorem B3199895 : Blo 2131435 3199895 := bstep (se 1 (by rfl) ⟨2399921, by rfl⟩ : syracuseStep 3199895 = 4799843) B4799843
theorem B2133263 : Blo 2131435 2133263 := bstep (se 1 (by rfl) ⟨1599947, by rfl⟩ : syracuseStep 2133263 = 3199895) B3199895
theorem B3199901 : Blo 2131435 3199901 := bbase (se 3 (by rfl) ⟨599981, by rfl⟩ : syracuseStep 3199901 = 1199963) (by norm_num)
theorem B2133267 : Blo 2131435 2133267 := bstep (se 1 (by rfl) ⟨1599950, by rfl⟩ : syracuseStep 2133267 = 3199901) B3199901
theorem B4799861 : Blo 2131435 4799861 := bbase (se 5 (by rfl) ⟨224993, by rfl⟩ : syracuseStep 4799861 = 449987) (by norm_num)
theorem B3199907 : Blo 2131435 3199907 := bstep (se 1 (by rfl) ⟨2399930, by rfl⟩ : syracuseStep 3199907 = 4799861) B4799861
theorem B2133271 : Blo 2131435 2133271 := bstep (se 1 (by rfl) ⟨1599953, by rfl⟩ : syracuseStep 2133271 = 3199907) B3199907
theorem B2597789 : Blo 2131435 2597789 := bbase (se 3 (by rfl) ⟨487085, by rfl⟩ : syracuseStep 2597789 = 974171) (by norm_num)
theorem B6927437 : Blo 2131435 6927437 := bstep (se 3 (by rfl) ⟨1298894, by rfl⟩ : syracuseStep 6927437 = 2597789) B2597789
theorem B4618291 : Blo 2131435 4618291 := bstep (se 1 (by rfl) ⟨3463718, by rfl⟩ : syracuseStep 4618291 = 6927437) B6927437
theorem B6157721 : Blo 2131435 6157721 := bstep (se 2 (by rfl) ⟨2309145, by rfl⟩ : syracuseStep 6157721 = 4618291) B4618291
theorem B16420589 : Blo 2131435 16420589 := bstep (se 3 (by rfl) ⟨3078860, by rfl⟩ : syracuseStep 16420589 = 6157721) B6157721
theorem B10947059 : Blo 2131435 10947059 := bstep (se 1 (by rfl) ⟨8210294, by rfl⟩ : syracuseStep 10947059 = 16420589) B16420589
theorem B7298039 : Blo 2131435 7298039 := bstep (se 1 (by rfl) ⟨5473529, by rfl⟩ : syracuseStep 7298039 = 10947059) B10947059
theorem B4865359 : Blo 2131435 4865359 := bstep (se 1 (by rfl) ⟨3649019, by rfl⟩ : syracuseStep 4865359 = 7298039) B7298039
theorem B6487145 : Blo 2131435 6487145 := bstep (se 2 (by rfl) ⟨2432679, by rfl⟩ : syracuseStep 6487145 = 4865359) B4865359
theorem B4324763 : Blo 2131435 4324763 := bstep (se 1 (by rfl) ⟨3243572, by rfl⟩ : syracuseStep 4324763 = 6487145) B6487145
theorem B11532701 : Blo 2131435 11532701 := bstep (se 3 (by rfl) ⟨2162381, by rfl⟩ : syracuseStep 11532701 = 4324763) B4324763
theorem B7688467 : Blo 2131435 7688467 := bstep (se 1 (by rfl) ⟨5766350, by rfl⟩ : syracuseStep 7688467 = 11532701) B11532701
theorem B10251289 : Blo 2131435 10251289 := bstep (se 2 (by rfl) ⟨3844233, by rfl⟩ : syracuseStep 10251289 = 7688467) B7688467
theorem B13668385 : Blo 2131435 13668385 := bstep (se 2 (by rfl) ⟨5125644, by rfl⟩ : syracuseStep 13668385 = 10251289) B10251289
theorem B18224513 : Blo 2131435 18224513 := bstep (se 2 (by rfl) ⟨6834192, by rfl⟩ : syracuseStep 18224513 = 13668385) B13668385
theorem B12149675 : Blo 2131435 12149675 := bstep (se 1 (by rfl) ⟨9112256, by rfl⟩ : syracuseStep 12149675 = 18224513) B18224513
theorem B8099783 : Blo 2131435 8099783 := bstep (se 1 (by rfl) ⟨6074837, by rfl⟩ : syracuseStep 8099783 = 12149675) B12149675
theorem B5399855 : Blo 2131435 5399855 := bstep (se 1 (by rfl) ⟨4049891, by rfl⟩ : syracuseStep 5399855 = 8099783) B8099783
theorem B3599903 : Blo 2131435 3599903 := bstep (se 1 (by rfl) ⟨2699927, by rfl⟩ : syracuseStep 3599903 = 5399855) B5399855
theorem B2399935 : Blo 2131435 2399935 := bstep (se 1 (by rfl) ⟨1799951, by rfl⟩ : syracuseStep 2399935 = 3599903) B3599903
theorem B3199913 : Blo 2131435 3199913 := bstep (se 2 (by rfl) ⟨1199967, by rfl⟩ : syracuseStep 3199913 = 2399935) B2399935
theorem B2133275 : Blo 2131435 2133275 := bstep (se 1 (by rfl) ⟨1599956, by rfl⟩ : syracuseStep 2133275 = 3199913) B3199913
theorem B8099797 : Blo 2131435 8099797 := bbase (se 7 (by rfl) ⟨94919, by rfl⟩ : syracuseStep 8099797 = 189839) (by norm_num)
theorem B10799729 : Blo 2131435 10799729 := bstep (se 2 (by rfl) ⟨4049898, by rfl⟩ : syracuseStep 10799729 = 8099797) B8099797
theorem B7199819 : Blo 2131435 7199819 := bstep (se 1 (by rfl) ⟨5399864, by rfl⟩ : syracuseStep 7199819 = 10799729) B10799729
theorem B4799879 : Blo 2131435 4799879 := bstep (se 1 (by rfl) ⟨3599909, by rfl⟩ : syracuseStep 4799879 = 7199819) B7199819
theorem B3199919 : Blo 2131435 3199919 := bstep (se 1 (by rfl) ⟨2399939, by rfl⟩ : syracuseStep 3199919 = 4799879) B4799879
theorem B2133279 : Blo 2131435 2133279 := bstep (se 1 (by rfl) ⟨1599959, by rfl⟩ : syracuseStep 2133279 = 3199919) B3199919
theorem B3199925 : Blo 2131435 3199925 := bbase (se 5 (by rfl) ⟨149996, by rfl⟩ : syracuseStep 3199925 = 299993) (by norm_num)
theorem B2133283 : Blo 2131435 2133283 := bstep (se 1 (by rfl) ⟨1599962, by rfl⟩ : syracuseStep 2133283 = 3199925) B3199925
theorem B5399885 : Blo 2131435 5399885 := bbase (se 3 (by rfl) ⟨1012478, by rfl⟩ : syracuseStep 5399885 = 2024957) (by norm_num)
theorem B3599923 : Blo 2131435 3599923 := bstep (se 1 (by rfl) ⟨2699942, by rfl⟩ : syracuseStep 3599923 = 5399885) B5399885
theorem B4799897 : Blo 2131435 4799897 := bstep (se 2 (by rfl) ⟨1799961, by rfl⟩ : syracuseStep 4799897 = 3599923) B3599923
theorem B3199931 : Blo 2131435 3199931 := bstep (se 1 (by rfl) ⟨2399948, by rfl⟩ : syracuseStep 3199931 = 4799897) B4799897
theorem B2133287 : Blo 2131435 2133287 := bstep (se 1 (by rfl) ⟨1599965, by rfl⟩ : syracuseStep 2133287 = 3199931) B3199931
theorem B2399953 : Blo 2131435 2399953 := bbase (se 2 (by rfl) ⟨899982, by rfl⟩ : syracuseStep 2399953 = 1799965) (by norm_num)
theorem B3199937 : Blo 2131435 3199937 := bstep (se 2 (by rfl) ⟨1199976, by rfl⟩ : syracuseStep 3199937 = 2399953) B2399953
theorem B2133291 : Blo 2131435 2133291 := bstep (se 1 (by rfl) ⟨1599968, by rfl⟩ : syracuseStep 2133291 = 3199937) B3199937
theorem B5125693 : Blo 2131435 5125693 := bbase (se 3 (by rfl) ⟨961067, by rfl⟩ : syracuseStep 5125693 = 1922135) (by norm_num)
theorem B6834257 : Blo 2131435 6834257 := bstep (se 2 (by rfl) ⟨2562846, by rfl⟩ : syracuseStep 6834257 = 5125693) B5125693
theorem B4556171 : Blo 2131435 4556171 := bstep (se 1 (by rfl) ⟨3417128, by rfl⟩ : syracuseStep 4556171 = 6834257) B6834257
theorem B3037447 : Blo 2131435 3037447 := bstep (se 1 (by rfl) ⟨2278085, by rfl⟩ : syracuseStep 3037447 = 4556171) B4556171
theorem B4049929 : Blo 2131435 4049929 := bstep (se 2 (by rfl) ⟨1518723, by rfl⟩ : syracuseStep 4049929 = 3037447) B3037447
theorem B5399905 : Blo 2131435 5399905 := bstep (se 2 (by rfl) ⟨2024964, by rfl⟩ : syracuseStep 5399905 = 4049929) B4049929
theorem B7199873 : Blo 2131435 7199873 := bstep (se 2 (by rfl) ⟨2699952, by rfl⟩ : syracuseStep 7199873 = 5399905) B5399905
theorem B4799915 : Blo 2131435 4799915 := bstep (se 1 (by rfl) ⟨3599936, by rfl⟩ : syracuseStep 4799915 = 7199873) B7199873
theorem B3199943 : Blo 2131435 3199943 := bstep (se 1 (by rfl) ⟨2399957, by rfl⟩ : syracuseStep 3199943 = 4799915) B4799915
theorem B2133295 : Blo 2131435 2133295 := bstep (se 1 (by rfl) ⟨1599971, by rfl⟩ : syracuseStep 2133295 = 3199943) B3199943
theorem B3199949 : Blo 2131435 3199949 := bbase (se 3 (by rfl) ⟨599990, by rfl⟩ : syracuseStep 3199949 = 1199981) (by norm_num)
theorem B2133299 : Blo 2131435 2133299 := bstep (se 1 (by rfl) ⟨1599974, by rfl⟩ : syracuseStep 2133299 = 3199949) B3199949
theorem B4799933 : Blo 2131435 4799933 := bbase (se 3 (by rfl) ⟨899987, by rfl⟩ : syracuseStep 4799933 = 1799975) (by norm_num)
theorem B3199955 : Blo 2131435 3199955 := bstep (se 1 (by rfl) ⟨2399966, by rfl⟩ : syracuseStep 3199955 = 4799933) B4799933
theorem B2133303 : Blo 2131435 2133303 := bstep (se 1 (by rfl) ⟨1599977, by rfl⟩ : syracuseStep 2133303 = 3199955) B3199955
theorem B3599957 : Blo 2131435 3599957 := bbase (se 8 (by rfl) ⟨21093, by rfl⟩ : syracuseStep 3599957 = 42187) (by norm_num)
theorem B2399971 : Blo 2131435 2399971 := bstep (se 1 (by rfl) ⟨1799978, by rfl⟩ : syracuseStep 2399971 = 3599957) B3599957
theorem B3199961 : Blo 2131435 3199961 := bstep (se 2 (by rfl) ⟨1199985, by rfl⟩ : syracuseStep 3199961 = 2399971) B2399971
theorem B2133307 : Blo 2131435 2133307 := bstep (se 1 (by rfl) ⟨1599980, by rfl⟩ : syracuseStep 2133307 = 3199961) B3199961
theorem B10251461 : Blo 2131435 10251461 := bbase (se 4 (by rfl) ⟨961074, by rfl⟩ : syracuseStep 10251461 = 1922149) (by norm_num)
theorem B6834307 : Blo 2131435 6834307 := bstep (se 1 (by rfl) ⟨5125730, by rfl⟩ : syracuseStep 6834307 = 10251461) B10251461
theorem B9112409 : Blo 2131435 9112409 := bstep (se 2 (by rfl) ⟨3417153, by rfl⟩ : syracuseStep 9112409 = 6834307) B6834307
theorem B6074939 : Blo 2131435 6074939 := bstep (se 1 (by rfl) ⟨4556204, by rfl⟩ : syracuseStep 6074939 = 9112409) B9112409
theorem B16199837 : Blo 2131435 16199837 := bstep (se 3 (by rfl) ⟨3037469, by rfl⟩ : syracuseStep 16199837 = 6074939) B6074939
theorem B10799891 : Blo 2131435 10799891 := bstep (se 1 (by rfl) ⟨8099918, by rfl⟩ : syracuseStep 10799891 = 16199837) B16199837
theorem B7199927 : Blo 2131435 7199927 := bstep (se 1 (by rfl) ⟨5399945, by rfl⟩ : syracuseStep 7199927 = 10799891) B10799891
theorem B4799951 : Blo 2131435 4799951 := bstep (se 1 (by rfl) ⟨3599963, by rfl⟩ : syracuseStep 4799951 = 7199927) B7199927
theorem B3199967 : Blo 2131435 3199967 := bstep (se 1 (by rfl) ⟨2399975, by rfl⟩ : syracuseStep 3199967 = 4799951) B4799951
theorem B2133311 : Blo 2131435 2133311 := bstep (se 1 (by rfl) ⟨1599983, by rfl⟩ : syracuseStep 2133311 = 3199967) B3199967
theorem B3199973 : Blo 2131435 3199973 := bbase (se 4 (by rfl) ⟨299997, by rfl⟩ : syracuseStep 3199973 = 599995) (by norm_num)
theorem B2133315 : Blo 2131435 2133315 := bstep (se 1 (by rfl) ⟨1599986, by rfl⟩ : syracuseStep 2133315 = 3199973) B3199973
theorem B4324853 : Blo 2131435 4324853 := bbase (se 5 (by rfl) ⟨202727, by rfl⟩ : syracuseStep 4324853 = 405455) (by norm_num)
theorem B11532941 : Blo 2131435 11532941 := bstep (se 3 (by rfl) ⟨2162426, by rfl⟩ : syracuseStep 11532941 = 4324853) B4324853
theorem B7688627 : Blo 2131435 7688627 := bstep (se 1 (by rfl) ⟨5766470, by rfl⟩ : syracuseStep 7688627 = 11532941) B11532941
theorem B5125751 : Blo 2131435 5125751 := bstep (se 1 (by rfl) ⟨3844313, by rfl⟩ : syracuseStep 5125751 = 7688627) B7688627
theorem B3417167 : Blo 2131435 3417167 := bstep (se 1 (by rfl) ⟨2562875, by rfl⟩ : syracuseStep 3417167 = 5125751) B5125751
theorem B9112445 : Blo 2131435 9112445 := bstep (se 3 (by rfl) ⟨1708583, by rfl⟩ : syracuseStep 9112445 = 3417167) B3417167
theorem B6074963 : Blo 2131435 6074963 := bstep (se 1 (by rfl) ⟨4556222, by rfl⟩ : syracuseStep 6074963 = 9112445) B9112445
theorem B4049975 : Blo 2131435 4049975 := bstep (se 1 (by rfl) ⟨3037481, by rfl⟩ : syracuseStep 4049975 = 6074963) B6074963
theorem B2699983 : Blo 2131435 2699983 := bstep (se 1 (by rfl) ⟨2024987, by rfl⟩ : syracuseStep 2699983 = 4049975) B4049975
theorem B3599977 : Blo 2131435 3599977 := bstep (se 2 (by rfl) ⟨1349991, by rfl⟩ : syracuseStep 3599977 = 2699983) B2699983
theorem B4799969 : Blo 2131435 4799969 := bstep (se 2 (by rfl) ⟨1799988, by rfl⟩ : syracuseStep 4799969 = 3599977) B3599977
theorem B3199979 : Blo 2131435 3199979 := bstep (se 1 (by rfl) ⟨2399984, by rfl⟩ : syracuseStep 3199979 = 4799969) B4799969
theorem B2133319 : Blo 2131435 2133319 := bstep (se 1 (by rfl) ⟨1599989, by rfl⟩ : syracuseStep 2133319 = 3199979) B3199979
theorem B2399989 : Blo 2131435 2399989 := bbase (se 5 (by rfl) ⟨112499, by rfl⟩ : syracuseStep 2399989 = 224999) (by norm_num)
theorem B3199985 : Blo 2131435 3199985 := bstep (se 2 (by rfl) ⟨1199994, by rfl⟩ : syracuseStep 3199985 = 2399989) B2399989
theorem B2133323 : Blo 2131435 2133323 := bstep (se 1 (by rfl) ⟨1599992, by rfl⟩ : syracuseStep 2133323 = 3199985) B3199985
theorem B2699993 : Blo 2131435 2699993 := bbase (se 2 (by rfl) ⟨1012497, by rfl⟩ : syracuseStep 2699993 = 2024995) (by norm_num)
theorem B7199981 : Blo 2131435 7199981 := bstep (se 3 (by rfl) ⟨1349996, by rfl⟩ : syracuseStep 7199981 = 2699993) B2699993
theorem B4799987 : Blo 2131435 4799987 := bstep (se 1 (by rfl) ⟨3599990, by rfl⟩ : syracuseStep 4799987 = 7199981) B7199981
theorem B3199991 : Blo 2131435 3199991 := bstep (se 1 (by rfl) ⟨2399993, by rfl⟩ : syracuseStep 3199991 = 4799987) B4799987
theorem B2133327 : Blo 2131435 2133327 := bstep (se 1 (by rfl) ⟨1599995, by rfl⟩ : syracuseStep 2133327 = 3199991) B3199991
theorem B3199997 : Blo 2131435 3199997 := bbase (se 3 (by rfl) ⟨599999, by rfl⟩ : syracuseStep 3199997 = 1199999) (by norm_num)
theorem B2133331 : Blo 2131435 2133331 := bstep (se 1 (by rfl) ⟨1599998, by rfl⟩ : syracuseStep 2133331 = 3199997) B3199997
theorem B4800005 : Blo 2131435 4800005 := bbase (se 4 (by rfl) ⟨450000, by rfl⟩ : syracuseStep 4800005 = 900001) (by norm_num)
theorem B3200003 : Blo 2131435 3200003 := bstep (se 1 (by rfl) ⟨2400002, by rfl⟩ : syracuseStep 3200003 = 4800005) B4800005
theorem B2133335 : Blo 2131435 2133335 := bstep (se 1 (by rfl) ⟨1600001, by rfl⟩ : syracuseStep 2133335 = 3200003) B3200003
theorem B4050013 : Blo 2131435 4050013 := bbase (se 3 (by rfl) ⟨759377, by rfl⟩ : syracuseStep 4050013 = 1518755) (by norm_num)
theorem B5400017 : Blo 2131435 5400017 := bstep (se 2 (by rfl) ⟨2025006, by rfl⟩ : syracuseStep 5400017 = 4050013) B4050013
theorem B3600011 : Blo 2131435 3600011 := bstep (se 1 (by rfl) ⟨2700008, by rfl⟩ : syracuseStep 3600011 = 5400017) B5400017
theorem B2400007 : Blo 2131435 2400007 := bstep (se 1 (by rfl) ⟨1800005, by rfl⟩ : syracuseStep 2400007 = 3600011) B3600011
theorem B3200009 : Blo 2131435 3200009 := bstep (se 2 (by rfl) ⟨1200003, by rfl⟩ : syracuseStep 3200009 = 2400007) B2400007
theorem B2133339 : Blo 2131435 2133339 := bstep (se 1 (by rfl) ⟨1600004, by rfl⟩ : syracuseStep 2133339 = 3200009) B3200009
theorem B10800053 : Blo 2131435 10800053 := bbase (se 5 (by rfl) ⟨506252, by rfl⟩ : syracuseStep 10800053 = 1012505) (by norm_num)
theorem B7200035 : Blo 2131435 7200035 := bstep (se 1 (by rfl) ⟨5400026, by rfl⟩ : syracuseStep 7200035 = 10800053) B10800053
theorem B4800023 : Blo 2131435 4800023 := bstep (se 1 (by rfl) ⟨3600017, by rfl⟩ : syracuseStep 4800023 = 7200035) B7200035
theorem B3200015 : Blo 2131435 3200015 := bstep (se 1 (by rfl) ⟨2400011, by rfl⟩ : syracuseStep 3200015 = 4800023) B4800023
theorem B2133343 : Blo 2131435 2133343 := bstep (se 1 (by rfl) ⟨1600007, by rfl⟩ : syracuseStep 2133343 = 3200015) B3200015
theorem B3200021 : Blo 2131435 3200021 := bbase (se 6 (by rfl) ⟨75000, by rfl⟩ : syracuseStep 3200021 = 150001) (by norm_num)
theorem B2133347 : Blo 2131435 2133347 := bstep (se 1 (by rfl) ⟨1600010, by rfl⟩ : syracuseStep 2133347 = 3200021) B3200021
theorem B2597881 : Blo 2131435 2597881 := bbase (se 2 (by rfl) ⟨974205, by rfl⟩ : syracuseStep 2597881 = 1948411) (by norm_num)
theorem B3463841 : Blo 2131435 3463841 := bstep (se 2 (by rfl) ⟨1298940, by rfl⟩ : syracuseStep 3463841 = 2597881) B2597881
theorem B9236909 : Blo 2131435 9236909 := bstep (se 3 (by rfl) ⟨1731920, by rfl⟩ : syracuseStep 9236909 = 3463841) B3463841
theorem B6157939 : Blo 2131435 6157939 := bstep (se 1 (by rfl) ⟨4618454, by rfl⟩ : syracuseStep 6157939 = 9236909) B9236909
theorem B8210585 : Blo 2131435 8210585 := bstep (se 2 (by rfl) ⟨3078969, by rfl⟩ : syracuseStep 8210585 = 6157939) B6157939
theorem B21894893 : Blo 2131435 21894893 := bstep (se 3 (by rfl) ⟨4105292, by rfl⟩ : syracuseStep 21894893 = 8210585) B8210585
theorem B14596595 : Blo 2131435 14596595 := bstep (se 1 (by rfl) ⟨10947446, by rfl⟩ : syracuseStep 14596595 = 21894893) B21894893
theorem B9731063 : Blo 2131435 9731063 := bstep (se 1 (by rfl) ⟨7298297, by rfl⟩ : syracuseStep 9731063 = 14596595) B14596595
theorem B6487375 : Blo 2131435 6487375 := bstep (se 1 (by rfl) ⟨4865531, by rfl⟩ : syracuseStep 6487375 = 9731063) B9731063
theorem B8649833 : Blo 2131435 8649833 := bstep (se 2 (by rfl) ⟨3243687, by rfl⟩ : syracuseStep 8649833 = 6487375) B6487375
theorem B23066221 : Blo 2131435 23066221 := bstep (se 3 (by rfl) ⟨4324916, by rfl⟩ : syracuseStep 23066221 = 8649833) B8649833
theorem B30754961 : Blo 2131435 30754961 := bstep (se 2 (by rfl) ⟨11533110, by rfl⟩ : syracuseStep 30754961 = 23066221) B23066221
theorem B20503307 : Blo 2131435 20503307 := bstep (se 1 (by rfl) ⟨15377480, by rfl⟩ : syracuseStep 20503307 = 30754961) B30754961
theorem B13668871 : Blo 2131435 13668871 := bstep (se 1 (by rfl) ⟨10251653, by rfl⟩ : syracuseStep 13668871 = 20503307) B20503307
theorem B18225161 : Blo 2131435 18225161 := bstep (se 2 (by rfl) ⟨6834435, by rfl⟩ : syracuseStep 18225161 = 13668871) B13668871
theorem B12150107 : Blo 2131435 12150107 := bstep (se 1 (by rfl) ⟨9112580, by rfl⟩ : syracuseStep 12150107 = 18225161) B18225161
theorem B8100071 : Blo 2131435 8100071 := bstep (se 1 (by rfl) ⟨6075053, by rfl⟩ : syracuseStep 8100071 = 12150107) B12150107
theorem B5400047 : Blo 2131435 5400047 := bstep (se 1 (by rfl) ⟨4050035, by rfl⟩ : syracuseStep 5400047 = 8100071) B8100071
theorem B3600031 : Blo 2131435 3600031 := bstep (se 1 (by rfl) ⟨2700023, by rfl⟩ : syracuseStep 3600031 = 5400047) B5400047
theorem B4800041 : Blo 2131435 4800041 := bstep (se 2 (by rfl) ⟨1800015, by rfl⟩ : syracuseStep 4800041 = 3600031) B3600031
theorem B3200027 : Blo 2131435 3200027 := bstep (se 1 (by rfl) ⟨2400020, by rfl⟩ : syracuseStep 3200027 = 4800041) B4800041
theorem B2133351 : Blo 2131435 2133351 := bstep (se 1 (by rfl) ⟨1600013, by rfl⟩ : syracuseStep 2133351 = 3200027) B3200027
theorem B2400025 : Blo 2131435 2400025 := bbase (se 2 (by rfl) ⟨900009, by rfl⟩ : syracuseStep 2400025 = 1800019) (by norm_num)
theorem B3200033 : Blo 2131435 3200033 := bstep (se 2 (by rfl) ⟨1200012, by rfl⟩ : syracuseStep 3200033 = 2400025) B2400025
theorem B2133355 : Blo 2131435 2133355 := bstep (se 1 (by rfl) ⟨1600016, by rfl⟩ : syracuseStep 2133355 = 3200033) B3200033
theorem B8100101 : Blo 2131435 8100101 := bbase (se 4 (by rfl) ⟨759384, by rfl⟩ : syracuseStep 8100101 = 1518769) (by norm_num)
theorem B5400067 : Blo 2131435 5400067 := bstep (se 1 (by rfl) ⟨4050050, by rfl⟩ : syracuseStep 5400067 = 8100101) B8100101
theorem B7200089 : Blo 2131435 7200089 := bstep (se 2 (by rfl) ⟨2700033, by rfl⟩ : syracuseStep 7200089 = 5400067) B5400067
theorem B4800059 : Blo 2131435 4800059 := bstep (se 1 (by rfl) ⟨3600044, by rfl⟩ : syracuseStep 4800059 = 7200089) B7200089
theorem B3200039 : Blo 2131435 3200039 := bstep (se 1 (by rfl) ⟨2400029, by rfl⟩ : syracuseStep 3200039 = 4800059) B4800059
theorem B2133359 : Blo 2131435 2133359 := bstep (se 1 (by rfl) ⟨1600019, by rfl⟩ : syracuseStep 2133359 = 3200039) B3200039
theorem B3200045 : Blo 2131435 3200045 := bbase (se 3 (by rfl) ⟨600008, by rfl⟩ : syracuseStep 3200045 = 1200017) (by norm_num)
theorem B2133363 : Blo 2131435 2133363 := bstep (se 1 (by rfl) ⟨1600022, by rfl⟩ : syracuseStep 2133363 = 3200045) B3200045
theorem B4800077 : Blo 2131435 4800077 := bbase (se 3 (by rfl) ⟨900014, by rfl⟩ : syracuseStep 4800077 = 1800029) (by norm_num)
theorem B3200051 : Blo 2131435 3200051 := bstep (se 1 (by rfl) ⟨2400038, by rfl⟩ : syracuseStep 3200051 = 4800077) B4800077
theorem B2133367 : Blo 2131435 2133367 := bstep (se 1 (by rfl) ⟨1600025, by rfl⟩ : syracuseStep 2133367 = 3200051) B3200051
theorem B2700049 : Blo 2131435 2700049 := bbase (se 2 (by rfl) ⟨1012518, by rfl⟩ : syracuseStep 2700049 = 2025037) (by norm_num)
theorem B3600065 : Blo 2131435 3600065 := bstep (se 2 (by rfl) ⟨1350024, by rfl⟩ : syracuseStep 3600065 = 2700049) B2700049
theorem B2400043 : Blo 2131435 2400043 := bstep (se 1 (by rfl) ⟨1800032, by rfl⟩ : syracuseStep 2400043 = 3600065) B3600065
theorem B3200057 : Blo 2131435 3200057 := bstep (se 2 (by rfl) ⟨1200021, by rfl⟩ : syracuseStep 3200057 = 2400043) B2400043
theorem B2133371 : Blo 2131435 2133371 := bstep (se 1 (by rfl) ⟨1600028, by rfl⟩ : syracuseStep 2133371 = 3200057) B3200057
theorem B4556341 : Blo 2131435 4556341 := bbase (se 5 (by rfl) ⟨213578, by rfl⟩ : syracuseStep 4556341 = 427157) (by norm_num)
theorem B24300485 : Blo 2131435 24300485 := bstep (se 4 (by rfl) ⟨2278170, by rfl⟩ : syracuseStep 24300485 = 4556341) B4556341
theorem B16200323 : Blo 2131435 16200323 := bstep (se 1 (by rfl) ⟨12150242, by rfl⟩ : syracuseStep 16200323 = 24300485) B24300485
theorem B10800215 : Blo 2131435 10800215 := bstep (se 1 (by rfl) ⟨8100161, by rfl⟩ : syracuseStep 10800215 = 16200323) B16200323
theorem B7200143 : Blo 2131435 7200143 := bstep (se 1 (by rfl) ⟨5400107, by rfl⟩ : syracuseStep 7200143 = 10800215) B10800215
theorem B4800095 : Blo 2131435 4800095 := bstep (se 1 (by rfl) ⟨3600071, by rfl⟩ : syracuseStep 4800095 = 7200143) B7200143
theorem B3200063 : Blo 2131435 3200063 := bstep (se 1 (by rfl) ⟨2400047, by rfl⟩ : syracuseStep 3200063 = 4800095) B4800095
theorem B2133375 : Blo 2131435 2133375 := bstep (se 1 (by rfl) ⟨1600031, by rfl⟩ : syracuseStep 2133375 = 3200063) B3200063
theorem B3200069 : Blo 2131435 3200069 := bbase (se 4 (by rfl) ⟨300006, by rfl⟩ : syracuseStep 3200069 = 600013) (by norm_num)
theorem B2133379 : Blo 2131435 2133379 := bstep (se 1 (by rfl) ⟨1600034, by rfl⟩ : syracuseStep 2133379 = 3200069) B3200069
theorem B3600085 : Blo 2131435 3600085 := bbase (se 7 (by rfl) ⟨42188, by rfl⟩ : syracuseStep 3600085 = 84377) (by norm_num)
theorem B4800113 : Blo 2131435 4800113 := bstep (se 2 (by rfl) ⟨1800042, by rfl⟩ : syracuseStep 4800113 = 3600085) B3600085
theorem B3200075 : Blo 2131435 3200075 := bstep (se 1 (by rfl) ⟨2400056, by rfl⟩ : syracuseStep 3200075 = 4800113) B4800113
theorem B2133383 : Blo 2131435 2133383 := bstep (se 1 (by rfl) ⟨1600037, by rfl⟩ : syracuseStep 2133383 = 3200075) B3200075
theorem B2400061 : Blo 2131435 2400061 := bbase (se 3 (by rfl) ⟨450011, by rfl⟩ : syracuseStep 2400061 = 900023) (by norm_num)
theorem B3200081 : Blo 2131435 3200081 := bstep (se 2 (by rfl) ⟨1200030, by rfl⟩ : syracuseStep 3200081 = 2400061) B2400061
theorem B2133387 : Blo 2131435 2133387 := bstep (se 1 (by rfl) ⟨1600040, by rfl⟩ : syracuseStep 2133387 = 3200081) B3200081
theorem B7200197 : Blo 2131435 7200197 := bbase (se 4 (by rfl) ⟨675018, by rfl⟩ : syracuseStep 7200197 = 1350037) (by norm_num)
theorem B4800131 : Blo 2131435 4800131 := bstep (se 1 (by rfl) ⟨3600098, by rfl⟩ : syracuseStep 4800131 = 7200197) B7200197
theorem B3200087 : Blo 2131435 3200087 := bstep (se 1 (by rfl) ⟨2400065, by rfl⟩ : syracuseStep 3200087 = 4800131) B4800131
theorem B2133391 : Blo 2131435 2133391 := bstep (se 1 (by rfl) ⟨1600043, by rfl⟩ : syracuseStep 2133391 = 3200087) B3200087
theorem B3200093 : Blo 2131435 3200093 := bbase (se 3 (by rfl) ⟨600017, by rfl⟩ : syracuseStep 3200093 = 1200035) (by norm_num)
theorem B2133395 : Blo 2131435 2133395 := bstep (se 1 (by rfl) ⟨1600046, by rfl⟩ : syracuseStep 2133395 = 3200093) B3200093
theorem B4800149 : Blo 2131435 4800149 := bbase (se 6 (by rfl) ⟨112503, by rfl⟩ : syracuseStep 4800149 = 225007) (by norm_num)
theorem B3200099 : Blo 2131435 3200099 := bstep (se 1 (by rfl) ⟨2400074, by rfl⟩ : syracuseStep 3200099 = 4800149) B4800149
theorem B2133399 : Blo 2131435 2133399 := bstep (se 1 (by rfl) ⟨1600049, by rfl⟩ : syracuseStep 2133399 = 3200099) B3200099
theorem B2278201 : Blo 2131435 2278201 := bbase (se 2 (by rfl) ⟨854325, by rfl⟩ : syracuseStep 2278201 = 1708651) (by norm_num)
theorem B3037601 : Blo 2131435 3037601 := bstep (se 2 (by rfl) ⟨1139100, by rfl⟩ : syracuseStep 3037601 = 2278201) B2278201
theorem B8100269 : Blo 2131435 8100269 := bstep (se 3 (by rfl) ⟨1518800, by rfl⟩ : syracuseStep 8100269 = 3037601) B3037601
theorem B5400179 : Blo 2131435 5400179 := bstep (se 1 (by rfl) ⟨4050134, by rfl⟩ : syracuseStep 5400179 = 8100269) B8100269
theorem B3600119 : Blo 2131435 3600119 := bstep (se 1 (by rfl) ⟨2700089, by rfl⟩ : syracuseStep 3600119 = 5400179) B5400179
theorem B2400079 : Blo 2131435 2400079 := bstep (se 1 (by rfl) ⟨1800059, by rfl⟩ : syracuseStep 2400079 = 3600119) B3600119
theorem B3200105 : Blo 2131435 3200105 := bstep (se 2 (by rfl) ⟨1200039, by rfl⟩ : syracuseStep 3200105 = 2400079) B2400079
theorem B2133403 : Blo 2131435 2133403 := bstep (se 1 (by rfl) ⟨1600052, by rfl⟩ : syracuseStep 2133403 = 3200105) B3200105
theorem B3243773 : Blo 2131435 3243773 := bbase (se 3 (by rfl) ⟨608207, by rfl⟩ : syracuseStep 3243773 = 1216415) (by norm_num)
theorem B8650061 : Blo 2131435 8650061 := bstep (se 3 (by rfl) ⟨1621886, by rfl⟩ : syracuseStep 8650061 = 3243773) B3243773
theorem B5766707 : Blo 2131435 5766707 := bstep (se 1 (by rfl) ⟨4325030, by rfl⟩ : syracuseStep 5766707 = 8650061) B8650061
theorem B3844471 : Blo 2131435 3844471 := bstep (se 1 (by rfl) ⟨2883353, by rfl⟩ : syracuseStep 3844471 = 5766707) B5766707
theorem B5125961 : Blo 2131435 5125961 := bstep (se 2 (by rfl) ⟨1922235, by rfl⟩ : syracuseStep 5125961 = 3844471) B3844471
theorem B13669229 : Blo 2131435 13669229 := bstep (se 3 (by rfl) ⟨2562980, by rfl⟩ : syracuseStep 13669229 = 5125961) B5125961
theorem B9112819 : Blo 2131435 9112819 := bstep (se 1 (by rfl) ⟨6834614, by rfl⟩ : syracuseStep 9112819 = 13669229) B13669229
theorem B12150425 : Blo 2131435 12150425 := bstep (se 2 (by rfl) ⟨4556409, by rfl⟩ : syracuseStep 12150425 = 9112819) B9112819
theorem B8100283 : Blo 2131435 8100283 := bstep (se 1 (by rfl) ⟨6075212, by rfl⟩ : syracuseStep 8100283 = 12150425) B12150425
theorem B10800377 : Blo 2131435 10800377 := bstep (se 2 (by rfl) ⟨4050141, by rfl⟩ : syracuseStep 10800377 = 8100283) B8100283
theorem B7200251 : Blo 2131435 7200251 := bstep (se 1 (by rfl) ⟨5400188, by rfl⟩ : syracuseStep 7200251 = 10800377) B10800377
theorem B4800167 : Blo 2131435 4800167 := bstep (se 1 (by rfl) ⟨3600125, by rfl⟩ : syracuseStep 4800167 = 7200251) B7200251
theorem B3200111 : Blo 2131435 3200111 := bstep (se 1 (by rfl) ⟨2400083, by rfl⟩ : syracuseStep 3200111 = 4800167) B4800167
theorem B2133407 : Blo 2131435 2133407 := bstep (se 1 (by rfl) ⟨1600055, by rfl⟩ : syracuseStep 2133407 = 3200111) B3200111
theorem B3200117 : Blo 2131435 3200117 := bbase (se 5 (by rfl) ⟨150005, by rfl⟩ : syracuseStep 3200117 = 300011) (by norm_num)
theorem B2133411 : Blo 2131435 2133411 := bstep (se 1 (by rfl) ⟨1600058, by rfl⟩ : syracuseStep 2133411 = 3200117) B3200117
theorem B4050157 : Blo 2131435 4050157 := bbase (se 3 (by rfl) ⟨759404, by rfl⟩ : syracuseStep 4050157 = 1518809) (by norm_num)
theorem B5400209 : Blo 2131435 5400209 := bstep (se 2 (by rfl) ⟨2025078, by rfl⟩ : syracuseStep 5400209 = 4050157) B4050157
theorem B3600139 : Blo 2131435 3600139 := bstep (se 1 (by rfl) ⟨2700104, by rfl⟩ : syracuseStep 3600139 = 5400209) B5400209
theorem B4800185 : Blo 2131435 4800185 := bstep (se 2 (by rfl) ⟨1800069, by rfl⟩ : syracuseStep 4800185 = 3600139) B3600139
theorem B3200123 : Blo 2131435 3200123 := bstep (se 1 (by rfl) ⟨2400092, by rfl⟩ : syracuseStep 3200123 = 4800185) B4800185
theorem B2133415 : Blo 2131435 2133415 := bstep (se 1 (by rfl) ⟨1600061, by rfl⟩ : syracuseStep 2133415 = 3200123) B3200123
theorem B2400097 : Blo 2131435 2400097 := bbase (se 2 (by rfl) ⟨900036, by rfl⟩ : syracuseStep 2400097 = 1800073) (by norm_num)
theorem B3200129 : Blo 2131435 3200129 := bstep (se 2 (by rfl) ⟨1200048, by rfl⟩ : syracuseStep 3200129 = 2400097) B2400097
theorem B2133419 : Blo 2131435 2133419 := bstep (se 1 (by rfl) ⟨1600064, by rfl⟩ : syracuseStep 2133419 = 3200129) B3200129
theorem B5400229 : Blo 2131435 5400229 := bbase (se 4 (by rfl) ⟨506271, by rfl⟩ : syracuseStep 5400229 = 1012543) (by norm_num)
theorem B7200305 : Blo 2131435 7200305 := bstep (se 2 (by rfl) ⟨2700114, by rfl⟩ : syracuseStep 7200305 = 5400229) B5400229
theorem B4800203 : Blo 2131435 4800203 := bstep (se 1 (by rfl) ⟨3600152, by rfl⟩ : syracuseStep 4800203 = 7200305) B7200305
theorem B3200135 : Blo 2131435 3200135 := bstep (se 1 (by rfl) ⟨2400101, by rfl⟩ : syracuseStep 3200135 = 4800203) B4800203
theorem B2133423 : Blo 2131435 2133423 := bstep (se 1 (by rfl) ⟨1600067, by rfl⟩ : syracuseStep 2133423 = 3200135) B3200135
theorem B3200141 : Blo 2131435 3200141 := bbase (se 3 (by rfl) ⟨600026, by rfl⟩ : syracuseStep 3200141 = 1200053) (by norm_num)
theorem B2133427 : Blo 2131435 2133427 := bstep (se 1 (by rfl) ⟨1600070, by rfl⟩ : syracuseStep 2133427 = 3200141) B3200141
theorem B4800221 : Blo 2131435 4800221 := bbase (se 3 (by rfl) ⟨900041, by rfl⟩ : syracuseStep 4800221 = 1800083) (by norm_num)
theorem B3200147 : Blo 2131435 3200147 := bstep (se 1 (by rfl) ⟨2400110, by rfl⟩ : syracuseStep 3200147 = 4800221) B4800221
theorem B2133431 : Blo 2131435 2133431 := bstep (se 1 (by rfl) ⟨1600073, by rfl⟩ : syracuseStep 2133431 = 3200147) B3200147
theorem B3600173 : Blo 2131435 3600173 := bbase (se 3 (by rfl) ⟨675032, by rfl⟩ : syracuseStep 3600173 = 1350065) (by norm_num)
theorem B2400115 : Blo 2131435 2400115 := bstep (se 1 (by rfl) ⟨1800086, by rfl⟩ : syracuseStep 2400115 = 3600173) B3600173
theorem B3200153 : Blo 2131435 3200153 := bstep (se 2 (by rfl) ⟨1200057, by rfl⟩ : syracuseStep 3200153 = 2400115) B2400115
theorem B2133435 : Blo 2131435 2133435 := bstep (se 1 (by rfl) ⟨1600076, by rfl⟩ : syracuseStep 2133435 = 3200153) B3200153
theorem C0 (j : ℕ) (h1 : 532858 ≤ j) (h2 : j ≤ 533358) : Blo 2131435 (4 * j + 3) := by
  interval_cases j
  · exact B2131435
  · exact B2131439
  · exact B2131443
  · exact B2131447
  · exact B2131451
  · exact B2131455
  · exact B2131459
  · exact B2131463
  · exact B2131467
  · exact B2131471
  · exact B2131475
  · exact B2131479
  · exact B2131483
  · exact B2131487
  · exact B2131491
  · exact B2131495
  · exact B2131499
  · exact B2131503
  · exact B2131507
  · exact B2131511
  · exact B2131515
  · exact B2131519
  · exact B2131523
  · exact B2131527
  · exact B2131531
  · exact B2131535
  · exact B2131539
  · exact B2131543
  · exact B2131547
  · exact B2131551
  · exact B2131555
  · exact B2131559
  · exact B2131563
  · exact B2131567
  · exact B2131571
  · exact B2131575
  · exact B2131579
  · exact B2131583
  · exact B2131587
  · exact B2131591
  · exact B2131595
  · exact B2131599
  · exact B2131603
  · exact B2131607
  · exact B2131611
  · exact B2131615
  · exact B2131619
  · exact B2131623
  · exact B2131627
  · exact B2131631
  · exact B2131635
  · exact B2131639
  · exact B2131643
  · exact B2131647
  · exact B2131651
  · exact B2131655
  · exact B2131659
  · exact B2131663
  · exact B2131667
  · exact B2131671
  · exact B2131675
  · exact B2131679
  · exact B2131683
  · exact B2131687
  · exact B2131691
  · exact B2131695
  · exact B2131699
  · exact B2131703
  · exact B2131707
  · exact B2131711
  · exact B2131715
  · exact B2131719
  · exact B2131723
  · exact B2131727
  · exact B2131731
  · exact B2131735
  · exact B2131739
  · exact B2131743
  · exact B2131747
  · exact B2131751
  · exact B2131755
  · exact B2131759
  · exact B2131763
  · exact B2131767
  · exact B2131771
  · exact B2131775
  · exact B2131779
  · exact B2131783
  · exact B2131787
  · exact B2131791
  · exact B2131795
  · exact B2131799
  · exact B2131803
  · exact B2131807
  · exact B2131811
  · exact B2131815
  · exact B2131819
  · exact B2131823
  · exact B2131827
  · exact B2131831
  · exact B2131835
  · exact B2131839
  · exact B2131843
  · exact B2131847
  · exact B2131851
  · exact B2131855
  · exact B2131859
  · exact B2131863
  · exact B2131867
  · exact B2131871
  · exact B2131875
  · exact B2131879
  · exact B2131883
  · exact B2131887
  · exact B2131891
  · exact B2131895
  · exact B2131899
  · exact B2131903
  · exact B2131907
  · exact B2131911
  · exact B2131915
  · exact B2131919
  · exact B2131923
  · exact B2131927
  · exact B2131931
  · exact B2131935
  · exact B2131939
  · exact B2131943
  · exact B2131947
  · exact B2131951
  · exact B2131955
  · exact B2131959
  · exact B2131963
  · exact B2131967
  · exact B2131971
  · exact B2131975
  · exact B2131979
  · exact B2131983
  · exact B2131987
  · exact B2131991
  · exact B2131995
  · exact B2131999
  · exact B2132003
  · exact B2132007
  · exact B2132011
  · exact B2132015
  · exact B2132019
  · exact B2132023
  · exact B2132027
  · exact B2132031
  · exact B2132035
  · exact B2132039
  · exact B2132043
  · exact B2132047
  · exact B2132051
  · exact B2132055
  · exact B2132059
  · exact B2132063
  · exact B2132067
  · exact B2132071
  · exact B2132075
  · exact B2132079
  · exact B2132083
  · exact B2132087
  · exact B2132091
  · exact B2132095
  · exact B2132099
  · exact B2132103
  · exact B2132107
  · exact B2132111
  · exact B2132115
  · exact B2132119
  · exact B2132123
  · exact B2132127
  · exact B2132131
  · exact B2132135
  · exact B2132139
  · exact B2132143
  · exact B2132147
  · exact B2132151
  · exact B2132155
  · exact B2132159
  · exact B2132163
  · exact B2132167
  · exact B2132171
  · exact B2132175
  · exact B2132179
  · exact B2132183
  · exact B2132187
  · exact B2132191
  · exact B2132195
  · exact B2132199
  · exact B2132203
  · exact B2132207
  · exact B2132211
  · exact B2132215
  · exact B2132219
  · exact B2132223
  · exact B2132227
  · exact B2132231
  · exact B2132235
  · exact B2132239
  · exact B2132243
  · exact B2132247
  · exact B2132251
  · exact B2132255
  · exact B2132259
  · exact B2132263
  · exact B2132267
  · exact B2132271
  · exact B2132275
  · exact B2132279
  · exact B2132283
  · exact B2132287
  · exact B2132291
  · exact B2132295
  · exact B2132299
  · exact B2132303
  · exact B2132307
  · exact B2132311
  · exact B2132315
  · exact B2132319
  · exact B2132323
  · exact B2132327
  · exact B2132331
  · exact B2132335
  · exact B2132339
  · exact B2132343
  · exact B2132347
  · exact B2132351
  · exact B2132355
  · exact B2132359
  · exact B2132363
  · exact B2132367
  · exact B2132371
  · exact B2132375
  · exact B2132379
  · exact B2132383
  · exact B2132387
  · exact B2132391
  · exact B2132395
  · exact B2132399
  · exact B2132403
  · exact B2132407
  · exact B2132411
  · exact B2132415
  · exact B2132419
  · exact B2132423
  · exact B2132427
  · exact B2132431
  · exact B2132435
  · exact B2132439
  · exact B2132443
  · exact B2132447
  · exact B2132451
  · exact B2132455
  · exact B2132459
  · exact B2132463
  · exact B2132467
  · exact B2132471
  · exact B2132475
  · exact B2132479
  · exact B2132483
  · exact B2132487
  · exact B2132491
  · exact B2132495
  · exact B2132499
  · exact B2132503
  · exact B2132507
  · exact B2132511
  · exact B2132515
  · exact B2132519
  · exact B2132523
  · exact B2132527
  · exact B2132531
  · exact B2132535
  · exact B2132539
  · exact B2132543
  · exact B2132547
  · exact B2132551
  · exact B2132555
  · exact B2132559
  · exact B2132563
  · exact B2132567
  · exact B2132571
  · exact B2132575
  · exact B2132579
  · exact B2132583
  · exact B2132587
  · exact B2132591
  · exact B2132595
  · exact B2132599
  · exact B2132603
  · exact B2132607
  · exact B2132611
  · exact B2132615
  · exact B2132619
  · exact B2132623
  · exact B2132627
  · exact B2132631
  · exact B2132635
  · exact B2132639
  · exact B2132643
  · exact B2132647
  · exact B2132651
  · exact B2132655
  · exact B2132659
  · exact B2132663
  · exact B2132667
  · exact B2132671
  · exact B2132675
  · exact B2132679
  · exact B2132683
  · exact B2132687
  · exact B2132691
  · exact B2132695
  · exact B2132699
  · exact B2132703
  · exact B2132707
  · exact B2132711
  · exact B2132715
  · exact B2132719
  · exact B2132723
  · exact B2132727
  · exact B2132731
  · exact B2132735
  · exact B2132739
  · exact B2132743
  · exact B2132747
  · exact B2132751
  · exact B2132755
  · exact B2132759
  · exact B2132763
  · exact B2132767
  · exact B2132771
  · exact B2132775
  · exact B2132779
  · exact B2132783
  · exact B2132787
  · exact B2132791
  · exact B2132795
  · exact B2132799
  · exact B2132803
  · exact B2132807
  · exact B2132811
  · exact B2132815
  · exact B2132819
  · exact B2132823
  · exact B2132827
  · exact B2132831
  · exact B2132835
  · exact B2132839
  · exact B2132843
  · exact B2132847
  · exact B2132851
  · exact B2132855
  · exact B2132859
  · exact B2132863
  · exact B2132867
  · exact B2132871
  · exact B2132875
  · exact B2132879
  · exact B2132883
  · exact B2132887
  · exact B2132891
  · exact B2132895
  · exact B2132899
  · exact B2132903
  · exact B2132907
  · exact B2132911
  · exact B2132915
  · exact B2132919
  · exact B2132923
  · exact B2132927
  · exact B2132931
  · exact B2132935
  · exact B2132939
  · exact B2132943
  · exact B2132947
  · exact B2132951
  · exact B2132955
  · exact B2132959
  · exact B2132963
  · exact B2132967
  · exact B2132971
  · exact B2132975
  · exact B2132979
  · exact B2132983
  · exact B2132987
  · exact B2132991
  · exact B2132995
  · exact B2132999
  · exact B2133003
  · exact B2133007
  · exact B2133011
  · exact B2133015
  · exact B2133019
  · exact B2133023
  · exact B2133027
  · exact B2133031
  · exact B2133035
  · exact B2133039
  · exact B2133043
  · exact B2133047
  · exact B2133051
  · exact B2133055
  · exact B2133059
  · exact B2133063
  · exact B2133067
  · exact B2133071
  · exact B2133075
  · exact B2133079
  · exact B2133083
  · exact B2133087
  · exact B2133091
  · exact B2133095
  · exact B2133099
  · exact B2133103
  · exact B2133107
  · exact B2133111
  · exact B2133115
  · exact B2133119
  · exact B2133123
  · exact B2133127
  · exact B2133131
  · exact B2133135
  · exact B2133139
  · exact B2133143
  · exact B2133147
  · exact B2133151
  · exact B2133155
  · exact B2133159
  · exact B2133163
  · exact B2133167
  · exact B2133171
  · exact B2133175
  · exact B2133179
  · exact B2133183
  · exact B2133187
  · exact B2133191
  · exact B2133195
  · exact B2133199
  · exact B2133203
  · exact B2133207
  · exact B2133211
  · exact B2133215
  · exact B2133219
  · exact B2133223
  · exact B2133227
  · exact B2133231
  · exact B2133235
  · exact B2133239
  · exact B2133243
  · exact B2133247
  · exact B2133251
  · exact B2133255
  · exact B2133259
  · exact B2133263
  · exact B2133267
  · exact B2133271
  · exact B2133275
  · exact B2133279
  · exact B2133283
  · exact B2133287
  · exact B2133291
  · exact B2133295
  · exact B2133299
  · exact B2133303
  · exact B2133307
  · exact B2133311
  · exact B2133315
  · exact B2133319
  · exact B2133323
  · exact B2133327
  · exact B2133331
  · exact B2133335
  · exact B2133339
  · exact B2133343
  · exact B2133347
  · exact B2133351
  · exact B2133355
  · exact B2133359
  · exact B2133363
  · exact B2133367
  · exact B2133371
  · exact B2133375
  · exact B2133379
  · exact B2133383
  · exact B2133387
  · exact B2133391
  · exact B2133395
  · exact B2133399
  · exact B2133403
  · exact B2133407
  · exact B2133411
  · exact B2133415
  · exact B2133419
  · exact B2133423
  · exact B2133427
  · exact B2133431
  · exact B2133435
theorem solution (m : ℕ) (hlo : 2131435 ≤ m) (hhi : m ≤ 2133435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 532858 ≤ j := by omega
    have hj2 : j ≤ 533358 := by omega
    have hb : Blo 2131435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
