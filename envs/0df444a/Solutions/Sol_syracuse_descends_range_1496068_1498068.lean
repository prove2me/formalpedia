-- Prove2me | solution 1 for syracuse_descends_range_1496068_1498068
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:47:23.383238+00:00
-- url     : https://prove2.me/submissions/599faa47-320a-4b9a-8858-56e6a9ff8e69

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


theorem B3366917 : Blo 1496068 3366917 := bbase (se 4 (by rfl) ⟨315648, by rfl⟩ : syracuseStep 3366917 = 631297) (by norm_num)
theorem B2244629 : Blo 1496068 2244629 := bbase (se 6 (by rfl) ⟨52608, by rfl⟩ : syracuseStep 2244629 = 105217) (by norm_num)
theorem B2244653 : Blo 1496068 2244653 := bbase (se 3 (by rfl) ⟨420872, by rfl⟩ : syracuseStep 2244653 = 841745) (by norm_num)
theorem B2244677 : Blo 1496068 2244677 := bbase (se 4 (by rfl) ⟨210438, by rfl⟩ : syracuseStep 2244677 = 420877) (by norm_num)
theorem B3366989 : Blo 1496068 3366989 := bbase (se 3 (by rfl) ⟨631310, by rfl⟩ : syracuseStep 3366989 = 1262621) (by norm_num)
theorem B2244701 : Blo 1496068 2244701 := bbase (se 3 (by rfl) ⟨420881, by rfl⟩ : syracuseStep 2244701 = 841763) (by norm_num)
theorem B5685349 : Blo 1496068 5685349 := bbase (se 4 (by rfl) ⟨533001, by rfl⟩ : syracuseStep 5685349 = 1066003) (by norm_num)
theorem B2244725 : Blo 1496068 2244725 := bbase (se 5 (by rfl) ⟨105221, by rfl⟩ : syracuseStep 2244725 = 210443) (by norm_num)
theorem B2244749 : Blo 1496068 2244749 := bbase (se 3 (by rfl) ⟨420890, by rfl⟩ : syracuseStep 2244749 = 841781) (by norm_num)
theorem B3367061 : Blo 1496068 3367061 := bbase (se 6 (by rfl) ⟨78915, by rfl⟩ : syracuseStep 3367061 = 157831) (by norm_num)
theorem B2244773 : Blo 1496068 2244773 := bbase (se 4 (by rfl) ⟨210447, by rfl⟩ : syracuseStep 2244773 = 420895) (by norm_num)
theorem B2842789 : Blo 1496068 2842789 := bbase (se 4 (by rfl) ⟨266511, by rfl⟩ : syracuseStep 2842789 = 533023) (by norm_num)
theorem B2244797 : Blo 1496068 2244797 := bbase (se 3 (by rfl) ⟨420899, by rfl⟩ : syracuseStep 2244797 = 841799) (by norm_num)
theorem B2244821 : Blo 1496068 2244821 := bbase (se 7 (by rfl) ⟨26306, by rfl⟩ : syracuseStep 2244821 = 52613) (by norm_num)
theorem B3367133 : Blo 1496068 3367133 := bbase (se 3 (by rfl) ⟨631337, by rfl⟩ : syracuseStep 3367133 = 1262675) (by norm_num)
theorem B2244845 : Blo 1496068 2244845 := bbase (se 3 (by rfl) ⟨420908, by rfl⟩ : syracuseStep 2244845 = 841817) (by norm_num)
theorem B1597681 : Blo 1496068 1597681 := bbase (se 2 (by rfl) ⟨599130, by rfl⟩ : syracuseStep 1597681 = 1198261) (by norm_num)
theorem B2220277 : Blo 1496068 2220277 := bbase (se 5 (by rfl) ⟨104075, by rfl⟩ : syracuseStep 2220277 = 208151) (by norm_num)
theorem B2244869 : Blo 1496068 2244869 := bbase (se 4 (by rfl) ⟨210456, by rfl⟩ : syracuseStep 2244869 = 420913) (by norm_num)
theorem B2244893 : Blo 1496068 2244893 := bbase (se 3 (by rfl) ⟨420917, by rfl⟩ : syracuseStep 2244893 = 841835) (by norm_num)
theorem B3367205 : Blo 1496068 3367205 := bbase (se 4 (by rfl) ⟨315675, by rfl⟩ : syracuseStep 3367205 = 631351) (by norm_num)
theorem B2130229 : Blo 1496068 2130229 := bbase (se 5 (by rfl) ⟨99854, by rfl⟩ : syracuseStep 2130229 = 199709) (by norm_num)
theorem B2244917 : Blo 1496068 2244917 := bbase (se 5 (by rfl) ⟨105230, by rfl⟩ : syracuseStep 2244917 = 210461) (by norm_num)
theorem B2842933 : Blo 1496068 2842933 := bbase (se 5 (by rfl) ⟨133262, by rfl⟩ : syracuseStep 2842933 = 266525) (by norm_num)
theorem B2244941 : Blo 1496068 2244941 := bbase (se 3 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 2244941 = 841853) (by norm_num)
theorem B20496725 : Blo 1496068 20496725 := bbase (se 10 (by rfl) ⟨30024, by rfl⟩ : syracuseStep 20496725 = 60049) (by norm_num)
theorem B2244965 : Blo 1496068 2244965 := bbase (se 4 (by rfl) ⟨210465, by rfl⟩ : syracuseStep 2244965 = 420931) (by norm_num)
theorem B3367277 : Blo 1496068 3367277 := bbase (se 3 (by rfl) ⟨631364, by rfl⟩ : syracuseStep 3367277 = 1262729) (by norm_num)
theorem B2244989 : Blo 1496068 2244989 := bbase (se 3 (by rfl) ⟨420935, by rfl⟩ : syracuseStep 2244989 = 841871) (by norm_num)
theorem B2245013 : Blo 1496068 2245013 := bbase (se 6 (by rfl) ⟨52617, by rfl⟩ : syracuseStep 2245013 = 105235) (by norm_num)
theorem B5685653 : Blo 1496068 5685653 := bbase (se 6 (by rfl) ⟨133257, by rfl⟩ : syracuseStep 5685653 = 266515) (by norm_num)
theorem B5054885 : Blo 1496068 5054885 := bbase (se 4 (by rfl) ⟨473895, by rfl⟩ : syracuseStep 5054885 = 947791) (by norm_num)
theorem B2245037 : Blo 1496068 2245037 := bbase (se 3 (by rfl) ⟨420944, by rfl⟩ : syracuseStep 2245037 = 841889) (by norm_num)
theorem B3367349 : Blo 1496068 3367349 := bbase (se 5 (by rfl) ⟨157844, by rfl⟩ : syracuseStep 3367349 = 315689) (by norm_num)
theorem B2245061 : Blo 1496068 2245061 := bbase (se 4 (by rfl) ⟨210474, by rfl⟩ : syracuseStep 2245061 = 420949) (by norm_num)
theorem B2843093 : Blo 1496068 2843093 := bbase (se 7 (by rfl) ⟨33317, by rfl⟩ : syracuseStep 2843093 = 66635) (by norm_num)
theorem B2245085 : Blo 1496068 2245085 := bbase (se 3 (by rfl) ⟨420953, by rfl⟩ : syracuseStep 2245085 = 841907) (by norm_num)
theorem B2245109 : Blo 1496068 2245109 := bbase (se 5 (by rfl) ⟨105239, by rfl⟩ : syracuseStep 2245109 = 210479) (by norm_num)
theorem B3367421 : Blo 1496068 3367421 := bbase (se 3 (by rfl) ⟨631391, by rfl⟩ : syracuseStep 3367421 = 1262783) (by norm_num)
theorem B2245133 : Blo 1496068 2245133 := bbase (se 3 (by rfl) ⟨420962, by rfl⟩ : syracuseStep 2245133 = 841925) (by norm_num)
theorem B2245157 : Blo 1496068 2245157 := bbase (se 4 (by rfl) ⟨210483, by rfl⟩ : syracuseStep 2245157 = 420967) (by norm_num)
theorem B2245181 : Blo 1496068 2245181 := bbase (se 3 (by rfl) ⟨420971, by rfl⟩ : syracuseStep 2245181 = 841943) (by norm_num)
theorem B3367493 : Blo 1496068 3367493 := bbase (se 4 (by rfl) ⟨315702, by rfl⟩ : syracuseStep 3367493 = 631405) (by norm_num)
theorem B2245205 : Blo 1496068 2245205 := bbase (se 8 (by rfl) ⟨13155, by rfl⟩ : syracuseStep 2245205 = 26311) (by norm_num)
theorem B7578197 : Blo 1496068 7578197 := bbase (se 8 (by rfl) ⟨44403, by rfl⟩ : syracuseStep 7578197 = 88807) (by norm_num)
theorem B2843237 : Blo 1496068 2843237 := bbase (se 4 (by rfl) ⟨266553, by rfl⟩ : syracuseStep 2843237 = 533107) (by norm_num)
theorem B2245229 : Blo 1496068 2245229 := bbase (se 3 (by rfl) ⟨420980, by rfl⟩ : syracuseStep 2245229 = 841961) (by norm_num)
theorem B2245253 : Blo 1496068 2245253 := bbase (se 4 (by rfl) ⟨210492, by rfl⟩ : syracuseStep 2245253 = 420985) (by norm_num)
theorem B3367565 : Blo 1496068 3367565 := bbase (se 3 (by rfl) ⟨631418, by rfl⟩ : syracuseStep 3367565 = 1262837) (by norm_num)
theorem B3195541 : Blo 1496068 3195541 := bbase (se 6 (by rfl) ⟨74895, by rfl⟩ : syracuseStep 3195541 = 149791) (by norm_num)
theorem B2245277 : Blo 1496068 2245277 := bbase (se 3 (by rfl) ⟨420989, by rfl⟩ : syracuseStep 2245277 = 841979) (by norm_num)
theorem B1598125 : Blo 1496068 1598125 := bbase (se 3 (by rfl) ⟨299648, by rfl⟩ : syracuseStep 1598125 = 599297) (by norm_num)
theorem B2245301 : Blo 1496068 2245301 := bbase (se 5 (by rfl) ⟨105248, by rfl⟩ : syracuseStep 2245301 = 210497) (by norm_num)
theorem B2245325 : Blo 1496068 2245325 := bbase (se 3 (by rfl) ⟨420998, by rfl⟩ : syracuseStep 2245325 = 841997) (by norm_num)
theorem B3367637 : Blo 1496068 3367637 := bbase (se 7 (by rfl) ⟨39464, by rfl⟩ : syracuseStep 3367637 = 78929) (by norm_num)
theorem B2245349 : Blo 1496068 2245349 := bbase (se 4 (by rfl) ⟨210501, by rfl⟩ : syracuseStep 2245349 = 421003) (by norm_num)
theorem B2245373 : Blo 1496068 2245373 := bbase (se 3 (by rfl) ⟨421007, by rfl⟩ : syracuseStep 2245373 = 842015) (by norm_num)
theorem B3597061 : Blo 1496068 3597061 := bbase (se 4 (by rfl) ⟨337224, by rfl⟩ : syracuseStep 3597061 = 674449) (by norm_num)
theorem B2245397 : Blo 1496068 2245397 := bbase (se 6 (by rfl) ⟨52626, by rfl⟩ : syracuseStep 2245397 = 105253) (by norm_num)
theorem B3367709 : Blo 1496068 3367709 := bbase (se 3 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 3367709 = 1262891) (by norm_num)
theorem B2130725 : Blo 1496068 2130725 := bbase (se 4 (by rfl) ⟨199755, by rfl⟩ : syracuseStep 2130725 = 399511) (by norm_num)
theorem B1598249 : Blo 1496068 1598249 := bbase (se 2 (by rfl) ⟨599343, by rfl⟩ : syracuseStep 1598249 = 1198687) (by norm_num)
theorem B2245421 : Blo 1496068 2245421 := bbase (se 3 (by rfl) ⟨421016, by rfl⟩ : syracuseStep 2245421 = 842033) (by norm_num)
theorem B2245445 : Blo 1496068 2245445 := bbase (se 4 (by rfl) ⟨210510, by rfl⟩ : syracuseStep 2245445 = 421021) (by norm_num)
theorem B5055317 : Blo 1496068 5055317 := bbase (se 9 (by rfl) ⟨14810, by rfl⟩ : syracuseStep 5055317 = 29621) (by norm_num)
theorem B2245469 : Blo 1496068 2245469 := bbase (se 3 (by rfl) ⟨421025, by rfl⟩ : syracuseStep 2245469 = 842051) (by norm_num)
theorem B3367781 : Blo 1496068 3367781 := bbase (se 4 (by rfl) ⟨315729, by rfl⟩ : syracuseStep 3367781 = 631459) (by norm_num)
theorem B2245493 : Blo 1496068 2245493 := bbase (se 5 (by rfl) ⟨105257, by rfl⟩ : syracuseStep 2245493 = 210515) (by norm_num)
theorem B2843525 : Blo 1496068 2843525 := bbase (se 4 (by rfl) ⟨266580, by rfl⟩ : syracuseStep 2843525 = 533161) (by norm_num)
theorem B2245517 : Blo 1496068 2245517 := bbase (se 3 (by rfl) ⟨421034, by rfl⟩ : syracuseStep 2245517 = 842069) (by norm_num)
theorem B2245541 : Blo 1496068 2245541 := bbase (se 4 (by rfl) ⟨210519, by rfl⟩ : syracuseStep 2245541 = 421039) (by norm_num)
theorem B2024357 : Blo 1496068 2024357 := bbase (se 4 (by rfl) ⟨189783, by rfl⟩ : syracuseStep 2024357 = 379567) (by norm_num)
theorem B3367853 : Blo 1496068 3367853 := bbase (se 3 (by rfl) ⟨631472, by rfl⟩ : syracuseStep 3367853 = 1262945) (by norm_num)
theorem B2245565 : Blo 1496068 2245565 := bbase (se 3 (by rfl) ⟨421043, by rfl⟩ : syracuseStep 2245565 = 842087) (by norm_num)
theorem B2024389 : Blo 1496068 2024389 := bbase (se 4 (by rfl) ⟨189786, by rfl⟩ : syracuseStep 2024389 = 379573) (by norm_num)
theorem B2245589 : Blo 1496068 2245589 := bbase (se 7 (by rfl) ⟨26315, by rfl⟩ : syracuseStep 2245589 = 52631) (by norm_num)
theorem B2245613 : Blo 1496068 2245613 := bbase (se 3 (by rfl) ⟨421052, by rfl⟩ : syracuseStep 2245613 = 842105) (by norm_num)
theorem B3367925 : Blo 1496068 3367925 := bbase (se 5 (by rfl) ⟨157871, by rfl⟩ : syracuseStep 3367925 = 315743) (by norm_num)
theorem B4260869 : Blo 1496068 4260869 := bbase (se 4 (by rfl) ⟨399456, by rfl⟩ : syracuseStep 4260869 = 798913) (by norm_num)
theorem B2245637 : Blo 1496068 2245637 := bbase (se 4 (by rfl) ⟨210528, by rfl⟩ : syracuseStep 2245637 = 421057) (by norm_num)
theorem B2245661 : Blo 1496068 2245661 := bbase (se 3 (by rfl) ⟨421061, by rfl⟩ : syracuseStep 2245661 = 842123) (by norm_num)
theorem B2843677 : Blo 1496068 2843677 := bbase (se 3 (by rfl) ⟨533189, by rfl⟩ : syracuseStep 2843677 = 1066379) (by norm_num)
theorem B1598501 : Blo 1496068 1598501 := bbase (se 4 (by rfl) ⟨149859, by rfl⟩ : syracuseStep 1598501 = 299719) (by norm_num)
theorem B2245685 : Blo 1496068 2245685 := bbase (se 5 (by rfl) ⟨105266, by rfl⟩ : syracuseStep 2245685 = 210533) (by norm_num)
theorem B2925629 : Blo 1496068 2925629 := bbase (se 3 (by rfl) ⟨548555, by rfl⟩ : syracuseStep 2925629 = 1097111) (by norm_num)
theorem B3367997 : Blo 1496068 3367997 := bbase (se 3 (by rfl) ⟨631499, by rfl⟩ : syracuseStep 3367997 = 1262999) (by norm_num)
theorem B2245709 : Blo 1496068 2245709 := bbase (se 3 (by rfl) ⟨421070, by rfl⟩ : syracuseStep 2245709 = 842141) (by norm_num)
theorem B2245733 : Blo 1496068 2245733 := bbase (se 4 (by rfl) ⟨210537, by rfl⟩ : syracuseStep 2245733 = 421075) (by norm_num)
theorem B7193717 : Blo 1496068 7193717 := bbase (se 5 (by rfl) ⟨337205, by rfl⟩ : syracuseStep 7193717 = 674411) (by norm_num)
theorem B2245757 : Blo 1496068 2245757 := bbase (se 3 (by rfl) ⟨421079, by rfl⟩ : syracuseStep 2245757 = 842159) (by norm_num)
theorem B3368069 : Blo 1496068 3368069 := bbase (se 4 (by rfl) ⟨315756, by rfl⟩ : syracuseStep 3368069 = 631513) (by norm_num)
theorem B2245781 : Blo 1496068 2245781 := bbase (se 6 (by rfl) ⟨52635, by rfl⟩ : syracuseStep 2245781 = 105271) (by norm_num)
theorem B2245805 : Blo 1496068 2245805 := bbase (se 3 (by rfl) ⟨421088, by rfl⟩ : syracuseStep 2245805 = 842177) (by norm_num)
theorem B1893557 : Blo 1496068 1893557 := bbase (se 5 (by rfl) ⟨88760, by rfl⟩ : syracuseStep 1893557 = 177521) (by norm_num)
theorem B2245829 : Blo 1496068 2245829 := bbase (se 4 (by rfl) ⟨210546, by rfl⟩ : syracuseStep 2245829 = 421093) (by norm_num)
theorem B3368141 : Blo 1496068 3368141 := bbase (se 3 (by rfl) ⟨631526, by rfl⟩ : syracuseStep 3368141 = 1263053) (by norm_num)
theorem B2245853 : Blo 1496068 2245853 := bbase (se 3 (by rfl) ⟨421097, by rfl⟩ : syracuseStep 2245853 = 842195) (by norm_num)
theorem B1893613 : Blo 1496068 1893613 := bbase (se 3 (by rfl) ⟨355052, by rfl⟩ : syracuseStep 1893613 = 710105) (by norm_num)
theorem B2245877 : Blo 1496068 2245877 := bbase (se 5 (by rfl) ⟨105275, by rfl⟩ : syracuseStep 2245877 = 210551) (by norm_num)
theorem B5055749 : Blo 1496068 5055749 := bbase (se 4 (by rfl) ⟨473976, by rfl⟩ : syracuseStep 5055749 = 947953) (by norm_num)
theorem B2245901 : Blo 1496068 2245901 := bbase (se 3 (by rfl) ⟨421106, by rfl⟩ : syracuseStep 2245901 = 842213) (by norm_num)
theorem B3368213 : Blo 1496068 3368213 := bbase (se 6 (by rfl) ⟨78942, by rfl⟩ : syracuseStep 3368213 = 157885) (by norm_num)
theorem B2245925 : Blo 1496068 2245925 := bbase (se 4 (by rfl) ⟨210555, by rfl⟩ : syracuseStep 2245925 = 421111) (by norm_num)
theorem B2245949 : Blo 1496068 2245949 := bbase (se 3 (by rfl) ⟨421115, by rfl⟩ : syracuseStep 2245949 = 842231) (by norm_num)
theorem B1516865 : Blo 1496068 1516865 := bbase (se 2 (by rfl) ⟨568824, by rfl⟩ : syracuseStep 1516865 = 1137649) (by norm_num)
theorem B1893709 : Blo 1496068 1893709 := bbase (se 3 (by rfl) ⟨355070, by rfl⟩ : syracuseStep 1893709 = 710141) (by norm_num)
theorem B2131277 : Blo 1496068 2131277 := bbase (se 3 (by rfl) ⟨399614, by rfl⟩ : syracuseStep 2131277 = 799229) (by norm_num)
theorem B2843981 : Blo 1496068 2843981 := bbase (se 3 (by rfl) ⟨533246, by rfl⟩ : syracuseStep 2843981 = 1066493) (by norm_num)
theorem B2245973 : Blo 1496068 2245973 := bbase (se 12 (by rfl) ⟨822, by rfl⟩ : syracuseStep 2245973 = 1645) (by norm_num)
theorem B3368285 : Blo 1496068 3368285 := bbase (se 3 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 3368285 = 1263107) (by norm_num)
theorem B2245997 : Blo 1496068 2245997 := bbase (se 3 (by rfl) ⟨421124, by rfl⟩ : syracuseStep 2245997 = 842249) (by norm_num)
theorem B2246021 : Blo 1496068 2246021 := bbase (se 4 (by rfl) ⟨210564, by rfl⟩ : syracuseStep 2246021 = 421129) (by norm_num)
theorem B2246045 : Blo 1496068 2246045 := bbase (se 3 (by rfl) ⟨421133, by rfl⟩ : syracuseStep 2246045 = 842267) (by norm_num)
theorem B3368357 : Blo 1496068 3368357 := bbase (se 4 (by rfl) ⟨315783, by rfl⟩ : syracuseStep 3368357 = 631567) (by norm_num)
theorem B2246069 : Blo 1496068 2246069 := bbase (se 5 (by rfl) ⟨105284, by rfl⟩ : syracuseStep 2246069 = 210569) (by norm_num)
theorem B2524621 : Blo 1496068 2524621 := bbase (se 3 (by rfl) ⟨473366, by rfl⟩ : syracuseStep 2524621 = 946733) (by norm_num)
theorem B2246093 : Blo 1496068 2246093 := bbase (se 3 (by rfl) ⟨421142, by rfl⟩ : syracuseStep 2246093 = 842285) (by norm_num)
theorem B1598945 : Blo 1496068 1598945 := bbase (se 2 (by rfl) ⟨599604, by rfl⟩ : syracuseStep 1598945 = 1199209) (by norm_num)
theorem B2246117 : Blo 1496068 2246117 := bbase (se 4 (by rfl) ⟨210573, by rfl⟩ : syracuseStep 2246117 = 421147) (by norm_num)
theorem B3368429 : Blo 1496068 3368429 := bbase (se 3 (by rfl) ⟨631580, by rfl⟩ : syracuseStep 3368429 = 1263161) (by norm_num)
theorem B1893881 : Blo 1496068 1893881 := bbase (se 2 (by rfl) ⟨710205, by rfl⟩ : syracuseStep 1893881 = 1420411) (by norm_num)
theorem B2246141 : Blo 1496068 2246141 := bbase (se 3 (by rfl) ⟨421151, by rfl⟩ : syracuseStep 2246141 = 842303) (by norm_num)
theorem B2246165 : Blo 1496068 2246165 := bbase (se 6 (by rfl) ⟨52644, by rfl⟩ : syracuseStep 2246165 = 105289) (by norm_num)
theorem B2524709 : Blo 1496068 2524709 := bbase (se 4 (by rfl) ⟨236691, by rfl⟩ : syracuseStep 2524709 = 473383) (by norm_num)
theorem B2246189 : Blo 1496068 2246189 := bbase (se 3 (by rfl) ⟨421160, by rfl⟩ : syracuseStep 2246189 = 842321) (by norm_num)
theorem B1893937 : Blo 1496068 1893937 := bbase (se 2 (by rfl) ⟨710226, by rfl⟩ : syracuseStep 1893937 = 1420453) (by norm_num)
theorem B3368501 : Blo 1496068 3368501 := bbase (se 5 (by rfl) ⟨157898, by rfl⟩ : syracuseStep 3368501 = 315797) (by norm_num)
theorem B8529461 : Blo 1496068 8529461 := bbase (se 5 (by rfl) ⟨399818, by rfl⟩ : syracuseStep 8529461 = 799637) (by norm_num)
theorem B2246213 : Blo 1496068 2246213 := bbase (se 4 (by rfl) ⟨210582, by rfl⟩ : syracuseStep 2246213 = 421165) (by norm_num)
theorem B2246237 : Blo 1496068 2246237 := bbase (se 3 (by rfl) ⟨421169, by rfl⟩ : syracuseStep 2246237 = 842339) (by norm_num)
theorem B2246261 : Blo 1496068 2246261 := bbase (se 5 (by rfl) ⟨105293, by rfl⟩ : syracuseStep 2246261 = 210587) (by norm_num)
theorem B3368573 : Blo 1496068 3368573 := bbase (se 3 (by rfl) ⟨631607, by rfl⟩ : syracuseStep 3368573 = 1263215) (by norm_num)
theorem B2246285 : Blo 1496068 2246285 := bbase (se 3 (by rfl) ⟨421178, by rfl⟩ : syracuseStep 2246285 = 842357) (by norm_num)
theorem B1894033 : Blo 1496068 1894033 := bbase (se 2 (by rfl) ⟨710262, by rfl⟩ : syracuseStep 1894033 = 1420525) (by norm_num)
theorem B19195541 : Blo 1496068 19195541 := bbase (se 6 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 19195541 = 899791) (by norm_num)
theorem B2524837 : Blo 1496068 2524837 := bbase (se 4 (by rfl) ⟨236703, by rfl⟩ : syracuseStep 2524837 = 473407) (by norm_num)
theorem B2246309 : Blo 1496068 2246309 := bbase (se 4 (by rfl) ⟨210591, by rfl⟩ : syracuseStep 2246309 = 421183) (by norm_num)
theorem B2049709 : Blo 1496068 2049709 := bbase (se 3 (by rfl) ⟨384320, by rfl⟩ : syracuseStep 2049709 = 768641) (by norm_num)
theorem B2246333 : Blo 1496068 2246333 := bbase (se 3 (by rfl) ⟨421187, by rfl⟩ : syracuseStep 2246333 = 842375) (by norm_num)
theorem B6391493 : Blo 1496068 6391493 := bbase (se 4 (by rfl) ⟨599202, by rfl⟩ : syracuseStep 6391493 = 1198405) (by norm_num)
theorem B3368645 : Blo 1496068 3368645 := bbase (se 4 (by rfl) ⟨315810, by rfl⟩ : syracuseStep 3368645 = 631621) (by norm_num)
theorem B2246357 : Blo 1496068 2246357 := bbase (se 7 (by rfl) ⟨26324, by rfl⟩ : syracuseStep 2246357 = 52649) (by norm_num)
theorem B1599193 : Blo 1496068 1599193 := bbase (se 2 (by rfl) ⟨599697, by rfl⟩ : syracuseStep 1599193 = 1199395) (by norm_num)
theorem B2246381 : Blo 1496068 2246381 := bbase (se 3 (by rfl) ⟨421196, by rfl⟩ : syracuseStep 2246381 = 842393) (by norm_num)
theorem B14378741 : Blo 1496068 14378741 := bbase (se 5 (by rfl) ⟨674003, by rfl⟩ : syracuseStep 14378741 = 1348007) (by norm_num)
theorem B2524925 : Blo 1496068 2524925 := bbase (se 3 (by rfl) ⟨473423, by rfl⟩ : syracuseStep 2524925 = 946847) (by norm_num)
theorem B2246405 : Blo 1496068 2246405 := bbase (se 4 (by rfl) ⟨210600, by rfl⟩ : syracuseStep 2246405 = 421201) (by norm_num)
theorem B3368717 : Blo 1496068 3368717 := bbase (se 3 (by rfl) ⟨631634, by rfl⟩ : syracuseStep 3368717 = 1263269) (by norm_num)
theorem B2246429 : Blo 1496068 2246429 := bbase (se 3 (by rfl) ⟨421205, by rfl⟩ : syracuseStep 2246429 = 842411) (by norm_num)
theorem B5121829 : Blo 1496068 5121829 := bbase (se 4 (by rfl) ⟨480171, by rfl⟩ : syracuseStep 5121829 = 960343) (by norm_num)
theorem B12814133 : Blo 1496068 12814133 := bbase (se 5 (by rfl) ⟨600662, by rfl⟩ : syracuseStep 12814133 = 1201325) (by norm_num)
theorem B2246453 : Blo 1496068 2246453 := bbase (se 5 (by rfl) ⟨105302, by rfl⟩ : syracuseStep 2246453 = 210605) (by norm_num)
theorem B1894205 : Blo 1496068 1894205 := bbase (se 3 (by rfl) ⟨355163, by rfl⟩ : syracuseStep 1894205 = 710327) (by norm_num)
theorem B2246477 : Blo 1496068 2246477 := bbase (se 3 (by rfl) ⟨421214, by rfl⟩ : syracuseStep 2246477 = 842429) (by norm_num)
theorem B3368789 : Blo 1496068 3368789 := bbase (se 9 (by rfl) ⟨9869, by rfl⟩ : syracuseStep 3368789 = 19739) (by norm_num)
theorem B1664869 : Blo 1496068 1664869 := bbase (se 4 (by rfl) ⟨156081, by rfl⟩ : syracuseStep 1664869 = 312163) (by norm_num)
theorem B7579493 : Blo 1496068 7579493 := bbase (se 4 (by rfl) ⟨710577, by rfl⟩ : syracuseStep 7579493 = 1421155) (by norm_num)
theorem B2246501 : Blo 1496068 2246501 := bbase (se 4 (by rfl) ⟨210609, by rfl⟩ : syracuseStep 2246501 = 421219) (by norm_num)
theorem B1894261 : Blo 1496068 1894261 := bbase (se 5 (by rfl) ⟨88793, by rfl⟩ : syracuseStep 1894261 = 177587) (by norm_num)
theorem B2525053 : Blo 1496068 2525053 := bbase (se 3 (by rfl) ⟨473447, by rfl⟩ : syracuseStep 2525053 = 946895) (by norm_num)
theorem B2246525 : Blo 1496068 2246525 := bbase (se 3 (by rfl) ⟨421223, by rfl⟩ : syracuseStep 2246525 = 842447) (by norm_num)
theorem B1517449 : Blo 1496068 1517449 := bbase (se 2 (by rfl) ⟨569043, by rfl⟩ : syracuseStep 1517449 = 1138087) (by norm_num)
theorem B2246549 : Blo 1496068 2246549 := bbase (se 6 (by rfl) ⟨52653, by rfl⟩ : syracuseStep 2246549 = 105307) (by norm_num)
theorem B3368861 : Blo 1496068 3368861 := bbase (se 3 (by rfl) ⟨631661, by rfl⟩ : syracuseStep 3368861 = 1263323) (by norm_num)
theorem B2246573 : Blo 1496068 2246573 := bbase (se 3 (by rfl) ⟨421232, by rfl⟩ : syracuseStep 2246573 = 842465) (by norm_num)
theorem B2246597 : Blo 1496068 2246597 := bbase (se 4 (by rfl) ⟨210618, by rfl⟩ : syracuseStep 2246597 = 421237) (by norm_num)
theorem B2525141 : Blo 1496068 2525141 := bbase (se 7 (by rfl) ⟨29591, by rfl⟩ : syracuseStep 2525141 = 59183) (by norm_num)
theorem B1894357 : Blo 1496068 1894357 := bbase (se 7 (by rfl) ⟨22199, by rfl⟩ : syracuseStep 1894357 = 44399) (by norm_num)
theorem B2246621 : Blo 1496068 2246621 := bbase (se 3 (by rfl) ⟨421241, by rfl⟩ : syracuseStep 2246621 = 842483) (by norm_num)
theorem B6391781 : Blo 1496068 6391781 := bbase (se 4 (by rfl) ⟨599229, by rfl⟩ : syracuseStep 6391781 = 1198459) (by norm_num)
theorem B3368933 : Blo 1496068 3368933 := bbase (se 4 (by rfl) ⟨315837, by rfl⟩ : syracuseStep 3368933 = 631675) (by norm_num)
theorem B2246645 : Blo 1496068 2246645 := bbase (se 5 (by rfl) ⟨105311, by rfl⟩ : syracuseStep 2246645 = 210623) (by norm_num)
theorem B2246669 : Blo 1496068 2246669 := bbase (se 3 (by rfl) ⟨421250, by rfl⟩ : syracuseStep 2246669 = 842501) (by norm_num)
theorem B2246693 : Blo 1496068 2246693 := bbase (se 4 (by rfl) ⟨210627, by rfl⟩ : syracuseStep 2246693 = 421255) (by norm_num)
theorem B3369005 : Blo 1496068 3369005 := bbase (se 3 (by rfl) ⟨631688, by rfl⟩ : syracuseStep 3369005 = 1263377) (by norm_num)
theorem B6826037 : Blo 1496068 6826037 := bbase (se 5 (by rfl) ⟨319970, by rfl⟩ : syracuseStep 6826037 = 639941) (by norm_num)
theorem B2132029 : Blo 1496068 2132029 := bbase (se 3 (by rfl) ⟨399755, by rfl⟩ : syracuseStep 2132029 = 799511) (by norm_num)
theorem B2246717 : Blo 1496068 2246717 := bbase (se 3 (by rfl) ⟨421259, by rfl⟩ : syracuseStep 2246717 = 842519) (by norm_num)
theorem B2525269 : Blo 1496068 2525269 := bbase (se 8 (by rfl) ⟨14796, by rfl⟩ : syracuseStep 2525269 = 29593) (by norm_num)
theorem B2246741 : Blo 1496068 2246741 := bbase (se 8 (by rfl) ⟨13164, by rfl⟩ : syracuseStep 2246741 = 26329) (by norm_num)
theorem B2246765 : Blo 1496068 2246765 := bbase (se 3 (by rfl) ⟨421268, by rfl⟩ : syracuseStep 2246765 = 842537) (by norm_num)
theorem B3197045 : Blo 1496068 3197045 := bbase (se 5 (by rfl) ⟨149861, by rfl⟩ : syracuseStep 3197045 = 299723) (by norm_num)
theorem B3369077 : Blo 1496068 3369077 := bbase (se 5 (by rfl) ⟨157925, by rfl⟩ : syracuseStep 3369077 = 315851) (by norm_num)
theorem B1894529 : Blo 1496068 1894529 := bbase (se 2 (by rfl) ⟨710448, by rfl⟩ : syracuseStep 1894529 = 1420897) (by norm_num)
theorem B2246789 : Blo 1496068 2246789 := bbase (se 4 (by rfl) ⟨210636, by rfl⟩ : syracuseStep 2246789 = 421273) (by norm_num)
theorem B1599637 : Blo 1496068 1599637 := bbase (se 6 (by rfl) ⟨37491, by rfl⟩ : syracuseStep 1599637 = 74983) (by norm_num)
theorem B1706141 : Blo 1496068 1706141 := bbase (se 3 (by rfl) ⟨319901, by rfl⟩ : syracuseStep 1706141 = 639803) (by norm_num)
theorem B1517725 : Blo 1496068 1517725 := bbase (se 3 (by rfl) ⟨284573, by rfl⟩ : syracuseStep 1517725 = 569147) (by norm_num)
theorem B2246813 : Blo 1496068 2246813 := bbase (se 3 (by rfl) ⟨421277, by rfl⟩ : syracuseStep 2246813 = 842555) (by norm_num)
theorem B4262053 : Blo 1496068 4262053 := bbase (se 4 (by rfl) ⟨399567, by rfl⟩ : syracuseStep 4262053 = 799135) (by norm_num)
theorem B2525357 : Blo 1496068 2525357 := bbase (se 3 (by rfl) ⟨473504, by rfl⟩ : syracuseStep 2525357 = 947009) (by norm_num)
theorem B2246837 : Blo 1496068 2246837 := bbase (se 5 (by rfl) ⟨105320, by rfl⟩ : syracuseStep 2246837 = 210641) (by norm_num)
theorem B1894585 : Blo 1496068 1894585 := bbase (se 2 (by rfl) ⟨710469, by rfl⟩ : syracuseStep 1894585 = 1420939) (by norm_num)
theorem B3369149 : Blo 1496068 3369149 := bbase (se 3 (by rfl) ⟨631715, by rfl⟩ : syracuseStep 3369149 = 1263431) (by norm_num)
theorem B2246861 : Blo 1496068 2246861 := bbase (se 3 (by rfl) ⟨421286, by rfl⟩ : syracuseStep 2246861 = 842573) (by norm_num)
theorem B1599697 : Blo 1496068 1599697 := bbase (se 2 (by rfl) ⟨599886, by rfl⟩ : syracuseStep 1599697 = 1199773) (by norm_num)
theorem B2246885 : Blo 1496068 2246885 := bbase (se 4 (by rfl) ⟨210645, by rfl⟩ : syracuseStep 2246885 = 421291) (by norm_num)
theorem B2246909 : Blo 1496068 2246909 := bbase (se 3 (by rfl) ⟨421295, by rfl⟩ : syracuseStep 2246909 = 842591) (by norm_num)
theorem B3787013 : Blo 1496068 3787013 := bbase (se 4 (by rfl) ⟨355032, by rfl⟩ : syracuseStep 3787013 = 710065) (by norm_num)
theorem B3197189 : Blo 1496068 3197189 := bbase (se 4 (by rfl) ⟨299736, by rfl⟩ : syracuseStep 3197189 = 599473) (by norm_num)
theorem B3369221 : Blo 1496068 3369221 := bbase (se 4 (by rfl) ⟨315864, by rfl⟩ : syracuseStep 3369221 = 631729) (by norm_num)
theorem B2246933 : Blo 1496068 2246933 := bbase (se 6 (by rfl) ⟨52662, by rfl⟩ : syracuseStep 2246933 = 105325) (by norm_num)
theorem B1894681 : Blo 1496068 1894681 := bbase (se 2 (by rfl) ⟨710505, by rfl⟩ : syracuseStep 1894681 = 1421011) (by norm_num)
theorem B2525485 : Blo 1496068 2525485 := bbase (se 3 (by rfl) ⟨473528, by rfl⟩ : syracuseStep 2525485 = 947057) (by norm_num)
theorem B2246957 : Blo 1496068 2246957 := bbase (se 3 (by rfl) ⟨421304, by rfl⟩ : syracuseStep 2246957 = 842609) (by norm_num)
theorem B4262213 : Blo 1496068 4262213 := bbase (se 4 (by rfl) ⟨399582, by rfl⟩ : syracuseStep 4262213 = 799165) (by norm_num)
theorem B2246981 : Blo 1496068 2246981 := bbase (se 4 (by rfl) ⟨210654, by rfl⟩ : syracuseStep 2246981 = 421309) (by norm_num)
theorem B3369293 : Blo 1496068 3369293 := bbase (se 3 (by rfl) ⟨631742, by rfl⟩ : syracuseStep 3369293 = 1263485) (by norm_num)
theorem B11372885 : Blo 1496068 11372885 := bbase (se 10 (by rfl) ⟨16659, by rfl⟩ : syracuseStep 11372885 = 33319) (by norm_num)
theorem B2247005 : Blo 1496068 2247005 := bbase (se 3 (by rfl) ⟨421313, by rfl⟩ : syracuseStep 2247005 = 842627) (by norm_num)
theorem B2247029 : Blo 1496068 2247029 := bbase (se 5 (by rfl) ⟨105329, by rfl⟩ : syracuseStep 2247029 = 210659) (by norm_num)
theorem B2525573 : Blo 1496068 2525573 := bbase (se 4 (by rfl) ⟨236772, by rfl⟩ : syracuseStep 2525573 = 473545) (by norm_num)
theorem B2247053 : Blo 1496068 2247053 := bbase (se 3 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 2247053 = 842645) (by norm_num)
theorem B3369365 : Blo 1496068 3369365 := bbase (se 6 (by rfl) ⟨78969, by rfl⟩ : syracuseStep 3369365 = 157939) (by norm_num)
theorem B2247077 : Blo 1496068 2247077 := bbase (se 4 (by rfl) ⟨210663, by rfl⟩ : syracuseStep 2247077 = 421327) (by norm_num)
theorem B2247101 : Blo 1496068 2247101 := bbase (se 3 (by rfl) ⟨421331, by rfl⟩ : syracuseStep 2247101 = 842663) (by norm_num)
theorem B1894853 : Blo 1496068 1894853 := bbase (se 4 (by rfl) ⟨177642, by rfl⟩ : syracuseStep 1894853 = 355285) (by norm_num)
theorem B5687765 : Blo 1496068 5687765 := bbase (se 7 (by rfl) ⟨66653, by rfl⟩ : syracuseStep 5687765 = 133307) (by norm_num)
theorem B3369437 : Blo 1496068 3369437 := bbase (se 3 (by rfl) ⟨631769, by rfl⟩ : syracuseStep 3369437 = 1263539) (by norm_num)
theorem B1894909 : Blo 1496068 1894909 := bbase (se 3 (by rfl) ⟨355295, by rfl⟩ : syracuseStep 1894909 = 710591) (by norm_num)
theorem B2525701 : Blo 1496068 2525701 := bbase (se 4 (by rfl) ⟨236784, by rfl⟩ : syracuseStep 2525701 = 473569) (by norm_num)
theorem B3369509 : Blo 1496068 3369509 := bbase (se 4 (by rfl) ⟨315891, by rfl⟩ : syracuseStep 3369509 = 631783) (by norm_num)
theorem B4262453 : Blo 1496068 4262453 := bbase (se 5 (by rfl) ⟨199802, by rfl⟩ : syracuseStep 4262453 = 399605) (by norm_num)
theorem B3787357 : Blo 1496068 3787357 := bbase (se 3 (by rfl) ⟨710129, by rfl⟩ : syracuseStep 3787357 = 1420259) (by norm_num)
theorem B2525789 : Blo 1496068 2525789 := bbase (se 3 (by rfl) ⟨473585, by rfl⟩ : syracuseStep 2525789 = 947171) (by norm_num)
theorem B1895005 : Blo 1496068 1895005 := bbase (se 3 (by rfl) ⟨355313, by rfl⟩ : syracuseStep 1895005 = 710627) (by norm_num)
theorem B3197549 : Blo 1496068 3197549 := bbase (se 3 (by rfl) ⟨599540, by rfl⟩ : syracuseStep 3197549 = 1199081) (by norm_num)
theorem B3369581 : Blo 1496068 3369581 := bbase (se 3 (by rfl) ⟨631796, by rfl⟩ : syracuseStep 3369581 = 1263593) (by norm_num)
theorem B2697853 : Blo 1496068 2697853 := bbase (se 3 (by rfl) ⟨505847, by rfl⟩ : syracuseStep 2697853 = 1011695) (by norm_num)
theorem B3369653 : Blo 1496068 3369653 := bbase (se 5 (by rfl) ⟨157952, by rfl⟩ : syracuseStep 3369653 = 315905) (by norm_num)
theorem B3787469 : Blo 1496068 3787469 := bbase (se 3 (by rfl) ⟨710150, by rfl⟩ : syracuseStep 3787469 = 1420301) (by norm_num)
theorem B6392533 : Blo 1496068 6392533 := bbase (se 7 (by rfl) ⟨74912, by rfl⟩ : syracuseStep 6392533 = 149825) (by norm_num)
theorem B2525917 : Blo 1496068 2525917 := bbase (se 3 (by rfl) ⟨473609, by rfl⟩ : syracuseStep 2525917 = 947219) (by norm_num)
theorem B11365109 : Blo 1496068 11365109 := bbase (se 5 (by rfl) ⟨532739, by rfl⟩ : syracuseStep 11365109 = 1065479) (by norm_num)
theorem B4262645 : Blo 1496068 4262645 := bbase (se 5 (by rfl) ⟨199811, by rfl⟩ : syracuseStep 4262645 = 399623) (by norm_num)
theorem B3369725 : Blo 1496068 3369725 := bbase (se 3 (by rfl) ⟨631823, by rfl⟩ : syracuseStep 3369725 = 1263647) (by norm_num)
theorem B1895177 : Blo 1496068 1895177 := bbase (se 2 (by rfl) ⟨710691, by rfl⟩ : syracuseStep 1895177 = 1421383) (by norm_num)
theorem B3033893 : Blo 1496068 3033893 := bbase (se 4 (by rfl) ⟨284427, by rfl⟩ : syracuseStep 3033893 = 568855) (by norm_num)
theorem B2526005 : Blo 1496068 2526005 := bbase (se 5 (by rfl) ⟨118406, by rfl⟩ : syracuseStep 2526005 = 236813) (by norm_num)
theorem B1895233 : Blo 1496068 1895233 := bbase (se 2 (by rfl) ⟨710712, by rfl⟩ : syracuseStep 1895233 = 1421425) (by norm_num)
theorem B3369797 : Blo 1496068 3369797 := bbase (se 4 (by rfl) ⟨315918, by rfl⟩ : syracuseStep 3369797 = 631837) (by norm_num)
theorem B2132821 : Blo 1496068 2132821 := bbase (se 9 (by rfl) ⟨6248, by rfl⟩ : syracuseStep 2132821 = 12497) (by norm_num)
theorem B3074917 : Blo 1496068 3074917 := bbase (se 4 (by rfl) ⟨288273, by rfl⟩ : syracuseStep 3074917 = 576547) (by norm_num)
theorem B3787661 : Blo 1496068 3787661 := bbase (se 3 (by rfl) ⟨710186, by rfl⟩ : syracuseStep 3787661 = 1420373) (by norm_num)
theorem B2050957 : Blo 1496068 2050957 := bbase (se 3 (by rfl) ⟨384554, by rfl⟩ : syracuseStep 2050957 = 769109) (by norm_num)
theorem B3369869 : Blo 1496068 3369869 := bbase (se 3 (by rfl) ⟨631850, by rfl⟩ : syracuseStep 3369869 = 1263701) (by norm_num)
theorem B1895329 : Blo 1496068 1895329 := bbase (se 2 (by rfl) ⟨710748, by rfl⟩ : syracuseStep 1895329 = 1421497) (by norm_num)
theorem B5049269 : Blo 1496068 5049269 := bbase (se 5 (by rfl) ⟨236684, by rfl⟩ : syracuseStep 5049269 = 473369) (by norm_num)
theorem B2526133 : Blo 1496068 2526133 := bbase (se 5 (by rfl) ⟨118412, by rfl⟩ : syracuseStep 2526133 = 236825) (by norm_num)
theorem B3369941 : Blo 1496068 3369941 := bbase (se 7 (by rfl) ⟨39491, by rfl⟩ : syracuseStep 3369941 = 78983) (by norm_num)
theorem B2526221 : Blo 1496068 2526221 := bbase (se 3 (by rfl) ⟨473666, by rfl⟩ : syracuseStep 2526221 = 947333) (by norm_num)
theorem B3370013 : Blo 1496068 3370013 := bbase (se 3 (by rfl) ⟨631877, by rfl⟩ : syracuseStep 3370013 = 1263755) (by norm_num)
theorem B1895501 : Blo 1496068 1895501 := bbase (se 3 (by rfl) ⟨355406, by rfl⟩ : syracuseStep 1895501 = 710813) (by norm_num)
theorem B3370085 : Blo 1496068 3370085 := bbase (se 4 (by rfl) ⟨315945, by rfl⟩ : syracuseStep 3370085 = 631891) (by norm_num)
theorem B7580789 : Blo 1496068 7580789 := bbase (se 5 (by rfl) ⟨355349, by rfl⟩ : syracuseStep 7580789 = 710699) (by norm_num)
theorem B1895557 : Blo 1496068 1895557 := bbase (se 4 (by rfl) ⟨177708, by rfl⟩ : syracuseStep 1895557 = 355417) (by norm_num)
theorem B2526349 : Blo 1496068 2526349 := bbase (se 3 (by rfl) ⟨473690, by rfl⟩ : syracuseStep 2526349 = 947381) (by norm_num)
theorem B3370157 : Blo 1496068 3370157 := bbase (se 3 (by rfl) ⟨631904, by rfl⟩ : syracuseStep 3370157 = 1263809) (by norm_num)
theorem B3788005 : Blo 1496068 3788005 := bbase (se 4 (by rfl) ⟨355125, by rfl⟩ : syracuseStep 3788005 = 710251) (by norm_num)
theorem B2526437 : Blo 1496068 2526437 := bbase (se 4 (by rfl) ⟨236853, by rfl⟩ : syracuseStep 2526437 = 473707) (by norm_num)
theorem B1895653 : Blo 1496068 1895653 := bbase (se 4 (by rfl) ⟨177717, by rfl⟩ : syracuseStep 1895653 = 355435) (by norm_num)
theorem B3239149 : Blo 1496068 3239149 := bbase (se 3 (by rfl) ⟨607340, by rfl⟩ : syracuseStep 3239149 = 1214681) (by norm_num)
theorem B3370229 : Blo 1496068 3370229 := bbase (se 5 (by rfl) ⟨157979, by rfl⟩ : syracuseStep 3370229 = 315959) (by norm_num)
theorem B3370301 : Blo 1496068 3370301 := bbase (se 3 (by rfl) ⟨631931, by rfl⟩ : syracuseStep 3370301 = 1263863) (by norm_num)
theorem B3788117 : Blo 1496068 3788117 := bbase (se 11 (by rfl) ⟨2774, by rfl⟩ : syracuseStep 3788117 = 5549) (by norm_num)
theorem B5049701 : Blo 1496068 5049701 := bbase (se 4 (by rfl) ⟨473409, by rfl⟩ : syracuseStep 5049701 = 946819) (by norm_num)
theorem B2526565 : Blo 1496068 2526565 := bbase (se 4 (by rfl) ⟨236865, by rfl⟩ : syracuseStep 2526565 = 473731) (by norm_num)
theorem B1822061 : Blo 1496068 1822061 := bbase (se 3 (by rfl) ⟨341636, by rfl⟩ : syracuseStep 1822061 = 683273) (by norm_num)
theorem B3370373 : Blo 1496068 3370373 := bbase (se 4 (by rfl) ⟨315972, by rfl⟩ : syracuseStep 3370373 = 631945) (by norm_num)
theorem B1895825 : Blo 1496068 1895825 := bbase (se 2 (by rfl) ⟨710934, by rfl⟩ : syracuseStep 1895825 = 1421869) (by norm_num)
theorem B6393269 : Blo 1496068 6393269 := bbase (se 5 (by rfl) ⟨299684, by rfl⟩ : syracuseStep 6393269 = 599369) (by norm_num)
theorem B3239357 : Blo 1496068 3239357 := bbase (se 3 (by rfl) ⟨607379, by rfl⟩ : syracuseStep 3239357 = 1214759) (by norm_num)
theorem B2526653 : Blo 1496068 2526653 := bbase (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) (by norm_num)
theorem B5393861 : Blo 1496068 5393861 := bbase (se 4 (by rfl) ⟨505674, by rfl⟩ : syracuseStep 5393861 = 1011349) (by norm_num)
theorem B3034565 : Blo 1496068 3034565 := bbase (se 4 (by rfl) ⟨284490, by rfl⟩ : syracuseStep 3034565 = 568981) (by norm_num)
theorem B1895881 : Blo 1496068 1895881 := bbase (se 2 (by rfl) ⟨710955, by rfl⟩ : syracuseStep 1895881 = 1421911) (by norm_num)
theorem B3370445 : Blo 1496068 3370445 := bbase (se 3 (by rfl) ⟨631958, by rfl⟩ : syracuseStep 3370445 = 1263917) (by norm_num)
theorem B14396885 : Blo 1496068 14396885 := bbase (se 7 (by rfl) ⟨168713, by rfl⟩ : syracuseStep 14396885 = 337427) (by norm_num)
theorem B3198437 : Blo 1496068 3198437 := bbase (se 4 (by rfl) ⟨299853, by rfl⟩ : syracuseStep 3198437 = 599707) (by norm_num)
theorem B3788309 : Blo 1496068 3788309 := bbase (se 6 (by rfl) ⟨88788, by rfl⟩ : syracuseStep 3788309 = 177577) (by norm_num)
theorem B3370517 : Blo 1496068 3370517 := bbase (se 6 (by rfl) ⟨78996, by rfl⟩ : syracuseStep 3370517 = 157993) (by norm_num)
theorem B1895977 : Blo 1496068 1895977 := bbase (se 2 (by rfl) ⟨710991, by rfl⟩ : syracuseStep 1895977 = 1421983) (by norm_num)
theorem B2526781 : Blo 1496068 2526781 := bbase (se 3 (by rfl) ⟨473771, by rfl⟩ : syracuseStep 2526781 = 947543) (by norm_num)
theorem B3370589 : Blo 1496068 3370589 := bbase (se 3 (by rfl) ⟨631985, by rfl⟩ : syracuseStep 3370589 = 1263971) (by norm_num)
theorem B1683085 : Blo 1496068 1683085 := bbase (se 3 (by rfl) ⟨315578, by rfl⟩ : syracuseStep 1683085 = 631157) (by norm_num)
theorem B2526869 : Blo 1496068 2526869 := bbase (se 6 (by rfl) ⟨59223, by rfl⟩ : syracuseStep 2526869 = 118447) (by norm_num)
theorem B1683121 : Blo 1496068 1683121 := bbase (se 2 (by rfl) ⟨631170, by rfl⟩ : syracuseStep 1683121 = 1262341) (by norm_num)
theorem B1683157 : Blo 1496068 1683157 := bbase (se 7 (by rfl) ⟨19724, by rfl⟩ : syracuseStep 1683157 = 39449) (by norm_num)
theorem B4263637 : Blo 1496068 4263637 := bbase (se 7 (by rfl) ⟨49964, by rfl⟩ : syracuseStep 4263637 = 99929) (by norm_num)
theorem B8531669 : Blo 1496068 8531669 := bbase (se 7 (by rfl) ⟨99980, by rfl⟩ : syracuseStep 8531669 = 199961) (by norm_num)
theorem B3198685 : Blo 1496068 3198685 := bbase (se 3 (by rfl) ⟨599753, by rfl⟩ : syracuseStep 3198685 = 1199507) (by norm_num)
theorem B1683193 : Blo 1496068 1683193 := bbase (se 2 (by rfl) ⟨631197, by rfl⟩ : syracuseStep 1683193 = 1262395) (by norm_num)
theorem B1797881 : Blo 1496068 1797881 := bbase (se 2 (by rfl) ⟨674205, by rfl⟩ : syracuseStep 1797881 = 1348411) (by norm_num)
theorem B5050133 : Blo 1496068 5050133 := bbase (se 6 (by rfl) ⟨118362, by rfl⟩ : syracuseStep 5050133 = 236725) (by norm_num)
theorem B2526997 : Blo 1496068 2526997 := bbase (se 6 (by rfl) ⟨59226, by rfl⟩ : syracuseStep 2526997 = 118453) (by norm_num)
theorem B9596693 : Blo 1496068 9596693 := bbase (se 6 (by rfl) ⟨224922, by rfl⟩ : syracuseStep 9596693 = 449845) (by norm_num)
theorem B1683229 : Blo 1496068 1683229 := bbase (se 3 (by rfl) ⟨315605, by rfl⟩ : syracuseStep 1683229 = 631211) (by norm_num)
theorem B1683265 : Blo 1496068 1683265 := bbase (se 2 (by rfl) ⟨631224, by rfl⟩ : syracuseStep 1683265 = 1262449) (by norm_num)
theorem B1683301 : Blo 1496068 1683301 := bbase (se 4 (by rfl) ⟨157809, by rfl⟩ : syracuseStep 1683301 = 315619) (by norm_num)
theorem B3788653 : Blo 1496068 3788653 := bbase (se 3 (by rfl) ⟨710372, by rfl⟩ : syracuseStep 3788653 = 1420745) (by norm_num)
theorem B2527085 : Blo 1496068 2527085 := bbase (se 3 (by rfl) ⟨473828, by rfl⟩ : syracuseStep 2527085 = 947657) (by norm_num)
theorem B1683337 : Blo 1496068 1683337 := bbase (se 2 (by rfl) ⟨631251, by rfl⟩ : syracuseStep 1683337 = 1262503) (by norm_num)
theorem B1945513 : Blo 1496068 1945513 := bbase (se 2 (by rfl) ⟨729567, by rfl⟩ : syracuseStep 1945513 = 1459135) (by norm_num)
theorem B1683373 : Blo 1496068 1683373 := bbase (se 3 (by rfl) ⟨315632, by rfl⟩ : syracuseStep 1683373 = 631265) (by norm_num)
theorem B1683409 : Blo 1496068 1683409 := bbase (se 2 (by rfl) ⟨631278, by rfl⟩ : syracuseStep 1683409 = 1262557) (by norm_num)
theorem B3788765 : Blo 1496068 3788765 := bbase (se 3 (by rfl) ⟨710393, by rfl⟩ : syracuseStep 3788765 = 1420787) (by norm_num)
theorem B2527213 : Blo 1496068 2527213 := bbase (se 3 (by rfl) ⟨473852, by rfl⟩ : syracuseStep 2527213 = 947705) (by norm_num)
theorem B1683445 : Blo 1496068 1683445 := bbase (se 5 (by rfl) ⟨78911, by rfl⟩ : syracuseStep 1683445 = 157823) (by norm_num)
theorem B1683481 : Blo 1496068 1683481 := bbase (se 2 (by rfl) ⟨631305, by rfl⟩ : syracuseStep 1683481 = 1262611) (by norm_num)
theorem B1683517 : Blo 1496068 1683517 := bbase (se 3 (by rfl) ⟨315659, by rfl⟩ : syracuseStep 1683517 = 631319) (by norm_num)
theorem B2527301 : Blo 1496068 2527301 := bbase (se 4 (by rfl) ⟨236934, by rfl⟩ : syracuseStep 2527301 = 473869) (by norm_num)
theorem B4796501 : Blo 1496068 4796501 := bbase (se 8 (by rfl) ⟨28104, by rfl⟩ : syracuseStep 4796501 = 56209) (by norm_num)
theorem B1683553 : Blo 1496068 1683553 := bbase (se 2 (by rfl) ⟨631332, by rfl⟩ : syracuseStep 1683553 = 1262665) (by norm_num)
theorem B4550789 : Blo 1496068 4550789 := bbase (se 4 (by rfl) ⟨426636, by rfl⟩ : syracuseStep 4550789 = 853273) (by norm_num)
theorem B1683589 : Blo 1496068 1683589 := bbase (se 4 (by rfl) ⟨157836, by rfl⟩ : syracuseStep 1683589 = 315673) (by norm_num)
theorem B3788957 : Blo 1496068 3788957 := bbase (se 3 (by rfl) ⟨710429, by rfl⟩ : syracuseStep 3788957 = 1420859) (by norm_num)
theorem B1683625 : Blo 1496068 1683625 := bbase (se 2 (by rfl) ⟨631359, by rfl⟩ : syracuseStep 1683625 = 1262719) (by norm_num)
theorem B5050565 : Blo 1496068 5050565 := bbase (se 4 (by rfl) ⟨473490, by rfl⟩ : syracuseStep 5050565 = 946981) (by norm_num)
theorem B2527429 : Blo 1496068 2527429 := bbase (se 4 (by rfl) ⟨236946, by rfl⟩ : syracuseStep 2527429 = 473893) (by norm_num)
theorem B1683661 : Blo 1496068 1683661 := bbase (se 3 (by rfl) ⟨315686, by rfl⟩ : syracuseStep 1683661 = 631373) (by norm_num)
theorem B3199189 : Blo 1496068 3199189 := bbase (se 7 (by rfl) ⟨37490, by rfl⟩ : syracuseStep 3199189 = 74981) (by norm_num)
theorem B1683697 : Blo 1496068 1683697 := bbase (se 2 (by rfl) ⟨631386, by rfl⟩ : syracuseStep 1683697 = 1262773) (by norm_num)
theorem B1683733 : Blo 1496068 1683733 := bbase (se 6 (by rfl) ⟨39462, by rfl⟩ : syracuseStep 1683733 = 78925) (by norm_num)
theorem B2527517 : Blo 1496068 2527517 := bbase (se 3 (by rfl) ⟨473909, by rfl⟩ : syracuseStep 2527517 = 947819) (by norm_num)
theorem B5681461 : Blo 1496068 5681461 := bbase (se 5 (by rfl) ⟨266318, by rfl⟩ : syracuseStep 5681461 = 532637) (by norm_num)
theorem B1683769 : Blo 1496068 1683769 := bbase (se 2 (by rfl) ⟨631413, by rfl⟩ : syracuseStep 1683769 = 1262827) (by norm_num)
theorem B1683805 : Blo 1496068 1683805 := bbase (se 3 (by rfl) ⟨315713, by rfl⟩ : syracuseStep 1683805 = 631427) (by norm_num)
theorem B2429309 : Blo 1496068 2429309 := bbase (se 3 (by rfl) ⟨455495, by rfl⟩ : syracuseStep 2429309 = 910991) (by norm_num)
theorem B1683841 : Blo 1496068 1683841 := bbase (se 2 (by rfl) ⟨631440, by rfl⟩ : syracuseStep 1683841 = 1262881) (by norm_num)
theorem B7582085 : Blo 1496068 7582085 := bbase (se 4 (by rfl) ⟨710820, by rfl⟩ : syracuseStep 7582085 = 1421641) (by norm_num)
theorem B2527645 : Blo 1496068 2527645 := bbase (se 3 (by rfl) ⟨473933, by rfl⟩ : syracuseStep 2527645 = 947867) (by norm_num)
theorem B1683877 : Blo 1496068 1683877 := bbase (se 4 (by rfl) ⟨157863, by rfl⟩ : syracuseStep 1683877 = 315727) (by norm_num)
theorem B1798573 : Blo 1496068 1798573 := bbase (se 3 (by rfl) ⟨337232, by rfl⟩ : syracuseStep 1798573 = 674465) (by norm_num)
theorem B1683913 : Blo 1496068 1683913 := bbase (se 2 (by rfl) ⟨631467, by rfl⟩ : syracuseStep 1683913 = 1262935) (by norm_num)
theorem B1683949 : Blo 1496068 1683949 := bbase (se 3 (by rfl) ⟨315740, by rfl⟩ : syracuseStep 1683949 = 631481) (by norm_num)
theorem B3789301 : Blo 1496068 3789301 := bbase (se 5 (by rfl) ⟨177623, by rfl⟩ : syracuseStep 3789301 = 355247) (by norm_num)
theorem B2527733 : Blo 1496068 2527733 := bbase (se 5 (by rfl) ⟨118487, by rfl⟩ : syracuseStep 2527733 = 236975) (by norm_num)
theorem B1798669 : Blo 1496068 1798669 := bbase (se 3 (by rfl) ⟨337250, by rfl⟩ : syracuseStep 1798669 = 674501) (by norm_num)
theorem B1683985 : Blo 1496068 1683985 := bbase (se 2 (by rfl) ⟨631494, by rfl⟩ : syracuseStep 1683985 = 1262989) (by norm_num)
theorem B1684021 : Blo 1496068 1684021 := bbase (se 5 (by rfl) ⟨78938, by rfl⟩ : syracuseStep 1684021 = 157877) (by norm_num)
theorem B1684057 : Blo 1496068 1684057 := bbase (se 2 (by rfl) ⟨631521, by rfl⟩ : syracuseStep 1684057 = 1263043) (by norm_num)
theorem B2396765 : Blo 1496068 2396765 := bbase (se 3 (by rfl) ⟨449393, by rfl⟩ : syracuseStep 2396765 = 898787) (by norm_num)
theorem B5681765 : Blo 1496068 5681765 := bbase (se 4 (by rfl) ⟨532665, by rfl⟩ : syracuseStep 5681765 = 1065331) (by norm_num)
theorem B3789413 : Blo 1496068 3789413 := bbase (se 4 (by rfl) ⟨355257, by rfl⟩ : syracuseStep 3789413 = 710515) (by norm_num)
theorem B5050997 : Blo 1496068 5050997 := bbase (se 5 (by rfl) ⟨236765, by rfl⟩ : syracuseStep 5050997 = 473531) (by norm_num)
theorem B2527861 : Blo 1496068 2527861 := bbase (se 5 (by rfl) ⟨118493, by rfl⟩ : syracuseStep 2527861 = 236987) (by norm_num)
theorem B1684093 : Blo 1496068 1684093 := bbase (se 3 (by rfl) ⟨315767, by rfl⟩ : syracuseStep 1684093 = 631535) (by norm_num)
theorem B1684129 : Blo 1496068 1684129 := bbase (se 2 (by rfl) ⟨631548, by rfl⟩ : syracuseStep 1684129 = 1263097) (by norm_num)
theorem B7197349 : Blo 1496068 7197349 := bbase (se 4 (by rfl) ⟨674751, by rfl⟩ : syracuseStep 7197349 = 1349503) (by norm_num)
theorem B1684165 : Blo 1496068 1684165 := bbase (se 4 (by rfl) ⟨157890, by rfl⟩ : syracuseStep 1684165 = 315781) (by norm_num)
theorem B2527949 : Blo 1496068 2527949 := bbase (se 3 (by rfl) ⟨473990, by rfl⟩ : syracuseStep 2527949 = 947981) (by norm_num)
theorem B2396893 : Blo 1496068 2396893 := bbase (se 3 (by rfl) ⟨449417, by rfl⟩ : syracuseStep 2396893 = 898835) (by norm_num)
theorem B1684201 : Blo 1496068 1684201 := bbase (se 2 (by rfl) ⟨631575, by rfl⟩ : syracuseStep 1684201 = 1263151) (by norm_num)
theorem B1684237 : Blo 1496068 1684237 := bbase (se 3 (by rfl) ⟨315794, by rfl⟩ : syracuseStep 1684237 = 631589) (by norm_num)
theorem B7574309 : Blo 1496068 7574309 := bbase (se 4 (by rfl) ⟨710091, by rfl⟩ : syracuseStep 7574309 = 1420183) (by norm_num)
theorem B3789605 : Blo 1496068 3789605 := bbase (se 4 (by rfl) ⟨355275, by rfl⟩ : syracuseStep 3789605 = 710551) (by norm_num)
theorem B4264741 : Blo 1496068 4264741 := bbase (se 4 (by rfl) ⟨399819, by rfl⟩ : syracuseStep 4264741 = 799639) (by norm_num)
theorem B1684273 : Blo 1496068 1684273 := bbase (se 2 (by rfl) ⟨631602, by rfl⟩ : syracuseStep 1684273 = 1263205) (by norm_num)
theorem B1684309 : Blo 1496068 1684309 := bbase (se 9 (by rfl) ⟨4934, by rfl⟩ : syracuseStep 1684309 = 9869) (by norm_num)
theorem B19452757 : Blo 1496068 19452757 := bbase (se 9 (by rfl) ⟨56990, by rfl⟩ : syracuseStep 19452757 = 113981) (by norm_num)
theorem B1684345 : Blo 1496068 1684345 := bbase (se 2 (by rfl) ⟨631629, by rfl⟩ : syracuseStep 1684345 = 1263259) (by norm_num)
theorem B1684381 : Blo 1496068 1684381 := bbase (se 3 (by rfl) ⟨315821, by rfl⟩ : syracuseStep 1684381 = 631643) (by norm_num)
theorem B1684417 : Blo 1496068 1684417 := bbase (se 2 (by rfl) ⟨631656, by rfl⟩ : syracuseStep 1684417 = 1263313) (by norm_num)
theorem B1684453 : Blo 1496068 1684453 := bbase (se 4 (by rfl) ⟨157917, by rfl⟩ : syracuseStep 1684453 = 315835) (by norm_num)
theorem B4797413 : Blo 1496068 4797413 := bbase (se 4 (by rfl) ⟨449757, by rfl⟩ : syracuseStep 4797413 = 899515) (by norm_num)
theorem B1684489 : Blo 1496068 1684489 := bbase (se 2 (by rfl) ⟨631683, by rfl⟩ : syracuseStep 1684489 = 1263367) (by norm_num)
theorem B5051429 : Blo 1496068 5051429 := bbase (se 4 (by rfl) ⟨473571, by rfl⟩ : syracuseStep 5051429 = 947143) (by norm_num)
theorem B1684525 : Blo 1496068 1684525 := bbase (se 3 (by rfl) ⟨315848, by rfl⟩ : syracuseStep 1684525 = 631697) (by norm_num)
theorem B1684561 : Blo 1496068 1684561 := bbase (se 2 (by rfl) ⟨631710, by rfl⟩ : syracuseStep 1684561 = 1263421) (by norm_num)
theorem B2397277 : Blo 1496068 2397277 := bbase (se 3 (by rfl) ⟨449489, by rfl⟩ : syracuseStep 2397277 = 898979) (by norm_num)
theorem B1684597 : Blo 1496068 1684597 := bbase (se 5 (by rfl) ⟨78965, by rfl⟩ : syracuseStep 1684597 = 157931) (by norm_num)
theorem B3789949 : Blo 1496068 3789949 := bbase (se 3 (by rfl) ⟨710615, by rfl⟩ : syracuseStep 3789949 = 1421231) (by norm_num)
theorem B3036293 : Blo 1496068 3036293 := bbase (se 4 (by rfl) ⟨284652, by rfl⟩ : syracuseStep 3036293 = 569305) (by norm_num)
theorem B1684633 : Blo 1496068 1684633 := bbase (se 2 (by rfl) ⟨631737, by rfl⟩ : syracuseStep 1684633 = 1263475) (by norm_num)
theorem B3036325 : Blo 1496068 3036325 := bbase (se 4 (by rfl) ⟨284655, by rfl⟩ : syracuseStep 3036325 = 569311) (by norm_num)
theorem B1684669 : Blo 1496068 1684669 := bbase (se 3 (by rfl) ⟨315875, by rfl⟩ : syracuseStep 1684669 = 631751) (by norm_num)
theorem B7189717 : Blo 1496068 7189717 := bbase (se 7 (by rfl) ⟨84254, by rfl⟩ : syracuseStep 7189717 = 168509) (by norm_num)
theorem B2561237 : Blo 1496068 2561237 := bbase (se 7 (by rfl) ⟨30014, by rfl⟩ : syracuseStep 2561237 = 60029) (by norm_num)
theorem B1684705 : Blo 1496068 1684705 := bbase (se 2 (by rfl) ⟨631764, by rfl⟩ : syracuseStep 1684705 = 1263529) (by norm_num)
theorem B3790061 : Blo 1496068 3790061 := bbase (se 3 (by rfl) ⟨710636, by rfl⟩ : syracuseStep 3790061 = 1421273) (by norm_num)
theorem B3077357 : Blo 1496068 3077357 := bbase (se 3 (by rfl) ⟨577004, by rfl⟩ : syracuseStep 3077357 = 1154009) (by norm_num)
theorem B1946873 : Blo 1496068 1946873 := bbase (se 2 (by rfl) ⟨730077, by rfl⟩ : syracuseStep 1946873 = 1460155) (by norm_num)
theorem B1684741 : Blo 1496068 1684741 := bbase (se 4 (by rfl) ⟨157944, by rfl⟩ : syracuseStep 1684741 = 315889) (by norm_num)
theorem B1799453 : Blo 1496068 1799453 := bbase (se 3 (by rfl) ⟨337397, by rfl⟩ : syracuseStep 1799453 = 674795) (by norm_num)
theorem B1684777 : Blo 1496068 1684777 := bbase (se 2 (by rfl) ⟨631791, by rfl⟩ : syracuseStep 1684777 = 1263583) (by norm_num)
theorem B14390581 : Blo 1496068 14390581 := bbase (se 5 (by rfl) ⟨674558, by rfl⟩ : syracuseStep 14390581 = 1349117) (by norm_num)
theorem B2159941 : Blo 1496068 2159941 := bbase (se 4 (by rfl) ⟨202494, by rfl⟩ : syracuseStep 2159941 = 404989) (by norm_num)
theorem B1684813 : Blo 1496068 1684813 := bbase (se 3 (by rfl) ⟨315902, by rfl⟩ : syracuseStep 1684813 = 631805) (by norm_num)
theorem B2397533 : Blo 1496068 2397533 := bbase (se 3 (by rfl) ⟨449537, by rfl⟩ : syracuseStep 2397533 = 899075) (by norm_num)
theorem B1684849 : Blo 1496068 1684849 := bbase (se 2 (by rfl) ⟨631818, by rfl⟩ : syracuseStep 1684849 = 1263637) (by norm_num)
theorem B1684885 : Blo 1496068 1684885 := bbase (se 6 (by rfl) ⟨39489, by rfl⟩ : syracuseStep 1684885 = 78979) (by norm_num)
theorem B3790253 : Blo 1496068 3790253 := bbase (se 3 (by rfl) ⟨710672, by rfl⟩ : syracuseStep 3790253 = 1421345) (by norm_num)
theorem B1684921 : Blo 1496068 1684921 := bbase (se 2 (by rfl) ⟨631845, by rfl⟩ : syracuseStep 1684921 = 1263691) (by norm_num)
theorem B48534997 : Blo 1496068 48534997 := bbase (se 7 (by rfl) ⟨568769, by rfl⟩ : syracuseStep 48534997 = 1137539) (by norm_num)
theorem B5051861 : Blo 1496068 5051861 := bbase (se 7 (by rfl) ⟨59201, by rfl⟩ : syracuseStep 5051861 = 118403) (by norm_num)
theorem B1684957 : Blo 1496068 1684957 := bbase (se 3 (by rfl) ⟨315929, by rfl⟩ : syracuseStep 1684957 = 631859) (by norm_num)
theorem B3413477 : Blo 1496068 3413477 := bbase (se 4 (by rfl) ⟨320013, by rfl⟩ : syracuseStep 3413477 = 640027) (by norm_num)
theorem B1684993 : Blo 1496068 1684993 := bbase (se 2 (by rfl) ⟨631872, by rfl⟩ : syracuseStep 1684993 = 1263745) (by norm_num)
theorem B1685029 : Blo 1496068 1685029 := bbase (se 4 (by rfl) ⟨157971, by rfl⟩ : syracuseStep 1685029 = 315943) (by norm_num)
theorem B2430517 : Blo 1496068 2430517 := bbase (se 5 (by rfl) ⟨113930, by rfl⟩ : syracuseStep 2430517 = 227861) (by norm_num)
theorem B9229877 : Blo 1496068 9229877 := bbase (se 5 (by rfl) ⟨432650, by rfl⟩ : syracuseStep 9229877 = 865301) (by norm_num)
theorem B1685065 : Blo 1496068 1685065 := bbase (se 2 (by rfl) ⟨631899, by rfl⟩ : syracuseStep 1685065 = 1263799) (by norm_num)
theorem B1685101 : Blo 1496068 1685101 := bbase (se 3 (by rfl) ⟨315956, by rfl⟩ : syracuseStep 1685101 = 631913) (by norm_num)
theorem B10786421 : Blo 1496068 10786421 := bbase (se 5 (by rfl) ⟨505613, by rfl⟩ : syracuseStep 10786421 = 1011227) (by norm_num)
theorem B2561653 : Blo 1496068 2561653 := bbase (se 5 (by rfl) ⟨120077, by rfl⟩ : syracuseStep 2561653 = 240155) (by norm_num)
theorem B1685137 : Blo 1496068 1685137 := bbase (se 2 (by rfl) ⟨631926, by rfl⟩ : syracuseStep 1685137 = 1263853) (by norm_num)
theorem B7583381 : Blo 1496068 7583381 := bbase (se 6 (by rfl) ⟨177735, by rfl⟩ : syracuseStep 7583381 = 355471) (by norm_num)
theorem B3118765 : Blo 1496068 3118765 := bbase (se 3 (by rfl) ⟨584768, by rfl⟩ : syracuseStep 3118765 = 1169537) (by norm_num)
theorem B1685173 : Blo 1496068 1685173 := bbase (se 5 (by rfl) ⟨78992, by rfl⟩ : syracuseStep 1685173 = 157985) (by norm_num)
theorem B1685209 : Blo 1496068 1685209 := bbase (se 2 (by rfl) ⟨631953, by rfl⟩ : syracuseStep 1685209 = 1263907) (by norm_num)
theorem B1685245 : Blo 1496068 1685245 := bbase (se 3 (by rfl) ⟨315983, by rfl⟩ : syracuseStep 1685245 = 631967) (by norm_num)
theorem B3790597 : Blo 1496068 3790597 := bbase (se 4 (by rfl) ⟨355368, by rfl⟩ : syracuseStep 3790597 = 710737) (by norm_num)
theorem B1685281 : Blo 1496068 1685281 := bbase (se 2 (by rfl) ⟨631980, by rfl⟩ : syracuseStep 1685281 = 1263961) (by norm_num)
theorem B2561861 : Blo 1496068 2561861 := bbase (se 4 (by rfl) ⟨240174, by rfl⟩ : syracuseStep 2561861 = 480349) (by norm_num)
theorem B1685317 : Blo 1496068 1685317 := bbase (se 4 (by rfl) ⟨157998, by rfl⟩ : syracuseStep 1685317 = 315997) (by norm_num)
theorem B3790709 : Blo 1496068 3790709 := bbase (se 5 (by rfl) ⟨177689, by rfl⟩ : syracuseStep 3790709 = 355379) (by norm_num)
theorem B5052293 : Blo 1496068 5052293 := bbase (se 4 (by rfl) ⟨473652, by rfl⟩ : syracuseStep 5052293 = 947305) (by norm_num)
theorem B2275213 : Blo 1496068 2275213 := bbase (se 3 (by rfl) ⟨426602, by rfl⟩ : syracuseStep 2275213 = 853205) (by norm_num)
theorem B7575605 : Blo 1496068 7575605 := bbase (se 5 (by rfl) ⟨355106, by rfl⟩ : syracuseStep 7575605 = 710213) (by norm_num)
theorem B3790901 : Blo 1496068 3790901 := bbase (se 5 (by rfl) ⟨177698, by rfl⟩ : syracuseStep 3790901 = 355397) (by norm_num)
theorem B2562173 : Blo 1496068 2562173 := bbase (se 3 (by rfl) ⟨480407, by rfl⟩ : syracuseStep 2562173 = 960815) (by norm_num)
theorem B2398405 : Blo 1496068 2398405 := bbase (se 4 (by rfl) ⟨224850, by rfl⟩ : syracuseStep 2398405 = 449701) (by norm_num)
theorem B6830309 : Blo 1496068 6830309 := bbase (se 4 (by rfl) ⟨640341, by rfl⟩ : syracuseStep 6830309 = 1280683) (by norm_num)
theorem B2275565 : Blo 1496068 2275565 := bbase (se 3 (by rfl) ⟨426668, by rfl⟩ : syracuseStep 2275565 = 853337) (by norm_num)
theorem B8091893 : Blo 1496068 8091893 := bbase (se 5 (by rfl) ⟨379307, by rfl⟩ : syracuseStep 8091893 = 758615) (by norm_num)
theorem B2840845 : Blo 1496068 2840845 := bbase (se 3 (by rfl) ⟨532658, by rfl⟩ : syracuseStep 2840845 = 1065317) (by norm_num)
theorem B2398501 : Blo 1496068 2398501 := bbase (se 4 (by rfl) ⟨224859, by rfl⟩ : syracuseStep 2398501 = 449719) (by norm_num)
theorem B2881829 : Blo 1496068 2881829 := bbase (se 4 (by rfl) ⟨270171, by rfl⟩ : syracuseStep 2881829 = 540343) (by norm_num)
theorem B4798757 : Blo 1496068 4798757 := bbase (se 4 (by rfl) ⟨449883, by rfl⟩ : syracuseStep 4798757 = 899767) (by norm_num)
theorem B5052725 : Blo 1496068 5052725 := bbase (se 5 (by rfl) ⟨236846, by rfl⟩ : syracuseStep 5052725 = 473693) (by norm_num)
theorem B3791245 : Blo 1496068 3791245 := bbase (se 3 (by rfl) ⟨710858, by rfl⟩ : syracuseStep 3791245 = 1421717) (by norm_num)
theorem B2840989 : Blo 1496068 2840989 := bbase (se 3 (by rfl) ⟨532685, by rfl⟩ : syracuseStep 2840989 = 1065371) (by norm_num)
theorem B2398661 : Blo 1496068 2398661 := bbase (se 4 (by rfl) ⟨224874, by rfl⟩ : syracuseStep 2398661 = 449749) (by norm_num)
theorem B8526293 : Blo 1496068 8526293 := bbase (se 7 (by rfl) ⟨99917, by rfl⟩ : syracuseStep 8526293 = 199835) (by norm_num)
theorem B3594725 : Blo 1496068 3594725 := bbase (se 4 (by rfl) ⟨337005, by rfl⟩ : syracuseStep 3594725 = 674011) (by norm_num)
theorem B3791357 : Blo 1496068 3791357 := bbase (se 3 (by rfl) ⟨710879, by rfl⟩ : syracuseStep 3791357 = 1421759) (by norm_num)
theorem B2841149 : Blo 1496068 2841149 := bbase (se 3 (by rfl) ⟨532715, by rfl⟩ : syracuseStep 2841149 = 1065431) (by norm_num)
theorem B4381253 : Blo 1496068 4381253 := bbase (se 4 (by rfl) ⟨410742, by rfl⟩ : syracuseStep 4381253 = 821485) (by norm_num)
theorem B6396565 : Blo 1496068 6396565 := bbase (se 6 (by rfl) ⟨149919, by rfl⟩ : syracuseStep 6396565 = 299839) (by norm_num)
theorem B5683877 : Blo 1496068 5683877 := bbase (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) (by norm_num)
theorem B3791549 : Blo 1496068 3791549 := bbase (se 3 (by rfl) ⟨710915, by rfl⟩ : syracuseStep 3791549 = 1421831) (by norm_num)
theorem B2841293 : Blo 1496068 2841293 := bbase (se 3 (by rfl) ⟨532742, by rfl⟩ : syracuseStep 2841293 = 1065485) (by norm_num)
theorem B5053157 : Blo 1496068 5053157 := bbase (se 4 (by rfl) ⟨473733, by rfl⟩ : syracuseStep 5053157 = 947467) (by norm_num)
theorem B3595013 : Blo 1496068 3595013 := bbase (se 4 (by rfl) ⟨337032, by rfl⟩ : syracuseStep 3595013 = 674065) (by norm_num)
theorem B6478613 : Blo 1496068 6478613 := bbase (se 6 (by rfl) ⟨151842, by rfl⟩ : syracuseStep 6478613 = 303685) (by norm_num)
theorem B5684165 : Blo 1496068 5684165 := bbase (se 4 (by rfl) ⟨532890, by rfl⟩ : syracuseStep 5684165 = 1065781) (by norm_num)
theorem B2841581 : Blo 1496068 2841581 := bbase (se 3 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 2841581 = 1065593) (by norm_num)
theorem B3791893 : Blo 1496068 3791893 := bbase (se 6 (by rfl) ⟨88872, by rfl⟩ : syracuseStep 3791893 = 177745) (by norm_num)
theorem B2276429 : Blo 1496068 2276429 := bbase (se 3 (by rfl) ⟨426830, by rfl⟩ : syracuseStep 2276429 = 853661) (by norm_num)
theorem B2841733 : Blo 1496068 2841733 := bbase (se 4 (by rfl) ⟨266412, by rfl⟩ : syracuseStep 2841733 = 532825) (by norm_num)
theorem B5053589 : Blo 1496068 5053589 := bbase (se 6 (by rfl) ⟨118443, by rfl⟩ : syracuseStep 5053589 = 236887) (by norm_num)
theorem B2161829 : Blo 1496068 2161829 := bbase (se 4 (by rfl) ⟨202671, by rfl⟩ : syracuseStep 2161829 = 405343) (by norm_num)
theorem B12147893 : Blo 1496068 12147893 := bbase (se 5 (by rfl) ⟨569432, by rfl⟩ : syracuseStep 12147893 = 1138865) (by norm_num)
theorem B3415229 : Blo 1496068 3415229 := bbase (se 3 (by rfl) ⟨640355, by rfl⟩ : syracuseStep 3415229 = 1280711) (by norm_num)
theorem B1621289 : Blo 1496068 1621289 := bbase (se 2 (by rfl) ⟨607983, by rfl⟩ : syracuseStep 1621289 = 1215967) (by norm_num)
theorem B3366197 : Blo 1496068 3366197 := bbase (se 5 (by rfl) ⟨157790, by rfl⟩ : syracuseStep 3366197 = 315581) (by norm_num)
theorem B7576901 : Blo 1496068 7576901 := bbase (se 4 (by rfl) ⟨710334, by rfl⟩ : syracuseStep 7576901 = 1420669) (by norm_num)
theorem B3366269 : Blo 1496068 3366269 := bbase (se 3 (by rfl) ⟨631175, by rfl⟩ : syracuseStep 3366269 = 1262351) (by norm_num)
theorem B2842037 : Blo 1496068 2842037 := bbase (se 5 (by rfl) ⟨133220, by rfl⟩ : syracuseStep 2842037 = 266441) (by norm_num)
theorem B12795317 : Blo 1496068 12795317 := bbase (se 5 (by rfl) ⟨599780, by rfl⟩ : syracuseStep 12795317 = 1199561) (by norm_num)
theorem B3366341 : Blo 1496068 3366341 := bbase (se 4 (by rfl) ⟨315594, by rfl⟩ : syracuseStep 3366341 = 631189) (by norm_num)
theorem B1973705 : Blo 1496068 1973705 := bbase (se 2 (by rfl) ⟨740139, by rfl⟩ : syracuseStep 1973705 = 1480279) (by norm_num)
theorem B4554245 : Blo 1496068 4554245 := bbase (se 4 (by rfl) ⟨426960, by rfl⟩ : syracuseStep 4554245 = 853921) (by norm_num)
theorem B3366413 : Blo 1496068 3366413 := bbase (se 3 (by rfl) ⟨631202, by rfl⟩ : syracuseStep 3366413 = 1262405) (by norm_num)
theorem B4046357 : Blo 1496068 4046357 := bbase (se 6 (by rfl) ⟨94836, by rfl⟩ : syracuseStep 4046357 = 189673) (by norm_num)
theorem B2244125 : Blo 1496068 2244125 := bbase (se 3 (by rfl) ⟨420773, by rfl⟩ : syracuseStep 2244125 = 841547) (by norm_num)
theorem B2022941 : Blo 1496068 2022941 := bbase (se 3 (by rfl) ⟨379301, by rfl⟩ : syracuseStep 2022941 = 758603) (by norm_num)
theorem B2244149 : Blo 1496068 2244149 := bbase (se 5 (by rfl) ⟨105194, by rfl⟩ : syracuseStep 2244149 = 210389) (by norm_num)
theorem B12787253 : Blo 1496068 12787253 := bbase (se 5 (by rfl) ⟨599402, by rfl⟩ : syracuseStep 12787253 = 1198805) (by norm_num)
theorem B5054021 : Blo 1496068 5054021 := bbase (se 4 (by rfl) ⟨473814, by rfl⟩ : syracuseStep 5054021 = 947629) (by norm_num)
theorem B2244173 : Blo 1496068 2244173 := bbase (se 3 (by rfl) ⟨420782, by rfl⟩ : syracuseStep 2244173 = 841565) (by norm_num)
theorem B3366485 : Blo 1496068 3366485 := bbase (se 8 (by rfl) ⟨19725, by rfl⟩ : syracuseStep 3366485 = 39451) (by norm_num)
theorem B10788437 : Blo 1496068 10788437 := bbase (se 8 (by rfl) ⟨63213, by rfl⟩ : syracuseStep 10788437 = 126427) (by norm_num)
theorem B13663829 : Blo 1496068 13663829 := bbase (se 8 (by rfl) ⟨80061, by rfl⟩ : syracuseStep 13663829 = 160123) (by norm_num)
theorem B2244197 : Blo 1496068 2244197 := bbase (se 4 (by rfl) ⟨210393, by rfl⟩ : syracuseStep 2244197 = 420787) (by norm_num)
theorem B8527477 : Blo 1496068 8527477 := bbase (se 5 (by rfl) ⟨399725, by rfl⟩ : syracuseStep 8527477 = 799451) (by norm_num)
theorem B2244221 : Blo 1496068 2244221 := bbase (se 3 (by rfl) ⟨420791, by rfl⟩ : syracuseStep 2244221 = 841583) (by norm_num)
theorem B2244245 : Blo 1496068 2244245 := bbase (se 6 (by rfl) ⟨52599, by rfl⟩ : syracuseStep 2244245 = 105199) (by norm_num)
theorem B3366557 : Blo 1496068 3366557 := bbase (se 3 (by rfl) ⟨631229, by rfl⟩ : syracuseStep 3366557 = 1262459) (by norm_num)
theorem B2244269 : Blo 1496068 2244269 := bbase (se 3 (by rfl) ⟨420800, by rfl⟩ : syracuseStep 2244269 = 841601) (by norm_num)
theorem B2244293 : Blo 1496068 2244293 := bbase (se 4 (by rfl) ⟨210402, by rfl⟩ : syracuseStep 2244293 = 420805) (by norm_num)
theorem B2244317 : Blo 1496068 2244317 := bbase (se 3 (by rfl) ⟨420809, by rfl⟩ : syracuseStep 2244317 = 841619) (by norm_num)
theorem B3366629 : Blo 1496068 3366629 := bbase (se 4 (by rfl) ⟨315621, by rfl⟩ : syracuseStep 3366629 = 631243) (by norm_num)
theorem B2244341 : Blo 1496068 2244341 := bbase (se 5 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 2244341 = 210407) (by norm_num)
theorem B2244365 : Blo 1496068 2244365 := bbase (se 3 (by rfl) ⟨420818, by rfl⟩ : syracuseStep 2244365 = 841637) (by norm_num)
theorem B2244389 : Blo 1496068 2244389 := bbase (se 4 (by rfl) ⟨210411, by rfl⟩ : syracuseStep 2244389 = 420823) (by norm_num)
theorem B3366701 : Blo 1496068 3366701 := bbase (se 3 (by rfl) ⟨631256, by rfl⟩ : syracuseStep 3366701 = 1262513) (by norm_num)
theorem B2244413 : Blo 1496068 2244413 := bbase (se 3 (by rfl) ⟨420827, by rfl⟩ : syracuseStep 2244413 = 841655) (by norm_num)
theorem B2244437 : Blo 1496068 2244437 := bbase (se 9 (by rfl) ⟨6575, by rfl⟩ : syracuseStep 2244437 = 13151) (by norm_num)
theorem B2244461 : Blo 1496068 2244461 := bbase (se 3 (by rfl) ⟨420836, by rfl⟩ : syracuseStep 2244461 = 841673) (by norm_num)
theorem B3366773 : Blo 1496068 3366773 := bbase (se 5 (by rfl) ⟨157817, by rfl⟩ : syracuseStep 3366773 = 315635) (by norm_num)
theorem B2244485 : Blo 1496068 2244485 := bbase (se 4 (by rfl) ⟨210420, by rfl⟩ : syracuseStep 2244485 = 420841) (by norm_num)
theorem B2023309 : Blo 1496068 2023309 := bbase (se 3 (by rfl) ⟨379370, by rfl⟩ : syracuseStep 2023309 = 758741) (by norm_num)
theorem B2244509 : Blo 1496068 2244509 := bbase (se 3 (by rfl) ⟨420845, by rfl⟩ : syracuseStep 2244509 = 841691) (by norm_num)
theorem B2244533 : Blo 1496068 2244533 := bbase (se 5 (by rfl) ⟨105212, by rfl⟩ : syracuseStep 2244533 = 210425) (by norm_num)
theorem B3366845 : Blo 1496068 3366845 := bbase (se 3 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 3366845 = 1262567) (by norm_num)
theorem B2244557 : Blo 1496068 2244557 := bbase (se 3 (by rfl) ⟨420854, by rfl⟩ : syracuseStep 2244557 = 841709) (by norm_num)
theorem B2244581 : Blo 1496068 2244581 := bbase (se 4 (by rfl) ⟨210429, by rfl⟩ : syracuseStep 2244581 = 420859) (by norm_num)
theorem B5054453 : Blo 1496068 5054453 := bbase (se 5 (by rfl) ⟨236927, by rfl⟩ : syracuseStep 5054453 = 473855) (by norm_num)
theorem B2244605 : Blo 1496068 2244605 := bbase (se 3 (by rfl) ⟨420863, by rfl⟩ : syracuseStep 2244605 = 841727) (by norm_num)
theorem B2244611 : Blo 1496068 2244611 := bstep (se 1 (by rfl) ⟨1683458, by rfl⟩ : syracuseStep 2244611 = 3366917) B3366917
theorem B2244641 : Blo 1496068 2244641 := bstep (se 2 (by rfl) ⟨841740, by rfl⟩ : syracuseStep 2244641 = 1683481) B1683481
theorem B2244659 : Blo 1496068 2244659 := bstep (se 1 (by rfl) ⟨1683494, by rfl⟩ : syracuseStep 2244659 = 3366989) B3366989
theorem B9592901 : Blo 1496068 9592901 := bstep (se 4 (by rfl) ⟨899334, by rfl⟩ : syracuseStep 9592901 = 1798669) B1798669
theorem B2244689 : Blo 1496068 2244689 := bstep (se 2 (by rfl) ⟨841758, by rfl⟩ : syracuseStep 2244689 = 1683517) B1683517
theorem B2842705 : Blo 1496068 2842705 := bstep (se 2 (by rfl) ⟨1066014, by rfl⟩ : syracuseStep 2842705 = 2132029) B2132029
theorem B2244707 : Blo 1496068 2244707 := bstep (se 1 (by rfl) ⟨1683530, by rfl⟩ : syracuseStep 2244707 = 3367061) B3367061
theorem B3367025 : Blo 1496068 3367025 := bstep (se 2 (by rfl) ⟨1262634, by rfl⟩ : syracuseStep 3367025 = 2525269) B2525269
theorem B2244737 : Blo 1496068 2244737 := bstep (se 2 (by rfl) ⟨841776, by rfl⟩ : syracuseStep 2244737 = 1683553) B1683553
theorem B3367043 : Blo 1496068 3367043 := bstep (se 1 (by rfl) ⟨2525282, by rfl⟩ : syracuseStep 3367043 = 5050565) B5050565
theorem B2244755 : Blo 1496068 2244755 := bstep (se 1 (by rfl) ⟨1683566, by rfl⟩ : syracuseStep 2244755 = 3367133) B3367133
theorem B2244785 : Blo 1496068 2244785 := bstep (se 2 (by rfl) ⟨841794, by rfl⟩ : syracuseStep 2244785 = 1683589) B1683589
theorem B2244803 : Blo 1496068 2244803 := bstep (se 1 (by rfl) ⟨1683602, by rfl⟩ : syracuseStep 2244803 = 3367205) B3367205
theorem B6070477 : Blo 1496068 6070477 := bstep (se 3 (by rfl) ⟨1138214, by rfl⟩ : syracuseStep 6070477 = 2276429) B2276429
theorem B5054669 : Blo 1496068 5054669 := bstep (se 3 (by rfl) ⟨947750, by rfl⟩ : syracuseStep 5054669 = 1895501) B1895501
theorem B2023633 : Blo 1496068 2023633 := bstep (se 2 (by rfl) ⟨758862, by rfl⟩ : syracuseStep 2023633 = 1517725) B1517725
theorem B2244833 : Blo 1496068 2244833 := bstep (se 2 (by rfl) ⟨841812, by rfl⟩ : syracuseStep 2244833 = 1683625) B1683625
theorem B13664483 : Blo 1496068 13664483 := bstep (se 1 (by rfl) ⟨10248362, by rfl⟩ : syracuseStep 13664483 = 20496725) B20496725
theorem B2244851 : Blo 1496068 2244851 := bstep (se 1 (by rfl) ⟨1683638, by rfl⟩ : syracuseStep 2244851 = 3367277) B3367277
theorem B5054723 : Blo 1496068 5054723 := bstep (se 1 (by rfl) ⟨3791042, by rfl⟩ : syracuseStep 5054723 = 7582085) B7582085
theorem B2244881 : Blo 1496068 2244881 := bstep (se 2 (by rfl) ⟨841830, by rfl⟩ : syracuseStep 2244881 = 1683661) B1683661
theorem B2244899 : Blo 1496068 2244899 := bstep (se 1 (by rfl) ⟨1683674, by rfl⟩ : syracuseStep 2244899 = 3367349) B3367349
theorem B2130241 : Blo 1496068 2130241 := bstep (se 2 (by rfl) ⟨798840, by rfl⟩ : syracuseStep 2130241 = 1597681) B1597681
theorem B2244929 : Blo 1496068 2244929 := bstep (se 2 (by rfl) ⟨841848, by rfl⟩ : syracuseStep 2244929 = 1683697) B1683697
theorem B2244947 : Blo 1496068 2244947 := bstep (se 1 (by rfl) ⟨1683710, by rfl⟩ : syracuseStep 2244947 = 3367421) B3367421
theorem B2244977 : Blo 1496068 2244977 := bstep (se 2 (by rfl) ⟨841866, by rfl⟩ : syracuseStep 2244977 = 1683733) B1683733
theorem B2244995 : Blo 1496068 2244995 := bstep (se 1 (by rfl) ⟨1683746, by rfl⟩ : syracuseStep 2244995 = 3367493) B3367493
theorem B3367313 : Blo 1496068 3367313 := bstep (se 2 (by rfl) ⟨1262742, by rfl⟩ : syracuseStep 3367313 = 2525485) B2525485
theorem B1597843 : Blo 1496068 1597843 := bstep (se 1 (by rfl) ⟨1198382, by rfl⟩ : syracuseStep 1597843 = 2396765) B2396765
theorem B2245025 : Blo 1496068 2245025 := bstep (se 2 (by rfl) ⟨841884, by rfl⟩ : syracuseStep 2245025 = 1683769) B1683769
theorem B3367331 : Blo 1496068 3367331 := bstep (se 1 (by rfl) ⟨2525498, by rfl⟩ : syracuseStep 3367331 = 5050997) B5050997
theorem B2245043 : Blo 1496068 2245043 := bstep (se 1 (by rfl) ⟨1683782, by rfl⟩ : syracuseStep 2245043 = 3367565) B3367565
theorem B2245073 : Blo 1496068 2245073 := bstep (se 2 (by rfl) ⟨841902, by rfl⟩ : syracuseStep 2245073 = 1683805) B1683805
theorem B2245091 : Blo 1496068 2245091 := bstep (se 1 (by rfl) ⟨1683818, by rfl⟩ : syracuseStep 2245091 = 3367637) B3367637
theorem B2245121 : Blo 1496068 2245121 := bstep (se 2 (by rfl) ⟨841920, by rfl⟩ : syracuseStep 2245121 = 1683841) B1683841
theorem B5054993 : Blo 1496068 5054993 := bstep (se 2 (by rfl) ⟨1895622, by rfl⟩ : syracuseStep 5054993 = 3791245) B3791245
theorem B2245139 : Blo 1496068 2245139 := bstep (se 1 (by rfl) ⟨1683854, by rfl⟩ : syracuseStep 2245139 = 3367709) B3367709
theorem B2245169 : Blo 1496068 2245169 := bstep (se 2 (by rfl) ⟨841938, by rfl⟩ : syracuseStep 2245169 = 1683877) B1683877
theorem B72811061 : Blo 1496068 72811061 := bstep (se 5 (by rfl) ⟨3413018, by rfl⟩ : syracuseStep 72811061 = 6826037) B6826037
theorem B2245187 : Blo 1496068 2245187 := bstep (se 1 (by rfl) ⟨1683890, by rfl⟩ : syracuseStep 2245187 = 3367781) B3367781
theorem B2245217 : Blo 1496068 2245217 := bstep (se 2 (by rfl) ⟨841956, by rfl⟩ : syracuseStep 2245217 = 1683913) B1683913
theorem B2245235 : Blo 1496068 2245235 := bstep (se 1 (by rfl) ⟨1683926, by rfl⟩ : syracuseStep 2245235 = 3367853) B3367853
theorem B2245265 : Blo 1496068 2245265 := bstep (se 2 (by rfl) ⟨841974, by rfl⟩ : syracuseStep 2245265 = 1683949) B1683949
theorem B2245283 : Blo 1496068 2245283 := bstep (se 1 (by rfl) ⟨1683962, by rfl⟩ : syracuseStep 2245283 = 3367925) B3367925
theorem B3367601 : Blo 1496068 3367601 := bstep (se 2 (by rfl) ⟨1262850, by rfl⟩ : syracuseStep 3367601 = 2525701) B2525701
theorem B2245313 : Blo 1496068 2245313 := bstep (se 2 (by rfl) ⟨841992, by rfl⟩ : syracuseStep 2245313 = 1683985) B1683985
theorem B3367619 : Blo 1496068 3367619 := bstep (se 1 (by rfl) ⟨2525714, by rfl⟩ : syracuseStep 3367619 = 5051429) B5051429
theorem B1950419 : Blo 1496068 1950419 := bstep (se 1 (by rfl) ⟨1462814, by rfl⟩ : syracuseStep 1950419 = 2925629) B2925629
theorem B2245331 : Blo 1496068 2245331 := bstep (se 1 (by rfl) ⟨1683998, by rfl⟩ : syracuseStep 2245331 = 3367997) B3367997
theorem B2245361 : Blo 1496068 2245361 := bstep (se 2 (by rfl) ⟨842010, by rfl⟩ : syracuseStep 2245361 = 1684021) B1684021
theorem B2245379 : Blo 1496068 2245379 := bstep (se 1 (by rfl) ⟨1684034, by rfl⟩ : syracuseStep 2245379 = 3368069) B3368069
theorem B2024195 : Blo 1496068 2024195 := bstep (se 1 (by rfl) ⟨1518146, by rfl⟩ : syracuseStep 2024195 = 3036293) B3036293
theorem B7684877 : Blo 1496068 7684877 := bstep (se 3 (by rfl) ⟨1440914, by rfl⟩ : syracuseStep 7684877 = 2881829) B2881829
theorem B2245409 : Blo 1496068 2245409 := bstep (se 2 (by rfl) ⟨842028, by rfl⟩ : syracuseStep 2245409 = 1684057) B1684057
theorem B2245427 : Blo 1496068 2245427 := bstep (se 1 (by rfl) ⟨1684070, by rfl⟩ : syracuseStep 2245427 = 3368141) B3368141
theorem B2245457 : Blo 1496068 2245457 := bstep (se 2 (by rfl) ⟨842046, by rfl⟩ : syracuseStep 2245457 = 1684093) B1684093
theorem B3597137 : Blo 1496068 3597137 := bstep (se 2 (by rfl) ⟨1348926, by rfl⟩ : syracuseStep 3597137 = 2697853) B2697853
theorem B2245475 : Blo 1496068 2245475 := bstep (se 1 (by rfl) ⟨1684106, by rfl⟩ : syracuseStep 2245475 = 3368213) B3368213
theorem B4260721 : Blo 1496068 4260721 := bstep (se 2 (by rfl) ⟨1597770, by rfl⟩ : syracuseStep 4260721 = 3195541) B3195541
theorem B8528753 : Blo 1496068 8528753 := bstep (se 2 (by rfl) ⟨3198282, by rfl⟩ : syracuseStep 8528753 = 6396565) B6396565
theorem B2245505 : Blo 1496068 2245505 := bstep (se 2 (by rfl) ⟨842064, by rfl⟩ : syracuseStep 2245505 = 1684129) B1684129
theorem B2130833 : Blo 1496068 2130833 := bstep (se 2 (by rfl) ⟨799062, by rfl⟩ : syracuseStep 2130833 = 1598125) B1598125
theorem B2245523 : Blo 1496068 2245523 := bstep (se 1 (by rfl) ⟨1684142, by rfl⟩ : syracuseStep 2245523 = 3368285) B3368285
theorem B2245553 : Blo 1496068 2245553 := bstep (se 2 (by rfl) ⟨842082, by rfl⟩ : syracuseStep 2245553 = 1684165) B1684165
theorem B2245571 : Blo 1496068 2245571 := bstep (se 1 (by rfl) ⟨1684178, by rfl⟩ : syracuseStep 2245571 = 3368357) B3368357
theorem B4858829 : Blo 1496068 4858829 := bstep (se 3 (by rfl) ⟨911030, by rfl⟩ : syracuseStep 4858829 = 1822061) B1822061
theorem B3195857 : Blo 1496068 3195857 := bstep (se 2 (by rfl) ⟨1198446, by rfl⟩ : syracuseStep 3195857 = 2396893) B2396893
theorem B3367889 : Blo 1496068 3367889 := bstep (se 2 (by rfl) ⟨1262958, by rfl⟩ : syracuseStep 3367889 = 2525917) B2525917
theorem B2245601 : Blo 1496068 2245601 := bstep (se 2 (by rfl) ⟨842100, by rfl⟩ : syracuseStep 2245601 = 1684201) B1684201
theorem B3367907 : Blo 1496068 3367907 := bstep (se 1 (by rfl) ⟨2525930, by rfl⟩ : syracuseStep 3367907 = 5051861) B5051861
theorem B2245619 : Blo 1496068 2245619 := bstep (se 1 (by rfl) ⟨1684214, by rfl⟩ : syracuseStep 2245619 = 3368429) B3368429
theorem B2245649 : Blo 1496068 2245649 := bstep (se 2 (by rfl) ⟨842118, by rfl⟩ : syracuseStep 2245649 = 1684237) B1684237
theorem B2245667 : Blo 1496068 2245667 := bstep (se 1 (by rfl) ⟨1684250, by rfl⟩ : syracuseStep 2245667 = 3368501) B3368501
theorem B6153251 : Blo 1496068 6153251 := bstep (se 1 (by rfl) ⟨4614938, by rfl⟩ : syracuseStep 6153251 = 9229877) B9229877
theorem B5686307 : Blo 1496068 5686307 := bstep (se 1 (by rfl) ⟨4264730, by rfl⟩ : syracuseStep 5686307 = 8529461) B8529461
theorem B5055533 : Blo 1496068 5055533 := bstep (se 3 (by rfl) ⟨947912, by rfl⟩ : syracuseStep 5055533 = 1895825) B1895825
theorem B5686321 : Blo 1496068 5686321 := bstep (se 2 (by rfl) ⟨2132370, by rfl⟩ : syracuseStep 5686321 = 4264741) B4264741
theorem B2245697 : Blo 1496068 2245697 := bstep (se 2 (by rfl) ⟨842136, by rfl⟩ : syracuseStep 2245697 = 1684273) B1684273
theorem B2245715 : Blo 1496068 2245715 := bstep (se 1 (by rfl) ⟨1684286, by rfl⟩ : syracuseStep 2245715 = 3368573) B3368573
theorem B5055587 : Blo 1496068 5055587 := bstep (se 1 (by rfl) ⟨3791690, by rfl⟩ : syracuseStep 5055587 = 7583381) B7583381
theorem B12797027 : Blo 1496068 12797027 := bstep (se 1 (by rfl) ⟨9597770, by rfl⟩ : syracuseStep 12797027 = 19195541) B19195541
theorem B2245745 : Blo 1496068 2245745 := bstep (se 2 (by rfl) ⟨842154, by rfl⟩ : syracuseStep 2245745 = 1684309) B1684309
theorem B25937009 : Blo 1496068 25937009 := bstep (se 2 (by rfl) ⟨9726378, by rfl⟩ : syracuseStep 25937009 = 19452757) B19452757
theorem B2843761 : Blo 1496068 2843761 := bstep (se 2 (by rfl) ⟨1066410, by rfl⟩ : syracuseStep 2843761 = 2132821) B2132821
theorem B4260995 : Blo 1496068 4260995 := bstep (se 1 (by rfl) ⟨3195746, by rfl⟩ : syracuseStep 4260995 = 6391493) B6391493
theorem B2245763 : Blo 1496068 2245763 := bstep (se 1 (by rfl) ⟨1684322, by rfl⟩ : syracuseStep 2245763 = 3368645) B3368645
theorem B2245793 : Blo 1496068 2245793 := bstep (se 2 (by rfl) ⟨842172, by rfl⟩ : syracuseStep 2245793 = 1684345) B1684345
theorem B9585827 : Blo 1496068 9585827 := bstep (se 1 (by rfl) ⟨7189370, by rfl⟩ : syracuseStep 9585827 = 14378741) B14378741
theorem B2245811 : Blo 1496068 2245811 := bstep (se 1 (by rfl) ⟨1684358, by rfl⟩ : syracuseStep 2245811 = 3368717) B3368717
theorem B2245841 : Blo 1496068 2245841 := bstep (se 2 (by rfl) ⟨842190, by rfl⟩ : syracuseStep 2245841 = 1684381) B1684381
theorem B2245859 : Blo 1496068 2245859 := bstep (se 1 (by rfl) ⟨1684394, by rfl⟩ : syracuseStep 2245859 = 3368789) B3368789
theorem B3368177 : Blo 1496068 3368177 := bstep (se 2 (by rfl) ⟨1263066, by rfl⟩ : syracuseStep 3368177 = 2526133) B2526133
theorem B2245889 : Blo 1496068 2245889 := bstep (se 2 (by rfl) ⟨842208, by rfl⟩ : syracuseStep 2245889 = 1684417) B1684417
theorem B3368195 : Blo 1496068 3368195 := bstep (se 1 (by rfl) ⟨2526146, by rfl⟩ : syracuseStep 3368195 = 5052293) B5052293
theorem B2245907 : Blo 1496068 2245907 := bstep (se 1 (by rfl) ⟨1684430, by rfl⟩ : syracuseStep 2245907 = 3368861) B3368861
theorem B2245937 : Blo 1496068 2245937 := bstep (se 2 (by rfl) ⟨842226, by rfl⟩ : syracuseStep 2245937 = 1684453) B1684453
theorem B27329845 : Blo 1496068 27329845 := bstep (se 5 (by rfl) ⟨1281086, by rfl⟩ : syracuseStep 27329845 = 2562173) B2562173
theorem B4261187 : Blo 1496068 4261187 := bstep (se 1 (by rfl) ⟨3195890, by rfl⟩ : syracuseStep 4261187 = 6391781) B6391781
theorem B2245955 : Blo 1496068 2245955 := bstep (se 1 (by rfl) ⟨1684466, by rfl⟩ : syracuseStep 2245955 = 3368933) B3368933
theorem B2245985 : Blo 1496068 2245985 := bstep (se 2 (by rfl) ⟨842244, by rfl⟩ : syracuseStep 2245985 = 1684489) B1684489
theorem B5055857 : Blo 1496068 5055857 := bstep (se 2 (by rfl) ⟨1895946, by rfl⟩ : syracuseStep 5055857 = 3791893) B3791893
theorem B2246003 : Blo 1496068 2246003 := bstep (se 1 (by rfl) ⟨1684502, by rfl⟩ : syracuseStep 2246003 = 3369005) B3369005
theorem B2246033 : Blo 1496068 2246033 := bstep (se 2 (by rfl) ⟨842262, by rfl⟩ : syracuseStep 2246033 = 1684525) B1684525
theorem B2131363 : Blo 1496068 2131363 := bstep (se 1 (by rfl) ⟨1598522, by rfl⟩ : syracuseStep 2131363 = 3197045) B3197045
theorem B2246051 : Blo 1496068 2246051 := bstep (se 1 (by rfl) ⟨1684538, by rfl⟩ : syracuseStep 2246051 = 3369077) B3369077
theorem B2246081 : Blo 1496068 2246081 := bstep (se 2 (by rfl) ⟨842280, by rfl⟩ : syracuseStep 2246081 = 1684561) B1684561
theorem B3196369 : Blo 1496068 3196369 := bstep (se 2 (by rfl) ⟨1198638, by rfl⟩ : syracuseStep 3196369 = 2397277) B2397277
theorem B2246099 : Blo 1496068 2246099 := bstep (se 1 (by rfl) ⟨1684574, by rfl⟩ : syracuseStep 2246099 = 3369149) B3369149
theorem B2246129 : Blo 1496068 2246129 := bstep (se 2 (by rfl) ⟨842298, by rfl⟩ : syracuseStep 2246129 = 1684597) B1684597
theorem B2524675 : Blo 1496068 2524675 := bstep (se 1 (by rfl) ⟨1893506, by rfl⟩ : syracuseStep 2524675 = 3787013) B3787013
theorem B2246147 : Blo 1496068 2246147 := bstep (se 1 (by rfl) ⟨1684610, by rfl⟩ : syracuseStep 2246147 = 3369221) B3369221
theorem B3368465 : Blo 1496068 3368465 := bstep (se 2 (by rfl) ⟨1263174, by rfl⟩ : syracuseStep 3368465 = 2526349) B2526349
theorem B2246177 : Blo 1496068 2246177 := bstep (se 2 (by rfl) ⟨842316, by rfl⟩ : syracuseStep 2246177 = 1684633) B1684633
theorem B3368483 : Blo 1496068 3368483 := bstep (se 1 (by rfl) ⟨2526362, by rfl⟩ : syracuseStep 3368483 = 5052725) B5052725
theorem B4048433 : Blo 1496068 4048433 := bstep (se 2 (by rfl) ⟨1518162, by rfl⟩ : syracuseStep 4048433 = 3036325) B3036325
theorem B2246195 : Blo 1496068 2246195 := bstep (se 1 (by rfl) ⟨1684646, by rfl⟩ : syracuseStep 2246195 = 3369293) B3369293
theorem B2246225 : Blo 1496068 2246225 := bstep (se 2 (by rfl) ⟨842334, by rfl⟩ : syracuseStep 2246225 = 1684669) B1684669
theorem B2246243 : Blo 1496068 2246243 := bstep (se 1 (by rfl) ⟨1684682, by rfl⟩ : syracuseStep 2246243 = 3369365) B3369365
theorem B9586289 : Blo 1496068 9586289 := bstep (se 2 (by rfl) ⟨3594858, by rfl⟩ : syracuseStep 9586289 = 7189717) B7189717
theorem B2246273 : Blo 1496068 2246273 := bstep (se 2 (by rfl) ⟨842352, by rfl⟩ : syracuseStep 2246273 = 1684705) B1684705
theorem B1599107 : Blo 1496068 1599107 := bstep (se 1 (by rfl) ⟨1199330, by rfl⟩ : syracuseStep 1599107 = 2398661) B2398661
theorem B2524817 : Blo 1496068 2524817 := bstep (se 2 (by rfl) ⟨946806, by rfl⟩ : syracuseStep 2524817 = 1893613) B1893613
theorem B4318865 : Blo 1496068 4318865 := bstep (se 2 (by rfl) ⟨1619574, by rfl⟩ : syracuseStep 4318865 = 3239149) B3239149
theorem B2246291 : Blo 1496068 2246291 := bstep (se 1 (by rfl) ⟨1684718, by rfl⟩ : syracuseStep 2246291 = 3369437) B3369437
theorem B2246321 : Blo 1496068 2246321 := bstep (se 2 (by rfl) ⟨842370, by rfl⟩ : syracuseStep 2246321 = 1684741) B1684741
theorem B2246339 : Blo 1496068 2246339 := bstep (se 1 (by rfl) ⟨1684754, by rfl⟩ : syracuseStep 2246339 = 3369509) B3369509
theorem B1894099 : Blo 1496068 1894099 := bstep (se 1 (by rfl) ⟨1420574, by rfl⟩ : syracuseStep 1894099 = 2841149) B2841149
theorem B2246369 : Blo 1496068 2246369 := bstep (se 2 (by rfl) ⟨842388, by rfl⟩ : syracuseStep 2246369 = 1684777) B1684777
theorem B19187441 : Blo 1496068 19187441 := bstep (se 2 (by rfl) ⟨7195290, by rfl⟩ : syracuseStep 19187441 = 14390581) B14390581
theorem B2131699 : Blo 1496068 2131699 := bstep (se 1 (by rfl) ⟨1598774, by rfl⟩ : syracuseStep 2131699 = 3197549) B3197549
theorem B2246387 : Blo 1496068 2246387 := bstep (se 1 (by rfl) ⟨1684790, by rfl⟩ : syracuseStep 2246387 = 3369581) B3369581
theorem B2524945 : Blo 1496068 2524945 := bstep (se 2 (by rfl) ⟨946854, by rfl⟩ : syracuseStep 2524945 = 1893709) B1893709
theorem B2246417 : Blo 1496068 2246417 := bstep (se 2 (by rfl) ⟨842406, by rfl⟩ : syracuseStep 2246417 = 1684813) B1684813
theorem B2246435 : Blo 1496068 2246435 := bstep (se 1 (by rfl) ⟨1684826, by rfl⟩ : syracuseStep 2246435 = 3369653) B3369653
theorem B3368753 : Blo 1496068 3368753 := bstep (se 2 (by rfl) ⟨1263282, by rfl⟩ : syracuseStep 3368753 = 2526565) B2526565
theorem B2524979 : Blo 1496068 2524979 := bstep (se 1 (by rfl) ⟨1893734, by rfl⟩ : syracuseStep 2524979 = 3787469) B3787469
theorem B1894195 : Blo 1496068 1894195 := bstep (se 1 (by rfl) ⟨1420646, by rfl⟩ : syracuseStep 1894195 = 2841293) B2841293
theorem B2246465 : Blo 1496068 2246465 := bstep (se 2 (by rfl) ⟨842424, by rfl⟩ : syracuseStep 2246465 = 1684849) B1684849
theorem B3368771 : Blo 1496068 3368771 := bstep (se 1 (by rfl) ⟨2526578, by rfl⟩ : syracuseStep 3368771 = 5053157) B5053157
theorem B2246483 : Blo 1496068 2246483 := bstep (se 1 (by rfl) ⟨1684862, by rfl⟩ : syracuseStep 2246483 = 3369725) B3369725
theorem B4319075 : Blo 1496068 4319075 := bstep (se 1 (by rfl) ⟨3239306, by rfl⟩ : syracuseStep 4319075 = 6478613) B6478613
theorem B2246513 : Blo 1496068 2246513 := bstep (se 2 (by rfl) ⟨842442, by rfl⟩ : syracuseStep 2246513 = 1684885) B1684885
theorem B2246531 : Blo 1496068 2246531 := bstep (se 1 (by rfl) ⟨1684898, by rfl⟩ : syracuseStep 2246531 = 3369797) B3369797
theorem B2246561 : Blo 1496068 2246561 := bstep (se 2 (by rfl) ⟨842460, by rfl⟩ : syracuseStep 2246561 = 1684921) B1684921
theorem B2525107 : Blo 1496068 2525107 := bstep (se 1 (by rfl) ⟨1893830, by rfl⟩ : syracuseStep 2525107 = 3787661) B3787661
theorem B2246579 : Blo 1496068 2246579 := bstep (se 1 (by rfl) ⟨1684934, by rfl⟩ : syracuseStep 2246579 = 3369869) B3369869
theorem B2246609 : Blo 1496068 2246609 := bstep (se 2 (by rfl) ⟨842478, by rfl⟩ : syracuseStep 2246609 = 1684957) B1684957
theorem B2246627 : Blo 1496068 2246627 := bstep (se 1 (by rfl) ⟨1684970, by rfl⟩ : syracuseStep 2246627 = 3369941) B3369941
theorem B4794349 : Blo 1496068 4794349 := bstep (se 3 (by rfl) ⟨898940, by rfl⟩ : syracuseStep 4794349 = 1797881) B1797881
theorem B2246657 : Blo 1496068 2246657 := bstep (se 2 (by rfl) ⟨842496, by rfl⟩ : syracuseStep 2246657 = 1684993) B1684993
theorem B2246675 : Blo 1496068 2246675 := bstep (se 1 (by rfl) ⟨1685006, by rfl⟩ : syracuseStep 2246675 = 3370013) B3370013
theorem B2246705 : Blo 1496068 2246705 := bstep (se 2 (by rfl) ⟨842514, by rfl⟩ : syracuseStep 2246705 = 1685029) B1685029
theorem B32368693 : Blo 1496068 32368693 := bstep (se 5 (by rfl) ⟨1517282, by rfl⟩ : syracuseStep 32368693 = 3034565) B3034565
theorem B2525249 : Blo 1496068 2525249 := bstep (se 2 (by rfl) ⟨946968, by rfl⟩ : syracuseStep 2525249 = 1893937) B1893937
theorem B2246723 : Blo 1496068 2246723 := bstep (se 1 (by rfl) ⟨1685042, by rfl⟩ : syracuseStep 2246723 = 3370085) B3370085
theorem B3369041 : Blo 1496068 3369041 := bstep (se 2 (by rfl) ⟨1263390, by rfl⟩ : syracuseStep 3369041 = 2526781) B2526781
theorem B2246753 : Blo 1496068 2246753 := bstep (se 2 (by rfl) ⟨842532, by rfl⟩ : syracuseStep 2246753 = 1685065) B1685065
theorem B3369059 : Blo 1496068 3369059 := bstep (se 1 (by rfl) ⟨2526794, by rfl⟩ : syracuseStep 3369059 = 5053589) B5053589
theorem B4261997 : Blo 1496068 4261997 := bstep (se 3 (by rfl) ⟨799124, by rfl⟩ : syracuseStep 4261997 = 1598249) B1598249
theorem B2246771 : Blo 1496068 2246771 := bstep (se 1 (by rfl) ⟨1685078, by rfl⟩ : syracuseStep 2246771 = 3370157) B3370157
theorem B34171021 : Blo 1496068 34171021 := bstep (se 3 (by rfl) ⟨6407066, by rfl⟩ : syracuseStep 34171021 = 12814133) B12814133
theorem B2246801 : Blo 1496068 2246801 := bstep (se 2 (by rfl) ⟨842550, by rfl⟩ : syracuseStep 2246801 = 1685101) B1685101
theorem B2246819 : Blo 1496068 2246819 := bstep (se 1 (by rfl) ⟨1685114, by rfl⟩ : syracuseStep 2246819 = 3370229) B3370229
theorem B2525377 : Blo 1496068 2525377 := bstep (se 2 (by rfl) ⟨947016, by rfl⟩ : syracuseStep 2525377 = 1894033) B1894033
theorem B2246849 : Blo 1496068 2246849 := bstep (se 2 (by rfl) ⟨842568, by rfl⟩ : syracuseStep 2246849 = 1685137) B1685137
theorem B2246867 : Blo 1496068 2246867 := bstep (se 1 (by rfl) ⟨1685150, by rfl⟩ : syracuseStep 2246867 = 3370301) B3370301
theorem B2525411 : Blo 1496068 2525411 := bstep (se 1 (by rfl) ⟨1894058, by rfl⟩ : syracuseStep 2525411 = 3788117) B3788117
theorem B2246897 : Blo 1496068 2246897 := bstep (se 2 (by rfl) ⟨842586, by rfl⟩ : syracuseStep 2246897 = 1685173) B1685173
theorem B2246915 : Blo 1496068 2246915 := bstep (se 1 (by rfl) ⟨1685186, by rfl⟩ : syracuseStep 2246915 = 3370373) B3370373
theorem B2132257 : Blo 1496068 2132257 := bstep (se 2 (by rfl) ⟨799596, by rfl⟩ : syracuseStep 2132257 = 1599193) B1599193
theorem B2246945 : Blo 1496068 2246945 := bstep (se 2 (by rfl) ⟨842604, by rfl⟩ : syracuseStep 2246945 = 1685209) B1685209
theorem B4262179 : Blo 1496068 4262179 := bstep (se 1 (by rfl) ⟨3196634, by rfl⟩ : syracuseStep 4262179 = 6393269) B6393269
theorem B1894691 : Blo 1496068 1894691 := bstep (se 1 (by rfl) ⟨1421018, by rfl⟩ : syracuseStep 1894691 = 2842037) B2842037
theorem B8530211 : Blo 1496068 8530211 := bstep (se 1 (by rfl) ⟨6397658, by rfl⟩ : syracuseStep 8530211 = 12795317) B12795317
theorem B2246963 : Blo 1496068 2246963 := bstep (se 1 (by rfl) ⟨1685222, by rfl⟩ : syracuseStep 2246963 = 3370445) B3370445
theorem B2132291 : Blo 1496068 2132291 := bstep (se 1 (by rfl) ⟨1599218, by rfl⟩ : syracuseStep 2132291 = 3198437) B3198437
theorem B2246993 : Blo 1496068 2246993 := bstep (se 2 (by rfl) ⟨842622, by rfl⟩ : syracuseStep 2246993 = 1685245) B1685245
theorem B2525539 : Blo 1496068 2525539 := bstep (se 1 (by rfl) ⟨1894154, by rfl⟩ : syracuseStep 2525539 = 3788309) B3788309
theorem B2697571 : Blo 1496068 2697571 := bstep (se 1 (by rfl) ⟨2023178, by rfl⟩ : syracuseStep 2697571 = 4046357) B4046357
theorem B2247011 : Blo 1496068 2247011 := bstep (se 1 (by rfl) ⟨1685258, by rfl⟩ : syracuseStep 2247011 = 3370517) B3370517
theorem B3369329 : Blo 1496068 3369329 := bstep (se 2 (by rfl) ⟨1263498, by rfl⟩ : syracuseStep 3369329 = 2526997) B2526997
theorem B2247041 : Blo 1496068 2247041 := bstep (se 2 (by rfl) ⟨842640, by rfl⟩ : syracuseStep 2247041 = 1685281) B1685281
theorem B3369347 : Blo 1496068 3369347 := bstep (se 1 (by rfl) ⟨2527010, by rfl⟩ : syracuseStep 3369347 = 5054021) B5054021
theorem B2247059 : Blo 1496068 2247059 := bstep (se 1 (by rfl) ⟨1685294, by rfl⟩ : syracuseStep 2247059 = 3370589) B3370589
theorem B2247089 : Blo 1496068 2247089 := bstep (se 2 (by rfl) ⟨842658, by rfl⟩ : syracuseStep 2247089 = 1685317) B1685317
theorem B5687779 : Blo 1496068 5687779 := bstep (se 1 (by rfl) ⟨4265834, by rfl⟩ : syracuseStep 5687779 = 8531669) B8531669
theorem B2525681 : Blo 1496068 2525681 := bstep (se 2 (by rfl) ⟨947130, by rfl⟩ : syracuseStep 2525681 = 1894261) B1894261
theorem B3033617 : Blo 1496068 3033617 := bstep (se 2 (by rfl) ⟨1137606, by rfl⟩ : syracuseStep 3033617 = 2275213) B2275213
theorem B2697745 : Blo 1496068 2697745 := bstep (se 2 (by rfl) ⟨1011654, by rfl⟩ : syracuseStep 2697745 = 2023309) B2023309
theorem B2525809 : Blo 1496068 2525809 := bstep (se 2 (by rfl) ⟨947178, by rfl⟩ : syracuseStep 2525809 = 1894357) B1894357
theorem B3369617 : Blo 1496068 3369617 := bstep (se 2 (by rfl) ⟨1263606, by rfl⟩ : syracuseStep 3369617 = 2527213) B2527213
theorem B2525843 : Blo 1496068 2525843 := bstep (se 1 (by rfl) ⟨1894382, by rfl⟩ : syracuseStep 2525843 = 3788765) B3788765
theorem B3369635 : Blo 1496068 3369635 := bstep (se 1 (by rfl) ⟨2527226, by rfl⟩ : syracuseStep 3369635 = 5054453) B5054453
theorem B3033859 : Blo 1496068 3033859 := bstep (se 1 (by rfl) ⟨2275394, by rfl⟩ : syracuseStep 3033859 = 4550789) B4550789
theorem B4262669 : Blo 1496068 4262669 := bstep (se 3 (by rfl) ⟨799250, by rfl⟩ : syracuseStep 4262669 = 1598501) B1598501
theorem B2525971 : Blo 1496068 2525971 := bstep (se 1 (by rfl) ⟨1894478, by rfl⟩ : syracuseStep 2525971 = 3788957) B3788957
theorem B7580465 : Blo 1496068 7580465 := bstep (se 2 (by rfl) ⟨2842674, by rfl⟩ : syracuseStep 7580465 = 5685349) B5685349
theorem B2132849 : Blo 1496068 2132849 := bstep (se 2 (by rfl) ⟨799818, by rfl⟩ : syracuseStep 2132849 = 1599637) B1599637
theorem B12790669 : Blo 1496068 12790669 := bstep (se 3 (by rfl) ⟨2398250, by rfl⟩ : syracuseStep 12790669 = 4796501) B4796501
theorem B2526113 : Blo 1496068 2526113 := bstep (se 2 (by rfl) ⟨947292, by rfl⟩ : syracuseStep 2526113 = 1894585) B1894585
theorem B3197873 : Blo 1496068 3197873 := bstep (se 2 (by rfl) ⟨1199202, by rfl⟩ : syracuseStep 3197873 = 2398405) B2398405
theorem B3369905 : Blo 1496068 3369905 := bstep (se 2 (by rfl) ⟨1263714, by rfl⟩ : syracuseStep 3369905 = 2527429) B2527429
theorem B2132929 : Blo 1496068 2132929 := bstep (se 2 (by rfl) ⟨799848, by rfl⟩ : syracuseStep 2132929 = 1599697) B1599697
theorem B3369923 : Blo 1496068 3369923 := bstep (se 1 (by rfl) ⟨2527442, by rfl⟩ : syracuseStep 3369923 = 5054885) B5054885
theorem B1895395 : Blo 1496068 1895395 := bstep (se 1 (by rfl) ⟨1421546, by rfl⟩ : syracuseStep 1895395 = 2843093) B2843093
theorem B2960369 : Blo 1496068 2960369 := bstep (se 2 (by rfl) ⟨1110138, by rfl⟩ : syracuseStep 2960369 = 2220277) B2220277
theorem B3787793 : Blo 1496068 3787793 := bstep (se 2 (by rfl) ⟨1420422, by rfl⟩ : syracuseStep 3787793 = 2840845) B2840845
theorem B2526241 : Blo 1496068 2526241 := bstep (se 2 (by rfl) ⟨947340, by rfl⟩ : syracuseStep 2526241 = 1894681) B1894681
theorem B3787843 : Blo 1496068 3787843 := bstep (se 1 (by rfl) ⟨2840882, by rfl⟩ : syracuseStep 3787843 = 5681765) B5681765
theorem B2526275 : Blo 1496068 2526275 := bstep (se 1 (by rfl) ⟨1894706, by rfl⟩ : syracuseStep 2526275 = 3789413) B3789413
theorem B1895491 : Blo 1496068 1895491 := bstep (se 1 (by rfl) ⟨1421618, by rfl⟩ : syracuseStep 1895491 = 2843237) B2843237
theorem B4549709 : Blo 1496068 4549709 := bstep (se 3 (by rfl) ⟨853070, by rfl⟩ : syracuseStep 4549709 = 1706141) B1706141
theorem B5049485 : Blo 1496068 5049485 := bstep (se 3 (by rfl) ⟨946778, by rfl⟩ : syracuseStep 5049485 = 1893557) B1893557
theorem B5049539 : Blo 1496068 5049539 := bstep (se 1 (by rfl) ⟨3787154, by rfl⟩ : syracuseStep 5049539 = 7574309) B7574309
theorem B2526403 : Blo 1496068 2526403 := bstep (se 1 (by rfl) ⟨1894802, by rfl⟩ : syracuseStep 2526403 = 3789605) B3789605
theorem B3787985 : Blo 1496068 3787985 := bstep (se 2 (by rfl) ⟨1420494, by rfl⟩ : syracuseStep 3787985 = 2840989) B2840989
theorem B3370193 : Blo 1496068 3370193 := bstep (se 2 (by rfl) ⟨1263822, by rfl⟩ : syracuseStep 3370193 = 2527645) B2527645
theorem B3370211 : Blo 1496068 3370211 := bstep (se 1 (by rfl) ⟨2527658, by rfl⟩ : syracuseStep 3370211 = 5055317) B5055317
theorem B3198275 : Blo 1496068 3198275 := bstep (se 1 (by rfl) ⟨2398706, by rfl⟩ : syracuseStep 3198275 = 4797413) B4797413
theorem B2526545 : Blo 1496068 2526545 := bstep (se 2 (by rfl) ⟨947454, by rfl⟩ : syracuseStep 2526545 = 1894909) B1894909
theorem B4795811 : Blo 1496068 4795811 := bstep (se 1 (by rfl) ⟨3596858, by rfl⟩ : syracuseStep 4795811 = 7193717) B7193717
theorem B5049809 : Blo 1496068 5049809 := bstep (se 2 (by rfl) ⟨1893678, by rfl⟩ : syracuseStep 5049809 = 3787357) B3787357
theorem B2526673 : Blo 1496068 2526673 := bstep (se 2 (by rfl) ⟨947502, by rfl⟩ : syracuseStep 2526673 = 1895005) B1895005
theorem B1707491 : Blo 1496068 1707491 := bstep (se 1 (by rfl) ⟨1280618, by rfl⟩ : syracuseStep 1707491 = 2561237) B2561237
theorem B3370481 : Blo 1496068 3370481 := bstep (se 2 (by rfl) ⟨1263930, by rfl⟩ : syracuseStep 3370481 = 2527861) B2527861
theorem B2526707 : Blo 1496068 2526707 := bstep (se 1 (by rfl) ⟨1895030, by rfl⟩ : syracuseStep 2526707 = 3790061) B3790061
theorem B3370499 : Blo 1496068 3370499 := bstep (se 1 (by rfl) ⟨2527874, by rfl⟩ : syracuseStep 3370499 = 5055749) B5055749
theorem B9596465 : Blo 1496068 9596465 := bstep (se 2 (by rfl) ⟨3598674, by rfl⟩ : syracuseStep 9596465 = 7197349) B7197349
theorem B1895987 : Blo 1496068 1895987 := bstep (se 1 (by rfl) ⟨1421990, by rfl⟩ : syracuseStep 1895987 = 2843981) B2843981
theorem B6393421 : Blo 1496068 6393421 := bstep (se 3 (by rfl) ⟨1198766, by rfl⟩ : syracuseStep 6393421 = 2397533) B2397533
theorem B8523377 : Blo 1496068 8523377 := bstep (se 2 (by rfl) ⟨3196266, by rfl⟩ : syracuseStep 8523377 = 6392533) B6392533
theorem B2526835 : Blo 1496068 2526835 := bstep (se 1 (by rfl) ⟨1895126, by rfl⟩ : syracuseStep 2526835 = 3790253) B3790253
theorem B4796081 : Blo 1496068 4796081 := bstep (se 2 (by rfl) ⟨1798530, by rfl⟩ : syracuseStep 4796081 = 3597061) B3597061
theorem B1683139 : Blo 1496068 1683139 := bstep (se 1 (by rfl) ⟨1262354, by rfl⟩ : syracuseStep 1683139 = 2524709) B2524709
theorem B2526977 : Blo 1496068 2526977 := bstep (se 2 (by rfl) ⟨947616, by rfl⟩ : syracuseStep 2526977 = 1895233) B1895233
theorem B4099889 : Blo 1496068 4099889 := bstep (se 2 (by rfl) ⟨1537458, by rfl⟩ : syracuseStep 4099889 = 3074917) B3074917
theorem B8638285 : Blo 1496068 8638285 := bstep (se 3 (by rfl) ⟨1619678, by rfl⟩ : syracuseStep 8638285 = 3239357) B3239357
theorem B1683283 : Blo 1496068 1683283 := bstep (se 1 (by rfl) ⟨1262462, by rfl⟩ : syracuseStep 1683283 = 2524925) B2524925
theorem B2527105 : Blo 1496068 2527105 := bstep (se 2 (by rfl) ⟨947664, by rfl⟩ : syracuseStep 2527105 = 1895329) B1895329
theorem B1707907 : Blo 1496068 1707907 := bstep (se 1 (by rfl) ⟨1280930, by rfl⟩ : syracuseStep 1707907 = 2561861) B2561861
theorem B2527139 : Blo 1496068 2527139 := bstep (se 1 (by rfl) ⟨1895354, by rfl⟩ : syracuseStep 2527139 = 3790709) B3790709
theorem B4263853 : Blo 1496068 4263853 := bstep (se 3 (by rfl) ⟨799472, by rfl⟩ : syracuseStep 4263853 = 1598945) B1598945
theorem B1683427 : Blo 1496068 1683427 := bstep (se 1 (by rfl) ⟨1262570, by rfl⟩ : syracuseStep 1683427 = 2525141) B2525141
theorem B5050349 : Blo 1496068 5050349 := bstep (se 3 (by rfl) ⟨946940, by rfl⟩ : syracuseStep 5050349 = 1893881) B1893881
theorem B12144653 : Blo 1496068 12144653 := bstep (se 3 (by rfl) ⟨2277122, by rfl⟩ : syracuseStep 12144653 = 4554245) B4554245
theorem B5050403 : Blo 1496068 5050403 := bstep (se 1 (by rfl) ⟨3787802, by rfl⟩ : syracuseStep 5050403 = 7575605) B7575605
theorem B2527267 : Blo 1496068 2527267 := bstep (se 1 (by rfl) ⟨1895450, by rfl⟩ : syracuseStep 2527267 = 3790901) B3790901
theorem B5394509 : Blo 1496068 5394509 := bstep (se 3 (by rfl) ⟨1011470, by rfl⟩ : syracuseStep 5394509 = 2022941) B2022941
theorem B1683571 : Blo 1496068 1683571 := bstep (se 1 (by rfl) ⟨1262678, by rfl⟩ : syracuseStep 1683571 = 2525357) B2525357
theorem B5394595 : Blo 1496068 5394595 := bstep (se 1 (by rfl) ⟨4045946, by rfl⟩ : syracuseStep 5394595 = 8091893) B8091893
theorem B3788977 : Blo 1496068 3788977 := bstep (se 2 (by rfl) ⟨1420866, by rfl⟩ : syracuseStep 3788977 = 2841733) B2841733
theorem B2527409 : Blo 1496068 2527409 := bstep (se 2 (by rfl) ⟨947778, by rfl⟩ : syracuseStep 2527409 = 1895557) B1895557
theorem B3199171 : Blo 1496068 3199171 := bstep (se 1 (by rfl) ⟨2399378, by rfl⟩ : syracuseStep 3199171 = 4798757) B4798757
theorem B12792005 : Blo 1496068 12792005 := bstep (se 4 (by rfl) ⟨1199250, by rfl⟩ : syracuseStep 12792005 = 2398501) B2398501
theorem B7581923 : Blo 1496068 7581923 := bstep (se 1 (by rfl) ⟨5686442, by rfl⟩ : syracuseStep 7581923 = 11372885) B11372885
theorem B1683715 : Blo 1496068 1683715 := bstep (se 1 (by rfl) ⟨1262786, by rfl⟩ : syracuseStep 1683715 = 2525573) B2525573
theorem B5050673 : Blo 1496068 5050673 := bstep (se 2 (by rfl) ⟨1894002, by rfl⟩ : syracuseStep 5050673 = 3788005) B3788005
theorem B2527537 : Blo 1496068 2527537 := bstep (se 2 (by rfl) ⟨947826, by rfl⟩ : syracuseStep 2527537 = 1895653) B1895653
theorem B2396483 : Blo 1496068 2396483 := bstep (se 1 (by rfl) ⟨1797362, by rfl⟩ : syracuseStep 2396483 = 3594725) B3594725
theorem B2527571 : Blo 1496068 2527571 := bstep (se 1 (by rfl) ⟨1895678, by rfl⟩ : syracuseStep 2527571 = 3791357) B3791357
theorem B2920835 : Blo 1496068 2920835 := bstep (se 1 (by rfl) ⟨2190626, by rfl⟩ : syracuseStep 2920835 = 4381253) B4381253
theorem B1683859 : Blo 1496068 1683859 := bstep (se 1 (by rfl) ⟨1262894, by rfl⟩ : syracuseStep 1683859 = 2525789) B2525789
theorem B2879921 : Blo 1496068 2879921 := bstep (se 2 (by rfl) ⟨1079970, by rfl⟩ : syracuseStep 2879921 = 2159941) B2159941
theorem B3789251 : Blo 1496068 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B2527699 : Blo 1496068 2527699 := bstep (se 1 (by rfl) ⟨1895774, by rfl⟩ : syracuseStep 2527699 = 3791549) B3791549
theorem B2396675 : Blo 1496068 2396675 := bstep (se 1 (by rfl) ⟨1797506, by rfl⟩ : syracuseStep 2396675 = 3595013) B3595013
theorem B1684003 : Blo 1496068 1684003 := bstep (se 1 (by rfl) ⟨1263002, by rfl⟩ : syracuseStep 1684003 = 2526005) B2526005
theorem B2527841 : Blo 1496068 2527841 := bstep (se 2 (by rfl) ⟨947940, by rfl⟩ : syracuseStep 2527841 = 1895881) B1895881
theorem B64713329 : Blo 1496068 64713329 := bstep (se 2 (by rfl) ⟨24267498, by rfl⟩ : syracuseStep 64713329 = 48534997) B48534997
theorem B3789443 : Blo 1496068 3789443 := bstep (se 1 (by rfl) ⟨2842082, by rfl⟩ : syracuseStep 3789443 = 5684165) B5684165
theorem B11367053 : Blo 1496068 11367053 := bstep (se 3 (by rfl) ⟨2131322, by rfl⟩ : syracuseStep 11367053 = 4262645) B4262645
theorem B1684147 : Blo 1496068 1684147 := bstep (se 1 (by rfl) ⟨1263110, by rfl⟩ : syracuseStep 1684147 = 2526221) B2526221
theorem B2527969 : Blo 1496068 2527969 := bstep (se 2 (by rfl) ⟨947988, by rfl⟩ : syracuseStep 2527969 = 1895977) B1895977
theorem B3240689 : Blo 1496068 3240689 := bstep (se 2 (by rfl) ⟨1215258, by rfl⟩ : syracuseStep 3240689 = 2430517) B2430517
theorem B5681933 : Blo 1496068 5681933 := bstep (se 3 (by rfl) ⟨1065362, by rfl⟩ : syracuseStep 5681933 = 2130725) B2130725
theorem B8090381 : Blo 1496068 8090381 := bstep (se 3 (by rfl) ⟨1516946, by rfl⟩ : syracuseStep 8090381 = 3033893) B3033893
theorem B35517205 : Blo 1496068 35517205 := bstep (se 6 (by rfl) ⟨832434, by rfl⟩ : syracuseStep 35517205 = 1664869) B1664869
theorem B8098595 : Blo 1496068 8098595 := bstep (se 1 (by rfl) ⟨6073946, by rfl⟩ : syracuseStep 8098595 = 12147893) B12147893
theorem B1684291 : Blo 1496068 1684291 := bstep (se 1 (by rfl) ⟨1263218, by rfl⟩ : syracuseStep 1684291 = 2526437) B2526437
theorem B5051213 : Blo 1496068 5051213 := bstep (se 3 (by rfl) ⟨947102, by rfl⟩ : syracuseStep 5051213 = 1894205) B1894205
theorem B5051267 : Blo 1496068 5051267 := bstep (se 1 (by rfl) ⟨3788450, by rfl⟩ : syracuseStep 5051267 = 7576901) B7576901
theorem B2732945 : Blo 1496068 2732945 := bstep (se 2 (by rfl) ⟨1024854, by rfl⟩ : syracuseStep 2732945 = 2049709) B2049709
theorem B4158353 : Blo 1496068 4158353 := bstep (se 2 (by rfl) ⟨1559382, by rfl⟩ : syracuseStep 4158353 = 3118765) B3118765
theorem B4264913 : Blo 1496068 4264913 := bstep (se 2 (by rfl) ⟨1599342, by rfl⟩ : syracuseStep 4264913 = 3198685) B3198685
theorem B1684435 : Blo 1496068 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B9597923 : Blo 1496068 9597923 := bstep (se 1 (by rfl) ⟨7198442, by rfl⟩ : syracuseStep 9597923 = 14396885) B14396885
theorem B7582733 : Blo 1496068 7582733 := bstep (se 3 (by rfl) ⟨1421762, by rfl⟩ : syracuseStep 7582733 = 2843525) B2843525
theorem B1496083 : Blo 1496068 1496083 := bstep (se 1 (by rfl) ⟨1122062, by rfl⟩ : syracuseStep 1496083 = 2244125) B2244125
theorem B1496099 : Blo 1496068 1496099 := bstep (se 1 (by rfl) ⟨1122074, by rfl⟩ : syracuseStep 1496099 = 2244149) B2244149
theorem B8524835 : Blo 1496068 8524835 := bstep (se 1 (by rfl) ⟨6393626, by rfl⟩ : syracuseStep 8524835 = 12787253) B12787253
theorem B6829105 : Blo 1496068 6829105 := bstep (se 2 (by rfl) ⟨2560914, by rfl⟩ : syracuseStep 6829105 = 5121829) B5121829
theorem B1496115 : Blo 1496068 1496115 := bstep (se 1 (by rfl) ⟨1122086, by rfl⟩ : syracuseStep 1496115 = 2244173) B2244173
theorem B1496131 : Blo 1496068 1496131 := bstep (se 1 (by rfl) ⟨1122098, by rfl⟩ : syracuseStep 1496131 = 2244197) B2244197
theorem B1496147 : Blo 1496068 1496147 := bstep (se 1 (by rfl) ⟨1122110, by rfl⟩ : syracuseStep 1496147 = 2244221) B2244221
theorem B1496163 : Blo 1496068 1496163 := bstep (se 1 (by rfl) ⟨1122122, by rfl⟩ : syracuseStep 1496163 = 2244245) B2244245
theorem B1684579 : Blo 1496068 1684579 := bstep (se 1 (by rfl) ⟨1263434, by rfl⟩ : syracuseStep 1684579 = 2526869) B2526869
theorem B1496179 : Blo 1496068 1496179 := bstep (se 1 (by rfl) ⟨1122134, by rfl⟩ : syracuseStep 1496179 = 2244269) B2244269
theorem B1496195 : Blo 1496068 1496195 := bstep (se 1 (by rfl) ⟨1122146, by rfl⟩ : syracuseStep 1496195 = 2244293) B2244293
theorem B5051537 : Blo 1496068 5051537 := bstep (se 2 (by rfl) ⟨1894326, by rfl⟩ : syracuseStep 5051537 = 3788653) B3788653
theorem B1496211 : Blo 1496068 1496211 := bstep (se 1 (by rfl) ⟨1122158, by rfl⟩ : syracuseStep 1496211 = 2244317) B2244317
theorem B1496227 : Blo 1496068 1496227 := bstep (se 1 (by rfl) ⟨1122170, by rfl⟩ : syracuseStep 1496227 = 2244341) B2244341
theorem B1496243 : Blo 1496068 1496243 := bstep (se 1 (by rfl) ⟨1122182, by rfl⟩ : syracuseStep 1496243 = 2244365) B2244365
theorem B1496259 : Blo 1496068 1496259 := bstep (se 1 (by rfl) ⟨1122194, by rfl⟩ : syracuseStep 1496259 = 2244389) B2244389
theorem B1496275 : Blo 1496068 1496275 := bstep (se 1 (by rfl) ⟨1122206, by rfl⟩ : syracuseStep 1496275 = 2244413) B2244413
theorem B2594017 : Blo 1496068 2594017 := bstep (se 2 (by rfl) ⟨972756, by rfl⟩ : syracuseStep 2594017 = 1945513) B1945513
theorem B1496291 : Blo 1496068 1496291 := bstep (se 1 (by rfl) ⟨1122218, by rfl⟩ : syracuseStep 1496291 = 2244437) B2244437
theorem B1496307 : Blo 1496068 1496307 := bstep (se 1 (by rfl) ⟨1122230, by rfl⟩ : syracuseStep 1496307 = 2244461) B2244461
theorem B1684723 : Blo 1496068 1684723 := bstep (se 1 (by rfl) ⟨1263542, by rfl⟩ : syracuseStep 1684723 = 2527085) B2527085
theorem B1496323 : Blo 1496068 1496323 := bstep (se 1 (by rfl) ⟨1122242, by rfl⟩ : syracuseStep 1496323 = 2244485) B2244485
theorem B1496339 : Blo 1496068 1496339 := bstep (se 1 (by rfl) ⟨1122254, by rfl⟩ : syracuseStep 1496339 = 2244509) B2244509
theorem B1496355 : Blo 1496068 1496355 := bstep (se 1 (by rfl) ⟨1122266, by rfl⟩ : syracuseStep 1496355 = 2244533) B2244533
theorem B1496371 : Blo 1496068 1496371 := bstep (se 1 (by rfl) ⟨1122278, by rfl⟩ : syracuseStep 1496371 = 2244557) B2244557
theorem B1496387 : Blo 1496068 1496387 := bstep (se 1 (by rfl) ⟨1122290, by rfl⟩ : syracuseStep 1496387 = 2244581) B2244581
theorem B1496403 : Blo 1496068 1496403 := bstep (se 1 (by rfl) ⟨1122302, by rfl⟩ : syracuseStep 1496403 = 2244605) B2244605
theorem B1496419 : Blo 1496068 1496419 := bstep (se 1 (by rfl) ⟨1122314, by rfl⟩ : syracuseStep 1496419 = 2244629) B2244629
theorem B1496435 : Blo 1496068 1496435 := bstep (se 1 (by rfl) ⟨1122326, by rfl⟩ : syracuseStep 1496435 = 2244653) B2244653
theorem B1496451 : Blo 1496068 1496451 := bstep (se 1 (by rfl) ⟨1122338, by rfl⟩ : syracuseStep 1496451 = 2244677) B2244677
theorem B1684867 : Blo 1496068 1684867 := bstep (se 1 (by rfl) ⟨1263650, by rfl⟩ : syracuseStep 1684867 = 2527301) B2527301
theorem B1496467 : Blo 1496068 1496467 := bstep (se 1 (by rfl) ⟨1122350, by rfl⟩ : syracuseStep 1496467 = 2244701) B2244701
theorem B1496483 : Blo 1496068 1496483 := bstep (se 1 (by rfl) ⟨1122362, by rfl⟩ : syracuseStep 1496483 = 2244725) B2244725
theorem B1496499 : Blo 1496068 1496499 := bstep (se 1 (by rfl) ⟨1122374, by rfl⟩ : syracuseStep 1496499 = 2244749) B2244749
theorem B1496515 : Blo 1496068 1496515 := bstep (se 1 (by rfl) ⟨1122386, by rfl⟩ : syracuseStep 1496515 = 2244773) B2244773
theorem B1496531 : Blo 1496068 1496531 := bstep (se 1 (by rfl) ⟨1122398, by rfl⟩ : syracuseStep 1496531 = 2244797) B2244797
theorem B1496547 : Blo 1496068 1496547 := bstep (se 1 (by rfl) ⟨1122410, by rfl⟩ : syracuseStep 1496547 = 2244821) B2244821
theorem B1496563 : Blo 1496068 1496563 := bstep (se 1 (by rfl) ⟨1122422, by rfl⟩ : syracuseStep 1496563 = 2244845) B2244845
theorem B1496579 : Blo 1496068 1496579 := bstep (se 1 (by rfl) ⟨1122434, by rfl⟩ : syracuseStep 1496579 = 2244869) B2244869
theorem B1496595 : Blo 1496068 1496595 := bstep (se 1 (by rfl) ⟨1122446, by rfl⟩ : syracuseStep 1496595 = 2244893) B2244893
theorem B1685011 : Blo 1496068 1685011 := bstep (se 1 (by rfl) ⟨1263758, by rfl⟩ : syracuseStep 1685011 = 2527517) B2527517
theorem B1496611 : Blo 1496068 1496611 := bstep (se 1 (by rfl) ⟨1122458, by rfl⟩ : syracuseStep 1496611 = 2244917) B2244917
theorem B5682737 : Blo 1496068 5682737 := bstep (se 2 (by rfl) ⟨2131026, by rfl⟩ : syracuseStep 5682737 = 4262053) B4262053
theorem B3790385 : Blo 1496068 3790385 := bstep (se 2 (by rfl) ⟨1421394, by rfl⟩ : syracuseStep 3790385 = 2842789) B2842789
theorem B1496627 : Blo 1496068 1496627 := bstep (se 1 (by rfl) ⟨1122470, by rfl⟩ : syracuseStep 1496627 = 2244941) B2244941
theorem B1496643 : Blo 1496068 1496643 := bstep (se 1 (by rfl) ⟨1122482, by rfl⟩ : syracuseStep 1496643 = 2244965) B2244965
theorem B1619539 : Blo 1496068 1619539 := bstep (se 1 (by rfl) ⟨1214654, by rfl⟩ : syracuseStep 1619539 = 2429309) B2429309
theorem B1496659 : Blo 1496068 1496659 := bstep (se 1 (by rfl) ⟨1122494, by rfl⟩ : syracuseStep 1496659 = 2244989) B2244989
theorem B1496675 : Blo 1496068 1496675 := bstep (se 1 (by rfl) ⟨1122506, by rfl⟩ : syracuseStep 1496675 = 2245013) B2245013
theorem B3790435 : Blo 1496068 3790435 := bstep (se 1 (by rfl) ⟨2842826, by rfl⟩ : syracuseStep 3790435 = 5685653) B5685653
theorem B4265585 : Blo 1496068 4265585 := bstep (se 2 (by rfl) ⟨1599594, by rfl⟩ : syracuseStep 4265585 = 3199189) B3199189
theorem B1496691 : Blo 1496068 1496691 := bstep (se 1 (by rfl) ⟨1122518, by rfl⟩ : syracuseStep 1496691 = 2245037) B2245037
theorem B1496707 : Blo 1496068 1496707 := bstep (se 1 (by rfl) ⟨1122530, by rfl⟩ : syracuseStep 1496707 = 2245061) B2245061
theorem B1496723 : Blo 1496068 1496723 := bstep (se 1 (by rfl) ⟨1122542, by rfl⟩ : syracuseStep 1496723 = 2245085) B2245085
theorem B1496739 : Blo 1496068 1496739 := bstep (se 1 (by rfl) ⟨1122554, by rfl⟩ : syracuseStep 1496739 = 2245109) B2245109
theorem B1685155 : Blo 1496068 1685155 := bstep (se 1 (by rfl) ⟨1263866, by rfl⟩ : syracuseStep 1685155 = 2527733) B2527733
theorem B5052077 : Blo 1496068 5052077 := bstep (se 3 (by rfl) ⟨947264, by rfl⟩ : syracuseStep 5052077 = 1894529) B1894529
theorem B1496755 : Blo 1496068 1496755 := bstep (se 1 (by rfl) ⟨1122566, by rfl⟩ : syracuseStep 1496755 = 2245133) B2245133
theorem B1496771 : Blo 1496068 1496771 := bstep (se 1 (by rfl) ⟨1122578, by rfl⟩ : syracuseStep 1496771 = 2245157) B2245157
theorem B1496787 : Blo 1496068 1496787 := bstep (se 1 (by rfl) ⟨1122590, by rfl⟩ : syracuseStep 1496787 = 2245181) B2245181
theorem B1496803 : Blo 1496068 1496803 := bstep (se 1 (by rfl) ⟨1122602, by rfl⟩ : syracuseStep 1496803 = 2245205) B2245205
theorem B5052131 : Blo 1496068 5052131 := bstep (se 1 (by rfl) ⟨3789098, by rfl⟩ : syracuseStep 5052131 = 7578197) B7578197
theorem B7575281 : Blo 1496068 7575281 := bstep (se 2 (by rfl) ⟨2840730, by rfl⟩ : syracuseStep 7575281 = 5681461) B5681461
theorem B3790577 : Blo 1496068 3790577 := bstep (se 2 (by rfl) ⟨1421466, by rfl⟩ : syracuseStep 3790577 = 2842933) B2842933
theorem B1496819 : Blo 1496068 1496819 := bstep (se 1 (by rfl) ⟨1122614, by rfl⟩ : syracuseStep 1496819 = 2245229) B2245229
theorem B1496835 : Blo 1496068 1496835 := bstep (se 1 (by rfl) ⟨1122626, by rfl⟩ : syracuseStep 1496835 = 2245253) B2245253
theorem B5764877 : Blo 1496068 5764877 := bstep (se 3 (by rfl) ⟨1080914, by rfl⟩ : syracuseStep 5764877 = 2161829) B2161829
theorem B1496851 : Blo 1496068 1496851 := bstep (se 1 (by rfl) ⟨1122638, by rfl⟩ : syracuseStep 1496851 = 2245277) B2245277
theorem B1496867 : Blo 1496068 1496867 := bstep (se 1 (by rfl) ⟨1122650, by rfl⟩ : syracuseStep 1496867 = 2245301) B2245301
theorem B1496883 : Blo 1496068 1496883 := bstep (se 1 (by rfl) ⟨1122662, by rfl⟩ : syracuseStep 1496883 = 2245325) B2245325
theorem B1685299 : Blo 1496068 1685299 := bstep (se 1 (by rfl) ⟨1263974, by rfl⟩ : syracuseStep 1685299 = 2527949) B2527949
theorem B1496899 : Blo 1496068 1496899 := bstep (se 1 (by rfl) ⟨1122674, by rfl⟩ : syracuseStep 1496899 = 2245349) B2245349
theorem B1496915 : Blo 1496068 1496915 := bstep (se 1 (by rfl) ⟨1122686, by rfl⟩ : syracuseStep 1496915 = 2245373) B2245373
theorem B1496931 : Blo 1496068 1496931 := bstep (se 1 (by rfl) ⟨1122698, by rfl⟩ : syracuseStep 1496931 = 2245397) B2245397
theorem B1496947 : Blo 1496068 1496947 := bstep (se 1 (by rfl) ⟨1122710, by rfl⟩ : syracuseStep 1496947 = 2245421) B2245421
theorem B1496963 : Blo 1496068 1496963 := bstep (se 1 (by rfl) ⟨1122722, by rfl⟩ : syracuseStep 1496963 = 2245445) B2245445
theorem B2398097 : Blo 1496068 2398097 := bstep (se 2 (by rfl) ⟨899286, by rfl⟩ : syracuseStep 2398097 = 1798573) B1798573
theorem B1496979 : Blo 1496068 1496979 := bstep (se 1 (by rfl) ⟨1122734, by rfl⟩ : syracuseStep 1496979 = 2245469) B2245469
theorem B1496995 : Blo 1496068 1496995 := bstep (se 1 (by rfl) ⟨1122746, by rfl⟩ : syracuseStep 1496995 = 2245493) B2245493
theorem B1497011 : Blo 1496068 1497011 := bstep (se 1 (by rfl) ⟨1122758, by rfl⟩ : syracuseStep 1497011 = 2245517) B2245517
theorem B1497027 : Blo 1496068 1497027 := bstep (se 1 (by rfl) ⟨1122770, by rfl⟩ : syracuseStep 1497027 = 2245541) B2245541
theorem B8206285 : Blo 1496068 8206285 := bstep (se 3 (by rfl) ⟨1538678, by rfl⟩ : syracuseStep 8206285 = 3077357) B3077357
theorem B1497043 : Blo 1496068 1497043 := bstep (se 1 (by rfl) ⟨1122782, by rfl⟩ : syracuseStep 1497043 = 2245565) B2245565
theorem B1497059 : Blo 1496068 1497059 := bstep (se 1 (by rfl) ⟨1122794, by rfl⟩ : syracuseStep 1497059 = 2245589) B2245589
theorem B5191661 : Blo 1496068 5191661 := bstep (se 3 (by rfl) ⟨973436, by rfl⟩ : syracuseStep 5191661 = 1946873) B1946873
theorem B5052401 : Blo 1496068 5052401 := bstep (se 2 (by rfl) ⟨1894650, by rfl⟩ : syracuseStep 5052401 = 3789301) B3789301
theorem B1497075 : Blo 1496068 1497075 := bstep (se 1 (by rfl) ⟨1122806, by rfl⟩ : syracuseStep 1497075 = 2245613) B2245613
theorem B2840579 : Blo 1496068 2840579 := bstep (se 1 (by rfl) ⟨2130434, by rfl⟩ : syracuseStep 2840579 = 4260869) B4260869
theorem B1497091 : Blo 1496068 1497091 := bstep (se 1 (by rfl) ⟨1122818, by rfl⟩ : syracuseStep 1497091 = 2245637) B2245637
theorem B8525837 : Blo 1496068 8525837 := bstep (se 3 (by rfl) ⟨1598594, by rfl⟩ : syracuseStep 8525837 = 3197189) B3197189
theorem B1497107 : Blo 1496068 1497107 := bstep (se 1 (by rfl) ⟨1122830, by rfl⟩ : syracuseStep 1497107 = 2245661) B2245661
theorem B1497123 : Blo 1496068 1497123 := bstep (se 1 (by rfl) ⟨1122842, by rfl⟩ : syracuseStep 1497123 = 2245685) B2245685
theorem B1497139 : Blo 1496068 1497139 := bstep (se 1 (by rfl) ⟨1122854, by rfl⟩ : syracuseStep 1497139 = 2245709) B2245709
theorem B1497155 : Blo 1496068 1497155 := bstep (se 1 (by rfl) ⟨1122866, by rfl⟩ : syracuseStep 1497155 = 2245733) B2245733
theorem B4798541 : Blo 1496068 4798541 := bstep (se 3 (by rfl) ⟨899726, by rfl⟩ : syracuseStep 4798541 = 1799453) B1799453
theorem B1497171 : Blo 1496068 1497171 := bstep (se 1 (by rfl) ⟨1122878, by rfl⟩ : syracuseStep 1497171 = 2245757) B2245757
theorem B1497187 : Blo 1496068 1497187 := bstep (se 1 (by rfl) ⟨1122890, by rfl⟩ : syracuseStep 1497187 = 2245781) B2245781
theorem B4323437 : Blo 1496068 4323437 := bstep (se 3 (by rfl) ⟨810644, by rfl⟩ : syracuseStep 4323437 = 1621289) B1621289
theorem B1497203 : Blo 1496068 1497203 := bstep (se 1 (by rfl) ⟨1122902, by rfl⟩ : syracuseStep 1497203 = 2245805) B2245805
theorem B1497219 : Blo 1496068 1497219 := bstep (se 1 (by rfl) ⟨1122914, by rfl⟩ : syracuseStep 1497219 = 2245829) B2245829
theorem B1497235 : Blo 1496068 1497235 := bstep (se 1 (by rfl) ⟨1122926, by rfl⟩ : syracuseStep 1497235 = 2245853) B2245853
theorem B1497251 : Blo 1496068 1497251 := bstep (se 1 (by rfl) ⟨1122938, by rfl⟩ : syracuseStep 1497251 = 2245877) B2245877
theorem B4044973 : Blo 1496068 4044973 := bstep (se 3 (by rfl) ⟨758432, by rfl⟩ : syracuseStep 4044973 = 1516865) B1516865
theorem B1497267 : Blo 1496068 1497267 := bstep (se 1 (by rfl) ⟨1122950, by rfl⟩ : syracuseStep 1497267 = 2245901) B2245901
theorem B1497283 : Blo 1496068 1497283 := bstep (se 1 (by rfl) ⟨1122962, by rfl⟩ : syracuseStep 1497283 = 2245925) B2245925
theorem B5683405 : Blo 1496068 5683405 := bstep (se 3 (by rfl) ⟨1065638, by rfl⟩ : syracuseStep 5683405 = 2131277) B2131277
theorem B1497299 : Blo 1496068 1497299 := bstep (se 1 (by rfl) ⟨1122974, by rfl⟩ : syracuseStep 1497299 = 2245949) B2245949
theorem B1497315 : Blo 1496068 1497315 := bstep (se 1 (by rfl) ⟨1122986, by rfl⟩ : syracuseStep 1497315 = 2245973) B2245973
theorem B1497331 : Blo 1496068 1497331 := bstep (se 1 (by rfl) ⟨1122998, by rfl⟩ : syracuseStep 1497331 = 2245997) B2245997
theorem B1497347 : Blo 1496068 1497347 := bstep (se 1 (by rfl) ⟨1123010, by rfl⟩ : syracuseStep 1497347 = 2246021) B2246021
theorem B1497363 : Blo 1496068 1497363 := bstep (se 1 (by rfl) ⟨1123022, by rfl⟩ : syracuseStep 1497363 = 2246045) B2246045
theorem B1497379 : Blo 1496068 1497379 := bstep (se 1 (by rfl) ⟨1123034, by rfl⟩ : syracuseStep 1497379 = 2246069) B2246069
theorem B1497395 : Blo 1496068 1497395 := bstep (se 1 (by rfl) ⟨1123046, by rfl⟩ : syracuseStep 1497395 = 2246093) B2246093
theorem B2275651 : Blo 1496068 2275651 := bstep (se 1 (by rfl) ⟨1706738, by rfl⟩ : syracuseStep 2275651 = 3413477) B3413477
theorem B1497411 : Blo 1496068 1497411 := bstep (se 1 (by rfl) ⟨1123058, by rfl⟩ : syracuseStep 1497411 = 2246117) B2246117
theorem B1497427 : Blo 1496068 1497427 := bstep (se 1 (by rfl) ⟨1123070, by rfl⟩ : syracuseStep 1497427 = 2246141) B2246141
theorem B1497443 : Blo 1496068 1497443 := bstep (se 1 (by rfl) ⟨1123082, by rfl⟩ : syracuseStep 1497443 = 2246165) B2246165
theorem B1497459 : Blo 1496068 1497459 := bstep (se 1 (by rfl) ⟨1123094, by rfl⟩ : syracuseStep 1497459 = 2246189) B2246189
theorem B1497475 : Blo 1496068 1497475 := bstep (se 1 (by rfl) ⟨1123106, by rfl⟩ : syracuseStep 1497475 = 2246213) B2246213
theorem B1497491 : Blo 1496068 1497491 := bstep (se 1 (by rfl) ⟨1123118, by rfl⟩ : syracuseStep 1497491 = 2246237) B2246237
theorem B7190947 : Blo 1496068 7190947 := bstep (se 1 (by rfl) ⟨5393210, by rfl⟩ : syracuseStep 7190947 = 10786421) B10786421
theorem B1497507 : Blo 1496068 1497507 := bstep (se 1 (by rfl) ⟨1123130, by rfl⟩ : syracuseStep 1497507 = 2246261) B2246261
theorem B1497523 : Blo 1496068 1497523 := bstep (se 1 (by rfl) ⟨1123142, by rfl⟩ : syracuseStep 1497523 = 2246285) B2246285
theorem B1497539 : Blo 1496068 1497539 := bstep (se 1 (by rfl) ⟨1123154, by rfl⟩ : syracuseStep 1497539 = 2246309) B2246309
theorem B1497555 : Blo 1496068 1497555 := bstep (se 1 (by rfl) ⟨1123166, by rfl⟩ : syracuseStep 1497555 = 2246333) B2246333
theorem B1497571 : Blo 1496068 1497571 := bstep (se 1 (by rfl) ⟨1123178, by rfl⟩ : syracuseStep 1497571 = 2246357) B2246357
theorem B1497587 : Blo 1496068 1497587 := bstep (se 1 (by rfl) ⟨1123190, by rfl⟩ : syracuseStep 1497587 = 2246381) B2246381
theorem B1497603 : Blo 1496068 1497603 := bstep (se 1 (by rfl) ⟨1123202, by rfl⟩ : syracuseStep 1497603 = 2246405) B2246405
theorem B5052941 : Blo 1496068 5052941 := bstep (se 3 (by rfl) ⟨947426, by rfl⟩ : syracuseStep 5052941 = 1894853) B1894853
theorem B2734609 : Blo 1496068 2734609 := bstep (se 2 (by rfl) ⟨1025478, by rfl⟩ : syracuseStep 2734609 = 2050957) B2050957
theorem B1497619 : Blo 1496068 1497619 := bstep (se 1 (by rfl) ⟨1123214, by rfl⟩ : syracuseStep 1497619 = 2246429) B2246429
theorem B1497635 : Blo 1496068 1497635 := bstep (se 1 (by rfl) ⟨1123226, by rfl⟩ : syracuseStep 1497635 = 2246453) B2246453
theorem B1497651 : Blo 1496068 1497651 := bstep (se 1 (by rfl) ⟨1123238, by rfl⟩ : syracuseStep 1497651 = 2246477) B2246477
theorem B5052995 : Blo 1496068 5052995 := bstep (se 1 (by rfl) ⟨3789746, by rfl⟩ : syracuseStep 5052995 = 7579493) B7579493
theorem B1497667 : Blo 1496068 1497667 := bstep (se 1 (by rfl) ⟨1123250, by rfl⟩ : syracuseStep 1497667 = 2246501) B2246501
theorem B1497683 : Blo 1496068 1497683 := bstep (se 1 (by rfl) ⟨1123262, by rfl⟩ : syracuseStep 1497683 = 2246525) B2246525
theorem B1497699 : Blo 1496068 1497699 := bstep (se 1 (by rfl) ⟨1123274, by rfl⟩ : syracuseStep 1497699 = 2246549) B2246549
theorem B1497715 : Blo 1496068 1497715 := bstep (se 1 (by rfl) ⟨1123286, by rfl⟩ : syracuseStep 1497715 = 2246573) B2246573
theorem B1497731 : Blo 1496068 1497731 := bstep (se 1 (by rfl) ⟨1123298, by rfl⟩ : syracuseStep 1497731 = 2246597) B2246597
theorem B1497747 : Blo 1496068 1497747 := bstep (se 1 (by rfl) ⟨1123310, by rfl⟩ : syracuseStep 1497747 = 2246621) B2246621
theorem B1497763 : Blo 1496068 1497763 := bstep (se 1 (by rfl) ⟨1123322, by rfl⟩ : syracuseStep 1497763 = 2246645) B2246645
theorem B1497779 : Blo 1496068 1497779 := bstep (se 1 (by rfl) ⟨1123334, by rfl⟩ : syracuseStep 1497779 = 2246669) B2246669
theorem B1497795 : Blo 1496068 1497795 := bstep (se 1 (by rfl) ⟨1123346, by rfl⟩ : syracuseStep 1497795 = 2246693) B2246693
theorem B1497811 : Blo 1496068 1497811 := bstep (se 1 (by rfl) ⟨1123358, by rfl⟩ : syracuseStep 1497811 = 2246717) B2246717
theorem B3791569 : Blo 1496068 3791569 := bstep (se 2 (by rfl) ⟨1421838, by rfl⟩ : syracuseStep 3791569 = 2843677) B2843677
theorem B1497827 : Blo 1496068 1497827 := bstep (se 1 (by rfl) ⟨1123370, by rfl⟩ : syracuseStep 1497827 = 2246741) B2246741
theorem B1497843 : Blo 1496068 1497843 := bstep (se 1 (by rfl) ⟨1123382, by rfl⟩ : syracuseStep 1497843 = 2246765) B2246765
theorem B1497859 : Blo 1496068 1497859 := bstep (se 1 (by rfl) ⟨1123394, by rfl⟩ : syracuseStep 1497859 = 2246789) B2246789
theorem B1497875 : Blo 1496068 1497875 := bstep (se 1 (by rfl) ⟨1123406, by rfl⟩ : syracuseStep 1497875 = 2246813) B2246813
theorem B1497891 : Blo 1496068 1497891 := bstep (se 1 (by rfl) ⟨1123418, by rfl⟩ : syracuseStep 1497891 = 2246837) B2246837
theorem B1497907 : Blo 1496068 1497907 := bstep (se 1 (by rfl) ⟨1123430, by rfl⟩ : syracuseStep 1497907 = 2246861) B2246861
theorem B4553539 : Blo 1496068 4553539 := bstep (se 1 (by rfl) ⟨3415154, by rfl⟩ : syracuseStep 4553539 = 6830309) B6830309
theorem B1497923 : Blo 1496068 1497923 := bstep (se 1 (by rfl) ⟨1123442, by rfl⟩ : syracuseStep 1497923 = 2246885) B2246885
theorem B5053265 : Blo 1496068 5053265 := bstep (se 2 (by rfl) ⟨1894974, by rfl⟩ : syracuseStep 5053265 = 3789949) B3789949
theorem B1497939 : Blo 1496068 1497939 := bstep (se 1 (by rfl) ⟨1123454, by rfl⟩ : syracuseStep 1497939 = 2246909) B2246909
theorem B1497955 : Blo 1496068 1497955 := bstep (se 1 (by rfl) ⟨1123466, by rfl⟩ : syracuseStep 1497955 = 2246933) B2246933
theorem B1497971 : Blo 1496068 1497971 := bstep (se 1 (by rfl) ⟨1123478, by rfl⟩ : syracuseStep 1497971 = 2246957) B2246957
theorem B2841475 : Blo 1496068 2841475 := bstep (se 1 (by rfl) ⟨2131106, by rfl⟩ : syracuseStep 2841475 = 4262213) B4262213
theorem B1497987 : Blo 1496068 1497987 := bstep (se 1 (by rfl) ⟨1123490, by rfl⟩ : syracuseStep 1497987 = 2246981) B2246981
theorem B28769165 : Blo 1496068 28769165 := bstep (se 3 (by rfl) ⟨5394218, by rfl⟩ : syracuseStep 28769165 = 10788437) B10788437
theorem B36436877 : Blo 1496068 36436877 := bstep (se 3 (by rfl) ⟨6831914, by rfl⟩ : syracuseStep 36436877 = 13663829) B13663829
theorem B1498003 : Blo 1496068 1498003 := bstep (se 1 (by rfl) ⟨1123502, by rfl⟩ : syracuseStep 1498003 = 2247005) B2247005
theorem B1498019 : Blo 1496068 1498019 := bstep (se 1 (by rfl) ⟨1123514, by rfl⟩ : syracuseStep 1498019 = 2247029) B2247029
theorem B1498035 : Blo 1496068 1498035 := bstep (se 1 (by rfl) ⟨1123526, by rfl⟩ : syracuseStep 1498035 = 2247053) B2247053
theorem B1498051 : Blo 1496068 1498051 := bstep (se 1 (by rfl) ⟨1123538, by rfl⟩ : syracuseStep 1498051 = 2247077) B2247077
theorem B11361221 : Blo 1496068 11361221 := bstep (se 4 (by rfl) ⟨1065114, by rfl⟩ : syracuseStep 11361221 = 2130229) B2130229
theorem B1498067 : Blo 1496068 1498067 := bstep (se 1 (by rfl) ⟨1123550, by rfl⟩ : syracuseStep 1498067 = 2247101) B2247101
theorem B5684195 : Blo 1496068 5684195 := bstep (se 1 (by rfl) ⟨4263146, by rfl⟩ : syracuseStep 5684195 = 8526293) B8526293
theorem B3791843 : Blo 1496068 3791843 := bstep (se 1 (by rfl) ⟨2843882, by rfl⟩ : syracuseStep 3791843 = 5687765) B5687765
theorem B2841635 : Blo 1496068 2841635 := bstep (se 1 (by rfl) ⟨2131226, by rfl⟩ : syracuseStep 2841635 = 4262453) B4262453
theorem B21593141 : Blo 1496068 21593141 := bstep (se 5 (by rfl) ⟨1012178, by rfl⟩ : syracuseStep 21593141 = 2024357) B2024357
theorem B7576739 : Blo 1496068 7576739 := bstep (se 1 (by rfl) ⟨5682554, by rfl⟩ : syracuseStep 7576739 = 11365109) B11365109
theorem B3366161 : Blo 1496068 3366161 := bstep (se 2 (by rfl) ⟨1262310, by rfl⟩ : syracuseStep 3366161 = 2524621) B2524621
theorem B3366179 : Blo 1496068 3366179 := bstep (se 1 (by rfl) ⟨2524634, by rfl⟩ : syracuseStep 3366179 = 5049269) B5049269
theorem B5053805 : Blo 1496068 5053805 := bstep (se 3 (by rfl) ⟨947588, by rfl⟩ : syracuseStep 5053805 = 1895177) B1895177
theorem B5053859 : Blo 1496068 5053859 := bstep (se 1 (by rfl) ⟨3790394, by rfl⟩ : syracuseStep 5053859 = 7580789) B7580789
theorem B21052853 : Blo 1496068 21052853 := bstep (se 5 (by rfl) ⟨986852, by rfl⟩ : syracuseStep 21052853 = 1973705) B1973705
theorem B2276819 : Blo 1496068 2276819 := bstep (se 1 (by rfl) ⟨1707614, by rfl⟩ : syracuseStep 2276819 = 3415229) B3415229
theorem B11369969 : Blo 1496068 11369969 := bstep (se 2 (by rfl) ⟨4263738, by rfl⟩ : syracuseStep 11369969 = 8527477) B8527477
theorem B3415537 : Blo 1496068 3415537 := bstep (se 2 (by rfl) ⟨1280826, by rfl⟩ : syracuseStep 3415537 = 2561653) B2561653
theorem B2244113 : Blo 1496068 2244113 := bstep (se 2 (by rfl) ⟨841542, by rfl⟩ : syracuseStep 2244113 = 1683085) B1683085
theorem B2244131 : Blo 1496068 2244131 := bstep (se 1 (by rfl) ⟨1683098, by rfl⟩ : syracuseStep 2244131 = 3366197) B3366197
theorem B3366449 : Blo 1496068 3366449 := bstep (se 2 (by rfl) ⟨1262418, by rfl⟩ : syracuseStep 3366449 = 2524837) B2524837
theorem B2244161 : Blo 1496068 2244161 := bstep (se 2 (by rfl) ⟨841560, by rfl⟩ : syracuseStep 2244161 = 1683121) B1683121
theorem B3366467 : Blo 1496068 3366467 := bstep (se 1 (by rfl) ⟨2524850, by rfl⟩ : syracuseStep 3366467 = 5049701) B5049701
theorem B2244179 : Blo 1496068 2244179 := bstep (se 1 (by rfl) ⟨1683134, by rfl⟩ : syracuseStep 2244179 = 3366269) B3366269
theorem B2244209 : Blo 1496068 2244209 := bstep (se 2 (by rfl) ⟨841578, by rfl⟩ : syracuseStep 2244209 = 1683157) B1683157
theorem B5684849 : Blo 1496068 5684849 := bstep (se 2 (by rfl) ⟨2131818, by rfl⟩ : syracuseStep 5684849 = 4263637) B4263637
theorem B2244227 : Blo 1496068 2244227 := bstep (se 1 (by rfl) ⟨1683170, by rfl⟩ : syracuseStep 2244227 = 3366341) B3366341
theorem B3595907 : Blo 1496068 3595907 := bstep (se 1 (by rfl) ⟨2696930, by rfl⟩ : syracuseStep 3595907 = 5393861) B5393861
theorem B2244257 : Blo 1496068 2244257 := bstep (se 2 (by rfl) ⟨841596, by rfl⟩ : syracuseStep 2244257 = 1683193) B1683193
theorem B5054129 : Blo 1496068 5054129 := bstep (se 2 (by rfl) ⟨1895298, by rfl⟩ : syracuseStep 5054129 = 3790597) B3790597
theorem B2244275 : Blo 1496068 2244275 := bstep (se 1 (by rfl) ⟨1683206, by rfl⟩ : syracuseStep 2244275 = 3366413) B3366413
theorem B10796741 : Blo 1496068 10796741 := bstep (se 4 (by rfl) ⟨1012194, by rfl⟩ : syracuseStep 10796741 = 2024389) B2024389
theorem B2244305 : Blo 1496068 2244305 := bstep (se 2 (by rfl) ⟨841614, by rfl⟩ : syracuseStep 2244305 = 1683229) B1683229
theorem B2244323 : Blo 1496068 2244323 := bstep (se 1 (by rfl) ⟨1683242, by rfl⟩ : syracuseStep 2244323 = 3366485) B3366485
theorem B2244353 : Blo 1496068 2244353 := bstep (se 2 (by rfl) ⟨841632, by rfl⟩ : syracuseStep 2244353 = 1683265) B1683265
theorem B2244371 : Blo 1496068 2244371 := bstep (se 1 (by rfl) ⟨1683278, by rfl⟩ : syracuseStep 2244371 = 3366557) B3366557
theorem B2244401 : Blo 1496068 2244401 := bstep (se 2 (by rfl) ⟨841650, by rfl⟩ : syracuseStep 2244401 = 1683301) B1683301
theorem B24272693 : Blo 1496068 24272693 := bstep (se 5 (by rfl) ⟨1137782, by rfl⟩ : syracuseStep 24272693 = 2275565) B2275565
theorem B2244419 : Blo 1496068 2244419 := bstep (se 1 (by rfl) ⟨1683314, by rfl⟩ : syracuseStep 2244419 = 3366629) B3366629
theorem B3366737 : Blo 1496068 3366737 := bstep (se 2 (by rfl) ⟨1262526, by rfl⟩ : syracuseStep 3366737 = 2525053) B2525053
theorem B2244449 : Blo 1496068 2244449 := bstep (se 2 (by rfl) ⟨841668, by rfl⟩ : syracuseStep 2244449 = 1683337) B1683337
theorem B2023265 : Blo 1496068 2023265 := bstep (se 2 (by rfl) ⟨758724, by rfl⟩ : syracuseStep 2023265 = 1517449) B1517449
theorem B3366755 : Blo 1496068 3366755 := bstep (se 1 (by rfl) ⟨2525066, by rfl⟩ : syracuseStep 3366755 = 5050133) B5050133
theorem B6397795 : Blo 1496068 6397795 := bstep (se 1 (by rfl) ⟨4798346, by rfl⟩ : syracuseStep 6397795 = 9596693) B9596693
theorem B2244467 : Blo 1496068 2244467 := bstep (se 1 (by rfl) ⟨1683350, by rfl⟩ : syracuseStep 2244467 = 3366701) B3366701
theorem B2244497 : Blo 1496068 2244497 := bstep (se 2 (by rfl) ⟨841686, by rfl⟩ : syracuseStep 2244497 = 1683373) B1683373
theorem B2244515 : Blo 1496068 2244515 := bstep (se 1 (by rfl) ⟨1683386, by rfl⟩ : syracuseStep 2244515 = 3366773) B3366773
theorem B2244545 : Blo 1496068 2244545 := bstep (se 2 (by rfl) ⟨841704, by rfl⟩ : syracuseStep 2244545 = 1683409) B1683409
theorem B7577549 : Blo 1496068 7577549 := bstep (se 3 (by rfl) ⟨1420790, by rfl⟩ : syracuseStep 7577549 = 2841581) B2841581
theorem B2244563 : Blo 1496068 2244563 := bstep (se 1 (by rfl) ⟨1683422, by rfl⟩ : syracuseStep 2244563 = 3366845) B3366845
theorem B2244593 : Blo 1496068 2244593 := bstep (se 2 (by rfl) ⟨841722, by rfl⟩ : syracuseStep 2244593 = 1683445) B1683445
theorem B3366935 : Blo 1496068 3366935 := bstep (se 1 (by rfl) ⟨2525201, by rfl⟩ : syracuseStep 3366935 = 5050403) B5050403
theorem B3596339 : Blo 1496068 3596339 := bstep (se 1 (by rfl) ⟨2697254, by rfl⟩ : syracuseStep 3596339 = 5394509) B5394509
theorem B2244683 : Blo 1496068 2244683 := bstep (se 1 (by rfl) ⟨1683512, by rfl⟩ : syracuseStep 2244683 = 3367025) B3367025
theorem B2244695 : Blo 1496068 2244695 := bstep (se 1 (by rfl) ⟨1683521, by rfl⟩ : syracuseStep 2244695 = 3367043) B3367043
theorem B16408669 : Blo 1496068 16408669 := bstep (se 3 (by rfl) ⟨3076625, by rfl⟩ : syracuseStep 16408669 = 6153251) B6153251
theorem B8528003 : Blo 1496068 8528003 := bstep (se 1 (by rfl) ⟨6396002, by rfl⟩ : syracuseStep 8528003 = 12792005) B12792005
theorem B5054615 : Blo 1496068 5054615 := bstep (se 1 (by rfl) ⟨3790961, by rfl⟩ : syracuseStep 5054615 = 7581923) B7581923
theorem B9109655 : Blo 1496068 9109655 := bstep (se 1 (by rfl) ⟨6832241, by rfl⟩ : syracuseStep 9109655 = 13664483) B13664483
theorem B2244761 : Blo 1496068 2244761 := bstep (se 2 (by rfl) ⟨841785, by rfl⟩ : syracuseStep 2244761 = 1683571) B1683571
theorem B3367115 : Blo 1496068 3367115 := bstep (se 1 (by rfl) ⟨2525336, by rfl⟩ : syracuseStep 3367115 = 5050673) B5050673
theorem B1597655 : Blo 1496068 1597655 := bstep (se 1 (by rfl) ⟨1198241, by rfl⟩ : syracuseStep 1597655 = 2396483) B2396483
theorem B7192793 : Blo 1496068 7192793 := bstep (se 2 (by rfl) ⟨2697297, by rfl⟩ : syracuseStep 7192793 = 5394595) B5394595
theorem B3367169 : Blo 1496068 3367169 := bstep (se 2 (by rfl) ⟨1262688, by rfl⟩ : syracuseStep 3367169 = 2525377) B2525377
theorem B2244875 : Blo 1496068 2244875 := bstep (se 1 (by rfl) ⟨1683656, by rfl⟩ : syracuseStep 2244875 = 3367313) B3367313
theorem B7577873 : Blo 1496068 7577873 := bstep (se 2 (by rfl) ⟨2841702, by rfl⟩ : syracuseStep 7577873 = 5683405) B5683405
theorem B8093969 : Blo 1496068 8093969 := bstep (se 2 (by rfl) ⟨3035238, by rfl⟩ : syracuseStep 8093969 = 6070477) B6070477
theorem B2244887 : Blo 1496068 2244887 := bstep (se 1 (by rfl) ⟨1683665, by rfl⟩ : syracuseStep 2244887 = 3367331) B3367331
theorem B2244953 : Blo 1496068 2244953 := bstep (se 2 (by rfl) ⟨841857, by rfl⟩ : syracuseStep 2244953 = 1683715) B1683715
theorem B2843009 : Blo 1496068 2843009 := bstep (se 2 (by rfl) ⟨1066128, by rfl⟩ : syracuseStep 2843009 = 2132257) B2132257
theorem B7578035 : Blo 1496068 7578035 := bstep (se 1 (by rfl) ⟨5683526, by rfl⟩ : syracuseStep 7578035 = 11367053) B11367053
theorem B2245067 : Blo 1496068 2245067 := bstep (se 1 (by rfl) ⟨1683800, by rfl⟩ : syracuseStep 2245067 = 3367601) B3367601
theorem B2245079 : Blo 1496068 2245079 := bstep (se 1 (by rfl) ⟨1683809, by rfl⟩ : syracuseStep 2245079 = 3367619) B3367619
theorem B3367385 : Blo 1496068 3367385 := bstep (se 2 (by rfl) ⟨1262769, by rfl⟩ : syracuseStep 3367385 = 2525539) B2525539
theorem B3596761 : Blo 1496068 3596761 := bstep (se 2 (by rfl) ⟨1348785, by rfl⟩ : syracuseStep 3596761 = 2697571) B2697571
theorem B5399063 : Blo 1496068 5399063 := bstep (se 1 (by rfl) ⟨4049297, by rfl⟩ : syracuseStep 5399063 = 8098595) B8098595
theorem B2130457 : Blo 1496068 2130457 := bstep (se 2 (by rfl) ⟨798921, by rfl⟩ : syracuseStep 2130457 = 1597843) B1597843
theorem B2245145 : Blo 1496068 2245145 := bstep (se 2 (by rfl) ⟨841929, by rfl⟩ : syracuseStep 2245145 = 1683859) B1683859
theorem B3367475 : Blo 1496068 3367475 := bstep (se 1 (by rfl) ⟨2525606, by rfl⟩ : syracuseStep 3367475 = 5051213) B5051213
theorem B5685835 : Blo 1496068 5685835 := bstep (se 1 (by rfl) ⟨4264376, by rfl⟩ : syracuseStep 5685835 = 8528753) B8528753
theorem B3367511 : Blo 1496068 3367511 := bstep (se 1 (by rfl) ⟨2525633, by rfl⟩ : syracuseStep 3367511 = 5051267) B5051267
theorem B2130571 : Blo 1496068 2130571 := bstep (se 1 (by rfl) ⟨1597928, by rfl⟩ : syracuseStep 2130571 = 3195857) B3195857
theorem B2245259 : Blo 1496068 2245259 := bstep (se 1 (by rfl) ⟨1683944, by rfl⟩ : syracuseStep 2245259 = 3367889) B3367889
theorem B2843275 : Blo 1496068 2843275 := bstep (se 1 (by rfl) ⟨2132456, by rfl⟩ : syracuseStep 2843275 = 4264913) B4264913
theorem B2245271 : Blo 1496068 2245271 := bstep (se 1 (by rfl) ⟨1683953, by rfl⟩ : syracuseStep 2245271 = 3367907) B3367907
theorem B6398615 : Blo 1496068 6398615 := bstep (se 1 (by rfl) ⟨4798961, by rfl⟩ : syracuseStep 6398615 = 9597923) B9597923
theorem B5055155 : Blo 1496068 5055155 := bstep (se 1 (by rfl) ⟨3791366, by rfl⟩ : syracuseStep 5055155 = 7582733) B7582733
theorem B3596993 : Blo 1496068 3596993 := bstep (se 2 (by rfl) ⟨1348872, by rfl⟩ : syracuseStep 3596993 = 2697745) B2697745
theorem B3646145 : Blo 1496068 3646145 := bstep (se 2 (by rfl) ⟨1367304, by rfl⟩ : syracuseStep 3646145 = 2734609) B2734609
theorem B2245337 : Blo 1496068 2245337 := bstep (se 2 (by rfl) ⟨842001, by rfl⟩ : syracuseStep 2245337 = 1684003) B1684003
theorem B3367691 : Blo 1496068 3367691 := bstep (se 1 (by rfl) ⟨2525768, by rfl⟩ : syracuseStep 3367691 = 5051537) B5051537
theorem B6390551 : Blo 1496068 6390551 := bstep (se 1 (by rfl) ⟨4792913, by rfl⟩ : syracuseStep 6390551 = 9585827) B9585827
theorem B3367745 : Blo 1496068 3367745 := bstep (se 2 (by rfl) ⟨1262904, by rfl⟩ : syracuseStep 3367745 = 2525809) B2525809
theorem B2245451 : Blo 1496068 2245451 := bstep (se 1 (by rfl) ⟨1684088, by rfl⟩ : syracuseStep 2245451 = 3368177) B3368177
theorem B2245463 : Blo 1496068 2245463 := bstep (se 1 (by rfl) ⟨1684097, by rfl⟩ : syracuseStep 2245463 = 3368195) B3368195
theorem B11363165 : Blo 1496068 11363165 := bstep (se 3 (by rfl) ⟨2130593, by rfl⟩ : syracuseStep 11363165 = 4261187) B4261187
theorem B5686109 : Blo 1496068 5686109 := bstep (se 3 (by rfl) ⟨1066145, by rfl⟩ : syracuseStep 5686109 = 2132291) B2132291
theorem B2245529 : Blo 1496068 2245529 := bstep (se 2 (by rfl) ⟨842073, by rfl⟩ : syracuseStep 2245529 = 1684147) B1684147
theorem B5055425 : Blo 1496068 5055425 := bstep (se 2 (by rfl) ⟨1895784, by rfl⟩ : syracuseStep 5055425 = 3791569) B3791569
theorem B2245643 : Blo 1496068 2245643 := bstep (se 1 (by rfl) ⟨1684232, by rfl⟩ : syracuseStep 2245643 = 3368465) B3368465
theorem B2245655 : Blo 1496068 2245655 := bstep (se 1 (by rfl) ⟨1684241, by rfl⟩ : syracuseStep 2245655 = 3368483) B3368483
theorem B3367961 : Blo 1496068 3367961 := bstep (se 2 (by rfl) ⟨1262985, by rfl⟩ : syracuseStep 3367961 = 2525971) B2525971
theorem B6390859 : Blo 1496068 6390859 := bstep (se 1 (by rfl) ⟨4793144, by rfl⟩ : syracuseStep 6390859 = 9586289) B9586289
theorem B2843723 : Blo 1496068 2843723 := bstep (se 1 (by rfl) ⟨2132792, by rfl⟩ : syracuseStep 2843723 = 4265585) B4265585
theorem B2245721 : Blo 1496068 2245721 := bstep (se 2 (by rfl) ⟨842145, by rfl⟩ : syracuseStep 2245721 = 1684291) B1684291
theorem B3368051 : Blo 1496068 3368051 := bstep (se 1 (by rfl) ⟨2526038, by rfl⟩ : syracuseStep 3368051 = 5052077) B5052077
theorem B3368087 : Blo 1496068 3368087 := bstep (se 1 (by rfl) ⟨2526065, by rfl⟩ : syracuseStep 3368087 = 5052131) B5052131
theorem B3843251 : Blo 1496068 3843251 := bstep (se 1 (by rfl) ⟨2882438, by rfl⟩ : syracuseStep 3843251 = 5764877) B5764877
theorem B2245835 : Blo 1496068 2245835 := bstep (se 1 (by rfl) ⟨1684376, by rfl⟩ : syracuseStep 2245835 = 3368753) B3368753
theorem B2245847 : Blo 1496068 2245847 := bstep (se 1 (by rfl) ⟨1684385, by rfl⟩ : syracuseStep 2245847 = 3368771) B3368771
theorem B2843905 : Blo 1496068 2843905 := bstep (se 2 (by rfl) ⟨1066464, by rfl⟩ : syracuseStep 2843905 = 2132929) B2132929
theorem B2245913 : Blo 1496068 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B3368267 : Blo 1496068 3368267 := bstep (se 1 (by rfl) ⟨2526200, by rfl⟩ : syracuseStep 3368267 = 5052401) B5052401
theorem B1893719 : Blo 1496068 1893719 := bstep (se 1 (by rfl) ⟨1420289, by rfl⟩ : syracuseStep 1893719 = 2840579) B2840579
theorem B6391133 : Blo 1496068 6391133 := bstep (se 3 (by rfl) ⟨1198337, by rfl⟩ : syracuseStep 6391133 = 2396675) B2396675
theorem B17057141 : Blo 1496068 17057141 := bstep (se 5 (by rfl) ⟨799553, by rfl⟩ : syracuseStep 17057141 = 1599107) B1599107
theorem B3368321 : Blo 1496068 3368321 := bstep (se 2 (by rfl) ⟨1263120, by rfl⟩ : syracuseStep 3368321 = 2526241) B2526241
theorem B2246027 : Blo 1496068 2246027 := bstep (se 1 (by rfl) ⟨1684520, by rfl⟩ : syracuseStep 2246027 = 3369041) B3369041
theorem B2246039 : Blo 1496068 2246039 := bstep (se 1 (by rfl) ⟨1684529, by rfl⟩ : syracuseStep 2246039 = 3369059) B3369059
theorem B2246105 : Blo 1496068 2246105 := bstep (se 2 (by rfl) ⟨842289, by rfl⟩ : syracuseStep 2246105 = 1684579) B1684579
theorem B5055965 : Blo 1496068 5055965 := bstep (se 3 (by rfl) ⟨947993, by rfl⟩ : syracuseStep 5055965 = 1895987) B1895987
theorem B5686807 : Blo 1496068 5686807 := bstep (se 1 (by rfl) ⟨4265105, by rfl⟩ : syracuseStep 5686807 = 8530211) B8530211
theorem B2246219 : Blo 1496068 2246219 := bstep (se 1 (by rfl) ⟨1684664, by rfl⟩ : syracuseStep 2246219 = 3369329) B3369329
theorem B2246231 : Blo 1496068 2246231 := bstep (se 1 (by rfl) ⟨1684673, by rfl⟩ : syracuseStep 2246231 = 3369347) B3369347
theorem B3368537 : Blo 1496068 3368537 := bstep (se 2 (by rfl) ⟨1263201, by rfl⟩ : syracuseStep 3368537 = 2526403) B2526403
theorem B2246297 : Blo 1496068 2246297 := bstep (se 2 (by rfl) ⟨842361, by rfl⟩ : syracuseStep 2246297 = 1684723) B1684723
theorem B3368627 : Blo 1496068 3368627 := bstep (se 1 (by rfl) ⟨2526470, by rfl⟩ : syracuseStep 3368627 = 5052941) B5052941
theorem B3368663 : Blo 1496068 3368663 := bstep (se 1 (by rfl) ⟨2526497, by rfl⟩ : syracuseStep 3368663 = 5052995) B5052995
theorem B36439793 : Blo 1496068 36439793 := bstep (se 2 (by rfl) ⟨13664922, by rfl⟩ : syracuseStep 36439793 = 27329845) B27329845
theorem B2246411 : Blo 1496068 2246411 := bstep (se 1 (by rfl) ⟨1684808, by rfl⟩ : syracuseStep 2246411 = 3369617) B3369617
theorem B2246423 : Blo 1496068 2246423 := bstep (se 1 (by rfl) ⟨1684817, by rfl⟩ : syracuseStep 2246423 = 3369635) B3369635
theorem B2246489 : Blo 1496068 2246489 := bstep (se 2 (by rfl) ⟨842433, by rfl⟩ : syracuseStep 2246489 = 1684867) B1684867
theorem B3368843 : Blo 1496068 3368843 := bstep (se 1 (by rfl) ⟨2526632, by rfl⟩ : syracuseStep 3368843 = 5053265) B5053265
theorem B19179443 : Blo 1496068 19179443 := bstep (se 1 (by rfl) ⟨14384582, by rfl⟩ : syracuseStep 19179443 = 28769165) B28769165
theorem B24291251 : Blo 1496068 24291251 := bstep (se 1 (by rfl) ⟨18218438, by rfl⟩ : syracuseStep 24291251 = 36436877) B36436877
theorem B4261825 : Blo 1496068 4261825 := bstep (se 2 (by rfl) ⟨1598184, by rfl⟩ : syracuseStep 4261825 = 3196369) B3196369
theorem B3368897 : Blo 1496068 3368897 := bstep (se 2 (by rfl) ⟨1263336, by rfl⟩ : syracuseStep 3368897 = 2526673) B2526673
theorem B2131915 : Blo 1496068 2131915 := bstep (se 1 (by rfl) ⟨1598936, by rfl⟩ : syracuseStep 2131915 = 3197873) B3197873
theorem B2246603 : Blo 1496068 2246603 := bstep (se 1 (by rfl) ⟨1684952, by rfl⟩ : syracuseStep 2246603 = 3369905) B3369905
theorem B2246615 : Blo 1496068 2246615 := bstep (se 1 (by rfl) ⟨1684961, by rfl⟩ : syracuseStep 2246615 = 3369923) B3369923
theorem B2525195 : Blo 1496068 2525195 := bstep (se 1 (by rfl) ⟨1893896, by rfl⟩ : syracuseStep 2525195 = 3787793) B3787793
theorem B1894423 : Blo 1496068 1894423 := bstep (se 1 (by rfl) ⟨1420817, by rfl⟩ : syracuseStep 1894423 = 2841635) B2841635
theorem B2246681 : Blo 1496068 2246681 := bstep (se 2 (by rfl) ⟨842505, by rfl⟩ : syracuseStep 2246681 = 1685011) B1685011
theorem B14395427 : Blo 1496068 14395427 := bstep (se 1 (by rfl) ⟨10796570, by rfl⟩ : syracuseStep 14395427 = 21593141) B21593141
theorem B3033139 : Blo 1496068 3033139 := bstep (se 1 (by rfl) ⟨2274854, by rfl⟩ : syracuseStep 3033139 = 4549709) B4549709
theorem B2525323 : Blo 1496068 2525323 := bstep (se 1 (by rfl) ⟨1893992, by rfl⟩ : syracuseStep 2525323 = 3787985) B3787985
theorem B2246795 : Blo 1496068 2246795 := bstep (se 1 (by rfl) ⟨1685096, by rfl⟩ : syracuseStep 2246795 = 3370193) B3370193
theorem B2246807 : Blo 1496068 2246807 := bstep (se 1 (by rfl) ⟨1685105, by rfl⟩ : syracuseStep 2246807 = 3370211) B3370211
theorem B3369113 : Blo 1496068 3369113 := bstep (se 2 (by rfl) ⟨1263417, by rfl⟩ : syracuseStep 3369113 = 2526835) B2526835
theorem B2132183 : Blo 1496068 2132183 := bstep (se 1 (by rfl) ⟨1599137, by rfl⟩ : syracuseStep 2132183 = 3198275) B3198275
theorem B2246873 : Blo 1496068 2246873 := bstep (se 2 (by rfl) ⟨842577, by rfl⟩ : syracuseStep 2246873 = 1685155) B1685155
theorem B3369203 : Blo 1496068 3369203 := bstep (se 1 (by rfl) ⟨2526902, by rfl⟩ : syracuseStep 3369203 = 5053805) B5053805
theorem B3197207 : Blo 1496068 3197207 := bstep (se 1 (by rfl) ⟨2397905, by rfl⟩ : syracuseStep 3197207 = 4795811) B4795811
theorem B3369239 : Blo 1496068 3369239 := bstep (se 1 (by rfl) ⟨2526929, by rfl⟩ : syracuseStep 3369239 = 5053859) B5053859
theorem B2525465 : Blo 1496068 2525465 := bstep (se 2 (by rfl) ⟨947049, by rfl⟩ : syracuseStep 2525465 = 1894099) B1894099
theorem B14035235 : Blo 1496068 14035235 := bstep (se 1 (by rfl) ⟨10526426, by rfl⟩ : syracuseStep 14035235 = 21052853) B21052853
theorem B5687597 : Blo 1496068 5687597 := bstep (se 3 (by rfl) ⟨1066424, by rfl⟩ : syracuseStep 5687597 = 2132849) B2132849
theorem B1517879 : Blo 1496068 1517879 := bstep (se 1 (by rfl) ⟨1138409, by rfl⟩ : syracuseStep 1517879 = 2276819) B2276819
theorem B7579979 : Blo 1496068 7579979 := bstep (se 1 (by rfl) ⟨5684984, by rfl⟩ : syracuseStep 7579979 = 11369969) B11369969
theorem B2246987 : Blo 1496068 2246987 := bstep (se 1 (by rfl) ⟨1685240, by rfl⟩ : syracuseStep 2246987 = 3370481) B3370481
theorem B2246999 : Blo 1496068 2246999 := bstep (se 1 (by rfl) ⟨1685249, by rfl⟩ : syracuseStep 2246999 = 3370499) B3370499
theorem B2525593 : Blo 1496068 2525593 := bstep (se 2 (by rfl) ⟨947097, by rfl⟩ : syracuseStep 2525593 = 1894195) B1894195
theorem B2247065 : Blo 1496068 2247065 := bstep (se 2 (by rfl) ⟨842649, by rfl⟩ : syracuseStep 2247065 = 1685299) B1685299
theorem B3197387 : Blo 1496068 3197387 := bstep (se 1 (by rfl) ⟨2398040, by rfl⟩ : syracuseStep 3197387 = 4796081) B4796081
theorem B3369419 : Blo 1496068 3369419 := bstep (se 1 (by rfl) ⟨2527064, by rfl⟩ : syracuseStep 3369419 = 5054129) B5054129
theorem B8530393 : Blo 1496068 8530393 := bstep (se 2 (by rfl) ⟨3198897, by rfl⟩ : syracuseStep 8530393 = 6397795) B6397795
theorem B3369473 : Blo 1496068 3369473 := bstep (se 2 (by rfl) ⟨1263552, by rfl⟩ : syracuseStep 3369473 = 2527105) B2527105
theorem B16181795 : Blo 1496068 16181795 := bstep (se 1 (by rfl) ⟨12136346, by rfl⟩ : syracuseStep 16181795 = 24272693) B24272693
theorem B6392465 : Blo 1496068 6392465 := bstep (se 2 (by rfl) ⟨2397174, by rfl⟩ : syracuseStep 6392465 = 4794349) B4794349
theorem B8096435 : Blo 1496068 8096435 := bstep (se 1 (by rfl) ⟨6072326, by rfl⟩ : syracuseStep 8096435 = 12144653) B12144653
theorem B3369689 : Blo 1496068 3369689 := bstep (se 2 (by rfl) ⟨1263633, by rfl⟩ : syracuseStep 3369689 = 2527267) B2527267
theorem B43158257 : Blo 1496068 43158257 := bstep (se 2 (by rfl) ⟨16184346, by rfl⟩ : syracuseStep 43158257 = 32368693) B32368693
theorem B3369779 : Blo 1496068 3369779 := bstep (se 1 (by rfl) ⟨2527334, by rfl⟩ : syracuseStep 3369779 = 5054669) B5054669
theorem B3369815 : Blo 1496068 3369815 := bstep (se 1 (by rfl) ⟨2527361, by rfl⟩ : syracuseStep 3369815 = 5054723) B5054723
theorem B5393297 : Blo 1496068 5393297 := bstep (se 2 (by rfl) ⟨2022486, by rfl⟩ : syracuseStep 5393297 = 4044973) B4044973
theorem B1919947 : Blo 1496068 1919947 := bstep (se 1 (by rfl) ⟨1439960, by rfl⟩ : syracuseStep 1919947 = 2879921) B2879921
theorem B2526167 : Blo 1496068 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B3369995 : Blo 1496068 3369995 := bstep (se 1 (by rfl) ⟨2527496, by rfl⟩ : syracuseStep 3369995 = 5054993) B5054993
theorem B48540707 : Blo 1496068 48540707 := bstep (se 1 (by rfl) ⟨36405530, by rfl⟩ : syracuseStep 48540707 = 72811061) B72811061
theorem B3370049 : Blo 1496068 3370049 := bstep (se 2 (by rfl) ⟨1263768, by rfl⟩ : syracuseStep 3370049 = 2527537) B2527537
theorem B43142219 : Blo 1496068 43142219 := bstep (se 1 (by rfl) ⟨32356664, by rfl⟩ : syracuseStep 43142219 = 64713329) B64713329
theorem B2526295 : Blo 1496068 2526295 := bstep (se 1 (by rfl) ⟨1894721, by rfl⟩ : syracuseStep 2526295 = 3789443) B3789443
theorem B3034201 : Blo 1496068 3034201 := bstep (se 2 (by rfl) ⟨1137825, by rfl⟩ : syracuseStep 3034201 = 2275651) B2275651
theorem B3787955 : Blo 1496068 3787955 := bstep (se 1 (by rfl) ⟨2840966, by rfl⟩ : syracuseStep 3787955 = 5681933) B5681933
theorem B5393587 : Blo 1496068 5393587 := bstep (se 1 (by rfl) ⟨4045190, by rfl⟩ : syracuseStep 5393587 = 8090381) B8090381
theorem B5123251 : Blo 1496068 5123251 := bstep (se 1 (by rfl) ⟨3842438, by rfl⟩ : syracuseStep 5123251 = 7684877) B7684877
theorem B9587929 : Blo 1496068 9587929 := bstep (se 2 (by rfl) ⟨3595473, by rfl⟩ : syracuseStep 9587929 = 7190947) B7190947
theorem B2772235 : Blo 1496068 2772235 := bstep (se 1 (by rfl) ⟨2079176, by rfl⟩ : syracuseStep 2772235 = 4158353) B4158353
theorem B3370265 : Blo 1496068 3370265 := bstep (se 2 (by rfl) ⟨1263849, by rfl⟩ : syracuseStep 3370265 = 2527699) B2527699
theorem B3239219 : Blo 1496068 3239219 := bstep (se 1 (by rfl) ⟨2429414, by rfl⟩ : syracuseStep 3239219 = 4858829) B4858829
theorem B3370355 : Blo 1496068 3370355 := bstep (se 1 (by rfl) ⟨2527766, by rfl⟩ : syracuseStep 3370355 = 5055533) B5055533
theorem B3370391 : Blo 1496068 3370391 := bstep (se 1 (by rfl) ⟨2527793, by rfl⟩ : syracuseStep 3370391 = 5055587) B5055587
theorem B8531351 : Blo 1496068 8531351 := bstep (se 1 (by rfl) ⟨6398513, by rfl⟩ : syracuseStep 8531351 = 12797027) B12797027
theorem B3370571 : Blo 1496068 3370571 := bstep (se 1 (by rfl) ⟨2527928, by rfl⟩ : syracuseStep 3370571 = 5055857) B5055857
theorem B3370625 : Blo 1496068 3370625 := bstep (se 2 (by rfl) ⟨1263984, by rfl⟩ : syracuseStep 3370625 = 2527969) B2527969
theorem B3788491 : Blo 1496068 3788491 := bstep (se 1 (by rfl) ⟨2841368, by rfl⟩ : syracuseStep 3788491 = 5682737) B5682737
theorem B2526923 : Blo 1496068 2526923 := bstep (se 1 (by rfl) ⟨1895192, by rfl⟩ : syracuseStep 2526923 = 3790385) B3790385
theorem B2698955 : Blo 1496068 2698955 := bstep (se 1 (by rfl) ⟨2024216, by rfl⟩ : syracuseStep 2698955 = 4048433) B4048433
theorem B10792709 : Blo 1496068 10792709 := bstep (se 4 (by rfl) ⟨1011816, by rfl⟩ : syracuseStep 10792709 = 2023633) B2023633
theorem B1683211 : Blo 1496068 1683211 := bstep (se 1 (by rfl) ⟨1262408, by rfl⟩ : syracuseStep 1683211 = 2524817) B2524817
theorem B2879243 : Blo 1496068 2879243 := bstep (se 1 (by rfl) ⟨2159432, by rfl⟩ : syracuseStep 2879243 = 4318865) B4318865
theorem B5680961 : Blo 1496068 5680961 := bstep (se 2 (by rfl) ⟨2130360, by rfl⟩ : syracuseStep 5680961 = 4260721) B4260721
theorem B5050187 : Blo 1496068 5050187 := bstep (se 1 (by rfl) ⟨3787640, by rfl⟩ : syracuseStep 5050187 = 7575281) B7575281
theorem B12791627 : Blo 1496068 12791627 := bstep (se 1 (by rfl) ⟨9593720, by rfl⟩ : syracuseStep 12791627 = 19187441) B19187441
theorem B2527051 : Blo 1496068 2527051 := bstep (se 1 (by rfl) ⟨1895288, by rfl⟩ : syracuseStep 2527051 = 3790577) B3790577
theorem B3788633 : Blo 1496068 3788633 := bstep (se 2 (by rfl) ⟨1420737, by rfl⟩ : syracuseStep 3788633 = 2841475) B2841475
theorem B1683319 : Blo 1496068 1683319 := bstep (se 1 (by rfl) ⟨1262489, by rfl⟩ : syracuseStep 1683319 = 2524979) B2524979
theorem B2879383 : Blo 1496068 2879383 := bstep (se 1 (by rfl) ⟨2159537, by rfl⟩ : syracuseStep 2879383 = 4319075) B4319075
theorem B2527193 : Blo 1496068 2527193 := bstep (se 2 (by rfl) ⟨947697, by rfl⟩ : syracuseStep 2527193 = 1895395) B1895395
theorem B1683499 : Blo 1496068 1683499 := bstep (se 1 (by rfl) ⟨1262624, by rfl⟩ : syracuseStep 1683499 = 2525249) B2525249
theorem B8089645 : Blo 1496068 8089645 := bstep (se 3 (by rfl) ⟨1516808, by rfl⟩ : syracuseStep 8089645 = 3033617) B3033617
theorem B3199027 : Blo 1496068 3199027 := bstep (se 1 (by rfl) ⟨2399270, by rfl⟩ : syracuseStep 3199027 = 4798541) B4798541
theorem B9105473 : Blo 1496068 9105473 := bstep (se 2 (by rfl) ⟨3414552, by rfl⟩ : syracuseStep 9105473 = 6829105) B6829105
theorem B7581761 : Blo 1496068 7581761 := bstep (se 2 (by rfl) ⟨2843160, by rfl⟩ : syracuseStep 7581761 = 5686321) B5686321
theorem B5050457 : Blo 1496068 5050457 := bstep (se 2 (by rfl) ⟨1893921, by rfl⟩ : syracuseStep 5050457 = 3787843) B3787843
theorem B2527321 : Blo 1496068 2527321 := bstep (se 2 (by rfl) ⟨947745, by rfl⟩ : syracuseStep 2527321 = 1895491) B1895491
theorem B1683607 : Blo 1496068 1683607 := bstep (se 1 (by rfl) ⟨1262705, by rfl⟩ : syracuseStep 1683607 = 2525411) B2525411
theorem B29151413 : Blo 1496068 29151413 := bstep (se 5 (by rfl) ⟨1366472, by rfl⟩ : syracuseStep 29151413 = 2732945) B2732945
theorem B1683787 : Blo 1496068 1683787 := bstep (se 1 (by rfl) ⟨1262840, by rfl⟩ : syracuseStep 1683787 = 2525681) B2525681
theorem B24285541 : Blo 1496068 24285541 := bstep (se 4 (by rfl) ⟨2276769, by rfl⟩ : syracuseStep 24285541 = 4553539) B4553539
theorem B34550165 : Blo 1496068 34550165 := bstep (se 6 (by rfl) ⟨809769, by rfl⟩ : syracuseStep 34550165 = 1619539) B1619539
theorem B1683895 : Blo 1496068 1683895 := bstep (se 1 (by rfl) ⟨1262921, by rfl⟩ : syracuseStep 1683895 = 2525843) B2525843
theorem B1684075 : Blo 1496068 1684075 := bstep (se 1 (by rfl) ⟨1263056, by rfl⟩ : syracuseStep 1684075 = 2526113) B2526113
theorem B7574147 : Blo 1496068 7574147 := bstep (se 1 (by rfl) ⟨5680610, by rfl⟩ : syracuseStep 7574147 = 11361221) B11361221
theorem B3789463 : Blo 1496068 3789463 := bstep (se 1 (by rfl) ⟨2842097, by rfl⟩ : syracuseStep 3789463 = 5684195) B5684195
theorem B2527895 : Blo 1496068 2527895 := bstep (se 1 (by rfl) ⟨1895921, by rfl⟩ : syracuseStep 2527895 = 3791843) B3791843
theorem B1684183 : Blo 1496068 1684183 := bstep (se 1 (by rfl) ⟨1263137, by rfl⟩ : syracuseStep 1684183 = 2526275) B2526275
theorem B8524561 : Blo 1496068 8524561 := bstep (se 2 (by rfl) ⟨3196710, by rfl⟩ : syracuseStep 8524561 = 6393421) B6393421
theorem B5051159 : Blo 1496068 5051159 := bstep (se 1 (by rfl) ⟨3788369, by rfl⟩ : syracuseStep 5051159 = 7576739) B7576739
theorem B1684363 : Blo 1496068 1684363 := bstep (se 1 (by rfl) ⟨1263272, by rfl⟩ : syracuseStep 1684363 = 2526545) B2526545
theorem B5395373 : Blo 1496068 5395373 := bstep (se 3 (by rfl) ⟨1011632, by rfl⟩ : syracuseStep 5395373 = 2023265) B2023265
theorem B1684471 : Blo 1496068 1684471 := bstep (se 1 (by rfl) ⟨1263353, by rfl⟩ : syracuseStep 1684471 = 2526707) B2526707
theorem B1496075 : Blo 1496068 1496075 := bstep (se 1 (by rfl) ⟨1122056, by rfl⟩ : syracuseStep 1496075 = 2244113) B2244113
theorem B1496087 : Blo 1496068 1496087 := bstep (se 1 (by rfl) ⟨1122065, by rfl⟩ : syracuseStep 1496087 = 2244131) B2244131
theorem B1496107 : Blo 1496068 1496107 := bstep (se 1 (by rfl) ⟨1122080, by rfl⟩ : syracuseStep 1496107 = 2244161) B2244161
theorem B5682221 : Blo 1496068 5682221 := bstep (se 3 (by rfl) ⟨1065416, by rfl⟩ : syracuseStep 5682221 = 2130833) B2130833
theorem B6394925 : Blo 1496068 6394925 := bstep (se 3 (by rfl) ⟨1199048, by rfl⟩ : syracuseStep 6394925 = 2398097) B2398097
theorem B1496119 : Blo 1496068 1496119 := bstep (se 1 (by rfl) ⟨1122089, by rfl⟩ : syracuseStep 1496119 = 2244179) B2244179
theorem B1496139 : Blo 1496068 1496139 := bstep (se 1 (by rfl) ⟨1122104, by rfl⟩ : syracuseStep 1496139 = 2244209) B2244209
theorem B5682251 : Blo 1496068 5682251 := bstep (se 1 (by rfl) ⟨4261688, by rfl⟩ : syracuseStep 5682251 = 8523377) B8523377
theorem B3789899 : Blo 1496068 3789899 := bstep (se 1 (by rfl) ⟨2842424, by rfl⟩ : syracuseStep 3789899 = 5684849) B5684849
theorem B1496151 : Blo 1496068 1496151 := bstep (se 1 (by rfl) ⟨1122113, by rfl⟩ : syracuseStep 1496151 = 2244227) B2244227
theorem B2397271 : Blo 1496068 2397271 := bstep (se 1 (by rfl) ⟨1797953, by rfl⟩ : syracuseStep 2397271 = 3595907) B3595907
theorem B1496171 : Blo 1496068 1496171 := bstep (se 1 (by rfl) ⟨1122128, by rfl⟩ : syracuseStep 1496171 = 2244257) B2244257
theorem B1496183 : Blo 1496068 1496183 := bstep (se 1 (by rfl) ⟨1122137, by rfl⟩ : syracuseStep 1496183 = 2244275) B2244275
theorem B7197827 : Blo 1496068 7197827 := bstep (se 1 (by rfl) ⟨5398370, by rfl⟩ : syracuseStep 7197827 = 10796741) B10796741
theorem B1496203 : Blo 1496068 1496203 := bstep (se 1 (by rfl) ⟨1122152, by rfl⟩ : syracuseStep 1496203 = 2244305) B2244305
theorem B1496215 : Blo 1496068 1496215 := bstep (se 1 (by rfl) ⟨1122161, by rfl⟩ : syracuseStep 1496215 = 2244323) B2244323
theorem B1496235 : Blo 1496068 1496235 := bstep (se 1 (by rfl) ⟨1122176, by rfl⟩ : syracuseStep 1496235 = 2244353) B2244353
theorem B1684651 : Blo 1496068 1684651 := bstep (se 1 (by rfl) ⟨1263488, by rfl⟩ : syracuseStep 1684651 = 2526977) B2526977
theorem B1496247 : Blo 1496068 1496247 := bstep (se 1 (by rfl) ⟨1122185, by rfl⟩ : syracuseStep 1496247 = 2244371) B2244371
theorem B1496267 : Blo 1496068 1496267 := bstep (se 1 (by rfl) ⟨1122200, by rfl⟩ : syracuseStep 1496267 = 2244401) B2244401
theorem B2733259 : Blo 1496068 2733259 := bstep (se 1 (by rfl) ⟨2049944, by rfl⟩ : syracuseStep 2733259 = 4099889) B4099889
theorem B1496279 : Blo 1496068 1496279 := bstep (se 1 (by rfl) ⟨1122209, by rfl⟩ : syracuseStep 1496279 = 2244419) B2244419
theorem B1496299 : Blo 1496068 1496299 := bstep (se 1 (by rfl) ⟨1122224, by rfl⟩ : syracuseStep 1496299 = 2244449) B2244449
theorem B1496311 : Blo 1496068 1496311 := bstep (se 1 (by rfl) ⟨1122233, by rfl⟩ : syracuseStep 1496311 = 2244467) B2244467
theorem B18216197 : Blo 1496068 18216197 := bstep (se 4 (by rfl) ⟨1707768, by rfl⟩ : syracuseStep 18216197 = 3415537) B3415537
theorem B1496331 : Blo 1496068 1496331 := bstep (se 1 (by rfl) ⟨1122248, by rfl⟩ : syracuseStep 1496331 = 2244497) B2244497
theorem B10941713 : Blo 1496068 10941713 := bstep (se 2 (by rfl) ⟨4103142, by rfl⟩ : syracuseStep 10941713 = 8206285) B8206285
theorem B1496343 : Blo 1496068 1496343 := bstep (se 1 (by rfl) ⟨1122257, by rfl⟩ : syracuseStep 1496343 = 2244515) B2244515
theorem B1684759 : Blo 1496068 1684759 := bstep (se 1 (by rfl) ⟨1263569, by rfl⟩ : syracuseStep 1684759 = 2527139) B2527139
theorem B1496363 : Blo 1496068 1496363 := bstep (se 1 (by rfl) ⟨1122272, by rfl⟩ : syracuseStep 1496363 = 2244545) B2244545
theorem B5051699 : Blo 1496068 5051699 := bstep (se 1 (by rfl) ⟨3788774, by rfl⟩ : syracuseStep 5051699 = 7577549) B7577549
theorem B1496375 : Blo 1496068 1496375 := bstep (se 1 (by rfl) ⟨1122281, by rfl⟩ : syracuseStep 1496375 = 2244563) B2244563
theorem B1496395 : Blo 1496068 1496395 := bstep (se 1 (by rfl) ⟨1122296, by rfl⟩ : syracuseStep 1496395 = 2244593) B2244593
theorem B1496407 : Blo 1496068 1496407 := bstep (se 1 (by rfl) ⟨1122305, by rfl⟩ : syracuseStep 1496407 = 2244611) B2244611
theorem B1496427 : Blo 1496068 1496427 := bstep (se 1 (by rfl) ⟨1122320, by rfl⟩ : syracuseStep 1496427 = 2244641) B2244641
theorem B1496439 : Blo 1496068 1496439 := bstep (se 1 (by rfl) ⟨1122329, by rfl⟩ : syracuseStep 1496439 = 2244659) B2244659
theorem B6395267 : Blo 1496068 6395267 := bstep (se 1 (by rfl) ⟨4796450, by rfl⟩ : syracuseStep 6395267 = 9592901) B9592901
theorem B1496459 : Blo 1496068 1496459 := bstep (se 1 (by rfl) ⟨1122344, by rfl⟩ : syracuseStep 1496459 = 2244689) B2244689
theorem B1496471 : Blo 1496068 1496471 := bstep (se 1 (by rfl) ⟨1122353, by rfl⟩ : syracuseStep 1496471 = 2244707) B2244707
theorem B1496491 : Blo 1496068 1496491 := bstep (se 1 (by rfl) ⟨1122368, by rfl⟩ : syracuseStep 1496491 = 2244737) B2244737
theorem B1496503 : Blo 1496068 1496503 := bstep (se 1 (by rfl) ⟨1122377, by rfl⟩ : syracuseStep 1496503 = 2244755) B2244755
theorem B3790273 : Blo 1496068 3790273 := bstep (se 2 (by rfl) ⟨1421352, by rfl⟩ : syracuseStep 3790273 = 2842705) B2842705
theorem B1496523 : Blo 1496068 1496523 := bstep (se 1 (by rfl) ⟨1122392, by rfl⟩ : syracuseStep 1496523 = 2244785) B2244785
theorem B1684939 : Blo 1496068 1684939 := bstep (se 1 (by rfl) ⟨1263704, by rfl⟩ : syracuseStep 1684939 = 2527409) B2527409
theorem B1496535 : Blo 1496068 1496535 := bstep (se 1 (by rfl) ⟨1122401, by rfl⟩ : syracuseStep 1496535 = 2244803) B2244803
theorem B1496555 : Blo 1496068 1496555 := bstep (se 1 (by rfl) ⟨1122416, by rfl⟩ : syracuseStep 1496555 = 2244833) B2244833
theorem B1496567 : Blo 1496068 1496567 := bstep (se 1 (by rfl) ⟨1122425, by rfl⟩ : syracuseStep 1496567 = 2244851) B2244851
theorem B1496587 : Blo 1496068 1496587 := bstep (se 1 (by rfl) ⟨1122440, by rfl⟩ : syracuseStep 1496587 = 2244881) B2244881
theorem B45561361 : Blo 1496068 45561361 := bstep (se 2 (by rfl) ⟨17085510, by rfl⟩ : syracuseStep 45561361 = 34171021) B34171021
theorem B1496599 : Blo 1496068 1496599 := bstep (se 1 (by rfl) ⟨1122449, by rfl⟩ : syracuseStep 1496599 = 2244899) B2244899
theorem B1496619 : Blo 1496068 1496619 := bstep (se 1 (by rfl) ⟨1122464, by rfl⟩ : syracuseStep 1496619 = 2244929) B2244929
theorem B1496631 : Blo 1496068 1496631 := bstep (se 1 (by rfl) ⟨1122473, by rfl⟩ : syracuseStep 1496631 = 2244947) B2244947
theorem B1685047 : Blo 1496068 1685047 := bstep (se 1 (by rfl) ⟨1263785, by rfl⟩ : syracuseStep 1685047 = 2527571) B2527571
theorem B5051969 : Blo 1496068 5051969 := bstep (se 2 (by rfl) ⟨1894488, by rfl⟩ : syracuseStep 5051969 = 3788977) B3788977
theorem B1496651 : Blo 1496068 1496651 := bstep (se 1 (by rfl) ⟨1122488, by rfl⟩ : syracuseStep 1496651 = 2244977) B2244977
theorem B1496663 : Blo 1496068 1496663 := bstep (se 1 (by rfl) ⟨1122497, by rfl⟩ : syracuseStep 1496663 = 2244995) B2244995
theorem B1947223 : Blo 1496068 1947223 := bstep (se 1 (by rfl) ⟨1460417, by rfl⟩ : syracuseStep 1947223 = 2920835) B2920835
theorem B4265561 : Blo 1496068 4265561 := bstep (se 2 (by rfl) ⟨1599585, by rfl⟩ : syracuseStep 4265561 = 3199171) B3199171
theorem B1496683 : Blo 1496068 1496683 := bstep (se 1 (by rfl) ⟨1122512, by rfl⟩ : syracuseStep 1496683 = 2245025) B2245025
theorem B1496695 : Blo 1496068 1496695 := bstep (se 1 (by rfl) ⟨1122521, by rfl⟩ : syracuseStep 1496695 = 2245043) B2245043
theorem B1496715 : Blo 1496068 1496715 := bstep (se 1 (by rfl) ⟨1122536, by rfl⟩ : syracuseStep 1496715 = 2245073) B2245073
theorem B1496727 : Blo 1496068 1496727 := bstep (se 1 (by rfl) ⟨1122545, by rfl⟩ : syracuseStep 1496727 = 2245091) B2245091
theorem B1496747 : Blo 1496068 1496747 := bstep (se 1 (by rfl) ⟨1122560, by rfl⟩ : syracuseStep 1496747 = 2245121) B2245121
theorem B1496759 : Blo 1496068 1496759 := bstep (se 1 (by rfl) ⟨1122569, by rfl⟩ : syracuseStep 1496759 = 2245139) B2245139
theorem B1496779 : Blo 1496068 1496779 := bstep (se 1 (by rfl) ⟨1122584, by rfl⟩ : syracuseStep 1496779 = 2245169) B2245169
theorem B1496791 : Blo 1496068 1496791 := bstep (se 1 (by rfl) ⟨1122593, by rfl⟩ : syracuseStep 1496791 = 2245187) B2245187
theorem B5682905 : Blo 1496068 5682905 := bstep (se 2 (by rfl) ⟨2131089, by rfl⟩ : syracuseStep 5682905 = 4262179) B4262179
theorem B1496811 : Blo 1496068 1496811 := bstep (se 1 (by rfl) ⟨1122608, by rfl⟩ : syracuseStep 1496811 = 2245217) B2245217
theorem B1685227 : Blo 1496068 1685227 := bstep (se 1 (by rfl) ⟨1263920, by rfl⟩ : syracuseStep 1685227 = 2527841) B2527841
theorem B1496823 : Blo 1496068 1496823 := bstep (se 1 (by rfl) ⟨1122617, by rfl⟩ : syracuseStep 1496823 = 2245235) B2245235
theorem B2840321 : Blo 1496068 2840321 := bstep (se 2 (by rfl) ⟨1065120, by rfl⟩ : syracuseStep 2840321 = 2130241) B2130241
theorem B1496843 : Blo 1496068 1496843 := bstep (se 1 (by rfl) ⟨1122632, by rfl⟩ : syracuseStep 1496843 = 2245265) B2245265
theorem B1496855 : Blo 1496068 1496855 := bstep (se 1 (by rfl) ⟨1122641, by rfl⟩ : syracuseStep 1496855 = 2245283) B2245283
theorem B1496875 : Blo 1496068 1496875 := bstep (se 1 (by rfl) ⟨1122656, by rfl⟩ : syracuseStep 1496875 = 2245313) B2245313
theorem B1496887 : Blo 1496068 1496887 := bstep (se 1 (by rfl) ⟨1122665, by rfl⟩ : syracuseStep 1496887 = 2245331) B2245331
theorem B1496907 : Blo 1496068 1496907 := bstep (se 1 (by rfl) ⟨1122680, by rfl⟩ : syracuseStep 1496907 = 2245361) B2245361
theorem B1496919 : Blo 1496068 1496919 := bstep (se 1 (by rfl) ⟨1122689, by rfl⟩ : syracuseStep 1496919 = 2245379) B2245379
theorem B1496939 : Blo 1496068 1496939 := bstep (se 1 (by rfl) ⟨1122704, by rfl⟩ : syracuseStep 1496939 = 2245409) B2245409
theorem B1496951 : Blo 1496068 1496951 := bstep (se 1 (by rfl) ⟨1122713, by rfl⟩ : syracuseStep 1496951 = 2245427) B2245427
theorem B1496971 : Blo 1496068 1496971 := bstep (se 1 (by rfl) ⟨1122728, by rfl⟩ : syracuseStep 1496971 = 2245457) B2245457
theorem B2398091 : Blo 1496068 2398091 := bstep (se 1 (by rfl) ⟨1798568, by rfl⟩ : syracuseStep 2398091 = 3597137) B3597137
theorem B1496983 : Blo 1496068 1496983 := bstep (se 1 (by rfl) ⟨1122737, by rfl⟩ : syracuseStep 1496983 = 2245475) B2245475
theorem B1497003 : Blo 1496068 1497003 := bstep (se 1 (by rfl) ⟨1122752, by rfl⟩ : syracuseStep 1497003 = 2245505) B2245505
theorem B1497015 : Blo 1496068 1497015 := bstep (se 1 (by rfl) ⟨1122761, by rfl⟩ : syracuseStep 1497015 = 2245523) B2245523
theorem B1497035 : Blo 1496068 1497035 := bstep (se 1 (by rfl) ⟨1122776, by rfl⟩ : syracuseStep 1497035 = 2245553) B2245553
theorem B1497047 : Blo 1496068 1497047 := bstep (se 1 (by rfl) ⟨1122785, by rfl⟩ : syracuseStep 1497047 = 2245571) B2245571
theorem B7583705 : Blo 1496068 7583705 := bstep (se 2 (by rfl) ⟨2843889, by rfl⟩ : syracuseStep 7583705 = 5687779) B5687779
theorem B1497067 : Blo 1496068 1497067 := bstep (se 1 (by rfl) ⟨1122800, by rfl⟩ : syracuseStep 1497067 = 2245601) B2245601
theorem B1497079 : Blo 1496068 1497079 := bstep (se 1 (by rfl) ⟨1122809, by rfl⟩ : syracuseStep 1497079 = 2245619) B2245619
theorem B1497099 : Blo 1496068 1497099 := bstep (se 1 (by rfl) ⟨1122824, by rfl⟩ : syracuseStep 1497099 = 2245649) B2245649
theorem B5683223 : Blo 1496068 5683223 := bstep (se 1 (by rfl) ⟨4262417, by rfl⟩ : syracuseStep 5683223 = 8524835) B8524835
theorem B1497111 : Blo 1496068 1497111 := bstep (se 1 (by rfl) ⟨1122833, by rfl⟩ : syracuseStep 1497111 = 2245667) B2245667
theorem B3790871 : Blo 1496068 3790871 := bstep (se 1 (by rfl) ⟨2843153, by rfl⟩ : syracuseStep 3790871 = 5686307) B5686307
theorem B1497131 : Blo 1496068 1497131 := bstep (se 1 (by rfl) ⟨1122848, by rfl⟩ : syracuseStep 1497131 = 2245697) B2245697
theorem B1497143 : Blo 1496068 1497143 := bstep (se 1 (by rfl) ⟨1122857, by rfl⟩ : syracuseStep 1497143 = 2245715) B2245715
theorem B1497163 : Blo 1496068 1497163 := bstep (se 1 (by rfl) ⟨1122872, by rfl⟩ : syracuseStep 1497163 = 2245745) B2245745
theorem B17291339 : Blo 1496068 17291339 := bstep (se 1 (by rfl) ⟨12968504, by rfl⟩ : syracuseStep 17291339 = 25937009) B25937009
theorem B2840663 : Blo 1496068 2840663 := bstep (se 1 (by rfl) ⟨2130497, by rfl⟩ : syracuseStep 2840663 = 4260995) B4260995
theorem B1497175 : Blo 1496068 1497175 := bstep (se 1 (by rfl) ⟨1122881, by rfl⟩ : syracuseStep 1497175 = 2245763) B2245763
theorem B5052509 : Blo 1496068 5052509 := bstep (se 3 (by rfl) ⟨947345, by rfl⟩ : syracuseStep 5052509 = 1894691) B1894691
theorem B1497195 : Blo 1496068 1497195 := bstep (se 1 (by rfl) ⟨1122896, by rfl⟩ : syracuseStep 1497195 = 2245793) B2245793
theorem B1497207 : Blo 1496068 1497207 := bstep (se 1 (by rfl) ⟨1122905, by rfl⟩ : syracuseStep 1497207 = 2245811) B2245811
theorem B1497227 : Blo 1496068 1497227 := bstep (se 1 (by rfl) ⟨1122920, by rfl⟩ : syracuseStep 1497227 = 2245841) B2245841
theorem B1497239 : Blo 1496068 1497239 := bstep (se 1 (by rfl) ⟨1122929, by rfl⟩ : syracuseStep 1497239 = 2245859) B2245859
theorem B1497259 : Blo 1496068 1497259 := bstep (se 1 (by rfl) ⟨1122944, by rfl⟩ : syracuseStep 1497259 = 2245889) B2245889
theorem B1497271 : Blo 1496068 1497271 := bstep (se 1 (by rfl) ⟨1122953, by rfl⟩ : syracuseStep 1497271 = 2245907) B2245907
theorem B1497291 : Blo 1496068 1497291 := bstep (se 1 (by rfl) ⟨1122968, by rfl⟩ : syracuseStep 1497291 = 2245937) B2245937
theorem B1497303 : Blo 1496068 1497303 := bstep (se 1 (by rfl) ⟨1122977, by rfl⟩ : syracuseStep 1497303 = 2245955) B2245955
theorem B1497323 : Blo 1496068 1497323 := bstep (se 1 (by rfl) ⟨1122992, by rfl⟩ : syracuseStep 1497323 = 2245985) B2245985
theorem B1497335 : Blo 1496068 1497335 := bstep (se 1 (by rfl) ⟨1123001, by rfl⟩ : syracuseStep 1497335 = 2246003) B2246003
theorem B1497355 : Blo 1496068 1497355 := bstep (se 1 (by rfl) ⟨1123016, by rfl⟩ : syracuseStep 1497355 = 2246033) B2246033
theorem B1497367 : Blo 1496068 1497367 := bstep (se 1 (by rfl) ⟨1123025, by rfl⟩ : syracuseStep 1497367 = 2246051) B2246051
theorem B1497387 : Blo 1496068 1497387 := bstep (se 1 (by rfl) ⟨1123040, by rfl⟩ : syracuseStep 1497387 = 2246081) B2246081
theorem B1497399 : Blo 1496068 1497399 := bstep (se 1 (by rfl) ⟨1123049, by rfl⟩ : syracuseStep 1497399 = 2246099) B2246099
theorem B1497419 : Blo 1496068 1497419 := bstep (se 1 (by rfl) ⟨1123064, by rfl⟩ : syracuseStep 1497419 = 2246129) B2246129
theorem B1497431 : Blo 1496068 1497431 := bstep (se 1 (by rfl) ⟨1123073, by rfl⟩ : syracuseStep 1497431 = 2246147) B2246147
theorem B4045145 : Blo 1496068 4045145 := bstep (se 2 (by rfl) ⟨1516929, by rfl⟩ : syracuseStep 4045145 = 3033859) B3033859
theorem B1497451 : Blo 1496068 1497451 := bstep (se 1 (by rfl) ⟨1123088, by rfl⟩ : syracuseStep 1497451 = 2246177) B2246177
theorem B47356273 : Blo 1496068 47356273 := bstep (se 2 (by rfl) ⟨17758602, by rfl⟩ : syracuseStep 47356273 = 35517205) B35517205
theorem B1497463 : Blo 1496068 1497463 := bstep (se 1 (by rfl) ⟨1123097, by rfl⟩ : syracuseStep 1497463 = 2246195) B2246195
theorem B1497483 : Blo 1496068 1497483 := bstep (se 1 (by rfl) ⟨1123112, by rfl⟩ : syracuseStep 1497483 = 2246225) B2246225
theorem B1497495 : Blo 1496068 1497495 := bstep (se 1 (by rfl) ⟨1123121, by rfl⟩ : syracuseStep 1497495 = 2246243) B2246243
theorem B1497515 : Blo 1496068 1497515 := bstep (se 1 (by rfl) ⟨1123136, by rfl⟩ : syracuseStep 1497515 = 2246273) B2246273
theorem B1497527 : Blo 1496068 1497527 := bstep (se 1 (by rfl) ⟨1123145, by rfl⟩ : syracuseStep 1497527 = 2246291) B2246291
theorem B1497547 : Blo 1496068 1497547 := bstep (se 1 (by rfl) ⟨1123160, by rfl⟩ : syracuseStep 1497547 = 2246321) B2246321
theorem B1497559 : Blo 1496068 1497559 := bstep (se 1 (by rfl) ⟨1123169, by rfl⟩ : syracuseStep 1497559 = 2246339) B2246339
theorem B1497579 : Blo 1496068 1497579 := bstep (se 1 (by rfl) ⟨1123184, by rfl⟩ : syracuseStep 1497579 = 2246369) B2246369
theorem B1497591 : Blo 1496068 1497591 := bstep (se 1 (by rfl) ⟨1123193, by rfl⟩ : syracuseStep 1497591 = 2246387) B2246387
theorem B13834757 : Blo 1496068 13834757 := bstep (se 4 (by rfl) ⟨1297008, by rfl⟩ : syracuseStep 13834757 = 2594017) B2594017
theorem B1497611 : Blo 1496068 1497611 := bstep (se 1 (by rfl) ⟨1123208, by rfl⟩ : syracuseStep 1497611 = 2246417) B2246417
theorem B17054225 : Blo 1496068 17054225 := bstep (se 2 (by rfl) ⟨6395334, by rfl⟩ : syracuseStep 17054225 = 12790669) B12790669
theorem B1497623 : Blo 1496068 1497623 := bstep (se 1 (by rfl) ⟨1123217, by rfl⟩ : syracuseStep 1497623 = 2246435) B2246435
theorem B1497643 : Blo 1496068 1497643 := bstep (se 1 (by rfl) ⟨1123232, by rfl⟩ : syracuseStep 1497643 = 2246465) B2246465
theorem B1497655 : Blo 1496068 1497655 := bstep (se 1 (by rfl) ⟨1123241, by rfl⟩ : syracuseStep 1497655 = 2246483) B2246483
theorem B1497675 : Blo 1496068 1497675 := bstep (se 1 (by rfl) ⟨1123256, by rfl⟩ : syracuseStep 1497675 = 2246513) B2246513
theorem B1497687 : Blo 1496068 1497687 := bstep (se 1 (by rfl) ⟨1123265, by rfl⟩ : syracuseStep 1497687 = 2246531) B2246531
theorem B4553309 : Blo 1496068 4553309 := bstep (se 3 (by rfl) ⟨853745, by rfl⟩ : syracuseStep 4553309 = 1707491) B1707491
theorem B1497707 : Blo 1496068 1497707 := bstep (se 1 (by rfl) ⟨1123280, by rfl⟩ : syracuseStep 1497707 = 2246561) B2246561
theorem B1497719 : Blo 1496068 1497719 := bstep (se 1 (by rfl) ⟨1123289, by rfl⟩ : syracuseStep 1497719 = 2246579) B2246579
theorem B1497739 : Blo 1496068 1497739 := bstep (se 1 (by rfl) ⟨1123304, by rfl⟩ : syracuseStep 1497739 = 2246609) B2246609
theorem B1497751 : Blo 1496068 1497751 := bstep (se 1 (by rfl) ⟨1123313, by rfl⟩ : syracuseStep 1497751 = 2246627) B2246627
theorem B1497771 : Blo 1496068 1497771 := bstep (se 1 (by rfl) ⟨1123328, by rfl⟩ : syracuseStep 1497771 = 2246657) B2246657
theorem B5683891 : Blo 1496068 5683891 := bstep (se 1 (by rfl) ⟨4262918, by rfl⟩ : syracuseStep 5683891 = 8525837) B8525837
theorem B1497783 : Blo 1496068 1497783 := bstep (se 1 (by rfl) ⟨1123337, by rfl⟩ : syracuseStep 1497783 = 2246675) B2246675
theorem B1497803 : Blo 1496068 1497803 := bstep (se 1 (by rfl) ⟨1123352, by rfl⟩ : syracuseStep 1497803 = 2246705) B2246705
theorem B1497815 : Blo 1496068 1497815 := bstep (se 1 (by rfl) ⟨1123361, by rfl⟩ : syracuseStep 1497815 = 2246723) B2246723
theorem B1497835 : Blo 1496068 1497835 := bstep (se 1 (by rfl) ⟨1123376, by rfl⟩ : syracuseStep 1497835 = 2246753) B2246753
theorem B2841331 : Blo 1496068 2841331 := bstep (se 1 (by rfl) ⟨2130998, by rfl⟩ : syracuseStep 2841331 = 4261997) B4261997
theorem B2882291 : Blo 1496068 2882291 := bstep (se 1 (by rfl) ⟨2161718, by rfl⟩ : syracuseStep 2882291 = 4323437) B4323437
theorem B1497847 : Blo 1496068 1497847 := bstep (se 1 (by rfl) ⟨1123385, by rfl⟩ : syracuseStep 1497847 = 2246771) B2246771
theorem B1497867 : Blo 1496068 1497867 := bstep (se 1 (by rfl) ⟨1123400, by rfl⟩ : syracuseStep 1497867 = 2246801) B2246801
theorem B1497879 : Blo 1496068 1497879 := bstep (se 1 (by rfl) ⟨1123409, by rfl⟩ : syracuseStep 1497879 = 2246819) B2246819
theorem B1497899 : Blo 1496068 1497899 := bstep (se 1 (by rfl) ⟨1123424, by rfl⟩ : syracuseStep 1497899 = 2246849) B2246849
theorem B1497911 : Blo 1496068 1497911 := bstep (se 1 (by rfl) ⟨1123433, by rfl⟩ : syracuseStep 1497911 = 2246867) B2246867
theorem B3791681 : Blo 1496068 3791681 := bstep (se 2 (by rfl) ⟨1421880, by rfl⟩ : syracuseStep 3791681 = 2843761) B2843761
theorem B1497931 : Blo 1496068 1497931 := bstep (se 1 (by rfl) ⟨1123448, by rfl⟩ : syracuseStep 1497931 = 2246897) B2246897
theorem B1497943 : Blo 1496068 1497943 := bstep (se 1 (by rfl) ⟨1123457, by rfl⟩ : syracuseStep 1497943 = 2246915) B2246915
theorem B1497963 : Blo 1496068 1497963 := bstep (se 1 (by rfl) ⟨1123472, by rfl⟩ : syracuseStep 1497963 = 2246945) B2246945
theorem B1497975 : Blo 1496068 1497975 := bstep (se 1 (by rfl) ⟨1123481, by rfl⟩ : syracuseStep 1497975 = 2246963) B2246963
theorem B1497995 : Blo 1496068 1497995 := bstep (se 1 (by rfl) ⟨1123496, by rfl⟩ : syracuseStep 1497995 = 2246993) B2246993
theorem B1498007 : Blo 1496068 1498007 := bstep (se 1 (by rfl) ⟨1123505, by rfl⟩ : syracuseStep 1498007 = 2247011) B2247011
theorem B1498027 : Blo 1496068 1498027 := bstep (se 1 (by rfl) ⟨1123520, by rfl⟩ : syracuseStep 1498027 = 2247041) B2247041
theorem B1498039 : Blo 1496068 1498039 := bstep (se 1 (by rfl) ⟨1123529, by rfl⟩ : syracuseStep 1498039 = 2247059) B2247059
theorem B1498059 : Blo 1496068 1498059 := bstep (se 1 (by rfl) ⟨1123544, by rfl⟩ : syracuseStep 1498059 = 2247089) B2247089
theorem B2841779 : Blo 1496068 2841779 := bstep (se 1 (by rfl) ⟨2131334, by rfl⟩ : syracuseStep 2841779 = 4262669) B4262669
theorem B5053643 : Blo 1496068 5053643 := bstep (se 1 (by rfl) ⟨3790232, by rfl⟩ : syracuseStep 5053643 = 7580465) B7580465
theorem B2841817 : Blo 1496068 2841817 := bstep (se 2 (by rfl) ⟨1065681, by rfl⟩ : syracuseStep 2841817 = 2131363) B2131363
theorem B5201117 : Blo 1496068 5201117 := bstep (se 3 (by rfl) ⟨975209, by rfl⟩ : syracuseStep 5201117 = 1950419) B1950419
theorem B8641837 : Blo 1496068 8641837 := bstep (se 3 (by rfl) ⟨1620344, by rfl⟩ : syracuseStep 8641837 = 3240689) B3240689
theorem B1973579 : Blo 1496068 1973579 := bstep (se 1 (by rfl) ⟨1480184, by rfl⟩ : syracuseStep 1973579 = 2960369) B2960369
theorem B3366233 : Blo 1496068 3366233 := bstep (se 2 (by rfl) ⟨1262337, by rfl⟩ : syracuseStep 3366233 = 2524675) B2524675
theorem B5397853 : Blo 1496068 5397853 := bstep (se 3 (by rfl) ⟨1012097, by rfl⟩ : syracuseStep 5397853 = 2024195) B2024195
theorem B3366323 : Blo 1496068 3366323 := bstep (se 1 (by rfl) ⟨2524742, by rfl⟩ : syracuseStep 3366323 = 5049485) B5049485
theorem B3366359 : Blo 1496068 3366359 := bstep (se 1 (by rfl) ⟨2524769, by rfl⟩ : syracuseStep 3366359 = 5049539) B5049539
theorem B5053913 : Blo 1496068 5053913 := bstep (se 2 (by rfl) ⟨1895217, by rfl⟩ : syracuseStep 5053913 = 3790435) B3790435
theorem B2244107 : Blo 1496068 2244107 := bstep (se 1 (by rfl) ⟨1683080, by rfl⟩ : syracuseStep 2244107 = 3366161) B3366161
theorem B2244119 : Blo 1496068 2244119 := bstep (se 1 (by rfl) ⟨1683089, by rfl⟩ : syracuseStep 2244119 = 3366179) B3366179
theorem B2244185 : Blo 1496068 2244185 := bstep (se 2 (by rfl) ⟨841569, by rfl⟩ : syracuseStep 2244185 = 1683139) B1683139
theorem B3366539 : Blo 1496068 3366539 := bstep (se 1 (by rfl) ⟨2524904, by rfl⟩ : syracuseStep 3366539 = 5049809) B5049809
theorem B2842265 : Blo 1496068 2842265 := bstep (se 2 (by rfl) ⟨1065849, by rfl⟩ : syracuseStep 2842265 = 2131699) B2131699
theorem B3366593 : Blo 1496068 3366593 := bstep (se 2 (by rfl) ⟨1262472, by rfl⟩ : syracuseStep 3366593 = 2524945) B2524945
theorem B2244299 : Blo 1496068 2244299 := bstep (se 1 (by rfl) ⟨1683224, by rfl⟩ : syracuseStep 2244299 = 3366449) B3366449
theorem B6397643 : Blo 1496068 6397643 := bstep (se 1 (by rfl) ⟨4798232, by rfl⟩ : syracuseStep 6397643 = 9596465) B9596465
theorem B2244311 : Blo 1496068 2244311 := bstep (se 1 (by rfl) ⟨1683233, by rfl⟩ : syracuseStep 2244311 = 3366467) B3366467
theorem B11517713 : Blo 1496068 11517713 := bstep (se 2 (by rfl) ⟨4319142, by rfl⟩ : syracuseStep 11517713 = 8638285) B8638285
theorem B2244377 : Blo 1496068 2244377 := bstep (se 2 (by rfl) ⟨841641, by rfl⟩ : syracuseStep 2244377 = 1683283) B1683283
theorem B2277209 : Blo 1496068 2277209 := bstep (se 2 (by rfl) ⟨853953, by rfl⟩ : syracuseStep 2277209 = 1707907) B1707907
theorem B2244491 : Blo 1496068 2244491 := bstep (se 1 (by rfl) ⟨1683368, by rfl⟩ : syracuseStep 2244491 = 3366737) B3366737
theorem B5685137 : Blo 1496068 5685137 := bstep (se 2 (by rfl) ⟨2131926, by rfl⟩ : syracuseStep 5685137 = 4263853) B4263853
theorem B2244503 : Blo 1496068 2244503 := bstep (se 1 (by rfl) ⟨1683377, by rfl⟩ : syracuseStep 2244503 = 3366755) B3366755
theorem B3366809 : Blo 1496068 3366809 := bstep (se 2 (by rfl) ⟨1262553, by rfl⟩ : syracuseStep 3366809 = 2525107) B2525107
theorem B13844429 : Blo 1496068 13844429 := bstep (se 3 (by rfl) ⟨2595830, by rfl⟩ : syracuseStep 13844429 = 5191661) B5191661
theorem B2244569 : Blo 1496068 2244569 := bstep (se 2 (by rfl) ⟨841713, by rfl⟩ : syracuseStep 2244569 = 1683427) B1683427
theorem B3366899 : Blo 1496068 3366899 := bstep (se 1 (by rfl) ⟨2525174, by rfl⟩ : syracuseStep 3366899 = 5050349) B5050349
theorem B2244623 : Blo 1496068 2244623 := bstep (se 1 (by rfl) ⟨1683467, by rfl⟩ : syracuseStep 2244623 = 3366935) B3366935
theorem B6070315 : Blo 1496068 6070315 := bstep (se 1 (by rfl) ⟨4552736, by rfl⟩ : syracuseStep 6070315 = 9105473) B9105473
theorem B5054507 : Blo 1496068 5054507 := bstep (se 1 (by rfl) ⟨3790880, by rfl⟩ : syracuseStep 5054507 = 7581761) B7581761
theorem B2244665 : Blo 1496068 2244665 := bstep (se 2 (by rfl) ⟨841749, by rfl⟩ : syracuseStep 2244665 = 1683499) B1683499
theorem B3366971 : Blo 1496068 3366971 := bstep (se 1 (by rfl) ⟨2525228, by rfl⟩ : syracuseStep 3366971 = 5050457) B5050457
theorem B5685335 : Blo 1496068 5685335 := bstep (se 1 (by rfl) ⟨4264001, by rfl⟩ : syracuseStep 5685335 = 8528003) B8528003
theorem B2244743 : Blo 1496068 2244743 := bstep (se 1 (by rfl) ⟨1683557, by rfl⟩ : syracuseStep 2244743 = 3367115) B3367115
theorem B2244779 : Blo 1496068 2244779 := bstep (se 1 (by rfl) ⟨1683584, by rfl⟩ : syracuseStep 2244779 = 3367169) B3367169
theorem B3367097 : Blo 1496068 3367097 := bstep (se 2 (by rfl) ⟨1262661, by rfl⟩ : syracuseStep 3367097 = 2525323) B2525323
theorem B2244809 : Blo 1496068 2244809 := bstep (se 2 (by rfl) ⟨841803, by rfl⟩ : syracuseStep 2244809 = 1683607) B1683607
theorem B2244923 : Blo 1496068 2244923 := bstep (se 1 (by rfl) ⟨1683692, by rfl⟩ : syracuseStep 2244923 = 3367385) B3367385
theorem B19194205 : Blo 1496068 19194205 := bstep (se 3 (by rfl) ⟨3598913, by rfl⟩ : syracuseStep 19194205 = 7197827) B7197827
theorem B2244983 : Blo 1496068 2244983 := bstep (se 1 (by rfl) ⟨1683737, by rfl⟩ : syracuseStep 2244983 = 3367475) B3367475
theorem B2245007 : Blo 1496068 2245007 := bstep (se 1 (by rfl) ⟨1683755, by rfl⟩ : syracuseStep 2245007 = 3367511) B3367511
theorem B2245049 : Blo 1496068 2245049 := bstep (se 2 (by rfl) ⟨841893, by rfl⟩ : syracuseStep 2245049 = 1683787) B1683787
theorem B2245127 : Blo 1496068 2245127 := bstep (se 1 (by rfl) ⟨1683845, by rfl⟩ : syracuseStep 2245127 = 3367691) B3367691
theorem B4260367 : Blo 1496068 4260367 := bstep (se 1 (by rfl) ⟨3195275, by rfl⟩ : syracuseStep 4260367 = 6390551) B6390551
theorem B3367439 : Blo 1496068 3367439 := bstep (se 1 (by rfl) ⟨2525579, by rfl⟩ : syracuseStep 3367439 = 5051159) B5051159
theorem B3367457 : Blo 1496068 3367457 := bstep (se 2 (by rfl) ⟨1262796, by rfl⟩ : syracuseStep 3367457 = 2525593) B2525593
theorem B2245163 : Blo 1496068 2245163 := bstep (se 1 (by rfl) ⟨1683872, by rfl⟩ : syracuseStep 2245163 = 3367745) B3367745
theorem B4260413 : Blo 1496068 4260413 := bstep (se 3 (by rfl) ⟨798827, by rfl⟩ : syracuseStep 4260413 = 1597655) B1597655
theorem B5685821 : Blo 1496068 5685821 := bstep (se 3 (by rfl) ⟨1066091, by rfl⟩ : syracuseStep 5685821 = 2132183) B2132183
theorem B2245193 : Blo 1496068 2245193 := bstep (se 2 (by rfl) ⟨841947, by rfl⟩ : syracuseStep 2245193 = 1683895) B1683895
theorem B3596915 : Blo 1496068 3596915 := bstep (se 1 (by rfl) ⟨2697686, by rfl⟩ : syracuseStep 3596915 = 5395373) B5395373
theorem B2245307 : Blo 1496068 2245307 := bstep (se 1 (by rfl) ⟨1683980, by rfl⟩ : syracuseStep 2245307 = 3367961) B3367961
theorem B2245367 : Blo 1496068 2245367 := bstep (se 1 (by rfl) ⟨1684025, by rfl⟩ : syracuseStep 2245367 = 3368051) B3368051
theorem B2245391 : Blo 1496068 2245391 := bstep (se 1 (by rfl) ⟨1684043, by rfl⟩ : syracuseStep 2245391 = 3368087) B3368087
theorem B2245433 : Blo 1496068 2245433 := bstep (se 2 (by rfl) ⟨842037, by rfl⟩ : syracuseStep 2245433 = 1684075) B1684075
theorem B4047677 : Blo 1496068 4047677 := bstep (se 3 (by rfl) ⟨758939, by rfl⟩ : syracuseStep 4047677 = 1517879) B1517879
theorem B3367799 : Blo 1496068 3367799 := bstep (se 1 (by rfl) ⟨2525849, by rfl⟩ : syracuseStep 3367799 = 5051699) B5051699
theorem B2245511 : Blo 1496068 2245511 := bstep (se 1 (by rfl) ⟨1684133, by rfl⟩ : syracuseStep 2245511 = 3368267) B3368267
theorem B4260755 : Blo 1496068 4260755 := bstep (se 1 (by rfl) ⟨3195566, by rfl⟩ : syracuseStep 4260755 = 6391133) B6391133
theorem B7578521 : Blo 1496068 7578521 := bstep (se 2 (by rfl) ⟨2841945, by rfl⟩ : syracuseStep 7578521 = 5683891) B5683891
theorem B11371427 : Blo 1496068 11371427 := bstep (se 1 (by rfl) ⟨8528570, by rfl⟩ : syracuseStep 11371427 = 17057141) B17057141
theorem B2245547 : Blo 1496068 2245547 := bstep (se 1 (by rfl) ⟨1684160, by rfl⟩ : syracuseStep 2245547 = 3368321) B3368321
theorem B43148213 : Blo 1496068 43148213 := bstep (se 5 (by rfl) ⟨2022572, by rfl⟩ : syracuseStep 43148213 = 4045145) B4045145
theorem B2245577 : Blo 1496068 2245577 := bstep (se 2 (by rfl) ⟨842091, by rfl⟩ : syracuseStep 2245577 = 1684183) B1684183
theorem B3367979 : Blo 1496068 3367979 := bstep (se 1 (by rfl) ⟨2525984, by rfl⟩ : syracuseStep 3367979 = 5051969) B5051969
theorem B2245691 : Blo 1496068 2245691 := bstep (se 1 (by rfl) ⟨1684268, by rfl⟩ : syracuseStep 2245691 = 3368537) B3368537
theorem B2245751 : Blo 1496068 2245751 := bstep (se 1 (by rfl) ⟨1684313, by rfl⟩ : syracuseStep 2245751 = 3368627) B3368627
theorem B2245775 : Blo 1496068 2245775 := bstep (se 1 (by rfl) ⟨1684331, by rfl⟩ : syracuseStep 2245775 = 3368663) B3368663
theorem B1893547 : Blo 1496068 1893547 := bstep (se 1 (by rfl) ⟨1420160, by rfl⟩ : syracuseStep 1893547 = 2840321) B2840321
theorem B2245817 : Blo 1496068 2245817 := bstep (se 2 (by rfl) ⟨842181, by rfl⟩ : syracuseStep 2245817 = 1684363) B1684363
theorem B2245895 : Blo 1496068 2245895 := bstep (se 1 (by rfl) ⟨1684421, by rfl⟩ : syracuseStep 2245895 = 3368843) B3368843
theorem B2245931 : Blo 1496068 2245931 := bstep (se 1 (by rfl) ⟨1684448, by rfl⟩ : syracuseStep 2245931 = 3368897) B3368897
theorem B5055803 : Blo 1496068 5055803 := bstep (se 1 (by rfl) ⟨3791852, by rfl⟩ : syracuseStep 5055803 = 7583705) B7583705
theorem B2245961 : Blo 1496068 2245961 := bstep (se 2 (by rfl) ⟨842235, by rfl⟩ : syracuseStep 2245961 = 1684471) B1684471
theorem B11527559 : Blo 1496068 11527559 := bstep (se 1 (by rfl) ⟨8645669, by rfl⟩ : syracuseStep 11527559 = 17291339) B17291339
theorem B1893775 : Blo 1496068 1893775 := bstep (se 1 (by rfl) ⟨1420331, by rfl⟩ : syracuseStep 1893775 = 2840663) B2840663
theorem B3368339 : Blo 1496068 3368339 := bstep (se 1 (by rfl) ⟨2526254, by rfl⟩ : syracuseStep 3368339 = 5052509) B5052509
theorem B8521145 : Blo 1496068 8521145 := bstep (se 2 (by rfl) ⟨3195429, by rfl⟩ : syracuseStep 8521145 = 6390859) B6390859
theorem B2246075 : Blo 1496068 2246075 := bstep (se 1 (by rfl) ⟨1684556, by rfl⟩ : syracuseStep 2246075 = 3369113) B3369113
theorem B3196361 : Blo 1496068 3196361 := bstep (se 2 (by rfl) ⟨1198635, by rfl⟩ : syracuseStep 3196361 = 2397271) B2397271
theorem B3368393 : Blo 1496068 3368393 := bstep (se 2 (by rfl) ⟨1263147, by rfl⟩ : syracuseStep 3368393 = 2526295) B2526295
theorem B2246135 : Blo 1496068 2246135 := bstep (se 1 (by rfl) ⟨1684601, by rfl⟩ : syracuseStep 2246135 = 3369203) B3369203
theorem B2131471 : Blo 1496068 2131471 := bstep (se 1 (by rfl) ⟨1598603, by rfl⟩ : syracuseStep 2131471 = 3197207) B3197207
theorem B2246159 : Blo 1496068 2246159 := bstep (se 1 (by rfl) ⟨1684619, by rfl⟩ : syracuseStep 2246159 = 3369239) B3369239
theorem B2246201 : Blo 1496068 2246201 := bstep (se 2 (by rfl) ⟨842325, by rfl⟩ : syracuseStep 2246201 = 1684651) B1684651
theorem B2131591 : Blo 1496068 2131591 := bstep (se 1 (by rfl) ⟨1598693, by rfl⟩ : syracuseStep 2131591 = 3197387) B3197387
theorem B2246279 : Blo 1496068 2246279 := bstep (se 1 (by rfl) ⟨1684709, by rfl⟩ : syracuseStep 2246279 = 3369419) B3369419
theorem B2246315 : Blo 1496068 2246315 := bstep (se 1 (by rfl) ⟨1684736, by rfl⟩ : syracuseStep 2246315 = 3369473) B3369473
theorem B3696313 : Blo 1496068 3696313 := bstep (se 2 (by rfl) ⟨1386117, by rfl⟩ : syracuseStep 3696313 = 2772235) B2772235
theorem B2246345 : Blo 1496068 2246345 := bstep (se 2 (by rfl) ⟨842379, by rfl⟩ : syracuseStep 2246345 = 1684759) B1684759
theorem B4261643 : Blo 1496068 4261643 := bstep (se 1 (by rfl) ⟨3196232, by rfl⟩ : syracuseStep 4261643 = 6392465) B6392465
theorem B2246459 : Blo 1496068 2246459 := bstep (se 1 (by rfl) ⟨1684844, by rfl⟩ : syracuseStep 2246459 = 3369689) B3369689
theorem B28772171 : Blo 1496068 28772171 := bstep (se 1 (by rfl) ⟨21579128, by rfl⟩ : syracuseStep 28772171 = 43158257) B43158257
theorem B2246519 : Blo 1496068 2246519 := bstep (se 1 (by rfl) ⟨1684889, by rfl⟩ : syracuseStep 2246519 = 3369779) B3369779
theorem B2246543 : Blo 1496068 2246543 := bstep (se 1 (by rfl) ⟨1684907, by rfl⟩ : syracuseStep 2246543 = 3369815) B3369815
theorem B2246585 : Blo 1496068 2246585 := bstep (se 2 (by rfl) ⟨842469, by rfl⟩ : syracuseStep 2246585 = 1684939) B1684939
theorem B7686109 : Blo 1496068 7686109 := bstep (se 3 (by rfl) ⟨1441145, by rfl⟩ : syracuseStep 7686109 = 2882291) B2882291
theorem B2246663 : Blo 1496068 2246663 := bstep (se 1 (by rfl) ⟨1684997, by rfl⟩ : syracuseStep 2246663 = 3369995) B3369995
theorem B32360471 : Blo 1496068 32360471 := bstep (se 1 (by rfl) ⟨24270353, by rfl⟩ : syracuseStep 32360471 = 48540707) B48540707
theorem B2246699 : Blo 1496068 2246699 := bstep (se 1 (by rfl) ⟨1685024, by rfl⟩ : syracuseStep 2246699 = 3370049) B3370049
theorem B2246729 : Blo 1496068 2246729 := bstep (se 2 (by rfl) ⟨842523, by rfl⟩ : syracuseStep 2246729 = 1685047) B1685047
theorem B2525303 : Blo 1496068 2525303 := bstep (se 1 (by rfl) ⟨1893977, by rfl⟩ : syracuseStep 2525303 = 3787955) B3787955
theorem B1894519 : Blo 1496068 1894519 := bstep (se 1 (by rfl) ⟨1420889, by rfl⟩ : syracuseStep 1894519 = 2841779) B2841779
theorem B3369095 : Blo 1496068 3369095 := bstep (se 1 (by rfl) ⟨2526821, by rfl⟩ : syracuseStep 3369095 = 5053643) B5053643
theorem B3467411 : Blo 1496068 3467411 := bstep (se 1 (by rfl) ⟨2600558, by rfl⟩ : syracuseStep 3467411 = 5201117) B5201117
theorem B2246843 : Blo 1496068 2246843 := bstep (se 1 (by rfl) ⟨1685132, by rfl⟩ : syracuseStep 2246843 = 3370265) B3370265
theorem B2246903 : Blo 1496068 2246903 := bstep (se 1 (by rfl) ⟨1685177, by rfl⟩ : syracuseStep 2246903 = 3370355) B3370355
theorem B2246927 : Blo 1496068 2246927 := bstep (se 1 (by rfl) ⟨1685195, by rfl⟩ : syracuseStep 2246927 = 3370391) B3370391
theorem B5687567 : Blo 1496068 5687567 := bstep (se 1 (by rfl) ⟨4265675, by rfl⟩ : syracuseStep 5687567 = 8531351) B8531351
theorem B2246969 : Blo 1496068 2246969 := bstep (se 2 (by rfl) ⟨842613, by rfl⟩ : syracuseStep 2246969 = 1685227) B1685227
theorem B3369275 : Blo 1496068 3369275 := bstep (se 1 (by rfl) ⟨2526956, by rfl⟩ : syracuseStep 3369275 = 5053913) B5053913
theorem B2247047 : Blo 1496068 2247047 := bstep (se 1 (by rfl) ⟨1685285, by rfl⟩ : syracuseStep 2247047 = 3370571) B3370571
theorem B2247083 : Blo 1496068 2247083 := bstep (se 1 (by rfl) ⟨1685312, by rfl⟩ : syracuseStep 2247083 = 3370625) B3370625
theorem B3369401 : Blo 1496068 3369401 := bstep (se 2 (by rfl) ⟨1263525, by rfl⟩ : syracuseStep 3369401 = 2527051) B2527051
theorem B1894843 : Blo 1496068 1894843 := bstep (se 1 (by rfl) ⟨1421132, by rfl⟩ : syracuseStep 1894843 = 2842265) B2842265
theorem B7195139 : Blo 1496068 7195139 := bstep (se 1 (by rfl) ⟨5396354, by rfl⟩ : syracuseStep 7195139 = 10792709) B10792709
theorem B1919495 : Blo 1496068 1919495 := bstep (se 1 (by rfl) ⟨1439621, by rfl⟩ : syracuseStep 1919495 = 2879243) B2879243
theorem B7678475 : Blo 1496068 7678475 := bstep (se 1 (by rfl) ⟨5758856, by rfl⟩ : syracuseStep 7678475 = 11517713) B11517713
theorem B3787307 : Blo 1496068 3787307 := bstep (se 1 (by rfl) ⟨2840480, by rfl⟩ : syracuseStep 3787307 = 5680961) B5680961
theorem B2525755 : Blo 1496068 2525755 := bstep (se 1 (by rfl) ⟨1894316, by rfl⟩ : syracuseStep 2525755 = 3788633) B3788633
theorem B1518139 : Blo 1496068 1518139 := bstep (se 1 (by rfl) ⟨1138604, by rfl⟩ : syracuseStep 1518139 = 2277209) B2277209
theorem B2525897 : Blo 1496068 2525897 := bstep (se 2 (by rfl) ⟨947211, by rfl⟩ : syracuseStep 2525897 = 1894423) B1894423
theorem B3369743 : Blo 1496068 3369743 := bstep (se 1 (by rfl) ⟨2527307, by rfl⟩ : syracuseStep 3369743 = 5054615) B5054615
theorem B6073103 : Blo 1496068 6073103 := bstep (se 1 (by rfl) ⟨4554827, by rfl⟩ : syracuseStep 6073103 = 9109655) B9109655
theorem B3369761 : Blo 1496068 3369761 := bstep (se 2 (by rfl) ⟨1263660, by rfl⟩ : syracuseStep 3369761 = 2527321) B2527321
theorem B19434275 : Blo 1496068 19434275 := bstep (se 1 (by rfl) ⟨14575706, by rfl⟩ : syracuseStep 19434275 = 29151413) B29151413
theorem B4795195 : Blo 1496068 4795195 := bstep (se 1 (by rfl) ⟨3596396, by rfl⟩ : syracuseStep 4795195 = 7192793) B7192793
theorem B1895339 : Blo 1496068 1895339 := bstep (se 1 (by rfl) ⟨1421504, by rfl⟩ : syracuseStep 1895339 = 2843009) B2843009
theorem B3599375 : Blo 1496068 3599375 := bstep (se 1 (by rfl) ⟨2699531, by rfl⟩ : syracuseStep 3599375 = 5399063) B5399063
theorem B5049431 : Blo 1496068 5049431 := bstep (se 1 (by rfl) ⟨3787073, by rfl⟩ : syracuseStep 5049431 = 7574147) B7574147
theorem B3370103 : Blo 1496068 3370103 := bstep (se 1 (by rfl) ⟨2527577, by rfl⟩ : syracuseStep 3370103 = 5055155) B5055155
theorem B4795681 : Blo 1496068 4795681 := bstep (se 2 (by rfl) ⟨1798380, by rfl⟩ : syracuseStep 4795681 = 3596761) B3596761
theorem B11373857 : Blo 1496068 11373857 := bstep (se 2 (by rfl) ⟨4265196, by rfl⟩ : syracuseStep 11373857 = 8530393) B8530393
theorem B3370283 : Blo 1496068 3370283 := bstep (se 1 (by rfl) ⟨2527712, by rfl⟩ : syracuseStep 3370283 = 5055425) B5055425
theorem B3788147 : Blo 1496068 3788147 := bstep (se 1 (by rfl) ⟨2841110, by rfl⟩ : syracuseStep 3788147 = 5682221) B5682221
theorem B4263283 : Blo 1496068 4263283 := bstep (se 1 (by rfl) ⟨3197462, by rfl⟩ : syracuseStep 4263283 = 6394925) B6394925
theorem B3788167 : Blo 1496068 3788167 := bstep (se 1 (by rfl) ⟨2841125, by rfl⟩ : syracuseStep 3788167 = 5682251) B5682251
theorem B2526599 : Blo 1496068 2526599 := bstep (se 1 (by rfl) ⟨1894949, by rfl⟩ : syracuseStep 2526599 = 3789899) B3789899
theorem B1895815 : Blo 1496068 1895815 := bstep (se 1 (by rfl) ⟨1421861, by rfl⟩ : syracuseStep 1895815 = 2843723) B2843723
theorem B7581113 : Blo 1496068 7581113 := bstep (se 2 (by rfl) ⟨2842917, by rfl⟩ : syracuseStep 7581113 = 5685835) B5685835
theorem B12144131 : Blo 1496068 12144131 := bstep (se 1 (by rfl) ⟨9108098, by rfl⟩ : syracuseStep 12144131 = 18216197) B18216197
theorem B7294475 : Blo 1496068 7294475 := bstep (se 1 (by rfl) ⟨5470856, by rfl⟩ : syracuseStep 7294475 = 10941713) B10941713
theorem B5262877 : Blo 1496068 5262877 := bstep (se 3 (by rfl) ⟨986789, by rfl⟩ : syracuseStep 5262877 = 1973579) B1973579
theorem B5049917 : Blo 1496068 5049917 := bstep (se 3 (by rfl) ⟨946859, by rfl⟩ : syracuseStep 5049917 = 1893719) B1893719
theorem B4263511 : Blo 1496068 4263511 := bstep (se 1 (by rfl) ⟨3197633, by rfl⟩ : syracuseStep 4263511 = 6395267) B6395267
theorem B3370643 : Blo 1496068 3370643 := bstep (se 1 (by rfl) ⟨2527982, by rfl⟩ : syracuseStep 3370643 = 5055965) B5055965
theorem B3788441 : Blo 1496068 3788441 := bstep (se 2 (by rfl) ⟨1420665, by rfl⟩ : syracuseStep 3788441 = 2841331) B2841331
theorem B11366081 : Blo 1496068 11366081 := bstep (se 2 (by rfl) ⟨4262280, by rfl⟩ : syracuseStep 11366081 = 8524561) B8524561
theorem B3788603 : Blo 1496068 3788603 := bstep (se 1 (by rfl) ⟨2841452, by rfl⟩ : syracuseStep 3788603 = 5682905) B5682905
theorem B24293195 : Blo 1496068 24293195 := bstep (se 1 (by rfl) ⟨18219896, by rfl⟩ : syracuseStep 24293195 = 36439793) B36439793
theorem B2559929 : Blo 1496068 2559929 := bstep (se 2 (by rfl) ⟨959973, by rfl⟩ : syracuseStep 2559929 = 1919947) B1919947
theorem B1683463 : Blo 1496068 1683463 := bstep (se 1 (by rfl) ⟨1262597, by rfl⟩ : syracuseStep 1683463 = 2525195) B2525195
theorem B36892685 : Blo 1496068 36892685 := bstep (se 3 (by rfl) ⟨6917378, by rfl⟩ : syracuseStep 36892685 = 13834757) B13834757
theorem B3788815 : Blo 1496068 3788815 := bstep (se 1 (by rfl) ⟨2841611, by rfl⟩ : syracuseStep 3788815 = 5683223) B5683223
theorem B2527247 : Blo 1496068 2527247 := bstep (se 1 (by rfl) ⟨1895435, by rfl⟩ : syracuseStep 2527247 = 3790871) B3790871
theorem B9596951 : Blo 1496068 9596951 := bstep (se 1 (by rfl) ⟨7197713, by rfl⟩ : syracuseStep 9596951 = 14395427) B14395427
theorem B1683643 : Blo 1496068 1683643 := bstep (se 1 (by rfl) ⟨1262732, by rfl⟩ : syracuseStep 1683643 = 2525465) B2525465
theorem B11374829 : Blo 1496068 11374829 := bstep (se 3 (by rfl) ⟨2132780, by rfl⟩ : syracuseStep 11374829 = 4265561) B4265561
theorem B12783905 : Blo 1496068 12783905 := bstep (se 2 (by rfl) ⟨4793964, by rfl⟩ : syracuseStep 12783905 = 9587929) B9587929
theorem B3789089 : Blo 1496068 3789089 := bstep (se 2 (by rfl) ⟨1420908, by rfl⟩ : syracuseStep 3789089 = 2841817) B2841817
theorem B11522449 : Blo 1496068 11522449 := bstep (se 2 (by rfl) ⟨4320918, by rfl⟩ : syracuseStep 11522449 = 8641837) B8641837
theorem B3035539 : Blo 1496068 3035539 := bstep (se 1 (by rfl) ⟨2276654, by rfl⟩ : syracuseStep 3035539 = 4553309) B4553309
theorem B7197137 : Blo 1496068 7197137 := bstep (se 2 (by rfl) ⟨2698926, by rfl⟩ : syracuseStep 7197137 = 5397853) B5397853
theorem B2527787 : Blo 1496068 2527787 := bstep (se 1 (by rfl) ⟨1895840, by rfl⟩ : syracuseStep 2527787 = 3791681) B3791681
theorem B1684111 : Blo 1496068 1684111 := bstep (se 1 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 1684111 = 2526167) B2526167
theorem B60748481 : Blo 1496068 60748481 := bstep (se 2 (by rfl) ⟨22780680, by rfl⟩ : syracuseStep 60748481 = 45561361) B45561361
theorem B7582409 : Blo 1496068 7582409 := bstep (se 2 (by rfl) ⟨2843403, by rfl⟩ : syracuseStep 7582409 = 5686807) B5686807
theorem B2159479 : Blo 1496068 2159479 := bstep (se 1 (by rfl) ⟨1619609, by rfl⟩ : syracuseStep 2159479 = 3239219) B3239219
theorem B5051321 : Blo 1496068 5051321 := bstep (se 2 (by rfl) ⟨1894245, by rfl⟩ : syracuseStep 5051321 = 3788491) B3788491
theorem B1496071 : Blo 1496068 1496071 := bstep (se 1 (by rfl) ⟨1122053, by rfl⟩ : syracuseStep 1496071 = 2244107) B2244107
theorem B1496079 : Blo 1496068 1496079 := bstep (se 1 (by rfl) ⟨1122059, by rfl⟩ : syracuseStep 1496079 = 2244119) B2244119
theorem B6394909 : Blo 1496068 6394909 := bstep (se 3 (by rfl) ⟨1199045, by rfl⟩ : syracuseStep 6394909 = 2398091) B2398091
theorem B1496123 : Blo 1496068 1496123 := bstep (se 1 (by rfl) ⟨1122092, by rfl⟩ : syracuseStep 1496123 = 2244185) B2244185
theorem B1496199 : Blo 1496068 1496199 := bstep (se 1 (by rfl) ⟨1122149, by rfl⟩ : syracuseStep 1496199 = 2244299) B2244299
theorem B1684615 : Blo 1496068 1684615 := bstep (se 1 (by rfl) ⟨1263461, by rfl⟩ : syracuseStep 1684615 = 2526923) B2526923
theorem B1799303 : Blo 1496068 1799303 := bstep (se 1 (by rfl) ⟨1349477, by rfl⟩ : syracuseStep 1799303 = 2698955) B2698955
theorem B4265095 : Blo 1496068 4265095 := bstep (se 1 (by rfl) ⟨3198821, by rfl⟩ : syracuseStep 4265095 = 6397643) B6397643
theorem B1496207 : Blo 1496068 1496207 := bstep (se 1 (by rfl) ⟨1122155, by rfl⟩ : syracuseStep 1496207 = 2244311) B2244311
theorem B1496251 : Blo 1496068 1496251 := bstep (se 1 (by rfl) ⟨1122188, by rfl⟩ : syracuseStep 1496251 = 2244377) B2244377
theorem B3839177 : Blo 1496068 3839177 := bstep (se 2 (by rfl) ⟨1439691, by rfl⟩ : syracuseStep 3839177 = 2879383) B2879383
theorem B5682433 : Blo 1496068 5682433 := bstep (se 2 (by rfl) ⟨2130912, by rfl⟩ : syracuseStep 5682433 = 4261825) B4261825
theorem B1496327 : Blo 1496068 1496327 := bstep (se 1 (by rfl) ⟨1122245, by rfl⟩ : syracuseStep 1496327 = 2244491) B2244491
theorem B3790091 : Blo 1496068 3790091 := bstep (se 1 (by rfl) ⟨2842568, by rfl⟩ : syracuseStep 3790091 = 5685137) B5685137
theorem B1496335 : Blo 1496068 1496335 := bstep (se 1 (by rfl) ⟨1122251, by rfl⟩ : syracuseStep 1496335 = 2244503) B2244503
theorem B9229619 : Blo 1496068 9229619 := bstep (se 1 (by rfl) ⟨6922214, by rfl⟩ : syracuseStep 9229619 = 13844429) B13844429
theorem B1496379 : Blo 1496068 1496379 := bstep (se 1 (by rfl) ⟨1122284, by rfl⟩ : syracuseStep 1496379 = 2244569) B2244569
theorem B1684795 : Blo 1496068 1684795 := bstep (se 1 (by rfl) ⟨1263596, by rfl⟩ : syracuseStep 1684795 = 2527193) B2527193
theorem B1496455 : Blo 1496068 1496455 := bstep (se 1 (by rfl) ⟨1122341, by rfl⟩ : syracuseStep 1496455 = 2244683) B2244683
theorem B1496463 : Blo 1496068 1496463 := bstep (se 1 (by rfl) ⟨1122347, by rfl⟩ : syracuseStep 1496463 = 2244695) B2244695
theorem B10786193 : Blo 1496068 10786193 := bstep (se 2 (by rfl) ⟨4044822, by rfl⟩ : syracuseStep 10786193 = 8089645) B8089645
theorem B4044185 : Blo 1496068 4044185 := bstep (se 2 (by rfl) ⟨1516569, by rfl⟩ : syracuseStep 4044185 = 3033139) B3033139
theorem B4265369 : Blo 1496068 4265369 := bstep (se 2 (by rfl) ⟨1599513, by rfl⟩ : syracuseStep 4265369 = 3199027) B3199027
theorem B1496507 : Blo 1496068 1496507 := bstep (se 1 (by rfl) ⟨1122380, by rfl⟩ : syracuseStep 1496507 = 2244761) B2244761
theorem B21878225 : Blo 1496068 21878225 := bstep (se 2 (by rfl) ⟨8204334, by rfl⟩ : syracuseStep 21878225 = 16408669) B16408669
theorem B9590237 : Blo 1496068 9590237 := bstep (se 3 (by rfl) ⟨1798169, by rfl⟩ : syracuseStep 9590237 = 3596339) B3596339
theorem B1496583 : Blo 1496068 1496583 := bstep (se 1 (by rfl) ⟨1122437, by rfl⟩ : syracuseStep 1496583 = 2244875) B2244875
theorem B5051915 : Blo 1496068 5051915 := bstep (se 1 (by rfl) ⟨3788936, by rfl⟩ : syracuseStep 5051915 = 7577873) B7577873
theorem B5395979 : Blo 1496068 5395979 := bstep (se 1 (by rfl) ⟨4046984, by rfl⟩ : syracuseStep 5395979 = 8093969) B8093969
theorem B1496591 : Blo 1496068 1496591 := bstep (se 1 (by rfl) ⟨1122443, by rfl⟩ : syracuseStep 1496591 = 2244887) B2244887
theorem B1496635 : Blo 1496068 1496635 := bstep (se 1 (by rfl) ⟨1122476, by rfl⟩ : syracuseStep 1496635 = 2244953) B2244953
theorem B23033443 : Blo 1496068 23033443 := bstep (se 1 (by rfl) ⟨17275082, by rfl⟩ : syracuseStep 23033443 = 34550165) B34550165
theorem B5052023 : Blo 1496068 5052023 := bstep (se 1 (by rfl) ⟨3789017, by rfl⟩ : syracuseStep 5052023 = 7578035) B7578035
theorem B1496711 : Blo 1496068 1496711 := bstep (se 1 (by rfl) ⟨1122533, by rfl⟩ : syracuseStep 1496711 = 2245067) B2245067
theorem B1496719 : Blo 1496068 1496719 := bstep (se 1 (by rfl) ⟨1122539, by rfl⟩ : syracuseStep 1496719 = 2245079) B2245079
theorem B1496763 : Blo 1496068 1496763 := bstep (se 1 (by rfl) ⟨1122572, by rfl⟩ : syracuseStep 1496763 = 2245145) B2245145
theorem B1496839 : Blo 1496068 1496839 := bstep (se 1 (by rfl) ⟨1122629, by rfl⟩ : syracuseStep 1496839 = 2245259) B2245259
theorem B1496847 : Blo 1496068 1496847 := bstep (se 1 (by rfl) ⟨1122635, by rfl⟩ : syracuseStep 1496847 = 2245271) B2245271
theorem B1685263 : Blo 1496068 1685263 := bstep (se 1 (by rfl) ⟨1263947, by rfl⟩ : syracuseStep 1685263 = 2527895) B2527895
theorem B10385189 : Blo 1496068 10385189 := bstep (se 4 (by rfl) ⟨973611, by rfl⟩ : syracuseStep 10385189 = 1947223) B1947223
theorem B2397995 : Blo 1496068 2397995 := bstep (se 1 (by rfl) ⟨1798496, by rfl⟩ : syracuseStep 2397995 = 3596993) B3596993
theorem B32380721 : Blo 1496068 32380721 := bstep (se 2 (by rfl) ⟨12142770, by rfl⟩ : syracuseStep 32380721 = 24285541) B24285541
theorem B1496891 : Blo 1496068 1496891 := bstep (se 1 (by rfl) ⟨1122668, by rfl⟩ : syracuseStep 1496891 = 2245337) B2245337
theorem B63141697 : Blo 1496068 63141697 := bstep (se 2 (by rfl) ⟨23678136, by rfl⟩ : syracuseStep 63141697 = 47356273) B47356273
theorem B1496967 : Blo 1496068 1496967 := bstep (se 1 (by rfl) ⟨1122725, by rfl⟩ : syracuseStep 1496967 = 2245451) B2245451
theorem B1496975 : Blo 1496068 1496975 := bstep (se 1 (by rfl) ⟨1122731, by rfl⟩ : syracuseStep 1496975 = 2245463) B2245463
theorem B7575443 : Blo 1496068 7575443 := bstep (se 1 (by rfl) ⟨5681582, by rfl⟩ : syracuseStep 7575443 = 11363165) B11363165
theorem B3790739 : Blo 1496068 3790739 := bstep (se 1 (by rfl) ⟨2843054, by rfl⟩ : syracuseStep 3790739 = 5686109) B5686109
theorem B1497019 : Blo 1496068 1497019 := bstep (se 1 (by rfl) ⟨1122764, by rfl⟩ : syracuseStep 1497019 = 2245529) B2245529
theorem B1497095 : Blo 1496068 1497095 := bstep (se 1 (by rfl) ⟨1122821, by rfl⟩ : syracuseStep 1497095 = 2245643) B2245643
theorem B1497103 : Blo 1496068 1497103 := bstep (se 1 (by rfl) ⟨1122827, by rfl⟩ : syracuseStep 1497103 = 2245655) B2245655
theorem B2840609 : Blo 1496068 2840609 := bstep (se 2 (by rfl) ⟨1065228, by rfl⟩ : syracuseStep 2840609 = 2130457) B2130457
theorem B1497147 : Blo 1496068 1497147 := bstep (se 1 (by rfl) ⟨1122860, by rfl⟩ : syracuseStep 1497147 = 2245721) B2245721
theorem B37427293 : Blo 1496068 37427293 := bstep (se 3 (by rfl) ⟨7017617, by rfl⟩ : syracuseStep 37427293 = 14035235) B14035235
theorem B2562167 : Blo 1496068 2562167 := bstep (se 1 (by rfl) ⟨1921625, by rfl⟩ : syracuseStep 2562167 = 3843251) B3843251
theorem B1497223 : Blo 1496068 1497223 := bstep (se 1 (by rfl) ⟨1122917, by rfl⟩ : syracuseStep 1497223 = 2245835) B2245835
theorem B1497231 : Blo 1496068 1497231 := bstep (se 1 (by rfl) ⟨1122923, by rfl⟩ : syracuseStep 1497231 = 2245847) B2245847
theorem B2840761 : Blo 1496068 2840761 := bstep (se 2 (by rfl) ⟨1065285, by rfl⟩ : syracuseStep 2840761 = 2130571) B2130571
theorem B3791033 : Blo 1496068 3791033 := bstep (se 2 (by rfl) ⟨1421637, by rfl⟩ : syracuseStep 3791033 = 2843275) B2843275
theorem B1497275 : Blo 1496068 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B5052617 : Blo 1496068 5052617 := bstep (se 2 (by rfl) ⟨1894731, by rfl⟩ : syracuseStep 5052617 = 3789463) B3789463
theorem B1497351 : Blo 1496068 1497351 := bstep (se 1 (by rfl) ⟨1123013, by rfl⟩ : syracuseStep 1497351 = 2246027) B2246027
theorem B1497359 : Blo 1496068 1497359 := bstep (se 1 (by rfl) ⟨1123019, by rfl⟩ : syracuseStep 1497359 = 2246039) B2246039
theorem B1497403 : Blo 1496068 1497403 := bstep (se 1 (by rfl) ⟨1123052, by rfl⟩ : syracuseStep 1497403 = 2246105) B2246105
theorem B1497479 : Blo 1496068 1497479 := bstep (se 1 (by rfl) ⟨1123109, by rfl⟩ : syracuseStep 1497479 = 2246219) B2246219
theorem B1497487 : Blo 1496068 1497487 := bstep (se 1 (by rfl) ⟨1123115, by rfl⟩ : syracuseStep 1497487 = 2246231) B2246231
theorem B1497531 : Blo 1496068 1497531 := bstep (se 1 (by rfl) ⟨1123148, by rfl⟩ : syracuseStep 1497531 = 2246297) B2246297
theorem B1497607 : Blo 1496068 1497607 := bstep (se 1 (by rfl) ⟨1123205, by rfl⟩ : syracuseStep 1497607 = 2246411) B2246411
theorem B1497615 : Blo 1496068 1497615 := bstep (se 1 (by rfl) ⟨1123211, by rfl⟩ : syracuseStep 1497615 = 2246423) B2246423
theorem B1497659 : Blo 1496068 1497659 := bstep (se 1 (by rfl) ⟨1123244, by rfl⟩ : syracuseStep 1497659 = 2246489) B2246489
theorem B12786295 : Blo 1496068 12786295 := bstep (se 1 (by rfl) ⟨9589721, by rfl⟩ : syracuseStep 12786295 = 19179443) B19179443
theorem B16194167 : Blo 1496068 16194167 := bstep (se 1 (by rfl) ⟨12145625, by rfl⟩ : syracuseStep 16194167 = 24291251) B24291251
theorem B1497735 : Blo 1496068 1497735 := bstep (se 1 (by rfl) ⟨1123301, by rfl⟩ : syracuseStep 1497735 = 2246603) B2246603
theorem B1497743 : Blo 1496068 1497743 := bstep (se 1 (by rfl) ⟨1123307, by rfl⟩ : syracuseStep 1497743 = 2246615) B2246615
theorem B1497787 : Blo 1496068 1497787 := bstep (se 1 (by rfl) ⟨1123340, by rfl⟩ : syracuseStep 1497787 = 2246681) B2246681
theorem B1497863 : Blo 1496068 1497863 := bstep (se 1 (by rfl) ⟨1123397, by rfl⟩ : syracuseStep 1497863 = 2246795) B2246795
theorem B1497871 : Blo 1496068 1497871 := bstep (se 1 (by rfl) ⟨1123403, by rfl⟩ : syracuseStep 1497871 = 2246807) B2246807
theorem B4045601 : Blo 1496068 4045601 := bstep (se 2 (by rfl) ⟨1517100, by rfl⟩ : syracuseStep 4045601 = 3034201) B3034201
theorem B1497915 : Blo 1496068 1497915 := bstep (se 1 (by rfl) ⟨1123436, by rfl⟩ : syracuseStep 1497915 = 2246873) B2246873
theorem B3791731 : Blo 1496068 3791731 := bstep (se 1 (by rfl) ⟨2843798, by rfl⟩ : syracuseStep 3791731 = 5687597) B5687597
theorem B5053319 : Blo 1496068 5053319 := bstep (se 1 (by rfl) ⟨3789989, by rfl⟩ : syracuseStep 5053319 = 7579979) B7579979
theorem B1497991 : Blo 1496068 1497991 := bstep (se 1 (by rfl) ⟨1123493, by rfl⟩ : syracuseStep 1497991 = 2246987) B2246987
theorem B1497999 : Blo 1496068 1497999 := bstep (se 1 (by rfl) ⟨1123499, by rfl⟩ : syracuseStep 1497999 = 2246999) B2246999
theorem B7191449 : Blo 1496068 7191449 := bstep (se 2 (by rfl) ⟨2696793, by rfl⟩ : syracuseStep 7191449 = 5393587) B5393587
theorem B6831001 : Blo 1496068 6831001 := bstep (se 2 (by rfl) ⟨2561625, by rfl⟩ : syracuseStep 6831001 = 5123251) B5123251
theorem B3644345 : Blo 1496068 3644345 := bstep (se 2 (by rfl) ⟨1366629, by rfl⟩ : syracuseStep 3644345 = 2733259) B2733259
theorem B1498043 : Blo 1496068 1498043 := bstep (se 1 (by rfl) ⟨1123532, by rfl⟩ : syracuseStep 1498043 = 2247065) B2247065
theorem B3791873 : Blo 1496068 3791873 := bstep (se 2 (by rfl) ⟨1421952, by rfl⟩ : syracuseStep 3791873 = 2843905) B2843905
theorem B11369483 : Blo 1496068 11369483 := bstep (se 1 (by rfl) ⟨8527112, by rfl⟩ : syracuseStep 11369483 = 17054225) B17054225
theorem B10787863 : Blo 1496068 10787863 := bstep (se 1 (by rfl) ⟨8090897, by rfl⟩ : syracuseStep 10787863 = 16181795) B16181795
theorem B17062973 : Blo 1496068 17062973 := bstep (se 3 (by rfl) ⟨3199307, by rfl⟩ : syracuseStep 17062973 = 6398615) B6398615
theorem B5397623 : Blo 1496068 5397623 := bstep (se 1 (by rfl) ⟨4048217, by rfl⟩ : syracuseStep 5397623 = 8096435) B8096435
theorem B9723053 : Blo 1496068 9723053 := bstep (se 3 (by rfl) ⟨1823072, by rfl⟩ : syracuseStep 9723053 = 3646145) B3646145
theorem B5053697 : Blo 1496068 5053697 := bstep (se 2 (by rfl) ⟨1895136, by rfl⟩ : syracuseStep 5053697 = 3790273) B3790273
theorem B3595531 : Blo 1496068 3595531 := bstep (se 1 (by rfl) ⟨2696648, by rfl⟩ : syracuseStep 3595531 = 5393297) B5393297
theorem B28761479 : Blo 1496068 28761479 := bstep (se 1 (by rfl) ⟨21571109, by rfl⟩ : syracuseStep 28761479 = 43142219) B43142219
theorem B2244155 : Blo 1496068 2244155 := bstep (se 1 (by rfl) ⟨1683116, by rfl⟩ : syracuseStep 2244155 = 3366233) B3366233
theorem B2244215 : Blo 1496068 2244215 := bstep (se 1 (by rfl) ⟨1683161, by rfl⟩ : syracuseStep 2244215 = 3366323) B3366323
theorem B2244239 : Blo 1496068 2244239 := bstep (se 1 (by rfl) ⟨1683179, by rfl⟩ : syracuseStep 2244239 = 3366359) B3366359
theorem B2244281 : Blo 1496068 2244281 := bstep (se 2 (by rfl) ⟨841605, by rfl⟩ : syracuseStep 2244281 = 1683211) B1683211
theorem B2244359 : Blo 1496068 2244359 := bstep (se 1 (by rfl) ⟨1683269, by rfl⟩ : syracuseStep 2244359 = 3366539) B3366539
theorem B2244395 : Blo 1496068 2244395 := bstep (se 1 (by rfl) ⟨1683296, by rfl⟩ : syracuseStep 2244395 = 3366593) B3366593
theorem B2244425 : Blo 1496068 2244425 := bstep (se 2 (by rfl) ⟨841659, by rfl⟩ : syracuseStep 2244425 = 1683319) B1683319
theorem B3366791 : Blo 1496068 3366791 := bstep (se 1 (by rfl) ⟨2525093, by rfl⟩ : syracuseStep 3366791 = 5050187) B5050187
theorem B8527751 : Blo 1496068 8527751 := bstep (se 1 (by rfl) ⟨6395813, by rfl⟩ : syracuseStep 8527751 = 12791627) B12791627
theorem B2842553 : Blo 1496068 2842553 := bstep (se 2 (by rfl) ⟨1065957, by rfl⟩ : syracuseStep 2842553 = 2131915) B2131915
theorem B2244539 : Blo 1496068 2244539 := bstep (se 1 (by rfl) ⟨1683404, by rfl⟩ : syracuseStep 2244539 = 3366809) B3366809
theorem B2244599 : Blo 1496068 2244599 := bstep (se 1 (by rfl) ⟨1683449, by rfl⟩ : syracuseStep 2244599 = 3366899) B3366899
theorem B2244617 : Blo 1496068 2244617 := bstep (se 2 (by rfl) ⟨841731, by rfl⟩ : syracuseStep 2244617 = 1683463) B1683463
theorem B6397967 : Blo 1496068 6397967 := bstep (se 1 (by rfl) ⟨4798475, by rfl⟩ : syracuseStep 6397967 = 9596951) B9596951
theorem B2244647 : Blo 1496068 2244647 := bstep (se 1 (by rfl) ⟨1683485, by rfl⟩ : syracuseStep 2244647 = 3366971) B3366971
theorem B8093753 : Blo 1496068 8093753 := bstep (se 2 (by rfl) ⟨3035157, by rfl⟩ : syracuseStep 8093753 = 6070315) B6070315
theorem B2244731 : Blo 1496068 2244731 := bstep (se 1 (by rfl) ⟨1683548, by rfl⟩ : syracuseStep 2244731 = 3367097) B3367097
theorem B2244857 : Blo 1496068 2244857 := bstep (se 2 (by rfl) ⟨841821, by rfl⟩ : syracuseStep 2244857 = 1683643) B1683643
theorem B2244959 : Blo 1496068 2244959 := bstep (se 1 (by rfl) ⟨1683719, by rfl⟩ : syracuseStep 2244959 = 3367439) B3367439
theorem B2244971 : Blo 1496068 2244971 := bstep (se 1 (by rfl) ⟨1683728, by rfl⟩ : syracuseStep 2244971 = 3367457) B3367457
theorem B25592273 : Blo 1496068 25592273 := bstep (se 2 (by rfl) ⟨9597102, by rfl⟩ : syracuseStep 25592273 = 19194205) B19194205
theorem B5054939 : Blo 1496068 5054939 := bstep (se 1 (by rfl) ⟨3791204, by rfl⟩ : syracuseStep 5054939 = 7582409) B7582409
theorem B2245199 : Blo 1496068 2245199 := bstep (se 1 (by rfl) ⟨1683899, by rfl⟩ : syracuseStep 2245199 = 3367799) B3367799
theorem B3367547 : Blo 1496068 3367547 := bstep (se 1 (by rfl) ⟨2525660, by rfl⟩ : syracuseStep 3367547 = 5051321) B5051321
theorem B2245319 : Blo 1496068 2245319 := bstep (se 1 (by rfl) ⟨1683989, by rfl⟩ : syracuseStep 2245319 = 3367979) B3367979
theorem B3367673 : Blo 1496068 3367673 := bstep (se 2 (by rfl) ⟨1262877, by rfl⟩ : syracuseStep 3367673 = 2525755) B2525755
theorem B2024185 : Blo 1496068 2024185 := bstep (se 2 (by rfl) ⟨759069, by rfl⟩ : syracuseStep 2024185 = 1518139) B1518139
theorem B17048393 : Blo 1496068 17048393 := bstep (se 2 (by rfl) ⟨6393147, by rfl⟩ : syracuseStep 17048393 = 12786295) B12786295
theorem B2245481 : Blo 1496068 2245481 := bstep (se 2 (by rfl) ⟨842055, by rfl⟩ : syracuseStep 2245481 = 1684111) B1684111
theorem B6153079 : Blo 1496068 6153079 := bstep (se 1 (by rfl) ⟨4614809, by rfl⟩ : syracuseStep 6153079 = 9229619) B9229619
theorem B7685039 : Blo 1496068 7685039 := bstep (se 1 (by rfl) ⟨5763779, by rfl⟩ : syracuseStep 7685039 = 11527559) B11527559
theorem B2245559 : Blo 1496068 2245559 := bstep (se 1 (by rfl) ⟨1684169, by rfl⟩ : syracuseStep 2245559 = 3368339) B3368339
theorem B2696123 : Blo 1496068 2696123 := bstep (se 1 (by rfl) ⟨2022092, by rfl⟩ : syracuseStep 2696123 = 4044185) B4044185
theorem B2843579 : Blo 1496068 2843579 := bstep (se 1 (by rfl) ⟨2132684, by rfl⟩ : syracuseStep 2843579 = 4265369) B4265369
theorem B2245595 : Blo 1496068 2245595 := bstep (se 1 (by rfl) ⟨1684196, by rfl⟩ : syracuseStep 2245595 = 3368393) B3368393
theorem B3367943 : Blo 1496068 3367943 := bstep (se 1 (by rfl) ⟨2525957, by rfl⟩ : syracuseStep 3367943 = 5051915) B5051915
theorem B3597319 : Blo 1496068 3597319 := bstep (se 1 (by rfl) ⟨2697989, by rfl⟩ : syracuseStep 3597319 = 5395979) B5395979
theorem B3368015 : Blo 1496068 3368015 := bstep (se 1 (by rfl) ⟨2526011, by rfl⟩ : syracuseStep 3368015 = 5052023) B5052023
theorem B5055641 : Blo 1496068 5055641 := bstep (se 2 (by rfl) ⟨1895865, by rfl⟩ : syracuseStep 5055641 = 3791731) B3791731
theorem B6923459 : Blo 1496068 6923459 := bstep (se 1 (by rfl) ⟨5192594, by rfl⟩ : syracuseStep 6923459 = 10385189) B10385189
theorem B1598663 : Blo 1496068 1598663 := bstep (se 1 (by rfl) ⟨1198997, by rfl⟩ : syracuseStep 1598663 = 2397995) B2397995
theorem B21587147 : Blo 1496068 21587147 := bstep (se 1 (by rfl) ⟨16190360, by rfl⟩ : syracuseStep 21587147 = 32380721) B32380721
theorem B2246063 : Blo 1496068 2246063 := bstep (se 1 (by rfl) ⟨1684547, by rfl⟩ : syracuseStep 2246063 = 3369095) B3369095
theorem B2311607 : Blo 1496068 2311607 := bstep (se 1 (by rfl) ⟨1733705, by rfl⟩ : syracuseStep 2311607 = 3467411) B3467411
theorem B3368411 : Blo 1496068 3368411 := bstep (se 1 (by rfl) ⟨2526308, by rfl⟩ : syracuseStep 3368411 = 5052617) B5052617
theorem B2246153 : Blo 1496068 2246153 := bstep (se 2 (by rfl) ⟨842307, by rfl⟩ : syracuseStep 2246153 = 1684615) B1684615
theorem B5686793 : Blo 1496068 5686793 := bstep (se 2 (by rfl) ⟨2132547, by rfl⟩ : syracuseStep 5686793 = 4265095) B4265095
theorem B2246183 : Blo 1496068 2246183 := bstep (se 1 (by rfl) ⟨1684637, by rfl⟩ : syracuseStep 2246183 = 3369275) B3369275
theorem B2524729 : Blo 1496068 2524729 := bstep (se 2 (by rfl) ⟨946773, by rfl⟩ : syracuseStep 2524729 = 1893547) B1893547
theorem B2246267 : Blo 1496068 2246267 := bstep (se 1 (by rfl) ⟨1684700, by rfl⟩ : syracuseStep 2246267 = 3369401) B3369401
theorem B4794041 : Blo 1496068 4794041 := bstep (se 2 (by rfl) ⟨1797765, by rfl⟩ : syracuseStep 4794041 = 3595531) B3595531
theorem B2524871 : Blo 1496068 2524871 := bstep (se 1 (by rfl) ⟨1893653, by rfl⟩ : syracuseStep 2524871 = 3787307) B3787307
theorem B2246393 : Blo 1496068 2246393 := bstep (se 2 (by rfl) ⟨842397, by rfl⟩ : syracuseStep 2246393 = 1684795) B1684795
theorem B2246495 : Blo 1496068 2246495 := bstep (se 1 (by rfl) ⟨1684871, by rfl⟩ : syracuseStep 2246495 = 3369743) B3369743
theorem B2525033 : Blo 1496068 2525033 := bstep (se 2 (by rfl) ⟨946887, by rfl⟩ : syracuseStep 2525033 = 1893775) B1893775
theorem B2697067 : Blo 1496068 2697067 := bstep (se 1 (by rfl) ⟨2022800, by rfl⟩ : syracuseStep 2697067 = 4045601) B4045601
theorem B2246507 : Blo 1496068 2246507 := bstep (se 1 (by rfl) ⟨1684880, by rfl⟩ : syracuseStep 2246507 = 3369761) B3369761
theorem B3368879 : Blo 1496068 3368879 := bstep (se 1 (by rfl) ⟨2526659, by rfl⟩ : syracuseStep 3368879 = 5053319) B5053319
theorem B4794299 : Blo 1496068 4794299 := bstep (se 1 (by rfl) ⟨3595724, by rfl⟩ : syracuseStep 4794299 = 7191449) B7191449
theorem B7579655 : Blo 1496068 7579655 := bstep (se 1 (by rfl) ⟨5684741, by rfl⟩ : syracuseStep 7579655 = 11369483) B11369483
theorem B3598415 : Blo 1496068 3598415 := bstep (se 1 (by rfl) ⟨2698811, by rfl⟩ : syracuseStep 3598415 = 5397623) B5397623
theorem B2246735 : Blo 1496068 2246735 := bstep (se 1 (by rfl) ⟨1685051, by rfl⟩ : syracuseStep 2246735 = 3370103) B3370103
theorem B16189541 : Blo 1496068 16189541 := bstep (se 4 (by rfl) ⟨1517769, by rfl⟩ : syracuseStep 16189541 = 3035539) B3035539
theorem B6482035 : Blo 1496068 6482035 := bstep (se 1 (by rfl) ⟨4861526, by rfl⟩ : syracuseStep 6482035 = 9723053) B9723053
theorem B3369131 : Blo 1496068 3369131 := bstep (se 1 (by rfl) ⟨2526848, by rfl⟩ : syracuseStep 3369131 = 5053697) B5053697
theorem B2246855 : Blo 1496068 2246855 := bstep (se 1 (by rfl) ⟨1685141, by rfl⟩ : syracuseStep 2246855 = 3370283) B3370283
theorem B2525431 : Blo 1496068 2525431 := bstep (se 1 (by rfl) ⟨1894073, by rfl⟩ : syracuseStep 2525431 = 3788147) B3788147
theorem B8096087 : Blo 1496068 8096087 := bstep (se 1 (by rfl) ⟨6072065, by rfl⟩ : syracuseStep 8096087 = 12144131) B12144131
theorem B2247017 : Blo 1496068 2247017 := bstep (se 2 (by rfl) ⟨842631, by rfl⟩ : syracuseStep 2247017 = 1685263) B1685263
theorem B2247095 : Blo 1496068 2247095 := bstep (se 1 (by rfl) ⟨1685321, by rfl⟩ : syracuseStep 2247095 = 3370643) B3370643
theorem B2525627 : Blo 1496068 2525627 := bstep (se 1 (by rfl) ⟨1894220, by rfl⟩ : syracuseStep 2525627 = 3788441) B3788441
theorem B6826477 : Blo 1496068 6826477 := bstep (se 3 (by rfl) ⟨1279964, by rfl⟩ : syracuseStep 6826477 = 2559929) B2559929
theorem B7580141 : Blo 1496068 7580141 := bstep (se 3 (by rfl) ⟨1421276, by rfl⟩ : syracuseStep 7580141 = 2842553) B2842553
theorem B2525735 : Blo 1496068 2525735 := bstep (se 1 (by rfl) ⟨1894301, by rfl⟩ : syracuseStep 2525735 = 3788603) B3788603
theorem B24595123 : Blo 1496068 24595123 := bstep (se 1 (by rfl) ⟨18446342, by rfl⟩ : syracuseStep 24595123 = 36892685) B36892685
theorem B3369671 : Blo 1496068 3369671 := bstep (se 1 (by rfl) ⟨2527253, by rfl⟩ : syracuseStep 3369671 = 5054507) B5054507
theorem B28068677 : Blo 1496068 28068677 := bstep (se 4 (by rfl) ⟨2631438, by rfl⟩ : syracuseStep 28068677 = 5262877) B5262877
theorem B2526025 : Blo 1496068 2526025 := bstep (se 2 (by rfl) ⟨947259, by rfl⟩ : syracuseStep 2526025 = 1894519) B1894519
theorem B8522603 : Blo 1496068 8522603 := bstep (se 1 (by rfl) ⟨6391952, by rfl⟩ : syracuseStep 8522603 = 12783905) B12783905
theorem B2526059 : Blo 1496068 2526059 := bstep (se 1 (by rfl) ⟨1894544, by rfl⟩ : syracuseStep 2526059 = 3789089) B3789089
theorem B3787681 : Blo 1496068 3787681 := bstep (se 2 (by rfl) ⟨1420380, by rfl⟩ : syracuseStep 3787681 = 2840761) B2840761
theorem B15363265 : Blo 1496068 15363265 := bstep (se 2 (by rfl) ⟨5761224, by rfl⟩ : syracuseStep 15363265 = 11522449) B11522449
theorem B2698451 : Blo 1496068 2698451 := bstep (se 1 (by rfl) ⟨2023838, by rfl⟩ : syracuseStep 2698451 = 4047677) B4047677
theorem B2526457 : Blo 1496068 2526457 := bstep (se 2 (by rfl) ⟨947421, by rfl⟩ : syracuseStep 2526457 = 1894843) B1894843
theorem B7580951 : Blo 1496068 7580951 := bstep (se 1 (by rfl) ⟨5685713, by rfl⟩ : syracuseStep 7580951 = 11371427) B11371427
theorem B28765475 : Blo 1496068 28765475 := bstep (se 1 (by rfl) ⟨21574106, by rfl⟩ : syracuseStep 28765475 = 43148213) B43148213
theorem B5680489 : Blo 1496068 5680489 := bstep (se 2 (by rfl) ⟨2130183, by rfl⟩ : syracuseStep 5680489 = 4260367) B4260367
theorem B2559451 : Blo 1496068 2559451 := bstep (se 1 (by rfl) ⟨1919588, by rfl⟩ : syracuseStep 2559451 = 3839177) B3839177
theorem B2526727 : Blo 1496068 2526727 := bstep (se 1 (by rfl) ⟨1895045, by rfl⟩ : syracuseStep 2526727 = 3790091) B3790091
theorem B3370535 : Blo 1496068 3370535 := bstep (se 1 (by rfl) ⟨2527901, by rfl⟩ : syracuseStep 3370535 = 5055803) B5055803
theorem B5680763 : Blo 1496068 5680763 := bstep (se 1 (by rfl) ⟨4260572, by rfl⟩ : syracuseStep 5680763 = 8521145) B8521145
theorem B14585483 : Blo 1496068 14585483 := bstep (se 1 (by rfl) ⟨10939112, by rfl⟩ : syracuseStep 14585483 = 21878225) B21878225
theorem B6393491 : Blo 1496068 6393491 := bstep (se 1 (by rfl) ⟨4795118, by rfl⟩ : syracuseStep 6393491 = 9590237) B9590237
theorem B6393593 : Blo 1496068 6393593 := bstep (se 2 (by rfl) ⟨2397597, by rfl⟩ : syracuseStep 6393593 = 4795195) B4795195
theorem B8523629 : Blo 1496068 8523629 := bstep (se 3 (by rfl) ⟨1598180, by rfl⟩ : syracuseStep 8523629 = 3196361) B3196361
theorem B19181447 : Blo 1496068 19181447 := bstep (se 1 (by rfl) ⟨14386085, by rfl⟩ : syracuseStep 19181447 = 28772171) B28772171
theorem B5050295 : Blo 1496068 5050295 := bstep (se 1 (by rfl) ⟨3787721, by rfl⟩ : syracuseStep 5050295 = 7575443) B7575443
theorem B2527159 : Blo 1496068 2527159 := bstep (se 1 (by rfl) ⟨1895369, by rfl⟩ : syracuseStep 2527159 = 3790739) B3790739
theorem B21573647 : Blo 1496068 21573647 := bstep (se 1 (by rfl) ⟨16180235, by rfl⟩ : syracuseStep 21573647 = 32360471) B32360471
theorem B1683535 : Blo 1496068 1683535 := bstep (se 1 (by rfl) ⟨1262651, by rfl⟩ : syracuseStep 1683535 = 2525303) B2525303
theorem B1708111 : Blo 1496068 1708111 := bstep (se 1 (by rfl) ⟨1281083, by rfl⟩ : syracuseStep 1708111 = 2562167) B2562167
theorem B2527355 : Blo 1496068 2527355 := bstep (se 1 (by rfl) ⟨1895516, by rfl⟩ : syracuseStep 2527355 = 3791033) B3791033
theorem B4796759 : Blo 1496068 4796759 := bstep (se 1 (by rfl) ⟨3597569, by rfl⟩ : syracuseStep 4796759 = 7195139) B7195139
theorem B6394241 : Blo 1496068 6394241 := bstep (se 2 (by rfl) ⟨2397840, by rfl⟩ : syracuseStep 6394241 = 4795681) B4795681
theorem B1683931 : Blo 1496068 1683931 := bstep (se 1 (by rfl) ⟨1262948, by rfl⟩ : syracuseStep 1683931 = 2525897) B2525897
theorem B5050889 : Blo 1496068 5050889 := bstep (se 2 (by rfl) ⟨1894083, by rfl⟩ : syracuseStep 5050889 = 3788167) B3788167
theorem B2527753 : Blo 1496068 2527753 := bstep (se 2 (by rfl) ⟨947907, by rfl⟩ : syracuseStep 2527753 = 1895815) B1895815
theorem B12956183 : Blo 1496068 12956183 := bstep (se 1 (by rfl) ⟨9717137, by rfl⟩ : syracuseStep 12956183 = 19434275) B19434275
theorem B2429563 : Blo 1496068 2429563 := bstep (se 1 (by rfl) ⟨1822172, by rfl⟩ : syracuseStep 2429563 = 3644345) B3644345
theorem B2527915 : Blo 1496068 2527915 := bstep (se 1 (by rfl) ⟨1895936, by rfl⟩ : syracuseStep 2527915 = 3791873) B3791873
theorem B11375315 : Blo 1496068 11375315 := bstep (se 1 (by rfl) ⟨8531486, by rfl⟩ : syracuseStep 11375315 = 17062973) B17062973
theorem B7582571 : Blo 1496068 7582571 := bstep (se 1 (by rfl) ⟨5686928, by rfl⟩ : syracuseStep 7582571 = 11373857) B11373857
theorem B4928417 : Blo 1496068 4928417 := bstep (se 2 (by rfl) ⟨1848156, by rfl⟩ : syracuseStep 4928417 = 3696313) B3696313
theorem B19174319 : Blo 1496068 19174319 := bstep (se 1 (by rfl) ⟨14380739, by rfl⟩ : syracuseStep 19174319 = 28761479) B28761479
theorem B1684399 : Blo 1496068 1684399 := bstep (se 1 (by rfl) ⟨1263299, by rfl⟩ : syracuseStep 1684399 = 2526599) B2526599
theorem B4862983 : Blo 1496068 4862983 := bstep (se 1 (by rfl) ⟨3647237, by rfl⟩ : syracuseStep 4862983 = 7294475) B7294475
theorem B1496103 : Blo 1496068 1496103 := bstep (se 1 (by rfl) ⟨1122077, by rfl⟩ : syracuseStep 1496103 = 2244155) B2244155
theorem B1496143 : Blo 1496068 1496143 := bstep (se 1 (by rfl) ⟨1122107, by rfl⟩ : syracuseStep 1496143 = 2244215) B2244215
theorem B1496159 : Blo 1496068 1496159 := bstep (se 1 (by rfl) ⟨1122119, by rfl⟩ : syracuseStep 1496159 = 2244239) B2244239
theorem B1496187 : Blo 1496068 1496187 := bstep (se 1 (by rfl) ⟨1122140, by rfl⟩ : syracuseStep 1496187 = 2244281) B2244281
theorem B1496239 : Blo 1496068 1496239 := bstep (se 1 (by rfl) ⟨1122179, by rfl⟩ : syracuseStep 1496239 = 2244359) B2244359
theorem B1496263 : Blo 1496068 1496263 := bstep (se 1 (by rfl) ⟨1122197, by rfl⟩ : syracuseStep 1496263 = 2244395) B2244395
theorem B1496283 : Blo 1496068 1496283 := bstep (se 1 (by rfl) ⟨1122212, by rfl⟩ : syracuseStep 1496283 = 2244425) B2244425
theorem B1496359 : Blo 1496068 1496359 := bstep (se 1 (by rfl) ⟨1122269, by rfl⟩ : syracuseStep 1496359 = 2244539) B2244539
theorem B1496399 : Blo 1496068 1496399 := bstep (se 1 (by rfl) ⟨1122299, by rfl⟩ : syracuseStep 1496399 = 2244599) B2244599
theorem B1496415 : Blo 1496068 1496415 := bstep (se 1 (by rfl) ⟨1122311, by rfl⟩ : syracuseStep 1496415 = 2244623) B2244623
theorem B1684831 : Blo 1496068 1684831 := bstep (se 1 (by rfl) ⟨1263623, by rfl⟩ : syracuseStep 1684831 = 2527247) B2527247
theorem B5051753 : Blo 1496068 5051753 := bstep (se 2 (by rfl) ⟨1894407, by rfl⟩ : syracuseStep 5051753 = 3788815) B3788815
theorem B1496443 : Blo 1496068 1496443 := bstep (se 1 (by rfl) ⟨1122332, by rfl⟩ : syracuseStep 1496443 = 2244665) B2244665
theorem B9598333 : Blo 1496068 9598333 := bstep (se 3 (by rfl) ⟨1799687, by rfl⟩ : syracuseStep 9598333 = 3599375) B3599375
theorem B3790223 : Blo 1496068 3790223 := bstep (se 1 (by rfl) ⟨2842667, by rfl⟩ : syracuseStep 3790223 = 5685335) B5685335
theorem B7574957 : Blo 1496068 7574957 := bstep (se 3 (by rfl) ⟨1420304, by rfl⟩ : syracuseStep 7574957 = 2840609) B2840609
theorem B1496495 : Blo 1496068 1496495 := bstep (se 1 (by rfl) ⟨1122371, by rfl⟩ : syracuseStep 1496495 = 2244743) B2244743
theorem B1496519 : Blo 1496068 1496519 := bstep (se 1 (by rfl) ⟨1122389, by rfl⟩ : syracuseStep 1496519 = 2244779) B2244779
theorem B49903057 : Blo 1496068 49903057 := bstep (se 2 (by rfl) ⟨18713646, by rfl⟩ : syracuseStep 49903057 = 37427293) B37427293
theorem B1496539 : Blo 1496068 1496539 := bstep (se 1 (by rfl) ⟨1122404, by rfl⟩ : syracuseStep 1496539 = 2244809) B2244809
theorem B7583219 : Blo 1496068 7583219 := bstep (se 1 (by rfl) ⟨5687414, by rfl⟩ : syracuseStep 7583219 = 11374829) B11374829
theorem B1496615 : Blo 1496068 1496615 := bstep (se 1 (by rfl) ⟨1122461, by rfl⟩ : syracuseStep 1496615 = 2244923) B2244923
theorem B1496655 : Blo 1496068 1496655 := bstep (se 1 (by rfl) ⟨1122491, by rfl⟩ : syracuseStep 1496655 = 2244983) B2244983
theorem B1496671 : Blo 1496068 1496671 := bstep (se 1 (by rfl) ⟨1122503, by rfl⟩ : syracuseStep 1496671 = 2245007) B2245007
theorem B1496699 : Blo 1496068 1496699 := bstep (se 1 (by rfl) ⟨1122524, by rfl⟩ : syracuseStep 1496699 = 2245049) B2245049
theorem B4798091 : Blo 1496068 4798091 := bstep (se 1 (by rfl) ⟨3598568, by rfl⟩ : syracuseStep 4798091 = 7197137) B7197137
theorem B1496751 : Blo 1496068 1496751 := bstep (se 1 (by rfl) ⟨1122563, by rfl⟩ : syracuseStep 1496751 = 2245127) B2245127
theorem B1496775 : Blo 1496068 1496775 := bstep (se 1 (by rfl) ⟨1122581, by rfl⟩ : syracuseStep 1496775 = 2245163) B2245163
theorem B1685191 : Blo 1496068 1685191 := bstep (se 1 (by rfl) ⟨1263893, by rfl⟩ : syracuseStep 1685191 = 2527787) B2527787
theorem B2840275 : Blo 1496068 2840275 := bstep (se 1 (by rfl) ⟨2130206, by rfl⟩ : syracuseStep 2840275 = 4260413) B4260413
theorem B3790547 : Blo 1496068 3790547 := bstep (se 1 (by rfl) ⟨2842910, by rfl⟩ : syracuseStep 3790547 = 5685821) B5685821
theorem B1496795 : Blo 1496068 1496795 := bstep (se 1 (by rfl) ⟨1122596, by rfl⟩ : syracuseStep 1496795 = 2245193) B2245193
theorem B2397943 : Blo 1496068 2397943 := bstep (se 1 (by rfl) ⟨1798457, by rfl⟩ : syracuseStep 2397943 = 3596915) B3596915
theorem B1496871 : Blo 1496068 1496871 := bstep (se 1 (by rfl) ⟨1122653, by rfl⟩ : syracuseStep 1496871 = 2245307) B2245307
theorem B40498987 : Blo 1496068 40498987 := bstep (se 1 (by rfl) ⟨30374240, by rfl⟩ : syracuseStep 40498987 = 60748481) B60748481
theorem B1496911 : Blo 1496068 1496911 := bstep (se 1 (by rfl) ⟨1122683, by rfl⟩ : syracuseStep 1496911 = 2245367) B2245367
theorem B1496927 : Blo 1496068 1496927 := bstep (se 1 (by rfl) ⟨1122695, by rfl⟩ : syracuseStep 1496927 = 2245391) B2245391
theorem B1496955 : Blo 1496068 1496955 := bstep (se 1 (by rfl) ⟨1122716, by rfl⟩ : syracuseStep 1496955 = 2245433) B2245433
theorem B1497007 : Blo 1496068 1497007 := bstep (se 1 (by rfl) ⟨1122755, by rfl⟩ : syracuseStep 1497007 = 2245511) B2245511
theorem B2840503 : Blo 1496068 2840503 := bstep (se 1 (by rfl) ⟨2130377, by rfl⟩ : syracuseStep 2840503 = 4260755) B4260755
theorem B5052347 : Blo 1496068 5052347 := bstep (se 1 (by rfl) ⟨3789260, by rfl⟩ : syracuseStep 5052347 = 7578521) B7578521
theorem B1497031 : Blo 1496068 1497031 := bstep (se 1 (by rfl) ⟨1122773, by rfl⟩ : syracuseStep 1497031 = 2245547) B2245547
theorem B1497051 : Blo 1496068 1497051 := bstep (se 1 (by rfl) ⟨1122788, by rfl⟩ : syracuseStep 1497051 = 2245577) B2245577
theorem B1497127 : Blo 1496068 1497127 := bstep (se 1 (by rfl) ⟨1122845, by rfl⟩ : syracuseStep 1497127 = 2245691) B2245691
theorem B1497167 : Blo 1496068 1497167 := bstep (se 1 (by rfl) ⟨1122875, by rfl⟩ : syracuseStep 1497167 = 2245751) B2245751
theorem B1497183 : Blo 1496068 1497183 := bstep (se 1 (by rfl) ⟨1122887, by rfl⟩ : syracuseStep 1497183 = 2245775) B2245775
theorem B1497211 : Blo 1496068 1497211 := bstep (se 1 (by rfl) ⟨1122908, by rfl⟩ : syracuseStep 1497211 = 2245817) B2245817
theorem B1497263 : Blo 1496068 1497263 := bstep (se 1 (by rfl) ⟨1122947, by rfl⟩ : syracuseStep 1497263 = 2245895) B2245895
theorem B1497287 : Blo 1496068 1497287 := bstep (se 1 (by rfl) ⟨1122965, by rfl⟩ : syracuseStep 1497287 = 2245931) B2245931
theorem B1497307 : Blo 1496068 1497307 := bstep (se 1 (by rfl) ⟨1122980, by rfl⟩ : syracuseStep 1497307 = 2245961) B2245961
theorem B7190795 : Blo 1496068 7190795 := bstep (se 1 (by rfl) ⟨5393096, by rfl⟩ : syracuseStep 7190795 = 10786193) B10786193
theorem B1497383 : Blo 1496068 1497383 := bstep (se 1 (by rfl) ⟨1123037, by rfl⟩ : syracuseStep 1497383 = 2246075) B2246075
theorem B1497423 : Blo 1496068 1497423 := bstep (se 1 (by rfl) ⟨1123067, by rfl⟩ : syracuseStep 1497423 = 2246135) B2246135
theorem B1497439 : Blo 1496068 1497439 := bstep (se 1 (by rfl) ⟨1123079, by rfl⟩ : syracuseStep 1497439 = 2246159) B2246159
theorem B1497467 : Blo 1496068 1497467 := bstep (se 1 (by rfl) ⟨1123100, by rfl⟩ : syracuseStep 1497467 = 2246201) B2246201
theorem B1497519 : Blo 1496068 1497519 := bstep (se 1 (by rfl) ⟨1123139, by rfl⟩ : syracuseStep 1497519 = 2246279) B2246279
theorem B1497543 : Blo 1496068 1497543 := bstep (se 1 (by rfl) ⟨1123157, by rfl⟩ : syracuseStep 1497543 = 2246315) B2246315
theorem B1497563 : Blo 1496068 1497563 := bstep (se 1 (by rfl) ⟨1123172, by rfl⟩ : syracuseStep 1497563 = 2246345) B2246345
theorem B2841095 : Blo 1496068 2841095 := bstep (se 1 (by rfl) ⟨2130821, by rfl⟩ : syracuseStep 2841095 = 4261643) B4261643
theorem B9108001 : Blo 1496068 9108001 := bstep (se 2 (by rfl) ⟨3415500, by rfl⟩ : syracuseStep 9108001 = 6831001) B6831001
theorem B1497639 : Blo 1496068 1497639 := bstep (se 1 (by rfl) ⟨1123229, by rfl⟩ : syracuseStep 1497639 = 2246459) B2246459
theorem B1497679 : Blo 1496068 1497679 := bstep (se 1 (by rfl) ⟨1123259, by rfl⟩ : syracuseStep 1497679 = 2246519) B2246519
theorem B1497695 : Blo 1496068 1497695 := bstep (se 1 (by rfl) ⟨1123271, by rfl⟩ : syracuseStep 1497695 = 2246543) B2246543
theorem B1497723 : Blo 1496068 1497723 := bstep (se 1 (by rfl) ⟨1123292, by rfl⟩ : syracuseStep 1497723 = 2246585) B2246585
theorem B1497775 : Blo 1496068 1497775 := bstep (se 1 (by rfl) ⟨1123331, by rfl⟩ : syracuseStep 1497775 = 2246663) B2246663
theorem B5118653 : Blo 1496068 5118653 := bstep (se 3 (by rfl) ⟨959747, by rfl⟩ : syracuseStep 5118653 = 1919495) B1919495
theorem B1497799 : Blo 1496068 1497799 := bstep (se 1 (by rfl) ⟨1123349, by rfl⟩ : syracuseStep 1497799 = 2246699) B2246699
theorem B14383817 : Blo 1496068 14383817 := bstep (se 2 (by rfl) ⟨5393931, by rfl⟩ : syracuseStep 14383817 = 10787863) B10787863
theorem B8526545 : Blo 1496068 8526545 := bstep (se 2 (by rfl) ⟨3197454, by rfl⟩ : syracuseStep 8526545 = 6394909) B6394909
theorem B1497819 : Blo 1496068 1497819 := bstep (se 1 (by rfl) ⟨1123364, by rfl⟩ : syracuseStep 1497819 = 2246729) B2246729
theorem B19192565 : Blo 1496068 19192565 := bstep (se 5 (by rfl) ⟨899651, by rfl⟩ : syracuseStep 19192565 = 1799303) B1799303
theorem B1497895 : Blo 1496068 1497895 := bstep (se 1 (by rfl) ⟨1123421, by rfl⟩ : syracuseStep 1497895 = 2246843) B2246843
theorem B1497935 : Blo 1496068 1497935 := bstep (se 1 (by rfl) ⟨1123451, by rfl⟩ : syracuseStep 1497935 = 2246903) B2246903
theorem B1497951 : Blo 1496068 1497951 := bstep (se 1 (by rfl) ⟨1123463, by rfl⟩ : syracuseStep 1497951 = 2246927) B2246927
theorem B3791711 : Blo 1496068 3791711 := bstep (se 1 (by rfl) ⟨2843783, by rfl⟩ : syracuseStep 3791711 = 5687567) B5687567
theorem B1497979 : Blo 1496068 1497979 := bstep (se 1 (by rfl) ⟨1123484, by rfl⟩ : syracuseStep 1497979 = 2246969) B2246969
theorem B1498031 : Blo 1496068 1498031 := bstep (se 1 (by rfl) ⟨1123523, by rfl⟩ : syracuseStep 1498031 = 2247047) B2247047
theorem B1498055 : Blo 1496068 1498055 := bstep (se 1 (by rfl) ⟨1123541, by rfl⟩ : syracuseStep 1498055 = 2247083) B2247083
theorem B7576577 : Blo 1496068 7576577 := bstep (se 2 (by rfl) ⟨2841216, by rfl⟩ : syracuseStep 7576577 = 5682433) B5682433
theorem B5118983 : Blo 1496068 5118983 := bstep (se 1 (by rfl) ⟨3839237, by rfl⟩ : syracuseStep 5118983 = 7678475) B7678475
theorem B10796111 : Blo 1496068 10796111 := bstep (se 1 (by rfl) ⟨8097083, by rfl⟩ : syracuseStep 10796111 = 16194167) B16194167
theorem B5684377 : Blo 1496068 5684377 := bstep (se 2 (by rfl) ⟨2131641, by rfl⟩ : syracuseStep 5684377 = 4263283) B4263283
theorem B11517221 : Blo 1496068 11517221 := bstep (se 4 (by rfl) ⟨1079739, by rfl⟩ : syracuseStep 11517221 = 2159479) B2159479
theorem B2841961 : Blo 1496068 2841961 := bstep (se 2 (by rfl) ⟨1065735, by rfl⟩ : syracuseStep 2841961 = 2131471) B2131471
theorem B16194941 : Blo 1496068 16194941 := bstep (se 3 (by rfl) ⟨3036551, by rfl⟩ : syracuseStep 16194941 = 6073103) B6073103
theorem B3366287 : Blo 1496068 3366287 := bstep (se 1 (by rfl) ⟨2524715, by rfl⟩ : syracuseStep 3366287 = 5049431) B5049431
theorem B5684681 : Blo 1496068 5684681 := bstep (se 2 (by rfl) ⟨2131755, by rfl⟩ : syracuseStep 5684681 = 4263511) B4263511
theorem B30711257 : Blo 1496068 30711257 := bstep (se 2 (by rfl) ⟨11516721, by rfl⟩ : syracuseStep 30711257 = 23033443) B23033443
theorem B2842121 : Blo 1496068 2842121 := bstep (se 2 (by rfl) ⟨1065795, by rfl⟩ : syracuseStep 2842121 = 2131591) B2131591
theorem B5054075 : Blo 1496068 5054075 := bstep (se 1 (by rfl) ⟨3790556, by rfl⟩ : syracuseStep 5054075 = 7581113) B7581113
theorem B3366611 : Blo 1496068 3366611 := bstep (se 1 (by rfl) ⟨2524958, by rfl⟩ : syracuseStep 3366611 = 5049917) B5049917
theorem B84188929 : Blo 1496068 84188929 := bstep (se 2 (by rfl) ⟨31570848, by rfl⟩ : syracuseStep 84188929 = 63141697) B63141697
theorem B5054237 : Blo 1496068 5054237 := bstep (se 3 (by rfl) ⟨947669, by rfl⟩ : syracuseStep 5054237 = 1895339) B1895339
theorem B7577387 : Blo 1496068 7577387 := bstep (se 1 (by rfl) ⟨5683040, by rfl⟩ : syracuseStep 7577387 = 11366081) B11366081
theorem B40992581 : Blo 1496068 40992581 := bstep (se 4 (by rfl) ⟨3843054, by rfl⟩ : syracuseStep 40992581 = 7686109) B7686109
theorem B16195463 : Blo 1496068 16195463 := bstep (se 1 (by rfl) ⟨12146597, by rfl⟩ : syracuseStep 16195463 = 24293195) B24293195
theorem B2244527 : Blo 1496068 2244527 := bstep (se 1 (by rfl) ⟨1683395, by rfl⟩ : syracuseStep 2244527 = 3366791) B3366791
theorem B5685167 : Blo 1496068 5685167 := bstep (se 1 (by rfl) ⟨4263875, by rfl⟩ : syracuseStep 5685167 = 8527751) B8527751
theorem B2244713 : Blo 1496068 2244713 := bstep (se 2 (by rfl) ⟨841767, by rfl⟩ : syracuseStep 2244713 = 1683535) B1683535
theorem B2277481 : Blo 1496068 2277481 := bstep (se 2 (by rfl) ⟨854055, by rfl⟩ : syracuseStep 2277481 = 1708111) B1708111
theorem B8642713 : Blo 1496068 8642713 := bstep (se 2 (by rfl) ⟨3241017, by rfl⟩ : syracuseStep 8642713 = 6482035) B6482035
theorem B3367241 : Blo 1496068 3367241 := bstep (se 2 (by rfl) ⟨1262715, by rfl⟩ : syracuseStep 3367241 = 2525431) B2525431
theorem B3367259 : Blo 1496068 3367259 := bstep (se 1 (by rfl) ⟨2525444, by rfl⟩ : syracuseStep 3367259 = 5050889) B5050889
theorem B2245031 : Blo 1496068 2245031 := bstep (se 1 (by rfl) ⟨1683773, by rfl⟩ : syracuseStep 2245031 = 3367547) B3367547
theorem B2245115 : Blo 1496068 2245115 := bstep (se 1 (by rfl) ⟨1683836, by rfl⟩ : syracuseStep 2245115 = 3367673) B3367673
theorem B5055047 : Blo 1496068 5055047 := bstep (se 1 (by rfl) ⟨3791285, by rfl⟩ : syracuseStep 5055047 = 7582571) B7582571
theorem B3285611 : Blo 1496068 3285611 := bstep (se 1 (by rfl) ⟨2464208, by rfl⟩ : syracuseStep 3285611 = 4928417) B4928417
theorem B2245241 : Blo 1496068 2245241 := bstep (se 2 (by rfl) ⟨841965, by rfl⟩ : syracuseStep 2245241 = 1683931) B1683931
theorem B9101969 : Blo 1496068 9101969 := bstep (se 2 (by rfl) ⟨3413238, by rfl⟩ : syracuseStep 9101969 = 6826477) B6826477
theorem B2245295 : Blo 1496068 2245295 := bstep (se 1 (by rfl) ⟨1683971, by rfl⟩ : syracuseStep 2245295 = 3367943) B3367943
theorem B2245343 : Blo 1496068 2245343 := bstep (se 1 (by rfl) ⟨1684007, by rfl⟩ : syracuseStep 2245343 = 3368015) B3368015
theorem B32793497 : Blo 1496068 32793497 := bstep (se 2 (by rfl) ⟨12297561, by rfl⟩ : syracuseStep 32793497 = 24595123) B24595123
theorem B3367835 : Blo 1496068 3367835 := bstep (se 1 (by rfl) ⟨2525876, by rfl⟩ : syracuseStep 3367835 = 5051753) B5051753
theorem B1541071 : Blo 1496068 1541071 := bstep (se 1 (by rfl) ⟨1155803, by rfl⟩ : syracuseStep 1541071 = 2311607) B2311607
theorem B2245607 : Blo 1496068 2245607 := bstep (se 1 (by rfl) ⟨1684205, by rfl⟩ : syracuseStep 2245607 = 3368411) B3368411
theorem B5055479 : Blo 1496068 5055479 := bstep (se 1 (by rfl) ⟨3791609, by rfl⟩ : syracuseStep 5055479 = 7583219) B7583219
theorem B3368033 : Blo 1496068 3368033 := bstep (se 2 (by rfl) ⟨1263012, by rfl⟩ : syracuseStep 3368033 = 2526025) B2526025
theorem B3196027 : Blo 1496068 3196027 := bstep (se 1 (by rfl) ⟨2397020, by rfl⟩ : syracuseStep 3196027 = 4794041) B4794041
theorem B2245865 : Blo 1496068 2245865 := bstep (se 2 (by rfl) ⟨842199, by rfl⟩ : syracuseStep 2245865 = 1684399) B1684399
theorem B2245919 : Blo 1496068 2245919 := bstep (se 1 (by rfl) ⟨1684439, by rfl⟩ : syracuseStep 2245919 = 3368879) B3368879
theorem B12789029 : Blo 1496068 12789029 := bstep (se 4 (by rfl) ⟨1198971, by rfl⟩ : syracuseStep 12789029 = 2397943) B2397943
theorem B3196199 : Blo 1496068 3196199 := bstep (se 1 (by rfl) ⟨2397149, by rfl⟩ : syracuseStep 3196199 = 4794299) B4794299
theorem B3368231 : Blo 1496068 3368231 := bstep (se 1 (by rfl) ⟨2526173, by rfl⟩ : syracuseStep 3368231 = 5052347) B5052347
theorem B2246087 : Blo 1496068 2246087 := bstep (se 1 (by rfl) ⟨1684565, by rfl⟩ : syracuseStep 2246087 = 3369131) B3369131
theorem B4793863 : Blo 1496068 4793863 := bstep (se 1 (by rfl) ⟨3595397, by rfl⟩ : syracuseStep 4793863 = 7190795) B7190795
theorem B7579169 : Blo 1496068 7579169 := bstep (se 2 (by rfl) ⟨2842188, by rfl⟩ : syracuseStep 7579169 = 5684377) B5684377
theorem B3368609 : Blo 1496068 3368609 := bstep (se 2 (by rfl) ⟨1263228, by rfl⟩ : syracuseStep 3368609 = 2526457) B2526457
theorem B2246441 : Blo 1496068 2246441 := bstep (se 2 (by rfl) ⟨842415, by rfl⟩ : syracuseStep 2246441 = 1684831) B1684831
theorem B2246447 : Blo 1496068 2246447 := bstep (se 1 (by rfl) ⟨1684835, by rfl⟩ : syracuseStep 2246447 = 3369671) B3369671
theorem B13649741 : Blo 1496068 13649741 := bstep (se 3 (by rfl) ⟨2559326, by rfl⟩ : syracuseStep 13649741 = 5118653) B5118653
theorem B12797777 : Blo 1496068 12797777 := bstep (se 2 (by rfl) ⟨4799166, by rfl⟩ : syracuseStep 12797777 = 9598333) B9598333
theorem B18712451 : Blo 1496068 18712451 := bstep (se 1 (by rfl) ⟨14034338, by rfl⟩ : syracuseStep 18712451 = 28068677) B28068677
theorem B66537409 : Blo 1496068 66537409 := bstep (se 2 (by rfl) ⟨24951528, by rfl⟩ : syracuseStep 66537409 = 49903057) B49903057
theorem B3368969 : Blo 1496068 3368969 := bstep (se 2 (by rfl) ⟨1263363, by rfl⟩ : syracuseStep 3368969 = 2526727) B2526727
theorem B7678147 : Blo 1496068 7678147 := bstep (se 1 (by rfl) ⟨5758610, by rfl⟩ : syracuseStep 7678147 = 11517221) B11517221
theorem B2246921 : Blo 1496068 2246921 := bstep (se 2 (by rfl) ⟨842595, by rfl⟩ : syracuseStep 2246921 = 1685191) B1685191
theorem B3787033 : Blo 1496068 3787033 := bstep (se 2 (by rfl) ⟨1420137, by rfl⟩ : syracuseStep 3787033 = 2840275) B2840275
theorem B20474171 : Blo 1496068 20474171 := bstep (se 1 (by rfl) ⟨15355628, by rfl⟩ : syracuseStep 20474171 = 30711257) B30711257
theorem B1894747 : Blo 1496068 1894747 := bstep (se 1 (by rfl) ⟨1421060, by rfl⟩ : syracuseStep 1894747 = 2842121) B2842121
theorem B2247023 : Blo 1496068 2247023 := bstep (se 1 (by rfl) ⟨1685267, by rfl⟩ : syracuseStep 2247023 = 3370535) B3370535
theorem B3787175 : Blo 1496068 3787175 := bstep (se 1 (by rfl) ⟨2840381, by rfl⟩ : syracuseStep 3787175 = 5680763) B5680763
theorem B3369383 : Blo 1496068 3369383 := bstep (se 1 (by rfl) ⟨2527037, by rfl⟩ : syracuseStep 3369383 = 5054075) B5054075
theorem B4262327 : Blo 1496068 4262327 := bstep (se 1 (by rfl) ⟨3196745, by rfl⟩ : syracuseStep 4262327 = 6393491) B6393491
theorem B4262395 : Blo 1496068 4262395 := bstep (se 1 (by rfl) ⟨3196796, by rfl⟩ : syracuseStep 4262395 = 6393593) B6393593
theorem B3369491 : Blo 1496068 3369491 := bstep (se 1 (by rfl) ⟨2527118, by rfl⟩ : syracuseStep 3369491 = 5054237) B5054237
theorem B3787337 : Blo 1496068 3787337 := bstep (se 2 (by rfl) ⟨1420251, by rfl⟩ : syracuseStep 3787337 = 2840503) B2840503
theorem B3369545 : Blo 1496068 3369545 := bstep (se 2 (by rfl) ⟨1263579, by rfl⟩ : syracuseStep 3369545 = 2527159) B2527159
theorem B3197839 : Blo 1496068 3197839 := bstep (se 1 (by rfl) ⟨2398379, by rfl⟩ : syracuseStep 3197839 = 4796759) B4796759
theorem B3369959 : Blo 1496068 3369959 := bstep (se 1 (by rfl) ⟨2527469, by rfl⟩ : syracuseStep 3369959 = 5054939) B5054939
theorem B8637455 : Blo 1496068 8637455 := bstep (se 1 (by rfl) ⟨6478091, by rfl⟩ : syracuseStep 8637455 = 12956183) B12956183
theorem B4263101 : Blo 1496068 4263101 := bstep (se 3 (by rfl) ⟨799331, by rfl⟩ : syracuseStep 4263101 = 1598663) B1598663
theorem B11365595 : Blo 1496068 11365595 := bstep (se 1 (by rfl) ⟨8524196, by rfl⟩ : syracuseStep 11365595 = 17048393) B17048393
theorem B12782879 : Blo 1496068 12782879 := bstep (se 1 (by rfl) ⟨9587159, by rfl⟩ : syracuseStep 12782879 = 19174319) B19174319
theorem B5123359 : Blo 1496068 5123359 := bstep (se 1 (by rfl) ⟨3842519, by rfl⟩ : syracuseStep 5123359 = 7685039) B7685039
theorem B1895719 : Blo 1496068 1895719 := bstep (se 1 (by rfl) ⟨1421789, by rfl⟩ : syracuseStep 1895719 = 2843579) B2843579
theorem B3370337 : Blo 1496068 3370337 := bstep (se 2 (by rfl) ⟨1263876, by rfl⟩ : syracuseStep 3370337 = 2527753) B2527753
theorem B12144001 : Blo 1496068 12144001 := bstep (se 2 (by rfl) ⟨4554000, by rfl⟩ : syracuseStep 12144001 = 9108001) B9108001
theorem B3370427 : Blo 1496068 3370427 := bstep (se 1 (by rfl) ⟨2527820, by rfl⟩ : syracuseStep 3370427 = 5055641) B5055641
theorem B4615639 : Blo 1496068 4615639 := bstep (se 1 (by rfl) ⟨3461729, by rfl⟩ : syracuseStep 4615639 = 6923459) B6923459
theorem B3239417 : Blo 1496068 3239417 := bstep (se 2 (by rfl) ⟨1214781, by rfl⟩ : syracuseStep 3239417 = 2429563) B2429563
theorem B3370553 : Blo 1496068 3370553 := bstep (se 2 (by rfl) ⟨1263957, by rfl⟩ : syracuseStep 3370553 = 2527915) B2527915
theorem B2526815 : Blo 1496068 2526815 := bstep (se 1 (by rfl) ⟨1895111, by rfl⟩ : syracuseStep 2526815 = 3790223) B3790223
theorem B5049971 : Blo 1496068 5049971 := bstep (se 1 (by rfl) ⟨3787478, by rfl⟩ : syracuseStep 5049971 = 7574957) B7574957
theorem B2698913 : Blo 1496068 2698913 := bstep (se 2 (by rfl) ⟨1012092, by rfl⟩ : syracuseStep 2698913 = 2024185) B2024185
theorem B17051309 : Blo 1496068 17051309 := bstep (se 3 (by rfl) ⟨3197120, by rfl⟩ : syracuseStep 17051309 = 6394241) B6394241
theorem B3198727 : Blo 1496068 3198727 := bstep (se 1 (by rfl) ⟨2399045, by rfl⟩ : syracuseStep 3198727 = 4798091) B4798091
theorem B1683247 : Blo 1496068 1683247 := bstep (se 1 (by rfl) ⟨1262435, by rfl⟩ : syracuseStep 1683247 = 2524871) B2524871
theorem B2527031 : Blo 1496068 2527031 := bstep (se 1 (by rfl) ⟨1895273, by rfl⟩ : syracuseStep 2527031 = 3790547) B3790547
theorem B8204105 : Blo 1496068 8204105 := bstep (se 2 (by rfl) ⟨3076539, by rfl⟩ : syracuseStep 8204105 = 6153079) B6153079
theorem B5050241 : Blo 1496068 5050241 := bstep (se 2 (by rfl) ⟨1893840, by rfl⟩ : syracuseStep 5050241 = 3787681) B3787681
theorem B1683355 : Blo 1496068 1683355 := bstep (se 1 (by rfl) ⟨1262516, by rfl⟩ : syracuseStep 1683355 = 2525033) B2525033
theorem B4796425 : Blo 1496068 4796425 := bstep (se 2 (by rfl) ⟨1798659, by rfl⟩ : syracuseStep 4796425 = 3597319) B3597319
theorem B6483977 : Blo 1496068 6483977 := bstep (se 2 (by rfl) ⟨2431491, by rfl⟩ : syracuseStep 6483977 = 4862983) B4862983
theorem B10793027 : Blo 1496068 10793027 := bstep (se 1 (by rfl) ⟨8094770, by rfl⟩ : syracuseStep 10793027 = 16189541) B16189541
theorem B20484353 : Blo 1496068 20484353 := bstep (se 2 (by rfl) ⟨7681632, by rfl⟩ : syracuseStep 20484353 = 15363265) B15363265
theorem B1683751 : Blo 1496068 1683751 := bstep (se 1 (by rfl) ⟨1262813, by rfl⟩ : syracuseStep 1683751 = 2525627) B2525627
theorem B1683823 : Blo 1496068 1683823 := bstep (se 1 (by rfl) ⟨1262867, by rfl⟩ : syracuseStep 1683823 = 2525735) B2525735
theorem B9589211 : Blo 1496068 9589211 := bstep (se 1 (by rfl) ⟨7191908, by rfl⟩ : syracuseStep 9589211 = 14383817) B14383817
theorem B7573985 : Blo 1496068 7573985 := bstep (se 2 (by rfl) ⟨2840244, by rfl⟩ : syracuseStep 7573985 = 5680489) B5680489
theorem B3789281 : Blo 1496068 3789281 := bstep (se 2 (by rfl) ⟨1420980, by rfl⟩ : syracuseStep 3789281 = 2841961) B2841961
theorem B2527807 : Blo 1496068 2527807 := bstep (se 1 (by rfl) ⟨1895855, by rfl⟩ : syracuseStep 2527807 = 3791711) B3791711
theorem B5681735 : Blo 1496068 5681735 := bstep (se 1 (by rfl) ⟨4261301, by rfl⟩ : syracuseStep 5681735 = 8522603) B8522603
theorem B1684039 : Blo 1496068 1684039 := bstep (se 1 (by rfl) ⟨1263029, by rfl⟩ : syracuseStep 1684039 = 2526059) B2526059
theorem B3412601 : Blo 1496068 3412601 := bstep (se 2 (by rfl) ⟨1279725, by rfl⟩ : syracuseStep 3412601 = 2559451) B2559451
theorem B5051051 : Blo 1496068 5051051 := bstep (se 1 (by rfl) ⟨3788288, by rfl⟩ : syracuseStep 5051051 = 7576577) B7576577
theorem B3412655 : Blo 1496068 3412655 := bstep (se 1 (by rfl) ⟨2559491, by rfl⟩ : syracuseStep 3412655 = 5118983) B5118983
theorem B7197407 : Blo 1496068 7197407 := bstep (se 1 (by rfl) ⟨5398055, by rfl⟩ : syracuseStep 7197407 = 10796111) B10796111
theorem B1798967 : Blo 1496068 1798967 := bstep (se 1 (by rfl) ⟨1349225, by rfl⟩ : syracuseStep 1798967 = 2698451) B2698451
theorem B3789787 : Blo 1496068 3789787 := bstep (se 1 (by rfl) ⟨2842340, by rfl⟩ : syracuseStep 3789787 = 5684681) B5684681
theorem B112251905 : Blo 1496068 112251905 := bstep (se 2 (by rfl) ⟨42094464, by rfl⟩ : syracuseStep 112251905 = 84188929) B84188929
theorem B53998649 : Blo 1496068 53998649 := bstep (se 2 (by rfl) ⟨20249493, by rfl⟩ : syracuseStep 53998649 = 40498987) B40498987
theorem B7189661 : Blo 1496068 7189661 := bstep (se 3 (by rfl) ⟨1348061, by rfl⟩ : syracuseStep 7189661 = 2696123) B2696123
theorem B5051591 : Blo 1496068 5051591 := bstep (se 1 (by rfl) ⟨3788693, by rfl⟩ : syracuseStep 5051591 = 7577387) B7577387
theorem B5682419 : Blo 1496068 5682419 := bstep (se 1 (by rfl) ⟨4261814, by rfl⟩ : syracuseStep 5682419 = 8523629) B8523629
theorem B1496351 : Blo 1496068 1496351 := bstep (se 1 (by rfl) ⟨1122263, by rfl⟩ : syracuseStep 1496351 = 2244527) B2244527
theorem B3790111 : Blo 1496068 3790111 := bstep (se 1 (by rfl) ⟨2842583, by rfl⟩ : syracuseStep 3790111 = 5685167) B5685167
theorem B1496411 : Blo 1496068 1496411 := bstep (se 1 (by rfl) ⟨1122308, by rfl⟩ : syracuseStep 1496411 = 2244617) B2244617
theorem B14382431 : Blo 1496068 14382431 := bstep (se 1 (by rfl) ⟨10786823, by rfl⟩ : syracuseStep 14382431 = 21573647) B21573647
theorem B4265311 : Blo 1496068 4265311 := bstep (se 1 (by rfl) ⟨3198983, by rfl⟩ : syracuseStep 4265311 = 6397967) B6397967
theorem B1496431 : Blo 1496068 1496431 := bstep (se 1 (by rfl) ⟨1122323, by rfl⟩ : syracuseStep 1496431 = 2244647) B2244647
theorem B5395835 : Blo 1496068 5395835 := bstep (se 1 (by rfl) ⟨4046876, by rfl⟩ : syracuseStep 5395835 = 8093753) B8093753
theorem B1496487 : Blo 1496068 1496487 := bstep (se 1 (by rfl) ⟨1122365, by rfl⟩ : syracuseStep 1496487 = 2244731) B2244731
theorem B1684903 : Blo 1496068 1684903 := bstep (se 1 (by rfl) ⟨1263677, by rfl⟩ : syracuseStep 1684903 = 2527355) B2527355
theorem B1496571 : Blo 1496068 1496571 := bstep (se 1 (by rfl) ⟨1122428, by rfl⟩ : syracuseStep 1496571 = 2244857) B2244857
theorem B1496639 : Blo 1496068 1496639 := bstep (se 1 (by rfl) ⟨1122479, by rfl⟩ : syracuseStep 1496639 = 2244959) B2244959
theorem B1496647 : Blo 1496068 1496647 := bstep (se 1 (by rfl) ⟨1122485, by rfl⟩ : syracuseStep 1496647 = 2244971) B2244971
theorem B17061515 : Blo 1496068 17061515 := bstep (se 1 (by rfl) ⟨12796136, by rfl⟩ : syracuseStep 17061515 = 25592273) B25592273
theorem B1496799 : Blo 1496068 1496799 := bstep (se 1 (by rfl) ⟨1122599, by rfl⟩ : syracuseStep 1496799 = 2245199) B2245199
theorem B1496879 : Blo 1496068 1496879 := bstep (se 1 (by rfl) ⟨1122659, by rfl⟩ : syracuseStep 1496879 = 2245319) B2245319
theorem B7583543 : Blo 1496068 7583543 := bstep (se 1 (by rfl) ⟨5687657, by rfl⟩ : syracuseStep 7583543 = 11375315) B11375315
theorem B1496987 : Blo 1496068 1496987 := bstep (se 1 (by rfl) ⟨1122740, by rfl⟩ : syracuseStep 1496987 = 2245481) B2245481
theorem B1497039 : Blo 1496068 1497039 := bstep (se 1 (by rfl) ⟨1122779, by rfl⟩ : syracuseStep 1497039 = 2245559) B2245559
theorem B1497063 : Blo 1496068 1497063 := bstep (se 1 (by rfl) ⟨1122797, by rfl⟩ : syracuseStep 1497063 = 2245595) B2245595
theorem B14391431 : Blo 1496068 14391431 := bstep (se 1 (by rfl) ⟨10793573, by rfl⟩ : syracuseStep 14391431 = 21587147) B21587147
theorem B1497375 : Blo 1496068 1497375 := bstep (se 1 (by rfl) ⟨1123031, by rfl⟩ : syracuseStep 1497375 = 2246063) B2246063
theorem B1497435 : Blo 1496068 1497435 := bstep (se 1 (by rfl) ⟨1123076, by rfl⟩ : syracuseStep 1497435 = 2246153) B2246153
theorem B3791195 : Blo 1496068 3791195 := bstep (se 1 (by rfl) ⟨2843396, by rfl⟩ : syracuseStep 3791195 = 5686793) B5686793
theorem B1497455 : Blo 1496068 1497455 := bstep (se 1 (by rfl) ⟨1123091, by rfl⟩ : syracuseStep 1497455 = 2246183) B2246183
theorem B1497511 : Blo 1496068 1497511 := bstep (se 1 (by rfl) ⟨1123133, by rfl⟩ : syracuseStep 1497511 = 2246267) B2246267
theorem B1497595 : Blo 1496068 1497595 := bstep (se 1 (by rfl) ⟨1123196, by rfl⟩ : syracuseStep 1497595 = 2246393) B2246393
theorem B1497663 : Blo 1496068 1497663 := bstep (se 1 (by rfl) ⟨1123247, by rfl⟩ : syracuseStep 1497663 = 2246495) B2246495
theorem B1497671 : Blo 1496068 1497671 := bstep (se 1 (by rfl) ⟨1123253, by rfl⟩ : syracuseStep 1497671 = 2246507) B2246507
theorem B5053103 : Blo 1496068 5053103 := bstep (se 1 (by rfl) ⟨3789827, by rfl⟩ : syracuseStep 5053103 = 7579655) B7579655
theorem B7576253 : Blo 1496068 7576253 := bstep (se 3 (by rfl) ⟨1420547, by rfl⟩ : syracuseStep 7576253 = 2841095) B2841095
theorem B2398943 : Blo 1496068 2398943 := bstep (se 1 (by rfl) ⟨1799207, by rfl⟩ : syracuseStep 2398943 = 3598415) B3598415
theorem B1497823 : Blo 1496068 1497823 := bstep (se 1 (by rfl) ⟨1123367, by rfl⟩ : syracuseStep 1497823 = 2246735) B2246735
theorem B1497903 : Blo 1496068 1497903 := bstep (se 1 (by rfl) ⟨1123427, by rfl⟩ : syracuseStep 1497903 = 2246855) B2246855
theorem B5397391 : Blo 1496068 5397391 := bstep (se 1 (by rfl) ⟨4048043, by rfl⟩ : syracuseStep 5397391 = 8096087) B8096087
theorem B1498011 : Blo 1496068 1498011 := bstep (se 1 (by rfl) ⟨1123508, by rfl⟩ : syracuseStep 1498011 = 2247017) B2247017
theorem B1498063 : Blo 1496068 1498063 := bstep (se 1 (by rfl) ⟨1123547, by rfl⟩ : syracuseStep 1498063 = 2247095) B2247095
theorem B5053427 : Blo 1496068 5053427 := bstep (se 1 (by rfl) ⟨3790070, by rfl⟩ : syracuseStep 5053427 = 7580141) B7580141
theorem B5684363 : Blo 1496068 5684363 := bstep (se 1 (by rfl) ⟨4263272, by rfl⟩ : syracuseStep 5684363 = 8526545) B8526545
theorem B12795043 : Blo 1496068 12795043 := bstep (se 1 (by rfl) ⟨9596282, by rfl⟩ : syracuseStep 12795043 = 19192565) B19192565
theorem B3366305 : Blo 1496068 3366305 := bstep (se 2 (by rfl) ⟨1262364, by rfl⟩ : syracuseStep 3366305 = 2524729) B2524729
theorem B5053967 : Blo 1496068 5053967 := bstep (se 1 (by rfl) ⟨3790475, by rfl⟩ : syracuseStep 5053967 = 7580951) B7580951
theorem B19176983 : Blo 1496068 19176983 := bstep (se 1 (by rfl) ⟨14382737, by rfl⟩ : syracuseStep 19176983 = 28765475) B28765475
theorem B10796627 : Blo 1496068 10796627 := bstep (se 1 (by rfl) ⟨8097470, by rfl⟩ : syracuseStep 10796627 = 16194941) B16194941
theorem B2244191 : Blo 1496068 2244191 := bstep (se 1 (by rfl) ⟨1683143, by rfl⟩ : syracuseStep 2244191 = 3366287) B3366287
theorem B9723655 : Blo 1496068 9723655 := bstep (se 1 (by rfl) ⟨7292741, by rfl⟩ : syracuseStep 9723655 = 14585483) B14585483
theorem B2244407 : Blo 1496068 2244407 := bstep (se 1 (by rfl) ⟨1683305, by rfl⟩ : syracuseStep 2244407 = 3366611) B3366611
theorem B3596089 : Blo 1496068 3596089 := bstep (se 2 (by rfl) ⟨1348533, by rfl⟩ : syracuseStep 3596089 = 2697067) B2697067
theorem B27328387 : Blo 1496068 27328387 := bstep (se 1 (by rfl) ⟨20496290, by rfl⟩ : syracuseStep 27328387 = 40992581) B40992581
theorem B12787631 : Blo 1496068 12787631 := bstep (se 1 (by rfl) ⟨9590723, by rfl⟩ : syracuseStep 12787631 = 19181447) B19181447
theorem B10796975 : Blo 1496068 10796975 := bstep (se 1 (by rfl) ⟨8097731, by rfl⟩ : syracuseStep 10796975 = 16195463) B16195463
theorem B3366863 : Blo 1496068 3366863 := bstep (se 1 (by rfl) ⟨2525147, by rfl⟩ : syracuseStep 3366863 = 5050295) B5050295
theorem B2244827 : Blo 1496068 2244827 := bstep (se 1 (by rfl) ⟨1683620, by rfl⟩ : syracuseStep 2244827 = 3367241) B3367241
theorem B2244839 : Blo 1496068 2244839 := bstep (se 1 (by rfl) ⟨1683629, by rfl⟩ : syracuseStep 2244839 = 3367259) B3367259
theorem B2245001 : Blo 1496068 2245001 := bstep (se 2 (by rfl) ⟨841875, by rfl⟩ : syracuseStep 2245001 = 1683751) B1683751
theorem B3367367 : Blo 1496068 3367367 := bstep (se 1 (by rfl) ⟨2525525, by rfl⟩ : syracuseStep 3367367 = 5051051) B5051051
theorem B2245097 : Blo 1496068 2245097 := bstep (se 2 (by rfl) ⟨841911, by rfl⟩ : syracuseStep 2245097 = 1683823) B1683823
theorem B2245223 : Blo 1496068 2245223 := bstep (se 1 (by rfl) ⟨1683917, by rfl⟩ : syracuseStep 2245223 = 3367835) B3367835
theorem B74834603 : Blo 1496068 74834603 := bstep (se 1 (by rfl) ⟨56125952, by rfl⟩ : syracuseStep 74834603 = 112251905) B112251905
theorem B54624941 : Blo 1496068 54624941 := bstep (se 3 (by rfl) ⟨10242176, by rfl⟩ : syracuseStep 54624941 = 20484353) B20484353
theorem B2245355 : Blo 1496068 2245355 := bstep (se 1 (by rfl) ⟨1684016, by rfl⟩ : syracuseStep 2245355 = 3368033) B3368033
theorem B2245385 : Blo 1496068 2245385 := bstep (se 2 (by rfl) ⟨842019, by rfl⟩ : syracuseStep 2245385 = 1684039) B1684039
theorem B4793107 : Blo 1496068 4793107 := bstep (se 1 (by rfl) ⟨3594830, by rfl⟩ : syracuseStep 4793107 = 7189661) B7189661
theorem B3367727 : Blo 1496068 3367727 := bstep (se 1 (by rfl) ⟨2525795, by rfl⟩ : syracuseStep 3367727 = 5051591) B5051591
theorem B2130799 : Blo 1496068 2130799 := bstep (se 1 (by rfl) ⟨1598099, by rfl⟩ : syracuseStep 2130799 = 3196199) B3196199
theorem B2245487 : Blo 1496068 2245487 := bstep (se 1 (by rfl) ⟨1684115, by rfl⟩ : syracuseStep 2245487 = 3368231) B3368231
theorem B3597223 : Blo 1496068 3597223 := bstep (se 1 (by rfl) ⟨2697917, by rfl⟩ : syracuseStep 3597223 = 5395835) B5395835
theorem B2245739 : Blo 1496068 2245739 := bstep (se 1 (by rfl) ⟨1684304, by rfl⟩ : syracuseStep 2245739 = 3368609) B3368609
theorem B5055695 : Blo 1496068 5055695 := bstep (se 1 (by rfl) ⟨3791771, by rfl⟩ : syracuseStep 5055695 = 7583543) B7583543
theorem B2245979 : Blo 1496068 2245979 := bstep (se 1 (by rfl) ⟨1684484, by rfl⟩ : syracuseStep 2245979 = 3368969) B3368969
theorem B9594287 : Blo 1496068 9594287 := bstep (se 1 (by rfl) ⟨7195715, by rfl⟩ : syracuseStep 9594287 = 14391431) B14391431
theorem B13649447 : Blo 1496068 13649447 := bstep (se 1 (by rfl) ⟨10237085, by rfl⟩ : syracuseStep 13649447 = 20474171) B20474171
theorem B2524783 : Blo 1496068 2524783 := bstep (se 1 (by rfl) ⟨1893587, by rfl⟩ : syracuseStep 2524783 = 3787175) B3787175
theorem B2246255 : Blo 1496068 2246255 := bstep (se 1 (by rfl) ⟨1684691, by rfl⟩ : syracuseStep 2246255 = 3369383) B3369383
theorem B2246327 : Blo 1496068 2246327 := bstep (se 1 (by rfl) ⟨1684745, by rfl⟩ : syracuseStep 2246327 = 3369491) B3369491
theorem B2524891 : Blo 1496068 2524891 := bstep (se 1 (by rfl) ⟨1893668, by rfl⟩ : syracuseStep 2524891 = 3787337) B3787337
theorem B2246363 : Blo 1496068 2246363 := bstep (se 1 (by rfl) ⟨1684772, by rfl⟩ : syracuseStep 2246363 = 3369545) B3369545
theorem B3368735 : Blo 1496068 3368735 := bstep (se 1 (by rfl) ⟨2526551, by rfl⟩ : syracuseStep 3368735 = 5053103) B5053103
theorem B5687081 : Blo 1496068 5687081 := bstep (se 2 (by rfl) ⟨2132655, by rfl⟩ : syracuseStep 5687081 = 4265311) B4265311
theorem B2246537 : Blo 1496068 2246537 := bstep (se 2 (by rfl) ⟨842451, by rfl⟩ : syracuseStep 2246537 = 1684903) B1684903
theorem B2246639 : Blo 1496068 2246639 := bstep (se 1 (by rfl) ⟨1684979, by rfl⟩ : syracuseStep 2246639 = 3369959) B3369959
theorem B3368951 : Blo 1496068 3368951 := bstep (se 1 (by rfl) ⟨2526713, by rfl⟩ : syracuseStep 3368951 = 5053427) B5053427
theorem B6391817 : Blo 1496068 6391817 := bstep (se 2 (by rfl) ⟨2396931, by rfl⟩ : syracuseStep 6391817 = 4793863) B4793863
theorem B8521919 : Blo 1496068 8521919 := bstep (se 1 (by rfl) ⟨6391439, by rfl⟩ : syracuseStep 8521919 = 12782879) B12782879
theorem B2246891 : Blo 1496068 2246891 := bstep (se 1 (by rfl) ⟨1685168, by rfl⟩ : syracuseStep 2246891 = 3370337) B3370337
theorem B2246951 : Blo 1496068 2246951 := bstep (se 1 (by rfl) ⟨1685213, by rfl⟩ : syracuseStep 2246951 = 3370427) B3370427
theorem B3369311 : Blo 1496068 3369311 := bstep (se 1 (by rfl) ⟨2526983, by rfl⟩ : syracuseStep 3369311 = 5053967) B5053967
theorem B2247035 : Blo 1496068 2247035 := bstep (se 1 (by rfl) ⟨1685276, by rfl⟩ : syracuseStep 2247035 = 3370553) B3370553
theorem B4794785 : Blo 1496068 4794785 := bstep (se 2 (by rfl) ⟨1798044, by rfl⟩ : syracuseStep 4794785 = 3596089) B3596089
theorem B8219045 : Blo 1496068 8219045 := bstep (se 4 (by rfl) ⟨770535, by rfl⟩ : syracuseStep 8219045 = 1541071) B1541071
theorem B7195351 : Blo 1496068 7195351 := bstep (se 1 (by rfl) ⟨5396513, by rfl⟩ : syracuseStep 7195351 = 10793027) B10793027
theorem B6392807 : Blo 1496068 6392807 := bstep (se 1 (by rfl) ⟨4794605, by rfl⟩ : syracuseStep 6392807 = 9589211) B9589211
theorem B5049323 : Blo 1496068 5049323 := bstep (se 1 (by rfl) ⟨3786992, by rfl⟩ : syracuseStep 5049323 = 7573985) B7573985
theorem B2526187 : Blo 1496068 2526187 := bstep (se 1 (by rfl) ⟨1894640, by rfl⟩ : syracuseStep 2526187 = 3789281) B3789281
theorem B5049377 : Blo 1496068 5049377 := bstep (se 2 (by rfl) ⟨1893516, by rfl⟩ : syracuseStep 5049377 = 3787033) B3787033
theorem B3787823 : Blo 1496068 3787823 := bstep (se 1 (by rfl) ⟨2840867, by rfl⟩ : syracuseStep 3787823 = 5681735) B5681735
theorem B3370031 : Blo 1496068 3370031 := bstep (se 1 (by rfl) ⟨2527523, by rfl⟩ : syracuseStep 3370031 = 5055047) B5055047
theorem B2190407 : Blo 1496068 2190407 := bstep (se 1 (by rfl) ⟨1642805, by rfl⟩ : syracuseStep 2190407 = 3285611) B3285611
theorem B2526329 : Blo 1496068 2526329 := bstep (se 2 (by rfl) ⟨947373, by rfl⟩ : syracuseStep 2526329 = 1894747) B1894747
theorem B3370319 : Blo 1496068 3370319 := bstep (se 1 (by rfl) ⟨2527739, by rfl⟩ : syracuseStep 3370319 = 5055479) B5055479
theorem B35999099 : Blo 1496068 35999099 := bstep (se 1 (by rfl) ⟨26999324, by rfl⟩ : syracuseStep 35999099 = 53998649) B53998649
theorem B3370409 : Blo 1496068 3370409 := bstep (se 2 (by rfl) ⟨1263903, by rfl⟩ : syracuseStep 3370409 = 2527807) B2527807
theorem B3788279 : Blo 1496068 3788279 := bstep (se 1 (by rfl) ⟨2841209, by rfl⟩ : syracuseStep 3788279 = 5682419) B5682419
theorem B9588287 : Blo 1496068 9588287 := bstep (se 1 (by rfl) ⟨7191215, by rfl⟩ : syracuseStep 9588287 = 14382431) B14382431
theorem B11374343 : Blo 1496068 11374343 := bstep (se 1 (by rfl) ⟨8530757, by rfl⟩ : syracuseStep 11374343 = 17061515) B17061515
theorem B4263785 : Blo 1496068 4263785 := bstep (se 2 (by rfl) ⟨1598919, by rfl⟩ : syracuseStep 4263785 = 3197839) B3197839
theorem B7196521 : Blo 1496068 7196521 := bstep (se 2 (by rfl) ⟨2698695, by rfl⟩ : syracuseStep 7196521 = 5397391) B5397391
theorem B8531851 : Blo 1496068 8531851 := bstep (se 1 (by rfl) ⟨6398888, by rfl⟩ : syracuseStep 8531851 = 12797777) B12797777
theorem B8638445 : Blo 1496068 8638445 := bstep (se 3 (by rfl) ⟨1619708, by rfl⟩ : syracuseStep 8638445 = 3239417) B3239417
theorem B17060057 : Blo 1496068 17060057 := bstep (se 2 (by rfl) ⟨6397521, by rfl⟩ : syracuseStep 17060057 = 12795043) B12795043
theorem B2527463 : Blo 1496068 2527463 := bstep (se 1 (by rfl) ⟨1895597, by rfl⟩ : syracuseStep 2527463 = 3791195) B3791195
theorem B2527625 : Blo 1496068 2527625 := bstep (se 2 (by rfl) ⟨947859, by rfl⟩ : syracuseStep 2527625 = 1895719) B1895719
theorem B5050835 : Blo 1496068 5050835 := bstep (se 1 (by rfl) ⟨3788126, by rfl⟩ : syracuseStep 5050835 = 7576253) B7576253
theorem B16192001 : Blo 1496068 16192001 := bstep (se 2 (by rfl) ⟨6072000, by rfl⟩ : syracuseStep 16192001 = 12144001) B12144001
theorem B3789575 : Blo 1496068 3789575 := bstep (se 1 (by rfl) ⟨2842181, by rfl⟩ : syracuseStep 3789575 = 5684363) B5684363
theorem B4797245 : Blo 1496068 4797245 := bstep (se 3 (by rfl) ⟨899483, by rfl⟩ : syracuseStep 4797245 = 1798967) B1798967
theorem B12964873 : Blo 1496068 12964873 := bstep (se 2 (by rfl) ⟨4861827, by rfl⟩ : syracuseStep 12964873 = 9723655) B9723655
theorem B4264969 : Blo 1496068 4264969 := bstep (se 2 (by rfl) ⟨1599363, by rfl⟩ : syracuseStep 4264969 = 3198727) B3198727
theorem B12784655 : Blo 1496068 12784655 := bstep (se 1 (by rfl) ⟨9588491, by rfl⟩ : syracuseStep 12784655 = 19176983) B19176983
theorem B7197751 : Blo 1496068 7197751 := bstep (se 1 (by rfl) ⟨5398313, by rfl⟩ : syracuseStep 7197751 = 10796627) B10796627
theorem B1496127 : Blo 1496068 1496127 := bstep (se 1 (by rfl) ⟨1122095, by rfl⟩ : syracuseStep 1496127 = 2244191) B2244191
theorem B1684543 : Blo 1496068 1684543 := bstep (se 1 (by rfl) ⟨1263407, by rfl⟩ : syracuseStep 1684543 = 2526815) B2526815
theorem B1799275 : Blo 1496068 1799275 := bstep (se 1 (by rfl) ⟨1349456, by rfl⟩ : syracuseStep 1799275 = 2698913) B2698913
theorem B11367539 : Blo 1496068 11367539 := bstep (se 1 (by rfl) ⟨8525654, by rfl⟩ : syracuseStep 11367539 = 17051309) B17051309
theorem B1496271 : Blo 1496068 1496271 := bstep (se 1 (by rfl) ⟨1122203, by rfl⟩ : syracuseStep 1496271 = 2244407) B2244407
theorem B1684687 : Blo 1496068 1684687 := bstep (se 1 (by rfl) ⟨1263515, by rfl⟩ : syracuseStep 1684687 = 2527031) B2527031
theorem B5469403 : Blo 1496068 5469403 := bstep (se 1 (by rfl) ⟨4102052, by rfl⟩ : syracuseStep 5469403 = 8204105) B8204105
theorem B88716545 : Blo 1496068 88716545 := bstep (se 2 (by rfl) ⟨33268704, by rfl⟩ : syracuseStep 88716545 = 66537409) B66537409
theorem B8525087 : Blo 1496068 8525087 := bstep (se 1 (by rfl) ⟨6393815, by rfl⟩ : syracuseStep 8525087 = 12787631) B12787631
theorem B7197983 : Blo 1496068 7197983 := bstep (se 1 (by rfl) ⟨5398487, by rfl⟩ : syracuseStep 7197983 = 10796975) B10796975
theorem B4322651 : Blo 1496068 4322651 := bstep (se 1 (by rfl) ⟨3241988, by rfl⟩ : syracuseStep 4322651 = 6483977) B6483977
theorem B6395233 : Blo 1496068 6395233 := bstep (se 2 (by rfl) ⟨2398212, by rfl⟩ : syracuseStep 6395233 = 4796425) B4796425
theorem B1496475 : Blo 1496068 1496475 := bstep (se 1 (by rfl) ⟨1122356, by rfl⟩ : syracuseStep 1496475 = 2244713) B2244713
theorem B3036641 : Blo 1496068 3036641 := bstep (se 2 (by rfl) ⟨1138740, by rfl⟩ : syracuseStep 3036641 = 2277481) B2277481
theorem B11523617 : Blo 1496068 11523617 := bstep (se 2 (by rfl) ⟨4321356, by rfl⟩ : syracuseStep 11523617 = 8642713) B8642713
theorem B10237529 : Blo 1496068 10237529 := bstep (se 2 (by rfl) ⟨3839073, by rfl⟩ : syracuseStep 10237529 = 7678147) B7678147
theorem B1496687 : Blo 1496068 1496687 := bstep (se 1 (by rfl) ⟨1122515, by rfl⟩ : syracuseStep 1496687 = 2245031) B2245031
theorem B1496743 : Blo 1496068 1496743 := bstep (se 1 (by rfl) ⟨1122557, by rfl⟩ : syracuseStep 1496743 = 2245115) B2245115
theorem B2275067 : Blo 1496068 2275067 := bstep (se 1 (by rfl) ⟨1706300, by rfl⟩ : syracuseStep 2275067 = 3412601) B3412601
theorem B1496827 : Blo 1496068 1496827 := bstep (se 1 (by rfl) ⟨1122620, by rfl⟩ : syracuseStep 1496827 = 2245241) B2245241
theorem B6067979 : Blo 1496068 6067979 := bstep (se 1 (by rfl) ⟨4550984, by rfl⟩ : syracuseStep 6067979 = 9101969) B9101969
theorem B2275103 : Blo 1496068 2275103 := bstep (se 1 (by rfl) ⟨1706327, by rfl⟩ : syracuseStep 2275103 = 3412655) B3412655
theorem B1496863 : Blo 1496068 1496863 := bstep (se 1 (by rfl) ⟨1122647, by rfl⟩ : syracuseStep 1496863 = 2245295) B2245295
theorem B1496895 : Blo 1496068 1496895 := bstep (se 1 (by rfl) ⟨1122671, by rfl⟩ : syracuseStep 1496895 = 2245343) B2245343
theorem B4798271 : Blo 1496068 4798271 := bstep (se 1 (by rfl) ⟨3598703, by rfl⟩ : syracuseStep 4798271 = 7197407) B7197407
theorem B21862331 : Blo 1496068 21862331 := bstep (se 1 (by rfl) ⟨16396748, by rfl⟩ : syracuseStep 21862331 = 32793497) B32793497
theorem B17045477 : Blo 1496068 17045477 := bstep (se 4 (by rfl) ⟨1598013, by rfl⟩ : syracuseStep 17045477 = 3196027) B3196027
theorem B1497071 : Blo 1496068 1497071 := bstep (se 1 (by rfl) ⟨1122803, by rfl⟩ : syracuseStep 1497071 = 2245607) B2245607
theorem B5683193 : Blo 1496068 5683193 := bstep (se 2 (by rfl) ⟨2131197, by rfl⟩ : syracuseStep 5683193 = 4262395) B4262395
theorem B1497243 : Blo 1496068 1497243 := bstep (se 1 (by rfl) ⟨1122932, by rfl⟩ : syracuseStep 1497243 = 2245865) B2245865
theorem B1497279 : Blo 1496068 1497279 := bstep (se 1 (by rfl) ⟨1122959, by rfl⟩ : syracuseStep 1497279 = 2245919) B2245919
theorem B8526019 : Blo 1496068 8526019 := bstep (se 1 (by rfl) ⟨6394514, by rfl⟩ : syracuseStep 8526019 = 12789029) B12789029
theorem B1497391 : Blo 1496068 1497391 := bstep (se 1 (by rfl) ⟨1123043, by rfl⟩ : syracuseStep 1497391 = 2246087) B2246087
theorem B5052779 : Blo 1496068 5052779 := bstep (se 1 (by rfl) ⟨3789584, by rfl⟩ : syracuseStep 5052779 = 7579169) B7579169
theorem B1497627 : Blo 1496068 1497627 := bstep (se 1 (by rfl) ⟨1123220, by rfl⟩ : syracuseStep 1497627 = 2246441) B2246441
theorem B1497631 : Blo 1496068 1497631 := bstep (se 1 (by rfl) ⟨1123223, by rfl⟩ : syracuseStep 1497631 = 2246447) B2246447
theorem B9099827 : Blo 1496068 9099827 := bstep (se 1 (by rfl) ⟨6824870, by rfl⟩ : syracuseStep 9099827 = 13649741) B13649741
theorem B12474967 : Blo 1496068 12474967 := bstep (se 1 (by rfl) ⟨9356225, by rfl⟩ : syracuseStep 12474967 = 18712451) B18712451
theorem B5053049 : Blo 1496068 5053049 := bstep (se 2 (by rfl) ⟨1894893, by rfl⟩ : syracuseStep 5053049 = 3789787) B3789787
theorem B1497947 : Blo 1496068 1497947 := bstep (se 1 (by rfl) ⟨1123460, by rfl⟩ : syracuseStep 1497947 = 2246921) B2246921
theorem B1498015 : Blo 1496068 1498015 := bstep (se 1 (by rfl) ⟨1123511, by rfl⟩ : syracuseStep 1498015 = 2247023) B2247023
theorem B2841551 : Blo 1496068 2841551 := bstep (se 1 (by rfl) ⟨2131163, by rfl⟩ : syracuseStep 2841551 = 4262327) B4262327
theorem B5053481 : Blo 1496068 5053481 := bstep (se 2 (by rfl) ⟨1895055, by rfl⟩ : syracuseStep 5053481 = 3790111) B3790111
theorem B6831145 : Blo 1496068 6831145 := bstep (se 2 (by rfl) ⟨2561679, by rfl⟩ : syracuseStep 6831145 = 5123359) B5123359
theorem B98466965 : Blo 1496068 98466965 := bstep (se 6 (by rfl) ⟨2307819, by rfl⟩ : syracuseStep 98466965 = 4615639) B4615639
theorem B6397181 : Blo 1496068 6397181 := bstep (se 3 (by rfl) ⟨1199471, by rfl⟩ : syracuseStep 6397181 = 2398943) B2398943
theorem B5758303 : Blo 1496068 5758303 := bstep (se 1 (by rfl) ⟨4318727, by rfl⟩ : syracuseStep 5758303 = 8637455) B8637455
theorem B2842067 : Blo 1496068 2842067 := bstep (se 1 (by rfl) ⟨2131550, by rfl⟩ : syracuseStep 2842067 = 4263101) B4263101
theorem B7577063 : Blo 1496068 7577063 := bstep (se 1 (by rfl) ⟨5682797, by rfl⟩ : syracuseStep 7577063 = 11365595) B11365595
theorem B2244203 : Blo 1496068 2244203 := bstep (se 1 (by rfl) ⟨1683152, by rfl⟩ : syracuseStep 2244203 = 3366305) B3366305
theorem B2244329 : Blo 1496068 2244329 := bstep (se 2 (by rfl) ⟨841623, by rfl⟩ : syracuseStep 2244329 = 1683247) B1683247
theorem B3366647 : Blo 1496068 3366647 := bstep (se 1 (by rfl) ⟨2524985, by rfl⟩ : syracuseStep 3366647 = 5049971) B5049971
theorem B36437849 : Blo 1496068 36437849 := bstep (se 2 (by rfl) ⟨13664193, by rfl⟩ : syracuseStep 36437849 = 27328387) B27328387
theorem B2244473 : Blo 1496068 2244473 := bstep (se 2 (by rfl) ⟨841677, by rfl⟩ : syracuseStep 2244473 = 1683355) B1683355
theorem B3366827 : Blo 1496068 3366827 := bstep (se 1 (by rfl) ⟨2525120, by rfl⟩ : syracuseStep 3366827 = 5050241) B5050241
theorem B2244575 : Blo 1496068 2244575 := bstep (se 1 (by rfl) ⟨1683431, by rfl⟩ : syracuseStep 2244575 = 3366863) B3366863
theorem B5841085 : Blo 1496068 5841085 := bstep (se 3 (by rfl) ⟨1095203, by rfl⟩ : syracuseStep 5841085 = 2190407) B2190407
theorem B2244911 : Blo 1496068 2244911 := bstep (se 1 (by rfl) ⟨1683683, by rfl⟩ : syracuseStep 2244911 = 3367367) B3367367
theorem B3367223 : Blo 1496068 3367223 := bstep (se 1 (by rfl) ⟨2525417, by rfl⟩ : syracuseStep 3367223 = 5050835) B5050835
theorem B49889735 : Blo 1496068 49889735 := bstep (se 1 (by rfl) ⟨37417301, by rfl⟩ : syracuseStep 49889735 = 74834603) B74834603
theorem B2245151 : Blo 1496068 2245151 := bstep (se 1 (by rfl) ⟨1683863, by rfl⟩ : syracuseStep 2245151 = 3367727) B3367727
theorem B7578359 : Blo 1496068 7578359 := bstep (se 1 (by rfl) ⟨5683769, by rfl⟩ : syracuseStep 7578359 = 11367539) B11367539
theorem B11527069 : Blo 1496068 11527069 := bstep (se 3 (by rfl) ⟨2161325, by rfl⟩ : syracuseStep 11527069 = 4322651) B4322651
theorem B9593801 : Blo 1496068 9593801 := bstep (se 2 (by rfl) ⟨3597675, by rfl⟩ : syracuseStep 9593801 = 7195351) B7195351
theorem B6390809 : Blo 1496068 6390809 := bstep (se 2 (by rfl) ⟨2396553, by rfl⟩ : syracuseStep 6390809 = 4793107) B4793107
theorem B6825019 : Blo 1496068 6825019 := bstep (se 1 (by rfl) ⟨5118764, by rfl⟩ : syracuseStep 6825019 = 10237529) B10237529
theorem B1516735 : Blo 1496068 1516735 := bstep (se 1 (by rfl) ⟨1137551, by rfl⟩ : syracuseStep 1516735 = 2275103) B2275103
theorem B2245823 : Blo 1496068 2245823 := bstep (se 1 (by rfl) ⟨1684367, by rfl⟩ : syracuseStep 2245823 = 3368735) B3368735
theorem B7578845 : Blo 1496068 7578845 := bstep (se 3 (by rfl) ⟨1421033, by rfl⟩ : syracuseStep 7578845 = 2842067) B2842067
theorem B14574887 : Blo 1496068 14574887 := bstep (se 1 (by rfl) ⟨10931165, by rfl⟩ : syracuseStep 14574887 = 21862331) B21862331
theorem B3368249 : Blo 1496068 3368249 := bstep (se 2 (by rfl) ⟨1263093, by rfl⟩ : syracuseStep 3368249 = 2526187) B2526187
theorem B11363651 : Blo 1496068 11363651 := bstep (se 1 (by rfl) ⟨8522738, by rfl⟩ : syracuseStep 11363651 = 17045477) B17045477
theorem B2245967 : Blo 1496068 2245967 := bstep (se 1 (by rfl) ⟨1684475, by rfl⟩ : syracuseStep 2245967 = 3368951) B3368951
theorem B4261211 : Blo 1496068 4261211 := bstep (se 1 (by rfl) ⟨3195908, by rfl⟩ : syracuseStep 4261211 = 6391817) B6391817
theorem B17286497 : Blo 1496068 17286497 := bstep (se 2 (by rfl) ⟨6482436, by rfl⟩ : syracuseStep 17286497 = 12964873) B12964873
theorem B5686625 : Blo 1496068 5686625 := bstep (se 2 (by rfl) ⟨2132484, by rfl⟩ : syracuseStep 5686625 = 4264969) B4264969
theorem B2246057 : Blo 1496068 2246057 := bstep (se 2 (by rfl) ⟨842271, by rfl⟩ : syracuseStep 2246057 = 1684543) B1684543
theorem B2246207 : Blo 1496068 2246207 := bstep (se 1 (by rfl) ⟨1684655, by rfl⟩ : syracuseStep 2246207 = 3369311) B3369311
theorem B3368519 : Blo 1496068 3368519 := bstep (se 1 (by rfl) ⟨2526389, by rfl⟩ : syracuseStep 3368519 = 5052779) B5052779
theorem B2246249 : Blo 1496068 2246249 := bstep (se 2 (by rfl) ⟨842343, by rfl⟩ : syracuseStep 2246249 = 1684687) B1684687
theorem B3196523 : Blo 1496068 3196523 := bstep (se 1 (by rfl) ⟨2397392, by rfl⟩ : syracuseStep 3196523 = 4794785) B4794785
theorem B7292537 : Blo 1496068 7292537 := bstep (se 2 (by rfl) ⟨2734701, by rfl⟩ : syracuseStep 7292537 = 5469403) B5469403
theorem B3368699 : Blo 1496068 3368699 := bstep (se 1 (by rfl) ⟨2526524, by rfl⟩ : syracuseStep 3368699 = 5053049) B5053049
theorem B7677737 : Blo 1496068 7677737 := bstep (se 2 (by rfl) ⟨2879151, by rfl⟩ : syracuseStep 7677737 = 5758303) B5758303
theorem B1894367 : Blo 1496068 1894367 := bstep (se 1 (by rfl) ⟨1420775, by rfl⟩ : syracuseStep 1894367 = 2841551) B2841551
theorem B4261871 : Blo 1496068 4261871 := bstep (se 1 (by rfl) ⟨3196403, by rfl⟩ : syracuseStep 4261871 = 6392807) B6392807
theorem B3368987 : Blo 1496068 3368987 := bstep (se 1 (by rfl) ⟨2526740, by rfl⟩ : syracuseStep 3368987 = 5053481) B5053481
theorem B2525215 : Blo 1496068 2525215 := bstep (se 1 (by rfl) ⟨1893911, by rfl⟩ : syracuseStep 2525215 = 3787823) B3787823
theorem B2246687 : Blo 1496068 2246687 := bstep (se 1 (by rfl) ⟨1685015, by rfl⟩ : syracuseStep 2246687 = 3370031) B3370031
theorem B65644643 : Blo 1496068 65644643 := bstep (se 1 (by rfl) ⟨49233482, by rfl⟩ : syracuseStep 65644643 = 98466965) B98466965
theorem B2246879 : Blo 1496068 2246879 := bstep (se 1 (by rfl) ⟨1685159, by rfl⟩ : syracuseStep 2246879 = 3370319) B3370319
theorem B2246939 : Blo 1496068 2246939 := bstep (se 1 (by rfl) ⟨1685204, by rfl⟩ : syracuseStep 2246939 = 3370409) B3370409
theorem B2525519 : Blo 1496068 2525519 := bstep (se 1 (by rfl) ⟨1894139, by rfl⟩ : syracuseStep 2525519 = 3788279) B3788279
theorem B6392191 : Blo 1496068 6392191 := bstep (se 1 (by rfl) ⟨4794143, by rfl⟩ : syracuseStep 6392191 = 9588287) B9588287
theorem B9595361 : Blo 1496068 9595361 := bstep (se 2 (by rfl) ⟨3598260, by rfl⟩ : syracuseStep 9595361 = 7196521) B7196521
theorem B24291899 : Blo 1496068 24291899 := bstep (se 1 (by rfl) ⟨18218924, by rfl⟩ : syracuseStep 24291899 = 36437849) B36437849
theorem B11373371 : Blo 1496068 11373371 := bstep (se 1 (by rfl) ⟨8530028, by rfl⟩ : syracuseStep 11373371 = 17060057) B17060057
theorem B36432773 : Blo 1496068 36432773 := bstep (se 4 (by rfl) ⟨3415572, by rfl⟩ : syracuseStep 36432773 = 6831145) B6831145
theorem B36416627 : Blo 1496068 36416627 := bstep (se 1 (by rfl) ⟨27312470, by rfl⟩ : syracuseStep 36416627 = 54624941) B54624941
theorem B2526383 : Blo 1496068 2526383 := bstep (se 1 (by rfl) ⟨1894787, by rfl⟩ : syracuseStep 2526383 = 3789575) B3789575
theorem B8523103 : Blo 1496068 8523103 := bstep (se 1 (by rfl) ⟨6392327, by rfl⟩ : syracuseStep 8523103 = 12784655) B12784655
theorem B16633289 : Blo 1496068 16633289 := bstep (se 2 (by rfl) ⟨6237483, by rfl⟩ : syracuseStep 16633289 = 12474967) B12474967
theorem B3370463 : Blo 1496068 3370463 := bstep (se 1 (by rfl) ⟨2527847, by rfl⟩ : syracuseStep 3370463 = 5055695) B5055695
theorem B3198847 : Blo 1496068 3198847 := bstep (se 1 (by rfl) ⟨2399135, by rfl⟩ : syracuseStep 3198847 = 4798271) B4798271
theorem B4796297 : Blo 1496068 4796297 := bstep (se 2 (by rfl) ⟨1798611, by rfl⟩ : syracuseStep 4796297 = 3597223) B3597223
theorem B3788795 : Blo 1496068 3788795 := bstep (se 1 (by rfl) ⟨2841596, by rfl⟩ : syracuseStep 3788795 = 5683193) B5683193
theorem B9597001 : Blo 1496068 9597001 := bstep (se 2 (by rfl) ⟨3598875, by rfl⟩ : syracuseStep 9597001 = 7197751) B7197751
theorem B5681279 : Blo 1496068 5681279 := bstep (se 1 (by rfl) ⟨4260959, by rfl⟩ : syracuseStep 5681279 = 8521919) B8521919
theorem B6066551 : Blo 1496068 6066551 := bstep (se 1 (by rfl) ⟨4549913, by rfl⟩ : syracuseStep 6066551 = 9099827) B9099827
theorem B6066845 : Blo 1496068 6066845 := bstep (se 3 (by rfl) ⟨1137533, by rfl⟩ : syracuseStep 6066845 = 2275067) B2275067
theorem B1684219 : Blo 1496068 1684219 := bstep (se 1 (by rfl) ⟨1263164, by rfl⟩ : syracuseStep 1684219 = 2526329) B2526329
theorem B12792653 : Blo 1496068 12792653 := bstep (se 3 (by rfl) ⟨2398622, by rfl⟩ : syracuseStep 12792653 = 4797245) B4797245
theorem B4264787 : Blo 1496068 4264787 := bstep (se 1 (by rfl) ⟨3198590, by rfl⟩ : syracuseStep 4264787 = 6397181) B6397181
theorem B23999399 : Blo 1496068 23999399 := bstep (se 1 (by rfl) ⟨17999549, by rfl⟩ : syracuseStep 23999399 = 35999099) B35999099
theorem B5051375 : Blo 1496068 5051375 := bstep (se 1 (by rfl) ⟨3788531, by rfl⟩ : syracuseStep 5051375 = 7577063) B7577063
theorem B1496135 : Blo 1496068 1496135 := bstep (se 1 (by rfl) ⟨1122101, by rfl⟩ : syracuseStep 1496135 = 2244203) B2244203
theorem B1496219 : Blo 1496068 1496219 := bstep (se 1 (by rfl) ⟨1122164, by rfl⟩ : syracuseStep 1496219 = 2244329) B2244329
theorem B7582895 : Blo 1496068 7582895 := bstep (se 1 (by rfl) ⟨5687171, by rfl⟩ : syracuseStep 7582895 = 11374343) B11374343
theorem B11375801 : Blo 1496068 11375801 := bstep (se 2 (by rfl) ⟨4265925, by rfl⟩ : syracuseStep 11375801 = 8531851) B8531851
theorem B1496315 : Blo 1496068 1496315 := bstep (se 1 (by rfl) ⟨1122236, by rfl⟩ : syracuseStep 1496315 = 2244473) B2244473
theorem B1496383 : Blo 1496068 1496383 := bstep (se 1 (by rfl) ⟨1122287, by rfl⟩ : syracuseStep 1496383 = 2244575) B2244575
theorem B1496551 : Blo 1496068 1496551 := bstep (se 1 (by rfl) ⟨1122413, by rfl⟩ : syracuseStep 1496551 = 2244827) B2244827
theorem B1496559 : Blo 1496068 1496559 := bstep (se 1 (by rfl) ⟨1122419, by rfl⟩ : syracuseStep 1496559 = 2244839) B2244839
theorem B1684975 : Blo 1496068 1684975 := bstep (se 1 (by rfl) ⟨1263731, by rfl⟩ : syracuseStep 1684975 = 2527463) B2527463
theorem B11368025 : Blo 1496068 11368025 := bstep (se 2 (by rfl) ⟨4263009, by rfl⟩ : syracuseStep 11368025 = 8526019) B8526019
theorem B1496667 : Blo 1496068 1496667 := bstep (se 1 (by rfl) ⟨1122500, by rfl⟩ : syracuseStep 1496667 = 2245001) B2245001
theorem B1685083 : Blo 1496068 1685083 := bstep (se 1 (by rfl) ⟨1263812, by rfl⟩ : syracuseStep 1685083 = 2527625) B2527625
theorem B1496731 : Blo 1496068 1496731 := bstep (se 1 (by rfl) ⟨1122548, by rfl⟩ : syracuseStep 1496731 = 2245097) B2245097
theorem B10794667 : Blo 1496068 10794667 := bstep (se 1 (by rfl) ⟨8096000, by rfl⟩ : syracuseStep 10794667 = 16192001) B16192001
theorem B1496815 : Blo 1496068 1496815 := bstep (se 1 (by rfl) ⟨1122611, by rfl⟩ : syracuseStep 1496815 = 2245223) B2245223
theorem B1496903 : Blo 1496068 1496903 := bstep (se 1 (by rfl) ⟨1122677, by rfl⟩ : syracuseStep 1496903 = 2245355) B2245355
theorem B1496923 : Blo 1496068 1496923 := bstep (se 1 (by rfl) ⟨1122692, by rfl⟩ : syracuseStep 1496923 = 2245385) B2245385
theorem B1496991 : Blo 1496068 1496991 := bstep (se 1 (by rfl) ⟨1122743, by rfl⟩ : syracuseStep 1496991 = 2245487) B2245487
theorem B1497159 : Blo 1496068 1497159 := bstep (se 1 (by rfl) ⟨1122869, by rfl⟩ : syracuseStep 1497159 = 2245739) B2245739
theorem B59144363 : Blo 1496068 59144363 := bstep (se 1 (by rfl) ⟨44358272, by rfl⟩ : syracuseStep 59144363 = 88716545) B88716545
theorem B5683391 : Blo 1496068 5683391 := bstep (se 1 (by rfl) ⟨4262543, by rfl⟩ : syracuseStep 5683391 = 8525087) B8525087
theorem B4798655 : Blo 1496068 4798655 := bstep (se 1 (by rfl) ⟨3598991, by rfl⟩ : syracuseStep 4798655 = 7197983) B7197983
theorem B1497319 : Blo 1496068 1497319 := bstep (se 1 (by rfl) ⟨1122989, by rfl⟩ : syracuseStep 1497319 = 2245979) B2245979
theorem B6396191 : Blo 1496068 6396191 := bstep (se 1 (by rfl) ⟨4797143, by rfl⟩ : syracuseStep 6396191 = 9594287) B9594287
theorem B7682411 : Blo 1496068 7682411 := bstep (se 1 (by rfl) ⟨5761808, by rfl⟩ : syracuseStep 7682411 = 11523617) B11523617
theorem B9099631 : Blo 1496068 9099631 := bstep (se 1 (by rfl) ⟨6824723, by rfl⟩ : syracuseStep 9099631 = 13649447) B13649447
theorem B1497503 : Blo 1496068 1497503 := bstep (se 1 (by rfl) ⟨1123127, by rfl⟩ : syracuseStep 1497503 = 2246255) B2246255
theorem B1497551 : Blo 1496068 1497551 := bstep (se 1 (by rfl) ⟨1123163, by rfl⟩ : syracuseStep 1497551 = 2246327) B2246327
theorem B1497575 : Blo 1496068 1497575 := bstep (se 1 (by rfl) ⟨1123181, by rfl⟩ : syracuseStep 1497575 = 2246363) B2246363
theorem B2841065 : Blo 1496068 2841065 := bstep (se 2 (by rfl) ⟨1065399, by rfl⟩ : syracuseStep 2841065 = 2130799) B2130799
theorem B4045319 : Blo 1496068 4045319 := bstep (se 1 (by rfl) ⟨3033989, by rfl⟩ : syracuseStep 4045319 = 6067979) B6067979
theorem B3791387 : Blo 1496068 3791387 := bstep (se 1 (by rfl) ⟨2843540, by rfl⟩ : syracuseStep 3791387 = 5687081) B5687081
theorem B1497691 : Blo 1496068 1497691 := bstep (se 1 (by rfl) ⟨1123268, by rfl⟩ : syracuseStep 1497691 = 2246537) B2246537
theorem B1497759 : Blo 1496068 1497759 := bstep (se 1 (by rfl) ⟨1123319, by rfl⟩ : syracuseStep 1497759 = 2246639) B2246639
theorem B2399033 : Blo 1496068 2399033 := bstep (se 2 (by rfl) ⟨899637, by rfl⟩ : syracuseStep 2399033 = 1799275) B1799275
theorem B1497927 : Blo 1496068 1497927 := bstep (se 1 (by rfl) ⟨1123445, by rfl⟩ : syracuseStep 1497927 = 2246891) B2246891
theorem B1497967 : Blo 1496068 1497967 := bstep (se 1 (by rfl) ⟨1123475, by rfl⟩ : syracuseStep 1497967 = 2246951) B2246951
theorem B1498023 : Blo 1496068 1498023 := bstep (se 1 (by rfl) ⟨1123517, by rfl⟩ : syracuseStep 1498023 = 2247035) B2247035
theorem B5479363 : Blo 1496068 5479363 := bstep (se 1 (by rfl) ⟨4109522, by rfl⟩ : syracuseStep 5479363 = 8219045) B8219045
theorem B8526977 : Blo 1496068 8526977 := bstep (se 2 (by rfl) ⟨3197616, by rfl⟩ : syracuseStep 8526977 = 6395233) B6395233
theorem B3366215 : Blo 1496068 3366215 := bstep (se 1 (by rfl) ⟨2524661, by rfl⟩ : syracuseStep 3366215 = 5049323) B5049323
theorem B3366251 : Blo 1496068 3366251 := bstep (se 1 (by rfl) ⟨2524688, by rfl⟩ : syracuseStep 3366251 = 5049377) B5049377
theorem B3366377 : Blo 1496068 3366377 := bstep (se 2 (by rfl) ⟨1262391, by rfl⟩ : syracuseStep 3366377 = 2524783) B2524783
theorem B3366521 : Blo 1496068 3366521 := bstep (se 2 (by rfl) ⟨1262445, by rfl⟩ : syracuseStep 3366521 = 2524891) B2524891
theorem B32390837 : Blo 1496068 32390837 := bstep (se 5 (by rfl) ⟨1518320, by rfl⟩ : syracuseStep 32390837 = 3036641) B3036641
theorem B2244431 : Blo 1496068 2244431 := bstep (se 1 (by rfl) ⟨1683323, by rfl⟩ : syracuseStep 2244431 = 3366647) B3366647
theorem B2842523 : Blo 1496068 2842523 := bstep (se 1 (by rfl) ⟨2131892, by rfl⟩ : syracuseStep 2842523 = 4263785) B4263785
theorem B2244551 : Blo 1496068 2244551 := bstep (se 1 (by rfl) ⟨1683413, by rfl⟩ : syracuseStep 2244551 = 3366827) B3366827
theorem B23035853 : Blo 1496068 23035853 := bstep (se 3 (by rfl) ⟨4319222, by rfl⟩ : syracuseStep 23035853 = 8638445) B8638445
theorem B3366953 : Blo 1496068 3366953 := bstep (se 2 (by rfl) ⟨1262607, by rfl⟩ : syracuseStep 3366953 = 2525215) B2525215
theorem B12796001 : Blo 1496068 12796001 := bstep (se 2 (by rfl) ⟨4798500, by rfl⟩ : syracuseStep 12796001 = 9597001) B9597001
theorem B2244815 : Blo 1496068 2244815 := bstep (se 1 (by rfl) ⟨1683611, by rfl⟩ : syracuseStep 2244815 = 3367223) B3367223
theorem B33259823 : Blo 1496068 33259823 := bstep (se 1 (by rfl) ⟨24944867, by rfl⟩ : syracuseStep 33259823 = 49889735) B49889735
theorem B12132841 : Blo 1496068 12132841 := bstep (se 2 (by rfl) ⟨4549815, by rfl⟩ : syracuseStep 12132841 = 9099631) B9099631
theorem B8528435 : Blo 1496068 8528435 := bstep (se 1 (by rfl) ⟨6396326, by rfl⟩ : syracuseStep 8528435 = 12792653) B12792653
theorem B2843191 : Blo 1496068 2843191 := bstep (se 1 (by rfl) ⟨2132393, by rfl⟩ : syracuseStep 2843191 = 4264787) B4264787
theorem B15999599 : Blo 1496068 15999599 := bstep (se 1 (by rfl) ⟨11999699, by rfl⟩ : syracuseStep 15999599 = 23999399) B23999399
theorem B3367583 : Blo 1496068 3367583 := bstep (se 1 (by rfl) ⟨2525687, by rfl⟩ : syracuseStep 3367583 = 5051375) B5051375
theorem B4260539 : Blo 1496068 4260539 := bstep (se 1 (by rfl) ⟨3195404, by rfl⟩ : syracuseStep 4260539 = 6390809) B6390809
theorem B5055263 : Blo 1496068 5055263 := bstep (se 1 (by rfl) ⟨3791447, by rfl⟩ : syracuseStep 5055263 = 7582895) B7582895
theorem B9716591 : Blo 1496068 9716591 := bstep (se 1 (by rfl) ⟨7287443, by rfl⟩ : syracuseStep 9716591 = 14574887) B14574887
theorem B2245499 : Blo 1496068 2245499 := bstep (se 1 (by rfl) ⟨1684124, by rfl⟩ : syracuseStep 2245499 = 3368249) B3368249
theorem B2245625 : Blo 1496068 2245625 := bstep (se 2 (by rfl) ⟨842109, by rfl⟩ : syracuseStep 2245625 = 1684219) B1684219
theorem B2245679 : Blo 1496068 2245679 := bstep (se 1 (by rfl) ⟨1684259, by rfl⟩ : syracuseStep 2245679 = 3368519) B3368519
theorem B7578683 : Blo 1496068 7578683 := bstep (se 1 (by rfl) ⟨5684012, by rfl⟩ : syracuseStep 7578683 = 11368025) B11368025
theorem B2245799 : Blo 1496068 2245799 := bstep (se 1 (by rfl) ⟨1684349, by rfl⟩ : syracuseStep 2245799 = 3368699) B3368699
theorem B15369425 : Blo 1496068 15369425 := bstep (se 2 (by rfl) ⟨5763534, by rfl⟩ : syracuseStep 15369425 = 11527069) B11527069
theorem B2245991 : Blo 1496068 2245991 := bstep (se 1 (by rfl) ⟨1684493, by rfl⟩ : syracuseStep 2245991 = 3368987) B3368987
theorem B43763095 : Blo 1496068 43763095 := bstep (se 1 (by rfl) ⟨32822321, by rfl⟩ : syracuseStep 43763095 = 65644643) B65644643
theorem B39429575 : Blo 1496068 39429575 := bstep (se 1 (by rfl) ⟨29572181, by rfl⟩ : syracuseStep 39429575 = 59144363) B59144363
theorem B1894043 : Blo 1496068 1894043 := bstep (se 1 (by rfl) ⟨1420532, by rfl⟩ : syracuseStep 1894043 = 2841065) B2841065
theorem B2696879 : Blo 1496068 2696879 := bstep (se 1 (by rfl) ⟨2022659, by rfl⟩ : syracuseStep 2696879 = 4045319) B4045319
theorem B11364137 : Blo 1496068 11364137 := bstep (se 2 (by rfl) ⟨4261551, by rfl⟩ : syracuseStep 11364137 = 8523103) B8523103
theorem B1599355 : Blo 1496068 1599355 := bstep (se 1 (by rfl) ⟨1199516, by rfl⟩ : syracuseStep 1599355 = 2399033) B2399033
theorem B2246633 : Blo 1496068 2246633 := bstep (se 2 (by rfl) ⟨842487, by rfl⟩ : syracuseStep 2246633 = 1684975) B1684975
theorem B2246777 : Blo 1496068 2246777 := bstep (se 2 (by rfl) ⟨842541, by rfl⟩ : syracuseStep 2246777 = 1685083) B1685083
theorem B2246975 : Blo 1496068 2246975 := bstep (se 1 (by rfl) ⟨1685231, by rfl⟩ : syracuseStep 2246975 = 3370463) B3370463
theorem B3197531 : Blo 1496068 3197531 := bstep (se 1 (by rfl) ⟨2398148, by rfl⟩ : syracuseStep 3197531 = 4796297) B4796297
theorem B1895015 : Blo 1496068 1895015 := bstep (se 1 (by rfl) ⟨1421261, by rfl⟩ : syracuseStep 1895015 = 2842523) B2842523
theorem B2525863 : Blo 1496068 2525863 := bstep (se 1 (by rfl) ⟨1894397, by rfl⟩ : syracuseStep 2525863 = 3788795) B3788795
theorem B3787519 : Blo 1496068 3787519 := bstep (se 1 (by rfl) ⟨2840639, by rfl⟩ : syracuseStep 3787519 = 5681279) B5681279
theorem B8522921 : Blo 1496068 8522921 := bstep (se 2 (by rfl) ⟨3196095, by rfl⟩ : syracuseStep 8522921 = 6392191) B6392191
theorem B8089253 : Blo 1496068 8089253 := bstep (se 4 (by rfl) ⟨758367, by rfl⟩ : syracuseStep 8089253 = 1516735) B1516735
theorem B4861691 : Blo 1496068 4861691 := bstep (se 1 (by rfl) ⟨3646268, by rfl⟩ : syracuseStep 4861691 = 7292537) B7292537
theorem B44355437 : Blo 1496068 44355437 := bstep (se 3 (by rfl) ⟨8316644, by rfl⟩ : syracuseStep 44355437 = 16633289) B16633289
theorem B3788927 : Blo 1496068 3788927 := bstep (se 1 (by rfl) ⟨2841695, by rfl⟩ : syracuseStep 3788927 = 5683391) B5683391
theorem B3199103 : Blo 1496068 3199103 := bstep (se 1 (by rfl) ⟨2399327, by rfl⟩ : syracuseStep 3199103 = 4798655) B4798655
theorem B4264127 : Blo 1496068 4264127 := bstep (se 1 (by rfl) ⟨3198095, by rfl⟩ : syracuseStep 4264127 = 6396191) B6396191
theorem B1683679 : Blo 1496068 1683679 := bstep (se 1 (by rfl) ⟨1262759, by rfl⟩ : syracuseStep 1683679 = 2525519) B2525519
theorem B8524061 : Blo 1496068 8524061 := bstep (se 3 (by rfl) ⟨1598261, by rfl⟩ : syracuseStep 8524061 = 3196523) B3196523
theorem B2527591 : Blo 1496068 2527591 := bstep (se 1 (by rfl) ⟨1895693, by rfl⟩ : syracuseStep 2527591 = 3791387) B3791387
theorem B7582247 : Blo 1496068 7582247 := bstep (se 1 (by rfl) ⟨5686685, by rfl⟩ : syracuseStep 7582247 = 11373371) B11373371
theorem B24277751 : Blo 1496068 24277751 := bstep (se 1 (by rfl) ⟨18208313, by rfl⟩ : syracuseStep 24277751 = 36416627) B36416627
theorem B1684255 : Blo 1496068 1684255 := bstep (se 1 (by rfl) ⟨1263191, by rfl⟩ : syracuseStep 1684255 = 2526383) B2526383
theorem B4265129 : Blo 1496068 4265129 := bstep (se 2 (by rfl) ⟨1599423, by rfl⟩ : syracuseStep 4265129 = 3198847) B3198847
theorem B1496287 : Blo 1496068 1496287 := bstep (se 1 (by rfl) ⟨1122215, by rfl⟩ : syracuseStep 1496287 = 2244431) B2244431
theorem B5051645 : Blo 1496068 5051645 := bstep (se 3 (by rfl) ⟨947183, by rfl⟩ : syracuseStep 5051645 = 1894367) B1894367
theorem B1496367 : Blo 1496068 1496367 := bstep (se 1 (by rfl) ⟨1122275, by rfl⟩ : syracuseStep 1496367 = 2244551) B2244551
theorem B15357235 : Blo 1496068 15357235 := bstep (se 1 (by rfl) ⟨11517926, by rfl⟩ : syracuseStep 15357235 = 23035853) B23035853
theorem B1496607 : Blo 1496068 1496607 := bstep (se 1 (by rfl) ⟨1122455, by rfl⟩ : syracuseStep 1496607 = 2244911) B2244911
theorem B4044367 : Blo 1496068 4044367 := bstep (se 1 (by rfl) ⟨3033275, by rfl⟩ : syracuseStep 4044367 = 6066551) B6066551
theorem B7788113 : Blo 1496068 7788113 := bstep (se 2 (by rfl) ⟨2920542, by rfl⟩ : syracuseStep 7788113 = 5841085) B5841085
theorem B1496767 : Blo 1496068 1496767 := bstep (se 1 (by rfl) ⟨1122575, by rfl⟩ : syracuseStep 1496767 = 2245151) B2245151
theorem B4044563 : Blo 1496068 4044563 := bstep (se 1 (by rfl) ⟨3033422, by rfl⟩ : syracuseStep 4044563 = 6066845) B6066845
theorem B5052239 : Blo 1496068 5052239 := bstep (se 1 (by rfl) ⟨3789179, by rfl⟩ : syracuseStep 5052239 = 7578359) B7578359
theorem B6395867 : Blo 1496068 6395867 := bstep (se 1 (by rfl) ⟨4796900, by rfl⟩ : syracuseStep 6395867 = 9593801) B9593801
theorem B7583867 : Blo 1496068 7583867 := bstep (se 1 (by rfl) ⟨5687900, by rfl⟩ : syracuseStep 7583867 = 11375801) B11375801
theorem B1497215 : Blo 1496068 1497215 := bstep (se 1 (by rfl) ⟨1122911, by rfl⟩ : syracuseStep 1497215 = 2245823) B2245823
theorem B5052563 : Blo 1496068 5052563 := bstep (se 1 (by rfl) ⟨3789422, by rfl⟩ : syracuseStep 5052563 = 7578845) B7578845
theorem B7575767 : Blo 1496068 7575767 := bstep (se 1 (by rfl) ⟨5681825, by rfl⟩ : syracuseStep 7575767 = 11363651) B11363651
theorem B1497311 : Blo 1496068 1497311 := bstep (se 1 (by rfl) ⟨1122983, by rfl⟩ : syracuseStep 1497311 = 2245967) B2245967
theorem B2840807 : Blo 1496068 2840807 := bstep (se 1 (by rfl) ⟨2130605, by rfl⟩ : syracuseStep 2840807 = 4261211) B4261211
theorem B11524331 : Blo 1496068 11524331 := bstep (se 1 (by rfl) ⟨8643248, by rfl⟩ : syracuseStep 11524331 = 17286497) B17286497
theorem B3791083 : Blo 1496068 3791083 := bstep (se 1 (by rfl) ⟨2843312, by rfl⟩ : syracuseStep 3791083 = 5686625) B5686625
theorem B1497371 : Blo 1496068 1497371 := bstep (se 1 (by rfl) ⟨1123028, by rfl⟩ : syracuseStep 1497371 = 2246057) B2246057
theorem B20486429 : Blo 1496068 20486429 := bstep (se 3 (by rfl) ⟨3841205, by rfl⟩ : syracuseStep 20486429 = 7682411) B7682411
theorem B1497471 : Blo 1496068 1497471 := bstep (se 1 (by rfl) ⟨1123103, by rfl⟩ : syracuseStep 1497471 = 2246207) B2246207
theorem B1497499 : Blo 1496068 1497499 := bstep (se 1 (by rfl) ⟨1123124, by rfl⟩ : syracuseStep 1497499 = 2246249) B2246249
theorem B5118491 : Blo 1496068 5118491 := bstep (se 1 (by rfl) ⟨3838868, by rfl⟩ : syracuseStep 5118491 = 7677737) B7677737
theorem B7305817 : Blo 1496068 7305817 := bstep (se 2 (by rfl) ⟨2739681, by rfl⟩ : syracuseStep 7305817 = 5479363) B5479363
theorem B2841247 : Blo 1496068 2841247 := bstep (se 1 (by rfl) ⟨2130935, by rfl⟩ : syracuseStep 2841247 = 4261871) B4261871
theorem B1497791 : Blo 1496068 1497791 := bstep (se 1 (by rfl) ⟨1123343, by rfl⟩ : syracuseStep 1497791 = 2246687) B2246687
theorem B9100025 : Blo 1496068 9100025 := bstep (se 2 (by rfl) ⟨3412509, by rfl⟩ : syracuseStep 9100025 = 6825019) B6825019
theorem B1497919 : Blo 1496068 1497919 := bstep (se 1 (by rfl) ⟨1123439, by rfl⟩ : syracuseStep 1497919 = 2246879) B2246879
theorem B1497959 : Blo 1496068 1497959 := bstep (se 1 (by rfl) ⟨1123469, by rfl⟩ : syracuseStep 1497959 = 2246939) B2246939
theorem B6396907 : Blo 1496068 6396907 := bstep (se 1 (by rfl) ⟨4797680, by rfl⟩ : syracuseStep 6396907 = 9595361) B9595361
theorem B16194599 : Blo 1496068 16194599 := bstep (se 1 (by rfl) ⟨12145949, by rfl⟩ : syracuseStep 16194599 = 24291899) B24291899
theorem B24288515 : Blo 1496068 24288515 := bstep (se 1 (by rfl) ⟨18216386, by rfl⟩ : syracuseStep 24288515 = 36432773) B36432773
theorem B5684651 : Blo 1496068 5684651 := bstep (se 1 (by rfl) ⟨4263488, by rfl⟩ : syracuseStep 5684651 = 8526977) B8526977
theorem B2244143 : Blo 1496068 2244143 := bstep (se 1 (by rfl) ⟨1683107, by rfl⟩ : syracuseStep 2244143 = 3366215) B3366215
theorem B14392889 : Blo 1496068 14392889 := bstep (se 2 (by rfl) ⟨5397333, by rfl⟩ : syracuseStep 14392889 = 10794667) B10794667
theorem B2244167 : Blo 1496068 2244167 := bstep (se 1 (by rfl) ⟨1683125, by rfl⟩ : syracuseStep 2244167 = 3366251) B3366251
theorem B2244251 : Blo 1496068 2244251 := bstep (se 1 (by rfl) ⟨1683188, by rfl⟩ : syracuseStep 2244251 = 3366377) B3366377
theorem B2244347 : Blo 1496068 2244347 := bstep (se 1 (by rfl) ⟨1683260, by rfl⟩ : syracuseStep 2244347 = 3366521) B3366521
theorem B21593891 : Blo 1496068 21593891 := bstep (se 1 (by rfl) ⟨16195418, by rfl⟩ : syracuseStep 21593891 = 32390837) B32390837
theorem B2244635 : Blo 1496068 2244635 := bstep (se 1 (by rfl) ⟨1683476, by rfl⟩ : syracuseStep 2244635 = 3366953) B3366953
theorem B2842751 : Blo 1496068 2842751 := bstep (se 1 (by rfl) ⟨2132063, by rfl⟩ : syracuseStep 2842751 = 4264127) B4264127
theorem B2244905 : Blo 1496068 2244905 := bstep (se 2 (by rfl) ⟨841839, by rfl⟩ : syracuseStep 2244905 = 1683679) B1683679
theorem B5054777 : Blo 1496068 5054777 := bstep (se 2 (by rfl) ⟨1895541, by rfl⟩ : syracuseStep 5054777 = 3791083) B3791083
theorem B5054831 : Blo 1496068 5054831 := bstep (se 1 (by rfl) ⟨3791123, by rfl⟩ : syracuseStep 5054831 = 7582247) B7582247
theorem B5685623 : Blo 1496068 5685623 := bstep (se 1 (by rfl) ⟨4264217, by rfl⟩ : syracuseStep 5685623 = 8528435) B8528435
theorem B10666399 : Blo 1496068 10666399 := bstep (se 1 (by rfl) ⟨7999799, by rfl⟩ : syracuseStep 10666399 = 15999599) B15999599
theorem B2245055 : Blo 1496068 2245055 := bstep (se 1 (by rfl) ⟨1683791, by rfl⟩ : syracuseStep 2245055 = 3367583) B3367583
theorem B2843419 : Blo 1496068 2843419 := bstep (se 1 (by rfl) ⟨2132564, by rfl⟩ : syracuseStep 2843419 = 4265129) B4265129
theorem B9741089 : Blo 1496068 9741089 := bstep (se 2 (by rfl) ⟨3652908, by rfl⟩ : syracuseStep 9741089 = 7305817) B7305817
theorem B3367763 : Blo 1496068 3367763 := bstep (se 1 (by rfl) ⟨2525822, by rfl⟩ : syracuseStep 3367763 = 5051645) B5051645
theorem B3367817 : Blo 1496068 3367817 := bstep (se 2 (by rfl) ⟨1262931, by rfl⟩ : syracuseStep 3367817 = 2525863) B2525863
theorem B2245673 : Blo 1496068 2245673 := bstep (se 2 (by rfl) ⟨842127, by rfl⟩ : syracuseStep 2245673 = 1684255) B1684255
theorem B2696375 : Blo 1496068 2696375 := bstep (se 1 (by rfl) ⟨2022281, by rfl⟩ : syracuseStep 2696375 = 4044563) B4044563
theorem B3368159 : Blo 1496068 3368159 := bstep (se 1 (by rfl) ⟨2526119, by rfl⟩ : syracuseStep 3368159 = 5052239) B5052239
theorem B8529209 : Blo 1496068 8529209 := bstep (se 2 (by rfl) ⟨3198453, by rfl⟩ : syracuseStep 8529209 = 6396907) B6396907
theorem B13649309 : Blo 1496068 13649309 := bstep (se 3 (by rfl) ⟨2559245, by rfl⟩ : syracuseStep 13649309 = 5118491) B5118491
theorem B5055911 : Blo 1496068 5055911 := bstep (se 1 (by rfl) ⟨3791933, by rfl⟩ : syracuseStep 5055911 = 7583867) B7583867
theorem B3368375 : Blo 1496068 3368375 := bstep (se 1 (by rfl) ⟨2526281, by rfl⟩ : syracuseStep 3368375 = 5052563) B5052563
theorem B1893871 : Blo 1496068 1893871 := bstep (se 1 (by rfl) ⟨1420403, by rfl⟩ : syracuseStep 1893871 = 2840807) B2840807
theorem B13657619 : Blo 1496068 13657619 := bstep (se 1 (by rfl) ⟨10243214, by rfl⟩ : syracuseStep 13657619 = 20486429) B20486429
theorem B2131687 : Blo 1496068 2131687 := bstep (se 1 (by rfl) ⟨1598765, by rfl⟩ : syracuseStep 2131687 = 3197531) B3197531
theorem B8529893 : Blo 1496068 8529893 := bstep (se 4 (by rfl) ⟨799677, by rfl⟩ : syracuseStep 8529893 = 1599355) B1599355
theorem B5392489 : Blo 1496068 5392489 := bstep (se 2 (by rfl) ⟨2022183, by rfl⟩ : syracuseStep 5392489 = 4044367) B4044367
theorem B9595259 : Blo 1496068 9595259 := bstep (se 1 (by rfl) ⟨7196444, by rfl⟩ : syracuseStep 9595259 = 14392889) B14392889
theorem B5392835 : Blo 1496068 5392835 := bstep (se 1 (by rfl) ⟨4044626, by rfl⟩ : syracuseStep 5392835 = 8089253) B8089253
theorem B14395927 : Blo 1496068 14395927 := bstep (se 1 (by rfl) ⟨10796945, by rfl⟩ : syracuseStep 14395927 = 21593891) B21593891
theorem B8530667 : Blo 1496068 8530667 := bstep (se 1 (by rfl) ⟨6398000, by rfl⟩ : syracuseStep 8530667 = 12796001) B12796001
theorem B2525951 : Blo 1496068 2525951 := bstep (se 1 (by rfl) ⟨1894463, by rfl⟩ : syracuseStep 2525951 = 3788927) B3788927
theorem B2132735 : Blo 1496068 2132735 := bstep (se 1 (by rfl) ⟨1599551, by rfl⟩ : syracuseStep 2132735 = 3199103) B3199103
theorem B3370121 : Blo 1496068 3370121 := bstep (se 2 (by rfl) ⟨1263795, by rfl⟩ : syracuseStep 3370121 = 2527591) B2527591
theorem B3370175 : Blo 1496068 3370175 := bstep (se 1 (by rfl) ⟨2527631, by rfl⟩ : syracuseStep 3370175 = 5055263) B5055263
theorem B3788329 : Blo 1496068 3788329 := bstep (se 2 (by rfl) ⟨1420623, by rfl⟩ : syracuseStep 3788329 = 2841247) B2841247
theorem B5050025 : Blo 1496068 5050025 := bstep (se 2 (by rfl) ⟨1893759, by rfl⟩ : syracuseStep 5050025 = 3787519) B3787519
theorem B1797919 : Blo 1496068 1797919 := bstep (se 1 (by rfl) ⟨1348439, by rfl⟩ : syracuseStep 1797919 = 2696879) B2696879
theorem B4263911 : Blo 1496068 4263911 := bstep (se 1 (by rfl) ⟨3197933, by rfl⟩ : syracuseStep 4263911 = 6395867) B6395867
theorem B5050511 : Blo 1496068 5050511 := bstep (se 1 (by rfl) ⟨3787883, by rfl⟩ : syracuseStep 5050511 = 7575767) B7575767
theorem B20476313 : Blo 1496068 20476313 := bstep (se 2 (by rfl) ⟨7678617, by rfl⟩ : syracuseStep 20476313 = 15357235) B15357235
theorem B5050781 : Blo 1496068 5050781 := bstep (se 3 (by rfl) ⟨947021, by rfl⟩ : syracuseStep 5050781 = 1894043) B1894043
theorem B6066683 : Blo 1496068 6066683 := bstep (se 1 (by rfl) ⟨4550012, by rfl⟩ : syracuseStep 6066683 = 9100025) B9100025
theorem B5681947 : Blo 1496068 5681947 := bstep (se 1 (by rfl) ⟨4261460, by rfl⟩ : syracuseStep 5681947 = 8522921) B8522921
theorem B16192343 : Blo 1496068 16192343 := bstep (se 1 (by rfl) ⟨12144257, by rfl⟩ : syracuseStep 16192343 = 24288515) B24288515
theorem B3789767 : Blo 1496068 3789767 := bstep (se 1 (by rfl) ⟨2842325, by rfl⟩ : syracuseStep 3789767 = 5684651) B5684651
theorem B1496095 : Blo 1496068 1496095 := bstep (se 1 (by rfl) ⟨1122071, by rfl⟩ : syracuseStep 1496095 = 2244143) B2244143
theorem B1496111 : Blo 1496068 1496111 := bstep (se 1 (by rfl) ⟨1122083, by rfl⟩ : syracuseStep 1496111 = 2244167) B2244167
theorem B1496167 : Blo 1496068 1496167 := bstep (se 1 (by rfl) ⟨1122125, by rfl⟩ : syracuseStep 1496167 = 2244251) B2244251
theorem B1496231 : Blo 1496068 1496231 := bstep (se 1 (by rfl) ⟨1122173, by rfl⟩ : syracuseStep 1496231 = 2244347) B2244347
theorem B3241127 : Blo 1496068 3241127 := bstep (se 1 (by rfl) ⟨2430845, by rfl⟩ : syracuseStep 3241127 = 4861691) B4861691
theorem B29570291 : Blo 1496068 29570291 := bstep (se 1 (by rfl) ⟨22177718, by rfl⟩ : syracuseStep 29570291 = 44355437) B44355437
theorem B1496543 : Blo 1496068 1496543 := bstep (se 1 (by rfl) ⟨1122407, by rfl⟩ : syracuseStep 1496543 = 2244815) B2244815
theorem B5682707 : Blo 1496068 5682707 := bstep (se 1 (by rfl) ⟨4262030, by rfl⟩ : syracuseStep 5682707 = 8524061) B8524061
theorem B22173215 : Blo 1496068 22173215 := bstep (se 1 (by rfl) ⟨16629911, by rfl⟩ : syracuseStep 22173215 = 33259823) B33259823
theorem B2840359 : Blo 1496068 2840359 := bstep (se 1 (by rfl) ⟨2130269, by rfl⟩ : syracuseStep 2840359 = 4260539) B4260539
theorem B16185167 : Blo 1496068 16185167 := bstep (se 1 (by rfl) ⟨12138875, by rfl⟩ : syracuseStep 16185167 = 24277751) B24277751
theorem B6477727 : Blo 1496068 6477727 := bstep (se 1 (by rfl) ⟨4858295, by rfl⟩ : syracuseStep 6477727 = 9716591) B9716591
theorem B1496999 : Blo 1496068 1496999 := bstep (se 1 (by rfl) ⟨1122749, by rfl⟩ : syracuseStep 1496999 = 2245499) B2245499
theorem B16177121 : Blo 1496068 16177121 := bstep (se 2 (by rfl) ⟨6066420, by rfl⟩ : syracuseStep 16177121 = 12132841) B12132841
theorem B1497083 : Blo 1496068 1497083 := bstep (se 1 (by rfl) ⟨1122812, by rfl⟩ : syracuseStep 1497083 = 2245625) B2245625
theorem B1497119 : Blo 1496068 1497119 := bstep (se 1 (by rfl) ⟨1122839, by rfl⟩ : syracuseStep 1497119 = 2245679) B2245679
theorem B5052455 : Blo 1496068 5052455 := bstep (se 1 (by rfl) ⟨3789341, by rfl⟩ : syracuseStep 5052455 = 7578683) B7578683
theorem B3790921 : Blo 1496068 3790921 := bstep (se 2 (by rfl) ⟨1421595, by rfl⟩ : syracuseStep 3790921 = 2843191) B2843191
theorem B1497199 : Blo 1496068 1497199 := bstep (se 1 (by rfl) ⟨1122899, by rfl⟩ : syracuseStep 1497199 = 2245799) B2245799
theorem B10246283 : Blo 1496068 10246283 := bstep (se 1 (by rfl) ⟨7684712, by rfl⟩ : syracuseStep 10246283 = 15369425) B15369425
theorem B1497327 : Blo 1496068 1497327 := bstep (se 1 (by rfl) ⟨1122995, by rfl⟩ : syracuseStep 1497327 = 2245991) B2245991
theorem B26286383 : Blo 1496068 26286383 := bstep (se 1 (by rfl) ⟨19714787, by rfl⟩ : syracuseStep 26286383 = 39429575) B39429575
theorem B5192075 : Blo 1496068 5192075 := bstep (se 1 (by rfl) ⟨3894056, by rfl⟩ : syracuseStep 5192075 = 7788113) B7788113
theorem B7576091 : Blo 1496068 7576091 := bstep (se 1 (by rfl) ⟨5682068, by rfl⟩ : syracuseStep 7576091 = 11364137) B11364137
theorem B1497755 : Blo 1496068 1497755 := bstep (se 1 (by rfl) ⟨1123316, by rfl⟩ : syracuseStep 1497755 = 2246633) B2246633
theorem B1497851 : Blo 1496068 1497851 := bstep (se 1 (by rfl) ⟨1123388, by rfl⟩ : syracuseStep 1497851 = 2246777) B2246777
theorem B7682887 : Blo 1496068 7682887 := bstep (se 1 (by rfl) ⟨5762165, by rfl⟩ : syracuseStep 7682887 = 11524331) B11524331
theorem B1497983 : Blo 1496068 1497983 := bstep (se 1 (by rfl) ⟨1123487, by rfl⟩ : syracuseStep 1497983 = 2246975) B2246975
theorem B5053373 : Blo 1496068 5053373 := bstep (se 3 (by rfl) ⟨947507, by rfl⟩ : syracuseStep 5053373 = 1895015) B1895015
theorem B58350793 : Blo 1496068 58350793 := bstep (se 2 (by rfl) ⟨21881547, by rfl⟩ : syracuseStep 58350793 = 43763095) B43763095
theorem B10796399 : Blo 1496068 10796399 := bstep (se 1 (by rfl) ⟨8097299, by rfl⟩ : syracuseStep 10796399 = 16194599) B16194599
theorem B3367007 : Blo 1496068 3367007 := bstep (se 1 (by rfl) ⟨2525255, by rfl⟩ : syracuseStep 3367007 = 5050511) B5050511
theorem B5054561 : Blo 1496068 5054561 := bstep (se 2 (by rfl) ⟨1895460, by rfl⟩ : syracuseStep 5054561 = 3790921) B3790921
theorem B3367187 : Blo 1496068 3367187 := bstep (se 1 (by rfl) ⟨2525390, by rfl⟩ : syracuseStep 3367187 = 5050781) B5050781
theorem B14221865 : Blo 1496068 14221865 := bstep (se 2 (by rfl) ⟨5333199, by rfl⟩ : syracuseStep 14221865 = 10666399) B10666399
theorem B2245175 : Blo 1496068 2245175 := bstep (se 1 (by rfl) ⟨1683881, by rfl⟩ : syracuseStep 2245175 = 3367763) B3367763
theorem B2245211 : Blo 1496068 2245211 := bstep (se 1 (by rfl) ⟨1683908, by rfl⟩ : syracuseStep 2245211 = 3367817) B3367817
theorem B38355605 : Blo 1496068 38355605 := bstep (se 6 (by rfl) ⟨898959, by rfl⟩ : syracuseStep 38355605 = 1797919) B1797919
theorem B19194569 : Blo 1496068 19194569 := bstep (se 2 (by rfl) ⟨7197963, by rfl⟩ : syracuseStep 19194569 = 14395927) B14395927
theorem B2245439 : Blo 1496068 2245439 := bstep (se 1 (by rfl) ⟨1684079, by rfl⟩ : syracuseStep 2245439 = 3368159) B3368159
theorem B5686139 : Blo 1496068 5686139 := bstep (se 1 (by rfl) ⟨4264604, by rfl⟩ : syracuseStep 5686139 = 8529209) B8529209
theorem B2245583 : Blo 1496068 2245583 := bstep (se 1 (by rfl) ⟨1684187, by rfl⟩ : syracuseStep 2245583 = 3368375) B3368375
theorem B10790111 : Blo 1496068 10790111 := bstep (se 1 (by rfl) ⟨8092583, by rfl⟩ : syracuseStep 10790111 = 16185167) B16185167
theorem B5686595 : Blo 1496068 5686595 := bstep (se 1 (by rfl) ⟨4264946, by rfl⟩ : syracuseStep 5686595 = 8529893) B8529893
theorem B3368303 : Blo 1496068 3368303 := bstep (se 1 (by rfl) ⟨2526227, by rfl⟩ : syracuseStep 3368303 = 5052455) B5052455
theorem B17524255 : Blo 1496068 17524255 := bstep (se 1 (by rfl) ⟨13143191, by rfl⟩ : syracuseStep 17524255 = 26286383) B26286383
theorem B77801057 : Blo 1496068 77801057 := bstep (se 2 (by rfl) ⟨29175396, by rfl⟩ : syracuseStep 77801057 = 58350793) B58350793
theorem B5687111 : Blo 1496068 5687111 := bstep (se 1 (by rfl) ⟨4265333, by rfl⟩ : syracuseStep 5687111 = 8530667) B8530667
theorem B3368915 : Blo 1496068 3368915 := bstep (se 1 (by rfl) ⟨2526686, by rfl⟩ : syracuseStep 3368915 = 5053373) B5053373
theorem B2525161 : Blo 1496068 2525161 := bstep (se 2 (by rfl) ⟨946935, by rfl⟩ : syracuseStep 2525161 = 1893871) B1893871
theorem B5687293 : Blo 1496068 5687293 := bstep (se 3 (by rfl) ⟨1066367, by rfl⟩ : syracuseStep 5687293 = 2132735) B2132735
theorem B2246747 : Blo 1496068 2246747 := bstep (se 1 (by rfl) ⟨1685060, by rfl⟩ : syracuseStep 2246747 = 3370121) B3370121
theorem B2246783 : Blo 1496068 2246783 := bstep (se 1 (by rfl) ⟨1685087, by rfl⟩ : syracuseStep 2246783 = 3370175) B3370175
theorem B3787145 : Blo 1496068 3787145 := bstep (se 2 (by rfl) ⟨1420179, by rfl⟩ : syracuseStep 3787145 = 2840359) B2840359
theorem B8636969 : Blo 1496068 8636969 := bstep (se 2 (by rfl) ⟨3238863, by rfl⟩ : syracuseStep 8636969 = 6477727) B6477727
theorem B1895167 : Blo 1496068 1895167 := bstep (se 1 (by rfl) ⟨1421375, by rfl⟩ : syracuseStep 1895167 = 2842751) B2842751
theorem B3369851 : Blo 1496068 3369851 := bstep (se 1 (by rfl) ⟨2527388, by rfl⟩ : syracuseStep 3369851 = 5054777) B5054777
theorem B3369887 : Blo 1496068 3369887 := bstep (se 1 (by rfl) ⟨2527415, by rfl⟩ : syracuseStep 3369887 = 5054831) B5054831
theorem B13650875 : Blo 1496068 13650875 := bstep (se 1 (by rfl) ⟨10238156, by rfl⟩ : syracuseStep 13650875 = 20476313) B20476313
theorem B2526511 : Blo 1496068 2526511 := bstep (se 1 (by rfl) ⟨1894883, by rfl⟩ : syracuseStep 2526511 = 3789767) B3789767
theorem B19713527 : Blo 1496068 19713527 := bstep (se 1 (by rfl) ⟨14785145, by rfl⟩ : syracuseStep 19713527 = 29570291) B29570291
theorem B3370607 : Blo 1496068 3370607 := bstep (se 1 (by rfl) ⟨2527955, by rfl⟩ : syracuseStep 3370607 = 5055911) B5055911
theorem B3788471 : Blo 1496068 3788471 := bstep (se 1 (by rfl) ⟨2841353, by rfl⟩ : syracuseStep 3788471 = 5682707) B5682707
theorem B10243849 : Blo 1496068 10243849 := bstep (se 2 (by rfl) ⟨3841443, by rfl⟩ : syracuseStep 10243849 = 7682887) B7682887
theorem B10784747 : Blo 1496068 10784747 := bstep (se 1 (by rfl) ⟨8088560, by rfl⟩ : syracuseStep 10784747 = 16177121) B16177121
theorem B3461383 : Blo 1496068 3461383 := bstep (se 1 (by rfl) ⟨2596037, by rfl⟩ : syracuseStep 3461383 = 5192075) B5192075
theorem B5050727 : Blo 1496068 5050727 := bstep (se 1 (by rfl) ⟨3788045, by rfl⟩ : syracuseStep 5050727 = 7576091) B7576091
theorem B1683967 : Blo 1496068 1683967 := bstep (se 1 (by rfl) ⟨1262975, by rfl⟩ : syracuseStep 1683967 = 2525951) B2525951
theorem B5051105 : Blo 1496068 5051105 := bstep (se 2 (by rfl) ⟨1894164, by rfl⟩ : syracuseStep 5051105 = 3788329) B3788329
theorem B7197599 : Blo 1496068 7197599 := bstep (se 1 (by rfl) ⟨5398199, by rfl⟩ : syracuseStep 7197599 = 10796399) B10796399
theorem B1496423 : Blo 1496068 1496423 := bstep (se 1 (by rfl) ⟨1122317, by rfl⟩ : syracuseStep 1496423 = 2244635) B2244635
theorem B7189985 : Blo 1496068 7189985 := bstep (se 2 (by rfl) ⟨2696244, by rfl⟩ : syracuseStep 7189985 = 5392489) B5392489
theorem B1496603 : Blo 1496068 1496603 := bstep (se 1 (by rfl) ⟨1122452, by rfl⟩ : syracuseStep 1496603 = 2244905) B2244905
theorem B3790415 : Blo 1496068 3790415 := bstep (se 1 (by rfl) ⟨2842811, by rfl⟩ : syracuseStep 3790415 = 5685623) B5685623
theorem B1496703 : Blo 1496068 1496703 := bstep (se 1 (by rfl) ⟨1122527, by rfl⟩ : syracuseStep 1496703 = 2245055) B2245055
theorem B4044455 : Blo 1496068 4044455 := bstep (se 1 (by rfl) ⟨3033341, by rfl⟩ : syracuseStep 4044455 = 6066683) B6066683
theorem B7190333 : Blo 1496068 7190333 := bstep (se 3 (by rfl) ⟨1348187, by rfl⟩ : syracuseStep 7190333 = 2696375) B2696375
theorem B6494059 : Blo 1496068 6494059 := bstep (se 1 (by rfl) ⟨4870544, by rfl⟩ : syracuseStep 6494059 = 9741089) B9741089
theorem B1497115 : Blo 1496068 1497115 := bstep (se 1 (by rfl) ⟨1122836, by rfl⟩ : syracuseStep 1497115 = 2245673) B2245673
theorem B2160751 : Blo 1496068 2160751 := bstep (se 1 (by rfl) ⟨1620563, by rfl⟩ : syracuseStep 2160751 = 3241127) B3241127
theorem B9099539 : Blo 1496068 9099539 := bstep (se 1 (by rfl) ⟨6824654, by rfl⟩ : syracuseStep 9099539 = 13649309) B13649309
theorem B7575929 : Blo 1496068 7575929 := bstep (se 2 (by rfl) ⟨2840973, by rfl⟩ : syracuseStep 7575929 = 5681947) B5681947
theorem B3791225 : Blo 1496068 3791225 := bstep (se 2 (by rfl) ⟨1421709, by rfl⟩ : syracuseStep 3791225 = 2843419) B2843419
theorem B11368997 : Blo 1496068 11368997 := bstep (se 4 (by rfl) ⟨1065843, by rfl⟩ : syracuseStep 11368997 = 2131687) B2131687
theorem B36420317 : Blo 1496068 36420317 := bstep (se 3 (by rfl) ⟨6828809, by rfl⟩ : syracuseStep 36420317 = 13657619) B13657619
theorem B59128573 : Blo 1496068 59128573 := bstep (se 3 (by rfl) ⟨11086607, by rfl⟩ : syracuseStep 59128573 = 22173215) B22173215
theorem B6830855 : Blo 1496068 6830855 := bstep (se 1 (by rfl) ⟨5123141, by rfl⟩ : syracuseStep 6830855 = 10246283) B10246283
theorem B6396839 : Blo 1496068 6396839 := bstep (se 1 (by rfl) ⟨4797629, by rfl⟩ : syracuseStep 6396839 = 9595259) B9595259
theorem B3595223 : Blo 1496068 3595223 := bstep (se 1 (by rfl) ⟨2696417, by rfl⟩ : syracuseStep 3595223 = 5392835) B5392835
theorem B43179581 : Blo 1496068 43179581 := bstep (se 3 (by rfl) ⟨8096171, by rfl⟩ : syracuseStep 43179581 = 16192343) B16192343
theorem B3366683 : Blo 1496068 3366683 := bstep (se 1 (by rfl) ⟨2525012, by rfl⟩ : syracuseStep 3366683 = 5050025) B5050025
theorem B2842607 : Blo 1496068 2842607 := bstep (se 1 (by rfl) ⟨2131955, by rfl⟩ : syracuseStep 2842607 = 4263911) B4263911
theorem B2244671 : Blo 1496068 2244671 := bstep (se 1 (by rfl) ⟨1683503, by rfl⟩ : syracuseStep 2244671 = 3367007) B3367007
theorem B2244791 : Blo 1496068 2244791 := bstep (se 1 (by rfl) ⟨1683593, by rfl⟩ : syracuseStep 2244791 = 3367187) B3367187
theorem B3367151 : Blo 1496068 3367151 := bstep (se 1 (by rfl) ⟨2525363, by rfl⟩ : syracuseStep 3367151 = 5050727) B5050727
theorem B12796379 : Blo 1496068 12796379 := bstep (se 1 (by rfl) ⟨9597284, by rfl⟩ : syracuseStep 12796379 = 19194569) B19194569
theorem B3367403 : Blo 1496068 3367403 := bstep (se 1 (by rfl) ⟨2525552, by rfl⟩ : syracuseStep 3367403 = 5051105) B5051105
theorem B2245289 : Blo 1496068 2245289 := bstep (se 2 (by rfl) ⟨841983, by rfl⟩ : syracuseStep 2245289 = 1683967) B1683967
theorem B2245535 : Blo 1496068 2245535 := bstep (se 1 (by rfl) ⟨1684151, by rfl⟩ : syracuseStep 2245535 = 3368303) B3368303
theorem B2696303 : Blo 1496068 2696303 := bstep (se 1 (by rfl) ⟨2022227, by rfl⟩ : syracuseStep 2696303 = 4044455) B4044455
theorem B4793555 : Blo 1496068 4793555 := bstep (se 1 (by rfl) ⟨3595166, by rfl⟩ : syracuseStep 4793555 = 7190333) B7190333
theorem B2245943 : Blo 1496068 2245943 := bstep (se 1 (by rfl) ⟨1684457, by rfl⟩ : syracuseStep 2245943 = 3368915) B3368915
theorem B2524763 : Blo 1496068 2524763 := bstep (se 1 (by rfl) ⟨1893572, by rfl⟩ : syracuseStep 2524763 = 3787145) B3787145
theorem B7579331 : Blo 1496068 7579331 := bstep (se 1 (by rfl) ⟨5684498, by rfl⟩ : syracuseStep 7579331 = 11368997) B11368997
theorem B3368681 : Blo 1496068 3368681 := bstep (se 2 (by rfl) ⟨1263255, by rfl⟩ : syracuseStep 3368681 = 2526511) B2526511
theorem B2246567 : Blo 1496068 2246567 := bstep (se 1 (by rfl) ⟨1684925, by rfl⟩ : syracuseStep 2246567 = 3369851) B3369851
theorem B2246591 : Blo 1496068 2246591 := bstep (se 1 (by rfl) ⟨1684943, by rfl⟩ : syracuseStep 2246591 = 3369887) B3369887
theorem B23365673 : Blo 1496068 23365673 := bstep (se 2 (by rfl) ⟨8762127, by rfl⟩ : syracuseStep 23365673 = 17524255) B17524255
theorem B13142351 : Blo 1496068 13142351 := bstep (se 1 (by rfl) ⟨9856763, by rfl⟩ : syracuseStep 13142351 = 19713527) B19713527
theorem B13658465 : Blo 1496068 13658465 := bstep (se 2 (by rfl) ⟨5121924, by rfl⟩ : syracuseStep 13658465 = 10243849) B10243849
theorem B2247071 : Blo 1496068 2247071 := bstep (se 1 (by rfl) ⟨1685303, by rfl⟩ : syracuseStep 2247071 = 3370607) B3370607
theorem B2525647 : Blo 1496068 2525647 := bstep (se 1 (by rfl) ⟨1894235, by rfl⟩ : syracuseStep 2525647 = 3788471) B3788471
theorem B9587261 : Blo 1496068 9587261 := bstep (se 3 (by rfl) ⟨1797611, by rfl⟩ : syracuseStep 9587261 = 3595223) B3595223
theorem B1895071 : Blo 1496068 1895071 := bstep (se 1 (by rfl) ⟨1421303, by rfl⟩ : syracuseStep 1895071 = 2842607) B2842607
theorem B3369707 : Blo 1496068 3369707 := bstep (se 1 (by rfl) ⟨2527280, by rfl⟩ : syracuseStep 3369707 = 5054561) B5054561
theorem B25570403 : Blo 1496068 25570403 := bstep (se 1 (by rfl) ⟨19177802, by rfl⟩ : syracuseStep 25570403 = 38355605) B38355605
theorem B28773629 : Blo 1496068 28773629 := bstep (se 3 (by rfl) ⟨5395055, by rfl⟩ : syracuseStep 28773629 = 10790111) B10790111
theorem B2526889 : Blo 1496068 2526889 := bstep (se 2 (by rfl) ⟨947583, by rfl⟩ : syracuseStep 2526889 = 1895167) B1895167
theorem B2526943 : Blo 1496068 2526943 := bstep (se 1 (by rfl) ⟨1895207, by rfl⟩ : syracuseStep 2526943 = 3790415) B3790415
theorem B51867371 : Blo 1496068 51867371 := bstep (se 1 (by rfl) ⟨38900528, by rfl⟩ : syracuseStep 51867371 = 77801057) B77801057
theorem B19173293 : Blo 1496068 19173293 := bstep (se 3 (by rfl) ⟨3594992, by rfl⟩ : syracuseStep 19173293 = 7189985) B7189985
theorem B18460709 : Blo 1496068 18460709 := bstep (se 4 (by rfl) ⟨1730691, by rfl⟩ : syracuseStep 18460709 = 3461383) B3461383
theorem B37924973 : Blo 1496068 37924973 := bstep (se 3 (by rfl) ⟨7110932, by rfl⟩ : syracuseStep 37924973 = 14221865) B14221865
theorem B6066359 : Blo 1496068 6066359 := bstep (se 1 (by rfl) ⟨4549769, by rfl⟩ : syracuseStep 6066359 = 9099539) B9099539
theorem B5050619 : Blo 1496068 5050619 := bstep (se 1 (by rfl) ⟨3787964, by rfl⟩ : syracuseStep 5050619 = 7575929) B7575929
theorem B2527483 : Blo 1496068 2527483 := bstep (se 1 (by rfl) ⟨1895612, by rfl⟩ : syracuseStep 2527483 = 3791225) B3791225
theorem B4264559 : Blo 1496068 4264559 := bstep (se 1 (by rfl) ⟨3198419, by rfl⟩ : syracuseStep 4264559 = 6396839) B6396839
theorem B1261409557 : Blo 1496068 1261409557 := bstep (se 6 (by rfl) ⟨29564286, by rfl⟩ : syracuseStep 1261409557 = 59128573) B59128573
theorem B7189831 : Blo 1496068 7189831 := bstep (se 1 (by rfl) ⟨5392373, by rfl⟩ : syracuseStep 7189831 = 10784747) B10784747
theorem B7583057 : Blo 1496068 7583057 := bstep (se 2 (by rfl) ⟨2843646, by rfl⟩ : syracuseStep 7583057 = 5687293) B5687293
theorem B2881001 : Blo 1496068 2881001 := bstep (se 2 (by rfl) ⟨1080375, by rfl⟩ : syracuseStep 2881001 = 2160751) B2160751
theorem B1496783 : Blo 1496068 1496783 := bstep (se 1 (by rfl) ⟨1122587, by rfl⟩ : syracuseStep 1496783 = 2245175) B2245175
theorem B1496807 : Blo 1496068 1496807 := bstep (se 1 (by rfl) ⟨1122605, by rfl⟩ : syracuseStep 1496807 = 2245211) B2245211
theorem B1496959 : Blo 1496068 1496959 := bstep (se 1 (by rfl) ⟨1122719, by rfl⟩ : syracuseStep 1496959 = 2245439) B2245439
theorem B3790759 : Blo 1496068 3790759 := bstep (se 1 (by rfl) ⟨2843069, by rfl⟩ : syracuseStep 3790759 = 5686139) B5686139
theorem B4798399 : Blo 1496068 4798399 := bstep (se 1 (by rfl) ⟨3598799, by rfl⟩ : syracuseStep 4798399 = 7197599) B7197599
theorem B1497055 : Blo 1496068 1497055 := bstep (se 1 (by rfl) ⟨1122791, by rfl⟩ : syracuseStep 1497055 = 2245583) B2245583
theorem B3791063 : Blo 1496068 3791063 := bstep (se 1 (by rfl) ⟨2843297, by rfl⟩ : syracuseStep 3791063 = 5686595) B5686595
theorem B3791407 : Blo 1496068 3791407 := bstep (se 1 (by rfl) ⟨2843555, by rfl⟩ : syracuseStep 3791407 = 5687111) B5687111
theorem B1497831 : Blo 1496068 1497831 := bstep (se 1 (by rfl) ⟨1123373, by rfl⟩ : syracuseStep 1497831 = 2246747) B2246747
theorem B1497855 : Blo 1496068 1497855 := bstep (se 1 (by rfl) ⟨1123391, by rfl⟩ : syracuseStep 1497855 = 2246783) B2246783
theorem B5757979 : Blo 1496068 5757979 := bstep (se 1 (by rfl) ⟨4318484, by rfl⟩ : syracuseStep 5757979 = 8636969) B8636969
theorem B24280211 : Blo 1496068 24280211 := bstep (se 1 (by rfl) ⟨18210158, by rfl⟩ : syracuseStep 24280211 = 36420317) B36420317
theorem B4553903 : Blo 1496068 4553903 := bstep (se 1 (by rfl) ⟨3415427, by rfl⟩ : syracuseStep 4553903 = 6830855) B6830855
theorem B34634981 : Blo 1496068 34634981 := bstep (se 4 (by rfl) ⟨3247029, by rfl⟩ : syracuseStep 34634981 = 6494059) B6494059
theorem B9100583 : Blo 1496068 9100583 := bstep (se 1 (by rfl) ⟨6825437, by rfl⟩ : syracuseStep 9100583 = 13650875) B13650875
theorem B28786387 : Blo 1496068 28786387 := bstep (se 1 (by rfl) ⟨21589790, by rfl⟩ : syracuseStep 28786387 = 43179581) B43179581
theorem B2244455 : Blo 1496068 2244455 := bstep (se 1 (by rfl) ⟨1683341, by rfl⟩ : syracuseStep 2244455 = 3366683) B3366683
theorem B3366881 : Blo 1496068 3366881 := bstep (se 2 (by rfl) ⟨1262580, by rfl⟩ : syracuseStep 3366881 = 2525161) B2525161
theorem B2244767 : Blo 1496068 2244767 := bstep (se 1 (by rfl) ⟨1683575, by rfl⟩ : syracuseStep 2244767 = 3367151) B3367151
theorem B3367079 : Blo 1496068 3367079 := bstep (se 1 (by rfl) ⟨2525309, by rfl⟩ : syracuseStep 3367079 = 5050619) B5050619
theorem B2244935 : Blo 1496068 2244935 := bstep (se 1 (by rfl) ⟨1683701, by rfl⟩ : syracuseStep 2244935 = 3367403) B3367403
theorem B2843039 : Blo 1496068 2843039 := bstep (se 1 (by rfl) ⟨2132279, by rfl⟩ : syracuseStep 2843039 = 4264559) B4264559
theorem B3367529 : Blo 1496068 3367529 := bstep (se 2 (by rfl) ⟨1262823, by rfl⟩ : syracuseStep 3367529 = 2525647) B2525647
theorem B5055209 : Blo 1496068 5055209 := bstep (se 2 (by rfl) ⟨1895703, by rfl⟩ : syracuseStep 5055209 = 3791407) B3791407
theorem B3195703 : Blo 1496068 3195703 := bstep (se 1 (by rfl) ⟨2396777, by rfl⟩ : syracuseStep 3195703 = 4793555) B4793555
theorem B5055371 : Blo 1496068 5055371 := bstep (se 1 (by rfl) ⟨3791528, by rfl⟩ : syracuseStep 5055371 = 7583057) B7583057
theorem B2245787 : Blo 1496068 2245787 := bstep (se 1 (by rfl) ⟨1684340, by rfl⟩ : syracuseStep 2245787 = 3368681) B3368681
theorem B7677305 : Blo 1496068 7677305 := bstep (se 2 (by rfl) ⟨2878989, by rfl⟩ : syracuseStep 7677305 = 5757979) B5757979
theorem B9586441 : Blo 1496068 9586441 := bstep (se 2 (by rfl) ⟨3594915, by rfl⟩ : syracuseStep 9586441 = 7189831) B7189831
theorem B2246471 : Blo 1496068 2246471 := bstep (se 1 (by rfl) ⟨1684853, by rfl⟩ : syracuseStep 2246471 = 3369707) B3369707
theorem B3369185 : Blo 1496068 3369185 := bstep (se 2 (by rfl) ⟨1263444, by rfl⟩ : syracuseStep 3369185 = 2526889) B2526889
theorem B38381849 : Blo 1496068 38381849 := bstep (se 2 (by rfl) ⟨14393193, by rfl⟩ : syracuseStep 38381849 = 28786387) B28786387
theorem B3369257 : Blo 1496068 3369257 := bstep (se 2 (by rfl) ⟨1263471, by rfl⟩ : syracuseStep 3369257 = 2526943) B2526943
theorem B12782195 : Blo 1496068 12782195 := bstep (se 1 (by rfl) ⟨9586646, by rfl⟩ : syracuseStep 12782195 = 19173293) B19173293
theorem B12307139 : Blo 1496068 12307139 := bstep (se 1 (by rfl) ⟨9230354, by rfl⟩ : syracuseStep 12307139 = 18460709) B18460709
theorem B25283315 : Blo 1496068 25283315 := bstep (se 1 (by rfl) ⟨18962486, by rfl⟩ : syracuseStep 25283315 = 37924973) B37924973
theorem B8530919 : Blo 1496068 8530919 := bstep (se 1 (by rfl) ⟨6398189, by rfl⟩ : syracuseStep 8530919 = 12796379) B12796379
theorem B3369977 : Blo 1496068 3369977 := bstep (se 2 (by rfl) ⟨1263741, by rfl⟩ : syracuseStep 3369977 = 2527483) B2527483
theorem B1797535 : Blo 1496068 1797535 := bstep (se 1 (by rfl) ⟨1348151, by rfl⟩ : syracuseStep 1797535 = 2696303) B2696303
theorem B2526761 : Blo 1496068 2526761 := bstep (se 2 (by rfl) ⟨947535, by rfl⟩ : syracuseStep 2526761 = 1895071) B1895071
theorem B1920667 : Blo 1496068 1920667 := bstep (se 1 (by rfl) ⟨1440500, by rfl⟩ : syracuseStep 1920667 = 2881001) B2881001
theorem B1683175 : Blo 1496068 1683175 := bstep (se 1 (by rfl) ⟨1262381, by rfl⟩ : syracuseStep 1683175 = 2524763) B2524763
theorem B15577115 : Blo 1496068 15577115 := bstep (se 1 (by rfl) ⟨11682836, by rfl⟩ : syracuseStep 15577115 = 23365673) B23365673
theorem B2527375 : Blo 1496068 2527375 := bstep (se 1 (by rfl) ⟨1895531, by rfl⟩ : syracuseStep 2527375 = 3791063) B3791063
theorem B8761567 : Blo 1496068 8761567 := bstep (se 1 (by rfl) ⟨6571175, by rfl⟩ : syracuseStep 8761567 = 13142351) B13142351
theorem B9105643 : Blo 1496068 9105643 := bstep (se 1 (by rfl) ⟨6829232, by rfl⟩ : syracuseStep 9105643 = 13658465) B13658465
theorem B1681879409 : Blo 1496068 1681879409 := bstep (se 2 (by rfl) ⟨630704778, by rfl⟩ : syracuseStep 1681879409 = 1261409557) B1261409557
theorem B3035935 : Blo 1496068 3035935 := bstep (se 1 (by rfl) ⟨2276951, by rfl⟩ : syracuseStep 3035935 = 4553903) B4553903
theorem B23089987 : Blo 1496068 23089987 := bstep (se 1 (by rfl) ⟨17317490, by rfl⟩ : syracuseStep 23089987 = 34634981) B34634981
theorem B19182419 : Blo 1496068 19182419 := bstep (se 1 (by rfl) ⟨14386814, by rfl⟩ : syracuseStep 19182419 = 28773629) B28773629
theorem B6067055 : Blo 1496068 6067055 := bstep (se 1 (by rfl) ⟨4550291, by rfl⟩ : syracuseStep 6067055 = 9100583) B9100583
theorem B1496303 : Blo 1496068 1496303 := bstep (se 1 (by rfl) ⟨1122227, by rfl⟩ : syracuseStep 1496303 = 2244455) B2244455
theorem B1496447 : Blo 1496068 1496447 := bstep (se 1 (by rfl) ⟨1122335, by rfl⟩ : syracuseStep 1496447 = 2244671) B2244671
theorem B4044239 : Blo 1496068 4044239 := bstep (se 1 (by rfl) ⟨3033179, by rfl⟩ : syracuseStep 4044239 = 6066359) B6066359
theorem B1496527 : Blo 1496068 1496527 := bstep (se 1 (by rfl) ⟨1122395, by rfl⟩ : syracuseStep 1496527 = 2244791) B2244791
theorem B1496859 : Blo 1496068 1496859 := bstep (se 1 (by rfl) ⟨1122644, by rfl⟩ : syracuseStep 1496859 = 2245289) B2245289
theorem B1497023 : Blo 1496068 1497023 := bstep (se 1 (by rfl) ⟨1122767, by rfl⟩ : syracuseStep 1497023 = 2245535) B2245535
theorem B1497295 : Blo 1496068 1497295 := bstep (se 1 (by rfl) ⟨1122971, by rfl⟩ : syracuseStep 1497295 = 2245943) B2245943
theorem B5052887 : Blo 1496068 5052887 := bstep (se 1 (by rfl) ⟨3789665, by rfl⟩ : syracuseStep 5052887 = 7579331) B7579331
theorem B1497711 : Blo 1496068 1497711 := bstep (se 1 (by rfl) ⟨1123283, by rfl⟩ : syracuseStep 1497711 = 2246567) B2246567
theorem B1497727 : Blo 1496068 1497727 := bstep (se 1 (by rfl) ⟨1123295, by rfl⟩ : syracuseStep 1497727 = 2246591) B2246591
theorem B25566029 : Blo 1496068 25566029 := bstep (se 3 (by rfl) ⟨4793630, by rfl⟩ : syracuseStep 25566029 = 9587261) B9587261
theorem B1498047 : Blo 1496068 1498047 := bstep (se 1 (by rfl) ⟨1123535, by rfl⟩ : syracuseStep 1498047 = 2247071) B2247071
theorem B17046935 : Blo 1496068 17046935 := bstep (se 1 (by rfl) ⟨12785201, by rfl⟩ : syracuseStep 17046935 = 25570403) B25570403
theorem B16186807 : Blo 1496068 16186807 := bstep (se 1 (by rfl) ⟨12140105, by rfl⟩ : syracuseStep 16186807 = 24280211) B24280211
theorem B34578247 : Blo 1496068 34578247 := bstep (se 1 (by rfl) ⟨25933685, by rfl⟩ : syracuseStep 34578247 = 51867371) B51867371
theorem B5054345 : Blo 1496068 5054345 := bstep (se 2 (by rfl) ⟨1895379, by rfl⟩ : syracuseStep 5054345 = 3790759) B3790759
theorem B6397865 : Blo 1496068 6397865 := bstep (se 2 (by rfl) ⟨2399199, by rfl⟩ : syracuseStep 6397865 = 4798399) B4798399
theorem B2244587 : Blo 1496068 2244587 := bstep (se 1 (by rfl) ⟨1683440, by rfl⟩ : syracuseStep 2244587 = 3366881) B3366881
theorem B2244719 : Blo 1496068 2244719 := bstep (se 1 (by rfl) ⟨1683539, by rfl⟩ : syracuseStep 2244719 = 3367079) B3367079
theorem B11682089 : Blo 1496068 11682089 := bstep (se 2 (by rfl) ⟨4380783, by rfl⟩ : syracuseStep 11682089 = 8761567) B8761567
theorem B12140857 : Blo 1496068 12140857 := bstep (se 2 (by rfl) ⟨4552821, by rfl⟩ : syracuseStep 12140857 = 9105643) B9105643
theorem B2245019 : Blo 1496068 2245019 := bstep (se 1 (by rfl) ⟨1683764, by rfl⟩ : syracuseStep 2245019 = 3367529) B3367529
theorem B12788279 : Blo 1496068 12788279 := bstep (se 1 (by rfl) ⟨9591209, by rfl⟩ : syracuseStep 12788279 = 19182419) B19182419
theorem B2696159 : Blo 1496068 2696159 := bstep (se 1 (by rfl) ⟨2022119, by rfl⟩ : syracuseStep 2696159 = 4044239) B4044239
theorem B4047913 : Blo 1496068 4047913 := bstep (se 2 (by rfl) ⟨1517967, by rfl⟩ : syracuseStep 4047913 = 3035935) B3035935
theorem B4260937 : Blo 1496068 4260937 := bstep (se 2 (by rfl) ⟨1597851, by rfl⟩ : syracuseStep 4260937 = 3195703) B3195703
theorem B30786649 : Blo 1496068 30786649 := bstep (se 2 (by rfl) ⟨11544993, by rfl⟩ : syracuseStep 30786649 = 23089987) B23089987
theorem B2246123 : Blo 1496068 2246123 := bstep (se 1 (by rfl) ⟨1684592, by rfl⟩ : syracuseStep 2246123 = 3369185) B3369185
theorem B2246171 : Blo 1496068 2246171 := bstep (se 1 (by rfl) ⟨1684628, by rfl⟩ : syracuseStep 2246171 = 3369257) B3369257
theorem B3368591 : Blo 1496068 3368591 := bstep (se 1 (by rfl) ⟨2526443, by rfl⟩ : syracuseStep 3368591 = 5052887) B5052887
theorem B8521463 : Blo 1496068 8521463 := bstep (se 1 (by rfl) ⟨6391097, by rfl⟩ : syracuseStep 8521463 = 12782195) B12782195
theorem B5687279 : Blo 1496068 5687279 := bstep (se 1 (by rfl) ⟨4265459, by rfl⟩ : syracuseStep 5687279 = 8530919) B8530919
theorem B2246651 : Blo 1496068 2246651 := bstep (se 1 (by rfl) ⟨1684988, by rfl⟩ : syracuseStep 2246651 = 3369977) B3369977
theorem B11364623 : Blo 1496068 11364623 := bstep (se 1 (by rfl) ⟨8523467, by rfl⟩ : syracuseStep 11364623 = 17046935) B17046935
theorem B86329637 : Blo 1496068 86329637 := bstep (se 4 (by rfl) ⟨8093403, by rfl⟩ : syracuseStep 86329637 = 16186807) B16186807
theorem B12781921 : Blo 1496068 12781921 := bstep (se 2 (by rfl) ⟨4793220, by rfl⟩ : syracuseStep 12781921 = 9586441) B9586441
theorem B3369563 : Blo 1496068 3369563 := bstep (se 1 (by rfl) ⟨2527172, by rfl⟩ : syracuseStep 3369563 = 5054345) B5054345
theorem B3369833 : Blo 1496068 3369833 := bstep (se 2 (by rfl) ⟨1263687, by rfl⟩ : syracuseStep 3369833 = 2527375) B2527375
theorem B3370139 : Blo 1496068 3370139 := bstep (se 1 (by rfl) ⟨2527604, by rfl⟩ : syracuseStep 3370139 = 5055209) B5055209
theorem B3370247 : Blo 1496068 3370247 := bstep (se 1 (by rfl) ⟨2527685, by rfl⟩ : syracuseStep 3370247 = 5055371) B5055371
theorem B7581437 : Blo 1496068 7581437 := bstep (se 3 (by rfl) ⟨1421519, by rfl⟩ : syracuseStep 7581437 = 2843039) B2843039
theorem B25587899 : Blo 1496068 25587899 := bstep (se 1 (by rfl) ⟨19190924, by rfl⟩ : syracuseStep 25587899 = 38381849) B38381849
theorem B8204759 : Blo 1496068 8204759 := bstep (se 1 (by rfl) ⟨6153569, by rfl⟩ : syracuseStep 8204759 = 12307139) B12307139
theorem B16855543 : Blo 1496068 16855543 := bstep (se 1 (by rfl) ⟨12641657, by rfl⟩ : syracuseStep 16855543 = 25283315) B25283315
theorem B2396713 : Blo 1496068 2396713 := bstep (se 2 (by rfl) ⟨898767, by rfl⟩ : syracuseStep 2396713 = 1797535) B1797535
theorem B17044019 : Blo 1496068 17044019 := bstep (se 1 (by rfl) ⟨12783014, by rfl⟩ : syracuseStep 17044019 = 25566029) B25566029
theorem B2560889 : Blo 1496068 2560889 := bstep (se 2 (by rfl) ⟨960333, by rfl⟩ : syracuseStep 2560889 = 1920667) B1920667
theorem B1684507 : Blo 1496068 1684507 := bstep (se 1 (by rfl) ⟨1263380, by rfl⟩ : syracuseStep 1684507 = 2526761) B2526761
theorem B4265243 : Blo 1496068 4265243 := bstep (se 1 (by rfl) ⟨3198932, by rfl⟩ : syracuseStep 4265243 = 6397865) B6397865
theorem B1496391 : Blo 1496068 1496391 := bstep (se 1 (by rfl) ⟨1122293, by rfl⟩ : syracuseStep 1496391 = 2244587) B2244587
theorem B41538973 : Blo 1496068 41538973 := bstep (se 3 (by rfl) ⟨7788557, by rfl⟩ : syracuseStep 41538973 = 15577115) B15577115
theorem B1496511 : Blo 1496068 1496511 := bstep (se 1 (by rfl) ⟨1122383, by rfl⟩ : syracuseStep 1496511 = 2244767) B2244767
theorem B1496623 : Blo 1496068 1496623 := bstep (se 1 (by rfl) ⟨1122467, by rfl⟩ : syracuseStep 1496623 = 2244935) B2244935
theorem B1121252939 : Blo 1496068 1121252939 := bstep (se 1 (by rfl) ⟨840939704, by rfl⟩ : syracuseStep 1121252939 = 1681879409) B1681879409
theorem B4044703 : Blo 1496068 4044703 := bstep (se 1 (by rfl) ⟨3033527, by rfl⟩ : syracuseStep 4044703 = 6067055) B6067055
theorem B1497191 : Blo 1496068 1497191 := bstep (se 1 (by rfl) ⟨1122893, by rfl⟩ : syracuseStep 1497191 = 2245787) B2245787
theorem B5118203 : Blo 1496068 5118203 := bstep (se 1 (by rfl) ⟨3838652, by rfl⟩ : syracuseStep 5118203 = 7677305) B7677305
theorem B1497647 : Blo 1496068 1497647 := bstep (se 1 (by rfl) ⟨1123235, by rfl⟩ : syracuseStep 1497647 = 2246471) B2246471
theorem B2244233 : Blo 1496068 2244233 := bstep (se 2 (by rfl) ⟨841587, by rfl⟩ : syracuseStep 2244233 = 1683175) B1683175
theorem B46104329 : Blo 1496068 46104329 := bstep (se 2 (by rfl) ⟨17289123, by rfl⟩ : syracuseStep 46104329 = 34578247) B34578247
theorem B11362679 : Blo 1496068 11362679 := bstep (se 1 (by rfl) ⟨8522009, by rfl⟩ : syracuseStep 11362679 = 17044019) B17044019
theorem B16187809 : Blo 1496068 16187809 := bstep (se 2 (by rfl) ⟨6070428, by rfl⟩ : syracuseStep 16187809 = 12140857) B12140857
theorem B3195617 : Blo 1496068 3195617 := bstep (se 2 (by rfl) ⟨1198356, by rfl⟩ : syracuseStep 3195617 = 2396713) B2396713
theorem B2843495 : Blo 1496068 2843495 := bstep (se 1 (by rfl) ⟨2132621, by rfl⟩ : syracuseStep 2843495 = 4265243) B4265243
theorem B2245727 : Blo 1496068 2245727 := bstep (se 1 (by rfl) ⟨1684295, by rfl⟩ : syracuseStep 2245727 = 3368591) B3368591
theorem B2246009 : Blo 1496068 2246009 := bstep (se 2 (by rfl) ⟨842253, by rfl⟩ : syracuseStep 2246009 = 1684507) B1684507
theorem B2246375 : Blo 1496068 2246375 := bstep (se 1 (by rfl) ⟨1684781, by rfl⟩ : syracuseStep 2246375 = 3369563) B3369563
theorem B2246555 : Blo 1496068 2246555 := bstep (se 1 (by rfl) ⟨1684916, by rfl⟩ : syracuseStep 2246555 = 3369833) B3369833
theorem B2246759 : Blo 1496068 2246759 := bstep (se 1 (by rfl) ⟨1685069, by rfl⟩ : syracuseStep 2246759 = 3370139) B3370139
theorem B2246831 : Blo 1496068 2246831 := bstep (se 1 (by rfl) ⟨1685123, by rfl⟩ : syracuseStep 2246831 = 3370247) B3370247
theorem B5392937 : Blo 1496068 5392937 := bstep (se 2 (by rfl) ⟨2022351, by rfl⟩ : syracuseStep 5392937 = 4044703) B4044703
theorem B17058599 : Blo 1496068 17058599 := bstep (se 1 (by rfl) ⟨12793949, by rfl⟩ : syracuseStep 17058599 = 25587899) B25587899
theorem B21588869 : Blo 1496068 21588869 := bstep (se 4 (by rfl) ⟨2023956, by rfl⟩ : syracuseStep 21588869 = 4047913) B4047913
theorem B17042561 : Blo 1496068 17042561 := bstep (se 2 (by rfl) ⟨6390960, by rfl⟩ : syracuseStep 17042561 = 12781921) B12781921
theorem B164195461 : Blo 1496068 164195461 := bstep (se 4 (by rfl) ⟨15393324, by rfl⟩ : syracuseStep 164195461 = 30786649) B30786649
theorem B1707259 : Blo 1496068 1707259 := bstep (se 1 (by rfl) ⟨1280444, by rfl⟩ : syracuseStep 1707259 = 2560889) B2560889
theorem B1797439 : Blo 1496068 1797439 := bstep (se 1 (by rfl) ⟨1348079, by rfl⟩ : syracuseStep 1797439 = 2696159) B2696159
theorem B22474057 : Blo 1496068 22474057 := bstep (se 2 (by rfl) ⟨8427771, by rfl⟩ : syracuseStep 22474057 = 16855543) B16855543
theorem B5680975 : Blo 1496068 5680975 := bstep (se 1 (by rfl) ⟨4260731, by rfl⟩ : syracuseStep 5680975 = 8521463) B8521463
theorem B5681249 : Blo 1496068 5681249 := bstep (se 2 (by rfl) ⟨2130468, by rfl⟩ : syracuseStep 5681249 = 4260937) B4260937
theorem B3412135 : Blo 1496068 3412135 := bstep (se 1 (by rfl) ⟨2559101, by rfl⟩ : syracuseStep 3412135 = 5118203) B5118203
theorem B57553091 : Blo 1496068 57553091 := bstep (se 1 (by rfl) ⟨43164818, by rfl⟩ : syracuseStep 57553091 = 86329637) B86329637
theorem B1496155 : Blo 1496068 1496155 := bstep (se 1 (by rfl) ⟨1122116, by rfl⟩ : syracuseStep 1496155 = 2244233) B2244233
theorem B1496479 : Blo 1496068 1496479 := bstep (se 1 (by rfl) ⟨1122359, by rfl⟩ : syracuseStep 1496479 = 2244719) B2244719
theorem B7788059 : Blo 1496068 7788059 := bstep (se 1 (by rfl) ⟨5841044, by rfl⟩ : syracuseStep 7788059 = 11682089) B11682089
theorem B1496679 : Blo 1496068 1496679 := bstep (se 1 (by rfl) ⟨1122509, by rfl⟩ : syracuseStep 1496679 = 2245019) B2245019
theorem B5469839 : Blo 1496068 5469839 := bstep (se 1 (by rfl) ⟨4102379, by rfl⟩ : syracuseStep 5469839 = 8204759) B8204759
theorem B8525519 : Blo 1496068 8525519 := bstep (se 1 (by rfl) ⟨6394139, by rfl⟩ : syracuseStep 8525519 = 12788279) B12788279
theorem B1497415 : Blo 1496068 1497415 := bstep (se 1 (by rfl) ⟨1123061, by rfl⟩ : syracuseStep 1497415 = 2246123) B2246123
theorem B1497447 : Blo 1496068 1497447 := bstep (se 1 (by rfl) ⟨1123085, by rfl⟩ : syracuseStep 1497447 = 2246171) B2246171
theorem B747501959 : Blo 1496068 747501959 := bstep (se 1 (by rfl) ⟨560626469, by rfl⟩ : syracuseStep 747501959 = 1121252939) B1121252939
theorem B3791519 : Blo 1496068 3791519 := bstep (se 1 (by rfl) ⟨2843639, by rfl⟩ : syracuseStep 3791519 = 5687279) B5687279
theorem B1497767 : Blo 1496068 1497767 := bstep (se 1 (by rfl) ⟨1123325, by rfl⟩ : syracuseStep 1497767 = 2246651) B2246651
theorem B7576415 : Blo 1496068 7576415 := bstep (se 1 (by rfl) ⟨5682311, by rfl⟩ : syracuseStep 7576415 = 11364623) B11364623
theorem B55385297 : Blo 1496068 55385297 := bstep (se 2 (by rfl) ⟨20769486, by rfl⟩ : syracuseStep 55385297 = 41538973) B41538973
theorem B5054291 : Blo 1496068 5054291 := bstep (se 1 (by rfl) ⟨3790718, by rfl⟩ : syracuseStep 5054291 = 7581437) B7581437
theorem B30736219 : Blo 1496068 30736219 := bstep (se 1 (by rfl) ⟨23052164, by rfl⟩ : syracuseStep 30736219 = 46104329) B46104329
theorem B3646559 : Blo 1496068 3646559 := bstep (se 1 (by rfl) ⟨2734919, by rfl⟩ : syracuseStep 3646559 = 5469839) B5469839
theorem B11372399 : Blo 1496068 11372399 := bstep (se 1 (by rfl) ⟨8529299, by rfl⟩ : syracuseStep 11372399 = 17058599) B17058599
theorem B8521645 : Blo 1496068 8521645 := bstep (se 3 (by rfl) ⟨1597808, by rfl⟩ : syracuseStep 8521645 = 3195617) B3195617
theorem B36923531 : Blo 1496068 36923531 := bstep (se 1 (by rfl) ⟨27692648, by rfl⟩ : syracuseStep 36923531 = 55385297) B55385297
theorem B3369527 : Blo 1496068 3369527 := bstep (se 1 (by rfl) ⟨2527145, by rfl⟩ : syracuseStep 3369527 = 5054291) B5054291
theorem B3787499 : Blo 1496068 3787499 := bstep (se 1 (by rfl) ⟨2840624, by rfl⟩ : syracuseStep 3787499 = 5681249) B5681249
theorem B4549513 : Blo 1496068 4549513 := bstep (se 2 (by rfl) ⟨1706067, by rfl⟩ : syracuseStep 4549513 = 3412135) B3412135
theorem B1895663 : Blo 1496068 1895663 := bstep (se 1 (by rfl) ⟨1421747, by rfl⟩ : syracuseStep 1895663 = 2843495) B2843495
theorem B14381165 : Blo 1496068 14381165 := bstep (se 3 (by rfl) ⟨2696468, by rfl⟩ : syracuseStep 14381165 = 5392937) B5392937
theorem B218927281 : Blo 1496068 218927281 := bstep (se 2 (by rfl) ⟨82097730, by rfl⟩ : syracuseStep 218927281 = 164195461) B164195461
theorem B2396585 : Blo 1496068 2396585 := bstep (se 2 (by rfl) ⟨898719, by rfl⟩ : syracuseStep 2396585 = 1797439) B1797439
theorem B2527679 : Blo 1496068 2527679 := bstep (se 1 (by rfl) ⟨1895759, by rfl⟩ : syracuseStep 2527679 = 3791519) B3791519
theorem B5050943 : Blo 1496068 5050943 := bstep (se 1 (by rfl) ⟨3788207, by rfl⟩ : syracuseStep 5050943 = 7576415) B7576415
theorem B7574633 : Blo 1496068 7574633 := bstep (se 2 (by rfl) ⟨2840487, by rfl⟩ : syracuseStep 7574633 = 5680975) B5680975
theorem B40981625 : Blo 1496068 40981625 := bstep (se 2 (by rfl) ⟨15368109, by rfl⟩ : syracuseStep 40981625 = 30736219) B30736219
theorem B38368727 : Blo 1496068 38368727 := bstep (se 1 (by rfl) ⟨28776545, by rfl⟩ : syracuseStep 38368727 = 57553091) B57553091
theorem B7575119 : Blo 1496068 7575119 := bstep (se 1 (by rfl) ⟨5681339, by rfl⟩ : syracuseStep 7575119 = 11362679) B11362679
theorem B21583745 : Blo 1496068 21583745 := bstep (se 2 (by rfl) ⟨8093904, by rfl⟩ : syracuseStep 21583745 = 16187809) B16187809
theorem B1497151 : Blo 1496068 1497151 := bstep (se 1 (by rfl) ⟨1122863, by rfl⟩ : syracuseStep 1497151 = 2245727) B2245727
theorem B1497339 : Blo 1496068 1497339 := bstep (se 1 (by rfl) ⟨1123004, by rfl⟩ : syracuseStep 1497339 = 2246009) B2246009
theorem B5192039 : Blo 1496068 5192039 := bstep (se 1 (by rfl) ⟨3894029, by rfl⟩ : syracuseStep 5192039 = 7788059) B7788059
theorem B5683679 : Blo 1496068 5683679 := bstep (se 1 (by rfl) ⟨4262759, by rfl⟩ : syracuseStep 5683679 = 8525519) B8525519
theorem B1497583 : Blo 1496068 1497583 := bstep (se 1 (by rfl) ⟨1123187, by rfl⟩ : syracuseStep 1497583 = 2246375) B2246375
theorem B1497703 : Blo 1496068 1497703 := bstep (se 1 (by rfl) ⟨1123277, by rfl⟩ : syracuseStep 1497703 = 2246555) B2246555
theorem B1497839 : Blo 1496068 1497839 := bstep (se 1 (by rfl) ⟨1123379, by rfl⟩ : syracuseStep 1497839 = 2246759) B2246759
theorem B1497887 : Blo 1496068 1497887 := bstep (se 1 (by rfl) ⟨1123415, by rfl⟩ : syracuseStep 1497887 = 2246831) B2246831
theorem B498334639 : Blo 1496068 498334639 := bstep (se 1 (by rfl) ⟨373750979, by rfl⟩ : syracuseStep 498334639 = 747501959) B747501959
theorem B2276345 : Blo 1496068 2276345 := bstep (se 2 (by rfl) ⟨853629, by rfl⟩ : syracuseStep 2276345 = 1707259) B1707259
theorem B29965409 : Blo 1496068 29965409 := bstep (se 2 (by rfl) ⟨11237028, by rfl⟩ : syracuseStep 29965409 = 22474057) B22474057
theorem B14392579 : Blo 1496068 14392579 := bstep (se 1 (by rfl) ⟨10794434, by rfl⟩ : syracuseStep 14392579 = 21588869) B21588869
theorem B11361707 : Blo 1496068 11361707 := bstep (se 1 (by rfl) ⟨8521280, by rfl⟩ : syracuseStep 11361707 = 17042561) B17042561
theorem B3367295 : Blo 1496068 3367295 := bstep (se 1 (by rfl) ⟨2525471, by rfl⟩ : syracuseStep 3367295 = 5050943) B5050943
theorem B5055101 : Blo 1496068 5055101 := bstep (se 3 (by rfl) ⟨947831, by rfl⟩ : syracuseStep 5055101 = 1895663) B1895663
theorem B27321083 : Blo 1496068 27321083 := bstep (se 1 (by rfl) ⟨20490812, by rfl⟩ : syracuseStep 27321083 = 40981625) B40981625
theorem B13845437 : Blo 1496068 13845437 := bstep (se 3 (by rfl) ⟨2596019, by rfl⟩ : syracuseStep 13845437 = 5192039) B5192039
theorem B6390893 : Blo 1496068 6390893 := bstep (se 3 (by rfl) ⟨1198292, by rfl⟩ : syracuseStep 6390893 = 2396585) B2396585
theorem B664446185 : Blo 1496068 664446185 := bstep (se 2 (by rfl) ⟨249167319, by rfl⟩ : syracuseStep 664446185 = 498334639) B498334639
theorem B2246351 : Blo 1496068 2246351 := bstep (se 1 (by rfl) ⟨1684763, by rfl⟩ : syracuseStep 2246351 = 3369527) B3369527
theorem B2524999 : Blo 1496068 2524999 := bstep (se 1 (by rfl) ⟨1893749, by rfl⟩ : syracuseStep 2524999 = 3787499) B3787499
theorem B1517563 : Blo 1496068 1517563 := bstep (se 1 (by rfl) ⟨1138172, by rfl⟩ : syracuseStep 1517563 = 2276345) B2276345
theorem B9587443 : Blo 1496068 9587443 := bstep (se 1 (by rfl) ⟨7190582, by rfl⟩ : syracuseStep 9587443 = 14381165) B14381165
theorem B98462749 : Blo 1496068 98462749 := bstep (se 3 (by rfl) ⟨18461765, by rfl⟩ : syracuseStep 98462749 = 36923531) B36923531
theorem B5049755 : Blo 1496068 5049755 := bstep (se 1 (by rfl) ⟨3787316, by rfl⟩ : syracuseStep 5049755 = 7574633) B7574633
theorem B25579151 : Blo 1496068 25579151 := bstep (se 1 (by rfl) ⟨19184363, by rfl⟩ : syracuseStep 25579151 = 38368727) B38368727
theorem B5050079 : Blo 1496068 5050079 := bstep (se 1 (by rfl) ⟨3787559, by rfl⟩ : syracuseStep 5050079 = 7575119) B7575119
theorem B6066017 : Blo 1496068 6066017 := bstep (se 2 (by rfl) ⟨2274756, by rfl⟩ : syracuseStep 6066017 = 4549513) B4549513
theorem B7581599 : Blo 1496068 7581599 := bstep (se 1 (by rfl) ⟨5686199, by rfl⟩ : syracuseStep 7581599 = 11372399) B11372399
theorem B14389163 : Blo 1496068 14389163 := bstep (se 1 (by rfl) ⟨10791872, by rfl⟩ : syracuseStep 14389163 = 21583745) B21583745
theorem B3789119 : Blo 1496068 3789119 := bstep (se 1 (by rfl) ⟨2841839, by rfl⟩ : syracuseStep 3789119 = 5683679) B5683679
theorem B19190105 : Blo 1496068 19190105 := bstep (se 2 (by rfl) ⟨7196289, by rfl⟩ : syracuseStep 19190105 = 14392579) B14392579
theorem B19976939 : Blo 1496068 19976939 := bstep (se 1 (by rfl) ⟨14982704, by rfl⟩ : syracuseStep 19976939 = 29965409) B29965409
theorem B7574471 : Blo 1496068 7574471 := bstep (se 1 (by rfl) ⟨5680853, by rfl⟩ : syracuseStep 7574471 = 11361707) B11361707
theorem B291903041 : Blo 1496068 291903041 := bstep (se 2 (by rfl) ⟨109463640, by rfl⟩ : syracuseStep 291903041 = 218927281) B218927281
theorem B1685119 : Blo 1496068 1685119 := bstep (se 1 (by rfl) ⟨1263839, by rfl⟩ : syracuseStep 1685119 = 2527679) B2527679
theorem B2431039 : Blo 1496068 2431039 := bstep (se 1 (by rfl) ⟨1823279, by rfl⟩ : syracuseStep 2431039 = 3646559) B3646559
theorem B11362193 : Blo 1496068 11362193 := bstep (se 2 (by rfl) ⟨4260822, by rfl⟩ : syracuseStep 11362193 = 8521645) B8521645
theorem B2244863 : Blo 1496068 2244863 := bstep (se 1 (by rfl) ⟨1683647, by rfl⟩ : syracuseStep 2244863 = 3367295) B3367295
theorem B4260595 : Blo 1496068 4260595 := bstep (se 1 (by rfl) ⟨3195446, by rfl⟩ : syracuseStep 4260595 = 6390893) B6390893
theorem B194602027 : Blo 1496068 194602027 := bstep (se 1 (by rfl) ⟨145951520, by rfl⟩ : syracuseStep 194602027 = 291903041) B291903041
theorem B2246825 : Blo 1496068 2246825 := bstep (se 2 (by rfl) ⟨842559, by rfl⟩ : syracuseStep 2246825 = 1685119) B1685119
theorem B2526079 : Blo 1496068 2526079 := bstep (se 1 (by rfl) ⟨1894559, by rfl⟩ : syracuseStep 2526079 = 3789119) B3789119
theorem B3370067 : Blo 1496068 3370067 := bstep (se 1 (by rfl) ⟨2527550, by rfl⟩ : syracuseStep 3370067 = 5055101) B5055101
theorem B18214055 : Blo 1496068 18214055 := bstep (se 1 (by rfl) ⟨13660541, by rfl⟩ : syracuseStep 18214055 = 27321083) B27321083
theorem B5049647 : Blo 1496068 5049647 := bstep (se 1 (by rfl) ⟨3787235, by rfl⟩ : syracuseStep 5049647 = 7574471) B7574471
theorem B12783257 : Blo 1496068 12783257 := bstep (se 2 (by rfl) ⟨4793721, by rfl⟩ : syracuseStep 12783257 = 9587443) B9587443
theorem B17052767 : Blo 1496068 17052767 := bstep (se 1 (by rfl) ⟨12789575, by rfl⟩ : syracuseStep 17052767 = 25579151) B25579151
theorem B4044011 : Blo 1496068 4044011 := bstep (se 1 (by rfl) ⟨3033008, by rfl⟩ : syracuseStep 4044011 = 6066017) B6066017
theorem B7574795 : Blo 1496068 7574795 := bstep (se 1 (by rfl) ⟨5681096, by rfl⟩ : syracuseStep 7574795 = 11362193) B11362193
theorem B3241385 : Blo 1496068 3241385 := bstep (se 2 (by rfl) ⟨1215519, by rfl⟩ : syracuseStep 3241385 = 2431039) B2431039
theorem B12793403 : Blo 1496068 12793403 := bstep (se 1 (by rfl) ⟨9595052, by rfl⟩ : syracuseStep 12793403 = 19190105) B19190105
theorem B13317959 : Blo 1496068 13317959 := bstep (se 1 (by rfl) ⟨9988469, by rfl⟩ : syracuseStep 13317959 = 19976939) B19976939
theorem B9230291 : Blo 1496068 9230291 := bstep (se 1 (by rfl) ⟨6922718, by rfl⟩ : syracuseStep 9230291 = 13845437) B13845437
theorem B442964123 : Blo 1496068 442964123 := bstep (se 1 (by rfl) ⟨332223092, by rfl⟩ : syracuseStep 442964123 = 664446185) B664446185
theorem B1497567 : Blo 1496068 1497567 := bstep (se 1 (by rfl) ⟨1123175, by rfl⟩ : syracuseStep 1497567 = 2246351) B2246351
theorem B131283665 : Blo 1496068 131283665 := bstep (se 2 (by rfl) ⟨49231374, by rfl⟩ : syracuseStep 131283665 = 98462749) B98462749
theorem B3366503 : Blo 1496068 3366503 := bstep (se 1 (by rfl) ⟨2524877, by rfl⟩ : syracuseStep 3366503 = 5049755) B5049755
theorem B3366665 : Blo 1496068 3366665 := bstep (se 2 (by rfl) ⟨1262499, by rfl⟩ : syracuseStep 3366665 = 2524999) B2524999
theorem B3366719 : Blo 1496068 3366719 := bstep (se 1 (by rfl) ⟨2525039, by rfl⟩ : syracuseStep 3366719 = 5050079) B5050079
theorem B5054399 : Blo 1496068 5054399 := bstep (se 1 (by rfl) ⟨3790799, by rfl⟩ : syracuseStep 5054399 = 7581599) B7581599
theorem B9592775 : Blo 1496068 9592775 := bstep (se 1 (by rfl) ⟨7194581, by rfl⟩ : syracuseStep 9592775 = 14389163) B14389163
theorem B2023417 : Blo 1496068 2023417 := bstep (se 2 (by rfl) ⟨758781, by rfl⟩ : syracuseStep 2023417 = 1517563) B1517563
theorem B8528935 : Blo 1496068 8528935 := bstep (se 1 (by rfl) ⟨6396701, by rfl⟩ : syracuseStep 8528935 = 12793403) B12793403
theorem B3368105 : Blo 1496068 3368105 := bstep (se 2 (by rfl) ⟨1263039, by rfl⟩ : syracuseStep 3368105 = 2526079) B2526079
theorem B6153527 : Blo 1496068 6153527 := bstep (se 1 (by rfl) ⟨4615145, by rfl⟩ : syracuseStep 6153527 = 9230291) B9230291
theorem B2246711 : Blo 1496068 2246711 := bstep (se 1 (by rfl) ⟨1685033, by rfl⟩ : syracuseStep 2246711 = 3370067) B3370067
theorem B12142703 : Blo 1496068 12142703 := bstep (se 1 (by rfl) ⟨9107027, by rfl⟩ : syracuseStep 12142703 = 18214055) B18214055
theorem B35514557 : Blo 1496068 35514557 := bstep (se 3 (by rfl) ⟨6658979, by rfl⟩ : syracuseStep 35514557 = 13317959) B13317959
theorem B8522171 : Blo 1496068 8522171 := bstep (se 1 (by rfl) ⟨6391628, by rfl⟩ : syracuseStep 8522171 = 12783257) B12783257
theorem B3369599 : Blo 1496068 3369599 := bstep (se 1 (by rfl) ⟨2527199, by rfl⟩ : syracuseStep 3369599 = 5054399) B5054399
theorem B2697889 : Blo 1496068 2697889 := bstep (se 2 (by rfl) ⟨1011708, by rfl⟩ : syracuseStep 2697889 = 2023417) B2023417
theorem B10784029 : Blo 1496068 10784029 := bstep (se 3 (by rfl) ⟨2022005, by rfl⟩ : syracuseStep 10784029 = 4044011) B4044011
theorem B5049863 : Blo 1496068 5049863 := bstep (se 1 (by rfl) ⟨3787397, by rfl⟩ : syracuseStep 5049863 = 7574795) B7574795
theorem B5680793 : Blo 1496068 5680793 := bstep (se 2 (by rfl) ⟨2130297, by rfl⟩ : syracuseStep 5680793 = 4260595) B4260595
theorem B259469369 : Blo 1496068 259469369 := bstep (se 2 (by rfl) ⟨97301013, by rfl⟩ : syracuseStep 259469369 = 194602027) B194602027
theorem B295309415 : Blo 1496068 295309415 := bstep (se 1 (by rfl) ⟨221482061, by rfl⟩ : syracuseStep 295309415 = 442964123) B442964123
theorem B6395183 : Blo 1496068 6395183 := bstep (se 1 (by rfl) ⟨4796387, by rfl⟩ : syracuseStep 6395183 = 9592775) B9592775
theorem B1496575 : Blo 1496068 1496575 := bstep (se 1 (by rfl) ⟨1122431, by rfl⟩ : syracuseStep 1496575 = 2244863) B2244863
theorem B11368511 : Blo 1496068 11368511 := bstep (se 1 (by rfl) ⟨8526383, by rfl⟩ : syracuseStep 11368511 = 17052767) B17052767
theorem B2160923 : Blo 1496068 2160923 := bstep (se 1 (by rfl) ⟨1620692, by rfl⟩ : syracuseStep 2160923 = 3241385) B3241385
theorem B1497883 : Blo 1496068 1497883 := bstep (se 1 (by rfl) ⟨1123412, by rfl⟩ : syracuseStep 1497883 = 2246825) B2246825
theorem B87522443 : Blo 1496068 87522443 := bstep (se 1 (by rfl) ⟨65641832, by rfl⟩ : syracuseStep 87522443 = 131283665) B131283665
theorem B3366431 : Blo 1496068 3366431 := bstep (se 1 (by rfl) ⟨2524823, by rfl⟩ : syracuseStep 3366431 = 5049647) B5049647
theorem B2244335 : Blo 1496068 2244335 := bstep (se 1 (by rfl) ⟨1683251, by rfl⟩ : syracuseStep 2244335 = 3366503) B3366503
theorem B2244443 : Blo 1496068 2244443 := bstep (se 1 (by rfl) ⟨1683332, by rfl⟩ : syracuseStep 2244443 = 3366665) B3366665
theorem B2244479 : Blo 1496068 2244479 := bstep (se 1 (by rfl) ⟨1683359, by rfl⟩ : syracuseStep 2244479 = 3366719) B3366719
theorem B2245403 : Blo 1496068 2245403 := bstep (se 1 (by rfl) ⟨1684052, by rfl⟩ : syracuseStep 2245403 = 3368105) B3368105
theorem B16409405 : Blo 1496068 16409405 := bstep (se 3 (by rfl) ⟨3076763, by rfl⟩ : syracuseStep 16409405 = 6153527) B6153527
theorem B3597185 : Blo 1496068 3597185 := bstep (se 2 (by rfl) ⟨1348944, by rfl⟩ : syracuseStep 3597185 = 2697889) B2697889
theorem B7579007 : Blo 1496068 7579007 := bstep (se 1 (by rfl) ⟨5684255, by rfl⟩ : syracuseStep 7579007 = 11368511) B11368511
theorem B11371913 : Blo 1496068 11371913 := bstep (se 2 (by rfl) ⟨4264467, by rfl⟩ : syracuseStep 11371913 = 8528935) B8528935
theorem B8095135 : Blo 1496068 8095135 := bstep (se 1 (by rfl) ⟨6071351, by rfl⟩ : syracuseStep 8095135 = 12142703) B12142703
theorem B23676371 : Blo 1496068 23676371 := bstep (se 1 (by rfl) ⟨17757278, by rfl⟩ : syracuseStep 23676371 = 35514557) B35514557
theorem B14378705 : Blo 1496068 14378705 := bstep (se 2 (by rfl) ⟨5392014, by rfl⟩ : syracuseStep 14378705 = 10784029) B10784029
theorem B2246399 : Blo 1496068 2246399 := bstep (se 1 (by rfl) ⟨1684799, by rfl⟩ : syracuseStep 2246399 = 3369599) B3369599
theorem B3787195 : Blo 1496068 3787195 := bstep (se 1 (by rfl) ⟨2840396, by rfl⟩ : syracuseStep 3787195 = 5680793) B5680793
theorem B196872943 : Blo 1496068 196872943 := bstep (se 1 (by rfl) ⟨147654707, by rfl⟩ : syracuseStep 196872943 = 295309415) B295309415
theorem B5762461 : Blo 1496068 5762461 := bstep (se 3 (by rfl) ⟨1080461, by rfl⟩ : syracuseStep 5762461 = 2160923) B2160923
theorem B4263455 : Blo 1496068 4263455 := bstep (se 1 (by rfl) ⟨3197591, by rfl⟩ : syracuseStep 4263455 = 6395183) B6395183
theorem B5681447 : Blo 1496068 5681447 := bstep (se 1 (by rfl) ⟨4261085, by rfl⟩ : syracuseStep 5681447 = 8522171) B8522171
theorem B58348295 : Blo 1496068 58348295 := bstep (se 1 (by rfl) ⟨43761221, by rfl⟩ : syracuseStep 58348295 = 87522443) B87522443
theorem B1496223 : Blo 1496068 1496223 := bstep (se 1 (by rfl) ⟨1122167, by rfl⟩ : syracuseStep 1496223 = 2244335) B2244335
theorem B1496295 : Blo 1496068 1496295 := bstep (se 1 (by rfl) ⟨1122221, by rfl⟩ : syracuseStep 1496295 = 2244443) B2244443
theorem B1496319 : Blo 1496068 1496319 := bstep (se 1 (by rfl) ⟨1122239, by rfl⟩ : syracuseStep 1496319 = 2244479) B2244479
theorem B172979579 : Blo 1496068 172979579 := bstep (se 1 (by rfl) ⟨129734684, by rfl⟩ : syracuseStep 172979579 = 259469369) B259469369
theorem B1497807 : Blo 1496068 1497807 := bstep (se 1 (by rfl) ⟨1123355, by rfl⟩ : syracuseStep 1497807 = 2246711) B2246711
theorem B3366575 : Blo 1496068 3366575 := bstep (se 1 (by rfl) ⟨2524931, by rfl⟩ : syracuseStep 3366575 = 5049863) B5049863
theorem B2244287 : Blo 1496068 2244287 := bstep (se 1 (by rfl) ⟨1683215, by rfl⟩ : syracuseStep 2244287 = 3366431) B3366431
theorem B115319719 : Blo 1496068 115319719 := bstep (se 1 (by rfl) ⟨86489789, by rfl⟩ : syracuseStep 115319719 = 172979579) B172979579
theorem B262497257 : Blo 1496068 262497257 := bstep (se 2 (by rfl) ⟨98436471, by rfl⟩ : syracuseStep 262497257 = 196872943) B196872943
theorem B9585803 : Blo 1496068 9585803 := bstep (se 1 (by rfl) ⟨7189352, by rfl⟩ : syracuseStep 9585803 = 14378705) B14378705
theorem B3787631 : Blo 1496068 3787631 := bstep (se 1 (by rfl) ⟨2840723, by rfl⟩ : syracuseStep 3787631 = 5681447) B5681447
theorem B38898863 : Blo 1496068 38898863 := bstep (se 1 (by rfl) ⟨29174147, by rfl⟩ : syracuseStep 38898863 = 58348295) B58348295
theorem B10939603 : Blo 1496068 10939603 := bstep (se 1 (by rfl) ⟨8204702, by rfl⟩ : syracuseStep 10939603 = 16409405) B16409405
theorem B5049593 : Blo 1496068 5049593 := bstep (se 2 (by rfl) ⟨1893597, by rfl⟩ : syracuseStep 5049593 = 3787195) B3787195
theorem B7581275 : Blo 1496068 7581275 := bstep (se 1 (by rfl) ⟨5685956, by rfl⟩ : syracuseStep 7581275 = 11371913) B11371913
theorem B10793513 : Blo 1496068 10793513 := bstep (se 2 (by rfl) ⟨4047567, by rfl⟩ : syracuseStep 10793513 = 8095135) B8095135
theorem B1496191 : Blo 1496068 1496191 := bstep (se 1 (by rfl) ⟨1122143, by rfl⟩ : syracuseStep 1496191 = 2244287) B2244287
theorem B1496935 : Blo 1496068 1496935 := bstep (se 1 (by rfl) ⟨1122701, by rfl⟩ : syracuseStep 1496935 = 2245403) B2245403
theorem B2398123 : Blo 1496068 2398123 := bstep (se 1 (by rfl) ⟨1798592, by rfl⟩ : syracuseStep 2398123 = 3597185) B3597185
theorem B5052671 : Blo 1496068 5052671 := bstep (se 1 (by rfl) ⟨3789503, by rfl⟩ : syracuseStep 5052671 = 7579007) B7579007
theorem B15784247 : Blo 1496068 15784247 := bstep (se 1 (by rfl) ⟨11838185, by rfl⟩ : syracuseStep 15784247 = 23676371) B23676371
theorem B1497599 : Blo 1496068 1497599 := bstep (se 1 (by rfl) ⟨1123199, by rfl⟩ : syracuseStep 1497599 = 2246399) B2246399
theorem B7683281 : Blo 1496068 7683281 := bstep (se 2 (by rfl) ⟨2881230, by rfl⟩ : syracuseStep 7683281 = 5762461) B5762461
theorem B2842303 : Blo 1496068 2842303 := bstep (se 1 (by rfl) ⟨2131727, by rfl⟩ : syracuseStep 2842303 = 4263455) B4263455
theorem B2244383 : Blo 1496068 2244383 := bstep (se 1 (by rfl) ⟨1683287, by rfl⟩ : syracuseStep 2244383 = 3366575) B3366575
theorem B174998171 : Blo 1496068 174998171 := bstep (se 1 (by rfl) ⟨131248628, by rfl⟩ : syracuseStep 174998171 = 262497257) B262497257
theorem B6390535 : Blo 1496068 6390535 := bstep (se 1 (by rfl) ⟨4792901, by rfl⟩ : syracuseStep 6390535 = 9585803) B9585803
theorem B3368447 : Blo 1496068 3368447 := bstep (se 1 (by rfl) ⟨2526335, by rfl⟩ : syracuseStep 3368447 = 5052671) B5052671
theorem B2525087 : Blo 1496068 2525087 := bstep (se 1 (by rfl) ⟨1893815, by rfl⟩ : syracuseStep 2525087 = 3787631) B3787631
theorem B5122187 : Blo 1496068 5122187 := bstep (se 1 (by rfl) ⟨3841640, by rfl⟩ : syracuseStep 5122187 = 7683281) B7683281
theorem B3197497 : Blo 1496068 3197497 := bstep (se 2 (by rfl) ⟨1199061, by rfl⟩ : syracuseStep 3197497 = 2398123) B2398123
theorem B7195675 : Blo 1496068 7195675 := bstep (se 1 (by rfl) ⟨5396756, by rfl⟩ : syracuseStep 7195675 = 10793513) B10793513
theorem B153759625 : Blo 1496068 153759625 := bstep (se 2 (by rfl) ⟨57659859, by rfl⟩ : syracuseStep 153759625 = 115319719) B115319719
theorem B10522831 : Blo 1496068 10522831 := bstep (se 1 (by rfl) ⟨7892123, by rfl⟩ : syracuseStep 10522831 = 15784247) B15784247
theorem B14586137 : Blo 1496068 14586137 := bstep (se 2 (by rfl) ⟨5469801, by rfl⟩ : syracuseStep 14586137 = 10939603) B10939603
theorem B25932575 : Blo 1496068 25932575 := bstep (se 1 (by rfl) ⟨19449431, by rfl⟩ : syracuseStep 25932575 = 38898863) B38898863
theorem B3789737 : Blo 1496068 3789737 := bstep (se 2 (by rfl) ⟨1421151, by rfl⟩ : syracuseStep 3789737 = 2842303) B2842303
theorem B1496255 : Blo 1496068 1496255 := bstep (se 1 (by rfl) ⟨1122191, by rfl⟩ : syracuseStep 1496255 = 2244383) B2244383
theorem B3366395 : Blo 1496068 3366395 := bstep (se 1 (by rfl) ⟨2524796, by rfl⟩ : syracuseStep 3366395 = 5049593) B5049593
theorem B5054183 : Blo 1496068 5054183 := bstep (se 1 (by rfl) ⟨3790637, by rfl⟩ : syracuseStep 5054183 = 7581275) B7581275
theorem B9724091 : Blo 1496068 9724091 := bstep (se 1 (by rfl) ⟨7293068, by rfl⟩ : syracuseStep 9724091 = 14586137) B14586137
theorem B2245631 : Blo 1496068 2245631 := bstep (se 1 (by rfl) ⟨1684223, by rfl⟩ : syracuseStep 2245631 = 3368447) B3368447
theorem B8520713 : Blo 1496068 8520713 := bstep (se 2 (by rfl) ⟨3195267, by rfl⟩ : syracuseStep 8520713 = 6390535) B6390535
theorem B9594233 : Blo 1496068 9594233 := bstep (se 2 (by rfl) ⟨3597837, by rfl⟩ : syracuseStep 9594233 = 7195675) B7195675
theorem B3369455 : Blo 1496068 3369455 := bstep (se 1 (by rfl) ⟨2527091, by rfl⟩ : syracuseStep 3369455 = 5054183) B5054183
theorem B116665447 : Blo 1496068 116665447 := bstep (se 1 (by rfl) ⟨87499085, by rfl⟩ : syracuseStep 116665447 = 174998171) B174998171
theorem B2526491 : Blo 1496068 2526491 := bstep (se 1 (by rfl) ⟨1894868, by rfl⟩ : syracuseStep 2526491 = 3789737) B3789737
theorem B4263329 : Blo 1496068 4263329 := bstep (se 2 (by rfl) ⟨1598748, by rfl⟩ : syracuseStep 4263329 = 3197497) B3197497
theorem B1683391 : Blo 1496068 1683391 := bstep (se 1 (by rfl) ⟨1262543, by rfl⟩ : syracuseStep 1683391 = 2525087) B2525087
theorem B69153533 : Blo 1496068 69153533 := bstep (se 3 (by rfl) ⟨12966287, by rfl⟩ : syracuseStep 69153533 = 25932575) B25932575
theorem B14030441 : Blo 1496068 14030441 := bstep (se 2 (by rfl) ⟨5261415, by rfl⟩ : syracuseStep 14030441 = 10522831) B10522831
theorem B3414791 : Blo 1496068 3414791 := bstep (se 1 (by rfl) ⟨2561093, by rfl⟩ : syracuseStep 3414791 = 5122187) B5122187
theorem B820051333 : Blo 1496068 820051333 := bstep (se 4 (by rfl) ⟨76879812, by rfl⟩ : syracuseStep 820051333 = 153759625) B153759625
theorem B2244263 : Blo 1496068 2244263 := bstep (se 1 (by rfl) ⟨1683197, by rfl⟩ : syracuseStep 2244263 = 3366395) B3366395
theorem B2246303 : Blo 1496068 2246303 := bstep (se 1 (by rfl) ⟨1684727, by rfl⟩ : syracuseStep 2246303 = 3369455) B3369455
theorem B17494428437 : Blo 1496068 17494428437 := bstep (se 6 (by rfl) ⟨410025666, by rfl⟩ : syracuseStep 17494428437 = 820051333) B820051333
theorem B25930909 : Blo 1496068 25930909 := bstep (se 3 (by rfl) ⟨4862045, by rfl⟩ : syracuseStep 25930909 = 9724091) B9724091
theorem B5680475 : Blo 1496068 5680475 := bstep (se 1 (by rfl) ⟨4260356, by rfl⟩ : syracuseStep 5680475 = 8520713) B8520713
theorem B155553929 : Blo 1496068 155553929 := bstep (se 2 (by rfl) ⟨58332723, by rfl⟩ : syracuseStep 155553929 = 116665447) B116665447
theorem B1684327 : Blo 1496068 1684327 := bstep (se 1 (by rfl) ⟨1263245, by rfl⟩ : syracuseStep 1684327 = 2526491) B2526491
theorem B1496175 : Blo 1496068 1496175 := bstep (se 1 (by rfl) ⟨1122131, by rfl⟩ : syracuseStep 1496175 = 2244263) B2244263
theorem B46102355 : Blo 1496068 46102355 := bstep (se 1 (by rfl) ⟨34576766, by rfl⟩ : syracuseStep 46102355 = 69153533) B69153533
theorem B1497087 : Blo 1496068 1497087 := bstep (se 1 (by rfl) ⟨1122815, by rfl⟩ : syracuseStep 1497087 = 2245631) B2245631
theorem B6396155 : Blo 1496068 6396155 := bstep (se 1 (by rfl) ⟨4797116, by rfl⟩ : syracuseStep 6396155 = 9594233) B9594233
theorem B9353627 : Blo 1496068 9353627 := bstep (se 1 (by rfl) ⟨7015220, by rfl⟩ : syracuseStep 9353627 = 14030441) B14030441
theorem B2276527 : Blo 1496068 2276527 := bstep (se 1 (by rfl) ⟨1707395, by rfl⟩ : syracuseStep 2276527 = 3414791) B3414791
theorem B2842219 : Blo 1496068 2842219 := bstep (se 1 (by rfl) ⟨2131664, by rfl⟩ : syracuseStep 2842219 = 4263329) B4263329
theorem B2244521 : Blo 1496068 2244521 := bstep (se 2 (by rfl) ⟨841695, by rfl⟩ : syracuseStep 2244521 = 1683391) B1683391
theorem B103702619 : Blo 1496068 103702619 := bstep (se 1 (by rfl) ⟨77776964, by rfl⟩ : syracuseStep 103702619 = 155553929) B155553929
theorem B2245769 : Blo 1496068 2245769 := bstep (se 2 (by rfl) ⟨842163, by rfl⟩ : syracuseStep 2245769 = 1684327) B1684327
theorem B6235751 : Blo 1496068 6235751 := bstep (se 1 (by rfl) ⟨4676813, by rfl⟩ : syracuseStep 6235751 = 9353627) B9353627
theorem B11662952291 : Blo 1496068 11662952291 := bstep (se 1 (by rfl) ⟨8747214218, by rfl⟩ : syracuseStep 11662952291 = 17494428437) B17494428437
theorem B3786983 : Blo 1496068 3786983 := bstep (se 1 (by rfl) ⟨2840237, by rfl⟩ : syracuseStep 3786983 = 5680475) B5680475
theorem B4264103 : Blo 1496068 4264103 := bstep (se 1 (by rfl) ⟨3198077, by rfl⟩ : syracuseStep 4264103 = 6396155) B6396155
theorem B34574545 : Blo 1496068 34574545 := bstep (se 2 (by rfl) ⟨12965454, by rfl⟩ : syracuseStep 34574545 = 25930909) B25930909
theorem B3035369 : Blo 1496068 3035369 := bstep (se 2 (by rfl) ⟨1138263, by rfl⟩ : syracuseStep 3035369 = 2276527) B2276527
theorem B3789625 : Blo 1496068 3789625 := bstep (se 2 (by rfl) ⟨1421109, by rfl⟩ : syracuseStep 3789625 = 2842219) B2842219
theorem B1496347 : Blo 1496068 1496347 := bstep (se 1 (by rfl) ⟨1122260, by rfl⟩ : syracuseStep 1496347 = 2244521) B2244521
theorem B1497535 : Blo 1496068 1497535 := bstep (se 1 (by rfl) ⟨1123151, by rfl⟩ : syracuseStep 1497535 = 2246303) B2246303
theorem B30734903 : Blo 1496068 30734903 := bstep (se 1 (by rfl) ⟨23051177, by rfl⟩ : syracuseStep 30734903 = 46102355) B46102355
theorem B2023579 : Blo 1496068 2023579 := bstep (se 1 (by rfl) ⟨1517684, by rfl⟩ : syracuseStep 2023579 = 3035369) B3035369
theorem B11370941 : Blo 1496068 11370941 := bstep (se 3 (by rfl) ⟨2132051, by rfl⟩ : syracuseStep 11370941 = 4264103) B4264103
theorem B2524655 : Blo 1496068 2524655 := bstep (se 1 (by rfl) ⟨1893491, by rfl⟩ : syracuseStep 2524655 = 3786983) B3786983
theorem B20489935 : Blo 1496068 20489935 := bstep (se 1 (by rfl) ⟨15367451, by rfl⟩ : syracuseStep 20489935 = 30734903) B30734903
theorem B69135079 : Blo 1496068 69135079 := bstep (se 1 (by rfl) ⟨51851309, by rfl⟩ : syracuseStep 69135079 = 103702619) B103702619
theorem B4157167 : Blo 1496068 4157167 := bstep (se 1 (by rfl) ⟨3117875, by rfl⟩ : syracuseStep 4157167 = 6235751) B6235751
theorem B184397573 : Blo 1496068 184397573 := bstep (se 4 (by rfl) ⟨17287272, by rfl⟩ : syracuseStep 184397573 = 34574545) B34574545
theorem B7775301527 : Blo 1496068 7775301527 := bstep (se 1 (by rfl) ⟨5831476145, by rfl⟩ : syracuseStep 7775301527 = 11662952291) B11662952291
theorem B1497179 : Blo 1496068 1497179 := bstep (se 1 (by rfl) ⟨1122884, by rfl⟩ : syracuseStep 1497179 = 2245769) B2245769
theorem B5052833 : Blo 1496068 5052833 := bstep (se 2 (by rfl) ⟨1894812, by rfl⟩ : syracuseStep 5052833 = 3789625) B3789625
theorem B3368555 : Blo 1496068 3368555 := bstep (se 1 (by rfl) ⟨2526416, by rfl⟩ : syracuseStep 3368555 = 5052833) B5052833
theorem B122931715 : Blo 1496068 122931715 := bstep (se 1 (by rfl) ⟨92198786, by rfl⟩ : syracuseStep 122931715 = 184397573) B184397573
theorem B2698105 : Blo 1496068 2698105 := bstep (se 2 (by rfl) ⟨1011789, by rfl⟩ : syracuseStep 2698105 = 2023579) B2023579
theorem B7580627 : Blo 1496068 7580627 := bstep (se 1 (by rfl) ⟨5685470, by rfl⟩ : syracuseStep 7580627 = 11370941) B11370941
theorem B92180105 : Blo 1496068 92180105 := bstep (se 2 (by rfl) ⟨34567539, by rfl⟩ : syracuseStep 92180105 = 69135079) B69135079
theorem B1683103 : Blo 1496068 1683103 := bstep (se 1 (by rfl) ⟨1262327, by rfl⟩ : syracuseStep 1683103 = 2524655) B2524655
theorem B5542889 : Blo 1496068 5542889 := bstep (se 2 (by rfl) ⟨2078583, by rfl⟩ : syracuseStep 5542889 = 4157167) B4157167
theorem B5183534351 : Blo 1496068 5183534351 := bstep (se 1 (by rfl) ⟨3887650763, by rfl⟩ : syracuseStep 5183534351 = 7775301527) B7775301527
theorem B27319913 : Blo 1496068 27319913 := bstep (se 2 (by rfl) ⟨10244967, by rfl⟩ : syracuseStep 27319913 = 20489935) B20489935
theorem B3455689567 : Blo 1496068 3455689567 := bstep (se 1 (by rfl) ⟨2591767175, by rfl⟩ : syracuseStep 3455689567 = 5183534351) B5183534351
theorem B2245703 : Blo 1496068 2245703 := bstep (se 1 (by rfl) ⟨1684277, by rfl⟩ : syracuseStep 2245703 = 3368555) B3368555
theorem B3597473 : Blo 1496068 3597473 := bstep (se 2 (by rfl) ⟨1349052, by rfl⟩ : syracuseStep 3597473 = 2698105) B2698105
theorem B18213275 : Blo 1496068 18213275 := bstep (se 1 (by rfl) ⟨13659956, by rfl⟩ : syracuseStep 18213275 = 27319913) B27319913
theorem B14781037 : Blo 1496068 14781037 := bstep (se 3 (by rfl) ⟨2771444, by rfl⟩ : syracuseStep 14781037 = 5542889) B5542889
theorem B163908953 : Blo 1496068 163908953 := bstep (se 2 (by rfl) ⟨61465857, by rfl⟩ : syracuseStep 163908953 = 122931715) B122931715
theorem B61453403 : Blo 1496068 61453403 := bstep (se 1 (by rfl) ⟨46090052, by rfl⟩ : syracuseStep 61453403 = 92180105) B92180105
theorem B5053751 : Blo 1496068 5053751 := bstep (se 1 (by rfl) ⟨3790313, by rfl⟩ : syracuseStep 5053751 = 7580627) B7580627
theorem B2244137 : Blo 1496068 2244137 := bstep (se 2 (by rfl) ⟨841551, by rfl⟩ : syracuseStep 2244137 = 1683103) B1683103
theorem B9593261 : Blo 1496068 9593261 := bstep (se 3 (by rfl) ⟨1798736, by rfl⟩ : syracuseStep 9593261 = 3597473) B3597473
theorem B40968935 : Blo 1496068 40968935 := bstep (se 1 (by rfl) ⟨30726701, by rfl⟩ : syracuseStep 40968935 = 61453403) B61453403
theorem B12142183 : Blo 1496068 12142183 := bstep (se 1 (by rfl) ⟨9106637, by rfl⟩ : syracuseStep 12142183 = 18213275) B18213275
theorem B3369167 : Blo 1496068 3369167 := bstep (se 1 (by rfl) ⟨2526875, by rfl⟩ : syracuseStep 3369167 = 5053751) B5053751
theorem B4607586089 : Blo 1496068 4607586089 := bstep (se 2 (by rfl) ⟨1727844783, by rfl⟩ : syracuseStep 4607586089 = 3455689567) B3455689567
theorem B1496091 : Blo 1496068 1496091 := bstep (se 1 (by rfl) ⟨1122068, by rfl⟩ : syracuseStep 1496091 = 2244137) B2244137
theorem B1497135 : Blo 1496068 1497135 := bstep (se 1 (by rfl) ⟨1122851, by rfl⟩ : syracuseStep 1497135 = 2245703) B2245703
theorem B19708049 : Blo 1496068 19708049 := bstep (se 2 (by rfl) ⟨7390518, by rfl⟩ : syracuseStep 19708049 = 14781037) B14781037
theorem B109272635 : Blo 1496068 109272635 := bstep (se 1 (by rfl) ⟨81954476, by rfl⟩ : syracuseStep 109272635 = 163908953) B163908953
theorem B27312623 : Blo 1496068 27312623 := bstep (se 1 (by rfl) ⟨20484467, by rfl⟩ : syracuseStep 27312623 = 40968935) B40968935
theorem B2246111 : Blo 1496068 2246111 := bstep (se 1 (by rfl) ⟨1684583, by rfl⟩ : syracuseStep 2246111 = 3369167) B3369167
theorem B16189577 : Blo 1496068 16189577 := bstep (se 2 (by rfl) ⟨6071091, by rfl⟩ : syracuseStep 16189577 = 12142183) B12142183
theorem B3071724059 : Blo 1496068 3071724059 := bstep (se 1 (by rfl) ⟨2303793044, by rfl⟩ : syracuseStep 3071724059 = 4607586089) B4607586089
theorem B72848423 : Blo 1496068 72848423 := bstep (se 1 (by rfl) ⟨54636317, by rfl⟩ : syracuseStep 72848423 = 109272635) B109272635
theorem B6395507 : Blo 1496068 6395507 := bstep (se 1 (by rfl) ⟨4796630, by rfl⟩ : syracuseStep 6395507 = 9593261) B9593261
theorem B13138699 : Blo 1496068 13138699 := bstep (se 1 (by rfl) ⟨9854024, by rfl⟩ : syracuseStep 13138699 = 19708049) B19708049
theorem B48565615 : Blo 1496068 48565615 := bstep (se 1 (by rfl) ⟨36424211, by rfl⟩ : syracuseStep 48565615 = 72848423) B72848423
theorem B17518265 : Blo 1496068 17518265 := bstep (se 2 (by rfl) ⟨6569349, by rfl⟩ : syracuseStep 17518265 = 13138699) B13138699
theorem B4263671 : Blo 1496068 4263671 := bstep (se 1 (by rfl) ⟨3197753, by rfl⟩ : syracuseStep 4263671 = 6395507) B6395507
theorem B10793051 : Blo 1496068 10793051 := bstep (se 1 (by rfl) ⟨8094788, by rfl⟩ : syracuseStep 10793051 = 16189577) B16189577
theorem B2047816039 : Blo 1496068 2047816039 := bstep (se 1 (by rfl) ⟨1535862029, by rfl⟩ : syracuseStep 2047816039 = 3071724059) B3071724059
theorem B18208415 : Blo 1496068 18208415 := bstep (se 1 (by rfl) ⟨13656311, by rfl⟩ : syracuseStep 18208415 = 27312623) B27312623
theorem B1497407 : Blo 1496068 1497407 := bstep (se 1 (by rfl) ⟨1123055, by rfl⟩ : syracuseStep 1497407 = 2246111) B2246111
theorem B7195367 : Blo 1496068 7195367 := bstep (se 1 (by rfl) ⟨5396525, by rfl⟩ : syracuseStep 7195367 = 10793051) B10793051
theorem B2730421385 : Blo 1496068 2730421385 := bstep (se 2 (by rfl) ⟨1023908019, by rfl⟩ : syracuseStep 2730421385 = 2047816039) B2047816039
theorem B64754153 : Blo 1496068 64754153 := bstep (se 2 (by rfl) ⟨24282807, by rfl⟩ : syracuseStep 64754153 = 48565615) B48565615
theorem B11678843 : Blo 1496068 11678843 := bstep (se 1 (by rfl) ⟨8759132, by rfl⟩ : syracuseStep 11678843 = 17518265) B17518265
theorem B12138943 : Blo 1496068 12138943 := bstep (se 1 (by rfl) ⟨9104207, by rfl⟩ : syracuseStep 12138943 = 18208415) B18208415
theorem B2842447 : Blo 1496068 2842447 := bstep (se 1 (by rfl) ⟨2131835, by rfl⟩ : syracuseStep 2842447 = 4263671) B4263671
theorem B1820280923 : Blo 1496068 1820280923 := bstep (se 1 (by rfl) ⟨1365210692, by rfl⟩ : syracuseStep 1820280923 = 2730421385) B2730421385
theorem B7785895 : Blo 1496068 7785895 := bstep (se 1 (by rfl) ⟨5839421, by rfl⟩ : syracuseStep 7785895 = 11678843) B11678843
theorem B4796911 : Blo 1496068 4796911 := bstep (se 1 (by rfl) ⟨3597683, by rfl⟩ : syracuseStep 4796911 = 7195367) B7195367
theorem B3789929 : Blo 1496068 3789929 := bstep (se 2 (by rfl) ⟨1421223, by rfl⟩ : syracuseStep 3789929 = 2842447) B2842447
theorem B43169435 : Blo 1496068 43169435 := bstep (se 1 (by rfl) ⟨32377076, by rfl⟩ : syracuseStep 43169435 = 64754153) B64754153
theorem B16185257 : Blo 1496068 16185257 := bstep (se 2 (by rfl) ⟨6069471, by rfl⟩ : syracuseStep 16185257 = 12138943) B12138943
theorem B28779623 : Blo 1496068 28779623 := bstep (se 1 (by rfl) ⟨21584717, by rfl⟩ : syracuseStep 28779623 = 43169435) B43169435
theorem B10790171 : Blo 1496068 10790171 := bstep (se 1 (by rfl) ⟨8092628, by rfl⟩ : syracuseStep 10790171 = 16185257) B16185257
theorem B10381193 : Blo 1496068 10381193 := bstep (se 2 (by rfl) ⟨3892947, by rfl⟩ : syracuseStep 10381193 = 7785895) B7785895
theorem B2526619 : Blo 1496068 2526619 := bstep (se 1 (by rfl) ⟨1894964, by rfl⟩ : syracuseStep 2526619 = 3789929) B3789929
theorem B1213520615 : Blo 1496068 1213520615 := bstep (se 1 (by rfl) ⟨910140461, by rfl⟩ : syracuseStep 1213520615 = 1820280923) B1820280923
theorem B25583525 : Blo 1496068 25583525 := bstep (se 4 (by rfl) ⟨2398455, by rfl⟩ : syracuseStep 25583525 = 4796911) B4796911
theorem B19186415 : Blo 1496068 19186415 := bstep (se 1 (by rfl) ⟨14389811, by rfl⟩ : syracuseStep 19186415 = 28779623) B28779623
theorem B7193447 : Blo 1496068 7193447 := bstep (se 1 (by rfl) ⟨5395085, by rfl⟩ : syracuseStep 7193447 = 10790171) B10790171
theorem B3368825 : Blo 1496068 3368825 := bstep (se 2 (by rfl) ⟨1263309, by rfl⟩ : syracuseStep 3368825 = 2526619) B2526619
theorem B809013743 : Blo 1496068 809013743 := bstep (se 1 (by rfl) ⟨606760307, by rfl⟩ : syracuseStep 809013743 = 1213520615) B1213520615
theorem B6920795 : Blo 1496068 6920795 := bstep (se 1 (by rfl) ⟨5190596, by rfl⟩ : syracuseStep 6920795 = 10381193) B10381193
theorem B17055683 : Blo 1496068 17055683 := bstep (se 1 (by rfl) ⟨12791762, by rfl⟩ : syracuseStep 17055683 = 25583525) B25583525
theorem B2245883 : Blo 1496068 2245883 := bstep (se 1 (by rfl) ⟨1684412, by rfl⟩ : syracuseStep 2245883 = 3368825) B3368825
theorem B4613863 : Blo 1496068 4613863 := bstep (se 1 (by rfl) ⟨3460397, by rfl⟩ : syracuseStep 4613863 = 6920795) B6920795
theorem B12790943 : Blo 1496068 12790943 := bstep (se 1 (by rfl) ⟨9593207, by rfl⟩ : syracuseStep 12790943 = 19186415) B19186415
theorem B4795631 : Blo 1496068 4795631 := bstep (se 1 (by rfl) ⟨3596723, by rfl⟩ : syracuseStep 4795631 = 7193447) B7193447
theorem B539342495 : Blo 1496068 539342495 := bstep (se 1 (by rfl) ⟨404506871, by rfl⟩ : syracuseStep 539342495 = 809013743) B809013743
theorem B11370455 : Blo 1496068 11370455 := bstep (se 1 (by rfl) ⟨8527841, by rfl⟩ : syracuseStep 11370455 = 17055683) B17055683
theorem B3197087 : Blo 1496068 3197087 := bstep (se 1 (by rfl) ⟨2397815, by rfl⟩ : syracuseStep 3197087 = 4795631) B4795631
theorem B7580303 : Blo 1496068 7580303 := bstep (se 1 (by rfl) ⟨5685227, by rfl⟩ : syracuseStep 7580303 = 11370455) B11370455
theorem B1497255 : Blo 1496068 1497255 := bstep (se 1 (by rfl) ⟨1122941, by rfl⟩ : syracuseStep 1497255 = 2245883) B2245883
theorem B359561663 : Blo 1496068 359561663 := bstep (se 1 (by rfl) ⟨269671247, by rfl⟩ : syracuseStep 359561663 = 539342495) B539342495
theorem B8527295 : Blo 1496068 8527295 := bstep (se 1 (by rfl) ⟨6395471, by rfl⟩ : syracuseStep 8527295 = 12790943) B12790943
theorem B6151817 : Blo 1496068 6151817 := bstep (se 2 (by rfl) ⟨2306931, by rfl⟩ : syracuseStep 6151817 = 4613863) B4613863
theorem B2131391 : Blo 1496068 2131391 := bstep (se 1 (by rfl) ⟨1598543, by rfl⟩ : syracuseStep 2131391 = 3197087) B3197087
theorem B239707775 : Blo 1496068 239707775 := bstep (se 1 (by rfl) ⟨179780831, by rfl⟩ : syracuseStep 239707775 = 359561663) B359561663
theorem B4101211 : Blo 1496068 4101211 := bstep (se 1 (by rfl) ⟨3075908, by rfl⟩ : syracuseStep 4101211 = 6151817) B6151817
theorem B5053535 : Blo 1496068 5053535 := bstep (se 1 (by rfl) ⟨3790151, by rfl⟩ : syracuseStep 5053535 = 7580303) B7580303
theorem B5684863 : Blo 1496068 5684863 := bstep (se 1 (by rfl) ⟨4263647, by rfl⟩ : syracuseStep 5684863 = 8527295) B8527295
theorem B21873125 : Blo 1496068 21873125 := bstep (se 4 (by rfl) ⟨2050605, by rfl⟩ : syracuseStep 21873125 = 4101211) B4101211
theorem B3369023 : Blo 1496068 3369023 := bstep (se 1 (by rfl) ⟨2526767, by rfl⟩ : syracuseStep 3369023 = 5053535) B5053535
theorem B7579817 : Blo 1496068 7579817 := bstep (se 2 (by rfl) ⟨2842431, by rfl⟩ : syracuseStep 7579817 = 5684863) B5684863
theorem B5683709 : Blo 1496068 5683709 := bstep (se 3 (by rfl) ⟨1065695, by rfl⟩ : syracuseStep 5683709 = 2131391) B2131391
theorem B639220733 : Blo 1496068 639220733 := bstep (se 3 (by rfl) ⟨119853887, by rfl⟩ : syracuseStep 639220733 = 239707775) B239707775
theorem B58328333 : Blo 1496068 58328333 := bstep (se 3 (by rfl) ⟨10936562, by rfl⟩ : syracuseStep 58328333 = 21873125) B21873125
theorem B2246015 : Blo 1496068 2246015 := bstep (se 1 (by rfl) ⟨1684511, by rfl⟩ : syracuseStep 2246015 = 3369023) B3369023
theorem B3789139 : Blo 1496068 3789139 := bstep (se 1 (by rfl) ⟨2841854, by rfl⟩ : syracuseStep 3789139 = 5683709) B5683709
theorem B5053211 : Blo 1496068 5053211 := bstep (se 1 (by rfl) ⟨3789908, by rfl⟩ : syracuseStep 5053211 = 7579817) B7579817
theorem B426147155 : Blo 1496068 426147155 := bstep (se 1 (by rfl) ⟨319610366, by rfl⟩ : syracuseStep 426147155 = 639220733) B639220733
theorem B3368807 : Blo 1496068 3368807 := bstep (se 1 (by rfl) ⟨2526605, by rfl⟩ : syracuseStep 3368807 = 5053211) B5053211
theorem B5052185 : Blo 1496068 5052185 := bstep (se 2 (by rfl) ⟨1894569, by rfl⟩ : syracuseStep 5052185 = 3789139) B3789139
theorem B38885555 : Blo 1496068 38885555 := bstep (se 1 (by rfl) ⟨29164166, by rfl⟩ : syracuseStep 38885555 = 58328333) B58328333
theorem B1497343 : Blo 1496068 1497343 := bstep (se 1 (by rfl) ⟨1123007, by rfl⟩ : syracuseStep 1497343 = 2246015) B2246015
theorem B284098103 : Blo 1496068 284098103 := bstep (se 1 (by rfl) ⟨213073577, by rfl⟩ : syracuseStep 284098103 = 426147155) B426147155
theorem B103694813 : Blo 1496068 103694813 := bstep (se 3 (by rfl) ⟨19442777, by rfl⟩ : syracuseStep 103694813 = 38885555) B38885555
theorem B3368123 : Blo 1496068 3368123 := bstep (se 1 (by rfl) ⟨2526092, by rfl⟩ : syracuseStep 3368123 = 5052185) B5052185
theorem B2245871 : Blo 1496068 2245871 := bstep (se 1 (by rfl) ⟨1684403, by rfl⟩ : syracuseStep 2245871 = 3368807) B3368807
theorem B189398735 : Blo 1496068 189398735 := bstep (se 1 (by rfl) ⟨142049051, by rfl⟩ : syracuseStep 189398735 = 284098103) B284098103
theorem B2245415 : Blo 1496068 2245415 := bstep (se 1 (by rfl) ⟨1684061, by rfl⟩ : syracuseStep 2245415 = 3368123) B3368123
theorem B126265823 : Blo 1496068 126265823 := bstep (se 1 (by rfl) ⟨94699367, by rfl⟩ : syracuseStep 126265823 = 189398735) B189398735
theorem B69129875 : Blo 1496068 69129875 := bstep (se 1 (by rfl) ⟨51847406, by rfl⟩ : syracuseStep 69129875 = 103694813) B103694813
theorem B1497247 : Blo 1496068 1497247 := bstep (se 1 (by rfl) ⟨1122935, by rfl⟩ : syracuseStep 1497247 = 2245871) B2245871
theorem B84177215 : Blo 1496068 84177215 := bstep (se 1 (by rfl) ⟨63132911, by rfl⟩ : syracuseStep 84177215 = 126265823) B126265823
theorem B1496943 : Blo 1496068 1496943 := bstep (se 1 (by rfl) ⟨1122707, by rfl⟩ : syracuseStep 1496943 = 2245415) B2245415
theorem B46086583 : Blo 1496068 46086583 := bstep (se 1 (by rfl) ⟨34564937, by rfl⟩ : syracuseStep 46086583 = 69129875) B69129875
theorem B61448777 : Blo 1496068 61448777 := bstep (se 2 (by rfl) ⟨23043291, by rfl⟩ : syracuseStep 61448777 = 46086583) B46086583
theorem B56118143 : Blo 1496068 56118143 := bstep (se 1 (by rfl) ⟨42088607, by rfl⟩ : syracuseStep 56118143 = 84177215) B84177215
theorem B149648381 : Blo 1496068 149648381 := bstep (se 3 (by rfl) ⟨28059071, by rfl⟩ : syracuseStep 149648381 = 56118143) B56118143
theorem B40965851 : Blo 1496068 40965851 := bstep (se 1 (by rfl) ⟨30724388, by rfl⟩ : syracuseStep 40965851 = 61448777) B61448777
theorem B109242269 : Blo 1496068 109242269 := bstep (se 3 (by rfl) ⟨20482925, by rfl⟩ : syracuseStep 109242269 = 40965851) B40965851
theorem B99765587 : Blo 1496068 99765587 := bstep (se 1 (by rfl) ⟨74824190, by rfl⟩ : syracuseStep 99765587 = 149648381) B149648381
theorem B72828179 : Blo 1496068 72828179 := bstep (se 1 (by rfl) ⟨54621134, by rfl⟩ : syracuseStep 72828179 = 109242269) B109242269
theorem B66510391 : Blo 1496068 66510391 := bstep (se 1 (by rfl) ⟨49882793, by rfl⟩ : syracuseStep 66510391 = 99765587) B99765587
theorem B88680521 : Blo 1496068 88680521 := bstep (se 2 (by rfl) ⟨33255195, by rfl⟩ : syracuseStep 88680521 = 66510391) B66510391
theorem B48552119 : Blo 1496068 48552119 := bstep (se 1 (by rfl) ⟨36414089, by rfl⟩ : syracuseStep 48552119 = 72828179) B72828179
theorem B32368079 : Blo 1496068 32368079 := bstep (se 1 (by rfl) ⟨24276059, by rfl⟩ : syracuseStep 32368079 = 48552119) B48552119
theorem B236481389 : Blo 1496068 236481389 := bstep (se 3 (by rfl) ⟨44340260, by rfl⟩ : syracuseStep 236481389 = 88680521) B88680521
theorem B21578719 : Blo 1496068 21578719 := bstep (se 1 (by rfl) ⟨16184039, by rfl⟩ : syracuseStep 21578719 = 32368079) B32368079
theorem B157654259 : Blo 1496068 157654259 := bstep (se 1 (by rfl) ⟨118240694, by rfl⟩ : syracuseStep 157654259 = 236481389) B236481389
theorem B28771625 : Blo 1496068 28771625 := bstep (se 2 (by rfl) ⟨10789359, by rfl⟩ : syracuseStep 28771625 = 21578719) B21578719
theorem B105102839 : Blo 1496068 105102839 := bstep (se 1 (by rfl) ⟨78827129, by rfl⟩ : syracuseStep 105102839 = 157654259) B157654259
theorem B70068559 : Blo 1496068 70068559 := bstep (se 1 (by rfl) ⟨52551419, by rfl⟩ : syracuseStep 70068559 = 105102839) B105102839
theorem B19181083 : Blo 1496068 19181083 := bstep (se 1 (by rfl) ⟨14385812, by rfl⟩ : syracuseStep 19181083 = 28771625) B28771625
theorem B93424745 : Blo 1496068 93424745 := bstep (se 2 (by rfl) ⟨35034279, by rfl⟩ : syracuseStep 93424745 = 70068559) B70068559
theorem B25574777 : Blo 1496068 25574777 := bstep (se 2 (by rfl) ⟨9590541, by rfl⟩ : syracuseStep 25574777 = 19181083) B19181083
theorem B17049851 : Blo 1496068 17049851 := bstep (se 1 (by rfl) ⟨12787388, by rfl⟩ : syracuseStep 17049851 = 25574777) B25574777
theorem B62283163 : Blo 1496068 62283163 := bstep (se 1 (by rfl) ⟨46712372, by rfl⟩ : syracuseStep 62283163 = 93424745) B93424745
theorem B83044217 : Blo 1496068 83044217 := bstep (se 2 (by rfl) ⟨31141581, by rfl⟩ : syracuseStep 83044217 = 62283163) B62283163
theorem B11366567 : Blo 1496068 11366567 := bstep (se 1 (by rfl) ⟨8524925, by rfl⟩ : syracuseStep 11366567 = 17049851) B17049851
theorem B7577711 : Blo 1496068 7577711 := bstep (se 1 (by rfl) ⟨5683283, by rfl⟩ : syracuseStep 7577711 = 11366567) B11366567
theorem B55362811 : Blo 1496068 55362811 := bstep (se 1 (by rfl) ⟨41522108, by rfl⟩ : syracuseStep 55362811 = 83044217) B83044217
theorem B5051807 : Blo 1496068 5051807 := bstep (se 1 (by rfl) ⟨3788855, by rfl⟩ : syracuseStep 5051807 = 7577711) B7577711
theorem B73817081 : Blo 1496068 73817081 := bstep (se 2 (by rfl) ⟨27681405, by rfl⟩ : syracuseStep 73817081 = 55362811) B55362811
theorem B3367871 : Blo 1496068 3367871 := bstep (se 1 (by rfl) ⟨2525903, by rfl⟩ : syracuseStep 3367871 = 5051807) B5051807
theorem B49211387 : Blo 1496068 49211387 := bstep (se 1 (by rfl) ⟨36908540, by rfl⟩ : syracuseStep 49211387 = 73817081) B73817081
theorem B2245247 : Blo 1496068 2245247 := bstep (se 1 (by rfl) ⟨1683935, by rfl⟩ : syracuseStep 2245247 = 3367871) B3367871
theorem B32807591 : Blo 1496068 32807591 := bstep (se 1 (by rfl) ⟨24605693, by rfl⟩ : syracuseStep 32807591 = 49211387) B49211387
theorem B1496831 : Blo 1496068 1496831 := bstep (se 1 (by rfl) ⟨1122623, by rfl⟩ : syracuseStep 1496831 = 2245247) B2245247
theorem B21871727 : Blo 1496068 21871727 := bstep (se 1 (by rfl) ⟨16403795, by rfl⟩ : syracuseStep 21871727 = 32807591) B32807591
theorem B14581151 : Blo 1496068 14581151 := bstep (se 1 (by rfl) ⟨10935863, by rfl⟩ : syracuseStep 14581151 = 21871727) B21871727
theorem B9720767 : Blo 1496068 9720767 := bstep (se 1 (by rfl) ⟨7290575, by rfl⟩ : syracuseStep 9720767 = 14581151) B14581151
theorem B25922045 : Blo 1496068 25922045 := bstep (se 3 (by rfl) ⟨4860383, by rfl⟩ : syracuseStep 25922045 = 9720767) B9720767
theorem B17281363 : Blo 1496068 17281363 := bstep (se 1 (by rfl) ⟨12961022, by rfl⟩ : syracuseStep 17281363 = 25922045) B25922045
theorem B23041817 : Blo 1496068 23041817 := bstep (se 2 (by rfl) ⟨8640681, by rfl⟩ : syracuseStep 23041817 = 17281363) B17281363
theorem B15361211 : Blo 1496068 15361211 := bstep (se 1 (by rfl) ⟨11520908, by rfl⟩ : syracuseStep 15361211 = 23041817) B23041817
theorem B40963229 : Blo 1496068 40963229 := bstep (se 3 (by rfl) ⟨7680605, by rfl⟩ : syracuseStep 40963229 = 15361211) B15361211
theorem B27308819 : Blo 1496068 27308819 := bstep (se 1 (by rfl) ⟨20481614, by rfl⟩ : syracuseStep 27308819 = 40963229) B40963229
theorem B18205879 : Blo 1496068 18205879 := bstep (se 1 (by rfl) ⟨13654409, by rfl⟩ : syracuseStep 18205879 = 27308819) B27308819
theorem B24274505 : Blo 1496068 24274505 := bstep (se 2 (by rfl) ⟨9102939, by rfl⟩ : syracuseStep 24274505 = 18205879) B18205879
theorem B16183003 : Blo 1496068 16183003 := bstep (se 1 (by rfl) ⟨12137252, by rfl⟩ : syracuseStep 16183003 = 24274505) B24274505
theorem B21577337 : Blo 1496068 21577337 := bstep (se 2 (by rfl) ⟨8091501, by rfl⟩ : syracuseStep 21577337 = 16183003) B16183003
theorem B14384891 : Blo 1496068 14384891 := bstep (se 1 (by rfl) ⟨10788668, by rfl⟩ : syracuseStep 14384891 = 21577337) B21577337
theorem B9589927 : Blo 1496068 9589927 := bstep (se 1 (by rfl) ⟨7192445, by rfl⟩ : syracuseStep 9589927 = 14384891) B14384891
theorem B12786569 : Blo 1496068 12786569 := bstep (se 2 (by rfl) ⟨4794963, by rfl⟩ : syracuseStep 12786569 = 9589927) B9589927
theorem B8524379 : Blo 1496068 8524379 := bstep (se 1 (by rfl) ⟨6393284, by rfl⟩ : syracuseStep 8524379 = 12786569) B12786569
theorem B5682919 : Blo 1496068 5682919 := bstep (se 1 (by rfl) ⟨4262189, by rfl⟩ : syracuseStep 5682919 = 8524379) B8524379
theorem B7577225 : Blo 1496068 7577225 := bstep (se 2 (by rfl) ⟨2841459, by rfl⟩ : syracuseStep 7577225 = 5682919) B5682919
theorem B5051483 : Blo 1496068 5051483 := bstep (se 1 (by rfl) ⟨3788612, by rfl⟩ : syracuseStep 5051483 = 7577225) B7577225
theorem B3367655 : Blo 1496068 3367655 := bstep (se 1 (by rfl) ⟨2525741, by rfl⟩ : syracuseStep 3367655 = 5051483) B5051483
theorem B2245103 : Blo 1496068 2245103 := bstep (se 1 (by rfl) ⟨1683827, by rfl⟩ : syracuseStep 2245103 = 3367655) B3367655
theorem B1496735 : Blo 1496068 1496735 := bstep (se 1 (by rfl) ⟨1122551, by rfl⟩ : syracuseStep 1496735 = 2245103) B2245103

theorem C0 (j : ℕ) (h1 : 374017 ≤ j) (h2 : j ≤ 374516) : Blo 1496068 (4 * j + 3) := by
  interval_cases j
  · exact B1496071
  · exact B1496075
  · exact B1496079
  · exact B1496083
  · exact B1496087
  · exact B1496091
  · exact B1496095
  · exact B1496099
  · exact B1496103
  · exact B1496107
  · exact B1496111
  · exact B1496115
  · exact B1496119
  · exact B1496123
  · exact B1496127
  · exact B1496131
  · exact B1496135
  · exact B1496139
  · exact B1496143
  · exact B1496147
  · exact B1496151
  · exact B1496155
  · exact B1496159
  · exact B1496163
  · exact B1496167
  · exact B1496171
  · exact B1496175
  · exact B1496179
  · exact B1496183
  · exact B1496187
  · exact B1496191
  · exact B1496195
  · exact B1496199
  · exact B1496203
  · exact B1496207
  · exact B1496211
  · exact B1496215
  · exact B1496219
  · exact B1496223
  · exact B1496227
  · exact B1496231
  · exact B1496235
  · exact B1496239
  · exact B1496243
  · exact B1496247
  · exact B1496251
  · exact B1496255
  · exact B1496259
  · exact B1496263
  · exact B1496267
  · exact B1496271
  · exact B1496275
  · exact B1496279
  · exact B1496283
  · exact B1496287
  · exact B1496291
  · exact B1496295
  · exact B1496299
  · exact B1496303
  · exact B1496307
  · exact B1496311
  · exact B1496315
  · exact B1496319
  · exact B1496323
  · exact B1496327
  · exact B1496331
  · exact B1496335
  · exact B1496339
  · exact B1496343
  · exact B1496347
  · exact B1496351
  · exact B1496355
  · exact B1496359
  · exact B1496363
  · exact B1496367
  · exact B1496371
  · exact B1496375
  · exact B1496379
  · exact B1496383
  · exact B1496387
  · exact B1496391
  · exact B1496395
  · exact B1496399
  · exact B1496403
  · exact B1496407
  · exact B1496411
  · exact B1496415
  · exact B1496419
  · exact B1496423
  · exact B1496427
  · exact B1496431
  · exact B1496435
  · exact B1496439
  · exact B1496443
  · exact B1496447
  · exact B1496451
  · exact B1496455
  · exact B1496459
  · exact B1496463
  · exact B1496467
  · exact B1496471
  · exact B1496475
  · exact B1496479
  · exact B1496483
  · exact B1496487
  · exact B1496491
  · exact B1496495
  · exact B1496499
  · exact B1496503
  · exact B1496507
  · exact B1496511
  · exact B1496515
  · exact B1496519
  · exact B1496523
  · exact B1496527
  · exact B1496531
  · exact B1496535
  · exact B1496539
  · exact B1496543
  · exact B1496547
  · exact B1496551
  · exact B1496555
  · exact B1496559
  · exact B1496563
  · exact B1496567
  · exact B1496571
  · exact B1496575
  · exact B1496579
  · exact B1496583
  · exact B1496587
  · exact B1496591
  · exact B1496595
  · exact B1496599
  · exact B1496603
  · exact B1496607
  · exact B1496611
  · exact B1496615
  · exact B1496619
  · exact B1496623
  · exact B1496627
  · exact B1496631
  · exact B1496635
  · exact B1496639
  · exact B1496643
  · exact B1496647
  · exact B1496651
  · exact B1496655
  · exact B1496659
  · exact B1496663
  · exact B1496667
  · exact B1496671
  · exact B1496675
  · exact B1496679
  · exact B1496683
  · exact B1496687
  · exact B1496691
  · exact B1496695
  · exact B1496699
  · exact B1496703
  · exact B1496707
  · exact B1496711
  · exact B1496715
  · exact B1496719
  · exact B1496723
  · exact B1496727
  · exact B1496731
  · exact B1496735
  · exact B1496739
  · exact B1496743
  · exact B1496747
  · exact B1496751
  · exact B1496755
  · exact B1496759
  · exact B1496763
  · exact B1496767
  · exact B1496771
  · exact B1496775
  · exact B1496779
  · exact B1496783
  · exact B1496787
  · exact B1496791
  · exact B1496795
  · exact B1496799
  · exact B1496803
  · exact B1496807
  · exact B1496811
  · exact B1496815
  · exact B1496819
  · exact B1496823
  · exact B1496827
  · exact B1496831
  · exact B1496835
  · exact B1496839
  · exact B1496843
  · exact B1496847
  · exact B1496851
  · exact B1496855
  · exact B1496859
  · exact B1496863
  · exact B1496867
  · exact B1496871
  · exact B1496875
  · exact B1496879
  · exact B1496883
  · exact B1496887
  · exact B1496891
  · exact B1496895
  · exact B1496899
  · exact B1496903
  · exact B1496907
  · exact B1496911
  · exact B1496915
  · exact B1496919
  · exact B1496923
  · exact B1496927
  · exact B1496931
  · exact B1496935
  · exact B1496939
  · exact B1496943
  · exact B1496947
  · exact B1496951
  · exact B1496955
  · exact B1496959
  · exact B1496963
  · exact B1496967
  · exact B1496971
  · exact B1496975
  · exact B1496979
  · exact B1496983
  · exact B1496987
  · exact B1496991
  · exact B1496995
  · exact B1496999
  · exact B1497003
  · exact B1497007
  · exact B1497011
  · exact B1497015
  · exact B1497019
  · exact B1497023
  · exact B1497027
  · exact B1497031
  · exact B1497035
  · exact B1497039
  · exact B1497043
  · exact B1497047
  · exact B1497051
  · exact B1497055
  · exact B1497059
  · exact B1497063
  · exact B1497067
  · exact B1497071
  · exact B1497075
  · exact B1497079
  · exact B1497083
  · exact B1497087
  · exact B1497091
  · exact B1497095
  · exact B1497099
  · exact B1497103
  · exact B1497107
  · exact B1497111
  · exact B1497115
  · exact B1497119
  · exact B1497123
  · exact B1497127
  · exact B1497131
  · exact B1497135
  · exact B1497139
  · exact B1497143
  · exact B1497147
  · exact B1497151
  · exact B1497155
  · exact B1497159
  · exact B1497163
  · exact B1497167
  · exact B1497171
  · exact B1497175
  · exact B1497179
  · exact B1497183
  · exact B1497187
  · exact B1497191
  · exact B1497195
  · exact B1497199
  · exact B1497203
  · exact B1497207
  · exact B1497211
  · exact B1497215
  · exact B1497219
  · exact B1497223
  · exact B1497227
  · exact B1497231
  · exact B1497235
  · exact B1497239
  · exact B1497243
  · exact B1497247
  · exact B1497251
  · exact B1497255
  · exact B1497259
  · exact B1497263
  · exact B1497267
  · exact B1497271
  · exact B1497275
  · exact B1497279
  · exact B1497283
  · exact B1497287
  · exact B1497291
  · exact B1497295
  · exact B1497299
  · exact B1497303
  · exact B1497307
  · exact B1497311
  · exact B1497315
  · exact B1497319
  · exact B1497323
  · exact B1497327
  · exact B1497331
  · exact B1497335
  · exact B1497339
  · exact B1497343
  · exact B1497347
  · exact B1497351
  · exact B1497355
  · exact B1497359
  · exact B1497363
  · exact B1497367
  · exact B1497371
  · exact B1497375
  · exact B1497379
  · exact B1497383
  · exact B1497387
  · exact B1497391
  · exact B1497395
  · exact B1497399
  · exact B1497403
  · exact B1497407
  · exact B1497411
  · exact B1497415
  · exact B1497419
  · exact B1497423
  · exact B1497427
  · exact B1497431
  · exact B1497435
  · exact B1497439
  · exact B1497443
  · exact B1497447
  · exact B1497451
  · exact B1497455
  · exact B1497459
  · exact B1497463
  · exact B1497467
  · exact B1497471
  · exact B1497475
  · exact B1497479
  · exact B1497483
  · exact B1497487
  · exact B1497491
  · exact B1497495
  · exact B1497499
  · exact B1497503
  · exact B1497507
  · exact B1497511
  · exact B1497515
  · exact B1497519
  · exact B1497523
  · exact B1497527
  · exact B1497531
  · exact B1497535
  · exact B1497539
  · exact B1497543
  · exact B1497547
  · exact B1497551
  · exact B1497555
  · exact B1497559
  · exact B1497563
  · exact B1497567
  · exact B1497571
  · exact B1497575
  · exact B1497579
  · exact B1497583
  · exact B1497587
  · exact B1497591
  · exact B1497595
  · exact B1497599
  · exact B1497603
  · exact B1497607
  · exact B1497611
  · exact B1497615
  · exact B1497619
  · exact B1497623
  · exact B1497627
  · exact B1497631
  · exact B1497635
  · exact B1497639
  · exact B1497643
  · exact B1497647
  · exact B1497651
  · exact B1497655
  · exact B1497659
  · exact B1497663
  · exact B1497667
  · exact B1497671
  · exact B1497675
  · exact B1497679
  · exact B1497683
  · exact B1497687
  · exact B1497691
  · exact B1497695
  · exact B1497699
  · exact B1497703
  · exact B1497707
  · exact B1497711
  · exact B1497715
  · exact B1497719
  · exact B1497723
  · exact B1497727
  · exact B1497731
  · exact B1497735
  · exact B1497739
  · exact B1497743
  · exact B1497747
  · exact B1497751
  · exact B1497755
  · exact B1497759
  · exact B1497763
  · exact B1497767
  · exact B1497771
  · exact B1497775
  · exact B1497779
  · exact B1497783
  · exact B1497787
  · exact B1497791
  · exact B1497795
  · exact B1497799
  · exact B1497803
  · exact B1497807
  · exact B1497811
  · exact B1497815
  · exact B1497819
  · exact B1497823
  · exact B1497827
  · exact B1497831
  · exact B1497835
  · exact B1497839
  · exact B1497843
  · exact B1497847
  · exact B1497851
  · exact B1497855
  · exact B1497859
  · exact B1497863
  · exact B1497867
  · exact B1497871
  · exact B1497875
  · exact B1497879
  · exact B1497883
  · exact B1497887
  · exact B1497891
  · exact B1497895
  · exact B1497899
  · exact B1497903
  · exact B1497907
  · exact B1497911
  · exact B1497915
  · exact B1497919
  · exact B1497923
  · exact B1497927
  · exact B1497931
  · exact B1497935
  · exact B1497939
  · exact B1497943
  · exact B1497947
  · exact B1497951
  · exact B1497955
  · exact B1497959
  · exact B1497963
  · exact B1497967
  · exact B1497971
  · exact B1497975
  · exact B1497979
  · exact B1497983
  · exact B1497987
  · exact B1497991
  · exact B1497995
  · exact B1497999
  · exact B1498003
  · exact B1498007
  · exact B1498011
  · exact B1498015
  · exact B1498019
  · exact B1498023
  · exact B1498027
  · exact B1498031
  · exact B1498035
  · exact B1498039
  · exact B1498043
  · exact B1498047
  · exact B1498051
  · exact B1498055
  · exact B1498059
  · exact B1498063
  · exact B1498067

theorem solution (m : ℕ) (hlo : 1496068 ≤ m) (hhi : m ≤ 1498068) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 374017 ≤ j := by omega
    have hj2 : j ≤ 374516 := by omega
    have hb : Blo 1496068 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
