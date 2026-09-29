-- Prove2me | solution 1 for syracuse_descends_range_670310_674310
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:52.377654+00:00
-- url     : https://prove2.me/submissions/a827e291-7ae7-4489-ab2c-9491e4bb0bb8

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


theorem B1146893 : Blo 670310 1146893 := bbase (se 3 (by rfl) ⟨215042, by rfl⟩ : syracuseStep 1146893 = 430085) (by norm_num)
theorem B1146901 : Blo 670310 1146901 := bbase (se 6 (by rfl) ⟨26880, by rfl⟩ : syracuseStep 1146901 = 53761) (by norm_num)
theorem B1278013 : Blo 670310 1278013 := bbase (se 3 (by rfl) ⟨239627, by rfl⟩ : syracuseStep 1278013 = 479255) (by norm_num)
theorem B852049 : Blo 670310 852049 := bbase (se 2 (by rfl) ⟨319518, by rfl⟩ : syracuseStep 852049 = 639037) (by norm_num)
theorem B1212517 : Blo 670310 1212517 := bbase (se 4 (by rfl) ⟨113673, by rfl⟩ : syracuseStep 1212517 = 227347) (by norm_num)
theorem B1704037 : Blo 670310 1704037 := bbase (se 4 (by rfl) ⟨159753, by rfl⟩ : syracuseStep 1704037 = 319507) (by norm_num)
theorem B1212581 : Blo 670310 1212581 := bbase (se 4 (by rfl) ⟨113679, by rfl⟩ : syracuseStep 1212581 = 227359) (by norm_num)
theorem B1704149 : Blo 670310 1704149 := bbase (se 7 (by rfl) ⟨19970, by rfl⟩ : syracuseStep 1704149 = 39941) (by norm_num)
theorem B1278173 : Blo 670310 1278173 := bbase (se 3 (by rfl) ⟨239657, by rfl⟩ : syracuseStep 1278173 = 479315) (by norm_num)
theorem B852221 : Blo 670310 852221 := bbase (se 3 (by rfl) ⟨159791, by rfl⟩ : syracuseStep 852221 = 319583) (by norm_num)
theorem B852277 : Blo 670310 852277 := bbase (se 5 (by rfl) ⟨39950, by rfl⟩ : syracuseStep 852277 = 79901) (by norm_num)
theorem B1278317 : Blo 670310 1278317 := bbase (se 3 (by rfl) ⟨239684, by rfl⟩ : syracuseStep 1278317 = 479369) (by norm_num)
theorem B1704341 : Blo 670310 1704341 := bbase (se 6 (by rfl) ⟨39945, by rfl⟩ : syracuseStep 1704341 = 79891) (by norm_num)
theorem B852373 : Blo 670310 852373 := bbase (se 6 (by rfl) ⟨19977, by rfl⟩ : syracuseStep 852373 = 39955) (by norm_num)
theorem B754105 : Blo 670310 754105 := bbase (se 2 (by rfl) ⟨282789, by rfl⟩ : syracuseStep 754105 = 565579) (by norm_num)
theorem B754141 : Blo 670310 754141 := bbase (se 3 (by rfl) ⟨141401, by rfl⟩ : syracuseStep 754141 = 282803) (by norm_num)
theorem B754177 : Blo 670310 754177 := bbase (se 2 (by rfl) ⟨282816, by rfl⟩ : syracuseStep 754177 = 565633) (by norm_num)
theorem B754213 : Blo 670310 754213 := bbase (se 4 (by rfl) ⟨70707, by rfl⟩ : syracuseStep 754213 = 141415) (by norm_num)
theorem B852545 : Blo 670310 852545 := bbase (se 2 (by rfl) ⟨319704, by rfl⟩ : syracuseStep 852545 = 639409) (by norm_num)
theorem B754249 : Blo 670310 754249 := bbase (se 2 (by rfl) ⟨282843, by rfl⟩ : syracuseStep 754249 = 565687) (by norm_num)
theorem B754285 : Blo 670310 754285 := bbase (se 3 (by rfl) ⟨141428, by rfl⟩ : syracuseStep 754285 = 282857) (by norm_num)
theorem B688753 : Blo 670310 688753 := bbase (se 2 (by rfl) ⟨258282, by rfl⟩ : syracuseStep 688753 = 516565) (by norm_num)
theorem B852601 : Blo 670310 852601 := bbase (se 2 (by rfl) ⟨319725, by rfl⟩ : syracuseStep 852601 = 639451) (by norm_num)
theorem B1278605 : Blo 670310 1278605 := bbase (se 3 (by rfl) ⟨239738, by rfl⟩ : syracuseStep 1278605 = 479477) (by norm_num)
theorem B754321 : Blo 670310 754321 := bbase (se 2 (by rfl) ⟨282870, by rfl⟩ : syracuseStep 754321 = 565741) (by norm_num)
theorem B754357 : Blo 670310 754357 := bbase (se 5 (by rfl) ⟨35360, by rfl⟩ : syracuseStep 754357 = 70721) (by norm_num)
theorem B754393 : Blo 670310 754393 := bbase (se 2 (by rfl) ⟨282897, by rfl⟩ : syracuseStep 754393 = 565795) (by norm_num)
theorem B852697 : Blo 670310 852697 := bbase (se 2 (by rfl) ⟨319761, by rfl⟩ : syracuseStep 852697 = 639523) (by norm_num)
theorem B1704685 : Blo 670310 1704685 := bbase (se 3 (by rfl) ⟨319628, by rfl⟩ : syracuseStep 1704685 = 639257) (by norm_num)
theorem B754429 : Blo 670310 754429 := bbase (se 3 (by rfl) ⟨141455, by rfl⟩ : syracuseStep 754429 = 282911) (by norm_num)
theorem B754465 : Blo 670310 754465 := bbase (se 2 (by rfl) ⟨282924, by rfl⟩ : syracuseStep 754465 = 565849) (by norm_num)
theorem B1278757 : Blo 670310 1278757 := bbase (se 4 (by rfl) ⟨119883, by rfl⟩ : syracuseStep 1278757 = 239767) (by norm_num)
theorem B754501 : Blo 670310 754501 := bbase (se 4 (by rfl) ⟨70734, by rfl⟩ : syracuseStep 754501 = 141469) (by norm_num)
theorem B1704797 : Blo 670310 1704797 := bbase (se 3 (by rfl) ⟨319649, by rfl⟩ : syracuseStep 1704797 = 639299) (by norm_num)
theorem B754537 : Blo 670310 754537 := bbase (se 2 (by rfl) ⟨282951, by rfl⟩ : syracuseStep 754537 = 565903) (by norm_num)
theorem B820081 : Blo 670310 820081 := bbase (se 2 (by rfl) ⟨307530, by rfl⟩ : syracuseStep 820081 = 615061) (by norm_num)
theorem B852869 : Blo 670310 852869 := bbase (se 4 (by rfl) ⟨79956, by rfl⟩ : syracuseStep 852869 = 159913) (by norm_num)
theorem B1508237 : Blo 670310 1508237 := bbase (se 3 (by rfl) ⟨282794, by rfl⟩ : syracuseStep 1508237 = 565589) (by norm_num)
theorem B754573 : Blo 670310 754573 := bbase (se 3 (by rfl) ⟨141482, by rfl⟩ : syracuseStep 754573 = 282965) (by norm_num)
theorem B754609 : Blo 670310 754609 := bbase (se 2 (by rfl) ⟨282978, by rfl⟩ : syracuseStep 754609 = 565957) (by norm_num)
theorem B852925 : Blo 670310 852925 := bbase (se 3 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 852925 = 319847) (by norm_num)
theorem B1508309 : Blo 670310 1508309 := bbase (se 7 (by rfl) ⟨17675, by rfl⟩ : syracuseStep 1508309 = 35351) (by norm_num)
theorem B754645 : Blo 670310 754645 := bbase (se 7 (by rfl) ⟨8843, by rfl⟩ : syracuseStep 754645 = 17687) (by norm_num)
theorem B754681 : Blo 670310 754681 := bbase (se 2 (by rfl) ⟨283005, by rfl⟩ : syracuseStep 754681 = 566011) (by norm_num)
theorem B1508381 : Blo 670310 1508381 := bbase (se 3 (by rfl) ⟨282821, by rfl⟩ : syracuseStep 1508381 = 565643) (by norm_num)
theorem B754717 : Blo 670310 754717 := bbase (se 3 (by rfl) ⟨141509, by rfl⟩ : syracuseStep 754717 = 283019) (by norm_num)
theorem B1704989 : Blo 670310 1704989 := bbase (se 3 (by rfl) ⟨319685, by rfl⟩ : syracuseStep 1704989 = 639371) (by norm_num)
theorem B853021 : Blo 670310 853021 := bbase (se 3 (by rfl) ⟨159941, by rfl⟩ : syracuseStep 853021 = 319883) (by norm_num)
theorem B754753 : Blo 670310 754753 := bbase (se 2 (by rfl) ⟨283032, by rfl⟩ : syracuseStep 754753 = 566065) (by norm_num)
theorem B3408965 : Blo 670310 3408965 := bbase (se 4 (by rfl) ⟨319590, by rfl⟩ : syracuseStep 3408965 = 639181) (by norm_num)
theorem B1279061 : Blo 670310 1279061 := bbase (se 8 (by rfl) ⟨7494, by rfl⟩ : syracuseStep 1279061 = 14989) (by norm_num)
theorem B1508453 : Blo 670310 1508453 := bbase (se 4 (by rfl) ⟨141417, by rfl⟩ : syracuseStep 1508453 = 282835) (by norm_num)
theorem B754789 : Blo 670310 754789 := bbase (se 4 (by rfl) ⟨70761, by rfl⟩ : syracuseStep 754789 = 141523) (by norm_num)
theorem B754825 : Blo 670310 754825 := bbase (se 2 (by rfl) ⟨283059, by rfl⟩ : syracuseStep 754825 = 566119) (by norm_num)
theorem B6915221 : Blo 670310 6915221 := bbase (se 6 (by rfl) ⟨162075, by rfl⟩ : syracuseStep 6915221 = 324151) (by norm_num)
theorem B1508525 : Blo 670310 1508525 := bbase (se 3 (by rfl) ⟨282848, by rfl⟩ : syracuseStep 1508525 = 565697) (by norm_num)
theorem B754861 : Blo 670310 754861 := bbase (se 3 (by rfl) ⟨141536, by rfl⟩ : syracuseStep 754861 = 283073) (by norm_num)
theorem B853193 : Blo 670310 853193 := bbase (se 2 (by rfl) ⟨319947, by rfl⟩ : syracuseStep 853193 = 639895) (by norm_num)
theorem B754897 : Blo 670310 754897 := bbase (se 2 (by rfl) ⟨283086, by rfl⟩ : syracuseStep 754897 = 566173) (by norm_num)
theorem B1508597 : Blo 670310 1508597 := bbase (se 5 (by rfl) ⟨70715, by rfl⟩ : syracuseStep 1508597 = 141431) (by norm_num)
theorem B754933 : Blo 670310 754933 := bbase (se 5 (by rfl) ⟨35387, by rfl⟩ : syracuseStep 754933 = 70775) (by norm_num)
theorem B853249 : Blo 670310 853249 := bbase (se 2 (by rfl) ⟨319968, by rfl⟩ : syracuseStep 853249 = 639937) (by norm_num)
theorem B754969 : Blo 670310 754969 := bbase (se 2 (by rfl) ⟨283113, by rfl⟩ : syracuseStep 754969 = 566227) (by norm_num)
theorem B918821 : Blo 670310 918821 := bbase (se 4 (by rfl) ⟨86139, by rfl⟩ : syracuseStep 918821 = 172279) (by norm_num)
theorem B1508669 : Blo 670310 1508669 := bbase (se 3 (by rfl) ⟨282875, by rfl⟩ : syracuseStep 1508669 = 565751) (by norm_num)
theorem B755005 : Blo 670310 755005 := bbase (se 3 (by rfl) ⟨141563, by rfl⟩ : syracuseStep 755005 = 283127) (by norm_num)
theorem B755041 : Blo 670310 755041 := bbase (se 2 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 755041 = 566281) (by norm_num)
theorem B853345 : Blo 670310 853345 := bbase (se 2 (by rfl) ⟨320004, by rfl⟩ : syracuseStep 853345 = 640009) (by norm_num)
theorem B5113205 : Blo 670310 5113205 := bbase (se 5 (by rfl) ⟨239681, by rfl⟩ : syracuseStep 5113205 = 479363) (by norm_num)
theorem B1705333 : Blo 670310 1705333 := bbase (se 5 (by rfl) ⟨79937, by rfl⟩ : syracuseStep 1705333 = 159875) (by norm_num)
theorem B1508741 : Blo 670310 1508741 := bbase (se 4 (by rfl) ⟨141444, by rfl⟩ : syracuseStep 1508741 = 282889) (by norm_num)
theorem B755077 : Blo 670310 755077 := bbase (se 4 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 755077 = 141577) (by norm_num)
theorem B2262437 : Blo 670310 2262437 := bbase (se 4 (by rfl) ⟨212103, by rfl⟩ : syracuseStep 2262437 = 424207) (by norm_num)
theorem B755113 : Blo 670310 755113 := bbase (se 2 (by rfl) ⟨283167, by rfl⟩ : syracuseStep 755113 = 566335) (by norm_num)
theorem B1508813 : Blo 670310 1508813 := bbase (se 3 (by rfl) ⟨282902, by rfl⟩ : syracuseStep 1508813 = 565805) (by norm_num)
theorem B755149 : Blo 670310 755149 := bbase (se 3 (by rfl) ⟨141590, by rfl⟩ : syracuseStep 755149 = 283181) (by norm_num)
theorem B1705445 : Blo 670310 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B755185 : Blo 670310 755185 := bbase (se 2 (by rfl) ⟨283194, by rfl⟩ : syracuseStep 755185 = 566389) (by norm_num)
theorem B1508885 : Blo 670310 1508885 := bbase (se 6 (by rfl) ⟨35364, by rfl⟩ : syracuseStep 1508885 = 70729) (by norm_num)
theorem B755221 : Blo 670310 755221 := bbase (se 6 (by rfl) ⟨17700, by rfl⟩ : syracuseStep 755221 = 35401) (by norm_num)
theorem B755257 : Blo 670310 755257 := bbase (se 2 (by rfl) ⟨283221, by rfl⟩ : syracuseStep 755257 = 566443) (by norm_num)
theorem B1508957 : Blo 670310 1508957 := bbase (se 3 (by rfl) ⟨282929, by rfl⟩ : syracuseStep 1508957 = 565859) (by norm_num)
theorem B755293 : Blo 670310 755293 := bbase (se 3 (by rfl) ⟨141617, by rfl⟩ : syracuseStep 755293 = 283235) (by norm_num)
theorem B755329 : Blo 670310 755329 := bbase (se 2 (by rfl) ⟨283248, by rfl⟩ : syracuseStep 755329 = 566497) (by norm_num)
theorem B1509029 : Blo 670310 1509029 := bbase (se 4 (by rfl) ⟨141471, by rfl⟩ : syracuseStep 1509029 = 282943) (by norm_num)
theorem B755365 : Blo 670310 755365 := bbase (se 4 (by rfl) ⟨70815, by rfl⟩ : syracuseStep 755365 = 141631) (by norm_num)
theorem B1705637 : Blo 670310 1705637 := bbase (se 4 (by rfl) ⟨159903, by rfl⟩ : syracuseStep 1705637 = 319807) (by norm_num)
theorem B755401 : Blo 670310 755401 := bbase (se 2 (by rfl) ⟨283275, by rfl⟩ : syracuseStep 755401 = 566551) (by norm_num)
theorem B1148645 : Blo 670310 1148645 := bbase (se 4 (by rfl) ⟨107685, by rfl⟩ : syracuseStep 1148645 = 215371) (by norm_num)
theorem B1509101 : Blo 670310 1509101 := bbase (se 3 (by rfl) ⟨282956, by rfl⟩ : syracuseStep 1509101 = 565913) (by norm_num)
theorem B755437 : Blo 670310 755437 := bbase (se 3 (by rfl) ⟨141644, by rfl⟩ : syracuseStep 755437 = 283289) (by norm_num)
theorem B755473 : Blo 670310 755473 := bbase (se 2 (by rfl) ⟨283302, by rfl⟩ : syracuseStep 755473 = 566605) (by norm_num)
theorem B1509173 : Blo 670310 1509173 := bbase (se 5 (by rfl) ⟨70742, by rfl⟩ : syracuseStep 1509173 = 141485) (by norm_num)
theorem B755509 : Blo 670310 755509 := bbase (se 5 (by rfl) ⟨35414, by rfl⟩ : syracuseStep 755509 = 70829) (by norm_num)
theorem B1279813 : Blo 670310 1279813 := bbase (se 4 (by rfl) ⟨119982, by rfl⟩ : syracuseStep 1279813 = 239965) (by norm_num)
theorem B2262869 : Blo 670310 2262869 := bbase (se 9 (by rfl) ⟨6629, by rfl⟩ : syracuseStep 2262869 = 13259) (by norm_num)
theorem B755545 : Blo 670310 755545 := bbase (se 2 (by rfl) ⟨283329, by rfl⟩ : syracuseStep 755545 = 566659) (by norm_num)
theorem B1509245 : Blo 670310 1509245 := bbase (se 3 (by rfl) ⟨282983, by rfl⟩ : syracuseStep 1509245 = 565967) (by norm_num)
theorem B755581 : Blo 670310 755581 := bbase (se 3 (by rfl) ⟨141671, by rfl⟩ : syracuseStep 755581 = 283343) (by norm_num)
theorem B755617 : Blo 670310 755617 := bbase (se 2 (by rfl) ⟨283356, by rfl⟩ : syracuseStep 755617 = 566713) (by norm_num)
theorem B1509317 : Blo 670310 1509317 := bbase (se 4 (by rfl) ⟨141498, by rfl⟩ : syracuseStep 1509317 = 282997) (by norm_num)
theorem B755653 : Blo 670310 755653 := bbase (se 4 (by rfl) ⟨70842, by rfl⟩ : syracuseStep 755653 = 141685) (by norm_num)
theorem B21792725 : Blo 670310 21792725 := bbase (se 7 (by rfl) ⟨255383, by rfl⟩ : syracuseStep 21792725 = 510767) (by norm_num)
theorem B1279957 : Blo 670310 1279957 := bbase (se 7 (by rfl) ⟨14999, by rfl⟩ : syracuseStep 1279957 = 29999) (by norm_num)
theorem B2557925 : Blo 670310 2557925 := bbase (se 4 (by rfl) ⟨239805, by rfl⟩ : syracuseStep 2557925 = 479611) (by norm_num)
theorem B755689 : Blo 670310 755689 := bbase (se 2 (by rfl) ⟨283383, by rfl⟩ : syracuseStep 755689 = 566767) (by norm_num)
theorem B1705981 : Blo 670310 1705981 := bbase (se 3 (by rfl) ⟨319871, by rfl⟩ : syracuseStep 1705981 = 639743) (by norm_num)
theorem B1509389 : Blo 670310 1509389 := bbase (se 3 (by rfl) ⟨283010, by rfl⟩ : syracuseStep 1509389 = 566021) (by norm_num)
theorem B755725 : Blo 670310 755725 := bbase (se 3 (by rfl) ⟨141698, by rfl⟩ : syracuseStep 755725 = 283397) (by norm_num)
theorem B1640461 : Blo 670310 1640461 := bbase (se 3 (by rfl) ⟨307586, by rfl⟩ : syracuseStep 1640461 = 615173) (by norm_num)
theorem B755761 : Blo 670310 755761 := bbase (se 2 (by rfl) ⟨283410, by rfl⟩ : syracuseStep 755761 = 566821) (by norm_num)
theorem B1509461 : Blo 670310 1509461 := bbase (se 8 (by rfl) ⟨8844, by rfl⟩ : syracuseStep 1509461 = 17689) (by norm_num)
theorem B755797 : Blo 670310 755797 := bbase (se 8 (by rfl) ⟨4428, by rfl⟩ : syracuseStep 755797 = 8857) (by norm_num)
theorem B1706093 : Blo 670310 1706093 := bbase (se 3 (by rfl) ⟨319892, by rfl⟩ : syracuseStep 1706093 = 639785) (by norm_num)
theorem B1280117 : Blo 670310 1280117 := bbase (se 5 (by rfl) ⟨60005, by rfl⟩ : syracuseStep 1280117 = 120011) (by norm_num)
theorem B755833 : Blo 670310 755833 := bbase (se 2 (by rfl) ⟨283437, by rfl⟩ : syracuseStep 755833 = 566875) (by norm_num)
theorem B1509533 : Blo 670310 1509533 := bbase (se 3 (by rfl) ⟨283037, by rfl⟩ : syracuseStep 1509533 = 566075) (by norm_num)
theorem B755869 : Blo 670310 755869 := bbase (se 3 (by rfl) ⟨141725, by rfl⟩ : syracuseStep 755869 = 283451) (by norm_num)
theorem B755905 : Blo 670310 755905 := bbase (se 2 (by rfl) ⟨283464, by rfl⟩ : syracuseStep 755905 = 566929) (by norm_num)
theorem B1509605 : Blo 670310 1509605 := bbase (se 4 (by rfl) ⟨141525, by rfl⟩ : syracuseStep 1509605 = 283051) (by norm_num)
theorem B755941 : Blo 670310 755941 := bbase (se 4 (by rfl) ⟨70869, by rfl⟩ : syracuseStep 755941 = 141739) (by norm_num)
theorem B2263301 : Blo 670310 2263301 := bbase (se 4 (by rfl) ⟨212184, by rfl⟩ : syracuseStep 2263301 = 424369) (by norm_num)
theorem B2558213 : Blo 670310 2558213 := bbase (se 4 (by rfl) ⟨239832, by rfl⟩ : syracuseStep 2558213 = 479665) (by norm_num)
theorem B755977 : Blo 670310 755977 := bbase (se 2 (by rfl) ⟨283491, by rfl⟩ : syracuseStep 755977 = 566983) (by norm_num)
theorem B1509677 : Blo 670310 1509677 := bbase (se 3 (by rfl) ⟨283064, by rfl⟩ : syracuseStep 1509677 = 566129) (by norm_num)
theorem B756013 : Blo 670310 756013 := bbase (se 3 (by rfl) ⟨141752, by rfl⟩ : syracuseStep 756013 = 283505) (by norm_num)
theorem B1706285 : Blo 670310 1706285 := bbase (se 3 (by rfl) ⟨319928, by rfl⟩ : syracuseStep 1706285 = 639857) (by norm_num)
theorem B756049 : Blo 670310 756049 := bbase (se 2 (by rfl) ⟨283518, by rfl⟩ : syracuseStep 756049 = 567037) (by norm_num)
theorem B3410261 : Blo 670310 3410261 := bbase (se 10 (by rfl) ⟨4995, by rfl⟩ : syracuseStep 3410261 = 9991) (by norm_num)
theorem B2754917 : Blo 670310 2754917 := bbase (se 4 (by rfl) ⟨258273, by rfl⟩ : syracuseStep 2754917 = 516547) (by norm_num)
theorem B1509749 : Blo 670310 1509749 := bbase (se 5 (by rfl) ⟨70769, by rfl⟩ : syracuseStep 1509749 = 141539) (by norm_num)
theorem B756085 : Blo 670310 756085 := bbase (se 5 (by rfl) ⟨35441, by rfl⟩ : syracuseStep 756085 = 70883) (by norm_num)
theorem B1968533 : Blo 670310 1968533 := bbase (se 6 (by rfl) ⟨46137, by rfl⟩ : syracuseStep 1968533 = 92275) (by norm_num)
theorem B756121 : Blo 670310 756121 := bbase (se 2 (by rfl) ⟨283545, by rfl⟩ : syracuseStep 756121 = 567091) (by norm_num)
theorem B1509821 : Blo 670310 1509821 := bbase (se 3 (by rfl) ⟨283091, by rfl⟩ : syracuseStep 1509821 = 566183) (by norm_num)
theorem B756157 : Blo 670310 756157 := bbase (se 3 (by rfl) ⟨141779, by rfl⟩ : syracuseStep 756157 = 283559) (by norm_num)
theorem B756193 : Blo 670310 756193 := bbase (se 2 (by rfl) ⟨283572, by rfl⟩ : syracuseStep 756193 = 567145) (by norm_num)
theorem B1509893 : Blo 670310 1509893 := bbase (se 4 (by rfl) ⟨141552, by rfl⟩ : syracuseStep 1509893 = 283105) (by norm_num)
theorem B756229 : Blo 670310 756229 := bbase (se 4 (by rfl) ⟨70896, by rfl⟩ : syracuseStep 756229 = 141793) (by norm_num)
theorem B756265 : Blo 670310 756265 := bbase (se 2 (by rfl) ⟨283599, by rfl⟩ : syracuseStep 756265 = 567199) (by norm_num)
theorem B1509965 : Blo 670310 1509965 := bbase (se 3 (by rfl) ⟨283118, by rfl⟩ : syracuseStep 1509965 = 566237) (by norm_num)
theorem B756301 : Blo 670310 756301 := bbase (se 3 (by rfl) ⟨141806, by rfl⟩ : syracuseStep 756301 = 283613) (by norm_num)
theorem B2722405 : Blo 670310 2722405 := bbase (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) (by norm_num)
theorem B756337 : Blo 670310 756337 := bbase (se 2 (by rfl) ⟨283626, by rfl⟩ : syracuseStep 756337 = 567253) (by norm_num)
theorem B1706629 : Blo 670310 1706629 := bbase (se 4 (by rfl) ⟨159996, by rfl⟩ : syracuseStep 1706629 = 319993) (by norm_num)
theorem B1510037 : Blo 670310 1510037 := bbase (se 6 (by rfl) ⟨35391, by rfl⟩ : syracuseStep 1510037 = 70783) (by norm_num)
theorem B756373 : Blo 670310 756373 := bbase (se 6 (by rfl) ⟨17727, by rfl⟩ : syracuseStep 756373 = 35455) (by norm_num)
theorem B2263733 : Blo 670310 2263733 := bbase (se 5 (by rfl) ⟨106112, by rfl⟩ : syracuseStep 2263733 = 212225) (by norm_num)
theorem B756409 : Blo 670310 756409 := bbase (se 2 (by rfl) ⟨283653, by rfl⟩ : syracuseStep 756409 = 567307) (by norm_num)
theorem B1510109 : Blo 670310 1510109 := bbase (se 3 (by rfl) ⟨283145, by rfl⟩ : syracuseStep 1510109 = 566291) (by norm_num)
theorem B756445 : Blo 670310 756445 := bbase (se 3 (by rfl) ⟨141833, by rfl⟩ : syracuseStep 756445 = 283667) (by norm_num)
theorem B1706741 : Blo 670310 1706741 := bbase (se 5 (by rfl) ⟨80003, by rfl⟩ : syracuseStep 1706741 = 160007) (by norm_num)
theorem B756481 : Blo 670310 756481 := bbase (se 2 (by rfl) ⟨283680, by rfl⟩ : syracuseStep 756481 = 567361) (by norm_num)
theorem B1510181 : Blo 670310 1510181 := bbase (se 4 (by rfl) ⟨141579, by rfl⟩ : syracuseStep 1510181 = 283159) (by norm_num)
theorem B756517 : Blo 670310 756517 := bbase (se 4 (by rfl) ⟨70923, by rfl⟩ : syracuseStep 756517 = 141847) (by norm_num)
theorem B756553 : Blo 670310 756553 := bbase (se 2 (by rfl) ⟨283707, by rfl⟩ : syracuseStep 756553 = 567415) (by norm_num)
theorem B1510253 : Blo 670310 1510253 := bbase (se 3 (by rfl) ⟨283172, by rfl⟩ : syracuseStep 1510253 = 566345) (by norm_num)
theorem B756589 : Blo 670310 756589 := bbase (se 3 (by rfl) ⟨141860, by rfl⟩ : syracuseStep 756589 = 283721) (by norm_num)
theorem B756625 : Blo 670310 756625 := bbase (se 2 (by rfl) ⟨283734, by rfl⟩ : syracuseStep 756625 = 567469) (by norm_num)
theorem B1510325 : Blo 670310 1510325 := bbase (se 5 (by rfl) ⟨70796, by rfl⟩ : syracuseStep 1510325 = 141593) (by norm_num)
theorem B756661 : Blo 670310 756661 := bbase (se 5 (by rfl) ⟨35468, by rfl⟩ : syracuseStep 756661 = 70937) (by norm_num)
theorem B756697 : Blo 670310 756697 := bbase (se 2 (by rfl) ⟨283761, by rfl⟩ : syracuseStep 756697 = 567523) (by norm_num)
theorem B1510397 : Blo 670310 1510397 := bbase (se 3 (by rfl) ⟨283199, by rfl⟩ : syracuseStep 1510397 = 566399) (by norm_num)
theorem B756733 : Blo 670310 756733 := bbase (se 3 (by rfl) ⟨141887, by rfl⟩ : syracuseStep 756733 = 283775) (by norm_num)
theorem B756769 : Blo 670310 756769 := bbase (se 2 (by rfl) ⟨283788, by rfl⟩ : syracuseStep 756769 = 567577) (by norm_num)
theorem B1510469 : Blo 670310 1510469 := bbase (se 4 (by rfl) ⟨141606, by rfl⟩ : syracuseStep 1510469 = 283213) (by norm_num)
theorem B756805 : Blo 670310 756805 := bbase (se 4 (by rfl) ⟨70950, by rfl⟩ : syracuseStep 756805 = 141901) (by norm_num)
theorem B6458453 : Blo 670310 6458453 := bbase (se 8 (by rfl) ⟨37842, by rfl⟩ : syracuseStep 6458453 = 75685) (by norm_num)
theorem B2264165 : Blo 670310 2264165 := bbase (se 4 (by rfl) ⟨212265, by rfl⟩ : syracuseStep 2264165 = 424531) (by norm_num)
theorem B756841 : Blo 670310 756841 := bbase (se 2 (by rfl) ⟨283815, by rfl⟩ : syracuseStep 756841 = 567631) (by norm_num)
theorem B1510541 : Blo 670310 1510541 := bbase (se 3 (by rfl) ⟨283226, by rfl⟩ : syracuseStep 1510541 = 566453) (by norm_num)
theorem B756877 : Blo 670310 756877 := bbase (se 3 (by rfl) ⟨141914, by rfl⟩ : syracuseStep 756877 = 283829) (by norm_num)
theorem B756913 : Blo 670310 756913 := bbase (se 2 (by rfl) ⟨283842, by rfl⟩ : syracuseStep 756913 = 567685) (by norm_num)
theorem B1510613 : Blo 670310 1510613 := bbase (se 7 (by rfl) ⟨17702, by rfl⟩ : syracuseStep 1510613 = 35405) (by norm_num)
theorem B756949 : Blo 670310 756949 := bbase (se 7 (by rfl) ⟨8870, by rfl⟩ : syracuseStep 756949 = 17741) (by norm_num)
theorem B756985 : Blo 670310 756985 := bbase (se 2 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 756985 = 567739) (by norm_num)
theorem B1510685 : Blo 670310 1510685 := bbase (se 3 (by rfl) ⟨283253, by rfl⟩ : syracuseStep 1510685 = 566507) (by norm_num)
theorem B757021 : Blo 670310 757021 := bbase (se 3 (by rfl) ⟨141941, by rfl⟩ : syracuseStep 757021 = 283883) (by norm_num)
theorem B757057 : Blo 670310 757057 := bbase (se 2 (by rfl) ⟨283896, by rfl⟩ : syracuseStep 757057 = 567793) (by norm_num)
theorem B1510757 : Blo 670310 1510757 := bbase (se 4 (by rfl) ⟨141633, by rfl⟩ : syracuseStep 1510757 = 283267) (by norm_num)
theorem B757093 : Blo 670310 757093 := bbase (se 4 (by rfl) ⟨70977, by rfl⟩ : syracuseStep 757093 = 141955) (by norm_num)
theorem B757129 : Blo 670310 757129 := bbase (se 2 (by rfl) ⟨283923, by rfl⟩ : syracuseStep 757129 = 567847) (by norm_num)
theorem B1019285 : Blo 670310 1019285 := bbase (se 6 (by rfl) ⟨23889, by rfl⟩ : syracuseStep 1019285 = 47779) (by norm_num)
theorem B2559397 : Blo 670310 2559397 := bbase (se 4 (by rfl) ⟨239943, by rfl⟩ : syracuseStep 2559397 = 479887) (by norm_num)
theorem B1510829 : Blo 670310 1510829 := bbase (se 3 (by rfl) ⟨283280, by rfl⟩ : syracuseStep 1510829 = 566561) (by norm_num)
theorem B757165 : Blo 670310 757165 := bbase (se 3 (by rfl) ⟨141968, by rfl⟩ : syracuseStep 757165 = 283937) (by norm_num)
theorem B3837365 : Blo 670310 3837365 := bbase (se 5 (by rfl) ⟨179876, by rfl⟩ : syracuseStep 3837365 = 359753) (by norm_num)
theorem B757201 : Blo 670310 757201 := bbase (se 2 (by rfl) ⟨283950, by rfl⟩ : syracuseStep 757201 = 567901) (by norm_num)
theorem B1510901 : Blo 670310 1510901 := bbase (se 5 (by rfl) ⟨70823, by rfl⟩ : syracuseStep 1510901 = 141647) (by norm_num)
theorem B757237 : Blo 670310 757237 := bbase (se 5 (by rfl) ⟨35495, by rfl⟩ : syracuseStep 757237 = 70991) (by norm_num)
theorem B1019413 : Blo 670310 1019413 := bbase (se 6 (by rfl) ⟨23892, by rfl⟩ : syracuseStep 1019413 = 47785) (by norm_num)
theorem B2264597 : Blo 670310 2264597 := bbase (se 6 (by rfl) ⟨53076, by rfl⟩ : syracuseStep 2264597 = 106153) (by norm_num)
theorem B757273 : Blo 670310 757273 := bbase (se 2 (by rfl) ⟨283977, by rfl⟩ : syracuseStep 757273 = 567955) (by norm_num)
theorem B1510973 : Blo 670310 1510973 := bbase (se 3 (by rfl) ⟨283307, by rfl⟩ : syracuseStep 1510973 = 566615) (by norm_num)
theorem B757309 : Blo 670310 757309 := bbase (se 3 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 757309 = 283991) (by norm_num)
theorem B2068037 : Blo 670310 2068037 := bbase (se 4 (by rfl) ⟨193878, by rfl⟩ : syracuseStep 2068037 = 387757) (by norm_num)
theorem B2362949 : Blo 670310 2362949 := bbase (se 4 (by rfl) ⟨221526, by rfl⟩ : syracuseStep 2362949 = 443053) (by norm_num)
theorem B757345 : Blo 670310 757345 := bbase (se 2 (by rfl) ⟨284004, by rfl⟩ : syracuseStep 757345 = 568009) (by norm_num)
theorem B3411557 : Blo 670310 3411557 := bbase (se 4 (by rfl) ⟨319833, by rfl⟩ : syracuseStep 3411557 = 639667) (by norm_num)
theorem B1511045 : Blo 670310 1511045 := bbase (se 4 (by rfl) ⟨141660, by rfl⟩ : syracuseStep 1511045 = 283321) (by norm_num)
theorem B757381 : Blo 670310 757381 := bbase (se 4 (by rfl) ⟨71004, by rfl⟩ : syracuseStep 757381 = 142009) (by norm_num)
theorem B757417 : Blo 670310 757417 := bbase (se 2 (by rfl) ⟨284031, by rfl⟩ : syracuseStep 757417 = 568063) (by norm_num)
theorem B1511117 : Blo 670310 1511117 := bbase (se 3 (by rfl) ⟨283334, by rfl⟩ : syracuseStep 1511117 = 566669) (by norm_num)
theorem B757453 : Blo 670310 757453 := bbase (se 3 (by rfl) ⟨142022, by rfl⟩ : syracuseStep 757453 = 284045) (by norm_num)
theorem B2559701 : Blo 670310 2559701 := bbase (se 7 (by rfl) ⟨29996, by rfl⟩ : syracuseStep 2559701 = 59993) (by norm_num)
theorem B757489 : Blo 670310 757489 := bbase (se 2 (by rfl) ⟨284058, by rfl⟩ : syracuseStep 757489 = 568117) (by norm_num)
theorem B1511189 : Blo 670310 1511189 := bbase (se 6 (by rfl) ⟨35418, by rfl⟩ : syracuseStep 1511189 = 70837) (by norm_num)
theorem B757525 : Blo 670310 757525 := bbase (se 6 (by rfl) ⟨17754, by rfl⟩ : syracuseStep 757525 = 35509) (by norm_num)
theorem B757561 : Blo 670310 757561 := bbase (se 2 (by rfl) ⟨284085, by rfl⟩ : syracuseStep 757561 = 568171) (by norm_num)
theorem B1511261 : Blo 670310 1511261 := bbase (se 3 (by rfl) ⟨283361, by rfl⟩ : syracuseStep 1511261 = 566723) (by norm_num)
theorem B757597 : Blo 670310 757597 := bbase (se 3 (by rfl) ⟨142049, by rfl⟩ : syracuseStep 757597 = 284099) (by norm_num)
theorem B757633 : Blo 670310 757633 := bbase (se 2 (by rfl) ⟨284112, by rfl⟩ : syracuseStep 757633 = 568225) (by norm_num)
theorem B1511333 : Blo 670310 1511333 := bbase (se 4 (by rfl) ⟨141687, by rfl⟩ : syracuseStep 1511333 = 283375) (by norm_num)
theorem B757669 : Blo 670310 757669 := bbase (se 4 (by rfl) ⟨71031, by rfl⟩ : syracuseStep 757669 = 142063) (by norm_num)
theorem B2265029 : Blo 670310 2265029 := bbase (se 4 (by rfl) ⟨212346, by rfl⟩ : syracuseStep 2265029 = 424693) (by norm_num)
theorem B757705 : Blo 670310 757705 := bbase (se 2 (by rfl) ⟨284139, by rfl⟩ : syracuseStep 757705 = 568279) (by norm_num)
theorem B692173 : Blo 670310 692173 := bbase (se 3 (by rfl) ⟨129782, by rfl⟩ : syracuseStep 692173 = 259565) (by norm_num)
theorem B11636693 : Blo 670310 11636693 := bbase (se 7 (by rfl) ⟨136367, by rfl⟩ : syracuseStep 11636693 = 272735) (by norm_num)
theorem B1511405 : Blo 670310 1511405 := bbase (se 3 (by rfl) ⟨283388, by rfl⟩ : syracuseStep 1511405 = 566777) (by norm_num)
theorem B757741 : Blo 670310 757741 := bbase (se 3 (by rfl) ⟨142076, by rfl⟩ : syracuseStep 757741 = 284153) (by norm_num)
theorem B757777 : Blo 670310 757777 := bbase (se 2 (by rfl) ⟨284166, by rfl⟩ : syracuseStep 757777 = 568333) (by norm_num)
theorem B1511477 : Blo 670310 1511477 := bbase (se 5 (by rfl) ⟨70850, by rfl⟩ : syracuseStep 1511477 = 141701) (by norm_num)
theorem B757813 : Blo 670310 757813 := bbase (se 5 (by rfl) ⟨35522, by rfl⟩ : syracuseStep 757813 = 71045) (by norm_num)
theorem B757849 : Blo 670310 757849 := bbase (se 2 (by rfl) ⟨284193, by rfl⟩ : syracuseStep 757849 = 568387) (by norm_num)
theorem B1511549 : Blo 670310 1511549 := bbase (se 3 (by rfl) ⟨283415, by rfl⟩ : syracuseStep 1511549 = 566831) (by norm_num)
theorem B757885 : Blo 670310 757885 := bbase (se 3 (by rfl) ⟨142103, by rfl⟩ : syracuseStep 757885 = 284207) (by norm_num)
theorem B757921 : Blo 670310 757921 := bbase (se 2 (by rfl) ⟨284220, by rfl⟩ : syracuseStep 757921 = 568441) (by norm_num)
theorem B1511621 : Blo 670310 1511621 := bbase (se 4 (by rfl) ⟨141714, by rfl⟩ : syracuseStep 1511621 = 283429) (by norm_num)
theorem B757957 : Blo 670310 757957 := bbase (se 4 (by rfl) ⟨71058, by rfl⟩ : syracuseStep 757957 = 142117) (by norm_num)
theorem B757993 : Blo 670310 757993 := bbase (se 2 (by rfl) ⟨284247, by rfl⟩ : syracuseStep 757993 = 568495) (by norm_num)
theorem B1511693 : Blo 670310 1511693 := bbase (se 3 (by rfl) ⟨283442, by rfl⟩ : syracuseStep 1511693 = 566885) (by norm_num)
theorem B758029 : Blo 670310 758029 := bbase (se 3 (by rfl) ⟨142130, by rfl⟩ : syracuseStep 758029 = 284261) (by norm_num)
theorem B758065 : Blo 670310 758065 := bbase (se 2 (by rfl) ⟨284274, by rfl⟩ : syracuseStep 758065 = 568549) (by norm_num)
theorem B4297045 : Blo 670310 4297045 := bbase (se 10 (by rfl) ⟨6294, by rfl⟩ : syracuseStep 4297045 = 12589) (by norm_num)
theorem B1511765 : Blo 670310 1511765 := bbase (se 10 (by rfl) ⟨2214, by rfl⟩ : syracuseStep 1511765 = 4429) (by norm_num)
theorem B758101 : Blo 670310 758101 := bbase (se 10 (by rfl) ⟨1110, by rfl⟩ : syracuseStep 758101 = 2221) (by norm_num)
theorem B2265461 : Blo 670310 2265461 := bbase (se 5 (by rfl) ⟨106193, by rfl⟩ : syracuseStep 2265461 = 212387) (by norm_num)
theorem B758137 : Blo 670310 758137 := bbase (se 2 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 758137 = 568603) (by norm_num)
theorem B954757 : Blo 670310 954757 := bbase (se 4 (by rfl) ⟨89508, by rfl⟩ : syracuseStep 954757 = 179017) (by norm_num)
theorem B1511837 : Blo 670310 1511837 := bbase (se 3 (by rfl) ⟨283469, by rfl⟩ : syracuseStep 1511837 = 566939) (by norm_num)
theorem B758173 : Blo 670310 758173 := bbase (se 3 (by rfl) ⟨142157, by rfl⟩ : syracuseStep 758173 = 284315) (by norm_num)
theorem B758209 : Blo 670310 758209 := bbase (se 2 (by rfl) ⟨284328, by rfl⟩ : syracuseStep 758209 = 568657) (by norm_num)
theorem B1511909 : Blo 670310 1511909 := bbase (se 4 (by rfl) ⟨141741, by rfl⟩ : syracuseStep 1511909 = 283483) (by norm_num)
theorem B758245 : Blo 670310 758245 := bbase (se 4 (by rfl) ⟨71085, by rfl⟩ : syracuseStep 758245 = 142171) (by norm_num)
theorem B758281 : Blo 670310 758281 := bbase (se 2 (by rfl) ⟨284355, by rfl⟩ : syracuseStep 758281 = 568711) (by norm_num)
theorem B1511981 : Blo 670310 1511981 := bbase (se 3 (by rfl) ⟨283496, by rfl⟩ : syracuseStep 1511981 = 566993) (by norm_num)
theorem B758317 : Blo 670310 758317 := bbase (se 3 (by rfl) ⟨142184, by rfl⟩ : syracuseStep 758317 = 284369) (by norm_num)
theorem B758353 : Blo 670310 758353 := bbase (se 2 (by rfl) ⟨284382, by rfl⟩ : syracuseStep 758353 = 568765) (by norm_num)
theorem B3838549 : Blo 670310 3838549 := bbase (se 8 (by rfl) ⟨22491, by rfl⟩ : syracuseStep 3838549 = 44983) (by norm_num)
theorem B1151581 : Blo 670310 1151581 := bbase (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) (by norm_num)
theorem B1512053 : Blo 670310 1512053 := bbase (se 5 (by rfl) ⟨70877, by rfl⟩ : syracuseStep 1512053 = 141755) (by norm_num)
theorem B758389 : Blo 670310 758389 := bbase (se 5 (by rfl) ⟨35549, by rfl⟩ : syracuseStep 758389 = 71099) (by norm_num)
theorem B758425 : Blo 670310 758425 := bbase (se 2 (by rfl) ⟨284409, by rfl⟩ : syracuseStep 758425 = 568819) (by norm_num)
theorem B1512125 : Blo 670310 1512125 := bbase (se 3 (by rfl) ⟨283523, by rfl⟩ : syracuseStep 1512125 = 567047) (by norm_num)
theorem B758461 : Blo 670310 758461 := bbase (se 3 (by rfl) ⟨142211, by rfl⟩ : syracuseStep 758461 = 284423) (by norm_num)
theorem B955093 : Blo 670310 955093 := bbase (se 7 (by rfl) ⟨11192, by rfl⟩ : syracuseStep 955093 = 22385) (by norm_num)
theorem B1020629 : Blo 670310 1020629 := bbase (se 7 (by rfl) ⟨11960, by rfl⟩ : syracuseStep 1020629 = 23921) (by norm_num)
theorem B758497 : Blo 670310 758497 := bbase (se 2 (by rfl) ⟨284436, by rfl⟩ : syracuseStep 758497 = 568873) (by norm_num)
theorem B1512197 : Blo 670310 1512197 := bbase (se 4 (by rfl) ⟨141768, by rfl⟩ : syracuseStep 1512197 = 283537) (by norm_num)
theorem B758533 : Blo 670310 758533 := bbase (se 4 (by rfl) ⟨71112, by rfl⟩ : syracuseStep 758533 = 142225) (by norm_num)
theorem B2265893 : Blo 670310 2265893 := bbase (se 4 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 2265893 = 424855) (by norm_num)
theorem B758569 : Blo 670310 758569 := bbase (se 2 (by rfl) ⟨284463, by rfl⟩ : syracuseStep 758569 = 568927) (by norm_num)
theorem B1512269 : Blo 670310 1512269 := bbase (se 3 (by rfl) ⟨283550, by rfl⟩ : syracuseStep 1512269 = 567101) (by norm_num)
theorem B3412853 : Blo 670310 3412853 := bbase (se 5 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 3412853 = 319955) (by norm_num)
theorem B1512341 : Blo 670310 1512341 := bbase (se 6 (by rfl) ⟨35445, by rfl⟩ : syracuseStep 1512341 = 70891) (by norm_num)
theorem B1020829 : Blo 670310 1020829 := bbase (se 3 (by rfl) ⟨191405, by rfl⟩ : syracuseStep 1020829 = 382811) (by norm_num)
theorem B955309 : Blo 670310 955309 := bbase (se 3 (by rfl) ⟨179120, by rfl⟩ : syracuseStep 955309 = 358241) (by norm_num)
theorem B1512413 : Blo 670310 1512413 := bbase (se 3 (by rfl) ⟨283577, by rfl⟩ : syracuseStep 1512413 = 567155) (by norm_num)
theorem B726013 : Blo 670310 726013 := bbase (se 3 (by rfl) ⟨136127, by rfl⟩ : syracuseStep 726013 = 272255) (by norm_num)
theorem B1512485 : Blo 670310 1512485 := bbase (se 4 (by rfl) ⟨141795, by rfl⟩ : syracuseStep 1512485 = 283591) (by norm_num)
theorem B2430005 : Blo 670310 2430005 := bbase (se 5 (by rfl) ⟨113906, by rfl⟩ : syracuseStep 2430005 = 227813) (by norm_num)
theorem B1512557 : Blo 670310 1512557 := bbase (se 3 (by rfl) ⟨283604, by rfl⟩ : syracuseStep 1512557 = 567209) (by norm_num)
theorem B1512629 : Blo 670310 1512629 := bbase (se 5 (by rfl) ⟨70904, by rfl⟩ : syracuseStep 1512629 = 141809) (by norm_num)
theorem B1021133 : Blo 670310 1021133 := bbase (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) (by norm_num)
theorem B2266325 : Blo 670310 2266325 := bbase (se 7 (by rfl) ⟨26558, by rfl⟩ : syracuseStep 2266325 = 53117) (by norm_num)
theorem B2495701 : Blo 670310 2495701 := bbase (se 7 (by rfl) ⟨29246, by rfl⟩ : syracuseStep 2495701 = 58493) (by norm_num)
theorem B1512701 : Blo 670310 1512701 := bbase (se 3 (by rfl) ⟨283631, by rfl⟩ : syracuseStep 1512701 = 567263) (by norm_num)
theorem B726289 : Blo 670310 726289 := bbase (se 2 (by rfl) ⟨272358, by rfl⟩ : syracuseStep 726289 = 544717) (by norm_num)
theorem B955685 : Blo 670310 955685 := bbase (se 4 (by rfl) ⟨89595, by rfl⟩ : syracuseStep 955685 = 179191) (by norm_num)
theorem B1512773 : Blo 670310 1512773 := bbase (se 4 (by rfl) ⟨141822, by rfl⟩ : syracuseStep 1512773 = 283645) (by norm_num)
theorem B1611085 : Blo 670310 1611085 := bbase (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) (by norm_num)
theorem B1512845 : Blo 670310 1512845 := bbase (se 3 (by rfl) ⟨283658, by rfl⟩ : syracuseStep 1512845 = 567317) (by norm_num)
theorem B1611181 : Blo 670310 1611181 := bbase (se 3 (by rfl) ⟨302096, by rfl⟩ : syracuseStep 1611181 = 604193) (by norm_num)
theorem B1512917 : Blo 670310 1512917 := bbase (se 7 (by rfl) ⟨17729, by rfl⟩ : syracuseStep 1512917 = 35459) (by norm_num)
theorem B1512989 : Blo 670310 1512989 := bbase (se 3 (by rfl) ⟨283685, by rfl⟩ : syracuseStep 1512989 = 567371) (by norm_num)
theorem B1513061 : Blo 670310 1513061 := bbase (se 4 (by rfl) ⟨141849, by rfl⟩ : syracuseStep 1513061 = 283699) (by norm_num)
theorem B2266757 : Blo 670310 2266757 := bbase (se 4 (by rfl) ⟨212508, by rfl⟩ : syracuseStep 2266757 = 425017) (by norm_num)
theorem B1513133 : Blo 670310 1513133 := bbase (se 3 (by rfl) ⟨283712, by rfl⟩ : syracuseStep 1513133 = 567425) (by norm_num)
theorem B1513205 : Blo 670310 1513205 := bbase (se 5 (by rfl) ⟨70931, by rfl⟩ : syracuseStep 1513205 = 141863) (by norm_num)
theorem B1513277 : Blo 670310 1513277 := bbase (se 3 (by rfl) ⟨283739, by rfl⟩ : syracuseStep 1513277 = 567479) (by norm_num)
theorem B1513349 : Blo 670310 1513349 := bbase (se 4 (by rfl) ⟨141876, by rfl⟩ : syracuseStep 1513349 = 283753) (by norm_num)
theorem B1611701 : Blo 670310 1611701 := bbase (se 5 (by rfl) ⟨75548, by rfl⟩ : syracuseStep 1611701 = 151097) (by norm_num)
theorem B1513421 : Blo 670310 1513421 := bbase (se 3 (by rfl) ⟨283766, by rfl⟩ : syracuseStep 1513421 = 567533) (by norm_num)
theorem B1513493 : Blo 670310 1513493 := bbase (se 6 (by rfl) ⟨35472, by rfl⟩ : syracuseStep 1513493 = 70945) (by norm_num)
theorem B1021997 : Blo 670310 1021997 := bbase (se 3 (by rfl) ⟨191624, by rfl⟩ : syracuseStep 1021997 = 383249) (by norm_num)
theorem B2267189 : Blo 670310 2267189 := bbase (se 5 (by rfl) ⟨106274, by rfl⟩ : syracuseStep 2267189 = 212549) (by norm_num)
theorem B1513565 : Blo 670310 1513565 := bbase (se 3 (by rfl) ⟨283793, by rfl⟩ : syracuseStep 1513565 = 567587) (by norm_num)
theorem B3545189 : Blo 670310 3545189 := bbase (se 4 (by rfl) ⟨332361, by rfl⟩ : syracuseStep 3545189 = 664723) (by norm_num)
theorem B1513637 : Blo 670310 1513637 := bbase (se 4 (by rfl) ⟨141903, by rfl⟩ : syracuseStep 1513637 = 283807) (by norm_num)
theorem B1513709 : Blo 670310 1513709 := bbase (se 3 (by rfl) ⟨283820, by rfl⟩ : syracuseStep 1513709 = 567641) (by norm_num)
theorem B1513781 : Blo 670310 1513781 := bbase (se 5 (by rfl) ⟨70958, by rfl⟩ : syracuseStep 1513781 = 141917) (by norm_num)
theorem B1513853 : Blo 670310 1513853 := bbase (se 3 (by rfl) ⟨283847, by rfl⟩ : syracuseStep 1513853 = 567695) (by norm_num)
theorem B1612229 : Blo 670310 1612229 := bbase (se 4 (by rfl) ⟨151146, by rfl⟩ : syracuseStep 1612229 = 302293) (by norm_num)
theorem B1513925 : Blo 670310 1513925 := bbase (se 4 (by rfl) ⟨141930, by rfl⟩ : syracuseStep 1513925 = 283861) (by norm_num)
theorem B3447269 : Blo 670310 3447269 := bbase (se 4 (by rfl) ⟨323181, by rfl⟩ : syracuseStep 3447269 = 646363) (by norm_num)
theorem B2267621 : Blo 670310 2267621 := bbase (se 4 (by rfl) ⟨212589, by rfl⟩ : syracuseStep 2267621 = 425179) (by norm_num)
theorem B1513997 : Blo 670310 1513997 := bbase (se 3 (by rfl) ⟨283874, by rfl⟩ : syracuseStep 1513997 = 567749) (by norm_num)
theorem B1514069 : Blo 670310 1514069 := bbase (se 8 (by rfl) ⟨8871, by rfl⟩ : syracuseStep 1514069 = 17743) (by norm_num)
theorem B1514141 : Blo 670310 1514141 := bbase (se 3 (by rfl) ⟨283901, by rfl⟩ : syracuseStep 1514141 = 567803) (by norm_num)
theorem B1612469 : Blo 670310 1612469 := bbase (se 5 (by rfl) ⟨75584, by rfl⟩ : syracuseStep 1612469 = 151169) (by norm_num)
theorem B957109 : Blo 670310 957109 := bbase (se 5 (by rfl) ⟨44864, by rfl⟩ : syracuseStep 957109 = 89729) (by norm_num)
theorem B1514213 : Blo 670310 1514213 := bbase (se 4 (by rfl) ⟨141957, by rfl⟩ : syracuseStep 1514213 = 283915) (by norm_num)
theorem B1514285 : Blo 670310 1514285 := bbase (se 3 (by rfl) ⟨283928, by rfl⟩ : syracuseStep 1514285 = 567857) (by norm_num)
theorem B1514357 : Blo 670310 1514357 := bbase (se 5 (by rfl) ⟨70985, by rfl⟩ : syracuseStep 1514357 = 141971) (by norm_num)
theorem B2268053 : Blo 670310 2268053 := bbase (se 6 (by rfl) ⟨53157, by rfl⟩ : syracuseStep 2268053 = 106315) (by norm_num)
theorem B1514429 : Blo 670310 1514429 := bbase (se 3 (by rfl) ⟨283955, by rfl⟩ : syracuseStep 1514429 = 567911) (by norm_num)
theorem B1514501 : Blo 670310 1514501 := bbase (se 4 (by rfl) ⟨141984, by rfl⟩ : syracuseStep 1514501 = 283969) (by norm_num)
theorem B1514573 : Blo 670310 1514573 := bbase (se 3 (by rfl) ⟨283982, by rfl⟩ : syracuseStep 1514573 = 567965) (by norm_num)
theorem B1514645 : Blo 670310 1514645 := bbase (se 6 (by rfl) ⟨35499, by rfl⟩ : syracuseStep 1514645 = 70999) (by norm_num)
theorem B1514717 : Blo 670310 1514717 := bbase (se 3 (by rfl) ⟨284009, by rfl⟩ : syracuseStep 1514717 = 568019) (by norm_num)
theorem B957701 : Blo 670310 957701 := bbase (se 4 (by rfl) ⟨89784, by rfl⟩ : syracuseStep 957701 = 179569) (by norm_num)
theorem B1514789 : Blo 670310 1514789 := bbase (se 4 (by rfl) ⟨142011, by rfl⟩ : syracuseStep 1514789 = 284023) (by norm_num)
theorem B2268485 : Blo 670310 2268485 := bbase (se 4 (by rfl) ⟨212670, by rfl⟩ : syracuseStep 2268485 = 425341) (by norm_num)
theorem B957781 : Blo 670310 957781 := bbase (se 11 (by rfl) ⟨701, by rfl⟩ : syracuseStep 957781 = 1403) (by norm_num)
theorem B1514861 : Blo 670310 1514861 := bbase (se 3 (by rfl) ⟨284036, by rfl⟩ : syracuseStep 1514861 = 568073) (by norm_num)
theorem B1514933 : Blo 670310 1514933 := bbase (se 5 (by rfl) ⟨71012, by rfl⟩ : syracuseStep 1514933 = 142025) (by norm_num)
theorem B957901 : Blo 670310 957901 := bbase (se 3 (by rfl) ⟨179606, by rfl⟩ : syracuseStep 957901 = 359213) (by norm_num)
theorem B1515005 : Blo 670310 1515005 := bbase (se 3 (by rfl) ⟨284063, by rfl⟩ : syracuseStep 1515005 = 568127) (by norm_num)
theorem B957997 : Blo 670310 957997 := bbase (se 3 (by rfl) ⟨179624, by rfl⟩ : syracuseStep 957997 = 359249) (by norm_num)
theorem B1515077 : Blo 670310 1515077 := bbase (se 4 (by rfl) ⟨142038, by rfl⟩ : syracuseStep 1515077 = 284077) (by norm_num)
theorem B1515149 : Blo 670310 1515149 := bbase (se 3 (by rfl) ⟨284090, by rfl⟩ : syracuseStep 1515149 = 568181) (by norm_num)
theorem B1515221 : Blo 670310 1515221 := bbase (se 7 (by rfl) ⟨17756, by rfl⟩ : syracuseStep 1515221 = 35513) (by norm_num)
theorem B3448565 : Blo 670310 3448565 := bbase (se 5 (by rfl) ⟨161651, by rfl⟩ : syracuseStep 3448565 = 323303) (by norm_num)
theorem B2268917 : Blo 670310 2268917 := bbase (se 5 (by rfl) ⟨106355, by rfl⟩ : syracuseStep 2268917 = 212711) (by norm_num)
theorem B6463253 : Blo 670310 6463253 := bbase (se 6 (by rfl) ⟨151482, by rfl⟩ : syracuseStep 6463253 = 302965) (by norm_num)
theorem B1515293 : Blo 670310 1515293 := bbase (se 3 (by rfl) ⟨284117, by rfl⟩ : syracuseStep 1515293 = 568235) (by norm_num)
theorem B3645269 : Blo 670310 3645269 := bbase (se 9 (by rfl) ⟨10679, by rfl⟩ : syracuseStep 3645269 = 21359) (by norm_num)
theorem B1515365 : Blo 670310 1515365 := bbase (se 4 (by rfl) ⟨142065, by rfl⟩ : syracuseStep 1515365 = 284131) (by norm_num)
theorem B860053 : Blo 670310 860053 := bbase (se 6 (by rfl) ⟨20157, by rfl⟩ : syracuseStep 860053 = 40315) (by norm_num)
theorem B2039701 : Blo 670310 2039701 := bbase (se 6 (by rfl) ⟨47805, by rfl⟩ : syracuseStep 2039701 = 95611) (by norm_num)
theorem B1515437 : Blo 670310 1515437 := bbase (se 3 (by rfl) ⟨284144, by rfl⟩ : syracuseStep 1515437 = 568289) (by norm_num)
theorem B1515509 : Blo 670310 1515509 := bbase (se 5 (by rfl) ⟨71039, by rfl⟩ : syracuseStep 1515509 = 142079) (by norm_num)
theorem B958493 : Blo 670310 958493 := bbase (se 3 (by rfl) ⟨179717, by rfl⟩ : syracuseStep 958493 = 359435) (by norm_num)
theorem B1515581 : Blo 670310 1515581 := bbase (se 3 (by rfl) ⟨284171, by rfl⟩ : syracuseStep 1515581 = 568343) (by norm_num)
theorem B1515653 : Blo 670310 1515653 := bbase (se 4 (by rfl) ⟨142092, by rfl⟩ : syracuseStep 1515653 = 284185) (by norm_num)
theorem B2269349 : Blo 670310 2269349 := bbase (se 4 (by rfl) ⟨212751, by rfl⟩ : syracuseStep 2269349 = 425503) (by norm_num)
theorem B1515725 : Blo 670310 1515725 := bbase (se 3 (by rfl) ⟨284198, by rfl⟩ : syracuseStep 1515725 = 568397) (by norm_num)
theorem B4301045 : Blo 670310 4301045 := bbase (se 5 (by rfl) ⟨201611, by rfl⟩ : syracuseStep 4301045 = 403223) (by norm_num)
theorem B1515797 : Blo 670310 1515797 := bbase (se 6 (by rfl) ⟨35526, by rfl⟩ : syracuseStep 1515797 = 71053) (by norm_num)
theorem B1515869 : Blo 670310 1515869 := bbase (se 3 (by rfl) ⟨284225, by rfl⟩ : syracuseStep 1515869 = 568451) (by norm_num)
theorem B1614181 : Blo 670310 1614181 := bbase (se 4 (by rfl) ⟨151329, by rfl⟩ : syracuseStep 1614181 = 302659) (by norm_num)
theorem B1515941 : Blo 670310 1515941 := bbase (se 4 (by rfl) ⟨142119, by rfl⟩ : syracuseStep 1515941 = 284239) (by norm_num)
theorem B1516013 : Blo 670310 1516013 := bbase (se 3 (by rfl) ⟨284252, by rfl⟩ : syracuseStep 1516013 = 568505) (by norm_num)
theorem B1090061 : Blo 670310 1090061 := bbase (se 3 (by rfl) ⟨204386, by rfl⟩ : syracuseStep 1090061 = 408773) (by norm_num)
theorem B1516085 : Blo 670310 1516085 := bbase (se 5 (by rfl) ⟨71066, by rfl⟩ : syracuseStep 1516085 = 142133) (by norm_num)
theorem B959045 : Blo 670310 959045 := bbase (se 4 (by rfl) ⟨89910, by rfl⟩ : syracuseStep 959045 = 179821) (by norm_num)
theorem B1024589 : Blo 670310 1024589 := bbase (se 3 (by rfl) ⟨192110, by rfl⟩ : syracuseStep 1024589 = 384221) (by norm_num)
theorem B2269781 : Blo 670310 2269781 := bbase (se 8 (by rfl) ⟨13299, by rfl⟩ : syracuseStep 2269781 = 26599) (by norm_num)
theorem B1516157 : Blo 670310 1516157 := bbase (se 3 (by rfl) ⟨284279, by rfl⟩ : syracuseStep 1516157 = 568559) (by norm_num)
theorem B1516229 : Blo 670310 1516229 := bbase (se 4 (by rfl) ⟨142146, by rfl⟩ : syracuseStep 1516229 = 284293) (by norm_num)
theorem B860873 : Blo 670310 860873 := bbase (se 2 (by rfl) ⟨322827, by rfl⟩ : syracuseStep 860873 = 645655) (by norm_num)
theorem B1516301 : Blo 670310 1516301 := bbase (se 3 (by rfl) ⟨284306, by rfl⟩ : syracuseStep 1516301 = 568613) (by norm_num)
theorem B1516373 : Blo 670310 1516373 := bbase (se 9 (by rfl) ⟨4442, by rfl⟩ : syracuseStep 1516373 = 8885) (by norm_num)
theorem B2040709 : Blo 670310 2040709 := bbase (se 4 (by rfl) ⟨191316, by rfl⟩ : syracuseStep 2040709 = 382633) (by norm_num)
theorem B1516445 : Blo 670310 1516445 := bbase (se 3 (by rfl) ⟨284333, by rfl⟩ : syracuseStep 1516445 = 568667) (by norm_num)
theorem B6202325 : Blo 670310 6202325 := bbase (se 7 (by rfl) ⟨72683, by rfl⟩ : syracuseStep 6202325 = 145367) (by norm_num)
theorem B9675733 : Blo 670310 9675733 := bbase (se 7 (by rfl) ⟨113387, by rfl⟩ : syracuseStep 9675733 = 226775) (by norm_num)
theorem B1516517 : Blo 670310 1516517 := bbase (se 4 (by rfl) ⟨142173, by rfl⟩ : syracuseStep 1516517 = 284347) (by norm_num)
theorem B2270213 : Blo 670310 2270213 := bbase (se 4 (by rfl) ⟨212832, by rfl⟩ : syracuseStep 2270213 = 425665) (by norm_num)
theorem B1516589 : Blo 670310 1516589 := bbase (se 3 (by rfl) ⟨284360, by rfl⟩ : syracuseStep 1516589 = 568721) (by norm_num)
theorem B4138037 : Blo 670310 4138037 := bbase (se 5 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 4138037 = 387941) (by norm_num)
theorem B1516661 : Blo 670310 1516661 := bbase (se 5 (by rfl) ⟨71093, by rfl⟩ : syracuseStep 1516661 = 142187) (by norm_num)
theorem B1090685 : Blo 670310 1090685 := bbase (se 3 (by rfl) ⟨204503, by rfl⟩ : syracuseStep 1090685 = 409007) (by norm_num)
theorem B1516733 : Blo 670310 1516733 := bbase (se 3 (by rfl) ⟨284387, by rfl⟩ : syracuseStep 1516733 = 568775) (by norm_num)
theorem B1516805 : Blo 670310 1516805 := bbase (se 4 (by rfl) ⟨142200, by rfl⟩ : syracuseStep 1516805 = 284401) (by norm_num)
theorem B959797 : Blo 670310 959797 := bbase (se 5 (by rfl) ⟨44990, by rfl⟩ : syracuseStep 959797 = 89981) (by norm_num)
theorem B1516877 : Blo 670310 1516877 := bbase (se 3 (by rfl) ⟨284414, by rfl⟩ : syracuseStep 1516877 = 568829) (by norm_num)
theorem B1910117 : Blo 670310 1910117 := bbase (se 4 (by rfl) ⟨179073, by rfl⟩ : syracuseStep 1910117 = 358147) (by norm_num)
theorem B1516949 : Blo 670310 1516949 := bbase (se 6 (by rfl) ⟨35553, by rfl⟩ : syracuseStep 1516949 = 71107) (by norm_num)
theorem B2270645 : Blo 670310 2270645 := bbase (se 5 (by rfl) ⟨106436, by rfl⟩ : syracuseStep 2270645 = 212873) (by norm_num)
theorem B1811909 : Blo 670310 1811909 := bbase (se 4 (by rfl) ⟨169866, by rfl⟩ : syracuseStep 1811909 = 339733) (by norm_num)
theorem B1517021 : Blo 670310 1517021 := bbase (se 3 (by rfl) ⟨284441, by rfl⟩ : syracuseStep 1517021 = 568883) (by norm_num)
theorem B1517093 : Blo 670310 1517093 := bbase (se 4 (by rfl) ⟨142227, by rfl⟩ : syracuseStep 1517093 = 284455) (by norm_num)
theorem B1517165 : Blo 670310 1517165 := bbase (se 3 (by rfl) ⟨284468, by rfl⟩ : syracuseStep 1517165 = 568937) (by norm_num)
theorem B1615621 : Blo 670310 1615621 := bbase (se 4 (by rfl) ⟨151464, by rfl⟩ : syracuseStep 1615621 = 302929) (by norm_num)
theorem B2271077 : Blo 670310 2271077 := bbase (se 4 (by rfl) ⟨212913, by rfl⟩ : syracuseStep 2271077 = 425827) (by norm_num)
theorem B9218069 : Blo 670310 9218069 := bbase (se 6 (by rfl) ⟨216048, by rfl⟩ : syracuseStep 9218069 = 432097) (by norm_num)
theorem B3451045 : Blo 670310 3451045 := bbase (se 4 (by rfl) ⟨323535, by rfl⟩ : syracuseStep 3451045 = 647071) (by norm_num)
theorem B2271509 : Blo 670310 2271509 := bbase (se 6 (by rfl) ⟨53238, by rfl⟩ : syracuseStep 2271509 = 106477) (by norm_num)
theorem B3451189 : Blo 670310 3451189 := bbase (se 5 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 3451189 = 323549) (by norm_num)
theorem B3221861 : Blo 670310 3221861 := bbase (se 4 (by rfl) ⟨302049, by rfl⟩ : syracuseStep 3221861 = 604099) (by norm_num)
theorem B1616237 : Blo 670310 1616237 := bbase (se 3 (by rfl) ⟨303044, by rfl⟩ : syracuseStep 1616237 = 606089) (by norm_num)
theorem B3058037 : Blo 670310 3058037 := bbase (se 5 (by rfl) ⟨143345, by rfl⟩ : syracuseStep 3058037 = 286691) (by norm_num)
theorem B3058181 : Blo 670310 3058181 := bbase (se 4 (by rfl) ⟨286704, by rfl⟩ : syracuseStep 3058181 = 573409) (by norm_num)
theorem B1944101 : Blo 670310 1944101 := bbase (se 4 (by rfl) ⟨182259, by rfl⟩ : syracuseStep 1944101 = 364519) (by norm_num)
theorem B1616429 : Blo 670310 1616429 := bbase (se 3 (by rfl) ⟨303080, by rfl⟩ : syracuseStep 1616429 = 606161) (by norm_num)
theorem B2042533 : Blo 670310 2042533 := bbase (se 4 (by rfl) ⟨191487, by rfl⟩ : syracuseStep 2042533 = 382975) (by norm_num)
theorem B2271941 : Blo 670310 2271941 := bbase (se 4 (by rfl) ⟨212994, by rfl⟩ : syracuseStep 2271941 = 425989) (by norm_num)
theorem B2730709 : Blo 670310 2730709 := bbase (se 7 (by rfl) ⟨32000, by rfl⟩ : syracuseStep 2730709 = 64001) (by norm_num)
theorem B1616717 : Blo 670310 1616717 := bbase (se 3 (by rfl) ⟨303134, by rfl⟩ : syracuseStep 1616717 = 606269) (by norm_num)
theorem B1911701 : Blo 670310 1911701 := bbase (se 6 (by rfl) ⟨44805, by rfl⟩ : syracuseStep 1911701 = 89611) (by norm_num)
theorem B1813445 : Blo 670310 1813445 := bbase (se 4 (by rfl) ⟨170010, by rfl⟩ : syracuseStep 1813445 = 340021) (by norm_num)
theorem B2272373 : Blo 670310 2272373 := bbase (se 5 (by rfl) ⟨106517, by rfl⟩ : syracuseStep 2272373 = 213035) (by norm_num)
theorem B10890389 : Blo 670310 10890389 := bbase (se 6 (by rfl) ⟨255243, by rfl⟩ : syracuseStep 10890389 = 510487) (by norm_num)
theorem B863389 : Blo 670310 863389 := bbase (se 3 (by rfl) ⟨161885, by rfl⟩ : syracuseStep 863389 = 323771) (by norm_num)
theorem B3452357 : Blo 670310 3452357 := bbase (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) (by norm_num)
theorem B863717 : Blo 670310 863717 := bbase (se 4 (by rfl) ⟨80973, by rfl⟩ : syracuseStep 863717 = 161947) (by norm_num)
theorem B2272805 : Blo 670310 2272805 := bbase (se 4 (by rfl) ⟨213075, by rfl⟩ : syracuseStep 2272805 = 426151) (by norm_num)
theorem B1912373 : Blo 670310 1912373 := bbase (se 5 (by rfl) ⟨89642, by rfl⟩ : syracuseStep 1912373 = 179285) (by norm_num)
theorem B10923605 : Blo 670310 10923605 := bbase (se 8 (by rfl) ⟨64005, by rfl⟩ : syracuseStep 10923605 = 128011) (by norm_num)
theorem B1093349 : Blo 670310 1093349 := bbase (se 4 (by rfl) ⟨102501, by rfl⟩ : syracuseStep 1093349 = 205003) (by norm_num)
theorem B2043701 : Blo 670310 2043701 := bbase (se 5 (by rfl) ⟨95798, by rfl⟩ : syracuseStep 2043701 = 191597) (by norm_num)
theorem B864209 : Blo 670310 864209 := bbase (se 2 (by rfl) ⟨324078, by rfl⟩ : syracuseStep 864209 = 648157) (by norm_num)
theorem B2273237 : Blo 670310 2273237 := bbase (se 7 (by rfl) ⟨26639, by rfl⟩ : syracuseStep 2273237 = 53279) (by norm_num)
theorem B1912805 : Blo 670310 1912805 := bbase (se 4 (by rfl) ⟨179325, by rfl⟩ : syracuseStep 1912805 = 358651) (by norm_num)
theorem B864281 : Blo 670310 864281 := bbase (se 2 (by rfl) ⟨324105, by rfl⟩ : syracuseStep 864281 = 648211) (by norm_num)
theorem B6140117 : Blo 670310 6140117 := bbase (se 7 (by rfl) ⟨71954, by rfl⟩ : syracuseStep 6140117 = 143909) (by norm_num)
theorem B766297 : Blo 670310 766297 := bbase (se 2 (by rfl) ⟨287361, by rfl⟩ : syracuseStep 766297 = 574723) (by norm_num)
theorem B2273669 : Blo 670310 2273669 := bbase (se 4 (by rfl) ⟨213156, by rfl⟩ : syracuseStep 2273669 = 426313) (by norm_num)
theorem B2306501 : Blo 670310 2306501 := bbase (se 4 (by rfl) ⟨216234, by rfl⟩ : syracuseStep 2306501 = 432469) (by norm_num)
theorem B7746005 : Blo 670310 7746005 := bbase (se 7 (by rfl) ⟨90773, by rfl⟩ : syracuseStep 7746005 = 181547) (by norm_num)
theorem B1094285 : Blo 670310 1094285 := bbase (se 3 (by rfl) ⟨205178, by rfl⟩ : syracuseStep 1094285 = 410357) (by norm_num)
theorem B11481749 : Blo 670310 11481749 := bbase (se 6 (by rfl) ⟨269103, by rfl⟩ : syracuseStep 11481749 = 538207) (by norm_num)
theorem B1913557 : Blo 670310 1913557 := bbase (se 7 (by rfl) ⟨22424, by rfl⟩ : syracuseStep 1913557 = 44849) (by norm_num)
theorem B1815317 : Blo 670310 1815317 := bbase (se 6 (by rfl) ⟨42546, by rfl⟩ : syracuseStep 1815317 = 85093) (by norm_num)
theorem B1618717 : Blo 670310 1618717 := bbase (se 3 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 1618717 = 607019) (by norm_num)
theorem B2274101 : Blo 670310 2274101 := bbase (se 5 (by rfl) ⟨106598, by rfl⟩ : syracuseStep 2274101 = 213197) (by norm_num)
theorem B2732885 : Blo 670310 2732885 := bbase (se 9 (by rfl) ⟨8006, by rfl⟩ : syracuseStep 2732885 = 16013) (by norm_num)
theorem B2274533 : Blo 670310 2274533 := bbase (se 4 (by rfl) ⟨213237, by rfl⟩ : syracuseStep 2274533 = 426475) (by norm_num)
theorem B2274965 : Blo 670310 2274965 := bbase (se 6 (by rfl) ⟨53319, by rfl⟩ : syracuseStep 2274965 = 106639) (by norm_num)
theorem B2275397 : Blo 670310 2275397 := bbase (se 4 (by rfl) ⟨213318, by rfl⟩ : syracuseStep 2275397 = 426637) (by norm_num)
theorem B1620101 : Blo 670310 1620101 := bbase (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) (by norm_num)
theorem B4307093 : Blo 670310 4307093 := bbase (se 6 (by rfl) ⟨100947, by rfl⟩ : syracuseStep 4307093 = 201895) (by norm_num)
theorem B2865365 : Blo 670310 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B5257685 : Blo 670310 5257685 := bbase (se 7 (by rfl) ⟨61613, by rfl⟩ : syracuseStep 5257685 = 123227) (by norm_num)
theorem B27605717 : Blo 670310 27605717 := bbase (se 7 (by rfl) ⟨323504, by rfl⟩ : syracuseStep 27605717 = 647009) (by norm_num)
theorem B2866373 : Blo 670310 2866373 := bbase (se 4 (by rfl) ⟨268722, by rfl⟩ : syracuseStep 2866373 = 537445) (by norm_num)
theorem B1457365 : Blo 670310 1457365 := bbase (se 7 (by rfl) ⟨17078, by rfl⟩ : syracuseStep 1457365 = 34157) (by norm_num)
theorem B1818085 : Blo 670310 1818085 := bbase (se 4 (by rfl) ⟨170445, by rfl⟩ : syracuseStep 1818085 = 340891) (by norm_num)
theorem B1916405 : Blo 670310 1916405 := bbase (se 5 (by rfl) ⟨89831, by rfl⟩ : syracuseStep 1916405 = 179663) (by norm_num)
theorem B4079861 : Blo 670310 4079861 := bbase (se 5 (by rfl) ⟨191243, by rfl⟩ : syracuseStep 4079861 = 382487) (by norm_num)
theorem B1818949 : Blo 670310 1818949 := bbase (se 4 (by rfl) ⟨170526, by rfl⟩ : syracuseStep 1818949 = 341053) (by norm_num)
theorem B1360261 : Blo 670310 1360261 := bbase (se 4 (by rfl) ⟨127524, by rfl⟩ : syracuseStep 1360261 = 255049) (by norm_num)
theorem B3228149 : Blo 670310 3228149 := bbase (se 5 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 3228149 = 302639) (by norm_num)
theorem B3228245 : Blo 670310 3228245 := bbase (se 8 (by rfl) ⟨18915, by rfl⟩ : syracuseStep 3228245 = 37831) (by norm_num)
theorem B1917589 : Blo 670310 1917589 := bbase (se 6 (by rfl) ⟨44943, by rfl⟩ : syracuseStep 1917589 = 89887) (by norm_num)
theorem B1131205 : Blo 670310 1131205 := bbase (se 4 (by rfl) ⟨106050, by rfl⟩ : syracuseStep 1131205 = 212101) (by norm_num)
theorem B2179813 : Blo 670310 2179813 := bbase (se 4 (by rfl) ⟨204357, by rfl⟩ : syracuseStep 2179813 = 408715) (by norm_num)
theorem B1131293 : Blo 670310 1131293 := bbase (se 3 (by rfl) ⟨212117, by rfl⟩ : syracuseStep 1131293 = 424235) (by norm_num)
theorem B1917749 : Blo 670310 1917749 := bbase (se 5 (by rfl) ⟨89894, by rfl⟩ : syracuseStep 1917749 = 179789) (by norm_num)
theorem B1721213 : Blo 670310 1721213 := bbase (se 3 (by rfl) ⟨322727, by rfl⟩ : syracuseStep 1721213 = 645455) (by norm_num)
theorem B1131421 : Blo 670310 1131421 := bbase (se 3 (by rfl) ⟨212141, by rfl⟩ : syracuseStep 1131421 = 424283) (by norm_num)
theorem B2868149 : Blo 670310 2868149 := bbase (se 5 (by rfl) ⟨134444, by rfl⟩ : syracuseStep 2868149 = 268889) (by norm_num)
theorem B1131509 : Blo 670310 1131509 := bbase (se 5 (by rfl) ⟨53039, by rfl⟩ : syracuseStep 1131509 = 106079) (by norm_num)
theorem B1917989 : Blo 670310 1917989 := bbase (se 4 (by rfl) ⟨179811, by rfl⟩ : syracuseStep 1917989 = 359623) (by norm_num)
theorem B1131637 : Blo 670310 1131637 := bbase (se 5 (by rfl) ⟨53045, by rfl⟩ : syracuseStep 1131637 = 106091) (by norm_num)
theorem B2802869 : Blo 670310 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B1131725 : Blo 670310 1131725 := bbase (se 3 (by rfl) ⟨212198, by rfl⟩ : syracuseStep 1131725 = 424397) (by norm_num)
theorem B1918181 : Blo 670310 1918181 := bbase (se 4 (by rfl) ⟨179829, by rfl⟩ : syracuseStep 1918181 = 359659) (by norm_num)
theorem B1230061 : Blo 670310 1230061 := bbase (se 3 (by rfl) ⟨230636, by rfl⟩ : syracuseStep 1230061 = 461273) (by norm_num)
theorem B1819909 : Blo 670310 1819909 := bbase (se 4 (by rfl) ⟨170616, by rfl⟩ : syracuseStep 1819909 = 341233) (by norm_num)
theorem B1131853 : Blo 670310 1131853 := bbase (se 3 (by rfl) ⟨212222, by rfl⟩ : syracuseStep 1131853 = 424445) (by norm_num)
theorem B1131941 : Blo 670310 1131941 := bbase (se 4 (by rfl) ⟨106119, by rfl⟩ : syracuseStep 1131941 = 212239) (by norm_num)
theorem B1132069 : Blo 670310 1132069 := bbase (se 4 (by rfl) ⟨106131, by rfl⟩ : syracuseStep 1132069 = 212263) (by norm_num)
theorem B1132157 : Blo 670310 1132157 := bbase (se 3 (by rfl) ⟨212279, by rfl⟩ : syracuseStep 1132157 = 424559) (by norm_num)
theorem B1132285 : Blo 670310 1132285 := bbase (se 3 (by rfl) ⟨212303, by rfl⟩ : syracuseStep 1132285 = 424607) (by norm_num)
theorem B1132373 : Blo 670310 1132373 := bbase (se 9 (by rfl) ⟨3317, by rfl⟩ : syracuseStep 1132373 = 6635) (by norm_num)
theorem B1296253 : Blo 670310 1296253 := bbase (se 3 (by rfl) ⟨243047, by rfl⟩ : syracuseStep 1296253 = 486095) (by norm_num)
theorem B3819413 : Blo 670310 3819413 := bbase (se 6 (by rfl) ⟨89517, by rfl⟩ : syracuseStep 3819413 = 179035) (by norm_num)
theorem B1132501 : Blo 670310 1132501 := bbase (se 7 (by rfl) ⟨13271, by rfl⟩ : syracuseStep 1132501 = 26543) (by norm_num)
theorem B1132589 : Blo 670310 1132589 := bbase (se 3 (by rfl) ⟨212360, by rfl⟩ : syracuseStep 1132589 = 424721) (by norm_num)
theorem B1132717 : Blo 670310 1132717 := bbase (se 3 (by rfl) ⟨212384, by rfl⟩ : syracuseStep 1132717 = 424769) (by norm_num)
theorem B5097653 : Blo 670310 5097653 := bbase (se 5 (by rfl) ⟨238952, by rfl⟩ : syracuseStep 5097653 = 477905) (by norm_num)
theorem B1919173 : Blo 670310 1919173 := bbase (se 4 (by rfl) ⟨179922, by rfl⟩ : syracuseStep 1919173 = 359845) (by norm_num)
theorem B1132805 : Blo 670310 1132805 := bbase (se 4 (by rfl) ⟨106200, by rfl⟩ : syracuseStep 1132805 = 212401) (by norm_num)
theorem B2148677 : Blo 670310 2148677 := bbase (se 4 (by rfl) ⟨201438, by rfl⟩ : syracuseStep 2148677 = 402877) (by norm_num)
theorem B1132933 : Blo 670310 1132933 := bbase (se 4 (by rfl) ⟨106212, by rfl⟩ : syracuseStep 1132933 = 212425) (by norm_num)
theorem B1296821 : Blo 670310 1296821 := bbase (se 5 (by rfl) ⟨60788, by rfl⟩ : syracuseStep 1296821 = 121577) (by norm_num)
theorem B3230165 : Blo 670310 3230165 := bbase (se 7 (by rfl) ⟨37853, by rfl⟩ : syracuseStep 3230165 = 75707) (by norm_num)
theorem B1133021 : Blo 670310 1133021 := bbase (se 3 (by rfl) ⟨212441, by rfl⟩ : syracuseStep 1133021 = 424883) (by norm_num)
theorem B1133149 : Blo 670310 1133149 := bbase (se 3 (by rfl) ⟨212465, by rfl⟩ : syracuseStep 1133149 = 424931) (by norm_num)
theorem B1133237 : Blo 670310 1133237 := bbase (se 5 (by rfl) ⟨53120, by rfl⟩ : syracuseStep 1133237 = 106241) (by norm_num)
theorem B1297093 : Blo 670310 1297093 := bbase (se 4 (by rfl) ⟨121602, by rfl⟩ : syracuseStep 1297093 = 243205) (by norm_num)
theorem B12896981 : Blo 670310 12896981 := bbase (se 7 (by rfl) ⟨151136, by rfl⟩ : syracuseStep 12896981 = 302273) (by norm_num)
theorem B7785173 : Blo 670310 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B6146837 : Blo 670310 6146837 := bbase (se 6 (by rfl) ⟨144066, by rfl⟩ : syracuseStep 6146837 = 288133) (by norm_num)
theorem B1133365 : Blo 670310 1133365 := bbase (se 5 (by rfl) ⟨53126, by rfl⟩ : syracuseStep 1133365 = 106253) (by norm_num)
theorem B2804597 : Blo 670310 2804597 := bbase (se 5 (by rfl) ⟨131465, by rfl⟩ : syracuseStep 2804597 = 262931) (by norm_num)
theorem B1133453 : Blo 670310 1133453 := bbase (se 3 (by rfl) ⟨212522, by rfl⟩ : syracuseStep 1133453 = 425045) (by norm_num)
theorem B1133581 : Blo 670310 1133581 := bbase (se 3 (by rfl) ⟨212546, by rfl⟩ : syracuseStep 1133581 = 425093) (by norm_num)
theorem B805961 : Blo 670310 805961 := bbase (se 2 (by rfl) ⟨302235, by rfl⟩ : syracuseStep 805961 = 604471) (by norm_num)
theorem B1133669 : Blo 670310 1133669 := bbase (se 4 (by rfl) ⟨106281, by rfl⟩ : syracuseStep 1133669 = 212563) (by norm_num)
theorem B3394709 : Blo 670310 3394709 := bbase (se 6 (by rfl) ⟨79563, by rfl⟩ : syracuseStep 3394709 = 159127) (by norm_num)
theorem B1133797 : Blo 670310 1133797 := bbase (se 4 (by rfl) ⟨106293, by rfl⟩ : syracuseStep 1133797 = 212587) (by norm_num)
theorem B1133885 : Blo 670310 1133885 := bbase (se 3 (by rfl) ⟨212603, by rfl⟩ : syracuseStep 1133885 = 425207) (by norm_num)
theorem B806269 : Blo 670310 806269 := bbase (se 3 (by rfl) ⟨151175, by rfl⟩ : syracuseStep 806269 = 302351) (by norm_num)
theorem B1723789 : Blo 670310 1723789 := bbase (se 3 (by rfl) ⟨323210, by rfl⟩ : syracuseStep 1723789 = 646421) (by norm_num)
theorem B1134013 : Blo 670310 1134013 := bbase (se 3 (by rfl) ⟨212627, by rfl⟩ : syracuseStep 1134013 = 425255) (by norm_num)
theorem B806369 : Blo 670310 806369 := bbase (se 2 (by rfl) ⟨302388, by rfl⟩ : syracuseStep 806369 = 604777) (by norm_num)
theorem B1822181 : Blo 670310 1822181 := bbase (se 4 (by rfl) ⟨170829, by rfl⟩ : syracuseStep 1822181 = 341659) (by norm_num)
theorem B1134101 : Blo 670310 1134101 := bbase (se 6 (by rfl) ⟨26580, by rfl⟩ : syracuseStep 1134101 = 53161) (by norm_num)
theorem B1134229 : Blo 670310 1134229 := bbase (se 6 (by rfl) ⟨26583, by rfl⟩ : syracuseStep 1134229 = 53167) (by norm_num)
theorem B1134317 : Blo 670310 1134317 := bbase (se 3 (by rfl) ⟨212684, by rfl⟩ : syracuseStep 1134317 = 425369) (by norm_num)
theorem B872245 : Blo 670310 872245 := bbase (se 5 (by rfl) ⟨40886, by rfl⟩ : syracuseStep 872245 = 81773) (by norm_num)
theorem B4083509 : Blo 670310 4083509 := bbase (se 5 (by rfl) ⟨191414, by rfl⟩ : syracuseStep 4083509 = 382829) (by norm_num)
theorem B4312885 : Blo 670310 4312885 := bbase (se 5 (by rfl) ⟨202166, by rfl⟩ : syracuseStep 4312885 = 404333) (by norm_num)
theorem B3231589 : Blo 670310 3231589 := bbase (se 4 (by rfl) ⟨302961, by rfl⟩ : syracuseStep 3231589 = 605923) (by norm_num)
theorem B1134445 : Blo 670310 1134445 := bbase (se 3 (by rfl) ⟨212708, by rfl⟩ : syracuseStep 1134445 = 425417) (by norm_num)
theorem B806773 : Blo 670310 806773 := bbase (se 5 (by rfl) ⟨37817, by rfl⟩ : syracuseStep 806773 = 75635) (by norm_num)
theorem B1134533 : Blo 670310 1134533 := bbase (se 4 (by rfl) ⟨106362, by rfl⟩ : syracuseStep 1134533 = 212725) (by norm_num)
theorem B1134661 : Blo 670310 1134661 := bbase (se 4 (by rfl) ⟨106374, by rfl⟩ : syracuseStep 1134661 = 212749) (by norm_num)
theorem B1134749 : Blo 670310 1134749 := bbase (se 3 (by rfl) ⟨212765, by rfl⟩ : syracuseStep 1134749 = 425531) (by norm_num)
theorem B807157 : Blo 670310 807157 := bbase (se 5 (by rfl) ⟨37835, by rfl⟩ : syracuseStep 807157 = 75671) (by norm_num)
theorem B1134877 : Blo 670310 1134877 := bbase (se 3 (by rfl) ⟨212789, by rfl⟩ : syracuseStep 1134877 = 425579) (by norm_num)
theorem B1134965 : Blo 670310 1134965 := bbase (se 5 (by rfl) ⟨53201, by rfl⟩ : syracuseStep 1134965 = 106403) (by norm_num)
theorem B3396005 : Blo 670310 3396005 := bbase (se 4 (by rfl) ⟨318375, by rfl⟩ : syracuseStep 3396005 = 636751) (by norm_num)
theorem B1364413 : Blo 670310 1364413 := bbase (se 3 (by rfl) ⟨255827, by rfl⟩ : syracuseStep 1364413 = 511655) (by norm_num)
theorem B2150869 : Blo 670310 2150869 := bbase (se 7 (by rfl) ⟨25205, by rfl⟩ : syracuseStep 2150869 = 50411) (by norm_num)
theorem B1135093 : Blo 670310 1135093 := bbase (se 5 (by rfl) ⟨53207, by rfl⟩ : syracuseStep 1135093 = 106415) (by norm_num)
theorem B7655957 : Blo 670310 7655957 := bbase (se 6 (by rfl) ⟨179436, by rfl⟩ : syracuseStep 7655957 = 358873) (by norm_num)
theorem B1135181 : Blo 670310 1135181 := bbase (se 3 (by rfl) ⟨212846, by rfl⟩ : syracuseStep 1135181 = 425693) (by norm_num)
theorem B1135309 : Blo 670310 1135309 := bbase (se 3 (by rfl) ⟨212870, by rfl⟩ : syracuseStep 1135309 = 425741) (by norm_num)
theorem B873181 : Blo 670310 873181 := bbase (se 3 (by rfl) ⟨163721, by rfl⟩ : syracuseStep 873181 = 327443) (by norm_num)
theorem B5755637 : Blo 670310 5755637 := bbase (se 5 (by rfl) ⟨269795, by rfl⟩ : syracuseStep 5755637 = 539591) (by norm_num)
theorem B1135397 : Blo 670310 1135397 := bbase (se 4 (by rfl) ⟨106443, by rfl⟩ : syracuseStep 1135397 = 212887) (by norm_num)
theorem B6476597 : Blo 670310 6476597 := bbase (se 5 (by rfl) ⟨303590, by rfl⟩ : syracuseStep 6476597 = 607181) (by norm_num)
theorem B1037125 : Blo 670310 1037125 := bbase (se 4 (by rfl) ⟨97230, by rfl⟩ : syracuseStep 1037125 = 194461) (by norm_num)
theorem B971669 : Blo 670310 971669 := bbase (se 6 (by rfl) ⟨22773, by rfl⟩ : syracuseStep 971669 = 45547) (by norm_num)
theorem B1135525 : Blo 670310 1135525 := bbase (se 4 (by rfl) ⟨106455, by rfl⟩ : syracuseStep 1135525 = 212911) (by norm_num)
theorem B1135613 : Blo 670310 1135613 := bbase (se 3 (by rfl) ⟨212927, by rfl⟩ : syracuseStep 1135613 = 425855) (by norm_num)
theorem B808013 : Blo 670310 808013 := bbase (se 3 (by rfl) ⟨151502, by rfl⟩ : syracuseStep 808013 = 303005) (by norm_num)
theorem B2872421 : Blo 670310 2872421 := bbase (se 4 (by rfl) ⟨269289, by rfl⟩ : syracuseStep 2872421 = 538579) (by norm_num)
theorem B1135741 : Blo 670310 1135741 := bbase (se 3 (by rfl) ⟨212951, by rfl⟩ : syracuseStep 1135741 = 425903) (by norm_num)
theorem B1135829 : Blo 670310 1135829 := bbase (se 7 (by rfl) ⟨13310, by rfl⟩ : syracuseStep 1135829 = 26621) (by norm_num)
theorem B2151701 : Blo 670310 2151701 := bbase (se 6 (by rfl) ⟨50430, by rfl⟩ : syracuseStep 2151701 = 100861) (by norm_num)
theorem B1135957 : Blo 670310 1135957 := bbase (se 18 (by rfl) ⟨6, by rfl⟩ : syracuseStep 1135957 = 13) (by norm_num)
theorem B808321 : Blo 670310 808321 := bbase (se 2 (by rfl) ⟨303120, by rfl⟩ : syracuseStep 808321 = 606241) (by norm_num)
theorem B1136045 : Blo 670310 1136045 := bbase (se 3 (by rfl) ⟨213008, by rfl⟩ : syracuseStep 1136045 = 426017) (by norm_num)
theorem B1136173 : Blo 670310 1136173 := bbase (se 3 (by rfl) ⟨213032, by rfl⟩ : syracuseStep 1136173 = 426065) (by norm_num)
theorem B808537 : Blo 670310 808537 := bbase (se 2 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 808537 = 606403) (by norm_num)
theorem B1136261 : Blo 670310 1136261 := bbase (se 4 (by rfl) ⟨106524, by rfl⟩ : syracuseStep 1136261 = 213049) (by norm_num)
theorem B3397301 : Blo 670310 3397301 := bbase (se 5 (by rfl) ⟨159248, by rfl⟩ : syracuseStep 3397301 = 318497) (by norm_num)
theorem B1136389 : Blo 670310 1136389 := bbase (se 4 (by rfl) ⟨106536, by rfl⟩ : syracuseStep 1136389 = 213073) (by norm_num)
theorem B1136477 : Blo 670310 1136477 := bbase (se 3 (by rfl) ⟨213089, by rfl⟩ : syracuseStep 1136477 = 426179) (by norm_num)
theorem B1005485 : Blo 670310 1005485 := bbase (se 3 (by rfl) ⟨188528, by rfl⟩ : syracuseStep 1005485 = 377057) (by norm_num)
theorem B1005509 : Blo 670310 1005509 := bbase (se 4 (by rfl) ⟨94266, by rfl⟩ : syracuseStep 1005509 = 188533) (by norm_num)
theorem B1005533 : Blo 670310 1005533 := bbase (se 3 (by rfl) ⟨188537, by rfl⟩ : syracuseStep 1005533 = 377075) (by norm_num)
theorem B1136605 : Blo 670310 1136605 := bbase (se 3 (by rfl) ⟨213113, by rfl⟩ : syracuseStep 1136605 = 426227) (by norm_num)
theorem B1005557 : Blo 670310 1005557 := bbase (se 5 (by rfl) ⟨47135, by rfl⟩ : syracuseStep 1005557 = 94271) (by norm_num)
theorem B1005581 : Blo 670310 1005581 := bbase (se 3 (by rfl) ⟨188546, by rfl⟩ : syracuseStep 1005581 = 377093) (by norm_num)
theorem B1005605 : Blo 670310 1005605 := bbase (se 4 (by rfl) ⟨94275, by rfl⟩ : syracuseStep 1005605 = 188551) (by norm_num)
theorem B1136693 : Blo 670310 1136693 := bbase (se 5 (by rfl) ⟨53282, by rfl⟩ : syracuseStep 1136693 = 106565) (by norm_num)
theorem B1005629 : Blo 670310 1005629 := bbase (se 3 (by rfl) ⟨188555, by rfl⟩ : syracuseStep 1005629 = 377111) (by norm_num)
theorem B1005653 : Blo 670310 1005653 := bbase (se 8 (by rfl) ⟨5892, by rfl⟩ : syracuseStep 1005653 = 11785) (by norm_num)
theorem B1005677 : Blo 670310 1005677 := bbase (se 3 (by rfl) ⟨188564, by rfl⟩ : syracuseStep 1005677 = 377129) (by norm_num)
theorem B1005701 : Blo 670310 1005701 := bbase (se 4 (by rfl) ⟨94284, by rfl⟩ : syracuseStep 1005701 = 188569) (by norm_num)
theorem B1005725 : Blo 670310 1005725 := bbase (se 3 (by rfl) ⟨188573, by rfl⟩ : syracuseStep 1005725 = 377147) (by norm_num)
theorem B809137 : Blo 670310 809137 := bbase (se 2 (by rfl) ⟨303426, by rfl⟩ : syracuseStep 809137 = 606853) (by norm_num)
theorem B1005749 : Blo 670310 1005749 := bbase (se 5 (by rfl) ⟨47144, by rfl⟩ : syracuseStep 1005749 = 94289) (by norm_num)
theorem B1136821 : Blo 670310 1136821 := bbase (se 5 (by rfl) ⟨53288, by rfl⟩ : syracuseStep 1136821 = 106577) (by norm_num)
theorem B1005773 : Blo 670310 1005773 := bbase (se 3 (by rfl) ⟨188582, by rfl⟩ : syracuseStep 1005773 = 377165) (by norm_num)
theorem B1005797 : Blo 670310 1005797 := bbase (se 4 (by rfl) ⟨94293, by rfl⟩ : syracuseStep 1005797 = 188587) (by norm_num)
theorem B1005821 : Blo 670310 1005821 := bbase (se 3 (by rfl) ⟨188591, by rfl⟩ : syracuseStep 1005821 = 377183) (by norm_num)
theorem B1136909 : Blo 670310 1136909 := bbase (se 3 (by rfl) ⟨213170, by rfl⟩ : syracuseStep 1136909 = 426341) (by norm_num)
theorem B1005845 : Blo 670310 1005845 := bbase (se 6 (by rfl) ⟨23574, by rfl⟩ : syracuseStep 1005845 = 47149) (by norm_num)
theorem B1005869 : Blo 670310 1005869 := bbase (se 3 (by rfl) ⟨188600, by rfl⟩ : syracuseStep 1005869 = 377201) (by norm_num)
theorem B1005893 : Blo 670310 1005893 := bbase (se 4 (by rfl) ⟨94302, by rfl⟩ : syracuseStep 1005893 = 188605) (by norm_num)
theorem B1005917 : Blo 670310 1005917 := bbase (se 3 (by rfl) ⟨188609, by rfl⟩ : syracuseStep 1005917 = 377219) (by norm_num)
theorem B1005941 : Blo 670310 1005941 := bbase (se 5 (by rfl) ⟨47153, by rfl⟩ : syracuseStep 1005941 = 94307) (by norm_num)
theorem B1005965 : Blo 670310 1005965 := bbase (se 3 (by rfl) ⟨188618, by rfl⟩ : syracuseStep 1005965 = 377237) (by norm_num)
theorem B1137037 : Blo 670310 1137037 := bbase (se 3 (by rfl) ⟨213194, by rfl⟩ : syracuseStep 1137037 = 426389) (by norm_num)
theorem B1005989 : Blo 670310 1005989 := bbase (se 4 (by rfl) ⟨94311, by rfl⟩ : syracuseStep 1005989 = 188623) (by norm_num)
theorem B1006013 : Blo 670310 1006013 := bbase (se 3 (by rfl) ⟨188627, by rfl⟩ : syracuseStep 1006013 = 377255) (by norm_num)
theorem B1006037 : Blo 670310 1006037 := bbase (se 7 (by rfl) ⟨11789, by rfl⟩ : syracuseStep 1006037 = 23579) (by norm_num)
theorem B1137125 : Blo 670310 1137125 := bbase (se 4 (by rfl) ⟨106605, by rfl⟩ : syracuseStep 1137125 = 213211) (by norm_num)
theorem B1006061 : Blo 670310 1006061 := bbase (se 3 (by rfl) ⟨188636, by rfl⟩ : syracuseStep 1006061 = 377273) (by norm_num)
theorem B1006085 : Blo 670310 1006085 := bbase (se 4 (by rfl) ⟨94320, by rfl⟩ : syracuseStep 1006085 = 188641) (by norm_num)
theorem B1432093 : Blo 670310 1432093 := bbase (se 3 (by rfl) ⟨268517, by rfl⟩ : syracuseStep 1432093 = 537035) (by norm_num)
theorem B1006109 : Blo 670310 1006109 := bbase (se 3 (by rfl) ⟨188645, by rfl⟩ : syracuseStep 1006109 = 377291) (by norm_num)
theorem B1006133 : Blo 670310 1006133 := bbase (se 5 (by rfl) ⟨47162, by rfl⟩ : syracuseStep 1006133 = 94325) (by norm_num)
theorem B1006157 : Blo 670310 1006157 := bbase (se 3 (by rfl) ⟨188654, by rfl⟩ : syracuseStep 1006157 = 377309) (by norm_num)
theorem B2546261 : Blo 670310 2546261 := bbase (se 8 (by rfl) ⟨14919, by rfl⟩ : syracuseStep 2546261 = 29839) (by norm_num)
theorem B1006181 : Blo 670310 1006181 := bbase (se 4 (by rfl) ⟨94329, by rfl⟩ : syracuseStep 1006181 = 188659) (by norm_num)
theorem B1137253 : Blo 670310 1137253 := bbase (se 4 (by rfl) ⟨106617, by rfl⟩ : syracuseStep 1137253 = 213235) (by norm_num)
theorem B1006205 : Blo 670310 1006205 := bbase (se 3 (by rfl) ⟨188663, by rfl⟩ : syracuseStep 1006205 = 377327) (by norm_num)
theorem B1006229 : Blo 670310 1006229 := bbase (se 6 (by rfl) ⟨23583, by rfl⟩ : syracuseStep 1006229 = 47167) (by norm_num)
theorem B1006253 : Blo 670310 1006253 := bbase (se 3 (by rfl) ⟨188672, by rfl⟩ : syracuseStep 1006253 = 377345) (by norm_num)
theorem B1727165 : Blo 670310 1727165 := bbase (se 3 (by rfl) ⟨323843, by rfl⟩ : syracuseStep 1727165 = 647687) (by norm_num)
theorem B1137341 : Blo 670310 1137341 := bbase (se 3 (by rfl) ⟨213251, by rfl⟩ : syracuseStep 1137341 = 426503) (by norm_num)
theorem B1006277 : Blo 670310 1006277 := bbase (se 4 (by rfl) ⟨94338, by rfl⟩ : syracuseStep 1006277 = 188677) (by norm_num)
theorem B1006301 : Blo 670310 1006301 := bbase (se 3 (by rfl) ⟨188681, by rfl⟩ : syracuseStep 1006301 = 377363) (by norm_num)
theorem B1006325 : Blo 670310 1006325 := bbase (se 5 (by rfl) ⟨47171, by rfl⟩ : syracuseStep 1006325 = 94343) (by norm_num)
theorem B1006349 : Blo 670310 1006349 := bbase (se 3 (by rfl) ⟨188690, by rfl⟩ : syracuseStep 1006349 = 377381) (by norm_num)
theorem B1006373 : Blo 670310 1006373 := bbase (se 4 (by rfl) ⟨94347, by rfl⟩ : syracuseStep 1006373 = 188695) (by norm_num)
theorem B1006397 : Blo 670310 1006397 := bbase (se 3 (by rfl) ⟨188699, by rfl⟩ : syracuseStep 1006397 = 377399) (by norm_num)
theorem B1137469 : Blo 670310 1137469 := bbase (se 3 (by rfl) ⟨213275, by rfl⟩ : syracuseStep 1137469 = 426551) (by norm_num)
theorem B1006421 : Blo 670310 1006421 := bbase (se 9 (by rfl) ⟨2948, by rfl⟩ : syracuseStep 1006421 = 5897) (by norm_num)
theorem B6216533 : Blo 670310 6216533 := bbase (se 9 (by rfl) ⟨18212, by rfl⟩ : syracuseStep 6216533 = 36425) (by norm_num)
theorem B2874197 : Blo 670310 2874197 := bbase (se 9 (by rfl) ⟨8420, by rfl⟩ : syracuseStep 2874197 = 16841) (by norm_num)
theorem B1006445 : Blo 670310 1006445 := bbase (se 3 (by rfl) ⟨188708, by rfl⟩ : syracuseStep 1006445 = 377417) (by norm_num)
theorem B2546549 : Blo 670310 2546549 := bbase (se 5 (by rfl) ⟨119369, by rfl⟩ : syracuseStep 2546549 = 238739) (by norm_num)
theorem B1006469 : Blo 670310 1006469 := bbase (se 4 (by rfl) ⟨94356, by rfl⟩ : syracuseStep 1006469 = 188713) (by norm_num)
theorem B1137557 : Blo 670310 1137557 := bbase (se 6 (by rfl) ⟨26661, by rfl⟩ : syracuseStep 1137557 = 53323) (by norm_num)
theorem B1006493 : Blo 670310 1006493 := bbase (se 3 (by rfl) ⟨188717, by rfl⟩ : syracuseStep 1006493 = 377435) (by norm_num)
theorem B1006517 : Blo 670310 1006517 := bbase (se 5 (by rfl) ⟨47180, by rfl⟩ : syracuseStep 1006517 = 94361) (by norm_num)
theorem B3398597 : Blo 670310 3398597 := bbase (se 4 (by rfl) ⟨318618, by rfl⟩ : syracuseStep 3398597 = 637237) (by norm_num)
theorem B1006541 : Blo 670310 1006541 := bbase (se 3 (by rfl) ⟨188726, by rfl⟩ : syracuseStep 1006541 = 377453) (by norm_num)
theorem B1727453 : Blo 670310 1727453 := bbase (se 3 (by rfl) ⟨323897, by rfl⟩ : syracuseStep 1727453 = 647795) (by norm_num)
theorem B1006565 : Blo 670310 1006565 := bbase (se 4 (by rfl) ⟨94365, by rfl⟩ : syracuseStep 1006565 = 188731) (by norm_num)
theorem B4676597 : Blo 670310 4676597 := bbase (se 5 (by rfl) ⟨219215, by rfl⟩ : syracuseStep 4676597 = 438431) (by norm_num)
theorem B1006589 : Blo 670310 1006589 := bbase (se 3 (by rfl) ⟨188735, by rfl⟩ : syracuseStep 1006589 = 377471) (by norm_num)
theorem B1006613 : Blo 670310 1006613 := bbase (se 6 (by rfl) ⟨23592, by rfl⟩ : syracuseStep 1006613 = 47185) (by norm_num)
theorem B1137685 : Blo 670310 1137685 := bbase (se 6 (by rfl) ⟨26664, by rfl⟩ : syracuseStep 1137685 = 53329) (by norm_num)
theorem B1006637 : Blo 670310 1006637 := bbase (se 3 (by rfl) ⟨188744, by rfl⟩ : syracuseStep 1006637 = 377489) (by norm_num)
theorem B1006661 : Blo 670310 1006661 := bbase (se 4 (by rfl) ⟨94374, by rfl⟩ : syracuseStep 1006661 = 188749) (by norm_num)
theorem B2874437 : Blo 670310 2874437 := bbase (se 4 (by rfl) ⟨269478, by rfl⟩ : syracuseStep 2874437 = 538957) (by norm_num)
theorem B1006685 : Blo 670310 1006685 := bbase (se 3 (by rfl) ⟨188753, by rfl⟩ : syracuseStep 1006685 = 377507) (by norm_num)
theorem B2153573 : Blo 670310 2153573 := bbase (se 4 (by rfl) ⟨201897, by rfl⟩ : syracuseStep 2153573 = 403795) (by norm_num)
theorem B1137773 : Blo 670310 1137773 := bbase (se 3 (by rfl) ⟨213332, by rfl⟩ : syracuseStep 1137773 = 426665) (by norm_num)
theorem B1006709 : Blo 670310 1006709 := bbase (se 5 (by rfl) ⟨47189, by rfl⟩ : syracuseStep 1006709 = 94379) (by norm_num)
theorem B1006733 : Blo 670310 1006733 := bbase (se 3 (by rfl) ⟨188762, by rfl⟩ : syracuseStep 1006733 = 377525) (by norm_num)
theorem B908437 : Blo 670310 908437 := bbase (se 6 (by rfl) ⟨21291, by rfl⟩ : syracuseStep 908437 = 42583) (by norm_num)
theorem B1006757 : Blo 670310 1006757 := bbase (se 4 (by rfl) ⟨94383, by rfl⟩ : syracuseStep 1006757 = 188767) (by norm_num)
theorem B1006781 : Blo 670310 1006781 := bbase (se 3 (by rfl) ⟨188771, by rfl⟩ : syracuseStep 1006781 = 377543) (by norm_num)
theorem B1006805 : Blo 670310 1006805 := bbase (se 7 (by rfl) ⟨11798, by rfl⟩ : syracuseStep 1006805 = 23597) (by norm_num)
theorem B1006829 : Blo 670310 1006829 := bbase (se 3 (by rfl) ⟨188780, by rfl⟩ : syracuseStep 1006829 = 377561) (by norm_num)
theorem B1006853 : Blo 670310 1006853 := bbase (se 4 (by rfl) ⟨94392, by rfl⟩ : syracuseStep 1006853 = 188785) (by norm_num)
theorem B1006877 : Blo 670310 1006877 := bbase (se 3 (by rfl) ⟨188789, by rfl⟩ : syracuseStep 1006877 = 377579) (by norm_num)
theorem B1006901 : Blo 670310 1006901 := bbase (se 5 (by rfl) ⟨47198, by rfl⟩ : syracuseStep 1006901 = 94397) (by norm_num)
theorem B1006925 : Blo 670310 1006925 := bbase (se 3 (by rfl) ⟨188798, by rfl⟩ : syracuseStep 1006925 = 377597) (by norm_num)
theorem B1006949 : Blo 670310 1006949 := bbase (se 4 (by rfl) ⟨94401, by rfl⟩ : syracuseStep 1006949 = 188803) (by norm_num)
theorem B1006973 : Blo 670310 1006973 := bbase (se 3 (by rfl) ⟨188807, by rfl⟩ : syracuseStep 1006973 = 377615) (by norm_num)
theorem B1432981 : Blo 670310 1432981 := bbase (se 6 (by rfl) ⟨33585, by rfl⟩ : syracuseStep 1432981 = 67171) (by norm_num)
theorem B1006997 : Blo 670310 1006997 := bbase (se 6 (by rfl) ⟨23601, by rfl⟩ : syracuseStep 1006997 = 47203) (by norm_num)
theorem B1007021 : Blo 670310 1007021 := bbase (se 3 (by rfl) ⟨188816, by rfl⟩ : syracuseStep 1007021 = 377633) (by norm_num)
theorem B1007045 : Blo 670310 1007045 := bbase (se 4 (by rfl) ⟨94410, by rfl⟩ : syracuseStep 1007045 = 188821) (by norm_num)
theorem B1007069 : Blo 670310 1007069 := bbase (se 3 (by rfl) ⟨188825, by rfl⟩ : syracuseStep 1007069 = 377651) (by norm_num)
theorem B1007093 : Blo 670310 1007093 := bbase (se 5 (by rfl) ⟨47207, by rfl⟩ : syracuseStep 1007093 = 94415) (by norm_num)
theorem B1007117 : Blo 670310 1007117 := bbase (se 3 (by rfl) ⟨188834, by rfl⟩ : syracuseStep 1007117 = 377669) (by norm_num)
theorem B1007141 : Blo 670310 1007141 := bbase (se 4 (by rfl) ⟨94419, by rfl⟩ : syracuseStep 1007141 = 188839) (by norm_num)
theorem B1007165 : Blo 670310 1007165 := bbase (se 3 (by rfl) ⟨188843, by rfl⟩ : syracuseStep 1007165 = 377687) (by norm_num)
theorem B1007189 : Blo 670310 1007189 := bbase (se 8 (by rfl) ⟨5901, by rfl⟩ : syracuseStep 1007189 = 11803) (by norm_num)
theorem B1007213 : Blo 670310 1007213 := bbase (se 3 (by rfl) ⟨188852, by rfl⟩ : syracuseStep 1007213 = 377705) (by norm_num)
theorem B1007237 : Blo 670310 1007237 := bbase (se 4 (by rfl) ⟨94428, by rfl⟩ : syracuseStep 1007237 = 188857) (by norm_num)
theorem B5758613 : Blo 670310 5758613 := bbase (se 6 (by rfl) ⟨134967, by rfl⟩ : syracuseStep 5758613 = 269935) (by norm_num)
theorem B1007261 : Blo 670310 1007261 := bbase (se 3 (by rfl) ⟨188861, by rfl⟩ : syracuseStep 1007261 = 377723) (by norm_num)
theorem B1007285 : Blo 670310 1007285 := bbase (se 5 (by rfl) ⟨47216, by rfl⟩ : syracuseStep 1007285 = 94433) (by norm_num)
theorem B1007309 : Blo 670310 1007309 := bbase (se 3 (by rfl) ⟨188870, by rfl⟩ : syracuseStep 1007309 = 377741) (by norm_num)
theorem B1007333 : Blo 670310 1007333 := bbase (se 4 (by rfl) ⟨94437, by rfl⟩ : syracuseStep 1007333 = 188875) (by norm_num)
theorem B1007357 : Blo 670310 1007357 := bbase (se 3 (by rfl) ⟨188879, by rfl⟩ : syracuseStep 1007357 = 377759) (by norm_num)
theorem B1007381 : Blo 670310 1007381 := bbase (se 6 (by rfl) ⟨23610, by rfl⟩ : syracuseStep 1007381 = 47221) (by norm_num)
theorem B1007405 : Blo 670310 1007405 := bbase (se 3 (by rfl) ⟨188888, by rfl⟩ : syracuseStep 1007405 = 377777) (by norm_num)
theorem B1007429 : Blo 670310 1007429 := bbase (se 4 (by rfl) ⟨94446, by rfl⟩ : syracuseStep 1007429 = 188893) (by norm_num)
theorem B1007453 : Blo 670310 1007453 := bbase (se 3 (by rfl) ⟨188897, by rfl⟩ : syracuseStep 1007453 = 377795) (by norm_num)
theorem B1007477 : Blo 670310 1007477 := bbase (se 5 (by rfl) ⟨47225, by rfl⟩ : syracuseStep 1007477 = 94451) (by norm_num)
theorem B1433477 : Blo 670310 1433477 := bbase (se 4 (by rfl) ⟨134388, by rfl⟩ : syracuseStep 1433477 = 268777) (by norm_num)
theorem B1007501 : Blo 670310 1007501 := bbase (se 3 (by rfl) ⟨188906, by rfl⟩ : syracuseStep 1007501 = 377813) (by norm_num)
theorem B1007525 : Blo 670310 1007525 := bbase (se 4 (by rfl) ⟨94455, by rfl⟩ : syracuseStep 1007525 = 188911) (by norm_num)
theorem B1007549 : Blo 670310 1007549 := bbase (se 3 (by rfl) ⟨188915, by rfl⟩ : syracuseStep 1007549 = 377831) (by norm_num)
theorem B1007573 : Blo 670310 1007573 := bbase (se 7 (by rfl) ⟨11807, by rfl⟩ : syracuseStep 1007573 = 23615) (by norm_num)
theorem B1007597 : Blo 670310 1007597 := bbase (se 3 (by rfl) ⟨188924, by rfl⟩ : syracuseStep 1007597 = 377849) (by norm_num)
theorem B1007621 : Blo 670310 1007621 := bbase (se 4 (by rfl) ⟨94464, by rfl⟩ : syracuseStep 1007621 = 188929) (by norm_num)
theorem B2547733 : Blo 670310 2547733 := bbase (se 6 (by rfl) ⟨59712, by rfl⟩ : syracuseStep 2547733 = 119425) (by norm_num)
theorem B1007645 : Blo 670310 1007645 := bbase (se 3 (by rfl) ⟨188933, by rfl⟩ : syracuseStep 1007645 = 377867) (by norm_num)
theorem B1007669 : Blo 670310 1007669 := bbase (se 5 (by rfl) ⟨47234, by rfl⟩ : syracuseStep 1007669 = 94469) (by norm_num)
theorem B1007693 : Blo 670310 1007693 := bbase (se 3 (by rfl) ⟨188942, by rfl⟩ : syracuseStep 1007693 = 377885) (by norm_num)
theorem B1007717 : Blo 670310 1007717 := bbase (se 4 (by rfl) ⟨94473, by rfl⟩ : syracuseStep 1007717 = 188947) (by norm_num)
theorem B1007741 : Blo 670310 1007741 := bbase (se 3 (by rfl) ⟨188951, by rfl⟩ : syracuseStep 1007741 = 377903) (by norm_num)
theorem B1007765 : Blo 670310 1007765 := bbase (se 6 (by rfl) ⟨23619, by rfl⟩ : syracuseStep 1007765 = 47239) (by norm_num)
theorem B1007789 : Blo 670310 1007789 := bbase (se 3 (by rfl) ⟨188960, by rfl⟩ : syracuseStep 1007789 = 377921) (by norm_num)
theorem B1007813 : Blo 670310 1007813 := bbase (se 4 (by rfl) ⟨94482, by rfl⟩ : syracuseStep 1007813 = 188965) (by norm_num)
theorem B3399893 : Blo 670310 3399893 := bbase (se 7 (by rfl) ⟨39842, by rfl⟩ : syracuseStep 3399893 = 79685) (by norm_num)
theorem B1007837 : Blo 670310 1007837 := bbase (se 3 (by rfl) ⟨188969, by rfl⟩ : syracuseStep 1007837 = 377939) (by norm_num)
theorem B1007861 : Blo 670310 1007861 := bbase (se 5 (by rfl) ⟨47243, by rfl⟩ : syracuseStep 1007861 = 94487) (by norm_num)
theorem B1007885 : Blo 670310 1007885 := bbase (se 3 (by rfl) ⟨188978, by rfl⟩ : syracuseStep 1007885 = 377957) (by norm_num)
theorem B7266581 : Blo 670310 7266581 := bbase (se 6 (by rfl) ⟨170310, by rfl⟩ : syracuseStep 7266581 = 340621) (by norm_num)
theorem B1007909 : Blo 670310 1007909 := bbase (se 4 (by rfl) ⟨94491, by rfl⟩ : syracuseStep 1007909 = 188983) (by norm_num)
theorem B6447413 : Blo 670310 6447413 := bbase (se 5 (by rfl) ⟨302222, by rfl⟩ : syracuseStep 6447413 = 604445) (by norm_num)
theorem B1007933 : Blo 670310 1007933 := bbase (se 3 (by rfl) ⟨188987, by rfl⟩ : syracuseStep 1007933 = 377975) (by norm_num)
theorem B2548037 : Blo 670310 2548037 := bbase (se 4 (by rfl) ⟨238878, by rfl⟩ : syracuseStep 2548037 = 477757) (by norm_num)
theorem B1007957 : Blo 670310 1007957 := bbase (se 10 (by rfl) ⟨1476, by rfl⟩ : syracuseStep 1007957 = 2953) (by norm_num)
theorem B680293 : Blo 670310 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B1007981 : Blo 670310 1007981 := bbase (se 3 (by rfl) ⟨188996, by rfl⟩ : syracuseStep 1007981 = 377993) (by norm_num)
theorem B1008005 : Blo 670310 1008005 := bbase (se 4 (by rfl) ⟨94500, by rfl⟩ : syracuseStep 1008005 = 189001) (by norm_num)
theorem B1008029 : Blo 670310 1008029 := bbase (se 3 (by rfl) ⟨189005, by rfl⟩ : syracuseStep 1008029 = 378011) (by norm_num)
theorem B1008053 : Blo 670310 1008053 := bbase (se 5 (by rfl) ⟨47252, by rfl⟩ : syracuseStep 1008053 = 94505) (by norm_num)
theorem B1008077 : Blo 670310 1008077 := bbase (se 3 (by rfl) ⟨189014, by rfl⟩ : syracuseStep 1008077 = 378029) (by norm_num)
theorem B1008101 : Blo 670310 1008101 := bbase (se 4 (by rfl) ⟨94509, by rfl⟩ : syracuseStep 1008101 = 189019) (by norm_num)
theorem B1008125 : Blo 670310 1008125 := bbase (se 3 (by rfl) ⟨189023, by rfl⟩ : syracuseStep 1008125 = 378047) (by norm_num)
theorem B1008149 : Blo 670310 1008149 := bbase (se 6 (by rfl) ⟨23628, by rfl⟩ : syracuseStep 1008149 = 47257) (by norm_num)
theorem B1008173 : Blo 670310 1008173 := bbase (se 3 (by rfl) ⟨189032, by rfl⟩ : syracuseStep 1008173 = 378065) (by norm_num)
theorem B1008197 : Blo 670310 1008197 := bbase (se 4 (by rfl) ⟨94518, by rfl⟩ : syracuseStep 1008197 = 189037) (by norm_num)
theorem B1008221 : Blo 670310 1008221 := bbase (se 3 (by rfl) ⟨189041, by rfl⟩ : syracuseStep 1008221 = 378083) (by norm_num)
theorem B1008245 : Blo 670310 1008245 := bbase (se 5 (by rfl) ⟨47261, by rfl⟩ : syracuseStep 1008245 = 94523) (by norm_num)
theorem B1008269 : Blo 670310 1008269 := bbase (se 3 (by rfl) ⟨189050, by rfl⟩ : syracuseStep 1008269 = 378101) (by norm_num)
theorem B1008293 : Blo 670310 1008293 := bbase (se 4 (by rfl) ⟨94527, by rfl⟩ : syracuseStep 1008293 = 189055) (by norm_num)
theorem B1008317 : Blo 670310 1008317 := bbase (se 3 (by rfl) ⟨189059, by rfl⟩ : syracuseStep 1008317 = 378119) (by norm_num)
theorem B5726933 : Blo 670310 5726933 := bbase (se 7 (by rfl) ⟨67112, by rfl⟩ : syracuseStep 5726933 = 134225) (by norm_num)
theorem B1008341 : Blo 670310 1008341 := bbase (se 7 (by rfl) ⟨11816, by rfl⟩ : syracuseStep 1008341 = 23633) (by norm_num)
theorem B1008365 : Blo 670310 1008365 := bbase (se 3 (by rfl) ⟨189068, by rfl⟩ : syracuseStep 1008365 = 378137) (by norm_num)
theorem B1434365 : Blo 670310 1434365 := bbase (se 3 (by rfl) ⟨268943, by rfl⟩ : syracuseStep 1434365 = 537887) (by norm_num)
theorem B1008389 : Blo 670310 1008389 := bbase (se 4 (by rfl) ⟨94536, by rfl⟩ : syracuseStep 1008389 = 189073) (by norm_num)
theorem B1008413 : Blo 670310 1008413 := bbase (se 3 (by rfl) ⟨189077, by rfl⟩ : syracuseStep 1008413 = 378155) (by norm_num)
theorem B1008437 : Blo 670310 1008437 := bbase (se 5 (by rfl) ⟨47270, by rfl⟩ : syracuseStep 1008437 = 94541) (by norm_num)
theorem B1008461 : Blo 670310 1008461 := bbase (se 3 (by rfl) ⟨189086, by rfl⟩ : syracuseStep 1008461 = 378173) (by norm_num)
theorem B1008485 : Blo 670310 1008485 := bbase (se 4 (by rfl) ⟨94545, by rfl⟩ : syracuseStep 1008485 = 189091) (by norm_num)
theorem B1434485 : Blo 670310 1434485 := bbase (se 5 (by rfl) ⟨67241, by rfl⟩ : syracuseStep 1434485 = 134483) (by norm_num)
theorem B1008509 : Blo 670310 1008509 := bbase (se 3 (by rfl) ⟨189095, by rfl⟩ : syracuseStep 1008509 = 378191) (by norm_num)
theorem B1008533 : Blo 670310 1008533 := bbase (se 6 (by rfl) ⟨23637, by rfl⟩ : syracuseStep 1008533 = 47275) (by norm_num)
theorem B1008557 : Blo 670310 1008557 := bbase (se 3 (by rfl) ⟨189104, by rfl⟩ : syracuseStep 1008557 = 378209) (by norm_num)
theorem B1008581 : Blo 670310 1008581 := bbase (se 4 (by rfl) ⟨94554, by rfl⟩ : syracuseStep 1008581 = 189109) (by norm_num)
theorem B1008605 : Blo 670310 1008605 := bbase (se 3 (by rfl) ⟨189113, by rfl⟩ : syracuseStep 1008605 = 378227) (by norm_num)
theorem B1008629 : Blo 670310 1008629 := bbase (se 5 (by rfl) ⟨47279, by rfl⟩ : syracuseStep 1008629 = 94559) (by norm_num)
theorem B1663997 : Blo 670310 1663997 := bbase (se 3 (by rfl) ⟨311999, by rfl⟩ : syracuseStep 1663997 = 623999) (by norm_num)
theorem B2909189 : Blo 670310 2909189 := bbase (se 4 (by rfl) ⟨272736, by rfl⟩ : syracuseStep 2909189 = 545473) (by norm_num)
theorem B1008653 : Blo 670310 1008653 := bbase (se 3 (by rfl) ⟨189122, by rfl⟩ : syracuseStep 1008653 = 378245) (by norm_num)
theorem B1008677 : Blo 670310 1008677 := bbase (se 4 (by rfl) ⟨94563, by rfl⟩ : syracuseStep 1008677 = 189127) (by norm_num)
theorem B1008701 : Blo 670310 1008701 := bbase (se 3 (by rfl) ⟨189131, by rfl⟩ : syracuseStep 1008701 = 378263) (by norm_num)
theorem B1008725 : Blo 670310 1008725 := bbase (se 8 (by rfl) ⟨5910, by rfl⟩ : syracuseStep 1008725 = 11821) (by norm_num)
theorem B1008749 : Blo 670310 1008749 := bbase (se 3 (by rfl) ⟨189140, by rfl⟩ : syracuseStep 1008749 = 378281) (by norm_num)
theorem B910453 : Blo 670310 910453 := bbase (se 5 (by rfl) ⟨42677, by rfl⟩ : syracuseStep 910453 = 85355) (by norm_num)
theorem B1008773 : Blo 670310 1008773 := bbase (se 4 (by rfl) ⟨94572, by rfl⟩ : syracuseStep 1008773 = 189145) (by norm_num)
theorem B1696909 : Blo 670310 1696909 := bbase (se 3 (by rfl) ⟨318170, by rfl⟩ : syracuseStep 1696909 = 636341) (by norm_num)
theorem B1008797 : Blo 670310 1008797 := bbase (se 3 (by rfl) ⟨189149, by rfl⟩ : syracuseStep 1008797 = 378299) (by norm_num)
theorem B1008821 : Blo 670310 1008821 := bbase (se 5 (by rfl) ⟨47288, by rfl⟩ : syracuseStep 1008821 = 94577) (by norm_num)
theorem B1008845 : Blo 670310 1008845 := bbase (se 3 (by rfl) ⟨189158, by rfl⟩ : syracuseStep 1008845 = 378317) (by norm_num)
theorem B1008869 : Blo 670310 1008869 := bbase (se 4 (by rfl) ⟨94581, by rfl⟩ : syracuseStep 1008869 = 189163) (by norm_num)
theorem B1697021 : Blo 670310 1697021 := bbase (se 3 (by rfl) ⟨318191, by rfl⟩ : syracuseStep 1697021 = 636383) (by norm_num)
theorem B1008893 : Blo 670310 1008893 := bbase (se 3 (by rfl) ⟨189167, by rfl⟩ : syracuseStep 1008893 = 378335) (by norm_num)
theorem B1008917 : Blo 670310 1008917 := bbase (se 6 (by rfl) ⟨23646, by rfl⟩ : syracuseStep 1008917 = 47293) (by norm_num)
theorem B1008941 : Blo 670310 1008941 := bbase (se 3 (by rfl) ⟨189176, by rfl⟩ : syracuseStep 1008941 = 378353) (by norm_num)
theorem B2876725 : Blo 670310 2876725 := bbase (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) (by norm_num)
theorem B1008965 : Blo 670310 1008965 := bbase (se 4 (by rfl) ⟨94590, by rfl⟩ : syracuseStep 1008965 = 189181) (by norm_num)
theorem B1008989 : Blo 670310 1008989 := bbase (se 3 (by rfl) ⟨189185, by rfl⟩ : syracuseStep 1008989 = 378371) (by norm_num)
theorem B1009013 : Blo 670310 1009013 := bbase (se 5 (by rfl) ⟨47297, by rfl⟩ : syracuseStep 1009013 = 94595) (by norm_num)
theorem B1009037 : Blo 670310 1009037 := bbase (se 3 (by rfl) ⟨189194, by rfl⟩ : syracuseStep 1009037 = 378389) (by norm_num)
theorem B1009061 : Blo 670310 1009061 := bbase (se 4 (by rfl) ⟨94599, by rfl⟩ : syracuseStep 1009061 = 189199) (by norm_num)
theorem B1697213 : Blo 670310 1697213 := bbase (se 3 (by rfl) ⟨318227, by rfl⟩ : syracuseStep 1697213 = 636455) (by norm_num)
theorem B1009085 : Blo 670310 1009085 := bbase (se 3 (by rfl) ⟨189203, by rfl⟩ : syracuseStep 1009085 = 378407) (by norm_num)
theorem B1009109 : Blo 670310 1009109 := bbase (se 7 (by rfl) ⟨11825, by rfl⟩ : syracuseStep 1009109 = 23651) (by norm_num)
theorem B3401189 : Blo 670310 3401189 := bbase (se 4 (by rfl) ⟨318861, by rfl⟩ : syracuseStep 3401189 = 637723) (by norm_num)
theorem B1435117 : Blo 670310 1435117 := bbase (se 3 (by rfl) ⟨269084, by rfl⟩ : syracuseStep 1435117 = 538169) (by norm_num)
theorem B1009133 : Blo 670310 1009133 := bbase (se 3 (by rfl) ⟨189212, by rfl⟩ : syracuseStep 1009133 = 378425) (by norm_num)
theorem B2942453 : Blo 670310 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B1009157 : Blo 670310 1009157 := bbase (se 4 (by rfl) ⟨94608, by rfl⟩ : syracuseStep 1009157 = 189217) (by norm_num)
theorem B1009181 : Blo 670310 1009181 := bbase (se 3 (by rfl) ⟨189221, by rfl⟩ : syracuseStep 1009181 = 378443) (by norm_num)
theorem B1009205 : Blo 670310 1009205 := bbase (se 5 (by rfl) ⟨47306, by rfl⟩ : syracuseStep 1009205 = 94613) (by norm_num)
theorem B1009229 : Blo 670310 1009229 := bbase (se 3 (by rfl) ⟨189230, by rfl⟩ : syracuseStep 1009229 = 378461) (by norm_num)
theorem B1009253 : Blo 670310 1009253 := bbase (se 4 (by rfl) ⟨94617, by rfl⟩ : syracuseStep 1009253 = 189235) (by norm_num)
theorem B1009277 : Blo 670310 1009277 := bbase (se 3 (by rfl) ⟨189239, by rfl⟩ : syracuseStep 1009277 = 378479) (by norm_num)
theorem B1009301 : Blo 670310 1009301 := bbase (se 6 (by rfl) ⟨23655, by rfl⟩ : syracuseStep 1009301 = 47311) (by norm_num)
theorem B1009325 : Blo 670310 1009325 := bbase (se 3 (by rfl) ⟨189248, by rfl⟩ : syracuseStep 1009325 = 378497) (by norm_num)
theorem B1009349 : Blo 670310 1009349 := bbase (se 4 (by rfl) ⟨94626, by rfl⟩ : syracuseStep 1009349 = 189253) (by norm_num)
theorem B1009373 : Blo 670310 1009373 := bbase (se 3 (by rfl) ⟨189257, by rfl⟩ : syracuseStep 1009373 = 378515) (by norm_num)
theorem B1009397 : Blo 670310 1009397 := bbase (se 5 (by rfl) ⟨47315, by rfl⟩ : syracuseStep 1009397 = 94631) (by norm_num)
theorem B1009421 : Blo 670310 1009421 := bbase (se 3 (by rfl) ⟨189266, by rfl⟩ : syracuseStep 1009421 = 378533) (by norm_num)
theorem B1697557 : Blo 670310 1697557 := bbase (se 6 (by rfl) ⟨39786, by rfl⟩ : syracuseStep 1697557 = 79573) (by norm_num)
theorem B5105429 : Blo 670310 5105429 := bbase (se 6 (by rfl) ⟨119658, by rfl⟩ : syracuseStep 5105429 = 239317) (by norm_num)
theorem B1009445 : Blo 670310 1009445 := bbase (se 4 (by rfl) ⟨94635, by rfl⟩ : syracuseStep 1009445 = 189271) (by norm_num)
theorem B2156341 : Blo 670310 2156341 := bbase (se 5 (by rfl) ⟨101078, by rfl⟩ : syracuseStep 2156341 = 202157) (by norm_num)
theorem B1009469 : Blo 670310 1009469 := bbase (se 3 (by rfl) ⟨189275, by rfl⟩ : syracuseStep 1009469 = 378551) (by norm_num)
theorem B681793 : Blo 670310 681793 := bbase (se 2 (by rfl) ⟨255672, by rfl⟩ : syracuseStep 681793 = 511345) (by norm_num)
theorem B1009493 : Blo 670310 1009493 := bbase (se 9 (by rfl) ⟨2957, by rfl⟩ : syracuseStep 1009493 = 5915) (by norm_num)
theorem B1009517 : Blo 670310 1009517 := bbase (se 3 (by rfl) ⟨189284, by rfl⟩ : syracuseStep 1009517 = 378569) (by norm_num)
theorem B3073909 : Blo 670310 3073909 := bbase (se 5 (by rfl) ⟨144089, by rfl⟩ : syracuseStep 3073909 = 288179) (by norm_num)
theorem B1697669 : Blo 670310 1697669 := bbase (se 4 (by rfl) ⟨159156, by rfl⟩ : syracuseStep 1697669 = 318313) (by norm_num)
theorem B1009541 : Blo 670310 1009541 := bbase (se 4 (by rfl) ⟨94644, by rfl⟩ : syracuseStep 1009541 = 189289) (by norm_num)
theorem B1009565 : Blo 670310 1009565 := bbase (se 3 (by rfl) ⟨189293, by rfl⟩ : syracuseStep 1009565 = 378587) (by norm_num)
theorem B1009589 : Blo 670310 1009589 := bbase (se 5 (by rfl) ⟨47324, by rfl⟩ : syracuseStep 1009589 = 94649) (by norm_num)
theorem B1075133 : Blo 670310 1075133 := bbase (se 3 (by rfl) ⟨201587, by rfl⟩ : syracuseStep 1075133 = 403175) (by norm_num)
theorem B1009613 : Blo 670310 1009613 := bbase (se 3 (by rfl) ⟨189302, by rfl⟩ : syracuseStep 1009613 = 378605) (by norm_num)
theorem B4319189 : Blo 670310 4319189 := bbase (se 7 (by rfl) ⟨50615, by rfl⟩ : syracuseStep 4319189 = 101231) (by norm_num)
theorem B1009637 : Blo 670310 1009637 := bbase (se 4 (by rfl) ⟨94653, by rfl⟩ : syracuseStep 1009637 = 189307) (by norm_num)
theorem B1009661 : Blo 670310 1009661 := bbase (se 3 (by rfl) ⟨189311, by rfl⟩ : syracuseStep 1009661 = 378623) (by norm_num)
theorem B1009685 : Blo 670310 1009685 := bbase (se 6 (by rfl) ⟨23664, by rfl⟩ : syracuseStep 1009685 = 47329) (by norm_num)
theorem B1009709 : Blo 670310 1009709 := bbase (se 3 (by rfl) ⟨189320, by rfl⟩ : syracuseStep 1009709 = 378641) (by norm_num)
theorem B1697861 : Blo 670310 1697861 := bbase (se 4 (by rfl) ⟨159174, by rfl⟩ : syracuseStep 1697861 = 318349) (by norm_num)
theorem B1009733 : Blo 670310 1009733 := bbase (se 4 (by rfl) ⟨94662, by rfl⟩ : syracuseStep 1009733 = 189325) (by norm_num)
theorem B1009757 : Blo 670310 1009757 := bbase (se 3 (by rfl) ⟨189329, by rfl⟩ : syracuseStep 1009757 = 378659) (by norm_num)
theorem B4843637 : Blo 670310 4843637 := bbase (se 5 (by rfl) ⟨227045, by rfl⟩ : syracuseStep 4843637 = 454091) (by norm_num)
theorem B1009781 : Blo 670310 1009781 := bbase (se 5 (by rfl) ⟨47333, by rfl⟩ : syracuseStep 1009781 = 94667) (by norm_num)
theorem B1009805 : Blo 670310 1009805 := bbase (se 3 (by rfl) ⟨189338, by rfl⟩ : syracuseStep 1009805 = 378677) (by norm_num)
theorem B1009829 : Blo 670310 1009829 := bbase (se 4 (by rfl) ⟨94671, by rfl⟩ : syracuseStep 1009829 = 189343) (by norm_num)
theorem B1009853 : Blo 670310 1009853 := bbase (se 3 (by rfl) ⟨189347, by rfl⟩ : syracuseStep 1009853 = 378695) (by norm_num)
theorem B1009877 : Blo 670310 1009877 := bbase (se 7 (by rfl) ⟨11834, by rfl⟩ : syracuseStep 1009877 = 23669) (by norm_num)
theorem B1009901 : Blo 670310 1009901 := bbase (se 3 (by rfl) ⟨189356, by rfl⟩ : syracuseStep 1009901 = 378713) (by norm_num)
theorem B1894661 : Blo 670310 1894661 := bbase (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) (by norm_num)
theorem B1009925 : Blo 670310 1009925 := bbase (se 4 (by rfl) ⟨94680, by rfl⟩ : syracuseStep 1009925 = 189361) (by norm_num)
theorem B1009949 : Blo 670310 1009949 := bbase (se 3 (by rfl) ⟨189365, by rfl⟩ : syracuseStep 1009949 = 378731) (by norm_num)
theorem B1009973 : Blo 670310 1009973 := bbase (se 5 (by rfl) ⟨47342, by rfl⟩ : syracuseStep 1009973 = 94685) (by norm_num)
theorem B1009997 : Blo 670310 1009997 := bbase (se 3 (by rfl) ⟨189374, by rfl⟩ : syracuseStep 1009997 = 378749) (by norm_num)
theorem B1436005 : Blo 670310 1436005 := bbase (se 4 (by rfl) ⟨134625, by rfl⟩ : syracuseStep 1436005 = 269251) (by norm_num)
theorem B1010021 : Blo 670310 1010021 := bbase (se 4 (by rfl) ⟨94689, by rfl⟩ : syracuseStep 1010021 = 189379) (by norm_num)
theorem B1010045 : Blo 670310 1010045 := bbase (se 3 (by rfl) ⟨189383, by rfl⟩ : syracuseStep 1010045 = 378767) (by norm_num)
theorem B1075589 : Blo 670310 1075589 := bbase (se 4 (by rfl) ⟨100836, by rfl⟩ : syracuseStep 1075589 = 201673) (by norm_num)
theorem B2550149 : Blo 670310 2550149 := bbase (se 4 (by rfl) ⟨239076, by rfl⟩ : syracuseStep 2550149 = 478153) (by norm_num)
theorem B1010069 : Blo 670310 1010069 := bbase (se 6 (by rfl) ⟨23673, by rfl⟩ : syracuseStep 1010069 = 47347) (by norm_num)
theorem B1698205 : Blo 670310 1698205 := bbase (se 3 (by rfl) ⟨318413, by rfl⟩ : syracuseStep 1698205 = 636827) (by norm_num)
theorem B1010093 : Blo 670310 1010093 := bbase (se 3 (by rfl) ⟨189392, by rfl⟩ : syracuseStep 1010093 = 378785) (by norm_num)
theorem B1010117 : Blo 670310 1010117 := bbase (se 4 (by rfl) ⟨94698, by rfl⟩ : syracuseStep 1010117 = 189397) (by norm_num)
theorem B1436125 : Blo 670310 1436125 := bbase (se 3 (by rfl) ⟨269273, by rfl⟩ : syracuseStep 1436125 = 538547) (by norm_num)
theorem B1010141 : Blo 670310 1010141 := bbase (se 3 (by rfl) ⟨189401, by rfl⟩ : syracuseStep 1010141 = 378803) (by norm_num)
theorem B1010165 : Blo 670310 1010165 := bbase (se 5 (by rfl) ⟨47351, by rfl⟩ : syracuseStep 1010165 = 94703) (by norm_num)
theorem B1698317 : Blo 670310 1698317 := bbase (se 3 (by rfl) ⟨318434, by rfl⟩ : syracuseStep 1698317 = 636869) (by norm_num)
theorem B1010189 : Blo 670310 1010189 := bbase (se 3 (by rfl) ⟨189410, by rfl⟩ : syracuseStep 1010189 = 378821) (by norm_num)
theorem B1010213 : Blo 670310 1010213 := bbase (se 4 (by rfl) ⟨94707, by rfl⟩ : syracuseStep 1010213 = 189415) (by norm_num)
theorem B1010237 : Blo 670310 1010237 := bbase (se 3 (by rfl) ⟨189419, by rfl⟩ : syracuseStep 1010237 = 378839) (by norm_num)
theorem B3238469 : Blo 670310 3238469 := bbase (se 4 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 3238469 = 607213) (by norm_num)
theorem B1010261 : Blo 670310 1010261 := bbase (se 8 (by rfl) ⟨5919, by rfl⟩ : syracuseStep 1010261 = 11839) (by norm_num)
theorem B1010285 : Blo 670310 1010285 := bbase (se 3 (by rfl) ⟨189428, by rfl⟩ : syracuseStep 1010285 = 378857) (by norm_num)
theorem B682625 : Blo 670310 682625 := bbase (se 2 (by rfl) ⟨255984, by rfl⟩ : syracuseStep 682625 = 511969) (by norm_num)
theorem B1010309 : Blo 670310 1010309 := bbase (se 4 (by rfl) ⟨94716, by rfl⟩ : syracuseStep 1010309 = 189433) (by norm_num)
theorem B1010333 : Blo 670310 1010333 := bbase (se 3 (by rfl) ⟨189437, by rfl⟩ : syracuseStep 1010333 = 378875) (by norm_num)
theorem B2550437 : Blo 670310 2550437 := bbase (se 4 (by rfl) ⟨239103, by rfl⟩ : syracuseStep 2550437 = 478207) (by norm_num)
theorem B1010357 : Blo 670310 1010357 := bbase (se 5 (by rfl) ⟨47360, by rfl⟩ : syracuseStep 1010357 = 94721) (by norm_num)
theorem B1698509 : Blo 670310 1698509 := bbase (se 3 (by rfl) ⟨318470, by rfl⟩ : syracuseStep 1698509 = 636941) (by norm_num)
theorem B1010381 : Blo 670310 1010381 := bbase (se 3 (by rfl) ⟨189446, by rfl⟩ : syracuseStep 1010381 = 378893) (by norm_num)
theorem B1436381 : Blo 670310 1436381 := bbase (se 3 (by rfl) ⟨269321, by rfl⟩ : syracuseStep 1436381 = 538643) (by norm_num)
theorem B1010405 : Blo 670310 1010405 := bbase (se 4 (by rfl) ⟨94725, by rfl⟩ : syracuseStep 1010405 = 189451) (by norm_num)
theorem B3402485 : Blo 670310 3402485 := bbase (se 5 (by rfl) ⟨159491, by rfl⟩ : syracuseStep 3402485 = 318983) (by norm_num)
theorem B1010429 : Blo 670310 1010429 := bbase (se 3 (by rfl) ⟨189455, by rfl⟩ : syracuseStep 1010429 = 378911) (by norm_num)
theorem B2878213 : Blo 670310 2878213 := bbase (se 4 (by rfl) ⟨269832, by rfl⟩ : syracuseStep 2878213 = 539665) (by norm_num)
theorem B1010453 : Blo 670310 1010453 := bbase (se 6 (by rfl) ⟨23682, by rfl⟩ : syracuseStep 1010453 = 47365) (by norm_num)
theorem B2878229 : Blo 670310 2878229 := bbase (se 6 (by rfl) ⟨67458, by rfl⟩ : syracuseStep 2878229 = 134917) (by norm_num)
theorem B1010477 : Blo 670310 1010477 := bbase (se 3 (by rfl) ⟨189464, by rfl⟩ : syracuseStep 1010477 = 378929) (by norm_num)
theorem B1010501 : Blo 670310 1010501 := bbase (se 4 (by rfl) ⟨94734, by rfl⟩ : syracuseStep 1010501 = 189469) (by norm_num)
theorem B2419541 : Blo 670310 2419541 := bbase (se 9 (by rfl) ⟨7088, by rfl⟩ : syracuseStep 2419541 = 14177) (by norm_num)
theorem B1010525 : Blo 670310 1010525 := bbase (se 3 (by rfl) ⟨189473, by rfl⟩ : syracuseStep 1010525 = 378947) (by norm_num)
theorem B1010549 : Blo 670310 1010549 := bbase (se 5 (by rfl) ⟨47369, by rfl⟩ : syracuseStep 1010549 = 94739) (by norm_num)
theorem B1010573 : Blo 670310 1010573 := bbase (se 3 (by rfl) ⟨189482, by rfl⟩ : syracuseStep 1010573 = 378965) (by norm_num)
theorem B1010597 : Blo 670310 1010597 := bbase (se 4 (by rfl) ⟨94743, by rfl⟩ : syracuseStep 1010597 = 189487) (by norm_num)
theorem B1010621 : Blo 670310 1010621 := bbase (se 3 (by rfl) ⟨189491, by rfl⟩ : syracuseStep 1010621 = 378983) (by norm_num)
theorem B1272773 : Blo 670310 1272773 := bbase (se 4 (by rfl) ⟨119322, by rfl⟩ : syracuseStep 1272773 = 238645) (by norm_num)
theorem B1010645 : Blo 670310 1010645 := bbase (se 7 (by rfl) ⟨11843, by rfl⟩ : syracuseStep 1010645 = 23687) (by norm_num)
theorem B1010669 : Blo 670310 1010669 := bbase (se 3 (by rfl) ⟨189500, by rfl⟩ : syracuseStep 1010669 = 379001) (by norm_num)
theorem B1010693 : Blo 670310 1010693 := bbase (se 4 (by rfl) ⟨94752, by rfl⟩ : syracuseStep 1010693 = 189505) (by norm_num)
theorem B3075077 : Blo 670310 3075077 := bbase (se 4 (by rfl) ⟨288288, by rfl⟩ : syracuseStep 3075077 = 576577) (by norm_num)
theorem B1010717 : Blo 670310 1010717 := bbase (se 3 (by rfl) ⟨189509, by rfl⟩ : syracuseStep 1010717 = 379019) (by norm_num)
theorem B1698853 : Blo 670310 1698853 := bbase (se 4 (by rfl) ⟨159267, by rfl⟩ : syracuseStep 1698853 = 318535) (by norm_num)
theorem B1010741 : Blo 670310 1010741 := bbase (se 5 (by rfl) ⟨47378, by rfl⟩ : syracuseStep 1010741 = 94757) (by norm_num)
theorem B1010765 : Blo 670310 1010765 := bbase (se 3 (by rfl) ⟨189518, by rfl⟩ : syracuseStep 1010765 = 379037) (by norm_num)
theorem B1272925 : Blo 670310 1272925 := bbase (se 3 (by rfl) ⟨238673, by rfl⟩ : syracuseStep 1272925 = 477347) (by norm_num)
theorem B1010789 : Blo 670310 1010789 := bbase (se 4 (by rfl) ⟨94761, by rfl⟩ : syracuseStep 1010789 = 189523) (by norm_num)
theorem B1010813 : Blo 670310 1010813 := bbase (se 3 (by rfl) ⟨189527, by rfl⟩ : syracuseStep 1010813 = 379055) (by norm_num)
theorem B1698965 : Blo 670310 1698965 := bbase (se 6 (by rfl) ⟨39819, by rfl⟩ : syracuseStep 1698965 = 79639) (by norm_num)
theorem B1010837 : Blo 670310 1010837 := bbase (se 6 (by rfl) ⟨23691, by rfl⟩ : syracuseStep 1010837 = 47383) (by norm_num)
theorem B1010861 : Blo 670310 1010861 := bbase (se 3 (by rfl) ⟨189536, by rfl⟩ : syracuseStep 1010861 = 379073) (by norm_num)
theorem B1010885 : Blo 670310 1010885 := bbase (se 4 (by rfl) ⟨94770, by rfl⟩ : syracuseStep 1010885 = 189541) (by norm_num)
theorem B1010909 : Blo 670310 1010909 := bbase (se 3 (by rfl) ⟨189545, by rfl⟩ : syracuseStep 1010909 = 379091) (by norm_num)
theorem B683245 : Blo 670310 683245 := bbase (se 3 (by rfl) ⟨128108, by rfl⟩ : syracuseStep 683245 = 256217) (by norm_num)
theorem B1010933 : Blo 670310 1010933 := bbase (se 5 (by rfl) ⟨47387, by rfl⟩ : syracuseStep 1010933 = 94775) (by norm_num)
theorem B3075317 : Blo 670310 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B1010957 : Blo 670310 1010957 := bbase (se 3 (by rfl) ⟨189554, by rfl⟩ : syracuseStep 1010957 = 379109) (by norm_num)
theorem B1010981 : Blo 670310 1010981 := bbase (se 4 (by rfl) ⟨94779, by rfl⟩ : syracuseStep 1010981 = 189559) (by norm_num)
theorem B716089 : Blo 670310 716089 := bbase (se 2 (by rfl) ⟨268533, by rfl⟩ : syracuseStep 716089 = 537067) (by norm_num)
theorem B1011005 : Blo 670310 1011005 := bbase (se 3 (by rfl) ⟨189563, by rfl⟩ : syracuseStep 1011005 = 379127) (by norm_num)
theorem B1699157 : Blo 670310 1699157 := bbase (se 11 (by rfl) ⟨1244, by rfl⟩ : syracuseStep 1699157 = 2489) (by norm_num)
theorem B1011029 : Blo 670310 1011029 := bbase (se 11 (by rfl) ⟨740, by rfl⟩ : syracuseStep 1011029 = 1481) (by norm_num)
theorem B1076581 : Blo 670310 1076581 := bbase (se 4 (by rfl) ⟨100929, by rfl⟩ : syracuseStep 1076581 = 201859) (by norm_num)
theorem B1011053 : Blo 670310 1011053 := bbase (se 3 (by rfl) ⟨189572, by rfl⟩ : syracuseStep 1011053 = 379145) (by norm_num)
theorem B716149 : Blo 670310 716149 := bbase (se 5 (by rfl) ⟨33569, by rfl⟩ : syracuseStep 716149 = 67139) (by norm_num)
theorem B1011077 : Blo 670310 1011077 := bbase (se 4 (by rfl) ⟨94788, by rfl⟩ : syracuseStep 1011077 = 189577) (by norm_num)
theorem B1273229 : Blo 670310 1273229 := bbase (se 3 (by rfl) ⟨238730, by rfl⟩ : syracuseStep 1273229 = 477461) (by norm_num)
theorem B1011101 : Blo 670310 1011101 := bbase (se 3 (by rfl) ⟨189581, by rfl⟩ : syracuseStep 1011101 = 379163) (by norm_num)
theorem B1011125 : Blo 670310 1011125 := bbase (se 5 (by rfl) ⟨47396, by rfl⟩ : syracuseStep 1011125 = 94793) (by norm_num)
theorem B1011149 : Blo 670310 1011149 := bbase (se 3 (by rfl) ⟨189590, by rfl⟩ : syracuseStep 1011149 = 379181) (by norm_num)
theorem B1011173 : Blo 670310 1011173 := bbase (se 4 (by rfl) ⟨94797, by rfl⟩ : syracuseStep 1011173 = 189595) (by norm_num)
theorem B1011197 : Blo 670310 1011197 := bbase (se 3 (by rfl) ⟨189599, by rfl⟩ : syracuseStep 1011197 = 379199) (by norm_num)
theorem B1011221 : Blo 670310 1011221 := bbase (se 6 (by rfl) ⟨23700, by rfl⟩ : syracuseStep 1011221 = 47401) (by norm_num)
theorem B1011245 : Blo 670310 1011245 := bbase (se 3 (by rfl) ⟨189608, by rfl⟩ : syracuseStep 1011245 = 379217) (by norm_num)
theorem B3829301 : Blo 670310 3829301 := bbase (se 5 (by rfl) ⟨179498, by rfl⟩ : syracuseStep 3829301 = 358997) (by norm_num)
theorem B1011269 : Blo 670310 1011269 := bbase (se 4 (by rfl) ⟨94806, by rfl⟩ : syracuseStep 1011269 = 189613) (by norm_num)
theorem B1437269 : Blo 670310 1437269 := bbase (se 8 (by rfl) ⟨8421, by rfl⟩ : syracuseStep 1437269 = 16843) (by norm_num)
theorem B1011293 : Blo 670310 1011293 := bbase (se 3 (by rfl) ⟨189617, by rfl⟩ : syracuseStep 1011293 = 379235) (by norm_num)
theorem B1011317 : Blo 670310 1011317 := bbase (se 5 (by rfl) ⟨47405, by rfl⟩ : syracuseStep 1011317 = 94811) (by norm_num)
theorem B1011341 : Blo 670310 1011341 := bbase (se 3 (by rfl) ⟨189626, by rfl⟩ : syracuseStep 1011341 = 379253) (by norm_num)
theorem B1011365 : Blo 670310 1011365 := bbase (se 4 (by rfl) ⟨94815, by rfl⟩ : syracuseStep 1011365 = 189631) (by norm_num)
theorem B1699501 : Blo 670310 1699501 := bbase (se 3 (by rfl) ⟨318656, by rfl⟩ : syracuseStep 1699501 = 637313) (by norm_num)
theorem B716465 : Blo 670310 716465 := bbase (se 2 (by rfl) ⟨268674, by rfl⟩ : syracuseStep 716465 = 537349) (by norm_num)
theorem B1011389 : Blo 670310 1011389 := bbase (se 3 (by rfl) ⟨189635, by rfl⟩ : syracuseStep 1011389 = 379271) (by norm_num)
theorem B1011413 : Blo 670310 1011413 := bbase (se 7 (by rfl) ⟨11852, by rfl⟩ : syracuseStep 1011413 = 23705) (by norm_num)
theorem B1011437 : Blo 670310 1011437 := bbase (se 3 (by rfl) ⟨189644, by rfl⟩ : syracuseStep 1011437 = 379289) (by norm_num)
theorem B1011461 : Blo 670310 1011461 := bbase (se 4 (by rfl) ⟨94824, by rfl⟩ : syracuseStep 1011461 = 189649) (by norm_num)
theorem B1699613 : Blo 670310 1699613 := bbase (se 3 (by rfl) ⟨318677, by rfl⟩ : syracuseStep 1699613 = 637355) (by norm_num)
theorem B2420549 : Blo 670310 2420549 := bbase (se 4 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 2420549 = 453853) (by norm_num)
theorem B2551621 : Blo 670310 2551621 := bbase (se 4 (by rfl) ⟨239214, by rfl⟩ : syracuseStep 2551621 = 478429) (by norm_num)
theorem B1437509 : Blo 670310 1437509 := bbase (se 4 (by rfl) ⟨134766, by rfl⟩ : syracuseStep 1437509 = 269533) (by norm_num)
theorem B1699805 : Blo 670310 1699805 := bbase (se 3 (by rfl) ⟨318713, by rfl⟩ : syracuseStep 1699805 = 637427) (by norm_num)
theorem B1077229 : Blo 670310 1077229 := bbase (se 3 (by rfl) ⟨201980, by rfl⟩ : syracuseStep 1077229 = 403961) (by norm_num)
theorem B3403781 : Blo 670310 3403781 := bbase (se 4 (by rfl) ⟨319104, by rfl⟩ : syracuseStep 3403781 = 638209) (by norm_num)
theorem B716909 : Blo 670310 716909 := bbase (se 3 (by rfl) ⟨134420, by rfl⟩ : syracuseStep 716909 = 268841) (by norm_num)
theorem B2551925 : Blo 670310 2551925 := bbase (se 5 (by rfl) ⟨119621, by rfl⟩ : syracuseStep 2551925 = 239243) (by norm_num)
theorem B1273981 : Blo 670310 1273981 := bbase (se 3 (by rfl) ⟨238871, by rfl⟩ : syracuseStep 1273981 = 477743) (by norm_num)
theorem B716969 : Blo 670310 716969 := bbase (se 2 (by rfl) ⟨268863, by rfl⟩ : syracuseStep 716969 = 537727) (by norm_num)
theorem B1274125 : Blo 670310 1274125 := bbase (se 3 (by rfl) ⟨238898, by rfl⟩ : syracuseStep 1274125 = 477797) (by norm_num)
theorem B717097 : Blo 670310 717097 := bbase (se 2 (by rfl) ⟨268911, by rfl⟩ : syracuseStep 717097 = 537823) (by norm_num)
theorem B1700149 : Blo 670310 1700149 := bbase (se 5 (by rfl) ⟨79694, by rfl⟩ : syracuseStep 1700149 = 159389) (by norm_num)
theorem B1438013 : Blo 670310 1438013 := bbase (se 3 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 1438013 = 539255) (by norm_num)
theorem B1438021 : Blo 670310 1438021 := bbase (se 4 (by rfl) ⟨134814, by rfl⟩ : syracuseStep 1438021 = 269629) (by norm_num)
theorem B1700261 : Blo 670310 1700261 := bbase (se 4 (by rfl) ⟨159399, by rfl⟩ : syracuseStep 1700261 = 318799) (by norm_num)
theorem B1274285 : Blo 670310 1274285 := bbase (se 3 (by rfl) ⟨238928, by rfl⟩ : syracuseStep 1274285 = 477857) (by norm_num)
theorem B848389 : Blo 670310 848389 := bbase (se 4 (by rfl) ⟨79536, by rfl⟩ : syracuseStep 848389 = 159073) (by norm_num)
theorem B1274429 : Blo 670310 1274429 := bbase (se 3 (by rfl) ⟨238955, by rfl⟩ : syracuseStep 1274429 = 477911) (by norm_num)
theorem B848485 : Blo 670310 848485 := bbase (se 4 (by rfl) ⟨79545, by rfl⟩ : syracuseStep 848485 = 159091) (by norm_num)
theorem B1700453 : Blo 670310 1700453 := bbase (se 4 (by rfl) ⟨159417, by rfl⟩ : syracuseStep 1700453 = 318835) (by norm_num)
theorem B2159237 : Blo 670310 2159237 := bbase (se 4 (by rfl) ⟨202428, by rfl⟩ : syracuseStep 2159237 = 404857) (by norm_num)
theorem B5436085 : Blo 670310 5436085 := bbase (se 5 (by rfl) ⟨254816, by rfl⟩ : syracuseStep 5436085 = 509633) (by norm_num)
theorem B2585317 : Blo 670310 2585317 := bbase (se 4 (by rfl) ⟨242373, by rfl⟩ : syracuseStep 2585317 = 484747) (by norm_num)
theorem B717541 : Blo 670310 717541 := bbase (se 4 (by rfl) ⟨67269, by rfl⟩ : syracuseStep 717541 = 134539) (by norm_num)
theorem B848657 : Blo 670310 848657 := bbase (se 2 (by rfl) ⟨318246, by rfl⟩ : syracuseStep 848657 = 636493) (by norm_num)
theorem B848713 : Blo 670310 848713 := bbase (se 2 (by rfl) ⟨318267, by rfl⟩ : syracuseStep 848713 = 636535) (by norm_num)
theorem B1274717 : Blo 670310 1274717 := bbase (se 3 (by rfl) ⟨239009, by rfl⟩ : syracuseStep 1274717 = 478019) (by norm_num)
theorem B717661 : Blo 670310 717661 := bbase (se 3 (by rfl) ⟨134561, by rfl⟩ : syracuseStep 717661 = 269123) (by norm_num)
theorem B1078157 : Blo 670310 1078157 := bbase (se 3 (by rfl) ⟨202154, by rfl⟩ : syracuseStep 1078157 = 404309) (by norm_num)
theorem B848809 : Blo 670310 848809 := bbase (se 2 (by rfl) ⟨318303, by rfl⟩ : syracuseStep 848809 = 636607) (by norm_num)
theorem B1700797 : Blo 670310 1700797 := bbase (se 3 (by rfl) ⟨318899, by rfl⟩ : syracuseStep 1700797 = 637799) (by norm_num)
theorem B1274869 : Blo 670310 1274869 := bbase (se 5 (by rfl) ⟨59759, by rfl⟩ : syracuseStep 1274869 = 119519) (by norm_num)
theorem B1700909 : Blo 670310 1700909 := bbase (se 3 (by rfl) ⟨318920, by rfl⟩ : syracuseStep 1700909 = 637841) (by norm_num)
theorem B848981 : Blo 670310 848981 := bbase (se 8 (by rfl) ⟨4974, by rfl⟩ : syracuseStep 848981 = 9949) (by norm_num)
theorem B717913 : Blo 670310 717913 := bbase (se 2 (by rfl) ⟨269217, by rfl⟩ : syracuseStep 717913 = 538435) (by norm_num)
theorem B717917 : Blo 670310 717917 := bbase (se 3 (by rfl) ⟨134609, by rfl⟩ : syracuseStep 717917 = 269219) (by norm_num)
theorem B849037 : Blo 670310 849037 := bbase (se 3 (by rfl) ⟨159194, by rfl⟩ : syracuseStep 849037 = 318389) (by norm_num)
theorem B849133 : Blo 670310 849133 := bbase (se 3 (by rfl) ⟨159212, by rfl⟩ : syracuseStep 849133 = 318425) (by norm_num)
theorem B1701101 : Blo 670310 1701101 := bbase (se 3 (by rfl) ⟨318956, by rfl⟩ : syracuseStep 1701101 = 637913) (by norm_num)
theorem B4846837 : Blo 670310 4846837 := bbase (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) (by norm_num)
theorem B3405077 : Blo 670310 3405077 := bbase (se 6 (by rfl) ⟨79806, by rfl⟩ : syracuseStep 3405077 = 159613) (by norm_num)
theorem B1275173 : Blo 670310 1275173 := bbase (se 4 (by rfl) ⟨119547, by rfl⟩ : syracuseStep 1275173 = 239095) (by norm_num)
theorem B12285269 : Blo 670310 12285269 := bbase (se 13 (by rfl) ⟨2249, by rfl⟩ : syracuseStep 12285269 = 4499) (by norm_num)
theorem B1078613 : Blo 670310 1078613 := bbase (se 13 (by rfl) ⟨197, by rfl⟩ : syracuseStep 1078613 = 395) (by norm_num)
theorem B849305 : Blo 670310 849305 := bbase (se 2 (by rfl) ⟨318489, by rfl⟩ : syracuseStep 849305 = 636979) (by norm_num)
theorem B1439149 : Blo 670310 1439149 := bbase (se 3 (by rfl) ⟨269840, by rfl⟩ : syracuseStep 1439149 = 539681) (by norm_num)
theorem B849361 : Blo 670310 849361 := bbase (se 2 (by rfl) ⟨318510, by rfl⟩ : syracuseStep 849361 = 637021) (by norm_num)
theorem B849457 : Blo 670310 849457 := bbase (se 2 (by rfl) ⟨318546, by rfl⟩ : syracuseStep 849457 = 637093) (by norm_num)
theorem B1701445 : Blo 670310 1701445 := bbase (se 4 (by rfl) ⟨159510, by rfl⟩ : syracuseStep 1701445 = 319021) (by norm_num)
theorem B718481 : Blo 670310 718481 := bbase (se 2 (by rfl) ⟨269430, by rfl⟩ : syracuseStep 718481 = 538861) (by norm_num)
theorem B1701557 : Blo 670310 1701557 := bbase (se 5 (by rfl) ⟨79760, by rfl⟩ : syracuseStep 1701557 = 159521) (by norm_num)
theorem B849629 : Blo 670310 849629 := bbase (se 3 (by rfl) ⟨159305, by rfl⟩ : syracuseStep 849629 = 318611) (by norm_num)
theorem B849685 : Blo 670310 849685 := bbase (se 6 (by rfl) ⟨19914, by rfl⟩ : syracuseStep 849685 = 39829) (by norm_num)
theorem B1439525 : Blo 670310 1439525 := bbase (se 4 (by rfl) ⟨134955, by rfl⟩ : syracuseStep 1439525 = 269911) (by norm_num)
theorem B718669 : Blo 670310 718669 := bbase (se 3 (by rfl) ⟨134750, by rfl⟩ : syracuseStep 718669 = 269501) (by norm_num)
theorem B849781 : Blo 670310 849781 := bbase (se 5 (by rfl) ⟨39833, by rfl⟩ : syracuseStep 849781 = 79667) (by norm_num)
theorem B1701749 : Blo 670310 1701749 := bbase (se 5 (by rfl) ⟨79769, by rfl⟩ : syracuseStep 1701749 = 159539) (by norm_num)
theorem B1275925 : Blo 670310 1275925 := bbase (se 6 (by rfl) ⟨29904, by rfl⟩ : syracuseStep 1275925 = 59809) (by norm_num)
theorem B849953 : Blo 670310 849953 := bbase (se 2 (by rfl) ⟨318732, by rfl⟩ : syracuseStep 849953 = 637465) (by norm_num)
theorem B850009 : Blo 670310 850009 := bbase (se 2 (by rfl) ⟨318753, by rfl⟩ : syracuseStep 850009 = 637507) (by norm_num)
theorem B1210477 : Blo 670310 1210477 := bbase (se 3 (by rfl) ⟨226964, by rfl⟩ : syracuseStep 1210477 = 453929) (by norm_num)
theorem B1276069 : Blo 670310 1276069 := bbase (se 4 (by rfl) ⟨119631, by rfl⟩ : syracuseStep 1276069 = 239263) (by norm_num)
theorem B2554037 : Blo 670310 2554037 := bbase (se 5 (by rfl) ⟨119720, by rfl⟩ : syracuseStep 2554037 = 239441) (by norm_num)
theorem B850105 : Blo 670310 850105 := bbase (se 2 (by rfl) ⟨318789, by rfl⟩ : syracuseStep 850105 = 637579) (by norm_num)
theorem B1702093 : Blo 670310 1702093 := bbase (se 3 (by rfl) ⟨319142, by rfl⟩ : syracuseStep 1702093 = 638285) (by norm_num)
theorem B2423029 : Blo 670310 2423029 := bbase (se 5 (by rfl) ⟨113579, by rfl⟩ : syracuseStep 2423029 = 227159) (by norm_num)
theorem B1210621 : Blo 670310 1210621 := bbase (se 3 (by rfl) ⟨226991, by rfl⟩ : syracuseStep 1210621 = 453983) (by norm_num)
theorem B1702205 : Blo 670310 1702205 := bbase (se 3 (by rfl) ⟨319163, by rfl⟩ : syracuseStep 1702205 = 638327) (by norm_num)
theorem B1210693 : Blo 670310 1210693 := bbase (se 4 (by rfl) ⟨113502, by rfl⟩ : syracuseStep 1210693 = 227005) (by norm_num)
theorem B1276229 : Blo 670310 1276229 := bbase (se 4 (by rfl) ⟨119646, by rfl⟩ : syracuseStep 1276229 = 239293) (by norm_num)
theorem B850277 : Blo 670310 850277 := bbase (se 4 (by rfl) ⟨79713, by rfl⟩ : syracuseStep 850277 = 159427) (by norm_num)
theorem B2423189 : Blo 670310 2423189 := bbase (se 6 (by rfl) ⟨56793, by rfl⟩ : syracuseStep 2423189 = 113587) (by norm_num)
theorem B850333 : Blo 670310 850333 := bbase (se 3 (by rfl) ⟨159437, by rfl⟩ : syracuseStep 850333 = 318875) (by norm_num)
theorem B1276373 : Blo 670310 1276373 := bbase (se 7 (by rfl) ⟨14957, by rfl⟩ : syracuseStep 1276373 = 29915) (by norm_num)
theorem B2554325 : Blo 670310 2554325 := bbase (se 7 (by rfl) ⟨29933, by rfl⟩ : syracuseStep 2554325 = 59867) (by norm_num)
theorem B850429 : Blo 670310 850429 := bbase (se 3 (by rfl) ⟨159455, by rfl⟩ : syracuseStep 850429 = 318911) (by norm_num)
theorem B1702397 : Blo 670310 1702397 := bbase (se 3 (by rfl) ⟨319199, by rfl⟩ : syracuseStep 1702397 = 638399) (by norm_num)
theorem B3406373 : Blo 670310 3406373 := bbase (se 4 (by rfl) ⟨319347, by rfl⟩ : syracuseStep 3406373 = 638695) (by norm_num)
theorem B9697877 : Blo 670310 9697877 := bbase (se 8 (by rfl) ⟨56823, by rfl⟩ : syracuseStep 9697877 = 113647) (by norm_num)
theorem B719489 : Blo 670310 719489 := bbase (se 2 (by rfl) ⟨269808, by rfl⟩ : syracuseStep 719489 = 539617) (by norm_num)
theorem B850601 : Blo 670310 850601 := bbase (se 2 (by rfl) ⟨318975, by rfl⟩ : syracuseStep 850601 = 637951) (by norm_num)
theorem B1080029 : Blo 670310 1080029 := bbase (se 3 (by rfl) ⟨202505, by rfl⟩ : syracuseStep 1080029 = 405011) (by norm_num)
theorem B850657 : Blo 670310 850657 := bbase (se 2 (by rfl) ⟨318996, by rfl⟩ : syracuseStep 850657 = 637993) (by norm_num)
theorem B1276661 : Blo 670310 1276661 := bbase (se 5 (by rfl) ⟨59843, by rfl⟩ : syracuseStep 1276661 = 119687) (by norm_num)
theorem B850753 : Blo 670310 850753 := bbase (se 2 (by rfl) ⟨319032, by rfl⟩ : syracuseStep 850753 = 638065) (by norm_num)
theorem B1702741 : Blo 670310 1702741 := bbase (se 9 (by rfl) ⟨4988, by rfl⟩ : syracuseStep 1702741 = 9977) (by norm_num)
theorem B1276813 : Blo 670310 1276813 := bbase (se 3 (by rfl) ⟨239402, by rfl⟩ : syracuseStep 1276813 = 478805) (by norm_num)
theorem B1702853 : Blo 670310 1702853 := bbase (se 4 (by rfl) ⟨159642, by rfl⟩ : syracuseStep 1702853 = 319285) (by norm_num)
theorem B850925 : Blo 670310 850925 := bbase (se 3 (by rfl) ⟨159548, by rfl⟩ : syracuseStep 850925 = 319097) (by norm_num)
theorem B850981 : Blo 670310 850981 := bbase (se 4 (by rfl) ⟨79779, by rfl⟩ : syracuseStep 850981 = 159559) (by norm_num)
theorem B719933 : Blo 670310 719933 := bbase (se 3 (by rfl) ⟨134987, by rfl⟩ : syracuseStep 719933 = 269975) (by norm_num)
theorem B851077 : Blo 670310 851077 := bbase (se 4 (by rfl) ⟨79788, by rfl⟩ : syracuseStep 851077 = 159577) (by norm_num)
theorem B1703045 : Blo 670310 1703045 := bbase (se 4 (by rfl) ⟨159660, by rfl⟩ : syracuseStep 1703045 = 319321) (by norm_num)
theorem B1277117 : Blo 670310 1277117 := bbase (se 3 (by rfl) ⟨239459, by rfl⟩ : syracuseStep 1277117 = 478919) (by norm_num)
theorem B2718965 : Blo 670310 2718965 := bbase (se 5 (by rfl) ⟨127451, by rfl⟩ : syracuseStep 2718965 = 254903) (by norm_num)
theorem B851249 : Blo 670310 851249 := bbase (se 2 (by rfl) ⟨319218, by rfl⟩ : syracuseStep 851249 = 638437) (by norm_num)
theorem B851305 : Blo 670310 851305 := bbase (se 2 (by rfl) ⟨319239, by rfl⟩ : syracuseStep 851305 = 638479) (by norm_num)
theorem B851401 : Blo 670310 851401 := bbase (se 2 (by rfl) ⟨319275, by rfl⟩ : syracuseStep 851401 = 638551) (by norm_num)
theorem B1703389 : Blo 670310 1703389 := bbase (se 3 (by rfl) ⟨319385, by rfl⟩ : syracuseStep 1703389 = 638771) (by norm_num)
theorem B1703501 : Blo 670310 1703501 := bbase (se 3 (by rfl) ⟨319406, by rfl⟩ : syracuseStep 1703501 = 638813) (by norm_num)
theorem B1212005 : Blo 670310 1212005 := bbase (se 4 (by rfl) ⟨113625, by rfl⟩ : syracuseStep 1212005 = 227251) (by norm_num)
theorem B851573 : Blo 670310 851573 := bbase (se 5 (by rfl) ⟨39917, by rfl⟩ : syracuseStep 851573 = 79835) (by norm_num)
theorem B2555509 : Blo 670310 2555509 := bbase (se 5 (by rfl) ⟨119789, by rfl⟩ : syracuseStep 2555509 = 239579) (by norm_num)
theorem B851629 : Blo 670310 851629 := bbase (se 3 (by rfl) ⟨159680, by rfl⟩ : syracuseStep 851629 = 319361) (by norm_num)
theorem B2457317 : Blo 670310 2457317 := bbase (se 4 (by rfl) ⟨230373, by rfl⟩ : syracuseStep 2457317 = 460747) (by norm_num)
theorem B851725 : Blo 670310 851725 := bbase (se 3 (by rfl) ⟨159698, by rfl⟩ : syracuseStep 851725 = 319397) (by norm_num)
theorem B1703693 : Blo 670310 1703693 := bbase (se 3 (by rfl) ⟨319442, by rfl⟩ : syracuseStep 1703693 = 638885) (by norm_num)
theorem B3407669 : Blo 670310 3407669 := bbase (se 5 (by rfl) ⟨159734, by rfl⟩ : syracuseStep 3407669 = 319469) (by norm_num)
theorem B1212293 : Blo 670310 1212293 := bbase (se 4 (by rfl) ⟨113652, by rfl⟩ : syracuseStep 1212293 = 227305) (by norm_num)
theorem B1310629 : Blo 670310 1310629 := bbase (se 4 (by rfl) ⟨122871, by rfl⟩ : syracuseStep 1310629 = 245743) (by norm_num)
theorem B2555813 : Blo 670310 2555813 := bbase (se 4 (by rfl) ⟨239607, by rfl⟩ : syracuseStep 2555813 = 479215) (by norm_num)
theorem B1277869 : Blo 670310 1277869 := bbase (se 3 (by rfl) ⟨239600, by rfl⟩ : syracuseStep 1277869 = 479201) (by norm_num)
theorem B4358069 : Blo 670310 4358069 := bbase (se 5 (by rfl) ⟨204284, by rfl⟩ : syracuseStep 4358069 = 408569) (by norm_num)
theorem B851897 : Blo 670310 851897 := bbase (se 2 (by rfl) ⟨319461, by rfl⟩ : syracuseStep 851897 = 638923) (by norm_num)
theorem B851953 : Blo 670310 851953 := bbase (se 2 (by rfl) ⟨319482, by rfl⟩ : syracuseStep 851953 = 638965) (by norm_num)
theorem B2555981 : Blo 670310 2555981 := bstep (se 3 (by rfl) ⟨479246, by rfl⟩ : syracuseStep 2555981 = 958493) B958493
theorem B1704017 : Blo 670310 1704017 := bstep (se 2 (by rfl) ⟨639006, by rfl⟩ : syracuseStep 1704017 = 1278013) B1278013
theorem B852115 : Blo 670310 852115 := bstep (se 1 (by rfl) ⟨639086, by rfl⟩ : syracuseStep 852115 = 1278173) B1278173
theorem B2719907 : Blo 670310 2719907 := bstep (se 1 (by rfl) ⟨2039930, by rfl⟩ : syracuseStep 2719907 = 4079861) B4079861
theorem B852211 : Blo 670310 852211 := bstep (se 1 (by rfl) ⟨639158, by rfl⟩ : syracuseStep 852211 = 1278317) B1278317
theorem B2425265 : Blo 670310 2425265 := bstep (se 2 (by rfl) ⟨909474, by rfl⟩ : syracuseStep 2425265 = 1818949) B1818949
theorem B754195 : Blo 670310 754195 := bstep (se 1 (by rfl) ⟨565646, by rfl⟩ : syracuseStep 754195 = 1131293) B1131293
theorem B1278499 : Blo 670310 1278499 := bstep (se 1 (by rfl) ⟨958874, by rfl⟩ : syracuseStep 1278499 = 1917749) B1917749
theorem B1147475 : Blo 670310 1147475 := bstep (se 1 (by rfl) ⟨860606, by rfl⟩ : syracuseStep 1147475 = 1721213) B1721213
theorem B754339 : Blo 670310 754339 := bstep (se 1 (by rfl) ⟨565754, by rfl⟩ : syracuseStep 754339 = 1131509) B1131509
theorem B1278659 : Blo 670310 1278659 := bstep (se 1 (by rfl) ⟨958994, by rfl⟩ : syracuseStep 1278659 = 1917989) B1917989
theorem B852707 : Blo 670310 852707 := bstep (se 1 (by rfl) ⟨639530, by rfl⟩ : syracuseStep 852707 = 1279061) B1279061
theorem B1868579 : Blo 670310 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B754483 : Blo 670310 754483 := bstep (se 1 (by rfl) ⟨565862, by rfl⟩ : syracuseStep 754483 = 1131725) B1131725
theorem B3834701 : Blo 670310 3834701 := bstep (se 3 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 3834701 = 1438013) B1438013
theorem B2556785 : Blo 670310 2556785 := bstep (se 2 (by rfl) ⟨958794, by rfl⟩ : syracuseStep 2556785 = 1917589) B1917589
theorem B3408803 : Blo 670310 3408803 := bstep (se 1 (by rfl) ⟨2556602, by rfl⟩ : syracuseStep 3408803 = 5113205) B5113205
theorem B1508273 : Blo 670310 1508273 := bstep (se 2 (by rfl) ⟨565602, by rfl⟩ : syracuseStep 1508273 = 1131205) B1131205
theorem B1508291 : Blo 670310 1508291 := bstep (se 1 (by rfl) ⟨1131218, by rfl⟩ : syracuseStep 1508291 = 2262437) B2262437
theorem B754627 : Blo 670310 754627 := bstep (se 1 (by rfl) ⟨565970, by rfl⟩ : syracuseStep 754627 = 1131941) B1131941
theorem B1705009 : Blo 670310 1705009 := bstep (se 2 (by rfl) ⟨639378, by rfl⟩ : syracuseStep 1705009 = 1278757) B1278757
theorem B37815349 : Blo 670310 37815349 := bstep (se 5 (by rfl) ⟨1772594, by rfl⟩ : syracuseStep 37815349 = 3545189) B3545189
theorem B754771 : Blo 670310 754771 := bstep (se 1 (by rfl) ⟨566078, by rfl⟩ : syracuseStep 754771 = 1132157) B1132157
theorem B2720945 : Blo 670310 2720945 := bstep (se 2 (by rfl) ⟨1020354, by rfl⟩ : syracuseStep 2720945 = 2040709) B2040709
theorem B1508561 : Blo 670310 1508561 := bstep (se 2 (by rfl) ⟨565710, by rfl⟩ : syracuseStep 1508561 = 1131421) B1131421
theorem B1508579 : Blo 670310 1508579 := bstep (se 1 (by rfl) ⟨1131434, by rfl⟩ : syracuseStep 1508579 = 2262869) B2262869
theorem B754915 : Blo 670310 754915 := bstep (se 1 (by rfl) ⟨566186, by rfl⟩ : syracuseStep 754915 = 1132373) B1132373
theorem B1705283 : Blo 670310 1705283 := bstep (se 1 (by rfl) ⟨1278962, by rfl⟩ : syracuseStep 1705283 = 2557925) B2557925
theorem B755059 : Blo 670310 755059 := bstep (se 1 (by rfl) ⟨566294, by rfl⟩ : syracuseStep 755059 = 1132589) B1132589
theorem B853411 : Blo 670310 853411 := bstep (se 1 (by rfl) ⟨640058, by rfl⟩ : syracuseStep 853411 = 1280117) B1280117
theorem B1508849 : Blo 670310 1508849 := bstep (se 2 (by rfl) ⟨565818, by rfl⟩ : syracuseStep 1508849 = 1131637) B1131637
theorem B1213937 : Blo 670310 1213937 := bstep (se 2 (by rfl) ⟨455226, by rfl⟩ : syracuseStep 1213937 = 910453) B910453
theorem B1508867 : Blo 670310 1508867 := bstep (se 1 (by rfl) ⟨1131650, by rfl⟩ : syracuseStep 1508867 = 2263301) B2263301
theorem B755203 : Blo 670310 755203 := bstep (se 1 (by rfl) ⟨566402, by rfl⟩ : syracuseStep 755203 = 1132805) B1132805
theorem B1705475 : Blo 670310 1705475 := bstep (se 1 (by rfl) ⟨1279106, by rfl⟩ : syracuseStep 1705475 = 2558213) B2558213
theorem B2557453 : Blo 670310 2557453 := bstep (se 3 (by rfl) ⟨479522, by rfl⟩ : syracuseStep 2557453 = 959045) B959045
theorem B2262545 : Blo 670310 2262545 := bstep (se 2 (by rfl) ⟨848454, by rfl⟩ : syracuseStep 2262545 = 1696909) B1696909
theorem B1836611 : Blo 670310 1836611 := bstep (se 1 (by rfl) ⟨1377458, by rfl⟩ : syracuseStep 1836611 = 2754917) B2754917
theorem B1312355 : Blo 670310 1312355 := bstep (se 1 (by rfl) ⟨984266, by rfl⟩ : syracuseStep 1312355 = 1968533) B1968533
theorem B1640081 : Blo 670310 1640081 := bstep (se 2 (by rfl) ⟨615030, by rfl⟩ : syracuseStep 1640081 = 1230061) B1230061
theorem B755347 : Blo 670310 755347 := bstep (se 1 (by rfl) ⟨566510, by rfl⟩ : syracuseStep 755347 = 1133021) B1133021
theorem B2426545 : Blo 670310 2426545 := bstep (se 2 (by rfl) ⟨909954, by rfl⟩ : syracuseStep 2426545 = 1819909) B1819909
theorem B3409613 : Blo 670310 3409613 := bstep (se 3 (by rfl) ⟨639302, by rfl⟩ : syracuseStep 3409613 = 1278605) B1278605
theorem B3835633 : Blo 670310 3835633 := bstep (se 2 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 3835633 = 2876725) B2876725
theorem B1279729 : Blo 670310 1279729 := bstep (se 2 (by rfl) ⟨479898, by rfl⟩ : syracuseStep 1279729 = 959797) B959797
theorem B1509137 : Blo 670310 1509137 := bstep (se 2 (by rfl) ⟨565926, by rfl⟩ : syracuseStep 1509137 = 1131853) B1131853
theorem B1509155 : Blo 670310 1509155 := bstep (se 1 (by rfl) ⟨1131866, by rfl⟩ : syracuseStep 1509155 = 2263733) B2263733
theorem B755491 : Blo 670310 755491 := bstep (se 1 (by rfl) ⟨566618, by rfl⟩ : syracuseStep 755491 = 1133237) B1133237
theorem B4097891 : Blo 670310 4097891 := bstep (se 1 (by rfl) ⟨3073418, by rfl⟩ : syracuseStep 4097891 = 6146837) B6146837
theorem B1869731 : Blo 670310 1869731 := bstep (se 1 (by rfl) ⟨1402298, by rfl⟩ : syracuseStep 1869731 = 2804597) B2804597
theorem B755635 : Blo 670310 755635 := bstep (se 1 (by rfl) ⟨566726, by rfl⟩ : syracuseStep 755635 = 1133453) B1133453
theorem B2263085 : Blo 670310 2263085 := bstep (se 3 (by rfl) ⟨424328, by rfl⟩ : syracuseStep 2263085 = 848657) B848657
theorem B1509425 : Blo 670310 1509425 := bstep (se 2 (by rfl) ⟨566034, by rfl⟩ : syracuseStep 1509425 = 1132069) B1132069
theorem B1509443 : Blo 670310 1509443 := bstep (se 1 (by rfl) ⟨1132082, by rfl⟩ : syracuseStep 1509443 = 2264165) B2264165
theorem B755779 : Blo 670310 755779 := bstep (se 1 (by rfl) ⟨566834, by rfl⟩ : syracuseStep 755779 = 1133669) B1133669
theorem B2263139 : Blo 670310 2263139 := bstep (se 1 (by rfl) ⟨1697354, by rfl⟩ : syracuseStep 2263139 = 3394709) B3394709
theorem B755923 : Blo 670310 755923 := bstep (se 1 (by rfl) ⟨566942, by rfl⟩ : syracuseStep 755923 = 1133885) B1133885
theorem B2558243 : Blo 670310 2558243 := bstep (se 1 (by rfl) ⟨1918682, by rfl⟩ : syracuseStep 2558243 = 3837365) B3837365
theorem B1509713 : Blo 670310 1509713 := bstep (se 2 (by rfl) ⟨566142, by rfl⟩ : syracuseStep 1509713 = 1132285) B1132285
theorem B1509731 : Blo 670310 1509731 := bstep (se 1 (by rfl) ⟨1132298, by rfl⟩ : syracuseStep 1509731 = 2264597) B2264597
theorem B756067 : Blo 670310 756067 := bstep (se 1 (by rfl) ⟨567050, by rfl⟩ : syracuseStep 756067 = 1134101) B1134101
theorem B2263409 : Blo 670310 2263409 := bstep (se 2 (by rfl) ⟨848778, by rfl⟩ : syracuseStep 2263409 = 1697557) B1697557
theorem B1378691 : Blo 670310 1378691 := bstep (se 1 (by rfl) ⟨1034018, by rfl⟩ : syracuseStep 1378691 = 2068037) B2068037
theorem B1575299 : Blo 670310 1575299 := bstep (se 1 (by rfl) ⟨1181474, by rfl⟩ : syracuseStep 1575299 = 2362949) B2362949
theorem B2591117 : Blo 670310 2591117 := bstep (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) B971669
theorem B1706417 : Blo 670310 1706417 := bstep (se 2 (by rfl) ⟨639906, by rfl⟩ : syracuseStep 1706417 = 1279813) B1279813
theorem B1706467 : Blo 670310 1706467 := bstep (se 1 (by rfl) ⟨1279850, by rfl⟩ : syracuseStep 1706467 = 2559701) B2559701
theorem B4098545 : Blo 670310 4098545 := bstep (se 2 (by rfl) ⟨1536954, by rfl⟩ : syracuseStep 4098545 = 3073909) B3073909
theorem B756211 : Blo 670310 756211 := bstep (se 1 (by rfl) ⟨567158, by rfl⟩ : syracuseStep 756211 = 1134317) B1134317
theorem B2722339 : Blo 670310 2722339 := bstep (se 1 (by rfl) ⟨2041754, by rfl⟩ : syracuseStep 2722339 = 4083509) B4083509
theorem B1510001 : Blo 670310 1510001 := bstep (se 2 (by rfl) ⟨566250, by rfl⟩ : syracuseStep 1510001 = 1132501) B1132501
theorem B1706609 : Blo 670310 1706609 := bstep (se 2 (by rfl) ⟨639978, by rfl⟩ : syracuseStep 1706609 = 1279957) B1279957
theorem B1510019 : Blo 670310 1510019 := bstep (se 1 (by rfl) ⟨1132514, by rfl⟩ : syracuseStep 1510019 = 2265029) B2265029
theorem B756355 : Blo 670310 756355 := bstep (se 1 (by rfl) ⟨567266, by rfl⟩ : syracuseStep 756355 = 1134533) B1134533
theorem B756499 : Blo 670310 756499 := bstep (se 1 (by rfl) ⟨567374, by rfl⟩ : syracuseStep 756499 = 1134749) B1134749
theorem B2263949 : Blo 670310 2263949 := bstep (se 3 (by rfl) ⟨424490, by rfl⟩ : syracuseStep 2263949 = 848981) B848981
theorem B1510289 : Blo 670310 1510289 := bstep (se 2 (by rfl) ⟨566358, by rfl⟩ : syracuseStep 1510289 = 1132717) B1132717
theorem B1510307 : Blo 670310 1510307 := bstep (se 1 (by rfl) ⟨1132730, by rfl⟩ : syracuseStep 1510307 = 2265461) B2265461
theorem B756643 : Blo 670310 756643 := bstep (se 1 (by rfl) ⟨567482, by rfl⟩ : syracuseStep 756643 = 1134965) B1134965
theorem B2558897 : Blo 670310 2558897 := bstep (se 2 (by rfl) ⟨959586, by rfl⟩ : syracuseStep 2558897 = 1919173) B1919173
theorem B2264003 : Blo 670310 2264003 := bstep (se 1 (by rfl) ⟨1698002, by rfl⟩ : syracuseStep 2264003 = 3396005) B3396005
theorem B756787 : Blo 670310 756787 := bstep (se 1 (by rfl) ⟨567590, by rfl⟩ : syracuseStep 756787 = 1135181) B1135181
theorem B3837091 : Blo 670310 3837091 := bstep (se 1 (by rfl) ⟨2877818, by rfl⟩ : syracuseStep 3837091 = 5755637) B5755637
theorem B1510577 : Blo 670310 1510577 := bstep (se 2 (by rfl) ⟨566466, by rfl⟩ : syracuseStep 1510577 = 1132933) B1132933
theorem B1510595 : Blo 670310 1510595 := bstep (se 1 (by rfl) ⟨1132946, by rfl⟩ : syracuseStep 1510595 = 2265893) B2265893
theorem B756931 : Blo 670310 756931 := bstep (se 1 (by rfl) ⟨567698, by rfl⟩ : syracuseStep 756931 = 1135397) B1135397
theorem B2264273 : Blo 670310 2264273 := bstep (se 2 (by rfl) ⟨849102, by rfl⟩ : syracuseStep 2264273 = 1698205) B1698205
theorem B3673349 : Blo 670310 3673349 := bstep (se 4 (by rfl) ⟨344376, by rfl⟩ : syracuseStep 3673349 = 688753) B688753
theorem B5115149 : Blo 670310 5115149 := bstep (se 3 (by rfl) ⟨959090, by rfl⟩ : syracuseStep 5115149 = 1918181) B1918181
theorem B757075 : Blo 670310 757075 := bstep (se 1 (by rfl) ⟨567806, by rfl⟩ : syracuseStep 757075 = 1135613) B1135613
theorem B1510865 : Blo 670310 1510865 := bstep (se 2 (by rfl) ⟨566574, by rfl⟩ : syracuseStep 1510865 = 1133149) B1133149
theorem B1510883 : Blo 670310 1510883 := bstep (se 1 (by rfl) ⟨1133162, by rfl⟩ : syracuseStep 1510883 = 2266325) B2266325
theorem B757219 : Blo 670310 757219 := bstep (se 1 (by rfl) ⟨567914, by rfl⟩ : syracuseStep 757219 = 1135829) B1135829
theorem B2723377 : Blo 670310 2723377 := bstep (se 2 (by rfl) ⟨1021266, by rfl⟩ : syracuseStep 2723377 = 2042533) B2042533
theorem B3640945 : Blo 670310 3640945 := bstep (se 2 (by rfl) ⟨1365354, by rfl⟩ : syracuseStep 3640945 = 2730709) B2730709
theorem B757363 : Blo 670310 757363 := bstep (se 1 (by rfl) ⟨568022, by rfl⟩ : syracuseStep 757363 = 1136045) B1136045
theorem B3837617 : Blo 670310 3837617 := bstep (se 2 (by rfl) ⟨1439106, by rfl⟩ : syracuseStep 3837617 = 2878213) B2878213
theorem B2264813 : Blo 670310 2264813 := bstep (se 3 (by rfl) ⟨424652, by rfl⟩ : syracuseStep 2264813 = 849305) B849305
theorem B1511153 : Blo 670310 1511153 := bstep (se 2 (by rfl) ⟨566682, by rfl⟩ : syracuseStep 1511153 = 1133365) B1133365
theorem B1511171 : Blo 670310 1511171 := bstep (se 1 (by rfl) ⟨1133378, by rfl⟩ : syracuseStep 1511171 = 2266757) B2266757
theorem B757507 : Blo 670310 757507 := bstep (se 1 (by rfl) ⟨568130, by rfl⟩ : syracuseStep 757507 = 1136261) B1136261
theorem B2264867 : Blo 670310 2264867 := bstep (se 1 (by rfl) ⟨1698650, by rfl⟩ : syracuseStep 2264867 = 3397301) B3397301
theorem B757651 : Blo 670310 757651 := bstep (se 1 (by rfl) ⟨568238, by rfl⟩ : syracuseStep 757651 = 1136477) B1136477
theorem B1511441 : Blo 670310 1511441 := bstep (se 2 (by rfl) ⟨566790, by rfl⟩ : syracuseStep 1511441 = 1133581) B1133581
theorem B1511459 : Blo 670310 1511459 := bstep (se 1 (by rfl) ⟨1133594, by rfl⟩ : syracuseStep 1511459 = 2267189) B2267189
theorem B757795 : Blo 670310 757795 := bstep (se 1 (by rfl) ⟨568346, by rfl⟩ : syracuseStep 757795 = 1136693) B1136693
theorem B2265137 : Blo 670310 2265137 := bstep (se 2 (by rfl) ⟨849426, by rfl⟩ : syracuseStep 2265137 = 1698853) B1698853
theorem B757939 : Blo 670310 757939 := bstep (se 1 (by rfl) ⟨568454, by rfl⟩ : syracuseStep 757939 = 1136909) B1136909
theorem B1151185 : Blo 670310 1151185 := bstep (se 2 (by rfl) ⟨431694, by rfl⟩ : syracuseStep 1151185 = 863389) B863389
theorem B1511729 : Blo 670310 1511729 := bstep (se 2 (by rfl) ⟨566898, by rfl⟩ : syracuseStep 1511729 = 1133797) B1133797
theorem B2298179 : Blo 670310 2298179 := bstep (se 1 (by rfl) ⟨1723634, by rfl⟩ : syracuseStep 2298179 = 3447269) B3447269
theorem B1511747 : Blo 670310 1511747 := bstep (se 1 (by rfl) ⟨1133810, by rfl⟩ : syracuseStep 1511747 = 2267621) B2267621
theorem B758083 : Blo 670310 758083 := bstep (se 1 (by rfl) ⟨568562, by rfl⟩ : syracuseStep 758083 = 1137125) B1137125
theorem B954785 : Blo 670310 954785 := bstep (se 2 (by rfl) ⟨358044, by rfl⟩ : syracuseStep 954785 = 716089) B716089
theorem B1151443 : Blo 670310 1151443 := bstep (se 1 (by rfl) ⟨863582, by rfl⟩ : syracuseStep 1151443 = 1727165) B1727165
theorem B758227 : Blo 670310 758227 := bstep (se 1 (by rfl) ⟨568670, by rfl⟩ : syracuseStep 758227 = 1137341) B1137341
theorem B954865 : Blo 670310 954865 := bstep (se 2 (by rfl) ⟨358074, by rfl⟩ : syracuseStep 954865 = 716149) B716149
theorem B2298385 : Blo 670310 2298385 := bstep (se 2 (by rfl) ⟨861894, by rfl⟩ : syracuseStep 2298385 = 1723789) B1723789
theorem B3412529 : Blo 670310 3412529 := bstep (se 2 (by rfl) ⟨1279698, by rfl⟩ : syracuseStep 3412529 = 2559397) B2559397
theorem B2265677 : Blo 670310 2265677 := bstep (se 3 (by rfl) ⟨424814, by rfl⟩ : syracuseStep 2265677 = 849629) B849629
theorem B1512017 : Blo 670310 1512017 := bstep (se 2 (by rfl) ⟨567006, by rfl⟩ : syracuseStep 1512017 = 1134013) B1134013
theorem B1512035 : Blo 670310 1512035 := bstep (se 1 (by rfl) ⟨1134026, by rfl⟩ : syracuseStep 1512035 = 2268053) B2268053
theorem B758371 : Blo 670310 758371 := bstep (se 1 (by rfl) ⟨568778, by rfl⟩ : syracuseStep 758371 = 1137557) B1137557
theorem B2265731 : Blo 670310 2265731 := bstep (se 1 (by rfl) ⟨1699298, by rfl⟩ : syracuseStep 2265731 = 3398597) B3398597
theorem B3117731 : Blo 670310 3117731 := bstep (se 1 (by rfl) ⟨2338298, by rfl⟩ : syracuseStep 3117731 = 4676597) B4676597
theorem B758515 : Blo 670310 758515 := bstep (se 1 (by rfl) ⟨568886, by rfl⟩ : syracuseStep 758515 = 1137773) B1137773
theorem B1512305 : Blo 670310 1512305 := bstep (se 2 (by rfl) ⟨567114, by rfl⟩ : syracuseStep 1512305 = 1134229) B1134229
theorem B1512323 : Blo 670310 1512323 := bstep (se 1 (by rfl) ⟨1134242, by rfl⟩ : syracuseStep 1512323 = 2268485) B2268485
theorem B2266001 : Blo 670310 2266001 := bstep (se 2 (by rfl) ⟨849750, by rfl⟩ : syracuseStep 2266001 = 1699501) B1699501
theorem B3839075 : Blo 670310 3839075 := bstep (se 1 (by rfl) ⟨2879306, by rfl⟩ : syracuseStep 3839075 = 5758613) B5758613
theorem B1512593 : Blo 670310 1512593 := bstep (se 2 (by rfl) ⟨567222, by rfl⟩ : syracuseStep 1512593 = 1134445) B1134445
theorem B2299043 : Blo 670310 2299043 := bstep (se 1 (by rfl) ⟨1724282, by rfl⟩ : syracuseStep 2299043 = 3448565) B3448565
theorem B1512611 : Blo 670310 1512611 := bstep (se 1 (by rfl) ⟨1134458, by rfl⟩ : syracuseStep 1512611 = 2268917) B2268917
theorem B2430179 : Blo 670310 2430179 := bstep (se 1 (by rfl) ⟨1822634, by rfl⟩ : syracuseStep 2430179 = 3645269) B3645269
theorem B955651 : Blo 670310 955651 := bstep (se 1 (by rfl) ⟨716738, by rfl⟩ : syracuseStep 955651 = 1433477) B1433477
theorem B922897 : Blo 670310 922897 := bstep (se 2 (by rfl) ⟨346086, by rfl⟩ : syracuseStep 922897 = 692173) B692173
theorem B3872069 : Blo 670310 3872069 := bstep (se 4 (by rfl) ⟨363006, by rfl⟩ : syracuseStep 3872069 = 726013) B726013
theorem B2266541 : Blo 670310 2266541 := bstep (se 3 (by rfl) ⟨424976, by rfl⟩ : syracuseStep 2266541 = 849953) B849953
theorem B1512881 : Blo 670310 1512881 := bstep (se 2 (by rfl) ⟨567330, by rfl⟩ : syracuseStep 1512881 = 1134661) B1134661
theorem B1512899 : Blo 670310 1512899 := bstep (se 1 (by rfl) ⟨1134674, by rfl⟩ : syracuseStep 1512899 = 2269349) B2269349
theorem B2725325 : Blo 670310 2725325 := bstep (se 3 (by rfl) ⟨510998, by rfl⟩ : syracuseStep 2725325 = 1021997) B1021997
theorem B2266595 : Blo 670310 2266595 := bstep (se 1 (by rfl) ⟨1699946, by rfl⟩ : syracuseStep 2266595 = 3399893) B3399893
theorem B4298275 : Blo 670310 4298275 := bstep (se 1 (by rfl) ⟨3223706, by rfl⟩ : syracuseStep 4298275 = 6447413) B6447413
theorem B1513169 : Blo 670310 1513169 := bstep (se 2 (by rfl) ⟨567438, by rfl⟩ : syracuseStep 1513169 = 1134877) B1134877
theorem B956129 : Blo 670310 956129 := bstep (se 2 (by rfl) ⟨358548, by rfl⟩ : syracuseStep 956129 = 717097) B717097
theorem B1513187 : Blo 670310 1513187 := bstep (se 1 (by rfl) ⟨1134890, by rfl⟩ : syracuseStep 1513187 = 2269781) B2269781
theorem B2266865 : Blo 670310 2266865 := bstep (se 2 (by rfl) ⟨850074, by rfl⟩ : syracuseStep 2266865 = 1700149) B1700149
theorem B1021729 : Blo 670310 1021729 := bstep (se 2 (by rfl) ⟨383148, by rfl⟩ : syracuseStep 1021729 = 766297) B766297
theorem B956243 : Blo 670310 956243 := bstep (se 1 (by rfl) ⟨717182, by rfl⟩ : syracuseStep 956243 = 1434365) B1434365
theorem B956323 : Blo 670310 956323 := bstep (se 1 (by rfl) ⟨717242, by rfl⟩ : syracuseStep 956323 = 1434485) B1434485
theorem B4134883 : Blo 670310 4134883 := bstep (se 1 (by rfl) ⟨3101162, by rfl⟩ : syracuseStep 4134883 = 6202325) B6202325
theorem B1513457 : Blo 670310 1513457 := bstep (se 2 (by rfl) ⟨567546, by rfl⟩ : syracuseStep 1513457 = 1135093) B1135093
theorem B1939459 : Blo 670310 1939459 := bstep (se 1 (by rfl) ⟨1454594, by rfl⟩ : syracuseStep 1939459 = 2909189) B2909189
theorem B1513475 : Blo 670310 1513475 := bstep (se 1 (by rfl) ⟨1135106, by rfl⟩ : syracuseStep 1513475 = 2270213) B2270213
theorem B2758691 : Blo 670310 2758691 := bstep (se 1 (by rfl) ⟨2069018, by rfl⟩ : syracuseStep 2758691 = 4138037) B4138037
theorem B5118065 : Blo 670310 5118065 := bstep (se 2 (by rfl) ⟨1919274, by rfl⟩ : syracuseStep 5118065 = 3838549) B3838549
theorem B7248113 : Blo 670310 7248113 := bstep (se 2 (by rfl) ⟨2718042, by rfl⟩ : syracuseStep 7248113 = 5436085) B5436085
theorem B8591629 : Blo 670310 8591629 := bstep (se 3 (by rfl) ⟨1610930, by rfl⟩ : syracuseStep 8591629 = 3221861) B3221861
theorem B2267405 : Blo 670310 2267405 := bstep (se 3 (by rfl) ⟨425138, by rfl⟩ : syracuseStep 2267405 = 850277) B850277
theorem B1513745 : Blo 670310 1513745 := bstep (se 2 (by rfl) ⟨567654, by rfl⟩ : syracuseStep 1513745 = 1135309) B1135309
theorem B1513763 : Blo 670310 1513763 := bstep (se 1 (by rfl) ⟨1135322, by rfl⟩ : syracuseStep 1513763 = 2270645) B2270645
theorem B3447089 : Blo 670310 3447089 := bstep (se 2 (by rfl) ⟨1292658, by rfl⟩ : syracuseStep 3447089 = 2585317) B2585317
theorem B2267459 : Blo 670310 2267459 := bstep (se 1 (by rfl) ⟨1700594, by rfl⟩ : syracuseStep 2267459 = 3401189) B3401189
theorem B956881 : Blo 670310 956881 := bstep (se 2 (by rfl) ⟨358830, by rfl⟩ : syracuseStep 956881 = 717661) B717661
theorem B4299277 : Blo 670310 4299277 := bstep (se 3 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 4299277 = 1612229) B1612229
theorem B1514033 : Blo 670310 1514033 := bstep (se 2 (by rfl) ⟨567762, by rfl⟩ : syracuseStep 1514033 = 1135525) B1135525
theorem B1514051 : Blo 670310 1514051 := bstep (se 1 (by rfl) ⟨1135538, by rfl⟩ : syracuseStep 1514051 = 2271077) B2271077
theorem B2267729 : Blo 670310 2267729 := bstep (se 2 (by rfl) ⟨850398, by rfl⟩ : syracuseStep 2267729 = 1700797) B1700797
theorem B5184269 : Blo 670310 5184269 := bstep (se 3 (by rfl) ⟨972050, by rfl⟩ : syracuseStep 5184269 = 1944101) B1944101
theorem B1514321 : Blo 670310 1514321 := bstep (se 2 (by rfl) ⟨567870, by rfl⟩ : syracuseStep 1514321 = 1135741) B1135741
theorem B1514339 : Blo 670310 1514339 := bstep (se 1 (by rfl) ⟨1135754, by rfl⟩ : syracuseStep 1514339 = 2271509) B2271509
theorem B2038691 : Blo 670310 2038691 := bstep (se 1 (by rfl) ⟨1529018, by rfl⟩ : syracuseStep 2038691 = 3058037) B3058037
theorem B6462449 : Blo 670310 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B2038787 : Blo 670310 2038787 := bstep (se 1 (by rfl) ⟨1529090, by rfl⟩ : syracuseStep 2038787 = 3058181) B3058181
theorem B2268269 : Blo 670310 2268269 := bstep (se 3 (by rfl) ⟨425300, by rfl⟩ : syracuseStep 2268269 = 850601) B850601
theorem B1514609 : Blo 670310 1514609 := bstep (se 2 (by rfl) ⟨567978, by rfl⟩ : syracuseStep 1514609 = 1135957) B1135957
theorem B1514627 : Blo 670310 1514627 := bstep (se 1 (by rfl) ⟨1135970, by rfl⟩ : syracuseStep 1514627 = 2271941) B2271941
theorem B957587 : Blo 670310 957587 := bstep (se 1 (by rfl) ⟨718190, by rfl⟩ : syracuseStep 957587 = 1436381) B1436381
theorem B2268323 : Blo 670310 2268323 := bstep (se 1 (by rfl) ⟨1701242, by rfl⟩ : syracuseStep 2268323 = 3402485) B3402485
theorem B5741765 : Blo 670310 5741765 := bstep (se 4 (by rfl) ⟨538290, by rfl⟩ : syracuseStep 5741765 = 1076581) B1076581
theorem B1613027 : Blo 670310 1613027 := bstep (se 1 (by rfl) ⟨1209770, by rfl⟩ : syracuseStep 1613027 = 2419541) B2419541
theorem B1514897 : Blo 670310 1514897 := bstep (se 2 (by rfl) ⟨568086, by rfl⟩ : syracuseStep 1514897 = 1136173) B1136173
theorem B1514915 : Blo 670310 1514915 := bstep (se 1 (by rfl) ⟨1136186, by rfl⟩ : syracuseStep 1514915 = 2272373) B2272373
theorem B2268593 : Blo 670310 2268593 := bstep (se 2 (by rfl) ⟨850722, by rfl⟩ : syracuseStep 2268593 = 1701445) B1701445
theorem B9182645 : Blo 670310 9182645 := bstep (se 5 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 9182645 = 860873) B860873
theorem B8592965 : Blo 670310 8592965 := bstep (se 4 (by rfl) ⟨805590, by rfl⟩ : syracuseStep 8592965 = 1611181) B1611181
theorem B2301571 : Blo 670310 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B1515185 : Blo 670310 1515185 := bstep (se 2 (by rfl) ⟨568194, by rfl⟩ : syracuseStep 1515185 = 1136389) B1136389
theorem B1515203 : Blo 670310 1515203 := bstep (se 1 (by rfl) ⟨1136402, by rfl⟩ : syracuseStep 1515203 = 2272805) B2272805
theorem B7282403 : Blo 670310 7282403 := bstep (se 1 (by rfl) ⟨5461802, by rfl⟩ : syracuseStep 7282403 = 10923605) B10923605
theorem B958225 : Blo 670310 958225 := bstep (se 2 (by rfl) ⟨359334, by rfl⟩ : syracuseStep 958225 = 718669) B718669
theorem B728899 : Blo 670310 728899 := bstep (se 1 (by rfl) ⟨546674, by rfl⟩ : syracuseStep 728899 = 1093349) B1093349
theorem B1613699 : Blo 670310 1613699 := bstep (se 1 (by rfl) ⟨1210274, by rfl⟩ : syracuseStep 1613699 = 2420549) B2420549
theorem B958339 : Blo 670310 958339 := bstep (se 1 (by rfl) ⟨718754, by rfl⟩ : syracuseStep 958339 = 1437509) B1437509
theorem B2269133 : Blo 670310 2269133 := bstep (se 3 (by rfl) ⟨425462, by rfl⟩ : syracuseStep 2269133 = 850925) B850925
theorem B1515473 : Blo 670310 1515473 := bstep (se 2 (by rfl) ⟨568302, by rfl⟩ : syracuseStep 1515473 = 1136605) B1136605
theorem B1515491 : Blo 670310 1515491 := bstep (se 1 (by rfl) ⟨1136618, by rfl⟩ : syracuseStep 1515491 = 2273237) B2273237
theorem B2269187 : Blo 670310 2269187 := bstep (se 1 (by rfl) ⟨1701890, by rfl⟩ : syracuseStep 2269187 = 3403781) B3403781
theorem B1613969 : Blo 670310 1613969 := bstep (se 2 (by rfl) ⟨605238, by rfl⟩ : syracuseStep 1613969 = 1210477) B1210477
theorem B1515761 : Blo 670310 1515761 := bstep (se 2 (by rfl) ⟨568410, by rfl⟩ : syracuseStep 1515761 = 1136821) B1136821
theorem B1515779 : Blo 670310 1515779 := bstep (se 1 (by rfl) ⟨1136834, by rfl⟩ : syracuseStep 1515779 = 2273669) B2273669
theorem B2269457 : Blo 670310 2269457 := bstep (se 2 (by rfl) ⟨851046, by rfl⟩ : syracuseStep 2269457 = 1702093) B1702093
theorem B1614161 : Blo 670310 1614161 := bstep (se 2 (by rfl) ⟨605310, by rfl⟩ : syracuseStep 1614161 = 1210621) B1210621
theorem B29041037 : Blo 670310 29041037 := bstep (se 3 (by rfl) ⟨5445194, by rfl⟩ : syracuseStep 29041037 = 10890389) B10890389
theorem B1614257 : Blo 670310 1614257 := bstep (se 2 (by rfl) ⟨605346, by rfl⟩ : syracuseStep 1614257 = 1210693) B1210693
theorem B729523 : Blo 670310 729523 := bstep (se 1 (by rfl) ⟨547142, by rfl⟩ : syracuseStep 729523 = 1094285) B1094285
theorem B1516049 : Blo 670310 1516049 := bstep (se 2 (by rfl) ⟨568518, by rfl⟩ : syracuseStep 1516049 = 1137037) B1137037
theorem B1516067 : Blo 670310 1516067 := bstep (se 1 (by rfl) ⟨1137050, by rfl⟩ : syracuseStep 1516067 = 2274101) B2274101
theorem B7250573 : Blo 670310 7250573 := bstep (se 3 (by rfl) ⟨1359482, by rfl⟩ : syracuseStep 7250573 = 2718965) B2718965
theorem B1909457 : Blo 670310 1909457 := bstep (se 2 (by rfl) ⟨716046, by rfl⟩ : syracuseStep 1909457 = 1432093) B1432093
theorem B2269997 : Blo 670310 2269997 := bstep (se 3 (by rfl) ⟨425624, by rfl⟩ : syracuseStep 2269997 = 851249) B851249
theorem B1516337 : Blo 670310 1516337 := bstep (se 2 (by rfl) ⟨568626, by rfl⟩ : syracuseStep 1516337 = 1137253) B1137253
theorem B1516355 : Blo 670310 1516355 := bstep (se 1 (by rfl) ⟨1137266, by rfl⟩ : syracuseStep 1516355 = 2274533) B2274533
theorem B2270051 : Blo 670310 2270051 := bstep (se 1 (by rfl) ⟨1702538, by rfl⟩ : syracuseStep 2270051 = 3405077) B3405077
theorem B1516625 : Blo 670310 1516625 := bstep (se 2 (by rfl) ⟨568734, by rfl⟩ : syracuseStep 1516625 = 1137469) B1137469
theorem B1516643 : Blo 670310 1516643 := bstep (se 1 (by rfl) ⟨1137482, by rfl⟩ : syracuseStep 1516643 = 2274965) B2274965
theorem B2270321 : Blo 670310 2270321 := bstep (se 2 (by rfl) ⟨851370, by rfl⟩ : syracuseStep 2270321 = 1702741) B1702741
theorem B959683 : Blo 670310 959683 := bstep (se 1 (by rfl) ⟨719762, by rfl⟩ : syracuseStep 959683 = 1439525) B1439525
theorem B2303245 : Blo 670310 2303245 := bstep (se 3 (by rfl) ⟨431858, by rfl⟩ : syracuseStep 2303245 = 863717) B863717
theorem B4859149 : Blo 670310 4859149 := bstep (se 3 (by rfl) ⟨911090, by rfl⟩ : syracuseStep 4859149 = 1822181) B1822181
theorem B1516913 : Blo 670310 1516913 := bstep (se 2 (by rfl) ⟨568842, by rfl⟩ : syracuseStep 1516913 = 1137685) B1137685
theorem B1516931 : Blo 670310 1516931 := bstep (se 1 (by rfl) ⟨1137698, by rfl⟩ : syracuseStep 1516931 = 2275397) B2275397
theorem B1910243 : Blo 670310 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B1615459 : Blo 670310 1615459 := bstep (se 1 (by rfl) ⟨1211594, by rfl⟩ : syracuseStep 1615459 = 2423189) B2423189
theorem B1943153 : Blo 670310 1943153 := bstep (se 2 (by rfl) ⟨728682, by rfl⟩ : syracuseStep 1943153 = 1457365) B1457365
theorem B2270861 : Blo 670310 2270861 := bstep (se 3 (by rfl) ⟨425786, by rfl⟩ : syracuseStep 2270861 = 851573) B851573
theorem B2270915 : Blo 670310 2270915 := bstep (se 1 (by rfl) ⟨1703186, by rfl⟩ : syracuseStep 2270915 = 3406373) B3406373
theorem B6465251 : Blo 670310 6465251 := bstep (se 1 (by rfl) ⟨4848938, by rfl⟩ : syracuseStep 6465251 = 9697877) B9697877
theorem B1910573 : Blo 670310 1910573 := bstep (se 3 (by rfl) ⟨358232, by rfl⟩ : syracuseStep 1910573 = 716465) B716465
theorem B1910641 : Blo 670310 1910641 := bstep (se 2 (by rfl) ⟨716490, by rfl⟩ : syracuseStep 1910641 = 1432981) B1432981
theorem B2271185 : Blo 670310 2271185 := bstep (se 2 (by rfl) ⟨851694, by rfl⟩ : syracuseStep 2271185 = 1703389) B1703389
theorem B1910915 : Blo 670310 1910915 := bstep (se 1 (by rfl) ⟨1433186, by rfl⟩ : syracuseStep 1910915 = 2866373) B2866373
theorem B2271725 : Blo 670310 2271725 := bstep (se 3 (by rfl) ⟨425948, by rfl⟩ : syracuseStep 2271725 = 851897) B851897
theorem B2271779 : Blo 670310 2271779 := bstep (se 1 (by rfl) ⟨1703834, by rfl⟩ : syracuseStep 2271779 = 3407669) B3407669
theorem B2304557 : Blo 670310 2304557 := bstep (se 3 (by rfl) ⟨432104, by rfl⟩ : syracuseStep 2304557 = 864209) B864209
theorem B1747505 : Blo 670310 1747505 := bstep (se 2 (by rfl) ⟨655314, by rfl⟩ : syracuseStep 1747505 = 1310629) B1310629
theorem B3058381 : Blo 670310 3058381 := bstep (se 3 (by rfl) ⟨573446, by rfl⟩ : syracuseStep 3058381 = 1146893) B1146893
theorem B2304749 : Blo 670310 2304749 := bstep (se 3 (by rfl) ⟨432140, by rfl⟩ : syracuseStep 2304749 = 864281) B864281
theorem B1616689 : Blo 670310 1616689 := bstep (se 2 (by rfl) ⟨606258, by rfl⟩ : syracuseStep 1616689 = 1212517) B1212517
theorem B2272049 : Blo 670310 2272049 := bstep (se 2 (by rfl) ⟨852018, by rfl⟩ : syracuseStep 2272049 = 1704037) B1704037
theorem B1911757 : Blo 670310 1911757 := bstep (se 3 (by rfl) ⟨358454, by rfl⟩ : syracuseStep 1911757 = 716909) B716909
theorem B1911917 : Blo 670310 1911917 := bstep (se 3 (by rfl) ⟨358484, by rfl⟩ : syracuseStep 1911917 = 716969) B716969
theorem B1813681 : Blo 670310 1813681 := bstep (se 2 (by rfl) ⟨680130, by rfl⟩ : syracuseStep 1813681 = 1360261) B1360261
theorem B1912099 : Blo 670310 1912099 := bstep (se 1 (by rfl) ⟨1434074, by rfl⟩ : syracuseStep 1912099 = 2868149) B2868149
theorem B7679285 : Blo 670310 7679285 := bstep (se 5 (by rfl) ⟨359966, by rfl⟩ : syracuseStep 7679285 = 719933) B719933
theorem B2272589 : Blo 670310 2272589 := bstep (se 3 (by rfl) ⟨426110, by rfl⟩ : syracuseStep 2272589 = 852221) B852221
theorem B2272643 : Blo 670310 2272643 := bstep (se 1 (by rfl) ⟨1704482, by rfl⟩ : syracuseStep 2272643 = 3408965) B3408965
theorem B2272913 : Blo 670310 2272913 := bstep (se 2 (by rfl) ⟨852342, by rfl⟩ : syracuseStep 2272913 = 1704685) B1704685
theorem B1093441 : Blo 670310 1093441 := bstep (se 2 (by rfl) ⟨410040, by rfl⟩ : syracuseStep 1093441 = 820081) B820081
theorem B765763 : Blo 670310 765763 := bstep (se 1 (by rfl) ⟨574322, by rfl⟩ : syracuseStep 765763 = 1148645) B1148645
theorem B14528483 : Blo 670310 14528483 := bstep (se 1 (by rfl) ⟨10896362, by rfl⟩ : syracuseStep 14528483 = 21792725) B21792725
theorem B2273453 : Blo 670310 2273453 := bstep (se 3 (by rfl) ⟨426272, by rfl⟩ : syracuseStep 2273453 = 852545) B852545
theorem B2732237 : Blo 670310 2732237 := bstep (se 3 (by rfl) ⟨512294, by rfl⟩ : syracuseStep 2732237 = 1024589) B1024589
theorem B2273507 : Blo 670310 2273507 := bstep (se 1 (by rfl) ⟨1705130, by rfl⟩ : syracuseStep 2273507 = 3410261) B3410261
theorem B8597987 : Blo 670310 8597987 := bstep (se 1 (by rfl) ⟨6448490, by rfl⟩ : syracuseStep 8597987 = 12896981) B12896981
theorem B2273777 : Blo 670310 2273777 := bstep (se 2 (by rfl) ⟨852666, by rfl⟩ : syracuseStep 2273777 = 1705333) B1705333
theorem B1913489 : Blo 670310 1913489 := bstep (se 2 (by rfl) ⟨717558, by rfl⟩ : syracuseStep 1913489 = 1435117) B1435117
theorem B4305635 : Blo 670310 4305635 := bstep (se 1 (by rfl) ⟨3229226, by rfl⟩ : syracuseStep 4305635 = 6458453) B6458453
theorem B2274317 : Blo 670310 2274317 := bstep (se 3 (by rfl) ⟨426434, by rfl⟩ : syracuseStep 2274317 = 852869) B852869
theorem B2274371 : Blo 670310 2274371 := bstep (se 1 (by rfl) ⟨1705778, by rfl⟩ : syracuseStep 2274371 = 3411557) B3411557
theorem B4437325 : Blo 670310 4437325 := bstep (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) B1663997
theorem B2274641 : Blo 670310 2274641 := bstep (se 2 (by rfl) ⟨852990, by rfl⟩ : syracuseStep 2274641 = 1705981) B1705981
theorem B4601393 : Blo 670310 4601393 := bstep (se 2 (by rfl) ⟨1725522, by rfl⟩ : syracuseStep 4601393 = 3451045) B3451045
theorem B1914445 : Blo 670310 1914445 := bstep (se 3 (by rfl) ⟨358958, by rfl⟩ : syracuseStep 1914445 = 717917) B717917
theorem B4601585 : Blo 670310 4601585 := bstep (se 2 (by rfl) ⟨1725594, by rfl⟩ : syracuseStep 4601585 = 3451189) B3451189
theorem B1914673 : Blo 670310 1914673 := bstep (se 2 (by rfl) ⟨718002, by rfl⟩ : syracuseStep 1914673 = 1436005) B1436005
theorem B2275181 : Blo 670310 2275181 := bstep (se 3 (by rfl) ⟨426596, by rfl⟩ : syracuseStep 2275181 = 853193) B853193
theorem B2275235 : Blo 670310 2275235 := bstep (se 1 (by rfl) ⟨1706426, by rfl⟩ : syracuseStep 2275235 = 3412853) B3412853
theorem B1914833 : Blo 670310 1914833 := bstep (se 2 (by rfl) ⟨718062, by rfl⟩ : syracuseStep 1914833 = 1436125) B1436125
theorem B1914947 : Blo 670310 1914947 := bstep (se 1 (by rfl) ⟨1436210, by rfl⟩ : syracuseStep 1914947 = 2872421) B2872421
theorem B2275505 : Blo 670310 2275505 := bstep (se 2 (by rfl) ⟨853314, by rfl⟩ : syracuseStep 2275505 = 1706629) B1706629
theorem B4831757 : Blo 670310 4831757 := bstep (se 3 (by rfl) ⟨905954, by rfl⟩ : syracuseStep 4831757 = 1811909) B1811909
theorem B670323 : Blo 670310 670323 := bstep (se 1 (by rfl) ⟨502742, by rfl⟩ : syracuseStep 670323 = 1005485) B1005485
theorem B670339 : Blo 670310 670339 := bstep (se 1 (by rfl) ⟨502754, by rfl⟩ : syracuseStep 670339 = 1005509) B1005509
theorem B670355 : Blo 670310 670355 := bstep (se 1 (by rfl) ⟨502766, by rfl⟩ : syracuseStep 670355 = 1005533) B1005533
theorem B670371 : Blo 670310 670371 := bstep (se 1 (by rfl) ⟨502778, by rfl⟩ : syracuseStep 670371 = 1005557) B1005557
theorem B670387 : Blo 670310 670387 := bstep (se 1 (by rfl) ⟨502790, by rfl⟩ : syracuseStep 670387 = 1005581) B1005581
theorem B670403 : Blo 670310 670403 := bstep (se 1 (by rfl) ⟨502802, by rfl⟩ : syracuseStep 670403 = 1005605) B1005605
theorem B670419 : Blo 670310 670419 := bstep (se 1 (by rfl) ⟨502814, by rfl⟩ : syracuseStep 670419 = 1005629) B1005629
theorem B670435 : Blo 670310 670435 := bstep (se 1 (by rfl) ⟨502826, by rfl⟩ : syracuseStep 670435 = 1005653) B1005653
theorem B670451 : Blo 670310 670451 := bstep (se 1 (by rfl) ⟨502838, by rfl⟩ : syracuseStep 670451 = 1005677) B1005677
theorem B670467 : Blo 670310 670467 := bstep (se 1 (by rfl) ⟨502850, by rfl⟩ : syracuseStep 670467 = 1005701) B1005701
theorem B670483 : Blo 670310 670483 := bstep (se 1 (by rfl) ⟨502862, by rfl⟩ : syracuseStep 670483 = 1005725) B1005725
theorem B670499 : Blo 670310 670499 := bstep (se 1 (by rfl) ⟨502874, by rfl⟩ : syracuseStep 670499 = 1005749) B1005749
theorem B670515 : Blo 670310 670515 := bstep (se 1 (by rfl) ⟨502886, by rfl⟩ : syracuseStep 670515 = 1005773) B1005773
theorem B670531 : Blo 670310 670531 := bstep (se 1 (by rfl) ⟨502898, by rfl⟩ : syracuseStep 670531 = 1005797) B1005797
theorem B670547 : Blo 670310 670547 := bstep (se 1 (by rfl) ⟨502910, by rfl⟩ : syracuseStep 670547 = 1005821) B1005821
theorem B670563 : Blo 670310 670563 := bstep (se 1 (by rfl) ⟨502922, by rfl⟩ : syracuseStep 670563 = 1005845) B1005845
theorem B670579 : Blo 670310 670579 := bstep (se 1 (by rfl) ⟨502934, by rfl⟩ : syracuseStep 670579 = 1005869) B1005869
theorem B670595 : Blo 670310 670595 := bstep (se 1 (by rfl) ⟨502946, by rfl⟩ : syracuseStep 670595 = 1005893) B1005893
theorem B670611 : Blo 670310 670611 := bstep (se 1 (by rfl) ⟨502958, by rfl⟩ : syracuseStep 670611 = 1005917) B1005917
theorem B670627 : Blo 670310 670627 := bstep (se 1 (by rfl) ⟨502970, by rfl⟩ : syracuseStep 670627 = 1005941) B1005941
theorem B670643 : Blo 670310 670643 := bstep (se 1 (by rfl) ⟨502982, by rfl⟩ : syracuseStep 670643 = 1005965) B1005965
theorem B670659 : Blo 670310 670659 := bstep (se 1 (by rfl) ⟨502994, by rfl⟩ : syracuseStep 670659 = 1005989) B1005989
theorem B670675 : Blo 670310 670675 := bstep (se 1 (by rfl) ⟨503006, by rfl⟩ : syracuseStep 670675 = 1006013) B1006013
theorem B670691 : Blo 670310 670691 := bstep (se 1 (by rfl) ⟨503018, by rfl⟩ : syracuseStep 670691 = 1006037) B1006037
theorem B670707 : Blo 670310 670707 := bstep (se 1 (by rfl) ⟨503030, by rfl⟩ : syracuseStep 670707 = 1006061) B1006061
theorem B670723 : Blo 670310 670723 := bstep (se 1 (by rfl) ⟨503042, by rfl⟩ : syracuseStep 670723 = 1006085) B1006085
theorem B670739 : Blo 670310 670739 := bstep (se 1 (by rfl) ⟨503054, by rfl⟩ : syracuseStep 670739 = 1006109) B1006109
theorem B670755 : Blo 670310 670755 := bstep (se 1 (by rfl) ⟨503066, by rfl⟩ : syracuseStep 670755 = 1006133) B1006133
theorem B1915949 : Blo 670310 1915949 := bstep (se 3 (by rfl) ⟨359240, by rfl⟩ : syracuseStep 1915949 = 718481) B718481
theorem B670771 : Blo 670310 670771 := bstep (se 1 (by rfl) ⟨503078, by rfl⟩ : syracuseStep 670771 = 1006157) B1006157
theorem B670787 : Blo 670310 670787 := bstep (se 1 (by rfl) ⟨503090, by rfl⟩ : syracuseStep 670787 = 1006181) B1006181
theorem B670803 : Blo 670310 670803 := bstep (se 1 (by rfl) ⟨503102, by rfl⟩ : syracuseStep 670803 = 1006205) B1006205
theorem B670819 : Blo 670310 670819 := bstep (se 1 (by rfl) ⟨503114, by rfl⟩ : syracuseStep 670819 = 1006229) B1006229
theorem B670835 : Blo 670310 670835 := bstep (se 1 (by rfl) ⟨503126, by rfl⟩ : syracuseStep 670835 = 1006253) B1006253
theorem B670851 : Blo 670310 670851 := bstep (se 1 (by rfl) ⟨503138, by rfl⟩ : syracuseStep 670851 = 1006277) B1006277
theorem B670867 : Blo 670310 670867 := bstep (se 1 (by rfl) ⟨503150, by rfl⟩ : syracuseStep 670867 = 1006301) B1006301
theorem B670883 : Blo 670310 670883 := bstep (se 1 (by rfl) ⟨503162, by rfl⟩ : syracuseStep 670883 = 1006325) B1006325
theorem B670899 : Blo 670310 670899 := bstep (se 1 (by rfl) ⟨503174, by rfl⟩ : syracuseStep 670899 = 1006349) B1006349
theorem B670915 : Blo 670310 670915 := bstep (se 1 (by rfl) ⟨503186, by rfl⟩ : syracuseStep 670915 = 1006373) B1006373
theorem B670931 : Blo 670310 670931 := bstep (se 1 (by rfl) ⟨503198, by rfl⟩ : syracuseStep 670931 = 1006397) B1006397
theorem B670947 : Blo 670310 670947 := bstep (se 1 (by rfl) ⟨503210, by rfl⟩ : syracuseStep 670947 = 1006421) B1006421
theorem B4144355 : Blo 670310 4144355 := bstep (se 1 (by rfl) ⟨3108266, by rfl⟩ : syracuseStep 4144355 = 6216533) B6216533
theorem B1916131 : Blo 670310 1916131 := bstep (se 1 (by rfl) ⟨1437098, by rfl⟩ : syracuseStep 1916131 = 2874197) B2874197
theorem B670963 : Blo 670310 670963 := bstep (se 1 (by rfl) ⟨503222, by rfl⟩ : syracuseStep 670963 = 1006445) B1006445
theorem B670979 : Blo 670310 670979 := bstep (se 1 (by rfl) ⟨503234, by rfl⟩ : syracuseStep 670979 = 1006469) B1006469
theorem B670995 : Blo 670310 670995 := bstep (se 1 (by rfl) ⟨503246, by rfl⟩ : syracuseStep 670995 = 1006493) B1006493
theorem B671011 : Blo 670310 671011 := bstep (se 1 (by rfl) ⟨503258, by rfl⟩ : syracuseStep 671011 = 1006517) B1006517
theorem B671027 : Blo 670310 671027 := bstep (se 1 (by rfl) ⟨503270, by rfl⟩ : syracuseStep 671027 = 1006541) B1006541
theorem B671043 : Blo 670310 671043 := bstep (se 1 (by rfl) ⟨503282, by rfl⟩ : syracuseStep 671043 = 1006565) B1006565
theorem B671059 : Blo 670310 671059 := bstep (se 1 (by rfl) ⟨503294, by rfl⟩ : syracuseStep 671059 = 1006589) B1006589
theorem B671075 : Blo 670310 671075 := bstep (se 1 (by rfl) ⟨503306, by rfl⟩ : syracuseStep 671075 = 1006613) B1006613
theorem B1359217 : Blo 670310 1359217 := bstep (se 2 (by rfl) ⟨509706, by rfl⟩ : syracuseStep 1359217 = 1019413) B1019413
theorem B671091 : Blo 670310 671091 := bstep (se 1 (by rfl) ⟨503318, by rfl⟩ : syracuseStep 671091 = 1006637) B1006637
theorem B671107 : Blo 670310 671107 := bstep (se 1 (by rfl) ⟨503330, by rfl⟩ : syracuseStep 671107 = 1006661) B1006661
theorem B1916291 : Blo 670310 1916291 := bstep (se 1 (by rfl) ⟨1437218, by rfl⟩ : syracuseStep 1916291 = 2874437) B2874437
theorem B671123 : Blo 670310 671123 := bstep (se 1 (by rfl) ⟨503342, by rfl⟩ : syracuseStep 671123 = 1006685) B1006685
theorem B671139 : Blo 670310 671139 := bstep (se 1 (by rfl) ⟨503354, by rfl⟩ : syracuseStep 671139 = 1006709) B1006709
theorem B671155 : Blo 670310 671155 := bstep (se 1 (by rfl) ⟨503366, by rfl⟩ : syracuseStep 671155 = 1006733) B1006733
theorem B671171 : Blo 670310 671171 := bstep (se 1 (by rfl) ⟨503378, by rfl⟩ : syracuseStep 671171 = 1006757) B1006757
theorem B671187 : Blo 670310 671187 := bstep (se 1 (by rfl) ⟨503390, by rfl⟩ : syracuseStep 671187 = 1006781) B1006781
theorem B671203 : Blo 670310 671203 := bstep (se 1 (by rfl) ⟨503402, by rfl⟩ : syracuseStep 671203 = 1006805) B1006805
theorem B671219 : Blo 670310 671219 := bstep (se 1 (by rfl) ⟨503414, by rfl⟩ : syracuseStep 671219 = 1006829) B1006829
theorem B671235 : Blo 670310 671235 := bstep (se 1 (by rfl) ⟨503426, by rfl⟩ : syracuseStep 671235 = 1006853) B1006853
theorem B671251 : Blo 670310 671251 := bstep (se 1 (by rfl) ⟨503438, by rfl⟩ : syracuseStep 671251 = 1006877) B1006877
theorem B671267 : Blo 670310 671267 := bstep (se 1 (by rfl) ⟨503450, by rfl⟩ : syracuseStep 671267 = 1006901) B1006901
theorem B671283 : Blo 670310 671283 := bstep (se 1 (by rfl) ⟨503462, by rfl⟩ : syracuseStep 671283 = 1006925) B1006925
theorem B671299 : Blo 670310 671299 := bstep (se 1 (by rfl) ⟨503474, by rfl⟩ : syracuseStep 671299 = 1006949) B1006949
theorem B671315 : Blo 670310 671315 := bstep (se 1 (by rfl) ⟨503486, by rfl⟩ : syracuseStep 671315 = 1006973) B1006973
theorem B671331 : Blo 670310 671331 := bstep (se 1 (by rfl) ⟨503498, by rfl⟩ : syracuseStep 671331 = 1006997) B1006997
theorem B671347 : Blo 670310 671347 := bstep (se 1 (by rfl) ⟨503510, by rfl⟩ : syracuseStep 671347 = 1007021) B1007021
theorem B671363 : Blo 670310 671363 := bstep (se 1 (by rfl) ⟨503522, by rfl⟩ : syracuseStep 671363 = 1007045) B1007045
theorem B671379 : Blo 670310 671379 := bstep (se 1 (by rfl) ⟨503534, by rfl⟩ : syracuseStep 671379 = 1007069) B1007069
theorem B671395 : Blo 670310 671395 := bstep (se 1 (by rfl) ⟨503546, by rfl⟩ : syracuseStep 671395 = 1007093) B1007093
theorem B671411 : Blo 670310 671411 := bstep (se 1 (by rfl) ⟨503558, by rfl⟩ : syracuseStep 671411 = 1007117) B1007117
theorem B671427 : Blo 670310 671427 := bstep (se 1 (by rfl) ⟨503570, by rfl⟩ : syracuseStep 671427 = 1007141) B1007141
theorem B671443 : Blo 670310 671443 := bstep (se 1 (by rfl) ⟨503582, by rfl⟩ : syracuseStep 671443 = 1007165) B1007165
theorem B671459 : Blo 670310 671459 := bstep (se 1 (by rfl) ⟨503594, by rfl⟩ : syracuseStep 671459 = 1007189) B1007189
theorem B5750513 : Blo 670310 5750513 := bstep (se 2 (by rfl) ⟨2156442, by rfl⟩ : syracuseStep 5750513 = 4312885) B4312885
theorem B1162993 : Blo 670310 1162993 := bstep (se 2 (by rfl) ⟨436122, by rfl⟩ : syracuseStep 1162993 = 872245) B872245
theorem B671475 : Blo 670310 671475 := bstep (se 1 (by rfl) ⟨503606, by rfl⟩ : syracuseStep 671475 = 1007213) B1007213
theorem B671491 : Blo 670310 671491 := bstep (se 1 (by rfl) ⟨503618, by rfl⟩ : syracuseStep 671491 = 1007237) B1007237
theorem B671507 : Blo 670310 671507 := bstep (se 1 (by rfl) ⟨503630, by rfl⟩ : syracuseStep 671507 = 1007261) B1007261
theorem B671523 : Blo 670310 671523 := bstep (se 1 (by rfl) ⟨503642, by rfl⟩ : syracuseStep 671523 = 1007285) B1007285
theorem B4308785 : Blo 670310 4308785 := bstep (se 2 (by rfl) ⟨1615794, by rfl⟩ : syracuseStep 4308785 = 3231589) B3231589
theorem B671539 : Blo 670310 671539 := bstep (se 1 (by rfl) ⟨503654, by rfl⟩ : syracuseStep 671539 = 1007309) B1007309
theorem B671555 : Blo 670310 671555 := bstep (se 1 (by rfl) ⟨503666, by rfl⟩ : syracuseStep 671555 = 1007333) B1007333
theorem B2867021 : Blo 670310 2867021 := bstep (se 3 (by rfl) ⟨537566, by rfl⟩ : syracuseStep 2867021 = 1075133) B1075133
theorem B671571 : Blo 670310 671571 := bstep (se 1 (by rfl) ⟨503678, by rfl⟩ : syracuseStep 671571 = 1007357) B1007357
theorem B671587 : Blo 670310 671587 := bstep (se 1 (by rfl) ⟨503690, by rfl⟩ : syracuseStep 671587 = 1007381) B1007381
theorem B4308835 : Blo 670310 4308835 := bstep (se 1 (by rfl) ⟨3231626, by rfl⟩ : syracuseStep 4308835 = 6463253) B6463253
theorem B671603 : Blo 670310 671603 := bstep (se 1 (by rfl) ⟨503702, by rfl⟩ : syracuseStep 671603 = 1007405) B1007405
theorem B671619 : Blo 670310 671619 := bstep (se 1 (by rfl) ⟨503714, by rfl⟩ : syracuseStep 671619 = 1007429) B1007429
theorem B671635 : Blo 670310 671635 := bstep (se 1 (by rfl) ⟨503726, by rfl⟩ : syracuseStep 671635 = 1007453) B1007453
theorem B671651 : Blo 670310 671651 := bstep (se 1 (by rfl) ⟨503738, by rfl⟩ : syracuseStep 671651 = 1007477) B1007477
theorem B671667 : Blo 670310 671667 := bstep (se 1 (by rfl) ⟨503750, by rfl⟩ : syracuseStep 671667 = 1007501) B1007501
theorem B671683 : Blo 670310 671683 := bstep (se 1 (by rfl) ⟨503762, by rfl⟩ : syracuseStep 671683 = 1007525) B1007525
theorem B671699 : Blo 670310 671699 := bstep (se 1 (by rfl) ⟨503774, by rfl⟩ : syracuseStep 671699 = 1007549) B1007549
theorem B671715 : Blo 670310 671715 := bstep (se 1 (by rfl) ⟨503786, by rfl⟩ : syracuseStep 671715 = 1007573) B1007573
theorem B671731 : Blo 670310 671731 := bstep (se 1 (by rfl) ⟨503798, by rfl⟩ : syracuseStep 671731 = 1007597) B1007597
theorem B671747 : Blo 670310 671747 := bstep (se 1 (by rfl) ⟨503810, by rfl⟩ : syracuseStep 671747 = 1007621) B1007621
theorem B671763 : Blo 670310 671763 := bstep (se 1 (by rfl) ⟨503822, by rfl⟩ : syracuseStep 671763 = 1007645) B1007645
theorem B671779 : Blo 670310 671779 := bstep (se 1 (by rfl) ⟨503834, by rfl⟩ : syracuseStep 671779 = 1007669) B1007669
theorem B671795 : Blo 670310 671795 := bstep (se 1 (by rfl) ⟨503846, by rfl⟩ : syracuseStep 671795 = 1007693) B1007693
theorem B671811 : Blo 670310 671811 := bstep (se 1 (by rfl) ⟨503858, by rfl⟩ : syracuseStep 671811 = 1007717) B1007717
theorem B671827 : Blo 670310 671827 := bstep (se 1 (by rfl) ⟨503870, by rfl⟩ : syracuseStep 671827 = 1007741) B1007741
theorem B671843 : Blo 670310 671843 := bstep (se 1 (by rfl) ⟨503882, by rfl⟩ : syracuseStep 671843 = 1007765) B1007765
theorem B671859 : Blo 670310 671859 := bstep (se 1 (by rfl) ⟨503894, by rfl⟩ : syracuseStep 671859 = 1007789) B1007789
theorem B671875 : Blo 670310 671875 := bstep (se 1 (by rfl) ⟨503906, by rfl⟩ : syracuseStep 671875 = 1007813) B1007813
theorem B671891 : Blo 670310 671891 := bstep (se 1 (by rfl) ⟨503918, by rfl⟩ : syracuseStep 671891 = 1007837) B1007837
theorem B2867363 : Blo 670310 2867363 := bstep (se 1 (by rfl) ⟨2150522, by rfl⟩ : syracuseStep 2867363 = 4301045) B4301045
theorem B671907 : Blo 670310 671907 := bstep (se 1 (by rfl) ⟨503930, by rfl⟩ : syracuseStep 671907 = 1007861) B1007861
theorem B671923 : Blo 670310 671923 := bstep (se 1 (by rfl) ⟨503942, by rfl⟩ : syracuseStep 671923 = 1007885) B1007885
theorem B671939 : Blo 670310 671939 := bstep (se 1 (by rfl) ⟨503954, by rfl⟩ : syracuseStep 671939 = 1007909) B1007909
theorem B671955 : Blo 670310 671955 := bstep (se 1 (by rfl) ⟨503966, by rfl⟩ : syracuseStep 671955 = 1007933) B1007933
theorem B671971 : Blo 670310 671971 := bstep (se 1 (by rfl) ⟨503978, by rfl⟩ : syracuseStep 671971 = 1007957) B1007957
theorem B671987 : Blo 670310 671987 := bstep (se 1 (by rfl) ⟨503990, by rfl⟩ : syracuseStep 671987 = 1007981) B1007981
theorem B672003 : Blo 670310 672003 := bstep (se 1 (by rfl) ⟨504002, by rfl⟩ : syracuseStep 672003 = 1008005) B1008005
theorem B672019 : Blo 670310 672019 := bstep (se 1 (by rfl) ⟨504014, by rfl⟩ : syracuseStep 672019 = 1008029) B1008029
theorem B672035 : Blo 670310 672035 := bstep (se 1 (by rfl) ⟨504026, by rfl⟩ : syracuseStep 672035 = 1008053) B1008053
theorem B672051 : Blo 670310 672051 := bstep (se 1 (by rfl) ⟨504038, by rfl⟩ : syracuseStep 672051 = 1008077) B1008077
theorem B672067 : Blo 670310 672067 := bstep (se 1 (by rfl) ⟨504050, by rfl⟩ : syracuseStep 672067 = 1008101) B1008101
theorem B672083 : Blo 670310 672083 := bstep (se 1 (by rfl) ⟨504062, by rfl⟩ : syracuseStep 672083 = 1008125) B1008125
theorem B672099 : Blo 670310 672099 := bstep (se 1 (by rfl) ⟨504074, by rfl⟩ : syracuseStep 672099 = 1008149) B1008149
theorem B672115 : Blo 670310 672115 := bstep (se 1 (by rfl) ⟨504086, by rfl⟩ : syracuseStep 672115 = 1008173) B1008173
theorem B672131 : Blo 670310 672131 := bstep (se 1 (by rfl) ⟨504098, by rfl⟩ : syracuseStep 672131 = 1008197) B1008197
theorem B672147 : Blo 670310 672147 := bstep (se 1 (by rfl) ⟨504110, by rfl⟩ : syracuseStep 672147 = 1008221) B1008221
theorem B672163 : Blo 670310 672163 := bstep (se 1 (by rfl) ⟨504122, by rfl⟩ : syracuseStep 672163 = 1008245) B1008245
theorem B1917361 : Blo 670310 1917361 := bstep (se 2 (by rfl) ⟨719010, by rfl⟩ : syracuseStep 1917361 = 1438021) B1438021
theorem B672179 : Blo 670310 672179 := bstep (se 1 (by rfl) ⟨504134, by rfl⟩ : syracuseStep 672179 = 1008269) B1008269
theorem B672195 : Blo 670310 672195 := bstep (se 1 (by rfl) ⟨504146, by rfl⟩ : syracuseStep 672195 = 1008293) B1008293
theorem B672211 : Blo 670310 672211 := bstep (se 1 (by rfl) ⟨504158, by rfl⟩ : syracuseStep 672211 = 1008317) B1008317
theorem B3817955 : Blo 670310 3817955 := bstep (se 1 (by rfl) ⟨2863466, by rfl⟩ : syracuseStep 3817955 = 5726933) B5726933
theorem B672227 : Blo 670310 672227 := bstep (se 1 (by rfl) ⟨504170, by rfl⟩ : syracuseStep 672227 = 1008341) B1008341
theorem B672243 : Blo 670310 672243 := bstep (se 1 (by rfl) ⟨504182, by rfl⟩ : syracuseStep 672243 = 1008365) B1008365
theorem B672259 : Blo 670310 672259 := bstep (se 1 (by rfl) ⟨504194, by rfl⟩ : syracuseStep 672259 = 1008389) B1008389
theorem B672275 : Blo 670310 672275 := bstep (se 1 (by rfl) ⟨504206, by rfl⟩ : syracuseStep 672275 = 1008413) B1008413
theorem B672291 : Blo 670310 672291 := bstep (se 1 (by rfl) ⟨504218, by rfl⟩ : syracuseStep 672291 = 1008437) B1008437
theorem B672307 : Blo 670310 672307 := bstep (se 1 (by rfl) ⟨504230, by rfl⟩ : syracuseStep 672307 = 1008461) B1008461
theorem B672323 : Blo 670310 672323 := bstep (se 1 (by rfl) ⟨504242, by rfl⟩ : syracuseStep 672323 = 1008485) B1008485
theorem B1819217 : Blo 670310 1819217 := bstep (se 2 (by rfl) ⟨682206, by rfl⟩ : syracuseStep 1819217 = 1364413) B1364413
theorem B672339 : Blo 670310 672339 := bstep (se 1 (by rfl) ⟨504254, by rfl⟩ : syracuseStep 672339 = 1008509) B1008509
theorem B672355 : Blo 670310 672355 := bstep (se 1 (by rfl) ⟨504266, by rfl⟩ : syracuseStep 672355 = 1008533) B1008533
theorem B2867825 : Blo 670310 2867825 := bstep (se 2 (by rfl) ⟨1075434, by rfl⟩ : syracuseStep 2867825 = 2150869) B2150869
theorem B672371 : Blo 670310 672371 := bstep (se 1 (by rfl) ⟨504278, by rfl⟩ : syracuseStep 672371 = 1008557) B1008557
theorem B672387 : Blo 670310 672387 := bstep (se 1 (by rfl) ⟨504290, by rfl⟩ : syracuseStep 672387 = 1008581) B1008581
theorem B672403 : Blo 670310 672403 := bstep (se 1 (by rfl) ⟨504302, by rfl⟩ : syracuseStep 672403 = 1008605) B1008605
theorem B672419 : Blo 670310 672419 := bstep (se 1 (by rfl) ⟨504314, by rfl⟩ : syracuseStep 672419 = 1008629) B1008629
theorem B1131185 : Blo 670310 1131185 := bstep (se 2 (by rfl) ⟨424194, by rfl⟩ : syracuseStep 1131185 = 848389) B848389
theorem B672435 : Blo 670310 672435 := bstep (se 1 (by rfl) ⟨504326, by rfl⟩ : syracuseStep 672435 = 1008653) B1008653
theorem B672451 : Blo 670310 672451 := bstep (se 1 (by rfl) ⟨504338, by rfl⟩ : syracuseStep 672451 = 1008677) B1008677
theorem B672467 : Blo 670310 672467 := bstep (se 1 (by rfl) ⟨504350, by rfl⟩ : syracuseStep 672467 = 1008701) B1008701
theorem B672483 : Blo 670310 672483 := bstep (se 1 (by rfl) ⟨504362, by rfl⟩ : syracuseStep 672483 = 1008725) B1008725
theorem B672499 : Blo 670310 672499 := bstep (se 1 (by rfl) ⟨504374, by rfl⟩ : syracuseStep 672499 = 1008749) B1008749
theorem B672515 : Blo 670310 672515 := bstep (se 1 (by rfl) ⟨504386, by rfl⟩ : syracuseStep 672515 = 1008773) B1008773
theorem B672531 : Blo 670310 672531 := bstep (se 1 (by rfl) ⟨504398, by rfl⟩ : syracuseStep 672531 = 1008797) B1008797
theorem B672547 : Blo 670310 672547 := bstep (se 1 (by rfl) ⟨504410, by rfl⟩ : syracuseStep 672547 = 1008821) B1008821
theorem B1131313 : Blo 670310 1131313 := bstep (se 2 (by rfl) ⟨424242, by rfl⟩ : syracuseStep 1131313 = 848485) B848485
theorem B672563 : Blo 670310 672563 := bstep (se 1 (by rfl) ⟨504422, by rfl⟩ : syracuseStep 672563 = 1008845) B1008845
theorem B672579 : Blo 670310 672579 := bstep (se 1 (by rfl) ⟨504434, by rfl⟩ : syracuseStep 672579 = 1008869) B1008869
theorem B1131347 : Blo 670310 1131347 := bstep (se 1 (by rfl) ⟨848510, by rfl⟩ : syracuseStep 1131347 = 1697021) B1697021
theorem B672595 : Blo 670310 672595 := bstep (se 1 (by rfl) ⟨504446, by rfl⟩ : syracuseStep 672595 = 1008893) B1008893
theorem B672611 : Blo 670310 672611 := bstep (se 1 (by rfl) ⟨504458, by rfl⟩ : syracuseStep 672611 = 1008917) B1008917
theorem B672627 : Blo 670310 672627 := bstep (se 1 (by rfl) ⟨504470, by rfl⟩ : syracuseStep 672627 = 1008941) B1008941
theorem B672643 : Blo 670310 672643 := bstep (se 1 (by rfl) ⟨504482, by rfl⟩ : syracuseStep 672643 = 1008965) B1008965
theorem B672659 : Blo 670310 672659 := bstep (se 1 (by rfl) ⟨504494, by rfl⟩ : syracuseStep 672659 = 1008989) B1008989
theorem B672675 : Blo 670310 672675 := bstep (se 1 (by rfl) ⟨504506, by rfl⟩ : syracuseStep 672675 = 1009013) B1009013
theorem B672691 : Blo 670310 672691 := bstep (se 1 (by rfl) ⟨504518, by rfl⟩ : syracuseStep 672691 = 1009037) B1009037
theorem B672707 : Blo 670310 672707 := bstep (se 1 (by rfl) ⟨504530, by rfl⟩ : syracuseStep 672707 = 1009061) B1009061
theorem B1164241 : Blo 670310 1164241 := bstep (se 2 (by rfl) ⟨436590, by rfl⟩ : syracuseStep 1164241 = 873181) B873181
theorem B1131475 : Blo 670310 1131475 := bstep (se 1 (by rfl) ⟨848606, by rfl⟩ : syracuseStep 1131475 = 1697213) B1697213
theorem B672723 : Blo 670310 672723 := bstep (se 1 (by rfl) ⟨504542, by rfl⟩ : syracuseStep 672723 = 1009085) B1009085
theorem B672739 : Blo 670310 672739 := bstep (se 1 (by rfl) ⟨504554, by rfl⟩ : syracuseStep 672739 = 1009109) B1009109
theorem B672755 : Blo 670310 672755 := bstep (se 1 (by rfl) ⟨504566, by rfl⟩ : syracuseStep 672755 = 1009133) B1009133
theorem B672771 : Blo 670310 672771 := bstep (se 1 (by rfl) ⟨504578, by rfl⟩ : syracuseStep 672771 = 1009157) B1009157
theorem B672787 : Blo 670310 672787 := bstep (se 1 (by rfl) ⟨504590, by rfl⟩ : syracuseStep 672787 = 1009181) B1009181
theorem B672803 : Blo 670310 672803 := bstep (se 1 (by rfl) ⟨504602, by rfl⟩ : syracuseStep 672803 = 1009205) B1009205
theorem B672819 : Blo 670310 672819 := bstep (se 1 (by rfl) ⟨504614, by rfl⟩ : syracuseStep 672819 = 1009229) B1009229
theorem B672835 : Blo 670310 672835 := bstep (se 1 (by rfl) ⟨504626, by rfl⟩ : syracuseStep 672835 = 1009253) B1009253
theorem B672851 : Blo 670310 672851 := bstep (se 1 (by rfl) ⟨504638, by rfl⟩ : syracuseStep 672851 = 1009277) B1009277
theorem B1131617 : Blo 670310 1131617 := bstep (se 2 (by rfl) ⟨424356, by rfl⟩ : syracuseStep 1131617 = 848713) B848713
theorem B672867 : Blo 670310 672867 := bstep (se 1 (by rfl) ⟨504650, by rfl⟩ : syracuseStep 672867 = 1009301) B1009301
theorem B672883 : Blo 670310 672883 := bstep (se 1 (by rfl) ⟨504662, by rfl⟩ : syracuseStep 672883 = 1009325) B1009325
theorem B672899 : Blo 670310 672899 := bstep (se 1 (by rfl) ⟨504674, by rfl⟩ : syracuseStep 672899 = 1009349) B1009349
theorem B3458189 : Blo 670310 3458189 := bstep (se 3 (by rfl) ⟨648410, by rfl⟩ : syracuseStep 3458189 = 1296821) B1296821
theorem B672915 : Blo 670310 672915 := bstep (se 1 (by rfl) ⟨504686, by rfl⟩ : syracuseStep 672915 = 1009373) B1009373
theorem B672931 : Blo 670310 672931 := bstep (se 1 (by rfl) ⟨504698, by rfl⟩ : syracuseStep 672931 = 1009397) B1009397
theorem B672947 : Blo 670310 672947 := bstep (se 1 (by rfl) ⟨504710, by rfl⟩ : syracuseStep 672947 = 1009421) B1009421
theorem B672963 : Blo 670310 672963 := bstep (se 1 (by rfl) ⟨504722, by rfl⟩ : syracuseStep 672963 = 1009445) B1009445
theorem B1361105 : Blo 670310 1361105 := bstep (se 2 (by rfl) ⟨510414, by rfl⟩ : syracuseStep 1361105 = 1020829) B1020829
theorem B672979 : Blo 670310 672979 := bstep (se 1 (by rfl) ⟨504734, by rfl⟩ : syracuseStep 672979 = 1009469) B1009469
theorem B1131745 : Blo 670310 1131745 := bstep (se 2 (by rfl) ⟨424404, by rfl⟩ : syracuseStep 1131745 = 848809) B848809
theorem B672995 : Blo 670310 672995 := bstep (se 1 (by rfl) ⟨504746, by rfl⟩ : syracuseStep 672995 = 1009493) B1009493
theorem B673011 : Blo 670310 673011 := bstep (se 1 (by rfl) ⟨504758, by rfl⟩ : syracuseStep 673011 = 1009517) B1009517
theorem B1131779 : Blo 670310 1131779 := bstep (se 1 (by rfl) ⟨848834, by rfl⟩ : syracuseStep 1131779 = 1697669) B1697669
theorem B673027 : Blo 670310 673027 := bstep (se 1 (by rfl) ⟨504770, by rfl⟩ : syracuseStep 673027 = 1009541) B1009541
theorem B673043 : Blo 670310 673043 := bstep (se 1 (by rfl) ⟨504782, by rfl⟩ : syracuseStep 673043 = 1009565) B1009565
theorem B673059 : Blo 670310 673059 := bstep (se 1 (by rfl) ⟨504794, by rfl⟩ : syracuseStep 673059 = 1009589) B1009589
theorem B673075 : Blo 670310 673075 := bstep (se 1 (by rfl) ⟨504806, by rfl⟩ : syracuseStep 673075 = 1009613) B1009613
theorem B673091 : Blo 670310 673091 := bstep (se 1 (by rfl) ⟨504818, by rfl⟩ : syracuseStep 673091 = 1009637) B1009637
theorem B673107 : Blo 670310 673107 := bstep (se 1 (by rfl) ⟨504830, by rfl⟩ : syracuseStep 673107 = 1009661) B1009661
theorem B673123 : Blo 670310 673123 := bstep (se 1 (by rfl) ⟨504842, by rfl⟩ : syracuseStep 673123 = 1009685) B1009685
theorem B6145379 : Blo 670310 6145379 := bstep (se 1 (by rfl) ⟨4609034, by rfl⟩ : syracuseStep 6145379 = 9218069) B9218069
theorem B673139 : Blo 670310 673139 := bstep (se 1 (by rfl) ⟨504854, by rfl⟩ : syracuseStep 673139 = 1009709) B1009709
theorem B1131907 : Blo 670310 1131907 := bstep (se 1 (by rfl) ⟨848930, by rfl⟩ : syracuseStep 1131907 = 1697861) B1697861
theorem B673155 : Blo 670310 673155 := bstep (se 1 (by rfl) ⟨504866, by rfl⟩ : syracuseStep 673155 = 1009733) B1009733
theorem B673171 : Blo 670310 673171 := bstep (se 1 (by rfl) ⟨504878, by rfl⟩ : syracuseStep 673171 = 1009757) B1009757
theorem B3229091 : Blo 670310 3229091 := bstep (se 1 (by rfl) ⟨2421818, by rfl⟩ : syracuseStep 3229091 = 4843637) B4843637
theorem B673187 : Blo 670310 673187 := bstep (se 1 (by rfl) ⟨504890, by rfl⟩ : syracuseStep 673187 = 1009781) B1009781
theorem B673203 : Blo 670310 673203 := bstep (se 1 (by rfl) ⟨504902, by rfl⟩ : syracuseStep 673203 = 1009805) B1009805
theorem B673219 : Blo 670310 673219 := bstep (se 1 (by rfl) ⟨504914, by rfl⟩ : syracuseStep 673219 = 1009829) B1009829
theorem B673235 : Blo 670310 673235 := bstep (se 1 (by rfl) ⟨504926, by rfl⟩ : syracuseStep 673235 = 1009853) B1009853
theorem B673251 : Blo 670310 673251 := bstep (se 1 (by rfl) ⟨504938, by rfl⟩ : syracuseStep 673251 = 1009877) B1009877
theorem B673267 : Blo 670310 673267 := bstep (se 1 (by rfl) ⟨504950, by rfl⟩ : syracuseStep 673267 = 1009901) B1009901
theorem B1263107 : Blo 670310 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B673283 : Blo 670310 673283 := bstep (se 1 (by rfl) ⟨504962, by rfl⟩ : syracuseStep 673283 = 1009925) B1009925
theorem B1132049 : Blo 670310 1132049 := bstep (se 2 (by rfl) ⟨424518, by rfl⟩ : syracuseStep 1132049 = 849037) B849037
theorem B673299 : Blo 670310 673299 := bstep (se 1 (by rfl) ⟨504974, by rfl⟩ : syracuseStep 673299 = 1009949) B1009949
theorem B673315 : Blo 670310 673315 := bstep (se 1 (by rfl) ⟨504986, by rfl⟩ : syracuseStep 673315 = 1009973) B1009973
theorem B673331 : Blo 670310 673331 := bstep (se 1 (by rfl) ⟨504998, by rfl⟩ : syracuseStep 673331 = 1009997) B1009997
theorem B673347 : Blo 670310 673347 := bstep (se 1 (by rfl) ⟨505010, by rfl⟩ : syracuseStep 673347 = 1010021) B1010021
theorem B673363 : Blo 670310 673363 := bstep (se 1 (by rfl) ⟨505022, by rfl⟩ : syracuseStep 673363 = 1010045) B1010045
theorem B673379 : Blo 670310 673379 := bstep (se 1 (by rfl) ⟨505034, by rfl⟩ : syracuseStep 673379 = 1010069) B1010069
theorem B3327601 : Blo 670310 3327601 := bstep (se 2 (by rfl) ⟨1247850, by rfl⟩ : syracuseStep 3327601 = 2495701) B2495701
theorem B673395 : Blo 670310 673395 := bstep (se 1 (by rfl) ⟨505046, by rfl⟩ : syracuseStep 673395 = 1010093) B1010093
theorem B673411 : Blo 670310 673411 := bstep (se 1 (by rfl) ⟨505058, by rfl⟩ : syracuseStep 673411 = 1010117) B1010117
theorem B1132177 : Blo 670310 1132177 := bstep (se 2 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 1132177 = 849133) B849133
theorem B673427 : Blo 670310 673427 := bstep (se 1 (by rfl) ⟨505070, by rfl⟩ : syracuseStep 673427 = 1010141) B1010141
theorem B673443 : Blo 670310 673443 := bstep (se 1 (by rfl) ⟨505082, by rfl⟩ : syracuseStep 673443 = 1010165) B1010165
theorem B1820333 : Blo 670310 1820333 := bstep (se 3 (by rfl) ⟨341312, by rfl⟩ : syracuseStep 1820333 = 682625) B682625
theorem B1918637 : Blo 670310 1918637 := bstep (se 3 (by rfl) ⟨359744, by rfl⟩ : syracuseStep 1918637 = 719489) B719489
theorem B1132211 : Blo 670310 1132211 := bstep (se 1 (by rfl) ⟨849158, by rfl⟩ : syracuseStep 1132211 = 1698317) B1698317
theorem B673459 : Blo 670310 673459 := bstep (se 1 (by rfl) ⟨505094, by rfl⟩ : syracuseStep 673459 = 1010189) B1010189
theorem B673475 : Blo 670310 673475 := bstep (se 1 (by rfl) ⟨505106, by rfl⟩ : syracuseStep 673475 = 1010213) B1010213
theorem B673491 : Blo 670310 673491 := bstep (se 1 (by rfl) ⟨505118, by rfl⟩ : syracuseStep 673491 = 1010237) B1010237
theorem B673507 : Blo 670310 673507 := bstep (se 1 (by rfl) ⟨505130, by rfl⟩ : syracuseStep 673507 = 1010261) B1010261
theorem B673523 : Blo 670310 673523 := bstep (se 1 (by rfl) ⟨505142, by rfl⟩ : syracuseStep 673523 = 1010285) B1010285
theorem B673539 : Blo 670310 673539 := bstep (se 1 (by rfl) ⟨505154, by rfl⟩ : syracuseStep 673539 = 1010309) B1010309
theorem B2148113 : Blo 670310 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B673555 : Blo 670310 673555 := bstep (se 1 (by rfl) ⟨505166, by rfl⟩ : syracuseStep 673555 = 1010333) B1010333
theorem B673571 : Blo 670310 673571 := bstep (se 1 (by rfl) ⟨505178, by rfl⟩ : syracuseStep 673571 = 1010357) B1010357
theorem B1132339 : Blo 670310 1132339 := bstep (se 1 (by rfl) ⟨849254, by rfl⟩ : syracuseStep 1132339 = 1698509) B1698509
theorem B673587 : Blo 670310 673587 := bstep (se 1 (by rfl) ⟨505190, by rfl⟩ : syracuseStep 673587 = 1010381) B1010381
theorem B673603 : Blo 670310 673603 := bstep (se 1 (by rfl) ⟨505202, by rfl⟩ : syracuseStep 673603 = 1010405) B1010405
theorem B673619 : Blo 670310 673619 := bstep (se 1 (by rfl) ⟨505214, by rfl⟩ : syracuseStep 673619 = 1010429) B1010429
theorem B673635 : Blo 670310 673635 := bstep (se 1 (by rfl) ⟨505226, by rfl⟩ : syracuseStep 673635 = 1010453) B1010453
theorem B1918819 : Blo 670310 1918819 := bstep (se 1 (by rfl) ⟨1439114, by rfl⟩ : syracuseStep 1918819 = 2878229) B2878229
theorem B673651 : Blo 670310 673651 := bstep (se 1 (by rfl) ⟨505238, by rfl⟩ : syracuseStep 673651 = 1010477) B1010477
theorem B673667 : Blo 670310 673667 := bstep (se 1 (by rfl) ⟨505250, by rfl⟩ : syracuseStep 673667 = 1010501) B1010501
theorem B20760461 : Blo 670310 20760461 := bstep (se 3 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 20760461 = 7785173) B7785173
theorem B1918865 : Blo 670310 1918865 := bstep (se 2 (by rfl) ⟨719574, by rfl⟩ : syracuseStep 1918865 = 1439149) B1439149
theorem B673683 : Blo 670310 673683 := bstep (se 1 (by rfl) ⟨505262, by rfl⟩ : syracuseStep 673683 = 1010525) B1010525
theorem B673699 : Blo 670310 673699 := bstep (se 1 (by rfl) ⟨505274, by rfl⟩ : syracuseStep 673699 = 1010549) B1010549
theorem B673715 : Blo 670310 673715 := bstep (se 1 (by rfl) ⟨505286, by rfl⟩ : syracuseStep 673715 = 1010573) B1010573
theorem B1132481 : Blo 670310 1132481 := bstep (se 2 (by rfl) ⟨424680, by rfl⟩ : syracuseStep 1132481 = 849361) B849361
theorem B673731 : Blo 670310 673731 := bstep (se 1 (by rfl) ⟨505298, by rfl⟩ : syracuseStep 673731 = 1010597) B1010597
theorem B673747 : Blo 670310 673747 := bstep (se 1 (by rfl) ⟨505310, by rfl⟩ : syracuseStep 673747 = 1010621) B1010621
theorem B673763 : Blo 670310 673763 := bstep (se 1 (by rfl) ⟨505322, by rfl⟩ : syracuseStep 673763 = 1010645) B1010645
theorem B673779 : Blo 670310 673779 := bstep (se 1 (by rfl) ⟨505334, by rfl⟩ : syracuseStep 673779 = 1010669) B1010669
theorem B673795 : Blo 670310 673795 := bstep (se 1 (by rfl) ⟨505346, by rfl⟩ : syracuseStep 673795 = 1010693) B1010693
theorem B2050051 : Blo 670310 2050051 := bstep (se 1 (by rfl) ⟨1537538, by rfl⟩ : syracuseStep 2050051 = 3075077) B3075077
theorem B673811 : Blo 670310 673811 := bstep (se 1 (by rfl) ⟨505358, by rfl⟩ : syracuseStep 673811 = 1010717) B1010717
theorem B673827 : Blo 670310 673827 := bstep (se 1 (by rfl) ⟨505370, by rfl⟩ : syracuseStep 673827 = 1010741) B1010741
theorem B673843 : Blo 670310 673843 := bstep (se 1 (by rfl) ⟨505382, by rfl⟩ : syracuseStep 673843 = 1010765) B1010765
theorem B1132609 : Blo 670310 1132609 := bstep (se 2 (by rfl) ⟨424728, by rfl⟩ : syracuseStep 1132609 = 849457) B849457
theorem B673859 : Blo 670310 673859 := bstep (se 1 (by rfl) ⟨505394, by rfl⟩ : syracuseStep 673859 = 1010789) B1010789
theorem B673875 : Blo 670310 673875 := bstep (se 1 (by rfl) ⟨505406, by rfl⟩ : syracuseStep 673875 = 1010813) B1010813
theorem B1132643 : Blo 670310 1132643 := bstep (se 1 (by rfl) ⟨849482, by rfl⟩ : syracuseStep 1132643 = 1698965) B1698965
theorem B673891 : Blo 670310 673891 := bstep (se 1 (by rfl) ⟨505418, by rfl⟩ : syracuseStep 673891 = 1010837) B1010837
theorem B673907 : Blo 670310 673907 := bstep (se 1 (by rfl) ⟨505430, by rfl⟩ : syracuseStep 673907 = 1010861) B1010861
theorem B673923 : Blo 670310 673923 := bstep (se 1 (by rfl) ⟨505442, by rfl⟩ : syracuseStep 673923 = 1010885) B1010885
theorem B673939 : Blo 670310 673939 := bstep (se 1 (by rfl) ⟨505454, by rfl⟩ : syracuseStep 673939 = 1010909) B1010909
theorem B673955 : Blo 670310 673955 := bstep (se 1 (by rfl) ⟨505466, by rfl⟩ : syracuseStep 673955 = 1010933) B1010933
theorem B2050211 : Blo 670310 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B673971 : Blo 670310 673971 := bstep (se 1 (by rfl) ⟨505478, by rfl⟩ : syracuseStep 673971 = 1010957) B1010957
theorem B673987 : Blo 670310 673987 := bstep (se 1 (by rfl) ⟨505490, by rfl⟩ : syracuseStep 673987 = 1010981) B1010981
theorem B4311245 : Blo 670310 4311245 := bstep (se 3 (by rfl) ⟨808358, by rfl⟩ : syracuseStep 4311245 = 1616717) B1616717
theorem B674003 : Blo 670310 674003 := bstep (se 1 (by rfl) ⟨505502, by rfl⟩ : syracuseStep 674003 = 1011005) B1011005
theorem B1132771 : Blo 670310 1132771 := bstep (se 1 (by rfl) ⟨849578, by rfl⟩ : syracuseStep 1132771 = 1699157) B1699157
theorem B674019 : Blo 670310 674019 := bstep (se 1 (by rfl) ⟨505514, by rfl⟩ : syracuseStep 674019 = 1011029) B1011029
theorem B674035 : Blo 670310 674035 := bstep (se 1 (by rfl) ⟨505526, by rfl⟩ : syracuseStep 674035 = 1011053) B1011053
theorem B674051 : Blo 670310 674051 := bstep (se 1 (by rfl) ⟨505538, by rfl⟩ : syracuseStep 674051 = 1011077) B1011077
theorem B674067 : Blo 670310 674067 := bstep (se 1 (by rfl) ⟨505550, by rfl⟩ : syracuseStep 674067 = 1011101) B1011101
theorem B674083 : Blo 670310 674083 := bstep (se 1 (by rfl) ⟨505562, by rfl⟩ : syracuseStep 674083 = 1011125) B1011125
theorem B674099 : Blo 670310 674099 := bstep (se 1 (by rfl) ⟨505574, by rfl⟩ : syracuseStep 674099 = 1011149) B1011149
theorem B674115 : Blo 670310 674115 := bstep (se 1 (by rfl) ⟨505586, by rfl⟩ : syracuseStep 674115 = 1011173) B1011173
theorem B674131 : Blo 670310 674131 := bstep (se 1 (by rfl) ⟨505598, by rfl⟩ : syracuseStep 674131 = 1011197) B1011197
theorem B674147 : Blo 670310 674147 := bstep (se 1 (by rfl) ⟨505610, by rfl⟩ : syracuseStep 674147 = 1011221) B1011221
theorem B1132913 : Blo 670310 1132913 := bstep (se 2 (by rfl) ⟨424842, by rfl⟩ : syracuseStep 1132913 = 849685) B849685
theorem B674163 : Blo 670310 674163 := bstep (se 1 (by rfl) ⟨505622, by rfl⟩ : syracuseStep 674163 = 1011245) B1011245
theorem B674179 : Blo 670310 674179 := bstep (se 1 (by rfl) ⟨505634, by rfl⟩ : syracuseStep 674179 = 1011269) B1011269
theorem B674195 : Blo 670310 674195 := bstep (se 1 (by rfl) ⟨505646, by rfl⟩ : syracuseStep 674195 = 1011293) B1011293
theorem B674211 : Blo 670310 674211 := bstep (se 1 (by rfl) ⟨505658, by rfl⟩ : syracuseStep 674211 = 1011317) B1011317
theorem B674227 : Blo 670310 674227 := bstep (se 1 (by rfl) ⟨505670, by rfl⟩ : syracuseStep 674227 = 1011341) B1011341
theorem B674243 : Blo 670310 674243 := bstep (se 1 (by rfl) ⟨505682, by rfl⟩ : syracuseStep 674243 = 1011365) B1011365
theorem B674259 : Blo 670310 674259 := bstep (se 1 (by rfl) ⟨505694, by rfl⟩ : syracuseStep 674259 = 1011389) B1011389
theorem B674275 : Blo 670310 674275 := bstep (se 1 (by rfl) ⟨505706, by rfl⟩ : syracuseStep 674275 = 1011413) B1011413
theorem B1133041 : Blo 670310 1133041 := bstep (se 2 (by rfl) ⟨424890, by rfl⟩ : syracuseStep 1133041 = 849781) B849781
theorem B674291 : Blo 670310 674291 := bstep (se 1 (by rfl) ⟨505718, by rfl⟩ : syracuseStep 674291 = 1011437) B1011437
theorem B674307 : Blo 670310 674307 := bstep (se 1 (by rfl) ⟨505730, by rfl⟩ : syracuseStep 674307 = 1011461) B1011461
theorem B3394061 : Blo 670310 3394061 := bstep (se 3 (by rfl) ⟨636386, by rfl⟩ : syracuseStep 3394061 = 1272773) B1272773
theorem B1133075 : Blo 670310 1133075 := bstep (se 1 (by rfl) ⟨849806, by rfl⟩ : syracuseStep 1133075 = 1699613) B1699613
theorem B1362467 : Blo 670310 1362467 := bstep (se 1 (by rfl) ⟨1021850, by rfl⟩ : syracuseStep 1362467 = 2043701) B2043701
theorem B4606541 : Blo 670310 4606541 := bstep (se 3 (by rfl) ⟨863726, by rfl⟩ : syracuseStep 4606541 = 1727453) B1727453
theorem B1133203 : Blo 670310 1133203 := bstep (se 1 (by rfl) ⟨849902, by rfl⟩ : syracuseStep 1133203 = 1699805) B1699805
theorem B1133345 : Blo 670310 1133345 := bstep (se 2 (by rfl) ⟨425004, by rfl⟩ : syracuseStep 1133345 = 850009) B850009
theorem B2149229 : Blo 670310 2149229 := bstep (se 3 (by rfl) ⟨402980, by rfl⟩ : syracuseStep 2149229 = 805961) B805961
theorem B1133473 : Blo 670310 1133473 := bstep (se 2 (by rfl) ⟨425052, by rfl⟩ : syracuseStep 1133473 = 850105) B850105
theorem B1133507 : Blo 670310 1133507 := bstep (se 1 (by rfl) ⟨850130, by rfl⟩ : syracuseStep 1133507 = 1700261) B1700261
theorem B5164003 : Blo 670310 5164003 := bstep (se 1 (by rfl) ⟨3873002, by rfl⟩ : syracuseStep 5164003 = 7746005) B7746005
theorem B3230705 : Blo 670310 3230705 := bstep (se 2 (by rfl) ⟨1211514, by rfl⟩ : syracuseStep 3230705 = 2423029) B2423029
theorem B1133635 : Blo 670310 1133635 := bstep (se 1 (by rfl) ⟨850226, by rfl⟩ : syracuseStep 1133635 = 1700453) B1700453
theorem B7654499 : Blo 670310 7654499 := bstep (se 1 (by rfl) ⟨5740874, by rfl⟩ : syracuseStep 7654499 = 11481749) B11481749
theorem B1133777 : Blo 670310 1133777 := bstep (se 2 (by rfl) ⟨425166, by rfl⟩ : syracuseStep 1133777 = 850333) B850333
theorem B1821923 : Blo 670310 1821923 := bstep (se 1 (by rfl) ⟨1366442, by rfl⟩ : syracuseStep 1821923 = 2732885) B2732885
theorem B1133905 : Blo 670310 1133905 := bstep (se 2 (by rfl) ⟨425214, by rfl⟩ : syracuseStep 1133905 = 850429) B850429
theorem B1133939 : Blo 670310 1133939 := bstep (se 1 (by rfl) ⟨850454, by rfl⟩ : syracuseStep 1133939 = 1700909) B1700909
theorem B1134067 : Blo 670310 1134067 := bstep (se 1 (by rfl) ⟨850550, by rfl⟩ : syracuseStep 1134067 = 1701101) B1701101
theorem B1134209 : Blo 670310 1134209 := bstep (se 2 (by rfl) ⟨425328, by rfl⟩ : syracuseStep 1134209 = 850657) B850657
theorem B1134337 : Blo 670310 1134337 := bstep (se 2 (by rfl) ⟨425376, by rfl⟩ : syracuseStep 1134337 = 850753) B850753
theorem B1134371 : Blo 670310 1134371 := bstep (se 1 (by rfl) ⟨850778, by rfl⟩ : syracuseStep 1134371 = 1701557) B1701557
theorem B1134499 : Blo 670310 1134499 := bstep (se 1 (by rfl) ⟨850874, by rfl⟩ : syracuseStep 1134499 = 1701749) B1701749
theorem B2150317 : Blo 670310 2150317 := bstep (se 3 (by rfl) ⟨403184, by rfl⟩ : syracuseStep 2150317 = 806369) B806369
theorem B1134641 : Blo 670310 1134641 := bstep (se 2 (by rfl) ⟨425490, by rfl⟩ : syracuseStep 1134641 = 850981) B850981
theorem B2871395 : Blo 670310 2871395 := bstep (se 1 (by rfl) ⟨2153546, by rfl⟩ : syracuseStep 2871395 = 4307093) B4307093
theorem B1134769 : Blo 670310 1134769 := bstep (se 2 (by rfl) ⟨425538, by rfl⟩ : syracuseStep 1134769 = 851077) B851077
theorem B1134803 : Blo 670310 1134803 := bstep (se 1 (by rfl) ⟨851102, by rfl⟩ : syracuseStep 1134803 = 1702205) B1702205
theorem B1134931 : Blo 670310 1134931 := bstep (se 1 (by rfl) ⟨851198, by rfl⟩ : syracuseStep 1134931 = 1702397) B1702397
theorem B1135073 : Blo 670310 1135073 := bstep (se 2 (by rfl) ⟨425652, by rfl⟩ : syracuseStep 1135073 = 851305) B851305
theorem B18403811 : Blo 670310 18403811 := bstep (se 1 (by rfl) ⟨13802858, by rfl⟩ : syracuseStep 18403811 = 27605717) B27605717
theorem B1135201 : Blo 670310 1135201 := bstep (se 2 (by rfl) ⟨425700, by rfl⟩ : syracuseStep 1135201 = 851401) B851401
theorem B1135235 : Blo 670310 1135235 := bstep (se 1 (by rfl) ⟨851426, by rfl⟩ : syracuseStep 1135235 = 1702853) B1702853
theorem B1135363 : Blo 670310 1135363 := bstep (se 1 (by rfl) ⟨851522, by rfl⟩ : syracuseStep 1135363 = 1703045) B1703045
theorem B1135505 : Blo 670310 1135505 := bstep (se 2 (by rfl) ⟨425814, by rfl⟩ : syracuseStep 1135505 = 851629) B851629
theorem B3232781 : Blo 670310 3232781 := bstep (se 3 (by rfl) ⟨606146, by rfl⟩ : syracuseStep 3232781 = 1212293) B1212293
theorem B1135633 : Blo 670310 1135633 := bstep (se 2 (by rfl) ⟨425862, by rfl⟩ : syracuseStep 1135633 = 851725) B851725
theorem B1135667 : Blo 670310 1135667 := bstep (se 1 (by rfl) ⟨851750, by rfl⟩ : syracuseStep 1135667 = 1703501) B1703501
theorem B808003 : Blo 670310 808003 := bstep (se 1 (by rfl) ⟨606002, by rfl⟩ : syracuseStep 808003 = 1212005) B1212005
theorem B1135795 : Blo 670310 1135795 := bstep (se 1 (by rfl) ⟨851846, by rfl⟩ : syracuseStep 1135795 = 1703693) B1703693
theorem B2905379 : Blo 670310 2905379 := bstep (se 1 (by rfl) ⟨2179034, by rfl⟩ : syracuseStep 2905379 = 4358069) B4358069
theorem B1135937 : Blo 670310 1135937 := bstep (se 2 (by rfl) ⟨425976, by rfl⟩ : syracuseStep 1135937 = 851953) B851953
theorem B1529201 : Blo 670310 1529201 := bstep (se 2 (by rfl) ⟨573450, by rfl⟩ : syracuseStep 1529201 = 1146901) B1146901
theorem B3396977 : Blo 670310 3396977 := bstep (se 2 (by rfl) ⟨1273866, by rfl⟩ : syracuseStep 3396977 = 2547733) B2547733
theorem B1136065 : Blo 670310 1136065 := bstep (se 2 (by rfl) ⟨426024, by rfl⟩ : syracuseStep 1136065 = 852049) B852049
theorem B808387 : Blo 670310 808387 := bstep (se 1 (by rfl) ⟨606290, by rfl⟩ : syracuseStep 808387 = 1212581) B1212581
theorem B1136099 : Blo 670310 1136099 := bstep (se 1 (by rfl) ⟨852074, by rfl⟩ : syracuseStep 1136099 = 1704149) B1704149
theorem B1136227 : Blo 670310 1136227 := bstep (se 1 (by rfl) ⟨852170, by rfl⟩ : syracuseStep 1136227 = 1704341) B1704341
theorem B2152099 : Blo 670310 2152099 := bstep (se 1 (by rfl) ⟨1614074, by rfl⟩ : syracuseStep 2152099 = 3228149) B3228149
theorem B2152163 : Blo 670310 2152163 := bstep (se 1 (by rfl) ⟨1614122, by rfl⟩ : syracuseStep 2152163 = 3228245) B3228245
theorem B1136369 : Blo 670310 1136369 := bstep (se 2 (by rfl) ⟨426138, by rfl⟩ : syracuseStep 1136369 = 852277) B852277
theorem B907057 : Blo 670310 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B2152241 : Blo 670310 2152241 := bstep (se 2 (by rfl) ⟨807090, by rfl⟩ : syracuseStep 2152241 = 1614181) B1614181
theorem B1136497 : Blo 670310 1136497 := bstep (se 2 (by rfl) ⟨426186, by rfl⟩ : syracuseStep 1136497 = 852373) B852373
theorem B1136531 : Blo 670310 1136531 := bstep (se 1 (by rfl) ⟨852398, by rfl⟩ : syracuseStep 1136531 = 1704797) B1704797
theorem B1005473 : Blo 670310 1005473 := bstep (se 2 (by rfl) ⟨377052, by rfl⟩ : syracuseStep 1005473 = 754105) B754105
theorem B1005491 : Blo 670310 1005491 := bstep (se 1 (by rfl) ⟨754118, by rfl⟩ : syracuseStep 1005491 = 1508237) B1508237
theorem B1005521 : Blo 670310 1005521 := bstep (se 2 (by rfl) ⟨377070, by rfl⟩ : syracuseStep 1005521 = 754141) B754141
theorem B1005539 : Blo 670310 1005539 := bstep (se 1 (by rfl) ⟨754154, by rfl⟩ : syracuseStep 1005539 = 1508309) B1508309
theorem B1005569 : Blo 670310 1005569 := bstep (se 2 (by rfl) ⟨377088, by rfl⟩ : syracuseStep 1005569 = 754177) B754177
theorem B1005587 : Blo 670310 1005587 := bstep (se 1 (by rfl) ⟨754190, by rfl⟩ : syracuseStep 1005587 = 1508381) B1508381
theorem B1136659 : Blo 670310 1136659 := bstep (se 1 (by rfl) ⟨852494, by rfl⟩ : syracuseStep 1136659 = 1704989) B1704989
theorem B1005617 : Blo 670310 1005617 := bstep (se 2 (by rfl) ⟨377106, by rfl⟩ : syracuseStep 1005617 = 754213) B754213
theorem B1005635 : Blo 670310 1005635 := bstep (se 1 (by rfl) ⟨754226, by rfl⟩ : syracuseStep 1005635 = 1508453) B1508453
theorem B1005665 : Blo 670310 1005665 := bstep (se 2 (by rfl) ⟨377124, by rfl⟩ : syracuseStep 1005665 = 754249) B754249
theorem B4610147 : Blo 670310 4610147 := bstep (se 1 (by rfl) ⟨3457610, by rfl⟩ : syracuseStep 4610147 = 6915221) B6915221
theorem B1005683 : Blo 670310 1005683 := bstep (se 1 (by rfl) ⟨754262, by rfl⟩ : syracuseStep 1005683 = 1508525) B1508525
theorem B1005713 : Blo 670310 1005713 := bstep (se 2 (by rfl) ⟨377142, by rfl⟩ : syracuseStep 1005713 = 754285) B754285
theorem B1136801 : Blo 670310 1136801 := bstep (se 2 (by rfl) ⟨426300, by rfl⟩ : syracuseStep 1136801 = 852601) B852601
theorem B1005731 : Blo 670310 1005731 := bstep (se 1 (by rfl) ⟨754298, by rfl⟩ : syracuseStep 1005731 = 1508597) B1508597
theorem B1005761 : Blo 670310 1005761 := bstep (se 2 (by rfl) ⟨377160, by rfl⟩ : syracuseStep 1005761 = 754321) B754321
theorem B1005779 : Blo 670310 1005779 := bstep (se 1 (by rfl) ⟨754334, by rfl⟩ : syracuseStep 1005779 = 1508669) B1508669
theorem B1005809 : Blo 670310 1005809 := bstep (se 2 (by rfl) ⟨377178, by rfl⟩ : syracuseStep 1005809 = 754357) B754357
theorem B1005827 : Blo 670310 1005827 := bstep (se 1 (by rfl) ⟨754370, by rfl⟩ : syracuseStep 1005827 = 1508741) B1508741
theorem B1005857 : Blo 670310 1005857 := bstep (se 2 (by rfl) ⟨377196, by rfl⟩ : syracuseStep 1005857 = 754393) B754393
theorem B1136929 : Blo 670310 1136929 := bstep (se 2 (by rfl) ⟨426348, by rfl⟩ : syracuseStep 1136929 = 852697) B852697
theorem B2906417 : Blo 670310 2906417 := bstep (se 2 (by rfl) ⟨1089906, by rfl⟩ : syracuseStep 2906417 = 2179813) B2179813
theorem B1005875 : Blo 670310 1005875 := bstep (se 1 (by rfl) ⟨754406, by rfl⟩ : syracuseStep 1005875 = 1508813) B1508813
theorem B1136963 : Blo 670310 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B1005905 : Blo 670310 1005905 := bstep (se 2 (by rfl) ⟨377214, by rfl⟩ : syracuseStep 1005905 = 754429) B754429
theorem B1005923 : Blo 670310 1005923 := bstep (se 1 (by rfl) ⟨754442, by rfl⟩ : syracuseStep 1005923 = 1508885) B1508885
theorem B1005953 : Blo 670310 1005953 := bstep (se 2 (by rfl) ⟨377232, by rfl⟩ : syracuseStep 1005953 = 754465) B754465
theorem B1005971 : Blo 670310 1005971 := bstep (se 1 (by rfl) ⟨754478, by rfl⟩ : syracuseStep 1005971 = 1508957) B1508957
theorem B1006001 : Blo 670310 1006001 := bstep (se 2 (by rfl) ⟨377250, by rfl⟩ : syracuseStep 1006001 = 754501) B754501
theorem B1006019 : Blo 670310 1006019 := bstep (se 1 (by rfl) ⟨754514, by rfl⟩ : syracuseStep 1006019 = 1509029) B1509029
theorem B1137091 : Blo 670310 1137091 := bstep (se 1 (by rfl) ⟨852818, by rfl⟩ : syracuseStep 1137091 = 1705637) B1705637
theorem B1006049 : Blo 670310 1006049 := bstep (se 2 (by rfl) ⟨377268, by rfl⟩ : syracuseStep 1006049 = 754537) B754537
theorem B1006067 : Blo 670310 1006067 := bstep (se 1 (by rfl) ⟨754550, by rfl⟩ : syracuseStep 1006067 = 1509101) B1509101
theorem B1006097 : Blo 670310 1006097 := bstep (se 2 (by rfl) ⟨377286, by rfl⟩ : syracuseStep 1006097 = 754573) B754573
theorem B1006115 : Blo 670310 1006115 := bstep (se 1 (by rfl) ⟨754586, by rfl⟩ : syracuseStep 1006115 = 1509173) B1509173
theorem B1006145 : Blo 670310 1006145 := bstep (se 2 (by rfl) ⟨377304, by rfl⟩ : syracuseStep 1006145 = 754609) B754609
theorem B1137233 : Blo 670310 1137233 := bstep (se 2 (by rfl) ⟨426462, by rfl⟩ : syracuseStep 1137233 = 852925) B852925
theorem B1006163 : Blo 670310 1006163 := bstep (se 1 (by rfl) ⟨754622, by rfl⟩ : syracuseStep 1006163 = 1509245) B1509245
theorem B2546275 : Blo 670310 2546275 := bstep (se 1 (by rfl) ⟨1909706, by rfl⟩ : syracuseStep 2546275 = 3819413) B3819413
theorem B1006193 : Blo 670310 1006193 := bstep (se 2 (by rfl) ⟨377322, by rfl⟩ : syracuseStep 1006193 = 754645) B754645
theorem B12900977 : Blo 670310 12900977 := bstep (se 2 (by rfl) ⟨4837866, by rfl⟩ : syracuseStep 12900977 = 9675733) B9675733
theorem B1006211 : Blo 670310 1006211 := bstep (se 1 (by rfl) ⟨754658, by rfl⟩ : syracuseStep 1006211 = 1509317) B1509317
theorem B1006241 : Blo 670310 1006241 := bstep (se 2 (by rfl) ⟨377340, by rfl⟩ : syracuseStep 1006241 = 754681) B754681
theorem B1006259 : Blo 670310 1006259 := bstep (se 1 (by rfl) ⟨754694, by rfl⟩ : syracuseStep 1006259 = 1509389) B1509389
theorem B1006289 : Blo 670310 1006289 := bstep (se 2 (by rfl) ⟨377358, by rfl⟩ : syracuseStep 1006289 = 754717) B754717
theorem B1137361 : Blo 670310 1137361 := bstep (se 2 (by rfl) ⟨426510, by rfl⟩ : syracuseStep 1137361 = 853021) B853021
theorem B1006307 : Blo 670310 1006307 := bstep (se 1 (by rfl) ⟨754730, by rfl⟩ : syracuseStep 1006307 = 1509461) B1509461
theorem B1137395 : Blo 670310 1137395 := bstep (se 1 (by rfl) ⟨853046, by rfl⟩ : syracuseStep 1137395 = 1706093) B1706093
theorem B1006337 : Blo 670310 1006337 := bstep (se 2 (by rfl) ⟨377376, by rfl⟩ : syracuseStep 1006337 = 754753) B754753
theorem B1006355 : Blo 670310 1006355 := bstep (se 1 (by rfl) ⟨754766, by rfl⟩ : syracuseStep 1006355 = 1509533) B1509533
theorem B3398435 : Blo 670310 3398435 := bstep (se 1 (by rfl) ⟨2548826, by rfl⟩ : syracuseStep 3398435 = 5097653) B5097653
theorem B1006385 : Blo 670310 1006385 := bstep (se 2 (by rfl) ⟨377394, by rfl⟩ : syracuseStep 1006385 = 754789) B754789
theorem B1006403 : Blo 670310 1006403 := bstep (se 1 (by rfl) ⟨754802, by rfl⟩ : syracuseStep 1006403 = 1509605) B1509605
theorem B1006433 : Blo 670310 1006433 := bstep (se 2 (by rfl) ⟨377412, by rfl⟩ : syracuseStep 1006433 = 754825) B754825
theorem B1006451 : Blo 670310 1006451 := bstep (se 1 (by rfl) ⟨754838, by rfl⟩ : syracuseStep 1006451 = 1509677) B1509677
theorem B1137523 : Blo 670310 1137523 := bstep (se 1 (by rfl) ⟨853142, by rfl⟩ : syracuseStep 1137523 = 1706285) B1706285
theorem B1432451 : Blo 670310 1432451 := bstep (se 1 (by rfl) ⟨1074338, by rfl⟩ : syracuseStep 1432451 = 2148677) B2148677
theorem B1006481 : Blo 670310 1006481 := bstep (se 2 (by rfl) ⟨377430, by rfl⟩ : syracuseStep 1006481 = 754861) B754861
theorem B1006499 : Blo 670310 1006499 := bstep (se 1 (by rfl) ⟨754874, by rfl⟩ : syracuseStep 1006499 = 1509749) B1509749
theorem B1006529 : Blo 670310 1006529 := bstep (se 2 (by rfl) ⟨377448, by rfl⟩ : syracuseStep 1006529 = 754897) B754897
theorem B1006547 : Blo 670310 1006547 := bstep (se 1 (by rfl) ⟨754910, by rfl⟩ : syracuseStep 1006547 = 1509821) B1509821
theorem B1006577 : Blo 670310 1006577 := bstep (se 2 (by rfl) ⟨377466, by rfl⟩ : syracuseStep 1006577 = 754933) B754933
theorem B1137665 : Blo 670310 1137665 := bstep (se 2 (by rfl) ⟨426624, by rfl⟩ : syracuseStep 1137665 = 853249) B853249
theorem B1006595 : Blo 670310 1006595 := bstep (se 1 (by rfl) ⟨754946, by rfl⟩ : syracuseStep 1006595 = 1509893) B1509893
theorem B1006625 : Blo 670310 1006625 := bstep (se 2 (by rfl) ⟨377484, by rfl⟩ : syracuseStep 1006625 = 754969) B754969
theorem B1006643 : Blo 670310 1006643 := bstep (se 1 (by rfl) ⟨754982, by rfl⟩ : syracuseStep 1006643 = 1509965) B1509965
theorem B1006673 : Blo 670310 1006673 := bstep (se 2 (by rfl) ⟨377502, by rfl⟩ : syracuseStep 1006673 = 755005) B755005
theorem B1006691 : Blo 670310 1006691 := bstep (se 1 (by rfl) ⟨755018, by rfl⟩ : syracuseStep 1006691 = 1510037) B1510037
theorem B1006721 : Blo 670310 1006721 := bstep (se 2 (by rfl) ⟨377520, by rfl⟩ : syracuseStep 1006721 = 755041) B755041
theorem B1137793 : Blo 670310 1137793 := bstep (se 2 (by rfl) ⟨426672, by rfl⟩ : syracuseStep 1137793 = 853345) B853345
theorem B1006739 : Blo 670310 1006739 := bstep (se 1 (by rfl) ⟨755054, by rfl⟩ : syracuseStep 1006739 = 1510109) B1510109
theorem B1137827 : Blo 670310 1137827 := bstep (se 1 (by rfl) ⟨853370, by rfl⟩ : syracuseStep 1137827 = 1706741) B1706741
theorem B1006769 : Blo 670310 1006769 := bstep (se 2 (by rfl) ⟨377538, by rfl⟩ : syracuseStep 1006769 = 755077) B755077
theorem B1006787 : Blo 670310 1006787 := bstep (se 1 (by rfl) ⟨755090, by rfl⟩ : syracuseStep 1006787 = 1510181) B1510181
theorem B1006817 : Blo 670310 1006817 := bstep (se 2 (by rfl) ⟨377556, by rfl⟩ : syracuseStep 1006817 = 755113) B755113
theorem B1006835 : Blo 670310 1006835 := bstep (se 1 (by rfl) ⟨755126, by rfl⟩ : syracuseStep 1006835 = 1510253) B1510253
theorem B1006865 : Blo 670310 1006865 := bstep (se 2 (by rfl) ⟨377574, by rfl⟩ : syracuseStep 1006865 = 755149) B755149
theorem B1006883 : Blo 670310 1006883 := bstep (se 1 (by rfl) ⟨755162, by rfl⟩ : syracuseStep 1006883 = 1510325) B1510325
theorem B1006913 : Blo 670310 1006913 := bstep (se 2 (by rfl) ⟨377592, by rfl⟩ : syracuseStep 1006913 = 755185) B755185
theorem B1006931 : Blo 670310 1006931 := bstep (se 1 (by rfl) ⟨755198, by rfl⟩ : syracuseStep 1006931 = 1510397) B1510397
theorem B1006961 : Blo 670310 1006961 := bstep (se 2 (by rfl) ⟨377610, by rfl⟩ : syracuseStep 1006961 = 755221) B755221
theorem B1006979 : Blo 670310 1006979 := bstep (se 1 (by rfl) ⟨755234, by rfl⟩ : syracuseStep 1006979 = 1510469) B1510469
theorem B1007009 : Blo 670310 1007009 := bstep (se 2 (by rfl) ⟨377628, by rfl⟩ : syracuseStep 1007009 = 755257) B755257
theorem B1007027 : Blo 670310 1007027 := bstep (se 1 (by rfl) ⟨755270, by rfl⟩ : syracuseStep 1007027 = 1510541) B1510541
theorem B1007057 : Blo 670310 1007057 := bstep (se 2 (by rfl) ⟨377646, by rfl⟩ : syracuseStep 1007057 = 755293) B755293
theorem B1007075 : Blo 670310 1007075 := bstep (se 1 (by rfl) ⟨755306, by rfl⟩ : syracuseStep 1007075 = 1510613) B1510613
theorem B1007105 : Blo 670310 1007105 := bstep (se 2 (by rfl) ⟨377664, by rfl⟩ : syracuseStep 1007105 = 755329) B755329
theorem B1007123 : Blo 670310 1007123 := bstep (se 1 (by rfl) ⟨755342, by rfl⟩ : syracuseStep 1007123 = 1510685) B1510685
theorem B1007153 : Blo 670310 1007153 := bstep (se 2 (by rfl) ⟨377682, by rfl⟩ : syracuseStep 1007153 = 755365) B755365
theorem B1007171 : Blo 670310 1007171 := bstep (se 1 (by rfl) ⟨755378, by rfl⟩ : syracuseStep 1007171 = 1510757) B1510757
theorem B3399245 : Blo 670310 3399245 := bstep (se 3 (by rfl) ⟨637358, by rfl⟩ : syracuseStep 3399245 = 1274717) B1274717
theorem B1007201 : Blo 670310 1007201 := bstep (se 2 (by rfl) ⟨377700, by rfl⟩ : syracuseStep 1007201 = 755401) B755401
theorem B679523 : Blo 670310 679523 := bstep (se 1 (by rfl) ⟨509642, by rfl⟩ : syracuseStep 679523 = 1019285) B1019285
theorem B1007219 : Blo 670310 1007219 := bstep (se 1 (by rfl) ⟨755414, by rfl⟩ : syracuseStep 1007219 = 1510829) B1510829
theorem B1007249 : Blo 670310 1007249 := bstep (se 2 (by rfl) ⟨377718, by rfl⟩ : syracuseStep 1007249 = 755437) B755437
theorem B1007267 : Blo 670310 1007267 := bstep (se 1 (by rfl) ⟨755450, by rfl⟩ : syracuseStep 1007267 = 1510901) B1510901
theorem B2154161 : Blo 670310 2154161 := bstep (se 2 (by rfl) ⟨807810, by rfl⟩ : syracuseStep 2154161 = 1615621) B1615621
theorem B1007297 : Blo 670310 1007297 := bstep (se 2 (by rfl) ⟨377736, by rfl⟩ : syracuseStep 1007297 = 755473) B755473
theorem B2875085 : Blo 670310 2875085 := bstep (se 3 (by rfl) ⟨539078, by rfl⟩ : syracuseStep 2875085 = 1078157) B1078157
theorem B1007315 : Blo 670310 1007315 := bstep (se 1 (by rfl) ⟨755486, by rfl⟩ : syracuseStep 1007315 = 1510973) B1510973
theorem B2875121 : Blo 670310 2875121 := bstep (se 2 (by rfl) ⟨1078170, by rfl⟩ : syracuseStep 2875121 = 2156341) B2156341
theorem B1007345 : Blo 670310 1007345 := bstep (se 2 (by rfl) ⟨377754, by rfl⟩ : syracuseStep 1007345 = 755509) B755509
theorem B1007363 : Blo 670310 1007363 := bstep (se 1 (by rfl) ⟨755522, by rfl⟩ : syracuseStep 1007363 = 1511045) B1511045
theorem B1007393 : Blo 670310 1007393 := bstep (se 2 (by rfl) ⟨377772, by rfl⟩ : syracuseStep 1007393 = 755545) B755545
theorem B1007411 : Blo 670310 1007411 := bstep (se 1 (by rfl) ⟨755558, by rfl⟩ : syracuseStep 1007411 = 1511117) B1511117
theorem B1007441 : Blo 670310 1007441 := bstep (se 2 (by rfl) ⟨377790, by rfl⟩ : syracuseStep 1007441 = 755581) B755581
theorem B1007459 : Blo 670310 1007459 := bstep (se 1 (by rfl) ⟨755594, by rfl⟩ : syracuseStep 1007459 = 1511189) B1511189
theorem B1007489 : Blo 670310 1007489 := bstep (se 2 (by rfl) ⟨377808, by rfl⟩ : syracuseStep 1007489 = 755617) B755617
theorem B1007507 : Blo 670310 1007507 := bstep (se 1 (by rfl) ⟨755630, by rfl⟩ : syracuseStep 1007507 = 1511261) B1511261
theorem B1007537 : Blo 670310 1007537 := bstep (se 2 (by rfl) ⟨377826, by rfl⟩ : syracuseStep 1007537 = 755653) B755653
theorem B1007555 : Blo 670310 1007555 := bstep (se 1 (by rfl) ⟨755666, by rfl⟩ : syracuseStep 1007555 = 1511333) B1511333
theorem B1007585 : Blo 670310 1007585 := bstep (se 2 (by rfl) ⟨377844, by rfl⟩ : syracuseStep 1007585 = 755689) B755689
theorem B7757795 : Blo 670310 7757795 := bstep (se 1 (by rfl) ⟨5818346, by rfl⟩ : syracuseStep 7757795 = 11636693) B11636693
theorem B1007603 : Blo 670310 1007603 := bstep (se 1 (by rfl) ⟨755702, by rfl⟩ : syracuseStep 1007603 = 1511405) B1511405
theorem B1007633 : Blo 670310 1007633 := bstep (se 2 (by rfl) ⟨377862, by rfl⟩ : syracuseStep 1007633 = 755725) B755725
theorem B2187281 : Blo 670310 2187281 := bstep (se 2 (by rfl) ⟨820230, by rfl⟩ : syracuseStep 2187281 = 1640461) B1640461
theorem B1007651 : Blo 670310 1007651 := bstep (se 1 (by rfl) ⟨755738, by rfl⟩ : syracuseStep 1007651 = 1511477) B1511477
theorem B1007681 : Blo 670310 1007681 := bstep (se 2 (by rfl) ⟨377880, by rfl⟩ : syracuseStep 1007681 = 755761) B755761
theorem B1007699 : Blo 670310 1007699 := bstep (se 1 (by rfl) ⟨755774, by rfl⟩ : syracuseStep 1007699 = 1511549) B1511549
theorem B1007729 : Blo 670310 1007729 := bstep (se 2 (by rfl) ⟨377898, by rfl⟩ : syracuseStep 1007729 = 755797) B755797
theorem B1007747 : Blo 670310 1007747 := bstep (se 1 (by rfl) ⟨755810, by rfl⟩ : syracuseStep 1007747 = 1511621) B1511621
theorem B6480013 : Blo 670310 6480013 := bstep (se 3 (by rfl) ⟨1215002, by rfl⟩ : syracuseStep 6480013 = 2430005) B2430005
theorem B1007777 : Blo 670310 1007777 := bstep (se 2 (by rfl) ⟨377916, by rfl⟩ : syracuseStep 1007777 = 755833) B755833
theorem B1007795 : Blo 670310 1007795 := bstep (se 1 (by rfl) ⟨755846, by rfl⟩ : syracuseStep 1007795 = 1511693) B1511693
theorem B2154701 : Blo 670310 2154701 := bstep (se 3 (by rfl) ⟨404006, by rfl⟩ : syracuseStep 2154701 = 808013) B808013
theorem B1007825 : Blo 670310 1007825 := bstep (se 2 (by rfl) ⟨377934, by rfl⟩ : syracuseStep 1007825 = 755869) B755869
theorem B1007843 : Blo 670310 1007843 := bstep (se 1 (by rfl) ⟨755882, by rfl⟩ : syracuseStep 1007843 = 1511765) B1511765
theorem B1007873 : Blo 670310 1007873 := bstep (se 2 (by rfl) ⟨377952, by rfl⟩ : syracuseStep 1007873 = 755905) B755905
theorem B1007891 : Blo 670310 1007891 := bstep (se 1 (by rfl) ⟨755918, by rfl⟩ : syracuseStep 1007891 = 1511837) B1511837
theorem B1007921 : Blo 670310 1007921 := bstep (se 2 (by rfl) ⟨377970, by rfl⟩ : syracuseStep 1007921 = 755941) B755941
theorem B1007939 : Blo 670310 1007939 := bstep (se 1 (by rfl) ⟨755954, by rfl⟩ : syracuseStep 1007939 = 1511909) B1511909
theorem B2908493 : Blo 670310 2908493 := bstep (se 3 (by rfl) ⟨545342, by rfl⟩ : syracuseStep 2908493 = 1090685) B1090685
theorem B1007969 : Blo 670310 1007969 := bstep (se 2 (by rfl) ⟨377988, by rfl⟩ : syracuseStep 1007969 = 755977) B755977
theorem B5103971 : Blo 670310 5103971 := bstep (se 1 (by rfl) ⟨3827978, by rfl⟩ : syracuseStep 5103971 = 7655957) B7655957
theorem B1007987 : Blo 670310 1007987 := bstep (se 1 (by rfl) ⟨755990, by rfl⟩ : syracuseStep 1007987 = 1511981) B1511981
theorem B1008017 : Blo 670310 1008017 := bstep (se 2 (by rfl) ⟨378006, by rfl⟩ : syracuseStep 1008017 = 756013) B756013
theorem B1008035 : Blo 670310 1008035 := bstep (se 1 (by rfl) ⟨756026, by rfl⟩ : syracuseStep 1008035 = 1512053) B1512053
theorem B1008065 : Blo 670310 1008065 := bstep (se 2 (by rfl) ⟨378024, by rfl⟩ : syracuseStep 1008065 = 756049) B756049
theorem B1008083 : Blo 670310 1008083 := bstep (se 1 (by rfl) ⟨756062, by rfl⟩ : syracuseStep 1008083 = 1512125) B1512125
theorem B680419 : Blo 670310 680419 := bstep (se 1 (by rfl) ⟨510314, by rfl⟩ : syracuseStep 680419 = 1020629) B1020629
theorem B1008113 : Blo 670310 1008113 := bstep (se 2 (by rfl) ⟨378042, by rfl⟩ : syracuseStep 1008113 = 756085) B756085
theorem B1008131 : Blo 670310 1008131 := bstep (se 1 (by rfl) ⟨756098, by rfl⟩ : syracuseStep 1008131 = 1512197) B1512197
theorem B1008161 : Blo 670310 1008161 := bstep (se 2 (by rfl) ⟨378060, by rfl⟩ : syracuseStep 1008161 = 756121) B756121
theorem B4317731 : Blo 670310 4317731 := bstep (se 1 (by rfl) ⟨3238298, by rfl⟩ : syracuseStep 4317731 = 6476597) B6476597
theorem B1008179 : Blo 670310 1008179 := bstep (se 1 (by rfl) ⟨756134, by rfl⟩ : syracuseStep 1008179 = 1512269) B1512269
theorem B1008209 : Blo 670310 1008209 := bstep (se 2 (by rfl) ⟨378078, by rfl⟩ : syracuseStep 1008209 = 756157) B756157
theorem B1008227 : Blo 670310 1008227 := bstep (se 1 (by rfl) ⟨756170, by rfl⟩ : syracuseStep 1008227 = 1512341) B1512341
theorem B1008257 : Blo 670310 1008257 := bstep (se 2 (by rfl) ⟨378096, by rfl⟩ : syracuseStep 1008257 = 756193) B756193
theorem B1008275 : Blo 670310 1008275 := bstep (se 1 (by rfl) ⟨756206, by rfl⟩ : syracuseStep 1008275 = 1512413) B1512413
theorem B1008305 : Blo 670310 1008305 := bstep (se 2 (by rfl) ⟨378114, by rfl⟩ : syracuseStep 1008305 = 756229) B756229
theorem B1008323 : Blo 670310 1008323 := bstep (se 1 (by rfl) ⟨756242, by rfl⟩ : syracuseStep 1008323 = 1512485) B1512485
theorem B1008353 : Blo 670310 1008353 := bstep (se 2 (by rfl) ⟨378132, by rfl⟩ : syracuseStep 1008353 = 756265) B756265
theorem B1008371 : Blo 670310 1008371 := bstep (se 1 (by rfl) ⟨756278, by rfl⟩ : syracuseStep 1008371 = 1512557) B1512557
theorem B2450189 : Blo 670310 2450189 := bstep (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) B918821
theorem B2548493 : Blo 670310 2548493 := bstep (se 3 (by rfl) ⟨477842, by rfl⟩ : syracuseStep 2548493 = 955685) B955685
theorem B1008401 : Blo 670310 1008401 := bstep (se 2 (by rfl) ⟨378150, by rfl⟩ : syracuseStep 1008401 = 756301) B756301
theorem B1008419 : Blo 670310 1008419 := bstep (se 1 (by rfl) ⟨756314, by rfl⟩ : syracuseStep 1008419 = 1512629) B1512629
theorem B3629873 : Blo 670310 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B680755 : Blo 670310 680755 := bstep (se 1 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 680755 = 1021133) B1021133
theorem B1008449 : Blo 670310 1008449 := bstep (se 2 (by rfl) ⟨378168, by rfl⟩ : syracuseStep 1008449 = 756337) B756337
theorem B1008467 : Blo 670310 1008467 := bstep (se 1 (by rfl) ⟨756350, by rfl⟩ : syracuseStep 1008467 = 1512701) B1512701
theorem B1434467 : Blo 670310 1434467 := bstep (se 1 (by rfl) ⟨1075850, by rfl⟩ : syracuseStep 1434467 = 2151701) B2151701
theorem B1008497 : Blo 670310 1008497 := bstep (se 2 (by rfl) ⟨378186, by rfl⟩ : syracuseStep 1008497 = 756373) B756373
theorem B1008515 : Blo 670310 1008515 := bstep (se 1 (by rfl) ⟨756386, by rfl⟩ : syracuseStep 1008515 = 1512773) B1512773
theorem B1008545 : Blo 670310 1008545 := bstep (se 2 (by rfl) ⟨378204, by rfl⟩ : syracuseStep 1008545 = 756409) B756409
theorem B1729457 : Blo 670310 1729457 := bstep (se 2 (by rfl) ⟨648546, by rfl⟩ : syracuseStep 1729457 = 1297093) B1297093
theorem B1008563 : Blo 670310 1008563 := bstep (se 1 (by rfl) ⟨756422, by rfl⟩ : syracuseStep 1008563 = 1512845) B1512845
theorem B1008593 : Blo 670310 1008593 := bstep (se 2 (by rfl) ⟨378222, by rfl⟩ : syracuseStep 1008593 = 756445) B756445
theorem B1008611 : Blo 670310 1008611 := bstep (se 1 (by rfl) ⟨756458, by rfl⟩ : syracuseStep 1008611 = 1512917) B1512917
theorem B1008641 : Blo 670310 1008641 := bstep (se 2 (by rfl) ⟨378240, by rfl⟩ : syracuseStep 1008641 = 756481) B756481
theorem B1008659 : Blo 670310 1008659 := bstep (se 1 (by rfl) ⟨756494, by rfl⟩ : syracuseStep 1008659 = 1512989) B1512989
theorem B1008689 : Blo 670310 1008689 := bstep (se 2 (by rfl) ⟨378258, by rfl⟩ : syracuseStep 1008689 = 756517) B756517
theorem B1008707 : Blo 670310 1008707 := bstep (se 1 (by rfl) ⟨756530, by rfl⟩ : syracuseStep 1008707 = 1513061) B1513061
theorem B1008737 : Blo 670310 1008737 := bstep (se 2 (by rfl) ⟨378276, by rfl⟩ : syracuseStep 1008737 = 756553) B756553
theorem B1008755 : Blo 670310 1008755 := bstep (se 1 (by rfl) ⟨756566, by rfl⟩ : syracuseStep 1008755 = 1513133) B1513133
theorem B1008785 : Blo 670310 1008785 := bstep (se 2 (by rfl) ⟨378294, by rfl⟩ : syracuseStep 1008785 = 756589) B756589
theorem B1008803 : Blo 670310 1008803 := bstep (se 1 (by rfl) ⟨756602, by rfl⟩ : syracuseStep 1008803 = 1513205) B1513205
theorem B1008833 : Blo 670310 1008833 := bstep (se 2 (by rfl) ⟨378312, by rfl⟩ : syracuseStep 1008833 = 756625) B756625
theorem B3826885 : Blo 670310 3826885 := bstep (se 4 (by rfl) ⟨358770, by rfl⟩ : syracuseStep 3826885 = 717541) B717541
theorem B1008851 : Blo 670310 1008851 := bstep (se 1 (by rfl) ⟨756638, by rfl⟩ : syracuseStep 1008851 = 1513277) B1513277
theorem B1008881 : Blo 670310 1008881 := bstep (se 2 (by rfl) ⟨378330, by rfl⟩ : syracuseStep 1008881 = 756661) B756661
theorem B1008899 : Blo 670310 1008899 := bstep (se 1 (by rfl) ⟨756674, by rfl⟩ : syracuseStep 1008899 = 1513349) B1513349
theorem B1008929 : Blo 670310 1008929 := bstep (se 2 (by rfl) ⟨378348, by rfl⟩ : syracuseStep 1008929 = 756697) B756697
theorem B1074467 : Blo 670310 1074467 := bstep (se 1 (by rfl) ⟨805850, by rfl⟩ : syracuseStep 1074467 = 1611701) B1611701
theorem B1008947 : Blo 670310 1008947 := bstep (se 1 (by rfl) ⟨756710, by rfl⟩ : syracuseStep 1008947 = 1513421) B1513421
theorem B1008977 : Blo 670310 1008977 := bstep (se 2 (by rfl) ⟨378366, by rfl⟩ : syracuseStep 1008977 = 756733) B756733
theorem B1008995 : Blo 670310 1008995 := bstep (se 1 (by rfl) ⟨756746, by rfl⟩ : syracuseStep 1008995 = 1513493) B1513493
theorem B1009025 : Blo 670310 1009025 := bstep (se 2 (by rfl) ⟨378384, by rfl⟩ : syracuseStep 1009025 = 756769) B756769
theorem B1009043 : Blo 670310 1009043 := bstep (se 1 (by rfl) ⟨756782, by rfl⟩ : syracuseStep 1009043 = 1513565) B1513565
theorem B1009073 : Blo 670310 1009073 := bstep (se 2 (by rfl) ⟨378402, by rfl⟩ : syracuseStep 1009073 = 756805) B756805
theorem B1009091 : Blo 670310 1009091 := bstep (se 1 (by rfl) ⟨756818, by rfl⟩ : syracuseStep 1009091 = 1513637) B1513637
theorem B1697233 : Blo 670310 1697233 := bstep (se 2 (by rfl) ⟨636462, by rfl⟩ : syracuseStep 1697233 = 1272925) B1272925
theorem B1009121 : Blo 670310 1009121 := bstep (se 2 (by rfl) ⟨378420, by rfl⟩ : syracuseStep 1009121 = 756841) B756841
theorem B1009139 : Blo 670310 1009139 := bstep (se 1 (by rfl) ⟨756854, by rfl⟩ : syracuseStep 1009139 = 1513709) B1513709
theorem B1009169 : Blo 670310 1009169 := bstep (se 2 (by rfl) ⟨378438, by rfl⟩ : syracuseStep 1009169 = 756877) B756877
theorem B1009187 : Blo 670310 1009187 := bstep (se 1 (by rfl) ⟨756890, by rfl⟩ : syracuseStep 1009187 = 1513781) B1513781
theorem B1009217 : Blo 670310 1009217 := bstep (se 2 (by rfl) ⟨378456, by rfl⟩ : syracuseStep 1009217 = 756913) B756913
theorem B1009235 : Blo 670310 1009235 := bstep (se 1 (by rfl) ⟨756926, by rfl⟩ : syracuseStep 1009235 = 1513853) B1513853
theorem B1009265 : Blo 670310 1009265 := bstep (se 2 (by rfl) ⟨378474, by rfl⟩ : syracuseStep 1009265 = 756949) B756949
theorem B1009283 : Blo 670310 1009283 := bstep (se 1 (by rfl) ⟨756962, by rfl⟩ : syracuseStep 1009283 = 1513925) B1513925
theorem B910993 : Blo 670310 910993 := bstep (se 2 (by rfl) ⟨341622, by rfl⟩ : syracuseStep 910993 = 683245) B683245
theorem B1009313 : Blo 670310 1009313 := bstep (se 2 (by rfl) ⟨378492, by rfl⟩ : syracuseStep 1009313 = 756985) B756985
theorem B1009331 : Blo 670310 1009331 := bstep (se 1 (by rfl) ⟨756998, by rfl⟩ : syracuseStep 1009331 = 1513997) B1513997
theorem B5531333 : Blo 670310 5531333 := bstep (se 4 (by rfl) ⟨518562, by rfl⟩ : syracuseStep 5531333 = 1037125) B1037125
theorem B1009361 : Blo 670310 1009361 := bstep (se 2 (by rfl) ⟨378510, by rfl⟩ : syracuseStep 1009361 = 757021) B757021
theorem B1697507 : Blo 670310 1697507 := bstep (se 1 (by rfl) ⟨1273130, by rfl⟩ : syracuseStep 1697507 = 2546261) B2546261
theorem B1009379 : Blo 670310 1009379 := bstep (se 1 (by rfl) ⟨757034, by rfl⟩ : syracuseStep 1009379 = 1514069) B1514069
theorem B1009409 : Blo 670310 1009409 := bstep (se 2 (by rfl) ⟨378528, by rfl⟩ : syracuseStep 1009409 = 757057) B757057
theorem B1009427 : Blo 670310 1009427 := bstep (se 1 (by rfl) ⟨757070, by rfl⟩ : syracuseStep 1009427 = 1514141) B1514141
theorem B1074979 : Blo 670310 1074979 := bstep (se 1 (by rfl) ⟨806234, by rfl⟩ : syracuseStep 1074979 = 1612469) B1612469
theorem B1009457 : Blo 670310 1009457 := bstep (se 2 (by rfl) ⟨378546, by rfl⟩ : syracuseStep 1009457 = 757093) B757093
theorem B1009475 : Blo 670310 1009475 := bstep (se 1 (by rfl) ⟨757106, by rfl⟩ : syracuseStep 1009475 = 1514213) B1514213
theorem B1075025 : Blo 670310 1075025 := bstep (se 2 (by rfl) ⟨403134, by rfl⟩ : syracuseStep 1075025 = 806269) B806269
theorem B1009505 : Blo 670310 1009505 := bstep (se 2 (by rfl) ⟨378564, by rfl⟩ : syracuseStep 1009505 = 757129) B757129
theorem B1009523 : Blo 670310 1009523 := bstep (se 1 (by rfl) ⟨757142, by rfl⟩ : syracuseStep 1009523 = 1514285) B1514285
theorem B1009553 : Blo 670310 1009553 := bstep (se 2 (by rfl) ⟨378582, by rfl⟩ : syracuseStep 1009553 = 757165) B757165
theorem B1697699 : Blo 670310 1697699 := bstep (se 1 (by rfl) ⟨1273274, by rfl⟩ : syracuseStep 1697699 = 2546549) B2546549
theorem B1009571 : Blo 670310 1009571 := bstep (se 1 (by rfl) ⟨757178, by rfl⟩ : syracuseStep 1009571 = 1514357) B1514357
theorem B1009601 : Blo 670310 1009601 := bstep (se 2 (by rfl) ⟨378600, by rfl⟩ : syracuseStep 1009601 = 757201) B757201
theorem B1009619 : Blo 670310 1009619 := bstep (se 1 (by rfl) ⟨757214, by rfl⟩ : syracuseStep 1009619 = 1514429) B1514429
theorem B1009649 : Blo 670310 1009649 := bstep (se 2 (by rfl) ⟨378618, by rfl⟩ : syracuseStep 1009649 = 757237) B757237
theorem B1009667 : Blo 670310 1009667 := bstep (se 1 (by rfl) ⟨757250, by rfl⟩ : syracuseStep 1009667 = 1514501) B1514501
theorem B1009697 : Blo 670310 1009697 := bstep (se 2 (by rfl) ⟨378636, by rfl⟩ : syracuseStep 1009697 = 757273) B757273
theorem B1009715 : Blo 670310 1009715 := bstep (se 1 (by rfl) ⟨757286, by rfl⟩ : syracuseStep 1009715 = 1514573) B1514573
theorem B1435715 : Blo 670310 1435715 := bstep (se 1 (by rfl) ⟨1076786, by rfl⟩ : syracuseStep 1435715 = 2153573) B2153573
theorem B1009745 : Blo 670310 1009745 := bstep (se 2 (by rfl) ⟨378654, by rfl⟩ : syracuseStep 1009745 = 757309) B757309
theorem B1009763 : Blo 670310 1009763 := bstep (se 1 (by rfl) ⟨757322, by rfl⟩ : syracuseStep 1009763 = 1514645) B1514645
theorem B1009793 : Blo 670310 1009793 := bstep (se 2 (by rfl) ⟨378672, by rfl⟩ : syracuseStep 1009793 = 757345) B757345
theorem B1009811 : Blo 670310 1009811 := bstep (se 1 (by rfl) ⟨757358, by rfl⟩ : syracuseStep 1009811 = 1514717) B1514717
theorem B1009841 : Blo 670310 1009841 := bstep (se 2 (by rfl) ⟨378690, by rfl⟩ : syracuseStep 1009841 = 757381) B757381
theorem B1009859 : Blo 670310 1009859 := bstep (se 1 (by rfl) ⟨757394, by rfl⟩ : syracuseStep 1009859 = 1514789) B1514789
theorem B1009889 : Blo 670310 1009889 := bstep (se 2 (by rfl) ⟨378708, by rfl⟩ : syracuseStep 1009889 = 757417) B757417
theorem B1009907 : Blo 670310 1009907 := bstep (se 1 (by rfl) ⟨757430, by rfl⟩ : syracuseStep 1009907 = 1514861) B1514861
theorem B1009937 : Blo 670310 1009937 := bstep (se 2 (by rfl) ⟨378726, by rfl⟩ : syracuseStep 1009937 = 757453) B757453
theorem B1009955 : Blo 670310 1009955 := bstep (se 1 (by rfl) ⟨757466, by rfl⟩ : syracuseStep 1009955 = 1514933) B1514933
theorem B1009985 : Blo 670310 1009985 := bstep (se 2 (by rfl) ⟨378744, by rfl⟩ : syracuseStep 1009985 = 757489) B757489
theorem B1010003 : Blo 670310 1010003 := bstep (se 1 (by rfl) ⟨757502, by rfl⟩ : syracuseStep 1010003 = 1515005) B1515005
theorem B1010033 : Blo 670310 1010033 := bstep (se 2 (by rfl) ⟨378762, by rfl⟩ : syracuseStep 1010033 = 757525) B757525
theorem B1010051 : Blo 670310 1010051 := bstep (se 1 (by rfl) ⟨757538, by rfl⟩ : syracuseStep 1010051 = 1515077) B1515077
theorem B1010081 : Blo 670310 1010081 := bstep (se 2 (by rfl) ⟨378780, by rfl⟩ : syracuseStep 1010081 = 757561) B757561
theorem B3402161 : Blo 670310 3402161 := bstep (se 2 (by rfl) ⟨1275810, by rfl⟩ : syracuseStep 3402161 = 2551621) B2551621
theorem B1010099 : Blo 670310 1010099 := bstep (se 1 (by rfl) ⟨757574, by rfl⟩ : syracuseStep 1010099 = 1515149) B1515149
theorem B1010129 : Blo 670310 1010129 := bstep (se 2 (by rfl) ⟨378798, by rfl⟩ : syracuseStep 1010129 = 757597) B757597
theorem B1010147 : Blo 670310 1010147 := bstep (se 1 (by rfl) ⟨757610, by rfl⟩ : syracuseStep 1010147 = 1515221) B1515221
theorem B1075697 : Blo 670310 1075697 := bstep (se 2 (by rfl) ⟨403386, by rfl⟩ : syracuseStep 1075697 = 806773) B806773
theorem B1010177 : Blo 670310 1010177 := bstep (se 2 (by rfl) ⟨378816, by rfl⟩ : syracuseStep 1010177 = 757633) B757633
theorem B1010195 : Blo 670310 1010195 := bstep (se 1 (by rfl) ⟨757646, by rfl⟩ : syracuseStep 1010195 = 1515293) B1515293
theorem B1010225 : Blo 670310 1010225 := bstep (se 2 (by rfl) ⟨378834, by rfl⟩ : syracuseStep 1010225 = 757669) B757669
theorem B1010243 : Blo 670310 1010243 := bstep (se 1 (by rfl) ⟨757682, by rfl⟩ : syracuseStep 1010243 = 1515365) B1515365
theorem B1010273 : Blo 670310 1010273 := bstep (se 2 (by rfl) ⟨378852, by rfl⟩ : syracuseStep 1010273 = 757705) B757705
theorem B1010291 : Blo 670310 1010291 := bstep (se 1 (by rfl) ⟨757718, by rfl⟩ : syracuseStep 1010291 = 1515437) B1515437
theorem B1436305 : Blo 670310 1436305 := bstep (se 2 (by rfl) ⟨538614, by rfl⟩ : syracuseStep 1436305 = 1077229) B1077229
theorem B1010321 : Blo 670310 1010321 := bstep (se 2 (by rfl) ⟨378870, by rfl⟩ : syracuseStep 1010321 = 757741) B757741
theorem B1010339 : Blo 670310 1010339 := bstep (se 1 (by rfl) ⟨757754, by rfl⟩ : syracuseStep 1010339 = 1515509) B1515509
theorem B1010369 : Blo 670310 1010369 := bstep (se 2 (by rfl) ⟨378888, by rfl⟩ : syracuseStep 1010369 = 757777) B757777
theorem B1010387 : Blo 670310 1010387 := bstep (se 1 (by rfl) ⟨757790, by rfl⟩ : syracuseStep 1010387 = 1515581) B1515581
theorem B1010417 : Blo 670310 1010417 := bstep (se 2 (by rfl) ⟨378906, by rfl⟩ : syracuseStep 1010417 = 757813) B757813
theorem B1010435 : Blo 670310 1010435 := bstep (se 1 (by rfl) ⟨757826, by rfl⟩ : syracuseStep 1010435 = 1515653) B1515653
theorem B1010465 : Blo 670310 1010465 := bstep (se 2 (by rfl) ⟨378924, by rfl⟩ : syracuseStep 1010465 = 757849) B757849
theorem B1010483 : Blo 670310 1010483 := bstep (se 1 (by rfl) ⟨757862, by rfl⟩ : syracuseStep 1010483 = 1515725) B1515725
theorem B11627317 : Blo 670310 11627317 := bstep (se 5 (by rfl) ⟨545030, by rfl⟩ : syracuseStep 11627317 = 1090061) B1090061
theorem B1698641 : Blo 670310 1698641 := bstep (se 2 (by rfl) ⟨636990, by rfl⟩ : syracuseStep 1698641 = 1273981) B1273981
theorem B1010513 : Blo 670310 1010513 := bstep (se 2 (by rfl) ⟨378942, by rfl⟩ : syracuseStep 1010513 = 757885) B757885
theorem B4844387 : Blo 670310 4844387 := bstep (se 1 (by rfl) ⟨3633290, by rfl⟩ : syracuseStep 4844387 = 7266581) B7266581
theorem B1010531 : Blo 670310 1010531 := bstep (se 1 (by rfl) ⟨757898, by rfl⟩ : syracuseStep 1010531 = 1515797) B1515797
theorem B1010561 : Blo 670310 1010561 := bstep (se 2 (by rfl) ⟨378960, by rfl⟩ : syracuseStep 1010561 = 757921) B757921
theorem B1698691 : Blo 670310 1698691 := bstep (se 1 (by rfl) ⟨1274018, by rfl⟩ : syracuseStep 1698691 = 2548037) B2548037
theorem B1010579 : Blo 670310 1010579 := bstep (se 1 (by rfl) ⟨757934, by rfl⟩ : syracuseStep 1010579 = 1515869) B1515869
theorem B1010609 : Blo 670310 1010609 := bstep (se 2 (by rfl) ⟨378978, by rfl⟩ : syracuseStep 1010609 = 757957) B757957
theorem B1010627 : Blo 670310 1010627 := bstep (se 1 (by rfl) ⟨757970, by rfl⟩ : syracuseStep 1010627 = 1515941) B1515941
theorem B1010657 : Blo 670310 1010657 := bstep (se 2 (by rfl) ⟨378996, by rfl⟩ : syracuseStep 1010657 = 757993) B757993
theorem B1076209 : Blo 670310 1076209 := bstep (se 2 (by rfl) ⟨403578, by rfl⟩ : syracuseStep 1076209 = 807157) B807157
theorem B1010675 : Blo 670310 1010675 := bstep (se 1 (by rfl) ⟨758006, by rfl⟩ : syracuseStep 1010675 = 1516013) B1516013
theorem B1698833 : Blo 670310 1698833 := bstep (se 2 (by rfl) ⟨637062, by rfl⟩ : syracuseStep 1698833 = 1274125) B1274125
theorem B1010705 : Blo 670310 1010705 := bstep (se 2 (by rfl) ⟨379014, by rfl⟩ : syracuseStep 1010705 = 758029) B758029
theorem B15494165 : Blo 670310 15494165 := bstep (se 6 (by rfl) ⟨363144, by rfl⟩ : syracuseStep 15494165 = 726289) B726289
theorem B1010723 : Blo 670310 1010723 := bstep (se 1 (by rfl) ⟨758042, by rfl⟩ : syracuseStep 1010723 = 1516085) B1516085
theorem B1010753 : Blo 670310 1010753 := bstep (se 2 (by rfl) ⟨379032, by rfl⟩ : syracuseStep 1010753 = 758065) B758065
theorem B1010771 : Blo 670310 1010771 := bstep (se 1 (by rfl) ⟨758078, by rfl⟩ : syracuseStep 1010771 = 1516157) B1516157
theorem B5729393 : Blo 670310 5729393 := bstep (se 2 (by rfl) ⟨2148522, by rfl⟩ : syracuseStep 5729393 = 4297045) B4297045
theorem B1010801 : Blo 670310 1010801 := bstep (se 2 (by rfl) ⟨379050, by rfl⟩ : syracuseStep 1010801 = 758101) B758101
theorem B1010819 : Blo 670310 1010819 := bstep (se 1 (by rfl) ⟨758114, by rfl⟩ : syracuseStep 1010819 = 1516229) B1516229
theorem B3828869 : Blo 670310 3828869 := bstep (se 4 (by rfl) ⟨358956, by rfl⟩ : syracuseStep 3828869 = 717913) B717913
theorem B1010849 : Blo 670310 1010849 := bstep (se 2 (by rfl) ⟨379068, by rfl⟩ : syracuseStep 1010849 = 758137) B758137
theorem B1273009 : Blo 670310 1273009 := bstep (se 2 (by rfl) ⟨477378, by rfl⟩ : syracuseStep 1273009 = 954757) B954757
theorem B1010867 : Blo 670310 1010867 := bstep (se 1 (by rfl) ⟨758150, by rfl⟩ : syracuseStep 1010867 = 1516301) B1516301
theorem B1010897 : Blo 670310 1010897 := bstep (se 2 (by rfl) ⟨379086, by rfl⟩ : syracuseStep 1010897 = 758173) B758173
theorem B1010915 : Blo 670310 1010915 := bstep (se 1 (by rfl) ⟨758186, by rfl⟩ : syracuseStep 1010915 = 1516373) B1516373
theorem B1010945 : Blo 670310 1010945 := bstep (se 2 (by rfl) ⟨379104, by rfl⟩ : syracuseStep 1010945 = 758209) B758209
theorem B1010963 : Blo 670310 1010963 := bstep (se 1 (by rfl) ⟨758222, by rfl⟩ : syracuseStep 1010963 = 1516445) B1516445
theorem B1010993 : Blo 670310 1010993 := bstep (se 2 (by rfl) ⟨379122, by rfl⟩ : syracuseStep 1010993 = 758245) B758245
theorem B1011011 : Blo 670310 1011011 := bstep (se 1 (by rfl) ⟨758258, by rfl⟩ : syracuseStep 1011011 = 1516517) B1516517
theorem B1011041 : Blo 670310 1011041 := bstep (se 2 (by rfl) ⟨379140, by rfl⟩ : syracuseStep 1011041 = 758281) B758281
theorem B1011059 : Blo 670310 1011059 := bstep (se 1 (by rfl) ⟨758294, by rfl⟩ : syracuseStep 1011059 = 1516589) B1516589
theorem B1011089 : Blo 670310 1011089 := bstep (se 2 (by rfl) ⟨379158, by rfl⟩ : syracuseStep 1011089 = 758317) B758317
theorem B1011107 : Blo 670310 1011107 := bstep (se 1 (by rfl) ⟨758330, by rfl⟩ : syracuseStep 1011107 = 1516661) B1516661
theorem B1011137 : Blo 670310 1011137 := bstep (se 2 (by rfl) ⟨379176, by rfl⟩ : syracuseStep 1011137 = 758353) B758353
theorem B1535441 : Blo 670310 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B1011155 : Blo 670310 1011155 := bstep (se 1 (by rfl) ⟨758366, by rfl⟩ : syracuseStep 1011155 = 1516733) B1516733
theorem B1011185 : Blo 670310 1011185 := bstep (se 2 (by rfl) ⟨379194, by rfl⟩ : syracuseStep 1011185 = 758389) B758389
theorem B1011203 : Blo 670310 1011203 := bstep (se 1 (by rfl) ⟨758402, by rfl⟩ : syracuseStep 1011203 = 1516805) B1516805
theorem B1011233 : Blo 670310 1011233 := bstep (se 2 (by rfl) ⟨379212, by rfl⟩ : syracuseStep 1011233 = 758425) B758425
theorem B1011251 : Blo 670310 1011251 := bstep (se 1 (by rfl) ⟨758438, by rfl⟩ : syracuseStep 1011251 = 1516877) B1516877
theorem B1273411 : Blo 670310 1273411 := bstep (se 1 (by rfl) ⟨955058, by rfl⟩ : syracuseStep 1273411 = 1910117) B1910117
theorem B1011281 : Blo 670310 1011281 := bstep (se 2 (by rfl) ⟨379230, by rfl⟩ : syracuseStep 1011281 = 758461) B758461
theorem B1011299 : Blo 670310 1011299 := bstep (se 1 (by rfl) ⟨758474, by rfl⟩ : syracuseStep 1011299 = 1516949) B1516949
theorem B1273457 : Blo 670310 1273457 := bstep (se 2 (by rfl) ⟨477546, by rfl⟩ : syracuseStep 1273457 = 955093) B955093
theorem B2551409 : Blo 670310 2551409 := bstep (se 2 (by rfl) ⟨956778, by rfl⟩ : syracuseStep 2551409 = 1913557) B1913557
theorem B1011329 : Blo 670310 1011329 := bstep (se 2 (by rfl) ⟨379248, by rfl⟩ : syracuseStep 1011329 = 758497) B758497
theorem B1011347 : Blo 670310 1011347 := bstep (se 1 (by rfl) ⟨758510, by rfl⟩ : syracuseStep 1011347 = 1517021) B1517021
theorem B1961635 : Blo 670310 1961635 := bstep (se 1 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 1961635 = 2942453) B2942453
theorem B1011377 : Blo 670310 1011377 := bstep (se 2 (by rfl) ⟨379266, by rfl⟩ : syracuseStep 1011377 = 758533) B758533
theorem B1011395 : Blo 670310 1011395 := bstep (se 1 (by rfl) ⟨758546, by rfl⟩ : syracuseStep 1011395 = 1517093) B1517093
theorem B2158289 : Blo 670310 2158289 := bstep (se 2 (by rfl) ⟨809358, by rfl⟩ : syracuseStep 2158289 = 1618717) B1618717
theorem B1011425 : Blo 670310 1011425 := bstep (se 2 (by rfl) ⟨379284, by rfl⟩ : syracuseStep 1011425 = 758569) B758569
theorem B1011443 : Blo 670310 1011443 := bstep (se 1 (by rfl) ⟨758582, by rfl⟩ : syracuseStep 1011443 = 1517165) B1517165
theorem B3403619 : Blo 670310 3403619 := bstep (se 1 (by rfl) ⟨2552714, by rfl⟩ : syracuseStep 3403619 = 5105429) B5105429
theorem B8613773 : Blo 670310 8613773 := bstep (se 3 (by rfl) ⟨1615082, by rfl⟩ : syracuseStep 8613773 = 3230165) B3230165
theorem B1273745 : Blo 670310 1273745 := bstep (se 2 (by rfl) ⟨477654, by rfl⟩ : syracuseStep 1273745 = 955309) B955309
theorem B2879459 : Blo 670310 2879459 := bstep (se 1 (by rfl) ⟨2159594, by rfl⟩ : syracuseStep 2879459 = 4319189) B4319189
theorem B1699825 : Blo 670310 1699825 := bstep (se 2 (by rfl) ⟨637434, by rfl⟩ : syracuseStep 1699825 = 1274869) B1274869
theorem B14544917 : Blo 670310 14544917 := bstep (se 6 (by rfl) ⟨340896, by rfl⟩ : syracuseStep 14544917 = 681793) B681793
theorem B1077491 : Blo 670310 1077491 := bstep (se 1 (by rfl) ⟨808118, by rfl⟩ : syracuseStep 1077491 = 1616237) B1616237
theorem B717059 : Blo 670310 717059 := bstep (se 1 (by rfl) ⟨537794, by rfl⟩ : syracuseStep 717059 = 1075589) B1075589
theorem B1700099 : Blo 670310 1700099 := bstep (se 1 (by rfl) ⟨1275074, by rfl⟩ : syracuseStep 1700099 = 2550149) B2550149
theorem B1077619 : Blo 670310 1077619 := bstep (se 1 (by rfl) ⟨808214, by rfl⟩ : syracuseStep 1077619 = 1616429) B1616429
theorem B2158979 : Blo 670310 2158979 := bstep (se 1 (by rfl) ⟨1619234, by rfl⟩ : syracuseStep 2158979 = 3238469) B3238469
theorem B1700291 : Blo 670310 1700291 := bstep (se 1 (by rfl) ⟨1275218, by rfl⟩ : syracuseStep 1700291 = 2550437) B2550437
theorem B1077761 : Blo 670310 1077761 := bstep (se 2 (by rfl) ⟨404160, by rfl⟩ : syracuseStep 1077761 = 808321) B808321
theorem B1274467 : Blo 670310 1274467 := bstep (se 1 (by rfl) ⟨955850, by rfl⟩ : syracuseStep 1274467 = 1911701) B1911701
theorem B1208963 : Blo 670310 1208963 := bstep (se 1 (by rfl) ⟨906722, by rfl⟩ : syracuseStep 1208963 = 1813445) B1813445
theorem B3404429 : Blo 670310 3404429 := bstep (se 3 (by rfl) ⟨638330, by rfl⟩ : syracuseStep 3404429 = 1276661) B1276661
theorem B1078049 : Blo 670310 1078049 := bstep (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) B808537
theorem B848819 : Blo 670310 848819 := bstep (se 1 (by rfl) ⟨636614, by rfl⟩ : syracuseStep 848819 = 1273229) B1273229
theorem B1274915 : Blo 670310 1274915 := bstep (se 1 (by rfl) ⟨956186, by rfl⟩ : syracuseStep 1274915 = 1912373) B1912373
theorem B2552867 : Blo 670310 2552867 := bstep (se 1 (by rfl) ⟨1914650, by rfl⟩ : syracuseStep 2552867 = 3829301) B3829301
theorem B1275203 : Blo 670310 1275203 := bstep (se 1 (by rfl) ⟨956402, by rfl⟩ : syracuseStep 1275203 = 1912805) B1912805
theorem B1701233 : Blo 670310 1701233 := bstep (se 2 (by rfl) ⟨637962, by rfl⟩ : syracuseStep 1701233 = 1275925) B1275925
theorem B1701283 : Blo 670310 1701283 := bstep (se 1 (by rfl) ⟨1275962, by rfl⟩ : syracuseStep 1701283 = 2551925) B2551925
theorem B4093411 : Blo 670310 4093411 := bstep (se 1 (by rfl) ⟨3070058, by rfl⟩ : syracuseStep 4093411 = 6140117) B6140117
theorem B1701425 : Blo 670310 1701425 := bstep (se 2 (by rfl) ⟨638034, by rfl⟩ : syracuseStep 1701425 = 1276069) B1276069
theorem B1078849 : Blo 670310 1078849 := bstep (se 2 (by rfl) ⟨404568, by rfl⟩ : syracuseStep 1078849 = 809137) B809137
theorem B5109317 : Blo 670310 5109317 := bstep (se 4 (by rfl) ⟨478998, by rfl⟩ : syracuseStep 5109317 = 957997) B957997
theorem B849523 : Blo 670310 849523 := bstep (se 1 (by rfl) ⟨637142, by rfl⟩ : syracuseStep 849523 = 1274285) B1274285
theorem B1537667 : Blo 670310 1537667 := bstep (se 1 (by rfl) ⟨1153250, by rfl⟩ : syracuseStep 1537667 = 2306501) B2306501
theorem B849619 : Blo 670310 849619 := bstep (se 1 (by rfl) ⟨637214, by rfl⟩ : syracuseStep 849619 = 1274429) B1274429
theorem B1439491 : Blo 670310 1439491 := bstep (se 1 (by rfl) ⟨1079618, by rfl⟩ : syracuseStep 1439491 = 2159237) B2159237
theorem B1210211 : Blo 670310 1210211 := bstep (se 1 (by rfl) ⟨907658, by rfl⟩ : syracuseStep 1210211 = 1815317) B1815317
theorem B2553869 : Blo 670310 2553869 := bstep (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) B957701
theorem B850115 : Blo 670310 850115 := bstep (se 1 (by rfl) ⟨637586, by rfl⟩ : syracuseStep 850115 = 1275173) B1275173
theorem B8190179 : Blo 670310 8190179 := bstep (se 1 (by rfl) ⟨6142634, by rfl⟩ : syracuseStep 8190179 = 12285269) B12285269
theorem B719075 : Blo 670310 719075 := bstep (se 1 (by rfl) ⟨539306, by rfl⟩ : syracuseStep 719075 = 1078613) B1078613
theorem B1276145 : Blo 670310 1276145 := bstep (se 2 (by rfl) ⟨478554, by rfl⟩ : syracuseStep 1276145 = 957109) B957109
theorem B1702417 : Blo 670310 1702417 := bstep (se 2 (by rfl) ⟨638406, by rfl⟩ : syracuseStep 1702417 = 1276813) B1276813
theorem B1080067 : Blo 670310 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B1702691 : Blo 670310 1702691 := bstep (se 1 (by rfl) ⟨1277018, by rfl⟩ : syracuseStep 1702691 = 2554037) B2554037
theorem B1211249 : Blo 670310 1211249 := bstep (se 2 (by rfl) ⟨454218, by rfl⟩ : syracuseStep 1211249 = 908437) B908437
theorem B850819 : Blo 670310 850819 := bstep (se 1 (by rfl) ⟨638114, by rfl⟩ : syracuseStep 850819 = 1276229) B1276229
theorem B3832717 : Blo 670310 3832717 := bstep (se 3 (by rfl) ⟨718634, by rfl⟩ : syracuseStep 3832717 = 1437269) B1437269
theorem B850915 : Blo 670310 850915 := bstep (se 1 (by rfl) ⟨638186, by rfl⟩ : syracuseStep 850915 = 1276373) B1276373
theorem B1702883 : Blo 670310 1702883 := bstep (se 1 (by rfl) ⟨1277162, by rfl⟩ : syracuseStep 1702883 = 2554325) B2554325
theorem B3505123 : Blo 670310 3505123 := bstep (se 1 (by rfl) ⟨2628842, by rfl⟩ : syracuseStep 3505123 = 5257685) B5257685
theorem B1277041 : Blo 670310 1277041 := bstep (se 2 (by rfl) ⟨478890, by rfl⟩ : syracuseStep 1277041 = 957781) B957781
theorem B720019 : Blo 670310 720019 := bstep (se 1 (by rfl) ⟨540014, by rfl⟩ : syracuseStep 720019 = 1080029) B1080029
theorem B6552845 : Blo 670310 6552845 := bstep (se 3 (by rfl) ⟨1228658, by rfl⟩ : syracuseStep 6552845 = 2457317) B2457317
theorem B1277201 : Blo 670310 1277201 := bstep (se 2 (by rfl) ⟨478950, by rfl⟩ : syracuseStep 1277201 = 957901) B957901
theorem B2424113 : Blo 670310 2424113 := bstep (se 2 (by rfl) ⟨909042, by rfl⟩ : syracuseStep 2424113 = 1818085) B1818085
theorem B6913349 : Blo 670310 6913349 := bstep (se 4 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 6913349 = 1296253) B1296253
theorem B851411 : Blo 670310 851411 := bstep (se 1 (by rfl) ⟨638558, by rfl⟩ : syracuseStep 851411 = 1277117) B1277117
theorem B3407345 : Blo 670310 3407345 := bstep (se 2 (by rfl) ⟨1277754, by rfl⟩ : syracuseStep 3407345 = 2555509) B2555509
theorem B1277603 : Blo 670310 1277603 := bstep (se 1 (by rfl) ⟨958202, by rfl⟩ : syracuseStep 1277603 = 1916405) B1916405
theorem B1146737 : Blo 670310 1146737 := bstep (se 2 (by rfl) ⟨430026, by rfl⟩ : syracuseStep 1146737 = 860053) B860053
theorem B2719601 : Blo 670310 2719601 := bstep (se 2 (by rfl) ⟨1019850, by rfl⟩ : syracuseStep 2719601 = 2039701) B2039701
theorem B1703825 : Blo 670310 1703825 := bstep (se 2 (by rfl) ⟨638934, by rfl⟩ : syracuseStep 1703825 = 1277869) B1277869
theorem B1703875 : Blo 670310 1703875 := bstep (se 1 (by rfl) ⟨1277906, by rfl⟩ : syracuseStep 1703875 = 2555813) B2555813
theorem B5832749 : Blo 670310 5832749 := bstep (se 3 (by rfl) ⟨1093640, by rfl⟩ : syracuseStep 5832749 = 2187281) B2187281
theorem B1703987 : Blo 670310 1703987 := bstep (se 1 (by rfl) ⟨1277990, by rfl⟩ : syracuseStep 1703987 = 2555981) B2555981
theorem B754123 : Blo 670310 754123 := bstep (se 1 (by rfl) ⟨565592, by rfl⟩ : syracuseStep 754123 = 1131185) B1131185
theorem B852439 : Blo 670310 852439 := bstep (se 1 (by rfl) ⟨639329, by rfl⟩ : syracuseStep 852439 = 1278659) B1278659
theorem B1245719 : Blo 670310 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B2556467 : Blo 670310 2556467 := bstep (se 1 (by rfl) ⟨1917350, by rfl⟩ : syracuseStep 2556467 = 3834701) B3834701
theorem B754231 : Blo 670310 754231 := bstep (se 1 (by rfl) ⟨565673, by rfl⟩ : syracuseStep 754231 = 1131347) B1131347
theorem B2556481 : Blo 670310 2556481 := bstep (se 2 (by rfl) ⟨958680, by rfl⟩ : syracuseStep 2556481 = 1917361) B1917361
theorem B1704523 : Blo 670310 1704523 := bstep (se 1 (by rfl) ⟨1278392, by rfl⟩ : syracuseStep 1704523 = 2556785) B2556785
theorem B1704665 : Blo 670310 1704665 := bstep (se 2 (by rfl) ⟨639249, by rfl⟩ : syracuseStep 1704665 = 1278499) B1278499
theorem B754411 : Blo 670310 754411 := bstep (se 1 (by rfl) ⟨565808, by rfl⟩ : syracuseStep 754411 = 1131617) B1131617
theorem B754519 : Blo 670310 754519 := bstep (se 1 (by rfl) ⟨565889, by rfl⟩ : syracuseStep 754519 = 1131779) B1131779
theorem B4096919 : Blo 670310 4096919 := bstep (se 1 (by rfl) ⟨3072689, by rfl⟩ : syracuseStep 4096919 = 6145379) B6145379
theorem B1508363 : Blo 670310 1508363 := bstep (se 1 (by rfl) ⟨1131272, by rfl⟩ : syracuseStep 1508363 = 2262545) B2262545
theorem B754699 : Blo 670310 754699 := bstep (se 1 (by rfl) ⟨566024, by rfl⟩ : syracuseStep 754699 = 1132049) B1132049
theorem B1508417 : Blo 670310 1508417 := bstep (se 2 (by rfl) ⟨565656, by rfl⟩ : syracuseStep 1508417 = 1131313) B1131313
theorem B1213555 : Blo 670310 1213555 := bstep (se 1 (by rfl) ⟨910166, by rfl⟩ : syracuseStep 1213555 = 1820333) B1820333
theorem B1279091 : Blo 670310 1279091 := bstep (se 1 (by rfl) ⟨959318, by rfl⟩ : syracuseStep 1279091 = 1918637) B1918637
theorem B754807 : Blo 670310 754807 := bstep (se 1 (by rfl) ⟨566105, by rfl⟩ : syracuseStep 754807 = 1132211) B1132211
theorem B1279243 : Blo 670310 1279243 := bstep (se 1 (by rfl) ⟨959432, by rfl⟩ : syracuseStep 1279243 = 1918865) B1918865
theorem B1246487 : Blo 670310 1246487 := bstep (se 1 (by rfl) ⟨934865, by rfl⟩ : syracuseStep 1246487 = 1869731) B1869731
theorem B1508633 : Blo 670310 1508633 := bstep (se 2 (by rfl) ⟨565737, by rfl⟩ : syracuseStep 1508633 = 1131475) B1131475
theorem B754987 : Blo 670310 754987 := bstep (se 1 (by rfl) ⟨566240, by rfl⟩ : syracuseStep 754987 = 1132481) B1132481
theorem B1508723 : Blo 670310 1508723 := bstep (se 1 (by rfl) ⟨1131542, by rfl⟩ : syracuseStep 1508723 = 2263085) B2263085
theorem B1508759 : Blo 670310 1508759 := bstep (se 1 (by rfl) ⟨1131569, by rfl⟩ : syracuseStep 1508759 = 2263139) B2263139
theorem B755095 : Blo 670310 755095 := bstep (se 1 (by rfl) ⟨566321, by rfl⟩ : syracuseStep 755095 = 1132643) B1132643
theorem B1705495 : Blo 670310 1705495 := bstep (se 1 (by rfl) ⟨1279121, by rfl⟩ : syracuseStep 1705495 = 2558243) B2558243
theorem B4851245 : Blo 670310 4851245 := bstep (se 3 (by rfl) ⟨909608, by rfl⟩ : syracuseStep 4851245 = 1819217) B1819217
theorem B1508939 : Blo 670310 1508939 := bstep (se 1 (by rfl) ⟨1131704, by rfl⟩ : syracuseStep 1508939 = 2263409) B2263409
theorem B755275 : Blo 670310 755275 := bstep (se 1 (by rfl) ⟨566456, by rfl⟩ : syracuseStep 755275 = 1132913) B1132913
theorem B919127 : Blo 670310 919127 := bstep (se 1 (by rfl) ⟨689345, by rfl⟩ : syracuseStep 919127 = 1378691) B1378691
theorem B1050199 : Blo 670310 1050199 := bstep (se 1 (by rfl) ⟨787649, by rfl⟩ : syracuseStep 1050199 = 1575299) B1575299
theorem B1279577 : Blo 670310 1279577 := bstep (se 2 (by rfl) ⟨479841, by rfl⟩ : syracuseStep 1279577 = 959683) B959683
theorem B1508993 : Blo 670310 1508993 := bstep (se 2 (by rfl) ⟨565872, by rfl⟩ : syracuseStep 1508993 = 1131745) B1131745
theorem B2262707 : Blo 670310 2262707 := bstep (se 1 (by rfl) ⟨1697030, by rfl⟩ : syracuseStep 2262707 = 3394061) B3394061
theorem B755383 : Blo 670310 755383 := bstep (se 1 (by rfl) ⟨566537, by rfl⟩ : syracuseStep 755383 = 1133075) B1133075
theorem B1509209 : Blo 670310 1509209 := bstep (se 2 (by rfl) ⟨565953, by rfl⟩ : syracuseStep 1509209 = 1131907) B1131907
theorem B755563 : Blo 670310 755563 := bstep (se 1 (by rfl) ⟨566672, by rfl⟩ : syracuseStep 755563 = 1133345) B1133345
theorem B1509299 : Blo 670310 1509299 := bstep (se 1 (by rfl) ⟨1131974, by rfl⟩ : syracuseStep 1509299 = 2263949) B2263949
theorem B2262977 : Blo 670310 2262977 := bstep (se 2 (by rfl) ⟨848616, by rfl⟩ : syracuseStep 2262977 = 1697233) B1697233
theorem B1705931 : Blo 670310 1705931 := bstep (se 1 (by rfl) ⟨1279448, by rfl⟩ : syracuseStep 1705931 = 2558897) B2558897
theorem B1509335 : Blo 670310 1509335 := bstep (se 1 (by rfl) ⟨1132001, by rfl⟩ : syracuseStep 1509335 = 2264003) B2264003
theorem B755671 : Blo 670310 755671 := bstep (se 1 (by rfl) ⟨566753, by rfl⟩ : syracuseStep 755671 = 1133507) B1133507
theorem B3409937 : Blo 670310 3409937 := bstep (se 2 (by rfl) ⟨1278726, by rfl⟩ : syracuseStep 3409937 = 2557453) B2557453
theorem B1509515 : Blo 670310 1509515 := bstep (se 1 (by rfl) ⟨1132136, by rfl⟩ : syracuseStep 1509515 = 2264273) B2264273
theorem B755851 : Blo 670310 755851 := bstep (se 1 (by rfl) ⟨566888, by rfl⟩ : syracuseStep 755851 = 1133777) B1133777
theorem B1214615 : Blo 670310 1214615 := bstep (se 1 (by rfl) ⟨910961, by rfl⟩ : syracuseStep 1214615 = 1821923) B1821923
theorem B3410099 : Blo 670310 3410099 := bstep (se 1 (by rfl) ⟨2557574, by rfl⟩ : syracuseStep 3410099 = 5115149) B5115149
theorem B1509569 : Blo 670310 1509569 := bstep (se 2 (by rfl) ⟨566088, by rfl⟩ : syracuseStep 1509569 = 1132177) B1132177
theorem B1214657 : Blo 670310 1214657 := bstep (se 2 (by rfl) ⟨455496, by rfl⟩ : syracuseStep 1214657 = 910993) B910993
theorem B755959 : Blo 670310 755959 := bstep (se 1 (by rfl) ⟨566969, by rfl⟩ : syracuseStep 755959 = 1133939) B1133939
theorem B5114177 : Blo 670310 5114177 := bstep (se 2 (by rfl) ⟨1917816, by rfl⟩ : syracuseStep 5114177 = 3835633) B3835633
theorem B1706305 : Blo 670310 1706305 := bstep (se 2 (by rfl) ⟨639864, by rfl⟩ : syracuseStep 1706305 = 1279729) B1279729
theorem B1509785 : Blo 670310 1509785 := bstep (se 2 (by rfl) ⟨566169, by rfl⟩ : syracuseStep 1509785 = 1132339) B1132339
theorem B756139 : Blo 670310 756139 := bstep (se 1 (by rfl) ⟨567104, by rfl⟩ : syracuseStep 756139 = 1134209) B1134209
theorem B2558411 : Blo 670310 2558411 := bstep (se 1 (by rfl) ⟨1918808, by rfl⟩ : syracuseStep 2558411 = 3837617) B3837617
theorem B2558425 : Blo 670310 2558425 := bstep (se 2 (by rfl) ⟨959409, by rfl⟩ : syracuseStep 2558425 = 1918819) B1918819
theorem B2263517 : Blo 670310 2263517 := bstep (se 3 (by rfl) ⟨424409, by rfl⟩ : syracuseStep 2263517 = 848819) B848819
theorem B1509875 : Blo 670310 1509875 := bstep (se 1 (by rfl) ⟨1132406, by rfl⟩ : syracuseStep 1509875 = 2264813) B2264813
theorem B1509911 : Blo 670310 1509911 := bstep (se 1 (by rfl) ⟨1132433, by rfl⟩ : syracuseStep 1509911 = 2264867) B2264867
theorem B756247 : Blo 670310 756247 := bstep (se 1 (by rfl) ⟨567185, by rfl⟩ : syracuseStep 756247 = 1134371) B1134371
theorem B1510091 : Blo 670310 1510091 := bstep (se 1 (by rfl) ⟨1132568, by rfl⟩ : syracuseStep 1510091 = 2265137) B2265137
theorem B756427 : Blo 670310 756427 := bstep (se 1 (by rfl) ⟨567320, by rfl⟩ : syracuseStep 756427 = 1134641) B1134641
theorem B1510145 : Blo 670310 1510145 := bstep (se 2 (by rfl) ⟨566304, by rfl⟩ : syracuseStep 1510145 = 1132609) B1132609
theorem B12258053 : Blo 670310 12258053 := bstep (se 4 (by rfl) ⟨1149192, by rfl⟩ : syracuseStep 12258053 = 2298385) B2298385
theorem B756535 : Blo 670310 756535 := bstep (se 1 (by rfl) ⟨567401, by rfl⟩ : syracuseStep 756535 = 1134803) B1134803
theorem B1510361 : Blo 670310 1510361 := bstep (se 2 (by rfl) ⟨566385, by rfl⟩ : syracuseStep 1510361 = 1132771) B1132771
theorem B756715 : Blo 670310 756715 := bstep (se 1 (by rfl) ⟨567536, by rfl⟩ : syracuseStep 756715 = 1135073) B1135073
theorem B1510451 : Blo 670310 1510451 := bstep (se 1 (by rfl) ⟨1132838, by rfl⟩ : syracuseStep 1510451 = 2265677) B2265677
theorem B1510487 : Blo 670310 1510487 := bstep (se 1 (by rfl) ⟨1132865, by rfl⟩ : syracuseStep 1510487 = 2265731) B2265731
theorem B756823 : Blo 670310 756823 := bstep (se 1 (by rfl) ⟨567617, by rfl⟩ : syracuseStep 756823 = 1135235) B1135235
theorem B1510667 : Blo 670310 1510667 := bstep (se 1 (by rfl) ⟨1133000, by rfl⟩ : syracuseStep 1510667 = 2266001) B2266001
theorem B757003 : Blo 670310 757003 := bstep (se 1 (by rfl) ⟨567752, by rfl⟩ : syracuseStep 757003 = 1135505) B1135505
theorem B1510721 : Blo 670310 1510721 := bstep (se 2 (by rfl) ⟨566520, by rfl⟩ : syracuseStep 1510721 = 1133041) B1133041
theorem B757111 : Blo 670310 757111 := bstep (se 1 (by rfl) ⟨567833, by rfl⟩ : syracuseStep 757111 = 1135667) B1135667
theorem B2559383 : Blo 670310 2559383 := bstep (se 1 (by rfl) ⟨1919537, by rfl⟩ : syracuseStep 2559383 = 3839075) B3839075
theorem B1936919 : Blo 670310 1936919 := bstep (se 1 (by rfl) ⟨1452689, by rfl⟩ : syracuseStep 1936919 = 2905379) B2905379
theorem B1510937 : Blo 670310 1510937 := bstep (se 2 (by rfl) ⟨566601, by rfl⟩ : syracuseStep 1510937 = 1133203) B1133203
theorem B757291 : Blo 670310 757291 := bstep (se 1 (by rfl) ⟨567968, by rfl⟩ : syracuseStep 757291 = 1135937) B1135937
theorem B1019467 : Blo 670310 1019467 := bstep (se 1 (by rfl) ⟨764600, by rfl⟩ : syracuseStep 1019467 = 1529201) B1529201
theorem B2264651 : Blo 670310 2264651 := bstep (se 1 (by rfl) ⟨1698488, by rfl⟩ : syracuseStep 2264651 = 3396977) B3396977
theorem B1511027 : Blo 670310 1511027 := bstep (se 1 (by rfl) ⟨1133270, by rfl⟩ : syracuseStep 1511027 = 2266541) B2266541
theorem B1511063 : Blo 670310 1511063 := bstep (se 1 (by rfl) ⟨1133297, by rfl⟩ : syracuseStep 1511063 = 2266595) B2266595
theorem B757399 : Blo 670310 757399 := bstep (se 1 (by rfl) ⟨568049, by rfl⟩ : syracuseStep 757399 = 1136099) B1136099
theorem B15503089 : Blo 670310 15503089 := bstep (se 2 (by rfl) ⟨5813658, by rfl⟩ : syracuseStep 15503089 = 11627317) B11627317
theorem B1511243 : Blo 670310 1511243 := bstep (se 1 (by rfl) ⟨1133432, by rfl⟩ : syracuseStep 1511243 = 2266865) B2266865
theorem B757579 : Blo 670310 757579 := bstep (se 1 (by rfl) ⟨568184, by rfl⟩ : syracuseStep 757579 = 1136369) B1136369
theorem B2264921 : Blo 670310 2264921 := bstep (se 2 (by rfl) ⟨849345, by rfl⟩ : syracuseStep 2264921 = 1698691) B1698691
theorem B1511297 : Blo 670310 1511297 := bstep (se 2 (by rfl) ⟨566736, by rfl⟩ : syracuseStep 1511297 = 1133473) B1133473
theorem B757687 : Blo 670310 757687 := bstep (se 1 (by rfl) ⟨568265, by rfl⟩ : syracuseStep 757687 = 1136531) B1136531
theorem B6885337 : Blo 670310 6885337 := bstep (se 2 (by rfl) ⟨2582001, by rfl⟩ : syracuseStep 6885337 = 5164003) B5164003
theorem B3412043 : Blo 670310 3412043 := bstep (se 1 (by rfl) ⟨2559032, by rfl⟩ : syracuseStep 3412043 = 5118065) B5118065
theorem B1511513 : Blo 670310 1511513 := bstep (se 2 (by rfl) ⟨566817, by rfl⟩ : syracuseStep 1511513 = 1133635) B1133635
theorem B757867 : Blo 670310 757867 := bstep (se 1 (by rfl) ⟨568400, by rfl⟩ : syracuseStep 757867 = 1136801) B1136801
theorem B1511603 : Blo 670310 1511603 := bstep (se 1 (by rfl) ⟨1133702, by rfl⟩ : syracuseStep 1511603 = 2267405) B2267405
theorem B1937611 : Blo 670310 1937611 := bstep (se 1 (by rfl) ⟨1453208, by rfl⟩ : syracuseStep 1937611 = 2906417) B2906417
theorem B2298059 : Blo 670310 2298059 := bstep (se 1 (by rfl) ⟨1723544, by rfl⟩ : syracuseStep 2298059 = 3447089) B3447089
theorem B1511639 : Blo 670310 1511639 := bstep (se 1 (by rfl) ⟨1133729, by rfl⟩ : syracuseStep 1511639 = 2267459) B2267459
theorem B757975 : Blo 670310 757975 := bstep (se 1 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 757975 = 1136963) B1136963
theorem B5116121 : Blo 670310 5116121 := bstep (se 2 (by rfl) ⟨1918545, by rfl⟩ : syracuseStep 5116121 = 3837091) B3837091
theorem B1511819 : Blo 670310 1511819 := bstep (se 1 (by rfl) ⟨1133864, by rfl⟩ : syracuseStep 1511819 = 2267729) B2267729
theorem B758155 : Blo 670310 758155 := bstep (se 1 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 758155 = 1137233) B1137233
theorem B1511873 : Blo 670310 1511873 := bstep (se 2 (by rfl) ⟨566952, by rfl⟩ : syracuseStep 1511873 = 1133905) B1133905
theorem B758263 : Blo 670310 758263 := bstep (se 1 (by rfl) ⟨568697, by rfl⟩ : syracuseStep 758263 = 1137395) B1137395
theorem B14750221 : Blo 670310 14750221 := bstep (se 3 (by rfl) ⟨2765666, by rfl⟩ : syracuseStep 14750221 = 5531333) B5531333
theorem B2265623 : Blo 670310 2265623 := bstep (se 1 (by rfl) ⟨1699217, by rfl⟩ : syracuseStep 2265623 = 3398435) B3398435
theorem B1512089 : Blo 670310 1512089 := bstep (se 2 (by rfl) ⟨567033, by rfl⟩ : syracuseStep 1512089 = 1134067) B1134067
theorem B758443 : Blo 670310 758443 := bstep (se 1 (by rfl) ⟨568832, by rfl⟩ : syracuseStep 758443 = 1137665) B1137665
theorem B1512179 : Blo 670310 1512179 := bstep (se 1 (by rfl) ⟨1134134, by rfl⟩ : syracuseStep 1512179 = 2268269) B2268269
theorem B1512215 : Blo 670310 1512215 := bstep (se 1 (by rfl) ⟨1134161, by rfl⟩ : syracuseStep 1512215 = 2268323) B2268323
theorem B758551 : Blo 670310 758551 := bstep (se 1 (by rfl) ⟨568913, by rfl⟩ : syracuseStep 758551 = 1137827) B1137827
theorem B4854593 : Blo 670310 4854593 := bstep (se 2 (by rfl) ⟨1820472, by rfl⟩ : syracuseStep 4854593 = 3640945) B3640945
theorem B1512395 : Blo 670310 1512395 := bstep (se 1 (by rfl) ⟨1134296, by rfl⟩ : syracuseStep 1512395 = 2268593) B2268593
theorem B1512449 : Blo 670310 1512449 := bstep (se 2 (by rfl) ⟨567168, by rfl⟩ : syracuseStep 1512449 = 1134337) B1134337
theorem B2266163 : Blo 670310 2266163 := bstep (se 1 (by rfl) ⟨1699622, by rfl⟩ : syracuseStep 2266163 = 3399245) B3399245
theorem B4854935 : Blo 670310 4854935 := bstep (se 1 (by rfl) ⟨3641201, by rfl⟩ : syracuseStep 4854935 = 7282403) B7282403
theorem B1512665 : Blo 670310 1512665 := bstep (se 2 (by rfl) ⟨567249, by rfl⟩ : syracuseStep 1512665 = 1134499) B1134499
theorem B5739781 : Blo 670310 5739781 := bstep (se 4 (by rfl) ⟨538104, by rfl⟩ : syracuseStep 5739781 = 1076209) B1076209
theorem B1512755 : Blo 670310 1512755 := bstep (se 1 (by rfl) ⟨1134566, by rfl⟩ : syracuseStep 1512755 = 2269133) B2269133
theorem B2266433 : Blo 670310 2266433 := bstep (se 2 (by rfl) ⟨849912, by rfl⟩ : syracuseStep 2266433 = 1699825) B1699825
theorem B1512791 : Blo 670310 1512791 := bstep (se 1 (by rfl) ⟨1134593, by rfl⟩ : syracuseStep 1512791 = 2269187) B2269187
theorem B1512971 : Blo 670310 1512971 := bstep (se 1 (by rfl) ⟨1134728, by rfl⟩ : syracuseStep 1512971 = 2269457) B2269457
theorem B1938995 : Blo 670310 1938995 := bstep (se 1 (by rfl) ⟨1454246, by rfl⟩ : syracuseStep 1938995 = 2908493) B2908493
theorem B1513025 : Blo 670310 1513025 := bstep (se 2 (by rfl) ⟨567384, by rfl⟩ : syracuseStep 1513025 = 1134769) B1134769
theorem B1513241 : Blo 670310 1513241 := bstep (se 2 (by rfl) ⟨567465, by rfl⟩ : syracuseStep 1513241 = 1134931) B1134931
theorem B2266973 : Blo 670310 2266973 := bstep (se 3 (by rfl) ⟨425057, by rfl⟩ : syracuseStep 2266973 = 850115) B850115
theorem B1513331 : Blo 670310 1513331 := bstep (se 1 (by rfl) ⟨1134998, by rfl⟩ : syracuseStep 1513331 = 2269997) B2269997
theorem B1513367 : Blo 670310 1513367 := bstep (se 1 (by rfl) ⟨1135025, by rfl⟩ : syracuseStep 1513367 = 2270051) B2270051
theorem B1152971 : Blo 670310 1152971 := bstep (se 1 (by rfl) ⟨864728, by rfl⟩ : syracuseStep 1152971 = 1729457) B1729457
theorem B1513547 : Blo 670310 1513547 := bstep (se 1 (by rfl) ⟨1135160, by rfl⟩ : syracuseStep 1513547 = 2270321) B2270321
theorem B1513601 : Blo 670310 1513601 := bstep (se 2 (by rfl) ⟨567600, by rfl⟩ : syracuseStep 1513601 = 1135201) B1135201
theorem B9672965 : Blo 670310 9672965 := bstep (se 4 (by rfl) ⟨906840, by rfl⟩ : syracuseStep 9672965 = 1813681) B1813681
theorem B1513817 : Blo 670310 1513817 := bstep (se 2 (by rfl) ⟨567681, by rfl⟩ : syracuseStep 1513817 = 1135363) B1135363
theorem B14522773 : Blo 670310 14522773 := bstep (se 6 (by rfl) ⟨340377, by rfl⟩ : syracuseStep 14522773 = 680755) B680755
theorem B1513907 : Blo 670310 1513907 := bstep (se 1 (by rfl) ⟨1135430, by rfl⟩ : syracuseStep 1513907 = 2270861) B2270861
theorem B1513943 : Blo 670310 1513943 := bstep (se 1 (by rfl) ⟨1135457, by rfl⟩ : syracuseStep 1513943 = 2270915) B2270915
theorem B1514123 : Blo 670310 1514123 := bstep (se 1 (by rfl) ⟨1135592, by rfl⟩ : syracuseStep 1514123 = 2271185) B2271185
theorem B1514177 : Blo 670310 1514177 := bstep (se 2 (by rfl) ⟨567816, by rfl⟩ : syracuseStep 1514177 = 1135633) B1135633
theorem B957143 : Blo 670310 957143 := bstep (se 1 (by rfl) ⟨717857, by rfl⟩ : syracuseStep 957143 = 1435715) B1435715
theorem B4922117 : Blo 670310 4922117 := bstep (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) B922897
theorem B4660013 : Blo 670310 4660013 := bstep (se 3 (by rfl) ⟨873752, by rfl⟩ : syracuseStep 4660013 = 1747505) B1747505
theorem B1514393 : Blo 670310 1514393 := bstep (se 2 (by rfl) ⟨567897, by rfl⟩ : syracuseStep 1514393 = 1135795) B1135795
theorem B2268107 : Blo 670310 2268107 := bstep (se 1 (by rfl) ⟨1701080, by rfl⟩ : syracuseStep 2268107 = 3402161) B3402161
theorem B1514483 : Blo 670310 1514483 := bstep (se 1 (by rfl) ⟨1135862, by rfl⟩ : syracuseStep 1514483 = 2271725) B2271725
theorem B1514519 : Blo 670310 1514519 := bstep (se 1 (by rfl) ⟨1135889, by rfl⟩ : syracuseStep 1514519 = 2271779) B2271779
theorem B1514699 : Blo 670310 1514699 := bstep (se 1 (by rfl) ⟨1136024, by rfl⟩ : syracuseStep 1514699 = 2272049) B2272049
theorem B2268377 : Blo 670310 2268377 := bstep (se 2 (by rfl) ⟨850641, by rfl⟩ : syracuseStep 2268377 = 1701283) B1701283
theorem B1514753 : Blo 670310 1514753 := bstep (se 2 (by rfl) ⟨568032, by rfl⟩ : syracuseStep 1514753 = 1136065) B1136065
theorem B10329443 : Blo 670310 10329443 := bstep (se 1 (by rfl) ⟨7747082, by rfl⟩ : syracuseStep 10329443 = 15494165) B15494165
theorem B1514969 : Blo 670310 1514969 := bstep (se 2 (by rfl) ⟨568113, by rfl⟩ : syracuseStep 1514969 = 1136227) B1136227
theorem B5119523 : Blo 670310 5119523 := bstep (se 1 (by rfl) ⟨3839642, by rfl⟩ : syracuseStep 5119523 = 7679285) B7679285
theorem B1515059 : Blo 670310 1515059 := bstep (se 1 (by rfl) ⟨1136294, by rfl⟩ : syracuseStep 1515059 = 2272589) B2272589
theorem B1515095 : Blo 670310 1515095 := bstep (se 1 (by rfl) ⟨1136321, by rfl⟩ : syracuseStep 1515095 = 2272643) B2272643
theorem B1515275 : Blo 670310 1515275 := bstep (se 1 (by rfl) ⟨1136456, by rfl⟩ : syracuseStep 1515275 = 2272913) B2272913
theorem B1515329 : Blo 670310 1515329 := bstep (se 2 (by rfl) ⟨568248, by rfl⟩ : syracuseStep 1515329 = 1136497) B1136497
theorem B2269079 : Blo 670310 2269079 := bstep (se 1 (by rfl) ⟨1701809, by rfl⟩ : syracuseStep 2269079 = 3403619) B3403619
theorem B5742515 : Blo 670310 5742515 := bstep (se 1 (by rfl) ⟨4306886, by rfl⟩ : syracuseStep 5742515 = 8613773) B8613773
theorem B5513177 : Blo 670310 5513177 := bstep (se 2 (by rfl) ⟨2067441, by rfl⟩ : syracuseStep 5513177 = 4134883) B4134883
theorem B1515545 : Blo 670310 1515545 := bstep (se 2 (by rfl) ⟨568329, by rfl⟩ : syracuseStep 1515545 = 1136659) B1136659
theorem B1515635 : Blo 670310 1515635 := bstep (se 1 (by rfl) ⟨1136726, by rfl⟩ : syracuseStep 1515635 = 2273453) B2273453
theorem B1515671 : Blo 670310 1515671 := bstep (se 1 (by rfl) ⟨1136753, by rfl⟩ : syracuseStep 1515671 = 2273507) B2273507
theorem B1515851 : Blo 670310 1515851 := bstep (se 1 (by rfl) ⟨1136888, by rfl⟩ : syracuseStep 1515851 = 2273777) B2273777
theorem B1515905 : Blo 670310 1515905 := bstep (se 2 (by rfl) ⟨568464, by rfl⟩ : syracuseStep 1515905 = 1136929) B1136929
theorem B2269619 : Blo 670310 2269619 := bstep (se 1 (by rfl) ⟨1702214, by rfl⟩ : syracuseStep 2269619 = 3404429) B3404429
theorem B1516121 : Blo 670310 1516121 := bstep (se 2 (by rfl) ⟨568545, by rfl⟩ : syracuseStep 1516121 = 1137091) B1137091
theorem B1516211 : Blo 670310 1516211 := bstep (se 1 (by rfl) ⟨1137158, by rfl⟩ : syracuseStep 1516211 = 2274317) B2274317
theorem B2269889 : Blo 670310 2269889 := bstep (se 2 (by rfl) ⟨851208, by rfl⟩ : syracuseStep 2269889 = 1702417) B1702417
theorem B1516247 : Blo 670310 1516247 := bstep (se 1 (by rfl) ⟨1137185, by rfl⟩ : syracuseStep 1516247 = 2274371) B2274371
theorem B1516427 : Blo 670310 1516427 := bstep (se 1 (by rfl) ⟨1137320, by rfl⟩ : syracuseStep 1516427 = 2274641) B2274641
theorem B1516481 : Blo 670310 1516481 := bstep (se 2 (by rfl) ⟨568680, by rfl⟩ : syracuseStep 1516481 = 1137361) B1137361
theorem B1025111 : Blo 670310 1025111 := bstep (se 1 (by rfl) ⟨768833, by rfl⟩ : syracuseStep 1025111 = 1537667) B1537667
theorem B1516697 : Blo 670310 1516697 := bstep (se 2 (by rfl) ⟨568761, by rfl⟩ : syracuseStep 1516697 = 1137523) B1137523
theorem B2270429 : Blo 670310 2270429 := bstep (se 3 (by rfl) ⟨425705, by rfl⟩ : syracuseStep 2270429 = 851411) B851411
theorem B1516787 : Blo 670310 1516787 := bstep (se 1 (by rfl) ⟨1137590, by rfl⟩ : syracuseStep 1516787 = 2275181) B2275181
theorem B1516823 : Blo 670310 1516823 := bstep (se 1 (by rfl) ⟨1137617, by rfl⟩ : syracuseStep 1516823 = 2275235) B2275235
theorem B1517003 : Blo 670310 1517003 := bstep (se 1 (by rfl) ⟨1137752, by rfl⟩ : syracuseStep 1517003 = 2275505) B2275505
theorem B1517057 : Blo 670310 1517057 := bstep (se 2 (by rfl) ⟨568896, by rfl⟩ : syracuseStep 1517057 = 1137793) B1137793
theorem B960025 : Blo 670310 960025 := bstep (se 2 (by rfl) ⟨360009, by rfl⟩ : syracuseStep 960025 = 720019) B720019
theorem B1812061 : Blo 670310 1812061 := bstep (se 3 (by rfl) ⟨339761, by rfl⟩ : syracuseStep 1812061 = 679523) B679523
theorem B3221171 : Blo 670310 3221171 := bstep (se 1 (by rfl) ⟨2415878, by rfl⟩ : syracuseStep 3221171 = 4831757) B4831757
theorem B5744429 : Blo 670310 5744429 := bstep (se 3 (by rfl) ⟨1077080, by rfl⟩ : syracuseStep 5744429 = 2154161) B2154161
theorem B1812289 : Blo 670310 1812289 := bstep (se 2 (by rfl) ⟨679608, by rfl⟩ : syracuseStep 1812289 = 1359217) B1359217
theorem B2762903 : Blo 670310 2762903 := bstep (se 1 (by rfl) ⟨2072177, by rfl⟩ : syracuseStep 2762903 = 4144355) B4144355
theorem B4368563 : Blo 670310 4368563 := bstep (se 1 (by rfl) ⟨3276422, by rfl⟩ : syracuseStep 4368563 = 6552845) B6552845
theorem B1616075 : Blo 670310 1616075 := bstep (se 1 (by rfl) ⟨1212056, by rfl⟩ : syracuseStep 1616075 = 2424113) B2424113
theorem B1550657 : Blo 670310 1550657 := bstep (se 2 (by rfl) ⟨581496, by rfl⟩ : syracuseStep 1550657 = 1162993) B1162993
theorem B2271563 : Blo 670310 2271563 := bstep (se 1 (by rfl) ⟨1703672, by rfl⟩ : syracuseStep 2271563 = 3407345) B3407345
theorem B5745113 : Blo 670310 5745113 := bstep (se 2 (by rfl) ⟨2154417, by rfl⟩ : syracuseStep 5745113 = 4308835) B4308835
theorem B1911347 : Blo 670310 1911347 := bstep (se 1 (by rfl) ⟨1433510, by rfl⟩ : syracuseStep 1911347 = 2867021) B2867021
theorem B764491 : Blo 670310 764491 := bstep (se 1 (by rfl) ⟨573368, by rfl⟩ : syracuseStep 764491 = 1146737) B1146737
theorem B1813067 : Blo 670310 1813067 := bstep (se 1 (by rfl) ⟨1359800, by rfl⟩ : syracuseStep 1813067 = 2719601) B2719601
theorem B2271833 : Blo 670310 2271833 := bstep (se 2 (by rfl) ⟨851937, by rfl⟩ : syracuseStep 2271833 = 1703875) B1703875
theorem B1813271 : Blo 670310 1813271 := bstep (se 1 (by rfl) ⟨1359953, by rfl⟩ : syracuseStep 1813271 = 2719907) B2719907
theorem B1911575 : Blo 670310 1911575 := bstep (se 1 (by rfl) ⟨1433681, by rfl⟩ : syracuseStep 1911575 = 2867363) B2867363
theorem B1616843 : Blo 670310 1616843 := bstep (se 1 (by rfl) ⟨1212632, by rfl⟩ : syracuseStep 1616843 = 2425265) B2425265
theorem B764983 : Blo 670310 764983 := bstep (se 1 (by rfl) ⟨573737, by rfl⟩ : syracuseStep 764983 = 1147475) B1147475
theorem B1911883 : Blo 670310 1911883 := bstep (se 1 (by rfl) ⟨1433912, by rfl⟩ : syracuseStep 1911883 = 2867825) B2867825
theorem B2272535 : Blo 670310 2272535 := bstep (se 1 (by rfl) ⟨1704401, by rfl⟩ : syracuseStep 2272535 = 3408803) B3408803
theorem B1912157 : Blo 670310 1912157 := bstep (se 3 (by rfl) ⟨358529, by rfl⟩ : syracuseStep 1912157 = 717059) B717059
theorem B2305459 : Blo 670310 2305459 := bstep (se 1 (by rfl) ⟨1729094, by rfl⟩ : syracuseStep 2305459 = 3458189) B3458189
theorem B1813963 : Blo 670310 1813963 := bstep (se 1 (by rfl) ⟨1360472, by rfl⟩ : syracuseStep 1813963 = 2720945) B2720945
theorem B1224407 : Blo 670310 1224407 := bstep (se 1 (by rfl) ⟨918305, by rfl⟩ : syracuseStep 1224407 = 1836611) B1836611
theorem B1093387 : Blo 670310 1093387 := bstep (se 1 (by rfl) ⟨820040, by rfl⟩ : syracuseStep 1093387 = 1640081) B1640081
theorem B2273075 : Blo 670310 2273075 := bstep (se 1 (by rfl) ⟨1704806, by rfl⟩ : syracuseStep 2273075 = 3409613) B3409613
theorem B13840307 : Blo 670310 13840307 := bstep (se 1 (by rfl) ⟨10380230, by rfl⟩ : syracuseStep 13840307 = 20760461) B20760461
theorem B1552321 : Blo 670310 1552321 := bstep (se 2 (by rfl) ⟨582120, by rfl⟩ : syracuseStep 1552321 = 1164241) B1164241
theorem B2273345 : Blo 670310 2273345 := bstep (se 2 (by rfl) ⟨852504, by rfl⟩ : syracuseStep 2273345 = 1705009) B1705009
theorem B2732363 : Blo 670310 2732363 := bstep (se 1 (by rfl) ⟨2049272, by rfl⟩ : syracuseStep 2732363 = 4098545) B4098545
theorem B3223901 : Blo 670310 3223901 := bstep (se 3 (by rfl) ⟨604481, by rfl⟩ : syracuseStep 3223901 = 1208963) B1208963
theorem B2273885 : Blo 670310 2273885 := bstep (se 3 (by rfl) ⟨426353, by rfl⟩ : syracuseStep 2273885 = 852707) B852707
theorem B9679661 : Blo 670310 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B4436801 : Blo 670310 4436801 := bstep (se 2 (by rfl) ⟨1663800, by rfl⟩ : syracuseStep 4436801 = 3327601) B3327601
theorem B2733401 : Blo 670310 2733401 := bstep (se 2 (by rfl) ⟨1025025, by rfl⟩ : syracuseStep 2733401 = 2050051) B2050051
theorem B1914263 : Blo 670310 1914263 := bstep (se 1 (by rfl) ⟨1435697, by rfl⟩ : syracuseStep 1914263 = 2871395) B2871395
theorem B12269207 : Blo 670310 12269207 := bstep (se 1 (by rfl) ⟨9201905, by rfl⟩ : syracuseStep 12269207 = 18403811) B18403811
theorem B2275019 : Blo 670310 2275019 := bstep (se 1 (by rfl) ⟨1706264, by rfl⟩ : syracuseStep 2275019 = 3412529) B3412529
theorem B2275289 : Blo 670310 2275289 := bstep (se 2 (by rfl) ⟨853233, by rfl⟩ : syracuseStep 2275289 = 1706467) B1706467
theorem B1620119 : Blo 670310 1620119 := bstep (se 1 (by rfl) ⟨1215089, by rfl⟩ : syracuseStep 1620119 = 2430179) B2430179
theorem B1915073 : Blo 670310 1915073 := bstep (se 2 (by rfl) ⟨718152, by rfl⟩ : syracuseStep 1915073 = 1436305) B1436305
theorem B1816883 : Blo 670310 1816883 := bstep (se 1 (by rfl) ⟨1362662, by rfl⟩ : syracuseStep 1816883 = 2725325) B2725325
theorem B670315 : Blo 670310 670315 := bstep (se 1 (by rfl) ⟨502736, by rfl⟩ : syracuseStep 670315 = 1005473) B1005473
theorem B670327 : Blo 670310 670327 := bstep (se 1 (by rfl) ⟨502745, by rfl⟩ : syracuseStep 670327 = 1005491) B1005491
theorem B670347 : Blo 670310 670347 := bstep (se 1 (by rfl) ⟨502760, by rfl⟩ : syracuseStep 670347 = 1005521) B1005521
theorem B670359 : Blo 670310 670359 := bstep (se 1 (by rfl) ⟨502769, by rfl⟩ : syracuseStep 670359 = 1005539) B1005539
theorem B670379 : Blo 670310 670379 := bstep (se 1 (by rfl) ⟨502784, by rfl⟩ : syracuseStep 670379 = 1005569) B1005569
theorem B670391 : Blo 670310 670391 := bstep (se 1 (by rfl) ⟨502793, by rfl⟩ : syracuseStep 670391 = 1005587) B1005587
theorem B670411 : Blo 670310 670411 := bstep (se 1 (by rfl) ⟨502808, by rfl⟩ : syracuseStep 670411 = 1005617) B1005617
theorem B670423 : Blo 670310 670423 := bstep (se 1 (by rfl) ⟨502817, by rfl⟩ : syracuseStep 670423 = 1005635) B1005635
theorem B670443 : Blo 670310 670443 := bstep (se 1 (by rfl) ⟨502832, by rfl⟩ : syracuseStep 670443 = 1005665) B1005665
theorem B670455 : Blo 670310 670455 := bstep (se 1 (by rfl) ⟨502841, by rfl⟩ : syracuseStep 670455 = 1005683) B1005683
theorem B670475 : Blo 670310 670475 := bstep (se 1 (by rfl) ⟨502856, by rfl⟩ : syracuseStep 670475 = 1005713) B1005713
theorem B670487 : Blo 670310 670487 := bstep (se 1 (by rfl) ⟨502865, by rfl⟩ : syracuseStep 670487 = 1005731) B1005731
theorem B670507 : Blo 670310 670507 := bstep (se 1 (by rfl) ⟨502880, by rfl⟩ : syracuseStep 670507 = 1005761) B1005761
theorem B670519 : Blo 670310 670519 := bstep (se 1 (by rfl) ⟨502889, by rfl⟩ : syracuseStep 670519 = 1005779) B1005779
theorem B4832075 : Blo 670310 4832075 := bstep (se 1 (by rfl) ⟨3624056, by rfl⟩ : syracuseStep 4832075 = 7248113) B7248113
theorem B670539 : Blo 670310 670539 := bstep (se 1 (by rfl) ⟨502904, by rfl⟩ : syracuseStep 670539 = 1005809) B1005809
theorem B670551 : Blo 670310 670551 := bstep (se 1 (by rfl) ⟨502913, by rfl⟩ : syracuseStep 670551 = 1005827) B1005827
theorem B670571 : Blo 670310 670571 := bstep (se 1 (by rfl) ⟨502928, by rfl⟩ : syracuseStep 670571 = 1005857) B1005857
theorem B670583 : Blo 670310 670583 := bstep (se 1 (by rfl) ⟨502937, by rfl⟩ : syracuseStep 670583 = 1005875) B1005875
theorem B670603 : Blo 670310 670603 := bstep (se 1 (by rfl) ⟨502952, by rfl⟩ : syracuseStep 670603 = 1005905) B1005905
theorem B670615 : Blo 670310 670615 := bstep (se 1 (by rfl) ⟨502961, by rfl⟩ : syracuseStep 670615 = 1005923) B1005923
theorem B670635 : Blo 670310 670635 := bstep (se 1 (by rfl) ⟨502976, by rfl⟩ : syracuseStep 670635 = 1005953) B1005953
theorem B670647 : Blo 670310 670647 := bstep (se 1 (by rfl) ⟨502985, by rfl⟩ : syracuseStep 670647 = 1005971) B1005971
theorem B670667 : Blo 670310 670667 := bstep (se 1 (by rfl) ⟨503000, by rfl⟩ : syracuseStep 670667 = 1006001) B1006001
theorem B670679 : Blo 670310 670679 := bstep (se 1 (by rfl) ⟨503009, by rfl⟩ : syracuseStep 670679 = 1006019) B1006019
theorem B670699 : Blo 670310 670699 := bstep (se 1 (by rfl) ⟨503024, by rfl⟩ : syracuseStep 670699 = 1006049) B1006049
theorem B670711 : Blo 670310 670711 := bstep (se 1 (by rfl) ⟨503033, by rfl⟩ : syracuseStep 670711 = 1006067) B1006067
theorem B670731 : Blo 670310 670731 := bstep (se 1 (by rfl) ⟨503048, by rfl⟩ : syracuseStep 670731 = 1006097) B1006097
theorem B670743 : Blo 670310 670743 := bstep (se 1 (by rfl) ⟨503057, by rfl⟩ : syracuseStep 670743 = 1006115) B1006115
theorem B670763 : Blo 670310 670763 := bstep (se 1 (by rfl) ⟨503072, by rfl⟩ : syracuseStep 670763 = 1006145) B1006145
theorem B670775 : Blo 670310 670775 := bstep (se 1 (by rfl) ⟨503081, by rfl⟩ : syracuseStep 670775 = 1006163) B1006163
theorem B670795 : Blo 670310 670795 := bstep (se 1 (by rfl) ⟨503096, by rfl⟩ : syracuseStep 670795 = 1006193) B1006193
theorem B8600651 : Blo 670310 8600651 := bstep (se 1 (by rfl) ⟨6450488, by rfl⟩ : syracuseStep 8600651 = 12900977) B12900977
theorem B670807 : Blo 670310 670807 := bstep (se 1 (by rfl) ⟨503105, by rfl⟩ : syracuseStep 670807 = 1006211) B1006211
theorem B670827 : Blo 670310 670827 := bstep (se 1 (by rfl) ⟨503120, by rfl⟩ : syracuseStep 670827 = 1006241) B1006241
theorem B670839 : Blo 670310 670839 := bstep (se 1 (by rfl) ⟨503129, by rfl⟩ : syracuseStep 670839 = 1006259) B1006259
theorem B670859 : Blo 670310 670859 := bstep (se 1 (by rfl) ⟨503144, by rfl⟩ : syracuseStep 670859 = 1006289) B1006289
theorem B670871 : Blo 670310 670871 := bstep (se 1 (by rfl) ⟨503153, by rfl⟩ : syracuseStep 670871 = 1006307) B1006307
theorem B670891 : Blo 670310 670891 := bstep (se 1 (by rfl) ⟨503168, by rfl⟩ : syracuseStep 670891 = 1006337) B1006337
theorem B3456179 : Blo 670310 3456179 := bstep (se 1 (by rfl) ⟨2592134, by rfl⟩ : syracuseStep 3456179 = 5184269) B5184269
theorem B670903 : Blo 670310 670903 := bstep (se 1 (by rfl) ⟨503177, by rfl⟩ : syracuseStep 670903 = 1006355) B1006355
theorem B670923 : Blo 670310 670923 := bstep (se 1 (by rfl) ⟨503192, by rfl⟩ : syracuseStep 670923 = 1006385) B1006385
theorem B670935 : Blo 670310 670935 := bstep (se 1 (by rfl) ⟨503201, by rfl⟩ : syracuseStep 670935 = 1006403) B1006403
theorem B670955 : Blo 670310 670955 := bstep (se 1 (by rfl) ⟨503216, by rfl⟩ : syracuseStep 670955 = 1006433) B1006433
theorem B670967 : Blo 670310 670967 := bstep (se 1 (by rfl) ⟨503225, by rfl⟩ : syracuseStep 670967 = 1006451) B1006451
theorem B670987 : Blo 670310 670987 := bstep (se 1 (by rfl) ⟨503240, by rfl⟩ : syracuseStep 670987 = 1006481) B1006481
theorem B1359127 : Blo 670310 1359127 := bstep (se 1 (by rfl) ⟨1019345, by rfl⟩ : syracuseStep 1359127 = 2038691) B2038691
theorem B670999 : Blo 670310 670999 := bstep (se 1 (by rfl) ⟨503249, by rfl⟩ : syracuseStep 670999 = 1006499) B1006499
theorem B671019 : Blo 670310 671019 := bstep (se 1 (by rfl) ⟨503264, by rfl⟩ : syracuseStep 671019 = 1006529) B1006529
theorem B671031 : Blo 670310 671031 := bstep (se 1 (by rfl) ⟨503273, by rfl⟩ : syracuseStep 671031 = 1006547) B1006547
theorem B671051 : Blo 670310 671051 := bstep (se 1 (by rfl) ⟨503288, by rfl⟩ : syracuseStep 671051 = 1006577) B1006577
theorem B4308299 : Blo 670310 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B1359191 : Blo 670310 1359191 := bstep (se 1 (by rfl) ⟨1019393, by rfl⟩ : syracuseStep 1359191 = 2038787) B2038787
theorem B671063 : Blo 670310 671063 := bstep (se 1 (by rfl) ⟨503297, by rfl⟩ : syracuseStep 671063 = 1006595) B1006595
theorem B671083 : Blo 670310 671083 := bstep (se 1 (by rfl) ⟨503312, by rfl⟩ : syracuseStep 671083 = 1006625) B1006625
theorem B671095 : Blo 670310 671095 := bstep (se 1 (by rfl) ⟨503321, by rfl⟩ : syracuseStep 671095 = 1006643) B1006643
theorem B671115 : Blo 670310 671115 := bstep (se 1 (by rfl) ⟨503336, by rfl⟩ : syracuseStep 671115 = 1006673) B1006673
theorem B671127 : Blo 670310 671127 := bstep (se 1 (by rfl) ⟨503345, by rfl⟩ : syracuseStep 671127 = 1006691) B1006691
theorem B671147 : Blo 670310 671147 := bstep (se 1 (by rfl) ⟨503360, by rfl⟩ : syracuseStep 671147 = 1006721) B1006721
theorem B671159 : Blo 670310 671159 := bstep (se 1 (by rfl) ⟨503369, by rfl⟩ : syracuseStep 671159 = 1006739) B1006739
theorem B671179 : Blo 670310 671179 := bstep (se 1 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 671179 = 1006769) B1006769
theorem B671191 : Blo 670310 671191 := bstep (se 1 (by rfl) ⟨503393, by rfl⟩ : syracuseStep 671191 = 1006787) B1006787
theorem B671211 : Blo 670310 671211 := bstep (se 1 (by rfl) ⟨503408, by rfl⟩ : syracuseStep 671211 = 1006817) B1006817
theorem B671223 : Blo 670310 671223 := bstep (se 1 (by rfl) ⟨503417, by rfl⟩ : syracuseStep 671223 = 1006835) B1006835
theorem B671243 : Blo 670310 671243 := bstep (se 1 (by rfl) ⟨503432, by rfl⟩ : syracuseStep 671243 = 1006865) B1006865
theorem B671255 : Blo 670310 671255 := bstep (se 1 (by rfl) ⟨503441, by rfl⟩ : syracuseStep 671255 = 1006883) B1006883
theorem B671275 : Blo 670310 671275 := bstep (se 1 (by rfl) ⟨503456, by rfl⟩ : syracuseStep 671275 = 1006913) B1006913
theorem B671287 : Blo 670310 671287 := bstep (se 1 (by rfl) ⟨503465, by rfl⟩ : syracuseStep 671287 = 1006931) B1006931
theorem B671307 : Blo 670310 671307 := bstep (se 1 (by rfl) ⟨503480, by rfl⟩ : syracuseStep 671307 = 1006961) B1006961
theorem B671319 : Blo 670310 671319 := bstep (se 1 (by rfl) ⟨503489, by rfl⟩ : syracuseStep 671319 = 1006979) B1006979
theorem B10927709 : Blo 670310 10927709 := bstep (se 3 (by rfl) ⟨2048945, by rfl⟩ : syracuseStep 10927709 = 4097891) B4097891
theorem B671339 : Blo 670310 671339 := bstep (se 1 (by rfl) ⟨503504, by rfl⟩ : syracuseStep 671339 = 1007009) B1007009
theorem B671351 : Blo 670310 671351 := bstep (se 1 (by rfl) ⟨503513, by rfl⟩ : syracuseStep 671351 = 1007027) B1007027
theorem B671371 : Blo 670310 671371 := bstep (se 1 (by rfl) ⟨503528, by rfl⟩ : syracuseStep 671371 = 1007057) B1007057
theorem B671383 : Blo 670310 671383 := bstep (se 1 (by rfl) ⟨503537, by rfl⟩ : syracuseStep 671383 = 1007075) B1007075
theorem B671403 : Blo 670310 671403 := bstep (se 1 (by rfl) ⟨503552, by rfl⟩ : syracuseStep 671403 = 1007105) B1007105
theorem B671415 : Blo 670310 671415 := bstep (se 1 (by rfl) ⟨503561, by rfl⟩ : syracuseStep 671415 = 1007123) B1007123
theorem B671435 : Blo 670310 671435 := bstep (se 1 (by rfl) ⟨503576, by rfl⟩ : syracuseStep 671435 = 1007153) B1007153
theorem B671447 : Blo 670310 671447 := bstep (se 1 (by rfl) ⟨503585, by rfl⟩ : syracuseStep 671447 = 1007171) B1007171
theorem B671467 : Blo 670310 671467 := bstep (se 1 (by rfl) ⟨503600, by rfl⟩ : syracuseStep 671467 = 1007201) B1007201
theorem B671479 : Blo 670310 671479 := bstep (se 1 (by rfl) ⟨503609, by rfl⟩ : syracuseStep 671479 = 1007219) B1007219
theorem B1457921 : Blo 670310 1457921 := bstep (se 2 (by rfl) ⟨546720, by rfl⟩ : syracuseStep 1457921 = 1093441) B1093441
theorem B671499 : Blo 670310 671499 := bstep (se 1 (by rfl) ⟨503624, by rfl⟩ : syracuseStep 671499 = 1007249) B1007249
theorem B671511 : Blo 670310 671511 := bstep (se 1 (by rfl) ⟨503633, by rfl⟩ : syracuseStep 671511 = 1007267) B1007267
theorem B671531 : Blo 670310 671531 := bstep (se 1 (by rfl) ⟨503648, by rfl⟩ : syracuseStep 671531 = 1007297) B1007297
theorem B1916723 : Blo 670310 1916723 := bstep (se 1 (by rfl) ⟨1437542, by rfl⟩ : syracuseStep 1916723 = 2875085) B2875085
theorem B671543 : Blo 670310 671543 := bstep (se 1 (by rfl) ⟨503657, by rfl⟩ : syracuseStep 671543 = 1007315) B1007315
theorem B671563 : Blo 670310 671563 := bstep (se 1 (by rfl) ⟨503672, by rfl⟩ : syracuseStep 671563 = 1007345) B1007345
theorem B1916747 : Blo 670310 1916747 := bstep (se 1 (by rfl) ⟨1437560, by rfl⟩ : syracuseStep 1916747 = 2875121) B2875121
theorem B671575 : Blo 670310 671575 := bstep (se 1 (by rfl) ⟨503681, by rfl⟩ : syracuseStep 671575 = 1007363) B1007363
theorem B18693989 : Blo 670310 18693989 := bstep (se 4 (by rfl) ⟨1752561, by rfl⟩ : syracuseStep 18693989 = 3505123) B3505123
theorem B671595 : Blo 670310 671595 := bstep (se 1 (by rfl) ⟨503696, by rfl⟩ : syracuseStep 671595 = 1007393) B1007393
theorem B671607 : Blo 670310 671607 := bstep (se 1 (by rfl) ⟨503705, by rfl⟩ : syracuseStep 671607 = 1007411) B1007411
theorem B671627 : Blo 670310 671627 := bstep (se 1 (by rfl) ⟨503720, by rfl⟩ : syracuseStep 671627 = 1007441) B1007441
theorem B2867089 : Blo 670310 2867089 := bstep (se 2 (by rfl) ⟨1075158, by rfl⟩ : syracuseStep 2867089 = 2150317) B2150317
theorem B671639 : Blo 670310 671639 := bstep (se 1 (by rfl) ⟨503729, by rfl⟩ : syracuseStep 671639 = 1007459) B1007459
theorem B671659 : Blo 670310 671659 := bstep (se 1 (by rfl) ⟨503744, by rfl⟩ : syracuseStep 671659 = 1007489) B1007489
theorem B671671 : Blo 670310 671671 := bstep (se 1 (by rfl) ⟨503753, by rfl⟩ : syracuseStep 671671 = 1007507) B1007507
theorem B671691 : Blo 670310 671691 := bstep (se 1 (by rfl) ⟨503768, by rfl⟩ : syracuseStep 671691 = 1007537) B1007537
theorem B671703 : Blo 670310 671703 := bstep (se 1 (by rfl) ⟨503777, by rfl⟩ : syracuseStep 671703 = 1007555) B1007555
theorem B671723 : Blo 670310 671723 := bstep (se 1 (by rfl) ⟨503792, by rfl⟩ : syracuseStep 671723 = 1007585) B1007585
theorem B671735 : Blo 670310 671735 := bstep (se 1 (by rfl) ⟨503801, by rfl⟩ : syracuseStep 671735 = 1007603) B1007603
theorem B671755 : Blo 670310 671755 := bstep (se 1 (by rfl) ⟨503816, by rfl⟩ : syracuseStep 671755 = 1007633) B1007633
theorem B671767 : Blo 670310 671767 := bstep (se 1 (by rfl) ⟨503825, by rfl⟩ : syracuseStep 671767 = 1007651) B1007651
theorem B671787 : Blo 670310 671787 := bstep (se 1 (by rfl) ⟨503840, by rfl⟩ : syracuseStep 671787 = 1007681) B1007681
theorem B671799 : Blo 670310 671799 := bstep (se 1 (by rfl) ⟨503849, by rfl⟩ : syracuseStep 671799 = 1007699) B1007699
theorem B671819 : Blo 670310 671819 := bstep (se 1 (by rfl) ⟨503864, by rfl⟩ : syracuseStep 671819 = 1007729) B1007729
theorem B671831 : Blo 670310 671831 := bstep (se 1 (by rfl) ⟨503873, by rfl⟩ : syracuseStep 671831 = 1007747) B1007747
theorem B7356509 : Blo 670310 7356509 := bstep (se 3 (by rfl) ⟨1379345, by rfl⟩ : syracuseStep 7356509 = 2758691) B2758691
theorem B671851 : Blo 670310 671851 := bstep (se 1 (by rfl) ⟨503888, by rfl⟩ : syracuseStep 671851 = 1007777) B1007777
theorem B671863 : Blo 670310 671863 := bstep (se 1 (by rfl) ⟨503897, by rfl⟩ : syracuseStep 671863 = 1007795) B1007795
theorem B671883 : Blo 670310 671883 := bstep (se 1 (by rfl) ⟨503912, by rfl⟩ : syracuseStep 671883 = 1007825) B1007825
theorem B671895 : Blo 670310 671895 := bstep (se 1 (by rfl) ⟨503921, by rfl⟩ : syracuseStep 671895 = 1007843) B1007843
theorem B671915 : Blo 670310 671915 := bstep (se 1 (by rfl) ⟨503936, by rfl⟩ : syracuseStep 671915 = 1007873) B1007873
theorem B671927 : Blo 670310 671927 := bstep (se 1 (by rfl) ⟨503945, by rfl⟩ : syracuseStep 671927 = 1007891) B1007891
theorem B671947 : Blo 670310 671947 := bstep (se 1 (by rfl) ⟨503960, by rfl⟩ : syracuseStep 671947 = 1007921) B1007921
theorem B671959 : Blo 670310 671959 := bstep (se 1 (by rfl) ⟨503969, by rfl⟩ : syracuseStep 671959 = 1007939) B1007939
theorem B671979 : Blo 670310 671979 := bstep (se 1 (by rfl) ⟨503984, by rfl⟩ : syracuseStep 671979 = 1007969) B1007969
theorem B671991 : Blo 670310 671991 := bstep (se 1 (by rfl) ⟨503993, by rfl⟩ : syracuseStep 671991 = 1007987) B1007987
theorem B672011 : Blo 670310 672011 := bstep (se 1 (by rfl) ⟨504008, by rfl⟩ : syracuseStep 672011 = 1008017) B1008017
theorem B672023 : Blo 670310 672023 := bstep (se 1 (by rfl) ⟨504017, by rfl⟩ : syracuseStep 672023 = 1008035) B1008035
theorem B672043 : Blo 670310 672043 := bstep (se 1 (by rfl) ⟨504032, by rfl⟩ : syracuseStep 672043 = 1008065) B1008065
theorem B672055 : Blo 670310 672055 := bstep (se 1 (by rfl) ⟨504041, by rfl⟩ : syracuseStep 672055 = 1008083) B1008083
theorem B672075 : Blo 670310 672075 := bstep (se 1 (by rfl) ⟨504056, by rfl⟩ : syracuseStep 672075 = 1008113) B1008113
theorem B672087 : Blo 670310 672087 := bstep (se 1 (by rfl) ⟨504065, by rfl⟩ : syracuseStep 672087 = 1008131) B1008131
theorem B672107 : Blo 670310 672107 := bstep (se 1 (by rfl) ⟨504080, by rfl⟩ : syracuseStep 672107 = 1008161) B1008161
theorem B672119 : Blo 670310 672119 := bstep (se 1 (by rfl) ⟨504089, by rfl⟩ : syracuseStep 672119 = 1008179) B1008179
theorem B672139 : Blo 670310 672139 := bstep (se 1 (by rfl) ⟨504104, by rfl⟩ : syracuseStep 672139 = 1008209) B1008209
theorem B672151 : Blo 670310 672151 := bstep (se 1 (by rfl) ⟨504113, by rfl⟩ : syracuseStep 672151 = 1008227) B1008227
theorem B672171 : Blo 670310 672171 := bstep (se 1 (by rfl) ⟨504128, by rfl⟩ : syracuseStep 672171 = 1008257) B1008257
theorem B4833715 : Blo 670310 4833715 := bstep (se 1 (by rfl) ⟨3625286, by rfl⟩ : syracuseStep 4833715 = 7250573) B7250573
theorem B672183 : Blo 670310 672183 := bstep (se 1 (by rfl) ⟨504137, by rfl⟩ : syracuseStep 672183 = 1008275) B1008275
theorem B672203 : Blo 670310 672203 := bstep (se 1 (by rfl) ⟨504152, by rfl⟩ : syracuseStep 672203 = 1008305) B1008305
theorem B672215 : Blo 670310 672215 := bstep (se 1 (by rfl) ⟨504161, by rfl⟩ : syracuseStep 672215 = 1008323) B1008323
theorem B672235 : Blo 670310 672235 := bstep (se 1 (by rfl) ⟨504176, by rfl⟩ : syracuseStep 672235 = 1008353) B1008353
theorem B672247 : Blo 670310 672247 := bstep (se 1 (by rfl) ⟨504185, by rfl⟩ : syracuseStep 672247 = 1008371) B1008371
theorem B672267 : Blo 670310 672267 := bstep (se 1 (by rfl) ⟨504200, by rfl⟩ : syracuseStep 672267 = 1008401) B1008401
theorem B672279 : Blo 670310 672279 := bstep (se 1 (by rfl) ⟨504209, by rfl⟩ : syracuseStep 672279 = 1008419) B1008419
theorem B672299 : Blo 670310 672299 := bstep (se 1 (by rfl) ⟨504224, by rfl⟩ : syracuseStep 672299 = 1008449) B1008449
theorem B672311 : Blo 670310 672311 := bstep (se 1 (by rfl) ⟨504233, by rfl⟩ : syracuseStep 672311 = 1008467) B1008467
theorem B672331 : Blo 670310 672331 := bstep (se 1 (by rfl) ⟨504248, by rfl⟩ : syracuseStep 672331 = 1008497) B1008497
theorem B672343 : Blo 670310 672343 := bstep (se 1 (by rfl) ⟨504257, by rfl⟩ : syracuseStep 672343 = 1008515) B1008515
theorem B1917533 : Blo 670310 1917533 := bstep (se 3 (by rfl) ⟨359537, by rfl⟩ : syracuseStep 1917533 = 719075) B719075
theorem B672363 : Blo 670310 672363 := bstep (se 1 (by rfl) ⟨504272, by rfl⟩ : syracuseStep 672363 = 1008545) B1008545
theorem B672375 : Blo 670310 672375 := bstep (se 1 (by rfl) ⟨504281, by rfl⟩ : syracuseStep 672375 = 1008563) B1008563
theorem B672395 : Blo 670310 672395 := bstep (se 1 (by rfl) ⟨504296, by rfl⟩ : syracuseStep 672395 = 1008593) B1008593
theorem B672407 : Blo 670310 672407 := bstep (se 1 (by rfl) ⟨504305, by rfl⟩ : syracuseStep 672407 = 1008611) B1008611
theorem B672427 : Blo 670310 672427 := bstep (se 1 (by rfl) ⟨504320, by rfl⟩ : syracuseStep 672427 = 1008641) B1008641
theorem B672439 : Blo 670310 672439 := bstep (se 1 (by rfl) ⟨504329, by rfl⟩ : syracuseStep 672439 = 1008659) B1008659
theorem B672459 : Blo 670310 672459 := bstep (se 1 (by rfl) ⟨504344, by rfl⟩ : syracuseStep 672459 = 1008689) B1008689
theorem B672471 : Blo 670310 672471 := bstep (se 1 (by rfl) ⟨504353, by rfl⟩ : syracuseStep 672471 = 1008707) B1008707
theorem B672491 : Blo 670310 672491 := bstep (se 1 (by rfl) ⟨504368, by rfl⟩ : syracuseStep 672491 = 1008737) B1008737
theorem B672503 : Blo 670310 672503 := bstep (se 1 (by rfl) ⟨504377, by rfl⟩ : syracuseStep 672503 = 1008755) B1008755
theorem B672523 : Blo 670310 672523 := bstep (se 1 (by rfl) ⟨504392, by rfl⟩ : syracuseStep 672523 = 1008785) B1008785
theorem B672535 : Blo 670310 672535 := bstep (se 1 (by rfl) ⟨504401, by rfl⟩ : syracuseStep 672535 = 1008803) B1008803
theorem B672555 : Blo 670310 672555 := bstep (se 1 (by rfl) ⟨504416, by rfl⟩ : syracuseStep 672555 = 1008833) B1008833
theorem B672567 : Blo 670310 672567 := bstep (se 1 (by rfl) ⟨504425, by rfl⟩ : syracuseStep 672567 = 1008851) B1008851
theorem B672587 : Blo 670310 672587 := bstep (se 1 (by rfl) ⟨504440, by rfl⟩ : syracuseStep 672587 = 1008881) B1008881
theorem B672599 : Blo 670310 672599 := bstep (se 1 (by rfl) ⟨504449, by rfl⟩ : syracuseStep 672599 = 1008899) B1008899
theorem B672619 : Blo 670310 672619 := bstep (se 1 (by rfl) ⟨504464, by rfl⟩ : syracuseStep 672619 = 1008929) B1008929
theorem B672631 : Blo 670310 672631 := bstep (se 1 (by rfl) ⟨504473, by rfl⟩ : syracuseStep 672631 = 1008947) B1008947
theorem B672651 : Blo 670310 672651 := bstep (se 1 (by rfl) ⟨504488, by rfl⟩ : syracuseStep 672651 = 1008977) B1008977
theorem B672663 : Blo 670310 672663 := bstep (se 1 (by rfl) ⟨504497, by rfl⟩ : syracuseStep 672663 = 1008995) B1008995
theorem B672683 : Blo 670310 672683 := bstep (se 1 (by rfl) ⟨504512, by rfl⟩ : syracuseStep 672683 = 1009025) B1009025
theorem B672695 : Blo 670310 672695 := bstep (se 1 (by rfl) ⟨504521, by rfl⟩ : syracuseStep 672695 = 1009043) B1009043
theorem B672715 : Blo 670310 672715 := bstep (se 1 (by rfl) ⟨504536, by rfl⟩ : syracuseStep 672715 = 1009073) B1009073
theorem B672727 : Blo 670310 672727 := bstep (se 1 (by rfl) ⟨504545, by rfl⟩ : syracuseStep 672727 = 1009091) B1009091
theorem B672747 : Blo 670310 672747 := bstep (se 1 (by rfl) ⟨504560, by rfl⟩ : syracuseStep 672747 = 1009121) B1009121
theorem B672759 : Blo 670310 672759 := bstep (se 1 (by rfl) ⟨504569, by rfl⟩ : syracuseStep 672759 = 1009139) B1009139
theorem B672779 : Blo 670310 672779 := bstep (se 1 (by rfl) ⟨504584, by rfl⟩ : syracuseStep 672779 = 1009169) B1009169
theorem B672791 : Blo 670310 672791 := bstep (se 1 (by rfl) ⟨504593, by rfl⟩ : syracuseStep 672791 = 1009187) B1009187
theorem B672811 : Blo 670310 672811 := bstep (se 1 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 672811 = 1009217) B1009217
theorem B672823 : Blo 670310 672823 := bstep (se 1 (by rfl) ⟨504617, by rfl⟩ : syracuseStep 672823 = 1009235) B1009235
theorem B672843 : Blo 670310 672843 := bstep (se 1 (by rfl) ⟨504632, by rfl⟩ : syracuseStep 672843 = 1009265) B1009265
theorem B1295435 : Blo 670310 1295435 := bstep (se 1 (by rfl) ⟨971576, by rfl⟩ : syracuseStep 1295435 = 1943153) B1943153
theorem B672855 : Blo 670310 672855 := bstep (se 1 (by rfl) ⟨504641, by rfl⟩ : syracuseStep 672855 = 1009283) B1009283
theorem B672875 : Blo 670310 672875 := bstep (se 1 (by rfl) ⟨504656, by rfl⟩ : syracuseStep 672875 = 1009313) B1009313
theorem B672887 : Blo 670310 672887 := bstep (se 1 (by rfl) ⟨504665, by rfl⟩ : syracuseStep 672887 = 1009331) B1009331
theorem B672907 : Blo 670310 672907 := bstep (se 1 (by rfl) ⟨504680, by rfl⟩ : syracuseStep 672907 = 1009361) B1009361
theorem B1131671 : Blo 670310 1131671 := bstep (se 1 (by rfl) ⟨848753, by rfl⟩ : syracuseStep 1131671 = 1697507) B1697507
theorem B4310167 : Blo 670310 4310167 := bstep (se 1 (by rfl) ⟨3232625, by rfl⟩ : syracuseStep 4310167 = 6465251) B6465251
theorem B672919 : Blo 670310 672919 := bstep (se 1 (by rfl) ⟨504689, by rfl⟩ : syracuseStep 672919 = 1009379) B1009379
theorem B672939 : Blo 670310 672939 := bstep (se 1 (by rfl) ⟨504704, by rfl⟩ : syracuseStep 672939 = 1009409) B1009409
theorem B672951 : Blo 670310 672951 := bstep (se 1 (by rfl) ⟨504713, by rfl⟩ : syracuseStep 672951 = 1009427) B1009427
theorem B672971 : Blo 670310 672971 := bstep (se 1 (by rfl) ⟨504728, by rfl⟩ : syracuseStep 672971 = 1009457) B1009457
theorem B672983 : Blo 670310 672983 := bstep (se 1 (by rfl) ⟨504737, by rfl⟩ : syracuseStep 672983 = 1009475) B1009475
theorem B673003 : Blo 670310 673003 := bstep (se 1 (by rfl) ⟨504752, by rfl⟩ : syracuseStep 673003 = 1009505) B1009505
theorem B673015 : Blo 670310 673015 := bstep (se 1 (by rfl) ⟨504761, by rfl⟩ : syracuseStep 673015 = 1009523) B1009523
theorem B673035 : Blo 670310 673035 := bstep (se 1 (by rfl) ⟨504776, by rfl⟩ : syracuseStep 673035 = 1009553) B1009553
theorem B1131799 : Blo 670310 1131799 := bstep (se 1 (by rfl) ⟨848849, by rfl⟩ : syracuseStep 1131799 = 1697699) B1697699
theorem B673047 : Blo 670310 673047 := bstep (se 1 (by rfl) ⟨504785, by rfl⟩ : syracuseStep 673047 = 1009571) B1009571
theorem B673067 : Blo 670310 673067 := bstep (se 1 (by rfl) ⟨504800, by rfl⟩ : syracuseStep 673067 = 1009601) B1009601
theorem B673079 : Blo 670310 673079 := bstep (se 1 (by rfl) ⟨504809, by rfl⟩ : syracuseStep 673079 = 1009619) B1009619
theorem B673099 : Blo 670310 673099 := bstep (se 1 (by rfl) ⟨504824, by rfl⟩ : syracuseStep 673099 = 1009649) B1009649
theorem B673111 : Blo 670310 673111 := bstep (se 1 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 673111 = 1009667) B1009667
theorem B673131 : Blo 670310 673131 := bstep (se 1 (by rfl) ⟨504848, by rfl⟩ : syracuseStep 673131 = 1009697) B1009697
theorem B673143 : Blo 670310 673143 := bstep (se 1 (by rfl) ⟨504857, by rfl⟩ : syracuseStep 673143 = 1009715) B1009715
theorem B673163 : Blo 670310 673163 := bstep (se 1 (by rfl) ⟨504872, by rfl⟩ : syracuseStep 673163 = 1009745) B1009745
theorem B673175 : Blo 670310 673175 := bstep (se 1 (by rfl) ⟨504881, by rfl⟩ : syracuseStep 673175 = 1009763) B1009763
theorem B673195 : Blo 670310 673195 := bstep (se 1 (by rfl) ⟨504896, by rfl⟩ : syracuseStep 673195 = 1009793) B1009793
theorem B673207 : Blo 670310 673207 := bstep (se 1 (by rfl) ⟨504905, by rfl⟩ : syracuseStep 673207 = 1009811) B1009811
theorem B673227 : Blo 670310 673227 := bstep (se 1 (by rfl) ⟨504920, by rfl⟩ : syracuseStep 673227 = 1009841) B1009841
theorem B673239 : Blo 670310 673239 := bstep (se 1 (by rfl) ⟨504929, by rfl⟩ : syracuseStep 673239 = 1009859) B1009859
theorem B673259 : Blo 670310 673259 := bstep (se 1 (by rfl) ⟨504944, by rfl⟩ : syracuseStep 673259 = 1009889) B1009889
theorem B673271 : Blo 670310 673271 := bstep (se 1 (by rfl) ⟨504953, by rfl⟩ : syracuseStep 673271 = 1009907) B1009907
theorem B673291 : Blo 670310 673291 := bstep (se 1 (by rfl) ⟨504968, by rfl⟩ : syracuseStep 673291 = 1009937) B1009937
theorem B673303 : Blo 670310 673303 := bstep (se 1 (by rfl) ⟨504977, by rfl⟩ : syracuseStep 673303 = 1009955) B1009955
theorem B673323 : Blo 670310 673323 := bstep (se 1 (by rfl) ⟨504992, by rfl⟩ : syracuseStep 673323 = 1009985) B1009985
theorem B673335 : Blo 670310 673335 := bstep (se 1 (by rfl) ⟨505001, by rfl⟩ : syracuseStep 673335 = 1010003) B1010003
theorem B673355 : Blo 670310 673355 := bstep (se 1 (by rfl) ⟨505016, by rfl⟩ : syracuseStep 673355 = 1010033) B1010033
theorem B673367 : Blo 670310 673367 := bstep (se 1 (by rfl) ⟨505025, by rfl⟩ : syracuseStep 673367 = 1010051) B1010051
theorem B673387 : Blo 670310 673387 := bstep (se 1 (by rfl) ⟨505040, by rfl⟩ : syracuseStep 673387 = 1010081) B1010081
theorem B673399 : Blo 670310 673399 := bstep (se 1 (by rfl) ⟨505049, by rfl⟩ : syracuseStep 673399 = 1010099) B1010099
theorem B673419 : Blo 670310 673419 := bstep (se 1 (by rfl) ⟨505064, by rfl⟩ : syracuseStep 673419 = 1010129) B1010129
theorem B673431 : Blo 670310 673431 := bstep (se 1 (by rfl) ⟨505073, by rfl⟩ : syracuseStep 673431 = 1010147) B1010147
theorem B673451 : Blo 670310 673451 := bstep (se 1 (by rfl) ⟨505088, by rfl⟩ : syracuseStep 673451 = 1010177) B1010177
theorem B673463 : Blo 670310 673463 := bstep (se 1 (by rfl) ⟨505097, by rfl⟩ : syracuseStep 673463 = 1010195) B1010195
theorem B673483 : Blo 670310 673483 := bstep (se 1 (by rfl) ⟨505112, by rfl⟩ : syracuseStep 673483 = 1010225) B1010225
theorem B673495 : Blo 670310 673495 := bstep (se 1 (by rfl) ⟨505121, by rfl⟩ : syracuseStep 673495 = 1010243) B1010243
theorem B673515 : Blo 670310 673515 := bstep (se 1 (by rfl) ⟨505136, by rfl⟩ : syracuseStep 673515 = 1010273) B1010273
theorem B673527 : Blo 670310 673527 := bstep (se 1 (by rfl) ⟨505145, by rfl⟩ : syracuseStep 673527 = 1010291) B1010291
theorem B673547 : Blo 670310 673547 := bstep (se 1 (by rfl) ⟨505160, by rfl⟩ : syracuseStep 673547 = 1010321) B1010321
theorem B5916433 : Blo 670310 5916433 := bstep (se 2 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 5916433 = 4437325) B4437325
theorem B673559 : Blo 670310 673559 := bstep (se 1 (by rfl) ⟨505169, by rfl⟩ : syracuseStep 673559 = 1010339) B1010339
theorem B673579 : Blo 670310 673579 := bstep (se 1 (by rfl) ⟨505184, by rfl⟩ : syracuseStep 673579 = 1010369) B1010369
theorem B673591 : Blo 670310 673591 := bstep (se 1 (by rfl) ⟨505193, by rfl⟩ : syracuseStep 673591 = 1010387) B1010387
theorem B673611 : Blo 670310 673611 := bstep (se 1 (by rfl) ⟨505208, by rfl⟩ : syracuseStep 673611 = 1010417) B1010417
theorem B673623 : Blo 670310 673623 := bstep (se 1 (by rfl) ⟨505217, by rfl⟩ : syracuseStep 673623 = 1010435) B1010435
theorem B673643 : Blo 670310 673643 := bstep (se 1 (by rfl) ⟨505232, by rfl⟩ : syracuseStep 673643 = 1010465) B1010465
theorem B673655 : Blo 670310 673655 := bstep (se 1 (by rfl) ⟨505241, by rfl⟩ : syracuseStep 673655 = 1010483) B1010483
theorem B1132427 : Blo 670310 1132427 := bstep (se 1 (by rfl) ⟨849320, by rfl⟩ : syracuseStep 1132427 = 1698641) B1698641
theorem B673675 : Blo 670310 673675 := bstep (se 1 (by rfl) ⟨505256, by rfl⟩ : syracuseStep 673675 = 1010513) B1010513
theorem B3229591 : Blo 670310 3229591 := bstep (se 1 (by rfl) ⟨2422193, by rfl⟩ : syracuseStep 3229591 = 4844387) B4844387
theorem B673687 : Blo 670310 673687 := bstep (se 1 (by rfl) ⟨505265, by rfl⟩ : syracuseStep 673687 = 1010531) B1010531
theorem B673707 : Blo 670310 673707 := bstep (se 1 (by rfl) ⟨505280, by rfl⟩ : syracuseStep 673707 = 1010561) B1010561
theorem B673719 : Blo 670310 673719 := bstep (se 1 (by rfl) ⟨505289, by rfl⟩ : syracuseStep 673719 = 1010579) B1010579
theorem B673739 : Blo 670310 673739 := bstep (se 1 (by rfl) ⟨505304, by rfl⟩ : syracuseStep 673739 = 1010609) B1010609
theorem B673751 : Blo 670310 673751 := bstep (se 1 (by rfl) ⟨505313, by rfl⟩ : syracuseStep 673751 = 1010627) B1010627
theorem B5457881 : Blo 670310 5457881 := bstep (se 2 (by rfl) ⟨2046705, by rfl⟩ : syracuseStep 5457881 = 4093411) B4093411
theorem B673771 : Blo 670310 673771 := bstep (se 1 (by rfl) ⟨505328, by rfl⟩ : syracuseStep 673771 = 1010657) B1010657
theorem B673783 : Blo 670310 673783 := bstep (se 1 (by rfl) ⟨505337, by rfl⟩ : syracuseStep 673783 = 1010675) B1010675
theorem B1132555 : Blo 670310 1132555 := bstep (se 1 (by rfl) ⟨849416, by rfl⟩ : syracuseStep 1132555 = 1698833) B1698833
theorem B673803 : Blo 670310 673803 := bstep (se 1 (by rfl) ⟨505352, by rfl⟩ : syracuseStep 673803 = 1010705) B1010705
theorem B673815 : Blo 670310 673815 := bstep (se 1 (by rfl) ⟨505361, by rfl⟩ : syracuseStep 673815 = 1010723) B1010723
theorem B673835 : Blo 670310 673835 := bstep (se 1 (by rfl) ⟨505376, by rfl⟩ : syracuseStep 673835 = 1010753) B1010753
theorem B673847 : Blo 670310 673847 := bstep (se 1 (by rfl) ⟨505385, by rfl⟩ : syracuseStep 673847 = 1010771) B1010771
theorem B3819595 : Blo 670310 3819595 := bstep (se 1 (by rfl) ⟨2864696, by rfl⟩ : syracuseStep 3819595 = 5729393) B5729393
theorem B673867 : Blo 670310 673867 := bstep (se 1 (by rfl) ⟨505400, by rfl⟩ : syracuseStep 673867 = 1010801) B1010801
theorem B673879 : Blo 670310 673879 := bstep (se 1 (by rfl) ⟨505409, by rfl⟩ : syracuseStep 673879 = 1010819) B1010819
theorem B673899 : Blo 670310 673899 := bstep (se 1 (by rfl) ⟨505424, by rfl⟩ : syracuseStep 673899 = 1010849) B1010849
theorem B673911 : Blo 670310 673911 := bstep (se 1 (by rfl) ⟨505433, by rfl⟩ : syracuseStep 673911 = 1010867) B1010867
theorem B673931 : Blo 670310 673931 := bstep (se 1 (by rfl) ⟨505448, by rfl⟩ : syracuseStep 673931 = 1010897) B1010897
theorem B673943 : Blo 670310 673943 := bstep (se 1 (by rfl) ⟨505457, by rfl⟩ : syracuseStep 673943 = 1010915) B1010915
theorem B1132697 : Blo 670310 1132697 := bstep (se 2 (by rfl) ⟨424761, by rfl⟩ : syracuseStep 1132697 = 849523) B849523
theorem B673963 : Blo 670310 673963 := bstep (se 1 (by rfl) ⟨505472, by rfl⟩ : syracuseStep 673963 = 1010945) B1010945
theorem B673975 : Blo 670310 673975 := bstep (se 1 (by rfl) ⟨505481, by rfl⟩ : syracuseStep 673975 = 1010963) B1010963
theorem B673995 : Blo 670310 673995 := bstep (se 1 (by rfl) ⟨505496, by rfl⟩ : syracuseStep 673995 = 1010993) B1010993
theorem B674007 : Blo 670310 674007 := bstep (se 1 (by rfl) ⟨505505, by rfl⟩ : syracuseStep 674007 = 1011011) B1011011
theorem B2869465 : Blo 670310 2869465 := bstep (se 2 (by rfl) ⟨1076049, by rfl⟩ : syracuseStep 2869465 = 2152099) B2152099
theorem B674027 : Blo 670310 674027 := bstep (se 1 (by rfl) ⟨505520, by rfl⟩ : syracuseStep 674027 = 1011041) B1011041
theorem B674039 : Blo 670310 674039 := bstep (se 1 (by rfl) ⟨505529, by rfl⟩ : syracuseStep 674039 = 1011059) B1011059
theorem B674059 : Blo 670310 674059 := bstep (se 1 (by rfl) ⟨505544, by rfl⟩ : syracuseStep 674059 = 1011089) B1011089
theorem B674071 : Blo 670310 674071 := bstep (se 1 (by rfl) ⟨505553, by rfl⟩ : syracuseStep 674071 = 1011107) B1011107
theorem B1132825 : Blo 670310 1132825 := bstep (se 2 (by rfl) ⟨424809, by rfl⟩ : syracuseStep 1132825 = 849619) B849619
theorem B674091 : Blo 670310 674091 := bstep (se 1 (by rfl) ⟨505568, by rfl⟩ : syracuseStep 674091 = 1011137) B1011137
theorem B674103 : Blo 670310 674103 := bstep (se 1 (by rfl) ⟨505577, by rfl⟩ : syracuseStep 674103 = 1011155) B1011155
theorem B674123 : Blo 670310 674123 := bstep (se 1 (by rfl) ⟨505592, by rfl⟩ : syracuseStep 674123 = 1011185) B1011185
theorem B674135 : Blo 670310 674135 := bstep (se 1 (by rfl) ⟨505601, by rfl⟩ : syracuseStep 674135 = 1011203) B1011203
theorem B1919321 : Blo 670310 1919321 := bstep (se 2 (by rfl) ⟨719745, by rfl⟩ : syracuseStep 1919321 = 1439491) B1439491
theorem B3819869 : Blo 670310 3819869 := bstep (se 3 (by rfl) ⟨716225, by rfl⟩ : syracuseStep 3819869 = 1432451) B1432451
theorem B4311397 : Blo 670310 4311397 := bstep (se 4 (by rfl) ⟨404193, by rfl⟩ : syracuseStep 4311397 = 808387) B808387
theorem B674155 : Blo 670310 674155 := bstep (se 1 (by rfl) ⟨505616, by rfl⟩ : syracuseStep 674155 = 1011233) B1011233
theorem B674167 : Blo 670310 674167 := bstep (se 1 (by rfl) ⟨505625, by rfl⟩ : syracuseStep 674167 = 1011251) B1011251
theorem B1362305 : Blo 670310 1362305 := bstep (se 2 (by rfl) ⟨510864, by rfl⟩ : syracuseStep 1362305 = 1021729) B1021729
theorem B674187 : Blo 670310 674187 := bstep (se 1 (by rfl) ⟨505640, by rfl⟩ : syracuseStep 674187 = 1011281) B1011281
theorem B674199 : Blo 670310 674199 := bstep (se 1 (by rfl) ⟨505649, by rfl⟩ : syracuseStep 674199 = 1011299) B1011299
theorem B674219 : Blo 670310 674219 := bstep (se 1 (by rfl) ⟨505664, by rfl⟩ : syracuseStep 674219 = 1011329) B1011329
theorem B674231 : Blo 670310 674231 := bstep (se 1 (by rfl) ⟨505673, by rfl⟩ : syracuseStep 674231 = 1011347) B1011347
theorem B674251 : Blo 670310 674251 := bstep (se 1 (by rfl) ⟨505688, by rfl⟩ : syracuseStep 674251 = 1011377) B1011377
theorem B674263 : Blo 670310 674263 := bstep (se 1 (by rfl) ⟨505697, by rfl⟩ : syracuseStep 674263 = 1011395) B1011395
theorem B674283 : Blo 670310 674283 := bstep (se 1 (by rfl) ⟨505712, by rfl⟩ : syracuseStep 674283 = 1011425) B1011425
theorem B674295 : Blo 670310 674295 := bstep (se 1 (by rfl) ⟨505721, by rfl⟩ : syracuseStep 674295 = 1011443) B1011443
theorem B9685655 : Blo 670310 9685655 := bstep (se 1 (by rfl) ⟨7264241, by rfl⟩ : syracuseStep 9685655 = 14528483) B14528483
theorem B1919639 : Blo 670310 1919639 := bstep (se 1 (by rfl) ⟨1439729, by rfl⟩ : syracuseStep 1919639 = 2879459) B2879459
theorem B1821491 : Blo 670310 1821491 := bstep (se 1 (by rfl) ⟨1366118, by rfl⟩ : syracuseStep 1821491 = 2732237) B2732237
theorem B1133399 : Blo 670310 1133399 := bstep (se 1 (by rfl) ⟨850049, by rfl⟩ : syracuseStep 1133399 = 1700099) B1700099
theorem B1133527 : Blo 670310 1133527 := bstep (se 1 (by rfl) ⟨850145, by rfl⟩ : syracuseStep 1133527 = 1700291) B1700291
theorem B5753861 : Blo 670310 5753861 := bstep (se 4 (by rfl) ⟨539424, by rfl⟩ : syracuseStep 5753861 = 1078849) B1078849
theorem B11455505 : Blo 670310 11455505 := bstep (se 2 (by rfl) ⟨4295814, by rfl⟩ : syracuseStep 11455505 = 8591629) B8591629
theorem B2870423 : Blo 670310 2870423 := bstep (se 1 (by rfl) ⟨2152817, by rfl⟩ : syracuseStep 2870423 = 4305635) B4305635
theorem B3395033 : Blo 670310 3395033 := bstep (se 2 (by rfl) ⟨1273137, by rfl⟩ : syracuseStep 3395033 = 2546275) B2546275
theorem B1134155 : Blo 670310 1134155 := bstep (se 1 (by rfl) ⟨850616, by rfl⟩ : syracuseStep 1134155 = 1701233) B1701233
theorem B1134283 : Blo 670310 1134283 := bstep (se 1 (by rfl) ⟨850712, by rfl⟩ : syracuseStep 1134283 = 1701425) B1701425
theorem B3067595 : Blo 670310 3067595 := bstep (se 1 (by rfl) ⟨2300696, by rfl⟩ : syracuseStep 3067595 = 4601393) B4601393
theorem B3067723 : Blo 670310 3067723 := bstep (se 1 (by rfl) ⟨2300792, by rfl⟩ : syracuseStep 3067723 = 4601585) B4601585
theorem B1134425 : Blo 670310 1134425 := bstep (se 2 (by rfl) ⟨425409, by rfl⟩ : syracuseStep 1134425 = 850819) B850819
theorem B806807 : Blo 670310 806807 := bstep (se 1 (by rfl) ⟨605105, by rfl⟩ : syracuseStep 806807 = 1210211) B1210211
theorem B1134553 : Blo 670310 1134553 := bstep (se 2 (by rfl) ⟨425457, by rfl⟩ : syracuseStep 1134553 = 850915) B850915
theorem B5460119 : Blo 670310 5460119 := bstep (se 1 (by rfl) ⟨4095089, by rfl⟩ : syracuseStep 5460119 = 8190179) B8190179
theorem B4837637 : Blo 670310 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B4084069 : Blo 670310 4084069 := bstep (se 4 (by rfl) ⟨382881, by rfl⟩ : syracuseStep 4084069 = 765763) B765763
theorem B3887461 : Blo 670310 3887461 := bstep (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) B728899
theorem B1135127 : Blo 670310 1135127 := bstep (se 1 (by rfl) ⟨851345, by rfl⟩ : syracuseStep 1135127 = 1702691) B1702691
theorem B807499 : Blo 670310 807499 := bstep (se 1 (by rfl) ⟨605624, by rfl⟩ : syracuseStep 807499 = 1211249) B1211249
theorem B1135255 : Blo 670310 1135255 := bstep (se 1 (by rfl) ⟨851441, by rfl⟩ : syracuseStep 1135255 = 1702883) B1702883
theorem B3068761 : Blo 670310 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B4608899 : Blo 670310 4608899 := bstep (se 1 (by rfl) ⟨3456674, by rfl⟩ : syracuseStep 4608899 = 6913349) B6913349
theorem B3396653 : Blo 670310 3396653 := bstep (se 3 (by rfl) ⟨636872, by rfl⟩ : syracuseStep 3396653 = 1273745) B1273745
theorem B2872523 : Blo 670310 2872523 := bstep (se 1 (by rfl) ⟨2154392, by rfl⟩ : syracuseStep 2872523 = 4308785) B4308785
theorem B1135883 : Blo 670310 1135883 := bstep (se 1 (by rfl) ⟨851912, by rfl⟩ : syracuseStep 1135883 = 1703825) B1703825
theorem B1136011 : Blo 670310 1136011 := bstep (se 1 (by rfl) ⟨852008, by rfl⟩ : syracuseStep 1136011 = 1704017) B1704017
theorem B8640017 : Blo 670310 8640017 := bstep (se 2 (by rfl) ⟨3240006, by rfl⟩ : syracuseStep 8640017 = 6480013) B6480013
theorem B1136153 : Blo 670310 1136153 := bstep (se 2 (by rfl) ⟨426057, by rfl⟩ : syracuseStep 1136153 = 852115) B852115
theorem B2545303 : Blo 670310 2545303 := bstep (se 1 (by rfl) ⟨1908977, by rfl⟩ : syracuseStep 2545303 = 3817955) B3817955
theorem B1136281 : Blo 670310 1136281 := bstep (se 2 (by rfl) ⟨426105, by rfl⟩ : syracuseStep 1136281 = 852211) B852211
theorem B972697 : Blo 670310 972697 := bstep (se 2 (by rfl) ⟨364761, by rfl⟩ : syracuseStep 972697 = 729523) B729523
theorem B1005515 : Blo 670310 1005515 := bstep (se 1 (by rfl) ⟨754136, by rfl⟩ : syracuseStep 1005515 = 1508273) B1508273
theorem B1005527 : Blo 670310 1005527 := bstep (se 1 (by rfl) ⟨754145, by rfl⟩ : syracuseStep 1005527 = 1508291) B1508291
theorem B1005593 : Blo 670310 1005593 := bstep (se 2 (by rfl) ⟨377097, by rfl⟩ : syracuseStep 1005593 = 754195) B754195
theorem B1005707 : Blo 670310 1005707 := bstep (se 1 (by rfl) ⟨754280, by rfl⟩ : syracuseStep 1005707 = 1508561) B1508561
theorem B907403 : Blo 670310 907403 := bstep (se 1 (by rfl) ⟨680552, by rfl⟩ : syracuseStep 907403 = 1361105) B1361105
theorem B1005719 : Blo 670310 1005719 := bstep (se 1 (by rfl) ⟨754289, by rfl⟩ : syracuseStep 1005719 = 1508579) B1508579
theorem B1136855 : Blo 670310 1136855 := bstep (se 1 (by rfl) ⟨852641, by rfl⟩ : syracuseStep 1136855 = 1705283) B1705283
theorem B1005785 : Blo 670310 1005785 := bstep (se 2 (by rfl) ⟨377169, by rfl⟩ : syracuseStep 1005785 = 754339) B754339
theorem B2152727 : Blo 670310 2152727 := bstep (se 1 (by rfl) ⟨1614545, by rfl⟩ : syracuseStep 2152727 = 3229091) B3229091
theorem B1005899 : Blo 670310 1005899 := bstep (se 1 (by rfl) ⟨754424, by rfl⟩ : syracuseStep 1005899 = 1508849) B1508849
theorem B809291 : Blo 670310 809291 := bstep (se 1 (by rfl) ⟨606968, by rfl⟩ : syracuseStep 809291 = 1213937) B1213937
theorem B1005911 : Blo 670310 1005911 := bstep (se 1 (by rfl) ⟨754433, by rfl⟩ : syracuseStep 1005911 = 1508867) B1508867
theorem B842071 : Blo 670310 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B1136983 : Blo 670310 1136983 := bstep (se 1 (by rfl) ⟨852737, by rfl⟩ : syracuseStep 1136983 = 1705475) B1705475
theorem B5757277 : Blo 670310 5757277 := bstep (se 3 (by rfl) ⟨1079489, by rfl⟩ : syracuseStep 5757277 = 2158979) B2158979
theorem B49174901 : Blo 670310 49174901 := bstep (se 5 (by rfl) ⟨2305073, by rfl⟩ : syracuseStep 49174901 = 4610147) B4610147
theorem B874903 : Blo 670310 874903 := bstep (se 1 (by rfl) ⟨656177, by rfl⟩ : syracuseStep 874903 = 1312355) B1312355
theorem B1005977 : Blo 670310 1005977 := bstep (se 2 (by rfl) ⟨377241, by rfl⟩ : syracuseStep 1005977 = 754483) B754483
theorem B2546093 : Blo 670310 2546093 := bstep (se 3 (by rfl) ⟨477392, by rfl⟩ : syracuseStep 2546093 = 954785) B954785
theorem B1432075 : Blo 670310 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B1006091 : Blo 670310 1006091 := bstep (se 1 (by rfl) ⟨754568, by rfl⟩ : syracuseStep 1006091 = 1509137) B1509137
theorem B1006103 : Blo 670310 1006103 := bstep (se 1 (by rfl) ⟨754577, by rfl⟩ : syracuseStep 1006103 = 1509155) B1509155
theorem B1006169 : Blo 670310 1006169 := bstep (se 2 (by rfl) ⟨377313, by rfl⟩ : syracuseStep 1006169 = 754627) B754627
theorem B1006283 : Blo 670310 1006283 := bstep (se 1 (by rfl) ⟨754712, by rfl⟩ : syracuseStep 1006283 = 1509425) B1509425
theorem B1006295 : Blo 670310 1006295 := bstep (se 1 (by rfl) ⟨754721, by rfl⟩ : syracuseStep 1006295 = 1509443) B1509443
theorem B50420465 : Blo 670310 50420465 := bstep (se 2 (by rfl) ⟨18907674, by rfl⟩ : syracuseStep 50420465 = 37815349) B37815349
theorem B1366807 : Blo 670310 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B1006361 : Blo 670310 1006361 := bstep (se 2 (by rfl) ⟨377385, by rfl⟩ : syracuseStep 1006361 = 754771) B754771
theorem B2874163 : Blo 670310 2874163 := bstep (se 1 (by rfl) ⟨2155622, by rfl⟩ : syracuseStep 2874163 = 4311245) B4311245
theorem B1006475 : Blo 670310 1006475 := bstep (se 1 (by rfl) ⟨754856, by rfl⟩ : syracuseStep 1006475 = 1509713) B1509713
theorem B1006487 : Blo 670310 1006487 := bstep (se 1 (by rfl) ⟨754865, by rfl⟩ : syracuseStep 1006487 = 1509731) B1509731
theorem B5102513 : Blo 670310 5102513 := bstep (se 2 (by rfl) ⟨1913442, by rfl⟩ : syracuseStep 5102513 = 3826885) B3826885
theorem B1727411 : Blo 670310 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B1137611 : Blo 670310 1137611 := bstep (se 1 (by rfl) ⟨853208, by rfl⟩ : syracuseStep 1137611 = 1706417) B1706417
theorem B1006553 : Blo 670310 1006553 := bstep (se 2 (by rfl) ⟨377457, by rfl⟩ : syracuseStep 1006553 = 754915) B754915
theorem B3070993 : Blo 670310 3070993 := bstep (se 2 (by rfl) ⟨1151622, by rfl⟩ : syracuseStep 3070993 = 2303245) B2303245
theorem B6478865 : Blo 670310 6478865 := bstep (se 2 (by rfl) ⟨2429574, by rfl⟩ : syracuseStep 6478865 = 4859149) B4859149
theorem B3071027 : Blo 670310 3071027 := bstep (se 1 (by rfl) ⟨2303270, by rfl⟩ : syracuseStep 3071027 = 4606541) B4606541
theorem B1006667 : Blo 670310 1006667 := bstep (se 1 (by rfl) ⟨755000, by rfl⟩ : syracuseStep 1006667 = 1510001) B1510001
theorem B1137739 : Blo 670310 1137739 := bstep (se 1 (by rfl) ⟨853304, by rfl⟩ : syracuseStep 1137739 = 1706609) B1706609
theorem B1006679 : Blo 670310 1006679 := bstep (se 1 (by rfl) ⟨755009, by rfl⟩ : syracuseStep 1006679 = 1510019) B1510019
theorem B8313949 : Blo 670310 8313949 := bstep (se 3 (by rfl) ⟨1558865, by rfl⟩ : syracuseStep 8313949 = 3117731) B3117731
theorem B1006745 : Blo 670310 1006745 := bstep (se 2 (by rfl) ⟨377529, by rfl⟩ : syracuseStep 1006745 = 755059) B755059
theorem B1137881 : Blo 670310 1137881 := bstep (se 2 (by rfl) ⟨426705, by rfl⟩ : syracuseStep 1137881 = 853411) B853411
theorem B1432819 : Blo 670310 1432819 := bstep (se 1 (by rfl) ⟨1074614, by rfl⟩ : syracuseStep 1432819 = 2149229) B2149229
theorem B1006859 : Blo 670310 1006859 := bstep (se 1 (by rfl) ⟨755144, by rfl⟩ : syracuseStep 1006859 = 1510289) B1510289
theorem B1006871 : Blo 670310 1006871 := bstep (se 1 (by rfl) ⟨755153, by rfl⟩ : syracuseStep 1006871 = 1510307) B1510307
theorem B2153803 : Blo 670310 2153803 := bstep (se 1 (by rfl) ⟨1615352, by rfl⟩ : syracuseStep 2153803 = 3230705) B3230705
theorem B1006937 : Blo 670310 1006937 := bstep (se 2 (by rfl) ⟨377601, by rfl⟩ : syracuseStep 1006937 = 755203) B755203
theorem B5102999 : Blo 670310 5102999 := bstep (se 1 (by rfl) ⟨3827249, by rfl⟩ : syracuseStep 5102999 = 7654499) B7654499
theorem B2874797 : Blo 670310 2874797 := bstep (se 3 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 2874797 = 1078049) B1078049
theorem B1007051 : Blo 670310 1007051 := bstep (se 1 (by rfl) ⟨755288, by rfl⟩ : syracuseStep 1007051 = 1510577) B1510577
theorem B1007063 : Blo 670310 1007063 := bstep (se 1 (by rfl) ⟨755297, by rfl⟩ : syracuseStep 1007063 = 1510595) B1510595
theorem B2153945 : Blo 670310 2153945 := bstep (se 2 (by rfl) ⟨807729, by rfl⟩ : syracuseStep 2153945 = 1615459) B1615459
theorem B2448899 : Blo 670310 2448899 := bstep (se 1 (by rfl) ⟨1836674, by rfl⟩ : syracuseStep 2448899 = 3673349) B3673349
theorem B1007129 : Blo 670310 1007129 := bstep (se 2 (by rfl) ⟨377673, by rfl⟩ : syracuseStep 1007129 = 755347) B755347
theorem B3235393 : Blo 670310 3235393 := bstep (se 2 (by rfl) ⟨1213272, by rfl⟩ : syracuseStep 3235393 = 2426545) B2426545
theorem B3825245 : Blo 670310 3825245 := bstep (se 3 (by rfl) ⟨717233, by rfl⟩ : syracuseStep 3825245 = 1434467) B1434467
theorem B1007243 : Blo 670310 1007243 := bstep (se 1 (by rfl) ⟨755432, by rfl⟩ : syracuseStep 1007243 = 1510865) B1510865
theorem B1007255 : Blo 670310 1007255 := bstep (se 1 (by rfl) ⟨755441, by rfl⟩ : syracuseStep 1007255 = 1510883) B1510883
theorem B1433305 : Blo 670310 1433305 := bstep (se 2 (by rfl) ⟨537489, by rfl⟩ : syracuseStep 1433305 = 1074979) B1074979
theorem B1007321 : Blo 670310 1007321 := bstep (se 2 (by rfl) ⟨377745, by rfl⟩ : syracuseStep 1007321 = 755491) B755491
theorem B2547521 : Blo 670310 2547521 := bstep (se 2 (by rfl) ⟨955320, by rfl⟩ : syracuseStep 2547521 = 1910641) B1910641
theorem B1007435 : Blo 670310 1007435 := bstep (se 1 (by rfl) ⟨755576, by rfl⟩ : syracuseStep 1007435 = 1511153) B1511153
theorem B1007447 : Blo 670310 1007447 := bstep (se 1 (by rfl) ⟨755585, by rfl⟩ : syracuseStep 1007447 = 1511171) B1511171
theorem B3628901 : Blo 670310 3628901 := bstep (se 4 (by rfl) ⟨340209, by rfl⟩ : syracuseStep 3628901 = 680419) B680419
theorem B1007513 : Blo 670310 1007513 := bstep (se 2 (by rfl) ⟨377817, by rfl⟩ : syracuseStep 1007513 = 755635) B755635
theorem B1007627 : Blo 670310 1007627 := bstep (se 1 (by rfl) ⟨755720, by rfl⟩ : syracuseStep 1007627 = 1511441) B1511441
theorem B1007639 : Blo 670310 1007639 := bstep (se 1 (by rfl) ⟨755729, by rfl⟩ : syracuseStep 1007639 = 1511459) B1511459
theorem B1007705 : Blo 670310 1007705 := bstep (se 2 (by rfl) ⟨377889, by rfl⟩ : syracuseStep 1007705 = 755779) B755779
theorem B1007819 : Blo 670310 1007819 := bstep (se 1 (by rfl) ⟨755864, by rfl⟩ : syracuseStep 1007819 = 1511729) B1511729
theorem B1532119 : Blo 670310 1532119 := bstep (se 1 (by rfl) ⟨1149089, by rfl⟩ : syracuseStep 1532119 = 2298179) B2298179
theorem B1007831 : Blo 670310 1007831 := bstep (se 1 (by rfl) ⟨755873, by rfl⟩ : syracuseStep 1007831 = 1511747) B1511747
theorem B1007897 : Blo 670310 1007897 := bstep (se 2 (by rfl) ⟨377961, by rfl⟩ : syracuseStep 1007897 = 755923) B755923
theorem B1008011 : Blo 670310 1008011 := bstep (se 1 (by rfl) ⟨756008, by rfl⟩ : syracuseStep 1008011 = 1512017) B1512017
theorem B1008023 : Blo 670310 1008023 := bstep (se 1 (by rfl) ⟨756017, by rfl⟩ : syracuseStep 1008023 = 1512035) B1512035
theorem B1008089 : Blo 670310 1008089 := bstep (se 2 (by rfl) ⟨378033, by rfl⟩ : syracuseStep 1008089 = 756067) B756067
theorem B1008203 : Blo 670310 1008203 := bstep (se 1 (by rfl) ⟨756152, by rfl⟩ : syracuseStep 1008203 = 1512305) B1512305
theorem B1008215 : Blo 670310 1008215 := bstep (se 1 (by rfl) ⟨756161, by rfl⟩ : syracuseStep 1008215 = 1512323) B1512323
theorem B1008281 : Blo 670310 1008281 := bstep (se 2 (by rfl) ⟨378105, by rfl⟩ : syracuseStep 1008281 = 756211) B756211
theorem B2155187 : Blo 670310 2155187 := bstep (se 1 (by rfl) ⟨1616390, by rfl⟩ : syracuseStep 2155187 = 3232781) B3232781
theorem B3629785 : Blo 670310 3629785 := bstep (se 2 (by rfl) ⟨1361169, by rfl⟩ : syracuseStep 3629785 = 2722339) B2722339
theorem B1008395 : Blo 670310 1008395 := bstep (se 1 (by rfl) ⟨756296, by rfl⟩ : syracuseStep 1008395 = 1512593) B1512593
theorem B1532695 : Blo 670310 1532695 := bstep (se 1 (by rfl) ⟨1149521, by rfl⟩ : syracuseStep 1532695 = 2299043) B2299043
theorem B1008407 : Blo 670310 1008407 := bstep (se 1 (by rfl) ⟨756305, by rfl⟩ : syracuseStep 1008407 = 1512611) B1512611
theorem B1008473 : Blo 670310 1008473 := bstep (se 2 (by rfl) ⟨378177, by rfl⟩ : syracuseStep 1008473 = 756355) B756355
theorem B3400541 : Blo 670310 3400541 := bstep (se 3 (by rfl) ⟨637601, by rfl⟩ : syracuseStep 3400541 = 1275203) B1275203
theorem B2581379 : Blo 670310 2581379 := bstep (se 1 (by rfl) ⟨1936034, by rfl⟩ : syracuseStep 2581379 = 3872069) B3872069
theorem B1008587 : Blo 670310 1008587 := bstep (se 1 (by rfl) ⟨756440, by rfl⟩ : syracuseStep 1008587 = 1512881) B1512881
theorem B1008599 : Blo 670310 1008599 := bstep (se 1 (by rfl) ⟨756449, by rfl⟩ : syracuseStep 1008599 = 1512899) B1512899
theorem B1008665 : Blo 670310 1008665 := bstep (se 2 (by rfl) ⟨378249, by rfl⟩ : syracuseStep 1008665 = 756499) B756499
theorem B2155585 : Blo 670310 2155585 := bstep (se 2 (by rfl) ⟨808344, by rfl⟩ : syracuseStep 2155585 = 1616689) B1616689
theorem B16311365 : Blo 670310 16311365 := bstep (se 4 (by rfl) ⟨1529190, by rfl⟩ : syracuseStep 16311365 = 3058381) B3058381
theorem B1008779 : Blo 670310 1008779 := bstep (se 1 (by rfl) ⟨756584, by rfl⟩ : syracuseStep 1008779 = 1513169) B1513169
theorem B1434775 : Blo 670310 1434775 := bstep (se 1 (by rfl) ⟨1076081, by rfl⟩ : syracuseStep 1434775 = 2152163) B2152163
theorem B1008791 : Blo 670310 1008791 := bstep (se 1 (by rfl) ⟨756593, by rfl⟩ : syracuseStep 1008791 = 1513187) B1513187
theorem B1434827 : Blo 670310 1434827 := bstep (se 1 (by rfl) ⟨1076120, by rfl⟩ : syracuseStep 1434827 = 2152241) B2152241
theorem B1008857 : Blo 670310 1008857 := bstep (se 2 (by rfl) ⟨378321, by rfl⟩ : syracuseStep 1008857 = 756643) B756643
theorem B2549009 : Blo 670310 2549009 := bstep (se 2 (by rfl) ⟨955878, by rfl⟩ : syracuseStep 2549009 = 1911757) B1911757
theorem B1008971 : Blo 670310 1008971 := bstep (se 1 (by rfl) ⟨756728, by rfl⟩ : syracuseStep 1008971 = 1513457) B1513457
theorem B1008983 : Blo 670310 1008983 := bstep (se 1 (by rfl) ⟨756737, by rfl⟩ : syracuseStep 1008983 = 1513475) B1513475
theorem B1009049 : Blo 670310 1009049 := bstep (se 2 (by rfl) ⟨378393, by rfl⟩ : syracuseStep 1009049 = 756787) B756787
theorem B1009163 : Blo 670310 1009163 := bstep (se 1 (by rfl) ⟨756872, by rfl⟩ : syracuseStep 1009163 = 1513745) B1513745
theorem B1009175 : Blo 670310 1009175 := bstep (se 1 (by rfl) ⟨756881, by rfl⟩ : syracuseStep 1009175 = 1513763) B1513763
theorem B1697345 : Blo 670310 1697345 := bstep (se 2 (by rfl) ⟨636504, by rfl⟩ : syracuseStep 1697345 = 1273009) B1273009
theorem B1009241 : Blo 670310 1009241 := bstep (se 2 (by rfl) ⟨378465, by rfl⟩ : syracuseStep 1009241 = 756931) B756931
theorem B1009355 : Blo 670310 1009355 := bstep (se 1 (by rfl) ⟨757016, by rfl⟩ : syracuseStep 1009355 = 1514033) B1514033
theorem B1009367 : Blo 670310 1009367 := bstep (se 1 (by rfl) ⟨757025, by rfl⟩ : syracuseStep 1009367 = 1514051) B1514051
theorem B2549465 : Blo 670310 2549465 := bstep (se 2 (by rfl) ⟨956049, by rfl⟩ : syracuseStep 2549465 = 1912099) B1912099
theorem B1009433 : Blo 670310 1009433 := bstep (se 2 (by rfl) ⟨378537, by rfl⟩ : syracuseStep 1009433 = 757075) B757075
theorem B1009547 : Blo 670310 1009547 := bstep (se 1 (by rfl) ⟨757160, by rfl⟩ : syracuseStep 1009547 = 1514321) B1514321
theorem B1009559 : Blo 670310 1009559 := bstep (se 1 (by rfl) ⟨757169, by rfl⟩ : syracuseStep 1009559 = 1514339) B1514339
theorem B2549677 : Blo 670310 2549677 := bstep (se 3 (by rfl) ⟨478064, by rfl⟩ : syracuseStep 2549677 = 956129) B956129
theorem B1009625 : Blo 670310 1009625 := bstep (se 2 (by rfl) ⟨378609, by rfl⟩ : syracuseStep 1009625 = 757219) B757219
theorem B3631169 : Blo 670310 3631169 := bstep (se 2 (by rfl) ⟨1361688, by rfl⟩ : syracuseStep 3631169 = 2723377) B2723377
theorem B1009739 : Blo 670310 1009739 := bstep (se 1 (by rfl) ⟨757304, by rfl⟩ : syracuseStep 1009739 = 1514609) B1514609
theorem B1009751 : Blo 670310 1009751 := bstep (se 1 (by rfl) ⟨757313, by rfl⟩ : syracuseStep 1009751 = 1514627) B1514627
theorem B1697881 : Blo 670310 1697881 := bstep (se 2 (by rfl) ⟨636705, by rfl⟩ : syracuseStep 1697881 = 1273411) B1273411
theorem B3827843 : Blo 670310 3827843 := bstep (se 1 (by rfl) ⟨2870882, by rfl⟩ : syracuseStep 3827843 = 5741765) B5741765
theorem B1075351 : Blo 670310 1075351 := bstep (se 1 (by rfl) ⟨806513, by rfl⟩ : syracuseStep 1075351 = 1613027) B1613027
theorem B1009817 : Blo 670310 1009817 := bstep (se 2 (by rfl) ⟨378681, by rfl⟩ : syracuseStep 1009817 = 757363) B757363
theorem B2615513 : Blo 670310 2615513 := bstep (se 2 (by rfl) ⟨980817, by rfl⟩ : syracuseStep 2615513 = 1961635) B1961635
theorem B2549981 : Blo 670310 2549981 := bstep (se 3 (by rfl) ⟨478121, by rfl⟩ : syracuseStep 2549981 = 956243) B956243
theorem B1009931 : Blo 670310 1009931 := bstep (se 1 (by rfl) ⟨757448, by rfl⟩ : syracuseStep 1009931 = 1514897) B1514897
theorem B1009943 : Blo 670310 1009943 := bstep (se 1 (by rfl) ⟨757457, by rfl⟩ : syracuseStep 1009943 = 1514915) B1514915
theorem B6121763 : Blo 670310 6121763 := bstep (se 1 (by rfl) ⟨4591322, by rfl⟩ : syracuseStep 6121763 = 9182645) B9182645
theorem B1010009 : Blo 670310 1010009 := bstep (se 2 (by rfl) ⟨378753, by rfl⟩ : syracuseStep 1010009 = 757507) B757507
theorem B5728643 : Blo 670310 5728643 := bstep (se 1 (by rfl) ⟨4296482, by rfl⟩ : syracuseStep 5728643 = 8592965) B8592965
theorem B1010123 : Blo 670310 1010123 := bstep (se 1 (by rfl) ⟨757592, by rfl⟩ : syracuseStep 1010123 = 1515185) B1515185
theorem B1010135 : Blo 670310 1010135 := bstep (se 1 (by rfl) ⟨757601, by rfl⟩ : syracuseStep 1010135 = 1515203) B1515203
theorem B1010201 : Blo 670310 1010201 := bstep (se 2 (by rfl) ⟨378825, by rfl⟩ : syracuseStep 1010201 = 757651) B757651
theorem B1075799 : Blo 670310 1075799 := bstep (se 1 (by rfl) ⟨806849, by rfl⟩ : syracuseStep 1075799 = 1613699) B1613699
theorem B1010315 : Blo 670310 1010315 := bstep (se 1 (by rfl) ⟨757736, by rfl⟩ : syracuseStep 1010315 = 1515473) B1515473
theorem B5171863 : Blo 670310 5171863 := bstep (se 1 (by rfl) ⟨3878897, by rfl⟩ : syracuseStep 5171863 = 7757795) B7757795
theorem B1010327 : Blo 670310 1010327 := bstep (se 1 (by rfl) ⟨757745, by rfl⟩ : syracuseStep 1010327 = 1515491) B1515491
theorem B1010393 : Blo 670310 1010393 := bstep (se 2 (by rfl) ⟨378897, by rfl⟩ : syracuseStep 1010393 = 757795) B757795
theorem B1075979 : Blo 670310 1075979 := bstep (se 1 (by rfl) ⟨806984, by rfl⟩ : syracuseStep 1075979 = 1613969) B1613969
theorem B1436467 : Blo 670310 1436467 := bstep (se 1 (by rfl) ⟨1077350, by rfl⟩ : syracuseStep 1436467 = 2154701) B2154701
theorem B1010507 : Blo 670310 1010507 := bstep (se 1 (by rfl) ⟨757880, by rfl⟩ : syracuseStep 1010507 = 1515761) B1515761
theorem B1010519 : Blo 670310 1010519 := bstep (se 1 (by rfl) ⟨757889, by rfl⟩ : syracuseStep 1010519 = 1515779) B1515779
theorem B1076107 : Blo 670310 1076107 := bstep (se 1 (by rfl) ⟨807080, by rfl⟩ : syracuseStep 1076107 = 1614161) B1614161
theorem B3402647 : Blo 670310 3402647 := bstep (se 1 (by rfl) ⟨2551985, by rfl⟩ : syracuseStep 3402647 = 5103971) B5103971
theorem B1010585 : Blo 670310 1010585 := bstep (se 2 (by rfl) ⟨378969, by rfl⟩ : syracuseStep 1010585 = 757939) B757939
theorem B19360691 : Blo 670310 19360691 := bstep (se 1 (by rfl) ⟨14520518, by rfl⟩ : syracuseStep 19360691 = 29041037) B29041037
theorem B1534913 : Blo 670310 1534913 := bstep (se 2 (by rfl) ⟨575592, by rfl⟩ : syracuseStep 1534913 = 1151185) B1151185
theorem B1076171 : Blo 670310 1076171 := bstep (se 1 (by rfl) ⟨807128, by rfl⟩ : syracuseStep 1076171 = 1614257) B1614257
theorem B1010699 : Blo 670310 1010699 := bstep (se 1 (by rfl) ⟨758024, by rfl⟩ : syracuseStep 1010699 = 1516049) B1516049
theorem B1010711 : Blo 670310 1010711 := bstep (se 1 (by rfl) ⟨758033, by rfl⟩ : syracuseStep 1010711 = 1516067) B1516067
theorem B2878487 : Blo 670310 2878487 := bstep (se 1 (by rfl) ⟨2158865, by rfl⟩ : syracuseStep 2878487 = 4317731) B4317731
theorem B1010777 : Blo 670310 1010777 := bstep (se 2 (by rfl) ⟨379041, by rfl⟩ : syracuseStep 1010777 = 758083) B758083
theorem B1272971 : Blo 670310 1272971 := bstep (se 1 (by rfl) ⟨954728, by rfl⟩ : syracuseStep 1272971 = 1909457) B1909457
theorem B1436825 : Blo 670310 1436825 := bstep (se 2 (by rfl) ⟨538809, by rfl⟩ : syracuseStep 1436825 = 1077619) B1077619
theorem B1633459 : Blo 670310 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B1698995 : Blo 670310 1698995 := bstep (se 1 (by rfl) ⟨1274246, by rfl⟩ : syracuseStep 1698995 = 2548493) B2548493
theorem B1010891 : Blo 670310 1010891 := bstep (se 1 (by rfl) ⟨758168, by rfl⟩ : syracuseStep 1010891 = 1516337) B1516337
theorem B1010903 : Blo 670310 1010903 := bstep (se 1 (by rfl) ⟨758177, by rfl⟩ : syracuseStep 1010903 = 1516355) B1516355
theorem B1535257 : Blo 670310 1535257 := bstep (se 2 (by rfl) ⟨575721, by rfl⟩ : syracuseStep 1535257 = 1151443) B1151443
theorem B1010969 : Blo 670310 1010969 := bstep (se 2 (by rfl) ⟨379113, by rfl⟩ : syracuseStep 1010969 = 758227) B758227
theorem B1273153 : Blo 670310 1273153 := bstep (se 2 (by rfl) ⟨477432, by rfl⟩ : syracuseStep 1273153 = 954865) B954865
theorem B1011083 : Blo 670310 1011083 := bstep (se 1 (by rfl) ⟨758312, by rfl⟩ : syracuseStep 1011083 = 1516625) B1516625
theorem B1011095 : Blo 670310 1011095 := bstep (se 1 (by rfl) ⟨758321, by rfl⟩ : syracuseStep 1011095 = 1516643) B1516643
theorem B1699289 : Blo 670310 1699289 := bstep (se 2 (by rfl) ⟨637233, by rfl⟩ : syracuseStep 1699289 = 1274467) B1274467
theorem B1011161 : Blo 670310 1011161 := bstep (se 2 (by rfl) ⟨379185, by rfl⟩ : syracuseStep 1011161 = 758371) B758371
theorem B716311 : Blo 670310 716311 := bstep (se 1 (by rfl) ⟨537233, by rfl⟩ : syracuseStep 716311 = 1074467) B1074467
theorem B1011275 : Blo 670310 1011275 := bstep (se 1 (by rfl) ⟨758456, by rfl⟩ : syracuseStep 1011275 = 1516913) B1516913
theorem B1011287 : Blo 670310 1011287 := bstep (se 1 (by rfl) ⟨758465, by rfl⟩ : syracuseStep 1011287 = 1516931) B1516931
theorem B1273495 : Blo 670310 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B1011353 : Blo 670310 1011353 := bstep (se 2 (by rfl) ⟨379257, by rfl⟩ : syracuseStep 1011353 = 758515) B758515
theorem B1273715 : Blo 670310 1273715 := bstep (se 1 (by rfl) ⟨955286, by rfl⟩ : syracuseStep 1273715 = 1910573) B1910573
theorem B716683 : Blo 670310 716683 := bstep (se 1 (by rfl) ⟨537512, by rfl⟩ : syracuseStep 716683 = 1075025) B1075025
theorem B1273943 : Blo 670310 1273943 := bstep (se 1 (by rfl) ⟨955457, by rfl⟩ : syracuseStep 1273943 = 1910915) B1910915
theorem B1077337 : Blo 670310 1077337 := bstep (se 2 (by rfl) ⟨404001, by rfl⟩ : syracuseStep 1077337 = 808003) B808003
theorem B3633245 : Blo 670310 3633245 := bstep (se 3 (by rfl) ⟨681233, by rfl⟩ : syracuseStep 3633245 = 1362467) B1362467
theorem B717131 : Blo 670310 717131 := bstep (se 1 (by rfl) ⟨537848, by rfl⟩ : syracuseStep 717131 = 1075697) B1075697
theorem B1274201 : Blo 670310 1274201 := bstep (se 2 (by rfl) ⟨477825, by rfl⟩ : syracuseStep 1274201 = 955651) B955651
theorem B1536371 : Blo 670310 1536371 := bstep (se 1 (by rfl) ⟨1152278, by rfl⟩ : syracuseStep 1536371 = 2304557) B2304557
theorem B1536499 : Blo 670310 1536499 := bstep (se 1 (by rfl) ⟨1152374, by rfl⟩ : syracuseStep 1536499 = 2304749) B2304749
theorem B5731033 : Blo 670310 5731033 := bstep (se 2 (by rfl) ⟨2149137, by rfl⟩ : syracuseStep 5731033 = 4298275) B4298275
theorem B1274611 : Blo 670310 1274611 := bstep (se 1 (by rfl) ⟨955958, by rfl⟩ : syracuseStep 1274611 = 1911917) B1911917
theorem B2552579 : Blo 670310 2552579 := bstep (se 1 (by rfl) ⟨1914434, by rfl⟩ : syracuseStep 2552579 = 3828869) B3828869
theorem B2552593 : Blo 670310 2552593 := bstep (se 2 (by rfl) ⟨957222, by rfl⟩ : syracuseStep 2552593 = 1914445) B1914445
theorem B2552897 : Blo 670310 2552897 := bstep (se 2 (by rfl) ⟨957336, by rfl⟩ : syracuseStep 2552897 = 1914673) B1914673
theorem B848971 : Blo 670310 848971 := bstep (se 1 (by rfl) ⟨636728, by rfl⟩ : syracuseStep 848971 = 1273457) B1273457
theorem B1700939 : Blo 670310 1700939 := bstep (se 1 (by rfl) ⟨1275704, by rfl⟩ : syracuseStep 1700939 = 2551409) B2551409
theorem B1438859 : Blo 670310 1438859 := bstep (se 1 (by rfl) ⟨1079144, by rfl⟩ : syracuseStep 1438859 = 2158289) B2158289
theorem B1275097 : Blo 670310 1275097 := bstep (se 2 (by rfl) ⟨478161, by rfl⟩ : syracuseStep 1275097 = 956323) B956323
theorem B2585945 : Blo 670310 2585945 := bstep (se 2 (by rfl) ⟨969729, by rfl⟩ : syracuseStep 2585945 = 1939459) B1939459
theorem B9696611 : Blo 670310 9696611 := bstep (se 1 (by rfl) ⟨7272458, by rfl⟩ : syracuseStep 9696611 = 14544917) B14544917
theorem B718327 : Blo 670310 718327 := bstep (se 1 (by rfl) ⟨538745, by rfl⟩ : syracuseStep 718327 = 1077491) B1077491
theorem B5731991 : Blo 670310 5731991 := bstep (se 1 (by rfl) ⟨4298993, by rfl⟩ : syracuseStep 5731991 = 8597987) B8597987
theorem B718507 : Blo 670310 718507 := bstep (se 1 (by rfl) ⟨538880, by rfl⟩ : syracuseStep 718507 = 1077761) B1077761
theorem B2553565 : Blo 670310 2553565 := bstep (se 3 (by rfl) ⟨478793, by rfl⟩ : syracuseStep 2553565 = 957587) B957587
theorem B1275659 : Blo 670310 1275659 := bstep (se 1 (by rfl) ⟨956744, by rfl⟩ : syracuseStep 1275659 = 1913489) B1913489
theorem B1275841 : Blo 670310 1275841 := bstep (se 2 (by rfl) ⟨478440, by rfl⟩ : syracuseStep 1275841 = 956881) B956881
theorem B5732369 : Blo 670310 5732369 := bstep (se 2 (by rfl) ⟨2149638, by rfl⟩ : syracuseStep 5732369 = 4299277) B4299277
theorem B849943 : Blo 670310 849943 := bstep (se 1 (by rfl) ⟨637457, by rfl⟩ : syracuseStep 849943 = 1274915) B1274915
theorem B1701911 : Blo 670310 1701911 := bstep (se 1 (by rfl) ⟨1276433, by rfl⟩ : syracuseStep 1701911 = 2552867) B2552867
theorem B1440089 : Blo 670310 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B3406211 : Blo 670310 3406211 := bstep (se 1 (by rfl) ⟨2554658, by rfl⟩ : syracuseStep 3406211 = 5109317) B5109317
theorem B5110289 : Blo 670310 5110289 := bstep (se 2 (by rfl) ⟨1916358, by rfl⟩ : syracuseStep 5110289 = 3832717) B3832717
theorem B4094509 : Blo 670310 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B1276555 : Blo 670310 1276555 := bstep (se 1 (by rfl) ⟨957416, by rfl⟩ : syracuseStep 1276555 = 1914833) B1914833
theorem B1702579 : Blo 670310 1702579 := bstep (se 1 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 1702579 = 2553869) B2553869
theorem B1276631 : Blo 670310 1276631 := bstep (se 1 (by rfl) ⟨957473, by rfl⟩ : syracuseStep 1276631 = 1914947) B1914947
theorem B1702721 : Blo 670310 1702721 := bstep (se 2 (by rfl) ⟨638520, by rfl⟩ : syracuseStep 1702721 = 1277041) B1277041
theorem B850763 : Blo 670310 850763 := bstep (se 1 (by rfl) ⟨638072, by rfl⟩ : syracuseStep 850763 = 1276145) B1276145
theorem B2554841 : Blo 670310 2554841 := bstep (se 2 (by rfl) ⟨958065, by rfl⟩ : syracuseStep 2554841 = 1916131) B1916131
theorem B1277299 : Blo 670310 1277299 := bstep (se 1 (by rfl) ⟨957974, by rfl⟩ : syracuseStep 1277299 = 1915949) B1915949
theorem B851467 : Blo 670310 851467 := bstep (se 1 (by rfl) ⟨638600, by rfl⟩ : syracuseStep 851467 = 1277201) B1277201
theorem B1277527 : Blo 670310 1277527 := bstep (se 1 (by rfl) ⟨958145, by rfl⟩ : syracuseStep 1277527 = 1916291) B1916291
theorem B1277633 : Blo 670310 1277633 := bstep (se 2 (by rfl) ⟨479112, by rfl⟩ : syracuseStep 1277633 = 958225) B958225
theorem B851735 : Blo 670310 851735 := bstep (se 1 (by rfl) ⟨638801, by rfl⟩ : syracuseStep 851735 = 1277603) B1277603
theorem B3833675 : Blo 670310 3833675 := bstep (se 1 (by rfl) ⟨2875256, by rfl⟩ : syracuseStep 3833675 = 5750513) B5750513
theorem B1277785 : Blo 670310 1277785 := bstep (se 2 (by rfl) ⟨479169, by rfl⟩ : syracuseStep 1277785 = 958339) B958339
theorem B1704311 : Blo 670310 1704311 := bstep (se 1 (by rfl) ⟨1278233, by rfl⟩ : syracuseStep 1704311 = 2556467) B2556467
theorem B1278355 : Blo 670310 1278355 := bstep (se 1 (by rfl) ⟨958766, by rfl⟩ : syracuseStep 1278355 = 1917533) B1917533
theorem B3408641 : Blo 670310 3408641 := bstep (se 2 (by rfl) ⟨1278240, by rfl⟩ : syracuseStep 3408641 = 2556481) B2556481
theorem B754447 : Blo 670310 754447 := bstep (se 1 (by rfl) ⟨565835, by rfl⟩ : syracuseStep 754447 = 1131671) B1131671
theorem B1508471 : Blo 670310 1508471 := bstep (se 1 (by rfl) ⟨1131353, by rfl⟩ : syracuseStep 1508471 = 2262707) B2262707
theorem B754951 : Blo 670310 754951 := bstep (se 1 (by rfl) ⟨566213, by rfl⟩ : syracuseStep 754951 = 1132427) B1132427
theorem B1508651 : Blo 670310 1508651 := bstep (se 1 (by rfl) ⟨1131488, by rfl⟩ : syracuseStep 1508651 = 2262977) B2262977
theorem B755131 : Blo 670310 755131 := bstep (se 1 (by rfl) ⟨566348, by rfl⟩ : syracuseStep 755131 = 1132697) B1132697
theorem B3409451 : Blo 670310 3409451 := bstep (se 1 (by rfl) ⟨2557088, by rfl⟩ : syracuseStep 3409451 = 5114177) B5114177
theorem B1279547 : Blo 670310 1279547 := bstep (se 1 (by rfl) ⟨959660, by rfl⟩ : syracuseStep 1279547 = 1919321) B1919321
theorem B1705607 : Blo 670310 1705607 := bstep (se 1 (by rfl) ⟨1279205, by rfl⟩ : syracuseStep 1705607 = 2558411) B2558411
theorem B1509011 : Blo 670310 1509011 := bstep (se 1 (by rfl) ⟨1131758, by rfl⟩ : syracuseStep 1509011 = 2263517) B2263517
theorem B1705657 : Blo 670310 1705657 := bstep (se 2 (by rfl) ⟨639621, by rfl⟩ : syracuseStep 1705657 = 1279243) B1279243
theorem B1509065 : Blo 670310 1509065 := bstep (se 2 (by rfl) ⟨565899, by rfl⟩ : syracuseStep 1509065 = 1131799) B1131799
theorem B6457103 : Blo 670310 6457103 := bstep (se 1 (by rfl) ⟨4842827, by rfl⟩ : syracuseStep 6457103 = 9685655) B9685655
theorem B1214327 : Blo 670310 1214327 := bstep (se 1 (by rfl) ⟨910745, by rfl⟩ : syracuseStep 1214327 = 1821491) B1821491
theorem B755599 : Blo 670310 755599 := bstep (se 1 (by rfl) ⟨566699, by rfl⟩ : syracuseStep 755599 = 1133399) B1133399
theorem B3835907 : Blo 670310 3835907 := bstep (se 1 (by rfl) ⟨2876930, by rfl⟩ : syracuseStep 3835907 = 5753861) B5753861
theorem B7637003 : Blo 670310 7637003 := bstep (se 1 (by rfl) ⟨5727752, by rfl⟩ : syracuseStep 7637003 = 11455505) B11455505
theorem B1280033 : Blo 670310 1280033 := bstep (se 2 (by rfl) ⟨480012, by rfl⟩ : syracuseStep 1280033 = 960025) B960025
theorem B1706255 : Blo 670310 1706255 := bstep (se 1 (by rfl) ⟨1279691, by rfl⟩ : syracuseStep 1706255 = 2559383) B2559383
theorem B2263355 : Blo 670310 2263355 := bstep (se 1 (by rfl) ⟨1697516, by rfl⟩ : syracuseStep 2263355 = 3395033) B3395033
theorem B1509767 : Blo 670310 1509767 := bstep (se 1 (by rfl) ⟨1132325, by rfl⟩ : syracuseStep 1509767 = 2264651) B2264651
theorem B756103 : Blo 670310 756103 := bstep (se 1 (by rfl) ⟨567077, by rfl⟩ : syracuseStep 756103 = 1134155) B1134155
theorem B1509947 : Blo 670310 1509947 := bstep (se 1 (by rfl) ⟨1132460, by rfl⟩ : syracuseStep 1509947 = 2264921) B2264921
theorem B756283 : Blo 670310 756283 := bstep (se 1 (by rfl) ⟨567212, by rfl⟩ : syracuseStep 756283 = 1134425) B1134425
theorem B1510073 : Blo 670310 1510073 := bstep (se 2 (by rfl) ⟨566277, by rfl⟩ : syracuseStep 1510073 = 1132555) B1132555
theorem B3640079 : Blo 670310 3640079 := bstep (se 1 (by rfl) ⟨2730059, by rfl⟩ : syracuseStep 3640079 = 5460119) B5460119
theorem B2263841 : Blo 670310 2263841 := bstep (se 2 (by rfl) ⟨848940, by rfl⟩ : syracuseStep 2263841 = 1697881) B1697881
theorem B3410747 : Blo 670310 3410747 := bstep (se 1 (by rfl) ⟨2558060, by rfl⟩ : syracuseStep 3410747 = 5116121) B5116121
theorem B3410909 : Blo 670310 3410909 := bstep (se 3 (by rfl) ⟨639545, by rfl⟩ : syracuseStep 3410909 = 1279091) B1279091
theorem B1510415 : Blo 670310 1510415 := bstep (se 1 (by rfl) ⟨1132811, by rfl⟩ : syracuseStep 1510415 = 2265623) B2265623
theorem B756751 : Blo 670310 756751 := bstep (se 1 (by rfl) ⟨567563, by rfl⟩ : syracuseStep 756751 = 1135127) B1135127
theorem B1510433 : Blo 670310 1510433 := bstep (se 2 (by rfl) ⟨566412, by rfl⟩ : syracuseStep 1510433 = 1132825) B1132825
theorem B12946493 : Blo 670310 12946493 := bstep (se 3 (by rfl) ⟨2427467, by rfl⟩ : syracuseStep 12946493 = 4854935) B4854935
theorem B3411233 : Blo 670310 3411233 := bstep (se 2 (by rfl) ⟨1279212, by rfl⟩ : syracuseStep 3411233 = 2558425) B2558425
theorem B2264435 : Blo 670310 2264435 := bstep (se 1 (by rfl) ⟨1698326, by rfl⟩ : syracuseStep 2264435 = 3396653) B3396653
theorem B1510775 : Blo 670310 1510775 := bstep (se 1 (by rfl) ⟨1133081, by rfl⟩ : syracuseStep 1510775 = 2266163) B2266163
theorem B1019321 : Blo 670310 1019321 := bstep (se 2 (by rfl) ⟨382245, by rfl⟩ : syracuseStep 1019321 = 764491) B764491
theorem B757255 : Blo 670310 757255 := bstep (se 1 (by rfl) ⟨567941, by rfl⟩ : syracuseStep 757255 = 1135883) B1135883
theorem B1510955 : Blo 670310 1510955 := bstep (se 1 (by rfl) ⟨1133216, by rfl⟩ : syracuseStep 1510955 = 2266433) B2266433
theorem B757435 : Blo 670310 757435 := bstep (se 1 (by rfl) ⟨568076, by rfl⟩ : syracuseStep 757435 = 1136153) B1136153
theorem B1511315 : Blo 670310 1511315 := bstep (se 1 (by rfl) ⟨1133486, by rfl⟩ : syracuseStep 1511315 = 2266973) B2266973
theorem B1511369 : Blo 670310 1511369 := bstep (se 2 (by rfl) ⟨566763, by rfl⟩ : syracuseStep 1511369 = 1133527) B1133527
theorem B757903 : Blo 670310 757903 := bstep (se 1 (by rfl) ⟨568427, by rfl⟩ : syracuseStep 757903 = 1136855) B1136855
theorem B3412205 : Blo 670310 3412205 := bstep (se 3 (by rfl) ⟨639788, by rfl⟩ : syracuseStep 3412205 = 1279577) B1279577
theorem B3281411 : Blo 670310 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B1512071 : Blo 670310 1512071 := bstep (se 1 (by rfl) ⟨1134053, by rfl⟩ : syracuseStep 1512071 = 2268107) B2268107
theorem B758407 : Blo 670310 758407 := bstep (se 1 (by rfl) ⟨568805, by rfl⟩ : syracuseStep 758407 = 1137611) B1137611
theorem B955081 : Blo 670310 955081 := bstep (se 2 (by rfl) ⟨358155, by rfl⟩ : syracuseStep 955081 = 716311) B716311
theorem B1512251 : Blo 670310 1512251 := bstep (se 1 (by rfl) ⟨1134188, by rfl⟩ : syracuseStep 1512251 = 2268377) B2268377
theorem B758587 : Blo 670310 758587 := bstep (se 1 (by rfl) ⟨568940, by rfl⟩ : syracuseStep 758587 = 1137881) B1137881
theorem B6886295 : Blo 670310 6886295 := bstep (se 1 (by rfl) ⟨5164721, by rfl⟩ : syracuseStep 6886295 = 10329443) B10329443
theorem B1512377 : Blo 670310 1512377 := bstep (se 2 (by rfl) ⟨567141, by rfl⟩ : syracuseStep 1512377 = 1134283) B1134283
theorem B3413015 : Blo 670310 3413015 := bstep (se 1 (by rfl) ⟨2559761, by rfl⟩ : syracuseStep 3413015 = 5119523) B5119523
theorem B955577 : Blo 670310 955577 := bstep (se 2 (by rfl) ⟨358341, by rfl⟩ : syracuseStep 955577 = 716683) B716683
theorem B14554349 : Blo 670310 14554349 := bstep (se 3 (by rfl) ⟨2728940, by rfl⟩ : syracuseStep 14554349 = 5457881) B5457881
theorem B2069761 : Blo 670310 2069761 := bstep (se 2 (by rfl) ⟨776160, by rfl⟩ : syracuseStep 2069761 = 1552321) B1552321
theorem B1512719 : Blo 670310 1512719 := bstep (se 1 (by rfl) ⟨1134539, by rfl⟩ : syracuseStep 1512719 = 2269079) B2269079
theorem B9180449 : Blo 670310 9180449 := bstep (se 2 (by rfl) ⟨3442668, by rfl⟩ : syracuseStep 9180449 = 6885337) B6885337
theorem B1512737 : Blo 670310 1512737 := bstep (se 2 (by rfl) ⟨567276, by rfl⟩ : syracuseStep 1512737 = 1134553) B1134553
theorem B3675451 : Blo 670310 3675451 := bstep (se 1 (by rfl) ⟨2756588, by rfl⟩ : syracuseStep 3675451 = 5513177) B5513177
theorem B1513079 : Blo 670310 1513079 := bstep (se 1 (by rfl) ⟨1134809, by rfl⟩ : syracuseStep 1513079 = 2269619) B2269619
theorem B1513259 : Blo 670310 1513259 := bstep (se 1 (by rfl) ⟨1134944, by rfl⟩ : syracuseStep 1513259 = 2269889) B2269889
theorem B5445425 : Blo 670310 5445425 := bstep (se 2 (by rfl) ⟨2042034, by rfl⟩ : syracuseStep 5445425 = 4084069) B4084069
theorem B5183281 : Blo 670310 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B2267027 : Blo 670310 2267027 := bstep (se 1 (by rfl) ⟨1700270, by rfl⟩ : syracuseStep 2267027 = 3400541) B3400541
theorem B19666961 : Blo 670310 19666961 := bstep (se 2 (by rfl) ⟨7375110, by rfl⟩ : syracuseStep 19666961 = 14750221) B14750221
theorem B956551 : Blo 670310 956551 := bstep (se 1 (by rfl) ⟨717413, by rfl⟩ : syracuseStep 956551 = 1434827) B1434827
theorem B1513619 : Blo 670310 1513619 := bstep (se 1 (by rfl) ⟨1135214, by rfl⟩ : syracuseStep 1513619 = 2270429) B2270429
theorem B1513673 : Blo 670310 1513673 := bstep (se 2 (by rfl) ⟨567627, by rfl⟩ : syracuseStep 1513673 = 1135255) B1135255
theorem B7641377 : Blo 670310 7641377 := bstep (se 2 (by rfl) ⟨2865516, by rfl⟩ : syracuseStep 7641377 = 5731033) B5731033
theorem B1841935 : Blo 670310 1841935 := bstep (se 1 (by rfl) ⟨1381451, by rfl⟩ : syracuseStep 1841935 = 2762903) B2762903
theorem B1514375 : Blo 670310 1514375 := bstep (se 1 (by rfl) ⟨1135781, by rfl⟩ : syracuseStep 1514375 = 2271563) B2271563
theorem B1514555 : Blo 670310 1514555 := bstep (se 1 (by rfl) ⟨1135916, by rfl⟩ : syracuseStep 1514555 = 2271833) B2271833
theorem B5119037 : Blo 670310 5119037 := bstep (se 3 (by rfl) ⟨959819, by rfl⟩ : syracuseStep 5119037 = 1919639) B1919639
theorem B1514681 : Blo 670310 1514681 := bstep (se 2 (by rfl) ⟨568005, by rfl⟩ : syracuseStep 1514681 = 1136011) B1136011
theorem B2268431 : Blo 670310 2268431 := bstep (se 1 (by rfl) ⟨1701323, by rfl⟩ : syracuseStep 2268431 = 3402647) B3402647
theorem B1023275 : Blo 670310 1023275 := bstep (se 1 (by rfl) ⟨767456, by rfl⟩ : syracuseStep 1023275 = 1534913) B1534913
theorem B12426701 : Blo 670310 12426701 := bstep (se 3 (by rfl) ⟨2330006, by rfl⟩ : syracuseStep 12426701 = 4660013) B4660013
theorem B1515023 : Blo 670310 1515023 := bstep (se 1 (by rfl) ⟨1136267, by rfl⟩ : syracuseStep 1515023 = 2272535) B2272535
theorem B2268701 : Blo 670310 2268701 := bstep (se 3 (by rfl) ⟨425381, by rfl⟩ : syracuseStep 2268701 = 850763) B850763
theorem B1515041 : Blo 670310 1515041 := bstep (se 2 (by rfl) ⟨568140, by rfl⟩ : syracuseStep 1515041 = 1136281) B1136281
theorem B958009 : Blo 670310 958009 := bstep (se 2 (by rfl) ⟨359253, by rfl⟩ : syracuseStep 958009 = 718507) B718507
theorem B1515383 : Blo 670310 1515383 := bstep (se 1 (by rfl) ⟨1136537, by rfl⟩ : syracuseStep 1515383 = 2273075) B2273075
theorem B1515563 : Blo 670310 1515563 := bstep (se 1 (by rfl) ⟨1136672, by rfl⟩ : syracuseStep 1515563 = 2273345) B2273345
theorem B1024247 : Blo 670310 1024247 := bstep (se 1 (by rfl) ⟨768185, by rfl⟩ : syracuseStep 1024247 = 1536371) B1536371
theorem B1515923 : Blo 670310 1515923 := bstep (se 1 (by rfl) ⟨1136942, by rfl⟩ : syracuseStep 1515923 = 2273885) B2273885
theorem B1122761 : Blo 670310 1122761 := bstep (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) B842071
theorem B1515977 : Blo 670310 1515977 := bstep (se 2 (by rfl) ⟨568491, by rfl⟩ : syracuseStep 1515977 = 1136983) B1136983
theorem B7676369 : Blo 670310 7676369 := bstep (se 2 (by rfl) ⟨2878638, by rfl⟩ : syracuseStep 7676369 = 5757277) B5757277
theorem B2957867 : Blo 670310 2957867 := bstep (se 1 (by rfl) ⟨2218400, by rfl⟩ : syracuseStep 2957867 = 4436801) B4436801
theorem B1909433 : Blo 670310 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B959239 : Blo 670310 959239 := bstep (se 1 (by rfl) ⟨719429, by rfl⟩ : syracuseStep 959239 = 1438859) B1438859
theorem B6464407 : Blo 670310 6464407 := bstep (se 1 (by rfl) ⟨4848305, by rfl⟩ : syracuseStep 6464407 = 9696611) B9696611
theorem B2270105 : Blo 670310 2270105 := bstep (se 2 (by rfl) ⟨851289, by rfl⟩ : syracuseStep 2270105 = 1702579) B1702579
theorem B7644293 : Blo 670310 7644293 := bstep (se 4 (by rfl) ⟨716652, by rfl⟩ : syracuseStep 7644293 = 1433305) B1433305
theorem B1516679 : Blo 670310 1516679 := bstep (se 1 (by rfl) ⟨1137509, by rfl⟩ : syracuseStep 1516679 = 2275019) B2275019
theorem B1516859 : Blo 670310 1516859 := bstep (se 1 (by rfl) ⟨1137644, by rfl⟩ : syracuseStep 1516859 = 2275289) B2275289
theorem B1516985 : Blo 670310 1516985 := bstep (se 2 (by rfl) ⟨568869, by rfl⟩ : syracuseStep 1516985 = 1137739) B1137739
theorem B11085265 : Blo 670310 11085265 := bstep (se 2 (by rfl) ⟨4156974, by rfl⟩ : syracuseStep 11085265 = 8313949) B8313949
theorem B960059 : Blo 670310 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B2270807 : Blo 670310 2270807 := bstep (se 1 (by rfl) ⟨1703105, by rfl⟩ : syracuseStep 2270807 = 3406211) B3406211
theorem B1910425 : Blo 670310 1910425 := bstep (se 2 (by rfl) ⟨716409, by rfl⟩ : syracuseStep 1910425 = 1432819) B1432819
theorem B1812169 : Blo 670310 1812169 := bstep (se 2 (by rfl) ⟨679563, by rfl⟩ : syracuseStep 1812169 = 1359127) B1359127
theorem B16361189 : Blo 670310 16361189 := bstep (se 4 (by rfl) ⟨1533861, by rfl⟩ : syracuseStep 16361189 = 3067723) B3067723
theorem B18425717 : Blo 670310 18425717 := bstep (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) B1727411
theorem B3221383 : Blo 670310 3221383 := bstep (se 1 (by rfl) ⟨2416037, by rfl⟩ : syracuseStep 3221383 = 4832075) B4832075
theorem B2271293 : Blo 670310 2271293 := bstep (se 3 (by rfl) ⟨425867, by rfl⟩ : syracuseStep 2271293 = 851735) B851735
theorem B2304119 : Blo 670310 2304119 := bstep (se 1 (by rfl) ⟨1728089, by rfl⟩ : syracuseStep 2304119 = 3456179) B3456179
theorem B7285139 : Blo 670310 7285139 := bstep (se 1 (by rfl) ⟨5463854, by rfl⟩ : syracuseStep 7285139 = 10927709) B10927709
theorem B12462659 : Blo 670310 12462659 := bstep (se 1 (by rfl) ⟨9346994, by rfl⟩ : syracuseStep 12462659 = 18693989) B18693989
theorem B2042825 : Blo 670310 2042825 := bstep (se 2 (by rfl) ⟨766059, by rfl⟩ : syracuseStep 2042825 = 1532119) B1532119
theorem B2731279 : Blo 670310 2731279 := bstep (se 1 (by rfl) ⟨2048459, by rfl⟩ : syracuseStep 2731279 = 4096919) B4096919
theorem B863623 : Blo 670310 863623 := bstep (se 1 (by rfl) ⟨647717, by rfl⟩ : syracuseStep 863623 = 1295435) B1295435
theorem B2272697 : Blo 670310 2272697 := bstep (se 2 (by rfl) ⟨852261, by rfl⟩ : syracuseStep 2272697 = 1704523) B1704523
theorem B1912349 : Blo 670310 1912349 := bstep (se 3 (by rfl) ⟨358565, by rfl⟩ : syracuseStep 1912349 = 717131) B717131
theorem B2043593 : Blo 670310 2043593 := bstep (se 2 (by rfl) ⟨766347, by rfl⟩ : syracuseStep 2043593 = 1532695) B1532695
theorem B10333925 : Blo 670310 10333925 := bstep (se 4 (by rfl) ⟨968805, by rfl⟩ : syracuseStep 10333925 = 1937611) B1937611
theorem B2273291 : Blo 670310 2273291 := bstep (se 1 (by rfl) ⟨1704968, by rfl⟩ : syracuseStep 2273291 = 3409937) B3409937
theorem B3321917 : Blo 670310 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B504868949 : Blo 670310 504868949 := bstep (se 8 (by rfl) ⟨2958216, by rfl⟩ : syracuseStep 504868949 = 5916433) B5916433
theorem B2273399 : Blo 670310 2273399 := bstep (se 1 (by rfl) ⟨1705049, by rfl⟩ : syracuseStep 2273399 = 3410099) B3410099
theorem B1618073 : Blo 670310 1618073 := bstep (se 2 (by rfl) ⟨606777, by rfl⟩ : syracuseStep 1618073 = 1213555) B1213555
theorem B1913033 : Blo 670310 1913033 := bstep (se 2 (by rfl) ⟨717387, by rfl⟩ : syracuseStep 1913033 = 1434775) B1434775
theorem B5746889 : Blo 670310 5746889 := bstep (se 2 (by rfl) ⟨2155083, by rfl⟩ : syracuseStep 5746889 = 4310167) B4310167
theorem B8172035 : Blo 670310 8172035 := bstep (se 1 (by rfl) ⟨6129026, by rfl⟩ : syracuseStep 8172035 = 12258053) B12258053
theorem B2273993 : Blo 670310 2273993 := bstep (se 2 (by rfl) ⟨852747, by rfl⟩ : syracuseStep 2273993 = 1705495) B1705495
theorem B1913615 : Blo 670310 1913615 := bstep (se 1 (by rfl) ⟨1435211, by rfl⟩ : syracuseStep 1913615 = 2870423) B2870423
theorem B27898805 : Blo 670310 27898805 := bstep (se 5 (by rfl) ⟨1307756, by rfl⟩ : syracuseStep 27898805 = 2615513) B2615513
theorem B2045063 : Blo 670310 2045063 := bstep (se 1 (by rfl) ⟨1533797, by rfl⟩ : syracuseStep 2045063 = 3067595) B3067595
theorem B4306121 : Blo 670310 4306121 := bstep (se 2 (by rfl) ⟨1614795, by rfl⟩ : syracuseStep 4306121 = 3229591) B3229591
theorem B2274695 : Blo 670310 2274695 := bstep (se 1 (by rfl) ⟨1706021, by rfl⟩ : syracuseStep 2274695 = 3412043) B3412043
theorem B5092793 : Blo 670310 5092793 := bstep (se 2 (by rfl) ⟨1909797, by rfl⟩ : syracuseStep 5092793 = 3819595) B3819595
theorem B3225091 : Blo 670310 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B2275073 : Blo 670310 2275073 := bstep (se 2 (by rfl) ⟨853152, by rfl⟩ : syracuseStep 2275073 = 1706305) B1706305
theorem B5748529 : Blo 670310 5748529 := bstep (se 2 (by rfl) ⟨2155698, by rfl⟩ : syracuseStep 5748529 = 4311397) B4311397
theorem B3323965 : Blo 670310 3323965 := bstep (se 3 (by rfl) ⟨623243, by rfl⟩ : syracuseStep 3323965 = 1246487) B1246487
theorem B1915015 : Blo 670310 1915015 := bstep (se 1 (by rfl) ⟨1436261, by rfl⟩ : syracuseStep 1915015 = 2872523) B2872523
theorem B6895817 : Blo 670310 6895817 := bstep (se 2 (by rfl) ⟨2585931, by rfl⟩ : syracuseStep 6895817 = 5171863) B5171863
theorem B6895853 : Blo 670310 6895853 := bstep (se 3 (by rfl) ⟨1292972, by rfl⟩ : syracuseStep 6895853 = 2585945) B2585945
theorem B1292663 : Blo 670310 1292663 := bstep (se 1 (by rfl) ⟨969497, by rfl⟩ : syracuseStep 1292663 = 1938995) B1938995
theorem B1915289 : Blo 670310 1915289 := bstep (se 2 (by rfl) ⟨718233, by rfl⟩ : syracuseStep 1915289 = 1436467) B1436467
theorem B670343 : Blo 670310 670343 := bstep (se 1 (by rfl) ⟨502757, by rfl⟩ : syracuseStep 670343 = 1005515) B1005515
theorem B768647 : Blo 670310 768647 := bstep (se 1 (by rfl) ⟨576485, by rfl⟩ : syracuseStep 768647 = 1152971) B1152971
theorem B670351 : Blo 670310 670351 := bstep (se 1 (by rfl) ⟨502763, by rfl⟩ : syracuseStep 670351 = 1005527) B1005527
theorem B670395 : Blo 670310 670395 := bstep (se 1 (by rfl) ⟨502796, by rfl⟩ : syracuseStep 670395 = 1005593) B1005593
theorem B670471 : Blo 670310 670471 := bstep (se 1 (by rfl) ⟨502853, by rfl⟩ : syracuseStep 670471 = 1005707) B1005707
theorem B670479 : Blo 670310 670479 := bstep (se 1 (by rfl) ⟨502859, by rfl⟩ : syracuseStep 670479 = 1005719) B1005719
theorem B670523 : Blo 670310 670523 := bstep (se 1 (by rfl) ⟨502892, by rfl⟩ : syracuseStep 670523 = 1005785) B1005785
theorem B670599 : Blo 670310 670599 := bstep (se 1 (by rfl) ⟨502949, by rfl⟩ : syracuseStep 670599 = 1005899) B1005899
theorem B670607 : Blo 670310 670607 := bstep (se 1 (by rfl) ⟨502955, by rfl⟩ : syracuseStep 670607 = 1005911) B1005911
theorem B2177945 : Blo 670310 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B32783267 : Blo 670310 32783267 := bstep (se 1 (by rfl) ⟨24587450, by rfl⟩ : syracuseStep 32783267 = 49174901) B49174901
theorem B670651 : Blo 670310 670651 := bstep (se 1 (by rfl) ⟨502988, by rfl⟩ : syracuseStep 670651 = 1005977) B1005977
theorem B670727 : Blo 670310 670727 := bstep (se 1 (by rfl) ⟨503045, by rfl⟩ : syracuseStep 670727 = 1006091) B1006091
theorem B670735 : Blo 670310 670735 := bstep (se 1 (by rfl) ⟨503051, by rfl⟩ : syracuseStep 670735 = 1006103) B1006103
theorem B670779 : Blo 670310 670779 := bstep (se 1 (by rfl) ⟨503084, by rfl⟩ : syracuseStep 670779 = 1006169) B1006169
theorem B670855 : Blo 670310 670855 := bstep (se 1 (by rfl) ⟨503141, by rfl⟩ : syracuseStep 670855 = 1006283) B1006283
theorem B670863 : Blo 670310 670863 := bstep (se 1 (by rfl) ⟨503147, by rfl⟩ : syracuseStep 670863 = 1006295) B1006295
theorem B670907 : Blo 670310 670907 := bstep (se 1 (by rfl) ⟨503180, by rfl⟩ : syracuseStep 670907 = 1006361) B1006361
theorem B670983 : Blo 670310 670983 := bstep (se 1 (by rfl) ⟨503237, by rfl⟩ : syracuseStep 670983 = 1006475) B1006475
theorem B670991 : Blo 670310 670991 := bstep (se 1 (by rfl) ⟨503243, by rfl⟩ : syracuseStep 670991 = 1006487) B1006487
theorem B671035 : Blo 670310 671035 := bstep (se 1 (by rfl) ⟨503276, by rfl⟩ : syracuseStep 671035 = 1006553) B1006553
theorem B2047351 : Blo 670310 2047351 := bstep (se 1 (by rfl) ⟨1535513, by rfl⟩ : syracuseStep 2047351 = 3071027) B3071027
theorem B671111 : Blo 670310 671111 := bstep (se 1 (by rfl) ⟨503333, by rfl⟩ : syracuseStep 671111 = 1006667) B1006667
theorem B671119 : Blo 670310 671119 := bstep (se 1 (by rfl) ⟨503339, by rfl⟩ : syracuseStep 671119 = 1006679) B1006679
theorem B1359289 : Blo 670310 1359289 := bstep (se 2 (by rfl) ⟨509733, by rfl⟩ : syracuseStep 1359289 = 1019467) B1019467
theorem B671163 : Blo 670310 671163 := bstep (se 1 (by rfl) ⟨503372, by rfl⟩ : syracuseStep 671163 = 1006745) B1006745
theorem B671239 : Blo 670310 671239 := bstep (se 1 (by rfl) ⟨503429, by rfl⟩ : syracuseStep 671239 = 1006859) B1006859
theorem B671247 : Blo 670310 671247 := bstep (se 1 (by rfl) ⟨503435, by rfl⟩ : syracuseStep 671247 = 1006871) B1006871
theorem B671291 : Blo 670310 671291 := bstep (se 1 (by rfl) ⟨503468, by rfl⟩ : syracuseStep 671291 = 1006937) B1006937
theorem B1916531 : Blo 670310 1916531 := bstep (se 1 (by rfl) ⟨1437398, by rfl⟩ : syracuseStep 1916531 = 2874797) B2874797
theorem B671367 : Blo 670310 671367 := bstep (se 1 (by rfl) ⟨503525, by rfl⟩ : syracuseStep 671367 = 1007051) B1007051
theorem B671375 : Blo 670310 671375 := bstep (se 1 (by rfl) ⟨503531, by rfl⟩ : syracuseStep 671375 = 1007063) B1007063
theorem B1457849 : Blo 670310 1457849 := bstep (se 2 (by rfl) ⟨546693, by rfl⟩ : syracuseStep 1457849 = 1093387) B1093387
theorem B671419 : Blo 670310 671419 := bstep (se 1 (by rfl) ⟨503564, by rfl⟩ : syracuseStep 671419 = 1007129) B1007129
theorem B671495 : Blo 670310 671495 := bstep (se 1 (by rfl) ⟨503621, by rfl⟩ : syracuseStep 671495 = 1007243) B1007243
theorem B671503 : Blo 670310 671503 := bstep (se 1 (by rfl) ⟨503627, by rfl⟩ : syracuseStep 671503 = 1007255) B1007255
theorem B671547 : Blo 670310 671547 := bstep (se 1 (by rfl) ⟨503660, by rfl⟩ : syracuseStep 671547 = 1007321) B1007321
theorem B671623 : Blo 670310 671623 := bstep (se 1 (by rfl) ⟨503717, by rfl⟩ : syracuseStep 671623 = 1007435) B1007435
theorem B671631 : Blo 670310 671631 := bstep (se 1 (by rfl) ⟨503723, by rfl⟩ : syracuseStep 671631 = 1007447) B1007447
theorem B671675 : Blo 670310 671675 := bstep (se 1 (by rfl) ⟨503756, by rfl⟩ : syracuseStep 671675 = 1007513) B1007513
theorem B671751 : Blo 670310 671751 := bstep (se 1 (by rfl) ⟨503813, by rfl⟩ : syracuseStep 671751 = 1007627) B1007627
theorem B671759 : Blo 670310 671759 := bstep (se 1 (by rfl) ⟨503819, by rfl⟩ : syracuseStep 671759 = 1007639) B1007639
theorem B671803 : Blo 670310 671803 := bstep (se 1 (by rfl) ⟨503852, by rfl⟩ : syracuseStep 671803 = 1007705) B1007705
theorem B671879 : Blo 670310 671879 := bstep (se 1 (by rfl) ⟨503909, by rfl⟩ : syracuseStep 671879 = 1007819) B1007819
theorem B671887 : Blo 670310 671887 := bstep (se 1 (by rfl) ⟨503915, by rfl⟩ : syracuseStep 671887 = 1007831) B1007831
theorem B671931 : Blo 670310 671931 := bstep (se 1 (by rfl) ⟨503948, by rfl⟩ : syracuseStep 671931 = 1007897) B1007897
theorem B672007 : Blo 670310 672007 := bstep (se 1 (by rfl) ⟨504005, by rfl⟩ : syracuseStep 672007 = 1008011) B1008011
theorem B672015 : Blo 670310 672015 := bstep (se 1 (by rfl) ⟨504011, by rfl⟩ : syracuseStep 672015 = 1008023) B1008023
theorem B4079909 : Blo 670310 4079909 := bstep (se 4 (by rfl) ⟨382491, by rfl⟩ : syracuseStep 4079909 = 764983) B764983
theorem B672059 : Blo 670310 672059 := bstep (se 1 (by rfl) ⟨504044, by rfl⟩ : syracuseStep 672059 = 1008089) B1008089
theorem B672135 : Blo 670310 672135 := bstep (se 1 (by rfl) ⟨504101, by rfl⟩ : syracuseStep 672135 = 1008203) B1008203
theorem B672143 : Blo 670310 672143 := bstep (se 1 (by rfl) ⟨504107, by rfl⟩ : syracuseStep 672143 = 1008215) B1008215
theorem B672187 : Blo 670310 672187 := bstep (se 1 (by rfl) ⟨504140, by rfl⟩ : syracuseStep 672187 = 1008281) B1008281
theorem B672263 : Blo 670310 672263 := bstep (se 1 (by rfl) ⟨504197, by rfl⟩ : syracuseStep 672263 = 1008395) B1008395
theorem B672271 : Blo 670310 672271 := bstep (se 1 (by rfl) ⟨504203, by rfl⟩ : syracuseStep 672271 = 1008407) B1008407
theorem B672315 : Blo 670310 672315 := bstep (se 1 (by rfl) ⟨504236, by rfl⟩ : syracuseStep 672315 = 1008473) B1008473
theorem B1720919 : Blo 670310 1720919 := bstep (se 1 (by rfl) ⟨1290689, by rfl⟩ : syracuseStep 1720919 = 2581379) B2581379
theorem B672391 : Blo 670310 672391 := bstep (se 1 (by rfl) ⟨504293, by rfl⟩ : syracuseStep 672391 = 1008587) B1008587
theorem B672399 : Blo 670310 672399 := bstep (se 1 (by rfl) ⟨504299, by rfl⟩ : syracuseStep 672399 = 1008599) B1008599
theorem B2048665 : Blo 670310 2048665 := bstep (se 2 (by rfl) ⟨768249, by rfl⟩ : syracuseStep 2048665 = 1536499) B1536499
theorem B672443 : Blo 670310 672443 := bstep (se 1 (by rfl) ⟨504332, by rfl⟩ : syracuseStep 672443 = 1008665) B1008665
theorem B672519 : Blo 670310 672519 := bstep (se 1 (by rfl) ⟨504389, by rfl⟩ : syracuseStep 672519 = 1008779) B1008779
theorem B672527 : Blo 670310 672527 := bstep (se 1 (by rfl) ⟨504395, by rfl⟩ : syracuseStep 672527 = 1008791) B1008791
theorem B672571 : Blo 670310 672571 := bstep (se 1 (by rfl) ⟨504428, by rfl⟩ : syracuseStep 672571 = 1008857) B1008857
theorem B672647 : Blo 670310 672647 := bstep (se 1 (by rfl) ⟨504485, by rfl⟩ : syracuseStep 672647 = 1008971) B1008971
theorem B672655 : Blo 670310 672655 := bstep (se 1 (by rfl) ⟨504491, by rfl⟩ : syracuseStep 672655 = 1008983) B1008983
theorem B672699 : Blo 670310 672699 := bstep (se 1 (by rfl) ⟨504524, by rfl⟩ : syracuseStep 672699 = 1009049) B1009049
theorem B672775 : Blo 670310 672775 := bstep (se 1 (by rfl) ⟨504581, by rfl⟩ : syracuseStep 672775 = 1009163) B1009163
theorem B672783 : Blo 670310 672783 := bstep (se 1 (by rfl) ⟨504587, by rfl⟩ : syracuseStep 672783 = 1009175) B1009175
theorem B1131563 : Blo 670310 1131563 := bstep (se 1 (by rfl) ⟨848672, by rfl⟩ : syracuseStep 1131563 = 1697345) B1697345
theorem B672827 : Blo 670310 672827 := bstep (se 1 (by rfl) ⟨504620, by rfl⟩ : syracuseStep 672827 = 1009241) B1009241
theorem B2147447 : Blo 670310 2147447 := bstep (se 1 (by rfl) ⟨1610585, by rfl⟩ : syracuseStep 2147447 = 3221171) B3221171
theorem B672903 : Blo 670310 672903 := bstep (se 1 (by rfl) ⟨504677, by rfl⟩ : syracuseStep 672903 = 1009355) B1009355
theorem B672911 : Blo 670310 672911 := bstep (se 1 (by rfl) ⟨504683, by rfl⟩ : syracuseStep 672911 = 1009367) B1009367
theorem B672955 : Blo 670310 672955 := bstep (se 1 (by rfl) ⟨504716, by rfl⟩ : syracuseStep 672955 = 1009433) B1009433
theorem B673031 : Blo 670310 673031 := bstep (se 1 (by rfl) ⟨504773, by rfl⟩ : syracuseStep 673031 = 1009547) B1009547
theorem B673039 : Blo 670310 673039 := bstep (se 1 (by rfl) ⟨504779, by rfl⟩ : syracuseStep 673039 = 1009559) B1009559
theorem B673083 : Blo 670310 673083 := bstep (se 1 (by rfl) ⟨504812, by rfl⟩ : syracuseStep 673083 = 1009625) B1009625
theorem B673159 : Blo 670310 673159 := bstep (se 1 (by rfl) ⟨504869, by rfl⟩ : syracuseStep 673159 = 1009739) B1009739
theorem B673167 : Blo 670310 673167 := bstep (se 1 (by rfl) ⟨504875, by rfl⟩ : syracuseStep 673167 = 1009751) B1009751
theorem B1131961 : Blo 670310 1131961 := bstep (se 2 (by rfl) ⟨424485, by rfl⟩ : syracuseStep 1131961 = 848971) B848971
theorem B673211 : Blo 670310 673211 := bstep (se 1 (by rfl) ⟨504908, by rfl⟩ : syracuseStep 673211 = 1009817) B1009817
theorem B673287 : Blo 670310 673287 := bstep (se 1 (by rfl) ⟨504965, by rfl⟩ : syracuseStep 673287 = 1009931) B1009931
theorem B673295 : Blo 670310 673295 := bstep (se 1 (by rfl) ⟨504971, by rfl⟩ : syracuseStep 673295 = 1009943) B1009943
theorem B4081175 : Blo 670310 4081175 := bstep (se 1 (by rfl) ⟨3060881, by rfl⟩ : syracuseStep 4081175 = 6121763) B6121763
theorem B1033771 : Blo 670310 1033771 := bstep (se 1 (by rfl) ⟨775328, by rfl⟩ : syracuseStep 1033771 = 1550657) B1550657
theorem B673339 : Blo 670310 673339 := bstep (se 1 (by rfl) ⟨505004, by rfl⟩ : syracuseStep 673339 = 1010009) B1010009
theorem B2868797 : Blo 670310 2868797 := bstep (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) B1075799
theorem B3819095 : Blo 670310 3819095 := bstep (se 1 (by rfl) ⟨2864321, by rfl⟩ : syracuseStep 3819095 = 5728643) B5728643
theorem B673415 : Blo 670310 673415 := bstep (se 1 (by rfl) ⟨505061, by rfl⟩ : syracuseStep 673415 = 1010123) B1010123
theorem B673423 : Blo 670310 673423 := bstep (se 1 (by rfl) ⟨505067, by rfl⟩ : syracuseStep 673423 = 1010135) B1010135
theorem B7653041 : Blo 670310 7653041 := bstep (se 2 (by rfl) ⟨2869890, by rfl⟩ : syracuseStep 7653041 = 5739781) B5739781
theorem B673467 : Blo 670310 673467 := bstep (se 1 (by rfl) ⟨505100, by rfl⟩ : syracuseStep 673467 = 1010201) B1010201
theorem B673543 : Blo 670310 673543 := bstep (se 1 (by rfl) ⟨505157, by rfl⟩ : syracuseStep 673543 = 1010315) B1010315
theorem B673551 : Blo 670310 673551 := bstep (se 1 (by rfl) ⟨505163, by rfl⟩ : syracuseStep 673551 = 1010327) B1010327
theorem B673595 : Blo 670310 673595 := bstep (se 1 (by rfl) ⟨505196, by rfl⟩ : syracuseStep 673595 = 1010393) B1010393
theorem B673671 : Blo 670310 673671 := bstep (se 1 (by rfl) ⟨505253, by rfl⟩ : syracuseStep 673671 = 1010507) B1010507
theorem B673679 : Blo 670310 673679 := bstep (se 1 (by rfl) ⟨505259, by rfl⟩ : syracuseStep 673679 = 1010519) B1010519
theorem B673723 : Blo 670310 673723 := bstep (se 1 (by rfl) ⟨505292, by rfl⟩ : syracuseStep 673723 = 1010585) B1010585
theorem B673799 : Blo 670310 673799 := bstep (se 1 (by rfl) ⟨505349, by rfl⟩ : syracuseStep 673799 = 1010699) B1010699
theorem B673807 : Blo 670310 673807 := bstep (se 1 (by rfl) ⟨505355, by rfl⟩ : syracuseStep 673807 = 1010711) B1010711
theorem B1918991 : Blo 670310 1918991 := bstep (se 1 (by rfl) ⟨1439243, by rfl⟩ : syracuseStep 1918991 = 2878487) B2878487
theorem B673851 : Blo 670310 673851 := bstep (se 1 (by rfl) ⟨505388, by rfl⟩ : syracuseStep 673851 = 1010777) B1010777
theorem B4835389 : Blo 670310 4835389 := bstep (se 3 (by rfl) ⟨906635, by rfl⟩ : syracuseStep 4835389 = 1813271) B1813271
theorem B1132663 : Blo 670310 1132663 := bstep (se 1 (by rfl) ⟨849497, by rfl⟩ : syracuseStep 1132663 = 1698995) B1698995
theorem B673927 : Blo 670310 673927 := bstep (se 1 (by rfl) ⟨505445, by rfl⟩ : syracuseStep 673927 = 1010891) B1010891
theorem B673935 : Blo 670310 673935 := bstep (se 1 (by rfl) ⟨505451, by rfl⟩ : syracuseStep 673935 = 1010903) B1010903
theorem B673979 : Blo 670310 673979 := bstep (se 1 (by rfl) ⟨505484, by rfl⟩ : syracuseStep 673979 = 1010969) B1010969
theorem B3393737 : Blo 670310 3393737 := bstep (se 2 (by rfl) ⟨1272651, by rfl⟩ : syracuseStep 3393737 = 2545303) B2545303
theorem B674055 : Blo 670310 674055 := bstep (se 1 (by rfl) ⟨505541, by rfl⟩ : syracuseStep 674055 = 1011083) B1011083
theorem B674063 : Blo 670310 674063 := bstep (se 1 (by rfl) ⟨505547, by rfl⟩ : syracuseStep 674063 = 1011095) B1011095
theorem B1132859 : Blo 670310 1132859 := bstep (se 1 (by rfl) ⟨849644, by rfl⟩ : syracuseStep 1132859 = 1699289) B1699289
theorem B674107 : Blo 670310 674107 := bstep (se 1 (by rfl) ⟨505580, by rfl⟩ : syracuseStep 674107 = 1011161) B1011161
theorem B674183 : Blo 670310 674183 := bstep (se 1 (by rfl) ⟨505637, by rfl⟩ : syracuseStep 674183 = 1011275) B1011275
theorem B674191 : Blo 670310 674191 := bstep (se 1 (by rfl) ⟨505643, by rfl⟩ : syracuseStep 674191 = 1011287) B1011287
theorem B674235 : Blo 670310 674235 := bstep (se 1 (by rfl) ⟨505676, by rfl⟩ : syracuseStep 674235 = 1011353) B1011353
theorem B2869789 : Blo 670310 2869789 := bstep (se 3 (by rfl) ⟨538085, by rfl⟩ : syracuseStep 2869789 = 1076171) B1076171
theorem B1296929 : Blo 670310 1296929 := bstep (se 2 (by rfl) ⟨486348, by rfl⟩ : syracuseStep 1296929 = 972697) B972697
theorem B9226871 : Blo 670310 9226871 := bstep (se 1 (by rfl) ⟨6920153, by rfl⟩ : syracuseStep 9226871 = 13840307) B13840307
theorem B1133257 : Blo 670310 1133257 := bstep (se 2 (by rfl) ⟨424971, by rfl⟩ : syracuseStep 1133257 = 849943) B849943
theorem B1821575 : Blo 670310 1821575 := bstep (se 1 (by rfl) ⟨1366181, by rfl⟩ : syracuseStep 1821575 = 2732363) B2732363
theorem B2149267 : Blo 670310 2149267 := bstep (se 1 (by rfl) ⟨1611950, by rfl⟩ : syracuseStep 2149267 = 3223901) B3223901
theorem B17255429 : Blo 670310 17255429 := bstep (se 4 (by rfl) ⟨1617696, by rfl⟩ : syracuseStep 17255429 = 3235393) B3235393
theorem B1166537 : Blo 670310 1166537 := bstep (se 2 (by rfl) ⟨437451, by rfl⟩ : syracuseStep 1166537 = 874903) B874903
theorem B1133959 : Blo 670310 1133959 := bstep (se 1 (by rfl) ⟨850469, by rfl⟩ : syracuseStep 1133959 = 1700939) B1700939
theorem B5459345 : Blo 670310 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B1822267 : Blo 670310 1822267 := bstep (se 1 (by rfl) ⟨1366700, by rfl⟩ : syracuseStep 1822267 = 2733401) B2733401
theorem B3624509 : Blo 670310 3624509 := bstep (se 3 (by rfl) ⟨679595, by rfl⟩ : syracuseStep 3624509 = 1359191) B1359191
theorem B1822409 : Blo 670310 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B3821327 : Blo 670310 3821327 := bstep (se 1 (by rfl) ⟨2865995, by rfl⟩ : syracuseStep 3821327 = 5731991) B5731991
theorem B8179471 : Blo 670310 8179471 := bstep (se 1 (by rfl) ⟨6134603, by rfl⟩ : syracuseStep 8179471 = 12269207) B12269207
theorem B3821579 : Blo 670310 3821579 := bstep (se 1 (by rfl) ⟨2866184, by rfl⟩ : syracuseStep 3821579 = 5732369) B5732369
theorem B1134607 : Blo 670310 1134607 := bstep (se 1 (by rfl) ⟨850955, by rfl⟩ : syracuseStep 1134607 = 1701911) B1701911
theorem B5165117 : Blo 670310 5165117 := bstep (se 3 (by rfl) ⟨968459, by rfl⟩ : syracuseStep 5165117 = 1936919) B1936919
theorem B2871737 : Blo 670310 2871737 := bstep (se 2 (by rfl) ⟨1076901, by rfl⟩ : syracuseStep 2871737 = 2153803) B2153803
theorem B1135147 : Blo 670310 1135147 := bstep (se 1 (by rfl) ⟨851360, by rfl⟩ : syracuseStep 1135147 = 1702721) B1702721
theorem B3265085 : Blo 670310 3265085 := bstep (se 3 (by rfl) ⟨612203, by rfl⟩ : syracuseStep 3265085 = 1224407) B1224407
theorem B1135289 : Blo 670310 1135289 := bstep (se 2 (by rfl) ⟨425733, by rfl⟩ : syracuseStep 1135289 = 851467) B851467
theorem B2872199 : Blo 670310 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B2151485 : Blo 670310 2151485 := bstep (se 3 (by rfl) ⟨403403, by rfl⟩ : syracuseStep 2151485 = 806807) B806807
theorem B971947 : Blo 670310 971947 := bstep (se 1 (by rfl) ⟨728960, by rfl⟩ : syracuseStep 971947 = 1457921) B1457921
theorem B3822785 : Blo 670310 3822785 := bstep (se 2 (by rfl) ⟨1433544, by rfl⟩ : syracuseStep 3822785 = 2867089) B2867089
theorem B3888499 : Blo 670310 3888499 := bstep (se 1 (by rfl) ⟨2916374, by rfl⟩ : syracuseStep 3888499 = 5832749) B5832749
theorem B1135991 : Blo 670310 1135991 := bstep (se 1 (by rfl) ⟨851993, by rfl⟩ : syracuseStep 1135991 = 1703987) B1703987
theorem B4904339 : Blo 670310 4904339 := bstep (se 1 (by rfl) ⟨3678254, by rfl⟩ : syracuseStep 4904339 = 7356509) B7356509
theorem B1136443 : Blo 670310 1136443 := bstep (se 1 (by rfl) ⟨852332, by rfl⟩ : syracuseStep 1136443 = 1704665) B1704665
theorem B6444953 : Blo 670310 6444953 := bstep (se 2 (by rfl) ⟨2416857, by rfl⟩ : syracuseStep 6444953 = 4833715) B4833715
theorem B1005497 : Blo 670310 1005497 := bstep (se 2 (by rfl) ⟨377061, by rfl⟩ : syracuseStep 1005497 = 754123) B754123
theorem B1136585 : Blo 670310 1136585 := bstep (se 2 (by rfl) ⟨426219, by rfl⟩ : syracuseStep 1136585 = 852439) B852439
theorem B1005575 : Blo 670310 1005575 := bstep (se 1 (by rfl) ⟨754181, by rfl⟩ : syracuseStep 1005575 = 1508363) B1508363
theorem B1005611 : Blo 670310 1005611 := bstep (se 1 (by rfl) ⟨754208, by rfl⟩ : syracuseStep 1005611 = 1508417) B1508417
theorem B1005641 : Blo 670310 1005641 := bstep (se 2 (by rfl) ⟨377115, by rfl⟩ : syracuseStep 1005641 = 754231) B754231
theorem B1005755 : Blo 670310 1005755 := bstep (se 1 (by rfl) ⟨754316, by rfl⟩ : syracuseStep 1005755 = 1508633) B1508633
theorem B1005815 : Blo 670310 1005815 := bstep (se 1 (by rfl) ⟨754361, by rfl⟩ : syracuseStep 1005815 = 1508723) B1508723
theorem B1005839 : Blo 670310 1005839 := bstep (se 1 (by rfl) ⟨754379, by rfl⟩ : syracuseStep 1005839 = 1508759) B1508759
theorem B4839713 : Blo 670310 4839713 := bstep (se 2 (by rfl) ⟨1814892, by rfl⟩ : syracuseStep 4839713 = 3629785) B3629785
theorem B1005881 : Blo 670310 1005881 := bstep (se 2 (by rfl) ⟨377205, by rfl⟩ : syracuseStep 1005881 = 754411) B754411
theorem B3234163 : Blo 670310 3234163 := bstep (se 1 (by rfl) ⟨2425622, by rfl⟩ : syracuseStep 3234163 = 4851245) B4851245
theorem B1005959 : Blo 670310 1005959 := bstep (se 1 (by rfl) ⟨754469, by rfl⟩ : syracuseStep 1005959 = 1508939) B1508939
theorem B1005995 : Blo 670310 1005995 := bstep (se 1 (by rfl) ⟨754496, by rfl⟩ : syracuseStep 1005995 = 1508993) B1508993
theorem B1006025 : Blo 670310 1006025 := bstep (se 2 (by rfl) ⟨377259, by rfl⟩ : syracuseStep 1006025 = 754519) B754519
theorem B1006139 : Blo 670310 1006139 := bstep (se 1 (by rfl) ⟨754604, by rfl⟩ : syracuseStep 1006139 = 1509209) B1509209
theorem B1006199 : Blo 670310 1006199 := bstep (se 1 (by rfl) ⟨754649, by rfl⟩ : syracuseStep 1006199 = 1509299) B1509299
theorem B1137287 : Blo 670310 1137287 := bstep (se 1 (by rfl) ⟨852965, by rfl⟩ : syracuseStep 1137287 = 1705931) B1705931
theorem B1006223 : Blo 670310 1006223 := bstep (se 1 (by rfl) ⟨754667, by rfl⟩ : syracuseStep 1006223 = 1509335) B1509335
theorem B1006265 : Blo 670310 1006265 := bstep (se 2 (by rfl) ⟨377349, by rfl⟩ : syracuseStep 1006265 = 754699) B754699
theorem B2874113 : Blo 670310 2874113 := bstep (se 2 (by rfl) ⟨1077792, by rfl⟩ : syracuseStep 2874113 = 2155585) B2155585
theorem B1006343 : Blo 670310 1006343 := bstep (se 1 (by rfl) ⟨754757, by rfl⟩ : syracuseStep 1006343 = 1509515) B1509515
theorem B809743 : Blo 670310 809743 := bstep (se 1 (by rfl) ⟨607307, by rfl⟩ : syracuseStep 809743 = 1214615) B1214615
theorem B1006379 : Blo 670310 1006379 := bstep (se 1 (by rfl) ⟨754784, by rfl⟩ : syracuseStep 1006379 = 1509569) B1509569
theorem B809771 : Blo 670310 809771 := bstep (se 1 (by rfl) ⟨607328, by rfl⟩ : syracuseStep 809771 = 1214657) B1214657
theorem B1006409 : Blo 670310 1006409 := bstep (se 2 (by rfl) ⟨377403, by rfl⟩ : syracuseStep 1006409 = 754807) B754807
theorem B2546579 : Blo 670310 2546579 := bstep (se 1 (by rfl) ⟨1909934, by rfl⟩ : syracuseStep 2546579 = 3819869) B3819869
theorem B1006523 : Blo 670310 1006523 := bstep (se 1 (by rfl) ⟨754892, by rfl⟩ : syracuseStep 1006523 = 1509785) B1509785
theorem B1006583 : Blo 670310 1006583 := bstep (se 1 (by rfl) ⟨754937, by rfl⟩ : syracuseStep 1006583 = 1509875) B1509875
theorem B1006607 : Blo 670310 1006607 := bstep (se 1 (by rfl) ⟨754955, by rfl⟩ : syracuseStep 1006607 = 1509911) B1509911
theorem B1006649 : Blo 670310 1006649 := bstep (se 2 (by rfl) ⟨377493, by rfl⟩ : syracuseStep 1006649 = 754987) B754987
theorem B1006727 : Blo 670310 1006727 := bstep (se 1 (by rfl) ⟨755045, by rfl⟩ : syracuseStep 1006727 = 1510091) B1510091
theorem B1006763 : Blo 670310 1006763 := bstep (se 1 (by rfl) ⟨755072, by rfl⟩ : syracuseStep 1006763 = 1510145) B1510145
theorem B1006793 : Blo 670310 1006793 := bstep (se 2 (by rfl) ⟨377547, by rfl⟩ : syracuseStep 1006793 = 755095) B755095
theorem B1006907 : Blo 670310 1006907 := bstep (se 1 (by rfl) ⟨755180, by rfl⟩ : syracuseStep 1006907 = 1510361) B1510361
theorem B1006967 : Blo 670310 1006967 := bstep (se 1 (by rfl) ⟨755225, by rfl⟩ : syracuseStep 1006967 = 1510451) B1510451
theorem B1006991 : Blo 670310 1006991 := bstep (se 1 (by rfl) ⟨755243, by rfl⟩ : syracuseStep 1006991 = 1510487) B1510487
theorem B1007033 : Blo 670310 1007033 := bstep (se 2 (by rfl) ⟨377637, by rfl⟩ : syracuseStep 1007033 = 755275) B755275
theorem B2416081 : Blo 670310 2416081 := bstep (se 2 (by rfl) ⟨906030, by rfl⟩ : syracuseStep 2416081 = 1812061) B1812061
theorem B1007111 : Blo 670310 1007111 := bstep (se 1 (by rfl) ⟨755333, by rfl⟩ : syracuseStep 1007111 = 1510667) B1510667
theorem B1007147 : Blo 670310 1007147 := bstep (se 1 (by rfl) ⟨755360, by rfl⟩ : syracuseStep 1007147 = 1510721) B1510721
theorem B1007177 : Blo 670310 1007177 := bstep (se 2 (by rfl) ⟨377691, by rfl⟩ : syracuseStep 1007177 = 755383) B755383
theorem B1007291 : Blo 670310 1007291 := bstep (se 1 (by rfl) ⟨755468, by rfl⟩ : syracuseStep 1007291 = 1510937) B1510937
theorem B1007351 : Blo 670310 1007351 := bstep (se 1 (by rfl) ⟨755513, by rfl⟩ : syracuseStep 1007351 = 1511027) B1511027
theorem B2416385 : Blo 670310 2416385 := bstep (se 2 (by rfl) ⟨906144, by rfl⟩ : syracuseStep 2416385 = 1812289) B1812289
theorem B1007375 : Blo 670310 1007375 := bstep (se 1 (by rfl) ⟨755531, by rfl⟩ : syracuseStep 1007375 = 1511063) B1511063
theorem B1007417 : Blo 670310 1007417 := bstep (se 2 (by rfl) ⟨377781, by rfl⟩ : syracuseStep 1007417 = 755563) B755563
theorem B1007495 : Blo 670310 1007495 := bstep (se 1 (by rfl) ⟨755621, by rfl⟩ : syracuseStep 1007495 = 1511243) B1511243
theorem B3399569 : Blo 670310 3399569 := bstep (se 2 (by rfl) ⟨1274838, by rfl⟩ : syracuseStep 3399569 = 2549677) B2549677
theorem B1007531 : Blo 670310 1007531 := bstep (se 1 (by rfl) ⟨755648, by rfl⟩ : syracuseStep 1007531 = 1511297) B1511297
theorem B1007561 : Blo 670310 1007561 := bstep (se 2 (by rfl) ⟨377835, by rfl⟩ : syracuseStep 1007561 = 755671) B755671
theorem B1007675 : Blo 670310 1007675 := bstep (se 1 (by rfl) ⟨755756, by rfl⟩ : syracuseStep 1007675 = 1511513) B1511513
theorem B1007735 : Blo 670310 1007735 := bstep (se 1 (by rfl) ⟨755801, by rfl⟩ : syracuseStep 1007735 = 1511603) B1511603
theorem B1532039 : Blo 670310 1532039 := bstep (se 1 (by rfl) ⟨1149029, by rfl⟩ : syracuseStep 1532039 = 2298059) B2298059
theorem B1007759 : Blo 670310 1007759 := bstep (se 1 (by rfl) ⟨755819, by rfl⟩ : syracuseStep 1007759 = 1511639) B1511639
theorem B1007801 : Blo 670310 1007801 := bstep (se 2 (by rfl) ⟨377925, by rfl⟩ : syracuseStep 1007801 = 755851) B755851
theorem B1433801 : Blo 670310 1433801 := bstep (se 2 (by rfl) ⟨537675, by rfl⟩ : syracuseStep 1433801 = 1075351) B1075351
theorem B1007879 : Blo 670310 1007879 := bstep (se 1 (by rfl) ⟨755909, by rfl⟩ : syracuseStep 1007879 = 1511819) B1511819
theorem B3825953 : Blo 670310 3825953 := bstep (se 2 (by rfl) ⟨1434732, by rfl⟩ : syracuseStep 3825953 = 2869465) B2869465
theorem B1007915 : Blo 670310 1007915 := bstep (se 1 (by rfl) ⟨755936, by rfl⟩ : syracuseStep 1007915 = 1511873) B1511873
theorem B1007945 : Blo 670310 1007945 := bstep (se 2 (by rfl) ⟨377979, by rfl⟩ : syracuseStep 1007945 = 755959) B755959
theorem B1008059 : Blo 670310 1008059 := bstep (se 1 (by rfl) ⟨756044, by rfl⟩ : syracuseStep 1008059 = 1512089) B1512089
theorem B1008119 : Blo 670310 1008119 := bstep (se 1 (by rfl) ⟨756089, by rfl⟩ : syracuseStep 1008119 = 1512179) B1512179
theorem B1008143 : Blo 670310 1008143 := bstep (se 1 (by rfl) ⟨756107, by rfl⟩ : syracuseStep 1008143 = 1512215) B1512215
theorem B3236395 : Blo 670310 3236395 := bstep (se 1 (by rfl) ⟨2427296, by rfl⟩ : syracuseStep 3236395 = 4854593) B4854593
theorem B1008185 : Blo 670310 1008185 := bstep (se 2 (by rfl) ⟨378069, by rfl⟩ : syracuseStep 1008185 = 756139) B756139
theorem B3072599 : Blo 670310 3072599 := bstep (se 1 (by rfl) ⟨2304449, by rfl⟩ : syracuseStep 3072599 = 4608899) B4608899
theorem B1008263 : Blo 670310 1008263 := bstep (se 1 (by rfl) ⟨756197, by rfl⟩ : syracuseStep 1008263 = 1512395) B1512395
theorem B1008299 : Blo 670310 1008299 := bstep (se 1 (by rfl) ⟨756224, by rfl⟩ : syracuseStep 1008299 = 1512449) B1512449
theorem B1008329 : Blo 670310 1008329 := bstep (se 2 (by rfl) ⟨378123, by rfl⟩ : syracuseStep 1008329 = 756247) B756247
theorem B1008443 : Blo 670310 1008443 := bstep (se 1 (by rfl) ⟨756332, by rfl⟩ : syracuseStep 1008443 = 1512665) B1512665
theorem B1008503 : Blo 670310 1008503 := bstep (se 1 (by rfl) ⟨756377, by rfl⟩ : syracuseStep 1008503 = 1512755) B1512755
theorem B1008527 : Blo 670310 1008527 := bstep (se 1 (by rfl) ⟨756395, by rfl⟩ : syracuseStep 1008527 = 1512791) B1512791
theorem B1008569 : Blo 670310 1008569 := bstep (se 2 (by rfl) ⟨378213, by rfl⟩ : syracuseStep 1008569 = 756427) B756427
theorem B1008647 : Blo 670310 1008647 := bstep (se 1 (by rfl) ⟨756485, by rfl⟩ : syracuseStep 1008647 = 1512971) B1512971
theorem B5760011 : Blo 670310 5760011 := bstep (se 1 (by rfl) ⟨4320008, by rfl⟩ : syracuseStep 5760011 = 8640017) B8640017
theorem B1008683 : Blo 670310 1008683 := bstep (se 1 (by rfl) ⟨756512, by rfl⟩ : syracuseStep 1008683 = 1513025) B1513025
theorem B1008713 : Blo 670310 1008713 := bstep (se 2 (by rfl) ⟨378267, by rfl⟩ : syracuseStep 1008713 = 756535) B756535
theorem B1434809 : Blo 670310 1434809 := bstep (se 2 (by rfl) ⟨538053, by rfl⟩ : syracuseStep 1434809 = 1076107) B1076107
theorem B1008827 : Blo 670310 1008827 := bstep (se 1 (by rfl) ⟨756620, by rfl⟩ : syracuseStep 1008827 = 1513241) B1513241
theorem B1008887 : Blo 670310 1008887 := bstep (se 1 (by rfl) ⟨756665, by rfl⟩ : syracuseStep 1008887 = 1513331) B1513331
theorem B1008911 : Blo 670310 1008911 := bstep (se 1 (by rfl) ⟨756683, by rfl⟩ : syracuseStep 1008911 = 1513367) B1513367
theorem B1008953 : Blo 670310 1008953 := bstep (se 2 (by rfl) ⟨378357, by rfl⟩ : syracuseStep 1008953 = 756715) B756715
theorem B1009031 : Blo 670310 1009031 := bstep (se 1 (by rfl) ⟨756773, by rfl⟩ : syracuseStep 1009031 = 1513547) B1513547
theorem B1009067 : Blo 670310 1009067 := bstep (se 1 (by rfl) ⟨756800, by rfl⟩ : syracuseStep 1009067 = 1513601) B1513601
theorem B2549177 : Blo 670310 2549177 := bstep (se 2 (by rfl) ⟨955941, by rfl⟩ : syracuseStep 2549177 = 1911883) B1911883
theorem B1009097 : Blo 670310 1009097 := bstep (se 2 (by rfl) ⟨378411, by rfl⟩ : syracuseStep 1009097 = 756823) B756823
theorem B6448643 : Blo 670310 6448643 := bstep (se 1 (by rfl) ⟨4836482, by rfl⟩ : syracuseStep 6448643 = 9672965) B9672965
theorem B1435151 : Blo 670310 1435151 := bstep (se 1 (by rfl) ⟨1076363, by rfl⟩ : syracuseStep 1435151 = 2152727) B2152727
theorem B1009211 : Blo 670310 1009211 := bstep (se 1 (by rfl) ⟨756908, by rfl⟩ : syracuseStep 1009211 = 1513817) B1513817
theorem B2451005 : Blo 670310 2451005 := bstep (se 3 (by rfl) ⟨459563, by rfl⟩ : syracuseStep 2451005 = 919127) B919127
theorem B1697395 : Blo 670310 1697395 := bstep (se 1 (by rfl) ⟨1273046, by rfl⟩ : syracuseStep 1697395 = 2546093) B2546093
theorem B1009271 : Blo 670310 1009271 := bstep (se 1 (by rfl) ⟨756953, by rfl⟩ : syracuseStep 1009271 = 1513907) B1513907
theorem B1009295 : Blo 670310 1009295 := bstep (se 1 (by rfl) ⟨756971, by rfl⟩ : syracuseStep 1009295 = 1513943) B1513943
theorem B1009337 : Blo 670310 1009337 := bstep (se 2 (by rfl) ⟨378501, by rfl⟩ : syracuseStep 1009337 = 757003) B757003
theorem B1697537 : Blo 670310 1697537 := bstep (se 2 (by rfl) ⟨636576, by rfl⟩ : syracuseStep 1697537 = 1273153) B1273153
theorem B1009415 : Blo 670310 1009415 := bstep (se 1 (by rfl) ⟨757061, by rfl⟩ : syracuseStep 1009415 = 1514123) B1514123
theorem B1009451 : Blo 670310 1009451 := bstep (se 1 (by rfl) ⟨757088, by rfl⟩ : syracuseStep 1009451 = 1514177) B1514177
theorem B1009481 : Blo 670310 1009481 := bstep (se 2 (by rfl) ⟨378555, by rfl⟩ : syracuseStep 1009481 = 757111) B757111
theorem B33613643 : Blo 670310 33613643 := bstep (se 1 (by rfl) ⟨25210232, by rfl⟩ : syracuseStep 33613643 = 50420465) B50420465
theorem B3073945 : Blo 670310 3073945 := bstep (se 2 (by rfl) ⟨1152729, by rfl⟩ : syracuseStep 3073945 = 2305459) B2305459
theorem B2418617 : Blo 670310 2418617 := bstep (se 2 (by rfl) ⟨906981, by rfl⟩ : syracuseStep 2418617 = 1813963) B1813963
theorem B1009595 : Blo 670310 1009595 := bstep (se 1 (by rfl) ⟨757196, by rfl⟩ : syracuseStep 1009595 = 1514393) B1514393
theorem B3401675 : Blo 670310 3401675 := bstep (se 1 (by rfl) ⟨2551256, by rfl⟩ : syracuseStep 3401675 = 5102513) B5102513
theorem B1009655 : Blo 670310 1009655 := bstep (se 1 (by rfl) ⟨757241, by rfl⟩ : syracuseStep 1009655 = 1514483) B1514483
theorem B4319243 : Blo 670310 4319243 := bstep (se 1 (by rfl) ⟨3239432, by rfl⟩ : syracuseStep 4319243 = 6478865) B6478865
theorem B1009679 : Blo 670310 1009679 := bstep (se 1 (by rfl) ⟨757259, by rfl⟩ : syracuseStep 1009679 = 1514519) B1514519
theorem B1009721 : Blo 670310 1009721 := bstep (se 2 (by rfl) ⟨378645, by rfl⟩ : syracuseStep 1009721 = 757291) B757291
theorem B1009799 : Blo 670310 1009799 := bstep (se 1 (by rfl) ⟨757349, by rfl⟩ : syracuseStep 1009799 = 1514699) B1514699
theorem B1009835 : Blo 670310 1009835 := bstep (se 1 (by rfl) ⟨757376, by rfl⟩ : syracuseStep 1009835 = 1514753) B1514753
theorem B1697993 : Blo 670310 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B1009865 : Blo 670310 1009865 := bstep (se 2 (by rfl) ⟨378699, by rfl⟩ : syracuseStep 1009865 = 757399) B757399
theorem B3401999 : Blo 670310 3401999 := bstep (se 1 (by rfl) ⟨2551499, by rfl⟩ : syracuseStep 3401999 = 5102999) B5102999
theorem B1435963 : Blo 670310 1435963 := bstep (se 1 (by rfl) ⟨1076972, by rfl⟩ : syracuseStep 1435963 = 2153945) B2153945
theorem B1009979 : Blo 670310 1009979 := bstep (se 1 (by rfl) ⟨757484, by rfl⟩ : syracuseStep 1009979 = 1514969) B1514969
theorem B20670785 : Blo 670310 20670785 := bstep (se 2 (by rfl) ⟨7751544, by rfl⟩ : syracuseStep 20670785 = 15503089) B15503089
theorem B1632599 : Blo 670310 1632599 := bstep (se 1 (by rfl) ⟨1224449, by rfl⟩ : syracuseStep 1632599 = 2448899) B2448899
theorem B1010039 : Blo 670310 1010039 := bstep (se 1 (by rfl) ⟨757529, by rfl⟩ : syracuseStep 1010039 = 1515059) B1515059
theorem B1010063 : Blo 670310 1010063 := bstep (se 1 (by rfl) ⟨757547, by rfl⟩ : syracuseStep 1010063 = 1515095) B1515095
theorem B2550163 : Blo 670310 2550163 := bstep (se 1 (by rfl) ⟨1912622, by rfl⟩ : syracuseStep 2550163 = 3825245) B3825245
theorem B1010105 : Blo 670310 1010105 := bstep (se 2 (by rfl) ⟨378789, by rfl⟩ : syracuseStep 1010105 = 757579) B757579
theorem B1010183 : Blo 670310 1010183 := bstep (se 1 (by rfl) ⟨757637, by rfl⟩ : syracuseStep 1010183 = 1515275) B1515275
theorem B1698347 : Blo 670310 1698347 := bstep (se 1 (by rfl) ⟨1273760, by rfl⟩ : syracuseStep 1698347 = 2547521) B2547521
theorem B1010219 : Blo 670310 1010219 := bstep (se 1 (by rfl) ⟨757664, by rfl⟩ : syracuseStep 1010219 = 1515329) B1515329
theorem B2419267 : Blo 670310 2419267 := bstep (se 1 (by rfl) ⟨1814450, by rfl⟩ : syracuseStep 2419267 = 3628901) B3628901
theorem B1010249 : Blo 670310 1010249 := bstep (se 2 (by rfl) ⟨378843, by rfl⟩ : syracuseStep 1010249 = 757687) B757687
theorem B3828343 : Blo 670310 3828343 := bstep (se 1 (by rfl) ⟨2871257, by rfl⟩ : syracuseStep 3828343 = 5742515) B5742515
theorem B1010363 : Blo 670310 1010363 := bstep (se 1 (by rfl) ⟨757772, by rfl⟩ : syracuseStep 1010363 = 1515545) B1515545
theorem B1010423 : Blo 670310 1010423 := bstep (se 1 (by rfl) ⟨757817, by rfl⟩ : syracuseStep 1010423 = 1515635) B1515635
theorem B1010447 : Blo 670310 1010447 := bstep (se 1 (by rfl) ⟨757835, by rfl⟩ : syracuseStep 1010447 = 1515671) B1515671
theorem B1436449 : Blo 670310 1436449 := bstep (se 2 (by rfl) ⟨538668, by rfl⟩ : syracuseStep 1436449 = 1077337) B1077337
theorem B1010489 : Blo 670310 1010489 := bstep (se 2 (by rfl) ⟨378933, by rfl⟩ : syracuseStep 1010489 = 757867) B757867
theorem B1010567 : Blo 670310 1010567 := bstep (se 1 (by rfl) ⟨757925, by rfl⟩ : syracuseStep 1010567 = 1515851) B1515851
theorem B1010603 : Blo 670310 1010603 := bstep (se 1 (by rfl) ⟨757952, by rfl⟩ : syracuseStep 1010603 = 1515905) B1515905
theorem B1010633 : Blo 670310 1010633 := bstep (se 2 (by rfl) ⟨378987, by rfl⟩ : syracuseStep 1010633 = 757975) B757975
theorem B2419741 : Blo 670310 2419741 := bstep (se 3 (by rfl) ⟨453701, by rfl⟩ : syracuseStep 2419741 = 907403) B907403
theorem B1010747 : Blo 670310 1010747 := bstep (se 1 (by rfl) ⟨758060, by rfl⟩ : syracuseStep 1010747 = 1516121) B1516121
theorem B4320317 : Blo 670310 4320317 := bstep (se 3 (by rfl) ⟨810059, by rfl⟩ : syracuseStep 4320317 = 1620119) B1620119
theorem B1436791 : Blo 670310 1436791 := bstep (se 1 (by rfl) ⟨1077593, by rfl⟩ : syracuseStep 1436791 = 2155187) B2155187
theorem B1010807 : Blo 670310 1010807 := bstep (se 1 (by rfl) ⟨758105, by rfl⟩ : syracuseStep 1010807 = 1516211) B1516211
theorem B1010831 : Blo 670310 1010831 := bstep (se 1 (by rfl) ⟨758123, by rfl⟩ : syracuseStep 1010831 = 1516247) B1516247
theorem B1010873 : Blo 670310 1010873 := bstep (se 2 (by rfl) ⟨379077, by rfl⟩ : syracuseStep 1010873 = 758155) B758155
theorem B1010951 : Blo 670310 1010951 := bstep (se 1 (by rfl) ⟨758213, by rfl⟩ : syracuseStep 1010951 = 1516427) B1516427
theorem B1010987 : Blo 670310 1010987 := bstep (se 1 (by rfl) ⟨758240, by rfl⟩ : syracuseStep 1010987 = 1516481) B1516481
theorem B1011017 : Blo 670310 1011017 := bstep (se 2 (by rfl) ⟨379131, by rfl⟩ : syracuseStep 1011017 = 758263) B758263
theorem B10874243 : Blo 670310 10874243 := bstep (se 1 (by rfl) ⟨8155682, by rfl⟩ : syracuseStep 10874243 = 16311365) B16311365
theorem B683407 : Blo 670310 683407 := bstep (se 1 (by rfl) ⟨512555, by rfl⟩ : syracuseStep 683407 = 1025111) B1025111
theorem B1076665 : Blo 670310 1076665 := bstep (se 2 (by rfl) ⟨403749, by rfl⟩ : syracuseStep 1076665 = 807499) B807499
theorem B1011131 : Blo 670310 1011131 := bstep (se 1 (by rfl) ⟨758348, by rfl⟩ : syracuseStep 1011131 = 1516697) B1516697
theorem B1011191 : Blo 670310 1011191 := bstep (se 1 (by rfl) ⟨758393, by rfl⟩ : syracuseStep 1011191 = 1516787) B1516787
theorem B1699339 : Blo 670310 1699339 := bstep (se 1 (by rfl) ⟨1274504, by rfl⟩ : syracuseStep 1699339 = 2549009) B2549009
theorem B1011215 : Blo 670310 1011215 := bstep (se 1 (by rfl) ⟨758411, by rfl⟩ : syracuseStep 1011215 = 1516823) B1516823
theorem B2158109 : Blo 670310 2158109 := bstep (se 3 (by rfl) ⟨404645, by rfl⟩ : syracuseStep 2158109 = 809291) B809291
theorem B1011257 : Blo 670310 1011257 := bstep (se 2 (by rfl) ⟨379221, by rfl⟩ : syracuseStep 1011257 = 758443) B758443
theorem B1011335 : Blo 670310 1011335 := bstep (se 1 (by rfl) ⟨758501, by rfl⟩ : syracuseStep 1011335 = 1517003) B1517003
theorem B1699481 : Blo 670310 1699481 := bstep (se 2 (by rfl) ⟨637305, by rfl⟩ : syracuseStep 1699481 = 1274611) B1274611
theorem B1011371 : Blo 670310 1011371 := bstep (se 1 (by rfl) ⟨758528, by rfl⟩ : syracuseStep 1011371 = 1517057) B1517057
theorem B3632813 : Blo 670310 3632813 := bstep (se 3 (by rfl) ⟨681152, by rfl⟩ : syracuseStep 3632813 = 1362305) B1362305
theorem B3403457 : Blo 670310 3403457 := bstep (se 2 (by rfl) ⟨1276296, by rfl⟩ : syracuseStep 3403457 = 2552593) B2552593
theorem B1011401 : Blo 670310 1011401 := bstep (se 2 (by rfl) ⟨379275, by rfl⟩ : syracuseStep 1011401 = 758551) B758551
theorem B4091681 : Blo 670310 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B1699643 : Blo 670310 1699643 := bstep (se 1 (by rfl) ⟨1274732, by rfl⟩ : syracuseStep 1699643 = 2549465) B2549465
theorem B3829619 : Blo 670310 3829619 := bstep (se 1 (by rfl) ⟨2872214, by rfl⟩ : syracuseStep 3829619 = 5744429) B5744429
theorem B2420779 : Blo 670310 2420779 := bstep (se 1 (by rfl) ⟨1815584, by rfl⟩ : syracuseStep 2420779 = 3631169) B3631169
theorem B2551895 : Blo 670310 2551895 := bstep (se 1 (by rfl) ⟨1913921, by rfl⟩ : syracuseStep 2551895 = 3827843) B3827843
theorem B2912375 : Blo 670310 2912375 := bstep (se 1 (by rfl) ⟨2184281, by rfl⟩ : syracuseStep 2912375 = 4368563) B4368563
theorem B8188037 : Blo 670310 8188037 := bstep (se 4 (by rfl) ⟨767628, by rfl⟩ : syracuseStep 8188037 = 1535257) B1535257
theorem B1077383 : Blo 670310 1077383 := bstep (se 1 (by rfl) ⟨808037, by rfl⟩ : syracuseStep 1077383 = 1616075) B1616075
theorem B1699987 : Blo 670310 1699987 := bstep (se 1 (by rfl) ⟨1274990, by rfl⟩ : syracuseStep 1699987 = 2549981) B2549981
theorem B1700129 : Blo 670310 1700129 := bstep (se 2 (by rfl) ⟨637548, by rfl⟩ : syracuseStep 1700129 = 1275097) B1275097
theorem B3830075 : Blo 670310 3830075 := bstep (se 1 (by rfl) ⟨2872556, by rfl⟩ : syracuseStep 3830075 = 5745113) B5745113
theorem B1274231 : Blo 670310 1274231 := bstep (se 1 (by rfl) ⟨955673, by rfl⟩ : syracuseStep 1274231 = 1911347) B1911347
theorem B1208711 : Blo 670310 1208711 := bstep (se 1 (by rfl) ⟨906533, by rfl⟩ : syracuseStep 1208711 = 1813067) B1813067
theorem B717319 : Blo 670310 717319 := bstep (se 1 (by rfl) ⟨537989, by rfl⟩ : syracuseStep 717319 = 1075979) B1075979
theorem B1274383 : Blo 670310 1274383 := bstep (se 1 (by rfl) ⟨955787, by rfl⟩ : syracuseStep 1274383 = 1911575) B1911575
theorem B2552381 : Blo 670310 2552381 := bstep (se 3 (by rfl) ⟨478571, by rfl⟩ : syracuseStep 2552381 = 957143) B957143
theorem B12907127 : Blo 670310 12907127 := bstep (se 1 (by rfl) ⟨9680345, by rfl⟩ : syracuseStep 12907127 = 19360691) B19360691
theorem B1077895 : Blo 670310 1077895 := bstep (se 1 (by rfl) ⟨808421, by rfl⟩ : syracuseStep 1077895 = 1616843) B1616843
theorem B848647 : Blo 670310 848647 := bstep (se 1 (by rfl) ⟨636485, by rfl⟩ : syracuseStep 848647 = 1272971) B1272971
theorem B1274771 : Blo 670310 1274771 := bstep (se 1 (by rfl) ⟨956078, by rfl⟩ : syracuseStep 1274771 = 1912157) B1912157
theorem B3404753 : Blo 670310 3404753 := bstep (se 2 (by rfl) ⟨1276782, by rfl⟩ : syracuseStep 3404753 = 2553565) B2553565
theorem B849143 : Blo 670310 849143 := bstep (se 1 (by rfl) ⟨636857, by rfl⟩ : syracuseStep 849143 = 1273715) B1273715
theorem B1701121 : Blo 670310 1701121 := bstep (se 2 (by rfl) ⟨637920, by rfl⟩ : syracuseStep 1701121 = 1275841) B1275841
theorem B3831077 : Blo 670310 3831077 := bstep (se 4 (by rfl) ⟨359163, by rfl⟩ : syracuseStep 3831077 = 718327) B718327
theorem B849295 : Blo 670310 849295 := bstep (se 1 (by rfl) ⟨636971, by rfl⟩ : syracuseStep 849295 = 1273943) B1273943
theorem B2422163 : Blo 670310 2422163 := bstep (se 1 (by rfl) ⟨1816622, by rfl⟩ : syracuseStep 2422163 = 3633245) B3633245
theorem B849467 : Blo 670310 849467 := bstep (se 1 (by rfl) ⟨637100, by rfl⟩ : syracuseStep 849467 = 1274201) B1274201
theorem B3831533 : Blo 670310 3831533 := bstep (se 3 (by rfl) ⟨718412, by rfl⟩ : syracuseStep 3831533 = 1436825) B1436825
theorem B5601061 : Blo 670310 5601061 := bstep (se 4 (by rfl) ⟨525099, by rfl⟩ : syracuseStep 5601061 = 1050199) B1050199
theorem B1701719 : Blo 670310 1701719 := bstep (se 1 (by rfl) ⟨1276289, by rfl⟩ : syracuseStep 1701719 = 2552579) B2552579
theorem B19363697 : Blo 670310 19363697 := bstep (se 2 (by rfl) ⟨7261386, by rfl⟩ : syracuseStep 19363697 = 14522773) B14522773
theorem B6453107 : Blo 670310 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B1701931 : Blo 670310 1701931 := bstep (se 1 (by rfl) ⟨1276448, by rfl⟩ : syracuseStep 1701931 = 2552897) B2552897
theorem B1702073 : Blo 670310 1702073 := bstep (se 2 (by rfl) ⟨638277, by rfl⟩ : syracuseStep 1702073 = 1276555) B1276555
theorem B1276175 : Blo 670310 1276175 := bstep (se 1 (by rfl) ⟨957131, by rfl⟩ : syracuseStep 1276175 = 1914263) B1914263
theorem B3832217 : Blo 670310 3832217 := bstep (se 2 (by rfl) ⟨1437081, by rfl⟩ : syracuseStep 3832217 = 2874163) B2874163
theorem B850439 : Blo 670310 850439 := bstep (se 1 (by rfl) ⟨637829, by rfl⟩ : syracuseStep 850439 = 1275659) B1275659
theorem B4094657 : Blo 670310 4094657 := bstep (se 2 (by rfl) ⟨1535496, by rfl⟩ : syracuseStep 4094657 = 3070993) B3070993
theorem B1276715 : Blo 670310 1276715 := bstep (se 1 (by rfl) ⟨957536, by rfl⟩ : syracuseStep 1276715 = 1915073) B1915073
theorem B1211255 : Blo 670310 1211255 := bstep (se 1 (by rfl) ⟨908441, by rfl⟩ : syracuseStep 1211255 = 1816883) B1816883
theorem B3406859 : Blo 670310 3406859 := bstep (se 1 (by rfl) ⟨2555144, by rfl⟩ : syracuseStep 3406859 = 5110289) B5110289
theorem B851087 : Blo 670310 851087 := bstep (se 1 (by rfl) ⟨638315, by rfl⟩ : syracuseStep 851087 = 1276631) B1276631
theorem B1703065 : Blo 670310 1703065 := bstep (se 2 (by rfl) ⟨638649, by rfl⟩ : syracuseStep 1703065 = 1277299) B1277299
theorem B3407021 : Blo 670310 3407021 := bstep (se 3 (by rfl) ⟨638816, by rfl⟩ : syracuseStep 3407021 = 1277633) B1277633
theorem B1703227 : Blo 670310 1703227 := bstep (se 1 (by rfl) ⟨1277420, by rfl⟩ : syracuseStep 1703227 = 2554841) B2554841
theorem B5733767 : Blo 670310 5733767 := bstep (se 1 (by rfl) ⟨4300325, by rfl⟩ : syracuseStep 5733767 = 8600651) B8600651
theorem B1703369 : Blo 670310 1703369 := bstep (se 2 (by rfl) ⟨638763, by rfl⟩ : syracuseStep 1703369 = 1277527) B1277527
theorem B5111261 : Blo 670310 5111261 := bstep (se 3 (by rfl) ⟨958361, by rfl⟩ : syracuseStep 5111261 = 1916723) B1916723
theorem B1703713 : Blo 670310 1703713 := bstep (se 2 (by rfl) ⟨638892, by rfl⟩ : syracuseStep 1703713 = 1277785) B1277785
theorem B1277831 : Blo 670310 1277831 := bstep (se 1 (by rfl) ⟨958373, by rfl⟩ : syracuseStep 1277831 = 1916747) B1916747
theorem B2555783 : Blo 670310 2555783 := bstep (se 1 (by rfl) ⟨1916837, by rfl⟩ : syracuseStep 2555783 = 3833675) B3833675
theorem B1147279 : Blo 670310 1147279 := bstep (se 1 (by rfl) ⟨860459, by rfl⟩ : syracuseStep 1147279 = 1720919) B1720919
theorem B1704473 : Blo 670310 1704473 := bstep (se 2 (by rfl) ⟨639177, by rfl⟩ : syracuseStep 1704473 = 1278355) B1278355
theorem B754375 : Blo 670310 754375 := bstep (se 1 (by rfl) ⟨565781, by rfl⟩ : syracuseStep 754375 = 1131563) B1131563
theorem B10879757 : Blo 670310 10879757 := bstep (se 3 (by rfl) ⟨2039954, by rfl⟩ : syracuseStep 10879757 = 4079909) B4079909
theorem B1278985 : Blo 670310 1278985 := bstep (se 2 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 1278985 = 959239) B959239
theorem B2720783 : Blo 670310 2720783 := bstep (se 1 (by rfl) ⟨2040587, by rfl⟩ : syracuseStep 2720783 = 4081175) B4081175
theorem B853031 : Blo 670310 853031 := bstep (se 1 (by rfl) ⟨639773, by rfl⟩ : syracuseStep 853031 = 1279547) B1279547
theorem B8619209 : Blo 670310 8619209 := bstep (se 2 (by rfl) ⟨3232203, by rfl⟩ : syracuseStep 8619209 = 6464407) B6464407
theorem B2557271 : Blo 670310 2557271 := bstep (se 1 (by rfl) ⟨1917953, by rfl⟩ : syracuseStep 2557271 = 3835907) B3835907
theorem B8750429 : Blo 670310 8750429 := bstep (se 3 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 8750429 = 3281411) B3281411
theorem B1279327 : Blo 670310 1279327 := bstep (se 1 (by rfl) ⟨959495, by rfl⟩ : syracuseStep 1279327 = 1918991) B1918991
theorem B853355 : Blo 670310 853355 := bstep (se 1 (by rfl) ⟨640016, by rfl⟩ : syracuseStep 853355 = 1280033) B1280033
theorem B2262491 : Blo 670310 2262491 := bstep (se 1 (by rfl) ⟨1696868, by rfl⟩ : syracuseStep 2262491 = 3393737) B3393737
theorem B1508903 : Blo 670310 1508903 := bstep (se 1 (by rfl) ⟨1131677, by rfl⟩ : syracuseStep 1508903 = 2263355) B2263355
theorem B755239 : Blo 670310 755239 := bstep (se 1 (by rfl) ⟨566429, by rfl⟩ : syracuseStep 755239 = 1132859) B1132859
theorem B1509227 : Blo 670310 1509227 := bstep (se 1 (by rfl) ⟨1131920, by rfl⟩ : syracuseStep 1509227 = 2263841) B2263841
theorem B1509281 : Blo 670310 1509281 := bstep (se 2 (by rfl) ⟨565980, by rfl⟩ : syracuseStep 1509281 = 1131961) B1131961
theorem B11503619 : Blo 670310 11503619 := bstep (se 1 (by rfl) ⟨8627714, by rfl⟩ : syracuseStep 11503619 = 17255429) B17255429
theorem B1378361 : Blo 670310 1378361 := bstep (se 2 (by rfl) ⟨516885, by rfl⟩ : syracuseStep 1378361 = 1033771) B1033771
theorem B2263193 : Blo 670310 2263193 := bstep (se 2 (by rfl) ⟨848697, by rfl⟩ : syracuseStep 2263193 = 1697395) B1697395
theorem B1509623 : Blo 670310 1509623 := bstep (se 1 (by rfl) ⟨1132217, by rfl⟩ : syracuseStep 1509623 = 2264435) B2264435
theorem B3639563 : Blo 670310 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B1214939 : Blo 670310 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B4295177 : Blo 670310 4295177 := bstep (se 2 (by rfl) ⟨1610691, by rfl⟩ : syracuseStep 4295177 = 3221383) B3221383
theorem B4098593 : Blo 670310 4098593 := bstep (se 2 (by rfl) ⟨1536972, by rfl⟩ : syracuseStep 4098593 = 3073945) B3073945
theorem B3443411 : Blo 670310 3443411 := bstep (se 1 (by rfl) ⟨2582558, by rfl⟩ : syracuseStep 3443411 = 5165117) B5165117
theorem B1510217 : Blo 670310 1510217 := bstep (se 2 (by rfl) ⟨566331, by rfl⟩ : syracuseStep 1510217 = 1132663) B1132663
theorem B756859 : Blo 670310 756859 := bstep (se 1 (by rfl) ⟨567644, by rfl⟩ : syracuseStep 756859 = 1135289) B1135289
theorem B4590863 : Blo 670310 4590863 := bstep (se 1 (by rfl) ⟨3443147, by rfl⟩ : syracuseStep 4590863 = 6886295) B6886295
theorem B2264381 : Blo 670310 2264381 := bstep (se 3 (by rfl) ⟨424571, by rfl⟩ : syracuseStep 2264381 = 849143) B849143
theorem B9702899 : Blo 670310 9702899 := bstep (se 1 (by rfl) ⟨7277174, by rfl⟩ : syracuseStep 9702899 = 14554349) B14554349
theorem B757327 : Blo 670310 757327 := bstep (se 1 (by rfl) ⟨567995, by rfl⟩ : syracuseStep 757327 = 1135991) B1135991
theorem B1511009 : Blo 670310 1511009 := bstep (se 2 (by rfl) ⟨566628, by rfl⟩ : syracuseStep 1511009 = 1133257) B1133257
theorem B6459101 : Blo 670310 6459101 := bstep (se 3 (by rfl) ⟨1211081, by rfl⟩ : syracuseStep 6459101 = 2422163) B2422163
theorem B1511351 : Blo 670310 1511351 := bstep (se 1 (by rfl) ⟨1133513, by rfl⟩ : syracuseStep 1511351 = 2267027) B2267027
theorem B4296635 : Blo 670310 4296635 := bstep (se 1 (by rfl) ⟨3222476, by rfl⟩ : syracuseStep 4296635 = 6444953) B6444953
theorem B757723 : Blo 670310 757723 := bstep (se 1 (by rfl) ⟨568292, by rfl⟩ : syracuseStep 757723 = 1136585) B1136585
theorem B13111307 : Blo 670310 13111307 := bstep (se 1 (by rfl) ⟨9833480, by rfl⟩ : syracuseStep 13111307 = 19666961) B19666961
theorem B2265245 : Blo 670310 2265245 := bstep (se 3 (by rfl) ⟨424733, by rfl⟩ : syracuseStep 2265245 = 849467) B849467
theorem B2560157 : Blo 670310 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B3641705 : Blo 670310 3641705 := bstep (se 2 (by rfl) ⟨1365639, by rfl⟩ : syracuseStep 3641705 = 2731279) B2731279
theorem B758191 : Blo 670310 758191 := bstep (se 1 (by rfl) ⟨568643, by rfl⟩ : syracuseStep 758191 = 1137287) B1137287
theorem B1511945 : Blo 670310 1511945 := bstep (se 2 (by rfl) ⟨566979, by rfl⟩ : syracuseStep 1511945 = 1133959) B1133959
theorem B2265785 : Blo 670310 2265785 := bstep (se 2 (by rfl) ⟨849669, by rfl⟩ : syracuseStep 2265785 = 1699339) B1699339
theorem B3412691 : Blo 670310 3412691 := bstep (se 1 (by rfl) ⟨2559518, by rfl⟩ : syracuseStep 3412691 = 5119037) B5119037
theorem B2429689 : Blo 670310 2429689 := bstep (se 2 (by rfl) ⟨911133, by rfl⟩ : syracuseStep 2429689 = 1822267) B1822267
theorem B14521133 : Blo 670310 14521133 := bstep (se 3 (by rfl) ⟨2722712, by rfl⟩ : syracuseStep 14521133 = 5445425) B5445425
theorem B1512287 : Blo 670310 1512287 := bstep (se 1 (by rfl) ⟨1134215, by rfl⟩ : syracuseStep 1512287 = 2268431) B2268431
theorem B1512467 : Blo 670310 1512467 := bstep (se 1 (by rfl) ⟨1134350, by rfl⟩ : syracuseStep 1512467 = 2268701) B2268701
theorem B1610923 : Blo 670310 1610923 := bstep (se 1 (by rfl) ⟨1208192, by rfl⟩ : syracuseStep 1610923 = 2416385) B2416385
theorem B2266379 : Blo 670310 2266379 := bstep (se 1 (by rfl) ⟨1699784, by rfl⟩ : syracuseStep 2266379 = 3399569) B3399569
theorem B1512809 : Blo 670310 1512809 := bstep (se 2 (by rfl) ⟨567303, by rfl⟩ : syracuseStep 1512809 = 1134607) B1134607
theorem B2266649 : Blo 670310 2266649 := bstep (se 2 (by rfl) ⟨849993, by rfl⟩ : syracuseStep 2266649 = 1699987) B1699987
theorem B5117579 : Blo 670310 5117579 := bstep (se 1 (by rfl) ⟨3838184, by rfl⟩ : syracuseStep 5117579 = 7676369) B7676369
theorem B1971911 : Blo 670310 1971911 := bstep (se 1 (by rfl) ⟨1478933, by rfl⟩ : syracuseStep 1971911 = 2957867) B2957867
theorem B1513403 : Blo 670310 1513403 := bstep (se 1 (by rfl) ⟨1135052, by rfl⟩ : syracuseStep 1513403 = 2270105) B2270105
theorem B3840007 : Blo 670310 3840007 := bstep (se 1 (by rfl) ⟨2880005, by rfl⟩ : syracuseStep 3840007 = 5760011) B5760011
theorem B1513529 : Blo 670310 1513529 := bstep (se 2 (by rfl) ⟨567573, by rfl⟩ : syracuseStep 1513529 = 1135147) B1135147
theorem B956539 : Blo 670310 956539 := bstep (se 1 (by rfl) ⟨717404, by rfl⟩ : syracuseStep 956539 = 1434809) B1434809
theorem B3447101 : Blo 670310 3447101 := bstep (se 3 (by rfl) ⟨646331, by rfl⟩ : syracuseStep 3447101 = 1292663) B1292663
theorem B4299095 : Blo 670310 4299095 := bstep (se 1 (by rfl) ⟨3224321, by rfl⟩ : syracuseStep 4299095 = 6448643) B6448643
theorem B956767 : Blo 670310 956767 := bstep (se 1 (by rfl) ⟨717575, by rfl⟩ : syracuseStep 956767 = 1435151) B1435151
theorem B1513871 : Blo 670310 1513871 := bstep (se 1 (by rfl) ⟨1135403, by rfl⟩ : syracuseStep 1513871 = 2270807) B2270807
theorem B2267783 : Blo 670310 2267783 := bstep (se 1 (by rfl) ⟨1700837, by rfl⟩ : syracuseStep 2267783 = 3401675) B3401675
theorem B2267837 : Blo 670310 2267837 := bstep (se 3 (by rfl) ⟨425219, by rfl⟩ : syracuseStep 2267837 = 850439) B850439
theorem B1514195 : Blo 670310 1514195 := bstep (se 1 (by rfl) ⟨1135646, by rfl⟩ : syracuseStep 1514195 = 2271293) B2271293
theorem B2267999 : Blo 670310 2267999 := bstep (se 1 (by rfl) ⟨1700999, by rfl⟩ : syracuseStep 2267999 = 3401999) B3401999
theorem B1088399 : Blo 670310 1088399 := bstep (se 1 (by rfl) ⟨816299, by rfl⟩ : syracuseStep 1088399 = 1632599) B1632599
theorem B4856759 : Blo 670310 4856759 := bstep (se 1 (by rfl) ⟨3642569, by rfl⟩ : syracuseStep 4856759 = 7285139) B7285139
theorem B2759681 : Blo 670310 2759681 := bstep (se 2 (by rfl) ⟨1034880, by rfl⟩ : syracuseStep 2759681 = 2069761) B2069761
theorem B2268161 : Blo 670310 2268161 := bstep (se 2 (by rfl) ⟨850560, by rfl⟩ : syracuseStep 2268161 = 1701121) B1701121
theorem B5184665 : Blo 670310 5184665 := bstep (se 2 (by rfl) ⟨1944249, by rfl⟩ : syracuseStep 5184665 = 3888499) B3888499
theorem B4300121 : Blo 670310 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B9706877 : Blo 670310 9706877 := bstep (se 3 (by rfl) ⟨1820039, by rfl⟩ : syracuseStep 9706877 = 3640079) B3640079
theorem B3644837 : Blo 670310 3644837 := bstep (se 4 (by rfl) ⟨341703, by rfl⟩ : syracuseStep 3644837 = 683407) B683407
theorem B7249495 : Blo 670310 7249495 := bstep (se 1 (by rfl) ⟨5437121, by rfl⟩ : syracuseStep 7249495 = 10874243) B10874243
theorem B1515131 : Blo 670310 1515131 := bstep (se 1 (by rfl) ⟨1136348, by rfl⟩ : syracuseStep 1515131 = 2272697) B2272697
theorem B4857533 : Blo 670310 4857533 := bstep (se 3 (by rfl) ⟨910787, by rfl⟩ : syracuseStep 4857533 = 1821575) B1821575
theorem B1515257 : Blo 670310 1515257 := bstep (se 2 (by rfl) ⟨568221, by rfl⟩ : syracuseStep 1515257 = 1136443) B1136443
theorem B59121413 : Blo 670310 59121413 := bstep (se 4 (by rfl) ⟨5542632, by rfl⟩ : syracuseStep 59121413 = 11085265) B11085265
theorem B2268971 : Blo 670310 2268971 := bstep (se 1 (by rfl) ⟨1701728, by rfl⟩ : syracuseStep 2268971 = 3403457) B3403457
theorem B6889283 : Blo 670310 6889283 := bstep (se 1 (by rfl) ⟨5166962, by rfl⟩ : syracuseStep 6889283 = 10333925) B10333925
theorem B5447533 : Blo 670310 5447533 := bstep (se 3 (by rfl) ⟨1021412, by rfl⟩ : syracuseStep 5447533 = 2042825) B2042825
theorem B1515527 : Blo 670310 1515527 := bstep (se 1 (by rfl) ⟨1136645, by rfl⟩ : syracuseStep 1515527 = 2273291) B2273291
theorem B2269241 : Blo 670310 2269241 := bstep (se 2 (by rfl) ⟨850965, by rfl⟩ : syracuseStep 2269241 = 1701931) B1701931
theorem B1941583 : Blo 670310 1941583 := bstep (se 1 (by rfl) ⟨1456187, by rfl⟩ : syracuseStep 1941583 = 2912375) B2912375
theorem B1515599 : Blo 670310 1515599 := bstep (se 1 (by rfl) ⟨1136699, by rfl⟩ : syracuseStep 1515599 = 2273399) B2273399
theorem B4431953 : Blo 670310 4431953 := bstep (se 2 (by rfl) ⟨1661982, by rfl⟩ : syracuseStep 4431953 = 3323965) B3323965
theorem B5448023 : Blo 670310 5448023 := bstep (se 1 (by rfl) ⟨4086017, by rfl⟩ : syracuseStep 5448023 = 8172035) B8172035
theorem B2269565 : Blo 670310 2269565 := bstep (se 3 (by rfl) ⟨425543, by rfl⟩ : syracuseStep 2269565 = 851087) B851087
theorem B1515995 : Blo 670310 1515995 := bstep (se 1 (by rfl) ⟨1136996, by rfl⟩ : syracuseStep 1515995 = 2273993) B2273993
theorem B2269835 : Blo 670310 2269835 := bstep (se 1 (by rfl) ⟨1702376, by rfl⟩ : syracuseStep 2269835 = 3404753) B3404753
theorem B1516463 : Blo 670310 1516463 := bstep (se 1 (by rfl) ⟨1137347, by rfl⟩ : syracuseStep 1516463 = 2274695) B2274695
theorem B1516715 : Blo 670310 1516715 := bstep (se 1 (by rfl) ⟨1137536, by rfl⟩ : syracuseStep 1516715 = 2275073) B2275073
theorem B33137869 : Blo 670310 33137869 := bstep (se 3 (by rfl) ⟨6213350, by rfl⟩ : syracuseStep 33137869 = 12426701) B12426701
theorem B4302071 : Blo 670310 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B4597211 : Blo 670310 4597211 := bstep (se 1 (by rfl) ⟨3447908, by rfl⟩ : syracuseStep 4597211 = 6895817) B6895817
theorem B4597235 : Blo 670310 4597235 := bstep (se 1 (by rfl) ⟨3447926, by rfl⟩ : syracuseStep 4597235 = 6895853) B6895853
theorem B2270753 : Blo 670310 2270753 := bstep (se 2 (by rfl) ⟨851532, by rfl⟩ : syracuseStep 2270753 = 1703065) B1703065
theorem B2270969 : Blo 670310 2270969 := bstep (se 2 (by rfl) ⟨851613, by rfl⟩ : syracuseStep 2270969 = 1703227) B1703227
theorem B2729771 : Blo 670310 2729771 := bstep (se 1 (by rfl) ⟨2047328, by rfl⟩ : syracuseStep 2729771 = 4094657) B4094657
theorem B2729801 : Blo 670310 2729801 := bstep (se 2 (by rfl) ⟨1023675, by rfl⟩ : syracuseStep 2729801 = 2047351) B2047351
theorem B1812385 : Blo 670310 1812385 := bstep (se 2 (by rfl) ⟨679644, by rfl⟩ : syracuseStep 1812385 = 1359289) B1359289
theorem B1451963 : Blo 670310 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B3221441 : Blo 670310 3221441 := bstep (se 2 (by rfl) ⟨1208040, by rfl⟩ : syracuseStep 3221441 = 2416081) B2416081
theorem B2271239 : Blo 670310 2271239 := bstep (se 1 (by rfl) ⟨1703429, by rfl⟩ : syracuseStep 2271239 = 3406859) B3406859
theorem B2271347 : Blo 670310 2271347 := bstep (se 1 (by rfl) ⟨1703510, by rfl⟩ : syracuseStep 2271347 = 3407021) B3407021
theorem B2271617 : Blo 670310 2271617 := bstep (se 2 (by rfl) ⟨851856, by rfl⟩ : syracuseStep 2271617 = 1703713) B1703713
theorem B2272427 : Blo 670310 2272427 := bstep (se 1 (by rfl) ⟨1704320, by rfl⟩ : syracuseStep 2272427 = 3408641) B3408641
theorem B2731553 : Blo 670310 2731553 := bstep (se 2 (by rfl) ⟨1024332, by rfl⟩ : syracuseStep 2731553 = 2048665) B2048665
theorem B2272967 : Blo 670310 2272967 := bstep (se 1 (by rfl) ⟨1704725, by rfl⟩ : syracuseStep 2272967 = 3409451) B3409451
theorem B4304735 : Blo 670310 4304735 := bstep (se 1 (by rfl) ⟨3228551, by rfl⟩ : syracuseStep 4304735 = 6457103) B6457103
theorem B2994029 : Blo 670310 2994029 := bstep (se 3 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 2994029 = 1122761) B1122761
theorem B5091335 : Blo 670310 5091335 := bstep (se 1 (by rfl) ⟨3818501, by rfl⟩ : syracuseStep 5091335 = 7637003) B7637003
theorem B5091821 : Blo 670310 5091821 := bstep (se 3 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 5091821 = 1909433) B1909433
theorem B2273831 : Blo 670310 2273831 := bstep (se 1 (by rfl) ⟨1705373, by rfl⟩ : syracuseStep 2273831 = 3410747) B3410747
theorem B2273939 : Blo 670310 2273939 := bstep (se 1 (by rfl) ⟨1705454, by rfl⟩ : syracuseStep 2273939 = 3410909) B3410909
theorem B8630995 : Blo 670310 8630995 := bstep (se 1 (by rfl) ⟨6473246, by rfl⟩ : syracuseStep 8630995 = 12946493) B12946493
theorem B2274155 : Blo 670310 2274155 := bstep (se 1 (by rfl) ⟨1705616, by rfl⟩ : syracuseStep 2274155 = 3411233) B3411233
theorem B2274209 : Blo 670310 2274209 := bstep (se 2 (by rfl) ⟨852828, by rfl⟩ : syracuseStep 2274209 = 1705657) B1705657
theorem B2274803 : Blo 670310 2274803 := bstep (se 1 (by rfl) ⟨1706102, by rfl⟩ : syracuseStep 2274803 = 3412205) B3412205
theorem B1914491 : Blo 670310 1914491 := bstep (se 1 (by rfl) ⟨1435868, by rfl⟩ : syracuseStep 1914491 = 2871737) B2871737
theorem B2176723 : Blo 670310 2176723 := bstep (se 1 (by rfl) ⟨1632542, by rfl⟩ : syracuseStep 2176723 = 3265085) B3265085
theorem B1914617 : Blo 670310 1914617 := bstep (se 2 (by rfl) ⟨717981, by rfl⟩ : syracuseStep 1914617 = 1435963) B1435963
theorem B1914799 : Blo 670310 1914799 := bstep (se 1 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 1914799 = 2872199) B2872199
theorem B2275343 : Blo 670310 2275343 := bstep (se 1 (by rfl) ⟨1706507, by rfl⟩ : syracuseStep 2275343 = 3413015) B3413015
theorem B3225689 : Blo 670310 3225689 := bstep (se 2 (by rfl) ⟨1209633, by rfl⟩ : syracuseStep 3225689 = 2419267) B2419267
theorem B1915265 : Blo 670310 1915265 := bstep (se 2 (by rfl) ⟨718224, by rfl⟩ : syracuseStep 1915265 = 1436449) B1436449
theorem B5093765 : Blo 670310 5093765 := bstep (se 4 (by rfl) ⟨477540, by rfl⟩ : syracuseStep 5093765 = 955081) B955081
theorem B2865689 : Blo 670310 2865689 := bstep (se 2 (by rfl) ⟨1074633, by rfl⟩ : syracuseStep 2865689 = 2149267) B2149267
theorem B670331 : Blo 670310 670331 := bstep (se 1 (by rfl) ⟨502748, by rfl⟩ : syracuseStep 670331 = 1005497) B1005497
theorem B670383 : Blo 670310 670383 := bstep (se 1 (by rfl) ⟨502787, by rfl⟩ : syracuseStep 670383 = 1005575) B1005575
theorem B670407 : Blo 670310 670407 := bstep (se 1 (by rfl) ⟨502805, by rfl⟩ : syracuseStep 670407 = 1005611) B1005611
theorem B3226321 : Blo 670310 3226321 := bstep (se 2 (by rfl) ⟨1209870, by rfl⟩ : syracuseStep 3226321 = 2419741) B2419741
theorem B670427 : Blo 670310 670427 := bstep (se 1 (by rfl) ⟨502820, by rfl⟩ : syracuseStep 670427 = 1005641) B1005641
theorem B670503 : Blo 670310 670503 := bstep (se 1 (by rfl) ⟨502877, by rfl⟩ : syracuseStep 670503 = 1005755) B1005755
theorem B1915721 : Blo 670310 1915721 := bstep (se 2 (by rfl) ⟨718395, by rfl⟩ : syracuseStep 1915721 = 1436791) B1436791
theorem B7650125 : Blo 670310 7650125 := bstep (se 3 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 7650125 = 2868797) B2868797
theorem B670543 : Blo 670310 670543 := bstep (se 1 (by rfl) ⟨502907, by rfl⟩ : syracuseStep 670543 = 1005815) B1005815
theorem B670559 : Blo 670310 670559 := bstep (se 1 (by rfl) ⟨502919, by rfl⟩ : syracuseStep 670559 = 1005839) B1005839
theorem B5094251 : Blo 670310 5094251 := bstep (se 1 (by rfl) ⟨3820688, by rfl⟩ : syracuseStep 5094251 = 7641377) B7641377
theorem B3226475 : Blo 670310 3226475 := bstep (se 1 (by rfl) ⟨2419856, by rfl⟩ : syracuseStep 3226475 = 4839713) B4839713
theorem B52312949 : Blo 670310 52312949 := bstep (se 5 (by rfl) ⟨2452169, by rfl⟩ : syracuseStep 52312949 = 4904339) B4904339
theorem B670587 : Blo 670310 670587 := bstep (se 1 (by rfl) ⟨502940, by rfl⟩ : syracuseStep 670587 = 1005881) B1005881
theorem B670639 : Blo 670310 670639 := bstep (se 1 (by rfl) ⟨502979, by rfl⟩ : syracuseStep 670639 = 1005959) B1005959
theorem B670663 : Blo 670310 670663 := bstep (se 1 (by rfl) ⟨502997, by rfl⟩ : syracuseStep 670663 = 1005995) B1005995
theorem B670683 : Blo 670310 670683 := bstep (se 1 (by rfl) ⟨503012, by rfl⟩ : syracuseStep 670683 = 1006025) B1006025
theorem B670759 : Blo 670310 670759 := bstep (se 1 (by rfl) ⟨503069, by rfl⟩ : syracuseStep 670759 = 1006139) B1006139
theorem B670799 : Blo 670310 670799 := bstep (se 1 (by rfl) ⟨503099, by rfl⟩ : syracuseStep 670799 = 1006199) B1006199
theorem B670815 : Blo 670310 670815 := bstep (se 1 (by rfl) ⟨503111, by rfl⟩ : syracuseStep 670815 = 1006223) B1006223
theorem B670843 : Blo 670310 670843 := bstep (se 1 (by rfl) ⟨503132, by rfl⟩ : syracuseStep 670843 = 1006265) B1006265
theorem B1916075 : Blo 670310 1916075 := bstep (se 1 (by rfl) ⟨1437056, by rfl⟩ : syracuseStep 1916075 = 2874113) B2874113
theorem B670895 : Blo 670310 670895 := bstep (se 1 (by rfl) ⟨503171, by rfl⟩ : syracuseStep 670895 = 1006343) B1006343
theorem B670919 : Blo 670310 670919 := bstep (se 1 (by rfl) ⟨503189, by rfl⟩ : syracuseStep 670919 = 1006379) B1006379
theorem B670939 : Blo 670310 670939 := bstep (se 1 (by rfl) ⟨503204, by rfl⟩ : syracuseStep 670939 = 1006409) B1006409
theorem B671015 : Blo 670310 671015 := bstep (se 1 (by rfl) ⟨503261, by rfl⟩ : syracuseStep 671015 = 1006523) B1006523
theorem B671055 : Blo 670310 671055 := bstep (se 1 (by rfl) ⟨503291, by rfl⟩ : syracuseStep 671055 = 1006583) B1006583
theorem B671071 : Blo 670310 671071 := bstep (se 1 (by rfl) ⟨503303, by rfl⟩ : syracuseStep 671071 = 1006607) B1006607
theorem B671099 : Blo 670310 671099 := bstep (se 1 (by rfl) ⟨503324, by rfl⟩ : syracuseStep 671099 = 1006649) B1006649
theorem B671151 : Blo 670310 671151 := bstep (se 1 (by rfl) ⟨503363, by rfl⟩ : syracuseStep 671151 = 1006727) B1006727
theorem B671175 : Blo 670310 671175 := bstep (se 1 (by rfl) ⟨503381, by rfl⟩ : syracuseStep 671175 = 1006763) B1006763
theorem B671195 : Blo 670310 671195 := bstep (se 1 (by rfl) ⟨503396, by rfl⟩ : syracuseStep 671195 = 1006793) B1006793
theorem B671271 : Blo 670310 671271 := bstep (se 1 (by rfl) ⟨503453, by rfl⟩ : syracuseStep 671271 = 1006907) B1006907
theorem B671311 : Blo 670310 671311 := bstep (se 1 (by rfl) ⟨503483, by rfl⟩ : syracuseStep 671311 = 1006967) B1006967
theorem B671327 : Blo 670310 671327 := bstep (se 1 (by rfl) ⟨503495, by rfl⟩ : syracuseStep 671327 = 1006991) B1006991
theorem B671355 : Blo 670310 671355 := bstep (se 1 (by rfl) ⟨503516, by rfl⟩ : syracuseStep 671355 = 1007033) B1007033
theorem B671407 : Blo 670310 671407 := bstep (se 1 (by rfl) ⟨503555, by rfl⟩ : syracuseStep 671407 = 1007111) B1007111
theorem B671431 : Blo 670310 671431 := bstep (se 1 (by rfl) ⟨503573, by rfl⟩ : syracuseStep 671431 = 1007147) B1007147
theorem B671451 : Blo 670310 671451 := bstep (se 1 (by rfl) ⟨503588, by rfl⟩ : syracuseStep 671451 = 1007177) B1007177
theorem B671527 : Blo 670310 671527 := bstep (se 1 (by rfl) ⟨503645, by rfl⟩ : syracuseStep 671527 = 1007291) B1007291
theorem B671567 : Blo 670310 671567 := bstep (se 1 (by rfl) ⟨503675, by rfl⟩ : syracuseStep 671567 = 1007351) B1007351
theorem B671583 : Blo 670310 671583 := bstep (se 1 (by rfl) ⟨503687, by rfl⟩ : syracuseStep 671583 = 1007375) B1007375
theorem B671611 : Blo 670310 671611 := bstep (se 1 (by rfl) ⟨503708, by rfl⟩ : syracuseStep 671611 = 1007417) B1007417
theorem B671663 : Blo 670310 671663 := bstep (se 1 (by rfl) ⟨503747, by rfl⟩ : syracuseStep 671663 = 1007495) B1007495
theorem B671687 : Blo 670310 671687 := bstep (se 1 (by rfl) ⟨503765, by rfl⟩ : syracuseStep 671687 = 1007531) B1007531
theorem B671707 : Blo 670310 671707 := bstep (se 1 (by rfl) ⟨503780, by rfl⟩ : syracuseStep 671707 = 1007561) B1007561
theorem B671783 : Blo 670310 671783 := bstep (se 1 (by rfl) ⟨503837, by rfl⟩ : syracuseStep 671783 = 1007675) B1007675
theorem B3227705 : Blo 670310 3227705 := bstep (se 2 (by rfl) ⟨1210389, by rfl⟩ : syracuseStep 3227705 = 2420779) B2420779
theorem B671823 : Blo 670310 671823 := bstep (se 1 (by rfl) ⟨503867, by rfl⟩ : syracuseStep 671823 = 1007735) B1007735
theorem B671839 : Blo 670310 671839 := bstep (se 1 (by rfl) ⟨503879, by rfl⟩ : syracuseStep 671839 = 1007759) B1007759
theorem B671867 : Blo 670310 671867 := bstep (se 1 (by rfl) ⟨503900, by rfl⟩ : syracuseStep 671867 = 1007801) B1007801
theorem B671919 : Blo 670310 671919 := bstep (se 1 (by rfl) ⟨503939, by rfl⟩ : syracuseStep 671919 = 1007879) B1007879
theorem B671943 : Blo 670310 671943 := bstep (se 1 (by rfl) ⟨503957, by rfl⟩ : syracuseStep 671943 = 1007915) B1007915
theorem B671963 : Blo 670310 671963 := bstep (se 1 (by rfl) ⟨503972, by rfl⟩ : syracuseStep 671963 = 1007945) B1007945
theorem B672039 : Blo 670310 672039 := bstep (se 1 (by rfl) ⟨504029, by rfl⟩ : syracuseStep 672039 = 1008059) B1008059
theorem B672079 : Blo 670310 672079 := bstep (se 1 (by rfl) ⟨504059, by rfl⟩ : syracuseStep 672079 = 1008119) B1008119
theorem B672095 : Blo 670310 672095 := bstep (se 1 (by rfl) ⟨504071, by rfl⟩ : syracuseStep 672095 = 1008143) B1008143
theorem B672123 : Blo 670310 672123 := bstep (se 1 (by rfl) ⟨504092, by rfl⟩ : syracuseStep 672123 = 1008185) B1008185
theorem B2048399 : Blo 670310 2048399 := bstep (se 1 (by rfl) ⟨1536299, by rfl⟩ : syracuseStep 2048399 = 3072599) B3072599
theorem B672175 : Blo 670310 672175 := bstep (se 1 (by rfl) ⟨504131, by rfl⟩ : syracuseStep 672175 = 1008263) B1008263
theorem B672199 : Blo 670310 672199 := bstep (se 1 (by rfl) ⟨504149, by rfl⟩ : syracuseStep 672199 = 1008299) B1008299
theorem B672219 : Blo 670310 672219 := bstep (se 1 (by rfl) ⟨504164, by rfl⟩ : syracuseStep 672219 = 1008329) B1008329
theorem B672295 : Blo 670310 672295 := bstep (se 1 (by rfl) ⟨504221, by rfl⟩ : syracuseStep 672295 = 1008443) B1008443
theorem B672335 : Blo 670310 672335 := bstep (se 1 (by rfl) ⟨504251, by rfl⟩ : syracuseStep 672335 = 1008503) B1008503
theorem B672351 : Blo 670310 672351 := bstep (se 1 (by rfl) ⟨504263, by rfl⟩ : syracuseStep 672351 = 1008527) B1008527
theorem B672379 : Blo 670310 672379 := bstep (se 1 (by rfl) ⟨504284, by rfl⟩ : syracuseStep 672379 = 1008569) B1008569
theorem B672431 : Blo 670310 672431 := bstep (se 1 (by rfl) ⟨504323, by rfl⟩ : syracuseStep 672431 = 1008647) B1008647
theorem B672455 : Blo 670310 672455 := bstep (se 1 (by rfl) ⟨504341, by rfl⟩ : syracuseStep 672455 = 1008683) B1008683
theorem B672475 : Blo 670310 672475 := bstep (se 1 (by rfl) ⟨504356, by rfl⟩ : syracuseStep 672475 = 1008713) B1008713
theorem B5096195 : Blo 670310 5096195 := bstep (se 1 (by rfl) ⟨3822146, by rfl⟩ : syracuseStep 5096195 = 7644293) B7644293
theorem B672551 : Blo 670310 672551 := bstep (se 1 (by rfl) ⟨504413, by rfl⟩ : syracuseStep 672551 = 1008827) B1008827
theorem B672591 : Blo 670310 672591 := bstep (se 1 (by rfl) ⟨504443, by rfl⟩ : syracuseStep 672591 = 1008887) B1008887
theorem B672607 : Blo 670310 672607 := bstep (se 1 (by rfl) ⟨504455, by rfl⟩ : syracuseStep 672607 = 1008911) B1008911
theorem B672635 : Blo 670310 672635 := bstep (se 1 (by rfl) ⟨504476, by rfl⟩ : syracuseStep 672635 = 1008953) B1008953
theorem B672687 : Blo 670310 672687 := bstep (se 1 (by rfl) ⟨504515, by rfl⟩ : syracuseStep 672687 = 1009031) B1009031
theorem B672711 : Blo 670310 672711 := bstep (se 1 (by rfl) ⟨504533, by rfl⟩ : syracuseStep 672711 = 1009067) B1009067
theorem B672731 : Blo 670310 672731 := bstep (se 1 (by rfl) ⟨504548, by rfl⟩ : syracuseStep 672731 = 1009097) B1009097
theorem B1131529 : Blo 670310 1131529 := bstep (se 2 (by rfl) ⟨424323, by rfl⟩ : syracuseStep 1131529 = 848647) B848647
theorem B672807 : Blo 670310 672807 := bstep (se 1 (by rfl) ⟨504605, by rfl⟩ : syracuseStep 672807 = 1009211) B1009211
theorem B672847 : Blo 670310 672847 := bstep (se 1 (by rfl) ⟨504635, by rfl⟩ : syracuseStep 672847 = 1009271) B1009271
theorem B672863 : Blo 670310 672863 := bstep (se 1 (by rfl) ⟨504647, by rfl⟩ : syracuseStep 672863 = 1009295) B1009295
theorem B672891 : Blo 670310 672891 := bstep (se 1 (by rfl) ⟨504668, by rfl⟩ : syracuseStep 672891 = 1009337) B1009337
theorem B1131691 : Blo 670310 1131691 := bstep (se 1 (by rfl) ⟨848768, by rfl⟩ : syracuseStep 1131691 = 1697537) B1697537
theorem B672943 : Blo 670310 672943 := bstep (se 1 (by rfl) ⟨504707, by rfl⟩ : syracuseStep 672943 = 1009415) B1009415
theorem B672967 : Blo 670310 672967 := bstep (se 1 (by rfl) ⟨504725, by rfl⟩ : syracuseStep 672967 = 1009451) B1009451
theorem B672987 : Blo 670310 672987 := bstep (se 1 (by rfl) ⟨504740, by rfl⟩ : syracuseStep 672987 = 1009481) B1009481
theorem B673063 : Blo 670310 673063 := bstep (se 1 (by rfl) ⟨504797, by rfl⟩ : syracuseStep 673063 = 1009595) B1009595
theorem B673103 : Blo 670310 673103 := bstep (se 1 (by rfl) ⟨504827, by rfl⟩ : syracuseStep 673103 = 1009655) B1009655
theorem B673119 : Blo 670310 673119 := bstep (se 1 (by rfl) ⟨504839, by rfl⟩ : syracuseStep 673119 = 1009679) B1009679
theorem B673147 : Blo 670310 673147 := bstep (se 1 (by rfl) ⟨504860, by rfl⟩ : syracuseStep 673147 = 1009721) B1009721
theorem B3458477 : Blo 670310 3458477 := bstep (se 3 (by rfl) ⟨648464, by rfl⟩ : syracuseStep 3458477 = 1296929) B1296929
theorem B673199 : Blo 670310 673199 := bstep (se 1 (by rfl) ⟨504899, by rfl⟩ : syracuseStep 673199 = 1009799) B1009799
theorem B673223 : Blo 670310 673223 := bstep (se 1 (by rfl) ⟨504917, by rfl⟩ : syracuseStep 673223 = 1009835) B1009835
theorem B1131995 : Blo 670310 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B673243 : Blo 670310 673243 := bstep (se 1 (by rfl) ⟨504932, by rfl⟩ : syracuseStep 673243 = 1009865) B1009865
theorem B673319 : Blo 670310 673319 := bstep (se 1 (by rfl) ⟨504989, by rfl⟩ : syracuseStep 673319 = 1009979) B1009979
theorem B13780523 : Blo 670310 13780523 := bstep (se 1 (by rfl) ⟨10335392, by rfl⟩ : syracuseStep 13780523 = 20670785) B20670785
theorem B1295929 : Blo 670310 1295929 := bstep (se 2 (by rfl) ⟨485973, by rfl⟩ : syracuseStep 1295929 = 971947) B971947
theorem B673359 : Blo 670310 673359 := bstep (se 1 (by rfl) ⟨505019, by rfl⟩ : syracuseStep 673359 = 1010039) B1010039
theorem B673375 : Blo 670310 673375 := bstep (se 1 (by rfl) ⟨505031, by rfl⟩ : syracuseStep 673375 = 1010063) B1010063
theorem B673403 : Blo 670310 673403 := bstep (se 1 (by rfl) ⟨505052, by rfl⟩ : syracuseStep 673403 = 1010105) B1010105
theorem B673455 : Blo 670310 673455 := bstep (se 1 (by rfl) ⟨505091, by rfl⟩ : syracuseStep 673455 = 1010183) B1010183
theorem B2049725 : Blo 670310 2049725 := bstep (se 3 (by rfl) ⟨384323, by rfl⟩ : syracuseStep 2049725 = 768647) B768647
theorem B1132231 : Blo 670310 1132231 := bstep (se 1 (by rfl) ⟨849173, by rfl⟩ : syracuseStep 1132231 = 1698347) B1698347
theorem B673479 : Blo 670310 673479 := bstep (se 1 (by rfl) ⟨505109, by rfl⟩ : syracuseStep 673479 = 1010219) B1010219
theorem B8308439 : Blo 670310 8308439 := bstep (se 1 (by rfl) ⟨6231329, by rfl⟩ : syracuseStep 8308439 = 12462659) B12462659
theorem B673499 : Blo 670310 673499 := bstep (se 1 (by rfl) ⟨505124, by rfl⟩ : syracuseStep 673499 = 1010249) B1010249
theorem B4900601 : Blo 670310 4900601 := bstep (se 2 (by rfl) ⟨1837725, by rfl⟩ : syracuseStep 4900601 = 3675451) B3675451
theorem B673575 : Blo 670310 673575 := bstep (se 1 (by rfl) ⟨505181, by rfl⟩ : syracuseStep 673575 = 1010363) B1010363
theorem B673615 : Blo 670310 673615 := bstep (se 1 (by rfl) ⟨505211, by rfl⟩ : syracuseStep 673615 = 1010423) B1010423
theorem B673631 : Blo 670310 673631 := bstep (se 1 (by rfl) ⟨505223, by rfl⟩ : syracuseStep 673631 = 1010447) B1010447
theorem B1132393 : Blo 670310 1132393 := bstep (se 2 (by rfl) ⟨424647, by rfl⟩ : syracuseStep 1132393 = 849295) B849295
theorem B673659 : Blo 670310 673659 := bstep (se 1 (by rfl) ⟨505244, by rfl⟩ : syracuseStep 673659 = 1010489) B1010489
theorem B673711 : Blo 670310 673711 := bstep (se 1 (by rfl) ⟨505283, by rfl⟩ : syracuseStep 673711 = 1010567) B1010567
theorem B673735 : Blo 670310 673735 := bstep (se 1 (by rfl) ⟨505301, by rfl⟩ : syracuseStep 673735 = 1010603) B1010603
theorem B673755 : Blo 670310 673755 := bstep (se 1 (by rfl) ⟨505316, by rfl⟩ : syracuseStep 673755 = 1010633) B1010633
theorem B4605989 : Blo 670310 4605989 := bstep (se 4 (by rfl) ⟨431811, by rfl⟩ : syracuseStep 4605989 = 863623) B863623
theorem B673831 : Blo 670310 673831 := bstep (se 1 (by rfl) ⟨505373, by rfl⟩ : syracuseStep 673831 = 1010747) B1010747
theorem B673871 : Blo 670310 673871 := bstep (se 1 (by rfl) ⟨505403, by rfl⟩ : syracuseStep 673871 = 1010807) B1010807
theorem B673887 : Blo 670310 673887 := bstep (se 1 (by rfl) ⟨505415, by rfl⟩ : syracuseStep 673887 = 1010831) B1010831
theorem B673915 : Blo 670310 673915 := bstep (se 1 (by rfl) ⟨505436, by rfl⟩ : syracuseStep 673915 = 1010873) B1010873
theorem B673967 : Blo 670310 673967 := bstep (se 1 (by rfl) ⟨505475, by rfl⟩ : syracuseStep 673967 = 1010951) B1010951
theorem B673991 : Blo 670310 673991 := bstep (se 1 (by rfl) ⟨505493, by rfl⟩ : syracuseStep 673991 = 1010987) B1010987
theorem B674011 : Blo 670310 674011 := bstep (se 1 (by rfl) ⟨505508, by rfl⟩ : syracuseStep 674011 = 1011017) B1011017
theorem B674087 : Blo 670310 674087 := bstep (se 1 (by rfl) ⟨505565, by rfl⟩ : syracuseStep 674087 = 1011131) B1011131
theorem B674127 : Blo 670310 674127 := bstep (se 1 (by rfl) ⟨505595, by rfl⟩ : syracuseStep 674127 = 1011191) B1011191
theorem B674143 : Blo 670310 674143 := bstep (se 1 (by rfl) ⟨505607, by rfl⟩ : syracuseStep 674143 = 1011215) B1011215
theorem B674171 : Blo 670310 674171 := bstep (se 1 (by rfl) ⟨505628, by rfl⟩ : syracuseStep 674171 = 1011257) B1011257
theorem B674223 : Blo 670310 674223 := bstep (se 1 (by rfl) ⟨505667, by rfl⟩ : syracuseStep 674223 = 1011335) B1011335
theorem B1132987 : Blo 670310 1132987 := bstep (se 1 (by rfl) ⟨849740, by rfl⟩ : syracuseStep 1132987 = 1699481) B1699481
theorem B674247 : Blo 670310 674247 := bstep (se 1 (by rfl) ⟨505685, by rfl⟩ : syracuseStep 674247 = 1011371) B1011371
theorem B1362395 : Blo 670310 1362395 := bstep (se 1 (by rfl) ⟨1021796, by rfl⟩ : syracuseStep 1362395 = 2043593) B2043593
theorem B674267 : Blo 670310 674267 := bstep (se 1 (by rfl) ⟨505700, by rfl⟩ : syracuseStep 674267 = 1011401) B1011401
theorem B1133095 : Blo 670310 1133095 := bstep (se 1 (by rfl) ⟨849821, by rfl⟩ : syracuseStep 1133095 = 1699643) B1699643
theorem B2214611 : Blo 670310 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B336579299 : Blo 670310 336579299 := bstep (se 1 (by rfl) ⟨252434474, by rfl⟩ : syracuseStep 336579299 = 504868949) B504868949
theorem B5458691 : Blo 670310 5458691 := bstep (se 1 (by rfl) ⟨4094018, by rfl⟩ : syracuseStep 5458691 = 8188037) B8188037
theorem B1133419 : Blo 670310 1133419 := bstep (se 1 (by rfl) ⟨850064, by rfl⟩ : syracuseStep 1133419 = 1700129) B1700129
theorem B805807 : Blo 670310 805807 := bstep (se 1 (by rfl) ⟨604355, by rfl⟩ : syracuseStep 805807 = 1208711) B1208711
theorem B8604751 : Blo 670310 8604751 := bstep (se 1 (by rfl) ⟨6453563, by rfl⟩ : syracuseStep 8604751 = 12907127) B12907127
theorem B4312217 : Blo 670310 4312217 := bstep (se 2 (by rfl) ⟨1617081, by rfl⟩ : syracuseStep 4312217 = 3234163) B3234163
theorem B18599203 : Blo 670310 18599203 := bstep (se 1 (by rfl) ⟨13949402, by rfl⟩ : syracuseStep 18599203 = 27898805) B27898805
theorem B1363375 : Blo 670310 1363375 := bstep (se 1 (by rfl) ⟨1022531, by rfl⟩ : syracuseStep 1363375 = 2045063) B2045063
theorem B2870747 : Blo 670310 2870747 := bstep (se 1 (by rfl) ⟨2153060, by rfl⟩ : syracuseStep 2870747 = 4306121) B4306121
theorem B3395195 : Blo 670310 3395195 := bstep (se 1 (by rfl) ⟨2546396, by rfl⟩ : syracuseStep 3395195 = 5092793) B5092793
theorem B1134479 : Blo 670310 1134479 := bstep (se 1 (by rfl) ⟨850859, by rfl⟩ : syracuseStep 1134479 = 1701719) B1701719
theorem B5099597 : Blo 670310 5099597 := bstep (se 3 (by rfl) ⟨956174, by rfl⟩ : syracuseStep 5099597 = 1912349) B1912349
theorem B1134715 : Blo 670310 1134715 := bstep (se 1 (by rfl) ⟨851036, by rfl⟩ : syracuseStep 1134715 = 1702073) B1702073
theorem B807503 : Blo 670310 807503 := bstep (se 1 (by rfl) ⟨605627, by rfl⟩ : syracuseStep 807503 = 1211255) B1211255
theorem B3822511 : Blo 670310 3822511 := bstep (se 1 (by rfl) ⟨2866883, by rfl⟩ : syracuseStep 3822511 = 5733767) B5733767
theorem B1135579 : Blo 670310 1135579 := bstep (se 1 (by rfl) ⟨851684, by rfl⟩ : syracuseStep 1135579 = 1703369) B1703369
theorem B971899 : Blo 670310 971899 := bstep (se 1 (by rfl) ⟨728924, by rfl⟩ : syracuseStep 971899 = 1457849) B1457849
theorem B1136207 : Blo 670310 1136207 := bstep (se 1 (by rfl) ⟨852155, by rfl⟩ : syracuseStep 1136207 = 1704311) B1704311
theorem B4085437 : Blo 670310 4085437 := bstep (se 3 (by rfl) ⟨766019, by rfl⟩ : syracuseStep 4085437 = 1532039) B1532039
theorem B3823469 : Blo 670310 3823469 := bstep (se 3 (by rfl) ⟨716900, by rfl⟩ : syracuseStep 3823469 = 1433801) B1433801
theorem B4315193 : Blo 670310 4315193 := bstep (se 2 (by rfl) ⟨1618197, by rfl⟩ : syracuseStep 4315193 = 3236395) B3236395
theorem B1431631 : Blo 670310 1431631 := bstep (se 1 (by rfl) ⟨1073723, by rfl⟩ : syracuseStep 1431631 = 2147447) B2147447
theorem B1005647 : Blo 670310 1005647 := bstep (se 1 (by rfl) ⟨754235, by rfl⟩ : syracuseStep 1005647 = 1508471) B1508471
theorem B1005767 : Blo 670310 1005767 := bstep (se 1 (by rfl) ⟨754325, by rfl⟩ : syracuseStep 1005767 = 1508651) B1508651
theorem B3397949 : Blo 670310 3397949 := bstep (se 3 (by rfl) ⟨637115, by rfl⟩ : syracuseStep 3397949 = 1274231) B1274231
theorem B1005929 : Blo 670310 1005929 := bstep (se 2 (by rfl) ⟨377223, by rfl⟩ : syracuseStep 1005929 = 754447) B754447
theorem B2546063 : Blo 670310 2546063 := bstep (se 1 (by rfl) ⟨1909547, by rfl⟩ : syracuseStep 2546063 = 3819095) B3819095
theorem B1137071 : Blo 670310 1137071 := bstep (se 1 (by rfl) ⟨852803, by rfl⟩ : syracuseStep 1137071 = 1705607) B1705607
theorem B1006007 : Blo 670310 1006007 := bstep (se 1 (by rfl) ⟨754505, by rfl⟩ : syracuseStep 1006007 = 1509011) B1509011
theorem B5102027 : Blo 670310 5102027 := bstep (se 1 (by rfl) ⟨3826520, by rfl⟩ : syracuseStep 5102027 = 7653041) B7653041
theorem B1006043 : Blo 670310 1006043 := bstep (se 1 (by rfl) ⟨754532, by rfl⟩ : syracuseStep 1006043 = 1509065) B1509065
theorem B809551 : Blo 670310 809551 := bstep (se 1 (by rfl) ⟨607163, by rfl⟩ : syracuseStep 809551 = 1214327) B1214327
theorem B1137503 : Blo 670310 1137503 := bstep (se 1 (by rfl) ⟨853127, by rfl⟩ : syracuseStep 1137503 = 1706255) B1706255
theorem B1006511 : Blo 670310 1006511 := bstep (se 1 (by rfl) ⟨754883, by rfl⟩ : syracuseStep 1006511 = 1509767) B1509767
theorem B1006601 : Blo 670310 1006601 := bstep (se 2 (by rfl) ⟨377475, by rfl⟩ : syracuseStep 1006601 = 754951) B754951
theorem B1006631 : Blo 670310 1006631 := bstep (se 1 (by rfl) ⟨754973, by rfl⟩ : syracuseStep 1006631 = 1509947) B1509947
theorem B6151247 : Blo 670310 6151247 := bstep (se 1 (by rfl) ⟨4613435, by rfl⟩ : syracuseStep 6151247 = 9226871) B9226871
theorem B1006715 : Blo 670310 1006715 := bstep (se 1 (by rfl) ⟨755036, by rfl⟩ : syracuseStep 1006715 = 1510073) B1510073
theorem B1006841 : Blo 670310 1006841 := bstep (se 2 (by rfl) ⟨377565, by rfl⟩ : syracuseStep 1006841 = 755131) B755131
theorem B1006943 : Blo 670310 1006943 := bstep (se 1 (by rfl) ⟨755207, by rfl⟩ : syracuseStep 1006943 = 1510415) B1510415
theorem B1006955 : Blo 670310 1006955 := bstep (se 1 (by rfl) ⟨755216, by rfl⟩ : syracuseStep 1006955 = 1510433) B1510433
theorem B777691 : Blo 670310 777691 := bstep (se 1 (by rfl) ⟨583268, by rfl⟩ : syracuseStep 777691 = 1166537) B1166537
theorem B2547233 : Blo 670310 2547233 := bstep (se 2 (by rfl) ⟨955212, by rfl⟩ : syracuseStep 2547233 = 1910425) B1910425
theorem B1007183 : Blo 670310 1007183 := bstep (se 1 (by rfl) ⟨755387, by rfl⟩ : syracuseStep 1007183 = 1510775) B1510775
theorem B2416225 : Blo 670310 2416225 := bstep (se 2 (by rfl) ⟨906084, by rfl⟩ : syracuseStep 2416225 = 1812169) B1812169
theorem B679547 : Blo 670310 679547 := bstep (se 1 (by rfl) ⟨509660, by rfl⟩ : syracuseStep 679547 = 1019321) B1019321
theorem B1007303 : Blo 670310 1007303 := bstep (se 1 (by rfl) ⟨755477, by rfl⟩ : syracuseStep 1007303 = 1510955) B1510955
theorem B2416339 : Blo 670310 2416339 := bstep (se 1 (by rfl) ⟨1812254, by rfl⟩ : syracuseStep 2416339 = 3624509) B3624509
theorem B2547551 : Blo 670310 2547551 := bstep (se 1 (by rfl) ⟨1910663, by rfl⟩ : syracuseStep 2547551 = 3821327) B3821327
theorem B1007465 : Blo 670310 1007465 := bstep (se 2 (by rfl) ⟨377799, by rfl⟩ : syracuseStep 1007465 = 755599) B755599
theorem B1007543 : Blo 670310 1007543 := bstep (se 1 (by rfl) ⟨755657, by rfl⟩ : syracuseStep 1007543 = 1511315) B1511315
theorem B1007579 : Blo 670310 1007579 := bstep (se 1 (by rfl) ⟨755684, by rfl⟩ : syracuseStep 1007579 = 1511369) B1511369
theorem B2547719 : Blo 670310 2547719 := bstep (se 1 (by rfl) ⟨1910789, by rfl⟩ : syracuseStep 2547719 = 3821579) B3821579
theorem B3825701 : Blo 670310 3825701 := bstep (se 4 (by rfl) ⟨358659, by rfl⟩ : syracuseStep 3825701 = 717319) B717319
theorem B6447185 : Blo 670310 6447185 := bstep (se 2 (by rfl) ⟨2417694, by rfl⟩ : syracuseStep 6447185 = 4835389) B4835389
theorem B1008047 : Blo 670310 1008047 := bstep (se 1 (by rfl) ⟨756035, by rfl⟩ : syracuseStep 1008047 = 1512071) B1512071
theorem B2548205 : Blo 670310 2548205 := bstep (se 3 (by rfl) ⟨477788, by rfl⟩ : syracuseStep 2548205 = 955577) B955577
theorem B1008137 : Blo 670310 1008137 := bstep (se 2 (by rfl) ⟨378051, by rfl⟩ : syracuseStep 1008137 = 756103) B756103
theorem B3400217 : Blo 670310 3400217 := bstep (se 2 (by rfl) ⟨1275081, by rfl⟩ : syracuseStep 3400217 = 2550163) B2550163
theorem B1008167 : Blo 670310 1008167 := bstep (se 1 (by rfl) ⟨756125, by rfl⟩ : syracuseStep 1008167 = 1512251) B1512251
theorem B1008251 : Blo 670310 1008251 := bstep (se 1 (by rfl) ⟨756188, by rfl⟩ : syracuseStep 1008251 = 1512377) B1512377
theorem B3826385 : Blo 670310 3826385 := bstep (se 2 (by rfl) ⟨1434894, by rfl⟩ : syracuseStep 3826385 = 2869789) B2869789
theorem B1434323 : Blo 670310 1434323 := bstep (se 1 (by rfl) ⟨1075742, by rfl⟩ : syracuseStep 1434323 = 2151485) B2151485
theorem B1008377 : Blo 670310 1008377 := bstep (se 2 (by rfl) ⟨378141, by rfl⟩ : syracuseStep 1008377 = 756283) B756283
theorem B2548523 : Blo 670310 2548523 := bstep (se 1 (by rfl) ⟨1911392, by rfl⟩ : syracuseStep 2548523 = 3822785) B3822785
theorem B5104457 : Blo 670310 5104457 := bstep (se 2 (by rfl) ⟨1914171, by rfl⟩ : syracuseStep 5104457 = 3828343) B3828343
theorem B1008479 : Blo 670310 1008479 := bstep (se 1 (by rfl) ⟨756359, by rfl⟩ : syracuseStep 1008479 = 1512719) B1512719
theorem B6120299 : Blo 670310 6120299 := bstep (se 1 (by rfl) ⟨4590224, by rfl⟩ : syracuseStep 6120299 = 9180449) B9180449
theorem B1008491 : Blo 670310 1008491 := bstep (se 1 (by rfl) ⟨756368, by rfl⟩ : syracuseStep 1008491 = 1512737) B1512737
theorem B1008719 : Blo 670310 1008719 := bstep (se 1 (by rfl) ⟨756539, by rfl⟩ : syracuseStep 1008719 = 1513079) B1513079
theorem B1008839 : Blo 670310 1008839 := bstep (se 1 (by rfl) ⟨756629, by rfl⟩ : syracuseStep 1008839 = 1513259) B1513259
theorem B1009001 : Blo 670310 1009001 := bstep (se 2 (by rfl) ⟨378375, by rfl⟩ : syracuseStep 1009001 = 756751) B756751
theorem B1009079 : Blo 670310 1009079 := bstep (se 1 (by rfl) ⟨756809, by rfl⟩ : syracuseStep 1009079 = 1513619) B1513619
theorem B1009115 : Blo 670310 1009115 := bstep (se 1 (by rfl) ⟨756836, by rfl⟩ : syracuseStep 1009115 = 1513673) B1513673
theorem B1435553 : Blo 670310 1435553 := bstep (se 2 (by rfl) ⟨538332, by rfl⟩ : syracuseStep 1435553 = 1076665) B1076665
theorem B1009583 : Blo 670310 1009583 := bstep (se 1 (by rfl) ⟨757187, by rfl⟩ : syracuseStep 1009583 = 1514375) B1514375
theorem B1697719 : Blo 670310 1697719 := bstep (se 1 (by rfl) ⟨1273289, by rfl⟩ : syracuseStep 1697719 = 2546579) B2546579
theorem B1009673 : Blo 670310 1009673 := bstep (se 2 (by rfl) ⟨378627, by rfl⟩ : syracuseStep 1009673 = 757255) B757255
theorem B1009703 : Blo 670310 1009703 := bstep (se 1 (by rfl) ⟨757277, by rfl⟩ : syracuseStep 1009703 = 1514555) B1514555
theorem B1009787 : Blo 670310 1009787 := bstep (se 1 (by rfl) ⟨757340, by rfl⟩ : syracuseStep 1009787 = 1514681) B1514681
theorem B682183 : Blo 670310 682183 := bstep (se 1 (by rfl) ⟨511637, by rfl⟩ : syracuseStep 682183 = 1023275) B1023275
theorem B1009913 : Blo 670310 1009913 := bstep (se 2 (by rfl) ⟨378717, by rfl⟩ : syracuseStep 1009913 = 757435) B757435
theorem B1010015 : Blo 670310 1010015 := bstep (se 1 (by rfl) ⟨757511, by rfl⟩ : syracuseStep 1010015 = 1515023) B1515023
theorem B10905961 : Blo 670310 10905961 := bstep (se 2 (by rfl) ⟨4089735, by rfl⟩ : syracuseStep 10905961 = 8179471) B8179471
theorem B1010027 : Blo 670310 1010027 := bstep (se 1 (by rfl) ⟨757520, by rfl⟩ : syracuseStep 1010027 = 1515041) B1515041
theorem B6449645 : Blo 670310 6449645 := bstep (se 3 (by rfl) ⟨1209308, by rfl⟩ : syracuseStep 6449645 = 2418617) B2418617
theorem B1010255 : Blo 670310 1010255 := bstep (se 1 (by rfl) ⟨757691, by rfl⟩ : syracuseStep 1010255 = 1515383) B1515383
theorem B1010375 : Blo 670310 1010375 := bstep (se 1 (by rfl) ⟨757781, by rfl⟩ : syracuseStep 1010375 = 1515563) B1515563
theorem B682831 : Blo 670310 682831 := bstep (se 1 (by rfl) ⟨512123, by rfl⟩ : syracuseStep 682831 = 1024247) B1024247
theorem B1010537 : Blo 670310 1010537 := bstep (se 2 (by rfl) ⟨378951, by rfl⟩ : syracuseStep 1010537 = 757903) B757903
theorem B2550635 : Blo 670310 2550635 := bstep (se 1 (by rfl) ⟨1912976, by rfl⟩ : syracuseStep 2550635 = 3825953) B3825953
theorem B1010615 : Blo 670310 1010615 := bstep (se 1 (by rfl) ⟨757961, by rfl⟩ : syracuseStep 1010615 = 1515923) B1515923
theorem B1010651 : Blo 670310 1010651 := bstep (se 1 (by rfl) ⟨757988, by rfl⟩ : syracuseStep 1010651 = 1515977) B1515977
theorem B1699177 : Blo 670310 1699177 := bstep (se 2 (by rfl) ⟨637191, by rfl⟩ : syracuseStep 1699177 = 1274383) B1274383
theorem B3403133 : Blo 670310 3403133 := bstep (se 3 (by rfl) ⟨638087, by rfl⟩ : syracuseStep 3403133 = 1276175) B1276175
theorem B1011119 : Blo 670310 1011119 := bstep (se 1 (by rfl) ⟨758339, by rfl⟩ : syracuseStep 1011119 = 1516679) B1516679
theorem B1437193 : Blo 670310 1437193 := bstep (se 2 (by rfl) ⟨538947, by rfl⟩ : syracuseStep 1437193 = 1077895) B1077895
theorem B1011209 : Blo 670310 1011209 := bstep (se 2 (by rfl) ⟨379203, by rfl⟩ : syracuseStep 1011209 = 758407) B758407
theorem B1011239 : Blo 670310 1011239 := bstep (se 1 (by rfl) ⟨758429, by rfl⟩ : syracuseStep 1011239 = 1516859) B1516859
theorem B1699451 : Blo 670310 1699451 := bstep (se 1 (by rfl) ⟨1274588, by rfl⟩ : syracuseStep 1699451 = 2549177) B2549177
theorem B1011323 : Blo 670310 1011323 := bstep (se 1 (by rfl) ⟨758492, by rfl⟩ : syracuseStep 1011323 = 1516985) B1516985
theorem B1634003 : Blo 670310 1634003 := bstep (se 1 (by rfl) ⟨1225502, by rfl⟩ : syracuseStep 1634003 = 2451005) B2451005
theorem B1011449 : Blo 670310 1011449 := bstep (se 2 (by rfl) ⟨379293, by rfl⟩ : syracuseStep 1011449 = 758587) B758587
theorem B10907459 : Blo 670310 10907459 := bstep (se 1 (by rfl) ⟨8180594, by rfl⟩ : syracuseStep 10907459 = 16361189) B16361189
theorem B22409095 : Blo 670310 22409095 := bstep (se 1 (by rfl) ⟨16806821, by rfl⟩ : syracuseStep 22409095 = 33613643) B33613643
theorem B12283811 : Blo 670310 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B2879495 : Blo 670310 2879495 := bstep (se 1 (by rfl) ⟨2159621, by rfl⟩ : syracuseStep 2879495 = 4319243) B4319243
theorem B1536079 : Blo 670310 1536079 := bstep (se 1 (by rfl) ⟨1152059, by rfl⟩ : syracuseStep 1536079 = 2304119) B2304119
theorem B2880211 : Blo 670310 2880211 := bstep (se 1 (by rfl) ⟨2160158, by rfl⟩ : syracuseStep 2880211 = 4320317) B4320317
theorem B2159389 : Blo 670310 2159389 := bstep (se 3 (by rfl) ⟨404885, by rfl⟩ : syracuseStep 2159389 = 809771) B809771
theorem B1438739 : Blo 670310 1438739 := bstep (se 1 (by rfl) ⟨1079054, by rfl⟩ : syracuseStep 1438739 = 2158109) B2158109
theorem B7468081 : Blo 670310 7468081 := bstep (se 2 (by rfl) ⟨2800530, by rfl⟩ : syracuseStep 7468081 = 5601061) B5601061
theorem B7664705 : Blo 670310 7664705 := bstep (se 2 (by rfl) ⟨2874264, by rfl⟩ : syracuseStep 7664705 = 5748529) B5748529
theorem B6911041 : Blo 670310 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B2421875 : Blo 670310 2421875 := bstep (se 1 (by rfl) ⟨1816406, by rfl⟩ : syracuseStep 2421875 = 3632813) B3632813
theorem B2553079 : Blo 670310 2553079 := bstep (se 1 (by rfl) ⟨1914809, by rfl⟩ : syracuseStep 2553079 = 3829619) B3829619
theorem B1701263 : Blo 670310 1701263 := bstep (se 1 (by rfl) ⟨1275947, by rfl⟩ : syracuseStep 1701263 = 2551895) B2551895
theorem B718255 : Blo 670310 718255 := bstep (se 1 (by rfl) ⟨538691, by rfl⟩ : syracuseStep 718255 = 1077383) B1077383
theorem B1078715 : Blo 670310 1078715 := bstep (se 1 (by rfl) ⟨809036, by rfl⟩ : syracuseStep 1078715 = 1618073) B1618073
theorem B1275355 : Blo 670310 1275355 := bstep (se 1 (by rfl) ⟨956516, by rfl⟩ : syracuseStep 1275355 = 1913033) B1913033
theorem B3831259 : Blo 670310 3831259 := bstep (se 1 (by rfl) ⟨2873444, by rfl⟩ : syracuseStep 3831259 = 5746889) B5746889
theorem B1275401 : Blo 670310 1275401 := bstep (se 2 (by rfl) ⟨478275, by rfl⟩ : syracuseStep 1275401 = 956551) B956551
theorem B2553353 : Blo 670310 2553353 := bstep (se 2 (by rfl) ⟨957507, by rfl⟩ : syracuseStep 2553353 = 1915015) B1915015
theorem B2553383 : Blo 670310 2553383 := bstep (se 1 (by rfl) ⟨1915037, by rfl⟩ : syracuseStep 2553383 = 3830075) B3830075
theorem B1701587 : Blo 670310 1701587 := bstep (se 1 (by rfl) ⟨1276190, by rfl⟩ : syracuseStep 1701587 = 2552381) B2552381
theorem B1275743 : Blo 670310 1275743 := bstep (se 1 (by rfl) ⟨956807, by rfl⟩ : syracuseStep 1275743 = 1913615) B1913615
theorem B849847 : Blo 670310 849847 := bstep (se 1 (by rfl) ⟨637385, by rfl⟩ : syracuseStep 849847 = 1274771) B1274771
theorem B2554051 : Blo 670310 2554051 := bstep (se 1 (by rfl) ⟨1915538, by rfl⟩ : syracuseStep 2554051 = 3831077) B3831077
theorem B2455913 : Blo 670310 2455913 := bstep (se 2 (by rfl) ⟨920967, by rfl⟩ : syracuseStep 2455913 = 1841935) B1841935
theorem B1079657 : Blo 670310 1079657 := bstep (se 2 (by rfl) ⟨404871, by rfl⟩ : syracuseStep 1079657 = 809743) B809743
theorem B2554355 : Blo 670310 2554355 := bstep (se 1 (by rfl) ⟨1915766, by rfl⟩ : syracuseStep 2554355 = 3831533) B3831533
theorem B12909131 : Blo 670310 12909131 := bstep (se 1 (by rfl) ⟨9681848, by rfl⟩ : syracuseStep 12909131 = 19363697) B19363697
theorem B1276859 : Blo 670310 1276859 := bstep (se 1 (by rfl) ⟨957644, by rfl⟩ : syracuseStep 1276859 = 1915289) B1915289
theorem B2554811 : Blo 670310 2554811 := bstep (se 1 (by rfl) ⟨1916108, by rfl⟩ : syracuseStep 2554811 = 3832217) B3832217
theorem B851143 : Blo 670310 851143 := bstep (se 1 (by rfl) ⟨638357, by rfl⟩ : syracuseStep 851143 = 1276715) B1276715
theorem B21855511 : Blo 670310 21855511 := bstep (se 1 (by rfl) ⟨16391633, by rfl⟩ : syracuseStep 21855511 = 32783267) B32783267
theorem B1277345 : Blo 670310 1277345 := bstep (se 2 (by rfl) ⟨479004, by rfl⟩ : syracuseStep 1277345 = 958009) B958009
theorem B10911149 : Blo 670310 10911149 := bstep (se 3 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 10911149 = 4091681) B4091681
theorem B3407507 : Blo 670310 3407507 := bstep (se 1 (by rfl) ⟨2555630, by rfl⟩ : syracuseStep 3407507 = 5111261) B5111261
theorem B1277687 : Blo 670310 1277687 := bstep (se 1 (by rfl) ⟨958265, by rfl⟩ : syracuseStep 1277687 = 1916531) B1916531
theorem B851887 : Blo 670310 851887 := bstep (se 1 (by rfl) ⟨638915, by rfl⟩ : syracuseStep 851887 = 1277831) B1277831
theorem B1703855 : Blo 670310 1703855 := bstep (se 1 (by rfl) ⟨1277891, by rfl⟩ : syracuseStep 1703855 = 2555783) B2555783
theorem B2588777 : Blo 670310 2588777 := bstep (se 2 (by rfl) ⟨970791, by rfl⟩ : syracuseStep 2588777 = 1941583) B1941583
theorem B1704847 : Blo 670310 1704847 := bstep (se 1 (by rfl) ⟨1278635, by rfl⟩ : syracuseStep 1704847 = 2557271) B2557271
theorem B5833619 : Blo 670310 5833619 := bstep (se 1 (by rfl) ⟨4375214, by rfl⟩ : syracuseStep 5833619 = 8750429) B8750429
theorem B1508327 : Blo 670310 1508327 := bstep (se 1 (by rfl) ⟨1131245, by rfl⟩ : syracuseStep 1508327 = 2262491) B2262491
theorem B754663 : Blo 670310 754663 := bstep (se 1 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 754663 = 1131995) B1131995
theorem B5538959 : Blo 670310 5538959 := bstep (se 1 (by rfl) ⟨4154219, by rfl⟩ : syracuseStep 5538959 = 8308439) B8308439
theorem B7669079 : Blo 670310 7669079 := bstep (se 1 (by rfl) ⟨5751809, by rfl⟩ : syracuseStep 7669079 = 11503619) B11503619
theorem B1508705 : Blo 670310 1508705 := bstep (se 2 (by rfl) ⟨565764, by rfl⟩ : syracuseStep 1508705 = 1131529) B1131529
theorem B1705313 : Blo 670310 1705313 := bstep (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) B1278985
theorem B918907 : Blo 670310 918907 := bstep (se 1 (by rfl) ⟨689180, by rfl⟩ : syracuseStep 918907 = 1378361) B1378361
theorem B1508795 : Blo 670310 1508795 := bstep (se 1 (by rfl) ⟨1131596, by rfl⟩ : syracuseStep 1508795 = 2263193) B2263193
theorem B2426375 : Blo 670310 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B1508921 : Blo 670310 1508921 := bstep (se 2 (by rfl) ⟨565845, by rfl⟩ : syracuseStep 1508921 = 1131691) B1131691
theorem B1705769 : Blo 670310 1705769 := bstep (se 2 (by rfl) ⟨639663, by rfl⟩ : syracuseStep 1705769 = 1279327) B1279327
theorem B1476407 : Blo 670310 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B3639127 : Blo 670310 3639127 := bstep (se 1 (by rfl) ⟨2729345, by rfl⟩ : syracuseStep 3639127 = 5458691) B5458691
theorem B1509587 : Blo 670310 1509587 := bstep (se 1 (by rfl) ⟨1132190, by rfl⟩ : syracuseStep 1509587 = 2264381) B2264381
theorem B1509641 : Blo 670310 1509641 := bstep (se 2 (by rfl) ⟨566115, by rfl⟩ : syracuseStep 1509641 = 1132231) B1132231
theorem B16320797 : Blo 670310 16320797 := bstep (se 3 (by rfl) ⟨3060149, by rfl⟩ : syracuseStep 16320797 = 6120299) B6120299
theorem B2263463 : Blo 670310 2263463 := bstep (se 1 (by rfl) ⟨1697597, by rfl⟩ : syracuseStep 2263463 = 3395195) B3395195
theorem B1509857 : Blo 670310 1509857 := bstep (se 2 (by rfl) ⟨566196, by rfl⟩ : syracuseStep 1509857 = 1132393) B1132393
theorem B2263625 : Blo 670310 2263625 := bstep (se 2 (by rfl) ⟨848859, by rfl⟩ : syracuseStep 2263625 = 1697719) B1697719
theorem B756319 : Blo 670310 756319 := bstep (se 1 (by rfl) ⟨567239, by rfl⟩ : syracuseStep 756319 = 1134479) B1134479
theorem B1510163 : Blo 670310 1510163 := bstep (se 1 (by rfl) ⟨1132622, by rfl⟩ : syracuseStep 1510163 = 2265245) B2265245
theorem B1706771 : Blo 670310 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B2427803 : Blo 670310 2427803 := bstep (se 1 (by rfl) ⟨1820852, by rfl⟩ : syracuseStep 2427803 = 3641705) B3641705
theorem B1510523 : Blo 670310 1510523 := bstep (se 1 (by rfl) ⟨1132892, by rfl⟩ : syracuseStep 1510523 = 2265785) B2265785
theorem B1510649 : Blo 670310 1510649 := bstep (se 2 (by rfl) ⟨566493, by rfl⟩ : syracuseStep 1510649 = 1132987) B1132987
theorem B1510793 : Blo 670310 1510793 := bstep (se 2 (by rfl) ⟨566547, by rfl⟩ : syracuseStep 1510793 = 1133095) B1133095
theorem B1510919 : Blo 670310 1510919 := bstep (se 1 (by rfl) ⟨1133189, by rfl⟩ : syracuseStep 1510919 = 2266379) B2266379
theorem B1511099 : Blo 670310 1511099 := bstep (se 1 (by rfl) ⟨1133324, by rfl⟩ : syracuseStep 1511099 = 2266649) B2266649
theorem B757471 : Blo 670310 757471 := bstep (se 1 (by rfl) ⟨568103, by rfl⟩ : syracuseStep 757471 = 1136207) B1136207
theorem B3411719 : Blo 670310 3411719 := bstep (se 1 (by rfl) ⟨2558789, by rfl⟩ : syracuseStep 3411719 = 5117579) B5117579
theorem B1511225 : Blo 670310 1511225 := bstep (se 2 (by rfl) ⟨566709, by rfl⟩ : syracuseStep 1511225 = 1133419) B1133419
theorem B11473001 : Blo 670310 11473001 := bstep (se 2 (by rfl) ⟨4302375, by rfl⟩ : syracuseStep 11473001 = 8604751) B8604751
theorem B2265299 : Blo 670310 2265299 := bstep (se 1 (by rfl) ⟨1698974, by rfl⟩ : syracuseStep 2265299 = 3397949) B3397949
theorem B758047 : Blo 670310 758047 := bstep (se 1 (by rfl) ⟨568535, by rfl⟩ : syracuseStep 758047 = 1137071) B1137071
theorem B3641765 : Blo 670310 3641765 := bstep (se 4 (by rfl) ⟨341415, by rfl⟩ : syracuseStep 3641765 = 682831) B682831
theorem B1511855 : Blo 670310 1511855 := bstep (se 1 (by rfl) ⟨1133891, by rfl⟩ : syracuseStep 1511855 = 2267783) B2267783
theorem B1511891 : Blo 670310 1511891 := bstep (se 1 (by rfl) ⟨1133918, by rfl⟩ : syracuseStep 1511891 = 2267837) B2267837
theorem B2265569 : Blo 670310 2265569 := bstep (se 2 (by rfl) ⟨849588, by rfl⟩ : syracuseStep 2265569 = 1699177) B1699177
theorem B1511999 : Blo 670310 1511999 := bstep (se 1 (by rfl) ⟨1133999, by rfl⟩ : syracuseStep 1511999 = 2267999) B2267999
theorem B758335 : Blo 670310 758335 := bstep (se 1 (by rfl) ⟨568751, by rfl⟩ : syracuseStep 758335 = 1137503) B1137503
theorem B1512107 : Blo 670310 1512107 := bstep (se 1 (by rfl) ⟨1134080, by rfl⟩ : syracuseStep 1512107 = 2268161) B2268161
theorem B4100831 : Blo 670310 4100831 := bstep (se 1 (by rfl) ⟨3075623, by rfl⟩ : syracuseStep 4100831 = 6151247) B6151247
theorem B4297637 : Blo 670310 4297637 := bstep (se 4 (by rfl) ⟨402903, by rfl⟩ : syracuseStep 4297637 = 805807) B805807
theorem B2429891 : Blo 670310 2429891 := bstep (se 1 (by rfl) ⟨1822418, by rfl⟩ : syracuseStep 2429891 = 3644837) B3644837
theorem B3871901 : Blo 670310 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B1512647 : Blo 670310 1512647 := bstep (se 1 (by rfl) ⟨1134485, by rfl⟩ : syracuseStep 1512647 = 2268971) B2268971
theorem B4592855 : Blo 670310 4592855 := bstep (se 1 (by rfl) ⟨3444641, by rfl⟩ : syracuseStep 4592855 = 6889283) B6889283
theorem B1512827 : Blo 670310 1512827 := bstep (se 1 (by rfl) ⟨1134620, by rfl⟩ : syracuseStep 1512827 = 2269241) B2269241
theorem B4298123 : Blo 670310 4298123 := bstep (se 1 (by rfl) ⟨3223592, by rfl⟩ : syracuseStep 4298123 = 6447185) B6447185
theorem B1512953 : Blo 670310 1512953 := bstep (se 2 (by rfl) ⟨567357, by rfl⟩ : syracuseStep 1512953 = 1134715) B1134715
theorem B1513043 : Blo 670310 1513043 := bstep (se 1 (by rfl) ⟨1134782, by rfl⟩ : syracuseStep 1513043 = 2269565) B2269565
theorem B2266811 : Blo 670310 2266811 := bstep (se 1 (by rfl) ⟨1700108, by rfl⟩ : syracuseStep 2266811 = 3400217) B3400217
theorem B1513223 : Blo 670310 1513223 := bstep (se 1 (by rfl) ⟨1134917, by rfl⟩ : syracuseStep 1513223 = 2269835) B2269835
theorem B956215 : Blo 670310 956215 := bstep (se 1 (by rfl) ⟨717161, by rfl⟩ : syracuseStep 956215 = 1434323) B1434323
theorem B5183461 : Blo 670310 5183461 := bstep (se 4 (by rfl) ⟨485949, by rfl⟩ : syracuseStep 5183461 = 971899) B971899
theorem B11507993 : Blo 670310 11507993 := bstep (se 2 (by rfl) ⟨4315497, by rfl⟩ : syracuseStep 11507993 = 8630995) B8630995
theorem B3840281 : Blo 670310 3840281 := bstep (se 2 (by rfl) ⟨1440105, by rfl⟩ : syracuseStep 3840281 = 2880211) B2880211
theorem B1513835 : Blo 670310 1513835 := bstep (se 1 (by rfl) ⟨1135376, by rfl⟩ : syracuseStep 1513835 = 2270753) B2270753
theorem B1513979 : Blo 670310 1513979 := bstep (se 1 (by rfl) ⟨1135484, by rfl⟩ : syracuseStep 1513979 = 2270969) B2270969
theorem B957035 : Blo 670310 957035 := bstep (se 1 (by rfl) ⟨717776, by rfl⟩ : syracuseStep 957035 = 1435553) B1435553
theorem B1514105 : Blo 670310 1514105 := bstep (se 2 (by rfl) ⟨567789, by rfl⟩ : syracuseStep 1514105 = 1135579) B1135579
theorem B1514159 : Blo 670310 1514159 := bstep (se 1 (by rfl) ⟨1135619, by rfl⟩ : syracuseStep 1514159 = 2271239) B2271239
theorem B1514231 : Blo 670310 1514231 := bstep (se 1 (by rfl) ⟨1135673, by rfl⟩ : syracuseStep 1514231 = 2271347) B2271347
theorem B9214721 : Blo 670310 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B99195749 : Blo 670310 99195749 := bstep (se 4 (by rfl) ⟨9299601, by rfl⟩ : syracuseStep 99195749 = 18599203) B18599203
theorem B1514411 : Blo 670310 1514411 := bstep (se 1 (by rfl) ⟨1135808, by rfl⟩ : syracuseStep 1514411 = 2271617) B2271617
theorem B4299763 : Blo 670310 4299763 := bstep (se 1 (by rfl) ⟨3224822, by rfl⟩ : syracuseStep 4299763 = 6449645) B6449645
theorem B9182429 : Blo 670310 9182429 := bstep (se 3 (by rfl) ⟨1721705, by rfl⟩ : syracuseStep 9182429 = 3443411) B3443411
theorem B957673 : Blo 670310 957673 := bstep (se 2 (by rfl) ⟨359127, by rfl⟩ : syracuseStep 957673 = 718255) B718255
theorem B1514951 : Blo 670310 1514951 := bstep (se 1 (by rfl) ⟨1136213, by rfl⟩ : syracuseStep 1514951 = 2272427) B2272427
theorem B5447249 : Blo 670310 5447249 := bstep (se 2 (by rfl) ⟨2042718, by rfl⟩ : syracuseStep 5447249 = 4085437) B4085437
theorem B2268755 : Blo 670310 2268755 := bstep (se 1 (by rfl) ⟨1701566, by rfl⟩ : syracuseStep 2268755 = 3403133) B3403133
theorem B1515311 : Blo 670310 1515311 := bstep (se 1 (by rfl) ⟨1136483, by rfl⟩ : syracuseStep 1515311 = 2272967) B2272967
theorem B1089335 : Blo 670310 1089335 := bstep (se 1 (by rfl) ⟨817001, by rfl⟩ : syracuseStep 1089335 = 1634003) B1634003
theorem B5120009 : Blo 670310 5120009 := bstep (se 2 (by rfl) ⟨1920003, by rfl⟩ : syracuseStep 5120009 = 3840007) B3840007
theorem B1908841 : Blo 670310 1908841 := bstep (se 2 (by rfl) ⟨715815, by rfl⟩ : syracuseStep 1908841 = 1431631) B1431631
theorem B1515887 : Blo 670310 1515887 := bstep (se 1 (by rfl) ⟨1136915, by rfl⟩ : syracuseStep 1515887 = 2273831) B2273831
theorem B1515959 : Blo 670310 1515959 := bstep (se 1 (by rfl) ⟨1136969, by rfl⟩ : syracuseStep 1515959 = 2273939) B2273939
theorem B1516103 : Blo 670310 1516103 := bstep (se 1 (by rfl) ⟨1137077, by rfl⟩ : syracuseStep 1516103 = 2274155) B2274155
theorem B1516139 : Blo 670310 1516139 := bstep (se 1 (by rfl) ⟨1137104, by rfl⟩ : syracuseStep 1516139 = 2274209) B2274209
theorem B959159 : Blo 670310 959159 := bstep (se 1 (by rfl) ⟨719369, by rfl⟩ : syracuseStep 959159 = 1438739) B1438739
theorem B1614583 : Blo 670310 1614583 := bstep (se 1 (by rfl) ⟨1210937, by rfl⟩ : syracuseStep 1614583 = 2421875) B2421875
theorem B4301761 : Blo 670310 4301761 := bstep (se 2 (by rfl) ⟨1613160, by rfl⟩ : syracuseStep 4301761 = 3226321) B3226321
theorem B1516535 : Blo 670310 1516535 := bstep (se 1 (by rfl) ⟨1137401, by rfl⟩ : syracuseStep 1516535 = 2274803) B2274803
theorem B11609189 : Blo 670310 11609189 := bstep (se 4 (by rfl) ⟨1088361, by rfl⟩ : syracuseStep 11609189 = 2176723) B2176723
theorem B1516895 : Blo 670310 1516895 := bstep (se 1 (by rfl) ⟨1137671, by rfl⟩ : syracuseStep 1516895 = 2275343) B2275343
theorem B1812125 : Blo 670310 1812125 := bstep (se 3 (by rfl) ⟨339773, by rfl⟩ : syracuseStep 1812125 = 679547) B679547
theorem B1910459 : Blo 670310 1910459 := bstep (se 1 (by rfl) ⟨1432844, by rfl⟩ : syracuseStep 1910459 = 2865689) B2865689
theorem B29140681 : Blo 670310 29140681 := bstep (se 2 (by rfl) ⟨10927755, by rfl⟩ : syracuseStep 29140681 = 21855511) B21855511
theorem B34875299 : Blo 670310 34875299 := bstep (se 1 (by rfl) ⟨26156474, by rfl⟩ : syracuseStep 34875299 = 52312949) B52312949
theorem B3221633 : Blo 670310 3221633 := bstep (se 2 (by rfl) ⟨1208112, by rfl⟩ : syracuseStep 3221633 = 2416225) B2416225
theorem B3221785 : Blo 670310 3221785 := bstep (se 2 (by rfl) ⟨1208169, by rfl⟩ : syracuseStep 3221785 = 2416339) B2416339
theorem B2271671 : Blo 670310 2271671 := bstep (se 1 (by rfl) ⟨1703753, by rfl⟩ : syracuseStep 2271671 = 3407507) B3407507
theorem B7253171 : Blo 670310 7253171 := bstep (se 1 (by rfl) ⟨5439878, by rfl⟩ : syracuseStep 7253171 = 10879757) B10879757
theorem B1813855 : Blo 670310 1813855 := bstep (se 1 (by rfl) ⟨1360391, by rfl⟩ : syracuseStep 1813855 = 2720783) B2720783
theorem B5746139 : Blo 670310 5746139 := bstep (se 1 (by rfl) ⟨4309604, by rfl⟩ : syracuseStep 5746139 = 8619209) B8619209
theorem B2305651 : Blo 670310 2305651 := bstep (se 1 (by rfl) ⟨1729238, by rfl⟩ : syracuseStep 2305651 = 3458477) B3458477
theorem B9187015 : Blo 670310 9187015 := bstep (se 1 (by rfl) ⟨6890261, by rfl⟩ : syracuseStep 9187015 = 13780523) B13780523
theorem B44183825 : Blo 670310 44183825 := bstep (se 2 (by rfl) ⟨16568934, by rfl⟩ : syracuseStep 44183825 = 33137869) B33137869
theorem B2863451 : Blo 670310 2863451 := bstep (se 1 (by rfl) ⟨2147588, by rfl⟩ : syracuseStep 2863451 = 4295177) B4295177
theorem B2732395 : Blo 670310 2732395 := bstep (se 1 (by rfl) ⟨2049296, by rfl⟩ : syracuseStep 2732395 = 4098593) B4098593
theorem B3060575 : Blo 670310 3060575 := bstep (se 1 (by rfl) ⟨2295431, by rfl⟩ : syracuseStep 3060575 = 4590863) B4590863
theorem B1913831 : Blo 670310 1913831 := bstep (se 1 (by rfl) ⟨1435373, by rfl⟩ : syracuseStep 1913831 = 2870747) B2870747
theorem B6468599 : Blo 670310 6468599 := bstep (se 1 (by rfl) ⟨4851449, by rfl⟩ : syracuseStep 6468599 = 9702899) B9702899
theorem B4306067 : Blo 670310 4306067 := bstep (se 1 (by rfl) ⟨3229550, by rfl⟩ : syracuseStep 4306067 = 6459101) B6459101
theorem B2864423 : Blo 670310 2864423 := bstep (se 1 (by rfl) ⟨2148317, by rfl⟩ : syracuseStep 2864423 = 4296635) B4296635
theorem B2274749 : Blo 670310 2274749 := bstep (se 3 (by rfl) ⟨426515, by rfl⟩ : syracuseStep 2274749 = 853031) B853031
theorem B2275127 : Blo 670310 2275127 := bstep (se 1 (by rfl) ⟨1706345, by rfl⟩ : syracuseStep 2275127 = 3412691) B3412691
theorem B9680755 : Blo 670310 9680755 := bstep (se 1 (by rfl) ⟨7260566, by rfl⟩ : syracuseStep 9680755 = 14521133) B14521133
theorem B2275613 : Blo 670310 2275613 := bstep (se 3 (by rfl) ⟨426677, by rfl⟩ : syracuseStep 2275613 = 853355) B853355
theorem B670431 : Blo 670310 670431 := bstep (se 1 (by rfl) ⟨502823, by rfl⟩ : syracuseStep 670431 = 1005647) B1005647
theorem B670511 : Blo 670310 670511 := bstep (se 1 (by rfl) ⟨502883, by rfl⟩ : syracuseStep 670511 = 1005767) B1005767
theorem B11516741 : Blo 670310 11516741 := bstep (se 4 (by rfl) ⟨1079694, by rfl⟩ : syracuseStep 11516741 = 2159389) B2159389
theorem B670619 : Blo 670310 670619 := bstep (se 1 (by rfl) ⟨502964, by rfl⟩ : syracuseStep 670619 = 1005929) B1005929
theorem B670671 : Blo 670310 670671 := bstep (se 1 (by rfl) ⟨503003, by rfl⟩ : syracuseStep 670671 = 1006007) B1006007
theorem B670695 : Blo 670310 670695 := bstep (se 1 (by rfl) ⟨503021, by rfl⟩ : syracuseStep 670695 = 1006043) B1006043
theorem B5258429 : Blo 670310 5258429 := bstep (se 3 (by rfl) ⟨985955, by rfl⟩ : syracuseStep 5258429 = 1971911) B1971911
theorem B1817833 : Blo 670310 1817833 := bstep (se 2 (by rfl) ⟨681687, by rfl⟩ : syracuseStep 1817833 = 1363375) B1363375
theorem B671007 : Blo 670310 671007 := bstep (se 1 (by rfl) ⟨503255, by rfl⟩ : syracuseStep 671007 = 1006511) B1006511
theorem B671067 : Blo 670310 671067 := bstep (se 1 (by rfl) ⟨503300, by rfl⟩ : syracuseStep 671067 = 1006601) B1006601
theorem B1916257 : Blo 670310 1916257 := bstep (se 2 (by rfl) ⟨718596, by rfl⟩ : syracuseStep 1916257 = 1437193) B1437193
theorem B671087 : Blo 670310 671087 := bstep (se 1 (by rfl) ⟨503315, by rfl⟩ : syracuseStep 671087 = 1006631) B1006631
theorem B671143 : Blo 670310 671143 := bstep (se 1 (by rfl) ⟨503357, by rfl⟩ : syracuseStep 671143 = 1006715) B1006715
theorem B3456443 : Blo 670310 3456443 := bstep (se 1 (by rfl) ⟨2592332, by rfl⟩ : syracuseStep 3456443 = 5184665) B5184665
theorem B671227 : Blo 670310 671227 := bstep (se 1 (by rfl) ⟨503420, by rfl⟩ : syracuseStep 671227 = 1006841) B1006841
theorem B2866747 : Blo 670310 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B671295 : Blo 670310 671295 := bstep (se 1 (by rfl) ⟨503471, by rfl⟩ : syracuseStep 671295 = 1006943) B1006943
theorem B671303 : Blo 670310 671303 := bstep (se 1 (by rfl) ⟨503477, by rfl⟩ : syracuseStep 671303 = 1006955) B1006955
theorem B6471251 : Blo 670310 6471251 := bstep (se 1 (by rfl) ⟨4853438, by rfl⟩ : syracuseStep 6471251 = 9706877) B9706877
theorem B671455 : Blo 670310 671455 := bstep (se 1 (by rfl) ⟨503591, by rfl⟩ : syracuseStep 671455 = 1007183) B1007183
theorem B671535 : Blo 670310 671535 := bstep (se 1 (by rfl) ⟨503651, by rfl⟩ : syracuseStep 671535 = 1007303) B1007303
theorem B671643 : Blo 670310 671643 := bstep (se 1 (by rfl) ⟨503732, by rfl⟩ : syracuseStep 671643 = 1007465) B1007465
theorem B671695 : Blo 670310 671695 := bstep (se 1 (by rfl) ⟨503771, by rfl⟩ : syracuseStep 671695 = 1007543) B1007543
theorem B671719 : Blo 670310 671719 := bstep (se 1 (by rfl) ⟨503789, by rfl⟩ : syracuseStep 671719 = 1007579) B1007579
theorem B2048105 : Blo 670310 2048105 := bstep (se 2 (by rfl) ⟨768039, by rfl⟩ : syracuseStep 2048105 = 1536079) B1536079
theorem B39829765 : Blo 670310 39829765 := bstep (se 4 (by rfl) ⟨3734040, by rfl⟩ : syracuseStep 39829765 = 7468081) B7468081
theorem B672031 : Blo 670310 672031 := bstep (se 1 (by rfl) ⟨504023, by rfl⟩ : syracuseStep 672031 = 1008047) B1008047
theorem B672091 : Blo 670310 672091 := bstep (se 1 (by rfl) ⟨504068, by rfl⟩ : syracuseStep 672091 = 1008137) B1008137
theorem B672111 : Blo 670310 672111 := bstep (se 1 (by rfl) ⟨504083, by rfl⟩ : syracuseStep 672111 = 1008167) B1008167
theorem B672167 : Blo 670310 672167 := bstep (se 1 (by rfl) ⟨504125, by rfl⟩ : syracuseStep 672167 = 1008251) B1008251
theorem B672251 : Blo 670310 672251 := bstep (se 1 (by rfl) ⟨504188, by rfl⟩ : syracuseStep 672251 = 1008377) B1008377
theorem B672319 : Blo 670310 672319 := bstep (se 1 (by rfl) ⟨504239, by rfl⟩ : syracuseStep 672319 = 1008479) B1008479
theorem B672327 : Blo 670310 672327 := bstep (se 1 (by rfl) ⟨504245, by rfl⟩ : syracuseStep 672327 = 1008491) B1008491
theorem B672479 : Blo 670310 672479 := bstep (se 1 (by rfl) ⟨504359, by rfl⟩ : syracuseStep 672479 = 1008719) B1008719
theorem B672559 : Blo 670310 672559 := bstep (se 1 (by rfl) ⟨504419, by rfl⟩ : syracuseStep 672559 = 1008839) B1008839
theorem B9192269 : Blo 670310 9192269 := bstep (se 3 (by rfl) ⟨1723550, by rfl⟩ : syracuseStep 9192269 = 3447101) B3447101
theorem B2868047 : Blo 670310 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B672667 : Blo 670310 672667 := bstep (se 1 (by rfl) ⟨504500, by rfl⟩ : syracuseStep 672667 = 1009001) B1009001
theorem B672719 : Blo 670310 672719 := bstep (se 1 (by rfl) ⟨504539, by rfl⟩ : syracuseStep 672719 = 1009079) B1009079
theorem B3064807 : Blo 670310 3064807 := bstep (se 1 (by rfl) ⟨2298605, by rfl⟩ : syracuseStep 3064807 = 4597211) B4597211
theorem B672743 : Blo 670310 672743 := bstep (se 1 (by rfl) ⟨504557, by rfl⟩ : syracuseStep 672743 = 1009115) B1009115
theorem B3064823 : Blo 670310 3064823 := bstep (se 1 (by rfl) ⟨2298617, by rfl⟩ : syracuseStep 3064823 = 4597235) B4597235
theorem B1819847 : Blo 670310 1819847 := bstep (se 1 (by rfl) ⟨1364885, by rfl⟩ : syracuseStep 1819847 = 2729771) B2729771
theorem B1819867 : Blo 670310 1819867 := bstep (se 1 (by rfl) ⟨1364900, by rfl⟩ : syracuseStep 1819867 = 2729801) B2729801
theorem B5096681 : Blo 670310 5096681 := bstep (se 2 (by rfl) ⟨1911255, by rfl⟩ : syracuseStep 5096681 = 3822511) B3822511
theorem B673055 : Blo 670310 673055 := bstep (se 1 (by rfl) ⟨504791, by rfl⟩ : syracuseStep 673055 = 1009583) B1009583
theorem B2147627 : Blo 670310 2147627 := bstep (se 1 (by rfl) ⟨1610720, by rfl⟩ : syracuseStep 2147627 = 3221441) B3221441
theorem B673115 : Blo 670310 673115 := bstep (se 1 (by rfl) ⟨504836, by rfl⟩ : syracuseStep 673115 = 1009673) B1009673
theorem B673135 : Blo 670310 673135 := bstep (se 1 (by rfl) ⟨504851, by rfl⟩ : syracuseStep 673135 = 1009703) B1009703
theorem B673191 : Blo 670310 673191 := bstep (se 1 (by rfl) ⟨504893, by rfl⟩ : syracuseStep 673191 = 1009787) B1009787
theorem B673275 : Blo 670310 673275 := bstep (se 1 (by rfl) ⟨504956, by rfl⟩ : syracuseStep 673275 = 1009913) B1009913
theorem B2147897 : Blo 670310 2147897 := bstep (se 2 (by rfl) ⟨805461, by rfl⟩ : syracuseStep 2147897 = 1610923) B1610923
theorem B673343 : Blo 670310 673343 := bstep (se 1 (by rfl) ⟨505007, by rfl⟩ : syracuseStep 673343 = 1010015) B1010015
theorem B673351 : Blo 670310 673351 := bstep (se 1 (by rfl) ⟨505013, by rfl⟩ : syracuseStep 673351 = 1010027) B1010027
theorem B673503 : Blo 670310 673503 := bstep (se 1 (by rfl) ⟨505127, by rfl⟩ : syracuseStep 673503 = 1010255) B1010255
theorem B673583 : Blo 670310 673583 := bstep (se 1 (by rfl) ⟨505187, by rfl⟩ : syracuseStep 673583 = 1010375) B1010375
theorem B673691 : Blo 670310 673691 := bstep (se 1 (by rfl) ⟨505268, by rfl⟩ : syracuseStep 673691 = 1010537) B1010537
theorem B673743 : Blo 670310 673743 := bstep (se 1 (by rfl) ⟨505307, by rfl⟩ : syracuseStep 673743 = 1010615) B1010615
theorem B673767 : Blo 670310 673767 := bstep (se 1 (by rfl) ⟨505325, by rfl⟩ : syracuseStep 673767 = 1010651) B1010651
theorem B674079 : Blo 670310 674079 := bstep (se 1 (by rfl) ⟨505559, by rfl⟩ : syracuseStep 674079 = 1011119) B1011119
theorem B674139 : Blo 670310 674139 := bstep (se 1 (by rfl) ⟨505604, by rfl⟩ : syracuseStep 674139 = 1011209) B1011209
theorem B1821035 : Blo 670310 1821035 := bstep (se 1 (by rfl) ⟨1365776, by rfl⟩ : syracuseStep 1821035 = 2731553) B2731553
theorem B674159 : Blo 670310 674159 := bstep (se 1 (by rfl) ⟨505619, by rfl⟩ : syracuseStep 674159 = 1011239) B1011239
theorem B2902397 : Blo 670310 2902397 := bstep (se 3 (by rfl) ⟨544199, by rfl⟩ : syracuseStep 2902397 = 1088399) B1088399
theorem B1132967 : Blo 670310 1132967 := bstep (se 1 (by rfl) ⟨849725, by rfl⟩ : syracuseStep 1132967 = 1699451) B1699451
theorem B674215 : Blo 670310 674215 := bstep (se 1 (by rfl) ⟨505661, by rfl⟩ : syracuseStep 674215 = 1011323) B1011323
theorem B4147685 : Blo 670310 4147685 := bstep (se 4 (by rfl) ⟨388845, by rfl⟩ : syracuseStep 4147685 = 777691) B777691
theorem B674299 : Blo 670310 674299 := bstep (se 1 (by rfl) ⟨505724, by rfl⟩ : syracuseStep 674299 = 1011449) B1011449
theorem B2869823 : Blo 670310 2869823 := bstep (se 1 (by rfl) ⟨2152367, by rfl⟩ : syracuseStep 2869823 = 4304735) B4304735
theorem B1133129 : Blo 670310 1133129 := bstep (se 2 (by rfl) ⟨424923, by rfl⟩ : syracuseStep 1133129 = 849847) B849847
theorem B7359149 : Blo 670310 7359149 := bstep (se 3 (by rfl) ⟨1379840, by rfl⟩ : syracuseStep 7359149 = 2759681) B2759681
theorem B3394223 : Blo 670310 3394223 := bstep (se 1 (by rfl) ⟨2545667, by rfl⟩ : syracuseStep 3394223 = 5091335) B5091335
theorem B1919663 : Blo 670310 1919663 := bstep (se 1 (by rfl) ⟨1439747, by rfl⟩ : syracuseStep 1919663 = 2879495) B2879495
theorem B3394547 : Blo 670310 3394547 := bstep (se 1 (by rfl) ⟨2545910, by rfl⟩ : syracuseStep 3394547 = 5091821) B5091821
theorem B1134175 : Blo 670310 1134175 := bstep (se 1 (by rfl) ⟨850631, by rfl⟩ : syracuseStep 1134175 = 1701263) B1701263
theorem B1134391 : Blo 670310 1134391 := bstep (se 1 (by rfl) ⟨850793, by rfl⟩ : syracuseStep 1134391 = 1701587) B1701587
theorem B2150459 : Blo 670310 2150459 := bstep (se 1 (by rfl) ⟨1612844, by rfl⟩ : syracuseStep 2150459 = 3225689) B3225689
theorem B3395843 : Blo 670310 3395843 := bstep (se 1 (by rfl) ⟨2546882, by rfl⟩ : syracuseStep 3395843 = 5093765) B5093765
theorem B1134857 : Blo 670310 1134857 := bstep (se 2 (by rfl) ⟨425571, by rfl⟩ : syracuseStep 1134857 = 851143) B851143
theorem B8606087 : Blo 670310 8606087 := bstep (se 1 (by rfl) ⟨6454565, by rfl⟩ : syracuseStep 8606087 = 12909131) B12909131
theorem B5100083 : Blo 670310 5100083 := bstep (se 1 (by rfl) ⟨3825062, by rfl⟩ : syracuseStep 5100083 = 7650125) B7650125
theorem B3396167 : Blo 670310 3396167 := bstep (se 1 (by rfl) ⟨2547125, by rfl⟩ : syracuseStep 3396167 = 5094251) B5094251
theorem B2150983 : Blo 670310 2150983 := bstep (se 1 (by rfl) ⟨1613237, by rfl⟩ : syracuseStep 2150983 = 3226475) B3226475
theorem B7263377 : Blo 670310 7263377 := bstep (se 2 (by rfl) ⟨2723766, by rfl⟩ : syracuseStep 7263377 = 5447533) B5447533
theorem B1135849 : Blo 670310 1135849 := bstep (se 2 (by rfl) ⟨425943, by rfl⟩ : syracuseStep 1135849 = 851887) B851887
theorem B1135903 : Blo 670310 1135903 := bstep (se 1 (by rfl) ⟨851927, by rfl⟩ : syracuseStep 1135903 = 1703855) B1703855
theorem B2151803 : Blo 670310 2151803 := bstep (se 1 (by rfl) ⟨1613852, by rfl⟩ : syracuseStep 2151803 = 3227705) B3227705
theorem B11818541 : Blo 670310 11818541 := bstep (se 3 (by rfl) ⟨2215976, by rfl⟩ : syracuseStep 11818541 = 4431953) B4431953
theorem B1365599 : Blo 670310 1365599 := bstep (se 1 (by rfl) ⟨1024199, by rfl⟩ : syracuseStep 1365599 = 2048399) B2048399
theorem B1136315 : Blo 670310 1136315 := bstep (se 1 (by rfl) ⟨852236, by rfl⟩ : syracuseStep 1136315 = 1704473) B1704473
theorem B3397463 : Blo 670310 3397463 := bstep (se 1 (by rfl) ⟨2548097, by rfl⟩ : syracuseStep 3397463 = 5096195) B5096195
theorem B1529705 : Blo 670310 1529705 := bstep (se 2 (by rfl) ⟨573639, by rfl⟩ : syracuseStep 1529705 = 1147279) B1147279
theorem B5101541 : Blo 670310 5101541 := bstep (se 4 (by rfl) ⟨478269, by rfl⟩ : syracuseStep 5101541 = 956539) B956539
theorem B1005833 : Blo 670310 1005833 := bstep (se 2 (by rfl) ⟨377187, by rfl⟩ : syracuseStep 1005833 = 754375) B754375
theorem B1005935 : Blo 670310 1005935 := bstep (se 1 (by rfl) ⟨754451, by rfl⟩ : syracuseStep 1005935 = 1508903) B1508903
theorem B1366483 : Blo 670310 1366483 := bstep (se 1 (by rfl) ⟨1024862, by rfl⟩ : syracuseStep 1366483 = 2049725) B2049725
theorem B3267067 : Blo 670310 3267067 := bstep (se 1 (by rfl) ⟨2450300, by rfl⟩ : syracuseStep 3267067 = 4900601) B4900601
theorem B1006151 : Blo 670310 1006151 := bstep (se 1 (by rfl) ⟨754613, by rfl⟩ : syracuseStep 1006151 = 1509227) B1509227
theorem B1006187 : Blo 670310 1006187 := bstep (se 1 (by rfl) ⟨754640, by rfl⟩ : syracuseStep 1006187 = 1509281) B1509281
theorem B1006415 : Blo 670310 1006415 := bstep (se 1 (by rfl) ⟨754811, by rfl⟩ : syracuseStep 1006415 = 1509623) B1509623
theorem B2153341 : Blo 670310 2153341 := bstep (se 3 (by rfl) ⟨403751, by rfl⟩ : syracuseStep 2153341 = 807503) B807503
theorem B908263 : Blo 670310 908263 := bstep (se 1 (by rfl) ⟨681197, by rfl⟩ : syracuseStep 908263 = 1362395) B1362395
theorem B224386199 : Blo 670310 224386199 := bstep (se 1 (by rfl) ⟨168289649, by rfl⟩ : syracuseStep 224386199 = 336579299) B336579299
theorem B1006811 : Blo 670310 1006811 := bstep (se 1 (by rfl) ⟨755108, by rfl⟩ : syracuseStep 1006811 = 1510217) B1510217
theorem B1006985 : Blo 670310 1006985 := bstep (se 2 (by rfl) ⟨377619, by rfl⟩ : syracuseStep 1006985 = 755239) B755239
theorem B1727905 : Blo 670310 1727905 := bstep (se 2 (by rfl) ⟨647964, by rfl⟩ : syracuseStep 1727905 = 1295929) B1295929
theorem B1007339 : Blo 670310 1007339 := bstep (se 1 (by rfl) ⟨755504, by rfl⟩ : syracuseStep 1007339 = 1511009) B1511009
theorem B2416513 : Blo 670310 2416513 := bstep (se 2 (by rfl) ⟨906192, by rfl⟩ : syracuseStep 2416513 = 1812385) B1812385
theorem B1007567 : Blo 670310 1007567 := bstep (se 1 (by rfl) ⟨755675, by rfl⟩ : syracuseStep 1007567 = 1511351) B1511351
theorem B8740871 : Blo 670310 8740871 := bstep (se 1 (by rfl) ⟨6555653, by rfl⟩ : syracuseStep 8740871 = 13111307) B13111307
theorem B3399731 : Blo 670310 3399731 := bstep (se 1 (by rfl) ⟨2549798, by rfl⟩ : syracuseStep 3399731 = 5099597) B5099597
theorem B909577 : Blo 670310 909577 := bstep (se 2 (by rfl) ⟨341091, by rfl⟩ : syracuseStep 909577 = 682183) B682183
theorem B1007963 : Blo 670310 1007963 := bstep (se 1 (by rfl) ⟨755972, by rfl⟩ : syracuseStep 1007963 = 1511945) B1511945
theorem B14541281 : Blo 670310 14541281 := bstep (se 2 (by rfl) ⟨5452980, by rfl⟩ : syracuseStep 14541281 = 10905961) B10905961
theorem B1008191 : Blo 670310 1008191 := bstep (se 1 (by rfl) ⟨756143, by rfl⟩ : syracuseStep 1008191 = 1512287) B1512287
theorem B1008311 : Blo 670310 1008311 := bstep (se 1 (by rfl) ⟨756233, by rfl⟩ : syracuseStep 1008311 = 1512467) B1512467
theorem B1008539 : Blo 670310 1008539 := bstep (se 1 (by rfl) ⟨756404, by rfl⟩ : syracuseStep 1008539 = 1512809) B1512809
theorem B2876573 : Blo 670310 2876573 := bstep (se 3 (by rfl) ⟨539357, by rfl⟩ : syracuseStep 2876573 = 1078715) B1078715
theorem B2548979 : Blo 670310 2548979 := bstep (se 1 (by rfl) ⟨1911734, by rfl⟩ : syracuseStep 2548979 = 3823469) B3823469
theorem B1008935 : Blo 670310 1008935 := bstep (se 1 (by rfl) ⟨756701, by rfl⟩ : syracuseStep 1008935 = 1513403) B1513403
theorem B1009019 : Blo 670310 1009019 := bstep (se 1 (by rfl) ⟨756764, by rfl⟩ : syracuseStep 1009019 = 1513529) B1513529
theorem B2876795 : Blo 670310 2876795 := bstep (se 1 (by rfl) ⟨2157596, by rfl⟩ : syracuseStep 2876795 = 4315193) B4315193
theorem B1009145 : Blo 670310 1009145 := bstep (se 2 (by rfl) ⟨378429, by rfl⟩ : syracuseStep 1009145 = 756859) B756859
theorem B1697375 : Blo 670310 1697375 := bstep (se 1 (by rfl) ⟨1273031, by rfl⟩ : syracuseStep 1697375 = 2546063) B2546063
theorem B1009247 : Blo 670310 1009247 := bstep (se 1 (by rfl) ⟨756935, by rfl⟩ : syracuseStep 1009247 = 1513871) B1513871
theorem B3401351 : Blo 670310 3401351 := bstep (se 1 (by rfl) ⟨2551013, by rfl⟩ : syracuseStep 3401351 = 5102027) B5102027
theorem B1009463 : Blo 670310 1009463 := bstep (se 1 (by rfl) ⟨757097, by rfl⟩ : syracuseStep 1009463 = 1514195) B1514195
theorem B3237839 : Blo 670310 3237839 := bstep (se 1 (by rfl) ⟨2428379, by rfl⟩ : syracuseStep 3237839 = 4856759) B4856759
theorem B1009769 : Blo 670310 1009769 := bstep (se 2 (by rfl) ⟨378663, by rfl⟩ : syracuseStep 1009769 = 757327) B757327
theorem B1698155 : Blo 670310 1698155 := bstep (se 1 (by rfl) ⟨1273616, by rfl⟩ : syracuseStep 1698155 = 2547233) B2547233
theorem B1010087 : Blo 670310 1010087 := bstep (se 1 (by rfl) ⟨757565, by rfl⟩ : syracuseStep 1010087 = 1515131) B1515131
theorem B3238355 : Blo 670310 3238355 := bstep (se 1 (by rfl) ⟨2428766, by rfl⟩ : syracuseStep 3238355 = 4857533) B4857533
theorem B1010171 : Blo 670310 1010171 := bstep (se 1 (by rfl) ⟨757628, by rfl⟩ : syracuseStep 1010171 = 1515257) B1515257
theorem B39414275 : Blo 670310 39414275 := bstep (se 1 (by rfl) ⟨29560706, by rfl⟩ : syracuseStep 39414275 = 59121413) B59121413
theorem B29878793 : Blo 670310 29878793 := bstep (se 2 (by rfl) ⟨11204547, by rfl⟩ : syracuseStep 29878793 = 22409095) B22409095
theorem B1698367 : Blo 670310 1698367 := bstep (se 1 (by rfl) ⟨1273775, by rfl⟩ : syracuseStep 1698367 = 2547551) B2547551
theorem B1010297 : Blo 670310 1010297 := bstep (se 2 (by rfl) ⟨378861, by rfl⟩ : syracuseStep 1010297 = 757723) B757723
theorem B1698479 : Blo 670310 1698479 := bstep (se 1 (by rfl) ⟨1273859, by rfl⟩ : syracuseStep 1698479 = 2547719) B2547719
theorem B1010351 : Blo 670310 1010351 := bstep (se 1 (by rfl) ⟨757763, by rfl⟩ : syracuseStep 1010351 = 1515527) B1515527
theorem B2550467 : Blo 670310 2550467 := bstep (se 1 (by rfl) ⟨1912850, by rfl⟩ : syracuseStep 2550467 = 3825701) B3825701
theorem B1010399 : Blo 670310 1010399 := bstep (se 1 (by rfl) ⟨757799, by rfl⟩ : syracuseStep 1010399 = 1515599) B1515599
theorem B12282637 : Blo 670310 12282637 := bstep (se 3 (by rfl) ⟨2302994, by rfl⟩ : syracuseStep 12282637 = 4605989) B4605989
theorem B3632015 : Blo 670310 3632015 := bstep (se 1 (by rfl) ⟨2724011, by rfl⟩ : syracuseStep 3632015 = 5448023) B5448023
theorem B1010663 : Blo 670310 1010663 := bstep (se 1 (by rfl) ⟨757997, by rfl⟩ : syracuseStep 1010663 = 1515995) B1515995
theorem B1698803 : Blo 670310 1698803 := bstep (se 1 (by rfl) ⟨1274102, by rfl⟩ : syracuseStep 1698803 = 2548205) B2548205
theorem B2550923 : Blo 670310 2550923 := bstep (se 1 (by rfl) ⟨1913192, by rfl⟩ : syracuseStep 2550923 = 3826385) B3826385
theorem B1699015 : Blo 670310 1699015 := bstep (se 1 (by rfl) ⟨1274261, by rfl⟩ : syracuseStep 1699015 = 2548523) B2548523
theorem B3402971 : Blo 670310 3402971 := bstep (se 1 (by rfl) ⟨2552228, by rfl⟩ : syracuseStep 3402971 = 5104457) B5104457
theorem B1010921 : Blo 670310 1010921 := bstep (se 2 (by rfl) ⟨379095, by rfl⟩ : syracuseStep 1010921 = 758191) B758191
theorem B1010975 : Blo 670310 1010975 := bstep (se 1 (by rfl) ⟨758231, by rfl⟩ : syracuseStep 1010975 = 1516463) B1516463
theorem B1011143 : Blo 670310 1011143 := bstep (se 1 (by rfl) ⟨758357, by rfl⟩ : syracuseStep 1011143 = 1516715) B1516715
theorem B11464253 : Blo 670310 11464253 := bstep (se 3 (by rfl) ⟨2149547, by rfl⟩ : syracuseStep 11464253 = 4299095) B4299095
theorem B3239585 : Blo 670310 3239585 := bstep (se 2 (by rfl) ⟨1214844, by rfl⟩ : syracuseStep 3239585 = 2429689) B2429689
theorem B5107373 : Blo 670310 5107373 := bstep (se 3 (by rfl) ⟨957632, by rfl⟩ : syracuseStep 5107373 = 1915265) B1915265
theorem B3239837 : Blo 670310 3239837 := bstep (se 3 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 3239837 = 1214939) B1214939
theorem B3404105 : Blo 670310 3404105 := bstep (se 2 (by rfl) ⟨1276539, by rfl⟩ : syracuseStep 3404105 = 2553079) B2553079
theorem B1700423 : Blo 670310 1700423 := bstep (se 1 (by rfl) ⟨1275317, by rfl⟩ : syracuseStep 1700423 = 2550635) B2550635
theorem B1700473 : Blo 670310 1700473 := bstep (se 2 (by rfl) ⟨637677, by rfl⟩ : syracuseStep 1700473 = 1275355) B1275355
theorem B5108345 : Blo 670310 5108345 := bstep (se 2 (by rfl) ⟨1915629, by rfl⟩ : syracuseStep 5108345 = 3831259) B3831259
theorem B7271639 : Blo 670310 7271639 := bstep (se 1 (by rfl) ⟨5453729, by rfl⟩ : syracuseStep 7271639 = 10907459) B10907459
theorem B2553065 : Blo 670310 2553065 := bstep (se 2 (by rfl) ⟨957399, by rfl⟩ : syracuseStep 2553065 = 1914799) B1914799
theorem B1996019 : Blo 670310 1996019 := bstep (se 1 (by rfl) ⟨1497014, by rfl⟩ : syracuseStep 1996019 = 2994029) B2994029
theorem B8189207 : Blo 670310 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B3405401 : Blo 670310 3405401 := bstep (se 2 (by rfl) ⟨1277025, by rfl⟩ : syracuseStep 3405401 = 2554051) B2554051
theorem B11499245 : Blo 670310 11499245 := bstep (se 3 (by rfl) ⟨2156108, by rfl⟩ : syracuseStep 11499245 = 4312217) B4312217
theorem B1275689 : Blo 670310 1275689 := bstep (se 2 (by rfl) ⟨478383, by rfl⟩ : syracuseStep 1275689 = 956767) B956767
theorem B5109803 : Blo 670310 5109803 := bstep (se 1 (by rfl) ⟨3832352, by rfl⟩ : syracuseStep 5109803 = 7664705) B7664705
theorem B1079401 : Blo 670310 1079401 := bstep (se 2 (by rfl) ⟨404775, by rfl⟩ : syracuseStep 1079401 = 809551) B809551
theorem B850267 : Blo 670310 850267 := bstep (se 1 (by rfl) ⟨637700, by rfl⟩ : syracuseStep 850267 = 1275401) B1275401
theorem B1702235 : Blo 670310 1702235 := bstep (se 1 (by rfl) ⟨1276676, by rfl⟩ : syracuseStep 1702235 = 2553353) B2553353
theorem B1702255 : Blo 670310 1702255 := bstep (se 1 (by rfl) ⟨1276691, by rfl⟩ : syracuseStep 1702255 = 2553383) B2553383
theorem B1276327 : Blo 670310 1276327 := bstep (se 1 (by rfl) ⟨957245, by rfl⟩ : syracuseStep 1276327 = 1914491) B1914491
theorem B1276411 : Blo 670310 1276411 := bstep (se 1 (by rfl) ⟨957308, by rfl⟩ : syracuseStep 1276411 = 1914617) B1914617
theorem B850495 : Blo 670310 850495 := bstep (se 1 (by rfl) ⟨637871, by rfl⟩ : syracuseStep 850495 = 1275743) B1275743
theorem B1637275 : Blo 670310 1637275 := bstep (se 1 (by rfl) ⟨1227956, by rfl⟩ : syracuseStep 1637275 = 2455913) B2455913
theorem B719771 : Blo 670310 719771 := bstep (se 1 (by rfl) ⟨539828, by rfl⟩ : syracuseStep 719771 = 1079657) B1079657
theorem B1702903 : Blo 670310 1702903 := bstep (se 1 (by rfl) ⟨1277177, by rfl⟩ : syracuseStep 1702903 = 2554355) B2554355
theorem B1277147 : Blo 670310 1277147 := bstep (se 1 (by rfl) ⟨957860, by rfl⟩ : syracuseStep 1277147 = 1915721) B1915721
theorem B851239 : Blo 670310 851239 := bstep (se 1 (by rfl) ⟨638429, by rfl⟩ : syracuseStep 851239 = 1276859) B1276859
theorem B1703207 : Blo 670310 1703207 := bstep (se 1 (by rfl) ⟨1277405, by rfl⟩ : syracuseStep 1703207 = 2554811) B2554811
theorem B1277383 : Blo 670310 1277383 := bstep (se 1 (by rfl) ⟨958037, by rfl⟩ : syracuseStep 1277383 = 1916075) B1916075
theorem B9665993 : Blo 670310 9665993 := bstep (se 2 (by rfl) ⟨3624747, by rfl⟩ : syracuseStep 9665993 = 7249495) B7249495
theorem B851563 : Blo 670310 851563 := bstep (se 1 (by rfl) ⟨638672, by rfl⟩ : syracuseStep 851563 = 1277345) B1277345
theorem B7274099 : Blo 670310 7274099 := bstep (se 1 (by rfl) ⟨5455574, by rfl⟩ : syracuseStep 7274099 = 10911149) B10911149
theorem B851791 : Blo 670310 851791 := bstep (se 1 (by rfl) ⟨638843, by rfl⟩ : syracuseStep 851791 = 1277687) B1277687
theorem B1212769 : Blo 670310 1212769 := bstep (se 2 (by rfl) ⟨454788, by rfl⟩ : syracuseStep 1212769 = 909577) B909577
theorem B6128179 : Blo 670310 6128179 := bstep (se 1 (by rfl) ⟨4596134, by rfl⟩ : syracuseStep 6128179 = 9192269) B9192269
theorem B1213231 : Blo 670310 1213231 := bstep (se 1 (by rfl) ⟨909923, by rfl⟩ : syracuseStep 1213231 = 1819847) B1819847
theorem B5112719 : Blo 670310 5112719 := bstep (se 1 (by rfl) ⟨3834539, by rfl⟩ : syracuseStep 5112719 = 7669079) B7669079
theorem B5735681 : Blo 670310 5735681 := bstep (se 2 (by rfl) ⟨2150880, by rfl⟩ : syracuseStep 5735681 = 4301761) B4301761
theorem B10880531 : Blo 670310 10880531 := bstep (se 1 (by rfl) ⟨8160398, by rfl⟩ : syracuseStep 10880531 = 16320797) B16320797
theorem B1214023 : Blo 670310 1214023 := bstep (se 1 (by rfl) ⟨910517, by rfl⟩ : syracuseStep 1214023 = 1821035) B1821035
theorem B1508975 : Blo 670310 1508975 := bstep (se 1 (by rfl) ⟨1131731, by rfl⟩ : syracuseStep 1508975 = 2263463) B2263463
theorem B755311 : Blo 670310 755311 := bstep (se 1 (by rfl) ⟨566483, by rfl⟩ : syracuseStep 755311 = 1132967) B1132967
theorem B2426489 : Blo 670310 2426489 := bstep (se 2 (by rfl) ⟨909933, by rfl⟩ : syracuseStep 2426489 = 1819867) B1819867
theorem B1509083 : Blo 670310 1509083 := bstep (se 1 (by rfl) ⟨1131812, by rfl⟩ : syracuseStep 1509083 = 2263625) B2263625
theorem B755419 : Blo 670310 755419 := bstep (se 1 (by rfl) ⟨566564, by rfl⟩ : syracuseStep 755419 = 1133129) B1133129
theorem B2262815 : Blo 670310 2262815 := bstep (se 1 (by rfl) ⟨1697111, by rfl⟩ : syracuseStep 2262815 = 3394223) B3394223
theorem B1279775 : Blo 670310 1279775 := bstep (se 1 (by rfl) ⟨959831, by rfl⟩ : syracuseStep 1279775 = 1919663) B1919663
theorem B2557757 : Blo 670310 2557757 := bstep (se 3 (by rfl) ⟨479579, by rfl⟩ : syracuseStep 2557757 = 959159) B959159
theorem B2263031 : Blo 670310 2263031 := bstep (se 1 (by rfl) ⟨1697273, by rfl⟩ : syracuseStep 2263031 = 3394547) B3394547
theorem B4852169 : Blo 670310 4852169 := bstep (se 2 (by rfl) ⟨1819563, by rfl⟩ : syracuseStep 4852169 = 3639127) B3639127
theorem B1510199 : Blo 670310 1510199 := bstep (se 1 (by rfl) ⟨1132649, by rfl⟩ : syracuseStep 1510199 = 2265299) B2265299
theorem B2263895 : Blo 670310 2263895 := bstep (se 1 (by rfl) ⟨1697921, by rfl⟩ : syracuseStep 2263895 = 3395843) B3395843
theorem B756571 : Blo 670310 756571 := bstep (se 1 (by rfl) ⟨567428, by rfl⟩ : syracuseStep 756571 = 1134857) B1134857
theorem B5737391 : Blo 670310 5737391 := bstep (se 1 (by rfl) ⟨4303043, by rfl⟩ : syracuseStep 5737391 = 8606087) B8606087
theorem B1510379 : Blo 670310 1510379 := bstep (se 1 (by rfl) ⟨1132784, by rfl⟩ : syracuseStep 1510379 = 2265569) B2265569
theorem B4295713 : Blo 670310 4295713 := bstep (se 2 (by rfl) ⟨1610892, by rfl⟩ : syracuseStep 4295713 = 3221785) B3221785
theorem B2264111 : Blo 670310 2264111 := bstep (se 1 (by rfl) ⟨1698083, by rfl⟩ : syracuseStep 2264111 = 3396167) B3396167
theorem B10325069 : Blo 670310 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B2264489 : Blo 670310 2264489 := bstep (se 2 (by rfl) ⟨849183, by rfl⟩ : syracuseStep 2264489 = 1698367) B1698367
theorem B7638461 : Blo 670310 7638461 := bstep (se 3 (by rfl) ⟨1432211, by rfl⟩ : syracuseStep 7638461 = 2864423) B2864423
theorem B5738141 : Blo 670310 5738141 := bstep (se 3 (by rfl) ⟨1075901, by rfl⟩ : syracuseStep 5738141 = 2151803) B2151803
theorem B1511207 : Blo 670310 1511207 := bstep (se 1 (by rfl) ⟨1133405, by rfl⟩ : syracuseStep 1511207 = 2266811) B2266811
theorem B757543 : Blo 670310 757543 := bstep (se 1 (by rfl) ⟨568157, by rfl⟩ : syracuseStep 757543 = 1136315) B1136315
theorem B2264975 : Blo 670310 2264975 := bstep (se 1 (by rfl) ⟨1698731, by rfl⟩ : syracuseStep 2264975 = 3397463) B3397463
theorem B1019803 : Blo 670310 1019803 := bstep (se 1 (by rfl) ⟨764852, by rfl⟩ : syracuseStep 1019803 = 1529705) B1529705
theorem B7671995 : Blo 670310 7671995 := bstep (se 1 (by rfl) ⟨5753996, by rfl⟩ : syracuseStep 7671995 = 11507993) B11507993
theorem B2560187 : Blo 670310 2560187 := bstep (se 1 (by rfl) ⟨1920140, by rfl⟩ : syracuseStep 2560187 = 3840281) B3840281
theorem B3641597 : Blo 670310 3641597 := bstep (se 3 (by rfl) ⟨682799, by rfl⟩ : syracuseStep 3641597 = 1365599) B1365599
theorem B2265353 : Blo 670310 2265353 := bstep (se 2 (by rfl) ⟨849507, by rfl⟩ : syracuseStep 2265353 = 1699015) B1699015
theorem B66130499 : Blo 670310 66130499 := bstep (se 1 (by rfl) ⟨49597874, by rfl⟩ : syracuseStep 66130499 = 99195749) B99195749
theorem B149590799 : Blo 670310 149590799 := bstep (se 1 (by rfl) ⟨112193099, by rfl⟩ : syracuseStep 149590799 = 224386199) B224386199
theorem B1512233 : Blo 670310 1512233 := bstep (se 2 (by rfl) ⟨567087, by rfl⟩ : syracuseStep 1512233 = 1134175) B1134175
theorem B3937085 : Blo 670310 3937085 := bstep (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) B1476407
theorem B1512503 : Blo 670310 1512503 := bstep (se 1 (by rfl) ⟨1134377, by rfl⟩ : syracuseStep 1512503 = 2268755) B2268755
theorem B1512521 : Blo 670310 1512521 := bstep (se 2 (by rfl) ⟨567195, by rfl⟩ : syracuseStep 1512521 = 1134391) B1134391
theorem B3413339 : Blo 670310 3413339 := bstep (se 1 (by rfl) ⟨2560004, by rfl⟩ : syracuseStep 3413339 = 5120009) B5120009
theorem B2266487 : Blo 670310 2266487 := bstep (se 1 (by rfl) ⟨1699865, by rfl⟩ : syracuseStep 2266487 = 3399731) B3399731
theorem B3643193 : Blo 670310 3643193 := bstep (se 2 (by rfl) ⟨1366197, by rfl⟩ : syracuseStep 3643193 = 2732395) B2732395
theorem B7739459 : Blo 670310 7739459 := bstep (se 1 (by rfl) ⟨5804594, by rfl⟩ : syracuseStep 7739459 = 11609189) B11609189
theorem B2267297 : Blo 670310 2267297 := bstep (se 2 (by rfl) ⟨850236, by rfl⟩ : syracuseStep 2267297 = 1700473) B1700473
theorem B7739725 : Blo 670310 7739725 := bstep (se 3 (by rfl) ⟨1451198, by rfl⟩ : syracuseStep 7739725 = 2902397) B2902397
theorem B2267567 : Blo 670310 2267567 := bstep (se 1 (by rfl) ⟨1700675, by rfl⟩ : syracuseStep 2267567 = 3401351) B3401351
theorem B1514447 : Blo 670310 1514447 := bstep (se 1 (by rfl) ⟨1135835, by rfl⟩ : syracuseStep 1514447 = 2271671) B2271671
theorem B1514465 : Blo 670310 1514465 := bstep (se 2 (by rfl) ⟨567924, by rfl⟩ : syracuseStep 1514465 = 1135849) B1135849
theorem B1514537 : Blo 670310 1514537 := bstep (se 2 (by rfl) ⟨567951, by rfl⟩ : syracuseStep 1514537 = 1135903) B1135903
theorem B2268647 : Blo 670310 2268647 := bstep (se 1 (by rfl) ⟨1701485, by rfl⟩ : syracuseStep 2268647 = 3402971) B3402971
theorem B7642835 : Blo 670310 7642835 := bstep (se 1 (by rfl) ⟨5732126, by rfl⟩ : syracuseStep 7642835 = 11464253) B11464253
theorem B2269403 : Blo 670310 2269403 := bstep (se 1 (by rfl) ⟨1702052, by rfl⟩ : syracuseStep 2269403 = 3404105) B3404105
theorem B1908967 : Blo 670310 1908967 := bstep (se 1 (by rfl) ⟨1431725, by rfl⟩ : syracuseStep 1908967 = 2863451) B2863451
theorem B2269673 : Blo 670310 2269673 := bstep (se 2 (by rfl) ⟨851127, by rfl⟩ : syracuseStep 2269673 = 1702255) B1702255
theorem B2040383 : Blo 670310 2040383 := bstep (se 1 (by rfl) ⟨1530287, by rfl⟩ : syracuseStep 2040383 = 3060575) B3060575
theorem B1516499 : Blo 670310 1516499 := bstep (se 1 (by rfl) ⟨1137374, by rfl⟩ : syracuseStep 1516499 = 2274749) B2274749
theorem B2270267 : Blo 670310 2270267 := bstep (se 1 (by rfl) ⟨1702700, by rfl⟩ : syracuseStep 2270267 = 3405401) B3405401
theorem B1516751 : Blo 670310 1516751 := bstep (se 1 (by rfl) ⟨1137563, by rfl⟩ : syracuseStep 1516751 = 2275127) B2275127
theorem B2270537 : Blo 670310 2270537 := bstep (se 2 (by rfl) ⟨851451, by rfl⟩ : syracuseStep 2270537 = 1702903) B1702903
theorem B1517075 : Blo 670310 1517075 := bstep (se 1 (by rfl) ⟨1137806, by rfl⟩ : syracuseStep 1517075 = 2275613) B2275613
theorem B2303873 : Blo 670310 2303873 := bstep (se 2 (by rfl) ⟨863952, by rfl⟩ : syracuseStep 2303873 = 1727905) B1727905
theorem B7677827 : Blo 670310 7677827 := bstep (se 1 (by rfl) ⟨5758370, by rfl⟩ : syracuseStep 7677827 = 11516741) B11516741
theorem B2304295 : Blo 670310 2304295 := bstep (se 1 (by rfl) ⟨1728221, by rfl⟩ : syracuseStep 2304295 = 3456443) B3456443
theorem B3222017 : Blo 670310 3222017 := bstep (se 2 (by rfl) ⟨1208256, by rfl⟩ : syracuseStep 3222017 = 2416513) B2416513
theorem B1912031 : Blo 670310 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B2043215 : Blo 670310 2043215 := bstep (se 1 (by rfl) ⟨1532411, by rfl⟩ : syracuseStep 2043215 = 3064823) B3064823
theorem B1617583 : Blo 670310 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B9711373 : Blo 670310 9711373 := bstep (se 3 (by rfl) ⟨1820882, by rfl⟩ : syracuseStep 9711373 = 3641765) B3641765
theorem B2273129 : Blo 670310 2273129 := bstep (se 2 (by rfl) ⟨852423, by rfl⟩ : syracuseStep 2273129 = 1704847) B1704847
theorem B2765123 : Blo 670310 2765123 := bstep (se 1 (by rfl) ⟨2073842, by rfl⟩ : syracuseStep 2765123 = 4147685) B4147685
theorem B1913215 : Blo 670310 1913215 := bstep (se 1 (by rfl) ⟨1434911, by rfl⟩ : syracuseStep 1913215 = 2869823) B2869823
theorem B1618535 : Blo 670310 1618535 := bstep (se 1 (by rfl) ⟨1213901, by rfl⟩ : syracuseStep 1618535 = 2427803) B2427803
theorem B2274479 : Blo 670310 2274479 := bstep (se 1 (by rfl) ⟨1705859, by rfl⟩ : syracuseStep 2274479 = 3411719) B3411719
theorem B7648667 : Blo 670310 7648667 := bstep (se 1 (by rfl) ⟨5736500, by rfl⟩ : syracuseStep 7648667 = 11473001) B11473001
theorem B2733887 : Blo 670310 2733887 := bstep (se 1 (by rfl) ⟨2050415, by rfl⟩ : syracuseStep 2733887 = 4100831) B4100831
theorem B2865091 : Blo 670310 2865091 := bstep (se 1 (by rfl) ⟨2148818, by rfl⟩ : syracuseStep 2865091 = 4297637) B4297637
theorem B1619927 : Blo 670310 1619927 := bstep (se 1 (by rfl) ⟨1214945, by rfl⟩ : syracuseStep 1619927 = 2429891) B2429891
theorem B3061903 : Blo 670310 3061903 := bstep (se 1 (by rfl) ⟨2296427, by rfl⟩ : syracuseStep 3061903 = 4592855) B4592855
theorem B2865415 : Blo 670310 2865415 := bstep (se 1 (by rfl) ⟨2149061, by rfl⟩ : syracuseStep 2865415 = 4298123) B4298123
theorem B7879027 : Blo 670310 7879027 := bstep (se 1 (by rfl) ⟨5909270, by rfl⟩ : syracuseStep 7879027 = 11818541) B11818541
theorem B670555 : Blo 670310 670555 := bstep (se 1 (by rfl) ⟨502916, by rfl⟩ : syracuseStep 670555 = 1005833) B1005833
theorem B670623 : Blo 670310 670623 := bstep (se 1 (by rfl) ⟨502967, by rfl⟩ : syracuseStep 670623 = 1005935) B1005935
theorem B670767 : Blo 670310 670767 := bstep (se 1 (by rfl) ⟨503075, by rfl⟩ : syracuseStep 670767 = 1006151) B1006151
theorem B670791 : Blo 670310 670791 := bstep (se 1 (by rfl) ⟨503093, by rfl⟩ : syracuseStep 670791 = 1006187) B1006187
theorem B6143147 : Blo 670310 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B670943 : Blo 670310 670943 := bstep (se 1 (by rfl) ⟨503207, by rfl⟩ : syracuseStep 670943 = 1006415) B1006415
theorem B671207 : Blo 670310 671207 := bstep (se 1 (by rfl) ⟨503405, by rfl⟩ : syracuseStep 671207 = 1006811) B1006811
theorem B671323 : Blo 670310 671323 := bstep (se 1 (by rfl) ⟨503492, by rfl⟩ : syracuseStep 671323 = 1006985) B1006985
theorem B671559 : Blo 670310 671559 := bstep (se 1 (by rfl) ⟨503669, by rfl⟩ : syracuseStep 671559 = 1007339) B1007339
theorem B671711 : Blo 670310 671711 := bstep (se 1 (by rfl) ⟨503783, by rfl⟩ : syracuseStep 671711 = 1007567) B1007567
theorem B671975 : Blo 670310 671975 := bstep (se 1 (by rfl) ⟨503981, by rfl⟩ : syracuseStep 671975 = 1007963) B1007963
theorem B672127 : Blo 670310 672127 := bstep (se 1 (by rfl) ⟨504095, by rfl⟩ : syracuseStep 672127 = 1008191) B1008191
theorem B672207 : Blo 670310 672207 := bstep (se 1 (by rfl) ⟨504155, by rfl⟩ : syracuseStep 672207 = 1008311) B1008311
theorem B672359 : Blo 670310 672359 := bstep (se 1 (by rfl) ⟨504269, by rfl⟩ : syracuseStep 672359 = 1008539) B1008539
theorem B2867977 : Blo 670310 2867977 := bstep (se 2 (by rfl) ⟨1075491, by rfl⟩ : syracuseStep 2867977 = 2150983) B2150983
theorem B1917715 : Blo 670310 1917715 := bstep (se 1 (by rfl) ⟨1438286, by rfl⟩ : syracuseStep 1917715 = 2876573) B2876573
theorem B672623 : Blo 670310 672623 := bstep (se 1 (by rfl) ⟨504467, by rfl⟩ : syracuseStep 672623 = 1008935) B1008935
theorem B672679 : Blo 670310 672679 := bstep (se 1 (by rfl) ⟨504509, by rfl⟩ : syracuseStep 672679 = 1009019) B1009019
theorem B1917863 : Blo 670310 1917863 := bstep (se 1 (by rfl) ⟨1438397, by rfl⟩ : syracuseStep 1917863 = 2876795) B2876795
theorem B672763 : Blo 670310 672763 := bstep (se 1 (by rfl) ⟨504572, by rfl⟩ : syracuseStep 672763 = 1009145) B1009145
theorem B1131583 : Blo 670310 1131583 := bstep (se 1 (by rfl) ⟨848687, by rfl⟩ : syracuseStep 1131583 = 1697375) B1697375
theorem B672831 : Blo 670310 672831 := bstep (se 1 (by rfl) ⟨504623, by rfl⟩ : syracuseStep 672831 = 1009247) B1009247
theorem B672975 : Blo 670310 672975 := bstep (se 1 (by rfl) ⟨504731, by rfl⟩ : syracuseStep 672975 = 1009463) B1009463
theorem B23250199 : Blo 670310 23250199 := bstep (se 1 (by rfl) ⟨17437649, by rfl⟩ : syracuseStep 23250199 = 34875299) B34875299
theorem B673179 : Blo 670310 673179 := bstep (se 1 (by rfl) ⟨504884, by rfl⟩ : syracuseStep 673179 = 1009769) B1009769
theorem B2147755 : Blo 670310 2147755 := bstep (se 1 (by rfl) ⟨1610816, by rfl⟩ : syracuseStep 2147755 = 3221633) B3221633
theorem B1132103 : Blo 670310 1132103 := bstep (se 1 (by rfl) ⟨849077, by rfl⟩ : syracuseStep 1132103 = 1698155) B1698155
theorem B673391 : Blo 670310 673391 := bstep (se 1 (by rfl) ⟨505043, by rfl⟩ : syracuseStep 673391 = 1010087) B1010087
theorem B673447 : Blo 670310 673447 := bstep (se 1 (by rfl) ⟨505085, by rfl⟩ : syracuseStep 673447 = 1010171) B1010171
theorem B673531 : Blo 670310 673531 := bstep (se 1 (by rfl) ⟨505148, by rfl⟩ : syracuseStep 673531 = 1010297) B1010297
theorem B1132319 : Blo 670310 1132319 := bstep (se 1 (by rfl) ⟨849239, by rfl⟩ : syracuseStep 1132319 = 1698479) B1698479
theorem B673567 : Blo 670310 673567 := bstep (se 1 (by rfl) ⟨505175, by rfl⟩ : syracuseStep 673567 = 1010351) B1010351
theorem B673599 : Blo 670310 673599 := bstep (se 1 (by rfl) ⟨505199, by rfl⟩ : syracuseStep 673599 = 1010399) B1010399
theorem B4900837 : Blo 670310 4900837 := bstep (se 4 (by rfl) ⟨459453, by rfl⟩ : syracuseStep 4900837 = 918907) B918907
theorem B673775 : Blo 670310 673775 := bstep (se 1 (by rfl) ⟨505331, by rfl⟩ : syracuseStep 673775 = 1010663) B1010663
theorem B1132535 : Blo 670310 1132535 := bstep (se 1 (by rfl) ⟨849401, by rfl⟩ : syracuseStep 1132535 = 1698803) B1698803
theorem B4835447 : Blo 670310 4835447 := bstep (se 1 (by rfl) ⟨3626585, by rfl⟩ : syracuseStep 4835447 = 7253171) B7253171
theorem B673947 : Blo 670310 673947 := bstep (se 1 (by rfl) ⟨505460, by rfl⟩ : syracuseStep 673947 = 1010921) B1010921
theorem B673983 : Blo 670310 673983 := bstep (se 1 (by rfl) ⟨505487, by rfl⟩ : syracuseStep 673983 = 1010975) B1010975
theorem B674095 : Blo 670310 674095 := bstep (se 1 (by rfl) ⟨505571, by rfl⟩ : syracuseStep 674095 = 1011143) B1011143
theorem B1919389 : Blo 670310 1919389 := bstep (se 3 (by rfl) ⟨359885, by rfl⟩ : syracuseStep 1919389 = 719771) B719771
theorem B1133615 : Blo 670310 1133615 := bstep (se 1 (by rfl) ⟨850211, by rfl⟩ : syracuseStep 1133615 = 1700423) B1700423
theorem B1133689 : Blo 670310 1133689 := bstep (se 2 (by rfl) ⟨425133, by rfl⟩ : syracuseStep 1133689 = 850267) B850267
theorem B1821977 : Blo 670310 1821977 := bstep (se 2 (by rfl) ⟨683241, by rfl⟩ : syracuseStep 1821977 = 1366483) B1366483
theorem B4312399 : Blo 670310 4312399 := bstep (se 1 (by rfl) ⟨3234299, by rfl⟩ : syracuseStep 4312399 = 6468599) B6468599
theorem B1133993 : Blo 670310 1133993 := bstep (se 2 (by rfl) ⟨425247, by rfl⟩ : syracuseStep 1133993 = 850495) B850495
theorem B2870711 : Blo 670310 2870711 := bstep (se 1 (by rfl) ⟨2153033, by rfl⟩ : syracuseStep 2870711 = 4306067) B4306067
theorem B1330679 : Blo 670310 1330679 := bstep (se 1 (by rfl) ⟨998009, by rfl⟩ : syracuseStep 1330679 = 1996019) B1996019
theorem B5459471 : Blo 670310 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B2871121 : Blo 670310 2871121 := bstep (se 2 (by rfl) ⟨1076670, by rfl⟩ : syracuseStep 2871121 = 2153341) B2153341
theorem B2183033 : Blo 670310 2183033 := bstep (se 2 (by rfl) ⟨818637, by rfl⟩ : syracuseStep 2183033 = 1637275) B1637275
theorem B1134823 : Blo 670310 1134823 := bstep (se 1 (by rfl) ⟨851117, by rfl⟩ : syracuseStep 1134823 = 1702235) B1702235
theorem B1134985 : Blo 670310 1134985 := bstep (se 2 (by rfl) ⟨425619, by rfl⟩ : syracuseStep 1134985 = 851239) B851239
theorem B3822329 : Blo 670310 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B1135417 : Blo 670310 1135417 := bstep (se 2 (by rfl) ⟨425781, by rfl⟩ : syracuseStep 1135417 = 851563) B851563
theorem B2904893 : Blo 670310 2904893 := bstep (se 3 (by rfl) ⟨544667, by rfl⟩ : syracuseStep 2904893 = 1089335) B1089335
theorem B1135471 : Blo 670310 1135471 := bstep (se 1 (by rfl) ⟨851603, by rfl⟩ : syracuseStep 1135471 = 1703207) B1703207
theorem B6443995 : Blo 670310 6443995 := bstep (se 1 (by rfl) ⟨4832996, by rfl⟩ : syracuseStep 6443995 = 9665993) B9665993
theorem B4314167 : Blo 670310 4314167 := bstep (se 1 (by rfl) ⟨3235625, by rfl⟩ : syracuseStep 4314167 = 6471251) B6471251
theorem B1135721 : Blo 670310 1135721 := bstep (se 2 (by rfl) ⟨425895, by rfl⟩ : syracuseStep 1135721 = 851791) B851791
theorem B1725851 : Blo 670310 1725851 := bstep (se 1 (by rfl) ⟨1294388, by rfl⟩ : syracuseStep 1725851 = 2588777) B2588777
theorem B2545121 : Blo 670310 2545121 := bstep (se 2 (by rfl) ⟨954420, by rfl⟩ : syracuseStep 2545121 = 1908841) B1908841
theorem B5461613 : Blo 670310 5461613 := bstep (se 3 (by rfl) ⟨1024052, by rfl⟩ : syracuseStep 5461613 = 2048105) B2048105
theorem B53106353 : Blo 670310 53106353 := bstep (se 2 (by rfl) ⟨19914882, by rfl⟩ : syracuseStep 53106353 = 39829765) B39829765
theorem B3889079 : Blo 670310 3889079 := bstep (se 1 (by rfl) ⟨2916809, by rfl⟩ : syracuseStep 3889079 = 5833619) B5833619
theorem B1005551 : Blo 670310 1005551 := bstep (se 1 (by rfl) ⟨754163, by rfl⟩ : syracuseStep 1005551 = 1508327) B1508327
theorem B3692639 : Blo 670310 3692639 := bstep (se 1 (by rfl) ⟨2769479, by rfl⟩ : syracuseStep 3692639 = 5538959) B5538959
theorem B3397787 : Blo 670310 3397787 := bstep (se 1 (by rfl) ⟨2548340, by rfl⟩ : syracuseStep 3397787 = 5096681) B5096681
theorem B1431751 : Blo 670310 1431751 := bstep (se 1 (by rfl) ⟨1073813, by rfl⟩ : syracuseStep 1431751 = 2147627) B2147627
theorem B1005803 : Blo 670310 1005803 := bstep (se 1 (by rfl) ⟨754352, by rfl⟩ : syracuseStep 1005803 = 1508705) B1508705
theorem B1136875 : Blo 670310 1136875 := bstep (se 1 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 1136875 = 1705313) B1705313
theorem B1005863 : Blo 670310 1005863 := bstep (se 1 (by rfl) ⟨754397, by rfl⟩ : syracuseStep 1005863 = 1508795) B1508795
theorem B1431931 : Blo 670310 1431931 := bstep (se 1 (by rfl) ⟨1073948, by rfl⟩ : syracuseStep 1431931 = 2147897) B2147897
theorem B1005947 : Blo 670310 1005947 := bstep (se 1 (by rfl) ⟨754460, by rfl⟩ : syracuseStep 1005947 = 1508921) B1508921
theorem B1137179 : Blo 670310 1137179 := bstep (se 1 (by rfl) ⟨852884, by rfl⟩ : syracuseStep 1137179 = 1705769) B1705769
theorem B1006217 : Blo 670310 1006217 := bstep (se 2 (by rfl) ⟨377331, by rfl⟩ : syracuseStep 1006217 = 754663) B754663
theorem B4086409 : Blo 670310 4086409 := bstep (se 2 (by rfl) ⟨1532403, by rfl⟩ : syracuseStep 4086409 = 3064807) B3064807
theorem B1006391 : Blo 670310 1006391 := bstep (se 1 (by rfl) ⟨754793, by rfl⟩ : syracuseStep 1006391 = 1509587) B1509587
theorem B1006427 : Blo 670310 1006427 := bstep (se 1 (by rfl) ⟨754820, by rfl⟩ : syracuseStep 1006427 = 1509641) B1509641
theorem B1006571 : Blo 670310 1006571 := bstep (se 1 (by rfl) ⟨754928, by rfl⟩ : syracuseStep 1006571 = 1509857) B1509857
theorem B4906099 : Blo 670310 4906099 := bstep (se 1 (by rfl) ⟨3679574, by rfl⟩ : syracuseStep 4906099 = 7359149) B7359149
theorem B1006775 : Blo 670310 1006775 := bstep (se 1 (by rfl) ⟨755081, by rfl⟩ : syracuseStep 1006775 = 1510163) B1510163
theorem B1137847 : Blo 670310 1137847 := bstep (se 1 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 1137847 = 1706771) B1706771
theorem B1007015 : Blo 670310 1007015 := bstep (se 1 (by rfl) ⟨755261, by rfl⟩ : syracuseStep 1007015 = 1510523) B1510523
theorem B1007099 : Blo 670310 1007099 := bstep (se 1 (by rfl) ⟨755324, by rfl⟩ : syracuseStep 1007099 = 1510649) B1510649
theorem B1007195 : Blo 670310 1007195 := bstep (se 1 (by rfl) ⟨755396, by rfl⟩ : syracuseStep 1007195 = 1510793) B1510793
theorem B38854241 : Blo 670310 38854241 := bstep (se 2 (by rfl) ⟨14570340, by rfl⟩ : syracuseStep 38854241 = 29140681) B29140681
theorem B1007279 : Blo 670310 1007279 := bstep (se 1 (by rfl) ⟨755459, by rfl⟩ : syracuseStep 1007279 = 1510919) B1510919
theorem B1007399 : Blo 670310 1007399 := bstep (se 1 (by rfl) ⟨755549, by rfl⟩ : syracuseStep 1007399 = 1511099) B1511099
theorem B1007483 : Blo 670310 1007483 := bstep (se 1 (by rfl) ⟨755612, by rfl⟩ : syracuseStep 1007483 = 1511225) B1511225
theorem B1433639 : Blo 670310 1433639 := bstep (se 1 (by rfl) ⟨1075229, by rfl⟩ : syracuseStep 1433639 = 2150459) B2150459
theorem B1007903 : Blo 670310 1007903 := bstep (se 1 (by rfl) ⟨755927, by rfl⟩ : syracuseStep 1007903 = 1511855) B1511855
theorem B1007927 : Blo 670310 1007927 := bstep (se 1 (by rfl) ⟨755945, by rfl⟩ : syracuseStep 1007927 = 1511891) B1511891
theorem B3400055 : Blo 670310 3400055 := bstep (se 1 (by rfl) ⟨2550041, by rfl⟩ : syracuseStep 3400055 = 5100083) B5100083
theorem B1007999 : Blo 670310 1007999 := bstep (se 1 (by rfl) ⟨755999, by rfl⟩ : syracuseStep 1007999 = 1511999) B1511999
theorem B1008071 : Blo 670310 1008071 := bstep (se 1 (by rfl) ⟨756053, by rfl⟩ : syracuseStep 1008071 = 1512107) B1512107
theorem B4842251 : Blo 670310 4842251 := bstep (se 1 (by rfl) ⟨3631688, by rfl⟩ : syracuseStep 4842251 = 7263377) B7263377
theorem B1008425 : Blo 670310 1008425 := bstep (se 2 (by rfl) ⟨378159, by rfl⟩ : syracuseStep 1008425 = 756319) B756319
theorem B1008431 : Blo 670310 1008431 := bstep (se 1 (by rfl) ⟨756323, by rfl⟩ : syracuseStep 1008431 = 1512647) B1512647
theorem B1008551 : Blo 670310 1008551 := bstep (se 1 (by rfl) ⟨756413, by rfl⟩ : syracuseStep 1008551 = 1512827) B1512827
theorem B1008635 : Blo 670310 1008635 := bstep (se 1 (by rfl) ⟨756476, by rfl⟩ : syracuseStep 1008635 = 1512953) B1512953
theorem B16376849 : Blo 670310 16376849 := bstep (se 2 (by rfl) ⟨6141318, by rfl⟩ : syracuseStep 16376849 = 12282637) B12282637
theorem B1008695 : Blo 670310 1008695 := bstep (se 1 (by rfl) ⟨756521, by rfl⟩ : syracuseStep 1008695 = 1513043) B1513043
theorem B1008815 : Blo 670310 1008815 := bstep (se 1 (by rfl) ⟨756611, by rfl⟩ : syracuseStep 1008815 = 1513223) B1513223
theorem B8611109 : Blo 670310 8611109 := bstep (se 4 (by rfl) ⟨807291, by rfl⟩ : syracuseStep 8611109 = 1614583) B1614583
theorem B3401027 : Blo 670310 3401027 := bstep (se 1 (by rfl) ⟨2550770, by rfl⟩ : syracuseStep 3401027 = 5101541) B5101541
theorem B1009223 : Blo 670310 1009223 := bstep (se 1 (by rfl) ⟨756917, by rfl⟩ : syracuseStep 1009223 = 1513835) B1513835
theorem B1009319 : Blo 670310 1009319 := bstep (se 1 (by rfl) ⟨756989, by rfl⟩ : syracuseStep 1009319 = 1513979) B1513979
theorem B1009403 : Blo 670310 1009403 := bstep (se 1 (by rfl) ⟨757052, by rfl⟩ : syracuseStep 1009403 = 1514105) B1514105
theorem B1009439 : Blo 670310 1009439 := bstep (se 1 (by rfl) ⟨757079, by rfl⟩ : syracuseStep 1009439 = 1514159) B1514159
theorem B2418473 : Blo 670310 2418473 := bstep (se 2 (by rfl) ⟨906927, by rfl⟩ : syracuseStep 2418473 = 1813855) B1813855
theorem B1009487 : Blo 670310 1009487 := bstep (se 1 (by rfl) ⟨757115, by rfl⟩ : syracuseStep 1009487 = 1514231) B1514231
theorem B1009607 : Blo 670310 1009607 := bstep (se 1 (by rfl) ⟨757205, by rfl⟩ : syracuseStep 1009607 = 1514411) B1514411
theorem B3401837 : Blo 670310 3401837 := bstep (se 3 (by rfl) ⟨637844, by rfl⟩ : syracuseStep 3401837 = 1275689) B1275689
theorem B6121619 : Blo 670310 6121619 := bstep (se 1 (by rfl) ⟨4591214, by rfl⟩ : syracuseStep 6121619 = 9182429) B9182429
theorem B3074201 : Blo 670310 3074201 := bstep (se 2 (by rfl) ⟨1152825, by rfl⟩ : syracuseStep 3074201 = 2305651) B2305651
theorem B12249353 : Blo 670310 12249353 := bstep (se 2 (by rfl) ⟨4593507, by rfl⟩ : syracuseStep 12249353 = 9187015) B9187015
theorem B1009961 : Blo 670310 1009961 := bstep (se 2 (by rfl) ⟨378735, by rfl⟩ : syracuseStep 1009961 = 757471) B757471
theorem B1009967 : Blo 670310 1009967 := bstep (se 1 (by rfl) ⟨757475, by rfl⟩ : syracuseStep 1009967 = 1514951) B1514951
theorem B3631499 : Blo 670310 3631499 := bstep (se 1 (by rfl) ⟨2723624, by rfl⟩ : syracuseStep 3631499 = 5447249) B5447249
theorem B1010207 : Blo 670310 1010207 := bstep (se 1 (by rfl) ⟨757655, by rfl⟩ : syracuseStep 1010207 = 1515311) B1515311
theorem B4844069 : Blo 670310 4844069 := bstep (se 4 (by rfl) ⟨454131, by rfl⟩ : syracuseStep 4844069 = 908263) B908263
theorem B5827247 : Blo 670310 5827247 := bstep (se 1 (by rfl) ⟨4370435, by rfl⟩ : syracuseStep 5827247 = 8740871) B8740871
theorem B1010591 : Blo 670310 1010591 := bstep (se 1 (by rfl) ⟨757943, by rfl⟩ : syracuseStep 1010591 = 1515887) B1515887
theorem B1010639 : Blo 670310 1010639 := bstep (se 1 (by rfl) ⟨757979, by rfl⟩ : syracuseStep 1010639 = 1515959) B1515959
theorem B9694187 : Blo 670310 9694187 := bstep (se 1 (by rfl) ⟨7270640, by rfl⟩ : syracuseStep 9694187 = 14541281) B14541281
theorem B1010729 : Blo 670310 1010729 := bstep (se 2 (by rfl) ⟨379023, by rfl⟩ : syracuseStep 1010729 = 758047) B758047
theorem B1010735 : Blo 670310 1010735 := bstep (se 1 (by rfl) ⟨758051, by rfl⟩ : syracuseStep 1010735 = 1516103) B1516103
theorem B1010759 : Blo 670310 1010759 := bstep (se 1 (by rfl) ⟨758069, by rfl⟩ : syracuseStep 1010759 = 1516139) B1516139
theorem B1011023 : Blo 670310 1011023 := bstep (se 1 (by rfl) ⟨758267, by rfl⟩ : syracuseStep 1011023 = 1516535) B1516535
theorem B1011113 : Blo 670310 1011113 := bstep (se 2 (by rfl) ⟨379167, by rfl⟩ : syracuseStep 1011113 = 758335) B758335
theorem B1699319 : Blo 670310 1699319 := bstep (se 1 (by rfl) ⟨1274489, by rfl⟩ : syracuseStep 1699319 = 2548979) B2548979
theorem B1011263 : Blo 670310 1011263 := bstep (se 1 (by rfl) ⟨758447, by rfl⟩ : syracuseStep 1011263 = 1516895) B1516895
theorem B1208083 : Blo 670310 1208083 := bstep (se 1 (by rfl) ⟨906062, by rfl⟩ : syracuseStep 1208083 = 1812125) B1812125
theorem B1273639 : Blo 670310 1273639 := bstep (se 1 (by rfl) ⟨955229, by rfl⟩ : syracuseStep 1273639 = 1910459) B1910459
theorem B2158559 : Blo 670310 2158559 := bstep (se 1 (by rfl) ⟨1618919, by rfl⟩ : syracuseStep 2158559 = 3237839) B3237839
theorem B2552093 : Blo 670310 2552093 := bstep (se 3 (by rfl) ⟨478517, by rfl⟩ : syracuseStep 2552093 = 957035) B957035
theorem B2158903 : Blo 670310 2158903 := bstep (se 1 (by rfl) ⟨1619177, by rfl⟩ : syracuseStep 2158903 = 3238355) B3238355
theorem B26276183 : Blo 670310 26276183 := bstep (se 1 (by rfl) ⟨19707137, by rfl⟩ : syracuseStep 26276183 = 39414275) B39414275
theorem B19919195 : Blo 670310 19919195 := bstep (se 1 (by rfl) ⟨14939396, by rfl⟩ : syracuseStep 19919195 = 29878793) B29878793
theorem B1700311 : Blo 670310 1700311 := bstep (se 1 (by rfl) ⟨1275233, by rfl⟩ : syracuseStep 1700311 = 2550467) B2550467
theorem B2421343 : Blo 670310 2421343 := bstep (se 1 (by rfl) ⟨1816007, by rfl⟩ : syracuseStep 2421343 = 3632015) B3632015
theorem B1700615 : Blo 670310 1700615 := bstep (se 1 (by rfl) ⟨1275461, by rfl⟩ : syracuseStep 1700615 = 2550923) B2550923
theorem B3830759 : Blo 670310 3830759 := bstep (se 1 (by rfl) ⟨2873069, by rfl⟩ : syracuseStep 3830759 = 5746139) B5746139
theorem B1274953 : Blo 670310 1274953 := bstep (se 2 (by rfl) ⟨478107, by rfl⟩ : syracuseStep 1274953 = 956215) B956215
theorem B2159723 : Blo 670310 2159723 := bstep (se 1 (by rfl) ⟨1619792, by rfl⟩ : syracuseStep 2159723 = 3239585) B3239585
theorem B3404915 : Blo 670310 3404915 := bstep (se 1 (by rfl) ⟨2553686, by rfl⟩ : syracuseStep 3404915 = 5107373) B5107373
theorem B12907673 : Blo 670310 12907673 := bstep (se 2 (by rfl) ⟨4840377, by rfl⟩ : syracuseStep 12907673 = 9680755) B9680755
theorem B2159891 : Blo 670310 2159891 := bstep (se 1 (by rfl) ⟨1619918, by rfl⟩ : syracuseStep 2159891 = 3239837) B3239837
theorem B6911281 : Blo 670310 6911281 := bstep (se 2 (by rfl) ⟨2591730, by rfl⟩ : syracuseStep 6911281 = 5183461) B5183461
theorem B1439201 : Blo 670310 1439201 := bstep (se 2 (by rfl) ⟨539700, by rfl⟩ : syracuseStep 1439201 = 1079401) B1079401
theorem B29455883 : Blo 670310 29455883 := bstep (se 1 (by rfl) ⟨22091912, by rfl⟩ : syracuseStep 29455883 = 44183825) B44183825
theorem B3405563 : Blo 670310 3405563 := bstep (se 1 (by rfl) ⟨2554172, by rfl⟩ : syracuseStep 3405563 = 5108345) B5108345
theorem B1701769 : Blo 670310 1701769 := bstep (se 2 (by rfl) ⟨638163, by rfl⟩ : syracuseStep 1701769 = 1276327) B1276327
theorem B3405725 : Blo 670310 3405725 := bstep (se 3 (by rfl) ⟨638573, by rfl⟩ : syracuseStep 3405725 = 1277147) B1277147
theorem B1275887 : Blo 670310 1275887 := bstep (se 1 (by rfl) ⟨956915, by rfl⟩ : syracuseStep 1275887 = 1913831) B1913831
theorem B4356089 : Blo 670310 4356089 := bstep (se 2 (by rfl) ⟨1633533, by rfl⟩ : syracuseStep 4356089 = 3267067) B3267067
theorem B1701881 : Blo 670310 1701881 := bstep (se 2 (by rfl) ⟨638205, by rfl⟩ : syracuseStep 1701881 = 1276411) B1276411
theorem B4847759 : Blo 670310 4847759 := bstep (se 1 (by rfl) ⟨3635819, by rfl⟩ : syracuseStep 4847759 = 7271639) B7271639
theorem B1702043 : Blo 670310 1702043 := bstep (se 1 (by rfl) ⟨1276532, by rfl⟩ : syracuseStep 1702043 = 2553065) B2553065
theorem B7666163 : Blo 670310 7666163 := bstep (se 1 (by rfl) ⟨5749622, by rfl⟩ : syracuseStep 7666163 = 11499245) B11499245
theorem B5733017 : Blo 670310 5733017 := bstep (se 2 (by rfl) ⟨2149881, by rfl⟩ : syracuseStep 5733017 = 4299763) B4299763
theorem B3406535 : Blo 670310 3406535 := bstep (se 1 (by rfl) ⟨2554901, by rfl⟩ : syracuseStep 3406535 = 5109803) B5109803
theorem B2423777 : Blo 670310 2423777 := bstep (se 2 (by rfl) ⟨908916, by rfl⟩ : syracuseStep 2423777 = 1817833) B1817833
theorem B1276897 : Blo 670310 1276897 := bstep (se 2 (by rfl) ⟨478836, by rfl⟩ : syracuseStep 1276897 = 957673) B957673
theorem B2555009 : Blo 670310 2555009 := bstep (se 2 (by rfl) ⟨958128, by rfl⟩ : syracuseStep 2555009 = 1916257) B1916257
theorem B1703177 : Blo 670310 1703177 := bstep (se 2 (by rfl) ⟨638691, by rfl⟩ : syracuseStep 1703177 = 1277383) B1277383
theorem B3505619 : Blo 670310 3505619 := bstep (se 1 (by rfl) ⟨2629214, by rfl⟩ : syracuseStep 3505619 = 5258429) B5258429
theorem B4849399 : Blo 670310 4849399 := bstep (se 1 (by rfl) ⟨3637049, by rfl⟩ : syracuseStep 4849399 = 7274099) B7274099
theorem B3408479 : Blo 670310 3408479 := bstep (se 1 (by rfl) ⟨2556359, by rfl⟩ : syracuseStep 3408479 = 5112719) B5112719
theorem B1278575 : Blo 670310 1278575 := bstep (se 1 (by rfl) ⟨958931, by rfl⟩ : syracuseStep 1278575 = 1917863) B1917863
theorem B2556953 : Blo 670310 2556953 := bstep (se 2 (by rfl) ⟨958857, by rfl⟩ : syracuseStep 2556953 = 1917715) B1917715
theorem B754735 : Blo 670310 754735 := bstep (se 1 (by rfl) ⟨566051, by rfl⟩ : syracuseStep 754735 = 1132103) B1132103
theorem B1508543 : Blo 670310 1508543 := bstep (se 1 (by rfl) ⟨1131407, by rfl⟩ : syracuseStep 1508543 = 2262815) B2262815
theorem B754879 : Blo 670310 754879 := bstep (se 1 (by rfl) ⟨566159, by rfl⟩ : syracuseStep 754879 = 1132319) B1132319
theorem B853183 : Blo 670310 853183 := bstep (se 1 (by rfl) ⟨639887, by rfl⟩ : syracuseStep 853183 = 1279775) B1279775
theorem B1705171 : Blo 670310 1705171 := bstep (se 1 (by rfl) ⟨1278878, by rfl⟩ : syracuseStep 1705171 = 2557757) B2557757
theorem B1508687 : Blo 670310 1508687 := bstep (se 1 (by rfl) ⟨1131515, by rfl⟩ : syracuseStep 1508687 = 2263031) B2263031
theorem B755023 : Blo 670310 755023 := bstep (se 1 (by rfl) ⟨566267, by rfl⟩ : syracuseStep 755023 = 1132535) B1132535
theorem B1508777 : Blo 670310 1508777 := bstep (se 2 (by rfl) ⟨565791, by rfl⟩ : syracuseStep 1508777 = 1131583) B1131583
theorem B12289573 : Blo 670310 12289573 := bstep (se 4 (by rfl) ⟨1152147, by rfl⟩ : syracuseStep 12289573 = 2304295) B2304295
theorem B31000265 : Blo 670310 31000265 := bstep (se 2 (by rfl) ⟨11625099, by rfl⟩ : syracuseStep 31000265 = 23250199) B23250199
theorem B1509263 : Blo 670310 1509263 := bstep (se 1 (by rfl) ⟨1131947, by rfl⟩ : syracuseStep 1509263 = 2263895) B2263895
theorem B1509407 : Blo 670310 1509407 := bstep (se 1 (by rfl) ⟨1132055, by rfl⟩ : syracuseStep 1509407 = 2264111) B2264111
theorem B755743 : Blo 670310 755743 := bstep (se 1 (by rfl) ⟨566807, by rfl⟩ : syracuseStep 755743 = 1133615) B1133615
theorem B6883379 : Blo 670310 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B1214651 : Blo 670310 1214651 := bstep (se 1 (by rfl) ⟨910988, by rfl⟩ : syracuseStep 1214651 = 1821977) B1821977
theorem B1509659 : Blo 670310 1509659 := bstep (se 1 (by rfl) ⟨1132244, by rfl⟩ : syracuseStep 1509659 = 2264489) B2264489
theorem B755995 : Blo 670310 755995 := bstep (se 1 (by rfl) ⟨566996, by rfl⟩ : syracuseStep 755995 = 1133993) B1133993
theorem B887119 : Blo 670310 887119 := bstep (se 1 (by rfl) ⟨665339, by rfl⟩ : syracuseStep 887119 = 1330679) B1330679
theorem B3639647 : Blo 670310 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B1509983 : Blo 670310 1509983 := bstep (se 1 (by rfl) ⟨1132487, by rfl⟩ : syracuseStep 1509983 = 2264975) B2264975
theorem B5114663 : Blo 670310 5114663 := bstep (se 1 (by rfl) ⟨3835997, by rfl⟩ : syracuseStep 5114663 = 7671995) B7671995
theorem B1706791 : Blo 670310 1706791 := bstep (se 1 (by rfl) ⟨1280093, by rfl⟩ : syracuseStep 1706791 = 2560187) B2560187
theorem B2427731 : Blo 670310 2427731 := bstep (se 1 (by rfl) ⟨1820798, by rfl⟩ : syracuseStep 2427731 = 3641597) B3641597
theorem B1510235 : Blo 670310 1510235 := bstep (se 1 (by rfl) ⟨1132676, by rfl⟩ : syracuseStep 1510235 = 2265353) B2265353
theorem B2559185 : Blo 670310 2559185 := bstep (se 2 (by rfl) ⟨959694, by rfl⟩ : syracuseStep 2559185 = 1919389) B1919389
theorem B1936595 : Blo 670310 1936595 := bstep (se 1 (by rfl) ⟨1452446, by rfl⟩ : syracuseStep 1936595 = 2904893) B2904893
theorem B2624723 : Blo 670310 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B757147 : Blo 670310 757147 := bstep (se 1 (by rfl) ⟨567860, by rfl⟩ : syracuseStep 757147 = 1135721) B1135721
theorem B1510991 : Blo 670310 1510991 := bstep (se 1 (by rfl) ⟨1133243, by rfl⟩ : syracuseStep 1510991 = 2266487) B2266487
theorem B1150567 : Blo 670310 1150567 := bstep (se 1 (by rfl) ⟨862925, by rfl⟩ : syracuseStep 1150567 = 1725851) B1725851
theorem B3641075 : Blo 670310 3641075 := bstep (se 1 (by rfl) ⟨2730806, by rfl⟩ : syracuseStep 3641075 = 5461613) B5461613
theorem B2428795 : Blo 670310 2428795 := bstep (se 1 (by rfl) ⟨1821596, by rfl⟩ : syracuseStep 2428795 = 3643193) B3643193
theorem B2592719 : Blo 670310 2592719 := bstep (se 1 (by rfl) ⟨1944539, by rfl⟩ : syracuseStep 2592719 = 3889079) B3889079
theorem B2461759 : Blo 670310 2461759 := bstep (se 1 (by rfl) ⟨1846319, by rfl⟩ : syracuseStep 2461759 = 3692639) B3692639
theorem B2265191 : Blo 670310 2265191 := bstep (se 1 (by rfl) ⟨1698893, by rfl⟩ : syracuseStep 2265191 = 3397787) B3397787
theorem B1511531 : Blo 670310 1511531 := bstep (se 1 (by rfl) ⟨1133648, by rfl⟩ : syracuseStep 1511531 = 2267297) B2267297
theorem B1511585 : Blo 670310 1511585 := bstep (se 2 (by rfl) ⟨566844, by rfl⟩ : syracuseStep 1511585 = 1133689) B1133689
theorem B1511711 : Blo 670310 1511711 := bstep (se 1 (by rfl) ⟨1133783, by rfl⟩ : syracuseStep 1511711 = 2267567) B2267567
theorem B758119 : Blo 670310 758119 := bstep (se 1 (by rfl) ⟨568589, by rfl⟩ : syracuseStep 758119 = 1137179) B1137179
theorem B1512431 : Blo 670310 1512431 := bstep (se 1 (by rfl) ⟨1134323, by rfl⟩ : syracuseStep 1512431 = 2268647) B2268647
theorem B12948497 : Blo 670310 12948497 := bstep (se 2 (by rfl) ⟨4855686, by rfl⟩ : syracuseStep 12948497 = 9711373) B9711373
theorem B1610777 : Blo 670310 1610777 := bstep (se 2 (by rfl) ⟨604041, by rfl⟩ : syracuseStep 1610777 = 1208083) B1208083
theorem B1512935 : Blo 670310 1512935 := bstep (se 1 (by rfl) ⟨1134701, by rfl⟩ : syracuseStep 1512935 = 2269403) B2269403
theorem B2266703 : Blo 670310 2266703 := bstep (se 1 (by rfl) ⟨1700027, by rfl⟩ : syracuseStep 2266703 = 3400055) B3400055
theorem B1513097 : Blo 670310 1513097 := bstep (se 2 (by rfl) ⟨567411, by rfl⟩ : syracuseStep 1513097 = 1134823) B1134823
theorem B1513115 : Blo 670310 1513115 := bstep (se 1 (by rfl) ⟨1134836, by rfl⟩ : syracuseStep 1513115 = 2269673) B2269673
theorem B1513313 : Blo 670310 1513313 := bstep (se 2 (by rfl) ⟨567492, by rfl⟩ : syracuseStep 1513313 = 1134985) B1134985
theorem B2267081 : Blo 670310 2267081 := bstep (se 2 (by rfl) ⟨850155, by rfl⟩ : syracuseStep 2267081 = 1700311) B1700311
theorem B10917899 : Blo 670310 10917899 := bstep (se 1 (by rfl) ⟨8188424, by rfl⟩ : syracuseStep 10917899 = 16376849) B16376849
theorem B1513511 : Blo 670310 1513511 := bstep (se 1 (by rfl) ⟨1135133, by rfl⟩ : syracuseStep 1513511 = 2270267) B2270267
theorem B5740739 : Blo 670310 5740739 := bstep (se 1 (by rfl) ⟨4305554, by rfl⟩ : syracuseStep 5740739 = 8611109) B8611109
theorem B2267351 : Blo 670310 2267351 := bstep (se 1 (by rfl) ⟨1700513, by rfl⟩ : syracuseStep 2267351 = 3401027) B3401027
theorem B1513691 : Blo 670310 1513691 := bstep (se 1 (by rfl) ⟨1135268, by rfl⟩ : syracuseStep 1513691 = 2270537) B2270537
theorem B1513889 : Blo 670310 1513889 := bstep (se 2 (by rfl) ⟨567708, by rfl⟩ : syracuseStep 1513889 = 1135417) B1135417
theorem B1513961 : Blo 670310 1513961 := bstep (se 2 (by rfl) ⟨567735, by rfl⟩ : syracuseStep 1513961 = 1135471) B1135471
theorem B1612315 : Blo 670310 1612315 := bstep (se 1 (by rfl) ⟨1209236, by rfl⟩ : syracuseStep 1612315 = 2418473) B2418473
theorem B5118551 : Blo 670310 5118551 := bstep (se 1 (by rfl) ⟨3838913, by rfl⟩ : syracuseStep 5118551 = 7677827) B7677827
theorem B8591993 : Blo 670310 8591993 := bstep (se 2 (by rfl) ⟨3221997, by rfl⟩ : syracuseStep 8591993 = 6443995) B6443995
theorem B2267891 : Blo 670310 2267891 := bstep (se 1 (by rfl) ⟨1700918, by rfl⟩ : syracuseStep 2267891 = 3401837) B3401837
theorem B9215041 : Blo 670310 9215041 := bstep (se 2 (by rfl) ⟨3455640, by rfl⟩ : syracuseStep 9215041 = 6911281) B6911281
theorem B6462791 : Blo 670310 6462791 := bstep (se 1 (by rfl) ⟨4847093, by rfl⟩ : syracuseStep 6462791 = 9694187) B9694187
theorem B2269025 : Blo 670310 2269025 := bstep (se 2 (by rfl) ⟨850884, by rfl⟩ : syracuseStep 2269025 = 1701769) B1701769
theorem B1515419 : Blo 670310 1515419 := bstep (se 1 (by rfl) ⟨1136564, by rfl⟩ : syracuseStep 1515419 = 2273129) B2273129
theorem B6463405 : Blo 670310 6463405 := bstep (se 3 (by rfl) ⟨1211888, by rfl⟩ : syracuseStep 6463405 = 2423777) B2423777
theorem B1843415 : Blo 670310 1843415 := bstep (se 1 (by rfl) ⟨1382561, by rfl⟩ : syracuseStep 1843415 = 2765123) B2765123
theorem B13279463 : Blo 670310 13279463 := bstep (se 1 (by rfl) ⟨9959597, by rfl⟩ : syracuseStep 13279463 = 19919195) B19919195
theorem B1909001 : Blo 670310 1909001 := bstep (se 2 (by rfl) ⟨715875, by rfl⟩ : syracuseStep 1909001 = 1431751) B1431751
theorem B1515833 : Blo 670310 1515833 := bstep (se 2 (by rfl) ⟨568437, by rfl⟩ : syracuseStep 1515833 = 1136875) B1136875
theorem B1909241 : Blo 670310 1909241 := bstep (se 2 (by rfl) ⟨715965, by rfl⟩ : syracuseStep 1909241 = 1431931) B1431931
theorem B2269943 : Blo 670310 2269943 := bstep (se 1 (by rfl) ⟨1702457, by rfl⟩ : syracuseStep 2269943 = 3404915) B3404915
theorem B1516319 : Blo 670310 1516319 := bstep (se 1 (by rfl) ⟨1137239, by rfl⟩ : syracuseStep 1516319 = 2274479) B2274479
theorem B5448545 : Blo 670310 5448545 := bstep (se 2 (by rfl) ⟨2043204, by rfl⟩ : syracuseStep 5448545 = 4086409) B4086409
theorem B959467 : Blo 670310 959467 := bstep (se 1 (by rfl) ⟨719600, by rfl⟩ : syracuseStep 959467 = 1439201) B1439201
theorem B19637255 : Blo 670310 19637255 := bstep (se 1 (by rfl) ⟨14727941, by rfl⟩ : syracuseStep 19637255 = 29455883) B29455883
theorem B2270375 : Blo 670310 2270375 := bstep (se 1 (by rfl) ⟨1702781, by rfl⟩ : syracuseStep 2270375 = 3405563) B3405563
theorem B9348317 : Blo 670310 9348317 := bstep (se 3 (by rfl) ⟨1752809, by rfl⟩ : syracuseStep 9348317 = 3505619) B3505619
theorem B2270483 : Blo 670310 2270483 := bstep (se 1 (by rfl) ⟨1702862, by rfl⟩ : syracuseStep 2270483 = 3405725) B3405725
theorem B25863461 : Blo 670310 25863461 := bstep (se 4 (by rfl) ⟨2424699, by rfl⟩ : syracuseStep 25863461 = 4849399) B4849399
theorem B1517129 : Blo 670310 1517129 := bstep (se 2 (by rfl) ⟨568923, by rfl⟩ : syracuseStep 1517129 = 1137847) B1137847
theorem B2271023 : Blo 670310 2271023 := bstep (se 1 (by rfl) ⟨1703267, by rfl⟩ : syracuseStep 2271023 = 3406535) B3406535
theorem B1617025 : Blo 670310 1617025 := bstep (se 2 (by rfl) ⟨606384, by rfl⟩ : syracuseStep 1617025 = 1212769) B1212769
theorem B7253687 : Blo 670310 7253687 := bstep (se 1 (by rfl) ⟨5440265, by rfl⟩ : syracuseStep 7253687 = 10880531) B10880531
theorem B1617641 : Blo 670310 1617641 := bstep (se 2 (by rfl) ⟨606615, by rfl⟩ : syracuseStep 1617641 = 1213231) B1213231
theorem B1617659 : Blo 670310 1617659 := bstep (se 1 (by rfl) ⟨1213244, by rfl⟩ : syracuseStep 1617659 = 2426489) B2426489
theorem B3223631 : Blo 670310 3223631 := bstep (se 1 (by rfl) ⟨2417723, by rfl⟩ : syracuseStep 3223631 = 4835447) B4835447
theorem B2863673 : Blo 670310 2863673 := bstep (se 2 (by rfl) ⟨1073877, by rfl⟩ : syracuseStep 2863673 = 2147755) B2147755
theorem B1618697 : Blo 670310 1618697 := bstep (se 2 (by rfl) ⟨607011, by rfl⟩ : syracuseStep 1618697 = 1214023) B1214023
theorem B1913807 : Blo 670310 1913807 := bstep (se 1 (by rfl) ⟨1435355, by rfl⟩ : syracuseStep 1913807 = 2870711) B2870711
theorem B5092307 : Blo 670310 5092307 := bstep (se 1 (by rfl) ⟨3819230, by rfl⟩ : syracuseStep 5092307 = 7638461) B7638461
theorem B1455355 : Blo 670310 1455355 := bstep (se 1 (by rfl) ⟨1091516, by rfl⟩ : syracuseStep 1455355 = 2183033) B2183033
theorem B6534449 : Blo 670310 6534449 := bstep (se 2 (by rfl) ⟨2450418, by rfl⟩ : syracuseStep 6534449 = 4900837) B4900837
theorem B44086999 : Blo 670310 44086999 := bstep (se 1 (by rfl) ⟨33065249, by rfl⟩ : syracuseStep 44086999 = 66130499) B66130499
theorem B99727199 : Blo 670310 99727199 := bstep (se 1 (by rfl) ⟨74795399, by rfl⟩ : syracuseStep 99727199 = 149590799) B149590799
theorem B2275559 : Blo 670310 2275559 := bstep (se 1 (by rfl) ⟨1706669, by rfl⟩ : syracuseStep 2275559 = 3413339) B3413339
theorem B35404235 : Blo 670310 35404235 := bstep (se 1 (by rfl) ⟨26553176, by rfl⟩ : syracuseStep 35404235 = 53106353) B53106353
theorem B670367 : Blo 670310 670367 := bstep (se 1 (by rfl) ⟨502775, by rfl⟩ : syracuseStep 670367 = 1005551) B1005551
theorem B5159639 : Blo 670310 5159639 := bstep (se 1 (by rfl) ⟨3869729, by rfl⟩ : syracuseStep 5159639 = 7739459) B7739459
theorem B670535 : Blo 670310 670535 := bstep (se 1 (by rfl) ⟨502901, by rfl⟩ : syracuseStep 670535 = 1005803) B1005803
theorem B670575 : Blo 670310 670575 := bstep (se 1 (by rfl) ⟨502931, by rfl⟩ : syracuseStep 670575 = 1005863) B1005863
theorem B670631 : Blo 670310 670631 := bstep (se 1 (by rfl) ⟨502973, by rfl⟩ : syracuseStep 670631 = 1005947) B1005947
theorem B670811 : Blo 670310 670811 := bstep (se 1 (by rfl) ⟨503108, by rfl⟩ : syracuseStep 670811 = 1006217) B1006217
theorem B5749865 : Blo 670310 5749865 := bstep (se 2 (by rfl) ⟨2156199, by rfl⟩ : syracuseStep 5749865 = 4312399) B4312399
theorem B670927 : Blo 670310 670927 := bstep (se 1 (by rfl) ⟨503195, by rfl⟩ : syracuseStep 670927 = 1006391) B1006391
theorem B670951 : Blo 670310 670951 := bstep (se 1 (by rfl) ⟨503213, by rfl⟩ : syracuseStep 670951 = 1006427) B1006427
theorem B671047 : Blo 670310 671047 := bstep (se 1 (by rfl) ⟨503285, by rfl⟩ : syracuseStep 671047 = 1006571) B1006571
theorem B671183 : Blo 670310 671183 := bstep (se 1 (by rfl) ⟨503387, by rfl⟩ : syracuseStep 671183 = 1006775) B1006775
theorem B671343 : Blo 670310 671343 := bstep (se 1 (by rfl) ⟨503507, by rfl⟩ : syracuseStep 671343 = 1007015) B1007015
theorem B671399 : Blo 670310 671399 := bstep (se 1 (by rfl) ⟨503549, by rfl⟩ : syracuseStep 671399 = 1007099) B1007099
theorem B671463 : Blo 670310 671463 := bstep (se 1 (by rfl) ⟨503597, by rfl⟩ : syracuseStep 671463 = 1007195) B1007195
theorem B25902827 : Blo 670310 25902827 := bstep (se 1 (by rfl) ⟨19427120, by rfl⟩ : syracuseStep 25902827 = 38854241) B38854241
theorem B671519 : Blo 670310 671519 := bstep (se 1 (by rfl) ⟨503639, by rfl⟩ : syracuseStep 671519 = 1007279) B1007279
theorem B5095223 : Blo 670310 5095223 := bstep (se 1 (by rfl) ⟨3821417, by rfl⟩ : syracuseStep 5095223 = 7642835) B7642835
theorem B671599 : Blo 670310 671599 := bstep (se 1 (by rfl) ⟨503699, by rfl⟩ : syracuseStep 671599 = 1007399) B1007399
theorem B1359737 : Blo 670310 1359737 := bstep (se 2 (by rfl) ⟨509901, by rfl⟩ : syracuseStep 1359737 = 1019803) B1019803
theorem B671655 : Blo 670310 671655 := bstep (se 1 (by rfl) ⟨503741, by rfl⟩ : syracuseStep 671655 = 1007483) B1007483
theorem B671935 : Blo 670310 671935 := bstep (se 1 (by rfl) ⟨503951, by rfl⟩ : syracuseStep 671935 = 1007903) B1007903
theorem B671951 : Blo 670310 671951 := bstep (se 1 (by rfl) ⟨503963, by rfl⟩ : syracuseStep 671951 = 1007927) B1007927
theorem B671999 : Blo 670310 671999 := bstep (se 1 (by rfl) ⟨503999, by rfl⟩ : syracuseStep 671999 = 1007999) B1007999
theorem B672047 : Blo 670310 672047 := bstep (se 1 (by rfl) ⟨504035, by rfl⟩ : syracuseStep 672047 = 1008071) B1008071
theorem B1360255 : Blo 670310 1360255 := bstep (se 1 (by rfl) ⟨1020191, by rfl⟩ : syracuseStep 1360255 = 2040383) B2040383
theorem B3228167 : Blo 670310 3228167 := bstep (se 1 (by rfl) ⟨2421125, by rfl⟩ : syracuseStep 3228167 = 4842251) B4842251
theorem B672283 : Blo 670310 672283 := bstep (se 1 (by rfl) ⟨504212, by rfl⟩ : syracuseStep 672283 = 1008425) B1008425
theorem B672287 : Blo 670310 672287 := bstep (se 1 (by rfl) ⟨504215, by rfl⟩ : syracuseStep 672287 = 1008431) B1008431
theorem B26165861 : Blo 670310 26165861 := bstep (se 4 (by rfl) ⟨2453049, by rfl⟩ : syracuseStep 26165861 = 4906099) B4906099
theorem B672367 : Blo 670310 672367 := bstep (se 1 (by rfl) ⟨504275, by rfl⟩ : syracuseStep 672367 = 1008551) B1008551
theorem B672423 : Blo 670310 672423 := bstep (se 1 (by rfl) ⟨504317, by rfl⟩ : syracuseStep 672423 = 1008635) B1008635
theorem B672463 : Blo 670310 672463 := bstep (se 1 (by rfl) ⟨504347, by rfl⟩ : syracuseStep 672463 = 1008695) B1008695
theorem B672543 : Blo 670310 672543 := bstep (se 1 (by rfl) ⟨504407, by rfl⟩ : syracuseStep 672543 = 1008815) B1008815
theorem B3228457 : Blo 670310 3228457 := bstep (se 2 (by rfl) ⟨1210671, by rfl⟩ : syracuseStep 3228457 = 2421343) B2421343
theorem B672815 : Blo 670310 672815 := bstep (se 1 (by rfl) ⟨504611, by rfl⟩ : syracuseStep 672815 = 1009223) B1009223
theorem B672879 : Blo 670310 672879 := bstep (se 1 (by rfl) ⟨504659, by rfl⟩ : syracuseStep 672879 = 1009319) B1009319
theorem B672935 : Blo 670310 672935 := bstep (se 1 (by rfl) ⟨504701, by rfl⟩ : syracuseStep 672935 = 1009403) B1009403
theorem B672959 : Blo 670310 672959 := bstep (se 1 (by rfl) ⟨504719, by rfl⟩ : syracuseStep 672959 = 1009439) B1009439
theorem B672991 : Blo 670310 672991 := bstep (se 1 (by rfl) ⟨504743, by rfl⟩ : syracuseStep 672991 = 1009487) B1009487
theorem B673071 : Blo 670310 673071 := bstep (se 1 (by rfl) ⟨504803, by rfl⟩ : syracuseStep 673071 = 1009607) B1009607
theorem B4081079 : Blo 670310 4081079 := bstep (se 1 (by rfl) ⟨3060809, by rfl⟩ : syracuseStep 4081079 = 6121619) B6121619
theorem B2049467 : Blo 670310 2049467 := bstep (se 1 (by rfl) ⟨1537100, by rfl⟩ : syracuseStep 2049467 = 3074201) B3074201
theorem B673307 : Blo 670310 673307 := bstep (se 1 (by rfl) ⟨504980, by rfl⟩ : syracuseStep 673307 = 1009961) B1009961
theorem B673311 : Blo 670310 673311 := bstep (se 1 (by rfl) ⟨504983, by rfl⟩ : syracuseStep 673311 = 1009967) B1009967
theorem B2148011 : Blo 670310 2148011 := bstep (se 1 (by rfl) ⟨1611008, by rfl⟩ : syracuseStep 2148011 = 3222017) B3222017
theorem B673471 : Blo 670310 673471 := bstep (se 1 (by rfl) ⟨505103, by rfl⟩ : syracuseStep 673471 = 1010207) B1010207
theorem B3229379 : Blo 670310 3229379 := bstep (se 1 (by rfl) ⟨2422034, by rfl⟩ : syracuseStep 3229379 = 4844069) B4844069
theorem B3884831 : Blo 670310 3884831 := bstep (se 1 (by rfl) ⟨2913623, by rfl⟩ : syracuseStep 3884831 = 5827247) B5827247
theorem B673727 : Blo 670310 673727 := bstep (se 1 (by rfl) ⟨505295, by rfl⟩ : syracuseStep 673727 = 1010591) B1010591
theorem B673759 : Blo 670310 673759 := bstep (se 1 (by rfl) ⟨505319, by rfl⟩ : syracuseStep 673759 = 1010639) B1010639
theorem B673819 : Blo 670310 673819 := bstep (se 1 (by rfl) ⟨505364, by rfl⟩ : syracuseStep 673819 = 1010729) B1010729
theorem B673823 : Blo 670310 673823 := bstep (se 1 (by rfl) ⟨505367, by rfl⟩ : syracuseStep 673823 = 1010735) B1010735
theorem B673839 : Blo 670310 673839 := bstep (se 1 (by rfl) ⟨505379, by rfl⟩ : syracuseStep 673839 = 1010759) B1010759
theorem B1362143 : Blo 670310 1362143 := bstep (se 1 (by rfl) ⟨1021607, by rfl⟩ : syracuseStep 1362143 = 2043215) B2043215
theorem B674015 : Blo 670310 674015 := bstep (se 1 (by rfl) ⟨505511, by rfl⟩ : syracuseStep 674015 = 1011023) B1011023
theorem B674075 : Blo 670310 674075 := bstep (se 1 (by rfl) ⟨505556, by rfl⟩ : syracuseStep 674075 = 1011113) B1011113
theorem B1132879 : Blo 670310 1132879 := bstep (se 1 (by rfl) ⟨849659, by rfl⟩ : syracuseStep 1132879 = 1699319) B1699319
theorem B674175 : Blo 670310 674175 := bstep (se 1 (by rfl) ⟨505631, by rfl⟩ : syracuseStep 674175 = 1011263) B1011263
theorem B3820121 : Blo 670310 3820121 := bstep (se 2 (by rfl) ⟨1432545, by rfl⟩ : syracuseStep 3820121 = 2865091) B2865091
theorem B4082537 : Blo 670310 4082537 := bstep (se 2 (by rfl) ⟨1530951, by rfl⟩ : syracuseStep 4082537 = 3061903) B3061903
theorem B17517455 : Blo 670310 17517455 := bstep (se 1 (by rfl) ⟨13138091, by rfl⟩ : syracuseStep 17517455 = 26276183) B26276183
theorem B3820553 : Blo 670310 3820553 := bstep (se 2 (by rfl) ⟨1432707, by rfl⟩ : syracuseStep 3820553 = 2865415) B2865415
theorem B10505369 : Blo 670310 10505369 := bstep (se 2 (by rfl) ⟨3939513, by rfl⟩ : syracuseStep 10505369 = 7879027) B7879027
theorem B1133743 : Blo 670310 1133743 := bstep (se 1 (by rfl) ⟨850307, by rfl⟩ : syracuseStep 1133743 = 1700615) B1700615
theorem B8605115 : Blo 670310 8605115 := bstep (se 1 (by rfl) ⟨6453836, by rfl⟩ : syracuseStep 8605115 = 12907673) B12907673
theorem B5099111 : Blo 670310 5099111 := bstep (se 1 (by rfl) ⟨3824333, by rfl⟩ : syracuseStep 5099111 = 7648667) B7648667
theorem B1822591 : Blo 670310 1822591 := bstep (se 1 (by rfl) ⟨1366943, by rfl⟩ : syracuseStep 1822591 = 2733887) B2733887
theorem B2904059 : Blo 670310 2904059 := bstep (se 1 (by rfl) ⟨2178044, by rfl⟩ : syracuseStep 2904059 = 4356089) B4356089
theorem B1134587 : Blo 670310 1134587 := bstep (se 1 (by rfl) ⟨850940, by rfl⟩ : syracuseStep 1134587 = 1701881) B1701881
theorem B3231839 : Blo 670310 3231839 := bstep (se 1 (by rfl) ⟨2423879, by rfl⟩ : syracuseStep 3231839 = 4847759) B4847759
theorem B1134695 : Blo 670310 1134695 := bstep (se 1 (by rfl) ⟨851021, by rfl⟩ : syracuseStep 1134695 = 1702043) B1702043
theorem B3822011 : Blo 670310 3822011 := bstep (se 1 (by rfl) ⟨2866508, by rfl⟩ : syracuseStep 3822011 = 5733017) B5733017
theorem B1135451 : Blo 670310 1135451 := bstep (se 1 (by rfl) ⟨851588, by rfl⟩ : syracuseStep 1135451 = 1703177) B1703177
theorem B3823037 : Blo 670310 3823037 := bstep (se 3 (by rfl) ⟨716819, by rfl⟩ : syracuseStep 3823037 = 1433639) B1433639
theorem B2545289 : Blo 670310 2545289 := bstep (se 2 (by rfl) ⟨954483, by rfl⟩ : syracuseStep 2545289 = 1908967) B1908967
theorem B3823787 : Blo 670310 3823787 := bstep (se 1 (by rfl) ⟨2867840, by rfl⟩ : syracuseStep 3823787 = 5735681) B5735681
theorem B3823969 : Blo 670310 3823969 := bstep (se 2 (by rfl) ⟨1433988, by rfl⟩ : syracuseStep 3823969 = 2867977) B2867977
theorem B130734485 : Blo 670310 130734485 := bstep (se 6 (by rfl) ⟨3064089, by rfl⟩ : syracuseStep 130734485 = 6128179) B6128179
theorem B1005983 : Blo 670310 1005983 := bstep (se 1 (by rfl) ⟨754487, by rfl⟩ : syracuseStep 1005983 = 1508975) B1508975
theorem B1006055 : Blo 670310 1006055 := bstep (se 1 (by rfl) ⟨754541, by rfl⟩ : syracuseStep 1006055 = 1509083) B1509083
theorem B3234779 : Blo 670310 3234779 := bstep (se 1 (by rfl) ⟨2426084, by rfl⟩ : syracuseStep 3234779 = 4852169) B4852169
theorem B1006799 : Blo 670310 1006799 := bstep (se 1 (by rfl) ⟨755099, by rfl⟩ : syracuseStep 1006799 = 1510199) B1510199
theorem B3824927 : Blo 670310 3824927 := bstep (se 1 (by rfl) ⟨2868695, by rfl⟩ : syracuseStep 3824927 = 5737391) B5737391
theorem B1006919 : Blo 670310 1006919 := bstep (se 1 (by rfl) ⟨755189, by rfl⟩ : syracuseStep 1006919 = 1510379) B1510379
theorem B1007081 : Blo 670310 1007081 := bstep (se 2 (by rfl) ⟨377655, by rfl⟩ : syracuseStep 1007081 = 755311) B755311
theorem B1007225 : Blo 670310 1007225 := bstep (se 2 (by rfl) ⟨377709, by rfl⟩ : syracuseStep 1007225 = 755419) B755419
theorem B3825427 : Blo 670310 3825427 := bstep (se 1 (by rfl) ⟨2869070, by rfl⟩ : syracuseStep 3825427 = 5738141) B5738141
theorem B1007471 : Blo 670310 1007471 := bstep (se 1 (by rfl) ⟨755603, by rfl⟩ : syracuseStep 1007471 = 1511207) B1511207
theorem B5759261 : Blo 670310 5759261 := bstep (se 3 (by rfl) ⟨1079861, by rfl⟩ : syracuseStep 5759261 = 2159723) B2159723
theorem B2548219 : Blo 670310 2548219 := bstep (se 1 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 2548219 = 3822329) B3822329
theorem B1008155 : Blo 670310 1008155 := bstep (se 1 (by rfl) ⟨756116, by rfl⟩ : syracuseStep 1008155 = 1512233) B1512233
theorem B1008335 : Blo 670310 1008335 := bstep (se 1 (by rfl) ⟨756251, by rfl⟩ : syracuseStep 1008335 = 1512503) B1512503
theorem B2876111 : Blo 670310 2876111 := bstep (se 1 (by rfl) ⟨2157083, by rfl⟩ : syracuseStep 2876111 = 4314167) B4314167
theorem B1008347 : Blo 670310 1008347 := bstep (se 1 (by rfl) ⟨756260, by rfl⟩ : syracuseStep 1008347 = 1512521) B1512521
theorem B1696747 : Blo 670310 1696747 := bstep (se 1 (by rfl) ⟨1272560, by rfl⟩ : syracuseStep 1696747 = 2545121) B2545121
theorem B1008761 : Blo 670310 1008761 := bstep (se 2 (by rfl) ⟨378285, by rfl⟩ : syracuseStep 1008761 = 756571) B756571
theorem B5727617 : Blo 670310 5727617 := bstep (se 2 (by rfl) ⟨2147856, by rfl⟩ : syracuseStep 5727617 = 4295713) B4295713
theorem B1009631 : Blo 670310 1009631 := bstep (se 1 (by rfl) ⟨757223, by rfl⟩ : syracuseStep 1009631 = 1514447) B1514447
theorem B1009643 : Blo 670310 1009643 := bstep (se 1 (by rfl) ⟨757232, by rfl⟩ : syracuseStep 1009643 = 1514465) B1514465
theorem B1009691 : Blo 670310 1009691 := bstep (se 1 (by rfl) ⟨757268, by rfl⟩ : syracuseStep 1009691 = 1514537) B1514537
theorem B2156777 : Blo 670310 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B1698185 : Blo 670310 1698185 := bstep (se 2 (by rfl) ⟨636819, by rfl⟩ : syracuseStep 1698185 = 1273639) B1273639
theorem B1010057 : Blo 670310 1010057 := bstep (se 2 (by rfl) ⟨378771, by rfl⟩ : syracuseStep 1010057 = 757543) B757543
theorem B3828161 : Blo 670310 3828161 := bstep (se 2 (by rfl) ⟨1435560, by rfl⟩ : syracuseStep 3828161 = 2871121) B2871121
theorem B2878537 : Blo 670310 2878537 := bstep (se 2 (by rfl) ⟨1079451, by rfl⟩ : syracuseStep 2878537 = 2158903) B2158903
theorem B2550953 : Blo 670310 2550953 := bstep (se 2 (by rfl) ⟨956607, by rfl⟩ : syracuseStep 2550953 = 1913215) B1913215
theorem B1010999 : Blo 670310 1010999 := bstep (se 1 (by rfl) ⟨758249, by rfl⟩ : syracuseStep 1010999 = 1516499) B1516499
theorem B32664941 : Blo 670310 32664941 := bstep (se 3 (by rfl) ⟨6124676, by rfl⟩ : syracuseStep 32664941 = 12249353) B12249353
theorem B1011167 : Blo 670310 1011167 := bstep (se 1 (by rfl) ⟨758375, by rfl⟩ : syracuseStep 1011167 = 1516751) B1516751
theorem B1011383 : Blo 670310 1011383 := bstep (se 1 (by rfl) ⟨758537, by rfl⟩ : syracuseStep 1011383 = 1517075) B1517075
theorem B1535915 : Blo 670310 1535915 := bstep (se 1 (by rfl) ⟨1151936, by rfl⟩ : syracuseStep 1535915 = 2303873) B2303873
theorem B1699937 : Blo 670310 1699937 := bstep (se 2 (by rfl) ⟨637476, by rfl⟩ : syracuseStep 1699937 = 1274953) B1274953
theorem B2420999 : Blo 670310 2420999 := bstep (se 1 (by rfl) ⟨1815749, by rfl⟩ : syracuseStep 2420999 = 3631499) B3631499
theorem B1274687 : Blo 670310 1274687 := bstep (se 1 (by rfl) ⟨956015, by rfl⟩ : syracuseStep 1274687 = 1912031) B1912031
theorem B1439039 : Blo 670310 1439039 := bstep (se 1 (by rfl) ⟨1079279, by rfl⟩ : syracuseStep 1439039 = 2158559) B2158559
theorem B1701395 : Blo 670310 1701395 := bstep (se 1 (by rfl) ⟨1276046, by rfl⟩ : syracuseStep 1701395 = 2552093) B2552093
theorem B1079023 : Blo 670310 1079023 := bstep (se 1 (by rfl) ⟨809267, by rfl⟩ : syracuseStep 1079023 = 1618535) B1618535
theorem B10319633 : Blo 670310 10319633 := bstep (se 2 (by rfl) ⟨3869862, by rfl⟩ : syracuseStep 10319633 = 7739725) B7739725
theorem B2553839 : Blo 670310 2553839 := bstep (se 1 (by rfl) ⟨1915379, by rfl⟩ : syracuseStep 2553839 = 3830759) B3830759
theorem B1439927 : Blo 670310 1439927 := bstep (se 1 (by rfl) ⟨1079945, by rfl⟩ : syracuseStep 1439927 = 2159891) B2159891
theorem B1702529 : Blo 670310 1702529 := bstep (se 2 (by rfl) ⟨638448, by rfl⟩ : syracuseStep 1702529 = 1276897) B1276897
theorem B1079951 : Blo 670310 1079951 := bstep (se 1 (by rfl) ⟨809963, by rfl⟩ : syracuseStep 1079951 = 1619927) B1619927
theorem B850591 : Blo 670310 850591 := bstep (se 1 (by rfl) ⟨637943, by rfl⟩ : syracuseStep 850591 = 1275887) B1275887
theorem B5110775 : Blo 670310 5110775 := bstep (se 1 (by rfl) ⟨3833081, by rfl⟩ : syracuseStep 5110775 = 7666163) B7666163
theorem B1703339 : Blo 670310 1703339 := bstep (se 1 (by rfl) ⟨1277504, by rfl⟩ : syracuseStep 1703339 = 2555009) B2555009
theorem B4095431 : Blo 670310 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B8618237 : Blo 670310 8618237 := bstep (se 3 (by rfl) ⟨1615919, by rfl⟩ : syracuseStep 8618237 = 3231839) B3231839
theorem B852383 : Blo 670310 852383 := bstep (se 1 (by rfl) ⟨639287, by rfl⟩ : syracuseStep 852383 = 1278575) B1278575
theorem B1704635 : Blo 670310 1704635 := bstep (se 1 (by rfl) ⟨1278476, by rfl⟩ : syracuseStep 1704635 = 2556953) B2556953
theorem B2720719 : Blo 670310 2720719 := bstep (se 1 (by rfl) ⟨2040539, by rfl⟩ : syracuseStep 2720719 = 4081079) B4081079
theorem B2589887 : Blo 670310 2589887 := bstep (se 1 (by rfl) ⟨1942415, by rfl⟩ : syracuseStep 2589887 = 3884831) B3884831
theorem B2262329 : Blo 670310 2262329 := bstep (se 2 (by rfl) ⟨848373, by rfl⟩ : syracuseStep 2262329 = 1696747) B1696747
theorem B1279289 : Blo 670310 1279289 := bstep (se 2 (by rfl) ⟨479733, by rfl⟩ : syracuseStep 1279289 = 959467) B959467
theorem B4588919 : Blo 670310 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B2426431 : Blo 670310 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B3409775 : Blo 670310 3409775 := bstep (se 1 (by rfl) ⟨2557331, by rfl⟩ : syracuseStep 3409775 = 5114663) B5114663
theorem B2721691 : Blo 670310 2721691 := bstep (se 1 (by rfl) ⟨2041268, by rfl⟩ : syracuseStep 2721691 = 4082537) B4082537
theorem B1706123 : Blo 670310 1706123 := bstep (se 1 (by rfl) ⟨1279592, by rfl⟩ : syracuseStep 1706123 = 2559185) B2559185
theorem B5736743 : Blo 670310 5736743 := bstep (se 1 (by rfl) ⟨4302557, by rfl⟩ : syracuseStep 5736743 = 8605115) B8605115
theorem B2427383 : Blo 670310 2427383 := bstep (se 1 (by rfl) ⟨1820537, by rfl⟩ : syracuseStep 2427383 = 3641075) B3641075
theorem B756391 : Blo 670310 756391 := bstep (se 1 (by rfl) ⟨567293, by rfl⟩ : syracuseStep 756391 = 1134587) B1134587
theorem B4295405 : Blo 670310 4295405 := bstep (se 3 (by rfl) ⟨805388, by rfl⟩ : syracuseStep 4295405 = 1610777) B1610777
theorem B1510127 : Blo 670310 1510127 := bstep (se 1 (by rfl) ⟨1132595, by rfl⟩ : syracuseStep 1510127 = 2265191) B2265191
theorem B756463 : Blo 670310 756463 := bstep (se 1 (by rfl) ⟨567347, by rfl⟩ : syracuseStep 756463 = 1134695) B1134695
theorem B1510505 : Blo 670310 1510505 := bstep (se 2 (by rfl) ⟨566439, by rfl⟩ : syracuseStep 1510505 = 1132879) B1132879
theorem B756967 : Blo 670310 756967 := bstep (se 1 (by rfl) ⟨567725, by rfl⟩ : syracuseStep 756967 = 1135451) B1135451
theorem B1511135 : Blo 670310 1511135 := bstep (se 1 (by rfl) ⟨1133351, by rfl⟩ : syracuseStep 1511135 = 2266703) B2266703
theorem B1511387 : Blo 670310 1511387 := bstep (se 1 (by rfl) ⟨1133540, by rfl⟩ : syracuseStep 1511387 = 2267081) B2267081
theorem B7278599 : Blo 670310 7278599 := bstep (se 1 (by rfl) ⟨5458949, by rfl⟩ : syracuseStep 7278599 = 10917899) B10917899
theorem B3838049 : Blo 670310 3838049 := bstep (se 2 (by rfl) ⟨1439268, by rfl⟩ : syracuseStep 3838049 = 2878537) B2878537
theorem B1511567 : Blo 670310 1511567 := bstep (se 1 (by rfl) ⟨1133675, by rfl⟩ : syracuseStep 1511567 = 2267351) B2267351
theorem B1511657 : Blo 670310 1511657 := bstep (se 2 (by rfl) ⟨566871, by rfl⟩ : syracuseStep 1511657 = 1133743) B1133743
theorem B3412367 : Blo 670310 3412367 := bstep (se 1 (by rfl) ⟨2559275, by rfl⟩ : syracuseStep 3412367 = 5118551) B5118551
theorem B1511927 : Blo 670310 1511927 := bstep (se 1 (by rfl) ⟨1133945, by rfl⟩ : syracuseStep 1511927 = 2267891) B2267891
theorem B1512683 : Blo 670310 1512683 := bstep (se 1 (by rfl) ⟨1134512, by rfl⟩ : syracuseStep 1512683 = 2269025) B2269025
theorem B8852975 : Blo 670310 8852975 := bstep (se 1 (by rfl) ⟨6639731, by rfl⟩ : syracuseStep 8852975 = 13279463) B13279463
theorem B3839507 : Blo 670310 3839507 := bstep (se 1 (by rfl) ⟨2879630, by rfl⟩ : syracuseStep 3839507 = 5759261) B5759261
theorem B1513295 : Blo 670310 1513295 := bstep (se 1 (by rfl) ⟨1134971, by rfl⟩ : syracuseStep 1513295 = 2269943) B2269943
theorem B1513583 : Blo 670310 1513583 := bstep (se 1 (by rfl) ⟨1135187, by rfl⟩ : syracuseStep 1513583 = 2270375) B2270375
theorem B6232211 : Blo 670310 6232211 := bstep (se 1 (by rfl) ⟨4674158, by rfl⟩ : syracuseStep 6232211 = 9348317) B9348317
theorem B1513655 : Blo 670310 1513655 := bstep (se 1 (by rfl) ⟨1135241, by rfl⟩ : syracuseStep 1513655 = 2270483) B2270483
theorem B17242307 : Blo 670310 17242307 := bstep (se 1 (by rfl) ⟨12931730, by rfl⟩ : syracuseStep 17242307 = 25863461) B25863461
theorem B1514015 : Blo 670310 1514015 := bstep (se 1 (by rfl) ⟨1135511, by rfl⟩ : syracuseStep 1514015 = 2271023) B2271023
theorem B1940473 : Blo 670310 1940473 := bstep (se 2 (by rfl) ⟨727677, by rfl⟩ : syracuseStep 1940473 = 1455355) B1455355
theorem B1023943 : Blo 670310 1023943 := bstep (se 1 (by rfl) ⟨767957, by rfl⟩ : syracuseStep 1023943 = 1535915) B1535915
theorem B1613999 : Blo 670310 1613999 := bstep (se 1 (by rfl) ⟨1210499, by rfl⟩ : syracuseStep 1613999 = 2420999) B2420999
theorem B65544389 : Blo 670310 65544389 := bstep (se 4 (by rfl) ⟨6144786, by rfl⟩ : syracuseStep 65544389 = 12289573) B12289573
theorem B1909115 : Blo 670310 1909115 := bstep (se 1 (by rfl) ⟨1431836, by rfl⟩ : syracuseStep 1909115 = 2863673) B2863673
theorem B6136357 : Blo 670310 6136357 := bstep (se 4 (by rfl) ⟨575283, by rfl⟩ : syracuseStep 6136357 = 1150567) B1150567
theorem B959359 : Blo 670310 959359 := bstep (se 1 (by rfl) ⟨719519, by rfl⟩ : syracuseStep 959359 = 1439039) B1439039
theorem B959951 : Blo 670310 959951 := bstep (se 1 (by rfl) ⟨719963, by rfl⟩ : syracuseStep 959951 = 1439927) B1439927
theorem B1517039 : Blo 670310 1517039 := bstep (se 1 (by rfl) ⟨1137779, by rfl⟩ : syracuseStep 1517039 = 2275559) B2275559
theorem B23602823 : Blo 670310 23602823 := bstep (se 1 (by rfl) ⟨17702117, by rfl⟩ : syracuseStep 23602823 = 35404235) B35404235
theorem B2730287 : Blo 670310 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B7744157 : Blo 670310 7744157 := bstep (se 3 (by rfl) ⟨1452029, by rfl⟩ : syracuseStep 7744157 = 2904059) B2904059
theorem B2272319 : Blo 670310 2272319 := bstep (se 1 (by rfl) ⟨1704239, by rfl⟩ : syracuseStep 2272319 = 3408479) B3408479
theorem B17443907 : Blo 670310 17443907 := bstep (se 1 (by rfl) ⟨13082930, by rfl⟩ : syracuseStep 17443907 = 26165861) B26165861
theorem B1813673 : Blo 670310 1813673 := bstep (se 2 (by rfl) ⟨680127, by rfl⟩ : syracuseStep 1813673 = 1360255) B1360255
theorem B4304609 : Blo 670310 4304609 := bstep (se 2 (by rfl) ⟨1614228, by rfl⟩ : syracuseStep 4304609 = 3228457) B3228457
theorem B2273561 : Blo 670310 2273561 := bstep (se 2 (by rfl) ⟨852585, by rfl⟩ : syracuseStep 2273561 = 1705171) B1705171
theorem B4731301 : Blo 670310 4731301 := bstep (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) B887119
theorem B1618487 : Blo 670310 1618487 := bstep (se 1 (by rfl) ⟨1213865, by rfl⟩ : syracuseStep 1618487 = 2427731) B2427731
theorem B11678303 : Blo 670310 11678303 := bstep (se 1 (by rfl) ⟨8758727, by rfl⟩ : syracuseStep 11678303 = 17517455) B17517455
theorem B1291063 : Blo 670310 1291063 := bstep (se 1 (by rfl) ⟨968297, by rfl⟩ : syracuseStep 1291063 = 1936595) B1936595
theorem B1749815 : Blo 670310 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B8632331 : Blo 670310 8632331 := bstep (se 1 (by rfl) ⟨6474248, by rfl⟩ : syracuseStep 8632331 = 12948497) B12948497
theorem B2275721 : Blo 670310 2275721 := bstep (se 2 (by rfl) ⟨853395, by rfl⟩ : syracuseStep 2275721 = 1706791) B1706791
theorem B670655 : Blo 670310 670655 := bstep (se 1 (by rfl) ⟨502991, by rfl⟩ : syracuseStep 670655 = 1005983) B1005983
theorem B670703 : Blo 670310 670703 := bstep (se 1 (by rfl) ⟨503027, by rfl⟩ : syracuseStep 670703 = 1006055) B1006055
theorem B671199 : Blo 670310 671199 := bstep (se 1 (by rfl) ⟨503399, by rfl⟩ : syracuseStep 671199 = 1006799) B1006799
theorem B671279 : Blo 670310 671279 := bstep (se 1 (by rfl) ⟨503459, by rfl⟩ : syracuseStep 671279 = 1006919) B1006919
theorem B4308527 : Blo 670310 4308527 := bstep (se 1 (by rfl) ⟨3231395, by rfl⟩ : syracuseStep 4308527 = 6462791) B6462791
theorem B671387 : Blo 670310 671387 := bstep (se 1 (by rfl) ⟨503540, by rfl⟩ : syracuseStep 671387 = 1007081) B1007081
theorem B671483 : Blo 670310 671483 := bstep (se 1 (by rfl) ⟨503612, by rfl⟩ : syracuseStep 671483 = 1007225) B1007225
theorem B671647 : Blo 670310 671647 := bstep (se 1 (by rfl) ⟨503735, by rfl⟩ : syracuseStep 671647 = 1007471) B1007471
theorem B1228943 : Blo 670310 1228943 := bstep (se 1 (by rfl) ⟨921707, by rfl⟩ : syracuseStep 1228943 = 1843415) B1843415
theorem B672103 : Blo 670310 672103 := bstep (se 1 (by rfl) ⟨504077, by rfl⟩ : syracuseStep 672103 = 1008155) B1008155
theorem B672223 : Blo 670310 672223 := bstep (se 1 (by rfl) ⟨504167, by rfl⟩ : syracuseStep 672223 = 1008335) B1008335
theorem B1917407 : Blo 670310 1917407 := bstep (se 1 (by rfl) ⟨1438055, by rfl⟩ : syracuseStep 1917407 = 2876111) B2876111
theorem B672231 : Blo 670310 672231 := bstep (se 1 (by rfl) ⟨504173, by rfl⟩ : syracuseStep 672231 = 1008347) B1008347
theorem B13091503 : Blo 670310 13091503 := bstep (se 1 (by rfl) ⟨9818627, by rfl⟩ : syracuseStep 13091503 = 19637255) B19637255
theorem B672507 : Blo 670310 672507 := bstep (se 1 (by rfl) ⟨504380, by rfl⟩ : syracuseStep 672507 = 1008761) B1008761
theorem B3818411 : Blo 670310 3818411 := bstep (se 1 (by rfl) ⟨2863808, by rfl⟩ : syracuseStep 3818411 = 5727617) B5727617
theorem B673087 : Blo 670310 673087 := bstep (se 1 (by rfl) ⟨504815, by rfl⟩ : syracuseStep 673087 = 1009631) B1009631
theorem B673095 : Blo 670310 673095 := bstep (se 1 (by rfl) ⟨504821, by rfl⟩ : syracuseStep 673095 = 1009643) B1009643
theorem B673127 : Blo 670310 673127 := bstep (se 1 (by rfl) ⟨504845, by rfl⟩ : syracuseStep 673127 = 1009691) B1009691
theorem B1132123 : Blo 670310 1132123 := bstep (se 1 (by rfl) ⟨849092, by rfl⟩ : syracuseStep 1132123 = 1698185) B1698185
theorem B673371 : Blo 670310 673371 := bstep (se 1 (by rfl) ⟨505028, by rfl⟩ : syracuseStep 673371 = 1010057) B1010057
theorem B673999 : Blo 670310 673999 := bstep (se 1 (by rfl) ⟨505499, by rfl⟩ : syracuseStep 673999 = 1010999) B1010999
theorem B21776627 : Blo 670310 21776627 := bstep (se 1 (by rfl) ⟨16332470, by rfl⟩ : syracuseStep 21776627 = 32664941) B32664941
theorem B674111 : Blo 670310 674111 := bstep (se 1 (by rfl) ⟨505583, by rfl⟩ : syracuseStep 674111 = 1011167) B1011167
theorem B4835791 : Blo 670310 4835791 := bstep (se 1 (by rfl) ⟨3626843, by rfl⟩ : syracuseStep 4835791 = 7253687) B7253687
theorem B674255 : Blo 670310 674255 := bstep (se 1 (by rfl) ⟨505691, by rfl⟩ : syracuseStep 674255 = 1011383) B1011383
theorem B2149087 : Blo 670310 2149087 := bstep (se 1 (by rfl) ⟨1611815, by rfl⟩ : syracuseStep 2149087 = 3223631) B3223631
theorem B1133291 : Blo 670310 1133291 := bstep (se 1 (by rfl) ⟨849968, by rfl⟩ : syracuseStep 1133291 = 1699937) B1699937
theorem B5098625 : Blo 670310 5098625 := bstep (se 2 (by rfl) ⟨1911984, by rfl⟩ : syracuseStep 5098625 = 3823969) B3823969
theorem B3394871 : Blo 670310 3394871 := bstep (se 1 (by rfl) ⟨2546153, by rfl⟩ : syracuseStep 3394871 = 5092307) B5092307
theorem B2149753 : Blo 670310 2149753 := bstep (se 2 (by rfl) ⟨806157, by rfl⟩ : syracuseStep 2149753 = 1612315) B1612315
theorem B1134121 : Blo 670310 1134121 := bstep (se 2 (by rfl) ⟨425295, by rfl⟩ : syracuseStep 1134121 = 850591) B850591
theorem B1134263 : Blo 670310 1134263 := bstep (se 1 (by rfl) ⟨850697, by rfl⟩ : syracuseStep 1134263 = 1701395) B1701395
theorem B1135019 : Blo 670310 1135019 := bstep (se 1 (by rfl) ⟨851264, by rfl⟩ : syracuseStep 1135019 = 1702529) B1702529
theorem B9720485 : Blo 670310 9720485 := bstep (se 4 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 9720485 = 1822591) B1822591
theorem B1135559 : Blo 670310 1135559 := bstep (se 1 (by rfl) ⟨851669, by rfl⟩ : syracuseStep 1135559 = 1703339) B1703339
theorem B5100569 : Blo 670310 5100569 := bstep (se 2 (by rfl) ⟨1912713, by rfl⟩ : syracuseStep 5100569 = 3825427) B3825427
theorem B3396815 : Blo 670310 3396815 := bstep (se 1 (by rfl) ⟨2547611, by rfl⟩ : syracuseStep 3396815 = 5095223) B5095223
theorem B906491 : Blo 670310 906491 := bstep (se 1 (by rfl) ⟨679868, by rfl⟩ : syracuseStep 906491 = 1359737) B1359737
theorem B13129381 : Blo 670310 13129381 := bstep (se 4 (by rfl) ⟨1230879, by rfl⟩ : syracuseStep 13129381 = 2461759) B2461759
theorem B2152111 : Blo 670310 2152111 := bstep (se 1 (by rfl) ⟨1614083, by rfl⟩ : syracuseStep 2152111 = 3228167) B3228167
theorem B3397625 : Blo 670310 3397625 := bstep (se 2 (by rfl) ⟨1274109, by rfl⟩ : syracuseStep 3397625 = 2548219) B2548219
theorem B1005695 : Blo 670310 1005695 := bstep (se 1 (by rfl) ⟨754271, by rfl⟩ : syracuseStep 1005695 = 1508543) B1508543
theorem B1005791 : Blo 670310 1005791 := bstep (se 1 (by rfl) ⟨754343, by rfl⟩ : syracuseStep 1005791 = 1508687) B1508687
theorem B1005851 : Blo 670310 1005851 := bstep (se 1 (by rfl) ⟨754388, by rfl⟩ : syracuseStep 1005851 = 1508777) B1508777
theorem B1432007 : Blo 670310 1432007 := bstep (se 1 (by rfl) ⟨1074005, by rfl⟩ : syracuseStep 1432007 = 2148011) B2148011
theorem B2152919 : Blo 670310 2152919 := bstep (se 1 (by rfl) ⟨1614689, by rfl⟩ : syracuseStep 2152919 = 3229379) B3229379
theorem B20666843 : Blo 670310 20666843 := bstep (se 1 (by rfl) ⟨15500132, by rfl⟩ : syracuseStep 20666843 = 31000265) B31000265
theorem B1006175 : Blo 670310 1006175 := bstep (se 1 (by rfl) ⟨754631, by rfl⟩ : syracuseStep 1006175 = 1509263) B1509263
theorem B1006271 : Blo 670310 1006271 := bstep (se 1 (by rfl) ⟨754703, by rfl⟩ : syracuseStep 1006271 = 1509407) B1509407
theorem B1006313 : Blo 670310 1006313 := bstep (se 2 (by rfl) ⟨377367, by rfl⟩ : syracuseStep 1006313 = 754735) B754735
theorem B809767 : Blo 670310 809767 := bstep (se 1 (by rfl) ⟨607325, by rfl⟩ : syracuseStep 809767 = 1214651) B1214651
theorem B908095 : Blo 670310 908095 := bstep (se 1 (by rfl) ⟨681071, by rfl⟩ : syracuseStep 908095 = 1362143) B1362143
theorem B1006439 : Blo 670310 1006439 := bstep (se 1 (by rfl) ⟨754829, by rfl⟩ : syracuseStep 1006439 = 1509659) B1509659
theorem B1006505 : Blo 670310 1006505 := bstep (se 2 (by rfl) ⟨377439, by rfl⟩ : syracuseStep 1006505 = 754879) B754879
theorem B1137577 : Blo 670310 1137577 := bstep (se 2 (by rfl) ⟨426591, by rfl⟩ : syracuseStep 1137577 = 853183) B853183
theorem B2546747 : Blo 670310 2546747 := bstep (se 1 (by rfl) ⟨1910060, by rfl⟩ : syracuseStep 2546747 = 3820121) B3820121
theorem B1006655 : Blo 670310 1006655 := bstep (se 1 (by rfl) ⟨754991, by rfl⟩ : syracuseStep 1006655 = 1509983) B1509983
theorem B1006697 : Blo 670310 1006697 := bstep (se 2 (by rfl) ⟨377511, by rfl⟩ : syracuseStep 1006697 = 755023) B755023
theorem B1006823 : Blo 670310 1006823 := bstep (se 1 (by rfl) ⟨755117, by rfl⟩ : syracuseStep 1006823 = 1510235) B1510235
theorem B2547035 : Blo 670310 2547035 := bstep (se 1 (by rfl) ⟨1910276, by rfl⟩ : syracuseStep 2547035 = 3820553) B3820553
theorem B7003579 : Blo 670310 7003579 := bstep (se 1 (by rfl) ⟨5252684, by rfl⟩ : syracuseStep 7003579 = 10505369) B10505369
theorem B1007327 : Blo 670310 1007327 := bstep (se 1 (by rfl) ⟨755495, by rfl⟩ : syracuseStep 1007327 = 1510991) B1510991
theorem B3399407 : Blo 670310 3399407 := bstep (se 1 (by rfl) ⟨2549555, by rfl⟩ : syracuseStep 3399407 = 5099111) B5099111
theorem B5103485 : Blo 670310 5103485 := bstep (se 3 (by rfl) ⟨956903, by rfl⟩ : syracuseStep 5103485 = 1913807) B1913807
theorem B1728479 : Blo 670310 1728479 := bstep (se 1 (by rfl) ⟨1296359, by rfl⟩ : syracuseStep 1728479 = 2592719) B2592719
theorem B1007657 : Blo 670310 1007657 := bstep (se 2 (by rfl) ⟨377871, by rfl⟩ : syracuseStep 1007657 = 755743) B755743
theorem B1007687 : Blo 670310 1007687 := bstep (se 1 (by rfl) ⟨755765, by rfl⟩ : syracuseStep 1007687 = 1511531) B1511531
theorem B1007723 : Blo 670310 1007723 := bstep (se 1 (by rfl) ⟨755792, by rfl⟩ : syracuseStep 1007723 = 1511585) B1511585
theorem B1007807 : Blo 670310 1007807 := bstep (se 1 (by rfl) ⟨755855, by rfl⟩ : syracuseStep 1007807 = 1511711) B1511711
theorem B2548007 : Blo 670310 2548007 := bstep (se 1 (by rfl) ⟨1911005, by rfl⟩ : syracuseStep 2548007 = 3822011) B3822011
theorem B1007993 : Blo 670310 1007993 := bstep (se 2 (by rfl) ⟨377997, by rfl⟩ : syracuseStep 1007993 = 755995) B755995
theorem B1008287 : Blo 670310 1008287 := bstep (se 1 (by rfl) ⟨756215, by rfl⟩ : syracuseStep 1008287 = 1512431) B1512431
theorem B2548691 : Blo 670310 2548691 := bstep (se 1 (by rfl) ⟨1911518, by rfl⟩ : syracuseStep 2548691 = 3823037) B3823037
theorem B1008623 : Blo 670310 1008623 := bstep (se 1 (by rfl) ⟨756467, by rfl⟩ : syracuseStep 1008623 = 1512935) B1512935
theorem B1696859 : Blo 670310 1696859 := bstep (se 1 (by rfl) ⟨1272644, by rfl⟩ : syracuseStep 1696859 = 2545289) B2545289
theorem B1008731 : Blo 670310 1008731 := bstep (se 1 (by rfl) ⟨756548, by rfl⟩ : syracuseStep 1008731 = 1513097) B1513097
theorem B1008743 : Blo 670310 1008743 := bstep (se 1 (by rfl) ⟨756557, by rfl⟩ : syracuseStep 1008743 = 1513115) B1513115
theorem B5465245 : Blo 670310 5465245 := bstep (se 3 (by rfl) ⟨1024733, by rfl⟩ : syracuseStep 5465245 = 2049467) B2049467
theorem B1008875 : Blo 670310 1008875 := bstep (se 1 (by rfl) ⟨756656, by rfl⟩ : syracuseStep 1008875 = 1513313) B1513313
theorem B1009007 : Blo 670310 1009007 := bstep (se 1 (by rfl) ⟨756755, by rfl⟩ : syracuseStep 1009007 = 1513511) B1513511
theorem B2549191 : Blo 670310 2549191 := bstep (se 1 (by rfl) ⟨1911893, by rfl⟩ : syracuseStep 2549191 = 3823787) B3823787
theorem B3827159 : Blo 670310 3827159 := bstep (se 1 (by rfl) ⟨2870369, by rfl⟩ : syracuseStep 3827159 = 5740739) B5740739
theorem B1009127 : Blo 670310 1009127 := bstep (se 1 (by rfl) ⟨756845, by rfl⟩ : syracuseStep 1009127 = 1513691) B1513691
theorem B2156033 : Blo 670310 2156033 := bstep (se 2 (by rfl) ⟨808512, by rfl⟩ : syracuseStep 2156033 = 1617025) B1617025
theorem B87156323 : Blo 670310 87156323 := bstep (se 1 (by rfl) ⟨65367242, by rfl⟩ : syracuseStep 87156323 = 130734485) B130734485
theorem B1009259 : Blo 670310 1009259 := bstep (se 1 (by rfl) ⟨756944, by rfl⟩ : syracuseStep 1009259 = 1513889) B1513889
theorem B1009307 : Blo 670310 1009307 := bstep (se 1 (by rfl) ⟨756980, by rfl⟩ : syracuseStep 1009307 = 1513961) B1513961
theorem B5727995 : Blo 670310 5727995 := bstep (se 1 (by rfl) ⟨4295996, by rfl⟩ : syracuseStep 5727995 = 8591993) B8591993
theorem B1009529 : Blo 670310 1009529 := bstep (se 2 (by rfl) ⟨378573, by rfl⟩ : syracuseStep 1009529 = 757147) B757147
theorem B2156519 : Blo 670310 2156519 := bstep (se 1 (by rfl) ⟨1617389, by rfl⟩ : syracuseStep 2156519 = 3234779) B3234779
theorem B2549951 : Blo 670310 2549951 := bstep (se 1 (by rfl) ⟨1912463, by rfl⟩ : syracuseStep 2549951 = 3824927) B3824927
theorem B3238393 : Blo 670310 3238393 := bstep (se 2 (by rfl) ⟨1214397, by rfl⟩ : syracuseStep 3238393 = 2428795) B2428795
theorem B1010279 : Blo 670310 1010279 := bstep (se 1 (by rfl) ⟨757709, by rfl⟩ : syracuseStep 1010279 = 1515419) B1515419
theorem B1272667 : Blo 670310 1272667 := bstep (se 1 (by rfl) ⟨954500, by rfl⟩ : syracuseStep 1272667 = 1909001) B1909001
theorem B1010555 : Blo 670310 1010555 := bstep (se 1 (by rfl) ⟨757916, by rfl⟩ : syracuseStep 1010555 = 1515833) B1515833
theorem B1272827 : Blo 670310 1272827 := bstep (se 1 (by rfl) ⟨954620, by rfl⟩ : syracuseStep 1272827 = 1909241) B1909241
theorem B1010825 : Blo 670310 1010825 := bstep (se 2 (by rfl) ⟨379059, by rfl⟩ : syracuseStep 1010825 = 758119) B758119
theorem B1010879 : Blo 670310 1010879 := bstep (se 1 (by rfl) ⟨758159, by rfl⟩ : syracuseStep 1010879 = 1516319) B1516319
theorem B3632363 : Blo 670310 3632363 := bstep (se 1 (by rfl) ⟨2724272, by rfl⟩ : syracuseStep 3632363 = 5448545) B5448545
theorem B1011419 : Blo 670310 1011419 := bstep (se 1 (by rfl) ⟨758564, by rfl⟩ : syracuseStep 1011419 = 1517129) B1517129
theorem B1437851 : Blo 670310 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B2552107 : Blo 670310 2552107 := bstep (se 1 (by rfl) ⟨1914080, by rfl⟩ : syracuseStep 2552107 = 3828161) B3828161
theorem B2879869 : Blo 670310 2879869 := bstep (se 3 (by rfl) ⟨539975, by rfl⟩ : syracuseStep 2879869 = 1079951) B1079951
theorem B1700635 : Blo 670310 1700635 := bstep (se 1 (by rfl) ⟨1275476, by rfl⟩ : syracuseStep 1700635 = 2550953) B2550953
theorem B58782665 : Blo 670310 58782665 := bstep (se 2 (by rfl) ⟨22043499, by rfl⟩ : syracuseStep 58782665 = 44086999) B44086999
theorem B1438697 : Blo 670310 1438697 := bstep (se 2 (by rfl) ⟨539511, by rfl⟩ : syracuseStep 1438697 = 1079023) B1079023
theorem B1078427 : Blo 670310 1078427 := bstep (se 1 (by rfl) ⟨808820, by rfl⟩ : syracuseStep 1078427 = 1617641) B1617641
theorem B1078439 : Blo 670310 1078439 := bstep (se 1 (by rfl) ⟨808829, by rfl⟩ : syracuseStep 1078439 = 1617659) B1617659
theorem B1079131 : Blo 670310 1079131 := bstep (se 1 (by rfl) ⟨809348, by rfl⟩ : syracuseStep 1079131 = 1618697) B1618697
theorem B849791 : Blo 670310 849791 := bstep (se 1 (by rfl) ⟨637343, by rfl⟩ : syracuseStep 849791 = 1274687) B1274687
theorem B4356299 : Blo 670310 4356299 := bstep (se 1 (by rfl) ⟨3267224, by rfl⟩ : syracuseStep 4356299 = 6534449) B6534449
theorem B6879755 : Blo 670310 6879755 := bstep (se 1 (by rfl) ⟨5159816, by rfl⟩ : syracuseStep 6879755 = 10319633) B10319633
theorem B66484799 : Blo 670310 66484799 := bstep (se 1 (by rfl) ⟨49863599, by rfl⟩ : syracuseStep 66484799 = 99727199) B99727199
theorem B1702559 : Blo 670310 1702559 := bstep (se 1 (by rfl) ⟨1276919, by rfl⟩ : syracuseStep 1702559 = 2553839) B2553839
theorem B12286721 : Blo 670310 12286721 := bstep (se 2 (by rfl) ⟨4607520, by rfl⟩ : syracuseStep 12286721 = 9215041) B9215041
theorem B3439759 : Blo 670310 3439759 := bstep (se 1 (by rfl) ⟨2579819, by rfl⟩ : syracuseStep 3439759 = 5159639) B5159639
theorem B3407183 : Blo 670310 3407183 := bstep (se 1 (by rfl) ⟨2555387, by rfl⟩ : syracuseStep 3407183 = 5110775) B5110775
theorem B3833243 : Blo 670310 3833243 := bstep (se 1 (by rfl) ⟨2874932, by rfl⟩ : syracuseStep 3833243 = 5749865) B5749865
theorem B17268551 : Blo 670310 17268551 := bstep (se 1 (by rfl) ⟨12951413, by rfl⟩ : syracuseStep 17268551 = 25902827) B25902827
theorem B8617873 : Blo 670310 8617873 := bstep (se 2 (by rfl) ⟨3231702, by rfl⟩ : syracuseStep 8617873 = 6463405) B6463405
theorem B1278271 : Blo 670310 1278271 := bstep (se 1 (by rfl) ⟨958703, by rfl⟩ : syracuseStep 1278271 = 1917407) B1917407
theorem B3277181 : Blo 670310 3277181 := bstep (se 3 (by rfl) ⟨614471, by rfl⟩ : syracuseStep 3277181 = 1228943) B1228943
theorem B1508219 : Blo 670310 1508219 := bstep (se 1 (by rfl) ⟨1131164, by rfl⟩ : syracuseStep 1508219 = 2262329) B2262329
theorem B852859 : Blo 670310 852859 := bstep (se 1 (by rfl) ⟨639644, by rfl⟩ : syracuseStep 852859 = 1279289) B1279289
theorem B1279145 : Blo 670310 1279145 := bstep (se 2 (by rfl) ⟨479679, by rfl⟩ : syracuseStep 1279145 = 959359) B959359
theorem B14517751 : Blo 670310 14517751 := bstep (se 1 (by rfl) ⟨10888313, by rfl⟩ : syracuseStep 14517751 = 21776627) B21776627
theorem B755527 : Blo 670310 755527 := bstep (se 1 (by rfl) ⟨566645, by rfl⟩ : syracuseStep 755527 = 1133291) B1133291
theorem B1509497 : Blo 670310 1509497 := bstep (se 2 (by rfl) ⟨566061, by rfl⟩ : syracuseStep 1509497 = 1132123) B1132123
theorem B25233605 : Blo 670310 25233605 := bstep (se 4 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 25233605 = 4731301) B4731301
theorem B2263247 : Blo 670310 2263247 := bstep (se 1 (by rfl) ⟨1697435, by rfl⟩ : syracuseStep 2263247 = 3394871) B3394871
theorem B756175 : Blo 670310 756175 := bstep (se 1 (by rfl) ⟨567131, by rfl⟩ : syracuseStep 756175 = 1134263) B1134263
theorem B4852399 : Blo 670310 4852399 := bstep (se 1 (by rfl) ⟨3639299, by rfl⟩ : syracuseStep 4852399 = 7278599) B7278599
theorem B2558699 : Blo 670310 2558699 := bstep (se 1 (by rfl) ⟨1919024, by rfl⟩ : syracuseStep 2558699 = 3838049) B3838049
theorem B756679 : Blo 670310 756679 := bstep (se 1 (by rfl) ⟨567509, by rfl⟩ : syracuseStep 756679 = 1135019) B1135019
theorem B757039 : Blo 670310 757039 := bstep (se 1 (by rfl) ⟨567779, by rfl⟩ : syracuseStep 757039 = 1135559) B1135559
theorem B2264543 : Blo 670310 2264543 := bstep (se 1 (by rfl) ⟨1698407, by rfl⟩ : syracuseStep 2264543 = 3396815) B3396815
theorem B5901983 : Blo 670310 5901983 := bstep (se 1 (by rfl) ⟨4426487, by rfl⟩ : syracuseStep 5901983 = 8852975) B8852975
theorem B2559671 : Blo 670310 2559671 := bstep (se 1 (by rfl) ⟨1919753, by rfl⟩ : syracuseStep 2559671 = 3839507) B3839507
theorem B2559869 : Blo 670310 2559869 := bstep (se 3 (by rfl) ⟨479975, by rfl⟩ : syracuseStep 2559869 = 959951) B959951
theorem B2265083 : Blo 670310 2265083 := bstep (se 1 (by rfl) ⟨1698812, by rfl⟩ : syracuseStep 2265083 = 3397625) B3397625
theorem B954671 : Blo 670310 954671 := bstep (se 1 (by rfl) ⟨716003, by rfl⟩ : syracuseStep 954671 = 1432007) B1432007
theorem B1512161 : Blo 670310 1512161 := bstep (se 2 (by rfl) ⟨567060, by rfl⟩ : syracuseStep 1512161 = 1134121) B1134121
theorem B2266109 : Blo 670310 2266109 := bstep (se 3 (by rfl) ⟨424895, by rfl⟩ : syracuseStep 2266109 = 849791) B849791
theorem B2266271 : Blo 670310 2266271 := bstep (se 1 (by rfl) ⟨1699703, by rfl⟩ : syracuseStep 2266271 = 3399407) B3399407
theorem B1152319 : Blo 670310 1152319 := bstep (se 1 (by rfl) ⟨864239, by rfl⟩ : syracuseStep 1152319 = 1728479) B1728479
theorem B3839825 : Blo 670310 3839825 := bstep (se 2 (by rfl) ⟨1439934, by rfl⟩ : syracuseStep 3839825 = 2879869) B2879869
theorem B7280765 : Blo 670310 7280765 := bstep (se 3 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 7280765 = 2730287) B2730287
theorem B2267513 : Blo 670310 2267513 := bstep (se 2 (by rfl) ⟨850317, by rfl⟩ : syracuseStep 2267513 = 1700635) B1700635
theorem B58104215 : Blo 670310 58104215 := bstep (se 1 (by rfl) ⟨43578161, by rfl⟩ : syracuseStep 58104215 = 87156323) B87156323
theorem B15735215 : Blo 670310 15735215 := bstep (se 1 (by rfl) ⟨11801411, by rfl⟩ : syracuseStep 15735215 = 23602823) B23602823
theorem B5741117 : Blo 670310 5741117 := bstep (se 3 (by rfl) ⟨1076459, by rfl⟩ : syracuseStep 5741117 = 2152919) B2152919
theorem B1514879 : Blo 670310 1514879 := bstep (se 1 (by rfl) ⟨1136159, by rfl⟩ : syracuseStep 1514879 = 2272319) B2272319
theorem B17505841 : Blo 670310 17505841 := bstep (se 2 (by rfl) ⟨6564690, by rfl⟩ : syracuseStep 17505841 = 13129381) B13129381
theorem B958567 : Blo 670310 958567 := bstep (se 1 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 958567 = 1437851) B1437851
theorem B1515707 : Blo 670310 1515707 := bstep (se 1 (by rfl) ⟨1136780, by rfl⟩ : syracuseStep 1515707 = 2273561) B2273561
theorem B959131 : Blo 670310 959131 := bstep (se 1 (by rfl) ⟨719348, by rfl⟩ : syracuseStep 959131 = 1438697) B1438697
theorem B1516769 : Blo 670310 1516769 := bstep (se 2 (by rfl) ⟨568788, by rfl⟩ : syracuseStep 1516769 = 1137577) B1137577
theorem B1517147 : Blo 670310 1517147 := bstep (se 1 (by rfl) ⟨1137860, by rfl⟩ : syracuseStep 1517147 = 2275721) B2275721
theorem B2271455 : Blo 670310 2271455 := bstep (se 1 (by rfl) ⟨1703591, by rfl⟩ : syracuseStep 2271455 = 3407183) B3407183
theorem B11512367 : Blo 670310 11512367 := bstep (se 1 (by rfl) ⟨8634275, by rfl⟩ : syracuseStep 11512367 = 17268551) B17268551
theorem B5745491 : Blo 670310 5745491 := bstep (se 1 (by rfl) ⟨4309118, by rfl⟩ : syracuseStep 5745491 = 8618237) B8618237
theorem B3059279 : Blo 670310 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B2273021 : Blo 670310 2273021 := bstep (se 3 (by rfl) ⟨426191, by rfl⟩ : syracuseStep 2273021 = 852383) B852383
theorem B2273183 : Blo 670310 2273183 := bstep (se 1 (by rfl) ⟨1704887, by rfl⟩ : syracuseStep 2273183 = 3409775) B3409775
theorem B7286993 : Blo 670310 7286993 := bstep (se 2 (by rfl) ⟨2732622, by rfl⟩ : syracuseStep 7286993 = 5465245) B5465245
theorem B31142141 : Blo 670310 31142141 := bstep (se 3 (by rfl) ⟨5839151, by rfl⟩ : syracuseStep 31142141 = 11678303) B11678303
theorem B1618255 : Blo 670310 1618255 := bstep (se 1 (by rfl) ⟨1213691, by rfl⟩ : syracuseStep 1618255 = 2427383) B2427383
theorem B2863603 : Blo 670310 2863603 := bstep (se 1 (by rfl) ⟨2147702, by rfl⟩ : syracuseStep 2863603 = 4295405) B4295405
theorem B2274911 : Blo 670310 2274911 := bstep (se 1 (by rfl) ⟨1706183, by rfl⟩ : syracuseStep 2274911 = 3412367) B3412367
theorem B2865449 : Blo 670310 2865449 := bstep (se 2 (by rfl) ⟨1074543, by rfl⟩ : syracuseStep 2865449 = 2149087) B2149087
theorem B670463 : Blo 670310 670463 := bstep (se 1 (by rfl) ⟨502847, by rfl⟩ : syracuseStep 670463 = 1005695) B1005695
theorem B670527 : Blo 670310 670527 := bstep (se 1 (by rfl) ⟨502895, by rfl⟩ : syracuseStep 670527 = 1005791) B1005791
theorem B670567 : Blo 670310 670567 := bstep (se 1 (by rfl) ⟨502925, by rfl⟩ : syracuseStep 670567 = 1005851) B1005851
theorem B13777895 : Blo 670310 13777895 := bstep (se 1 (by rfl) ⟨10333421, by rfl⟩ : syracuseStep 13777895 = 20666843) B20666843
theorem B670783 : Blo 670310 670783 := bstep (se 1 (by rfl) ⟨503087, by rfl⟩ : syracuseStep 670783 = 1006175) B1006175
theorem B670847 : Blo 670310 670847 := bstep (se 1 (by rfl) ⟨503135, by rfl⟩ : syracuseStep 670847 = 1006271) B1006271
theorem B670875 : Blo 670310 670875 := bstep (se 1 (by rfl) ⟨503156, by rfl⟩ : syracuseStep 670875 = 1006313) B1006313
theorem B2866337 : Blo 670310 2866337 := bstep (se 2 (by rfl) ⟨1074876, by rfl⟩ : syracuseStep 2866337 = 2149753) B2149753
theorem B670959 : Blo 670310 670959 := bstep (se 1 (by rfl) ⟨503219, by rfl⟩ : syracuseStep 670959 = 1006439) B1006439
theorem B671003 : Blo 670310 671003 := bstep (se 1 (by rfl) ⟨503252, by rfl⟩ : syracuseStep 671003 = 1006505) B1006505
theorem B671103 : Blo 670310 671103 := bstep (se 1 (by rfl) ⟨503327, by rfl⟩ : syracuseStep 671103 = 1006655) B1006655
theorem B671131 : Blo 670310 671131 := bstep (se 1 (by rfl) ⟨503348, by rfl⟩ : syracuseStep 671131 = 1006697) B1006697
theorem B671215 : Blo 670310 671215 := bstep (se 1 (by rfl) ⟨503411, by rfl⟩ : syracuseStep 671215 = 1006823) B1006823
theorem B671551 : Blo 670310 671551 := bstep (se 1 (by rfl) ⟨503663, by rfl⟩ : syracuseStep 671551 = 1007327) B1007327
theorem B671771 : Blo 670310 671771 := bstep (se 1 (by rfl) ⟨503828, by rfl⟩ : syracuseStep 671771 = 1007657) B1007657
theorem B671791 : Blo 670310 671791 := bstep (se 1 (by rfl) ⟨503843, by rfl⟩ : syracuseStep 671791 = 1007687) B1007687
theorem B671815 : Blo 670310 671815 := bstep (se 1 (by rfl) ⟨503861, by rfl⟩ : syracuseStep 671815 = 1007723) B1007723
theorem B671871 : Blo 670310 671871 := bstep (se 1 (by rfl) ⟨503903, by rfl⟩ : syracuseStep 671871 = 1007807) B1007807
theorem B43696259 : Blo 670310 43696259 := bstep (se 1 (by rfl) ⟨32772194, by rfl⟩ : syracuseStep 43696259 = 65544389) B65544389
theorem B671995 : Blo 670310 671995 := bstep (se 1 (by rfl) ⟨503996, by rfl⟩ : syracuseStep 671995 = 1007993) B1007993
theorem B672191 : Blo 670310 672191 := bstep (se 1 (by rfl) ⟨504143, by rfl⟩ : syracuseStep 672191 = 1008287) B1008287
theorem B11616797 : Blo 670310 11616797 := bstep (se 3 (by rfl) ⟨2178149, by rfl⟩ : syracuseStep 11616797 = 4356299) B4356299
theorem B672415 : Blo 670310 672415 := bstep (se 1 (by rfl) ⟨504311, by rfl⟩ : syracuseStep 672415 = 1008623) B1008623
theorem B1131239 : Blo 670310 1131239 := bstep (se 1 (by rfl) ⟨848429, by rfl⟩ : syracuseStep 1131239 = 1696859) B1696859
theorem B672487 : Blo 670310 672487 := bstep (se 1 (by rfl) ⟨504365, by rfl⟩ : syracuseStep 672487 = 1008731) B1008731
theorem B672495 : Blo 670310 672495 := bstep (se 1 (by rfl) ⟨504371, by rfl⟩ : syracuseStep 672495 = 1008743) B1008743
theorem B672583 : Blo 670310 672583 := bstep (se 1 (by rfl) ⟨504437, by rfl⟩ : syracuseStep 672583 = 1008875) B1008875
theorem B672671 : Blo 670310 672671 := bstep (se 1 (by rfl) ⟨504503, by rfl⟩ : syracuseStep 672671 = 1009007) B1009007
theorem B672751 : Blo 670310 672751 := bstep (se 1 (by rfl) ⟨504563, by rfl⟩ : syracuseStep 672751 = 1009127) B1009127
theorem B672839 : Blo 670310 672839 := bstep (se 1 (by rfl) ⟨504629, by rfl⟩ : syracuseStep 672839 = 1009259) B1009259
theorem B1721417 : Blo 670310 1721417 := bstep (se 2 (by rfl) ⟨645531, by rfl⟩ : syracuseStep 1721417 = 1291063) B1291063
theorem B672871 : Blo 670310 672871 := bstep (se 1 (by rfl) ⟨504653, by rfl⟩ : syracuseStep 672871 = 1009307) B1009307
theorem B3818663 : Blo 670310 3818663 := bstep (se 1 (by rfl) ⟨2863997, by rfl⟩ : syracuseStep 3818663 = 5727995) B5727995
theorem B673019 : Blo 670310 673019 := bstep (se 1 (by rfl) ⟨504764, by rfl⟩ : syracuseStep 673019 = 1009529) B1009529
theorem B673519 : Blo 670310 673519 := bstep (se 1 (by rfl) ⟨505139, by rfl⟩ : syracuseStep 673519 = 1010279) B1010279
theorem B5162771 : Blo 670310 5162771 := bstep (se 1 (by rfl) ⟨3872078, by rfl⟩ : syracuseStep 5162771 = 7744157) B7744157
theorem B673703 : Blo 670310 673703 := bstep (se 1 (by rfl) ⟨505277, by rfl⟩ : syracuseStep 673703 = 1010555) B1010555
theorem B673883 : Blo 670310 673883 := bstep (se 1 (by rfl) ⟨505412, by rfl⟩ : syracuseStep 673883 = 1010825) B1010825
theorem B673919 : Blo 670310 673919 := bstep (se 1 (by rfl) ⟨505439, by rfl⟩ : syracuseStep 673919 = 1010879) B1010879
theorem B2869481 : Blo 670310 2869481 := bstep (se 2 (by rfl) ⟨1076055, by rfl⟩ : syracuseStep 2869481 = 2152111) B2152111
theorem B674279 : Blo 670310 674279 := bstep (se 1 (by rfl) ⟨505709, by rfl⟩ : syracuseStep 674279 = 1011419) B1011419
theorem B2869739 : Blo 670310 2869739 := bstep (se 1 (by rfl) ⟨2152304, by rfl⟩ : syracuseStep 2869739 = 4304609) B4304609
theorem B1166543 : Blo 670310 1166543 := bstep (se 1 (by rfl) ⟨874907, by rfl⟩ : syracuseStep 1166543 = 1749815) B1749815
theorem B5754887 : Blo 670310 5754887 := bstep (se 1 (by rfl) ⟨4316165, by rfl⟩ : syracuseStep 5754887 = 8632331) B8632331
theorem B44323199 : Blo 670310 44323199 := bstep (se 1 (by rfl) ⟨33242399, by rfl⟩ : syracuseStep 44323199 = 66484799) B66484799
theorem B1135039 : Blo 670310 1135039 := bstep (se 1 (by rfl) ⟨851279, by rfl⟩ : syracuseStep 1135039 = 1702559) B1702559
theorem B2872351 : Blo 670310 2872351 := bstep (se 1 (by rfl) ⟨2154263, by rfl⟩ : syracuseStep 2872351 = 4308527) B4308527
theorem B11490497 : Blo 670310 11490497 := bstep (se 2 (by rfl) ⟨4308936, by rfl⟩ : syracuseStep 11490497 = 8617873) B8617873
theorem B1365257 : Blo 670310 1365257 := bstep (se 2 (by rfl) ⟨511971, by rfl⟩ : syracuseStep 1365257 = 1023943) B1023943
theorem B1136423 : Blo 670310 1136423 := bstep (se 1 (by rfl) ⟨852317, by rfl⟩ : syracuseStep 1136423 = 1704635) B1704635
theorem B2545607 : Blo 670310 2545607 := bstep (se 1 (by rfl) ⟨1909205, by rfl⟩ : syracuseStep 2545607 = 3818411) B3818411
theorem B8181809 : Blo 670310 8181809 := bstep (se 2 (by rfl) ⟨3068178, by rfl⟩ : syracuseStep 8181809 = 6136357) B6136357
theorem B1726591 : Blo 670310 1726591 := bstep (se 1 (by rfl) ⟨1294943, by rfl⟩ : syracuseStep 1726591 = 2589887) B2589887
theorem B17455337 : Blo 670310 17455337 := bstep (se 2 (by rfl) ⟨6545751, by rfl⟩ : syracuseStep 17455337 = 13091503) B13091503
theorem B3627625 : Blo 670310 3627625 := bstep (se 2 (by rfl) ⟨1360359, by rfl⟩ : syracuseStep 3627625 = 2720719) B2720719
theorem B1137415 : Blo 670310 1137415 := bstep (se 1 (by rfl) ⟨853061, by rfl⟩ : syracuseStep 1137415 = 1706123) B1706123
theorem B3824495 : Blo 670310 3824495 := bstep (se 1 (by rfl) ⟨2868371, by rfl⟩ : syracuseStep 3824495 = 5736743) B5736743
theorem B1006751 : Blo 670310 1006751 := bstep (se 1 (by rfl) ⟨755063, by rfl⟩ : syracuseStep 1006751 = 1510127) B1510127
theorem B3398921 : Blo 670310 3398921 := bstep (se 2 (by rfl) ⟨1274595, by rfl⟩ : syracuseStep 3398921 = 2549191) B2549191
theorem B1007003 : Blo 670310 1007003 := bstep (se 1 (by rfl) ⟨755252, by rfl⟩ : syracuseStep 1007003 = 1510505) B1510505
theorem B3235241 : Blo 670310 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B3399083 : Blo 670310 3399083 := bstep (se 1 (by rfl) ⟨2549312, by rfl⟩ : syracuseStep 3399083 = 5098625) B5098625
theorem B1007423 : Blo 670310 1007423 := bstep (se 1 (by rfl) ⟨755567, by rfl⟩ : syracuseStep 1007423 = 1511135) B1511135
theorem B3628921 : Blo 670310 3628921 := bstep (se 2 (by rfl) ⟨1360845, by rfl⟩ : syracuseStep 3628921 = 2721691) B2721691
theorem B1007591 : Blo 670310 1007591 := bstep (se 1 (by rfl) ⟨755693, by rfl⟩ : syracuseStep 1007591 = 1511387) B1511387
theorem B1007711 : Blo 670310 1007711 := bstep (se 1 (by rfl) ⟨755783, by rfl⟩ : syracuseStep 1007711 = 1511567) B1511567
theorem B1007771 : Blo 670310 1007771 := bstep (se 1 (by rfl) ⟨755828, by rfl⟩ : syracuseStep 1007771 = 1511657) B1511657
theorem B1007951 : Blo 670310 1007951 := bstep (se 1 (by rfl) ⟨755963, by rfl⟩ : syracuseStep 1007951 = 1511927) B1511927
theorem B2875837 : Blo 670310 2875837 := bstep (se 3 (by rfl) ⟨539219, by rfl⟩ : syracuseStep 2875837 = 1078439) B1078439
theorem B6480323 : Blo 670310 6480323 := bstep (se 1 (by rfl) ⟨4860242, by rfl⟩ : syracuseStep 6480323 = 9720485) B9720485
theorem B6447721 : Blo 670310 6447721 := bstep (se 2 (by rfl) ⟨2417895, by rfl⟩ : syracuseStep 6447721 = 4835791) B4835791
theorem B2417309 : Blo 670310 2417309 := bstep (se 3 (by rfl) ⟨453245, by rfl⟩ : syracuseStep 2417309 = 906491) B906491
theorem B4317857 : Blo 670310 4317857 := bstep (se 2 (by rfl) ⟨1619196, by rfl⟩ : syracuseStep 4317857 = 3238393) B3238393
theorem B3400379 : Blo 670310 3400379 := bstep (se 1 (by rfl) ⟨2550284, by rfl⟩ : syracuseStep 3400379 = 5100569) B5100569
theorem B1008455 : Blo 670310 1008455 := bstep (se 1 (by rfl) ⟨756341, by rfl⟩ : syracuseStep 1008455 = 1512683) B1512683
theorem B1008521 : Blo 670310 1008521 := bstep (se 2 (by rfl) ⟨378195, by rfl⟩ : syracuseStep 1008521 = 756391) B756391
theorem B1008617 : Blo 670310 1008617 := bstep (se 2 (by rfl) ⟨378231, by rfl⟩ : syracuseStep 1008617 = 756463) B756463
theorem B1696889 : Blo 670310 1696889 := bstep (se 2 (by rfl) ⟨636333, by rfl⟩ : syracuseStep 1696889 = 1272667) B1272667
theorem B1008863 : Blo 670310 1008863 := bstep (se 1 (by rfl) ⟨756647, by rfl⟩ : syracuseStep 1008863 = 1513295) B1513295
theorem B1009055 : Blo 670310 1009055 := bstep (se 1 (by rfl) ⟨756791, by rfl⟩ : syracuseStep 1009055 = 1513583) B1513583
theorem B4154807 : Blo 670310 4154807 := bstep (se 1 (by rfl) ⟨3116105, by rfl⟩ : syracuseStep 4154807 = 6232211) B6232211
theorem B1009103 : Blo 670310 1009103 := bstep (se 1 (by rfl) ⟨756827, by rfl⟩ : syracuseStep 1009103 = 1513655) B1513655
theorem B11494871 : Blo 670310 11494871 := bstep (se 1 (by rfl) ⟨8621153, by rfl⟩ : syracuseStep 11494871 = 17242307) B17242307
theorem B4318757 : Blo 670310 4318757 := bstep (se 4 (by rfl) ⟨404883, by rfl⟩ : syracuseStep 4318757 = 809767) B809767
theorem B1009289 : Blo 670310 1009289 := bstep (se 2 (by rfl) ⟨378483, by rfl⟩ : syracuseStep 1009289 = 756967) B756967
theorem B1009343 : Blo 670310 1009343 := bstep (se 1 (by rfl) ⟨757007, by rfl⟩ : syracuseStep 1009343 = 1514015) B1514015
theorem B1697831 : Blo 670310 1697831 := bstep (se 1 (by rfl) ⟨1273373, by rfl⟩ : syracuseStep 1697831 = 2546747) B2546747
theorem B1698023 : Blo 670310 1698023 := bstep (se 1 (by rfl) ⟨1273517, by rfl⟩ : syracuseStep 1698023 = 2547035) B2547035
theorem B3402323 : Blo 670310 3402323 := bstep (se 1 (by rfl) ⟨2551742, by rfl⟩ : syracuseStep 3402323 = 5103485) B5103485
theorem B1075999 : Blo 670310 1075999 := bstep (se 1 (by rfl) ⟨806999, by rfl⟩ : syracuseStep 1075999 = 1613999) B1613999
theorem B1698671 : Blo 670310 1698671 := bstep (se 1 (by rfl) ⟨1274003, by rfl⟩ : syracuseStep 1698671 = 2548007) B2548007
theorem B1272743 : Blo 670310 1272743 := bstep (se 1 (by rfl) ⟨954557, by rfl⟩ : syracuseStep 1272743 = 1909115) B1909115
theorem B3402809 : Blo 670310 3402809 := bstep (se 2 (by rfl) ⟨1276053, by rfl⟩ : syracuseStep 3402809 = 2552107) B2552107
theorem B1699127 : Blo 670310 1699127 := bstep (se 1 (by rfl) ⟨1274345, by rfl⟩ : syracuseStep 1699127 = 2548691) B2548691
theorem B2551439 : Blo 670310 2551439 := bstep (se 1 (by rfl) ⟨1913579, by rfl⟩ : syracuseStep 2551439 = 3827159) B3827159
theorem B1011359 : Blo 670310 1011359 := bstep (se 1 (by rfl) ⟨758519, by rfl⟩ : syracuseStep 1011359 = 1517039) B1517039
theorem B1437355 : Blo 670310 1437355 := bstep (se 1 (by rfl) ⟨1078016, by rfl⟩ : syracuseStep 1437355 = 2156033) B2156033
theorem B1437679 : Blo 670310 1437679 := bstep (se 1 (by rfl) ⟨1078259, by rfl⟩ : syracuseStep 1437679 = 2156519) B2156519
theorem B18346013 : Blo 670310 18346013 := bstep (se 3 (by rfl) ⟨3439877, by rfl⟩ : syracuseStep 18346013 = 6879755) B6879755
theorem B1699967 : Blo 670310 1699967 := bstep (se 1 (by rfl) ⟨1274975, by rfl⟩ : syracuseStep 1699967 = 2549951) B2549951
theorem B848551 : Blo 670310 848551 := bstep (se 1 (by rfl) ⟨636413, by rfl⟩ : syracuseStep 848551 = 1272827) B1272827
theorem B11629271 : Blo 670310 11629271 := bstep (se 1 (by rfl) ⟨8721953, by rfl⟩ : syracuseStep 11629271 = 17443907) B17443907
theorem B1209115 : Blo 670310 1209115 := bstep (se 1 (by rfl) ⟨906836, by rfl⟩ : syracuseStep 1209115 = 1813673) B1813673
theorem B2421575 : Blo 670310 2421575 := bstep (se 1 (by rfl) ⟨1816181, by rfl⟩ : syracuseStep 2421575 = 3632363) B3632363
theorem B1438841 : Blo 670310 1438841 := bstep (se 2 (by rfl) ⟨539565, by rfl⟩ : syracuseStep 1438841 = 1079131) B1079131
theorem B1078991 : Blo 670310 1078991 := bstep (se 1 (by rfl) ⟨809243, by rfl⟩ : syracuseStep 1078991 = 1618487) B1618487
theorem B39188443 : Blo 670310 39188443 := bstep (se 1 (by rfl) ⟨29391332, by rfl⟩ : syracuseStep 39188443 = 58782665) B58782665
theorem B718951 : Blo 670310 718951 := bstep (se 1 (by rfl) ⟨539213, by rfl⟩ : syracuseStep 718951 = 1078427) B1078427
theorem B1210793 : Blo 670310 1210793 := bstep (se 2 (by rfl) ⟨454047, by rfl⟩ : syracuseStep 1210793 = 908095) B908095
theorem B2587297 : Blo 670310 2587297 := bstep (se 2 (by rfl) ⟨970236, by rfl⟩ : syracuseStep 2587297 = 1940473) B1940473
theorem B4586345 : Blo 670310 4586345 := bstep (se 2 (by rfl) ⟨1719879, by rfl⟩ : syracuseStep 4586345 = 3439759) B3439759
theorem B8191147 : Blo 670310 8191147 := bstep (se 1 (by rfl) ⟨6143360, by rfl⟩ : syracuseStep 8191147 = 12286721) B12286721
theorem B9338105 : Blo 670310 9338105 := bstep (se 2 (by rfl) ⟨3501789, by rfl⟩ : syracuseStep 9338105 = 7003579) B7003579
theorem B2555495 : Blo 670310 2555495 := bstep (se 1 (by rfl) ⟨1916621, by rfl⟩ : syracuseStep 2555495 = 3833243) B3833243
theorem B29130839 : Blo 670310 29130839 := bstep (se 1 (by rfl) ⟨21848129, by rfl⟩ : syracuseStep 29130839 = 43696259) B43696259
theorem B1278089 : Blo 670310 1278089 := bstep (se 2 (by rfl) ⟨479283, by rfl⟩ : syracuseStep 1278089 = 958567) B958567
theorem B1704361 : Blo 670310 1704361 := bstep (se 2 (by rfl) ⟨639135, by rfl⟩ : syracuseStep 1704361 = 1278271) B1278271
theorem B754159 : Blo 670310 754159 := bstep (se 1 (by rfl) ⟨565619, by rfl⟩ : syracuseStep 754159 = 1131239) B1131239
theorem B3834449 : Blo 670310 3834449 := bstep (se 2 (by rfl) ⟨1437918, by rfl⟩ : syracuseStep 3834449 = 2875837) B2875837
theorem B852763 : Blo 670310 852763 := bstep (se 1 (by rfl) ⟨639572, by rfl⟩ : syracuseStep 852763 = 1279145) B1279145
theorem B1278841 : Blo 670310 1278841 := bstep (se 2 (by rfl) ⟨479565, by rfl⟩ : syracuseStep 1278841 = 959131) B959131
theorem B3441847 : Blo 670310 3441847 := bstep (se 1 (by rfl) ⟨2581385, by rfl⟩ : syracuseStep 3441847 = 5162771) B5162771
theorem B1508831 : Blo 670310 1508831 := bstep (se 1 (by rfl) ⟨1131623, by rfl⟩ : syracuseStep 1508831 = 2263247) B2263247
theorem B1705799 : Blo 670310 1705799 := bstep (se 1 (by rfl) ⟨1279349, by rfl⟩ : syracuseStep 1705799 = 2558699) B2558699
theorem B1509695 : Blo 670310 1509695 := bstep (se 1 (by rfl) ⟨1132271, by rfl⟩ : syracuseStep 1509695 = 2264543) B2264543
theorem B3934655 : Blo 670310 3934655 := bstep (se 1 (by rfl) ⟨2950991, by rfl⟩ : syracuseStep 3934655 = 5901983) B5901983
theorem B1706447 : Blo 670310 1706447 := bstep (se 1 (by rfl) ⟨1279835, by rfl⟩ : syracuseStep 1706447 = 2559671) B2559671
theorem B1706579 : Blo 670310 1706579 := bstep (se 1 (by rfl) ⟨1279934, by rfl⟩ : syracuseStep 1706579 = 2559869) B2559869
theorem B1510055 : Blo 670310 1510055 := bstep (se 1 (by rfl) ⟨1132541, by rfl⟩ : syracuseStep 1510055 = 2265083) B2265083
theorem B3836591 : Blo 670310 3836591 := bstep (se 1 (by rfl) ⟨2877443, by rfl⟩ : syracuseStep 3836591 = 5754887) B5754887
theorem B4590445 : Blo 670310 4590445 := bstep (se 3 (by rfl) ⟨860708, by rfl⟩ : syracuseStep 4590445 = 1721417) B1721417
theorem B3836909 : Blo 670310 3836909 := bstep (se 3 (by rfl) ⟨719420, by rfl⟩ : syracuseStep 3836909 = 1438841) B1438841
theorem B1510739 : Blo 670310 1510739 := bstep (se 1 (by rfl) ⟨1133054, by rfl⟩ : syracuseStep 1510739 = 2266109) B2266109
theorem B1510847 : Blo 670310 1510847 := bstep (se 1 (by rfl) ⟨1133135, by rfl⟩ : syracuseStep 1510847 = 2266271) B2266271
theorem B757615 : Blo 670310 757615 := bstep (se 1 (by rfl) ⟨568211, by rfl⟩ : syracuseStep 757615 = 1136423) B1136423
theorem B2559883 : Blo 670310 2559883 := bstep (se 1 (by rfl) ⟨1919912, by rfl⟩ : syracuseStep 2559883 = 3839825) B3839825
theorem B4853843 : Blo 670310 4853843 := bstep (se 1 (by rfl) ⟨3640382, by rfl⟩ : syracuseStep 4853843 = 7280765) B7280765
theorem B11636891 : Blo 670310 11636891 := bstep (se 1 (by rfl) ⟨8727668, by rfl⟩ : syracuseStep 11636891 = 17455337) B17455337
theorem B1511675 : Blo 670310 1511675 := bstep (se 1 (by rfl) ⟨1133756, by rfl⟩ : syracuseStep 1511675 = 2267513) B2267513
theorem B38736143 : Blo 670310 38736143 := bstep (se 1 (by rfl) ⟨29052107, by rfl⟩ : syracuseStep 38736143 = 58104215) B58104215
theorem B10490143 : Blo 670310 10490143 := bstep (se 1 (by rfl) ⟨7867607, by rfl⟩ : syracuseStep 10490143 = 15735215) B15735215
theorem B12915125 : Blo 670310 12915125 := bstep (se 5 (by rfl) ⟨605396, by rfl⟩ : syracuseStep 12915125 = 1210793) B1210793
theorem B2265947 : Blo 670310 2265947 := bstep (se 1 (by rfl) ⟨1699460, by rfl⟩ : syracuseStep 2265947 = 3398921) B3398921
theorem B2266055 : Blo 670310 2266055 := bstep (se 1 (by rfl) ⟨1699541, by rfl⟩ : syracuseStep 2266055 = 3399083) B3399083
theorem B1611539 : Blo 670310 1611539 := bstep (se 1 (by rfl) ⟨1208654, by rfl⟩ : syracuseStep 1611539 = 2417309) B2417309
theorem B2266919 : Blo 670310 2266919 := bstep (se 1 (by rfl) ⟨1700189, by rfl⟩ : syracuseStep 2266919 = 3400379) B3400379
theorem B1513385 : Blo 670310 1513385 := bstep (se 2 (by rfl) ⟨567519, by rfl⟩ : syracuseStep 1513385 = 1135039) B1135039
theorem B1612153 : Blo 670310 1612153 := bstep (se 2 (by rfl) ⟨604557, by rfl⟩ : syracuseStep 1612153 = 1209115) B1209115
theorem B1514303 : Blo 670310 1514303 := bstep (se 1 (by rfl) ⟨1135727, by rfl⟩ : syracuseStep 1514303 = 2271455) B2271455
theorem B7674911 : Blo 670310 7674911 := bstep (se 1 (by rfl) ⟨5756183, by rfl⟩ : syracuseStep 7674911 = 11512367) B11512367
theorem B2268215 : Blo 670310 2268215 := bstep (se 1 (by rfl) ⟨1701161, by rfl⟩ : syracuseStep 2268215 = 3402323) B3402323
theorem B2268539 : Blo 670310 2268539 := bstep (se 1 (by rfl) ⟨1701404, by rfl⟩ : syracuseStep 2268539 = 3402809) B3402809
theorem B2039519 : Blo 670310 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B1515347 : Blo 670310 1515347 := bstep (se 1 (by rfl) ⟨1136510, by rfl⟩ : syracuseStep 1515347 = 2273021) B2273021
theorem B36741053 : Blo 670310 36741053 := bstep (se 3 (by rfl) ⟨6888947, by rfl⟩ : syracuseStep 36741053 = 13777895) B13777895
theorem B1515455 : Blo 670310 1515455 := bstep (se 1 (by rfl) ⟨1136591, by rfl⟩ : syracuseStep 1515455 = 2273183) B2273183
theorem B12230675 : Blo 670310 12230675 := bstep (se 1 (by rfl) ⟨9173006, by rfl⟩ : syracuseStep 12230675 = 18346013) B18346013
theorem B958601 : Blo 670310 958601 := bstep (se 2 (by rfl) ⟨359475, by rfl⟩ : syracuseStep 958601 = 718951) B718951
theorem B4857995 : Blo 670310 4857995 := bstep (se 1 (by rfl) ⟨3643496, by rfl⟩ : syracuseStep 4857995 = 7286993) B7286993
theorem B2302121 : Blo 670310 2302121 := bstep (se 2 (by rfl) ⟨863295, by rfl⟩ : syracuseStep 2302121 = 1726591) B1726591
theorem B1614383 : Blo 670310 1614383 := bstep (se 1 (by rfl) ⟨1210787, by rfl⟩ : syracuseStep 1614383 = 2421575) B2421575
theorem B3449729 : Blo 670310 3449729 := bstep (se 2 (by rfl) ⟨1293648, by rfl⟩ : syracuseStep 3449729 = 2587297) B2587297
theorem B1516553 : Blo 670310 1516553 := bstep (se 2 (by rfl) ⟨568707, by rfl⟩ : syracuseStep 1516553 = 1137415) B1137415
theorem B1516607 : Blo 670310 1516607 := bstep (se 1 (by rfl) ⟨1137455, by rfl⟩ : syracuseStep 1516607 = 2274911) B2274911
theorem B1910299 : Blo 670310 1910299 := bstep (se 1 (by rfl) ⟨1432724, by rfl⟩ : syracuseStep 1910299 = 2865449) B2865449
theorem B10921529 : Blo 670310 10921529 := bstep (se 2 (by rfl) ⟨4095573, by rfl⟩ : syracuseStep 10921529 = 8191147) B8191147
theorem B3057563 : Blo 670310 3057563 := bstep (se 1 (by rfl) ⟨2293172, by rfl⟩ : syracuseStep 3057563 = 4586345) B4586345
theorem B23341121 : Blo 670310 23341121 := bstep (se 2 (by rfl) ⟨8752920, by rfl⟩ : syracuseStep 23341121 = 17505841) B17505841
theorem B1910891 : Blo 670310 1910891 := bstep (se 1 (by rfl) ⟨1433168, by rfl⟩ : syracuseStep 1910891 = 2866337) B2866337
theorem B8596961 : Blo 670310 8596961 := bstep (se 2 (by rfl) ⟨3223860, by rfl⟩ : syracuseStep 8596961 = 6447721) B6447721
theorem B30978125 : Blo 670310 30978125 := bstep (se 3 (by rfl) ⟨5808398, by rfl⟩ : syracuseStep 30978125 = 11616797) B11616797
theorem B16822403 : Blo 670310 16822403 := bstep (se 1 (by rfl) ⟨12616802, by rfl⟩ : syracuseStep 16822403 = 25233605) B25233605
theorem B1912987 : Blo 670310 1912987 := bstep (se 1 (by rfl) ⟨1434740, by rfl⟩ : syracuseStep 1912987 = 2869481) B2869481
theorem B1913159 : Blo 670310 1913159 := bstep (se 1 (by rfl) ⟨1434869, by rfl⟩ : syracuseStep 1913159 = 2869739) B2869739
theorem B6469865 : Blo 670310 6469865 := bstep (se 2 (by rfl) ⟨2426199, by rfl⟩ : syracuseStep 6469865 = 4852399) B4852399
theorem B5454539 : Blo 670310 5454539 := bstep (se 1 (by rfl) ⟨4090904, by rfl⟩ : syracuseStep 5454539 = 8181809) B8181809
theorem B671167 : Blo 670310 671167 := bstep (se 1 (by rfl) ⟨503375, by rfl⟩ : syracuseStep 671167 = 1006751) B1006751
theorem B1916473 : Blo 670310 1916473 := bstep (se 2 (by rfl) ⟨718677, by rfl⟩ : syracuseStep 1916473 = 1437355) B1437355
theorem B671335 : Blo 670310 671335 := bstep (se 1 (by rfl) ⟨503501, by rfl⟩ : syracuseStep 671335 = 1007003) B1007003
theorem B671615 : Blo 670310 671615 := bstep (se 1 (by rfl) ⟨503711, by rfl⟩ : syracuseStep 671615 = 1007423) B1007423
theorem B671727 : Blo 670310 671727 := bstep (se 1 (by rfl) ⟨503795, by rfl⟩ : syracuseStep 671727 = 1007591) B1007591
theorem B671807 : Blo 670310 671807 := bstep (se 1 (by rfl) ⟨503855, by rfl⟩ : syracuseStep 671807 = 1007711) B1007711
theorem B671847 : Blo 670310 671847 := bstep (se 1 (by rfl) ⟨503885, by rfl⟩ : syracuseStep 671847 = 1007771) B1007771
theorem B671967 : Blo 670310 671967 := bstep (se 1 (by rfl) ⟨503975, by rfl⟩ : syracuseStep 671967 = 1007951) B1007951
theorem B672303 : Blo 670310 672303 := bstep (se 1 (by rfl) ⟨504227, by rfl⟩ : syracuseStep 672303 = 1008455) B1008455
theorem B672347 : Blo 670310 672347 := bstep (se 1 (by rfl) ⟨504260, by rfl⟩ : syracuseStep 672347 = 1008521) B1008521
theorem B3818137 : Blo 670310 3818137 := bstep (se 2 (by rfl) ⟨1431801, by rfl⟩ : syracuseStep 3818137 = 2863603) B2863603
theorem B672411 : Blo 670310 672411 := bstep (se 1 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 672411 = 1008617) B1008617
theorem B1131259 : Blo 670310 1131259 := bstep (se 1 (by rfl) ⟨848444, by rfl⟩ : syracuseStep 1131259 = 1696889) B1696889
theorem B672575 : Blo 670310 672575 := bstep (se 1 (by rfl) ⟨504431, by rfl⟩ : syracuseStep 672575 = 1008863) B1008863
theorem B1131401 : Blo 670310 1131401 := bstep (se 2 (by rfl) ⟨424275, by rfl⟩ : syracuseStep 1131401 = 848551) B848551
theorem B672703 : Blo 670310 672703 := bstep (se 1 (by rfl) ⟨504527, by rfl⟩ : syracuseStep 672703 = 1009055) B1009055
theorem B2769871 : Blo 670310 2769871 := bstep (se 1 (by rfl) ⟨2077403, by rfl⟩ : syracuseStep 2769871 = 4154807) B4154807
theorem B672735 : Blo 670310 672735 := bstep (se 1 (by rfl) ⟨504551, by rfl⟩ : syracuseStep 672735 = 1009103) B1009103
theorem B672859 : Blo 670310 672859 := bstep (se 1 (by rfl) ⟨504644, by rfl⟩ : syracuseStep 672859 = 1009289) B1009289
theorem B672895 : Blo 670310 672895 := bstep (se 1 (by rfl) ⟨504671, by rfl⟩ : syracuseStep 672895 = 1009343) B1009343
theorem B1131887 : Blo 670310 1131887 := bstep (se 1 (by rfl) ⟨848915, by rfl⟩ : syracuseStep 1131887 = 1697831) B1697831
theorem B1132015 : Blo 670310 1132015 := bstep (se 1 (by rfl) ⟨849011, by rfl⟩ : syracuseStep 1132015 = 1698023) B1698023
theorem B1132447 : Blo 670310 1132447 := bstep (se 1 (by rfl) ⟨849335, by rfl⟩ : syracuseStep 1132447 = 1698671) B1698671
theorem B1132751 : Blo 670310 1132751 := bstep (se 1 (by rfl) ⟨849563, by rfl⟩ : syracuseStep 1132751 = 1699127) B1699127
theorem B674239 : Blo 670310 674239 := bstep (se 1 (by rfl) ⟨505679, by rfl⟩ : syracuseStep 674239 = 1011359) B1011359
theorem B52251257 : Blo 670310 52251257 := bstep (se 2 (by rfl) ⟨19594221, by rfl⟩ : syracuseStep 52251257 = 39188443) B39188443
theorem B1133311 : Blo 670310 1133311 := bstep (se 1 (by rfl) ⟨849983, by rfl⟩ : syracuseStep 1133311 = 1699967) B1699967
theorem B20761427 : Blo 670310 20761427 := bstep (se 1 (by rfl) ⟨15571070, by rfl⟩ : syracuseStep 20761427 = 31142141) B31142141
theorem B7752847 : Blo 670310 7752847 := bstep (se 1 (by rfl) ⟨5814635, by rfl⟩ : syracuseStep 7752847 = 11629271) B11629271
theorem B4836833 : Blo 670310 4836833 := bstep (se 2 (by rfl) ⟨1813812, by rfl⟩ : syracuseStep 4836833 = 3627625) B3627625
theorem B4838561 : Blo 670310 4838561 := bstep (se 2 (by rfl) ⟨1814460, by rfl⟩ : syracuseStep 4838561 = 3628921) B3628921
theorem B2184787 : Blo 670310 2184787 := bstep (se 1 (by rfl) ⟨1638590, by rfl⟩ : syracuseStep 2184787 = 3277181) B3277181
theorem B1005479 : Blo 670310 1005479 := bstep (se 1 (by rfl) ⟨754109, by rfl⟩ : syracuseStep 1005479 = 1508219) B1508219
theorem B2545775 : Blo 670310 2545775 := bstep (se 1 (by rfl) ⟨1909331, by rfl⟩ : syracuseStep 2545775 = 3818663) B3818663
theorem B2545789 : Blo 670310 2545789 := bstep (se 3 (by rfl) ⟨477335, by rfl⟩ : syracuseStep 2545789 = 954671) B954671
theorem B1137145 : Blo 670310 1137145 := bstep (se 2 (by rfl) ⟨426429, by rfl⟩ : syracuseStep 1137145 = 852859) B852859
theorem B1006331 : Blo 670310 1006331 := bstep (se 1 (by rfl) ⟨754748, by rfl⟩ : syracuseStep 1006331 = 1509497) B1509497
theorem B19357001 : Blo 670310 19357001 := bstep (se 2 (by rfl) ⟨7258875, by rfl⟩ : syracuseStep 19357001 = 14517751) B14517751
theorem B777695 : Blo 670310 777695 := bstep (se 1 (by rfl) ⟨583271, by rfl⟩ : syracuseStep 777695 = 1166543) B1166543
theorem B1007369 : Blo 670310 1007369 := bstep (se 2 (by rfl) ⟨377763, by rfl⟩ : syracuseStep 1007369 = 755527) B755527
theorem B29548799 : Blo 670310 29548799 := bstep (se 1 (by rfl) ⟨22161599, by rfl⟩ : syracuseStep 29548799 = 44323199) B44323199
theorem B1008107 : Blo 670310 1008107 := bstep (se 1 (by rfl) ⟨756080, by rfl⟩ : syracuseStep 1008107 = 1512161) B1512161
theorem B1008233 : Blo 670310 1008233 := bstep (se 2 (by rfl) ⟨378087, by rfl⟩ : syracuseStep 1008233 = 756175) B756175
theorem B7660331 : Blo 670310 7660331 := bstep (se 1 (by rfl) ⟨5745248, by rfl⟩ : syracuseStep 7660331 = 11490497) B11490497
theorem B910171 : Blo 670310 910171 := bstep (se 1 (by rfl) ⟨682628, by rfl⟩ : syracuseStep 910171 = 1365257) B1365257
theorem B1434665 : Blo 670310 1434665 := bstep (se 2 (by rfl) ⟨537999, by rfl⟩ : syracuseStep 1434665 = 1075999) B1075999
theorem B1008905 : Blo 670310 1008905 := bstep (se 2 (by rfl) ⟨378339, by rfl⟩ : syracuseStep 1008905 = 756679) B756679
theorem B1697071 : Blo 670310 1697071 := bstep (se 1 (by rfl) ⟨1272803, by rfl⟩ : syracuseStep 1697071 = 2545607) B2545607
theorem B3827411 : Blo 670310 3827411 := bstep (se 1 (by rfl) ⟨2870558, by rfl⟩ : syracuseStep 3827411 = 5741117) B5741117
theorem B1009385 : Blo 670310 1009385 := bstep (se 2 (by rfl) ⟨378519, by rfl⟩ : syracuseStep 1009385 = 757039) B757039
theorem B2549663 : Blo 670310 2549663 := bstep (se 1 (by rfl) ⟨1912247, by rfl⟩ : syracuseStep 2549663 = 3824495) B3824495
theorem B1009919 : Blo 670310 1009919 := bstep (se 1 (by rfl) ⟨757439, by rfl⟩ : syracuseStep 1009919 = 1514879) B1514879
theorem B2156827 : Blo 670310 2156827 := bstep (se 1 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 2156827 = 3235241) B3235241
theorem B1010471 : Blo 670310 1010471 := bstep (se 1 (by rfl) ⟨757853, by rfl⟩ : syracuseStep 1010471 = 1515707) B1515707
theorem B4320215 : Blo 670310 4320215 := bstep (se 1 (by rfl) ⟨3240161, by rfl⟩ : syracuseStep 4320215 = 6480323) B6480323
theorem B2157673 : Blo 670310 2157673 := bstep (se 2 (by rfl) ⟨809127, by rfl⟩ : syracuseStep 2157673 = 1618255) B1618255
theorem B2878571 : Blo 670310 2878571 := bstep (se 1 (by rfl) ⟨2158928, by rfl⟩ : syracuseStep 2878571 = 4317857) B4317857
theorem B1011179 : Blo 670310 1011179 := bstep (se 1 (by rfl) ⟨758384, by rfl⟩ : syracuseStep 1011179 = 1516769) B1516769
theorem B7663247 : Blo 670310 7663247 := bstep (se 1 (by rfl) ⟨5747435, by rfl⟩ : syracuseStep 7663247 = 11494871) B11494871
theorem B2879171 : Blo 670310 2879171 := bstep (se 1 (by rfl) ⟨2159378, by rfl⟩ : syracuseStep 2879171 = 4318757) B4318757
theorem B1011431 : Blo 670310 1011431 := bstep (se 1 (by rfl) ⟨758573, by rfl⟩ : syracuseStep 1011431 = 1517147) B1517147
theorem B3829801 : Blo 670310 3829801 := bstep (se 2 (by rfl) ⟨1436175, by rfl⟩ : syracuseStep 3829801 = 2872351) B2872351
theorem B1536425 : Blo 670310 1536425 := bstep (se 2 (by rfl) ⟨576159, by rfl⟩ : syracuseStep 1536425 = 1152319) B1152319
theorem B3830327 : Blo 670310 3830327 := bstep (se 1 (by rfl) ⟨2872745, by rfl⟩ : syracuseStep 3830327 = 5745491) B5745491
theorem B848495 : Blo 670310 848495 := bstep (se 1 (by rfl) ⟨636371, by rfl⟩ : syracuseStep 848495 = 1272743) B1272743
theorem B1700959 : Blo 670310 1700959 := bstep (se 1 (by rfl) ⟨1275719, by rfl⟩ : syracuseStep 1700959 = 2551439) B2551439
theorem B719327 : Blo 670310 719327 := bstep (se 1 (by rfl) ⟨539495, by rfl⟩ : syracuseStep 719327 = 1078991) B1078991
theorem B6225403 : Blo 670310 6225403 := bstep (se 1 (by rfl) ⟨4669052, by rfl⟩ : syracuseStep 6225403 = 9338105) B9338105
theorem B1703663 : Blo 670310 1703663 := bstep (se 1 (by rfl) ⟨1277747, by rfl⟩ : syracuseStep 1703663 = 2555495) B2555495
theorem B7667621 : Blo 670310 7667621 := bstep (se 4 (by rfl) ⟨718839, by rfl⟩ : syracuseStep 7667621 = 1437679) B1437679
theorem B852059 : Blo 670310 852059 := bstep (se 1 (by rfl) ⟨639044, by rfl⟩ : syracuseStep 852059 = 1278089) B1278089
theorem B2556269 : Blo 670310 2556269 := bstep (se 3 (by rfl) ⟨479300, by rfl⟩ : syracuseStep 2556269 = 958601) B958601
theorem B2556299 : Blo 670310 2556299 := bstep (se 1 (by rfl) ⟨1917224, by rfl⟩ : syracuseStep 2556299 = 3834449) B3834449
theorem B754267 : Blo 670310 754267 := bstep (se 1 (by rfl) ⟨565700, by rfl⟩ : syracuseStep 754267 = 1131401) B1131401
theorem B754591 : Blo 670310 754591 := bstep (se 1 (by rfl) ⟨565943, by rfl⟩ : syracuseStep 754591 = 1131887) B1131887
theorem B1508345 : Blo 670310 1508345 := bstep (se 2 (by rfl) ⟨565629, by rfl⟩ : syracuseStep 1508345 = 1131259) B1131259
theorem B1213561 : Blo 670310 1213561 := bstep (se 2 (by rfl) ⟨455085, by rfl⟩ : syracuseStep 1213561 = 910171) B910171
theorem B1705121 : Blo 670310 1705121 := bstep (se 2 (by rfl) ⟨639420, by rfl⟩ : syracuseStep 1705121 = 1278841) B1278841
theorem B755167 : Blo 670310 755167 := bstep (se 1 (by rfl) ⟨566375, by rfl⟩ : syracuseStep 755167 = 1132751) B1132751
theorem B4589129 : Blo 670310 4589129 := bstep (se 2 (by rfl) ⟨1720923, by rfl⟩ : syracuseStep 4589129 = 3441847) B3441847
theorem B2262653 : Blo 670310 2262653 := bstep (se 3 (by rfl) ⟨424247, by rfl⟩ : syracuseStep 2262653 = 848495) B848495
theorem B2623103 : Blo 670310 2623103 := bstep (se 1 (by rfl) ⟨1967327, by rfl⟩ : syracuseStep 2623103 = 3934655) B3934655
theorem B2262761 : Blo 670310 2262761 := bstep (se 2 (by rfl) ⟨848535, by rfl⟩ : syracuseStep 2262761 = 1697071) B1697071
theorem B34834171 : Blo 670310 34834171 := bstep (se 1 (by rfl) ⟨26125628, by rfl⟩ : syracuseStep 34834171 = 52251257) B52251257
theorem B2557727 : Blo 670310 2557727 := bstep (se 1 (by rfl) ⟨1918295, by rfl⟩ : syracuseStep 2557727 = 3836591) B3836591
theorem B1509353 : Blo 670310 1509353 := bstep (se 2 (by rfl) ⟨566007, by rfl⟩ : syracuseStep 1509353 = 1132015) B1132015
theorem B2557939 : Blo 670310 2557939 := bstep (se 1 (by rfl) ⟨1918454, by rfl⟩ : syracuseStep 2557939 = 3836909) B3836909
theorem B1509929 : Blo 670310 1509929 := bstep (se 2 (by rfl) ⟨566223, by rfl⟩ : syracuseStep 1509929 = 1132447) B1132447
theorem B25824095 : Blo 670310 25824095 := bstep (se 1 (by rfl) ⟨19368071, by rfl⟩ : syracuseStep 25824095 = 38736143) B38736143
theorem B1510631 : Blo 670310 1510631 := bstep (se 1 (by rfl) ⟨1132973, by rfl⟩ : syracuseStep 1510631 = 2265947) B2265947
theorem B1510703 : Blo 670310 1510703 := bstep (se 1 (by rfl) ⟨1133027, by rfl⟩ : syracuseStep 1510703 = 2266055) B2266055
theorem B1511081 : Blo 670310 1511081 := bstep (se 2 (by rfl) ⟨566655, by rfl⟩ : syracuseStep 1511081 = 1133311) B1133311
theorem B1511279 : Blo 670310 1511279 := bstep (se 1 (by rfl) ⟨1133459, by rfl⟩ : syracuseStep 1511279 = 2266919) B2266919
theorem B5116607 : Blo 670310 5116607 := bstep (se 1 (by rfl) ⟨3837455, by rfl⟩ : syracuseStep 5116607 = 7674911) B7674911
theorem B1512143 : Blo 670310 1512143 := bstep (se 1 (by rfl) ⟨1134107, by rfl⟩ : syracuseStep 1512143 = 2268215) B2268215
theorem B1512359 : Blo 670310 1512359 := bstep (se 1 (by rfl) ⟨1134269, by rfl⟩ : syracuseStep 1512359 = 2268539) B2268539
theorem B3413177 : Blo 670310 3413177 := bstep (se 2 (by rfl) ⟨1279941, by rfl⟩ : syracuseStep 3413177 = 2559883) B2559883
theorem B19699199 : Blo 670310 19699199 := bstep (se 1 (by rfl) ⟨14774399, by rfl⟩ : syracuseStep 19699199 = 29548799) B29548799
theorem B956443 : Blo 670310 956443 := bstep (se 1 (by rfl) ⟨717332, by rfl⟩ : syracuseStep 956443 = 1434665) B1434665
theorem B7281019 : Blo 670310 7281019 := bstep (se 1 (by rfl) ⟨5460764, by rfl⟩ : syracuseStep 7281019 = 10921529) B10921529
theorem B2038375 : Blo 670310 2038375 := bstep (se 1 (by rfl) ⟨1528781, by rfl⟩ : syracuseStep 2038375 = 3057563) B3057563
theorem B2267945 : Blo 670310 2267945 := bstep (se 2 (by rfl) ⟨850479, by rfl⟩ : syracuseStep 2267945 = 1700959) B1700959
theorem B20652083 : Blo 670310 20652083 := bstep (se 1 (by rfl) ⟨15489062, by rfl⟩ : syracuseStep 20652083 = 30978125) B30978125
theorem B11214935 : Blo 670310 11214935 := bstep (se 1 (by rfl) ⟨8411201, by rfl⟩ : syracuseStep 11214935 = 16822403) B16822403
theorem B1024283 : Blo 670310 1024283 := bstep (se 1 (by rfl) ⟨768212, by rfl⟩ : syracuseStep 1024283 = 1536425) B1536425
theorem B1516193 : Blo 670310 1516193 := bstep (se 2 (by rfl) ⟨568572, by rfl⟩ : syracuseStep 1516193 = 1137145) B1137145
theorem B2073853 : Blo 670310 2073853 := bstep (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) B777695
theorem B8300537 : Blo 670310 8300537 := bstep (se 2 (by rfl) ⟨3112701, by rfl⟩ : syracuseStep 8300537 = 6225403) B6225403
theorem B2272481 : Blo 670310 2272481 := bstep (se 2 (by rfl) ⟨852180, by rfl⟩ : syracuseStep 2272481 = 1704361) B1704361
theorem B5090849 : Blo 670310 5090849 := bstep (se 2 (by rfl) ⟨1909068, by rfl⟩ : syracuseStep 5090849 = 3818137) B3818137
theorem B13840951 : Blo 670310 13840951 := bstep (se 1 (by rfl) ⟨10380713, by rfl⟩ : syracuseStep 13840951 = 20761427) B20761427
theorem B3224555 : Blo 670310 3224555 := bstep (se 1 (by rfl) ⟨2418416, by rfl⟩ : syracuseStep 3224555 = 4836833) B4836833
theorem B3225707 : Blo 670310 3225707 := bstep (se 1 (by rfl) ⟨2419280, by rfl⟩ : syracuseStep 3225707 = 4838561) B4838561
theorem B670319 : Blo 670310 670319 := bstep (se 1 (by rfl) ⟨502739, by rfl⟩ : syracuseStep 670319 = 1005479) B1005479
theorem B10337129 : Blo 670310 10337129 := bstep (se 2 (by rfl) ⟨3876423, by rfl⟩ : syracuseStep 10337129 = 7752847) B7752847
theorem B670887 : Blo 670310 670887 := bstep (se 1 (by rfl) ⟨503165, by rfl⟩ : syracuseStep 670887 = 1006331) B1006331
theorem B1359679 : Blo 670310 1359679 := bstep (se 1 (by rfl) ⟨1019759, by rfl⟩ : syracuseStep 1359679 = 2039519) B2039519
theorem B671579 : Blo 670310 671579 := bstep (se 1 (by rfl) ⟨503684, by rfl⟩ : syracuseStep 671579 = 1007369) B1007369
theorem B24494035 : Blo 670310 24494035 := bstep (se 1 (by rfl) ⟨18370526, by rfl⟩ : syracuseStep 24494035 = 36741053) B36741053
theorem B5095709 : Blo 670310 5095709 := bstep (se 3 (by rfl) ⟨955445, by rfl⟩ : syracuseStep 5095709 = 1910891) B1910891
theorem B672071 : Blo 670310 672071 := bstep (se 1 (by rfl) ⟨504053, by rfl⟩ : syracuseStep 672071 = 1008107) B1008107
theorem B672155 : Blo 670310 672155 := bstep (se 1 (by rfl) ⟨504116, by rfl⟩ : syracuseStep 672155 = 1008233) B1008233
theorem B672603 : Blo 670310 672603 := bstep (se 1 (by rfl) ⟨504452, by rfl⟩ : syracuseStep 672603 = 1008905) B1008905
theorem B672923 : Blo 670310 672923 := bstep (se 1 (by rfl) ⟨504692, by rfl⟩ : syracuseStep 672923 = 1009385) B1009385
theorem B1918205 : Blo 670310 1918205 := bstep (se 3 (by rfl) ⟨359663, by rfl⟩ : syracuseStep 1918205 = 719327) B719327
theorem B673279 : Blo 670310 673279 := bstep (se 1 (by rfl) ⟨504959, by rfl⟩ : syracuseStep 673279 = 1009919) B1009919
theorem B673647 : Blo 670310 673647 := bstep (se 1 (by rfl) ⟨505235, by rfl⟩ : syracuseStep 673647 = 1010471) B1010471
theorem B1919047 : Blo 670310 1919047 := bstep (se 1 (by rfl) ⟨1439285, by rfl⟩ : syracuseStep 1919047 = 2878571) B2878571
theorem B674119 : Blo 670310 674119 := bstep (se 1 (by rfl) ⟨505589, by rfl⟩ : syracuseStep 674119 = 1011179) B1011179
theorem B1919447 : Blo 670310 1919447 := bstep (se 1 (by rfl) ⟨1439585, by rfl⟩ : syracuseStep 1919447 = 2879171) B2879171
theorem B674287 : Blo 670310 674287 := bstep (se 1 (by rfl) ⟨505715, by rfl⟩ : syracuseStep 674287 = 1011431) B1011431
theorem B3394385 : Blo 670310 3394385 := bstep (se 2 (by rfl) ⟨1272894, by rfl⟩ : syracuseStep 3394385 = 2545789) B2545789
theorem B2149537 : Blo 670310 2149537 := bstep (se 2 (by rfl) ⟨806076, by rfl⟩ : syracuseStep 2149537 = 1612153) B1612153
theorem B4313243 : Blo 670310 4313243 := bstep (se 1 (by rfl) ⟨3234932, by rfl⟩ : syracuseStep 4313243 = 6469865) B6469865
theorem B1135775 : Blo 670310 1135775 := bstep (se 1 (by rfl) ⟨851831, by rfl⟩ : syracuseStep 1135775 = 1703663) B1703663
theorem B19420559 : Blo 670310 19420559 := bstep (se 1 (by rfl) ⟨14565419, by rfl⟩ : syracuseStep 19420559 = 29130839) B29130839
theorem B1005545 : Blo 670310 1005545 := bstep (se 2 (by rfl) ⟨377079, by rfl⟩ : syracuseStep 1005545 = 754159) B754159
theorem B1005887 : Blo 670310 1005887 := bstep (se 1 (by rfl) ⟨754415, by rfl⟩ : syracuseStep 1005887 = 1508831) B1508831
theorem B1137017 : Blo 670310 1137017 := bstep (se 2 (by rfl) ⟨426381, by rfl⟩ : syracuseStep 1137017 = 852763) B852763
theorem B1137199 : Blo 670310 1137199 := bstep (se 1 (by rfl) ⟨852899, by rfl⟩ : syracuseStep 1137199 = 1705799) B1705799
theorem B3693161 : Blo 670310 3693161 := bstep (se 2 (by rfl) ⟨1384935, by rfl⟩ : syracuseStep 3693161 = 2769871) B2769871
theorem B1006463 : Blo 670310 1006463 := bstep (se 1 (by rfl) ⟨754847, by rfl⟩ : syracuseStep 1006463 = 1509695) B1509695
theorem B1137631 : Blo 670310 1137631 := bstep (se 1 (by rfl) ⟨853223, by rfl⟩ : syracuseStep 1137631 = 1706447) B1706447
theorem B1137719 : Blo 670310 1137719 := bstep (se 1 (by rfl) ⟨853289, by rfl⟩ : syracuseStep 1137719 = 1706579) B1706579
theorem B1006703 : Blo 670310 1006703 := bstep (se 1 (by rfl) ⟨755027, by rfl⟩ : syracuseStep 1006703 = 1510055) B1510055
theorem B2547065 : Blo 670310 2547065 := bstep (se 2 (by rfl) ⟨955149, by rfl⟩ : syracuseStep 2547065 = 1910299) B1910299
theorem B1007159 : Blo 670310 1007159 := bstep (se 1 (by rfl) ⟨755369, by rfl⟩ : syracuseStep 1007159 = 1510739) B1510739
theorem B1007231 : Blo 670310 1007231 := bstep (se 1 (by rfl) ⟨755423, by rfl⟩ : syracuseStep 1007231 = 1510847) B1510847
theorem B9199277 : Blo 670310 9199277 := bstep (se 3 (by rfl) ⟨1724864, by rfl⟩ : syracuseStep 9199277 = 3449729) B3449729
theorem B3235895 : Blo 670310 3235895 := bstep (se 1 (by rfl) ⟨2426921, by rfl⟩ : syracuseStep 3235895 = 4853843) B4853843
theorem B7757927 : Blo 670310 7757927 := bstep (se 1 (by rfl) ⟨5818445, by rfl⟩ : syracuseStep 7757927 = 11636891) B11636891
theorem B1007783 : Blo 670310 1007783 := bstep (se 1 (by rfl) ⟨755837, by rfl⟩ : syracuseStep 1007783 = 1511675) B1511675
theorem B8610083 : Blo 670310 8610083 := bstep (se 1 (by rfl) ⟨6457562, by rfl⟩ : syracuseStep 8610083 = 12915125) B12915125
theorem B2875769 : Blo 670310 2875769 := bstep (se 2 (by rfl) ⟨1078413, by rfl⟩ : syracuseStep 2875769 = 2156827) B2156827
theorem B6120593 : Blo 670310 6120593 := bstep (se 2 (by rfl) ⟨2295222, by rfl⟩ : syracuseStep 6120593 = 4590445) B4590445
theorem B1074359 : Blo 670310 1074359 := bstep (se 1 (by rfl) ⟨805769, by rfl⟩ : syracuseStep 1074359 = 1611539) B1611539
theorem B1008923 : Blo 670310 1008923 := bstep (se 1 (by rfl) ⟨756692, by rfl⟩ : syracuseStep 1008923 = 1513385) B1513385
theorem B1697183 : Blo 670310 1697183 := bstep (se 1 (by rfl) ⟨1272887, by rfl⟩ : syracuseStep 1697183 = 2545775) B2545775
theorem B2876897 : Blo 670310 2876897 := bstep (se 2 (by rfl) ⟨1078836, by rfl⟩ : syracuseStep 2876897 = 2157673) B2157673
theorem B1009535 : Blo 670310 1009535 := bstep (se 1 (by rfl) ⟨757151, by rfl⟩ : syracuseStep 1009535 = 1514303) B1514303
theorem B12904667 : Blo 670310 12904667 := bstep (se 1 (by rfl) ⟨9678500, by rfl⟩ : syracuseStep 12904667 = 19357001) B19357001
theorem B1010153 : Blo 670310 1010153 := bstep (se 2 (by rfl) ⟨378807, by rfl⟩ : syracuseStep 1010153 = 757615) B757615
theorem B1010231 : Blo 670310 1010231 := bstep (se 1 (by rfl) ⟨757673, by rfl⟩ : syracuseStep 1010231 = 1515347) B1515347
theorem B1010303 : Blo 670310 1010303 := bstep (se 1 (by rfl) ⟨757727, by rfl⟩ : syracuseStep 1010303 = 1515455) B1515455
theorem B8153783 : Blo 670310 8153783 := bstep (se 1 (by rfl) ⟨6115337, by rfl⟩ : syracuseStep 8153783 = 12230675) B12230675
theorem B5106401 : Blo 670310 5106401 := bstep (se 2 (by rfl) ⟨1914900, by rfl⟩ : syracuseStep 5106401 = 3829801) B3829801
theorem B3238663 : Blo 670310 3238663 := bstep (se 1 (by rfl) ⟨2428997, by rfl⟩ : syracuseStep 3238663 = 4857995) B4857995
theorem B1534747 : Blo 670310 1534747 := bstep (se 1 (by rfl) ⟨1151060, by rfl⟩ : syracuseStep 1534747 = 2302121) B2302121
theorem B2550649 : Blo 670310 2550649 := bstep (se 2 (by rfl) ⟨956493, by rfl⟩ : syracuseStep 2550649 = 1912987) B1912987
theorem B1076255 : Blo 670310 1076255 := bstep (se 1 (by rfl) ⟨807191, by rfl⟩ : syracuseStep 1076255 = 1614383) B1614383
theorem B13986857 : Blo 670310 13986857 := bstep (se 2 (by rfl) ⟨5245071, by rfl⟩ : syracuseStep 13986857 = 10490143) B10490143
theorem B5106887 : Blo 670310 5106887 := bstep (se 1 (by rfl) ⟨3830165, by rfl⟩ : syracuseStep 5106887 = 7660331) B7660331
theorem B1011035 : Blo 670310 1011035 := bstep (se 1 (by rfl) ⟨758276, by rfl⟩ : syracuseStep 1011035 = 1516553) B1516553
theorem B1011071 : Blo 670310 1011071 := bstep (se 1 (by rfl) ⟨758303, by rfl⟩ : syracuseStep 1011071 = 1516607) B1516607
theorem B2551607 : Blo 670310 2551607 := bstep (se 1 (by rfl) ⟨1913705, by rfl⟩ : syracuseStep 2551607 = 3827411) B3827411
theorem B1699775 : Blo 670310 1699775 := bstep (se 1 (by rfl) ⟨1274831, by rfl⟩ : syracuseStep 1699775 = 2549663) B2549663
theorem B15560747 : Blo 670310 15560747 := bstep (se 1 (by rfl) ⟨11670560, by rfl⟩ : syracuseStep 15560747 = 23341121) B23341121
theorem B2880143 : Blo 670310 2880143 := bstep (se 1 (by rfl) ⟨2160107, by rfl⟩ : syracuseStep 2880143 = 4320215) B4320215
theorem B2913049 : Blo 670310 2913049 := bstep (se 2 (by rfl) ⟨1092393, by rfl⟩ : syracuseStep 2913049 = 2184787) B2184787
theorem B5731307 : Blo 670310 5731307 := bstep (se 1 (by rfl) ⟨4298480, by rfl⟩ : syracuseStep 5731307 = 8596961) B8596961
theorem B5108831 : Blo 670310 5108831 := bstep (se 1 (by rfl) ⟨3831623, by rfl⟩ : syracuseStep 5108831 = 7663247) B7663247
theorem B1275439 : Blo 670310 1275439 := bstep (se 1 (by rfl) ⟨956579, by rfl⟩ : syracuseStep 1275439 = 1913159) B1913159
theorem B2553551 : Blo 670310 2553551 := bstep (se 1 (by rfl) ⟨1915163, by rfl⟩ : syracuseStep 2553551 = 3830327) B3830327
theorem B3636359 : Blo 670310 3636359 := bstep (se 1 (by rfl) ⟨2727269, by rfl⟩ : syracuseStep 3636359 = 5454539) B5454539
theorem B2555297 : Blo 670310 2555297 := bstep (se 2 (by rfl) ⟨958236, by rfl⟩ : syracuseStep 2555297 = 1916473) B1916473
theorem B5111747 : Blo 670310 5111747 := bstep (se 1 (by rfl) ⟨3833810, by rfl⟩ : syracuseStep 5111747 = 7667621) B7667621
theorem B1704179 : Blo 670310 1704179 := bstep (se 1 (by rfl) ⟨1278134, by rfl⟩ : syracuseStep 1704179 = 2556269) B2556269
theorem B1704199 : Blo 670310 1704199 := bstep (se 1 (by rfl) ⟨1278149, by rfl⟩ : syracuseStep 1704199 = 2556299) B2556299
theorem B1278803 : Blo 670310 1278803 := bstep (se 1 (by rfl) ⟨959102, by rfl⟩ : syracuseStep 1278803 = 1918205) B1918205
theorem B1508435 : Blo 670310 1508435 := bstep (se 1 (by rfl) ⟨1131326, by rfl⟩ : syracuseStep 1508435 = 2262653) B2262653
theorem B1508507 : Blo 670310 1508507 := bstep (se 1 (by rfl) ⟨1131380, by rfl⟩ : syracuseStep 1508507 = 2262761) B2262761
theorem B1705151 : Blo 670310 1705151 := bstep (se 1 (by rfl) ⟨1278863, by rfl⟩ : syracuseStep 1705151 = 2557727) B2557727
theorem B1279631 : Blo 670310 1279631 := bstep (se 1 (by rfl) ⟨959723, by rfl⟩ : syracuseStep 1279631 = 1919447) B1919447
theorem B2262923 : Blo 670310 2262923 := bstep (se 1 (by rfl) ⟨1697192, by rfl⟩ : syracuseStep 2262923 = 3394385) B3394385
theorem B3410585 : Blo 670310 3410585 := bstep (se 2 (by rfl) ⟨1278969, by rfl⟩ : syracuseStep 3410585 = 2557939) B2557939
theorem B2558729 : Blo 670310 2558729 := bstep (se 2 (by rfl) ⟨959523, by rfl⟩ : syracuseStep 2558729 = 1919047) B1919047
theorem B3411071 : Blo 670310 3411071 := bstep (se 1 (by rfl) ⟨2558303, by rfl⟩ : syracuseStep 3411071 = 5116607) B5116607
theorem B757183 : Blo 670310 757183 := bstep (se 1 (by rfl) ⟨567887, by rfl⟩ : syracuseStep 757183 = 1135775) B1135775
theorem B12947039 : Blo 670310 12947039 := bstep (se 1 (by rfl) ⟨9710279, by rfl⟩ : syracuseStep 12947039 = 19420559) B19420559
theorem B15536261 : Blo 670310 15536261 := bstep (se 4 (by rfl) ⟨1456524, by rfl⟩ : syracuseStep 15536261 = 2913049) B2913049
theorem B758011 : Blo 670310 758011 := bstep (se 1 (by rfl) ⟨568508, by rfl⟩ : syracuseStep 758011 = 1137017) B1137017
theorem B2462107 : Blo 670310 2462107 := bstep (se 1 (by rfl) ⟨1846580, by rfl⟩ : syracuseStep 2462107 = 3693161) B3693161
theorem B1511963 : Blo 670310 1511963 := bstep (se 1 (by rfl) ⟨1133972, by rfl⟩ : syracuseStep 1511963 = 2267945) B2267945
theorem B758479 : Blo 670310 758479 := bstep (se 1 (by rfl) ⟨568859, by rfl⟩ : syracuseStep 758479 = 1137719) B1137719
theorem B6132851 : Blo 670310 6132851 := bstep (se 1 (by rfl) ⟨4599638, by rfl⟩ : syracuseStep 6132851 = 9199277) B9199277
theorem B13768055 : Blo 670310 13768055 := bstep (se 1 (by rfl) ⟨10326041, by rfl⟩ : syracuseStep 13768055 = 20652083) B20652083
theorem B7476623 : Blo 670310 7476623 := bstep (se 1 (by rfl) ⟨5607467, by rfl⟩ : syracuseStep 7476623 = 11214935) B11214935
theorem B5740055 : Blo 670310 5740055 := bstep (se 1 (by rfl) ⟨4305041, by rfl⟩ : syracuseStep 5740055 = 8610083) B8610083
theorem B18454601 : Blo 670310 18454601 := bstep (se 2 (by rfl) ⟨6920475, by rfl⟩ : syracuseStep 18454601 = 13840951) B13840951
theorem B1514987 : Blo 670310 1514987 := bstep (se 1 (by rfl) ⟨1136240, by rfl⟩ : syracuseStep 1514987 = 2272481) B2272481
theorem B9708025 : Blo 670310 9708025 := bstep (se 2 (by rfl) ⟨3640509, by rfl⟩ : syracuseStep 9708025 = 7281019) B7281019
theorem B1516265 : Blo 670310 1516265 := bstep (se 2 (by rfl) ⟨568599, by rfl⟩ : syracuseStep 1516265 = 1137199) B1137199
theorem B1516841 : Blo 670310 1516841 := bstep (se 2 (by rfl) ⟨568815, by rfl⟩ : syracuseStep 1516841 = 1137631) B1137631
theorem B6891419 : Blo 670310 6891419 := bstep (se 1 (by rfl) ⟨5168564, by rfl⟩ : syracuseStep 6891419 = 10337129) B10337129
theorem B1812905 : Blo 670310 1812905 := bstep (se 2 (by rfl) ⟨679839, by rfl⟩ : syracuseStep 1812905 = 1359679) B1359679
theorem B2272157 : Blo 670310 2272157 := bstep (se 3 (by rfl) ⟨426029, by rfl⟩ : syracuseStep 2272157 = 852059) B852059
theorem B2731421 : Blo 670310 2731421 := bstep (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) B1024283
theorem B3059419 : Blo 670310 3059419 := bstep (se 1 (by rfl) ⟨2294564, by rfl⟩ : syracuseStep 3059419 = 4589129) B4589129
theorem B1748735 : Blo 670310 1748735 := bstep (se 1 (by rfl) ⟨1311551, by rfl⟩ : syracuseStep 1748735 = 2623103) B2623103
theorem B2765137 : Blo 670310 2765137 := bstep (se 2 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 2765137 = 2073853) B2073853
theorem B17216063 : Blo 670310 17216063 := bstep (se 1 (by rfl) ⟨12912047, by rfl⟩ : syracuseStep 17216063 = 25824095) B25824095
theorem B46445561 : Blo 670310 46445561 := bstep (se 2 (by rfl) ⟨17417085, by rfl⟩ : syracuseStep 46445561 = 34834171) B34834171
theorem B2275451 : Blo 670310 2275451 := bstep (se 1 (by rfl) ⟨1706588, by rfl⟩ : syracuseStep 2275451 = 3413177) B3413177
theorem B2046329 : Blo 670310 2046329 := bstep (se 2 (by rfl) ⟨767373, by rfl⟩ : syracuseStep 2046329 = 1534747) B1534747
theorem B670363 : Blo 670310 670363 := bstep (se 1 (by rfl) ⟨502772, by rfl⟩ : syracuseStep 670363 = 1005545) B1005545
theorem B670591 : Blo 670310 670591 := bstep (se 1 (by rfl) ⟨502943, by rfl⟩ : syracuseStep 670591 = 1005887) B1005887
theorem B2866049 : Blo 670310 2866049 := bstep (se 2 (by rfl) ⟨1074768, by rfl⟩ : syracuseStep 2866049 = 2149537) B2149537
theorem B670975 : Blo 670310 670975 := bstep (se 1 (by rfl) ⟨503231, by rfl⟩ : syracuseStep 670975 = 1006463) B1006463
theorem B671135 : Blo 670310 671135 := bstep (se 1 (by rfl) ⟨503351, by rfl⟩ : syracuseStep 671135 = 1006703) B1006703
theorem B671439 : Blo 670310 671439 := bstep (se 1 (by rfl) ⟨503579, by rfl⟩ : syracuseStep 671439 = 1007159) B1007159
theorem B671487 : Blo 670310 671487 := bstep (se 1 (by rfl) ⟨503615, by rfl⟩ : syracuseStep 671487 = 1007231) B1007231
theorem B671855 : Blo 670310 671855 := bstep (se 1 (by rfl) ⟨503891, by rfl⟩ : syracuseStep 671855 = 1007783) B1007783
theorem B1917179 : Blo 670310 1917179 := bstep (se 1 (by rfl) ⟨1437884, by rfl⟩ : syracuseStep 1917179 = 2875769) B2875769
theorem B6472325 : Blo 670310 6472325 := bstep (se 4 (by rfl) ⟨606780, by rfl⟩ : syracuseStep 6472325 = 1213561) B1213561
theorem B4080395 : Blo 670310 4080395 := bstep (se 1 (by rfl) ⟨3060296, by rfl⟩ : syracuseStep 4080395 = 6120593) B6120593
theorem B672615 : Blo 670310 672615 := bstep (se 1 (by rfl) ⟨504461, by rfl⟩ : syracuseStep 672615 = 1008923) B1008923
theorem B1131455 : Blo 670310 1131455 := bstep (se 1 (by rfl) ⟨848591, by rfl⟩ : syracuseStep 1131455 = 1697183) B1697183
theorem B1917931 : Blo 670310 1917931 := bstep (se 1 (by rfl) ⟨1438448, by rfl⟩ : syracuseStep 1917931 = 2876897) B2876897
theorem B673023 : Blo 670310 673023 := bstep (se 1 (by rfl) ⟨504767, by rfl⟩ : syracuseStep 673023 = 1009535) B1009535
theorem B8603111 : Blo 670310 8603111 := bstep (se 1 (by rfl) ⟨6452333, by rfl⟩ : syracuseStep 8603111 = 12904667) B12904667
theorem B673435 : Blo 670310 673435 := bstep (se 1 (by rfl) ⟨505076, by rfl⟩ : syracuseStep 673435 = 1010153) B1010153
theorem B673487 : Blo 670310 673487 := bstep (se 1 (by rfl) ⟨505115, by rfl⟩ : syracuseStep 673487 = 1010231) B1010231
theorem B673535 : Blo 670310 673535 := bstep (se 1 (by rfl) ⟨505151, by rfl⟩ : syracuseStep 673535 = 1010303) B1010303
theorem B9324571 : Blo 670310 9324571 := bstep (se 1 (by rfl) ⟨6993428, by rfl⟩ : syracuseStep 9324571 = 13986857) B13986857
theorem B674023 : Blo 670310 674023 := bstep (se 1 (by rfl) ⟨505517, by rfl⟩ : syracuseStep 674023 = 1011035) B1011035
theorem B674047 : Blo 670310 674047 := bstep (se 1 (by rfl) ⟨505535, by rfl⟩ : syracuseStep 674047 = 1011071) B1011071
theorem B3393899 : Blo 670310 3393899 := bstep (se 1 (by rfl) ⟨2545424, by rfl⟩ : syracuseStep 3393899 = 5090849) B5090849
theorem B1133183 : Blo 670310 1133183 := bstep (se 1 (by rfl) ⟨849887, by rfl⟩ : syracuseStep 1133183 = 1699775) B1699775
theorem B10373831 : Blo 670310 10373831 := bstep (se 1 (by rfl) ⟨7780373, by rfl⟩ : syracuseStep 10373831 = 15560747) B15560747
theorem B1920095 : Blo 670310 1920095 := bstep (se 1 (by rfl) ⟨1440071, by rfl⟩ : syracuseStep 1920095 = 2880143) B2880143
theorem B3820871 : Blo 670310 3820871 := bstep (se 1 (by rfl) ⟨2865653, by rfl⟩ : syracuseStep 3820871 = 5731307) B5731307
theorem B2149703 : Blo 670310 2149703 := bstep (se 1 (by rfl) ⟨1612277, by rfl⟩ : syracuseStep 2149703 = 3224555) B3224555
theorem B2150471 : Blo 670310 2150471 := bstep (se 1 (by rfl) ⟨1612853, by rfl⟩ : syracuseStep 2150471 = 3225707) B3225707
theorem B32658713 : Blo 670310 32658713 := bstep (se 2 (by rfl) ⟨12247017, by rfl⟩ : syracuseStep 32658713 = 24494035) B24494035
theorem B3397139 : Blo 670310 3397139 := bstep (se 1 (by rfl) ⟨2547854, by rfl⟩ : syracuseStep 3397139 = 5095709) B5095709
theorem B1005563 : Blo 670310 1005563 := bstep (se 1 (by rfl) ⟨754172, by rfl⟩ : syracuseStep 1005563 = 1508345) B1508345
theorem B1136747 : Blo 670310 1136747 := bstep (se 1 (by rfl) ⟨852560, by rfl⟩ : syracuseStep 1136747 = 1705121) B1705121
theorem B1005689 : Blo 670310 1005689 := bstep (se 2 (by rfl) ⟨377133, by rfl⟩ : syracuseStep 1005689 = 754267) B754267
theorem B1006121 : Blo 670310 1006121 := bstep (se 2 (by rfl) ⟨377295, by rfl⟩ : syracuseStep 1006121 = 754591) B754591
theorem B1006235 : Blo 670310 1006235 := bstep (se 1 (by rfl) ⟨754676, by rfl⟩ : syracuseStep 1006235 = 1509353) B1509353
theorem B1006619 : Blo 670310 1006619 := bstep (se 1 (by rfl) ⟨754964, by rfl⟩ : syracuseStep 1006619 = 1509929) B1509929
theorem B1006889 : Blo 670310 1006889 := bstep (se 2 (by rfl) ⟨377583, by rfl⟩ : syracuseStep 1006889 = 755167) B755167
theorem B1007087 : Blo 670310 1007087 := bstep (se 1 (by rfl) ⟨755315, by rfl⟩ : syracuseStep 1007087 = 1510631) B1510631
theorem B1007135 : Blo 670310 1007135 := bstep (se 1 (by rfl) ⟨755351, by rfl⟩ : syracuseStep 1007135 = 1510703) B1510703
theorem B1007387 : Blo 670310 1007387 := bstep (se 1 (by rfl) ⟨755540, by rfl⟩ : syracuseStep 1007387 = 1511081) B1511081
theorem B1007519 : Blo 670310 1007519 := bstep (se 1 (by rfl) ⟨755639, by rfl⟩ : syracuseStep 1007519 = 1511279) B1511279
theorem B2875495 : Blo 670310 2875495 := bstep (se 1 (by rfl) ⟨2156621, by rfl⟩ : syracuseStep 2875495 = 4313243) B4313243
theorem B1008095 : Blo 670310 1008095 := bstep (se 1 (by rfl) ⟨756071, by rfl⟩ : syracuseStep 1008095 = 1512143) B1512143
theorem B1008239 : Blo 670310 1008239 := bstep (se 1 (by rfl) ⟨756179, by rfl⟩ : syracuseStep 1008239 = 1512359) B1512359
theorem B13132799 : Blo 670310 13132799 := bstep (se 1 (by rfl) ⟨9849599, by rfl⟩ : syracuseStep 13132799 = 19699199) B19699199
theorem B4318217 : Blo 670310 4318217 := bstep (se 2 (by rfl) ⟨1619331, by rfl⟩ : syracuseStep 4318217 = 3238663) B3238663
theorem B3400865 : Blo 670310 3400865 := bstep (se 2 (by rfl) ⟨1275324, by rfl⟩ : syracuseStep 3400865 = 2550649) B2550649
theorem B1698043 : Blo 670310 1698043 := bstep (se 1 (by rfl) ⟨1273532, by rfl⟩ : syracuseStep 1698043 = 2547065) B2547065
theorem B2157263 : Blo 670310 2157263 := bstep (se 1 (by rfl) ⟨1617947, by rfl⟩ : syracuseStep 2157263 = 3235895) B3235895
theorem B5171951 : Blo 670310 5171951 := bstep (se 1 (by rfl) ⟨3878963, by rfl⟩ : syracuseStep 5171951 = 7757927) B7757927
theorem B1010795 : Blo 670310 1010795 := bstep (se 1 (by rfl) ⟨758096, by rfl⟩ : syracuseStep 1010795 = 1516193) B1516193
theorem B716239 : Blo 670310 716239 := bstep (se 1 (by rfl) ⟨537179, by rfl⟩ : syracuseStep 716239 = 1074359) B1074359
theorem B5533691 : Blo 670310 5533691 := bstep (se 1 (by rfl) ⟨4150268, by rfl⟩ : syracuseStep 5533691 = 8300537) B8300537
theorem B5435855 : Blo 670310 5435855 := bstep (se 1 (by rfl) ⟨4076891, by rfl⟩ : syracuseStep 5435855 = 8153783) B8153783
theorem B3404267 : Blo 670310 3404267 := bstep (se 1 (by rfl) ⟨2553200, by rfl⟩ : syracuseStep 3404267 = 5106401) B5106401
theorem B717503 : Blo 670310 717503 := bstep (se 1 (by rfl) ⟨538127, by rfl⟩ : syracuseStep 717503 = 1076255) B1076255
theorem B1700585 : Blo 670310 1700585 := bstep (se 2 (by rfl) ⟨637719, by rfl⟩ : syracuseStep 1700585 = 1275439) B1275439
theorem B3404591 : Blo 670310 3404591 := bstep (se 1 (by rfl) ⟨2553443, by rfl⟩ : syracuseStep 3404591 = 5106887) B5106887
theorem B1701071 : Blo 670310 1701071 := bstep (se 1 (by rfl) ⟨1275803, by rfl⟩ : syracuseStep 1701071 = 2551607) B2551607
theorem B1275257 : Blo 670310 1275257 := bstep (se 2 (by rfl) ⟨478221, by rfl⟩ : syracuseStep 1275257 = 956443) B956443
theorem B3405887 : Blo 670310 3405887 := bstep (se 1 (by rfl) ⟨2554415, by rfl⟩ : syracuseStep 3405887 = 5108831) B5108831
theorem B2717833 : Blo 670310 2717833 := bstep (se 2 (by rfl) ⟨1019187, by rfl⟩ : syracuseStep 2717833 = 2038375) B2038375
theorem B1702367 : Blo 670310 1702367 := bstep (se 1 (by rfl) ⟨1276775, by rfl⟩ : syracuseStep 1702367 = 2553551) B2553551
theorem B2424239 : Blo 670310 2424239 := bstep (se 1 (by rfl) ⟨1818179, by rfl⟩ : syracuseStep 2424239 = 3636359) B3636359
theorem B1703531 : Blo 670310 1703531 := bstep (se 1 (by rfl) ⟨1277648, by rfl⟩ : syracuseStep 1703531 = 2555297) B2555297
theorem B3407831 : Blo 670310 3407831 := bstep (se 1 (by rfl) ⟨2555873, by rfl⟩ : syracuseStep 3407831 = 5111747) B5111747
theorem B3833993 : Blo 670310 3833993 := bstep (se 2 (by rfl) ⟨1437747, by rfl⟩ : syracuseStep 3833993 = 2875495) B2875495
theorem B1278119 : Blo 670310 1278119 := bstep (se 1 (by rfl) ⟨958589, by rfl⟩ : syracuseStep 1278119 = 1917179) B1917179
theorem B852535 : Blo 670310 852535 := bstep (se 1 (by rfl) ⟨639401, by rfl⟩ : syracuseStep 852535 = 1278803) B1278803
theorem B754303 : Blo 670310 754303 := bstep (se 1 (by rfl) ⟨565727, by rfl⟩ : syracuseStep 754303 = 1131455) B1131455
theorem B12944033 : Blo 670310 12944033 := bstep (se 2 (by rfl) ⟨4854012, by rfl⟩ : syracuseStep 12944033 = 9708025) B9708025
theorem B5735407 : Blo 670310 5735407 := bstep (se 1 (by rfl) ⟨4301555, by rfl⟩ : syracuseStep 5735407 = 8603111) B8603111
theorem B853087 : Blo 670310 853087 := bstep (se 1 (by rfl) ⟨639815, by rfl⟩ : syracuseStep 853087 = 1279631) B1279631
theorem B1508615 : Blo 670310 1508615 := bstep (se 1 (by rfl) ⟨1131461, by rfl⟩ : syracuseStep 1508615 = 2262923) B2262923
theorem B2557241 : Blo 670310 2557241 := bstep (se 2 (by rfl) ⟨958965, by rfl⟩ : syracuseStep 2557241 = 1917931) B1917931
theorem B2262599 : Blo 670310 2262599 := bstep (se 1 (by rfl) ⟨1696949, by rfl⟩ : syracuseStep 2262599 = 3393899) B3393899
theorem B755455 : Blo 670310 755455 := bstep (se 1 (by rfl) ⟨566591, by rfl⟩ : syracuseStep 755455 = 1133183) B1133183
theorem B6915887 : Blo 670310 6915887 := bstep (se 1 (by rfl) ⟨5186915, by rfl⟩ : syracuseStep 6915887 = 10373831) B10373831
theorem B1705819 : Blo 670310 1705819 := bstep (se 1 (by rfl) ⟨1279364, by rfl⟩ : syracuseStep 1705819 = 2558729) B2558729
theorem B10881053 : Blo 670310 10881053 := bstep (se 3 (by rfl) ⟨2040197, by rfl⟩ : syracuseStep 10881053 = 4080395) B4080395
theorem B1280063 : Blo 670310 1280063 := bstep (se 1 (by rfl) ⟨960047, by rfl⟩ : syracuseStep 1280063 = 1920095) B1920095
theorem B10357507 : Blo 670310 10357507 := bstep (se 1 (by rfl) ⟨7768130, by rfl⟩ : syracuseStep 10357507 = 15536261) B15536261
theorem B2264057 : Blo 670310 2264057 := bstep (se 2 (by rfl) ⟨849021, by rfl⟩ : syracuseStep 2264057 = 1698043) B1698043
theorem B9178703 : Blo 670310 9178703 := bstep (se 1 (by rfl) ⟨6884027, by rfl⟩ : syracuseStep 9178703 = 13768055) B13768055
theorem B4984415 : Blo 670310 4984415 := bstep (se 1 (by rfl) ⟨3738311, by rfl⟩ : syracuseStep 4984415 = 7476623) B7476623
theorem B2264759 : Blo 670310 2264759 := bstep (se 1 (by rfl) ⟨1698569, by rfl⟩ : syracuseStep 2264759 = 3397139) B3397139
theorem B757831 : Blo 670310 757831 := bstep (se 1 (by rfl) ⟨568373, by rfl⟩ : syracuseStep 757831 = 1136747) B1136747
theorem B954985 : Blo 670310 954985 := bstep (se 2 (by rfl) ⟨358119, by rfl⟩ : syracuseStep 954985 = 716239) B716239
theorem B3282809 : Blo 670310 3282809 := bstep (se 2 (by rfl) ⟨1231053, by rfl⟩ : syracuseStep 3282809 = 2462107) B2462107
theorem B8755199 : Blo 670310 8755199 := bstep (se 1 (by rfl) ⟨6566399, by rfl⟩ : syracuseStep 8755199 = 13132799) B13132799
theorem B2267243 : Blo 670310 2267243 := bstep (se 1 (by rfl) ⟨1700432, by rfl⟩ : syracuseStep 2267243 = 3400865) B3400865
theorem B4594279 : Blo 670310 4594279 := bstep (se 1 (by rfl) ⟨3445709, by rfl⟩ : syracuseStep 4594279 = 6891419) B6891419
theorem B3447967 : Blo 670310 3447967 := bstep (se 1 (by rfl) ⟨2585975, by rfl⟩ : syracuseStep 3447967 = 5171951) B5171951
theorem B1514771 : Blo 670310 1514771 := bstep (se 1 (by rfl) ⟨1136078, by rfl⟩ : syracuseStep 1514771 = 2272157) B2272157
theorem B2269511 : Blo 670310 2269511 := bstep (se 1 (by rfl) ⟨1702133, by rfl⟩ : syracuseStep 2269511 = 3404267) B3404267
theorem B11477375 : Blo 670310 11477375 := bstep (se 1 (by rfl) ⟨8608031, by rfl⟩ : syracuseStep 11477375 = 17216063) B17216063
theorem B2269727 : Blo 670310 2269727 := bstep (se 1 (by rfl) ⟨1702295, by rfl⟩ : syracuseStep 2269727 = 3404591) B3404591
theorem B7283789 : Blo 670310 7283789 := bstep (se 3 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 7283789 = 2731421) B2731421
theorem B2270591 : Blo 670310 2270591 := bstep (se 1 (by rfl) ⟨1702943, by rfl⟩ : syracuseStep 2270591 = 3405887) B3405887
theorem B1516967 : Blo 670310 1516967 := bstep (se 1 (by rfl) ⟨1137725, by rfl⟩ : syracuseStep 1516967 = 2275451) B2275451
theorem B1910699 : Blo 670310 1910699 := bstep (se 1 (by rfl) ⟨1433024, by rfl⟩ : syracuseStep 1910699 = 2866049) B2866049
theorem B1616159 : Blo 670310 1616159 := bstep (se 1 (by rfl) ⟨1212119, by rfl⟩ : syracuseStep 1616159 = 2424239) B2424239
theorem B2271887 : Blo 670310 2271887 := bstep (se 1 (by rfl) ⟨1703915, by rfl⟩ : syracuseStep 2271887 = 3407831) B3407831
theorem B14756509 : Blo 670310 14756509 := bstep (se 3 (by rfl) ⟨2766845, by rfl⟩ : syracuseStep 14756509 = 5533691) B5533691
theorem B2272265 : Blo 670310 2272265 := bstep (se 2 (by rfl) ⟨852099, by rfl⟩ : syracuseStep 2272265 = 1704199) B1704199
theorem B2273723 : Blo 670310 2273723 := bstep (se 1 (by rfl) ⟨1705292, by rfl⟩ : syracuseStep 2273723 = 3410585) B3410585
theorem B1913341 : Blo 670310 1913341 := bstep (se 3 (by rfl) ⟨358751, by rfl⟩ : syracuseStep 1913341 = 717503) B717503
theorem B2274047 : Blo 670310 2274047 := bstep (se 1 (by rfl) ⟨1705535, by rfl⟩ : syracuseStep 2274047 = 3411071) B3411071
theorem B8631359 : Blo 670310 8631359 := bstep (se 1 (by rfl) ⟨6473519, by rfl⟩ : syracuseStep 8631359 = 12947039) B12947039
theorem B12432761 : Blo 670310 12432761 := bstep (se 2 (by rfl) ⟨4662285, by rfl⟩ : syracuseStep 12432761 = 9324571) B9324571
theorem B21772475 : Blo 670310 21772475 := bstep (se 1 (by rfl) ⟨16329356, by rfl⟩ : syracuseStep 21772475 = 32658713) B32658713
theorem B670375 : Blo 670310 670375 := bstep (se 1 (by rfl) ⟨502781, by rfl⟩ : syracuseStep 670375 = 1005563) B1005563
theorem B670459 : Blo 670310 670459 := bstep (se 1 (by rfl) ⟨502844, by rfl⟩ : syracuseStep 670459 = 1005689) B1005689
theorem B670747 : Blo 670310 670747 := bstep (se 1 (by rfl) ⟨503060, by rfl⟩ : syracuseStep 670747 = 1006121) B1006121
theorem B670823 : Blo 670310 670823 := bstep (se 1 (by rfl) ⟨503117, by rfl⟩ : syracuseStep 670823 = 1006235) B1006235
theorem B671079 : Blo 670310 671079 := bstep (se 1 (by rfl) ⟨503309, by rfl⟩ : syracuseStep 671079 = 1006619) B1006619
theorem B671259 : Blo 670310 671259 := bstep (se 1 (by rfl) ⟨503444, by rfl⟩ : syracuseStep 671259 = 1006889) B1006889
theorem B4079225 : Blo 670310 4079225 := bstep (se 2 (by rfl) ⟨1529709, by rfl⟩ : syracuseStep 4079225 = 3059419) B3059419
theorem B671391 : Blo 670310 671391 := bstep (se 1 (by rfl) ⟨503543, by rfl⟩ : syracuseStep 671391 = 1007087) B1007087
theorem B671423 : Blo 670310 671423 := bstep (se 1 (by rfl) ⟨503567, by rfl⟩ : syracuseStep 671423 = 1007135) B1007135
theorem B671591 : Blo 670310 671591 := bstep (se 1 (by rfl) ⟨503693, by rfl⟩ : syracuseStep 671591 = 1007387) B1007387
theorem B671679 : Blo 670310 671679 := bstep (se 1 (by rfl) ⟨503759, by rfl⟩ : syracuseStep 671679 = 1007519) B1007519
theorem B672063 : Blo 670310 672063 := bstep (se 1 (by rfl) ⟨504047, by rfl⟩ : syracuseStep 672063 = 1008095) B1008095
theorem B672159 : Blo 670310 672159 := bstep (se 1 (by rfl) ⟨504119, by rfl⟩ : syracuseStep 672159 = 1008239) B1008239
theorem B3686849 : Blo 670310 3686849 := bstep (se 2 (by rfl) ⟨1382568, by rfl⟩ : syracuseStep 3686849 = 2765137) B2765137
theorem B673863 : Blo 670310 673863 := bstep (se 1 (by rfl) ⟨505397, by rfl⟩ : syracuseStep 673863 = 1010795) B1010795
theorem B1165823 : Blo 670310 1165823 := bstep (se 1 (by rfl) ⟨874367, by rfl⟩ : syracuseStep 1165823 = 1748735) B1748735
theorem B3623777 : Blo 670310 3623777 := bstep (se 2 (by rfl) ⟨1358916, by rfl⟩ : syracuseStep 3623777 = 2717833) B2717833
theorem B3623903 : Blo 670310 3623903 := bstep (se 1 (by rfl) ⟨2717927, by rfl⟩ : syracuseStep 3623903 = 5435855) B5435855
theorem B1133723 : Blo 670310 1133723 := bstep (se 1 (by rfl) ⟨850292, by rfl⟩ : syracuseStep 1133723 = 1700585) B1700585
theorem B1134047 : Blo 670310 1134047 := bstep (se 1 (by rfl) ⟨850535, by rfl⟩ : syracuseStep 1134047 = 1701071) B1701071
theorem B1364219 : Blo 670310 1364219 := bstep (se 1 (by rfl) ⟨1023164, by rfl⟩ : syracuseStep 1364219 = 2046329) B2046329
theorem B1134911 : Blo 670310 1134911 := bstep (se 1 (by rfl) ⟨851183, by rfl⟩ : syracuseStep 1134911 = 1702367) B1702367
theorem B1135687 : Blo 670310 1135687 := bstep (se 1 (by rfl) ⟨851765, by rfl⟩ : syracuseStep 1135687 = 1703531) B1703531
theorem B1136119 : Blo 670310 1136119 := bstep (se 1 (by rfl) ⟨852089, by rfl⟩ : syracuseStep 1136119 = 1704179) B1704179
theorem B4314883 : Blo 670310 4314883 := bstep (se 1 (by rfl) ⟨3236162, by rfl⟩ : syracuseStep 4314883 = 6472325) B6472325
theorem B1005623 : Blo 670310 1005623 := bstep (se 1 (by rfl) ⟨754217, by rfl⟩ : syracuseStep 1005623 = 1508435) B1508435
theorem B1005671 : Blo 670310 1005671 := bstep (se 1 (by rfl) ⟨754253, by rfl⟩ : syracuseStep 1005671 = 1508507) B1508507
theorem B1136767 : Blo 670310 1136767 := bstep (se 1 (by rfl) ⟨852575, by rfl⟩ : syracuseStep 1136767 = 1705151) B1705151
theorem B2547247 : Blo 670310 2547247 := bstep (se 1 (by rfl) ⟨1910435, by rfl⟩ : syracuseStep 2547247 = 3820871) B3820871
theorem B1433135 : Blo 670310 1433135 := bstep (se 1 (by rfl) ⟨1074851, by rfl⟩ : syracuseStep 1433135 = 2149703) B2149703
theorem B1433647 : Blo 670310 1433647 := bstep (se 1 (by rfl) ⟨1075235, by rfl⟩ : syracuseStep 1433647 = 2150471) B2150471
theorem B1007975 : Blo 670310 1007975 := bstep (se 1 (by rfl) ⟨755981, by rfl⟩ : syracuseStep 1007975 = 1511963) B1511963
theorem B4088567 : Blo 670310 4088567 := bstep (se 1 (by rfl) ⟨3066425, by rfl⟩ : syracuseStep 4088567 = 6132851) B6132851
theorem B3826703 : Blo 670310 3826703 := bstep (se 1 (by rfl) ⟨2870027, by rfl⟩ : syracuseStep 3826703 = 5740055) B5740055
theorem B1009577 : Blo 670310 1009577 := bstep (se 2 (by rfl) ⟨378591, by rfl⟩ : syracuseStep 1009577 = 757183) B757183
theorem B1009991 : Blo 670310 1009991 := bstep (se 1 (by rfl) ⟨757493, by rfl⟩ : syracuseStep 1009991 = 1514987) B1514987
theorem B49212269 : Blo 670310 49212269 := bstep (se 3 (by rfl) ⟨9227300, by rfl⟩ : syracuseStep 49212269 = 18454601) B18454601
theorem B1010681 : Blo 670310 1010681 := bstep (se 2 (by rfl) ⟨379005, by rfl⟩ : syracuseStep 1010681 = 758011) B758011
theorem B1010843 : Blo 670310 1010843 := bstep (se 1 (by rfl) ⟨758132, by rfl⟩ : syracuseStep 1010843 = 1516265) B1516265
theorem B2878811 : Blo 670310 2878811 := bstep (se 1 (by rfl) ⟨2159108, by rfl⟩ : syracuseStep 2878811 = 4318217) B4318217
theorem B1011227 : Blo 670310 1011227 := bstep (se 1 (by rfl) ⟨758420, by rfl⟩ : syracuseStep 1011227 = 1516841) B1516841
theorem B1011305 : Blo 670310 1011305 := bstep (se 2 (by rfl) ⟨379239, by rfl⟩ : syracuseStep 1011305 = 758479) B758479
theorem B1208603 : Blo 670310 1208603 := bstep (se 1 (by rfl) ⟨906452, by rfl⟩ : syracuseStep 1208603 = 1812905) B1812905
theorem B1438175 : Blo 670310 1438175 := bstep (se 1 (by rfl) ⟨1078631, by rfl⟩ : syracuseStep 1438175 = 2157263) B2157263
theorem B30963707 : Blo 670310 30963707 := bstep (se 1 (by rfl) ⟨23222780, by rfl⟩ : syracuseStep 30963707 = 46445561) B46445561
theorem B850171 : Blo 670310 850171 := bstep (se 1 (by rfl) ⟨637628, by rfl⟩ : syracuseStep 850171 = 1275257) B1275257
theorem B2555995 : Blo 670310 2555995 := bstep (se 1 (by rfl) ⟨1916996, by rfl⟩ : syracuseStep 2555995 = 3833993) B3833993
theorem B2457899 : Blo 670310 2457899 := bstep (se 1 (by rfl) ⟨1843424, by rfl⟩ : syracuseStep 2457899 = 3686849) B3686849
theorem B3408317 : Blo 670310 3408317 := bstep (se 3 (by rfl) ⟨639059, by rfl⟩ : syracuseStep 3408317 = 1278119) B1278119
theorem B1704827 : Blo 670310 1704827 := bstep (se 1 (by rfl) ⟨1278620, by rfl⟩ : syracuseStep 1704827 = 2557241) B2557241
theorem B1508399 : Blo 670310 1508399 := bstep (se 1 (by rfl) ⟨1131299, by rfl⟩ : syracuseStep 1508399 = 2262599) B2262599
theorem B3835133 : Blo 670310 3835133 := bstep (se 3 (by rfl) ⟨719087, by rfl⟩ : syracuseStep 3835133 = 1438175) B1438175
theorem B1509371 : Blo 670310 1509371 := bstep (se 1 (by rfl) ⟨1132028, by rfl⟩ : syracuseStep 1509371 = 2264057) B2264057
theorem B755815 : Blo 670310 755815 := bstep (se 1 (by rfl) ⟨566861, by rfl⟩ : syracuseStep 755815 = 1133723) B1133723
theorem B756031 : Blo 670310 756031 := bstep (se 1 (by rfl) ⟨567023, by rfl⟩ : syracuseStep 756031 = 1134047) B1134047
theorem B1509839 : Blo 670310 1509839 := bstep (se 1 (by rfl) ⟨1132379, by rfl⟩ : syracuseStep 1509839 = 2264759) B2264759
theorem B756607 : Blo 670310 756607 := bstep (se 1 (by rfl) ⟨567455, by rfl⟩ : syracuseStep 756607 = 1134911) B1134911
theorem B5836799 : Blo 670310 5836799 := bstep (se 1 (by rfl) ⟨4377599, by rfl⟩ : syracuseStep 5836799 = 8755199) B8755199
theorem B1511495 : Blo 670310 1511495 := bstep (se 1 (by rfl) ⟨1133621, by rfl⟩ : syracuseStep 1511495 = 2267243) B2267243
theorem B8754157 : Blo 670310 8754157 := bstep (se 3 (by rfl) ⟨1641404, by rfl⟩ : syracuseStep 8754157 = 3282809) B3282809
theorem B955423 : Blo 670310 955423 := bstep (se 1 (by rfl) ⟨716567, by rfl⟩ : syracuseStep 955423 = 1433135) B1433135
theorem B3413501 : Blo 670310 3413501 := bstep (se 3 (by rfl) ⟨640031, by rfl⟩ : syracuseStep 3413501 = 1280063) B1280063
theorem B1513007 : Blo 670310 1513007 := bstep (se 1 (by rfl) ⟨1134755, by rfl⟩ : syracuseStep 1513007 = 2269511) B2269511
theorem B1513151 : Blo 670310 1513151 := bstep (se 1 (by rfl) ⟨1134863, by rfl⟩ : syracuseStep 1513151 = 2269727) B2269727
theorem B4855859 : Blo 670310 4855859 := bstep (se 1 (by rfl) ⟨3641894, by rfl⟩ : syracuseStep 4855859 = 7283789) B7283789
theorem B1513727 : Blo 670310 1513727 := bstep (se 1 (by rfl) ⟨1135295, by rfl⟩ : syracuseStep 1513727 = 2270591) B2270591
theorem B1514249 : Blo 670310 1514249 := bstep (se 2 (by rfl) ⟨567843, by rfl⟩ : syracuseStep 1514249 = 1135687) B1135687
theorem B1514591 : Blo 670310 1514591 := bstep (se 1 (by rfl) ⟨1135943, by rfl⟩ : syracuseStep 1514591 = 2271887) B2271887
theorem B32808179 : Blo 670310 32808179 := bstep (se 1 (by rfl) ⟨24606134, by rfl⟩ : syracuseStep 32808179 = 49212269) B49212269
theorem B1514825 : Blo 670310 1514825 := bstep (se 2 (by rfl) ⟨568059, by rfl⟩ : syracuseStep 1514825 = 1136119) B1136119
theorem B1514843 : Blo 670310 1514843 := bstep (se 1 (by rfl) ⟨1136132, by rfl⟩ : syracuseStep 1514843 = 2272265) B2272265
theorem B1515689 : Blo 670310 1515689 := bstep (se 2 (by rfl) ⟨568383, by rfl⟩ : syracuseStep 1515689 = 1136767) B1136767
theorem B1515815 : Blo 670310 1515815 := bstep (se 1 (by rfl) ⟨1136861, by rfl⟩ : syracuseStep 1515815 = 2273723) B2273723
theorem B1516031 : Blo 670310 1516031 := bstep (se 1 (by rfl) ⟨1137023, by rfl⟩ : syracuseStep 1516031 = 2274047) B2274047
theorem B4597289 : Blo 670310 4597289 := bstep (se 2 (by rfl) ⟨1723983, by rfl⟩ : syracuseStep 4597289 = 3447967) B3447967
theorem B1911529 : Blo 670310 1911529 := bstep (se 2 (by rfl) ⟨716823, by rfl⟩ : syracuseStep 1911529 = 1433647) B1433647
theorem B8629355 : Blo 670310 8629355 := bstep (se 1 (by rfl) ⟨6472016, by rfl⟩ : syracuseStep 8629355 = 12944033) B12944033
theorem B7647209 : Blo 670310 7647209 := bstep (se 2 (by rfl) ⟨2867703, by rfl⟩ : syracuseStep 7647209 = 5735407) B5735407
theorem B7254035 : Blo 670310 7254035 := bstep (se 1 (by rfl) ⟨5440526, by rfl⟩ : syracuseStep 7254035 = 10881053) B10881053
theorem B3322943 : Blo 670310 3322943 := bstep (se 1 (by rfl) ⟨2492207, by rfl⟩ : syracuseStep 3322943 = 4984415) B4984415
theorem B2274425 : Blo 670310 2274425 := bstep (se 2 (by rfl) ⟨852909, by rfl⟩ : syracuseStep 2274425 = 1705819) B1705819
theorem B19675345 : Blo 670310 19675345 := bstep (se 2 (by rfl) ⟨7378254, by rfl⟩ : syracuseStep 19675345 = 14756509) B14756509
theorem B13810009 : Blo 670310 13810009 := bstep (se 2 (by rfl) ⟨5178753, by rfl⟩ : syracuseStep 13810009 = 10357507) B10357507
theorem B670415 : Blo 670310 670415 := bstep (se 1 (by rfl) ⟨502811, by rfl⟩ : syracuseStep 670415 = 1005623) B1005623
theorem B670447 : Blo 670310 670447 := bstep (se 1 (by rfl) ⟨502835, by rfl⟩ : syracuseStep 670447 = 1005671) B1005671
theorem B671983 : Blo 670310 671983 := bstep (se 1 (by rfl) ⟨503987, by rfl⟩ : syracuseStep 671983 = 1007975) B1007975
theorem B7651583 : Blo 670310 7651583 := bstep (se 1 (by rfl) ⟨5738687, by rfl⟩ : syracuseStep 7651583 = 11477375) B11477375
theorem B4309757 : Blo 670310 4309757 := bstep (se 3 (by rfl) ⟨808079, by rfl⟩ : syracuseStep 4309757 = 1616159) B1616159
theorem B673051 : Blo 670310 673051 := bstep (se 1 (by rfl) ⟨504788, by rfl⟩ : syracuseStep 673051 = 1009577) B1009577
theorem B673327 : Blo 670310 673327 := bstep (se 1 (by rfl) ⟨504995, by rfl⟩ : syracuseStep 673327 = 1009991) B1009991
theorem B673787 : Blo 670310 673787 := bstep (se 1 (by rfl) ⟨505340, by rfl⟩ : syracuseStep 673787 = 1010681) B1010681
theorem B673895 : Blo 670310 673895 := bstep (se 1 (by rfl) ⟨505421, by rfl⟩ : syracuseStep 673895 = 1010843) B1010843
theorem B1919207 : Blo 670310 1919207 := bstep (se 1 (by rfl) ⟨1439405, by rfl⟩ : syracuseStep 1919207 = 2878811) B2878811
theorem B5753177 : Blo 670310 5753177 := bstep (se 2 (by rfl) ⟨2157441, by rfl⟩ : syracuseStep 5753177 = 4314883) B4314883
theorem B674151 : Blo 670310 674151 := bstep (se 1 (by rfl) ⟨505613, by rfl⟩ : syracuseStep 674151 = 1011227) B1011227
theorem B674203 : Blo 670310 674203 := bstep (se 1 (by rfl) ⟨505652, by rfl⟩ : syracuseStep 674203 = 1011305) B1011305
theorem B805735 : Blo 670310 805735 := bstep (se 1 (by rfl) ⟨604301, by rfl⟩ : syracuseStep 805735 = 1208603) B1208603
theorem B1133561 : Blo 670310 1133561 := bstep (se 2 (by rfl) ⟨425085, by rfl⟩ : syracuseStep 1133561 = 850171) B850171
theorem B5754239 : Blo 670310 5754239 := bstep (se 1 (by rfl) ⟨4315679, by rfl⟩ : syracuseStep 5754239 = 8631359) B8631359
theorem B3396329 : Blo 670310 3396329 := bstep (se 2 (by rfl) ⟨1273623, by rfl⟩ : syracuseStep 3396329 = 2547247) B2547247
theorem B1136713 : Blo 670310 1136713 := bstep (se 2 (by rfl) ⟨426267, by rfl⟩ : syracuseStep 1136713 = 852535) B852535
theorem B1005737 : Blo 670310 1005737 := bstep (se 2 (by rfl) ⟨377151, by rfl⟩ : syracuseStep 1005737 = 754303) B754303
theorem B1005743 : Blo 670310 1005743 := bstep (se 1 (by rfl) ⟨754307, by rfl⟩ : syracuseStep 1005743 = 1508615) B1508615
theorem B4610591 : Blo 670310 4610591 := bstep (se 1 (by rfl) ⟨3457943, by rfl⟩ : syracuseStep 4610591 = 6915887) B6915887
theorem B1137449 : Blo 670310 1137449 := bstep (se 2 (by rfl) ⟨426543, by rfl⟩ : syracuseStep 1137449 = 853087) B853087
theorem B777215 : Blo 670310 777215 := bstep (se 1 (by rfl) ⟨582911, by rfl⟩ : syracuseStep 777215 = 1165823) B1165823
theorem B2415851 : Blo 670310 2415851 := bstep (se 1 (by rfl) ⟨1811888, by rfl⟩ : syracuseStep 2415851 = 3623777) B3623777
theorem B10902845 : Blo 670310 10902845 := bstep (se 3 (by rfl) ⟨2044283, by rfl⟩ : syracuseStep 10902845 = 4088567) B4088567
theorem B2415935 : Blo 670310 2415935 := bstep (se 1 (by rfl) ⟨1811951, by rfl⟩ : syracuseStep 2415935 = 3623903) B3623903
theorem B1007273 : Blo 670310 1007273 := bstep (se 2 (by rfl) ⟨377727, by rfl⟩ : syracuseStep 1007273 = 755455) B755455
theorem B6119135 : Blo 670310 6119135 := bstep (se 1 (by rfl) ⟨4589351, by rfl⟩ : syracuseStep 6119135 = 9178703) B9178703
theorem B909479 : Blo 670310 909479 := bstep (se 1 (by rfl) ⟨682109, by rfl⟩ : syracuseStep 909479 = 1364219) B1364219
theorem B1009847 : Blo 670310 1009847 := bstep (se 1 (by rfl) ⟨757385, by rfl⟩ : syracuseStep 1009847 = 1514771) B1514771
theorem B1010441 : Blo 670310 1010441 := bstep (se 2 (by rfl) ⟨378915, by rfl⟩ : syracuseStep 1010441 = 757831) B757831
theorem B2551121 : Blo 670310 2551121 := bstep (se 2 (by rfl) ⟨956670, by rfl⟩ : syracuseStep 2551121 = 1913341) B1913341
theorem B2551135 : Blo 670310 2551135 := bstep (se 1 (by rfl) ⟨1913351, by rfl⟩ : syracuseStep 2551135 = 3826703) B3826703
theorem B1273313 : Blo 670310 1273313 := bstep (se 2 (by rfl) ⟨477492, by rfl⟩ : syracuseStep 1273313 = 954985) B954985
theorem B1011311 : Blo 670310 1011311 := bstep (se 1 (by rfl) ⟨758483, by rfl⟩ : syracuseStep 1011311 = 1516967) B1516967
theorem B1273799 : Blo 670310 1273799 := bstep (se 1 (by rfl) ⟨955349, by rfl⟩ : syracuseStep 1273799 = 1910699) B1910699
theorem B6125705 : Blo 670310 6125705 := bstep (se 2 (by rfl) ⟨2297139, by rfl⟩ : syracuseStep 6125705 = 4594279) B4594279
theorem B8288507 : Blo 670310 8288507 := bstep (se 1 (by rfl) ⟨6216380, by rfl⟩ : syracuseStep 8288507 = 12432761) B12432761
theorem B20642471 : Blo 670310 20642471 := bstep (se 1 (by rfl) ⟨15481853, by rfl⟩ : syracuseStep 20642471 = 30963707) B30963707
theorem B14514983 : Blo 670310 14514983 := bstep (se 1 (by rfl) ⟨10886237, by rfl⟩ : syracuseStep 14514983 = 21772475) B21772475
theorem B10877933 : Blo 670310 10877933 := bstep (se 3 (by rfl) ⟨2039612, by rfl⟩ : syracuseStep 10877933 = 4079225) B4079225
theorem B3407993 : Blo 670310 3407993 := bstep (se 2 (by rfl) ⟨1277997, by rfl⟩ : syracuseStep 3407993 = 2555995) B2555995
theorem B1638599 : Blo 670310 1638599 := bstep (se 1 (by rfl) ⟨1228949, by rfl⟩ : syracuseStep 1638599 = 2457899) B2457899
theorem B2425277 : Blo 670310 2425277 := bstep (se 3 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 2425277 = 909479) B909479
theorem B2556755 : Blo 670310 2556755 := bstep (se 1 (by rfl) ⟨1917566, by rfl⟩ : syracuseStep 2556755 = 3835133) B3835133
theorem B1279471 : Blo 670310 1279471 := bstep (se 1 (by rfl) ⟨959603, by rfl⟩ : syracuseStep 1279471 = 1919207) B1919207
theorem B3835451 : Blo 670310 3835451 := bstep (se 1 (by rfl) ⟨2876588, by rfl⟩ : syracuseStep 3835451 = 5753177) B5753177
theorem B755707 : Blo 670310 755707 := bstep (se 1 (by rfl) ⟨566780, by rfl⟩ : syracuseStep 755707 = 1133561) B1133561
theorem B3836159 : Blo 670310 3836159 := bstep (se 1 (by rfl) ⟨2877119, by rfl⟩ : syracuseStep 3836159 = 5754239) B5754239
theorem B2264219 : Blo 670310 2264219 := bstep (se 1 (by rfl) ⟨1698164, by rfl⟩ : syracuseStep 2264219 = 3396329) B3396329
theorem B758299 : Blo 670310 758299 := bstep (se 1 (by rfl) ⟨568724, by rfl⟩ : syracuseStep 758299 = 1137449) B1137449
theorem B1610567 : Blo 670310 1610567 := bstep (se 1 (by rfl) ⟨1207925, by rfl⟩ : syracuseStep 1610567 = 2415851) B2415851
theorem B1610623 : Blo 670310 1610623 := bstep (se 1 (by rfl) ⟨1207967, by rfl⟩ : syracuseStep 1610623 = 2415935) B2415935
theorem B11672209 : Blo 670310 11672209 := bstep (se 2 (by rfl) ⟨4377078, by rfl⟩ : syracuseStep 11672209 = 8754157) B8754157
theorem B29007821 : Blo 670310 29007821 := bstep (se 3 (by rfl) ⟨5438966, by rfl⟩ : syracuseStep 29007821 = 10877933) B10877933
theorem B2072573 : Blo 670310 2072573 := bstep (se 3 (by rfl) ⟨388607, by rfl⟩ : syracuseStep 2072573 = 777215) B777215
theorem B1515617 : Blo 670310 1515617 := bstep (se 2 (by rfl) ⟨568356, by rfl⟩ : syracuseStep 1515617 = 1136713) B1136713
theorem B1516283 : Blo 670310 1516283 := bstep (se 1 (by rfl) ⟨1137212, by rfl⟩ : syracuseStep 1516283 = 2274425) B2274425
theorem B9676655 : Blo 670310 9676655 := bstep (se 1 (by rfl) ⟨7257491, by rfl⟩ : syracuseStep 9676655 = 14514983) B14514983
theorem B2272211 : Blo 670310 2272211 := bstep (se 1 (by rfl) ⟨1704158, by rfl⟩ : syracuseStep 2272211 = 3408317) B3408317
theorem B2275667 : Blo 670310 2275667 := bstep (se 1 (by rfl) ⟨1706750, by rfl⟩ : syracuseStep 2275667 = 3413501) B3413501
theorem B670491 : Blo 670310 670491 := bstep (se 1 (by rfl) ⟨502868, by rfl⟩ : syracuseStep 670491 = 1005737) B1005737
theorem B670495 : Blo 670310 670495 := bstep (se 1 (by rfl) ⟨502871, by rfl⟩ : syracuseStep 670495 = 1005743) B1005743
theorem B21872119 : Blo 670310 21872119 := bstep (se 1 (by rfl) ⟨16404089, by rfl⟩ : syracuseStep 21872119 = 32808179) B32808179
theorem B671515 : Blo 670310 671515 := bstep (se 1 (by rfl) ⟨503636, by rfl⟩ : syracuseStep 671515 = 1007273) B1007273
theorem B4079423 : Blo 670310 4079423 := bstep (se 1 (by rfl) ⟨3059567, by rfl⟩ : syracuseStep 4079423 = 6119135) B6119135
theorem B3064859 : Blo 670310 3064859 := bstep (se 1 (by rfl) ⟨2298644, by rfl⟩ : syracuseStep 3064859 = 4597289) B4597289
theorem B673231 : Blo 670310 673231 := bstep (se 1 (by rfl) ⟨504923, by rfl⟩ : syracuseStep 673231 = 1009847) B1009847
theorem B673627 : Blo 670310 673627 := bstep (se 1 (by rfl) ⟨505220, by rfl⟩ : syracuseStep 673627 = 1010441) B1010441
theorem B5752903 : Blo 670310 5752903 := bstep (se 1 (by rfl) ⟨4314677, by rfl⟩ : syracuseStep 5752903 = 8629355) B8629355
theorem B674207 : Blo 670310 674207 := bstep (se 1 (by rfl) ⟨505655, by rfl⟩ : syracuseStep 674207 = 1011311) B1011311
theorem B5098139 : Blo 670310 5098139 := bstep (se 1 (by rfl) ⟨3823604, by rfl⟩ : syracuseStep 5098139 = 7647209) B7647209
theorem B4836023 : Blo 670310 4836023 := bstep (se 1 (by rfl) ⟨3627017, by rfl⟩ : syracuseStep 4836023 = 7254035) B7254035
theorem B26233793 : Blo 670310 26233793 := bstep (se 2 (by rfl) ⟨9837672, by rfl⟩ : syracuseStep 26233793 = 19675345) B19675345
theorem B2215295 : Blo 670310 2215295 := bstep (se 1 (by rfl) ⟨1661471, by rfl⟩ : syracuseStep 2215295 = 3322943) B3322943
theorem B4083803 : Blo 670310 4083803 := bstep (se 1 (by rfl) ⟨3062852, by rfl⟩ : syracuseStep 4083803 = 6125705) B6125705
theorem B5525671 : Blo 670310 5525671 := bstep (se 1 (by rfl) ⟨4144253, by rfl⟩ : syracuseStep 5525671 = 8288507) B8288507
theorem B5101055 : Blo 670310 5101055 := bstep (se 1 (by rfl) ⟨3825791, by rfl⟩ : syracuseStep 5101055 = 7651583) B7651583
theorem B2873171 : Blo 670310 2873171 := bstep (se 1 (by rfl) ⟨2154878, by rfl⟩ : syracuseStep 2873171 = 4309757) B4309757
theorem B1136551 : Blo 670310 1136551 := bstep (se 1 (by rfl) ⟨852413, by rfl⟩ : syracuseStep 1136551 = 1704827) B1704827
theorem B1005599 : Blo 670310 1005599 := bstep (se 1 (by rfl) ⟨754199, by rfl⟩ : syracuseStep 1005599 = 1508399) B1508399
theorem B1006247 : Blo 670310 1006247 := bstep (se 1 (by rfl) ⟨754685, by rfl⟩ : syracuseStep 1006247 = 1509371) B1509371
theorem B1006559 : Blo 670310 1006559 := bstep (se 1 (by rfl) ⟨754919, by rfl⟩ : syracuseStep 1006559 = 1509839) B1509839
theorem B3891199 : Blo 670310 3891199 := bstep (se 1 (by rfl) ⟨2918399, by rfl⟩ : syracuseStep 3891199 = 5836799) B5836799
theorem B1007663 : Blo 670310 1007663 := bstep (se 1 (by rfl) ⟨755747, by rfl⟩ : syracuseStep 1007663 = 1511495) B1511495
theorem B1007753 : Blo 670310 1007753 := bstep (se 2 (by rfl) ⟨377907, by rfl⟩ : syracuseStep 1007753 = 755815) B755815
theorem B1008041 : Blo 670310 1008041 := bstep (se 2 (by rfl) ⟨378015, by rfl⟩ : syracuseStep 1008041 = 756031) B756031
theorem B2548705 : Blo 670310 2548705 := bstep (se 2 (by rfl) ⟨955764, by rfl⟩ : syracuseStep 2548705 = 1911529) B1911529
theorem B1008671 : Blo 670310 1008671 := bstep (se 1 (by rfl) ⟨756503, by rfl⟩ : syracuseStep 1008671 = 1513007) B1513007
theorem B1008767 : Blo 670310 1008767 := bstep (se 1 (by rfl) ⟨756575, by rfl⟩ : syracuseStep 1008767 = 1513151) B1513151
theorem B1074313 : Blo 670310 1074313 := bstep (se 2 (by rfl) ⟨402867, by rfl⟩ : syracuseStep 1074313 = 805735) B805735
theorem B1008809 : Blo 670310 1008809 := bstep (se 2 (by rfl) ⟨378303, by rfl⟩ : syracuseStep 1008809 = 756607) B756607
theorem B3237239 : Blo 670310 3237239 := bstep (se 1 (by rfl) ⟨2427929, by rfl⟩ : syracuseStep 3237239 = 4855859) B4855859
theorem B1009151 : Blo 670310 1009151 := bstep (se 1 (by rfl) ⟨756863, by rfl⟩ : syracuseStep 1009151 = 1513727) B1513727
theorem B3073727 : Blo 670310 3073727 := bstep (se 1 (by rfl) ⟨2305295, by rfl⟩ : syracuseStep 3073727 = 4610591) B4610591
theorem B3401513 : Blo 670310 3401513 := bstep (se 2 (by rfl) ⟨1275567, by rfl⟩ : syracuseStep 3401513 = 2551135) B2551135
theorem B1009499 : Blo 670310 1009499 := bstep (se 1 (by rfl) ⟨757124, by rfl⟩ : syracuseStep 1009499 = 1514249) B1514249
theorem B1009727 : Blo 670310 1009727 := bstep (se 1 (by rfl) ⟨757295, by rfl⟩ : syracuseStep 1009727 = 1514591) B1514591
theorem B7268563 : Blo 670310 7268563 := bstep (se 1 (by rfl) ⟨5451422, by rfl⟩ : syracuseStep 7268563 = 10902845) B10902845
theorem B1009883 : Blo 670310 1009883 := bstep (se 1 (by rfl) ⟨757412, by rfl⟩ : syracuseStep 1009883 = 1514825) B1514825
theorem B1009895 : Blo 670310 1009895 := bstep (se 1 (by rfl) ⟨757421, by rfl⟩ : syracuseStep 1009895 = 1514843) B1514843
theorem B1010459 : Blo 670310 1010459 := bstep (se 1 (by rfl) ⟨757844, by rfl⟩ : syracuseStep 1010459 = 1515689) B1515689
theorem B1010543 : Blo 670310 1010543 := bstep (se 1 (by rfl) ⟨757907, by rfl⟩ : syracuseStep 1010543 = 1515815) B1515815
theorem B1010687 : Blo 670310 1010687 := bstep (se 1 (by rfl) ⟨758015, by rfl⟩ : syracuseStep 1010687 = 1516031) B1516031
theorem B1273897 : Blo 670310 1273897 := bstep (se 2 (by rfl) ⟨477711, by rfl⟩ : syracuseStep 1273897 = 955423) B955423
theorem B1700747 : Blo 670310 1700747 := bstep (se 1 (by rfl) ⟨1275560, by rfl⟩ : syracuseStep 1700747 = 2551121) B2551121
theorem B848875 : Blo 670310 848875 := bstep (se 1 (by rfl) ⟨636656, by rfl⟩ : syracuseStep 848875 = 1273313) B1273313
theorem B849199 : Blo 670310 849199 := bstep (se 1 (by rfl) ⟨636899, by rfl⟩ : syracuseStep 849199 = 1273799) B1273799
theorem B18413345 : Blo 670310 18413345 := bstep (se 2 (by rfl) ⟨6905004, by rfl⟩ : syracuseStep 18413345 = 13810009) B13810009
theorem B13761647 : Blo 670310 13761647 := bstep (se 1 (by rfl) ⟨10321235, by rfl⟩ : syracuseStep 13761647 = 20642471) B20642471
theorem B1704503 : Blo 670310 1704503 := bstep (se 1 (by rfl) ⟨1278377, by rfl⟩ : syracuseStep 1704503 = 2556755) B2556755
theorem B2556967 : Blo 670310 2556967 := bstep (se 1 (by rfl) ⟨1917725, by rfl⟩ : syracuseStep 2556967 = 3835451) B3835451
theorem B2557439 : Blo 670310 2557439 := bstep (se 1 (by rfl) ⟨1918079, by rfl⟩ : syracuseStep 2557439 = 3836159) B3836159
theorem B1705961 : Blo 670310 1705961 := bstep (se 2 (by rfl) ⟨639735, by rfl⟩ : syracuseStep 1705961 = 1279471) B1279471
theorem B1509479 : Blo 670310 1509479 := bstep (se 1 (by rfl) ⟨1132109, by rfl⟩ : syracuseStep 1509479 = 2264219) B2264219
theorem B1476863 : Blo 670310 1476863 := bstep (se 1 (by rfl) ⟨1107647, by rfl⟩ : syracuseStep 1476863 = 2215295) B2215295
theorem B2722535 : Blo 670310 2722535 := bstep (se 1 (by rfl) ⟨2041901, by rfl⟩ : syracuseStep 2722535 = 4083803) B4083803
theorem B7670537 : Blo 670310 7670537 := bstep (se 2 (by rfl) ⟨2876451, by rfl⟩ : syracuseStep 7670537 = 5752903) B5752903
theorem B8589989 : Blo 670310 8589989 := bstep (se 4 (by rfl) ⟨805311, by rfl⟩ : syracuseStep 8589989 = 1610623) B1610623
theorem B19338547 : Blo 670310 19338547 := bstep (se 1 (by rfl) ⟨14503910, by rfl⟩ : syracuseStep 19338547 = 29007821) B29007821
theorem B1381715 : Blo 670310 1381715 := bstep (se 1 (by rfl) ⟨1036286, by rfl⟩ : syracuseStep 1381715 = 2072573) B2072573
theorem B2267675 : Blo 670310 2267675 := bstep (se 1 (by rfl) ⟨1700756, by rfl⟩ : syracuseStep 2267675 = 3401513) B3401513
theorem B1514807 : Blo 670310 1514807 := bstep (se 1 (by rfl) ⟨1136105, by rfl⟩ : syracuseStep 1514807 = 2272211) B2272211
theorem B1515401 : Blo 670310 1515401 := bstep (se 2 (by rfl) ⟨568275, by rfl⟩ : syracuseStep 1515401 = 1136551) B1136551
theorem B1517111 : Blo 670310 1517111 := bstep (se 1 (by rfl) ⟨1137833, by rfl⟩ : syracuseStep 1517111 = 2275667) B2275667
theorem B5188265 : Blo 670310 5188265 := bstep (se 2 (by rfl) ⟨1945599, by rfl⟩ : syracuseStep 5188265 = 3891199) B3891199
theorem B2271995 : Blo 670310 2271995 := bstep (se 1 (by rfl) ⟨1703996, by rfl⟩ : syracuseStep 2271995 = 3407993) B3407993
theorem B1616851 : Blo 670310 1616851 := bstep (se 1 (by rfl) ⟨1212638, by rfl⟩ : syracuseStep 1616851 = 2425277) B2425277
theorem B2043239 : Blo 670310 2043239 := bstep (se 1 (by rfl) ⟨1532429, by rfl⟩ : syracuseStep 2043239 = 3064859) B3064859
theorem B3224015 : Blo 670310 3224015 := bstep (se 1 (by rfl) ⟨2418011, by rfl⟩ : syracuseStep 3224015 = 4836023) B4836023
theorem B17478389 : Blo 670310 17478389 := bstep (se 5 (by rfl) ⟨819299, by rfl⟩ : syracuseStep 17478389 = 1638599) B1638599
theorem B670399 : Blo 670310 670399 := bstep (se 1 (by rfl) ⟨502799, by rfl⟩ : syracuseStep 670399 = 1005599) B1005599
theorem B670831 : Blo 670310 670831 := bstep (se 1 (by rfl) ⟨503123, by rfl⟩ : syracuseStep 670831 = 1006247) B1006247
theorem B671039 : Blo 670310 671039 := bstep (se 1 (by rfl) ⟨503279, by rfl⟩ : syracuseStep 671039 = 1006559) B1006559
theorem B671775 : Blo 670310 671775 := bstep (se 1 (by rfl) ⟨503831, by rfl⟩ : syracuseStep 671775 = 1007663) B1007663
theorem B671835 : Blo 670310 671835 := bstep (se 1 (by rfl) ⟨503876, by rfl⟩ : syracuseStep 671835 = 1007753) B1007753
theorem B672027 : Blo 670310 672027 := bstep (se 1 (by rfl) ⟨504020, by rfl⟩ : syracuseStep 672027 = 1008041) B1008041
theorem B672447 : Blo 670310 672447 := bstep (se 1 (by rfl) ⟨504335, by rfl⟩ : syracuseStep 672447 = 1008671) B1008671
theorem B672511 : Blo 670310 672511 := bstep (se 1 (by rfl) ⟨504383, by rfl⟩ : syracuseStep 672511 = 1008767) B1008767
theorem B672539 : Blo 670310 672539 := bstep (se 1 (by rfl) ⟨504404, by rfl⟩ : syracuseStep 672539 = 1008809) B1008809
theorem B672767 : Blo 670310 672767 := bstep (se 1 (by rfl) ⟨504575, by rfl⟩ : syracuseStep 672767 = 1009151) B1009151
theorem B2049151 : Blo 670310 2049151 := bstep (se 1 (by rfl) ⟨1536863, by rfl⟩ : syracuseStep 2049151 = 3073727) B3073727
theorem B672999 : Blo 670310 672999 := bstep (se 1 (by rfl) ⟨504749, by rfl⟩ : syracuseStep 672999 = 1009499) B1009499
theorem B1131833 : Blo 670310 1131833 := bstep (se 2 (by rfl) ⟨424437, by rfl⟩ : syracuseStep 1131833 = 848875) B848875
theorem B673151 : Blo 670310 673151 := bstep (se 1 (by rfl) ⟨504863, by rfl⟩ : syracuseStep 673151 = 1009727) B1009727
theorem B673255 : Blo 670310 673255 := bstep (se 1 (by rfl) ⟨504941, by rfl⟩ : syracuseStep 673255 = 1009883) B1009883
theorem B673263 : Blo 670310 673263 := bstep (se 1 (by rfl) ⟨504947, by rfl⟩ : syracuseStep 673263 = 1009895) B1009895
theorem B1132265 : Blo 670310 1132265 := bstep (se 2 (by rfl) ⟨424599, by rfl⟩ : syracuseStep 1132265 = 849199) B849199
theorem B673639 : Blo 670310 673639 := bstep (se 1 (by rfl) ⟨505229, by rfl⟩ : syracuseStep 673639 = 1010459) B1010459
theorem B673695 : Blo 670310 673695 := bstep (se 1 (by rfl) ⟨505271, by rfl⟩ : syracuseStep 673695 = 1010543) B1010543
theorem B673791 : Blo 670310 673791 := bstep (se 1 (by rfl) ⟨505343, by rfl⟩ : syracuseStep 673791 = 1010687) B1010687
theorem B1133831 : Blo 670310 1133831 := bstep (se 1 (by rfl) ⟨850373, by rfl⟩ : syracuseStep 1133831 = 1700747) B1700747
theorem B12275563 : Blo 670310 12275563 := bstep (se 1 (by rfl) ⟨9206672, by rfl⟩ : syracuseStep 12275563 = 18413345) B18413345
theorem B3398273 : Blo 670310 3398273 := bstep (se 2 (by rfl) ⟨1274352, by rfl⟩ : syracuseStep 3398273 = 2548705) B2548705
theorem B1432417 : Blo 670310 1432417 := bstep (se 2 (by rfl) ⟨537156, by rfl⟩ : syracuseStep 1432417 = 1074313) B1074313
theorem B3398759 : Blo 670310 3398759 := bstep (se 1 (by rfl) ⟨2549069, by rfl⟩ : syracuseStep 3398759 = 5098139) B5098139
theorem B17489195 : Blo 670310 17489195 := bstep (se 1 (by rfl) ⟨13116896, by rfl⟩ : syracuseStep 17489195 = 26233793) B26233793
theorem B1007609 : Blo 670310 1007609 := bstep (se 2 (by rfl) ⟨377853, by rfl⟩ : syracuseStep 1007609 = 755707) B755707
theorem B9691417 : Blo 670310 9691417 := bstep (se 2 (by rfl) ⟨3634281, by rfl⟩ : syracuseStep 9691417 = 7268563) B7268563
theorem B1073711 : Blo 670310 1073711 := bstep (se 1 (by rfl) ⟨805283, by rfl⟩ : syracuseStep 1073711 = 1610567) B1610567
theorem B3400703 : Blo 670310 3400703 := bstep (se 1 (by rfl) ⟨2550527, by rfl⟩ : syracuseStep 3400703 = 5101055) B5101055
theorem B7661789 : Blo 670310 7661789 := bstep (se 3 (by rfl) ⟨1436585, by rfl⟩ : syracuseStep 7661789 = 2873171) B2873171
theorem B1698529 : Blo 670310 1698529 := bstep (se 2 (by rfl) ⟨636948, by rfl⟩ : syracuseStep 1698529 = 1273897) B1273897
theorem B1010411 : Blo 670310 1010411 := bstep (se 1 (by rfl) ⟨757808, by rfl⟩ : syracuseStep 1010411 = 1515617) B1515617
theorem B7367561 : Blo 670310 7367561 := bstep (se 2 (by rfl) ⟨2762835, by rfl⟩ : syracuseStep 7367561 = 5525671) B5525671
theorem B1010855 : Blo 670310 1010855 := bstep (se 1 (by rfl) ⟨758141, by rfl⟩ : syracuseStep 1010855 = 1516283) B1516283
theorem B1011065 : Blo 670310 1011065 := bstep (se 2 (by rfl) ⟨379149, by rfl⟩ : syracuseStep 1011065 = 758299) B758299
theorem B2158159 : Blo 670310 2158159 := bstep (se 1 (by rfl) ⟨1618619, by rfl⟩ : syracuseStep 2158159 = 3237239) B3237239
theorem B6451103 : Blo 670310 6451103 := bstep (se 1 (by rfl) ⟨4838327, by rfl⟩ : syracuseStep 6451103 = 9676655) B9676655
theorem B15562945 : Blo 670310 15562945 := bstep (se 2 (by rfl) ⟨5836104, by rfl⟩ : syracuseStep 15562945 = 11672209) B11672209
theorem B29162825 : Blo 670310 29162825 := bstep (se 2 (by rfl) ⟨10936059, by rfl⟩ : syracuseStep 29162825 = 21872119) B21872119
theorem B9174431 : Blo 670310 9174431 := bstep (se 1 (by rfl) ⟨6880823, by rfl⟩ : syracuseStep 9174431 = 13761647) B13761647
theorem B2719615 : Blo 670310 2719615 := bstep (se 1 (by rfl) ⟨2039711, by rfl⟩ : syracuseStep 2719615 = 4079423) B4079423
theorem B754555 : Blo 670310 754555 := bstep (se 1 (by rfl) ⟨565916, by rfl⟩ : syracuseStep 754555 = 1131833) B1131833
theorem B1704959 : Blo 670310 1704959 := bstep (se 1 (by rfl) ⟨1278719, by rfl⟩ : syracuseStep 1704959 = 2557439) B2557439
theorem B754843 : Blo 670310 754843 := bstep (se 1 (by rfl) ⟨566132, by rfl⟩ : syracuseStep 754843 = 1132265) B1132265
theorem B3409289 : Blo 670310 3409289 := bstep (se 2 (by rfl) ⟨1278483, by rfl⟩ : syracuseStep 3409289 = 2556967) B2556967
theorem B984575 : Blo 670310 984575 := bstep (se 1 (by rfl) ⟨738431, by rfl⟩ : syracuseStep 984575 = 1476863) B1476863
theorem B5113691 : Blo 670310 5113691 := bstep (se 1 (by rfl) ⟨3835268, by rfl⟩ : syracuseStep 5113691 = 7670537) B7670537
theorem B755887 : Blo 670310 755887 := bstep (se 1 (by rfl) ⟨566915, by rfl⟩ : syracuseStep 755887 = 1133831) B1133831
theorem B921143 : Blo 670310 921143 := bstep (se 1 (by rfl) ⟨690857, by rfl⟩ : syracuseStep 921143 = 1381715) B1381715
theorem B2264705 : Blo 670310 2264705 := bstep (se 2 (by rfl) ⟨849264, by rfl⟩ : syracuseStep 2264705 = 1698529) B1698529
theorem B1511783 : Blo 670310 1511783 := bstep (se 1 (by rfl) ⟨1133837, by rfl⟩ : syracuseStep 1511783 = 2267675) B2267675
theorem B2265515 : Blo 670310 2265515 := bstep (se 1 (by rfl) ⟨1699136, by rfl⟩ : syracuseStep 2265515 = 3398273) B3398273
theorem B2265839 : Blo 670310 2265839 := bstep (se 1 (by rfl) ⟨1699379, by rfl⟩ : syracuseStep 2265839 = 3398759) B3398759
theorem B8623205 : Blo 670310 8623205 := bstep (se 4 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 8623205 = 1616851) B1616851
theorem B2267135 : Blo 670310 2267135 := bstep (se 1 (by rfl) ⟨1700351, by rfl⟩ : syracuseStep 2267135 = 3400703) B3400703
theorem B1514663 : Blo 670310 1514663 := bstep (se 1 (by rfl) ⟨1135997, by rfl⟩ : syracuseStep 1514663 = 2271995) B2271995
theorem B20750593 : Blo 670310 20750593 := bstep (se 2 (by rfl) ⟨7781472, by rfl⟩ : syracuseStep 20750593 = 15562945) B15562945
theorem B5448637 : Blo 670310 5448637 := bstep (se 3 (by rfl) ⟨1021619, by rfl⟩ : syracuseStep 5448637 = 2043239) B2043239
theorem B1909889 : Blo 670310 1909889 := bstep (se 2 (by rfl) ⟨716208, by rfl⟩ : syracuseStep 1909889 = 1432417) B1432417
theorem B19441883 : Blo 670310 19441883 := bstep (se 1 (by rfl) ⟨14581412, by rfl⟩ : syracuseStep 19441883 = 29162825) B29162825
theorem B12921889 : Blo 670310 12921889 := bstep (se 2 (by rfl) ⟨4845708, by rfl⟩ : syracuseStep 12921889 = 9691417) B9691417
theorem B2732201 : Blo 670310 2732201 := bstep (se 2 (by rfl) ⟨1024575, by rfl⟩ : syracuseStep 2732201 = 2049151) B2049151
theorem B1815023 : Blo 670310 1815023 := bstep (se 1 (by rfl) ⟨1361267, by rfl⟩ : syracuseStep 1815023 = 2722535) B2722535
theorem B46609037 : Blo 670310 46609037 := bstep (se 3 (by rfl) ⟨8739194, by rfl⟩ : syracuseStep 46609037 = 17478389) B17478389
theorem B16367417 : Blo 670310 16367417 := bstep (se 2 (by rfl) ⟨6137781, by rfl⟩ : syracuseStep 16367417 = 12275563) B12275563
theorem B671739 : Blo 670310 671739 := bstep (se 1 (by rfl) ⟨503804, by rfl⟩ : syracuseStep 671739 = 1007609) B1007609
theorem B3458843 : Blo 670310 3458843 := bstep (se 1 (by rfl) ⟨2594132, by rfl⟩ : syracuseStep 3458843 = 5188265) B5188265
theorem B673607 : Blo 670310 673607 := bstep (se 1 (by rfl) ⟨505205, by rfl⟩ : syracuseStep 673607 = 1010411) B1010411
theorem B673903 : Blo 670310 673903 := bstep (se 1 (by rfl) ⟨505427, by rfl⟩ : syracuseStep 673903 = 1010855) B1010855
theorem B674043 : Blo 670310 674043 := bstep (se 1 (by rfl) ⟨505532, by rfl⟩ : syracuseStep 674043 = 1011065) B1011065
theorem B2149343 : Blo 670310 2149343 := bstep (se 1 (by rfl) ⟨1612007, by rfl⟩ : syracuseStep 2149343 = 3224015) B3224015
theorem B24465149 : Blo 670310 24465149 := bstep (se 3 (by rfl) ⟨4587215, by rfl⟩ : syracuseStep 24465149 = 9174431) B9174431
theorem B3626153 : Blo 670310 3626153 := bstep (se 2 (by rfl) ⟨1359807, by rfl⟩ : syracuseStep 3626153 = 2719615) B2719615
theorem B1136335 : Blo 670310 1136335 := bstep (se 1 (by rfl) ⟨852251, by rfl⟩ : syracuseStep 1136335 = 1704503) B1704503
theorem B1137307 : Blo 670310 1137307 := bstep (se 1 (by rfl) ⟨852980, by rfl⟩ : syracuseStep 1137307 = 1705961) B1705961
theorem B1006319 : Blo 670310 1006319 := bstep (se 1 (by rfl) ⟨754739, by rfl⟩ : syracuseStep 1006319 = 1509479) B1509479
theorem B5726659 : Blo 670310 5726659 := bstep (se 1 (by rfl) ⟨4294994, by rfl⟩ : syracuseStep 5726659 = 8589989) B8589989
theorem B2877545 : Blo 670310 2877545 := bstep (se 2 (by rfl) ⟨1079079, by rfl⟩ : syracuseStep 2877545 = 2158159) B2158159
theorem B11659463 : Blo 670310 11659463 := bstep (se 1 (by rfl) ⟨8744597, by rfl⟩ : syracuseStep 11659463 = 17489195) B17489195
theorem B1009871 : Blo 670310 1009871 := bstep (se 1 (by rfl) ⟨757403, by rfl⟩ : syracuseStep 1009871 = 1514807) B1514807
theorem B1010267 : Blo 670310 1010267 := bstep (se 1 (by rfl) ⟨757700, by rfl⟩ : syracuseStep 1010267 = 1515401) B1515401
theorem B715807 : Blo 670310 715807 := bstep (se 1 (by rfl) ⟨536855, by rfl⟩ : syracuseStep 715807 = 1073711) B1073711
theorem B1011407 : Blo 670310 1011407 := bstep (se 1 (by rfl) ⟨758555, by rfl⟩ : syracuseStep 1011407 = 1517111) B1517111
theorem B5107859 : Blo 670310 5107859 := bstep (se 1 (by rfl) ⟨3830894, by rfl⟩ : syracuseStep 5107859 = 7661789) B7661789
theorem B25784729 : Blo 670310 25784729 := bstep (se 2 (by rfl) ⟨9669273, by rfl⟩ : syracuseStep 25784729 = 19338547) B19338547
theorem B4911707 : Blo 670310 4911707 := bstep (se 1 (by rfl) ⟨3683780, by rfl⟩ : syracuseStep 4911707 = 7367561) B7367561
theorem B17202941 : Blo 670310 17202941 := bstep (se 3 (by rfl) ⟨3225551, by rfl⟩ : syracuseStep 17202941 = 6451103) B6451103
theorem B7635545 : Blo 670310 7635545 := bstep (se 2 (by rfl) ⟨2863329, by rfl⟩ : syracuseStep 7635545 = 5726659) B5726659
theorem B3409127 : Blo 670310 3409127 := bstep (se 1 (by rfl) ⟨2556845, by rfl⟩ : syracuseStep 3409127 = 5113691) B5113691
theorem B1509803 : Blo 670310 1509803 := bstep (se 1 (by rfl) ⟨1132352, by rfl⟩ : syracuseStep 1509803 = 2264705) B2264705
theorem B1510343 : Blo 670310 1510343 := bstep (se 1 (by rfl) ⟨1132757, by rfl⟩ : syracuseStep 1510343 = 2265515) B2265515
theorem B1510559 : Blo 670310 1510559 := bstep (se 1 (by rfl) ⟨1132919, by rfl⟩ : syracuseStep 1510559 = 2265839) B2265839
theorem B2625533 : Blo 670310 2625533 := bstep (se 3 (by rfl) ⟨492287, by rfl⟩ : syracuseStep 2625533 = 984575) B984575
theorem B1511423 : Blo 670310 1511423 := bstep (se 1 (by rfl) ⟨1133567, by rfl⟩ : syracuseStep 1511423 = 2267135) B2267135
theorem B7673453 : Blo 670310 7673453 := bstep (se 3 (by rfl) ⟨1438772, by rfl⟩ : syracuseStep 7673453 = 2877545) B2877545
theorem B7772975 : Blo 670310 7772975 := bstep (se 1 (by rfl) ⟨5829731, by rfl⟩ : syracuseStep 7772975 = 11659463) B11659463
theorem B1515113 : Blo 670310 1515113 := bstep (se 2 (by rfl) ⟨568167, by rfl⟩ : syracuseStep 1515113 = 1136335) B1136335
theorem B31072691 : Blo 670310 31072691 := bstep (se 1 (by rfl) ⟨23304518, by rfl⟩ : syracuseStep 31072691 = 46609037) B46609037
theorem B1516409 : Blo 670310 1516409 := bstep (se 2 (by rfl) ⟨568653, by rfl⟩ : syracuseStep 1516409 = 1137307) B1137307
theorem B27667457 : Blo 670310 27667457 := bstep (se 2 (by rfl) ⟨10375296, by rfl⟩ : syracuseStep 27667457 = 20750593) B20750593
theorem B2272859 : Blo 670310 2272859 := bstep (se 1 (by rfl) ⟨1704644, by rfl⟩ : syracuseStep 2272859 = 3409289) B3409289
theorem B5748803 : Blo 670310 5748803 := bstep (se 1 (by rfl) ⟨4311602, by rfl⟩ : syracuseStep 5748803 = 8623205) B8623205
theorem B670879 : Blo 670310 670879 := bstep (se 1 (by rfl) ⟨503159, by rfl⟩ : syracuseStep 670879 = 1006319) B1006319
theorem B3817637 : Blo 670310 3817637 := bstep (se 4 (by rfl) ⟨357903, by rfl⟩ : syracuseStep 3817637 = 715807) B715807
theorem B673247 : Blo 670310 673247 := bstep (se 1 (by rfl) ⟨504935, by rfl⟩ : syracuseStep 673247 = 1009871) B1009871
theorem B12961255 : Blo 670310 12961255 := bstep (se 1 (by rfl) ⟨9720941, by rfl⟩ : syracuseStep 12961255 = 19441883) B19441883
theorem B673511 : Blo 670310 673511 := bstep (se 1 (by rfl) ⟨505133, by rfl⟩ : syracuseStep 673511 = 1010267) B1010267
theorem B674271 : Blo 670310 674271 := bstep (se 1 (by rfl) ⟨505703, by rfl⟩ : syracuseStep 674271 = 1011407) B1011407
theorem B1821467 : Blo 670310 1821467 := bstep (se 1 (by rfl) ⟨1366100, by rfl⟩ : syracuseStep 1821467 = 2732201) B2732201
theorem B17189819 : Blo 670310 17189819 := bstep (se 1 (by rfl) ⟨12892364, by rfl⟩ : syracuseStep 17189819 = 25784729) B25784729
theorem B1136639 : Blo 670310 1136639 := bstep (se 1 (by rfl) ⟨852479, by rfl⟩ : syracuseStep 1136639 = 1704959) B1704959
theorem B1006073 : Blo 670310 1006073 := bstep (se 2 (by rfl) ⟨377277, by rfl⟩ : syracuseStep 1006073 = 754555) B754555
theorem B7264849 : Blo 670310 7264849 := bstep (se 2 (by rfl) ⟨2724318, by rfl⟩ : syracuseStep 7264849 = 5448637) B5448637
theorem B1006457 : Blo 670310 1006457 := bstep (se 2 (by rfl) ⟨377421, by rfl⟩ : syracuseStep 1006457 = 754843) B754843
theorem B1432895 : Blo 670310 1432895 := bstep (se 1 (by rfl) ⟨1074671, by rfl⟩ : syracuseStep 1432895 = 2149343) B2149343
theorem B16310099 : Blo 670310 16310099 := bstep (se 1 (by rfl) ⟨12232574, by rfl⟩ : syracuseStep 16310099 = 24465149) B24465149
theorem B1007849 : Blo 670310 1007849 := bstep (se 2 (by rfl) ⟨377943, by rfl⟩ : syracuseStep 1007849 = 755887) B755887
theorem B1007855 : Blo 670310 1007855 := bstep (se 1 (by rfl) ⟨755891, by rfl⟩ : syracuseStep 1007855 = 1511783) B1511783
theorem B2417435 : Blo 670310 2417435 := bstep (se 1 (by rfl) ⟨1813076, by rfl⟩ : syracuseStep 2417435 = 3626153) B3626153
theorem B17229185 : Blo 670310 17229185 := bstep (se 2 (by rfl) ⟨6460944, by rfl⟩ : syracuseStep 17229185 = 12921889) B12921889
theorem B1009775 : Blo 670310 1009775 := bstep (se 1 (by rfl) ⟨757331, by rfl⟩ : syracuseStep 1009775 = 1514663) B1514663
theorem B1273259 : Blo 670310 1273259 := bstep (se 1 (by rfl) ⟨954944, by rfl⟩ : syracuseStep 1273259 = 1909889) B1909889
theorem B3405239 : Blo 670310 3405239 := bstep (se 1 (by rfl) ⟨2553929, by rfl⟩ : syracuseStep 3405239 = 5107859) B5107859
theorem B36894325 : Blo 670310 36894325 := bstep (se 5 (by rfl) ⟨1729421, by rfl⟩ : syracuseStep 36894325 = 3458843) B3458843
theorem B1210015 : Blo 670310 1210015 := bstep (se 1 (by rfl) ⟨907511, by rfl⟩ : syracuseStep 1210015 = 1815023) B1815023
theorem B3274471 : Blo 670310 3274471 := bstep (se 1 (by rfl) ⟨2455853, by rfl⟩ : syracuseStep 3274471 = 4911707) B4911707
theorem B2456381 : Blo 670310 2456381 := bstep (se 3 (by rfl) ⟨460571, by rfl⟩ : syracuseStep 2456381 = 921143) B921143
theorem B11468627 : Blo 670310 11468627 := bstep (se 1 (by rfl) ⟨8601470, by rfl⟩ : syracuseStep 11468627 = 17202941) B17202941
theorem B10911611 : Blo 670310 10911611 := bstep (se 1 (by rfl) ⟨8183708, by rfl⟩ : syracuseStep 10911611 = 16367417) B16367417
theorem B5115635 : Blo 670310 5115635 := bstep (se 1 (by rfl) ⟨3836726, by rfl⟩ : syracuseStep 5115635 = 7673453) B7673453
theorem B757759 : Blo 670310 757759 := bstep (se 1 (by rfl) ⟨568319, by rfl⟩ : syracuseStep 757759 = 1136639) B1136639
theorem B5181983 : Blo 670310 5181983 := bstep (se 1 (by rfl) ⟨3886487, by rfl⟩ : syracuseStep 5181983 = 7772975) B7772975
theorem B1611623 : Blo 670310 1611623 := bstep (se 1 (by rfl) ⟨1208717, by rfl⟩ : syracuseStep 1611623 = 2417435) B2417435
theorem B4857245 : Blo 670310 4857245 := bstep (se 3 (by rfl) ⟨910733, by rfl⟩ : syracuseStep 4857245 = 1821467) B1821467
theorem B49192433 : Blo 670310 49192433 := bstep (se 2 (by rfl) ⟨18447162, by rfl⟩ : syracuseStep 49192433 = 36894325) B36894325
theorem B1613353 : Blo 670310 1613353 := bstep (se 2 (by rfl) ⟨605007, by rfl⟩ : syracuseStep 1613353 = 1210015) B1210015
theorem B1515239 : Blo 670310 1515239 := bstep (se 1 (by rfl) ⟨1136429, by rfl⟩ : syracuseStep 1515239 = 2272859) B2272859
theorem B2270159 : Blo 670310 2270159 := bstep (se 1 (by rfl) ⟨1702619, by rfl⟩ : syracuseStep 2270159 = 3405239) B3405239
theorem B7645751 : Blo 670310 7645751 := bstep (se 1 (by rfl) ⟨5734313, by rfl⟩ : syracuseStep 7645751 = 11468627) B11468627
theorem B5090363 : Blo 670310 5090363 := bstep (se 1 (by rfl) ⟨3817772, by rfl⟩ : syracuseStep 5090363 = 7635545) B7635545
theorem B2272751 : Blo 670310 2272751 := bstep (se 1 (by rfl) ⟨1704563, by rfl⟩ : syracuseStep 2272751 = 3409127) B3409127
theorem B17281673 : Blo 670310 17281673 := bstep (se 2 (by rfl) ⟨6480627, by rfl⟩ : syracuseStep 17281673 = 12961255) B12961255
theorem B1750355 : Blo 670310 1750355 := bstep (se 1 (by rfl) ⟨1312766, by rfl⟩ : syracuseStep 1750355 = 2625533) B2625533
theorem B670715 : Blo 670310 670715 := bstep (se 1 (by rfl) ⟨503036, by rfl⟩ : syracuseStep 670715 = 1006073) B1006073
theorem B670971 : Blo 670310 670971 := bstep (se 1 (by rfl) ⟨503228, by rfl⟩ : syracuseStep 670971 = 1006457) B1006457
theorem B671899 : Blo 670310 671899 := bstep (se 1 (by rfl) ⟨503924, by rfl⟩ : syracuseStep 671899 = 1007849) B1007849
theorem B671903 : Blo 670310 671903 := bstep (se 1 (by rfl) ⟨503927, by rfl⟩ : syracuseStep 671903 = 1007855) B1007855
theorem B11486123 : Blo 670310 11486123 := bstep (se 1 (by rfl) ⟨8614592, by rfl⟩ : syracuseStep 11486123 = 17229185) B17229185
theorem B673183 : Blo 670310 673183 := bstep (se 1 (by rfl) ⟨504887, by rfl⟩ : syracuseStep 673183 = 1009775) B1009775
theorem B9686465 : Blo 670310 9686465 := bstep (se 2 (by rfl) ⟨3632424, by rfl⟩ : syracuseStep 9686465 = 7264849) B7264849
theorem B3821053 : Blo 670310 3821053 := bstep (se 3 (by rfl) ⟨716447, by rfl⟩ : syracuseStep 3821053 = 1432895) B1432895
theorem B3395357 : Blo 670310 3395357 := bstep (se 3 (by rfl) ⟨636629, by rfl⟩ : syracuseStep 3395357 = 1273259) B1273259
theorem B2545091 : Blo 670310 2545091 := bstep (se 1 (by rfl) ⟨1908818, by rfl⟩ : syracuseStep 2545091 = 3817637) B3817637
theorem B82860509 : Blo 670310 82860509 := bstep (se 3 (by rfl) ⟨15536345, by rfl⟩ : syracuseStep 82860509 = 31072691) B31072691
theorem B1006535 : Blo 670310 1006535 := bstep (se 1 (by rfl) ⟨754901, by rfl⟩ : syracuseStep 1006535 = 1509803) B1509803
theorem B11459879 : Blo 670310 11459879 := bstep (se 1 (by rfl) ⟨8594909, by rfl⟩ : syracuseStep 11459879 = 17189819) B17189819
theorem B1006895 : Blo 670310 1006895 := bstep (se 1 (by rfl) ⟨755171, by rfl⟩ : syracuseStep 1006895 = 1510343) B1510343
theorem B1007039 : Blo 670310 1007039 := bstep (se 1 (by rfl) ⟨755279, by rfl⟩ : syracuseStep 1007039 = 1510559) B1510559
theorem B1007615 : Blo 670310 1007615 := bstep (se 1 (by rfl) ⟨755711, by rfl⟩ : syracuseStep 1007615 = 1511423) B1511423
theorem B1010075 : Blo 670310 1010075 := bstep (se 1 (by rfl) ⟨757556, by rfl⟩ : syracuseStep 1010075 = 1515113) B1515113
theorem B10873399 : Blo 670310 10873399 := bstep (se 1 (by rfl) ⟨8155049, by rfl⟩ : syracuseStep 10873399 = 16310099) B16310099
theorem B1010939 : Blo 670310 1010939 := bstep (se 1 (by rfl) ⟨758204, by rfl⟩ : syracuseStep 1010939 = 1516409) B1516409
theorem B18444971 : Blo 670310 18444971 := bstep (se 1 (by rfl) ⟨13833728, by rfl⟩ : syracuseStep 18444971 = 27667457) B27667457
theorem B17463845 : Blo 670310 17463845 := bstep (se 4 (by rfl) ⟨1637235, by rfl⟩ : syracuseStep 17463845 = 3274471) B3274471
theorem B3832535 : Blo 670310 3832535 := bstep (se 1 (by rfl) ⟨2874401, by rfl⟩ : syracuseStep 3832535 = 5748803) B5748803
theorem B1637587 : Blo 670310 1637587 := bstep (se 1 (by rfl) ⟨1228190, by rfl⟩ : syracuseStep 1637587 = 2456381) B2456381
theorem B7274407 : Blo 670310 7274407 := bstep (se 1 (by rfl) ⟨5455805, by rfl⟩ : syracuseStep 7274407 = 10911611) B10911611
theorem B6457643 : Blo 670310 6457643 := bstep (se 1 (by rfl) ⟨4843232, by rfl⟩ : syracuseStep 6457643 = 9686465) B9686465
theorem B3410423 : Blo 670310 3410423 := bstep (se 1 (by rfl) ⟨2557817, by rfl⟩ : syracuseStep 3410423 = 5115635) B5115635
theorem B2263571 : Blo 670310 2263571 := bstep (se 1 (by rfl) ⟨1697678, by rfl⟩ : syracuseStep 2263571 = 3395357) B3395357
theorem B7639919 : Blo 670310 7639919 := bstep (se 1 (by rfl) ⟨5729939, by rfl⟩ : syracuseStep 7639919 = 11459879) B11459879
theorem B4297661 : Blo 670310 4297661 := bstep (se 3 (by rfl) ⟨805811, by rfl⟩ : syracuseStep 4297661 = 1611623) B1611623
theorem B1513439 : Blo 670310 1513439 := bstep (se 1 (by rfl) ⟨1135079, by rfl⟩ : syracuseStep 1513439 = 2270159) B2270159
theorem B1515167 : Blo 670310 1515167 := bstep (se 1 (by rfl) ⟨1136375, by rfl⟩ : syracuseStep 1515167 = 2272751) B2272751
theorem B12296647 : Blo 670310 12296647 := bstep (se 1 (by rfl) ⟨9222485, by rfl⟩ : syracuseStep 12296647 = 18444971) B18444971
theorem B11642563 : Blo 670310 11642563 := bstep (se 1 (by rfl) ⟨8731922, by rfl⟩ : syracuseStep 11642563 = 17463845) B17463845
theorem B3454655 : Blo 670310 3454655 := bstep (se 1 (by rfl) ⟨2590991, by rfl⟩ : syracuseStep 3454655 = 5181983) B5181983
theorem B14497865 : Blo 670310 14497865 := bstep (se 2 (by rfl) ⟨5436699, by rfl⟩ : syracuseStep 14497865 = 10873399) B10873399
theorem B671023 : Blo 670310 671023 := bstep (se 1 (by rfl) ⟨503267, by rfl⟩ : syracuseStep 671023 = 1006535) B1006535
theorem B5094737 : Blo 670310 5094737 := bstep (se 2 (by rfl) ⟨1910526, by rfl⟩ : syracuseStep 5094737 = 3821053) B3821053
theorem B671263 : Blo 670310 671263 := bstep (se 1 (by rfl) ⟨503447, by rfl⟩ : syracuseStep 671263 = 1006895) B1006895
theorem B671359 : Blo 670310 671359 := bstep (se 1 (by rfl) ⟨503519, by rfl⟩ : syracuseStep 671359 = 1007039) B1007039
theorem B671743 : Blo 670310 671743 := bstep (se 1 (by rfl) ⟨503807, by rfl⟩ : syracuseStep 671743 = 1007615) B1007615
theorem B673383 : Blo 670310 673383 := bstep (se 1 (by rfl) ⟨505037, by rfl⟩ : syracuseStep 673383 = 1010075) B1010075
theorem B5097167 : Blo 670310 5097167 := bstep (se 1 (by rfl) ⟨3822875, by rfl⟩ : syracuseStep 5097167 = 7645751) B7645751
theorem B3393575 : Blo 670310 3393575 := bstep (se 1 (by rfl) ⟨2545181, by rfl⟩ : syracuseStep 3393575 = 5090363) B5090363
theorem B673959 : Blo 670310 673959 := bstep (se 1 (by rfl) ⟨505469, by rfl⟩ : syracuseStep 673959 = 1010939) B1010939
theorem B11521115 : Blo 670310 11521115 := bstep (se 1 (by rfl) ⟨8640836, by rfl⟩ : syracuseStep 11521115 = 17281673) B17281673
theorem B1166903 : Blo 670310 1166903 := bstep (se 1 (by rfl) ⟨875177, by rfl⟩ : syracuseStep 1166903 = 1750355) B1750355
theorem B2183449 : Blo 670310 2183449 := bstep (se 2 (by rfl) ⟨818793, by rfl⟩ : syracuseStep 2183449 = 1637587) B1637587
theorem B2151137 : Blo 670310 2151137 := bstep (se 2 (by rfl) ⟨806676, by rfl⟩ : syracuseStep 2151137 = 1613353) B1613353
theorem B7657415 : Blo 670310 7657415 := bstep (se 1 (by rfl) ⟨5743061, by rfl⟩ : syracuseStep 7657415 = 11486123) B11486123
theorem B1696727 : Blo 670310 1696727 := bstep (se 1 (by rfl) ⟨1272545, by rfl⟩ : syracuseStep 1696727 = 2545091) B2545091
theorem B55240339 : Blo 670310 55240339 := bstep (se 1 (by rfl) ⟨41430254, by rfl⟩ : syracuseStep 55240339 = 82860509) B82860509
theorem B3238163 : Blo 670310 3238163 := bstep (se 1 (by rfl) ⟨2428622, by rfl⟩ : syracuseStep 3238163 = 4857245) B4857245
theorem B32794955 : Blo 670310 32794955 := bstep (se 1 (by rfl) ⟨24596216, by rfl⟩ : syracuseStep 32794955 = 49192433) B49192433
theorem B1010159 : Blo 670310 1010159 := bstep (se 1 (by rfl) ⟨757619, by rfl⟩ : syracuseStep 1010159 = 1515239) B1515239
theorem B1010345 : Blo 670310 1010345 := bstep (se 2 (by rfl) ⟨378879, by rfl⟩ : syracuseStep 1010345 = 757759) B757759
theorem B2555023 : Blo 670310 2555023 := bstep (se 1 (by rfl) ⟨1916267, by rfl⟩ : syracuseStep 2555023 = 3832535) B3832535
theorem B9699209 : Blo 670310 9699209 := bstep (se 2 (by rfl) ⟨3637203, by rfl⟩ : syracuseStep 9699209 = 7274407) B7274407
theorem B2262383 : Blo 670310 2262383 := bstep (se 1 (by rfl) ⟨1696787, by rfl⟩ : syracuseStep 2262383 = 3393575) B3393575
theorem B1509047 : Blo 670310 1509047 := bstep (se 1 (by rfl) ⟨1131785, by rfl⟩ : syracuseStep 1509047 = 2263571) B2263571
theorem B5736365 : Blo 670310 5736365 := bstep (se 3 (by rfl) ⟨1075568, by rfl⟩ : syracuseStep 5736365 = 2151137) B2151137
theorem B21863303 : Blo 670310 21863303 := bstep (se 1 (by rfl) ⟨16397477, by rfl⟩ : syracuseStep 21863303 = 32794955) B32794955
theorem B6466139 : Blo 670310 6466139 := bstep (se 1 (by rfl) ⟨4849604, by rfl⟩ : syracuseStep 6466139 = 9699209) B9699209
theorem B16395529 : Blo 670310 16395529 := bstep (se 2 (by rfl) ⟨6148323, by rfl⟩ : syracuseStep 16395529 = 12296647) B12296647
theorem B4305095 : Blo 670310 4305095 := bstep (se 1 (by rfl) ⟨3228821, by rfl⟩ : syracuseStep 4305095 = 6457643) B6457643
theorem B2273615 : Blo 670310 2273615 := bstep (se 1 (by rfl) ⟨1705211, by rfl⟩ : syracuseStep 2273615 = 3410423) B3410423
theorem B7680743 : Blo 670310 7680743 := bstep (se 1 (by rfl) ⟨5760557, by rfl⟩ : syracuseStep 7680743 = 11521115) B11521115
theorem B5093279 : Blo 670310 5093279 := bstep (se 1 (by rfl) ⟨3819959, by rfl⟩ : syracuseStep 5093279 = 7639919) B7639919
theorem B2865107 : Blo 670310 2865107 := bstep (se 1 (by rfl) ⟨2148830, by rfl⟩ : syracuseStep 2865107 = 4297661) B4297661
theorem B1131151 : Blo 670310 1131151 := bstep (se 1 (by rfl) ⟨848363, by rfl⟩ : syracuseStep 1131151 = 1696727) B1696727
theorem B673439 : Blo 670310 673439 := bstep (se 1 (by rfl) ⟨505079, by rfl⟩ : syracuseStep 673439 = 1010159) B1010159
theorem B673563 : Blo 670310 673563 := bstep (se 1 (by rfl) ⟨505172, by rfl⟩ : syracuseStep 673563 = 1010345) B1010345
theorem B36849653 : Blo 670310 36849653 := bstep (se 5 (by rfl) ⟨1727327, by rfl⟩ : syracuseStep 36849653 = 3454655) B3454655
theorem B3396491 : Blo 670310 3396491 := bstep (se 1 (by rfl) ⟨2547368, by rfl⟩ : syracuseStep 3396491 = 5094737) B5094737
theorem B3398111 : Blo 670310 3398111 := bstep (se 1 (by rfl) ⟨2548583, by rfl⟩ : syracuseStep 3398111 = 5097167) B5097167
theorem B73653785 : Blo 670310 73653785 := bstep (se 2 (by rfl) ⟨27620169, by rfl⟩ : syracuseStep 73653785 = 55240339) B55240339
theorem B15523417 : Blo 670310 15523417 := bstep (se 2 (by rfl) ⟨5821281, by rfl⟩ : syracuseStep 15523417 = 11642563) B11642563
theorem B777935 : Blo 670310 777935 := bstep (se 1 (by rfl) ⟨583451, by rfl⟩ : syracuseStep 777935 = 1166903) B1166903
theorem B5104943 : Blo 670310 5104943 := bstep (se 1 (by rfl) ⟨3828707, by rfl⟩ : syracuseStep 5104943 = 7657415) B7657415
theorem B1008959 : Blo 670310 1008959 := bstep (se 1 (by rfl) ⟨756719, by rfl⟩ : syracuseStep 1008959 = 1513439) B1513439
theorem B1010111 : Blo 670310 1010111 := bstep (se 1 (by rfl) ⟨757583, by rfl⟩ : syracuseStep 1010111 = 1515167) B1515167
theorem B2911265 : Blo 670310 2911265 := bstep (se 2 (by rfl) ⟨1091724, by rfl⟩ : syracuseStep 2911265 = 2183449) B2183449
theorem B2158775 : Blo 670310 2158775 := bstep (se 1 (by rfl) ⟨1619081, by rfl⟩ : syracuseStep 2158775 = 3238163) B3238163
theorem B9665243 : Blo 670310 9665243 := bstep (se 1 (by rfl) ⟨7248932, by rfl⟩ : syracuseStep 9665243 = 14497865) B14497865
theorem B3406697 : Blo 670310 3406697 := bstep (se 2 (by rfl) ⟨1277511, by rfl⟩ : syracuseStep 3406697 = 2555023) B2555023
theorem B1508201 : Blo 670310 1508201 := bstep (se 2 (by rfl) ⟨565575, by rfl⟩ : syracuseStep 1508201 = 1131151) B1131151
theorem B1508255 : Blo 670310 1508255 := bstep (se 1 (by rfl) ⟨1131191, by rfl⟩ : syracuseStep 1508255 = 2262383) B2262383
theorem B2264327 : Blo 670310 2264327 := bstep (se 1 (by rfl) ⟨1698245, by rfl⟩ : syracuseStep 2264327 = 3396491) B3396491
theorem B2265407 : Blo 670310 2265407 := bstep (se 1 (by rfl) ⟨1699055, by rfl⟩ : syracuseStep 2265407 = 3398111) B3398111
theorem B21860705 : Blo 670310 21860705 := bstep (se 2 (by rfl) ⟨8197764, by rfl⟩ : syracuseStep 21860705 = 16395529) B16395529
theorem B1940843 : Blo 670310 1940843 := bstep (se 1 (by rfl) ⟨1455632, by rfl⟩ : syracuseStep 1940843 = 2911265) B2911265
theorem B1515743 : Blo 670310 1515743 := bstep (se 1 (by rfl) ⟨1136807, by rfl⟩ : syracuseStep 1515743 = 2273615) B2273615
theorem B5120495 : Blo 670310 5120495 := bstep (se 1 (by rfl) ⟨3840371, by rfl⟩ : syracuseStep 5120495 = 7680743) B7680743
theorem B1910071 : Blo 670310 1910071 := bstep (se 1 (by rfl) ⟨1432553, by rfl⟩ : syracuseStep 1910071 = 2865107) B2865107
theorem B2074493 : Blo 670310 2074493 := bstep (se 3 (by rfl) ⟨388967, by rfl⟩ : syracuseStep 2074493 = 777935) B777935
theorem B2271131 : Blo 670310 2271131 := bstep (se 1 (by rfl) ⟨1703348, by rfl⟩ : syracuseStep 2271131 = 3406697) B3406697
theorem B49102523 : Blo 670310 49102523 := bstep (se 1 (by rfl) ⟨36826892, by rfl⟩ : syracuseStep 49102523 = 73653785) B73653785
theorem B672639 : Blo 670310 672639 := bstep (se 1 (by rfl) ⟨504479, by rfl⟩ : syracuseStep 672639 = 1008959) B1008959
theorem B673407 : Blo 670310 673407 := bstep (se 1 (by rfl) ⟨505055, by rfl⟩ : syracuseStep 673407 = 1010111) B1010111
theorem B4310759 : Blo 670310 4310759 := bstep (se 1 (by rfl) ⟨3233069, by rfl⟩ : syracuseStep 4310759 = 6466139) B6466139
theorem B2870063 : Blo 670310 2870063 := bstep (se 1 (by rfl) ⟨2152547, by rfl⟩ : syracuseStep 2870063 = 4305095) B4305095
theorem B3395519 : Blo 670310 3395519 := bstep (se 1 (by rfl) ⟨2546639, by rfl⟩ : syracuseStep 3395519 = 5093279) B5093279
theorem B6443495 : Blo 670310 6443495 := bstep (se 1 (by rfl) ⟨4832621, by rfl⟩ : syracuseStep 6443495 = 9665243) B9665243
theorem B20697889 : Blo 670310 20697889 := bstep (se 2 (by rfl) ⟨7761708, by rfl⟩ : syracuseStep 20697889 = 15523417) B15523417
theorem B1006031 : Blo 670310 1006031 := bstep (se 1 (by rfl) ⟨754523, by rfl⟩ : syracuseStep 1006031 = 1509047) B1509047
theorem B3824243 : Blo 670310 3824243 := bstep (se 1 (by rfl) ⟨2868182, by rfl⟩ : syracuseStep 3824243 = 5736365) B5736365
theorem B24566435 : Blo 670310 24566435 := bstep (se 1 (by rfl) ⟨18424826, by rfl⟩ : syracuseStep 24566435 = 36849653) B36849653
theorem B14575535 : Blo 670310 14575535 := bstep (se 1 (by rfl) ⟨10931651, by rfl⟩ : syracuseStep 14575535 = 21863303) B21863303
theorem B3403295 : Blo 670310 3403295 := bstep (se 1 (by rfl) ⟨2552471, by rfl⟩ : syracuseStep 3403295 = 5104943) B5104943
theorem B1439183 : Blo 670310 1439183 := bstep (se 1 (by rfl) ⟨1079387, by rfl⟩ : syracuseStep 1439183 = 2158775) B2158775
theorem B1509551 : Blo 670310 1509551 := bstep (se 1 (by rfl) ⟨1132163, by rfl⟩ : syracuseStep 1509551 = 2264327) B2264327
theorem B2263679 : Blo 670310 2263679 := bstep (se 1 (by rfl) ⟨1697759, by rfl⟩ : syracuseStep 2263679 = 3395519) B3395519
theorem B1510271 : Blo 670310 1510271 := bstep (se 1 (by rfl) ⟨1132703, by rfl⟩ : syracuseStep 1510271 = 2265407) B2265407
theorem B4295663 : Blo 670310 4295663 := bstep (se 1 (by rfl) ⟨3221747, by rfl⟩ : syracuseStep 4295663 = 6443495) B6443495
theorem B3413663 : Blo 670310 3413663 := bstep (se 1 (by rfl) ⟨2560247, by rfl⟩ : syracuseStep 3413663 = 5120495) B5120495
theorem B27597185 : Blo 670310 27597185 := bstep (se 2 (by rfl) ⟨10348944, by rfl⟩ : syracuseStep 27597185 = 20697889) B20697889
theorem B1514087 : Blo 670310 1514087 := bstep (se 1 (by rfl) ⟨1135565, by rfl⟩ : syracuseStep 1514087 = 2271131) B2271131
theorem B2268863 : Blo 670310 2268863 := bstep (se 1 (by rfl) ⟨1701647, by rfl⟩ : syracuseStep 2268863 = 3403295) B3403295
theorem B959455 : Blo 670310 959455 := bstep (se 1 (by rfl) ⟨719591, by rfl⟩ : syracuseStep 959455 = 1439183) B1439183
theorem B1913375 : Blo 670310 1913375 := bstep (se 1 (by rfl) ⟨1435031, by rfl⟩ : syracuseStep 1913375 = 2870063) B2870063
theorem B670687 : Blo 670310 670687 := bstep (se 1 (by rfl) ⟨503015, by rfl⟩ : syracuseStep 670687 = 1006031) B1006031
theorem B1293895 : Blo 670310 1293895 := bstep (se 1 (by rfl) ⟨970421, by rfl⟩ : syracuseStep 1293895 = 1940843) B1940843
theorem B9717023 : Blo 670310 9717023 := bstep (se 1 (by rfl) ⟨7287767, by rfl⟩ : syracuseStep 9717023 = 14575535) B14575535
theorem B1005467 : Blo 670310 1005467 := bstep (se 1 (by rfl) ⟨754100, by rfl⟩ : syracuseStep 1005467 = 1508201) B1508201
theorem B1005503 : Blo 670310 1005503 := bstep (se 1 (by rfl) ⟨754127, by rfl⟩ : syracuseStep 1005503 = 1508255) B1508255
theorem B2873839 : Blo 670310 2873839 := bstep (se 1 (by rfl) ⟨2155379, by rfl⟩ : syracuseStep 2873839 = 4310759) B4310759
theorem B2546761 : Blo 670310 2546761 := bstep (se 2 (by rfl) ⟨955035, by rfl⟩ : syracuseStep 2546761 = 1910071) B1910071
theorem B14573803 : Blo 670310 14573803 := bstep (se 1 (by rfl) ⟨10930352, by rfl⟩ : syracuseStep 14573803 = 21860705) B21860705
theorem B2549495 : Blo 670310 2549495 := bstep (se 1 (by rfl) ⟨1912121, by rfl⟩ : syracuseStep 2549495 = 3824243) B3824243
theorem B16377623 : Blo 670310 16377623 := bstep (se 1 (by rfl) ⟨12283217, by rfl⟩ : syracuseStep 16377623 = 24566435) B24566435
theorem B5531981 : Blo 670310 5531981 := bstep (se 3 (by rfl) ⟨1037246, by rfl⟩ : syracuseStep 5531981 = 2074493) B2074493
theorem B1010495 : Blo 670310 1010495 := bstep (se 1 (by rfl) ⟨757871, by rfl⟩ : syracuseStep 1010495 = 1515743) B1515743
theorem B32735015 : Blo 670310 32735015 := bstep (se 1 (by rfl) ⟨24551261, by rfl⟩ : syracuseStep 32735015 = 49102523) B49102523
theorem B19431737 : Blo 670310 19431737 := bstep (se 2 (by rfl) ⟨7286901, by rfl⟩ : syracuseStep 19431737 = 14573803) B14573803
theorem B1509119 : Blo 670310 1509119 := bstep (se 1 (by rfl) ⟨1131839, by rfl⟩ : syracuseStep 1509119 = 2263679) B2263679
theorem B1512575 : Blo 670310 1512575 := bstep (se 1 (by rfl) ⟨1134431, by rfl⟩ : syracuseStep 1512575 = 2268863) B2268863
theorem B5117093 : Blo 670310 5117093 := bstep (se 4 (by rfl) ⟨479727, by rfl⟩ : syracuseStep 5117093 = 959455) B959455
theorem B10918415 : Blo 670310 10918415 := bstep (se 1 (by rfl) ⟨8188811, by rfl⟩ : syracuseStep 10918415 = 16377623) B16377623
theorem B2863775 : Blo 670310 2863775 := bstep (se 1 (by rfl) ⟨2147831, by rfl⟩ : syracuseStep 2863775 = 4295663) B4295663
theorem B2275775 : Blo 670310 2275775 := bstep (se 1 (by rfl) ⟨1706831, by rfl⟩ : syracuseStep 2275775 = 3413663) B3413663
theorem B670311 : Blo 670310 670311 := bstep (se 1 (by rfl) ⟨502733, by rfl⟩ : syracuseStep 670311 = 1005467) B1005467
theorem B670335 : Blo 670310 670335 := bstep (se 1 (by rfl) ⟨502751, by rfl⟩ : syracuseStep 670335 = 1005503) B1005503
theorem B18398123 : Blo 670310 18398123 := bstep (se 1 (by rfl) ⟨13798592, by rfl⟩ : syracuseStep 18398123 = 27597185) B27597185
theorem B673663 : Blo 670310 673663 := bstep (se 1 (by rfl) ⟨505247, by rfl⟩ : syracuseStep 673663 = 1010495) B1010495
theorem B3395681 : Blo 670310 3395681 := bstep (se 2 (by rfl) ⟨1273380, by rfl⟩ : syracuseStep 3395681 = 2546761) B2546761
theorem B1725193 : Blo 670310 1725193 := bstep (se 2 (by rfl) ⟨646947, by rfl⟩ : syracuseStep 1725193 = 1293895) B1293895
theorem B6478015 : Blo 670310 6478015 := bstep (se 1 (by rfl) ⟨4858511, by rfl⟩ : syracuseStep 6478015 = 9717023) B9717023
theorem B1006367 : Blo 670310 1006367 := bstep (se 1 (by rfl) ⟨754775, by rfl⟩ : syracuseStep 1006367 = 1509551) B1509551
theorem B1006847 : Blo 670310 1006847 := bstep (se 1 (by rfl) ⟨755135, by rfl⟩ : syracuseStep 1006847 = 1510271) B1510271
theorem B59007797 : Blo 670310 59007797 := bstep (se 5 (by rfl) ⟨2765990, by rfl⟩ : syracuseStep 59007797 = 5531981) B5531981
theorem B1009391 : Blo 670310 1009391 := bstep (se 1 (by rfl) ⟨757043, by rfl⟩ : syracuseStep 1009391 = 1514087) B1514087
theorem B1699663 : Blo 670310 1699663 := bstep (se 1 (by rfl) ⟨1274747, by rfl⟩ : syracuseStep 1699663 = 2549495) B2549495
theorem B1275583 : Blo 670310 1275583 := bstep (se 1 (by rfl) ⟨956687, by rfl⟩ : syracuseStep 1275583 = 1913375) B1913375
theorem B3831785 : Blo 670310 3831785 := bstep (se 2 (by rfl) ⟨1436919, by rfl⟩ : syracuseStep 3831785 = 2873839) B2873839
theorem B21823343 : Blo 670310 21823343 := bstep (se 1 (by rfl) ⟨16367507, by rfl⟩ : syracuseStep 21823343 = 32735015) B32735015
theorem B2263787 : Blo 670310 2263787 := bstep (se 1 (by rfl) ⟨1697840, by rfl⟩ : syracuseStep 2263787 = 3395681) B3395681
theorem B3411395 : Blo 670310 3411395 := bstep (se 1 (by rfl) ⟨2558546, by rfl⟩ : syracuseStep 3411395 = 5117093) B5117093
theorem B2266217 : Blo 670310 2266217 := bstep (se 2 (by rfl) ⟨849831, by rfl⟩ : syracuseStep 2266217 = 1699663) B1699663
theorem B2300257 : Blo 670310 2300257 := bstep (se 2 (by rfl) ⟨862596, by rfl⟩ : syracuseStep 2300257 = 1725193) B1725193
theorem B1909183 : Blo 670310 1909183 := bstep (se 1 (by rfl) ⟨1431887, by rfl⟩ : syracuseStep 1909183 = 2863775) B2863775
theorem B1517183 : Blo 670310 1517183 := bstep (se 1 (by rfl) ⟨1137887, by rfl⟩ : syracuseStep 1517183 = 2275775) B2275775
theorem B12265415 : Blo 670310 12265415 := bstep (se 1 (by rfl) ⟨9199061, by rfl⟩ : syracuseStep 12265415 = 18398123) B18398123
theorem B12954491 : Blo 670310 12954491 := bstep (se 1 (by rfl) ⟨9715868, by rfl⟩ : syracuseStep 12954491 = 19431737) B19431737
theorem B670911 : Blo 670310 670911 := bstep (se 1 (by rfl) ⟨503183, by rfl⟩ : syracuseStep 670911 = 1006367) B1006367
theorem B671231 : Blo 670310 671231 := bstep (se 1 (by rfl) ⟨503423, by rfl⟩ : syracuseStep 671231 = 1006847) B1006847
theorem B39338531 : Blo 670310 39338531 := bstep (se 1 (by rfl) ⟨29503898, by rfl⟩ : syracuseStep 39338531 = 59007797) B59007797
theorem B672927 : Blo 670310 672927 := bstep (se 1 (by rfl) ⟨504695, by rfl⟩ : syracuseStep 672927 = 1009391) B1009391
theorem B29115773 : Blo 670310 29115773 := bstep (se 3 (by rfl) ⟨5459207, by rfl⟩ : syracuseStep 29115773 = 10918415) B10918415
theorem B8637353 : Blo 670310 8637353 := bstep (se 2 (by rfl) ⟨3239007, by rfl⟩ : syracuseStep 8637353 = 6478015) B6478015
theorem B1006079 : Blo 670310 1006079 := bstep (se 1 (by rfl) ⟨754559, by rfl⟩ : syracuseStep 1006079 = 1509119) B1509119
theorem B1008383 : Blo 670310 1008383 := bstep (se 1 (by rfl) ⟨756287, by rfl⟩ : syracuseStep 1008383 = 1512575) B1512575
theorem B1700777 : Blo 670310 1700777 := bstep (se 2 (by rfl) ⟨637791, by rfl⟩ : syracuseStep 1700777 = 1275583) B1275583
theorem B2554523 : Blo 670310 2554523 := bstep (se 1 (by rfl) ⟨1915892, by rfl⟩ : syracuseStep 2554523 = 3831785) B3831785
theorem B14548895 : Blo 670310 14548895 := bstep (se 1 (by rfl) ⟨10911671, by rfl⟩ : syracuseStep 14548895 = 21823343) B21823343
theorem B1509191 : Blo 670310 1509191 := bstep (se 1 (by rfl) ⟨1131893, by rfl⟩ : syracuseStep 1509191 = 2263787) B2263787
theorem B1510811 : Blo 670310 1510811 := bstep (se 1 (by rfl) ⟨1133108, by rfl⟩ : syracuseStep 1510811 = 2266217) B2266217
theorem B26225687 : Blo 670310 26225687 := bstep (se 1 (by rfl) ⟨19669265, by rfl⟩ : syracuseStep 26225687 = 39338531) B39338531
theorem B19410515 : Blo 670310 19410515 := bstep (se 1 (by rfl) ⟨14557886, by rfl⟩ : syracuseStep 19410515 = 29115773) B29115773
theorem B12268037 : Blo 670310 12268037 := bstep (se 4 (by rfl) ⟨1150128, by rfl⟩ : syracuseStep 12268037 = 2300257) B2300257
theorem B2274263 : Blo 670310 2274263 := bstep (se 1 (by rfl) ⟨1705697, by rfl⟩ : syracuseStep 2274263 = 3411395) B3411395
theorem B670719 : Blo 670310 670719 := bstep (se 1 (by rfl) ⟨503039, by rfl⟩ : syracuseStep 670719 = 1006079) B1006079
theorem B672255 : Blo 670310 672255 := bstep (se 1 (by rfl) ⟨504191, by rfl⟩ : syracuseStep 672255 = 1008383) B1008383
theorem B8176943 : Blo 670310 8176943 := bstep (se 1 (by rfl) ⟨6132707, by rfl⟩ : syracuseStep 8176943 = 12265415) B12265415
theorem B8636327 : Blo 670310 8636327 := bstep (se 1 (by rfl) ⟨6477245, by rfl⟩ : syracuseStep 8636327 = 12954491) B12954491
theorem B1133851 : Blo 670310 1133851 := bstep (se 1 (by rfl) ⟨850388, by rfl⟩ : syracuseStep 1133851 = 1700777) B1700777
theorem B2545577 : Blo 670310 2545577 := bstep (se 2 (by rfl) ⟨954591, by rfl⟩ : syracuseStep 2545577 = 1909183) B1909183
theorem B5758235 : Blo 670310 5758235 := bstep (se 1 (by rfl) ⟨4318676, by rfl⟩ : syracuseStep 5758235 = 8637353) B8637353
theorem B1011455 : Blo 670310 1011455 := bstep (se 1 (by rfl) ⟨758591, by rfl⟩ : syracuseStep 1011455 = 1517183) B1517183
theorem B1703015 : Blo 670310 1703015 := bstep (se 1 (by rfl) ⟨1277261, by rfl⟩ : syracuseStep 1703015 = 2554523) B2554523
theorem B9699263 : Blo 670310 9699263 := bstep (se 1 (by rfl) ⟨7274447, by rfl⟩ : syracuseStep 9699263 = 14548895) B14548895
theorem B1511801 : Blo 670310 1511801 := bstep (se 2 (by rfl) ⟨566925, by rfl⟩ : syracuseStep 1511801 = 1133851) B1133851
theorem B3838823 : Blo 670310 3838823 := bstep (se 1 (by rfl) ⟨2879117, by rfl⟩ : syracuseStep 3838823 = 5758235) B5758235
theorem B1516175 : Blo 670310 1516175 := bstep (se 1 (by rfl) ⟨1137131, by rfl⟩ : syracuseStep 1516175 = 2274263) B2274263
theorem B6466175 : Blo 670310 6466175 := bstep (se 1 (by rfl) ⟨4849631, by rfl⟩ : syracuseStep 6466175 = 9699263) B9699263
theorem B5451295 : Blo 670310 5451295 := bstep (se 1 (by rfl) ⟨4088471, by rfl⟩ : syracuseStep 5451295 = 8176943) B8176943
theorem B32714765 : Blo 670310 32714765 := bstep (se 3 (by rfl) ⟨6134018, by rfl⟩ : syracuseStep 32714765 = 12268037) B12268037
theorem B17483791 : Blo 670310 17483791 := bstep (se 1 (by rfl) ⟨13112843, by rfl⟩ : syracuseStep 17483791 = 26225687) B26225687
theorem B674303 : Blo 670310 674303 := bstep (se 1 (by rfl) ⟨505727, by rfl⟩ : syracuseStep 674303 = 1011455) B1011455
theorem B1135343 : Blo 670310 1135343 := bstep (se 1 (by rfl) ⟨851507, by rfl⟩ : syracuseStep 1135343 = 1703015) B1703015
theorem B1006127 : Blo 670310 1006127 := bstep (se 1 (by rfl) ⟨754595, by rfl⟩ : syracuseStep 1006127 = 1509191) B1509191
theorem B5757551 : Blo 670310 5757551 := bstep (se 1 (by rfl) ⟨4318163, by rfl⟩ : syracuseStep 5757551 = 8636327) B8636327
theorem B1007207 : Blo 670310 1007207 := bstep (se 1 (by rfl) ⟨755405, by rfl⟩ : syracuseStep 1007207 = 1510811) B1510811
theorem B1697051 : Blo 670310 1697051 := bstep (se 1 (by rfl) ⟨1272788, by rfl⟩ : syracuseStep 1697051 = 2545577) B2545577
theorem B12940343 : Blo 670310 12940343 := bstep (se 1 (by rfl) ⟨9705257, by rfl⟩ : syracuseStep 12940343 = 19410515) B19410515
theorem B756895 : Blo 670310 756895 := bstep (se 1 (by rfl) ⟨567671, by rfl⟩ : syracuseStep 756895 = 1135343) B1135343
theorem B2559215 : Blo 670310 2559215 := bstep (se 1 (by rfl) ⟨1919411, by rfl⟩ : syracuseStep 2559215 = 3838823) B3838823
theorem B3838367 : Blo 670310 3838367 := bstep (se 1 (by rfl) ⟨2878775, by rfl⟩ : syracuseStep 3838367 = 5757551) B5757551
theorem B8626895 : Blo 670310 8626895 := bstep (se 1 (by rfl) ⟨6470171, by rfl⟩ : syracuseStep 8626895 = 12940343) B12940343
theorem B23311721 : Blo 670310 23311721 := bstep (se 2 (by rfl) ⟨8741895, by rfl⟩ : syracuseStep 23311721 = 17483791) B17483791
theorem B670751 : Blo 670310 670751 := bstep (se 1 (by rfl) ⟨503063, by rfl⟩ : syracuseStep 670751 = 1006127) B1006127
theorem B671471 : Blo 670310 671471 := bstep (se 1 (by rfl) ⟨503603, by rfl⟩ : syracuseStep 671471 = 1007207) B1007207
theorem B1131367 : Blo 670310 1131367 := bstep (se 1 (by rfl) ⟨848525, by rfl⟩ : syracuseStep 1131367 = 1697051) B1697051
theorem B4310783 : Blo 670310 4310783 := bstep (se 1 (by rfl) ⟨3233087, by rfl⟩ : syracuseStep 4310783 = 6466175) B6466175
theorem B21809843 : Blo 670310 21809843 := bstep (se 1 (by rfl) ⟨16357382, by rfl⟩ : syracuseStep 21809843 = 32714765) B32714765
theorem B1007867 : Blo 670310 1007867 := bstep (se 1 (by rfl) ⟨755900, by rfl⟩ : syracuseStep 1007867 = 1511801) B1511801
theorem B7268393 : Blo 670310 7268393 := bstep (se 2 (by rfl) ⟨2725647, by rfl⟩ : syracuseStep 7268393 = 5451295) B5451295
theorem B1010783 : Blo 670310 1010783 := bstep (se 1 (by rfl) ⟨758087, by rfl⟩ : syracuseStep 1010783 = 1516175) B1516175
theorem B1508489 : Blo 670310 1508489 := bstep (se 2 (by rfl) ⟨565683, by rfl⟩ : syracuseStep 1508489 = 1131367) B1131367
theorem B1706143 : Blo 670310 1706143 := bstep (se 1 (by rfl) ⟨1279607, by rfl⟩ : syracuseStep 1706143 = 2559215) B2559215
theorem B2558911 : Blo 670310 2558911 := bstep (se 1 (by rfl) ⟨1919183, by rfl⟩ : syracuseStep 2558911 = 3838367) B3838367
theorem B15541147 : Blo 670310 15541147 := bstep (se 1 (by rfl) ⟨11655860, by rfl⟩ : syracuseStep 15541147 = 23311721) B23311721
theorem B671911 : Blo 670310 671911 := bstep (se 1 (by rfl) ⟨503933, by rfl⟩ : syracuseStep 671911 = 1007867) B1007867
theorem B5751263 : Blo 670310 5751263 := bstep (se 1 (by rfl) ⟨4313447, by rfl⟩ : syracuseStep 5751263 = 8626895) B8626895
theorem B673855 : Blo 670310 673855 := bstep (se 1 (by rfl) ⟨505391, by rfl⟩ : syracuseStep 673855 = 1010783) B1010783
theorem B2873855 : Blo 670310 2873855 := bstep (se 1 (by rfl) ⟨2155391, by rfl⟩ : syracuseStep 2873855 = 4310783) B4310783
theorem B14539895 : Blo 670310 14539895 := bstep (se 1 (by rfl) ⟨10904921, by rfl⟩ : syracuseStep 14539895 = 21809843) B21809843
theorem B1009193 : Blo 670310 1009193 := bstep (se 2 (by rfl) ⟨378447, by rfl⟩ : syracuseStep 1009193 = 756895) B756895
theorem B4845595 : Blo 670310 4845595 := bstep (se 1 (by rfl) ⟨3634196, by rfl⟩ : syracuseStep 4845595 = 7268393) B7268393
theorem B3834175 : Blo 670310 3834175 := bstep (se 1 (by rfl) ⟨2875631, by rfl⟩ : syracuseStep 3834175 = 5751263) B5751263
theorem B3411881 : Blo 670310 3411881 := bstep (se 2 (by rfl) ⟨1279455, by rfl⟩ : syracuseStep 3411881 = 2558911) B2558911
theorem B6460793 : Blo 670310 6460793 := bstep (se 2 (by rfl) ⟨2422797, by rfl⟩ : syracuseStep 6460793 = 4845595) B4845595
theorem B20721529 : Blo 670310 20721529 := bstep (se 2 (by rfl) ⟨7770573, by rfl⟩ : syracuseStep 20721529 = 15541147) B15541147
theorem B2274857 : Blo 670310 2274857 := bstep (se 2 (by rfl) ⟨853071, by rfl⟩ : syracuseStep 2274857 = 1706143) B1706143
theorem B1915903 : Blo 670310 1915903 := bstep (se 1 (by rfl) ⟨1436927, by rfl⟩ : syracuseStep 1915903 = 2873855) B2873855
theorem B672795 : Blo 670310 672795 := bstep (se 1 (by rfl) ⟨504596, by rfl⟩ : syracuseStep 672795 = 1009193) B1009193
theorem B1005659 : Blo 670310 1005659 := bstep (se 1 (by rfl) ⟨754244, by rfl⟩ : syracuseStep 1005659 = 1508489) B1508489
theorem B9693263 : Blo 670310 9693263 := bstep (se 1 (by rfl) ⟨7269947, by rfl⟩ : syracuseStep 9693263 = 14539895) B14539895
theorem B5112233 : Blo 670310 5112233 := bstep (se 2 (by rfl) ⟨1917087, by rfl⟩ : syracuseStep 5112233 = 3834175) B3834175
theorem B27628705 : Blo 670310 27628705 := bstep (se 2 (by rfl) ⟨10360764, by rfl⟩ : syracuseStep 27628705 = 20721529) B20721529
theorem B6462175 : Blo 670310 6462175 := bstep (se 1 (by rfl) ⟨4846631, by rfl⟩ : syracuseStep 6462175 = 9693263) B9693263
theorem B1516571 : Blo 670310 1516571 := bstep (se 1 (by rfl) ⟨1137428, by rfl⟩ : syracuseStep 1516571 = 2274857) B2274857
theorem B2274587 : Blo 670310 2274587 := bstep (se 1 (by rfl) ⟨1705940, by rfl⟩ : syracuseStep 2274587 = 3411881) B3411881
theorem B4307195 : Blo 670310 4307195 := bstep (se 1 (by rfl) ⟨3230396, by rfl⟩ : syracuseStep 4307195 = 6460793) B6460793
theorem B670439 : Blo 670310 670439 := bstep (se 1 (by rfl) ⟨502829, by rfl⟩ : syracuseStep 670439 = 1005659) B1005659
theorem B2554537 : Blo 670310 2554537 := bstep (se 2 (by rfl) ⟨957951, by rfl⟩ : syracuseStep 2554537 = 1915903) B1915903
theorem B3408155 : Blo 670310 3408155 := bstep (se 1 (by rfl) ⟨2556116, by rfl⟩ : syracuseStep 3408155 = 5112233) B5112233
theorem B36838273 : Blo 670310 36838273 := bstep (se 2 (by rfl) ⟨13814352, by rfl⟩ : syracuseStep 36838273 = 27628705) B27628705
theorem B1516391 : Blo 670310 1516391 := bstep (se 1 (by rfl) ⟨1137293, by rfl⟩ : syracuseStep 1516391 = 2274587) B2274587
theorem B2871463 : Blo 670310 2871463 := bstep (se 1 (by rfl) ⟨2153597, by rfl⟩ : syracuseStep 2871463 = 4307195) B4307195
theorem B1011047 : Blo 670310 1011047 := bstep (se 1 (by rfl) ⟨758285, by rfl⟩ : syracuseStep 1011047 = 1516571) B1516571
theorem B3406049 : Blo 670310 3406049 := bstep (se 2 (by rfl) ⟨1277268, by rfl⟩ : syracuseStep 3406049 = 2554537) B2554537
theorem B8616233 : Blo 670310 8616233 := bstep (se 2 (by rfl) ⟨3231087, by rfl⟩ : syracuseStep 8616233 = 6462175) B6462175
theorem B2270699 : Blo 670310 2270699 := bstep (se 1 (by rfl) ⟨1703024, by rfl⟩ : syracuseStep 2270699 = 3406049) B3406049
theorem B5744155 : Blo 670310 5744155 := bstep (se 1 (by rfl) ⟨4308116, by rfl⟩ : syracuseStep 5744155 = 8616233) B8616233
theorem B2272103 : Blo 670310 2272103 := bstep (se 1 (by rfl) ⟨1704077, by rfl⟩ : syracuseStep 2272103 = 3408155) B3408155
theorem B674031 : Blo 670310 674031 := bstep (se 1 (by rfl) ⟨505523, by rfl⟩ : syracuseStep 674031 = 1011047) B1011047
theorem B3828617 : Blo 670310 3828617 := bstep (se 2 (by rfl) ⟨1435731, by rfl⟩ : syracuseStep 3828617 = 2871463) B2871463
theorem B1010927 : Blo 670310 1010927 := bstep (se 1 (by rfl) ⟨758195, by rfl⟩ : syracuseStep 1010927 = 1516391) B1516391
theorem B49117697 : Blo 670310 49117697 := bstep (se 2 (by rfl) ⟨18419136, by rfl⟩ : syracuseStep 49117697 = 36838273) B36838273
theorem B1513799 : Blo 670310 1513799 := bstep (se 1 (by rfl) ⟨1135349, by rfl⟩ : syracuseStep 1513799 = 2270699) B2270699
theorem B1514735 : Blo 670310 1514735 := bstep (se 1 (by rfl) ⟨1136051, by rfl⟩ : syracuseStep 1514735 = 2272103) B2272103
theorem B32745131 : Blo 670310 32745131 := bstep (se 1 (by rfl) ⟨24558848, by rfl⟩ : syracuseStep 32745131 = 49117697) B49117697
theorem B673951 : Blo 670310 673951 := bstep (se 1 (by rfl) ⟨505463, by rfl⟩ : syracuseStep 673951 = 1010927) B1010927
theorem B7658873 : Blo 670310 7658873 := bstep (se 2 (by rfl) ⟨2872077, by rfl⟩ : syracuseStep 7658873 = 5744155) B5744155
theorem B2552411 : Blo 670310 2552411 := bstep (se 1 (by rfl) ⟨1914308, by rfl⟩ : syracuseStep 2552411 = 3828617) B3828617
theorem B21830087 : Blo 670310 21830087 := bstep (se 1 (by rfl) ⟨16372565, by rfl⟩ : syracuseStep 21830087 = 32745131) B32745131
theorem B1009199 : Blo 670310 1009199 := bstep (se 1 (by rfl) ⟨756899, by rfl⟩ : syracuseStep 1009199 = 1513799) B1513799
theorem B1009823 : Blo 670310 1009823 := bstep (se 1 (by rfl) ⟨757367, by rfl⟩ : syracuseStep 1009823 = 1514735) B1514735
theorem B5105915 : Blo 670310 5105915 := bstep (se 1 (by rfl) ⟨3829436, by rfl⟩ : syracuseStep 5105915 = 7658873) B7658873
theorem B1701607 : Blo 670310 1701607 := bstep (se 1 (by rfl) ⟨1276205, by rfl⟩ : syracuseStep 1701607 = 2552411) B2552411
theorem B14553391 : Blo 670310 14553391 := bstep (se 1 (by rfl) ⟨10915043, by rfl⟩ : syracuseStep 14553391 = 21830087) B21830087
theorem B2268809 : Blo 670310 2268809 := bstep (se 2 (by rfl) ⟨850803, by rfl⟩ : syracuseStep 2268809 = 1701607) B1701607
theorem B672799 : Blo 670310 672799 := bstep (se 1 (by rfl) ⟨504599, by rfl⟩ : syracuseStep 672799 = 1009199) B1009199
theorem B673215 : Blo 670310 673215 := bstep (se 1 (by rfl) ⟨504911, by rfl⟩ : syracuseStep 673215 = 1009823) B1009823
theorem B3403943 : Blo 670310 3403943 := bstep (se 1 (by rfl) ⟨2552957, by rfl⟩ : syracuseStep 3403943 = 5105915) B5105915
theorem B1512539 : Blo 670310 1512539 := bstep (se 1 (by rfl) ⟨1134404, by rfl⟩ : syracuseStep 1512539 = 2268809) B2268809
theorem B19404521 : Blo 670310 19404521 := bstep (se 2 (by rfl) ⟨7276695, by rfl⟩ : syracuseStep 19404521 = 14553391) B14553391
theorem B2269295 : Blo 670310 2269295 := bstep (se 1 (by rfl) ⟨1701971, by rfl⟩ : syracuseStep 2269295 = 3403943) B3403943
theorem B1512863 : Blo 670310 1512863 := bstep (se 1 (by rfl) ⟨1134647, by rfl⟩ : syracuseStep 1512863 = 2269295) B2269295
theorem B1008359 : Blo 670310 1008359 := bstep (se 1 (by rfl) ⟨756269, by rfl⟩ : syracuseStep 1008359 = 1512539) B1512539
theorem B12936347 : Blo 670310 12936347 := bstep (se 1 (by rfl) ⟨9702260, by rfl⟩ : syracuseStep 12936347 = 19404521) B19404521
theorem B8624231 : Blo 670310 8624231 := bstep (se 1 (by rfl) ⟨6468173, by rfl⟩ : syracuseStep 8624231 = 12936347) B12936347
theorem B672239 : Blo 670310 672239 := bstep (se 1 (by rfl) ⟨504179, by rfl⟩ : syracuseStep 672239 = 1008359) B1008359
theorem B1008575 : Blo 670310 1008575 := bstep (se 1 (by rfl) ⟨756431, by rfl⟩ : syracuseStep 1008575 = 1512863) B1512863
theorem B5749487 : Blo 670310 5749487 := bstep (se 1 (by rfl) ⟨4312115, by rfl⟩ : syracuseStep 5749487 = 8624231) B8624231
theorem B672383 : Blo 670310 672383 := bstep (se 1 (by rfl) ⟨504287, by rfl⟩ : syracuseStep 672383 = 1008575) B1008575
theorem B3832991 : Blo 670310 3832991 := bstep (se 1 (by rfl) ⟨2874743, by rfl⟩ : syracuseStep 3832991 = 5749487) B5749487
theorem B2555327 : Blo 670310 2555327 := bstep (se 1 (by rfl) ⟨1916495, by rfl⟩ : syracuseStep 2555327 = 3832991) B3832991
theorem B1703551 : Blo 670310 1703551 := bstep (se 1 (by rfl) ⟨1277663, by rfl⟩ : syracuseStep 1703551 = 2555327) B2555327
theorem B2271401 : Blo 670310 2271401 := bstep (se 2 (by rfl) ⟨851775, by rfl⟩ : syracuseStep 2271401 = 1703551) B1703551
theorem B1514267 : Blo 670310 1514267 := bstep (se 1 (by rfl) ⟨1135700, by rfl⟩ : syracuseStep 1514267 = 2271401) B2271401
theorem B1009511 : Blo 670310 1009511 := bstep (se 1 (by rfl) ⟨757133, by rfl⟩ : syracuseStep 1009511 = 1514267) B1514267
theorem B673007 : Blo 670310 673007 := bstep (se 1 (by rfl) ⟨504755, by rfl⟩ : syracuseStep 673007 = 1009511) B1009511

theorem C0 (j : ℕ) (h1 : 167577 ≤ j) (h2 : j ≤ 168276) : Blo 670310 (4 * j + 3) := by
  interval_cases j
  · exact B670311
  · exact B670315
  · exact B670319
  · exact B670323
  · exact B670327
  · exact B670331
  · exact B670335
  · exact B670339
  · exact B670343
  · exact B670347
  · exact B670351
  · exact B670355
  · exact B670359
  · exact B670363
  · exact B670367
  · exact B670371
  · exact B670375
  · exact B670379
  · exact B670383
  · exact B670387
  · exact B670391
  · exact B670395
  · exact B670399
  · exact B670403
  · exact B670407
  · exact B670411
  · exact B670415
  · exact B670419
  · exact B670423
  · exact B670427
  · exact B670431
  · exact B670435
  · exact B670439
  · exact B670443
  · exact B670447
  · exact B670451
  · exact B670455
  · exact B670459
  · exact B670463
  · exact B670467
  · exact B670471
  · exact B670475
  · exact B670479
  · exact B670483
  · exact B670487
  · exact B670491
  · exact B670495
  · exact B670499
  · exact B670503
  · exact B670507
  · exact B670511
  · exact B670515
  · exact B670519
  · exact B670523
  · exact B670527
  · exact B670531
  · exact B670535
  · exact B670539
  · exact B670543
  · exact B670547
  · exact B670551
  · exact B670555
  · exact B670559
  · exact B670563
  · exact B670567
  · exact B670571
  · exact B670575
  · exact B670579
  · exact B670583
  · exact B670587
  · exact B670591
  · exact B670595
  · exact B670599
  · exact B670603
  · exact B670607
  · exact B670611
  · exact B670615
  · exact B670619
  · exact B670623
  · exact B670627
  · exact B670631
  · exact B670635
  · exact B670639
  · exact B670643
  · exact B670647
  · exact B670651
  · exact B670655
  · exact B670659
  · exact B670663
  · exact B670667
  · exact B670671
  · exact B670675
  · exact B670679
  · exact B670683
  · exact B670687
  · exact B670691
  · exact B670695
  · exact B670699
  · exact B670703
  · exact B670707
  · exact B670711
  · exact B670715
  · exact B670719
  · exact B670723
  · exact B670727
  · exact B670731
  · exact B670735
  · exact B670739
  · exact B670743
  · exact B670747
  · exact B670751
  · exact B670755
  · exact B670759
  · exact B670763
  · exact B670767
  · exact B670771
  · exact B670775
  · exact B670779
  · exact B670783
  · exact B670787
  · exact B670791
  · exact B670795
  · exact B670799
  · exact B670803
  · exact B670807
  · exact B670811
  · exact B670815
  · exact B670819
  · exact B670823
  · exact B670827
  · exact B670831
  · exact B670835
  · exact B670839
  · exact B670843
  · exact B670847
  · exact B670851
  · exact B670855
  · exact B670859
  · exact B670863
  · exact B670867
  · exact B670871
  · exact B670875
  · exact B670879
  · exact B670883
  · exact B670887
  · exact B670891
  · exact B670895
  · exact B670899
  · exact B670903
  · exact B670907
  · exact B670911
  · exact B670915
  · exact B670919
  · exact B670923
  · exact B670927
  · exact B670931
  · exact B670935
  · exact B670939
  · exact B670943
  · exact B670947
  · exact B670951
  · exact B670955
  · exact B670959
  · exact B670963
  · exact B670967
  · exact B670971
  · exact B670975
  · exact B670979
  · exact B670983
  · exact B670987
  · exact B670991
  · exact B670995
  · exact B670999
  · exact B671003
  · exact B671007
  · exact B671011
  · exact B671015
  · exact B671019
  · exact B671023
  · exact B671027
  · exact B671031
  · exact B671035
  · exact B671039
  · exact B671043
  · exact B671047
  · exact B671051
  · exact B671055
  · exact B671059
  · exact B671063
  · exact B671067
  · exact B671071
  · exact B671075
  · exact B671079
  · exact B671083
  · exact B671087
  · exact B671091
  · exact B671095
  · exact B671099
  · exact B671103
  · exact B671107
  · exact B671111
  · exact B671115
  · exact B671119
  · exact B671123
  · exact B671127
  · exact B671131
  · exact B671135
  · exact B671139
  · exact B671143
  · exact B671147
  · exact B671151
  · exact B671155
  · exact B671159
  · exact B671163
  · exact B671167
  · exact B671171
  · exact B671175
  · exact B671179
  · exact B671183
  · exact B671187
  · exact B671191
  · exact B671195
  · exact B671199
  · exact B671203
  · exact B671207
  · exact B671211
  · exact B671215
  · exact B671219
  · exact B671223
  · exact B671227
  · exact B671231
  · exact B671235
  · exact B671239
  · exact B671243
  · exact B671247
  · exact B671251
  · exact B671255
  · exact B671259
  · exact B671263
  · exact B671267
  · exact B671271
  · exact B671275
  · exact B671279
  · exact B671283
  · exact B671287
  · exact B671291
  · exact B671295
  · exact B671299
  · exact B671303
  · exact B671307
  · exact B671311
  · exact B671315
  · exact B671319
  · exact B671323
  · exact B671327
  · exact B671331
  · exact B671335
  · exact B671339
  · exact B671343
  · exact B671347
  · exact B671351
  · exact B671355
  · exact B671359
  · exact B671363
  · exact B671367
  · exact B671371
  · exact B671375
  · exact B671379
  · exact B671383
  · exact B671387
  · exact B671391
  · exact B671395
  · exact B671399
  · exact B671403
  · exact B671407
  · exact B671411
  · exact B671415
  · exact B671419
  · exact B671423
  · exact B671427
  · exact B671431
  · exact B671435
  · exact B671439
  · exact B671443
  · exact B671447
  · exact B671451
  · exact B671455
  · exact B671459
  · exact B671463
  · exact B671467
  · exact B671471
  · exact B671475
  · exact B671479
  · exact B671483
  · exact B671487
  · exact B671491
  · exact B671495
  · exact B671499
  · exact B671503
  · exact B671507
  · exact B671511
  · exact B671515
  · exact B671519
  · exact B671523
  · exact B671527
  · exact B671531
  · exact B671535
  · exact B671539
  · exact B671543
  · exact B671547
  · exact B671551
  · exact B671555
  · exact B671559
  · exact B671563
  · exact B671567
  · exact B671571
  · exact B671575
  · exact B671579
  · exact B671583
  · exact B671587
  · exact B671591
  · exact B671595
  · exact B671599
  · exact B671603
  · exact B671607
  · exact B671611
  · exact B671615
  · exact B671619
  · exact B671623
  · exact B671627
  · exact B671631
  · exact B671635
  · exact B671639
  · exact B671643
  · exact B671647
  · exact B671651
  · exact B671655
  · exact B671659
  · exact B671663
  · exact B671667
  · exact B671671
  · exact B671675
  · exact B671679
  · exact B671683
  · exact B671687
  · exact B671691
  · exact B671695
  · exact B671699
  · exact B671703
  · exact B671707
  · exact B671711
  · exact B671715
  · exact B671719
  · exact B671723
  · exact B671727
  · exact B671731
  · exact B671735
  · exact B671739
  · exact B671743
  · exact B671747
  · exact B671751
  · exact B671755
  · exact B671759
  · exact B671763
  · exact B671767
  · exact B671771
  · exact B671775
  · exact B671779
  · exact B671783
  · exact B671787
  · exact B671791
  · exact B671795
  · exact B671799
  · exact B671803
  · exact B671807
  · exact B671811
  · exact B671815
  · exact B671819
  · exact B671823
  · exact B671827
  · exact B671831
  · exact B671835
  · exact B671839
  · exact B671843
  · exact B671847
  · exact B671851
  · exact B671855
  · exact B671859
  · exact B671863
  · exact B671867
  · exact B671871
  · exact B671875
  · exact B671879
  · exact B671883
  · exact B671887
  · exact B671891
  · exact B671895
  · exact B671899
  · exact B671903
  · exact B671907
  · exact B671911
  · exact B671915
  · exact B671919
  · exact B671923
  · exact B671927
  · exact B671931
  · exact B671935
  · exact B671939
  · exact B671943
  · exact B671947
  · exact B671951
  · exact B671955
  · exact B671959
  · exact B671963
  · exact B671967
  · exact B671971
  · exact B671975
  · exact B671979
  · exact B671983
  · exact B671987
  · exact B671991
  · exact B671995
  · exact B671999
  · exact B672003
  · exact B672007
  · exact B672011
  · exact B672015
  · exact B672019
  · exact B672023
  · exact B672027
  · exact B672031
  · exact B672035
  · exact B672039
  · exact B672043
  · exact B672047
  · exact B672051
  · exact B672055
  · exact B672059
  · exact B672063
  · exact B672067
  · exact B672071
  · exact B672075
  · exact B672079
  · exact B672083
  · exact B672087
  · exact B672091
  · exact B672095
  · exact B672099
  · exact B672103
  · exact B672107
  · exact B672111
  · exact B672115
  · exact B672119
  · exact B672123
  · exact B672127
  · exact B672131
  · exact B672135
  · exact B672139
  · exact B672143
  · exact B672147
  · exact B672151
  · exact B672155
  · exact B672159
  · exact B672163
  · exact B672167
  · exact B672171
  · exact B672175
  · exact B672179
  · exact B672183
  · exact B672187
  · exact B672191
  · exact B672195
  · exact B672199
  · exact B672203
  · exact B672207
  · exact B672211
  · exact B672215
  · exact B672219
  · exact B672223
  · exact B672227
  · exact B672231
  · exact B672235
  · exact B672239
  · exact B672243
  · exact B672247
  · exact B672251
  · exact B672255
  · exact B672259
  · exact B672263
  · exact B672267
  · exact B672271
  · exact B672275
  · exact B672279
  · exact B672283
  · exact B672287
  · exact B672291
  · exact B672295
  · exact B672299
  · exact B672303
  · exact B672307
  · exact B672311
  · exact B672315
  · exact B672319
  · exact B672323
  · exact B672327
  · exact B672331
  · exact B672335
  · exact B672339
  · exact B672343
  · exact B672347
  · exact B672351
  · exact B672355
  · exact B672359
  · exact B672363
  · exact B672367
  · exact B672371
  · exact B672375
  · exact B672379
  · exact B672383
  · exact B672387
  · exact B672391
  · exact B672395
  · exact B672399
  · exact B672403
  · exact B672407
  · exact B672411
  · exact B672415
  · exact B672419
  · exact B672423
  · exact B672427
  · exact B672431
  · exact B672435
  · exact B672439
  · exact B672443
  · exact B672447
  · exact B672451
  · exact B672455
  · exact B672459
  · exact B672463
  · exact B672467
  · exact B672471
  · exact B672475
  · exact B672479
  · exact B672483
  · exact B672487
  · exact B672491
  · exact B672495
  · exact B672499
  · exact B672503
  · exact B672507
  · exact B672511
  · exact B672515
  · exact B672519
  · exact B672523
  · exact B672527
  · exact B672531
  · exact B672535
  · exact B672539
  · exact B672543
  · exact B672547
  · exact B672551
  · exact B672555
  · exact B672559
  · exact B672563
  · exact B672567
  · exact B672571
  · exact B672575
  · exact B672579
  · exact B672583
  · exact B672587
  · exact B672591
  · exact B672595
  · exact B672599
  · exact B672603
  · exact B672607
  · exact B672611
  · exact B672615
  · exact B672619
  · exact B672623
  · exact B672627
  · exact B672631
  · exact B672635
  · exact B672639
  · exact B672643
  · exact B672647
  · exact B672651
  · exact B672655
  · exact B672659
  · exact B672663
  · exact B672667
  · exact B672671
  · exact B672675
  · exact B672679
  · exact B672683
  · exact B672687
  · exact B672691
  · exact B672695
  · exact B672699
  · exact B672703
  · exact B672707
  · exact B672711
  · exact B672715
  · exact B672719
  · exact B672723
  · exact B672727
  · exact B672731
  · exact B672735
  · exact B672739
  · exact B672743
  · exact B672747
  · exact B672751
  · exact B672755
  · exact B672759
  · exact B672763
  · exact B672767
  · exact B672771
  · exact B672775
  · exact B672779
  · exact B672783
  · exact B672787
  · exact B672791
  · exact B672795
  · exact B672799
  · exact B672803
  · exact B672807
  · exact B672811
  · exact B672815
  · exact B672819
  · exact B672823
  · exact B672827
  · exact B672831
  · exact B672835
  · exact B672839
  · exact B672843
  · exact B672847
  · exact B672851
  · exact B672855
  · exact B672859
  · exact B672863
  · exact B672867
  · exact B672871
  · exact B672875
  · exact B672879
  · exact B672883
  · exact B672887
  · exact B672891
  · exact B672895
  · exact B672899
  · exact B672903
  · exact B672907
  · exact B672911
  · exact B672915
  · exact B672919
  · exact B672923
  · exact B672927
  · exact B672931
  · exact B672935
  · exact B672939
  · exact B672943
  · exact B672947
  · exact B672951
  · exact B672955
  · exact B672959
  · exact B672963
  · exact B672967
  · exact B672971
  · exact B672975
  · exact B672979
  · exact B672983
  · exact B672987
  · exact B672991
  · exact B672995
  · exact B672999
  · exact B673003
  · exact B673007
  · exact B673011
  · exact B673015
  · exact B673019
  · exact B673023
  · exact B673027
  · exact B673031
  · exact B673035
  · exact B673039
  · exact B673043
  · exact B673047
  · exact B673051
  · exact B673055
  · exact B673059
  · exact B673063
  · exact B673067
  · exact B673071
  · exact B673075
  · exact B673079
  · exact B673083
  · exact B673087
  · exact B673091
  · exact B673095
  · exact B673099
  · exact B673103
  · exact B673107

theorem C1 (j : ℕ) (h1 : 168277 ≤ j) (h2 : j ≤ 168576) : Blo 670310 (4 * j + 3) := by
  interval_cases j
  · exact B673111
  · exact B673115
  · exact B673119
  · exact B673123
  · exact B673127
  · exact B673131
  · exact B673135
  · exact B673139
  · exact B673143
  · exact B673147
  · exact B673151
  · exact B673155
  · exact B673159
  · exact B673163
  · exact B673167
  · exact B673171
  · exact B673175
  · exact B673179
  · exact B673183
  · exact B673187
  · exact B673191
  · exact B673195
  · exact B673199
  · exact B673203
  · exact B673207
  · exact B673211
  · exact B673215
  · exact B673219
  · exact B673223
  · exact B673227
  · exact B673231
  · exact B673235
  · exact B673239
  · exact B673243
  · exact B673247
  · exact B673251
  · exact B673255
  · exact B673259
  · exact B673263
  · exact B673267
  · exact B673271
  · exact B673275
  · exact B673279
  · exact B673283
  · exact B673287
  · exact B673291
  · exact B673295
  · exact B673299
  · exact B673303
  · exact B673307
  · exact B673311
  · exact B673315
  · exact B673319
  · exact B673323
  · exact B673327
  · exact B673331
  · exact B673335
  · exact B673339
  · exact B673343
  · exact B673347
  · exact B673351
  · exact B673355
  · exact B673359
  · exact B673363
  · exact B673367
  · exact B673371
  · exact B673375
  · exact B673379
  · exact B673383
  · exact B673387
  · exact B673391
  · exact B673395
  · exact B673399
  · exact B673403
  · exact B673407
  · exact B673411
  · exact B673415
  · exact B673419
  · exact B673423
  · exact B673427
  · exact B673431
  · exact B673435
  · exact B673439
  · exact B673443
  · exact B673447
  · exact B673451
  · exact B673455
  · exact B673459
  · exact B673463
  · exact B673467
  · exact B673471
  · exact B673475
  · exact B673479
  · exact B673483
  · exact B673487
  · exact B673491
  · exact B673495
  · exact B673499
  · exact B673503
  · exact B673507
  · exact B673511
  · exact B673515
  · exact B673519
  · exact B673523
  · exact B673527
  · exact B673531
  · exact B673535
  · exact B673539
  · exact B673543
  · exact B673547
  · exact B673551
  · exact B673555
  · exact B673559
  · exact B673563
  · exact B673567
  · exact B673571
  · exact B673575
  · exact B673579
  · exact B673583
  · exact B673587
  · exact B673591
  · exact B673595
  · exact B673599
  · exact B673603
  · exact B673607
  · exact B673611
  · exact B673615
  · exact B673619
  · exact B673623
  · exact B673627
  · exact B673631
  · exact B673635
  · exact B673639
  · exact B673643
  · exact B673647
  · exact B673651
  · exact B673655
  · exact B673659
  · exact B673663
  · exact B673667
  · exact B673671
  · exact B673675
  · exact B673679
  · exact B673683
  · exact B673687
  · exact B673691
  · exact B673695
  · exact B673699
  · exact B673703
  · exact B673707
  · exact B673711
  · exact B673715
  · exact B673719
  · exact B673723
  · exact B673727
  · exact B673731
  · exact B673735
  · exact B673739
  · exact B673743
  · exact B673747
  · exact B673751
  · exact B673755
  · exact B673759
  · exact B673763
  · exact B673767
  · exact B673771
  · exact B673775
  · exact B673779
  · exact B673783
  · exact B673787
  · exact B673791
  · exact B673795
  · exact B673799
  · exact B673803
  · exact B673807
  · exact B673811
  · exact B673815
  · exact B673819
  · exact B673823
  · exact B673827
  · exact B673831
  · exact B673835
  · exact B673839
  · exact B673843
  · exact B673847
  · exact B673851
  · exact B673855
  · exact B673859
  · exact B673863
  · exact B673867
  · exact B673871
  · exact B673875
  · exact B673879
  · exact B673883
  · exact B673887
  · exact B673891
  · exact B673895
  · exact B673899
  · exact B673903
  · exact B673907
  · exact B673911
  · exact B673915
  · exact B673919
  · exact B673923
  · exact B673927
  · exact B673931
  · exact B673935
  · exact B673939
  · exact B673943
  · exact B673947
  · exact B673951
  · exact B673955
  · exact B673959
  · exact B673963
  · exact B673967
  · exact B673971
  · exact B673975
  · exact B673979
  · exact B673983
  · exact B673987
  · exact B673991
  · exact B673995
  · exact B673999
  · exact B674003
  · exact B674007
  · exact B674011
  · exact B674015
  · exact B674019
  · exact B674023
  · exact B674027
  · exact B674031
  · exact B674035
  · exact B674039
  · exact B674043
  · exact B674047
  · exact B674051
  · exact B674055
  · exact B674059
  · exact B674063
  · exact B674067
  · exact B674071
  · exact B674075
  · exact B674079
  · exact B674083
  · exact B674087
  · exact B674091
  · exact B674095
  · exact B674099
  · exact B674103
  · exact B674107
  · exact B674111
  · exact B674115
  · exact B674119
  · exact B674123
  · exact B674127
  · exact B674131
  · exact B674135
  · exact B674139
  · exact B674143
  · exact B674147
  · exact B674151
  · exact B674155
  · exact B674159
  · exact B674163
  · exact B674167
  · exact B674171
  · exact B674175
  · exact B674179
  · exact B674183
  · exact B674187
  · exact B674191
  · exact B674195
  · exact B674199
  · exact B674203
  · exact B674207
  · exact B674211
  · exact B674215
  · exact B674219
  · exact B674223
  · exact B674227
  · exact B674231
  · exact B674235
  · exact B674239
  · exact B674243
  · exact B674247
  · exact B674251
  · exact B674255
  · exact B674259
  · exact B674263
  · exact B674267
  · exact B674271
  · exact B674275
  · exact B674279
  · exact B674283
  · exact B674287
  · exact B674291
  · exact B674295
  · exact B674299
  · exact B674303
  · exact B674307

theorem solution (m : ℕ) (hlo : 670310 ≤ m) (hhi : m ≤ 674310) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 167577 ≤ j := by omega
    have hj2 : j ≤ 168576 := by omega
    have hb : Blo 670310 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 168277 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
